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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import DefsE DefsW.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.EH Require Import Pool.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import TdEnter Td PkExit VDestroy.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2F Require Import T_Ubs2F.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2U Require Import T_Ubs2U.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE Require Import T_Ubs2UE.
Module C_UW_52944_f61d2_w7_r14_pP_L0.

Definition ROOT : sstate := (t_st T_Ubs2UE.T_UW_52944_f61d2_w7_r14_pP_L0).
Definition CUTS : IMap.t template := imap_of [(580%uint63, T_Ubs2UE.T_ZLOOP_w4_r11_pP_L0_km260)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2UE.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan (StrLz.lz_dec "-$>Y`LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X0<3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZYa@#5%()<I7XD58?%,-&2LH3;TPAERPPBERPPCERPP6TPP6VPPEERPPFERPPGERPPHERPPIERPPJERPPKERPPLERPPMERPPNERPPIUPPJUPPBWPPOERPP0VPP;UPP3VPLPP4VPP5V0&%-($LWPP7VPU4b:Qj0XjOWjNWjMWjLWjKWjJWjIWjHWjGWjFWjEWjDWjCWjBWjAWj@Wj?Wj>Wj=Wj<Wj;Wj:Wj9Wj8Wj7Wj6Wj5Wj4Wi6T6TiDSESi>SBSi<S<SiOR:SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSySPk[Q0#(-#%ySPk1RQySPkAS1#)8#0@#)#>@$'$<@#.$'0(%#2@''(%@$5%,-#$[QySPylQ<;3X@8;1+2%klR@':(@@'6(-7#0-#,ySQfQ0000OOOOOOOOW@D2#-%OOW@%$%9@&,(2@$4%+@%$*-@'-(+@$;%2@$7*-"%pstring).
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2UE.T_UW_52944_f61d2_w7_r14_pP_L0) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_UW_52944_f61d2_w7_r14_pP_L0.

Module C_UW_52944_f61d2_w8_r15_pv_L0.

Definition ROOT : sstate := (t_st T_Ubs2UE.T_UW_52944_f61d2_w8_r15_pv_L0).
Definition CUTS : IMap.t template := imap_of [(582%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_pv_L0_km260)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2UE.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan (StrLz.lz_dec "-$>Y`LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X0<3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZYa@#5%()<I7XD58?%,-&2LH3;TPBERPPCERPPDERPP6TPP6VPPFERPPGERPPHERPPIERPPJERPPKERPPLERPPMERPPNERPPOERPPIUPPJUPPCWPP0FRPP0VPP;UPP3VPLPP4VPP5V0&%-';7VPU6b9Qj0XjOWjNWjMWjLWjKWjJWjIWjHWjGWjFWjEWjDWjCWjBWjAWj@Wj?Wj>Wj=Wj<Wj;Wj:Wj9Wj8Wj7Wj6Wj5Wi4W4Wi6T6Ti>SESi<S<SiOR:SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSySPk[Q0#(-#%ySPk1RQySPkAS1#)8#0@#)#>@$'$<@#.$'0(%#2@''(%@$5%,-#$[QySPylQ<;3X@841++%klR@':(@@'6(-7#0-#,ySQfQ0000OOOOOOOOW@D2#-%OOW@%$%9@&,(2@$4%+@%$*-@'-(+@$;%2@$7*-"%pstring).
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2UE.T_UW_52944_f61d2_w8_r15_pv_L0) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_UW_52944_f61d2_w8_r15_pv_L0.

Module C_UW_52944_fce48_w7_r14_pP_L0.

Definition ROOT : sstate := (t_st T_Ubs2UE.T_UW_52944_fce48_w7_r14_pP_L0).
Definition CUTS : IMap.t template := imap_of [(580%uint63, T_Ubs2UE.T_ZLOOP_w4_r11_pP_L0_km260)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2UE.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan (StrLz.lz_dec "-$>Y`LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X0<3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZYa@#5%()<I7XD58?%,-&2LH3;TPAERPPBERPPCERPP6TPP6VPPEERPPFERPPGERPPHERPPIERPPJERPPKERPPLERPPMERPPNERPPIUPPJUPPBWPPOERPP1VPP<UPP3VPLPP4VPP5V0&%-($LWPP9VPU4b:Qj0XjOWjNWjMWjLWjKWjJWjIWjHWjGWjFWjEWjDWjCWjBWjAWj@Wj?Wj>Wj=Wj<Wj;Wj:Wj9Wj8Wj7Wj6Wj5Wj4Wi6T6TiDSESi>SBSi<S<SiOR:SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSySPk[Q0#(%ySP@,$,9-#-k1RQySPcyT8J0TSPkASQy1#)8#0@#)#>@$'$<@#,$'@,)1$'@101->$k22(.%DJ1@'%(.@$5%,-#$[QySPylQ<;3X@@@20;@=/20;%klR@':(@@'6(-7#0-#,ySQfQ0000OOOOOOOOW@D2#-%OOW@%$%9@&,(2@$4%+@%$*-@'-(+@$;%2@$7*-"%pstring).
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2UE.T_UW_52944_fce48_w7_r14_pP_L0) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_UW_52944_fce48_w7_r14_pP_L0.

Module C_UW_52944_fce48_w8_r15_pv_L0.

Definition ROOT : sstate := (t_st T_Ubs2UE.T_UW_52944_fce48_w8_r15_pv_L0).
Definition CUTS : IMap.t template := imap_of [(582%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_pv_L0_km260)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2UE.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan (StrLz.lz_dec "-$>Y`LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X0<3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZYa@#5%()<I7XD58?%,-&2LH3;TPBERPPCERPPDERPP6TPP6VPPFERPPGERPPHERPPIERPPJERPPKERPPLERPPMERPPNERPPOERPPIUPPJUPPCWPP0FRPP1VPP<UPP3VPLPP4VPP5V0&%-';9VPU6b9Qj0XjOWjNWjMWjLWjKWjJWjIWjHWjGWjFWjEWjDWjCWjBWjAWj@Wj?Wj>Wj=Wj<Wj;Wj:Wj9Wj8Wj7Wj6Wj5Wi4W4Wi6T6Ti>SESi<S<SiOR:SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSySPk[Q0#(%ySP@+;,2-#-k1RQySPcyT8J0TSPkASQy1#)8#0@#)#>@$'$<@#,$'@+@1#>@1)1-0$k22(.%DJ1@'%(.@$5%,-#$[QySPylQ<;3X@@@2/=@<12/=%klR@':(@@'6(-7#0-#,ySQfQ0000OOOOOOOOW@D2#-%OOW@%$%9@&,(2@$4%+@%$*-@'-(+@$;%2@$7*-"%pstring).
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2UE.T_UW_52944_fce48_w8_r15_pv_L0) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_UW_52944_fce48_w8_r15_pv_L0.

Module C_UW_52944_ff71a_w7_r14_pP_L0.

Definition ROOT : sstate := (t_st T_Ubs2UE.T_UW_52944_ff71a_w7_r14_pP_L0).
Definition CUTS : IMap.t template := imap_of [(580%uint63, T_Ubs2UE.T_ZLOOP_w4_r11_pP_L0_km260)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2UE.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan (StrLz.lz_dec "-$>Y`LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X0<3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZYa@#5%()<I7XD58?%,-&2LH3;TPAERPPBERPPCERPP6TPP8VPPEERPPFERPPGERPPHERPPIERPPJERPPKERPPLERPPMERPPNERPPJUPPKUPPBWPPOERPP3VPP<UPP5VPLPP6VPP7V0&%-($LWPP;VPU4b:Qj0XjOWjNWjMWjLWjKWjJWjIWjHWjGWjFWjEWjDWjCWjBWjAWj@Wj?Wj>Wj=Wj<Wj;Wj:Wj9Wj8Wj7Wj6Wj5Wj4Wi6T6TiDSESi>SBSi<S<SiOR:SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSySPk[Q0#(%ySP@,$,9-#-k1RQySPcyT8J0TSPkASQy1#)8#0@#)#>@$'$<@#,$'@,)1$'@101->$k22(.%DJ1@'%(.@$5%,-#$[QySPylQ<;3X@@@20;@=/20;%klR@':(@@'6(-7#0-#,ySQfQ0000OOOOOOOOW@D2#-%OOW@%$%9@&,(2@$4%+@%$*-@'-(+@$;%2@$7*-"%pstring).
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2UE.T_UW_52944_ff71a_w7_r14_pP_L0) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_UW_52944_ff71a_w7_r14_pP_L0.

Module C_UW_52944_ff71a_w8_r15_pv_L0.

Definition ROOT : sstate := (t_st T_Ubs2UE.T_UW_52944_ff71a_w8_r15_pv_L0).
Definition CUTS : IMap.t template := imap_of [(582%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_pv_L0_km260)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2UE.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan (StrLz.lz_dec "-$>Y`LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X0<3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZYa@#5%()<I7XD58?%,-&2LH3;TPBERPPCERPPDERPP6TPP8VPPFERPPGERPPHERPPIERPPJERPPKERPPLERPPMERPPNERPPOERPPJUPPKUPPCWPP0FRPP3VPP<UPP5VPLPP6VPP7V0&%-';;VPU6b9Qj0XjOWjNWjMWjLWjKWjJWjIWjHWjGWjFWjEWjDWjCWjBWjAWj@Wj?Wj>Wj=Wj<Wj;Wj:Wj9Wj8Wj7Wj6Wj5Wi4W4Wi6T6Ti>SESi<S<SiOR:SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSySPk[Q0#(%ySP@+;,2-#-k1RQySPcyT8J0TSPkASQy1#)8#0@#)#>@$'$<@#,$'@+@1#>@1)1-0$k22(.%DJ1@'%(.@$5%,-#$[QySPylQ<;3X@@@2/=@<12/=%klR@':(@@'6(-7#0-#,ySQfQ0000OOOOOOOOW@D2#-%OOW@%$%9@&,(2@$4%+@%$*-@'-(+@$;%2@$7*-"%pstring).
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2UE.T_UW_52944_ff71a_w8_r15_pv_L0) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_UW_52944_ff71a_w8_r15_pv_L0.

Module C_ZLOOP_w4_r11_p3h682ecc7db_L0.

Definition ROOT : sstate := (t_st T_Ubs2UE.T_ZLOOP_w4_r11_p3h682ecc7db_L0).
Definition CUTS : IMap.t template := imap_of [(101%uint63, T_Ubs2UE.T_FINAL_r9); (576%uint63, T_Ubs2UE.T_ZLOOP_w4_r11_p3h682ecc7db_L0)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (t_measure T_Ubs2UE.T_ZLOOP_w4_r11_p3h682ecc7db_L0).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2UE.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y`LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X0<3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZP4XPP5XPP6XPP7XPP2XPP2XPP9XPP:XPP;XPP<XPP=XPP>XPP?XPP@XPPAXPPBXPPCXPP3XPV0b1QjOWiHWNWjGWiDWFWjCWjBWjAWj@Wj?Wj>Wj=Wj<Wj;Wj:Wj9Wj8Wj7Wj6Wj5Wj4Wi6T6TiDSESi>SBSi<S<SiOR:SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSySPk[QySPylQ45OSLLHMSL8QL<G0]PHXPL@;0]L<B0]L<G0]L<G0]LPL0TL=RP0YPP1YPP2YPP3YPPARPPBRPPCRPPDRPPERPPFRPPGRPPHRPPDWPPJRPPKRPPLRPPMRPPEWPPORPP0SPP1SPP2SPP3SPP4SPPFWPLRP5bPU5S@QjKTjJTjITjHTjGTjFTjETjDTjCTjBTjATj@Tj?Tj>Tj=Tj<Tj;Tj:Tj9Tj8Tj7Tj6Tj5Tj4Tj3Tj2Tj1Tj0TjOSjNSjMSjLSjKSjJSjISjHSjGSjFSiDSESi>SBSi<S<Si5S:Si;R<Ri0R1Ri\\iZZiUXiPSk5QQfQ0000OOOOOOOOW6OOOOOOOOOOOWySPylQ4<3XySPylQ<;3XySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPk[QySPk[QySPylQ45OSk7QR"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2UE.T_ZLOOP_w4_r11_p3h682ecc7db_L0) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_ZLOOP_w4_r11_p3h682ecc7db_L0.

Module C_ZLOOP_w5_r12_p3h6818cc68b_L0.

Definition ROOT : sstate := (t_st T_Ubs2UE.T_ZLOOP_w5_r12_p3h6818cc68b_L0).
Definition CUTS : IMap.t template := imap_of [(101%uint63, T_Ubs2UE.T_FINAL_r9); (577%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_p3h6818cc68b_L0)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (t_measure T_Ubs2UE.T_ZLOOP_w5_r12_p3h6818cc68b_L0).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2UE.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y`LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X0<3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZP5XPP6XPP7XPP8XPP3XPP3XPP:XPP;XPP<XPP=XPP>XPP?XPP@XPPAXPPBXPPCXPPDXPP4XPV1b2Qj0XiIWOWjHWiEWGWjDWjCWjBWjAWj@Wj?Wj>Wj=Wj<Wj;Wj:Wj9Wj8Wj7Wj6Wj5Wi4W4Wi6T6TiDSESi>SBSi<S<SiOR:SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSySPk[QySPylQ45OSLLHMSP8bPP9bPP:bPP;bPP<bPP=bPP>bPP?bPP@bPPAbPPBbPPCbPPDbPPEbPPARPPBRPPCRPPDRPPERPPFRPPGRPPHRPPEWPPJRPPKRPPLRPPMRPPFWPPORPP0SPP1SPP2SPP3SPP4SPPGWPLQPFbPU5S@QjKTjJTjITjHTjGTjFTjETjDTjCTjBTjATj@Tj?Tj>Tj=Tj<Tj;Tj:Tj9Tj8Tj7Tj6Tj5Tj4Tj3Tj2Tj1Tj0TjOSjNSjMSjLSjKSjJSjISjHSjGSjFSiDSESi>SBSi<S<Si5S:Si;R<Ri0R1Ri\\iZZiUXiPSk5QQfQ0000OOOOOOOOW6OOOOOOOOOOOWySPk[QySPylQ<;3XLLHMSP8bPP9bPP:bPP;bPP<bPP=bPP>bPP?bPP@bPPAbPPBbPPCbPPDbPPEbPPARPPBRPPCRPPDRPPERPPFRPPGRPPHRPPEWPPJRPPKRPPLRPPMRPPFWPPORPP0SPP1SPP2SPP3SPP4SPPGWPLQPFbPU5S@QjKTjJTjITjHTjGTjFTjETjDTjCTjBTjATj@Tj?Tj>Tj=Tj<Tj;Tj:Tj9Tj8Tj7Tj6Tj5Tj4Tj3Tj2Tj1Tj0TjOSjNSjMSjLSjKSjJSjISjHSjGSjFSiDSESi>SBSi<S<Si5S:Si;R<Ri0R1Ri\\iZZiUXiPSk5QQfQ0000OOOOOOOOW6OOOOOOOOOOOWySPk[QySPylQ<;3XklRySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPk[QySPk[QySPylQ45OSk7QR"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2UE.T_ZLOOP_w5_r12_p3h6818cc68b_L0) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_ZLOOP_w5_r12_p3h6818cc68b_L0.

Module C_ZLOOP_w5_r12_p3h6824cc132_L0.

Definition ROOT : sstate := (t_st T_Ubs2UE.T_ZLOOP_w5_r12_p3h6824cc132_L0).
Definition CUTS : IMap.t template := imap_of [(101%uint63, T_Ubs2UE.T_FINAL_r9); (578%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_p3h6824cc132_L0)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (t_measure T_Ubs2UE.T_ZLOOP_w5_r12_p3h6824cc132_L0).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2UE.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y`LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X0<3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZP5XPP6XPP7XPP8XPP3XPP3XPP:XPP;XPP<XPP=XPP>XPP?XPP@XPPAXPPBXPPCXPPDXPP4XPV2b2Qj0XiIWOWjHWiEWGWjDWjCWjBWjAWj@Wj?Wj>Wj=Wj<Wj;Wj:Wj9Wj8Wj7Wj6Wj5Wi4W4Wi6T6TiDSESi>SBSi<S<SiOR:SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSySPk[QySPylQ45OSLLHMSP8bPP9bPP:bPP;bPP<bPP=bPP>bPP?bPP@bPPAbPPBbPPCbPPDbPPEbPPARPPBRPPCRPPDRPPERPPFRPPGRPPHRPPEWPPJRPPKRPPLRPPMRPPFWPPORPP0SPP1SPP2SPP3SPP4SPPGWPLRPFbPU5S@QjKTjJTjITjHTjGTjFTjETjDTjCTjBTjATj@Tj?Tj>Tj=Tj<Tj;Tj:Tj9Tj8Tj7Tj6Tj5Tj4Tj3Tj2Tj1Tj0TjOSjNSjMSjLSjKSjJSjISjHSjGSjFSiDSESi>SBSi<S<Si5S:Si;R<Ri0R1Ri\\iZZiUXiPSk5QQfQ0000OOOOOOOOW6OOOOOOOOOOOWySPk[QySPylQ<;3XLLHMSP8bPP9bPP:bPP;bPP<bPP=bPP>bPP?bPP@bPPAbPPBbPPCbPPDbPPEbPPARPPBRPPCRPPDRPPERPPFRPPGRPPHRPPEWPPJRPPKRPPLRPPMRPPFWPPORPP0SPP1SPP2SPP3SPP4SPPGWPLRPFbPU5S@QjKTjJTjITjHTjGTjFTjETjDTjCTjBTjATj@Tj?Tj>Tj=Tj<Tj;Tj:Tj9Tj8Tj7Tj6Tj5Tj4Tj3Tj2Tj1Tj0TjOSjNSjMSjLSjKSjJSjISjHSjGSjFSiDSESi>SBSi<S<Si5S:Si;R<Ri0R1Ri\\iZZiUXiPSk5QQfQ0000OOOOOOOOW6OOOOOOOOOOOWySPk[QySPylQ<;3XklRySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPk[QySPk[QySPylQ45OSk7QR"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2UE.T_ZLOOP_w5_r12_p3h6824cc132_L0) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_ZLOOP_w5_r12_p3h6824cc132_L0.
