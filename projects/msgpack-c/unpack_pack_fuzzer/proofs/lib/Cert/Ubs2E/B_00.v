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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2L Require Import T_Ubs2L.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2E Require Import T_Ubs2E.
Module C_EH_1fba8_LIBENT_r8_1.

Definition ROOT : sstate := (t_st T_Ubs2L.T_THROW_1fba8_LIBENT_r8_1).
Definition CUTS : IMap.t template := imap_of [(105%uint63, T_Ubs2E.T_XA_1fba8_6b647_blk_w3_r10_L0); (106%uint63, T_Ubs2E.T_XA_1fba8_6b647_p682f0_w2_r9_p3h6818cc776); (107%uint63, T_Ubs2E.T_XA_1fba8_6b647_p682f0_w2_r9_p3h6824cc449)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2E.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y_LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZU:S[iBTFTi:T:TiCSCSi=SASi@R;Si:R;Ri0R0Ri\\iZZiUXiPSySPylQ013XU:S[iBTFTi:T:TiCSCSi=SASi@R;Si:R;Ri0R0Ri\\iZZiUXiPSySPylQ013XU;S[iBTFTi:T:TiCSCSi=SASi@R;Si:R;Ri0R0Ri\\iZZiUXiPSySPylQ013Xk4QSySPU9S[i8TGTiFSFSiCSCSi=SASi@R;Si:R;Ri0R0Ri\\iZZiUXiPSySPkmRySPylQ<61X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2L.T_THROW_1fba8_LIBENT_r8_1) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_EH_1fba8_LIBENT_r8_1.

Module C_EH_1fba8_LIBENT_r9_1.

Definition ROOT : sstate := (t_st T_Ubs2L.T_THROW_1fba8_LIBENT_r9_1).
Definition CUTS : IMap.t template := imap_of [(102%uint63, T_Ubs2E.T_XA_1fba8_1acc8_blk_w4_r11_L0); (103%uint63, T_Ubs2E.T_XA_1fba8_1acc8_p682f0_w3_r10_p3h6818cc776); (104%uint63, T_Ubs2E.T_XA_1fba8_1acc8_p682f0_w3_r10_p3h6824cc449)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2E.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y_LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZU7S[iATETi9T9TiDSESi>SBSiAR<Si;R<Ri0R1Ri\\iZZiUXiPSySPylQ013XU7S[iATETi9T9TiDSESi>SBSiAR<Si;R<Ri0R1Ri\\iZZiUXiPSySPylQ013XU8S[iATETi9T9TiDSESi>SBSiAR<Si;R<Ri0R1Ri\\iZZiUXiPSySPylQ013Xk4QSySPU6SYi7TFTi>SESiAR<Si;R<Ri0R1Ri\\iZZiUXiPSySPkmRySPylQ<61X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2L.T_THROW_1fba8_LIBENT_r9_1) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_EH_1fba8_LIBENT_r9_1.

Module C_EH_1fc40_LIBENT_r8_2.

Definition ROOT : sstate := (t_st T_Ubs2L.T_THROW_1fc40_LIBENT_r8_2).
Definition CUTS : IMap.t template := imap_of [(108%uint63, T_Ubs2E.T_XA_1fc40_72faa_blk_w4_r11_L0); (109%uint63, T_Ubs2E.T_XA_1fc40_72faa_p682f0_w3_r10_p3h6818cc776); (110%uint63, T_Ubs2E.T_XA_1fc40_72faa_p682f0_w3_r10_p3h6824cc449)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2E.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y_LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZU=S\i3U7UiKTKTi7T7TiCSCSi=SASi@R;Si:R;Ri0R0Ri\\iZZiUXiPSySPylQ013XU=S\i3U7UiKTKTi7T7TiCSCSi=SASi@R;Si:R;Ri0R0Ri\\iZZiUXiPSySPylQ013XU>S\i3U7UiKTKTi7T7TiCSCSi=SASi@R;Si:R;Ri0R0Ri\\iZZiUXiPSySPylQ013Xk4QSySPU<S\iIT8Ui7T7TiFSFSiCSCSi=SASi@R;Si:R;Ri0R0Ri\\iZZiUXiPSySPkmRySPylQ<61X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2L.T_THROW_1fc40_LIBENT_r8_2) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_EH_1fc40_LIBENT_r8_2.

Module C_EH_1fc40_LIBENT_r9_2.

Definition ROOT : sstate := (t_st T_Ubs2L.T_THROW_1fc40_LIBENT_r9_2).
Definition CUTS : IMap.t template := imap_of [(111%uint63, T_Ubs2E.T_XA_1fc40_991f7_blk_w5_r12_L0); (112%uint63, T_Ubs2E.T_XA_1fc40_991f7_p682f0_w4_r11_p3h6818cc776); (113%uint63, T_Ubs2E.T_XA_1fc40_991f7_p682f0_w4_r11_p3h6824cc449)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2E.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y_LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZU@S\i2U6UiJTJTi6T6TiDSESi>SBSiAR<Si;R<Ri0R1Ri\\iZZiUXiPSySPylQ013XU@S\i2U6UiJTJTi6T6TiDSESi>SBSiAR<Si;R<Ri0R1Ri\\iZZiUXiPSySPylQ013XUAS\i2U6UiJTJTi6T6TiDSESi>SBSiAR<Si;R<Ri0R1Ri\\iZZiUXiPSySPylQ013Xk4QSySPU?SZiHT7Ui6T6Ti>SESiAR<Si;R<Ri0R1Ri\\iZZiUXiPSySPkmRySPylQ<61X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2L.T_THROW_1fc40_LIBENT_r9_2) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_EH_1fc40_LIBENT_r9_2.

Module C_EH_2037c_LIBENT_r8_4.

Definition ROOT : sstate := (t_st T_Ubs2L.T_THROW_2037c_LIBENT_r8_4).
Definition CUTS : IMap.t template := imap_of [(114%uint63, T_Ubs2E.T_XA_2037c_01284_blk_w6_r13_L0); (115%uint63, T_Ubs2E.T_XA_2037c_01284_p682f0_w5_r12_p3h6818cc776); (116%uint63, T_Ubs2E.T_XA_2037c_01284_p682f0_w5_r12_p3h6824cc449)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2E.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y_LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZUCS^iEVIVi=V=ViIUIUiHTHTi7T7TiCSCSi=SASi@R;Si:R;Ri0R0Ri\\iZZiUXiPSySPylQ013XUCS^iEVIVi=V=ViIUIUiHTHTi7T7TiCSCSi=SASi@R;Si:R;Ri0R0Ri\\iZZiUXiPSySPylQ013XUDS^iEVIVi=V=ViIUIUiHTHTi7T7TiCSCSi=SASi@R;Si:R;Ri0R0Ri\\iZZiUXiPSySPylQ013Xk4QSySPPJVPPIVPUBS`jJVjIVi;VHViIUIUiHTHTi7T7TiFSFSiCSCSi=SASi@R;Si:R;Ri0R0Ri\\iZZiUXiPSySPkmRySPylQ<61X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2L.T_THROW_2037c_LIBENT_r8_4) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_EH_2037c_LIBENT_r8_4.

Module C_EH_52944_LIBENT_r8_3.

Definition ROOT : sstate := (t_st T_Ubs2L.T_THROW_52944_LIBENT_r8_3).
Definition CUTS : IMap.t template := imap_of [(120%uint63, T_Ubs2E.T_XA_52944_a198b_blk_w5_r12_L0); (121%uint63, T_Ubs2E.T_XA_52944_a198b_p682f0_w4_r11_p3h6818cc776); (122%uint63, T_Ubs2E.T_XA_52944_a198b_p682f0_w4_r11_p3h6824cc449)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2E.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y_LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZUIS]i4V8ViLULUiHTHTi7T7TiCSCSi=SASi@R;Si:R;Ri0R0Ri\\iZZiUXiPSySPylQ013XUIS]i4V8ViLULUiHTHTi7T7TiCSCSi=SASi@R;Si:R;Ri0R0Ri\\iZZiUXiPSySPylQ013XUJS]i4V8ViLULUiHTHTi7T7TiCSCSi=SASi@R;Si:R;Ri0R0Ri\\iZZiUXiPSySPylQ013Xk4QSySPUHS]iJU9ViHTHTi7T7TiFSFSiCSCSi=SASi@R;Si:R;Ri0R0Ri\\iZZiUXiPSySPkmRySPylQ<61X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2L.T_THROW_52944_LIBENT_r8_3) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_EH_52944_LIBENT_r8_3.

Module C_EH_52944_LIBENT_r9_3.

Definition ROOT : sstate := (t_st T_Ubs2L.T_THROW_52944_LIBENT_r9_3).
Definition CUTS : IMap.t template := imap_of [(117%uint63, T_Ubs2E.T_XA_52944_67536_blk_w6_r13_L0); (118%uint63, T_Ubs2E.T_XA_52944_67536_p682f0_w5_r12_p3h6818cc776); (119%uint63, T_Ubs2E.T_XA_52944_67536_p682f0_w5_r12_p3h6824cc449)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2E.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y_LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZUFS]i3V7ViKUKUiGTGTi6T6TiDSESi>SBSiAR<Si;R<Ri0R1Ri\\iZZiUXiPSySPylQ013XUFS]i3V7ViKUKUiGTGTi6T6TiDSESi>SBSiAR<Si;R<Ri0R1Ri\\iZZiUXiPSySPylQ013XUGS]i3V7ViKUKUiGTGTi6T6TiDSESi>SBSiAR<Si;R<Ri0R1Ri\\iZZiUXiPSySPylQ013Xk4QSySPUES[iIU8ViGTGTi6T6Ti>SESiAR<Si;R<Ri0R1Ri\\iZZiUXiPSySPkmRySPylQ<61X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2L.T_THROW_52944_LIBENT_r9_3) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_EH_52944_LIBENT_r9_3.

Module C_EH_52944_LIBENT_r9_4.

Definition ROOT : sstate := (t_st T_Ubs2L.T_THROW_52944_LIBENT_r9_4).
Definition CUTS : IMap.t template := imap_of [(123%uint63, T_Ubs2E.T_XA_52944_d4b36_blk_w7_r14_L0); (124%uint63, T_Ubs2E.T_XA_52944_d4b36_p682f0_w6_r13_p3h6818cc776); (125%uint63, T_Ubs2E.T_XA_52944_d4b36_p682f0_w6_r13_p3h6824cc449)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2E.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y_LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZPLVPP4WPP5WPP6WPP7WPP8WPULSbjNVjMVjLVjKVjJVjIViHUHUiGTGTi6T6TiDSESi>SBSiAR<Si;R<Ri0R1Ri\\iZZiUXiPSySPylQ013XPLVPP4WPP5WPP6WPP7WPP8WPULSbjNVjMVjLVjKVjJVjIViHUHUiGTGTi6T6TiDSESi>SBSiAR<Si;R<Ri0R1Ri\\iZZiUXiPSySPylQ013XPLVPP4WPP5WPP6WPP7WPP8WPUMSbjNVjMVjLVjKVjJVjIViHUHUiGTGTi6T6TiDSESi>SBSiAR<Si;R<Ri0R1Ri\\iZZiUXiPSySPylQ013Xk4QSySPP9WPUKS]iJV8WjIViHUHUiGTGTi6T6Ti>SESiAR<Si;R<Ri0R1Ri\\iZZiUXiPSySPkmRySPylQ<61X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2L.T_THROW_52944_LIBENT_r9_4) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_EH_52944_LIBENT_r9_4.

Module C_XA_1fba8_1acc8_blk_w4_r11_L0.

Definition ROOT : sstate := (t_st T_Ubs2E.T_XA_1fba8_1acc8_blk_w4_r11_L0).
Definition CUTS : IMap.t template := imap_of [(131%uint63, T_Ubs2E.T_UW_1fba8_1acc8_w4_r11_pv_L0)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2E.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y_LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZPJYPPKYPPLYPLQPNYPPOYPP0ZPP1ZPP2ZPP3ZPP4ZPP5ZPP6ZPP7ZPLQP8ZPLQU3Tmj9Wj8Wj7Wj6Wj5Wj4Wj3Wj2Wj1Wj0WjOVjNVjMVjLVjKVjJVjIViFTFTi@TDTi7T9Ti>SESi<S<SiAR:Si;R<Ri0R1Ri\\iZZiUXiPSfQ0000OOOOOOOOW@FOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPPJYPPKYPPLYPM;CIOOOOOOOOOWPNYPPOYPP0ZPP1ZPP2ZPP3ZPP4ZPP5ZPP6ZPP7ZPP;SPP8ZPL0H:FB1M8>2C6TU3Tmj9Wj8Wj7Wj6Wj5Wj4Wj3Wj2Wj1Wj0WjOVjNVjMVjLVjKVjJVjIViFTFTi@TDTi7T9Ti>SESi<S<SiAR:Si;R<Ri0R1Ri\\iZZiUXiPSfQ0000OOOOOOOOW@FOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPcySPylQ<71X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2E.T_XA_1fba8_1acc8_blk_w4_r11_L0) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_XA_1fba8_1acc8_blk_w4_r11_L0.

Module C_XA_1fba8_1acc8_p682f0_w3_r10_p3h6818cc776.

Definition ROOT : sstate := (t_st T_Ubs2E.T_XA_1fba8_1acc8_p682f0_w3_r10_p3h6818cc776).
Definition CUTS : IMap.t template := imap_of [(129%uint63, T_Ubs2E.T_UW_1fba8_1acc8_w3_r10_p3h6818cc5fb_L0)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2E.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y_LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZPJYPPKYPPLYPLQPNYPPOYPP0ZPP1ZPP2ZPP3ZPP4ZPP5ZPP6ZPP7ZPLQP8ZPLQU1Tmj9Wj8Wj7Wj6Wj5Wj4Wj3Wj2Wj1Wj0WjOVjNVjMVjLVjKVjJVjIViATDTi9T9TiDSESi>SBSi<S<SiAR:Si;R<Ri0R1Ri\\iZZiUXiPSfQ0000OOOOOOOOW@FOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPPJYPPKYPPLYPM;CIOOOOOOOOOWPNYPPOYPP0ZPP1ZPP2ZPP3ZPP4ZPP5ZPP6ZPP7ZPP;SPP8ZPL0H:FB1M8>2C6TU1Tmj9Wj8Wj7Wj6Wj5Wj4Wj3Wj2Wj1Wj0WjOVjNVjMVjLVjKVjJVjIViATDTi9T9TiDSESi>SBSi<S<SiAR:Si;R<Ri0R1Ri\\iZZiUXiPSfQ0000OOOOOOOOW@FOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPcySPylQ<71X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2E.T_XA_1fba8_1acc8_p682f0_w3_r10_p3h6818cc776) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_XA_1fba8_1acc8_p682f0_w3_r10_p3h6818cc776.

Module C_XA_1fba8_1acc8_p682f0_w3_r10_p3h6824cc449.

Definition ROOT : sstate := (t_st T_Ubs2E.T_XA_1fba8_1acc8_p682f0_w3_r10_p3h6824cc449).
Definition CUTS : IMap.t template := imap_of [(130%uint63, T_Ubs2E.T_UW_1fba8_1acc8_w3_r10_p3h6824cc7f7_L0)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2E.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y_LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZPJYPPKYPPLYPLQPNYPPOYPP0ZPP1ZPP2ZPP3ZPP4ZPP5ZPP6ZPP7ZPLQP8ZPLQU2Tmj9Wj8Wj7Wj6Wj5Wj4Wj3Wj2Wj1Wj0WjOVjNVjMVjLVjKVjJVjIViATDTi9T9TiDSESi>SBSi<S<SiAR:Si;R<Ri0R1Ri\\iZZiUXiPSfQ0000OOOOOOOOW@FOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPPJYPPKYPPLYPM;CIOOOOOOOOOWPNYPPOYPP0ZPP1ZPP2ZPP3ZPP4ZPP5ZPP6ZPP7ZPP;SPP8ZPL0H:FB1M8>2C6TU2Tmj9Wj8Wj7Wj6Wj5Wj4Wj3Wj2Wj1Wj0WjOVjNVjMVjLVjKVjJVjIViATDTi9T9TiDSESi>SBSi<S<SiAR:Si;R<Ri0R1Ri\\iZZiUXiPSfQ0000OOOOOOOOW@FOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPcySPylQ<71X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2E.T_XA_1fba8_1acc8_p682f0_w3_r10_p3h6824cc449) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_XA_1fba8_1acc8_p682f0_w3_r10_p3h6824cc449.

Module C_XA_1fba8_6b647_blk_w3_r10_L0.

Definition ROOT : sstate := (t_st T_Ubs2E.T_XA_1fba8_6b647_blk_w3_r10_L0).
Definition CUTS : IMap.t template := imap_of [(134%uint63, T_Ubs2E.T_UW_1fba8_6b647_w3_r10_pv_L0)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2E.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y_LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZPJYPPKYPPLYPLQPNYPPOYPP0ZPP1ZPP2ZPP3ZPP4ZPP5ZPP6ZPP7ZPLQP8ZPLQU6Toj9Wj8Wj7Wj6Wj5Wj4Wj3Wj2Wj1Wj0WjOVjNVjMVjLVjKVjJVjIViGTGTiATETi8T:TiFSFSiCSCSi=SASi;S;Si@R9Si:R;Ri0R0Ri\\iZZiUXiPSfQ0000OOOOOOOOW@FOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPPJYPPKYPPLYPM;CIOOOOOOOOOWPNYPPOYPP0ZPP1ZPP2ZPP3ZPP4ZPP5ZPP6ZPP7ZPP:SPP8ZPL0H:FB1M8>2C6TU6Toj9Wj8Wj7Wj6Wj5Wj4Wj3Wj2Wj1Wj0WjOVjNVjMVjLVjKVjJVjIViGTGTiATETi8T:TiFSFSiCSCSi=SASi;S;Si@R9Si:R;Ri0R0Ri\\iZZiUXiPSfQ0000OOOOOOOOW@FOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPcySPylQ<71X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2E.T_XA_1fba8_6b647_blk_w3_r10_L0) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_XA_1fba8_6b647_blk_w3_r10_L0.

Module C_XA_1fba8_6b647_p682f0_w2_r9_p3h6818cc776.

Definition ROOT : sstate := (t_st T_Ubs2E.T_XA_1fba8_6b647_p682f0_w2_r9_p3h6818cc776).
Definition CUTS : IMap.t template := imap_of [(132%uint63, T_Ubs2E.T_UW_1fba8_6b647_w2_r9_p3h6818cc5fb_L0)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2E.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y_LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZPJYPPKYPPLYPLQPNYPPOYPP0ZPP1ZPP2ZPP3ZPP4ZPP5ZPP6ZPP7ZPLQP8ZPLQU4Tmj9Wj8Wj7Wj6Wj5Wj4Wj3Wj2Wj1Wj0WjOVjNVjMVjLVjKVjJVjIViBTETi:T:TiCSCSi=SASi;S;Si@R9Si:R;Ri0R0Ri\\iZZiUXiPSfQ0000OOOOOOOOW@FOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPPJYPPKYPPLYPM;CIOOOOOOOOOWPNYPPOYPP0ZPP1ZPP2ZPP3ZPP4ZPP5ZPP6ZPP7ZPP:SPP8ZPL0H:FB1M8>2C6TU4Tmj9Wj8Wj7Wj6Wj5Wj4Wj3Wj2Wj1Wj0WjOVjNVjMVjLVjKVjJVjIViBTETi:T:TiCSCSi=SASi;S;Si@R9Si:R;Ri0R0Ri\\iZZiUXiPSfQ0000OOOOOOOOW@FOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPcySPylQ<71X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2E.T_XA_1fba8_6b647_p682f0_w2_r9_p3h6818cc776) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_XA_1fba8_6b647_p682f0_w2_r9_p3h6818cc776.

Module C_XA_1fba8_6b647_p682f0_w2_r9_p3h6824cc449.

Definition ROOT : sstate := (t_st T_Ubs2E.T_XA_1fba8_6b647_p682f0_w2_r9_p3h6824cc449).
Definition CUTS : IMap.t template := imap_of [(133%uint63, T_Ubs2E.T_UW_1fba8_6b647_w2_r9_p3h6824cc7f7_L0)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2E.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y_LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZPJYPPKYPPLYPLQPNYPPOYPP0ZPP1ZPP2ZPP3ZPP4ZPP5ZPP6ZPP7ZPLQP8ZPLQU5Tmj9Wj8Wj7Wj6Wj5Wj4Wj3Wj2Wj1Wj0WjOVjNVjMVjLVjKVjJVjIViBTETi:T:TiCSCSi=SASi;S;Si@R9Si:R;Ri0R0Ri\\iZZiUXiPSfQ0000OOOOOOOOW@FOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPPJYPPKYPPLYPM;CIOOOOOOOOOWPNYPPOYPP0ZPP1ZPP2ZPP3ZPP4ZPP5ZPP6ZPP7ZPP:SPP8ZPL0H:FB1M8>2C6TU5Tmj9Wj8Wj7Wj6Wj5Wj4Wj3Wj2Wj1Wj0WjOVjNVjMVjLVjKVjJVjIViBTETi:T:TiCSCSi=SASi;S;Si@R9Si:R;Ri0R0Ri\\iZZiUXiPSfQ0000OOOOOOOOW@FOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPcySPylQ<71X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2E.T_XA_1fba8_6b647_p682f0_w2_r9_p3h6824cc449) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_XA_1fba8_6b647_p682f0_w2_r9_p3h6824cc449.

Module C_XA_1fc40_72faa_blk_w4_r11_L0.

Definition ROOT : sstate := (t_st T_Ubs2E.T_XA_1fc40_72faa_blk_w4_r11_L0).
Definition CUTS : IMap.t template := imap_of [(137%uint63, T_Ubs2E.T_UW_1fc40_72faa_w4_r11_pv_L0)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2E.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y_LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZPJYPPKYPPLYPLQPNYPPOYPP0ZPP1ZPP2ZPP3ZPP4ZPP5ZPP6ZPP7ZPLQP8ZPLQU9T0Qj9Wj8Wj7Wj6Wj5Wj4Wj3Wj2Wj1Wj0WjOVjNVjMVjLVjKVjJVjIVi8U8Ui2U6UiITKTi7T7TiFSFSiCSCSi=SASi;S;Si@R9Si:R;Ri0R0Ri\\iZZiUXiPSfQ0000OOOOOOOOW>FOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPPJYPPKYPPLYPM;CIOOOOOOOOOWPNYPPOYPP0ZPP1ZPP2ZPP3ZPP4ZPP5ZPP6ZPP7ZPP:SPP8ZPL0H:FB1M8>2C6TU9T0Qj9Wj8Wj7Wj6Wj5Wj4Wj3Wj2Wj1Wj0WjOVjNVjMVjLVjKVjJVjIVi8U8Ui2U6UiITKTi7T7TiFSFSiCSCSi=SASi;S;Si@R9Si:R;Ri0R0Ri\\iZZiUXiPSfQ0000OOOOOOOOW>FOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPcySPylQ<71X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2E.T_XA_1fc40_72faa_blk_w4_r11_L0) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_XA_1fc40_72faa_blk_w4_r11_L0.

Module C_XA_1fc40_72faa_p682f0_w3_r10_p3h6818cc776.

Definition ROOT : sstate := (t_st T_Ubs2E.T_XA_1fc40_72faa_p682f0_w3_r10_p3h6818cc776).
Definition CUTS : IMap.t template := imap_of [(135%uint63, T_Ubs2E.T_UW_1fc40_72faa_w3_r10_p3h6818cc5fb_L0)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2E.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y_LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZPJYPPKYPPLYPLQPNYPPOYPP0ZPP1ZPP2ZPP3ZPP4ZPP5ZPP6ZPP7ZPLQP8ZPLQU7Tnj9Wj8Wj7Wj6Wj5Wj4Wj3Wj2Wj1Wj0WjOVjNVjMVjLVjKVjJVjIVi3U6UiKTKTi7T7TiCSCSi=SASi;S;Si@R9Si:R;Ri0R0Ri\\iZZiUXiPSfQ0000OOOOOOOOW>FOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPPJYPPKYPPLYPM;CIOOOOOOOOOWPNYPPOYPP0ZPP1ZPP2ZPP3ZPP4ZPP5ZPP6ZPP7ZPP:SPP8ZPL0H:FB1M8>2C6TU7Tnj9Wj8Wj7Wj6Wj5Wj4Wj3Wj2Wj1Wj0WjOVjNVjMVjLVjKVjJVjIVi3U6UiKTKTi7T7TiCSCSi=SASi;S;Si@R9Si:R;Ri0R0Ri\\iZZiUXiPSfQ0000OOOOOOOOW>FOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPcySPylQ<71X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2E.T_XA_1fc40_72faa_p682f0_w3_r10_p3h6818cc776) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_XA_1fc40_72faa_p682f0_w3_r10_p3h6818cc776.

Module C_XA_1fc40_72faa_p682f0_w3_r10_p3h6824cc449.

Definition ROOT : sstate := (t_st T_Ubs2E.T_XA_1fc40_72faa_p682f0_w3_r10_p3h6824cc449).
Definition CUTS : IMap.t template := imap_of [(136%uint63, T_Ubs2E.T_UW_1fc40_72faa_w3_r10_p3h6824cc7f7_L0)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2E.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y_LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZPJYPPKYPPLYPLQPNYPPOYPP0ZPP1ZPP2ZPP3ZPP4ZPP5ZPP6ZPP7ZPLQP8ZPLQU8Tnj9Wj8Wj7Wj6Wj5Wj4Wj3Wj2Wj1Wj0WjOVjNVjMVjLVjKVjJVjIVi3U6UiKTKTi7T7TiCSCSi=SASi;S;Si@R9Si:R;Ri0R0Ri\\iZZiUXiPSfQ0000OOOOOOOOW>FOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPPJYPPKYPPLYPM;CIOOOOOOOOOWPNYPPOYPP0ZPP1ZPP2ZPP3ZPP4ZPP5ZPP6ZPP7ZPP:SPP8ZPL0H:FB1M8>2C6TU8Tnj9Wj8Wj7Wj6Wj5Wj4Wj3Wj2Wj1Wj0WjOVjNVjMVjLVjKVjJVjIVi3U6UiKTKTi7T7TiCSCSi=SASi;S;Si@R9Si:R;Ri0R0Ri\\iZZiUXiPSfQ0000OOOOOOOOW>FOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPcySPylQ<71X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2E.T_XA_1fc40_72faa_p682f0_w3_r10_p3h6824cc449) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_XA_1fc40_72faa_p682f0_w3_r10_p3h6824cc449.

Module C_XA_1fc40_991f7_blk_w5_r12_L0.

Definition ROOT : sstate := (t_st T_Ubs2E.T_XA_1fc40_991f7_blk_w5_r12_L0).
Definition CUTS : IMap.t template := imap_of [(140%uint63, T_Ubs2E.T_UW_1fc40_991f7_w5_r12_pv_L0)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2E.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y_LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZPJYPPKYPPLYPLQPNYPPOYPP0ZPP1ZPP2ZPP3ZPP4ZPP5ZPP6ZPP7ZPLQP8ZPLQU<Tnj9Wj8Wj7Wj6Wj5Wj4Wj3Wj2Wj1Wj0WjOVjNVjMVjLVjKVjJVjIVi7U7Ui1U5UiHTJTi6T6Ti>SESi<S<SiAR:Si;R<Ri0R1Ri\\iZZiUXiPSfQ0000OOOOOOOOW>FOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPPJYPPKYPPLYPM;CIOOOOOOOOOWPNYPPOYPP0ZPP1ZPP2ZPP3ZPP4ZPP5ZPP6ZPP7ZPP;SPP8ZPL0H:FB1M8>2C6TU<Tnj9Wj8Wj7Wj6Wj5Wj4Wj3Wj2Wj1Wj0WjOVjNVjMVjLVjKVjJVjIVi7U7Ui1U5UiHTJTi6T6Ti>SESi<S<SiAR:Si;R<Ri0R1Ri\\iZZiUXiPSfQ0000OOOOOOOOW>FOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPcySPylQ<71X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2E.T_XA_1fc40_991f7_blk_w5_r12_L0) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_XA_1fc40_991f7_blk_w5_r12_L0.

Module C_XA_1fc40_991f7_p682f0_w4_r11_p3h6818cc776.

Definition ROOT : sstate := (t_st T_Ubs2E.T_XA_1fc40_991f7_p682f0_w4_r11_p3h6818cc776).
Definition CUTS : IMap.t template := imap_of [(138%uint63, T_Ubs2E.T_UW_1fc40_991f7_w4_r11_p3h6818cc5fb_L0)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2E.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y_LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZPJYPPKYPPLYPLQPNYPPOYPP0ZPP1ZPP2ZPP3ZPP4ZPP5ZPP6ZPP7ZPLQP8ZPLQU:Tnj9Wj8Wj7Wj6Wj5Wj4Wj3Wj2Wj1Wj0WjOVjNVjMVjLVjKVjJVjIVi2U5UiJTJTi6T6TiDSESi>SBSi<S<SiAR:Si;R<Ri0R1Ri\\iZZiUXiPSfQ0000OOOOOOOOW>FOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPPJYPPKYPPLYPM;CIOOOOOOOOOWPNYPPOYPP0ZPP1ZPP2ZPP3ZPP4ZPP5ZPP6ZPP7ZPP;SPP8ZPL0H:FB1M8>2C6TU:Tnj9Wj8Wj7Wj6Wj5Wj4Wj3Wj2Wj1Wj0WjOVjNVjMVjLVjKVjJVjIVi2U5UiJTJTi6T6TiDSESi>SBSi<S<SiAR:Si;R<Ri0R1Ri\\iZZiUXiPSfQ0000OOOOOOOOW>FOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPcySPylQ<71X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2E.T_XA_1fc40_991f7_p682f0_w4_r11_p3h6818cc776) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_XA_1fc40_991f7_p682f0_w4_r11_p3h6818cc776.

Module C_XA_1fc40_991f7_p682f0_w4_r11_p3h6824cc449.

Definition ROOT : sstate := (t_st T_Ubs2E.T_XA_1fc40_991f7_p682f0_w4_r11_p3h6824cc449).
Definition CUTS : IMap.t template := imap_of [(139%uint63, T_Ubs2E.T_UW_1fc40_991f7_w4_r11_p3h6824cc7f7_L0)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2E.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y_LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZPJYPPKYPPLYPLQPNYPPOYPP0ZPP1ZPP2ZPP3ZPP4ZPP5ZPP6ZPP7ZPLQP8ZPLQU;Tnj9Wj8Wj7Wj6Wj5Wj4Wj3Wj2Wj1Wj0WjOVjNVjMVjLVjKVjJVjIVi2U5UiJTJTi6T6TiDSESi>SBSi<S<SiAR:Si;R<Ri0R1Ri\\iZZiUXiPSfQ0000OOOOOOOOW>FOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPPJYPPKYPPLYPM;CIOOOOOOOOOWPNYPPOYPP0ZPP1ZPP2ZPP3ZPP4ZPP5ZPP6ZPP7ZPP;SPP8ZPL0H:FB1M8>2C6TU;Tnj9Wj8Wj7Wj6Wj5Wj4Wj3Wj2Wj1Wj0WjOVjNVjMVjLVjKVjJVjIVi2U5UiJTJTi6T6TiDSESi>SBSi<S<SiAR:Si;R<Ri0R1Ri\\iZZiUXiPSfQ0000OOOOOOOOW>FOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPcySPylQ<71X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2E.T_XA_1fc40_991f7_p682f0_w4_r11_p3h6824cc449) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_XA_1fc40_991f7_p682f0_w4_r11_p3h6824cc449.

Module C_XA_2037c_01284_blk_w6_r13_L0.

Definition ROOT : sstate := (t_st T_Ubs2E.T_XA_2037c_01284_blk_w6_r13_L0).
Definition CUTS : IMap.t template := imap_of [(126%uint63, T_Ubs2E.T_THROW_n52944_XA_2037c_01284_blk_w6_r13_L0_1); (143%uint63, T_Ubs2E.T_UW_2037c_01284_w7_r14_pv_L0)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2E.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y_LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZPLVPPMVPPNVPPOVPP0WPP1WPP2WPP3WPP4WPP5WPP6WPP7WPP8WPP9WPP:WPUNSmj8Wj7Wj6Wj5Wj4Wj3Wj2Wj1Wj0WjOVjNVjMVjLVjKVjJViIVIViIUIUiHTHTi7T7TiFSFSiCSCSi=SASi@R;Si:R;Ri0R0Ri\\iZZiUXiPSySPP;WPP=ZPP>ZPP?ZPLQPAZPPBZPPCZPPDZPPEZPPFZPPGZPPHZPPIZPPJZPLQPKZPPMVPPNVPLQP6WPP7WPP8WPP9WPU?T7QjAWj@Wj?Wj>Wj=Wj<Wj;Wj:Wj9Wj8Wj7Wj6Wj5Wj4Wj3Wj2Wj1Wj0WjOVjNVjMVjLVjKVjJViIVIViIUIUiHTHTi7T7TiFSFSiCSCSi=SASi;S;Si@R9Si:R;Ri0R0Ri\\iZZiUXiPSfQ0000OOOOOOOOWNEOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPP;WPP=ZPP>ZPP?ZPM;CIOOOOOOOOOWPAZPPBZPPCZPPDZPPEZPPFZPPGZPPHZPPIZPPJZPP:SPPKZPPMVPPNVPL0H:FB1M8>2C6TP6WPP7WPP8WPP9WPU?T7QjAWj@Wj?Wj>Wj=Wj<Wj;Wj:Wj9Wj8Wj7Wj6Wj5Wj4Wj3Wj2Wj1Wj0WjOVjNVjMVjLVjKVjJViIVIViIUIUiHTHTi7T7TiFSFSiCSCSi=SASi;S;Si@R9Si:R;Ri0R0Ri\\iZZiUXiPSfQ0000OOOOOOOOWNEOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPcySPylQ@G4ZySPknRySPylQ<71X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2E.T_XA_2037c_01284_blk_w6_r13_L0) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_XA_2037c_01284_blk_w6_r13_L0.

Module C_XA_2037c_01284_p682f0_w5_r12_p3h6818cc776.

Definition ROOT : sstate := (t_st T_Ubs2E.T_XA_2037c_01284_p682f0_w5_r12_p3h6818cc776).
Definition CUTS : IMap.t template := imap_of [(127%uint63, T_Ubs2E.T_THROW_n52944_XA_2037c_01284_p682f0_w5_r12_p3h6818cc776_1); (141%uint63, T_Ubs2E.T_UW_2037c_01284_w6_r13_p3h6818ccedd_L0)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2E.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y_LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZPKVPPLVPPMVPPNVPPOVPP0WPP1WPP2WPP3WPP4WPP5WPP6WPP7WPP8WPP9WPUOSkj7Wj6Wj5Wj4Wj3Wj2Wj1Wj0WjOVjNVjMVjLVjKVjJVjIViIUIUiHTHTi7T7TiCSCSi=SASi@R;Si:R;Ri0R0Ri\\iZZiUXiPSySPP:WPP<ZPP=ZPP>ZPLQP@ZPPAZPPBZPPCZPPDZPPEZPPFZPPGZPPHZPPIZPLQPJZPPLVPPMVPLQP5WPP6WPP7WPP8WPU=T5Qj@Wj?Wj>Wj=Wj<Wj;Wj:Wj9Wj8Wj7Wj6Wj5Wj4Wj3Wj2Wj1Wj0WjOVjNVjMVjLVjKVjJVjIViIUIUiHTHTi7T7TiCSCSi=SASi;S;Si@R9Si:R;Ri0R0Ri\\iZZiUXiPSfQ0000OOOOOOOOWNEOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPP:WPP<ZPP=ZPP>ZPM;CIOOOOOOOOOWP@ZPPAZPPBZPPCZPPDZPPEZPPFZPPGZPPHZPPIZPP:SPPJZPPLVPPMVPL0H:FB1M8>2C6TP5WPP6WPP7WPP8WPU=T5Qj@Wj?Wj>Wj=Wj<Wj;Wj:Wj9Wj8Wj7Wj6Wj5Wj4Wj3Wj2Wj1Wj0WjOVjNVjMVjLVjKVjJVjIViIUIUiHTHTi7T7TiCSCSi=SASi;S;Si@R9Si:R;Ri0R0Ri\\iZZiUXiPSfQ0000OOOOOOOOWNEOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPcySPylQ@G4ZySPknRySPylQ<71X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2E.T_XA_2037c_01284_p682f0_w5_r12_p3h6818cc776) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_XA_2037c_01284_p682f0_w5_r12_p3h6818cc776.

Module C_XA_2037c_01284_p682f0_w5_r12_p3h6824cc449.

Definition ROOT : sstate := (t_st T_Ubs2E.T_XA_2037c_01284_p682f0_w5_r12_p3h6824cc449).
Definition CUTS : IMap.t template := imap_of [(128%uint63, T_Ubs2E.T_THROW_n52944_XA_2037c_01284_p682f0_w5_r12_p3h6824cc449_1); (142%uint63, T_Ubs2E.T_UW_2037c_01284_w6_r13_p3h6824cca88_L0)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2E.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y_LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZPKVPPLVPPMVPPNVPPOVPP0WPP1WPP2WPP3WPP4WPP5WPP6WPP7WPP8WPP9WPU0Tkj7Wj6Wj5Wj4Wj3Wj2Wj1Wj0WjOVjNVjMVjLVjKVjJVjIViIUIUiHTHTi7T7TiCSCSi=SASi@R;Si:R;Ri0R0Ri\\iZZiUXiPSySPP:WPP<ZPP=ZPP>ZPLQP@ZPPAZPPBZPPCZPPDZPPEZPPFZPPGZPPHZPPIZPLQPJZPPLVPPMVPLQP5WPP6WPP7WPP8WPU>T5Qj@Wj?Wj>Wj=Wj<Wj;Wj:Wj9Wj8Wj7Wj6Wj5Wj4Wj3Wj2Wj1Wj0WjOVjNVjMVjLVjKVjJVjIViIUIUiHTHTi7T7TiCSCSi=SASi;S;Si@R9Si:R;Ri0R0Ri\\iZZiUXiPSfQ0000OOOOOOOOWNEOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPP:WPP<ZPP=ZPP>ZPM;CIOOOOOOOOOWP@ZPPAZPPBZPPCZPPDZPPEZPPFZPPGZPPHZPPIZPP:SPPJZPPLVPPMVPL0H:FB1M8>2C6TP5WPP6WPP7WPP8WPU>T5Qj@Wj?Wj>Wj=Wj<Wj;Wj:Wj9Wj8Wj7Wj6Wj5Wj4Wj3Wj2Wj1Wj0WjOVjNVjMVjLVjKVjJVjIViIUIUiHTHTi7T7TiCSCSi=SASi;S;Si@R9Si:R;Ri0R0Ri\\iZZiUXiPSfQ0000OOOOOOOOWNEOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPcySPylQ@G4ZySPknRySPylQ<71X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2E.T_XA_2037c_01284_p682f0_w5_r12_p3h6824cc449) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_XA_2037c_01284_p682f0_w5_r12_p3h6824cc449.

Module C_XA_52944_67536_blk_w6_r13_L0.

Definition ROOT : sstate := (t_st T_Ubs2E.T_XA_52944_67536_blk_w6_r13_L0).
Definition CUTS : IMap.t template := imap_of [(146%uint63, T_Ubs2E.T_UW_52944_67536_w6_r13_pv_L0)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2E.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y_LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZPJYPPKYPPLYPLQPNYPPOYPP0ZPP1ZPP2ZPP3ZPP4ZPP5ZPP6ZPP7ZPLQP8ZPLQUBToj9Wj8Wj7Wj6Wj5Wj4Wj3Wj2Wj1Wj0WjOVjNVjMVjLVjKVjJVjIVi8V8Vi2V6ViIUKUiGTGTi6T6Ti>SESi<S<SiAR:Si;R<Ri0R1Ri\\iZZiUXiPSfQ0000OOOOOOOOWNEOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPPJYPPKYPPLYPM;CIOOOOOOOOOWPNYPPOYPP0ZPP1ZPP2ZPP3ZPP4ZPP5ZPP6ZPP7ZPP;SPP8ZPL0H:FB1M8>2C6TUBToj9Wj8Wj7Wj6Wj5Wj4Wj3Wj2Wj1Wj0WjOVjNVjMVjLVjKVjJVjIVi8V8Vi2V6ViIUKUiGTGTi6T6Ti>SESi<S<SiAR:Si;R<Ri0R1Ri\\iZZiUXiPSfQ0000OOOOOOOOWNEOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPcySPylQ<71X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2E.T_XA_52944_67536_blk_w6_r13_L0) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_XA_52944_67536_blk_w6_r13_L0.

Module C_XA_52944_67536_p682f0_w5_r12_p3h6818cc776.

Definition ROOT : sstate := (t_st T_Ubs2E.T_XA_52944_67536_p682f0_w5_r12_p3h6818cc776).
Definition CUTS : IMap.t template := imap_of [(144%uint63, T_Ubs2E.T_UW_52944_67536_w5_r12_p3h6818cc5fb_L0)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2E.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y_LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZPJYPPKYPPLYPLQPNYPPOYPP0ZPP1ZPP2ZPP3ZPP4ZPP5ZPP6ZPP7ZPLQP8ZPLQU@Toj9Wj8Wj7Wj6Wj5Wj4Wj3Wj2Wj1Wj0WjOVjNVjMVjLVjKVjJVjIVi3V6ViKUKUiGTGTi6T6TiDSESi>SBSi<S<SiAR:Si;R<Ri0R1Ri\\iZZiUXiPSfQ0000OOOOOOOOWNEOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPPJYPPKYPPLYPM;CIOOOOOOOOOWPNYPPOYPP0ZPP1ZPP2ZPP3ZPP4ZPP5ZPP6ZPP7ZPP;SPP8ZPL0H:FB1M8>2C6TU@Toj9Wj8Wj7Wj6Wj5Wj4Wj3Wj2Wj1Wj0WjOVjNVjMVjLVjKVjJVjIVi3V6ViKUKUiGTGTi6T6TiDSESi>SBSi<S<SiAR:Si;R<Ri0R1Ri\\iZZiUXiPSfQ0000OOOOOOOOWNEOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPcySPylQ<71X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2E.T_XA_52944_67536_p682f0_w5_r12_p3h6818cc776) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_XA_52944_67536_p682f0_w5_r12_p3h6818cc776.

Module C_XA_52944_67536_p682f0_w5_r12_p3h6824cc449.

Definition ROOT : sstate := (t_st T_Ubs2E.T_XA_52944_67536_p682f0_w5_r12_p3h6824cc449).
Definition CUTS : IMap.t template := imap_of [(145%uint63, T_Ubs2E.T_UW_52944_67536_w5_r12_p3h6824cc7f7_L0)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2E.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y_LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZPJYPPKYPPLYPLQPNYPPOYPP0ZPP1ZPP2ZPP3ZPP4ZPP5ZPP6ZPP7ZPLQP8ZPLQUAToj9Wj8Wj7Wj6Wj5Wj4Wj3Wj2Wj1Wj0WjOVjNVjMVjLVjKVjJVjIVi3V6ViKUKUiGTGTi6T6TiDSESi>SBSi<S<SiAR:Si;R<Ri0R1Ri\\iZZiUXiPSfQ0000OOOOOOOOWNEOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPPJYPPKYPPLYPM;CIOOOOOOOOOWPNYPPOYPP0ZPP1ZPP2ZPP3ZPP4ZPP5ZPP6ZPP7ZPP;SPP8ZPL0H:FB1M8>2C6TUAToj9Wj8Wj7Wj6Wj5Wj4Wj3Wj2Wj1Wj0WjOVjNVjMVjLVjKVjJVjIVi3V6ViKUKUiGTGTi6T6TiDSESi>SBSi<S<SiAR:Si;R<Ri0R1Ri\\iZZiUXiPSfQ0000OOOOOOOOWNEOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPcySPylQ<71X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2E.T_XA_52944_67536_p682f0_w5_r12_p3h6824cc449) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_XA_52944_67536_p682f0_w5_r12_p3h6824cc449.

Module C_XA_52944_a198b_blk_w5_r12_L0.

Definition ROOT : sstate := (t_st T_Ubs2E.T_XA_52944_a198b_blk_w5_r12_L0).
Definition CUTS : IMap.t template := imap_of [(149%uint63, T_Ubs2E.T_UW_52944_a198b_w5_r12_pv_L0)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2E.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y_LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZPJYPPKYPPLYPLQPNYPPOYPP0ZPP1ZPP2ZPP3ZPP4ZPP5ZPP6ZPP7ZPLQP8ZPLQUET1Qj9Wj8Wj7Wj6Wj5Wj4Wj3Wj2Wj1Wj0WjOVjNVjMVjLVjKVjJVjIVi9V9Vi3V7ViJULUiHTHTi7T7TiFSFSiCSCSi=SASi;S;Si@R9Si:R;Ri0R0Ri\\iZZiUXiPSfQ0000OOOOOOOOWNEOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPPJYPPKYPPLYPM;CIOOOOOOOOOWPNYPPOYPP0ZPP1ZPP2ZPP3ZPP4ZPP5ZPP6ZPP7ZPP:SPP8ZPL0H:FB1M8>2C6TUET1Qj9Wj8Wj7Wj6Wj5Wj4Wj3Wj2Wj1Wj0WjOVjNVjMVjLVjKVjJVjIVi9V9Vi3V7ViJULUiHTHTi7T7TiFSFSiCSCSi=SASi;S;Si@R9Si:R;Ri0R0Ri\\iZZiUXiPSfQ0000OOOOOOOOWNEOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPcySPylQ<71X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2E.T_XA_52944_a198b_blk_w5_r12_L0) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_XA_52944_a198b_blk_w5_r12_L0.

Module C_XA_52944_a198b_p682f0_w4_r11_p3h6818cc776.

Definition ROOT : sstate := (t_st T_Ubs2E.T_XA_52944_a198b_p682f0_w4_r11_p3h6818cc776).
Definition CUTS : IMap.t template := imap_of [(147%uint63, T_Ubs2E.T_UW_52944_a198b_w4_r11_p3h6818cc5fb_L0)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2E.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y_LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZPJYPPKYPPLYPLQPNYPPOYPP0ZPP1ZPP2ZPP3ZPP4ZPP5ZPP6ZPP7ZPLQP8ZPLQUCToj9Wj8Wj7Wj6Wj5Wj4Wj3Wj2Wj1Wj0WjOVjNVjMVjLVjKVjJVjIVi4V7ViLULUiHTHTi7T7TiCSCSi=SASi;S;Si@R9Si:R;Ri0R0Ri\\iZZiUXiPSfQ0000OOOOOOOOWNEOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPPJYPPKYPPLYPM;CIOOOOOOOOOWPNYPPOYPP0ZPP1ZPP2ZPP3ZPP4ZPP5ZPP6ZPP7ZPP:SPP8ZPL0H:FB1M8>2C6TUCToj9Wj8Wj7Wj6Wj5Wj4Wj3Wj2Wj1Wj0WjOVjNVjMVjLVjKVjJVjIVi4V7ViLULUiHTHTi7T7TiCSCSi=SASi;S;Si@R9Si:R;Ri0R0Ri\\iZZiUXiPSfQ0000OOOOOOOOWNEOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPcySPylQ<71X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2E.T_XA_52944_a198b_p682f0_w4_r11_p3h6818cc776) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_XA_52944_a198b_p682f0_w4_r11_p3h6818cc776.

Module C_XA_52944_a198b_p682f0_w4_r11_p3h6824cc449.

Definition ROOT : sstate := (t_st T_Ubs2E.T_XA_52944_a198b_p682f0_w4_r11_p3h6824cc449).
Definition CUTS : IMap.t template := imap_of [(148%uint63, T_Ubs2E.T_UW_52944_a198b_w4_r11_p3h6824cc7f7_L0)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2E.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y_LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZPJYPPKYPPLYPLQPNYPPOYPP0ZPP1ZPP2ZPP3ZPP4ZPP5ZPP6ZPP7ZPLQP8ZPLQUDToj9Wj8Wj7Wj6Wj5Wj4Wj3Wj2Wj1Wj0WjOVjNVjMVjLVjKVjJVjIVi4V7ViLULUiHTHTi7T7TiCSCSi=SASi;S;Si@R9Si:R;Ri0R0Ri\\iZZiUXiPSfQ0000OOOOOOOOWNEOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPPJYPPKYPPLYPM;CIOOOOOOOOOWPNYPPOYPP0ZPP1ZPP2ZPP3ZPP4ZPP5ZPP6ZPP7ZPP:SPP8ZPL0H:FB1M8>2C6TUDToj9Wj8Wj7Wj6Wj5Wj4Wj3Wj2Wj1Wj0WjOVjNVjMVjLVjKVjJVjIVi4V7ViLULUiHTHTi7T7TiCSCSi=SASi;S;Si@R9Si:R;Ri0R0Ri\\iZZiUXiPSfQ0000OOOOOOOOWNEOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPcySPylQ<71X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2E.T_XA_52944_a198b_p682f0_w4_r11_p3h6824cc449) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_XA_52944_a198b_p682f0_w4_r11_p3h6824cc449.

Module C_XA_52944_d4b36_blk_w7_r14_L0.

Definition ROOT : sstate := (t_st T_Ubs2E.T_XA_52944_d4b36_blk_w7_r14_L0).
Definition CUTS : IMap.t template := imap_of [(152%uint63, T_Ubs2E.T_UW_52944_d4b36_w7_r14_pv_L0)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2E.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y_LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZP:ZPP;ZPP<ZPLQP>ZPP?ZPP@ZPPAZPPBZPPCZPPDZPPEZPPFZPPGZPLQPHZPPJVPPKVPPLVPLQP3WPP4WPP5WPP6WPP7WPUHT6QjBWjAWj@Wj?Wj>Wj=Wj<Wj;Wj:Wj9Wj8Wj7Wj6Wj5Wj4Wj3Wj2Wj1Wj0WjOVjNVjMVjLVjKVjJViIVIViHUHUiGTGTi6T6Ti>SESi<S<SiAR:Si;R<Ri0R1Ri\\iZZiUXiPSfQ0000OOOOOOOOW>EOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPP:ZPP;ZPP<ZPM;CIOOOOOOOOOWP>ZPP?ZPP@ZPPAZPPBZPPCZPPDZPPEZPPFZPPGZPP;SPPHZPPJVPPKVPPLVPL0H:FB1M8>2C6TP3WPP4WPP5WPP6WPP7WPUHT6QjBWjAWj@Wj?Wj>Wj=Wj<Wj;Wj:Wj9Wj8Wj7Wj6Wj5Wj4Wj3Wj2Wj1Wj0WjOVjNVjMVjLVjKVjJViIVIViHUHUiGTGTi6T6Ti>SESi<S<SiAR:Si;R<Ri0R1Ri\\iZZiUXiPSfQ0000OOOOOOOOW>EOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPcySPylQ<71X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2E.T_XA_52944_d4b36_blk_w7_r14_L0) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_XA_52944_d4b36_blk_w7_r14_L0.

Module C_XA_52944_d4b36_p682f0_w6_r13_p3h6818cc776.

Definition ROOT : sstate := (t_st T_Ubs2E.T_XA_52944_d4b36_p682f0_w6_r13_p3h6818cc776).
Definition CUTS : IMap.t template := imap_of [(150%uint63, T_Ubs2E.T_UW_52944_d4b36_w6_r13_p3h6818cc5fb_L0)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2E.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y_LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZP0ZPP1ZPP2ZPLQP4ZPP5ZPP6ZPP7ZPP8ZPP9ZPP:ZPP;ZPP<ZPP=ZPLQP>ZPPIVPLQPJVPPKVPPLVPPMVPUFT3Qj>Wj=Wj<Wj;Wj:Wj9Wj8Wj7Wj6Wj5Wj4Wj3Wj2Wj1Wj0WjOVjNVjMVjLVjKVjJVjIViHUHUiGTGTi6T6TiDSESi>SBSi<S<SiAR:Si;R<Ri0R1Ri\\iZZiUXiPSfQ0000OOOOOOOOW>EOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPP0ZPP1ZPP2ZPM;CIOOOOOOOOOWP4ZPP5ZPP6ZPP7ZPP8ZPP9ZPP:ZPP;ZPP<ZPP=ZPP;SPP>ZPPIVPL0H:FB1M8>2C6TPJVPPKVPPLVPPMVPUFT3Qj>Wj=Wj<Wj;Wj:Wj9Wj8Wj7Wj6Wj5Wj4Wj3Wj2Wj1Wj0WjOVjNVjMVjLVjKVjJVjIViHUHUiGTGTi6T6TiDSESi>SBSi<S<SiAR:Si;R<Ri0R1Ri\\iZZiUXiPSfQ0000OOOOOOOOW>EOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPcySPylQ<71X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2E.T_XA_52944_d4b36_p682f0_w6_r13_p3h6818cc776) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_XA_52944_d4b36_p682f0_w6_r13_p3h6818cc776.

Module C_XA_52944_d4b36_p682f0_w6_r13_p3h6824cc449.

Definition ROOT : sstate := (t_st T_Ubs2E.T_XA_52944_d4b36_p682f0_w6_r13_p3h6824cc449).
Definition CUTS : IMap.t template := imap_of [(151%uint63, T_Ubs2E.T_UW_52944_d4b36_w6_r13_p3h6824cc7f7_L0)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2E.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y_LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZP0ZPP1ZPP2ZPLQP4ZPP5ZPP6ZPP7ZPP8ZPP9ZPP:ZPP;ZPP<ZPP=ZPLQP>ZPPIVPLQPJVPPKVPPLVPPMVPUGT3Qj>Wj=Wj<Wj;Wj:Wj9Wj8Wj7Wj6Wj5Wj4Wj3Wj2Wj1Wj0WjOVjNVjMVjLVjKVjJVjIViHUHUiGTGTi6T6TiDSESi>SBSi<S<SiAR:Si;R<Ri0R1Ri\\iZZiUXiPSfQ0000OOOOOOOOW>EOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPP0ZPP1ZPP2ZPM;CIOOOOOOOOOWP4ZPP5ZPP6ZPP7ZPP8ZPP9ZPP:ZPP;ZPP<ZPP=ZPP;SPP>ZPPIVPL0H:FB1M8>2C6TPJVPPKVPPLVPPMVPUGT3Qj>Wj=Wj<Wj;Wj:Wj9Wj8Wj7Wj6Wj5Wj4Wj3Wj2Wj1Wj0WjOVjNVjMVjLVjKVjJVjIViHUHUiGTGTi6T6TiDSESi>SBSi<S<SiAR:Si;R<Ri0R1Ri\\iZZiUXiPSfQ0000OOOOOOOOW>EOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPcySPylQ<71X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2E.T_XA_52944_d4b36_p682f0_w6_r13_p3h6824cc449) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_XA_52944_d4b36_p682f0_w6_r13_p3h6824cc449.

Module C_THROW_n52944_XA_2037c_01284_blk_w6_r13_L0_1.

Definition ROOT : sstate := (t_st T_Ubs2E.T_THROW_n52944_XA_2037c_01284_blk_w6_r13_L0_1).
Definition CUTS : IMap.t template := imap_of [(157%uint63, T_Ubs2E.T_XA_52944_a3813_blk_w7_r14_L0); (158%uint63, T_Ubs2E.T_XA_52944_a3813_p682f0_w6_r13_p3h6818cc776); (159%uint63, T_Ubs2E.T_XA_52944_a3813_p682f0_w6_r13_p3h6824cc449)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2E.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y_LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZP<WPPDWPPEWPPFWPPGWPPHWPUNTcjOVjNVjMVjLVjKVjJViIVIViIUIUiHTHTi7T7TiCSCSi=SASi@R;Si:R;Ri0R0Ri\\iZZiUXiPSySPylQ013XP<WPPDWPPEWPPFWPPGWPPHWPUNTcjOVjNVjMVjLVjKVjJViIVIViIUIUiHTHTi7T7TiCSCSi=SASi@R;Si:R;Ri0R0Ri\\iZZiUXiPSySPylQ013XP<WPPDWPPEWPPFWPPGWPPHWPUOTcjOVjNVjMVjLVjKVjJViIVIViIUIUiHTHTi7T7TiCSCSi=SASi@R;Si:R;Ri0R0Ri\\iZZiUXiPSySPylQ013Xk4QSySPPIWPP:WPP;WPP<WPP=WPP>WPP?WPP@WPPAWPPBWPPCWPPDWPPEWPPFWPPGWPPHWPUMTnj9Wj8Wj7Wj6Wj5Wj4Wj3Wj2Wj1Wj0WjOVjNVjMVjLVjKVjJViIVIViIUIUiHTHTi7T7TiFSFSiCSCSi=SASi@R;Si:R;Ri0R0Ri\\iZZiUXiPSySPkmRySPylQ<61X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2E.T_THROW_n52944_XA_2037c_01284_blk_w6_r13_L0_1) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_THROW_n52944_XA_2037c_01284_blk_w6_r13_L0_1.

Module C_THROW_n52944_XA_2037c_01284_p682f0_w5_r12_p3h6818cc776_1.

Definition ROOT : sstate := (t_st T_Ubs2E.T_THROW_n52944_XA_2037c_01284_p682f0_w5_r12_p3h6818cc776_1).
Definition CUTS : IMap.t template := imap_of [(155%uint63, T_Ubs2E.T_XA_52944_8ec98_blk_w6_r13_L0); (156%uint63, T_Ubs2E.T_XA_52944_8ec98_p68250_w5_r12_p3h6818cc99d)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2E.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y_LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZP;WPPCWPPDWPPEWPPFWPPGWPULTbjNVjMVjLVjKVjJVjIViIUIUiHTHTi7T7TiCSCSi=SASi@R;Si:R;Ri0R0Ri\\iZZiUXiPSySPylQ013XySPPHWPP9WPP:WPP;WPP<WPP=WPP>WPP?WPP@WPPAWPPBWPPCWPPDWPPEWPPFWPPGWPUKTlj8Wj7Wj6Wj5Wj4Wj3Wj2Wj1Wj0WjOVjNVjMVjLVjKVjJVjIViIUIUiHTHTi7T7TiCSCSi=SASi@R;Si:R;Ri0R0Ri\\iZZiUXiPSySPkmRySPylQ<61X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2E.T_THROW_n52944_XA_2037c_01284_p682f0_w5_r12_p3h6818cc776_1) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_THROW_n52944_XA_2037c_01284_p682f0_w5_r12_p3h6818cc776_1.

Module C_THROW_n52944_XA_2037c_01284_p682f0_w5_r12_p3h6824cc449_1.

Definition ROOT : sstate := (t_st T_Ubs2E.T_THROW_n52944_XA_2037c_01284_p682f0_w5_r12_p3h6824cc449_1).
Definition CUTS : IMap.t template := imap_of [(153%uint63, T_Ubs2E.T_XA_52944_61dc2_blk_w6_r13_L0); (154%uint63, T_Ubs2E.T_XA_52944_61dc2_p68250_w5_r12_p3h6818cc132)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2E.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y_LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZP;WPPCWPPDWPPEWPPFWPPGWPUJTbjNVjMVjLVjKVjJVjIViIUIUiHTHTi7T7TiCSCSi=SASi@R;Si:R;Ri0R0Ri\\iZZiUXiPSySPylQ013XySPPHWPP9WPP:WPP;WPP<WPP=WPP>WPP?WPP@WPPAWPPBWPPCWPPDWPPEWPPFWPPGWPUITlj8Wj7Wj6Wj5Wj4Wj3Wj2Wj1Wj0WjOVjNVjMVjLVjKVjJVjIViIUIUiHTHTi7T7TiCSCSi=SASi@R;Si:R;Ri0R0Ri\\iZZiUXiPSySPkmRySPylQ<61X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2E.T_THROW_n52944_XA_2037c_01284_p682f0_w5_r12_p3h6824cc449_1) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_THROW_n52944_XA_2037c_01284_p682f0_w5_r12_p3h6824cc449_1.

Module C_UW_1fba8_1acc8_w3_r10_p3h6818cc5fb_L0.

Definition ROOT : sstate := (t_st T_Ubs2E.T_UW_1fba8_1acc8_w3_r10_p3h6818cc5fb_L0).
Definition CUTS : IMap.t template := imap_of [(101%uint63, T_Ubs2E.T_FINAL_r9)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2E.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y_LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZY`LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X<I7XD58X4<5Y4F5Y8F5Y@@<Y<G4ZLLHMSL<G0]LHRP9TPL@;0]L<G0]L<<0]L<<0]LPL0TLHRPATPPBTPPCTPPDTPPARPPBRPPCRPPDRPPERPPFRPPGRPPHRPPIRPPJRPPKRPPLRPPMRPPNRPPORPP0SPP1SPP2SPP3SPP4SPP7WPLQP9oPU5S@QjKTjJTjITjHTjGTjFTjETjDTjCTjBTjATj@Tj?Tj>Tj=Tj<Tj;Tj:Tj9Tj8Tj7Tj6Tj5Tj4Tj3Tj2Tj1Tj0TjOSjNSjMSjLSjKSjJSjISjHSjGSjFSiDSESi>SBSi<S<Si5S:Si;R<Ri0R1Ri\\iZZiUXiPSk5QQfQ0000OOOOOOOOW6OOOOOOOOOOOWySPylQ<;3XySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOW@FOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOW@FOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOW@FOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPySQ"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2E.T_UW_1fba8_1acc8_w3_r10_p3h6818cc5fb_L0) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_UW_1fba8_1acc8_w3_r10_p3h6818cc5fb_L0.

Module C_UW_1fba8_1acc8_w3_r10_p3h6824cc7f7_L0.

Definition ROOT : sstate := (t_st T_Ubs2E.T_UW_1fba8_1acc8_w3_r10_p3h6824cc7f7_L0).
Definition CUTS : IMap.t template := imap_of [(101%uint63, T_Ubs2E.T_FINAL_r9)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2E.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y_LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZY`LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X<I7XD58X4<5Y4F5Y8F5Y@@<Y<G4ZLLHMSL<G0]L8QP9TPL@;0]L<G0]L<B0]L<B0]LPL0TL8QPATPPBTPPCTPPDTPPARPPBRPPCRPPDRPPERPPFRPPGRPPHRPPIRPPJRPPKRPPLRPPMRPPNRPPORPP0SPP1SPP2SPP3SPP4SPP7WPLRP9oPU5S@QjKTjJTjITjHTjGTjFTjETjDTjCTjBTjATj@Tj?Tj>Tj=Tj<Tj;Tj:Tj9Tj8Tj7Tj6Tj5Tj4Tj3Tj2Tj1Tj0TjOSjNSjMSjLSjKSjJSjISjHSjGSjFSiDSESi>SBSi<S<Si5S:Si;R<Ri0R1Ri\\iZZiUXiPSk5QQfQ0000OOOOOOOOW6OOOOOOOOOOOWySPylQ<;3XySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOW@FOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOW@FOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOW@FOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPySQ"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2E.T_UW_1fba8_1acc8_w3_r10_p3h6824cc7f7_L0) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_UW_1fba8_1acc8_w3_r10_p3h6824cc7f7_L0.

Module C_UW_1fba8_1acc8_w4_r11_pv_L0.

Definition ROOT : sstate := (t_st T_Ubs2E.T_UW_1fba8_1acc8_w4_r11_pv_L0).
Definition CUTS : IMap.t template := imap_of [(101%uint63, T_Ubs2E.T_FINAL_r9)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2E.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y_LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZY`LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X<I7XD58X4<5Y4F5Y8F5Y@@<Y<G4ZLLHMSP;oPP<oPP=oPP>oPP?oPP@oPPAoPPBoPPCoPPDoPPEoPPFoPPGoPPHoPPARPPBRPPCRPPDRPPERPPFRPPGRPPHRPPIRPPJRPPKRPPLRPPMRPPNRPPORPP0SPP1SPP2SPP3SPP4SPP7WPPCSPPIoPU5S@QjKTjJTjITjHTjGTjFTjETjDTjCTjBTjATj@Tj?Tj>Tj=Tj<Tj;Tj:Tj9Tj8Tj7Tj6Tj5Tj4Tj3Tj2Tj1Tj0TjOSjNSjMSjLSjKSjJSjISjHSjGSjFSiDSESi>SBSi<S<Si5S:Si;R<Ri0R1Ri\\iZZiUXiPSfQ0000OOOOOOOOW6OOOOOOOOOOOWySPk[QySPylQ<;3XLLHMSP;oPP<oPP=oPP>oPP?oPP@oPPAoPPBoPPCoPPDoPPEoPPFoPPGoPPHoPPARPPBRPPCRPPDRPPERPPFRPPGRPPHRPPIRPPJRPPKRPPLRPPMRPPNRPPORPP0SPP1SPP2SPP3SPP4SPP7WPPCSPPIoPU5S@QjKTjJTjITjHTjGTjFTjETjDTjCTjBTjATj@Tj?Tj>Tj=Tj<Tj;Tj:Tj9Tj8Tj7Tj6Tj5Tj4Tj3Tj2Tj1Tj0TjOSjNSjMSjLSjKSjJSjISjHSjGSjFSiDSESi>SBSi<S<Si5S:Si;R<Ri0R1Ri\\iZZiUXiPSfQ0000OOOOOOOOW6OOOOOOOOOOOWySPk[QySPylQ<;3XklRySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOW@FOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOW@FOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOW@FOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPySQ"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2E.T_UW_1fba8_1acc8_w4_r11_pv_L0) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_UW_1fba8_1acc8_w4_r11_pv_L0.

Module C_UW_1fba8_6b647_w2_r9_p3h6818cc5fb_L0.

Definition ROOT : sstate := (t_st T_Ubs2E.T_UW_1fba8_6b647_w2_r9_p3h6818cc5fb_L0).
Definition CUTS : IMap.t template := imap_of [(100%uint63, T_Ubs2E.T_FINAL_r8)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2E.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y_LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZY`LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X<I7XD58X4<5Y4F5Y8F5Y@@<Y<G4ZLLHMSL<G0]LHRP:TPL@;0]L<G0]L<<0]L<<0]LPL0TLHRPBTPPCTPPDTPPETPP@RPPARPPBRPPCRPPDRPPERPPFRPPGRPPHRPPIRPPJRPPKRPPLRPPMRPPNRPPORPP0SPP1SPP2SPP3SPP7WPLQP9oPU4S?QjLTjKTjJTjITjHTjGTjFTjETjDTjCTjBTjATj@Tj?Tj>Tj=Tj<Tj;Tj:Tj9Tj8Tj7Tj6Tj5Tj4Tj3Tj2Tj1Tj0TjOSjNSjMSjLSjKSjJSjISjHSjGSi=S@Si;S;Si4S9Si:R;Ri0R0Ri\\iZZiUXiPSk5QQfQ0000OOOOOOOOW6OOOOOOOOOOOWySPylQ<;3XySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOW@FOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOW@FOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOW@FOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPySQ"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2E.T_UW_1fba8_6b647_w2_r9_p3h6818cc5fb_L0) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_UW_1fba8_6b647_w2_r9_p3h6818cc5fb_L0.

Module C_UW_1fba8_6b647_w2_r9_p3h6824cc7f7_L0.

Definition ROOT : sstate := (t_st T_Ubs2E.T_UW_1fba8_6b647_w2_r9_p3h6824cc7f7_L0).
Definition CUTS : IMap.t template := imap_of [(100%uint63, T_Ubs2E.T_FINAL_r8)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2E.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y_LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZY`LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X<I7XD58X4<5Y4F5Y8F5Y@@<Y<G4ZLLHMSL<G0]L8QP:TPL@;0]L<G0]L<B0]L<B0]LPL0TL8QPBTPPCTPPDTPPETPP@RPPARPPBRPPCRPPDRPPERPPFRPPGRPPHRPPIRPPJRPPKRPPLRPPMRPPNRPPORPP0SPP1SPP2SPP3SPP7WPLRP9oPU4S?QjLTjKTjJTjITjHTjGTjFTjETjDTjCTjBTjATj@Tj?Tj>Tj=Tj<Tj;Tj:Tj9Tj8Tj7Tj6Tj5Tj4Tj3Tj2Tj1Tj0TjOSjNSjMSjLSjKSjJSjISjHSjGSi=S@Si;S;Si4S9Si:R;Ri0R0Ri\\iZZiUXiPSk5QQfQ0000OOOOOOOOW6OOOOOOOOOOOWySPylQ<;3XySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOW@FOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOW@FOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOW@FOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPySQ"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2E.T_UW_1fba8_6b647_w2_r9_p3h6824cc7f7_L0) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_UW_1fba8_6b647_w2_r9_p3h6824cc7f7_L0.

Module C_UW_1fba8_6b647_w3_r10_pv_L0.

Definition ROOT : sstate := (t_st T_Ubs2E.T_UW_1fba8_6b647_w3_r10_pv_L0).
Definition CUTS : IMap.t template := imap_of [(100%uint63, T_Ubs2E.T_FINAL_r8)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2E.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y_LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZY`LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X<I7XD58X4<5Y4F5Y8F5Y@@<Y<G4ZLLHMSP;oPP<oPP=oPP>oPP?oPP@oPPAoPPBoPPCoPPDoPPEoPPFoPPGoPPHoPP@RPPARPPBRPPCRPPDRPPERPPFRPPGRPPHRPPIRPPJRPPKRPPLRPPMRPPNRPPORPP0SPP1SPP2SPP3SPP7WPPFSPPIoPU4S?QjLTjKTjJTjITjHTjGTjFTjETjDTjCTjBTjATj@Tj?Tj>Tj=Tj<Tj;Tj:Tj9Tj8Tj7Tj6Tj5Tj4Tj3Tj2Tj1Tj0TjOSjNSjMSjLSjKSjJSjISjHSjGSi=S@Si;S;Si4S9Si:R;Ri0R0Ri\\iZZiUXiPSfQ0000OOOOOOOOW6OOOOOOOOOOOWySPk[QySPylQ<;3XLLHMSP;oPP<oPP=oPP>oPP?oPP@oPPAoPPBoPPCoPPDoPPEoPPFoPPGoPPHoPP@RPPARPPBRPPCRPPDRPPERPPFRPPGRPPHRPPIRPPJRPPKRPPLRPPMRPPNRPPORPP0SPP1SPP2SPP3SPP7WPPFSPPIoPU4S?QjLTjKTjJTjITjHTjGTjFTjETjDTjCTjBTjATj@Tj?Tj>Tj=Tj<Tj;Tj:Tj9Tj8Tj7Tj6Tj5Tj4Tj3Tj2Tj1Tj0TjOSjNSjMSjLSjKSjJSjISjHSjGSi=S@Si;S;Si4S9Si:R;Ri0R0Ri\\iZZiUXiPSfQ0000OOOOOOOOW6OOOOOOOOOOOWySPk[QySPylQ<;3XklRySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOW@FOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOW@FOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOW@FOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPySQ"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2E.T_UW_1fba8_6b647_w3_r10_pv_L0) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_UW_1fba8_6b647_w3_r10_pv_L0.

Module C_UW_1fc40_72faa_w3_r10_p3h6818cc5fb_L0.

Definition ROOT : sstate := (t_st T_Ubs2E.T_UW_1fc40_72faa_w3_r10_p3h6818cc5fb_L0).
Definition CUTS : IMap.t template := imap_of [(100%uint63, T_Ubs2E.T_FINAL_r8)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2E.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y_LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZY`LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X<I7XD58X4<5Y4F5Y8F5Y@@<Y<G4ZLLHMSL<G0]PLlPPMlPL@;0]L<G0]L<<0]L<<0]LPL0TLHRP5mPP6mPP7mPP8mPP@RPPARPPBRPPCRPPDRPPERPPFRPPGRPPHRPPIRPPJRPPKRPPLRPPMRPPNRPPORPP0SPP1SPP2SPP3SPP7WPLQP:6QPU4S?QjLTjKTjJTjITjHTjGTjFTjETjDTjCTjBTjATj@Tj?Tj>Tj=Tj<Tj;Tj:Tj9Tj8Tj7Tj6Tj5Tj4Tj3Tj2Tj1Tj0TjOSjNSjMSjLSjKSjJSjISjHSjGSi=S@Si;S;Si4S9Si:R;Ri0R0Ri\\iZZiUXiPSk5QQfQ0000OOOOOOOOW6OOOOOOOOOOOWySPylQ<;3XySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPk[QySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOW>FOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOW>FOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOW>FOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPySQ"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2E.T_UW_1fc40_72faa_w3_r10_p3h6818cc5fb_L0) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_UW_1fc40_72faa_w3_r10_p3h6818cc5fb_L0.

Module C_UW_1fc40_72faa_w3_r10_p3h6824cc7f7_L0.

Definition ROOT : sstate := (t_st T_Ubs2E.T_UW_1fc40_72faa_w3_r10_p3h6824cc7f7_L0).
Definition CUTS : IMap.t template := imap_of [(100%uint63, T_Ubs2E.T_FINAL_r8)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2E.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y_LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZY`LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X<I7XD58X4<5Y4F5Y8F5Y@@<Y<G4ZLLHMSL<G0]PLlPPMlPL@;0]L<G0]L<B0]L<B0]LPL0TL8QP5mPP6mPP7mPP8mPP@RPPARPPBRPPCRPPDRPPERPPFRPPGRPPHRPPIRPPJRPPKRPPLRPPMRPPNRPPORPP0SPP1SPP2SPP3SPP7WPLRP:6QPU4S?QjLTjKTjJTjITjHTjGTjFTjETjDTjCTjBTjATj@Tj?Tj>Tj=Tj<Tj;Tj:Tj9Tj8Tj7Tj6Tj5Tj4Tj3Tj2Tj1Tj0TjOSjNSjMSjLSjKSjJSjISjHSjGSi=S@Si;S;Si4S9Si:R;Ri0R0Ri\\iZZiUXiPSk5QQfQ0000OOOOOOOOW6OOOOOOOOOOOWySPylQ<;3XySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPk[QySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOW>FOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOW>FOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOW>FOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPySQ"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2E.T_UW_1fc40_72faa_w3_r10_p3h6824cc7f7_L0) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_UW_1fc40_72faa_w3_r10_p3h6824cc7f7_L0.

Module C_UW_1fc40_72faa_w4_r11_pv_L0.

Definition ROOT : sstate := (t_st T_Ubs2E.T_UW_1fc40_72faa_w4_r11_pv_L0).
Definition CUTS : IMap.t template := imap_of [(100%uint63, T_Ubs2E.T_FINAL_r8)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2E.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y_LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZY`LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X<I7XD58X4<5Y4F5Y8F5Y@@<Y<G4ZLLHMSP<6QPP=6QPP>6QPP?6QPP@6QPPA6QPPB6QPPC6QPPD6QPPE6QPPF6QPPG6QPPH6QPPI6QPP@RPPARPPBRPPCRPPDRPPERPPFRPPGRPPHRPPIRPPJRPPKRPPLRPPMRPPNRPPORPP0SPP1SPP2SPP3SPP7WPPFSPPJ6QPU4S?QjLTjKTjJTjITjHTjGTjFTjETjDTjCTjBTjATj@Tj?Tj>Tj=Tj<Tj;Tj:Tj9Tj8Tj7Tj6Tj5Tj4Tj3Tj2Tj1Tj0TjOSjNSjMSjLSjKSjJSjISjHSjGSi=S@Si;S;Si4S9Si:R;Ri0R0Ri\\iZZiUXiPSfQ0000OOOOOOOOW6OOOOOOOOOOOWySPk[QySPylQ<;3XLLHMSP<6QPP=6QPP>6QPP?6QPP@6QPPA6QPPB6QPPC6QPPD6QPPE6QPPF6QPPG6QPPH6QPPI6QPP@RPPARPPBRPPCRPPDRPPERPPFRPPGRPPHRPPIRPPJRPPKRPPLRPPMRPPNRPPORPP0SPP1SPP2SPP3SPP7WPPFSPPJ6QPU4S?QjLTjKTjJTjITjHTjGTjFTjETjDTjCTjBTjATj@Tj?Tj>Tj=Tj<Tj;Tj:Tj9Tj8Tj7Tj6Tj5Tj4Tj3Tj2Tj1Tj0TjOSjNSjMSjLSjKSjJSjISjHSjGSi=S@Si;S;Si4S9Si:R;Ri0R0Ri\\iZZiUXiPSfQ0000OOOOOOOOW6OOOOOOOOOOOWySPk[QySPylQ<;3XklRySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPk[QySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOW>FOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOW>FOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOW>FOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPySQ"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2E.T_UW_1fc40_72faa_w4_r11_pv_L0) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_UW_1fc40_72faa_w4_r11_pv_L0.

Module C_UW_1fc40_991f7_w4_r11_p3h6818cc5fb_L0.

Definition ROOT : sstate := (t_st T_Ubs2E.T_UW_1fc40_991f7_w4_r11_p3h6818cc5fb_L0).
Definition CUTS : IMap.t template := imap_of [(101%uint63, T_Ubs2E.T_FINAL_r9)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2E.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y_LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZY`LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X<I7XD58X4<5Y4F5Y8F5Y@@<Y<G4ZLLHMSL<G0]PLlPPMlPL@;0]L<G0]L<<0]L<<0]LPL0TLHRP5mPP6mPP7mPP8mPPARPPBRPPCRPPDRPPERPPFRPPGRPPHRPPIRPPJRPPKRPPLRPPMRPPNRPPORPP0SPP1SPP2SPP3SPP4SPP7WPLQP:6QPU5S@QjKTjJTjITjHTjGTjFTjETjDTjCTjBTjATj@Tj?Tj>Tj=Tj<Tj;Tj:Tj9Tj8Tj7Tj6Tj5Tj4Tj3Tj2Tj1Tj0TjOSjNSjMSjLSjKSjJSjISjHSjGSjFSiDSESi>SBSi<S<Si5S:Si;R<Ri0R1Ri\\iZZiUXiPSk5QQfQ0000OOOOOOOOW6OOOOOOOOOOOWySPylQ<;3XySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPk[QySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOW>FOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOW>FOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOW>FOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPySQ"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2E.T_UW_1fc40_991f7_w4_r11_p3h6818cc5fb_L0) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_UW_1fc40_991f7_w4_r11_p3h6818cc5fb_L0.

Module C_UW_1fc40_991f7_w4_r11_p3h6824cc7f7_L0.

Definition ROOT : sstate := (t_st T_Ubs2E.T_UW_1fc40_991f7_w4_r11_p3h6824cc7f7_L0).
Definition CUTS : IMap.t template := imap_of [(101%uint63, T_Ubs2E.T_FINAL_r9)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2E.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y_LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZY`LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X<I7XD58X4<5Y4F5Y8F5Y@@<Y<G4ZLLHMSL<G0]PLlPPMlPL@;0]L<G0]L<B0]L<B0]LPL0TL8QP5mPP6mPP7mPP8mPPARPPBRPPCRPPDRPPERPPFRPPGRPPHRPPIRPPJRPPKRPPLRPPMRPPNRPPORPP0SPP1SPP2SPP3SPP4SPP7WPLRP:6QPU5S@QjKTjJTjITjHTjGTjFTjETjDTjCTjBTjATj@Tj?Tj>Tj=Tj<Tj;Tj:Tj9Tj8Tj7Tj6Tj5Tj4Tj3Tj2Tj1Tj0TjOSjNSjMSjLSjKSjJSjISjHSjGSjFSiDSESi>SBSi<S<Si5S:Si;R<Ri0R1Ri\\iZZiUXiPSk5QQfQ0000OOOOOOOOW6OOOOOOOOOOOWySPylQ<;3XySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPk[QySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOW>FOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOW>FOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOW>FOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPySQ"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2E.T_UW_1fc40_991f7_w4_r11_p3h6824cc7f7_L0) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_UW_1fc40_991f7_w4_r11_p3h6824cc7f7_L0.

Module C_UW_1fc40_991f7_w5_r12_pv_L0.

Definition ROOT : sstate := (t_st T_Ubs2E.T_UW_1fc40_991f7_w5_r12_pv_L0).
Definition CUTS : IMap.t template := imap_of [(101%uint63, T_Ubs2E.T_FINAL_r9)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2E.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y_LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZY`LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X<I7XD58X4<5Y4F5Y8F5Y@@<Y<G4ZLLHMSP<6QPP=6QPP>6QPP?6QPP@6QPPA6QPPB6QPPC6QPPD6QPPE6QPPF6QPPG6QPPH6QPPI6QPPARPPBRPPCRPPDRPPERPPFRPPGRPPHRPPIRPPJRPPKRPPLRPPMRPPNRPPORPP0SPP1SPP2SPP3SPP4SPP7WPPCSPPJ6QPU5S@QjKTjJTjITjHTjGTjFTjETjDTjCTjBTjATj@Tj?Tj>Tj=Tj<Tj;Tj:Tj9Tj8Tj7Tj6Tj5Tj4Tj3Tj2Tj1Tj0TjOSjNSjMSjLSjKSjJSjISjHSjGSjFSiDSESi>SBSi<S<Si5S:Si;R<Ri0R1Ri\\iZZiUXiPSfQ0000OOOOOOOOW6OOOOOOOOOOOWySPk[QySPylQ<;3XLLHMSP<6QPP=6QPP>6QPP?6QPP@6QPPA6QPPB6QPPC6QPPD6QPPE6QPPF6QPPG6QPPH6QPPI6QPPARPPBRPPCRPPDRPPERPPFRPPGRPPHRPPIRPPJRPPKRPPLRPPMRPPNRPPORPP0SPP1SPP2SPP3SPP4SPP7WPPCSPPJ6QPU5S@QjKTjJTjITjHTjGTjFTjETjDTjCTjBTjATj@Tj?Tj>Tj=Tj<Tj;Tj:Tj9Tj8Tj7Tj6Tj5Tj4Tj3Tj2Tj1Tj0TjOSjNSjMSjLSjKSjJSjISjHSjGSjFSiDSESi>SBSi<S<Si5S:Si;R<Ri0R1Ri\\iZZiUXiPSfQ0000OOOOOOOOW6OOOOOOOOOOOWySPk[QySPylQ<;3XklRySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPk[QySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOW>FOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOW>FOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOW>FOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPySQ"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2E.T_UW_1fc40_991f7_w5_r12_pv_L0) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_UW_1fc40_991f7_w5_r12_pv_L0.

Module C_UW_2037c_01284_w6_r13_p3h6818ccedd_L0.

Definition ROOT : sstate := (t_st T_Ubs2E.T_UW_2037c_01284_w6_r13_p3h6818ccedd_L0).
Definition CUTS : IMap.t template := imap_of [(100%uint63, T_Ubs2E.T_FINAL_r8)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2E.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y_LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZY`LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X<I7XD58X4<5Y4F5Y8F5Y@@<Y<G4ZLLHMSL<G0]P7=QPP8=QPL@;0]L<G0]L<<0]L<<0]LPL0TLHRP@=QPPA=QPPB=QPPC=QPP@RPPARPPBRPPCRPPDRPPERPPFRPPGRPPHRPPIRPPJRPPKRPPLRPPMRPPNRPPORPP0SPP1SPP2SPP3SPP8WPLQPD=QPU4S?QjLTjKTjJTjITjHTjGTjFTjETjDTjCTjBTjATj@Tj?Tj>Tj=Tj<Tj;Tj:Tj9Tj8Tj7Tj6Tj5Tj4Tj3Tj2Tj1Tj0TjOSjNSjMSjLSjKSjJSjISjHSjGSi=S@Si;S;Si4S9Si:R;Ri0R0Ri\\iZZiUXiPSk5QQfQ0000OOOOOOOOW6OOOOOOOOOOOWySPylQ<;3XySPk[QySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPk[QySPk[QySPylQ45OSySPk[QySPk[QySPyl`LHMS05OSDJ0T@K0TLJ1TH7AT861X871XL03X8;3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOWNEOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOWNEOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOWNEOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOWNEOOOOOOOOOOWySPkASQySPkASQySPkASQySPySQ"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2E.T_UW_2037c_01284_w6_r13_p3h6818ccedd_L0) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_UW_2037c_01284_w6_r13_p3h6818ccedd_L0.

Module C_UW_2037c_01284_w6_r13_p3h6824cca88_L0.

Definition ROOT : sstate := (t_st T_Ubs2E.T_UW_2037c_01284_w6_r13_p3h6824cca88_L0).
Definition CUTS : IMap.t template := imap_of [(100%uint63, T_Ubs2E.T_FINAL_r8)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2E.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y_LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZY`LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X<I7XD58X4<5Y4F5Y8F5Y@@<Y<G4ZLLHMSL<G0]P7=QPP8=QPL@;0]L<G0]L<B0]L<B0]LPL0TL8QP@=QPPA=QPPB=QPPC=QPP@RPPARPPBRPPCRPPDRPPERPPFRPPGRPPHRPPIRPPJRPPKRPPLRPPMRPPNRPPORPP0SPP1SPP2SPP3SPP8WPLRPD=QPU4S?QjLTjKTjJTjITjHTjGTjFTjETjDTjCTjBTjATj@Tj?Tj>Tj=Tj<Tj;Tj:Tj9Tj8Tj7Tj6Tj5Tj4Tj3Tj2Tj1Tj0TjOSjNSjMSjLSjKSjJSjISjHSjGSi=S@Si;S;Si4S9Si:R;Ri0R0Ri\\iZZiUXiPSk5QQfQ0000OOOOOOOOW6OOOOOOOOOOOWySPylQ<;3XySPk[QySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPk[QySPk[QySPylQ45OSySPk[QySPk[QySPyl`LHMS05OSDJ0T@K0TLJ1TH7AT861X871XL03X8;3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOWNEOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOWNEOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOWNEOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOWNEOOOOOOOOOOWySPkASQySPkASQySPkASQySPySQ"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2E.T_UW_2037c_01284_w6_r13_p3h6824cca88_L0) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_UW_2037c_01284_w6_r13_p3h6824cca88_L0.

Module C_UW_2037c_01284_w7_r14_pv_L0.

Definition ROOT : sstate := (t_st T_Ubs2E.T_UW_2037c_01284_w7_r14_pv_L0).
Definition CUTS : IMap.t template := imap_of [(100%uint63, T_Ubs2E.T_FINAL_r8)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2E.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y_LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZY`LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X<I7XD58X4<5Y4F5Y8F5Y@@<Y<G4ZLLHMSPH=QPPI=QPPJ=QPPK=QPPL=QPPM=QPPN=QPPO=QPP0>QPP1>QPP2>QPP3>QPP4>QPP5>QPP@RPPARPPBRPPCRPPDRPPERPPFRPPGRPPHRPPIRPPJRPPKRPPLRPPMRPPNRPPORPP0SPP1SPP2SPP3SPP9WPPFSPP6>QPU4S?QjLTjKTjJTjITjHTjGTjFTjETjDTjCTjBTjATj@Tj?Tj>Tj=Tj<Tj;Tj:Tj9Tj8Tj7Tj6Tj5Tj4Tj3Tj2Tj1Tj0TjOSjNSjMSjLSjKSjJSjISjHSjGSi=S@Si;S;Si4S9Si:R;Ri0R0Ri\\iZZiUXiPSfQ0000OOOOOOOOW6OOOOOOOOOOOWySPk[QySPylQ<;3XLLHMSPH=QPPI=QPPJ=QPPK=QPPL=QPPM=QPPN=QPPO=QPP0>QPP1>QPP2>QPP3>QPP4>QPP5>QPP@RPPARPPBRPPCRPPDRPPERPPFRPPGRPPHRPPIRPPJRPPKRPPLRPPMRPPNRPPORPP0SPP1SPP2SPP3SPP9WPPFSPP6>QPU4S?QjLTjKTjJTjITjHTjGTjFTjETjDTjCTjBTjATj@Tj?Tj>Tj=Tj<Tj;Tj:Tj9Tj8Tj7Tj6Tj5Tj4Tj3Tj2Tj1Tj0TjOSjNSjMSjLSjKSjJSjISjHSjGSi=S@Si;S;Si4S9Si:R;Ri0R0Ri\\iZZiUXiPSfQ0000OOOOOOOOW6OOOOOOOOOOOWySPk[QySPylQ<;3XklRySPk[QySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPk[QySPk[QySPylQ45OSySPk[QySPk[QySPyl`LHMS05OSDJ0T@K0TLJ1TH7AT861X871XL03X8;3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOWNEOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOWNEOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOWNEOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOWNEOOOOOOOOOOWySPkASQySPkASQySPkASQySPySQ"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2E.T_UW_2037c_01284_w7_r14_pv_L0) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_UW_2037c_01284_w7_r14_pv_L0.

Module C_UW_52944_67536_w5_r12_p3h6818cc5fb_L0.

Definition ROOT : sstate := (t_st T_Ubs2E.T_UW_52944_67536_w5_r12_p3h6818cc5fb_L0).
Definition CUTS : IMap.t template := imap_of [(101%uint63, T_Ubs2E.T_FINAL_r9)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2E.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y_LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZY`LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X<I7XD58X4<5Y4F5Y8F5Y@@<Y<G4ZLLHMSL<G0]P>LQPP?LQPL@;0]L<G0]L<<0]L<<0]LPL0TLHRPGLQPPHLQPPILQPPJLQPPARPPBRPPCRPPDRPPERPPFRPPGRPPHRPPIRPPJRPPKRPPLRPPMRPPNRPPORPP0SPP1SPP2SPP3SPP4SPP7WPLQPL5RPU5S@QjKTjJTjITjHTjGTjFTjETjDTjCTjBTjATj@Tj?Tj>Tj=Tj<Tj;Tj:Tj9Tj8Tj7Tj6Tj5Tj4Tj3Tj2Tj1Tj0TjOSjNSjMSjLSjKSjJSjISjHSjGSjFSiDSESi>SBSi<S<Si5S:Si;R<Ri0R1Ri\\iZZiUXiPSk5QQfQ0000OOOOOOOOW6OOOOOOOOOOOWySPylQ<;3XySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPk[QySPk[QySPylQ45OSySPk[QySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOWNEOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOWNEOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOWNEOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOWNEOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOWNEOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOWNEOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOWNEOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPySQ"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2E.T_UW_52944_67536_w5_r12_p3h6818cc5fb_L0) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_UW_52944_67536_w5_r12_p3h6818cc5fb_L0.

Module C_UW_52944_67536_w5_r12_p3h6824cc7f7_L0.

Definition ROOT : sstate := (t_st T_Ubs2E.T_UW_52944_67536_w5_r12_p3h6824cc7f7_L0).
Definition CUTS : IMap.t template := imap_of [(101%uint63, T_Ubs2E.T_FINAL_r9)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2E.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y_LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZY`LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X<I7XD58X4<5Y4F5Y8F5Y@@<Y<G4ZLLHMSL<G0]P>LQPP?LQPL@;0]L<G0]L<B0]L<B0]LPL0TL8QPGLQPPHLQPPILQPPJLQPPARPPBRPPCRPPDRPPERPPFRPPGRPPHRPPIRPPJRPPKRPPLRPPMRPPNRPPORPP0SPP1SPP2SPP3SPP4SPP7WPLRPL5RPU5S@QjKTjJTjITjHTjGTjFTjETjDTjCTjBTjATj@Tj?Tj>Tj=Tj<Tj;Tj:Tj9Tj8Tj7Tj6Tj5Tj4Tj3Tj2Tj1Tj0TjOSjNSjMSjLSjKSjJSjISjHSjGSjFSiDSESi>SBSi<S<Si5S:Si;R<Ri0R1Ri\\iZZiUXiPSk5QQfQ0000OOOOOOOOW6OOOOOOOOOOOWySPylQ<;3XySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPk[QySPk[QySPylQ45OSySPk[QySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOWNEOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOWNEOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOWNEOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOWNEOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOWNEOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOWNEOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOWNEOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPySQ"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2E.T_UW_52944_67536_w5_r12_p3h6824cc7f7_L0) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_UW_52944_67536_w5_r12_p3h6824cc7f7_L0.

Module C_UW_52944_67536_w6_r13_pv_L0.

Definition ROOT : sstate := (t_st T_Ubs2E.T_UW_52944_67536_w6_r13_pv_L0).
Definition CUTS : IMap.t template := imap_of [(101%uint63, T_Ubs2E.T_FINAL_r9)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2E.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan (StrLz.lz_dec "-$:Y_LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZY`@#1%$)<I7XD58?%(-.'LLHMSPN5RPPO5RPP06RPP16RPP26RPP36RPP46RPP56RPP66RPP76RPP86RPP96RPP:6RPP;6RPPARPPBRPPCRPPDRPPERPPFRPPGRPPHRPPIRPPJRPPKRPPLRPPMRPPNRPPORPP0SPP1SPP2SPP3SPP4SPP7WPPCSPP<6RPU5S@QjKTjJTjITjHTjGTjFTjETjDTjCTjBTjATj@Tj?Tj>Tj=Tj<Tj;Tj:Tj9Tj8Tj7Tj6Tj5Tj4Tj3Tj2Tj1Tj0TjOSjNSjMSjLSjKSjJSjISjHSjGSjFSiDSESi>SBSi<S<Si5S:Si;R<Ri0R1Ri\\iZZiUXiPSfQ0000OOOOOOOOW62#,-#,OOOWySPk[QySPylQ<;3X@.8//,klRySPkASQ1#)8#0@#)#>@$'$<<#7#[0#(1(#&45OS4#8@&1(&@&1'(@'=(47#0%ySQ91*-$NE91*-@%$%9@';(2@%8($@$;*-@$7';"%pstring).
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2E.T_UW_52944_67536_w6_r13_pv_L0) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_UW_52944_67536_w6_r13_pv_L0.

Module C_UW_52944_a198b_w4_r11_p3h6818cc5fb_L0.

Definition ROOT : sstate := (t_st T_Ubs2E.T_UW_52944_a198b_w4_r11_p3h6818cc5fb_L0).
Definition CUTS : IMap.t template := imap_of [(100%uint63, T_Ubs2E.T_FINAL_r8)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2E.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y_LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZY`LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X<I7XD58X4<5Y4F5Y8F5Y@@<Y<G4ZLLHMSL<G0]P>LQPP?LQPL@;0]L<G0]L<<0]L<<0]LPL0TLHRPGLQPPHLQPPILQPPJLQPP@RPPARPPBRPPCRPPDRPPERPPFRPPGRPPHRPPIRPPJRPPKRPPLRPPMRPPNRPPORPP0SPP1SPP2SPP3SPP7WPLQPL5RPU4S?QjLTjKTjJTjITjHTjGTjFTjETjDTjCTjBTjATj@Tj?Tj>Tj=Tj<Tj;Tj:Tj9Tj8Tj7Tj6Tj5Tj4Tj3Tj2Tj1Tj0TjOSjNSjMSjLSjKSjJSjISjHSjGSi=S@Si;S;Si4S9Si:R;Ri0R0Ri\\iZZiUXiPSk5QQfQ0000OOOOOOOOW6OOOOOOOOOOOWySPylQ<;3XySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPk[QySPk[QySPylQ45OSySPk[QySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOWNEOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOWNEOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOWNEOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOWNEOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOWNEOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOWNEOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOWNEOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPySQ"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2E.T_UW_52944_a198b_w4_r11_p3h6818cc5fb_L0) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_UW_52944_a198b_w4_r11_p3h6818cc5fb_L0.

Module C_UW_52944_a198b_w4_r11_p3h6824cc7f7_L0.

Definition ROOT : sstate := (t_st T_Ubs2E.T_UW_52944_a198b_w4_r11_p3h6824cc7f7_L0).
Definition CUTS : IMap.t template := imap_of [(100%uint63, T_Ubs2E.T_FINAL_r8)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2E.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y_LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZY`LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X<I7XD58X4<5Y4F5Y8F5Y@@<Y<G4ZLLHMSL<G0]P>LQPP?LQPL@;0]L<G0]L<B0]L<B0]LPL0TL8QPGLQPPHLQPPILQPPJLQPP@RPPARPPBRPPCRPPDRPPERPPFRPPGRPPHRPPIRPPJRPPKRPPLRPPMRPPNRPPORPP0SPP1SPP2SPP3SPP7WPLRPL5RPU4S?QjLTjKTjJTjITjHTjGTjFTjETjDTjCTjBTjATj@Tj?Tj>Tj=Tj<Tj;Tj:Tj9Tj8Tj7Tj6Tj5Tj4Tj3Tj2Tj1Tj0TjOSjNSjMSjLSjKSjJSjISjHSjGSi=S@Si;S;Si4S9Si:R;Ri0R0Ri\\iZZiUXiPSk5QQfQ0000OOOOOOOOW6OOOOOOOOOOOWySPylQ<;3XySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPk[QySPk[QySPylQ45OSySPk[QySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOWNEOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOWNEOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOWNEOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOWNEOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOWNEOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOWNEOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOWNEOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPySQ"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2E.T_UW_52944_a198b_w4_r11_p3h6824cc7f7_L0) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_UW_52944_a198b_w4_r11_p3h6824cc7f7_L0.

Module C_UW_52944_a198b_w5_r12_pv_L0.

Definition ROOT : sstate := (t_st T_Ubs2E.T_UW_52944_a198b_w5_r12_pv_L0).
Definition CUTS : IMap.t template := imap_of [(100%uint63, T_Ubs2E.T_FINAL_r8)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2E.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y_LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZY`LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X<I7XD58X4<5Y4F5Y8F5Y@@<Y<G4ZLLHMSPN5RPPO5RPP06RPP16RPP26RPP36RPP46RPP56RPP66RPP76RPP86RPP96RPP:6RPP;6RPP@RPPARPPBRPPCRPPDRPPERPPFRPPGRPPHRPPIRPPJRPPKRPPLRPPMRPPNRPPORPP0SPP1SPP2SPP3SPP7WPPFSPP<6RPU4S?QjLTjKTjJTjITjHTjGTjFTjETjDTjCTjBTjATj@Tj?Tj>Tj=Tj<Tj;Tj:Tj9Tj8Tj7Tj6Tj5Tj4Tj3Tj2Tj1Tj0TjOSjNSjMSjLSjKSjJSjISjHSjGSi=S@Si;S;Si4S9Si:R;Ri0R0Ri\\iZZiUXiPSfQ0000OOOOOOOOW6OOOOOOOOOOOWySPk[QySPylQ<;3XLLHMSPN5RPPO5RPP06RPP16RPP26RPP36RPP46RPP56RPP66RPP76RPP86RPP96RPP:6RPP;6RPP@RPPARPPBRPPCRPPDRPPERPPFRPPGRPPHRPPIRPPJRPPKRPPLRPPMRPPNRPPORPP0SPP1SPP2SPP3SPP7WPPFSPP<6RPU4S?QjLTjKTjJTjITjHTjGTjFTjETjDTjCTjBTjATj@Tj?Tj>Tj=Tj<Tj;Tj:Tj9Tj8Tj7Tj6Tj5Tj4Tj3Tj2Tj1Tj0TjOSjNSjMSjLSjKSjJSjISjHSjGSi=S@Si;S;Si4S9Si:R;Ri0R0Ri\\iZZiUXiPSfQ0000OOOOOOOOW6OOOOOOOOOOOWySPk[QySPylQ<;3XklRySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPk[QySPk[QySPylQ45OSySPk[QySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOWNEOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOWNEOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOWNEOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOWNEOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOWNEOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOWNEOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOWNEOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPySQ"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2E.T_UW_52944_a198b_w5_r12_pv_L0) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_UW_52944_a198b_w5_r12_pv_L0.

Module C_UW_52944_d4b36_w6_r13_p3h6818cc5fb_L0.

Definition ROOT : sstate := (t_st T_Ubs2E.T_UW_52944_d4b36_w6_r13_p3h6818cc5fb_L0).
Definition CUTS : IMap.t template := imap_of [(101%uint63, T_Ubs2E.T_FINAL_r9)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2E.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y_LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZY`LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X<I7XD58X4<5Y4F5Y8F5Y@@<Y<G4ZLLHMSL<G0]PD3RPPE3RPL@;0]L<G0]L<<0]L<<0]LPL0TLHRPM3RPPN3RPPO3RPP04RPPARPPBRPPCRPPDRPPERPPFRPPGRPPHRPPIRPPJRPPKRPPLRPPMRPPNRPPORPP0SPP1SPP2SPP3SPP4SPP7WPLQP2=RPU5S@QjKTjJTjITjHTjGTjFTjETjDTjCTjBTjATj@Tj?Tj>Tj=Tj<Tj;Tj:Tj9Tj8Tj7Tj6Tj5Tj4Tj3Tj2Tj1Tj0TjOSjNSjMSjLSjKSjJSjISjHSjGSjFSiDSESi>SBSi<S<Si5S:Si;R<Ri0R1Ri\\iZZiUXiPSk5QQfQ0000OOOOOOOOW6OOOOOOOOOOOWySPylQ<;3XySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPk[QySPk[QySPylQ45OSySPk[QySPk[QySPyl`LHMS05OSDJ0T@K0TLJ1TH7AT861X871XL03X8;3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOW>EOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOW>EOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOW>EOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOW>EOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOW>EOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOW>EOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOW>EOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOW>EOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPySQ"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2E.T_UW_52944_d4b36_w6_r13_p3h6818cc5fb_L0) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_UW_52944_d4b36_w6_r13_p3h6818cc5fb_L0.

Module C_UW_52944_d4b36_w6_r13_p3h6824cc7f7_L0.

Definition ROOT : sstate := (t_st T_Ubs2E.T_UW_52944_d4b36_w6_r13_p3h6824cc7f7_L0).
Definition CUTS : IMap.t template := imap_of [(101%uint63, T_Ubs2E.T_FINAL_r9)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2E.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y_LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZY`LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X<I7XD58X4<5Y4F5Y8F5Y@@<Y<G4ZLLHMSL<G0]PD3RPPE3RPL@;0]L<G0]L<B0]L<B0]LPL0TL8QPM3RPPN3RPPO3RPP04RPPARPPBRPPCRPPDRPPERPPFRPPGRPPHRPPIRPPJRPPKRPPLRPPMRPPNRPPORPP0SPP1SPP2SPP3SPP4SPP7WPLRP2=RPU5S@QjKTjJTjITjHTjGTjFTjETjDTjCTjBTjATj@Tj?Tj>Tj=Tj<Tj;Tj:Tj9Tj8Tj7Tj6Tj5Tj4Tj3Tj2Tj1Tj0TjOSjNSjMSjLSjKSjJSjISjHSjGSjFSiDSESi>SBSi<S<Si5S:Si;R<Ri0R1Ri\\iZZiUXiPSk5QQfQ0000OOOOOOOOW6OOOOOOOOOOOWySPylQ<;3XySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPk[QySPk[QySPylQ45OSySPk[QySPk[QySPyl`LHMS05OSDJ0T@K0TLJ1TH7AT861X871XL03X8;3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOW>EOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOW>EOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOW>EOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOW>EOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOW>EOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOW>EOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOW>EOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOW>EOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPySQ"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2E.T_UW_52944_d4b36_w6_r13_p3h6824cc7f7_L0) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_UW_52944_d4b36_w6_r13_p3h6824cc7f7_L0.

Module C_UW_52944_d4b36_w7_r14_pv_L0.

Definition ROOT : sstate := (t_st T_Ubs2E.T_UW_52944_d4b36_w7_r14_pv_L0).
Definition CUTS : IMap.t template := imap_of [(101%uint63, T_Ubs2E.T_FINAL_r9)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2E.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan (StrLz.lz_dec "-$:Y_LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZY`@#1%$)<I7XD58?%(-.'LLHMSP8=RPP9=RPP:=RPP;=RPP<=RPP==RPP>=RPP?=RPP@=RPPA=RPPB=RPPC=RPPD=RPPE=RPPARPPBRPPCRPPDRPPERPPFRPPGRPPHRPPIRPPJRPPKRPPLRPPMRPPNRPPORPP0SPP1SPP2SPP3SPP4SPP8WPPCSPPF=RPU5S@QjKTjJTjITjHTjGTjFTjETjDTjCTjBTjATj@Tj?Tj>Tj=Tj<Tj;Tj:Tj9Tj8Tj7Tj6Tj5Tj4Tj3Tj2Tj1Tj0TjOSjNSjMSjLSjKSjJSjISjHSjGSjFSiDSESi>SBSi<S<Si5S:Si;R<Ri0R1Ri\\iZZiUXiPSfQ0000OOOOOOOOW62#,-#,OOOWySPk[QySPylQ<;3X@.8//,klRySPkASQ1#)8#0@#)#>@$'$<<#7#[0#(1(#&45OS;#83155(DJ0T@K@#?17;@&5*6@&1'(@'=(4@$&$<%ySQ91.+$>E91.+@%$%9@';(2@&((2@$4%+@$;*-@$7';"%pstring).
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2E.T_UW_52944_d4b36_w7_r14_pv_L0) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_UW_52944_d4b36_w7_r14_pv_L0.

Module C_XA_52944_61dc2_blk_w6_r13_L0.

Definition ROOT : sstate := (t_st T_Ubs2E.T_XA_52944_61dc2_blk_w6_r13_L0).
Definition CUTS : IMap.t template := imap_of [(161%uint63, T_Ubs2E.T_UW_52944_61dc2_w6_r13_p3h6824cc132_L0)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2E.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y_LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZP:ZPP;ZPP<ZPLQP>ZPP?ZPP@ZPPAZPPBZPPCZPPDZPPEZPPFZPPGZPLQPHZPPJVPPKVPPLVPLQP3WPP4WPP5WPP6WPP7WPU1U7QjBWjAWj@Wj?Wj>Wj=Wj<Wj;Wj:Wj9Wj8Wj7Wj6Wj5Wj4Wj3Wj2Wj1Wj0WjOVjNVjMVjLVjKVjJViIVIViIUIUiHTHTi7T7TiCSCSi=SASi;S;Si@R9Si:R;Ri0R0Ri\\iZZiUXiPSfQ0000OOOOOOOOWDEOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPP:ZPP;ZPP<ZPM;CIOOOOOOOOOWP>ZPP?ZPP@ZPPAZPPBZPPCZPPDZPPEZPPFZPPGZPP:SPPHZPPJVPPKVPPLVPL0H:FB1M8>2C6TP3WPP4WPP5WPP6WPP7WPU1U7QjBWjAWj@Wj?Wj>Wj=Wj<Wj;Wj:Wj9Wj8Wj7Wj6Wj5Wj4Wj3Wj2Wj1Wj0WjOVjNVjMVjLVjKVjJViIVIViIUIUiHTHTi7T7TiCSCSi=SASi;S;Si@R9Si:R;Ri0R0Ri\\iZZiUXiPSfQ0000OOOOOOOOWDEOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPcySPylQ<71X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2E.T_XA_52944_61dc2_blk_w6_r13_L0) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_XA_52944_61dc2_blk_w6_r13_L0.
