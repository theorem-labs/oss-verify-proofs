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
Module C_EH_1f934_s8_m5_w4_r11_pv_L0_f4e7bc6.

Definition ROOT : sstate := (t_st T_Ubs2U.T_THROW_1f934_s8_m5_w4_r11_pv_L0_f4e7bc6).
Definition CUTS : IMap.t template := imap_of [(102%uint63, T_Ubs2UE.T_XA_1f934_b775a_blk_w5_r12_L0); (103%uint63, T_Ubs2UE.T_XA_1f934_b775a_p682f0_w4_r11_pP)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2UE.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y`LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X0<3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZLMSLHRL<<0]P4WPP5WPLTU7Sfj9Wj8Wj7Wj6Wj5Wj4Wi1W3WiIVIViLUEViIUJUi6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XLMSLHRL<<0]P4WPP5WPLTU7Sfj9Wj8Wj7Wj6Wj5Wj4Wi1W3WiIVIViLUEViIUJUi6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XL=RL8QL<B0]P4WPP5WPLUU7Sfj9Wj8Wj7Wj6Wj5Wj4Wi1W3WiIVIViLUEViIUJUi6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013Xk4QSySPP6WPP4WPP5WPU6Saj6Wj5Wj4WiGV3WiLUEViIUJUi6T6Ti>SESiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSySPkmRySPylQ<61X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2U.T_THROW_1f934_s8_m5_w4_r11_pv_L0_f4e7bc6) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_EH_1f934_s8_m5_w4_r11_pv_L0_f4e7bc6.

Module C_EH_2037c_s10_m5_w6_r13_pv_L0_fcc6b22.

Definition ROOT : sstate := (t_st T_Ubs2U.T_THROW_2037c_s10_m5_w6_r13_pv_L0_fcc6b22).
Definition CUTS : IMap.t template := imap_of [(104%uint63, T_Ubs2UE.T_XA_2037c_48285_blk_w7_r14_L0); (105%uint63, T_Ubs2UE.T_XA_2037c_48285_p682f0_w6_r13_pP)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2UE.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y`LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X0<3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZLMSLHRL<<0]LTU9SfjOVjNVjMVjLViGVKVi?V?ViMU;ViJUKUi@U@Ui;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XLMSLHRL<<0]LTU9SfjOVjNVjMVjLViGVKVi?V?ViMU;ViJUKUi@U@Ui;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XL=RL8QL<B0]LUU9SfjOVjNVjMVjLViGVKVi?V?ViMU;ViJUKUi@U@Ui;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013Xk4QSySPU8S`i=VLViMU;ViJUKUi@U@Ui;U<Ui6T6Ti>SESiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSySPkmRySPylQ<61X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2U.T_THROW_2037c_s10_m5_w6_r13_pv_L0_fcc6b22) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_EH_2037c_s10_m5_w6_r13_pv_L0_fcc6b22.

Module C_EH_2148c_s10_m5_w6_r13_pv_L0_fe23fcf.

Definition ROOT : sstate := (t_st T_Ubs2U.T_THROW_2148c_s10_m5_w6_r13_pv_L0_fe23fcf).
Definition CUTS : IMap.t template := imap_of [(106%uint63, T_Ubs2UE.T_XA_2148c_bdba1_blk_w7_r14_L0); (107%uint63, T_Ubs2UE.T_XA_2148c_bdba1_p682f0_w6_r13_pP)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2UE.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y`LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X0<3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZLMSLHRL<<0]LTU;SgjMVjLVjKVjJViEVIVi=V=ViNU9ViKULUiEUFUi@UAUi;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XLMSLHRL<<0]LTU;SgjMVjLVjKVjJViEVIVi=V=ViNU9ViKULUiEUFUi@UAUi;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XL=RL8QL<B0]LUU;SgjMVjLVjKVjJViEVIVi=V=ViNU9ViKULUiEUFUi@UAUi;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013Xk4QSySPU:Sai;VJViNU9ViKULUiEUFUi@UAUi;U<Ui6T6Ti>SESiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSySPkmRySPylQ<61X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2U.T_THROW_2148c_s10_m5_w6_r13_pv_L0_fe23fcf) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_EH_2148c_s10_m5_w6_r13_pv_L0_fe23fcf.

Module C_EH_21778_s10_m5_w6_r13_pv_L0_feddc33.

Definition ROOT : sstate := (t_st T_Ubs2U.T_THROW_21778_s10_m5_w6_r13_pv_L0_feddc33).
Definition CUTS : IMap.t template := imap_of [(108%uint63, T_Ubs2UE.T_XA_21778_a5925_blk_w7_r14_L0); (109%uint63, T_Ubs2UE.T_XA_21778_a5925_p682f0_w6_r13_pP)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2UE.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y`LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X0<3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZLMSLHRL<<0]LTU=Sgj1Wj0WjOVjNViIVMViAVAVi1V=ViNUOUiGUIUiAUAUi;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XLMSLHRL<<0]LTU=Sgj1Wj0WjOVjNViIVMViAVAVi1V=ViNUOUiGUIUiAUAUi;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XL=RL8QL<B0]LUU=Sgj1Wj0WjOVjNViIVMViAVAVi1V=ViNUOUiGUIUiAUAUi;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013Xk4QSySPU<Sai?VNVi1V=ViNUOUiGUIUiAUAUi;U<Ui6T6Ti>SESiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSySPkmRySPylQ<61X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2U.T_THROW_21778_s10_m5_w6_r13_pv_L0_feddc33) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_EH_21778_s10_m5_w6_r13_pv_L0_feddc33.

Module C_EH_21988_s10_m5_w6_r13_pv_L0_fdbc943.

Definition ROOT : sstate := (t_st T_Ubs2U.T_THROW_21988_s10_m5_w6_r13_pv_L0_fdbc943).
Definition CUTS : IMap.t template := imap_of [(110%uint63, T_Ubs2UE.T_XA_21988_93638_blk_w7_r14_L0); (111%uint63, T_Ubs2UE.T_XA_21988_93638_p682f0_w6_r13_pP)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2UE.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y`LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X0<3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZLMSLHRL<<0]LTU?SgjMVjLVjKVjJViEVIVi=V=ViNU9ViKULUiEUFUi@UAUi;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XLMSLHRL<<0]LTU?SgjMVjLVjKVjJViEVIVi=V=ViNU9ViKULUiEUFUi@UAUi;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XL=RL8QL<B0]LUU?SgjMVjLVjKVjJViEVIVi=V=ViNU9ViKULUiEUFUi@UAUi;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013Xk4QSySPU>Sai;VJViNU9ViKULUiEUFUi@UAUi;U<Ui6T6Ti>SESiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSySPkmRySPylQ<61X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2U.T_THROW_21988_s10_m5_w6_r13_pv_L0_fdbc943) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_EH_21988_s10_m5_w6_r13_pv_L0_fdbc943.

Module C_EH_21b0c_s10_m5_w6_r13_pv_L0_f4f9b8e.

Definition ROOT : sstate := (t_st T_Ubs2U.T_THROW_21b0c_s10_m5_w6_r13_pv_L0_f4f9b8e).
Definition CUTS : IMap.t template := imap_of [(112%uint63, T_Ubs2UE.T_XA_21b0c_10317_blk_w7_r14_L0); (113%uint63, T_Ubs2UE.T_XA_21b0c_10317_p682f0_w6_r13_pP)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2UE.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y`LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X0<3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZLMSLHRL<<0]LTUASgjMVjLVjKVjJViEVIVi=V=ViNU9ViKULUiEUFUi@UAUi;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XLMSLHRL<<0]LTUASgjMVjLVjKVjJViEVIVi=V=ViNU9ViKULUiEUFUi@UAUi;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XL=RL8QL<B0]LUUASgjMVjLVjKVjJViEVIVi=V=ViNU9ViKULUiEUFUi@UAUi;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013Xk4QSySPU@Sai;VJViNU9ViKULUiEUFUi@UAUi;U<Ui6T6Ti>SESiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSySPkmRySPylQ<61X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2U.T_THROW_21b0c_s10_m5_w6_r13_pv_L0_f4f9b8e) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_EH_21b0c_s10_m5_w6_r13_pv_L0_f4f9b8e.

Module C_EH_223c4_s8_m5_w6_r13_pv_L0_f035ac3.

Definition ROOT : sstate := (t_st T_Ubs2U.T_THROW_223c4_s8_m5_w6_r13_pv_L0_f035ac3).
Definition CUTS : IMap.t template := imap_of [(126%uint63, T_Ubs2UE.T_XA_223c4_94b12_blk_w7_r14_L0); (127%uint63, T_Ubs2UE.T_XA_223c4_94b12_p682f0_w6_r13_pP)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2UE.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y`LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X0<3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZLMSLHRL<<0]LTUOSgj0WjOVjNVjMViHVLVi@V@Vi0V<ViMUNUiHUHUi@U@Ui;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XLMSLHRL<<0]LTUOSgj0WjOVjNVjMViHVLVi@V@Vi0V<ViMUNUiHUHUi@U@Ui;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XL=RL8QL<B0]LUUOSgj0WjOVjNVjMViHVLVi@V@Vi0V<ViMUNUiHUHUi@U@Ui;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013Xk4QSySPUNSai>VMVi0V<ViMUNUiHUHUi@U@Ui;U<Ui6T6Ti>SESiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSySPkmRySPylQ<61X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2U.T_THROW_223c4_s8_m5_w6_r13_pv_L0_f035ac3) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_EH_223c4_s8_m5_w6_r13_pv_L0_f035ac3.

Module C_EH_223c4_s8_m5_w6_r13_pv_L0_f1f8875.

Definition ROOT : sstate := (t_st T_Ubs2U.T_THROW_223c4_s8_m5_w6_r13_pv_L0_f1f8875).
Definition CUTS : IMap.t template := imap_of [(114%uint63, T_Ubs2UE.T_XA_223c4_03848_blk_w7_r14_L0); (115%uint63, T_Ubs2UE.T_XA_223c4_03848_p682f0_w6_r13_pP)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2UE.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y`LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X0<3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZLMSLHRL<<0]LTUCSfj1Wj0WjOVjNViIVMViAVAViOU=ViLUMUi@U@Ui;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XLMSLHRL<<0]LTUCSfj1Wj0WjOVjNViIVMViAVAViOU=ViLUMUi@U@Ui;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XL=RL8QL<B0]LUUCSfj1Wj0WjOVjNViIVMViAVAViOU=ViLUMUi@U@Ui;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013Xk4QSySPUBS`i?VNViOU=ViLUMUi@U@Ui;U<Ui6T6Ti>SESiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSySPkmRySPylQ<61X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2U.T_THROW_223c4_s8_m5_w6_r13_pv_L0_f1f8875) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_EH_223c4_s8_m5_w6_r13_pv_L0_f1f8875.

Module C_EH_223c4_s8_m5_w6_r13_pv_L0_f5f981e.

Definition ROOT : sstate := (t_st T_Ubs2U.T_THROW_223c4_s8_m5_w6_r13_pv_L0_f5f981e).
Definition CUTS : IMap.t template := imap_of [(122%uint63, T_Ubs2UE.T_XA_223c4_7b44c_blk_w7_r14_L0); (123%uint63, T_Ubs2UE.T_XA_223c4_7b44c_p682f0_w6_r13_pP)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2UE.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y`LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X0<3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZLMSLHRL<<0]LTUKSgj5Wj4Wj3Wj2WiMV1WiEVEVi0VAViMUNUiHUHUi@U@Ui;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XLMSLHRL<<0]LTUKSgj5Wj4Wj3Wj2WiMV1WiEVEVi0VAViMUNUiHUHUi@U@Ui;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XL=RL8QL<B0]LUUKSgj5Wj4Wj3Wj2WiMV1WiEVEVi0VAViMUNUiHUHUi@U@Ui;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013Xk4QSySPUJSaiCV2Wi0VAViMUNUiHUHUi@U@Ui;U<Ui6T6Ti>SESiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSySPkmRySPylQ<61X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2U.T_THROW_223c4_s8_m5_w6_r13_pv_L0_f5f981e) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_EH_223c4_s8_m5_w6_r13_pv_L0_f5f981e.

Module C_EH_223c4_s8_m5_w6_r13_pv_L0_f8ed8f0.

Definition ROOT : sstate := (t_st T_Ubs2U.T_THROW_223c4_s8_m5_w6_r13_pv_L0_f8ed8f0).
Definition CUTS : IMap.t template := imap_of [(130%uint63, T_Ubs2UE.T_XA_223c4_da298_blk_w7_r14_L0); (131%uint63, T_Ubs2UE.T_XA_223c4_da298_p682f0_w6_r13_pP)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2UE.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y`LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X0<3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZLMSLHRL<<0]LTU3Tgj6Wj5Wj4Wj3WiNV2WiFVFVi0VBViMUNUiHUHUi@U@Ui;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XLMSLHRL<<0]LTU3Tgj6Wj5Wj4Wj3WiNV2WiFVFVi0VBViMUNUiHUHUi@U@Ui;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XL=RL8QL<B0]LUU3Tgj6Wj5Wj4Wj3WiNV2WiFVFVi0VBViMUNUiHUHUi@U@Ui;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013Xk4QSySPU2TaiDV3Wi0VBViMUNUiHUHUi@U@Ui;U<Ui6T6Ti>SESiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSySPkmRySPylQ<61X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2U.T_THROW_223c4_s8_m5_w6_r13_pv_L0_f8ed8f0) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_EH_223c4_s8_m5_w6_r13_pv_L0_f8ed8f0.

Module C_EH_223c4_s8_m5_w6_r13_pv_L0_faafca4.

Definition ROOT : sstate := (t_st T_Ubs2U.T_THROW_223c4_s8_m5_w6_r13_pv_L0_faafca4).
Definition CUTS : IMap.t template := imap_of [(118%uint63, T_Ubs2UE.T_XA_223c4_60f3c_blk_w7_r14_L0); (119%uint63, T_Ubs2UE.T_XA_223c4_60f3c_p682f0_w6_r13_pP)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2UE.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y`LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X0<3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZLMSLHRL<<0]LTUGSfj1Wj0WjOVjNViIVMViAVAViOU=ViLUMUi@U@Ui;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XLMSLHRL<<0]LTUGSfj1Wj0WjOVjNViIVMViAVAViOU=ViLUMUi@U@Ui;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XL=RL8QL<B0]LUUGSfj1Wj0WjOVjNViIVMViAVAViOU=ViLUMUi@U@Ui;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013Xk4QSySPUFS`i?VNViOU=ViLUMUi@U@Ui;U<Ui6T6Ti>SESiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSySPkmRySPylQ<61X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2U.T_THROW_223c4_s8_m5_w6_r13_pv_L0_faafca4) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_EH_223c4_s8_m5_w6_r13_pv_L0_faafca4.

Module C_EH_223c4_s8_m5_w6_r13_pv_L0_facbb14.

Definition ROOT : sstate := (t_st T_Ubs2U.T_THROW_223c4_s8_m5_w6_r13_pv_L0_facbb14).
Definition CUTS : IMap.t template := imap_of [(124%uint63, T_Ubs2UE.T_XA_223c4_83af5_blk_w7_r14_L0); (125%uint63, T_Ubs2UE.T_XA_223c4_83af5_p682f0_w6_r13_pP)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2UE.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y`LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X0<3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZLMSLHRL<<0]LTUMSgj4Wj3Wj2Wj1WiLV0WiDVDVi0V@ViMUNUiHUHUi@U@Ui;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XLMSLHRL<<0]LTUMSgj4Wj3Wj2Wj1WiLV0WiDVDVi0V@ViMUNUiHUHUi@U@Ui;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XL=RL8QL<B0]LUUMSgj4Wj3Wj2Wj1WiLV0WiDVDVi0V@ViMUNUiHUHUi@U@Ui;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013Xk4QSySPULSaiBV1Wi0V@ViMUNUiHUHUi@U@Ui;U<Ui6T6Ti>SESiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSySPkmRySPylQ<61X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2U.T_THROW_223c4_s8_m5_w6_r13_pv_L0_facbb14) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_EH_223c4_s8_m5_w6_r13_pv_L0_facbb14.

Module C_EH_223c4_s8_m5_w6_r13_pv_L0_fc26717.

Definition ROOT : sstate := (t_st T_Ubs2U.T_THROW_223c4_s8_m5_w6_r13_pv_L0_fc26717).
Definition CUTS : IMap.t template := imap_of [(120%uint63, T_Ubs2UE.T_XA_223c4_63bac_blk_w7_r14_L0); (121%uint63, T_Ubs2UE.T_XA_223c4_63bac_p682f0_w6_r13_pP)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2UE.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y`LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X0<3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZLMSLHRL<<0]LTUISgj4Wj3Wj2Wj1WiLV0WiDVDVi0V@ViMUNUiHUHUi@U@Ui;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XLMSLHRL<<0]LTUISgj4Wj3Wj2Wj1WiLV0WiDVDVi0V@ViMUNUiHUHUi@U@Ui;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XL=RL8QL<B0]LUUISgj4Wj3Wj2Wj1WiLV0WiDVDVi0V@ViMUNUiHUHUi@U@Ui;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013Xk4QSySPUHSaiBV1Wi0V@ViMUNUiHUHUi@U@Ui;U<Ui6T6Ti>SESiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSySPkmRySPylQ<61X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2U.T_THROW_223c4_s8_m5_w6_r13_pv_L0_fc26717) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_EH_223c4_s8_m5_w6_r13_pv_L0_fc26717.

Module C_EH_223c4_s8_m5_w6_r13_pv_L0_ff7bc35.

Definition ROOT : sstate := (t_st T_Ubs2U.T_THROW_223c4_s8_m5_w6_r13_pv_L0_ff7bc35).
Definition CUTS : IMap.t template := imap_of [(128%uint63, T_Ubs2UE.T_XA_223c4_982fd_blk_w7_r14_L0); (129%uint63, T_Ubs2UE.T_XA_223c4_982fd_p682f0_w6_r13_pP)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2UE.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y`LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X0<3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZLMSLHRL<<0]LTU1Tgj6Wj5Wj4Wj3WiNV2WiFVFVi0VBViMUNUiHUHUi@U@Ui;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XLMSLHRL<<0]LTU1Tgj6Wj5Wj4Wj3WiNV2WiFVFVi0VBViMUNUiHUHUi@U@Ui;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XL=RL8QL<B0]LUU1Tgj6Wj5Wj4Wj3WiNV2WiFVFVi0VBViMUNUiHUHUi@U@Ui;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013Xk4QSySPU0TaiDV3Wi0VBViMUNUiHUHUi@U@Ui;U<Ui6T6Ti>SESiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSySPkmRySPylQ<61X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2U.T_THROW_223c4_s8_m5_w6_r13_pv_L0_ff7bc35) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_EH_223c4_s8_m5_w6_r13_pv_L0_ff7bc35.

Module C_EH_223c4_s8_m5_w6_r13_pv_L0_ffc17f0.

Definition ROOT : sstate := (t_st T_Ubs2U.T_THROW_223c4_s8_m5_w6_r13_pv_L0_ffc17f0).
Definition CUTS : IMap.t template := imap_of [(116%uint63, T_Ubs2UE.T_XA_223c4_3b079_blk_w7_r14_L0); (117%uint63, T_Ubs2UE.T_XA_223c4_3b079_p682f0_w6_r13_pP)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2UE.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y`LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X0<3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZLMSLHRL<<0]LTUESgj2Wj1Wj0WjOViJVNViBVBVi0V>ViMUNUiHUHUi@U@Ui;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XLMSLHRL<<0]LTUESgj2Wj1Wj0WjOViJVNViBVBVi0V>ViMUNUiHUHUi@U@Ui;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XL=RL8QL<B0]LUUESgj2Wj1Wj0WjOViJVNViBVBVi0V>ViMUNUiHUHUi@U@Ui;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013Xk4QSySPUDSai@VOVi0V>ViMUNUiHUHUi@U@Ui;U<Ui6T6Ti>SESiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSySPkmRySPylQ<61X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2U.T_THROW_223c4_s8_m5_w6_r13_pv_L0_ffc17f0) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_EH_223c4_s8_m5_w6_r13_pv_L0_ffc17f0.

Module C_EH_22558_s10_m5_w6_r13_pv_L0_f5d1dca.

Definition ROOT : sstate := (t_st T_Ubs2U.T_THROW_22558_s10_m5_w6_r13_pv_L0_f5d1dca).
Definition CUTS : IMap.t template := imap_of [(132%uint63, T_Ubs2UE.T_XA_22558_a059b_blk_w7_r14_L0); (133%uint63, T_Ubs2UE.T_XA_22558_a059b_p682f0_w6_r13_pP)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2UE.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y`LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X0<3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZLMSLHRL<<0]LTU5TfjOVjNVjMVjLViGVKVi?V?ViMU;ViJUKUi@UAUi;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XLMSLHRL<<0]LTU5TfjOVjNVjMVjLViGVKVi?V?ViMU;ViJUKUi@UAUi;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XL=RL8QL<B0]LUU5TfjOVjNVjMVjLViGVKVi?V?ViMU;ViJUKUi@UAUi;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013Xk4QSySPU4T`i=VLViMU;ViJUKUi@UAUi;U<Ui6T6Ti>SESiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSySPkmRySPylQ<61X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2U.T_THROW_22558_s10_m5_w6_r13_pv_L0_f5d1dca) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_EH_22558_s10_m5_w6_r13_pv_L0_f5d1dca.

Module C_EH_22558_s10_m5_w6_r13_pv_L0_fc741c4.

Definition ROOT : sstate := (t_st T_Ubs2U.T_THROW_22558_s10_m5_w6_r13_pv_L0_fc741c4).
Definition CUTS : IMap.t template := imap_of [(134%uint63, T_Ubs2UE.T_XA_22558_fe93b_blk_w7_r14_L0); (135%uint63, T_Ubs2UE.T_XA_22558_fe93b_p682f0_w6_r13_pP)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2UE.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y`LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X0<3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZLMSLHRL<<0]LTU7TfjMVjLVjKVjJViEVIVi=V=ViLU9ViIUJUi@UAUi;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XLMSLHRL<<0]LTU7TfjMVjLVjKVjJViEVIVi=V=ViLU9ViIUJUi@UAUi;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XL=RL8QL<B0]LUU7TfjMVjLVjKVjJViEVIVi=V=ViLU9ViIUJUi@UAUi;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013Xk4QSySPU6T`i;VJViLU9ViIUJUi@UAUi;U<Ui6T6Ti>SESiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSySPkmRySPylQ<61X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2U.T_THROW_22558_s10_m5_w6_r13_pv_L0_fc741c4) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_EH_22558_s10_m5_w6_r13_pv_L0_fc741c4.

Module C_EH_22594_s10_m5_w6_r13_pv_L0_f0112c1.

Definition ROOT : sstate := (t_st T_Ubs2U.T_THROW_22594_s10_m5_w6_r13_pv_L0_f0112c1).
Definition CUTS : IMap.t template := imap_of [(146%uint63, T_Ubs2UE.T_XA_22594_994b7_blk_w7_r14_L0); (147%uint63, T_Ubs2UE.T_XA_22594_994b7_p682f0_w6_r13_pP)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2UE.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y`LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X0<3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZLMSLHRL<<0]LTUCTfjKVjJVjIVjHViCVGVi;V;ViMU7ViIUJUi@UAUi;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XLMSLHRL<<0]LTUCTfjKVjJVjIVjHViCVGVi;V;ViMU7ViIUJUi@UAUi;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XL=RL8QL<B0]LUUCTfjKVjJVjIVjHViCVGVi;V;ViMU7ViIUJUi@UAUi;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013Xk4QSySPUBT`i9VHViMU7ViIUJUi@UAUi;U<Ui6T6Ti>SESiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSySPkmRySPylQ<61X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2U.T_THROW_22594_s10_m5_w6_r13_pv_L0_f0112c1) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_EH_22594_s10_m5_w6_r13_pv_L0_f0112c1.

Module C_EH_22594_s10_m5_w6_r13_pv_L0_f22fe23.

Definition ROOT : sstate := (t_st T_Ubs2U.T_THROW_22594_s10_m5_w6_r13_pv_L0_f22fe23).
Definition CUTS : IMap.t template := imap_of [(144%uint63, T_Ubs2UE.T_XA_22594_7fad4_blk_w7_r14_L0); (145%uint63, T_Ubs2UE.T_XA_22594_7fad4_p682f0_w6_r13_pP)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2UE.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y`LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X0<3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZLMSLHRL<<0]LTUATgjKVjJVjIVjHViCVGVi;V;ViMU7ViIUJUiDUDUi@U@Ui;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XLMSLHRL<<0]LTUATgjKVjJVjIVjHViCVGVi;V;ViMU7ViIUJUiDUDUi@U@Ui;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XL=RL8QL<B0]LUUATgjKVjJVjIVjHViCVGVi;V;ViMU7ViIUJUiDUDUi@U@Ui;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013Xk4QSySPU@Tai9VHViMU7ViIUJUiDUDUi@U@Ui;U<Ui6T6Ti>SESiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSySPkmRySPylQ<61X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2U.T_THROW_22594_s10_m5_w6_r13_pv_L0_f22fe23) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_EH_22594_s10_m5_w6_r13_pv_L0_f22fe23.

Module C_EH_22594_s10_m5_w6_r13_pv_L0_f6b0049.

Definition ROOT : sstate := (t_st T_Ubs2U.T_THROW_22594_s10_m5_w6_r13_pv_L0_f6b0049).
Definition CUTS : IMap.t template := imap_of [(138%uint63, T_Ubs2UE.T_XA_22594_34d3b_blk_w7_r14_L0); (139%uint63, T_Ubs2UE.T_XA_22594_34d3b_p682f0_w6_r13_pP)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2UE.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y`LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X0<3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZLMSLHRL<<0]LTU;TgjKVjJVjIVjHViCVGVi;V;ViMU7ViIUJUiDUDUi@U@Ui;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XLMSLHRL<<0]LTU;TgjKVjJVjIVjHViCVGVi;V;ViMU7ViIUJUiDUDUi@U@Ui;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XL=RL8QL<B0]LUU;TgjKVjJVjIVjHViCVGVi;V;ViMU7ViIUJUiDUDUi@U@Ui;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013Xk4QSySPU:Tai9VHViMU7ViIUJUiDUDUi@U@Ui;U<Ui6T6Ti>SESiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSySPkmRySPylQ<61X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2U.T_THROW_22594_s10_m5_w6_r13_pv_L0_f6b0049) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_EH_22594_s10_m5_w6_r13_pv_L0_f6b0049.

Module C_EH_22594_s10_m5_w6_r13_pv_L0_fa9077c.

Definition ROOT : sstate := (t_st T_Ubs2U.T_THROW_22594_s10_m5_w6_r13_pv_L0_fa9077c).
Definition CUTS : IMap.t template := imap_of [(140%uint63, T_Ubs2UE.T_XA_22594_738a4_blk_w7_r14_L0); (141%uint63, T_Ubs2UE.T_XA_22594_738a4_p682f0_w6_r13_pP)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2UE.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y`LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X0<3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZLMSLHRL<<0]LTU=TfjOVjNVjMVjLViGVKVi?V?ViOU;ViIUJUi@UAUi;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XLMSLHRL<<0]LTU=TfjOVjNVjMVjLViGVKVi?V?ViOU;ViIUJUi@UAUi;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XL=RL8QL<B0]LUU=TfjOVjNVjMVjLViGVKVi?V?ViOU;ViIUJUi@UAUi;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013Xk4QSySPU<T`i=VLViOU;ViIUJUi@UAUi;U<Ui6T6Ti>SESiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSySPkmRySPylQ<61X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2U.T_THROW_22594_s10_m5_w6_r13_pv_L0_fa9077c) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_EH_22594_s10_m5_w6_r13_pv_L0_fa9077c.

Module C_EH_22594_s10_m5_w6_r13_pv_L0_fc6bbf1.

Definition ROOT : sstate := (t_st T_Ubs2U.T_THROW_22594_s10_m5_w6_r13_pv_L0_fc6bbf1).
Definition CUTS : IMap.t template := imap_of [(142%uint63, T_Ubs2UE.T_XA_22594_7b220_blk_w7_r14_L0); (143%uint63, T_Ubs2UE.T_XA_22594_7b220_p682f0_w6_r13_pP)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2UE.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y`LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X0<3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZLMSLHRL<<0]LTU?TfjKVjJVjIVjHViCVGVi;V;ViMU7ViIUJUi@UAUi;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XLMSLHRL<<0]LTU?TfjKVjJVjIVjHViCVGVi;V;ViMU7ViIUJUi@UAUi;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XL=RL8QL<B0]LUU?TfjKVjJVjIVjHViCVGVi;V;ViMU7ViIUJUi@UAUi;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013Xk4QSySPU>T`i9VHViMU7ViIUJUi@UAUi;U<Ui6T6Ti>SESiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSySPkmRySPylQ<61X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2U.T_THROW_22594_s10_m5_w6_r13_pv_L0_fc6bbf1) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_EH_22594_s10_m5_w6_r13_pv_L0_fc6bbf1.

Module C_EH_22594_s10_m5_w6_r13_pv_L0_ffe383d.

Definition ROOT : sstate := (t_st T_Ubs2U.T_THROW_22594_s10_m5_w6_r13_pv_L0_ffe383d).
Definition CUTS : IMap.t template := imap_of [(136%uint63, T_Ubs2UE.T_XA_22594_02d0c_blk_w7_r14_L0); (137%uint63, T_Ubs2UE.T_XA_22594_02d0c_p682f0_w6_r13_pP)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2UE.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y`LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X0<3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZLMSLHRL<<0]LTU9TgjOVjNVjMVjLViGVKVi?V?ViOU;ViIUJUiDUDUi@U@Ui;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XLMSLHRL<<0]LTU9TgjOVjNVjMVjLViGVKVi?V?ViOU;ViIUJUiDUDUi@U@Ui;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XL=RL8QL<B0]LUU9TgjOVjNVjMVjLViGVKVi?V?ViOU;ViIUJUiDUDUi@U@Ui;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013Xk4QSySPU8Tai=VLViOU;ViIUJUiDUDUi@U@Ui;U<Ui6T6Ti>SESiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSySPkmRySPylQ<61X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2U.T_THROW_22594_s10_m5_w6_r13_pv_L0_ffe383d) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_EH_22594_s10_m5_w6_r13_pv_L0_ffe383d.

Module C_EH_22a3c_s10_m5_w6_r13_pv_L0_f09c586.

Definition ROOT : sstate := (t_st T_Ubs2U.T_THROW_22a3c_s10_m5_w6_r13_pv_L0_f09c586).
Definition CUTS : IMap.t template := imap_of [(150%uint63, T_Ubs2UE.T_XA_22a3c_ed69c_blk_w7_r14_L0); (151%uint63, T_Ubs2UE.T_XA_22a3c_ed69c_p682f0_w6_r13_pP)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2UE.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y`LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X0<3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZLMSLHRL<<0]LTUGTfjMVjLVjKVjJViEVIVi=V=ViLU9ViIUJUi@UAUi;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XLMSLHRL<<0]LTUGTfjMVjLVjKVjJViEVIVi=V=ViLU9ViIUJUi@UAUi;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XL=RL8QL<B0]LUUGTfjMVjLVjKVjJViEVIVi=V=ViLU9ViIUJUi@UAUi;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013Xk4QSySPUFT`i;VJViLU9ViIUJUi@UAUi;U<Ui6T6Ti>SESiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSySPkmRySPylQ<61X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2U.T_THROW_22a3c_s10_m5_w6_r13_pv_L0_f09c586) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_EH_22a3c_s10_m5_w6_r13_pv_L0_f09c586.

Module C_EH_22a3c_s10_m5_w6_r13_pv_L0_f22463f.

Definition ROOT : sstate := (t_st T_Ubs2U.T_THROW_22a3c_s10_m5_w6_r13_pv_L0_f22463f).
Definition CUTS : IMap.t template := imap_of [(148%uint63, T_Ubs2UE.T_XA_22a3c_e2130_blk_w7_r14_L0); (149%uint63, T_Ubs2UE.T_XA_22a3c_e2130_p682f0_w6_r13_pP)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2UE.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y`LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X0<3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZLMSLHRL<<0]LTUETfjOVjNVjMVjLViGVKVi?V?ViMU;ViJUKUi@UAUi;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XLMSLHRL<<0]LTUETfjOVjNVjMVjLViGVKVi?V?ViMU;ViJUKUi@UAUi;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XL=RL8QL<B0]LUUETfjOVjNVjMVjLViGVKVi?V?ViMU;ViJUKUi@UAUi;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013Xk4QSySPUDT`i=VLViMU;ViJUKUi@UAUi;U<Ui6T6Ti>SESiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSySPkmRySPylQ<61X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2U.T_THROW_22a3c_s10_m5_w6_r13_pv_L0_f22463f) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_EH_22a3c_s10_m5_w6_r13_pv_L0_f22463f.

Module C_EH_22a78_s10_m5_w6_r13_pv_L0_f563d8b.

Definition ROOT : sstate := (t_st T_Ubs2U.T_THROW_22a78_s10_m5_w6_r13_pv_L0_f563d8b).
Definition CUTS : IMap.t template := imap_of [(156%uint63, T_Ubs2UE.T_XA_22a78_ab96b_blk_w7_r14_L0); (157%uint63, T_Ubs2UE.T_XA_22a78_ab96b_p682f0_w6_r13_pP)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2UE.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y`LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X0<3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZLMSLHRL<<0]LTUMTgjKVjJVjIVjHViCVGVi;V;ViMU7ViIUJUiDUDUi@U@Ui;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XLMSLHRL<<0]LTUMTgjKVjJVjIVjHViCVGVi;V;ViMU7ViIUJUiDUDUi@U@Ui;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XL=RL8QL<B0]LUUMTgjKVjJVjIVjHViCVGVi;V;ViMU7ViIUJUiDUDUi@U@Ui;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013Xk4QSySPULTai9VHViMU7ViIUJUiDUDUi@U@Ui;U<Ui6T6Ti>SESiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSySPkmRySPylQ<61X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2U.T_THROW_22a78_s10_m5_w6_r13_pv_L0_f563d8b) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_EH_22a78_s10_m5_w6_r13_pv_L0_f563d8b.

Module C_EH_22a78_s10_m5_w6_r13_pv_L0_f602539.

Definition ROOT : sstate := (t_st T_Ubs2U.T_THROW_22a78_s10_m5_w6_r13_pv_L0_f602539).
Definition CUTS : IMap.t template := imap_of [(158%uint63, T_Ubs2UE.T_XA_22a78_d91f1_blk_w7_r14_L0); (159%uint63, T_Ubs2UE.T_XA_22a78_d91f1_p682f0_w6_r13_pP)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2UE.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y`LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X0<3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZLMSLHRL<<0]LTUOTfjKVjJVjIVjHViCVGVi;V;ViMU7ViIUJUi@UAUi;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XLMSLHRL<<0]LTUOTfjKVjJVjIVjHViCVGVi;V;ViMU7ViIUJUi@UAUi;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XL=RL8QL<B0]LUUOTfjKVjJVjIVjHViCVGVi;V;ViMU7ViIUJUi@UAUi;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013Xk4QSySPUNT`i9VHViMU7ViIUJUi@UAUi;U<Ui6T6Ti>SESiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSySPkmRySPylQ<61X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2U.T_THROW_22a78_s10_m5_w6_r13_pv_L0_f602539) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_EH_22a78_s10_m5_w6_r13_pv_L0_f602539.

Module C_EH_22a78_s10_m5_w6_r13_pv_L0_f7455d2.

Definition ROOT : sstate := (t_st T_Ubs2U.T_THROW_22a78_s10_m5_w6_r13_pv_L0_f7455d2).
Definition CUTS : IMap.t template := imap_of [(162%uint63, T_Ubs2UE.T_XA_22a78_fd155_blk_w7_r14_L0); (163%uint63, T_Ubs2UE.T_XA_22a78_fd155_p682f0_w6_r13_pP)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2UE.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y`LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X0<3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZLMSLHRL<<0]LTU3UfjOVjNVjMVjLViGVKVi?V?ViOU;ViIUJUi@UAUi;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XLMSLHRL<<0]LTU3UfjOVjNVjMVjLViGVKVi?V?ViOU;ViIUJUi@UAUi;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XL=RL8QL<B0]LUU3UfjOVjNVjMVjLViGVKVi?V?ViOU;ViIUJUi@UAUi;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013Xk4QSySPU2U`i=VLViOU;ViIUJUi@UAUi;U<Ui6T6Ti>SESiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSySPkmRySPylQ<61X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2U.T_THROW_22a78_s10_m5_w6_r13_pv_L0_f7455d2) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_EH_22a78_s10_m5_w6_r13_pv_L0_f7455d2.

Module C_EH_22a78_s10_m5_w6_r13_pv_L0_f7fd4f7.

Definition ROOT : sstate := (t_st T_Ubs2U.T_THROW_22a78_s10_m5_w6_r13_pv_L0_f7fd4f7).
Definition CUTS : IMap.t template := imap_of [(154%uint63, T_Ubs2UE.T_XA_22a78_8d778_blk_w7_r14_L0); (155%uint63, T_Ubs2UE.T_XA_22a78_8d778_p682f0_w6_r13_pP)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2UE.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y`LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X0<3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZLMSLHRL<<0]LTUKTgjKVjJVjIVjHViCVGVi;V;ViMU7ViIUJUiDUDUi@U@Ui;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XLMSLHRL<<0]LTUKTgjKVjJVjIVjHViCVGVi;V;ViMU7ViIUJUiDUDUi@U@Ui;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XL=RL8QL<B0]LUUKTgjKVjJVjIVjHViCVGVi;V;ViMU7ViIUJUiDUDUi@U@Ui;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013Xk4QSySPUJTai9VHViMU7ViIUJUiDUDUi@U@Ui;U<Ui6T6Ti>SESiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSySPkmRySPylQ<61X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2U.T_THROW_22a78_s10_m5_w6_r13_pv_L0_f7fd4f7) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_EH_22a78_s10_m5_w6_r13_pv_L0_f7fd4f7.

Module C_EH_22a78_s10_m5_w6_r13_pv_L0_fb0e3f3.

Definition ROOT : sstate := (t_st T_Ubs2U.T_THROW_22a78_s10_m5_w6_r13_pv_L0_fb0e3f3).
Definition CUTS : IMap.t template := imap_of [(152%uint63, T_Ubs2UE.T_XA_22a78_515a8_blk_w7_r14_L0); (153%uint63, T_Ubs2UE.T_XA_22a78_515a8_p682f0_w6_r13_pP)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2UE.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y`LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X0<3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZLMSLHRL<<0]LTUITgjOVjNVjMVjLViGVKVi?V?ViOU;ViIUJUiDUDUi@U@Ui;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XLMSLHRL<<0]LTUITgjOVjNVjMVjLViGVKVi?V?ViOU;ViIUJUiDUDUi@U@Ui;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XL=RL8QL<B0]LUUITgjOVjNVjMVjLViGVKVi?V?ViOU;ViIUJUiDUDUi@U@Ui;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013Xk4QSySPUHTai=VLViOU;ViIUJUiDUDUi@U@Ui;U<Ui6T6Ti>SESiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSySPkmRySPylQ<61X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2U.T_THROW_22a78_s10_m5_w6_r13_pv_L0_fb0e3f3) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_EH_22a78_s10_m5_w6_r13_pv_L0_fb0e3f3.

Module C_EH_22a78_s10_m5_w6_r13_pv_L0_fec03a0.

Definition ROOT : sstate := (t_st T_Ubs2U.T_THROW_22a78_s10_m5_w6_r13_pv_L0_fec03a0).
Definition CUTS : IMap.t template := imap_of [(160%uint63, T_Ubs2UE.T_XA_22a78_e82d1_blk_w7_r14_L0); (161%uint63, T_Ubs2UE.T_XA_22a78_e82d1_p682f0_w6_r13_pP)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2UE.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y`LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X0<3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZLMSLHRL<<0]LTU1UfjKVjJVjIVjHViCVGVi;V;ViMU7ViIUJUi@UAUi;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XLMSLHRL<<0]LTU1UfjKVjJVjIVjHViCVGVi;V;ViMU7ViIUJUi@UAUi;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XL=RL8QL<B0]LUU1UfjKVjJVjIVjHViCVGVi;V;ViMU7ViIUJUi@UAUi;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013Xk4QSySPU0U`i9VHViMU7ViIUJUi@UAUi;U<Ui6T6Ti>SESiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSySPkmRySPylQ<61X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2U.T_THROW_22a78_s10_m5_w6_r13_pv_L0_fec03a0) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_EH_22a78_s10_m5_w6_r13_pv_L0_fec03a0.

Module C_EH_236d8_s8_m5_w6_r13_pv_L0_f14f430.

Definition ROOT : sstate := (t_st T_Ubs2U.T_THROW_236d8_s8_m5_w6_r13_pv_L0_f14f430).
Definition CUTS : IMap.t template := imap_of [(168%uint63, T_Ubs2UE.T_XA_236d8_175a8_blk_w7_r14_L0); (169%uint63, T_Ubs2UE.T_XA_236d8_175a8_p682f0_w6_r13_pP)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2UE.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y`LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X0<3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZLMSLHRP5WPL<<0]P=WPP>WPP?WPP@WPPAWPLTU9Ujj=Wj<Wj;Wj:Wj9Wj8Wj7Wj6Wj5Wj4WiOU1WiLUMUi@U@Ui;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XLMSLHRP5WPL<<0]P=WPP>WPP?WPP@WPPAWPLTU9Ujj=Wj<Wj;Wj:Wj9Wj8Wj7Wj6Wj5Wj4WiOU1WiLUMUi@U@Ui;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XL=RL8QP5WPL<B0]P=WPP>WPP?WPP@WPPAWPLUU9Ujj=Wj<Wj;Wj:Wj9Wj8Wj7Wj6Wj5Wj4WiOU1WiLUMUi@U@Ui;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013Xk4QSySPPBWPP4WPP5WPP6WPP7WPP8WPP9WPP:WPP;WPP<WPP=WPP>WPP?WPP@WPPAWPU8UojBWjAWj@Wj?Wj>Wj=Wj<Wj;Wj:Wj9Wj8Wj7Wj6Wj5Wj4Wi3W3WiOU1WiLUMUi@U@Ui;U<Ui6T6Ti>SESiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSySPkmRySPylQ<61X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2U.T_THROW_236d8_s8_m5_w6_r13_pv_L0_f14f430) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_EH_236d8_s8_m5_w6_r13_pv_L0_f14f430.

Module C_EH_236d8_s8_m5_w6_r13_pv_L0_f2dbbe6.

Definition ROOT : sstate := (t_st T_Ubs2U.T_THROW_236d8_s8_m5_w6_r13_pv_L0_f2dbbe6).
Definition CUTS : IMap.t template := imap_of [(188%uint63, T_Ubs2UE.T_XA_236d8_c92f2_blk_w7_r14_L0); (189%uint63, T_Ubs2UE.T_XA_236d8_c92f2_p682f0_w6_r13_pP)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2UE.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y`LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X0<3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZLMSLHRP5WPL<<0]P=WPP>WPP?WPP@WPPAWPLTUMUkj=Wj<Wj;Wj:Wj9Wj8Wj7Wj6Wj5Wj4Wi0V1WiMUNUiHUHUi@U@Ui;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XLMSLHRP5WPL<<0]P=WPP>WPP?WPP@WPPAWPLTUMUkj=Wj<Wj;Wj:Wj9Wj8Wj7Wj6Wj5Wj4Wi0V1WiMUNUiHUHUi@U@Ui;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XL=RL8QP5WPL<B0]P=WPP>WPP?WPP@WPPAWPLUUMUkj=Wj<Wj;Wj:Wj9Wj8Wj7Wj6Wj5Wj4Wi0V1WiMUNUiHUHUi@U@Ui;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013Xk4QSySPPBWPP4WPP5WPP6WPP7WPP8WPP9WPP:WPP;WPP<WPP=WPP>WPP?WPP@WPPAWPULU0QjBWjAWj@Wj?Wj>Wj=Wj<Wj;Wj:Wj9Wj8Wj7Wj6Wj5Wj4Wi3W3Wi0V1WiMUNUiHUHUi@U@Ui;U<Ui6T6Ti>SESiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSySPkmRySPylQ<61X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2U.T_THROW_236d8_s8_m5_w6_r13_pv_L0_f2dbbe6) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_EH_236d8_s8_m5_w6_r13_pv_L0_f2dbbe6.

Module C_EH_236d8_s8_m5_w6_r13_pv_L0_f341c20.

Definition ROOT : sstate := (t_st T_Ubs2U.T_THROW_236d8_s8_m5_w6_r13_pv_L0_f341c20).
Definition CUTS : IMap.t template := imap_of [(176%uint63, T_Ubs2UE.T_XA_236d8_6a133_blk_w7_r14_L0); (177%uint63, T_Ubs2UE.T_XA_236d8_6a133_p682f0_w6_r13_pP)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2UE.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y`LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X0<3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZLMSLHRL<<0]P>WPP?WPP@WPPAWPPBWPLTUAUkj=Wj<Wj;Wj:Wj9Wj8Wj7Wi6W6Wj5Wj4Wi0V2WiMUNUiHUHUi@U@Ui;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XLMSLHRL<<0]P>WPP?WPP@WPPAWPPBWPLTUAUkj=Wj<Wj;Wj:Wj9Wj8Wj7Wi6W6Wj5Wj4Wi0V2WiMUNUiHUHUi@U@Ui;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XL=RL8QL<B0]P>WPP?WPP@WPPAWPPBWPLUUAUkj=Wj<Wj;Wj:Wj9Wj8Wj7Wi6W6Wj5Wj4Wi0V2WiMUNUiHUHUi@U@Ui;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013Xk4QSySPPCWPP4WPP5WPP6WPP7WPP8WPP9WPP:WPP;WPP<WPP=WPP>WPP?WPP@WPPAWPPBWPU@U0QjCWjBWjAWj@Wj?Wj>Wj=Wj<Wj;Wj:Wj9Wj8Wj7Wj6Wj5Wj4Wi0V2WiMUNUiHUHUi@U@Ui;U<Ui6T6Ti>SESiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSySPkmRySPylQ<61X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2U.T_THROW_236d8_s8_m5_w6_r13_pv_L0_f341c20) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_EH_236d8_s8_m5_w6_r13_pv_L0_f341c20.

Module C_EH_236d8_s8_m5_w6_r13_pv_L0_f73af75.

Definition ROOT : sstate := (t_st T_Ubs2U.T_THROW_236d8_s8_m5_w6_r13_pv_L0_f73af75).
Definition CUTS : IMap.t template := imap_of [(166%uint63, T_Ubs2UE.T_XA_236d8_15ebf_blk_w7_r14_L0); (167%uint63, T_Ubs2UE.T_XA_236d8_15ebf_p682f0_w6_r13_pP)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2UE.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y`LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X0<3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZLMSLHRL<<0]P;WPP<WPP=WPP>WPP?WPLTU7Ujj<Wj;Wj:Wj9Wj8Wj7Wj6Wj5Wj4Wi3W3WiOUOViLUMUi@U@Ui;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XLMSLHRL<<0]P;WPP<WPP=WPP>WPP?WPLTU7Ujj<Wj;Wj:Wj9Wj8Wj7Wj6Wj5Wj4Wi3W3WiOUOViLUMUi@U@Ui;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XL=RL8QL<B0]P;WPP<WPP=WPP>WPP?WPLUU7Ujj<Wj;Wj:Wj9Wj8Wj7Wj6Wj5Wj4Wi3W3WiOUOViLUMUi@U@Ui;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013Xk4QSySPP@WPP4WPP5WPP6WPP7WPP8WPP9WPP:WPP;WPP<WPP=WPP>WPP?WPU6Umj@Wj?Wj>Wj=Wj<Wj;Wj:Wj9Wj8Wj7Wj6Wj5Wj4Wi1W3WiOUOViLUMUi@U@Ui;U<Ui6T6Ti>SESiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSySPkmRySPylQ<61X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2U.T_THROW_236d8_s8_m5_w6_r13_pv_L0_f73af75) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_EH_236d8_s8_m5_w6_r13_pv_L0_f73af75.

Module C_EH_236d8_s8_m5_w6_r13_pv_L0_f796e66.

Definition ROOT : sstate := (t_st T_Ubs2U.T_THROW_236d8_s8_m5_w6_r13_pv_L0_f796e66).
Definition CUTS : IMap.t template := imap_of [(174%uint63, T_Ubs2UE.T_XA_236d8_52706_blk_w7_r14_L0); (175%uint63, T_Ubs2UE.T_XA_236d8_52706_p682f0_w6_r13_pP)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2UE.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y`LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X0<3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZLMSLHRP4WPL<<0]P<WPP=WPP>WPP?WPP@WPLTU?Ukj=Wj<Wj;Wj:Wj9Wj8Wj7Wj6Wj5Wj4Wi0V0WiMUNUiHUHUi@U@Ui;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XLMSLHRP4WPL<<0]P<WPP=WPP>WPP?WPP@WPLTU?Ukj=Wj<Wj;Wj:Wj9Wj8Wj7Wj6Wj5Wj4Wi0V0WiMUNUiHUHUi@U@Ui;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XL=RL8QP4WPL<B0]P<WPP=WPP>WPP?WPP@WPLUU?Ukj=Wj<Wj;Wj:Wj9Wj8Wj7Wj6Wj5Wj4Wi0V0WiMUNUiHUHUi@U@Ui;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013Xk4QSySPPAWPP4WPP5WPP6WPP7WPP8WPP9WPP:WPP;WPP<WPP=WPP>WPP?WPP@WPU>UojAWj@Wj?Wj>Wj=Wj<Wj;Wj:Wj9Wj8Wj7Wj6Wj5Wj4Wi2W3Wi0V0WiMUNUiHUHUi@U@Ui;U<Ui6T6Ti>SESiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSySPkmRySPylQ<61X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2U.T_THROW_236d8_s8_m5_w6_r13_pv_L0_f796e66) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_EH_236d8_s8_m5_w6_r13_pv_L0_f796e66.

Module C_EH_236d8_s8_m5_w6_r13_pv_L0_f8199b2.

Definition ROOT : sstate := (t_st T_Ubs2U.T_THROW_236d8_s8_m5_w6_r13_pv_L0_f8199b2).
Definition CUTS : IMap.t template := imap_of [(190%uint63, T_Ubs2UE.T_XA_236d8_ea939_blk_w7_r14_L0); (191%uint63, T_Ubs2UE.T_XA_236d8_ea939_p682f0_w6_r13_pP)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2UE.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y`LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X0<3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZLMSLHRP7WPL<<0]P?WPP@WPPAWPPBWPPCWPLTUOUkj=Wj<Wj;Wj:Wj9Wj8Wj7Wj6Wj5Wj4Wi0V3WiMUNUiHUHUi@U@Ui;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XLMSLHRP7WPL<<0]P?WPP@WPPAWPPBWPPCWPLTUOUkj=Wj<Wj;Wj:Wj9Wj8Wj7Wj6Wj5Wj4Wi0V3WiMUNUiHUHUi@U@Ui;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XL=RL8QP7WPL<B0]P?WPP@WPPAWPPBWPPCWPLUUOUkj=Wj<Wj;Wj:Wj9Wj8Wj7Wj6Wj5Wj4Wi0V3WiMUNUiHUHUi@U@Ui;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013Xk4QSySPPDWPUNUbi5WCWj4Wi0V3WiMUNUiHUHUi@U@Ui;U<Ui6T6Ti>SESiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSySPkmRySPylQ<61X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2U.T_THROW_236d8_s8_m5_w6_r13_pv_L0_f8199b2) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_EH_236d8_s8_m5_w6_r13_pv_L0_f8199b2.

Module C_EH_236d8_s8_m5_w6_r13_pv_L0_f853637.

Definition ROOT : sstate := (t_st T_Ubs2U.T_THROW_236d8_s8_m5_w6_r13_pv_L0_f853637).
Definition CUTS : IMap.t template := imap_of [(180%uint63, T_Ubs2UE.T_XA_236d8_8204c_blk_w7_r14_L0); (181%uint63, T_Ubs2UE.T_XA_236d8_8204c_p682f0_w6_r13_pP)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2UE.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y`LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X0<3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZLMSLHRP7WPL<<0]P?WPP@WPPAWPPBWPPCWPLTUEUkj=Wj<Wj;Wj:Wj9Wj8Wj7Wj6Wj5Wj4Wi0V3WiMUNUiHUHUi@U@Ui;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XLMSLHRP7WPL<<0]P?WPP@WPPAWPPBWPPCWPLTUEUkj=Wj<Wj;Wj:Wj9Wj8Wj7Wj6Wj5Wj4Wi0V3WiMUNUiHUHUi@U@Ui;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XL=RL8QP7WPL<B0]P?WPP@WPPAWPPBWPPCWPLUUEUkj=Wj<Wj;Wj:Wj9Wj8Wj7Wj6Wj5Wj4Wi0V3WiMUNUiHUHUi@U@Ui;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013Xk4QSySPPDWPUDUbi5WCWj4Wi0V3WiMUNUiHUHUi@U@Ui;U<Ui6T6Ti>SESiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSySPkmRySPylQ<61X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2U.T_THROW_236d8_s8_m5_w6_r13_pv_L0_f853637) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_EH_236d8_s8_m5_w6_r13_pv_L0_f853637.

Module C_EH_236d8_s8_m5_w6_r13_pv_L0_f87081d.

Definition ROOT : sstate := (t_st T_Ubs2U.T_THROW_236d8_s8_m5_w6_r13_pv_L0_f87081d).
Definition CUTS : IMap.t template := imap_of [(172%uint63, T_Ubs2UE.T_XA_236d8_3e1cd_blk_w7_r14_L0); (173%uint63, T_Ubs2UE.T_XA_236d8_3e1cd_p682f0_w6_r13_pP)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2UE.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y`LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X0<3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZLMSLHRL<<0]P>WPP?WPP@WPPAWPPBWPLTU=Ukj=Wj<Wj;Wj:Wj9Wj8Wj7Wi6W6Wj5Wj4Wi0V2WiMUNUiHUHUi@U@Ui;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XLMSLHRL<<0]P>WPP?WPP@WPPAWPPBWPLTU=Ukj=Wj<Wj;Wj:Wj9Wj8Wj7Wi6W6Wj5Wj4Wi0V2WiMUNUiHUHUi@U@Ui;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XL=RL8QL<B0]P>WPP?WPP@WPPAWPPBWPLUU=Ukj=Wj<Wj;Wj:Wj9Wj8Wj7Wi6W6Wj5Wj4Wi0V2WiMUNUiHUHUi@U@Ui;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013Xk4QSySPPCWPP4WPP5WPP6WPP7WPP8WPP9WPP:WPP;WPP<WPP=WPP>WPP?WPP@WPPAWPPBWPU<U0QjCWjBWjAWj@Wj?Wj>Wj=Wj<Wj;Wj:Wj9Wj8Wj7Wj6Wj5Wj4Wi0V2WiMUNUiHUHUi@U@Ui;U<Ui6T6Ti>SESiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSySPkmRySPylQ<61X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2U.T_THROW_236d8_s8_m5_w6_r13_pv_L0_f87081d) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_EH_236d8_s8_m5_w6_r13_pv_L0_f87081d.

Module C_EH_236d8_s8_m5_w6_r13_pv_L0_f907e85.

Definition ROOT : sstate := (t_st T_Ubs2U.T_THROW_236d8_s8_m5_w6_r13_pv_L0_f907e85).
Definition CUTS : IMap.t template := imap_of [(184%uint63, T_Ubs2UE.T_XA_236d8_b649e_blk_w7_r14_L0); (185%uint63, T_Ubs2UE.T_XA_236d8_b649e_p682f0_w6_r13_pP)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2UE.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y`LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X0<3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZLMSLHRL<<0]P;WPP<WPP=WPP>WPP?WPLTUIUjj<Wj;Wj:Wj9Wj8Wj7Wj6Wj5Wj4Wi3W3WiOUOViLUMUi@U@Ui;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XLMSLHRL<<0]P;WPP<WPP=WPP>WPP?WPLTUIUjj<Wj;Wj:Wj9Wj8Wj7Wj6Wj5Wj4Wi3W3WiOUOViLUMUi@U@Ui;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XL=RL8QL<B0]P;WPP<WPP=WPP>WPP?WPLUUIUjj<Wj;Wj:Wj9Wj8Wj7Wj6Wj5Wj4Wi3W3WiOUOViLUMUi@U@Ui;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013Xk4QSySPP@WPP4WPP5WPP6WPP7WPP8WPP9WPP:WPP;WPP<WPP=WPP>WPP?WPUHUmj@Wj?Wj>Wj=Wj<Wj;Wj:Wj9Wj8Wj7Wj6Wj5Wj4Wi1W3WiOUOViLUMUi@U@Ui;U<Ui6T6Ti>SESiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSySPkmRySPylQ<61X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2U.T_THROW_236d8_s8_m5_w6_r13_pv_L0_f907e85) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_EH_236d8_s8_m5_w6_r13_pv_L0_f907e85.

Module C_EH_236d8_s8_m5_w6_r13_pv_L0_f9a9bb5.

Definition ROOT : sstate := (t_st T_Ubs2U.T_THROW_236d8_s8_m5_w6_r13_pv_L0_f9a9bb5).
Definition CUTS : IMap.t template := imap_of [(182%uint63, T_Ubs2UE.T_XA_236d8_b5974_blk_w7_r14_L0); (183%uint63, T_Ubs2UE.T_XA_236d8_b5974_p682f0_w6_r13_pP)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2UE.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y`LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X0<3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZLMSLHRP5WPL<<0]P=WPP>WPP?WPP@WPPAWPLTUGUjj=Wj<Wj;Wj:Wj9Wj8Wj7Wj6Wj5Wj4WiOU1WiLUMUi@U@Ui;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XLMSLHRP5WPL<<0]P=WPP>WPP?WPP@WPPAWPLTUGUjj=Wj<Wj;Wj:Wj9Wj8Wj7Wj6Wj5Wj4WiOU1WiLUMUi@U@Ui;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XL=RL8QP5WPL<B0]P=WPP>WPP?WPP@WPPAWPLUUGUjj=Wj<Wj;Wj:Wj9Wj8Wj7Wj6Wj5Wj4WiOU1WiLUMUi@U@Ui;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013Xk4QSySPPBWPP4WPP5WPP6WPP7WPP8WPP9WPP:WPP;WPP<WPP=WPP>WPP?WPP@WPPAWPUFUojBWjAWj@Wj?Wj>Wj=Wj<Wj;Wj:Wj9Wj8Wj7Wj6Wj5Wj4Wi3W3WiOU1WiLUMUi@U@Ui;U<Ui6T6Ti>SESiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSySPkmRySPylQ<61X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2U.T_THROW_236d8_s8_m5_w6_r13_pv_L0_f9a9bb5) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_EH_236d8_s8_m5_w6_r13_pv_L0_f9a9bb5.

Module C_EH_236d8_s8_m5_w6_r13_pv_L0_fbb59fd.

Definition ROOT : sstate := (t_st T_Ubs2U.T_THROW_236d8_s8_m5_w6_r13_pv_L0_fbb59fd).
Definition CUTS : IMap.t template := imap_of [(186%uint63, T_Ubs2UE.T_XA_236d8_c7850_blk_w7_r14_L0); (187%uint63, T_Ubs2UE.T_XA_236d8_c7850_p682f0_w6_r13_pP)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2UE.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y`LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X0<3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZLMSLHRP5WPL<<0]P=WPP>WPP?WPP@WPPAWPLTUKUjj=Wj<Wj;Wj:Wj9Wj8Wj7Wj6Wj5Wj4WiOU1WiLUMUi@U@Ui;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XLMSLHRP5WPL<<0]P=WPP>WPP?WPP@WPPAWPLTUKUjj=Wj<Wj;Wj:Wj9Wj8Wj7Wj6Wj5Wj4WiOU1WiLUMUi@U@Ui;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XL=RL8QP5WPL<B0]P=WPP>WPP?WPP@WPPAWPLUUKUjj=Wj<Wj;Wj:Wj9Wj8Wj7Wj6Wj5Wj4WiOU1WiLUMUi@U@Ui;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013Xk4QSySPPBWPP4WPP5WPP6WPP7WPP8WPP9WPP:WPP;WPP<WPP=WPP>WPP?WPP@WPPAWPUJUojBWjAWj@Wj?Wj>Wj=Wj<Wj;Wj:Wj9Wj8Wj7Wj6Wj5Wj4Wi3W3WiOU1WiLUMUi@U@Ui;U<Ui6T6Ti>SESiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSySPkmRySPylQ<61X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2U.T_THROW_236d8_s8_m5_w6_r13_pv_L0_fbb59fd) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_EH_236d8_s8_m5_w6_r13_pv_L0_fbb59fd.

Module C_EH_236d8_s8_m5_w6_r13_pv_L0_fcadae6.

Definition ROOT : sstate := (t_st T_Ubs2U.T_THROW_236d8_s8_m5_w6_r13_pv_L0_fcadae6).
Definition CUTS : IMap.t template := imap_of [(164%uint63, T_Ubs2UE.T_XA_236d8_0c366_blk_w7_r14_L0); (165%uint63, T_Ubs2UE.T_XA_236d8_0c366_p682f0_w6_r13_pP)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2UE.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y`LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X0<3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZLMSLHRP7WPL<<0]P?WPP@WPPAWPPBWPPCWPLTU5Ukj=Wj<Wj;Wj:Wj9Wj8Wj7Wj6Wj5Wj4Wi1V3WiNUOUiHUIUi@U@Ui;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XLMSLHRP7WPL<<0]P?WPP@WPPAWPPBWPPCWPLTU5Ukj=Wj<Wj;Wj:Wj9Wj8Wj7Wj6Wj5Wj4Wi1V3WiNUOUiHUIUi@U@Ui;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XL=RL8QP7WPL<B0]P?WPP@WPPAWPPBWPPCWPLUU5Ukj=Wj<Wj;Wj:Wj9Wj8Wj7Wj6Wj5Wj4Wi1V3WiNUOUiHUIUi@U@Ui;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013Xk4QSySPPDWPU4Ubi5WCWj4Wi1V3WiNUOUiHUIUi@U@Ui;U<Ui6T6Ti>SESiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSySPkmRySPylQ<61X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2U.T_THROW_236d8_s8_m5_w6_r13_pv_L0_fcadae6) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_EH_236d8_s8_m5_w6_r13_pv_L0_fcadae6.

Module C_EH_236d8_s8_m5_w6_r13_pv_L0_fcd577e.

Definition ROOT : sstate := (t_st T_Ubs2U.T_THROW_236d8_s8_m5_w6_r13_pv_L0_fcd577e).
Definition CUTS : IMap.t template := imap_of [(178%uint63, T_Ubs2UE.T_XA_236d8_6db84_blk_w7_r14_L0); (179%uint63, T_Ubs2UE.T_XA_236d8_6db84_p682f0_w6_r13_pP)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2UE.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y`LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X0<3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZLMSLHRP5WPL<<0]P=WPP>WPP?WPP@WPPAWPLTUCUkj=Wj<Wj;Wj:Wj9Wj8Wj7Wj6Wj5Wj4Wi0V1WiMUNUiHUHUi@U@Ui;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XLMSLHRP5WPL<<0]P=WPP>WPP?WPP@WPPAWPLTUCUkj=Wj<Wj;Wj:Wj9Wj8Wj7Wj6Wj5Wj4Wi0V1WiMUNUiHUHUi@U@Ui;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XL=RL8QP5WPL<B0]P=WPP>WPP?WPP@WPPAWPLUUCUkj=Wj<Wj;Wj:Wj9Wj8Wj7Wj6Wj5Wj4Wi0V1WiMUNUiHUHUi@U@Ui;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013Xk4QSySPPBWPP4WPP5WPP6WPP7WPP8WPP9WPP:WPP;WPP<WPP=WPP>WPP?WPP@WPPAWPUBU0QjBWjAWj@Wj?Wj>Wj=Wj<Wj;Wj:Wj9Wj8Wj7Wj6Wj5Wj4Wi3W3Wi0V1WiMUNUiHUHUi@U@Ui;U<Ui6T6Ti>SESiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSySPkmRySPylQ<61X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2U.T_THROW_236d8_s8_m5_w6_r13_pv_L0_fcd577e) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_EH_236d8_s8_m5_w6_r13_pv_L0_fcd577e.

Module C_EH_236d8_s8_m5_w6_r13_pv_L0_fd804b6.

Definition ROOT : sstate := (t_st T_Ubs2U.T_THROW_236d8_s8_m5_w6_r13_pv_L0_fd804b6).
Definition CUTS : IMap.t template := imap_of [(170%uint63, T_Ubs2UE.T_XA_236d8_1cfef_blk_w7_r14_L0); (171%uint63, T_Ubs2UE.T_XA_236d8_1cfef_p682f0_w6_r13_pP)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2UE.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y`LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X0<3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZLMSLHRP7WPL<<0]P?WPP@WPPAWPPBWPPCWPLTU;Ujj=Wj<Wj;Wj:Wj9Wj8Wj7Wj6Wj5Wj4WiOU3WiLUMUi@U@Ui;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XLMSLHRP7WPL<<0]P?WPP@WPPAWPPBWPPCWPLTU;Ujj=Wj<Wj;Wj:Wj9Wj8Wj7Wj6Wj5Wj4WiOU3WiLUMUi@U@Ui;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XL=RL8QP7WPL<B0]P?WPP@WPPAWPPBWPPCWPLUU;Ujj=Wj<Wj;Wj:Wj9Wj8Wj7Wj6Wj5Wj4WiOU3WiLUMUi@U@Ui;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013Xk4QSySPPDWPU:Uai5WCWj4WiOU3WiLUMUi@U@Ui;U<Ui6T6Ti>SESiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSySPkmRySPylQ<61X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2U.T_THROW_236d8_s8_m5_w6_r13_pv_L0_fd804b6) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_EH_236d8_s8_m5_w6_r13_pv_L0_fd804b6.

Module C_EH_52944_s8_m5_w5_r12_pv_L0_f2b130e.

Definition ROOT : sstate := (t_st T_Ubs2U.T_THROW_52944_s8_m5_w5_r12_pv_L0_f2b130e).
Definition CUTS : IMap.t template := imap_of [(210%uint63, T_Ubs2UE.T_XA_52944_73b21_blk_w6_r13_L0); (211%uint63, T_Ubs2UE.T_XA_52944_73b21_p682f0_w5_r12_pP)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2UE.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y`LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X0<3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZLMSLHRL<<0]P5WPP6WPP7WPP8WPP9WPLTUCVij<Wj;Wj:Wj9Wj8Wj7Wj6Wj5Wj4WiMVMViMUIViJUKUi;U;Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XLMSLHRL<<0]P5WPP6WPP7WPP8WPP9WPLTUCVij<Wj;Wj:Wj9Wj8Wj7Wj6Wj5Wj4WiMVMViMUIViJUKUi;U;Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XL=RL8QL<B0]P5WPP6WPP7WPP8WPP9WPLUUCVij<Wj;Wj:Wj9Wj8Wj7Wj6Wj5Wj4WiMVMViMUIViJUKUi;U;Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013Xk4QSySPP:WPP4WPP5WPP6WPP7WPP8WPP9WPUBVfj:Wj9Wj8Wj7Wj6Wj5Wj4WiKV3WiMUIViJUKUi;U;Ui6T6Ti>SESiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSySPkmRySPylQ<61X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2U.T_THROW_52944_s8_m5_w5_r12_pv_L0_f2b130e) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_EH_52944_s8_m5_w5_r12_pv_L0_f2b130e.

Module C_EH_52944_s8_m5_w6_r13_pv_L0_f03adaa.

Definition ROOT : sstate := (t_st T_Ubs2U.T_THROW_52944_s8_m5_w6_r13_pv_L0_f03adaa).
Definition CUTS : IMap.t template := imap_of [(198%uint63, T_Ubs2UE.T_XA_52944_15e9e_blk_w7_r14_L0); (199%uint63, T_Ubs2UE.T_XA_52944_15e9e_p682f0_w6_r13_pP)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2UE.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y`LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X0<3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZLMSLHRL<<0]LTU7Vgj2Wj1Wj0WjOViJVNViBVBVi1V>ViNUOUiIUIUi@UAUi;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XLMSLHRL<<0]LTU7Vgj2Wj1Wj0WjOViJVNViBVBVi1V>ViNUOUiIUIUi@UAUi;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XL=RL8QL<B0]LUU7Vgj2Wj1Wj0WjOViJVNViBVBVi1V>ViNUOUiIUIUi@UAUi;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013Xk4QSySPU6Vai@VOVi1V>ViNUOUiIUIUi@UAUi;U<Ui6T6Ti>SESiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSySPkmRySPylQ<61X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2U.T_THROW_52944_s8_m5_w6_r13_pv_L0_f03adaa) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_EH_52944_s8_m5_w6_r13_pv_L0_f03adaa.

Module C_EH_52944_s8_m5_w6_r13_pv_L0_f03df9d.

Definition ROOT : sstate := (t_st T_Ubs2U.T_THROW_52944_s8_m5_w6_r13_pv_L0_f03df9d).
Definition CUTS : IMap.t template := imap_of [(216%uint63, T_Ubs2UE.T_XA_52944_8bc0a_blk_w7_r14_L0); (217%uint63, T_Ubs2UE.T_XA_52944_8bc0a_p682f0_w6_r13_pP)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2UE.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y`LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X0<3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZLMSLHRL<<0]LTUIVgj7Wj6Wj5Wj4WiOV3WiGVGVi1VCViNUOUiIUIUi@UAUi;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XLMSLHRL<<0]LTUIVgj7Wj6Wj5Wj4WiOV3WiGVGVi1VCViNUOUiIUIUi@UAUi;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XL=RL8QL<B0]LUUIVgj7Wj6Wj5Wj4WiOV3WiGVGVi1VCViNUOUiIUIUi@UAUi;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013Xk4QSySPUHVaiEV4Wi1VCViNUOUiIUIUi@UAUi;U<Ui6T6Ti>SESiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSySPkmRySPylQ<61X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2U.T_THROW_52944_s8_m5_w6_r13_pv_L0_f03df9d) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_EH_52944_s8_m5_w6_r13_pv_L0_f03df9d.

Module C_EH_52944_s8_m5_w6_r13_pv_L0_f076dee.

Definition ROOT : sstate := (t_st T_Ubs2U.T_THROW_52944_s8_m5_w6_r13_pv_L0_f076dee).
Definition CUTS : IMap.t template := imap_of [(222%uint63, T_Ubs2UE.T_XA_52944_bb715_blk_w7_r14_L0); (223%uint63, T_Ubs2UE.T_XA_52944_bb715_p682f0_w6_r13_pP)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2UE.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y`LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X0<3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZLMSLHRL<<0]LTUOVgj1Wj0WjOVjNViIVMViAVAVi1V=ViNUOUiIUIUi@UAUi;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XLMSLHRL<<0]LTUOVgj1Wj0WjOVjNViIVMViAVAVi1V=ViNUOUiIUIUi@UAUi;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XL=RL8QL<B0]LUUOVgj1Wj0WjOVjNViIVMViAVAVi1V=ViNUOUiIUIUi@UAUi;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013Xk4QSySPUNVai?VNVi1V=ViNUOUiIUIUi@UAUi;U<Ui6T6Ti>SESiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSySPkmRySPylQ<61X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2U.T_THROW_52944_s8_m5_w6_r13_pv_L0_f076dee) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_EH_52944_s8_m5_w6_r13_pv_L0_f076dee.

Module C_EH_52944_s8_m5_w6_r13_pv_L0_f0e861c.

Definition ROOT : sstate := (t_st T_Ubs2U.T_THROW_52944_s8_m5_w6_r13_pv_L0_f0e861c).
Definition CUTS : IMap.t template := imap_of [(212%uint63, T_Ubs2UE.T_XA_52944_81f3e_blk_w7_r14_L0); (213%uint63, T_Ubs2UE.T_XA_52944_81f3e_p682f0_w6_r13_pP)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2UE.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y`LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X0<3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZLMSLHRL<<0]LTUEVgj4Wj3Wj2Wj1WiLV0WiDVDVi1V@ViNUOUiIUIUi@UAUi;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XLMSLHRL<<0]LTUEVgj4Wj3Wj2Wj1WiLV0WiDVDVi1V@ViNUOUiIUIUi@UAUi;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XL=RL8QL<B0]LUUEVgj4Wj3Wj2Wj1WiLV0WiDVDVi1V@ViNUOUiIUIUi@UAUi;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013Xk4QSySPUDVaiBV1Wi1V@ViNUOUiIUIUi@UAUi;U<Ui6T6Ti>SESiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSySPkmRySPylQ<61X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2U.T_THROW_52944_s8_m5_w6_r13_pv_L0_f0e861c) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_EH_52944_s8_m5_w6_r13_pv_L0_f0e861c.

Module C_EH_52944_s8_m5_w6_r13_pv_L0_f0edd6e.

Definition ROOT : sstate := (t_st T_Ubs2U.T_THROW_52944_s8_m5_w6_r13_pv_L0_f0edd6e).
Definition CUTS : IMap.t template := imap_of [(196%uint63, T_Ubs2UE.T_XA_52944_0db6b_blk_w7_r14_L0); (197%uint63, T_Ubs2UE.T_XA_52944_0db6b_p682f0_w6_r13_pP)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2UE.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y`LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X0<3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZLMSLHRL<<0]LTU5Vgj3Wj2Wj1Wj0WiKVOViCVCVi1V?ViNUOUiIUIUi@UAUi;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XLMSLHRL<<0]LTU5Vgj3Wj2Wj1Wj0WiKVOViCVCVi1V?ViNUOUiIUIUi@UAUi;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XL=RL8QL<B0]LUU5Vgj3Wj2Wj1Wj0WiKVOViCVCVi1V?ViNUOUiIUIUi@UAUi;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013Xk4QSySPU4VaiAV0Wi1V?ViNUOUiIUIUi@UAUi;U<Ui6T6Ti>SESiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSySPkmRySPylQ<61X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2U.T_THROW_52944_s8_m5_w6_r13_pv_L0_f0edd6e) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_EH_52944_s8_m5_w6_r13_pv_L0_f0edd6e.

Module C_EH_52944_s8_m5_w6_r13_pv_L0_f133da2.

Definition ROOT : sstate := (t_st T_Ubs2U.T_THROW_52944_s8_m5_w6_r13_pv_L0_f133da2).
Definition CUTS : IMap.t template := imap_of [(200%uint63, T_Ubs2UE.T_XA_52944_2a6cb_blk_w7_r14_L0); (201%uint63, T_Ubs2UE.T_XA_52944_2a6cb_p682f0_w6_r13_pP)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2UE.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y`LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X0<3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZLMSLHRL<<0]LTU9Vgj4Wj3Wj2Wj1WiLV0WiDVDVi1V@ViNUOUiIUIUi@UAUi;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XLMSLHRL<<0]LTU9Vgj4Wj3Wj2Wj1WiLV0WiDVDVi1V@ViNUOUiIUIUi@UAUi;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XL=RL8QL<B0]LUU9Vgj4Wj3Wj2Wj1WiLV0WiDVDVi1V@ViNUOUiIUIUi@UAUi;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013Xk4QSySPU8VaiBV1Wi1V@ViNUOUiIUIUi@UAUi;U<Ui6T6Ti>SESiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSySPkmRySPylQ<61X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2U.T_THROW_52944_s8_m5_w6_r13_pv_L0_f133da2) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_EH_52944_s8_m5_w6_r13_pv_L0_f133da2.

Module C_EH_52944_s8_m5_w6_r13_pv_L0_f29322f.

Definition ROOT : sstate := (t_st T_Ubs2U.T_THROW_52944_s8_m5_w6_r13_pv_L0_f29322f).
Definition CUTS : IMap.t template := imap_of [(218%uint63, T_Ubs2UE.T_XA_52944_af6c4_blk_w7_r14_L0); (219%uint63, T_Ubs2UE.T_XA_52944_af6c4_p682f0_w6_r13_pP)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2UE.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y`LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X0<3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZLMSLHRL<<0]LTUKVgj4Wj3Wj2Wj1WiLV0WiDVDVi1V@ViNUOUiIUIUi@UAUi;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XLMSLHRL<<0]LTUKVgj4Wj3Wj2Wj1WiLV0WiDVDVi1V@ViNUOUiIUIUi@UAUi;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XL=RL8QL<B0]LUUKVgj4Wj3Wj2Wj1WiLV0WiDVDVi1V@ViNUOUiIUIUi@UAUi;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013Xk4QSySPUJVaiBV1Wi1V@ViNUOUiIUIUi@UAUi;U<Ui6T6Ti>SESiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSySPkmRySPylQ<61X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2U.T_THROW_52944_s8_m5_w6_r13_pv_L0_f29322f) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_EH_52944_s8_m5_w6_r13_pv_L0_f29322f.

Module C_EH_52944_s8_m5_w6_r13_pv_L0_f2b130e.

Definition ROOT : sstate := (t_st T_Ubs2U.T_THROW_52944_s8_m5_w6_r13_pv_L0_f2b130e).
Definition CUTS : IMap.t template := imap_of [(204%uint63, T_Ubs2UE.T_XA_52944_4a174_blk_w7_r14_L0); (205%uint63, T_Ubs2UE.T_XA_52944_4a174_p682f0_w6_r13_pP)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2UE.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y`LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X0<3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZLMSLHRP7WPL<<0]P?WPP@WPPAWPPBWPPCWPLTU=Vjj=Wj<Wj;Wj:Wj9Wj8Wj7Wj6Wj5Wj4Wi0V3WiMUNUi@UAUi;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XLMSLHRP7WPL<<0]P?WPP@WPPAWPPBWPPCWPLTU=Vjj=Wj<Wj;Wj:Wj9Wj8Wj7Wj6Wj5Wj4Wi0V3WiMUNUi@UAUi;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XL=RL8QP7WPL<B0]P?WPP@WPPAWPPBWPPCWPLUU=Vjj=Wj<Wj;Wj:Wj9Wj8Wj7Wj6Wj5Wj4Wi0V3WiMUNUi@UAUi;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013Xk4QSySPPDWPU<Vai5WCWj4Wi0V3WiMUNUi@UAUi;U<Ui6T6Ti>SESiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSySPkmRySPylQ<61X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2U.T_THROW_52944_s8_m5_w6_r13_pv_L0_f2b130e) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_EH_52944_s8_m5_w6_r13_pv_L0_f2b130e.

Module C_EH_52944_s8_m5_w6_r13_pv_L0_f37e2fb.

Definition ROOT : sstate := (t_st T_Ubs2U.T_THROW_52944_s8_m5_w6_r13_pv_L0_f37e2fb).
Definition CUTS : IMap.t template := imap_of [(228%uint63, T_Ubs2UE.T_XA_52944_c50a9_blk_w7_r14_L0); (229%uint63, T_Ubs2UE.T_XA_52944_c50a9_p682f0_w6_r13_pP)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2UE.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y`LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X0<3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZLMSLHRL<<0]LTU5Wgj3Wj2Wj1Wj0WiKVOViCVCVi1V?ViNUOUiIUIUi@UAUi;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XLMSLHRL<<0]LTU5Wgj3Wj2Wj1Wj0WiKVOViCVCVi1V?ViNUOUiIUIUi@UAUi;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XL=RL8QL<B0]LUU5Wgj3Wj2Wj1Wj0WiKVOViCVCVi1V?ViNUOUiIUIUi@UAUi;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013Xk4QSySPU4WaiAV0Wi1V?ViNUOUiIUIUi@UAUi;U<Ui6T6Ti>SESiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSySPkmRySPylQ<61X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2U.T_THROW_52944_s8_m5_w6_r13_pv_L0_f37e2fb) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_EH_52944_s8_m5_w6_r13_pv_L0_f37e2fb.

Module C_EH_52944_s8_m5_w6_r13_pv_L0_f47233d.

Definition ROOT : sstate := (t_st T_Ubs2U.T_THROW_52944_s8_m5_w6_r13_pv_L0_f47233d).
Definition CUTS : IMap.t template := imap_of [(208%uint63, T_Ubs2UE.T_XA_52944_63732_blk_w7_r14_L0); (209%uint63, T_Ubs2UE.T_XA_52944_63732_p682f0_w6_r13_pP)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2UE.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y`LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X0<3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZLMSLHRL<<0]LTUAVgj5Wj4Wj3Wj2WiMV1WiEVEVi1VAViNUOUiIUIUi@UAUi;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XLMSLHRL<<0]LTUAVgj5Wj4Wj3Wj2WiMV1WiEVEVi1VAViNUOUiIUIUi@UAUi;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XL=RL8QL<B0]LUUAVgj5Wj4Wj3Wj2WiMV1WiEVEVi1VAViNUOUiIUIUi@UAUi;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013Xk4QSySPU@VaiCV2Wi1VAViNUOUiIUIUi@UAUi;U<Ui6T6Ti>SESiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSySPkmRySPylQ<61X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2U.T_THROW_52944_s8_m5_w6_r13_pv_L0_f47233d) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_EH_52944_s8_m5_w6_r13_pv_L0_f47233d.

Module C_EH_52944_s8_m5_w6_r13_pv_L0_f5b0f5e.

Definition ROOT : sstate := (t_st T_Ubs2U.T_THROW_52944_s8_m5_w6_r13_pv_L0_f5b0f5e).
Definition CUTS : IMap.t template := imap_of [(202%uint63, T_Ubs2UE.T_XA_52944_45f12_blk_w7_r14_L0); (203%uint63, T_Ubs2UE.T_XA_52944_45f12_p682f0_w6_r13_pP)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2UE.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y`LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X0<3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZLMSLHRL<<0]LTU;Vgj1Wj0WjOVjNViIVMViAVAVi1V=ViNUOUiIUIUi@UAUi;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XLMSLHRL<<0]LTU;Vgj1Wj0WjOVjNViIVMViAVAVi1V=ViNUOUiIUIUi@UAUi;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XL=RL8QL<B0]LUU;Vgj1Wj0WjOVjNViIVMViAVAVi1V=ViNUOUiIUIUi@UAUi;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013Xk4QSySPU:Vai?VNVi1V=ViNUOUiIUIUi@UAUi;U<Ui6T6Ti>SESiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSySPkmRySPylQ<61X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2U.T_THROW_52944_s8_m5_w6_r13_pv_L0_f5b0f5e) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_EH_52944_s8_m5_w6_r13_pv_L0_f5b0f5e.

Module C_EH_52944_s8_m5_w6_r13_pv_L0_f6e7a6f.

Definition ROOT : sstate := (t_st T_Ubs2U.T_THROW_52944_s8_m5_w6_r13_pv_L0_f6e7a6f).
Definition CUTS : IMap.t template := imap_of [(230%uint63, T_Ubs2UE.T_XA_52944_cd178_blk_w7_r14_L0); (231%uint63, T_Ubs2UE.T_XA_52944_cd178_p682f0_w6_r13_pP)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2UE.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y`LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X0<3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZLMSLHRL<<0]LTU7Wgj4Wj3Wj2Wj1WiLV0WiDVDVi1V@ViNUOUiIUIUi@UAUi;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XLMSLHRL<<0]LTU7Wgj4Wj3Wj2Wj1WiLV0WiDVDVi1V@ViNUOUiIUIUi@UAUi;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XL=RL8QL<B0]LUU7Wgj4Wj3Wj2Wj1WiLV0WiDVDVi1V@ViNUOUiIUIUi@UAUi;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013Xk4QSySPU6WaiBV1Wi1V@ViNUOUiIUIUi@UAUi;U<Ui6T6Ti>SESiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSySPkmRySPylQ<61X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2U.T_THROW_52944_s8_m5_w6_r13_pv_L0_f6e7a6f) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_EH_52944_s8_m5_w6_r13_pv_L0_f6e7a6f.

Module C_EH_52944_s8_m5_w6_r13_pv_L0_f844317.

Definition ROOT : sstate := (t_st T_Ubs2U.T_THROW_52944_s8_m5_w6_r13_pv_L0_f844317).
Definition CUTS : IMap.t template := imap_of [(206%uint63, T_Ubs2UE.T_XA_52944_5942e_blk_w7_r14_L0); (207%uint63, T_Ubs2UE.T_XA_52944_5942e_p682f0_w6_r13_pP)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2UE.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y`LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X0<3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZLMSLHRL<<0]LTU?Vgj2Wj1Wj0WjOViJVNViBVBVi1V>ViNUOUiIUIUi@UAUi;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XLMSLHRL<<0]LTU?Vgj2Wj1Wj0WjOViJVNViBVBVi1V>ViNUOUiIUIUi@UAUi;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XL=RL8QL<B0]LUU?Vgj2Wj1Wj0WjOViJVNViBVBVi1V>ViNUOUiIUIUi@UAUi;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013Xk4QSySPU>Vai@VOVi1V>ViNUOUiIUIUi@UAUi;U<Ui6T6Ti>SESiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSySPkmRySPylQ<61X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2U.T_THROW_52944_s8_m5_w6_r13_pv_L0_f844317) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_EH_52944_s8_m5_w6_r13_pv_L0_f844317.

Module C_EH_52944_s8_m5_w6_r13_pv_L0_f8d1338.

Definition ROOT : sstate := (t_st T_Ubs2U.T_THROW_52944_s8_m5_w6_r13_pv_L0_f8d1338).
Definition CUTS : IMap.t template := imap_of [(220%uint63, T_Ubs2UE.T_XA_52944_bb428_blk_w7_r14_L0); (221%uint63, T_Ubs2UE.T_XA_52944_bb428_p682f0_w6_r13_pP)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2UE.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y`LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X0<3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZLMSLHRL<<0]LTUMVgj3Wj2Wj1Wj0WiKVOViCVCVi1V?ViNUOUiIUIUi@UAUi;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XLMSLHRL<<0]LTUMVgj3Wj2Wj1Wj0WiKVOViCVCVi1V?ViNUOUiIUIUi@UAUi;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013XL=RL8QL<B0]LUUMVgj3Wj2Wj1Wj0WiKVOViCVCVi1V?ViNUOUiIUIUi@UAUi;U<Ui6T6TiDSESi>SBSiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSkFSQySPylQ013Xk4QSySPULVaiAV0Wi1V?ViNUOUiIUIUi@UAUi;U<Ui6T6Ti>SESiOR<SiJRMRiARHRi;R<Ri0R1Ri\\iZZiUXiPSySPkmRySPylQ<61X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2U.T_THROW_52944_s8_m5_w6_r13_pv_L0_f8d1338) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_EH_52944_s8_m5_w6_r13_pv_L0_f8d1338.
