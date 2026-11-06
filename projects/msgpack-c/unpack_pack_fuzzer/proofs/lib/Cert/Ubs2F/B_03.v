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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2F Require Import T_Ubs2F.
Module C_MF_1f6a4_n_c1000000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_1.
Definition Fc0 : fact := (FAlign 92%uint63 4%uint63).
Definition Fc1 : fact := (FRange 92%uint63 (wp 4096%uint63) (wp 140737488355327%uint63)).
Definition FSc0 : list fact := (F147 :: Fc0 :: Fc1 :: FS172).
Definition FSc1 : list fact := (F146 :: FSc0).

Definition ROOT : sstate := (t_st T_Ubs2F.R_MF_1f6a4_n_c1000000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_1).
Definition CUTS : IMap.t template := imap_of [(210%uint63, T_Ubs2F.T_LIB_r10o5n0o7n1o1n12o3n2_s3_w0_e0b0)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2F.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Yb0NLS40MS80MS<0MSD0MSD3MS4EMS01NSDM3YL>4Y4<5Y4F5Y4@@Y<2AY0BAY<G4Z<A6Z8<7ZLQB1TQLIQA2LAQA6LPB0TQA8ZRPLVA0ZLPB0[XRPA1MJOOOOOOOOOOOWA0ZPLRPPNRPPORPP0SPP2SPP3SPP4SPP5SPP6SPP7SPP8SPP9SPP:SPP;SPP9RPP<SPP4RPL0000`P;RPUBVhjCRjBRjARj@Rj?Rj>Rj=Rj<Rj;Rj:Rj9Rj8Rj7Rj6Rj5Rj4Rj3Rj2Rj1Ri0R0Ri\\iZZiUXiPSySPk_QRQRRA0LPB0[XvqRRLPB0]XeqRQLPB0^XeqySP"%pstring.
Definition OBLS : list obligation := [

  (FSc0,
   F146);

  (FSc1,
   F145) ].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2F.R_MF_1f6a4_n_c1000000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_1) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_MF_1f6a4_n_c1000000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_1.

Module C_MF_1f6a4_n_c1000000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_0.

Definition ROOT : sstate := (t_st T_Ubs2F.R_MF_1f6a4_n_c1000000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_0).
Definition CUTS : IMap.t template := imap_of [(203%uint63, T_Ubs2F.T_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0); (204%uint63, T_Ubs2F.T_EXIT_2_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2F.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Yb0NLS40MS80MS<0MSD0MSD3MS4EMS01NSDM3YL>4Y4<5Y4F5Y4@@Y<2AY0BAY<G4Z<A6Z8<7ZPMRPPNRPPORPP0SPP1SPP2SPP3SPP4SPP5SPP6SPP7SPP8SPP9SPP:SPP9RPP;SPP;RPP4RPU;VfjARj@Rj?Rj>Rj=Rj<Rj;Rj:Rj9Rj8Rj7Rj6Rj5Rj4Rj3Rj2Rj1Rj0Ri\\iZZiUXiPSySPk[QySPPMRPPNRPPORPP0SPP1SPP2SPP3SPP4SPP5SPP6SPP7SPP8SPP9SPP:SPP9RPP;SPP;RPP4RPU<VfjARj@Rj?Rj>Rj=Rj<Rj;Rj:Rj9Rj8Rj7Rj6Rj5Rj4Rj3Rj2Rj1Rj0Ri\\iZZiUXiPSySPk[QySPcySP"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2F.R_MF_1f6a4_n_c1000000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_0) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_MF_1f6a4_n_c1000000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_0.

Module C_MF_1f6a4_n_c1000000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_1.
Definition Fc0 : fact := (FAlign 92%uint63 4%uint63).
Definition Fc1 : fact := (FRange 92%uint63 (wp 4096%uint63) (wp 140737488355327%uint63)).
Definition FSc0 : list fact := (F147 :: Fc0 :: Fc1 :: FS173).
Definition FSc1 : list fact := (F146 :: FSc0).

Definition ROOT : sstate := (t_st T_Ubs2F.R_MF_1f6a4_n_c1000000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_1).
Definition CUTS : IMap.t template := imap_of [(211%uint63, T_Ubs2F.T_LIB_r10o5n0o7n1o1n12o3n2_s4_w0_e0b0)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2F.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Yb0NLS40MS80MS<0MSD0MSD3MS4EMS01NSDM3YL>4Y4<5Y4F5Y4@@Y<2AY0BAY<G4Z<A6Z8<7ZLQB1TQLIQA2LAQA6LPB0TQA8ZRPLVA0ZLPB0[XRPA1MJOOOOOOOOOOOWA0ZPLRPPNRPPORPP0SPP2SPP3SPP4SPP5SPP6SPP7SPP8SPP9SPP:SPP;SPP9RPP<SPP4RPL0000`P;RPUCVhjCRjBRjARj@Rj?Rj>Rj=Rj<Rj;Rj:Rj9Rj8Rj7Rj6Rj5Rj4Rj3Rj2Rj1Ri0R0Ri\\iZZiUXiPSySPk_QRQRRA0LPB0[XvqRRLPB0]XeqRQLPB0^XeqySP"%pstring.
Definition OBLS : list obligation := [

  (FSc0,
   F146);

  (FSc1,
   F145) ].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2F.R_MF_1f6a4_n_c1000000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_1) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_MF_1f6a4_n_c1000000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_1.

Module C_MF_1f418_2000000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0.

Definition ROOT : sstate := (t_st T_Ubs2F.R_MF_1f418_2000000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0).
Definition CUTS : IMap.t template := imap_of [(342%uint63, T_Ubs2F.T_SW_MF_1f418_2000000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0_1)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2F.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "UFZYiHR0SiDRDRiBRBRi?R?Ri0R0Ri\\iZZiUXiPSylb0NLS40MS80MS<0MSD0MSD3MS4EMS01NSDM3YL>4Y4<5Y4F5Y4@@Y<2AY0BAY<G4Z<A6Z8<7Z"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2F.R_MF_1f418_2000000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_MF_1f418_2000000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0.

Module C_MF_1f418_2000000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_1.

Definition ROOT : sstate := (t_st T_Ubs2F.R_MF_1f418_2000000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_1).
Definition CUTS : IMap.t template := imap_of [(340%uint63, T_Ubs2F.T_POSTREAD_2000000_BGBlob); (341%uint63, T_Ubs2F.T_RLOOP_2000000_BGBlob_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2F.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Yb0NLS40MS80MS<0MSD0MSD3MS4EMS01NSDM3YL>4Y4<5Y4F5Y4@@Y<2AY0BAY<G4Z<A6Z8<7ZLPB0[XL0000`A1ZP1SPP3TPP4TPP5TPP6TPP1S0000`P7TPP8TPP9TPP:TPP;TPP<TPP=TPL0002`P>TPP?TPP@TPPATPP?RPPBTPUEZhjCRjBRjARj@Rj?Rj>Rj=Rj<Rj;Rj:Rj9Rj8Rj7Rj6Rj5Rj4Rj3Rj2Rj1Rj0Ri\\iZZiUXiPSylQ80MSySPk^QySPP1SPP4TPP5TPP6TPLPL000RP>TPP?TPP@TPPATPP?RPPBTPLPB0[XUDZaj<Rj;Rj:Rj9Rj8Rj7Rj6Rj5Rj4Rj3Rj2Rj1Rj0Ri\\iZZiUXiPSkYQySPkeQySPylQ@0MSyla0NLS40MS<0MSD0MSD3MS4EMS01NSDM3YL>4Y4<5Y4F5Y4@@Y<2AY0BAY<G4Z<A6Z8<7ZylQ80MSySPk^QySPP1SPPCSPPDSPPESPRPL000RPMSPPNSPPOSPP0TPP?RPP1TPL0000`UDZaj<Rj;Rj:Rj9Rj8Rj7Rj6Rj5Rj4Rj3Rj2Rj1Rj0Ri\\iZZiUXiPSkYQLPB0[Xh1SLPB0[XgCcySPRPL000RuqkeRySPk[QySPk]QySP"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2F.R_MF_1f418_2000000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_1) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_MF_1f418_2000000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_1.

Module C_POSTREAD_2000000_BGBlob.

Definition ROOT : sstate := (t_st T_Ubs2F.T_POSTREAD_2000000_BGBlob).
Definition CUTS : IMap.t template := imap_of [(343%uint63, T_Ubs2F.T_MF_1f6a4_n_c2000000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0); (344%uint63, T_Ubs2F.T_MF_1f6a4_n_c2000000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z); (345%uint63, T_Ubs2F.T_MF_1f6a4_n_c2000000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0); (346%uint63, T_Ubs2F.T_MF_1f6a4_n_c2000000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0); (347%uint63, T_Ubs2F.T_MF_1f6a4_n_c2000000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2F.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Yb0NLS40MS80MS<0MSD0MSD3MS4EMS01NSDM3YL>4Y4<5Y4F5Y4@@Y<2AY0BAY<G4Z<A6Z8<7ZLPB0[XLQB1TQLIQA2LAQA6LPB0TQA8A1MJOOOOOOOOOOOWA0ZP6RPP7RPP8RPP9RPP:RPP;RPP<RPUHZ\j;Rj:Rj9Rj8Rj7Rj6Rj5Ri0R4Ri\\iZZiUXiPSLPRPuqRPL00000RuqySPP6RPP7RPP8RPP9RPP:RPP;RPP<RPUGZ\j;Rj:Rj9Rj8Rj7Rj6Rj5Ri0R4Ri\\iZZiUXiPSLPRPuqRPL00000RuqySPylQ8EMSP6RPP7RPP8RPP9RPP:RPP;RPP<RPUIZ\j;Rj:Rj9Rj8Rj7Rj6Rj5Ri0R4Ri\\iZZiUXiPSLPRPuqRPL00000RuqySPylQ8EMSP6RPP7RPP8RPP9RPP:RPP;RPP<RPUJZ\j;Rj:Rj9Rj8Rj7Rj6Rj5Ri0R4Ri\\iZZiUXiPSLPRPuqRPL00000RuqySPylQ8EMSP6RPP7RPP8RPP9RPP:RPP;RPP<RPUKZ\j;Rj:Rj9Rj8Rj7Rj6Rj5Ri0R4Ri\\iZZiUXiPSLPRPuqRPL00000RuqySPylQ8EMSs:TTySPcySPkgQySPylQH3MS"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2F.T_POSTREAD_2000000_BGBlob) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_POSTREAD_2000000_BGBlob.

Module C_RLOOP_2000000_BGBlob_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0.

Definition ROOT : sstate := (t_st T_Ubs2F.T_RLOOP_2000000_BGBlob_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0).
Definition CUTS : IMap.t template := imap_of [(340%uint63, T_Ubs2F.T_POSTREAD_2000000_BGBlob); (341%uint63, T_Ubs2F.T_RLOOP_2000000_BGBlob_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0); (348%uint63, T_Ubs2F.T_MF_1f418_4000000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (t_measure T_Ubs2F.T_RLOOP_2000000_BGBlob_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2F.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Yb0NLS40MS80MS<0MSD0MSD3MS4EMS01NSDM3YL>4Y4<5Y4F5Y4@@Y<2AY0BAY<G4Z<A6Z8<7ZYa0NLS40MS<0MSD0MSD3MS4EMS01NSDM3YL>4Y4<5Y4F5Y4@@Y<2AY0BAY<G4Z<A6Z8<7ZLPB0[XP=RPA1ZP2RPP3RPP4RPP6RPP7RPP8RPP9RPP:RPP;RPP<RPP>RPP?RPP@RPPARPPBRPPCRPULZej@Rj?Rj>Rj=Rj<Rj;Rj:Rj9Rj8Rj7Rj6Rj5Rj4Rj3Rj2Rj1Ri0R0Ri\\iZZiUXiPSySPylQH0MSL00000Qb=RPDRPPERPPFRPPGRPP0RPP=RPA0PHRPPIRPPJRPPKRPPLRPPMRPPNRPP=R000RPORPP0SPP1SPP2SPP3SPVEZhjCRiBRBRjARj@Rj?Rj>Rj=Rj<Rj;Rj:Rj9Rj8Rj7Rj6Rj5Rj4Rj3Rj2Rj1Ri0R0Ri\\iZZiUXiPSylQ80MSySPk^QySPPERPPFRPPGRPLPL00000QLPB0[XA1PORPP0SPP1SPP2SPPBRPP3SPLPB0[XUDZaj<Rj;Rj:Rj9Rj8Rj7Rj6Rj5Rj4Rj3Rj2Rj1Ri0R0Ri\\iZZiUXiPSkYQySPkeQySPPERPPFRPPGRPLPL000RPORPP0SPP1SPP2SPPBRPP3SPLPB0[XUDZaj<Rj;Rj:Rj9Rj8Rj7Rj6Rj5Rj4Rj3Rj2Rj1Ri0R0Ri\\iZZiUXiPSkYQySPkeQySPcySPylQ@0MSySQylQ80MSySPk^QySPP2RPP3RPP4RPRPL000RP>RPP?RPP@RPPARPPBRPPCRPP=RPUDZaj<Rj;Rj:Rj9Rj8Rj7Rj6Rj5Rj4Rj3Rj2Rj1Ri0R0Ri\\iZZiUXiPSkYQLPB0[Xh0RLPB0[XgCcySPRPL000RuqkeRySPylQ@0MSP=RPL000NovqcySQ"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2F.T_RLOOP_2000000_BGBlob_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_RLOOP_2000000_BGBlob_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0.

Module C_MF_1f6a4_n_c2000000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_0.

Definition ROOT : sstate := (t_st T_Ubs2F.R_MF_1f6a4_n_c2000000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_0).
Definition CUTS : IMap.t template := imap_of [(203%uint63, T_Ubs2F.T_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0); (204%uint63, T_Ubs2F.T_EXIT_2_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2F.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Yb0NLS40MS80MS<0MSD0MSD3MS4EMS01NSDM3YL>4Y4<5Y4F5Y4@@Y<2AY0BAY<G4Z<A6Z8<7ZPMRPPNRPPORPP0SPP1SPP2SPP3SPP4SPP5SPP6SPP7SPP8SPP9SPP:SPP9RPP;SPP;RPP4RPU;VfjARj@Rj?Rj>Rj=Rj<Rj;Rj:Rj9Rj8Rj7Rj6Rj5Rj4Rj3Rj2Rj1Rj0Ri\\iZZiUXiPSySPk[QySPPMRPPNRPPORPP0SPP1SPP2SPP3SPP4SPP5SPP6SPP7SPP8SPP9SPP:SPP9RPP;SPP;RPP4RPU<VfjARj@Rj?Rj>Rj=Rj<Rj;Rj:Rj9Rj8Rj7Rj6Rj5Rj4Rj3Rj2Rj1Rj0Ri\\iZZiUXiPSySPk[QySPcySP"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2F.R_MF_1f6a4_n_c2000000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_0) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_MF_1f6a4_n_c2000000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_0.

Module C_MF_1f6a4_n_c2000000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_1.
Definition Fc0 : fact := (FAlign 92%uint63 4%uint63).
Definition Fc1 : fact := (FRange 92%uint63 (wp 4096%uint63) (wp 140737488355327%uint63)).
Definition FSc0 : list fact := (F147 :: Fc0 :: Fc1 :: FS177).
Definition FSc1 : list fact := (F146 :: FSc0).

Definition ROOT : sstate := (t_st T_Ubs2F.R_MF_1f6a4_n_c2000000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_1).
Definition CUTS : IMap.t template := imap_of [(207%uint63, T_Ubs2F.T_LIB_r10o5n0o7n1o1n12o3n2_s1_w0_e0b0)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2F.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Yb0NLS40MS80MS<0MSD0MSD3MS4EMS01NSDM3YL>4Y4<5Y4F5Y4@@Y<2AY0BAY<G4Z<A6Z8<7ZLQB1TQLIQA2LAQA6LPB0TQA8ZRPLVA0ZLPB0[XRPA1MJOOOOOOOOOOOWA0ZPLRPPNRPPORPP0SPP2SPP3SPP4SPP5SPP6SPP7SPP8SPP9SPP:SPP;SPP9RPP<SPP4RPL00000QP;RPU?VhjCRjBRjARj@Rj?Rj>Rj=Rj<Rj;Rj:Rj9Rj8Rj7Rj6Rj5Rj4Rj3Rj2Rj1Ri0R0Ri\\iZZiUXiPSySPk_QRQRRA0LPB0[XvqRRLPB0]XeqRQLPB0^XeqySP"%pstring.
Definition OBLS : list obligation := [

  (FSc0,
   F146);

  (FSc1,
   F145) ].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2F.R_MF_1f6a4_n_c2000000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_1) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_MF_1f6a4_n_c2000000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_1.

Module C_MF_1f6a4_n_c2000000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_0.

Definition ROOT : sstate := (t_st T_Ubs2F.R_MF_1f6a4_n_c2000000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_0).
Definition CUTS : IMap.t template := imap_of [(203%uint63, T_Ubs2F.T_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0); (204%uint63, T_Ubs2F.T_EXIT_2_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2F.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Yb0NLS40MS80MS<0MSD0MSD3MS4EMS01NSDM3YL>4Y4<5Y4F5Y4@@Y<2AY0BAY<G4Z<A6Z8<7ZPMRPPNRPPORPP0SPP1SPP2SPP3SPP4SPP5SPP6SPP7SPP8SPP9SPP:SPP9RPP;SPP;RPP4RPU;VfjARj@Rj?Rj>Rj=Rj<Rj;Rj:Rj9Rj8Rj7Rj6Rj5Rj4Rj3Rj2Rj1Rj0Ri\\iZZiUXiPSySPk[QySPPMRPPNRPPORPP0SPP1SPP2SPP3SPP4SPP5SPP6SPP7SPP8SPP9SPP:SPP9RPP;SPP;RPP4RPU<VfjARj@Rj?Rj>Rj=Rj<Rj;Rj:Rj9Rj8Rj7Rj6Rj5Rj4Rj3Rj2Rj1Rj0Ri\\iZZiUXiPSySPk[QySPcySP"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2F.R_MF_1f6a4_n_c2000000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_0) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_MF_1f6a4_n_c2000000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_0.

Module C_MF_1f6a4_n_c2000000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_1.
Definition Fc0 : fact := (FAlign 92%uint63 4%uint63).
Definition Fc1 : fact := (FRange 92%uint63 (wp 4096%uint63) (wp 140737488355327%uint63)).
Definition FSc0 : list fact := (F147 :: Fc0 :: Fc1 :: FS178).
Definition FSc1 : list fact := (F146 :: FSc0).

Definition ROOT : sstate := (t_st T_Ubs2F.R_MF_1f6a4_n_c2000000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_1).
Definition CUTS : IMap.t template := imap_of [(208%uint63, T_Ubs2F.T_LIB_r10o5n0o7n1o1n12o3n2_s1_w0_e0b0z)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2F.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Yb0NLS40MS80MS<0MSD0MSD3MS4EMS01NSDM3YL>4Y4<5Y4F5Y4@@Y<2AY0BAY<G4Z<A6Z8<7ZLQB1TQLIQA2LAQA6LPB0TQA8ZRPLVA0ZLPB0[XRPA1MJOOOOOOOOOOOWA0ZPLRPPNRPPORPP0SPP2SPP3SPP4SPP5SPP6SPP7SPP8SPP9SPP:SPP;SPP9RPP<SPP4RPL00000QP;RPU@VhjCRjBRjARj@Rj?Rj>Rj=Rj<Rj;Rj:Rj9Rj8Rj7Rj6Rj5Rj4Rj3Rj2Rj1Ri0R0Ri\\iZZiUXiPSySPk_QRQRRA0LPB0[XvqRRLPB0]XeqRQLPB0^XeqySP"%pstring.
Definition OBLS : list obligation := [

  (FSc0,
   F146);

  (FSc1,
   F145) ].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2F.R_MF_1f6a4_n_c2000000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_1) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_MF_1f6a4_n_c2000000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_1.

Module C_MF_1f6a4_n_c2000000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_0.

Definition ROOT : sstate := (t_st T_Ubs2F.R_MF_1f6a4_n_c2000000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_0).
Definition CUTS : IMap.t template := imap_of [(203%uint63, T_Ubs2F.T_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0); (204%uint63, T_Ubs2F.T_EXIT_2_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2F.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Yb0NLS40MS80MS<0MSD0MSD3MS4EMS01NSDM3YL>4Y4<5Y4F5Y4@@Y<2AY0BAY<G4Z<A6Z8<7ZPMRPPNRPPORPP0SPP1SPP2SPP3SPP4SPP5SPP6SPP7SPP8SPP9SPP:SPP9RPP;SPP;RPP4RPU;VfjARj@Rj?Rj>Rj=Rj<Rj;Rj:Rj9Rj8Rj7Rj6Rj5Rj4Rj3Rj2Rj1Rj0Ri\\iZZiUXiPSySPk[QySPPMRPPNRPPORPP0SPP1SPP2SPP3SPP4SPP5SPP6SPP7SPP8SPP9SPP:SPP9RPP;SPP;RPP4RPU<VfjARj@Rj?Rj>Rj=Rj<Rj;Rj:Rj9Rj8Rj7Rj6Rj5Rj4Rj3Rj2Rj1Rj0Ri\\iZZiUXiPSySPk[QySPcySP"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2F.R_MF_1f6a4_n_c2000000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_0) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_MF_1f6a4_n_c2000000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_0.

Module C_MF_1f6a4_n_c2000000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_1.
Definition Fc0 : fact := (FAlign 92%uint63 4%uint63).
Definition Fc1 : fact := (FRange 92%uint63 (wp 4096%uint63) (wp 140737488355327%uint63)).
Definition FSc0 : list fact := (F147 :: Fc0 :: Fc1 :: FS179).
Definition FSc1 : list fact := (F146 :: FSc0).

Definition ROOT : sstate := (t_st T_Ubs2F.R_MF_1f6a4_n_c2000000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_1).
Definition CUTS : IMap.t template := imap_of [(209%uint63, T_Ubs2F.T_LIB_r10o5n0o7n1o1n12o3n2_s2_w0_e0b0)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2F.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Yb0NLS40MS80MS<0MSD0MSD3MS4EMS01NSDM3YL>4Y4<5Y4F5Y4@@Y<2AY0BAY<G4Z<A6Z8<7ZLQB1TQLIQA2LAQA6LPB0TQA8ZRPLVA0ZLPB0[XRPA1MJOOOOOOOOOOOWA0ZPLRPPNRPPORPP0SPP2SPP3SPP4SPP5SPP6SPP7SPP8SPP9SPP:SPP;SPP9RPP<SPP4RPL00000QP;RPUAVhjCRjBRjARj@Rj?Rj>Rj=Rj<Rj;Rj:Rj9Rj8Rj7Rj6Rj5Rj4Rj3Rj2Rj1Ri0R0Ri\\iZZiUXiPSySPk_QRQRRA0LPB0[XvqRRLPB0]XeqRQLPB0^XeqySP"%pstring.
Definition OBLS : list obligation := [

  (FSc0,
   F146);

  (FSc1,
   F145) ].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2F.R_MF_1f6a4_n_c2000000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_1) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_MF_1f6a4_n_c2000000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_1.

Module C_MF_1f6a4_n_c2000000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_0.

Definition ROOT : sstate := (t_st T_Ubs2F.R_MF_1f6a4_n_c2000000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_0).
Definition CUTS : IMap.t template := imap_of [(203%uint63, T_Ubs2F.T_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0); (204%uint63, T_Ubs2F.T_EXIT_2_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2F.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Yb0NLS40MS80MS<0MSD0MSD3MS4EMS01NSDM3YL>4Y4<5Y4F5Y4@@Y<2AY0BAY<G4Z<A6Z8<7ZPMRPPNRPPORPP0SPP1SPP2SPP3SPP4SPP5SPP6SPP7SPP8SPP9SPP:SPP9RPP;SPP;RPP4RPU;VfjARj@Rj?Rj>Rj=Rj<Rj;Rj:Rj9Rj8Rj7Rj6Rj5Rj4Rj3Rj2Rj1Rj0Ri\\iZZiUXiPSySPk[QySPPMRPPNRPPORPP0SPP1SPP2SPP3SPP4SPP5SPP6SPP7SPP8SPP9SPP:SPP9RPP;SPP;RPP4RPU<VfjARj@Rj?Rj>Rj=Rj<Rj;Rj:Rj9Rj8Rj7Rj6Rj5Rj4Rj3Rj2Rj1Rj0Ri\\iZZiUXiPSySPk[QySPcySP"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2F.R_MF_1f6a4_n_c2000000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_0) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_MF_1f6a4_n_c2000000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_0.

Module C_MF_1f6a4_n_c2000000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_1.
Definition Fc0 : fact := (FAlign 92%uint63 4%uint63).
Definition Fc1 : fact := (FRange 92%uint63 (wp 4096%uint63) (wp 140737488355327%uint63)).
Definition FSc0 : list fact := (F147 :: Fc0 :: Fc1 :: FS180).
Definition FSc1 : list fact := (F146 :: FSc0).

Definition ROOT : sstate := (t_st T_Ubs2F.R_MF_1f6a4_n_c2000000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_1).
Definition CUTS : IMap.t template := imap_of [(210%uint63, T_Ubs2F.T_LIB_r10o5n0o7n1o1n12o3n2_s3_w0_e0b0)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2F.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Yb0NLS40MS80MS<0MSD0MSD3MS4EMS01NSDM3YL>4Y4<5Y4F5Y4@@Y<2AY0BAY<G4Z<A6Z8<7ZLQB1TQLIQA2LAQA6LPB0TQA8ZRPLVA0ZLPB0[XRPA1MJOOOOOOOOOOOWA0ZPLRPPNRPPORPP0SPP2SPP3SPP4SPP5SPP6SPP7SPP8SPP9SPP:SPP;SPP9RPP<SPP4RPL00000QP;RPUBVhjCRjBRjARj@Rj?Rj>Rj=Rj<Rj;Rj:Rj9Rj8Rj7Rj6Rj5Rj4Rj3Rj2Rj1Ri0R0Ri\\iZZiUXiPSySPk_QRQRRA0LPB0[XvqRRLPB0]XeqRQLPB0^XeqySP"%pstring.
Definition OBLS : list obligation := [

  (FSc0,
   F146);

  (FSc1,
   F145) ].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2F.R_MF_1f6a4_n_c2000000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_1) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_MF_1f6a4_n_c2000000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_1.

Module C_MF_1f6a4_n_c2000000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_0.

Definition ROOT : sstate := (t_st T_Ubs2F.R_MF_1f6a4_n_c2000000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_0).
Definition CUTS : IMap.t template := imap_of [(203%uint63, T_Ubs2F.T_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0); (204%uint63, T_Ubs2F.T_EXIT_2_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2F.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Yb0NLS40MS80MS<0MSD0MSD3MS4EMS01NSDM3YL>4Y4<5Y4F5Y4@@Y<2AY0BAY<G4Z<A6Z8<7ZPMRPPNRPPORPP0SPP1SPP2SPP3SPP4SPP5SPP6SPP7SPP8SPP9SPP:SPP9RPP;SPP;RPP4RPU;VfjARj@Rj?Rj>Rj=Rj<Rj;Rj:Rj9Rj8Rj7Rj6Rj5Rj4Rj3Rj2Rj1Rj0Ri\\iZZiUXiPSySPk[QySPPMRPPNRPPORPP0SPP1SPP2SPP3SPP4SPP5SPP6SPP7SPP8SPP9SPP:SPP9RPP;SPP;RPP4RPU<VfjARj@Rj?Rj>Rj=Rj<Rj;Rj:Rj9Rj8Rj7Rj6Rj5Rj4Rj3Rj2Rj1Rj0Ri\\iZZiUXiPSySPk[QySPcySP"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2F.R_MF_1f6a4_n_c2000000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_0) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_MF_1f6a4_n_c2000000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_0.

Module C_MF_1f6a4_n_c2000000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_1.
Definition Fc0 : fact := (FAlign 92%uint63 4%uint63).
Definition Fc1 : fact := (FRange 92%uint63 (wp 4096%uint63) (wp 140737488355327%uint63)).
Definition FSc0 : list fact := (F147 :: Fc0 :: Fc1 :: FS181).
Definition FSc1 : list fact := (F146 :: FSc0).

Definition ROOT : sstate := (t_st T_Ubs2F.R_MF_1f6a4_n_c2000000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_1).
Definition CUTS : IMap.t template := imap_of [(211%uint63, T_Ubs2F.T_LIB_r10o5n0o7n1o1n12o3n2_s4_w0_e0b0)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2F.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Yb0NLS40MS80MS<0MSD0MSD3MS4EMS01NSDM3YL>4Y4<5Y4F5Y4@@Y<2AY0BAY<G4Z<A6Z8<7ZLQB1TQLIQA2LAQA6LPB0TQA8ZRPLVA0ZLPB0[XRPA1MJOOOOOOOOOOOWA0ZPLRPPNRPPORPP0SPP2SPP3SPP4SPP5SPP6SPP7SPP8SPP9SPP:SPP;SPP9RPP<SPP4RPL00000QP;RPUCVhjCRjBRjARj@Rj?Rj>Rj=Rj<Rj;Rj:Rj9Rj8Rj7Rj6Rj5Rj4Rj3Rj2Rj1Ri0R0Ri\\iZZiUXiPSySPk_QRQRRA0LPB0[XvqRRLPB0]XeqRQLPB0^XeqySP"%pstring.
Definition OBLS : list obligation := [

  (FSc0,
   F146);

  (FSc1,
   F145) ].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2F.R_MF_1f6a4_n_c2000000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_1) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_MF_1f6a4_n_c2000000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_1.

Module C_MF_1f418_4000000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0.

Definition ROOT : sstate := (t_st T_Ubs2F.R_MF_1f418_4000000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0).
Definition CUTS : IMap.t template := imap_of [(351%uint63, T_Ubs2F.T_SW_MF_1f418_4000000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0_1)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2F.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "UOZYiHR0SiDRDRiBRBRi?R?Ri0R0Ri\\iZZiUXiPSylb0NLS40MS80MS<0MSD0MSD3MS4EMS01NSDM3YL>4Y4<5Y4F5Y4@@Y<2AY0BAY<G4Z<A6Z8<7Z"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2F.R_MF_1f418_4000000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_MF_1f418_4000000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0.

Module C_MF_1f418_4000000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_1.

Definition ROOT : sstate := (t_st T_Ubs2F.R_MF_1f418_4000000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_1).
Definition CUTS : IMap.t template := imap_of [(349%uint63, T_Ubs2F.T_POSTREAD_4000000_BGBlob); (350%uint63, T_Ubs2F.T_RLOOP_4000000_BGBlob_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2F.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Yb0NLS40MS80MS<0MSD0MSD3MS4EMS01NSDM3YL>4Y4<5Y4F5Y4@@Y<2AY0BAY<G4Z<A6Z8<7ZLPB0[XL00000QA1ZP1SPP3TPP4TPP5TPP6TPP1S00000QP7TPP8TPP9TPP:TPP;TPP<TPP=TPL00020QP>TPP?TPP@TPPATPP?RPPBTPUNZhjCRjBRjARj@Rj?Rj>Rj=Rj<Rj;Rj:Rj9Rj8Rj7Rj6Rj5Rj4Rj3Rj2Rj1Rj0Ri\\iZZiUXiPSylQ80MSySPk^QySPP1SPP4TPP5TPP6TPLPL000RP>TPP?TPP@TPPATPP?RPPBTPLPB0[XUMZaj<Rj;Rj:Rj9Rj8Rj7Rj6Rj5Rj4Rj3Rj2Rj1Rj0Ri\\iZZiUXiPSySPkeQySPylQ@0MSyla0NLS40MS<0MSD0MSD3MS4EMS01NSDM3YL>4Y4<5Y4F5Y4@@Y<2AY0BAY<G4Z<A6Z8<7ZylQ80MSySPk^QySPP1SPPCSPPDSPPESPRPL000RPMSPPNSPPOSPP0TPP?RPP1TPL00000QUMZaj<Rj;Rj:Rj9Rj8Rj7Rj6Rj5Rj4Rj3Rj2Rj1Rj0Ri\\iZZiUXiPSLPB0[Xh1SLPB0[XgCcySPRPL000RuqkeRySPk[QySPk]QySP"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2F.R_MF_1f418_4000000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_1) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_MF_1f418_4000000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_1.

Module C_POSTREAD_4000000_BGBlob.

Definition ROOT : sstate := (t_st T_Ubs2F.T_POSTREAD_4000000_BGBlob).
Definition CUTS : IMap.t template := imap_of [(352%uint63, T_Ubs2F.T_MF_1f6a4_n_c4000000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0); (353%uint63, T_Ubs2F.T_MF_1f6a4_n_c4000000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z); (354%uint63, T_Ubs2F.T_MF_1f6a4_n_c4000000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0); (355%uint63, T_Ubs2F.T_MF_1f6a4_n_c4000000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0); (356%uint63, T_Ubs2F.T_MF_1f6a4_n_c4000000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2F.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Yb0NLS40MS80MS<0MSD0MSD3MS4EMS01NSDM3YL>4Y4<5Y4F5Y4@@Y<2AY0BAY<G4Z<A6Z8<7ZLPB0[XLQB1TQLIQA2LAQA6LPB0TQA8A1MJOOOOOOOOOOOWA0ZP6RPP7RPP8RPP9RPP:RPP;RPP<RPU1[\j;Rj:Rj9Rj8Rj7Rj6Rj5Ri0R4Ri\\iZZiUXiPSLPRPuqRPL00000RuqySPP6RPP7RPP8RPP9RPP:RPP;RPP<RPU0[\j;Rj:Rj9Rj8Rj7Rj6Rj5Ri0R4Ri\\iZZiUXiPSLPRPuqRPL00000RuqySPylQ8EMSP6RPP7RPP8RPP9RPP:RPP;RPP<RPU2[\j;Rj:Rj9Rj8Rj7Rj6Rj5Ri0R4Ri\\iZZiUXiPSLPRPuqRPL00000RuqySPylQ8EMSP6RPP7RPP8RPP9RPP:RPP;RPP<RPU3[\j;Rj:Rj9Rj8Rj7Rj6Rj5Ri0R4Ri\\iZZiUXiPSLPRPuqRPL00000RuqySPylQ8EMSP6RPP7RPP8RPP9RPP:RPP;RPP<RPU4[\j;Rj:Rj9Rj8Rj7Rj6Rj5Ri0R4Ri\\iZZiUXiPSLPRPuqRPL00000RuqySPylQ8EMSs:TTySPcySPkgQySPylQH3MS"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2F.T_POSTREAD_4000000_BGBlob) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_POSTREAD_4000000_BGBlob.

Module C_RLOOP_4000000_BGBlob_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0.

Definition ROOT : sstate := (t_st T_Ubs2F.T_RLOOP_4000000_BGBlob_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0).
Definition CUTS : IMap.t template := imap_of [(349%uint63, T_Ubs2F.T_POSTREAD_4000000_BGBlob); (350%uint63, T_Ubs2F.T_RLOOP_4000000_BGBlob_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0); (357%uint63, T_Ubs2F.T_SW_RLOOP_4000000_BGBlob_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_1)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (t_measure T_Ubs2F.T_RLOOP_4000000_BGBlob_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2F.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Yb0NLS40MS80MS<0MSD0MSD3MS4EMS01NSDM3YL>4Y4<5Y4F5Y4@@Y<2AY0BAY<G4Z<A6Z8<7ZYa0NLS40MS<0MSD0MSD3MS4EMS01NSDM3YL>4Y4<5Y4F5Y4@@Y<2AY0BAY<G4Z<A6Z8<7ZLPB0[XP=RPA1ZU5[YiKT3UiETGTiBRBRi8R=Ri0R0Ri\\iZZiUXiPSkcQySPk\QySPylQ8@@YySPk\QySPylQ8@@YySPk\QySPylQ8@@YySPk\QySPylQ8@@YySPk\QySPylQ8@@YySPylQH0MSL00000Rb=RPDRPPERPPFRPPGRPP0RPP=RPA0PHRPPIRPPJRPPKRPPLRPPMRPPNRPP=R000RPORPP0SPP1SPP2SPP3SPVNZhjCRiBRBRjARj@Rj?Rj>Rj=Rj<Rj;Rj:Rj9Rj8Rj7Rj6Rj5Rj4Rj3Rj2Rj1Ri0R0Ri\\iZZiUXiPSylQ80MSySPk^QySPPERPPFRPPGRPLPL00000RLPB0[XA1PORPP0SPP1SPP2SPPBRPP3SPLPB0[XUMZaj<Rj;Rj:Rj9Rj8Rj7Rj6Rj5Rj4Rj3Rj2Rj1Ri0R0Ri\\iZZiUXiPSySPkeQySPPERPPFRPPGRPLPL000RPORPP0SPP1SPP2SPPBRPP3SPLPB0[XUMZaj<Rj;Rj:Rj9Rj8Rj7Rj6Rj5Rj4Rj3Rj2Rj1Ri0R0Ri\\iZZiUXiPSySPkeQySPcySPylQ@0MSySQylQ80MSySPk^QySPP2RPP3RPP4RPRPL000RP>RPP?RPP@RPPARPPBRPPCRPP=RPUMZaj<Rj;Rj:Rj9Rj8Rj7Rj6Rj5Rj4Rj3Rj2Rj1Ri0R0Ri\\iZZiUXiPSLPB0[Xh0RLPB0[XgCcySPRPL000RuqkeRySPylQ@0MSP=RPL000NOQvqcySQ"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2F.T_RLOOP_4000000_BGBlob_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_RLOOP_4000000_BGBlob_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0.

Module C_MF_1f6a4_n_c4000000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_0.

Definition ROOT : sstate := (t_st T_Ubs2F.R_MF_1f6a4_n_c4000000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_0).
Definition CUTS : IMap.t template := imap_of [(203%uint63, T_Ubs2F.T_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0); (204%uint63, T_Ubs2F.T_EXIT_2_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2F.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Yb0NLS40MS80MS<0MSD0MSD3MS4EMS01NSDM3YL>4Y4<5Y4F5Y4@@Y<2AY0BAY<G4Z<A6Z8<7ZPMRPPNRPPORPP0SPP1SPP2SPP3SPP4SPP5SPP6SPP7SPP8SPP9SPP:SPP9RPP;SPP;RPP4RPU;VfjARj@Rj?Rj>Rj=Rj<Rj;Rj:Rj9Rj8Rj7Rj6Rj5Rj4Rj3Rj2Rj1Rj0Ri\\iZZiUXiPSySPk[QySPPMRPPNRPPORPP0SPP1SPP2SPP3SPP4SPP5SPP6SPP7SPP8SPP9SPP:SPP9RPP;SPP;RPP4RPU<VfjARj@Rj?Rj>Rj=Rj<Rj;Rj:Rj9Rj8Rj7Rj6Rj5Rj4Rj3Rj2Rj1Rj0Ri\\iZZiUXiPSySPk[QySPcySP"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2F.R_MF_1f6a4_n_c4000000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_0) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_MF_1f6a4_n_c4000000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_0.

Module C_MF_1f6a4_n_c4000000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_1.
Definition Fc0 : fact := (FAlign 92%uint63 4%uint63).
Definition Fc1 : fact := (FRange 92%uint63 (wp 4096%uint63) (wp 140737488355327%uint63)).
Definition FSc0 : list fact := (F147 :: Fc0 :: Fc1 :: FS185).
Definition FSc1 : list fact := (F146 :: FSc0).

Definition ROOT : sstate := (t_st T_Ubs2F.R_MF_1f6a4_n_c4000000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_1).
Definition CUTS : IMap.t template := imap_of [(207%uint63, T_Ubs2F.T_LIB_r10o5n0o7n1o1n12o3n2_s1_w0_e0b0)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2F.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Yb0NLS40MS80MS<0MSD0MSD3MS4EMS01NSDM3YL>4Y4<5Y4F5Y4@@Y<2AY0BAY<G4Z<A6Z8<7ZLQB1TQLIQA2LAQA6LPB0TQA8ZRPLVA0ZLPB0[XRPA1MJOOOOOOOOOOOWA0ZPLRPPNRPPORPP0SPP2SPP3SPP4SPP5SPP6SPP7SPP8SPP9SPP:SPP;SPP9RPP<SPP4RPL00000RP;RPU?VhjCRjBRjARj@Rj?Rj>Rj=Rj<Rj;Rj:Rj9Rj8Rj7Rj6Rj5Rj4Rj3Rj2Rj1Ri0R0Ri\\iZZiUXiPSySPk_QRQRRA0LPB0[XvqRRLPB0]XeqRQLPB0^XeqySP"%pstring.
Definition OBLS : list obligation := [

  (FSc0,
   F146);

  (FSc1,
   F145) ].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2F.R_MF_1f6a4_n_c4000000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_1) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_MF_1f6a4_n_c4000000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_1.

Module C_MF_1f6a4_n_c4000000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_0.

Definition ROOT : sstate := (t_st T_Ubs2F.R_MF_1f6a4_n_c4000000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_0).
Definition CUTS : IMap.t template := imap_of [(203%uint63, T_Ubs2F.T_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0); (204%uint63, T_Ubs2F.T_EXIT_2_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2F.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Yb0NLS40MS80MS<0MSD0MSD3MS4EMS01NSDM3YL>4Y4<5Y4F5Y4@@Y<2AY0BAY<G4Z<A6Z8<7ZPMRPPNRPPORPP0SPP1SPP2SPP3SPP4SPP5SPP6SPP7SPP8SPP9SPP:SPP9RPP;SPP;RPP4RPU;VfjARj@Rj?Rj>Rj=Rj<Rj;Rj:Rj9Rj8Rj7Rj6Rj5Rj4Rj3Rj2Rj1Rj0Ri\\iZZiUXiPSySPk[QySPPMRPPNRPPORPP0SPP1SPP2SPP3SPP4SPP5SPP6SPP7SPP8SPP9SPP:SPP9RPP;SPP;RPP4RPU<VfjARj@Rj?Rj>Rj=Rj<Rj;Rj:Rj9Rj8Rj7Rj6Rj5Rj4Rj3Rj2Rj1Rj0Ri\\iZZiUXiPSySPk[QySPcySP"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2F.R_MF_1f6a4_n_c4000000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_0) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_MF_1f6a4_n_c4000000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_0.

Module C_MF_1f6a4_n_c4000000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_1.
Definition Fc0 : fact := (FAlign 92%uint63 4%uint63).
Definition Fc1 : fact := (FRange 92%uint63 (wp 4096%uint63) (wp 140737488355327%uint63)).
Definition FSc0 : list fact := (F147 :: Fc0 :: Fc1 :: FS186).
Definition FSc1 : list fact := (F146 :: FSc0).

Definition ROOT : sstate := (t_st T_Ubs2F.R_MF_1f6a4_n_c4000000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_1).
Definition CUTS : IMap.t template := imap_of [(208%uint63, T_Ubs2F.T_LIB_r10o5n0o7n1o1n12o3n2_s1_w0_e0b0z)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2F.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Yb0NLS40MS80MS<0MSD0MSD3MS4EMS01NSDM3YL>4Y4<5Y4F5Y4@@Y<2AY0BAY<G4Z<A6Z8<7ZLQB1TQLIQA2LAQA6LPB0TQA8ZRPLVA0ZLPB0[XRPA1MJOOOOOOOOOOOWA0ZPLRPPNRPPORPP0SPP2SPP3SPP4SPP5SPP6SPP7SPP8SPP9SPP:SPP;SPP9RPP<SPP4RPL00000RP;RPU@VhjCRjBRjARj@Rj?Rj>Rj=Rj<Rj;Rj:Rj9Rj8Rj7Rj6Rj5Rj4Rj3Rj2Rj1Ri0R0Ri\\iZZiUXiPSySPk_QRQRRA0LPB0[XvqRRLPB0]XeqRQLPB0^XeqySP"%pstring.
Definition OBLS : list obligation := [

  (FSc0,
   F146);

  (FSc1,
   F145) ].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2F.R_MF_1f6a4_n_c4000000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_1) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_MF_1f6a4_n_c4000000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_1.

Module C_MF_1f6a4_n_c4000000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_0.

Definition ROOT : sstate := (t_st T_Ubs2F.R_MF_1f6a4_n_c4000000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_0).
Definition CUTS : IMap.t template := imap_of [(203%uint63, T_Ubs2F.T_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0); (204%uint63, T_Ubs2F.T_EXIT_2_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2F.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Yb0NLS40MS80MS<0MSD0MSD3MS4EMS01NSDM3YL>4Y4<5Y4F5Y4@@Y<2AY0BAY<G4Z<A6Z8<7ZPMRPPNRPPORPP0SPP1SPP2SPP3SPP4SPP5SPP6SPP7SPP8SPP9SPP:SPP9RPP;SPP;RPP4RPU;VfjARj@Rj?Rj>Rj=Rj<Rj;Rj:Rj9Rj8Rj7Rj6Rj5Rj4Rj3Rj2Rj1Rj0Ri\\iZZiUXiPSySPk[QySPPMRPPNRPPORPP0SPP1SPP2SPP3SPP4SPP5SPP6SPP7SPP8SPP9SPP:SPP9RPP;SPP;RPP4RPU<VfjARj@Rj?Rj>Rj=Rj<Rj;Rj:Rj9Rj8Rj7Rj6Rj5Rj4Rj3Rj2Rj1Rj0Ri\\iZZiUXiPSySPk[QySPcySP"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2F.R_MF_1f6a4_n_c4000000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_0) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_MF_1f6a4_n_c4000000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_0.

Module C_MF_1f6a4_n_c4000000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_1.
Definition Fc0 : fact := (FAlign 92%uint63 4%uint63).
Definition Fc1 : fact := (FRange 92%uint63 (wp 4096%uint63) (wp 140737488355327%uint63)).
Definition FSc0 : list fact := (F147 :: Fc0 :: Fc1 :: FS187).
Definition FSc1 : list fact := (F146 :: FSc0).

Definition ROOT : sstate := (t_st T_Ubs2F.R_MF_1f6a4_n_c4000000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_1).
Definition CUTS : IMap.t template := imap_of [(209%uint63, T_Ubs2F.T_LIB_r10o5n0o7n1o1n12o3n2_s2_w0_e0b0)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2F.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Yb0NLS40MS80MS<0MSD0MSD3MS4EMS01NSDM3YL>4Y4<5Y4F5Y4@@Y<2AY0BAY<G4Z<A6Z8<7ZLQB1TQLIQA2LAQA6LPB0TQA8ZRPLVA0ZLPB0[XRPA1MJOOOOOOOOOOOWA0ZPLRPPNRPPORPP0SPP2SPP3SPP4SPP5SPP6SPP7SPP8SPP9SPP:SPP;SPP9RPP<SPP4RPL00000RP;RPUAVhjCRjBRjARj@Rj?Rj>Rj=Rj<Rj;Rj:Rj9Rj8Rj7Rj6Rj5Rj4Rj3Rj2Rj1Ri0R0Ri\\iZZiUXiPSySPk_QRQRRA0LPB0[XvqRRLPB0]XeqRQLPB0^XeqySP"%pstring.
Definition OBLS : list obligation := [

  (FSc0,
   F146);

  (FSc1,
   F145) ].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2F.R_MF_1f6a4_n_c4000000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_1) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_MF_1f6a4_n_c4000000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_1.

Module C_MF_1f6a4_n_c4000000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_0.

Definition ROOT : sstate := (t_st T_Ubs2F.R_MF_1f6a4_n_c4000000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_0).
Definition CUTS : IMap.t template := imap_of [(203%uint63, T_Ubs2F.T_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0); (204%uint63, T_Ubs2F.T_EXIT_2_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2F.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Yb0NLS40MS80MS<0MSD0MSD3MS4EMS01NSDM3YL>4Y4<5Y4F5Y4@@Y<2AY0BAY<G4Z<A6Z8<7ZPMRPPNRPPORPP0SPP1SPP2SPP3SPP4SPP5SPP6SPP7SPP8SPP9SPP:SPP9RPP;SPP;RPP4RPU;VfjARj@Rj?Rj>Rj=Rj<Rj;Rj:Rj9Rj8Rj7Rj6Rj5Rj4Rj3Rj2Rj1Rj0Ri\\iZZiUXiPSySPk[QySPPMRPPNRPPORPP0SPP1SPP2SPP3SPP4SPP5SPP6SPP7SPP8SPP9SPP:SPP9RPP;SPP;RPP4RPU<VfjARj@Rj?Rj>Rj=Rj<Rj;Rj:Rj9Rj8Rj7Rj6Rj5Rj4Rj3Rj2Rj1Rj0Ri\\iZZiUXiPSySPk[QySPcySP"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2F.R_MF_1f6a4_n_c4000000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_0) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_MF_1f6a4_n_c4000000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_0.

Module C_MF_1f6a4_n_c4000000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_1.
Definition Fc0 : fact := (FAlign 92%uint63 4%uint63).
Definition Fc1 : fact := (FRange 92%uint63 (wp 4096%uint63) (wp 140737488355327%uint63)).
Definition FSc0 : list fact := (F147 :: Fc0 :: Fc1 :: FS188).
Definition FSc1 : list fact := (F146 :: FSc0).

Definition ROOT : sstate := (t_st T_Ubs2F.R_MF_1f6a4_n_c4000000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_1).
Definition CUTS : IMap.t template := imap_of [(210%uint63, T_Ubs2F.T_LIB_r10o5n0o7n1o1n12o3n2_s3_w0_e0b0)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2F.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Yb0NLS40MS80MS<0MSD0MSD3MS4EMS01NSDM3YL>4Y4<5Y4F5Y4@@Y<2AY0BAY<G4Z<A6Z8<7ZLQB1TQLIQA2LAQA6LPB0TQA8ZRPLVA0ZLPB0[XRPA1MJOOOOOOOOOOOWA0ZPLRPPNRPPORPP0SPP2SPP3SPP4SPP5SPP6SPP7SPP8SPP9SPP:SPP;SPP9RPP<SPP4RPL00000RP;RPUBVhjCRjBRjARj@Rj?Rj>Rj=Rj<Rj;Rj:Rj9Rj8Rj7Rj6Rj5Rj4Rj3Rj2Rj1Ri0R0Ri\\iZZiUXiPSySPk_QRQRRA0LPB0[XvqRRLPB0]XeqRQLPB0^XeqySP"%pstring.
Definition OBLS : list obligation := [

  (FSc0,
   F146);

  (FSc1,
   F145) ].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2F.R_MF_1f6a4_n_c4000000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_1) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_MF_1f6a4_n_c4000000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_1.

Module C_MF_1f6a4_n_c4000000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_0.

Definition ROOT : sstate := (t_st T_Ubs2F.R_MF_1f6a4_n_c4000000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_0).
Definition CUTS : IMap.t template := imap_of [(203%uint63, T_Ubs2F.T_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0); (204%uint63, T_Ubs2F.T_EXIT_2_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2F.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Yb0NLS40MS80MS<0MSD0MSD3MS4EMS01NSDM3YL>4Y4<5Y4F5Y4@@Y<2AY0BAY<G4Z<A6Z8<7ZPMRPPNRPPORPP0SPP1SPP2SPP3SPP4SPP5SPP6SPP7SPP8SPP9SPP:SPP9RPP;SPP;RPP4RPU;VfjARj@Rj?Rj>Rj=Rj<Rj;Rj:Rj9Rj8Rj7Rj6Rj5Rj4Rj3Rj2Rj1Rj0Ri\\iZZiUXiPSySPk[QySPPMRPPNRPPORPP0SPP1SPP2SPP3SPP4SPP5SPP6SPP7SPP8SPP9SPP:SPP9RPP;SPP;RPP4RPU<VfjARj@Rj?Rj>Rj=Rj<Rj;Rj:Rj9Rj8Rj7Rj6Rj5Rj4Rj3Rj2Rj1Rj0Ri\\iZZiUXiPSySPk[QySPcySP"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2F.R_MF_1f6a4_n_c4000000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_0) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_MF_1f6a4_n_c4000000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_0.

Module C_MF_1f6a4_n_c4000000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_1.
Definition Fc0 : fact := (FAlign 92%uint63 4%uint63).
Definition Fc1 : fact := (FRange 92%uint63 (wp 4096%uint63) (wp 140737488355327%uint63)).
Definition FSc0 : list fact := (F147 :: Fc0 :: Fc1 :: FS189).
Definition FSc1 : list fact := (F146 :: FSc0).

Definition ROOT : sstate := (t_st T_Ubs2F.R_MF_1f6a4_n_c4000000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_1).
Definition CUTS : IMap.t template := imap_of [(211%uint63, T_Ubs2F.T_LIB_r10o5n0o7n1o1n12o3n2_s4_w0_e0b0)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2F.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Yb0NLS40MS80MS<0MSD0MSD3MS4EMS01NSDM3YL>4Y4<5Y4F5Y4@@Y<2AY0BAY<G4Z<A6Z8<7ZLQB1TQLIQA2LAQA6LPB0TQA8ZRPLVA0ZLPB0[XRPA1MJOOOOOOOOOOOWA0ZPLRPPNRPPORPP0SPP2SPP3SPP4SPP5SPP6SPP7SPP8SPP9SPP:SPP;SPP9RPP<SPP4RPL00000RP;RPUCVhjCRjBRjARj@Rj?Rj>Rj=Rj<Rj;Rj:Rj9Rj8Rj7Rj6Rj5Rj4Rj3Rj2Rj1Ri0R0Ri\\iZZiUXiPSySPk_QRQRRA0LPB0[XvqRRLPB0]XeqRQLPB0^XeqySP"%pstring.
Definition OBLS : list obligation := [

  (FSc0,
   F146);

  (FSc1,
   F145) ].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2F.R_MF_1f6a4_n_c4000000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_1) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_MF_1f6a4_n_c4000000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_1.

Module C_SWRET_4c7a8_r9o2n1o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230.

Definition ROOT : sstate := (t_st T_Ubs2F.T_SWRET_4c7a8_r9o2n1o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230).
Definition CUTS : IMap.t template := imap_of [(359%uint63, T_Ubs2F.T_EXIT_2_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2F.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "P2RPP3RPP4RPP7RPP8RPP9RPP:RPP;RPP<RPP=RPP>RPP?RPP@RPPARPPBRPPCRPPDRPPERPPFRPU7[hjCRjBRjARj@Rj?Rj>Rj=Rj<Rj;Rj:Rj9Rj8Rj7Rj6Rj5Rj4Rj3Rj2Rj1Ri0R0Ri\\iZZiUXiPSylb0NLS40MS80MS<0MSD0MSD3MS4EMS01NSDM3YL>4Y4<5Y4F5Y4@@Y<2AY0BAY<G4Z<A6Z8<7Z"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2F.T_SWRET_4c7a8_r9o2n1o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_SWRET_4c7a8_r9o2n1o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230.

Module C_EXIT_2_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0.

Definition ROOT : sstate := (t_st T_Ubs2F.T_EXIT_2_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0).
Definition CUTS : IMap.t template := imap_of [].
Definition ECALLS : IMap.t sstate := imap_of [(360%uint63, T_Ubs2F.E_EXIT_2_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_1)].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2F.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "w8[Wi9R>Ri7R7Ri0R3Ri\\iZZiUXiPSylb0NLS40MS80MS<0MSD0MSD3MS4EMS01NSDM3YL>4Y4<5Y4F5Y4@@Y<2AY0BAY<G4Z<A6Z8<7ZylQ0?4Y"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2F.T_EXIT_2_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_EXIT_2_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0.
