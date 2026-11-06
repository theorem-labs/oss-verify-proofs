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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2L Require Import T_Ubs2L.
Module C_LIBENT_r8.

Definition ROOT : sstate := (t_st T_Ubs2F.T_LIBGEN_r8).
Definition CUTS : IMap.t template := imap_of [(101%uint63, T_Ubs2L.T_THROW_1fba8_LIBENT_r8_1); (103%uint63, T_Ubs2L.T_THROW_1fc40_LIBENT_r8_2); (105%uint63, T_Ubs2L.T_THROW_2037c_LIBENT_r8_4); (106%uint63, T_Ubs2L.T_THROW_52944_LIBENT_r8_3)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2L.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "YW0L1T861X4<5Y4F5Y8F5Y@@<Y<G4ZU5S[iHS6TiFSFSiCSCSi=SASi@R;Si:R;Ri0R0Ri\\iZZiUXiPSySPU7S\i9TGTi7T7TiFSFSiCSCSi=SASi@R;Si:R;Ri0R0Ri\\iZZiUXiPSySPU:S]i:UHUiHTHTi7T7TiFSFSiCSCSi=SASi@R;Si:R;Ri0R0Ri\\iZZiUXiPSySPU9S_i1V9ViKUMUiIUIUiHTHTi7T7TiFSFSiCSCSi=SASi@R;Si:R;Ri0R0Ri\\iZZiUXiPSySPk\QySPknRySPk\QySPknRySPknRySP"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2F.T_LIBGEN_r8) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_LIBENT_r8.

Module C_LIBENT_r9.

Definition ROOT : sstate := (t_st T_Ubs2F.T_LIBGEN_r9).
Definition CUTS : IMap.t template := imap_of [(100%uint63, T_Ubs2L.T_G0_r14o5n0o7n1o1n24o3n2); (102%uint63, T_Ubs2L.T_THROW_1fba8_LIBENT_r9_1); (104%uint63, T_Ubs2L.T_THROW_1fc40_LIBENT_r9_2); (107%uint63, T_Ubs2L.T_THROW_52944_LIBENT_r9_3); (108%uint63, T_Ubs2L.T_THROW_52944_LIBENT_r9_4)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2L.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "YW0L1T861X4<5Y4F5Y8F5Y@@<Y<G4ZU6SYiGS5Ti>SESiAR<Si;R<Ri0R1Ri\\iZZiUXiPSySPU8SZi8TFTi6T6Ti>SESiAR<Si;R<Ri0R1Ri\\iZZiUXiPSySPU;S[i9UGUiGTGTi6T6Ti>SESiAR<Si;R<Ri0R1Ri\\iZZiUXiPSySPU<S\i:VHViHUHUiGTGTi6T6Ti>SESiAR<Si;R<Ri0R1Ri\\iZZiUXiPSySPPHUPPIVPPKVPPLVPPMVPP1WPP2WPP3WPP4WPP5WPP6WPP7WPP8WPP9WPU4Shj:Uj9Uj8Uj7Uj6Uj5Uj4Uj3Uj2Uj1Uj0UjOTjNTjMTiGTGTi6T6Ti>SESiAR<Si;R<Ri0R1Ri\\iZZiUXiPSySPk\QySPknRySPk\QySPknRySPk\QySPknRySPknRySP"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2F.T_LIBGEN_r9) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_LIBENT_r9.
