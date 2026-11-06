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
Module C_XA_52944_61dc2_p68250_w5_r12_p3h6818cc132.

Definition ROOT : sstate := (t_st T_Ubs2E.T_XA_52944_61dc2_p68250_w5_r12_p3h6818cc132).
Definition CUTS : IMap.t template := imap_of [(160%uint63, T_Ubs2E.T_UW_52944_61dc2_w5_r12_p3h6818ccc7a_L0)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2E.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y_LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZP0ZPP1ZPP2ZPLQP4ZPP5ZPP6ZPP7ZPP8ZPP9ZPP:ZPP;ZPP<ZPP=ZPLQP>ZPPIVPLQPJVPPKVPPLVPPMVPU0U3Qj>Wj=Wj<Wj;Wj:Wj9Wj8Wj7Wj6Wj5Wj4Wj3Wj2Wj1Wj0WjOVjNVjMVjLVjKVjJVjIViIUIUiHTHTi7T7TiCSCSi=SASi;S;Si@R9Si:R;Ri0R0Ri\\iZZiUXiPSfQ0000OOOOOOOOWDEOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPP0ZPP1ZPP2ZPM;CIOOOOOOOOOWP4ZPP5ZPP6ZPP7ZPP8ZPP9ZPP:ZPP;ZPP<ZPP=ZPP:SPP>ZPPIVPL0H:FB1M8>2C6TPJVPPKVPPLVPPMVPU0U3Qj>Wj=Wj<Wj;Wj:Wj9Wj8Wj7Wj6Wj5Wj4Wj3Wj2Wj1Wj0WjOVjNVjMVjLVjKVjJVjIViIUIUiHTHTi7T7TiCSCSi=SASi;S;Si@R9Si:R;Ri0R0Ri\\iZZiUXiPSfQ0000OOOOOOOOWDEOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPcySPylQ<71X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2E.T_XA_52944_61dc2_p68250_w5_r12_p3h6818cc132) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_XA_52944_61dc2_p68250_w5_r12_p3h6818cc132.

Module C_XA_52944_8ec98_blk_w6_r13_L0.

Definition ROOT : sstate := (t_st T_Ubs2E.T_XA_52944_8ec98_blk_w6_r13_L0).
Definition CUTS : IMap.t template := imap_of [(163%uint63, T_Ubs2E.T_UW_52944_8ec98_w6_r13_p3h6818cc68b_L0)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2E.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y_LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZP:ZPP;ZPP<ZPLQP>ZPP?ZPP@ZPPAZPPBZPPCZPPDZPPEZPPFZPPGZPLQPHZPPJVPPKVPPLVPLQP3WPP4WPP5WPP6WPP7WPU3U7QjBWjAWj@Wj?Wj>Wj=Wj<Wj;Wj:Wj9Wj8Wj7Wj6Wj5Wj4Wj3Wj2Wj1Wj0WjOVjNVjMVjLVjKVjJViIVIViIUIUiHTHTi7T7TiCSCSi=SASi;S;Si@R9Si:R;Ri0R0Ri\\iZZiUXiPSfQ0000OOOOOOOOWDEOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPP:ZPP;ZPP<ZPM;CIOOOOOOOOOWP>ZPP?ZPP@ZPPAZPPBZPPCZPPDZPPEZPPFZPPGZPP:SPPHZPPJVPPKVPPLVPL0H:FB1M8>2C6TP3WPP4WPP5WPP6WPP7WPU3U7QjBWjAWj@Wj?Wj>Wj=Wj<Wj;Wj:Wj9Wj8Wj7Wj6Wj5Wj4Wj3Wj2Wj1Wj0WjOVjNVjMVjLVjKVjJViIVIViIUIUiHTHTi7T7TiCSCSi=SASi;S;Si@R9Si:R;Ri0R0Ri\\iZZiUXiPSfQ0000OOOOOOOOWDEOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPcySPylQ<71X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2E.T_XA_52944_8ec98_blk_w6_r13_L0) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_XA_52944_8ec98_blk_w6_r13_L0.

Module C_XA_52944_8ec98_p68250_w5_r12_p3h6818cc99d.

Definition ROOT : sstate := (t_st T_Ubs2E.T_XA_52944_8ec98_p68250_w5_r12_p3h6818cc99d).
Definition CUTS : IMap.t template := imap_of [(162%uint63, T_Ubs2E.T_UW_52944_8ec98_w5_r12_p3h6818cc113_L0)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2E.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y_LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZP0ZPP1ZPP2ZPLQP4ZPP5ZPP6ZPP7ZPP8ZPP9ZPP:ZPP;ZPP<ZPP=ZPLQP>ZPPIVPLQPJVPPKVPPLVPPMVPU2U3Qj>Wj=Wj<Wj;Wj:Wj9Wj8Wj7Wj6Wj5Wj4Wj3Wj2Wj1Wj0WjOVjNVjMVjLVjKVjJVjIViIUIUiHTHTi7T7TiCSCSi=SASi;S;Si@R9Si:R;Ri0R0Ri\\iZZiUXiPSfQ0000OOOOOOOOWDEOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPP0ZPP1ZPP2ZPM;CIOOOOOOOOOWP4ZPP5ZPP6ZPP7ZPP8ZPP9ZPP:ZPP;ZPP<ZPP=ZPP:SPP>ZPPIVPL0H:FB1M8>2C6TPJVPPKVPPLVPPMVPU2U3Qj>Wj=Wj<Wj;Wj:Wj9Wj8Wj7Wj6Wj5Wj4Wj3Wj2Wj1Wj0WjOVjNVjMVjLVjKVjJVjIViIUIUiHTHTi7T7TiCSCSi=SASi;S;Si@R9Si:R;Ri0R0Ri\\iZZiUXiPSfQ0000OOOOOOOOWDEOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPcySPylQ<71X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2E.T_XA_52944_8ec98_p68250_w5_r12_p3h6818cc99d) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_XA_52944_8ec98_p68250_w5_r12_p3h6818cc99d.

Module C_XA_52944_a3813_blk_w7_r14_L0.

Definition ROOT : sstate := (t_st T_Ubs2E.T_XA_52944_a3813_blk_w7_r14_L0).
Definition CUTS : IMap.t template := imap_of [(166%uint63, T_Ubs2E.T_UW_52944_a3813_w7_r14_pv_L0)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2E.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y_LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZP;ZPP<ZPP=ZPLQP?ZPP@ZPPAZPPBZPPCZPPDZPPEZPPFZPPGZPPHZPLQPIZPPKVPPLVPPMVPLQP4WPP5WPP6WPP7WPP8WPU6U8QjCWjBWjAWj@Wj?Wj>Wj=Wj<Wj;Wj:Wj9Wj8Wj7Wj6Wj5Wj4Wj3Wj2Wj1Wj0WjOVjNVjMVjLVjKViIVJViIUIUiHTHTi7T7TiFSFSiCSCSi=SASi;S;Si@R9Si:R;Ri0R0Ri\\iZZiUXiPSfQ0000OOOOOOOOWDEOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPP;ZPP<ZPP=ZPM;CIOOOOOOOOOWP?ZPP@ZPPAZPPBZPPCZPPDZPPEZPPFZPPGZPPHZPP:SPPIZPPKVPPLVPPMVPL0H:FB1M8>2C6TP4WPP5WPP6WPP7WPP8WPU6U8QjCWjBWjAWj@Wj?Wj>Wj=Wj<Wj;Wj:Wj9Wj8Wj7Wj6Wj5Wj4Wj3Wj2Wj1Wj0WjOVjNVjMVjLVjKViIVJViIUIUiHTHTi7T7TiFSFSiCSCSi=SASi;S;Si@R9Si:R;Ri0R0Ri\\iZZiUXiPSfQ0000OOOOOOOOWDEOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPcySPylQ<71X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2E.T_XA_52944_a3813_blk_w7_r14_L0) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_XA_52944_a3813_blk_w7_r14_L0.

Module C_XA_52944_a3813_p682f0_w6_r13_p3h6818cc776.

Definition ROOT : sstate := (t_st T_Ubs2E.T_XA_52944_a3813_p682f0_w6_r13_p3h6818cc776).
Definition CUTS : IMap.t template := imap_of [(164%uint63, T_Ubs2E.T_UW_52944_a3813_w6_r13_p3h6818cc5fb_L0)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2E.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y_LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZP1ZPP2ZPP3ZPLQP5ZPP6ZPP7ZPP8ZPP9ZPP:ZPP;ZPP<ZPP=ZPP>ZPLQP?ZPPJVPLQPKVPPLVPPMVPPNVPU4U4Qj?Wj>Wj=Wj<Wj;Wj:Wj9Wj8Wj7Wj6Wj5Wj4Wj3Wj2Wj1Wj0WjOVjNVjMVjLVjKVjJViIVIViIUIUiHTHTi7T7TiCSCSi=SASi;S;Si@R9Si:R;Ri0R0Ri\\iZZiUXiPSfQ0000OOOOOOOOWDEOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPP1ZPP2ZPP3ZPM;CIOOOOOOOOOWP5ZPP6ZPP7ZPP8ZPP9ZPP:ZPP;ZPP<ZPP=ZPP>ZPP:SPP?ZPPJVPL0H:FB1M8>2C6TPKVPPLVPPMVPPNVPU4U4Qj?Wj>Wj=Wj<Wj;Wj:Wj9Wj8Wj7Wj6Wj5Wj4Wj3Wj2Wj1Wj0WjOVjNVjMVjLVjKVjJViIVIViIUIUiHTHTi7T7TiCSCSi=SASi;S;Si@R9Si:R;Ri0R0Ri\\iZZiUXiPSfQ0000OOOOOOOOWDEOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPcySPylQ<71X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2E.T_XA_52944_a3813_p682f0_w6_r13_p3h6818cc776) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_XA_52944_a3813_p682f0_w6_r13_p3h6818cc776.

Module C_XA_52944_a3813_p682f0_w6_r13_p3h6824cc449.

Definition ROOT : sstate := (t_st T_Ubs2E.T_XA_52944_a3813_p682f0_w6_r13_p3h6824cc449).
Definition CUTS : IMap.t template := imap_of [(165%uint63, T_Ubs2E.T_UW_52944_a3813_w6_r13_p3h6824cc7f7_L0)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2E.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y_LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZP1ZPP2ZPP3ZPLQP5ZPP6ZPP7ZPP8ZPP9ZPP:ZPP;ZPP<ZPP=ZPP>ZPLQP?ZPPJVPLQPKVPPLVPPMVPPNVPU5U4Qj?Wj>Wj=Wj<Wj;Wj:Wj9Wj8Wj7Wj6Wj5Wj4Wj3Wj2Wj1Wj0WjOVjNVjMVjLVjKVjJViIVIViIUIUiHTHTi7T7TiCSCSi=SASi;S;Si@R9Si:R;Ri0R0Ri\\iZZiUXiPSfQ0000OOOOOOOOWDEOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPP1ZPP2ZPP3ZPM;CIOOOOOOOOOWP5ZPP6ZPP7ZPP8ZPP9ZPP:ZPP;ZPP<ZPP=ZPP>ZPP:SPP?ZPPJVPL0H:FB1M8>2C6TPKVPPLVPPMVPPNVPU5U4Qj?Wj>Wj=Wj<Wj;Wj:Wj9Wj8Wj7Wj6Wj5Wj4Wj3Wj2Wj1Wj0WjOVjNVjMVjLVjKVjJViIVIViIUIUiHTHTi7T7TiCSCSi=SASi;S;Si@R9Si:R;Ri0R0Ri\\iZZiUXiPSfQ0000OOOOOOOOWDEOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPcySPylQ<71X"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2E.T_XA_52944_a3813_p682f0_w6_r13_p3h6824cc449) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_XA_52944_a3813_p682f0_w6_r13_p3h6824cc449.

Module C_UW_52944_61dc2_w5_r12_p3h6818ccc7a_L0.

Definition ROOT : sstate := (t_st T_Ubs2E.T_UW_52944_61dc2_w5_r12_p3h6818ccc7a_L0).
Definition CUTS : IMap.t template := imap_of [(100%uint63, T_Ubs2E.T_FINAL_r8)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2E.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y_LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZY`LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X<I7XD58X4<5Y4F5Y8F5Y@@<Y<G4ZLLHMSL8QL<G0]PENQPL@;0]L<B0]L<G0]L<G0]LPL0TL=RPMNQPPNNQPPONQPP0OQPP@RPPARPPBRPPCRPPDRPPERPPFRPPGRPPHRPPIRPPJRPPKRPPLRPPMRPPNRPPORPP0SPP1SPP2SPP3SPP7WPLRP28RPU4S?QjLTjKTjJTjITjHTjGTjFTjETjDTjCTjBTjATj@Tj?Tj>Tj=Tj<Tj;Tj:Tj9Tj8Tj7Tj6Tj5Tj4Tj3Tj2Tj1Tj0TjOSjNSjMSjLSjKSjJSjISjHSjGSi=S@Si;S;Si4S9Si:R;Ri0R0Ri\\iZZiUXiPSk5QQfQ0000OOOOOOOOW6OOOOOOOOOOOWySPylQ<;3XySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPk[QySPk[QySPylQ45OSySPk[QySPk[QySPyl`LHMS05OSDJ0T@K0TLJ1TH7AT861X871XL03X8;3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPylQ<;3XySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOWDEOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOWDEOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOWDEOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOWDEOOOOOOOOOOWySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOWDEOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOWDEOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOWDEOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPySQ"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2E.T_UW_52944_61dc2_w5_r12_p3h6818ccc7a_L0) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_UW_52944_61dc2_w5_r12_p3h6818ccc7a_L0.

Module C_UW_52944_61dc2_w6_r13_p3h6824cc132_L0.

Definition ROOT : sstate := (t_st T_Ubs2E.T_UW_52944_61dc2_w6_r13_p3h6824cc132_L0).
Definition CUTS : IMap.t template := imap_of [(100%uint63, T_Ubs2E.T_FINAL_r8)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2E.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan (StrLz.lz_dec "-$:Y_LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZY`@#1%$)<I7XD58?%(-.$LLHMSP88RPP98RPP:8RPP;8RPP<8RPP=8RPP>8RPP?8RPP@8RPPA8RPPB8RPPC8RPPD8RPPE8RPP@RPPARPPBRPPCRPPDRPPERPPFRPPGRPPHRPPIRPPJRPPKRPPLRPPMRPPNRPPORPP0SPP1SPP2SPP3SPP8WPLRPF8RPU4S?QjLTjKTjJTjITjHTjGTjFTjETjDTjCTjBTjATj@Tj?Tj>Tj=Tj<Tj;Tj:Tj9Tj8Tj7Tj6Tj5Tj4Tj3Tj2Tj1Tj0TjOSjNSjMSjLSjKSjJSjISjHSjGSi=S@Si;S;Si4S9Si:R;Ri0R0Ri\\iZZiUXiPSk5QQfQ0000OOOOOOOOW62#,-#,OOOWySPk[QySPylQ<;3X@.5/,,klRySPkASQ1#)8#0@#)#>@$'$<<#7#[0#(1(#&45OS;#8315/(DJ0T@K@#?175@&5*6@#/$'100@'9(7@'('=$yS:1..$DE91..@%$%9@&/(2@$&%2@&6'-@%+($%ySQ"%pstring).
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2E.T_UW_52944_61dc2_w6_r13_p3h6824cc132_L0) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_UW_52944_61dc2_w6_r13_p3h6824cc132_L0.

Module C_UW_52944_8ec98_w5_r12_p3h6818cc113_L0.

Definition ROOT : sstate := (t_st T_Ubs2E.T_UW_52944_8ec98_w5_r12_p3h6818cc113_L0).
Definition CUTS : IMap.t template := imap_of [(100%uint63, T_Ubs2E.T_FINAL_r8)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2E.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Y_LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZY`LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X<I7XD58X4<5Y4F5Y8F5Y@@<Y<G4ZLLHMSL8QL<G0]PENQPL@;0]L<B0]L<G0]L<G0]LPL0TL=RPMNQPPNNQPPONQPP0OQPP@RPPARPPBRPPCRPPDRPPERPPFRPPGRPPHRPPIRPPJRPPKRPPLRPPMRPPNRPPORPP0SPP1SPP2SPP3SPP7WPLRP28RPU4S?QjLTjKTjJTjITjHTjGTjFTjETjDTjCTjBTjATj@Tj?Tj>Tj=Tj<Tj;Tj:Tj9Tj8Tj7Tj6Tj5Tj4Tj3Tj2Tj1Tj0TjOSjNSjMSjLSjKSjJSjISjHSjGSi=S@Si;S;Si4S9Si:R;Ri0R0Ri\\iZZiUXiPSk5QQfQ0000OOOOOOOOW6OOOOOOOOOOOWySPylQ<;3XySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPk[QySPk[QySPylQ45OSySPk[QySPk[QySPyl`LHMS05OSDJ0T@K0TLJ1TH7AT861X871XL03X8;3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPylQ<;3XySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOWDEOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOWDEOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOWDEOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOWDEOOOOOOOOOOWySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOWDEOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOWDEOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPkASQySPySQfQ0000OOOOOOOOWDEOOOOOOOOOOWySPkASQySPkASQySPkASQySPkASQySPkASQySPySQ"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2E.T_UW_52944_8ec98_w5_r12_p3h6818cc113_L0) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_UW_52944_8ec98_w5_r12_p3h6818cc113_L0.

Module C_UW_52944_8ec98_w6_r13_p3h6818cc68b_L0.

Definition ROOT : sstate := (t_st T_Ubs2E.T_UW_52944_8ec98_w6_r13_p3h6818cc68b_L0).
Definition CUTS : IMap.t template := imap_of [(100%uint63, T_Ubs2E.T_FINAL_r8)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2E.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan (StrLz.lz_dec "-$:Y_LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZY`@#1%$)<I7XD58?%(-.$LLHMSP88RPP98RPP:8RPP;8RPP<8RPP=8RPP>8RPP?8RPP@8RPPA8RPPB8RPPC8RPPD8RPPE8RPP@RPPARPPBRPPCRPPDRPPERPPFRPPGRPPHRPPIRPPJRPPKRPPLRPPMRPPNRPPORPP0SPP1SPP2SPP3SPP8WPLQPF8RPU4S?QjLTjKTjJTjITjHTjGTjFTjETjDTjCTjBTjATj@Tj?Tj>Tj=Tj<Tj;Tj:Tj9Tj8Tj7Tj6Tj5Tj4Tj3Tj2Tj1Tj0TjOSjNSjMSjLSjKSjJSjISjHSjGSi=S@Si;S;Si4S9Si:R;Ri0R0Ri\\iZZiUXiPSk5QQfQ0000OOOOOOOOW62#,-#,OOOWySPk[QySPylQ<;3X@.5/,,klRySPkASQ1#)8#0@#)#>@$'$<<#7#[0#(1(#&45OS;#8315/(DJ0T@K@#?175@&5*6@#/$'100@'9(7@'('=$yS:1..$DE91..@%$%9@&/(2@$&%2@&6'-@%+($%ySQ"%pstring).
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2E.T_UW_52944_8ec98_w6_r13_p3h6818cc68b_L0) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_UW_52944_8ec98_w6_r13_p3h6818cc68b_L0.

Module C_UW_52944_a3813_w6_r13_p3h6818cc5fb_L0.

Definition ROOT : sstate := (t_st T_Ubs2E.T_UW_52944_a3813_w6_r13_p3h6818cc5fb_L0).
Definition CUTS : IMap.t template := imap_of [(100%uint63, T_Ubs2E.T_FINAL_r8)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2E.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan (StrLz.lz_dec "-$:Y_LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZY`@#1%$)<I7XD58@#,%((DJ0T@K@#?'.--;LLHMSL<G0]P6OQPP7OQPL@;0]L<G0]L<<0]L<<0]LPL0TLHRP?OQPP@OQPPAOQPPBOQPP@RPPARPPBRPPCRPPDRPPERPPFRPPGRPPHRPPIRPPJRPPKRPPLRPPMRPPNRPPORPP0SPP1SPP2SPP3SPP8WPLQPD8RPU4S?QjLTjKTjJTjITjHTjGTjFTjETjDTjCTjBTjATj@Tj?Tj>Tj=Tj<Tj;Tj:Tj9Tj8Tj7Tj6Tj5Tj4Tj3Tj2Tj1Tj0TjOSjNSjMSjLSjKSjJSjISjHSjGSi=S@Si;S;Si4S9Si:R;Ri0R0Ri\\iZZiUXiPSk5QQfQ0000OOOOOOOOW62#,-#-OOOWySPylQ<;3XySPkASQ1#)8#0@#)#>@$'$<<#7#[0#(#Q0'>&45OS:#8$SR@&5(2@#5)71./@951,,$kl@';(@@'''=$yS:1,*$DE81,*@%$%9@&0(2@$&%2@&6'-@%+($%ySQ"%pstring).
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2E.T_UW_52944_a3813_w6_r13_p3h6818cc5fb_L0) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_UW_52944_a3813_w6_r13_p3h6818cc5fb_L0.

Module C_UW_52944_a3813_w6_r13_p3h6824cc7f7_L0.

Definition ROOT : sstate := (t_st T_Ubs2E.T_UW_52944_a3813_w6_r13_p3h6824cc7f7_L0).
Definition CUTS : IMap.t template := imap_of [(100%uint63, T_Ubs2E.T_FINAL_r8)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2E.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan (StrLz.lz_dec "-$:Y_LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZY`@#1%$)<I7XD58@#,%((DJ0T@K@#?'.--;LLHMSL<G0]P6OQPP7OQPL@;0]L<G0]L<B0]L<B0]LPL0TL8QP?OQPP@OQPPAOQPPBOQPP@RPPARPPBRPPCRPPDRPPERPPFRPPGRPPHRPPIRPPJRPPKRPPLRPPMRPPNRPPORPP0SPP1SPP2SPP3SPP8WPLRPD8RPU4S?QjLTjKTjJTjITjHTjGTjFTjETjDTjCTjBTjATj@Tj?Tj>Tj=Tj<Tj;Tj:Tj9Tj8Tj7Tj6Tj5Tj4Tj3Tj2Tj1Tj0TjOSjNSjMSjLSjKSjJSjISjHSjGSi=S@Si;S;Si4S9Si:R;Ri0R0Ri\\iZZiUXiPSk5QQfQ0000OOOOOOOOW62#,-#-OOOWySPylQ<;3XySPkASQ1#)8#0@#)#>@$'$<<#7#[0#(#Q0'>&45OS:#8$SR@&5(2@#5)71./@951,,$kl@';(@@'''=$yS:1,*$DE81,*@%$%9@&0(2@$&%2@&6'-@%+($%ySQ"%pstring).
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2E.T_UW_52944_a3813_w6_r13_p3h6824cc7f7_L0) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_UW_52944_a3813_w6_r13_p3h6824cc7f7_L0.

Module C_UW_52944_a3813_w7_r14_pv_L0.

Definition ROOT : sstate := (t_st T_Ubs2E.T_UW_52944_a3813_w7_r14_pv_L0).
Definition CUTS : IMap.t template := imap_of [(100%uint63, T_Ubs2E.T_FINAL_r8)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Ubs2E.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan (StrLz.lz_dec "-$:Y_LHMS05OS@J0TLJ1TH7AT861X871XL03X8;3X8I7X4<5Y4F5Y8F5Y@@<Y<G4ZY`@#1%$)<I7XD58@#,%((DJ0T@K@#?'.--@LLHMSPJ8RPPK8RPPL8RPPM8RPPN8RPPO8RPP09RPP19RPP29RPP39RPP49RPP59RPP69RPP79RPP@RPPARPPBRPPCRPPDRPPERPPFRPPGRPPHRPPIRPPJRPPKRPPLRPPMRPPNRPPORPP0SPP1SPP2SPP3SPP9WPPFSPP89RPU4S?QjLTjKTjJTjITjHTjGTjFTjETjDTjCTjBTjATj@Tj?Tj>Tj=Tj<Tj;Tj:Tj9Tj8Tj7Tj6Tj5Tj4Tj3Tj2Tj1Tj0TjOSjNSjMSjLSjKSjJSjISjHSjGSi=S@Si;S;Si4S9Si:R;Ri0R0Ri\\iZZiUXiPSfQ0000OOOOOOOOW62#,-#,OOOWySPk[QySPylQ<;3X@.3/*,klRySPkASQ1#)8#0@#)#>@$'$<<#7#[0#(1(#&45OS:#8#S@&6(2@#5)7@.:1,:@:%19$@&8.2@&1'(@$&$<%ySQ91,3$DE91,3@%$%9@&/(2@$&%2@&6'-@%+($%ySQ"%pstring).
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Ubs2E.T_UW_52944_a3813_w7_r14_pv_L0) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_UW_52944_a3813_w7_r14_pv_L0.
