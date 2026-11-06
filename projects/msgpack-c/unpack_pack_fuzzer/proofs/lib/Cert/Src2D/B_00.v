(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith List PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Mem Instr State Step Plan Notation.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Img Require Import ImgSrc ItabSrc RotSrc.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import Rot.
Import ListNotations W64 Val Mem FI St Step Plan.
From Stdlib Require Import PrimString.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require PlanDec.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require StrLz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib DefsA DefsM Defs DefsB.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2D Require Import T_Src2D.
Module C_DRV.

Definition ROOT : sstate := T_Src2D.T_DRV2.
Definition CUTS : IMap.t template := imap_of [(100%uint63, T_Src2D.T_OPEN_)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Src2D.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "U4SUi0R0Ri\\iZZiUXiPSylb0?KS4AKS8AKS<AKSDAKSDDKS46LS0BLS@MMXH>NX0<OX0FOX0@:Y82;YLA;Y8GNY8A0Z4<1Z"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN T_Src2D.T_DRV2 = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotSrc.ROT RotSrc.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_DRV.

Module C_OPEN__0.

Definition ROOT : sstate := (t_st T_Src2D.R_OPEN__0).
Definition CUTS : IMap.t template := imap_of [(101%uint63, T_Src2D.T_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Src2D.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Yb0?KS4AKS8AKS<AKSDAKSDDKS46LS0BLS@MMXH>NX0<OX0FOX0@:Y82;YLA;Y8GNY8A0Z4<1ZU5SUi0R0Ri\\iZZiUXiPSySPylc4?KS4AKS8AKS<AKSDAKSDDKS@1LS46LS0BLS@MMXH>NX0<OX0FOX0@:Y82;YLA;Y8GNY8A0Z4<1ZySP"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Src2D.R_OPEN__0) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotSrc.ROT RotSrc.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_OPEN__0.

Module C_OPEN__1.

Definition ROOT : sstate := (t_st T_Src2D.R_OPEN__1).
Definition CUTS : IMap.t template := imap_of [(102%uint63, T_Src2D.T_OPENERR_)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Src2D.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "MDOOOOOOOOOOOWP0RPL\U6SWj2Rj1Rj0Ri\\iZZiUXiPSylb0?KS4AKS8AKS<AKSDAKSDDKS46LS0BLS@MMXH>NX0<OX0FOX0@:Y82;YLA;Y8GNY8A0Z4<1Z"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Src2D.R_OPEN__1) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotSrc.ROT RotSrc.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_OPEN__1.

Module C_OPEN__2.

Definition ROOT : sstate := (t_st T_Src2D.R_OPEN__2).
Definition CUTS : IMap.t template := imap_of [(102%uint63, T_Src2D.T_OPENERR_)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Src2D.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "MCOOOOOOOOOOOWP0RPL]U6SWj2Rj1Rj0Ri\\iZZiUXiPSylb0?KS4AKS8AKS<AKSDAKSDDKS46LS0BLS@MMXH>NX0<OX0FOX0@:Y82;YLA;Y8GNY8A0Z4<1Z"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Src2D.R_OPEN__2) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotSrc.ROT RotSrc.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_OPEN__2.

Module C_OPEN__3.

Definition ROOT : sstate := (t_st T_Src2D.R_OPEN__3).
Definition CUTS : IMap.t template := imap_of [(102%uint63, T_Src2D.T_OPENERR_)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Src2D.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "M8OOOOOOOOOOOWP0RPLhU6SWj2Rj1Rj0Ri\\iZZiUXiPSylb0?KS4AKS8AKS<AKSDAKSDDKS46LS0BLS@MMXH>NX0<OX0FOX0@:Y82;YLA;Y8GNY8A0Z4<1Z"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Src2D.R_OPEN__3) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotSrc.ROT RotSrc.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_OPEN__3.

Module C_OPEN__4.

Definition ROOT : sstate := (t_st T_Src2D.R_OPEN__4).
Definition CUTS : IMap.t template := imap_of [(102%uint63, T_Src2D.T_OPENERR_)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Src2D.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "M9OOOOOOOOOOOWP0RPLgU6SWj2Rj1Rj0Ri\\iZZiUXiPSylb0?KS4AKS8AKS<AKSDAKSDDKS46LS0BLS@MMXH>NX0<OX0FOX0@:Y82;YLA;Y8GNY8A0Z4<1Z"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Src2D.R_OPEN__4) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotSrc.ROT RotSrc.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_OPEN__4.

Module C_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_0.

Definition ROOT : sstate := (t_st T_Src2D.R_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_0).
Definition CUTS : IMap.t template := imap_of [(103%uint63, T_Src2D.T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_0_1)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Src2D.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "U7SXi8R@Ri4R4Ri2R2Ri0R0Ri\\iZZiUXiPSylb0?KS4AKS8AKS<AKSDAKSDDKS46LS0BLS@MMXH>NX0<OX0FOX0@:Y82;YLA;Y8GNY8A0Z4<1Z"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Src2D.R_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_0) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotSrc.ROT RotSrc.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_0.

Module C_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1.

Definition ROOT : sstate := (t_st T_Src2D.R_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1).
Definition CUTS : IMap.t template := imap_of [(104%uint63, T_Src2D.T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_1); (105%uint63, T_Src2D.T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_10); (106%uint63, T_Src2D.T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_11); (107%uint63, T_Src2D.T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_12); (108%uint63, T_Src2D.T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_13); (109%uint63, T_Src2D.T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_14); (110%uint63, T_Src2D.T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_15); (111%uint63, T_Src2D.T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_16); (112%uint63, T_Src2D.T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_17); (113%uint63, T_Src2D.T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_18); (114%uint63, T_Src2D.T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_19); (115%uint63, T_Src2D.T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_2); (116%uint63, T_Src2D.T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_20); (117%uint63, T_Src2D.T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_21); (118%uint63, T_Src2D.T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_22); (119%uint63, T_Src2D.T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_23); (120%uint63, T_Src2D.T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_24); (121%uint63, T_Src2D.T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_25); (122%uint63, T_Src2D.T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_26); (123%uint63, T_Src2D.T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_27); (124%uint63, T_Src2D.T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_28); (125%uint63, T_Src2D.T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_29); (126%uint63, T_Src2D.T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_3); (127%uint63, T_Src2D.T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_30); (128%uint63, T_Src2D.T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_31); (129%uint63, T_Src2D.T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_32); (130%uint63, T_Src2D.T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_33); (131%uint63, T_Src2D.T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_34); (132%uint63, T_Src2D.T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_35); (133%uint63, T_Src2D.T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_36); (134%uint63, T_Src2D.T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_37); (135%uint63, T_Src2D.T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_38); (136%uint63, T_Src2D.T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_39); (137%uint63, T_Src2D.T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_4); (138%uint63, T_Src2D.T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_40); (139%uint63, T_Src2D.T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_41); (140%uint63, T_Src2D.T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_42); (141%uint63, T_Src2D.T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_43); (142%uint63, T_Src2D.T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_44); (143%uint63, T_Src2D.T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_45); (144%uint63, T_Src2D.T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_46); (145%uint63, T_Src2D.T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_47); (146%uint63, T_Src2D.T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_48); (147%uint63, T_Src2D.T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_49); (148%uint63, T_Src2D.T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_5); (149%uint63, T_Src2D.T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_50); (150%uint63, T_Src2D.T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_51); (151%uint63, T_Src2D.T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_52); (152%uint63, T_Src2D.T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_53); (153%uint63, T_Src2D.T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_54); (154%uint63, T_Src2D.T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_55); (155%uint63, T_Src2D.T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_56); (156%uint63, T_Src2D.T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_57); (157%uint63, T_Src2D.T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_58); (158%uint63, T_Src2D.T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_59); (159%uint63, T_Src2D.T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_6); (160%uint63, T_Src2D.T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_60); (161%uint63, T_Src2D.T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_61); (162%uint63, T_Src2D.T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_62); (163%uint63, T_Src2D.T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_63); (164%uint63, T_Src2D.T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_7); (165%uint63, T_Src2D.T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_8); (166%uint63, T_Src2D.T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_9)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Src2D.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan (StrLz.lz_dec "-&?Yb0?KS4AKS8AKS<AKSDAKSDDKS46LS0BLS@MMXH>NX0<OX0FOX0@:Y82;YLA;Y8GNY8A0Z4<1ZU8SXi9UAUi3U5UiARARi0R0Ri\\iZZiUXiPSkcQySPk\QySPylQ4@:Y:#2$UC@$5%-#N@$5%-$9T@$4%-#D@$5%-#O@$5%-$4U@$4%-#5@$5%-#6@$5%-#9@$51%3#:@$5%-#;@$5%-#<@$5%-#=@$5%-#>@$5%-#?@$5%-#@@$5%-#A@$5%-#B@$5%-#D@$5%-#E@$5%-#F@$5%-#G@$5%-#H@$5%-#I@$5%-#J@$5%-#K@$5%-#L@$5%-#M@$5%-#O@$5%-#0@$522'#1@$5%-#2@$5%-#3@$629*@$5%-#5@$5%-#6@$5%-#7@$5%-#8@$5%-#:@$5%-#;@$5%-#<@$5%-#=@$5%-#>@$5%-#?@$5%-#@@$5%-#A@$5%-#B@$5%-#C@$5%-#E@$5%-#F@$5%-#G@$5%-#H@$5%-#I@$5%-#J@$5%-#K@$5%-#L@$5%-#M@$5%-#N@$5%-#0@$5437#1@$5%--#*2UYiHT1UiETETiCTCT@#6%2-#0s9NQNQU3UYi8TATi5T5Ti3T3@#*%(#c>'<#`@#.(4'ySPkf1#2)@AKSySP"%pstring).
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Src2D.R_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotSrc.ROT RotSrc.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1.

Module C_OPENERR_.

Definition ROOT : sstate := (t_st T_Src2D.T_OPENERR_).
Definition CUTS : IMap.t template := imap_of [(167%uint63, T_Src2D.T_SW_OPENERR__1); (168%uint63, T_Src2D.T_SW_OPENERR__10); (169%uint63, T_Src2D.T_SW_OPENERR__11); (170%uint63, T_Src2D.T_SW_OPENERR__12); (171%uint63, T_Src2D.T_SW_OPENERR__13); (172%uint63, T_Src2D.T_SW_OPENERR__14); (173%uint63, T_Src2D.T_SW_OPENERR__15); (174%uint63, T_Src2D.T_SW_OPENERR__16); (175%uint63, T_Src2D.T_SW_OPENERR__17); (176%uint63, T_Src2D.T_SW_OPENERR__18); (177%uint63, T_Src2D.T_SW_OPENERR__19); (178%uint63, T_Src2D.T_SW_OPENERR__2); (179%uint63, T_Src2D.T_SW_OPENERR__20); (180%uint63, T_Src2D.T_SW_OPENERR__21); (181%uint63, T_Src2D.T_SW_OPENERR__22); (182%uint63, T_Src2D.T_SW_OPENERR__23); (183%uint63, T_Src2D.T_SW_OPENERR__24); (184%uint63, T_Src2D.T_SW_OPENERR__25); (185%uint63, T_Src2D.T_SW_OPENERR__26); (186%uint63, T_Src2D.T_SW_OPENERR__27); (187%uint63, T_Src2D.T_SW_OPENERR__28); (188%uint63, T_Src2D.T_SW_OPENERR__29); (189%uint63, T_Src2D.T_SW_OPENERR__3); (190%uint63, T_Src2D.T_SW_OPENERR__30); (191%uint63, T_Src2D.T_SW_OPENERR__31); (192%uint63, T_Src2D.T_SW_OPENERR__32); (193%uint63, T_Src2D.T_SW_OPENERR__33); (194%uint63, T_Src2D.T_SW_OPENERR__34); (195%uint63, T_Src2D.T_SW_OPENERR__35); (196%uint63, T_Src2D.T_SW_OPENERR__36); (197%uint63, T_Src2D.T_SW_OPENERR__37); (198%uint63, T_Src2D.T_SW_OPENERR__38); (199%uint63, T_Src2D.T_SW_OPENERR__39); (200%uint63, T_Src2D.T_SW_OPENERR__4); (201%uint63, T_Src2D.T_SW_OPENERR__40); (202%uint63, T_Src2D.T_SW_OPENERR__41); (203%uint63, T_Src2D.T_SW_OPENERR__42); (204%uint63, T_Src2D.T_SW_OPENERR__43); (205%uint63, T_Src2D.T_SW_OPENERR__44); (206%uint63, T_Src2D.T_SW_OPENERR__45); (207%uint63, T_Src2D.T_SW_OPENERR__46); (208%uint63, T_Src2D.T_SW_OPENERR__47); (209%uint63, T_Src2D.T_SW_OPENERR__48); (210%uint63, T_Src2D.T_SW_OPENERR__49); (211%uint63, T_Src2D.T_SW_OPENERR__5); (212%uint63, T_Src2D.T_SW_OPENERR__50); (213%uint63, T_Src2D.T_SW_OPENERR__51); (214%uint63, T_Src2D.T_SW_OPENERR__52); (215%uint63, T_Src2D.T_SW_OPENERR__53); (216%uint63, T_Src2D.T_SW_OPENERR__54); (217%uint63, T_Src2D.T_SW_OPENERR__55); (218%uint63, T_Src2D.T_SW_OPENERR__56); (219%uint63, T_Src2D.T_SW_OPENERR__57); (220%uint63, T_Src2D.T_SW_OPENERR__58); (221%uint63, T_Src2D.T_SW_OPENERR__59); (222%uint63, T_Src2D.T_SW_OPENERR__6); (223%uint63, T_Src2D.T_SW_OPENERR__60); (224%uint63, T_Src2D.T_SW_OPENERR__61); (225%uint63, T_Src2D.T_SW_OPENERR__62); (226%uint63, T_Src2D.T_SW_OPENERR__63); (227%uint63, T_Src2D.T_SW_OPENERR__64); (228%uint63, T_Src2D.T_SW_OPENERR__65); (229%uint63, T_Src2D.T_SW_OPENERR__7); (230%uint63, T_Src2D.T_SW_OPENERR__8); (231%uint63, T_Src2D.T_SW_OPENERR__9)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Src2D.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan (StrLz.lz_dec "-&:Yb0?KS4AKS8AKS<AKSDAKSDDKS46LS0BLS@MMXH>NX0<OX0FOX0@:Y82;YLA;Y8GNY8A0Z4<1ZU7UWiJT2UiDTFTi0R1Ri\\iZZiUXiPSkcQySPk\QySPylQ4@:Y:#2$UB@$0%(#M@$0%($8V@$/%(#C@$0%(#N@$0%($5W@$/%(#6@$0%(#7@$0%(#8@$01$.#9@$0%(#:@$0%(#;@$0%(#<@$0%(#=@$0%(#>@$0%(#?@$0%(#@@$0%(#A@$0%(#C@$0%(#D@$0%(#E@$0%(#F@$0%(#G@$0%(#H@$0%(#I@$0%(#J@$0%(#K@$0%(#L@$0%(#N@$0%(#O@$0%(#0@$020(#1@$0%(#2@$0%(#3@$0%(#4@$128@@$0%(#6@$0%(#7@$0%(#9@$0%(#:@$0%(#;@$0%(#<@$0%(#=@$0%(#>@$0%(#?@$0%(#@@$0%(#A@$0%(#B@$0%(#D@$0%(#E@$0%(#F@$0%(#G@$0%(#H@$0%(#I@$0%(#J@$0%(#K@$0%(#L@$0%(#M@$0%(#O@$0%(#0@$04-.#1@$0%(#2@$0%(-#)3WXi9TBTi6T6Ti4T4@#2%--#1s90R0RU4WXiIS2TiFSFSiDSDS@#$%##c>'2#`@#.(*)ySPylc4@#$5/0%@1L@#>5/4"%pstring).
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Src2D.T_OPENERR_) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotSrc.ROT RotSrc.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_OPENERR_.

Module C_SWRET_4ab38_r8o4n0o7n1o1n6o3n2_s3_w0_e67bd0b67bd0.

Definition ROOT : sstate := (t_st T_Src2D.T_SWRET_4ab38_r8o4n0o7n1o1n6o3n2_s3_w0_e67bd0b67bd0).
Definition CUTS : IMap.t template := imap_of [(239%uint63, T_Src2D.T_EXIT_2_r8o4n0o7n1o1n6o3n2_s3_w0_e67bd0b67bd0)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Src2D.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "P1RPP2RPP3RPP4RPP5RPP6RPP7RPP8RPP9RPP:RPP;RPP<RPP=RPP>RPP?RPP@RPU?Wdj?Rj>Rj=Rj<Rj;Rj:Rj9Rj8Rj7Rj6Rj5Rj4Rj3Rj2Rj1Rj0Ri\\iZZiUXiPSylb0?KS4AKS8AKS<AKSDAKSDDKS46LS0BLS@MMXH>NX0<OX0FOX0@:Y82;YLA;Y8GNY8A0Z4<1Z"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Src2D.T_SWRET_4ab38_r8o4n0o7n1o1n6o3n2_s3_w0_e67bd0b67bd0) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotSrc.ROT RotSrc.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_SWRET_4ab38_r8o4n0o7n1o1n6o3n2_s3_w0_e67bd0b67bd0.

Module C_SWRET_4b164_r9o4n0o7n1o1n9o3n2_s566c8_w0_ev1_0x230bv1_0x230.

Definition ROOT : sstate := (t_st T_Src2D.T_SWRET_4b164_r9o4n0o7n1o1n9o3n2_s566c8_w0_ev1_0x230bv1_0x230).
Definition CUTS : IMap.t template := imap_of [(243%uint63, T_Src2D.T_SW_SWRET_4b164_r9o4n0o7n1o1n9o3n2_s566c8_w0_ev1_0x230bv1_0x230_1)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Src2D.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "UCWWi8RARi2R4Ri0R0Ri\\iZZiUXiPSylb0?KS4AKS8AKS<AKSDAKSDDKS46LS0BLS@MMXH>NX0<OX0FOX0@:Y82;YLA;Y8GNY8A0Z4<1Z"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Src2D.T_SWRET_4b164_r9o4n0o7n1o1n9o3n2_s566c8_w0_ev1_0x230bv1_0x230) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotSrc.ROT RotSrc.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_SWRET_4b164_r9o4n0o7n1o1n9o3n2_s566c8_w0_ev1_0x230bv1_0x230.

Module C_SWRET_4bb84_r9o4n0o7n1o1n9o3n2_s566c8_w0_ev1_0x230bv1_0x230.

Definition ROOT : sstate := (t_st T_Src2D.T_SWRET_4bb84_r9o4n0o7n1o1n9o3n2_s566c8_w0_ev1_0x230bv1_0x230).
Definition CUTS : IMap.t template := imap_of [(245%uint63, T_Src2D.T_SW_SWRET_4bb84_r9o4n0o7n1o1n9o3n2_s566c8_w0_ev1_0x230bv1_0x230_1)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Src2D.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Yb0?KS4AKS8AKS<AKSDAKSDDKS46LS0BLS@MMXH>NX0<OX0FOX0@:Y82;YLA;Y8GNY8A0Z4<1ZUEWXiIR1SiCRERi@R@Ri0R0Ri\\iZZiUXiPSySPk\QySPylQ4@:YySP"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Src2D.T_SWRET_4bb84_r9o4n0o7n1o1n9o3n2_s566c8_w0_ev1_0x230bv1_0x230) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotSrc.ROT RotSrc.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_SWRET_4bb84_r9o4n0o7n1o1n9o3n2_s566c8_w0_ev1_0x230bv1_0x230.

Module C_SWRET_4b164_r8o7n1o1n6o5n0o3n2_s566c8_w0_ev1_0x230bv1_0x230.

Definition ROOT : sstate := (t_st T_Src2D.T_SWRET_4b164_r8o7n1o1n6o5n0o3n2_s566c8_w0_ev1_0x230bv1_0x230).
Definition CUTS : IMap.t template := imap_of [(242%uint63, T_Src2D.T_SW_SWRET_4b164_r8o7n1o1n6o5n0o3n2_s566c8_w0_ev1_0x230bv1_0x230_1)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Src2D.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "UBWVi7RARi1R3Ri\\iZZiUXiPSylb0?KS4AKS8AKS<AKSDAKSDDKS46LS0BLS@MMXH>NX0<OX0FOX0@:Y82;YLA;Y8GNY8A0Z4<1Z"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Src2D.T_SWRET_4b164_r8o7n1o1n6o5n0o3n2_s566c8_w0_ev1_0x230bv1_0x230) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotSrc.ROT RotSrc.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_SWRET_4b164_r8o7n1o1n6o5n0o3n2_s566c8_w0_ev1_0x230bv1_0x230.

Module C_SWRET_4bb84_r8o7n1o1n6o5n0o3n2_s566c8_w0_ev1_0x230bv1_0x230.

Definition ROOT : sstate := (t_st T_Src2D.T_SWRET_4bb84_r8o7n1o1n6o5n0o3n2_s566c8_w0_ev1_0x230bv1_0x230).
Definition CUTS : IMap.t template := imap_of [(244%uint63, T_Src2D.T_SW_SWRET_4bb84_r8o7n1o1n6o5n0o3n2_s566c8_w0_ev1_0x230bv1_0x230_1)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Src2D.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Yb0?KS4AKS8AKS<AKSDAKSDDKS46LS0BLS@MMXH>NX0<OX0FOX0@:Y82;YLA;Y8GNY8A0Z4<1ZUDWXiIR1SiCRERiARARi?R?Ri\\iZZiUXiPSySPk\QySPylQ4@:YySP"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Src2D.T_SWRET_4bb84_r8o7n1o1n6o5n0o3n2_s566c8_w0_ev1_0x230bv1_0x230) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotSrc.ROT RotSrc.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_SWRET_4bb84_r8o7n1o1n6o5n0o3n2_s566c8_w0_ev1_0x230bv1_0x230.

Module C_EXIT_2_r8o4n0o7n1o1n6o3n2_s3_w0_e67bd0b67bd0.

Definition ROOT : sstate := (t_st T_Src2D.T_EXIT_2_r8o4n0o7n1o1n6o3n2_s3_w0_e67bd0b67bd0).
Definition CUTS : IMap.t template := imap_of [].
Definition ECALLS : IMap.t sstate := imap_of [(250%uint63, T_Src2D.E_EXIT_2_r8o4n0o7n1o1n6o3n2_s3_w0_e67bd0b67bd0_1)].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Src2D.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "wJWWi:R?Ri8R8Ri0R2Ri\\iZZiUXiPSylb0?KS4AKS8AKS<AKSDAKSDDKS46LS0BLS@MMXH>NX0<OX0FOX0@:Y82;YLA;Y8GNY8A0Z4<1ZylQL>NX"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Src2D.T_EXIT_2_r8o4n0o7n1o1n6o3n2_s3_w0_e67bd0b67bd0) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotSrc.ROT RotSrc.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_EXIT_2_r8o4n0o7n1o1n6o3n2_s3_w0_e67bd0b67bd0.

Module C_SWRET_4af94_r8o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63.

Definition ROOT : sstate := (t_st T_Src2D.T_SWRET_4af94_r8o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63).
Definition CUTS : IMap.t template := imap_of [(251%uint63, T_Src2D.T_EXIT_2_r8o7n1o1n6o5n0o3n2_s0_w0_e0b0_k63)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Src2D.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "P1RPP2RPP3RPP6RPP7RPP8RPP9RPP:RPP;RPP<RPP=RPP>RPP?RPP@RPPARPUKWcj>Rj=Rj<Rj;Rj:Rj9Rj8Rj7Rj6Rj5Rj4Rj3Rj2Rj1Rj0Ri\\iZZiUXiPSylb0?KS4AKS8AKS<AKSDAKSDDKS46LS0BLS@MMXH>NX0<OX0FOX0@:Y82;YLA;Y8GNY8A0Z4<1Z"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Src2D.T_SWRET_4af94_r8o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotSrc.ROT RotSrc.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_SWRET_4af94_r8o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63.

Module C_SWRET_4af94_r8o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230_ka.

Definition ROOT : sstate := (t_st T_Src2D.T_SWRET_4af94_r8o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230_ka).
Definition CUTS : IMap.t template := imap_of [(252%uint63, T_Src2D.T_EXIT_2_r8o7n1o1n6o5n0o3n2_s0_w0_e0b0_ka)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Src2D.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "P1RPP2RPP3RPP6RPP7RPP8RPP9RPP:RPP;RPP<RPP=RPP>RPP?RPP@RPPARPULWcj>Rj=Rj<Rj;Rj:Rj9Rj8Rj7Rj6Rj5Rj4Rj3Rj2Rj1Rj0Ri\\iZZiUXiPSylb0?KS4AKS8AKS<AKSDAKSDDKS46LS0BLS@MMXH>NX0<OX0FOX0@:Y82;YLA;Y8GNY8A0Z4<1Z"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Src2D.T_SWRET_4af94_r8o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230_ka) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotSrc.ROT RotSrc.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_SWRET_4af94_r8o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230_ka.

Module C_SWRET_4af94_r9o4n0o7n1o1n9o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63.

Definition ROOT : sstate := (t_st T_Src2D.T_SWRET_4af94_r9o4n0o7n1o1n9o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63).
Definition CUTS : IMap.t template := imap_of [(253%uint63, T_Src2D.T_EXIT_2_r9o4n0o7n1o1n9o3n2_s3_w0_e0b0_k63)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Src2D.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "P2RPP3RPP4RPP7RPP8RPP9RPP:RPP;RPP<RPP=RPP>RPP?RPP@RPPARPUMWcj>Rj=Rj<Rj;Rj:Rj9Rj8Rj7Rj6Rj5Rj4Rj3Rj2Rj1Ri0R0Ri\\iZZiUXiPSylb0?KS4AKS8AKS<AKSDAKSDDKS46LS0BLS@MMXH>NX0<OX0FOX0@:Y82;YLA;Y8GNY8A0Z4<1Z"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Src2D.T_SWRET_4af94_r9o4n0o7n1o1n9o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotSrc.ROT RotSrc.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_SWRET_4af94_r9o4n0o7n1o1n9o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63.

Module C_SWRET_4af94_r9o4n0o7n1o1n9o3n2_s67bd0_w0_ev1_0x230bv1_0x230_ka.

Definition ROOT : sstate := (t_st T_Src2D.T_SWRET_4af94_r9o4n0o7n1o1n9o3n2_s67bd0_w0_ev1_0x230bv1_0x230_ka).
Definition CUTS : IMap.t template := imap_of [(254%uint63, T_Src2D.T_EXIT_2_r9o4n0o7n1o1n9o3n2_s3_w0_e0b0_ka)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Src2D.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "P2RPP3RPP4RPP7RPP8RPP9RPP:RPP;RPP<RPP=RPP>RPP?RPP@RPPARPUNWcj>Rj=Rj<Rj;Rj:Rj9Rj8Rj7Rj6Rj5Rj4Rj3Rj2Rj1Ri0R0Ri\\iZZiUXiPSylb0?KS4AKS8AKS<AKSDAKSDDKS46LS0BLS@MMXH>NX0<OX0FOX0@:Y82;YLA;Y8GNY8A0Z4<1Z"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Src2D.T_SWRET_4af94_r9o4n0o7n1o1n9o3n2_s67bd0_w0_ev1_0x230bv1_0x230_ka) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotSrc.ROT RotSrc.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_SWRET_4af94_r9o4n0o7n1o1n9o3n2_s67bd0_w0_ev1_0x230bv1_0x230_ka.

Module C_EXIT_2_r8o7n1o1n6o5n0o3n2_s0_w0_e0b0_k63.

Definition ROOT : sstate := (t_st T_Src2D.T_EXIT_2_r8o7n1o1n6o5n0o3n2_s0_w0_e0b0_k63).
Definition CUTS : IMap.t template := imap_of [].
Definition ECALLS : IMap.t sstate := imap_of [(255%uint63, T_Src2D.E_EXIT_2_r8o7n1o1n6o5n0o3n2_s0_w0_e0b0_k63_1)].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Src2D.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "wOWWi8R=Ri6R6Ri0R2Ri\\iZZiUXiPSylb0?KS4AKS8AKS<AKSDAKSDDKS46LS0BLS@MMXH>NX0<OX0FOX0@:Y82;YLA;Y8GNY8A0Z4<1ZylQL>NX"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Src2D.T_EXIT_2_r8o7n1o1n6o5n0o3n2_s0_w0_e0b0_k63) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotSrc.ROT RotSrc.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_EXIT_2_r8o7n1o1n6o5n0o3n2_s0_w0_e0b0_k63.

Module C_EXIT_2_r8o7n1o1n6o5n0o3n2_s0_w0_e0b0_ka.

Definition ROOT : sstate := (t_st T_Src2D.T_EXIT_2_r8o7n1o1n6o5n0o3n2_s0_w0_e0b0_ka).
Definition CUTS : IMap.t template := imap_of [].
Definition ECALLS : IMap.t sstate := imap_of [(256%uint63, T_Src2D.E_EXIT_2_r8o7n1o1n6o5n0o3n2_s0_w0_e0b0_ka_1)].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Src2D.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "w0XWi8R=Ri6R6Ri0R2Ri\\iZZiUXiPSylb0?KS4AKS8AKS<AKSDAKSDDKS46LS0BLS@MMXH>NX0<OX0FOX0@:Y82;YLA;Y8GNY8A0Z4<1ZylQL>NX"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Src2D.T_EXIT_2_r8o7n1o1n6o5n0o3n2_s0_w0_e0b0_ka) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotSrc.ROT RotSrc.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_EXIT_2_r8o7n1o1n6o5n0o3n2_s0_w0_e0b0_ka.

Module C_EXIT_2_r9o4n0o7n1o1n9o3n2_s3_w0_e0b0_k63.

Definition ROOT : sstate := (t_st T_Src2D.T_EXIT_2_r9o4n0o7n1o1n9o3n2_s3_w0_e0b0_k63).
Definition CUTS : IMap.t template := imap_of [].
Definition ECALLS : IMap.t sstate := imap_of [(257%uint63, T_Src2D.E_EXIT_2_r9o4n0o7n1o1n9o3n2_s3_w0_e0b0_k63_1)].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Src2D.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "w1XWi9R>Ri7R7Ri0R3Ri\\iZZiUXiPSylb0?KS4AKS8AKS<AKSDAKSDDKS46LS0BLS@MMXH>NX0<OX0FOX0@:Y82;YLA;Y8GNY8A0Z4<1ZylQL>NX"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Src2D.T_EXIT_2_r9o4n0o7n1o1n9o3n2_s3_w0_e0b0_k63) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotSrc.ROT RotSrc.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_EXIT_2_r9o4n0o7n1o1n9o3n2_s3_w0_e0b0_k63.

Module C_EXIT_2_r9o4n0o7n1o1n9o3n2_s3_w0_e0b0_ka.

Definition ROOT : sstate := (t_st T_Src2D.T_EXIT_2_r9o4n0o7n1o1n9o3n2_s3_w0_e0b0_ka).
Definition CUTS : IMap.t template := imap_of [].
Definition ECALLS : IMap.t sstate := imap_of [(258%uint63, T_Src2D.E_EXIT_2_r9o4n0o7n1o1n9o3n2_s3_w0_e0b0_ka_1)].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Src2D.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "w2XWi9R>Ri7R7Ri0R3Ri\\iZZiUXiPSylb0?KS4AKS8AKS<AKSDAKSDDKS46LS0BLS@MMXH>NX0<OX0FOX0@:Y82;YLA;Y8GNY8A0Z4<1ZylQL>NX"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Src2D.T_EXIT_2_r9o4n0o7n1o1n9o3n2_s3_w0_e0b0_ka) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotSrc.ROT RotSrc.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_EXIT_2_r9o4n0o7n1o1n9o3n2_s3_w0_e0b0_ka.
