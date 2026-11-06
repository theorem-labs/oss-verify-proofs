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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.UbsNU Require Import T_UbsNU.
Module C_DRV.

Definition ROOT : sstate := T_UbsNU.T_DRVN.
Definition CUTS : IMap.t template := imap_of [(100%uint63, T_UbsNU.T_SW_DRV_1); (101%uint63, T_UbsNU.T_SW_DRV_10); (102%uint63, T_UbsNU.T_SW_DRV_11); (103%uint63, T_UbsNU.T_SW_DRV_12); (104%uint63, T_UbsNU.T_SW_DRV_13); (105%uint63, T_UbsNU.T_SW_DRV_14); (106%uint63, T_UbsNU.T_SW_DRV_15); (107%uint63, T_UbsNU.T_SW_DRV_16); (108%uint63, T_UbsNU.T_SW_DRV_17); (109%uint63, T_UbsNU.T_SW_DRV_18); (110%uint63, T_UbsNU.T_SW_DRV_19); (111%uint63, T_UbsNU.T_SW_DRV_2); (112%uint63, T_UbsNU.T_SW_DRV_20); (113%uint63, T_UbsNU.T_SW_DRV_21); (114%uint63, T_UbsNU.T_SW_DRV_22); (115%uint63, T_UbsNU.T_SW_DRV_23); (116%uint63, T_UbsNU.T_SW_DRV_24); (117%uint63, T_UbsNU.T_SW_DRV_25); (118%uint63, T_UbsNU.T_SW_DRV_26); (119%uint63, T_UbsNU.T_SW_DRV_27); (120%uint63, T_UbsNU.T_SW_DRV_28); (121%uint63, T_UbsNU.T_SW_DRV_29); (122%uint63, T_UbsNU.T_SW_DRV_3); (123%uint63, T_UbsNU.T_SW_DRV_30); (124%uint63, T_UbsNU.T_SW_DRV_31); (125%uint63, T_UbsNU.T_SW_DRV_32); (126%uint63, T_UbsNU.T_SW_DRV_33); (127%uint63, T_UbsNU.T_SW_DRV_34); (128%uint63, T_UbsNU.T_SW_DRV_35); (129%uint63, T_UbsNU.T_SW_DRV_36); (130%uint63, T_UbsNU.T_SW_DRV_37); (131%uint63, T_UbsNU.T_SW_DRV_38); (132%uint63, T_UbsNU.T_SW_DRV_39); (133%uint63, T_UbsNU.T_SW_DRV_4); (134%uint63, T_UbsNU.T_SW_DRV_40); (135%uint63, T_UbsNU.T_SW_DRV_41); (136%uint63, T_UbsNU.T_SW_DRV_42); (137%uint63, T_UbsNU.T_SW_DRV_43); (138%uint63, T_UbsNU.T_SW_DRV_44); (139%uint63, T_UbsNU.T_SW_DRV_45); (140%uint63, T_UbsNU.T_SW_DRV_46); (141%uint63, T_UbsNU.T_SW_DRV_47); (142%uint63, T_UbsNU.T_SW_DRV_48); (143%uint63, T_UbsNU.T_SW_DRV_49); (144%uint63, T_UbsNU.T_SW_DRV_5); (145%uint63, T_UbsNU.T_SW_DRV_50); (146%uint63, T_UbsNU.T_SW_DRV_51); (147%uint63, T_UbsNU.T_SW_DRV_52); (148%uint63, T_UbsNU.T_SW_DRV_53); (149%uint63, T_UbsNU.T_SW_DRV_54); (150%uint63, T_UbsNU.T_SW_DRV_55); (151%uint63, T_UbsNU.T_SW_DRV_56); (152%uint63, T_UbsNU.T_SW_DRV_57); (153%uint63, T_UbsNU.T_SW_DRV_58); (154%uint63, T_UbsNU.T_SW_DRV_59); (155%uint63, T_UbsNU.T_SW_DRV_6); (156%uint63, T_UbsNU.T_SW_DRV_60); (157%uint63, T_UbsNU.T_SW_DRV_61); (158%uint63, T_UbsNU.T_SW_DRV_62); (159%uint63, T_UbsNU.T_SW_DRV_63); (160%uint63, T_UbsNU.T_SW_DRV_64); (161%uint63, T_UbsNU.T_SW_DRV_65); (162%uint63, T_UbsNU.T_SW_DRV_66); (163%uint63, T_UbsNU.T_SW_DRV_67); (164%uint63, T_UbsNU.T_SW_DRV_68); (165%uint63, T_UbsNU.T_SW_DRV_69); (166%uint63, T_UbsNU.T_SW_DRV_7); (167%uint63, T_UbsNU.T_SW_DRV_70); (168%uint63, T_UbsNU.T_SW_DRV_71); (169%uint63, T_UbsNU.T_SW_DRV_72); (170%uint63, T_UbsNU.T_SW_DRV_73); (171%uint63, T_UbsNU.T_SW_DRV_74); (172%uint63, T_UbsNU.T_SW_DRV_75); (173%uint63, T_UbsNU.T_SW_DRV_8); (174%uint63, T_UbsNU.T_SW_DRV_9)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_UbsNU.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan (StrLz.lz_dec "-&4Yb0NLS40MS80MS<0MSD0MSD3MS4EMS01NSDM3YL>4Y4<5Y4F5Y4@@Y<2AY0BAY<G4Z<A6Z8<7ZU4SUiHT0UiBTDTi0R0Ri\\iPXkcQySPk\QySPylQ8@@Y:#2$U?@$*$@#J@$*$@$5T@$)$@#@@$*$@#K@$*$@$6U@$)$@#=@$*$@#>@$*$@#5@$*0@#6@$*$@#7@$*$@#8@$*$@#9@$*$@#:@$*$@#;@$*$@#<@$*$@#=@$*$@#>@$*$@#@@$*$@#A@$*$@#B@$*$@#C@$*$@#D@$*$@#E@$*$@#F@$*$@#G@$*$@#H@$*$@#I@$*$@#K@$*$@#L@$*$@#M@$*$@#N@$*$@#O@$*$@#0@$*20@#1@$*$@#2@$*$@#3@$*$@#4@$+28@@$*$@#7@$*$@#8@$*$@#9@$*$@#:@$*$@#;@$*$@#<@$*$@#=@$*$@#>@$*$@#?@$*$@#A@$*$@#B@$*$@#C@$*$@#D@$*$@#E@$*$@#F@$*$@#G@$*$@#H@$*$@#I@$*$@#J@$*$@#L@$*$@#M@$*$@#N@$*$@#O@$*$@#0@$*4(@#1@$*$@#2@$*$@#3@$*$@-#)4UVi7T@Ti4T4Ti2T2@#,%'$U5@#=$5#7@#=$5#8@#=$5#9@#=$5#:@#=$5#;@#<$5-#1s9:R:RU<UViGS0TiDSDSiBSBS;$;#c>0>#`@#.1#6%ySP"%pstring).
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN T_UbsNU.T_DRVN = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_DRV.

Module C_SWRET_4c7a8_r7o7n1o1n6o5n0o3n2_s693e0_w0_ev1_0x230bv1_0x230.

Definition ROOT : sstate := (t_st T_UbsNU.T_SWRET_4c7a8_r7o7n1o1n6o5n0o3n2_s693e0_w0_ev1_0x230bv1_0x230).
Definition CUTS : IMap.t template := imap_of [(178%uint63, T_UbsNU.T_EXIT_2_r7o7n1o1n6o5n0o3n2_s0_w0_e0b0)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_UbsNU.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "P1RPP2RPP3RPP6RPP7RPP8RPP9RPP:RPP;RPP<RPP=RPP>RPP?RPP@RPUBU`j=Rj<Rj;Rj:Rj9Rj8Rj7Rj6Rj5Rj4Rj3Rj2Rj1Rj0Ri\\iPXylb0NLS40MS80MS<0MSD0MSD3MS4EMS01NSDM3YL>4Y4<5Y4F5Y4@@Y<2AY0BAY<G4Z<A6Z8<7Z"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_UbsNU.T_SWRET_4c7a8_r7o7n1o1n6o5n0o3n2_s693e0_w0_ev1_0x230bv1_0x230) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_SWRET_4c7a8_r7o7n1o1n6o5n0o3n2_s693e0_w0_ev1_0x230bv1_0x230.

Module C_SWRET_4c978_r7o7n1o1n6o5n0o3n2_s57ed8_w0_ev1_0x230bv1_0x230.

Definition ROOT : sstate := (t_st T_UbsNU.T_SWRET_4c978_r7o7n1o1n6o5n0o3n2_s57ed8_w0_ev1_0x230bv1_0x230).
Definition CUTS : IMap.t template := imap_of [(179%uint63, T_UbsNU.T_SW_SWRET_4c978_r7o7n1o1n6o5n0o3n2_s57ed8_w0_ev1_0x230bv1_0x230_1)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_UbsNU.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "UCUTi7R@Ri1R3Ri\\iPXylb0NLS40MS80MS<0MSD0MSD3MS4EMS01NSDM3YL>4Y4<5Y4F5Y4@@Y<2AY0BAY<G4Z<A6Z8<7Z"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_UbsNU.T_SWRET_4c978_r7o7n1o1n6o5n0o3n2_s57ed8_w0_ev1_0x230bv1_0x230) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_SWRET_4c978_r7o7n1o1n6o5n0o3n2_s57ed8_w0_ev1_0x230bv1_0x230.

Module C_SWRET_4d398_r7o7n1o1n6o5n0o3n2_s57ed8_w0_ev1_0x230bv1_0x230.

Definition ROOT : sstate := (t_st T_UbsNU.T_SWRET_4d398_r7o7n1o1n6o5n0o3n2_s57ed8_w0_ev1_0x230bv1_0x230).
Definition CUTS : IMap.t template := imap_of [(180%uint63, T_UbsNU.T_SW_SWRET_4d398_r7o7n1o1n6o5n0o3n2_s57ed8_w0_ev1_0x230bv1_0x230_1)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_UbsNU.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Yb0NLS40MS80MS<0MSD0MSD3MS4EMS01NSDM3YL>4Y4<5Y4F5Y4@@Y<2AY0BAY<G4Z<A6Z8<7ZUDUUiHR0SiBRDRi?R?Ri\\iPXySPk\QySPylQ8@@YySP"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_UbsNU.T_SWRET_4d398_r7o7n1o1n6o5n0o3n2_s57ed8_w0_ev1_0x230bv1_0x230) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_SWRET_4d398_r7o7n1o1n6o5n0o3n2_s57ed8_w0_ev1_0x230bv1_0x230.

Module C_EXIT_2_r7o7n1o1n6o5n0o3n2_s0_w0_e0b0.

Definition ROOT : sstate := (t_st T_UbsNU.T_EXIT_2_r7o7n1o1n6o5n0o3n2_s0_w0_e0b0).
Definition CUTS : IMap.t template := imap_of [].
Definition ECALLS : IMap.t sstate := imap_of [(181%uint63, T_UbsNU.E_EXIT_2_r7o7n1o1n6o5n0o3n2_s0_w0_e0b0_1)].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_UbsNU.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "wEUUi8R=Ri6R6Ri0R2Ri\\iPXylb0NLS40MS80MS<0MSD0MSD3MS4EMS01NSDM3YL>4Y4<5Y4F5Y4@@Y<2AY0BAY<G4Z<A6Z8<7ZylQ0?4Y"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_UbsNU.T_EXIT_2_r7o7n1o1n6o5n0o3n2_s0_w0_e0b0) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotUbs.ROT RotUbs.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_EXIT_2_r7o7n1o1n6o5n0o3n2_s0_w0_e0b0.
