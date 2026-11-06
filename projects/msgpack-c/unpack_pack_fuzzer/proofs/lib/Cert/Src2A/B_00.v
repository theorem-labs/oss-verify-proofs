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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2A Require Import T_Src2A.
Module C_DRV.

Definition ROOT : sstate := T_Src2A.T_DRV2.
Definition CUTS : IMap.t template := imap_of [(100%uint63, T_Src2A.T_OPENERR_)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Src2A.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Yb0?KS4AKS8AKS<AKSDAKSDDKS46LS0BLS@MMXH>NX0<OX0FOX0@:Y82;YLA;Y8GNY8A0Z4<1ZU4SUi0R0Ri\\iZZiUXiPSySPkjQySP"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN T_Src2A.T_DRV2 = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotSrc.ROT RotSrc.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_DRV.

Module C_OPENERR_.

Definition ROOT : sstate := (t_st T_Src2A.T_OPENERR_).
Definition CUTS : IMap.t template := imap_of [(101%uint63, T_Src2A.T_SW_OPENERR__1); (102%uint63, T_Src2A.T_SW_OPENERR__10); (103%uint63, T_Src2A.T_SW_OPENERR__11); (104%uint63, T_Src2A.T_SW_OPENERR__12); (105%uint63, T_Src2A.T_SW_OPENERR__13); (106%uint63, T_Src2A.T_SW_OPENERR__14); (107%uint63, T_Src2A.T_SW_OPENERR__15); (108%uint63, T_Src2A.T_SW_OPENERR__16); (109%uint63, T_Src2A.T_SW_OPENERR__17); (110%uint63, T_Src2A.T_SW_OPENERR__18); (111%uint63, T_Src2A.T_SW_OPENERR__19); (112%uint63, T_Src2A.T_SW_OPENERR__2); (113%uint63, T_Src2A.T_SW_OPENERR__20); (114%uint63, T_Src2A.T_SW_OPENERR__21); (115%uint63, T_Src2A.T_SW_OPENERR__22); (116%uint63, T_Src2A.T_SW_OPENERR__23); (117%uint63, T_Src2A.T_SW_OPENERR__24); (118%uint63, T_Src2A.T_SW_OPENERR__25); (119%uint63, T_Src2A.T_SW_OPENERR__26); (120%uint63, T_Src2A.T_SW_OPENERR__27); (121%uint63, T_Src2A.T_SW_OPENERR__28); (122%uint63, T_Src2A.T_SW_OPENERR__29); (123%uint63, T_Src2A.T_SW_OPENERR__3); (124%uint63, T_Src2A.T_SW_OPENERR__30); (125%uint63, T_Src2A.T_SW_OPENERR__31); (126%uint63, T_Src2A.T_SW_OPENERR__32); (127%uint63, T_Src2A.T_SW_OPENERR__33); (128%uint63, T_Src2A.T_SW_OPENERR__34); (129%uint63, T_Src2A.T_SW_OPENERR__35); (130%uint63, T_Src2A.T_SW_OPENERR__36); (131%uint63, T_Src2A.T_SW_OPENERR__37); (132%uint63, T_Src2A.T_SW_OPENERR__38); (133%uint63, T_Src2A.T_SW_OPENERR__39); (134%uint63, T_Src2A.T_SW_OPENERR__4); (135%uint63, T_Src2A.T_SW_OPENERR__40); (136%uint63, T_Src2A.T_SW_OPENERR__41); (137%uint63, T_Src2A.T_SW_OPENERR__42); (138%uint63, T_Src2A.T_SW_OPENERR__43); (139%uint63, T_Src2A.T_SW_OPENERR__44); (140%uint63, T_Src2A.T_SW_OPENERR__45); (141%uint63, T_Src2A.T_SW_OPENERR__46); (142%uint63, T_Src2A.T_SW_OPENERR__47); (143%uint63, T_Src2A.T_SW_OPENERR__48); (144%uint63, T_Src2A.T_SW_OPENERR__49); (145%uint63, T_Src2A.T_SW_OPENERR__5); (146%uint63, T_Src2A.T_SW_OPENERR__50); (147%uint63, T_Src2A.T_SW_OPENERR__51); (148%uint63, T_Src2A.T_SW_OPENERR__52); (149%uint63, T_Src2A.T_SW_OPENERR__53); (150%uint63, T_Src2A.T_SW_OPENERR__54); (151%uint63, T_Src2A.T_SW_OPENERR__55); (152%uint63, T_Src2A.T_SW_OPENERR__56); (153%uint63, T_Src2A.T_SW_OPENERR__57); (154%uint63, T_Src2A.T_SW_OPENERR__58); (155%uint63, T_Src2A.T_SW_OPENERR__59); (156%uint63, T_Src2A.T_SW_OPENERR__6); (157%uint63, T_Src2A.T_SW_OPENERR__60); (158%uint63, T_Src2A.T_SW_OPENERR__61); (159%uint63, T_Src2A.T_SW_OPENERR__62); (160%uint63, T_Src2A.T_SW_OPENERR__63); (161%uint63, T_Src2A.T_SW_OPENERR__64); (162%uint63, T_Src2A.T_SW_OPENERR__65); (163%uint63, T_Src2A.T_SW_OPENERR__7); (164%uint63, T_Src2A.T_SW_OPENERR__8); (165%uint63, T_Src2A.T_SW_OPENERR__9)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Src2A.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan (StrLz.lz_dec "-&:Yb0?KS4AKS8AKS<AKSDAKSDDKS46LS0BLS@MMXH>NX0<OX0FOX0@:Y82;YLA;Y8GNY8A0Z4<1ZU5SWiHT0UiBTDTi0R0Ri\\iZZiUXiPSkcQySPk\QySPylQ4@:Y:#2$U@@$0%(#K@$0%($6T@$/%(#A@$0%(#L@$0%($3U@$/%(#4@$0%(#5@$0%(#6@$01$.#7@$0%(#8@$0%(#9@$0%(#:@$0%(#;@$0%(#<@$0%(#=@$0%(#>@$0%(#?@$0%(#A@$0%(#B@$0%(#C@$0%(#D@$0%(#E@$0%(#F@$0%(#G@$0%(#H@$0%(#I@$0%(#J@$0%(#L@$0%(#M@$0%(#N@$0%(#O@$0%(#0@$0244#1@$0%(#2@$128@@$0%(#4@$0%(#5@$0%(#7@$0%(#8@$0%(#9@$0%(#:@$0%(#;@$0%(#<@$0%(#=@$0%(#>@$0%(#?@$0%(#@@$0%(#B@$0%(#C@$0%(#D@$0%(#E@$0%(#F@$0%(#G@$0%(#H@$0%(#I@$0%(#J@$0%(#K@$0%(#M@$0%(#N@$0%(#O@$0%(#0@$041:-#)1UXi7T@Ti4T4Ti2T2@#2%--#1s90R0RU2UXiGS0TiDSDSiBSBS@#$%##c>'2#`@#.(*)ySPylc4@#$5/0%@1L@#>5/4"%pstring).
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Src2A.T_OPENERR_) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotSrc.ROT RotSrc.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_OPENERR_.

Module C_SWRET_4b164_r8o7n1o1n6o5n0o3n2_s566c8_w0_ev1_0x230bv1_0x230.

Definition ROOT : sstate := (t_st T_Src2A.T_SWRET_4b164_r8o7n1o1n6o5n0o3n2_s566c8_w0_ev1_0x230bv1_0x230).
Definition CUTS : IMap.t template := imap_of [(170%uint63, T_Src2A.T_SW_SWRET_4b164_r8o7n1o1n6o5n0o3n2_s566c8_w0_ev1_0x230bv1_0x230_1)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Src2A.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "U:UVi7R@Ri1R3Ri\\iZZiUXiPSylb0?KS4AKS8AKS<AKSDAKSDDKS46LS0BLS@MMXH>NX0<OX0FOX0@:Y82;YLA;Y8GNY8A0Z4<1Z"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Src2A.T_SWRET_4b164_r8o7n1o1n6o5n0o3n2_s566c8_w0_ev1_0x230bv1_0x230) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotSrc.ROT RotSrc.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_SWRET_4b164_r8o7n1o1n6o5n0o3n2_s566c8_w0_ev1_0x230bv1_0x230.

Module C_SWRET_4bb84_r8o7n1o1n6o5n0o3n2_s566c8_w0_ev1_0x230bv1_0x230.

Definition ROOT : sstate := (t_st T_Src2A.T_SWRET_4bb84_r8o7n1o1n6o5n0o3n2_s566c8_w0_ev1_0x230bv1_0x230).
Definition CUTS : IMap.t template := imap_of [(171%uint63, T_Src2A.T_SW_SWRET_4bb84_r8o7n1o1n6o5n0o3n2_s566c8_w0_ev1_0x230bv1_0x230_1)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Src2A.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "Yb0?KS4AKS8AKS<AKSDAKSDDKS46LS0BLS@MMXH>NX0<OX0FOX0@:Y82;YLA;Y8GNY8A0Z4<1ZU;UWiHR0SiBRDRi?R?Ri\\iZZiUXiPSySPk\QySPylQ4@:YySP"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Src2A.T_SWRET_4bb84_r8o7n1o1n6o5n0o3n2_s566c8_w0_ev1_0x230bv1_0x230) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotSrc.ROT RotSrc.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_SWRET_4bb84_r8o7n1o1n6o5n0o3n2_s566c8_w0_ev1_0x230bv1_0x230.

Module C_SWRET_4af94_r8o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63.

Definition ROOT : sstate := (t_st T_Src2A.T_SWRET_4af94_r8o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63).
Definition CUTS : IMap.t template := imap_of [(174%uint63, T_Src2A.T_EXIT_2_r8o7n1o1n6o5n0o3n2_s0_w0_e0b0_k63)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Src2A.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "P1RPP2RPP3RPP6RPP7RPP8RPP9RPP:RPP;RPP<RPP=RPP>RPP?RPP@RPU>Ubj=Rj<Rj;Rj:Rj9Rj8Rj7Rj6Rj5Rj4Rj3Rj2Rj1Rj0Ri\\iZZiUXiPSylb0?KS4AKS8AKS<AKSDAKSDDKS46LS0BLS@MMXH>NX0<OX0FOX0@:Y82;YLA;Y8GNY8A0Z4<1Z"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Src2A.T_SWRET_4af94_r8o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotSrc.ROT RotSrc.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_SWRET_4af94_r8o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63.

Module C_SWRET_4af94_r8o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230_ka.

Definition ROOT : sstate := (t_st T_Src2A.T_SWRET_4af94_r8o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230_ka).
Definition CUTS : IMap.t template := imap_of [(175%uint63, T_Src2A.T_EXIT_2_r8o7n1o1n6o5n0o3n2_s0_w0_e0b0_ka)].
Definition ECALLS : IMap.t sstate := imap_of [].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Src2A.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "P1RPP2RPP3RPP6RPP7RPP8RPP9RPP:RPP;RPP<RPP=RPP>RPP?RPP@RPU?Ubj=Rj<Rj;Rj:Rj9Rj8Rj7Rj6Rj5Rj4Rj3Rj2Rj1Rj0Ri\\iZZiUXiPSylb0?KS4AKS8AKS<AKSDAKSDDKS46LS0BLS@MMXH>NX0<OX0FOX0@:Y82;YLA;Y8GNY8A0Z4<1Z"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Src2A.T_SWRET_4af94_r8o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230_ka) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotSrc.ROT RotSrc.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_SWRET_4af94_r8o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230_ka.

Module C_EXIT_2_r8o7n1o1n6o5n0o3n2_s0_w0_e0b0_k63.

Definition ROOT : sstate := (t_st T_Src2A.T_EXIT_2_r8o7n1o1n6o5n0o3n2_s0_w0_e0b0_k63).
Definition CUTS : IMap.t template := imap_of [].
Definition ECALLS : IMap.t sstate := imap_of [(176%uint63, T_Src2A.E_EXIT_2_r8o7n1o1n6o5n0o3n2_s0_w0_e0b0_k63_1)].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Src2A.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "w@UWi8R=Ri6R6Ri0R2Ri\\iZZiUXiPSylb0?KS4AKS8AKS<AKSDAKSDDKS46LS0BLS@MMXH>NX0<OX0FOX0@:Y82;YLA;Y8GNY8A0Z4<1ZylQL>NX"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Src2A.T_EXIT_2_r8o7n1o1n6o5n0o3n2_s0_w0_e0b0_k63) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotSrc.ROT RotSrc.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_EXIT_2_r8o7n1o1n6o5n0o3n2_s0_w0_e0b0_k63.

Module C_EXIT_2_r8o7n1o1n6o5n0o3n2_s0_w0_e0b0_ka.

Definition ROOT : sstate := (t_st T_Src2A.T_EXIT_2_r8o7n1o1n6o5n0o3n2_s0_w0_e0b0_ka).
Definition CUTS : IMap.t template := imap_of [].
Definition ECALLS : IMap.t sstate := imap_of [(177%uint63, T_Src2A.E_EXIT_2_r8o7n1o1n6o5n0o3n2_s0_w0_e0b0_ka_1)].
Definition MROOT : sv := (VL (wp 0%uint63)).
Definition CTX : ctx := Ctx ITAB CUTS ECALLS T_Src2A.CONTRACTS MROOT.
Definition PLAN : plan := PlanDec.dec_plan "wAUWi8R=Ri6R6Ri0R2Ri\\iZZiUXiPSylb0?KS4AKS8AKS<AKSDAKSDDKS46LS0BLS@MMXH>NX0<OX0FOX0@:Y82;YLA;Y8GNY8A0Z4<1ZylQL>NX"%pstring.
Definition OBLS : list obligation := [].

Lemma WF : ctx_wfb CTX = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma CHK : check SEGS CTX PLAN (t_st T_Src2A.T_EXIT_2_r8o7n1o1n6o5n0o3n2_s0_w0_e0b0_ka) = Some OBLS.
Proof. rewrite (Rot.Rot.check_r_eq SEGS RotSrc.ROT RotSrc.ROT_ok). vm_cast_no_check (eq_refl (Some OBLS)). Qed.

End C_EXIT_2_r8o7n1o1n6o5n0o3n2_s0_w0_e0b0_ka.
