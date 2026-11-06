(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith List PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Mem Instr State Step Plan Notation.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Img Require Import ImgAsan ItabAsan RotAsan.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import Rot.
Import ListNotations W64 Val Mem FI St Step Plan.
From Stdlib Require Import PrimString.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require PlanDec.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require StrLz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib DefsA DefsM Defs DefsB.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib DefsA DefsM Defs DefsB.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.EH Require Import Pool.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Actr.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import ActrB FaC RangeC StrRegC ReadC MemsetC MemcpyC Memcpy0C PubC MemcpyPC MemsetPC RstageC BlobC PayloadC HalfC VprintfC FprintfC FprintfSC StrnlenC FwriteC FwritePostC UnreggC.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import GRealign.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import GTwinSub CaseF.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import GshC.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import StrlenC.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import OpDropC.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import RoLitA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import AmallocNnC.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import ReadDirC.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import RoLit.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import GViewDrop2.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import GUnrealign.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import ShLoadLit.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import GBgNone.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.AsanU Require UnivAsan.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import GFmv.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import PkMid.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import PkLoad2.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import PkFld2.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import OpShLoad.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.PkA Require Import PkRegrowAC.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.PkA Require Import PkBodyAC.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Ops GLib GUnp GWin G2 G2Z G2B G3 G3P G4 GRoom G1 G0 G6 GCap GNz GShr GCur GBnd VDestroy GSplit GName GVEnd GInv TdEnter Td PkOps PkEnter PkExit PkStack PkPeek PkFld PkBody PkRegrow PkCap PkInv G0A G1A G3PA G4A G6A GInvA GWinA GBndA GMid GNarrow GNameA GPerm GTwinViewC GVecHi GViewDrop2 GSeal GPotHR Pot GPot GPotInit GPotName OpShLoadU GGran GGranP GChk GBgNone GExcl GRoomA GAncA GCnt GCurA PkShrink.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import SinkC.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.UnpA Require Import G6RegrowAC GCapB GTwinBnd GVEndA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Asan2F Require Import T_Asan2F.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Asan2L Require Import T_Asan2L.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Asan2U Require Import T_Asan2U.

Module C_PKPOP_e_m0k0uNp_kw0019197819078781996.
Definition CUTL := (cons (pair 137%uint63 T_ZLOOP_w10_r21_pv_L0) (cons (pair 1009%uint63 T_PKHEAD_m1k0uFpw_kw0019197819078781996) (cons (pair 1010%uint63 T_PKPOP_e_m0k0uNp_kw0019197819078781996) (cons (pair 1019%uint63 T_PKHEAD_m0k0uFpw_kw0019197819078781996) (cons (pair 1021%uint63 T_PKHEAD_m1k1uFpw_kw0019197819078781996) (cons (pair 1028%uint63 T_PKPOP_e_m1k0uNp_kw0019197819078781996) (nil))))))).
Definition CTX := mkctx CUTL EC0 (t_measure T_PKPOP_e_m0k0uNp_kw0019197819078781996).
Definition PLAN := PL "-@@YK_0L>W4M>W@H0Y441YD@1Y@B7Z40C[05D[0GD[@DF[D0I[H0I[L0I[01I[LC1\8?G\44Ba84Ba45Ba85Ba06Ba46BaH8BaL8BaD9BaH9BaD:BaH:BaL;Ba0<BaD<BaH<Ba4DBa<GBa0NBa@NBaDNBaHNBaLNBa@<Ca4ACaHDCa0KCa4KCa4MCaLNCa0OCaD3DaL4Da05Da45Da85Da40EaHAEaLGEa0HEa<IEa@IEa@NEaDNEa@0FaD0FaL1Fa42Fa85Fa<5Fa@>Fa8?Fa<?Fa@?FaD?Fa0IFa80GaH9Ga0=Ga4=GaLEGa0FGa<HGaDJGaD0HaH0HaH@HaL@HaHEHaLEHa0HHaHJHaLJHa8MHa4OHaL:Ia0;IaD?Ia4@Ia8@Ia4CIaDEIaHEIaDOIa@1JaD1Ja@8JaD8Ja<AJa@AJaLCJa4FJa4LJa8LJaH4KaL4KaH9KaL9Ka0<Ka<>Ka@>Ka8GKa<GKa8JKa0LKa0NKa4NKaH4LaD5La09La0:LaH>LaH?LaLELa8HLa@JLaHKLa0MLa@MLaL3MaD4Ma49Ma8:Ma<<Ma4=MaH@Ma8BMa8IMa0JMa<KMa@NMaHOMaL1Na@2Na46Na07NaD;Na8<Na@?Na4@NaDCNa4JNa8LNa0MNaDMNa41Oa@2Oa@9Oa4:OaH;OaL=Oa@>OaHAOa@COa4DOaHGOa0IOa4KOaHKOa400b010b440bH40b490b0:0b4<0b4?0b4@0b8C0bLC0bHG0b<H0bLJ0bD71b<81b8<1b0=1bL@1bD95bH95bLD5b0E5b<H5b846b056bL66bH76b@86b0=6bL@6b0A6b8G6b<G6bHG6bLK6bL07bL=7b0>7b<>7bDB7bDG7bH48b088b488b@;8b4J8b0K8bHK8b<09b<49b@49-@@b8;9b<;9bH>9b8M9b4N9bLN9b<3:b87:b<7:bL=:b0>:b<>:b4?:bDC:bDI:b08;b48;b@8;b89;b@>;b@C;b@1<bD1<b02<bH2<b<7<b<=<bHK<bLK<b8L<b0M<b<2=b<7=bDC=b4E=b8E=bDG=b40>b<0>b03>b89>b<@>b@@>bDE>bHE>bLF>bDJ>b@K>bDN>b4O>b<5?bH5?b89?bL:?b@=?bD=?b4C?b8C?b0F?b4F?b4L?b8L?bDN?bLN?b@0@bH4@bH;@bL<@b0=@b<?@b4C@b@4AbD4AbL:Ab0;Ab4<AbL?AbH@AbLCAb<DAb<JAbHJAb@NAb40BbH2BbL2Bb88Bb<8Bb@<BbD<BbH@BbL@Bb0EBb4EBb0LBb4LBb<5CbL5Cb06Cb46Cb86CbL=Cb4ACb8HCb@LCb0MCb4MCb8MCb<MCb<7DbD7DbH7DbD;Db8<Db0ADbDADbLADb0BDb4CDbHCDbDDDb8EDb4FDb<FDbLGDb@HDbDHDbLHDbHJDbLKDb4LDb4MDbHMDbLMDb4NDb4ODbHODbLODb40Eb81Eb42Eb<6EbD6Eb48EbH8EbL8Eb49Eb4;Eb<;Eb@;EbD<Eb0=Eb8>Eb<@EbH@Eb<MEbH>Fb8?Fb<?Fb@?FbD?FbHJFb<0Gb01Gb41Gb81Gb<1GbDFGbLNGb@OGbDOGbHOGbLOGb@BHbLHHb0IHb4JHb@JHbH0Ib81Ib<1Ib@1IbD1IbDBIb0IIb@IIbDIIbHIIbLIIbL:JbHBJbLBJbLNJb0OJb@7KbD7Kb<;Kb4>Kb8>Kb@AKb0BKb4BKb8BKb<BKbH;Lb8CLbHCLbLCLb0DLb4DLb4LMb86NbL6Nb07Nb47Nb87NbL6Ob4?Ob8?Ob8AObDAOb@BObHBObHIObDMObHMOb430c8-.(30c490c890cL;0c8D0c<D0cLN0c0O0cL31c041c4:1c8:1c4E1c8E1c8F1cLI1cLK1c<CAf<DAf0>Cf4ICf@JGf04Hf@4Hf<KHfLKHfHIKf@JKf02LfH2LfH3Lf<4LfH<Lf8BLf0HLfDNLfDOOf@10g4:0g8=4g@>4g<?Fg@?FgH?FgH5GgD>Gg@BGg8M;h<M>h88?h@G?hH1CiL1CiP4YhPHXPA1ZPHXPPIXPA0ZLHIBbPM[PPN[PPO[PPJUPPFXPP1\PP2\PP3\PP4\PP5\PP6\PP7\PP8\PP9\PP:\PP:XPP;XPP?XPP@XPPAXPPBXPPHWPPCXPLAWLBWLCWPDXPPEX0&%-)$NXPPIYPU9T>QjCXjBXjAXj@Xj?Xj>Xj=Xj<Xj;Xj:Xj9Xj8Xj7Xj6Xj5Xj4Xj3Xj2Xj1Xj0XjOWjNWjMWjLWjKWjJWjIWjHWjGWjFWjEWjDWi1W2WiNVNVi=V>ViIUMUi3UGUiET1Ui?T@Ti0T5Ti0R1Riddi\\iZZiUXiPSySPk<<E@A]QySPk4C>26]Qk00#*'ySPkD1#)*>;36]Qk@0#*(ySPkA\0#<&92C@7#4#30#0+@AI36]Qk<0#*5#<+HEH36]QkD0#*(ySPkHL0$1#D0#*-#4ySPylQ0>CbPHXPb4YkHRQySPkLE41&6-&*P4YPP9YPP:YPP;YPPHXPP=YPP>YPP?YPP@YPPAYPPBYPPCYPPDYPPEYPPFYPP5YPP6YPLPLPLPLPVBo6Qj3Yj2Yj1YiMX0YjLXjKXjJXi:XI@#;1#$&iDWJ@$/02)cyT0@Eb0*7-#/RQvqk3]Qk<NBK?^Qk<@JA1^@#$.$-$?ylQ<>EbySPP6YPbKXP4YPP7YPL<=EbPLWPPMWPP5YPLhPEWTP4YXL000OOOQQ6YOOOOOO0#(-#.WP7YQLPP6XPP7XPP8XPP9X31/*0%7+<XPP=XPP>=1/;%CXP71/.1137'P6YPM8&1-#9MXPPOXPP0YPVKoFQj1Yj0YjOXiNXNXjMX30--#*jIXjHXjGXjFXjEXjDX@$:11<@$01#:%k>S01+7%ACA0110-#)LRP6YPvqylQL@EbLP:.=$uq01#4*@@EbkDRQ01&#-#(LFJbSPk<5C36]Qk80#*0$.&4=Eb0#,-$%H<Ebk495@B]Qk4=6=D]QLPP6YPuqRPL000000000Tvq21&+-##P5YPP4YXP6Y@#&1$:@$$1$5#M11?/21$'&Ao<Q@$=1#%%iMW@$;11?51##109;0%@$:/:@4/2.;)P0YPPOX22/%&40Q842/&11@$%MXN41??@)(2/,#L22/*$@Q@#-2/)(LPP7YR@$@2/);22661=@-#%MoDQjOXjNXiMX@(22.?@#<2.7$@H@$>2.7&kERS"%pstring.
Definition OBLS := OB0.

Lemma WF : WFS CTX. Proof. wf_tac. Qed.
Lemma CHK : CHKS CTX PLAN (t_st T_PKPOP_e_m0k0uNp_kw0019197819078781996) OBLS. Proof. chk_tac. Qed.
End C_PKPOP_e_m0k0uNp_kw0019197819078781996.
