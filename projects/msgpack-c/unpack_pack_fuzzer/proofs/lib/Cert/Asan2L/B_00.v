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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Asan2F Require Import T_Asan2F.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Asan2L Require Import T_Asan2L.

Module C_LIBENT_r12.
Definition CUTL := (cons (pair 100%uint63 T_G0_r31o5n0o1n63o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0) (cons (pair 101%uint63 T_THROW_8d6b8_LIBENT_r12_1) (cons (pair 103%uint63 T_THROW_8d78c_LIBENT_r12_2) (cons (pair 106%uint63 T_THROW_ccc04_LIBENT_r12_3) (cons (pair 107%uint63 T_THROW_ccc04_LIBENT_r12_4) (nil)))))).
Definition CTX := mkctx CUTL EC0 MR0.
Definition PLAN := PLR "Y9Y0L>W4M>W@H0Y441YD@1Y40C[05D[0GD[@DF[D0I[H0I[L0I[01I[LC1\8?G\44Ba84Ba45Ba85Ba06Ba46BaH8BaL8BaD9BaH9BaD:BaH:BaL;Ba0<BaD<BaH<Ba<GBa0NBa@NBaDNBaHNBaLNBa4ACa0KCa4KCa4MCaLNCa0OCaD3DaL4Da05Da45Da85Da40EaHAEaLGEa0HEa<IEa@IEa@NEaDNEa@0FaD0Fa85Fa<5Fa@>Fa8?Fa<?Fa@?FaD?Fa80GaH9Ga0=Ga4=GaLEGa0FGaD0HaH0HaH@HaL@HaHEHaLEHaHJHaLJHaL:Ia0;Ia4@Ia8@IaDEIaHEIaDOIa@1JaD1Ja@8JaD8Ja<AJa@AJa4LJa8LJaH4KaL4KaH9KaL9Ka<>Ka@>Ka8GKa<GKa0LKa0NKa4NKaD95bH95bLD5b0E5b0=6bL@6b0A6b8G6b<G6bL=7b0>7bH48b088b488b<09b<49b@49b8;9b<;9b<3:b87:b<7:bL=:b0>:b08;b48;b@1<bD1<bHK<bLK<b4E=b8E=b<@>b@@>bDE>bHE>b89?bL:?b@=?bD=?b4C?b8C?b0F?b4F?b4L?b8L?bL<@b0=@b@4AbD4AbL:Ab0;Ab@NAb40BbH2BbL2Bb88Bb<8Bb@<BbD<BbH@BbL@Bb0EBb4EBb0LBb4LBb<5CbL5Cb06Cb46Cb86Cb4ACb8HCb@LCb0MCb4MCb8MCb<MCb<MEbH>Fb8?Fb<?Fb@?FbD?FbHJFb<0Gb01Gb41Gb81Gb<1GbDFGbLNGb@OGbDOGbHOGbLOGb@BHbLHHb0IHbH0Ib81Ib<1Ib@1IbD1IbDBIb0IIb@IIbDIIbHIIbLIIbL:JbHBJbLBJbLNJb0OJb@7KbD7Kb<;Kb4>Kb8>Kb@AKb0BKb4BKb8BKb<BKbH;Lb8CLbHCLbLCLb0DLb4DLb4LMb86NbL6Nb07Nb47Nb87NbL6Ob4?Ob8?ObDMObHMOb430c830c490c890c8D0c<D0cLN0c0O0cL31c041c4:1c8:1c4E1c8E1c8F1cLI1cLK1c<CAf@JGf04Hf@4Hf<KHfLKHfHIKf@JKf02LfH2LfH3Lf<4LfH<Lf8BLf0HLfDNLfDOOf@10g4:0g8=4g@>4g<?Fg@?FgH?FgH5GgD>Gg@BGg8M;h<M>h88?h@G?hH1CiL1CiU5S]i1W?WiNVOVi=V>ViAUMUiET?Ui?T@Ti0T5Ti0R1Riddi\\iZZiUXiPSySPU7S^iBW0Xi?W@WiNVOVi=V>ViAUMUiET?Ui?T@Ti0T5Ti0R1Riddi\\iZZiUXiPSySPU:S_i@YNYi0X1Xi?W@WiNVOVi=V>ViAUMUiET?Ui?T@Ti0T5Ti0R1Riddi\\iZZiUXiPSySPk<>J36]QySPU;Sai@\N\iN[O[iNYOYi0X1Xi?W@WiNVOVi=V>ViAUMUiET?Ui?T@Ti0T5Ti0R1Riddi\\iZZiUXiPSySPk<>J36]QySPP?WPP@WPP0XPP1XPPNYPPOYPPN[PPO[PPN\PPO\PP@]PPA]PPB]PPH]PPI]PPJ]PPK]PPL]PPM]PU4SnjCWjBWjAWj@Wj?Wj>Wj=Wj<Wj;Wj:Wj9Wj8Wj7Wj6Wj5Wj4Wj3Wj2Wj1WiNVOVi=V>ViETMUi?T@Ti0T5Ti0R1Riddi\\iZZiUXiPSySPkH>C26]QkD>C26]QySPk3]QySPk<LC26]Qk8LC26]QySPkO\QySPk<GC26]Qk8GC26]QySPk04C26]QkL3C26]QySPk@\RySPk4KB26]Qk0KB26]QySPkM\QySPkE\QySPk42?26]Qk02?26]QkL1?26]QkH1?26]QySPylQD>FaySPk3]QySPk@MA26]Qk<MA26]QySPk<=A26]Qk8=A26]QySPk8C@26]Qk4C@26]QySPk3]QySPk<8A26]Qk88A26]QySPkO\QySPk<3A26]Qk83A26]QySPk@8@26]Qk<8@26]QySPk@\RySPkDO?26]Qk@O?26]QySPkM\QySPkK\QySPkLG>26]QkHG>26]QySPkM\QySPk@\RySPk0<>26]QkL;>26]QySPk@\RySPkF\QySPkHG<26]QkDG<26]Qk@G<26]Qk<G<26]QySPylQH3DaySPkF\QySPk<A;26]Qk8A;26]Qk4A;26]Qk0A;26]QySPylQ4NBak@B0E>]Qk@0@F=]Qm2ySP"%pstring.
Definition OBLS := OB0.

Lemma WF : WFS CTX. Proof. wf_tac. Qed.
Lemma CHK : CHKS CTX PLAN (t_st T_Asan2F.T_LIBGEN_r12) OBLS. Proof. chk_tac. Qed.
End C_LIBENT_r12.

Module C_LIBENT_r9.
Definition CUTL := (cons (pair 102%uint63 T_THROW_8d6b8_LIBENT_r9_1) (cons (pair 104%uint63 T_THROW_8d78c_LIBENT_r9_2) (cons (pair 105%uint63 T_THROW_8e7a8_LIBENT_r9_4) (cons (pair 108%uint63 T_THROW_ccc04_LIBENT_r9_3) (nil))))).
Definition CTX := mkctx CUTL EC0 MR0.
Definition PLAN := PLR "Y9Y0L>W4M>W@H0Y441YD@1Y40C[05D[0GD[@DF[D0I[H0I[L0I[01I[LC1\8?G\44Ba84Ba45Ba85Ba06Ba46BaH8BaL8BaD9BaH9BaD:BaH:BaL;Ba0<BaD<BaH<Ba<GBa0NBa@NBaDNBaHNBaLNBa4ACa0KCa4KCa4MCaLNCa0OCaD3DaL4Da05Da45Da85Da40EaHAEaLGEa0HEa<IEa@IEa@NEaDNEa@0FaD0Fa85Fa<5Fa@>Fa8?Fa<?Fa@?FaD?Fa80GaH9Ga0=Ga4=GaLEGa0FGaD0HaH0HaH@HaL@HaHEHaLEHaHJHaLJHaL:Ia0;Ia4@Ia8@IaDEIaHEIaDOIa@1JaD1Ja@8JaD8Ja<AJa@AJa4LJa8LJaH4KaL4KaH9KaL9Ka<>Ka@>Ka8GKa<GKa0LKa0NKa4NKaD95bH95bLD5b0E5b0=6bL@6b0A6b8G6b<G6bL=7b0>7bH48b088b488b<09b<49b@49b8;9b<;9b<3:b87:b<7:bL=:b0>:b08;b48;b@1<bD1<bHK<bLK<b4E=b8E=b<@>b@@>bDE>bHE>b89?bL:?b@=?bD=?b4C?b8C?b0F?b4F?b4L?b8L?bL<@b0=@b@4AbD4AbL:Ab0;Ab@NAb40BbH2BbL2Bb88Bb<8Bb@<BbD<BbH@BbL@Bb0EBb4EBb0LBb4LBb<5CbL5Cb06Cb46Cb86Cb4ACb8HCb@LCb0MCb4MCb8MCb<MCb<MEbH>Fb8?Fb<?Fb@?FbD?FbHJFb<0Gb01Gb41Gb81Gb<1GbDFGbLNGb@OGbDOGbHOGbLOGb@BHbLHHb0IHbH0Ib81Ib<1Ib@1IbD1IbDBIb0IIb@IIbDIIbHIIbLIIbL:JbHBJbLBJbLNJb0OJb@7KbD7Kb<;Kb4>Kb8>Kb@AKb0BKb4BKb8BKb<BKbH;Lb8CLbHCLbLCLb0DLb4DLb4LMb86NbL6Nb07Nb47Nb87NbL6Ob4?Ob8?ObDMObHMOb430c830c490c890c8D0c<D0cLN0c0O0cL31c041c4:1c8:1c4E1c8E1c8F1cLI1cLK1c<CAf@JGf04Hf@4Hf<KHfLKHfHIKf@JKf02LfH2LfH3Lf<4LfH<Lf8BLf0HLfDNLfDOOf@10g4:0g8=4g@>4g<?Fg@?FgH?FgH5GgD>Gg@BGg8M;h<M>h88?h@G?hH1CiL1CiU6S^i0W>WiMVNVi<V=ViGULUi>UAUiBT<Ui<T=Ti0T2Ti0R1Riddi\\iZZiUXiPSySPU8S_iAWOWi>W?WiMVNVi<V=ViGULUi>UAUiBT<Ui<T=Ti0T2Ti0R1Riddi\\iZZiUXiPSySPU<S`i?YMYiOW0Xi>W?WiMVNVi<V=ViGULUi>UAUiBT<Ui<T=Ti0T2Ti0R1Riddi\\iZZiUXiPSySPk<>J36]QySPU9SaiE[N[i?[A[iMYNYiOW0Xi>W?WiMVNVi<V=ViGULUiBTAUi<T=Ti0T2Ti0R1Riddi\\iZZiUXiPSySPkE\QySPk42?26]Qk02?26]QkL1?26]QkH1?26]QySPylQD>FaySPk3]QySPk@MA26]Qk<MA26]QySPk<=A26]Qk8=A26]QySPk8C@26]Qk4C@26]QySPk3]QySPk<8A26]Qk88A26]QySPkO\QySPk<3A26]Qk83A26]QySPk@8@26]Qk<8@26]QySPk@\RySPkDO?26]Qk@O?26]QySPkM\QySPkK\QySPkLG>26]QkHG>26]QySPkM\QySPk@\RySPk0<>26]QkL;>26]QySPk@\RySPkF\QySPkHG<26]QkDG<26]Qk@G<26]Qk<G<26]QySPylQH3DaySPkF\QySPk<A;26]Qk8A;26]Qk4A;26]Qk0A;26]QySPylQ4NBak@B0E>]Qk@0@F=]Qm2ySP"%pstring.
Definition OBLS := OB0.

Lemma WF : WFS CTX. Proof. wf_tac. Qed.
Lemma CHK : CHKS CTX PLAN (t_st T_Asan2F.T_LIBGEN_r9) OBLS. Proof. chk_tac. Qed.
End C_LIBENT_r9.
