(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith List PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Mem Instr State Step Plan Notation.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Img Require Import ImgBoth ItabBoth RotBoth.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import Rot.
Import ListNotations W64 Val Mem FI St Step Plan.
From Stdlib Require Import PrimString.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require PlanDec.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require StrLz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib DefsA DefsM Defs DefsB.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.EH Require Import Pool.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Actr. Import Actr.TwinB.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import ActrB FaC RangeC StrRegC ReadC MemsetC MemcpyC Memcpy0C PubC MemcpyPC MemsetPC RstageC BlobC PayloadC HalfC VprintfC FprintfC FprintfSC StrnlenC FwriteC FwritePostC UnreggC. Import ActrB.TwinB FaC.TwinB RangeC.TwinB StrRegC.TwinB ReadC.TwinB MemsetC.TwinB MemcpyC.TwinB Memcpy0C.TwinB PubC.TwinB MemcpyPC.TwinB MemsetPC.TwinB RstageC.TwinB BlobC.TwinB PayloadC.TwinB HalfC.TwinB VprintfC.TwinB FprintfC.TwinB FprintfSC.TwinB StrnlenC.TwinB FwriteC.TwinB FwritePostC.TwinB UnreggC.TwinB.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import GRealign.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import GTwinSub CaseF.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import GshC. Import GshC.TwinB.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import StrlenC. Import StrlenC.TwinB.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import OpDropC. Import OpDropC.TwinB.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import RoLitA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import AmallocNnC. Import AmallocNnC.TwinB.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import ReadDirC. Import ReadDirC.TwinB.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import RoLit.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import GViewDrop2.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import GUnrealign.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import ShLoadLit.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import GBgNone.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.BothU Require UnivBoth.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Both2F Require Import T_Both2F.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Both2L Require Import T_Both2L.

Module C_LIBENT_r12.
Definition CUTL := (cons (pair 100%uint63 T_G0_r31o5n0o1n63o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0) (cons (pair 101%uint63 T_THROW_8e0d0_LIBENT_r12_1) (cons (pair 103%uint63 T_THROW_8e1c8_LIBENT_r12_2) (cons (pair 106%uint63 T_THROW_ced48_LIBENT_r12_3) (cons (pair 107%uint63 T_THROW_ced48_LIBENT_r12_4) (nil)))))).
Definition CTX := mkctx CUTL EC0 MR0.
Definition PLAN := PLR "Y7\@8AWD9AW053YD@3Y4M3YD<E[@AF[@3G[01I[4=K[8=K[<=K[@=K[<04\HKI\D@DaH@DaDADaHADa@BDaDBDa8EDa<EDa4FDa8FDa<HDa@HDaL3Ea@:Ea0;Ea4;Ea8;Ea<;EaDMEa@7FaD7FaD9FaL;Fa0<FaH@Fa0BFa4BFa8BFa<BFa@?Ga81HaL7Ha08Ha@9HaD9HaD?HaH?HaHAHaLAHaLFHa0GHa40IaL0Ia01Ia41Ia81Ia8BIaLKIa0OIa4OIa46Ja86Ja<=Ja@=Ja8IJa<IJaH8KaL8Ka8CKa<CKa4EKa8EKa8FKaHKKaLKKaD1LaH1La<7La@7LaH;LaL;LaLBLa0CLaLNLa0OLa46Ma86MaL;Ma0<MaLAMa0BMa@JMaDJMaD0NaD2NaH2Na@9NaD9Na0BNa4BNaLMNa0NNa<=Oa@=OaDGOaHGOa@MOaDMOa830b<30bH70bL70b<@0b@@0b0E0b4E0b8J0b<L0b4M0b8M0b<M0b@M0b4;6bHB7bLB7b@I7bDI7b<48b@48bD;8bH;8b8N8b<59b@59b0K9b4K9b<?:b@?:bDE:bHE:b8L:b0N:b4N:b44;b84;b4;;b8;;b0N;bL4<b05<b@G<bDN<bHN<b8F=b<F=bD>>bH>>b<6?b@6?b0O?b4O?bHK@bLK@b@0AbD0Ab85Ab<5Ab0:Ab4:AbD>AbH>Ab@CAbDCAb<GAb@GAb07Bb47BbD;BbH;Bb4?Bb8?BbDDBbHDBb81Cb83Cb48Cb88Cb0;Cb4;Cb0>Cb4>Cb@FCbDFCbDMCbHMCb0:Db4:DbH?DbL?DbHJDbLJDbD:EbH:EbLAEb0BEb@GEbDGEb0KEb4KEb@0FbD0Fb<=Fb<?Fb8DFb<DFb@HFbDHFbHLFbLLFb01Gb41Gb08Gb48GbL;Gb0<GbLDGb<EGb@EGbDEGbHEGbD0HbH7HbH;HbL;HbD5Jb06Jb46Jb86Jb<6Jb4@Jb4EJbDEJbHEJbLEJb0FJbD2Kb08Kb@8KbD8KbH8KbL8Kb4DKb@IKb0JKb4JKb8JKb<JKbD6Lb8;Lb<;Lb8BLb<BLb4ILb8ILbD1MbH1Mb<:Mb@:Mb@HMbDHMb01Nb41NbL:Nb0;NbH>Nb0BNb4BNb@ENb0FNb4FNb8FNb<FNb<BOb0JOb@JObDJObHJObLJObH71cLA1c<B1c@B1cDB1cHB1c482c4?2cD?2cH?2cL?2c0@2c<23cH83c<93c@93cD93cH93c4?4c8H4cHH4cLH4c0I4c4I4c4;5c4@5c8@5c0F5c4F5c@16cD16c496c896c8?6c<?6c@C6cDC6c<J6c@J6c877c<77c0G7c4G7cD28cH28c@88cD88cL?8c<@8c@@8cD@8cH@8cH29c099c499c@>9cD>9c4G9c8G9c0N9c4N9c4O9cH2:cH4:c8LIf8IOf<30gL<0g<=0g841gH41gD24g<34gL:4gD;4gD<4g8=4gDE4g4K4gL05g@75g@88g<:8g0C8g4F<g<G<g8HNg<HNgDHNgD>Og@GOg<KOg46Dh86Gh4AGh<0HhD:KiH:KiU5S]i1W?WiNVOVi=V>ViAUMUiET?Ui?T@Ti0T5Ti0R1Riddi\\iZZiUXiPSySPU7S^iBW0Xi?W@WiNVOVi=V>ViAUMUiET?Ui?T@Ti0T5Ti0R1Riddi\\iZZiUXiPSySPU:S_i@YNYi0X1Xi?W@WiNVOVi=V>ViAUMUiET?Ui?T@Ti0T5Ti0R1Riddi\\iZZiUXiPSySPk@H246]QySPU;Sai@\N\iN[O[iNYOYi0X1Xi?W@WiNVOVi=V>ViAUMUiET?Ui?T@Ti0T5Ti0R1Riddi\\iZZiUXiPSySPk@H246]QySPP?WPP@WPP0XPP1XPPNYPPOYPPN[PPO[PPN\PPO\PP@]PPA]PPB]PPJ]PPK]PPL]PPM]PU4SljAWj@Wj?Wj>Wj=Wj<Wj;Wj:Wj9Wj8Wj7Wj6Wj5Wj4Wj3Wj2Wj1WiNVOVi=V>ViETMUi?T@Ti0T5Ti0R1Riddi\\iZZiUXiPSySPk81H26]Qk41H26]QySPk3]QySPk4GH26]Qk0GH26]QySPk<AH26]Qk8AH26]QySPkO\QySPk4GH26]Qk0GH26]QySPk@;H26]Qk<;H26]QySPkHAG26]QkDAG26]QySPk@\RySPkL5G26]QkH5G26]QySPk<MF26]Qk8MF26]QySPkM\QySPkE\QySPk0EA26]QkLDA26]QkHDA26]QkDDA26]QySPylQ80IaySPkHBE26]QkDBE26]QySPk3]QySPk8KD26]Qk4KD26]QySPk0JE26]QkLIE26]QySPkDOD26]Qk@OD26]QySPk0JB26]QkLIB26]QySPkDLC26]Qk@LC26]QySPk3]QySPk8KD26]Qk4KD26]QySPk@ED26]Qk<ED26]QySPkO\QySPk8KD26]Qk4KD26]QySPkD?D26]Qk@?D26]QySPk4=C26]Qk0=C26]QySPk@\RySPk81C26]Qk41C26]QySPkLBB26]QkHBB26]QySPkM\QySPkK\QySPkH:A26]QkD:A26]QySPkM\QySPk@\RySPk<M@26]Qk8M@26]QySPk@\RySPkF\QySPk46?26]Qk06?26]QkL5?26]QkH5?26]QySPylQL@FaySPkF\QySPk4O=26]Qk0O=26]QkLN=26]QkHN=26]QySPylQD:Eak803E>]Qk8>BF=]Qm2ySP"%pstring.
Definition OBLS := OB0.

Lemma WF : WFS CTX. Proof. wf_tac. Qed.
Lemma CHK : CHKS CTX PLAN (t_st T_Both2F.T_LIBGEN_r12) OBLS. Proof. chk_tac. Qed.
End C_LIBENT_r12.

Module C_LIBENT_r9.
Definition CUTL := (cons (pair 102%uint63 T_THROW_8e0d0_LIBENT_r9_1) (cons (pair 104%uint63 T_THROW_8e1c8_LIBENT_r9_2) (cons (pair 105%uint63 T_THROW_8f7e4_LIBENT_r9_4) (cons (pair 108%uint63 T_THROW_ced48_LIBENT_r9_3) (nil))))).
Definition CTX := mkctx CUTL EC0 MR0.
Definition PLAN := PLR "Y7\@8AWD9AW053YD@3Y4M3YD<E[@AF[@3G[01I[4=K[8=K[<=K[@=K[<04\HKI\D@DaH@DaDADaHADa@BDaDBDa8EDa<EDa4FDa8FDa<HDa@HDaL3Ea@:Ea0;Ea4;Ea8;Ea<;EaDMEa@7FaD7FaD9FaL;Fa0<FaH@Fa0BFa4BFa8BFa<BFa@?Ga81HaL7Ha08Ha@9HaD9HaD?HaH?HaHAHaLAHaLFHa0GHa40IaL0Ia01Ia41Ia81Ia8BIaLKIa0OIa4OIa46Ja86Ja<=Ja@=Ja8IJa<IJaH8KaL8Ka8CKa<CKa4EKa8EKa8FKaHKKaLKKaD1LaH1La<7La@7LaH;LaL;LaLBLa0CLaLNLa0OLa46Ma86MaL;Ma0<MaLAMa0BMa@JMaDJMaD0NaD2NaH2Na@9NaD9Na0BNa4BNaLMNa0NNa<=Oa@=OaDGOaHGOa@MOaDMOa830b<30bH70bL70b<@0b@@0b0E0b4E0b8J0b<L0b4M0b8M0b<M0b@M0b4;6bHB7bLB7b@I7bDI7b<48b@48bD;8bH;8b8N8b<59b@59b0K9b4K9b<?:b@?:bDE:bHE:b8L:b0N:b4N:b44;b84;b4;;b8;;b0N;bL4<b05<b@G<bDN<bHN<b8F=b<F=bD>>bH>>b<6?b@6?b0O?b4O?bHK@bLK@b@0AbD0Ab85Ab<5Ab0:Ab4:AbD>AbH>Ab@CAbDCAb<GAb@GAb07Bb47BbD;BbH;Bb4?Bb8?BbDDBbHDBb81Cb83Cb48Cb88Cb0;Cb4;Cb0>Cb4>Cb@FCbDFCbDMCbHMCb0:Db4:DbH?DbL?DbHJDbLJDbD:EbH:EbLAEb0BEb@GEbDGEb0KEb4KEb@0FbD0Fb<=Fb<?Fb8DFb<DFb@HFbDHFbHLFbLLFb01Gb41Gb08Gb48GbL;Gb0<GbLDGb<EGb@EGbDEGbHEGbD0HbH7HbH;HbL;HbD5Jb06Jb46Jb86Jb<6Jb4@Jb4EJbDEJbHEJbLEJb0FJbD2Kb08Kb@8KbD8KbH8KbL8Kb4DKb@IKb0JKb4JKb8JKb<JKbD6Lb8;Lb<;Lb8BLb<BLb4ILb8ILbD1MbH1Mb<:Mb@:Mb@HMbDHMb01Nb41NbL:Nb0;NbH>Nb0BNb4BNb@ENb0FNb4FNb8FNb<FNb<BOb0JOb@JObDJObHJObLJObH71cLA1c<B1c@B1cDB1cHB1c482c4?2cD?2cH?2cL?2c0@2c<23cH83c<93c@93cD93cH93c4?4c8H4cHH4cLH4c0I4c4I4c4;5c4@5c8@5c0F5c4F5c@16cD16c496c896c8?6c<?6c@C6cDC6c<J6c@J6c877c<77c0G7c4G7cD28cH28c@88cD88cL?8c<@8c@@8cD@8cH@8cH29c099c499c@>9cD>9c4G9c8G9c0N9c4N9c4O9cH2:cH4:c8LIf8IOf<30gL<0g<=0g841gH41gD24g<34gL:4gD;4gD<4g8=4gDE4g4K4gL05g@75g@88g<:8g0C8g4F<g<G<g8HNg<HNgDHNgD>Og@GOg<KOg46Dh86Gh4AGh<0HhD:KiH:KiU6S^i0W>WiMVNVi<V=ViGULUi>UAUiBT<Ui<T=Ti0T2Ti0R1Riddi\\iZZiUXiPSySPU8S_iAWOWi>W?WiMVNVi<V=ViGULUi>UAUiBT<Ui<T=Ti0T2Ti0R1Riddi\\iZZiUXiPSySPU<S`i?YMYiOW0Xi>W?WiMVNVi<V=ViGULUi>UAUiBT<Ui<T=Ti0T2Ti0R1Riddi\\iZZiUXiPSySPk@H246]QySPU9SaiE[N[i?[A[iMYNYiOW0Xi>W?WiMVNVi<V=ViGULUiBTAUi<T=Ti0T2Ti0R1Riddi\\iZZiUXiPSySPkE\QySPk0EA26]QkLDA26]QkHDA26]QkDDA26]QySPylQ80IaySPkHBE26]QkDBE26]QySPk3]QySPk8KD26]Qk4KD26]QySPk0JE26]QkLIE26]QySPkDOD26]Qk@OD26]QySPk0JB26]QkLIB26]QySPkDLC26]Qk@LC26]QySPk3]QySPk8KD26]Qk4KD26]QySPk@ED26]Qk<ED26]QySPkO\QySPk8KD26]Qk4KD26]QySPkD?D26]Qk@?D26]QySPk4=C26]Qk0=C26]QySPk@\RySPk81C26]Qk41C26]QySPkLBB26]QkHBB26]QySPkM\QySPkK\QySPkH:A26]QkD:A26]QySPkM\QySPk@\RySPk<M@26]Qk8M@26]QySPk@\RySPkF\QySPk46?26]Qk06?26]QkL5?26]QkH5?26]QySPylQL@FaySPkF\QySPk4O=26]Qk0O=26]QkLN=26]QkHN=26]QySPylQD:Eak803E>]Qk8>BF=]Qm2ySP"%pstring.
Definition OBLS := OB0.

Lemma WF : WFS CTX. Proof. wf_tac. Qed.
Lemma CHK : CHKS CTX PLAN (t_st T_Both2F.T_LIBGEN_r9) OBLS. Proof. chk_tac. Qed.
End C_LIBENT_r9.
