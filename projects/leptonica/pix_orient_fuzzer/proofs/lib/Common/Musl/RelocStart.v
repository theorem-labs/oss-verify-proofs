(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Reloc Require Import Reloc RelocBlocks RelocImg.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_RelocStart () := "c69OSSVerify5KrLib6Common4Musl:RelocStart;rl_start_okC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02C69OSSVerify5KrLib6Common5Reloc5Reloc8rl_deltaC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common5Reloc8RelocImg:rl_data_loC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common4Musl:RelocStart8start_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3lebC47Corelib4Init9Datatypes9andb_propI47Corelib4Init5Logic3and00I47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z6eqb_eqI47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z6leb_leK47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C56Stdlib6ZArith6BinInt1Z3addC45stdpp9bitvector;definitions7Z_to_bvK47Corelib4Init5Logic2eq01C56Stdlib6ZArith6BinInt1Z7add_0_rC47Corelib4Init5Logic8eq_ind_rC69OSSVerify5KrLib6Common5Reloc5Reloc2rlC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common4Musl:RelocStart8rl_dABS0C1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition RPH0 : PhdrInfo := {| ph_addr := 0x10040%N; ph_ent := 56%N; ph_num := 10%N |}.

Definition start_ok (dABS_ data_lo : Z) : bool := ((dABS_ =? 0) && (0x10270 <=? data_lo))%Z.

Class RelocStart (RL : Reloc) (RD : RelocData RL) := {
  rl_start_ok : start_ok dABS rl_data_lo = true
}.

Section Facts.
  Context {RL : Reloc} {RD : RelocData RL} {RST : RelocStart RL RD}.

  Lemma rl_dABS0 : dABS = 0%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_RelocStart ()) ["Facts"] "h01Hh11mh21nh32H0h42_Hp;3p;1p;2g0000j3>Tg0017j14Tg001\j26Tg002\j2=Tg003aj2;Tg004ej25Tg005Bj13Tg005gj17Tg006Ej28Tg006bj39Tg007ER0j2:Tg007`j31Tg008:j2<Tf0R1#4#4p=2g008Zg009:711p=0p,2RLR2p,2RDR3p,3RST3>g009Z#4#2R4,62R51=23R3';#0g00:?R2,55R6%44#2#3#2#3#3#3#2#2#7/83R3;91%06R6%03R3':P0P6P3g00:]R4?152R7P1P0f1R0/51#0f2R8=140[R9A14011580#0R:[f3=148\:1<01P0n2001000000120000000X14X24P9^14^24P1P5P2P8O3P7P1b0b3X43X06P0P1O2n2001000000120000000b0b0o"). Qed.

  Lemma rl_hdr_below : (0x10270 <= rl_data_lo)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_RelocStart ()) ["Facts"] "h01Hh11mh21nh32H0h42_Hp;3p;1p;2g0000j3?Tg0017j13Tg001\j26Tg002\j2>Tg003aj2;Tg004ej28Tg005Bj12Tg005gj17Tg006Ej25Tg006bj39Tg007ER0j2:Tg00;;j24Tg00;Wj2=Tg007`j3<Tf0R1#3#3p=0g008Zg009:7<1p=1p,2RLR2p,2RDR3p,3RST3?g009Z#3#0R4,62R51>23R3';#1g00:?,85R5%34#0#2#0#2#2#2#0#0#7R4/53R2;91%15R5%12R2':P0P5P21443R6P1g00:]R7P0f1R0/51#1f2R8/40[R914011580#1R:[f3/48\:1=01P0n2001000000120000000X17W2P9^17^27P1P4P3P0O3P6P1b0b3X02X45P0P1O2n2001000000120000000b0b0o"). Qed.

  (* [comment removed for export] *)
  Lemma rl_abs : forall c, rl dABS c = Z_to_bv 64 c.
Proof.
ltac2:(KReplay.run1 (kr_t_RelocStart ()) ["Facts"] "h01zh11cp;1p;2p;3p;6g0017j10Tg00<7j1:Tg00<Uj18Tg00=8j24Tg00=Uj22Tg007`j31Tg00>;j29Tg00>Uj17Tg00?6j63Tg001\j26Tg00?Tj25Tg00:]R0P0g00:?R1g009Z#0#0#0R2#0#0#0#:R3#8R4f1R5f0R6'4,231235R531X00P0P61236R3=145X0019431461%76E3p,2RL/62R2g00@NE31526=143eW1o"). Qed.
End Facts.

