(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (2 recorded proofs replaced by written proofs (rw_bytes_b_any, rw_junk_image)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Cells Step Arr InitMem.
From OSSVerify.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_ACanary () := "C46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List8map_consK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes6option00C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3addK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2leC47Corelib4Init5Peano2ltK47Corelib4Init9Datatypes6option01K47Corelib4Init9Datatypes6option02K47Corelib4Init9Datatypes4list01C56Stdlib6ZArith6BinInt1Z2ltK47Corelib4Init5Logic2eq01C46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula03C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib4Init9Datatypes4list02C59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC47Corelib4Init9Datatypes4andbC47Corelib4Init9Datatypes9andb_propI47Corelib4Init5Logic3and00K47Corelib4Init9Datatypes3nat02C45stdpp9bitvector;definitions;bv_unsignedC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<find_segmentC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType<seg_writableC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType9seg_bytesC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType8seg_baseC56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z4to_NC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics?segment_byte_atI47Corelib4Init5Logic2ex00C47Corelib4Init5Logic3notK47Corelib4Init5Logic2ex01C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic9False_indK47Corelib4Init5Logic3and01C56Stdlib6ZArith6BinInt1Z7add_0_rC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega;ZifyClasses;rew_iff_revK46Stdlib9micromega7EnvRing5PExpr07C47Corelib4Init9Datatypes8list_indC59OSSVerify5KrLib3Lib7InitMem:rw_bytes_bC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem3mrdC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08C59OSSVerify5KrLib3Lib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C59OSSVerify5KrLib5BothW4BImg5bsegsC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z6inj_ltK47Corelib4Init9Datatypes3nat01K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205C56Stdlib6ZArith4Znat5Nat2Z8inj_succK47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I47Corelib4Init5Logic4True00I47Corelib4Init5Logic5False00K47Corelib4Init5Logic4True01C46Stdlib9micromega8ZifyInst7Inj_Z_ZK46Stdlib9micromega=RingMicromega3Op201C46Stdlib5Lists4List9app_nil_rC46Stdlib5Lists4List:length_mapC45stdpp9bitvector;definitions7Z_to_bvK59OSSVerify5KrLib3Lib5Cells4cell05C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3seqC47Corelib5Lists7ListDef3mapC59OSSVerify5KrLib3Lib5Cells8cells_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem5wr_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells8cells_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells;cells_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:length_seqC46Stdlib5Lists4List9nth_errorC47Corelib4Init9Datatypes:option_mapC56Stdlib5Arith8PeanoNat3Nat3ltbC47Corelib4Init3Nat3addC56Stdlib5Arith8PeanoNat3Nat6ltb_ltC47Corelib4Init5Logic6eq_symc59OSSVerify5KrLib5BothW7ACanary>rw_bytes_b_anyC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List=nth_error_seqC46Stdlib5Lists4List=nth_error_mapC47Corelib4Init9Datatypes3appC56Stdlib6ZArith6BinInt1Z6to_natC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C47Corelib4Init5Logic5proj2C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib5Arith8PeanoNat3Nat7add_0_rK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqI59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~K46Stdlib9micromega:ZMicromega;ZArithProof01C59OSSVerify5KrLib3Lib3Mem3le8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem:length_le8C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5BothW7ACanary=rw_junk_imageC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Lemma rw_bytes_b_any : forall bs A (m : word -> option byte),
  rw_bytes_b bsegs A bs = true -> (0 <= A)%Z -> (A + Z.of_nat (length bs) <= 2^64)%Z ->
  forall i, (i < length bs)%nat ->
    (exists b, mrd bsegs m (wa (A + Z.of_nat i)) = Some b) /\ wview bsegs m (wa (A + Z.of_nat i)) <> None.
Proof.
  induction bs as [|b0 bs IH]; intros A m Hb HA Hl i Hi; [cbn in Hi; lia|].
  cbn [rw_bytes_b] in Hb.
  destruct (seg_rom bsegs (wa A)) as [b'|] eqn:Er; [|discriminate].
  destruct (wview bsegs (fun _ => None) (wa A)) as [bw|] eqn:Ew; [|discriminate].
  apply andb_prop in Hb. destruct Hb as [_ Hb]. cbn [length] in Hl, Hi.
  destruct i as [|i].
  - rewrite Z.add_0_r. unfold mrd, wview in *. destruct (m (wa A)) as [b1|].
    + split; [exists b1; reflexivity| discriminate].
    + split; [exists b'; exact Er| rewrite Ew; discriminate].
  - replace (A + Z.of_nat (S i))%Z with ((A + 1) + Z.of_nat i)%Z by lia. apply (IH (A + 1)%Z m Hb); lia.
Qed.

Lemma rw_junk_image : forall (m : word -> option byte) A bs,
  rw_bytes_b bsegs A bs = true -> (0 <= A)%Z -> (A + Z.of_nat (length bs) <= 2^64)%Z ->
  exists bs', rw_cells bsegs m A [CB (length bs) bs'].
Proof.
  intros m A bs Hb HA Hl.
  set (f := fun i : nat => match mrd bsegs m (wa (A + Z.of_nat i)) with Some b => b | None => Z_to_bv 8 0 end).
  exists (map f (seq 0 (length bs))).
  split; [split|].
  - cbn. rewrite length_map, length_seq. split; [reflexivity| exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. split; [lia|]. rewrite length_map, length_seq. split; [lia|].
    intros i Hi. rewrite nth_error_map, nth_error_seq. replace (PeanoNat.Nat.ltb i (length bs)) with true by (symmetry; apply PeanoNat.Nat.ltb_lt; exact Hi). cbn [option_map Nat.add].
    destruct (rw_bytes_b_any bs A m Hb HA Hl i Hi) as [[b Hmb] _]. unfold f. rewrite Hmb. reflexivity.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. split; [lia|]. split; [lia|].
    intros i Hi. replace i with (Z.of_nat (Z.to_nat i)) by lia. apply (proj2 (rw_bytes_b_any bs A m Hb HA Hl (Z.to_nat i) ltac:(lia))).
Qed.

Lemma premap_canary_any : forall m : word -> option byte, exists cb, rw_cells bsegs m 0x60d2d0 [CB 8 cb].
Proof.
ltac2:(KReplay.run1 (kr_t_ACanary ()) ["CANSEC1"] "p'0h01Hh17__arithh24__ffh38__varmaph45__with53bs'h62cbh71nh82bsh91eh:1mi001xp;1p;2p;3p;4p;6p;7p10000p4p710g000MR0p4p710R1p8p1000kp4p7210P1p8g001Hj10Tg001mj1=Tg002Kj1<Tg003Nj1ZTg00=hj11Tg005Mj15Tg00i<j2QTg01AZj1LTg009<j2GTg00U9j3FTg00CBj3:Tg008@j1ATg002nj1BTg00:bj1VTg00<<j1UTg00<Zj1TTg00=Ej26Tg00R^j4@Tg00?Tj2STg00@6j2RTg00@bj3PTg00AAj4OTg006Hj29Tg00Eej12Tg004Pj1KTg0050j2;Tg005kj2HTg00R;j3ITg00T4j3JTg0040j2ETg01BJj1MTP0j6NTg01CAj6DTg00ibj28Tg00B3j37Tg00MQR0j2?Tg00N^j6CTg00NDj4YTg00Waj7XTg00jWj4WTf0R1#0#0p=3f1R2g00_eg00`DR3P3g00`dR3P1g00aDFXp=>g00ZmR4f2R5P2P1CWp=4g00boR6#0R7#3R8#0#3R9#=R:#<%=8#<R;#Z[P1%16#0#3#3#1#1#0#1#3#1#0#1#1#0#1#3#3#5R6g00\bR<,Q:R=#LR>g00[bR?g00\BR@'GRAAF46>=:?@dg00cTR4#ARB%B4R4g00]@RC#VRD%UCRE%TCRFPC16C<g00_>RG16C6RHC@'>1SF3R3P1P5PA1R15=:?@dAPC<2COR@b2b3b419<6P1b1g00]^R<g00^_#2#2#2#2#2#2#2#2R?%K1,;6%57R7%59'HR9'9X7<PBP4PDPEPC%58R8,6C9ICHPG16C7=JC:C@,>FP3P@b2b3b41;68/99P1b11E;>R>%M=R=ENED%B;R;g01@9R918>1%A9R837R@9426X5;'?P0P;A456@X5;f318?1=798R0746X6;,?;P1f4?46@P<P>f61815=798746X7<P1P?P=ECf518?2=798746P;f7?460X6;P5P1CYb0W0X8;P2P1O2n2001000000121100000b9W:o"). Qed.

End CANSEC1.
