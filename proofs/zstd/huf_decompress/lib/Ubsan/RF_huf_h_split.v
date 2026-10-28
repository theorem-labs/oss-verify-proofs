(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas FuzzProducer HufHarness.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg StdioFiles.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import RMallocRep RMallocTree RMalloc_iface Harness_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import RDriver_facts RF_huf_h_iface RF_huf_h_kit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import Prelim Monad Stdio Malloc Harness Prog.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RF_huf_h_split () := "C5ARocqVerifyHarness?AgentSubmission4Spec6Malloc4aptrC5ARocqVerifyHarness?AgentSubmission4Spec5Monad1MC5ARocqVerifyHarness?AgentSubmission6Malloc<MallocBlocks5blockC46Stdlib5Lists4List2InC47Corelib5Lists7ListDef3mapC46Stdlib5Lists4List8nil_consC35stdpp7tactics<f_equal_helpC47Corelib4Init5Logic8eq_ind_rC47Corelib4Init9Datatypes8list_indC47Corelib4Init9Datatypes3appC45stdpp;list_basics4list9app_inj_1C46Stdlib5Lists4List7map_appC5ARocqVerifyHarness?AgentSubmission4Spec6Malloc4optrC5ARocqVerifyHarness?AgentSubmission6Malloc8ProgDeps4bptrI47Corelib4Init5Logic2eq00C47Corelib4Init5Logic6eq_indI46Stdlib5Lists4List5NoDup00I47Corelib4Init9Datatypes4list00C5ARocqVerifyHarness?AgentSubmission5Ubsan=RMalloc_iface5RHEAPC5ARocqVerifyHarness?AgentSubmission5Ubsan>RMalloc_ifacePHRHEAP_blocks_nodup_proofI47Corelib4Init5Logic2or00C46Stdlib5Lists4List:in_app_iffK47Corelib4Init5Logic2eq01K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C5ARocqVerifyHarness?AgentSubmission6Malloc<MallocBlocks6blk_idC46Stdlib5Lists4List>NoDup_remove_2C47Corelib4Init5Logic3notC47Corelib4Init5Logic6eq_symC5ARocqVerifyHarness?AgentSubmission5Ubsan>RMalloc_ifacePKRHEAP_blocks_disjoint_proofK47Corelib4Init9Datatypes4list02I5ARocqVerifyHarness?AgentSubmission4Spec6PState6PState00C5ARocqVerifyHarness?AgentSubmission6Malloc:MallocTree3memI47Corelib4Init5Logic3and00C5ARocqVerifyHarness?AgentSubmission4Spec7Harness;fuzz_mallocC5ARocqVerifyHarness?AgentSubmission5Ubsan=RMalloc_iface=rclient_rangeC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst4ATOPC56Stdlib6ZArith6BinInt1Z2ltC5ARocqVerifyHarness?AgentSubmission5Ubsan>RMalloc_ifacePGRHEAP_block_range_proofC5ARocqVerifyHarness?AgentSubmission6Malloc<MallocBlocks8blk_addrC5ARocqVerifyHarness?AgentSubmission6Malloc<MallocBlocks8blk_sizeC5ARocqVerifyHarness?AgentSubmission5Ubsan=RMalloc_iface<rblock_rangeK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3addK47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic2ex00C5ARocqVerifyHarness?AgentSubmission6Common7RunDraw:atop_rangeK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr03K47Corelib4Init9Datatypes6option02K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_doneC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega7EnvRing5PExpr01C5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_h_kitHblocks_distinct_disjointK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula05K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03C5ARocqVerifyHarness?AgentSubmission5Ubsan:RMallocRep5RLIBCC5ARocqVerifyHarness?AgentSubmission5Ubsan:RMallocRep4RCTXC5ARocqVerifyHarness?AgentSubmission5Ubsan:RMallocRep6RERRNOC5ARocqVerifyHarness?AgentSubmission5Ubsan:RMallocRep:RSSP_GUARDC5ARocqVerifyHarness?AgentSubmission5Ubsan:RMallocRep8RGOT_SSPI46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init5Logic4True01I47Corelib4Init9Datatypes:comparison00C5ARocqVerifyHarness?AgentSubmission6Malloc<Malloc_iface9lb_removeC5ARocqVerifyHarness?AgentSubmission5Ubsan=RDriver_facts<lb_remove_hdC46Stdlib5Lists4List>NoDup_cons_iffC5ARocqVerifyHarness?AgentSubmission6Malloc<Malloc_iface8bptr_eqbC47Corelib4Init9Datatypes4negbC46Stdlib4Bool4Bool7Is_trueC35stdpp9decidable;Is_true_decC35stdpp4base6decideC45stdpp;list_basics4list;list_filterC35stdpp4base6filterI47Corelib4Init6Specif7sumbool00C5ARocqVerifyHarness?AgentSubmission5Ubsan=RDriver_facts;bptr_eqb_eqC47Corelib4Init5Logic9False_indC45stdpp;list_basics4list;filter_consK47Corelib4Init9Datatypes4bool02c5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_h_split=lb_remove_mid".
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Notation mem := (word -> option byte).

Section CANSEC1. Context {rc : runConstT}.

Definition PC_HM : Z := 0x1337c.     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition fz_rest (producer dt wksp dBuf : option bptr) : Monad.M PState Z :=
  Harness.free_opt raw_free dt ;;; Harness.free_opt raw_free wksp ;;; Harness.free_opt raw_free dBuf ;;;
  Harness.free_opt raw_free producer ;;; mret 0.

(* [comment removed for export] *)
Definition hM_state (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (LB : list block) (AB lo D : Z) (payload : list Z) (m : mem)
    (producer dt wksp dBuf : option bptr) (s' : PState) (ms' : machine_state) : Prop :=
  exists (p pd pw : bptr) (P DT W DST : Z) (LBd : list block) (f1 f2 f3 f4 f5 : Z) (j0 jdt jw jd : list byte)
         (rax t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem) (errv' : word),
    producer = Some p /\ dt = Some pd /\ wksp = Some pw
    /\ ((dBuf = None /\ DST = 0 /\ hp_dbuf (huf_draws payload (zlen payload)) = 0 /\ LBd = [])
        \/ (exists pb, dBuf = Some pb /\ LBd = [(pb, DST, hp_dbuf (huf_draws payload (zlen payload)))]
                       /\ rblock_range DST (hp_dbuf (huf_draws payload (zlen payload)))))
    /\ ms' = MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -128)) gp (Z_to_bv 64 RATP) t0 t1 t2 (Z_to_bv 64 P) (Z_to_bv 64 D)
                 (Z_to_bv 64 DST) a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 f5) (Z_to_bv 64 (hp_mtl (huf_draws payload (zlen payload)))) (Z_to_bv 64 DT) (Z_to_bv 64 W) s6
                 (Z_to_bv 64 (hp_dbuf (huf_draws payload (zlen payload))))
                 (Z_to_bv 64 f1) (Z_to_bv 64 f2) (Z_to_bv 64 f3) (Z_to_bv 64 f4) t3 t4 t5 t6)
                F (Z_to_bv 64 PC_HM) fc None m' (seg_rom usegs)
    /\ 0 <= f1 <= 1 /\ 0 <= f2 <= 1 /\ 0 <= f3 <= 1 /\ 0 <= f4 <= 1 /\ 0 <= f5 <= 1
    /\ RHEAP s' (LBd ++ (pw, W, 8704) :: (pd, DT, DT_BYTES (hp_mtl (huf_draws payload (zlen payload))))
                     :: (p, P, PRODUCER_SIZE) :: LB) m'
    /\ rblock_range P PRODUCER_SIZE /\ rblock_range DT (DT_BYTES (hp_mtl (huf_draws payload (zlen payload))))
    /\ rblock_range W 8704
    /\ rauxv_ok m' AB /\ rw_cells usegs m' RERRNO [C4 errv']
    /\ rw_cells usegs m' (bv_unsigned sp + -128)
         [CB 8 j0; C8 (Z_to_bv 64 (hp_streams (huf_draws payload (zlen payload))));
          C8 (Z_to_bv 64 (hp_symbols (huf_draws payload (zlen payload))));
          C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ bytes_at usegs m' D (map (Z_to_bv 8) payload)
    /\ prod_at m' P D (hp_rest (huf_draws payload (zlen payload)))
    /\ rw_cells usegs m' DT [CB (Z.to_nat (DT_BYTES (hp_mtl (huf_draws payload (zlen payload))))) jdt]
    /\ rw_cells usegs m' W [CB (Z.to_nat 8704) jw]
    /\ rw_cells usegs m' DST [CB (Z.to_nat (hp_dbuf (huf_draws payload (zlen payload)))) jd]
    /\ stk usegs m' lo (bv_unsigned sp + -128)
    /\ mem_inv usegs m'
    /\ rheap_pres LB (bv_unsigned sp) m m'
    /\ ps_so s' = ps_so s.

(* [comment removed for export] *)
Lemma RHEAP_disj_split : forall s m l1 b1 l2 b2 l3,
  RHEAP s (l1 ++ b1 :: l2 ++ b2 :: l3) m ->
  blk_addr b1 + blk_size b1 <= blk_addr b2 \/ blk_addr b2 + blk_size b2 <= blk_addr b1.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_h_split ()) ["CANSEC1"] "h01Hh11lh22NDh31Ah41ah52l'h61Eh72HPh82b1h92b2h:2l1h;2l2h<2l3h=1mh>1sp;1p;4p;5p;2p;3p;6p;:p10000p4p70p1000ep4p710R0p8g001VR1p4p70R2g002TR3p4p710p8P2g002kR4p4p710p8P2g003Gp4p710R5p8P2p1003dR6p4p710p8P2P6p4p7210p8P2g004AR6p4p710R7p8P2p1004_p4p710p8P2g005AR8p4p710p8P2p1005^p4p710R9p8P2g006AR2p4p710p8p1006]p4p70P0p8g007RR0p4p70R:g008KR;p4p710p8P:P4p4p7210p8P:g008eR<p4p710R=p8P:P5p8P:P7p8P:P2p4p7210R>p8P:g009AR:p4p710p8P9P7p8P>P=p8P>P7p8g009]j1:Tg00:=j4BTg00;;j5KTP:j2;TP8j35TP3j33Tg00<Mj2=Tg00<gj4ATP;j39Tg00=Fj2@Tg00=`j3<Tg00>:j38Tg00>TR;j17TP<j6JTg00?Sj5ITg00@6j1>Tg00@Oj4ETP6j6DTg00@kl:FTg00B@j3CTP4j4GTP2j5HTf1R2f0R45C1p=0A5124p=2P1P0P;P4CGp=1A3124p=4P1P0P;P2P4DHp=?A3024p=6g00B`g00CY%:1R;p,2rcR6f6R<f4R3f3R8f2R:1024'2'0'2f5R7CBP6f7R>10:2,28,03,27R=P<P4DK%1=,;0P6f8R6108:,23,07,2<P>P7P8P2%:4R=%:2R9g00DSA58:29384A3328A332:'=R?[A384:A3842'=A538:9332[R@A5738937:\?P8P:P2P4CAP4n2001000000120000000X4:W5W1X35R?P@^4:^59^1=^35R5P4P1P>1038,27R=,0<R9P<14<>14<9A91<<14<=1@1<3<38O5b0P?P5P4P1P>P9P3143>1439A91<3143=P?P5P4P1P<1073R=P7147<147=A917714731@173<38O5b03838O5b0%77%78590R8%:0R712>9#11;04X17P2%1>R2%19550R:1?>9EJ1;0:P0%16R:12<=#1R=%7>R9P4DIA50:=,69#>P4P?P5P4P0f:R9#1R=10><R<,26#1R@f9RA#7RB16B=16B@P7%1<950:%79R9/64X17P?P5P4P0%1ARA106>#1R>P9169A169>R>%76RA=9091692P0P9PAP3CE3<P>e38O5b0P@1?6<ED38O5b0O1b2b2W6%>8eM:Fb2W7X<;X91X;;X81W:W=W>o"). Qed.

(* [comment removed for export] *)
Lemma payload_own_disj : forall s m LBX LB b SPC D n,
  RHEAP s (LBX ++ LB) m -> In b LBX -> rclient_range LB SPC D n -> 0 <= n -> D + n <= ATOP -> ATOP < SPC ->
  D + n <= blk_addr b \/ blk_addr b + blk_size b <= D.
Proof.
  intros s m LBX LB b SPC D n HP Hb RR N0 DA AS.
  pose proof (RMalloc_ifaceP.RHEAP_block_range_proof _ _ _ b HP ltac:(apply in_or_app; left; exact Hb))
    as (B1 & B2 & B3 & B4 & B5).
  destruct RR as [RR|[(R1 & R2 & _)|(b' & Hb' & R1 & R2)]].
  - lia.
  - lia.
  - pose proof (blocks_distinct_disjoint s LBX LB m b b' HP Hb Hb') as DJ. lia.
Qed.

(* [comment removed for export] *)
Lemma lb_remove_mid : forall p pre b post, blk_id b = p -> List.NoDup (map blk_id (pre ++ b :: post)) ->
  lb_remove p (pre ++ b :: post) = pre ++ post.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_h_split ()) ["CANSEC1"] "p'0h01bi001bh11lh21Eh31ah41Ah51Nh62NDh74posth83preh91xh:1Hh;2Hbh<2l'h=1ph>2IHh?3IH'h@2NIhA1YhB2b0hC1si011si021ii031np;1p;2p;3p;5p;6p;8p;4g009]j1CTg00>TR0j13Tg013Fj2;Tg008Kj32Tg00Rhj1RTg014Hj5MTg00B@j3Ej2TTg009AR1j2?Tg002Tj35Tg00@6j14Tg00DSR2j2BTg015Mj3XTg0160j28Tg0171j17Tg017Oj16Tg017jj1ATg018Hj2WTg018\j1VTg019Aj6GTg019UR3j2UTg00=Fj2FTg003dj8QTg01:5j3NTg005Aj3<Tg00<Mj2HTg00<gj4LTg00=`j3KTg00>:j3OTg006Aj5PTg004Aj6DTg008ej6JTg01;9j2STg01;Xj5ZTg004_j5YTg002kj4ITg007RR4f1R5f0R632p==g001VR7?E56p=0P7P4P0A<756CIp=91?46p=>A<756p=1A5456p=:P7P4P0P6CIp=@%C7R8P7%35R9f4R:'=f3R;f2R</05R='9#>R>f6R?10;<R@,1:RA';11:<RB528[[^78^07X881=9;%R7RC/9=#>f5RDP;P<P5P6DM11C@,;D11C<528eW6W;X78X071=9Df7RC/;A=28B\>[^78^071=9?10D:R9/9=#>P1p4p710R1%C5R=P2AE<56,?<A5;<5#41?;5'B[R>A5<56#41?<6'BAE;<5,?;RB[A5:;<#41?:<'B\BAX<56P5n2001000000120000000W1X36W4P>^1=^36^41P6P4%3CR110:;,9?R>P5O41:1>#4%>>'BP2f8R>#319C9R9':#4%>9f;R9f9R110?DRB,1>'0';11>D,01528P6f:RA#310C?,91':#410>C,9A#>PAP1P>PCP6O4f>RC101>,19';119>528P8P3f=R?#3f?RE'8#7RF#6RG%4GRHP8%AF,WGRFP7P8%V7RI%36RJfARK'8#7RL#6X07%ALX97109A,1?EGRL,0CPLn20010000002100001000011?A,0C9286X18PF1UGHP3%3Cf@RH'8#7#6RG%4GP3%3E/8K#7#6R3%43RGP8P6P7P8PIfCRF,8J#7RL#6X07%ALX97f<RL,0?,1EEGRM,0HPMn20010000002100001000011C9,0E528P6P8P81T7HRCPCPM11ELR9P8\8/FCP;GQXA3P6O110H9928MP6%3HfBRM'8g011DR91F96%3K/8F=296P9%3FR3fERC'8=296%75#6#4%7<#6]5]2P5%3MRNfDRO'8RPg011dRQ529%7Q#6#4%3ORQfFRR;N51=QRPAP4fGRR10FMRF,9C,:6RQX04P4PNPQX=4%C4RQ%@O10MKRK#@5<41:36X1Qg003Gp4p710RQ%C6RNP2A<;<595;6A5:5;A5:5<'HR2[A5;6<A5;65'HA<:;<95:5[RSA<D:;95D<\2P;P<P5P6CLP6n2001000000120000000X3<X<=W1W4PS^3<^<=^1N^4QP6P4%@CRQ%@FRFP31:3Q1:3F1=33%@M,:31F433K3OO5b:19OKP7P4P0POPKDPEDPRPHEJ%3CP6EDO1b2W5W2g01<=RC929P%7C#6#4g012DW5W2n0110000020100P6P<O2b2bBO1'SX5GP6O1n200110100021010211103bCP7P8PI18JH#7RH#6X07RJ%AHX97RH10A1,1LRA,0?RIEGP7PJPHP?PADZED1;EI11L1,0?528eb?W6W@P5P6O2n2001000000121000000b6b:11B@,;>11B<528eW6W;X78X07W>X88X37P6DYW8X=4o"). Qed.

Lemma lb_remove_mid' : forall p pre b post l, l = pre ++ b :: post -> blk_id b = p -> List.NoDup (map blk_id l) ->
  lb_remove p l = pre ++ post.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_h_split ()) ["CANSEC1"] "h01lh11Hh22Hbh32NDh41bh51ph64posth73prep;1p;3p;2p;6p;4g009]j1:Tg00B@j32Tg005Aj30Tg008Kj31Tg00>TR0j15Tg009Aj23Tg013Fj29Tg01<]j68Tg004Aj67Tg002kj46Tg001VR1g007RR2P0f0R0C6p=4%:1R3f3R4f2R5f1R65215019130P3f4R7A2145501%57f6R8512%46,32f8/95f7R5f5R9501513[[X03%54=129A21749019#4,32P5P8P9P7P6P0E8W3W2P6P0E7W1X03X63X41W7X52o"). Qed.

End CANSEC1.
