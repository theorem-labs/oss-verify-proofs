(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import FseNCount FseLemmas FseAbs FseWriterRT FseNCountRT FseHarness.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Arr Bytes ZBridge Tac InitMem.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import AImg ABase RtCells ABytes AMalloc_iface AProg_kit AF_fse_iface AHarness_iface AKit FsKit AH_fse_kit AH_fse_pure AH_fse_calls AH_fse_tail.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Plain Require Import RF_fse_h_model.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import ShadowTac.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import FseWalkKitF.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_orc_old ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_k12.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.slia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.slia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.flia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.flia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange_nonneg ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_nonneg_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.solve_load ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.solve_load_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.word_eq_tac_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common.FseWalkKit.simpl_arr_sizes_fwk_k12.
(* [comment removed for export] *)

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_hint ::= acc_hint_shadow.
Local Ltac solve_load ::= first [ solve_load_guarded | solve_load_image ].
Local Ltac solve_store ::= solve_store_guarded.
Ltac callt tac := lazymatch goal with
| |- evtF ?segs _ _ (MS _ _ _ _ _ ?m _) => eapply evtF_cut; [ tac | post_call segs m ];
try (lazymatch goal with |- rng _ _ _ => solve_rng end)
end.
Definition off_band (W : list (Z * Z)) : Prop := Forall (fun iv => snd iv <= KLS \/ KHIGH <= fst iv) W.
Definition d1_keep (P : Prop) : Prop := P.
Ltac d1k H := let T := type of H in change (d1_keep T) in H.
Section CANSEC0. Context {rc : runConstT}.
#[using="Type"] Lemma unp_munch_band : forall W (mr mc : amem) X Y, unpoisoned mr X Y -> munch W mr mc -> off_band W -> Y <= KEND ->
unpoisoned mc X Y.
Proof.
intros W mr mc X Y U MU OB YE. pose proof U as (X0 & _ & _).
eapply unpoisoned_agree; [exact U|]. intros s Hs.
Local Ltac2 Set LiaHints.tbl := fun () => "0030>18620679972.1458388245507.2761767359710.8 00000300H00MS1RS2YE2X02Hs1H2H02H42H5S1H1R".
assert (R : KLOW <= s < KHIGH) by (rewrite !shad_div in Hs; unfold ASHOFF, KLOW, KHIGH, KEND in *; Z.div_mod_to_equations; lia).
apply MU. rewrite wa_unsigned by (unfold KLOW, KHIGH in R; lia).
clear - OB R. induction OB as [|[a b] W' H OB' IH]; cbn; [exact I|]. split; [| exact IH]. unfold KLS, KLOW, KHIGH in *. cbn in H. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC0.
Section CANSEC1. Context {rc : runConstT}.
Section D1.
Hypothesis U32R : prod_u32r_stmtA.
Variables (gp tp sp : word) (FR : bvmap 5 word) (fc : bv 32).
Variables (SPA lo F P D B : Z) (pl : list Z) (RNG : footprint).
Notation SP := (bv_unsigned sp).
Hypothesis LOS : lo <= SP - AHARNESS_STACK.
Hypothesis LOC : ATOP + 4096 <= lo.
Hypothesis SPT : SP + 16 <= 2^47.
Hypothesis SP16 : SP mod 16 = 0.
Hypothesis ESPA : SPA = (SP - 192) - (SP - 192) mod 32.
Hypothesis RSTK : rng RNG lo (SP - lo).
Hypothesis RI : rng_aimg RNG.
Hypothesis FH : ablk F (F + 2048).
Hypothesis FC : F + 2048 <= ATOP.
Hypothesis F2048 : F mod 2048 = 0.
Hypothesis RF : rng RNG F 2048.
Hypothesis RSF : rng RNG (shad F) 256.
Hypothesis BLKP : ablk P (P + 16).
Hypothesis P16 : P mod 16 = 0.
Hypothesis RP : rng RNG P 16.
Hypothesis RPS : rng RNG (shad P) 2.
Hypothesis PF : P + 16 <= F \/ F + 2048 <= P.
Hypothesis DLOC : (pl = [] /\ D = AEMPTY) \/ ablk D (D + zlen pl).
Hypothesis D8 : D mod 8 = 0.
Hypothesis RD : rng RNG D (zlen pl).
Hypothesis RDS : rng RNG (shad D) (nshad (zlen pl)).
Hypothesis DP : D + zlen pl <= P \/ P + 16 <= D.
Hypothesis DF : D + zlen pl <= F \/ F + 2048 <= D.
Hypothesis PLB : Forall (fun c => 0 <= c < 256) pl.
Hypothesis SZ26 : zlen pl < 2^26.
Variables (bsz RLOB RHIB : Z).
Hypothesis BLKB : ablk B (B + bsz).
Hypothesis B16 : B mod 16 = 0.
Hypothesis BSZ : 2 <= bsz <= 512.
Hypothesis RB : rng RNG B bsz.
Hypothesis RBS : rng RNG (shad B) (nshad bsz).
Hypothesis BP : B + bsz <= P \/ P + 16 <= B.
Hypothesis BD : B + bsz <= D \/ D + zlen pl <= B.
Hypothesis BF : B + bsz <= F \/ F + 2048 <= B.
Hypothesis BHULL : RLOB mod 4096 = 0 /\ RHIB mod 4096 = 0 /\ RLOB + 64 <= B /\ B + bsz + 64 <= RHIB
/\ rng RNG (shad RLOB) (shlen (RHIB - RLOB)).
Definition W_D : list (Z * Z) := [(P + 8, P + 16); (B, B + bsz); (SPA - 2224, SPA + 88)].
#[using="rc sp lo F D pl LOS LOC SP16 ESPA BLKP RLOB RHIB BLKB"] Lemma WD_off_band : off_band W_D.
Proof.
pose proof (ablk_disj_band _ _ BLKP) as DBP. pose proof (ablk_disj_band _ _ BLKB) as DBB.
pose proof (spa_props5 (bv_unsigned sp) SP16) as SPAP. cbv zeta in SPAP. rewrite <- ESPA in SPAP. destruct SPAP as (SPAB & _ & _).
atop_facts. unfold AHARNESS_STACK in LOS. unfold W_D, off_band, KHIGH, KLS in *.
Local Ltac2 Set LiaHints.tbl := fun () => "0030>47636524364.5668176945999.569384765995.56 00000500E00JS3DBBS3LOS3LOC4SPAB1HS3DBP".
repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma pD1 : forall (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 s10v x28 x29 x30 x31 : word) (m : amem) (Q : machine_state -> Prop)
(tl msv dsz rem : Z) (nc data buf' : list Z) (jB jd : list byte),
fseA pl (zlen pl) = (tl, msv, nc, data, dsz, bsz, rem) ->
rw_cells asegs m SPA [C8 (Z_to_bv 64 (SHF F + 76)); C8 (Z_to_bv 64 (SHF F + 4)); C8 (Z_to_bv 64 F); C8 (Z_to_bv 64 (SHF F + 148));
C8 (Z_to_bv 64 (F + 1760)); C8 (Z_to_bv 64 tl); C8 (Z_to_bv 64 F); CB 24 jd; C8 (Z_to_bv 64 F)] ->
u8arr asegs m (F + 32) (map (Z_to_bv 8) buf') -> length buf' = 512%nat -> firstn (Z.to_nat dsz) buf' = data ->
rw_cells asegs m B [CB (Z.to_nat bsz) jB] ->
rw_cells asegs m P [C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 rem)] ->
rw_cells asegs m (SHF F) (FSH Z64 Z64 Z64 B04 B04) ->
stk asegs m lo SPA -> mem_inv asegs m ->
fse_rt m -> bytes_at asegs m D (map (Z_to_bv 8) pl) ->
unpoisoned m P (P + 16) -> unpoisoned m D (D + zlen pl) -> unpoisoned m B (B + bsz) ->
wr_at asegs m (shad RLOB) (shlen (RHIB - RLOB)) ->
(forall m2 junkF remF (j16 : list byte) (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y22 y26 y28 y29 y30 y31 : word),
fseB_tail pl rem dsz bsz = (junkF, remF) ->
u8arr asegs m2 B (map (Z_to_bv 8) (data ++ junkF)) ->
rw_cells asegs m2 P [C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 remF)] ->
rw_cells asegs m2 SPA [C8 (Z_to_bv 64 (SHF F + 76)); C8 (Z_to_bv 64 (SHF F + 4)); C8 (Z_to_bv 64 F); C8 (Z_to_bv 64 (SHF F + 148));
C8 (Z_to_bv 64 (F + 1760)); C8 (Z_to_bv 64 tl); C8 (Z_to_bv 64 F); C8 (Z_to_bv 64 B); CB 16 j16; C8 (Z_to_bv 64 F)] ->
stk asegs m2 lo SPA -> munch W_D m m2 -> wmono asegs m m2 -> mem_inv asegs m2 ->
evtF asegs RNG Q
(MS (mkR y1 (Z_to_bv 64 SPA) gp tp y5 y6 y7 sp (Z_to_bv 64 SPA) y10 y11 y12 y13 y14 y15 y16 y17
y18 (Z_to_bv 64 2147450880) (Z_to_bv 64 dsz) (Z_to_bv 64 (F + 608)) y22 (Z_to_bv 64 bsz) (Z_to_bv 64 P) (Z_to_bv 64 msv)
y26 (Z_to_bv 64 (SHF F)) y28 y29 y30 y31)
FR (Z_to_bv 64 0x81210) fc None m2 (seg_rom asegs))) ->
evtF asegs RNG Q
(MS (mkR (Z_to_bv 64 0x811a4) (Z_to_bv 64 SPA) gp tp x5 x6 x7 sp (Z_to_bv 64 SPA)
(Z_to_bv 64 B) x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 (F + 1760)) (Z_to_bv 64 2147450880) (Z_to_bv 64 dsz) (Z_to_bv 64 (F + 608)) (Z_to_bv 64 (F + 32))
(Z_to_bv 64 bsz) (Z_to_bv 64 P) (Z_to_bv 64 msv) s10v (Z_to_bv 64 (SHF F)) x28 x29 x30 x31)
FR (Z_to_bv 64 0x811a4) fc None m (seg_rom asegs)).
Proof using All.
intros until jd. intros EA FRA DATAA LB' FBUF BLK PR SH ST MI RT PAY UNP UND UNB WRB K.
pose proof (ablk_lin _ _ FH) as (FH1 & FH2 & FH3 & FH4). unfold AIMG_HI in FH1.
pose proof (ablk_lin _ _ BLKP) as (PL1 & PL2 & PL3 & PL4). unfold AIMG_HI in PL1.
pose proof (ablk_lin _ _ BLKB) as (BL1 & BL2 & BL3 & BL4). unfold AIMG_HI in BL1.
Local Ltac2 Set LiaHints.tbl := fun () => "01Y0?12713651292.185130383073.168  13760571730.17 15270819193.18516340036816.1851700057559.8   17252208333.18118227143992.1591952414532.185 19628242851.16819955159707.18119962924073.19222174313527.8  22266103744.16822971108077.23 23298330693.12523372187914.16723492641683.1112373528761.134 23857759168.18423872474103.13724150941295.18225774293055.16825780320319.7  27723611718.18 28573892092.21729462113472.23 29934734406.16830060324404.15930510794559.13632425817165.21532586253210.16833255794547.16633266593731.16833503950328.16833719989128.10834376128545.7  35128051618.8  35146141675.16835343174615.16835411716338.16835736344964.16836878552440.13338018492403.14338290136343.16738973272592.17638973272592.19239950637341.9  39999590352.10841860328378.16842151071173.18542152988100.16842536083270.9  42542688070.16844211547229.16845535530108.16845650635045.1684567445114.168 4614731385.183 46155823319.1364629200200.166 48647284925.12948666356618.16851361801566.8  51363585374.16851413313480.16852127281523.7  52265662933.16052539698744.18553119579314.16853129809074.7  53576692526.18253679869799.1795382261114.185 55248589467.18155257533481.19256185095336.13157671293478.16858084563251.1685903570185.7   59753648227.16860596996423.18560938062552.7  60948869848.16861041885113.13261913100265.16861919078233.16662701961916.18562702041789.8  62954092739.18563658507757.16863903208344.16864862841078.7  64895283520.16765496908798.18165529336179.14365531440114.15166655676009.1686682763374.181 67305307379.13068408202176.16868506258730.1687029654466.168 8378993656.181 9789840039.143 00001201301L02R03X03Y04D04l05T05U06<06c06d07K07`08608^08o0:S0;Y0=A0>?0?B0?C0?[0@F0@[0AB0Aj0CV0Di0EQ0F90Fa0Gi0H>0HB0HC0HD0HE0HF0Hm0JN0L50LY0M=0Ma0Mb0N70O40Oo0Pg0Ph0R00S30S40S50SY0TA0Um0VU0Vl0WT0WU0WV0WW0WX0X@0YJ0Z]0Z^0[c0\G0]P0^80^`0_90`<0a40a?0af0c10c20cZ0d70d[0e?0fI0fJ0g20g30g40g50g\0hb0iI0j40k@0kh0lo0mV0mW0n^0oB0ojS3LOS3LOC3LB'3FH23PL23BL23BL32F42F63RSP1H2D05LDATA3LMD5LREST2H42BGFS3LOS3LOC2BP3PL33F114SPABS3LOS3LOC3BSZ3LB'3FH23PL23BL13BL22F42F63RSP1H2D05LDATA3LMD5LREST2H42BGS3LOS3LOC3BSZ3LB'3FH23PL23BL13BL22F42F63RSP1H2D05LDATA3LMD5LREST2H42BGFS3LB'3FH23PL23BL22F43F115LDATA3LMD5LREST2BGS3LB'3FH23PL23BL22F45LDATA3LMD5LREST3HB5S3LB'3FH23PL13PL23BL22F45LDATA3LMD5LRESTFS3LB'3FH23PL23BL22F42F65LDATA3LMD5LRESTS3LB'3FH23PL23BL22F42F65LDATA3LMD5LRESTFS3LB'3FH23PL23BL22F42F65LDATA3LMD5LRESTS5F20481H2H02H42H52H9S3LB'3FH23PL23BL22F41HS3LB'3FH23FH43PL23BL22F45LDATA3LMD5LRESTS3LB'3FH23PL23BL2S3LOS3LOC2PF2DP2DF3BSZ2BP2BD2BF5BHULL3LB'3FH13FH23PL13PL23BL13BL22F42F63F123RSP4SPAB1H2D04LENP5LDATAS3LOS3LOC3BSZ3LB'3FH23PL23BL13BL22F42F63RSP1H2D05LDATA3LMD5LREST2H42BGS3LOS3LOC2PF2DP2DF3BSZ2BP2BD2BF5BHULL3LB'3FH13FH23PL13PL23BL13BL22F42F63F123RSP4SPAB1H2D04LENP5LDATA3LMDS3LOS3LOC3LB'3FH23PL23BL22F42F63RSP1H2D02DT5LDATA3LMD5LREST2BGS3LOS3LOC3LB'3FH23PL23BL23BL32F42F63F113RSP1H2D05LDATA3LMD5LREST2H4FS3LOS3LOC2BD3F114SPAB2DTS3LB'3FH23PL23BL22F45LDATA3LMD5LREST3HB52HxS5F20481H2H02H42H52H9S3LB'3FH23PL23BL22F42F65LDATA3LMD5LRESTS3LB'3FH23PL23BL22F45LDATA3LMD5LREST3HB5S3LOS3LOC2PF2DP2DF3BSZ2BP2BD2BF5BHULL3LB'3FH13FH23PL13PL23BL13BL22F42F63F113F123RSP4SPAB1H2D04LENP5LDATA3LMDS3LOS3LOC3BSZ3LB'3FH23PL23PL33BL13BL23BL32F42F63RSP4SPAB1H2D05LDATA3LMD5LREST2H42BGS3LB'3FH23PL23BL22F43F115LDATA3LMD5LRESTS3LB'3FH23PL23BL22F43F115LDATA3LMD5LRESTS3LB'3FH23PL23BL22F43F115LDATA3LMD5LRESTS3LOS3LOC3LB'3FH23PL23BL23BL32F42F63F113RSP1H2D05LDATA3LMD5LREST3HB63HP6S3LB'3FH23FH43PL23BL2S2F6FFFFS3LB'3FH23PL23BL22F42F65LDATA3LMD5LRESTS3LOS3LOC2PF2DP2DF3BSZ2BP2BD2BF5BHULL3LB'3FH13FH23PL13PL23BL13BL22F42F62F93F123RSP4SPAB1H2D04LENPS3LOS3LOC2PF2DP2DF3BSZ2BP2BD2BF3LB'3FH23PL23BL13BL22F42F63F113F123RSP4SPAB1H2D04LENP5LDATA3LMD5LREST2H4S3LB'3FH23PL23BL22F45LDATA3LMD5LRESTS3LB'3FH23PL23BL22F45LDATA3LMD5LRESTS3LB'3FH23PL23BL22F45LDATA3LMD5LRESTFS3LB'3FH13FH23PL23BL2S3LOS3LOC3LB'3FH23PL23BL22F42F63RSP4SPAB1H2D05LDATA3LMD5LRESTS3LOS3LOC3LB'3FH23PL23BL22F42F63RSP1H2D05LDATA3LMD5LREST2BGS3LOS3LOC3LB'3FH23PL23BL22F42F63RSP1H2D05LDATA3LMD5LRESTFS3LOS3LOC3BSZ3LB'3FH23PL23BL13BL22F42F63RSP4SPAB1H2D05LDATA3LMD5LREST2H4S3LOS3LOC3LB'3FH23PL23BL23BL32F42F63F113RSP1H2D05LDATA3LMD5LREST2H4FFS3LB'3FH23PL23BL22F45LDATA3LMD5LRESTS3LB'3FH23PL23BL23BL42F45LDATA3LMD5LRESTS3LOS3LOC2PF2DP2DF3BSZ2BP2BD2BF5BHULL3LB'3FH13FH23PL13PL23BL13BL22F42F63F113F123RSP4SPAB1H2D04LENP5LDATA3LMDS3LB'3FH23PL23BL23BL42F45LDATA3LMD5LRESTS3LB'3FH23PL23BL22F42HpS3LB'3FH23FH43PL23BL22F45LDATA3LMD5LRESTFFFFS3LB'3FH23PL23BL22F45LDATA3LMD5LREST3HB5S3LOS3LOC3BSZ3LB'3FH23PL23PL33BL13BL22F42F63RSP1H2D05LDATA3LMD5LREST2H42BGS3LOS3LOC3LB'3FH23FH33PL23BL13BL23BL32F42F63F113RSP1H2D05LDATA3LMD5LREST2H43HB63HP2FS3LOS3LOC3LB'3FH23PL23BL13BL22F42F63RSP1H2D05LDATA3LMD5LREST2H42BG2EQS3LB'3FH23PL23BL22F45LDATA3LMD5LRESTS3LOS3LOC3BSZ3LB'3FH23PL23BL13BL22F42F63RSP1H2D02DT5LDATA3LMD5LREST2H42BGS3BSZ3LB'3FH23PL23BL22F45LDATA3LMD5LRESTS3BSZ3LB'3FH23PL23BL22F45LDATA3LMD5LRESTS3LB'3FH23PL23BL22F44SPABS3LOS3LOC3BSZ3LB'3FH23PL23BL23BL32F42F63RSP1H2D05LDATA3LMD5LREST2H4S3SPT3LB'3FH23PL23BL22F42F63RSP5SPA882D05LDATA3LMD5LRESTS2BF2F63F11S3LB'3FH23PL23BL22F42F65LDATA3LMD5LRESTS3LOS3LOC3BSZ3LB'3FH23PL23BL13BL22F42F63RSP4SPAB1H2D05LDATA3LMD5LREST2H42BGFS3LB'3FH13FH23PL23BL22F45LDATA3LMD5LRESTS3LB'3FH23PL23BL22F42B12B22B3S3LB'3FH23PL23BL22F45LDATA3LMD5LRESTS3LB'3FH23PL23BL22F45LDATA3LMD5LRESTS3LOS3LOC3SPT3LB'3FH23PL23BL22F42F63RSP4SPAB5SPA881H2D05LDATA3LMD5LREST2BGFS3LB'3FH23PL23BL22F43F125LDATA3LMD5LRESTFFFS3LB'3FH23PL23BL22F42F65LDATA3LMD5LRESTS3LOS3LOC3BSZ3LB'3FH23PL23BL13BL22F42F63RSP1H2D05LDATA3LMD5LREST2H42BGS3LB'3FH23PL23BL22F42F65LDATA3LMD5LRESTS3LB'3FH23PL23BL22F42F65LDATA3LMD5LREST3HB5S3LOS3LOC3BSZ3LB'3FH23FH33PL23BL13BL22F42F63RSP4SPAB1H2D05LDATA3LMD5LREST2H4S3LB'3FH23PL23PL43BL22F45LDATA3LMD5LRESTS3LOS3LOC2DP3BSZ5BHULL3LB'3FH13FH23PL13PL23BL13BL22F43F123RSP4SPAB1H2D0S3LB'3FH23PL23BL22F42F65LDATA3LMD5LRESTFS3LOS3LOC3BSZ3LB'3FH23FH33PL23BL13BL22F42F63RSP1H2D05LDATA3LMD5LREST2H4S3LB'3FH23PL23BL22F45LDATA3LMD5LRESTS3LB'3FH23PL23BL13BL22F45LDATA3LMD5LREST".
pose proof (fsh_unp_data m F F2048 ltac:(lia) ltac:(unfold KEND; lia) _ _ _ _ SH) as UDA.
pose proof (fsh_wr m F _ SH ltac:(reflexivity)) as WSH.
assert (AB : all_bytes pl) by (apply Forall_all_bytes; exact PLB).
pose proof (fseA_facts pl (zlen pl) AB ltac:(lia)) as FACTS. rewrite EA in FACTS.
destruct FACTS as (F1 & F2 & V & F4 & _ & F6 & F7 & F8 & F9 & F10 & F11 & F12).
unfold FSE_MIN_TABLELOG, FSE_MAX_TABLELOG in *.
pose proof WD_off_band as OBD.
unfold W_D in *. unfold SHF, FSH, AHARNESS_STACK in *.
pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
pose proof (spa_props5 SP SP16) as SPAP. cbv zeta in SPAP. rewrite <- ESPA in SPAP. destruct SPAP as (SPAB & SPA32 & SPA88).
atop_facts.
assert (D0 : 0 < D /\ D + zlen pl <= ATOP).
{ destruct DLOC as [[-> ->]|BB]; [unfold AEMPTY; cbn; lia| pose proof (ablk_lin _ _ BB) as (B1 & B2 & B3 & B4); unfold AIMG_HI in B1; lia]. }
destruct D0 as [D0 DT].
assert (BLKD : 0 < zlen pl -> ablk D (D + zlen pl)) by (intros Hp; destruct DLOC as [[-> _]|X]; [cbn in Hp; lia| exact X]).
assert (RFRA : rng RNG SPA 88) by (eapply rng_sub'; [exact RSTK| lia]).
assert (RSTKA : rng RNG lo (SPA - lo)) by (eapply rng_sub'; [exact RSTK| lia]).
assert (LENP : zlen (map (Z_to_bv 8) pl) = zlen pl) by (rewrite length_map; reflexivity).
assert (LDATA : length data = Z.to_nat dsz) by (unfold FseNCount.Zlength in F9; lia).
assert (DSZ : zlen data = dsz) by (rewrite LDATA; lia).
assert (LMD : length (map (Z_to_bv 8) data) = Z.to_nat dsz) by (rewrite length_map; exact LDATA).
assert (SRC : bytes_at asegs m (F + 32) (map (Z_to_bv 8) data)).
{ rewrite <- FBUF, <- firstn_map. apply bytes_at_firstnF; [exact (proj1 DATAA)| rewrite length_map; lia]. }
clear DATAA.
apply (rw_cells_split_CB _ _ _ [] _ _ [] [Z.to_nat dsz; Z.to_nat (bsz - dsz)]) in BLK; [| cbn; lia]. cbn [mk_CB_cells app] in BLK.
apply (proj1 (rw_cells_app _ _ _ [_] _)) in BLK. destruct BLK as [BLK1 BLK2]. cbn [cells_size csize Nat.add] in BLK2.
replace (B + Z.of_nat (Z.to_nat dsz + 0)) with (B + dsz) in BLK2 by lia.
assert (LREST : length (firstn (Z.to_nat (bsz - dsz)) (skipn (Z.to_nat dsz) jB)) = Z.to_nat (bsz - dsz))
by (destruct BLK2 as [[[Hn _] _] _]; exact Hn).
destruct BHULL as (H1 & H2 & H3 & H4 & H5).
destruct (block_hull RNG m B dsz RLOB RHIB ltac:(lia) H1 H2 H3 ltac:(lia) ltac:(lia) H5 WRB) as (RHB & WHB & HB1 & HB2 & HB3 & HB4 & HB5 & HB6).
pose proof (hull_props B dsz ltac:(lia)) as (HP1 & HP2 & HP3 & HP4 & HP5 & HP6).
assert (S72 : shad (F + 576) - shad F = 72) by (rewrite !shad_div; clear - F2048; Z.div_mod_to_equations; lia).
assert (F64 : F mod 64 = 0 /\ (F + 576) mod 64 = 0) by (clear - F2048; Z.div_mod_to_equations; lia).
assert (WHF : wr_at asegs m (shad F) (shad (F + 576) - shad F)) by (rewrite S72; eapply wr_at_sub; [exact WSH| lia| lia]).
assert (RHF : rng RNG (shad F) (shad (F + 576) - shad F)) by (rewrite S72; eapply rng_sub'; [exact RSF| lia]).
clear SH WRB H5 WSH.
d1k SP16. d1k ESPA. d1k F2048. d1k P16. d1k D8. d1k B16. d1k PF. d1k DLOC. d1k DP. d1k DF. d1k BP. d1k BD. d1k BF. d1k SPA32.
d1k H1. d1k H2. d1k HB3. d1k HB4. d1k HP3. d1k HP4. d1k F64.
pose proof (munch_refl [(P + 8, P + 16); (B, B + bsz); (SPA - 2224, SPA + 88)] m) as MU. pose proof (wmono_refl asegs m) as WM.
destruct RT as (GOT & RIC & REAL & SHB & INI & LAY & GOTM).
zstep. zstep. zstep. zstep.
rename m0 into m1.
assert (UNB1 : unpoisoned m1 B (B + dsz)).
{ eapply unpoisoned_sub; [eapply (unp_munch_band _ m m1 B (B + bsz) UNB MU OBD); unfold KEND; lia| lia| lia]. }
assert (UDA1 : unpoisoned m1 (F + 32) (F + 32 + dsz)).
{ eapply unpoisoned_sub; [eapply (unp_munch_band _ m m1 (F + 32) (F + 544) UDA MU OBD); unfold KEND; lia| lia| lia]. }
(eapply evtF_cut;
[ eapply (amemcpy_z RNG) with (RLO1 := F) (RHI1 := F + 576) (RLO2 := hull_lo B) (RHI2 := hull_hi B dsz) (lo := lo)
(src := map (Z_to_bv 8) data);
first [ assumption | exact BLK1 | (rewrite LMD; reflexivity)
| (apply ablk_app_blk; [eapply ablk_sub; [exact FH| lia| lia]| lia]) | (apply ablk_app_blk; [eapply ablk_sub; [exact BLKB| lia| lia]| lia])
| (clear - BF F6 F11; unfold d1_keep in *; lia)
| (left; lia)
| (repeat split; first [ assumption | exact (proj1 F64) | exact (proj2 F64) | lia | unfold KEND; lia ])
| (eapply rng_sub'; [exact RF| lia]) | (eapply rng_sub'; [exact RB| lia]) | (unfold KHIGH; lia) | lia ]
| ]).
intros ms' PO. cbv beta delta [amemcpy_postz] in PO.
destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & E & MUc & WMc & MIc & STc & CHc & BYc).
subst ms'.
clear BLK1 ST SRC MI BYc UNB1 UDA1.
d1k PR. d1k PAY.
transport_after_call_fast asegs m1 m2 MUc WMc.
unfold d1_keep in PR, PAY.
apply (rw_cells_transport asegs [(SPA - 2224, SPA); (B, B + dsz)] m1 m2 P _) in PR; [| exact MUc| exact WMc| cbn [disjoint_from cells_size csize Nat.add]; clear - BP F11 F6 SPAB LOS LOC PL3 RSP; unfold d1_keep in *; lia].
apply (bytes_at_transport asegs [(SPA - 2224, SPA); (B, B + dsz)] m1 m2 D _) in PAY; [| exact MUc| rewrite LENP; cbn [disjoint_from]; clear - BD F11 F6 SPAB LOS LOC DT RSP; unfold d1_keep in *; lia].
clear MUc WMc. try clear m1.
replace (ret_pc (Z_to_bv 64 528820)) with (Z_to_bv 64 528820) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
assert (RT2 : fse_rt m2) by exact (conj GOT (conj RIC (conj REAL (conj SHB (conj INI (conj LAY GOTM)))))).
zstep. if_cases BG; zify_cond BG.
-
assert (EQ : dsz = bsz) by lia.
apply (K m2 [] rem (skipn 8 jd)).
+ unfold fseB_tail. replace (Z.to_nat (bsz - dsz)) with 0%nat by lia. reflexivity.
+ rewrite app_nil_r. exact (u8arr_of_rw_cells asegs m2 B _ _ CHc).
+ exact PR.
+ exact FRA.
+ exact STc.
+ exact MU.
+ exact WM.
+ exact MIc.
-
zstep. zstep. zstep. zstep.
replace (Z_to_bv 64 (bsz - dsz)) with (Z_to_bv 64 (Z.of_nat (Z.to_nat (bsz - dsz)))) by (f_equal; lia).
replace (Z_to_bv 64 (dsz + B)) with (Z_to_bv 64 (B + (dsz + Z.of_nat (length (@nil Z))))) by (f_equal; change (Z.of_nat (length (@nil Z))) with 0; lia).
assert (UNP2 : unpoisoned m2 P (P + 16)) by (eapply (unp_munch_band _ m m2); [exact UNP| exact MU| exact OBD| unfold KEND; lia]).
assert (UND2 : unpoisoned m2 D (D + zlen pl)) by (eapply (unp_munch_band _ m m2); [exact UND| exact MU| exact OBD| unfold KEND; lia]).
assert (UNB2 : unpoisoned m2 B (B + bsz)) by (eapply (unp_munch_band _ m m2); [exact UNB| exact MU| exact OBD| unfold KEND; lia]).
assert (BA2 : u8arr asegs m2 B (map (Z_to_bv 8) (data ++ []) ++ firstn (Z.to_nat (bsz - dsz)) (skipn (Z.to_nat dsz) jB))).
{ rewrite app_nil_r. eapply u8arr_of_two_cb; [exact CHc|]. replace (B + Z.of_nat (Z.to_nat dsz)) with (B + dsz) by lia. exact BLK2. }
eapply (tail_loopA U32R RNG gp tp sp (Z_to_bv 64 (Z.shiftr F 3 + ASHOFF)) FR fc m2 SPA (F + 608) P D B pl data msv dsz bsz lo Q)
with (f := Z.to_nat (bsz - dsz)) (size := rem) (acc := []) (rest := firstn (Z.to_nat (bsz - dsz)) (skipn (Z.to_nat dsz) jB)) (m1 := m2);
[ first [ exact RT2 | exact UNP2 | exact UND2 | exact UNB2 | exact RSTKA | exact BLKD | assumption | (unfold KHIGH; lia) | lia ] .. | | | | | | ].
+ lia.
+ exact LREST.
+ change (Z.of_nat (length (@nil Z))) with 0. lia.
+ lia.
+ split; [exact BA2|]. split; [exact PR|]. split; [exact STc|]. split; [apply munch_refl|]. split; [apply wmono_refl| exact MIc].
+ intros m3 junkF remF y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y22 y26 y28 y29 y30 y31 ETL (BA3 & PR3 & ST3 & MU3 & WM3 & MI3) RR.
apply (K m3 junkF remF (skipn 8 jd) y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y22 y26 y28 y29 y30 y31).
* unfold fseB_tail. exact ETL.
* rewrite app_nil_r in BA3. exact BA3.
* exact PR3.
* eapply rw_cells_transport; [exact FRA| exact MU3| exact WM3|]. cbn [disjoint_from cells_size csize Nat.add]. lia.
* exact ST3.
* eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU3]. unfold sub_fp. cbn [outside]. intros x Hx. lia.
* eapply wmono_trans; [exact WM| exact WM3].
* exact MI3.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End D1.
End CANSEC1.
