(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import FseNCount FseLemmas FseHarness.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Arr Bytes ZBridge Tac InitMem.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import BImg ABase RtCells ABytes AF_fse_iface AHarness_iface AKit FsKit AH_fse_kit AH_fse_pure AH_fse_calls.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import ShadowTac.
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
Ltac bcase K := if_cases K; zify_cond K.
Ltac callt tac := lazymatch goal with
| |- evtF ?segs _ _ (MS _ _ _ _ _ ?m _) => eapply evtF_cut; [ tac | post_call segs m ];
try (lazymatch goal with |- rng _ _ _ => solve_rng end)
end.
Section CANSEC1. Context {rc : runConstT}.
Section B1.
Hypothesis U32R : prod_u32r_stmtA.
Variables (gp tp sp : word) (FR : bvmap 5 word) (fc : bv 32).
Variables (SPA lo F P D : Z) (pl : list Z) (RNG : footprint).
Notation SP := (bv_unsigned sp).
Hypothesis LOS : lo <= SP - AHARNESS_STACK.
Hypothesis LOC : ATOP + 4096 <= lo.
Hypothesis SPT : SP + 16 <= 2^47.
Hypothesis SP16 : SP mod 16 = 0.
Hypothesis ESPA : SPA = (SP - 224) - (SP - 224) mod 32.
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
Definition pB1_post (m : amem) (tl msv r2 : Z) (jb jc jd : list byte) : machine_state -> Prop :=
fun ms' => exists m' (y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word) (jb' jd' : list byte),
ms' = MS (mkR (Z_to_bv 64 0x80f28) (Z_to_bv 64 SPA) gp tp y5 y6 y7 sp (Z_to_bv 64 SPA) y10 y11 y12 y13 y14 y15 y16 y17
(Z_to_bv 64 tl) (Z_to_bv 64 ASHOFF) (Z_to_bv 64 (2^tl - 1)) (Z_to_bv 64 msv) (Z_to_bv 64 F)
(Z_to_bv 64 P) (Z_to_bv 64 (F + 608)) (Z_to_bv 64 (SHF F + 4)) (Z_to_bv 64 (SHF F)) (Z_to_bv 64 (SHF F + 76))
y28 y29 y30 y31)
FR (Z_to_bv 64 0x80f3c) fc None m' (seg_rom bsegs)
/\ munch [(P + 8, P + 16); (SPA - 2208, SPA + 120); (F + 608, F + 1120); (SHF F, SHF F + 256)] m m'
/\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo SPA
/\ prod_atA m' P D r2
/\ rw_cells bsegs m' SPA [CB 24 jb'; C8 (Z_to_bv 64 (SHF F + 76)); C8 (Z_to_bv 64 (SHF F + 4)); C8 (Z_to_bv 64 F); CB 16 jc;
C8 (Z_to_bv 64 (SHF F + 148)); C8 (Z_to_bv 64 tl); C8 (Z_to_bv 64 F); C8 (Z_to_bv 64 msv); CB 16 jd';
C8 (Z_to_bv 64 F)]
/\ rw_cells bsegs m' (F + 608) [CB 512 (repeat (Z_to_bv 8 0) 512)]
/\ rw_cells bsegs m' (SHF F) (FSH Z64 Z64 F8S BF8 BF8).
#[using="rc U32R LOS LOC SPT SP16 ESPA RSTK RI FH F2048 RF RSF BLKP P16 RP RPS PF DLOC D8 RD RDS DP DF PLB SZ26"] Lemma pB1 : forall (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 s2v s4v s5v s7v s8v x28 x29 x30 x31 : word) m (tl r1 msv r2 : Z)
(jb jc jd njunk : list byte),
uint32Range pl (zlen pl) 5 12 = (tl, r1) -> uint32Range pl r1 0 255 = (msv, r2) ->
mem_inv bsegs m -> stk bsegs m lo SPA ->
prod_atA m P D (zlen pl) -> bytes_at bsegs m D (map (Z_to_bv 8) pl) ->
rt_got m -> rt_got_ric m -> rt_shbase m -> rt_inited m -> rt_layout m -> rt_real_mem m ->
rw_cells bsegs m 0x99930 [C8 (Z_to_bv 64 0x9b778)] ->
unpoisoned m P (P + 16) -> unpoisoned m D (D + zlen pl) ->
rw_cells bsegs m SPA [CB 40 jb; C8 (Z_to_bv 64 F); CB 16 jc; C8 (Z_to_bv 64 (SHF F + 148)); CB 40 jd; C8 (Z_to_bv 64 F)] ->
rw_cells bsegs m (F + 608) [CB 512 njunk] ->
rw_cells bsegs m (SHF F) (FSH F8S F8S F8S BF8 BF8) ->
evtF bsegs RNG (pB1_post m tl msv r2 jb jc jd)
(MS (mkR (Z_to_bv 64 0x80ec0) (Z_to_bv 64 SPA) gp tp x5 x6 x7 sp (Z_to_bv 64 SPA) (Z_to_bv 64 P) x11 x12 x13 x14 x15 x16 x17
s2v (Z_to_bv 64 ASHOFF) s4v s5v (Z_to_bv 64 F) s7v s8v (Z_to_bv 64 (SHF F + 4)) (Z_to_bv 64 (SHF F))
(Z_to_bv 64 (SHF F + 76)) x28 x29 x30 x31)
FR (Z_to_bv 64 0x80ec0) fc None m (seg_rom bsegs)).
Proof.
intros until njunk. intros E1 E2 MI ST PR PAY GOT RIC SHB INI LAY REAL GOTM UNP UND FRA NCJ SH.
pose proof (ablk_lin _ _ FH) as (FH1 & FH2 & FH3 & FH4). unfold AIMG_HI in FH1.
pose proof (ablk_lin _ _ BLKP) as (PL1 & PL2 & PL3 & PL4). unfold AIMG_HI in PL1.
unfold SHF, FSH, AHARNESS_STACK in *.
pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. unfold KEND, KHIGH in *.
pose proof (spa_props5 SP SP16) as SPAP. cbv zeta in SPAP. rewrite <- ESPA in SPAP. destruct SPAP as (SPAB & SPA32 & SPA88).
Local Ltac2 Set LiaHints.tbl := fun () => "0210?10341277979.20212319391179.17613400123203.33 14252587283.10914252587283.11114455599423.11114461882242.12 14723231628.14514939502107.15115544262045.11115647574602.17615794320739.17615904717071.23 16062143640.20316443498762.1761667148538.102 18026261971.17318026261971.1741948122878.111 1948122878.128 19729040337.17423492641683.10923492641683.11323492641683.11423904006361.17624522298490.15925059262615.14525349552462.98 25675713676.15925715512380.17526918830103.15927164210705.17327164210705.17427719924594.10927989303397.17628087563647.12828089650114.10 28381206279.14829179601969.12829181696652.12 29782367974.11329782367974.12029782367974.17329782367974.17529782367974.98 29782367974.99 30096756805.99 30495313917.17632815121182.17 32815121182.23 3522744003.126 3522744003.128 35293574422.19035495549846.14535495549846.15935945580172.14535968369417.11135968369417.1283839306879.106 39867114339.17339867114339.17640081792849.12641107712084.10 41109804777.11141161917423.14342146777215.11142146777215.12842146777215.17643498632653.14443781234822.22 43781234822.23 4398706810.173 46696440342.12646856496503.17646861708755.17346861708755.17447888061852.19748653510305.10049846535446.17250692615968.10351357505765.11151357505765.12851357505765.17651990736557.17452544056194.11152544056194.1285377903808.111 5377903808.128 53857197511.17354070872470.14155144173634.12655581718629.17555904264338.10556041590156.14756170137001.17556170427449.11056170427577.12757022093363.17657261936172.17657391983121.17357391983121.1745847737990.174 59314873579.1435972701590.158 59851873173.14959860634550.14260592901373.11160592901373.12861035741573.10661144500785.17662376611962.17462536353548.15962697932550.11162697932550.12862697932550.1766340407843.176 64950891026.1996495453569.25  6495453569.26  65223193331.17566135216254.40 66135216371.35 66151427842.16 66775607233.1757673273466.158 8555112874.113 8567084618.176 89901372.158   9214086685.198 00000900`01<01E01N01O01P01Y01Z01c02`02m03B03K03T03a03j04304@04M04Z04c04o05;05<05E05R05[05d05m06:06m07`07i08208308408G08H08I08R08_08h09109:09C09N09m0:=0:Y0:b0:k0;40;=0;F0;S0<J0=A0=`0=m0>:0>G0>H0>I0>V0?50?T0@30@<0@X0A40A=0AF0AS0A\0Ae0An0B:0BC0C40C50C60C70Cj0DQ0E80Ee0FR0F_0Fh0G10G:0H<0Hi0I70IE0IS0I\0Ie0JX0KK0L>0LN0LW0Ld0M10MP0Mo0NA0NN0NW0Nd0OR0P@0Pn0Po0Q80QS0Qm0R60R^0SA0SP0SY0Sb0TG0UD0UM0UVS3FH23PL2S3LOS3LOC3FH23FH33PL23PL33RSP4SPAB2D01HS5F20482K81H2H02H42H52H93H14S3FH23PL2S3FH23PL2FFS3FH23PL2FS3FH23PL2S3LOS3LOC4SP165F20482PF2DP2DF3FH13FH23PL23RSP4SPAB5SPA322D01HS3FH13FH23PL2S5F20481H2H02H42H52H9S3FH23PL2S3FH23PL2S3FH23PL23BSFS3FH23PL2S3FH23PL2S3FH23PL13PL2S3FH23PL13PL2S3FH23PL23RSPS3FH23PL2S3FH23PL22N0S3FH23PL22N0FS3FH23PL2S3FH23PL23BSFS3FH23PL2S3FH23PL2S3FH23PL2S3FH23PL23BSFS3LOS3LOC4SP162PF2DP2DF3FH23PL23RSP4SPAB5SPA322D01HS3LOS3LOC4SP162PF2DP2DF3FH23PL23RSP4SPAB5SPA322D01HS3FH23PL2S3FH23PL2FFS2FH5F20481H2H03H19FFS3FH23PL2S3FH23PL23DL2S3FH23PL2S3FH23PL2S3FH23PL2S3FH23PL2S3FH23PL21HS3LOS3LOC3FH23PL23RSP4SPAB2D01HS3DBP1H2H02H42H5S3DBD3DL13DL43DBP1H2H02H42H5S3FH23PL2S3FH23PL2S3FH23PL2S3FH23PL2S3FH23PL2S3FH23PL23BSFS3LOS3LOC4SP163P162PF2DP2DF3FH23PL23RSP4SPAB5SPA322D01HS3LOS3LOC4SP163P162PF2DP2DF3FH23PL23RSP4SPAB5SPA322D01HS3LOS3LOC3FH23PL23RSP4SPAB2D01HS3FH13FH23PL2S3FH13FH23PL2S3FH23PL23R1RFFS3FH23PL23TLRS3LOS3LOC3FH23PL23RSP4SPAB2D01HS3LOS3LOC3FH23PL23RSP4SPAB2D01HS3LOS3LOC3FH23PL23RSP4SPAB2D01HS3FH23PL2S3PL13PL43DBP3DBF1H2H02H42H5S3DBD3DL13DL43DBF1H2H02H42H5S3FH23PL2S3FH23PL2S3FH23FH43PL2S3FH23PL2S3FH23PL2S3FH23PL2S3FH23PL22H0S3FH23PL2S3LOS3LOC4BLKP2PF2DP2DF3FH23PL23RSP4SPAB3BSF2D01HFFFS3LOS3LOC4SP162PF2DP2DF3FH23PL23RSP4SPAB5SPA322D01HS3LOS3LOC3FH23FH33PL23PL33RSP4SPAB2D01HS3LOS3LOC3FH23FH33PL23PL33RSP4SPAB2D01HS3LOS3LOC2PF3FH23FH33PL23PL33RSP4SPAB2D02DT1HS3LOS3LOC2PF3FH23FH33PL23PL33RSP4SPAB2D02DT1HS3FH23FH43PL2S3FH23PL2S3FH23PL2S3FH23PL2S3LOS3LOC4SP162PF2DP2DF3FH23PL23RSP4SPAB5SPA323BSF4SHDJ2D03PSH1B1HS5F20482PF2DP2DF3FH13FH33PL13PL31H2H03H193H34S3FH23PL24SPABS3FH23PL24SPABS3FH23PL24SPABS3FH23PL2S3FH23PL2S3LOS3LOC4SP162PF2DP2DF3FH23PL23RSP4SPAB5SPA322D01HS3LOS3LOC4SP162PF2DP2DF3FH23PL23RSP4SPAB5SPA322D01HS3LOS3LOC4SP162PF2DP2DF3FH23PL23RSP4SPAB5SPA322D01HS3FH23PL23TLR2KTS3FH23PL2S3FH23PL23TLRS3FH23PL23TLRS3LOS3LOC3FH23PL23RSP4SPAB2D01HS3LOS3LOC3FH23PL23RSP4SPAB2D01HS3FH23PL22B12B22B3S3FH23FH43PL2S3FH23PL2S3FH23PL23BSFS3LOS3LOC3SPT4ESPA3FH23PL23RSP4SPAB5SPA882D01HS3LOS3LOC3SPT4ESPA3FH23PL23RSP4SPAB5SPA882D01HS3LOS3LOC3SPT4ESPA3FH23PL23RSP4SPAB5SPA882D01HFS3FH23PL2S3LOS3LOC3PL34SPAB2H42H52H9S3LOS3LOC4SPAB2DT2H42H52H9S3FH23PL2S5F20483P162PF1H2H02H42H52H93H103H143H19S5F20482D82DF2N01H2H42H52H93H103H14S5F20481H2H02H4S3FH23PL2S3FH23PL2S3LOS3LOC3FH23PL23RSP4SPAB2D02DT2E01HS3LOS3LOC4SP165F20482PF2DP2DF3FH13FH23PL23RSP4SPAB5SPA322D01HS3FH23PL2S3FH23PL2".
replace (shad F) with (Z.shiftr F 3 + ASHOFF) in RSF by (unfold shad; lia).
assert (BSF : 2147450880 <= Z.shiftr F 3 + ASHOFF /\ Z.shiftr F 3 + ASHOFF + 256 <= 17594333495296) by (rewrite Z.shiftr_div_pow2 by lia; unfold ASHOFF; Z.div_mod_to_equations; lia).
assert (SHDJ : F + 2048 <= Z.shiftr F 3 + ASHOFF \/ Z.shiftr F 3 + ASHOFF + 256 <= F).
{ rewrite Z.shiftr_div_pow2 by lia. unfold ASHOFF. unfold ablk, AIMG_HI, KLS in FH. Z.div_mod_to_equations. lia. }
assert (BLKD : 0 < zlen pl -> ablk D (D + zlen pl)).
{ intros H0. destruct DLOC as [[-> _]|B]; [cbn in H0; lia| exact B]. }
assert (D0 : 0 < D /\ D + zlen pl <= ATOP).
{ destruct DLOC as [[-> ->]|B]; [unfold AEMPTY; cbn; lia| pose proof (ablk_lin _ _ B) as (B1 & B2 & B3 & B4); unfold AIMG_HI in B1; lia]. }
destruct D0 as [D0 DT].
assert (PSH : P + 16 <= Z.shiftr F 3 + ASHOFF \/ Z.shiftr F 3 + ASHOFF + 256 <= P).
{ unfold ablk, AIMG_HI, KLS in BLKP. lia. }
assert (DSH : D + zlen pl <= Z.shiftr F 3 + ASHOFF \/ Z.shiftr F 3 + ASHOFF + 256 <= D).
{ destruct DLOC as [[-> ->]|B]; [unfold AEMPTY; cbn; lia| unfold ablk, AIMG_HI, KLS in B; lia]. }
assert (LENP : zlen (map (Z_to_bv 8) pl) = zlen pl) by (rewrite length_map; reflexivity).
assert (RFRA : rng RNG SPA 120) by (eapply rng_sub'; [exact RSTK| lia]).
pose proof (munch_refl [(P + 8, P + 16); (SPA - 2208, SPA + 120); (F + 608, F + 1120); (Z.shiftr F 3 + ASHOFF, Z.shiftr F 3 + ASHOFF + 256)] m) as MU.
pose proof (wmono_refl bsegs m) as WM.
assert (UNPX : forall m', munch [(P + 8, P + 16); (SPA - 2208, SPA + 120); (F + 608, F + 1120); (Z.shiftr F 3 + ASHOFF, Z.shiftr F 3 + ASHOFF + 256)] m m' ->
unpoisoned m' P (P + 16)).
{ intros m' MU'. pose proof (ablk_disj_band _ _ BLKP) as DBP. pose proof (ablk_disj_band _ _ FH) as DBF. unfold KLS in DBP, DBF.
eapply unpoisoned_munch; [exact UNP| exact MU'|]. rewrite !shad_div, !Z.shiftr_div_pow2 by lia. unfold ASHOFF. cbn [disjoint_from]. change (2^3) with 8.
split; [clear - DBP PL1; Z.div_mod_to_equations; lia|]. split; [clear - DBP SPAB LOS LOC PL3; Z.div_mod_to_equations; lia|].
split; [clear - DBP DBF PL1 PL4 FH1 FH4; Z.div_mod_to_equations; lia|]. split; [clear - PF P16 F2048; Z.div_mod_to_equations; lia| exact I]. }
assert (UNDX : forall m', munch [(P + 8, P + 16); (SPA - 2208, SPA + 120); (F + 608, F + 1120); (Z.shiftr F 3 + ASHOFF, Z.shiftr F 3 + ASHOFF + 256)] m m' ->
unpoisoned m' D (D + zlen pl)).
{ intros m' MU'. destruct (Z.eq_dec (zlen pl) 0) as [E0|N0].
- rewrite E0, Z.add_0_r. apply unpoisoned_nil. lia.
- pose proof (ablk_disj_band _ _ (BLKD ltac:(lia))) as DBD. pose proof (ablk_lin _ _ (BLKD ltac:(lia))) as (DL1 & DL2 & DL3 & DL4). unfold AIMG_HI in DL1.
pose proof (ablk_disj_band _ _ FH) as DBF. pose proof (ablk_disj_band _ _ BLKP) as DBP. unfold KLS in DBD, DBF, DBP.
eapply unpoisoned_munch; [exact UND| exact MU'|]. rewrite !shad_div, !Z.shiftr_div_pow2 by lia. unfold ASHOFF. cbn [disjoint_from]. change (2^3) with 8.
split; [clear - DBD DBP PL1 PL4 DL1 DL4; Z.div_mod_to_equations; lia|]. split; [clear - DBD SPAB LOS LOC DT; Z.div_mod_to_equations; lia|].
split; [clear - DBD DBF DL1 DL4 FH1 FH4; Z.div_mod_to_equations; lia|]. split; [clear - DF D8 F2048 N0; Z.div_mod_to_equations; lia| exact I]. }
clear UNP UND.
pose proof (uint32Range_spec pl (zlen pl) 5 12 ltac:(apply Forall_all_bytes; exact PLB) ltac:(lia) ltac:(lia) ltac:(change (2^32) with 4294967296; lia)) as S1.
rewrite E1 in S1. destruct S1 as (TLR & R1R & _).
zstep. zstep. zstep.
zstep.
unfold prod_u32r_stmtA, APROD_U32R in U32R.
callt ltac:(eapply U32R with (SPV := SPA) (P := P) (D := D) (pl := pl) (size := zlen pl) (mn := 5) (mx := 12) (lo := lo));
[ first [ reflexivity | assumption | split; assumption | lia | (unfold KHIGH; lia) | (clear - P16; Z.div_mod_to_equations; lia)
| exact (UNPX _ MU) | exact (UNDX _ MU) ] .. | ].
clear PR. rename POST into PR. rename PC into ST. rewrite E1 in PR |- *. cbn [fst snd] in PR |- *. unfold prod_atA in PR.
zstep. zstep. zstep. zstep.
zstep.
pose proof (uint32Range_spec pl r1 0 255 ltac:(apply Forall_all_bytes; exact PLB) ltac:(lia) ltac:(lia) ltac:(change (2^32) with 4294967296; lia)) as S2.
rewrite E2 in S2. destruct S2 as (MSR & R2R & _).
callt ltac:(eapply U32R with (SPV := SPA) (P := P) (D := D) (pl := pl) (size := r1) (mn := 0) (mx := 255) (lo := lo));
[ first [ reflexivity | assumption | split; assumption | lia | (unfold KHIGH; lia) | (clear - P16; Z.div_mod_to_equations; lia)
| exact (UNPX _ MU) | exact (UNDX _ MU) ] .. | ].
try clear PR. rename POST into PR. rename PC into ST. rewrite E2 in PR |- *. cbn [fst snd] in PR |- *. unfold prod_atA in PR.
zstep.
zstep. bcase KT; [exfalso; rewrite ?unsigned_lit in KT by lia; lia|].
zstep.
zstep.
zstep. zstep. zstep.
first [rewrite rw0_valA' by lia | rewrite rw0_valA by lia].
zstep. zstep.
zstep.
rw_split SH 4%nat SHa SHr. rw_split SHr 1%nat SHb SHc.
call (ss_00_z RNG); [ first [ exact SHb | exact GOTM | exact REAL | eassumption | lia ] .. | ].
change (Z.to_nat 64) with 64%nat in POST. rw_join SHa POST SH1. rw_join SH1 SHc SH. cbn [app] in SH.
zstep. zstep.
zstep.
rw_split SH 13%nat SHa SHr. rw_split SHr 1%nat SHb SHc.
call (ss_00_z RNG); [ first [ exact SHb | exact GOTM | exact REAL | eassumption | lia ] .. | ].
change (Z.to_nat 64) with 64%nat in POST.
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) => assert (UNC : unpoisoned mx (F + 608) (F + 608 + 8 * Z.of_nat 64)) end.
{ apply unp_zero_cb; [clear - F2048; Z.div_mod_to_equations; lia| lia| unfold KEND; lia|].
replace (shad (F + 608)) with (Z.shiftr F 3 + ASHOFF + 76) by (unfold shad; rewrite !Z.shiftr_div_pow2 by lia; clear - F2048; Z.div_mod_to_equations; lia).
exact POST. }
change (8 * Z.of_nat 64) with 512 in UNC.
rw_join SHa POST SH1. rw_join SH1 SHc SH. cbn [app] in SH.
zstep. zstep. zstep.
zstep.
assert (SHE : forall k, 0 <= k <= 2048 -> k mod 8 = 0 -> shad (F + k) = Z.shiftr F 3 + ASHOFF + k / 8).
{ intros k Hk K8. unfold shad. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. clear - F2048 Hk K8. Z.div_mod_to_equations. lia. }
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
assert (WRH : wr_at bsegs mx (shad (F + 576)) (shad (F + 1152) - shad (F + 576)))
end.
{ rewrite (SHE 576), (SHE 1152) by lia. pose proof (proj2 SH) as WSH. cbn [cells_size csize Nat.add] in WSH.
eapply wr_at_sub; [exact WSH| lia ..]. }
assert (RHU : rng RNG (shad (F + 576)) (shad (F + 1152) - shad (F + 576))).
{ rewrite (SHE 576), (SHE 1152) by lia. eapply rng_sub'; [exact RSF| lia]. }
assert (APB : app_blk (F + 608) (F + 608 + 512)).
{ apply ablk_app_blk; [eapply ablk_sub; [exact FH| lia| lia]| lia]. }
callt ltac:(eapply (amemset_z RNG) with (RLO := F + 576) (RHI := F + 1152) (lo := lo));
[ first [ reflexivity | assumption | exact NCJ | lia | (unfold KHIGH; lia)
| (repeat split; first [lia | unfold KEND; lia | clear - F2048; Z.div_mod_to_equations; lia]) ] .. | ].
do 5 zstep.
apply evtF_done. unfold pB1_post, SHF, FSH.
do 18 eexists.
split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption|].
split; [unfold prod_atA; exact PR|]. split; [exact FRA|]. split; [exact POST| exact SH].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End B1.
End CANSEC1.
