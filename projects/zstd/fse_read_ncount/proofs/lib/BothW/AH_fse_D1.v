(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import FseNCount FseLemmas FseAbs FseWriterRT FseNCountRT FseHarness.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Arr Bytes ZBridge Tac InitMem.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import BImg ABase RtCells ABytes AMalloc_iface AProg_kit AF_fse_iface AHarness_iface AKit FsKit AH_fse_kit AH_fse_pure AH_fse_calls AH_fse_tail.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Plain Require Import RF_fse_h_model.
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
Definition W_D : list (Z * Z) := [(P + 8, P + 16); (B, B + bsz); (SPA - 2224, SPA + 120)].
#[using="rc sp lo F D pl LOS LOC SP16 ESPA BLKP RLOB RHIB BLKB"] Lemma WD_off_band : off_band W_D.
Proof.
pose proof (ablk_disj_band _ _ BLKP) as DBP. pose proof (ablk_disj_band _ _ BLKB) as DBB.
pose proof (spa_props5 (bv_unsigned sp) SP16) as SPAP. cbv zeta in SPAP. rewrite <- ESPA in SPAP. destruct SPAP as (SPAB & _ & _).
atop_facts. unfold AHARNESS_STACK in LOS. unfold W_D, off_band, KHIGH, KLS in *.
Local Ltac2 Set LiaHints.tbl := fun () => "0030>47636524364.5664910987599.569384765995.56 00000500E00JS3DBBS3LOS3LOC4SPAB1HS3DBP".
repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="rc U32R LOS LOC SPT SP16 ESPA RSTK RI FH F2048 RF RSF BLKP P16 RP RPS DLOC D8 RD RDS DP DF PLB SZ26 BLKB B16 BSZ RB RBS BP BD BF BHULL"] Lemma pD1 : forall (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 s9v s11v x28 x29 x30 x31 : word) (m : amem) (Q : machine_state -> Prop)
(tl msv dsz rem : Z) (nc data buf' : list Z) (jB jb jc jd : list byte),
fseA pl (zlen pl) = (tl, msv, nc, data, dsz, bsz, rem) ->
rw_cells bsegs m SPA [CB 24 jb; C8 (Z_to_bv 64 (SHF F + 76)); C8 (Z_to_bv 64 (SHF F + 4)); C8 (Z_to_bv 64 F);
C8 (Z_to_bv 64 (F + 1760)); CB 8 jc; C8 (Z_to_bv 64 (SHF F + 148)); C8 (Z_to_bv 64 tl); C8 (Z_to_bv 64 F);
C8 (Z_to_bv 64 msv); CB 16 jd; C8 (Z_to_bv 64 F)] ->
u8arr bsegs m (F + 32) (map (Z_to_bv 8) buf') -> length buf' = 512%nat -> firstn (Z.to_nat dsz) buf' = data ->
rw_cells bsegs m B [CB (Z.to_nat bsz) jB] ->
rw_cells bsegs m P [C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 rem)] ->
rw_cells bsegs m (SHF F) (FSH Z64 Z64 Z64 B04 B04) ->
stk bsegs m lo SPA -> mem_inv bsegs m ->
fse_rt m -> bytes_at bsegs m D (map (Z_to_bv 8) pl) ->
unpoisoned m P (P + 16) -> unpoisoned m D (D + zlen pl) -> unpoisoned m B (B + bsz) ->
wr_at bsegs m (shad RLOB) (shlen (RHIB - RLOB)) ->
(forall m2 junkF remF (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y20 y21 y25 y28 y29 y30 y31 : word),
fseB_tail pl rem dsz bsz = (junkF, remF) ->
u8arr bsegs m2 B (map (Z_to_bv 8) (data ++ junkF)) ->
rw_cells bsegs m2 P [C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 remF)] ->
rw_cells bsegs m2 SPA [CB 24 jb; C8 (Z_to_bv 64 (SHF F + 76)); C8 (Z_to_bv 64 (SHF F + 4)); C8 (Z_to_bv 64 F);
C8 (Z_to_bv 64 (F + 1760)); C8 (Z_to_bv 64 dsz); C8 (Z_to_bv 64 (SHF F + 148)); C8 (Z_to_bv 64 tl);
C8 (Z_to_bv 64 F); C8 (Z_to_bv 64 msv); CB 16 jd; C8 (Z_to_bv 64 F)] ->
stk bsegs m2 lo SPA -> munch W_D m m2 -> wmono bsegs m m2 -> mem_inv bsegs m2 ->
evtF bsegs RNG Q
(MS (mkR y1 (Z_to_bv 64 SPA) gp tp y5 y6 y7 sp (Z_to_bv 64 SPA) y10 y11 y12 y13 y14 y15 y16 y17
y18 (Z_to_bv 64 2147450880) y20 y21 (Z_to_bv 64 bsz) (Z_to_bv 64 P) (Z_to_bv 64 (F + 608)) y25
(Z_to_bv 64 (SHF F)) (Z_to_bv 64 B) y28 y29 y30 y31)
FR (Z_to_bv 64 0x8114c) fc None m2 (seg_rom bsegs))) ->
evtF bsegs RNG Q
(MS (mkR (Z_to_bv 64 0x810c4) (Z_to_bv 64 SPA) gp tp x5 x6 x7 sp (Z_to_bv 64 SPA)
(Z_to_bv 64 B) x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 dsz) (Z_to_bv 64 2147450880) (Z_to_bv 64 (F + 1760)) (Z_to_bv 64 (F + 32)) (Z_to_bv 64 bsz)
(Z_to_bv 64 P) (Z_to_bv 64 (F + 608)) s9v (Z_to_bv 64 (SHF F)) s11v x28 x29 x30 x31)
FR (Z_to_bv 64 0x810c4) fc None m (seg_rom bsegs)).
Proof.
intros until jd. intros EA FRA DATAA LB' FBUF BLK PR SH ST MI RT PAY UNP UND UNB WRB K.
pose proof (ablk_lin _ _ FH) as (FH1 & FH2 & FH3 & FH4). unfold AIMG_HI in FH1.
pose proof (ablk_lin _ _ BLKP) as (PL1 & PL2 & PL3 & PL4). unfold AIMG_HI in PL1.
pose proof (ablk_lin _ _ BLKB) as (BL1 & BL2 & BL3 & BL4). unfold AIMG_HI in BL1.
pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
pose proof (spa_props5 SP SP16) as SPAP. cbv zeta in SPAP. rewrite <- ESPA in SPAP. destruct SPAP as (SPAB & SPA32 & SPA120).
assert (D0 : 0 < D /\ D + zlen pl <= ATOP).
{ pose proof atop_range as ATR. Local Ltac2 Set LiaHints.tbl := fun () => "01O0?12715601132.18812924684033.18813684317200.19513684317203.19813760571730.17 15268607433.1881700057559.8   1706043863.172 18227369530.1631954364404.188 19628242851.17219955046160.18819962924073.19922168327223.17222266103744.17222971108077.23 23492641683.1282373528761.144 23870671586.18523872474103.14724150941288.18525774293055.17227723611718.18 27868141415.18428573892092.6  28750314815.18329462113472.23 29934734406.17230060549430.16330092713567.2  30510794559.14632428013911.13 32586253210.17233255990336.17033266593731.17233311715588.18833503950328.17233719989128.12534361761825.17235117825954.17235128051618.8  35736344964.17236878552440.14338033235920.14938290136343.1713839306879.140 39960879389.17239999590352.12542148826485.18842152988100.17242542688070.17242621589898.19845535530108.1724567445114.172 4614731390.186 46155823319.14648653510305.11748666356618.17252127281523.7  52141738355.17252265662933.16452541943432.18853119579314.1725336501062.188 53510313882.19853576692526.1885384210890.188 55248475920.18855257533481.19956185095336.1415889174793.172 5903570185.7   59753648227.17259850842910.18860599208439.18860948869848.17261035741573.8  61913100265.17261919405162.17062704206348.18862708105917.17262956075123.18863658507757.17263903208344.17264862841078.7  64873599222.17264895283520.17165496794741.18865518922064.14965531440114.1576685126354.184 67607347287.19068408202176.17268506258730.1729787679364.149 00001201V02:02^03704=04>04?04g05O05P06706^07j08Q08f0970:00;30<00<k0=n0>F0>j0>n0@30@H0@o0AW0A\0B]0C30C[0DC0Dk0F10G90GN0H50H60H70H^0IT0J[0K?0L40M70ML0NG0O?0PG0QQ0QR0R60R^0S[0So0TW0TX0TY0UA0VK0W^0XM0Y10Z60[?0[g0\O0\h0\i0]40][0^C0_N0`60`=0`a0aE0bP0cX0d@0dA0dB0dC0dD0dk0f10fX0gC0gk0i00iW0iX0j@S3LOS3LOC3LB'3FH23PL23BL23BL33RSP2D02H42F42F61H5LDATA3LMD5LREST2KBS3LB'3FH23PL23BL22F45LDATA3LMD5LRESTS3LB'3FH23PL23BL22F45LDATA3LMD5LRESTS3LB'3FH23PL23BL22F45LDATA3LMD5LRESTS3LOS3LOC2BP3PL34SPAB3F11S3LOS3LOC3BSZ3LB'3FH23PL23BL13BL23RSP2D02H42F42F61H5LDATA3LMD5LREST2KBFFS3LB'3FH23PL23BL22F45LDATA3LMD5LREST3HB5S3LB'3FH23PL13PL23BL22F45LDATA3LMD5LRESTFS3LB'3FH23PL23BL22F42F65LDATA3LMD5LRESTS3LB'3FH23PL23BL22F42F65LDATA3LMD5LRESTS3LOS3LOC3BSZ3LB'3FH23FH33PL23BL13BL23RSP4SPAB2D02H42F42F61H5LDATA3LMD5LRESTS3LB'3FH23PL23BL22F42F65LDATA3LMD5LRESTS5F20481H2H02H42H52H9S3LB'3FH23PL23BL2S3LOS3LOC3BSZ3LB'3FH23PL23BL13BL23RSP2D02H42F42F61H5LDATAS3LOS3LOC3BSZ3LB'3FH23PL23BL13BL23RSP2D02H42F42F61H5LDATA3LMD5LRESTS3LOS3LOC3BSZ3LB'3FH23PL23BL13BL23RSP2D02H42F42F61H5LDATA3LMDS3LOS3LOC3LB'3FH23PL23BL23RSP2D02DT2F42F61H5LDATA3LMD5LRESTS3LOS3LOC3LB'3FH23PL23BL23BL33RSP2D02H42F42F63F111H5LDATA3LMD5LRESTS3LOS3LOC2BD4SPAB2DT3F11S3LB'3FH23PL23BL22F45LDATA3LMD5LRESTS2HxS3LOS3LOC3LB'3FH23PL13PL23BL13BL23RSP4SPAB2D02F42F61H5LDATA3LMD5LRESTS5F20481H2H02H42H52H9S3LB'3FH23PL23BL22F42F65LDATA3LMD5LRESTS3LB'3FH23PL23BL22F45LDATA3LMD5LREST3HB5S3ATRS3LOS3LOC3BSZ3LB'3FH23PL23BL13BL23RSP2D02H42F42F63F111H5LDATA3LMDS3LOS3LOC3PL33BL34SPABS3LB'3FH23PL23BL22F43F115LDATA3LMD5LRESTS3LB'3FH23PL23BL22F43F115LDATA3LMD5LRESTS3LB'3FH23PL23BL22F43F115LDATA3LMD5LRESTS3LOS3LOC3BSZ3LB'3FH23PL23BL13BL23RSP2D02H42F42F61H5LDATA3LMD5LREST2KBS3LOS3LOC3LB'3FH23PL23BL23BL33RSP2D02F42F63F111H5LDATA3LMD5LREST3HB63HP6S3LB'3FH23FH43PL23BL2S3LB'3FH23PL23BL22F42F65LDATA3LMD5LRESTFFS3LB'3FH23PL23BL22F42F65LDATA3LMD5LRESTS3LOS3LOC3BSZ3LB'3FH23PL23BL13BL23RSP2D02H42F42F62F91HS3LOS3LOC3BSZ3LB'3FH23PL23BL13BL23RSP2D02H42F42F63F111H5LDATA3LMD5LRESTS3LB'3FH23PL23BL22F45LDATA3LMD5LRESTS3LOS3LOC3BSZ3LB'3FH23PL23BL13BL23RSP4SPAB2D02H42F41HS3LOS3LOC3LB'3FH23PL23BL23BL33RSP2D02H42F42F63F111H5LDATA3LMD5LRESTS3LB'3FH13FH23PL23BL2S3LOS3LOC3LB'3FH23PL23BL23RSP2D02F42F61H5LDATA3LMD5LREST2KBS3LOS3LOC3LB'3FH23PL23BL23RSP2D02F42F61H5LDATA3LMD5LRESTS3LOS3LOC3BSZ3LB'3FH23PL23BL13BL23RSP4SPAB2D02H42F42F61H5LDATA3LMD5LRESTS3LOS3LOC3BSZ3LB'3FH23PL23BL13BL23BL33RSP2D02H42F42F61H5LDATA3LMD5LREST2KBFS3LB'3FH23PL23BL22F45LDATA3LMD5LRESTS3LB'3FH23PL23BL23BL42F45LDATA3LMD5LRESTS3LOS3LOC3BSZ3LB'3FH23PL23BL13BL23RSP2D02H42F42F61H5LDATA3LMDS3LB'3FH23PL23BL22HpS3LB'3FH23FH43PL23BL22F45LDATA3LMD5LRESTFFS3LB'3FH23PL23BL22F45LDATA3LMD5LREST3HB5S3LOS3LOC3BSZ3LB'3FH23PL23PL33BL13BL23RSP2D02H42F42F61H5LDATA3LMD5LREST2KBS3LOS3LOC3LB'3FH23FH33PL23BL13BL23BL33RSP2D02H42F42F63F111H5LDATA3LMD5LREST3HB63HP2S3LB'3FH23PL23BL22F43F115LDATA3LMD5LREST3HB52KBS3LB'3FH23PL23BL22F45LDATA3LMD5LRESTS3LOS3LOC3LB'3FH23PL23BL13BL23RSP2D02H42F42F61H5LDATA3LMD5LREST2KB2EQS3LOS3LOC3BSZ3LB'3FH23PL23BL13BL23RSP2D02DT2H42F42F61H5LDATA3LMD5LREST2KBS3BSZ3LB'3FH23PL23BL22F45LDATA3LMD5LRESTS3BSZ3LB'3FH23PL23BL22F45LDATA3LMD5LRESTS3LB'3FH23PL23BL24SPAB2F4FS2BF2F63F11S3LB'3FH23PL23BL22F42F65LDATA3LMD5LRESTS3LB'3FH23PL23BL13BL22F45LDATA3LMD5LRESTS3LOS3LOC3BSZ3LB'3FH23PL23BL13BL23RSP4SPAB2D02H42F42F61H5LDATA3LMD5LREST2KBS3LB'3FH13FH23PL23BL22F45LDATA3LMD5LRESTS2B12B3S3LB'3FH23PL23BL22F45LDATA3LMD5LRESTS3LB'3FH23PL23BL22F45LDATA3LMD5LRESTS3LOS3LOC3SPT3LB'3FH23PL23BL23RSP4SPAB6SPA1202D02F42F61H5LDATA3LMD5LREST2KBS3LOS3LOC3SPT3LB'3FH23PL23BL23RSP4SPAB6SPA1202D02F42F61H5LDATA3LMD5LRESTS3LB'3FH23PL23BL22F43F125LDATA3LMD5LRESTFFFFS3LB'3FH23PL23BL22F42F65LDATA3LMD5LRESTS3LOS3LOC3BSZ3LB'3FH23PL23BL13BL23RSP2D02H42F42F61H5LDATA3LMD5LREST2KBS3LB'3FH23PL23BL22F42F65LDATA3LMD5LRESTS3LB'3FH23PL23BL22F42F65LDATA3LMD5LREST3HB5S3LB'3FH23PL23PL43BL22F45LDATA3LMD5LRESTS3LOS3LOC3LB'3FH23PL23BL13BL23RSP2D02H42F42F61H5LDATA3LMD5LREST2KB2EQS3LB'3FH23PL23BL22F42F65LDATA3LMD5LRESTFS3LB'3FH23PL23BL13BL22F45LDATA3LMD5LREST".
destruct DLOC as [[-> ->]|BB]; [unfold AEMPTY; cbn; clear - ATR; lia| pose proof (ablk_lin _ _ BB) as (B1 & B2 & B3 & B4); unfold AIMG_HI in B1; clear - B1 B2 B3 B4; lia]. }
destruct D0 as [D0 DT].
assert (BLKD : 0 < zlen pl -> ablk D (D + zlen pl)) by (intros Hp; destruct DLOC as [[-> _]|X]; [cbn in Hp; lia| exact X]).
assert (S72 : shad (F + 576) - shad F = 72) by (rewrite !shad_div; clear - F2048; Z.div_mod_to_equations; lia).
assert (F64 : F mod 64 = 0 /\ (F + 576) mod 64 = 0) by (clear - F2048; Z.div_mod_to_equations; lia).
destruct BHULL as (H1 & H2 & H3 & H4 & H5).
d1k SP16. d1k ESPA. d1k F2048. d1k P16. d1k D8. d1k B16. d1k PF. d1k DLOC. d1k DP. d1k DF. d1k BP. d1k BD. d1k BF. d1k SPA32.
d1k H1. d1k H2. d1k F64.
pose proof (fsh_unp_data m F F2048 ltac:(lia) ltac:(unfold KEND; lia) _ _ _ _ SH) as UDA.
pose proof (fsh_wr m F _ SH ltac:(reflexivity)) as WSH.
assert (AB : all_bytes pl) by (apply Forall_all_bytes; exact PLB).
pose proof (fseA_facts pl (zlen pl) AB ltac:(lia)) as FACTS. rewrite EA in FACTS.
destruct FACTS as (F1 & F2 & V & F4 & _ & F6 & F7 & F8 & F9 & F10 & F11 & F12).
unfold FSE_MIN_TABLELOG, FSE_MAX_TABLELOG in *.
pose proof WD_off_band as OBD.
unfold W_D in *. unfold SHF, FSH, AHARNESS_STACK in *.
atop_facts.
assert (RFRA : rng RNG SPA 120) by (eapply rng_sub'; [exact RSTK| lia]).
assert (RSTKA : rng RNG lo (SPA - lo)) by (eapply rng_sub'; [exact RSTK| lia]).
assert (LENP : zlen (map (Z_to_bv 8) pl) = zlen pl) by (rewrite length_map; reflexivity).
assert (LDATA : length data = Z.to_nat dsz) by (unfold FseNCount.Zlength in F9; lia).
assert (DSZ : zlen data = dsz) by (rewrite LDATA; lia).
assert (LMD : length (map (Z_to_bv 8) data) = Z.to_nat dsz) by (rewrite length_map; exact LDATA).
assert (SRC : bytes_at bsegs m (F + 32) (map (Z_to_bv 8) data)).
{ rewrite <- FBUF, <- firstn_map. apply bytes_at_firstnF; [exact (proj1 DATAA)| rewrite length_map; lia]. }
clear DATAA.
apply (rw_cells_split_CB _ _ _ [] _ _ [] [Z.to_nat dsz; Z.to_nat (bsz - dsz)]) in BLK; [| cbn; lia]. cbn [mk_CB_cells app] in BLK.
apply (proj1 (rw_cells_app _ _ _ [_] _)) in BLK. destruct BLK as [BLK1 BLK2]. cbn [cells_size csize Nat.add] in BLK2.
replace (B + Z.of_nat (Z.to_nat dsz + 0)) with (B + dsz) in BLK2 by lia.
set (rest := firstn (Z.to_nat (bsz - dsz)) (skipn (Z.to_nat dsz) jB)) in *.
assert (LREST : length rest = Z.to_nat (bsz - dsz)) by (destruct BLK2 as [[[Hn _] _] _]; exact Hn).
destruct (block_hull RNG m B dsz RLOB RHIB ltac:(lia) H1 H2 H3 ltac:(lia) ltac:(lia) H5 WRB) as (RHB & WHB & HB1 & HB2 & HB3 & HB4 & HB5 & HB6).
pose proof (hull_props B dsz ltac:(lia)) as (HP1 & HP2 & HP3 & HP4 & HP5 & HP6).
assert (WHF : wr_at bsegs m (shad F) (shad (F + 576) - shad F)) by (rewrite S72; eapply wr_at_sub; [exact WSH| lia| lia]).
assert (RHF : rng RNG (shad F) (shad (F + 576) - shad F)) by (rewrite S72; eapply rng_sub'; [exact RSF| lia]).
clear SH WRB H5 WSH.
d1k HB3. d1k HB4. d1k HP3. d1k HP4.
pose proof (munch_refl [(P + 8, P + 16); (B, B + bsz); (SPA - 2224, SPA + 120)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
pose proof RT as RT0. d1k RT0.
destruct RT as (GOT & RIC & REAL & SHB & INI & LAY & GOTM).
d1k UNP. d1k UND. d1k UNB. d1k UDA.
zstep. zstep. zstep. zstep.
assert (UNB1 : unpoisoned m B (B + dsz)) by (unfold d1_keep in UNB; eapply unpoisoned_sub; [exact UNB| lia| lia]).
assert (UDA1 : unpoisoned m (F + 32) (F + 32 + dsz)) by (unfold d1_keep in UDA; eapply unpoisoned_sub; [exact UDA| lia| lia]).
eapply evtF_cut;
[ eapply (amemcpy_z RNG) with (RLO1 := F) (RHI1 := F + 576) (RLO2 := hull_lo B) (RHI2 := hull_hi B dsz) (lo := lo)
(src := map (Z_to_bv 8) data);
first [ assumption | exact BLK1 | (rewrite LMD; reflexivity) | (unfold KHIGH; lia)
| (apply ablk_app_blk; [eapply ablk_sub; [exact FH| lia| lia]| lia]) | (apply ablk_app_blk; [eapply ablk_sub; [exact BLKB| lia| lia]| lia])
| (clear - BF F6 F11; unfold d1_keep in *; lia)
| (left; lia)
| (repeat split; first [ assumption | exact (proj1 F64) | exact (proj2 F64) | lia | unfold KEND; lia ])
| (eapply rng_sub'; [exact RF| lia]) | (eapply rng_sub'; [exact RB| lia]) | lia
]
| ].
intros ms' PO. cbv beta delta [amemcpy_postz] in PO.
destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & E & MUc & WMc & MIc & STc & CHc & BYc).
subst ms'.
clear BLK1 ST SRC MI BYc UNB1 UDA1.
d1k PR. d1k PAY.
transport_after_call_fast bsegs m m2 MUc WMc.
unfold d1_keep in PR, PAY.
apply (rw_cells_transport bsegs [(SPA - 2224, SPA); (B, B + dsz)] m m2 P _) in PR;
[| exact MUc| exact WMc| cbn [disjoint_from cells_size csize Nat.add]; clear - BP F11 F6 SPAB LOS LOC PL3 RSP; unfold d1_keep in *; lia].
apply (bytes_at_transport bsegs [(SPA - 2224, SPA); (B, B + dsz)] m m2 D _) in PAY;
[| exact MUc| rewrite LENP; cbn [disjoint_from]; clear - BD F11 F6 SPAB LOS LOC DT RSP; unfold d1_keep in *; lia].
clear MUc WMc.
replace (ret_pc (Z_to_bv 64 0x810d4)) with (Z_to_bv 64 0x810d4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
zstep.
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m3 end.
assert (BA : u8arr bsegs m3 B (map (Z_to_bv 8) data ++ rest)).
{ pose proof (proj2 (rw_cells_app bsegs m3 B [CB (Z.to_nat dsz) (map (Z_to_bv 8) data)] [CB (Z.to_nat (bsz - dsz)) rest])) as AP.
cbn [cells_size csize Nat.add] in AP. replace (B + Z.of_nat (Z.to_nat dsz + 0)) with (B + dsz) in AP by lia.
specialize (AP (conj CHc BLK2)). cbn [app] in AP.
pose proof (rw_cells_merge bsegs m3 B [] [CB (Z.to_nat dsz) (map (Z_to_bv 8) data); CB (Z.to_nat (bsz - dsz)) rest] []) as MGc.
rewrite app_nil_r in MGc. specialize (MGc AP). clear AP. cbn [app cells_size csize cells_bytes cbytes Nat.add] in MGc.
apply u8arr_of_rw_cells in MGc. rewrite app_nil_r in MGc. exact MGc. }
clear CHc BLK2.
assert (RT3 : fse_rt m3).
{ unfold d1_keep in RT0. eapply fse_rt_munch; [exact RT0| exact MU| exact WM|]. cbn [above]. unfold AIMG_HI. lia. }
assert (UNP3 : unpoisoned m3 P (P + 16)) by (unfold d1_keep in UNP; eapply (unp_munch_band _ m m3); [exact UNP| exact MU| exact OBD| unfold KEND; lia]).
assert (UND3 : unpoisoned m3 D (D + zlen pl)) by (unfold d1_keep in UND; eapply (unp_munch_band _ m m3); [exact UND| exact MU| exact OBD| unfold KEND; lia]).
assert (UNB3 : unpoisoned m3 B (B + bsz)) by (unfold d1_keep in UNB; eapply (unp_munch_band _ m m3); [exact UNB| exact MU| exact OBD| unfold KEND; lia]).
zstep.
if_cases KB; zify_cond KB.
-
assert (EQ : bsz = dsz) by (unfold d1_keep in *; lia).
destruct rest as [|? ?]; [| cbn in LREST; lia]. rewrite app_nil_r in BA.
eapply (K m3 [] rem); try eassumption.
+ unfold fseB_tail. replace (Z.to_nat (bsz - dsz)) with 0%nat by lia. reflexivity.
+ rewrite app_nil_r. exact BA.
-
zstep. zstep. zstep. zstep. zstep.
rewrite (proj2 (Z.ltb_lt 0 B)) by lia. cbn [Z.b2z].
replace (bsz - dsz) with (Z.of_nat (Z.to_nat (bsz - dsz))) by lia.
replace (dsz + B) with (B + (dsz + zlen (@nil Z))) by (cbn; lia).
eapply (tail_loopA U32R RNG gp tp sp (Z_to_bv 64 (F ≫ 3 + ASHOFF)) FR fc m3 SPA (F + 608) P D B pl data dsz bsz lo Q
ltac:(lia) ltac:(lia) ltac:(unfold KHIGH; lia) ltac:(lia) ltac:(lia) DP ltac:(lia) BP BD DSZ PLB ltac:(lia) P16 D0 D8
BLKP BLKD BLKB B16 RI RSTKA RP RPS RD RDS RB RBS RT3 PAY UNP3 UND3 UNB3
(Z.to_nat (bsz - dsz)) rem [] rest m3);
[ lia | exact LREST | cbn; lia | lia | | ].
+
rewrite app_nil_r. split; [exact BA|]. split; [exact PR|]. split; [exact STc|].
split; [apply munch_refl|]. split; [apply wmono_refl| exact MIc].
+ intros m4 junkF remF y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y20 y21 y25 y28 y29 y30 y31 ET (BA2 & PR2 & ST2 & MU2 & WM2 & MI2) RF'.
rewrite app_nil_r in BA2.
apply (rw_cells_transport bsegs [(P + 8, P + 16); (B, B + bsz); (SPA - 16, SPA)] m3 m4 SPA _) in FRA;
[| exact MU2| exact WM2| cbn [disjoint_from cells_size csize Nat.add]; clear - PL3 BL3 LOS LOC SPAB; lia].
assert (MUF : munch [(P + 8, P + 16); (B, B + bsz); (SPA - 2224, SPA + 120)] m m4).
{ eapply munch_trans; [exact MU| eapply munch_weaken; [| exact MU2]].
unfold sub_fp; cbn [outside]. intros x Hx. clear - Hx. lia. }
assert (WMF : wmono bsegs m m4) by (eapply wmono_trans; [exact WM| exact WM2]).
eapply (K m4 junkF remF);
[ unfold fseB_tail; exact ET | exact BA2 | exact PR2 | exact FRA | exact ST2 | exact MUF | exact WMF | exact MI2 ].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End D1.
End CANSEC1.
