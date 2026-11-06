(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac InitMem ITree Nodes Decode.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import ExecF ITreeA Shadow.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import AImg RtCells AProto ABase ABytes AMalloc_iface ADepot_iface ARep ALayout AHeapP ARepExt
FsKit AFake_iface F_tlsga F_m2s_b AFake_sm0 AFake_arep AFake_sm0r AF_fse_rd_iface.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
Import ListNotations.
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

Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section CANSEC1. Context {rc : runConstT}.
Section S.
Variable DI : ADepotIface.
Variables (AQ ASEC : alayout -> astate -> aconc -> amem -> Prop).
Hypothesis HL : ahole_laws (AH DI AQ ASEC).
Variable CI : list (Z * Z).
Hypothesis CI_OK : forall iv, In iv CI -> 0 <= fst iv /\ snd iv <= AIMG_HI.
Notation AH := (AFake_arep.AH DI AQ ASEC).
Notation sm0_postP := (AFake_arep.sm0_postP DI AQ ASEC CI).
Notation FB0 F := (mkABlock (ABFake 0) F 64).
#[using="HL CI_OK"] Theorem stack_malloc_0r_P : forall (L : alayout) (RNG : footprint)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(FR : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (lo : Z),
AHEAP_P AH L RNG st LB m ->
fake0_le1 LB ->
mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - SM_STACK ->
bv_unsigned sp <= al_top L ->
tp = Z_to_bv 64 ATP ->
rng RNG lo (al_top L - lo) -> rng_aimg RNG -> afake_rng L RNG ->
evtF asegs RNG (sm0_postP L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
FR (Z_to_bv 64 ASTKMALLOC0) fc None m (seg_rom asegs)).
Proof.
intros until lo. intros AHP LE1 MI ST BOT LO SPT TP RSTK RIMG (RF & RSH & RD).
pose proof AHP as (ALO & ARNG & [X [AR BL]] & HFK). cbn [AFake_arep.AH ah_fake] in HFK.
pose proof HFK as (G & CE & (h0 & h1 & h2 & hs & HNT) & LOG & NGC & DC1 & DC2 & FL & LV).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11).
pose proof (ablk_lin _ _ G2) as (GL1 & GL2 & GL3 & GL4). pose proof G5 as (G5s & G5i & G5l). pose proof G7 as (G7s & G7i & G7l).
unfold sclr, KLS in G5s, G7s. pose proof G7i as G7I. unfold iclr, AIMG_LO in G7I. pose proof atop_range as ATR.
destruct CE as (REAL & DTVP & DV & DTV1 & BD & CF & VERB & T48).
pose proof (alayout_t L ALO) as (TL1 & TL2 & TL3 & TL4). pose proof (alayout_t_lin L ALO) as (TL5 & _).
pose proof (alayout_ctx L ALO) as (CL1 & CL2 & CL3 & CL4 & CL5).
pose proof (alayout_stack L ALO) as (SK1 & SK2 & SK3).
destruct (AREP_cells _ _ _ L st X m AR) as (R2 & R11 & R13 & R14 & R15 & R16 & R24 & R25 & R28 & RR).
Local Ltac2 Set LiaHints.tbl := fun () => "02;0?10092530843.1901043511398.164 1043511398.169 11186298754.1331127175226.164 1127175226.169 1232026594.210 14712686997.35 15047146784.16515047308710.2081566707379.209 16597815198.21016643975587.16416643975587.1691713438335.10  1715765315.12  17991417480.16417991417480.16918426717457.26 18426717457.29 18926599560.15618926746797.16020211304835.28 20735943053.7  22369263914.17223300114087.6  26087858018.20926861977183.13226889197080.19127033617613.21029147256744.21529297457836.16429299450114.16029784464364.13629784497005.18429786479080.16630375295474.21033085935132.24 33086189277.19 33092481056.21 33490756850.18233742932914.16433742932914.16933977372108.5  34118493740.8  34301889471.35 34303987250.42 34304097934.26 34304097934.28 34304097934.29 34494347618.17435000748274.21035097887758.26 35097887758.29 35441213895.16435441213895.16935695677603.16435695677603.16937656117931.28 3769089931.29  38137814781.13139756652530.21040354203149.16040354416424.15641889083930.17141889386282.17341996636011.16441996636011.1694626871848.131 46442045225.17446901028642.21046901177752.22846903072696.22046903274638.21846903274892.16047348482913.17248235394228.1564835283238.2   49927382112.20952101696360.19 52101737131.21552101950377.24 52107990421.21 52469690798.17352564951269.18 52564951269.23 52679724388.15653891125283.21454965485378.16454965485378.16955355428199.19155448986806.21755448989219.21855448989473.16055449179413.22055451086645.22855451297167.21055873094590.18155878677456.10 55878874588.16 56170432923.16456170432923.16956759370246.21 56765398074.24 56765644088.21556765668603.19 56953681963.20957161297437.15457980378352.19158037925428.17958351784165.17358424762250.13259308663781.16759424320314.17959749980982.18859750091318.21060046456050.21060524391140.5  60524548822.20961161457197.17161161650461.20963238601098.17163370183848.17963370230317.17463370230318.17265018425489.16565018425489.18965645947670.18066755833475.15366862548982.13367070302598.13367149867122.16467149867122.16967419257744.1916755523980.156 67760285770.35 68162253911.1337569773426.210 8320852291.9   00000K00T00]00b00c00d01Y02A02F02K02k03403503603M03^03g04004A04R04W04\04m05505I05U06406906A06b06j07?07S07X07]07b08W08n09E09X09]09b09g09o0::0:]0;30;b0<Q0=@0=T0>I0>c0?=0?>0??0?D0?I0?c0@?0@D0A90A>0AC0AH0AM0AN0AO0AT0Ah0Am0B20B70B<0BA0BU0B]0Bb0CB0C[0Co0DX0E40EH0F00Ff0Fn0GF0GO0GX0G`0Gh0H00H80H@0HH0HP0Hh0I20II0IR0I[0I_0Ic0Ik0Io0JM0JR0JZ0K20KF0KK0L80LA0L`0M>0N30N;0NS0Ng0O?0OS0OX0O]0Ob0P30PP0Ph0Pm0Q20Q70Q?0QG0QO0QT0QX0Q]0RR0RZS3GL13GL23G5l3G7l2PB3HFF2WFS3GL23CL2S3GL23CL2S3GL2FFS3BOT2LO3GL13GL23G5l3G7l3ATR3SHS2PB3SHF3SB15HFLAG3HFFS2PB5HFLAG3HFF3F642Ha3A'R2NA3G2b1H2H02H4S3GL2S3GL2S3GL13GL23G5l3G7l2PB3SHF3SB13HFFS3GL13GL2FFS2G32PB3HFF2X11H3GL12HrS3ATR2Hr2Y12Y22Y4S3BOT3GL2S3BOT3GL2S3GL13GL33ATR3FRGS3GL13GL33ATR3FRGS3GL2S3GL2S3GL13GL33ATR3FRGS2PB3G2cS3GL13GL23G5l3G7l2PBS2PB3SB13SB2S3BOT2LO3GL13GL23G5l3G7l2PB3HFFS3GL2S3GL22LJS3GL13GL23G5l3G7l3SHS3SHF3SB13HFFS3GL22N3S3GL13GL23G5l3G7l3Hp'S3GL13GL23G5l3G7l2PBS3GL2S3GL2S3GL2S3BOT2LO3GL13GL23G5l3G7l3ATR3SHS2PB3SHF3SB15HFLAG3HFFS2PB5HFLAG3HFF2Hr2Y32Y4S3BOT2LO2G32PB5HFLAG2HsS3GL12PB5HFLAG2Hr1HS3GL2S3GL2S3GL2S2PB3HFFS2G32PB3HFFS3BOT2LO3ATR3A'R1H2H02PB3HFF2NA3G2bS3F642NA1H2H02H42H52H9S3BOT2LO3GL33FRG2PB3HFF2G13GL23SHF3SHD5HFLAG2NES3BOT2LO3GL33FRG2PB3HFF2G13GL23SHF3SHD5HFLAG2NES3BOT2LO3GL33FRG2PB3HFF2G13GL23SHF3SHD5HFLAG2NES3GL13GL23G5l3G7l2PBS3BOT2LO3GL13GL23G5l3G7l3ATR3SHS2PB3SHF3SB15HFLAG3HFFS2G13GL13GL22PB3SHF3HFF2NES2G13GL13GL22PB3SHF3HFF2NEFFS3GL2S3GL2S2G13GL13GL22PB3SHF3HFF2NES2G12G33ATR2PB1H2H02H42H52H9S3GL2S3BOT2LO3GL13GL23G5l3G7l3ATR3SHS2PB3SHF3SB15HFLAG3HFFS3GL2S3GL2S3GL2S3GL2FFS3GL2S3GL13GL23G5l3G7l2PBS3GL2S3GL2S3GL2S3GL2S3GL2S3GL13GL23G5l3G7l2PBS3GL22PBS3G7IS3GL13GL23G5l3G7l2PB3SHF3SB13HFFS2Hs3BOT2LO2G32PB3HFF3ATRS3GL22N12N22N42N52N6S3BOT2LO2Hr2Y22PB3HFF2Y32Y42G33GL13ATR2Y1S3BOT2LO3ATR2Hr1H3GL12PB3HFFS3GL13GL23G5l3G7l2PBS3BOT2LO2G33GL13ATR2PB3SHF3SHD5HFLAG3HFFS3BOT2LO2G32G62G93GL13G5s3ATR2PB3SHF3SB33SHD5HFLAG3HFFS3GL22PBS3GL13GL23G5l3G7l2PB3HFFS3GL23G7lS3GL23G7lS3GL22LJS3GL22PBS3GL22PBS3GL22PBS3GL22PBS3GL22PBS3GL22PBS3GL13GL23G5l3G7l2PB3HFFS2X12X42DJS2G13GL12PB3HFF2Q32Q41DS3SPT3GL2S3SPT3GL2S2HaS2HaS3GL22HaS2HaS3GL13GL23G5l3G7l2PB5HFLAG3HFFS3GL2S3GL22LJS3GL13GL23G5l3G7l2PB3SB1S3GL13GL23G5l3G7l2PBS3GL2S2G52G72G93G103G113GL13GL23G5s3G7s3CL33N122EFS3GL23SB2S3GL13GL23G5l3G7l5HFLAG3HFF3Hp'S3GL13GL23G5l3G7l2PB5HFLAG3HFFS3BOT2LO3GL13GL23G5l3G7l3ATR3SHS2PB3SHF3SB15HFLAG3HFFS2PB3HFFS3GL13GL23G5l3G7l2PB3HFFS3GL13GL23G5l3G7l2PBS3GL13GL23G5l3G7l2PB3HFFS3GL13GL23G5l3G7l2PBS3GL2S3GL2S3GL2S3GL23G5l3G7l3HF'S3GL13GL23G5l3G7l3HFF3Hp'3HF'S3GL13GL23G5l3G7l2PB3HFFS3GL2S3GL2S3GL2S2LO3GL2S2LO3GL2S3GL22LJS3GL2S2HaS3GL2S3BOT2LO3GL13GL23G5l3G7l3ATR3SHS2PB3SHF3SB15HFLAG3HFFS2PB3HFF".
pose proof (relro_word m 0x997d0 0x131f18 RR ltac:(unfold ARELRO_LO; lia) ltac:(unfold ARELRO_HI; lia) ltac:(vm_compute; reflexivity)) as GB0.
pose proof (relro_word m 0x9a478 8 RR ltac:(unfold ARELRO_LO; lia) ltac:(unfold ARELRO_HI; lia) ltac:(vm_compute; reflexivity)) as G08.
assert (DESC : rw_cells asegs m AFSDESC [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 18446744073709549568)]).
{ unfold AFSDESC. apply (proj2 (rw_cells_app asegs m 0x9a468 [C8 (Z_to_bv 64 1)] [C8 (Z_to_bv 64 18446744073709549568)])).
split; [| cbn]; (apply relro_word; [exact RR| unfold ARELRO_LO; lia| unfold ARELRO_HI; lia| vm_compute; reflexivity]). }
unfold FAKESZ, KHIGH, AIMG_HI, SM_STACK in *.
set (h := bv_unsigned h0).
assert (HB : 0 <= h < 2^64) by (subst h; apply bv_unsigned_in_range).
assert (SHS : shad (al_fake L) = 0x7fff8000 + (al_fake L) / 8 /\ shlen 11571200 = 1446400).
{ unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. split; reflexivity. }
destruct SHS as [SHS SHL]. rewrite SHL in *.
destruct (c8c8_of_dc m _ T48) as (tb & te & T48').
assert (HNT' : rw_cells asegs m (al_fake L) [C8 (Z_to_bv 64 h); C8 h1; C8 h2; CB 64 hs]) by (subst h; rewrite Z_to_bv_bv_unsigned; exact HNT).
pose proof ARNG as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10).
clearbody h.
assert (EFLg : forall pos, (al_fake L) + 4096 + pos = fk_flag L 0 pos)
by (intros pos; unfold fk_flag, fk_flags; cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.sub]; lia).
assert (EFRg : forall pos, (al_fake L) + 36864 + pos * 64 = fk_frame L 0 pos)
by (intros pos; unfold fk_frame, fk_frames, fk_fsize; cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.add]; lia).
assert (FLB : forall pos, 0 <= pos < 16384 -> exists fb, rw_cells asegs m ((al_fake L) + 4096 + pos) [C1 fb]).
{ intros pos PB. pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) ((al_fake L) + 4096 + pos) 1 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as D3.
exact (c1_of_dc m _ D3). }
assert (FLV : forall pos fb, 0 <= pos < 16384 -> rw_cells asegs m ((al_fake L) + 4096 + pos) [C1 fb] -> fb <> Z_to_bv 8 0 ->
In (FB0 (fk_frame L 0 pos)) LB /\ fb = Z_to_bv 8 1).
{ intros pos fb PB FLx NE.
assert (IN : In (FB0 (fk_frame L 0 pos)) LB).
{ change 64 with (fk_fsize 0). apply (FL 0 pos fb); [unfold FK_NCLS; lia| unfold fk_nframes; cbn; lia| | exact NE].
rewrite <- EFLg. apply (rw_C1_high m _ fb FLx). lia. }
split; [exact IN|].
destruct (LV 0 _ _ IN) as (_ & _ & pos' & Hp' & HF' & B1).
assert (pos' = pos) as ->.
{ unfold fk_frame, fk_frames, fk_fsize in HF'. cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.add] in HF'. unfold fk_nframes in Hp'. cbn in Hp'. lia. }
rewrite <- EFLg in B1. pose proof (rw_C1_high m _ fb FLx ltac:(lia)) as B2. congruence. }
assert (CHOICE : exists pos hn, 0 <= pos < 16384 /\ rw_cells asegs m ((al_fake L) + 4096 + pos) [C1 (Z_to_bv 8 0)] /\
forall (j24 j56 sh0 : word),
rw_cells asegs m ((al_fake L) + 36864 + pos * 64 + 24) [C8 j24] -> rw_cells asegs m ((al_fake L) + 36864 + pos * 64 + 56) [C8 j56] ->
rw_cells asegs m (shad ((al_fake L) + 36864 + pos * 64)) [C8 sh0] ->
evtF asegs RNG (sm0_cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc lo (al_fake L) hn
((al_fake L) + 4096 + pos) ((al_fake L) + 36864 + pos * 64) h1 h2 hs m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
FR (Z_to_bv 64 ASTKMALLOC0) fc None m (seg_rom asegs))).
{ assert (PB1 : 0 <= Z.land h 16383 < 16384).
{ change 16383 with (Z.ones 14). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
destruct (FLB (Z.land h 16383) PB1) as [fb1 FL1].
destruct (decide (fb1 = Z_to_bv 8 0)) as [E1|NE1].
-
subst fb1. exists (Z.land h 16383), h. split; [exact PB1|]. split; [exact FL1|].
intros j24 j56 sh0 F24 F56 SH0.
eapply (stack_malloc0_cspec RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
FR fc m lo (al_ctx L) (al_t L) (al_dtls L) 0x5d5410 (al_fake L) h (Z.land h 16383) ((al_fake L) + 4096 + Z.land h 16383)
((al_fake L) + 36864 + Z.land h 16383 * 64) j24 j56 sh0 h1 h2 hs);
try exact MI; try exact ST; try exact TP; try eassumption; try reflexivity; try (unfold AIMG_HI; lia).
all: try (unfold tlsga_cells; split; [exact REAL|]; split; [exact DESC|]; split; [exact DTVP|]; split; [exact DTV1|];
split; [exact R2|]; split; [exact CF|]; split; [exact GB0|]; split; [exact VERB|]; split; [exact G08|];
split; [exact DV|]; split; [exact BD|]; exists tb, te; exact T48').
all: try (eapply rng_sub'; [exact RSTK| lia]).
all: try (eapply rng_sub'; [exact A3| lia]).
-
destruct (FLV (Z.land h 16383) fb1 PB1 FL1 NE1) as [IN1 ->].
assert (PB2 : 0 <= Z.land (h + 1) 16383 < 16384).
{ change 16383 with (Z.ones 14). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
pose proof (land16383_succ_neq h) as N12.
destruct (FLB (Z.land (h + 1) 16383) PB2) as [fb2 FL2].
assert (fb2 = Z_to_bv 8 0) as ->.
{ destruct (decide (fb2 = Z_to_bv 8 0)) as [E|NE]; [exact E| exfalso].
destruct (FLV (Z.land (h + 1) 16383) fb2 PB2 FL2 NE) as [IN2 _].
destruct (LE1 _ _ _ _ IN1 IN2) as [EF _]. rewrite <- !EFRg in EF. lia. }
exists (Z.land (h + 1) 16383), (h + 1). split; [exact PB2|]. split; [exact FL2|].
intros j24 j56 sh0 F24 F56 SH0.
eapply (stack_malloc0_cspec2 RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
FR fc m lo (al_ctx L) (al_t L) (al_dtls L) 0x5d5410 (al_fake L) h (Z.land h 16383) ((al_fake L) + 4096 + Z.land h 16383)
(Z.land (h + 1) 16383) ((al_fake L) + 4096 + Z.land (h + 1) 16383) ((al_fake L) + 36864 + Z.land (h + 1) 16383 * 64)
j24 j56 sh0 h1 h2 hs);
try exact MI; try exact ST; try exact TP; try eassumption; try reflexivity; try (unfold AIMG_HI; lia).
all: try (unfold tlsga_cells; split; [exact REAL|]; split; [exact DESC|]; split; [exact DTVP|]; split; [exact DTV1|];
split; [exact R2|]; split; [exact CF|]; split; [exact GB0|]; split; [exact VERB|]; split; [exact G08|];
split; [exact DV|]; split; [exact BD|]; exists tb, te; exact T48').
all: try (eapply rng_sub'; [exact RSTK| lia]).
all: try (eapply rng_sub'; [exact A3| lia]). }
destruct CHOICE as (pos & hn & PB & FL0 & WALK).
set (flag := (al_fake L) + 4096 + pos) in *. set (F := (al_fake L) + 36864 + pos * 64) in *.
assert (EFL : flag = fk_flag L 0 pos) by (subst flag; apply EFLg).
assert (EFR : F = fk_frame L 0 pos) by (subst F; apply EFRg).
assert (EFF : fflag L 0 F = flag) by (rewrite EFR, fflag_frame, <- EFL by lia; reflexivity).
assert (SHF : shad F = 0x7fff8000 + F / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
assert (SHB : shad (al_fake L) + 4608 + 8 * pos = shad F /\ shad F + 8 <= shad (al_fake L) + 1446400 /\ shad F + 8 <= 0x10007fff8000).
{ rewrite SHF, SHS. subst F. clear - G1 GL1 G3 PB ATR. Z.div_mod_to_equations. lia. }
destruct SHB as (SB1 & SB2 & SB3).
assert (SHD : shad F + 8 <= al_fake L \/ al_fake L + 11571200 <= shad F).
{ pose proof G2 as G2c. unfold ablk, AIMG_HI, KLS in G2c. rewrite SHF. subst F. clear - G2c G3 PB ATR. lia. }
pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) F 24 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as DJ0.
pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) (F + 24) 8 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as D24.
pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) (F + 32) 24 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as DJ1.
pose proof (dc_sub m ((al_fake L) + 4096) (11571200 - 4096) (F + 56) 8 DC1 ltac:(lia) ltac:(lia) ltac:(lia)) as D56.
destruct (c8_of_dc m _ D24) as [j24 F24]. destruct (c8_of_dc m _ D56) as [j56 F56].
pose proof (dc_sub m (shad (al_fake L)) 1446400 (shad F) 8 DC2 ltac:(lia) ltac:(lia) ltac:(lia)) as DS2.
destruct (c8_of_dc m _ DS2) as [sh0 SH0].
assert (HFLAG : flag = (al_fake L) + 4096 + pos) by reflexivity.
assert (HFF : F = (al_fake L) + 36864 + pos * 64) by reflexivity.
clearbody flag F.
assert (NOTIN : ~ In (FB0 F) LB).
{ intros IN. destruct (LV 0 F 64 IN) as (_ & _ & pos' & Hp' & HF' & B1).
assert (pos' = pos) as ->.
{ rewrite EFR in HF'. unfold fk_frame, fk_frames, fk_fsize in HF'. cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.add] in HF'.
unfold fk_nframes in Hp'. cbn in Hp'. lia. }
rewrite <- EFL in B1. pose proof (rw_C1_high m flag _ FL0 ltac:(lia)) as B0. rewrite B0 in B1. injection B1 as B1.
vm_compute in B1. discriminate B1. }
eapply evtF_mono; [exact (WALK j24 j56 sh0 F24 F56 SH0)|].
cbv beta. intros ms' PO.
destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & m' & -> & MU & WM & MI' & ST' & HNT2 & FL1 & F24' & F56' & SH').
unfold sm0_W in MU. rewrite SHF in MU.
assert (OUT : forall a, 0 <= a < 2^64 ->
~ (bv_unsigned sp - 208 <= a < bv_unsigned sp) -> ~ ((al_fake L) <= a < (al_fake L) + 8) -> a <> flag ->
~ (F + 24 <= a < F + 32) -> ~ (F + 56 <= a < F + 64) -> ~ (2147450880 + F / 8 <= a < 2147450880 + F / 8 + 8) ->
m' (wa a) = m (wa a)).
{ intros a Ha N1 N2 N3 N4 N5 N6. apply MU. rewrite wa_unsigned by lia. cbn [outside]. repeat split; lia. }
assert (F64 : F mod 64 = 0) by (rewrite EFR; apply fk_frame_al64; [exact G1| lia]).
Local Ltac xport H MU WM := eapply rw_cells_transport; [exact H| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add length]; lia].
Local Ltac xportk H MU WM K := eapply rw_cells_transport; [exact H| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add length]; first [K; lia | lia]].
assert (AR' : AREP AH L st X m').
{ eapply (arep_ext_sm0 _ _ _ HL L st X m m' (bv_unsigned sp) (al_fake L) flag F ALO AR MU WM); first [reflexivity | lia]. }
assert (HFK' : AFAKE L (FB0 F :: LB) m').
{ split; [exact G|]. split.
{ unfold afake_cells. split; [xport REAL MU WM|]. split; [xport DTVP MU WM|]. split; [xport DV MU WM|]. split; [xport DTV1 MU WM|].
split; [xportk BD MU WM ltac:(clear -G5s G6 G9 G3 GL1 BOT LO SPT HFLAG HFF PB SHF SB1 SB3 SHD ATR)|]. split; [xport CF MU WM|]. split; [xport VERB MU WM|]. eapply dc_at_any2; [exact T48| exact WM| clear -G7I; lia]. }
split; [exists (Z_to_bv 64 (hn + 1)), h1, h2, hs; exact HNT2|].
split; [xportk LOG MU WM ltac:(clear -G3 GL1 BOT LO SPT HFLAG HFF PB SHF SHD ATR)|]. split; [xportk NGC MU WM ltac:(clear -G3 GL1 BOT LO SPT HFLAG HFF PB SHF SHD ATR)|].
split; [eapply dc_at_any; [exact DC1| exact WM| lia]|].
split; [eapply dc_at_any; [exact DC2| exact WM| lia]|].
split.
- intros c pos' b Hc Hp Hb NZ.
destruct (Z.eq_dec c 0) as [->|NC]; [destruct (Z.eq_dec pos' pos) as [->|NP]|].
+ left. rewrite <- EFR. unfold fk_fsize. reflexivity.
+ right. pose proof (fk_flags_disjoint L 0 pos' 0 pos Hc Hp Hc ltac:(unfold fk_nframes; cbn; lia) ltac:(congruence)) as NE.
rewrite <- EFL in NE. pose proof (fk_flag_range L 0 pos' Hc Hp) as FRG.
rewrite OUT in Hb by (first [clear -FRG NE Hb G1 G3 GL1 GL2 GL3 GL4 BOT LO SPT HFF HFLAG PB SHD SHF ATR; unfold FAKESZ in *; lia | unfold FAKESZ in *; lia]). eapply FL; eauto.
+ right. pose proof (fk_flags_disjoint L c pos' 0 pos Hc Hp ltac:(unfold FK_NCLS; lia) ltac:(unfold fk_nframes; cbn; lia) ltac:(congruence)) as NE.
rewrite <- EFL in NE. pose proof (fk_flag_range L c pos' Hc Hp) as FRG.
rewrite OUT in Hb by (first [clear -FRG NE Hb G1 G3 GL1 GL2 GL3 GL4 BOT LO SPT HFF HFLAG PB SHD SHF ATR; unfold FAKESZ in *; lia | unfold FAKESZ in *; lia]). eapply FL; eauto.
- intros c F' n' [E|Hin].
+ injection E as <- <- <-. split; [unfold FK_NCLS; lia|]. split; [reflexivity|].
exists pos. split; [unfold fk_nframes; cbn; lia|]. split; [exact EFR|].
rewrite <- EFL. apply (rw_C1_high m' flag _ FL1). lia.
+ destruct (LV c F' n' Hin) as (Hc & Hn & pos' & Hp & HF' & B1).
split; [exact Hc|]. split; [exact Hn|]. exists pos'. split; [exact Hp|]. split; [exact HF'|].
assert (NE : fk_flag L c pos' <> flag).
{ rewrite EFL. apply (fk_flags_disjoint L c pos' 0 pos Hc Hp ltac:(unfold FK_NCLS; lia) ltac:(unfold fk_nframes; cbn; lia)).
intros E. injection E as -> ->. apply NOTIN. rewrite EFR, <- HF'. rewrite Hn in Hin. unfold fk_fsize in Hin.
cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.add] in Hin. exact Hin. }
pose proof (fk_flag_range L c pos' Hc Hp) as FRG. rewrite OUT by (first [clear -FRG NE G1 G3 GL1 GL2 GL3 GL4 BOT LO SPT HFF HFLAG PB SHD SHF ATR; unfold FAKESZ in *; lia | unfold FAKESZ in *; lia]). exact B1. }
assert (BL' : ablocks L st X (FB0 F :: LB)).
{ destruct BL as (B1 & B2 & B3 & B4). split; [|split; [|split]].
- intros p A n [E|Hin]; [discriminate| exact (B1 p A n Hin)].
- intros c A n [E|Hin]; [| exact (B2 c A n Hin)]. injection E as <- <- <-. unfold FAKESZ in *; lia.
- cbn. exact B3.
- constructor; [exact NOTIN| exact B4]. }
assert (AHP' : AHEAP_P AH L RNG st (FB0 F :: LB) m').
{ split; [exact ALO|]. split; [exact ARNG|]. split; [exists X; split; [exact AR'| exact BL']|]. cbn [AFake_arep.AH ah_fake]. exact HFK'. }
assert (BLK : forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b) /\ ab_addr b + ab_size b <= ATOP
/\ (ab_addr b + ab_size b <= al_fake L \/ al_fake L + 36864 <= ab_addr b)
/\ (ab_addr b + ab_size b <= F \/ F + 64 <= ab_addr b)).
{ intros b Hb. destruct b as [[p|c'] A' n']; cbn.
- pose proof (HB_FAKE _ _ _ L RNG st LB m p A' n' AHP Hb) as [[Q1 [Q2 [Q3 Q4]]] D]. split; [exact Q1|]. first [clear -Q2 Q3 Q4 D HFF PB G1 G3 GL1 ATR; unfold FAKESZ in *; lia | lia].
- pose proof (afake_lb L LB m c' A' n' HFK Hb) as (Hc' & Hn' & Np' & _ & X1 & X2 & X3 & X4 & pos' & Hp' & HF' & _).
assert (NEQ : (c', pos') <> (0, pos)).
{ intros E; injection E as -> ->. apply NOTIN. rewrite EFR, <- HF'. rewrite Hn' in Hb.
replace (fk_fsize 0) with 64 in Hb by reflexivity. exact Hb. }
pose proof (fk_frames_disjoint L c' pos' 0 pos Hc' Hp' ltac:(unfold FK_NCLS; lia) ltac:(unfold fk_nframes; cbn; lia) NEQ) as DJ.
rewrite <- HF', <- EFR, <- Hn' in DJ. replace (fk_fsize 0) with 64 in DJ by reflexivity.
split; [exact X3|]. first [clear -X1 X2 X4 DJ; unfold FAKESZ in *; lia | unfold FAKESZ in *; lia]. }
assert (CLA : forall a', (ATOP <= a' < 2^47 \/ in_ranges CI a' \/ in_fake LB a') ->
0 <= a' < 2^47 /\ ~ (F <= a' < F + 64)).
{ intros a' [X1|[(iv & Hiv & Hr)|(c' & FA & fn & Hb & Hr)]];
[ atop_facts; clear - X1 G3 HFF PB; lia | pose proof (CI_OK iv Hiv); clear - Hr H GL1 HFF PB; lia |].
destruct (BLK _ Hb) as (Y1 & Y2 & Y3 & Y4). cbn in Y1, Y2, Y3, Y4, Hr. apply ablk_lin in Y1. clear - Y1 Y2 Y3 Y4 Hr ATR. lia. }
clear R2 R11 R13 R14 R15 R16 R24 R25 R28 REAL DTVP DV DTV1 BD CF VERB T48 T48' HNT HNT' LOG NGC DC1 DC2 GB0 G08 DESC FL0 F24 F56 SH0
D24 D56 DS2 RR A10.
assert (HPR : aheap_pres CI LB (bv_unsigned sp) m m').
{ intros a Ha Hc. split; [| intros W0; apply WM; exact W0].
destruct Hc as [Hs|[(iv & Hiv & Hr)|[(b & Hb & Hr)|(a' & Ha' & ->)]]].
- apply OUT; clear - Ha Hs SK3 BOT LO GL1 G3 HFF HFLAG PB ATR; lia.
- pose proof (CI_OK iv Hiv). apply OUT; clear - Ha H Hr SK3 BOT LO GL1 G3 HFF HFLAG PB ATR; lia.
- destruct (BLK b Hb) as (Y1 & Y2 & Y3 & Y4). unfold ablk, AIMG_HI, KLS in Y1. apply OUT; clear - Ha Y1 Y2 Y3 Y4 Hr SK3 BOT LO GL1 G3 HFF HFLAG PB ATR; lia.
- destruct (CLA a' Ha') as [A'R NA].
assert (SHA : shad a' = 2147450880 + a' / 8) by (unfold shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; reflexivity).
rewrite SHA in Ha |- *.
pose proof G2 as G2b. unfold ablk, AIMG_HI, KLS in G2b.
apply OUT; clear - Ha A'R NA F64 G2b G3 HFF HFLAG PB LO SK3 BOT ATR; Z.div_mod_to_equations; lia. }
pose proof (dc_at_any m m' F 24 DJ0 WM ltac:(lia)) as DJ0'.
pose proof (dc_at_any m m' (F + 32) 24 DJ1 WM ltac:(lia)) as DJ1'.
destruct (dc_take m' F 24 8 DJ0' ltac:(lia)) as [DW0 DW12]. replace (24 - 8) with 16 in DW12 by reflexivity.
destruct (c8_of_dc m' F DW0) as [j0 J0]. destruct (c8c8_of_dc m' (F + 8) DW12) as (j1 & j2 & J12).
destruct DJ1' as [junk1 J1]. change (Z.to_nat 24) with 24%nat in J1.
assert (LJ : length junk1 = 24%nat) by (destruct J1 as [[[WF _] _] _]; cbn in WF; lia).
assert (FRM : rw_cells asegs m' F [C8 j0; C8 j1; C8 j2; CB 32 (le8 sp ++ junk1); C8 (Z_to_bv 64 (fflag L 0 F))]).
{ rewrite EFF.
apply (proj2 (rw_cells_app asegs m' F [C8 j0] _)). split; [exact J0|]. cbn [cells_size csize Nat.add].
apply (proj2 (rw_cells_app asegs m' (F + Z.of_nat 8) [C8 j1; C8 j2] _)). split; [replace (F + Z.of_nat 8) with (F + 8) by lia; exact J12|].
cbn [cells_size csize Nat.add].
apply (proj2 (rw_cells_app asegs m' (F + Z.of_nat 8 + Z.of_nat 16) [CB 32 (le8 sp ++ junk1)] _)). split.
- replace (F + Z.of_nat 8 + Z.of_nat 16) with (F + 24) by lia.
eapply rw_cells_recast; [apply (proj2 (rw_cells_app asegs m' (F + 24) [C8 sp] [CB 24 junk1])); split; [exact F24'|];
cbn [cells_size csize Nat.add]; replace (F + 24 + Z.of_nat 8) with (F + 32) by lia; exact J1 | | |].
+ cbn [cells_wf cell_wf]. rewrite length_app, length_le8, LJ. split; [reflexivity| exact I].
+ cbn [cells_bytes cbytes app]. rewrite <- app_assoc. cbn [app]. rewrite !app_nil_r. reflexivity.
+ reflexivity.
- cbn [cells_size csize Nat.add]. replace (F + Z.of_nat 8 + Z.of_nat 16 + Z.of_nat 32) with (F + 56) by lia. exact F56'. }
unfold AFake_arep.sm0_postP. exists F. do 14 eexists. exists m', j0, j1, j2, (le8 sp ++ junk1).
split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact HPR|]. split; [exact AHP'|].
split; [exact F64|]. split; [eapply ablk_sub; [exact G2| clear - HFF PB; lia| clear - HFF PB; lia]|]. split; [atop_facts; clear - G3 HFF PB; lia|].
split; [exact FRM|]. split; [exact SH'|].
split; [eapply rng_sub'; [exact A7| clear - GL1 G3 HFF PB; lia]|].
eapply rng_sub'; [exact A8| rewrite SHL; clear - SB1 SB2 PB; lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Section Inst.
Variable AI : AMallocIface.
Hypothesis E : AHEAP AI = AHEAP_P AH.
Hypothesis EC : aci AI = CI.
#[using="DI AQ ASEC HL CI CI_OK E EC"] Lemma stack_malloc_0r_AI : stack_malloc_0r_stmt AI fflag afake_rng.
Proof.
unfold stack_malloc_0r_stmt. intros until lo. intros AHx LE MI ST BOT LO SPT TP RSTK RI RFS.
rewrite E in AHx.
eapply evtF_mono; [eapply stack_malloc_0r_P; eassumption|].
cbv beta. intros ms' PO. unfold AFake_arep.sm0_postP in PO. unfold sm0r_post.
destruct PO as (F & x0 & x1 & x2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & m' & j0 & j1 & j2 & junk & EQ & MI' & ST' & HPR & AH' & REST).
exists F, x0, x1, x2, y1, y2, y3, y4, y5, y6, y7, x3, x4, x5, x6, m', j0, j1, j2, junk.
rewrite E, EC. repeat (split; [assumption|]). exact REST.
Qed.
End Inst.
End S.
End CANSEC1.
