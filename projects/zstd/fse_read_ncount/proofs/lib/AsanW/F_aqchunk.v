(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Arr InitMem.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import AImg ABase AQConst ABytes ADepot_iface.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import AKit AKit2 AKitQ F_aunwind.
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
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes_k12.
(* [comment removed for export] *)

Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac band_lin :=
repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Section CANSEC1. Context {rc : runConstT}.
Section QChunk.
Variable DI : ADepotIface.
Definition qchunk_post (L : alayout) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(t hm n S lo : Z) (m : amem) : machine_state -> Prop :=
fun ms' => exists (id : Z) t0 t1 t2 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0x9f0f0) (Z_to_bv 64 (t + 80)) (Z_to_bv 64 (t + 208)) (Z_to_bv 64 S)
(Z_to_bv 64 hm) (Z_to_bv 64 n) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x3659c) fc None m' (seg_rom asegs)
/\ munch [(bv_unsigned sp - 1072, bv_unsigned sp); (hm + 16, hm + 24); (ADEPOT_LO, ADEPOT_HI); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608)]%Z m m'
/\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp)
/\ rw_cells asegs m' (hm + 16) [C8 (Z_to_bv 64 id)] /\ 0 < id < 2^31
/\ ADEPOT DI L m'.
#[using="Type"] Lemma qchunk_spec : forall (L : alayout) (t hm S : Z) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : amem) (n ctx b1 actx lo sz pc : Z) (uw top bot : word) (tb : list word) (tr : list Z),
stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 48 - ADEPOT_STACK ->
mem_inv asegs m ->
tp = Z_to_bv 64 ATP ->
a0 = Z_to_bv 64 AINSTANCE -> a1 = Z_to_bv 64 hm -> a3 = Z_to_bv 64 S ->
rw_cells asegs m hm [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)] ->
rw_cells asegs m (hm + 16) [C8 uw] -> 0 <= b1 < 256 -> 0 <= n < 2^32 ->
AIMG_HI <= hm -> hm + 24 <= ATOP ->
rw_cells asegs m ATSDI [C1 (Z_to_bv 8 1)] -> rw_cells asegs m ATSDK [C4 (Z_to_bv 64 0)] ->
rw_cells asegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells asegs m ATSD [C8 (Z_to_bv 64 ctx)] ->
rw_cells asegs m (ctx + 152) [C8 (Z_to_bv 64 t)] -> rw_cells asegs m (ctx + 8) [C4 (Z_to_bv 64 0)] ->
rw_cells asegs m t [C8 (Z_to_bv 64 ctx); C8 top; C8 bot] ->
0 < ctx -> AIMG_HI <= ctx -> ctx + 4096 <= ATOP -> iclr t 4096 -> t + 4096 <= ATOP ->
rw_cells asegs m S [C8 (Z_to_bv 64 (S + 16)); C4 (Z_to_bv 64 sz); C4 (Z_to_bv 64 0)] ->
u64arr asegs m (S + 16) tb -> length tb = 255%nat ->
sz = 1 + Z.of_nat (length tr) -> sz <= 255 ->
map bv_unsigned (firstn (Datatypes.S (length tr)) tb) = pc :: tr -> In (pc :: tr) (al_U L) ->
bv_unsigned sp <= S -> S + 2056 <= 2^47 ->
ADEPOT DI L m ->
AIMG_HI <= al_nodes L -> al_nodes L + 1048576 <= ATOP -> AIMG_HI <= al_store L -> al_store L + 8388608 <= ATOP ->
(hm + 24 <= al_nodes L \/ al_nodes L + 1048576 <= hm) -> (hm + 24 <= al_store L \/ al_store L + 8388608 <= hm) ->
(hm + 24 <= t \/ t + 4096 <= hm) -> (hm + 24 <= ctx \/ ctx + 4096 <= hm) ->
(t + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= t) -> (t + 4096 <= al_store L \/ al_store L + 8388608 <= t) ->
(ctx + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= ctx) -> (ctx + 4096 <= al_store L \/ al_store L + 8388608 <= ctx) ->
rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG S 2056 -> rng RNG ctx 4096 -> rng RNG t 4096 -> rng RNG hm 24 ->
rng RNG (al_nodes L) 1048576 -> rng RNG (al_store L) 8388608 ->
evtF asegs RNG (qchunk_post L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t hm n S lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x36424) fc None m (seg_rom asegs)).
Proof.
intros until tr. intros ST CEIL LO MI TP -> -> -> HD UW B1 N H0 H1 TI TK T88 TSD CT CT8 TT CX0 C0 C1 T0 T1 SO TB LTB SZ SZB TR TU SPS STOP
DEP N0 N1 R0 R1 DHN DHR DHT DHC DTN DTS DCN DCS RIMG RSTK RS RCTX RT RH RND RSR. band_lin.
unfold AIMG_HI, AINSTANCE, AQUAR_Q, ATSDI, ATSDK, ATP88, ATSD in *.
pose proof (munch_refl [(bv_unsigned sp - 1072, bv_unsigned sp); (hm + 16, hm + 24); (ADEPOT_LO, ADEPOT_HI); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
word_range sp SPR.
pose proof (munch_refl [(bv_unsigned sp - 1072, bv_unsigned sp)]%Z m) as MU0. pose proof (wmono_refl asegs m) as WM0.
Local Ltac2 Set LiaHints.tbl := fun () => "03;0?100583406.117  10189594146.11810189594146.14210345787758.12011377951233.13211601497306.11711801586693.12011805467289.11711805467289.11811805467289.11911805467289.12011805467289.14212876582062.11913205419683.11813205419683.1421343986644.135 13629548202.13313696072622.1191382808063.125 14793086516.11514793086516.11614869079534.12016760036534.12016872280319.11917212185306.12017755388179.14217776320431.11817776320431.1391800609155.119 1800609155.140 1811592986.115 18213949967.13518612176510.11718748206397.12019432966222.11919601172814.11919682054918.11320313996398.11920979536691.11821716436098.11821716436098.14222284289799.12022389541692.1172260382799.135 22632813821.12022700267513.12123589365338.11924336903790.12024638473347.12024638473347.14125632264527.1352597469155.139 27822129059.11827822129059.14227906986121.13228417259964.11928485987241.12628680522126.13529193796462.11929321812773.11230430348557.12430607025542.11230717345253.14231378308326.11032307613550.11732805605487.14432852234768.12033364883216.11733680001082.12033683797454.1203390055657.125 34430152252.12034466804606.12035101720189.12035850771151.13536059409850.11236115622446.11936115622446.14036635088338.11336646331050.13337317216127.12037381576063.12037429491794.11837429491794.14237436222938.1203805649895.142 38446806799.11838446806799.14038508687005.1423888239342.120 39896594704.12040457739452.11940491529500.11840491529500.14240641857600.12441030367075.13542535283918.12042799229438.11942831019478.11842831019478.14242970897846.13943061363337.1084353604764.142 43987951406.11943987951406.14043988483203.11743988483203.13944484923210.12044536297306.13945221239098.12045454594454.13345848756903.11746134254574.12046298861963.12646468661564.12047129173530.13247143256106.13947988463743.12048057003647.12049425192486.11249649769127.12050317564526.11950354202374.11850354202374.14250362574674.11850362574674.14250487304575.11750500879323.11350693720814.12050734000704.13551711223320.13152105090727.11952567164907.11752567164907.11852567164907.11952567164907.12052567164907.14252579502455.1355300105810.118 5300105810.142 53415683838.11953767577775.11853767577775.13954243526019.11954243526019.14054404701703.13554636957394.11854636957394.14254722921710.11955909760549.11356050151177.11956172315833.11156184866200.1125627121139.130 563227834.119  56323790752.12056324080430.12056675150386.11856729251374.11756981146544.11857745675194.11959134147250.11859314873579.1145953130734.120 59586081465.14060385159294.12060858483367.12061158554239.11761482382924.11561534126183.14161628829678.11761674577390.12061917199020.11761917199023.13961939782288.1466213631999.119 62575797294.12062704248302.11963045513727.11963235321900.11663235321900.13863305555623.11964352634714.11964997134979.12064997134979.14165206925737.12565440506593.1256559606672.119 6637455766.115 66423386478.1196647326864.119 67469470029.11767469470029.13467934818849.12068096078318.117760149966.117  7754842205.142 7848643581.120 8583720762.117 8684881006.119 8800126135.136 8925969151.119 9333008750.119 00000900E00N00W00[00g01B01C01D01E01F01G01S01_01h01i01j02602702F02U02^02g03303?03@03D03H03I03J03V03i03n04;04G04S04Y04b04c04h05805905=05P05]06k07707@07A07B07U07V07b07k07o08308409F09O09S09T09U09V09W09`09a09j0:30:80:D0:E0:I0:N0:[0:n0:o0;30;70;B0;E0;Q0;]0;f0;j0<60<70<80<90<E0<N0<W0<[0<d0=80=90>?0>K0>P0>U0>Y0>Z0>^0>n0?20?60?70?80?90?=0?B0?C0?D0?M0?N0?R0?V0?Z0?f0@20@70@80@A0@M0@N0@W0@[0@g0@l0A50AL0AM0AN0AO0AP0AQ0AR0AS0Bi0C20C60C;0C?0CC0CD0CE0CF0CO0CS0C\0C`0Ca0Cb0Cc0Cg0Cl0D<0DH0DI0DU0DY0D^0Dj0E50E>0E?0ED0EE0EQ0ER0ES0E\0Ee0Ei0Em0F00F<0FH0FQ0F]0Fa0Fe0Ff0G20G30G40G50G60G?0G@0GI0GR0Gf0H`0I00I90IE0II0IV0I[0Id0K80KD0KMS4CEIL2LOS4CEIL2LO2T1S3LTB3DHTS4CEIL2LOS2IDS4CEIL2LO2H1S3Hsp4CEIL2LO2C12H13LTB3SPSSSSSSS4CEIL2LO2H1S4CEIL2LO2C1S3LTB3DHCFSS4CEIL2LO2H1SS4CEIL2LO3SPR1HS4CEIL2LO3SPR1HS4CEIL2LOS3SPS3HspS4CEIL2LO2C1S4CEIL2LO2H1SS2LOS2LOSSS3LTB2SZ3SZBS4CEIL2LO2N02R03HspS3SPSS4CEIL2LO3HspS4CEIL2LO2T1S4CEIL2LO2T1S4STOPS4CEIL2LOSS3SPSS4CEIL2LO2H13SPSFS2HBS4CEIL2LO2N02R03HspS4CEIL2LO3HspS2H02C03LTB2N02R03DHN3DHR3DHT3DHC3DTN3DTS3DCN3DCS3Hsp1H4CEIL2LO2H12C12T12N12R1S4CEIL2LO2H1S4CEIL2LOSSS4CEIL2LO2N02R03HspSS4CEIL2LO2C1S3LTB3DHCS2LOS2HBSS4CEIL2LO2H02H12C02C12T02T13LTB2N02N12R02R13DHN3DHR3DHT3DHC3DTN3DTS3DCN3DCS2K03HspS4CEIL2LOS2LOSSSSS4CEIL2LOSS3LTB3SPSS3LTB3SPSS3SPRS4CEIL2LO2T1SS2HBS3SPSS4CEIL2LO3HspS4CEIL2LO2N02R03HspSS2LOS2LOS2T02T13LTBS1NS4CEIL2LO2C1S4CEIL2LO2C1S4CEIL2LOS2H0S4CEIL2LO2H1SSSS4CEIL2LO2H1S4CEIL2LOS3LTB3SPSS2HBS3LTB3SPSS4CEIL2LO2H13LTB3SPSSS4CEIL2LO2H12C12T02T13LTB2N12R13DHN3DHR3DHT3DHC3DTN3DTS3DCN3DCS2K03HspS4CEIL2LO2T1S3SPSS3SPRS2HBFS2LOS4CEIL2LO2H13SPSS2LOS2LOSSFS2IDS3SPRSSS4CEIL2LOSS2HBS2IDS2IDS4CEIL2LO2C1S4CEIL2LO2C1S3CX0SS4CEIL2LOS4CEIL2LO2H1SS4CEIL2LOS2H0S4CEIL2LO2C1S3SPSS4CEIL2LOS4CEIL2LO3SPS2N12R13HspSSSSSSSS4CEIL2LO2N12R13Hsp3SPS2H02H12C02C12T02T13LTB2N02R03DHN3DHR3DHT3DHC3DTN3DTS3DCN3DCS2K0S4CEIL2LOS2H0S3SPSS2LOS2LOSSFS4CEIL2LOS2H0S4CEIL2LOS2LOSSSS2IDS3SPRS4CEIL2LO2H13HspS4CEIL2LO2H1SS4CEIL2LO2H1S2HBS3SPRS4CEIL2LO2H1S2T03LTB2K0S4CEIL2LOSS3SPSSS4CEIL2LO2C1SSS4CEIL2LOS4CEIL2LOS2LOS2LOS1NS4CEIL2LO2C1S4CEIL2LO2H1S4CEIL2LOS4CEIL2LO2C1S2LOS2LOSS4CEIL2LO2H1SSSSS3LTB3SPSSS4CEIL2LOS3LTB3SPSS4CEIL2LO2N12R12Ha1HS2H02C02T03LTB2N02R03DHN3DHR3DHT3DHC3DTN3DTS3DCN3DCS2K02HaS4CEIL2LO2T13HspS4CEIL2LOS4CEIL2LO2T1S2H0S4CEIL2LO3HspS3SPRS4CEIL2LOS4CEIL2LO2H02H12C02C12T02T13LTB2N02N12R02R13DHN3DHR3DHT3DHC3DTN3DTS3DCN3DCS2K03Hsp1HS4CEIL2LO2C1S4CEIL2LO".
carve_frame 48%nat ST.
do 7 step.
step. lstep. step. step. if_lit.
step. step.
box RT. box RH. box RS.
step. call_sp get_current_thread_spec;
[exact ST | exact CEIL | lia | exact MI | exact TP | exact TI | exact TK | exact T88 | exact TSD | exact CT | lia | exact C1 | solve_rng | ].
unbox RT. unbox RH. unbox RS. rename POST into ST. try rename MI0 into MI.
step. if_cases K0; zify_cond K0; [exfalso; lia|].
step. step.
rw_split SO 1%nat SOa SOb. apply rw_cells_C4C4_to_C8 in SOb; [|lia].
step. lstep. step. step.
box RT. box RH. box RCTX.
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
assert (DEP1 : ADEPOT DI L mm)
by (eapply (adi_frame DI); [exact DEP| exact MU0| exact WM0|];
constructor; [| constructor]; cbn [fst snd]; intros a Ha; unfold AIMG_HI in *; lia) end.
clear MU0 WM0 DEP.
step. call_sp (adi_put DI L);
[exact ST | exact CEIL | lia | exact MI | exact TP | reflexivity | reflexivity | exact SZ | exact SZB | exact TB | exact LTB | exact TR | exact TU
| lia | lia | exact DEP1 | exact N0 | exact N1 | exact R0 | exact R1 | solve_rng | solve_rng | ].
unbox RT. unbox RH. unbox RCTX. try rename MI0 into MI. clear DEP1.
match goal with H : stk asegs ?mm lo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into ST end.
match goal with H : ADEPOT DI L ?mm |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into DEP2 end.
match goal with H : 0 < ?i < 2 ^ 31 |- _ => rename H into ID; rename i into id end.
zstep. zstep. zstep. zstep.
rewrite Z.lor_0_l. rewrite (Z.mod_small id 4294967296) by lia.
snapshot [(hm + 16, hm + 24)]%Z MU1 WM1.
step.
zstep. lstep. lstep. zstep. zstep.
zstep. zstep. rewrite Z.lor_0_l.
step. step.
do 8 step.
release_frame FR ST (bv_unsigned sp).
unfold qchunk_post. finish.
- exact UW.
- lia.
- lia.
- eapply (adi_frame DI); [exact DEP2| exact MU1| exact WM1|].
constructor; [|constructor]. cbn [fst snd]. intros a Ha. unfold AIMG_HI in *. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End QChunk.
End CANSEC1.
