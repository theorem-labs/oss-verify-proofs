(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import Arr InitMem.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import AImg ABase AQConst ABytes ADepot_iface.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import AKit AKit2 AKitQ F_aunwind.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.


Section CANSEC1. Context {rc : runConstT}.
Section QChunk.
Variable DI : ADepotIface.

(* [comment removed for export] *)
Definition qchunk_post (L : alayout) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t hm n S lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (id : Z) t0 t1 t2 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0x9daf0) (Z_to_bv 64 (t + 80)) (Z_to_bv 64 (t + 208)) (Z_to_bv 64 S)
                  (Z_to_bv 64 hm) (Z_to_bv 64 n) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x3532c) fc None m' (seg_rom asegs)
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
  (* [comment removed for export] *)
  rw_cells asegs m hm [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 actx)] ->
  rw_cells asegs m (hm + 16) [C8 uw] -> 0 <= b1 < 256 -> 0 <= n < 2^32 ->
  AIMG_HI <= hm -> hm + 24 <= ATOP ->
  (* [comment removed for export] *)
  rw_cells asegs m ATSDI [C1 (Z_to_bv 8 1)] -> rw_cells asegs m ATSDK [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells asegs m ATSD [C8 (Z_to_bv 64 ctx)] ->
  rw_cells asegs m (ctx + 152) [C8 (Z_to_bv 64 t)] -> rw_cells asegs m (ctx + 8) [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m t [C8 (Z_to_bv 64 ctx); C8 top; C8 bot] ->
  0 < ctx -> AIMG_HI <= ctx -> ctx + 4096 <= ATOP -> iclr t 4096 -> t + 4096 <= ATOP ->
  (* [comment removed for export] *)
  rw_cells asegs m S [C8 (Z_to_bv 64 (S + 16)); C4 (Z_to_bv 64 sz); C4 (Z_to_bv 64 0)] ->
  u64arr asegs m (S + 16) tb -> length tb = 255%nat ->
  sz = 1 + Z.of_nat (length tr) -> sz <= 255 ->
  map bv_unsigned (firstn (Datatypes.S (length tr)) tb) = pc :: tr -> In (pc :: tr) (al_U L) ->
  bv_unsigned sp <= S -> S + 2056 <= 2^47 ->
  (* [comment removed for export] *)
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
        F (Z_to_bv 64 0x351b4) fc None m (seg_rom asegs)).
Proof.
  intros until tr. intros ST CEIL LO MI TP -> -> -> HD UW B1 N H0 H1 TI TK T88 TSD CT CT8 TT CX0 C0 C1 T0 T1 SO TB LTB SZ SZB TR TU SPS STOP
         DEP N0 N1 R0 R1 DHN DHR DHT DHC DTN DTS DCN DCS RIMG RSTK RS RCTX RT RH RND RSR. band_lin.   (* [comment removed for export] *)
  unfold AIMG_HI, AINSTANCE, AQUAR_Q, ATSDI, ATSDK, ATP88, ATSD in *.
  pose proof (munch_refl [(bv_unsigned sp - 1072, bv_unsigned sp); (hm + 16, hm + 24); (ADEPOT_LO, ADEPOT_HI); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - 1072, bv_unsigned sp)]%Z m) as MU0. pose proof (wmono_refl asegs m) as WM0.
  Local Ltac2 Set LiaHints.tbl := fun () => "03;0?10189594146.11810189594146.14211377951233.13211601497306.11711801586693.12011805467289.11711805467289.11811805467289.11911805467289.12011805467289.14211899494927.13512429510126.12012876582062.11913205419683.11813205419683.1421343986644.135 13629548202.13313696072622.1191382808063.125 14761575534.11914793086516.11514793086516.11615401314670.11916760036534.12016872280319.11917212185306.12017755388179.14217776320431.11817776320431.1391800609155.119 1800609155.140 1811592986.115 18612176510.11718694006766.11719317809487.13519432966222.11919601172814.11919682054918.11320979536691.11821716436098.11821716436098.14222284289799.12022389541692.11722700267513.12123028554134.13323589365338.11924638473347.12024638473347.1412597469155.139 27133822446.11927822129059.11827822129059.14227906986121.13228417259964.11928485987241.12628680522126.13529321812773.11229535791823.13530401015406.12030430348557.12430607025542.11230717345253.14231378308326.11032805605487.14432852234768.12033364883216.11733680001082.12033683797454.1203390055657.125 34430152252.12034466804606.12036059409850.11236115622446.11936115622446.14036635088338.11336646331050.13337317216127.12037381576063.12037436222938.1203805649895.142 38446806799.11838446806799.14038508687005.14238567244270.11739093924078.12039896594704.12040457739452.11940491529500.11840491529500.14240608002030.11740641857600.12440653749742.12041030367075.13541834437230.11942535283918.12042799229438.11942831019478.11842831019478.14242970897846.13943061363337.10843493603410.11843493603410.1424353604764.142 43987951406.11943987951406.14043988483203.11743988483203.13944484923210.12044536297306.13945221239098.12045415010670.11945848756903.11746162087634.11846162087634.14246298861963.12646468661564.12047129173530.13247143256106.13947988463743.12048057003647.12049425192486.11249649769127.12050077211645.12050354202374.11850354202374.14250487304575.11750500879323.11350734000704.13551711223320.13152105090727.11952198366190.12052567164907.11752567164907.11852567164907.11952567164907.12052567164907.14252579502455.13552994560594.11852994560594.14253415683838.11953767577775.11853767577775.13954243526019.11954243526019.14054404701703.13555909760549.11356050151177.11956172315833.11156184866200.1125627121139.130 563227834.119  56323790752.12056324080430.12056426686290.11856426686290.14256675150386.11856729251374.11756757832430.12056981146544.11857745675194.11958057019758.12059134147250.11859314873579.11459586081465.14060385159294.12060797519086.11960858483367.12060976774461.12061158554239.11761482382924.11561534126183.14161917199020.11761917199023.13961939782288.1466213631999.119 62575797294.12063045513727.11963235321900.11663235321900.13863305555623.11964352634714.11964665371727.13564862446845.12064997134979.12064997134979.14165036941718.11565206925737.12565440506593.12565458892654.1176559606672.119 6647326864.119 67469470029.11767469470029.13467934818849.12068008320110.119760149966.117  7754842205.142 8172837742.119 8583720762.117 8610795133.120 8800126135.136 8925969151.119 9956545262.120 00000<00E00I00U01001101201301401501H01Q01]01i02202302402@02A02J02Y02h03103:03F03R03S03W03[03\03]03i03n04704J04V04b04h04i04n05>05?05C06Q06R06^06_06`06a06j07607?07C07G07H08Z08^09109:09;09<09=09>09?09H09Q09V09b09c09g09l09m0:10:50:@0:C0:O0:[0:g0:h0:i0:j0;60;?0;H0;Q0;U0;^0<20<;0<<0<E0=K0=T0=`0=e0=j0=n0=o0>30><0>@0>P0>T0>X0>Y0>Z0>[0>_0>d0>m0>n0?70?;0?<0?@0?D0?H0?T0?`0?e0?f0@30@?0@@0@L0@Q0@h0@i0@j0A30A40A50A60A70A80BN0BW0B[0B`0Bd0Bh0Bi0Bj0Bk0Bo0C00C10C20C60C;0CK0CW0C`0Cd0Ce0D10D:0D>0DC0DL0DX0Dc0Dd0Di0E20E30E@0EL0EM0EN0ER0EV0EY0Ee0F10F=0FA0FE0FF0FR0Fe0G20G30G40G50G60G70G@0GI0GR0Gf0H`0I00I90IE0II0IR0IW0Id0K80KD0KMS4CEIL2LO2T1S3LTB3DHTS2IDS4CEIL2LO2H1S3Hsp4CEIL2LO2C12H13LTB3SPSSSSSSS4CEIL2LO2N02R03HspS4CEIL2LOS4CEIL2LO2H1S4CEIL2LO2C1S3LTB3DHCFSS4CEIL2LO2H1SS4CEIL2LOS4CEIL2LO3SPR1HS4CEIL2LO3SPR1HS4CEIL2LOS3SPS3HspS4CEIL2LO2C1S4CEIL2LO2H1SS2LOS2LOSSS3LTB2SZ3SZBS3SPSS4CEIL2LOS4CEIL2LO2N02R03HspS4CEIL2LO2T1S4CEIL2LO2T1S4STOPSS3SPSS4CEIL2LO2H13SPSFS2HBS2H02C03LTB2N02R03DHN3DHR3DHT3DHC3DTN3DTS3DCN3DCS3Hsp1H4CEIL2LO2H12C12T12N12R1SS4CEIL2LO2H1SSSS4CEIL2LOS4CEIL2LO2C1S3LTB3DHCS2LOS2HBSS4CEIL2LO2H02H12C02C12T02T13LTB2N02N12R02R13DHN3DHR3DHT3DHC3DTN3DTS3DCN3DCS2K03HspS2LOS4CEIL2LO2N02R03HspS4CEIL2LOSSSSSS3LTB3SPSS3LTB3SPSS3SPRS4CEIL2LO2T1SS2HBS3SPSSS2LOS2LOS2T02T13LTBS1NS4CEIL2LO2C1S4CEIL2LO2C1S4CEIL2LO2H1SSSS4CEIL2LO2H1S4CEIL2LOS4CEIL2LOS3LTB3SPSS2HBS3LTB3SPSS4CEIL2LO2H13LTB3SPSS4CEIL2LOSS4CEIL2LOS4CEIL2LO2H12C12T02T13LTB2N12R13DHN3DHR3DHT3DHC3DTN3DTS3DCN3DCS2K03HspS4CEIL2LOS4CEIL2LO2T1S3SPSS3SPRS2HBFS2LOS4CEIL2LOS2H0S4CEIL2LO2H13SPSS2LOS2LOSSFS2IDS3SPRS4CEIL2LOSS4CEIL2LOS2H0SS2HBS2IDS2IDS4CEIL2LO2C1S4CEIL2LO2C1S3CX0SS4CEIL2LO3HspS4CEIL2LO2H1SS4CEIL2LO2C1S3SPSS4CEIL2LO3SPS2N12R13HspSSS4CEIL2LOSSSSSS4CEIL2LO2N12R13Hsp3SPS2H02H12C02C12T02T13LTB2N02R03DHN3DHR3DHT3DHC3DTN3DTS3DCN3DCS2K0S4CEIL2LOS2H0S3SPSS2LOS2LOSSFS2LOSSSS2IDS3SPRS4CEIL2LO2H13HspS4CEIL2LO2H1S4CEIL2LOS2H0SS4CEIL2LO2H1S4CEIL2LOS2HBS3SPRS4CEIL2LOS4CEIL2LO2H1S2T03LTB2K0SS3SPSS4CEIL2LOSS4CEIL2LO3HspS4CEIL2LO2C1SSS2LOS2LOS1NS4CEIL2LO2C1S4CEIL2LO2H1S4CEIL2LO2C1S2LOS2LOSS4CEIL2LO2H1S4CEIL2LO2N02R03HspS4CEIL2LO3HspSSSSSS4CEIL2LOS3LTB3SPSS3LTB3SPSS4CEIL2LO2N12R12Ha1HS2H02C02T03LTB2N02R03DHN3DHR3DHT3DHC3DTN3DTS3DCN3DCS2K02HaS4CEIL2LO2T13HspS4CEIL2LOS4CEIL2LO2T1S2H0S4CEIL2LOS3SPRS4CEIL2LO3HspS4CEIL2LO2H02H12C02C12T02T13LTB2N02N12R02R13DHN3DHR3DHT3DHC3DTN3DTS3DCN3DCS2K03Hsp1HS4CEIL2LO2C1S4CEIL2LO".
carve_frame 48%nat ST.
  do 7 step.                                   (* [comment removed for export] *)
  step. lstep. step. step. if_lit.             (* [comment removed for export] *)
  step. step.                                  (* [comment removed for export] *)
  box RT. box RH. box RS.
  step. call_sp get_current_thread_spec;
    [exact ST | exact CEIL | lia | exact MI | exact TP | exact TI | exact TK | exact T88 | exact TSD | exact CT | lia | exact C1 | solve_rng | ].
  unbox RT. unbox RH. unbox RS. rename POST into ST. try rename MI0 into MI.
  step. if_cases K0; zify_cond K0; [exfalso; lia|].          (* [comment removed for export] *)
  step. step.                                  (* [comment removed for export] *)
  rw_split SO 1%nat SOa SOb. apply rw_cells_C4C4_to_C8 in SOb; [|lia].
  step. lstep. step. step.                     (* [comment removed for export] *)
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
  zstep. zstep. zstep. zstep.                  (* [comment removed for export] *)
  rewrite Z.lor_0_l. rewrite (Z.mod_small id 4294967296) by lia.
  snapshot [(hm + 16, hm + 24)]%Z MU1 WM1.
  step.                                        (* [comment removed for export] *)
  zstep. lstep. lstep. zstep. zstep.           (* [comment removed for export] *)
  zstep. zstep. rewrite Z.lor_0_l.             (* [comment removed for export] *)
  step. step.                                  (* [comment removed for export] *)
  do 8 step.                                   (* [comment removed for export] *)
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
