(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Arr Bytes ZBridge Tac InitMem.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import ExecF Shadow.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import BImg ABase RtCells ABytes AProto AMalloc_iface AProg_kit AHarness_iface
AFake5_iface AKit FsKit AH_fse_kit AH_fse_calls AH_fse_Eiface.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import ShadowTac.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import FseWalkKitF.
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
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_hint ::= acc_hint_shadow.
Local Ltac solve_load ::= first [ solve_load_guarded | solve_load_image ].
Local Ltac solve_store ::= solve_store_guarded.
Section CANSEC1. Context {rc : runConstT}.
#[using="Type"] Lemma app_not_clientE : forall CI LB SP R k a,
(forall iv, In iv CI -> snd iv <= AIMG_HI) -> (forall iv, In iv CI -> 0 <= fst iv) ->
ablk R (R + k) -> ATOP <= SP ->
(forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b)) ->
(forall b, In b LB -> R + k <= ab_addr b \/ ab_addr b + ab_size b <= R) ->
R <= a < R + k -> ~ aclient_addr CI LB SP a.
Proof.
intros CI LB SP R k a HCI HCI0 AR HSP HLB HD Ha. pose proof (ablk_lin _ _ AR) as (R1 & R2 & R3 & R4). pose proof atop_range as ATR.
unfold aclient_addr, in_ranges, in_block, in_fake. intros [X|[(iv & Hiv & H1 & H2)|[(b & Hb & H1)|(a' & Ha' & E)]]].
- Local Ltac2 Set LiaHints.tbl := fun () => "0070>40461521065.2240463667756.2740463674142.2759308579543.3059314873579.2359314873579.2459315137787.2000000700B00N00_00h01401AS3ATR1YS3ATR2Y12HBS2Y12Y21H2H0S2AR2Ha1E1H2H02H1S2Ha2H11HS2Ha2R12H21HS3HSP2Ha2R31X".
lia.
- pose proof (HCI iv Hiv). unfold AIMG_HI in *. lia.
- destruct (HD b Hb); lia.
- unfold ablk, AIMG_HI, KLS in AR. rewrite shad_div in E. unfold ASHOFF in E.
assert (0 <= a' < 2^47).
{ destruct Ha' as [Y|[(iv & Hiv & Y1 & Y2)|(c0 & A0 & n0 & Hin0 & Y1)]].
- lia.
- pose proof (HCI iv Hiv). pose proof (HCI0 iv Hiv). unfold AIMG_HI in *. lia.
- pose proof (HLB _ Hin0) as HB. cbn in HB. apply ablk_lin in HB. lia. }
Z.div_mod_to_equations; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma shadow_not_client2048 : forall CI LB SP F a,
(forall iv, In iv CI -> snd iv <= AIMG_HI) -> (forall iv, In iv CI -> 0 <= fst iv) ->
ablk F (F + 2048) -> F mod 2048 = 0 -> ATOP <= SP ->
(forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b)) ->
(forall b, In b LB -> F + 2048 <= ab_addr b \/ ab_addr b + ab_size b <= F) ->
shad F <= a < shad F + 256 -> ~ aclient_addr CI LB SP a.
Proof.
intros CI LB SP F a HCI HCI0 AF F64 HSP HLB HD Ha. pose proof (ablk_lin _ _ AF) as (F1 & F2 & F3 & F4). pose proof atop_range as ATR.
rewrite shad_div in Ha. unfold ASHOFF in Ha.
unfold aclient_addr, in_ranges, in_block, in_fake. intros [X|[(iv & Hiv & H1 & H2)|[(b & Hb & H1)|(a' & Ha' & E)]]].
- unfold AIMG_HI in *. Z.div_mod_to_equations. Local Ltac2 Set LiaHints.tbl := fun () => "0070>47750951579.4359308579027.2859308580059.3459308580184.3759308679520.2359310676304.3859314938599.2800000H00T00j01J01S01l025S3F642Ha1E1H2H02H42H52H9S2F12Y22FA1HS3HSP2Ha2F33ATR1X1H2H0S2AF3F642Ha2F33ATR2H12HB1H2H02H5S2F31Y2FAS3F642Ha2F12H21H2H02H32H7S2Y12FA1D".
lia.
- pose proof (HCI iv Hiv). unfold AIMG_HI in *. Z.div_mod_to_equations. lia.
- pose proof (HLB b Hb) as HB. unfold ablk, AIMG_HI, KLS in HB, AF. Z.div_mod_to_equations. lia.
- rewrite shad_div in E. unfold ASHOFF in E.
assert (FA : F <= a' < F + 2048) by (Z.div_mod_to_equations; lia).
destruct Ha' as [Y|[(iv & Hiv & Y1 & Y2)|(c0 & A0 & n0 & Hin0 & Y1)]].
+ lia.
+ pose proof (HCI iv Hiv). pose proof (HCI0 iv Hiv). unfold AIMG_HI in *. lia.
+ destruct (HD _ Hin0) as [D|D]; cbn in D; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Section E2P.
Variable AI : AMallocIface.
Notation CI := (aci AI).
Variable fflag : alayout -> Z -> Z -> Z.
Variable rng_fs : alayout -> footprint -> Prop.
#[using="Type"] Theorem pE2_proof : pE2_stmt AI fflag rng_fs.
Proof.
unfold pE2_stmt.
intros L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc
x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x27 x28 x29 x30 x31
m st LB SPA lo F P tl msv dsz j0 j1 j2 k0 j16
AH LBH SP16 ESPA ST LOC LOS SPT TP FRA STG FRB F2048 FH FC FHD FFL SH MI RSTK RI RFS RF RSF SF5.
pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
remember (bv_unsigned sp) as SP eqn:ESP.
pose proof (spa_props5 SP SP16) as SPAP. cbv zeta in SPAP. rewrite <- ESPA in SPAP. destruct SPAP as (SPAB & SPA32 & SPA120).
pose proof (ablk_lin _ _ FH) as (FH1 & FH2 & FH3 & FH4). unfold AIMG_HI in FH1.
pose proof atop_range as ATR. unfold AHARNESS_STACK in LOS.
pose proof (AI_layout AI _ _ _ _ _ AH) as (LY1 & LY2 & LY3 & LY4 & _).
pose proof (AI_aci_img AI) as HCI. pose proof (AI_aci_lo AI) as HCI0.
pose proof (fse_rtall_of_aheap AI _ _ _ _ _ AH) as RT.
assert (LBH' : forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b)).
{ intros b Hb. destruct (LBH b Hb) as (p & A & n & ->). cbn [ab_addr ab_size].
exact (proj1 (proj1 (proj2 (AI_block AI _ _ _ _ _ _ _ _ AH (or_intror Hb))))). }
assert (NFB : ~ In (FB5 F) LB).
{ pose proof (AI_blocks_nodup AI _ _ _ _ _ AH) as NDx. inversion NDx as [|x l NI0 N3]. exact NI0. }
assert (FFD : forall b, In b LB -> F + 2048 <= ab_addr b \/ ab_addr b + ab_size b <= F).
{ intros b Hb. assert (NE : FB5 F <> b) by (intros E; apply NFB; rewrite E; exact Hb).
pose proof (AI_blocks_disjoint AI _ _ _ _ _ _ _ AH ltac:(left; reflexivity) ltac:(right; exact Hb) NE) as D. cbn in D. Local Ltac2 Set LiaHints.tbl := fun () => "02^0?10154571189.1741042729656.175 11208550637.1521162083372.175 11801586693.14211801586693.14311801586693.15711801586693.1581209982779.132 12284914512.1751237157135.176 12429415553.8  12472314755.17512613398580.17512853773960.17414606541112.17514694329296.17515863960074.17615926818576.15516060046482.15316726002134.12416734151816.17417776320428.17518182778552.17518654511215.15619753240244.17521077578749.14321077578749.15822039128201.17522149436869.15622434261001.17522700267513.14422700267513.15924375359911.8  24559885228.17525071629079.15625345195586.10825878270252.17526313690633.17526328424249.17426731493561.1742688544073.132 26966040451.17626994131331.1762701064303.117 27267521383.11127408782892.17527493063733.17427612163536.17527997378679.5  28360455555.17728381205643.15229170016436.17529540039409.14829771365531.5  29771365531.6  29784302302.14529784458140.14929786462698.10829788494300.11030898146691.17630988419926.13931621251547.14231621251547.15731706468408.17 32336445724.17132338238897.16932645539000.1753287162942.155 33057073190.15633178574393.17433453380665.17433890036524.17534588340948.16935257437862.13935499906471.12435499906471.13936115622444.17536348315445.1743674939405.139 36754810808.17536960603523.17637124083238.12437497880812.14237497880812.1573832670845.111 38933424184.17539148471614.17139556451084.3  39934894388.17540047495227.3  40091925677.17441267028642.17141427975703.156422633296.175  43987951407.17644484923210.14244484923210.157449739755.4    45061001169.17445304574395.17645387618999.17645436016781.15845500491675.15645638131920.17545815404950.13947876533641.17547888061840.14148461155024.17549123722493.14349123722493.15849610168957.14349610168957.15850187954697.17150993995517.14350993995517.15851218488760.17551370739587.17551429472211.15651678667181.17451687845099.13851875497613.14352022267192.17552084281981.14352084281981.15852151878409.17552541044300.15353440271625.17553636779446.15653767577772.17554762063931.13154933170051.17655648185224.1715601542737.174 56041590272.15057080291252.17557081557379.17557349728844.13957456858889.17557848745613.12458317609353.17558746296584.17458977817012.17559308742867.14559611243400.17461917199021.17462110569494.15362459950672.17562652249012.17562701717305.14862708006973.16962979470417.17463152402819.17563235321901.1746448600629.174 64548988925.14364548988925.15864950891024.12665363719379.17665598123907.17665635316141.13265647830155.11765964935632.17566811069213.15666964538243.17667305651485.1177439380175.145 7843915089.174 7987546237.143 7987546237.158 8191316637.116 8723057972.175 8739922.145    9571392558.8   00000100200300@00`00a01A01B01C01D01E01U01V01W01X01Y01Z01[01\01]01^01_01l01m02202302902?02@02J02K02R02Y02b02o03003103>03?03@03A03G03H03I03O03V03c03d03e03o04004C04D04E04O04P04Q04R04S04T04U04V04`04j05905:05;05<05=05O05P05Q05^05d05j05k05l06906:06@06A06B06H06_07607K07L07Q07U07V07Z07g08108208308@08N08\08e08f08g08h08i09609709809909:09;09A09G09M09S09]09c09i09j09k09l0:90::0:;0:<0:B0:H0:I0:J0:K0:P0:]0:^0:_0:`0:a0;=0;>0;?0;@0;A0;G0;H0;I0;J0;R0;S0;`0;a0;b0;c0<D0<e0<f0<g0=40=50=;0=A0=B0=C0=D0=I0=N0=O0=P0=Q0=R0=S0=T0=Z0=`0=a0=b0=k0>9FFSS3ESP3LOS3SPTS3FH24SHDJ3LOC3LOS3ATR4BSF24SPABSS3FH24SHDJ3LOC3LOS3ATR4BSF24SPABSSFSS3SPT6SPA1203LY3SFFFFFSSSFS3ESP3LOS3SPTFS3FH1FS4BSF1S4BSF1FS3FH24SHDJFS3FH21HS3FH21HS3LOC3LOSS3ESP3LOS3SPTSSS3ESP3LOS3SPTFFFS4BSF1SSS4BSF1S3FH21DS3ESP3LOS3SPTFFS3LOS4SPABSS5F20482FH1H2H03H14FSS3SPT4SPABFSSSSSSS3FH24SHDJS3FH24SHDJS5F20481H2H02H4SSFSS3LOC3LOS4SPAB3FH3FFS3ESP3LOS3SPTS4SPABS4BSF2SSS3ESP3LOS3SPTFS4BSF1FSS4BSF2S3LOC3LOS4SPAB3ATR4BSF2S3LOC3LOS4SPAB3ATR4BSF2S3LOS3SPT4SPAB6SPA120FS3LOSS2HrFS2HrS3ESP3LOS3SPTS3LOS4SPABSFS3ESP3LOS3SPTS3LOC3ATR4BSF2S3LOC3ATR4BSF2S3SPT3LY3FFFFS3LOC3LOS3FH3FSFSFS4BSF1S4BSF1S4BSF1S4BSF1S3LOS4SPABS4BSF1S4BSF1FSSS3ESP3LOS3SPTSFFS4BSF1S4BSF1FSFS3FH4S3ESP3LOS3SPTSSSFS5F20483FH13FH33ATR1H2H03H14FSSFS4BSF1FFFS3FH12B0FS3ESP3LOS3SPTSFFS3LOC3LOS3SPT4SPAB6SPA1203ATR3LY3S3LOC3LOS3SPT4SPAB6SPA1203ATR3LY3FSS3ESP3LOS3SPTFS4BSF1S4BSF1SFSS3FH1S3FH1FSSSSFS4BSF1S4BSF1SFS3FH13FH4S3SPT4SPAB3LY3".
lia. }
replace (shad F) with (Z.shiftr F 3 + ASHOFF) in RSF by (unfold shad; lia).
assert (BSF : 2147450880 <= Z.shiftr F 3 + ASHOFF /\ Z.shiftr F 3 + ASHOFF + 256 <= 17594333495296)
by (rewrite Z.shiftr_div_pow2 by lia; unfold ASHOFF; Z.div_mod_to_equations; lia).
destruct BSF as [BSF1 BSF2].
assert (SHDJ : F + 2048 <= Z.shiftr F 3 + ASHOFF \/ Z.shiftr F 3 + ASHOFF + 256 <= F).
{ rewrite Z.shiftr_div_pow2 by lia. unfold ASHOFF. unfold ablk, AIMG_HI, KLS in FH. Z.div_mod_to_equations. lia. }
assert (RFRA : rng RNG SPA 120) by (eapply rng_sub'; [exact RSTK| lia]).
lazymatch goal with |- evtF _ _ ?Q _ => set (QQ := Q) end.
unfold FRA_E, SHF, FSH, ASHOFF in FRA, SH, RSF, BSF1, BSF2, SHDJ. unfold SHF, ASHOFF.
pose proof (munch_refl [(Z.shiftr F 3 + 2147450880, Z.shiftr F 3 + 2147450880 + 256); (F, F + 8)] m) as MU.
pose proof (wmono_refl bsegs m) as WM.
zstep. zstep.
zstep.
lazymatch goal with SHx : rw_cells bsegs _ (Z.shiftr F 3 + 2147450880) _ |- _ => rw_split SHx 13%nat SHa SHr end.
rw_split SHr 1%nat SHb SHc.
pose proof (fse_rt_munch _ _ _ RT MU WM ltac:(cbn [above]; unfold AIMG_HI; repeat split; lia)) as RTN.
unfold fse_rt in RTN. destruct RTN as (RT1 & RT2 & RT3 & RT4 & RT5 & RT6 & RT7).
call (ss_f8_z RNG); [ first [ exact SHb | eassumption | lia | eapply rng_sub'; [exact RSF| lia] ] .. | ].
change (Z.to_nat 64) with 64%nat in POST. rw_join SHa POST SH1. rw_join SH1 SHc SH2. cbn [app] in SH2.
clear RT1 RT2 RT3 RT4 RT5 RT6 RT7.
zstep. zstep.
zstep.
rw_split SH2 4%nat SHa' SHr'.
rw_split SHr' 1%nat SHb' SHc'.
pose proof (fse_rt_munch _ _ _ RT MU WM ltac:(cbn [above]; unfold AIMG_HI; repeat split; lia)) as RTN.
unfold fse_rt in RTN. destruct RTN as (RT1 & RT2 & RT3 & RT4 & RT5 & RT6 & RT7).
call (ss_f8_z RNG); [ first [ exact SHb' | eassumption | lia | eapply rng_sub'; [exact RSF| lia] ] .. | ].
change (Z.to_nat 64) with 64%nat in POST. rw_join SHa' POST SH3. rw_join SH3 SHc' SH4. cbn [app] in SH4.
clear RT1 RT2 RT3 RT4 RT5 RT6 RT7.
zstep. zstep.
zstep.
zstep.
zstep.
zstep. if_cases B0; zify_cond B0; [exfalso; lia|].
zstep.
zstep.
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m0 end.
assert (AH0 : AHEAP AI L RNG st (FB5 F :: LB) m0).
{ eapply (AI_frame AI); [exact AH| exact MU| exact WM|].
constructor; [cbn; right; right; right; right; exists 5, F, 2048; split; [left; reflexivity|]|].
{ unfold ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. clear - F2048 FH1. Z.div_mod_to_equations. lia. }
constructor; [cbn; right; left; exists (FB5 F); split; [left; reflexivity| cbn; lia]| constructor]. }
assert (AP0 : aheap_pres CI LB SP m m0).
{ eapply aheap_pres_of_munch; [exact MU| exact WM|]. intros a Ha. cbn [outside].
split; [intros Hr; refine (shadow_not_client2048 CI LB SP F a HCI HCI0 FH F2048 ltac:(clear - SPAB LOS LOC ATR; lia) LBH' FFD _ Ha);
rewrite shad_div; unfold ASHOFF; rewrite Z.shiftr_div_pow2 in Hr by lia; change (2^3) with 8 in Hr; clear - Hr; lia|].
split; [intros Hr; exact (app_not_clientE CI LB SP F 2048 a HCI HCI0 FH ltac:(clear - SPAB LOS LOC ATR; lia) LBH' FFD ltac:(clear - Hr; lia) Ha)| exact I]. }
assert (SH5 : rw_cells bsegs m0 (shad F) [CB 256 (cells_bytes (FSH F8S F8S F8S BF8 BF8))]).
{ apply (fsh_forget m0 F (FSH F8S F8S F8S BF8 BF8)); [unfold SHF, FSH, ASHOFF; exact SH4| reflexivity]. }
eapply evtF_cut.
{ eapply (SF5 L RNG) with (LB := LB) (F := F) (lo := lo);
first [ exact AH0 | exact FFL | exact SH5 | exact F2048 | exact FH | exact FC | exact MI | exact LOC | exact RSTK | exact RI | exact RFS
| exact RF | (replace (shad F) with (Z.shiftr F 3 + 2147450880) by (unfold shad, ASHOFF; lia); exact RSF)
| reflexivity
| (rewrite unsigned_lit by lia; exact ST)
| (rewrite unsigned_lit by lia; unfold SF5_STACK; clear - LOS SPAB; lia)
| (rewrite unsigned_lit by lia; clear - SPT SPAB; lia) ]. }
cbv beta. intros ms' PO.
destruct PO as (u0 & u1 & u2 & e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & u3 & u4 & u5 & u6 & m1 & -> & MI1 & ST1 & AP1 & AH1 & SHF1).
rewrite unsigned_lit in ST1, AP1 by lia.
replace (ret_pc (Z_to_bv 64 0x812a0)) with (Z_to_bv 64 0x812a0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
assert (FRB1 : rw_cells bsegs m1 (SP + -104) (FZRB13 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)).
{ eapply aheap_pres_rw_cells; [exact AP1| exact FRB|]. rewrite FZRB13_size. left; left. cbn. clear - SPAB SPA120 SPT RSP LY3. lia. }
assert (FRA1 : rw_cells bsegs m1 SPA
[CB 24 k0; C8 (Z_to_bv 64 (Z.shiftr F 3 + 2147450880 + 76)); C8 (Z_to_bv 64 (Z.shiftr F 3 + 2147450880 + 4));
C8 (Z_to_bv 64 F); C8 (Z_to_bv 64 (F + 1760)); C8 (Z_to_bv 64 dsz); C8 (Z_to_bv 64 (Z.shiftr F 3 + 2147450880 + 148));
C8 (Z_to_bv 64 tl); C8 (Z_to_bv 64 F); C8 (Z_to_bv 64 msv); CB 16 j16; C8 (Z_to_bv 64 F)]).
{ eapply aheap_pres_rw_cells; [exact AP1| exact FRA|]. left; left. cbn. clear - SPAB SPA120 SPT RSP LY3. lia. }
assert (STG1 : stk bsegs m1 (SPA + 120) (SP + -104)) by (eapply aheap_pres_stk; [exact AP1| exact STG| lia| clear - SPT LY3; lia]).
clear FRB FRA STG. unfold FZRB13 in FRB1. rewrite ESP in FRB1.
zstep.
zstep.
zstep.
do 13 zstep.
zstep.
zstep.
apply evtF_done. unfold QQ, pE2_post.
do 15 eexists. split; [reflexivity|].
split; [exact MI1|].
split.
{ rewrite <- ESP.
pose proof (stk_of_rw_cells bsegs m1 _ _ FRA1) as SA. cbn [cells_size csize Nat.add] in SA. change (Z.of_nat 120) with 120 in SA.
pose proof (stk_of_rw_cells bsegs m1 _ _ FRB1) as SB. cbn [cells_size csize Nat.add] in SB. change (Z.of_nat 104) with 104 in SB.
rewrite <- ESP in SB. replace (SP + -104 + 104) with SP in SB by lia.
apply (stk_merge bsegs m1 lo (SP + -104) SP); [| exact SB| lia].
apply (stk_merge bsegs m1 lo (SPA + 120) (SP + -104)); [| exact STG1| lia].
apply (stk_merge bsegs m1 lo SPA (SPA + 120)); [exact ST1| exact SA| destruct ST1 as [? _]; lia]. }
split.
{ rewrite <- ESP. eapply aheap_pres_trans; [exact AP0|]. eapply aheap_pres_weaken; [exact AP1| lia| intros b Hb; exact Hb]. }
exact AH1.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End E2P.
End CANSEC1.
