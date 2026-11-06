(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Arr Bytes ZBridge Tac InitMem.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import ExecF Shadow.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import AImg ABase RtCells ABytes AProto AMalloc_iface AProg_kit AHarness_iface
AFake5_iface AKit FsKit AH_fse_kit AH_fse_calls AH_fse_Eiface.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import ShadowTac.
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
x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x25 x26 x28 x29 x30 x31
m st LB SPA lo F P tl B j0 j1 j2 j16
AH LBH SP16 ESPA ST LOC LOS SPT TP FRA STG FRB F2048 FH FC FHD FFL SH MI RSTK RI RFS RF RSF SF5.
pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
remember (bv_unsigned sp) as SP eqn:ESP.
pose proof (spa_props5 SP SP16) as SPAP. cbv zeta in SPAP. rewrite <- ESPA in SPAP. destruct SPAP as (SPAB & SPA32 & SPA88).
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
pose proof (AI_blocks_disjoint AI _ _ _ _ _ _ _ AH ltac:(left; reflexivity) ltac:(right; exact Hb) NE) as D. cbn in D. Local Ltac2 Set LiaHints.tbl := fun () => "02^0?10028172029.14010028172029.15510154571189.1711042729656.172 11208550637.14911386766649.1241162083372.172 11801586693.13911801586693.14011801586693.15411801586693.15511975744272.1381209982779.129 1237157135.173 12429415553.8  12472314755.17212613398580.17212853773960.17114606541112.17215863960074.17315995863202.1681601252817.171 16726002134.12116734151816.17116814119318.15017776320428.17218182778552.17218654511215.14818995844176.17219753240244.17221895416531.17322026868477.14022026868477.1552203518672.172 22039128201.17222149436869.14822434261001.17222700267513.14122700267513.15623176426704.1722327531472.172 24205896189.14024205896189.15524375359911.8  24559885228.17225071629079.14825345195586.10525707527504.17225878270252.17226313690633.17226328424249.17126731493561.1712688544073.129 26966040451.17326994131331.1732701064303.114 27267521383.10827292214550.13627408782892.17227493063733.17127843455921.16627997378679.5  28360455555.17428381205643.14929170016436.17229540039409.14529771365531.5  29771365531.6  29784302302.14229784458140.14629786462698.10529788494300.10730857076817.17130898146691.17330988419926.13631571129736.16831621251547.13931621251547.15431706468408.17 32336445724.16832645539000.1723287162929.147 33057073190.14833178574393.1713331467785.168 33453380665.17133890036524.17234588340948.16635257437862.13635499906471.12135499906471.13635895327997.14035895327997.15536093405102.12336115622444.17236348315445.1713674939405.136 36754810808.17236960603523.17337124083238.12137497880812.13937497880812.15437569775952.17237693789777.1713851966096.152 38525121917.14038525121917.15538933424184.17239148471614.16839556451084.3  39934894388.17239954811344.17240047495227.3  40091925677.17140680074192.17241427975703.14843987951407.17344484923210.13944484923210.154449739755.4    45304574395.17345387618999.17345436016781.15545500491675.14847876533641.17251218488760.17251278759761.17151370739587.17251429472211.14851678667181.17151687845099.13551875497613.14052022267192.17252151878409.17252541044300.15053440271625.17253636779446.14853767577772.17254762063931.12854933170051.17356041590272.14757080291252.17257081557379.17257349728844.13657456858889.17257848745613.12158317609353.17258746296584.17158977817012.17259308742867.14259611243400.17161917199021.17162652249012.17262701717305.14562708006973.16663152402819.17263235321901.17163478620285.14063478620285.1556448600629.171 65598123907.17365635316141.12965647830155.11466811069213.14866964538243.17367305027709.10867305651485.1147381600893.140 7381600893.155 7439380175.142 8191316637.113 8723057972.172 8739922.142    9571392558.8   00000600<00=00>00?00@00M00m00n01N01O01P01Q01R01a01b01c01d01e01f02002102202302402A02B02G02H02I02J02P02V02W02X02b02c02j03103203303903?03H03U03V03W03X03e03f03g03h03n03o04004604=04>04K04L04M04W04X04k04l04m05705805905:05;05<05=05>05?05@05J05T05c05d05e05f06806906C06D06Q06W06]06^06_06e06k06l07907:07@07A07B07H07_08608708808908?08E08F08K08O08P08Q08U08b08c08d09109?09M09V09W09X09Y09f09g09h09i09j09k0:80:90::0:;0:<0:=0:>0:C0:P0:Q0:R0:n0:o0;00;10;20;80;90;:0;;0;C0;D0;Q0;R0<20<R0<S0<`0<f0<l0<m0<n0=30=80=90=:0=N0=O0=U0=[0=\0=]0=^0=g0>5S4BSF1S4BSF1FFSSS3ESP3LOS3SPTS3FH24SHDJ3LOC3LOS3ATR4BSF24SPABSS3FH24SHDJ3LOC3LOS3ATR4BSF24SPABSSSSS3SPT5SPA883LY3SFFFFS3LOS4SPABFSFSS3ESP3LOS3SPTFS3FH1FFFS4BSF1S4BSF1FFS3FH24SHDJFS3FH21HS3FH21HFFS4BSF1S4BSF1S3LOC3LOSS3ESP3LOS3SPTSSFS3ESP3LOS3SPTFFFS4BSF1SSS4BSF1S3FH21DSS3ESP3LOS3SPTFSS3LOS4SPABSS5F20482FH1H2H03H14FSS3SPT4SPABFSSSSFSSSS3FH24SHDJS3FH24SHDJS5F20481H2H02H4SFSS3LOC3LOS4SPAB3FH3FS3LOS4SPABFS3ESP3LOS3SPTS4SPABS4BSF2SSS4BSF1S4BSF1SS3ESP3LOS3SPTFS4BSF1FSS4BSF2S3LOC3LOS4SPAB3ATR4BSF2S3LOC3LOS4SPAB3ATR4BSF2FFSS4BSF1S4BSF1FS3LOSS2HrFFS2HrS3ESP3LOS3SPTFSS3ESP3LOS3SPTS3LOC3ATR4BSF2S3LOC3ATR4BSF2S3SPT3LY3FFFS3LOC3LOS3FH3FFFSSS3ESP3LOS3SPTSFFFSFS3FH4S3ESP3LOS3SPTSSS5F20483FH13FH33ATR1H2H03H14FSSFS4BSF1FFFS3FH12B0FS3ESP3LOS3SPTFS3LOC3LOS3SPT4SPAB5SPA883ATR3LY3S3LOC3LOS3SPT4SPAB5SPA883ATR3LY3SS3ESP3LOS3SPTS4BSF1S4BSF1FSS3FH1S3FH1SSS3LOS3SPT4SPAB5SPA88SS4BSF1S4BSF1SSFS3FH13FH4S3SPT4SPAB3LY3".
lia. }
replace (shad F) with (Z.shiftr F 3 + ASHOFF) in RSF by (unfold shad; lia).
assert (BSF : 2147450880 <= Z.shiftr F 3 + ASHOFF /\ Z.shiftr F 3 + ASHOFF + 256 <= 17594333495296)
by (rewrite Z.shiftr_div_pow2 by lia; unfold ASHOFF; Z.div_mod_to_equations; lia).
destruct BSF as [BSF1 BSF2].
assert (SHDJ : F + 2048 <= Z.shiftr F 3 + ASHOFF \/ Z.shiftr F 3 + ASHOFF + 256 <= F).
{ rewrite Z.shiftr_div_pow2 by lia. unfold ASHOFF. unfold ablk, AIMG_HI, KLS in FH. Z.div_mod_to_equations. lia. }
assert (RFRA : rng RNG SPA 88) by (eapply rng_sub'; [exact RSTK| lia]).
lazymatch goal with |- evtF _ _ ?Q _ => set (QQ := Q) end.
unfold FRA_E, SHF, FSH, ASHOFF in FRA, SH, RSF, BSF1, BSF2, SHDJ. unfold SHF, ASHOFF.
pose proof (munch_refl [(Z.shiftr F 3 + 2147450880, Z.shiftr F 3 + 2147450880 + 256); (F, F + 8)] m) as MU.
pose proof (wmono_refl asegs m) as WM.
zstep. zstep.
zstep.
lazymatch goal with SHx : rw_cells asegs _ (Z.shiftr F 3 + 2147450880) _ |- _ => rw_split SHx 13%nat SHa SHr end.
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
assert (SH5 : rw_cells asegs m0 (shad F) [CB 256 (cells_bytes (FSH F8S F8S F8S BF8 BF8))]).
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
replace (ret_pc (Z_to_bv 64 0x81330)) with (Z_to_bv 64 0x81330) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
assert (FRB1 : rw_cells asegs m1 (SP + -104) (FZRB13 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)).
{ eapply aheap_pres_rw_cells; [exact AP1| exact FRB|]. rewrite FZRB13_size. left; left. cbn. clear - SPAB SPA88 SPT RSP LY3. lia. }
assert (FRA1 : rw_cells asegs m1 SPA
[C8 (Z_to_bv 64 (Z.shiftr F 3 + 2147450880 + 76)); C8 (Z_to_bv 64 (Z.shiftr F 3 + 2147450880 + 4)); C8 (Z_to_bv 64 F);
C8 (Z_to_bv 64 (Z.shiftr F 3 + 2147450880 + 148)); C8 (Z_to_bv 64 (F + 1760)); C8 (Z_to_bv 64 tl); C8 (Z_to_bv 64 F);
C8 (Z_to_bv 64 B); CB 16 j16; C8 (Z_to_bv 64 F)]).
{ eapply aheap_pres_rw_cells; [exact AP1| exact FRA|]. left; left. cbn. clear - SPAB SPA88 SPT RSP LY3. lia. }
assert (STG1 : stk asegs m1 (SPA + 88) (SP + -104)) by (eapply aheap_pres_stk; [exact AP1| exact STG| lia| clear - SPT LY3; lia]).
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
pose proof (stk_of_rw_cells asegs m1 _ _ FRA1) as SA. cbn [cells_size csize Nat.add] in SA. change (Z.of_nat 88) with 88 in SA.
pose proof (stk_of_rw_cells asegs m1 _ _ FRB1) as SB. cbn [cells_size csize Nat.add] in SB. change (Z.of_nat 104) with 104 in SB.
rewrite <- ESP in SB. replace (SP + -104 + 104) with SP in SB by lia.
apply (stk_merge asegs m1 lo (SP + -104) SP); [| exact SB| lia].
apply (stk_merge asegs m1 lo (SPA + 88) (SP + -104)); [| exact STG1| lia].
apply (stk_merge asegs m1 lo SPA (SPA + 88)); [exact ST1| exact SA| destruct ST1 as [? _]; lia]. }
split.
{ rewrite <- ESP. eapply aheap_pres_trans; [exact AP0|]. eapply aheap_pres_weaken; [exact AP1| lia| intros b Hb; exact Hb]. }
exact AH1.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End E2P.
End CANSEC1.
