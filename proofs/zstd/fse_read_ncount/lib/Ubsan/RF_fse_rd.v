(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Spec Require Import FseNCount FseLemmas FseAbs FseReaderRT FseReadSound.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Common Require Import FseWalkKit FseRdKit FseRdKit2.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import UImg RF_fse_iface RF_fse_rd_base RF_fse_rd_mem RF_fse_rd_body.
Import ListNotations.
Open Scope Z_scope.
Section Top.
Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : fmem).
Variables (SPV NC MSVP TLP BUF : Z) (rt0 rt buf : list Z) (msv0 msv tl n lo : Z) (tl0 : word).
Hypothesis ARR : u8arr usegs m NC (u16s (map (Z_to_bv 64) rt0)).
Hypothesis HMSV : rw_cells usegs m MSVP [C4 (Z_to_bv 64 msv0)].
Hypothesis HTL : rw_cells usegs m TLP [C4 tl0].
Hypothesis HBUF : bytes_at usegs m BUF (map (Z_to_bv 8) buf).
Hypothesis FBY : Forall (fun c => 0 <= c < 256) buf.
Hypothesis RN : read_ncount rt0 msv0 buf = Ok (rt, msv, tl, n).
Hypothesis HM0 : 0 <= msv0 <= 255.
Hypothesis HLEN : zlen buf <= 65536.
Hypothesis HNP : 0 < NC.
Hypothesis HNA : NC mod 2 = 0.
Hypothesis HVP : 0 < MSVP.
Hypothesis HVA : MSVP mod 4 = 0.
Hypothesis HTP : 0 < TLP.
Hypothesis HTA : TLP mod 4 = 0.
Hypothesis HBP : 0 < BUF.
Hypothesis HSLACK : BUF + zlen buf + 8 <= 2^64.
Hypothesis ST : stk usegs m lo SPV.
Hypothesis LO : lo <= SPV - FSE_READ_STACK.
Hypothesis RSP : 0 <= SPV < 2^64.
Hypothesis SNS : NC + 2 * zlen rt0 <= lo \/ SPV <= NC.
Hypothesis SMS : MSVP + 4 <= lo \/ SPV <= MSVP.
Hypothesis STS : TLP + 4 <= lo \/ SPV <= TLP.
Hypothesis SBS : BUF + zlen buf <= lo \/ SPV <= BUF.
Hypothesis SNM : NC + 2 * zlen rt0 <= MSVP \/ MSVP + 4 <= NC.
Hypothesis SNT : NC + 2 * zlen rt0 <= TLP \/ TLP + 4 <= NC.
Hypothesis SNB : NC + 2 * zlen rt0 <= BUF \/ BUF + zlen buf <= NC.
Hypothesis SMT : MSVP + 4 <= TLP \/ TLP + 4 <= MSVP.
Hypothesis SMB : MSVP + 4 <= BUF \/ BUF + zlen buf <= MSVP.
Hypothesis STB : TLP + 4 <= BUF \/ BUF + zlen buf <= TLP.
Hypothesis MI : mem_inv usegs m.
Notation POST := (fse_read_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV NC MSVP TLP rt0 rt msv tl n lo m).
#[using="m SPV buf msv0 tl0 ARR HMSV HTL ST RSP"] Lemma bounds : 0 <= lo /\ (0 <= NC /\ NC + 2 * zlen rt0 <= 2^64) /\ (0 <= MSVP /\ MSVP + 4 <= 2^64) /\ (0 <= TLP /\ TLP + 4 <= 2^64).
Proof.
clear HNP HNA HVP HVA HTP HTA. destruct ST as (L0 & _). pose proof (u8arr_bound _ _ _ _ ARR) as B1. rewrite u16s_length, length_map in B1.
pose proof (rw_cells_bound _ _ _ _ HMSV) as B2. pose proof (rw_cells_bound _ _ _ _ HTL) as B3.
cbn [cells_size csize Nat.add] in B2, B3. repeat split; lia.
Qed.
#[using="msv0 tl0 ARR HMSV HTL HBUF FBY RN HM0 HLEN HNP HNA HVP HVA HTP HTA HBP HSLACK ST LO RSP SNS SMS STS SBS SNM SNT SNB SMT SMB STB MI"] Lemma rd_top8 : forall (t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 : word), 8 <= zlen buf ->
evt usegs POST
(MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 NC) (Z_to_bv 64 MSVP) (Z_to_bv 64 TLP) (Z_to_bv 64 BUF)
(Z_to_bv 64 (zlen buf)) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x13f40) fc None m (seg_rom usegs)).
Proof.
intros t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 H8.
destruct bounds as (L0 & BN & BM & BT).
pose proof RN as RN'. unfold read_ncount in RN'. unfold FseNCount.Zlength in RN'.
Local Ltac2 Set LiaHints.tbl := fun () => "00>0>10332462254.7410702180509.7411506872626.7415030856605.7415417666041.7418195709261.7422229545543.7439828196908.9743072656093.7445009000051.7445973040787.7454943314720.7255131041601.7466352651635.7400000500900=00A00E00J00O00P00U00Y00^00b00f00jS3RSPS2BTS2BNS2BMS2BNS3RSPS3HM0SS3HBPS2BTS3HM0S2H8S2LOS2BM".
replace (zlen buf <? 8) with false in RN' by (symmetry; apply Z.ltb_ge; lia).
destruct (read_body8_inv buf (msv0 + 1) rt0 rt msv tl n H8 RN') as (HL & _).
set (C := mkRD ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV NC MSVP TLP BUF lo rt0 buf msv0).
assert (OK : rd_ok C).
{ unfold rd_ok, RD_STACK, FSE_READ_STACK in *. cbn. repeat split; try assumption; try lia. }
eapply evt_mono.
- exact (rd_body8 C OK rt msv tl n tl0 t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 ARR HMSV HTL HBUF ST MI RN').
- intros ms' (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & m' & -> & MU & WM & MI' & ST' & A' & M' & T').
unfold fse_read_post. do 14 eexists. exists m'. split; [reflexivity|].
split. { eapply munch_weaken; [| exact MU]. unfold sub_fp, rd_W, RD_STACK, FSE_READ_STACK. subst C. cbn [outside c_NC c_rt0 c_MSVP c_TLP c_SP]. intros x; lia. }
split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact A'|]. split; [exact M'| exact T'].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="SPV rt0 buf RSP"] Lemma pad_tail : forall (z : byte) k, (k <= 8)%nat -> firstn (8 - k) (skipn k (repeat z 8)) = repeat z (8 - k).
Proof. intros z k Hk. do 9 (destruct k as [|k]; [reflexivity|]). Local Ltac2 Set LiaHints.tbl := fun () => "0010=6267230792.59000004S2Hk".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="msv0 tl0 ARR HMSV HTL HBUF FBY RN HM0 HLEN HNP HNA HVP HVA HTP HTA HBP HSLACK ST LO RSP SNS SMS STS SBS SNM SNT SNB SMT SMB STB MI"] Lemma rd_top_small : forall (t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 : word), zlen buf < 8 ->
evt usegs POST
(MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 NC) (Z_to_bv 64 MSVP) (Z_to_bv 64 TLP) (Z_to_bv 64 BUF)
(Z_to_bv 64 (zlen buf)) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x13f40) fc None m (seg_rom usegs)).
Proof.
intros t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 H8.
destruct bounds as (L0 & BN & BM & BT). unfold FSE_READ_STACK in *.
set (hb := zlen buf) in *. set (hbn := Z.to_nat hb).
set (buf' := buf ++ repeat 0 (Z.to_nat (8 - hb))).
assert (RB : read_ncount_body8 buf' (msv0 + 1) rt0 = Ok (rt, msv, tl, n) /\ n <= hb).
{ pose proof RN as RN'. unfold read_ncount in RN'. unfold FseNCount.Zlength in RN'. fold hb in RN'.
Local Ltac2 Set LiaHints.tbl := fun () => "03F0?103121726.106  10697708320.10410788034027.94 11046723646.93 11250791322.93 11494734482.92 11502400143.10411801586693.10711911295481.75 11969479934.93 12092314691.86 12647985899.12412748323370.12413061480274.93 13296895234.10413691071486.94 13999703166.93 14344564414.94 14724365828.12414725128542.82 15026939936.10415413193284.10417276395546.91 17319758254.1241773345681.129 1773345681.93  18434612386.92 18765052798.93 19630014259.10519786216602.93 20185404305.12920185404305.93 20388703870.93 21035712747.92 21150061547.91 21155567546.93 22163107130.94 22225596922.10422236621513.88 23027219972.12423287207578.93 23472906238.94 23897384501.10424441599211.93 24630998586.94 2506353810.92  25149005242.10625175044703.12425322204670.93 25711131602.94 25784352991.12425797024026.94 25822493694.94 25993133822.94 27497206270.91 28251215826.94 2865410014.104 29113359249.12829113359249.92 29302996030.88 29314792218.94 29488343488.10429590301777.12429971687518.12230035914494.94 30196181434.93 30272193814.10330655960555.93 31063185198.88 31105295486.93 31822630810.92 32072199403.93 32096482495.86 32103139463.88 32110716939.13132308657022.93 32382978064.12432566737944.10432651489978.93 32961963797.12233680001082.93 35327814042.93 35329728766.93 35723905681.13035723905681.94 35932178577.13035932178577.94 3748619754.104 37639535022.12437833440282.93 38503264702.94 38546453137.12938546453137.93 39190280004.10439223778541.92 39879683282.94 40437312978.93 41355402778.94 42528871806.93 42668201294.92 42726882866.12542764144210.93 42831019478.92 42964102526.93 43260551312.12443533417086.92 43863237274.93 44054420798.92 44174344683.94 44703552536.10444956307390.94 45012915662.10445221239098.94 45976956206.10446232973498.93 4682375403.93  47986254827.94 48394734674.93 48424436030.93 48486210139.88 48635769742.92 48788007787.12449006049551.10749468260241.12849468260241.93 49627019518.94 49860545874.93 49874048794.93 5016951787.94  50996573150.10451077962366.93 51088222973.10451177352322.12451261860670.93 51755794159.75 52131238270.93 5228128005.124 52293967358.91 52355136491.93 5260944683.121 52715537106.94 53766521426.93 54256680510.93 54261855034.91 54660907814.10754995113214.94 55331181010.91 55739861310.106563227834.93   5635726270.93  56364959130.10656813015230.93 57295673474.88 57739970690.10457745675194.92 57870213981.12558365643359.1245837044369.128 5837044369.91  59142600593.12959142600593.93 59314923118.86 59571612817.12959571612817.94 59847147663.10759884931217.12959884931217.93 59893051076.74 60087157525.10461172417726.91 61312968927.12461715584172.12161754264120.10661805773357.12261896502994.93 61910460954.94 61937685140.13061937685147.13162175718784.86 62321201534.93 62552440721.12962552440721.93 62900777713.10862907701586.92 63102335211.93 63411832446.92 63692253251.12163698612035.77 63905363476.12063943927429.88 63946022152.10464736957589.12565200320487.1046537483326.93  65805175866.94 66348211918.10466443715217.13066443715217.94 66619354511.92 66648899177.1076701218494.94  6757042411.93  67758960638.94 67942580008.91 67942580008.92 67942580008.93 67942580008.94 8280057722.84  8288550881.104 8564251134.93  8583720762.93  926450572.121  9805529181.125 9891784626.124 00000>00F00K00W00[00c00k00l01001801?01K01X01d01i02102902E02N02V02^02f02j03703<03A03M03U03]03a03f03k04304804=04B04G04P04U04^04b04j04o05405905A05O05]05e06106=06A06I06Q06Y06e07107607;07@07D07P07Q07Y07a07f07k08008<08D08H08M08[08e09309;09@09I09N09W09\09`09h09m0:20:70:<0:@0:M0:Q0:]0:b0:g0;00;50;A0;M0;Q0;Y0;]0;d0<00<50<=0<B0<J0<N0<Z0<_0<h0=40=<0=A0=J0=O0=T0=Y0=e0>10>?0>K0>Y0>a0>f0>k0?30??0?C0?H0?T0?\0?g0@00@<0@?0@G0@W0@_0@d0@i0A50AA0AM0AR0Ad0Al0B80BF0BK0BW0B\0Bh0Bo0C40C90C@0CN0CS0CX0C]0Cb0Cl0D10D60D70D<0DA0DE0DJ0DV0Db0Dj0E10E60EB0EF0ET0Eb0Ei0F10F60F;0FD0FP0FU0F]0Ff0Fk0G00G90GB0GI0GR0G^0Gc0Gk0H00H50H:0H?0HK0HP0HX0H]0Hb0Hg0Hl0I10I90IA0IF0IR0IY0IZS2LO3SMS3LWS1KS2BT3LWSS3LWSS2LO3SNS3LWSS2HBS2LO3STSS2BN3LWSFS2H8S2LO3STSS3LWS1KS2LO3SNS3LWSS3SNB3LWS3LBSS2LO3SBS3LWSS3LWSS2LO3SMSS2LO3STSS2LO3SNS3LWSS3STS3LWSS2LO3LWSS2BM3LWSS2BN3LWSS2HBS3STB3LWS3LBSS3LWSS3LWSS2LO3SNS3LWSS2LO3STSS2H83LWSS2HBS3LWSS3LWSS2LO3STSS3LWSS3LWSS3RSPS3RSPS3HM03LWSS3LWSS3SMS3LWSS2HBS2LO3SMSS3LWSS3LWSS3RSPS2LO3SMSS2LO3SNS3LWS1KS2LO3STS3LWS1KS2LO3STSS2LO3SBS3LWSS2LO3SMS3LWSS2HBS2LO3STSS2LO3SMSS2LO3STSS2LO3SBS3LWSS2LO3SMS3LWSS3LWSS3LWSS3LWSS2HBS2LO3SNS3LWSFS3LWS2N2S2LO3STSS3RSPS3LWSS3LWSS6HSLACK3LWSS2LO3SMSS2HBS3LWSS4HLEN3LWS3LBSS4HLEN3LWSS4HLEN3LWS3LBSS2LO3SMSS3LWSS3SMS3LWSS3RSPS3NLE3LWSS3RSPS2HBS2LO3SMSS3LWSS3LWSS3LWSS3LWSS2HcS3SMB3LWS3LBSS2HBS2LO3SNS3LWSS3LWSS3LWSS3SNS3LWSS3LWSS2LO3SBS3LWSS2LO3SBS3LWSS2HBS2LO3STSS2HBS3LWS1HS2LO3SBS3LWSS3RSPS2LO3SMSS3LWSS2LO3STSS2HBS2LO3SNS3LWSS3LWSS3STS3LWSS2LO3SNS3LWSS2BT3LWSS3RSPS3HM03LWSS3RSPS3LWSS3LWSS2LO3SBS3LWSS2LO3SNS3LWSS2LO3SBS3LWS1KS2LO3SBS3LWSS2LO3SNS3LWS1KS2H83LWSS3LWSS3LWSS2LO3STSS2LO3SBS3LWSS2HBS3LWSS2LO3STS3LWSS2LO3SMSS2LO2L03LWSS3SNS3LWSS2LO3SNS3LWSS1HS2LO3STSS2LO3SBS3LWS3LBSS2LO3SMSS3LWSS3LWSS2LO3SBS3LWSS2LO3SBS3LWSS2LO3SNS3LWSS3RSPS2LO3SBS3LWS3LBS1KS2LO3SMSS2LO3SBS3LWSS2LO3STS3LWS1KS3RSPS2LO3SNS3LWSS3LWSS2LO3SNS3LWSS3LWS1KS3LWSS3RSPS3LWS1HS2LO3SMS3LWS1KS3LWSS3LWSS3LWSS3LWSS2H83LWS1KS3LWSS3LWSFS3LWSS3LWSS2H8S3LWSS2LO3SNS3LWSS2LO3STS3LWSS2LO3LWSS3LWS1KS3LWSS2LO3SBS3LWSS2HBS3NLE3LWS1K2N1S3NLE3LWS1K2N1S3LWS1KS2LO3SMSS3LWSS3LWSS3LWS1K1HS2LO3SBS3LWSS3LWSS2LO3SMSS3LB'3LWSS3LB'S3LWSS3RSP3LWSS3RSP3LWSS3LWS1HS3RSP3LWSS2LO3SNS3LWSS3RSPS2BM3LWSS3LWSS3LWSS3LWSS3LWSS2LO3SNS3LWSS3LWSS2LO3STSS3LWSS3LWSS3LWSS3LWSS3LWSS2LO3LWSS2LO3SMSS3RSPS3HM02HL3LWSS3LWS1HF".
replace (hb <? 8) with true in RN' by (symmetry; apply Z.ltb_lt; lia). fold buf' in RN'.
destruct (read_ncount_body8 buf' (msv0 + 1) rt0) as [[[[nc1 msv1'] tl1] cs]| | |]; cbn [bind] in RN'; try discriminate RN'.
destruct (Z.ltb_spec hb cs); [discriminate RN'|]. injection RN' as <- <- <- <-. split; [reflexivity| lia]. }
destruct RB as [RB NLE].
assert (LB' : zlen buf' = 8) by (subst buf' hb; rewrite length_app, repeat_length; lia).
destruct (read_body8_inv buf' (msv0 + 1) rt0 rt msv tl n ltac:(lia) RB) as (HL & _).
pose proof (munch_refl [(NC, NC + 2 * zlen rt0); (MSVP, MSVP + 4); (TLP, TLP + 4); (SPV - 256, SPV)] m) as MU.
pose proof (wmono_refl usegs m) as WM.
assert (LWS : length (map (Z_to_bv 64) rt0) = length rt0) by apply length_map.
assert (LBS : zlen (map (Z_to_bv 8) buf) = hb) by (rewrite length_map; reflexivity).
carve_frame 128%nat ST.
do 14 zstep.
zstep. zstep. if_cases K0; zify_cond K0; [exfalso; lia|].
do 6 zstep.
zstep. if_cases K1; zify_cond K1;
[exfalso; rewrite (proj2 (Z.ltb_lt 0 BUF) ltac:(lia)), (proj2 (Z.ltb_ge (BUF + hb) 1) ltac:(lia)) in K1; vm_compute in K1; discriminate K1|].
zstep. if_cases K2; zify_cond K2; [exfalso; lia|].
assert (LV3 : Z.land MSVP 3 = MSVP mod 4) by (change 3 with (Z.ones 2); apply Z.land_ones; lia).
zstep. zstep. if_cases K3; zify_cond K3; [exfalso; lia|].
do 3 zstep.
if_cases K; zify_cond K; [exfalso; lia|].
do 6 zstep.
lazymatch type of FR with rw_cells _ _ _ (CB 16 ?j0 :: ?rest) => change (CB 16 j0 :: rest) with ([CB 16 j0] ++ rest) in FR end.
apply rd_rw_cells_app in FR. destruct FR as [FR0 FR]. cbn [cells_size csize Nat.add] in FR.
replace (SPV + -128 + Z.of_nat 16) with (SPV + -112) in FR by lia.
pose proof (rw_cells_merge usegs _ (SPV + -112) [] [C8 (Z_to_bv 64 0)]
[C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] FR) as FM.
cbn [app cells_size cells_bytes csize cbytes Nat.add] in FM. clear FR.
change (le8 (Z_to_bv 64 0) ++ []) with (repeat (Z_to_bv 8 0) 8) in FM.
pose proof (rw_cells_split_CB usegs _ (SPV + -112) [] 8 (repeat (Z_to_bv 8 0) 8)
[C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
[hbn; (8 - hbn)%nat] FM ltac:(cbn [sum_nat]; lia)) as FS.
cbn [app mk_CB_cells] in FS. clear FM. rewrite (pad_tail (Z_to_bv 8 0) hbn) in FS by lia.
change (CB hbn (firstn hbn (repeat (Z_to_bv 8 0) 8)) :: CB (8 - hbn) (repeat (Z_to_bv 8 0) (8 - hbn)) ::
[C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
with ([CB hbn (firstn hbn (repeat (Z_to_bv 8 0) 8))] ++ ([CB (8 - hbn) (repeat (Z_to_bv 8 0) (8 - hbn))] ++
[C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])) in FS.
apply rd_rw_cells_app in FS. destruct FS as [R1 FS]. apply rd_rw_cells_app in FS. destruct FS as [R2 R3].
cbn [cells_size csize Nat.add] in R2, R3.
replace (SPV + -112 + Z.of_nat (hbn + 0)) with (SPV + -112 + hb) in R2, R3 by lia.
replace (SPV + -112 + hb + Z.of_nat (8 - hbn + 0)) with (SPV + -104) in R3 by lia.
call (rd_memcpy_specZ (SPV + -112) BUF hb); [exact HBUF | rewrite length_map; unfold hb; lia | exact R1 | lia | eassumption
| first [reflexivity | f_equal; lia] | reflexivity | reflexivity | lia | lia | lia |].
assert (FB' : Forall (fun c => 0 <= c < 256) buf').
{ subst buf'. apply Forall_app. split; [exact FBY|]. apply Forall_forall. intros c Hc. apply repeat_spec in Hc. lia. }
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
assert (RB8 : rw_cells usegs mm (SPV + -112) [CB 8 (map (Z_to_bv 8) buf')]) end.
{ replace (SPV + -112 + hb) with (SPV + -112 + Z.of_nat (cells_size [CB hbn (map (Z_to_bv 8) buf)])) in R2
by (cbn [cells_size csize Nat.add]; lia).
lazymatch goal with P : rw_cells usegs ?mm (SPV + -112) [CB (Z.to_nat hb) (map (Z_to_bv 8) buf)] |- _ =>
pose proof (proj2 (rd_rw_cells_app usegs mm (SPV + -112) [CB hbn (map (Z_to_bv 8) buf)]
[CB (8 - hbn) (repeat (Z_to_bv 8 0) (8 - hbn))]) (conj P R2)) as RJ;
pose proof (rw_cells_merge usegs mm (SPV + -112) [] [CB hbn (map (Z_to_bv 8) buf); CB (8 - hbn) (repeat (Z_to_bv 8 0) (8 - hbn))] [] RJ) as RM
end.
cbn [app cells_size cells_bytes csize cbytes Nat.add] in RM. rewrite app_nil_r in RM.
replace (hbn + (8 - hbn + 0))%nat with 8%nat in RM by lia.
subst buf'. rewrite map_app, map_repeat. replace (Z.to_nat (8 - hb)) with (8 - hbn)%nat by lia. exact RM. }
clear R2.
do 7 zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
set (C' := mkRD (Z_to_bv 64 0x13fe8) gp tp (Z_to_bv 64 hb) (Z_to_bv 64 MSVP) (Z_to_bv 64 NC) (Z_to_bv 64 TLP) s4 (Z_to_bv 64 (BUF + hb))
s6 s7 s8 s9 s10 s11 F fc mm (SPV + -128) NC MSVP TLP (SPV + -112) lo rt0 buf' msv0) end.
assert (OK' : rd_ok C').
{ unfold rd_ok, RD_STACK. subst C'. cbn [c_buf c_msv0 c_rt0 c_SP c_lo c_NC c_BUF c_MSVP c_TLP]. rewrite LB'.
repeat split; try assumption; try lia. }
assert (HBUF' : bytes_at usegs (c_m C') (c_BUF C') (map (Z_to_bv 8) (c_buf C'))).
{ subst C'. cbn [c_m c_BUF c_buf]. destruct RB8 as [[_ BA] _]. cbn [cells_bytes cbytes] in BA. rewrite app_nil_r in BA. exact BA. }
replace (Z_to_bv 64 8) with (Z_to_bv 64 (zlen (c_buf C'))) by (subst C'; cbn [c_buf]; rewrite LB'; reflexivity).
eapply evt_cut.
{ eapply (rd_body8 C' OK' rt msv tl n tl0); subst C'; cbn [c_m c_NC c_rt0 c_MSVP c_msv0 c_TLP c_BUF c_buf c_lo c_SP];
try eassumption. }
intros ms' PO. hnf in PO. destruct_exs PO. destruct PO as (-> & MU' & WM' & MI' & ST' & ARR' & HMSV' & HTL').
unfold rd_W, RD_STACK in MU'. subst C'.
cbn [c_ra c_gp c_tp c_s0 c_s1 c_s2 c_s3 c_s4 c_s5 c_s6 c_s7 c_s8 c_s9 c_s10 c_s11 c_F c_fc c_m c_SP c_NC c_MSVP c_TLP c_BUF c_lo c_rt0 c_buf c_msv0] in *.
clear ARR HMSV HTL HBUF'.
lazymatch type of MU' with munch _ ?ma ?mb => transport_after_call usegs ma mb MU' WM'; clear MU' WM'; try clear ma end.
replace (ret_pc (Z_to_bv 64 0x13fe8)) with (Z_to_bv 64 0x13fe8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
assert (N1 : 1 <= n).
{ destruct (read_ncount_body8_total buf' (msv0 + 1) rt0 (Forall_all_bytes _ FB') ltac:(unfold FseNCount.Zlength; lia)
ltac:(unfold FseNCount.Zlength; lia)) as [(nc2 & msv2 & tl2 & n2 & E2 & _ & _ & _ & _ & N2 & _) | (e & E2)];
rewrite RB in E2; [injection E2 as <- <- <- <-; lia| discriminate E2]. }
zstep. zstep. replace (hb <? n) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
zstep. rewrite Z.land_0_r.
zstep. if_true.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => lazymatch type of FR0 with rw_cells _ _ _ [CB 16 ?j0] =>
assert (FR : rw_cells usegs mm (SPV + -128)
[CB 16 j0; CB 8 (map (Z_to_bv 8) buf'); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
end end.
{ lazymatch goal with |- rw_cells _ _ _ (CB 16 ?j0 :: ?rest) => change (CB 16 j0 :: rest) with ([CB 16 j0] ++ rest) end.
change (CB 8 (map (Z_to_bv 8) buf') :: [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
with ([CB 8 (map (Z_to_bv 8) buf')] ++ [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
apply rd_rw_cells_app. split; [exact FR0|]. cbn [cells_size csize Nat.add].
replace (SPV + -128 + Z.of_nat 16) with (SPV + -112) by lia.
apply rd_rw_cells_app. split; [exact RB8|]. cbn [cells_size csize Nat.add].
replace (SPV + -112 + Z.of_nat 8) with (SPV + -104) by lia. exact R3. }
clear FR0 RB8 R3.
do 13 zstep. zstep. zstep.
release_frame FR ST' SPV.
apply evt_done. unfold fse_read_post, FSE_READ_STACK.
do 14 eexists. eexists. split; [reflexivity|].
repeat (split; [eassumption|]). eassumption.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End Top.
Theorem fse_read_proof : fse_read_stmt.
Proof.
unfold fse_read_stmt.
intros ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m SPV NC MSVP TLP BUF
rt0 rt buf msv0 msv tl n lo tl0
ARR HMSV HTL HBUF FBY RN HM0 HLEN HNP HNA HVP HVA HTP HTA HBP HSLACK ST LO RSP SNS SMS STS SBS SNM SNT SNB SMT SMB STB MI -> -> -> -> ->.
unfold PFSE_READ.
zstep. zstep.
destruct (Z_lt_le_dec (zlen buf) 8) as [LT|GE].
- eapply (rd_top_small ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV NC MSVP TLP BUF rt0 rt buf msv0 msv tl n lo tl0); eassumption.
- eapply (rd_top8 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV NC MSVP TLP BUF rt0 rt buf msv0 msv tl n lo tl0); eassumption.
Qed.
