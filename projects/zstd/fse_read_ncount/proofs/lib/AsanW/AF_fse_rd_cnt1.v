(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import FseNCount FseLemmas FseReadSound.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Arr Bytes ZBridge.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import FseRdKit.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import AImg ABase RtCells AF_fse_rd_base.
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
Local Ltac acc_enrich ::= rewrite ?shad_div in *; rewrite ?nshad_div in *; unfold ASHOFF, KLOW, KHIGH, KEND in *; rewrite ?Z.shiftr_div_pow2 in * by lia.
Local Ltac acc_hint ::= rdA_acc_hint.
Section CANSEC1. Context {rc : runConstT}.
Section Count1.
Variable C : rdctxA.
Variable RNG : footprint.
Hypothesis OK : rd_okA C.
Hypothesis SH : rd_shA C.
Hypothesis RNGS : rd_rngA C RNG.
Variable tl : Z.
Hypothesis Htl : 5 <= tl <= 15.
Variable POST : machine_state -> Prop.
Notation buf := (a_buf C).
Notation msv1 := (a_msv0 C + 1).
Notation BUF := (a_BUF C).
Ltac cbnR := cbn [r_nc r_ip r_bitStream r_bitCount r_charnum r_remaining r_threshold r_nbBits r_previous0] in *.
Ltac zify_lts K :=
unfold bv_lts in K; rewrite ?land7_mod in K;
rewrite !signed_lit_small64 in K by (Z.div_mod_to_equations; lia);
zify_bool K.
#[using="rc OK RNGS"] Lemma cnt_loadA : forall s2 m1 msvw tlw count ip' (x6 x10 x11 x12 x14 x15 x30 : word),
rd_invA C m1 (r_nc s2) msvw tlw ->
0 <= ip' -> ip' + 4 <= zlen buf -> 0 <= r_bitCount s2 < 32 ->
r_ip s2 = ip' -> r_bitStream s2 = le32 buf ip' / 2 ^ r_bitCount s2 -> r_previous0 s2 = (count =? 0) ->
-1 <= count < 2^31 ->
x10 = Z_to_bv 64 (BUF + ip') -> x6 = Z_to_bv 64 (r_bitCount s2) ->
(forall y12 y14 y15 y19 y30, evtF asegs RNG POST (rd_headA C s2 m1 y12 y14 y15 y19 y30)) ->
evtF asegs RNG POST (rd_lstA C 0x822e8 m1 x6 x10 x11 x12 (Z_to_bv 64 (r_charnum s2)) x14 x15 (Z_to_bv 64 (r_remaining s2))
(Z_to_bv 64 (r_threshold s2)) (Z_to_bv 64 count) (Z_to_bv 64 (r_nbBits s2)) x30).
Proof.
intros s2 m1 msvw tlw count ip' x6 x10 x11 x12 x14 x15 x30 INV Hip0 Hip4 Hbc Eip Ebs Ep0 Hcount -> -> K.
destruct RNGS as (RI & RSTK & RN & RNS & RM & RMS & RT & RTS & RB & RBS).
destruct INV as (_ & _ & HBUF & _).
Local Ltac2 Set LiaHints.tbl := fun () => "00U0>11447729963.8711447729963.8811447729963.961164727413.55 14533046805.4115534906496.6521481650978.5125993773005.622623057474.75 3132576384.65 35120240342.4340138033082.5143929283712.6544144284019.6644207606616.6649792581730.5552520289792.5353508216721.6454742579132.3955036003864.7455705461570.6756641621271.4558067894962.7558805924860.6859586081465.6259588178610.6360245107409.6461536869752.6663407446814.5363872857902.6666721607490.7567048124130.6767488565603.6668185490472.66731462578.75  7330169908.65 8682883843.66 00000100200300A00L00M00R00W00X00Y00d00i00j00k00l01801901:01E01P01Q01\01]01h01i01j01k01l02302>02?02@02A02B02C02N02OFFFS3Hbc6Hcount1LS4Hip04Hip4FS3HbcS3HbcFFS4Hip04Hip4S3HbcFFFS6Hcount1L1NSSS4Hip04Hip4S4Hip04Hip4FS4Hip04Hip4FS4Hip04Hip4SSFFS3Hbc1LS4Hip04Hip4FFFFFS4Hip04Hip4F".
destruct (buf_rdA C OK m1 ip' HBUF ltac:(lia)) as [RD0 R0].
destruct (buf_rdA C OK m1 (ip' + 1) HBUF ltac:(lia)) as [RD1 R1].
destruct (buf_rdA C OK m1 (ip' + 2) HBUF ltac:(lia)) as [RD2 R2].
destruct (buf_rdA C OK m1 (ip' + 3) HBUF ltac:(lia)) as [RD3 R3].
rewrite !Z.add_assoc in RD1, RD2, RD3.
destruct s2 as [nc ip bs bc cn rem thr nb p0]. cbnR. subst ip p0.
unfold rd_lstA.
zstep. cbv beta. zstep. cbv beta. zstep. cbv beta. zstep. cbv beta.
zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
rewrite le32_lb_raw by assumption. rewrite (Z.mod_small bc 32) by lia. rewrite Z.shiftr_div_pow2 by lia.
fold (le32 buf ip'). rewrite <- Ebs.
pose proof K as K'. unfold rd_headA, rd_lstA in K'. cbnR.
zstep. zstep.
if_cases B; zify_cond B.
-
assert (count = 0).
{ destruct (Z.ltb_spec 0 (count mod 18446744073709551616)) as [L|L]; cbn [Z.b2z] in B; [discriminate B|].
destruct (Z.eq_dec count (-1)) as [->|N]; [cbn in L; lia|]. rewrite Z.mod_small in L by lia. lia. }
subst count. change (0 =? 0) with true in K'. apply K'.
- assert (count <> 0).
{ intros ->. apply B. reflexivity. }
replace (count =? 0) with false in K' by (symmetry; apply Z.eqb_neq; assumption).
zstep. apply K'.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="rc OK RNGS"] Lemma rl_chk2 : forall m1 ip' (x6 x11 x12 x13 x14 x15 x16 x17 x19 x23 x30 : word),
unpoisoned m1 BUF (BUF + zlen buf) -> 0 <= ip' -> ip' + 4 <= zlen buf ->
(forall y11 y12 y14, evtF asegs RNG POST (rd_lstA C 0x822e8 m1 x6 (Z_to_bv 64 (BUF + ip')) y11 y12 x13 y14 x15 x16 x17 x19 x23 x30)) ->
evtF asegs RNG POST (rd_lstA C 0x822d4 m1 x6 (Z_to_bv 64 (BUF + ip')) x11 x12 x13 x14 x15 x16 x17 x19 x23 x30).
Proof.
intros m1 ip' x6 x11 x12 x13 x14 x15 x16 x17 x19 x23 x30 UB P0 P4 K.
destruct RNGS as (RI & RSTK & RN & RNS & RM & RMS & RT & RTS & RB & RBS).
pose proof OK as OK'. destruct OK' as (HH & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & BB & _ & _ & _ & _ & _ & _ & _ & _ & B8).
pose proof (ablk_lin _ _ BB) as LBB. unfold KHIGH, AIMG_HI, KEND in *.
Local Ltac2 Set LiaHints.tbl := fun () => "00:0>14364725201.6119492076177.4533813554636.5235118377592.5235319175708.4136401657513.5536401657515.5449118288140.4159314873579.479446685103.61 00000500A00L00T00X00c00n01201C01MS3SR2S2P03LBB3CK2S2P02P43LBBS2B83LBBS2P4S2P02P43LBBS2P02P43LBBS2P0S2P03LBB3CK21G2G'S3CK21G2H0".
destruct (chkB m1 BUF (BUF + zlen buf) (BUF + ip' + 3) UB ltac:(lia) ltac:(lia)) as (b2 & RDB2 & CK2 & SR2).
unfold rd_lstA in K |- *.
zstep. zstep. zstep. zstep. rewrite sxb_sval.
zstep. if_cases G; zify_cond G.
- zstep. zstep. if_cases G'; zify_lts G'; [| exfalso; lia]. apply K.
- apply K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="rc OK RNGS"] Lemma rl_chk1 : forall m1 ip' (x6 x11 x12 x13 x14 x15 x16 x17 x19 x23 x30 : word),
unpoisoned m1 BUF (BUF + zlen buf) -> 0 <= ip' -> ip' + 4 <= zlen buf ->
(forall y11 y12, evtF asegs RNG POST (rd_lstA C 0x822d4 m1 x6 (Z_to_bv 64 (BUF + ip')) y11 y12 x13 x14 x15 x16 x17 x19 x23 x30)) ->
evtF asegs RNG POST (rd_lstA C 0x822c4 m1 x6 (Z_to_bv 64 (BUF + ip')) x11 x12 x13 x14 x15 x16 x17 x19 x23 x30).
Proof.
intros m1 ip' x6 x11 x12 x13 x14 x15 x16 x17 x19 x23 x30 UB P0 P4 K.
destruct RNGS as (RI & RSTK & RN & RNS & RM & RMS & RT & RTS & RB & RBS).
pose proof OK as OK'. destruct OK' as (HH & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & BB & _ & _ & _ & _ & _ & _ & _ & _ & B8).
pose proof (ablk_lin _ _ BB) as LBB. unfold KHIGH, AIMG_HI, KEND in *.
Local Ltac2 Set LiaHints.tbl := fun () => "00:0>33813554636.5234022604115.4134360486178.4135118377592.5239570211675.6153146557993.5453148655143.6159314873579.4764794109999.459446685103.61 00000;00?00C00K00P00[00f01701C01MS2P02P43LBBS2P4S2P0S2B83LBBS3SR1S2P02P43LBBS2P02P43LBBS2P03LBB3CK11G2G'S2P03LBB3CK1S3CK11G2H0".
destruct (chkB m1 BUF (BUF + zlen buf) (BUF + ip') UB ltac:(lia) ltac:(lia)) as (b1 & RDB1 & CK1 & SR1).
unfold rd_lstA in K |- *.
zstep. zstep. zstep. rewrite sxb_sval.
zstep. if_cases G; zify_cond G.
- zstep. zstep. if_cases G'; zify_lts G'; [| exfalso; lia]. apply K.
- apply K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="rc OK RNGS"] Lemma rl_chk1c : forall m1 (x6 x12 x13 x14 x15 x16 x17 x19 x23 x30 : word),
unpoisoned m1 BUF (BUF + zlen buf) ->
(forall y11 y12, evtF asegs RNG POST (rd_lstA C 0x822d4 m1 x6 (Z_to_bv 64 (BUF + zlen buf + -4)) y11 y12 x13 x14 x15 x16 x17 x19 x23 x30)) ->
evtF asegs RNG POST (rd_lstA C 0x82348 m1 x6 (Z_to_bv 64 (BUF + zlen buf + -4)) (Z_to_bv 64 (BUF + zlen buf + -4)) x12 x13 x14 x15 x16 x17 x19 x23 x30).
Proof.
intros m1 x6 x12 x13 x14 x15 x16 x17 x19 x23 x30 UB K.
destruct RNGS as (RI & RSTK & RN & RNS & RM & RMS & RT & RTS & RB & RBS).
pose proof OK as OK'. destruct OK' as (HH & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & BB & _ & _ & _ & _ & _ & _ & _ & _ & B8).
pose proof (ablk_lin _ _ BB) as LBB. unfold KHIGH, AIMG_HI, KEND in *.
Local Ltac2 Set LiaHints.tbl := fun () => "00:0>10990209200.5810992306367.5033813554636.4835118377592.4839570211675.5746153696197.3759314873579.4364794109999.418811860338.37 9446685103.57 00000800@00H00P00U00Y00j01601701AS2HH3LBBS2HH3LBBS2HH3LBBS2B83LBBS3SR1S2HHS2HH3LBB3CK11G2G'S2HH3LBB3CK1SS3CK11G2H0".
destruct (chkB m1 BUF (BUF + zlen buf) (BUF + zlen buf + -4) UB ltac:(lia) ltac:(lia)) as (b1 & RDB1 & CK1 & SR1).
unfold rd_lstA in K |- *.
zstep. zstep. zstep. rewrite sxb_sval.
zstep. if_cases G; zify_cond G.
- apply K.
- zstep. zstep. if_cases G'; zify_lts G'; [| exfalso; lia]. apply K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="rc OK SH RNGS"] Lemma cnt_reloadA : forall s1 s2 m1 msvw tlw count (x6 x11 x14 x15 x30 : word),
rd_invA C m1 (r_nc s1) msvw tlw -> reload buf s1 = Ok s2 ->
0 <= r_ip s1 -> r_ip s1 + 4 <= zlen buf -> 0 <= r_bitCount s1 < 64 ->
r_previous0 s1 = (count =? 0) -> -1 <= count < 2^31 ->
(forall y12 y14 y15 y19 y30, evtF asegs RNG POST (rd_headA C s2 m1 y12 y14 y15 y19 y30)) ->
evtF asegs RNG POST (rd_lstA C 0x822b4 m1 x6 (Z_to_bv 64 (BUF + r_ip s1)) x11 (Z_to_bv 64 (r_bitCount s1)) (Z_to_bv 64 (r_charnum s1))
x14 x15 (Z_to_bv 64 (r_remaining s1)) (Z_to_bv 64 (r_threshold s1)) (Z_to_bv 64 count) (Z_to_bv 64 (r_nbBits s1)) x30).
Proof.
intros s1 s2 m1 msvw tlw count x6 x11 x14 x15 x30 INV RL Hip0 Hip4 Hbc Ep0 Hcount K.
pose proof (reload_inv buf s1 s2 (buf_all_bytesA C OK) RL Hip0 Hip4 (proj1 Hbc)) as RI. cbv zeta in RI.
destruct RI as (I1 & I2 & I3 & ->).
pose proof RNGS as RNGS'. destruct RNGS' as (RIM & RSTK & RN & RNS & RM & RMS & RT & RTS & RB & RBS).
pose proof OK as OK'. destruct OK' as (HH & _ & _ & _ & _ & SP16 & SPK & LOS & LOA & _ & _ & _ & _ & _ & _ & BB & _ & _ & _ & _ & _ & _ & _ & _ & B8).
pose proof (spaA_bounds C SP16) as [[SPA1 SPA2] SPA3].
pose proof (ablk_lin _ _ BB) as LBB. pose proof atop_range as ATR. unfold RDA_CALLEE, KHIGH, AIMG_HI, KEND in *.
pose proof INV as INV'. destruct INV' as (_ & _ & _ & _ & _ & (j16 & FRM) & _ & MU & _). unfold FRA_main in FRM.
destruct (inv_shadowA C m1 OK SH MU) as (_ & _ & _ & UB).
destruct s1 as [nc ip bs bc cn rem thr nb p0]. cbnR. subst p0.
unfold reload_pos in *. unfold FseNCount.Zlength in *.
Local Ltac2 Set LiaHints.tbl := fun () => "00U0>10029754702.6510613833396.6310992306365.7611001195444.6511706759828.6513706453024.6216530564352.6521481521301.6222626797519.6825993772992.7225993772992.7327637725769.7527637725770.7529784644588.6229788724074.6330195467701.6532665485845.6435504068375.6535916362634.7537211491939.7638071471090.6538071471090.6640206209368.6540206209368.6642815240411.6544086960753.7246251409601.7247366385985.6447375192777.7656428502567.7258024162856.6459078035918.6563368379932.6267439684295.6567992669144.6567992669144.668929299744.65 00000400900Y01901>01C01D01I01J01O01T01^01h01i01j01k02K02O02P02Q02U02Y03;03^03g03k03o04V05=05>05B05F05G05P05Q05R06;S2B2S3HbcS3Hbc2I32HH3LOS3LOA4SPA23LBB3ATRS3Hbc2I32HH3LOS3LOA4SPA23LBB3ATRS3HbcS3HbcSS3HbcSS3HbcS3HbcS3LOS4SPA2S3LOS4SPA2SSSS3Hbc2I32HH3LOS3LOA4SPA23LBB3ATRS2B1FSS2I2S2I2S4Hip03Hbc2I33LOS3LOA4SPA23LBB3ATRS3Hbc2I32HH3LOS3LOA4SPA23LBB3ATR2B1S4Hip42B1S2I1S2I2S4Hip04Hip43Hbc2I33LOS3LOA4SPA23LBB3ATRS4Hip04Hip43Hbc2I33LOS3LOA4SPA23LBB3ATRFS2B1S2B2SS4Hip42B1SSS4Hip04Hip43Hbc2I33LOS3LOA4SPA23LBB3ATR1Q".
rewrite Z.shiftr_div_pow2 in * by lia. change (2^3) with 8 in *. rewrite land_7, land_31 in *.
assert (Q : 0 <= bc / 8 < 8) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
assert (LOAD : forall ip' bc' (y11 y12 y14 y15 y30 : word),
fst (if (ip <=? zlen buf - 7) || (ip + bc / 8 <=? zlen buf - 4) then (ip + bc / 8, bc mod 8) else (zlen buf - 4, (bc - 8 * (zlen buf - 4 - ip)) mod 32)) = ip' ->
snd (if (ip <=? zlen buf - 7) || (ip + bc / 8 <=? zlen buf - 4) then (ip + bc / 8, bc mod 8) else (zlen buf - 4, (bc - 8 * (zlen buf - 4 - ip)) mod 32)) = bc' ->
evtF asegs RNG POST (rd_lstA C 0x822d4 m1 (Z_to_bv 64 bc') (Z_to_bv 64 (BUF + ip')) y11 y12 (Z_to_bv 64 cn) y14 y15
(Z_to_bv 64 rem) (Z_to_bv 64 thr) (Z_to_bv 64 count) (Z_to_bv 64 nb) y30)).
{ intros ip' bc' y11 y12 y14 y15 y30 E1 E2. rewrite E1, E2 in *.
eapply (rl_chk2 m1 ip'); [exact UB| lia| lia|]. intros z11 z12 z14.
eapply (cnt_loadA (FseNCount.mkR nc ip' (le32 buf ip' / 2 ^ bc') bc' cn rem thr nb (count =? 0)) m1 msvw tlw count ip');
try eassumption; try reflexivity; cbnR; try lia; try reflexivity. }
clear K. unfold rd_lstA in LOAD |- *.
zstep. rewrite signed_lit by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
zstep.
if_cases B1; zify_cond B1.
-
zstep. zstep. zstep.
if_cases B2; zify_cond B2.
+
replace ((ip <=? zlen buf - 7) || (ip + bc / 8 <=? zlen buf - 4)) with true in LOAD, I2
by (symmetry; apply orb_true_iff; right; apply Z.leb_le; lia). cbn [fst] in I2.
zstep. zstep. rewrite land_7.
pose proof (rl_chk1 m1 (ip + bc / 8)) as CK1. unfold rd_lstA in CK1.
replace (BUF + ip + bc / 8) with (BUF + (ip + bc / 8)) by lia.
eapply CK1; [exact UB| lia| lia|]. intros y11 y12.
eapply (LOAD (ip + bc / 8) (bc mod 8)); reflexivity.
+ replace ((ip <=? zlen buf - 7) || (ip + bc / 8 <=? zlen buf - 4)) with false in LOAD
by (symmetry; apply orb_false_iff; split; apply Z.leb_gt; lia).
zstep. zstep.
replace (BUF + ip - (BUF + zlen buf + -4)) with (ip - zlen buf + 4) by lia.
rewrite (FseWalkKit.swrap32_small (ip - zlen buf + 4)) by lia.
zstep. zstep. zstep.
rewrite (clamp_bc bc (ip - zlen buf + 4)) by lia.
replace (bc + 8 * (ip - zlen buf + 4)) with (bc - 8 * (zlen buf - 4 - ip)) by lia.
zstep.
pose proof (rl_chk1c m1) as CK1. unfold rd_lstA in CK1.
eapply CK1; [exact UB|]. intros y11 y12.
replace (BUF + zlen buf + -4) with (BUF + (zlen buf - 4)) by lia.
eapply (LOAD (zlen buf - 4) ((bc - 8 * (zlen buf - 4 - ip)) mod 32)); reflexivity.
- replace ((ip <=? zlen buf - 7) || (ip + bc / 8 <=? zlen buf - 4)) with true in LOAD, I2
by (symmetry; apply orb_true_iff; left; apply Z.leb_le; lia). cbn [fst] in I2.
zstep. zstep. rewrite land_7.
pose proof (rl_chk1 m1 (ip + bc / 8)) as CK1. unfold rd_lstA in CK1.
replace (BUF + ip + bc / 8) with (BUF + (ip + bc / 8)) by lia.
eapply CK1; [exact UB| lia| lia|]. intros y11 y12.
eapply (LOAD (ip + bc / 8) (bc mod 8)); reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="rc OK RNGS"] Lemma cnt_hbA : forall r m1 nc msvw tlw (x6 x10 x11 x12 x13 x14 x15 x17 x19 x23 x30 : word),
rd_invA C m1 nc msvw tlw -> 2 <= r < 32768 ->
(forall y11 y14 y15 y17 y23, y23 = Z_to_bv 64 (Z.log2 r + 1) -> y17 = Z_to_bv 64 (2 ^ Z.log2 r) ->
evtF asegs RNG POST (rd_lstA C 0x822b0 m1 x6 x10 y11 x12 x13 y14 y15 (Z_to_bv 64 r) y17 x19 y23 x30)) ->
evtF asegs RNG POST (rd_lstA C 0x8223c m1 x6 x10 x11 x12 x13 x14 x15 (Z_to_bv 64 r) x17 x19 x23 x30).
Proof.
intros r m1 nc msvw tlw x6 x10 x11 x12 x13 x14 x15 x17 x19 x23 x30 INV Hr K.
pose proof INV as INV'. destruct INV' as (_ & _ & _ & _ & _ & (j16 & FRM) & _). unfold FRA_main in FRM.
pose proof RNGS as RNGS'. destruct RNGS' as (RIM & RSTK & _).
pose proof OK as OK'. destruct OK' as (_ & _ & _ & _ & _ & SP16 & SPK & LOS & LOA & _).
pose proof (spaA_bounds C SP16) as [[SPA1 SPA2] SPA3]. pose proof atop_range as ATR. unfold RDA_CALLEE, KHIGH, KEND in *.
unfold rd_lstA in *.
Local Ltac2 Set LiaHints.tbl := fun () => "00M0>12835519648.5012835519651.5112837616808.5212837616811.5313204214924.4114939502105.5123924481616.512548589754.50 28913119920.5428913119922.5228915217081.5128915217082.5029016324134.5629018421289.5134885248673.5341408184391.4952320880309.5152320880312.4859586081465.5159586081466.5059586081467.4959588178608.5459588178610.5264344627641.516744704702.52 8935173665.53 8935173666.52 8937270820.48 8937270826.50 00000100200300400800900C00D00E00F00G00H00L00P00Q00R00S00T00U00V00W00X00Y00Z00[00\00]00^00_FFFFS2HrFS3LOS4SPA2SSSSSS2HrS2HrFSFFSSSSSSSFFFF".
zstep. zstep. brute_regF 11 r 2 32766 sm1.
zstep. zstep. brute_regF 11 r 2 32766 sm2.
zstep. zstep. brute_regF 11 r 2 32766 sm3.
zstep. zstep. brute_regF 11 r 2 32766 sm4.
zstep. zstep. brute_regF 11 r 2 32766 sm5.
do 14 zstep.
brute_regF 11 r 2 32766 (fun r0 => 31 - Z.log2 r0).
zstep. zstep. zstep.
brute_regF 23 r 2 32766 (fun r0 => Z.log2 r0 + 1).
zstep. zstep.
brute_regF 17 r 2 32766 (fun r0 => 2 ^ Z.log2 r0).
eapply K; reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="rc OK SH RNGS"] Lemma cnt_finA : forall s1 m1 msvw tlw count fl (x6 x11 x14 x15 x30 : word),
rd_invA C m1 (r_nc s1) msvw tlw ->
0 <= r_ip s1 -> r_ip s1 + 4 <= zlen buf -> 0 <= r_bitCount s1 < 64 -> 1 <= r_charnum s1 <= msv1 -> 1 <= r_remaining s1 < 2^31 ->
r_previous0 s1 = (count =? 0) -> -1 <= count < 2^31 ->
(if msv1 <=? r_charnum s1 then Ok (Brk s1) else let! s2 := reload buf s1 in Ok (Cont s2)) = Ok fl ->
(forall s' m2 y6 y11 y14 y15 y17 y19 y23 y30, fl = Brk s' -> rd_invA C m2 (r_nc s') msvw tlw -> rd_brk_okA C s' ->
evtF asegs RNG POST (rd_exitA C s' m2 y6 y11 y14 y15 y17 y19 y23 y30)) ->
(forall s' m2 y12 y14 y15 y19 y30, fl = Cont s' -> rd_invA C m2 (r_nc s') msvw tlw ->
evtF asegs RNG POST (rd_headA C s' m2 y12 y14 y15 y19 y30)) ->
evtF asegs RNG POST (rd_lstA C 0x822b0 m1 x6 (Z_to_bv 64 (BUF + r_ip s1)) x11 (Z_to_bv 64 (r_bitCount s1)) (Z_to_bv 64 (r_charnum s1))
x14 x15 (Z_to_bv 64 (r_remaining s1)) (Z_to_bv 64 (r_threshold s1)) (Z_to_bv 64 count) (Z_to_bv 64 (r_nbBits s1)) x30).
Proof.
intros s1 m1 msvw tlw count fl x6 x11 x14 x15 x30 INV Hip0 Hip4 Hbc Hcn Hrem Ep0 Hcount RR KB KC.
pose proof OK as OK'. destruct OK' as (HH & _ & HM0 & _).
destruct (Z.leb_spec msv1 (r_charnum s1)) as [GE|LT].
-
injection RR as <-.
pose proof (KB s1 m1) as KB'. unfold rd_exitA, rd_lstA in KB'.
destruct s1 as [nc ip bs bc cn rem thr nb p0]. cbnR.
unfold rd_lstA.
zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0070>10429784937.4218302863776.4218302863776.4619622043024.4219622043024.4659315036641.4259315036641.4600000L00U00a00f00k011017S4Hip04Hip43Hbc3Hcn4Hrem3HM0S3Hcn3HM0S3Hcn3HM02LTS3HM0S3HM0S2GE1BS2LT1B".
if_cases B; zify_cond B; [| exfalso; lia].
eapply KB'; [reflexivity| exact INV|]. unfold rd_brk_okA. cbnR. change (2^31) with 2147483648 in *. lia.
- destruct (reload buf s1) as [s2| | |] eqn:RL; cbn [bind] in RR; try discriminate RR. injection RR as <-.
pose proof (fun y12 y14 y15 y19 y30 => KC s2 m1 y12 y14 y15 y19 y30 eq_refl) as KC'.
assert (INV2 : rd_invA C m1 (r_nc s2) msvw tlw).
{ pose proof (reload_inv buf s1 s2 (buf_all_bytesA C OK) RL Hip0 Hip4 (proj1 Hbc)) as RI. cbv zeta in RI.
destruct RI as (_ & _ & _ & ->). cbnR. exact INV. }
specialize (fun y12 y14 y15 y19 y30 => KC' y12 y14 y15 y19 y30 INV2).
pose proof (cnt_reloadA s1 s2 m1 msvw tlw count) as CR. unfold rd_lstA in CR.
destruct s1 as [nc ip bs bc cn rem thr nb p0]. cbnR.
unfold rd_lstA.
zstep. if_cases B; zify_cond B; [exfalso; lia|].
eapply CR; try eassumption; cbnR; try lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End Count1.
End CANSEC1.
