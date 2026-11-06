(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import FseNCount FseLemmas FseReadSound.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Arr Bytes ZBridge Image.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import FseRdKit FseRdKit2.
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
Definition ADB_TAB : Z := 138969.
#[using="Type"] Lemma tab_rdA : forall m1 i, mem_inv asegs m1 -> 0 <= i < 32 ->
ov_read_bytes asegs m1 (Z_to_bv 64 (ADB_TAB + i)) 1 = Some [Z_to_bv 8 (nth (Z.to_nat i) DB_TABLE 0)].
Proof.
intros m1 i MI Hi.
assert (RO : ro_cells asegs m1 ADB_TAB [CB 32 (map (Z_to_bv 8) DB_TABLE)]).
{ Local Ltac2 Set LiaHints.tbl := fun () => "0040=10351690818.62130477481.6 32807138238.552353795557.500000400800900:S2HiS2HiSS".
apply (ro_cells_image asegs m1 ADB_TAB (map (Z_to_bv 8) DB_TABLE) MI); [vm_compute; reflexivity| unfold ADB_TAB; lia| cbn; unfold ADB_TAB; lia]. }
destruct RO as [_ BA]. cbn [cells_bytes cbytes] in BA. rewrite app_nil_r in BA.
eapply (u8ro_read asegs m1 ADB_TAB _ i); [exact BA| | lia| unfold wa; f_equal; lia].
rewrite nth_error_map. rewrite (nth_error_nth' DB_TABLE 0) by (cbn; lia). reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Section Zero.
Variable C : rdctxA.
Variable RNG : footprint.
Hypothesis OK : rd_okA C.
Hypothesis SH : rd_shA C.
Hypothesis RNGS : rd_rngA C RNG.
Variable POST : machine_state -> Prop.
Notation buf := (a_buf C).
Notation msv1 := (a_msv0 C + 1).
Notation BUF := (a_BUF C).
Ltac cbnR := cbn [r_nc r_ip r_bitStream r_bitCount r_charnum r_remaining r_threshold r_nbBits r_previous0] in *.
Ltac zify_lts K :=
unfold bv_lts in K; rewrite ?land7_mod in K;
rewrite !signed_lit_small64 in K by (Z.div_mod_to_equations; lia);
zify_bool K.
#[using="rc OK SH"] Lemma bufmem : forall m1 nc msvw tlw, rd_invA C m1 nc msvw tlw ->
unpoisoned m1 BUF (BUF + zlen buf) /\ mem_inv asegs m1 /\ bytes_at asegs m1 BUF (map (Z_to_bv 8) buf).
Proof.
intros m1 nc msvw tlw (_ & _ & HB & _ & _ & _ & _ & MU & _ & MI).
destruct (inv_shadowA C m1 OK SH MU) as (_ & _ & _ & UB). auto.
Qed.
#[using="RNGS"] Lemma zero_ctz1A : forall bs m1 (x6 x10 x12 x13 x14 x15 x16 x17 x19 x23 x30 : word),
0 <= bs < 2^32 -> mem_inv asegs m1 ->
evtF asegs RNG POST (rd_lstA C 0x8204c m1 x6 x10 (Z_to_bv 64 (bv_swrap 32 bs)) (Z_to_bv 64 (ctzv bs)) x13 (Z_to_bv 64 ADB_TAB)
x15 x16 x17 x19 x23 x30) ->
evtF asegs RNG POST (rd_lstA C 0x82024 m1 x6 x10 (Z_to_bv 64 (bv_swrap 32 bs)) x12 x13 x14 x15 x16 x17 x19 x23 x30).
Proof.
intros bs m1 x6 x10 x12 x13 x14 x15 x16 x17 x19 x23 x30 Hbs MI K.
pose proof RNGS as RNGS'. destruct RNGS' as (RI & _).
pose proof (ctzv_range bs Hbs) as Rk. Local Ltac2 Set LiaHints.tbl := fun () => "00:0>14937404945.4124578435691.282521426602.38 27521348601.4528913119921.4128913119922.4044613673395.3959588178609.4159588178610.4062186928258.2500000100500600700800900=00>00?00CFS2RkFFSSS2RiSSS2Rk".
destruct (db_table_ok (ctzv bs) ltac:(lia)) as [Ri Et].
pose proof (tab_rdA m1 (db_idx (ctzv bs)) MI Ri) as RD. rewrite Et in RD. unfold ADB_TAB in *.
unfold rd_lstA in *.
do 9 zstep.
rewrite (ctz_index_form bs Hbs).
zstep. cbv beta. rewrite byte_lit by lia.
exact K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="rc OK SH RNGS"] Lemma zero_load1A : forall m1 msvw tlw nc ip' bc' cn (x11 x12 x15 x19 x30 : word) (x16 x17 x23 : word),
rd_invA C m1 nc msvw tlw -> 0 <= ip' -> ip' + 4 <= zlen buf -> 0 <= bc' < 32 -> 0 <= cn < 2^31 ->
(forall (y15 y30 : word), evtF asegs RNG POST (rd_lstA C 0x820d0 m1 (Z_to_bv 64 bc') (Z_to_bv 64 (BUF + ip'))
(Z_to_bv 64 (bv_swrap 32 (le32 buf ip' / 2 ^ bc'))) (Z_to_bv 64 (ctzv (le32 buf ip' / 2 ^ bc')))
(Z_to_bv 64 (cn + 36)) (Z_to_bv 64 ADB_TAB) y15 x16 x17 x19 x23 y30)) ->
evtF asegs RNG POST (rd_lstA C 0x8206c m1 (Z_to_bv 64 bc') (Z_to_bv 64 (BUF + ip')) x11 x12 (Z_to_bv 64 cn) (Z_to_bv 64 ADB_TAB)
x15 x16 x17 x19 x23 x30).
Proof.
intros m1 msvw tlw nc ip' bc' cn x11 x12 x15 x19 x30 x16 x17 x23 INV Hip0 Hip4 Hbc Hcn K.
destruct (bufmem m1 nc msvw tlw INV) as (UB & MI & HBUF).
destruct RNGS as (RI & RSTK & RN & RNS & RM & RMS & RT & RTS & RB & RBS).
pose proof OK as OK'. destruct OK' as (HH & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & BB & _ & _ & _ & _ & _ & _ & _ & _ & B8).
pose proof (ablk_lin _ _ BB) as LBB. unfold KHIGH, AIMG_HI, KEND in *.
Local Ltac2 Set LiaHints.tbl := fun () => "01?0?11447729958.10011447729963.10111447729963.10211447729963.10511447729963.99 11708949354.76 14364725201.81 14534970925.52 14937404945.76 15040017720.81 15534906502.79 19492076177.65 23985042083.76 2523523746.75  25261073778.72 2623057474.84  27846198189.72 28749142564.76 28913119920.77 28913119921.76 28913119926.79 29782367974.77 3132576390.79  33813554636.72 35016289838.80 35118050157.54 35118377592.72 35319175708.46 35616724157.76 36399560354.77 36401657513.75 38915001345.72 39440854097.72 40415828554.76 40690850763.58 40690850763.64 42389204136.72 43929283713.76 44144284019.78 44207606616.78 44611576251.76 44922573182.81 46073795420.78 48695830302.84 49035591555.76 49118288140.46 49846579416.84 52435088287.72 52837053217.72 54483527401.78 54738809505.50 55036003859.83 55705461570.80 56117678754.72 56648020013.56 56662150274.72 57631218415.61 58067894962.84 58702985864.80 58805924860.80 59314873579.67 59588178608.77 59588178609.76 59588178614.79 60593140095.72 61536869752.78 62433116916.76 63872857903.79 6455047084.77  66721607490.84 67048124130.80 67488565603.78 68169892079.64 68185490472.78 731462578.84   7330169908.77  8682883843.78  8918665695.64  9446685103.81  00000100200300400500600;00F00G00H00I00W00X00Y00Z00[00\00]00^00_00`00a00b01101201=01I01O01P01_01n01o02002102602;02<02=02>02?02C02D02E02F02G02M02N02O02P02Q02\02g02h02i03403503903:03;03F03]03^03_03`03a03b03c03n04304404504604:04;04<04G04H04M04WFFFFFFS3SR2S4Hip04Hip4FFFS4Hip03LBB3CK2FFFFFFSSSSFS4Hip04Hip43LBBFS4Hip04Hip4S3Hbc2B83LBBS4Hip4FS4Hip04Hip43LBBS4Hip04Hip43LBBFFFS3HbcS3HbcFFFFS2RiFFFFS4Hip0FFFFS4Hip04Hip4S4Hip04Hip4FFS4Hip04Hip4FS2RkFFS4Hip04Hip4S4Hip03Hbc3LBB3CK21G2G'SSSFFFS4Hip04Hip4S3HbcFFFS2RkFFS4Hip04Hip4FS3HbcS3CK21G2H0".
destruct (chkB m1 BUF (BUF + zlen buf) (BUF + ip' + 3) UB ltac:(lia) ltac:(lia)) as (b2 & RDB2 & CK2 & SR2).
destruct (buf_rdA C OK m1 ip' HBUF ltac:(lia)) as [RD0 R0].
destruct (buf_rdA C OK m1 (ip' + 1) HBUF ltac:(lia)) as [RD1 R1].
destruct (buf_rdA C OK m1 (ip' + 2) HBUF ltac:(lia)) as [RD2 R2].
destruct (buf_rdA C OK m1 (ip' + 3) HBUF ltac:(lia)) as [RD3 R3].
rewrite !Z.add_assoc in RD1, RD2, RD3.
set (bs' := le32 buf ip' / 2 ^ bc') in *.
assert (Rbs : 0 <= bs' < 2^32) by (subst bs'; apply shr_range; [apply le32_range; apply (buf_all_bytesA C OK)| lia]).
pose proof (ctzv_range bs' Rbs) as Rk. destruct (db_table_ok (ctzv bs') ltac:(lia)) as [Ri Et].
pose proof (tab_rdA m1 (db_idx (ctzv bs')) MI Ri) as RDT. rewrite Et in RDT. unfold ADB_TAB in *.
assert (LD : forall (y11 y12 y15 : word),
evtF asegs RNG POST (rd_lstA C 0x82080 m1 (Z_to_bv 64 bc') (Z_to_bv 64 (BUF + ip')) y11 y12 (Z_to_bv 64 cn) (Z_to_bv 64 138969)
y15 x16 x17 x19 x23 x30)).
{ intros y11 y12 y15. clear RDB2 CK2 SR2. unfold rd_lstA in K |- *.
zstep. cbv beta. zstep. cbv beta. zstep. cbv beta. zstep. cbv beta.
zstep. zstep. zstep. zstep. zstep. zstep.
zstep.
rewrite le32_lb_raw by assumption. rewrite (Z.mod_small bc' 32) by lia. rewrite Z.shiftr_div_pow2 by lia.
fold (le32 buf ip'). fold bs'.
do 7 zstep.
rewrite (ctz_index_form bs' Rbs).
zstep. cbv beta. rewrite byte_lit by lia.
zstep. rewrite ?(FseWalkKit.swrap32_small (cn + 36)) by lia.
apply K. }
unfold rd_lstA in LD |- *.
zstep. zstep. zstep. zstep. rewrite sxb_sval.
zstep. if_cases G; zify_cond G.
- zstep. zstep. if_cases G'; zify_lts G'; [| exfalso; lia]. apply LD.
- apply LD.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="rc OK SH RNGS"] Lemma zero_chk1A : forall m1 msvw tlw nc ip' (x6 x11 x12 x13 x15 x16 x17 x19 x23 x30 : word),
rd_invA C m1 nc msvw tlw -> 0 <= ip' -> ip' + 4 <= zlen buf ->
(forall y11 y12, evtF asegs RNG POST (rd_lstA C 0x8206c m1 x6 (Z_to_bv 64 (BUF + ip')) y11 y12 x13 (Z_to_bv 64 ADB_TAB) x15 x16 x17 x19 x23 x30)) ->
evtF asegs RNG POST (rd_lstA C 0x8205c m1 x6 (Z_to_bv 64 (BUF + ip')) x11 x12 x13 (Z_to_bv 64 ADB_TAB) x15 x16 x17 x19 x23 x30).
Proof.
intros m1 msvw tlw nc ip' x6 x11 x12 x13 x15 x16 x17 x19 x23 x30 INV P0 P4 K.
destruct (bufmem m1 nc msvw tlw INV) as (UB & MI & HBUF).
destruct RNGS as (RI & RSTK & RN & RNS & RM & RMS & RT & RTS & RB & RBS).
pose proof OK as OK'. destruct OK' as (HH & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & BB & _ & _ & _ & _ & _ & _ & _ & _ & B8).
pose proof (ablk_lin _ _ BB) as LBB. unfold KHIGH, AIMG_HI, KEND in *.
Local Ltac2 Set LiaHints.tbl := fun () => "00:0>33813554636.5534022604115.4434360486178.4435118377592.5539570211675.6453146557993.5753148655142.6559314873579.5064794109999.489446685103.64 00000;00?00C00K00P00[00f01701C01MS2P02P43LBBS2P4S2P0S2B83LBBS3SR1S2P02P43LBBS2P02P43LBBS2P03LBB3CK11G2G'S2P03LBB3CK1S3CK11G2H0".
destruct (chkB m1 BUF (BUF + zlen buf) (BUF + ip') UB ltac:(lia) ltac:(lia)) as (b1 & RDB1 & CK1 & SR1).
unfold rd_lstA in K |- *.
zstep. zstep. zstep. rewrite sxb_sval.
zstep. if_cases G; zify_cond G.
- zstep. zstep. if_cases G'; zify_lts G'; [| exfalso; lia]. apply K.
- apply K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="rc OK SH RNGS"] Lemma zero_chk1cA : forall m1 msvw tlw nc (x6 x11 x12 x13 x15 x16 x17 x19 x23 x30 : word),
rd_invA C m1 nc msvw tlw ->
(forall y11 y12, evtF asegs RNG POST (rd_lstA C 0x8206c m1 x6 (Z_to_bv 64 (BUF + zlen buf + -4)) y11 y12 x13 (Z_to_bv 64 ADB_TAB) x15 x16 x17 x19 x23 x30)) ->
evtF asegs RNG POST (rd_lstA C 0x820ec m1 x6 (Z_to_bv 64 (BUF + zlen buf + -4)) x11 x12 x13 (Z_to_bv 64 ADB_TAB) x15 x16 x17 x19 x23 x30).
Proof.
intros m1 msvw tlw nc x6 x11 x12 x13 x15 x16 x17 x19 x23 x30 INV K.
destruct (bufmem m1 nc msvw tlw INV) as (UB & MI & HBUF).
destruct RNGS as (RI & RSTK & RN & RNS & RM & RMS & RT & RTS & RB & RBS).
pose proof OK as OK'. destruct OK' as (HH & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & BB & _ & _ & _ & _ & _ & _ & _ & _ & B8).
pose proof (ablk_lin _ _ BB) as LBB. unfold KHIGH, AIMG_HI, KEND in *.
Local Ltac2 Set LiaHints.tbl := fun () => "00:0>10990209200.6210992306367.5433813554636.5235118377592.5239570211675.6146153696197.4159314873579.4764794109999.458811860338.41 9446685103.61 00000800@00H00P00U00Y00j01601701AS2HH3LBBS2HH3LBBS2HH3LBBS2B83LBBS3SR1S2HHS2HH3LBB3CK11G2G'S2HH3LBB3CK1SS3CK11G2H0".
destruct (chkB m1 BUF (BUF + zlen buf) (BUF + zlen buf + -4) UB ltac:(lia) ltac:(lia)) as (b1 & RDB1 & CK1 & SR1).
unfold rd_lstA in K |- *.
zstep. zstep. zstep. rewrite sxb_sval.
zstep. if_cases G; zify_cond G.
- apply K.
- zstep. zstep. if_cases G'; zify_lts G'; [| exfalso; lia]. apply K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="rc OK SH RNGS"] Lemma zero_repA : forall f s rep s1 rep1 m1 msvw tlw pc (x15 x16 x17 x19 x23 x30 : word),
rep_loop buf f s rep = Ok (s1, rep1) ->
rd_invA C m1 (r_nc s) msvw tlw ->
0 <= r_bitStream s < 2^32 -> 0 <= r_ip s -> r_ip s + 4 <= zlen buf -> 0 <= r_bitCount s < 32 ->
0 <= r_charnum s -> r_charnum s + 36 * Z.of_nat f <= 2^30 ->
rep = ctzv (r_bitStream s) / 2 ->
(pc = 0x8204c \/ pc = 0x820d0) ->
(forall y15 y30,
0 <= r_bitStream s1 < 2^32 -> 0 <= r_ip s1 -> r_ip s1 + 4 <= zlen buf -> 0 <= r_bitCount s1 < 32 ->
0 <= r_charnum s1 <= 2^30 -> rep1 = ctzv (r_bitStream s1) / 2 -> rep1 < 12 ->
r_nc s1 = r_nc s /\ r_remaining s1 = r_remaining s /\ r_threshold s1 = r_threshold s /\ r_nbBits s1 = r_nbBits s /\ r_previous0 s1 = r_previous0 s ->
evtF asegs RNG POST (rd_lstA C 0x82114 m1 (Z_to_bv 64 (r_bitCount s1)) (Z_to_bv 64 (BUF + r_ip s1)) (Z_to_bv 64 (bv_swrap 32 (r_bitStream s1)))
(Z_to_bv 64 (ctzv (r_bitStream s1))) (Z_to_bv 64 (r_charnum s1)) (Z_to_bv 64 ADB_TAB) y15 x16 x17 x19 x23 y30)) ->
evtF asegs RNG POST (rd_lstA C pc m1 (Z_to_bv 64 (r_bitCount s)) (Z_to_bv 64 (BUF + r_ip s)) (Z_to_bv 64 (bv_swrap 32 (r_bitStream s)))
(Z_to_bv 64 (ctzv (r_bitStream s))) (Z_to_bv 64 (r_charnum s)) (Z_to_bv 64 ADB_TAB) x15 x16 x17 x19 x23 x30).
Proof.
induction f as [|f IH]; intros s rep s1 rep1 m1 msvw tlw pc x15 x16 x17 x19 x23 x30 RL INV Hbs Hip0 Hip4 Hbc Hcn0 Hcn Erep Hpc K.
{ cbn in RL. discriminate RL. }
pose proof RNGS as RNGS0. destruct RNGS0 as (RIq & RSTK & _). pose proof (okA_lin C OK) as (_ & _ & _ & _ & _ & _ & LOs & LOAs & SPA1 & SPA2 & _). pose proof atop_range as ATR. unfold RDA_CALLEE in LOs.
pose proof OK as OK'. destruct OK' as (HH & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & BB & _ & _ & _ & _ & _ & _ & _ & _ & B8).
pose proof (ablk_lin _ _ BB) as LBB. unfold KHIGH, AIMG_HI, KEND in *.
pose proof INV as INV'. destruct INV' as (_ & _ & _ & _ & _ & (j16 & FRM) & _). unfold FRA_main in FRM.
pose proof (ctzv_range _ Hbs) as Rk.
cbn [rep_loop] in RL.
destruct s as [nc ip bs bc cn rem thr nb p0]. cbnR.
change (2^30) with 1073741824 in *. rewrite Nat2Z.inj_succ in Hcn.
destruct (Z.leb_spec 12 rep) as [GE|LT].
-
Local Ltac2 Set LiaHints.tbl := fun () => "00O0>12142180252.6014571758871.731667314836.54 1667314836.57 18348088741.5922626797519.6227639822916.7427907486628.6029786284892.6231171024267.5732671791780.5932676405652.7335506171687.5937211491939.7540688772470.7241207268175.734304519851.70 47364278768.5947377289920.7348792160730.7350001714856.7350278756614.6251189755707.7151456153634.7154388315196.60555273265.83  56588533450.7158030444185.5959315036641.5459315036641.5761756416939.5900000600700;00?00@00A00K00L00M00k01C01[01^01_01c01h01i02H02g02m03603703X03`03c03l03m04004704>04FS4Hip0SS2RkS2RkSSS3LOs4SPA1SSS4Hcn03Hcn3LOs4LOAs3ATR3LBB2RkS3LOs4LOAs3ATR2HH3LBB2RkS3LOs4LOAs3ATR2HH3LBB2RkS1BSS2I3S3HcnFS4Hip04Hip43LOs4LOAs3ATR3LBB2RkS4Hip04Hip43LOs4LOAs3ATR3LBB2RkS4Hcn0S2LT1H2H0SS4Hcn03Hcn3LOs4LOAs3ATR3LBB2Rk2I3S4Hip41BS1BS2GE1H2H0FS1BS3K241BS3K241BS4Hip41B".
assert (K24 : 24 <= ctzv bs) by (subst rep; Z.div_mod_to_equations; lia).
unfold FseNCount.Zlength in RL.
assert (LOAD : forall ip' bc' (y11 y12 y15 y30 : word),
(let! w := readLE32 buf ip' in let! bs0 := shr32 w bc' in let! repeats' := repeats_of bs0 in
rep_loop buf f (FseNCount.mkR nc ip' bs0 bc' (cn + 3 * 12) rem thr nb p0) repeats') = Ok (s1, rep1) ->
evtF asegs RNG POST (rd_lstA C 0x8206c m1 (Z_to_bv 64 bc') (Z_to_bv 64 (BUF + ip')) y11 y12 (Z_to_bv 64 cn) (Z_to_bv 64 ADB_TAB)
y15 x16 x17 x19 x23 y30)).
{ intros ip' bc' y11 y12 y15 y30 RL'.
destruct (readLE32 buf ip') as [w| | |] eqn:ER; cbn [bind] in RL'; try discriminate RL'.
destruct (shr32 w bc') as [bs'| | |] eqn:ES; cbn [bind] in RL'; try discriminate RL'.
destruct (repeats_of bs') as [rep'| | |] eqn:EP; cbn [bind] in RL'; try discriminate RL'.
destruct (readLE32_inv _ _ _ ER) as (I1 & I2 & ->). destruct (shr32_inv _ _ _ ES) as (I3 & ->).
assert (Rbs' : 0 <= le32 buf ip' / 2 ^ bc' < 2^32) by (apply shr_range; [apply le32_range; apply (buf_all_bytesA C OK)| lia]).
rewrite (repeats_of_ctzv _ Rbs') in EP. injection EP as <-.
eapply (zero_load1A m1 msvw tlw nc ip' bc' cn); try eassumption; try lia.
intros z15 z30.
eapply (IH (FseNCount.mkR nc ip' (le32 buf ip' / 2 ^ bc') bc' (cn + 3 * 12) rem thr nb p0) _ s1 rep1 m1 msvw tlw 0x820d0);
cbnR; try eassumption; try reflexivity; try lia.
all: intros y15' y30' H1 H2 H3 H4 H5 H6 H7 H8; apply K; assumption. }
clear IH K. unfold rd_lstA in LOAD |- *.
assert (T0 : forall (y15 : word), evtF asegs RNG POST
(rd_lstA C 0x82054 m1 (Z_to_bv 64 bc) (Z_to_bv 64 (BUF + ip)) (Z_to_bv 64 (bv_swrap 32 bs)) (Z_to_bv 64 (ctzv bs))
(Z_to_bv 64 cn) (Z_to_bv 64 ADB_TAB) y15 x16 x17 x19 x23 x30)).
{ intros y15. unfold rd_lstA. zstep.
if_cases B; zify_cond B.
-
replace (ip <=? zlen buf - 7) with false in RL by (symmetry; apply Z.leb_gt; lia).
zstep. replace (BUF + ip - (BUF + zlen buf + -7)) with (ip - zlen buf + 7) by lia.
rewrite ?(FseWalkKit.swrap32_small (ip - zlen buf + 7)) by lia.
zstep. zstep. zstep.
zstep.
pose proof (zero_chk1cA m1 msvw tlw nc) as CK. unfold rd_lstA in CK.
eapply CK; [exact INV|]. intros y11 y12.
replace (BUF + zlen buf + -4) with (BUF + (zlen buf - 4)) by lia.
replace (Z.land (((ip - zlen buf + 7) ≪ 3 + bc) mod 18446744073709551616) 31)
with (Z.land (bc - 8 * (zlen buf - 7 - ip)) 31).
2:{ rewrite !land_31. rewrite Z.shiftl_mul_pow2 by lia. change (2^3) with 8.
change 18446744073709551616 with (2^64). rewrite (Z.mod_mod_divide _ (2^64) 32) by (exists (2^59); reflexivity).
f_equal. lia. }
eapply (LOAD _ _ _ _ _ _ RL).
- replace (ip <=? zlen buf - 7) with true in RL by (symmetry; apply Z.leb_le; lia).
zstep.
pose proof (zero_chk1A m1 msvw tlw nc (ip + 3)) as CK. unfold rd_lstA in CK.
replace (BUF + ip + 3) with (BUF + (ip + 3)) by lia.
eapply CK; [exact INV| lia| lia|]. intros y11 y12.
eapply (LOAD _ _ _ _ _ _ RL). }
destruct Hpc as [-> | ->].
+ zstep. zstep. if_cases B; zify_cond B; [exfalso; lia|]. apply T0.
+ zstep. if_cases B; zify_cond B; [| exfalso; lia]. apply T0.
-
injection RL as <- <-. cbnR.
assert (K24 : ctzv bs < 24) by (subst rep; Z.div_mod_to_equations; lia).
specialize (fun y15 y30 => K y15 y30 Hbs Hip0 Hip4 Hbc ltac:(lia) Erep LT ltac:(repeat split; reflexivity)).
unfold rd_lstA in K |- *.
destruct Hpc as [-> | ->].
+ zstep. zstep. if_cases B; zify_cond B; [| exfalso; lia]. apply K.
+ zstep. if_cases B; zify_cond B; [exfalso; lia|]. zstep. apply K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="rc OK SH RNGS"] Lemma zero_load2A : forall s3 m1 msvw tlw ip' (x6 x10 x11 x12 x14 x15 x19 x30 : word),
rd_invA C m1 (r_nc s3) msvw tlw ->
0 <= ip' -> ip' + 4 <= zlen buf -> 0 <= r_bitCount s3 < 32 ->
r_ip s3 = ip' -> r_bitStream s3 = le32 buf ip' / 2 ^ r_bitCount s3 ->
x10 = Z_to_bv 64 (BUF + ip') -> x6 = Z_to_bv 64 (r_bitCount s3) ->
(forall y12 y14 y15 y19 y30, evtF asegs RNG POST (rd_cntA C s3 m1 y12 y14 y15 y19 y30)) ->
evtF asegs RNG POST (rd_lstA C 0x82174 m1 x6 x10 x11 x12 (Z_to_bv 64 (r_charnum s3)) x14 x15
(Z_to_bv 64 (r_remaining s3)) (Z_to_bv 64 (r_threshold s3)) x19 (Z_to_bv 64 (r_nbBits s3)) x30).
Proof.
intros s3 m1 msvw tlw ip' x6 x10 x11 x12 x14 x15 x19 x30 INV Hip0 Hip4 Hbc Eip Ebs -> -> K.
pose proof RNGS as RNGS0. destruct RNGS0 as (RIq & RSTK & RN & RNS & RM & RMS & RT & RTS & RB & RBS).
destruct (bufmem m1 _ msvw tlw INV) as (UB & MI & HBUF).
Local Ltac2 Set LiaHints.tbl := fun () => "00O0>11447729963.8911447729963.9011447729963.9714533046805.4015534906502.6921481239870.5325995870149.662623057474.76 3132576390.69 35120240342.4240138410406.5343929283712.6744144284019.6844207606616.6854728326447.3855036003867.7555705461570.6956641621271.4458067894962.7658805924860.7059588178608.6759588178609.6661536869752.6863872857902.6866721607490.7667048124130.6967488565603.6868185490472.68731462578.76  7330169908.67 8682883843.68 00000100200300>00?00D00I00J00K00V00[00\00]00^00i01401501@01A01L01M01N01O01Z01[01\01]01^01_01j01kFFFS4Hip04Hip4FS3HbcS3HbcFFS4Hip04Hip4S3HbcFFFS4Hip04Hip4S4Hip04Hip4FS4Hip04Hip4FS4Hip04Hip4SSFS4Hip04Hip4FFFFFS4Hip04Hip4F".
destruct (buf_rdA C OK m1 ip' HBUF ltac:(lia)) as [RD0 R0].
destruct (buf_rdA C OK m1 (ip' + 1) HBUF ltac:(lia)) as [RD1 R1].
destruct (buf_rdA C OK m1 (ip' + 2) HBUF ltac:(lia)) as [RD2 R2].
destruct (buf_rdA C OK m1 (ip' + 3) HBUF ltac:(lia)) as [RD3 R3].
rewrite !Z.add_assoc in RD1, RD2, RD3.
pose proof K as K'. unfold rd_cntA, rd_lstA in K'.
destruct s3 as [nc ip bs bc cn rem thr nb p0]. cbnR. subst ip.
unfold rd_lstA.
zstep. cbv beta. zstep. cbv beta. zstep. cbv beta. zstep. cbv beta.
zstep. zstep. zstep. zstep. zstep. zstep. zstep.
rewrite le32_lb_raw by assumption. rewrite (Z.mod_small bc 32) by lia. rewrite Z.shiftr_div_pow2 by lia.
fold (le32 buf ip'). rewrite <- Ebs.
apply K'.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="rc OK RNGS"] Lemma zrl_chk2 : forall m1 ip' (x6 x11 x12 x13 x14 x15 x16 x17 x19 x23 x30 : word),
unpoisoned m1 BUF (BUF + zlen buf) -> 0 <= ip' -> ip' + 4 <= zlen buf ->
(forall y11 y12 y14, evtF asegs RNG POST (rd_lstA C 0x82174 m1 x6 (Z_to_bv 64 (BUF + ip')) y11 y12 x13 y14 x15 x16 x17 x19 x23 x30)) ->
evtF asegs RNG POST (rd_lstA C 0x82160 m1 x6 (Z_to_bv 64 (BUF + ip')) x11 x12 x13 x14 x15 x16 x17 x19 x23 x30).
Proof.
intros m1 ip' x6 x11 x12 x13 x14 x15 x16 x17 x19 x23 x30 UB P0 P4 K.
destruct RNGS as (RI & RSTK & RN & RNS & RM & RMS & RT & RTS & RB & RBS).
pose proof OK as OK'. destruct OK' as (HH & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & BB & _ & _ & _ & _ & _ & _ & _ & _ & B8).
pose proof (ablk_lin _ _ BB) as LBB. unfold KHIGH, AIMG_HI, KEND in *.
Local Ltac2 Set LiaHints.tbl := fun () => "00:0>14364725201.5919492076177.4333813554636.5035118377592.5035319175708.3936401657513.5336401657515.5249118288140.3959314873579.459446685103.59 00000500A00L00T00X00c00n01201C01MS3SR2S2P03LBB3CK2S2P02P43LBBS2B83LBBS2P4S2P02P43LBBS2P02P43LBBS2P0S2P03LBB3CK21G2G'S3CK21G2H0".
destruct (chkB m1 BUF (BUF + zlen buf) (BUF + ip' + 3) UB ltac:(lia) ltac:(lia)) as (b2 & RDB2 & CK2 & SR2).
unfold rd_lstA in K |- *.
zstep. zstep. zstep. zstep. rewrite sxb_sval.
zstep. if_cases G; zify_cond G.
- zstep. zstep. if_cases G'; zify_lts G'; [| exfalso; lia]. apply K.
- apply K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="rc OK RNGS"] Lemma zrl_chk1 : forall m1 ip' (x6 x11 x12 x13 x14 x15 x16 x17 x19 x23 x30 : word),
unpoisoned m1 BUF (BUF + zlen buf) -> 0 <= ip' -> ip' + 4 <= zlen buf ->
(forall y11 y12, evtF asegs RNG POST (rd_lstA C 0x82160 m1 x6 (Z_to_bv 64 (BUF + ip')) y11 y12 x13 x14 x15 x16 x17 x19 x23 x30)) ->
evtF asegs RNG POST (rd_lstA C 0x82150 m1 x6 (Z_to_bv 64 (BUF + ip')) x11 x12 x13 x14 x15 x16 x17 x19 x23 x30).
Proof.
intros m1 ip' x6 x11 x12 x13 x14 x15 x16 x17 x19 x23 x30 UB P0 P4 K.
destruct RNGS as (RI & RSTK & RN & RNS & RM & RMS & RT & RTS & RB & RBS).
pose proof OK as OK'. destruct OK' as (HH & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & BB & _ & _ & _ & _ & _ & _ & _ & _ & B8).
pose proof (ablk_lin _ _ BB) as LBB. unfold KHIGH, AIMG_HI, KEND in *.
Local Ltac2 Set LiaHints.tbl := fun () => "00:0>33813554636.5034022604115.3934360486178.3935118377592.5039570211675.5953146557993.5253148655143.5959314873579.4564794109999.439446685103.59 00000;00?00C00K00P00[00f01701C01MS2P02P43LBBS2P4S2P0S2B83LBBS3SR1S2P02P43LBBS2P02P43LBBS2P03LBB3CK11G2G'S2P03LBB3CK1S3CK11G2H0".
destruct (chkB m1 BUF (BUF + zlen buf) (BUF + ip') UB ltac:(lia) ltac:(lia)) as (b1 & RDB1 & CK1 & SR1).
unfold rd_lstA in K |- *.
zstep. zstep. zstep. rewrite sxb_sval.
zstep. if_cases G; zify_cond G.
- zstep. zstep. if_cases G'; zify_lts G'; [| exfalso; lia]. apply K.
- apply K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="rc OK RNGS"] Lemma zrl_chk1c : forall m1 (x6 x12 x13 x14 x15 x16 x17 x19 x23 x30 : word),
unpoisoned m1 BUF (BUF + zlen buf) ->
(forall y11 y12, evtF asegs RNG POST (rd_lstA C 0x82160 m1 x6 (Z_to_bv 64 (BUF + zlen buf + -4)) y11 y12 x13 x14 x15 x16 x17 x19 x23 x30)) ->
evtF asegs RNG POST (rd_lstA C 0x82388 m1 x6 (Z_to_bv 64 (BUF + zlen buf + -4)) (Z_to_bv 64 (BUF + zlen buf + -4)) x12 x13 x14 x15 x16 x17 x19 x23 x30).
Proof.
intros m1 x6 x12 x13 x14 x15 x16 x17 x19 x23 x30 UB K.
destruct RNGS as (RI & RSTK & RN & RNS & RM & RMS & RT & RTS & RB & RBS).
pose proof OK as OK'. destruct OK' as (HH & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & BB & _ & _ & _ & _ & _ & _ & _ & _ & B8).
pose proof (ablk_lin _ _ BB) as LBB. unfold KHIGH, AIMG_HI, KEND in *.
Local Ltac2 Set LiaHints.tbl := fun () => "00:0>10990209200.5610992306367.4833813554636.4635118377592.4639570211675.5546153696197.3559314873579.4164794109999.398811860338.35 9446685103.55 00000800@00H00P00U00Y00j01601701AS2HH3LBBS2HH3LBBS2HH3LBBS2B83LBBS3SR1S2HHS2HH3LBB3CK11G2G'S2HH3LBB3CK1SS3CK11G2H0".
destruct (chkB m1 BUF (BUF + zlen buf) (BUF + zlen buf + -4) UB ltac:(lia) ltac:(lia)) as (b1 & RDB1 & CK1 & SR1).
unfold rd_lstA in K |- *.
zstep. zstep. zstep. rewrite sxb_sval.
zstep. if_cases G; zify_cond G.
- apply K.
- zstep. zstep. if_cases G'; zify_lts G'; [| exfalso; lia]. apply K.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="rc OK SH RNGS"] Lemma zero_reloadA : forall s2 s3 m1 msvw tlw (x6 x11 x14 x15 x19 x30 : word),
rd_invA C m1 (r_nc s2) msvw tlw -> reload buf s2 = Ok s3 ->
0 <= r_ip s2 -> r_ip s2 + 4 <= zlen buf -> 0 <= r_bitCount s2 < 64 ->
(forall y12 y14 y15 y19 y30, evtF asegs RNG POST (rd_cntA C s3 m1 y12 y14 y15 y19 y30)) ->
evtF asegs RNG POST (rd_lstA C 0x82140 m1 x6 (Z_to_bv 64 (BUF + r_ip s2)) x11 (Z_to_bv 64 (r_bitCount s2)) (Z_to_bv 64 (r_charnum s2))
x14 x15 (Z_to_bv 64 (r_remaining s2)) (Z_to_bv 64 (r_threshold s2)) x19 (Z_to_bv 64 (r_nbBits s2)) x30).
Proof.
intros s2 s3 m1 msvw tlw x6 x11 x14 x15 x19 x30 INV RL Hip0 Hip4 Hbc K.
pose proof RNGS as RNGS0. destruct RNGS0 as (RIq & RSTK & _). pose proof (okA_lin C OK) as (_ & _ & _ & _ & _ & _ & LOs & LOAs & SPA1 & SPA2 & _). pose proof atop_range as ATR. unfold RDA_CALLEE in LOs.
pose proof (reload_inv buf s2 s3 (buf_all_bytesA C OK) RL Hip0 Hip4 (proj1 Hbc)) as RI. cbv zeta in RI.
destruct RI as (I1 & I2 & I3 & ->).
pose proof OK as OK'. destruct OK' as (HH & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & BB & _ & _ & _ & _ & _ & _ & _ & _ & B8).
pose proof (ablk_lin _ _ BB) as LBB. unfold KHIGH, AIMG_HI, KEND in *.
pose proof INV as INV'. destruct INV' as (_ & _ & _ & _ & _ & (j16 & FRM) & _ & MU & _). unfold FRA_main in FRM.
destruct (inv_shadowA C m1 OK SH MU) as (_ & _ & _ & UB).
destruct s2 as [nc ip bs bc cn rem thr nb p0]. cbnR.
unfold reload_pos in *. unfold FseNCount.Zlength in *.
Local Ltac2 Set LiaHints.tbl := fun () => "00W0>10029754702.5210992306365.6311001195444.5211706759828.5213706453024.4916530564352.5221481521301.4922626797519.5525993772992.5925993772992.6025995870150.7227637725769.6227637725770.6229784644588.4929788724074.5030195467701.5230614832779.5032665485845.513497148261.50 35504068375.5235916362634.6237211491939.6338071471090.5238071471090.5340206209368.5240206209368.5342815240411.524304519847.59 44086960753.6046251409601.6047366385985.5147375192777.6358024162856.5159078035918.5263368379932.4967439684295.5267992669144.5267992669144.538929299744.52 00000400P00l01101601701<01=01B01G01L01V01`01a01b01c01h02D02G02K02L02M02Q02U03303R03[03\03`03d04G04j04n05205305<05=05>05cS2B2S3Hbc3LOs4LOAs3ATR2I32HH3LBBS3Hbc3LOs4LOAs3ATR2I32HH3LBBS3HbcS3HbcSS3HbcSS3HbcS3HbcS3HbcS3LOs4SPA1S3LOs4SPA1SSSS3HbcS3Hbc3LOs4LOAs3ATR2I32HH3LBBS1QS2B1FSS2I2S2B2S4Hip03Hbc3LOs4LOAs3ATR2I33LBBS3Hbc3LOs4LOAs3ATR2I32HH3LBB2B1S4Hip42B1FS2I1S2I2S4Hip04Hip43Hbc3LOs4LOAs3ATR2I33LBBS4Hip04Hip43Hbc3LOs4LOAs3ATR2I33LBBS2B1S2B2SS4Hip42B1SSS4Hip04Hip43Hbc3LOs4LOAs3ATR2I33LBB1Q".
rewrite Z.shiftr_div_pow2 in * by lia. change (2^3) with 8 in *. rewrite land_7, land_31 in *.
assert (Q : 0 <= bc / 8 < 8) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
assert (LOAD : forall ip' bc' (y11 y12 y14 y15 y19 y30 : word),
fst (if (ip <=? zlen buf - 7) || (ip + bc / 8 <=? zlen buf - 4) then (ip + bc / 8, bc mod 8) else (zlen buf - 4, (bc - 8 * (zlen buf - 4 - ip)) mod 32)) = ip' ->
snd (if (ip <=? zlen buf - 7) || (ip + bc / 8 <=? zlen buf - 4) then (ip + bc / 8, bc mod 8) else (zlen buf - 4, (bc - 8 * (zlen buf - 4 - ip)) mod 32)) = bc' ->
evtF asegs RNG POST (rd_lstA C 0x82160 m1 (Z_to_bv 64 bc') (Z_to_bv 64 (BUF + ip')) y11 y12 (Z_to_bv 64 cn) y14 y15
(Z_to_bv 64 rem) (Z_to_bv 64 thr) y19 (Z_to_bv 64 nb) y30)).
{ intros ip' bc' y11 y12 y14 y15 y19 y30 E1 E2. rewrite E1, E2 in *.
eapply (zrl_chk2 m1 ip'); [exact UB| lia| lia|]. intros z11 z12 z14.
eapply (zero_load2A (FseNCount.mkR nc ip' (le32 buf ip' / 2 ^ bc') bc' cn rem thr nb p0) m1 msvw tlw ip');
try eassumption; try reflexivity; cbnR; try lia; try reflexivity. }
clear K. unfold rd_lstA in LOAD |- *.
zstep. rewrite (wrap32_small bc) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
rewrite ?(FseWalkKit.swrap32_small (bc / 8)) by lia.
zstep.
if_cases B1; zify_cond B1.
- zstep. zstep. zstep.
if_cases B2; zify_cond B2.
+ replace ((ip <=? zlen buf - 7) || (ip + bc / 8 <=? zlen buf - 4)) with true in LOAD
by (symmetry; apply orb_true_iff; right; apply Z.leb_le; lia).
zstep. zstep. rewrite land_7.
pose proof (zrl_chk1 m1 (ip + bc / 8)) as CK1. unfold rd_lstA in CK1.
replace (BUF + ip + bc / 8) with (BUF + (ip + bc / 8)) by lia.
eapply CK1; [exact UB| lia| lia|]. intros y11 y12.
eapply (LOAD (ip + bc / 8) (bc mod 8)); reflexivity.
+ replace ((ip <=? zlen buf - 7) || (ip + bc / 8 <=? zlen buf - 4)) with false in LOAD
by (symmetry; apply orb_false_iff; split; apply Z.leb_gt; lia).
zstep. zstep.
replace (BUF + ip - (BUF + zlen buf + -4)) with (ip - zlen buf + 4) by lia.
rewrite ?(FseWalkKit.swrap32_small (ip - zlen buf + 4)) by lia.
zstep. zstep. zstep.
rewrite ?(Z.add_comm _ bc). rewrite (clamp_bc bc (ip - zlen buf + 4)) by lia.
replace (bc + 8 * (ip - zlen buf + 4)) with (bc - 8 * (zlen buf - 4 - ip)) by lia.
zstep.
pose proof (zrl_chk1c m1) as CK1. unfold rd_lstA in CK1.
eapply CK1; [exact UB|]. intros y11 y12.
replace (BUF + zlen buf + -4) with (BUF + (zlen buf - 4)) by lia.
eapply (LOAD (zlen buf - 4) ((bc - 8 * (zlen buf - 4 - ip)) mod 32)); reflexivity.
- replace ((ip <=? zlen buf - 7) || (ip + bc / 8 <=? zlen buf - 4)) with true in LOAD, I2
by (symmetry; apply orb_true_iff; left; apply Z.leb_le; lia). cbn [fst] in I2.
zstep. zstep. rewrite land_7.
pose proof (zrl_chk1 m1 (ip + bc / 8)) as CK1. unfold rd_lstA in CK1.
replace (BUF + ip + bc / 8) with (BUF + (ip + bc / 8)) by lia.
eapply CK1; [exact UB| lia| lia|]. intros y11 y12.
eapply (LOAD (ip + bc / 8) (bc mod 8)); reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="rc OK SH RNGS"] Lemma zero_tailA : forall s1 m1 msvw tlw fl (x15 x19 x30 : word),
rd_invA C m1 (r_nc s1) msvw tlw ->
0 <= r_bitStream s1 < 2^32 -> 0 <= r_ip s1 -> r_ip s1 + 4 <= zlen buf -> 0 <= r_bitCount s1 < 32 ->
0 <= r_charnum s1 <= 2^30 -> ctzv (r_bitStream s1) / 2 < 12 -> 0 <= r_remaining s1 < 2^31 ->
(let rep1 := ctzv (r_bitStream s1) / 2 in
let! bs := shr32 (r_bitStream s1) (2 * rep1) in
let s2 := FseNCount.mkR (r_nc s1) (r_ip s1) bs (r_bitCount s1 + 2 * rep1 + 2) (r_charnum s1 + 3 * rep1 + Z.land bs 3)
(r_remaining s1) (r_threshold s1) (r_nbBits s1) (r_previous0 s1) in
if msv1 <=? r_charnum s1 + 3 * rep1 + Z.land bs 3 then Ok (Brk s2) else let! s3 := reload buf s2 in Ok (Cont s3)) = Ok fl ->
(forall s' y6 y11 y14 y15 y17 y19 y23 y30, fl = Brk s' -> r_nc s' = r_nc s1 -> rd_brk_okA C s' ->
evtF asegs RNG POST (rd_exitA C s' m1 y6 y11 y14 y15 y17 y19 y23 y30)) ->
(forall s' y12 y14 y15 y19 y30, fl = Cont s' -> r_nc s' = r_nc s1 -> evtF asegs RNG POST (rd_cntA C s' m1 y12 y14 y15 y19 y30)) ->
evtF asegs RNG POST (rd_lstA C 0x82114 m1 (Z_to_bv 64 (r_bitCount s1)) (Z_to_bv 64 (BUF + r_ip s1)) (Z_to_bv 64 (bv_swrap 32 (r_bitStream s1)))
(Z_to_bv 64 (ctzv (r_bitStream s1))) (Z_to_bv 64 (r_charnum s1)) (Z_to_bv 64 ADB_TAB) x15
(Z_to_bv 64 (r_remaining s1)) (Z_to_bv 64 (r_threshold s1)) x19 (Z_to_bv 64 (r_nbBits s1)) x30).
Proof.
intros s1 m1 msvw tlw fl x15 x19 x30 INV Hbs Hip0 Hip4 Hbc Hcn Hrep Hrem RR KB KC.
pose proof OK as OK'. destruct OK' as (HH & _ & HM0 & _).
pose proof (ctzv_range _ Hbs) as Rk.
destruct s1 as [nc ip bs bc cn rem thr nb p0]. cbnR. cbv zeta in RR.
set (k := ctzv bs) in *. set (rep := k / 2) in *.
Local Ltac2 Set LiaHints.tbl := fun () => "00S0>101305884.46  10434093890.4612617000806.5616911362127.5317709097045.5718459507901.5718461605045.5918461605046.6819615514370.4819622043024.4723746375204.4625041511207.462505950386.46 2509909495.40 27396979568.5427519251445.5729890292957.5429890420804.4830439707575.4633257856505.4835589194279.4336400373101.4640829896556.4246950398903.4747130424411.5447130556610.4855707291962.5655903789380.4655916873729.4056428502567.5359060989939.4759251310730.438337467334.40 8931407120.47 9120371982.45 00000A00n01>01?01H01L01P01T01U01Z01n02402A02J02[02\02b02h02i03:03=03>03?03B03H03N03O03\03e04504804<04A04Q04_S3Hbs3Hbc2Rk4RrepS3Hbs4Hip04Hip43Hbc3Hcn4Hrem3HM02Rk4Rrep2L31BS3Hcn2Rk4Rrep2M1FS2Rk4RrepS2RkS2RkS2RkFS3HM0S3Hbs3Hcn2Rk4Rrep2L3S4Rbs2S3Hbs2Rk4RrepS2Rk4RrepS3Hbs3Hbc2Rk4RrepFS4Hip0S4Hip0SS3Hbs3Hbc2Rk4RrepS1HSSS1BS4Hip4S4Hip4SS3Hbs2Rk4RrepS2Rk4RrepS3Hbc2Rk4Rrep2M1S1BS2RkS3HbsS3Hcn2Rk4Rrep2L3S4Hrep2Rk1H2H0".
assert (Rrep : 0 <= rep <= 11 /\ 2 * rep <= k <= 2 * rep + 1) by (subst rep; Z.div_mod_to_equations; lia).
rewrite shr32_ok in RR by lia. cbn [bind] in RR.
set (bs2 := bs / 2 ^ (2 * rep)) in *.
assert (Rbs2 : 0 <= bs2 < 2^32) by (subst bs2; apply shr_range; lia).
assert (L3 : 0 <= Z.land bs2 3 <= 3) by (rewrite land_3; pose proof (Z.mod_pos_bound bs2 4 ltac:(lia)); lia).
change (2^30) with 1073741824 in *. change (2^31) with 2147483648 in *.
unfold rd_lstA.
destruct (ctz_masks k ltac:(lia)) as (M1 & M2 & M3). fold rep in M1, M2, M3.
zstep. rewrite M1. zstep. rewrite M2. zstep. rewrite M3.
zstep.
zstep. rewrite (wrap32_swrap32_u32 bs Hbs). rewrite (Z.mod_small (2 * rep) 32) by lia.
rewrite Z.shiftr_div_pow2 by lia. fold bs2.
zstep.
zstep. rewrite (land_swrap32 bs2 3) by lia.
zstep. rewrite ?(FseWalkKit.swrap32_small (2 * rep + rep + cn + Z.land bs2 3)) by lia.
replace (2 * rep + rep + cn + Z.land bs2 3) with (cn + 3 * rep + Z.land bs2 3) by lia.
zstep. zstep. rewrite ?(FseWalkKit.swrap32_small (bc + 2 * rep + 2)) by lia.
zstep.
if_cases B; zify_cond B.
-
replace (msv1 <=? cn + 3 * rep + Z.land bs2 3) with true in RR by (symmetry; apply Z.leb_le; lia).
injection RR as <-.
pose proof (KB (FseNCount.mkR nc ip bs2 (bc + 2 * rep + 2) (cn + 3 * rep + Z.land bs2 3) rem thr nb p0)) as KB'.
unfold rd_exitA, rd_lstA in KB'. cbnR.
eapply KB'; [reflexivity| reflexivity|]. unfold rd_brk_okA. cbnR. change (2^31) with 2147483648. lia.
- replace (msv1 <=? cn + 3 * rep + Z.land bs2 3) with false in RR by (symmetry; apply Z.leb_gt; lia).
destruct (reload buf (FseNCount.mkR nc ip bs2 (bc + 2 * rep + 2) (cn + 3 * rep + Z.land bs2 3) rem thr nb p0)) as [s3| | |] eqn:RL;
cbn [bind] in RR; try discriminate RR. injection RR as <-.
pose proof (fun y6 y11 y14 y15 y19 y30 => zero_reloadA (FseNCount.mkR nc ip bs2 (bc + 2 * rep + 2) (cn + 3 * rep + Z.land bs2 3) rem thr nb p0)
s3 m1 msvw tlw y6 y11 y14 y15 y19 y30 INV RL) as ZR. cbnR. unfold rd_lstA in ZR.
eapply ZR; try lia.
intros y12 y14 y15 y19 y30. apply KC; [reflexivity|].
pose proof (reload_inv buf _ s3 (buf_all_bytesA C OK) RL) as RI. cbnR. cbv zeta in RI.
destruct (RI ltac:(lia) ltac:(unfold FseNCount.Zlength; lia) ltac:(lia)) as (_ & _ & _ & ->). reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="rc OK SH RNGS"] Lemma zero_runA : forall tl s m1 msvw tlw fl (x12 x14 x15 x19 x30 : word),
5 <= tl <= 15 ->
rd_invA C m1 (r_nc s) msvw tlw -> CTL msv1 (a_rt0 C) tl s -> POS buf s -> r_bitCount s < 32 ->
rzero_block buf msv1 s = Ok fl ->
(forall s' y6 y11 y14 y15 y17 y19 y23 y30, fl = Brk s' -> r_nc s' = r_nc s -> rd_brk_okA C s' ->
evtF asegs RNG POST (rd_exitA C s' m1 y6 y11 y14 y15 y17 y19 y23 y30)) ->
(forall s' y12 y14 y15 y19 y30, fl = Cont s' -> r_nc s' = r_nc s -> evtF asegs RNG POST (rd_cntA C s' m1 y12 y14 y15 y19 y30)) ->
evtF asegs RNG POST (rd_lstA C 0x82024 m1 (Z_to_bv 64 (r_bitCount s)) (Z_to_bv 64 (BUF + r_ip s)) (Z_to_bv 64 (bv_swrap 32 (r_bitStream s)))
x12 (Z_to_bv 64 (r_charnum s)) x14 x15 (Z_to_bv 64 (r_remaining s)) (Z_to_bv 64 (r_threshold s)) x19
(Z_to_bv 64 (r_nbBits s)) x30).
Proof.
intros tl s m1 msvw tlw fl x12 x14 x15 x19 x30 Htl INV HC HP HB32 RR KB KC.
destruct (ctl_pos_ranges _ _ _ _ _ Htl HC HP) as (Rnb & Ethr & Rthr & Rrem & Rrem2 & Rcn & Lnc & Rip & Rip4 & Rbc & Rbs).
pose proof OK as OK'. destruct OK' as (HH & _ & HM0 & _).
unfold rzero_block in RR. rewrite (repeats_of_ctzv _ Rbs) in RR. cbn [bind] in RR.
destruct (rep_loop buf (S (Z.to_nat (FseNCount.Zlength buf))) s (ctzv (r_bitStream s) / 2)) as [[s1 rep1]| | |] eqn:RLP;
cbn [bind] in RR; try discriminate RR.
pose proof (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))))))) as MI.
eapply zero_ctz1A; [exact Rbs| exact MI|].
Local Ltac2 Set LiaHints.tbl := fun () => "00?0>15344331748.4319615265691.4319615387047.5724211034668.4324437530141.4324820138745.4334110585782.433469311006.57 3741032461.43 38997301646.4342546463553.5751210636862.4362941476274.4365711610522.577406823177.57 00000>00?00@00E00N00O00\00]00b01601R01\01d02902:S4HB323Lnc3RbcFFS3LncS3Lnc3RbsFS3Lnc3Rip3RcnFS3LncS3Rnb3Rcn3Lnc2HH3HM0S3Rnb4Rthr4Rrem5Rrem23Lnc2E2S3Lnc4Rip4S3Lnc2HHS3Rnb3Lnc5Erep15Hrep1F".
eapply (zero_repA _ s _ s1 rep1 m1 msvw tlw 0x8204c); try exact RLP; try exact INV; try lia; try reflexivity.
{ unfold FseNCount.Zlength. change (2^30) with 1073741824. rewrite Nat2Z.inj_succ, Z2Nat.id by lia. lia. }
intros z15 z30 Hbs1 Hip0 Hip4 Hbc1 Hcn1 Erep1 Hrep1 (E1 & E2 & E3 & E4 & E5).
rewrite <- E2, <- E3, <- E4.
eapply (zero_tailA s1 m1 msvw tlw fl); try eassumption; try lia.
- rewrite E1. exact INV.
- cbv zeta. rewrite <- Erep1. exact RR.
- intros s' y6 y11 y14 y15 y17 y19 y23 y30 EF EN BK. apply KB; [exact EF| rewrite EN; exact E1| exact BK].
- intros s' y12 y14 y15 y19 y30 EF EN. apply KC; [exact EF| rewrite EN; exact E1].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End Zero.
End CANSEC1.
