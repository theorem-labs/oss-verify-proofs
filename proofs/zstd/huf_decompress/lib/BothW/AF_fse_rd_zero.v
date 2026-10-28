(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas FseReadSound.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Arr Bytes ZBridge Image.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseRdKit FseRdKit2 BoFseRdKit3.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg ABase RtCells AF_fse_rd_base.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKitF.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_enrich ::= rewrite ?shad_div in *; rewrite ?nshad_div in *; unfold ASHOFF, KLOW, KHIGH, KEND in *; rewrite ?Z.shiftr_div_pow2 in * by lia.
Local Ltac acc_hint ::= rdA_acc_hint.
Section CANSEC1. Context {rc : runConstT}.
Definition ADB_TAB : Z := 134749.
#[using="Type"] Lemma tab_rdA : forall m1 i, mem_inv bsegs m1 -> 0 <= i < 32 ->
ov_read_bytes bsegs m1 (Z_to_bv 64 (ADB_TAB + i)) 1 = Some [Z_to_bv 8 (nth (Z.to_nat i) DB_TABLE 0)].
Proof.
intros m1 i MI Hi.
assert (RO : ro_cells bsegs m1 ADB_TAB [CB 32 (map (Z_to_bv 8) DB_TABLE)]).
{
apply (ro_cells_image bsegs m1 ADB_TAB (map (Z_to_bv 8) DB_TABLE) MI); [vm_compute; reflexivity| unfold ADB_TAB; lia| cbn; unfold ADB_TAB; lia]. }
destruct RO as [_ BA]. cbn [cells_bytes cbytes] in BA. rewrite app_nil_r in BA.
eapply (u8ro_read bsegs m1 ADB_TAB _ i); [exact BA| | lia| unfold wa; f_equal; lia].
rewrite nth_error_map. rewrite (nth_error_nth' DB_TABLE 0) by (cbn; lia). reflexivity.
Qed.
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
unpoisoned m1 BUF (BUF + zlen buf) /\ mem_inv bsegs m1 /\ bytes_at bsegs m1 BUF (map (Z_to_bv 8) buf).
Proof.
intros m1 nc msvw tlw (_ & _ & HB & _ & _ & _ & _ & MU & _ & MI).
destruct (inv_shadowA C m1 OK SH MU) as (_ & _ & _ & UB). auto.
Qed.
#[using="RNGS"] Lemma zero_ctz1A : forall bs m1 (x1 x7 x10 x11 x12 x13 x16 x18 x20 x22 x29 : word),
0 <= bs < 2^32 -> mem_inv bsegs m1 ->
(forall y29, evtF bsegs RNG POST (rd_lstA C 0x96d20 m1 x1 (Z_to_bv 64 (bv_swrap 32 bs)) x7 x10 x11 (Z_to_bv 64 (ctzv bs)) x13 x16 x18 x20
(Z_to_bv 64 ADB_TAB) y29)) ->
evtF bsegs RNG POST (rd_lstA C 0x96cf8 m1 x1 (Z_to_bv 64 (bv_swrap 32 bs)) x7 x10 x11 x12 x13 x16 x18 x20 x22 x29).
Proof.
intros bs m1 x1 x7 x10 x11 x12 x13 x16 x18 x20 x22 x29 Hbs MI K.
pose proof RNGS as RNGS'. destruct RNGS' as (RI & _).
pose proof (ctzv_range bs Hbs) as Rk.
destruct (db_table_ok (ctzv bs) ltac:(lia)) as [Ri Et].
pose proof (tab_rdA m1 (db_idx (ctzv bs)) MI Ri) as RD. rewrite Et in RD. unfold ADB_TAB in *.
unfold rd_lstA in *.
do 9 zstep.
rewrite (ctz_index_form bs Hbs).
zstep. cbv beta. rewrite byte_lit by lia.
apply K.
Qed.
#[using="rc OK SH RNGS"] Lemma zero_load1A : forall m1 msvw tlw nc ip' bc' cn (x1 x6 x7 x11 x12 x18 x20 x29 : word),
rd_invA C m1 nc msvw tlw -> 0 <= ip' -> ip' + 4 <= zlen buf -> 0 <= bc' < 32 -> 0 <= cn < 2^31 ->
(forall (y20 y29 : word), evtF bsegs RNG POST (rd_lstA C 0x96db0 m1 x1 (Z_to_bv 64 (bv_swrap 32 (le32 buf ip' / 2 ^ bc'))) x7
(Z_to_bv 64 (BUF + ip')) x11 (Z_to_bv 64 (ctzv (le32 buf ip' / 2 ^ bc'))) (Z_to_bv 64 (cn + 36))
(Z_to_bv 64 bc') x18 y20 (Z_to_bv 64 ADB_TAB) y29)) ->
evtF bsegs RNG POST (rd_lstA C 0x96d4c m1 x1 x6 x7 (Z_to_bv 64 (BUF + ip')) x11 x12 (Z_to_bv 64 cn) (Z_to_bv 64 bc') x18 x20
(Z_to_bv 64 ADB_TAB) x29).
Proof.
intros m1 msvw tlw nc ip' bc' cn x1 x6 x7 x11 x12 x18 x20 x29 INV Hip0 Hip4 Hbc Hcn K.
destruct (bufmem m1 nc msvw tlw INV) as (UB & MI & HBUF).
destruct RNGS as (RI & RSTK & RN & RNS & RM & RMS & RT & RTS & RB & RBS).
pose proof OK as OK'. destruct OK' as (HH & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & BB & _ & _ & _ & _ & _ & _ & _ & _ & B8).
pose proof (ablk_lin _ _ BB) as LBB. unfold KHIGH, AIMG_HI, KEND in *.
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
assert (LD : forall (y6 y12 y29 : word),
evtF bsegs RNG POST (rd_lstA C 0x96d60 m1 x1 y6 x7 (Z_to_bv 64 (BUF + ip')) x11 y12 (Z_to_bv 64 cn) (Z_to_bv 64 bc') x18 x20
(Z_to_bv 64 134749) y29)).
{ intros y6 y12 y29. clear RDB2 CK2 SR2. unfold rd_lstA in K |- *.
zstep. cbv beta. zstep. cbv beta. zstep. cbv beta. zstep. cbv beta.
zstep. zstep. zstep. zstep. zstep. zstep.
zstep.
rewrite le32_lb_raw by assumption. rewrite (Z.mod_small bc' 32) by lia. rewrite (Z.shiftr_div_pow2 _ bc') by lia.
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
Qed.
#[using="rc OK SH RNGS"] Lemma zero_chk1A : forall m1 msvw tlw nc ip' (x1 x6 x7 x11 x12 x13 x16 x18 x20 x29 : word),
rd_invA C m1 nc msvw tlw -> 0 <= ip' -> ip' + 4 <= zlen buf ->
(forall y6 y12, evtF bsegs RNG POST (rd_lstA C 0x96d4c m1 x1 y6 x7 (Z_to_bv 64 (BUF + ip')) x11 y12 x13 x16 x18 x20 (Z_to_bv 64 ADB_TAB) x29)) ->
evtF bsegs RNG POST (rd_lstA C 0x96d3c m1 x1 x6 x7 (Z_to_bv 64 (BUF + ip')) x11 x12 x13 x16 x18 x20 (Z_to_bv 64 ADB_TAB) x29).
Proof.
intros m1 msvw tlw nc ip' x1 x6 x7 x11 x12 x13 x16 x18 x20 x29 INV P0 P4 K.
destruct (bufmem m1 nc msvw tlw INV) as (UB & MI & HBUF).
destruct RNGS as (RI & RSTK & RN & RNS & RM & RMS & RT & RTS & RB & RBS).
pose proof OK as OK'. destruct OK' as (HH & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & BB & _ & _ & _ & _ & _ & _ & _ & _ & B8).
pose proof (ablk_lin _ _ BB) as LBB. unfold KHIGH, AIMG_HI, KEND in *.
destruct (chkB m1 BUF (BUF + zlen buf) (BUF + ip') UB ltac:(lia) ltac:(lia)) as (b1 & RDB1 & CK1 & SR1).
unfold rd_lstA in K |- *.
zstep. zstep. zstep. rewrite sxb_sval.
zstep. if_cases G; zify_cond G.
- zstep. zstep. if_cases G'; zify_lts G'; [| exfalso; lia]. apply K.
- apply K.
Qed.
#[using="rc OK SH RNGS"] Lemma zero_chk1cA : forall m1 msvw tlw nc (x1 x6 x7 x11 x12 x13 x16 x18 x20 x29 : word),
rd_invA C m1 nc msvw tlw ->
(forall y6 y12, evtF bsegs RNG POST (rd_lstA C 0x96d4c m1 x1 y6 x7 (Z_to_bv 64 (BUF + zlen buf + -4)) x11 y12 x13 x16 x18 x20 (Z_to_bv 64 ADB_TAB) x29)) ->
evtF bsegs RNG POST (rd_lstA C 0x96de8 m1 x1 x6 x7 (Z_to_bv 64 (BUF + zlen buf + -4)) x11 x12 x13 x16 x18 x20 (Z_to_bv 64 ADB_TAB) x29).
Proof.
intros m1 msvw tlw nc x1 x6 x7 x11 x12 x13 x16 x18 x20 x29 INV K.
destruct (bufmem m1 nc msvw tlw INV) as (UB & MI & HBUF).
destruct RNGS as (RI & RSTK & RN & RNS & RM & RMS & RT & RTS & RB & RBS).
pose proof OK as OK'. destruct OK' as (HH & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & BB & _ & _ & _ & _ & _ & _ & _ & _ & B8).
pose proof (ablk_lin _ _ BB) as LBB. unfold KHIGH, AIMG_HI, KEND in *.
destruct (chkB m1 BUF (BUF + zlen buf) (BUF + zlen buf + -4) UB ltac:(lia) ltac:(lia)) as (b1 & RDB1 & CK1 & SR1).
unfold rd_lstA in K |- *.
zstep. zstep. zstep. rewrite sxb_sval.
zstep. if_cases G; zify_cond G.
- apply K.
- zstep. zstep. if_cases G'; zify_lts G'; [| exfalso; lia]. apply K.
Qed.
#[using="rc OK SH RNGS"] Lemma zero_repA : forall f s rep s1 rep1 m1 msvw tlw pc (x1 x7 x11 x18 x20 x29 : word),
rep_loop buf f s rep = Ok (s1, rep1) ->
rd_invA C m1 (r_nc s) msvw tlw ->
0 <= r_bitStream s < 2^32 -> 0 <= r_ip s -> r_ip s + 4 <= zlen buf -> 0 <= r_bitCount s < 32 ->
0 <= r_charnum s -> r_charnum s + 36 * Z.of_nat f <= 2^30 ->
rep = ctzv (r_bitStream s) / 2 ->
(pc = 0x96d20 \/ pc = 0x96db0) ->
(forall y7 y20 y29,
0 <= r_bitStream s1 < 2^32 -> 0 <= r_ip s1 -> r_ip s1 + 4 <= zlen buf -> 0 <= r_bitCount s1 < 32 ->
0 <= r_charnum s1 <= 2^30 -> rep1 = ctzv (r_bitStream s1) / 2 -> rep1 < 12 ->
r_nc s1 = r_nc s /\ r_remaining s1 = r_remaining s /\ r_threshold s1 = r_threshold s /\ r_nbBits s1 = r_nbBits s /\ r_previous0 s1 = r_previous0 s ->
evtF bsegs RNG POST (rd_lstA C 0x96e10 m1 x1 (Z_to_bv 64 (bv_swrap 32 (r_bitStream s1))) y7 (Z_to_bv 64 (BUF + r_ip s1)) x11
(Z_to_bv 64 (ctzv (r_bitStream s1))) (Z_to_bv 64 (r_charnum s1)) (Z_to_bv 64 (r_bitCount s1)) x18 y20
(Z_to_bv 64 ADB_TAB) y29)) ->
evtF bsegs RNG POST (rd_lstA C pc m1 x1 (Z_to_bv 64 (bv_swrap 32 (r_bitStream s))) x7 (Z_to_bv 64 (BUF + r_ip s)) x11
(Z_to_bv 64 (ctzv (r_bitStream s))) (Z_to_bv 64 (r_charnum s)) (Z_to_bv 64 (r_bitCount s)) x18 x20
(Z_to_bv 64 ADB_TAB) x29).
Proof.
induction f as [|f IH]; intros s rep s1 rep1 m1 msvw tlw pc x1 x7 x11 x18 x20 x29 RL INV Hbs Hip0 Hip4 Hbc Hcn0 Hcn Erep Hpc K.
{ cbn in RL. discriminate RL. }
pose proof RNGS as RNGS0. destruct RNGS0 as (RIq & RSTK & _). pose proof (okA_lin C OK) as (_ & _ & _ & _ & _ & _ & LOs & LOAs & SPA1 & SPA2 & _). pose proof atop_range as ATR. unfold RDA_CALLEE in LOs.
pose proof OK as OK'. destruct OK' as (HH & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & BB & _ & _ & _ & _ & _ & _ & _ & _ & B8).
pose proof (ablk_lin _ _ BB) as LBB. unfold KHIGH, AIMG_HI, KEND in *.
pose proof INV as INV'. destruct INV' as (_ & _ & _ & _ & _ & (j0 & j64 & FRM) & _). unfold FRA_main in FRM.
pose proof (ctzv_range _ Hbs) as Rk.
cbn [rep_loop] in RL.
destruct s as [nc ip bs bc cn rem thr nb p0]. cbnR.
change (2^30) with 1073741824 in *. rewrite Nat2Z.inj_succ in Hcn.
destruct (Z.leb_spec 12 rep) as [GE|LT].
-
assert (K24 : 24 <= ctzv bs) by (subst rep; Z.div_mod_to_equations; lia).
unfold FseNCount.Zlength in RL.
assert (LOAD : forall ip' bc' (y6 y7 y12 y20 y29 : word),
(let! w := readLE32 buf ip' in let! bs0 := shr32 w bc' in let! repeats' := repeats_of bs0 in
rep_loop buf f (FseNCount.mkR nc ip' bs0 bc' (cn + 3 * 12) rem thr nb p0) repeats') = Ok (s1, rep1) ->
evtF bsegs RNG POST (rd_lstA C 0x96d4c m1 x1 y6 y7 (Z_to_bv 64 (BUF + ip')) x11 y12 (Z_to_bv 64 cn) (Z_to_bv 64 bc') x18 y20
(Z_to_bv 64 ADB_TAB) y29)).
{ intros ip' bc' y6 y7 y12 y20 y29 RL'.
destruct (readLE32 buf ip') as [w| | |] eqn:ER; cbn [bind] in RL'; try discriminate RL'.
destruct (shr32 w bc') as [bs'| | |] eqn:ES; cbn [bind] in RL'; try discriminate RL'.
destruct (repeats_of bs') as [rep'| | |] eqn:EP; cbn [bind] in RL'; try discriminate RL'.
destruct (readLE32_inv _ _ _ ER) as (I1 & I2 & ->). destruct (shr32_inv _ _ _ ES) as (I3 & ->).
assert (Rbs' : 0 <= le32 buf ip' / 2 ^ bc' < 2^32) by (apply shr_range; [apply le32_range; apply (buf_all_bytesA C OK)| lia]).
rewrite (repeats_of_ctzv _ Rbs') in EP. injection EP as <-.
eapply (zero_load1A m1 msvw tlw nc ip' bc' cn); try eassumption; try lia.
intros z20 z29.
eapply (IH (FseNCount.mkR nc ip' (le32 buf ip' / 2 ^ bc') bc' (cn + 3 * 12) rem thr nb p0) _ s1 rep1 m1 msvw tlw 0x96db0);
cbnR; try eassumption; try reflexivity; try lia.
all: intros y7' y20' y29' H1 H2 H3 H4 H5 H6 H7 H8; apply K; assumption. }
clear IH K.
assert (T0 : forall (y7 y12 : word), evtF bsegs RNG POST
(rd_lstA C 0x96d30 m1 x1 (Z_to_bv 64 (bv_swrap 32 bs)) y7 (Z_to_bv 64 (BUF + ip)) x11 y12
(Z_to_bv 64 cn) (Z_to_bv 64 bc) x18 x20 (Z_to_bv 64 ADB_TAB) x29)).
{ intros y7 y12. unfold rd_lstA in LOAD |- *. zstep.
if_cases B; zify_cond B.
-
replace (ip <=? zlen buf - 7) with false in RL by (symmetry; apply Z.leb_gt; lia).
zstep. replace (BUF + zlen buf + -7 - (BUF + ip)) with (zlen buf - 7 - ip) by lia.
set (d := zlen buf - 7 - ip) in *. assert (Rd : -3 <= d <= -1) by (subst d; lia).
zstep. zstep. zstep. zstep.
replace ((d + 1152921504606846976) ≫ 61) with 0
by (rewrite Z.shiftr_div_pow2 by lia; symmetry; apply Z.div_small; change (2^61) with 2305843009213693952; lia).
zstep. if_false.
zstep. rewrite (slliw3_neg d) by lia.
zstep. zstep. rewrite (subw_mod64 bc (8 * d)) by lia. rewrite (sub_mod64_word bc (8 * d)).
zstep. if_false.
zstep. zstep.
pose proof (zero_chk1cA m1 msvw tlw nc) as CK. unfold rd_lstA in CK.
eapply CK; [exact INV|]. intros z6 z12.
replace (BUF + zlen buf + -4) with (BUF + (zlen buf - 4)) by lia.
eapply (LOAD _ _ _ _ _ _ _ RL).
- replace (ip <=? zlen buf - 7) with true in RL by (symmetry; apply Z.leb_le; lia).
zstep.
zstep. if_cases G; zify_cond G; [exfalso; lia|].
pose proof (zero_chk1A m1 msvw tlw nc (ip + 3)) as CK. unfold rd_lstA in CK.
replace (BUF + ip + 3) with (BUF + (ip + 3)) by lia.
eapply CK; [exact INV| lia| lia|]. intros z6 z12.
eapply (LOAD _ _ _ _ _ _ _ RL). }
unfold rd_lstA in T0 |- *.
destruct Hpc as [-> | ->].
+ zstep. zstep. if_cases B; zify_cond B; [exfalso; lia|].
zstep. zstep. if_cases G; zify_cond G; [exfalso; lia|]. apply T0.
+ zstep. if_cases B; zify_cond B; [| exfalso; lia]. apply T0.
-
injection RL as <- <-. cbnR.
assert (K24 : ctzv bs < 24) by (subst rep; Z.div_mod_to_equations; lia).
specialize (fun y7 y20 y29 => K y7 y20 y29 Hbs Hip0 Hip4 Hbc ltac:(lia) Erep LT ltac:(repeat split; reflexivity)).
unfold rd_lstA in K |- *.
destruct Hpc as [-> | ->].
+ zstep. zstep. if_cases B; zify_cond B; [| exfalso; lia]. apply K.
+ zstep. if_cases B; zify_cond B; [exfalso; lia|]. zstep. apply K.
Qed.
#[using="rc OK SH RNGS"] Lemma zero_load2A : forall s3 m1 msvw tlw ip' (x6 x7 x10 x20 x22 x29 : word),
rd_invA C m1 (r_nc s3) msvw tlw ->
0 <= ip' -> ip' + 4 <= zlen buf -> 0 <= r_bitCount s3 < 32 ->
r_ip s3 = ip' -> r_bitStream s3 = le32 buf ip' / 2 ^ r_bitCount s3 ->
2 <= r_threshold s3 <= 32768 -> r_threshold s3 <= r_remaining s3 < 2 * r_threshold s3 ->
(forall y7 y10 y22, evtF bsegs RNG POST (rd_cntA C s3 m1 y7 y10 y22)) ->
evtF bsegs RNG POST (rd_lstA C 0x96e80 m1 (Z_to_bv 64 (r_nbBits s3)) x6 x7 x10 (Z_to_bv 64 (r_remaining s3)) (Z_to_bv 64 (BUF + ip'))
(Z_to_bv 64 (r_charnum s3)) (Z_to_bv 64 (r_bitCount s3)) (Z_to_bv 64 (r_threshold s3)) x20 x22 x29).
Proof.
intros s3 m1 msvw tlw ip' x6 x7 x10 x20 x22 x29 INV Hip0 Hip4 Hbc Eip Ebs Hthr Hrem K.
pose proof RNGS as RNGS0. destruct RNGS0 as (RIq & RSTK & RN & RNS & RM & RMS & RT & RTS & RB & RBS).
destruct (bufmem m1 _ msvw tlw INV) as (UB & MI & HBUF).
destruct (buf_rdA C OK m1 ip' HBUF ltac:(lia)) as [RD0 R0].
destruct (buf_rdA C OK m1 (ip' + 1) HBUF ltac:(lia)) as [RD1 R1].
destruct (buf_rdA C OK m1 (ip' + 2) HBUF ltac:(lia)) as [RD2 R2].
destruct (buf_rdA C OK m1 (ip' + 3) HBUF ltac:(lia)) as [RD3 R3].
rewrite !Z.add_assoc in RD1, RD2, RD3.
pose proof K as K'. unfold rd_cntA, rd_lstA in K'.
destruct s3 as [nc ip bs bc cn rem thr nb p0]. cbnR. subst ip.
unfold rd_lstA.
zstep. zstep. rewrite (FseWalkKit.swrap32_small (thr + 1073741824)) by lia.
zstep. if_cases G; zify_lts G; [exfalso; lia|].
zstep. cbv beta. zstep. cbv beta. zstep. cbv beta. zstep. cbv beta.
zstep. zstep. zstep. zstep. zstep. zstep. zstep.
rewrite le32_lb_raw by assumption. rewrite (Z.mod_small bc 32) by lia. rewrite (Z.shiftr_div_pow2 _ bc) by lia.
fold (le32 buf ip'). rewrite <- Ebs.
zstep. rewrite Z.shiftl_mul_pow2 by lia. change (2^1) with 2.
zstep. rewrite (FseWalkKit.swrap32_small (thr * 2 + -1)) by lia.
zstep. zstep. rewrite (FseWalkKit.swrap32_small (thr * 2 + -1 - rem)) by lia.
zstep. if_false.
apply K'.
Qed.
#[using="rc OK RNGS"] Lemma zrl_chk2 : forall m1 ip' (x1 x6 x7 x10 x11 x13 x16 x18 x20 x22 x29 : word),
unpoisoned m1 BUF (BUF + zlen buf) -> 0 <= ip' -> ip' + 4 <= zlen buf ->
(forall y6 y10 y29, evtF bsegs RNG POST (rd_lstA C 0x96e80 m1 x1 y6 x7 y10 x11 (Z_to_bv 64 (BUF + ip')) x13 x16 x18 x20 x22 y29)) ->
evtF bsegs RNG POST (rd_lstA C 0x96e6c m1 x1 x6 x7 x10 x11 (Z_to_bv 64 (BUF + ip')) x13 x16 x18 x20 x22 x29).
Proof.
intros m1 ip' x1 x6 x7 x10 x11 x13 x16 x18 x20 x22 x29 UB P0 P4 K.
destruct RNGS as (RI & RSTK & RN & RNS & RM & RMS & RT & RTS & RB & RBS).
pose proof OK as OK'. destruct OK' as (HH & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & BB & _ & _ & _ & _ & _ & _ & _ & _ & B8).
pose proof (ablk_lin _ _ BB) as LBB. unfold KHIGH, AIMG_HI, KEND in *.
destruct (chkB m1 BUF (BUF + zlen buf) (BUF + ip' + 3) UB ltac:(lia) ltac:(lia)) as (b2 & RDB2 & CK2 & SR2).
unfold rd_lstA in K |- *.
zstep. zstep. zstep. zstep. rewrite sxb_sval.
zstep. if_cases G; zify_cond G.
- zstep. zstep. if_cases G'; zify_lts G'; [| exfalso; lia]. apply K.
- apply K.
Qed.
#[using="rc OK RNGS"] Lemma zrl_chk1 : forall m1 ip' (x1 x6 x7 x10 x11 x13 x16 x18 x20 x22 x29 : word),
unpoisoned m1 BUF (BUF + zlen buf) -> 0 <= ip' -> ip' + 4 <= zlen buf ->
(forall y6 y10, evtF bsegs RNG POST (rd_lstA C 0x96e6c m1 x1 y6 x7 y10 x11 (Z_to_bv 64 (BUF + ip')) x13 x16 x18 x20 x22 x29)) ->
evtF bsegs RNG POST (rd_lstA C 0x96e5c m1 x1 x6 x7 x10 x11 (Z_to_bv 64 (BUF + ip')) x13 x16 x18 x20 x22 x29).
Proof.
intros m1 ip' x1 x6 x7 x10 x11 x13 x16 x18 x20 x22 x29 UB P0 P4 K.
destruct RNGS as (RI & RSTK & RN & RNS & RM & RMS & RT & RTS & RB & RBS).
pose proof OK as OK'. destruct OK' as (HH & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & BB & _ & _ & _ & _ & _ & _ & _ & _ & B8).
pose proof (ablk_lin _ _ BB) as LBB. unfold KHIGH, AIMG_HI, KEND in *.
destruct (chkB m1 BUF (BUF + zlen buf) (BUF + ip') UB ltac:(lia) ltac:(lia)) as (b1 & RDB1 & CK1 & SR1).
unfold rd_lstA in K |- *.
zstep. zstep. zstep. rewrite sxb_sval.
zstep. if_cases G; zify_cond G.
- zstep. zstep. if_cases G'; zify_lts G'; [| exfalso; lia]. apply K.
- apply K.
Qed.
#[using="rc OK SH RNGS"] Lemma zero_reloadA : forall s2 s3 m1 msvw tlw (x6 x7 x12 x20 x29 : word),
rd_invA C m1 (r_nc s2) msvw tlw -> reload buf s2 = Ok s3 ->
0 <= r_ip s2 -> r_ip s2 + 4 <= zlen buf -> 0 <= r_bitCount s2 < 64 ->
2 <= r_threshold s2 <= 32768 -> r_threshold s2 <= r_remaining s2 < 2 * r_threshold s2 ->
(forall y7 y10 y22, evtF bsegs RNG POST (rd_cntA C s3 m1 y7 y10 y22)) ->
evtF bsegs RNG POST (rd_lstA C 0x96e3c m1 (Z_to_bv 64 (r_nbBits s2)) x6 x7 (Z_to_bv 64 (BUF + r_ip s2)) (Z_to_bv 64 (r_remaining s2)) x12
(Z_to_bv 64 (r_charnum s2)) (Z_to_bv 64 (r_bitCount s2)) (Z_to_bv 64 (r_threshold s2)) x20 (Z_to_bv 64 ADB_TAB) x29).
Proof.
intros s2 s3 m1 msvw tlw x6 x7 x12 x20 x29 INV RL Hip0 Hip4 Hbc Hthr Hrem K.
pose proof RNGS as RNGS0. destruct RNGS0 as (RIq & RSTK & _). pose proof (okA_lin C OK) as (_ & _ & _ & _ & _ & _ & LOs & LOAs & SPA1 & SPA2 & _). pose proof atop_range as ATR. unfold RDA_CALLEE in LOs.
pose proof (reload_inv buf s2 s3 (buf_all_bytesA C OK) RL Hip0 Hip4 (proj1 Hbc)) as RI. cbv zeta in RI.
destruct RI as (I1 & I2 & I3 & ->).
pose proof OK as OK'. destruct OK' as (HH & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & BB & _ & _ & _ & _ & _ & _ & _ & _ & B8).
pose proof (ablk_lin _ _ BB) as LBB. unfold KHIGH, AIMG_HI, KEND in *.
pose proof INV as INV'. destruct INV' as (_ & _ & _ & _ & _ & (j0 & j64 & FRM) & _ & MU & _). unfold FRA_main in FRM.
destruct (inv_shadowA C m1 OK SH MU) as (_ & _ & _ & UB).
destruct s2 as [nc ip bs bc cn rem thr nb p0]. cbnR.
unfold reload_pos in *. unfold FseNCount.Zlength in *.
rewrite Z.shiftr_div_pow2 in * by lia. change (2^3) with 8 in *. rewrite land_7, land_31 in *.
assert (Q : 0 <= bc / 8 < 8) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
assert (LOAD : forall ip' bc' (y6 y7 y10 y20 y29 : word),
fst (if (ip <=? zlen buf - 7) || (ip + bc / 8 <=? zlen buf - 4) then (ip + bc / 8, bc mod 8) else (zlen buf - 4, (bc - 8 * (zlen buf - 4 - ip)) mod 32)) = ip' ->
snd (if (ip <=? zlen buf - 7) || (ip + bc / 8 <=? zlen buf - 4) then (ip + bc / 8, bc mod 8) else (zlen buf - 4, (bc - 8 * (zlen buf - 4 - ip)) mod 32)) = bc' ->
evtF bsegs RNG POST (rd_lstA C 0x96e5c m1 (Z_to_bv 64 nb) y6 y7 y10 (Z_to_bv 64 rem) (Z_to_bv 64 (BUF + ip')) (Z_to_bv 64 cn)
(Z_to_bv 64 bc') (Z_to_bv 64 thr) y20 (Z_to_bv 64 ADB_TAB) y29)).
{ intros ip' bc' y6 y7 y10 y20 y29 E1 E2. rewrite E1, E2 in *.
eapply (zrl_chk1 m1 ip'); [exact UB| lia| lia|]. intros z6 z10.
eapply (zrl_chk2 m1 ip'); [exact UB| lia| lia|]. intros w6 w10 w29.
eapply (zero_load2A (FseNCount.mkR nc ip' (le32 buf ip' / 2 ^ bc') bc' cn rem thr nb p0) m1 msvw tlw ip');
try eassumption; try reflexivity; cbnR; try lia; try reflexivity. }
clear K.
assert (T8 : forall (y6 y7 : word),
(ip <=? zlen buf - 7) || (ip + bc / 8 <=? zlen buf - 4) = true ->
evtF bsegs RNG POST (rd_lstA C 0x96e50 m1 (Z_to_bv 64 nb) y6 y7 (Z_to_bv 64 (BUF + ip)) (Z_to_bv 64 rem)
(Z_to_bv 64 (bc / 8 + (BUF + ip))) (Z_to_bv 64 cn) (Z_to_bv 64 bc) (Z_to_bv 64 thr) x20
(Z_to_bv 64 ADB_TAB) x29)).
{ intros y6 y7 EC. rewrite EC in LOAD. unfold rd_lstA in LOAD |- *.
zstep. if_cases G2; zify_cond G2; [exfalso; lia|].
zstep. rewrite land_7.
zstep. if_cases G3; zify_cond G3; [exfalso; lia|].
replace (bc / 8 + (BUF + ip)) with (BUF + (ip + bc / 8)) by lia.
eapply (LOAD (ip + bc / 8) (bc mod 8)); first [reflexivity | f_equal; lia]. }
unfold rd_lstA in LOAD, T8 |- *.
zstep. zstep. if_cases G1; zify_cond G1; [exfalso; lia|].
zstep. rewrite (wrap32_small bc) by lia. rewrite (Z.shiftr_div_pow2 bc 3) by lia. change (2^3) with 8.
rewrite ?(FseWalkKit.swrap32_small (bc / 8)) by lia.
zstep.
zstep.
if_cases B1; zify_cond B1.
-
zstep. if_cases G5; zify_cond G5; [exfalso; lia|].
zstep. zstep. zstep.
if_cases B2; zify_cond B2.
+ eapply T8. apply orb_true_iff. right. apply Z.leb_le. lia.
+ replace ((ip <=? zlen buf - 7) || (ip + bc / 8 <=? zlen buf - 4)) with false in LOAD
by (symmetry; apply orb_false_iff; split; apply Z.leb_gt; lia).
zstep. zstep. replace (BUF + zlen buf + -4 - (BUF + ip)) with (zlen buf - 4 - ip) by lia.
set (d := zlen buf - 4 - ip) in *. assert (Rd : 0 <= d <= 2) by (subst d; lia).
zstep. zstep. zstep. zstep.
replace ((d + 1152921504606846976) ≫ 61) with 0
by (rewrite Z.shiftr_div_pow2 by lia; symmetry; apply Z.div_small; change (2^61) with 2305843009213693952; lia).
zstep. if_false.
zstep. rewrite Z.shiftl_mul_pow2 by lia. change (2^3) with 8. rewrite (FseWalkKit.swrap32_small (d * 8)) by lia.
zstep. rewrite ?(Z.mod_small (d * 8)) by lia.
zstep. rewrite ?(FseWalkKit.swrap32_small (bc - d * 8)) by lia.
zstep. if_false.
zstep. rewrite land_31. zstep. zstep.
if_cases G4; zify_cond G4; [| exfalso; lia].
replace (BUF + zlen buf + -4) with (BUF + (zlen buf - 4)) by lia. replace (bc - d * 8) with (bc - 8 * d) by lia.
eapply (LOAD (zlen buf - 4) ((bc - 8 * (zlen buf - 4 - ip)) mod 32)); first [reflexivity | f_equal; lia | f_equal; f_equal; lia].
- eapply T8. apply orb_true_iff. left. apply Z.leb_le. lia.
Qed.
#[using="rc OK SH RNGS"] Lemma zero_tailA : forall s1 m1 msvw tlw fl (x7 x20 x29 : word),
rd_invA C m1 (r_nc s1) msvw tlw ->
0 <= r_bitStream s1 < 2^32 -> 0 <= r_ip s1 -> r_ip s1 + 4 <= zlen buf -> 0 <= r_bitCount s1 < 32 ->
0 <= r_charnum s1 <= 2^30 -> ctzv (r_bitStream s1) / 2 < 12 -> 0 <= r_remaining s1 < 2^31 ->
2 <= r_threshold s1 <= 32768 -> r_threshold s1 <= r_remaining s1 < 2 * r_threshold s1 ->
(let rep1 := ctzv (r_bitStream s1) / 2 in
let! bs := shr32 (r_bitStream s1) (2 * rep1) in
let s2 := FseNCount.mkR (r_nc s1) (r_ip s1) bs (r_bitCount s1 + 2 * rep1 + 2) (r_charnum s1 + 3 * rep1 + Z.land bs 3)
(r_remaining s1) (r_threshold s1) (r_nbBits s1) (r_previous0 s1) in
if msv1 <=? r_charnum s1 + 3 * rep1 + Z.land bs 3 then Ok (Brk s2) else let! s3 := reload buf s2 in Ok (Cont s3)) = Ok fl ->
(forall s' y1 y6 y7 y12 y18 y20 y22 y29, fl = Brk s' -> r_nc s' = r_nc s1 -> rd_brk_okA C s' ->
evtF bsegs RNG POST (rd_exitA C s' m1 y1 y6 y7 y12 y18 y20 y22 y29)) ->
(forall s' y7 y10 y22, fl = Cont s' -> r_nc s' = r_nc s1 -> evtF bsegs RNG POST (rd_cntA C s' m1 y7 y10 y22)) ->
evtF bsegs RNG POST (rd_lstA C 0x96e10 m1 (Z_to_bv 64 (r_nbBits s1)) (Z_to_bv 64 (bv_swrap 32 (r_bitStream s1))) x7
(Z_to_bv 64 (BUF + r_ip s1)) (Z_to_bv 64 (r_remaining s1)) (Z_to_bv 64 (ctzv (r_bitStream s1)))
(Z_to_bv 64 (r_charnum s1)) (Z_to_bv 64 (r_bitCount s1)) (Z_to_bv 64 (r_threshold s1)) x20
(Z_to_bv 64 ADB_TAB) x29).
Proof.
intros s1 m1 msvw tlw fl x7 x20 x29 INV Hbs Hip0 Hip4 Hbc Hcn Hrep Hrem Hthr Hrem2 RR KB KC.
pose proof OK as OK'. destruct OK' as (HH & _ & HM0 & _).
pose proof (ctzv_range _ Hbs) as Rk.
destruct s1 as [nc ip bs bc cn rem thr nb p0]. cbnR. cbv zeta in RR.
set (k := ctzv bs) in *. set (rep := k / 2) in *.
assert (Rrep : 0 <= rep <= 11 /\ 2 * rep <= k <= 2 * rep + 1) by (subst rep; Z.div_mod_to_equations; lia).
rewrite shr32_ok in RR by lia. cbn [bind] in RR.
set (bs2 := bs / 2 ^ (2 * rep)) in *.
assert (Rbs2 : 0 <= bs2 < 2^32) by (subst bs2; apply shr_range; lia).
assert (L3 : 0 <= Z.land bs2 3 <= 3) by (rewrite land_3; pose proof (Z.mod_pos_bound bs2 4 ltac:(lia)); lia).
change (2^30) with 1073741824 in *. change (2^31) with 2147483648 in *.
unfold rd_lstA.
destruct (ctz_masks k ltac:(lia)) as (M1 & M2 & M3). fold rep in M1, M2, M3.
zstep. rewrite M3. zstep. rewrite M1. zstep. rewrite M2.
zstep. rewrite (wrap32_swrap32_u32 bs Hbs). rewrite (Z.mod_small (2 * rep) 32) by lia.
rewrite (Z.shiftr_div_pow2 bs (2 * rep)) by lia. fold bs2.
zstep.
zstep.
zstep.
zstep. rewrite (land_swrap32 bs2 3) by lia.
zstep. rewrite ?(FseWalkKit.swrap32_small (2 * rep + rep + cn + Z.land bs2 3)) by lia.
replace (2 * rep + rep + cn + Z.land bs2 3) with (cn + 3 * rep + Z.land bs2 3) by lia.
zstep. rewrite ?(FseWalkKit.swrap32_small (bc + 2 * rep + 2)) by lia.
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
pose proof (fun y6 y7 y12 y20 y29 => zero_reloadA (FseNCount.mkR nc ip bs2 (bc + 2 * rep + 2) (cn + 3 * rep + Z.land bs2 3) rem thr nb p0)
s3 m1 msvw tlw y6 y7 y12 y20 y29 INV RL) as ZR. cbnR. unfold rd_lstA in ZR.
eapply ZR; try lia.
intros y7 y10 y22. apply KC; [reflexivity|].
pose proof (reload_inv buf _ s3 (buf_all_bytesA C OK) RL) as RI. cbnR. cbv zeta in RI.
destruct (RI ltac:(lia) ltac:(unfold FseNCount.Zlength; lia) ltac:(lia)) as (_ & _ & _ & ->). reflexivity.
Qed.
#[using="rc OK SH RNGS"] Lemma zero_runA : forall tl s m1 msvw tlw fl (x7 x12 x20 x22 x29 : word),
5 <= tl <= 15 ->
rd_invA C m1 (r_nc s) msvw tlw -> CTL msv1 (a_rt0 C) tl s -> POS buf s -> r_bitCount s < 32 ->
rzero_block buf msv1 s = Ok fl ->
(forall s' y1 y6 y7 y12 y18 y20 y22 y29, fl = Brk s' -> r_nc s' = r_nc s -> rd_brk_okA C s' ->
evtF bsegs RNG POST (rd_exitA C s' m1 y1 y6 y7 y12 y18 y20 y22 y29)) ->
(forall s' y7 y10 y22, fl = Cont s' -> r_nc s' = r_nc s -> evtF bsegs RNG POST (rd_cntA C s' m1 y7 y10 y22)) ->
evtF bsegs RNG POST (rd_lstA C 0x96cf8 m1 (Z_to_bv 64 (r_nbBits s)) (Z_to_bv 64 (bv_swrap 32 (r_bitStream s))) x7
(Z_to_bv 64 (BUF + r_ip s)) (Z_to_bv 64 (r_remaining s)) x12 (Z_to_bv 64 (r_charnum s))
(Z_to_bv 64 (r_bitCount s)) (Z_to_bv 64 (r_threshold s)) x20 x22 x29).
Proof.
intros tl s m1 msvw tlw fl x7 x12 x20 x22 x29 Htl INV HC HP HB32 RR KB KC.
destruct (ctl_pos_ranges _ _ _ _ _ Htl HC HP) as (Rnb & Ethr & Rthr & Rrem & Rrem2 & Rcn & Lnc & Rip & Rip4 & Rbc & Rbs).
pose proof OK as OK'. destruct OK' as (HH & _ & HM0 & _).
unfold rzero_block in RR. rewrite (repeats_of_ctzv _ Rbs) in RR. cbn [bind] in RR.
destruct (rep_loop buf (S (Z.to_nat (FseNCount.Zlength buf))) s (ctzv (r_bitStream s) / 2)) as [[s1 rep1]| | |] eqn:RLP;
cbn [bind] in RR; try discriminate RR.
pose proof (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))))))) as MI.
eapply zero_ctz1A; [exact Rbs| exact MI|]. intros y29.
eapply (zero_repA _ s _ s1 rep1 m1 msvw tlw 0x96d20); try exact RLP; try exact INV; try lia; try reflexivity.
{ unfold FseNCount.Zlength. change (2^30) with 1073741824. rewrite Nat2Z.inj_succ, Z2Nat.id by lia. lia. }
intros z7 z20 z29 Hbs1 Hip0 Hip4 Hbc1 Hcn1 Erep1 Hrep1 (E1 & E2 & E3 & E4 & E5).
rewrite <- E2, <- E3, <- E4.
eapply (zero_tailA s1 m1 msvw tlw fl); try eassumption; try lia.
- rewrite E1. exact INV.
- cbv zeta. rewrite <- Erep1. exact RR.
- intros s' y1 y6 y7 y12 y18 y20 y22 y29' EF EN BK. apply KB; [exact EF| rewrite EN; exact E1| exact BK].
- intros s' y7 y10 y22 EF EN. apply KC; [exact EF| rewrite EN; exact E1].
Qed.
End Zero.
End CANSEC1.
