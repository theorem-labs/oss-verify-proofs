(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Spec Require Import FseNCount FseLemmas FseReaderRT FseReadSound.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Common Require Import FseWalkKit FseRdKit FseRdKit2.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import UImg RF_fse_iface RF_fse_rd_base RF_fse_rd_loop.
Import ListNotations.
Open Scope Z_scope.
Section Hdr.
Variable C : rdctx.
Hypothesis OK : rd_ok C.
Notation buf := (c_buf C).
Notation msv1 := (c_msv0 C + 1).
Notation BUF := (c_BUF C).
Notation NC := (c_NC C).
Ltac cbnR := cbn [r_nc r_ip r_bitStream r_bitCount r_charnum r_remaining r_threshold r_nbBits r_previous0] in *.
#[using="OK"] Corollary hdr_loop : forall tl, 5 <= tl <= 15 -> forall f s sF m1 msvw pc (x1 x6 x11 x13 x14 x16 x24 x25 x26 x27 x28 x29 : word),
rloop buf msv1 f s = Ok sF ->
rd_inv C m1 (r_nc s) msvw (Z_to_bv 64 tl) -> CTL msv1 (c_rt0 C) tl s -> POS buf s -> r_bitCount s < 32 ->
r_remaining sF = 1 -> r_charnum sF <= msv1 -> r_bitCount sF <= 32 ->
pc = (if r_previous0 s then 0x140fc else 0x140e0) ->
x11 = Z_to_bv 64 (r_charnum s) -> x13 = Z_to_bv 64 (bv_swrap 32 (r_bitStream s)) -> x24 = Z_to_bv 64 (r_remaining s) ->
x25 = Z_to_bv 64 (r_threshold s) -> x26 = Z_to_bv 64 (r_bitCount s) -> x27 = Z_to_bv 64 (BUF + r_ip s) -> x29 = Z_to_bv 64 (r_nbBits s) ->
evt usegs (rd_body_post C (r_nc sF) (r_charnum sF - 1) tl (r_ip sF + (r_bitCount sF + 7) / 8))
(rd_lst C pc m1 x1 x6 x11 x13 x14 x16 x24 x25 x26 x27 x28 x29).
Proof.
intros tl Htl f s sF m1 msvw pc x1 x6 x11 x13 x14 x16 x24 x25 x26 x27 x28 x29 RL INV HC HP HB F1 F2 F3 -> -> -> -> -> -> -> ->.
exact (loop_run C OK tl Htl f s sF m1 msvw x1 x6 x14 x16 x28 RL INV HC HP HB F1 F2 F3).
Qed.
#[using="OK"] Lemma rd_header : forall m1 tl0 sF junk (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
u8arr usegs m1 NC (u16s (map (Z_to_bv 64) (zero_prefix (Z.to_nat msv1) (c_rt0 C)))) ->
bytes_at usegs m1 BUF (map (Z_to_bv 8) buf) ->
rw_cells usegs m1 (c_MSVP C) [C4 (Z_to_bv 64 (c_msv0 C))] -> rw_cells usegs m1 (c_TLP C) [C4 tl0] ->
rw_cells usegs m1 (c_SP C + -128) [CB 24 junk; C8 (c_s11 C); C8 (c_s10 C); C8 (c_s9 C); C8 (c_s8 C); C8 (c_s7 C); C8 (c_s6 C);
C8 (c_s5 C); C8 (c_s4 C); C8 (c_s3 C); C8 (c_s2 C); C8 (c_s1 C); C8 (c_s0 C); C8 (c_ra C)] ->
stk usegs m1 (c_lo C) (c_SP C + -128) -> munch (rd_W C) (c_m C) m1 -> wmono usegs (c_m C) m1 -> mem_inv usegs m1 ->
Z.land (le32 buf 0) 15 <= 10 ->
rloop buf msv1 (S (Z.to_nat msv1)) (rd_s0 buf msv1 (c_rt0 C)) = Ok sF ->
r_remaining sF = 1 -> r_charnum sF <= msv1 -> r_bitCount sF <= 32 ->
evt usegs (rd_body_post C (r_nc sF) (r_charnum sF - 1) (Z.land (le32 buf 0) 15 + 5) (r_ip sF + (r_bitCount sF + 7) / 8))
(MS (mkR x1 (Z_to_bv 64 (c_SP C + -128)) (c_gp C) (c_tp C) x5 x6 x7 (Z_to_bv 64 BUF) (Z_to_bv 64 (c_MSVP C))
x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 NC) (Z_to_bv 64 (c_TLP C)) (Z_to_bv 64 msv1) (Z_to_bv 64 (BUF + zlen buf)) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
(c_F C) (Z_to_bv 64 0x14020) (c_fc C) None m1 (seg_rom usegs)).
Proof.
intros m1 tl0 sF junk x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 ARR HBUF HMSV HTL FR ST MU WM MI HX RL F1 F2 F3.
pose proof OK as OK'. destruct OK' as (HH & FBY & HM0 & HM1 & RSP & LO & LO0 & (HN0 & HN1) & (HB0 & HB1) & (HV0 & HV1) & (HT0 & HT1) & SNS & SMS & STS & SBS & SNM & SNT & SNB & SMT & SMB & STB & (HNP & HNA) & (HVP & HVA) & (HTP & HTA) & HBP).
unfold RD_STACK in *.
Local Ltac2 Set LiaHints.tbl := fun () => "00Y0?10431528747.96 10431528748.10010647094532.71 12598390901.98 14202106942.75 15534906503.94 17713987757.10121922089021.73 22605103099.89 29315478722.87 3132576391.94  3223250298.89  37187770245.89 37211491939.10140825345228.89 41415729742.84 42831019478.10143290223857.87 43327240343.1014339286231.87  43774890704.10143929283719.94 48625107299.88 48771248059.58 51813165669.84 52567164907.10155590027237.87 55754453387.89 56091574818.87 56666956445.1015738588431.86  5750404528.101 58705023297.89 58756150127.84 59128021829.89 59314923118.86 59588178615.94 60154389715.90 61448213823.77 64391634778.87 65502002695.81 00000400800@00D00L00M00^00f00k01001101901>01C01H01M01V01^01c01n02702802C02L02T02Y02a02f02n03:03A03H03P03X03Y03c03h03o04704<04AS2RWS2RWS3LNC2HHS2P5S3LNC2HHFS3LNC3STB3SMT3SNTS3LNC2HHS3LNCS3LNCFS3LNC2RWS3LNCS3LNCS3LNCS3LNCS3LNC3HT1S3LNC2P5S3LNCS3LNC2HX2X0S3LNC3HT0FS3LNC2HX2X0S3HM03HM1S3LNC2X0S3LNCS3LNC2P5S3LNCS3LNC2X0S3LNC2LO3STSS2HX2X0S2HX2X0S3LNC2RWS3LNC2HXFS3LNC2HX1KS3LNCS3LNC1HS3LNC2HHS3LNCS3LNC".
destruct (rd_s0_inv buf msv1 (c_rt0 C) (buf_all_bytes C OK) (proj1 HH) ltac:(lia) HX) as (HC0 & HP0 & HB0').
pose proof (zero_prefix_length (Z.to_nat msv1) (c_rt0 C)) as LNC. unfold rd_W, RD_STACK in MU.
destruct (buf_rd C OK m1 0 HBUF ltac:(lia)) as [RD0 R0].
destruct (buf_rd C OK m1 1 HBUF ltac:(lia)) as [RD1 R1].
destruct (buf_rd C OK m1 2 HBUF ltac:(lia)) as [RD2 R2].
destruct (buf_rd C OK m1 3 HBUF ltac:(lia)) as [RD3 R3].
rewrite Z.add_0_r in RD0.
zstep. cbv beta. zstep. cbv beta. zstep. cbv beta. zstep. cbv beta.
zstep. zstep. zstep. zstep. zstep. zstep.
rewrite le32_lbu_raw by assumption.
change (Znth 0 buf + 2 ^ 8 * Znth 1 buf + 2 ^ 16 * Znth 2 buf + 2 ^ 24 * Znth 3 buf) with (le32 buf 0).
pose proof (le32_range buf 0 (buf_all_bytes C OK)) as RW.
set (W := le32 buf 0) in *.
zstep.
remember (Z.land W 15) as x eqn:Ex.
assert (X0 : 0 <= x) by (subst x; rewrite land_15; apply Z.mod_pos_bound; lia).
assert (P5 : 32 <= 2 ^ (x + 5) <= 32768).
{ split; [change 32 with (2^5)| change 32768 with (2^15)]; apply Z.pow_le_mono_r; lia. }
zstep. zstep.
if_cases K; zify_cond K; [| exfalso; lia].
zstep. if_cases G; zify_cond G; [exfalso; lia|].
assert (LT3 : Z.land (c_TLP C) 3 = c_TLP C mod 4) by (change 3 with (Z.ones 2); apply Z.land_ones; lia).
zstep. zstep. if_cases G2; zify_cond G2; [exfalso; lia|].
do 18 zstep.
zstep.
zstep. rewrite ?(Z.mod_small x 32) by lia. rewrite Z.shiftl_mul_pow2 by lia.
replace (32 * 2 ^ x) with (2 ^ (x + 5)) by (rewrite Z.pow_add_r by lia; change (2^5) with 32; lia).
rewrite (swrap32_small (2 ^ (x + 5))) by lia.
do 6 zstep. rewrite (swrap32_small (2 ^ (x + 5) + 1)) by lia.
zstep. zstep. zstep. zstep. if_false.
replace (Z_to_bv 64 (-2147483648)) with (Z_to_bv 64 18446744071562067968) by (apply bv_eq; reflexivity).
subst x.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
assert (INV0 : rd_inv C mm (r_nc (rd_s0 buf msv1 (c_rt0 C))) (Z_to_bv 64 (c_msv0 C)) (Z_to_bv 64 (Z.land W 15 + 5))) end.
{ unfold rd_s0. cbv zeta. cbnR. unfold rd_inv, rd_W, RD_STACK.
split; [exact ARR|]. split; [exact LNC|]. split; [exact HBUF|]. split; [exact HMSV|]. split; [exact HTL|].
split; [do 2 eexists; exact FR|]. split; [exact ST|]. split; [exact MU|]. split; [exact WM| exact MI]. }
eapply (hdr_loop (Z.land W 15 + 5) ltac:(lia) (S (Z.to_nat msv1)) (rd_s0 buf msv1 (c_rt0 C)) sF _ (Z_to_bv 64 (c_msv0 C)));
try eassumption; try reflexivity.
all: unfold rd_s0; cbv zeta; cbnR; fold W.
all: try (f_equal; lia).
rewrite Z.shiftr_div_pow2 by lia. f_equal. symmetry. apply swrap32_small.
assert (0 <= W / 2^4 < 2^28) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]). lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End Hdr.
