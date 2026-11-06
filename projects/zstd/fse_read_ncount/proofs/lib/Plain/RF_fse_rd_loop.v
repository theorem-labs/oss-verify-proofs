(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import FseNCount FseLemmas FseReadSound.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import FseWalkKit FseRdKit FseRdKit2.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Plain Require Import PImg RF_fse_iface RF_fse_rd_base RF_fse_rd_count RF_fse_rd_zero.
Import ListNotations.
Open Scope Z_scope.
Section Loop.
Variable C : rdctx.
Hypothesis OK : rd_ok C.
Variable tl : Z.
Hypothesis Htl : 5 <= tl <= 15.
Notation buf := (c_buf C).
Notation msv1 := (c_msv0 C + 1).
Notation BUF := (c_BUF C).
Ltac cbnR := cbn [r_nc r_ip r_bitStream r_bitCount r_charnum r_remaining r_threshold r_nbBits r_previous0] in *.
#[using="OK"] Lemma exit_run : forall s m1 msvw (x1 x20 x23 x24 x26 x27 x30 : word),
rd_inv C m1 (r_nc s) msvw (Z_to_bv 64 tl) -> rd_brk_ok C s ->
r_remaining s = 1 -> 1 <= r_charnum s <= msv1 -> r_bitCount s <= 32 ->
evt psegs (rd_body_post C (r_nc s) (r_charnum s - 1) tl (r_ip s + (r_bitCount s + 7) / 8))
(rd_exit C s m1 x1 x20 x23 x24 x26 x27 x30).
Proof.
intros s m1 msvw x1 x20 x23 x24 x26 x27 x30 INV (B1 & B2 & B3 & B4 & B5) Erem Hcn Hbc.
pose proof OK as OK'. destruct OK' as (HH & FBY & HM0 & HM1 & RSP & LO & LO0 & (HN0 & HN1) & (HB0 & HB1) & (HV0 & HV1) & (HT0 & HT1) & SNS & SMS & STS & SBS & SNM & SNT & SNB & SMT & SMB & STB).
unfold RD_STACK in *.
unfold rd_exit, rd_lst.
destruct s as [nc ip bs bc cn rem thr nb p0]. cbnR. subst rem.
destruct INV as (ARR & LNC & HBUF & HMSV & HTL & (junk8 & FR) & ST & MU & WM & MI). unfold rd_W, RD_STACK in MU.
assert (LWS : length (map (Z_to_bv 64) nc) = length (c_rt0 C)) by (rewrite length_map; exact LNC).
assert (LBS : zlen (map (Z_to_bv 8) buf) = zlen buf) by (rewrite length_map; reflexivity).
change (2^31) with 2147483648 in *.
zstep. zstep. zstep. if_false.
zstep.
Local Ltac2 Set LiaHints.tbl := fun () => "00V0>1010228364.79 10609739141.6811556575866.6912532123116.6813721967950.6914164276758.6816637712524.7917286780044.7817713987757.8418296467856.6719107270796.7819628484000.6720309704588.7820924707980.7828140551564.7629788655736.6829803348876.7830572420492.7732914133132.7634256419984.6935418171532.783714120674.80 37211491939.8442831019478.8443327240343.8443774890704.8444060886039.6847377289921.8250551044677.8252567164907.8456666956445.845815946124.78 59308628433.6759308628566.6863380911496.6865859608277.6866772733324.77800752792.68  00000900=00@00I00R00V00_00h01=01I01R01_01h02102:02;02D02M02V02b02k02o03803E03N03[03c04:04N04W04g05005@05H05I05N05W05`S3LNC3LWSS2B2S1QS3LNC3LWSS3LNC3LWSS2B2S3LNC3LWSS3LNC3LWSS3LNC3SMB3LWS3SMT3SNMS3LNC2B33LWSS3LNC3LWSS3LNC3HM03LWSS3LNC3LWSS3LNC3LWSS3LNC3LWSSS3LNC3LWSS3LNC3LWSS3LNC3LWSS3LNC2LO3LWSS3LNC3LWSS2B2S3LNC3LWSS3LNC3HV13LWSS3LNC3LWSS3LNC3HV03LWSS2B23HbcS3LNC2B42B53HB03HB13LWSS3LNC2HH3HB03HB13LWSS3LNC3LWSS3LNC2LO3SMS3LWSS3LNC3LWSS3LNC3Hcn3LWS2K2S3Hbc2K3SS3HbcS3LNC3LWSS3LNC3LWS".
if_cases K2; zify_cond K2; [|exfalso; lia].
zstep. zstep.
if_cases K3; zify_cond K3; rewrite ?signed_lit in K3 by lia; [exfalso; lia|].
zstep. zstep. zstep. zstep.
rewrite (swrap32_small (bc + 7)) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
assert (Q : 0 <= (bc + 7) / 8 < 5) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
rewrite (swrap32_small ((bc + 7) / 8)) by lia.
zstep. zstep.
replace (BUF + ip - BUF + (bc + 7) / 8) with (ip + (bc + 7) / 8) by lia.
do 13 zstep. zstep. zstep.
release_frame FR ST (c_SP C).
apply evt_done. unfold rd_body_post, rd_W, RD_STACK.
do 14 eexists. eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
split; [exact ARR|]. split; [| exact HTL].
replace (cn - 1) with (cn + -1) by lia. exact HMSV.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="OK"] Lemma buf_h8 : 8 <= FseNCount.Zlength buf.
Proof. unfold FseNCount.Zlength. destruct OK as (HH & _). Local Ltac2 Set LiaHints.tbl := fun () => "0010=52018712845.5000004S2HH".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="OK"] Lemma msv1_ok : 1 <= msv1 <= FseNCount.Zlength (c_rt0 C).
Proof. unfold FseNCount.Zlength. destruct OK as (_ & _ & HM0 & HM1 & _). Local Ltac2 Set LiaHints.tbl := fun () => "0010=48770900490.6000009S3HM03HM1".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="OK Htl"] Lemma loop_run : forall f s sF m1 msvw (x1 x25 x26 x27 : word),
rloop buf msv1 f s = Ok sF ->
rd_inv C m1 (r_nc s) msvw (Z_to_bv 64 tl) -> CTL msv1 (c_rt0 C) tl s -> POS buf s -> r_bitCount s < 32 ->
r_remaining sF = 1 -> r_charnum sF <= msv1 -> r_bitCount sF <= 32 ->
evt psegs (rd_body_post C (r_nc sF) (r_charnum sF - 1) tl (r_ip sF + (r_bitCount sF + 7) / 8)) (rd_head C s m1 x1 x25 x26 x27).
Proof.
induction f as [|f IH]; intros s sF m1 msvw x1 x25 x26 x27 RL INV HC HP HB32 F1 F2 F3.
{ cbn in RL. discriminate RL. }
cbn [rloop] in RL.
set (POSTF := rd_body_post C (r_nc sF) (r_charnum sF - 1) tl (r_ip sF + (r_bitCount sF + 7) / 8)).
assert (CNT : forall s1 m2 (y1 y23 y26 y27 : word),
rd_inv C m2 (r_nc s1) msvw (Z_to_bv 64 tl) -> CTL msv1 (c_rt0 C) tl s1 -> POS buf s1 -> r_bitCount s1 < 32 ->
(let! fl := rcount_block buf msv1 s1 in match fl with Brk s' => Ok s' | Cont s' => rloop buf msv1 f s' end) = Ok sF ->
evt psegs POSTF (rd_cnt C s1 m2 y1 y23 y26 y27)).
{ intros s1 m2 y1 y23 y26 y27 INV1 HC1 HP1 HB1 RL1.
destruct (rcount_total buf (buf_all_bytes C OK) buf_h8 msv1 (c_rt0 C) msv1_ok tl Htl s1 HC1 HP1 HB1) as (fl & EF & HF).
rewrite EF in RL1. cbn [bind] in RL1.
eapply (count_run C OK tl Htl POSTF s1 m2 msvw (Z_to_bv 64 tl) fl); try eassumption.
- intros s' m3 z1 z20 z23 z24 z26 z27 z30 -> INV3 BK. injection RL1 as ->.
destruct HF as ((_ & CN1 & _) & _).
eapply (exit_run sF m3 msvw); try assumption. Local Ltac2 Set LiaHints.tbl := fun () => "0030>45237659827.3566338264904.3566350914419.4500000100900AFS2F23CN1S2F23CN1".
lia.
- intros s' m3 z1 z25 z26 z27 -> INV3. destruct HF as (HC3 & HP3 & HB3 & _).
eapply IH; eassumption. }
unfold rbody in RL.
destruct (r_previous0 s) eqn:EP.
-
destruct (rzero_total buf (buf_all_bytes C OK) buf_h8 msv1 (c_rt0 C) msv1_ok tl Htl s HC HP HB32) as (flz & EZ & HZ).
rewrite EZ in RL. cbn [bind] in RL.
unfold rd_head. rewrite EP.
eapply (zero_run C OK POSTF tl s m1 msvw (Z_to_bv 64 tl) flz); try eassumption.
+ intros s' z1 z20 z23 z24 z26 z27 z30 -> EN BK. cbn [bind] in RL. injection RL as ->.
destruct HZ as ((_ & CN1 & _) & _).
eapply (exit_run sF m1 msvw); try assumption; try lia. rewrite EN. exact INV.
+ intros s' z1 z23 z26 z27 -> EN. destruct HZ as (HC1 & HP1 & HB1 & _).
apply CNT; try assumption. rewrite EN. exact INV.
-
cbn [bind] in RL.
pose proof (CNT s m1) as CNT'. unfold rd_cnt, rd_lst in CNT'.
unfold rd_head, rd_lst. rewrite EP.
zstep. zstep.
apply CNT'; assumption.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="OK Htl"] Corollary loop_run' : forall f s sF m1 msvw pc (x1 x12 x14 x20 x22 x23 x24 x25 x26 x27 x30 : word),
rloop buf msv1 f s = Ok sF ->
rd_inv C m1 (r_nc s) msvw (Z_to_bv 64 tl) -> CTL msv1 (c_rt0 C) tl s -> POS buf s -> r_bitCount s < 32 ->
r_remaining sF = 1 -> r_charnum sF <= msv1 -> r_bitCount sF <= 32 ->
pc = (if r_previous0 s then 0x13f88 else 0x13f80) ->
x12 = Z_to_bv 64 (r_remaining s) -> x14 = Z_to_bv 64 (BUF + r_ip s) -> x20 = Z_to_bv 64 (r_threshold s) ->
x22 = Z_to_bv 64 (r_bitCount s) -> x23 = Z_to_bv 64 (r_charnum s) -> x24 = Z_to_bv 64 (bv_swrap 32 (r_bitStream s)) ->
x30 = Z_to_bv 64 (r_nbBits s) ->
evt psegs (rd_body_post C (r_nc sF) (r_charnum sF - 1) tl (r_ip sF + (r_bitCount sF + 7) / 8))
(rd_lst C pc m1 x1 x12 x14 x20 x22 x23 x24 x25 x26 x27 x30).
Proof.
intros f s sF m1 msvw pc x1 x12 x14 x20 x22 x23 x24 x25 x26 x27 x30 RL INV HC HP HB F1 F2 F3 -> -> -> -> -> -> -> ->.
exact (loop_run f s sF m1 msvw x1 x25 x26 x27 RL INV HC HP HB F1 F2 F3).
Qed.
End Loop.
