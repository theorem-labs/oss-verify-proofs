(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import FseNCount FseLemmas FseReadSound.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import FseWalkKit FseRdKit.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Plain Require Import PImg RF_fse_iface RF_fse_rd_base.
Import ListNotations.
Open Scope Z_scope.
Section Count1.
Variable C : rdctx.
Hypothesis OK : rd_ok C.
Variable tl : Z.
Hypothesis Htl : 5 <= tl <= 15.
Variable POST : machine_state -> Prop.
Notation buf := (c_buf C).
Notation msv1 := (c_msv0 C + 1).
Notation BUF := (c_BUF C).
Ltac cbnR := cbn [r_nc r_ip r_bitStream r_bitCount r_charnum r_remaining r_threshold r_nbBits r_previous0] in *.
#[using="OK"] Lemma cnt_load : forall s2 m1 msvw tlw count ip' (x1 x14 x22 x24 x25 x26 x27 : word),
rd_inv C m1 (r_nc s2) msvw tlw ->
0 <= ip' -> ip' + 4 <= zlen buf -> 0 <= r_bitCount s2 < 32 ->
r_ip s2 = ip' -> r_bitStream s2 = le32 buf ip' / 2 ^ r_bitCount s2 -> r_previous0 s2 = (count =? 0) ->
-1 <= count < 2^31 ->
x14 = Z_to_bv 64 (BUF + ip') -> x22 = Z_to_bv 64 (r_bitCount s2) -> x24 = Z_to_bv 64 count ->
(forall y1 y25 y26 y27, evt psegs POST (rd_head C s2 m1 y1 y25 y26 y27)) ->
evt psegs POST (rd_lst C 0x14194 m1 x1 (Z_to_bv 64 (r_remaining s2)) x14 (Z_to_bv 64 (r_threshold s2)) x22
(Z_to_bv 64 (r_charnum s2)) x24 x25 x26 x27 (Z_to_bv 64 (r_nbBits s2))).
Proof.
intros s2 m1 msvw tlw count ip' x1 x14 x22 x24 x25 x26 x27 INV Hip0 Hip4 Hbc Eip Ebs Ep0 Hcount -> -> -> K.
destruct INV as (_ & _ & HBUF & _).
Local Ltac2 Set LiaHints.tbl := fun () => "00B0>1164727413.40 14533046805.2615534906497.4921481650978.3625995870147.513132576385.49 35120240342.2840138033082.3643929283719.5149792581730.4052520289792.3853508216725.5354738759716.2456641621271.3059588178608.5059588178615.5160245107413.5363407446814.3800000:00E00F00K00P00Q00\00a00b00n00o01001;01F01G01H01I01PS6Hcount1NS4Hip04Hip4FS3HbcS3HbcFS4Hip04Hip4S3HbcFS6Hcount1L1NSSS4Hip04Hip4S4Hip04Hip4SSFS3Hbc1L".
destruct (buf_rd C OK m1 ip' HBUF ltac:(lia)) as [RD0 R0].
destruct (buf_rd C OK m1 (ip' + 1) HBUF ltac:(lia)) as [RD1 R1].
destruct (buf_rd C OK m1 (ip' + 2) HBUF ltac:(lia)) as [RD2 R2].
destruct (buf_rd C OK m1 (ip' + 3) HBUF ltac:(lia)) as [RD3 R3].
rewrite !Z.add_assoc in RD1, RD2, RD3.
destruct s2 as [nc ip bs bc cn rem thr nb p0]. cbnR. subst ip p0.
unfold rd_lst.
zstep. cbv beta. zstep. cbv beta. zstep. cbv beta. zstep. cbv beta.
zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
rewrite le32_lb_raw by assumption. rewrite (Z.mod_small bc 32) by lia. rewrite Z.shiftr_div_pow2 by lia.
fold (le32 buf ip'). rewrite <- Ebs.
pose proof K as K'. unfold rd_head, rd_lst in K'. cbnR.
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
#[using="OK"] Lemma cnt_reload : forall s1 s2 m1 msvw tlw count (x1 x25 x26 x27 : word),
rd_inv C m1 (r_nc s1) msvw tlw -> reload buf s1 = Ok s2 ->
0 <= r_ip s1 -> r_ip s1 + 4 <= zlen buf -> 0 <= r_bitCount s1 < 64 ->
r_previous0 s1 = (count =? 0) -> -1 <= count < 2^31 ->
(forall y1 y25 y26 y27, evt psegs POST (rd_head C s2 m1 y1 y25 y26 y27)) ->
evt psegs POST (rd_lst C 0x14184 m1 x1 (Z_to_bv 64 (r_remaining s1)) (Z_to_bv 64 (BUF + r_ip s1)) (Z_to_bv 64 (r_threshold s1))
(Z_to_bv 64 (r_bitCount s1)) (Z_to_bv 64 (r_charnum s1)) (Z_to_bv 64 count) x25 x26 x27 (Z_to_bv 64 (r_nbBits s1))).
Proof.
intros s1 s2 m1 msvw tlw count x1 x25 x26 x27 INV RL Hip0 Hip4 Hbc Ep0 Hcount K.
pose proof (reload_inv buf s1 s2 (buf_all_bytes C OK) RL Hip0 Hip4 (proj1 Hbc)) as RI. cbv zeta in RI.
destruct RI as (I1 & I2 & I3 & ->).
pose proof OK as OK'. destruct OK' as (HH & _ & _ & _ & _ & _ & _ & _ & (HB0 & HB1) & _).
destruct s1 as [nc ip bs bc cn rem thr nb p0]. cbnR. subst p0.
unfold reload_pos in *. unfold FseNCount.Zlength in *.
Local Ltac2 Set LiaHints.tbl := fun () => "00L0>10029754702.3710613833396.3510992306353.4411001195444.3711706759828.3713703880721.3421479112868.3425993772992.4425993772992.4526766602107.3726766602234.3629786561501.3429788724074.3530195467701.3732458649881.3732665485845.3635504068375.3735916362634.4742815240411.3747366385985.3647375192773.4455726401616.3756428502567.4458024162856.3659078035918.3763370427949.3467439684295.378929299744.37 00000400900E00Q00V00[00`00e00j00k00l00m00n00o01001<01@01A01J01]02102902:02>02B02C02L02bS2B2S3HbcS2HH3HB03HB1S2HH3HB03HB1S3HbcS3HbcS3HbcS3HbcS3HbcSSSSSSS2HH3HB03HB1S2B1FS4Hip42B1S4Hip04Hip43HB03HB1S4Hip42HH3HB03HB12B1S3Hbc2B2FS2B1S2B2SS4Hip42B1S4Hip42HH3HB03HB11Q2B1".
rewrite Z.shiftr_div_pow2 in * by lia. change (2^3) with 8 in *. rewrite land_7, land_31 in *.
assert (Q : 0 <= bc / 8 < 8) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
assert (LOAD : forall ip' bc' (y1 y14 y22 y25 y26 y27 : word),
fst (if (ip <=? zlen buf - 7) || (ip + bc / 8 <=? zlen buf - 4) then (ip + bc / 8, bc mod 8) else (zlen buf - 4, (bc - 8 * (zlen buf - 4 - ip)) mod 32)) = ip' ->
snd (if (ip <=? zlen buf - 7) || (ip + bc / 8 <=? zlen buf - 4) then (ip + bc / 8, bc mod 8) else (zlen buf - 4, (bc - 8 * (zlen buf - 4 - ip)) mod 32)) = bc' ->
y14 = Z_to_bv 64 (BUF + ip') -> y22 = Z_to_bv 64 bc' ->
evt psegs POST (rd_lst C 0x14194 m1 y1 (Z_to_bv 64 rem) y14 (Z_to_bv 64 thr) y22 (Z_to_bv 64 cn) (Z_to_bv 64 count) y25 y26 y27 (Z_to_bv 64 nb))).
{ intros ip' bc' y1 y14 y22 y25 y26 y27 E1 E2 -> ->. rewrite E1, E2 in *.
eapply (cnt_load (FseNCount.mkR nc ip' (le32 buf ip' / 2 ^ bc') bc' cn rem thr nb (count =? 0)) m1 msvw tlw count ip'); try eassumption; try reflexivity; cbnR; try lia; try reflexivity. }
clear K. unfold rd_lst in LOAD |- *.
zstep. rewrite signed_lit by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
zstep.
if_cases B1; zify_cond B1.
-
zstep. zstep.
if_cases B2; zify_cond B2.
+
replace ((ip <=? zlen buf - 7) || (ip + bc / 8 <=? zlen buf - 4)) with true in LOAD
by (symmetry; apply orb_true_iff; right; apply Z.leb_le; lia).
zstep. zstep. rewrite land_7.
eapply (LOAD (ip + bc / 8) (bc mod 8)); first [reflexivity | f_equal; lia].
+ replace ((ip <=? zlen buf - 7) || (ip + bc / 8 <=? zlen buf - 4)) with false in LOAD
by (symmetry; apply orb_false_iff; split; apply Z.leb_gt; lia).
zstep. replace (BUF + ip - (BUF + zlen buf + -4)) with (ip - zlen buf + 4) by lia.
rewrite (swrap32_small (ip - zlen buf + 4)) by lia.
zstep. zstep. zstep.
rewrite (clamp_bc bc (ip - zlen buf + 4)) by lia.
zstep. zstep.
eapply (LOAD (zlen buf - 4) ((bc - 8 * (zlen buf - 4 - ip)) mod 32)); first [reflexivity | f_equal; lia | f_equal; f_equal; lia].
- replace ((ip <=? zlen buf - 7) || (ip + bc / 8 <=? zlen buf - 4)) with true in LOAD
by (symmetry; apply orb_true_iff; left; apply Z.leb_le; lia).
zstep. zstep. rewrite land_7.
eapply (LOAD (ip + bc / 8) (bc mod 8)); first [reflexivity | f_equal; lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma cnt_hb : forall r m1 (x1 x14 x20 x22 x23 x24 x25 x26 x27 x30 : word),
2 <= r < 32768 ->
(forall y20 y30, y30 = Z_to_bv 64 (Z.log2 r + 1) -> y20 = Z_to_bv 64 (2 ^ Z.log2 r) ->
evt psegs POST (rd_lst C 0x14180 m1 x1 (Z_to_bv 64 r) x14 y20 x22 x23 x24 x25 x26 x27 y30)) ->
evt psegs POST (rd_lst C 0x14118 m1 x1 (Z_to_bv 64 r) x14 x20 x22 x23 x24 x25 x26 x27 x30).
Proof.
intros r m1 x1 x14 x20 x22 x23 x24 x25 x26 x27 x30 Hr K.
unfold rd_lst in *.
Local Ltac2 Set LiaHints.tbl := fun () => "00C0>13204214924.2014939502107.282546492593.32 28915217082.2928915217083.2829016324132.3729018421291.2834887345834.2941408184391.2852320880311.2852320880312.2759586081466.2959586081467.2864344627643.286746801846.29 8935173665.32 8937270820.27 8937270822.25 8937270827.28 00000400500600700800<00@00A00B00C00D00E00F00G00H00I00J00K00LS2HrFSSSS2HrS2HrFSFFSSSSFFFF".
zstep. zstep. brute_reg 30 r 2 32766 sm1.
zstep. zstep. brute_reg 30 r 2 32766 sm2.
zstep. zstep. brute_reg 30 r 2 32766 sm3.
zstep. zstep. brute_reg 30 r 2 32766 sm4.
zstep. zstep. brute_reg 30 r 2 32766 sm5.
do 13 zstep.
brute_reg 30 r 2 32766 (fun r0 => 31 - Z.log2 r0).
zstep. zstep. zstep.
brute_reg 30 r 2 32766 (fun r0 => Z.log2 r0 + 1).
brute_reg 20 r 2 32766 (fun r0 => 2 ^ Z.log2 r0).
apply K; reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="OK"] Lemma cnt_fin : forall s1 m1 msvw tlw count fl (x1 x25 x26 x27 : word),
rd_inv C m1 (r_nc s1) msvw tlw ->
0 <= r_ip s1 -> r_ip s1 + 4 <= zlen buf -> 0 <= r_bitCount s1 < 64 -> 1 <= r_charnum s1 <= msv1 -> 1 <= r_remaining s1 < 2^31 ->
r_previous0 s1 = (count =? 0) -> -1 <= count < 2^31 ->
(if msv1 <=? r_charnum s1 then Ok (Brk s1) else let! s2 := reload buf s1 in Ok (Cont s2)) = Ok fl ->
(forall s' m2 y1 y20 y23 y24 y26 y27 y30, fl = Brk s' -> rd_inv C m2 (r_nc s') msvw tlw -> rd_brk_ok C s' ->
evt psegs POST (rd_exit C s' m2 y1 y20 y23 y24 y26 y27 y30)) ->
(forall s' m2 y1 y25 y26 y27, fl = Cont s' -> rd_inv C m2 (r_nc s') msvw tlw ->
evt psegs POST (rd_head C s' m2 y1 y25 y26 y27)) ->
evt psegs POST (rd_lst C 0x14180 m1 x1 (Z_to_bv 64 (r_remaining s1)) (Z_to_bv 64 (BUF + r_ip s1)) (Z_to_bv 64 (r_threshold s1))
(Z_to_bv 64 (r_bitCount s1)) (Z_to_bv 64 (r_charnum s1)) (Z_to_bv 64 count) x25 x26 x27 (Z_to_bv 64 (r_nbBits s1))).
Proof.
intros s1 m1 msvw tlw count fl x1 x25 x26 x27 INV Hip0 Hip4 Hbc Hcn Hrem Ep0 Hcount RR KB KC.
pose proof OK as OK'. destruct OK' as (HH & _ & HM0 & _).
destruct (Z.leb_spec msv1 (r_charnum s1)) as [GE|LT].
-
injection RR as <-.
pose proof (KB s1 m1) as KB'. unfold rd_exit, rd_lst in KB'.
destruct s1 as [nc ip bs bc cn rem thr nb p0]. cbnR.
unfold rd_lst.
zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0070>10429784937.3718302863776.3718302863776.4119622043024.3719622043024.4159315036641.3759315036641.4100000L00U00a00f00k011017S4Hip04Hip43Hbc3Hcn4Hrem3HM0S3Hcn3HM0S3Hcn3HM02LTS3HM0S3HM0S2GE1BS2LT1B".
if_cases B; zify_cond B; [| exfalso; lia].
zstep.
eapply KB'; [reflexivity| exact INV|]. unfold rd_brk_ok. cbnR. change (2^31) with 2147483648 in *. lia.
- destruct (reload buf s1) as [s2| | |] eqn:RL; cbn [bind] in RR; try discriminate RR. injection RR as <-.
pose proof (fun y1 y25 y26 y27 => KC s2 m1 y1 y25 y26 y27 eq_refl) as KC'.
assert (INV2 : rd_inv C m1 (r_nc s2) msvw tlw).
{ pose proof (reload_inv buf s1 s2 (buf_all_bytes C OK) RL Hip0 Hip4 (proj1 Hbc)) as RI. cbv zeta in RI.
destruct RI as (_ & _ & _ & ->). cbnR. exact INV. }
specialize (fun y1 y25 y26 y27 => KC' y1 y25 y26 y27 INV2).
pose proof (cnt_reload s1 s2 m1 msvw tlw count) as CR. unfold rd_lst in CR.
destruct s1 as [nc ip bs bc cn rem thr nb p0]. cbnR.
unfold rd_lst.
zstep. if_cases B; zify_cond B; [exfalso; lia|].
eapply CR; try eassumption; cbnR; try lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End Count1.
