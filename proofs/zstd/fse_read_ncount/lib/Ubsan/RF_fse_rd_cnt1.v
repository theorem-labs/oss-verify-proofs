(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Spec Require Import FseNCount FseLemmas FseReadSound.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Common Require Import FseWalkKit FseRdKit FseRdKit2.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import UImg RF_fse_iface RF_fse_rd_base RdChk.
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
#[using="OK"] Lemma cnt_load : forall s2 m1 msvw tlw count ip' (x1 x6 x13 x14 x16 x26 x27 x28 : word),
rd_inv C m1 (r_nc s2) msvw tlw ->
0 <= ip' -> ip' + 4 <= zlen buf -> 0 <= r_bitCount s2 < 32 ->
r_ip s2 = ip' -> r_bitStream s2 = le32 buf ip' / 2 ^ r_bitCount s2 -> r_previous0 s2 = (count =? 0) ->
-1 <= count < 2^31 ->
x16 = Z_to_bv 64 count -> x26 = Z_to_bv 64 (r_bitCount s2) -> x27 = Z_to_bv 64 (BUF + ip') ->
(forall y1 y6 y14 y16 y28, evt usegs POST (rd_head C s2 m1 y1 y6 y14 y16 y28)) ->
evt usegs POST (rd_lst C 0x143b4 m1 x1 x6 (Z_to_bv 64 (r_charnum s2)) x13 x14 x16 (Z_to_bv 64 (r_remaining s2))
 (Z_to_bv 64 (r_threshold s2)) x26 x27 x28 (Z_to_bv 64 (r_nbBits s2))).
Proof.
intros s2 m1 msvw tlw count ip' x1 x6 x13 x14 x16 x26 x27 x28 INV Hip0 Hip4 Hbc Eip Ebs Ep0 Hcount -> -> -> K.
destruct INV as (_ & _ & HBUF & _).
destruct (buf_rd C OK m1 ip' HBUF ltac:(lia)) as [RD0 R0].
destruct (buf_rd C OK m1 (ip' + 1) HBUF ltac:(lia)) as [RD1 R1].
destruct (buf_rd C OK m1 (ip' + 2) HBUF ltac:(lia)) as [RD2 R2].
destruct (buf_rd C OK m1 (ip' + 3) HBUF ltac:(lia)) as [RD3 R3].
rewrite !Z.add_assoc in RD1, RD2, RD3.
destruct s2 as [nc ip bs bc cn rem thr nb p0]. cbnR. subst ip p0.
pose proof K as K'. unfold rd_head, rd_lst in K'. cbnR.
unfold rd_lst.
zstep. cbv beta. zstep. cbv beta. zstep. cbv beta. zstep. cbv beta.
zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
rewrite le32_lb_raw by assumption. rewrite (Z.mod_small bc 32) by lia. rewrite Z.shiftr_div_pow2 by lia.
fold (le32 buf ip'). rewrite <- Ebs.
zstep.
if_cases B; zify_cond B.
-
assert (count = 0).
{ match type of B with context [0 <? ?e] => destruct (Z.ltb_spec 0 e) as [L|L] end; cbn in B; [discriminate B|].
  destruct (Z.eq_dec count (-1)) as [->|N]; [cbn in L; lia|]. rewrite Z.mod_small in L by lia. lia. }
subst count. change (0 =? 0) with true in K'. apply K'.
- assert (count <> 0).
{ intros ->. apply B. reflexivity. }
replace (count =? 0) with false in K' by (symmetry; apply Z.eqb_neq; assumption).
zstep. apply K'.
Qed.
#[using="Type"] Lemma ptr_add_chk : forall a d, 0 <= a -> a + d < 2^64 -> 0 <= d < 2^63 ->
Z.lxor (Z.lxor (Z.b2z (d + a <? a)) (Z.b2z (Z.lxor d (2^63) <? 2^63))) 1 = 1.
Proof.
intros a d Ha Had Hd. rewrite (proj2 (Z.ltb_ge (d + a) a)) by lia. rewrite zb_lxor_sign by lia.
rewrite Z.mod_small by lia. rewrite (proj2 (Z.ltb_ge _ _)) by lia. reflexivity.
Qed.
#[using="OK"] Lemma cnt_reload : forall s1 s2 m1 msvw tlw count (x6 x13 x14 x27 x28 : word),
rd_inv C m1 (r_nc s1) msvw tlw -> reload buf s1 = Ok s2 ->
0 <= r_ip s1 -> r_ip s1 + 4 <= zlen buf -> 0 <= r_bitCount s1 < 64 ->
r_previous0 s1 = (count =? 0) -> -1 <= count < 2^31 ->
(forall y1 y6 y14 y16 y28, evt usegs POST (rd_head C s2 m1 y1 y6 y14 y16 y28)) ->
evt usegs POST (rd_lst C 0x14384 m1 (Z_to_bv 64 (BUF + r_ip s1)) x6 (Z_to_bv 64 (r_charnum s1)) x13 x14 (Z_to_bv 64 count)
 (Z_to_bv 64 (r_remaining s1)) (Z_to_bv 64 (r_threshold s1)) (Z_to_bv 64 (r_bitCount s1)) x27 x28 (Z_to_bv 64 (r_nbBits s1))).
Proof.
intros s1 s2 m1 msvw tlw count x6 x13 x14 x27 x28 INV RL Hip0 Hip4 Hbc Ep0 Hcount K.
pose proof (reload_inv buf s1 s2 (buf_all_bytes C OK) RL Hip0 Hip4 (proj1 Hbc)) as RI. cbv zeta in RI.
destruct RI as (I1 & I2 & I3 & ->).
pose proof OK as OK'. destruct OK' as (HH & _ & _ & _ & _ & _ & _ & _ & (HB0 & HB1) & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HBP).
pose proof INV as (_ & _ & _ & _ & _ & (j0 & j16 & FR) & _).
destruct s1 as [nc ip bs bc cn rem thr nb p0]. cbnR. subst p0.
unfold reload_pos in *. unfold FseNCount.Zlength in *.
rewrite Z.shiftr_div_pow2 in * by lia. change (2^3) with 8 in *. rewrite land_7, land_31 in *.
assert (Q : 0 <= bc / 8 < 8) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
assert (LOAD : forall ip' bc' (y1 y6 y13 y14 y26 y27 y28 : word),
fst (if (ip <=? zlen buf - 7) || (ip + bc / 8 <=? zlen buf - 4) then (ip + bc / 8, bc mod 8) else (zlen buf - 4, (bc - 8 * (zlen buf - 4 - ip)) mod 32)) = ip' ->
snd (if (ip <=? zlen buf - 7) || (ip + bc / 8 <=? zlen buf - 4) then (ip + bc / 8, bc mod 8) else (zlen buf - 4, (bc - 8 * (zlen buf - 4 - ip)) mod 32)) = bc' ->
y27 = Z_to_bv 64 (BUF + ip') -> y26 = Z_to_bv 64 bc' ->
evt usegs POST (rd_lst C 0x143b4 m1 y1 y6 (Z_to_bv 64 cn) y13 y14 (Z_to_bv 64 count) (Z_to_bv 64 rem) (Z_to_bv 64 thr) y26 y27 y28 (Z_to_bv 64 nb))).
{ intros ip' bc' y1 y6 y13 y14 y26 y27 y28 E1 E2 -> ->. rewrite E1, E2 in *.
eapply (cnt_load (FseNCount.mkR nc ip' (le32 buf ip' / 2 ^ bc') bc' cn rem thr nb (count =? 0)) m1 msvw tlw count ip'); try eassumption; try reflexivity; cbnR; try lia; try reflexivity. }
clear K. unfold rd_lst in LOAD |- *.
zstep. if_cases B0; zify_cond B0; [exfalso; lia|].
zstep. rewrite signed_lit by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
zstep. zstep. zstep.
zstep. if_cases B1; zify_cond B1.
- replace ((ip <=? zlen buf - 7) || (ip + bc / 8 <=? zlen buf - 4)) with (ip + bc / 8 <=? zlen buf - 4) in LOAD
by (destruct (Z.leb_spec ip (zlen buf - 7)); [lia|reflexivity]).
zstep. if_cases B2; zify_cond B2; [exfalso; lia|].
zstep. zstep. zstep. if_cases B3; zify_cond B3; [rewrite ptr_add_chk in B3 by lia; discriminate B3|].
zstep. zstep. zstep. if_cases B4; zify_cond B4.
+ replace (ip + bc / 8 <=? zlen buf - 4) with true in LOAD by (symmetry; apply Z.leb_le; lia).
zstep. if_cases B5; zify_cond B5; [exfalso; lia|].
zstep. zstep. zstep. if_cases B6; zify_cond B6; [rewrite ptr_add_chk in B6 by lia; discriminate B6|].
zstep. zstep. if_cases B7; zify_cond B7; [exfalso; lia|].
eapply (LOAD (ip + bc / 8) (bc mod 8)); first [reflexivity | f_equal; lia | rewrite land_7; reflexivity].
+ replace (ip + bc / 8 <=? zlen buf - 4) with false in LOAD by (symmetry; apply Z.leb_gt; lia).
zstep. zstep. zstep. zstep. zstep. zstep. zstep. shr61.
zstep. zstep. zstep. zstep. chk64.
zstep. zstep. zstep. if_cases B5; zify_cond B5; [|exfalso; lia].
eapply (LOAD (zlen buf - 4) ((bc - 8 * (zlen buf - 4 - ip)) mod 32)); first [reflexivity | f_equal; lia | idtac].
f_equal. rewrite !land_31. rewrite Z.shiftl_mul_pow2 by lia. rewrite ?swrap32_eq. Z.div_mod_to_equations. lia.
- replace ((ip <=? zlen buf - 7) || (ip + bc / 8 <=? zlen buf - 4)) with true in LOAD
by (symmetry; apply orb_true_iff; left; apply Z.leb_le; lia).
zstep. if_cases B4; zify_cond B4; [exfalso; lia|].
zstep. zstep. zstep. if_cases B5; zify_cond B5; [rewrite ptr_add_chk in B5 by lia; discriminate B5|].
zstep. zstep. if_cases B6; zify_cond B6; [exfalso; lia|].
eapply (LOAD (ip + bc / 8) (bc mod 8)); first [reflexivity | f_equal; lia | rewrite land_7; reflexivity].
Qed.
#[using="Type"] Lemma cnt_hb : forall r m1 (x1 x6 x11 x13 x14 x16 x25 x26 x27 x28 x29 : word),
2 <= r < 32768 ->
(forall y13 y14 y25 y29, y29 = Z_to_bv 64 (Z.log2 r + 1) -> y25 = Z_to_bv 64 (2 ^ Z.log2 r) ->
 evt usegs POST (rd_lst C 0x14380 m1 x1 x6 x11 y13 y14 x16 (Z_to_bv 64 r) y25 x26 x27 x28 y29)) ->
evt usegs POST (rd_lst C 0x14314 m1 x1 x6 x11 x13 x14 x16 (Z_to_bv 64 r) x25 x26 x27 x28 x29).
Proof.
intros r m1 x1 x6 x11 x13 x14 x16 x25 x26 x27 x28 x29 Hr K.
unfold rd_lst in *.
zstep. zstep. brute_reg 13 r 2 32768 sm1.
zstep. zstep. brute_reg 13 r 2 32768 sm2.
zstep. zstep. brute_reg 13 r 2 32768 sm3.
zstep. zstep. brute_reg 13 r 2 32768 sm4.
zstep. zstep. brute_reg 13 r 2 32768 sm5.
do 13 zstep.
brute_reg 13 r 2 32768 (fun r0 => 31 - Z.log2 r0).
zstep. zstep. zstep. zstep.
brute_reg 29 r 2 32768 (fun r0 => Z.log2 r0 + 1).
brute_reg 25 r 2 32768 (fun r0 => 2 ^ Z.log2 r0).
apply K; reflexivity.
Qed.
#[using="OK"] Lemma cnt_fin : forall s1 m1 msvw tlw count fl (x6 x13 x14 x27 x28 : word),
rd_inv C m1 (r_nc s1) msvw tlw ->
0 <= r_ip s1 -> r_ip s1 + 4 <= zlen buf -> 0 <= r_bitCount s1 < 64 -> 1 <= r_charnum s1 <= msv1 -> 1 <= r_remaining s1 < 2^31 ->
r_previous0 s1 = (count =? 0) -> -1 <= count < 2^31 ->
(if msv1 <=? r_charnum s1 then Ok (Brk s1) else let! s2 := reload buf s1 in Ok (Cont s2)) = Ok fl ->
(forall s' m2 y1 y6 y13 y14 y16 y25 y28 y29, fl = Brk s' -> rd_inv C m2 (r_nc s') msvw tlw -> rd_brk_ok C s' ->
 evt usegs POST (rd_exit C s' m2 y1 y6 y13 y14 y16 y25 y28 y29)) ->
(forall s' m2 y1 y6 y14 y16 y28, fl = Cont s' -> rd_inv C m2 (r_nc s') msvw tlw ->
 evt usegs POST (rd_head C s' m2 y1 y6 y14 y16 y28)) ->
evt usegs POST (rd_lst C 0x14380 m1 (Z_to_bv 64 (BUF + r_ip s1)) x6 (Z_to_bv 64 (r_charnum s1)) x13 x14 (Z_to_bv 64 count)
 (Z_to_bv 64 (r_remaining s1)) (Z_to_bv 64 (r_threshold s1)) (Z_to_bv 64 (r_bitCount s1)) x27 x28 (Z_to_bv 64 (r_nbBits s1))).
Proof.
intros s1 m1 msvw tlw count fl x6 x13 x14 x27 x28 INV Hip0 Hip4 Hbc Hcn Hrem Ep0 Hcount RR KB KC.
pose proof OK as OK'. destruct OK' as (HH & _ & HM0 & _).
destruct (Z.leb_spec msv1 (r_charnum s1)) as [GE|LT].
-
injection RR as <-.
pose proof (KB s1 m1) as KB'. unfold rd_exit, rd_lst in KB'.
destruct s1 as [nc ip bs bc cn rem thr nb p0]. cbnR.
unfold rd_lst.
zstep. if_cases B; zify_cond B; [| exfalso; lia].
zstep.
eapply KB'; [reflexivity| exact INV|]. unfold rd_brk_ok. cbnR. change (2^31) with 2147483648 in *. lia.
- destruct (reload buf s1) as [s2| | |] eqn:RL; cbn [bind] in RR; try discriminate RR. injection RR as <-.
pose proof (fun y1 y6 y14 y16 y28 => KC s2 m1 y1 y6 y14 y16 y28 eq_refl) as KC'.
assert (INV2 : rd_inv C m1 (r_nc s2) msvw tlw).
{ pose proof (reload_inv buf s1 s2 (buf_all_bytes C OK) RL Hip0 Hip4 (proj1 Hbc)) as RI. cbv zeta in RI.
destruct RI as (_ & _ & _ & ->). cbnR. exact INV. }
specialize (fun y1 y6 y14 y16 y28 => KC' y1 y6 y14 y16 y28 INV2).
pose proof (cnt_reload s1 s2 m1 msvw tlw count) as CR. unfold rd_lst in CR.
destruct s1 as [nc ip bs bc cn rem thr nb p0]. cbnR.
unfold rd_lst.
zstep. if_cases B; zify_cond B; [exfalso; lia|].
eapply CR; try eassumption; cbnR; try lia.
Qed.
End Count1.
