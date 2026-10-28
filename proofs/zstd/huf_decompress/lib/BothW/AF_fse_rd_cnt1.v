(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas FseReadSound.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseRdKit.
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
#[using="rc OK RNGS"] Lemma cnt_loadA : forall s2 m1 msvw tlw count ip' (x6 x7 x12 x20 x29 : word),
rd_invA C m1 (r_nc s2) msvw tlw ->
0 <= ip' -> ip' + 4 <= zlen buf -> 0 <= r_bitCount s2 < 32 ->
r_ip s2 = ip' -> r_bitStream s2 = le32 buf ip' / 2 ^ r_bitCount s2 -> r_previous0 s2 = (count =? 0) ->
-1 <= count < 2^31 ->
(forall y7 y12 y20 y22 y29, evtF bsegs RNG POST (rd_headA C s2 m1 y7 y12 y20 y22 y29)) ->
evtF bsegs RNG POST (rd_lstA C 0x97068 m1 (Z_to_bv 64 (r_nbBits s2)) x6 x7 (Z_to_bv 64 (BUF + ip')) (Z_to_bv 64 (r_remaining s2)) x12
(Z_to_bv 64 (r_charnum s2)) (Z_to_bv 64 (r_bitCount s2)) (Z_to_bv 64 (r_threshold s2)) x20 (Z_to_bv 64 count) x29).
Proof.
intros s2 m1 msvw tlw count ip' x6 x7 x12 x20 x29 INV Hip0 Hip4 Hbc Eip Ebs Ep0 Hcount K.
destruct RNGS as (RI & RSTK & RN & RNS & RM & RMS & RT & RTS & RB & RBS).
destruct INV as (_ & _ & HBUF & _).
destruct (buf_rdA C OK m1 ip' HBUF ltac:(lia)) as [RD0 R0].
destruct (buf_rdA C OK m1 (ip' + 1) HBUF ltac:(lia)) as [RD1 R1].
destruct (buf_rdA C OK m1 (ip' + 2) HBUF ltac:(lia)) as [RD2 R2].
destruct (buf_rdA C OK m1 (ip' + 3) HBUF ltac:(lia)) as [RD3 R3].
rewrite !Z.add_assoc in RD1, RD2, RD3.
destruct s2 as [nc ip bs bc cn rem thr nb p0]. cbnR. subst ip p0.
unfold rd_lstA.
zstep. cbv beta. zstep. cbv beta. zstep. cbv beta. zstep. cbv beta.
zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
rewrite le32_lb_raw by assumption. rewrite (Z.mod_small bc 32) by lia. rewrite (Z.shiftr_div_pow2 _ bc) by lia.
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
Qed.
#[using="rc OK RNGS"] Lemma rl_chk2 : forall m1 ip' (x1 x6 x7 x11 x12 x13 x16 x18 x20 x22 x29 : word),
unpoisoned m1 BUF (BUF + zlen buf) -> 0 <= ip' -> ip' + 4 <= zlen buf ->
(forall y6 y7 y12, evtF bsegs RNG POST (rd_lstA C 0x97068 m1 x1 y6 y7 (Z_to_bv 64 (BUF + ip')) x11 y12 x13 x16 x18 x20 x22 x29)) ->
evtF bsegs RNG POST (rd_lstA C 0x97054 m1 x1 x6 x7 (Z_to_bv 64 (BUF + ip')) x11 x12 x13 x16 x18 x20 x22 x29).
Proof.
intros m1 ip' x1 x6 x7 x11 x12 x13 x16 x18 x20 x22 x29 UB P0 P4 K.
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
#[using="rc OK RNGS"] Lemma rl_chk1 : forall m1 ip' (x1 x6 x7 x11 x12 x13 x16 x18 x20 x22 x29 : word),
unpoisoned m1 BUF (BUF + zlen buf) -> 0 <= ip' -> ip' + 4 <= zlen buf ->
(forall y6 y12, evtF bsegs RNG POST (rd_lstA C 0x97054 m1 x1 y6 x7 (Z_to_bv 64 (BUF + ip')) x11 y12 x13 x16 x18 x20 x22 x29)) ->
evtF bsegs RNG POST (rd_lstA C 0x97044 m1 x1 x6 x7 (Z_to_bv 64 (BUF + ip')) x11 x12 x13 x16 x18 x20 x22 x29).
Proof.
intros m1 ip' x1 x6 x7 x11 x12 x13 x16 x18 x20 x22 x29 UB P0 P4 K.
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
#[using="rc OK SH RNGS"] Lemma cnt_reloadA : forall s1 s2 m1 msvw tlw count (x6 x7 x10 x20 x29 : word),
rd_invA C m1 (r_nc s1) msvw tlw -> reload buf s1 = Ok s2 ->
0 <= r_ip s1 -> r_ip s1 + 4 <= zlen buf -> 0 <= r_bitCount s1 < 64 ->
r_previous0 s1 = (count =? 0) -> -1 <= count < 2^31 ->
(forall y7 y12 y20 y22 y29, evtF bsegs RNG POST (rd_headA C s2 m1 y7 y12 y20 y22 y29)) ->
evtF bsegs RNG POST (rd_lstA C 0x97010 m1 (Z_to_bv 64 (r_nbBits s1)) x6 x7 x10 (Z_to_bv 64 (r_remaining s1)) (Z_to_bv 64 (BUF + r_ip s1))
(Z_to_bv 64 (r_charnum s1)) (Z_to_bv 64 (r_bitCount s1)) (Z_to_bv 64 (r_threshold s1)) x20 (Z_to_bv 64 count) x29).
Proof.
intros s1 s2 m1 msvw tlw count x6 x7 x10 x20 x29 INV RL Hip0 Hip4 Hbc Ep0 Hcount K.
pose proof (reload_inv buf s1 s2 (buf_all_bytesA C OK) RL Hip0 Hip4 (proj1 Hbc)) as RI. cbv zeta in RI.
destruct RI as (I1 & I2 & I3 & ->).
pose proof RNGS as RNGS'. destruct RNGS' as (RIM & RSTK & RN & RNS & RM & RMS & RT & RTS & RB & RBS).
pose proof OK as OK'. destruct OK' as (HH & _ & _ & _ & _ & SP16 & SPK & LOS & LOA & _ & _ & _ & _ & _ & _ & BB & _ & _ & _ & _ & _ & _ & _ & _ & B8).
pose proof (spaA_bounds C SP16) as [[SPA1 SPA2] SPA3].
pose proof (ablk_lin _ _ BB) as LBB. pose proof atop_range as ATR. unfold RDA_CALLEE, KHIGH, AIMG_HI, KEND in *.
pose proof INV as INV'. destruct INV' as (_ & _ & _ & _ & _ & (j0 & j64 & FRM) & _ & MU & _). unfold FRA_main in FRM.
destruct (inv_shadowA C m1 OK SH MU) as (_ & _ & _ & UB).
destruct s1 as [nc ip bs bc cn rem thr nb p0]. cbnR. subst p0.
unfold reload_pos in *. unfold FseNCount.Zlength in *.
rewrite Z.shiftr_div_pow2 in * by lia. change (2^3) with 8 in *. rewrite land_7, land_31 in *.
assert (Q : 0 <= bc / 8 < 8) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
assert (LOAD : forall ip' bc' (y6 y7 y12 y20 y29 : word),
fst (if (ip <=? zlen buf - 7) || (ip + bc / 8 <=? zlen buf - 4) then (ip + bc / 8, bc mod 8) else (zlen buf - 4, (bc - 8 * (zlen buf - 4 - ip)) mod 32)) = ip' ->
snd (if (ip <=? zlen buf - 7) || (ip + bc / 8 <=? zlen buf - 4) then (ip + bc / 8, bc mod 8) else (zlen buf - 4, (bc - 8 * (zlen buf - 4 - ip)) mod 32)) = bc' ->
evtF bsegs RNG POST (rd_lstA C 0x97044 m1 (Z_to_bv 64 nb) y6 y7 (Z_to_bv 64 (BUF + ip')) (Z_to_bv 64 rem) y12 (Z_to_bv 64 cn)
(Z_to_bv 64 bc') (Z_to_bv 64 thr) y20 (Z_to_bv 64 count) y29)).
{ intros ip' bc' y6 y7 y12 y20 y29 E1 E2. rewrite E1, E2 in *.
eapply (rl_chk1 m1 ip'); [exact UB| lia| lia|]. intros z6 z12.
eapply (rl_chk2 m1 ip'); [exact UB| lia| lia|]. intros w6 w7 w12.
eapply (cnt_loadA (FseNCount.mkR nc ip' (le32 buf ip' / 2 ^ bc') bc' cn rem thr nb (count =? 0)) m1 msvw tlw count ip');
try eassumption; try reflexivity; cbnR; try lia; try reflexivity. }
clear K.
assert (T8 : forall (y7 y20 : word),
(ip <=? zlen buf - 7) || (ip + bc / 8 <=? zlen buf - 4) = true ->
evtF bsegs RNG POST (rd_lstA C 0x9702c m1 (Z_to_bv 64 nb) (Z_to_bv 64 0) y7 (Z_to_bv 64 (bc / 8 + (BUF + ip))) (Z_to_bv 64 rem)
(Z_to_bv 64 (BUF + ip)) (Z_to_bv 64 cn) (Z_to_bv 64 bc) (Z_to_bv 64 thr) y20 (Z_to_bv 64 count) (Z_to_bv 64 0))).
{ intros y7 y20 EC. rewrite EC in LOAD. unfold rd_lstA in LOAD |- *.
zstep. if_cases G2; zify_cond G2; [exfalso; lia|].
zstep. zstep. zstep. if_false.
zstep. rewrite land_7. zstep. if_cases G3; zify_cond G3; [exfalso; lia|].
replace (bc / 8 + (BUF + ip)) with (BUF + (ip + bc / 8)) by lia.
eapply (LOAD (ip + bc / 8) (bc mod 8)); first [reflexivity | f_equal; lia]. }
unfold rd_lstA in LOAD, T8 |- *.
zstep. zstep. if_cases G1; zify_cond G1; [exfalso; lia|].
zstep. rewrite signed_lit by lia. rewrite (Z.shiftr_div_pow2 bc 3) by lia. change (2^3) with 8.
zstep. zstep.
replace (bc / 8 + (BUF + ip) <? BUF + ip) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
zstep.
replace (Z.lxor (bc / 8) 9223372036854775808 <? 0 + 9223372036854775808) with false
by (symmetry; apply Z.ltb_ge; change 9223372036854775808 with (2^63); rewrite zb_lxor_pow2_small by lia; lia).
cbn [Z.b2z].
zstep.
if_cases B1; zify_cond B1.
-
zstep. if_cases G5; zify_cond G5; [exfalso; lia|].
zstep. zstep. zstep. if_false.
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
#[using="rc OK RNGS"] Lemma cnt_hbA : forall r m1 nc msvw tlw (x1 x6 x7 x10 x12 x13 x16 x18 x20 x22 x29 : word),
rd_invA C m1 nc msvw tlw -> 2 <= r < 32768 ->
(forall y1 y6 y7 y10 y18, y1 = Z_to_bv 64 (Z.log2 r + 1) -> y18 = Z_to_bv 64 (2 ^ Z.log2 r) ->
evtF bsegs RNG POST (rd_lstA C 0x9700c m1 y1 y6 y7 y10 (Z_to_bv 64 r) x12 x13 x16 y18 x20 x22 x29)) ->
evtF bsegs RNG POST (rd_lstA C 0x96f90 m1 x1 x6 x7 x10 (Z_to_bv 64 r) x12 x13 x16 x18 x20 x22 x29).
Proof.
intros r m1 nc msvw tlw x1 x6 x7 x10 x12 x13 x16 x18 x20 x22 x29 INV Hr K.
pose proof INV as INV'. destruct INV' as (_ & _ & _ & _ & _ & (j0 & j64 & FRM) & _). unfold FRA_main in FRM.
pose proof RNGS as RNGS'. destruct RNGS' as (RIM & RSTK & _).
pose proof OK as OK'. destruct OK' as (_ & _ & _ & _ & _ & SP16 & SPK & LOS & LOA & _).
pose proof (spaA_bounds C SP16) as [[SPA1 SPA2] SPA3]. pose proof atop_range as ATR. unfold RDA_CALLEE, KHIGH, KEND in *.
unfold rd_lstA in *.
zstep. zstep. brute_regF 10 r 2 32766 sm1.
zstep. zstep. brute_regF 10 r 2 32766 sm2.
zstep. zstep. brute_regF 10 r 2 32766 sm3.
zstep. zstep. brute_regF 10 r 2 32766 sm4.
zstep. zstep. brute_regF 10 r 2 32766 sm5.
do 16 zstep.
brute_regF 10 r 2 32766 (fun r0 => 31 - Z.log2 r0).
zstep. zstep. zstep.
brute_regF 1 r 2 32766 (fun r0 => Z.log2 r0 + 1).
zstep. zstep.
brute_regF 18 r 2 32766 (fun r0 => 2 ^ Z.log2 r0).
eapply K; reflexivity.
Qed.
#[using="rc OK SH RNGS"] Lemma cnt_finA : forall s1 m1 msvw tlw count fl (x6 x7 x10 x20 x29 : word),
rd_invA C m1 (r_nc s1) msvw tlw ->
0 <= r_ip s1 -> r_ip s1 + 4 <= zlen buf -> 0 <= r_bitCount s1 < 64 -> 1 <= r_charnum s1 <= msv1 -> 1 <= r_remaining s1 < 2^31 ->
r_previous0 s1 = (count =? 0) -> -1 <= count < 2^31 ->
(if msv1 <=? r_charnum s1 then Ok (Brk s1) else let! s2 := reload buf s1 in Ok (Cont s2)) = Ok fl ->
(forall s' m2 y1 y6 y7 y12 y18 y20 y22 y29, fl = Brk s' -> rd_invA C m2 (r_nc s') msvw tlw -> rd_brk_okA C s' ->
evtF bsegs RNG POST (rd_exitA C s' m2 y1 y6 y7 y12 y18 y20 y22 y29)) ->
(forall s' m2 y7 y12 y20 y22 y29, fl = Cont s' -> rd_invA C m2 (r_nc s') msvw tlw ->
evtF bsegs RNG POST (rd_headA C s' m2 y7 y12 y20 y22 y29)) ->
evtF bsegs RNG POST (rd_lstA C 0x9700c m1 (Z_to_bv 64 (r_nbBits s1)) x6 x7 x10 (Z_to_bv 64 (r_remaining s1)) (Z_to_bv 64 (BUF + r_ip s1))
(Z_to_bv 64 (r_charnum s1)) (Z_to_bv 64 (r_bitCount s1)) (Z_to_bv 64 (r_threshold s1)) x20 (Z_to_bv 64 count) x29).
Proof.
intros s1 m1 msvw tlw count fl x6 x7 x10 x20 x29 INV Hip0 Hip4 Hbc Hcn Hrem Ep0 Hcount RR KB KC.
pose proof OK as OK'. destruct OK' as (HH & _ & HM0 & _).
destruct (Z.leb_spec msv1 (r_charnum s1)) as [GE|LT].
-
injection RR as <-.
pose proof (KB s1 m1) as KB'. unfold rd_exitA, rd_lstA in KB'.
destruct s1 as [nc ip bs bc cn rem thr nb p0]. cbnR.
unfold rd_lstA.
zstep.
if_cases B; zify_cond B; [| exfalso; lia].
zstep.
eapply KB'; [reflexivity| exact INV|]. unfold rd_brk_okA. cbnR. change (2^31) with 2147483648 in *. lia.
- destruct (reload buf s1) as [s2| | |] eqn:RL; cbn [bind] in RR; try discriminate RR. injection RR as <-.
pose proof (fun y7 y12 y20 y22 y29 => KC s2 m1 y7 y12 y20 y22 y29 eq_refl) as KC'.
assert (INV2 : rd_invA C m1 (r_nc s2) msvw tlw).
{ pose proof (reload_inv buf s1 s2 (buf_all_bytesA C OK) RL Hip0 Hip4 (proj1 Hbc)) as RI. cbv zeta in RI.
destruct RI as (_ & _ & _ & ->). cbnR. exact INV. }
specialize (fun y7 y12 y20 y22 y29 => KC' y7 y12 y20 y22 y29 INV2).
pose proof (cnt_reloadA s1 s2 m1 msvw tlw count) as CR. unfold rd_lstA in CR.
destruct s1 as [nc ip bs bc cn rem thr nb p0]. cbnR.
unfold rd_lstA.
zstep. if_cases B; zify_cond B; [exfalso; lia|].
eapply CR; try eassumption; cbnR; try lia.
Qed.
End Count1.
End CANSEC1.
