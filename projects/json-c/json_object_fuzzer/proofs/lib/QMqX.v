(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs QCiC Qpj5 QvDJ Q6sh QQwg QKTr QJBH QZzg QTVW QbcP_c1 Q61C QWRO Qu4g QFQR QmP7 QnRU QKBN QN4c QNQk QpY2 QOJv Q9Ho QV3O QYyZ Qu3b QjgW QpME QpF1 QVo2 QQ8H Qx6U QmvA QRfV QEYd QcA6 QcfN QlES Qt1l QUYN QdWK QmZe Q6iK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Qpj5.Mq1 QvDJ.Mq2 Q6sh QQwg QKTr.
Import QJBH.
Import QZzg QTVW QbcP_c1 Q61C QWRO Qu4g QFQR QmP7 QnRU.Mqe QKBN QN4c QNQk.Mq6 QTVW.Mq7 QNQk.Mq8 QpY2.Mqi QTVW.Mqa QOJv.Mqb QNQk Q9Ho.Mq4 QV3O QnRU.Mql QmP7.Mq1 QpY2.Mqb Q9Ho.Mq3 QYyZ.Mq8 QnRU.Mqc QOJv.Mqc Qu3b QYyZ.Mqc QjgW QYyZ.Mqa QpME.Mq8 QpF1 QVo2.Mq2 QQ8H.Mq5 Qx6U.Mq6 QmvA.Mq5 QpME.Mqc QVo2.Mq4 QpY2.Mqc QRfV.Mq3 QnRU.Mqk QEYd.Mq0 Qx6U.Mq7 QcA6.Mq4 QcfN.Mq4 QpY2.Mqf.
Import QlES.
Import Qt1l QUYN QdWK QmZe.Mq4 Q6iK.Mq0.
Import ListNotations.
Import Qc6I.Exc. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Local Ltac Q0z1.tslia ::= tslia_rel. Local Ltac mkr__tslia_0 := tslia_rel.
Local Ltac lia ::= lia_walk_nf. Local Ltac mkr__lia_1 := lia_walk_nf.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.
Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).
Local Notation mem := (word -> option byte) (only parsing).

Section Lift.
Context {BAND : Band}.
Variables (C : arun_components) (LV : lvp).
Hypothesis HRT : ac_RTconst C = RTconst.
Hypothesis HRS : ac_RStats C = RStats.
Hypothesis HRP : ac_RPrim C = RPrim.
Hypothesis HRC : ac_RChunks C = RChunks.
Hypothesis HRSE : ac_RSec C = RSec.
Hypothesis HRQ : ac_RQuar C = QXcn.RQuar.
Hypothesis HRD : ac_RDepot C = RDepot.
Hypothesis HRF : ac_RFake C = QsJM.RFake.
Hypothesis large_alloc_spec : forall RE X, large_alloc_stmt RE X LV.
Hypothesis poison_zero_spec : forall RE X, poison_zero_stmt_lh RE X LV.
Hypothesis OBL_RT_REPLACE_STR : forall RE X m, RTconst RE X m -> ro_cells asegs m (0x0ef9b8 + 29) [C1 (b8 1)].
Hypothesis OBL_RT_GOT_MEMCPY : forall RE X m, RTconst RE X m -> ro_cells asegs m 0x0e81e0 [C8 (wz 0x0ea1c8)].
Hypothesis OBL_MEMCPY : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (src junk : list byte),
bytes_at asegs m (bv_unsigned a1) src -> length src = Z.to_nat (bv_unsigned a2) ->
rw_cells asegs m (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) junk] ->
(bv_unsigned a1 + bv_unsigned a2 <= bv_unsigned a0 \/ bv_unsigned a0 + bv_unsigned a2 <= bv_unsigned a1)%Z ->
mem_inv asegs m ->
evt asegs (memcpy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 src m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xdda10) fc None m (seg_rom asegs)).

Definition strdup_W_sec (RE : aentry) (X : rlay) (bp : Z) : list (Z * Z) :=
(bp - STRDUP_STACK, bp) :: (rl_T X + 3168, rl_T X + 3169) :: (A_ERRNO, A_ERRNO + 4) :: tl (alloc_W_sec RE X (bp - 2160)).

Lemma lz_mono_sd : forall a RE X SP SP' mb msz x, SP <= SP' -> lz a RE X SP mb msz x -> lz a RE X SP' mb msz x.
Proof. intros a RE X SP SP' mb msz x LE [H|[H|[H|[H|H]]]]; unfold lz; [tauto| tauto| tauto| do 3 right; left; lia| tauto]. Qed.

Lemma strdup_W_sec_lz : forall a LB FS G RE X bp mb msz lo' hi' x,
gcons a LB FS G RE X -> band_lo <= bp - STRDUP_STACK -> 0 <= msz -> mb mod 8 = 0 ->
In (lo', hi') (strdup_W_sec RE X bp ++ [(mb, mb + msz); (SH mb, SH (mb + msz))]) -> lo' <= x < hi' -> lz a RE X bp mb msz x.
Proof.
intros a LB FS G RE X bp mb msz lo' hi' x GC CSP MSZ MB8 Hin Hx. unfold strdup_W_sec in Hin. unfold STRDUP_STACK in *.
cbn [app] in Hin. destruct Hin as [E|Hin].
- injection E as <- <-. do 3 right. left. lia.
- apply (lz_mono_sd a RE X (bp - 16) bp mb msz x ltac:(lia)).
apply (malloc_W_sec_lz a LB FS G RE X (bp - 16) mb msz lo' hi' x GC ltac:(unfold MALLOC_STACK; lia) MSZ MB8); [| exact Hx].
unfold malloc_W_sec. cbn [app]. right. replace (bp - 16 - 2144) with (bp - 2160) by lia. exact Hin.
Qed.

Lemma strdup_W_sec_z : forall a LB FS G RE X bp lo' hi' x,
gcons a LB FS G RE X -> band_lo <= bp - STRDUP_STACK ->
In (lo', hi') (strdup_W_sec RE X bp) -> lo' <= x < hi' -> fp_RStats RE X x \/ fp_RDepot RE X x \/ fp_RSec a RE X x \/ band_lo <= x < bp.
Proof.
intros a LB FS G RE X bp lo' hi' x GC CSP Hin Hx.
destruct (strdup_W_sec_lz a LB FS G RE X bp 0 0 lo' hi' x GC CSP ltac:(lia) eq_refl ltac:(apply in_app_iff; left; exact Hin) Hx) as [Z|[Z|[Z|[Z|Z]]]]; [tauto| tauto| tauto| tauto|].
exfalso. destruct Z as [[Z1 Z2]|[Z1 Z2]]; cbn [fst snd] in *; [lia|]. change (0 / 8) with 0 in Z2. lia.
Qed.

Lemma strdup_sec_A : forall L (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(s : PStateA) (LB : list ablock) (FS : list fframe) (RE : aentry) (b : ablock) (src lo : Z) (str : list byte) (dn : Z),
ae_L RE = L ->
ARUN C s LB FS RE m ->
In b LB -> ablk_addr b <= src -> src + Z.of_nat (length str) + 1 <= ablk_addr b + ablk_size b ->
bytes_at asegs m src (str ++ [b8 0]) -> ~ In (b8 0) str -> Z.of_nat (length str) + 1 <= 2^26 ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - STRDUP_STACK ->
mem_inv asegs m ->
tp = Z_to_bv 64 (ala_tp a_alayout) -> gp = Z_to_bv 64 (ala_gp a_alayout) ->
unw_readable asegs RE m (bv_unsigned sp) -> depot_n asegs m dn -> dn + 1 <= DEPOT_CAP ->
a0 = Z_to_bv 64 src ->
from_primary (Z.of_nat (length str) + 1) = false ->
@implMG PStateA asegs (at_nodeA LV asegs) _ (raw_malloc_A L (Z.of_nat (length str) + 1)) s
(fun r s' ms' => std_postA asegs a_alayout ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB FS lo m s' ms'
(fun a0' m' => (exists dn', depot_n asegs m' dn' /\ dn <= dn' <= dn + 1) /\ match r with
| None => a0' = Z_to_bv 64 0 /\ ARUN C s' LB FS RE m'
| Some p => exists A,
a0' = Z_to_bv 64 A /\ ablock_rangeA A (Z.of_nat (length str) + 1) /\ aptr_req p = Z.of_nat (length str) + 1
/\ ARUN C s' ((p, A, Z.of_nat (length str) + 1) :: LB) FS RE m'
/\ rw_cells asegs m' A [CB (S (length str)) (str ++ [b8 0])]
/\ blk_shadow asegs m' A (Z.of_nat (length str) + 1)
end))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 strdup_stub) fc None m (seg_rom asegs)).
Proof.
intros until dn; intros EL AR Hb HA1 HA2 SRC NZ NMAX ST CEIL LO MI -> -> UNW DNH DCAP -> HP.
cbn [ala_tp ala_gp a_alayout] in *.
pose proof DNH as [DNC DNP]. unfold DP_N in DNC.
pose proof CEIL as CEIL'. idtac. pose proof LO as LO0. unfold STRDUP_STACK in LO.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
set (n := Z.of_nat (length str) + 1) in *. set (bp := bv_unsigned sp) in *.

destruct b as [[p0 A0] n0]. cbn [ablk_addr ablk_size fst snd] in HA1, HA2.
pose proof (ARUN_block_range C _ _ _ _ _ _ AR Hb) as BR. cbn [ablk_addr ablk_size fst snd] in BR. destruct BR as ((APR & _) & _ & BN0 & BBL & _).
assert (KD : KHI <= src \/ (0 < src /\ src + n <= kLowEnd)).
{ rewrite ?KHI_eq. unfold kLowEnd. destruct APR as [[[AP1 AP2]|AP] _]; [right; unfold n; clear - AP1 AP2 HA1 HA2; lia| left; clear - AP HA1; lia]. }
pose proof (ARUN_block_shadow C _ _ _ _ _ _ _ _ AR Hb) as BSH.
pose proof (shadow_ok_sub m A0 n0 src n BSH HA1 ltac:(unfold n in *; lia) ltac:(unfold n; lia)) as SO.
destruct (ARUN_nbhd C HRP HRC HRQ HRF s LB FS RE m src n AR ltac:(left; exists p0, A0, n0; split; [exact Hb| split; unfold n in *; lia]) ltac:(unfold n; lia)) as [NW1 NW2].
destruct (ARUN_open C _ _ _ _ _ AR) as (X & G & LB0 & FS0 & PB & PF & AX).
destruct AX as (GC & R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8).
rewrite HRT in R1. rewrite HRS in R2. rewrite HRP in R3. rewrite HRC in R4. rewrite HRSE in R5. rewrite HRD in R7.
rename R1 into RT. rename R2 into RS. rename R5 into RSE. rename R7 into RD.
pose proof (gc_rlay _ _ _ _ _ _ GC) as RL. pose proof kconsts as (KR & KO & KS & K32 & KP & KU & KM & KX).
assert (Hn : 0 <= n <= 2^26) by (unfold n in *; lia).
pose proof (bytes_at_bound _ _ _ _ SRC) as SBD. rewrite length_app in SBD. cbn [length] in SBD.

assert (CSRC : forall x, src <= x < src + n -> aclient_addrA a_alayout LB FS bp x).
{ intros x Hx. right. right. left. exists (p0, A0, n0). split; [exact Hb|]. cbn [ablk_addr ablk_size fst snd]. unfold n in *. lia. }
assert (STU : src + Z.of_nat (length (str ++ [b8 0])) <= rl_T X + 3168 \/ rl_T X + 3169 <= src).
{ assert (LSB : Z.of_nat (length (str ++ [b8 0])) = n) by (rewrite length_app; cbn [length]; unfold n; lia). rewrite LSB.
destruct (Z_le_gt_dec (src + n) (rl_T X + 3168)) as [|G1]; [left; assumption|].
destruct (Z_le_gt_dec (rl_T X + 3169) src) as [|G2]; [right; assumption|]. exfalso.
apply (depot_client (ps_a s) LB0 FS0 G RE X LB FS bp (rl_T X + 3168) GC PB PF ltac:(unfold bp; lia)); [apply CSRC; lia|].
do 3 right. reflexivity. }
assert (SLO' : src + Z.of_nat (length (str ++ [b8 0])) <= lo) by (rewrite length_app; cbn [length]; unfold n in *; lia).
pose proof SRC as SRC0. hide SRC0.
apply raw_malloc_A_intro. rewrite <- EL.

pose proof (QKBN.rlay_obj_facts_lia RE X _ RL (T_obj RE X)) as (_ & TK & TB & _). cbn [fst snd] in TK, TB.
pose proof (QKBN.rlay_obj_facts_lia RE X _ RL (dn_obj RE X)) as (_ & NK & NC & _). cbn [fst snd] in NK, NC.
pose proof (QKBN.rlay_obj_facts_lia RE X _ RL (ssb_obj RE X)) as (_ & BK & BC & _). cbn [fst snd] in BK, BC.
pose proof (rlay_prim_facts RE X RL) as (_ & PK & PC & _ & QK & QC & _). unfold prim_hi in PC. unfold ptrarr_hi in QC. idtac. rewrite ?KHI_eq in PK.
change (al_space_beg (ae_L RE)) with (prim_lo RE) in PC. change (al_ptrarr (ae_L RE)) with (ptrarr_lo RE) in QC.
apply appr_to_lia in QK; [| lia| lia].
pose proof (munch_refl (strdup_W_sec RE X bp) m) as MU. pose proof (wmono_refl asegs m) as WM.
unfold strdup_W_sec, STRDUP_STACK, alloc_W_sec, ALLOC_STACK, SS_BASE, DP_END, A_ERRNO, A_INSTANCE in MU. cbn [tl app] in MU.

assert (SEF : forall mm mm' W, munch W mm mm' -> wmono asegs mm mm' ->
(forall lo' hi' z, In (lo', hi') W -> lo' <= z < hi' -> fp_RStats RE X z \/ fp_RDepot RE X z \/ band_lo <= z) ->
RSec (ps_a s) LB0 RE X mm -> RSec (ps_a s) LB0 RE X mm').
{ intros mm mm' W MUw WMw HW RSEw. eapply RSec_frame; [exact RSEw| exact WMw|]. eapply agree_on_of_munch; [exact MUw| exact WMw|]. intros z Fz _. apply outside_intro.
intros lo' hi' Hin Hz. destruct (HW lo' hi' z Hin Hz) as [P|[P|P]].
- exact (fpS_excl _ _ _ _ _ _ GC z P ltac:(right; left; exact Fz)).
- exact (fpD_excl _ _ _ _ _ _ GC z P ltac:(right; left; exact Fz)).
- pose proof (fp_lt_ceil _ _ _ _ _ _ GC z ltac:(do 4 right; left; exact Fz)). lia. }
apply aimplT_from_evt.
rewrite <- (Z_to_bv_bv_unsigned sp). fold bp.
eapply (strdup_p1 RE X (OBL_RT_REPLACE_STR RE X) m src lo bp str [] (str ++ [b8 0]) SRC eq_refl NZ SLO' ltac:(lia) SO NW1 NW2 KD ltac:(unfold n in *; lia) ltac:(unfold n in *; lia));
[exact RT| exact RL| exact MI| exact ST| exact CEIL'| exact LO0| unfold bp; lia| exact (RDepot_unw RE X _ RD)|].
intros mc ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' j1 j0 MUc WMc MIc STc FRc FR0c RTc SRCc TUc.
eapply (strdup_p2 RE X m src lo bp str (str ++ [b8 0]) SLO' STU);
[exact RT| exact RL| exact CEIL'| exact LO0| unfold bp; lia| exact UNW| exact MUc| exact WMc| exact MIc| exact STc| exact FRc| exact FR0c| exact SRCc| exact TUc|].
clear mc ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' j1 j0 MUc WMc MIc STc FRc FR0c RTc SRCc TUc.
intros m1 u0 u1 u2 u3 u4 u5 u6 u7 u8 u10 u11 u12 u13 sz q rest junk8 MU1 WM1 MI1 ST1 OBJ LQ SZR FR RT1 TU1 SRC1.
unfold sd_W in MU1.
assert (RS1 : RStats RE X m1).
{ eapply RStats_munch; [exact RS| exact MU1| exact WM1|]. constructor; [first [st_avoid_solve| eapply st_avoid_T; [eassumption| lia| lia]]|]. constructor; [st_avoid_solve| constructor]. }
assert (RSE1 : RSec (ps_a s) LB0 RE X m1).
{ eapply SEF; [exact MU1| exact WM1| | exact RSE]. intros lo' hi' z Hin Hz. cbn [In] in Hin. destruct Hin as [E|[E|[]]]; injection E as <- <-.
- do 2 right. idtac. lia.
- right; left. do 3 right. lia. }
assert (RD1 : RDepot RE X m1).
{ eapply RDepot_frame_unw; [exact RL| exact RD| exact WM1| | exact TU1]. eapply agree_on_of_munch; [exact MU1| exact WM1|]. intros z [Fz NZ'] _. cbn [outside].
pose proof (fp_lt_ceil _ _ _ _ _ _ GC z ltac:(do 5 right; left; exact Fz)). idtac. lia. }
phase_done MU m m1 MU1 WM1. clear RT RS RSE RD MI. try clear ST.
destruct (unw_obj_head _ _ _ _ _ _ OBJ LQ ltac:(lia)) as [OBJh (q30 & TRQ & LQ30)].

unfold asan_malloc_entry. carve_frame 16%nat ST1.
try match goal with H : rw_cells asegs _ (bp + -2144 + -16) _ |- _ => replace (bp + -2144 + -16) with (bp + -2160) in H by lia end.
try replace (bp + -2144 + -16) with (bp + -2160) in ST1 by lia.
pose proof (munch_refl [(bp - 2160, bp - 2144)] m1) as MUa. pose proof (wmono_refl asegs m1) as WMa.
step. stf. step.
step. step. step. stp. stp. step. stp.
step.
lazymatch type of MUa with munch _ _ ?mm =>
destruct (sz_frame RE X (ps_a s) LB0 FS0 G m1 mm _ GC MUa WMa ltac:(intros lo' hi' z Hin Hz; cbn [In] in Hin; destruct Hin as [E|[]]; injection E as <- <-; right; idtac; lia)) as (FT & _ & FD);
pose proof (FT RT1) as RT2; pose proof (FD RD1) as RD2;
assert (RSE2 : RSec (ps_a s) LB0 RE X mm) by (eapply SEF; [exact MUa| exact WMa| intros lo' hi' z Hin Hz; cbn [In] in Hin; destruct Hin as [E|[]]; injection E as <- <-; do 2 right; idtac; lia| exact RSE1]);
assert (RS2 : RStats RE X mm) by (eapply RStats_munch; [exact RS1| exact MUa| exact WMa| constructor; [st_avoid_solve| constructor]]) end.
clear FT FD RT1 RSE1 RD1 RS1 MUa WMa.
apply evt_done. change (wz 977752) with (wz A_INSTANCE).
eapply aimplT_then.
{ eapply (allocate_sec_spec LV RE X (large_alloc_spec RE X) (poison_zero_spec RE X) _ _ (wz 67584) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ s (ps_a s) G LB0 FS0 n 1 lo (bp + -2144) sz dn q30 GC RT2 RS2 RSE2 RD2);
[assumption| rewrite unsigned_lit by lia; exact ST1| exact CEIL'| rewrite unsigned_lit by lia; unfold ALLOC_STACK; lia| exact Hn| exact HP| lia
| exact OBJh| exact TRQ| exact LQ30| exact SZR| split; [unfold DP_N; exact DNC| exact DNP]| exact DCAP| rewrite unsigned_lit by lia; lia| lia]. }
intros [r a'] s' ms' PO. unfold alloc_post_sec in PO. rewrite !(unsigned_lit (bp + -2160)) in PO by lia.
destruct PO as (y0 & y1 & y2 & z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & y3 & y4 & y5 & y6 & m3 & -> & -> & WM3 & MI3 & ST3 & RT3 & RS3 & RD3 & DS3 & OBJ3 & TRQ3 & REST).
destruct (DS3 dn ltac:(split; [unfold DP_N; exact DNC| exact DNP]) ltac:(unfold DEPOT_CAP in DCAP; lia)) as (dn3 & [DNC3 DNP3] & DNR3). unfold DP_N in DNC3. clear DNC.
replace (ret_pc (wz 258660)) with (wz 258660) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
unfold alloc_W_sec, ALLOC_STACK, SS_BASE, DP_END, A_INSTANCE in REST.
clear OBJh TRQ RT2 RSE2 RD2 RS2.

assert (FRALL : forall mx, rw_cells asegs mx (bp + -2144) (unw_obj (bp + -2144) sz q rest bp) ->
rw_cells asegs mx (bp + -80) [CB 8 junk8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
rw_cells asegs mx (bp + -2144) (unw_obj (bp + -2144) sz q rest bp ++ [CB 8 junk8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])).
{ intros mx O1 O2. apply (proj2 (rw_cells_app asegs mx _ _ _)). split; [exact O1|].
destruct q as [|w0 [|w1 [|w2 [|w3 [|w4 [|w5 q']]]]]]; cbn in LQ; try (clear - LQ; lia).
unfold unw_obj. cbn [cells_size csize Nat.add map app]. replace (bp + -2144 + Z.of_nat 2064) with (bp + -80) by lia. exact O2. }
destruct r as [pq|].
-
destruct REST as (mb & -> & REG & TQ & GQ & CLS & CI & NX & NR & SPN & MBP & MBK & MBC & ZA & -> & MUk & RSEk & CM & _).
pose proof MBK as MBK'. apply appr_to_lia in MBK'; [| pose proof (sec_map_size_ge n ltac:(lia) HP) as [SMG0 _]; lia| lia].
set (msz := sec_map_size n) in *.
assert (MS8 : 8 * (msz / 8) = msz /\ 4096 <= msz) by (pose proof (sec_geom_facts n Hn HP) as (G1 & _ & _ & _ & G5 & G6 & G7 & G8 & _); fold msz in G7, G8; clear - G1 G5 G6 G7 G8; Z.div_mod_to_equations; lia).
assert (SHM : SH (mb + msz) = SH mb + msz / 8) by (rewrite <- SH_plus8; f_equal; lia).
assert (MBH : 0x647000 <= mb) by (pose proof (sec_map_size_ge n ltac:(lia) HP) as [SMG _]; fold msz in SMG; pose proof (sec_req_facts n ltac:(lia) HP) as [_ RQn]; clear - MBK' SMG RQn; lia).
assert (SHB : 0x80000000 <= SH mb /\ SH mb + msz / 8 <= SH band_lo) by (unfold SH, A_SHADOW_OFS; clear - MBH MBC MS8; Z.div_mod_to_equations; lia).
pose proof SH_band as SHBD.
rewrite SHM in MUk. remember (msz / 8) as q8 eqn:EQ8. clear EQ8.
assert (MBS : mb + msz <= bp - 3312) by (clear - MBC CEIL' LO; unfold bp in *; lia).
assert (SHS2 : SH mb + q8 <= bp - 3312) by (pose proof (@band_lo_range BAND) as BRG; clear - SHB SHBD CEIL' LO BRG; unfold bp in *; lia).
apply (munch_weaken _ (((bp - 3312, bp) :: (rl_T X + 3168, rl_T X + 3169) :: (6444156, 6444156 + 4) :: (1524768, 1524769) :: (rl_T X + 2800, rl_T X + 3168)
:: (977752 + 104, 977752 + 728) :: (ptrarr_lo RE, ptrarr_lo RE + 8388608) :: (1851528, 6373552) :: (rl_dn X, rl_dn X + 1048576) :: (rl_ssb X, rl_ssb X + 8388608) :: nil)
++ [(mb, mb + msz); (SH mb, SH mb + q8)])) in MU.
2:{ intros z Hz. cbn [outside app] in Hz |- *. clear - Hz. tauto. }
cbn [app] in MU. cbn [app] in MUk. lazymatch type of MUk with munch _ ?ma _ => phase_done MU ma m3 MUk WM3 end.
assert (MUF : munch (strdup_W_sec RE X bp ++ [(mb, mb + msz); (SH mb, SH (mb + msz))]) m m3).
{ rewrite SHM. unfold strdup_W_sec, STRDUP_STACK, alloc_W_sec, ALLOC_STACK, SS_BASE, DP_END, A_ERRNO, A_INSTANCE. cbn [tl app]. exact MU. }
destruct (lift_sec_some C HRT HRS HRP HRC HRSE HRD s LB FS RE X G LB0 FS0 a' n mb m m3 bp _ PB PF GC R3 R4 R6 R8 Hn HP ltac:(clear - CEIL' LO; unfold bp; lia)
REG TQ GQ CLS CI NX MBP MBK MBC ZA MUF WM
ltac:(intros lo' hi' x Hin Hx; eapply (strdup_W_sec_lz (ps_a s) LB0 FS0 G RE X);
[exact GC| unfold STRDUP_STACK; clear - CEIL' LO; unfold bp; lia| fold msz; clear - MS8; lia
| rewrite KP in MBP; clear - MBP; Z.div_mod_to_equations; lia| exact Hin| exact Hx])
RT3 RS3 RD3 RSEk CM) as (HP1 & HP2 & HP3 & HP4).

pose proof CM as (_ & _ & WR & _). pose proof (sec_geom_facts n Hn HP) as (_ & _ & Gn' & _). rewrite Gn' in WR.
pose proof (QcA6.Mq4.wr_at_hjunk _ _ _ WR ltac:(rewrite KU; clear - MBH; lia)) as HJ.
replace (mb + kSecUserOff + n) with (mb + kSecUserOff + Z.of_nat (Z.to_nat n)) in HJ by (clear - Hn; lia). destruct (hjunk_cells _ _ _ HJ) as [uj UJ].
assert (SRC3 : bytes_at asegs m3 src (str ++ [b8 0])).
{ unhide SRC0. eapply aheap_presA_bytes_at; [exact HP1| exact SRC0|]. right. right. left. exists (p0, A0, n0). split; [exact Hb|].
cbn [ablk_addr ablk_size fst snd]. rewrite length_app. cbn [length]. unfold n in *. clear - HA1 HA2. lia. }
pose proof (ARUN_blocks_nodup C _ _ _ _ _ HP3) as ND. cbn [map ablk_id fst] in ND.
assert (QP : ASec mb n <> p0).
{ intros E. inversion ND as [|? ? NI _]. apply NI. rewrite E. apply in_map_iff. exists (p0, A0, n0). split; [reflexivity| exact Hb]. }
assert (SEP : src + n <= mb + kSecUserOff \/ mb + kSecUserOff + n <= src).
{ destruct (ARUN_blocks_disjoint C _ _ _ _ _ (ASec mb n, mb + kSecUserOff, n) (p0, A0, n0) HP3 ltac:(left; reflexivity) ltac:(right; exact Hb) QP) as [D|D];
cbn [ablk_addr ablk_size fst snd] in D; unfold n in *; clear - D HA1 HA2; lia. }
assert (APOS : 0 < mb + kSecUserOff < 2^63 /\ 0 <= src < 2^63).
{ pose proof (@band_lo_range BAND) as BRG. rewrite KU. unfold n in *. clear - MBH MBC MS8 SBD BBL HA2 BRG. lia. }

step. unfold_cond; cond_unsig; if_false.
step. step. step.
release_frame FR0 ST3 (bp + -2144).
step.
replace (ret_pc (wz 357876)) with (wz 357876) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
step. unfold_cond; cond_unsig; if_true.
rtc RT3 23%nat K23. pose proof (OBL_RT_GOT_MEMCPY _ _ _ RT3) as KG.
step. step. step.
step. step. step.
step.
eapply evt_cut; [eapply (OBL_MEMCPY _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m3 (str ++ [b8 0]) uj);
[rewrite !unsigned_lit by lia; exact SRC3| rewrite !unsigned_lit by lia; rewrite length_app; cbn [length]; unfold n; lia
| rewrite !unsigned_lit by lia; exact UJ| rewrite !unsigned_lit by lia; lia| assumption]|].
intros ms'' PO. unfold memcpy_post in PO. rewrite !unsigned_lit in PO by lia.
destruct PO as (v0 & v1 & v2 & pw1 & pw2 & pw3 & pw4 & pw5 & pw6 & pw7 & v3 & v4 & v5 & v6 & m4 & -> & MU4 & WM4 & MI4 & UC4 & SRC4).
replace (ret_pc (wz 357780)) with (wz 357780) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
assert (AR4 : ARUN C (set_a a' s) ((ASec mb n, mb + kSecUserOff, n) :: LB) FS RE m4).
{ eapply (ARUN_frame C); [exact HP3| exact MU4| exact WM4|]. constructor; [| constructor].
right. right. left. exists (ASec mb n, mb + kSecUserOff, n). split; [left; reflexivity|]. cbn [ablk_addr ablk_size fst snd]. lia. }
assert (AP4 : aheap_presA asegs a_alayout LB FS bp m3 m4).
{ pose proof (aheap_presA_block_write C (set_a a' s) _ FS RE m3 m4 (ASec mb n, mb + kSecUserOff, n) (mb + kSecUserOff) (mb + kSecUserOff + n) bp HP3 ltac:(left; reflexivity)
ltac:(cbn [ablk_addr fst snd]; lia) ltac:(cbn [ablk_addr ablk_size fst snd]; lia) ltac:(clear - CEIL' LO; unfold bp; lia) MU4 WM4) as H.
assert (E : alb_remove (ablk_id (ASec mb n, mb + kSecUserOff, n)) ((ASec mb n, mb + kSecUserOff, n) :: LB) = LB) by (apply alb_remove_head_rl; cbn [map ablk_id fst]; exact ND).
exact (eq_ind _ (fun l => aheap_presA asegs a_alayout l FS bp m3 m4) H _ E). }
pose proof HP2 as (_ & _ & _ & BBLn & _).
clear MU MUF UJ OBJ3 TRQ3 SRC3 CM WR HJ.
transport_after_call asegs m3 m4 MU4 WM4.
step.
step. do 9 step. step.
pose proof (FRALL _ OBJ FR) as FRX. clear OBJ FR.
destruct q as [|w0 [|w1 [|w2 [|w3 [|w4 [|w5 q']]]]]]; cbn in LQ; try (clear - LQ; lia). unfold unw_obj in FRX. cbn [map app] in FRX.
release_frame FRX ST3 bp.
step.
subst bp. apply evt_done. cbn [fst snd]. unfold std_postA. do 15 eexists. exists m4. rewrite Z_to_bv_bv_unsigned.
split; [reflexivity|]. split; [assumption|]. split; [exact ST3|].
split; [eapply aheap_presA_trans; [exact HP1| exact AP4]|].
split; [reflexivity|]. split; [reflexivity|].
split; [exists dn3; split; [split; [unfold DP_N; exact DNC3| exact DNP3]| exact DNR3]|].
exists (mb + kSecUserOff). split; [reflexivity|]. split; [exact HP2|]. split; [reflexivity|]. split; [exact AR4|].
split; [replace (S (length str)) with (Z.to_nat n) by (unfold n; lia); exact UC4|].
exact (ARUN_block_shadow C _ _ _ _ _ _ _ _ AR4 ltac:(left; reflexivity)).
-
destruct REST as (-> & -> & MUk & RSEk).
lazymatch type of MUk with munch _ ?ma _ => phase_done MU ma m3 MUk WM3 end.
step. if_lit.
step.
pose proof (munch_refl [(bp - 2176, bp - 2160); (A_ERRNO, A_ERRNO + 4)] m3) as MUe. pose proof (wmono_refl asegs m3) as WMe. unfold A_ERRNO in MUe.
step. call_ch (set_errno_spec RE X) ltac:(fun PO => unfold A_ERRNO in PO; rewrite !(unsigned_lit (bp + -2160)) in PO by lia);
[exact RS3| assumption| rewrite unsigned_lit by lia; exact ST3| exact CEIL'| rewrite unsigned_lit by lia; lia|].
match goal with H : stk asegs _ lo _ |- _ => try rename H into ST4 end.
match goal with H : RStats RE X ?mm, H2 : mem_inv asegs ?mm |- _ => rename H into RS4 end.
lazymatch type of MUe with munch _ _ ?mm =>
destruct (sz_frame RE X (ps_a s) LB0 FS0 G m3 mm _ GC MUe WMe
ltac:(intros lo' hi' z Hin Hz; cbn [In] in Hin; destruct Hin as [E|[E|[]]]; injection E as <- <-;
[right; idtac; lia| left; right; left; split; cbn [fst snd]; unfold A_ERRNO; lia])) as (FT & _ & FD);
assert (RSE4 : RSec (ps_a s) LB0 RE X mm) by (eapply SEF; [exact MUe| exact WMe| intros lo' hi' z Hin Hz; cbn [In] in Hin; destruct Hin as [E|[E|[]]]; injection E as <- <-;
[do 2 right; idtac; lia| left; right; left; split; cbn [fst snd]; unfold A_ERRNO; lia]| exact RSEk]) end.
pose proof (FT RT3) as RT4. pose proof (FD RD3) as RD4. clear FT FD MUe WMe RT3 RSEk RD3 RS3.
step.
step. step. step.
release_frame FR0 ST4 (bp + -2144).
step.
replace (ret_pc (wz 357876)) with (wz 357876) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
step. if_lit.
step.
step. do 9 step. step.
pose proof (FRALL _ OBJ FR) as FRX. clear OBJ FR.
destruct q as [|w0 [|w1 [|w2 [|w3 [|w4 [|w5 q']]]]]]; cbn in LQ; try (clear - LQ; lia). unfold unw_obj in FRX. cbn [map app] in FRX.
release_frame FRX ST4 bp.
step.
assert (MUF0 : munch (strdup_W_sec RE X bp) m ltac:(lazymatch type of ST4 with stk _ ?mm _ _ => exact mm end)).
{ unfold strdup_W_sec, STRDUP_STACK, alloc_W_sec, ALLOC_STACK, SS_BASE, DP_END, A_ERRNO, A_INSTANCE. cbn [tl app]. exact MU. }
destruct (lift_sec_none C HRT HRS HRP HRC HRSE HRD s LB FS RE X G LB0 FS0 m _ bp _ PB PF GC R3 R4 R6 R8 ltac:(clear - CEIL' LO; unfold bp; lia) MUF0 WM
ltac:(intros lo' hi' xx Hin Hxx; eapply (strdup_W_sec_z (ps_a s) LB0 FS0 G RE X);
[exact GC| unfold STRDUP_STACK; clear - CEIL' LO; unfold bp; lia| exact Hin| exact Hxx])
RT4 RS4 RD4 RSE4) as [HP1 HP3].
subst bp. apply evt_done. cbn [fst snd]. unfold std_postA. do 15 eexists. lazymatch type of ST4 with stk _ ?mm _ _ => exists mm end. rewrite Z_to_bv_bv_unsigned.
split; [reflexivity|]. split; [assumption|]. split; [exact ST4|]. split; [exact HP1|].
split; [reflexivity|]. split; [reflexivity|]. split; [exists dn3; split; [split; [unfold DP_N; exact DNC3| exact DNP3]| exact DNR3]|]. split; [reflexivity|].
replace (set_a (ps_a s) s) with s by (destruct s; reflexivity). exact HP3.
Qed.

Theorem strdup_A : forall L (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(s : PStateA) (LB : list ablock) (FS : list fframe) (RE : aentry) (b : ablock) (src lo : Z) (str : list byte) (dn : Z),
ae_L RE = L ->
ARUN C s LB FS RE m ->
In b LB -> ablk_addr b <= src -> src + Z.of_nat (length str) + 1 <= ablk_addr b + ablk_size b ->
bytes_at asegs m src (str ++ [b8 0]) -> ~ In (b8 0) str -> Z.of_nat (length str) + 1 <= 2^26 ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - STRDUP_STACK ->
mem_inv asegs m ->
tp = Z_to_bv 64 (ala_tp a_alayout) -> gp = Z_to_bv 64 (ala_gp a_alayout) ->
unw_readable asegs RE m (bv_unsigned sp) -> depot_n asegs m dn -> dn + 1 <= DEPOT_CAP ->
a0 = Z_to_bv 64 src ->
@implMG PStateA asegs (at_nodeA LV asegs) _ (raw_malloc_A L (Z.of_nat (length str) + 1)) s
(fun r s' ms' => std_postA asegs a_alayout ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB FS lo m s' ms'
(fun a0' m' => (exists dn', depot_n asegs m' dn' /\ dn <= dn' <= dn + 1) /\ match r with
| None => a0' = Z_to_bv 64 0 /\ ARUN C s' LB FS RE m'
| Some p => exists A,
a0' = Z_to_bv 64 A /\ ablock_rangeA A (Z.of_nat (length str) + 1) /\ aptr_req p = Z.of_nat (length str) + 1
/\ ARUN C s' ((p, A, Z.of_nat (length str) + 1) :: LB) FS RE m'
/\ rw_cells asegs m' A [CB (S (length str)) (str ++ [b8 0])]
/\ blk_shadow asegs m' A (Z.of_nat (length str) + 1)
end))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 strdup_stub) fc None m (seg_rom asegs)).
Proof.
intros. destruct (from_primary (Z.of_nat (length str) + 1)) eqn:HP.
- eapply (strdup_prim_A C LV HRT HRS HRP HRC HRQ HRD HRF OBL_RT_REPLACE_STR OBL_RT_GOT_MEMCPY OBL_MEMCPY); eassumption.
- eapply strdup_sec_A; eassumption.
Qed.
End Lift.
End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc27. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q13u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q13u. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHig.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHig. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc6I.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc6I. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBrp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBrp. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDM6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDM6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QVsB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QVsB. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsn5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsn5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QwAs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QwAs.Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCiC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCiC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qpj5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qpj5.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvDJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QvDJ.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6sh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6sh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQwg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQwg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKTr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKTr.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJBH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJBH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvG1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QvG1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QyW2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QyW2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsGW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsGW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qp4j.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qp4j. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDw3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDw3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUxU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUxU. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNwL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNwL. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYnC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYnC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnRU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnRU.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSsj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSsj. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qu1d.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qu1d. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNQk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNQk.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTVW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTVW.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNQk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNQk.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpY2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpY2.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTVW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTVW.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOJv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QOJv.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNQk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNQk.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9Ho.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Ho.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QqLk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QqLk. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnRU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnRU.Mqa. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmP7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmP7.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpY2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpY2.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9Ho.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Ho.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYyZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYyZ.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnRU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnRU.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOJv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QOJv.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qu3b.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qu3b.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYyZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYyZ.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkfD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkfD. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYyZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYyZ.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpME.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpME.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkJ4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkJ4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QVo2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QVo2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQ8H.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQ8H.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qx6U.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qx6U.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmvA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmvA.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpME.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpME.Mq6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QVo2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QVo2.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpY2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpY2.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRfV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRfV.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnRU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnRU.Mq9. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEYd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEYd. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qx6U.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qx6U.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QcA6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QcA6.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QcfN.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QcfN.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpY2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpY2.Mq5.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlES.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qt1l.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qt1l.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUYN.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUYN.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdWK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdWK.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmZe.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmZe.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6iK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6iK.
Import ListNotations.
Import Qc6I.Exc. Local Ltac QoSL.addr_diff E A ::= QoSL.mkr__addr_diff_4 E A. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Local Ltac Q0z1.tslia ::= tslia_rel. Local Ltac mkr__tslia_0 := tslia_rel.
Local Ltac lia ::= lia_walk_nf. Local Ltac mkr__lia_1 := lia_walk_nf.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.
Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).
Local Notation mem := (word -> option byte) (only parsing).

Section Lift.
Context {BAND : Band}.
Variables (C : arun_components) (LV : lvp).
Hypothesis HRT : ac_RTconst C = RTconst.
Hypothesis HRS : ac_RStats C = RStats.
Hypothesis HRP : ac_RPrim C = RPrim.
Hypothesis HRC : ac_RChunks C = RChunks.
Hypothesis HRSE : ac_RSec C = RSec.
Hypothesis HRQ : ac_RQuar C = QUnM.RQuar.
Hypothesis HRD : ac_RDepot C = RDepot.
Hypothesis HRF : ac_RFake C = QZbm.RFake.
Hypothesis large_alloc_spec : forall RE X, large_alloc_stmt RE X LV.
Hypothesis poison_zero_spec : forall RE X, poison_zero_stmt_lh RE X LV.
Hypothesis OBL_RT_REPLACE_STR : forall RE X m, RTconst RE X m -> ro_cells asegs m (0x0ed2f8 + 29) [C1 (b8 1)].
Hypothesis OBL_RT_GOT_MEMCPY : forall RE X m, RTconst RE X m -> ro_cells asegs m 0x0e5de0 [C8 (wz 0x0e7da8)].
Hypothesis OBL_MEMCPY : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (src junk : list byte),
bytes_at asegs m (bv_unsigned a1) src -> length src = Z.to_nat (bv_unsigned a2) ->
rw_cells asegs m (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) junk] ->
(bv_unsigned a1 + bv_unsigned a2 <= bv_unsigned a0 \/ bv_unsigned a0 + bv_unsigned a2 <= bv_unsigned a1)%Z ->
mem_inv asegs m ->
evt asegs (memcpy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 src m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xdb34c) fc None m (seg_rom asegs)).

Definition strdup_W_sec (RE : aentry) (X : rlay) (bp : Z) : list (Z * Z) :=
(bp - STRDUP_STACK, bp) :: (rl_T X + 3168, rl_T X + 3169) :: (A_ERRNO, A_ERRNO + 4) :: tl (alloc_W_sec RE X (bp - 2160)).

Lemma lz_mono_sd : forall a RE X SP SP' mb msz x, SP <= SP' -> lz a RE X SP mb msz x -> lz a RE X SP' mb msz x.
Proof. intros a RE X SP SP' mb msz x LE [H|[H|[H|[H|H]]]]; unfold lz; [tauto| tauto| tauto| do 3 right; left; lia| tauto]. Qed.

Lemma strdup_W_sec_lz : forall a LB FS G RE X bp mb msz lo' hi' x,
gcons a LB FS G RE X -> band_lo <= bp - STRDUP_STACK -> 0 <= msz -> mb mod 8 = 0 ->
In (lo', hi') (strdup_W_sec RE X bp ++ [(mb, mb + msz); (SH mb, SH (mb + msz))]) -> lo' <= x < hi' -> lz a RE X bp mb msz x.
Proof.
intros a LB FS G RE X bp mb msz lo' hi' x GC CSP MSZ MB8 Hin Hx. unfold strdup_W_sec in Hin. unfold STRDUP_STACK in *.
cbn [app] in Hin. destruct Hin as [E|Hin].
- injection E as <- <-. do 3 right. left. lia.
- apply (lz_mono_sd a RE X (bp - 16) bp mb msz x ltac:(lia)).
apply (malloc_W_sec_lz a LB FS G RE X (bp - 16) mb msz lo' hi' x GC ltac:(unfold MALLOC_STACK; lia) MSZ MB8); [| exact Hx].
unfold malloc_W_sec. cbn [app]. right. replace (bp - 16 - 2144) with (bp - 2160) by lia. exact Hin.
Qed.

Lemma strdup_W_sec_z : forall a LB FS G RE X bp lo' hi' x,
gcons a LB FS G RE X -> band_lo <= bp - STRDUP_STACK ->
In (lo', hi') (strdup_W_sec RE X bp) -> lo' <= x < hi' -> fp_RStats RE X x \/ fp_RDepot RE X x \/ fp_RSec a RE X x \/ band_lo <= x < bp.
Proof.
intros a LB FS G RE X bp lo' hi' x GC CSP Hin Hx.
destruct (strdup_W_sec_lz a LB FS G RE X bp 0 0 lo' hi' x GC CSP ltac:(lia) eq_refl ltac:(apply in_app_iff; left; exact Hin) Hx) as [Z|[Z|[Z|[Z|Z]]]]; [tauto| tauto| tauto| tauto|].
exfalso. destruct Z as [[Z1 Z2]|[Z1 Z2]]; cbn [fst snd] in *; [lia|]. change (0 / 8) with 0 in Z2. lia.
Qed.

Lemma strdup_sec_A : forall L (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(s : PStateA) (LB : list ablock) (FS : list fframe) (RE : aentry) (b : ablock) (src lo : Z) (str : list byte) (dn : Z),
ae_L RE = L ->
ARUN C s LB FS RE m ->
In b LB -> ablk_addr b <= src -> src + Z.of_nat (length str) + 1 <= ablk_addr b + ablk_size b ->
bytes_at asegs m src (str ++ [b8 0]) -> ~ In (b8 0) str -> Z.of_nat (length str) + 1 <= 2^26 ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - STRDUP_STACK ->
mem_inv asegs m ->
tp = Z_to_bv 64 (ala_tp a_alayout) -> gp = Z_to_bv 64 (ala_gp a_alayout) ->
unw_readable asegs RE m (bv_unsigned sp) -> depot_n asegs m dn -> dn + 1 <= DEPOT_CAP ->
a0 = Z_to_bv 64 src ->
from_primary (Z.of_nat (length str) + 1) = false ->
@implMG PStateA asegs (at_nodeA LV asegs) _ (raw_malloc_A L (Z.of_nat (length str) + 1)) s
(fun r s' ms' => std_postA asegs a_alayout ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB FS lo m s' ms'
(fun a0' m' => (exists dn', depot_n asegs m' dn' /\ dn <= dn' <= dn + 1) /\ match r with
| None => a0' = Z_to_bv 64 0 /\ ARUN C s' LB FS RE m'
| Some p => exists A,
a0' = Z_to_bv 64 A /\ ablock_rangeA A (Z.of_nat (length str) + 1) /\ aptr_req p = Z.of_nat (length str) + 1
/\ ARUN C s' ((p, A, Z.of_nat (length str) + 1) :: LB) FS RE m'
/\ rw_cells asegs m' A [CB (S (length str)) (str ++ [b8 0])]
/\ blk_shadow asegs m' A (Z.of_nat (length str) + 1)
end))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 strdup_stub) fc None m (seg_rom asegs)).
Proof.
intros until dn; intros EL AR Hb HA1 HA2 SRC NZ NMAX ST CEIL LO MI -> -> UNW DNH DCAP -> HP.
cbn [ala_tp ala_gp a_alayout] in *.
pose proof DNH as [DNC DNP]. unfold DP_N in DNC.
pose proof CEIL as CEIL'. idtac. pose proof LO as LO0. unfold STRDUP_STACK in LO.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
set (n := Z.of_nat (length str) + 1) in *. set (bp := bv_unsigned sp) in *.

destruct b as [[p0 A0] n0]. cbn [ablk_addr ablk_size fst snd] in HA1, HA2.
pose proof (ARUN_block_range C _ _ _ _ _ _ AR Hb) as BR. cbn [ablk_addr ablk_size fst snd] in BR. destruct BR as ((APR & _) & _ & BN0 & BBL & _).
assert (KD : KHI <= src \/ (0 < src /\ src + n <= kLowEnd)).
{ rewrite ?KHI_eq. unfold kLowEnd. destruct APR as [[[AP1 AP2]|AP] _]; [right; unfold n; clear - AP1 AP2 HA1 HA2; lia| left; clear - AP HA1; lia]. }
pose proof (ARUN_block_shadow C _ _ _ _ _ _ _ _ AR Hb) as BSH.
pose proof (shadow_ok_sub m A0 n0 src n BSH HA1 ltac:(unfold n in *; lia) ltac:(unfold n; lia)) as SO.
destruct (ARUN_nbhd C HRP HRC HRQ HRF s LB FS RE m src n AR ltac:(left; exists p0, A0, n0; split; [exact Hb| split; unfold n in *; lia]) ltac:(unfold n; lia)) as [NW1 NW2].
destruct (ARUN_open C _ _ _ _ _ AR) as (X & G & LB0 & FS0 & PB & PF & AX).
destruct AX as (GC & R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8).
rewrite HRT in R1. rewrite HRS in R2. rewrite HRP in R3. rewrite HRC in R4. rewrite HRSE in R5. rewrite HRD in R7.
rename R1 into RT. rename R2 into RS. rename R5 into RSE. rename R7 into RD.
pose proof (gc_rlay _ _ _ _ _ _ GC) as RL. pose proof kconsts as (KR & KO & KS & K32 & KP & KU & KM & KX).
assert (Hn : 0 <= n <= 2^26) by (unfold n in *; lia).
pose proof (bytes_at_bound _ _ _ _ SRC) as SBD. rewrite length_app in SBD. cbn [length] in SBD.

assert (CSRC : forall x, src <= x < src + n -> aclient_addrA a_alayout LB FS bp x).
{ intros x Hx. right. right. left. exists (p0, A0, n0). split; [exact Hb|]. cbn [ablk_addr ablk_size fst snd]. unfold n in *. lia. }
assert (STU : src + Z.of_nat (length (str ++ [b8 0])) <= rl_T X + 3168 \/ rl_T X + 3169 <= src).
{ assert (LSB : Z.of_nat (length (str ++ [b8 0])) = n) by (rewrite length_app; cbn [length]; unfold n; lia). rewrite LSB.
destruct (Z_le_gt_dec (src + n) (rl_T X + 3168)) as [|G1]; [left; assumption|].
destruct (Z_le_gt_dec (rl_T X + 3169) src) as [|G2]; [right; assumption|]. exfalso.
apply (depot_client (ps_a s) LB0 FS0 G RE X LB FS bp (rl_T X + 3168) GC PB PF ltac:(unfold bp; lia)); [apply CSRC; lia|].
do 3 right. reflexivity. }
assert (SLO' : src + Z.of_nat (length (str ++ [b8 0])) <= lo) by (rewrite length_app; cbn [length]; unfold n in *; lia).
pose proof SRC as SRC0. hide SRC0.
apply raw_malloc_A_intro. rewrite <- EL.

pose proof (QSsj.rlay_obj_facts_lia RE X _ RL (T_obj RE X)) as (_ & TK & TB & _). cbn [fst snd] in TK, TB.
pose proof (QSsj.rlay_obj_facts_lia RE X _ RL (dn_obj RE X)) as (_ & NK & NC & _). cbn [fst snd] in NK, NC.
pose proof (QSsj.rlay_obj_facts_lia RE X _ RL (ssb_obj RE X)) as (_ & BK & BC & _). cbn [fst snd] in BK, BC.
pose proof (rlay_prim_facts RE X RL) as (_ & PK & PC & _ & QK & QC & _). unfold prim_hi in PC. unfold ptrarr_hi in QC. idtac. rewrite ?KHI_eq in PK.
change (al_space_beg (ae_L RE)) with (prim_lo RE) in PC. change (al_ptrarr (ae_L RE)) with (ptrarr_lo RE) in QC.
apply appr_to_lia in QK; [| lia| lia].
pose proof (munch_refl (strdup_W_sec RE X bp) m) as MU. pose proof (wmono_refl asegs m) as WM.
unfold strdup_W_sec, STRDUP_STACK, alloc_W_sec, ALLOC_STACK, SS_BASE, DP_END, A_ERRNO, A_INSTANCE in MU. cbn [tl app] in MU.

assert (SEF : forall mm mm' W, munch W mm mm' -> wmono asegs mm mm' ->
(forall lo' hi' z, In (lo', hi') W -> lo' <= z < hi' -> fp_RStats RE X z \/ fp_RDepot RE X z \/ band_lo <= z) ->
RSec (ps_a s) LB0 RE X mm -> RSec (ps_a s) LB0 RE X mm').
{ intros mm mm' W MUw WMw HW RSEw. eapply RSec_frame; [exact RSEw| exact WMw|]. eapply agree_on_of_munch; [exact MUw| exact WMw|]. intros z Fz _. apply outside_intro.
intros lo' hi' Hin Hz. destruct (HW lo' hi' z Hin Hz) as [P|[P|P]].
- exact (fpS_excl _ _ _ _ _ _ GC z P ltac:(right; left; exact Fz)).
- exact (fpD_excl _ _ _ _ _ _ GC z P ltac:(right; left; exact Fz)).
- pose proof (fp_lt_ceil _ _ _ _ _ _ GC z ltac:(do 4 right; left; exact Fz)). lia. }
apply aimplT_from_evt.
rewrite <- (Z_to_bv_bv_unsigned sp). fold bp.
eapply (strdup_p1 RE X (OBL_RT_REPLACE_STR RE X) m src lo bp str [] (str ++ [b8 0]) SRC eq_refl NZ SLO' ltac:(lia) SO NW1 NW2 KD ltac:(unfold n in *; lia) ltac:(unfold n in *; lia));
[exact RT| exact RL| exact MI| exact ST| exact CEIL'| exact LO0| unfold bp; lia| exact (RDepot_unw RE X _ RD)|].
intros mc ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' j1 j0 MUc WMc MIc STc FRc FR0c RTc SRCc TUc.
eapply (strdup_p2 RE X m src lo bp str (str ++ [b8 0]) SLO' STU);
[exact RT| exact RL| exact CEIL'| exact LO0| unfold bp; lia| exact UNW| exact MUc| exact WMc| exact MIc| exact STc| exact FRc| exact FR0c| exact SRCc| exact TUc|].
clear mc ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' j1 j0 MUc WMc MIc STc FRc FR0c RTc SRCc TUc.
intros m1 u0 u1 u2 u3 u4 u5 u6 u7 u8 u10 u11 u12 u13 sz q rest junk8 MU1 WM1 MI1 ST1 OBJ LQ SZR FR RT1 TU1 SRC1.
unfold sd_W in MU1.
assert (RS1 : RStats RE X m1).
{ eapply RStats_munch; [exact RS| exact MU1| exact WM1|]. constructor; [first [st_avoid_solve| eapply st_avoid_T; [eassumption| lia| lia]]|]. constructor; [st_avoid_solve| constructor]. }
assert (RSE1 : RSec (ps_a s) LB0 RE X m1).
{ eapply SEF; [exact MU1| exact WM1| | exact RSE]. intros lo' hi' z Hin Hz. cbn [In] in Hin. destruct Hin as [E|[E|[]]]; injection E as <- <-.
- do 2 right. idtac. lia.
- right; left. do 3 right. lia. }
assert (RD1 : RDepot RE X m1).
{ eapply RDepot_frame_unw; [exact RL| exact RD| exact WM1| | exact TU1]. eapply agree_on_of_munch; [exact MU1| exact WM1|]. intros z [Fz NZ'] _. cbn [outside].
pose proof (fp_lt_ceil _ _ _ _ _ _ GC z ltac:(do 5 right; left; exact Fz)). idtac. lia. }
phase_done MU m m1 MU1 WM1. clear RT RS RSE RD MI. try clear ST.
destruct (unw_obj_head _ _ _ _ _ _ OBJ LQ ltac:(lia)) as [OBJh (q30 & TRQ & LQ30)].

unfold asan_malloc_entry. carve_frame 16%nat ST1.
try match goal with H : rw_cells asegs _ (bp + -2144 + -16) _ |- _ => replace (bp + -2144 + -16) with (bp + -2160) in H by lia end.
try replace (bp + -2144 + -16) with (bp + -2160) in ST1 by lia.
pose proof (munch_refl [(bp - 2160, bp - 2144)] m1) as MUa. pose proof (wmono_refl asegs m1) as WMa.
step. stf. step.
step. step. step. stp. stp. step. stp.
step.
lazymatch type of MUa with munch _ _ ?mm =>
destruct (sz_frame RE X (ps_a s) LB0 FS0 G m1 mm _ GC MUa WMa ltac:(intros lo' hi' z Hin Hz; cbn [In] in Hin; destruct Hin as [E|[]]; injection E as <- <-; right; idtac; lia)) as (FT & _ & FD);
pose proof (FT RT1) as RT2; pose proof (FD RD1) as RD2;
assert (RSE2 : RSec (ps_a s) LB0 RE X mm) by (eapply SEF; [exact MUa| exact WMa| intros lo' hi' z Hin Hz; cbn [In] in Hin; destruct Hin as [E|[]]; injection E as <- <-; do 2 right; idtac; lia| exact RSE1]);
assert (RS2 : RStats RE X mm) by (eapply RStats_munch; [exact RS1| exact MUa| exact WMa| constructor; [st_avoid_solve| constructor]]) end.
clear FT FD RT1 RSE1 RD1 RS1 MUa WMa.
apply evt_done. change (wz 967832) with (wz A_INSTANCE).
eapply aimplT_then.
{ eapply (allocate_sec_spec LV RE X (large_alloc_spec RE X) (poison_zero_spec RE X) _ _ (wz 67584) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ s (ps_a s) G LB0 FS0 n 1 lo (bp + -2144) sz dn q30 GC RT2 RS2 RSE2 RD2);
[assumption| rewrite unsigned_lit by lia; exact ST1| exact CEIL'| rewrite unsigned_lit by lia; unfold ALLOC_STACK; lia| exact Hn| exact HP| lia
| exact OBJh| exact TRQ| exact LQ30| exact SZR| split; [unfold DP_N; exact DNC| exact DNP]| exact DCAP| rewrite unsigned_lit by lia; lia| lia]. }
intros [r a'] s' ms' PO. unfold alloc_post_sec in PO. rewrite !(unsigned_lit (bp + -2160)) in PO by lia.
destruct PO as (y0 & y1 & y2 & z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & y3 & y4 & y5 & y6 & m3 & -> & -> & WM3 & MI3 & ST3 & RT3 & RS3 & RD3 & DS3 & OBJ3 & TRQ3 & REST).
destruct (DS3 dn ltac:(split; [unfold DP_N; exact DNC| exact DNP]) ltac:(unfold DEPOT_CAP in DCAP; lia)) as (dn3 & [DNC3 DNP3] & DNR3). unfold DP_N in DNC3. clear DNC.
replace (ret_pc (wz 258104)) with (wz 258104) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
unfold alloc_W_sec, ALLOC_STACK, SS_BASE, DP_END, A_INSTANCE in REST.
clear OBJh TRQ RT2 RSE2 RD2 RS2.

assert (FRALL : forall mx, rw_cells asegs mx (bp + -2144) (unw_obj (bp + -2144) sz q rest bp) ->
rw_cells asegs mx (bp + -80) [CB 8 junk8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
rw_cells asegs mx (bp + -2144) (unw_obj (bp + -2144) sz q rest bp ++ [CB 8 junk8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])).
{ intros mx O1 O2. apply (proj2 (rw_cells_app asegs mx _ _ _)). split; [exact O1|].
destruct q as [|w0 [|w1 [|w2 [|w3 [|w4 [|w5 q']]]]]]; cbn in LQ; try (clear - LQ; lia).
unfold unw_obj. cbn [cells_size csize Nat.add map app]. replace (bp + -2144 + Z.of_nat 2064) with (bp + -80) by lia. exact O2. }
destruct r as [pq|].
-
destruct REST as (mb & -> & REG & TQ & GQ & CLS & CI & NX & NR & SPN & MBP & MBK & MBC & ZA & -> & MUk & RSEk & CM & _).
pose proof MBK as MBK'. apply appr_to_lia in MBK'; [| pose proof (sec_map_size_ge n ltac:(lia) HP) as [SMG0 _]; lia| lia].
set (msz := sec_map_size n) in *.
assert (MS8 : 8 * (msz / 8) = msz /\ 4096 <= msz) by (pose proof (sec_geom_facts n Hn HP) as (G1 & _ & _ & _ & G5 & G6 & G7 & G8 & _); fold msz in G7, G8; clear - G1 G5 G6 G7 G8; Z.div_mod_to_equations; lia).
assert (SHM : SH (mb + msz) = SH mb + msz / 8) by (rewrite <- SH_plus8; f_equal; lia).
assert (MBH : 0x645000 <= mb) by (pose proof (sec_map_size_ge n ltac:(lia) HP) as [SMG _]; fold msz in SMG; pose proof (sec_req_facts n ltac:(lia) HP) as [_ RQn]; clear - MBK' SMG RQn; lia).
assert (SHB : 0x80000000 <= SH mb /\ SH mb + msz / 8 <= SH band_lo) by (unfold SH, A_SHADOW_OFS; clear - MBH MBC MS8; Z.div_mod_to_equations; lia).
pose proof SH_band as SHBD.
rewrite SHM in MUk. remember (msz / 8) as q8 eqn:EQ8. clear EQ8.
assert (MBS : mb + msz <= bp - 3312) by (clear - MBC CEIL' LO; unfold bp in *; lia).
assert (SHS2 : SH mb + q8 <= bp - 3312) by (pose proof (@band_lo_range BAND) as BRG; clear - SHB SHBD CEIL' LO BRG; unfold bp in *; lia).
apply (munch_weaken _ (((bp - 3312, bp) :: (rl_T X + 3168, rl_T X + 3169) :: (6434236, 6434236 + 4) :: (1514848, 1514849) :: (rl_T X + 2800, rl_T X + 3168)
:: (967832 + 104, 967832 + 728) :: (ptrarr_lo RE, ptrarr_lo RE + 8388608) :: (1841608, 6363632) :: (rl_dn X, rl_dn X + 1048576) :: (rl_ssb X, rl_ssb X + 8388608) :: nil)
++ [(mb, mb + msz); (SH mb, SH mb + q8)])) in MU.
2:{ intros z Hz. cbn [outside app] in Hz |- *. clear - Hz. tauto. }
cbn [app] in MU. cbn [app] in MUk. lazymatch type of MUk with munch _ ?ma _ => phase_done MU ma m3 MUk WM3 end.
assert (MUF : munch (strdup_W_sec RE X bp ++ [(mb, mb + msz); (SH mb, SH (mb + msz))]) m m3).
{ rewrite SHM. unfold strdup_W_sec, STRDUP_STACK, alloc_W_sec, ALLOC_STACK, SS_BASE, DP_END, A_ERRNO, A_INSTANCE. cbn [tl app]. exact MU. }
destruct (lift_sec_some C HRT HRS HRP HRC HRSE HRD s LB FS RE X G LB0 FS0 a' n mb m m3 bp _ PB PF GC R3 R4 R6 R8 Hn HP ltac:(clear - CEIL' LO; unfold bp; lia)
REG TQ GQ CLS CI NX MBP MBK MBC ZA MUF WM
ltac:(intros lo' hi' x Hin Hx; eapply (strdup_W_sec_lz (ps_a s) LB0 FS0 G RE X);
[exact GC| unfold STRDUP_STACK; clear - CEIL' LO; unfold bp; lia| fold msz; clear - MS8; lia
| rewrite KP in MBP; clear - MBP; Z.div_mod_to_equations; lia| exact Hin| exact Hx])
RT3 RS3 RD3 RSEk CM) as (HP1 & HP2 & HP3 & HP4).

pose proof CM as (_ & _ & WR & _). pose proof (sec_geom_facts n Hn HP) as (_ & _ & Gn' & _). rewrite Gn' in WR.
pose proof (QcA6.Mq2.wr_at_hjunk _ _ _ WR ltac:(rewrite KU; clear - MBH; lia)) as HJ.
replace (mb + kSecUserOff + n) with (mb + kSecUserOff + Z.of_nat (Z.to_nat n)) in HJ by (clear - Hn; lia). destruct (hjunk_cells _ _ _ HJ) as [uj UJ].
assert (SRC3 : bytes_at asegs m3 src (str ++ [b8 0])).
{ unhide SRC0. eapply aheap_presA_bytes_at; [exact HP1| exact SRC0|]. right. right. left. exists (p0, A0, n0). split; [exact Hb|].
cbn [ablk_addr ablk_size fst snd]. rewrite length_app. cbn [length]. unfold n in *. clear - HA1 HA2. lia. }
pose proof (ARUN_blocks_nodup C _ _ _ _ _ HP3) as ND. cbn [map ablk_id fst] in ND.
assert (QP : ASec mb n <> p0).
{ intros E. inversion ND as [|? ? NI _]. apply NI. rewrite E. apply in_map_iff. exists (p0, A0, n0). split; [reflexivity| exact Hb]. }
assert (SEP : src + n <= mb + kSecUserOff \/ mb + kSecUserOff + n <= src).
{ destruct (ARUN_blocks_disjoint C _ _ _ _ _ (ASec mb n, mb + kSecUserOff, n) (p0, A0, n0) HP3 ltac:(left; reflexivity) ltac:(right; exact Hb) QP) as [D|D];
cbn [ablk_addr ablk_size fst snd] in D; unfold n in *; clear - D HA1 HA2; lia. }
assert (APOS : 0 < mb + kSecUserOff < 2^63 /\ 0 <= src < 2^63).
{ pose proof (@band_lo_range BAND) as BRG. rewrite KU. unfold n in *. clear - MBH MBC MS8 SBD BBL HA2 BRG. lia. }

step. unfold_cond; cond_unsig; if_false.
step. step. step.
release_frame FR0 ST3 (bp + -2144).
step.
replace (ret_pc (wz 356892)) with (wz 356892) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
step. unfold_cond; cond_unsig; if_true.
rtc RT3 23%nat K23. pose proof (OBL_RT_GOT_MEMCPY _ _ _ RT3) as KG.
step. step. step.
step. step. step.
step.
eapply evt_cut; [eapply (OBL_MEMCPY _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m3 (str ++ [b8 0]) uj);
[rewrite !unsigned_lit by lia; exact SRC3| rewrite !unsigned_lit by lia; rewrite length_app; cbn [length]; unfold n; lia
| rewrite !unsigned_lit by lia; exact UJ| rewrite !unsigned_lit by lia; lia| assumption]|].
intros ms'' PO. unfold memcpy_post in PO. rewrite !unsigned_lit in PO by lia.
destruct PO as (v0 & v1 & v2 & pw1 & pw2 & pw3 & pw4 & pw5 & pw6 & pw7 & v3 & v4 & v5 & v6 & m4 & -> & MU4 & WM4 & MI4 & UC4 & SRC4).
replace (ret_pc (wz 356796)) with (wz 356796) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
assert (AR4 : ARUN C (set_a a' s) ((ASec mb n, mb + kSecUserOff, n) :: LB) FS RE m4).
{ eapply (ARUN_frame C); [exact HP3| exact MU4| exact WM4|]. constructor; [| constructor].
right. right. left. exists (ASec mb n, mb + kSecUserOff, n). split; [left; reflexivity|]. cbn [ablk_addr ablk_size fst snd]. lia. }
assert (AP4 : aheap_presA asegs a_alayout LB FS bp m3 m4).
{ pose proof (aheap_presA_block_write C (set_a a' s) _ FS RE m3 m4 (ASec mb n, mb + kSecUserOff, n) (mb + kSecUserOff) (mb + kSecUserOff + n) bp HP3 ltac:(left; reflexivity)
ltac:(cbn [ablk_addr fst snd]; lia) ltac:(cbn [ablk_addr ablk_size fst snd]; lia) ltac:(clear - CEIL' LO; unfold bp; lia) MU4 WM4) as H.
assert (E : alb_remove (ablk_id (ASec mb n, mb + kSecUserOff, n)) ((ASec mb n, mb + kSecUserOff, n) :: LB) = LB) by (apply alb_remove_head_rl; cbn [map ablk_id fst]; exact ND).
exact (eq_ind _ (fun l => aheap_presA asegs a_alayout l FS bp m3 m4) H _ E). }
pose proof HP2 as (_ & _ & _ & BBLn & _).
clear MU MUF UJ OBJ3 TRQ3 SRC3 CM WR HJ.
transport_after_call asegs m3 m4 MU4 WM4.
step.
step. do 9 step. step.
pose proof (FRALL _ OBJ FR) as FRX. clear OBJ FR.
destruct q as [|w0 [|w1 [|w2 [|w3 [|w4 [|w5 q']]]]]]; cbn in LQ; try (clear - LQ; lia). unfold unw_obj in FRX. cbn [map app] in FRX.
release_frame FRX ST3 bp.
step.
subst bp. apply evt_done. cbn [fst snd]. unfold std_postA. do 15 eexists. exists m4. rewrite Z_to_bv_bv_unsigned.
split; [reflexivity|]. split; [assumption|]. split; [exact ST3|].
split; [eapply aheap_presA_trans; [exact HP1| exact AP4]|].
split; [reflexivity|]. split; [reflexivity|].
split; [exists dn3; split; [split; [unfold DP_N; exact DNC3| exact DNP3]| exact DNR3]|].
exists (mb + kSecUserOff). split; [reflexivity|]. split; [exact HP2|]. split; [reflexivity|]. split; [exact AR4|].
split; [replace (S (length str)) with (Z.to_nat n) by (unfold n; lia); exact UC4|].
exact (ARUN_block_shadow C _ _ _ _ _ _ _ _ AR4 ltac:(left; reflexivity)).
-
destruct REST as (-> & -> & MUk & RSEk).
lazymatch type of MUk with munch _ ?ma _ => phase_done MU ma m3 MUk WM3 end.
step. if_lit.
step.
pose proof (munch_refl [(bp - 2176, bp - 2160); (A_ERRNO, A_ERRNO + 4)] m3) as MUe. pose proof (wmono_refl asegs m3) as WMe. unfold A_ERRNO in MUe.
step. call_ch (set_errno_spec RE X) ltac:(fun PO => unfold A_ERRNO in PO; rewrite !(unsigned_lit (bp + -2160)) in PO by lia);
[exact RS3| assumption| rewrite unsigned_lit by lia; exact ST3| exact CEIL'| rewrite unsigned_lit by lia; lia|].
match goal with H : stk asegs _ lo _ |- _ => try rename H into ST4 end.
match goal with H : RStats RE X ?mm, H2 : mem_inv asegs ?mm |- _ => rename H into RS4 end.
lazymatch type of MUe with munch _ _ ?mm =>
destruct (sz_frame RE X (ps_a s) LB0 FS0 G m3 mm _ GC MUe WMe
ltac:(intros lo' hi' z Hin Hz; cbn [In] in Hin; destruct Hin as [E|[E|[]]]; injection E as <- <-;
[right; idtac; lia| left; right; left; split; cbn [fst snd]; unfold A_ERRNO; lia])) as (FT & _ & FD);
assert (RSE4 : RSec (ps_a s) LB0 RE X mm) by (eapply SEF; [exact MUe| exact WMe| intros lo' hi' z Hin Hz; cbn [In] in Hin; destruct Hin as [E|[E|[]]]; injection E as <- <-;
[do 2 right; idtac; lia| left; right; left; split; cbn [fst snd]; unfold A_ERRNO; lia]| exact RSEk]) end.
pose proof (FT RT3) as RT4. pose proof (FD RD3) as RD4. clear FT FD MUe WMe RT3 RSEk RD3 RS3.
step.
step. step. step.
release_frame FR0 ST4 (bp + -2144).
step.
replace (ret_pc (wz 356892)) with (wz 356892) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
step. if_lit.
step.
step. do 9 step. step.
pose proof (FRALL _ OBJ FR) as FRX. clear OBJ FR.
destruct q as [|w0 [|w1 [|w2 [|w3 [|w4 [|w5 q']]]]]]; cbn in LQ; try (clear - LQ; lia). unfold unw_obj in FRX. cbn [map app] in FRX.
release_frame FRX ST4 bp.
step.
assert (MUF0 : munch (strdup_W_sec RE X bp) m ltac:(lazymatch type of ST4 with stk _ ?mm _ _ => exact mm end)).
{ unfold strdup_W_sec, STRDUP_STACK, alloc_W_sec, ALLOC_STACK, SS_BASE, DP_END, A_ERRNO, A_INSTANCE. cbn [tl app]. exact MU. }
destruct (lift_sec_none C HRT HRS HRP HRC HRSE HRD s LB FS RE X G LB0 FS0 m _ bp _ PB PF GC R3 R4 R6 R8 ltac:(clear - CEIL' LO; unfold bp; lia) MUF0 WM
ltac:(intros lo' hi' xx Hin Hxx; eapply (strdup_W_sec_z (ps_a s) LB0 FS0 G RE X);
[exact GC| unfold STRDUP_STACK; clear - CEIL' LO; unfold bp; lia| exact Hin| exact Hxx])
RT4 RS4 RD4 RSE4) as [HP1 HP3].
subst bp. apply evt_done. cbn [fst snd]. unfold std_postA. do 15 eexists. lazymatch type of ST4 with stk _ ?mm _ _ => exists mm end. rewrite Z_to_bv_bv_unsigned.
split; [reflexivity|]. split; [assumption|]. split; [exact ST4|]. split; [exact HP1|].
split; [reflexivity|]. split; [reflexivity|]. split; [exists dn3; split; [split; [unfold DP_N; exact DNC3| exact DNP3]| exact DNR3]|]. split; [reflexivity|].
replace (set_a (ps_a s) s) with s by (destruct s; reflexivity). exact HP3.
Qed.

Theorem strdup_A : forall L (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(s : PStateA) (LB : list ablock) (FS : list fframe) (RE : aentry) (b : ablock) (src lo : Z) (str : list byte) (dn : Z),
ae_L RE = L ->
ARUN C s LB FS RE m ->
In b LB -> ablk_addr b <= src -> src + Z.of_nat (length str) + 1 <= ablk_addr b + ablk_size b ->
bytes_at asegs m src (str ++ [b8 0]) -> ~ In (b8 0) str -> Z.of_nat (length str) + 1 <= 2^26 ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - STRDUP_STACK ->
mem_inv asegs m ->
tp = Z_to_bv 64 (ala_tp a_alayout) -> gp = Z_to_bv 64 (ala_gp a_alayout) ->
unw_readable asegs RE m (bv_unsigned sp) -> depot_n asegs m dn -> dn + 1 <= DEPOT_CAP ->
a0 = Z_to_bv 64 src ->
@implMG PStateA asegs (at_nodeA LV asegs) _ (raw_malloc_A L (Z.of_nat (length str) + 1)) s
(fun r s' ms' => std_postA asegs a_alayout ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB FS lo m s' ms'
(fun a0' m' => (exists dn', depot_n asegs m' dn' /\ dn <= dn' <= dn + 1) /\ match r with
| None => a0' = Z_to_bv 64 0 /\ ARUN C s' LB FS RE m'
| Some p => exists A,
a0' = Z_to_bv 64 A /\ ablock_rangeA A (Z.of_nat (length str) + 1) /\ aptr_req p = Z.of_nat (length str) + 1
/\ ARUN C s' ((p, A, Z.of_nat (length str) + 1) :: LB) FS RE m'
/\ rw_cells asegs m' A [CB (S (length str)) (str ++ [b8 0])]
/\ blk_shadow asegs m' A (Z.of_nat (length str) + 1)
end))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 strdup_stub) fc None m (seg_rom asegs)).
Proof.
intros. destruct (from_primary (Z.of_nat (length str) + 1)) eqn:HP.
- eapply (strdup_prim_A C LV HRT HRS HRP HRC HRQ HRD HRF OBL_RT_REPLACE_STR OBL_RT_GOT_MEMCPY OBL_MEMCPY); eassumption.
- eapply strdup_sec_A; eassumption.
Qed.
End Lift.
