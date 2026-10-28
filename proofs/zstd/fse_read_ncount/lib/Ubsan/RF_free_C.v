(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Image ZBridge SysStep Walk Arr.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Common Require Import SFModel.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import UImgX.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Malloc Require Import F_malloc_free F_free_C.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import RMallocRep RMallocTree RMallocKit_B RMallocKit_B3 RF_get_meta RF_mm_syscalls.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Spec Require Import STree Malloc MallocCtrl.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import RunDraw.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section CANSEC1. Context {rc : runConstT}.
Definition rffin_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (W : list (Z * Z)) (m : word -> option byte) (st : mstate) (errv : word) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom usegs)
/\ munch W m m' /\ wmono usegs m m' /\ mem_inv usegs m'
/\ stk usegs m' lo (bv_unsigned sp)
/\ rw_cells usegs m' (errno_addr tp) [C4 errv]
/\ rmrep st m'.
#[using="Type"] Lemma rfree_fin0 : forall (sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 ra bw q0 q1 : word) F fc
(m : word -> option byte) (junk : list byte) (lo : Z) (st : mstate) (errv : word),
tp = Z_to_bv 64 RATP ->
rmrep st m -> mem_inv usegs m ->
rw_cells usegs m (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
rw_cells usegs m (errno_addr tp) [C4 errv] ->
stk usegs m lo (bv_unsigned sp + -48) -> ATOP <= lo -> lo <= bv_unsigned sp - 48 ->
evt usegs (rffin_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m st errv)
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 q0 q1 bw (wz 0) a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1546c) fc None m (seg_rom usegs)).
Proof.
intros until errv. intros TP MR MI FR ERR ST LO LOLE.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU.
pose proof (wmono_refl usegs m) as WM.
pose proof MR as (WF & CX & GL & AR & GR & SH). destruct GL as (LK & NL & _).
unfold RMLOCK, RNEED_LOCKS, RATP in *. atop_facts. subst tp.
Local Ltac2 Set LiaHints.tbl := fun () => "00<0>1800609155.68 24638473347.6725853096848.5827905021218.6043988483203.6651711223320.5954243526019.6757177349585.606262822416.58 64997134979.688826107286.59 8841017104.58 00000100200300900:00;00<00E00F00G00H00ISSSS4LOLESSSS2LO4LOLESSSS".
rewrite (unsigned_lit 192304) in ERR by lia. change (192304 + -164) with 192140 in ERR.
st1. st1. st1. st1.
st1.
eapply evt_cut.
{ eapply runlock_spec; rewrite unsigned_lit by lia; [reflexivity| exact LK]. }
intros ms' ->.
replace (ret_pc (Z_to_bv 64 0x15480)) with (Z_to_bv 64 0x15480) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
st1. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. }
st1. st1. st1. st1. st1. st1. st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR2 : rmrep st mX)
by (eapply rmrep_transport_high; [exact MR | exact MU | exact WM | intros l h [E|[]]; inversion E; subst; atop_facts; lia]) end.
release_frame FR ST (bv_unsigned sp).
apply evt_done. unfold rffin_post. do 16 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [| exact MR2].
rewrite (unsigned_lit 192304) by lia. change (192304 + -164) with 192140. exact ERR.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition rfmun_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (junk : list byte) (m : word -> option byte) (st : mstate) (errv bw lw : word) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR (Z_to_bv 64 0x1549c) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 bw lw bw lw a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (errno_addr tp)) (sx32 errv) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 rmunmap_entry) fc None m' (seg_rom usegs)
/\ munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
/\ stk usegs m' lo (bv_unsigned sp + -48)
/\ rw_cells usegs m' (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
/\ rw_cells usegs m' (errno_addr tp) [C4 errv]
/\ rmrep st m'.
#[using="Type"] Lemma rfree_tomunmap : forall (sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 ra bw q0 q1 : word) F fc
(m : word -> option byte) (junk : list byte) (lo len : Z) (st : mstate) (errv : word),
tp = Z_to_bv 64 RATP ->
rmrep st m -> mem_inv usegs m -> 0 < len < 2^64 ->
rw_cells usegs m (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
rw_cells usegs m (errno_addr tp) [C4 errv] ->
stk usegs m lo (bv_unsigned sp + -48) -> ATOP <= lo -> lo <= bv_unsigned sp - 48 ->
evt usegs (rfmun_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo junk m st errv bw (wz len))
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 q0 q1 bw (wz len) a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1546c) fc None m (seg_rom usegs)).
Proof.
intros until errv. intros TP MR MI HL FR ERR ST LO LOLE.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU.
pose proof (wmono_refl usegs m) as WM.
pose proof MR as (WF & CX & GL & AR & GR & SH). destruct GL as (LK & NL & _).
unfold RMLOCK, RNEED_LOCKS, RATP in *. atop_facts. subst tp.
Local Ltac2 Set LiaHints.tbl := fun () => "0090>25853096848.6057177349585.6259314923118.6159368190966.6759384358287.616262822416.60 65127317551.618828237488.62 8841017104.60 00000100:00@00A00B00C00G00H00ISS2LO4LOLES2HL1KSSSS2HLSS".
rewrite (unsigned_lit 192304) in ERR by lia. change (192304 + -164) with 192140 in ERR.
st1. st1. st1. st1.
st1.
eapply evt_cut.
{ eapply runlock_spec; rewrite unsigned_lit by lia; [reflexivity| exact LK]. }
intros ms' ->.
replace (ret_pc (Z_to_bv 64 0x15480)) with (Z_to_bv 64 0x15480) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
st1. if_cases K; zify_cond K. { exfalso. rewrite wz_unsigned in K by lia. lia. }
st1. st1. st1. st1.
replace (ret_pc (Z_to_bv 64 0x15488)) with (Z_to_bv 64 0x15488) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
st1. st1. st1. st1. st1.
lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ ?mX _) =>
assert (MR2 : rmrep st mX)
by (eapply rmrep_transport_high; [exact MR | exact MU | exact WM | intros l h [E|[]]; inversion E; subst; atop_facts; lia]) end.
apply evt_done. unfold rfmun_post. do 14 eexists. split; [rewrite (unsigned_lit 192304) by lia; reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|].
split; [rewrite (unsigned_lit 192304) by lia; change (192304 + -164) with 192140; exact ERR| exact MR2].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma rerrno_avoids_repfoot : forall st m a, rmrep st m -> 192140 <= a < 192144 -> ~ rrepfoot st a.
Proof.
intros st m a MR Ha. pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG).
intros [C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]].
- unfold RCTX in C. Local Ltac2 Set LiaHints.tbl := fun () => "0040>59323410545.1459323410545.2359323410545.3059323410545.3100000600A00W00mS2Ha1CS2Ha3Hin2D2S2Ha3Hin2Cb3Sb03Sb12D2S2Ha3Hin2Ca3Sa03Sa12D2".
lia.
- unfold RMLOCK in C. lia.
- unfold RNEED_LOCKS in C. lia.
- unfold RPAGE_SIZE in C. lia.
- destruct C as (ak & ar & Hak & Hin).
destruct (rarea_conc st ak ar WF Hak) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC).
destruct (WR _ _ Hra) as (_ & _ & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as [D1 D2]. pose proof (round_up_pg_ge (r_len ra)). lia.
- destruct C as (b & gh & Hb & Hin).
destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & SbA & RB0 & RBC).
destruct (WR _ _ Hrb) as (_ & _ & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as [D1 D2]. pose proof (round_up_pg_ge (r_len rb)). lia.
- destruct C as (rid & r & v & Hr & Hk & Hin & HC).
destruct (WR _ _ Hr) as (_ & _ & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as [D1 D2]. lia.
- unfold RGOT_SSP in C. lia.
- unfold RSSP_GUARD in C. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma rmrep_transport_frame_errno : forall st m m' (sp : Z),
rmrep st m -> munch [(sp - 48, sp); (192140, 192144)]%Z m m' -> wmono usegs m m' -> ATOP <= sp - 48 -> rmrep st m'.
Proof.
intros st m m' sp MR MU WM HS. eapply rmrep_transport_unowned; [exact MR | exact MU | exact WM |].
apply ivs_avoid_cons; [| apply ivs_avoid_cons; [| apply ivs_avoid_nil]].
- intros a Ha. pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG). atop_facts.
intros [C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]].
+ unfold RCTX in C. Local Ltac2 Set LiaHints.tbl := fun () => "0040>59311104486.2659311104486.3159311104486.3259315053158.1900000?00U00k01:S2HS2Ha3Hin3RBCS2HS2Ha3Hin2Cb3Sb13RBCS2HS2Ha3Hin2Ca3Sa13RBCS2HS2Ha5ATOPR1C".
lia.
+ unfold RMLOCK in C. lia.
+ unfold RNEED_LOCKS in C. lia.
+ unfold RPAGE_SIZE in C. lia.
+ destruct C as (ak & ar & Hak & Hin).
destruct (rarea_conc st ak ar WF Hak) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC). atop_facts. lia.
+ destruct C as (b & gh & Hb & Hin).
destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & SbA & RB0 & RBC). atop_facts. lia.
+ destruct C as (rid & r & v & Hr & Hk & Hin & HC).
destruct (WR _ _ Hr) as (_ & _ & _ & RBC & _). atop_facts. lia.
+ unfold RGOT_SSP in C. lia.
+ unfold RSSP_GUARD in C. lia.
- intros a Ha. eapply rerrno_avoids_repfoot; [exact MR | exact Ha].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma rfree_fin1 : forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 ra ew bw lw e' : word) F fc
(m : word -> option byte) (junk : list byte) (lo : Z) (st : mstate) (errv : word),
tp = Z_to_bv 64 RATP ->
rmrep st m -> mem_inv usegs m ->
rw_cells usegs m (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
le4 ew = le4 errv ->
rw_cells usegs m (errno_addr tp) [C4 e'] ->
stk usegs m lo (bv_unsigned sp + -48) -> ATOP <= lo -> lo <= bv_unsigned sp - 48 ->
evt usegs (rffin_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo [(bv_unsigned sp - 48, bv_unsigned sp); (192140, 192144)]%Z m st errv)
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 bw lw a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (errno_addr tp)) ew s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1549c) fc None m (seg_rom usegs)).
Proof.
intros until errv. intros TP MR MI FR EW ERR ST LO LOLE.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (192140, 192144)]%Z m) as MU.
pose proof (wmono_refl usegs m) as WM.
unfold RATP in *. atop_facts. subst tp.
Local Ltac2 Set LiaHints.tbl := fun () => "00>0>1800609155.65 24638473347.6425071629079.5927905021218.5739743004596.5943988483203.6351711223320.5654035953963.5954243526019.6357181542212.5664997134979.658701946673.59 8826107286.56 8841017104.55 00000100200300900:00;00<00K00L00U00V00W00X00YSSSS4LOLESSSS2LO4LOLE5ATOPRSS2LO4LOLESSSS".
rewrite (unsigned_lit 192304) in ERR by lia. change (192304 + -164) with 192140 in ERR.
rewrite (unsigned_lit 192304) by lia. change (192304 + -164) with 192140.
st1.
st1. st1. st1. st1. st1. st1. st1. st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR2 : rmrep st mX) by (eapply (rmrep_transport_frame_errno st m mX (bv_unsigned sp)); [exact MR | exact MU | exact WM | atop_facts; lia]) end.
release_frame FR ST (bv_unsigned sp).
apply evt_done. unfold rffin_post. do 16 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [| exact MR2].
rewrite (unsigned_lit 192304) by lia. change (192304 + -164) with 192140.
eapply rw_cells_congr; [| | | exact ERR]; [cbn [cells_bytes cbytes app]; rewrite EW; reflexivity| reflexivity| cbn; tauto].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC1.
