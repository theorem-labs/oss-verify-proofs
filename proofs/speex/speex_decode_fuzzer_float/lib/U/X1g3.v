(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bu X1cf X1cc X1bs X1c2 X1bn X1bj X1bk.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0qn X0px X0qc X0qp.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1m2 X1m3 X1m5 X1m6.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1ra X1qu X1qv X1qx X1r3 X1r4 X1nt.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition A_speex_bits_init : Z := 0x1c844.
Definition A_calloc : Z := 0x31788.
Definition BITS_CALLOC_STACK : Z := 8224.
Definition BITS_INIT_STACK : Z := 32 + BITS_CALLOC_STACK.

Definition bits_calloc_post {RCEIL : RunCeiling} (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(s : PState) (LB : list block) (n lo B : Z) (m : mem)
(r : option bptr) (s' : PState) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
/\ rw_cells rsegs m' (errno_addr tp) [C4 errv']
/\ rauxv_ok m' B
/\ rheap_pres LB (bv_unsigned sp) m m'
/\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
/\ match r with
| None => a0 = Z_to_bv 64 0 /\ RHEAP s' LB m'
| Some p => exists A,
a0 = Z_to_bv 64 A /\ rblock_range A n
/\ RHEAP s' ((p, A, n) :: LB) m'
/\ rw_cells rsegs m' A [CB (Z.to_nat n) (repeat (Z_to_bv 8 0) (Z.to_nat n))]
/\ (raddr_exposed s n -> A = ptr_addr s' p)
/\ rsmall_block s' p
end.

Definition bits_calloc_stmt {RCEIL : RunCeiling} : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(s : PState) (LB : list block) (m0 n0 lo B : Z) (errv : word),
RHEAP s LB m ->
rauxv_ok m B -> bv_unsigned sp <= B ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - BITS_CALLOC_STACK ->
rw_cells rsegs m (errno_addr tp) [C4 errv] ->
mem_inv rsegs m ->
tp = Z_to_bv 64 RATP ->
a0 = Z_to_bv 64 m0 -> a1 = Z_to_bv 64 n0 -> 0 <= m0 < 2^64 -> 0 <= n0 < 2^64 -> n0 * m0 <= RSMALL_MAX ->
implM rsegs (raw_calloc m0 n0) s
(bits_calloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB (n0 * m0) lo B m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_calloc) fc None m (seg_rom rsegs)).

Definition rheap_frame_stmt {RCEIL : RunCeiling} : Prop :=
forall s LB m m' W, RHEAP s LB m -> munch W m m' -> wmono rsegs m m' -> Forall (rclient_write_ok LB) W -> RHEAP s LB m'.

Definition speex_bits_init_post {RCEIL : RunCeiling} (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(s : PState) (LB : list block) (A lo B : Z) (m : mem)
(r : option (bits_st bptr)) (s' : PState) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
/\ rw_cells rsegs m' (errno_addr tp) [C4 errv']
/\ rauxv_ok m' B
/\ pres_except rsegs (rclient_addr LB (bv_unsigned sp)) [(A, A + 48)] m m'
/\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
/\ match r with
| None => RHEAP s' LB m' /\ (exists junk', rw_cells rsegs m' A [C8 (Z_to_bv 64 0); CB 40 junk'])
| Some b => exists D, RHEAP s' ((sb_chars b, D, 2000) :: LB) m' /\ rblock_range D 2000
/\ rsmall_block s' (sb_chars b)
/\ bits_rep rsegs m' A D b /\ bits_ok b
end.

Definition rheap_block_range_stmt {RCEIL : RunCeiling} : Prop :=
forall s LB m b, RHEAP s LB m -> In b LB -> rblock_range (blk_addr b) (blk_size b).

Lemma pres_except_of_rheap_pres : forall LB SP SP' X m m',
rheap_pres LB SP' m m' -> SP' <= SP -> pres_except rsegs (rclient_addr LB SP) X m m'.
Proof.
intros LB SP SP' X m m' H HS a Ha Hc _. apply H; [exact Ha|].
unfold rclient_addr in *. destruct Hc as [Hc|[Hc|Hc]]; [left; lia| right; left; exact Hc| right; right; exact Hc].
Qed.

Lemma le8_split_0 : le8 (Z_to_bv 64 0) = le4 (Z_to_bv 64 0) ++ le4 (Z_to_bv 64 0).
Proof. apply byte_list_eq. vm_compute. reflexivity. Qed.
Lemma le8_split_owner : le8 (Z_to_bv 64 4294967296) = le4 (Z_to_bv 64 0) ++ le4 (Z_to_bv 64 1).
Proof. apply byte_list_eq. vm_compute. reflexivity. Qed.
Lemma le8_split_bufsize : le8 (Z_to_bv 64 8589934592000) = le4 (Z_to_bv 64 0) ++ le4 (Z_to_bv 64 2000).
Proof. apply byte_list_eq. vm_compute. reflexivity. Qed.
Lemma init_data_bytes : zupd (zrepeat 0 MAX_CHARS_PER_FRAME) 0 0 = map bv_unsigned (repeat (Z_to_bv 8 0) 2000).
Proof. vm_compute. reflexivity. Qed.

Section F.
Context {RCEIL : RunCeiling}.
Hypothesis HC : bits_calloc_stmt.
Hypothesis HFR : rheap_frame_stmt.
Hypothesis HBR : rheap_block_range_stmt.

Ltac ntk := let K := fresh "K" in if_cases K; zify_cond K; [exfalso; lia | clear K].

#[using="Type"] Lemma outside_of_ranges : forall (lo SP : Z) X W a,
Forall (fun iv => (lo <= fst iv /\ snd iv <= SP) \/ In iv X) W -> (SP <= a \/ a < lo) -> ~ in_ivs X a -> outside W a.
Proof.
intros lo SP X W a FW CASES Hx. induction W as [|[lo' hi'] W IH]; [exact I|].
apply Forall_cons_iff in FW. destruct FW as [F1 FW]. cbn. split; [|apply IH; exact FW].
cbn in F1. destruct F1 as [F1|F1]; [lia|].
intros Hin. apply Hx. clear -Hin F1. induction X as [|iv X IH]; [destruct F1|].
cbn. destruct F1 as [E|F1]; [left; subst iv; cbn; lia| right; apply IH; exact F1].
Qed.

#[using="HBR"] Lemma pres_except_of_munch_client : forall s0 LB m0 (SP lo : Z) X W m m',
RHEAP s0 LB m0 -> alloc_ceiling <= lo -> lo <= SP ->
munch W m m' -> wmono rsegs m m' ->
Forall (fun iv => (lo <= fst iv /\ snd iv <= SP) \/ In iv X) W ->
pres_except rsegs (rclient_addr LB SP) X m m'.
Proof.
intros s0 LB m0 SP lo X W m m' HP CEIL LO MU WM FW.
eapply pres_except_of_munch; [exact MU| exact WM|].
intros a Ha Hc Hx. unfold alloc_ceiling in CEIL.
eapply outside_of_ranges; [exact FW| | exact Hx].
unfold rclient_addr, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in Hc.
destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [left; lia| right; lia|].
pose proof (HBR _ _ _ _ HP Hb) as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ _ R4 _ | sf_fb; destruct sfP_ as (_ & _ & _ & R4 & _) ]. unfold alloc_ceiling in R4. right. lia.
Qed.

#[using="Type"] Lemma outside_of_ranges_blk : forall (lo SP D n : Z) X W a,
Forall (fun iv => (lo <= fst iv /\ snd iv <= SP) \/ In iv X \/ (D <= fst iv /\ snd iv <= D + n)) W ->
(SP <= a \/ a < lo) -> ~ in_ivs X a -> ~ (D <= a < D + n) -> outside W a.
Proof.
intros lo SP D n X W a FW CASES Hx HD. induction W as [|[lo' hi'] W IH]; [exact I|].
apply Forall_cons_iff in FW. destruct FW as [F1 FW]. cbn. split; [|apply IH; exact FW].
cbn in F1. destruct F1 as [F1|[F1|F1]]; [lia| | lia].
intros Hin. apply Hx. clear -Hin F1. induction X as [|iv X IH]; [destruct F1|].
cbn. destruct F1 as [E|F1]; [left; subst iv; cbn; lia| right; apply IH; exact F1].
Qed.

#[using="HBR"] Lemma pres_except_of_munch_client_blk : forall s1 LB m1 (SP lo : Z) X W m m' p D n,
RHEAP s1 ((p, D, n) :: LB) m1 -> alloc_ceiling <= lo -> lo <= SP ->
munch W m m' -> wmono rsegs m m' ->
Forall (fun iv => (lo <= fst iv /\ snd iv <= SP) \/ In iv X \/ (D <= fst iv /\ snd iv <= D + n)) W ->
pres_except rsegs (rclient_addr LB SP) X m m'.
Proof.
intros s1 LB m1 SP lo X W m m' p D n HP CEIL LO MU WM FW.
eapply pres_except_of_munch; [exact MU| exact WM|].
intros a Ha Hc Hx. unfold alloc_ceiling in CEIL.
pose proof (HBR _ _ _ _ HP (or_introl eq_refl)) as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ _ D4 D5 | sf_fb; destruct sfP_ as (_ & _ & _ & D4 & D5) ]. cbn [blk_addr blk_size fst snd] in D4, D5. unfold alloc_ceiling in D4.
unfold rclient_addr, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in Hc.
destruct Hc as [Hc|[Hc|(b & Hb & Hr)]].
- eapply outside_of_ranges_blk; [exact FW| left; exact Hc| exact Hx| lia].
- eapply outside_of_ranges_blk; [exact FW| right; lia| exact Hx| lia].
- pose proof (HBR _ _ _ _ HP (or_intror Hb)) as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ _ R4 _ | sf_fb; destruct sfP_ as (_ & _ & _ & R4 & _) ]. unfold alloc_ceiling in R4.
eapply outside_of_ranges_blk; [exact FW| right; lia| exact Hx|].
pose proof (RHEAP_blocks_nodup_proof _ _ _ HP) as ND. cbn [map] in ND. apply (proj1 (List.NoDup_cons_iff _ _)) in ND. destruct ND as [NI _].
destruct (RHEAP_blocks_disjoint_proof _ _ _ (p, D, n) b HP (or_introl eq_refl) (or_intror Hb)) as [DJ|DJ].
{ intros E. apply NI. rewrite E. apply in_map. exact Hb. }
all: cbn [blk_addr blk_size fst snd] in DJ; lia.
Qed.

#[using="HC HFR HBR"] Lemma speex_bits_init_spec :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(s : PState) (LB : list block) (A lo B : Z) (errv : word) (junk : list byte),
RHEAP s LB m ->
rauxv_ok m B -> bv_unsigned sp <= B ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - BITS_INIT_STACK ->
rw_cells rsegs m (errno_addr tp) [C4 errv] ->
mem_inv rsegs m ->
tp = Z_to_bv 64 RATP ->
a0 = Z_to_bv 64 A -> rw_cells rsegs m A [CB 48 junk] -> bv_unsigned sp <= A -> A + 48 <= B -> A mod 8 = 0 ->
implM rsegs (speex_bits_init raw_calloc) s
(speex_bits_init_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB A lo B m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_speex_bits_init) fc None m (seg_rom rsegs)).
Proof.
intros until junk. intros HP AUX SPB ST CEIL LO ERR MI TP -> OBJ SPA AB AL.
unfold A_speex_bits_init, BITS_INIT_STACK, BITS_CALLOC_STACK in *.
pose proof CEIL as CEIL'. unfold alloc_ceiling in CEIL'.
pose proof (rw_cells_bound _ _ _ _ OBJ) as GB. cbn [cells_size csize Nat.add length] in GB.
pose proof (proj1 (proj1 OBJ)) as LJ. cbn in LJ. destruct LJ as [LJ _].
assert (ERRA : errno_addr tp = 316332) by (subst tp; rewrite unsigned_lit64 by (unfold RATP; lia); reflexivity).
rewrite ERRA in ERR.
unfold implM. iprefix.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
carve_frame 16%nat ST.
do 7 step.
apply evt_done. unfold speex_bits_init.
lazymatch goal with |- impl _ _ _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m1 end.
assert (HP1 : RHEAP s LB m1).
{ eapply HFR; [exact HP| exact MU| exact WM|]. constructor; [|constructor]. left. cbn. lia. }
assert (AUX1 : rauxv_ok m1 B).
{ eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [|constructor]. cbn. unfold RAUXV_CELL. lia. }
eapply (implM_bind rsegs).
{ eapply HC with (s := s) (LB := LB) (m0 := MAX_CHARS_PER_FRAME) (n0 := 1) (lo := lo) (B := B) (errv := errv);
try reflexivity; try exact HP1; try exact AUX1; try exact MI.
all: try (rewrite ?unsigned_lit64 by lia; unfold MAX_CHARS_PER_FRAME, RSMALL_MAX in *; lia).
all: rewrite ?unsigned_lit64 by lia.
all: try (rewrite ERRA; exact ERR); try exact TP; try exact ST; unfold BITS_CALLOC_STACK; lia. }
cbv beta. intros r s' ms' POST.
first [ sf_destruct 26%nat POST as x0 x1 x2 y0 y1 y2 y3 y4 y5 y6 y7 x3 x4 x5 x6 m2 errv2 -> MI2 ST2 ERR2 AUX2 PRES FA SO RES | sf_fb; destruct POST as (x0 & x1 & x2 & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & m2 & errv2 & -> & MI2 & ST2 & ERR2 & AUX2 & PRES & FA & SO & RES) ].
rewrite !unsigned_lit64 in ST2, PRES by lia. rewrite ERRA in ERR2.
replace (ret_pc (Z_to_bv 64 116832)) with (Z_to_bv 64 116832) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp + -16) [C8 s0; C8 ra]).
{ eapply rheap_pres_rw_cells; [exact PRES| exact FR| left; cbn; lia]. }
assert (OBJ2 : rw_cells rsegs m2 A [CB 48 junk]).
{ eapply rheap_pres_rw_cells; [exact PRES| exact OBJ| left; cbn; lia]. }
assert (P01 : pres_except rsegs (rclient_addr LB (bv_unsigned sp)) [(A, A + 48)] m m2).
{ eapply pres_except_trans.
- eapply (pres_except_of_munch_client s LB m); [exact HP| exact CEIL| lia| exact MU| exact WM|].
constructor; [left; cbn; lia| constructor].
- eapply pres_except_of_rheap_pres; [exact PRES| lia]. }
clear FR OBJ MU WM ST HP1 AUX1 MI ERR AUX.
destruct r as [p|].
-
first [ sf_destruct 7%nat RES as D -> BR HP2 BLK EXP SMALL | sf_fb; destruct RES as (D & -> & BR & HP2 & BLK & EXP & SMALL) ].
pose proof BR as sfP_; first [ sf_destruct 5%nat sfP_ as BR1 BR2 BR3 BR4 BR5 | sf_fb; destruct sfP_ as (BR1 & BR2 & BR3 & BR4 & BR5) ]. unfold alloc_ceiling in BR4.
change (1 * MAX_CHARS_PER_FRAME) with 2000 in HP2, BR, BR3, BR4, BR5.
change (Z.to_nat (1 * MAX_CHARS_PER_FRAME)) with 2000%nat in BLK.
pose proof (munch_refl [(A, A + 48); (D, D + 2000); (bv_unsigned sp + -16, bv_unsigned sp)] m2) as MU.
pose proof (wmono_refl rsegs m2) as WM.
assert (DA : D + 2000 <= A) by lia.
apply implM_ret.
zstep. ntk.
zstep. rewrite land7_mod8, AL.
zstep. ntk.
step. step. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit64 in K by lia; lia|]. clear K.
do 2 step. do 6 lstep. do 4 step.
release_frame FR2 ST2 (bv_unsigned sp).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => set (mF := mx) in * end.

assert (BLKF : rw_cells rsegs mF D [CB 2000 (repeat (Z_to_bv 8 0) 2000)]).
{ eapply rw_cells_samebytes; [exact BLK| split; [apply repeat_length| exact I]| vm_compute; reflexivity| reflexivity]. }
unfold speex_bits_init_post. finish.
+ rewrite ERRA. exact ERR2.
+ eapply rauxv_ok_frame; [exact AUX2| exact MU| exact WM|].
constructor; [cbn; unfold RAUXV_CELL; lia| constructor; [cbn; unfold RAUXV_CELL; lia| constructor; [cbn; unfold RAUXV_CELL; lia| constructor]]].
+ eapply pres_except_trans; [exact P01|].
eapply (pres_except_of_munch_client_blk s' LB m2 (bv_unsigned sp) lo _ _ _ _ p D 2000); [exact HP2| exact CEIL| lia| exact MU| exact WM|].
constructor; [right; left; left; reflexivity| constructor; [right; right; cbn; lia| constructor; [left; cbn; lia| constructor]]].
+ cbn [sb_chars speex_bits_reset]. exists D.
split; [|split; [exact BR| split; [exact SMALL| split]]].
* eapply HFR; [exact HP2| exact MU| exact WM|].
constructor; [left; cbn; lia| constructor; [right; right; exists (p, D, 2000); split; [left; reflexivity| cbn; lia]| constructor; [left; cbn; lia| constructor]]].
*
unfold bits_rep, speex_bits_reset; cbn. split; [|split].
-- pose proof (proj1 (proj1 OBJ2)) as WF2. cbn [cells_wf cell_wf] in WF2.
lazymatch type of OBJ2 with rw_cells _ _ _ [_; _; _; _; _; _; CB 16 ?jj] => exists jj end.
split; [tauto|].
unfold bits_cells; cbn.
eapply rw_cells_samebytes; [exact OBJ2| cbn [cells_wf cell_wf]; tauto| | reflexivity].
cbn [cells_bytes cbytes]. rewrite le8_split_0. rewrite <- !app_assoc. reflexivity.
-- exists (repeat (Z_to_bv 8 0) 2000). split; [apply (u8arr_of_rw_cells rsegs mF D 2000); exact BLKF|].
apply init_data_bytes.
-- unfold bits_side, BITS_BUF_MAX, BITS_SIZEOF, MAX_CHARS_PER_FRAME. cbn. lia.
* unfold bits_ok, speex_bits_reset, bits_pos; cbn [sb_data sb_nbBits sb_charPtr sb_bitPtr sb_owner sb_overflow sb_buf_size].
rewrite zlength_zupd, zlength_zrepeat by (unfold MAX_CHARS_PER_FRAME; lia). unfold MAX_CHARS_PER_FRAME. lia.
-
destruct RES as [-> HP2].
pose proof (munch_refl [(A, A + 48); (bv_unsigned sp + -16, bv_unsigned sp)] m2) as MU.
pose proof (wmono_refl rsegs m2) as WM.
apply implM_ret.
zstep. ntk.
zstep. rewrite land7_mod8, AL.
zstep. ntk.
lstep. step. if_cases K; zify_cond K; [| exfalso; rewrite ?unsigned_lit64 in K by lia; lia]. clear K.
do 4 step.
release_frame FR2 ST2 (bv_unsigned sp).
unfold speex_bits_init_post. finish.
+ rewrite ERRA. exact ERR2.
+ eapply rauxv_ok_frame; [exact AUX2| exact MU| exact WM|].
constructor; [cbn; unfold RAUXV_CELL; lia| constructor; [cbn; unfold RAUXV_CELL; lia| constructor]].
+ eapply pres_except_trans; [exact P01|].
eapply (pres_except_of_munch_client s LB m); [exact HP| exact CEIL| | exact MU| exact WM|]; [lia|].
constructor; [right; left; reflexivity| constructor; [left; cbn; lia| constructor]].
+ eapply HFR; [exact HP2| exact MU| exact WM|].
constructor; [left; cbn; lia| constructor; [left; cbn; lia| constructor]].
+ eexists. exact OBJ2.
Qed.
End F.
