(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bu X1cf X1cc X1bs X1c2 X1bn X1bj X1bk X1c0.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0qn X0px X0qc X0qp.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ff.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1m2 X1m3 X1m5 X1m6 X1ik X1ij.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1ra X1qu X1qv X1qx X1r3 X1r4 X1qz X1r0.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition sync_clear_post {RCEIL : RunCeiling} (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(s : PState) (LB' : list block) (A lo B : Z) (errv : word) (m : mem)
(r : sync_st bptr) (s' : PState) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
/\ rw_cells rsegs m' (errno_addr tp) [C4 errv] /\ rauxv_ok m' B
/\ cmod [(bv_unsigned sp - 16, bv_unsigned sp); (A, A + 32)] LB' (bv_unsigned sp) m m'
/\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
/\ RHEAP s' LB' m'
/\ r = ogg_sync_init /\ rw_cells rsegs m' A (sync_cells 0 ogg_sync_init).

Lemma lb_remove_sub : forall p LB b, In b (lb_remove p LB) -> In b LB.
Proof.
intros p LB b H. unfold lb_remove in H. induction LB as [|x LB IH]; cbn in *; [exact H|].
destruct (negb (bptr_eqb (blk_id x) p)); cbn in H; [destruct H as [->|H]; [left; reflexivity| right; apply IH; exact H]| right; apply IH; exact H].
Qed.

Lemma sync_cells_raw : forall m A D (sy : sync_st bptr),
rw_cells rsegs m A (sync_cells D sy) -> exists j24, rw_cells rsegs m A [C8 (wz D); CB 24 j24].
Proof.
intros m A D sy H. unfold sync_cells in H.
eexists. apply (rw_cells_merge rsegs m A [C8 (wz D)] [C4 (wz (sy_storage sy)); C4 (wz (sy_fill sy)); C4 (wz (sy_returned sy));
C4 (wz (sy_unsynced sy)); C4 (wz (sy_headerbytes sy)); C4 (wz (sy_bodybytes sy))] []). exact H.
Qed.
Lemma sync_cells_zero : forall m A,
rw_cells rsegs m A [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
rw_cells rsegs m A (sync_cells 0 ogg_sync_init).
Proof.
intros m A H. eapply rw_cells_recell; [exact H| cbn; repeat split; reflexivity| vm_compute; reflexivity| reflexivity].
Qed.

Section SC.
Context {RCEIL : RunCeiling}.
Hypothesis HF : rfree_stmt.

#[using="HF"] Lemma ogg_sync_clear_spec :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(s : PState) (LB : list block) (sy : sync_st bptr) (A D lo B : Z) (errv : word),
RHEAP s LB m ->
match sy_data sy with Some p => In (p, D, sy_storage sy) LB | None => D = 0 end ->
rauxv_ok m B -> bv_unsigned sp <= B -> bv_unsigned sp <= A -> A + 32 <= B ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 16 - RFREE_STACK ->
rw_cells rsegs m (errno_addr tp) [C4 errv] ->
mem_inv rsegs m ->
tp = Z_to_bv 64 RATP ->
a0 = Z_to_bv 64 A -> rw_cells rsegs m A (sync_cells D sy) ->
implM rsegs (ogg_sync_clear raw_free sy) s
(sync_clear_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s
(match sy_data sy with Some p => lb_remove p LB | None => LB end) A lo B errv m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_ogg_sync_clear) fc None m (seg_rom rsegs)).
Proof.
intros until errv. intros HP HIN AUX SPB SPA AB ST CEIL LO ERR MI TP -> SY.
unfold A_ogg_sync_clear. pose proof CEIL as CEIL'. unfold alloc_ceiling in CEIL'. unfold RFREE_STACK in LO.
unfold sync_cells, wz in SY.
pose proof (rw_cells_bound _ _ _ _ SY) as GB. cbn [cells_size csize Nat.add] in GB.
rewrite TP, unsigned_lit in ERR by (unfold RATP; lia). unfold RATP in ERR. replace (316496 + -164) with 316332 in ERR by reflexivity.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (A, A + 32)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
pose proof AUX as AUX0. first [ sf_destruct 16%nat AUX0 as av x3_ x4_ x5_ x16_ x6_ x11_ x12_ x23_ rnd _ _ _ AC1 AC2 _ | sf_fb; destruct AUX0 as (av & x3_ & x4_ & x5_ & x16_ & x6_ & x11_ & x12_ & x23_ & rnd & _ & _ & _ & AC1 & AC2 & _) ].
unfold ogg_sync_clear.
destruct (sy_data sy) as [p|].
-
pose proof (RHEAP_block_range_proof _ _ _ _ HP HIN) as BR. cbn [blk_addr blk_size fst snd] in BR. first [ sf_destruct 5%nat BR as BR1 BR2 BR3 BR4 BR5 | sf_fb; destruct BR as (BR1 & BR2 & BR3 & BR4 & BR5) ].
unfold implM. iprefix.
zstep. if_cases CN0; zify_cond CN0; rewrite ?unsigned_lit in CN0 by lia; [exfalso; lia|].
carve_frame 16%nat ST.
zstep. zstep. zstep. zstep. zstep.
zstep. if_cases CN1; zify_cond CN1; rewrite ?unsigned_lit, ?land_ones64, ?Z.mod_small in CN1 by lia; [exfalso; unfold alloc_ceiling in *; lia|].
zstep.

apply evt_done. eapply implM_bind.
{ unfold rfree_stmt, rfree_stmt_at in HF.
eapply HF with (s := s) (LB := LB) (p := p) (A := D) (n := sy_storage sy) (lo := lo) (B := B) (errv := errv).
- eapply RHEAP_frame_proof; [exact HP| exact MU| exact WM|].
apply Forall_cons; [left; cbn; lia|]. apply Forall_cons; [left; cbn; lia|]. apply Forall_nil.
- exact HIN.
- eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|].
apply Forall_cons; [cbn; unfold RAUXV_CELL; lia|]. apply Forall_cons; [cbn; unfold RAUXV_CELL; lia|]. apply Forall_nil.
- rewrite unsigned_lit by lia. lia.
- rewrite unsigned_lit by lia. exact ST.
- exact CEIL.
- rewrite unsigned_lit by lia. unfold RFREE_STACK. lia.
- rewrite TP, unsigned_lit by (unfold RATP; lia). unfold RATP. exact ERR.
- exact MI.
- exact TP.
- reflexivity. }
cbv beta. intros [] ps2 ms2 PO.
first [ sf_destruct 25%nat PO as t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 -> MI2 ST2 ERR2 AUX2 HPR FA2 SO2 HP2 | sf_fb; destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> & MI2 & ST2 & ERR2 & AUX2 & HPR & FA2 & SO2 & HP2) ].
rewrite unsigned_lit in ST2, HPR by lia.
rewrite TP, unsigned_lit in ERR2 by (unfold RATP; lia). unfold RATP in ERR2. replace (316496 + -164) with 316332 in ERR2 by reflexivity.
replace (ret_pc (Z_to_bv 64 197800)) with (Z_to_bv 64 197800) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

lazymatch goal with FRx : rw_cells rsegs _ (bv_unsigned sp + -16) _ |- _ =>
apply (rheap_pres_rw_cells _ _ _ _ _ _ HPR) in FRx; [| left; cbn; lia]; rename FRx into FR2 end.
apply (rheap_pres_rw_cells _ _ _ _ _ _ HPR) in SY; [| left; cbn; lia].
rename MU into MU0. rename WM into WM0. pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (A, A + 32)] m2) as MU. pose proof (wmono_refl rsegs m2) as WM.
destruct (sync_cells_raw _ _ _ _ ltac:(unfold sync_cells, wz; exact SY)) as [j24 SYR]. clear SY. unfold wz in SYR.
apply implM_ret.

lstep. lstep. lstep. lstep. zstep. zstep. zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
lazymatch goal with SYx : rw_cells rsegs mx A _ |- _ => pose proof (sync_cells_zero mx A SYx) as SYZ; clear SYx end end.
lazymatch goal with FRx : rw_cells rsegs _ (bv_unsigned sp + -16) _ |- _ => release_frame FRx ST2 (bv_unsigned sp) end.
zstep. zstep.
apply evt_done. unfold sync_clear_post. sf_eexists 14%nat.
lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => exists mx end.
split; [reflexivity|]. split; [assumption|]. split; [assumption|].
split. { rewrite TP, unsigned_lit by (unfold RATP; lia). unfold RATP. assumption. }
split. { eapply rauxv_ok_frame; [exact AUX2| exact MU| exact WM|].
apply Forall_cons; [cbn; unfold RAUXV_CELL; lia|]. apply Forall_cons; [cbn; unfold RAUXV_CELL; lia|]. apply Forall_nil. }
split. { lazymatch type of MU0 with munch ?W0 m ?ma => lazymatch type of MU with munch _ ?mb ?mc =>
apply (cmod_trans _ _ _ m ma mc); [| apply (cmod_trans _ _ _ ma mb mc)];
[ apply (cmod_weaken W0 _ LB _ (bv_unsigned sp) (bv_unsigned sp)); [apply cmod_of_munch; [exact MU0| exact WM0] | lia | apply lb_remove_sub | intros xq Hxq; exact Hxq]
| apply (cmod_weaken W0 _ (lb_remove p LB) _ (bv_unsigned sp + -16) (bv_unsigned sp));
[apply cmod_of_rheap_pres; exact HPR | lia | intros bq Hbq; exact Hbq | intros xq Hxq; exact Hxq]
| apply (cmod_weaken W0 _ (lb_remove p LB) _ (bv_unsigned sp) (bv_unsigned sp)); [apply cmod_of_munch; [exact MU| exact WM] | lia | intros bq Hbq; exact Hbq | intros xq Hxq; exact Hxq] ]
end end. }
split; [exact FA2|]. split; [exact SO2|].
split. { eapply RHEAP_frame_proof; [exact HP2| exact MU| exact WM|].
apply Forall_cons; [left; cbn; lia|]. apply Forall_cons; [left; cbn; lia|]. apply Forall_nil. }
split; [reflexivity| exact SYZ].
-
subst D. apply implM_ret.
zstep. if_cases CN0; zify_cond CN0; rewrite ?unsigned_lit in CN0 by lia; [exfalso; lia|].
carve_frame 16%nat ST.
zstep. zstep. zstep. zstep. zstep.
zstep. if_cases CN1; zify_cond CN1; [| exfalso; apply CN1; reflexivity].
destruct (sync_cells_raw _ _ _ _ ltac:(unfold sync_cells, wz; exact SY)) as [j24 SYR]. clear SY. unfold wz in SYR.
lstep. lstep. lstep. lstep. zstep. zstep. zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
lazymatch goal with SYx : rw_cells rsegs mx A _ |- _ => pose proof (sync_cells_zero mx A SYx) as SYZ; clear SYx end end.
lazymatch goal with FRx : rw_cells rsegs _ (bv_unsigned sp + -16) _ |- _ => release_frame FRx ST (bv_unsigned sp) end.
zstep. zstep.
apply evt_done. unfold sync_clear_post. sf_eexists 14%nat.
lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => exists mx end.
split; [reflexivity|]. split; [assumption|]. split; [assumption|].
split. { rewrite TP, unsigned_lit by (unfold RATP; lia). unfold RATP. assumption. }
split. { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|].
apply Forall_cons; [cbn; unfold RAUXV_CELL; lia|]. apply Forall_cons; [cbn; unfold RAUXV_CELL; lia|]. apply Forall_nil. }
split. { apply cmod_of_munch; [exact MU| exact WM]. }
split; [reflexivity|]. split; [reflexivity|].
split. { eapply RHEAP_frame_proof; [exact HP| exact MU| exact WM|].
apply Forall_cons; [left; cbn; lia|]. apply Forall_cons; [left; cbn; lia|]. apply Forall_nil. }
split; [reflexivity| exact SYZ].
Qed.
End SC.

Definition lb_remove_opt (o : option bptr) (LB : list block) : list block :=
match o with Some p => lb_remove p LB | None => LB end.

Lemma bptr_eqb_false : forall p q : bptr, p <> q -> bptr_eqb p q = false.
Proof.
intros [i o] [i' o'] NE. unfold bptr_eqb; cbn [fst snd].
destruct (Z.eqb_spec o o'); [|apply andb_false_r].
destruct (aptr_eqb i i') eqn:E; [|reflexivity]. exfalso. apply NE.
unfold aptr_eqb in E. apply andb_prop in E. destruct E as [E1 E2]. apply N.eqb_eq in E1. apply Z.eqb_eq in E2.
destruct i, i'; cbn in *; subst; reflexivity.
Qed.
Lemma lb_remove_keep : forall p LB b, In b LB -> blk_id b <> p -> In b (lb_remove p LB).
Proof.
intros p LB b H NE. unfold lb_remove. induction LB as [|x LB IH]; cbn in *; [exact H|].
destruct H as [->|H].
- rewrite (bptr_eqb_false _ _ NE). cbn. left; reflexivity.
- destruct (negb _); [right|]; apply IH; exact H.
Qed.
Lemma lb_remove_opt_sub : forall o LB b, In b (lb_remove_opt o LB) -> In b LB.
Proof. intros [p|] LB b H; [eapply lb_remove_sub; exact H| exact H]. Qed.

Definition stream_blocks (LB : list block) (os : stream_st bptr) (Bd L Gv : Z) : Prop :=
(match os_body_data os with Some p => exists n, In (p, Bd, n) LB | None => Bd = 0 end) /\
(match os_lacing_vals os with Some p => exists n, In (p, L, n) LB | None => L = 0 end) /\
(match os_granule_vals os with Some p => exists n, In (p, Gv, n) LB | None => Gv = 0 end) /\
(forall p q, os_body_data os = Some p -> os_lacing_vals os = Some q -> p <> q) /\
(forall p q, os_body_data os = Some p -> os_granule_vals os = Some q -> p <> q) /\
(forall p q, os_lacing_vals os = Some p -> os_granule_vals os = Some q -> p <> q).

Definition stream_clear_LB (LB : list block) (os : stream_st bptr) : list block :=
lb_remove_opt (os_granule_vals os) (lb_remove_opt (os_lacing_vals os) (lb_remove_opt (os_body_data os) LB)).

Definition zero_hdr : list byte := repeat (Z_to_bv 8 0) 284.

Definition memset_postZ (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(D C N : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(D, D + N)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ rw_cells rsegs m' D [CB (Z.to_nat N) (repeat (Z_to_bv 8 (C mod 256)) (Z.to_nat N))].
Lemma memset_callZ : forall ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (q D C N : Z) (junk : list byte),
rw_cells rsegs m D [CB (Z.to_nat N) junk] ->
mem_inv rsegs m ->
(0 <= q < 2^64)%Z -> (0 <= D < 2^64)%Z -> (0 <= C < 2^64)%Z -> (0 <= N < 2^64)%Z ->
evt rsegs (memset_postZ ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D C N m)
(MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 C) (Z_to_bv 64 N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x3a1dc) fc None m (seg_rom rsegs)).
Proof.
intros until junk. intros DST MI Hq HD HC HN.
assert (Ed : bv_unsigned (Z_to_bv 64 D) = D) by (apply unsigned_lit; lia).
assert (Ec : bv_unsigned (Z_to_bv 64 C) = C) by (apply unsigned_lit; lia).
assert (En : bv_unsigned (Z_to_bv 64 N) = N) by (apply unsigned_lit; lia).
eapply evt_mono.
{ eapply (X1ff.memset_spec ra (Z_to_bv 64 q)); rewrite ?Ed, ?En; eauto. }
intros ms' P. unfold X1ff.memset_post in P. rewrite !Ed, !Ec, !En in P. exact P.
Qed.

Lemma stream_cells_zero : forall m A,
rw_cells rsegs m A [CB 408 (repeat (Z_to_bv 8 0) 408)] -> rw_cells rsegs m A (stream_cells 0 0 0 zero_hdr stream_zero).
Proof.
intros m A H. eapply rw_cells_recell; [exact H| vm_compute; repeat split; reflexivity| vm_compute; reflexivity| reflexivity].
Qed.

Definition stream_clear_post {RCEIL : RunCeiling} (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(s : PState) (LB' : list block) (A lo B : Z) (errv : word) (m : mem)
(r : stream_st bptr) (s' : PState) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
/\ rw_cells rsegs m' (errno_addr tp) [C4 errv] /\ rauxv_ok m' B
/\ cmod [(bv_unsigned sp - 16, bv_unsigned sp); (A, A + 408)] LB' (bv_unsigned sp) m m'
/\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
/\ RHEAP s' LB' m'
/\ r = stream_zero /\ rw_cells rsegs m' A (stream_cells 0 0 0 zero_hdr stream_zero).

Section STC.
Context {RCEIL : RunCeiling}.
Hypothesis HF : rfree_stmt.

#[using="HF"] Lemma free_site1 : forall {R} (k : unit -> @X1qx.M PState R) (Q : R -> PState -> machine_state -> Prop)
(s : PState) (LB : list block) (o : option bptr) (X A lo B : Z) (errv : word) (hdr : list byte)
(sp gp tp : word) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w11 w12 w13 w14 w15 w16 w17 sv rv : word)
(x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem),
RHEAP s LB m -> match o with Some p => exists n, In (p, X, n) LB | None => X = 0 end ->
rauxv_ok m B -> bv_unsigned sp <= B -> bv_unsigned sp <= A -> A + 408 <= B ->
stk rsegs m lo (bv_unsigned sp + -16) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 16 - RFREE_STACK ->
rw_cells rsegs m 316332 [C4 errv] -> mem_inv rsegs m -> tp = Z_to_bv 64 RATP ->
rw_cells rsegs m (bv_unsigned sp + -16) [C8 sv; C8 rv] ->
rw_cells rsegs m A [C8 (Z_to_bv 64 X); C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; CB 284 hdr; C4 w11; C4 w12; C4 w13; C8 w14; C8 w15; C8 w16; C8 w17] ->
(forall (m' : mem) (s' : PState) (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
RHEAP s' (lb_remove_opt o LB) m' -> rauxv_ok m' B -> stk rsegs m' lo (bv_unsigned sp + -16) ->
rw_cells rsegs m' 316332 [C4 errv] -> mem_inv rsegs m' ->
cmod [(bv_unsigned sp - 16, bv_unsigned sp); (A, A + 408)] (lb_remove_opt o LB) (bv_unsigned sp) m m' ->
ps_fa s' = ps_fa s -> ps_so s' = ps_so s ->
rw_cells rsegs m' (bv_unsigned sp + -16) [C8 sv; C8 rv] ->
rw_cells rsegs m' A [C8 (Z_to_bv 64 X); C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; CB 284 hdr; C4 w11; C4 w12; C4 w13; C8 w14; C8 w15; C8 w16; C8 w17] ->
implM rsegs (k tt) s' Q
(MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp y5 y6 y7 (Z_to_bv 64 A) x9 y10 y11 y12 y13 y14 y15 y16 y17
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 y28 y29 y30 y31)
F (Z_to_bv 64 196816) fc None m' (seg_rom rsegs))) ->
implM rsegs (X1qx.mbind (mfree_opt raw_free o) k) s Q
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp x5 x6 x7 (Z_to_bv 64 A) x9 (Z_to_bv 64 A) x11 x12 x13 x14 x15 x16 x17
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
F (Z_to_bv 64 196804) fc None m (seg_rom rsegs)).
Proof.
intros until m. intros HP HIN AUX SPB SPA AB ST CEIL LO ERR MI TP FR OS K.
pose proof CEIL as CEIL'. unfold alloc_ceiling in CEIL'. unfold RFREE_STACK in LO.
pose proof (rw_cells_bound _ _ _ _ OS) as GB. cbn [cells_size csize Nat.add] in GB.
pose proof AUX as AUX0. first [ sf_destruct 16%nat AUX0 as av x3_ x4_ x5_ x16_ x6_ x11_ x12_ x23_ rnd _ _ _ AC1 AC2 _ | sf_fb; destruct AUX0 as (av & x3_ & x4_ & x5_ & x16_ & x6_ & x11_ & x12_ & x23_ & rnd & _ & _ & _ & AC1 & AC2 & _) ].
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (A, A + 408)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
destruct o as [p|].
- destruct HIN as [n HIN]. pose proof (RHEAP_block_range_proof _ _ _ _ HP HIN) as BR. cbn [blk_addr blk_size fst snd] in BR.
first [ sf_destruct 5%nat BR as BR1 BR2 BR3 BR4 BR5 | sf_fb; destruct BR as (BR1 & BR2 & BR3 & BR4 & BR5) ].
unfold implM. iprefix.
zstep. zstep. if_cases CN; zify_cond CN; rewrite ?unsigned_lit, ?land_ones64, ?Z.mod_small in CN by lia; [exfalso; unfold alloc_ceiling in *; lia|].
zstep. apply evt_done. cbn [mfree_opt]. eapply implM_bind.
{ unfold rfree_stmt, rfree_stmt_at in HF.
eapply HF with (s := s) (LB := LB) (p := p) (A := X) (n := n) (lo := lo) (B := B) (errv := errv).
- eapply RHEAP_frame_proof; [exact HP| exact MU| exact WM|].
apply Forall_cons; [left; cbn; lia|]. apply Forall_cons; [left; cbn; lia|]. apply Forall_nil.
- exact HIN.
- eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|].
apply Forall_cons; [cbn; unfold RAUXV_CELL; lia|]. apply Forall_cons; [cbn; unfold RAUXV_CELL; lia|]. apply Forall_nil.
- rewrite unsigned_lit by lia. lia.
- rewrite unsigned_lit by lia. exact ST.
- exact CEIL.
- rewrite unsigned_lit by lia. unfold RFREE_STACK. lia.
- rewrite TP, unsigned_lit by (unfold RATP; lia). unfold RATP. exact ERR.
- exact MI.
- exact TP.
- reflexivity. }
cbv beta. intros [] ps ms PO.
first [ sf_destruct 25%nat PO as t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' -> MI' ST' ERR' AUX' HPR FA SO HP' | sf_fb; destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MI' & ST' & ERR' & AUX' & HPR & FA & SO & HP') ].
rewrite unsigned_lit in ST', HPR by lia.
rewrite TP, unsigned_lit in ERR' by (unfold RATP; lia). unfold RATP in ERR'. replace (316496 + -164) with 316332 in ERR' by reflexivity.
replace (ret_pc (Z_to_bv 64 196816)) with (Z_to_bv 64 196816) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
apply (rheap_pres_rw_cells _ _ _ _ _ _ HPR) in FR; [| left; cbn; lia].
apply (rheap_pres_rw_cells _ _ _ _ _ _ HPR) in OS; [| left; cbn; lia].
eapply K; try eassumption.
cbn [lb_remove_opt].
apply (cmod_weaken [(bv_unsigned sp - 16, bv_unsigned sp); (A, A + 408)] _ (lb_remove p LB) _ (bv_unsigned sp + -16) (bv_unsigned sp));
[apply cmod_of_rheap_pres; exact HPR | lia | intros bq Hbq; exact Hbq | intros xq Hxq; exact Hxq].
- subst X. unfold implM. iprefix.
zstep. zstep. if_cases CN; zify_cond CN; [| exfalso; apply CN; reflexivity].
apply evt_done. cbn [mfree_opt]. apply implM_retb.
eapply K; try eassumption; try reflexivity. apply cmod_refl.
Qed.

#[using="HF"] Lemma free_site2 : forall {R} (k : unit -> @X1qx.M PState R) (Q : R -> PState -> machine_state -> Prop)
(s : PState) (LB : list block) (o : option bptr) (X A lo B : Z) (errv : word) (hdr : list byte)
(sp gp tp : word) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w11 w12 w13 w14 w15 w16 w17 sv rv : word)
(x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem),
RHEAP s LB m -> match o with Some p => exists n, In (p, X, n) LB | None => X = 0 end ->
rauxv_ok m B -> bv_unsigned sp <= B -> bv_unsigned sp <= A -> A + 408 <= B ->
stk rsegs m lo (bv_unsigned sp + -16) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 16 - RFREE_STACK ->
rw_cells rsegs m 316332 [C4 errv] -> mem_inv rsegs m -> tp = Z_to_bv 64 RATP ->
rw_cells rsegs m (bv_unsigned sp + -16) [C8 sv; C8 rv] ->
rw_cells rsegs m A [C8 w0; C8 w1; C8 w2; C8 w3; C8 (Z_to_bv 64 X); C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; CB 284 hdr; C4 w11; C4 w12; C4 w13; C8 w14; C8 w15; C8 w16; C8 w17] ->
(forall (m' : mem) (s' : PState) (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
RHEAP s' (lb_remove_opt o LB) m' -> rauxv_ok m' B -> stk rsegs m' lo (bv_unsigned sp + -16) ->
rw_cells rsegs m' 316332 [C4 errv] -> mem_inv rsegs m' ->
cmod [(bv_unsigned sp - 16, bv_unsigned sp); (A, A + 408)] (lb_remove_opt o LB) (bv_unsigned sp) m m' ->
ps_fa s' = ps_fa s -> ps_so s' = ps_so s ->
rw_cells rsegs m' (bv_unsigned sp + -16) [C8 sv; C8 rv] ->
rw_cells rsegs m' A [C8 w0; C8 w1; C8 w2; C8 w3; C8 (Z_to_bv 64 X); C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; CB 284 hdr; C4 w11; C4 w12; C4 w13; C8 w14; C8 w15; C8 w16; C8 w17] ->
implM rsegs (k tt) s' Q
(MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp y5 y6 y7 (Z_to_bv 64 A) x9 y10 y11 y12 y13 y14 y15 y16 y17
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 y28 y29 y30 y31)
F (Z_to_bv 64 196828) fc None m' (seg_rom rsegs))) ->
implM rsegs (X1qx.mbind (mfree_opt raw_free o) k) s Q
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp x5 x6 x7 (Z_to_bv 64 A) x9 x10 x11 x12 x13 x14 x15 x16 x17
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
F (Z_to_bv 64 196816) fc None m (seg_rom rsegs)).
Proof.
intros until m. intros HP HIN AUX SPB SPA AB ST CEIL LO ERR MI TP FR OS K.
pose proof CEIL as CEIL'. unfold alloc_ceiling in CEIL'. unfold RFREE_STACK in LO.
pose proof (rw_cells_bound _ _ _ _ OS) as GB. cbn [cells_size csize Nat.add] in GB.
pose proof AUX as AUX0. first [ sf_destruct 16%nat AUX0 as av x3_ x4_ x5_ x16_ x6_ x11_ x12_ x23_ rnd _ _ _ AC1 AC2 _ | sf_fb; destruct AUX0 as (av & x3_ & x4_ & x5_ & x16_ & x6_ & x11_ & x12_ & x23_ & rnd & _ & _ & _ & AC1 & AC2 & _) ].
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (A, A + 408)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
destruct o as [p|].
- destruct HIN as [n HIN]. pose proof (RHEAP_block_range_proof _ _ _ _ HP HIN) as BR. cbn [blk_addr blk_size fst snd] in BR.
first [ sf_destruct 5%nat BR as BR1 BR2 BR3 BR4 BR5 | sf_fb; destruct BR as (BR1 & BR2 & BR3 & BR4 & BR5) ].
unfold implM. iprefix.
zstep. zstep. if_cases CN; zify_cond CN; rewrite ?unsigned_lit, ?land_ones64, ?Z.mod_small in CN by lia; [exfalso; unfold alloc_ceiling in *; lia|].
zstep. apply evt_done. cbn [mfree_opt]. eapply implM_bind.
{ unfold rfree_stmt, rfree_stmt_at in HF.
eapply HF with (s := s) (LB := LB) (p := p) (A := X) (n := n) (lo := lo) (B := B) (errv := errv).
- eapply RHEAP_frame_proof; [exact HP| exact MU| exact WM|].
apply Forall_cons; [left; cbn; lia|]. apply Forall_cons; [left; cbn; lia|]. apply Forall_nil.
- exact HIN.
- eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|].
apply Forall_cons; [cbn; unfold RAUXV_CELL; lia|]. apply Forall_cons; [cbn; unfold RAUXV_CELL; lia|]. apply Forall_nil.
- rewrite unsigned_lit by lia. lia.
- rewrite unsigned_lit by lia. exact ST.
- exact CEIL.
- rewrite unsigned_lit by lia. unfold RFREE_STACK. lia.
- rewrite TP, unsigned_lit by (unfold RATP; lia). unfold RATP. exact ERR.
- exact MI.
- exact TP.
- reflexivity. }
cbv beta. intros [] ps ms PO.
first [ sf_destruct 25%nat PO as t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' -> MI' ST' ERR' AUX' HPR FA SO HP' | sf_fb; destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MI' & ST' & ERR' & AUX' & HPR & FA & SO & HP') ].
rewrite unsigned_lit in ST', HPR by lia.
rewrite TP, unsigned_lit in ERR' by (unfold RATP; lia). unfold RATP in ERR'. replace (316496 + -164) with 316332 in ERR' by reflexivity.
replace (ret_pc (Z_to_bv 64 196828)) with (Z_to_bv 64 196828) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
apply (rheap_pres_rw_cells _ _ _ _ _ _ HPR) in FR; [| left; cbn; lia].
apply (rheap_pres_rw_cells _ _ _ _ _ _ HPR) in OS; [| left; cbn; lia].
eapply K; try eassumption.
cbn [lb_remove_opt].
apply (cmod_weaken [(bv_unsigned sp - 16, bv_unsigned sp); (A, A + 408)] _ (lb_remove p LB) _ (bv_unsigned sp + -16) (bv_unsigned sp));
[apply cmod_of_rheap_pres; exact HPR | lia | intros bq Hbq; exact Hbq | intros xq Hxq; exact Hxq].
- subst X. unfold implM. iprefix.
zstep. zstep. if_cases CN; zify_cond CN; [| exfalso; apply CN; reflexivity].
apply evt_done. cbn [mfree_opt]. apply implM_retb.
eapply K; try eassumption; try reflexivity. apply cmod_refl.
Qed.

#[using="HF"] Lemma free_site3 : forall {R} (k : unit -> @X1qx.M PState R) (Q : R -> PState -> machine_state -> Prop)
(s : PState) (LB : list block) (o : option bptr) (X A lo B : Z) (errv : word) (hdr : list byte)
(sp gp tp : word) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w11 w12 w13 w14 w15 w16 w17 sv rv : word)
(x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem),
RHEAP s LB m -> match o with Some p => exists n, In (p, X, n) LB | None => X = 0 end ->
rauxv_ok m B -> bv_unsigned sp <= B -> bv_unsigned sp <= A -> A + 408 <= B ->
stk rsegs m lo (bv_unsigned sp + -16) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 16 - RFREE_STACK ->
rw_cells rsegs m 316332 [C4 errv] -> mem_inv rsegs m -> tp = Z_to_bv 64 RATP ->
rw_cells rsegs m (bv_unsigned sp + -16) [C8 sv; C8 rv] ->
rw_cells rsegs m A [C8 w0; C8 w1; C8 w2; C8 w3; C8 w4; C8 (Z_to_bv 64 X); C8 w6; C8 w7; C8 w8; C8 w9; CB 284 hdr; C4 w11; C4 w12; C4 w13; C8 w14; C8 w15; C8 w16; C8 w17] ->
(forall (m' : mem) (s' : PState) (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
RHEAP s' (lb_remove_opt o LB) m' -> rauxv_ok m' B -> stk rsegs m' lo (bv_unsigned sp + -16) ->
rw_cells rsegs m' 316332 [C4 errv] -> mem_inv rsegs m' ->
cmod [(bv_unsigned sp - 16, bv_unsigned sp); (A, A + 408)] (lb_remove_opt o LB) (bv_unsigned sp) m m' ->
ps_fa s' = ps_fa s -> ps_so s' = ps_so s ->
rw_cells rsegs m' (bv_unsigned sp + -16) [C8 sv; C8 rv] ->
rw_cells rsegs m' A [C8 w0; C8 w1; C8 w2; C8 w3; C8 w4; C8 (Z_to_bv 64 X); C8 w6; C8 w7; C8 w8; C8 w9; CB 284 hdr; C4 w11; C4 w12; C4 w13; C8 w14; C8 w15; C8 w16; C8 w17] ->
implM rsegs (k tt) s' Q
(MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp y5 y6 y7 (Z_to_bv 64 A) x9 y10 y11 y12 y13 y14 y15 y16 y17
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 y28 y29 y30 y31)
F (Z_to_bv 64 196840) fc None m' (seg_rom rsegs))) ->
implM rsegs (X1qx.mbind (mfree_opt raw_free o) k) s Q
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp x5 x6 x7 (Z_to_bv 64 A) x9 x10 x11 x12 x13 x14 x15 x16 x17
x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
F (Z_to_bv 64 196828) fc None m (seg_rom rsegs)).
Proof.
intros until m. intros HP HIN AUX SPB SPA AB ST CEIL LO ERR MI TP FR OS K.
pose proof CEIL as CEIL'. unfold alloc_ceiling in CEIL'. unfold RFREE_STACK in LO.
pose proof (rw_cells_bound _ _ _ _ OS) as GB. cbn [cells_size csize Nat.add] in GB.
pose proof AUX as AUX0. first [ sf_destruct 16%nat AUX0 as av x3_ x4_ x5_ x16_ x6_ x11_ x12_ x23_ rnd _ _ _ AC1 AC2 _ | sf_fb; destruct AUX0 as (av & x3_ & x4_ & x5_ & x16_ & x6_ & x11_ & x12_ & x23_ & rnd & _ & _ & _ & AC1 & AC2 & _) ].
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (A, A + 408)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
destruct o as [p|].
- destruct HIN as [n HIN]. pose proof (RHEAP_block_range_proof _ _ _ _ HP HIN) as BR. cbn [blk_addr blk_size fst snd] in BR.
first [ sf_destruct 5%nat BR as BR1 BR2 BR3 BR4 BR5 | sf_fb; destruct BR as (BR1 & BR2 & BR3 & BR4 & BR5) ].
unfold implM. iprefix.
zstep. zstep. if_cases CN; zify_cond CN; rewrite ?unsigned_lit, ?land_ones64, ?Z.mod_small in CN by lia; [exfalso; unfold alloc_ceiling in *; lia|].
zstep. apply evt_done. cbn [mfree_opt]. eapply implM_bind.
{ unfold rfree_stmt, rfree_stmt_at in HF.
eapply HF with (s := s) (LB := LB) (p := p) (A := X) (n := n) (lo := lo) (B := B) (errv := errv).
- eapply RHEAP_frame_proof; [exact HP| exact MU| exact WM|].
apply Forall_cons; [left; cbn; lia|]. apply Forall_cons; [left; cbn; lia|]. apply Forall_nil.
- exact HIN.
- eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|].
apply Forall_cons; [cbn; unfold RAUXV_CELL; lia|]. apply Forall_cons; [cbn; unfold RAUXV_CELL; lia|]. apply Forall_nil.
- rewrite unsigned_lit by lia. lia.
- rewrite unsigned_lit by lia. exact ST.
- exact CEIL.
- rewrite unsigned_lit by lia. unfold RFREE_STACK. lia.
- rewrite TP, unsigned_lit by (unfold RATP; lia). unfold RATP. exact ERR.
- exact MI.
- exact TP.
- reflexivity. }
cbv beta. intros [] ps ms PO.
first [ sf_destruct 25%nat PO as t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' -> MI' ST' ERR' AUX' HPR FA SO HP' | sf_fb; destruct PO as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MI' & ST' & ERR' & AUX' & HPR & FA & SO & HP') ].
rewrite unsigned_lit in ST', HPR by lia.
rewrite TP, unsigned_lit in ERR' by (unfold RATP; lia). unfold RATP in ERR'. replace (316496 + -164) with 316332 in ERR' by reflexivity.
replace (ret_pc (Z_to_bv 64 196840)) with (Z_to_bv 64 196840) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
apply (rheap_pres_rw_cells _ _ _ _ _ _ HPR) in FR; [| left; cbn; lia].
apply (rheap_pres_rw_cells _ _ _ _ _ _ HPR) in OS; [| left; cbn; lia].
eapply K; try eassumption.
cbn [lb_remove_opt].
apply (cmod_weaken [(bv_unsigned sp - 16, bv_unsigned sp); (A, A + 408)] _ (lb_remove p LB) _ (bv_unsigned sp + -16) (bv_unsigned sp));
[apply cmod_of_rheap_pres; exact HPR | lia | intros bq Hbq; exact Hbq | intros xq Hxq; exact Hxq].
- subst X. unfold implM. iprefix.
zstep. zstep. if_cases CN; zify_cond CN; [| exfalso; apply CN; reflexivity].
apply evt_done. cbn [mfree_opt]. apply implM_retb.
eapply K; try eassumption; try reflexivity. apply cmod_refl.
Qed.

#[using="HF"] Lemma ogg_stream_clear_spec :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(s : PState) (LB : list block) (os : stream_st bptr) (A Bd L Gv lo B : Z) (hdr : list byte) (errv : word),
RHEAP s LB m -> stream_blocks LB os Bd L Gv -> length hdr = 284%nat ->
rauxv_ok m B -> bv_unsigned sp <= B -> bv_unsigned sp <= A -> A + 408 <= B ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 16 - RFREE_STACK ->
rw_cells rsegs m (errno_addr tp) [C4 errv] ->
mem_inv rsegs m ->
tp = Z_to_bv 64 RATP ->
a0 = Z_to_bv 64 A -> rw_cells rsegs m A (stream_cells Bd L Gv hdr os) ->
implM rsegs (ogg_stream_clear raw_free os) s
(stream_clear_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s (stream_clear_LB LB os) A lo B errv m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_ogg_stream_clear) fc None m (seg_rom rsegs)).
Proof.
intros until errv. intros HP SB HL AUX SPB SPA AB ST CEIL LO ERR MI TP -> OS.
unfold A_ogg_stream_clear. pose proof CEIL as CEIL'. unfold alloc_ceiling in CEIL'. unfold RFREE_STACK in LO.
pose proof SB as sfP_; first [ sf_destruct 6%nat sfP_ as SB1 SB2 SB3 D12 D13 D23 | sf_fb; destruct sfP_ as (SB1 & SB2 & SB3 & D12 & D13 & D23) ].
unfold stream_cells, wz in OS.
pose proof (rw_cells_bound _ _ _ _ OS) as GB. cbn [cells_size csize Nat.add] in GB.
rewrite TP, unsigned_lit in ERR by (unfold RATP; lia). unfold RATP in ERR. replace (316496 + -164) with 316332 in ERR by reflexivity.
pose proof AUX as AUX0. first [ sf_destruct 16%nat AUX0 as av x3_ x4_ x5_ x16_ x6_ x11_ x12_ x23_ rnd _ _ _ AC1 AC2 _ | sf_fb; destruct AUX0 as (av & x3_ & x4_ & x5_ & x16_ & x6_ & x11_ & x12_ & x23_ & rnd & _ & _ & _ & AC1 & AC2 & _) ].
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (A, A + 408)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
unfold ogg_stream_clear, stream_clear_LB.
unfold implM. iprefix.
zstep. if_cases CN0; zify_cond CN0; rewrite ?unsigned_lit in CN0 by lia; [exfalso; lia|].
carve_frame 16%nat ST.
zstep. zstep. zstep. zstep.
apply evt_done.

eapply (free_site1 _ _ s LB (os_body_data os) Bd A lo B errv hdr sp gp tp).
all: lazymatch goal with
| |- rw_cells _ _ _ _ => first [exact OS | exact FR | exact ERR]
| |- RHEAP _ _ _ => eapply RHEAP_frame_proof; [exact HP| exact MU| exact WM|];
apply Forall_cons; [left; cbn; lia|]; apply Forall_cons; [left; cbn; lia|]; apply Forall_nil
| |- rauxv_ok _ _ => eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|];
apply Forall_cons; [cbn; unfold RAUXV_CELL; lia|]; apply Forall_cons; [cbn; unfold RAUXV_CELL; lia|]; apply Forall_nil
| |- stk _ _ _ _ => exact ST
| |- mem_inv _ _ => exact MI
| |- _ = Z_to_bv 64 RATP => exact TP
| |- match _ with _ => _ end => exact SB1
| |- forall m', _ => idtac
| |- word => exact (Z_to_bv 64 0)
| |- _ => try (unfold RFREE_STACK; lia)
end.
clear HP AUX ST ERR MI FR OS. rename MU into MU0. rename WM into WM0. intros m1' s1' y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 HP AUX ST ERR MI CM1 FA1 SO1 FR OS.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (A, A + 408)] m1') as MU. pose proof (wmono_refl rsegs m1') as WM.

eapply (free_site2 _ _ s1' _ (os_lacing_vals os) L A lo B errv hdr sp gp tp).
all: lazymatch goal with
| |- rw_cells _ _ _ _ => first [exact OS | exact FR | exact ERR]
| |- RHEAP _ _ _ => eapply RHEAP_frame_proof; [exact HP| exact MU| exact WM|];
apply Forall_cons; [left; cbn; lia|]; apply Forall_cons; [left; cbn; lia|]; apply Forall_nil
| |- rauxv_ok _ _ => eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|];
apply Forall_cons; [cbn; unfold RAUXV_CELL; lia|]; apply Forall_cons; [cbn; unfold RAUXV_CELL; lia|]; apply Forall_nil
| |- stk _ _ _ _ => exact ST
| |- mem_inv _ _ => exact MI
| |- _ = Z_to_bv 64 RATP => exact TP
| |- match _ with _ => _ end => destruct (os_lacing_vals os) as [p2|] eqn:E2; [| exact SB2]; destruct SB2 as [n2 IN2]; exists n2; destruct (os_body_data os) as [p1|]; [apply lb_remove_keep; [exact IN2| cbn; intros EQ; eapply D12; [reflexivity| reflexivity| symmetry; exact EQ]] | exact IN2]
| |- forall m', _ => idtac
| |- word => exact (Z_to_bv 64 0)
| |- _ => try (unfold RFREE_STACK; lia)
end.
clear HP AUX ST ERR MI FR OS MU WM. intros m2' s2' z1 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 HP AUX ST ERR MI CM2 FA2 SO2 FR OS.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (A, A + 408)] m2') as MU. pose proof (wmono_refl rsegs m2') as WM.

eapply (free_site3 _ _ s2' _ (os_granule_vals os) Gv A lo B errv hdr sp gp tp).
all: lazymatch goal with
| |- rw_cells _ _ _ _ => first [exact OS | exact FR | exact ERR]
| |- RHEAP _ _ _ => eapply RHEAP_frame_proof; [exact HP| exact MU| exact WM|];
apply Forall_cons; [left; cbn; lia|]; apply Forall_cons; [left; cbn; lia|]; apply Forall_nil
| |- rauxv_ok _ _ => eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|];
apply Forall_cons; [cbn; unfold RAUXV_CELL; lia|]; apply Forall_cons; [cbn; unfold RAUXV_CELL; lia|]; apply Forall_nil
| |- stk _ _ _ _ => exact ST
| |- mem_inv _ _ => exact MI
| |- _ = Z_to_bv 64 RATP => exact TP
| |- match _ with _ => _ end => destruct (os_granule_vals os) as [p3|] eqn:E3; [| exact SB3]; destruct SB3 as [n3 IN3]; exists n3;
destruct (os_lacing_vals os) as [p2|]; [apply lb_remove_keep; [| cbn; intros EQ; eapply D23; [reflexivity| reflexivity| symmetry; exact EQ]]|];
(destruct (os_body_data os) as [p1|]; [apply lb_remove_keep; [exact IN3| cbn; intros EQ; eapply D13; [reflexivity| reflexivity| symmetry; exact EQ]] | exact IN3])
| |- forall m', _ => idtac
| |- word => exact (Z_to_bv 64 0)
| |- _ => try (unfold RFREE_STACK; lia)
end.
clear HP AUX ST ERR MI FR OS MU WM. intros m3' s3' u1 u5 u6 u7 u10 u11 u12 u13 u14 u15 u16 u17 u28 u29 u30 u31 HP AUX ST ERR MI CM3 FA3 SO3 FR OS.
pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (A, A + 408)] m3') as MU. pose proof (wmono_refl rsegs m3') as WM.
pose proof (rw_cells_bound _ _ _ _ FR) as FB. cbn [cells_size csize Nat.add] in FB.
apply implM_ret.

destruct (rw_cells_forget _ _ _ _ OS) as [junk408 OSJ]. clear OS. cbn [cells_size csize Nat.add] in OSJ.
zstep. zstep. zstep. zstep.
call (memset_callZ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m3' (bv_unsigned sp + -16) A 0 408 junk408).
all: try (change (Z.to_nat 408) with 408%nat; exact OSJ). all: try exact MI. all: try lia.
rename POST into OSZ. change (Z.to_nat 408) with 408%nat in OSZ. change (0 mod 256) with 0 in OSZ.
lazymatch type of OSZ with rw_cells _ ?mx _ _ => pose proof (stream_cells_zero mx A OSZ) as OS end. clear OSZ.

zstep. zstep. zstep.
lazymatch goal with FRx : rw_cells rsegs _ (bv_unsigned sp + -16) _ |- _ => release_frame FRx ST (bv_unsigned sp) end.
zstep. zstep.
apply evt_done. unfold stream_clear_post. sf_eexists 14%nat.
lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => exists mx end.
split; [reflexivity|]. split; [assumption|]. split; [assumption|].
split. { rewrite TP, unsigned_lit by (unfold RATP; lia). unfold RATP. assumption. }
split. { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|].
apply Forall_cons; [cbn; unfold RAUXV_CELL; lia|]. apply Forall_cons; [cbn; unfold RAUXV_CELL; lia|]. apply Forall_nil. }
split. {
set (W := [(bv_unsigned sp - 16, bv_unsigned sp); (A, A + 408)]) in *.
set (LB1 := lb_remove_opt (os_body_data os) LB) in *. set (LB2 := lb_remove_opt (os_lacing_vals os) LB1) in *.
set (LB3 := lb_remove_opt (os_granule_vals os) LB2) in *.
assert (S12 : forall b, In b LB2 -> In b LB1) by (intros b Hb; eapply lb_remove_opt_sub; exact Hb).
assert (S23 : forall b, In b LB3 -> In b LB2) by (intros b Hb; eapply lb_remove_opt_sub; exact Hb).
assert (S01 : forall b, In b LB1 -> In b LB) by (intros b Hb; eapply lb_remove_opt_sub; exact Hb).
lazymatch type of MU0 with munch _ m ?ma => lazymatch type of MU with munch _ ?mb ?mc =>
apply (cmod_trans W LB3 (bv_unsigned sp) m ma mc);
[ apply (cmod_weaken W W LB LB3 (bv_unsigned sp) (bv_unsigned sp)); [apply cmod_of_munch; [exact MU0| exact WM0]| lia| intros bq Hbq; auto| intros xq Hxq; exact Hxq]
| apply (cmod_trans W LB3 (bv_unsigned sp) ma m1' mc);
[ apply (cmod_weaken W W LB1 LB3 (bv_unsigned sp) (bv_unsigned sp)); [exact CM1| lia| intros bq Hbq; auto| intros xq Hxq; exact Hxq]
| apply (cmod_trans W LB3 (bv_unsigned sp) m1' m2' mc);
[ apply (cmod_weaken W W LB2 LB3 (bv_unsigned sp) (bv_unsigned sp)); [exact CM2| lia| intros bq Hbq; auto| intros xq Hxq; exact Hxq]
| apply (cmod_trans W LB3 (bv_unsigned sp) m2' mb mc); [exact CM3| apply cmod_of_munch; [exact MU| exact WM]] ] ] ]
end end. }
split; [congruence|]. split; [congruence|].
split. { eapply RHEAP_frame_proof; [exact HP| exact MU| exact WM|].
apply Forall_cons; [left; cbn; lia|]. apply Forall_cons; [left; cbn; lia|]. apply Forall_nil. }
split; [reflexivity| exact OS].
Qed.
End STC.

Lemma nodup3 : forall (a b c : bptr) (l : list bptr), List.NoDup (a :: b :: c :: l) ->
a <> b /\ a <> c /\ b <> c /\ ~ In a l /\ ~ In b l /\ ~ In c l.
Proof.
intros a b c l ND. apply List.NoDup_cons_iff in ND. destruct ND as [Na ND]. apply List.NoDup_cons_iff in ND. destruct ND as [Nb ND].
apply List.NoDup_cons_iff in ND. destruct ND as [Nc ND]. cbn in Na, Nb. repeat split; try tauto; intros E; subst; tauto.
Qed.

Lemma nodup_in_tail : forall (x : bptr) l1 l2, List.NoDup (l1 ++ x :: l2) -> ~ In x l2.
Proof.
intros x l1 l2 ND. induction l1 as [|y l1 IH]; cbn in ND.
- apply List.NoDup_cons_iff in ND. tauto.
- apply List.NoDup_cons_iff in ND. apply IH. tauto.
Qed.

Lemma lb_remove_opt_keep : forall o L b, In b L -> match o with Some p => blk_id b <> p | None => True end -> In b (lb_remove_opt o L).
Proof. intros [p|] L b H Hn; [apply lb_remove_keep; assumption| exact H]. Qed.

Lemma in_map_blk_id : forall (b : block) LB, In b LB -> In (blk_id b) (map blk_id LB).
Proof. intros b LB H. apply in_map. exact H. Qed.
