(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Tac Image ZBridge SysStep SFModel Arr.
From OssFuzzTheorems.openssl.bignum.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Malloc Require Import F_malloc_free F_free_C.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgMallocU Require Import RMallocRep RMallocTree RMallocKit_B RMallocKit_B3 RF_get_meta RF_mm_syscalls.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import STree Malloc MallocCtrl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_nia__].
Local Ltac OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib.ZBridge.flia ::= first [ assumption | OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib.ZBridge.slim; lia | lia ].
Local Ltac OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib.ZBridge.mlia ::= Z.div_mod_to_equations; lia.
Local Ltac OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib.Step.slia ::= first [ exact I | lia | split; [lia|exact I] ].
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Definition rffin_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (W : list (Z * Z)) (m : word -> option byte) (st : mstate) (errv : word) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bgusegs)
    /\ munch W m m' /\ wmono bgusegs m m' /\ mem_inv bgusegs m'
    /\ stk bgusegs m' lo (bv_unsigned sp)
    /\ rw_cells bgusegs m' (errno_addr tp) [C4 errv]
    /\ rmrep st m'.

Lemma rfree_fin0 : forall (sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 ra bw q0 q1 : word) F fc
    (m : word -> option byte) (junk : list byte) (lo : Z) (st : mstate) (errv : word),
  tp = Z_to_bv 64 RATP ->
  rmrep st m -> mem_inv bgusegs m ->
  rw_cells bgusegs m (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells bgusegs m (errno_addr tp) [C4 errv] ->
  stk bgusegs m lo (bv_unsigned sp + -48) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 ->
  evt bgusegs (rffin_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m st errv)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 q0 q1 bw (wz 0) a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x2b11a0) fc None m (seg_rom bgusegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until errv. intros TP MR MI FR ERR ST LO LOLE.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl bgusegs m) as WM.
  pose proof MR as (WF & CX & GL & AR & GR & SH). destruct GL as (LK & NL & _).
  unfold RMLOCK, RNEED_LOCKS, RATP, OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec.Malloc.MCEIL in *; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *. subst tp.
  rewrite (unsigned_lit 3346328) in ERR by lia. change (3346328 + -164) with 3346164 in ERR.

  st1. st1. st1. st1.

  st1.
  eapply evt_cut.
  { eapply runlock_spec; rewrite unsigned_lit by lia; [reflexivity| exact LK]. }
  intros ms' ->.
  replace (ret_pc (Z_to_bv 64 0x2b11b4)) with (Z_to_bv 64 0x2b11b4) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).

  st1. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. }
  st1. st1. st1. st1. st1. st1. st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MR2 : rmrep st mX)
      by (eapply rmrep_transport_high; [exact MR | exact MU | exact WM | intros l h [E|[]]; inversion E; subst; unfold OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec.Malloc.MCEIL; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; lia]) end.
  release_frame FR ST (bv_unsigned sp).
  apply evt_done. unfold rffin_post. do 16 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [| exact MR2].
  rewrite (unsigned_lit 3346328) by lia. change (3346328 + -164) with 3346164. exact ERR.
Qed.

Definition rfmun_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (junk : list byte) (m : word -> option byte) (st : mstate) (errv bw lw : word) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR (Z_to_bv 64 0x2b11d0) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 bw lw bw lw a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 (errno_addr tp)) (sx32 errv) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 rmunmap_entry) fc None m' (seg_rom bgusegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m' /\ wmono bgusegs m m' /\ mem_inv bgusegs m'
    /\ stk bgusegs m' lo (bv_unsigned sp + -48)
    /\ rw_cells bgusegs m' (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells bgusegs m' (errno_addr tp) [C4 errv]
    /\ rmrep st m'.

Lemma rfree_tomunmap : forall (sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 ra bw q0 q1 : word) F fc
    (m : word -> option byte) (junk : list byte) (lo len : Z) (st : mstate) (errv : word),
  tp = Z_to_bv 64 RATP ->
  rmrep st m -> mem_inv bgusegs m -> 0 < len < 2^64 ->
  rw_cells bgusegs m (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells bgusegs m (errno_addr tp) [C4 errv] ->
  stk bgusegs m lo (bv_unsigned sp + -48) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 ->
  evt bgusegs (rfmun_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo junk m st errv bw (wz len))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 q0 q1 bw (wz len) a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x2b11a0) fc None m (seg_rom bgusegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until errv. intros TP MR MI HL FR ERR ST LO LOLE.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl bgusegs m) as WM.
  pose proof MR as (WF & CX & GL & AR & GR & SH). destruct GL as (LK & NL & _).
  unfold RMLOCK, RNEED_LOCKS, RATP, OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec.Malloc.MCEIL in *; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *. subst tp.
  rewrite (unsigned_lit 3346328) in ERR by lia. change (3346328 + -164) with 3346164 in ERR.

  st1. st1. st1. st1.

  st1.
  eapply evt_cut.
  { eapply runlock_spec; rewrite unsigned_lit by lia; [reflexivity| exact LK]. }
  intros ms' ->.
  replace (ret_pc (Z_to_bv 64 0x2b11b4)) with (Z_to_bv 64 0x2b11b4) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).

  st1. if_cases K; zify_cond K. { exfalso. rewrite wz_unsigned in K by lia. lia. }

  st1. st1. st1. st1.
  replace (ret_pc (Z_to_bv 64 0x2b11bc)) with (Z_to_bv 64 0x2b11bc) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).

  st1. st1. st1. st1. st1.
  lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ ?mX _) =>
    assert (MR2 : rmrep st mX)
      by (eapply rmrep_transport_high; [exact MR | exact MU | exact WM | intros l h [E|[]]; inversion E; subst; unfold OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec.Malloc.MCEIL; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; lia]) end.
  apply evt_done. unfold rfmun_post. do 14 eexists. split; [rewrite (unsigned_lit 3346328) by lia; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|].
  split; [rewrite (unsigned_lit 3346328) by lia; change (3346328 + -164) with 3346164; exact ERR| exact MR2].
Qed.

Lemma rerrno_avoids_repfoot : forall st m a, rmrep st m -> 3346164 <= a < 3346168 -> ~ rrepfoot st a.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros st m a MR Ha. pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG).
  intros [C|[C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]]].
  - unfold RCTX in C. lia.
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
  - unfold RVMLOCK in C. lia.
Qed.

Lemma rmrep_transport_frame_errno : forall st m m' (sp : Z),
  rmrep st m -> munch [(sp - 48, sp); (3346164, 3346168)]%Z m m' -> wmono bgusegs m m' -> alloc_ceiling <= sp - 48 -> rmrep st m'.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros st m m' sp MR MU WM HS. eapply rmrep_transport_unowned; [exact MR | exact MU | exact WM |].
  apply ivs_avoid_cons; [| apply ivs_avoid_cons; [| apply ivs_avoid_nil]].
  - intros a Ha. pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG). unfold OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec.Malloc.MCEIL in HS; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *.
    intros [C|[C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]]].
    + unfold RCTX in C. lia.
    + unfold RMLOCK in C. lia.
    + unfold RNEED_LOCKS in C. lia.
    + unfold RPAGE_SIZE in C. lia.
    + destruct C as (ak & ar & Hak & Hin).
      destruct (rarea_conc st ak ar WF Hak) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC). unfold OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec.Malloc.MCEIL in RBC; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *. lia.
    + destruct C as (b & gh & Hb & Hin).
      destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & SbA & RB0 & RBC). unfold OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec.Malloc.MCEIL in RBC; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *. lia.
    + destruct C as (rid & r & v & Hr & Hk & Hin & HC).
      destruct (WR _ _ Hr) as (_ & _ & _ & RBC & _). unfold OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec.Malloc.MCEIL in RBC; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *. lia.
    + unfold RGOT_SSP in C. lia.
    + unfold RSSP_GUARD in C. lia.
    + unfold RVMLOCK in C. lia.
  - intros a Ha. eapply rerrno_avoids_repfoot; [exact MR | exact Ha].
Qed.

Lemma rfree_fin1 : forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 ra ew bw lw e' : word) F fc
    (m : word -> option byte) (junk : list byte) (lo : Z) (st : mstate) (errv : word),
  tp = Z_to_bv 64 RATP ->
  rmrep st m -> mem_inv bgusegs m ->
  rw_cells bgusegs m (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  le4 ew = le4 errv ->
  rw_cells bgusegs m (errno_addr tp) [C4 e'] ->
  stk bgusegs m lo (bv_unsigned sp + -48) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 ->
  evt bgusegs (rffin_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo [(bv_unsigned sp - 48, bv_unsigned sp); (3346164, 3346168)]%Z m st errv)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 bw lw a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (errno_addr tp)) ew s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x2b11d0) fc None m (seg_rom bgusegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until errv. intros TP MR MI FR EW ERR ST LO LOLE.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (3346164, 3346168)]%Z m) as MU.
  pose proof (wmono_refl bgusegs m) as WM.
  unfold RATP, OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec.Malloc.MCEIL in *; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *. subst tp.
  rewrite (unsigned_lit 3346328) in ERR by lia. change (3346328 + -164) with 3346164 in ERR.
  rewrite (unsigned_lit 3346328) by lia. change (3346328 + -164) with 3346164.

  st1.

  st1. st1. st1. st1. st1. st1. st1. st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MR2 : rmrep st mX) by (eapply (rmrep_transport_frame_errno st m mX (bv_unsigned sp)); [exact MR | exact MU | exact WM | unfold OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec.Malloc.MCEIL; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; lia]) end.
  release_frame FR ST (bv_unsigned sp).
  apply evt_done. unfold rffin_post. do 16 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [| exact MR2].
  rewrite (unsigned_lit 3346328) by lia. change (3346328 + -164) with 3346164.
  eapply rw_cells_congr; [| | | exact ERR]; [cbn [cells_bytes cbytes app]; rewrite EW; reflexivity| reflexivity| cbn; tauto].
Qed.
End WithCeiling0.
