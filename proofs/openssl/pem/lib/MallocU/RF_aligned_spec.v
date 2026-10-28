(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep SFModel Arr ITree Nodes Decode.
From OssFuzzTheorems.openssl.pem.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import F_malloc_free MallocBlocks MallocHINV MallocFacts_B Malloc_iface MallocReframe MallocFacts_R.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog MI_Inv MI_Ext MI_Geom MI_WFree.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import F_free_K F_free F_free_spec.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require MallocKit_B.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMallocTree RMallocKit_A RMalloc_iface RMalloc_ifaceP RMalloc_impl RF_malloc_top RF_realloc_frame RF_realloc_rep RF_realloc_spec RF_aligned_frame RF_aligned_rep.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require MallocFacts_inv.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require MallocFacts_inv3.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_nia__].
Local Ltac OssFuzzTheorems.Proofs.openssl.pem.lib.Lib.ZBridge.flia ::= first [ assumption | OssFuzzTheorems.Proofs.openssl.pem.lib.Lib.ZBridge.slim; lia | lia ].
Local Ltac OssFuzzTheorems.Proofs.openssl.pem.lib.Lib.ZBridge.mlia ::= Z.div_mod_to_equations; lia.
Local Ltac OssFuzzTheorems.Proofs.openssl.pem.lib.Lib.Step.slia ::= first [ exact I | lia | split; [lia|exact I] ].
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition RALIGNED_SYM : Z := 0x2b242c.
Definition RALIGNED_MID : Z := 0x2b24cc.      (* [comment removed for export] *)
Definition RMEMALIGN_SYM : Z := 0x2b23c8.
Definition RMEMALIGN_MID : Z := 0x2b23f4.     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition raligned_pre_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (LB : list block) (lo len : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' j8,
    ms' = MS (mkR (Z_to_bv 64 RALIGNED_MID) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 64) (Z_to_bv 64 len) (Z_to_bv 64 (len + 48))
                  a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 rmalloc_entry) fc None m' (seg_rom usegs)
    /\ rw_cells usegs m' (bv_unsigned sp + -32) (ra_frame j8 ra s0 s1)
    /\ stk usegs m' lo (bv_unsigned sp + -32)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ RHEAP s LB m'.

Definition raligned_prefix_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LB : list block) (len lo : Z),
  RHEAP s LB m ->
  stk usegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 32 -> mem_inv usegs m ->
  rw_cells usegs m RMALLOC_REPLACED [C4 (Z_to_bv 64 0)] ->
  a0 = Z_to_bv 64 64 -> a1 = Z_to_bv 64 len -> 0 <= len < 2^32 ->
  evt usegs (raligned_pre_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB lo len m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 RALIGNED_SYM) fc None m (seg_rom usegs)).

Theorem raligned_prefix_spec : raligned_prefix_stmt.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB len lo
         HP ST LO SLO MI REPL A0 A1 N.
  eapply evt_mono.
  { unfold RALIGNED_SYM. eapply (raligned_prologue ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo len);
      [exact A0| exact A1| exact N| exact REPL| exact ST| unfold ceil_window in *; lia| exact SLO| exact MI]. }
  intros ms' (x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m1 & j8 & -> & FR & ST1 & MU & WM & MI1).
  unfold raligned_pre_post. exists x5, x6, x7, x11, x12, x13, x14, x15, x16, x17, x28, x29, x30, x31, m1, j8.
  split; [reflexivity|]. split; [exact FR|]. split; [exact ST1|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI1|].
  eapply (RHEAP_frame_proof s LB m m1 _ HP MU WM). constructor; [| constructor]. left. cbn [fst]. lia.
Qed.

Definition raligned_tail_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (LB : list block) (p : bptr) (A len lo B : Z) (errv : word) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' A' junk,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A') a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' (errno_addr tp) [C4 errv]
    /\ rauxv_ok m' B
    /\ A' mod 64 = 0 /\ A <= A' < A + 64
    /\ rheap_pres ((p, A', len) :: LB) (bv_unsigned sp) m m'
    /\ RHEAP s ((p, A', len) :: LB) m'
    /\ rw_cells usegs m' A' [CB (Z.to_nat len) junk].

Definition raligned_tail_stmt : Prop :=
  forall (x1 ra sp gp tp t0 t1 t2 s0 s1 q0 q1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LB : list block) (p : bptr) (A len lo B : Z) (errv : word) (j8 : list byte),
  RHEAP s ((p, A, len + 48) :: LB) m -> rfresh_blk s p A (len + 48) ->
  0 <= len -> len + 48 < MMAP_THRESHOLD ->
  rauxv_ok m B -> bv_unsigned sp <= B ->
  rw_cells usegs m (bv_unsigned sp + -32) (ra_frame j8 ra s0 s1) ->
  stk usegs m lo (bv_unsigned sp + -32) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 32 ->
  rw_cells usegs m (errno_addr tp) [C4 errv] ->
  mem_inv usegs m ->
  tp = Z_to_bv 64 RATP ->
  q0 = Z_to_bv 64 64 -> q1 = Z_to_bv 64 len -> a0 = Z_to_bv 64 A ->
  evt usegs (raligned_tail_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB p A len lo B errv m)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 q0 q1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 RALIGNED_MID) fc None m (seg_rom usegs)).

Lemma lb_remove_notin : forall (p : bptr) LB, ~ In p (map blk_id LB) -> lb_remove p LB = LB.
Proof.
  intros p LB. unfold lb_remove. induction LB as [|b LB IH]; intros NI; [reflexivity|].
  rewrite filter_cons. destruct (decide (negb (bptr_eqb (blk_id b) p))) as [D|D].
  - f_equal. apply IH. intros H. apply NI. right. exact H.
  - exfalso. apply NI. left. destruct (bptr_eqb (blk_id b) p) eqn:EB; [| exfalso; apply D; exact I].
    unfold bptr_eqb in EB. apply andb_true_iff in EB. destruct EB as [E1 E2].
    apply MallocKit_B.aptr_eqb_eq in E1. apply Z.eqb_eq in E2. destruct (blk_id b) as [c1 o1], p as [c2 o2]. cbn in *. subst. reflexivity.
Qed.

Lemma lb_remove_head : forall (p : bptr) A n LB, ~ In p (map blk_id LB) -> lb_remove p ((p, A, n) :: LB) = LB.
Proof.
  intros p A n LB NI. rewrite <- (lb_remove_notin p LB NI) at 2. unfold lb_remove.
  assert (E : bptr_eqb p p = true) by (unfold bptr_eqb; rewrite aptr_eqb_refl, Z.eqb_refl; reflexivity).
  rewrite filter_cons. change (blk_id (p, A, n)) with p.
  destruct (decide (negb (bptr_eqb p p))) as [D|D]; [| reflexivity].
  exfalso. rewrite E in D. exact D.
Qed.

Theorem raligned_tail_spec : raligned_tail_stmt.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros x1 ra sp gp tp t0 t1 t2 s0 s1 q0 q1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB p A len lo B errv j8
         HP FRESH LEN0 LTH AV HB FR ST LO SLO ERR MI TP HQ0 HQ1 HA0.
  set (n0 := len + 48) in *.
  pose proof (RHEAP_blocks_nodup_proof _ _ _ HP) as NDID.
  destruct HP as (st & LB0 & PERM & Hst & MRm & [BL AR]).
  assert (Hin : In (p, A, n0) ((p, A, n0) :: LB)) by (left; reflexivity).
  assert (Hin0 : In (p, A, n0) LB0) by (eapply Permutation_in; [apply Permutation_sym; exact PERM| exact Hin]).
  pose proof (MallocFacts_inv3.areach_cinv_proof _ _ AR) as C.
  pose proof (proj1 (List.Forall_forall _ _) (ci_blks _ _ C) (p, A, n0) Hin0) as BK.
  destruct BK as [(g0 & i0 & b0 & _ & _ & _ & _ & _ & (off & O0 & OA & _)) _ _].
  destruct (MallocFacts_inv.areach_blk_facts st LB0 (p, A, n0) off AR Hin0 O0 OA) as (g & bg & i & ai & a & ar & ka & BF & SCNT & NOGRP).
  unfold blk_addr, blk_slot, blk_size in OA, BF. cbn [fst snd] in OA, BF.
  set (c := fst p) in *.
  assert (INI : c_init_done (ctx st) <> 0).
  { destruct (MallocFacts_inv.areach_inv _ _ _ AR) as (L & LS & BL' & (IR & IA & _) & _).
    destruct (MI_Inv.ia_secret _ IA) as [_ [(_ & _ & E0)|(E1 & _)]]; [| unfold ctx; lia].
    exfalso. destruct (bf_area _ _ _ _ _ _ _ _ _ _ _ BF) as (Ha & _). rewrite E0 in Ha. rewrite lookup_empty in Ha. discriminate. }
  destruct (rrb_geo st LB0 c off n0 g bg i ai a ar ka C BF) as (r & Hr & Kr & B0 & S16 & SI0 & Hi & OFF & N0 & SPAN & FIT & O16 & RES0 & Ec & PM & Q1 & Q2).
  set (stride := get_stride (get_meta_rec st g)) in *.
  assert (ESS : sstart (MR st g) i = snd bg + 16 + stride * i).
  { unfold sstart, gbase, MR. rewrite (bf_mem _ _ _ _ _ _ _ _ _ _ _ BF). cbn [default from_option id snd]. unfold UNIT. reflexivity. }
  assert (Hrc : s_regions st !! fst c = Some r) by (rewrite Ec; exact Hr).
  assert (EA : A = r_base r + (snd bg + 16 + stride * i + 16 * off)).
  { rewrite OA, (conc_region' st c r Hrc), Ec. cbn [snd]. unfold UNIT. lia. }
  (* [comment removed for export] *)
  destruct FRESH as (gf & idf & SLf & CLSf & OFFf).
  rewrite <- Hst in SLf, CLSf, OFFf. rewrite MallocCtrl.s_slots_strip in SLf. rewrite MallocCtrl.get_meta_rec_strip in CLSf.
  fold c in SLf, OFFf. change (conc (strip st) c) with (conc st c) in OFFf.
  rewrite (bf_slot _ _ _ _ _ _ _ _ _ _ _ BF) in SLf. inversion SLf; subst gf idf. clear SLf.
  specialize (CLSf LTH). specialize (SCNT CLSf). unfold MR in SCNT. fold stride in SCNT.
  assert (ST20 : stride < 2^20).
  { pose proof (bf_i _ _ _ _ _ _ _ _ _ _ _ BF) as [I0 I1]. unfold MR in I1. clear - SCNT S16 I0 I1. nia. }
  assert (OFF255 : off <= 255) by (rewrite OA in OFFf; unfold UNIT in OFFf; clear - OFFf; lia).
  pose proof MRm as (WF & _). pose proof WF as (_ & WR & _).
  destruct (WR _ _ Hr) as (RB0 & RBAL & _ & RBC & _).
  pose proof (rregion_addr_facts st m _ r MRm Hr) as (_ & _ & _ & RIMG).
  pose proof (round_up_pg_ge (r_len r)) as RUP.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (NIDp : ~ In p (map blk_id LB)) by (cbn [map blk_id fst] in NDID; inversion NDID; assumption).
  pose proof (lb_remove_lbrm ((p, A, n0) :: LB) p A n0 (NoDup_map_perm blk_slot LB0 _ PERM (ci_nodup _ _ C)) Hin) as ELB.
  rewrite (lb_remove_head p A n0 LB NIDp) in ELB.
  assert (RIMG' : r_base r + round_up_pg (r_len r) <= 0x10000 \/ 0x353000 <= r_base r) by (apply RIMG; clear - SPAN B0 SI0 S16; lia).
  set (cz := snd bg + 16 + stride * i) in *. set (eo := cz + stride - 4).
  assert (ETP : errno_addr tp = 3344580) by (unfold errno_addr; rewrite TP; unfold RATP; rewrite unsigned_lit by lia; reflexivity).
  (* [comment removed for export] *)
  assert (CLOSE : forall (off' : Z) (st' : mstate) (m1 : mem) (A' : Z),
    A' = r_base r + (cz + 16 * off') -> off <= off' <= off + 3 -> 16 * off' + len + 4 <= stride ->
    ctrl_eq st st' -> reframe_ok st c off n0 off' len st' ->
    rmrep st' m1 -> mem_inv usegs m1 ->
    rpres_except (fun x => r_base r + cz - 3 <= x < r_base r + eo /\ ~ (A' <= x < A' + len)) m m1 ->
    rw_cells usegs m1 (errno_addr tp) [C4 errv] /\ rauxv_ok m1 B
    /\ rheap_pres ((p, A', len) :: LB) (bv_unsigned sp) m m1
    /\ RHEAP s ((p, A', len) :: LB) m1
    /\ exists junk, rw_cells usegs m1 A' [CB (Z.to_nat len) junk]).
  { intros off' st' m1 A' EA' OFR FIT' CE RFOK MR2 MI2 PE.
    assert (NIMG : forall x, r_base r + cz - 3 <= x < r_base r + eo -> r_base r <= x < r_base r + round_up_pg (r_len r)) by (intros x Hx; unfold eo, cz in *; clear - Hx SPAN B0 SI0; lia).
    split. { eapply rpres_except_rw_cells; [exact PE| exact ERR|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ].
             rewrite ETP. intros x Hx [X _]. specialize (NIMG x X). clear - NIMG RIMG' Hx. lia. }
    split. { eapply rauxv_ok_pres; [exact AV| exact PE| |].
             - intros x Hx [X _]. specialize (NIMG x X). unfold ceil_window in *. clear - NIMG RBC Hx HB LO SLO CEIL_RANGE__. lia.
             - unfold RAUXV_CELL. intros x Hx [X _]. specialize (NIMG x X). clear - NIMG RIMG' Hx. lia. }
    split.
    { eapply (rheap_pres_reframe st LB0 (p, A, n0) g i r m m1 lo (bv_unsigned sp) (bv_unsigned sp) (r_base r + cz - 3) A' (r_base r + eo) len);
        try eassumption.
      - exact (bf_slot _ _ _ _ _ _ _ _ _ _ _ BF).
      - clear - SLO. lia.
      - clear. lia.
      - rewrite ESS. fold cz. clear. lia.
      - unfold cz. clear - B0 SI0. lia.
      - rewrite sstart_succ, ESS. unfold MR. fold stride. fold cz. unfold eo. clear. lia.
      - unfold eo, cz. clear - SPAN. lia.
      - rewrite EA'. unfold eo. clear - FIT'. lia.
      - eapply rpres_except_mono; [exact PE|]. intros x Hx. right. exact Hx.
      - intros b [<-|Hb]; [left; reflexivity| right]. rewrite ELB in Hb. eapply In_lbrm_perm; [apply Permutation_sym; exact PERM| exact Hb]. }
    split.
    { exists st', ((p, A', len) :: lbrm LB0 (p, A, n0)).
      split. { rewrite ELB. apply perm_skip. apply lbrm_perm. exact PERM. }
      split. { rewrite (strip_ctrl_eq _ _ CE). exact Hst. }
      split; [exact MR2|]. split.
      + unfold brk_link in *. unfold ctx in *. rewrite (ce_ctx _ _ CE).
        destruct (c_brk (s_ctx st)) as [| |brid boff]; [exact I| exact I|]. rewrite BL. unfold conc, get_region. rewrite (ce_regions _ _ CE). reflexivity.
      + pose proof (areach_reframe st LB0 (p, A, n0) off' len st' AR Hin0) as ARF. cbn [blk_id blk_slot blk_addr blk_size fst snd] in ARF. fold c in ARF.
        replace (conc st c + UNIT * off') with A' in ARF by (rewrite EA', (conc_region' st c r Hrc), Ec; cbn [snd]; unfold UNIT; fold cz; clear; lia).
        apply ARF.
        replace ((A - conc st c) / UNIT) with off by (rewrite OA; replace (conc st c + UNIT * off - conc st c) with (off * UNIT) by lia; rewrite Z.div_mul by (unfold UNIT; lia); reflexivity).
        exact RFOK. }
    pose proof (ruser_chunk st' m1 (aadd c (UNIT * off')) r len MR2 ltac:(rewrite (ce_regions _ _ CE); exact Hrc) Kr
                  ltac:(rewrite Ec; cbn [aadd snd]; unfold UNIT; fold cz; unfold cz; clear - B0 SI0 O0 OFR; lia)
                  ltac:(rewrite Ec; cbn [aadd snd]; unfold UNIT; fold cz; unfold cz in *; clear - SPAN FIT'; lia) LEN0) as (junk & UC).
    assert (ECONC : conc st' (aadd c (UNIT * off')) = A').
    { unfold conc, get_region. rewrite (ce_regions _ _ CE). cbn [aadd fst snd]. rewrite Hrc, EA', Ec. cbn [snd]. unfold UNIT. fold cz. clear. lia. }
    rewrite ECONC in UC. exists junk. exact UC. }
  eapply evt_mono.
  { unfold RALIGNED_MID.
    eapply (raligned_tail_rep st LB0 c off n0 g bg i ai a ar ka C BF INI
              x1 ra sp gp tp t0 t1 t2 s0 s1 q0 q1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo r len j8);
      [exact MRm| exact MI| exact Hr| exact HQ0| exact HQ1| rewrite HA0, EA; reflexivity| reflexivity| exact LEN0| exact CLSf| exact SCNT| exact OFF255| | exact FR| exact ST| exact LO| exact SLO].
    intros b' gh Hgh Hf. specialize (NOGRP b' gh Hgh Hf). rewrite sstart_succ, ESS in NOGRP. unfold MR in NOGRP. fold stride in NOGRP. exact NOGRP. }
  fold stride. cbv zeta. fold cz. rewrite <- EA.
  intros ms' [(PM0 & RET)|(PM1 & RET)].
  - (* [comment removed for export] *)
    destruct RET as (x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m1 & -> & MR2 & TK2 & MI2 & ST2 & PE).
    fold eo in PE.
    destruct (CLOSE off (rf_setsize_st st c g bg i off len) m1 A ltac:(rewrite EA; unfold cz; clear; lia) ltac:(clear; lia) ltac:(unfold n0 in FIT; clear - FIT LEN0; lia)
                (rf_full_ctrl _ _ _ _ _)
                (reframe_ok_setsize st c g bg i off n0 len (bf_slot _ _ _ _ _ _ _ _ _ _ _ BF) (ex_intro _ ai (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF)) LEN0
                   ltac:(unfold MR; fold stride; unfold UNIT, IB, n0 in *; clear - FIT LEN0; lia)
                   ltac:(unfold MR; fold stride; unfold IB; clear - ST20 LEN0; lia))
                MR2 MI2 PE) as (E1 & E2 & E3 & E4 & junk & E5).
    unfold raligned_tail_post. exists x5, x6, x7, x11, x12, x13, x14, x15, x16, x17, x28, x29, x30, x31, m1, A, junk.
    split; [reflexivity|]. split; [exact MI2|]. split; [exact ST2|]. split; [exact E1|]. split; [exact E2|].
    split; [exact PM0|]. split; [clear; lia|]. split; [exact E3|]. split; [exact E4| exact E5].
  - (* [comment removed for export] *)
    destruct RET as (x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m1 & -> & MR2 & TK2 & MI2 & ST2 & PE).
    fold eo in PE.
    set (adj := 64 - A mod 64) in *.
    assert (ADJ : (adj = 16 \/ adj = 32 \/ adj = 48) /\ adj = 16 * (adj / 16)).
    { assert (P16 : A mod 16 = 0) by (rewrite EA; fold cz; clear - RBAL PM; unfold cz in *; Z.div_mod_to_equations; lia).
      unfold adj. clear - P16 PM1. Z.div_mod_to_equations. lia. }
    destruct ADJ as [ADJ3 ADJE]. set (d := adj / 16) in *.
    assert (DR : 1 <= d <= 3) by (clear - ADJ3 ADJE; lia).
    assert (FIT' : 16 * (off + d) + len + 4 <= stride) by (unfold n0 in FIT; clear - FIT DR; lia).
    assert (SIC : stride * (i + 1) <= stride * (m_last_idx (get_meta_rec st g) + 1)).
    { pose proof (bf_i _ _ _ _ _ _ _ _ _ _ _ BF) as [_ I1]. unfold MR in I1. apply Z.mul_le_mono_nonneg_l; [clear - S16; lia| clear - I1; lia]. }
    assert (QR' : 0 <= (sstart (MR st g) i + UNIT * (off + d) - snd (gbase (MR st g)) - UNIT) / UNIT < 2 ^ 16).
    { rewrite ESS. unfold gbase, MR. rewrite (bf_mem _ _ _ _ _ _ _ _ _ _ _ BF). cbn [default from_option id snd]. unfold UNIT.
      replace (snd bg + 16 + stride * i + 16 * (off + d) - snd bg - 16) with ((stride * i / 16 + off + d) * 16).
      2:{ clear - Q1. fold stride in Q1. assert (stride * i = 16 * (stride * i / 16)) by (Z.div_mod_to_equations; lia). lia. }
      rewrite Z.div_mul by (clear; lia).
      assert (X : 16 * (stride * i / 16 + off + d) < 2^20).
      { assert (stride * i = 16 * (stride * i / 16)) by (clear - Q1; fold stride in Q1; Z.div_mod_to_equations; lia).
        clear - H FIT' LEN0 SIC SCNT. lia. }
      clear - X SI0 OFF DR. split; [apply Z.add_nonneg_nonneg; [apply Z.add_nonneg_nonneg; [apply Z.div_pos; lia| lia]| lia]| lia]. }
    destruct (CLOSE (off + d) (rf_move_st st c g bg i (off + d) len) m1 (A + adj)
                ltac:(rewrite EA; unfold cz; clear - ADJE; fold d in ADJE; lia) ltac:(clear - DR; lia) FIT'
                (rf_full_ctrl _ _ _ _ _)
                (reframe_ok_move st c g bg i off n0 (off + d) len (bf_slot _ _ _ _ _ _ _ _ _ _ _ BF) (ex_intro _ ai (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF))
                   ltac:(clear - OFF OFF255 DR; lia) LEN0
                   ltac:(unfold MR; fold stride; unfold UNIT, IB; clear - FIT'; lia)
                   ltac:(unfold MR; fold stride; unfold IB; clear - ST20 LEN0; lia) QR')
                MR2 MI2 PE) as (E1 & E2 & E3 & E4 & junk & E5).
    unfold raligned_tail_post. exists x5, x6, x7, x11, x12, x13, x14, x15, x16, x17, x28, x29, x30, x31, m1, (A + adj), junk.
    split; [reflexivity|]. split; [exact MI2|]. split; [exact ST2|]. split; [exact E1|]. split; [exact E2|].
    split; [unfold adj; clear; Z.div_mod_to_equations; lia|]. split; [clear - ADJ3; lia|]. split; [exact E3|]. split; [exact E4| exact E5].
Qed.

(* [comment removed for export] *)
Definition rmemalign_pre_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 res : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (LB : list block) (lo len : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' j8,
    let sp1 := Z_to_bv 64 (bv_unsigned sp + -16) in
    ms' = MS (mkR (Z_to_bv 64 RALIGNED_MID) (Z_to_bv 64 (bv_unsigned sp1 + -32)) gp tp t0 t1 t2 (Z_to_bv 64 64) (Z_to_bv 64 len) (Z_to_bv 64 (len + 48))
                  a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 rmalloc_entry) fc None m' (seg_rom usegs)
    /\ rw_cells usegs m' (bv_unsigned sp + -16) [C8 s0; C8 ra]
    /\ rw_cells usegs m' (bv_unsigned sp1 + -32) (ra_frame j8 (Z_to_bv 64 RMEMALIGN_MID) res s1)
    /\ stk usegs m' lo (bv_unsigned sp1 + -32)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ RHEAP s LB m'.

Definition rmemalign_prefix_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LB : list block) (len lo : Z),
  RHEAP s LB m ->
  stk usegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 -> mem_inv usegs m ->
  rw_cells usegs m RMALLOC_REPLACED [C4 (Z_to_bv 64 0)] ->
  a1 = Z_to_bv 64 64 -> a2 = Z_to_bv 64 len -> 0 <= len < 2^32 ->
  evt usegs (rmemalign_pre_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 F fc s LB lo len m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 RMEMALIGN_SYM) fc None m (seg_rom usegs)).

Theorem rmemalign_prefix_spec : rmemalign_prefix_stmt.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB len lo
         HP ST LO SLO MI REPL A1 A2 N. subst a1 a2. unfold RMALLOC_REPLACED in REPL.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (ILO : 0x353000 <= lo) by (unfold ceil_window in *; lia).
  unfold RMEMALIGN_SYM.
  (* [comment removed for export] *)
  step. step. if_cases K0; zify_cond K0. 2:{ exfalso. rewrite ?unsigned_lit in K0 by lia. lia. }
  (* [comment removed for export] *)
  step. carve_frame 16%nat ST. step. step. step. step. step. step.
  set (sp1 := Z_to_bv 64 (bv_unsigned sp + -16)) in *.
  assert (SP1 : bv_unsigned sp1 = bv_unsigned sp + -16) by (unfold sp1; apply unsigned_lit; unfold ceil_window in *; lia).
  lazymatch goal with MIc : mem_inv usegs ?mc |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m1 end.
  assert (HP1 : RHEAP s LB m1).
  { eapply (RHEAP_frame_proof s LB m m1 _ HP MU WM). constructor; [| constructor]. left. cbn [fst]. lia. }
  eapply evt_mono.
  { eapply (raligned_prefix_spec _ sp1 gp tp _ _ _ a0 s1 _ _ _ _ _ _ _ _ s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m1 s LB len lo);
      [exact HP1| rewrite SP1; exact ST| exact LO| rewrite SP1; lia| assumption| unfold RMALLOC_REPLACED; assumption| reflexivity| reflexivity| exact N]. }
  intros ms' (x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m2 & j8 & -> & FR2 & ST2 & MU2 & WM2 & MI2 & HP2).
  unfold rmemalign_pre_post. exists x5, x6, x7, x11, x12, x13, x14, x15, x16, x17, x28, x29, x30, x31, m2, j8. cbv zeta. fold sp1.
  split; [reflexivity|].
  split. { eapply rw_cells_transport; [exact FR| exact MU2| exact WM2|]. cbn [cells_size csize Nat.add disjoint_from Z.of_nat Pos.of_succ_nat Pos.succ Pos.add].
           rewrite SP1. split; [right; lia| exact I]. }
  split; [exact FR2|]. split; [exact ST2|].
  split. { intros x Hx. rewrite (MU2 x), (MU x); [reflexivity| |]; cbn [outside] in Hx |- *; rewrite ?SP1; lia. }
  split; [exact (wmono_trans usegs _ _ _ WM WM2)|]. split; [exact MI2| exact HP2].
Qed.

Definition rmemalign_tail_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (LB : list block) (p : bptr) (A len lo B res : Z) (errv : word) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m1 m' A' junk,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(res, res + 8)]%Z m1 m' /\ wmono usegs m1 m'
    /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' res [C8 (Z_to_bv 64 A')]
    /\ rw_cells usegs m' (errno_addr tp) [C4 errv]
    /\ rauxv_ok m' B
    /\ A' mod 64 = 0 /\ A <= A' < A + 64
    /\ rheap_pres ((p, A', len) :: LB) (bv_unsigned sp) m m1
    /\ RHEAP s ((p, A', len) :: LB) m'
    /\ rw_cells usegs m' A' [CB (Z.to_nat len) junk].

Definition rmemalign_tail_stmt : Prop :=
  forall (x1 ra sp gp tp t0 t1 t2 s0 s1 q0 q1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 resw : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LB : list block) (p : bptr) (A len lo B : Z) (errv old : word) (j8 : list byte),
  let sp1 := Z_to_bv 64 (bv_unsigned sp + -16) in
  RHEAP s ((p, A, len + 48) :: LB) m -> rfresh_blk s p A (len + 48) ->
  0 <= len -> len + 48 < MMAP_THRESHOLD ->
  rauxv_ok m B -> bv_unsigned sp <= B ->
  rw_cells usegs m (bv_unsigned sp + -16) [C8 s0; C8 ra] ->
  rw_cells usegs m (bv_unsigned sp1 + -32) (ra_frame j8 (Z_to_bv 64 RMEMALIGN_MID) resw s1) ->
  stk usegs m lo (bv_unsigned sp1 + -32) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 ->
  rw_cells usegs m (bv_unsigned resw) [C8 old] -> bv_unsigned sp <= bv_unsigned resw -> bv_unsigned resw + 8 <= B ->
  rw_cells usegs m (errno_addr tp) [C4 errv] ->
  mem_inv usegs m ->
  tp = Z_to_bv 64 RATP ->
  q0 = Z_to_bv 64 64 -> q1 = Z_to_bv 64 len -> a0 = Z_to_bv 64 A ->
  evt usegs (rmemalign_tail_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB p A len lo B (bv_unsigned resw) errv m)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp1 + -32)) gp tp t0 t1 t2 q0 q1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 RALIGNED_MID) fc None m (seg_rom usegs)).

Theorem rmemalign_tail_spec : rmemalign_tail_stmt.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros x1 ra sp gp tp t0 t1 t2 s0 s1 q0 q1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 resw F fc m s LB p A len lo B errv old j8 sp1
         HP FRESH LEN0 LTH AV HB FRP FRA ST LO SLO RES RLO RHI ERR MI TP HQ0 HQ1 HA0.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (SP1 : bv_unsigned sp1 = bv_unsigned sp + -16) by (unfold sp1; apply unsigned_lit; unfold ceil_window in *; lia).
  eapply evt_cut.
  { eapply (raligned_tail_spec x1 (Z_to_bv 64 RMEMALIGN_MID) sp1 gp tp t0 t1 t2 resw s1 q0 q1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
              F fc m s LB p A len lo B errv j8);
      [exact HP| exact FRESH| exact LEN0| exact LTH| exact AV| rewrite SP1; lia| exact FRA| exact ST| exact LO| rewrite SP1; lia| exact ERR| exact MI| exact TP
      | exact HQ0| exact HQ1| exact HA0]. }
  intros ms1 (x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m1 & A' & junk & -> & MI1 & ST1 & ERR1 & AV1 & AL & AR' & HPR & HP1 & UC).
  rewrite SP1 in ST1, HPR.
  replace (ret_pc (Z_to_bv 64 RMEMALIGN_MID)) with (Z_to_bv 64 RMEMALIGN_MID) by (symmetry; apply ret_pc_even; [unfold RMEMALIGN_MID; lia| reflexivity]).
  (* [comment removed for export] *)
  assert (FRP1 : rw_cells usegs m1 (bv_unsigned sp + -16) [C8 s0; C8 ra]).
  { eapply rheap_pres_rw_cells; [exact HPR| exact FRP|]. left. lia. }
  assert (RES1 : rw_cells usegs m1 (bv_unsigned resw) [C8 old]).
  { eapply rheap_pres_rw_cells; [exact HPR| exact RES|]. left. lia. }
  pose proof (RHEAP_block_range_proof _ _ _ (p, A', len) HP1 ltac:(left; reflexivity)) as (BA0 & _ & _ & BAC & _). cbn [blk_addr blk_size fst snd] in BA0, BAC.
  assert (A'NZ : A' <> 0) by lia.
  assert (A'R : 0 <= A' < 2^64) by (unfold ceil_window in *; lia).
  unfold RMEMALIGN_MID. clear SP1. subst sp1.
  assert (ETP : errno_addr tp = 3344580) by (unfold errno_addr; rewrite TP; unfold RATP; rewrite unsigned_lit by lia; reflexivity).
  rewrite ETP in ERR1.
  pose proof (munch_refl [(bv_unsigned resw, bv_unsigned resw + 8)]%Z m1) as MU. pose proof (wmono_refl usegs m1) as WM.
  (* [comment removed for export] *)
  step. if_cases K0; zify_cond K0. { exfalso. rewrite ?unsigned_lit in K0 by lia. lia. }
  step. step. step.
  (* [comment removed for export] *)
  step. step. step.
  lazymatch goal with FRc : rw_cells usegs ?mc (bv_unsigned sp + -16) [C8 s0; C8 ra], STc : stk usegs ?mc lo (bv_unsigned sp + -16) |- _ =>
    release_frame FRc STc (bv_unsigned sp) end.
  step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m2 end.
  apply evt_done. unfold rmemalign_tail_post.
  do 14 eexists. exists m1, m2, A', junk.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
  split; [rewrite ETP; assumption|].
  split. { eapply rauxv_ok_pres; [exact AV1| eapply (rpres_except_of_munch (fun x => bv_unsigned resw <= x < bv_unsigned resw + 8) _ m1 m2 MU WM)| |].
           - intros x Hx NC. cbn [outside]. split; [exact NC| exact I].
           - intros x Hx X. lia.
           - unfold RAUXV_CELL. intros x Hx X. unfold ceil_window in *. lia. }
  split; [exact AL|]. split; [exact AR'|].
  split. { eapply rheap_pres_weaken; [exact HPR| lia| intros b Hb; exact Hb]. }
  split; [| assumption].
  eapply (RHEAP_frame_proof s _ m1 m2 _ HP1 MU WM). constructor; [| constructor]. left. cbn [fst]. lia.
Qed.
End WithCeiling0.
