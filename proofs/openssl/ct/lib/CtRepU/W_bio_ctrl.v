(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Lib_kit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXU Require Import HxpFacts.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApCells ApRepDefs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtBnU Require Import BnKit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 (zxb ?b) => constr:(C1 b)
  | Z_to_le_bytes 8 ?z => constr:(C8 (Z_to_bv 64 z))
  | Z_to_le_bytes 4 ?z => constr:(C4 (Z_to_bv 64 z))
  end.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].
Local Ltac al8chk A := zstep; let K := fresh "K" in if_cases K; zify_cond K;
  [exfalso; rewrite ?unsigned_lit in K by lia; try (change 7 with (Z.ones 3) in K; rewrite Z.land_ones in K by lia); clear - K A; Z.div_mod_to_equations; lia | clear K].

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition NULL_CTRL : Z := 0x194400.
Definition NULL_CTRL_TAB : Z := 0x594d0.   (* [comment removed for export] *)
Definition BIO_CTRL_PUSH : Z := 6.  Definition BIO_CTRL_POP : Z := 7.  Definition BIO_CTRL_SET_PREFIX : Z := 79.
Definition BIO_CTRL_SET_INDENT : Z := 80.  Definition BIO_CTRL_GET_INDENT : Z := 81.

Definition null_ctrl_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ctusegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m m' /\ wmono ctusegs m m' /\ mem_inv ctusegs m'
    /\ stk ctusegs m' lo (bv_unsigned sp).

(* [comment removed for export] *)
Lemma ro_cells_recast : forall m A cs cs',
  ro_cells ctusegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> ro_cells ctusegs m A cs'.
Proof. intros m A cs cs' [Hwf Hb] Hwf' Eb. split; [exact Hwf'| rewrite Eb; exact Hb]. Qed.

(* [comment removed for export] *)
Lemma null_ctrl_tab : forall m, mem_inv ctusegs m ->
  ro_cells ctusegs m (NULL_CTRL_TAB + 40) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].
Proof.
  intros m MI. eapply (ro_cells_recast m _ [CB 16 (repeat (Z_to_bv 8 0) 16)]).
  - apply (ro_cells_image ctusegs m (NULL_CTRL_TAB + 40) (repeat (Z_to_bv 8 0) 16) MI); [vm_compute; reflexivity| unfold NULL_CTRL_TAB; lia| unfold NULL_CTRL_TAB; cbn; lia].
  - cbn. auto.
  - cbv -[Z_to_bv]. reflexivity.
Qed.

Lemma null_ctrl_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (cmd lo : Z),
  stk ctusegs m lo (bv_unsigned sp) -> mem_inv ctusegs m -> GLOBALS_TOP <= lo -> (lo <= bv_unsigned sp - 16)%Z ->
  a1 = Z_to_bv 64 cmd -> (cmd = BIO_CTRL_PUSH \/ cmd = BIO_CTRL_POP \/ cmd = BIO_CTRL_SET_PREFIX) ->
  evt ctusegs (null_ctrl_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 NULL_CTRL) fc None m (seg_rom ctusegs)).
Proof.
  intros until lo. intros ST MI GLO LO -> Hcmd. unfold GLOBALS_TOP in GLO.
  pose proof (null_ctrl_tab m MI) as TAB. unfold NULL_CTRL_TAB in TAB. change (365776 + 40) with 365816 in TAB.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  unfold NULL_CTRL, BIO_CTRL_PUSH, BIO_CTRL_POP, BIO_CTRL_SET_PREFIX in *.
  carve_frame 16%nat ST.
  destruct Hcmd as [-> | [-> | ->]].
  - do 6 zstep. zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|]. clear K.
    do 5 zstep. do 4 zstep. release_frame FR ST (bv_unsigned sp). zstep. finish.
  - do 6 zstep. zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|]. clear K.
    do 5 zstep. do 4 zstep. release_frame FR ST (bv_unsigned sp). zstep. finish.
  - do 6 zstep. zstep. if_cases K; zify_cond K; [|exfalso; rewrite ?unsigned_lit in K by lia; lia]. clear K.
    zstep. do 3 zstep. release_frame FR ST (bv_unsigned sp). zstep. finish.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition BIO_CTRL : Z := 0x10c4f0.
Definition BIO_CTRL_FRAME : Z := 48.

(* [comment removed for export] *)
Definition ctrl_callee_post (spz : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo CSTK OA ON : Z) (cres : Z) (RC : (word -> option byte) -> Prop) (m1 : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m2,
    ms' = MS (mkR (Z_to_bv 64 0x10c5a4) (Z_to_bv 64 spz) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 cres) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x10c5a4) fc None m2 (seg_rom ctusegs)
    /\ munch [(spz - CSTK, spz); (OA, OA + ON)]%Z m1 m2 /\ wmono ctusegs m1 m2 /\ mem_inv ctusegs m2
    /\ stk ctusegs m2 lo spz /\ RC m2.

Definition bio_ctrl_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo CSTK OA ON : Z) (cres : Z) (RC : (word -> option byte) -> Prop) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 cres) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ctusegs)
    /\ munch [(bv_unsigned sp - BIO_CTRL_FRAME - CSTK, bv_unsigned sp); (OA, OA + ON)]%Z m m' /\ wmono ctusegs m m' /\ mem_inv ctusegs m'
    /\ stk ctusegs m' lo (bv_unsigned sp) /\ RC m'.

Lemma BIO_ctrl_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (bio MT CTRL cmd : Z) (init ptr next prev nw : Z) (lo CSTK OA ON : Z)
    (cres : Z) (RC : (word -> option byte) -> Prop),
  stk ctusegs m lo (bv_unsigned sp) -> mem_inv ctusegs m -> GLOBALS_TOP <= lo -> (0 <= CSTK)%Z -> (lo <= bv_unsigned sp - BIO_CTRL_FRAME - CSTK)%Z ->
  rw_cells ctusegs m bio (bio_cells MT init ptr next prev nw) -> (0 < bio /\ bio + BIO_SIZE <= lo)%Z -> (bio mod 8 = 0)%Z ->
  ro_cells ctusegs m (MT + 64) [C8 (Z_to_bv 64 CTRL)] -> (0 < MT /\ MT + 72 <= GLOBALS_TOP)%Z -> (MT mod 8 = 0)%Z -> (0 < CTRL < 2^64 /\ CTRL mod 2 = 0)%Z ->
  (0 <= ON /\ (OA + ON <= bio \/ bio + BIO_SIZE <= OA) /\ (OA + ON <= 65536 \/ GLOBALS_TOP <= OA) /\ OA + ON <= lo)%Z ->
  a0 = Z_to_bv 64 bio -> a1 = Z_to_bv 64 cmd ->
  (* [comment removed for export] *)
  (forall (t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' : word) m1,
     munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m1 -> wmono ctusegs m m1 -> mem_inv ctusegs m1 ->
     stk ctusegs m1 lo (bv_unsigned sp + -48) ->
     rw_cells ctusegs m1 bio (bio_cells MT init ptr next prev nw) ->
     evt ctusegs (ctrl_callee_post (bv_unsigned sp + -48) gp tp sp a2 a1 a3 a0 s5 s6 s7 s8 s9 s10 s11 F fc lo CSTK OA ON cres
                    (fun m2 => rw_cells ctusegs m2 bio (bio_cells MT init ptr next prev nw) /\ RC m2) m1)
       (MS (mkR (Z_to_bv 64 0x10c5a4) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0' t1' t2' sp a2 a0 a1 a2 a3 a4' a5' a6' a7'
                 a1 a3 a0 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
           F (Z_to_bv 64 CTRL) fc None m1 (seg_rom ctusegs))) ->
  evt ctusegs (bio_ctrl_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo CSTK OA ON cres RC m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 BIO_CTRL) fc None m (seg_rom ctusegs)).
Proof.
  intros until RC. intros ST MI GLO HC0 LO HB HBLO HBAL HMT HMTR HMTAL HCTRL HOA -> -> CALLEE.
  unfold BIO_CTRL, BIO_CTRL_FRAME, GLOBALS_TOP, BIO_SIZE in *.
  pose proof (munch_refl [(bv_unsigned sp - 48 - CSTK, bv_unsigned sp); (OA, OA + ON)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU'.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  assert (SEPB : bio + 128 <= bv_unsigned sp - 48 \/ bv_unsigned sp <= bio) by lia.
  assert (SEPM : MT + 64 + 8 <= bv_unsigned sp - 48 \/ bv_unsigned sp <= MT + 64) by lia.
  unfold bio_cells, MallocRep.wz in HB.
  carve_frame 48%nat ST.
  do 8 zstep.
  (* [comment removed for export] *) zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|]. clear K.
  zstep. zstep. al8chk HBAL. zstep. (* [comment removed for export] *) zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|]. clear K.
  zstep. zstep. al8chk HMTAL. zstep. (* [comment removed for export] *) zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|]. clear K.
  do 2 zstep. zstep. (* [comment removed for export] *) zstep. if_cases K; zify_cond K; [exfalso; apply K; reflexivity|]. clear K.
  zstep. (* [comment removed for export] *) zstep. if_cases K; zify_cond K; [|exfalso; apply K; reflexivity]. clear K.
  zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|]. clear K. zstep. al8chk HMTAL. zstep. do 4 zstep. zstep.
  replace (ret_pc (Z_to_bv 64 CTRL)) with (Z_to_bv 64 CTRL) by (symmetry; apply ret_pc_even; lia).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
  (* [comment removed for export] *)
  eapply evt_cut.
  { eapply (CALLEE _ _ _ _ _ _ _ _ _ _ _ m1); [exact MU'| exact WM| exact MI| exact ST| exact HB]. }
  clear MU'. post_call ctusegs m1.
  match goal with H : rw_cells ctusegs _ bio _ |- _ => rename H into HB2 end.
  match goal with H : stk ctusegs _ lo _ |- _ => rename H into ST end.
  zstep. zstep. (* [comment removed for export] *) zstep. if_cases K; zify_cond K; [exfalso; apply K; reflexivity|]. clear K.
  zstep. (* [comment removed for export] *) zstep. if_cases K; zify_cond K; [|exfalso; apply K; reflexivity]. clear K.
  zstep. do 6 zstep. zstep. release_frame FR ST (bv_unsigned sp). zstep.
  finish.
Qed.

(* [comment removed for export] *)
Definition BIO_CTRL_NULL_STACK : Z := BIO_CTRL_FRAME + 16.

Lemma BIO_ctrl_null_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (bio MT cmd : Z) (init ptr next prev nw : Z) (lo : Z),
  stk ctusegs m lo (bv_unsigned sp) -> mem_inv ctusegs m -> GLOBALS_TOP <= lo -> (lo <= bv_unsigned sp - BIO_CTRL_NULL_STACK)%Z ->
  rw_cells ctusegs m bio (bio_cells MT init ptr next prev nw) -> (0 < bio /\ bio + BIO_SIZE <= lo)%Z -> (bio mod 8 = 0)%Z ->
  ro_cells ctusegs m (MT + 64) [C8 (Z_to_bv 64 NULL_CTRL)] -> (0 < MT /\ MT + 72 <= GLOBALS_TOP)%Z -> (MT mod 8 = 0)%Z ->
  a0 = Z_to_bv 64 bio -> a1 = Z_to_bv 64 cmd -> (cmd = BIO_CTRL_PUSH \/ cmd = BIO_CTRL_POP \/ cmd = BIO_CTRL_SET_PREFIX) ->
  evt ctusegs (bio_ctrl_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo 16 0 0 0
                 (fun m' => rw_cells ctusegs m' bio (bio_cells MT init ptr next prev nw) /\ True) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 BIO_CTRL) fc None m (seg_rom ctusegs)).
Proof.
  intros until lo. intros ST MI GLO LO HB HBLO HBAL HMT HMTR HMTAL -> -> Hcmd. unfold BIO_CTRL_NULL_STACK, BIO_CTRL_FRAME in LO.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  eapply BIO_ctrl_spec; try eassumption; try reflexivity.
  - lia.
  - unfold BIO_CTRL_FRAME. lia.
  - unfold NULL_CTRL. lia.
  - unfold BIO_SIZE, GLOBALS_TOP in *. lia.
  - intros t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' m1 MU1 WM1 MI1 ST1 HB1.
    eapply evt_mono.
    { eapply (null_ctrl_spec) with (cmd := cmd) (lo := lo); [rewrite unsigned_lit by lia; exact ST1| exact MI1| exact GLO| rewrite unsigned_lit by lia; lia| reflexivity| exact Hcmd]. }
    intros ms' PO. unfold null_ctrl_post in PO. unfold ctrl_callee_post.
    destruct PO as (u0 & u1 & u2 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & u3 & u4 & u5 & u6 & m2 & -> & MUc & WMc & MIc & STc).
    rewrite unsigned_lit in MUc, STc by lia.
    replace (ret_pc (Z_to_bv 64 1099172)) with (Z_to_bv 64 1099172) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    do 14 eexists. exists m2. split; [reflexivity|]. split.
    { eapply munch_weaken; [|exact MUc]. unfold sub_fp. cbn [outside]. intros x Hx. lia. }
    split; [exact WMc|]. split; [exact MIc|]. split; [exact STc|]. cbv beta.
    assert (HB2 : rw_cells ctusegs m2 bio (bio_cells MT init ptr next prev nw)).
    { eapply rw_cells_transport; [exact HB1| exact MUc| exact WMc|]. cbn [disjoint_from]. unfold bio_cells. simpl_sizes. unfold BIO_SIZE in *. lia. }
    exact (conj HB2 (conj HB2 I)).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition PREFIX_CTRL : Z := 0x13f254.
Definition PREFIX_CTRL_DEFAULT_CSTK : Z := 80.

Lemma prefix_ctrl_default_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (bio cmd : Z) (ctxA onw : Z) (out oprev onw2 : Z) (ctxp ind ls : Z) (lo : Z),
  stk ctusegs m lo (bv_unsigned sp) -> mem_inv ctusegs m -> GLOBALS_TOP <= lo -> (lo <= bv_unsigned sp - PREFIX_CTRL_DEFAULT_CSTK)%Z ->
  rw_cells ctusegs m bio (bio_prefix_cells AP_PREFIX_METH ctxA out onw) -> (0 < bio /\ bio + BIO_SIZE <= lo)%Z -> (bio mod 8 = 0)%Z ->
  rw_cells ctusegs m ctxA (prefix_ctx_cells ctxp ind ls) -> (0 < ctxA /\ ctxA + PREFIX_CTX_SIZE <= lo)%Z ->
  rw_cells ctusegs m out (bio_null_cells NULL_METHOD oprev onw2) -> (0 < out /\ out + BIO_SIZE <= lo)%Z -> (out mod 8 = 0)%Z ->
  ro_cells ctusegs m (NULL_METHOD + 64) [C8 (Z_to_bv 64 NULL_CTRL)] ->
  a0 = Z_to_bv 64 bio -> a1 = Z_to_bv 64 cmd -> (cmd = BIO_CTRL_PUSH \/ cmd = BIO_CTRL_POP) ->
  evt ctusegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom ctusegs)
      /\ munch [(bv_unsigned sp - PREFIX_CTRL_DEFAULT_CSTK, bv_unsigned sp); (0, 0 + 0)]%Z m m' /\ wmono ctusegs m m' /\ mem_inv ctusegs m'
      /\ stk ctusegs m' lo (bv_unsigned sp)
      /\ rw_cells ctusegs m' bio (bio_prefix_cells AP_PREFIX_METH ctxA out onw)
      /\ rw_cells ctusegs m' ctxA (prefix_ctx_cells ctxp ind ls)
      /\ rw_cells ctusegs m' out (bio_null_cells NULL_METHOD oprev onw2))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 PREFIX_CTRL) fc None m (seg_rom ctusegs)).
Proof.
  intros until lo. intros ST MI GLO LO HB HBLO HBAL HC HCLO HO HOLO HOAL HMT -> -> Hcmd.
  unfold PREFIX_CTRL_DEFAULT_CSTK, PREFIX_CTRL, GLOBALS_TOP, BIO_SIZE, PREFIX_CTX_SIZE in *.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (0, 0 + 0)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  assert (SEPB : bio + 128 <= bv_unsigned sp - 80 \/ bv_unsigned sp <= bio) by lia.
  assert (SEPC : ctxA + 16 <= bv_unsigned sp - 80 \/ bv_unsigned sp <= ctxA) by lia.
  assert (SEPO : out + 128 <= bv_unsigned sp - 80 \/ bv_unsigned sp <= out) by lia.
  unfold NULL_METHOD in HMT. cbn [Z.add] in HMT.
  assert (SEPM : 2978032 + 64 + 8 <= bv_unsigned sp - 80 \/ bv_unsigned sp <= 2978032 + 64) by lia.
  unfold bio_prefix_cells, bio_null_cells, bio_cells, MallocRep.wz in HB, HO. unfold prefix_ctx_cells, MallocRep.wz in HC.
  carve_frame 64%nat ST.
  do 11 zstep. (* [comment removed for export] *)
  zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|]. clear K.
  do 4 zstep. zstep. (* [comment removed for export] *)
  carve_frame 16%nat ST. do 4 zstep. zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|]. clear K. zstep. al8chk HBAL. do 5 zstep. release_frame FR0 ST (bv_unsigned sp + -64).
  zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|]. clear K.
  unfold BIO_CTRL_PUSH, BIO_CTRL_POP in Hcmd.
  zstep. zstep. zstep. if_cases K; zify_cond K; [|exfalso; rewrite ?signed_small in K by lia; lia]. clear K.
  zstep. zstep. if_cases K; zify_cond K; [exfalso; rewrite ?signed_small, ?unsigned_lit in K by lia; lia|]. clear K.
  zstep. zstep. if_cases K; zify_cond K; [|exfalso; rewrite ?signed_small, ?unsigned_lit in K by lia; lia]. clear K.
  (* [comment removed for export] *)
  zstep. zstep. carve_frame 16%nat ST. do 4 zstep. zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|]. clear K. zstep. al8chk HBAL.
  do 5 zstep. release_frame FR0 ST (bv_unsigned sp + -64).
  zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|]. clear K.
  zstep. zstep. carve_frame 16%nat ST. do 4 zstep. zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|]. clear K. zstep. al8chk HBAL.
  do 5 zstep. release_frame FR0 ST (bv_unsigned sp + -64).
  do 3 zstep. do 8 zstep. zstep. release_frame FR ST (bv_unsigned sp). zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
  match goal with H : munch _ m m5 |- _ => rename H into MU5 end. match goal with H : wmono ctusegs m m5 |- _ => rename H into WM5 end.
  eapply evt_mono.
  { eapply BIO_ctrl_null_spec with (cmd := cmd) (lo := lo) (MT := NULL_METHOD);
      [exact ST| exact MI| unfold GLOBALS_TOP; lia| unfold BIO_CTRL_NULL_STACK, BIO_CTRL_FRAME; lia
      | unfold bio_cells, MallocRep.wz; exact HO| unfold BIO_SIZE; lia| exact HOAL| unfold NULL_METHOD; exact HMT| unfold NULL_METHOD, GLOBALS_TOP; lia| unfold NULL_METHOD; reflexivity
      | reflexivity| reflexivity| unfold BIO_CTRL_PUSH, BIO_CTRL_POP, BIO_CTRL_SET_PREFIX; lia]. }
  intros ms' PO. unfold bio_ctrl_post in PO.
  destruct PO as (u0 & u1 & u2 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & u3 & u4 & u5 & u6 & m6 & -> & MUc & WMc & MIc & STc & HO6 & _).
  unfold BIO_CTRL_FRAME in MUc.
  do 14 eexists. exists m6. split; [reflexivity|].
  split. { eapply munch_trans; [eapply munch_weaken; [|exact MU5]| eapply munch_weaken; [|exact MUc]]; unfold sub_fp; cbn [outside]; intros x Hx; lia. }
  split; [eapply wmono_trans; [exact WM5| exact WMc]|]. split; [exact MIc|]. split; [exact STc|].
  split. { unfold bio_prefix_cells, bio_cells, MallocRep.wz. eapply rw_cells_transport; [exact HB| exact MUc| exact WMc|]. cbn [disjoint_from]. simpl_sizes. lia. }
  split. { unfold prefix_ctx_cells, MallocRep.wz. eapply rw_cells_transport; [exact HC| exact MUc| exact WMc|]. cbn [disjoint_from]. simpl_sizes. lia. }
  unfold bio_null_cells. exact HO6.
Qed.

(* [comment removed for export] *)
Definition BIO_CTRL_PREFIX_DFL_STACK : Z := BIO_CTRL_FRAME + PREFIX_CTRL_DEFAULT_CSTK.

Lemma BIO_ctrl_prefix_default_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (bio cmd : Z) (ctxA onw : Z) (out oprev onw2 : Z) (ctxp ind ls : Z) (lo : Z),
  stk ctusegs m lo (bv_unsigned sp) -> mem_inv ctusegs m -> GLOBALS_TOP <= lo -> (lo <= bv_unsigned sp - BIO_CTRL_PREFIX_DFL_STACK)%Z ->
  rw_cells ctusegs m bio (bio_prefix_cells AP_PREFIX_METH ctxA out onw) -> (0 < bio /\ bio + BIO_SIZE <= lo)%Z -> (bio mod 8 = 0)%Z ->
  rw_cells ctusegs m ctxA (prefix_ctx_cells ctxp ind ls) -> (0 < ctxA /\ ctxA + PREFIX_CTX_SIZE <= lo)%Z ->
  rw_cells ctusegs m out (bio_null_cells NULL_METHOD oprev onw2) -> (0 < out /\ out + BIO_SIZE <= lo)%Z -> (out mod 8 = 0)%Z ->
  ro_cells ctusegs m (AP_PREFIX_METH + 64) [C8 (Z_to_bv 64 PREFIX_CTRL)] ->
  ro_cells ctusegs m (NULL_METHOD + 64) [C8 (Z_to_bv 64 NULL_CTRL)] ->
  a0 = Z_to_bv 64 bio -> a1 = Z_to_bv 64 cmd -> (cmd = BIO_CTRL_PUSH \/ cmd = BIO_CTRL_POP) ->
  evt ctusegs (bio_ctrl_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo PREFIX_CTRL_DEFAULT_CSTK 0 0 0
                 (fun m' => rw_cells ctusegs m' bio (bio_prefix_cells AP_PREFIX_METH ctxA out onw)
                            /\ rw_cells ctusegs m' ctxA (prefix_ctx_cells ctxp ind ls)
                            /\ rw_cells ctusegs m' out (bio_null_cells NULL_METHOD oprev onw2)) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 BIO_CTRL) fc None m (seg_rom ctusegs)).
Proof.
  intros until lo. intros ST MI GLO LO HB HBLO HBAL HC HCLO HO HOLO HOAL HMT HMT0 -> -> Hcmd. unfold BIO_CTRL_PREFIX_DFL_STACK, BIO_CTRL_FRAME, PREFIX_CTRL_DEFAULT_CSTK in LO.
  pose proof GLO as GLO0. unfold GLOBALS_TOP in GLO0.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  unfold bio_prefix_cells in *.
  eapply (BIO_ctrl_spec ra sp gp tp t0 t1 t2 s0 s1 _ _ a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m bio AP_PREFIX_METH PREFIX_CTRL cmd
            1 ctxA out 0 onw lo PREFIX_CTRL_DEFAULT_CSTK 0 0 0
            (fun m' => rw_cells ctusegs m' bio (bio_cells AP_PREFIX_METH 1 ctxA out 0 onw) /\ rw_cells ctusegs m' ctxA (prefix_ctx_cells ctxp ind ls)
                       /\ rw_cells ctusegs m' out (bio_null_cells NULL_METHOD oprev onw2)));
    [exact ST| exact MI| exact GLO| unfold PREFIX_CTRL_DEFAULT_CSTK; lia| unfold PREFIX_CTRL_DEFAULT_CSTK, BIO_CTRL_FRAME; lia
    | exact HB| exact HBLO| exact HBAL| exact HMT| unfold AP_PREFIX_METH, GLOBALS_TOP; lia| unfold AP_PREFIX_METH; reflexivity| unfold PREFIX_CTRL; lia| unfold BIO_SIZE, GLOBALS_TOP in *; lia
    | reflexivity| reflexivity| ].
  intros t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' m1 MU1 WM1 MI1 ST1 HB1. unfold PREFIX_CTRL_DEFAULT_CSTK in MU1.
  assert (HC1 : rw_cells ctusegs m1 ctxA (prefix_ctx_cells ctxp ind ls)).
  { unfold prefix_ctx_cells. eapply rw_cells_transport; [exact HC| exact MU1| exact WM1|]. cbn [disjoint_from]. simpl_sizes. unfold PREFIX_CTX_SIZE in *. lia. }
  assert (HO1 : rw_cells ctusegs m1 out (bio_null_cells NULL_METHOD oprev onw2)).
  { unfold bio_null_cells, bio_cells. eapply rw_cells_transport; [exact HO| exact MU1| exact WM1|]. cbn [disjoint_from]. simpl_sizes. unfold BIO_SIZE in *. lia. }
  assert (HMT1 : ro_cells ctusegs m1 (NULL_METHOD + 64) [C8 (Z_to_bv 64 NULL_CTRL)]).
  { eapply ro_cells_transport; [exact HMT0| exact MU1|]. cbn [disjoint_from]. simpl_sizes. unfold NULL_METHOD. lia. }
  eapply evt_mono.
  { eapply (prefix_ctrl_default_spec) with (cmd := cmd) (lo := lo);
      [rewrite unsigned_lit by lia; exact ST1| exact MI1| exact GLO| rewrite unsigned_lit by lia; unfold PREFIX_CTRL_DEFAULT_CSTK; lia
      | exact HB1| exact HBLO| exact HBAL| exact HC1| exact HCLO| exact HO1| exact HOLO| exact HOAL| exact HMT1| reflexivity| reflexivity| exact Hcmd]. }
  intros ms' PO. unfold ctrl_callee_post.
  destruct PO as (u0 & u1 & u2 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & u3 & u4 & u5 & u6 & m2 & -> & MUc & WMc & MIc & STc & HB2 & HC2 & HO2).
  rewrite unsigned_lit in MUc, STc by lia. unfold PREFIX_CTRL_DEFAULT_CSTK in MUc.
  replace (ret_pc (Z_to_bv 64 1099172)) with (Z_to_bv 64 1099172) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  do 14 eexists. exists m2. split; [reflexivity|]. split.
  { first [exact MUc | eapply munch_weaken; [|exact MUc]; unfold sub_fp; cbn [outside]; intros x Hx; lia]. }
  split; [exact WMc|]. split; [exact MIc|]. split; [exact STc|]. cbv beta.
  unfold bio_prefix_cells in HB2. exact (conj HB2 (conj HB2 (conj HC2 HO2))).
Qed.
End WithCeiling0.
