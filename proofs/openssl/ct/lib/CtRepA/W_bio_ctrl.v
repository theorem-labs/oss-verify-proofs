(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Malloc Prog.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface RT_client_kit D_defs D_cs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnP Require Import BnKit BnKit2.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnW Require Import BnTac BnMem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnAsan Require Import AsKit AsLoop.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import LibKitA ARun BnHeapA BnRepDefs BnRepA AsStruct.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApUTacB.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApATac ApBImg ApWalkTac ApRepDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac step := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.
Local Ltac zstep := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
(* [comment removed for export] *)
Local Ltac alia := unfold BnHeapA.ACEIL, SEGTOP_A, SHHI, SHLO, STACK_WIN, USTACK_TOP in *; lia.
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

Definition NULL_CTRL : Z := 0x3234a0.
Definition NULL_CTRL_TAB : Z := 0xa4f80.   (* [comment removed for export] *)
Definition BIO_CTRL_PUSH : Z := 6.  Definition BIO_CTRL_POP : Z := 7.  Definition BIO_CTRL_SET_PREFIX : Z := 79.
Definition BIO_CTRL_SET_INDENT : Z := 80.  Definition BIO_CTRL_GET_INDENT : Z := 81.
Definition BIO_CTRL : Z := 0x237cc0.
Definition BIO_CTRL_FRAME : Z := 96.
Definition BIO_CTRL_RET : Z := 0x237e98.   (* [comment removed for export] *)
Definition PREFIX_CTRL : Z := 0x294a8c.

(* [comment removed for export] *)
Lemma ro_cells_recast : forall m A cs cs',
  ro_cells ctasegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> ro_cells ctasegs m A cs'.
Proof. intros m A cs cs' [Hwf Hb] Hwf' Eb. split; [exact Hwf'| rewrite Eb; exact Hb]. Qed.

(* [comment removed for export] *)
Lemma null_ctrl_tab : forall m, mem_inv ctasegs m ->
  ro_cells ctasegs m (NULL_CTRL_TAB + 40) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].
Proof.
  intros m MI. eapply (ro_cells_recast m _ [CB 16 (repeat (Z_to_bv 8 0) 16)]).
  - apply (ro_cells_image ctasegs m (NULL_CTRL_TAB + 40) (repeat (Z_to_bv 8 0) 16) MI); [vm_compute; reflexivity| unfold NULL_CTRL_TAB; lia| unfold NULL_CTRL_TAB; cbn; lia].
  - cbn. auto.
  - cbv -[Z_to_bv]. reflexivity.
Qed.

Section WithRT.
Context {AR : ARun}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma null_ctrl_tab_acc : forall Σ OW LB m, AHEAP Σ OW LB m -> acc ctasegs m NULL_CTRL_TAB 96.
Proof.
  intros Σ OW LB m H. eapply (af_lib_acc_lit RT AF Σ m (0xa4f80, 96, 128)); [exact (AH_art _ _ _ _ H)| vm_compute; reflexivity| cbn; unfold NULL_CTRL_TAB; lia| cbn; unfold NULL_CTRL_TAB; lia].
Qed.

(* [comment removed for export] *)
Lemma null_meth_img : forall Σ OW LB m, AHEAP Σ OW LB m ->
  ro_cells ctasegs m (NULL_METHOD + 64) [C8 (Z_to_bv 64 NULL_CTRL)] /\ acc ctasegs m NULL_METHOD 112.
Proof.
  intros Σ OW LB m H. pose proof (AH_art _ _ _ _ H) as HA. split.
  - apply (relro_ro_cells m (NULL_METHOD + 64) _ (af_relro RT AF Σ m HA)); [cbn; auto| unfold RELRO_LO, NULL_METHOD; lia| unfold RELRO_HI, NULL_METHOD; cbn; lia| vm_compute; reflexivity].
  - eapply (af_lib_acc_lit RT AF Σ m (0x54daa0, 112, 160)); [exact HA| vm_compute; reflexivity| cbn; unfold NULL_METHOD; lia| cbn; unfold NULL_METHOD; lia].
Qed.

(* [comment removed for export] *)
Lemma prefix_meth_img : forall Σ OW LB m, AHEAP Σ OW LB m ->
  ro_cells ctasegs m (AP_PREFIX_METH + 64) [C8 (Z_to_bv 64 PREFIX_CTRL)] /\ acc ctasegs m AP_PREFIX_METH 112.
Proof.
  intros Σ OW LB m H. pose proof (AH_art _ _ _ _ H) as HA. split.
  - apply (relro_ro_cells m (AP_PREFIX_METH + 64) _ (af_relro RT AF Σ m HA)); [cbn; auto| unfold RELRO_LO, AP_PREFIX_METH; lia| unfold RELRO_HI, AP_PREFIX_METH; cbn; lia| vm_compute; reflexivity].
  - eapply (af_lib_acc_lit RT AF Σ m (0x5489c0, 112, 160)); [exact HA| vm_compute; reflexivity| cbn; unfold AP_PREFIX_METH; lia| cbn; unfold AP_PREFIX_METH; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition null_ctrl_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Σ : rts RT) (OW LB : list block) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ctasegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m m' /\ wmono ctasegs m m' /\ mem_inv ctasegs m'
    /\ stk ctasegs m' lo (bv_unsigned sp) /\ AHEAP Σ OW LB m'.

Lemma null_ctrl_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (Σ : rts RT) (OW LB : list block) (cmd lo : Z),
  AHEAP Σ OW LB m ->
  stk ctasegs m lo (bv_unsigned sp) -> mem_inv ctasegs m -> ACEIL <= lo -> (lo <= bv_unsigned sp - 16)%Z ->
  a1 = Z_to_bv 64 cmd -> (cmd = BIO_CTRL_PUSH \/ cmd = BIO_CTRL_POP \/ cmd = BIO_CTRL_SET_PREFIX) ->
  evt ctasegs (null_ctrl_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Σ OW LB lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 NULL_CTRL) fc None m (seg_rom ctasegs)).
Proof.
  intros until lo. intros HEAP ST MI CEIL LO -> Hcmd.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (stk_below ctasegs m lo _ MI ST ltac:(lia)) as SPT. unfold UTOP in SPT.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3.
  pose proof (null_ctrl_tab m MI) as TAB. unfold NULL_CTRL_TAB in TAB. change (675712 + 40) with 675752 in TAB.
  pose proof (null_ctrl_tab_acc _ _ _ _ HEAP) as ACCT. unfold NULL_CTRL_TAB in ACCT.
  destruct (AH_shb _ _ _ _ HEAP) as [SHB1 SHB2].
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  assert (OFF : offshW [(bv_unsigned sp - 16, bv_unsigned sp)]%Z) by (cbn [offshW]; alia).
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  unfold NULL_CTRL, BIO_CTRL_PUSH, BIO_CTRL_POP, BIO_CTRL_SET_PREFIX in *.
  carve_frame 16%nat ST.
  destruct Hcmd as [-> | [-> | ->]].
  - do 6 zstep. zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|]. clear K.
    (* [comment removed for export] *)
    do 5 zstep. do 4 zstep. release_frame FR ST (bv_unsigned sp). zstep. finish.
    eapply AH_frame; [exact HEAP| exact MU| exact WM| constructor; [left; cbn; alia| constructor]].
  - do 6 zstep. zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|]. clear K.
    do 5 zstep. do 4 zstep. release_frame FR ST (bv_unsigned sp). zstep. finish.
    eapply AH_frame; [exact HEAP| exact MU| exact WM| constructor; [left; cbn; alia| constructor]].
  - do 6 zstep. zstep. if_cases K; zify_cond K; [|exfalso; rewrite ?unsigned_lit in K by lia; lia]. clear K.
    zstep. do 3 zstep. release_frame FR ST (bv_unsigned sp). zstep. finish.
    eapply AH_frame; [exact HEAP| exact MU| exact WM| constructor; [left; cbn; alia| constructor]].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ctrl_callee_post (spz : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Σ : rts RT) (OW LB : list block) (lo CSTK OA ON : Z) (cres : Z) (RC : (word -> option byte) -> Prop) (m1 : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m2,
    ms' = MS (mkR (Z_to_bv 64 BIO_CTRL_RET) (Z_to_bv 64 spz) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 cres) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 BIO_CTRL_RET) fc None m2 (seg_rom ctasegs)
    /\ munch [(spz - CSTK, spz); (OA, OA + ON)]%Z m1 m2 /\ wmono ctasegs m1 m2 /\ mem_inv ctasegs m2
    /\ stk ctasegs m2 lo spz /\ AHEAP Σ OW LB m2 /\ RC m2.

Definition bio_ctrl_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Σ : rts RT) (OW LB : list block) (lo CSTK OA ON : Z) (cres : Z) (RC : (word -> option byte) -> Prop) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 cres) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ctasegs)
    /\ munch [(bv_unsigned sp - BIO_CTRL_FRAME - CSTK, bv_unsigned sp); (OA, OA + ON)]%Z m m' /\ wmono ctasegs m m' /\ mem_inv ctasegs m'
    /\ stk ctasegs m' lo (bv_unsigned sp) /\ AHEAP Σ OW LB m' /\ RC m'.

Lemma BIO_ctrl_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (Σ : rts RT) (OW LB : list block)
    (pb : bptr) (bio MT CTRL cmd : Z) (init ptr next prev nw : Z) (lo CSTK OA ON : Z)
    (cres : Z) (RC : (word -> option byte) -> Prop),
  AHEAP Σ OW LB m ->
  stk ctasegs m lo (bv_unsigned sp) -> mem_inv ctasegs m -> ACEIL <= lo -> (0 <= CSTK)%Z -> (lo <= bv_unsigned sp - BIO_CTRL_FRAME - CSTK)%Z ->
  In (pb, bio, BIO_SIZE) OW -> rw_cells ctasegs m bio (bio_cells MT init ptr next prev nw) ->
  ro_cells ctasegs m (MT + 64) [C8 (Z_to_bv 64 CTRL)] -> acc ctasegs m MT 112 -> (0 < MT /\ MT + 112 <= SEGTOP_A /\ MT mod 8 = 0)%Z ->
  (0 < CTRL < 2^64 /\ CTRL mod 2 = 0)%Z ->
  (0 <= ON /\ (OA + ON <= bio \/ bio + BIO_SIZE <= OA) /\ (OA + ON <= 65536 \/ SEGTOP_A <= OA) /\ OA + ON <= lo /\ (OA + ON <= SHLO \/ SHHI <= OA))%Z ->
  a0 = Z_to_bv 64 bio -> a1 = Z_to_bv 64 cmd ->
  (* [comment removed for export] *)
  (forall (t0' t1' t2' s0' s1' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' s9' s10' t3' t4' t5' t6' : word) m1,
     munch [(bv_unsigned sp - 96, bv_unsigned sp)]%Z m m1 -> wmono ctasegs m m1 -> mem_inv ctasegs m1 ->
     stk ctasegs m1 lo (bv_unsigned sp + -96) -> AHEAP Σ OW LB m1 ->
     rw_cells ctasegs m1 bio (bio_cells MT init ptr next prev nw) ->
     evt ctasegs (ctrl_callee_post (bv_unsigned sp + -96) gp tp s0' s1' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11 F fc Σ OW LB lo CSTK OA ON cres
                    (fun m2 => rw_cells ctasegs m2 bio (bio_cells MT init ptr next prev nw) /\ RC m2) m1)
       (MS (mkR (Z_to_bv 64 BIO_CTRL_RET) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0' t1' t2' s0' s1' a0 a1 a2 a3 a4' a5' a6' a7'
                 s2' s3' s4' s5' s6' s7' s8' s9' s10' s11 t3' t4' t5' t6')
           F (Z_to_bv 64 CTRL) fc None m1 (seg_rom ctasegs))) ->
  evt ctasegs (bio_ctrl_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Σ OW LB lo CSTK OA ON cres RC m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 BIO_CTRL) fc None m (seg_rom ctasegs)).
Proof.
  intros until RC. intros HEAP ST MI CEIL HC0 LO HBIN HB HMT ACCM HMTR HCTRL HOA -> -> CALLEE.
  unfold BIO_CTRL, BIO_CTRL_FRAME, BIO_CTRL_RET, BIO_SIZE in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (stk_below ctasegs m lo _ MI ST ltac:(lia)) as SPT. unfold UTOP in SPT.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3. unfold SEGTOP_A in HMTR, HOA.
  assert (HBIN' : In (pb, bio, 128) (OW ++ LB)) by (apply in_or_app; left; exact HBIN).
  pose proof (AH_range_gen _ _ _ _ _ HEAP HBIN') as (BB0 & _ & _ & BBC & BBI). cbn [blk_addr blk_size fst snd] in BB0, BBC, BBI.
  pose proof (proj1 (AH_okA _ _ _ _ _ _ _ HEAP HBIN)) as ALB.
  ablock HEAP HBIN' ACCB OFFB.
  destruct (AH_shb _ _ _ _ HEAP) as [SHB1 SHB2].
  pose proof (munch_refl [(bv_unsigned sp - 96 - CSTK, bv_unsigned sp); (OA, OA + ON)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)]%Z m) as MU'.
  assert (OFF : offshW [(bv_unsigned sp - 96 - CSTK, bv_unsigned sp); (OA, OA + ON)]%Z) by (cbn [offshW]; alia).
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  assert (SEPB : bio + 128 <= bv_unsigned sp - 96 \/ bv_unsigned sp <= bio) by lia.
  assert (SEPM : MT + 64 + 8 <= bv_unsigned sp - 96 \/ bv_unsigned sp <= MT + 64) by alia.
  unfold bio_cells, MallocRep.wz in HB.
  carve_frame 96%nat ST.
  do 14 zstep.
  (* [comment removed for export] *) zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|]. clear K.
  (* [comment removed for export] *)
  zstep. zstep. (* [comment removed for export] *) zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|]. clear K.
  (* [comment removed for export] *)
  zstep. zstep. (* [comment removed for export] *) zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|]. clear K.
  (* [comment removed for export] *)
  zstep. zstep. zstep.
  (* [comment removed for export] *) zstep. zstep. if_cases K; zify_cond K; [exfalso; apply K; reflexivity|]. clear K.
  (* [comment removed for export] *)
  zstep. zstep. if_cases K; zify_cond K; [|exfalso; apply K; reflexivity]. clear K.
  (* [comment removed for export] *)
  zstep. do 5 zstep. zstep.
  replace (ret_pc (Z_to_bv 64 CTRL)) with (Z_to_bv 64 CTRL) by (symmetry; apply ret_pc_even; lia).
  name_mem m1.
  assert (HEAP1 : AHEAP Σ OW LB m1).
  { eapply AH_frame; [exact HEAP| exact MU'| exact WM|]. constructor; [left; cbn; alia| constructor]. }
  (* [comment removed for export] *)
  eapply evt_cut.
  { eapply (CALLEE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1); [exact MU'| exact WM| exact MI| exact ST| exact HEAP1| exact HB]. }
  clear MU' HEAP1. post_call ctasegs m1.
  match goal with H : rw_cells ctasegs _ bio _ |- _ => rename H into HB2 end.
  match goal with H : stk ctasegs _ lo _ |- _ => rename H into ST end.
  match goal with H : AHEAP _ _ _ _ |- _ => rename H into HEAP2 end.
  (* [comment removed for export] *)
  zstep. zstep. (* [comment removed for export] *) zstep. if_cases K; zify_cond K; [exfalso; apply K; reflexivity|]. clear K.
  (* [comment removed for export] *) zstep. (* [comment removed for export] *) zstep. if_cases K; zify_cond K; [|exfalso; apply K; reflexivity]. clear K.
  (* [comment removed for export] *)
  zstep. do 12 zstep. zstep. release_frame FR ST (bv_unsigned sp). zstep.
  finish.
Qed.

(* [comment removed for export] *)
Definition BIO_CTRL_NULL_STACK : Z := BIO_CTRL_FRAME + 16.

Lemma BIO_ctrl_null_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (Σ : rts RT) (OW LB : list block) (pb : bptr) (bio cmd : Z) (init ptr next prev nw : Z) (lo : Z),
  AHEAP Σ OW LB m ->
  stk ctasegs m lo (bv_unsigned sp) -> mem_inv ctasegs m -> ACEIL <= lo -> (lo <= bv_unsigned sp - BIO_CTRL_NULL_STACK)%Z ->
  In (pb, bio, BIO_SIZE) OW -> rw_cells ctasegs m bio (bio_cells NULL_METHOD init ptr next prev nw) ->
  a0 = Z_to_bv 64 bio -> a1 = Z_to_bv 64 cmd -> (cmd = BIO_CTRL_PUSH \/ cmd = BIO_CTRL_POP \/ cmd = BIO_CTRL_SET_PREFIX) ->
  evt ctasegs (bio_ctrl_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Σ OW LB lo 16 0 0 0
                 (fun m' => rw_cells ctasegs m' bio (bio_cells NULL_METHOD init ptr next prev nw) /\ True) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 BIO_CTRL) fc None m (seg_rom ctasegs)).
Proof.
  intros until lo. intros HEAP ST MI CEIL LO HBIN HB -> -> Hcmd. unfold BIO_CTRL_NULL_STACK, BIO_CTRL_FRAME in LO.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3.
  destruct (null_meth_img _ _ _ _ HEAP) as [HMT ACCM].
  pose proof (AH_range_gen _ _ _ _ _ HEAP ltac:(apply in_or_app; left; exact HBIN)) as (BB0 & _ & _ & BBC & _). cbn [blk_addr blk_size fst snd] in BB0, BBC.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  eapply BIO_ctrl_spec with (pb := pb); try eassumption; try reflexivity.
  - lia.
  - unfold BIO_CTRL_FRAME. lia.
  - unfold NULL_METHOD, SEGTOP_A. split; [lia|]. split; [lia|]. reflexivity.
  - unfold NULL_CTRL. split; [lia|]. reflexivity.
  - unfold BIO_SIZE, SEGTOP_A, SHLO. lia.
  - intros t0' t1' t2' s0' s1' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' s9' s10' t3' t4' t5' t6' m1 MU1 WM1 MI1 ST1 HEAP1 HB1.
    eapply evt_mono.
    { eapply (null_ctrl_spec) with (cmd := cmd) (lo := lo);
        [exact HEAP1| rewrite unsigned_lit by lia; exact ST1| exact MI1| exact CEIL| rewrite unsigned_lit by lia; lia| reflexivity| exact Hcmd]. }
    intros ms' PO. unfold null_ctrl_post in PO. unfold ctrl_callee_post.
    destruct PO as (u0 & u1 & u2 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & u3 & u4 & u5 & u6 & m2 & -> & MUc & WMc & MIc & STc & HEAPc).
    rewrite unsigned_lit in MUc, STc by lia. unfold BIO_CTRL_RET.
    replace (ret_pc (Z_to_bv 64 2326168)) with (Z_to_bv 64 2326168) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    do 14 eexists. exists m2. split; [reflexivity|]. split.
    { eapply munch_weaken; [|exact MUc]. unfold sub_fp. cbn [outside]. intros x Hx. lia. }
    split; [exact WMc|]. split; [exact MIc|]. split; [exact STc|]. split; [exact HEAPc|]. cbv beta.
    assert (HB2 : rw_cells ctasegs m2 bio (bio_cells NULL_METHOD init ptr next prev nw)).
    { eapply rw_cells_transport; [exact HB1| exact MUc| exact WMc|]. cbn [disjoint_from]. unfold bio_cells. simpl_sizes. unfold BIO_SIZE in *. lia. }
    exact (conj HB2 (conj HB2 I)).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition PREFIX_CTRL_DEFAULT_CSTK : Z := 112.

Lemma prefix_ctrl_default_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (Σ : rts RT) (OW LB : list block) (pb pc po : bptr)
    (bio cmd : Z) (ctxA onw : Z) (out oprev onw2 : Z) (ctxp ind ls : Z) (lo : Z),
  AHEAP Σ OW LB m ->
  stk ctasegs m lo (bv_unsigned sp) -> mem_inv ctasegs m -> ACEIL <= lo -> (lo <= bv_unsigned sp - PREFIX_CTRL_DEFAULT_CSTK)%Z ->
  In (pb, bio, BIO_SIZE) OW -> rw_cells ctasegs m bio (bio_prefix_cells AP_PREFIX_METH ctxA out onw) ->
  In (pc, ctxA, PREFIX_CTX_SIZE) OW -> rw_cells ctasegs m ctxA (prefix_ctx_cells ctxp ind ls) ->
  In (po, out, BIO_SIZE) OW -> rw_cells ctasegs m out (bio_null_cells NULL_METHOD oprev onw2) ->
  a0 = Z_to_bv 64 bio -> a1 = Z_to_bv 64 cmd -> (cmd = BIO_CTRL_PUSH \/ cmd = BIO_CTRL_POP) ->
  evt ctasegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom ctasegs)
      /\ munch [(bv_unsigned sp - PREFIX_CTRL_DEFAULT_CSTK, bv_unsigned sp); (0, 0 + 0)]%Z m m' /\ wmono ctasegs m m' /\ mem_inv ctasegs m'
      /\ stk ctasegs m' lo (bv_unsigned sp) /\ AHEAP Σ OW LB m'
      /\ rw_cells ctasegs m' bio (bio_prefix_cells AP_PREFIX_METH ctxA out onw)
      /\ rw_cells ctasegs m' ctxA (prefix_ctx_cells ctxp ind ls)
      /\ rw_cells ctasegs m' out (bio_null_cells NULL_METHOD oprev onw2))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 PREFIX_CTRL) fc None m (seg_rom ctasegs)).
Proof.
  intros until lo. intros HEAP ST MI CEIL LO HBIN HB HCIN HC HOIN HO -> -> Hcmd.
  unfold PREFIX_CTRL_DEFAULT_CSTK, PREFIX_CTRL, BIO_SIZE, PREFIX_CTX_SIZE in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (stk_below ctasegs m lo _ MI ST ltac:(lia)) as SPT. unfold UTOP in SPT.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3.
  assert (HBIN' : In (pb, bio, 128) (OW ++ LB)) by (apply in_or_app; left; exact HBIN).
  assert (HCIN' : In (pc, ctxA, 16) (OW ++ LB)) by (apply in_or_app; left; exact HCIN).
  assert (HOIN' : In (po, out, 128) (OW ++ LB)) by (apply in_or_app; left; exact HOIN).
  pose proof (AH_range_gen _ _ _ _ _ HEAP HBIN') as (BB0 & _ & _ & BBC & BBI). cbn [blk_addr blk_size fst snd] in BB0, BBC, BBI.
  pose proof (AH_range_gen _ _ _ _ _ HEAP HCIN') as (BC0 & _ & _ & BCC & BCI). cbn [blk_addr blk_size fst snd] in BC0, BCC, BCI.
  pose proof (AH_range_gen _ _ _ _ _ HEAP HOIN') as (BO0 & _ & _ & BOC & BOI). cbn [blk_addr blk_size fst snd] in BO0, BOC, BOI.
  pose proof (proj1 (AH_okA _ _ _ _ _ _ _ HEAP HBIN)) as ALB. pose proof (proj1 (AH_okA _ _ _ _ _ _ _ HEAP HOIN)) as ALO.
  ablock HEAP HBIN' ACCB OFFB. ablock HEAP HOIN' ACCO OFFO.
  destruct (AH_shb _ _ _ _ HEAP) as [SHB1 SHB2].
  pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp); (0, 0 + 0)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  assert (OFF : offshW [(bv_unsigned sp - 112, bv_unsigned sp); (0, 0 + 0)]%Z) by (cbn [offshW]; alia).
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  assert (SEPB : bio + 128 <= bv_unsigned sp - 112 \/ bv_unsigned sp <= bio) by lia.
  assert (SEPC : ctxA + 16 <= bv_unsigned sp - 112 \/ bv_unsigned sp <= ctxA) by lia.
  assert (SEPO : out + 128 <= bv_unsigned sp - 112 \/ bv_unsigned sp <= out) by lia.
  unfold bio_prefix_cells, bio_null_cells, bio_cells, MallocRep.wz in HB, HO. unfold prefix_ctx_cells, MallocRep.wz in HC.
  carve_frame 80%nat ST.
  do 12 zstep. (* [comment removed for export] *)
  zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|]. clear K.
  (* [comment removed for export] *)
  do 4 zstep. zstep. zstep.
  carve_frame 16%nat ST. do 9 zstep. release_frame FR0 ST (bv_unsigned sp + -80).
  zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|]. clear K.
  unfold BIO_CTRL_PUSH, BIO_CTRL_POP in Hcmd.
  zstep. zstep. zstep. if_cases K; zify_cond K; [|exfalso; rewrite ?signed_small in K by lia; lia]. clear K.
  zstep. zstep. if_cases K; zify_cond K; [exfalso; rewrite ?signed_small, ?unsigned_lit in K by lia; lia|]. clear K.
  zstep. zstep. if_cases K; zify_cond K; [|exfalso; rewrite ?signed_small, ?unsigned_lit in K by lia; lia]. clear K.
  (* [comment removed for export] *)
  zstep. zstep. carve_frame 16%nat ST. do 4 zstep. zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|]. clear K.
  do 5 zstep. release_frame FR0 ST (bv_unsigned sp + -80).
  zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|]. clear K.
  zstep. zstep. carve_frame 16%nat ST. do 4 zstep. zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia|]. clear K.
  do 5 zstep. release_frame FR0 ST (bv_unsigned sp + -80).
  do 3 zstep. do 9 zstep. zstep. release_frame FR ST (bv_unsigned sp). zstep.
  name_mem m5.
  match goal with H : munch _ m m5 |- _ => rename H into MU5 end. match goal with H : wmono ctasegs m m5 |- _ => rename H into WM5 end.
  assert (HEAP5 : AHEAP Σ OW LB m5).
  { eapply AH_frame; [exact HEAP| exact MU5| exact WM5|]. constructor; [left; cbn; alia|]. constructor; [right; left; cbn; intros x Hx; exfalso; lia| constructor]. }
  eapply evt_mono.
  { eapply BIO_ctrl_null_spec with (cmd := cmd) (lo := lo) (pb := po);
      [exact HEAP5| exact ST| exact MI| exact CEIL| unfold BIO_CTRL_NULL_STACK, BIO_CTRL_FRAME; lia
      | exact HOIN| unfold bio_cells, MallocRep.wz; exact HO
      | reflexivity| reflexivity| unfold BIO_CTRL_PUSH, BIO_CTRL_POP, BIO_CTRL_SET_PREFIX; lia]. }
  intros ms' PO. unfold bio_ctrl_post in PO.
  destruct PO as (u0 & u1 & u2 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & u3 & u4 & u5 & u6 & m6 & -> & MUc & WMc & MIc & STc & HEAPc & HO6 & _).
  unfold BIO_CTRL_FRAME in MUc.
  do 14 eexists. exists m6. split; [reflexivity|].
  split. { eapply munch_trans; [eapply munch_weaken; [|exact MU5]| eapply munch_weaken; [|exact MUc]]; unfold sub_fp; cbn [outside]; intros x Hx; lia. }
  split; [eapply wmono_trans; [exact WM5| exact WMc]|]. split; [exact MIc|]. split; [exact STc|]. split; [exact HEAPc|].
  split. { unfold bio_prefix_cells, bio_cells, MallocRep.wz. eapply rw_cells_transport; [exact HB| exact MUc| exact WMc|]. cbn [disjoint_from]. simpl_sizes. lia. }
  split. { unfold prefix_ctx_cells, MallocRep.wz. eapply rw_cells_transport; [exact HC| exact MUc| exact WMc|]. cbn [disjoint_from]. simpl_sizes. lia. }
  unfold bio_null_cells. exact HO6.
Qed.

(* [comment removed for export] *)
Definition BIO_CTRL_PREFIX_DFL_STACK : Z := BIO_CTRL_FRAME + PREFIX_CTRL_DEFAULT_CSTK.

Lemma BIO_ctrl_prefix_default_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (Σ : rts RT) (OW LB : list block) (pb pc po : bptr)
    (bio cmd : Z) (ctxA onw : Z) (out oprev onw2 : Z) (ctxp ind ls : Z) (lo : Z),
  AHEAP Σ OW LB m ->
  stk ctasegs m lo (bv_unsigned sp) -> mem_inv ctasegs m -> ACEIL <= lo -> (lo <= bv_unsigned sp - BIO_CTRL_PREFIX_DFL_STACK)%Z ->
  In (pb, bio, BIO_SIZE) OW -> rw_cells ctasegs m bio (bio_prefix_cells AP_PREFIX_METH ctxA out onw) ->
  In (pc, ctxA, PREFIX_CTX_SIZE) OW -> rw_cells ctasegs m ctxA (prefix_ctx_cells ctxp ind ls) ->
  In (po, out, BIO_SIZE) OW -> rw_cells ctasegs m out (bio_null_cells NULL_METHOD oprev onw2) ->
  a0 = Z_to_bv 64 bio -> a1 = Z_to_bv 64 cmd -> (cmd = BIO_CTRL_PUSH \/ cmd = BIO_CTRL_POP) ->
  evt ctasegs (bio_ctrl_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Σ OW LB lo PREFIX_CTRL_DEFAULT_CSTK 0 0 0
                 (fun m' => rw_cells ctasegs m' bio (bio_prefix_cells AP_PREFIX_METH ctxA out onw)
                            /\ rw_cells ctasegs m' ctxA (prefix_ctx_cells ctxp ind ls)
                            /\ rw_cells ctasegs m' out (bio_null_cells NULL_METHOD oprev onw2)) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 BIO_CTRL) fc None m (seg_rom ctasegs)).
Proof.
  intros until lo. intros HEAP ST MI CEIL LO HBIN HB HCIN HC HOIN HO -> -> Hcmd. unfold BIO_CTRL_PREFIX_DFL_STACK, BIO_CTRL_FRAME, PREFIX_CTRL_DEFAULT_CSTK in LO.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3.
  destruct (prefix_meth_img _ _ _ _ HEAP) as [HMT ACCM].
  pose proof (AH_range_gen _ _ _ _ _ HEAP ltac:(apply in_or_app; left; exact HCIN)) as (_ & _ & _ & BCC & _). cbn [blk_addr blk_size fst snd] in BCC.
  pose proof (AH_range_gen _ _ _ _ _ HEAP ltac:(apply in_or_app; left; exact HOIN)) as (_ & _ & _ & BOC & _). cbn [blk_addr blk_size fst snd] in BOC.
  pose proof (AH_range_gen _ _ _ _ _ HEAP ltac:(apply in_or_app; left; exact HBIN)) as (BB0 & _ & _ & BBC & _). cbn [blk_addr blk_size fst snd] in BB0, BBC.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  unfold PREFIX_CTX_SIZE, BIO_SIZE in BCC, BOC, BBC.
  unfold bio_prefix_cells in *.
  eapply (BIO_ctrl_spec ra sp gp tp t0 t1 t2 s0 s1 _ _ a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Σ OW LB pb bio AP_PREFIX_METH PREFIX_CTRL cmd
            1 ctxA out 0 onw lo PREFIX_CTRL_DEFAULT_CSTK 0 0 0
            (fun m' => rw_cells ctasegs m' bio (bio_cells AP_PREFIX_METH 1 ctxA out 0 onw) /\ rw_cells ctasegs m' ctxA (prefix_ctx_cells ctxp ind ls)
                       /\ rw_cells ctasegs m' out (bio_null_cells NULL_METHOD oprev onw2)));
    [exact HEAP| exact ST| exact MI| exact CEIL| unfold PREFIX_CTRL_DEFAULT_CSTK; lia| unfold PREFIX_CTRL_DEFAULT_CSTK, BIO_CTRL_FRAME; lia
    | exact HBIN| exact HB| exact HMT| exact ACCM| unfold AP_PREFIX_METH, SEGTOP_A; split; [lia|]; split; [lia|]; reflexivity
    | unfold PREFIX_CTRL; split; [lia|]; reflexivity| unfold BIO_SIZE, SEGTOP_A, SHLO; lia
    | reflexivity| reflexivity| ].
  intros t0' t1' t2' s0' s1' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' s9' s10' t3' t4' t5' t6' m1 MU1 WM1 MI1 ST1 HEAP1 HB1. unfold PREFIX_CTRL_DEFAULT_CSTK in MU1.
  assert (HC1 : rw_cells ctasegs m1 ctxA (prefix_ctx_cells ctxp ind ls)).
  { unfold prefix_ctx_cells. eapply rw_cells_transport; [exact HC| exact MU1| exact WM1|]. cbn [disjoint_from]. simpl_sizes. lia. }
  assert (HO1 : rw_cells ctasegs m1 out (bio_null_cells NULL_METHOD oprev onw2)).
  { unfold bio_null_cells, bio_cells. eapply rw_cells_transport; [exact HO| exact MU1| exact WM1|]. cbn [disjoint_from]. simpl_sizes. lia. }
  eapply evt_mono.
  { eapply (prefix_ctrl_default_spec) with (cmd := cmd) (lo := lo) (pb := pb) (pc := pc) (po := po);
      [exact HEAP1| rewrite unsigned_lit by lia; exact ST1| exact MI1| exact CEIL| rewrite unsigned_lit by lia; unfold PREFIX_CTRL_DEFAULT_CSTK; lia
      | exact HBIN| exact HB1| exact HCIN| exact HC1| exact HOIN| exact HO1| reflexivity| reflexivity| exact Hcmd]. }
  intros ms' PO. unfold ctrl_callee_post.
  destruct PO as (u0 & u1 & u2 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & u3 & u4 & u5 & u6 & m2 & -> & MUc & WMc & MIc & STc & HEAPc & HB2 & HC2 & HO2).
  rewrite unsigned_lit in MUc, STc by lia. unfold PREFIX_CTRL_DEFAULT_CSTK in MUc. unfold BIO_CTRL_RET.
  replace (ret_pc (Z_to_bv 64 2326168)) with (Z_to_bv 64 2326168) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  do 14 eexists. exists m2. split; [reflexivity|]. split.
  { first [exact MUc | eapply munch_weaken; [|exact MUc]; unfold sub_fp; cbn [outside]; intros x Hx; lia]. }
  split; [exact WMc|]. split; [exact MIc|]. split; [exact STc|]. split; [exact HEAPc|]. cbv beta.
  unfold bio_prefix_cells in HB2. exact (conj HB2 (conj HB2 (conj HC2 HO2))).
Qed.
End WithRT.
