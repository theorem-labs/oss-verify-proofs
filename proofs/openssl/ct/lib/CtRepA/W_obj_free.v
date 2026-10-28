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
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem RzCPS. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Malloc Prog BnBase BnModel BnTree ApBase ApLogic.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface RT_client_kit D_defs D_cs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnP Require Import BnKit BnKit2.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnW Require Import BnTac BnMem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnAsan Require Import AsKit AsLoop.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import LibKitA ARun BnHeapA BnRepDefs BnRepA ImplA BnIfaceA AsStruct W_cryptoA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApUTacB.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApATac ApBImg ApWalkTac ApRepDefs ApIface W_bio_ctrl W_prefix_create.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac step := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.
Local Ltac zstep := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
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

Definition ASN1_OBJECT_FREE : Z := 0x2238c0.
Definition ASN1_OBJECT_FREE_STACK : Z := 64 + CRYPTO_FREE_STACK.
Definition AOBJ_DYN_FLAGS : Z := 9.       (* [comment removed for export] *)

Section WithRT.
Context {AR : ARun}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

(* [comment removed for export] *)
Definition vfree_postA (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (Σ : rts RT) (OW' LB : list block) (lo : Z) (m : mem) (fin : mem -> Prop)
    (Σ' : rts RT) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m',
    ms' = MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom ctasegs)
    /\ mem_inv ctasegs m' /\ stk ctasegs m' lo (bv_unsigned sp)
    /\ apres LB OW' (bv_unsigned sp) m m'
    /\ rt_credit RT Σ <= rt_credit RT Σ'
    /\ AHEAP Σ' OW' LB m' /\ fin m'.

(* [comment removed for export] *)
Ltac bytes_lit_eq := cbv -[Z_to_bv]; repeat first [reflexivity | apply (f_equal2 (@cons _)); [apply bv_eq; vm_compute; reflexivity|]].

(* [comment removed for export] *)
Lemma aobj_dyn_cells_b : forall m A sn ln nid len data,
  rw_cells ctasegs m A (asn1_object_cells sn ln nid len data AOBJ_DYN_FLAGS) ->
  rw_cells ctasegs m A ([C8 (wz sn); C8 (wz ln); C4 (wz nid); C4 (wz len); C8 (wz data)] ++
                        [C1 (Z_to_bv 8 9); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C4 (wz 0)]).
Proof.
  intros m A sn ln nid len data H. unfold asn1_object_cells, AOBJ_DYN_FLAGS in H.
  change [C8 (wz sn); C8 (wz ln); C4 (wz nid); C4 (wz len); C8 (wz data); C4 (wz 9); C4 (wz 0)]
    with ([C8 (wz sn); C8 (wz ln); C4 (wz nid); C4 (wz len); C8 (wz data)] ++ [C4 (wz 9); C4 (wz 0)]) in H.
  eapply rw_cells_recast; [exact H| | |].
  - destruct H as [[W _] _]. apply cells_wf_app in W. destruct W as [W1 W2]. apply cells_wf_app. split; [exact W1|]. cbn. tauto.
  - rewrite !cells_bytes_app. f_equal; unfold MallocRep.wz; bytes_lit_eq.
  - rewrite !cells_size_app. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma aclient_addr_sub : forall (L L' : list block) SP SP' a,
  (forall b, In b L' -> In b L) -> SP <= SP' -> aclient_addr L' SP' a -> aclient_addr L SP a.
Proof.
  intros L L' SP SP' a HL HS [Ha|[Ha|(b & Hb & Hr)]]; [left; lia| right; left; exact Ha| right; right].
  exists b. split; [apply HL; exact Hb| exact Hr].
Qed.

Lemma lb_remove2_app_incl : forall p q (OW LB : list block) b,
  In b (lb_remove p (lb_remove q OW) ++ LB) -> In b (OW ++ LB).
Proof.
  intros p q OW LB b Hb. apply in_app_iff in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left| right; exact Hb].
  eapply lb_remove_incl. eapply lb_remove_incl. exact Hb.
Qed.

Lemma lb_remove_app_incl1 : forall p (OW LB : list block) b,
  In b (lb_remove p OW ++ LB) -> In b (OW ++ LB).
Proof.
  intros p OW LB b Hb. apply in_app_iff in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left| right; exact Hb].
  eapply lb_remove_incl. exact Hb.
Qed.

(* [comment removed for export] *)
Lemma lb_remove_app_l : forall p (OW LB : list block) b,
  (forall b', In b' LB -> blk_id b' <> p) -> In b (lb_remove p OW ++ LB) -> In b (lb_remove p (OW ++ LB)).
Proof.
  intros p OW LB b HLB Hb. apply lb_remove_In. apply in_app_iff in Hb. destruct Hb as [Hb|Hb].
  - apply lb_remove_In in Hb. destruct Hb as [Hb Hne]. split; [apply in_or_app; left; exact Hb| exact Hne].
  - split; [apply in_or_app; right; exact Hb| exact (HLB b Hb)].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
Lemma ASN1_OBJECT_free_static_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (Σ : rts RT) (OW LB : list block) (lo X : Z),
  AHEAP Σ OW LB m ->
  stk ctasegs m lo (bv_unsigned sp) -> mem_inv ctasegs m -> ACEIL <= lo -> (lo <= bv_unsigned sp - 64)%Z ->
  ro_cells ctasegs m (X + 32) [C4 (wz 0)] -> 0 < X -> X + 40 <= SEGTOP_A -> X mod 8 = 0 -> acc ctasegs m X 40 -> a0 = wz X ->
  evt ctasegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom ctasegs)
      /\ munch [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m m' /\ wmono ctasegs m m' /\ mem_inv ctasegs m'
      /\ stk ctasegs m' lo (bv_unsigned sp) /\ AHEAP Σ OW LB m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ASN1_OBJECT_FREE) fc None m (seg_rom ctasegs)).
Proof.
  intros until X. intros HEAP ST MI CEIL LO FL XP XL XAL ACCX ->.
  unfold ASN1_OBJECT_FREE, MallocRep.wz in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (stk_below ctasegs m lo _ MI ST ltac:(lia)) as SPT. unfold UTOP in SPT.
  pose proof (AH_ceil _ _ _ _ HEAP) as (CL1 & CL2 & CL3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in CL1, CL2, CL3, XL.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  destruct (AH_shb _ _ _ _ HEAP) as [SHB1 SHB2].
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  assert (OFF : offshW [(bv_unsigned sp - 64, bv_unsigned sp)]%Z) by (cbn [offshW]; alia).
  pose proof (ro_cells_bound _ _ _ _ FL) as XB. cbn in XB.
  assert (FLB : ro_cells ctasegs m (X + 32) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]).
  { eapply ro_cells_recast; [exact FL| cbn; auto| unfold MallocRep.wz; bytes_lit_eq]. }
  carve_frame 64%nat ST. do 10 zstep.
  zstep. if_cases K0; zify_cond K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia|]. clear K0.
  zstep. zstep. zstep.
  zstep. if_cases K1; zify_cond K1; [|exfalso; revert K1; vm_compute; congruence]. clear K1.
  zstep. zstep.
  zstep. if_cases K2; zify_cond K2; [|exfalso; revert K2; vm_compute; congruence]. clear K2.
  zstep. zstep.
  zstep. if_cases K3; zify_cond K3; [exfalso; revert K3; vm_compute; congruence|]. clear K3.
  do 9 zstep. release_frame FR ST (bv_unsigned sp). zstep.
  name_mem m9.
  match goal with H : munch _ m m9 |- _ => rename H into MU9 end. match goal with H : wmono ctasegs m m9 |- _ => rename H into WM9 end.
  assert (HEAP9 : AHEAP Σ OW LB m9).
  { eapply AH_frame; [exact HEAP| exact MU9| exact WM9|]. constructor; [left; cbn; alia| constructor]. }
  finish.
Qed.

(* [comment removed for export] *)
Lemma ASN1_OBJECT_free_null_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  stk ctasegs m lo (bv_unsigned sp) -> mem_inv ctasegs m -> SEGTOP_A <= lo -> (lo <= bv_unsigned sp - 64)%Z ->
  a0 = Z_to_bv 64 0 ->
  evt ctasegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom ctasegs)
      /\ munch [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m m' /\ wmono ctasegs m m' /\ mem_inv ctasegs m'
      /\ stk ctasegs m' lo (bv_unsigned sp))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ASN1_OBJECT_FREE) fc None m (seg_rom ctasegs)).
Proof.
  intros until lo. intros ST MI GLO LO ->.
  unfold ASN1_OBJECT_FREE, SEGTOP_A in *.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  carve_frame 64%nat ST. do 10 zstep.
  zstep. if_cases K0; zify_cond K0; [|exfalso; apply K0; reflexivity]. clear K0.
  do 9 zstep. release_frame FR ST (bv_unsigned sp). zstep.
  finish.
Qed.

End WithRT.
