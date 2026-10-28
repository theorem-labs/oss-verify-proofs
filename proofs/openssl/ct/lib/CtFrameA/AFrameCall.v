(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac ZBridge RzCPS. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prog BnBase BnModel BnTree.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface D_defs I_lkit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import RT_iface2.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnAsan Require Import AsKit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import LibKitA ARun BnHeapA ImplA BnIfaceA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtFrameA Require Import AFrameKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section WithRT.
Context {AR : ARun}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation FR := (@ar_FR AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ASTA_reframe : forall Σ Σ' (Pm : machine_state -> Prop) c,
  rt_allow RT Σ' = rt_allow RT Σ -> (forall mo, ARTM RT Σ mo -> ARTM RT Σ' mo) ->
  ASTA RT Σ PMc Pm c -> ASTA RT Σ' PMc Pm c.
Proof.
  intros Σ Σ' Pm c EA EM H. unfold ASTA in *. rewrite EA. eapply AST_conseq; [exact H | intros ms X; exact X |].
  intros mo [X Y]. split; [exact (EM mo X) | exact Y].
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma AH_same_pb : forall Σ OW LB m m', AHEAP Σ OW LB m -> ART RT Σ m' -> wmono ctasegs m m' ->
  agree_on (fun a => exists b i, In b LB /\ pb_in b /\ 0 <= i < blk_size b /\ a = shad (blk_addr b + i)) m m' ->
  AHEAP Σ OW LB m'.
Proof.
  intros Σ OW LB m m' H HA WM AG. pose proof H as (_ & HS & HF & (FW & PB & LBr & P1 & P2 & F & AP) & Rest).
  split; [exact HA|]. split; [exact HS|]. split; [exact HF|]. split; [| exact Rest].
  split; [exact (fr_wr_wmono m m' FW WM)|]. exists PB, LBr. split; [exact P1|]. split; [exact P2|]. split; [| exact AP].
  apply Forall_forall. intros b Hb. destruct (proj1 (Forall_forall _ _) F b Hb) as (PI & Hn & WR & AC).
  assert (HbL : In b LB) by (eapply Permutation_in; [symmetry; exact P1 | apply in_or_app; left; exact Hb]).
  split; [exact PI|]. split; [exact Hn|]. split; [exact (wr_at_transport ctasegs m m' _ _ WR WM)|].
  eapply acc_agree; [exact AG | exact AC |]. intros i Hi. exists b, i. auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition sm_postA (k : nat) (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (Σ : rts RT) (OW LB : list block) (lo : Z) (m : mem)
    (Σ1 : rts RT) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m1 f,
    ms' = MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 s1 (wz f) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m1 (seg_rom ctasegs)
    /\ mem_inv ctasegs m1 /\ stk ctasegs m1 lo (bv_unsigned sp) /\ wmono ctasegs m m1
    /\ agree_on (aclient_addr (OW ++ LB) (bv_unsigned sp)) m m1
    /\ @BnHeapA.AHEAP (push AR f k) Σ1 OW LB m1
    /\ (forall b, In b (OW ++ LB) -> off_fr f k b)
    /\ rt_credit RT Σ1 = rt_credit RT Σ - 1
    /\ fr_geo f k
    /\ (exists junk, rw_cells ctasegs m1 f [CB (Z.to_nat (fs_size k - 8)) junk])
    /\ (exists junk, rw_cells ctasegs m1 (shad f) [CB (Z.to_nat (fs_size k / 8)) junk]).

Lemma stack_malloc_cpsA : forall (k : nat)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (lo : Z),
  (k <= 4)%nat -> AHEAP Σ OW LB m ->
  stk ctasegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo + RT_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv ctasegs m -> tp = wz TP_A ->
  (length FR < FRAMES_MAX)%nat -> 1 <= rt_credit RT Σ ->
  cps ctasegs (ASTA RT Σ PMc (eq (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F (wz (e_stack_malloc_g k)) fc None m (seg_rom ctasegs))))
            (fun c => exists Σ1, ASTA RT Σ1 PMc (sm_postA k ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB lo m Σ1) c).
Proof.
  intros until lo. intros Hk HEAP ST CEIL LO SPT SP16 MI -> HLEN CRED.
  unfold MallocRep.wz in *.
  pose proof (AH_frames _ _ _ _ HEAP) as EFR.
  eapply cps_conseq; [ eapply (rc2_stack_malloc RT (@ar_RC2 AR) k Hk Σ PMc) with (lo := lo); try reflexivity | intros c Hc; exact Hc | ].
  - exact ar_PMc_fdfs.
  - exact ar_PMc_ms.
  - rewrite EFR. exact HLEN.
  - exact CRED.
  - exact (AH_art _ _ _ _ HEAP).
  - exact MI.
  - rewrite <- (Z_to_bv_bv_unsigned sp). eapply call_okA; [exact HEAP | exact ST | exact CEIL | exact LO | exact SPT | exact SP16].
  - intros c (Σ1 & f & Hc & EF1 & EL1 & ES1 & EC1 & F0 & F64 & FTOP). exists Σ1.
    eapply ASTA_conseq; [exact Hc|]. clear Hc.
    intros ms (m1 & RS & (ART1 & MI1 & WM1 & ST1) & PRES & W1 & W2).
    destruct RS as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F1 & fc1 & ->).
    destruct (AH_enter Σ Σ1 OW LB m m1 f k _ HEAP ART1 EF1 EL1 ES1 PRES W1 W2) as (HEAP1 & FRESH).
    unfold sm_postA, MallocRep.wz. do 16 eexists. exists m1, f. split; [reflexivity|].
    split; [exact MI1|]. split; [exact ST1|]. split; [exact WM1|].
    split; [eapply (AH_agree _ _ _ _ _ _ _ HEAP); rewrite <- EFR; exact PRES|].
    split; [exact HEAP1|]. split; [exact FRESH|]. split; [exact EC1|].
    split; [exact (@AH_fr_geo (push AR f k) Σ1 OW LB m1 f k HEAP1 (or_introl eq_refl))|].
    pose proof (fs_size_pos k) as (FS1 & _). destruct (fs_size_div8 k) as (_ & FS2).
    split; [exact (wr_at_rw_CB m1 f _ W1 ltac:(lia)) | exact (wr_at_rw_CB m1 (shad f) _ W2 ltac:(lia))].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition shcall_postA (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (Σ : rts RT) (OW LB : list block) (lo d n v : Z) (m : mem)
    : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m',
    ms' = MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom ctasegs)
    /\ mem_inv ctasegs m' /\ stk ctasegs m' lo (bv_unsigned sp) /\ AHEAP Σ OW LB m' /\ wmono ctasegs m m'
    /\ agree_on (fun a => (aclient_addr (OW ++ LB) (bv_unsigned sp) a \/ fr_addr a) /\ ~ (d <= a < d + n)) m m'
    /\ bytes_at ctasegs m' d (repeat (Z_to_bv 8 v) (Z.to_nat n)) /\ wr_at ctasegs m' d n.

Lemma set_shadow_cpsA : forall (v : Z)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (lo d n f : Z) (k : nat),
  In v set_shadow_vals -> In (f, k) FR -> AHEAP Σ OW LB m ->
  stk ctasegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo + RT_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv ctasegs m -> tp = wz TP_A ->
  shad f <= d -> d + n <= shad f + fs_size k / 8 -> 0 <= n < 2^20 ->
  (forall b, In b LB -> off_fr f k b) ->
  a0 = wz d -> a1 = wz n ->
  cps ctasegs (ASTA RT Σ PMc (eq (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F (wz (e_set_shadow v)) fc None m (seg_rom ctasegs))))
            (ASTA RT Σ PMc (shcall_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB lo d n v m)).
Proof.
  intros until k. intros Hv Hf HEAP ST CEIL LO SPT SP16 MI -> D1 D2 HN OFF -> ->.
  unfold MallocRep.wz in *.
  pose proof (AH_frames _ _ _ _ HEAP) as EFR.
  destruct (AH_fr_wr _ _ _ _ f k HEAP Hf) as (_ & (W0 & W1 & W2)).
  destruct (AH_fr_geo _ _ _ _ f k HEAP Hf) as (G1 & G2 & G3 & G4 & G5).
  eapply cps_conseq; [ eapply (rc_set_shadow RT (@ar_RC AR) v Hv Σ PMc) with (d := d) (n := n) (lo := lo); try reflexivity | intros c Hc; exact Hc | ].
  - exact ar_PMc_fdfs.
  - exact ar_PMc_ms.
  - exact Hv.
  - exact HN.
  - intros i Hi. rewrite EFR. exists f, k. split; [exact Hf|]. rewrite shad_fr_end. lia.
  - split; [lia|]. split; [lia|]. intros i Hi. replace (d + i) with (shad f + (d - shad f + i)) by lia. apply W2. lia.
  - exact (AH_art _ _ _ _ HEAP).
  - exact MI.
  - rewrite <- (Z_to_bv_bv_unsigned sp). eapply call_okA; [exact HEAP | exact ST | exact CEIL | exact LO | exact SPT | exact SP16].
  - intros c (v0 & Hc). eapply ASTA_conseq; [exact Hc|]. clear Hc.
    intros ms (m2 & RS & (ART2 & MI2 & WM2 & ST2) & PRES & BZ).
    destruct RS as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F1 & fc1 & ->).
    rewrite EFR in PRES.
    assert (AGX : agree_on (fun a => (aclient_addr (OW ++ LB) (bv_unsigned sp) a \/ fr_addr a) /\ ~ (d <= a < d + n)) m m2).
    { intros a Ha [[Hc|[Hc|Hc]] Hd]; apply PRES; unfold wa; rewrite unsigned_lit by lia;
        [exact (AH_aclient _ _ _ _ _ _ HEAP Hc) | exact Hd | right; right; right; left; exact Hc | exact Hd | right; right; right; right; exact Hc | exact Hd]. }
    unfold shcall_postA, MallocRep.wz. do 17 eexists. exists m2. split; [reflexivity|].
    split; [exact MI2|]. split; [exact ST2|].
    split.
    { apply (AH_same_pb Σ OW LB m m2 HEAP ART2 WM2). intros a Ha (b & i & Hb & PI & Hi & ->).
      apply AGX; [exact Ha|]. split; [right; right; exact (pb_in_shadow b i PI Hi)|].
      assert (B0 : 0 < blk_addr b) by (destruct PI as (f' & k' & Hf' & Q1 & Q2); destruct (AH_fr_range _ _ _ _ f' k' HEAP Hf') as (R1 & _); lia).
      pose proof (off_fr_shadow f k b i ltac:(clear - G2; Z.div_mod_to_equations; lia) ltac:(lia) (OFF b Hb) Hi) as SO. lia. }
    split; [exact WM2|]. split; [exact AGX|]. split; [exact BZ|].
    apply (wr_at_transport ctasegs m m2 d n); [| exact WM2]. split; [lia|]. split; [lia|]. intros i Hi.
    replace (d + i) with (shad f + (d - shad f + i)) by lia. apply W2. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma fr_consts : forall Σ OW LB m, AHEAP Σ OW LB m ->
  ro_cells ctasegs m g_GOT_shadow_offset_cell [C8 (Z_to_bv 64 g_shadow_memory_dynamic_address)]
  /\ ro_cells ctasegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)]
  /\ ro_cells ctasegs m g_GOT_detect_uar [C8 (Z_to_bv 64 g_detect_stack_use_after_return)]
  /\ ro_cells ctasegs m g_detect_stack_use_after_return [C4 (Z_to_bv 64 1)].
Proof.
  intros Σ OW LB m H. destruct (af_client_consts RT AF Σ m (AH_art _ _ _ _ H)) as (C1 & C2 & C3 & C4 & _). auto.
Qed.

End WithRT.
