(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase ADepot_iface ADepot ADepotKit ADepot_tabscan ARepInit_kit.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AS Require Import MainExport MainFactsAsan MainEntryAsan.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Lemma tab_image : forall i, TAB <= i < NUNIQ ->
  seg_rom bsegs (wa i) = Some (Z_to_bv 8 0) /\ forall m, m (wa i) = None -> wview bsegs m (wa i) <> None.
Proof.
  intros i Hi. unfold TAB, NUNIQ in Hi.
  assert (U : bv_unsigned (wa i) = i) by (apply wa_unsigned; lia).
  assert (FS : find_segment bsegs i 1 = Some Asan_segment_003).
  { rewrite a_find_segment_1 by lia.
    destruct (Z.leb_spec0 0x10000 i); destruct (Z.leb_spec0 (i + 1) 0x32000); cbn [andb]; try lia.
    destruct (Z.leb_spec0 0x32000 i); destruct (Z.leb_spec0 (i + 1) 0xc6000); cbn [andb]; try lia.
    destruct (Z.leb_spec0 0xc6000 i); destruct (Z.leb_spec0 (i + 1) 0xc9000); cbn [andb]; try lia.
    destruct (Z.leb_spec0 0xc9000 i); destruct (Z.leb_spec0 (i + 1) 0x625000); cbn [andb]; try lia. reflexivity. }
  assert (OFF : Z.to_N (i - Z.of_N (seg_base Asan_segment_003)) = (0xe8bd8 + Z.to_N (i - 0x1b1bd8))%N).
  { replace (Z.of_N (seg_base Asan_segment_003)) with 0xc9000 by (vm_compute; reflexivity). lia. }
  pose proof (tab_byte_at (0xe8bd8 + Z.to_N (i - 0x1b1bd8))%N ltac:(lia)) as B.
  split.
  - unfold seg_rom, memory_read. rewrite U. change (Z.of_N 1) with 1. rewrite FS.
    replace (seg_readable Asan_segment_003) with true by (vm_compute; reflexivity).
    rewrite OFF. change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes].
    rewrite B. reflexivity.
  - intros m Hm. unfold wview. rewrite Hm, U, FS.
    replace (seg_writable Asan_segment_003) with true by (vm_compute; reflexivity).
    rewrite OFF, B. discriminate.
Qed.

(* [comment removed for export] *)
Lemma tab_cell0 : forall m b, 0 <= b < 1048576 ->
  (forall i, TAB + 4 * b <= i < TAB + 4 * b + 4 -> m (wa i) = None) ->
  rw_cells bsegs m (TAB + 4 * b) [C4 (Z_to_bv 64 0)].
Proof.
  intros m b Hb Hnone. unfold TAB, NUNIQ in *.
  split; [split|].
  - cbn. split; [reflexivity| exact I].
  - split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi.
    assert (R : TAB <= 1776600 + 4 * b + Z.of_nat i < NUNIQ) by (unfold TAB, NUNIQ; lia).
    destruct (tab_image _ R) as [SR _].
    unfold mrd. rewrite Hnone by lia. rewrite SR.
    destruct i as [|[|[|[|i]]]]; try reflexivity. lia.
  - split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi.
    assert (R : TAB <= 1776600 + 4 * b + i < NUNIQ) by (unfold TAB, NUNIQ; lia).
    destruct (tab_image _ R) as [_ WV]. apply WV. apply Hnone. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition dp_pfact_eqb (f g : pfact) : bool :=
  match f, g with
  | PVar n lo hi, PVar n' lo' hi' => Nat.eqb n n' && Z.eqb lo lo' && Z.eqb hi hi'
  | PRange e lo hi, PRange e' lo' hi' => zexp_eqb e e' && Z.eqb lo lo' && Z.eqb hi hi'
  | PDisj a1 n1 a2 n2, PDisj a1' n1' a2' n2' => zexp_eqb a1 a1' && Z.eqb n1 n1' && zexp_eqb a2 a2' && Z.eqb n2 n2'
  | _, _ => false
  end.
Lemma dp_pfact_eqb_eq : forall f g, dp_pfact_eqb f g = true -> f = g.
Proof.
  intros f g H. destruct f, g; cbn in H; try discriminate;
    repeat (apply andb_prop in H as [H ?X]);
    repeat match goal with
    | K : zexp_eqb _ _ = true |- _ => apply zexp_eqb_eq in K
    | K : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in K
    | K : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in K
    end; subst; reflexivity.
Qed.
Lemma dp_pfact_find : forall V (l : list pfact) f,
  Forall (pfact_ok V) l -> existsb (dp_pfact_eqb f) l = true -> pfact_ok V f.
Proof.
  intros V l f HF HE. apply existsb_exists in HE as (g & Hin & Hg). apply dp_pfact_eqb_eq in Hg. subst g.
  exact (proj1 (Forall_forall _ _) HF f Hin).
Qed.

End CANSEC1.
Local Ltac mf V m HM f H := pose proof (mfact_find bsegs V m _ f HM ltac:(vm_compute; reflexivity)) as H; cbn [mfact_ok zv cellw] in H.
Local Ltac pf V HP f H := pose proof (dp_pfact_find V _ f HP ltac:(vm_compute; reflexivity)) as H; cbn [pfact_ok zv] in H.

(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT}.
Lemma stk_of_zero : forall m a n, 0 <= a ->
  (forall i, 0 <= i < n -> m (wa (a + i)) = Some (Z_to_bv 8 0)) -> wr_at bsegs m a n -> stk bsegs m a (a + n).
Proof.
  intros m a n Ha Z0 (W1 & W2 & W3). split; [lia|]. split; [lia|]. intros x Hx.
  replace x with (a + (x - a)) by lia. split; [apply W3; lia|].
  exists (Z_to_bv 8 0). unfold mrd. rewrite Z0 by lia. reflexivity.
Qed.

Lemma wr_at_sub' : forall m a n a' n', wr_at bsegs m a n -> 0 <= a' -> a <= a' -> a' + n' <= a + n -> wr_at bsegs m a' n'.
Proof.
  intros m a n a' n' (W1 & W2 & W3) H0 H1 H2. split; [lia|]. split; [lia|]. intros i Hi.
  replace (a' + i) with (a + (a' - a + i)) by lia. apply W3. lia.
Qed.

(* [comment removed for export] *)
Lemma BUD_le : forall U hs n, Forall (fun u => (length u <= 254)%nat) U -> BUD U hs n <= 255 * Z.of_nat (length U).
Proof.
  induction U as [|u U IH]; intros hs n F; cbn [BUD length]; [lia|].
  inversion F; subst. specialize (IH hs n ltac:(assumption)). unfold ucost. destruct (has_hash hs n (hashU u)); lia.
Qed.
Lemma CNT_le : forall U hs n, CNT U hs n <= Z.of_nat (length U).
Proof.
  induction U as [|u U IH]; intros hs n; cbn [CNT length]; [lia|].
  specialize (IH hs n). destruct (has_hash hs n (hashU u)); lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition hw0 (w : bool) : Z := if w then 15947302641947485344 else 3271259264866474265.   (* [comment removed for export] *)
Definition bw0 (w : bool) : Z := if w then 894112 else 153881.                              (* [comment removed for export] *)
Definition tf0 (w : bool) : Z := if w then 3 else 2.
Definition D0 (w : bool) : dstate :=
  mkD 1 (fun b => if b =? bw0 w then 1 else 0) (fun _ => hw0 w) (fun _ => 0) (fun _ => 1) (tf0 w).

Lemma bw0_bkt : forall w, bkt (hw0 w) = bw0 w.
Proof. intros [|]; reflexivity. Qed.

Lemma D0_wf : forall w U, (length U <= 4096)%nat -> Forall (fun u => (length u <= 254)%nat) U -> dwf U (D0 w).
Proof.
  intros w U LU FU. pose proof (BUD_le U (fun _ => hw0 w) 1 FU) as B1. pose proof (CNT_le U (fun _ => hw0 w) 1) as C1.
  assert (HW : 0 <= hw0 w < 2^64) by (destruct w; cbn; lia).
  assert (TF : 0 <= tf0 w <= 3) by (destruct w; cbn; lia).
  unfold dwf, D0; cbn [dN dhd dhs dlk dsid dtf].
  split; [lia|]. split. { intros i Hi. lia. }
  split. { intros b Hb. destruct (Z.eqb_spec b (bw0 w)); [| lia]. split; [lia|]. intros _. rewrite bw0_bkt. lia. }
  split. { intros i Hi. split; [exact HW|]. split; [lia|]. intros C. exfalso. exact (C eq_refl). }
  split. { intros i Hi. rewrite bw0_bkt, Z.eqb_refl. assert (i = 1) by lia. subst i. cbn. left. reflexivity. }
  change (Z.to_nat 1) with 1%nat. lia.
Qed.

Theorem adepot_init : forall (V : nat -> Z) (w : bool) (U : list (list Z)) (m : amem),
  Forall (mfact_ok bsegs V m) both_mem_facts ->
  Forall (mfact_ok bsegs V m) (both_mem_facts_w w) ->
  Forall (pfact_ok V) both_pure_facts ->
  (length U <= 4096)%nat -> Forall (fun u => (length u <= 254)%nat) U ->
  32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat - 8388608 = ATOP ->      (* [comment removed for export] *)
  ADEPOTi (mkALayout (LV V) w U) m.
Proof.
  intros V w U m HM HMW HP LU FU HAT.
  set (L := mkALayout (LV V) w U).
  assert (EN : al_nodes L = 4096 * V 453%nat) by reflexivity.
  assert (ES : al_store L = 4096 * V 454%nat) by reflexivity.
  assert (EU : al_U L = U) by reflexivity.
  exists (D0 w). split; [rewrite EU; apply D0_wf; assumption|].
  (* [comment removed for export] *)
  pf V HP (PVar 453 1573 34359736064) P469. pf V HP (PVar 454 1573 34359734272) P470.
  pf V HP (PVar 0 4294901760 4294967295) P0. pf V HP (PVar 6 0 255) P6. pf V HP (PVar 10 0 7) P10.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 453)) 1048576 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936) DW469.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 454)) 8388608 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936) DW470.
  pf V HP (PDisj (ZMul (ZLit 4096) (ZV 453)) 1048576 (ZMul (ZLit 4096) (ZV 454)) 8388608) D56.
  split.
  2:{ unfold dlayout. rewrite EN, ES. unfold ABase.AIMG_HI. repeat split; try (clear - P469 P470 P0 P6 P10 DW469 DW470 D56 HAT; lia).
      all: rewrite Z.mul_comm; apply Z_mod_mult. }
  clear DW469 DW470.
  (* [comment removed for export] *)
  mf V m HM (MCell (ZLit 1711064) 8 (ZMul (ZLit 4096) (ZV 454))) CPTR.
  mf V m HM (MCell (ZLit 5970904) 4 (ZLit 1)) CNU.
  mf V m HM (MCell (ZLit 5970920) 8 (ZMul (ZLit 4096) (ZV 453))) CMAP.
  mf V m HM (MCell (ZAdd (ZMul (ZLit 4096) (ZV 453)) (ZLit 24)) 4 (ZLit 0)) CN24.
  mf V m HM (MCell (ZAdd (ZMul (ZLit 4096) (ZV 453)) (ZLit 28)) 4 (ZLit 1)) CN28.
  mf V m HM (MZero (ZAdd (ZMul (ZLit 4096) (ZV 453)) (ZLit 32)) 1048544) ZN.
  mf V m HM (MWr (ZMul (ZLit 4096) (ZV 453)) 1048576) WN.
  mf V m HM (MWr (ZMul (ZLit 4096) (ZV 454)) 8388608) WS.
  mf V m HM (MCell (ZAdd (ZMul (ZLit 4096) (ZV 454)) (ZLit 8)) 8 (ZLit 265756)) CS8.
  (* [comment removed for export] *)
  assert (WF : rw_cells bsegs m 1711048 [C8 (Z_to_bv 64 (tf0 w))]
            /\ rw_cells bsegs m 1711072 [C4 (Z_to_bv 64 (tf0 w))]
            /\ rw_cells bsegs m (1776600 + 4 * bw0 w) [C4 (Z_to_bv 64 1)]
            /\ (forall i, 1711080 <= i < 1776600 + 4 * bw0 w -> m (wa i) = None)
            /\ (forall i, 1776600 + 4 * bw0 w + 4 <= i < 5970904 -> m (wa i) = None)
            /\ rw_cells bsegs m (4096 * V 453%nat + 16) [C8 (Z_to_bv 64 (hw0 w))]
            /\ rw_cells bsegs m (4096 * V 454%nat) [C8 (Z_to_bv 64 (if w then 2 else 1))]
            /\ stk bsegs m (4096 * V 454%nat + 16) (4096 * V 454%nat + 8388608)).
  { destruct w; cbn [tf0 bw0 hw0] in *; unfold both_mem_facts_w in HMW.
    - mf V m HMW (MCell (ZLit 1711048) 8 (ZLit 3)) F1. mf V m HMW (MCell (ZLit 1711072) 4 (ZLit 3)) F2.
      mf V m HMW (MCell (ZLit 5353048) 4 (ZLit 1)) F3. mf V m HMW (MImg 1711080 5353048) F4. mf V m HMW (MImg 5353052 5970904) F5.
      mf V m HMW (MCell (ZAdd (ZMul (ZLit 4096) (ZV 453)) (ZLit 16)) 8 (ZLit 15947302641947485344)) F6.   (* [comment removed for export] *)
      mf V m HMW (MCell (ZMul (ZLit 4096) (ZV 454)) 8 (ZLit 2)) F7.
      mf V m HMW (MCell (ZAdd (ZMul (ZLit 4096) (ZV 454)) (ZLit 16)) 8 (ZLit 270700)) F8.
      mf V m HMW (MZero (ZAdd (ZMul (ZLit 4096) (ZV 454)) (ZLit 24)) 8388584) F9.
      refine (conj F1 (conj F2 (conj F3 (conj F4 (conj F5 (conj F6 (conj F7 _))))))).
      apply (stk_merge bsegs m _ (4096 * V 454%nat + 24)); [| | lia].
      + pose proof (stk_of_rw_cells bsegs m _ _ F8) as K. cbn [cells_size csize Nat.add] in K.
        replace (4096 * V 454%nat + 16 + Z.of_nat 8) with (4096 * V 454%nat + 24) in K by lia. exact K.
      + replace (4096 * V 454%nat + 8388608) with (4096 * V 454%nat + 24 + 8388584) by lia.
        apply stk_of_zero; [lia | exact F9 |]. eapply wr_at_sub'; [exact WS | lia | lia | lia].
    - mf V m HMW (MCell (ZLit 1711048) 8 (ZLit 2)) F1. mf V m HMW (MCell (ZLit 1711072) 4 (ZLit 2)) F2.
      mf V m HMW (MCell (ZLit 2392124) 4 (ZLit 1)) F3. mf V m HMW (MImg 1711080 2392124) F4. mf V m HMW (MImg 2392128 5970904) F5.
      mf V m HMW (MCell (ZAdd (ZMul (ZLit 4096) (ZV 453)) (ZLit 16)) 8 (ZLit 3271259264866474265)) F6.   (* [comment removed for export] *)
      mf V m HMW (MCell (ZMul (ZLit 4096) (ZV 454)) 8 (ZLit 1)) F7.
      mf V m HMW (MZero (ZAdd (ZMul (ZLit 4096) (ZV 454)) (ZLit 16)) 8388592) F9.
      refine (conj F1 (conj F2 (conj F3 (conj F4 (conj F5 (conj F6 (conj F7 _))))))).
      replace (4096 * V 454%nat + 8388608) with (4096 * V 454%nat + 16 + 8388592) by lia.
      apply stk_of_zero; [lia | exact F9 |]. eapply wr_at_sub'; [exact WS | lia | lia | lia]. }
  destruct WF as (CTF & CST & CBK & IM1 & IM2 & CN16 & CS0 & SKS16).
  unfold dcells, D0; cbn [dN dhd dhs dlk dsid dtf]. rewrite EN, ES. unfold SSTF, SSPTR, SSST, NUNIQ, MAP1.
  split; [exact CTF|]. split; [exact CPTR|]. split; [exact CST|]. split; [exact CNU|]. split; [exact CMAP|].
  split.
  { intros b Hb. destruct (Z.eqb_spec b (bw0 w)) as [->|NE]; [exact CBK|].
    apply tab_cell0; [exact Hb|]. unfold TAB. intros i Hi.
    assert (BW : 0 <= bw0 w < 1048576) by (destruct w; cbn; lia).
    destruct (Z.lt_ge_cases b (bw0 w)); [apply IM1; lia | apply IM2; lia]. }
  split.
  { intros i Hi. assert (i = 1) by lia. subst i.
    apply (proj2 (rw_cells_app bsegs m _ [_] _)). split; [exact CN16|]. cbn [cells_size csize Nat.add].
    apply (proj2 (rw_cells_app bsegs m _ [_] [_])). cbn [cells_size csize Nat.add]. split.
    - replace (4096 * V 453%nat + 16 * 1 + Z.of_nat 8) with (4096 * V 453%nat + 24) by lia. exact CN24.
    - replace (4096 * V 453%nat + 16 * 1 + Z.of_nat 8 + Z.of_nat 4) with (4096 * V 453%nat + 28) by lia. exact CN28. }
  split.
  { replace (4096 * V 453%nat + 1048576) with (4096 * V 453%nat + 32 + 1048544) by lia.
    replace (4096 * V 453%nat + 16 * (1 + 1)) with (4096 * V 453%nat + 32) by lia.
    apply stk_of_zero; [lia | exact ZN |]. eapply wr_at_sub'; [exact WN | lia | lia | lia]. }
  apply (stk_merge bsegs m _ (4096 * V 454%nat + 8)); [| | lia].
  { pose proof (stk_of_rw_cells bsegs m _ _ CS0) as K. cbn [cells_size csize Nat.add] in K.
    replace (4096 * V 454%nat + Z.of_nat 8) with (4096 * V 454%nat + 8) in K by lia. exact K. }
  apply (stk_merge bsegs m _ (4096 * V 454%nat + 16)); [| exact SKS16 | lia].
  pose proof (stk_of_rw_cells bsegs m _ _ CS8) as K. cbn [cells_size csize Nat.add] in K.
  replace (4096 * V 454%nat + 8 + Z.of_nat 8) with (4096 * V 454%nat + 16) in K by lia. exact K.
Qed.
End CANSEC2.
