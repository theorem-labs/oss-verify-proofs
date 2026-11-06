(** Helpers for the walk of check_csv in the UBSan image (U/Prog/check_csv.v; contract U/Prog/check_csv_c.v).
    The state at the loop head 0x148d8 (and at the tail 0x14994) of check_csv, its frame layout, the post, and the
    tactics the pass lemmas (U/Prog/ccsv_pass.v) and the tail (U/Prog/ccsv_tail.v) share.

    Frame (144 bytes at S - 144, S = the entry sp): [S-144, S-136) unused, d[8] at [S-136, S-128), want[40] at
    [S-128, S-88), ra and s0-s9 saved at [S-88, S) (s9 lowest, ra at S-8). At the loop head of pass i (a0 = i) the
    first n bytes of want hold csv_bytes (csv_prefix mask i) (n = t6), the rest of want and all of d hold junk. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes ZBridge Image.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import RateCfg RateCsv.
Import ListNotations.
Open Scope Z_scope.

(** memcmp of a list with itself. *)
(* from 25e3d17bdb50:proofs/libreac/fuzz_ctrl/lib/Prog/Seg/G03.v:24 (g03_memcmp) *)
Lemma ccsv_memcmp : forall l n, (n <= length l)%nat -> memcmp_model l l n = Some 0.
Proof.
  induction l as [|x l IH]; intros [|n] Hn; cbn in *; try reflexivity; try lia.
  rewrite Z.eqb_refl. apply IH. lia.
Qed.

(** ** Cells: merge a run of cells back into one byte block *)

Fixpoint take_cells (cs : list cell) (k : nat) : list cell * list cell :=
  match cs with
  | [] => ([], [])
  | c :: cs' => if Nat.eqb k 0 then ([], cs)
                else let '(a, b) := take_cells cs' (k - csize c) in (c :: a, b)
  end.

Lemma take_cells_app : forall cs k, fst (take_cells cs k) ++ snd (take_cells cs k) = cs.
Proof.
  induction cs as [|c cs IH]; intros k; cbn; [reflexivity|].
  destruct (Nat.eqb k 0); [reflexivity|].
  specialize (IH (k - csize c)%nat). destruct (take_cells cs (k - csize c)%nat) as [a b]. cbn in *. rewrite IH.
  reflexivity.
Qed.

(** The cells from byte k on that cover len bytes, as one CB cell. *)
Definition merge_at (cs : list cell) (k len : nat) : list cell :=
  let '(pre, r) := take_cells cs k in
  let '(mid, post) := take_cells r len in
  pre ++ CB (cells_size mid) (cells_bytes mid) :: post.

Lemma rw_cells_merge_at : forall m A cs k len, rw_cells rsegs m A cs -> rw_cells rsegs m A (merge_at cs k len).
Proof.
  intros m A cs k len H. unfold merge_at.
  pose proof (take_cells_app cs k) as E1. destruct (take_cells cs k) as [pre r]. cbn [fst snd] in E1.
  pose proof (take_cells_app r len) as E2. destruct (take_cells r len) as [mid post]. cbn [fst snd] in E2.
  apply rw_cells_merge. rewrite E2, E1. exact H.
Qed.

(** ** The loop-head state *)

(** want[40]: the prefix P (when not empty) and the junk after it. *)
Definition wcells (P : list Z) (wj : list byte) : list cell :=
  match P with
  | [] => [CB 40 wj]
  | _ :: _ => [CB (length P) (csv_bytes P); CB (40 - length P) wj]
  end.

(** The saved ra and s0-s9 at S-88 .. S. *)
Definition ccsv_saves (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 : word) : list cell :=
  [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(** Memory at a loop head: the frame (with want's prefix P), the stack below it, and the footprint so far. *)
Definition hd_mem (Sp lo : Z) (m0 m : word -> option byte) (P : list Z) (sv : list cell) : Prop :=
  exists j0 dj wj, rw_cells rsegs m (Sp + -144) (CB 8 j0 :: CB 8 dj :: wcells P wj ++ sv) /\
    stk rsegs m lo (Sp + -144) /\ munch [(Sp + -144, Sp)] m0 m /\ wmono rsegs m0 m /\ mem_inv rsegs m.

(** Registers at the loop head (pc 0x148d8, a0 = i) and at the tail (pc 0x14994, a0 = 3): the constants set up by
    0x14894 .. 0x148d4 (t1 = -40, t2 = 39, a2 = 3, a4 = 8, a5 = 10, a6 = d, a7 = 18, t0 = want, t3 = closed_list,
    t4 = 0x66666667, t5 = ','), s0 = buf, s1 = len, t6 = n; x18 .. x25 = s2 .. s9 hold junk. *)
Definition hd_st (pc i n Sp : Z) (ra gp tp s0 s1 a1 a3 x18 x19 x20 x21 x22 x23 x24 x25 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state :=
  MS (mkR ra (Z_to_bv 64 (Sp + -144)) gp tp (Z_to_bv 64 (Sp + -128)) (Z_to_bv 64 18446744073709551576)
          (Z_to_bv 64 39) s0 s1 (Z_to_bv 64 i) a1 (Z_to_bv 64 3) a3 (Z_to_bv 64 8) (Z_to_bv 64 10)
          (Z_to_bv 64 (Sp + -136)) (Z_to_bv 64 18) x18 x19 x20 x21 x22 x23 x24 x25 s10 s11 (Z_to_bv 64 67112)
          (Z_to_bv 64 1717986919) (Z_to_bv 64 44) (Z_to_bv 64 n))
     F (Z_to_bv 64 pc) fc None m (seg_rom rsegs).

(** The contract's post, with S = Sp. *)
Definition ccsv_post (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (Sp : Z) (F : bvmap 5 word)
    (fc : bv 32) (m0 : word -> option byte) (lo : Z) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = MS (mkR ra (Z_to_bv 64 Sp) gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    munch [(Sp + -144, Sp)] m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m' /\ stk rsegs m' lo Sp.

(** One pass of the loop from the head with a0 = i, t6 = n and want's prefix P, bit i of the mask = bit, to the
    state at pc' (the head again, or the tail after pass 2) with a0 = i', t6 = n', prefix P'. *)
Definition pass_spec (i n i' n' pc' : Z) (P P' : list Z) (bit : bool) : Prop :=
  forall (Q : machine_state -> Prop) (Sp lo : Z) (m0 m : word -> option byte)
         (ra gp tp s0 s1 a1 a3 x18 x19 x20 x21 x22 x23 x24 x25 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
         (sv : list cell),
    0 <= lo -> lo + 144 <= Sp -> Sp <= 2^64 ->
    Z.testbit (bv_unsigned a3) i = bit ->
    hd_mem Sp lo m0 m P sv ->
    (forall (m' : word -> option byte) (y18 y19 y20 y21 y22 y23 y24 y25 : word),
       hd_mem Sp lo m0 m' P' sv ->
       evt rsegs Q (hd_st pc' i' n' Sp ra gp tp s0 s1 a1 a3 y18 y19 y20 y21 y22 y23 y24 y25 s10 s11 F fc m')) ->
    evt rsegs Q (hd_st 0x148d8 i n Sp ra gp tp s0 s1 a1 a3 x18 x19 x20 x21 x22 x23 x24 x25 s10 s11 F fc m).

(** ** The bit test `srlw s2,a3,a0; andi s2,s2,1` *)

Lemma land1_b2z : forall x, Z.land x 1 = Z.b2z (Z.testbit x 0).
Proof.
  intros x. apply Z.bits_inj'. intros k Hk. rewrite Z.land_spec.
  destruct (Z.eq_dec k 0) as [->|Nk].
  - rewrite Z.b2z_bit0. change (Z.testbit 1 0) with true. apply andb_true_r.
  - assert (E1 : Z.testbit 1 k = false) by (apply Z.bits_above_log2; cbn; lia).
    rewrite E1, andb_false_r.
    destruct (Z.testbit x 0); cbn [Z.b2z]; [symmetry; exact E1 | symmetry; apply Z.testbit_0_l].
Qed.

Lemma ccsv_odd_mod : forall a k, 0 < k -> Z.odd (a mod 2 ^ k) = Z.odd a.
Proof. intros a k Hk. rewrite <- !Z.bit0_odd. apply Z.mod_pow2_bits_low. lia. Qed.

Lemma ccsv_bit : forall M i, 0 <= i < 32 ->
  Z.land (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (Z.shiftr (bv_wrap 32 M) (i mod 32))))) 1 = Z.b2z (Z.testbit M i).
Proof.
  intros M i Hi. rewrite (Z.mod_small i 32) by lia. rewrite unsigned_lit_wrap, land1_b2z. f_equal.
  rewrite Z.mod_pow2_bits_low by lia.
  remember (Z.shiftr (bv_wrap 32 M) i) as Y eqn:EY.
  change (bv_swrap 32 Y) with ((Y + 2^31) mod 2^32 - 2^31).
  rewrite Z.bit0_odd, Z.odd_sub, ccsv_odd_mod by lia. rewrite Z.odd_add.
  change (Z.odd (2^31)) with false. rewrite !xorb_false_r.
  rewrite <- Z.bit0_odd. subst Y. rewrite Z.shiftr_spec by lia.
  change (bv_wrap 32 M) with (M mod 2^32). rewrite Z.mod_pow2_bits_low by lia. reflexivity.
Qed.

(** ** From the head state of the tail to the tail's frame: want's 40 bytes and d merged into one block *)

Lemma ccsv_cells56 : forall m A j0 dj P wj sv, (length P <= 40)%nat ->
  rw_cells rsegs m A (CB 8 j0 :: CB 8 dj :: wcells P wj ++ sv) ->
  (exists j, rw_cells rsegs m A (CB 56 j :: sv)) /\ bytes_at rsegs m (A + 16) (csv_bytes P).
Proof.
  intros m A j0 dj P wj sv HP H. split.
  - pose proof (rw_cells_merge rsegs m A [] (CB 8 j0 :: CB 8 dj :: wcells P wj) sv H) as M.
    assert (Hs : cells_size (CB 8 j0 :: CB 8 dj :: wcells P wj) = 56%nat).
    { destruct P as [|z P']; [reflexivity|]. cbn [cells_size csize wcells]. cbn [length] in HP |- *. lia. }
    rewrite Hs in M. exists (cells_bytes (CB 8 j0 :: CB 8 dj :: wcells P wj)). exact M.
  - destruct H as [[Hwf Hb] _].
    cbn [cells_wf cell_wf] in Hwf. destruct Hwf as [L0 [Ld _]].
    cbn [cells_bytes cbytes] in Hb.
    apply bytes_at_app in Hb. destruct Hb as [_ Hb]. rewrite L0 in Hb.
    apply bytes_at_app in Hb. destruct Hb as [_ Hb]. rewrite Ld in Hb.
    replace (A + Z.of_nat 8 + Z.of_nat 8) with (A + 16) in Hb by lia.
    destruct P as [|x P'].
    + cbn [csv_bytes map]. apply bytes_at_nil. pose proof (bytes_at_bound _ _ _ _ Hb). lia.
    + cbn [wcells app cells_bytes cbytes] in Hb. apply bytes_at_app in Hb. exact (proj1 Hb).
Qed.

(** ** Tactics *)

(** A branch whose condition the context decides. *)
Ltac br := first [ if_false | if_true | idtac ].

(** A branch whose condition holds or fails by lia once each `bv_unsigned (Z_to_bv 64 z)` is z. *)
Ltac zbr :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      first [ replace c with true
                by (symmetry; unfold_cond; rewrite ?unsigned_lit by lia; fold_lit_ux; solve_cond_rec);
              cbv iota
            | replace c with false
                by (symmetry; unfold_cond; rewrite ?unsigned_lit by lia; fold_lit_ux; solve_cond_rec);
              cbv iota ]
  end.

(** The bit test at 0x148d8 .. 0x148e0, with B : Z.testbit (bv_unsigned a3) i = b. *)
Ltac bit_br B := rewrite ?ccsv_bit by lia; rewrite B; cbn [Z.b2z]; br.

(** A byte store of a literal: make the stored list a literal byte so the cell machinery takes it. *)
Ltac sbfix :=
  try lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) =>
      change (le1 (Z_to_bv 64 z)) with [Z_to_bv 8 z]; mem_after_store
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) =>
      change (Z_to_le_bytes 1 z) with [Z_to_bv 8 z]; mem_after_store
  end.

Ltac st1 := step; sbfix; br.

Ltac run_to pc :=
  repeat lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 pc) _ _ _ _) => fail
  | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => st1
  end.

(** Each literal word as its value in [0, 2^64). *)
Ltac norm_lits :=
  repeat match goal with
  | |- context [Z_to_bv 64 ?z] =>
      is_Zlit z;
      let z' := eval vm_compute in (z mod 2^64) in
      tryif constr_eq z z' then fail else
      replace (Z_to_bv 64 z) with (Z_to_bv 64 z') by (apply bv_eq; rewrite !Z_to_bv_unsigned; vm_compute; reflexivity)
  end.

(** The frame cells after a pass, merged back into hd_mem's shape: d at byte 8 and want's first n bytes at 16. *)
Ltac canon FR n :=
  apply (rw_cells_merge_at _ _ _ 8 8) in FR;
  cbn [merge_at take_cells cells_size cells_bytes csize cbytes Nat.eqb Nat.sub Nat.add app] in FR;
  apply (rw_cells_merge_at _ _ _ 16 n) in FR;
  cbn [merge_at take_cells cells_size cells_bytes csize cbytes Nat.eqb Nat.sub Nat.add app] in FR.

(** want's first bytes as csv_bytes P (a computation on literal bytes). *)
Ltac fix_want FR P :=
  lazymatch type of FR with
  | rw_cells _ _ _ (CB 8 _ :: CB 8 _ :: CB _ ?W :: _) =>
      replace W with (csv_bytes P) in FR by (vm_compute; reflexivity)
  end.

Ltac unfold_P H := unfold wcells, CSV_44K1, CSV_48K, CSV_96K in H; cbn [app length Nat.sub] in H.

(** At the next head: hd_mem for prefix P (n bytes) from the cells, then the continuation K. *)
Ltac close_pass K FR n P :=
  norm_lits; canon FR n; fix_want FR P;
  eapply K; unfold hd_mem; eexists _, _, _;
  split; [exact FR | split; [assumption | split; [assumption | split; assumption]]].
