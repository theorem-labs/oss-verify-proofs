(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan ValProofs MemProofs StepSoundBase StepSoundMem PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib DefsA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require Import CtrFX.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan CtrLib.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module Pool.

Definition POOL_ID : int := 7%uint63.

Record pent := PE { pe_g : int; pe_i : int; pe_w : int; pe_v : w64 }.
Definition pe_addr (e : pent) : int := PrimInt63.add (PrimInt63.lsl (pe_g e) 3%uint63) (pe_i e).

Section WithBase.
Variable FL : int.
Definition HB : int := PrimInt63.add FL 16%uint63.
Definition gk (a : int) : int := PrimInt63.lsr a 3%uint63.

Definition tbl (s : nat) : list pent :=
  match s with
  | 0%nat => [PE (gk FL) 0%uint63 8%uint63 wzero]
  | 1%nat => [PE (gk FL) 0%uint63 8%uint63 (wlit (PrimInt63.add HB 12%uint63));
              PE (gk (PrimInt63.add HB 8%uint63)) 4%uint63 4%uint63 (wlit 8192128%uint63)]
  | _ => [PE (gk FL) 0%uint63 8%uint63 (wlit (PrimInt63.add HB 204%uint63));
          PE (gk (PrimInt63.add HB 200%uint63)) 4%uint63 4%uint63 (wlit 5046275%uint63);
          PE (gk (PrimInt63.add HB 8%uint63)) 4%uint63 4%uint63 (wlit 3145856%uint63)]
  end.
Definition NSTATES : nat := 3%nat.

Definition NPARK : nat := 3%nat.
Definition ptbl (l : nat) : list pent :=
  match l with
  | 0%nat => [PE (gk FL) 0%uint63 8%uint63 (wlit (PrimInt63.add HB 12%uint63));
              PE (gk (PrimInt63.add HB 8%uint63)) 4%uint63 4%uint63 (wlit 5767296%uint63)]
  | 1%nat => [PE (gk FL) 0%uint63 8%uint63 (wlit (PrimInt63.add HB 204%uint63));
              PE (gk (PrimInt63.add HB 200%uint63)) 4%uint63 4%uint63 (wlit 2621443%uint63);
              PE (gk (PrimInt63.add HB 8%uint63)) 4%uint63 4%uint63 (wlit 3145856%uint63)]
  | _ => [PE (gk FL) 0%uint63 8%uint63 (wlit (PrimInt63.add HB 12%uint63));
          PE (gk (PrimInt63.add HB 200%uint63)) 4%uint63 4%uint63 (wlit 2621440%uint63);
          PE (gk (PrimInt63.add HB 8%uint63)) 4%uint63 4%uint63 (wlit 3145856%uint63)]
  end.

Definition iv_fl : int * int := (FL, PrimInt63.add FL 8%uint63).
Definition iv_hb : int * int := (HB, PrimInt63.add HB 512%uint63).
Definition iv_eqb (a b : int * int) : bool := PrimInt63.eqb (fst a) (fst b) && PrimInt63.eqb (snd a) (snd b).
Definition unpriv (priv : list (int * int)) : list (int * int) :=
  List.filter (fun iv => negb (iv_eqb iv iv_fl || iv_eqb iv iv_hb)) priv.
Definition priv_ok (priv : list (int * int)) : bool :=
  existsb (iv_eqb iv_fl) priv && existsb (iv_eqb iv_hb) priv
  && negb (in_priv_b (unpriv priv) FL 8%uint63) && negb (in_priv_b (unpriv priv) HB 512%uint63).

Definition iv_p12 : int * int := (PrimInt63.add HB 8%uint63, PrimInt63.add HB 16%uint63).
Definition iv_p204 : int * int := (PrimInt63.add HB 200%uint63, PrimInt63.add HB 208%uint63).
Definition is_park_iv (iv : int * int) : bool := iv_eqb iv iv_fl || iv_eqb iv iv_p12 || iv_eqb iv iv_p204.
Definition unpriv3 (priv : list (int * int)) : list (int * int) := List.filter (fun iv => negb (is_park_iv iv)) priv.
Definition priv3_ok (priv : list (int * int)) : bool :=
  negb (in_priv_b (unpriv3 priv) FL 8%uint63) && negb (in_priv_b (unpriv3 priv) (PrimInt63.add HB 8%uint63) 8%uint63)
  && negb (in_priv_b (unpriv3 priv) (PrimInt63.add HB 200%uint63) 8%uint63).

Definition dirty_pool (r : region) : region :=
  Region (rg_lo r) (rg_hi r) (rg_w r) (rg_bg r) (Mem.dirty_range (gk HB) 64 (Mem.dirty_range (gk FL) 1 (rg_cells r))).
Definition mat1 (r : region) (e : pent) : region :=
  Region (rg_lo r) (rg_hi r) (rg_w r) (rg_bg r) (IMap.add (pe_g e) (Gran true [Cell (pe_i e) (pe_w e) (VL (pe_v e))]) (rg_cells r)).
Definition mat (es : list pent) (r : region) : region := fold_left mat1 es r.

Definition set_r0 (st : sstate) (r : region) : IMap.t region := IMap.add 0%uint63 r (s_regs st).

Definition gnext (g : int) : int := PrimInt63.add g 1%uint63.
Definition strip3 (r : region) : region :=
  Region (rg_lo r) (rg_hi r) (rg_w r) (rg_bg r)
         (IMap.remove_range (gk FL) (gnext (gk FL))
            (IMap.remove_range (gk (PrimInt63.add HB 8%uint63)) (gnext (gk (PrimInt63.add HB 8%uint63)))
               (IMap.remove_range (gk (PrimInt63.add HB 200%uint63)) (gnext (gk (PrimInt63.add HB 200%uint63))) (rg_cells r)))).
Definition dirty3 (r : region) : region :=
  Region (rg_lo r) (rg_hi r) (rg_w r) (rg_bg r)
         (Mem.dirty_range (gk FL) 1 (Mem.dirty_range (gk (PrimInt63.add HB 8%uint63)) 1 (Mem.dirty_range (gk (PrimInt63.add HB 200%uint63)) 1 (rg_cells r)))).
Definition park_sel (l : nat) : w64 := wlit (PrimInt63.add 4%uint63 (Uint63.of_Z (Z.of_nat l))).
Definition park_st (st : sstate) (r0 : region) (l : nat) : sstate :=
  SS (s_pc st) (s_rf st) (s_ff st) (s_resv st) (set_r0 st (strip3 r0)) (s_facts st)
     (set_op POOL_ID [VL (park_sel l)] (s_ops st)) (iv_fl :: iv_p12 :: iv_p204 :: s_priv st) (s_next st).

Definition OPEN_MARK : w64 := wlit 3%uint63.
Definition open_st (st : sstate) (r0 : region) (s : nat) : sstate :=
  SS (s_pc st) (s_rf st) (s_ff st) (s_resv st) (set_r0 st (mat (tbl s) (dirty_pool r0))) (s_facts st)
     (set_op POOL_ID [VL OPEN_MARK] (s_ops st)) (unpriv (s_priv st)) (s_next st).

Definition sel_cases (fs : list fact) (sel : sv) : option (list nat) :=
  match sel with
  | VL w => if wltu w (wlit 3%uint63) then Some [Z.to_nat (w2Z w)] else None
  | _ => match decide_ltu fs sel (VL (wlit 3%uint63)) with
         | Some true => Some [0%nat; 1%nat; 2%nat]
         | _ => None
         end
  end.

Section WithSegs.
Variable segs : list Segment.

Definition pool_in_image : bool :=
  Mem.abs_writable segs (to_Z FL) 8 && Mem.abs_writable segs (to_Z HB) 512.

Definition open_apply (st : sstate) : option (list sstate) :=
  match find_op POOL_ID (s_ops st), IMap.find 0%uint63 (s_regs st) with
  | Some [sel], Some r0 =>
      if priv_ok (s_priv st) && Nat.eqb (CtrA.count_op POOL_ID (s_ops st)) 1%nat && pool_in_image
      then match sel_cases (s_facts st) sel with Some ss => Some (map (open_st st r0) ss) | None => None end
      else None
  | _, _ => None
  end.

Definition pent_matches (st : sstate) (e : pent) : bool :=
  match do_load segs st (VL (wlit (pe_addr e))) (pe_w e) false with
  | inl (Some (VL v)) => weqb v (pe_v e)
  | _ => false
  end.
Definition tbl_matches (st : sstate) (s : nat) : bool := forallb (pent_matches st) (tbl s).

Fixpoint first_state (st : sstate) (n : nat) (s : nat) : option nat :=
  match n with
  | 0%nat => None
  | S n' => if tbl_matches st s then Some s else first_state st n' (S s)
  end.

Definition strip_pool (r : region) : region :=
  Region (rg_lo r) (rg_hi r) (rg_w r) (rg_bg r)
         (IMap.remove_range (gk HB) (PrimInt63.add (gk HB) 64%uint63)
            (IMap.remove_range (gk FL) (PrimInt63.add (gk FL) 1%uint63) (rg_cells r))).
Definition close_st (st : sstate) (r0 : region) (s : nat) : sstate :=
  SS (s_pc st) (s_rf st) (s_ff st) (s_resv st) (set_r0 st (strip_pool r0)) (s_facts st)
     (set_op POOL_ID [VL (wlit (Uint63.of_Z (Z.of_nat s)))] (s_ops st)) (iv_fl :: iv_hb :: s_priv st) (s_next st).

Definition close_apply (st : sstate) : option (list sstate) :=
  match find_op POOL_ID (s_ops st), IMap.find 0%uint63 (s_regs st) with
  | Some [VL w], Some r0 =>
      if weqb w OPEN_MARK && Nat.eqb (CtrA.count_op POOL_ID (s_ops st)) 1%nat && pool_in_image
      then match first_state st NSTATES 0%nat with Some s => Some [close_st st r0 s] | None => None end
      else None
  | _, _ => None
  end.

Definition unpark_st (st : sstate) (r0 : region) (l : nat) : sstate :=
  SS (s_pc st) (s_rf st) (s_ff st) (s_resv st) (set_r0 st (mat (ptbl l) (dirty3 r0))) (s_facts st)
     (set_op POOL_ID [VL OPEN_MARK] (s_ops st)) (unpriv3 (s_priv st)) (s_next st).
Definition ptbl_matches (st : sstate) (l : nat) : bool := forallb (pent_matches st) (ptbl l).
Fixpoint first_layout (st : sstate) (n : nat) (l : nat) : option nat :=
  match n with
  | 0%nat => None
  | S n' => if ptbl_matches st l then Some l else first_layout st n' (S l)
  end.
Definition park_apply (st : sstate) : option (list sstate) :=
  match find_op POOL_ID (s_ops st), IMap.find 0%uint63 (s_regs st) with
  | Some [VL w], Some r0 =>
      if weqb w OPEN_MARK && Nat.eqb (CtrA.count_op POOL_ID (s_ops st)) 1%nat && pool_in_image
      then match first_layout st NPARK 0%nat with Some l => Some [park_st st r0 l] | None => None end
      else None
  | _, _ => None
  end.

Definition park_cases (fs : list fact) (sel : sv) : option (list nat) :=
  let b := sv_bounds fs sel in
  let lo := fst b in let hi := snd b in
  if negb (wt lo) && negb (wt hi) && PrimInt63.leb 4%uint63 (wl lo) && PrimInt63.leb (wl lo) (wl hi) && PrimInt63.ltb (wl hi) 7%uint63
  then Some (List.seq (Z.to_nat (to_Z (wl lo) - 4)) (Z.to_nat (to_Z (wl hi) - to_Z (wl lo) + 1)))
  else None.
Definition unpark_apply (st : sstate) : option (list sstate) :=
  match find_op POOL_ID (s_ops st), IMap.find 0%uint63 (s_regs st) with
  | Some [sel], Some r0 =>
      if priv3_ok (s_priv st) && Nat.eqb (CtrA.count_op POOL_ID (s_ops st)) 1%nat && pool_in_image
      then match park_cases (s_facts st) sel with Some ls => Some (map (unpark_st st r0) ls) | None => None end
      else None
  | _, _ => None
  end.

Definition open_c (pc : int) : contract := Contract pc open_apply.
Definition park_c (pc : int) : contract := Contract pc park_apply.
Definition unpark_c (pc : int) : contract := Contract pc unpark_apply.
Definition close_c (pc : int) : contract := Contract pc close_apply.
End WithSegs.

Section Meaning.
Variable segs : list Segment.
Definition pent_holds (m : word -> option byte) (e : pent) : Prop :=
  forall i, 0 <= i < to_Z (pe_w e) -> rb segs m (to_Z (pe_addr e) + i) = Some (byte_of (wbv (pe_v e)) i).
Definition pool_holds (args : list word) (m : word -> option byte) (model : Model) : Prop :=
  match args with
  | [sel] => bv_unsigned sel = 3 \/
             (exists s : nat, bv_unsigned sel = Z.of_nat s /\ (s < NSTATES)%nat /\ Forall (pent_holds m) (tbl s)) \/
             (exists l : nat, bv_unsigned sel = 4 + Z.of_nat l /\ (l < NPARK)%nat /\ Forall (pent_holds m) (ptbl l))
  | _ => False
  end.
Definition pool_fp (args : list word) : list (Z * Z) :=
  match args with
  | [sel] => if Z.eqb (bv_unsigned sel) 3 then []
             else if Z.ltb (bv_unsigned sel) 3 then [(to_Z FL, to_Z FL + 8); (to_Z HB, to_Z HB + 512)]
             else [(to_Z FL, to_Z FL + 8); (to_Z HB + 8, to_Z HB + 16); (to_Z HB + 200, to_Z HB + 208)]
  | _ => []
  end.
End Meaning.
End WithBase.
End Pool.

Import Pool.

Module PoolSnd.
Section Regions.
Variable segs : list Segment.

Lemma region_ok_priv_based : forall priv priv' E m k r,
  PrimInt63.eqb k 0%uint63 = false -> region_ok segs priv E m k r -> region_ok segs priv' E m k r.
Proof.
  intros priv priv' E m k r Hk [Rbst Rrange Rvalid Rcells Rin Rbg]. constructor; try assumption.
  - intros g gr c i Hf Hc Hi. pose proof (Rin g gr c i Hf Hc Hi) as [P1 P2]. split; [exact P1|]. intros K. rewrite K in Hk. discriminate.
  - intros o H1 H2 U. apply Rbg; [exact H1| | exact U]. intros K. rewrite K in Hk. discriminate.
Qed.

Lemma region0_priv_change : forall priv priv' E m r,
  region_ok segs priv E m 0%uint63 r ->
  (forall g gr c i, IMap.find g (rg_cells r) = Some gr -> In c (g_cells gr) -> 0 <= i < to_Z (c_w c) ->
     ~ in_priv priv' (8 * keyZ g + to_Z (c_idx c) + i)) ->
  (forall o, in_priv priv o -> ~ in_priv priv' o ->
     exists g gr, keyZ g = o / 8 /\ IMap.find g (rg_cells r) = Some gr /\ g_dirty gr = true) ->
  region_ok segs priv' E m 0%uint63 r.
Proof.
  intros priv priv' E m r [Rbst Rrange Rvalid Rcells Rin Rbg] PUB DIRTY. constructor; try assumption.
  - intros g gr c i Hf Hc Hi. pose proof (Rin g gr c i Hf Hc Hi) as [P1 P2]. split; [exact P1|].
    intros K. destruct (P2 K) as (Q1 & Q2 & Q3). split; [exact Q1|]. split; [exact Q2|]. apply (PUB g gr c i Hf Hc Hi).
  - intros o H1 H2 U. apply Rbg; [exact H1| | exact U]. intros K. destruct (H2 K) as (Q1 & Q2 & Q3).
    split; [exact Q1|]. split; [exact Q2|]. intros IP.
    destruct (DIRTY o IP Q3) as (g & gr & Hg & Hf & Hd).
    destruct (U g gr Hg Hf) as [D _]. rewrite Hd in D. discriminate.
Qed.

Lemma mat1_sound : forall priv E m r g idx w v,
  ev E 0%uint63 = Z_to_bv 64 0 ->
  region_ok segs priv E m 0%uint63 r ->
  IMap.find g (rg_cells r) = Some (Gran true []) ->
  0 <= to_Z idx -> 0 < to_Z w -> to_Z idx + to_Z w <= 8 ->
  (forall i, 0 <= i < to_Z w -> rb segs m (8 * keyZ g + to_Z idx + i) = Some (byte_of (wbv v) i)) ->
  (forall i, 0 <= i < to_Z w -> let o := 8 * keyZ g + to_Z idx + i in
      0 <= o < two63 / 2 /\ (exists seg, find_segment segs o 1 = Some seg) /\ ~ in_priv priv o) ->
  region_ok segs priv E m 0%uint63 (mat1 r (PE g idx w v))
  /\ (forall g', g' <> g -> IMap.find g' (rg_cells (mat1 r (PE g idx w v))) = IMap.find g' (rg_cells r))
  /\ IMap.find g (rg_cells (mat1 r (PE g idx w v))) = Some (Gran true [Cell idx w (VL v)]).
Proof.
  intros priv E m r g idx w v Hz RO Hg Hi Hw Hiw BY IN.
  pose proof RO as [Rbst Rrange Rvalid Rcells Rin Rbg].
  assert (E0 : bv_unsigned (ev E 0%uint63) = 0) by (rewrite Hz; reflexivity).
  assert (FO : forall g', g' <> g -> IMap.find g' (rg_cells (mat1 r (PE g idx w v))) = IMap.find g' (rg_cells r)).
  { intros g' Hne. unfold mat1. cbn [rg_cells pe_g pe_i pe_w pe_v]. apply IMap.find_add_other; [exact Rbst| congruence]. }
  assert (FS : IMap.find g (rg_cells (mat1 r (PE g idx w v))) = Some (Gran true [Cell idx w (VL v)])).
  { unfold mat1. cbn [rg_cells pe_g pe_i pe_w pe_v]. apply IMap.find_add_same. exact Rbst. }
  split; [| split; [exact FO| exact FS]].
  assert (CASE : forall g' gr', IMap.find g' (rg_cells (mat1 r (PE g idx w v))) = Some gr' ->
            (g' = g /\ gr' = Gran true [Cell idx w (VL v)]) \/ (g' <> g /\ IMap.find g' (rg_cells r) = Some gr')).
  { intros g' gr' Hf. destruct (Uint63.eqb g' g) eqn:EQ.
    - apply Uint63.eqb_correct in EQ. subst g'. rewrite FS in Hf. injection Hf as <-. left. auto.
    - apply Uint63.eqb_false_spec in EQ. right. rewrite FO in Hf by exact EQ. auto. }
  constructor; cbn [rg_lo rg_hi rg_w rg_bg].
  - unfold mat1. cbn [rg_cells]. apply IMap.bst_add. exact Rbst.
  - intros K. discriminate K.
  - intros K. discriminate K.
  - intros g' gr' Hf. destruct (CASE g' gr' Hf) as [[-> ->]|[Hne Hf']]; [| exact (Rcells g' gr' Hf')].
    cbn [g_cells]. split; [cbn; split; exact I|]. constructor; [|constructor].
    unfold cell_ok. cbn [c_idx c_w c_v den]. split; [lia|]. split; [lia|]. split; [lia|].
    intros i Hi'. rewrite E0, Z.add_0_l. apply BY. exact Hi'.
  - intros g' gr' c i Hf Hc Hi'. destruct (CASE g' gr' Hf) as [[-> ->]|[Hne Hf']]; [| exact (Rin g' gr' c i Hf' Hc Hi')].
    cbn [g_cells] in Hc. destruct Hc as [<-|[]]. cbn [c_idx c_w] in *. split; [intros K; discriminate K|].
    intros _. exact (IN i Hi').
  - intros o H1 H2 U. unfold bg_byte. cbn [rg_bg]. fold (bg_byte segs E 0%uint63 r o).
    apply Rbg; [exact H1| exact H2|].
    intros g' gr' Hg' Hf'. unfold uncovered in U. unfold mat1 in U. cbn [rg_cells pe_g] in U.
    destruct (Uint63.eqb g' g) eqn:EQ.
    + apply Uint63.eqb_correct in EQ. subst g'. destruct (U g (Gran true [Cell idx w (VL v)]) Hg' FS) as [D _]. discriminate D.
    + apply Uint63.eqb_false_spec in EQ. apply (U g' gr'); [exact Hg'|]. rewrite FO by exact EQ. exact Hf'.
Qed.

Definition removed (lo1 hi1 lo2 hi2 g : int) : bool :=
  (PrimInt63.leb lo2 g && PrimInt63.ltb g hi2) || (PrimInt63.leb lo1 g && PrimInt63.ltb g hi1).

Lemma strip_sound : forall priv priv' E m r lo1 hi1 lo2 hi2,
  region_ok segs priv E m 0%uint63 r ->
  (forall o, in_priv priv o -> in_priv priv' o) ->
  (forall g o, keyZ g = o / 8 -> removed lo1 hi1 lo2 hi2 g = true -> in_priv priv' o) ->
  (forall g gr c i, IMap.find g (rg_cells r) = Some gr -> removed lo1 hi1 lo2 hi2 g = false -> In c (g_cells gr) ->
     0 <= i < to_Z (c_w c) -> ~ in_priv priv' (8 * keyZ g + to_Z (c_idx c) + i)) ->
  let r' := Region (rg_lo r) (rg_hi r) (rg_w r) (rg_bg r) (IMap.remove_range lo2 hi2 (IMap.remove_range lo1 hi1 (rg_cells r))) in
  region_ok segs priv' E m 0%uint63 r'
  /\ (forall g, IMap.find g (rg_cells r') = if removed lo1 hi1 lo2 hi2 g then None else IMap.find g (rg_cells r)).
Proof.
  intros priv priv' E m r lo1 hi1 lo2 hi2 [Rbst Rrange Rvalid Rcells Rin Rbg] MONO RP PUB. cbn [rg_cells rg_lo rg_hi rg_w rg_bg].
  assert (B1 : IMap.bst (IMap.remove_range lo1 hi1 (rg_cells r))) by (apply IMap.remove_range_bst; exact Rbst).
  assert (F : forall g, IMap.find g (IMap.remove_range lo2 hi2 (IMap.remove_range lo1 hi1 (rg_cells r))) =
        if removed lo1 hi1 lo2 hi2 g then None else IMap.find g (rg_cells r)).
  { intros g. unfold removed. rewrite IMap.find_remove_range by exact B1. rewrite IMap.find_remove_range by exact Rbst.
    destruct (PrimInt63.leb lo2 g && PrimInt63.ltb g hi2); destruct (PrimInt63.leb lo1 g && PrimInt63.ltb g hi1); reflexivity. }
  split; [| exact F].
  assert (SUB : forall g gr, IMap.find g (IMap.remove_range lo2 hi2 (IMap.remove_range lo1 hi1 (rg_cells r))) = Some gr ->
                IMap.find g (rg_cells r) = Some gr /\ removed lo1 hi1 lo2 hi2 g = false).
  { intros g gr Hf. rewrite F in Hf. destruct (removed lo1 hi1 lo2 hi2 g); [discriminate| auto]. }
  constructor; cbn [rg_cells rg_lo rg_hi rg_w rg_bg].
  - apply IMap.remove_range_bst. exact B1.
  - intros K; discriminate K.
  - intros K; discriminate K.
  - intros g gr Hf. apply Rcells. apply SUB. exact Hf.
  - intros g gr c i Hf Hc Hi. destruct (SUB g gr Hf) as [Hf0 Hrm]. pose proof (Rin g gr c i Hf0 Hc Hi) as [P1 P2].
    split; [exact P1|]. intros K. destruct (P2 K) as (Q1 & Q2 & Q3). split; [exact Q1|]. split; [exact Q2|].
    apply (PUB g gr c i Hf0 Hrm Hc Hi).
  - intros o H1 H2 U. unfold bg_byte. cbn [rg_bg]. fold (bg_byte segs E 0%uint63 r o). apply Rbg; [exact H1| |].
    + intros K. destruct (H2 K) as (Q1 & Q2 & Q3). split; [exact Q1|]. split; [exact Q2|]. intros IP. apply Q3. apply MONO. exact IP.
    + intros g gr Hg Hf. destruct (removed lo1 hi1 lo2 hi2 g) eqn:RM.
      * exfalso. destruct (H2 eq_refl) as (_ & _ & Q3). apply Q3. apply (RP g o Hg RM).
      * apply (U g gr Hg). rewrite F, RM. exact Hf.
Qed.
End Regions.

Section Snd.
Variable segs : list Segment.
Variable OPS : optable.
Variable FL : int.
Variables (MP : Model -> Prop) (PB : (int -> list byte) -> Prop).
Hypothesis H_FL8 : to_Z FL mod 8 = 0.
Hypothesis H_FLB : to_Z FL + 1024 < 2 ^ 62.
Hypothesis H_holds : forall args m md, op_holds OPS POOL_ID args m md <-> pool_holds FL segs args m md.
Hypothesis H_fp : forall args, op_fp OPS POOL_ID args = pool_fp FL args.
Hypothesis H_cov : forall args a, ~ op_cov1 OPS POOL_ID args a.
Hypothesis H_others : forall id args a, PrimInt63.eqb id POOL_ID = false ->
  Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS id args) ->
  ~ (to_Z FL <= a < to_Z FL + 8) /\ ~ (to_Z FL + 16 <= a < to_Z FL + 528).

Let FLz : Z := to_Z FL.
Lemma FLz_nn : 0 <= FLz. Proof. unfold FLz. pose proof (to_Z_bounded FL). lia. Qed.
Lemma wB_val : wB = 2 ^ 63. Proof. reflexivity. Qed.
Lemma add_small' : forall a b, to_Z a + to_Z b < 2 ^ 63 -> to_Z (PrimInt63.add a b) = to_Z a + to_Z b.
Proof. intros a b H. rewrite add_spec. apply Z.mod_small. pose proof (to_Z_bounded a). pose proof (to_Z_bounded b). rewrite wB_val. lia. Qed.
Lemma HB_val : to_Z (HB FL) = FLz + 16.
Proof. unfold HB, FLz. rewrite add_small'; change (to_Z 16%uint63) with 16; [reflexivity| pose proof FLz_nn; unfold FLz in *; lia]. Qed.
Lemma gk_val : forall a, to_Z (gk a) = to_Z a / 8.
Proof. intros a. unfold gk. rewrite lsr_spec. reflexivity. Qed.
Lemma keyZ_small : forall g, to_Z g < 2 ^ 62 -> keyZ g = to_Z g.
Proof. intros g Hg. unfold keyZ, Mem.keyZ. destruct (Uint63.ltbP g bit62i) as [L|L]; [reflexivity|]. change (to_Z bit62i) with (2 ^ 62) in L. lia. Qed.

Definition dirtied (g : int) : bool :=
  (Z.eqb (to_Z g) (FLz / 8)) || (Z.leb (FLz / 8 + 2) (to_Z g) && Z.ltb (to_Z g) (FLz / 8 + 66)).

Lemma tbl_facts : forall s e, In e (tbl FL s) ->
  0 <= to_Z (pe_i e) /\ 0 < to_Z (pe_w e) /\ to_Z (pe_i e) + to_Z (pe_w e) <= 8
  /\ 8 * keyZ (pe_g e) + to_Z (pe_i e) = to_Z (pe_addr e)
  /\ to_Z (pe_g e) < 2 ^ 62
  /\ ((FLz <= to_Z (pe_addr e) /\ to_Z (pe_addr e) + to_Z (pe_w e) <= FLz + 8)
      \/ (FLz + 16 <= to_Z (pe_addr e) /\ to_Z (pe_addr e) + to_Z (pe_w e) <= FLz + 528))
  /\ dirtied (pe_g e) = true.
Proof.
  pose proof FLz_nn as NN. pose proof HB_val as HBv.
  assert (G0 : to_Z (gk FL) = FLz / 8) by apply gk_val.
  assert (G1 : to_Z (gk (PrimInt63.add (HB FL) 8%uint63)) = FLz / 8 + 3).
  { rewrite gk_val, add_small', HBv; change (to_Z 8%uint63) with 8; [| unfold FLz in *; lia].
    replace (FLz + 16 + 8) with (FLz + 3 * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
  assert (G2 : to_Z (gk (PrimInt63.add (HB FL) 200%uint63)) = FLz / 8 + 27).
  { rewrite gk_val, add_small', HBv; change (to_Z 200%uint63) with 200; [| unfold FLz in *; lia].
    replace (FLz + 16 + 200) with (FLz + 27 * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
  assert (D8 : FLz = 8 * (FLz / 8)) by (pose proof (Z.div_mod FLz 8 ltac:(lia)); unfold FLz in *; lia).
  assert (ADDR : forall g i, to_Z g < 2 ^ 59 -> 0 <= to_Z i < 8 -> to_Z (pe_addr (PE g i 8%uint63 wzero)) = 8 * to_Z g + to_Z i).
  { intros g i Hg Hi. unfold pe_addr. cbn [pe_g pe_i]. pose proof (to_Z_bounded g).
    rewrite add_small'; rewrite lsl_spec; change (2 ^ to_Z 3%uint63) with 8; rewrite wB_val, Z.mod_small; lia. }
  intros s e Hin.
  assert (CASES : e = PE (gk FL) 0%uint63 8%uint63 (pe_v e)
               \/ e = PE (gk (PrimInt63.add (HB FL) 8%uint63)) 4%uint63 4%uint63 (pe_v e)
               \/ e = PE (gk (PrimInt63.add (HB FL) 200%uint63)) 4%uint63 4%uint63 (pe_v e)).
  { destruct s as [|[|s']]; cbn [tbl] in Hin;
      repeat (destruct Hin as [<-|Hin]; [cbn [pe_v]; tauto|]); destruct Hin. }
  destruct CASES as [-> |[-> | ->]]; cbn [pe_g pe_i pe_w];
    change (to_Z 0%uint63) with 0; change (to_Z 4%uint63) with 4; change (to_Z 8%uint63) with 8.
  - rewrite keyZ_small by lia. unfold pe_addr; cbn [pe_g pe_i].
    rewrite add_small'; rewrite lsl_spec, G0; change (2 ^ to_Z 3%uint63) with 8; change (to_Z 0%uint63) with 0; rewrite wB_val, Z.mod_small; try lia.
    repeat split; try lia. unfold dirtied. rewrite G0, Z.eqb_refl. reflexivity.
  - rewrite keyZ_small by lia. unfold pe_addr; cbn [pe_g pe_i].
    rewrite add_small'; rewrite lsl_spec, G1; change (2 ^ to_Z 3%uint63) with 8; change (to_Z 4%uint63) with 4; rewrite wB_val, Z.mod_small; try lia.
    repeat split; try lia. unfold dirtied. rewrite G1.
    replace (FLz / 8 + 2 <=? FLz / 8 + 3) with true by (symmetry; apply Z.leb_le; lia).
    replace (FLz / 8 + 3 <? FLz / 8 + 66) with true by (symmetry; apply Z.ltb_lt; lia). apply orb_true_r.
  - rewrite keyZ_small by lia. unfold pe_addr; cbn [pe_g pe_i].
    rewrite add_small'; rewrite lsl_spec, G2; change (2 ^ to_Z 3%uint63) with 8; change (to_Z 4%uint63) with 4; rewrite wB_val, Z.mod_small; try lia.
    repeat split; try lia. unfold dirtied. rewrite G2.
    replace (FLz / 8 + 2 <=? FLz / 8 + 27) with true by (symmetry; apply Z.leb_le; lia).
    replace (FLz / 8 + 27 <? FLz / 8 + 66) with true by (symmetry; apply Z.ltb_lt; lia). apply orb_true_r.
Qed.

Lemma gkHB_val : to_Z (gk (HB FL)) = FLz / 8 + 2.
Proof. rewrite gk_val, HB_val. replace (FLz + 16) with (FLz + 2 * 8) by lia. rewrite Z.div_add by lia. reflexivity. Qed.
Lemma gkFL_val : to_Z (gk FL) = FLz / 8. Proof. apply gk_val. Qed.

Lemma dirty_pool_sound : forall priv E m r,
  region_ok segs priv E m 0%uint63 r ->
  region_ok segs priv E m 0%uint63 (dirty_pool FL r)
  /\ (forall g, IMap.find g (rg_cells (dirty_pool FL r)) = if dirtied g then Some (Gran true []) else IMap.find g (rg_cells r)).
Proof.
  intros priv E m r RO. pose proof FLz_nn as NN. unfold FLz in *.
  assert (B1 : to_Z (gk FL) + Z.of_nat 1 < wB) by (rewrite gkFL_val, wB_val; cbn [Z.of_nat]; unfold FLz; lia).
  assert (B2 : to_Z (gk (HB FL)) + Z.of_nat 64 < wB) by (rewrite gkHB_val, wB_val; unfold FLz; lia).
  pose proof (CtrFX.region_dirty_sound segs priv E m 0%uint63 r (gk FL) 1 B1 RO) as R1.
  pose proof (CtrFX.region_dirty_sound segs priv E m 0%uint63 _ (gk (HB FL)) 64 B2 R1) as R2. cbn [rg_lo rg_hi rg_w rg_bg rg_cells] in R2.
  split; [exact R2|].
  intros g. unfold dirty_pool. cbn [rg_cells].
  destruct (CtrFX.dirty_range_spec (gk FL) 1 (rg_cells r) (ro_bst _ _ _ _ _ _ RO) B1) as [Bd1 F1].
  destruct (CtrFX.dirty_range_spec (gk (HB FL)) 64 _ Bd1 B2) as [Bd2 F2].
  rewrite F2, F1, gkHB_val, gkFL_val. unfold dirtied. unfold FLz. change (Z.of_nat 64) with 64. change (Z.of_nat 1) with 1.
  destruct (Z.leb_spec (to_Z FL / 8 + 2) (to_Z g)); destruct (Z.ltb_spec (to_Z g) (to_Z FL / 8 + 2 + 64));
  destruct (Z.ltb_spec (to_Z g) (to_Z FL / 8 + 66)); destruct (Z.eqb_spec (to_Z g) (to_Z FL / 8));
  destruct (Z.leb_spec (to_Z FL / 8) (to_Z g)); destruct (Z.ltb_spec (to_Z g) (to_Z FL / 8 + 1)); cbn [andb orb];
  first [reflexivity | exfalso; lia].
Qed.

Fixpoint glookup (g : int) (es : list pent) : option pent :=
  match es with
  | [] => None
  | e :: es' => if PrimInt63.eqb (pe_g e) g then Some e else glookup g es'
  end.

Fixpoint gnodup (es : list pent) : Prop :=
  match es with
  | [] => True
  | e :: es' => (forall e', In e' es' -> pe_g e' <> pe_g e) /\ gnodup es'
  end.

Lemma mat_sound : forall priv E m es r,
  ev E 0%uint63 = Z_to_bv 64 0 ->
  region_ok segs priv E m 0%uint63 r ->
  gnodup es ->
  (forall e, In e es ->
     IMap.find (pe_g e) (rg_cells r) = Some (Gran true [])
     /\ 0 <= to_Z (pe_i e) /\ 0 < to_Z (pe_w e) /\ to_Z (pe_i e) + to_Z (pe_w e) <= 8
     /\ (forall i, 0 <= i < to_Z (pe_w e) -> rb segs m (8 * keyZ (pe_g e) + to_Z (pe_i e) + i) = Some (byte_of (wbv (pe_v e)) i))
     /\ (forall i, 0 <= i < to_Z (pe_w e) -> let o := 8 * keyZ (pe_g e) + to_Z (pe_i e) + i in
           0 <= o < two63 / 2 /\ (exists seg, find_segment segs o 1 = Some seg) /\ ~ in_priv priv o)) ->
  region_ok segs priv E m 0%uint63 (mat es r)
  /\ (forall g, IMap.find g (rg_cells (mat es r)) =
        match glookup g es with
        | Some e => Some (Gran true [Cell (pe_i e) (pe_w e) (VL (pe_v e))])
        | None => IMap.find g (rg_cells r)
        end).
Proof.
  intros priv E m es. induction es as [|e es IH]; intros r Hz RO ND PRE.
  - split; [exact RO| intros g; reflexivity].
  - cbn [mat fold_left]. change (fold_left mat1 es (mat1 r e)) with (mat es (mat1 r e)).
    destruct (PRE e (or_introl eq_refl)) as (Fg & Hi & Hw & Hiw & BY & IN).
    destruct e as [g idx w v]. cbn [pe_g pe_i pe_w pe_v] in *.
    destruct (mat1_sound segs priv E m r g idx w v Hz RO Fg Hi Hw Hiw BY IN) as (RO1 & FO & FS).
    destruct ND as [NI ND']. cbn [pe_g] in NI.
    destruct (IH (mat1 r (PE g idx w v)) Hz RO1 ND') as [RO2 F2].
    { intros e' He'. destruct (PRE e' (or_intror He')) as (Fg' & rest). split; [| exact rest].
      rewrite FO; [exact Fg'|]. intros EQ. apply (NI e' He'). rewrite <- EQ. reflexivity. }
    split; [exact RO2|]. intros g'. rewrite F2. cbn [glookup pe_g].
    destruct (Uint63.eqb g g') eqn:EQ.
    + apply Uint63.eqb_correct in EQ. subst g'.
      replace (glookup g es) with (@None pent); [exact FS|].
      clear - NI. induction es as [|e2 es IH2]; [reflexivity|]. cbn [glookup].
      destruct (Uint63.eqb (pe_g e2) g) eqn:EQ2; [apply Uint63.eqb_correct in EQ2; exfalso; apply (NI e2 (or_introl eq_refl)); exact EQ2|].
      apply IH2. intros e' H'. apply NI. right; exact H'.
    + apply Uint63.eqb_false_spec in EQ. destruct (glookup g' es); [reflexivity|]. apply FO. intros X; apply EQ; symmetry; exact X.
Qed.

Lemma iv_fl_val : to_Z (fst (iv_fl FL)) = FLz /\ to_Z (snd (iv_fl FL)) = FLz + 8.
Proof. unfold iv_fl. cbn [fst snd]. split; [reflexivity|]. rewrite add_small'; change (to_Z 8%uint63) with 8; [reflexivity| pose proof FLz_nn; unfold FLz in *; lia]. Qed.
Lemma iv_hb_val : to_Z (fst (iv_hb FL)) = FLz + 16 /\ to_Z (snd (iv_hb FL)) = FLz + 528.
Proof. unfold iv_hb. cbn [fst snd]. rewrite HB_val. split; [reflexivity|]. pose proof FLz_nn. rewrite add_small'; rewrite HB_val; change (to_Z 512%uint63) with 512; unfold FLz in *; lia. Qed.

Lemma iv_eqb_eq : forall a b, iv_eqb a b = true -> a = b.
Proof. intros [a1 a2] [b1 b2] H. unfold iv_eqb in H. cbn in H. apply andb_prop in H as [H1 H2]. apply Uint63.eqb_correct in H1. apply Uint63.eqb_correct in H2. subst. reflexivity. Qed.

Lemma unpriv_sub : forall priv o, in_priv (unpriv FL priv) o -> in_priv priv o.
Proof. intros priv o H. unfold in_priv, unpriv in *. apply Exists_exists in H as (iv & Hin & R). apply filter_In in Hin as [Hin _]. apply Exists_exists. exists iv. auto. Qed.

Lemma unpriv_lost : forall priv o, in_priv priv o -> ~ in_priv (unpriv FL priv) o ->
  (FLz <= o < FLz + 8) \/ (FLz + 16 <= o < FLz + 528).
Proof.
  intros priv o H Hn. unfold in_priv in H. apply Exists_exists in H as (iv & Hin & R).
  destruct (iv_eqb iv (iv_fl FL) || iv_eqb iv (iv_hb FL)) eqn:E.
  - apply orb_prop in E. destruct E as [E|E]; apply iv_eqb_eq in E; subst iv.
    + left. destruct iv_fl_val as [A B]. lia.
    + right. destruct iv_hb_val as [A B]. lia.
  - exfalso. apply Hn. unfold in_priv, unpriv. apply Exists_exists. exists iv. split; [| exact R].
    apply filter_In. split; [exact Hin|]. rewrite E. reflexivity.
Qed.

Lemma priv_ok_public : forall priv, priv_ok FL priv = true ->
  forall o, (FLz <= o < FLz + 8) \/ (FLz + 16 <= o < FLz + 528) -> ~ in_priv (unpriv FL priv) o.
Proof.
  intros priv H o Ho. unfold priv_ok in H. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply negb_true_iff in H3. apply negb_true_iff in H4. pose proof FLz_nn. pose proof HB_val.
  destruct Ho as [Ho|Ho].
  - apply (MemP.in_priv_b_false _ FL 8%uint63); [exact H3| change (to_Z 8%uint63) with 8; unfold two63, FLz in *; lia| change (to_Z 8%uint63) with 8; unfold FLz in *; lia].
  - apply (MemP.in_priv_b_false _ (HB FL) 512%uint63); [exact H4| change (to_Z 512%uint63) with 512; unfold two63, FLz in *; lia| change (to_Z 512%uint63) with 512; unfold FLz in *; lia].
Qed.

Lemma gnodup_tbl : forall s, gnodup (tbl FL s).
Proof.
  pose proof FLz_nn as NN. pose proof HB_val as HBv.
  assert (G0 : to_Z (gk FL) = FLz / 8) by apply gk_val.
  assert (G1 : to_Z (gk (PrimInt63.add (HB FL) 8%uint63)) = FLz / 8 + 3).
  { rewrite gk_val, add_small', HB_val; change (to_Z 8%uint63) with 8; [| unfold FLz in *; lia].
    replace (FLz + 16 + 8) with (FLz + 3 * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
  assert (G2 : to_Z (gk (PrimInt63.add (HB FL) 200%uint63)) = FLz / 8 + 27).
  { rewrite gk_val, add_small', HB_val; change (to_Z 200%uint63) with 200; [| unfold FLz in *; lia].
    replace (FLz + 16 + 200) with (FLz + 27 * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
  assert (NE : forall a b, to_Z a <> to_Z b -> a <> b) by (intros a b Hne Heq; apply Hne; rewrite Heq; reflexivity).
  intros [|[|s]]; cbn [tbl gnodup pe_g]; repeat split; intros e' He';
    repeat (destruct He' as [<-|He']; [cbn [pe_g]; apply NE; rewrite ?G0, ?G1, ?G2; lia|]); destruct He'.
Qed.

Lemma in_based_add0 : forall E R r a, IMap.bst R -> in_based E (IMap.add 0%uint63 r R) a <-> in_based E R a.
Proof.
  intros E R r a B. unfold in_based. split; intros (k & rk & Hf & Hk & Ha); exists k, rk; (split; [| auto]).
  - rewrite IMap.find_add_other in Hf; [exact Hf| exact B|]. intros X. subst k. discriminate Hk.
  - rewrite IMap.find_add_other; [exact Hf| exact B|]. intros X. subst k. discriminate Hk.
Qed.

Lemma of_Z_keyZ : forall z, 0 <= z < 2 ^ 62 -> keyZ (Uint63.of_Z z) = z /\ to_Z (Uint63.of_Z z) = z.
Proof.
  intros z Hz. assert (T : to_Z (Uint63.of_Z z) = z) by (rewrite of_Z_spec; apply Z.mod_small; rewrite wB_val; lia).
  split; [| exact T]. rewrite keyZ_small; rewrite T; lia.
Qed.

Lemma not_id_neq : forall id o, CtrFX.not_id id o -> PrimInt63.eqb (op_id o) id = false.
Proof. intros id o H. exact H. Qed.

Lemma open_st_ok : forall E st ms md sel r0 s,
  st_ok segs OPS E st ms md ->
  find_op POOL_ID (s_ops st) = Some [sel] ->
  CtrA.count_op POOL_ID (s_ops st) = 1%nat ->
  IMap.find 0%uint63 (s_regs st) = Some r0 ->
  priv_ok FL (s_priv st) = true ->
  pool_in_image FL segs = true ->
  (s < NSTATES)%nat ->
  Forall (pent_holds segs (ms_mem ms)) (tbl FL s) ->
  st_ok segs OPS E (open_st FL st r0 s) ms md.
Proof.
  intros E st ms md sel r0 s ST Hfind Hcnt Hr0 Hpriv Himg Hs TB.
  pose proof ST as [Spc Sx0 Sregs Sfregs Ssvc Sresv Sfcsr Srom Szero Sbst Sreg Sdisj Spub Sfacts Sops Sapart Smf Scov Sminv].
  pose proof FLz_nn as NN.
  unfold pool_in_image in Himg. apply andb_prop in Himg as [Img1 Img2].
  destruct (MemP.abs_writable_sound segs (to_Z FL) 8 ltac:(lia) ltac:(lia) Img1) as [_ SEG1].
  pose proof HB_val as HBv.
  destruct (MemP.abs_writable_sound segs (to_Z (HB FL)) 512 ltac:(rewrite HBv; lia) ltac:(lia) Img2) as [_ SEG2]. rewrite HBv in SEG2.
  assert (LT62 : FLz + 528 < 2 ^ 62) by (unfold FLz; lia).
  assert (D8 : FLz = 8 * (FLz / 8)) by (pose proof (Z.div_mod FLz 8 ltac:(lia)); unfold FLz in *; lia).
  set (priv' := unpriv FL (s_priv st)).

  pose proof (Sreg 0%uint63 r0 Hr0) as RO0.
  destruct (dirty_pool_sound (s_priv st) E (ms_mem ms) r0 RO0) as [RO1 F1].
  assert (RO1' : region_ok segs priv' E (ms_mem ms) 0%uint63 (dirty_pool FL r0)).
  { apply (region0_priv_change segs (s_priv st) priv'); [exact RO1| |].
    - intros g gr c i Hf Hc Hi IP. apply unpriv_sub in IP.
      exact (proj2 (proj2 (proj2 (ro_cells_in _ _ _ _ _ _ RO1 g gr c i Hf Hc Hi) eq_refl)) IP).
    - intros o IP NIP. destruct (unpriv_lost (s_priv st) o IP NIP) as [R|R].
      + destruct (of_Z_keyZ (o / 8)) as [K T]; [split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]|].
        exists (Uint63.of_Z (o / 8)), (Gran true []). split; [exact K|]. split; [| reflexivity].
        rewrite F1. unfold dirtied. rewrite T. replace (o / 8) with (FLz / 8) by (apply Z.div_unique with (r := o - FLz); lia).
        rewrite Z.eqb_refl. reflexivity.
      + destruct (of_Z_keyZ (o / 8)) as [K T]; [split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]|].
        exists (Uint63.of_Z (o / 8)), (Gran true []). split; [exact K|]. split; [| reflexivity].
        rewrite F1. unfold dirtied. rewrite T.
        assert (A1 : FLz / 8 + 2 <= o / 8) by (apply Z.div_le_lower_bound; lia).
        assert (A2 : o / 8 < FLz / 8 + 66) by (apply Z.div_lt_upper_bound; lia).
        replace (FLz / 8 + 2 <=? o / 8) with true by (symmetry; apply Z.leb_le; lia).
        replace (o / 8 <? FLz / 8 + 66) with true by (symmetry; apply Z.ltb_lt; lia). rewrite orb_true_r. reflexivity. }
  destruct (mat_sound priv' E (ms_mem ms) (tbl FL s) (dirty_pool FL r0) Szero RO1' (gnodup_tbl s)) as [RO2 F2].
  { intros e He. destruct (tbl_facts s e He) as (C1 & C2 & C3 & C4 & C5 & C6 & C7).
    split; [rewrite F1, C7; reflexivity|]. split; [exact C1|]. split; [exact C2|]. split; [exact C3|]. split.
    - intros i Hi. rewrite C4. apply (proj1 (Forall_forall _ _) TB e He i Hi).
    - intros i Hi. cbv zeta. rewrite C4. split; [rewrite MemP.half63; unfold FLz in *; lia|]. split.
      + destruct C6 as [C6|C6].
        * destruct (SEG1 (to_Z (pe_addr e) + i - to_Z FL) ltac:(unfold FLz in *; lia)) as [_ (seg & Hseg & _)].
          exists seg. replace (to_Z (pe_addr e) + i) with (to_Z FL + (to_Z (pe_addr e) + i - to_Z FL)) by lia. exact Hseg.
        * destruct (SEG2 (to_Z (pe_addr e) + i - (FLz + 16)) ltac:(unfold FLz in *; lia)) as [_ (seg & Hseg & _)].
          exists seg. replace (to_Z (pe_addr e) + i) with (FLz + 16 + (to_Z (pe_addr e) + i - (FLz + 16))) by lia. exact Hseg.
      + apply priv_ok_public; [exact Hpriv|]. unfold FLz in *. lia. }
  set (r2 := mat (tbl FL s) (dirty_pool FL r0)) in *.

  pose proof (CtrFX.find_op_unique POOL_ID (s_ops st) [sel] Hfind Hcnt) as (l1 & l2 & Eops & N1 & N2).
  assert (SET : set_op POOL_ID [VL (OPEN_MARK)] (s_ops st) = l1 ++ OpI POOL_ID [VL OPEN_MARK] :: l2).
  { rewrite Eops. apply CtrFX.set_op_split. exact N1. }
  assert (MARKu : bv_unsigned (den E (VL OPEN_MARK)) = 3).
  { cbn [den]. unfold OPEN_MARK. rewrite wbv_unsigned, wlit_ok. reflexivity. }
  constructor; cbn [s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next open_st set_r0]; try assumption.
  all: unfold set_r0; fold r2.
  -   apply IMap.bst_add. exact Sbst.
  -   intros k r Hf. destruct (Uint63.eqb k 0%uint63) eqn:EK.
    + apply Uint63.eqb_correct in EK. subst k. rewrite IMap.find_add_same in Hf by exact Sbst. injection Hf as <-. exact RO2.
    + apply Uint63.eqb_false_spec in EK. rewrite IMap.find_add_other in Hf; [| exact Sbst| congruence].
      apply (region_ok_priv_based segs (s_priv st)); [| exact (Sreg k r Hf)].
      destruct (Uint63.eqb k 0%uint63) eqn:X; [apply Uint63.eqb_correct in X; congruence| reflexivity].
  -   intros k1 q1 k2 q2 H1 H2 Hne E1 E2.
    rewrite IMap.find_add_other in H1; [| exact Sbst| intros X; subst k1; discriminate E1].
    rewrite IMap.find_add_other in H2; [| exact Sbst| intros X; subst k2; discriminate E2].
    exact (Sdisj k1 q1 k2 q2 H1 H2 Hne E1 E2).
  -   intros r g gr c Hf Hg Hc i Hi. rewrite IMap.find_add_same in Hf by exact Sbst. injection Hf as <-.
    exact (proj2 (proj2 (proj2 (ro_cells_in _ _ _ _ _ _ RO2 g gr c i Hg Hc Hi) eq_refl))).
  -   rewrite SET. rewrite Eops in Sops. unfold ops_hold in *. apply CtrFX.Forall_app3 in Sops as (O1 & O2 & O3).
    apply CtrFX.Forall_app3. split; [exact O1|]. split; [| exact O3].
    cbn [op_id op_args map]. apply H_holds. cbn [pool_holds]. left. exact MARKu.
  -   rewrite SET. rewrite Eops in Sapart. unfold ops_apart in *. apply CtrFX.Forall_app3 in Sapart as (A1 & A2 & A3).
    assert (OTHER : forall o, CtrFX.not_id POOL_ID o ->
              (forall a, Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS (op_id o) (map (den E) (op_args o))) ->
                 ~ in_based E (s_regs st) a /\ ((exists seg, find_segment segs a 1 = Some seg) -> in_priv (s_priv st) a)) ->
              forall a, Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS (op_id o) (map (den E) (op_args o))) ->
                 ~ in_based E (IMap.add 0%uint63 r2 (s_regs st)) a /\ ((exists seg, find_segment segs a 1 = Some seg) -> in_priv priv' a)).
    { intros o Hid Ho a Ha. destruct (Ho a Ha) as [NB IP]. split; [rewrite in_based_add0 by exact Sbst; exact NB|].
      intros SG. specialize (IP SG).
      destruct (H_others (op_id o) (map (den E) (op_args o)) a Hid Ha) as [X1 X2].
      unfold priv'. unfold in_priv, unpriv in *. apply Exists_exists in IP as (iv & Hin & R). apply Exists_exists. exists iv. split; [| exact R].
      apply filter_In. split; [exact Hin|].
      destruct (iv_eqb iv (iv_fl FL)) eqn:Q1; [apply iv_eqb_eq in Q1; subst iv; destruct iv_fl_val as [V1 V2]; exfalso; unfold FLz in *; lia|].
      destruct (iv_eqb iv (iv_hb FL)) eqn:Q2; [apply iv_eqb_eq in Q2; subst iv; destruct iv_hb_val as [V1 V2]; exfalso; unfold FLz in *; lia|].
      reflexivity. }
    apply CtrFX.Forall_app3. split; [| split].
    + apply Forall_forall. intros o Ho. apply OTHER; [exact (proj1 (Forall_forall _ _) N1 o Ho)| exact (proj1 (Forall_forall _ _) A1 o Ho)].
    + cbn [op_id op_args map]. intros a Ha. rewrite H_fp in Ha. unfold pool_fp in Ha. rewrite MARKu in Ha. cbn in Ha. inversion Ha.
    + apply Forall_forall. intros o Ho. apply OTHER; [exact (proj1 (Forall_forall _ _) N2 o Ho)| exact (proj1 (Forall_forall _ _) A3 o Ho)].
  -
    rewrite SET. intros a FA.
    assert (FA' : fx_acc segs E (s_regs st) a).
    { destruct FA as [B|S']; [left; rewrite in_based_add0 in B by exact Sbst; exact B | right; exact S']. }
    destruct (Scov a FA') as [C0|C1]; [left; exact C0| right].
    rewrite Eops in C1. unfold insts in *. rewrite map_app in *. cbn [map] in *.
    apply Exists_app in C1 as [C|C]; [apply Exists_app; left; exact C|].
    apply Exists_cons in C as [C|C]; [exfalso; cbn [fst snd op_id op_args] in C; exact (H_cov _ _ C)|].
    apply Exists_app. right. apply Exists_cons_tl. exact C.
Qed.

Lemma ov_read_bytes_inv : forall m A n bs, ov_read_bytes segs m (Z_to_bv 64 A) n = Some bs ->
  0 <= A -> A + Z.of_nat n <= two64 ->
  length bs = n /\ forall i, 0 <= i < Z.of_nat n -> rb segs m (A + i) = nth_error bs (Z.to_nat i).
Proof.
  intros m A n. revert A. induction n as [|n IH]; intros A bs H HA HAn.
  - cbn in H. injection H as <-. split; [reflexivity | intros i Hi; lia].
  - cbn [ov_read_bytes] in H. rewrite <- MemP.rb_unfold in H.
    destruct (rb segs m A) as [b|] eqn:Hb; [|discriminate H].
    rewrite MemP.Z_to_bv_succ in H.
    destruct (ov_read_bytes segs m (Z_to_bv 64 (A + 1)) n) as [bs'|] eqn:Hr; [|discriminate H]. injection H as <-.
    destruct (IH (A + 1) bs' Hr ltac:(lia) ltac:(lia)) as [Hlen Hbs]. split; [cbn; lia|].
    intros i Hi. destruct (Z.eq_dec i 0) as [->|Hi0].
    + rewrite Z.add_0_r. cbn. exact Hb.
    + replace (A + i) with (A + 1 + (i - 1)) by lia. rewrite Hbs by lia.
      replace (Z.to_nat i) with (S (Z.to_nat (i - 1))) by lia. reflexivity.
Qed.

Lemma wlit_word : forall i, wbv (wlit i) = Z_to_bv 64 (to_Z i).
Proof. intros i. apply bv_eq. rewrite wbv_unsigned, wlit_ok, Z_to_bv_small; [reflexivity|]. pose proof (to_Z_bounded i). rewrite bv_modulus_64, wB_two63 in *. unfold two63, two64 in *. lia. Qed.

Lemma pent_matches_sound : forall E st ms md e,
  st_ok segs OPS E st ms md -> pent_matches segs st e = true ->
  MemP.wok (pe_w e) -> to_Z (pe_addr e) + 8 < 2 ^ 62 ->
  pent_holds segs (ms_mem ms) e.
Proof.
  intros E st ms md e ST PM Hwok Ha. assert (Hw : 0 < to_Z (pe_w e) <= 8) by (unfold MemP.wok in Hwok; lia). unfold pent_matches in PM.
  destruct (do_load segs st (VL (wlit (pe_addr e))) (pe_w e) false) as [[[v'| | | | | | | | | |]|]|] eqn:DL; try discriminate PM.
  apply ValP.weqb_eq in PM. subst v'.
  destruct (StepM.do_load_sound segs OPS E st ms md _ _ false _ ST Hwok DL) as (bs & Len & OV & Dv).
  cbn [den] in OV, Dv. rewrite wlit_word in OV.
  pose proof (to_Z_bounded (pe_addr e)) as Ba.
  destruct (ov_read_bytes_inv (ms_mem ms) (to_Z (pe_addr e)) (Z.to_nat (to_Z (pe_w e))) bs OV ltac:(lia) ltac:(rewrite Z2Nat.id by lia; unfold two64; lia)) as [Len' RB].
  intros i Hi. rewrite RB by (rewrite Z2Nat.id by lia; lia).
  rewrite (nth_error_nth' _ (Z_to_bv 8 0)) by (rewrite Len; apply Nat2Z.inj_lt; rewrite !Z2Nat.id by lia; lia).
  f_equal. apply bv_eq. rewrite MemP.byte_of_zbyte by lia.
  rewrite <- (Z2Nat.id i) at 2 by lia. rewrite <- MemP.zbyte_bytes_le by (rewrite Len; apply Nat2Z.inj_lt; rewrite !Z2Nat.id by lia; lia).
  rewrite Z2Nat.id by lia. f_equal.

  rewrite Dv. unfold ext_word, le_bytes_to_word. rewrite Z_to_bv_unsigned.
  pose proof (MemP.bytes_le_to_Z_bound bs) as BB. rewrite Len, Z2Nat.id in BB by lia.
  assert (P8 : 2 ^ (8 * to_Z (pe_w e)) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
  rewrite (Z_to_bv_small 64) by (rewrite bv_modulus_64; unfold two64; lia).
  unfold ext_Z. rewrite Z.mul_0_r, Z.pow_0_r, Z.div_1_r, Z.mod_small by lia.
  unfold bv_wrap. rewrite bv_modulus_64, Z.mod_small by (unfold two64; lia). reflexivity.
Qed.

Lemma first_state_sound : forall st n s0 s, first_state FL segs st n s0 = Some s ->
  tbl_matches FL segs st s = true /\ (s < s0 + n)%nat.
Proof.
  intros st n. induction n as [|n IH]; intros s0 s H; cbn [first_state] in H; [discriminate|].
  destruct (tbl_matches FL segs st s0) eqn:M.
  - injection H as <-. split; [exact M| lia].
  - destruct (IH (S s0) s H) as [A B]. split; [exact A| lia].
Qed.

Lemma keyZ_nonneg_toZ : forall g, 0 <= keyZ g -> to_Z g = keyZ g.
Proof. intros g H. unfold keyZ, Mem.keyZ in *. destruct (PrimInt63.ltb g bit62i); [reflexivity|]. pose proof (to_Z_bounded g). rewrite wB_val in *. unfold two63 in *. lia. Qed.

Lemma tbl_wok : forall s e, In e (tbl FL s) -> MemP.wok (pe_w e).
Proof.
  intros [|[|s]] e Hin; cbn [tbl] in Hin;
    repeat (destruct Hin as [<-|Hin]; [cbn [pe_w]; unfold MemP.wok; first [right; right; right; reflexivity | right; right; left; reflexivity] |]); destruct Hin.
Qed.

Lemma close_st_ok : forall E st ms md w r0 s,
  st_ok segs OPS E st ms md ->
  find_op POOL_ID (s_ops st) = Some [VL w] -> weqb w OPEN_MARK = true ->
  CtrA.count_op POOL_ID (s_ops st) = 1%nat ->
  IMap.find 0%uint63 (s_regs st) = Some r0 ->
  pool_in_image FL segs = true ->
  (s < NSTATES)%nat -> tbl_matches FL segs st s = true ->
  st_ok segs OPS E (close_st FL st r0 s) ms md.
Proof.
  intros E st ms md w r0 s ST Hfind Hmark Hcnt Hr0 Himg Hs TM.
  pose proof ST as [Spc Sx0 Sregs Sfregs Ssvc Sresv Sfcsr Srom Szero Sbst Sreg Sdisj Spub Sfacts Sops Sapart Smf Scov Sminv].
  pose proof FLz_nn as NN. pose proof HB_val as HBv.
  unfold pool_in_image in Himg. apply andb_prop in Himg as [Img1 Img2].
  destruct (MemP.abs_writable_sound segs (to_Z FL) 8 ltac:(lia) ltac:(lia) Img1) as [_ SEG1].
  destruct (MemP.abs_writable_sound segs (to_Z (HB FL)) 512 ltac:(rewrite HBv; lia) ltac:(lia) Img2) as [_ SEG2]. rewrite HBv in SEG2.
  assert (LT62 : FLz + 528 < 2 ^ 62) by (unfold FLz; lia).
  assert (D8 : FLz = 8 * (FLz / 8)) by (pose proof (Z.div_mod FLz 8 ltac:(lia)); unfold FLz in *; lia).

  assert (TB : Forall (pent_holds segs (ms_mem ms)) (tbl FL s)).
  { apply Forall_forall. intros e He. unfold tbl_matches in TM.
    pose proof (proj1 (forallb_forall _ _) TM e He) as TMe.
    destruct (tbl_facts s e He) as (C1 & C2 & C3 & C4 & C5 & C6 & C7).
    apply (pent_matches_sound E st ms md e ST); [exact TMe| apply (tbl_wok s e He)| unfold FLz in *; lia]. }
  set (priv' := iv_fl FL :: iv_hb FL :: s_priv st).
  assert (MONO : forall o, in_priv (s_priv st) o -> in_priv priv' o) by (intros o H; unfold priv', in_priv; right; right; exact H).
  assert (INP : forall o, (FLz <= o < FLz + 8) \/ (FLz + 16 <= o < FLz + 528) -> in_priv priv' o).
  { intros o Ho. unfold priv', in_priv. destruct iv_fl_val as [A1 A2]. destruct iv_hb_val as [B1 B2].
    destruct Ho as [Ho|Ho]; [left; lia| right; left; lia]. }

  pose proof (Sreg 0%uint63 r0 Hr0) as RO0.
  assert (GK1 : to_Z (PrimInt63.add (gk FL) 1%uint63) = FLz / 8 + 1).
  { rewrite add_small'; rewrite gkFL_val; change (to_Z 1%uint63) with 1; [reflexivity| unfold FLz in *; lia]. }
  assert (GK2 : to_Z (PrimInt63.add (gk (HB FL)) 64%uint63) = FLz / 8 + 66).
  { rewrite add_small'; rewrite gkHB_val; change (to_Z 64%uint63) with 64; [lia| unfold FLz in *; lia]. }
  assert (RMS : forall g, removed (gk FL) (PrimInt63.add (gk FL) 1%uint63) (gk (HB FL)) (PrimInt63.add (gk (HB FL)) 64%uint63) g = true <->
               (to_Z g = FLz / 8 \/ (FLz / 8 + 2 <= to_Z g < FLz / 8 + 66))).
  { intros g. unfold removed. pose proof gkHB_val as V1. pose proof gkFL_val as V2.
    destruct (Uint63.lebP (gk (HB FL)) g); destruct (Uint63.ltbP g (PrimInt63.add (gk (HB FL)) 64%uint63));
    destruct (Uint63.lebP (gk FL) g); destruct (Uint63.ltbP g (PrimInt63.add (gk FL) 1%uint63)); cbn [andb orb];
    rewrite ?V1, ?V2, ?GK1, ?GK2 in *; split; intros HH; try reflexivity; try discriminate HH; lia. }
  assert (RM : forall g, removed (gk FL) (PrimInt63.add (gk FL) 1%uint63) (gk (HB FL)) (PrimInt63.add (gk (HB FL)) 64%uint63) g = true ->
               to_Z g = FLz / 8 \/ (FLz / 8 + 2 <= to_Z g < FLz / 8 + 66)) by (intros g; apply RMS).
  assert (NRM : forall g, removed (gk FL) (PrimInt63.add (gk FL) 1%uint63) (gk (HB FL)) (PrimInt63.add (gk (HB FL)) 64%uint63) g = false ->
               to_Z g <> FLz / 8 /\ ~ (FLz / 8 + 2 <= to_Z g < FLz / 8 + 66)).
  { intros g H. split; intros X; (enough (T : removed (gk FL) (PrimInt63.add (gk FL) 1%uint63) (gk (HB FL)) (PrimInt63.add (gk (HB FL)) 64%uint63) g = true) by (rewrite T in H; discriminate H)); apply RMS; [left| right]; exact X. }
  destruct (strip_sound segs (s_priv st) priv' E (ms_mem ms) r0 (gk FL) (PrimInt63.add (gk FL) 1%uint63) (gk (HB FL)) (PrimInt63.add (gk (HB FL)) 64%uint63) RO0 MONO) as [RO' F'].
  { intros g o Hg Hrm. apply INP. destruct (RM g Hrm) as [E1|E1].
    - pose proof (MemP.keyZ_range g). rewrite keyZ_small in Hg by (unfold FLz in *; lia).
      left. pose proof (Z.div_mod o 8 ltac:(lia)). pose proof (Z.mod_pos_bound o 8 ltac:(lia)). lia.
    - rewrite keyZ_small in Hg by (unfold FLz in *; lia).
      right. pose proof (Z.div_mod o 8 ltac:(lia)). pose proof (Z.mod_pos_bound o 8 ltac:(lia)). lia. }
  { intros g gr c i Hf Hrm Hc Hi IP.
    pose proof (ro_cells_in _ _ _ _ _ _ RO0 g gr c i Hf Hc Hi) as [_ P2]. destruct (P2 eq_refl) as (Q1 & Q2 & Q3).
    pose proof (ro_cells _ _ _ _ _ _ RO0 g gr Hf) as [_ CF]. pose proof (proj1 (Forall_forall _ _) CF c Hc) as (W1 & W2 & W3 & _).
    unfold priv', in_priv in IP. destruct iv_fl_val as [A1 A2]. destruct iv_hb_val as [B1 B2].
    destruct (NRM g Hrm) as [N1 N2].
    set (o := 8 * keyZ g + to_Z (c_idx c) + i) in *.
    assert (KO : keyZ g = o / 8) by (subst o; apply Z.div_unique with (r := to_Z (c_idx c) + i); lia).
    pose proof (MemP.keyZ_range g) as KR.
    inversion IP as [iv l R|iv l R]; subst.
    -   cbv beta in R. assert (o / 8 = FLz / 8) by (symmetry; apply Z.div_unique with (r := o - FLz); lia).
      apply N1. rewrite (keyZ_nonneg_toZ g) by lia. lia.
    - inversion R as [iv' l' R'|iv' l' R']; subst.
      + cbv beta in R'. assert (FLz / 8 + 2 <= o / 8 < FLz / 8 + 66) by (split; [apply Z.div_le_lower_bound; lia| apply Z.div_lt_upper_bound; lia]).
        apply N2. rewrite (keyZ_nonneg_toZ g) by lia. lia.
      + exact (Q3 R'). }
  set (r1 := strip_pool FL r0) in *.
  assert (Er1 : r1 = Region (rg_lo r0) (rg_hi r0) (rg_w r0) (rg_bg r0)
                       (IMap.remove_range (gk (HB FL)) (PrimInt63.add (gk (HB FL)) 64%uint63)
                          (IMap.remove_range (gk FL) (PrimInt63.add (gk FL) 1%uint63) (rg_cells r0)))) by reflexivity.
  rewrite <- Er1 in RO', F'.

  pose proof (CtrFX.find_op_unique POOL_ID (s_ops st) [VL w] Hfind Hcnt) as (l1 & l2 & Eops & N1 & N2).
  set (newarg := VL (wlit (Uint63.of_Z (Z.of_nat s)))).
  assert (SET : set_op POOL_ID [newarg] (s_ops st) = l1 ++ OpI POOL_ID [newarg] :: l2).
  { rewrite Eops. apply CtrFX.set_op_split. exact N1. }
  assert (NEWu : bv_unsigned (den E newarg) = Z.of_nat s).
  { subst newarg. cbn [den]. rewrite wbv_unsigned, wlit_ok, of_Z_spec. apply Z.mod_small. rewrite wB_val. unfold NSTATES in Hs. lia. }
  constructor; cbn [s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next close_st set_r0]; try assumption.
  all: unfold set_r0; fold r1; fold newarg; fold priv'.
  - apply IMap.bst_add. exact Sbst.
  - intros k r Hf. destruct (Uint63.eqb k 0%uint63) eqn:EK.
    + apply Uint63.eqb_correct in EK. subst k. rewrite IMap.find_add_same in Hf by exact Sbst. injection Hf as <-. exact RO'.
    + apply Uint63.eqb_false_spec in EK. rewrite IMap.find_add_other in Hf; [| exact Sbst| congruence].
      apply (region_ok_priv_based segs (s_priv st)); [| exact (Sreg k r Hf)].
      destruct (Uint63.eqb k 0%uint63) eqn:X; [apply Uint63.eqb_correct in X; congruence| reflexivity].
  - intros k1 q1 k2 q2 H1 H2 Hne E1 E2.
    rewrite IMap.find_add_other in H1; [| exact Sbst| intros X; subst k1; discriminate E1].
    rewrite IMap.find_add_other in H2; [| exact Sbst| intros X; subst k2; discriminate E2].
    exact (Sdisj k1 q1 k2 q2 H1 H2 Hne E1 E2).
  - intros r g gr c Hf Hg Hc i Hi. rewrite IMap.find_add_same in Hf by exact Sbst. injection Hf as <-.
    exact (proj2 (proj2 (proj2 (ro_cells_in _ _ _ _ _ _ RO' g gr c i Hg Hc Hi) eq_refl))).
  - rewrite SET. rewrite Eops in Sops. unfold ops_hold in *. apply CtrFX.Forall_app3 in Sops as (O1 & O2 & O3).
    apply CtrFX.Forall_app3. split; [exact O1|]. split; [| exact O3].
    cbn [op_id op_args map]. apply H_holds. cbn [pool_holds]. right. left. exists s. split; [exact NEWu|]. split; [exact Hs| exact TB].
  - rewrite SET. rewrite Eops in Sapart. unfold ops_apart in *. apply CtrFX.Forall_app3 in Sapart as (A1 & A2 & A3).
    assert (OTHER : forall o,
              (forall a, Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS (op_id o) (map (den E) (op_args o))) ->
                 ~ in_based E (s_regs st) a /\ ((exists seg, find_segment segs a 1 = Some seg) -> in_priv (s_priv st) a)) ->
              forall a, Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS (op_id o) (map (den E) (op_args o))) ->
                 ~ in_based E (IMap.add 0%uint63 r1 (s_regs st)) a /\ ((exists seg, find_segment segs a 1 = Some seg) -> in_priv priv' a)).
    { intros o Ho a Ha. destruct (Ho a Ha) as [NB IP]. split; [rewrite in_based_add0 by exact Sbst; exact NB|].
      intros SG. apply MONO. apply IP. exact SG. }
    apply CtrFX.Forall_app3. split; [| split].
    + apply Forall_forall. intros o Ho. apply OTHER. exact (proj1 (Forall_forall _ _) A1 o Ho).
    + cbn [op_id op_args map]. intros a Ha. rewrite H_fp in Ha. unfold pool_fp in Ha. rewrite NEWu in Ha.
      replace (Z.of_nat s =? 3) with false in Ha by (symmetry; apply Z.eqb_neq; unfold NSTATES in Hs; lia).
      replace (Z.of_nat s <? 3) with true in Ha by (symmetry; apply Z.ltb_lt; unfold NSTATES in Hs; lia).
      rewrite HBv in Ha.
      assert (R : (FLz <= a < FLz + 8) \/ (FLz + 16 <= a < FLz + 528)).
      { unfold FLz. inversion Ha as [iv l R|iv l R]; subst; [left; cbn in R; lia|].
        inversion R as [iv' l' R'|iv' l' R']; subst; [right; cbn in R'; lia| inversion R']. }
      split.
      * intros (k & rk & Fk & Kk & Rk). rewrite IMap.find_add_other in Fk; [| exact Sbst| intros X; subst k; discriminate Kk].
        pose proof (proj2 (proj2 (ro_valid _ _ _ _ _ _ (Sreg k rk Fk) Kk a Rk))) as NS.
        destruct R as [R|R].
        -- destruct (SEG1 (a - to_Z FL) ltac:(unfold FLz in *; lia)) as [_ (seg & Hseg & _)].
           replace (to_Z FL + (a - to_Z FL)) with a in Hseg by lia. rewrite NS in Hseg. discriminate Hseg.
        -- destruct (SEG2 (a - (FLz + 16)) ltac:(lia)) as [_ (seg & Hseg & _)].
           replace (FLz + 16 + (a - (FLz + 16))) with a in Hseg by lia. rewrite NS in Hseg. discriminate Hseg.
      * intros _. apply INP. exact R.
    + apply Forall_forall. intros o Ho. apply OTHER. exact (proj1 (Forall_forall _ _) A3 o Ho).
  -
    rewrite SET. intros a FA.
    assert (FA' : fx_acc segs E (s_regs st) a).
    { destruct FA as [B|S']; [left; rewrite in_based_add0 in B by exact Sbst; exact B | right; exact S']. }
    destruct (Scov a FA') as [C0|C1]; [left; exact C0| right].
    rewrite Eops in C1. unfold insts in *. rewrite map_app in *. cbn [map] in *.
    apply Exists_app in C1 as [C|C]; [apply Exists_app; left; exact C|].
    apply Exists_cons in C as [C|C]; [exfalso; cbn [fst snd op_id op_args] in C; exact (H_cov _ _ C)|].
    apply Exists_app. right. apply Exists_cons_tl. exact C.
Qed.

Lemma env_ext_refl : forall n E, PlanS.env_ext n E E.
Proof. intros n E. split; [reflexivity|]. intros k Hk. split; reflexivity. Qed.

Lemma ops_hold_find_op : forall E os m md id args,
  ops_hold OPS E os m md -> find_op id os = Some args -> op_holds OPS id (map (den E) args) m md.
Proof.
  intros E os m md id args H Hf. unfold ops_hold in H.
  exact (proj1 (Forall_forall _ _) H (OpI id args) (CtrFX.find_op_In id os args Hf)).
Qed.

Theorem open_sound : forall pc, PlanS.contract_sound segs OPS MP PB (open_c FL segs pc).
Proof.
  intros pc st sts Hpc Happ K E ms md ST HMP HPB HK. cbn [open_c c_apply] in Happ. unfold open_apply in Happ.
  destruct (find_op POOL_ID (s_ops st)) as [[|sel [|? ?]]|] eqn:Hfind; try discriminate Happ.
  destruct (IMap.find 0%uint63 (s_regs st)) as [r0|] eqn:Hr0; [|discriminate Happ].
  destruct (priv_ok FL (s_priv st)) eqn:Hpriv; [|discriminate Happ].
  destruct (Nat.eqb (CtrA.count_op POOL_ID (s_ops st)) 1) eqn:Hcnt; [|discriminate Happ]. apply Nat.eqb_eq in Hcnt.
  destruct (pool_in_image FL segs) eqn:Himg; [|discriminate Happ]. cbn [andb] in Happ.
  destruct (sel_cases (s_facts st) sel) as [ss|] eqn:Hsel; [|discriminate Happ]. injection Happ as <-.

  pose proof (ops_hold_find_op E (s_ops st) (ms_mem ms) md POOL_ID [sel] (so_ops _ _ _ _ _ _ ST) Hfind) as OP.
  apply H_holds in OP. cbn [map pool_holds] in OP.
  assert (REAL : exists s, In s ss /\ (s < NSTATES)%nat /\ Forall (pent_holds segs (ms_mem ms)) (tbl FL s)).
  { unfold sel_cases in Hsel. destruct sel as [w| | | | | | | | | |];
      [ destruct (wltu w (wlit 3%uint63)) eqn:LT; [|discriminate Hsel]; injection Hsel as <-;
        rewrite wltu_ok in LT; apply ValP.ltu_iff in LT; rewrite !wbv_unsigned, wlit_ok in LT; change (to_Z 3%uint63) with 3 in LT;
        cbn [den] in OP; rewrite wbv_unsigned in OP;
        destruct OP as [M|[(s & Hs & Hlt & TB)|(l & Hl & _)]]; [lia| |lia];
        exists s; split; [left; rewrite Hs, Nat2Z.id; reflexivity| split; [exact Hlt| exact TB]] | ..];
      (destruct (decide_ltu (s_facts st) _ (VL (wlit 3%uint63))) as [[|]|] eqn:D; try discriminate Hsel; injection Hsel as <-;
       pose proof (ValP.decide_ltu_sound E (s_facts st) (so_facts _ _ _ _ _ _ ST) _ _ true D) as LT;
       apply ValP.ltu_iff in LT; change (den E (VL (wlit 3%uint63))) with (wbv (wlit 3%uint63)) in LT;
       rewrite wbv_unsigned, wlit_ok in LT; change (to_Z 3%uint63) with 3 in LT;
       destruct OP as [M|[(s & Hs & Hlt & TB)|(l & Hl & _)]]; [lia| |lia];
       exists s; split; [| split; [exact Hlt| exact TB]];
       unfold NSTATES in Hlt; destruct s as [|[|[|s]]]; [left; reflexivity| right; left; reflexivity| right; right; left; reflexivity| lia]). }
  destruct REAL as (s & Hin & Hs & TB).
  apply (HK (open_st FL st r0 s) (in_map _ _ _ Hin) E ms md (env_ext_refl _ E) HMP).
  apply (open_st_ok E st ms md sel r0 s ST Hfind Hcnt Hr0 Hpriv Himg Hs TB).
Qed.

Theorem close_sound : forall pc, PlanS.contract_sound segs OPS MP PB (close_c FL segs pc).
Proof.
  intros pc st sts Hpc Happ K E ms md ST HMP HPB HK. cbn [close_c c_apply] in Happ. unfold close_apply in Happ.
  destruct (find_op POOL_ID (s_ops st)) as [[|[w| | | | | | | | | |] [|? ?]]|] eqn:Hfind; try discriminate Happ.
  destruct (IMap.find 0%uint63 (s_regs st)) as [r0|] eqn:Hr0; [|discriminate Happ].
  destruct (weqb w OPEN_MARK) eqn:Hmark; [|discriminate Happ].
  destruct (Nat.eqb (CtrA.count_op POOL_ID (s_ops st)) 1) eqn:Hcnt; [|discriminate Happ]. apply Nat.eqb_eq in Hcnt.
  destruct (pool_in_image FL segs) eqn:Himg; [|discriminate Happ]. cbn [andb] in Happ.
  destruct (first_state FL segs st NSTATES 0) as [s|] eqn:Hfs; [|discriminate Happ]. injection Happ as <-.
  destruct (first_state_sound st NSTATES 0%nat s Hfs) as [TM Hs].
  apply (HK (close_st FL st r0 s) (or_introl eq_refl) E ms md (env_ext_refl _ E) HMP).
  apply (close_st_ok E st ms md w r0 s ST Hfind Hmark Hcnt Hr0 Himg ltac:(lia) TM).
Qed.

Definition dirtied3 (g : int) : bool :=
  Z.eqb (to_Z g) (FLz / 8) || Z.eqb (to_Z g) (FLz / 8 + 3) || Z.eqb (to_Z g) (FLz / 8 + 27).

Lemma gk12_val : to_Z (gk (PrimInt63.add (HB FL) 8%uint63)) = FLz / 8 + 3.
Proof.
  pose proof FLz_nn as NN. pose proof HB_val as HBv.
  rewrite gk_val, add_small', HBv; change (to_Z 8%uint63) with 8; [| unfold FLz in *; lia].
  replace (FLz + 16 + 8) with (FLz + 3 * 8) by lia. rewrite Z.div_add by lia. reflexivity.
Qed.
Lemma gk204_val : to_Z (gk (PrimInt63.add (HB FL) 200%uint63)) = FLz / 8 + 27.
Proof.
  pose proof FLz_nn as NN. pose proof HB_val as HBv.
  rewrite gk_val, add_small', HBv; change (to_Z 200%uint63) with 200; [| unfold FLz in *; lia].
  replace (FLz + 16 + 200) with (FLz + 27 * 8) by lia. rewrite Z.div_add by lia. reflexivity.
Qed.

Lemma ptbl_facts : forall l e, In e (ptbl FL l) ->
  0 <= to_Z (pe_i e) /\ 0 < to_Z (pe_w e) /\ to_Z (pe_i e) + to_Z (pe_w e) <= 8
  /\ 8 * keyZ (pe_g e) + to_Z (pe_i e) = to_Z (pe_addr e)
  /\ to_Z (pe_g e) < 2 ^ 62
  /\ ((FLz <= to_Z (pe_addr e) /\ to_Z (pe_addr e) + to_Z (pe_w e) <= FLz + 8)
      \/ (FLz + 24 <= to_Z (pe_addr e) /\ to_Z (pe_addr e) + to_Z (pe_w e) <= FLz + 32)
      \/ (FLz + 216 <= to_Z (pe_addr e) /\ to_Z (pe_addr e) + to_Z (pe_w e) <= FLz + 224))
  /\ dirtied3 (pe_g e) = true.
Proof.
  pose proof FLz_nn as NN. pose proof HB_val as HBv.
  assert (G0 : to_Z (gk FL) = FLz / 8) by apply gk_val.
  pose proof gk12_val as G1. pose proof gk204_val as G2.
  assert (D8 : FLz = 8 * (FLz / 8)) by (pose proof (Z.div_mod FLz 8 ltac:(lia)); unfold FLz in *; lia).
  intros l e Hin.
  assert (CASES : e = PE (gk FL) 0%uint63 8%uint63 (pe_v e)
               \/ e = PE (gk (PrimInt63.add (HB FL) 8%uint63)) 4%uint63 4%uint63 (pe_v e)
               \/ e = PE (gk (PrimInt63.add (HB FL) 200%uint63)) 4%uint63 4%uint63 (pe_v e)).
  { destruct l as [|[|l']]; cbn [ptbl] in Hin;
      repeat (destruct Hin as [<-|Hin]; [cbn [pe_v]; tauto|]); destruct Hin. }
  destruct CASES as [-> |[-> | ->]]; cbn [pe_g pe_i pe_w];
    change (to_Z 0%uint63) with 0; change (to_Z 4%uint63) with 4; change (to_Z 8%uint63) with 8.
  - rewrite keyZ_small by lia. unfold pe_addr; cbn [pe_g pe_i].
    rewrite add_small'; rewrite lsl_spec, G0; change (2 ^ to_Z 3%uint63) with 8; change (to_Z 0%uint63) with 0; rewrite wB_val, Z.mod_small; try lia.
    repeat split; try lia. unfold dirtied3. rewrite G0, Z.eqb_refl. reflexivity.
  - rewrite keyZ_small by lia. unfold pe_addr; cbn [pe_g pe_i].
    rewrite add_small'; rewrite lsl_spec, G1; change (2 ^ to_Z 3%uint63) with 8; change (to_Z 4%uint63) with 4; rewrite wB_val, Z.mod_small; try lia.
    repeat split; try lia. unfold dirtied3. rewrite G1, Z.eqb_refl. rewrite orb_true_r. reflexivity.
  - rewrite keyZ_small by lia. unfold pe_addr; cbn [pe_g pe_i].
    rewrite add_small'; rewrite lsl_spec, G2; change (2 ^ to_Z 3%uint63) with 8; change (to_Z 4%uint63) with 4; rewrite wB_val, Z.mod_small; try lia.
    repeat split; try lia. unfold dirtied3. rewrite G2, Z.eqb_refl. apply orb_true_r.
Qed.

Lemma gnodup_ptbl : forall l, gnodup (ptbl FL l).
Proof.
  pose proof FLz_nn as NN.
  assert (G0 : to_Z (gk FL) = FLz / 8) by apply gk_val.
  pose proof gk12_val as G1. pose proof gk204_val as G2.
  assert (NE : forall a b, to_Z a <> to_Z b -> a <> b) by (intros a b Hne Heq; apply Hne; rewrite Heq; reflexivity).
  intros [|[|l]]; cbn [ptbl gnodup pe_g]; repeat split; intros e' He';
    repeat (destruct He' as [<-|He']; [cbn [pe_g]; apply NE; rewrite ?G0, ?G1, ?G2; lia|]); destruct He'.
Qed.

Lemma ptbl_wok : forall l e, In e (ptbl FL l) -> MemP.wok (pe_w e).
Proof.
  intros [|[|l]] e Hin; cbn [ptbl] in Hin;
    repeat (destruct Hin as [<-|Hin]; [cbn [pe_w]; unfold MemP.wok; first [right; right; right; reflexivity | right; right; left; reflexivity] |]); destruct Hin.
Qed.

Lemma dirty3_sound : forall priv E m r,
  region_ok segs priv E m 0%uint63 r ->
  region_ok segs priv E m 0%uint63 (dirty3 FL r)
  /\ (forall g, IMap.find g (rg_cells (dirty3 FL r)) = if dirtied3 g then Some (Gran true []) else IMap.find g (rg_cells r)).
Proof.
  intros priv E m r RO. pose proof FLz_nn as NN. unfold FLz in *.
  pose proof gkFL_val as V0. pose proof gk12_val as V1. pose proof gk204_val as V2. unfold FLz in *.
  assert (B0 : to_Z (gk FL) + Z.of_nat 1 < wB) by (rewrite V0, wB_val; cbn [Z.of_nat]; lia).
  assert (B1 : to_Z (gk (PrimInt63.add (HB FL) 8%uint63)) + Z.of_nat 1 < wB) by (rewrite V1, wB_val; cbn [Z.of_nat]; lia).
  assert (B2 : to_Z (gk (PrimInt63.add (HB FL) 200%uint63)) + Z.of_nat 1 < wB) by (rewrite V2, wB_val; cbn [Z.of_nat]; lia).
  pose proof (CtrFX.region_dirty_sound segs priv E m 0%uint63 r _ 1 B2 RO) as R2.
  pose proof (CtrFX.region_dirty_sound segs priv E m 0%uint63 _ _ 1 B1 R2) as R1. cbn [rg_lo rg_hi rg_w rg_bg rg_cells] in R1.
  pose proof (CtrFX.region_dirty_sound segs priv E m 0%uint63 _ _ 1 B0 R1) as R0. cbn [rg_lo rg_hi rg_w rg_bg rg_cells] in R0.
  split; [exact R0|].
  intros g. unfold dirty3. cbn [rg_cells].
  destruct (CtrFX.dirty_range_spec _ 1 (rg_cells r) (ro_bst _ _ _ _ _ _ RO) B2) as [Bd2 F2].
  destruct (CtrFX.dirty_range_spec _ 1 _ Bd2 B1) as [Bd1 F1].
  destruct (CtrFX.dirty_range_spec _ 1 _ Bd1 B0) as [Bd0 F0].
  rewrite F0, F1, F2, V0, V1, V2. unfold dirtied3, FLz. change (Z.of_nat 1) with 1.
  destruct (Z.eqb_spec (to_Z g) (to_Z FL / 8)); destruct (Z.eqb_spec (to_Z g) (to_Z FL / 8 + 3)); destruct (Z.eqb_spec (to_Z g) (to_Z FL / 8 + 27));
  destruct (Z.leb_spec (to_Z FL / 8) (to_Z g)); destruct (Z.ltb_spec (to_Z g) (to_Z FL / 8 + 1));
  destruct (Z.leb_spec (to_Z FL / 8 + 3) (to_Z g)); destruct (Z.ltb_spec (to_Z g) (to_Z FL / 8 + 3 + 1));
  destruct (Z.leb_spec (to_Z FL / 8 + 27) (to_Z g)); destruct (Z.ltb_spec (to_Z g) (to_Z FL / 8 + 27 + 1)); cbn [andb orb];
  first [reflexivity | exfalso; lia].
Qed.

Lemma div8_in : forall o G, 8 * G <= o < 8 * G + 8 -> o / 8 = G.
Proof. intros o G H. symmetry. apply Z.div_unique with (r := o - 8 * G); lia. Qed.
Lemma div8_cell : forall K idx i, 0 <= idx -> 0 <= i -> idx + i < 8 -> (8 * K + idx + i) / 8 = K.
Proof. intros K idx i H1 H2 H3. symmetry. apply Z.div_unique with (r := idx + i); lia. Qed.
Lemma in8_of_div : forall o G, o / 8 = G -> 8 * G <= o < 8 * G + 8.
Proof. intros o G H. pose proof (Z.div_mod o 8 ltac:(lia)). pose proof (Z.mod_pos_bound o 8 ltac:(lia)). lia. Qed.

Lemma gnext_val : forall g0, 0 <= to_Z g0 < 2 ^ 62 - 1 -> to_Z (gnext g0) = to_Z g0 + 1.
Proof. intros g0 Hg0. unfold gnext. rewrite add_small'; change (to_Z 1%uint63) with 1; [reflexivity| lia]. Qed.
Lemma rm1_spec : forall g0 g, 0 <= to_Z g0 < 2 ^ 62 - 1 -> (PrimInt63.leb g0 g && PrimInt63.ltb g (gnext g0)) = Z.eqb (to_Z g) (to_Z g0).
Proof.
  intros g0 g Hg0. pose proof (gnext_val g0 Hg0) as GN.
  destruct (Uint63.lebP g0 g); destruct (Uint63.ltbP g (gnext g0)); destruct (Z.eqb_spec (to_Z g) (to_Z g0)); cbn [andb];
    rewrite ?GN in *; first [reflexivity | exfalso; lia].
Qed.

Lemma strip_gran : forall priv E m r (g0 : int) (iv : int * int),
  region_ok segs priv E m 0%uint63 r ->
  0 <= to_Z g0 < 2 ^ 62 - 1 -> to_Z (fst iv) = 8 * to_Z g0 -> to_Z (snd iv) = 8 * to_Z g0 + 8 ->
  let r' := Region (rg_lo r) (rg_hi r) (rg_w r) (rg_bg r) (IMap.remove_range g0 (gnext g0) (rg_cells r)) in
  region_ok segs (iv :: priv) E m 0%uint63 r'
  /\ (forall g, IMap.find g (rg_cells r') = if Z.eqb (to_Z g) (to_Z g0) then None else IMap.find g (rg_cells r)).
Proof.
  intros priv E m r g0 iv RO Hg0 Hlo Hhi. cbv zeta. cbn [rg_cells].
  pose proof (fun g => rm1_spec g0 g Hg0) as RMS.
  pose proof RO as [Rbst Rrange Rvalid Rcells Rin Rbg].
  assert (F : forall g, IMap.find g (IMap.remove_range g0 (gnext g0) (rg_cells r)) = if Z.eqb (to_Z g) (to_Z g0) then None else IMap.find g (rg_cells r)).
  { intros g. rewrite IMap.find_remove_range by exact Rbst. rewrite RMS. reflexivity. }
  split; [| exact F].
  assert (SUB : forall g gr, IMap.find g (IMap.remove_range g0 (gnext g0) (rg_cells r)) = Some gr ->
                IMap.find g (rg_cells r) = Some gr /\ to_Z g <> to_Z g0).
  { intros g gr Hf. rewrite F in Hf. destruct (Z.eqb_spec (to_Z g) (to_Z g0)); [discriminate| auto]. }
  assert (INIV : forall o, to_Z (fst iv) <= o < to_Z (snd iv) -> o / 8 = to_Z g0).
  { intros o Ho. rewrite Hlo, Hhi in Ho. exact (div8_in o (to_Z g0) Ho). }
  constructor; cbn [rg_cells rg_lo rg_hi rg_w rg_bg].
  - apply IMap.remove_range_bst. exact Rbst.
  - intros K; discriminate K.
  - intros K; discriminate K.
  - intros g gr Hf. apply Rcells. apply SUB. exact Hf.
  - intros g gr c i Hf Hc Hi. destruct (SUB g gr Hf) as [Hf0 Hne]. pose proof (Rin g gr c i Hf0 Hc Hi) as [P1 P2].
    split; [exact P1|]. intros K. destruct (P2 K) as (Q1 & Q2 & Q3). split; [exact Q1|]. split; [exact Q2|].
    intros IP. unfold in_priv in IP. inversion IP as [iv' l R|iv' l R]; subst; [| exact (Q3 R)].
    cbv beta in R. pose proof (INIV _ R) as D.
    pose proof (proj2 (Rcells g gr Hf0)) as CF. pose proof (proj1 (Forall_forall _ _) CF c Hc) as (W1 & W2 & W3 & _).
    rewrite (div8_cell (keyZ g) (to_Z (c_idx c)) i) in D by (clear - W1 W2 W3 Hi; lia).
    pose proof (MemP.keyZ_range g) as KR. apply Hne. rewrite (keyZ_nonneg_toZ g) by (clear - D Hg0; lia). exact D.
  - intros o H1 H2 U. unfold bg_byte. cbn [rg_bg]. fold (bg_byte segs E 0%uint63 r o). apply Rbg; [exact H1| |].
    + intros K. destruct (H2 K) as (Q1 & Q2 & Q3). split; [exact Q1|]. split; [exact Q2|]. intros IP. apply Q3. unfold in_priv. right. exact IP.
    + intros g gr Hg Hf. destruct (Z.eqb_spec (to_Z g) (to_Z g0)) as [EQ|NE].
      * exfalso. destruct (H2 eq_refl) as (_ & _ & Q3). apply Q3. unfold in_priv. left.
        rewrite Hlo, Hhi. assert (KG : keyZ g = to_Z g) by (apply keyZ_small; clear - EQ Hg0; lia).
        apply in8_of_div. rewrite <- Hg, KG. exact EQ.
      * apply (U g gr Hg). rewrite F. destruct (Z.eqb_spec (to_Z g) (to_Z g0)); [contradiction| exact Hf].
Qed.

Lemma iv_p12_val : to_Z (fst (iv_p12 FL)) = FLz + 24 /\ to_Z (snd (iv_p12 FL)) = FLz + 32.
Proof.
  pose proof FLz_nn as NN. pose proof HB_val as HBv. unfold iv_p12. cbn [fst snd].
  split; rewrite add_small'; rewrite HBv; change (to_Z 8%uint63) with 8; change (to_Z 16%uint63) with 16; unfold FLz in *; lia.
Qed.
Lemma iv_p204_val : to_Z (fst (iv_p204 FL)) = FLz + 216 /\ to_Z (snd (iv_p204 FL)) = FLz + 224.
Proof.
  pose proof FLz_nn as NN. pose proof HB_val as HBv. unfold iv_p204. cbn [fst snd].
  split; rewrite add_small'; rewrite HBv; change (to_Z 200%uint63) with 200; change (to_Z 208%uint63) with 208; unfold FLz in *; lia.
Qed.

Definition in3 (o : Z) : Prop := (FLz <= o < FLz + 8) \/ (FLz + 24 <= o < FLz + 32) \/ (FLz + 216 <= o < FLz + 224).

Lemma unpriv3_sub : forall priv o, in_priv (unpriv3 FL priv) o -> in_priv priv o.
Proof. intros priv o H. unfold in_priv, unpriv3 in *. apply Exists_exists in H as (iv & Hin & R). apply filter_In in Hin as [Hin _]. apply Exists_exists. exists iv. auto. Qed.

Lemma unpriv3_lost : forall priv o, in_priv priv o -> ~ in_priv (unpriv3 FL priv) o -> in3 o.
Proof.
  intros priv o H Hn. unfold in_priv in H. apply Exists_exists in H as (iv & Hin & R).
  destruct (is_park_iv FL iv) eqn:E.
  - unfold is_park_iv in E. apply orb_prop in E. destruct E as [E|E]; [apply orb_prop in E; destruct E as [E|E]|]; apply iv_eqb_eq in E; subst iv.
    + left. destruct iv_fl_val as [A B]. rewrite A, B in R. exact R.
    + right. left. destruct iv_p12_val as [A B]. rewrite A, B in R. exact R.
    + right. right. destruct iv_p204_val as [A B]. rewrite A, B in R. exact R.
  - exfalso. apply Hn. unfold in_priv, unpriv3. apply Exists_exists. exists iv. split; [| exact R].
    apply filter_In. split; [exact Hin|]. rewrite E. reflexivity.
Qed.

Lemma priv3_ok_public : forall priv, priv3_ok FL priv = true -> forall o, in3 o -> ~ in_priv (unpriv3 FL priv) o.
Proof.
  intros priv H o Ho. unfold priv3_ok in H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply negb_true_iff in H1. apply negb_true_iff in H2. apply negb_true_iff in H3. pose proof FLz_nn as NN. pose proof HB_val as HBv.
  destruct iv_p12_val as [A12 _]. destruct iv_p204_val as [A204 _]. unfold iv_p12, iv_p204 in A12, A204. cbn [fst] in A12, A204.
  destruct Ho as [Ho|[Ho|Ho]].
  - apply (MemP.in_priv_b_false _ FL 8%uint63); [exact H1| change (to_Z 8%uint63) with 8; unfold two63, FLz in *; lia| change (to_Z 8%uint63) with 8; unfold FLz in *; lia].
  - apply (MemP.in_priv_b_false _ (PrimInt63.add (HB FL) 8%uint63) 8%uint63); [exact H2| change (to_Z 8%uint63) with 8; rewrite A12; unfold two63, FLz in *; lia| change (to_Z 8%uint63) with 8; rewrite A12; unfold FLz in *; lia].
  - apply (MemP.in_priv_b_false _ (PrimInt63.add (HB FL) 200%uint63) 8%uint63); [exact H3| change (to_Z 8%uint63) with 8; rewrite A204; unfold two63, FLz in *; lia| change (to_Z 8%uint63) with 8; rewrite A204; unfold FLz in *; lia].
Qed.

Lemma first_layout_sound : forall st n l0 l, first_layout FL segs st n l0 = Some l ->
  ptbl_matches FL segs st l = true /\ (l < l0 + n)%nat.
Proof.
  intros st n. induction n as [|n IH]; intros l0 l H; cbn [first_layout] in H; [discriminate|].
  destruct (ptbl_matches FL segs st l0) eqn:M.
  - injection H as <-. split; [exact M| lia].
  - destruct (IH (S l0) l H) as [A B]. split; [exact A| lia].
Qed.

Lemma park_sel_val : forall l, (l < NPARK)%nat -> w2Z (park_sel l) = 4 + Z.of_nat l.
Proof.
  intros l Hl. unfold park_sel, NPARK in *. rewrite wlit_ok.
  assert (T : to_Z (Uint63.of_Z (Z.of_nat l)) = Z.of_nat l) by (rewrite of_Z_spec; apply Z.mod_small; rewrite wB_val; lia).
  rewrite add_small'; rewrite T; change (to_Z 4%uint63) with 4; lia.
Qed.

Lemma D8_val : FLz = 8 * (FLz / 8).
Proof. pose proof (Z.div_mod FLz 8 ltac:(lia)). unfold FLz in *. lia. Qed.

Lemma in3_pool : forall o, in3 o -> (FLz <= o < FLz + 8) \/ (FLz + 16 <= o < FLz + 528).
Proof. intros o [H|[H|H]]; lia. Qed.

Lemma in3_dirtied : forall o, in3 o -> 0 <= o / 8 < 2 ^ 62 /\ (o / 8 = FLz / 8 \/ o / 8 = FLz / 8 + 3 \/ o / 8 = FLz / 8 + 27).
Proof.
  intros o Ho. pose proof FLz_nn as NN. pose proof D8_val as D8. assert (LT : FLz + 1024 < 2 ^ 62) by (unfold FLz; exact H_FLB).
  destruct Ho as [H|[H|H]].
  - assert (Q : o / 8 = FLz / 8) by (apply div8_in; lia). rewrite Q. split; [split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]| left; reflexivity].
  - assert (Q : o / 8 = FLz / 8 + 3) by (apply div8_in; lia). rewrite Q. split; [split; [pose proof (Z.div_pos FLz 8 NN ltac:(lia)); lia| assert (FLz / 8 < 2 ^ 59) by (apply Z.div_lt_upper_bound; lia); lia]| right; left; reflexivity].
  - assert (Q : o / 8 = FLz / 8 + 27) by (apply div8_in; lia). rewrite Q. split; [split; [pose proof (Z.div_pos FLz 8 NN ltac:(lia)); lia| assert (FLz / 8 < 2 ^ 59) by (apply Z.div_lt_upper_bound; lia); lia]| right; right; reflexivity].
Qed.

Lemma park_st_ok : forall E st ms md w r0 l,
  st_ok segs OPS E st ms md ->
  find_op POOL_ID (s_ops st) = Some [VL w] -> weqb w OPEN_MARK = true ->
  CtrA.count_op POOL_ID (s_ops st) = 1%nat ->
  IMap.find 0%uint63 (s_regs st) = Some r0 ->
  pool_in_image FL segs = true ->
  (l < NPARK)%nat -> ptbl_matches FL segs st l = true ->
  st_ok segs OPS E (park_st FL st r0 l) ms md.
Proof.
  intros E st ms md w r0 l ST Hfind Hmark Hcnt Hr0 Himg Hl TM.
  pose proof ST as [Spc Sx0 Sregs Sfregs Ssvc Sresv Sfcsr Srom Szero Sbst Sreg Sdisj Spub Sfacts Sops Sapart Smf Scov Sminv].
  pose proof FLz_nn as NN. pose proof HB_val as HBv. pose proof D8_val as D8.
  unfold pool_in_image in Himg. apply andb_prop in Himg as [Img1 Img2].
  destruct (MemP.abs_writable_sound segs (to_Z FL) 8 ltac:(lia) ltac:(lia) Img1) as [_ SEG1].
  destruct (MemP.abs_writable_sound segs (to_Z (HB FL)) 512 ltac:(rewrite HBv; lia) ltac:(lia) Img2) as [_ SEG2]. rewrite HBv in SEG2.
  assert (LT62 : FLz + 528 < 2 ^ 62) by (unfold FLz; lia).

  assert (TB : Forall (pent_holds segs (ms_mem ms)) (ptbl FL l)).
  { apply Forall_forall. intros e He. unfold ptbl_matches in TM.
    pose proof (proj1 (forallb_forall _ _) TM e He) as TMe.
    destruct (ptbl_facts l e He) as (C1 & C2 & C3 & C4 & C5 & C6 & C7).
    apply (pent_matches_sound E st ms md e ST); [exact TMe| apply (ptbl_wok l e He)| unfold FLz in *; lia]. }
  set (priv' := iv_fl FL :: iv_p12 FL :: iv_p204 FL :: s_priv st).
  assert (MONO : forall o, in_priv (s_priv st) o -> in_priv priv' o) by (intros o H; unfold priv', in_priv; right; right; right; exact H).
  assert (INP : forall o, in3 o -> in_priv priv' o).
  { intros o Ho. unfold priv', in_priv. destruct iv_fl_val as [A1 A2]. destruct iv_p12_val as [B1 B2]. destruct iv_p204_val as [C1 C2].
    destruct Ho as [Ho|[Ho|Ho]]; [left; rewrite A1, A2; exact Ho| right; left; rewrite B1, B2; exact Ho| right; right; left; rewrite C1, C2; exact Ho]. }

  pose proof (Sreg 0%uint63 r0 Hr0) as RO0.
  pose proof gkFL_val as V0. pose proof gk12_val as V1. pose proof gk204_val as V2.
  assert (Q59 : 0 <= FLz / 8 < 2 ^ 59) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
  destruct iv_fl_val as [A1 A2]. destruct iv_p12_val as [B1 B2]. destruct iv_p204_val as [C1 C2].
  destruct (strip_gran (s_priv st) E (ms_mem ms) r0 (gk (PrimInt63.add (HB FL) 200%uint63)) (iv_p204 FL) RO0) as [ROa Fa];
    [rewrite V2; lia| rewrite V2, C1; lia| rewrite V2, C2; lia|].
  destruct (strip_gran _ E (ms_mem ms) _ (gk (PrimInt63.add (HB FL) 8%uint63)) (iv_p12 FL) ROa) as [ROb Fb];
    [rewrite V1; lia| rewrite V1, B1; lia| rewrite V1, B2; lia|].
  destruct (strip_gran _ E (ms_mem ms) _ (gk FL) (iv_fl FL) ROb) as [ROc Fc];
    [rewrite V0; lia| rewrite V0, A1; lia| rewrite V0, A2; lia|].
  cbn [rg_lo rg_hi rg_w rg_bg rg_cells] in ROb, Fb, ROc, Fc.
  change (Region (rg_lo r0) (rg_hi r0) (rg_w r0) (rg_bg r0)
            (IMap.remove_range (gk FL) (gnext (gk FL))
               (IMap.remove_range (gk (PrimInt63.add (HB FL) 8%uint63)) (gnext (gk (PrimInt63.add (HB FL) 8%uint63)))
                  (IMap.remove_range (gk (PrimInt63.add (HB FL) 200%uint63)) (gnext (gk (PrimInt63.add (HB FL) 200%uint63))) (rg_cells r0)))))
    with (strip3 FL r0) in ROc.
  fold priv' in ROc. set (r1 := strip3 FL r0) in *.

  pose proof (CtrFX.find_op_unique POOL_ID (s_ops st) [VL w] Hfind Hcnt) as (l1 & l2 & Eops & N1 & N2).
  set (newarg := VL (park_sel l)).
  assert (SET : set_op POOL_ID [newarg] (s_ops st) = l1 ++ OpI POOL_ID [newarg] :: l2).
  { rewrite Eops. apply CtrFX.set_op_split. exact N1. }
  assert (NEWu : bv_unsigned (den E newarg) = 4 + Z.of_nat l).
  { subst newarg. cbn [den]. rewrite wbv_unsigned. apply park_sel_val. exact Hl. }
  constructor; cbn [s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next park_st set_r0]; try assumption.
  all: unfold set_r0; fold r1; fold newarg; fold priv'.
  - apply IMap.bst_add. exact Sbst.
  - intros k r Hf. destruct (Uint63.eqb k 0%uint63) eqn:EK.
    + apply Uint63.eqb_correct in EK. subst k. rewrite IMap.find_add_same in Hf by exact Sbst. injection Hf as <-. exact ROc.
    + apply Uint63.eqb_false_spec in EK. rewrite IMap.find_add_other in Hf; [| exact Sbst| congruence].
      apply (region_ok_priv_based segs (s_priv st)); [| exact (Sreg k r Hf)].
      destruct (Uint63.eqb k 0%uint63) eqn:X; [apply Uint63.eqb_correct in X; congruence| reflexivity].
  - intros k1 q1 k2 q2 H1 H2 Hne E1 E2.
    rewrite IMap.find_add_other in H1; [| exact Sbst| intros X; subst k1; discriminate E1].
    rewrite IMap.find_add_other in H2; [| exact Sbst| intros X; subst k2; discriminate E2].
    exact (Sdisj k1 q1 k2 q2 H1 H2 Hne E1 E2).
  - intros r g gr c Hf Hg Hc i Hi. rewrite IMap.find_add_same in Hf by exact Sbst. injection Hf as <-.
    exact (proj2 (proj2 (proj2 (ro_cells_in _ _ _ _ _ _ ROc g gr c i Hg Hc Hi) eq_refl))).
  - rewrite SET. rewrite Eops in Sops. unfold ops_hold in *. apply CtrFX.Forall_app3 in Sops as (O1 & O2 & O3).
    apply CtrFX.Forall_app3. split; [exact O1|]. split; [| exact O3].
    cbn [op_id op_args map]. apply H_holds. cbn [pool_holds]. right. right. exists l. split; [exact NEWu|]. split; [exact Hl| exact TB].
  - rewrite SET. rewrite Eops in Sapart. unfold ops_apart in *. apply CtrFX.Forall_app3 in Sapart as (A1' & A2' & A3').
    assert (OTHER : forall o,
              (forall a, Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS (op_id o) (map (den E) (op_args o))) ->
                 ~ in_based E (s_regs st) a /\ ((exists seg, find_segment segs a 1 = Some seg) -> in_priv (s_priv st) a)) ->
              forall a, Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS (op_id o) (map (den E) (op_args o))) ->
                 ~ in_based E (IMap.add 0%uint63 r1 (s_regs st)) a /\ ((exists seg, find_segment segs a 1 = Some seg) -> in_priv priv' a)).
    { intros o Ho a Ha. destruct (Ho a Ha) as [NB IP]. split; [rewrite in_based_add0 by exact Sbst; exact NB|].
      intros SG. apply MONO. apply IP. exact SG. }
    apply CtrFX.Forall_app3. split; [| split].
    + apply Forall_forall. intros o Ho. apply OTHER. exact (proj1 (Forall_forall _ _) A1' o Ho).
    + cbn [op_id op_args map]. intros a Ha. rewrite H_fp in Ha. unfold pool_fp in Ha. rewrite NEWu in Ha.
      replace (4 + Z.of_nat l =? 3) with false in Ha by (symmetry; apply Z.eqb_neq; lia).
      replace (4 + Z.of_nat l <? 3) with false in Ha by (symmetry; apply Z.ltb_ge; lia).
      rewrite HBv in Ha.
      assert (R : in3 a).
      { unfold in3, FLz. inversion Ha as [iv l0 R|iv l0 R]; subst; [left; cbn in R; lia|].
        inversion R as [iv' l' R'|iv' l' R']; subst; [right; left; cbn in R'; lia|].
        inversion R' as [iv'' l'' R''|iv'' l'' R'']; subst; [right; right; cbn in R''; lia| inversion R'']. }
      split.
      * intros (k & rk & Fk & Kk & Rk). rewrite IMap.find_add_other in Fk; [| exact Sbst| intros X; subst k; discriminate Kk].
        pose proof (proj2 (proj2 (ro_valid _ _ _ _ _ _ (Sreg k rk Fk) Kk a Rk))) as NS.
        destruct (in3_pool a R) as [R1|R1].
        -- destruct (SEG1 (a - to_Z FL) ltac:(unfold FLz in *; lia)) as [_ (seg & Hseg & _)].
           replace (to_Z FL + (a - to_Z FL)) with a in Hseg by lia. rewrite NS in Hseg. discriminate Hseg.
        -- destruct (SEG2 (a - (FLz + 16)) ltac:(lia)) as [_ (seg & Hseg & _)].
           replace (FLz + 16 + (a - (FLz + 16))) with a in Hseg by lia. rewrite NS in Hseg. discriminate Hseg.
      * intros _. apply INP. exact R.
    + apply Forall_forall. intros o Ho. apply OTHER. exact (proj1 (Forall_forall _ _) A3' o Ho).
  - rewrite SET. intros a FA.
    assert (FA' : fx_acc segs E (s_regs st) a).
    { destruct FA as [B|S']; [left; rewrite in_based_add0 in B by exact Sbst; exact B | right; exact S']. }
    destruct (Scov a FA') as [C0|C1']; [left; exact C0| right].
    rewrite Eops in C1'. unfold insts in *. rewrite map_app in *. cbn [map] in *.
    apply Exists_app in C1' as [C|C]; [apply Exists_app; left; exact C|].
    apply Exists_cons in C as [C|C]; [exfalso; cbn [fst snd op_id op_args] in C; exact (H_cov _ _ C)|].
    apply Exists_app. right. apply Exists_cons_tl. exact C.
Qed.

Lemma unpark_st_ok : forall E st ms md sel r0 l,
  st_ok segs OPS E st ms md ->
  find_op POOL_ID (s_ops st) = Some [sel] ->
  CtrA.count_op POOL_ID (s_ops st) = 1%nat ->
  IMap.find 0%uint63 (s_regs st) = Some r0 ->
  priv3_ok FL (s_priv st) = true ->
  pool_in_image FL segs = true ->
  (l < NPARK)%nat ->
  Forall (pent_holds segs (ms_mem ms)) (ptbl FL l) ->
  st_ok segs OPS E (unpark_st FL st r0 l) ms md.
Proof.
  intros E st ms md sel r0 l ST Hfind Hcnt Hr0 Hpriv Himg Hl TB.
  pose proof ST as [Spc Sx0 Sregs Sfregs Ssvc Sresv Sfcsr Srom Szero Sbst Sreg Sdisj Spub Sfacts Sops Sapart Smf Scov Sminv].
  pose proof FLz_nn as NN.
  unfold pool_in_image in Himg. apply andb_prop in Himg as [Img1 Img2].
  destruct (MemP.abs_writable_sound segs (to_Z FL) 8 ltac:(lia) ltac:(lia) Img1) as [_ SEG1].
  pose proof HB_val as HBv.
  destruct (MemP.abs_writable_sound segs (to_Z (HB FL)) 512 ltac:(rewrite HBv; lia) ltac:(lia) Img2) as [_ SEG2]. rewrite HBv in SEG2.
  assert (LT62 : FLz + 528 < 2 ^ 62) by (unfold FLz; lia).
  set (priv' := unpriv3 FL (s_priv st)).
  pose proof (Sreg 0%uint63 r0 Hr0) as RO0.
  destruct (dirty3_sound (s_priv st) E (ms_mem ms) r0 RO0) as [RO1 F1].
  assert (RO1' : region_ok segs priv' E (ms_mem ms) 0%uint63 (dirty3 FL r0)).
  { apply (region0_priv_change segs (s_priv st) priv'); [exact RO1| |].
    - intros g gr c i Hf Hc Hi IP. apply unpriv3_sub in IP.
      exact (proj2 (proj2 (proj2 (ro_cells_in _ _ _ _ _ _ RO1 g gr c i Hf Hc Hi) eq_refl)) IP).
    - intros o IP NIP. pose proof (unpriv3_lost (s_priv st) o IP NIP) as R3.
      destruct (in3_dirtied o R3) as [RNG CASES].
      destruct (of_Z_keyZ (o / 8) RNG) as [K T].
      exists (Uint63.of_Z (o / 8)), (Gran true []). split; [exact K|]. split; [| reflexivity].
      rewrite F1. unfold dirtied3. rewrite T.
      destruct CASES as [Q|[Q|Q]]; rewrite Q, ?Z.eqb_refl, ?orb_true_r; reflexivity. }
  destruct (mat_sound priv' E (ms_mem ms) (ptbl FL l) (dirty3 FL r0) Szero RO1' (gnodup_ptbl l)) as [RO2 F2].
  { intros e He. destruct (ptbl_facts l e He) as (C1 & C2 & C3 & C4 & C5 & C6 & C7).
    split; [rewrite F1, C7; reflexivity|]. split; [exact C1|]. split; [exact C2|]. split; [exact C3|]. split.
    - intros i Hi. rewrite C4. apply (proj1 (Forall_forall _ _) TB e He i Hi).
    - intros i Hi. cbv zeta. rewrite C4.
      assert (R3 : in3 (to_Z (pe_addr e) + i)) by (unfold in3; lia).
      split; [rewrite MemP.half63; unfold FLz in *; lia|]. split.
      + destruct (in3_pool _ R3) as [C6'|C6'].
        * destruct (SEG1 (to_Z (pe_addr e) + i - to_Z FL) ltac:(unfold FLz in *; lia)) as [_ (seg & Hseg & _)].
          exists seg. replace (to_Z (pe_addr e) + i) with (to_Z FL + (to_Z (pe_addr e) + i - to_Z FL)) by lia. exact Hseg.
        * destruct (SEG2 (to_Z (pe_addr e) + i - (FLz + 16)) ltac:(unfold FLz in *; lia)) as [_ (seg & Hseg & _)].
          exists seg. replace (to_Z (pe_addr e) + i) with (FLz + 16 + (to_Z (pe_addr e) + i - (FLz + 16))) by lia. exact Hseg.
      + apply priv3_ok_public; [exact Hpriv| exact R3]. }
  set (r2 := mat (ptbl FL l) (dirty3 FL r0)) in *.

  pose proof (CtrFX.find_op_unique POOL_ID (s_ops st) [sel] Hfind Hcnt) as (l1 & l2 & Eops & N1 & N2).
  assert (SET : set_op POOL_ID [VL (OPEN_MARK)] (s_ops st) = l1 ++ OpI POOL_ID [VL OPEN_MARK] :: l2).
  { rewrite Eops. apply CtrFX.set_op_split. exact N1. }
  assert (MARKu : bv_unsigned (den E (VL OPEN_MARK)) = 3).
  { cbn [den]. unfold OPEN_MARK. rewrite wbv_unsigned, wlit_ok. reflexivity. }
  constructor; cbn [s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next unpark_st set_r0]; try assumption.
  all: unfold set_r0; fold r2.
  - apply IMap.bst_add. exact Sbst.
  - intros k r Hf. destruct (Uint63.eqb k 0%uint63) eqn:EK.
    + apply Uint63.eqb_correct in EK. subst k. rewrite IMap.find_add_same in Hf by exact Sbst. injection Hf as <-. exact RO2.
    + apply Uint63.eqb_false_spec in EK. rewrite IMap.find_add_other in Hf; [| exact Sbst| congruence].
      apply (region_ok_priv_based segs (s_priv st)); [| exact (Sreg k r Hf)].
      destruct (Uint63.eqb k 0%uint63) eqn:X; [apply Uint63.eqb_correct in X; congruence| reflexivity].
  - intros k1 q1 k2 q2 H1 H2 Hne E1 E2.
    rewrite IMap.find_add_other in H1; [| exact Sbst| intros X; subst k1; discriminate E1].
    rewrite IMap.find_add_other in H2; [| exact Sbst| intros X; subst k2; discriminate E2].
    exact (Sdisj k1 q1 k2 q2 H1 H2 Hne E1 E2).
  - intros r g gr c Hf Hg Hc i Hi. rewrite IMap.find_add_same in Hf by exact Sbst. injection Hf as <-.
    exact (proj2 (proj2 (proj2 (ro_cells_in _ _ _ _ _ _ RO2 g gr c i Hg Hc Hi) eq_refl))).
  - rewrite SET. rewrite Eops in Sops. unfold ops_hold in *. apply CtrFX.Forall_app3 in Sops as (O1 & O2 & O3).
    apply CtrFX.Forall_app3. split; [exact O1|]. split; [| exact O3].
    cbn [op_id op_args map]. apply H_holds. cbn [pool_holds]. left. exact MARKu.
  - rewrite SET. rewrite Eops in Sapart. unfold ops_apart in *. apply CtrFX.Forall_app3 in Sapart as (A1 & A2 & A3).
    assert (OTHER : forall o, CtrFX.not_id POOL_ID o ->
              (forall a, Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS (op_id o) (map (den E) (op_args o))) ->
                 ~ in_based E (s_regs st) a /\ ((exists seg, find_segment segs a 1 = Some seg) -> in_priv (s_priv st) a)) ->
              forall a, Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS (op_id o) (map (den E) (op_args o))) ->
                 ~ in_based E (IMap.add 0%uint63 r2 (s_regs st)) a /\ ((exists seg, find_segment segs a 1 = Some seg) -> in_priv priv' a)).
    { intros o Hid Ho a Ha. destruct (Ho a Ha) as [NB IP]. split; [rewrite in_based_add0 by exact Sbst; exact NB|].
      intros SG. specialize (IP SG).
      destruct (H_others (op_id o) (map (den E) (op_args o)) a Hid Ha) as [X1 X2].
      unfold priv'. unfold in_priv, unpriv3 in *. apply Exists_exists in IP as (iv & Hin & R). apply Exists_exists. exists iv. split; [| exact R].
      apply filter_In. split; [exact Hin|].
      destruct (is_park_iv FL iv) eqn:Q; [exfalso| reflexivity].
      assert (R3 : in3 a).
      { unfold is_park_iv in Q. apply orb_prop in Q. destruct Q as [Q|Q]; [apply orb_prop in Q; destruct Q as [Q|Q]|]; apply iv_eqb_eq in Q; subst iv.
        - left. destruct iv_fl_val as [V1 V2]. rewrite V1, V2 in R. exact R.
        - right. left. destruct iv_p12_val as [V1 V2]. rewrite V1, V2 in R. exact R.
        - right. right. destruct iv_p204_val as [V1 V2]. rewrite V1, V2 in R. exact R. }
      destruct (in3_pool a R3) as [Z1|Z1]; [apply X1; unfold FLz in Z1; exact Z1| apply X2; unfold FLz in Z1; lia]. }
    apply CtrFX.Forall_app3. split; [| split].
    + apply Forall_forall. intros o Ho. apply OTHER; [exact (proj1 (Forall_forall _ _) N1 o Ho)| exact (proj1 (Forall_forall _ _) A1 o Ho)].
    + cbn [op_id op_args map]. intros a Ha. rewrite H_fp in Ha. unfold pool_fp in Ha. rewrite MARKu in Ha. cbn in Ha. inversion Ha.
    + apply Forall_forall. intros o Ho. apply OTHER; [exact (proj1 (Forall_forall _ _) N2 o Ho)| exact (proj1 (Forall_forall _ _) A3 o Ho)].
  - rewrite SET. intros a FA.
    assert (FA' : fx_acc segs E (s_regs st) a).
    { destruct FA as [B|S']; [left; rewrite in_based_add0 in B by exact Sbst; exact B | right; exact S']. }
    destruct (Scov a FA') as [C0|C1]; [left; exact C0| right].
    rewrite Eops in C1. unfold insts in *. rewrite map_app in *. cbn [map] in *.
    apply Exists_app in C1 as [C|C]; [apply Exists_app; left; exact C|].
    apply Exists_cons in C as [C|C]; [exfalso; cbn [fst snd op_id op_args] in C; exact (H_cov _ _ C)|].
    apply Exists_app. right. apply Exists_cons_tl. exact C.
Qed.

Lemma park_cases_sound : forall E fs sel ls l, facts_hold E fs -> park_cases fs sel = Some ls ->
  bv_unsigned (den E sel) = 4 + Z.of_nat l -> In l ls.
Proof.
  intros E fs sel ls l FH H D. unfold park_cases in H. cbv zeta in H.
  pose proof (ValP.sv_bounds_sound E fs FH sel) as B. unfold ValP.inb in B.
  destruct (sv_bounds fs sel) as [lo hi]. cbn [fst snd] in *.
  destruct (negb (wt lo) && negb (wt hi) && PrimInt63.leb 4%uint63 (wl lo) && PrimInt63.leb (wl lo) (wl hi) && PrimInt63.ltb (wl hi) 7%uint63) eqn:G; [|discriminate H].
  injection H as <-.
  apply andb_prop in G as [G G5]. apply andb_prop in G as [G G4]. apply andb_prop in G as [G G3]. apply andb_prop in G as [G1 G2].
  apply negb_true_iff in G1. apply negb_true_iff in G2.
  apply Uint63.leb_spec in G3. apply Uint63.leb_spec in G4. apply Uint63.ltb_spec in G5.
  change (to_Z 4%uint63) with 4 in G3. change (to_Z 7%uint63) with 7 in G5.
  assert (LO : w2Z lo = to_Z (wl lo)) by (unfold w2Z; rewrite G1; lia).
  assert (HI : w2Z hi = to_Z (wl hi)) by (unfold w2Z; rewrite G2; lia).
  rewrite LO, HI, D in B.
  apply in_seq. lia.
Qed.

Theorem park_sound : forall pc, PlanS.contract_sound segs OPS MP PB (park_c FL segs pc).
Proof.
  intros pc st sts Hpc Happ K E ms md ST HMP HPB HK. cbn [park_c c_apply] in Happ. unfold park_apply in Happ.
  destruct (find_op POOL_ID (s_ops st)) as [[|[w| | | | | | | | | |] [|? ?]]|] eqn:Hfind; try discriminate Happ.
  destruct (IMap.find 0%uint63 (s_regs st)) as [r0|] eqn:Hr0; [|discriminate Happ].
  destruct (weqb w OPEN_MARK) eqn:Hmark; [|discriminate Happ].
  destruct (Nat.eqb (CtrA.count_op POOL_ID (s_ops st)) 1) eqn:Hcnt; [|discriminate Happ]. apply Nat.eqb_eq in Hcnt.
  destruct (pool_in_image FL segs) eqn:Himg; [|discriminate Happ]. cbn [andb] in Happ.
  destruct (first_layout FL segs st NPARK 0) as [l|] eqn:Hfl; [|discriminate Happ]. injection Happ as <-.
  destruct (first_layout_sound st NPARK 0%nat l Hfl) as [TM Hl].
  apply (HK (park_st FL st r0 l) (or_introl eq_refl) E ms md (env_ext_refl _ E) HMP).
  apply (park_st_ok E st ms md w r0 l ST Hfind Hmark Hcnt Hr0 Himg ltac:(lia) TM).
Qed.

Theorem unpark_sound : forall pc, PlanS.contract_sound segs OPS MP PB (unpark_c FL segs pc).
Proof.
  intros pc st sts Hpc Happ K E ms md ST HMP HPB HK. cbn [unpark_c c_apply] in Happ. unfold unpark_apply in Happ.
  destruct (find_op POOL_ID (s_ops st)) as [[|sel [|? ?]]|] eqn:Hfind; try discriminate Happ.
  destruct (IMap.find 0%uint63 (s_regs st)) as [r0|] eqn:Hr0; [|discriminate Happ].
  destruct (priv3_ok FL (s_priv st)) eqn:Hpriv; [|discriminate Happ].
  destruct (Nat.eqb (CtrA.count_op POOL_ID (s_ops st)) 1) eqn:Hcnt; [|discriminate Happ]. apply Nat.eqb_eq in Hcnt.
  destruct (pool_in_image FL segs) eqn:Himg; [|discriminate Happ]. cbn [andb] in Happ.
  destruct (park_cases (s_facts st) sel) as [ls|] eqn:Hsel; [|discriminate Happ]. injection Happ as <-.
  pose proof (ops_hold_find_op E (s_ops st) (ms_mem ms) md POOL_ID [sel] (so_ops _ _ _ _ _ _ ST) Hfind) as OP.
  apply H_holds in OP. cbn [map pool_holds] in OP.

  assert (RNG : 4 <= bv_unsigned (den E sel) < 7).
  { unfold park_cases in Hsel. cbv zeta in Hsel.
    pose proof (ValP.sv_bounds_sound E (s_facts st) (so_facts _ _ _ _ _ _ ST) sel) as B. unfold ValP.inb in B.
    destruct (sv_bounds (s_facts st) sel) as [lo hi]. cbn [fst snd] in *.
    destruct (negb (wt lo) && negb (wt hi) && PrimInt63.leb 4%uint63 (wl lo) && PrimInt63.leb (wl lo) (wl hi) && PrimInt63.ltb (wl hi) 7%uint63) eqn:G; [|discriminate Hsel].
    apply andb_prop in G as [G G5]. apply andb_prop in G as [G G4]. apply andb_prop in G as [G G3]. apply andb_prop in G as [G1 G2].
    apply negb_true_iff in G1. apply negb_true_iff in G2.
    apply Uint63.leb_spec in G3. apply Uint63.ltb_spec in G5.
    change (to_Z 4%uint63) with 4 in G3. change (to_Z 7%uint63) with 7 in G5.
    assert (LO : w2Z lo = to_Z (wl lo)) by (unfold w2Z; rewrite G1; lia).
    assert (HI : w2Z hi = to_Z (wl hi)) by (unfold w2Z; rewrite G2; lia).
    rewrite LO, HI in B. lia. }
  destruct OP as [M|[(s & Hs & Hlt & _)|(l & Hl & Hlt & TB)]]; [lia| unfold NSTATES in Hlt; lia|].
  pose proof (park_cases_sound E (s_facts st) sel ls l (so_facts _ _ _ _ _ _ ST) Hsel Hl) as Hin.
  apply (HK (unpark_st FL st r0 l) (in_map _ _ _ Hin) E ms md (env_ext_refl _ E) HMP).
  apply (unpark_st_ok E st ms md sel r0 l ST Hfind Hcnt Hr0 Hpriv Himg Hlt TB).
Qed.

Lemma pool_frame : forall args m m' model,
  (forall a, 0 <= a < two64 -> Exists (fun iv => fst iv <= a < snd iv) (pool_fp FL args) -> m (Z_to_bv 64 a) = m' (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < two64 -> m (Z_to_bv 64 a) <> None -> m' (Z_to_bv 64 a) <> None) ->
  pool_holds FL segs args m model -> pool_holds FL segs args m' model.
Proof.
  intros args m m' model AG _ H. destruct args as [|sel [|? ?]]; cbn [pool_holds] in *; try exact H.
  pose proof FLz_nn as NN. pose proof HB_val as HBv.
  destruct H as [M|[(s & Hs & Hlt & HF)|(l & Hl & Hlt & HF)]]; [left; exact M| right; left| right; right].
  - exists s. split; [exact Hs|]. split; [exact Hlt|].
    apply Forall_forall. intros e He i Hi. pose proof (proj1 (Forall_forall _ _) HF e He i Hi) as B.
    destruct (tbl_facts s e He) as (C1 & C2 & C3 & C4 & C5 & C6 & C7).
    rewrite <- B. unfold rb. rewrite (AG (to_Z (pe_addr e) + i)); [reflexivity| unfold FLz, two64 in *; lia|].
    unfold pool_fp. rewrite Hs. replace (Z.of_nat s =? 3) with false by (symmetry; apply Z.eqb_neq; unfold NSTATES in Hlt; lia).
    replace (Z.of_nat s <? 3) with true by (symmetry; apply Z.ltb_lt; unfold NSTATES in Hlt; lia).
    rewrite HBv. unfold FLz in *. destruct C6 as [C6|C6]; [left; cbn [fst snd]; lia| right; left; cbn [fst snd]; lia].
  - exists l. split; [exact Hl|]. split; [exact Hlt|].
    apply Forall_forall. intros e He i Hi. pose proof (proj1 (Forall_forall _ _) HF e He i Hi) as B.
    destruct (ptbl_facts l e He) as (C1 & C2 & C3 & C4 & C5 & C6 & C7).
    rewrite <- B. unfold rb. rewrite (AG (to_Z (pe_addr e) + i)); [reflexivity| unfold FLz, two64 in *; lia|].
    unfold pool_fp. rewrite Hl. replace (4 + Z.of_nat l =? 3) with false by (symmetry; apply Z.eqb_neq; lia).
    replace (4 + Z.of_nat l <? 3) with false by (symmetry; apply Z.ltb_ge; lia).
    rewrite HBv. unfold FLz in *. destruct C6 as [C6|[C6|C6]]; [left; cbn [fst snd]; lia| right; left; cbn [fst snd]; lia| right; right; left; cbn [fst snd]; lia].
Qed.

Lemma pool_holds_fresh : forall m md,
  (forall i, 0 <= i < 8 -> rb segs m (to_Z FL + i) = Some (Z_to_bv 8 0)) ->
  pool_holds FL segs [Z_to_bv 64 0] m md.
Proof.
  intros m md HZ. cbn [pool_holds]. right. left. exists 0%nat. split; [rewrite Z_to_bv_small; [reflexivity| rewrite bv_modulus_64; unfold two64; lia]|].
  split; [unfold NSTATES; lia|].
  constructor; [|constructor]. intros i Hi. cbn [pe_w pe_v] in *. change (to_Z 8%uint63) with 8 in Hi.
  destruct (tbl_facts 0%nat (PE (gk FL) 0%uint63 8%uint63 wzero) (or_introl eq_refl)) as (C1 & C2 & C3 & C4 & C5 & C6 & C7).
  cbn [pe_g pe_i pe_w] in C4. change (to_Z 0%uint63) with 0 in C4. rewrite keyZ_small in C4 by exact C5.
  rewrite <- C4. rewrite gkFL_val. replace (8 * (FLz / 8) + 0 + i) with (to_Z FL + i) by (pose proof (Z.div_mod FLz 8 ltac:(lia)); unfold FLz in *; lia).
  rewrite HZ by lia. f_equal. apply bv_eq. rewrite MemP.byte_of_zbyte by lia. cbn [wbv]. rewrite wbv_unsigned, wzero_ok.
  unfold MemP.zbyte. rewrite Z.div_0_l by (apply Z.pow_nonzero; lia). reflexivity.
Qed.
End Snd.
End PoolSnd.
