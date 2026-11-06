(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan ValProofs MemProofs PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Model Layout Inv Arith Steps OpsBridge Ops GLib GUnp G3.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Export U32.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP MemP PlanS UB HeapOp UO UG GU G3 U32.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module GW.
Export U32.

Definition top_win (k : int) (len : int) (kd : int) : sv * sv * sv := (VP k wzero, VL (wlit len), VL (wlit kd)).
Definition region8 (cells : slot) : region :=
  Region 0%uint63 (VL (wlit 8%uint63)) true BGNone (IMap.add 0%uint63 (Gran false cells) IMap.empty).
Definition region24 : region := Region 0%uint63 (VL (wlit 24%uint63)) true BGNone IMap.empty.

Fixpoint find_first {A} (p : A -> bool) (l : list A) : option A :=
  match l with [] => None | x :: l' => if p x then Some x else find_first p l' end.
Lemma find_first_some : forall A (p : A -> bool) l x, find_first p l = Some x -> In x l /\ p x = true.
Proof.
  induction l as [|y l IH]; intros x H; cbn [find_first] in H; [discriminate|].
  destruct (p y) eqn:Q; [injection H as <-; split; [left; reflexivity| exact Q]|].
  destruct (IH x H) as [H1 H2]. split; [right; exact H1| exact H2].
Qed.

Definition only_kind (kd : Z) (w0 : option (sv * sv * sv)) (ws : list (sv * sv * sv)) : bool :=
  forallb (fun w => match kind_of w with
                    | Some k' => if k' =? kd then match w0 with Some x => win3_eqb w x | None => false end else true
                    | None => false
                    end) ws.
Lemma only_kind_sound : forall E kd w0 ws, only_kind kd w0 ws = true ->
  forall x, In x ws -> w_kind (wden E x) = kd -> w0 = Some x.
Proof.
  intros E kd w0 ws H x Hx K. pose proof (proj1 (forallb_forall _ _) H x Hx) as Q. cbn beta in Q.
  destruct (kind_of x) as [k'|] eqn:KO; [|discriminate]. rewrite (kind_of_sound E x k' KO) in K. subst k'. rewrite Z.eqb_refl in Q.
  destruct w0 as [w0|]; [|discriminate]. apply win3_eqb_eq in Q. congruence.
Qed.
Lemma only_kind_lit : forall E ws kd w0, only_kind kd w0 ws = true ->
  forall x, In x ws -> exists k, kind_of x = Some k /\ w_kind (wden E x) = k.
Proof.
  intros E ws kd w0 H x Hx. pose proof (proj1 (forallb_forall _ _) H x Hx) as Q. cbn beta in Q.
  destruct (kind_of x) as [k|] eqn:KO; [|discriminate]. exists k. split; [reflexivity| exact (kind_of_sound E x k KO)].
Qed.

Definition is_carve (w : sv * sv * sv) : bool :=
  match w with
  | (VP k o, _, VL kd) => weqb o wzero && negb (PrimInt63.eqb k 0%uint63) && negb (wt kd) && PrimInt63.eqb (wl kd) 5%uint63
  | _ => false
  end.

Definition size_sv (per : Z) (c : sv) : sv :=
  if per =? 1 then VAlu ALU_ADD (VAlu ALU_SLL c (VL (wlit 4%uint63))) (VAlu ALU_SLL c (VL (wlit 3%uint63)))
  else VAlu ALU_ADD (VAlu ALU_SLL c (VL (wlit 5%uint63))) (VAlu ALU_SLL c (VL (wlit 4%uint63))).

Definition anchor_defs (fs : list fact) (kA : int) : list sv :=
  VP kA wzero :: flat_map (fun f => match f with
                                 | FEq a b => (if sv_eqb a (VP kA wzero) then [b] else []) ++ (if sv_eqb b (VP kA wzero) then [a] else [])
                                 | _ => []
                                 end) fs.

Definition HMAX : w64 := wlit 4611686018427387904%uint63.
Lemma HMAX_val : w2Z HMAX = two62Z.
Proof. vm_compute. reflexivity. Qed.

Definition top_facts (fs : list fact) (base : sv) (n' : int) : list fact :=
  (let lo := fst (sv_bounds fs base) in if negb (wt lo) then [FRange n' lo HMAX] else [])
  ++ (if aligned fs base 3%uint63 then [FAlign n' 3%uint63] else []).

Definition zp_facts (fs : list fact) (kA : int) (n' : int) : list fact :=
  let lo := fst (sv_bounds fs (VP kA wzero)) in if negb (wt lo) then [FRange n' lo HMAX] else [].

Definition zf_facts (fs : list fact) (zfree : sv) (n' : int) : list fact :=
  let b := sv_bounds fs zfree in if negb (wt (snd b)) then [FRange n' wzero (wlit (wl (snd b)))] else [].

Definition no_cells (r : region) : bool := match rg_cells r with IMap.Leaf => true | _ => false end.

Section WithSegs.
Variable segs : list Segment.

Lemma to_Z_add_small : forall n i, to_Z n < to_Z bit62i -> to_Z i <= 8 -> to_Z (PrimInt63.add n i) = to_Z n + to_Z i.
Proof.
  intros n i Hn Hi. rewrite Uint63.add_spec. apply Z.mod_small. pose proof (int_range n). pose proof (int_range i).
  rewrite to_Z_bit62i in Hn. rewrite wB_two63. unfold two63. lia.
Qed.
Lemma ev_upd : forall E k w k', ev (env_upd E k w) k' = if PrimInt63.eqb k' k then w else ev E k'.
Proof. reflexivity. Qed.
Lemma ev_upd_other : forall E k w k', to_Z k' <> to_Z k -> ev (env_upd E k w) k' = ev E k'.
Proof.
  intros E k w k' NE. rewrite ev_upd. destruct (PrimInt63.eqb k' k) eqn:Q; [|reflexivity].
  apply Uint63.eqb_correct in Q. subst. contradiction.
Qed.

Lemma region_cells_vars_below : forall n st k r g gr c, st_vars_below n st = true -> IMap.bst (s_regs st) -> IMap.bst (rg_cells r) ->
  IMap.find k (s_regs st) = Some r -> IMap.find g (rg_cells r) = Some gr -> In c (g_cells gr) -> sv_vars_below n (c_v c) = true.
Proof.
  intros n st k r g gr c VB B BR F G Hc. unfold st_vars_below in VB.
  apply andb_prop in VB as [VB _]. apply andb_prop in VB as [VB _]. apply andb_prop in VB as [_ VB].
  pose proof (proj1 (IMap.forallb_spec _ _ B) VB k r F) as Q. apply andb_prop in Q as [_ Q]. unfold region_vars_below in Q.
  apply andb_prop in Q as [_ Q].
  pose proof (proj1 (IMap.forallb_spec _ _ BR) Q g gr G) as Q2. exact (slot_vars_below_In n _ c Q2 Hc).
Qed.
Lemma gran8_vars_below : forall n st k r g d v, st_vars_below n st = true -> IMap.bst (s_regs st) -> IMap.bst (rg_cells r) ->
  IMap.find k (s_regs st) = Some r -> gran8 r g = Some (d, v) -> sv_vars_below n v = true.
Proof.
  intros n st k r g d v VB B BR F G.
  exact (region_cells_vars_below n st k r g _ (Cell 0%uint63 8%uint63 v) VB B BR F (gran8_find r g d v G) ltac:(left; reflexivity)).
Qed.

Lemma top_win_den : forall E k len kd, wden E (top_win k len kd) = Win (bv_unsigned (ev E k)) (to_Z len) (to_Z kd).
Proof.
  intros E k len kd. unfold top_win, wden. rewrite (den_VP0 E k wzero (weqb_refl _)). cbn [den]. rewrite !wbv_unsigned, !wlit_ok. reflexivity.
Qed.
Lemma slot_win_top : forall k, slot_win k = top_win k 24%uint63 4%uint63.
Proof. reflexivity. Qed.

Lemma size_sv_den : forall E per c, (per = 1 \/ per = 2) -> bv_unsigned (den E c) <= 1000 ->
  bv_unsigned (den E (size_sv per c)) = OBJ_SIZE * per * bv_unsigned (den E c).
Proof.
  intros E per c Hp Hc. pose proof (bv_unsigned_in_range _ (den E c)) as R.
  unfold size_sv. destruct Hp as [-> | ->]; cbn [Z.eqb Pos.eqb den alu64 alu];
    rewrite bv_add_unsigned, !bv_shiftl_unsigned, !shamt6_bv, !Z.shiftl_mul_pow2, !wrap64 by apply int_range.
  - change (to_Z (shamt6 (wlit 4))) with 4. change (to_Z (shamt6 (wlit 3))) with 3. change (2^4) with 16. change (2^3) with 8.
    unfold OBJ_SIZE, two64. rewrite !Z.mod_small by lia. lia.
  - change (to_Z (shamt6 (wlit 5))) with 5. change (to_Z (shamt6 (wlit 4))) with 4. change (2^5) with 32. change (2^4) with 16.
    unfold OBJ_SIZE, two64. rewrite !Z.mod_small by lia. lia.
Qed.

Lemma anchor_defs_sound : forall E fs kA X, facts_hold E fs -> In X (anchor_defs fs kA) -> den E X = den E (VP kA wzero).
Proof.
  intros E fs kA X FH H. unfold anchor_defs in H. destruct H as [<-|H]; [reflexivity|].
  apply in_flat_map in H as (f & Hf & HX). pose proof (proj1 (Forall_forall _ _) FH f Hf) as FF.
  destruct f; try (destruct HX; fail); cbn [fact_holds] in FF.
  all: try solve [destruct HX].
  apply in_app_iff in HX as [HX|HX].
  - destruct (sv_eqb a (VP kA wzero)) eqn:Q; [|destruct HX]. apply sv_eqb_eq in Q. subst a. destruct HX as [<-|[]]. symmetry. exact FF.
  - destruct (sv_eqb b (VP kA wzero)) eqn:Q; [|destruct HX]. apply sv_eqb_eq in Q. subst b. destruct HX as [<-|[]]. exact FF.
Qed.

Lemma keyZ_of_Z : forall z, - two62Z <= z < two62Z -> keyZ (Uint63.of_Z z) = z.
Proof.
  intros z Hz. unfold two62Z in Hz. destruct (Z.lt_ge_cases z 0) as [NEG|NN]; [| apply keyZ_small; unfold two62Z; lia].
  destruct (keyZ_cases (Uint63.of_Z z)) as [[R K]|[R K]]; rewrite Uint63.of_Z_spec, wB_two63 in *.
  - exfalso. replace z with ((z + two63) + (-1) * two63) in R by lia. rewrite Z_mod_plus_full, Z.mod_small in R by (unfold two63; lia). unfold two63 in R. lia.
  - rewrite K. replace z with ((z + two63) + (-1) * two63) at 1 by lia. rewrite Z_mod_plus_full, Z.mod_small by (unfold two63; lia). unfold two63. lia.
Qed.

Lemma cell_at_ok_s : forall priv E m k r off w v,
  region_ok segs priv E m k r -> - two62Z <= off -> off < two62Z -> cell_at r off w = Some v ->
  let c := Cell (Uint63.of_Z (off mod 8)) w v in
  cell_ok segs E m (bv_unsigned (ev E k) + 8 * (off / 8)) c /\ to_Z (c_idx c) = off mod 8 /\
  (PrimInt63.eqb k 0%uint63 = false -> forall i, 0 <= i < to_Z w -> loZ r <= off + i < hiZ E r).
Proof.
  intros priv E m k r off w v RO H0 H62 CA. unfold cell_at in CA.
  destruct (IMap.find (Uint63.of_Z (off / 8)) (rg_cells r)) as [gr|] eqn:F; [|discriminate].
  apply find_cell_In in CA.
  assert (KZ : keyZ (Uint63.of_Z (off / 8)) = off / 8) by (apply keyZ_of_Z; unfold two62Z in *; lia).
  assert (IX : to_Z (Uint63.of_Z (off mod 8)) = off mod 8) by (apply of_Z_small; unfold two63; pose proof (Z.mod_pos_bound off 8); lia).
  destruct (ro_cells _ _ _ _ _ _ RO _ _ F) as [_ FC]. rewrite KZ in FC.
  pose proof (proj1 (Forall_forall _ _) FC _ CA) as CO.
  cbv zeta. split; [exact CO|]. split; [exact IX|].
  intros K i Hi. destruct (ro_cells_in _ _ _ _ _ _ RO _ gr _ i F CA Hi) as [IN _]. specialize (IN K).
  cbn [c_idx] in IN. rewrite KZ, IX in IN. pose proof (Z.div_mod off 8 ltac:(lia)). lia.
Qed.

Lemma cell_at_u64_s : forall priv E m k r off v,
  region_ok segs priv E m k r -> PrimInt63.eqb k 0%uint63 = false -> - two62Z <= off -> off < two62Z ->
  cell_at r off 8%uint63 = Some v ->
  u64_at (bmem_of segs m) (bv_unsigned (ev E k) + off) (bv_unsigned (den E v)) /\ loZ r <= off /\ off + 8 <= hiZ E r.
Proof.
  intros priv E m k r off v RO K H0 H62 CA.
  destruct (cell_at_ok_s priv E m k r off 8%uint63 v RO H0 H62 CA) as (CO & IX & IN). specialize (IN K). cbn [c_idx] in IX.
  pose proof (ro_range _ _ _ _ _ _ RO K) as [R1 R2].
  assert (L1 := IN 0 ltac:(change (to_Z 8%uint63) with 8; lia)). assert (L2 := IN 7 ltac:(change (to_Z 8%uint63) with 8; lia)).
  split; [| lia].
  pose proof (u64_at_of_cell segs E m (bv_unsigned (ev E k) + 8 * (off / 8)) _ CO eq_refl) as U. cbn [c_idx c_v] in U. rewrite IX in U.
  replace (bv_unsigned (ev E k) + 8 * (off / 8) + off mod 8) with (bv_unsigned (ev E k) + off) in U by (pose proof (Z.div_mod off 8 ltac:(lia)); lia).
  apply U; lia.
Qed.

Lemma cell_at_u32_s : forall priv E m k r off v,
  region_ok segs priv E m k r -> PrimInt63.eqb k 0%uint63 = false -> - two62Z <= off -> off < two62Z ->
  cell_at r off 4%uint63 = Some v ->
  u32_at (bmem_of segs m) (bv_unsigned (ev E k) + off) (bv_unsigned (den E v) mod 2 ^ 32) /\ loZ r <= off /\ off + 4 <= hiZ E r.
Proof.
  intros priv E m k r off v RO K H0 H62 CA.
  destruct (cell_at_ok_s priv E m k r off 4%uint63 v RO H0 H62 CA) as (CO & IX & IN). specialize (IN K). cbn [c_idx] in IX.
  pose proof (ro_range _ _ _ _ _ _ RO K) as [R1 R2].
  assert (L1 := IN 0 ltac:(change (to_Z 4%uint63) with 4; lia)). assert (L2 := IN 3 ltac:(change (to_Z 4%uint63) with 4; lia)).
  split; [| lia].
  pose proof (u32_at_of_cell segs E m (bv_unsigned (ev E k) + 8 * (off / 8)) _ CO eq_refl) as U. cbn [c_idx c_v] in U. rewrite IX in U.
  replace (bv_unsigned (ev E k) + 8 * (off / 8) + off mod 8) with (bv_unsigned (ev E k) + off) in U by (pose proof (Z.div_mod off 8 ltac:(lia)); lia).
  apply U; lia.
Qed.

Lemma cell_at_u8_s : forall priv E m k r off v,
  region_ok segs priv E m k r -> PrimInt63.eqb k 0%uint63 = false -> - two62Z <= off -> off < two62Z ->
  cell_at r off 1%uint63 = Some v ->
  u8_at (bmem_of segs m) (bv_unsigned (ev E k) + off) (bv_unsigned (den E v) mod 2 ^ 8) /\ loZ r <= off /\ off + 1 <= hiZ E r.
Proof.
  intros priv E m k r off v RO K H0 H62 CA.
  destruct (cell_at_ok_s priv E m k r off 1%uint63 v RO H0 H62 CA) as (CO & IX & IN). specialize (IN K). cbn [c_idx] in IX.
  pose proof (ro_range _ _ _ _ _ _ RO K) as [R1 R2].
  assert (L1 := IN 0 ltac:(change (to_Z 1%uint63) with 1; lia)).
  split; [| lia].
  pose proof (u8_at_of_cell segs E m (bv_unsigned (ev E k) + 8 * (off / 8)) _ CO eq_refl) as U. cbn [c_idx c_v] in U. rewrite IX in U.
  replace (bv_unsigned (ev E k) + 8 * (off / 8) + off mod 8) with (bv_unsigned (ev E k) + off) in U by (pose proof (Z.div_mod off 8 ltac:(lia)); lia).
  apply U; lia.
Qed.

Lemma rdZ_succ : forall (bm : bmem) a n, rdZ bm a (S n) = match bm a with Some b => match rdZ bm (a + 1) n with Some r => Some (b + 256 * r) | None => None end | None => None end.
Proof. reflexivity. Qed.

Lemma rdZ_range : forall m n a v, rdZ (bmem_of segs m) a (S n) = Some v -> 0 <= a /\ a + Z.of_nat (S n) <= two64.
Proof.
  intros m n. induction n as [|n IH]; intros a v H; rewrite rdZ_succ in H.
  - destruct (bmem_of segs m a) as [b|] eqn:B; [|discriminate]. pose proof (bmem_of_range segs m a b B) as [R _]. cbn [Z.of_nat Pos.of_succ_nat]. lia.
  - destruct (bmem_of segs m a) as [b|] eqn:B; [|discriminate].
    destruct (rdZ (bmem_of segs m) (a + 1) (S n)) as [w|] eqn:RR; [|discriminate].
    pose proof (bmem_of_range segs m a b B) as [R _]. pose proof (IH (a + 1) w RR) as [R3 R4]. lia.
Qed.

Lemma gran8_u64 : forall priv E m k r g d v,
  region_ok segs priv E m k r -> PrimInt63.eqb k 0%uint63 = false -> gran8 r g = Some (d, v) -> 0 <= keyZ g -> 8 * keyZ g < two62Z ->
  u64_at (bmem_of segs m) (bv_unsigned (ev E k) + 8 * keyZ g) (bv_unsigned (den E v)) /\ loZ r <= 8 * keyZ g /\ 8 * keyZ g + 8 <= hiZ E r.
Proof.
  intros priv E m k r g d v RO K G H0 H62.
  exact (cell_at_u64 segs priv E m k r (8 * keyZ g) v RO K ltac:(lia) H62 (gran8_cell_at r g d v G H0)).
Qed.

Lemma bytes_of_region : forall priv E m k r a,
  region_ok segs priv E m k r -> PrimInt63.eqb k 0%uint63 = false ->
  bv_unsigned (ev E k) + loZ r <= a < bv_unsigned (ev E k) + hiZ E r ->
  m (Z_to_bv 64 a) <> None /\ find_segment segs a 1 = None.
Proof.
  intros priv E m k r a RO K Ha. destruct (ro_valid _ _ _ _ _ _ RO K a Ha) as (RB & _ & NS). split; [| exact NS].
  pose proof (ro_range _ _ _ _ _ _ RO K) as [R1 R2].
  rewrite rb_unfold in RB. destruct (m (Z_to_bv 64 a)); [discriminate|].
  destruct (memory_read segs (Z_to_bv 64 a) 1) as [bs|] eqn:MR; [| exfalso; exact (RB eq_refl)].
  destruct (memory_read_find_segment segs a bs ltac:(lia) MR) as [seg SEG]. rewrite NS in SEG. discriminate.
Qed.

Lemma region24_ok : forall priv E m k,
  PrimInt63.eqb k 0%uint63 = false -> bv_unsigned (ev E k) + 24 < two64 ->
  (forall a, bv_unsigned (ev E k) <= a < bv_unsigned (ev E k) + 24 -> m (Z_to_bv 64 a) <> None /\ find_segment segs a 1 = None) ->
  region_ok segs priv E m k region24.
Proof.
  intros priv E m k K R BY. pose proof (bv_unsigned_in_range _ (ev E k)) as RK.
  apply (region_ok_fresh segs priv E m k region24 K).
  - exact I.
  - reflexivity.
  - change (loZ region24) with 0. lia.
  - unfold hiZ. cbn [region24 rg_hi den]. rewrite wbv_unsigned, wlit_ok. change (to_Z 24%uint63) with 24. lia.
  - intros a Ha. change (loZ region24) with 0 in Ha. unfold hiZ in Ha. cbn [region24 rg_hi den] in Ha. rewrite wbv_unsigned, wlit_ok in Ha.
    change (to_Z 24%uint63) with 24 in Ha. apply BY. lia.
  - intros g gr F. cbn [region24 rg_cells] in F. rewrite IMap.find_empty in F. discriminate.
Qed.

Lemma region8_u64_ok : forall priv E m k v z,
  PrimInt63.eqb k 0%uint63 = false -> bv_unsigned (ev E k) + 8 < two64 ->
  (forall a, bv_unsigned (ev E k) <= a < bv_unsigned (ev E k) + 8 -> m (Z_to_bv 64 a) <> None /\ find_segment segs a 1 = None) ->
  u64_at (bmem_of segs m) (bv_unsigned (ev E k)) z -> bv_unsigned (den E v) = z ->
  region_ok segs priv E m k (region8 [Cell 0%uint63 8%uint63 v]).
Proof.
  intros priv E m k v z K R BY U DV. pose proof (bv_unsigned_in_range _ (ev E k)) as RK.
  assert (HI : hiZ E (region8 [Cell 0%uint63 8%uint63 v]) = 8).
  { unfold hiZ. cbn [region8 rg_hi den]. rewrite wbv_unsigned, wlit_ok. reflexivity. }
  assert (LO : loZ (region8 [Cell 0%uint63 8%uint63 v]) = 0) by reflexivity.
  apply (region_ok_fresh segs priv E m k _ K).
  - cbn [region8 rg_cells]. apply IMap.bst_add. exact I.
  - reflexivity.
  - rewrite LO. lia.
  - rewrite HI. lia.
  - intros a Ha. rewrite LO, HI in Ha. apply BY. lia.
  - intros g gr F. cbn [region8 rg_cells] in F.
    destruct (Uint63.eqb g 0) eqn:GK.
    + apply Uint63.eqb_correct in GK. subst g. rewrite IMap.find_add_same in F by exact I. injection F as <-. cbn [g_cells].
      change (keyZ 0%uint63) with 0. rewrite Z.mul_0_r, Z.add_0_r. split.
      * split; [cbn; tauto|]. constructor; [|constructor].
        apply (cell_ok_of_u64 segs E m (bv_unsigned (ev E k)) 0%uint63 v z); [change (to_Z 0%uint63) with 0; lia| change (to_Z 0%uint63) with 0; lia| |].
        -- change (to_Z 0%uint63) with 0. rewrite Z.add_0_r. exact U.
        -- exact DV.
      * intros c i [<-|[]] Hi. cbn [c_w c_idx] in Hi |- *. change (to_Z 8%uint63) with 8 in Hi. change (to_Z 0%uint63) with 0. rewrite LO, HI. lia.
    + apply Uint63.eqb_false_correct in GK. rewrite IMap.find_add_other in F by (try exact I; congruence). rewrite IMap.find_empty in F. discriminate.
Qed.

Lemma region8_u32x2_ok : forall priv E m k v1 z1 v2 z2,
  PrimInt63.eqb k 0%uint63 = false -> bv_unsigned (ev E k) + 8 < two64 ->
  (forall a, bv_unsigned (ev E k) <= a < bv_unsigned (ev E k) + 8 -> m (Z_to_bv 64 a) <> None /\ find_segment segs a 1 = None) ->
  u32_at (bmem_of segs m) (bv_unsigned (ev E k)) z1 -> bv_unsigned (den E v1) mod 2 ^ 32 = z1 ->
  u32_at (bmem_of segs m) (bv_unsigned (ev E k) + 4) z2 -> bv_unsigned (den E v2) mod 2 ^ 32 = z2 ->
  region_ok segs priv E m k (region8 [Cell 0%uint63 4%uint63 v1; Cell 4%uint63 4%uint63 v2]).
Proof.
  intros priv E m k v1 z1 v2 z2 K R BY U1 D1 U2 D2. pose proof (bv_unsigned_in_range _ (ev E k)) as RK.
  assert (HI : hiZ E (region8 [Cell 0%uint63 4%uint63 v1; Cell 4%uint63 4%uint63 v2]) = 8).
  { unfold hiZ. cbn [region8 rg_hi den]. rewrite wbv_unsigned, wlit_ok. reflexivity. }
  assert (LO : loZ (region8 [Cell 0%uint63 4%uint63 v1; Cell 4%uint63 4%uint63 v2]) = 0) by reflexivity.
  apply (region_ok_fresh segs priv E m k _ K).
  - cbn [region8 rg_cells]. apply IMap.bst_add. exact I.
  - reflexivity.
  - rewrite LO. lia.
  - rewrite HI. lia.
  - intros a Ha. rewrite LO, HI in Ha. apply BY. lia.
  - intros g gr F. cbn [region8 rg_cells] in F.
    destruct (Uint63.eqb g 0) eqn:GK.
    + apply Uint63.eqb_correct in GK. subst g. rewrite IMap.find_add_same in F by exact I. injection F as <-. cbn [g_cells].
      change (keyZ 0%uint63) with 0. rewrite Z.mul_0_r, Z.add_0_r. split.
      * split; [cbn; change (to_Z 0%uint63) with 0; change (to_Z 4%uint63) with 4; lia|]. constructor; [| constructor; [|constructor]].
        -- apply (cell_ok_of_u32 segs E m (bv_unsigned (ev E k)) 0%uint63 v1 z1); [change (to_Z 0%uint63) with 0; lia| change (to_Z 0%uint63) with 0; lia| |].
           ++ change (to_Z 0%uint63) with 0. rewrite Z.add_0_r. exact U1.
           ++ exact D1.
        -- apply (cell_ok_of_u32 segs E m (bv_unsigned (ev E k)) 4%uint63 v2 z2); [change (to_Z 4%uint63) with 4; lia| change (to_Z 4%uint63) with 4; lia| |].
           ++ change (to_Z 4%uint63) with 4. exact U2.
           ++ exact D2.
      * intros c i [<-|[<-|[]]] Hi; cbn [c_w c_idx] in Hi |- *; [change (to_Z 4%uint63) with 4 in Hi; change (to_Z 0%uint63) with 0| change (to_Z 4%uint63) with 4 in Hi |- *]; rewrite LO, HI; lia.
    + apply Uint63.eqb_false_correct in GK. rewrite IMap.find_add_other in F by (try exact I; congruence). rewrite IMap.find_empty in F. discriminate.
Qed.

Lemma mod8_of_align : forall E fs k, facts_hold E fs -> PrimInt63.leb 3%uint63 (find_align fs k) = true -> bv_unsigned (ev E k) mod 8 = 0.
Proof.
  intros E fs k FH AL. pose proof (find_align_sound_gen E fs FH k) as A.
  apply Uint63.leb_spec in AL. change (to_Z 3%uint63) with 3 in AL. pose proof (int_range (find_align fs k)) as R.
  replace (2 ^ to_Z (find_align fs k)) with (8 * 2 ^ (to_Z (find_align fs k) - 3)) in A
    by (replace (to_Z (find_align fs k)) with (3 + (to_Z (find_align fs k) - 3)) at 2 by lia; rewrite Z.pow_add_r by lia; reflexivity).
  assert (P : 0 < 2 ^ (to_Z (find_align fs k) - 3)) by (apply Z.pow_pos_nonneg; lia).
  apply Z.mod_divide in A; [|lia]. apply Z.mod_divide; [lia|]. destruct A as [q Hq]. exists (q * 2 ^ (to_Z (find_align fs k) - 3)). lia.
Qed.

Lemma align_of_find : forall E fs k m, facts_hold E fs -> PrimInt63.leb m (find_align fs k) = true -> to_Z m <= 62 ->
  bv_unsigned (ev E k) mod 2 ^ (to_Z m) = 0.
Proof.
  intros E fs k m FH AL Hm. pose proof (find_align_sound_gen E fs FH k) as A.
  apply Uint63.leb_spec in AL. pose proof (int_range (find_align fs k)) as R. pose proof (int_range m) as Rm.
  replace (2 ^ to_Z (find_align fs k)) with (2 ^ to_Z m * 2 ^ (to_Z (find_align fs k) - to_Z m)) in A
    by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  assert (P : 0 < 2 ^ (to_Z (find_align fs k) - to_Z m)) by (apply Z.pow_pos_nonneg; lia).
  assert (P2 : 0 < 2 ^ to_Z m) by (apply Z.pow_pos_nonneg; lia).
  apply Z.mod_divide in A; [|lia]. apply Z.mod_divide; [lia|]. destruct A as [q Hq]. exists (q * 2 ^ (to_Z (find_align fs k) - to_Z m)). lia.
Qed.

Lemma top_facts_sound : forall E fs base n', facts_hold E fs ->
  bv_unsigned (den E base) <= bv_unsigned (ev E n') <= two62Z ->
  (bv_unsigned (ev E n') - bv_unsigned (den E base)) mod 8 = 0 ->
  Forall (fact_holds E) (top_facts fs base n').
Proof.
  intros E fs base n' FH B M8. unfold top_facts. apply Forall_app. split.
  - destruct (sv_bounds fs base) as [lo hi] eqn:SB. cbn [fst]. destruct (wt lo) eqn:T; [constructor|]. cbn [negb].
    pose proof (sv_bounds_sound E fs FH base) as I0. rewrite SB in I0. unfold inb in I0. cbn [fst snd] in I0.
    constructor; [|constructor]. cbn [fact_holds]. rewrite HMAX_val. lia.
  - destruct (aligned fs base 3) eqn:AL; [|constructor]. constructor; [|constructor]. cbn [fact_holds].
    pose proof (aligned_sound E fs FH base 3%uint63 AL ltac:(change (to_Z 3%uint63) with 3; lia)) as A. change (to_Z 3%uint63) with 3 in A |- *.
    change (2 ^ 3) with 8 in A |- *.
    replace (bv_unsigned (ev E n')) with ((bv_unsigned (ev E n') - bv_unsigned (den E base)) + bv_unsigned (den E base)) by lia.
    rewrite Z.add_mod, M8, A by lia. reflexivity.
Qed.

Lemma zp_facts_sound : forall E fs kA n', facts_hold E fs ->
  bv_unsigned (ev E kA) <= bv_unsigned (ev E n') <= two62Z ->
  Forall (fact_holds E) (zp_facts fs kA n').
Proof.
  intros E fs kA n' FH B. unfold zp_facts.
  destruct (sv_bounds fs (VP kA wzero)) as [lA hA] eqn:BA. cbn [fst]. destruct (wt lA) eqn:T; [constructor|]. cbn [negb].
  pose proof (sv_bounds_sound E fs FH (VP kA wzero)) as IA. rewrite BA in IA. unfold inb in IA. cbn [fst snd] in IA.
  rewrite (den_VP0 E kA wzero (weqb_refl _)) in IA.
  constructor; [|constructor]. cbn [fact_holds]. rewrite HMAX_val. lia.
Qed.

Lemma zf_facts_sound : forall E fs zfree n', facts_hold E fs ->
  bv_unsigned (ev E n') <= bv_unsigned (den E zfree) -> Forall (fact_holds E) (zf_facts fs zfree n').
Proof.
  intros E fs zfree n' FH LE. unfold zf_facts.
  destruct (sv_bounds fs zfree) as [lo hi] eqn:B. cbn [fst snd]. destruct (wt hi) eqn:T; [constructor|]. cbn [negb].
  pose proof (sv_bounds_sound E fs FH zfree) as I0. rewrite B in I0. unfold inb in I0. cbn [fst snd] in I0.
  pose proof (bv_unsigned_in_range _ (ev E n')).
  constructor; [|constructor]. cbn [fact_holds]. rewrite wlit_ok. change (w2Z wzero) with 0. unfold w2Z in I0. rewrite T in I0. lia.
Qed.

Definition sub_cell (f : sv -> sv) (c : cell) : cell := Cell (c_idx c) (c_w c) (f (c_v c)).
Definition sub_gran (f : sv -> sv) (g : gran) : gran := Gran (g_dirty g) (List.map (sub_cell f) (g_cells g)).
Definition subst_cells (f : sv -> sv) (r : region) : region :=
  Region (rg_lo r) (rg_hi r) (rg_w r) (rg_bg r) (IMap.map (sub_gran f) (rg_cells r)).

Lemma slot_sorted_map : forall f s, slot_sorted s -> slot_sorted (List.map (sub_cell f) s).
Proof.
  induction s as [|c s IH]; intros H; [exact I|].
  destruct H as [H1 H2]. cbn [List.map]. split; [| exact (IH H2)].
  destruct s as [|c' s']; cbn [List.map]; [exact I|]. cbn [sub_cell c_idx c_w]. exact H1.
Qed.

Lemma region_ok_subst_cells : forall priv E m k r f,
  (forall v, den E (f v) = den E v) -> region_ok segs priv E m k r -> region_ok segs priv E m k (subst_cells f r).
Proof.
  intros priv E m k r f HF RO.
  assert (HI : forall E0, hiZ E0 (subst_cells f r) = hiZ E0 r) by (intros; reflexivity).
  assert (LO : loZ (subst_cells f r) = loZ r) by reflexivity.
  assert (FIND : forall g gr, IMap.find g (rg_cells (subst_cells f r)) = Some gr -> exists gr0, IMap.find g (rg_cells r) = Some gr0 /\ gr = sub_gran f gr0).
  { intros g gr F. cbn [subst_cells rg_cells] in F. rewrite IMap.find_map in F. destruct (IMap.find g (rg_cells r)) as [gr0|]; [|discriminate].
    cbn [option_map] in F. injection F as <-. exists gr0. auto. }
  constructor.
  - cbn [subst_cells rg_cells]. apply IMap.bst_map. exact (ro_bst _ _ _ _ _ _ RO).
  - rewrite HI, LO. exact (ro_range _ _ _ _ _ _ RO).
  - rewrite HI, LO. cbn [subst_cells rg_w]. exact (ro_valid _ _ _ _ _ _ RO).
  - intros g gr F. destruct (FIND g gr F) as (gr0 & F0 & ->). cbn [sub_gran g_cells].
    destruct (ro_cells _ _ _ _ _ _ RO g gr0 F0) as [SS FC]. split; [exact (slot_sorted_map f _ SS)|].
    apply Forall_forall. intros c Hc. apply in_map_iff in Hc as (c0 & <- & Hc0).
    pose proof (proj1 (Forall_forall _ _) FC c0 Hc0) as (C1 & C2 & C3 & C4). unfold cell_ok. cbn [sub_cell c_idx c_w c_v].
    split; [exact C1|]. split; [exact C2|]. split; [exact C3|]. intros i Hi. rewrite HF. exact (C4 i Hi).
  - intros g gr c i F Hc Hi. rewrite HI, LO. destruct (FIND g gr F) as (gr0 & F0 & ->). cbn [sub_gran g_cells] in Hc.
    apply in_map_iff in Hc as (c0 & <- & Hc0). cbn [sub_cell c_idx c_w] in Hi |- *.
    exact (ro_cells_in _ _ _ _ _ _ RO g gr0 c0 i F0 Hc0 Hi).
  - intros o H1 H2 UC. rewrite HI, LO in H1.
    assert (UC' : uncovered r o).
    { intros g gr K0 F0. destruct (UC g (sub_gran f gr) K0 ltac:(cbn [subst_cells rg_cells]; rewrite IMap.find_map, F0; reflexivity)) as [D1 D2].
      cbn [sub_gran g_dirty g_cells] in D1, D2. split; [exact D1|].
      apply Forall_forall. intros c Hc. pose proof (proj1 (Forall_forall _ _) D2 (sub_cell f c) (in_map _ _ _ Hc)) as X.
      unfold covers in *. cbn [sub_cell c_idx c_w] in X. exact X. }
    pose proof (ro_bg _ _ _ _ _ _ RO o H1 H2 UC') as BG. unfold bg_byte in BG |- *. cbn [subst_cells rg_bg]. exact BG.
Qed.

Lemma st_ok_subst_cells : forall OPS E st ms mo k r f,
  st_ok segs OPS E st ms mo -> IMap.find k (s_regs st) = Some r -> PrimInt63.eqb k 0%uint63 = false ->
  (forall v, den E (f v) = den E v) ->
  st_ok segs OPS E (setregs st (IMap.add k (subst_cells f r) (s_regs st))) ms mo.
Proof.
  intros OPS E st ms mo k r f HS F K HF.
  pose proof HS as [Ppc Px0 Pregs Pfregs Psvc Presv Pfcsr Prom Pz Pbst Preg Pdisj Ppub Pfacts Pops Papart Pmf Pcov Pminv].
  assert (FIND : forall k' r', IMap.find k' (IMap.add k (subst_cells f r) (s_regs st)) = Some r' ->
            (k' = k /\ r' = subst_cells f r) \/ (k' <> k /\ IMap.find k' (s_regs st) = Some r')).
  { intros k' r' F'. destruct (Uint63.eqb k k') eqn:Q.
    - apply Uint63.eqb_correct in Q. subst k'. rewrite IMap.find_add_same in F' by exact Pbst. injection F' as <-. left; auto.
    - apply Uint63.eqb_false_correct in Q. rewrite IMap.find_add_other in F' by (exact Pbst || exact Q). right. split; [congruence| exact F']. }
  assert (RANGE : forall k' r', IMap.find k' (IMap.add k (subst_cells f r) (s_regs st)) = Some r' ->
            exists r0, IMap.find k' (s_regs st) = Some r0 /\ loZ r' = loZ r0 /\ (forall E0, hiZ E0 r' = hiZ E0 r0) /\ rg_w r' = rg_w r0).
  { intros k' r' F'. destruct (FIND k' r' F') as [[-> ->]|[NE F0]]; [exists r; rewrite F; repeat split; reflexivity| exists r'; auto]. }
  assert (BASED : forall a, in_based E (IMap.add k (subst_cells f r) (s_regs st)) a <-> in_based E (s_regs st) a).
  { intros a. unfold in_based. split.
    - intros (k' & r' & F' & K' & R'). destruct (RANGE k' r' F') as (r0 & F0 & L0 & H0 & _). exists k', r0. rewrite <- L0, <- (H0 E). auto.
    - intros (k' & r' & F' & K' & R'). destruct (Uint63.eqb k k') eqn:Q.
      + apply Uint63.eqb_correct in Q. subst k'. rewrite F in F'. injection F' as <-. exists k, (subst_cells f r).
        rewrite IMap.find_add_same by exact Pbst. auto.
      + apply Uint63.eqb_false_correct in Q. exists k', r'. rewrite IMap.find_add_other by (exact Pbst || exact Q). auto. }
  constructor; cbn [setregs s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next]; try assumption.
  - apply IMap.bst_add. exact Pbst.
  - intros k' r' F'. destruct (FIND k' r' F') as [[-> ->]|[NE F0]]; [apply region_ok_subst_cells; [exact HF| exact (Preg k r F)]| exact (Preg k' r' F0)].
  - intros k1 r1 k2 r2 F1 F2 NE K1 K2 W a [A1 A2].
    destruct (RANGE k1 r1 F1) as (q1 & G1 & L1 & H1 & W1). destruct (RANGE k2 r2 F2) as (q2 & G2 & L2 & H2 & W2).
    rewrite L1, (H1 E) in A1. rewrite L2, (H2 E) in A2. rewrite W1, W2 in W.
    exact (Pdisj k1 q1 k2 q2 G1 G2 NE K1 K2 W a (conj A1 A2)).
  - intros r0 g gr c F0. destruct (FIND _ r0 F0) as [[KK _]|[_ F1]]; [| exact (Ppub r0 g gr c F1)].
    exfalso. rewrite <- KK, Uint63.eqb_refl in K. discriminate.
  - unfold ops_apart in *. apply Forall_forall. intros o Ho a Ha. pose proof (proj1 (Forall_forall _ _) Papart o Ho a Ha) as [A B].
    split; [| exact B]. intros X. apply A. exact (proj1 (BASED a) X).
  -
    intros a FA. apply Pcov. destruct FA as [B|S]; [left; exact (proj1 (BASED a) B)| right; exact S].
Qed.

End WithSegs.
End GW.
