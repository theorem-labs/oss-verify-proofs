(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore FxSubst FxSound FxMem FxStep RefMemcpyLib.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Mem Cells Exec Frame Arr Step Image.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section Bridge.
Variable segs : list Segment.

#[using="Type"] Lemma rd1_mrd : forall m a, rd1 segs m a = mrd segs m a.
Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.

#[using="Type"] Lemma u_lden_range : forall E l, 0 <= bv_unsigned (lden E l) < two64.
Proof. LiaFast.lf_pins LiaFast.u0. intros E l. pose proof (bv_unsigned_in_range _ (lden E l)) as H. unfold bv_modulus in H. unfold two64. lia. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma rg_ok_of_rdwr : forall E m R A n,
  rg_kind R = RW -> rg_cont R = TEmpty -> bv_unsigned (lden E (rg_base R)) = A -> rsz E R = n -> 0 <= n -> A + n <= two64 ->
  (forall i, 0 <= i < n -> mrd segs m (wa (A + i)) <> None /\ wview segs m (wa (A + i)) <> None) ->
  rg_ok segs E m R.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E m R A n Hk Hc Hb Hs Hn HA H. unfold rg_ok. cbv zeta. rewrite Hb, Hs, Hk, Hc.
  split; [exact Hn|]. split; [exact HA|]. split.
  - intros i Hi. exact (H i Hi).
  - intros p v Hp. rewrite tget_empty in Hp. discriminate.
Qed.

#[using="Type"] Lemma rg_ok_of_u8arr : forall E m R A bs,
  rg_kind R = RW -> rg_cont R = TEmpty -> bv_unsigned (lden E (rg_base R)) = A -> rsz E R = Z.of_nat (length bs) ->
  u8arr segs m A bs -> rg_ok segs E m R.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E m R A bs Hk Hc Hb Hs (BA & WA). destruct BA as (B1 & B2 & B). destruct WA as (W1 & W2 & W).
  apply (rg_ok_of_rdwr E m R A (Z.of_nat (length bs))); try assumption; try lia.
  intros i Hi. split; [|exact (W i Hi)].
  pose proof (B (Z.to_nat i) ltac:(lia)) as R1. rewrite Z2Nat.id in R1 by lia. rewrite R1.
  destruct (nth_error bs (Z.to_nat i)) eqn:Hn; [discriminate|]. apply nth_error_None in Hn. lia.
Qed.

#[using="Type"] Lemma rg_ok_of_u64arr : forall E m R A ws,
  rg_kind R = RW -> rg_cont R = TEmpty -> bv_unsigned (lden E (rg_base R)) = A -> rsz E R = 8 * Z.of_nat (length ws) ->
  u64arr segs m A ws -> rg_ok segs E m R.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E m R A ws Hk Hc Hb Hs (BA & WA). destruct BA as (B1 & B2 & B). destruct WA as (W1 & W2 & W).
  rewrite u64s_length in B2.
  apply (rg_ok_of_rdwr E m R A (8 * Z.of_nat (length ws))); try assumption; try lia.
  intros i Hi. split; [|exact (W i Hi)].
  pose proof (B (Z.to_nat i) ltac:(rewrite u64s_length; lia)) as R1. rewrite Z2Nat.id in R1 by lia. rewrite R1.
  destruct (nth_error (u64s ws) (Z.to_nat i)) eqn:Hn; [discriminate|]. apply nth_error_None in Hn. rewrite u64s_length in Hn. lia.
Qed.

#[using="Type"] Lemma rg_ok_of_stk : forall E m R lo hi,
  rg_kind R = RW -> rg_cont R = TEmpty -> bv_unsigned (lden E (rg_base R)) = lo -> rsz E R = hi - lo -> lo <= hi ->
  stk segs m lo hi -> rg_ok segs E m R.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E m R lo hi Hk Hc Hb Hs Hlh (S1 & S2 & S).
  apply (rg_ok_of_rdwr E m R lo (hi - lo)); try assumption; try lia.
  - unfold two64. lia.
  - intros i Hi. destruct (S (lo + i) ltac:(lia)) as (Sw & b & Sr). split; [rewrite Sr; discriminate | exact Sw].
Qed.

#[using="Type"] Lemma rg_ok_of_rw_cells : forall E m R A cs,
  rg_kind R = RW -> rg_cont R = TEmpty -> bv_unsigned (lden E (rg_base R)) = A -> rsz E R = Z.of_nat (cells_size cs) ->
  rw_cells segs m A cs -> rg_ok segs E m R.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E m R A cs Hk Hc Hb Hs (CA & WA). destruct WA as (W1 & W2 & W).
  unfold cells_at in CA. destruct CA as (Hwf & BA). destruct BA as (B1 & B2 & B).
  pose proof (cells_bytes_length cs Hwf) as HL.
  apply (rg_ok_of_rdwr E m R A (Z.of_nat (cells_size cs))); try assumption; try lia.
  intros i Hi. split; [|exact (W i Hi)].
  pose proof (B (Z.to_nat i) ltac:(rewrite HL; lia)) as R1. rewrite Z2Nat.id in R1 by lia. rewrite R1.
  destruct (nth_error (cells_bytes cs) (Z.to_nat i)) eqn:Hn; [discriminate|]. apply nth_error_None in Hn.
  rewrite HL in Hn. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rg_ok_rt_of_rd : forall E m R A n,
  rg_kind R = RT -> rg_cont R = TEmpty -> bv_unsigned (lden E (rg_base R)) = A -> rsz E R = n -> 0 <= n -> A + n <= two64 ->
  (forall i, 0 <= i < n -> mrd segs m (wa (A + i)) <> None) -> rg_ok segs E m R.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E m R A n Hk Hc Hb Hs Hn HA H. unfold rg_ok. cbv zeta. rewrite Hb, Hs, Hk, Hc.
  split; [exact Hn|]. split; [exact HA|]. split.
  - intros i Hi. exact (H i Hi).
  - intros p v Hp. rewrite tget_empty in Hp. discriminate.
Qed.

#[using="Type"] Lemma rg_ok_rt_of_bytes_at : forall E m R A bs,
  rg_kind R = RT -> rg_cont R = TEmpty -> bv_unsigned (lden E (rg_base R)) = A -> rsz E R = Z.of_nat (length bs) ->
  bytes_at segs m A bs -> rg_ok segs E m R.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E m R A bs Hk Hc Hb Hs (B1 & B2 & B). apply (rg_ok_rt_of_rd E m R A (Z.of_nat (length bs))); try assumption; try lia.
  intros i Hi. pose proof (B (Z.to_nat i) ltac:(lia)) as R1. rewrite Z2Nat.id in R1 by lia. rewrite R1.
  destruct (nth_error bs (Z.to_nat i)) eqn:Hn; [discriminate|]. apply nth_error_None in Hn. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rg_ok_rz_of : forall E m R A n,
  rg_kind R = RZ -> rg_cont R = TEmpty -> bv_unsigned (lden E (rg_base R)) = A -> rsz E R = n -> 0 <= n -> A + n <= two64 ->
  (forall i, 0 <= i < n -> mrd segs m (wa (A + i)) = Some (Z_to_bv 8 0) /\ wview segs m (wa (A + i)) <> None) ->
  rg_ok segs E m R.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E m R A n Hk Hc Hb Hs Hn HA H. unfold rg_ok. cbv zeta. rewrite Hb, Hs, Hk, Hc.
  split; [exact Hn|]. split; [exact HA|]. split.
  - intros i Hi. destruct (H i Hi) as (Hr & Hw). split; [split; [rewrite rd1_mrd; unfold wa in Hr; rewrite Hr; discriminate | exact Hw]|].
    intros _. rewrite rd1_mrd. exact Hr.
  - intros p v Hp. rewrite tget_empty in Hp. discriminate.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rg_ok_tracked : forall E m R A n k,
  rg_kind R = k -> bv_unsigned (lden E (rg_base R)) = A -> rsz E R = n -> 0 <= n -> A + n <= two64 ->
  (forall i, 0 <= i < n ->
     match k with
     | RW => mrd segs m (wa (A + i)) <> None /\ wview segs m (wa (A + i)) <> None
     | RT => mrd segs m (wa (A + i)) <> None
     | _ => False
     end) ->
  (forall p v, tget p (rg_cont R) = Some v -> Zpos p - 1 < n /\ mrd segs m (wa (A + (Zpos p - 1))) = Some (bden E v)) ->
  rg_ok segs E m R.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E m R A n k Hk Hb Hs Hn HA H Ht. unfold rg_ok. cbv zeta. rewrite Hb, Hs, Hk.
  split; [exact Hn|]. split; [exact HA|]. split.
  - intros i Hi. pose proof (H i Hi) as X. destruct k; try (exfalso; exact X); exact X.
  - intros p v Hp. destruct (Ht p v Hp) as (H1 & H2). split; [exact H1 | exact H2].
Qed.

(* [comment removed for export] *)

#[using="Type"] Lemma rg_flat : forall E m R, rg_ok segs E m R ->
  0 <= rsz E R /\ bv_unsigned (lden E (rg_base R)) + rsz E R <= two64.
Proof. LiaFast.lf_pins LiaFast.u0. intros E m R (H1 & H2 & _). split; assumption. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rdwr_of_rg : forall E m R i, rg_ok segs E m R -> (rg_kind R = RW \/ rg_kind R = RZ \/ rg_kind R = RI) -> 0 <= i < rsz E R ->
  mrd segs m (wa (bv_unsigned (lden E (rg_base R)) + i)) <> None /\ wview segs m (wa (bv_unsigned (lden E (rg_base R)) + i)) <> None.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E m R i (_ & _ & H & _) Hk Hi. pose proof (H i Hi) as X. rewrite <- rd1_mrd. unfold wa.
  destruct Hk as [Hk|[Hk|Hk]]; rewrite Hk in X; [exact X | exact (proj1 X) | exact (proj1 X)].
Qed.

#[using="Type"] Lemma stk_of_rg : forall E m R lo hi, rg_ok segs E m R -> (rg_kind R = RW \/ rg_kind R = RZ \/ rg_kind R = RI) ->
  bv_unsigned (lden E (rg_base R)) = lo -> rsz E R = hi - lo -> stk segs m lo hi.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E m R lo hi HR Hk Hb Hs. pose proof (rg_flat E m R HR) as (F1 & F2). pose proof (u_lden_range E (rg_base R)) as U.
  split; [lia|]. split; [unfold two64 in *; lia|]. intros a Ha.
  destruct (rdwr_of_rg E m R (a - lo) HR Hk ltac:(lia)) as (Hr & Hw). rewrite Hb in Hr, Hw.
  replace (lo + (a - lo)) with a in Hr, Hw by lia. split; [exact Hw|].
  destruct (mrd segs m (wa a)) as [b|] eqn:E0; [exists b; reflexivity | exfalso; exact (Hr eq_refl)].
Qed.

#[using="Type"] Lemma wr_at_of_rg : forall E m R A n, rg_ok segs E m R -> (rg_kind R = RW \/ rg_kind R = RZ \/ rg_kind R = RI) ->
  bv_unsigned (lden E (rg_base R)) = A -> rsz E R = n -> wr_at segs m A n.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E m R A n HR Hk Hb Hs. pose proof (rg_flat E m R HR) as (F1 & F2). pose proof (u_lden_range E (rg_base R)) as U.
  split; [lia|]. split; [unfold two64 in *; lia|]. intros i Hi.
  destruct (rdwr_of_rg E m R i HR Hk ltac:(lia)) as (_ & Hw). rewrite Hb in Hw. exact Hw.
Qed.

#[using="Type"] Lemma rd_of_rg : forall E m R i, rg_ok segs E m R -> 0 <= i < rsz E R -> rg_kind R <> RO ->
  mrd segs m (wa (bv_unsigned (lden E (rg_base R)) + i)) <> None.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E m R i (_ & _ & H & _) Hi Hk. pose proof (H i Hi) as X. rewrite <- rd1_mrd. unfold wa.
  destruct (rg_kind R); [exact (proj1 X) | exfalso; exact (Hk eq_refl) | exact (proj1 (proj1 X)) | exact (proj1 (proj1 X)) | exact X].
Qed.

#[using="Type"] Lemma bytes_at_of_tracked : forall E m R (bs : list byte),
  rg_ok segs E m R -> Z.of_nat (length bs) <= rsz E R ->
  (forall i, (i < length bs)%nat -> exists v, tget (okey (Z.of_nat i)) (rg_cont R) = Some v /\ nth_error bs i = Some (bden E v)) ->
  bytes_at segs m (bv_unsigned (lden E (rg_base R))) bs.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E m R bs HR Hl H. pose proof (rg_flat E m R HR) as (F1 & F2). pose proof (u_lden_range E (rg_base R)) as U.
  destruct HR as (_ & _ & _ & Ht).
  split; [lia|]. split; [unfold two64 in *; lia|]. intros i Hi.
  destruct (H i Hi) as (v & Hv & Hn). destruct (Ht _ _ Hv) as (_ & Hr). rewrite Hn.
  unfold okey in Hr. rewrite Z2Pos.id in Hr by lia. replace (Z.of_nat i + 1 - 1) with (Z.of_nat i) in Hr by lia.
  rewrite <- rd1_mrd. exact Hr.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma zero_bytes_of_rz : forall E m R i, rg_ok segs E m R -> rg_kind R = RZ -> rg_cont R = TEmpty -> 0 <= i < rsz E R ->
  mrd segs m (wa (bv_unsigned (lden E (rg_base R)) + i)) = Some (Z_to_bv 8 0).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E m R i (_ & _ & H & _) Hk Hc Hi. pose proof (H i Hi) as X. rewrite Hk in X. destruct X as (_ & X). rewrite Hc in X.
  rewrite <- rd1_mrd. unfold wa. apply X. apply tget_empty.
Qed.


(* [comment removed for export] *)

#[using="Type"] Lemma bytes_exist : forall m A n, 0 <= A -> A + Z.of_nat n <= 2 ^ 64 ->
  (forall i, (i < n)%nat -> mrd segs m (wa (A + Z.of_nat i)) <> None) ->
  exists bs, bytes_at segs m A bs /\ length bs = n.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros m A n HA Hn H. revert A HA Hn H. induction n as [|n IH]; intros A HA Hn H.
  - exists []. split; [split; [lia|]; split; [cbn; lia|]; intros i Hi; cbn in Hi; lia | reflexivity].
  - destruct (mrd segs m (wa A)) as [b|] eqn:Hb; [|exfalso; apply (H 0%nat ltac:(lia)); rewrite Z.add_0_r; exact Hb].
    destruct (IH (A + 1) ltac:(lia) ltac:(lia)) as (bs & Hbs & Hl).
    { intros i Hi. replace (A + 1 + Z.of_nat i) with (A + Z.of_nat (S i)) by lia. apply H. lia. }
    exists (b :: bs). split; [|cbn; rewrite Hl; reflexivity].
    destruct Hbs as (_ & B2 & B). split; [lia|]. split; [cbn [length]; lia|].
    intros [|i] Hi; cbn [nth_error].
    + rewrite Z.add_0_r. exact Hb.
    + replace (A + Z.of_nat (S i)) with (A + 1 + Z.of_nat i) by lia. apply B. cbn in Hi. lia.
Qed.

#[using="Type"] Lemma le8_lez : forall bs, length bs = 8%nat -> le8 (Z_to_bv 64 (lez bs)) = bs.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros bs Hl. unfold le8, word_to_le_bytes.
  rewrite u_small64 by (pose proof (lez_bound_len bs 8 Hl) as X; unfold two64; lia).
  rewrite <- Hl at 1. apply Z_to_le_bytes_lez.
Qed.

#[using="Type"] Lemma u64s_exist : forall k bs, length bs = (8 * k)%nat -> exists ws, u64s ws = bs /\ length ws = k.
Proof. LiaFast.lf_pins LiaFast.u0.
  induction k as [|k IH]; intros bs Hl.
  - exists []. destruct bs; [split; reflexivity | cbn in Hl; lia].
  - assert (H8 : (8 <= length bs)%nat) by lia.
    destruct (IH (skipn 8 bs) ltac:(rewrite length_skipn; lia)) as (ws & Hws & Hk).
    exists (Z_to_bv 64 (lez (firstn 8 bs)) :: ws). split; [|cbn; rewrite Hk; reflexivity].
    cbn [u64s]. rewrite le8_lez by (rewrite length_firstn; lia). rewrite Hws. apply firstn_skipn.
Qed.

#[using="Type"] Lemma u64arr_of_rg : forall E m R A k, rg_ok segs E m R -> (rg_kind R = RW \/ rg_kind R = RZ \/ rg_kind R = RI) ->
  bv_unsigned (lden E (rg_base R)) = A -> rsz E R = 8 * Z.of_nat k -> exists ws, u64arr segs m A ws /\ length ws = k.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E m R A k HR Hk Hb Hs. pose proof (rg_flat E m R HR) as (F1 & F2). pose proof (u_lden_range E (rg_base R)) as U.
  assert (Hrd : forall i, (i < 8 * k)%nat -> mrd segs m (wa (A + Z.of_nat i)) <> None).
  { intros i Hi. pose proof (rdwr_of_rg E m R (Z.of_nat i) HR Hk ltac:(lia)) as (Hr & _). rewrite Hb in Hr. exact Hr. }
  destruct (bytes_exist m A (8 * k) ltac:(lia) ltac:(unfold two64 in *; lia) Hrd) as (bs & Hbs & Hl).
  destruct (u64s_exist k bs Hl) as (ws & Hws & Hk8). exists ws. split; [|exact Hk8].
  split; [rewrite Hws; exact Hbs|]. rewrite Hk8.
  pose proof (wr_at_of_rg E m R A (rsz E R) HR Hk Hb eq_refl) as W. rewrite Hs in W. exact W.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rg_ok_frame : forall E m m' R, rg_ok segs E m R ->
  (forall i, 0 <= i < rsz E R -> m' (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + i)) = m (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + i))) ->
  rg_ok segs E m' R.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E m m' R HR Hf. destruct HR as (H1 & H2 & H3 & H4). split; [exact H1|]. split; [exact H2|]. split.
  - intros i Hi. pose proof (H3 i Hi) as X. pose proof (Hf i Hi) as Y.
    assert (Er : rd1 segs m' (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + i)) = rd1 segs m (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + i)))
      by (unfold rd1; rewrite Y; reflexivity).
    assert (Ew : wview segs m' (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + i)) = wview segs m (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + i)))
      by (unfold wview; rewrite Y; reflexivity).
    destruct (rg_kind R); rewrite ?Er, ?Ew, ?Y; exact X.
  - intros p v Hp. destruct (H4 p v Hp) as (Hlt & Hr). split; [exact Hlt|].
    unfold rd1 in *. rewrite Hf; [exact Hr|]. pose proof (Pos2Z.is_pos p). lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma pristine_of_rg_ro : forall E m R A n, rg_ok segs E m R -> rg_kind R = RO ->
  bv_unsigned (lden E (rg_base R)) = A -> rsz E R = n -> pristine m A (A + n).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E m R A n HR Hk Hb Hs. pose proof (rg_flat E m R HR) as (F1 & F2). pose proof (u_lden_range E (rg_base R)) as U.
  destruct HR as (_ & _ & H & _). split; [lia|]. split; [unfold two64 in *; lia|]. intros i Hi.
  pose proof (H (i - A) ltac:(lia)) as X. rewrite Hk in X. rewrite Hb in X. replace (A + (i - A)) with i in X by lia.
  exact (proj1 X).
Qed.

#[using="Type"] Lemma zeros_bytes_of_rz : forall E m R A n, rg_ok segs E m R -> rg_kind R = RZ -> rg_cont R = TEmpty ->
  bv_unsigned (lden E (rg_base R)) = A -> rsz E R = Z.of_nat n ->
  bytes_at segs m A (repeat (Z_to_bv 8 0) n).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E m R A n HR Hk Hc Hb Hs. pose proof (rg_flat E m R HR) as (F1 & F2). pose proof (u_lden_range E (rg_base R)) as U.
  split; [lia|]. split; [rewrite repeat_length; unfold two64 in *; lia|]. intros i Hi. rewrite repeat_length in Hi.
  rewrite nth_error_repeat by exact Hi.
  pose proof (zero_bytes_of_rz E m R (Z.of_nat i) HR Hk Hc ltac:(lia)) as X. rewrite Hb in X. exact X.
Qed.

(* [comment removed for export] *)
Definition with_rom (ms : machine_state) (r : word -> option byte) : machine_state :=
  {| ms_regs := ms_regs ms; ms_fregs := ms_fregs ms; ms_pc_val := ms_pc_val ms; ms_svc_pending := ms_svc_pending ms;
     ms_resv := ms_resv ms; ms_fcsr := ms_fcsr ms; ms_mem := ms_mem ms; ms_rom := r |}.

#[using="Type"] Lemma step_with_rom : forall ms ms' r, RiscvSemantics.step segs ms = MachineOk ms' ->
  RiscvSemantics.step segs (with_rom ms r) = MachineOk (with_rom ms' r).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros ms ms' r H. destruct ms as [rg fr pc sv rs fc mem rom]. unfold with_rom in *.
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom] in *.
  unfold RiscvSemantics.step, drop_access_report, step_accesses, ms_pc in *. cbn [ms_pc_val ms_mem] in *.
  destruct (fetch_word segs pc) as [w|] eqn:F1.
  - unfold decode_exec_accesses in *. cbn [ms_regs ms_fregs ms_pc_val ms_resv ms_fcsr ms_mem ms_rom ms_reg] in *.
    destruct (is_ecall w); [injection H as <-; reflexivity|].
    destruct (decode_any w) as [[i isz]|]; [|destruct (is_defined_illegal w); discriminate].
    destruct (interp_eff_accesses _ _ _) as [rep| |]; try discriminate. destruct rep as [[c m'] acc]. cbn in *. injection H as <-. reflexivity.
  - destruct (fetch_word_ov segs mem pc) as [w|] eqn:F2.
    + unfold decode_exec_accesses in *. cbn [ms_regs ms_fregs ms_pc_val ms_resv ms_fcsr ms_mem ms_rom ms_reg] in *.
      destruct (is_ecall w); [injection H as <-; reflexivity|].
      destruct (decode_any w) as [[i isz]|]; [|destruct (is_defined_illegal w); discriminate].
      destruct (interp_eff_accesses _ _ _) as [rep| |]; try discriminate. destruct rep as [[c m'] acc]. cbn in *. injection H as <-. reflexivity.
    + destruct (fetch_tail_any segs mem pc) as [w|] eqn:F3.
      * unfold decode_exec_accesses in *. cbn [ms_regs ms_fregs ms_pc_val ms_resv ms_fcsr ms_mem ms_rom ms_reg] in *.
        destruct (is_ecall w); [injection H as <-; reflexivity|].
        destruct (decode_any w) as [[i isz]|]; [|destruct (is_defined_illegal w); discriminate].
        destruct (interp_eff_accesses _ _ _) as [rep| |]; try discriminate. destruct rep as [[c m'] acc]. cbn in *. injection H as <-. reflexivity.
      * unfold fetch_failure in H. destruct (negb _); [discriminate|]. destruct (_ || _)%bool; discriminate.
Qed.

#[using="Type"] Lemma with_rom_with_rom : forall ms r r', with_rom (with_rom ms r) r' = with_rom ms r'.
Proof. LiaFast.lf_pins LiaFast.u0. intros. reflexivity. Qed.
#[using="Type"] Lemma with_rom_eta : forall ms, with_rom ms (ms_rom ms) = ms.
Proof. LiaFast.lf_pins LiaFast.u0. intros [rg fr pc sv rs fc mem rom]. reflexivity. Qed.

#[using="Type"] Lemma msteps_with_rom : forall ms ms', msteps segs ms ms' -> forall r, msteps segs (with_rom ms r) (with_rom ms' r).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros ms ms' H. induction H as [ms|ms ms1 ms2 (Hs & Hst) _ IH]; intros r; [apply msteps_refl|].
  eapply msteps_cons; [|apply IH]. split; [exact Hs | exact (step_with_rom ms ms1 r Hst)].
Qed.

#[using="Type"] Lemma isteps_of_msteps : forall ms ms', msteps segs ms ms' -> isteps segs ms ms'.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros ms ms' H. induction H as [ms|ms ms1 ms2 (Hs & Hst) _ IH]; [apply ist_refl|]. eapply ist_step; [exact Hs | exact Hst | exact IH].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma evt_at_rom : forall (POST : machine_state -> Prop) ms r,
  evt segs POST (with_rom ms r) ->
  exists ms1 ms2, isteps segs ms ms1 /\ ms_eqv ms1 (with_rom ms2 (ms_rom ms)) /\ POST ms2.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros POST ms r (ms1 & ms2 & Hst & Heq & HP).
  exists (with_rom ms1 (ms_rom ms)), ms2. split; [|split; [|exact HP]].
  - apply isteps_of_msteps. rewrite <- (with_rom_eta ms) at 1. rewrite <- (with_rom_with_rom ms r (ms_rom ms)).
    exact (msteps_with_rom _ _ Hst (ms_rom ms)).
  - destruct Heq as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8). unfold with_rom. repeat split; cbn; assumption.
Qed.

End Bridge.
