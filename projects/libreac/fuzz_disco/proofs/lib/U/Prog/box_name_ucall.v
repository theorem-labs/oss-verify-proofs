From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes Arr ZBridge.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_box_name_model.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import reac_box_name_c sb_ch_c sb_dec_c.
Import ListNotations.
Open Scope Z_scope.

Definition bbuf (m : word -> option byte) (A : Z) (n : nat) (c : list Z) : Prop :=
  exists r, (length c + length r = n)%nat /\ u8arr rsegs m A (bn_bytes c ++ r).

Definition nn (cap : Z) (s : list Z) : Z := Z.min (Z.of_nat (length s)) (cap - 1).
Definition ovf (cap : Z) (s : list Z) : word := Z_to_bv 64 (if cap - 1 <? Z.of_nat (length s) then 1 else 0).
Definition rcells (B cap : Z) (s : list Z) (pad : word) : list cell :=
  [C8 (Z_to_bv 64 B); C8 (Z_to_bv 64 cap); C8 (Z_to_bv 64 (nn cap s)); C4 (ovf cap s); C4 pad].
Definition sbx (m : word -> option byte) (A B cap : Z) (s : list Z) : Prop :=
  (exists pad, rw_cells rsegs m A (rcells B cap s pad)) /\
  bbuf m B (Z.to_nat cap) (firstn (Z.to_nat (cap - 1)) s).

Lemma bn_bytes_length : forall c, length (bn_bytes c) = length c.
Proof. intros c. unfold bn_bytes. apply length_map. Qed.

Lemma bn_bytes_app : forall a b, bn_bytes (a ++ b) = bn_bytes a ++ bn_bytes b.
Proof. intros a b. unfold bn_bytes. apply map_app. Qed.

Lemma nn_rng : forall cap s, 1 <= cap -> 0 <= nn cap s <= cap - 1.
Proof. intros cap s H. unfold nn. lia. Qed.

Lemma le1_lit : forall c, 0 <= c < 2^64 -> le1 (Z_to_bv 64 c) = [Z_to_bv 8 c].
Proof. intros c Hc. unfold le1. rewrite unsigned_lit by lia. reflexivity. Qed.

Lemma wr_at_prefix : forall m A n k, wr_at rsegs m A n -> 0 <= k <= n -> wr_at rsegs m A k.
Proof. intros m A n k (H1 & H2 & H) Hk. split; [lia|]. split; [lia|]. intros j Hj. apply H. lia. Qed.

Lemma wr_at_sub : forall m A n k l, wr_at rsegs m A n -> 0 <= k -> 0 <= l -> k + l <= n -> wr_at rsegs m (A + k) l.
Proof.
  intros m A n k l (H1 & H2 & H) Hk Hl Hkl. split; [lia|]. split; [lia|].
  intros j Hj. replace (A + k + j) with (A + (k + j)) by lia. apply H. lia.
Qed.

Lemma rec_bytes : forall p c n ov pad,
  cells_bytes [C8 p; C8 c; C8 n; C4 ov; C4 pad] = sb_rec p c n ov ++ le4 pad.
Proof. intros. unfold sb_rec. cbn [cells_bytes cbytes]. rewrite app_nil_r, <- !app_assoc. reflexivity. Qed.

Lemma sb_rec_length : forall p c n ov, length (sb_rec p c n ov) = 28%nat.
Proof. intros. unfold sb_rec. rewrite !length_app, !length_le8, length_le4. reflexivity. Qed.

Lemma rec_get : forall m A p c n ov pad, rw_cells rsegs m A [C8 p; C8 c; C8 n; C4 ov; C4 pad] ->
  bytes_at rsegs m A (sb_rec p c n ov) /\ bytes_at rsegs m (A + 28) (le4 pad) /\ wr_at rsegs m A 32.
Proof.
  intros m A p c n ov pad [[_ Hb] Hw]. rewrite rec_bytes in Hb. apply bytes_at_app in Hb.
  rewrite sb_rec_length in Hb. destruct Hb as [H1 H2]. split; [exact H1|]. split; [exact H2|exact Hw].
Qed.

Lemma rec_put : forall m A p c n ov pad,
  bytes_at rsegs m A (sb_rec p c n ov) -> bytes_at rsegs m (A + 28) (le4 pad) -> wr_at rsegs m A 32 ->
  rw_cells rsegs m A [C8 p; C8 c; C8 n; C4 ov; C4 pad].
Proof.
  intros m A p c n ov pad H1 H2 Hw. split; [split|].
  - cbn. repeat split.
  - rewrite rec_bytes. apply bytes_at_app. rewrite sb_rec_length. split; assumption.
  - exact Hw.
Qed.

Lemma bytes_at_keep : forall W m m' A bs, bytes_at rsegs m A bs -> munch W m m' ->
  (forall x, A <= x < A + Z.of_nat (length bs) -> outside W x) -> bytes_at rsegs m' A bs.
Proof.
  intros W m m' A bs (Ha & Hl & H) MU Ho. split; [lia|]. split; [lia|].
  intros j Hj. unfold mrd. rewrite MU; [apply H; exact Hj|]. rewrite wa_unsigned by lia. apply Ho. lia.
Qed.

Lemma stk_keep : forall W m m' lo hi, stk rsegs m lo hi -> munch W m m' -> wmono rsegs m m' ->
  (forall x, lo <= x < hi -> outside W x) -> stk rsegs m' lo hi.
Proof.
  intros W m m' lo hi (H1 & H2 & H) MU WM Ho. split; [lia|]. split; [lia|].
  intros a Ha. destruct (H a Ha) as [Hw (b & Hb)]. split; [apply WM; exact Hw|].
  exists b. unfold mrd in *. rewrite MU; [exact Hb|]. rewrite wa_unsigned by lia. apply Ho. exact Ha.
Qed.

Lemma bbuf_wr : forall m B n c, bbuf m B n c -> wr_at rsegs m B (Z.of_nat n) /\ 0 <= B /\ B + Z.of_nat n <= 2^64.
Proof.
  intros m B n c (r & L & Hb & Hw). rewrite length_app, bn_bytes_length, L in Hw.
  pose proof Hw as (W1 & W2 & _). split; [exact Hw|]. lia.
Qed.

Lemma bbuf_keep : forall W m m' B n c, bbuf m B n c -> munch W m m' -> wmono rsegs m m' ->
  (forall x, B <= x < B + Z.of_nat n -> outside W x) -> bbuf m' B n c.
Proof.
  intros W m m' B n c (r & L & Hb & Hw) MU WM Ho. exists r. split; [exact L|]. split.
  - eapply bytes_at_keep; [exact Hb|exact MU|]. intros x Hx. apply Ho.
    rewrite length_app, bn_bytes_length in Hx. lia.
  - eapply wr_at_transport; [exact Hw|exact WM].
Qed.

Lemma bbuf_patch : forall W m m' A n c D,
  bbuf m A n c -> munch W m m' -> wmono rsegs m m' ->
  bytes_at rsegs m' (A + Z.of_nat (length c)) (bn_bytes D) -> (length c + length D <= n)%nat ->
  (forall x, A <= x < A + Z.of_nat n -> x < A + Z.of_nat (length c) \/ A + Z.of_nat (length c + length D) <= x ->
             outside W x) ->
  bbuf m' A n (c ++ D).
Proof.
  intros W m m' A n c D (r & L & Hb & Hw) MU WM HD Hn Ho.
  exists (skipn (length D) r). split; [rewrite length_app, length_skipn; lia|].
  pose proof (bytes_at_bound rsegs _ _ _ Hb) as BB. rewrite length_app, bn_bytes_length in BB.
  apply bytes_at_app in Hb. destruct Hb as [Hc Hr]. rewrite bn_bytes_length in Hr.
  rewrite <- (firstn_skipn (length D) r) in Hr. apply bytes_at_app in Hr. destruct Hr as [_ Hr].
  rewrite length_firstn in Hr. replace (Nat.min (length D) (length r)) with (length D) in Hr by lia.
  split.
  - rewrite bn_bytes_app, <- app_assoc. apply bytes_at_app. split.
    + eapply bytes_at_keep; [exact Hc|exact MU|]. intros x Hx. apply Ho; rewrite bn_bytes_length in Hx; lia.
    + rewrite bn_bytes_length. apply bytes_at_app. split; [exact HD|]. rewrite bn_bytes_length.
      eapply bytes_at_keep; [exact Hr|exact MU|]. intros x Hx. rewrite length_skipn in Hx. apply Ho; lia.
  - eapply wr_at_transport; [|exact WM].
    rewrite length_app, bn_bytes_length, length_app, length_skipn.
    replace (Z.of_nat (length c + length D + (length r - length D))) with (Z.of_nat (length (bn_bytes c ++ r)))
      by (rewrite length_app, bn_bytes_length; lia).
    exact Hw.
Qed.

Lemma u8arr_stk : forall m A bs, u8arr rsegs m A bs -> stk rsegs m A (A + Z.of_nat (length bs)).
Proof.
  intros m A bs H. apply rw_cells_of_u8arr in H. apply stk_of_rw_cells in H.
  cbn [cells_size csize] in H. rewrite Nat.add_0_r in H. exact H.
Qed.

Lemma sbx_stk : forall m A B cap s, sbx m A B cap s -> 1 <= cap ->
  stk rsegs m A (A + 32) /\ stk rsegs m B (B + cap).
Proof.
  intros m A B cap s ((pad & RC) & (r & L & U)) Hc. split.
  - apply stk_of_rw_cells in RC. exact RC.
  - apply u8arr_stk in U. rewrite length_app, bn_bytes_length, L, Z2Nat.id in U by lia. exact U.
Qed.

Lemma sbx_ch_st : forall m m' A B cap s c pad,
  rw_cells rsegs m A (rcells B cap s pad) -> bbuf m B (Z.to_nat cap) (firstn (Z.to_nat (cap - 1)) s) ->
  1 <= cap -> (B + cap <= A \/ A + 32 <= B) -> wmono rsegs m m' ->
  nn cap s + 1 < cap ->
  munch [(A + 16, A + 24); (B + nn cap s, B + nn cap s + 1)] m m' ->
  bytes_at rsegs m' A (sb_rec (Z_to_bv 64 B) (Z_to_bv 64 cap) (Z_to_bv 64 (nn cap s + 1)) (ovf cap s)) ->
  bytes_at rsegs m' (B + nn cap s) [Z_to_bv 8 c] ->
  sbx m' A B cap (s ++ [c]).
Proof.
  intros m m' A B cap s c pad RC BB Hcap DJ WM HC MU HB HY.
  assert (L : nn cap s = Z.of_nat (length s)) by (unfold nn in *; lia).
  assert (F1 : firstn (Z.to_nat (cap - 1)) s = s) by (apply firstn_all2; lia).
  assert (F2 : firstn (Z.to_nat (cap - 1)) (s ++ [c]) = s ++ [c])
    by (apply firstn_all2; rewrite length_app; cbn [length]; lia).
  assert (N2 : nn cap (s ++ [c]) = nn cap s + 1) by (unfold nn in *; rewrite length_app; cbn [length]; lia).
  assert (O2 : ovf cap (s ++ [c]) = ovf cap s).
  { unfold ovf. rewrite length_app. cbn [length].
    replace (cap - 1 <? Z.of_nat (length s + 1)) with false by (symmetry; apply Z.ltb_ge; lia).
    replace (cap - 1 <? Z.of_nat (length s)) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
  destruct (rec_get _ _ _ _ _ _ _ RC) as (_ & HP & HW).
  pose proof (bbuf_wr _ _ _ _ BB) as (BW & B0 & B1).
  split.
  - exists pad. unfold rcells. rewrite N2, O2. apply rec_put; [exact HB| |eapply wr_at_transport; [exact HW|exact WM]].
    eapply bytes_at_keep; [exact HP|exact MU|]. rewrite length_le4. intros x Hx. cbn [outside]. lia.
  - rewrite F2. rewrite F1 in BB. eapply (bbuf_patch _ m m' B (Z.to_nat cap) s [c]); [exact BB|exact MU|exact WM| | |].
    + rewrite <- L. exact HY.
    + cbn [length]. lia.
    + intros x Hx Hx2. cbn [length outside] in *. lia.
Qed.

Lemma sbx_ch_ov : forall m m' A B cap s c pad,
  rw_cells rsegs m A (rcells B cap s pad) -> bbuf m B (Z.to_nat cap) (firstn (Z.to_nat (cap - 1)) s) ->
  1 <= cap -> (B + cap <= A \/ A + 32 <= B) -> wmono rsegs m m' ->
  cap <= nn cap s + 1 ->
  munch [(A + 24, A + 28)] m m' ->
  bytes_at rsegs m' A (sb_rec (Z_to_bv 64 B) (Z_to_bv 64 cap) (Z_to_bv 64 (nn cap s)) (Z_to_bv 64 1)) ->
  sbx m' A B cap (s ++ [c]).
Proof.
  intros m m' A B cap s c pad RC BB Hcap DJ WM HC MU HB.
  assert (L : cap - 1 <= Z.of_nat (length s)) by (unfold nn in *; lia).
  assert (F2 : firstn (Z.to_nat (cap - 1)) (s ++ [c]) = firstn (Z.to_nat (cap - 1)) s).
  { rewrite firstn_app. replace (Z.to_nat (cap - 1) - length s)%nat with 0%nat by lia.
    cbn [firstn]. rewrite app_nil_r. reflexivity. }
  assert (N2 : nn cap (s ++ [c]) = nn cap s) by (unfold nn in *; rewrite length_app; cbn [length]; lia).
  assert (O2 : ovf cap (s ++ [c]) = Z_to_bv 64 1).
  { unfold ovf. rewrite length_app. cbn [length].
    replace (cap - 1 <? Z.of_nat (length s + 1)) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
  destruct (rec_get _ _ _ _ _ _ _ RC) as (_ & HP & HW).
  pose proof (bbuf_wr _ _ _ _ BB) as (BW & B0 & B1).
  split.
  - exists pad. unfold rcells. rewrite N2, O2. apply rec_put; [exact HB| |eapply wr_at_transport; [exact HW|exact WM]].
    eapply bytes_at_keep; [exact HP|exact MU|]. rewrite length_le4. intros x Hx. cbn [outside]. lia.
  - rewrite F2. eapply bbuf_keep; [exact BB|exact MU|exact WM|]. intros x Hx. cbn [outside]. lia.
Qed.

Lemma sbx_dec : forall m m' A B cap s D pad sp0,
  rw_cells rsegs m A (rcells B cap s pad) -> bbuf m B (Z.to_nat cap) (firstn (Z.to_nat (cap - 1)) s) ->
  1 <= cap -> (B + cap <= A \/ A + 32 <= B) -> wmono rsegs m m' -> sp0 <= A -> sp0 <= B ->
  munch [(sp0 - 64, sp0); (A + 16, A + 28);
         (B + nn cap s, B + nn cap s + Z.min (Z.of_nat (length D)) (sb_dec_room cap (nn cap s)))] m m' ->
  bytes_at rsegs m' A (sb_rec (Z_to_bv 64 B) (Z_to_bv 64 cap)
     (Z_to_bv 64 (nn cap s + Z.min (Z.of_nat (length D)) (sb_dec_room cap (nn cap s))))
     (if sb_dec_room cap (nn cap s) <? Z.of_nat (length D) then Z_to_bv 64 1 else ovf cap s)) ->
  (0 < sb_dec_room cap (nn cap s) ->
   bytes_at rsegs m' (B + nn cap s)
     (map (Z_to_bv 8) (firstn (Z.to_nat (Z.min (Z.of_nat (length D)) (sb_dec_room cap (nn cap s)))) D))) ->
  sbx m' A B cap (s ++ D).
Proof.
  intros m m' A B cap s D pad sp0 RC BB Hcap DJ WM HS1 HS2 MU HB HY.
  pose proof (nn_rng cap s Hcap) as NR.
  assert (RM : sb_dec_room cap (nn cap s) = cap - 1 - nn cap s).
  { unfold sb_dec_room. replace (nn cap s + 1 <=? cap) with true by (symmetry; apply Z.leb_le; lia). reflexivity. }
  rewrite RM in MU, HB, HY.
  destruct (rec_get _ _ _ _ _ _ _ RC) as (_ & HP & HW).
  pose proof (bbuf_wr _ _ _ _ BB) as (BW & B0 & B1).
  assert (N2 : nn cap (s ++ D) = nn cap s + Z.min (Z.of_nat (length D)) (cap - 1 - nn cap s))
    by (unfold nn in *; rewrite length_app; lia).
  assert (O2 : ovf cap (s ++ D) =
               if cap - 1 - nn cap s <? Z.of_nat (length D) then Z_to_bv 64 1 else ovf cap s).
  { unfold ovf, nn. rewrite length_app.
    destruct (Z.ltb_spec (cap - 1 - Z.min (Z.of_nat (length s)) (cap - 1)) (Z.of_nat (length D)));
    destruct (Z.ltb_spec (cap - 1) (Z.of_nat (length s + length D)));
    destruct (Z.ltb_spec (cap - 1) (Z.of_nat (length s))); try reflexivity; exfalso; lia. }
  split.
  - exists pad. unfold rcells. rewrite N2, O2. apply rec_put; [exact HB | | eapply wr_at_transport; [exact HW|exact WM]].
    eapply bytes_at_keep; [exact HP|exact MU|]. rewrite length_le4. intros x Hx. cbn [outside]. lia.
  - destruct (Z.ltb_spec (nn cap s) (cap - 1)) as [LT|GE].
    + assert (L : nn cap s = Z.of_nat (length s)) by (unfold nn in *; lia).
      assert (F1 : firstn (Z.to_nat (cap - 1)) s = s) by (apply firstn_all2; lia).
      assert (F2 : firstn (Z.to_nat (cap - 1)) (s ++ D) =
                   s ++ firstn (Z.to_nat (Z.min (Z.of_nat (length D)) (cap - 1 - nn cap s))) D).
      { rewrite firstn_app, F1. f_equal.
        destruct (Nat.le_ge_cases (length D) (Z.to_nat (cap - 1) - length s)) as [H|H].
        - rewrite !firstn_all2 by lia. reflexivity.
        - f_equal. lia. }
      rewrite F2. rewrite F1 in BB.
      eapply (bbuf_patch _ m m' B (Z.to_nat cap) s); [exact BB|exact MU|exact WM| | |].
      * rewrite <- L. exact (HY ltac:(lia)).
      * rewrite length_firstn. lia.
      * intros x Hx Hx2. rewrite length_firstn in Hx2. cbn [outside]. lia.
    + assert (L : nn cap s = cap - 1) by lia.
      assert (F2 : firstn (Z.to_nat (cap - 1)) (s ++ D) = firstn (Z.to_nat (cap - 1)) s).
      { rewrite firstn_app. replace (Z.to_nat (cap - 1) - length s)%nat with 0%nat by (unfold nn in L; lia).
        cbn [firstn]. rewrite app_nil_r. reflexivity. }
      rewrite F2. eapply bbuf_keep; [exact BB|exact MU|exact WM|]. intros x Hx. cbn [outside]. lia.
Qed.

Section Calls.
Hypothesis SBCH : sb_ch_contract.
Hypothesis DEC : sb_dec_contract.

Lemma ch_call : forall (Q : machine_state -> Prop)
    (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (r lo hi A B cap c : Z) (s : list Z),
  0 <= r < 2^64 -> r mod 2 = 0 ->
  bv_unsigned a0 = A -> A mod 8 = 0 -> a1 = Z_to_bv 64 c -> 0 <= c < 256 -> 1 <= cap ->
  sbx m A B cap s -> (B + cap <= A \/ A + 32 <= B) ->
  mem_inv rsegs m -> stk rsegs m lo hi -> 0 < hi -> hi <= A -> hi <= B ->
  (forall (m' : word -> option byte) (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
     sbx m' A B cap (s ++ [c]) -> munch [(A, A + 32); (B, B + cap)] m m' -> wmono rsegs m m' ->
     mem_inv rsegs m' -> stk rsegs m' lo hi ->
     evt rsegs Q (MS (mkR (Z_to_bv 64 r) sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                     F (Z_to_bv 64 r) fc None m' (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR (Z_to_bv 64 r) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 SB_CH) fc None m (seg_rom rsegs)).
Proof.
  intros Q sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    r lo hi A B cap c s Hr Hr2 HA HAL Ha1 Hc Hcap ((pad & RC) & BB) DJ MI ST H0 HHA HHB K.
  destruct (rec_get _ _ _ _ _ _ _ RC) as (HB & HP & HW).
  pose proof (bbuf_wr _ _ _ _ BB) as (BW & B0 & B1).
  pose proof (nn_rng cap s Hcap) as NR.
  pose proof (zr_word a0) as Ra0. unfold inr64 in Ra0.
  eapply evt_cut.
  { eapply SBCH with (p := Z_to_bv 64 B) (cap := Z_to_bv 64 cap) (n := Z_to_bv 64 (nn cap s)) (over := ovf cap s).
    - rewrite HA. exact HAL.
    - rewrite HA. exact HB.
    - rewrite HA. eapply wr_at_prefix; [exact HW|lia].
    - rewrite unsigned_lit by lia. lia.
    - rewrite !unsigned_lit by lia. intros Hlt. split; [lia|]. split; [lia|]. split.
      + eapply wr_at_sub; [exact BW|lia|lia|lia].
      + rewrite HA. lia.
    - exact MI. }
  intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
              E & WM & MI' & POST).
  subst ms'. rewrite ret_pc_even by (first [exact Hr | exact Hr2]).
  rewrite HA, !unsigned_lit in POST by lia. rewrite Ha1, le1_lit in POST by lia.
  destruct POST as [(HC & MU & HB') | (HC & MU & HB' & HY)].
  - apply K; [eapply sbx_ch_ov; eassumption | | exact WM | exact MI' |].
    + eapply munch_weaken; [|exact MU]. intros x Hx. cbn [outside] in *. lia.
    + eapply stk_keep; [exact ST|exact MU|exact WM|]. intros x Hx. cbn [outside]. lia.
  - apply K; [eapply sbx_ch_st; eassumption | | exact WM | exact MI' |].
    + eapply munch_weaken; [|exact MU]. intros x Hx. cbn [outside] in *. lia.
    + eapply stk_keep; [exact ST|exact MU|exact WM|]. intros x Hx. cbn [outside]. lia.
Qed.

Lemma dec_call : forall (Q : machine_state -> Prop)
    (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (r lo A B cap v md : Z) (s : list Z),
  0 <= r < 2^64 -> r mod 2 = 0 ->
  bv_unsigned a0 = A -> A mod 8 = 0 -> 0 <= v < 2^31 -> a1 = Z_to_bv 64 v -> (md = 1 \/ md = 2) ->
  a2 = Z_to_bv 64 md -> 1 <= cap ->
  sbx m A B cap s -> (B + cap <= A \/ A + 32 <= B) ->
  mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> lo + 64 <= bv_unsigned sp ->
  bv_unsigned sp <= A -> bv_unsigned sp <= B ->
  (forall (m' : word -> option byte) (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
     sbx m' A B cap (s ++ sb_dec_D v md) ->
     munch [(bv_unsigned sp - 64, bv_unsigned sp); (A, A + 32); (B, B + cap)] m m' -> wmono rsegs m m' ->
     mem_inv rsegs m' -> stk rsegs m' lo (bv_unsigned sp) ->
     evt rsegs Q (MS (mkR (Z_to_bv 64 r) sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                     F (Z_to_bv 64 r) fc None m' (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR (Z_to_bv 64 r) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 SB_DEC) fc None m (seg_rom rsegs)).
Proof.
  intros Q sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    r lo A B cap v md s Hr Hr2 HA HAL Hv Ha1 Hmd Ha2 Hcap ((pad & RC) & BB) DJ MI ST HLO HSA HSB K.
  destruct (rec_get _ _ _ _ _ _ _ RC) as (HB & HP & HW).
  pose proof (bbuf_wr _ _ _ _ BB) as (BW & B0 & B1).
  pose proof (nn_rng cap s Hcap) as NR.
  pose proof (zr_word a0) as Ra0. unfold inr64 in Ra0.
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  assert (RM : sb_dec_room cap (nn cap s) = cap - 1 - nn cap s).
  { unfold sb_dec_room. replace (nn cap s + 1 <=? cap) with true by (symmetry; apply Z.leb_le; lia). reflexivity. }
  eapply evt_cut.
  { eapply DEC with (lo := lo) (v := v) (md := md) (p := Z_to_bv 64 B) (cap := Z_to_bv 64 cap)
                    (n := Z_to_bv 64 (nn cap s)) (over := ovf cap s).
    - exact Hv.
    - exact Ha1.
    - exact Hmd.
    - exact Ha2.
    - rewrite HA. exact HB.
    - rewrite HA. eapply wr_at_prefix; [exact HW|lia].
    - rewrite HA. exact HAL.
    - rewrite unsigned_lit by lia. lia.
    - rewrite !unsigned_lit by lia. intros HR. unfold sb_dec_acc, SB_DEC_K. rewrite RM in *.
      pose proof ST as (Hlo0 & _ & _).
      split; [lia|]. split; [lia|]. split; [|split].
      + eapply wr_at_sub; [exact BW|lia|lia|lia].
      + rewrite HA. lia.
      + lia.
    - exact MI.
    - exact ST.
    - unfold SB_DEC_K. lia.
    - unfold SB_DEC_K. rewrite HA. lia. }
  intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
              E & MU & WM & MI' & ST' & HB' & HY).
  subst ms'. rewrite ret_pc_even by (first [exact Hr | exact Hr2]).
  rewrite HA, !unsigned_lit in MU by lia. rewrite HA, !unsigned_lit in HB' by lia.
  rewrite !unsigned_lit in HY by lia.
  unfold sb_dec_acc, SB_DEC_K in *.
  pose proof (sbx_dec _ _ _ _ _ _ _ _ _ RC BB Hcap DJ WM HSA HSB MU HB' HY) as SB'.
  rewrite RM in MU.
  apply K; [exact SB' | | exact WM | exact MI' | exact ST'].
  eapply munch_weaken; [|exact MU]. intros x Hx. cbn [outside] in *. lia.
Qed.

End Calls.
