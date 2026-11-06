(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith Lia Bool List.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.openssl.ct.lib.VCommon Require Import PropExec FastWord FastWordSem.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require Import ExTrie ExBytes.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require Import AxLazy AxLin AxRel AxVal AxBytes AxMem AxMemC AxEntryRel AsanWEbLoad.
Import ListNotations.

Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

Definition is_empty {A : Type} (t : itrie A) : bool := match t with IEmpty => true | _ => false end.

(* [comment removed for export] *)
Definition zz_fits (s : store) (R : region) (ts : terms) (o : w64) (n : Z) : bool :=
  match rg_kind R with
  | KZero | KShadow => is_empty (rg_cells R) &&&
             match lrange s (lsub (wS o, ts) (wS (rg_bo R), rg_ts R)) with
             | Some (lo, hi) => (0 <=? lo) && (hi + n <=? to_Z (rg_n R))
             | None => false
             end
  | _ => false
  end.

Definition xb_is0 (b : xb) : bool := match b with BL x => (x =? 0)%uint63 | _ => false end.

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
Fixpoint find_entry (A : list region) : option PhdrInfo :=
  match A with
  | [] => None
  | R :: A' => match rg_kind R with KEntry ph => Some ph | _ => find_entry A' end
  end.

Definition a_load3 (s : store) (A : list region) (v : xv) (n : nat) : option (list xb) :=
  match a_load2 segs s A v n with
  | Some l => Some l
  | None => match xaddr v with
            | Some (ts, o) => if lexists (fun R => zz_fits s R ts o (Z.of_nat n)) A then Some (repeat (BL 0%uint63) n) else
                match find_entry A with
                | Some ph => match eb_load ph s v n with Some l => if Nat.eqb (length l) n then Some l else None | None => None end
                | None => None
                end
            | None => None
            end
  end.

Definition a_store3 (s : store) (A : list region) (v : xv) (nb : list xb) : option (list region) :=
  match a_store2 segs s A v nb with
  | Some A' => Some A'
  | None => match xaddr v with
            | Some (ts, o) => if forallb xb_is0 nb &&& lexists (fun R => zz_fits s R ts o (Z.of_nat (length nb))) A then Some A else None
            | None => None
            end
  end.

Lemma xaddr_val (ρ : valuation) (v : xv) (a : bv 64) (ts : terms) (o : w64) :
  xv_val ρ v a -> xaddr v = Some (ts, o) -> bv_unsigned a = smod ρ ts o.
Proof.
  intros Hv Ea. destruct v; cbn [xaddr] in Ea; try discriminate; injection Ea as <- <-; cbn [xv_val] in Hv.
  - rewrite Hv. unfold smod. cbn [teval]. rewrite Z.add_0_l. symmetry. apply Z.mod_small. apply wZ_range.
  - exact Hv.
Qed.

(* [comment removed for export] *)
Lemma zz_core (ρ : valuation) (s : store) (R : region) (ts : terms) (o : w64) (n : Z) (a : bv 64) :
  0 < n -> sat ρ s -> region_wf ρ R -> bv_unsigned a = smod ρ ts o ->
  (match lrange s (lsub (wS o, ts) (wS (rg_bo R), rg_ts R)) with
   | Some (lo, hi) => (0 <=? lo) && (hi + n <=? to_Z (rg_n R))
   | None => false
   end) = true ->
  exists off, 0 <= off /\ off + n <= to_Z (rg_n R) /\ bv_unsigned a = rbase ρ R + off.
Proof.
  intros Hn0 Hs Hwf Ha H.
  destruct (lrange s (lsub (wS o, ts) (wS (rg_bo R), rg_ts R))) as [[lo hi]|] eqn:El; [|discriminate].
  apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  pose proof (lrange_sound ρ s _ Hs _ El) as Hr. cbn [fst snd] in Hr. rewrite leval_lsub in Hr. unfold leval in Hr. cbn [fst snd] in Hr.
  set (off := wS o + teval ρ ts - (wS (rg_bo R) + teval ρ (rg_ts R))) in *.
  exists off. split; [lia|]. split; [lia|].
  destruct Hwf as [W1 [W2 _]]. rewrite Ha.
  assert (E1 : smod ρ ts o = (teval ρ ts + wS o) mod two64).
  { unfold smod. rewrite <- (wS_mod o). rewrite Zplus_mod_idemp_r. reflexivity. }
  assert (E2 : rbase ρ R = (teval ρ (rg_ts R) + wS (rg_bo R)) mod two64).
  { unfold rbase, smod. rewrite <- (wS_mod (rg_bo R)). rewrite Zplus_mod_idemp_r. reflexivity. }
  rewrite E1. rewrite E2 in W1 |- *.
  replace (teval ρ ts + wS o) with ((teval ρ (rg_ts R) + wS (rg_bo R)) + off) by (unfold off; ring).
  rewrite Zplus_mod. rewrite (Z.mod_small off) by (unfold two64; lia).
  pose proof (Z.mod_pos_bound (teval ρ (rg_ts R) + wS (rg_bo R)) two64 ltac:(unfold two64; lia)).
  apply Z.mod_small. lia.
Qed.

Lemma zz_fits_addr (ρ : valuation) (s : store) (R : region) (ts : terms) (o : w64) (n : Z) (a : bv 64) :
  0 < n -> sat ρ s -> region_wf ρ R -> zz_fits s R ts o n = true -> bv_unsigned a = smod ρ ts o ->
  (rg_kind R = KZero \/ rg_kind R = KShadow) /\ rg_cells R = IEmpty /\
  exists off, 0 <= off /\ off + n <= to_Z (rg_n R) /\ bv_unsigned a = rbase ρ R + off.
Proof.
  intros Hn0 Hs Hwf H Ha. unfold zz_fits in H.
  assert (Hk : rg_kind R = KZero \/ rg_kind R = KShadow) by (destruct (rg_kind R); try discriminate; tauto).
  assert (H' : is_empty (rg_cells R) && (match lrange s (lsub (wS o, ts) (wS (rg_bo R), rg_ts R)) with
               | Some (lo, hi) => (0 <=? lo) && (hi + n <=? to_Z (rg_n R)) | None => false end) = true)
    by (destruct (rg_kind R); try discriminate; exact H).
  apply andb_prop in H' as [He H']. split; [exact Hk|].
  split; [destruct (rg_cells R); try discriminate; reflexivity|].
  exact (zz_core ρ s R ts o n a Hn0 Hs Hwf Ha H').
Qed.

Lemma rbyte_zz (R : region) (x : int) : (rg_kind R = KZero \/ rg_kind R = KShadow) -> rg_cells R = IEmpty -> rbyte segs R x = BL 0%uint63.
Proof. intros Hk Hc. unfold rbyte, get_cell_opt. rewrite Hc. rewrite iget_empty. unfold default_byte. destruct Hk as [Hk|Hk]; rewrite Hk; reflexivity. Qed.

Lemma zz_region_bytes (ρ : valuation) (m : word -> option byte) (R : region) :
  RRegion segs ρ m R -> (rg_kind R = KZero \/ rg_kind R = KShadow) -> rg_cells R = IEmpty -> region_wf ρ R ->
  forall off, 0 <= off < to_Z (rg_n R) -> rv segs m (wz (rbase ρ R + off)) = Some (Z_to_bv 8 0) /\ wview segs m (wz (rbase ρ R + off)) <> None.
Proof.
  intros HR Hk Hc Hwf off Hoff. destruct Hwf as [_ [H47 _]].
  rewrite RRegion_ne in HR by (unfold is_entry; destruct Hk as [Hk|Hk]; rewrite Hk; reflexivity).
  assert (Hx : to_Z (of_Z off) = off) by (rewrite of_Z_spec; apply Z.mod_small; change wB with (2^63); lia).
  destruct (HR (of_Z off) ltac:(lia)) as [[b [Hb Hab]] Hw]. rewrite Hx in Hb, Hw.
  rewrite (rbyte_zz R _ Hk Hc) in Hab. cbn [xb_z] in Hab. change (to_Z 0%uint63) with 0 in Hab.
  split.
  - rewrite Hb. f_equal. apply bv_eq. rewrite Hab. reflexivity.
  - apply Hw. destruct Hk as [Hk|Hk]; rewrite Hk; reflexivity.
Qed.

Lemma rdn_zz (ρ : valuation) (m : word -> option byte) (R : region) (n : nat) :
  RRegion segs ρ m R -> (rg_kind R = KZero \/ rg_kind R = KShadow) -> rg_cells R = IEmpty -> region_wf ρ R ->
  forall off, 0 <= off -> off + Z.of_nat n <= to_Z (rg_n R) ->
  rdn segs m (wz (rbase ρ R + off)) n = Some (repeat (Z_to_bv 8 0) n).
Proof.
  intros HR Hk Hc Hwf. induction n as [|n IH]; intros off H0 Hn; [reflexivity|].
  cbn [rdn repeat]. destruct (zz_region_bytes ρ m R HR Hk Hc Hwf off ltac:(lia)) as [Hb _].
  unfold rv in Hb. rewrite Hb. rewrite wz_succ. rewrite <- Z.add_assoc. rewrite IH by lia. reflexivity.
Qed.

Lemma find_entry_spec (A : list region) (ph : PhdrInfo) : find_entry A = Some ph -> exists R, In R A /\ rg_kind R = KEntry ph.
Proof.
  induction A as [|R A IH]; cbn [find_entry]; [discriminate|].
  destruct (rg_kind R) eqn:Ek; try (intros H; destruct (IH H) as [R1 [H1 H2]]; exists R1; split; [right; exact H1 | exact H2]).
  intros H. injection H as <-. exists R. split; [left; reflexivity | exact Ek].
Qed.

Lemma a_load3_sound (ρ : valuation) (s : store) (A : list region) (m : word -> option byte) (v : xv) (a : bv 64) (n : nat) (l : list xb) :
  sat ρ s -> RMem segs ρ A m -> xv_val ρ v a -> (1 <= n < 1000)%nat -> a_load3 s A v n = Some l ->
  exists bs, rdn segs m a n = Some bs /\ Forall2 (xb_bv ρ) l bs.
Proof.
  intros Hs HM Hv Hn H. unfold a_load3 in H. destruct (a_load2 segs s A v n) as [l0|] eqn:E.
  - injection H as <-. exact (a_load2_sound segs ρ s A m v a n l0 Hs HM Hv Hn E).
  - destruct (xaddr v) as [[ts o]|] eqn:Ea; [|discriminate].
    rewrite lexists_eq in H. destruct (existsb (fun R => zz_fits s R ts o (Z.of_nat n)) A) eqn:Ez.
    2:{ (* [comment removed for export] *)
      destruct (find_entry A) as [ph|] eqn:Efe; [|discriminate].
      destruct (eb_load ph s v n) as [l1|] eqn:Eeb; [|discriminate].
      destruct (Nat.eqb (length l1) n); [|discriminate]. injection H as <-.
      destruct (find_entry_spec A ph Efe) as [R [HIn Ek]].
      destruct HM as [_ HR]. rewrite Forall_forall in HR. pose proof (HR R HIn) as HRR. unfold RRegion in HRR. rewrite Ek in HRR.
      pose proof HRR as [_ [Hb _]]. rewrite Hb in HRR.
      exact (eb_load_sound segs ph ρ s m _ v a n l1 Hs HRR Hv Eeb). }
    injection H as <-.
    apply existsb_exists in Ez as [R [HIn Hz]].
    destruct HM as [Hok HR]. rewrite Forall_forall in HR. pose proof (HR R HIn) as HRR.
    assert (Hwf : region_wf ρ R).
    { clear -Hok HIn. induction A as [|R0 A' IH]; [destruct HIn|]. destruct Hok as [W [_ Hok']].
      destruct HIn as [<-|HIn]; [exact W | apply IH; assumption]. }
    destruct (zz_fits_addr ρ s R ts o (Z.of_nat n) a ltac:(lia) Hs Hwf Hz (xaddr_val ρ v a ts o Hv Ea)) as [Hk [Hc [off [H0 [H1 Ha]]]]].
    exists (repeat (Z_to_bv 8 0) n). split.
    + replace a with (wz (rbase ρ R + off)) by (apply bv_eq; rewrite u_wz; [lia | destruct Hwf as [W1 _]; unfold two64 in *; pose proof (smod_range ρ (rg_ts R) (rg_bo R)); unfold rbase in *; lia]).
      apply rdn_zz; assumption.
    + clear. induction n as [|n IH]; cbn [repeat]; constructor; [|exact IH]. unfold xb_bv. cbn [xb_z]. reflexivity.
Qed.

Lemma a_store3_sound (ρ : valuation) (s : store) (A A' : list region) (m : word -> option byte) (v : xv) (a : bv 64) (nb : list xb) (bs : list byte) :
  sat ρ s -> RMem segs ρ A m -> xv_val ρ v a -> (1 <= length nb < 1000)%nat -> Forall2 (xb_bv ρ) nb bs ->
  a_store3 s A v nb = Some A' ->
  store_ok segs m a (length nb) = true /\ RMem segs ρ A' (write_to_mem m a bs).
Proof.
  intros Hs HM Hv Hn Hf H. unfold a_store3 in H. destruct (a_store2 segs s A v nb) as [A0|] eqn:E.
  - injection H as <-. exact (a_store2_sound segs ρ s A A0 m v a nb bs Hs HM Hv Hn Hf E).
  - destruct (xaddr v) as [[ts o]|] eqn:Ea; [|discriminate].
    rewrite lexists_eq in H. change (if forallb xb_is0 nb then existsb (fun R => zz_fits s R ts o (Z.of_nat (length nb))) A else false)
      with (forallb xb_is0 nb && existsb (fun R => zz_fits s R ts o (Z.of_nat (length nb))) A) in H.
    destruct (forallb xb_is0 nb && existsb (fun R => zz_fits s R ts o (Z.of_nat (length nb))) A) eqn:Ez; [|discriminate].
    injection H as <-. apply andb_prop in Ez as [Hz0 Ez]. apply existsb_exists in Ez as [R [HIn Hz]].
    pose proof HM as [Hok HR]. rewrite Forall_forall in HR. pose proof (HR R HIn) as HRR.
    assert (Hwf : region_wf ρ R).
    { clear -Hok HIn. induction A as [|R0 A' IH]; [destruct HIn|]. destruct Hok as [W [_ Hok']].
      destruct HIn as [<-|HIn]; [exact W | apply IH; assumption]. }
    destruct (zz_fits_addr ρ s R ts o (Z.of_nat (length nb)) a ltac:(lia) Hs Hwf Hz (xaddr_val ρ v a ts o Hv Ea)) as [Hk [Hc [off [H0 [H1 Ha]]]]].
    pose proof (Forall2_length Hf) as Hlen.
    (* [comment removed for export] *)
    assert (Hbz : forall k b, nth_error bs k = Some b -> b = Z_to_bv 8 0).
    { intros k b Hk2. rewrite forallb_forall in Hz0.
      assert (Hkl : (k < length bs)%nat) by (apply nth_error_Some; rewrite Hk2; discriminate).
      destruct (Forall2_nth_error_ex _ nb bs k BT Hf ltac:(lia)) as [b' [Hb' Hab]].
      rewrite Hk2 in Hb'. injection Hb' as <-.
      assert (Hin : In (nth k nb BT) nb) by (apply nth_In; lia).
      specialize (Hz0 _ Hin). unfold xb_bv in Hab. destruct (nth k nb BT); try discriminate. cbn [xb_is0] in Hz0.
      apply Uint63.eqb_spec in Hz0. subst. cbn [xb_z] in Hab. apply bv_eq. rewrite Hab. reflexivity. }
    assert (Haw : a = wz (rbase ρ R + off)).
    { apply bv_eq. rewrite u_wz; [exact Ha|]. destruct Hwf as [W1 _].
      pose proof (smod_range ρ (rg_ts R) (rg_bo R)). unfold rbase in *. unfold two64 in *. lia. }
    assert (Hrange : forall y : word, rbase ρ R + off <= bv_unsigned y < rbase ρ R + off + Z.of_nat (length bs) ->
              write_to_mem m a bs y = Some (Z_to_bv 8 0)).
    { intros y Hy. rewrite Haw. rewrite (write_to_mem_spec bs m (rbase ρ R + off) y) .
      - destruct ((rbase ρ R + off <=? bv_unsigned y) && (bv_unsigned y <? rbase ρ R + off + Z.of_nat (length bs))) eqn:Ein.
        + destruct (nth_error bs (Z.to_nat (bv_unsigned y - (rbase ρ R + off)))) as [b|] eqn:Eb.
          * rewrite (Hbz _ b Eb). reflexivity.
          * apply nth_error_None in Eb. lia.
        + apply andb_false_iff in Ein as [E1|E1]; [apply Z.leb_gt in E1 | apply Z.ltb_ge in E1]; lia.
      - pose proof (smod_range ρ (rg_ts R) (rg_bo R)). unfold rbase in *. lia.
      - destruct Hwf as [W1 _]. rewrite <- Hlen. unfold two64 in *. lia. }
    assert (Hout : forall y : word, ~ (rbase ρ R + off <= bv_unsigned y < rbase ρ R + off + Z.of_nat (length bs)) ->
              write_to_mem m a bs y = m y).
    { intros y Hy. rewrite Haw. rewrite (write_to_mem_spec bs m (rbase ρ R + off) y).
      - destruct ((rbase ρ R + off <=? bv_unsigned y) && (bv_unsigned y <? rbase ρ R + off + Z.of_nat (length bs))) eqn:Ein; [|reflexivity].
        apply andb_prop in Ein as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. exfalso. apply Hy. lia.
      - pose proof (smod_range ρ (rg_ts R) (rg_bo R)). unfold rbase in *. lia.
      - destruct Hwf as [W1 _]. rewrite <- Hlen. unfold two64 in *. lia. }
    split.
    + (* [comment removed for export] *)
      rewrite Haw. replace (wz (rbase ρ R + off)) with (wz (rbase ρ R + to_Z (of_Z off))) by (rewrite of_Z_spec, Z.mod_small; [reflexivity | destruct Hwf as [_ [H47 _]]; change wB with (2^63); lia]).
      apply store_ok_range with (ρ := ρ) (R := R); [rewrite <- RRegion_ne by (unfold is_entry; destruct Hk as [Hk|Hk]; rewrite Hk; reflexivity); exact HRR | destruct Hk as [Hk|Hk]; rewrite Hk; reflexivity | |destruct Hwf as [_ [H47 _]]; exact H47].
      rewrite of_Z_spec, Z.mod_small by (destruct Hwf as [_ [H47 _]]; change wB with (2^63); lia). lia.
    + split; [exact Hok|]. apply Forall_forall. intros R2 HIn2.
      destruct (is_entry R2) eqn:Ee2.
      { (* [comment removed for export] *)
        assert (Hne : R2 <> R) by (intros ->; unfold is_entry in Ee2; destruct Hk as [Hk|Hk]; rewrite Hk in Ee2; discriminate).
        destruct (In_nth_error A R HIn) as [i Hi]. destruct (In_nth_error A R2 HIn2) as [j Hj].
        assert (Hij : i <> j) by (intros ->; rewrite Hi in Hj; injection Hj as ->; exact (Hne eq_refl)).
        pose proof (regions_ok_disj ρ A i j R R2 Hok Hi Hj Hij) as Hdis.
        assert (Hwf2 : region_wf ρ R2) by exact (regions_ok_nth ρ A j R2 Hok Hj).
        apply (RRegion_mframe segs ρ m _ R2 Hwf2); [|exact (HR R2 HIn2)].
        intros y Hy. apply Hout. pose proof Hwf2 as [W1 _].
        rewrite u_wz by (pose proof (smod_range ρ (rg_ts R2) (rg_bo R2)); unfold rbase in *; unfold two64 in *; lia).
        unfold rdisj in Hdis. rewrite <- Hlen. lia. }
      rewrite (RRegion_ne segs ρ _ R2 Ee2). intros y Hy.
      pose proof (HR R2 HIn2) as HR2. rewrite (RRegion_ne segs ρ _ R2 Ee2) in HR2.
      destruct (HR2 y Hy) as [[b [Hb Hab]] Hw].
      set (z := rbase ρ R2 + to_Z y).
      assert (Hz64 : bv_unsigned (wz z) = z).
      { apply u_wz. pose proof (smod_range ρ (rg_ts R2) (rg_bo R2)). pose proof (to_Z_bounded y). unfold z, rbase in *.
        assert (Hwf2 : region_wf ρ R2).
        { clear -Hok HIn2. induction A as [|R0 A' IH]; [destruct HIn2|]. destruct Hok as [W [_ Hok']].
          destruct HIn2 as [<-|HIn2]; [exact W | apply IH; assumption]. }
        destruct Hwf2 as [W1 _]. unfold rbase in W1. unfold two64 in *. change wB with (2^63) in *. lia. }
      fold z in Hb, Hw. unfold rv in Hb |- *. unfold wview in Hw |- *.
      destruct (Z_lt_le_dec z (rbase ρ R + off)) as [Hlo|Hlo]; [|destruct (Z_lt_le_dec z (rbase ρ R + off + Z.of_nat (length bs))) as [Hhi|Hhi]].
      * rewrite !(Hout (wz z)) by (rewrite Hz64; lia). split; [exists b; split; assumption | exact Hw].
      * (* [comment removed for export] *)
        rewrite !(Hrange (wz z)) by (rewrite Hz64; lia).
        (* [comment removed for export] *)
        destruct (zz_region_bytes ρ m R HRR Hk Hc Hwf (z - rbase ρ R) ltac:(rewrite <- Hlen in *; lia)) as [Hold _].
        replace (rbase ρ R + (z - rbase ρ R)) with z in Hold by ring. unfold rv in Hold.
        split.
        -- exists (Z_to_bv 8 0). split; [reflexivity|].
           destruct (m (wz z)) as [b0|] eqn:Em.
           ++ injection Hb as <-. injection Hold as <-. exact Hab.
           ++ rewrite Hb in Hold. injection Hold as ->. exact Hab.
        -- intros _. discriminate.
      * rewrite !(Hout (wz z)) by (rewrite Hz64; lia). split; [exists b; split; assumption | exact Hw].
Qed.

Lemma a_load3_length (s : store) (A : list region) (v : xv) (n : nat) (l : list xb) : a_load3 s A v n = Some l -> length l = n.
Proof.
  unfold a_load3. destruct (a_load2 segs s A v n) as [l0|] eqn:E.
  - intros H. injection H as <-. exact (a_load2_length segs s A v n l0 E).
  - destruct (xaddr v) as [[ts o]|]; [|discriminate]. destruct (lexists _ A).
    + intros H. injection H as <-. apply repeat_length.
    + destruct (find_entry A) as [ph|]; [|discriminate]. destruct (eb_load ph s v n) as [l1|]; [|discriminate].
      destruct (Nat.eqb (length l1) n) eqn:El; [|discriminate]. intros H. injection H as <-. apply Nat.eqb_eq. exact El.
Qed.


(* [comment removed for export] *)
Definition coef_of (ts : terms) (x : int) : Z := fold_left (fun acc p => if (fst p =? x)%uint63 then snd p else acc) ts 0.

(* [comment removed for export] *)
Fixpoint pivot (tf : terms) (ts : terms) : option (int * Z) :=
  match tf with
  | [] => None
  | (x, a) :: r => if negb (coef_of ts x =? 0) then Some (x, a) else pivot r ts
  end.

Fixpoint rel2 (s0 : store) (s : list fact) (c : Z) (ts : terms) : option ivl :=
  match s with
  | [] => None
  | Fact (cf, tf) lo hi false :: r =>
      let rest := rel2 s0 r c ts in
      match pivot tf ts with
      | Some (x, a) =>
          if a =? 0 then rest else
          let b := coef_of ts x in
          (* [comment removed for export] *)
          let resid := tadd (tscale a ts) (tscale (- b) tf) in
          match tbox s0 resid with
          | Some (bl, bh) =>
              let i := iscale b (lo - cf, hi - cf) in
              let lo' := a * c + fst i + bl in
              let hi' := a * c + snd i + bh in
              let r' := if 0 <? a then Some (fdivc lo' a, zdiv hi' a) else Some (fdivc (- hi') (- a), zdiv (- lo') (- a)) in
              imeet r' rest
          | None => rest
          end
      | None => rest
      end
  | _ :: r => rel2 s0 r c ts
  end.

Definition lrange2 (s : store) (f : lin) : option ivl := imeet (lrange s f) (rel2 s (st_facts s) (fst f) (snd f)).

Lemma rel2_sound (ρ : valuation) (s0 : store) (s : list fact) (c : Z) (ts : terms) :
  sat ρ s0 -> Forall (fact_sat ρ) s -> forall i, rel2 s0 s c ts = Some i -> fst i <= c + teval ρ ts <= snd i.
Proof.
  intros Hs0. induction s as [|[[cf tf] lo hi hl] r IH]; intros Hs i H; [discriminate|].
  inversion Hs as [|? ? Hf Hr]; subst. unfold fact_sat, leval in Hf. cbn [fc_f fc_lo fc_hi fc_hole fst snd] in Hf.
  destruct hl; cbn [rel2] in H; [apply IH; assumption|].
  destruct (pivot tf ts) as [[x a]|] eqn:Ep; [|apply IH; assumption].
  destruct (a =? 0) eqn:Ea0; [apply IH; assumption|]. apply Z.eqb_neq in Ea0.
  destruct (tbox s0 (tadd (tscale a ts) (tscale (- coef_of ts x) tf))) as [[bl bh]|] eqn:Et; [|apply IH; assumption].
  revert H. apply imeet_sound; [|intros j Hj; apply IH; assumption].
  pose proof (tbox_sound ρ s0 _ Hs0 _ Et) as Hb. cbn [fst snd] in Hb.
  rewrite teval_tadd, !teval_tscale in Hb.
  assert (Hi : fst (lo - cf, hi - cf) <= teval ρ tf <= snd (lo - cf, hi - cf)) by (cbn [fst snd]; lia).
  pose proof (iscale_sound (coef_of ts x) _ _ Hi) as Hsc.
  set (b := coef_of ts x) in *. set (isc := iscale b (lo - cf, hi - cf)) in *.
  set (z := c + teval ρ ts).
  assert (Hlo : a * c + fst isc + bl <= a * z) by (unfold z; lia).
  assert (Hhi : a * z <= a * c + snd isc + bh) by (unfold z; lia).
  intros j Hj. destruct (Z.ltb_spec 0 a) as [Ha|Ha]; injection Hj as <-; cbn [fst snd].
  - split; [apply fdivc_le; [exact Ha | lia] | apply zdiv_le_of; [exact Ha | lia]].
  - assert (E : - a * z = - (a * z)) by ring.
    split; [apply fdivc_le; [lia | rewrite E; lia] | apply zdiv_le_of; [lia | rewrite E; lia]].
Qed.

Lemma lrange2_sound (ρ : valuation) (s : store) (f : lin) :
  sat ρ s -> forall i, lrange2 s f = Some i -> fst i <= leval ρ f <= snd i.
Proof.
  intros Hs. unfold lrange2. apply imeet_sound.
  - intros i Hi. exact (lrange_sound ρ s f Hs i Hi).
  - intros i Hi. unfold leval. exact (rel2_sound ρ s (st_facts s) (fst f) (snd f) Hs (proj2 Hs) i Hi).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint rel3 (n : nat) (s0 : store) {struct n} : list fact -> Z -> terms -> option ivl :=
  fix go (s : list fact) (c : Z) (ts : terms) {struct s} : option ivl :=
  match s with
  | [] => None
  | Fact (cf, tf) lo hi false :: r =>
      let rest := go r c ts in
      match pivot tf ts with
      | Some (x, a) =>
          if a =? 0 then rest else
          let b := coef_of ts x in
          let resid := tadd (tscale a ts) (tscale (- b) tf) in
          let rb := match n with O => tbox s0 resid | S n' => imeet (tbox s0 resid) (rel3 n' s0 (st_facts s0) 0 resid) end in
          match rb with
          | Some (bl, bh) =>
              let i := iscale b (lo - cf, hi - cf) in
              let lo' := a * c + fst i + bl in
              let hi' := a * c + snd i + bh in
              let r' := if 0 <? a then Some (fdivc lo' a, zdiv hi' a) else Some (fdivc (- hi') (- a), zdiv (- lo') (- a)) in
              imeet r' rest
          | None => rest
          end
      | None => rest
      end
  | _ :: r => go r c ts
  end.

Lemma rel3_sound (ρ : valuation) (s0 : store) (n : nat) : sat ρ s0 ->
  forall (s : list fact) (c : Z) (ts : terms), Forall (fact_sat ρ) s -> forall i, rel3 n s0 s c ts = Some i -> fst i <= c + teval ρ ts <= snd i.
Proof.
  intros Hs0. induction n as [|n IHn]; intros s; induction s as [|[[cf tf] lo hi hl] r IH]; intros c ts Hs i H; try discriminate.
  all: inversion Hs as [|? ? Hf Hr]; subst; unfold fact_sat, leval in Hf; cbn [fc_f fc_lo fc_hi fc_hole fst snd] in Hf.
  all: destruct hl; cbn [rel3] in H; [apply (IH c ts Hr); assumption|].
  all: destruct (pivot tf ts) as [[x a]|] eqn:Ep; [|apply (IH c ts Hr); assumption].
  all: destruct (a =? 0) eqn:Ea0; [apply (IH c ts Hr); assumption|]; apply Z.eqb_neq in Ea0.
  1: destruct (tbox s0 (tadd (tscale a ts) (tscale (- coef_of ts x) tf))) as [[bl bh]|] eqn:Et; [|apply (IH c ts Hr); assumption].
  2: destruct (imeet (tbox s0 (tadd (tscale a ts) (tscale (- coef_of ts x) tf))) (rel3 n s0 (st_facts s0) 0 (tadd (tscale a ts) (tscale (- coef_of ts x) tf))))
       as [[bl bh]|] eqn:Et; [|apply (IH c ts Hr); assumption].
  all: revert H; apply imeet_sound; [|intros j Hj; apply (IH c ts Hr); assumption].
  1: pose proof (tbox_sound ρ s0 _ Hs0 _ Et) as Hb.
  2: assert (Hb : fst (bl, bh) <= teval ρ (tadd (tscale a ts) (tscale (- coef_of ts x) tf)) <= snd (bl, bh));
     [ revert Et; apply imeet_sound; [intros j Hj; exact (tbox_sound ρ s0 _ Hs0 _ Hj) | intros j Hj; pose proof (IHn (st_facts s0) 0 _ (proj2 Hs0) j Hj); lia ] | ].
  all: cbn [fst snd] in Hb; rewrite teval_tadd, !teval_tscale in Hb.
  all: assert (Hi : fst (lo - cf, hi - cf) <= teval ρ tf <= snd (lo - cf, hi - cf)) by (cbn [fst snd]; lia).
  all: pose proof (iscale_sound (coef_of ts x) _ _ Hi) as Hsc.
  all: set (b := coef_of ts x) in *; set (isc := iscale b (lo - cf, hi - cf)) in *.
  all: set (z := c + teval ρ ts).
  all: assert (Hlo : a * c + fst isc + bl <= a * z) by (unfold z; lia).
  all: assert (Hhi : a * z <= a * c + snd isc + bh) by (unfold z; lia).
  all: intros j Hj; destruct (Z.ltb_spec 0 a) as [Ha|Ha]; injection Hj as <-; cbn [fst snd].
  all: first [ split; [apply fdivc_le; [exact Ha | lia] | apply zdiv_le_of; [exact Ha | lia]]
             | assert (E : - a * z = - (a * z)) by ring;
               split; [apply fdivc_le; [lia | rewrite E; lia] | apply zdiv_le_of; [lia | rewrite E; lia]] ].
Qed.

Definition lrange3 (s : store) (f : lin) : option ivl := imeet (lrange s f) (rel3 2 s (st_facts s) (fst f) (snd f)).

Lemma lrange3_sound (ρ : valuation) (s : store) (f : lin) :
  sat ρ s -> forall i, lrange3 s f = Some i -> fst i <= leval ρ f <= snd i.
Proof.
  intros Hs. unfold lrange3. apply imeet_sound.
  - intros i Hi. exact (lrange_sound ρ s f Hs i Hi).
  - intros i Hi. unfold leval. exact (rel3_sound ρ s 2 Hs (st_facts s) (fst f) (snd f) (proj2 Hs) i Hi).
Qed.

Definition hs_beg : Z := 2201439137792.     (* [comment removed for export] *)
Definition hs_hi : Z := 17594333495296.     (* [comment removed for export] *)

Definition is_shadow (R : region) : bool := match rg_kind R with KShadow => true | _ => false end.

(* [comment removed for export] *)
Definition ls_beg : Z := 2147450880.        (* [comment removed for export] *)
Definition ls_end : Z := 2415882240.        (* [comment removed for export] *)

Lemma entry_not_shadow (R : region) : is_entry R = true -> is_shadow R = false.
Proof. unfold is_entry, is_shadow. destruct (rg_kind R); first [reflexivity | discriminate]. Qed.

Lemma RRegion_sh (ρ : valuation) (m : word -> option byte) (R : region) : is_shadow R = true -> RRegion segs ρ m R -> RRegion0 segs ρ m R.
Proof. intros Hs. rewrite RRegion_ne; [exact (fun X => X)|]. unfold is_shadow, is_entry in *. destruct (rg_kind R); first [reflexivity | discriminate Hs]. Qed.

Definition in_ss (z : Z) : Prop := (ls_beg <= z < ls_end) \/ (hs_beg <= z < hs_hi).

Definition in_rg (ρ : valuation) (R : region) (z : Z) : Prop := rbase ρ R <= z < rbase ρ R + to_Z (rg_n R).

(* [comment removed for export] *)
Definition hs_old (ρ : valuation) (A : list region) (m : word -> option byte) : Prop :=
  (forall R, In R A -> is_shadow R = false -> forall z, in_rg ρ R z -> ~ in_ss z) /\
  (forall z, in_ss z -> (forall R, In R A -> is_shadow R = true -> ~ in_rg ρ R z) ->
     m (wz z) = None \/ m (wz z) = Some (Z_to_bv 8 0)) /\
  ((forall z, ls_beg <= z < ls_end -> m (wz z) <> None) \/ (forall z, ls_beg <= z < ls_end -> m (wz z) = None)) /\
  ((forall z, hs_beg <= z < hs_hi -> m (wz z) <> None) \/ (forall z, hs_beg <= z < hs_hi -> m (wz z) = None)).

(* [comment removed for export] *)
Definition plain_mode (A : list region) : Prop :=
  (exists R, In R A /\ to_Z (rg_n R) = 0) /\ (forall R, In R A -> is_shadow R = false).

Definition hs_ok (ρ : valuation) (A : list region) (m : word -> option byte) : Prop := plain_mode A \/ hs_old ρ A m.

Lemma hs_old_ok (ρ : valuation) (A : list region) (m : word -> option byte) : hs_old ρ A m -> hs_ok ρ A m.
Proof. intros H. right. exact H. Qed.

Lemma plain_ok (ρ : valuation) (A : list region) (m : word -> option byte) : plain_mode A -> hs_ok ρ A m.
Proof. intros H. left. exact H. Qed.

(* [comment removed for export] *)
Lemma hs_old_of_pos (ρ : valuation) (A : list region) (m : word -> option byte) :
  (forall R, In R A -> 0 < to_Z (rg_n R)) -> hs_ok ρ A m -> hs_old ρ A m.
Proof. intros Hpos [[[R [HR Hn]] _]|H]; [specialize (Hpos R HR); lia | exact H]. Qed.

(* [comment removed for export] *)
Lemma hs_old_of_sh (ρ : valuation) (A : list region) (m : word -> option byte) (W : region) :
  In W A -> is_shadow W = true -> hs_ok ρ A m -> hs_old ρ A m.
Proof. intros HW Hs [[_ Hno]|H]; [rewrite (Hno W HW) in Hs; discriminate | exact H]. Qed.

(* [comment removed for export] *)
Definition segs_low (segs : list Segment) : Prop :=
  forall sg, In sg segs -> Z.of_N (seg_base sg) + Z.of_N (seg_size sg) <= ls_beg.

(* [comment removed for export] *)
Definition written_in (ρ : valuation) (A : list region) (a n : Z) : Prop :=
  exists R, In R A /\ rbase ρ R <= a /\ a + n <= rbase ρ R + to_Z (rg_n R).

(* [comment removed for export] *)
Definition off_range (s : store) (d : lin) (n N : Z) : option ivl :=
  (* [comment removed for export] *)
  if rbetween 3 s d N 4611686018427387903 then Some (N, 4611686018427387903)
  else if rbetween 3 s d (-4611686018427387903) (- n) then Some (-4611686018427387903, - n)
  else lrange2 s d.

Lemma off_range_sound (ρ : valuation) (s : store) (d : lin) (n N : Z) :
  sat ρ s -> forall i, off_range s d n N = Some i -> fst i <= leval ρ d <= snd i.
Proof.
  intros Hs i H. unfold off_range in H.
  destruct (rbetween 3 s d N 4611686018427387903) eqn:E2.
  { injection H as <-. exact (rbetween_sound ρ s 3 _ _ _ Hs E2). }
  destruct (rbetween 3 s d (-4611686018427387903) (- n)) eqn:E1.
  { injection H as <-. exact (rbetween_sound ρ s 3 _ _ _ Hs E1). }
  exact (lrange2_sound ρ s d Hs i H).
Qed.

Definition havoc_keys (k0 k1 : Z) : list Z := map (fun i => k0 + Z.of_nat i) (seq 0 (Z.to_nat (k1 - k0 + 1))).

Definition havoc_cells (R : region) (k0 k1 : Z) : region :=
  with_cells R (fold_left (fun t k => iset (rg_d R) t (of_Z k) (CB (repeat BT 8))) (havoc_keys k0 k1) (rg_cells R)).

Definition havoc_one (s : store) (ts : terms) (o : w64) (n : Z) (R : region) : option region :=
  match rg_kind R, rg_cells R with
  | KShadow, IEmpty => Some R
  | KShadow, _ =>
      match off_range s (lsub (wS o, ts) (wS (rg_bo R), rg_ts R)) n (to_Z (rg_n R)) with
      | Some (lo, hi) =>
          if negb ((- 4611686018427387904 <? lo) && (hi <? 4611686018427387904)) then None else
          if (hi + n <=? 0) || (to_Z (rg_n R) <=? lo) then Some R else
          let k0 := Z.max 0 lo / 8 in
          let k1 := Z.min (to_Z (rg_n R) - 1) (hi + n - 1) / 8 in
          if k1 - k0 <? 600 then Some (havoc_cells R k0 k1) else None
      | None => None
      end
  | _, _ => Some R
  end.

Fixpoint havoc_all (s : store) (ts : terms) (o : w64) (n : Z) (A : list region) : option (list region) :=
  match A with
  | [] => Some []
  | R :: A' => match havoc_one s ts o n R, havoc_all s ts o n A' with Some R', Some l => Some (R' :: l) | _, _ => None end
  end.

(* [comment removed for export] *)
Definition tgcd (ts : terms) : Z := fold_right (fun p g => Z.gcd (snd p) g) 0 ts.

Lemma tgcd_div (ρ : valuation) (ts : terms) : (tgcd ts | teval ρ ts).
Proof.
  induction ts as [|[x a] r IH]; cbn [tgcd fold_right teval snd].
  - exists 0. reflexivity.
  - apply Z.divide_add_r.
    + apply Z.divide_mul_l. apply Z.gcd_divide_l.
    + eapply Z.divide_trans; [apply Z.gcd_divide_r | exact IH].
Qed.

Definition gran (f : lin) (r : option ivl) : option ivl :=
  match r with
  | Some (lo, hi) =>
      let g := tgcd (snd f) in
      if g <=? 1 then r else Some (fst f - g * ((fst f - lo) / g), fst f + g * ((hi - fst f) / g))
  | None => None
  end.

Lemma gran_sound (ρ : valuation) (f : lin) (r : option ivl) :
  (forall i, r = Some i -> fst i <= leval ρ f <= snd i) -> forall i, gran f r = Some i -> fst i <= leval ρ f <= snd i.
Proof.
  intros Hr i H. destruct r as [[lo hi]|]; [|discriminate]. cbn [gran] in H.
  specialize (Hr _ eq_refl). cbn [fst snd] in Hr.
  destruct (Z.leb_spec (tgcd (snd f)) 1) as [Hg|Hg]; [injection H as <-; exact Hr|].
  injection H as <-. cbn [fst snd]. destruct (tgcd_div ρ (snd f)) as [q Hq].
  set (g := tgcd (snd f)) in *. unfold leval in *. rewrite Hq in *. clearbody g.
  assert (H1 : (hi - fst f) / g >= q) by (apply Z.le_ge, Z.div_le_lower_bound; lia).
  assert (H2 : (fst f - lo) / g >= - q) by (apply Z.le_ge, Z.div_le_lower_bound; lia).
  split; nia.
Qed.

(* [comment removed for export] *)
Definition in_hs_l (s : store) (ts : terms) (o : w64) (n : Z) : bool :=
  match lrange s (wS o, ts) with
  | Some (lo, hi) => (hs_beg <=? lo) &&& (hi + n <=? hs_hi)
  | None => false
  end.

Lemma in_hs_l_ex (ρ : valuation) (s : store) (ts : terms) (o : w64) (n : Z) :
  sat ρ s -> in_hs_l s ts o n = true ->
  exists lo hi, lo <= leval ρ (wS o, ts) <= hi /\ hs_beg <= lo /\ hi + n <= hs_hi.
Proof.
  intros Hs H. unfold in_hs_l in H. destruct (lrange s (wS o, ts)) as [[lo hi]|] eqn:El; [|discriminate].
  apply land_true in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  exists lo, hi. split; [exact (lrange_sound ρ s _ Hs _ El)|]. split; assumption.
Qed.

(* [comment removed for export] *)
Definition hs_wit (s : store) (A : list region) : bool :=
  lexists (fun R => is_shadow R &&& (0 <? to_Z (rg_n R)) &&& in_hs_l s (rg_ts R) (rg_bo R) 1) A.

Lemma hs_wit_ex (s : store) (A : list region) : hs_wit s A = true ->
  exists R, In R A /\ is_shadow R = true /\ 0 < to_Z (rg_n R) /\ in_hs_l s (rg_ts R) (rg_bo R) 1 = true.
Proof.
  intros H. apply lexists_exists in H as [R [HR Hc]]. apply land_true in Hc as [Hc Hb]. apply land_true in Hc as [Hsh Hpos].
  apply Z.ltb_lt in Hpos. exists R. repeat split; assumption.
Qed.

Lemma hs_old_of_wit (ρ : valuation) (s : store) (A : list region) (m : word -> option byte) :
  hs_wit s A = true -> hs_ok ρ A m -> hs_old ρ A m.
Proof. intros Hw Hhs. destruct (hs_wit_ex s A Hw) as (W & HW & HWs & _). exact (hs_old_of_sh ρ A m W HW HWs Hhs). Qed.

(* [comment removed for export] *)
Definition in_hs (s : store) (ts : terms) (o : w64) (n : Z) : bool :=
  rbetween 3 s (wS o, ts) hs_beg (hs_hi - n).

Lemma in_hs_ex (ρ : valuation) (s : store) (ts : terms) (o : w64) (n : Z) :
  sat ρ s -> in_hs s ts o n = true ->
  exists lo hi, lo <= leval ρ (wS o, ts) <= hi /\ hs_beg <= lo /\ hi + n <= hs_hi.
Proof.
  intros Hs H. pose proof (rbetween_sound ρ s 3 _ _ _ Hs H) as X.
  exists (leval ρ (wS o, ts)), (leval ρ (wS o, ts)). lia.
Qed.

Definition a_store4 (s : store) (A : list region) (v : xv) (nb : list xb) : option (list region) :=
  match a_store3 s A v nb with
  | Some A' => Some A'
  | None =>
      match xaddr v with
      | Some (ts, o) =>
          if forallb xb_is0 nb &&& hs_wit s A &&& in_hs s ts o (Z.of_nat (length nb))
          then havoc_all s ts o (Z.of_nat (length nb)) A else None
      | None => None
      end
  end.

Lemma write_to_mem_some (bs : list byte) : forall (m : word -> option byte) (a y : word),
  m y <> None -> write_to_mem m a bs y <> None.
Proof.
  induction bs as [|b bs IH]; intros m a y H; cbn [write_to_mem]; [exact H|].
  apply IH. destruct (bv_eqb y a); [discriminate | exact H].
Qed.

Lemma same_fields_refl (R : region) : same_fields R R.
Proof. repeat split. Qed.

Lemma Forall2_same_refl (A : list region) : Forall2 same_fields A A.
Proof. induction A as [|R A IH]; constructor; [apply same_fields_refl | exact IH]. Qed.

Lemma rbase_same (ρ : valuation) (R R' : region) : same_fields R R' -> rbase ρ R' = rbase ρ R.
Proof. intros [H1 [H2 _]]. unfold rbase. rewrite H1, H2. reflexivity. Qed.

Lemma region_wf_same (ρ : valuation) (R R' : region) : same_fields R R' -> region_wf ρ R -> region_wf ρ R'.
Proof.
  intros HS [W1 [W2 [W3 [W4 W5]]]]. pose proof (rbase_same ρ R R' HS) as Hb. destruct HS as [F1 [F2 [F3 [F4 F5]]]].
  unfold region_wf. rewrite Hb, F3, F5, F1. repeat split; try assumption. intros a i Hk. rewrite F4 in Hk. exact (W5 a i Hk).
Qed.

Lemma regions_ok_same (ρ : valuation) (A A' : list region) : Forall2 same_fields A A' -> regions_ok ρ A -> regions_ok ρ A'.
Proof.
  intros HF. induction HF as [|R R' A0 A0' HS HF IH]; intros Hok; [exact I|].
  destruct Hok as [Hwf [Hd Hok']]. split; [apply (region_wf_same ρ R R' HS Hwf)|]. split; [|apply IH; exact Hok'].
  clear IH Hok'. induction HF as [|Q Q' B B' HQ HF' IH2]; [constructor|]. inversion Hd as [|? ? Hd1 Hd2]; subst.
  constructor; [|apply IH2; exact Hd2]. unfold rdisj in *. rewrite (rbase_same ρ R R' HS), (rbase_same ρ Q Q' HQ).
  destruct HS as [_ [_ [E1 _]]]. destruct HQ as [_ [_ [E2 _]]]. rewrite E1, E2. exact Hd1.
Qed.

Lemma Forall2_In_l {X Y : Type} (P : X -> Y -> Prop) (l1 : list X) (l2 : list Y) (y : Y) :
  Forall2 P l1 l2 -> In y l2 -> exists x, In x l1 /\ P x y.
Proof.
  intros HF. induction HF as [|x0 y0 l1' l2' Hp HF IH]; intros Hin; [destruct Hin|].
  destruct Hin as [<-|Hin]; [exists x0; split; [left; reflexivity | exact Hp]|].
  destruct (IH Hin) as [x [Hx Hpx]]. exists x. split; [right; exact Hx | exact Hpx].
Qed.

Lemma Forall2_In_r {X Y : Type} (P : X -> Y -> Prop) (l1 : list X) (l2 : list Y) (x : X) :
  Forall2 P l1 l2 -> In x l1 -> exists y, In y l2 /\ P x y.
Proof.
  intros HF. induction HF as [|x0 y0 l1' l2' Hp HF IH]; intros Hin; [destruct Hin|].
  destruct Hin as [<-|Hin]; [exists y0; split; [left; reflexivity | exact Hp]|].
  destruct (IH Hin) as [y [Hy Hpy]]. exists y. split; [right; exact Hy | exact Hpy].
Qed.

Lemma is_shadow_same (R R' : region) : same_fields R R' -> is_shadow R' = is_shadow R.
Proof. intros [_ [_ [_ [E _]]]]. unfold is_shadow. rewrite E. reflexivity. Qed.

(* [comment removed for export] *)
Lemma plain_mode_same (A A' : list region) : Forall2 same_fields A A' -> plain_mode A -> plain_mode A'.
Proof.
  intros HF [[R [HR Hn]] Hno]. split.
  - destruct (Forall2_In_r _ A A' R HF HR) as [R' [HR' HS]]. exists R'. split; [exact HR'|].
    destruct HS as [_ [_ [E3 _]]]. rewrite E3. exact Hn.
  - intros R' HR'. destruct (Forall2_In_l _ A A' R' HF HR') as [R0 [HR0 HS]]. rewrite (is_shadow_same R0 R' HS). exact (Hno R0 HR0).
Qed.


Lemma a_store2_fields (s : store) (A A' : list region) (v : xv) (nb : list xb) :
  a_store2 segs s A v nb = Some A' -> Forall2 same_fields A A'.
Proof.
  unfold a_store2. destruct (a_store segs A v nb) as [A0|] eqn:E.
  - intros H. injection H as <-. exact (a_store_fields segs A A0 v nb E).
  - destruct (a_store segs (map (canon_region s) A) (canon_v s v) nb) as [A''|] eqn:E2; [|discriminate].
    intros H. injection H as <-. pose proof (a_store_fields segs _ _ _ _ E2) as HF.
    clear E E2. revert A'' HF. induction A as [|R A IH]; intros A'' HF; inversion HF as [|? R'' ? B HS HF' ]; subst; cbn [restore_bases]; constructor.
    + destruct HS as [F1 [F2 [F3 [F4 F5]]]]. unfold canon_region in *; cbn [rg_ts rg_bo rg_n rg_kind rg_d] in *.
      unfold same_fields, restore1. cbn [rg_ts rg_bo rg_n rg_kind rg_d]. repeat split; assumption.
    + apply IH. exact HF'.
Qed.

Lemma a_store3_fields (s : store) (A A' : list region) (v : xv) (nb : list xb) :
  a_store3 s A v nb = Some A' -> Forall2 same_fields A A'.
Proof.
  unfold a_store3. destruct (a_store2 segs s A v nb) as [A0|] eqn:E.
  - intros H. injection H as <-. exact (a_store2_fields s A A0 v nb E).
  - destruct (xaddr v) as [[ts o]|]; [|discriminate]. destruct (forallb xb_is0 nb); [|discriminate]. destruct (lexists _ A); [|discriminate].
    intros H. injection H as <-. apply Forall2_same_refl.
Qed.

Lemma havoc_one_fields (s : store) (ts : terms) (o : w64) (n : Z) (R R' : region) :
  havoc_one s ts o n R = Some R' -> same_fields R R'.
Proof.
  unfold havoc_one. intros H.
  destruct (rg_kind R); try (injection H as <-; apply same_fields_refl).
  destruct (rg_cells R); try (injection H as <-; apply same_fields_refl);
    destruct (off_range _ _ _ _) as [[lo hi]|]; try discriminate;
    destruct (negb _); try discriminate; destruct (_ || _); try (injection H as <-; apply same_fields_refl);
    destruct (_ <? 600); try discriminate; injection H as <-; repeat split.
Qed.

Lemma havoc_all_fields (s : store) (ts : terms) (o : w64) (n : Z) : forall (A A' : list region),
  havoc_all s ts o n A = Some A' -> Forall2 same_fields A A'.
Proof.
  induction A as [|R A IH]; intros A' H; cbn [havoc_all] in H.
  - injection H as <-. constructor.
  - destruct (havoc_one s ts o n R) as [R'|] eqn:E1; [|discriminate]. destruct (havoc_all s ts o n A) as [l|] eqn:E2; [|discriminate].
    injection H as <-. constructor; [exact (havoc_one_fields s ts o n R R' E1) | apply IH; reflexivity].
Qed.

Lemma a_store4_fields (s : store) (A A' : list region) (v : xv) (nb : list xb) :
  a_store4 s A v nb = Some A' -> Forall2 same_fields A A'.
Proof.
  unfold a_store4. destruct (a_store3 s A v nb) as [A0|] eqn:E.
  - intros H. injection H as <-. exact (a_store3_fields s A A0 v nb E).
  - destruct (xaddr v) as [[ts o]|]; [|discriminate]. destruct (forallb xb_is0 nb); [|discriminate]. destruct (hs_wit s A); [|discriminate].
    destruct (in_hs s ts o _); [|discriminate]. apply havoc_all_fields.
Qed.

(* [comment removed for export] *)
Lemma iget_fold_havoc (d : nat) (keys : list Z) : forall (t : itrie cell) (k : int),
  Forall (fun z => 0 <= z < 2 ^ Z.of_nat d) keys -> to_Z k < 2 ^ Z.of_nat d -> (d <= 44)%nat ->
  iget d (fold_left (fun t0 z => iset d t0 (of_Z z) (CB (repeat BT 8))) keys t) k =
  if existsb (fun z => z =? to_Z k) keys then Some (CB (repeat BT 8)) else iget d t k.
Proof.
  induction keys as [|z keys IH]; intros t k Hks Hk Hd; cbn [fold_left existsb]; [reflexivity|].
  inversion Hks as [|? ? Hz Hks']; subst. rewrite IH by assumption.
  destruct (existsb (fun z0 => z0 =? to_Z k) keys); [rewrite orb_true_r; reflexivity|]. rewrite orb_false_r.
  rewrite iget_iset. pose proof (to_Z_bounded k). change wB with (2 ^ 63) in *.
  assert (Hp : 2 ^ Z.of_nat d <= 2 ^ 44) by (apply Z.pow_le_mono_r; lia).
  rewrite of_Z_spec. change wB with (2 ^ 63). rewrite (Z.mod_small z (2 ^ 63)) by lia.
  rewrite (Z.mod_small z) by lia. rewrite (Z.mod_small (to_Z k)) by lia. reflexivity.
Qed.

Lemma havoc_keys_in (k0 k1 z : Z) : 0 <= k0 -> existsb (fun y => y =? z) (havoc_keys k0 k1) = (k0 <=? z) && (z <=? k1).
Proof.
  intros Hk0. unfold havoc_keys.
  destruct ((k0 <=? z) && (z <=? k1)) eqn:E.
  - apply existsb_exists. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
    exists z. split; [|apply Z.eqb_refl]. apply in_map_iff. exists (Z.to_nat (z - k0)). split; [lia|].
    apply in_seq. lia.
  - apply Bool.not_true_iff_false. intros Hex. apply existsb_exists in Hex as [y [Hy Hyz]]. apply Z.eqb_eq in Hyz. subst y.
    apply in_map_iff in Hy as [i [Hi Hin]]. apply in_seq in Hin. apply andb_false_iff in E as [E|E]; [apply Z.leb_gt in E | apply Z.leb_gt in E]; lia.
Qed.

Lemma rbyte_havoc (R : region) (k0 k1 : Z) (x : int) :
  0 <= k0 -> k1 < 2 ^ Z.of_nat (rg_d R) -> (rg_d R <= 44)%nat -> to_Z (rg_n R) <= 8 * 2 ^ Z.of_nat (rg_d R) -> to_Z x < to_Z (rg_n R) ->
  rbyte segs (havoc_cells R k0 k1) x = if (k0 <=? to_Z x / 8) && (to_Z x / 8 <=? k1) then BT else rbyte segs R x.
Proof.
  intros Hk0 Hk1 Hd Hn Hx. unfold rbyte, get_cell_opt, havoc_cells, with_cells. cbn [rg_d rg_cells].
  pose proof (key_small R x Hn Hx) as Hks.
  rewrite iget_fold_havoc by (try assumption; apply Forall_forall; intros z Hz; unfold havoc_keys in Hz;
                                apply in_map_iff in Hz as [i [<- Hi]]; apply in_seq in Hi; lia).
  rewrite phi_lsr3 in *. rewrite havoc_keys_in by exact Hk0.
  destruct ((k0 <=? to_Z x / 8) && (to_Z x / 8 <=? k1)); [|reflexivity].
  cbn [cbyte]. pose proof (Z.mod_pos_bound (to_Z x) 8 ltac:(lia)).
  unfold i2n. repeat match goal with |- context [if ?c then _ else _] => destruct c end; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma meet_off (ρ : valuation) (R : region) (f d lo hi n y : Z) :
  region_wf ρ R -> 0 <= f -> f + n <= two64 -> 0 <= n <= 1152921504606846976 ->
  d = f - leval ρ (wS (rg_bo R), rg_ts R) -> lo <= d <= hi -> - 4611686018427387904 < lo -> hi < 4611686018427387904 ->
  f <= y < f + n -> rbase ρ R <= y < rbase ρ R + to_Z (rg_n R) -> lo <= y - rbase ρ R < hi + n.
Proof.
  intros Hwf Hf0 Hfn Hn Hd Hlh Hlo Hhi Hy Hr.
  destruct Hwf as [W1 [W2 _]].
  assert (Hrb : rbase ρ R = (wS (rg_bo R) + teval ρ (rg_ts R)) mod two64).
  { unfold rbase, smod. rewrite <- (wS_mod (rg_bo R)). rewrite Zplus_mod_idemp_r. f_equal. ring. }
  unfold leval in Hd. cbn [fst snd] in Hd.
  set (g := wS (rg_bo R) + teval ρ (rg_ts R)) in *.
  pose proof (Z.div_mod g two64 ltac:(unfold two64; lia)) as Hdm.
  assert (E : y - rbase ρ R - ((y - f) + d) = two64 * (g / two64)) by (rewrite Hrb, Hd; lia).
  pose proof (to_Z_bounded (rg_n R)) as Hnb. change wB with (2 ^ 63) in Hnb.
  assert (Hk : g / two64 = 0).
  { assert (- two64 < two64 * (g / two64) < two64) by (unfold two64 in *; lia).
    unfold two64 in *. nia. }
  rewrite Hk in E. lia.
Qed.

Lemma store_ok_mapped (m : word -> option byte) : forall (n : nat) (a : Z),
  0 <= a -> a + Z.of_nat n <= two64 ->
  (forall j, a <= j < a + Z.of_nat n -> m (wz j) <> None) -> store_ok segs m (wz a) n = true.
Proof.
  induction n as [|n IH]; intros a Ha Hn H; [reflexivity|]. cbn [store_ok].
  unfold wview. destruct (m (wz a)) as [b|] eqn:E.
  - rewrite wz_succ. apply IH; [lia | lia | intros j Hj; apply H; lia].
  - exfalso. apply (H a); [lia | exact E].
Qed.

(* [comment removed for export] *)
Lemma havoc_one_sound (ρ : valuation) (s : store) (ts : terms) (o : w64) (n : Z) (R R' : region) (m m' : word -> option byte) (f : Z) :
  sat ρ s -> region_wf ρ R -> RRegion segs ρ m R ->
  (is_shadow R = false -> forall z, in_rg ρ R z -> ~ in_ss z) ->
  f = leval ρ (wS o, ts) -> hs_beg <= f -> f + n <= hs_hi -> 0 <= n <= 1152921504606846976 ->
  (forall y : word, f <= bv_unsigned y < f + n -> m' y = Some (Z_to_bv 8 0)) ->
  (forall y : word, ~ (f <= bv_unsigned y < f + n) -> m' y = m y) ->
  havoc_one s ts o n R = Some R' -> RRegion segs ρ m' R'.
Proof.
  intros Hs Hwf HRR Hdis Hf Hf1 Hf2 Hn Hin Hout H.
  pose proof Hwf as [W1 [W2 [W3 [W4 W5]]]].
  destruct (is_entry R) eqn:Ee.
  { (* [comment removed for export] *)
    assert (Ek : exists ph, rg_kind R = KEntry ph) by (unfold is_entry in Ee; destruct (rg_kind R); try discriminate; eexists; reflexivity).
    destruct Ek as [ph Ek]. unfold havoc_one in H. rewrite Ek in H. injection H as <-.
    apply (RRegion_mframe segs ρ m m' R Hwf); [|exact HRR].
    intros y Hy. apply Hout. rewrite u_wz by (pose proof (smod_range ρ (rg_ts R) (rg_bo R)); unfold rbase in *; unfold two64 in *; lia).
    intros Hc. apply (Hdis ltac:(unfold is_shadow; rewrite Ek; reflexivity) y); [unfold in_rg; lia | right; unfold hs_beg, hs_hi in *; lia]. }
  rewrite (RRegion_ne segs ρ m R Ee) in HRR.
  assert (Hy64 : forall x : int, to_Z x < to_Z (rg_n R) -> bv_unsigned (wz (rbase ρ R + to_Z x)) = rbase ρ R + to_Z x).
  { intros x Hx. apply u_wz. pose proof (to_Z_bounded x). change wB with (2 ^ 63) in *.
    pose proof (smod_range ρ (rg_ts R) (rg_bo R)). unfold rbase in *. unfold two64 in *. lia. }
  (* [comment removed for export] *)
  assert (Hkeep : (forall x : int, to_Z x < to_Z (rg_n R) -> ~ (f <= rbase ρ R + to_Z x < f + n)) -> RRegion segs ρ m' R).
  { intros Hno. rewrite (RRegion_ne segs ρ m' R Ee). intros x Hx. destruct (HRR x Hx) as [[b [Hb Hab]] Hw].
    assert (Eq : m' (wz (rbase ρ R + to_Z x)) = m (wz (rbase ρ R + to_Z x))) by (apply Hout; rewrite Hy64 by exact Hx; apply Hno; exact Hx).
    unfold rv, wview in *. rewrite Eq. split; [exists b; split; assumption | exact Hw]. }
  unfold havoc_one in H.
  destruct (rg_kind R) eqn:Ek;
    [injection H as <-; apply Hkeep; intros x Hx Hc; apply (Hdis ltac:(unfold is_shadow; rewrite Ek; reflexivity) (rbase ρ R + to_Z x)); [unfold in_rg; pose proof (to_Z_bounded x); lia | right; lia]
    | | injection H as <-; apply Hkeep; intros x Hx Hc; apply (Hdis ltac:(unfold is_shadow; rewrite Ek; reflexivity) (rbase ρ R + to_Z x)); [unfold in_rg; pose proof (to_Z_bounded x); lia | right; lia]
    | injection H as <-; apply Hkeep; intros x Hx Hc; apply (Hdis ltac:(unfold is_shadow; rewrite Ek; reflexivity) (rbase ρ R + to_Z x)); [unfold in_rg; pose proof (to_Z_bounded x); lia | right; lia]
    | exfalso; unfold is_entry in Ee; rewrite Ek in Ee; discriminate].
  (* [comment removed for export] *)
  assert (Hwritten : forall x : int, to_Z x < to_Z (rg_n R) -> f <= rbase ρ R + to_Z x < f + n ->
            m' (wz (rbase ρ R + to_Z x)) = Some (Z_to_bv 8 0)).
  { intros x Hx Hc. apply Hin. rewrite Hy64 by exact Hx. exact Hc. }
  assert (Hunw : forall x : int, to_Z x < to_Z (rg_n R) -> ~ (f <= rbase ρ R + to_Z x < f + n) ->
            m' (wz (rbase ρ R + to_Z x)) = m (wz (rbase ρ R + to_Z x))).
  { intros x Hx Hc. apply Hout. rewrite Hy64 by exact Hx. exact Hc. }
  (* [comment removed for export] *)
  assert (Hbyte : forall R0 : region, rg_n R0 = rg_n R -> rbase ρ R0 = rbase ρ R -> rk_writable (rg_kind R0) = true ->
            (forall x : int, to_Z x < to_Z (rg_n R) -> f <= rbase ρ R + to_Z x < f + n -> xb_z ρ (rbyte segs R0 x) 0) ->
            (forall x : int, to_Z x < to_Z (rg_n R) -> ~ (f <= rbase ρ R + to_Z x < f + n) -> forall z, xb_z ρ (rbyte segs R x) z -> xb_z ρ (rbyte segs R0 x) z) ->
            RRegion segs ρ m' R0).
  { intros R0 En Eb Ew Hw0 Hk0.
    rewrite RRegion_ne by (unfold is_entry; destruct (rg_kind R0); first [reflexivity | discriminate Ew]).
    intros x Hx. rewrite En in Hx. rewrite Eb.
    destruct (Z_lt_le_dec (rbase ρ R + to_Z x) f) as [H1|H1]; [|destruct (Z_lt_le_dec (rbase ρ R + to_Z x) (f + n)) as [H2|H2]].
    - assert (Hc : ~ (f <= rbase ρ R + to_Z x < f + n)) by lia.
      destruct (HRR x Hx) as [[b [Hb Hab]] Hw]. unfold rv, wview in *. rewrite (Hunw x Hx Hc).
      split; [exists b; split; [exact Hb | exact (Hk0 x Hx Hc _ Hab)] | intros _; apply Hw; rewrite Ek; reflexivity].
    - assert (Hc : f <= rbase ρ R + to_Z x < f + n) by lia.
      unfold rv, wview. rewrite (Hwritten x Hx Hc). split; [exists (Z_to_bv 8 0); split; [reflexivity | exact (Hw0 x Hx Hc)] | intros _; discriminate].
    - assert (Hc : ~ (f <= rbase ρ R + to_Z x < f + n)) by lia.
      destruct (HRR x Hx) as [[b [Hb Hab]] Hw]. unfold rv, wview in *. rewrite (Hunw x Hx Hc).
      split; [exists b; split; [exact Hb | exact (Hk0 x Hx Hc _ Hab)] | intros _; apply Hw; rewrite Ek; reflexivity]. }
  destruct (rg_cells R) eqn:Ec.
  - (* [comment removed for export] *)
    injection H as <-. apply Hbyte; try reflexivity; [rewrite Ek; reflexivity | | intros x _ _ z Hz; exact Hz].
    intros x _ _. rewrite rbyte_zz by first [right; exact Ek | exact Ec]. cbn [xb_z]. reflexivity.
  - destruct (off_range s (lsub (wS o, ts) (wS (rg_bo R), rg_ts R)) n (to_Z (rg_n R))) as [[lo hi]|] eqn:El; [|discriminate].
    destruct (negb ((- 4611686018427387904 <? lo) && (hi <? 4611686018427387904))) eqn:Eb; [discriminate|].
    apply negb_false_iff in Eb. apply andb_prop in Eb as [Eb1 Eb2]. apply Z.ltb_lt in Eb1. apply Z.ltb_lt in Eb2.
    pose proof (off_range_sound ρ s _ _ _ Hs _ El) as Hd. cbn [fst snd] in Hd. rewrite leval_lsub in Hd.
    assert (Hmeet : forall x : int, to_Z x < to_Z (rg_n R) -> f <= rbase ρ R + to_Z x < f + n -> lo <= to_Z x < hi + n).
    { intros x Hx Hc. pose proof (to_Z_bounded x). change wB with (2^63) in *.
      pose proof (meet_off ρ R f (f - leval ρ (wS (rg_bo R), rg_ts R)) lo hi n (rbase ρ R + to_Z x) Hwf ltac:(unfold hs_beg in *; lia)
                    ltac:(unfold hs_hi, two64 in *; lia) Hn eq_refl ltac:(rewrite Hf; lia) Eb1 Eb2 Hc ltac:(lia)) as Hm. lia. }
    destruct ((hi + n <=? 0) || (to_Z (rg_n R) <=? lo)) eqn:Eno.
    + injection H as <-. apply Hkeep. intros x Hx Hc. pose proof (Hmeet x Hx Hc). pose proof (to_Z_bounded x).
      apply orb_prop in Eno as [E|E]; apply Z.leb_le in E; lia.
    + destruct (_ <? 600); [|discriminate]. injection H as <-.
      set (k0 := Z.max 0 lo / 8). set (k1 := Z.min (to_Z (rg_n R) - 1) (hi + n - 1) / 8).
      assert (Hk0 : 0 <= k0) by (apply Z.div_pos; lia).
      assert (Hk1 : k1 < 2 ^ Z.of_nat (rg_d R)) by (unfold k1; apply Z.div_lt_upper_bound; lia).
      apply Hbyte.
      * reflexivity.
      * reflexivity.
      * unfold havoc_cells, with_cells. cbn [rg_kind]. rewrite Ek. reflexivity.
      * intros x Hx Hc. rewrite rbyte_havoc by assumption. pose proof (Hmeet x Hx Hc) as Hm. pose proof (to_Z_bounded x).
        replace ((k0 <=? to_Z x / 8) && (to_Z x / 8 <=? k1)) with true; [exact I|].
        symmetry. apply andb_true_iff. split; apply Z.leb_le; unfold k0, k1; apply Z.div_le_mono; lia.
      * intros x Hx Hc z Hz. rewrite rbyte_havoc by assumption. destruct (_ && _); [exact I | exact Hz].
  - destruct (off_range s (lsub (wS o, ts) (wS (rg_bo R), rg_ts R)) n (to_Z (rg_n R))) as [[lo hi]|] eqn:El; [|discriminate].
    destruct (negb ((- 4611686018427387904 <? lo) && (hi <? 4611686018427387904))) eqn:Eb; [discriminate|].
    apply negb_false_iff in Eb. apply andb_prop in Eb as [Eb1 Eb2]. apply Z.ltb_lt in Eb1. apply Z.ltb_lt in Eb2.
    pose proof (off_range_sound ρ s _ _ _ Hs _ El) as Hd. cbn [fst snd] in Hd. rewrite leval_lsub in Hd.
    assert (Hmeet : forall x : int, to_Z x < to_Z (rg_n R) -> f <= rbase ρ R + to_Z x < f + n -> lo <= to_Z x < hi + n).
    { intros x Hx Hc. pose proof (to_Z_bounded x). change wB with (2^63) in *.
      pose proof (meet_off ρ R f (f - leval ρ (wS (rg_bo R), rg_ts R)) lo hi n (rbase ρ R + to_Z x) Hwf ltac:(unfold hs_beg in *; lia)
                    ltac:(unfold hs_hi, two64 in *; lia) Hn eq_refl ltac:(rewrite Hf; lia) Eb1 Eb2 Hc ltac:(lia)) as Hm. lia. }
    destruct ((hi + n <=? 0) || (to_Z (rg_n R) <=? lo)) eqn:Eno.
    + injection H as <-. apply Hkeep. intros x Hx Hc. pose proof (Hmeet x Hx Hc). pose proof (to_Z_bounded x).
      apply orb_prop in Eno as [E|E]; apply Z.leb_le in E; lia.
    + destruct (_ <? 600); [|discriminate]. injection H as <-.
      set (k0 := Z.max 0 lo / 8). set (k1 := Z.min (to_Z (rg_n R) - 1) (hi + n - 1) / 8).
      assert (Hk0 : 0 <= k0) by (apply Z.div_pos; lia).
      assert (Hk1 : k1 < 2 ^ Z.of_nat (rg_d R)) by (unfold k1; apply Z.div_lt_upper_bound; lia).
      apply Hbyte.
      * reflexivity.
      * reflexivity.
      * unfold havoc_cells, with_cells. cbn [rg_kind]. rewrite Ek. reflexivity.
      * intros x Hx Hc. rewrite rbyte_havoc by assumption. pose proof (Hmeet x Hx Hc) as Hm. pose proof (to_Z_bounded x).
        replace ((k0 <=? to_Z x / 8) && (to_Z x / 8 <=? k1)) with true; [exact I|].
        symmetry. apply andb_true_iff. split; apply Z.leb_le; unfold k0, k1; apply Z.div_le_mono; lia.
      * intros x Hx Hc z Hz. rewrite rbyte_havoc by assumption. destruct (_ && _); [exact I | exact Hz].
Qed.

Lemma havoc_all_sound (ρ : valuation) (s : store) (ts : terms) (o : w64) (n : Z) (m m' : word -> option byte) (f : Z) :
  sat ρ s -> f = leval ρ (wS o, ts) -> hs_beg <= f -> f + n <= hs_hi -> 0 <= n <= 1152921504606846976 ->
  (forall y : word, f <= bv_unsigned y < f + n -> m' y = Some (Z_to_bv 8 0)) ->
  (forall y : word, ~ (f <= bv_unsigned y < f + n) -> m' y = m y) ->
  forall A A', havoc_all s ts o n A = Some A' -> regions_ok ρ A -> Forall (RRegion segs ρ m) A ->
  (forall R, In R A -> is_shadow R = false -> forall z, in_rg ρ R z -> ~ in_ss z) ->
  Forall (RRegion segs ρ m') A'.
Proof.
  intros Hs Hf Hf1 Hf2 Hn Hin Hout. induction A as [|R A IH]; intros A' H Hok HR Hdis; cbn [havoc_all] in H.
  - injection H as <-. constructor.
  - destruct (havoc_one s ts o n R) as [R'|] eqn:E1; [|discriminate]. destruct (havoc_all s ts o n A) as [l|] eqn:E2; [|discriminate].
    injection H as <-. destruct Hok as [Hwf [_ Hok']]. apply Forall_cons_iff in HR as [HR1 HR2].
    constructor.
    + apply (havoc_one_sound ρ s ts o n R R' m m' f Hs Hwf HR1); try assumption. intros Hns. apply Hdis; [left; reflexivity | exact Hns].
    + apply IH; [reflexivity | exact Hok' | exact HR2 |]. intros R0 HIn Hns. apply Hdis; [right; exact HIn | exact Hns].
Qed.

Lemma In_nth_error' {X : Type} (l : list X) (i : nat) (x : X) : nth_error l i = Some x -> In x l.
Proof. apply nth_error_In. Qed.

Lemma a_store_in (ρ : valuation) (A A' : list region) (v : xv) (a : bv 64) (nb : list xb) :
  regions_ok ρ A -> xv_val ρ v a -> (1 <= length nb < 1000)%nat -> a_store segs A v nb = Some A' ->
  written_in ρ A (bv_unsigned a) (Z.of_nat (length nb)).
Proof.
  intros Hok Hv Hn H. unfold a_store in H.
  destruct (xaddr v) as [[ts o]|] eqn:Ea; [|discriminate].
  destruct (find_reg A ts o (of_Z (Z.of_nat (length nb))) 0) as [[[i R] x]|] eqn:Ef; [|discriminate].
  destruct (find_reg_spec A ts o _ 0 i R x Ef) as [_ [Hi Hr]]. rewrite Nat.sub_0_r in Hi.
  pose proof (regions_ok_nth ρ A i R Hok Hi) as Hwf.
  destruct (roff_addr ρ R ts o (of_Z (Z.of_nat (length nb))) x a ltac:(rewrite phi_of_nat_small by lia; lia) Hwf
              (xaddr_val ρ v a ts o Hv Ea) Hr) as [Eaddr Hfit].
  rewrite phi_of_nat_small in Hfit by lia. pose proof (to_Z_bounded x).
  exists R. split; [exact (In_nth_error' A i R Hi)|]. lia.
Qed.

Lemma a_store2_in (ρ : valuation) (s : store) (A A' : list region) (v : xv) (a : bv 64) (nb : list xb) :
  sat ρ s -> regions_ok ρ A -> xv_val ρ v a -> (1 <= length nb < 1000)%nat -> a_store2 segs s A v nb = Some A' ->
  written_in ρ A (bv_unsigned a) (Z.of_nat (length nb)).
Proof.
  intros Hs Hok Hv Hn H. unfold a_store2 in H. destruct (a_store segs A v nb) as [A0|] eqn:E.
  - exact (a_store_in ρ A A0 v a nb Hok Hv Hn E).
  - destruct (a_store segs (map (canon_region s) A) (canon_v s v) nb) as [A''|] eqn:E2; [|discriminate].
    destruct (a_store_in ρ _ _ _ a nb (regions_ok_canon ρ s A Hs Hok) (canon_v_sound ρ s v a Hs Hv) Hn E2) as [R' [HIn [H1 H2]]].
    apply in_map_iff in HIn as [R [<- HR]]. rewrite (rbase_canon ρ s R Hs) in H1, H2. exists R. split; [exact HR|].
    unfold canon_region in H2; cbn [rg_n] in H2. lia.
Qed.

Lemma a_store3_in (ρ : valuation) (s : store) (A A' : list region) (v : xv) (a : bv 64) (nb : list xb) :
  sat ρ s -> regions_ok ρ A -> xv_val ρ v a -> (1 <= length nb < 1000)%nat -> a_store3 s A v nb = Some A' ->
  written_in ρ A (bv_unsigned a) (Z.of_nat (length nb)).
Proof.
  intros Hs Hok Hv Hn H. unfold a_store3 in H. destruct (a_store2 segs s A v nb) as [A0|] eqn:E.
  - exact (a_store2_in ρ s A A0 v a nb Hs Hok Hv Hn E).
  - destruct (xaddr v) as [[ts o]|] eqn:Ea; [|discriminate].
    rewrite lexists_eq in H. change (if forallb xb_is0 nb then existsb (fun R => zz_fits s R ts o (Z.of_nat (length nb))) A else false)
      with (forallb xb_is0 nb && existsb (fun R => zz_fits s R ts o (Z.of_nat (length nb))) A) in H.
    destruct (forallb xb_is0 nb && existsb (fun R => zz_fits s R ts o (Z.of_nat (length nb))) A) eqn:Ez; [|discriminate].
    apply andb_prop in Ez as [_ Ez]. apply existsb_exists in Ez as [R [HIn Hz]].
    assert (Hwf : region_wf ρ R).
    { clear -Hok HIn. induction A as [|R0 A' IH]; [destruct HIn|]. destruct Hok as [W [_ Hok']].
      destruct HIn as [<-|HIn]; [exact W | apply IH; assumption]. }
    destruct (zz_fits_addr ρ s R ts o (Z.of_nat (length nb)) a ltac:(lia) Hs Hwf Hz (xaddr_val ρ v a ts o Hv Ea)) as [_ [_ [off [H0 [H1 Ha]]]]].
    exists R. split; [exact HIn | lia].
Qed.

Lemma find_segment_at' (l : list Segment) (z : Z) (sg : Segment) :
  find_segment l z 1 = Some sg -> In sg l /\ Z.of_N (seg_base sg) <= z < Z.of_N (seg_base sg) + Z.of_N (seg_size sg).
Proof.
  induction l as [|s0 r IH]; cbn [find_segment]; [discriminate|].
  destruct (Z.leb (Z.of_N (seg_base s0)) z && Z.leb (z + 1) (Z.of_N (seg_base s0) + Z.of_N (seg_size s0))) eqn:E.
  - intros H. injection H as <-. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
    split; [left; reflexivity | lia].
  - intros H. destruct (IH H) as [H1 H2]. split; [right; exact H1 | exact H2].
Qed.

Lemma wview_mapped (m : word -> option byte) (z : Z) :
  segs_low segs -> in_ss z -> 0 <= z < two64 -> wview segs m (wz z) <> None -> m (wz z) <> None.
Proof.
  intros Hlow Hss Hz Hw. unfold wview in Hw. destruct (m (wz z)) as [b|] eqn:E; [discriminate|].
  destruct (find_segment segs (bv_unsigned (wz z)) 1) as [sg|] eqn:Ef; [|exfalso; apply Hw; reflexivity].
  exfalso. rewrite u_wz in Ef by (unfold two64 in *; lia).
  destruct (find_segment_at' segs z sg Ef) as [HIn Hr]. pose proof (Hlow sg HIn).
  unfold in_ss, ls_beg, ls_end, hs_beg, hs_hi in *. lia.
Qed.

(* [comment removed for export] *)
Lemma store_ok_wview (m : word -> option byte) : forall (n : nat) (a : Z),
  0 <= a -> a + Z.of_nat n <= two64 -> store_ok segs m (wz a) n = true ->
  forall z, a <= z < a + Z.of_nat n -> wview segs m (wz z) <> None.
Proof.
  induction n as [|n IH]; intros a Ha Hn H z Hz; [lia|]. cbn [store_ok] in H.
  destruct (wview segs m (wz a)) as [b|] eqn:E; [|discriminate]. rewrite wz_succ in H.
  destruct (Z.eq_dec z a) as [->|Hne]; [rewrite E; discriminate|]. apply (IH (a + 1)); [lia | lia | exact H | lia].
Qed.

(* [comment removed for export] *)
Lemma hs_ok_write (ρ : valuation) (A A' : list region) (m : word -> option byte) (a : bv 64) (bs : list byte) :
  segs_low segs -> hs_ok ρ A m -> Forall2 same_fields A A' ->
  written_in ρ A (bv_unsigned a) (Z.of_nat (length bs)) -> bv_unsigned a + Z.of_nat (length bs) <= two64 ->
  store_ok segs m a (length bs) = true ->
  hs_ok ρ A' (write_to_mem m a bs).
Proof.
  intros Hlow [Hpl|[P1 [P2 [P3 P4]]]] HF [R [HRin [Hw1 Hw2]]] Ha64 Hok; [left; exact (plain_mode_same A A' HF Hpl) | right].
  pose proof (bvu_range a) as Har.
  assert (Hwm : forall y : word, write_to_mem m a bs y =
            if (bv_unsigned a <=? bv_unsigned y) && (bv_unsigned y <? bv_unsigned a + Z.of_nat (length bs))
            then nth_error bs (Z.to_nat (bv_unsigned y - bv_unsigned a)) else m y).
  { intros y. replace a with (wz (bv_unsigned a)) at 1 by (apply bv_eq; rewrite u_wz; [reflexivity | unfold two64 in *; lia]).
    apply write_to_mem_spec; unfold two64 in *; lia. }
  assert (Hmapped : forall z, in_ss z -> bv_unsigned a <= z < bv_unsigned a + Z.of_nat (length bs) -> m (wz z) <> None).
  { intros z Hss Hz. apply wview_mapped; [exact Hlow | exact Hss | unfold two64 in *; lia|].
    replace a with (wz (bv_unsigned a)) in Hok by (apply bv_eq; rewrite u_wz; [reflexivity | unfold two64 in *; lia]).
    apply (store_ok_wview m (length bs) (bv_unsigned a)); [lia | exact Ha64 | exact Hok | exact Hz]. }
  assert (Hsome : forall z, 0 <= z < two64 -> m (wz z) <> None -> write_to_mem m a bs (wz z) <> None).
  { intros z _ Hz. apply write_to_mem_some. exact Hz. }
  assert (Hkeep : forall z, 0 <= z < two64 -> ~ (bv_unsigned a <= z < bv_unsigned a + Z.of_nat (length bs)) -> write_to_mem m a bs (wz z) = m (wz z)).
  { intros z Hz Hn. rewrite Hwm. rewrite u_wz by (unfold two64 in *; lia).
    replace ((bv_unsigned a <=? z) && (z <? bv_unsigned a + Z.of_nat (length bs))) with false; [reflexivity|].
    symmetry. apply Bool.not_true_iff_false. intros Hc. apply andb_prop in Hc as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. lia. }
  assert (Hss64 : forall z, in_ss z -> 0 <= z < two64) by (intros z Hz; unfold in_ss, ls_beg, ls_end, hs_beg, hs_hi, two64 in *; lia).
  (* [comment removed for export] *)
  assert (Hwss : forall z, in_ss z -> bv_unsigned a <= z < bv_unsigned a + Z.of_nat (length bs) -> is_shadow R = true).
  { intros z Hss Hz. destruct (is_shadow R) eqn:Es; [reflexivity|]. exfalso. apply (P1 R HRin Es z); [unfold in_rg; lia | exact Hss]. }
  split; [|split; [|split]].
  - intros R' HIn Hs z Hz. destruct (Forall2_In_l _ A A' R' HF HIn) as [R0 [HR0 HS]].
    rewrite (is_shadow_same R0 R' HS) in Hs. unfold in_rg in Hz. rewrite (rbase_same ρ R0 R' HS) in Hz.
    destruct HS as [_ [_ [E3 _]]]. rewrite E3 in Hz. exact (P1 R0 HR0 Hs z Hz).
  - intros z Hss Hout.
    assert (Hout0 : forall R0, In R0 A -> is_shadow R0 = true -> ~ in_rg ρ R0 z).
    { intros R0 HIn Hs Hz. destruct (Forall2_In_r _ A A' R0 HF HIn) as [R' [HR' HS]].
      apply (Hout R' HR'); [rewrite (is_shadow_same R0 R' HS); exact Hs|]. unfold in_rg in *.
      rewrite (rbase_same ρ R0 R' HS). destruct HS as [_ [_ [E3 _]]]. rewrite E3. exact Hz. }
    assert (Hnw : ~ (bv_unsigned a <= z < bv_unsigned a + Z.of_nat (length bs))).
    { intros Hz. apply (Hout0 R HRin (Hwss z Hss Hz)). unfold in_rg. lia. }
    rewrite (Hkeep z (Hss64 z Hss) Hnw). exact (P2 z Hss Hout0).
  - destruct P3 as [P3|P3]; [left | right]; intros z Hz; assert (Hss : in_ss z) by (left; exact Hz).
    + apply Hsome; [exact (Hss64 z Hss) | exact (P3 z Hz)].
    + assert (Hnw : ~ (bv_unsigned a <= z < bv_unsigned a + Z.of_nat (length bs))) by (intros Hw; exact (Hmapped z Hss Hw (P3 z Hz))).
      rewrite (Hkeep z (Hss64 z Hss) Hnw). exact (P3 z Hz).
  - destruct P4 as [P4|P4]; [left | right]; intros z Hz; assert (Hss : in_ss z) by (right; exact Hz).
    + apply Hsome; [exact (Hss64 z Hss) | exact (P4 z Hz)].
    + assert (Hnw : ~ (bv_unsigned a <= z < bv_unsigned a + Z.of_nat (length bs))) by (intros Hw; exact (Hmapped z Hss Hw (P4 z Hz))).
      rewrite (Hkeep z (Hss64 z Hss) Hnw). exact (P4 z Hz).
Qed.

(* [comment removed for export] *)
Lemma hs_old_geom (ρ : valuation) (A A' : list region) (m : word -> option byte) :
  Forall2 same_fields A A' -> hs_old ρ A m -> hs_old ρ A' m.
Proof.
  intros HF [P1 [P2 P34]]. split; [|split; [|exact P34]].
  - intros R' HIn Hs z Hz. destruct (Forall2_In_l _ A A' R' HF HIn) as [R0 [HR0 HS]].
    rewrite (is_shadow_same R0 R' HS) in Hs. unfold in_rg in Hz. rewrite (rbase_same ρ R0 R' HS) in Hz.
    destruct HS as [_ [_ [E3 _]]]. rewrite E3 in Hz. exact (P1 R0 HR0 Hs z Hz).
  - intros z Hss Hout. apply P2; [exact Hss|].
    intros R0 HIn Hsh Hz. destruct (Forall2_In_r _ A A' R0 HF HIn) as [R' [HR' HS]].
    apply (Hout R' HR'); [rewrite (is_shadow_same R0 R' HS); exact Hsh|]. unfold in_rg in *.
    rewrite (rbase_same ρ R0 R' HS). destruct HS as [_ [_ [E3 _]]]. rewrite E3. exact Hz.
Qed.

Lemma hs_ok_geom (ρ : valuation) (A A' : list region) (m : word -> option byte) :
  Forall2 same_fields A A' -> hs_ok ρ A m -> hs_ok ρ A' m.
Proof. intros HF [Hpl|Hold]; [left; exact (plain_mode_same A A' HF Hpl) | right; exact (hs_old_geom ρ A A' m HF Hold)]. Qed.

Lemma a_store4_sound (ρ : valuation) (s : store) (A A' : list region) (m : word -> option byte) (v : xv) (a : bv 64) (nb : list xb) (bs : list byte) :
  segs_low segs -> sat ρ s -> RMem segs ρ A m -> hs_ok ρ A m -> xv_val ρ v a -> (1 <= length nb < 1000)%nat -> Forall2 (xb_bv ρ) nb bs ->
  a_store4 s A v nb = Some A' ->
  store_ok segs m a (length nb) = true /\ RMem segs ρ A' (write_to_mem m a bs) /\ hs_ok ρ A' (write_to_mem m a bs).
Proof.
  intros Hlow Hs HM Hhs Hv Hn Hf H. pose proof (Forall2_length Hf) as Hlen. unfold a_store4 in H.
  destruct (a_store3 s A v nb) as [A0|] eqn:E.
  - injection H as <-. destruct (a_store3_sound ρ s A A0 m v a nb bs Hs HM Hv Hn Hf E) as [Hok HM'].
    split; [exact Hok|]. split; [exact HM'|].
    pose proof (a_store3_in ρ s A A0 v a nb Hs (proj1 HM) Hv Hn E) as Hin.
    assert (Ha64 : bv_unsigned a + Z.of_nat (length bs) <= two64).
    { destruct Hin as [R [HR [H1 H2]]]. destruct HM as [Hok0 _].
      assert (Hwf : region_wf ρ R).
      { clear -Hok0 HR. induction A as [|R0 A' IH]; [destruct HR|]. destruct Hok0 as [W [_ Hok']].
        destruct HR as [<-|HR]; [exact W | apply IH; assumption]. }
      destruct Hwf as [W1 _]. rewrite <- Hlen. lia. }
    apply (hs_ok_write ρ A A0 m a bs Hlow Hhs (a_store3_fields s A A0 v nb E)); [rewrite <- Hlen; exact Hin | exact Ha64 | rewrite <- Hlen; exact Hok].
  - destruct (xaddr v) as [[ts o]|] eqn:Ea; [|discriminate].
    destruct (forallb xb_is0 nb &&& hs_wit s A &&& in_hs s ts o (Z.of_nat (length nb))) eqn:Ec; [|discriminate].
    apply land_true in Ec as [Ec Eh]. apply land_true in Ec as [Hz0 Esh].
    destruct (in_hs_ex ρ s ts o _ Hs Eh) as (lo & hi & Hr & Eh1 & Eh2).
    set (f := leval ρ (wS o, ts)) in *.
    assert (Ha : bv_unsigned a = f).
    { rewrite (xaddr_val ρ v a ts o Hv Ea). unfold smod. rewrite <- (wS_mod o). rewrite Zplus_mod_idemp_r.
      replace (teval ρ ts + wS o) with f by (unfold f, leval; cbn [fst snd]; ring).
      apply Z.mod_small. unfold hs_beg, hs_hi, two64 in *. lia. }
    assert (Haw : a = wz f) by (apply bv_eq; rewrite u_wz; [exact Ha | unfold hs_beg, hs_hi in *; lia]).
    assert (Hbz : forall k b, nth_error bs k = Some b -> b = Z_to_bv 8 0).
    { intros k b Hk2. rewrite forallb_forall in Hz0.
      assert (Hkl : (k < length bs)%nat) by (apply nth_error_Some; rewrite Hk2; discriminate).
      destruct (Forall2_nth_error_ex _ nb bs k BT Hf ltac:(lia)) as [b' [Hb' Hab]].
      rewrite Hk2 in Hb'. injection Hb' as <-.
      assert (Hin : In (nth k nb BT) nb) by (apply nth_In; lia).
      specialize (Hz0 _ Hin). unfold xb_bv in Hab. destruct (nth k nb BT); try discriminate. cbn [xb_is0] in Hz0.
      apply Uint63.eqb_spec in Hz0. subst. cbn [xb_z] in Hab. apply bv_eq. rewrite Hab. reflexivity. }
    assert (Hin : forall y : word, f <= bv_unsigned y < f + Z.of_nat (length nb) -> write_to_mem m a bs y = Some (Z_to_bv 8 0)).
    { intros y Hy. rewrite Haw. rewrite (write_to_mem_spec bs m f y) by (unfold hs_beg, hs_hi in *; lia).
      rewrite <- Hlen. replace ((f <=? bv_unsigned y) && (bv_unsigned y <? f + Z.of_nat (length nb))) with true
        by (symmetry; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
      destruct (nth_error bs (Z.to_nat (bv_unsigned y - f))) as [b|] eqn:Eb.
      - rewrite (Hbz _ b Eb). reflexivity.
      - apply nth_error_None in Eb. lia. }
    assert (Hout : forall y : word, ~ (f <= bv_unsigned y < f + Z.of_nat (length nb)) -> write_to_mem m a bs y = m y).
    { intros y Hy. rewrite Haw. rewrite (write_to_mem_spec bs m f y) by (unfold hs_beg, hs_hi in *; lia).
      rewrite <- Hlen. replace ((f <=? bv_unsigned y) && (bv_unsigned y <? f + Z.of_nat (length nb))) with false; [reflexivity|].
      symmetry. apply Bool.not_true_iff_false. intros Hc. apply andb_prop in Hc as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
      apply Hy. lia. }
    assert (Hold : hs_old ρ A m) by (destruct (hs_wit_ex s A Esh) as (W & HW & HWs & _); exact (hs_old_of_sh ρ A m W HW HWs Hhs)).
    destruct Hold as [P1 [P2 [P3 P4]]].
    (* [comment removed for export] *)
    assert (HSm : forall z, hs_beg <= z < hs_hi -> m (wz z) <> None).
    { apply hs_wit_ex in Esh as (R & HRin & Hsh & Hpos & Hb).
      destruct (in_hs_l_ex ρ s _ _ _ Hs Hb) as (lb & hb & Hrb & Hb1 & Hb2).
      assert (Hrb' : rbase ρ R = leval ρ (wS (rg_bo R), rg_ts R)).
      { unfold rbase, smod. rewrite <- (wS_mod (rg_bo R)). rewrite Zplus_mod_idemp_r.
        replace (teval ρ (rg_ts R) + wS (rg_bo R)) with (leval ρ (wS (rg_bo R), rg_ts R)) by (unfold leval; cbn [fst snd]; ring).
        apply Z.mod_small. unfold hs_beg, hs_hi, two64 in *. lia. }
      destruct HM as [_ HR]. rewrite Forall_forall in HR.
      pose proof (HR R HRin) as HR0. rewrite RRegion_ne in HR0 by (unfold is_shadow, is_entry in *; destruct (rg_kind R); first [reflexivity | discriminate Hsh]).
      destruct (HR0 0%uint63 ltac:(change (to_Z 0%uint63) with 0; lia)) as [_ Hw].
      assert (Hwr : rk_writable (rg_kind R) = true) by (unfold is_shadow in Hsh; destruct (rg_kind R); try discriminate; reflexivity).
      specialize (Hw Hwr). change (to_Z 0%uint63) with 0 in Hw. rewrite Z.add_0_r in Hw.
      assert (Hm0 : m (wz (rbase ρ R)) <> None) by (apply wview_mapped; [exact Hlow | right; rewrite Hrb'; unfold hs_beg, hs_hi in *; lia | rewrite Hrb'; unfold hs_beg, hs_hi, two64 in *; lia | exact Hw]).
      destruct P4 as [P4|P4]; [exact P4|]. exfalso. apply Hm0. apply P4. rewrite Hrb'. unfold hs_beg, hs_hi in *. lia. }
    pose proof (havoc_all_fields s ts o _ A A' H) as HF.
    assert (Hss64 : forall z, in_ss z -> 0 <= z < two64) by (intros z Hz; unfold in_ss, ls_beg, ls_end, hs_beg, hs_hi, two64 in *; lia).
    split; [|split].
    + rewrite Haw. apply store_ok_mapped; [unfold hs_beg in *; lia | unfold hs_hi, two64 in *; lia |].
      intros j Hj. apply HSm. lia.
    + destruct HM as [Hok HR]. split; [exact (regions_ok_same ρ A A' HF Hok)|].
      exact (havoc_all_sound ρ s ts o (Z.of_nat (length nb)) m (write_to_mem m a bs) f Hs eq_refl ltac:(lia) ltac:(lia) ltac:(lia) Hin Hout A A' H Hok HR P1).
    + right. split; [|split; [|split]].
      * intros R' HIn Hsh z Hz. destruct (Forall2_In_l _ A A' R' HF HIn) as [R0 [HR0 HS]].
        rewrite (is_shadow_same R0 R' HS) in Hsh. unfold in_rg in Hz. rewrite (rbase_same ρ R0 R' HS) in Hz.
        destruct HS as [_ [_ [E3 _]]]. rewrite E3 in Hz. exact (P1 R0 HR0 Hsh z Hz).
      * intros z Hss Hout'.
        destruct (Z_lt_le_dec z f) as [H1|H1]; [|destruct (Z_lt_le_dec z (f + Z.of_nat (length nb))) as [H2|H2]].
        -- rewrite Hout by (rewrite u_wz by exact (Hss64 z Hss); lia). apply P2; [exact Hss|].
           intros R0 HIn Hsh Hz. destruct (Forall2_In_r _ A A' R0 HF HIn) as [R' [HR' HS]].
           apply (Hout' R' HR'); [rewrite (is_shadow_same R0 R' HS); exact Hsh|]. unfold in_rg in *.
           rewrite (rbase_same ρ R0 R' HS). destruct HS as [_ [_ [E3 _]]]. rewrite E3. exact Hz.
        -- right. apply Hin. rewrite u_wz by exact (Hss64 z Hss). lia.
        -- rewrite Hout by (rewrite u_wz by exact (Hss64 z Hss); lia). apply P2; [exact Hss|].
           intros R0 HIn Hsh Hz. destruct (Forall2_In_r _ A A' R0 HF HIn) as [R' [HR' HS]].
           apply (Hout' R' HR'); [rewrite (is_shadow_same R0 R' HS); exact Hsh|]. unfold in_rg in *.
           rewrite (rbase_same ρ R0 R' HS). destruct HS as [_ [_ [E3 _]]]. rewrite E3. exact Hz.
      * destruct P3 as [P3|P3]; [left | right]; intros z Hz;
          (rewrite Hout by (rewrite u_wz by (unfold ls_beg, ls_end, two64 in *; lia); unfold hs_beg, ls_end in *; lia)); exact (P3 z Hz).
      * left. intros z Hz. apply write_to_mem_some. exact (HSm z Hz).
Qed.

(* [comment removed for export] *)
Definition a_zfill (s : store) (A : list region) (ts : terms) (o : w64) (n : Z) : option (list region) :=
  if hs_wit s A &&& in_hs s ts o n &&& (0 <=? n)
  then havoc_all s ts o n A else None.

Lemma a_zfill_sound (ρ : valuation) (s : store) (A A' : list region) (m m' : word -> option byte) (ts : terms) (o : w64) (n : Z) :
  segs_low segs -> sat ρ s -> RMem segs ρ A m -> hs_ok ρ A m ->
  a_zfill s A ts o n = Some A' ->
  hs_beg <= leval ρ (wS o, ts) /\ leval ρ (wS o, ts) + n <= hs_hi /\ 0 <= n /\
  store_ok segs m (wz (leval ρ (wS o, ts))) (Z.to_nat n) = true /\
  ((forall y : word, leval ρ (wS o, ts) <= bv_unsigned y < leval ρ (wS o, ts) + n -> m' y = Some (Z_to_bv 8 0)) ->
   (forall y : word, ~ (leval ρ (wS o, ts) <= bv_unsigned y < leval ρ (wS o, ts) + n) -> m' y = m y) ->
   RMem segs ρ A' m' /\ hs_ok ρ A' m' /\ Forall2 same_fields A A').
Proof.
  intros Hlow Hs HM Hhs H. unfold a_zfill in H.
  destruct (hs_wit s A &&& in_hs s ts o n &&& (0 <=? n)) eqn:Ec; [|discriminate].
  apply land_true in Ec as [Ec Hn0]. apply land_true in Ec as [Esh Eh]. apply Z.leb_le in Hn0.
  destruct (in_hs_ex ρ s ts o _ Hs Eh) as (lo & hi & Hr & Eh1 & Eh2).
  set (f := leval ρ (wS o, ts)) in *.
  assert (Hold : hs_old ρ A m) by (destruct (hs_wit_ex s A Esh) as (W & HW & HWs & _); exact (hs_old_of_sh ρ A m W HW HWs Hhs)).
  destruct Hold as [P1 [P2 [P3 P4]]].
  assert (HSm : forall z, hs_beg <= z < hs_hi -> m (wz z) <> None).
  { apply hs_wit_ex in Esh as (R & HRin & Hsh & Hpos & Hb).
    destruct (in_hs_l_ex ρ s _ _ _ Hs Hb) as (lb & hb & Hrb & Hb1 & Hb2).
    assert (Hrb' : rbase ρ R = leval ρ (wS (rg_bo R), rg_ts R)).
    { unfold rbase, smod. rewrite <- (wS_mod (rg_bo R)). rewrite Zplus_mod_idemp_r.
      replace (teval ρ (rg_ts R) + wS (rg_bo R)) with (leval ρ (wS (rg_bo R), rg_ts R)) by (unfold leval; cbn [fst snd]; ring).
      apply Z.mod_small. unfold hs_beg, hs_hi, two64 in *. lia. }
    destruct HM as [_ HR]. rewrite Forall_forall in HR.
    pose proof (HR R HRin) as HR0. rewrite RRegion_ne in HR0 by (unfold is_shadow, is_entry in *; destruct (rg_kind R); first [reflexivity | discriminate Hsh]).
    destruct (HR0 0%uint63 ltac:(change (to_Z 0%uint63) with 0; lia)) as [_ Hw].
    assert (Hwr : rk_writable (rg_kind R) = true) by (unfold is_shadow in Hsh; destruct (rg_kind R); try discriminate; reflexivity).
    specialize (Hw Hwr). change (to_Z 0%uint63) with 0 in Hw. rewrite Z.add_0_r in Hw.
    assert (Hm0 : m (wz (rbase ρ R)) <> None) by (apply wview_mapped; [exact Hlow | right; rewrite Hrb'; unfold hs_beg, hs_hi in *; lia | rewrite Hrb'; unfold hs_beg, hs_hi, two64 in *; lia | exact Hw]).
    destruct P4 as [P4|P4]; [exact P4|]. exfalso. apply Hm0. apply P4. rewrite Hrb'. unfold hs_beg, hs_hi in *. lia. }
  pose proof (havoc_all_fields s ts o _ A A' H) as HF.
  assert (Hss64 : forall z, in_ss z -> 0 <= z < two64) by (intros z Hz; unfold in_ss, ls_beg, ls_end, hs_beg, hs_hi, two64 in *; lia).
  split; [lia|]. split; [lia|]. split; [exact Hn0|]. split.
  - apply store_ok_mapped; [unfold hs_beg in *; lia | rewrite Z2Nat.id by lia; unfold hs_hi, two64 in *; lia |].
    intros j Hj. rewrite Z2Nat.id in Hj by lia. apply HSm. lia.
  - intros Hin Hout. split; [|split; [|exact HF]].
    + destruct HM as [Hok HR]. split; [exact (regions_ok_same ρ A A' HF Hok)|].
      exact (havoc_all_sound ρ s ts o n m m' f Hs eq_refl ltac:(lia) ltac:(lia) ltac:(unfold hs_beg, hs_hi in *; lia) Hin Hout A A' H Hok HR P1).
    + right. split; [|split; [|split]].
      * intros R' HIn Hsh z Hz. destruct (Forall2_In_l _ A A' R' HF HIn) as [R0 [HR0 HS]].
        rewrite (is_shadow_same R0 R' HS) in Hsh. unfold in_rg in Hz. rewrite (rbase_same ρ R0 R' HS) in Hz.
        destruct HS as [_ [_ [E3 _]]]. rewrite E3 in Hz. exact (P1 R0 HR0 Hsh z Hz).
      * intros z Hss Hout'.
        destruct (Z_lt_le_dec z f) as [H1|H1]; [|destruct (Z_lt_le_dec z (f + n)) as [H2|H2]].
        -- rewrite Hout by (rewrite u_wz by exact (Hss64 z Hss); lia). apply P2; [exact Hss|].
           intros R0 HIn Hsh Hz. destruct (Forall2_In_r _ A A' R0 HF HIn) as [R' [HR' HS]].
           apply (Hout' R' HR'); [rewrite (is_shadow_same R0 R' HS); exact Hsh|]. unfold in_rg in *.
           rewrite (rbase_same ρ R0 R' HS). destruct HS as [_ [_ [E3 _]]]. rewrite E3. exact Hz.
        -- right. apply Hin. rewrite u_wz by exact (Hss64 z Hss). lia.
        -- rewrite Hout by (rewrite u_wz by exact (Hss64 z Hss); lia). apply P2; [exact Hss|].
           intros R0 HIn Hsh Hz. destruct (Forall2_In_r _ A A' R0 HF HIn) as [R' [HR' HS]].
           apply (Hout' R' HR'); [rewrite (is_shadow_same R0 R' HS); exact Hsh|]. unfold in_rg in *.
           rewrite (rbase_same ρ R0 R' HS). destruct HS as [_ [_ [E3 _]]]. rewrite E3. exact Hz.
      * destruct P3 as [P3|P3]; [left | right]; intros z Hz;
          (rewrite Hout by (rewrite u_wz by (unfold ls_beg, ls_end, two64 in *; lia); unfold hs_beg, ls_end in *; lia)); exact (P3 z Hz).
      * left. intros z Hz. destruct (Z_lt_le_dec z f) as [H1|H1]; [|destruct (Z_lt_le_dec z (f + n)) as [H2|H2]].
        -- rewrite Hout by (rewrite u_wz by (unfold hs_beg, hs_hi, two64 in *; lia); lia). exact (HSm z Hz).
        -- rewrite Hin by (rewrite u_wz by (unfold hs_beg, hs_hi, two64 in *; lia); lia). discriminate.
        -- rewrite Hout by (rewrite u_wz by (unfold hs_beg, hs_hi, two64 in *; lia); lia). exact (HSm z Hz).
Qed.

End WithSegs.
