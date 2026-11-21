(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan Require Import AllocSim.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.IK Require Import ZSysLite ZCall.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.PropExec.FPState}.

Fixpoint outside_all (x : Z) (rs : list (Z * Z)) : Prop :=
  match rs with
  | [] => True
  | (lo, n) :: rs' => ~ (lo <= x < lo + n) /\ outside_all x rs'
  end.

Fixpoint disj_all (a n : Z) (rs : list (Z * Z)) : Prop :=
  match rs with
  | [] => True
  | (lo, len) :: rs' => (a + n <= lo \/ lo + len <= a) /\ disj_all a n rs'
  end.

Fixpoint in_some (a n : Z) (rs : list (Z * Z)) : Prop :=
  match rs with
  | [] => False
  | (lo, len) :: rs' => (lo <= a /\ a + n <= lo + len) \/ in_some a n rs'
  end.

Fixpoint ranges_ok (rs : list (Z * Z)) : Prop :=
  match rs with
  | [] => True
  | (lo, len) :: rs' => 0 <= lo /\ lo + len <= two64 /\ ranges_ok rs'
  end.

Lemma disj_outside : forall a n rs x, disj_all a n rs -> a <= x < a + n -> outside_all x rs.
Proof.
  intros a n rs x. induction rs as [|[lo len] rs IH]; cbn; intros H Hx; [exact I|].
  destruct H as [H1 H2]. split; [lia | apply IH; assumption].
Qed.

Lemma in_some_not_outside : forall a n rs x, in_some a n rs -> a <= x < a + n -> ~ outside_all x rs.
Proof.
  intros a n rs x. induction rs as [|[lo len] rs IH]; cbn; intros H Hx; [exact (fun _ => H)|].
  intros [H1 H2]. destruct H as [H|H]; [lia | exact (IH H Hx H2)].
Qed.

Definition magreeL (M0 M : mem) (rs : list (Z * Z)) : Prop :=
  forall x : word, outside_all (bv_unsigned x) rs -> M x = M0 x.

Lemma magreeL_refl : forall M rs, magreeL M M rs.
Proof. intros M rs x _. reflexivity. Qed.

Definition mpostL (segs : list Segment) (M X : mem) (rs : list (Z * Z)) : Prop :=
  magreeL M X rs /\ (forall a n, mem_wr segs M a n -> mem_wr segs X a n).

Lemma mpostL_refl : forall segs M rs, mpostL segs M M rs.
Proof. intros. split; [apply magreeL_refl | auto]. Qed.

Lemma mpostL_trans : forall segs M1 M2 M3 rs,
  mpostL segs M1 M2 rs -> mpostL segs M2 M3 rs -> mpostL segs M1 M3 rs.
Proof.
  intros segs M1 M2 M3 rs [A1 W1] [A2 W2]. split; [| auto].
  intros x Hx. rewrite (A2 x Hx). apply A1. exact Hx.
Qed.

Lemma magreeL_weaken : forall M0 M rs rs',
  (forall x, outside_all x rs' -> outside_all x rs) -> magreeL M0 M rs -> magreeL M0 M rs'.
Proof. intros M0 M rs rs' Himp HA x Hx. apply HA. apply Himp. exact Hx. Qed.

Definition wb_stableL (Fr : mem -> Prop) (rs : list (Z * Z)) : Prop :=
  forall M a bs, framed Fr M -> in_some a (Z.of_nat (length bs)) rs -> framed Fr (wbytes M (w64 a) bs).

Lemma mpostL_stable : forall segs M0 rs, ranges_ok rs ->
  wb_stableL (fun M => mpostL segs M0 M rs) rs.
Proof.
  intros segs M0 rs Hok M a bs [HA HW] Hin. unfold framed. split.
  - intros x Hx.
    assert (Hb : 0 <= a /\ a + Z.of_nat (length bs) <= two64).
    { clear HA HW Hx. induction rs as [|[lo len] rs IH]; cbn in *; [destruct Hin|].
      destruct Hok as (O1 & O2 & O3). destruct Hin as [Hin|Hin]; [lia | apply IH; assumption]. }
    rewrite wbytes_out; [apply HA; exact Hx | lia | lia |].
    intros Hxin. exact (in_some_not_outside _ _ _ _ Hin Hxin Hx).
  - intros a' n' H. apply mem_wr_frame. apply HW. exact H.
Qed.

Section Facts.
Variable segs : list Segment.

Lemma mem_is_magreeL : forall M0 M rs a bs,
  magreeL M0 M rs -> mem_is segs M0 a bs ->
  0 <= a -> a + Z.of_nat (length bs) <= two64 -> disj_all a (Z.of_nat (length bs)) rs ->
  mem_is segs M a bs.
Proof.
  intros M0 M rs a bs HA H Ha Hn Hd. unfold mem_is in *.
  destruct bs as [|b bs']; [reflexivity|].
  assert (a < two64) by (cbn [length] in Hn; lia).
  rewrite (rdn_ext segs (length (b :: bs')) M M0 (w64 a)); [exact H| |];
    rewrite w64_unsigned, mod_small_u64 by lia; [rewrite <- two64_eq; lia|].
  intros x Hx. apply HA. eapply disj_outside; [exact Hd | lia].
Qed.

Lemma mem_u64_magreeL : forall M0 M rs a e,
  magreeL M0 M rs -> mem_u64 segs M0 a e -> 0 <= a -> a + 8 <= two64 -> disj_all a 8 rs -> mem_u64 segs M a e.
Proof. intros. unfold mem_u64 in *. eapply mem_is_magreeL; try eassumption; rewrite length_Z_to_le_bytes; assumption. Qed.
Lemma mem_u32_magreeL : forall M0 M rs a e,
  magreeL M0 M rs -> mem_u32 segs M0 a e -> 0 <= a -> a + 4 <= two64 -> disj_all a 4 rs -> mem_u32 segs M a e.
Proof. intros. unfold mem_u32 in *. eapply mem_is_magreeL; try eassumption; rewrite length_Z_to_le_bytes; assumption. Qed.
Lemma mem_u16_magreeL : forall M0 M rs a e,
  magreeL M0 M rs -> mem_u16 segs M0 a e -> 0 <= a -> a + 2 <= two64 -> disj_all a 2 rs -> mem_u16 segs M a e.
Proof. intros. unfold mem_u16 in *. eapply mem_is_magreeL; try eassumption; rewrite length_Z_to_le_bytes; assumption. Qed.
Lemma mem_u8_magreeL : forall M0 M rs a e,
  magreeL M0 M rs -> mem_u8 segs M0 a e -> 0 <= a -> a + 1 <= two64 -> disj_all a 1 rs -> mem_u8 segs M a e.
Proof. intros. unfold mem_u8 in *. eapply mem_is_magreeL; try eassumption; rewrite length_Z_to_le_bytes; assumption. Qed.

Lemma mem_zero_magreeL : forall M0 M rs a len,
  magreeL M0 M rs -> mem_zero segs M0 a len -> 0 <= a -> a + len <= two64 -> disj_all a len rs -> mem_zero segs M a len.
Proof.
  intros M0 M rs a len HA Hz Ha Hn Hd i Hi.
  pose proof (Hz i Hi) as Hb. change (mem_is segs M0 (a + i) [Z_to_bv 8 0]) in Hb.
  change (mem_is segs M (a + i) [Z_to_bv 8 0]).
  eapply mem_is_magreeL; [exact HA | exact Hb | lia | cbn [length Z.of_nat Pos.of_succ_nat]; lia |].
  cbn [length Z.of_nat Pos.of_succ_nat].
  clear Hz Hb HA. induction rs as [|[lo n] rs IH]; cbn in *; [exact I|]. destruct Hd as [H1 H2]. split; [lia | apply IH; exact H2].
Qed.

Lemma none_magreeL : forall M0 M rs (x : word),
  magreeL M0 M rs -> outside_all (bv_unsigned x) rs -> M0 x = None -> M x = None.
Proof. intros M0 M rs x HA Hx H0. rewrite (HA x Hx). exact H0. Qed.

End Facts.

Lemma framed_mpostL_trans : forall segs M0 Mo Mn rs rs',
  framed (fun X => mpostL segs M0 X rs) Mo -> mpostL segs Mo Mn rs' ->
  (forall x, outside_all x rs -> outside_all x rs') ->
  framed (fun X => mpostL segs M0 X rs) Mn.
Proof.
  intros segs M0 Mo Mn rs rs' [HF HWF] [HA HW] Himp. unfold framed. split; [| auto].
  intros x Hx. rewrite (HA x (Himp _ Hx)). apply HF. exact Hx.
Qed.

Fixpoint ranges_within (rs' rs : list (Z * Z)) : Prop :=
  match rs' with
  | [] => True
  | (lo, n) :: r => in_some lo n rs /\ ranges_within r rs
  end.

Lemma ranges_within_outside : forall rs' rs x,
  ranges_within rs' rs -> outside_all x rs -> outside_all x rs'.
Proof.
  intros rs' rs x. induction rs' as [|[lo n] r IH]; cbn; intros Hw Hx; [exact I|].
  destruct Hw as [Hin Hw]. split; [| apply IH; assumption].
  intros Hxin. exact (in_some_not_outside _ _ _ _ Hin Hxin Hx).
Qed.

Lemma mem_u64_magreeL1 : forall segs M0 M rs a e,
  magreeL M0 M rs -> mem_u64 segs M0 a e -> (0 <= a /\ a + 8 <= two64 /\ disj_all a 8 rs) -> mem_u64 segs M a e.
Proof. intros segs M0 M rs a e HA H (H1 & H2 & H3). exact (mem_u64_magreeL segs M0 M rs a e HA H H1 H2 H3). Qed.
Lemma mem_u32_magreeL1 : forall segs M0 M rs a e,
  magreeL M0 M rs -> mem_u32 segs M0 a e -> (0 <= a /\ a + 4 <= two64 /\ disj_all a 4 rs) -> mem_u32 segs M a e.
Proof. intros segs M0 M rs a e HA H (H1 & H2 & H3). exact (mem_u32_magreeL segs M0 M rs a e HA H H1 H2 H3). Qed.
Lemma mem_u16_magreeL1 : forall segs M0 M rs a e,
  magreeL M0 M rs -> mem_u16 segs M0 a e -> (0 <= a /\ a + 2 <= two64 /\ disj_all a 2 rs) -> mem_u16 segs M a e.
Proof. intros segs M0 M rs a e HA H (H1 & H2 & H3). exact (mem_u16_magreeL segs M0 M rs a e HA H H1 H2 H3). Qed.
Lemma mem_u8_magreeL1 : forall segs M0 M rs a e,
  magreeL M0 M rs -> mem_u8 segs M0 a e -> (0 <= a /\ a + 1 <= two64 /\ disj_all a 1 rs) -> mem_u8 segs M a e.
Proof. intros segs M0 M rs a e HA H (H1 & H2 & H3). exact (mem_u8_magreeL segs M0 M rs a e HA H H1 H2 H3). Qed.
Lemma mem_is_magreeL1 : forall segs M0 M rs a bs,
  magreeL M0 M rs -> mem_is segs M0 a bs ->
  (0 <= a /\ a + Z.of_nat (length bs) <= two64 /\ disj_all a (Z.of_nat (length bs)) rs) -> mem_is segs M a bs.
Proof. intros segs M0 M rs a bs HA H (H1 & H2 & H3). exact (mem_is_magreeL segs M0 M rs a bs HA H H1 H2 H3). Qed.
Lemma mem_zero_magreeL1 : forall segs M0 M rs a len,
  magreeL M0 M rs -> mem_zero segs M0 a len -> (0 <= a /\ a + len <= two64 /\ disj_all a len rs) -> mem_zero segs M a len.
Proof. intros segs M0 M rs a len HA H (H1 & H2 & H3). exact (mem_zero_magreeL segs M0 M rs a len HA H H1 H2 H3). Qed.

End FXG.
Ltac zconj_nf t :=
  let t1 := eval hnf in t in
  lazymatch t1 with
  | ?P /\ ?rest => let r := zconj_nf rest in constr:(P /\ r)
  | _ => t1
  end.
Ltac zconj_norm := lazymatch goal with |- ?G => let G' := zconj_nf G in change G' end.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.PropExec.FPState}.
End FXG.
Ltac zhead_cl a :=
  lazymatch a with
  | ?x + _ => zhead_cl x
  | ?x - _ => zhead_cl x
  | ?x => x
  end.
Ltac in_some_hd_pass :=
  lazymatch goal with
  | |- (?lo <= ?a /\ _) \/ _ =>
      let ha := zhead_cl a in let hl := zhead_cl lo in
      first [ constr_eq ha hl; left; zlia | right; in_some_hd_pass ]
  end.
Ltac in_some_tac := solve [ hnf; cbn [in_some]; zprune; first [ in_some_hd_pass | repeat first [ left; zlia | right ] ] ].
Ltac disj_all_tac := solve [ zconj_norm; zlia ].
Ltac ranges_ok_tac := solve [ zconj_norm; zlia ].
Ltac ranges_within_tac := solve [ hnf; cbn [ranges_within]; zprune; repeat split; try exact I; in_some_tac ].
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.PropExec.FPState}.
End FXG.
Ltac zsideL :=
  lazymatch goal with
  | |- ?A /\ ?B /\ disj_all ?a ?n ?rs =>
      let d := zconj_nf constr:(disj_all a n rs) in change (A /\ B /\ d)
  | |- _ => idtac
  end;
  zlen_norm; zlia.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.PropExec.FPState}.

End FXG.
Ltac zreattachL_extra HA Mo Mn := idtac.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.PropExec.FPState}.

End FXG.
Ltac zreattachL HP :=
  let HA := fresh "HA" in let HW := fresh "HW" in
  destruct HP as [HA HW];
  lazymatch type of HA with magreeL ?Mo ?Mn ?rs =>
  repeat match goal with
  | H : mem_u64 ?segs Mo ?a ?e |- _ =>
      first [ apply (mem_u64_magreeL1 segs Mo Mn rs a e HA) in H; [|solve [zsideL]]
            | idtac "zreattachL: dropped u64 fact at" a; clear H ]
  | H : mem_u32 ?segs Mo ?a ?e |- _ =>
      first [ apply (mem_u32_magreeL1 segs Mo Mn rs a e HA) in H; [|solve [zsideL]]
            | idtac "zreattachL: dropped u32 fact at" a; clear H ]
  | H : mem_u16 ?segs Mo ?a ?e |- _ =>
      first [ apply (mem_u16_magreeL1 segs Mo Mn rs a e HA) in H; [|solve [zsideL]]
            | idtac "zreattachL: dropped u16 fact at" a; clear H ]
  | H : mem_u8 ?segs Mo ?a ?e |- _ =>
      first [ apply (mem_u8_magreeL1 segs Mo Mn rs a e HA) in H; [|solve [zsideL]]
            | idtac "zreattachL: dropped u8 fact at" a; clear H ]
  | H : mem_is ?segs Mo ?a ?bs |- _ =>
      first [ apply (mem_is_magreeL1 segs Mo Mn rs a bs HA) in H; [|solve [zsideL]]
            | idtac "zreattachL: dropped mem_is fact at" a; clear H ]
  | H : mem_zero ?segs Mo ?a ?len |- _ =>
      first [ apply (mem_zero_magreeL1 segs Mo Mn rs a len HA) in H; [|solve [zsideL]]
            | idtac "zreattachL: dropped mem_zero fact at" a; clear H ]
  | H : framed (fun X => mpostL _ _ X _) Mo |- _ =>
      first [ let H' := fresh in
              pose proof (framed_mpostL_trans _ _ Mo Mn _ _ H (conj HA HW)
                            ltac:(intros x Hx; eapply ranges_within_outside; [| exact Hx]; ranges_within_tac)) as H';
              clear H; rename H' into H
            | idtac "zreattachL: could not transfer framed mpostL"; clear H ]
  | H : mem_wr ?segs Mo ?a ?n |- _ => apply (HW a n) in H
  end; zreattachL_extra HA Mo Mn; clear HA HW; try clear Mo end.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.PropExec.FPState}.

End FXG.
Ltac zderiveL HAG SF name :=
  lazymatch type of HAG with framed (fun X => mpostL ?segs ?M0 X ?rs) ?Mc =>
  lazymatch type of SF with
  | mem_u64 _ M0 ?a ?e => pose proof (mem_u64_magreeL1 segs M0 Mc rs a e (proj1 HAG) SF ltac:(solve [zsideL])) as name
  | mem_u32 _ M0 ?a ?e => pose proof (mem_u32_magreeL1 segs M0 Mc rs a e (proj1 HAG) SF ltac:(solve [zsideL])) as name
  | mem_u8 _ M0 ?a ?e => pose proof (mem_u8_magreeL1 segs M0 Mc rs a e (proj1 HAG) SF ltac:(solve [zsideL])) as name
  | mem_is _ M0 ?a ?bs => pose proof (mem_is_magreeL1 segs M0 Mc rs a bs (proj1 HAG) SF ltac:(solve [zsideL])) as name
  | mem_zero _ M0 ?a ?len => pose proof (mem_zero_magreeL1 segs M0 Mc rs a len (proj1 HAG) SF ltac:(solve [zsideL])) as name
  end end.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.PropExec.FPState}.

Lemma zframe_start : forall segs M rs (P : mem -> Prop),
  ranges_ok rs ->
  (forall Mc, wb_stableL (fun X => mpostL segs M X rs) rs -> framed (fun X => mpostL segs M X rs) Mc -> P Mc) ->
  P M.
Proof. intros segs M rs P Hok H. apply H; [apply mpostL_stable; exact Hok | apply mpostL_refl]. Qed.



Lemma zzero_out : forall M a n (x : word), 0 <= a -> a + n < two64 -> 0 <= n ->
  ~ (a <= bv_unsigned x < a + n) -> zzero M a n x = M x.
Proof.
  intros M a n x Ha Han Hn Hx. rewrite zzero_pt. unfold zmem.
  rewrite !w64_unsigned, !mod_small_u64 by lia.
  destruct ((a <=? bv_unsigned x) && (bv_unsigned x <? a + n)) eqn:E; [|reflexivity].
  apply andb_true_iff in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. exfalso. apply Hx. lia.
Qed.

Lemma zzero_in : forall M a n (x : word), 0 <= a -> a + n < two64 -> 0 <= n ->
  a <= bv_unsigned x < a + n -> zzero M a n x = Some (Z_to_bv 8 0).
Proof.
  intros M a n x Ha Han Hn Hx. rewrite zzero_pt. unfold zmem.
  rewrite !w64_unsigned, !mod_small_u64 by lia.
  rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
Qed.

Lemma zunmap_in : forall M a n (x : word), 0 <= a -> a + n < two64 -> 0 <= n ->
  a <= bv_unsigned x < a + n -> zunmap M a n x = None.
Proof.
  intros M a n x Ha Han Hn Hx. unfold zunmap, apply_unmaps, zeros_cover. cbn [existsb fst snd].
  rewrite !w64_unsigned, !mod_small_u64 by lia.
  rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
Qed.

Lemma zunmap_out' : forall M a n (x : word), 0 <= a -> a + n < two64 -> 0 <= n ->
  ~ (a <= bv_unsigned x < a + n) -> zunmap M a n x = M x.
Proof.
  intros M a n x Ha Han Hn Hx. apply zunmap_out. rewrite !w64_unsigned, !mod_small_u64 by lia. lia.
Qed.

Lemma wview_ext1 : forall segs M1 M2 (x : word), M1 x = M2 x -> wview segs M1 x = wview segs M2 x.
Proof. intros segs M1 M2 x E. unfold wview. rewrite E. reflexivity. Qed.

Lemma framed_mpostL_zzero : forall segs M M0 a n rs,
  0 <= a -> a + n < two64 -> 0 <= n ->
  framed (fun X => mpostL segs M X rs) M0 ->
  framed (fun X => mpostL segs (zzero M a n) X rs) (zzero M0 a n).
Proof.
  intros segs M M0 a n rs Ha Han Hn [HA HW]. unfold framed. split.
  - intros x Hx. destruct (Z_le_gt_dec a (bv_unsigned x)); [destruct (Z_lt_ge_dec (bv_unsigned x) (a + n))|].
    + rewrite !zzero_in by lia. reflexivity.
    + rewrite !zzero_out by lia. apply HA; assumption.
    + rewrite !zzero_out by lia. apply HA; assumption.
  - intros a' n' H i Hi. specialize (H i Hi).
    destruct (Z_le_gt_dec a (bv_unsigned (w64 (a' + i)))); [destruct (Z_lt_ge_dec (bv_unsigned (w64 (a' + i))) (a + n))|].
    + unfold wview. rewrite zzero_in by lia. discriminate.
    + rewrite (wview_ext1 segs (zzero M0 a n) M0) by (apply zzero_out; lia).
      rewrite (wview_ext1 segs (zzero M a n) M) in H by (apply zzero_out; lia).
      pose proof (HW (a' + i) 1 ltac:(intros j Hj; replace (a' + i + j) with (a' + i) by lia; exact H) 0 ltac:(lia)) as HW1.
      rewrite Z.add_0_r in HW1. exact HW1.
    + rewrite (wview_ext1 segs (zzero M0 a n) M0) by (apply zzero_out; lia).
      rewrite (wview_ext1 segs (zzero M a n) M) in H by (apply zzero_out; lia).
      pose proof (HW (a' + i) 1 ltac:(intros j Hj; replace (a' + i + j) with (a' + i) by lia; exact H) 0 ltac:(lia)) as HW1.
      rewrite Z.add_0_r in HW1. exact HW1.
Qed.

Lemma framed_mpostL_zunmap : forall segs M M0 a n rs,
  0 <= a -> a + n < two64 -> 0 <= n ->
  framed (fun X => mpostL segs M X rs) M0 ->
  framed (fun X => mpostL segs (zunmap M a n) X rs) (zunmap M0 a n).
Proof.
  intros segs M M0 a n rs Ha Han Hn [HA HW]. unfold framed. split.
  - intros x Hx. destruct (Z_le_gt_dec a (bv_unsigned x)); [destruct (Z_lt_ge_dec (bv_unsigned x) (a + n))|].
    + rewrite !zunmap_in by lia. reflexivity.
    + rewrite !zunmap_out' by lia. apply HA; assumption.
    + rewrite !zunmap_out' by lia. apply HA; assumption.
  - intros a' n' H i Hi. specialize (H i Hi).
    destruct (Z_le_gt_dec a (bv_unsigned (w64 (a' + i)))); [destruct (Z_lt_ge_dec (bv_unsigned (w64 (a' + i))) (a + n))|].
    + rewrite (wview_ext1 segs (zunmap M0 a n) (zunmap M a n)); [exact H|]. rewrite !zunmap_in by lia. reflexivity.
    + rewrite (wview_ext1 segs (zunmap M0 a n) M0) by (apply zunmap_out'; lia).
      rewrite (wview_ext1 segs (zunmap M a n) M) in H by (apply zunmap_out'; lia).
      pose proof (HW (a' + i) 1 ltac:(intros j Hj; replace (a' + i + j) with (a' + i) by lia; exact H) 0 ltac:(lia)) as HW1.
      rewrite Z.add_0_r in HW1. exact HW1.
    + rewrite (wview_ext1 segs (zunmap M0 a n) M0) by (apply zunmap_out'; lia).
      rewrite (wview_ext1 segs (zunmap M a n) M) in H by (apply zunmap_out'; lia).
      pose proof (HW (a' + i) 1 ltac:(intros j Hj; replace (a' + i + j) with (a' + i) by lia; exact H) 0 ltac:(lia)) as HW1.
      rewrite Z.add_0_r in HW1. exact HW1.
Qed.

Lemma framed_mpostL_weaken : forall segs M M0 rs rs',
  ranges_within rs rs' ->
  framed (fun X => mpostL segs M X rs) M0 ->
  framed (fun X => mpostL segs M X rs') M0.
Proof.
  intros segs M M0 rs rs' Hw [HA HW]. unfold framed. split; [| exact HW].
  intros x Hx. apply HA. eapply ranges_within_outside; eassumption.
Qed.

End FXG.
Ltac rebaseL_zzero HAG HST a n :=
  lazymatch type of HAG with
  | framed (fun X => mpostL ?segs ?M X ?rs) ?M0 =>
      apply (framed_mpostL_zzero segs M M0 a n rs ltac:(zlia) ltac:(zlia) ltac:(zlia)) in HAG;
      clear HST;
      pose proof (mpostL_stable segs (zzero M a n) rs ltac:(ranges_ok_tac)) as HST
  end.
Ltac rebaseL_zunmap HAG HST a n :=
  lazymatch type of HAG with
  | framed (fun X => mpostL ?segs ?M X ?rs) ?M0 =>
      apply (framed_mpostL_zunmap segs M M0 a n rs ltac:(zlia) ltac:(zlia) ltac:(zlia)) in HAG;
      clear HST;
      pose proof (mpostL_stable segs (zunmap M a n) rs ltac:(ranges_ok_tac)) as HST
  end.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.PropExec.FPState}.

End FXG.
Ltac widenL HAG HST rs' :=
  lazymatch type of HAG with
  | framed (fun X => mpostL ?segs ?M X ?rs) ?M0 =>
      apply (framed_mpostL_weaken segs M M0 rs rs' ltac:(ranges_within_tac)) in HAG;
      clear HST;
      pose proof (mpostL_stable segs M rs' ltac:(ranges_ok_tac)) as HST
  end.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.PropExec.FPState}.



Lemma mem_u16_magree : forall segs M0 M lo1 hi1 lo2 hi2 a e,
  magree M0 M lo1 hi1 lo2 hi2 -> mem_u16 segs M0 a e ->
  0 <= a -> a + 2 <= two64 ->
  (a + 2 <= lo1 \/ hi1 <= a) -> (a + 2 <= lo2 \/ hi2 <= a) ->
  mem_u16 segs M a e.
Proof. intros. unfold mem_u16 in *. eapply mem_is_magree; try eassumption; rewrite length_Z_to_le_bytes; lia. Qed.

Lemma mem_u8_magree : forall segs M0 M lo1 hi1 lo2 hi2 a e,
  magree M0 M lo1 hi1 lo2 hi2 -> mem_u8 segs M0 a e ->
  0 <= a -> a + 1 <= two64 ->
  (a + 1 <= lo1 \/ hi1 <= a) -> (a + 1 <= lo2 \/ hi2 <= a) ->
  mem_u8 segs M a e.
Proof. intros. unfold mem_u8 in *. eapply mem_is_magree; try eassumption; rewrite length_Z_to_le_bytes; lia. Qed.

Lemma mem_zero_magree : forall segs M0 M lo1 hi1 lo2 hi2 a len,
  magree M0 M lo1 hi1 lo2 hi2 -> mem_zero segs M0 a len ->
  0 <= a -> a + len <= two64 ->
  (a + len <= lo1 \/ hi1 <= a) -> (a + len <= lo2 \/ hi2 <= a) ->
  mem_zero segs M a len.
Proof.
  intros segs M0 M lo1 hi1 lo2 hi2 a len HA Hz Ha Hn H1 H2 i Hi.
  pose proof (Hz i Hi) as Hb. change (mem_is segs M0 (a + i) [Z_to_bv 8 0]) in Hb.
  change (mem_is segs M (a + i) [Z_to_bv 8 0]).
  eapply mem_is_magree; [exact HA | exact Hb | lia | cbn [length Z.of_nat Pos.of_succ_nat]; lia | cbn [length Z.of_nat Pos.of_succ_nat]; lia | cbn [length Z.of_nat Pos.of_succ_nat]; lia].
Qed.

Lemma framed_mpostL_trans2 : forall segs M0 Mo Mn rs a1 b1 a2 b2,
  framed (fun X => mpostL segs M0 X rs) Mo -> mpost segs Mo Mn a1 b1 a2 b2 ->
  in_some a1 (b1 - a1) rs \/ b1 <= a1 -> in_some a2 (b2 - a2) rs \/ b2 <= a2 ->
  framed (fun X => mpostL segs M0 X rs) Mn.
Proof.
  intros segs M0 Mo Mn rs a1 b1 a2 b2 [HF HWF] [HA HW] H1 H2. unfold framed. split; [| auto].
  intros x Hx. rewrite (HA x).
  - apply HF. exact Hx.
  - destruct H1 as [H1|H1]; [| lia]. intros Hin. exact (in_some_not_outside _ _ _ (bv_unsigned x) H1 ltac:(lia) Hx).
  - destruct H2 as [H2|H2]; [| lia]. intros Hin. exact (in_some_not_outside _ _ _ (bv_unsigned x) H2 ltac:(lia) Hx).
Qed.

End FXG.
Ltac zreattach_extra HA Mo Mn := idtac.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.PropExec.FPState}.

Lemma mem_u64_magree1 : forall segs M0 M lo1 hi1 lo2 hi2 a e,
  magree M0 M lo1 hi1 lo2 hi2 -> mem_u64 segs M0 a e ->
  (0 <= a /\ a + 8 <= two64 /\ (a + 8 <= lo1 \/ hi1 <= a) /\ (a + 8 <= lo2 \/ hi2 <= a)) ->
  mem_u64 segs M a e.
Proof. intros segs M0 M lo1 hi1 lo2 hi2 a e HA H (H1 & H2 & H3 & H4). exact (mem_u64_magree segs M0 M lo1 hi1 lo2 hi2 a e HA H H1 H2 H3 H4). Qed.
Lemma mem_u32_magree1 : forall segs M0 M lo1 hi1 lo2 hi2 a e,
  magree M0 M lo1 hi1 lo2 hi2 -> mem_u32 segs M0 a e ->
  (0 <= a /\ a + 4 <= two64 /\ (a + 4 <= lo1 \/ hi1 <= a) /\ (a + 4 <= lo2 \/ hi2 <= a)) ->
  mem_u32 segs M a e.
Proof. intros segs M0 M lo1 hi1 lo2 hi2 a e HA H (H1 & H2 & H3 & H4). exact (mem_u32_magree segs M0 M lo1 hi1 lo2 hi2 a e HA H H1 H2 H3 H4). Qed.
Lemma mem_u16_magree1 : forall segs M0 M lo1 hi1 lo2 hi2 a e,
  magree M0 M lo1 hi1 lo2 hi2 -> mem_u16 segs M0 a e ->
  (0 <= a /\ a + 2 <= two64 /\ (a + 2 <= lo1 \/ hi1 <= a) /\ (a + 2 <= lo2 \/ hi2 <= a)) ->
  mem_u16 segs M a e.
Proof. intros segs M0 M lo1 hi1 lo2 hi2 a e HA H (H1 & H2 & H3 & H4). exact (mem_u16_magree segs M0 M lo1 hi1 lo2 hi2 a e HA H H1 H2 H3 H4). Qed.
Lemma mem_u8_magree1 : forall segs M0 M lo1 hi1 lo2 hi2 a e,
  magree M0 M lo1 hi1 lo2 hi2 -> mem_u8 segs M0 a e ->
  (0 <= a /\ a + 1 <= two64 /\ (a + 1 <= lo1 \/ hi1 <= a) /\ (a + 1 <= lo2 \/ hi2 <= a)) ->
  mem_u8 segs M a e.
Proof. intros segs M0 M lo1 hi1 lo2 hi2 a e HA H (H1 & H2 & H3 & H4). exact (mem_u8_magree segs M0 M lo1 hi1 lo2 hi2 a e HA H H1 H2 H3 H4). Qed.
Lemma mem_is_magree1 : forall segs M0 M lo1 hi1 lo2 hi2 a bs,
  magree M0 M lo1 hi1 lo2 hi2 -> mem_is segs M0 a bs ->
  (0 <= a /\ a + Z.of_nat (length bs) <= two64 /\ (a + Z.of_nat (length bs) <= lo1 \/ hi1 <= a) /\ (a + Z.of_nat (length bs) <= lo2 \/ hi2 <= a)) ->
  mem_is segs M a bs.
Proof. intros segs M0 M lo1 hi1 lo2 hi2 a bs HA H (H1 & H2 & H3 & H4). exact (mem_is_magree segs M0 M lo1 hi1 lo2 hi2 a bs HA H H1 H2 H3 H4). Qed.
Lemma mem_zero_magree1 : forall segs M0 M lo1 hi1 lo2 hi2 a len,
  magree M0 M lo1 hi1 lo2 hi2 -> mem_zero segs M0 a len ->
  (0 <= a /\ a + len <= two64 /\ (a + len <= lo1 \/ hi1 <= a) /\ (a + len <= lo2 \/ hi2 <= a)) ->
  mem_zero segs M a len.
Proof. intros segs M0 M lo1 hi1 lo2 hi2 a len HA H (H1 & H2 & H3 & H4). exact (mem_zero_magree segs M0 M lo1 hi1 lo2 hi2 a len HA H H1 H2 H3 H4). Qed.

End FXG.
Ltac zside2 := zlen_norm; zlia.
Ltac zreattach HP ::=
  let HA := fresh "HA" in let HW := fresh "HW" in
  destruct HP as [HA HW];
  lazymatch type of HA with magree ?Mo ?Mn _ _ _ _ =>
  repeat match goal with
  | H : mem_u64 ?segs Mo ?a ?e |- _ =>
      first [ apply (mem_u64_magree1 segs Mo Mn _ _ _ _ a e HA) in H; [|solve [zside2]]
            | idtac "zreattach: dropped u64 fact at" a; clear H ]
  | H : mem_u32 ?segs Mo ?a ?e |- _ =>
      first [ apply (mem_u32_magree1 segs Mo Mn _ _ _ _ a e HA) in H; [|solve [zside2]]
            | idtac "zreattach: dropped u32 fact at" a; clear H ]
  | H : mem_u16 ?segs Mo ?a ?e |- _ =>
      first [ apply (mem_u16_magree1 segs Mo Mn _ _ _ _ a e HA) in H; [|solve [zside2]]
            | idtac "zreattach: dropped u16 fact at" a; clear H ]
  | H : mem_u8 ?segs Mo ?a ?e |- _ =>
      first [ apply (mem_u8_magree1 segs Mo Mn _ _ _ _ a e HA) in H; [|solve [zside2]]
            | idtac "zreattach: dropped u8 fact at" a; clear H ]
  | H : mem_is ?segs Mo ?a ?bs |- _ =>
      first [ apply (mem_is_magree1 segs Mo Mn _ _ _ _ a bs HA) in H; [|solve [zside2]]
            | idtac "zreattach: dropped mem_is fact at" a; clear H ]
  | H : mem_zero ?segs Mo ?a ?len |- _ =>
      first [ apply (mem_zero_magree1 segs Mo Mn _ _ _ _ a len HA) in H; [|solve [zside2]]
            | idtac "zreattach: dropped mem_zero fact at" a; clear H ]
  | H : framed (fun X => mpostL _ _ X _) Mo |- _ =>
      first [ let H' := fresh in
              pose proof (framed_mpostL_trans2 _ _ Mo Mn _ _ _ _ _ H (conj HA HW)
                            ltac:(first [right; zlia | left; in_some_tac]) ltac:(first [right; zlia | left; in_some_tac])) as H';
              clear H; rename H' into H
            | idtac "zreattach: could not transfer framed mpostL"; clear H ]
  | H : framed _ Mo |- _ =>
      first [ let H' := fresh in
              pose proof (framed_mpost_trans _ _ Mo Mn _ _ _ _ _ _ _ _ H (conj HA HW) ltac:(zlia) ltac:(zlia)) as H';
              clear H; rename H' into H
            | idtac "zreattach: could not transfer framed mpost"; clear H ]
  | H : mem_wr ?segs Mo ?a ?n |- _ => apply (HW a n) in H
  end;
  zreattach_extra HA Mo Mn;
  clear HA HW; try clear Mo end.
