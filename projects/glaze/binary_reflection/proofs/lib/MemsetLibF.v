(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module Frame.
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Section FPGen1.
Context {fx : FPState}.


Definition in_rng (a base : word) (len : Z) : Prop :=
  (bv_unsigned base <= bv_unsigned a < bv_unsigned base + len)%Z.



Fixpoint outside (a : word) (rs : list (word * Z)) : Prop :=
  match rs with
  | [] => True
  | (b, n) :: rs' => ~ in_rng a b n /\ outside a rs'
  end.

Lemma outside_app : forall a rs1 rs2, outside a (rs1 ++ rs2) <-> outside a rs1 /\ outside a rs2.
Proof.
  intros a rs1 rs2. induction rs1 as [|[b n] rs1 IH]; cbn; tauto.
Qed.

Definition frame_mod (mem mem' : word -> option byte) (rs : list (word * Z)) : Prop :=
  (forall a, outside a rs -> mem' a = mem a) /\ mem_grows mem mem'.

Lemma frame_mod_refl : forall mem rs, frame_mod mem mem rs.
Proof. intros. split; [intros; reflexivity | apply mem_grows_refl]. Qed.

Lemma frame_mod_weaken : forall mem mem' rs rs',
  (forall a, outside a rs' -> outside a rs) -> frame_mod mem mem' rs -> frame_mod mem mem' rs'.
Proof.
  intros mem mem' rs rs' Hw [He Hg]. split; [|exact Hg]. intros a Ha. apply He, Hw, Ha.
Qed.

Lemma frame_mod_trans : forall m1 m2 m3 rs1 rs2,
  frame_mod m1 m2 rs1 -> frame_mod m2 m3 rs2 -> frame_mod m1 m3 (rs1 ++ rs2).
Proof.
  intros m1 m2 m3 rs1 rs2 [E1 G1] [E2 G2]. split.
  - intros a Ha. apply outside_app in Ha as [H1 H2]. rewrite (E2 a H2). apply E1, H1.
  - eapply mem_grows_trans; eassumption.
Qed.

(* [comment removed for export] *)
Lemma frame_mod_trans_same : forall m1 m2 m3 rs,
  frame_mod m1 m2 rs -> frame_mod m2 m3 rs -> frame_mod m1 m3 rs.
Proof.
  intros m1 m2 m3 rs H1 H2. eapply frame_mod_weaken; [| exact (frame_mod_trans _ _ _ _ _ H1 H2)].
  intros a Ha. apply outside_app. tauto.
Qed.

(* [comment removed for export] *)
Lemma wbytes_outside : forall bs m (base a : word),
  ~ in_rng a base (Z.of_nat (length bs)) ->
  (bv_unsigned base + Z.of_nat (length bs) <= 2 ^ 64)%Z ->
  wbytes m base bs a = m a.
Proof.
  intros bs m base a Hn Hb. unfold in_rng in Hn.
  destruct (Z.lt_ge_cases (bv_unsigned a) (bv_unsigned base)) as [Hlt|Hge].
  - apply wbytes_below; assumption.
  - apply wbytes_above. lia.
Qed.

Lemma frame_mod_wbytes : forall m base bs,
  (bv_unsigned base + Z.of_nat (length bs) <= 2 ^ 64)%Z ->
  frame_mod m (wbytes m base bs) [(base, Z.of_nat (length bs))].
Proof.
  intros m base bs Hb. split.
  - intros a [Ha _]. apply wbytes_outside; assumption.
  - apply wbytes_grows.
Qed.



End FPGen1.
End Frame.
Require Stdlib.Logic.FunctionalExtensionality LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Run OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module MemSplit.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.StreamSim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma wbytes_inside : forall bs m (a x : word),
  bv_unsigned a + Z.of_nat (length bs) <= 2^64 ->
  bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat (length bs) ->
  wbytes m a bs x = Some (nth (Z.to_nat (bv_unsigned x - bv_unsigned a)) bs (Z_to_bv 8 0)).
Proof.
  induction bs as [|b rest IH]; intros m a x Hnw Hx; [cbn in Hx; lia|].
  cbn [wbytes length] in *.
  destruct (Z.eq_dec (bv_unsigned x) (bv_unsigned a)) as [Heq|Hne].
  - assert (x = a) by (apply bv_eq; exact Heq). subst x.
    rewrite Z.sub_diag. cbn [Z.to_nat nth].
    destruct rest as [|b' rest'].
    + cbn [wbytes]. rewrite bv_eqb_refl. reflexivity.
    + cbn [length] in Hnw. rewrite wbytes_below.
      * rewrite bv_eqb_refl. reflexivity.
      * rewrite u_add1 by lia. cbn [length]. lia.
      * rewrite u_add1 by lia. lia.
  - assert (Hu1 : bv_unsigned (a + 1) = bv_unsigned a + 1)
      by (apply u_add1; lia).
    rewrite (IH _ (a + 1)%bv) by (rewrite Hu1; lia).
    rewrite Hu1.
    replace (Z.to_nat (bv_unsigned x - bv_unsigned a))
      with (S (Z.to_nat (bv_unsigned x - (bv_unsigned a + 1)))) by lia.
    reflexivity.
Qed.

Lemma wbytes_outside : forall bs m (a x : word),
  bv_unsigned a + Z.of_nat (length bs) <= 2^64 ->
  (bv_unsigned x < bv_unsigned a \/ bv_unsigned a + Z.of_nat (length bs) <= bv_unsigned x) ->
  wbytes m a bs x = m x.
Proof.
  intros bs m a x Hnw [Hlt|Hge].
  - apply wbytes_below; assumption.
  - apply wbytes_above; assumption.
Qed.

(* [comment removed for export] *)
Lemma wbytes_select : forall (P : word -> bool) (f g : word -> option byte) (a : word) bs,
  bv_unsigned a + Z.of_nat (length bs) <= 2^64 ->
  (forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat (length bs) ->
                    P x = true) ->
  wbytes (fun x => if P x then f x else g x) a bs
  = (fun x => if P x then wbytes f a bs x else g x).
Proof.
  intros P f g a bs Hnw HP. apply functional_extensionality. intro x.
  destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned a)) as [Hlt|Hge].
  - rewrite !wbytes_outside by lia. reflexivity.
  - destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned a + Z.of_nat (length bs))) as [Hin|Hout].
    + rewrite !wbytes_inside by lia. rewrite (HP x) by lia. reflexivity.
    + rewrite !wbytes_outside by lia. reflexivity.
Qed.

Lemma wbytes_select_r : forall (P : word -> bool) (f g : word -> option byte) (a : word) bs,
  bv_unsigned a + Z.of_nat (length bs) <= 2^64 ->
  (forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat (length bs) ->
                    P x = false) ->
  wbytes (fun x => if P x then f x else g x) a bs
  = (fun x => if P x then f x else wbytes g a bs x).
Proof.
  intros P f g a bs Hnw HP. apply functional_extensionality. intro x.
  destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned a)) as [Hlt|Hge].
  - rewrite !wbytes_outside by lia. reflexivity.
  - destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned a + Z.of_nat (length bs))) as [Hin|Hout].
    + rewrite !wbytes_inside by lia. rewrite (HP x) by lia. reflexivity.
    + rewrite !wbytes_outside by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma wbytes_shadow : forall m (a : word) bs1 bs2,
  length bs1 = length bs2 ->
  bv_unsigned a + Z.of_nat (length bs2) <= 2^64 ->
  wbytes (wbytes m a bs1) a bs2 = wbytes m a bs2.
Proof.
  intros m a bs1 bs2 Hlen Hnw. apply functional_extensionality. intro x.
  destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned a)) as [Hlt|Hge].
  - rewrite !wbytes_outside by lia. reflexivity.
  - destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned a + Z.of_nat (length bs2))) as [Hin|Hout].
    + rewrite !wbytes_inside by lia. reflexivity.
    + rewrite !wbytes_outside by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rdn_const : forall segs m (a : word) n b,
  bv_unsigned a + Z.of_nat n <= 2^64 ->
  (forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat n -> m x = Some b) ->
  rdn segs m a n = Some (repeat b n).
Proof.
  intros segs m a n; revert a; induction n as [|n IH]; intros a b Hnw Hall; [reflexivity|].
  cbn [rdn repeat]. rewrite (Hall a) by lia.
  destruct n as [|n'].
  - reflexivity.
  - assert (Hu1 : bv_unsigned (a + 1) = bv_unsigned a + 1) by (apply u_add1; lia).
    rewrite (IH (a + 1)%bv b) by (rewrite Hu1; first [lia | intros x Hx; apply Hall; lia]).
    reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition win_lo (sp0 : word) : Z := bv_unsigned sp0 - stack_max_size.

Definition in_win (sp0 : word) (x : word) : Prop :=
  win_lo sp0 <= bv_unsigned x < bv_unsigned sp0.

Definition cmem (sp0 : word) (mem0 J D : word -> option byte) : word -> option byte :=
  fun a => if (bv_unsigned sp0 <=? bv_unsigned a) then mem0 a
           else if (win_lo sp0 <=? bv_unsigned a) then J a else D a.

(* [comment removed for export] *)
Definition wfJ (sp0 : word) (J : word -> option byte) : Prop :=
  forall x : word, in_win sp0 x -> J x <> None.

Lemma wfJ_const : forall sp0 b, wfJ sp0 (fun _ => Some b).
Proof. intros sp0 b x _. discriminate. Qed.

Lemma wfJ_wbytes : forall sp0 J a bs, wfJ sp0 J -> wfJ sp0 (wbytes J a bs).
Proof. intros sp0 J a bs H x Hx. apply wbytes_grows. apply H. exact Hx. Qed.







Section CMem.
  Variable sp0 : word.
  Variable mem0 : word -> option byte.

  Let csel := cmem sp0 mem0.

  Lemma stack_max_size_pos : 0 < stack_max_size.
  Proof. rewrite stack_max_size_val. lia. Qed.

  (* [comment removed for export] *)

  Lemma wbytes_cmem_win : forall J D (a : word) bs,
    win_lo sp0 <= bv_unsigned a ->
    bv_unsigned a + Z.of_nat (length bs) <= bv_unsigned sp0 ->
    wbytes (cmem sp0 mem0 J D) a bs = cmem sp0 mem0 (wbytes J a bs) D.
  Proof.
    intros J D a bs Hlo Hhi. unfold cmem.
    pose proof (u64_range sp0) as Hsp.
    rewrite (wbytes_select_r (fun x => bv_unsigned sp0 <=? bv_unsigned x) mem0
               (fun x => if win_lo sp0 <=? bv_unsigned x then J x else D x) a bs)
      by (first [lia | intros x Hx; apply Z.leb_gt; lia]).
    apply functional_extensionality. intro x.
    destruct (bv_unsigned sp0 <=? bv_unsigned x); [reflexivity|].
    rewrite (wbytes_select (fun x => win_lo sp0 <=? bv_unsigned x) J D a bs)
      by (first [lia | intros y Hy; apply Z.leb_le; lia]).
    reflexivity.
  Qed.

  Lemma wbytes_cmem_data : forall J D (a : word) bs,
    bv_unsigned a + Z.of_nat (length bs) <= win_lo sp0 ->
    wbytes (cmem sp0 mem0 J D) a bs = cmem sp0 mem0 J (wbytes D a bs).
  Proof.
    intros J D a bs Hhi. unfold cmem.
    pose proof (u64_range sp0) as Hsp. pose proof stack_max_size_pos.
    unfold win_lo in *.
    rewrite (wbytes_select_r (fun x => bv_unsigned sp0 <=? bv_unsigned x) mem0
               (fun x => if bv_unsigned sp0 - stack_max_size <=? bv_unsigned x then J x else D x) a bs)
      by (first [lia | intros x Hx; apply Z.leb_gt; lia]).
    apply functional_extensionality. intro x.
    destruct (bv_unsigned sp0 <=? bv_unsigned x); [reflexivity|].
    rewrite (wbytes_select_r (fun x => bv_unsigned sp0 - stack_max_size <=? bv_unsigned x) J D a bs)
      by (first [lia | intros y Hy; apply Z.leb_gt; lia]).
    reflexivity.
  Qed.

  (* [comment removed for export] *)

  Lemma rdn_cmem_above : forall segs J D (a : word) n,
    bv_unsigned sp0 <= bv_unsigned a ->
    bv_unsigned a + Z.of_nat n <= 2^64 ->
    rdn segs (cmem sp0 mem0 J D) a n = rdn segs mem0 a n.
  Proof.
    intros segs J D a n Hlo Hnw. apply rdn_ext; [exact Hnw|].
    intros x Hx. unfold cmem. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity.
  Qed.

  Lemma rdn_cmem_win : forall segs J D (a : word) n,
    win_lo sp0 <= bv_unsigned a ->
    bv_unsigned a + Z.of_nat n <= bv_unsigned sp0 ->
    rdn segs (cmem sp0 mem0 J D) a n = rdn segs J a n.
  Proof.
    intros segs J D a n Hlo Hhi. pose proof (u64_range sp0).
    apply rdn_ext; [lia|].
    intros x Hx. unfold cmem.
    rewrite (proj2 (Z.leb_gt _ _)) by lia.
    rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity.
  Qed.

  Lemma rdn_cmem_data : forall segs J D (a : word) n,
    bv_unsigned a + Z.of_nat n <= win_lo sp0 ->
    rdn segs (cmem sp0 mem0 J D) a n = rdn segs D a n.
  Proof.
    intros segs J D a n Hhi. pose proof (u64_range sp0). pose proof stack_max_size_pos.
    unfold win_lo in *.
    apply rdn_ext; [lia|].
    intros x Hx. unfold cmem, win_lo.
    rewrite (proj2 (Z.leb_gt _ _)) by lia.
    rewrite (proj2 (Z.leb_gt _ _)) by lia. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma cmem_at_above : forall J D (x : word),
    bv_unsigned sp0 <= bv_unsigned x -> cmem sp0 mem0 J D x = mem0 x.
  Proof. intros. unfold cmem. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity. Qed.

  Lemma cmem_at_win : forall J D (x : word),
    in_win sp0 x -> cmem sp0 mem0 J D x = J x.
  Proof.
    intros J D x [Hlo Hhi]. unfold cmem.
    rewrite (proj2 (Z.leb_gt _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity.
  Qed.

  Lemma cmem_at_data : forall J D (x : word),
    bv_unsigned x < win_lo sp0 -> cmem sp0 mem0 J D x = D x.
  Proof.
    intros J D x Hx. pose proof stack_max_size_pos. unfold cmem, win_lo in *.
    rewrite (proj2 (Z.leb_gt _ _)) by lia. rewrite (proj2 (Z.leb_gt _ _)) by lia. reflexivity.
  Qed.

  (* [comment removed for export] *)

  Lemma store_ok_cmem_win : forall segs J D (a : word) n,
    wfJ sp0 J ->
    win_lo sp0 <= bv_unsigned a ->
    bv_unsigned a + Z.of_nat n <= bv_unsigned sp0 ->
    store_ok segs (cmem sp0 mem0 J D) a n = true.
  Proof.
    intros segs J D a n HJ Hlo Hhi. pose proof (u64_range sp0).
    apply store_ok_of_all; [lia|].
    intros x Hx. unfold wview.
    rewrite cmem_at_win by (unfold in_win; lia).
    destruct (J x) as [b|] eqn:E; [discriminate|].
    exfalso. apply (HJ x); [unfold in_win; lia | exact E].
  Qed.

  Lemma store_ok_cmem_data : forall segs J D (a : word) n,
    wseg_ok segs a n = true ->
    store_ok segs (cmem sp0 mem0 J D) a n = true.
  Proof. intros. apply store_ok_wseg. assumption. Qed.

End CMem.

(* [comment removed for export] *)
Lemma cmem_init : forall ph (sp0 : word) av ev uid hw (rdraw : EntryDraw),
  wrap_mem ph sp0 av ev uid hw rdraw
  = cmem sp0 (wrap_mem ph sp0 av ev uid hw rdraw) (fun _ => Some (Z_to_bv 8 0)) (fun _ => None).
Proof.
  intros ph sp0 av ev uid hw rdraw. apply functional_extensionality. intro x.
  unfold cmem.
  destruct (bv_unsigned sp0 <=? bv_unsigned x) eqn:E1; [reflexivity|].
  apply Z.leb_gt in E1.
  unfold wrap_mem, win_lo.
  assert (Hst : stack_to_mem sp0 (entry_stack_image ph sp0 av ev uid hw rdraw) x = None).
  { unfold stack_to_mem. rewrite (proj2 (Z.leb_gt _ _)) by lia. reflexivity. }
  rewrite Hst. rewrite (proj2 (Z.ltb_lt _ _) E1), andb_true_r. reflexivity.
Qed.
End MemSplit.
Require Stdlib.NArith.NArith LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs OSSVerify.Proofs.glaze.binary_reflection.lib.PuLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module MuslStrlen.
(* [comment removed for export] *)

Import Stdlib.NArith.NArith Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac.

#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac lia ::= PuLia.lia_nd.
#[local] Ltac nia ::= PuLia.znia_nd.

Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Module HZ.
Local Open Scope Z_scope.


(* [comment removed for export] *)
Definition zb (x : Z) (i : nat) : Z := (x / 2^(8 * Z.of_nat i)) mod 256.

Fixpoint zdig (ds : list Z) : Z :=
  match ds with [] => 0 | d :: r => d + 256 * zdig r end.

Lemma pow2_8i_pos : forall i : nat, 0 < 2^(8 * Z.of_nat i).
Proof. intro i. apply Z.pow_pos_nonneg; lia. Qed.

Lemma zb_bound : forall x i, 0 <= zb x i < 256.
Proof. intros. unfold zb. apply Z.mod_pos_bound. lia. Qed.

Lemma zb_0 : forall i, zb 0 i = 0.
Proof. intro i. unfold zb. rewrite Zdiv_0_l. reflexivity. Qed.

(* [comment removed for export] *)

Lemma land_land_m : forall a b m, Z.land (Z.land a b) m = Z.land (Z.land a m) (Z.land b m).
Proof.
  intros. apply Z.bits_inj'. intros n Hn.
  rewrite !Z.land_spec.
  destruct (Z.testbit a n), (Z.testbit b n), (Z.testbit m n); reflexivity.
Qed.

Lemma land_lxor_m : forall a b m, Z.land (Z.lxor a b) m = Z.lxor (Z.land a m) (Z.land b m).
Proof.
  intros. apply Z.bits_inj'. intros n Hn.
  rewrite Z.land_spec, !Z.lxor_spec, !Z.land_spec.
  destruct (Z.testbit a n), (Z.testbit b n), (Z.testbit m n); reflexivity.
Qed.


Lemma zb_alt : forall x i, zb x i = Z.land (Z.shiftr x (8 * Z.of_nat i)) 255.
Proof.
  intros x i. unfold zb.
  rewrite Z.shiftr_div_pow2 by lia.
  change 255 with (Z.ones 8).
  rewrite Z.land_ones by lia. reflexivity.
Qed.

Lemma zb_land : forall u w i, zb (Z.land u w) i = Z.land (zb u i) (zb w i).
Proof.
  intros u w i. rewrite !zb_alt.
  rewrite Z.shiftr_land, land_land_m. reflexivity.
Qed.

Lemma zb_lxor : forall u w i, zb (Z.lxor u w) i = Z.lxor (zb u i) (zb w i).
Proof.
  intros u w i. rewrite !zb_alt.
  rewrite Z.shiftr_lxor, land_lxor_m. reflexivity.
Qed.

(* [comment removed for export] *)

Lemma zdig_nonneg : forall ds, Forall (fun d => 0 <= d < 256) ds -> 0 <= zdig ds.
Proof.
  induction ds as [|d ds IH]; intro H; cbn [zdig]; [lia|].
  apply Forall_cons_iff in H as [Hd Hds]; cbv beta in Hd.
  specialize (IH Hds). lia.
Qed.

Lemma zdig_lt : forall ds, Forall (fun d => 0 <= d < 256) ds ->
  zdig ds < 2^(8 * Z.of_nat (length ds)).
Proof.
  induction ds as [|d ds IH]; intro H; cbn [zdig length].
  - cbn. lia.
  - apply Forall_cons_iff in H as [Hd Hds]; cbv beta in Hd.
    specialize (IH Hds).
    replace (8 * Z.of_nat (S (length ds))) with (8 + 8 * Z.of_nat (length ds)) by lia.
    rewrite Z.pow_add_r by lia. change (2^8) with 256. lia.
Qed.

Lemma zb_zdig : forall ds, Forall (fun d => 0 <= d < 256) ds ->
  forall i, (i < length ds)%nat -> zb (zdig ds) i = nth i ds 0.
Proof.
  induction ds as [|d ds IH]; intros H i Hi; [cbn in Hi; lia|].
  apply Forall_cons_iff in H as [Hd Hds]; cbv beta in Hd.
  pose proof (zdig_nonneg ds Hds) as Hnn.
  destruct i as [|i]; cbn [nth].
  - cbn [zdig]. unfold zb.
    change (8 * Z.of_nat 0) with 0. change (2^0) with 1.
    rewrite Z.div_1_r.
    replace (d + 256 * zdig ds) with (d + zdig ds * 256) by lia.
    rewrite Z.mod_add by lia.
    apply Z.mod_small. lia.
  - cbn [length] in Hi.
    rewrite <- (IH Hds i ltac:(lia)).
    cbn [zdig]. unfold zb.
    replace (8 * Z.of_nat (S i)) with (8 + 8 * Z.of_nat i) by lia.
    rewrite Z.pow_add_r by lia. change (2^8) with 256.
    rewrite <- Z.div_div by (try lia; apply pow2_8i_pos).
    replace ((d + 256 * zdig ds) / 256) with (zdig ds); [reflexivity|].
    replace (d + 256 * zdig ds) with (zdig ds * 256 + d) by lia.
    rewrite Z.div_add_l by lia.
    rewrite (Z.div_small d 256) by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma zdig_recon8 : forall x, 0 <= x < 2^64 ->
  x = zdig [zb x 0; zb x 1; zb x 2; zb x 3; zb x 4; zb x 5; zb x 6; zb x 7].
Proof.
  intros x Hx. cbn [zdig]. unfold zb.
  change (8 * Z.of_nat 0) with 0. change (8 * Z.of_nat 1) with 8.
  change (8 * Z.of_nat 2) with 16. change (8 * Z.of_nat 3) with 24.
  change (8 * Z.of_nat 4) with 32. change (8 * Z.of_nat 5) with 40.
  change (8 * Z.of_nat 6) with 48. change (8 * Z.of_nat 7) with 56.
  change (2^0) with 1. rewrite Z.div_1_r.
  change (2^8) with 256.
  change (2^16) with (256*256).
  change (2^24) with (256*256*256).
  change (2^32) with (256*256*256*256).
  change (2^40) with (256*256*256*256*256).
  change (2^48) with (256*256*256*256*256*256).
  change (2^56) with (256*256*256*256*256*256*256).
  rewrite <- !Z.div_div by lia.
  pose proof (Z.div_mod x 256 ltac:(lia)).
  pose proof (Z.div_mod (x/256) 256 ltac:(lia)).
  pose proof (Z.div_mod (x/256/256) 256 ltac:(lia)).
  pose proof (Z.div_mod (x/256/256/256) 256 ltac:(lia)).
  pose proof (Z.div_mod (x/256/256/256/256) 256 ltac:(lia)).
  pose proof (Z.div_mod (x/256/256/256/256/256) 256 ltac:(lia)).
  pose proof (Z.div_mod (x/256/256/256/256/256/256) 256 ltac:(lia)).
  pose proof (Z.div_mod (x/256/256/256/256/256/256/256) 256 ltac:(lia)).
  assert (Htop : x/256/256/256/256/256/256/256/256 = 0).
  { rewrite !Z.div_div by lia. apply Z.div_small. lia. }
  lia.
Qed.

Lemma zb_eq0 : forall x, 0 <= x < 2^64 ->
  (forall i, (i < 8)%nat -> zb x i = 0) -> x = 0.
Proof.
  intros x Hx H. rewrite (zdig_recon8 x Hx).
  rewrite !H by lia. cbn [zdig]. lia.
Qed.

Lemma zb_neq0 : forall x i, zb x i <> 0 -> x <> 0.
Proof. intros x i H Hc. subst. rewrite zb_0 in H. lia. Qed.

(* [comment removed for export] *)

Lemma zb_split : forall lo hi i,
  0 <= lo < 2^(8 * Z.of_nat i) -> 0 <= hi ->
  zb (lo + 2^(8 * Z.of_nat i) * hi) i = hi mod 256.
Proof.
  intros lo hi i Hlo Hhi. unfold zb.
  rewrite Z.mul_comm, Z.div_add by (pose proof (pow2_8i_pos i); lia).
  rewrite (Z.div_small lo) by lia. reflexivity.
Qed.

Lemma zb_mod64 : forall y i, (i < 8)%nat -> 0 <= y < 2^65 ->
  zb (y mod 2^64) i = zb y i.
Proof.
  intros y i Hi Hy.
  destruct (Z_lt_le_dec y (2^64)) as [Hlt|Hge].
  - rewrite Z.mod_small by lia. reflexivity.
  - assert (Hm : y mod 2^64 = y - 2^64).
    { replace y with ((y - 2^64) + 1 * 2^64) at 1 by lia.
      rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
    rewrite Hm. unfold zb.
    pose proof (pow2_8i_pos i) as Hk.
    assert (Hd : 2^64 = 2^(64 - 8 * Z.of_nat i) * 2^(8 * Z.of_nat i)).
    { rewrite <- Z.pow_add_r by lia. f_equal. lia. }
    assert (Hdiv : (256 | 2^(64 - 8 * Z.of_nat i))).
    { replace (64 - 8 * Z.of_nat i) with (8 + (56 - 8 * Z.of_nat i)) by lia.
      rewrite Z.pow_add_r by lia. change (2^8) with 256.
      apply Z.divide_factor_l. }
    destruct Hdiv as [q Hq].
    replace (y - 2^64) with (y + (- (q * 256)) * 2^(8 * Z.of_nat i))
      by (rewrite Hd, Hq; lia).
    rewrite Z.div_add by lia.
    replace (y / 2 ^ (8 * Z.of_nat i) + - (q * 256))
      with (y / 2 ^ (8 * Z.of_nat i) + (- q) * 256) by lia.
    rewrite Z.mod_add by lia. reflexivity.
Qed.

(* [comment removed for export] *)

Definition ONESNEG : Z := 18374403900871474943.   (* [comment removed for export] *)
Definition HIGHS   : Z := 9259542123273814144.    (* [comment removed for export] *)
Definition ALLONES : Z := 18446744073709551615.   (* [comment removed for export] *)

Definition Tz (x : Z) : Z :=
  Z.land (Z.land ((x + ONESNEG) mod 2^64) (Z.lxor x ALLONES)) HIGHS.

Lemma land_le_r : forall a b, 0 <= b -> Z.land a b <= b.
Proof.
  intros a b Hb.
  rewrite Z.land_comm.
  pose proof (Z.sub_land_same_l b a) as H.
  assert (0 <= Z.land b (Z.lnot a)) by (apply Z.land_nonneg; left; lia).
  lia.
Qed.


Lemma Tz_range : forall x, 0 <= Tz x < 2^64.
Proof.
  intro x. unfold Tz. split.
  - apply Z.land_nonneg. right. unfold HIGHS. lia.
  - pose proof (land_le_r (Z.land ((x + ONESNEG) mod 2^64) (Z.lxor x ALLONES)) HIGHS
                  ltac:(unfold HIGHS; lia)). unfold HIGHS in *. lia.
Qed.

Ltac by8 i := destruct i as [|[|[|[|[|[|[|[|i]]]]]]]]; try lia; vm_compute; reflexivity.

Lemma zb_ALLONES : forall i, (i < 8)%nat -> zb ALLONES i = 255.
Proof. intros i Hi. by8 i. Qed.

Lemma zb_HIGHS : forall i, (i < 8)%nat -> zb HIGHS i = 128.
Proof. intros i Hi. by8 i. Qed.

Lemma Tz_byte : forall x i, (i < 8)%nat ->
  zb (Tz x) i
  = Z.land (Z.land (zb ((x + ONESNEG) mod 2^64) i) (Z.lxor (zb x i) 255)) 128.
Proof.
  intros x i Hi. unfold Tz.
  rewrite !zb_land, zb_lxor, zb_ALLONES by exact Hi.
  rewrite zb_HIGHS by exact Hi. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma byte_nozero : forall c, 1 <= c <= 255 ->
  Z.land (Z.land (c - 1) (Z.lxor c 255)) 128 = 0.
Proof.
  intros c Hc.
  assert (Hin : In (Z.to_nat c) (seq 1 255)) by (apply in_seq; lia).
  assert (Hall : forallb (fun n =>
      Z.eqb (Z.land (Z.land (Z.of_nat n - 1) (Z.lxor (Z.of_nat n) 255)) 128) 0)
      (seq 1 255) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in Hall. specialize (Hall _ Hin).
  apply Z.eqb_eq in Hall.
  replace (Z.of_nat (Z.to_nat c)) with c in Hall by lia. exact Hall.
Qed.

(* [comment removed for export] *)
Lemma Tz_nozero : forall x, 0 <= x < 2^64 ->
  (forall i, (i < 8)%nat -> zb x i <> 0) -> Tz x = 0.
Proof.
  intros x Hx Hnz.
  pose proof (zb_bound x 0). pose proof (zb_bound x 1). pose proof (zb_bound x 2).
  pose proof (zb_bound x 3). pose proof (zb_bound x 4). pose proof (zb_bound x 5).
  pose proof (zb_bound x 6). pose proof (zb_bound x 7).
  pose proof (Hnz 0%nat ltac:(lia)). pose proof (Hnz 1%nat ltac:(lia)).
  pose proof (Hnz 2%nat ltac:(lia)). pose proof (Hnz 3%nat ltac:(lia)).
  pose proof (Hnz 4%nat ltac:(lia)). pose proof (Hnz 5%nat ltac:(lia)).
  pose proof (Hnz 6%nat ltac:(lia)). pose proof (Hnz 7%nat ltac:(lia)).
  pose proof (zdig_recon8 x Hx) as Hrec.
  set (ds' := [zb x 0 - 1; zb x 1 - 1; zb x 2 - 1; zb x 3 - 1;
               zb x 4 - 1; zb x 5 - 1; zb x 6 - 1; zb x 7 - 1]).
  assert (Hds' : Forall (fun d => 0 <= d < 256) ds').
  { unfold ds'. repeat constructor; lia. }
  assert (Hlt' : 0 <= zdig ds' < 2^64).
  { split; [apply zdig_nonneg; exact Hds'|].
    pose proof (zdig_lt ds' Hds') as H'. unfold ds' in H' |- *.
    cbn [length] in H'. exact H'. }
  assert (Hy : (x + ONESNEG) mod 2^64 = zdig ds').
  { rewrite Hrec at 1.
    replace (zdig [zb x 0; zb x 1; zb x 2; zb x 3; zb x 4; zb x 5; zb x 6; zb x 7]
             + ONESNEG)
      with (zdig ds' + 1 * 2^64)
      by (unfold ds', ONESNEG; cbn [zdig]; lia).
    rewrite Z.mod_add by lia. apply Z.mod_small. exact Hlt'. }
  apply zb_eq0; [apply Tz_range|].
  intros i Hi. rewrite Tz_byte by exact Hi. rewrite Hy.
  rewrite (zb_zdig ds' Hds' i) by (unfold ds'; cbn [length]; lia).
  destruct i as [|[|[|[|[|[|[|[|i]]]]]]]]; try lia;
    unfold ds'; cbn [nth]; apply byte_nozero; lia.
Qed.

Lemma zb_split_255 : forall v lo Q i p,
  p = 2^(8 * Z.of_nat i) -> v = lo + p * (255 + 256 * Q) ->
  0 <= lo < p -> 0 <= Q -> zb v i = 255.
Proof.
  intros v lo Q i p Hp Hv Hlo HQ. subst p v.
  rewrite zb_split by (try lia; assumption).
  replace (255 + 256 * Q) with (255 + Q * 256) by lia.
  rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

(* [comment removed for export] *)
Lemma sum_byte_255 : forall x i, 0 <= x < 2^64 -> (i < 8)%nat -> zb x i = 0 ->
  (forall j, (j < i)%nat -> zb x j <> 0) ->
  zb (x + ONESNEG) i = 255.
Proof.
  intros x i Hx Hi Hz Hlow.
  pose proof (zb_bound x 0). pose proof (zb_bound x 1). pose proof (zb_bound x 2).
  pose proof (zb_bound x 3). pose proof (zb_bound x 4). pose proof (zb_bound x 5).
  pose proof (zb_bound x 6). pose proof (zb_bound x 7).
  pose proof (zdig_recon8 x Hx) as Hrec. cbn [zdig] in Hrec.
  unfold ONESNEG.
  destruct i as [|[|[|[|[|[|[|[|i]]]]]]]]; try lia.
  - (* [comment removed for export] *)
    apply (zb_split_255 _ (0) (zb x 1 * 1 + zb x 2 * 256 + zb x 3 * 65536 + zb x 4 * 16777216 + zb x 5 * 4294967296 + zb x 6 * 1099511627776 + zb x 7 * 281474976710656 + 71775015237779198) 0%nat 1);
      [ vm_compute; reflexivity | lia | lia | lia ].
  - (* [comment removed for export] *)
    pose proof (Hlow 0%nat ltac:(lia)).
    apply (zb_split_255 _ ((zb x 0 - 1) * 1) (zb x 2 * 1 + zb x 3 * 256 + zb x 4 * 65536 + zb x 5 * 16777216 + zb x 6 * 4294967296 + zb x 7 * 1099511627776 + 280371153272574) 1%nat 256);
      [ vm_compute; reflexivity | lia | lia | lia ].
  - (* [comment removed for export] *)
    pose proof (Hlow 0%nat ltac:(lia)).
    pose proof (Hlow 1%nat ltac:(lia)).
    apply (zb_split_255 _ ((zb x 0 - 1) * 1 + (zb x 1 - 1) * 256) (zb x 3 * 1 + zb x 4 * 256 + zb x 5 * 65536 + zb x 6 * 16777216 + zb x 7 * 4294967296 + 1095199817470) 2%nat 65536);
      [ vm_compute; reflexivity | lia | lia | lia ].
  - (* [comment removed for export] *)
    pose proof (Hlow 0%nat ltac:(lia)).
    pose proof (Hlow 1%nat ltac:(lia)).
    pose proof (Hlow 2%nat ltac:(lia)).
    apply (zb_split_255 _ ((zb x 0 - 1) * 1 + (zb x 1 - 1) * 256 + (zb x 2 - 1) * 65536) (zb x 4 * 1 + zb x 5 * 256 + zb x 6 * 65536 + zb x 7 * 16777216 + 4278124286) 3%nat 16777216);
      [ vm_compute; reflexivity | lia | lia | lia ].
  - (* [comment removed for export] *)
    pose proof (Hlow 0%nat ltac:(lia)).
    pose proof (Hlow 1%nat ltac:(lia)).
    pose proof (Hlow 2%nat ltac:(lia)).
    pose proof (Hlow 3%nat ltac:(lia)).
    apply (zb_split_255 _ ((zb x 0 - 1) * 1 + (zb x 1 - 1) * 256 + (zb x 2 - 1) * 65536 + (zb x 3 - 1) * 16777216) (zb x 5 * 1 + zb x 6 * 256 + zb x 7 * 65536 + 16711422) 4%nat 4294967296);
      [ vm_compute; reflexivity | lia | lia | lia ].
  - (* [comment removed for export] *)
    pose proof (Hlow 0%nat ltac:(lia)).
    pose proof (Hlow 1%nat ltac:(lia)).
    pose proof (Hlow 2%nat ltac:(lia)).
    pose proof (Hlow 3%nat ltac:(lia)).
    pose proof (Hlow 4%nat ltac:(lia)).
    apply (zb_split_255 _ ((zb x 0 - 1) * 1 + (zb x 1 - 1) * 256 + (zb x 2 - 1) * 65536 + (zb x 3 - 1) * 16777216 + (zb x 4 - 1) * 4294967296) (zb x 6 * 1 + zb x 7 * 256 + 65278) 5%nat 1099511627776);
      [ vm_compute; reflexivity | lia | lia | lia ].
  - (* [comment removed for export] *)
    pose proof (Hlow 0%nat ltac:(lia)).
    pose proof (Hlow 1%nat ltac:(lia)).
    pose proof (Hlow 2%nat ltac:(lia)).
    pose proof (Hlow 3%nat ltac:(lia)).
    pose proof (Hlow 4%nat ltac:(lia)).
    pose proof (Hlow 5%nat ltac:(lia)).
    apply (zb_split_255 _ ((zb x 0 - 1) * 1 + (zb x 1 - 1) * 256 + (zb x 2 - 1) * 65536 + (zb x 3 - 1) * 16777216 + (zb x 4 - 1) * 4294967296 + (zb x 5 - 1) * 1099511627776) (zb x 7 * 1 + 254) 6%nat 281474976710656);
      [ vm_compute; reflexivity | lia | lia | lia ].
  - (* [comment removed for export] *)
    pose proof (Hlow 0%nat ltac:(lia)).
    pose proof (Hlow 1%nat ltac:(lia)).
    pose proof (Hlow 2%nat ltac:(lia)).
    pose proof (Hlow 3%nat ltac:(lia)).
    pose proof (Hlow 4%nat ltac:(lia)).
    pose proof (Hlow 5%nat ltac:(lia)).
    pose proof (Hlow 6%nat ltac:(lia)).
    apply (zb_split_255 _ ((zb x 0 - 1) * 1 + (zb x 1 - 1) * 256 + (zb x 2 - 1) * 65536 + (zb x 3 - 1) * 16777216 + (zb x 4 - 1) * 4294967296 + (zb x 5 - 1) * 1099511627776 + (zb x 6 - 1) * 281474976710656) (0) 7%nat 72057594037927936);
      [ vm_compute; reflexivity | lia | lia | lia ].
Qed.


(* [comment removed for export] *)
Lemma Tz_haszero : forall x i, 0 <= x < 2^64 -> (i < 8)%nat -> zb x i = 0 ->
  (forall j, (j < i)%nat -> zb x j <> 0) -> Tz x <> 0.
Proof.
  intros x i Hx Hi Hz Hlow.
  apply (zb_neq0 _ i).
  rewrite Tz_byte by exact Hi.
  rewrite zb_mod64 by (first [exact Hi | unfold ONESNEG; lia]).
  rewrite (sum_byte_255 x i Hx Hi Hz Hlow), Hz.
  vm_compute. discriminate.
Qed.

End HZ.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma u8_zero : bv_unsigned (Z_to_bv 8 0) = 0%Z.
Proof. vm_compute. reflexivity. Qed.

Lemma lor_shiftl8 : forall a y : Z, (0 <= a < 256)%Z -> (0 <= y)%Z ->
  Z.lor a (Z.shiftl y 8) = (a + 256 * y)%Z.
Proof.
  intros a y Ha Hy.
  assert (Hs : Z.shiftl y 8 = (y * 2^8)%Z) by (apply Z.shiftl_mul_pow2; lia).
  assert (Hland : Z.land a (Z.shiftl y 8) = 0%Z).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.ltb n 8) eqn:E.
    - apply Z.ltb_lt in E.
      rewrite Hs, Z.mul_pow2_bits_low by lia. apply andb_false_r.
    - apply Z.ltb_ge in E.
      replace (Z.testbit a n) with false; [reflexivity|].
      symmetry. apply Z.testbit_false; [lia|].
      rewrite Z.div_small; [reflexivity|].
      split; [lia|]. eapply Z.lt_le_trans; [apply Ha|].
      change 256%Z with (2^8)%Z. apply Z.pow_le_mono_r; lia. }
  rewrite <- Z.lxor_lor by exact Hland.
  rewrite <- Z.add_nocarry_lxor by exact Hland.
  rewrite Hs. lia.
Qed.

Lemma bytes_le_to_Z_zdig : forall bs : list byte,
  bytes_le_to_Z bs = HZ.zdig (map bv_unsigned bs).
Proof.
  induction bs as [|b bs IH]; [reflexivity|].
  cbn [bytes_le_to_Z map HZ.zdig]. rewrite IH.
  apply lor_shiftl8; [apply u8_range|].
  apply HZ.zdig_nonneg. apply Forall_map, Forall_forall.
  intros x _. apply u8_range.
Qed.

Lemma zb_of_bytes : forall (bs : list byte) i, (i < length bs)%nat ->
  HZ.zb (bytes_le_to_Z bs) i = bv_unsigned (nth i bs (Z_to_bv 8 0)).
Proof.
  intros bs i Hi. rewrite bytes_le_to_Z_zdig.
  rewrite HZ.zb_zdig
    by (first [ apply Forall_map, Forall_forall; intros x _; apply u8_range
              | rewrite length_map; exact Hi ]).
  rewrite <- (map_nth bv_unsigned bs (Z_to_bv 8 0) i), u8_zero. reflexivity.
Qed.

Lemma bytes_le_to_Z_range : forall bs : list byte, length bs = 8%nat ->
  (0 <= bytes_le_to_Z bs < 2^64)%Z.
Proof.
  intros bs Hl. rewrite bytes_le_to_Z_zdig.
  assert (HF : Forall (fun d => (0 <= d < 256)%Z) (map bv_unsigned bs))
    by (apply Forall_map, Forall_forall; intros x _; apply u8_range).
  split; [apply HZ.zdig_nonneg; exact HF|].
  pose proof (HZ.zdig_lt _ HF) as H.
  rewrite length_map, Hl in H. exact H.
Qed.







(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section ArgvWord.

  Variable segs : list Segment.
  Variable ph : PhdrInfo.
  Variable sp : word.
  Variable av ev : list (list byte).
  Variable uid : word.
  Variable hw : word.

  (* [comment removed for export] *)
  Variable rnd : EntryDraw.

  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp ev.
  Hypothesis Hsp_lo : (sp_window_lo <= bv_unsigned sp)%Z.
  Hypothesis Hsp_hi : (bv_unsigned sp <= sp_window_hi)%Z.







End ArgvWord.
End MuslStrlen.
Require LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module RefMemcpyLib.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition sub {A} (bs : list A) (j k : nat) : list A := firstn k (skipn j bs).

Lemma firstn_add : forall {A} (l : list A) a b,
  firstn (a + b) l = firstn a l ++ firstn b (skipn a l).
Proof.
  intros A l a. revert l. induction a as [|a IH]; intros l b.
  - cbn. reflexivity.
  - destruct l as [|x l]; cbn.
    + destruct b; reflexivity.
    + rewrite IH. reflexivity.
Qed.

Lemma firstn_sub_app : forall {A} (bs : list A) j k,
  firstn j bs ++ sub bs j k = firstn (j + k) bs.
Proof. intros. unfold sub. rewrite firstn_add. reflexivity. Qed.

Lemma skipn_add : forall {A} (l : list A) a b, skipn (a + b) l = skipn b (skipn a l).
Proof.
  intros A l a. revert l. induction a as [|a IH]; intros l b; [reflexivity|].
  destruct l as [|x l]; cbn; [destruct b; reflexivity|]. apply IH.
Qed.

Lemma sub_length : forall {A} (bs : list A) j k,
  (j + k <= length bs)%nat -> length (sub bs j k) = k.
Proof.
  intros A bs j k H. unfold sub. rewrite length_firstn, length_skipn. lia.
Qed.

Lemma sub_split : forall {A} (bs : list A) j a b,
  sub bs j (a + b) = sub bs j a ++ sub bs (j + a) b.
Proof.
  intros A bs j a b. unfold sub. rewrite firstn_add. f_equal.
  rewrite <- skipn_add. f_equal; lia.
Qed.



Lemma sub_nth : forall (bs : list byte) j,
  (j < length bs)%nat -> sub bs j 1 = [nth j bs (Z_to_bv 8 0)].
Proof.
  intros bs j. revert bs. induction j as [|j IH]; intros bs H.
  - destruct bs; cbn in *; [lia|reflexivity].
  - destruct bs; cbn in *; [lia|]. unfold sub in IH. apply IH. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma at_succ : forall (a : word) d, (at_ a d + 1)%bv = at_ a (d + 1).
Proof.
  intros a d. unfold at_. apply bv_eq.
  rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_unsigned (1 : word)) with 1.
  rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.

Lemma word_succ_at : forall (a : word), (a + 1)%bv = at_ a 1.
Proof. intros a. rewrite <- (at_0 a) at 1. rewrite at_succ. reflexivity. Qed.

Lemma at_u : forall (a : word) d,
  0 <= bv_unsigned a + d -> bv_unsigned a + d < 2^64 ->
  bv_unsigned (at_ a d) = bv_unsigned a + d.
Proof. intros a d H1 H2. unfold at_. apply u_Z2bv; lia. Qed.

Lemma at_nat : forall (a : word) (j : nat), (a + nat_to_word j)%bv = at_ a (Z.of_nat j).
Proof.
  intros a j. unfold at_, nat_to_word. apply bv_eq.
  rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap.
  rewrite Zplus_mod_idemp_r. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma wbytes_app : forall bs1 bs2 m (a : word),
  wbytes m a (bs1 ++ bs2) = wbytes (wbytes m a bs1) (at_ a (Z.of_nat (length bs1))) bs2.
Proof.
  induction bs1 as [|b r IH]; intros bs2 m a.
  - cbn [app wbytes length Z.of_nat]. rewrite at_0. reflexivity.
  - cbn [app wbytes length]. rewrite IH. f_equal.
    rewrite word_succ_at, at_at. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma wbytes_extend : forall m (dst : word) bs j k,
  wbytes (wbytes m dst (firstn j bs)) (at_ dst (Z.of_nat j)) (sub bs j k)
  = wbytes m dst (firstn (j + k) bs) \/ (length bs < j)%nat.
Proof.
  intros m dst bs j k.
  destruct (Nat.le_gt_cases j (length bs)) as [H|H]; [left|right; exact H].
  rewrite <- firstn_sub_app, wbytes_app. rewrite length_firstn. f_equal. f_equal. f_equal. lia.
Qed.

Lemma wbytes_extend' : forall m (dst : word) bs j k,
  (j <= length bs)%nat ->
  wbytes (wbytes m dst (firstn j bs)) (at_ dst (Z.of_nat j)) (sub bs j k)
  = wbytes m dst (firstn (j + k) bs).
Proof.
  intros m dst bs j k H. destruct (wbytes_extend m dst bs j k) as [E|E]; [exact E|lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rdn_skipn : forall segs mem n (a : word) bs j,
  rdn segs mem a n = Some bs -> (j <= n)%nat ->
  rdn segs mem (at_ a (Z.of_nat j)) (n - j) = Some (skipn j bs).
Proof.
  intros segs mem n. induction n as [|n IH]; intros a bs j H Hj.
  - assert (j = 0)%nat by lia. subst j. cbn in H. injection H as <-.
    rewrite at_0. reflexivity.
  - cbn [rdn] in H.
    destruct (match mem a with Some b => Some b | None => seg_rom segs a end) as [b|] eqn:Eb; [|discriminate].
    destruct (rdn segs mem (a+1)%bv n) as [rest|] eqn:Er; [|discriminate].
    injection H as <-.
    destruct j as [|j].
    + rewrite at_0. cbn [Nat.sub skipn rdn]. rewrite Eb, Er. reflexivity.
    + cbn [skipn]. replace (S n - S j)%nat with (n - j)%nat by lia.
      replace (at_ a (Z.of_nat (S j))) with (at_ (a + 1)%bv (Z.of_nat j))
        by (rewrite word_succ_at, at_at; f_equal; lia).
      apply IH; [exact Er|lia].
Qed.

Lemma rdn_sub : forall segs mem n (a : word) bs j k,
  rdn segs mem a n = Some bs -> (j + k <= n)%nat ->
  rdn segs mem (at_ a (Z.of_nat j)) k = Some (sub bs j k).
Proof.
  intros segs mem n a bs j k H Hjk. unfold sub.
  apply (rdn_firstn segs mem (n - j)); [|lia].
  apply rdn_skipn; [exact H|lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Abbreviation lez := bytes_le_to_Z.

(* [comment removed for export] *)
Definition LWv (l : list byte) : word := v_lw (Z_to_bv 64 (lez l)).

Lemma lez_bound_len : forall bs k, length bs = k -> 0 <= lez bs < 2 ^ (8 * Z.of_nat k).
Proof. intros bs k <-. split; [apply bytes_le_to_Z_nonneg | apply bytes_le_to_Z_bound]. Qed.
Lemma lez4_range : forall l, length l = 4%nat -> 0 <= lez l < 2 ^ 32.
Proof. intros l H. pose proof (lez_bound_len l 4%nat H). change (8 * Z.of_nat 4) with 32 in H0. lia. Qed.
Lemma u_lez4 : forall l, length l = 4%nat -> bv_unsigned (Z_to_bv 64 (lez l)) = lez l.
Proof. intros l H. pose proof (lez4_range l H). apply u_Z2bv; lia. Qed.

Lemma testbit_u_LWv : forall l i, length l = 4%nat -> 0 <= i < 32 ->
  Z.testbit (bv_unsigned (LWv l)) i = Z.testbit (lez l) i.
Proof.
  intros l i H Hi. unfold LWv, v_lw. rewrite Z_to_bv_unsigned, u_lez4 by exact H.
  rewrite bv_wrap_spec_low by lia.
  rewrite bv_swrap_spec by lia.
  case_bool_decide; [reflexivity|].
  replace i with 31 by lia. reflexivity.
Qed.


Lemma lez_cons : forall b bs, lez (b :: bs) = Z.lor (bv_unsigned b) (Z.shiftl (lez bs) 8).
Proof. reflexivity. Qed.

Lemma testbit_lez_high : forall bs i, 8 * Z.of_nat (length bs) <= i -> Z.testbit (lez bs) i = false.
Proof.
  intros bs i Hi. apply (Z_testbit_high (8 * Z.of_nat (length bs))); try lia.
  apply lez_bound_len. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma testbit_lez_skipn : forall q bs i, 0 <= i ->
  Z.testbit (lez (skipn q bs)) i = Z.testbit (lez bs) (i + 8 * Z.of_nat q).
Proof.
  induction q as [|q IH]; intros bs i Hi.
  - cbn [skipn]. f_equal. lia.
  - destruct bs as [|b bs].
    + cbn [skipn lez]. rewrite !Z.bits_0. reflexivity.
    + cbn [skipn]. rewrite IH by lia. rewrite lez_cons.
      rewrite Z.lor_spec, Z.shiftl_spec by lia.
      pose proof (u8_range b).
      rewrite (Z_testbit_high 8 (bv_unsigned b)) by lia. cbn [orb]. f_equal. lia.
Qed.

Lemma testbit_lez_firstn : forall q bs i, 0 <= i ->
  Z.testbit (lez (firstn q bs)) i = if i <? 8 * Z.of_nat q then Z.testbit (lez bs) i else false.
Proof.
  induction q as [|q IH]; intros bs i Hi.
  - cbn [firstn lez]. rewrite Z.bits_0. destruct (Z.ltb_spec i (8 * Z.of_nat 0)); [lia|reflexivity].
  - destruct bs as [|b bs].
    + cbn [firstn lez]. rewrite !Z.bits_0. destruct (i <? _); reflexivity.
    + cbn [firstn]. rewrite !lez_cons, !Z.lor_spec, !Z.shiftl_spec by lia.
      destruct (Z.lt_ge_cases i 8) as [H8|H8].
      * rewrite !(Z.testbit_neg_r _ (i - 8)) by lia.
        destruct (Z.ltb_spec i (8 * Z.of_nat (S q))); [reflexivity|lia].
      * rewrite IH by lia.
        destruct (Z.ltb_spec (i - 8) (8 * Z.of_nat q)), (Z.ltb_spec i (8 * Z.of_nat (S q))); try lia; try reflexivity.
        pose proof (u8_range b). rewrite (Z_testbit_high 8 (bv_unsigned b)) by lia. reflexivity.
Qed.

Lemma testbit_lez_app : forall xs ys i, 0 <= i ->
  Z.testbit (lez (xs ++ ys)) i =
  if i <? 8 * Z.of_nat (length xs) then Z.testbit (lez xs) i else Z.testbit (lez ys) (i - 8 * Z.of_nat (length xs)).
Proof.
  intros xs ys i Hi. rewrite bytes_le_app, Z.lor_spec, Z.shiftl_spec by lia.
  destruct (Z.ltb_spec i (8 * Z.of_nat (length xs))).
  - rewrite (Z.testbit_neg_r (lez ys)) by lia. apply orb_false_r.
  - rewrite testbit_lez_high by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma Z_to_le_bytes_lez : forall bs, Z_to_le_bytes (length bs) (lez bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|].
  cbn [length Z_to_le_bytes].
  replace (Z.shiftr (lez (b :: bs)) 8) with (lez bs).
  2:{ apply Z.bits_inj'. intros i Hi. rewrite Z.shiftr_spec by lia.
      pose proof (testbit_lez_skipn 1 (b :: bs) i Hi) as E. change (skipn 1 (b :: bs)) with bs in E.
      rewrite E. reflexivity. }
  rewrite IH. f_equal.
  apply bv_eq. rewrite Z_to_bv_unsigned.
  apply Z.bits_inj'. intros i Hi. pose proof (u8_range b).
  destruct (Z.lt_ge_cases i 8).
  - rewrite bv_wrap_spec_low by lia. rewrite lez_cons, Z.lor_spec, Z.shiftl_spec by lia.
    rewrite (Z.testbit_neg_r _ (i - 8)) by lia. apply orb_false_r.
  - rewrite bv_wrap_spec_high by lia. symmetry. apply (Z_testbit_high 8); lia.
Qed.

Lemma word_to_le_bytes_4_eq : forall (v : word) (l : list byte),
  length l = 4%nat ->
  (forall i, 0 <= i < 32 -> Z.testbit (bv_unsigned v) i = Z.testbit (lez l) i) ->
  word_to_le_bytes 4 v = l.
Proof.
  intros v l Hl Hb. unfold word_to_le_bytes.
  rewrite <- (Z_to_le_bytes_wrap 4 32) by (cbn; lia).
  rewrite <- Hl at 1. rewrite <- (Z_to_le_bytes_lez l). rewrite Hl. f_equal.
  apply Z.bits_inj'. intros i Hi.
  destruct (Z.lt_ge_cases i 32).
  - rewrite bv_wrap_spec_low by lia. apply Hb. lia.
  - rewrite bv_wrap_spec_high by lia. symmetry. apply testbit_lez_high. rewrite Hl. cbn. lia.
Qed.

(* [comment removed for export] *)
Lemma sw_bytes_LWv : forall l, length l = 4%nat -> word_to_le_bytes 4 (LWv l) = l.
Proof.
  intros l H. apply word_to_le_bytes_4_eq; [exact H|]. intros i Hi. apply testbit_u_LWv; assumption.
Qed.

(* [comment removed for export] *)
Definition LBv (b : byte) : word := Z_to_bv 64 (bv_unsigned b).

Lemma sb_byte_LBv : forall b : byte, Z_to_bv 8 (bv_unsigned (LBv b)) = b.
Proof.
  intros b. unfold LBv. pose proof (u8_range b). rewrite u_Z2bv by lia.
  apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8) with 256. lia.
Qed.

(* [comment removed for export] *)
Lemma sb_byte_eq : forall (v : word) (b : byte),
  (forall i, 0 <= i < 8 -> Z.testbit (bv_unsigned v) i = Z.testbit (bv_unsigned b) i) ->
  Z_to_bv 8 (bv_unsigned v) = b.
Proof.
  intros v b Hb. apply bv_eq. rewrite Z_to_bv_unsigned.
  apply Z.bits_inj'. intros i Hi. pose proof (u8_range b).
  destruct (Z.lt_ge_cases i 8).
  - rewrite bv_wrap_spec_low by lia. apply Hb. lia.
  - rewrite bv_wrap_spec_high by lia. symmetry. apply (Z_testbit_high 8); lia.
Qed.

Lemma testbit_nth_lez : forall l q i, 0 <= i < 8 -> (q < length l)%nat ->
  Z.testbit (bv_unsigned (nth q l (Z_to_bv 8 0))) i = Z.testbit (lez l) (i + 8 * Z.of_nat q).
Proof.
  intros l q i Hi Hq. rewrite <- testbit_lez_skipn by lia.
  revert l Hq. induction q as [|q IH]; intros l Hq.
  - destruct l as [|b l]; [cbn in Hq; lia|]. cbn [nth skipn]. rewrite lez_cons.
    rewrite Z.lor_spec, Z.shiftl_spec, (Z.testbit_neg_r _ (i - 8)) by lia. symmetry. apply orb_false_r.
  - destruct l as [|b l]; [cbn in Hq; lia|]. cbn [nth skipn]. apply IH. cbn in Hq. lia.
Qed.

(* [comment removed for export] *)
Lemma sb_byte_srli_LWv : forall l q, length l = 4%nat -> (q <= 3)%nat ->
  Z_to_bv 8 (bv_unsigned (v_srli (LWv l) (8 * Z.of_nat q))) = nth q l (Z_to_bv 8 0).
Proof.
  intros l q H Hq. apply sb_byte_eq. intros i Hi.
  unfold v_srli. rewrite Z_to_bv_unsigned, bv_wrap_spec_low, Z.shiftr_spec by lia.
  rewrite testbit_u_LWv by (try exact H; lia).
  rewrite testbit_nth_lez by (try rewrite H; lia). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma testbit_u_srliw_LWv : forall l s i, length l = 4%nat -> 1 <= s -> 0 <= i ->
  Z.testbit (bv_unsigned (v_srliw (LWv l) s)) i = if i + s <? 32 then Z.testbit (lez l) (i + s) else false.
Proof.
  intros l s i H Hs Hi. unfold v_srliw. rewrite Z_to_bv_unsigned.
  assert (Sh : forall j, 0 <= j -> Z.testbit (Z.shiftr (bv_wrap 32 (bv_unsigned (LWv l))) s) j
                              = if j + s <? 32 then Z.testbit (lez l) (j + s) else false).
  { intros j Hj. rewrite Z.shiftr_spec by lia.
    destruct (Z.ltb_spec (j + s) 32).
    - rewrite bv_wrap_spec_low by lia. apply testbit_u_LWv; [exact H|lia].
    - apply bv_wrap_spec_high. lia. }
  destruct (Z.lt_ge_cases i 64).
  - rewrite bv_wrap_spec_low by lia. rewrite bv_swrap_spec by lia.
    case_bool_decide.
    + apply Sh. lia.
    + rewrite Sh by lia.
      destruct (Z.ltb_spec (Z.of_N 32 - 1 + s) 32), (Z.ltb_spec (i + s) 32); try lia; reflexivity.
  - rewrite bv_wrap_spec_high by lia. destruct (Z.ltb_spec (i + s) 32); [lia|reflexivity].
Qed.

(* [comment removed for export] *)
Lemma testbit_u_slli_LWv : forall l s i, length l = 4%nat -> 0 <= s -> 0 <= i < 32 ->
  Z.testbit (bv_unsigned (v_slli (LWv l) s)) i = if i <? s then false else Z.testbit (lez l) (i - s).
Proof.
  intros l s i H Hs Hi. unfold v_slli. rewrite Z_to_bv_unsigned.
  rewrite bv_wrap_spec_low by lia. rewrite Z.shiftl_spec by lia.
  destruct (Z.ltb_spec i s).
  - apply Z.testbit_neg_r. lia.
  - apply testbit_u_LWv; [exact H|lia].
Qed.

Lemma testbit_u_vor : forall (x y : word) i, 0 <= i ->
  Z.testbit (bv_unsigned (v_or x y)) i = Z.testbit (bv_unsigned x) i || Z.testbit (bv_unsigned y) i.
Proof.
  intros x y i Hi. unfold v_or. rewrite Z_to_bv_unsigned.
  destruct (Z.lt_ge_cases i 64).
  - rewrite bv_wrap_spec_low by lia. apply Z.lor_spec.
  - rewrite bv_wrap_spec_high by lia.
    pose proof (u64_range x). pose proof (u64_range y).
    rewrite (Z_testbit_high 64 (bv_unsigned x)) by lia. rewrite (Z_testbit_high 64 (bv_unsigned y)) by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma sw_bytes_merge : forall l1 l2 (q : nat) (v : word),
  length l1 = 4%nat -> length l2 = 4%nat -> (1 <= q <= 3)%nat ->
  v = v_or (v_slli (LWv l2) (32 - 8 * Z.of_nat q)) (v_srliw (LWv l1) (8 * Z.of_nat q)) ->
  word_to_le_bytes 4 v = skipn q l1 ++ firstn q l2.
Proof.
  intros l1 l2 q v H1 H2 Hq ->.
  apply word_to_le_bytes_4_eq.
  { rewrite length_app, length_skipn, length_firstn, H1, H2. lia. }
  intros i Hi.
  rewrite testbit_u_vor by lia.
  rewrite testbit_u_slli_LWv by (try exact H2; lia).
  rewrite testbit_u_srliw_LWv by (try exact H1; lia).
  rewrite testbit_lez_app by lia. rewrite length_skipn, H1.
  rewrite testbit_lez_skipn by lia.
  destruct (Z.ltb_spec i (32 - 8 * Z.of_nat q)), (Z.ltb_spec i (8 * Z.of_nat (4 - q))),
           (Z.ltb_spec (i + 8 * Z.of_nat q) 32); try lia.
  - reflexivity.
  - rewrite testbit_lez_firstn by lia.
    destruct (Z.ltb_spec (i - 8 * Z.of_nat (4 - q)) (8 * Z.of_nat q)); [|lia].
    rewrite orb_false_r. f_equal. lia.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma store_ok_at : forall segs m (dst : word) (N : nat) bsw j k,
  bv_unsigned dst + Z.of_nat N <= 2 ^ 64 ->
  store_ok segs m dst N = true ->
  0 <= j -> j + Z.of_nat k <= Z.of_nat N ->
  store_ok segs (wbytes m dst bsw) (at_ dst j) k = true.
Proof.
  intros segs m dst N bsw j k Hnw Hok Hj Hk.
  destruct k as [|k]; [reflexivity|].
  pose proof (u64_range dst).
  apply (store_ok_mono segs (S k) m); [apply wbytes_grows|].
  apply (store_ok_sub segs m dst (at_ dst j) N (S k) Hnw Hok); rewrite at_u; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition callee_kept : list reg :=
  [1; 2; 3; 4; 8; 9; 10; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

Definition keeps (regs regs' : bvmap 5 word) : Prop :=
  forall r : reg, In r callee_kept -> getr regs' r = getr regs r.

Lemma keeps_refl : forall regs, keeps regs regs.
Proof. intros regs r _. reflexivity. Qed.

Lemma keeps_trans : forall r1 r2 r3, keeps r1 r2 -> keeps r2 r3 -> keeps r1 r3.
Proof. intros r1 r2 r3 A B r Hr. rewrite (B r Hr). apply A, Hr. Qed.

(* [comment removed for export] *)
Lemma keeps_upd : forall regs regs' (rd : reg) v,
  keeps regs regs' -> ~ In rd callee_kept -> keeps regs (regupd regs' rd v).
Proof.
  intros regs regs' rd v K Hn r Hr.
  rewrite getr_other; [apply K, Hr|]. intros ->. exact (Hn Hr).
Qed.


Ltac kept_reg := cbv [callee_kept In]; intuition congruence.


(* [comment removed for export] *)
Lemma not_in_regs_lit : forall (r : reg) (l : list reg),
  existsb (fun x => bv_eqb x r) l = false -> ~ In r l.
Proof.
  intros r l H Hin.
  assert (E : existsb (fun x => bv_eqb x r) l = true)
    by (apply existsb_exists; exists r; split; [exact Hin | unfold bv_eqb; apply Z.eqb_refl]).
  rewrite E in H. discriminate H.
Qed.
Ltac not_kept_reg_lit r := lazymatch r with @BV _ ?z _ => lazymatch z with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end end.
Ltac not_kept :=
  first [ lazymatch goal with
          | |- ~ In ?r ?L => not_kept_reg_lit r; exact (not_in_regs_lit r L (@eq_refl bool false))
          end
        | cbv; intuition discriminate ].

(* [comment removed for export] *)
Ltac solve_keeps :=
  repeat (apply keeps_upd; [| not_kept]); first [apply keeps_refl | assumption].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma runs_trans : forall segs (s0 : machine_state)
    (st1 : bvmap 5 word -> machine_state) (P1 : bvmap 5 word -> Prop)
    (st2 : bvmap 5 word -> machine_state) (P2 : bvmap 5 word -> Prop),
  (exists r1, msteps segs s0 (st1 r1) /\ P1 r1) ->
  (forall r1, P1 r1 -> exists r2, msteps segs (st1 r1) (st2 r2) /\ P2 r2) ->
  exists r2, msteps segs s0 (st2 r2) /\ P2 r2.
Proof.
  intros segs s0 st1 P1 st2 P2 (r1 & R1 & H1) K.
  destruct (K r1 H1) as (r2 & R2 & H2).
  exists r2. split; [eapply msteps_trans; eassumption | exact H2].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition callee_saved : list reg :=
  [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

Definition keeps_cs (regs regs' : bvmap 5 word) : Prop :=
  forall r : reg, In r callee_saved -> getr regs' r = getr regs r.

Lemma keeps_cs_refl : forall regs, keeps_cs regs regs.
Proof. intros regs r _. reflexivity. Qed.

Lemma keeps_cs_trans : forall r1 r2 r3, keeps_cs r1 r2 -> keeps_cs r2 r3 -> keeps_cs r1 r3.
Proof. intros r1 r2 r3 A B r Hr. rewrite (B r Hr). apply A, Hr. Qed.

Lemma keeps_cs_upd : forall regs regs' (rd : reg) v,
  keeps_cs regs regs' -> ~ In rd callee_saved -> keeps_cs regs (regupd regs' rd v).
Proof.
  intros regs regs' rd v K Hn r Hr.
  rewrite getr_other; [apply K, Hr|]. intros ->. exact (Hn Hr).
Qed.

(* [comment removed for export] *)
Lemma keeps_cs_upd_same : forall regs regs' (rd : reg) v,
  keeps_cs regs regs' -> getr regs rd = v -> rd <> 0%bv -> keeps_cs regs (regupd regs' rd v).
Proof.
  intros regs regs' rd v K Hv Hnz r Hr.
  destruct (decide (r = rd)) as [->|Hne].
  - rewrite getr_same by exact Hnz. symmetry. exact Hv.
  - rewrite getr_other by exact Hne. apply K, Hr.
Qed.

Lemma keeps_keeps_cs : forall regs regs', keeps regs regs' -> keeps_cs regs regs'.
Proof.
  intros regs regs' K r Hr. apply K. unfold callee_saved, callee_kept in *. cbn [In] in *. intuition.
Qed.


Ltac solve_keeps_cs :=
  repeat (first [ apply keeps_cs_upd; [| not_kept]
                | apply keeps_cs_upd_same; [| solve [eauto | symmetry; eauto] | let X := fresh in intro X; discriminate X ] ]);
  first [apply keeps_cs_refl | assumption | apply keeps_keeps_cs; assumption].
End RefMemcpyLib.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim RefMemcpyLib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section FPGen1.
Context {fx : FPState}.

Definition ms_inb (i : Z) (iv : Z * Z) : bool := (fst iv <=? i) && (i <? fst iv + snd iv).
Definition ms_cov (L : list (Z * Z)) (i : Z) : bool := existsb (ms_inb i) L.

Lemma ms_inb_true : forall i o m, ms_inb i (o, m) = true <-> o <= i < o + m.
Proof.
  intros i o m. unfold ms_inb. cbn [fst snd]. rewrite andb_true_iff, Z.leb_le, Z.ltb_lt. tauto.
Qed.

Lemma ms_cov_cons : forall iv L i, ms_cov (iv :: L) i = ms_inb i iv || ms_cov L i.
Proof. reflexivity. Qed.


Lemma ms_cov_In : forall L i o m, In (o, m) L -> o <= i < o + m -> ms_cov L i = true.
Proof.
  intros L i o m Hin Hi. unfold ms_cov. apply existsb_exists. exists (o, m). split; [exact Hin|].
  apply ms_inb_true. exact Hi.
Qed.

(* [comment removed for export] *)
Fixpoint ms_chain (from to : Z) (L : list (Z * Z)) : Prop :=
  match L with
  | [] => to <= from
  | (o, m) :: L' => o <= from /\ ms_chain (o + m) to L'
  end.

Lemma ms_chain_cov : forall L from to i,
  ms_chain from to L -> from <= i < to -> exists o m, In (o, m) L /\ o <= i < o + m.
Proof.
  induction L as [|[o m] L IH]; intros from to i Hc Hi; cbn [ms_chain] in Hc.
  - lia.
  - destruct Hc as [Ho Hc].
    destruct (Z.lt_ge_cases i (o + m)) as [Hlt|Hge].
    + exists o, m. split; [left; reflexivity | lia].
    + destruct (IH (o + m) to i Hc ltac:(lia)) as (o' & m' & Hin & Hi').
      exists o', m'. split; [right; exact Hin | exact Hi'].
Qed.

(* [comment removed for export] *)
Lemma ms_cov_by_chain : forall (L L' : list (Z * Z)) n,
  incl L' L -> ms_chain 0 n L' -> forall i, 0 <= i < n -> ms_cov L i = true.
Proof.
  intros L L' n Hincl Hc i Hi.
  destruct (ms_chain_cov L' 0 n i Hc Hi) as (o & m & Hin & Hom).
  apply (ms_cov_In L i o m); [apply Hincl, Hin | exact Hom].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section CFill.
  Variable mem0 : word -> option byte.
  Variable d : word.
  Variable n : Z.
  Variable c : byte.
  Hypothesis Hn : 0 <= n.
  Hypothesis Hnw : bv_unsigned d + n < 2 ^ 64.

  Definition cfill (L : list (Z * Z)) : word -> option byte :=
    fun x => if (bv_unsigned d <=? bv_unsigned x) && (bv_unsigned x <? bv_unsigned d + n)
                && ms_cov L (bv_unsigned x - bv_unsigned d)
             then Some c else mem0 x.

  Lemma cfill_nil : cfill [] = mem0.
  Proof.
    apply functional_extensionality. intro x. unfold cfill. cbn [ms_cov existsb].
    rewrite andb_false_r. reflexivity.
  Qed.

  Lemma cfill_grows : forall L, mem_grows mem0 (cfill L).
  Proof.
    intros L x Hx. unfold cfill. destruct (_ && _); [discriminate | exact Hx].
  Qed.

  (* [comment removed for export] *)
  Lemma cfill_ext : forall L1 L2,
    (forall i, 0 <= i < n -> ms_cov L1 i = ms_cov L2 i) -> cfill L1 = cfill L2.
  Proof.
    intros L1 L2 H. apply functional_extensionality. intro x. unfold cfill.
    destruct (Z.leb_spec (bv_unsigned d) (bv_unsigned x)); [|reflexivity].
    destruct (Z.ltb_spec (bv_unsigned x) (bv_unsigned d + n)); [|reflexivity].
    cbn [andb]. rewrite H by lia. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma cfill_store : forall L o (m : nat),
    0 <= o -> o + Z.of_nat m <= n ->
    wbytes (cfill L) (at_ d o) (repeat c m) = cfill ((o, Z.of_nat m) :: L).
  Proof.
    intros L o m Ho Hm. apply functional_extensionality. intro x.
    pose proof (u64_range d). pose proof (u64_range x).
    assert (Ha : bv_unsigned (at_ d o) = bv_unsigned d + o) by (apply at_u; lia).
    destruct (Z.lt_ge_cases (bv_unsigned x) (bv_unsigned d + o)) as [Hlo|Hge];
      [| destruct (Z.lt_ge_cases (bv_unsigned x) (bv_unsigned d + o + Z.of_nat m)) as [Hin|Hhi]].
    - rewrite wbytes_outside by (rewrite repeat_length, Ha; lia).
      unfold cfill. rewrite ms_cov_cons.
      replace (ms_inb (bv_unsigned x - bv_unsigned d) (o, Z.of_nat m)) with false
        by (symmetry; apply not_true_iff_false; rewrite ms_inb_true; lia).
      reflexivity.
    - rewrite wbytes_inside by (rewrite repeat_length, Ha; lia).
      rewrite nth_repeat_lt by (rewrite Ha; lia). unfold cfill. rewrite ms_cov_cons.
      replace (ms_inb (bv_unsigned x - bv_unsigned d) (o, Z.of_nat m)) with true
        by (symmetry; apply ms_inb_true; lia).
      destruct (Z.leb_spec (bv_unsigned d) (bv_unsigned x)); [|lia].
      destruct (Z.ltb_spec (bv_unsigned x) (bv_unsigned d + n)); [|lia].
      reflexivity.
    - rewrite wbytes_outside by (rewrite repeat_length, Ha; lia).
      unfold cfill. rewrite ms_cov_cons.
      replace (ms_inb (bv_unsigned x - bv_unsigned d) (o, Z.of_nat m)) with false
        by (symmetry; apply not_true_iff_false; rewrite ms_inb_true; lia).
      reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma cfill_full : forall L,
    (forall i, 0 <= i < n -> ms_cov L i = true) ->
    cfill L = wbytes mem0 d (repeat c (Z.to_nat n)).
  Proof.
    intros L Hcov. apply functional_extensionality. intro x.
    pose proof (u64_range d). pose proof (u64_range x).
    unfold cfill.
    destruct (Z.leb_spec (bv_unsigned d) (bv_unsigned x)) as [H1|H1].
    - destruct (Z.ltb_spec (bv_unsigned x) (bv_unsigned d + n)) as [H2|H2]; cbn [andb].
      + rewrite Hcov by lia. rewrite wbytes_inside by (rewrite repeat_length; lia).
        rewrite nth_repeat_lt by lia. reflexivity.
      + rewrite wbytes_outside by (rewrite repeat_length; lia). reflexivity.
    - cbn [andb]. rewrite wbytes_outside by (rewrite repeat_length; lia). reflexivity.
  Qed.

  Lemma cfill_full_chain : forall L L',
    incl L' L -> ms_chain 0 n L' ->
    cfill L = wbytes mem0 d (repeat c (Z.to_nat n)).
  Proof. intros L L' Hi Hc. apply cfill_full. apply (ms_cov_by_chain L L'); assumption. Qed.

  (* [comment removed for export] *)
  Lemma cfill_store_ok : forall segs L o (m : nat),
    store_ok segs mem0 d (Z.to_nat n) = true ->
    0 <= o -> o + Z.of_nat m <= n ->
    store_ok segs (cfill L) (at_ d o) m = true.
  Proof.
    intros segs L o m Hok Ho Hm. pose proof (u64_range d).
    apply (store_ok_mono segs m mem0); [apply cfill_grows|].
    apply (store_ok_sub segs mem0 d (at_ d o) (Z.to_nat n) m); try (rewrite ?at_u; lia). exact Hok.
  Qed.
End CFill.


(* [comment removed for export] *)
Definition cbyte (cv : word) : byte := Z_to_bv 8 (bv_unsigned cv).
(* [comment removed for export] *)
Definition cbz (cv : word) : Z := bv_unsigned cv mod 256.
(* [comment removed for export] *)
Definition c32 (cv : word) : word := Z_to_bv 64 (cbz cv * 16843009).
(* [comment removed for export] *)
Definition c32h (cv : word) : word := Z_to_bv 64 (cbz cv * 16843009 * 2 ^ 32).
(* [comment removed for export] *)
Definition c64 (cv : word) : word := Z_to_bv 64 (cbz cv * 72340172838076673).

Lemma cbz_range : forall cv, 0 <= cbz cv < 256.
Proof. intros cv. unfold cbz. apply Z.mod_pos_bound. lia. Qed.

Lemma cbyte_mod : forall cv, Z_to_bv 8 (bv_unsigned cv mod 256) = cbyte cv.
Proof.
  intros cv. unfold cbyte. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap8_mod. apply Z.mod_mod. lia.
Qed.

Lemma cbyte_cbz : forall cv, cbyte cv = Z_to_bv 8 (cbz cv).
Proof. intros cv. unfold cbz. symmetry. apply cbyte_mod. Qed.


(* [comment removed for export] *)
Fixpoint ms_repl (k : nat) : Z := match k with O => 0 | S k' => 1 + 256 * ms_repl k' end.

Lemma ms_repl_nonneg : forall k, 0 <= ms_repl k.
Proof. induction k; cbn [ms_repl]; lia. Qed.

Lemma Z_to_le_bytes_ms_repl : forall k z, 0 <= z < 256 ->
  Z_to_le_bytes k (z * ms_repl k) = repeat (Z_to_bv 8 z) k.
Proof.
  induction k as [|k IH]; intros z Hz; [reflexivity|].
  cbn [Z_to_le_bytes ms_repl repeat]. pose proof (ms_repl_nonneg k). f_equal.
  - apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap8_mod.
    replace (z * (1 + 256 * ms_repl k)) with (z + (z * ms_repl k) * 256) by lia.
    rewrite Z.mod_add by lia. reflexivity.
  - rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
    replace (z * (1 + 256 * ms_repl k)) with (z + (z * ms_repl k) * 256) by lia.
    rewrite Z.div_add by lia. rewrite Z.div_small by lia. rewrite Z.add_0_l. apply IH. exact Hz.
Qed.

Lemma u_c32 : forall cv, bv_unsigned (c32 cv) = cbz cv * 16843009.
Proof. intros cv. pose proof (cbz_range cv). unfold c32. apply u_Z2bv; lia. Qed.

Lemma u_c32h : forall cv, bv_unsigned (c32h cv) = cbz cv * 16843009 * 2 ^ 32.
Proof. intros cv. pose proof (cbz_range cv). unfold c32h. apply u_Z2bv; lia. Qed.

Lemma u_c64 : forall cv, bv_unsigned (c64 cv) = cbz cv * 72340172838076673.
Proof. intros cv. pose proof (cbz_range cv). unfold c64. apply u_Z2bv; lia. Qed.

Lemma wleb4_c32 : forall cv, word_to_le_bytes 4 (c32 cv) = repeat (cbyte cv) 4.
Proof.
  intros cv. unfold word_to_le_bytes. rewrite u_c32, cbyte_cbz.
  change 16843009 with (ms_repl 4). apply Z_to_le_bytes_ms_repl. apply cbz_range.
Qed.

Lemma wleb8_c64 : forall cv, word_to_le_bytes 8 (c64 cv) = repeat (cbyte cv) 8.
Proof.
  intros cv. unfold word_to_le_bytes. rewrite u_c64, cbyte_cbz.
  change 72340172838076673 with (ms_repl 8). apply Z_to_le_bytes_ms_repl. apply cbz_range.
Qed.

(* [comment removed for export] *)
Lemma u_slli56 : forall cv, bv_unsigned (v_slli cv 56) = cbz cv * 2 ^ 56.
Proof.
  intros cv. unfold v_slli, cbz. rewrite Z_to_bv_unsigned, Z.shiftl_mul_pow2 by lia.
  pose proof (u64_range cv).
  unfold bv_wrap. change (bv_modulus 64) with (2 ^ 56 * 256).
  rewrite Z.mul_comm, Z.mul_mod_distr_l by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma mulhu_c32 : forall cv (m : word), bv_unsigned m = 4311810304 ->
  v_mulhu (v_slli cv 56) m = c32 cv.
Proof.
  intros cv m Hm. unfold v_mulhu, c32. f_equal. rewrite u_slli56, Hm.
  rewrite Z.shiftr_div_pow2 by lia.
  replace (cbz cv * 2 ^ 56 * 4311810304) with ((cbz cv * 16843009) * 2 ^ 64) by lia.
  apply Z.div_mul. lia.
Qed.

Lemma slli32_c32 : forall cv, v_slli (c32 cv) 32 = c32h cv.
Proof.
  intros cv. unfold v_slli, c32h. f_equal. rewrite u_c32, Z.shiftl_mul_pow2 by lia. reflexivity.
Qed.

Lemma srli32_c32h : forall cv, v_srli (c32h cv) 32 = c32 cv.
Proof.
  intros cv. unfold v_srli, c32. f_equal. rewrite u_c32h, Z.shiftr_div_pow2 by lia.
  apply Z.div_mul. lia.
Qed.

Lemma lor_disjoint_shift32 : forall a b, 0 <= a -> 0 <= b < 2 ^ 32 ->
  Z.lor (a * 2 ^ 32) b = a * 2 ^ 32 + b.
Proof.
  intros a b Ha Hb.
  assert (Hl : Z.land (a * 2 ^ 32) b = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i 32).
    - rewrite <- Z.shiftl_mul_pow2, Z.shiftl_spec by lia. rewrite (Z.testbit_neg_r a) by lia. reflexivity.
    - rewrite (Z_testbit_high 32 b) by lia. apply andb_false_r. }
  rewrite <- Z.lxor_lor by exact Hl. symmetry. apply Z.add_nocarry_lxor. exact Hl.
Qed.

Lemma or_c64 : forall cv, v_or (c32h cv) (c32 cv) = c64 cv.
Proof.
  intros cv. pose proof (cbz_range cv). unfold v_or, c64. f_equal. rewrite u_c32h, u_c32.
  rewrite lor_disjoint_shift32 by lia. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma mod4_mod_pow2' : forall t k, 2 <= k -> (t mod 2 ^ k) mod 4 = t mod 4.
Proof.
  intros t k Hk. apply Z.mod_mod_divide.
  exists (2 ^ (k - 2)). change 4 with (2 ^ 2). rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma negw_and3 : forall x : word,
  v_andi (v_subw (Z_to_bv 64 0) x) 3 = Z_to_bv 64 ((- bv_unsigned x) mod 4).
Proof.
  intros x. unfold v_andi, v_subw. f_equal.
  change (bv_wrap 64 3) with (Z.ones 2). rewrite Z.land_ones by lia.
  rewrite Z_to_bv_unsigned. change (bv_unsigned (Z_to_bv 64 0)) with 0.
  unfold bv_swrap. rewrite bv_wrap64_mod.
  change (bv_half_modulus 32) with (2 ^ 31).
  unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32). change (2 ^ 2) with 4.
  rewrite mod4_mod_pow2' by lia.
  rewrite <- Zminus_mod_idemp_l.
  rewrite mod4_mod_pow2' by lia.
  replace (0 - bv_unsigned x + 2 ^ 31) with ((- bv_unsigned x) + 536870912 * 4) by lia.
  rewrite Z.mod_add by lia.
  rewrite Zminus_mod_idemp_l.
  replace (- bv_unsigned x - 2 ^ 31) with ((- bv_unsigned x) + (- 536870912) * 4) by lia.
  rewrite Z.mod_add by lia. reflexivity.
Qed.

Lemma neg_mod4_range : forall u, 0 <= (- u) mod 4 <= 3.
Proof. intros u. pose proof (Z.mod_pos_bound (- u) 4). lia. Qed.


(* [comment removed for export] *)
Lemma land_trunc4 : forall a, 0 <= a < 2 ^ 64 -> Z.land a (2 ^ 64 - 4) = a - a mod 4.
Proof.
  intros a Ha.
  replace (2 ^ 64 - 4) with (Z.ldiff (Z.ones 64) (Z.ones 2)).
  2:{ rewrite Z.ldiff_land, <- Z.sub_land_same_l, Z.land_ones by lia.
      rewrite Z.ones_mod_pow2 by lia. rewrite !Z.ones_equiv. lia. }
  rewrite Z.ldiff_land, Z.land_assoc, Z.land_ones by lia.
  rewrite Z.mod_small by lia.
  rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia.
  rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
  pose proof (Z.div_mod a 4 ltac:(lia)). lia.
Qed.

Lemma andi_m4 : forall m, 0 <= m < 2 ^ 64 ->
  v_andi (Z_to_bv 64 m) (-4) = Z_to_bv 64 (m - m mod 4).
Proof.
  intros m Hm. unfold v_andi. f_equal. rewrite u_Z2bv by lia.
  change (bv_wrap 64 (-4)) with (2 ^ 64 - 4). apply land_trunc4. exact Hm.
Qed.

(* [comment removed for export] *)
Lemma land_4_cases : forall a, 0 <= a -> Z.land a 4 = 0 \/ Z.land a 4 = 4.
Proof.
  intros a Ha.
  destruct (Z.testbit a 2) eqn:E; [right|left];
    apply Z.bits_inj'; intros i Hi; rewrite Z.land_spec;
    change 4 with (2 ^ 2); rewrite Z.pow2_bits_eqb by lia;
    destruct (Z.eqb_spec 2 i) as [<-|Hne]; rewrite ?E, ?Z.bits_0; try reflexivity;
    apply andb_false_r.
Qed.

Lemma andi_4_cases : forall x : word, exists s4, v_andi x 4 = Z_to_bv 64 s4 /\ (s4 = 0 \/ s4 = 4).
Proof.
  intros x. exists (Z.land (bv_unsigned x) 4). split.
  - unfold v_andi. f_equal.
  - apply land_4_cases. apply u64_range.
Qed.

(* [comment removed for export] *)
Lemma ms_v_add_Z : forall (x : word) z, 0 <= z < 2 ^ 64 ->
  v_add x (Z_to_bv 64 z) = at_ x z.
Proof. intros x z Hz. unfold v_add, at_. rewrite u_Z2bv by lia. reflexivity. Qed.

Lemma ms_v_add_at_Z : forall (x : word) o z, 0 <= z < 2 ^ 64 ->
  v_add (at_ x o) (Z_to_bv 64 z) = at_ x (o + z).
Proof. intros x o z Hz. rewrite ms_v_add_Z by lia. apply at_at. Qed.

Lemma ms_v_sub_ZZ : forall a b, 0 <= b <= a -> a < 2 ^ 64 ->
  v_sub (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a - b).
Proof. intros a b H1 H2. unfold v_sub. rewrite !u_Z2bv by lia. reflexivity. Qed.

Lemma ms_v_addi_Z : forall a i, 0 <= a < 2 ^ 64 ->
  v_addi (Z_to_bv 64 a) i = Z_to_bv 64 (a + i).
Proof. intros a i Ha. unfold v_addi. rewrite u_Z2bv by lia. reflexivity. Qed.


Lemma ms_step_mulhu_at : forall segs regs pc mem rom w rd rs1 rs2 v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Mul M_MULHU rd rs1 rs2, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_mulhu (getr regs rs1) (getr regs rs2) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs1 rs2 v Hf He Hd Hrd Hv.
  rewrite (step_mulhu segs regs pc mem rom w rd rs1 rs2 Hf He Hd). rewrite Hrd, Hv. reflexivity.
Qed.

Lemma ms_step_or_at : forall segs regs pc mem rom w rd rs1 rs2 v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Op ALU_OR rd rs1 rs2, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_or (getr regs rs1) (getr regs rs2) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs1 rs2 v Hf He Hd Hrd Hv.
  rewrite (step_or segs regs pc mem rom w rd rs1 rs2 Hf He Hd). rewrite Hrd, Hv. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Stores.
  Variable segs : list Segment.
  Variable mem0 : word -> option byte.
  Variable d : word.
  Variable n : Z.
  Variable cv : word.
  Hypothesis Hn : 0 <= n.
  Hypothesis Hnw : bv_unsigned d + n < 2 ^ 64.
  Hypothesis Hok : store_ok segs mem0 d (Z.to_nat n) = true.

  #[local] Abbreviation CF := (cfill mem0 d n (cbyte cv)).

  Lemma cf_sb : forall regs pc rom w rs1 rs2 (imm : bv 12) L o0 o,
    fetch_word segs pc = Some w -> is_ecall w = false ->
    decode_any w = Some (Store SZ1 rs1 rs2 imm, 4%Z) ->
    getr regs rs1 = at_ d o0 -> (o0 + bv_signed imm = o)%Z ->
    getr regs rs2 = cv ->
    0 <= o -> o + 1 <= n ->
    RiscvSemantics.step segs (mkst regs pc (CF L) rom) =
    MachineOk (mkst regs (v_addi pc 4) (CF ((o, 1) :: L)) rom).
  Proof.
    intros regs pc rom w rs1 rs2 imm L o0 o Hf He Hdc Hrs1 Ho Hrs2 H0 H1.
    replace ((o, 1) :: L) with ((o, Z.of_nat 1) :: L) by reflexivity.
    rewrite <- (cfill_store mem0 d n (cbyte cv) Hnw L o 1) by lia.
    eapply step_sb_at; [exact Hf | exact He | exact Hdc | | exact Hrs2 | reflexivity |].
    - rewrite Hrs1, at_addi, Ho. reflexivity.
    - apply (cfill_store_ok mem0 d n (cbyte cv) Hnw segs); assumption || lia.
  Qed.

  Lemma cf_sw : forall regs pc rom w rs1 rs2 (imm : bv 12) L o0 o v,
    fetch_word segs pc = Some w -> is_ecall w = false ->
    decode_any w = Some (Store SZ4 rs1 rs2 imm, 4%Z) ->
    getr regs rs1 = at_ d o0 -> (o0 + bv_signed imm = o)%Z ->
    getr regs rs2 = v -> word_to_le_bytes 4 v = repeat (cbyte cv) 4 ->
    0 <= o -> o + 4 <= n ->
    RiscvSemantics.step segs (mkst regs pc (CF L) rom) =
    MachineOk (mkst regs (v_addi pc 4) (CF ((o, 4) :: L)) rom).
  Proof.
    intros regs pc rom w rs1 rs2 imm L o0 o v Hf He Hdc Hrs1 Ho Hrs2 Hv H0 H1.
    replace ((o, 4) :: L) with ((o, Z.of_nat 4) :: L) by reflexivity.
    rewrite <- (cfill_store mem0 d n (cbyte cv) Hnw L o 4) by lia.
    rewrite <- Hv.
    eapply step_sw_at; [exact Hf | exact He | exact Hdc | | exact Hrs2 |].
    - rewrite Hrs1, at_addi, Ho. reflexivity.
    - apply (cfill_store_ok mem0 d n (cbyte cv) Hnw segs); assumption || lia.
  Qed.

  Lemma cf_sd : forall regs pc rom w rs1 rs2 (imm : bv 12) L o0 o v,
    fetch_word segs pc = Some w -> is_ecall w = false ->
    decode_any w = Some (Store SZ8 rs1 rs2 imm, 4%Z) ->
    getr regs rs1 = at_ d o0 -> (o0 + bv_signed imm = o)%Z ->
    getr regs rs2 = v -> word_to_le_bytes 8 v = repeat (cbyte cv) 8 ->
    0 <= o -> o + 8 <= n ->
    RiscvSemantics.step segs (mkst regs pc (CF L) rom) =
    MachineOk (mkst regs (v_addi pc 4) (CF ((o, 8) :: L)) rom).
  Proof.
    intros regs pc rom w rs1 rs2 imm L o0 o v Hf He Hdc Hrs1 Ho Hrs2 Hv H0 H1.
    replace ((o, 8) :: L) with ((o, Z.of_nat 8) :: L) by reflexivity.
    rewrite <- (cfill_store mem0 d n (cbyte cv) Hnw L o 8) by lia.
    rewrite <- Hv.
    eapply step_sd_at; [exact Hf | exact He | exact Hdc | | exact Hrs2 |].
    - rewrite Hrs1, at_addi, Ho. reflexivity.
    - apply (cfill_store_ok mem0 d n (cbyte cv) Hnw segs); assumption || lia.
  Qed.
End Stores.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ms_clob : list reg := [11; 12; 13; 14; 15; 16]%bv.
Definition ms_agree (regs regs' : bvmap 5 word) : Prop :=
  regs_agree (fun r => In r ms_clob) regs regs'.

Lemma ms_agree_refl : forall regs, ms_agree regs regs.
Proof. intros regs. apply regs_agree_refl. Qed.

Lemma ms_agree_trans : forall r1 r2 r3, ms_agree r1 r2 -> ms_agree r2 r3 -> ms_agree r1 r3.
Proof. intros r1 r2 r3. apply regs_agree_trans. Qed.

Lemma ms_agree_upd : forall regs regs' (rd : reg) v,
  ms_agree regs regs' -> In rd ms_clob -> ms_agree regs (regupd regs' rd v).
Proof. intros regs regs' rd v H Hin. apply regs_agree_upd; assumption. Qed.


Lemma ms_agree_keeps : forall regs regs', ms_agree regs regs' -> keeps regs regs'.
Proof.
  intros regs regs' H r Hr. apply H. unfold callee_kept in Hr. unfold ms_clob. cbn [In] in *.
  intros Hc. decompose [or] Hr; subst; decompose [or] Hc; try discriminate; auto.
Qed.
End FPGen1.


Ltac in_clob := cbn [ms_clob In]; repeat first [ left; reflexivity | right ].
Ltac solve_ms_agree :=
  repeat (apply ms_agree_upd; [| in_clob]); first [apply ms_agree_refl | assumption].
