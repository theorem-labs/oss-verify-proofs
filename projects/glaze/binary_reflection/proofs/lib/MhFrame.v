(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.glaze.binary_reflection.images Require Import Plain.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhInv OSSVerify.Proofs.glaze.binary_reflection.lib.MhTac. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhInv OSSVerify.Proofs.glaze.binary_reflection.lib.MhTac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition agree_on (P : Z -> Prop) (M M' : mem) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> P a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a).

Lemma agree_on_mono : forall (P Q : Z -> Prop) M M',
  agree_on P M M' -> (forall a, Q a -> P a) -> agree_on Q M M'.
Proof. intros P Q M M' H HQ a Hr Ha. apply H; [exact Hr | apply HQ, Ha]. Qed.

Section Cells.
  Context {RN : mh_run}.
  Context {fx : FPState}.

  Lemma u64_lit : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
  Proof. intros z Hz. apply Z_to_bv_small. unfold bv_modulus. lia. Qed.

  Lemma cell_agree : forall M M' a n v,
    0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
    agree_on (fun x => a <= x < a + Z.of_nat n) M M' ->
    cell M a n v -> cell M' a n v.
  Proof.
    intros M M' a n v Ha Hnw Hag Hc. unfold cell in *. rewrite <- Hc.
    destruct n as [|n']; [reflexivity|].
    apply rdn_ext; [rewrite u64_lit by lia; lia|].
    intros x Hx. rewrite u64_lit in Hx by lia.
    pose proof (u64_range x).
    replace x with (Z_to_bv 64 (bv_unsigned x)) by (apply bv_eq; rewrite u64_lit by lia; reflexivity).
    apply Hag; lia.
  Qed.

  Lemma byte_agree : forall M M' a b,
    0 <= a < 2 ^ 64 -> agree_on (fun x => x = a) M M' -> byte_at M a b -> byte_at M' a b.
  Proof. intros M M' a b Hr Hag Hb. unfold byte_at in *. rewrite Hag by (exact Hr || reflexivity). exact Hb. Qed.

  Lemma defined_grows : forall M M' lo hi, mem_grows M M' -> defined M lo hi -> defined M' lo hi.
  Proof. intros M M' lo hi G D i Hi. apply G. apply D. exact Hi. Qed.

  Lemma img_clear_agree : forall M M' lo hi,
    0 <= lo -> hi <= 2 ^ 64 ->
    agree_on (fun x => lo <= x < hi) M M' -> img_clear M lo hi -> img_clear M' lo hi.
  Proof. intros M M' lo hi Hlo Hhi Hag Hc i Hi. rewrite Hag by (lia || exact Hi). apply Hc. exact Hi. Qed.

  (* [comment removed for export] *)
  Lemma agree_of_writes : forall (Wr P : Z -> Prop) M M',
    (forall a, 0 <= a < 2 ^ 64 -> M' (Z_to_bv 64 a) <> M (Z_to_bv 64 a) -> Wr a) ->
    (forall a, P a -> Wr a -> False) ->
    agree_on P M M'.
  Proof.
    intros Wr P M M' HW HP a Hr Ha.
    destruct (decide (M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))) as [E|NE]; [exact E|].
    exfalso. exact (HP a Ha (HW a Hr NE)).
  Qed.




  (* [comment removed for export] *)
  Lemma rep_meta_agree : forall M M' a r,
    0 <= a -> a + 40 < 2 ^ 64 ->
    agree_on (fun x => a <= x < a + 40) M M' -> rep_meta M a r -> rep_meta M' a r.
  Proof.
    intros M M' a r Ha Hnw Hag [P N Me Av Fr W].
    constructor; (eapply cell_agree; [ | | | eassumption]); try (cbn; lia);
      (eapply agree_on_mono; [exact Hag|]); cbn; intros; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma rep_meta_set_freed : forall M M' a r fr',
    0 <= a -> a + 40 < 2 ^ 64 ->
    agree_on (fun x => (a <= x < a + 28) \/ (a + 32 <= x < a + 40)) M M' ->
    cell M' (a + 28) 4 fr' ->
    rep_meta M a r -> rep_meta M' a (MR (mr_prev r) (mr_next r) (mr_mem r) (mr_avail r) fr' (mr_W r)).
  Proof.
    intros M M' a r fr' Ha Hnw Hag Hfr [P N Me Av Fr W].
    constructor; cbn; try exact Hfr; (eapply cell_agree; [ | | | eassumption]); try (cbn; lia);
      (eapply agree_on_mono; [exact Hag|]); cbn; intros; lia.
  Qed.
End Cells.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition set_slot (st : mst) (m i : Z) (s : slot_st) : mst :=
  MST (s_ctx st) (s_areas st) (s_meta st) (s_flist st) (s_alist st) (s_groups st) (s_ai st) (s_kind st)
      (fun m' k => if (Z.eqb m' m && Z.eqb k i)%bool then s else s_slot st m' k)
      (s_regions st) (s_brk st) (s_canary st) (s_errno st) (s_limbo st).

Definition set_meta (st : mst) (m : Z) (r : meta_rec) : mst :=
  MST (s_ctx st) (s_areas st) (fupd (s_meta st) m r) (s_flist st) (s_alist st) (s_groups st) (s_ai st) (s_kind st)
      (s_slot st) (s_regions st) (s_brk st) (s_canary st) (s_errno st) (s_limbo st).

Definition mr_set_freed (r : meta_rec) (fr : Z) : meta_rec :=
  MR (mr_prev r) (mr_next r) (mr_mem r) (mr_avail r) fr (mr_W r).
Definition mr_set_avail (r : meta_rec) (av : Z) : meta_rec :=
  MR (mr_prev r) (mr_next r) (mr_mem r) av (mr_freed r) (mr_W r).

Lemma s_slot_set_slot : forall st m i s m' k,
  s_slot (set_slot st m i s) m' k = if (Z.eqb m' m && Z.eqb k i)%bool then s else s_slot st m' k.
Proof. reflexivity. Qed.




(* [comment removed for export] *)
Section GeomStable.
  Context {RN : mh_run}.
  Variables (st : mst) (m : Z) (r : meta_rec).
  Hypothesis Hmem : mr_mem r = mr_mem (s_meta st m).
  Hypothesis HW : mr_W r = mr_W (s_meta st m).
  Let st' := set_meta st m r.










End GeomStable.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section RepGroupTransport.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (st1 st2 : mst) (M1 M2 : mem) (x : Z).
  (* [comment removed for export] *)
  Hypothesis Emem : g_mem st2 x = g_mem st1 x.
  Hypothesis Ecnt : g_cnt st2 x = g_cnt st1 x.
  Hypothesis Elast : g_lastidx st2 x = g_lastidx st1 x.
  Hypothesis Ess : forall k, g_slot_start st2 x k = g_slot_start st1 x k.
  Hypothesis Ese : forall k, g_slot_end st2 x k = g_slot_end st1 x k.
  Hypothesis Eai : s_ai st2 x = s_ai st1 x.
  Hypothesis Einb : forall q, inband st2 x q = inband st1 x q.
  Hypothesis Eend : endb_own st2 x -> endb_own st1 x.
  Hypothesis Ekind : match s_kind st2 x with GTop => s_kind st1 x = GTop /\ g_maplen st2 x = g_maplen st1 x | GNest _ _ _ => True end.
  (* [comment removed for export] *)
  Hypothesis Eslot : forall k, 0 <= k <= g_lastidx st1 x ->
    s_slot st2 x k = s_slot st1 x k \/ s_slot st2 x k = SAvail \/ s_slot st2 x k = SFreed.
  (* [comment removed for export] *)
  Hypothesis Agree : forall a, gcell st2 x a -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a).
  Hypothesis Grow : mem_grows M1 M2.
  (* [comment removed for export] *)
  Hypothesis Rng : 0 <= g_mem st1 x /\ g_mem st1 x + 16 <= g_span_end st1 x /\ g_span_end st1 x < 2 ^ 64.
  Hypothesis Cells1 : forall a, gcell st2 x a -> g_mem st1 x <= a < g_span_end st1 x.

  Lemma CR : forall a, gcell st2 x a -> 0 <= a < 2 ^ 64.
  Proof. intros a G. pose proof (Cells1 a G). lia. Qed.

  Lemma byte_tr : forall a b, gcell st2 x a -> byte_at M1 a b -> byte_at M2 a b.
  Proof. intros a b G B. unfold byte_at in *. rewrite (Agree a G). exact B. Qed.

  Lemma cell_tr : forall a n v, (forall y, a <= y < a + Z.of_nat n -> gcell st2 x y) -> (0 < Z.of_nat n) ->
    cell M1 a n v -> cell M2 a n v.
  Proof.
    intros a n v G Hn C.
    pose proof (CR a (G a ltac:(lia))). pose proof (CR (a + Z.of_nat n - 1) (G (a + Z.of_nat n - 1) ltac:(lia))).
    eapply cell_agree; [lia | lia | | exact C]. intros y Hy Hr. apply Agree. apply G. exact Hr.
  Qed.

  Lemma rep_hdr_transport : forall k q rc,
    0 <= k <= g_lastidx st1 x -> slot_ptr st2 x k = Some q ->
    rep_hdr st1 M1 x k q rc -> rep_hdr st2 M2 x k q rc.
  Proof.
    intros k q rc Hk Hq [A B C].
    assert (G : forall a, q - 4 <= a < q -> gcell st2 x a).
    { intros a Ha. unfold gcell. right. right. left. exists k, q. rewrite Elast. repeat split; try lia. exact Hq. }
    constructor.
    - apply byte_tr; [apply G; lia | exact A].
    - apply byte_tr; [apply G; lia | exact B].
    - rewrite Einb. apply cell_tr; [cbn; intros y Hy; apply G; lia | cbn; lia | exact C].
  Qed.

  Lemma rep_group_transport : rep_group st1 M1 x -> rep_group st2 M2 x.
  Proof.
    intros [Hm Hai Hh Hd Hs].
    assert (Gh : forall a, g_mem st1 x <= a < g_mem st1 x + 12 -> gcell st2 x a) by (intros a Ha; unfold gcell; left; rewrite Emem; exact Ha).
    constructor.
    - rewrite Emem. apply cell_tr; [cbn; intros y Hy; apply Gh; lia | cbn; lia | exact Hm].
    - rewrite Emem, Eai. destruct Hai as (b & Hb & Hba & Hmod). exists b. split; [exact Hb|]. split; [|exact Hmod].
      apply byte_tr; [apply Gh; lia | exact Hba].
    - intros k Hk Hend. rewrite Ess. rewrite Ecnt in Hk, Hend.
      assert (G : gcell st2 x (g_slot_start st1 x k - 4)).
      { unfold gcell. right. left. exists k. rewrite Ecnt, Ess. repeat split; try lia.
        destruct Hend as [H|H]; [left; exact H | right; exact H]. }
      apply byte_tr; [exact G|].
      apply Hh; [exact Hk|]. destruct Hend as [H|H]; [left; exact H | right; apply Eend; exact H].
    - destruct (s_kind st2 x); [|exact I]. destruct Ekind as [K E]. rewrite K in Hd. rewrite Emem, E.
      eapply defined_grows; [exact Grow | exact Hd].
    - intros k Hk. rewrite Elast in Hk.
      destruct (Eslot k Hk) as [E | [E | E]]; rewrite E; [|exact I|exact I].
      pose proof (Hs k Hk) as RS. destruct (s_slot st1 x k) as [| |q n o r|c o|o] eqn:Sk; cbn [rep_slot] in *; try exact I.
      + destruct RS as (RH & Rz & R5).
        assert (Hq : slot_ptr st2 x k = Some q) by (unfold slot_ptr; rewrite E; reflexivity).
        assert (Gf : forall a, ((0 < r /\ a = q + n) \/ (5 <= r /\ g_slot_end st1 x k - 5 <= a < g_slot_end st1 x k)) -> gcell st2 x a).
        { intros a Ha. unfold gcell. right. right. right. exists k, q, n, o, r. rewrite Elast, Ese. split; [lia|]. split; [exact E | exact Ha]. }
        split; [exact (rep_hdr_transport k q _ Hk Hq RH)|]. split.
        * intros Hr. apply byte_tr; [apply Gf; left; lia | exact (Rz Hr)].
        * intros Hr. destruct (R5 Hr) as [C B]. rewrite Ese. split.
          -- apply cell_tr; [cbn; intros y Hy; apply Gf; right; lia | cbn; lia | exact C].
          -- apply byte_tr; [apply Gf; right; lia | exact B].
      + destruct RS as (rc & Hrc & RH). exists rc. split; [exact Hrc|]. rewrite Ess.
        apply (rep_hdr_transport k _ rc Hk); [|exact RH]. unfold slot_ptr. rewrite E, Ess. reflexivity.
  Qed.
End RepGroupTransport.
