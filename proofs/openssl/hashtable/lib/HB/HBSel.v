(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.openssl.hashtable.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import PropExec ShapeAlg AgentLib AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanNodesIO AsanInit.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import CxRel CxPlan CxPlanSound CxGlue CxBatch.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import HBPlanImage HBAtable HBArg HBCheckG HBChain HBHop HBBatch HBFam2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import CAP. Import CXS.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition LV : nat := 574%nat.                       (* [comment removed for export] *)
Definition e_cl : expr := ION.CFGX 32.
Definition e_n : expr := ION.XROOM 32 (EVar LV).
Definition e_cm : expr := ION.XCM 32.
Definition e_b1s : expr := ION.XB1S 32.
Definition MAXS : Z := 9223372036854775807.
Definition cl_of (E : env) : Z := uE E e_cl.
Definition nb_of (E : env) : Z := Z.of_nat (length (eb E 32%nat)) - 6 - cl_of E.
Definition calls_of (E : env) : nat := if cl_of E =? 0 then 1%nat else Z.to_nat (uE E e_cm + 1).
Definition cnt_of (E : env) : bool := negb (uE E e_b1s <=? MAXS).

(* [comment removed for export] *)
Definition line_of (neg : bool) : list Z * list Z := if neg then ([45; 49], [10]) else ([48], [10]).
Definition lineZ (neg : bool) : list Z := fst (line_of neg) ++ snd (line_of neg).
Fixpoint rep (l : list Z) (j : nat) : list Z := match j with O => [] | S j' => l ++ rep l j' end.
Definition shapeB_of (vk : nat) (neg : bool) : shape :=
  SEmitP 1 [SPLit (fst (line_of neg)); SPLit (snd (line_of neg))]
    (SCase (EVar vk) 1 (SHole 1) (SCase (EVar vk) 2 (SHole 2) (SCase (EVar vk) 3 (SHole 3) (SHole 4)))).
Definition sC2s_can : list shape := SNil :: map (fun _ : nat => SCase e_b1s MAXS (SHole 0) (SHole 1)) [1; 2; 3; 4]%nat.
Definition sx_of (neg : bool) (j : nat) (ex : Z) : shape :=
  match j with 1%nat => SExit ex | _ => SEmitP 1 [SPLit (rep (lineZ neg) (j - 1))] (SExit ex) end.
(* [comment removed for export] *)
Definition sXs_of (neg : bool) : list (list shape) := [] :: map (fun j => [sx_of neg j 0; sx_of neg j 0]) [1; 2; 3; 4]%nat.

Definition W1 (bs : list Z) : list event := map (WriteEv (Z_to_bv 64 1)) (map (Z_to_bv 8) bs).
Definition TGT (neg : bool) (calls : nat) (cnt : bool) (fs : Fs.Fs) : TSet :=
  t_emit (W1 (lineZ neg)) (t_emit (W1 (rep (lineZ neg) (calls - 1))) (t_exit (Z_to_bv 64 0) fs))   (* [comment removed for export] *).

Lemma den_tgt : forall vk neg E fs calls,
  (1 <= calls <= 4)%nat -> uE E (EVar vk) = Z.of_nat calls ->
  t_eq (DEN (shapeB_of vk neg) sC2s_can (sXs_of neg) E fs) (TGT neg calls (cnt_of E) fs).
Proof.
  intros vk neg E fs calls Hc Hk. unfold DEN, shapeB_of, TGT. cbn [sd].
  assert (HW : Wp E 1 [SPLit (fst (line_of neg)); SPLit (snd (line_of neg))] = W1 (lineZ neg)).
  { unfold Wp, W1, lineZ. cbn [flat_map piece_den]. rewrite app_nil_r, !map_app. reflexivity. }
  rewrite HW. apply t_emit_congr.
  assert (Hhole : forall j, (1 <= j <= 4)%nat ->
            t_eq (HOLES_C sC2s_can (sXs_of neg) j E fs)
                 (t_emit (W1 (rep (lineZ neg) (j - 1))) (t_exit (Z_to_bv 64 0) fs))).
  { intros j Hj. unfold HOLES_C, sC2. rewrite (hole_cls_small j ltac:(lia)).
    assert (Hnth : nth j sC2s_can SNil = SCase e_b1s MAXS (SHole 0) (SHole 1)).
    { destruct j as [|[|[|[|[|j]]]]]; try lia; reflexivity. }
    rewrite Hnth. cbn [sd]. change (bv_unsigned (edenot E e_b1s)) with (uE E e_b1s).
    assert (Hsd : forall k ex, (k < 2)%nat -> nth k (nth j (sXs_of neg) []) SNil = sx_of neg j ex ->
                   t_eq (HOLES_X (sXs_of neg) j k E fs) (t_emit (W1 (rep (lineZ neg) (j - 1))) (t_exit (Z_to_bv 64 ex) fs))).
    { intros k ex Hk2 Hn. unfold HOLES_X, sX. rewrite (hole_cls_small j ltac:(lia)), (hole_cls_small k ltac:(lia)), Hn.
      destruct j as [|[|j]]; [lia | |].
      - cbn [sx_of sd Nat.sub rep W1 map]. apply t_eq_sym. apply t_emit_nil_eq. apply t_emit_has_nil.
      - cbn [sx_of sd]. unfold Wp, W1. cbn [flat_map piece_den]. rewrite app_nil_r. apply t_eq_refl. }
    unfold cnt_of. destruct (uE E e_b1s <=? MAXS) eqn:Hle; cbn [negb].
    - apply (Hsd 0%nat); [lia|]. destruct j as [|[|[|[|[|j]]]]]; try lia; reflexivity.
    - apply (Hsd 1%nat); [lia|]. destruct j as [|[|[|[|[|j]]]]]; try lia; reflexivity. }
  change (bv_unsigned (edenot E (EVar vk))) with (uE E (EVar vk)). rewrite Hk.
  destruct calls as [|[|[|[|[|c]]]]]; try lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.leb Z.compare Pos.compare Pos.compare_cont]; apply Hhole; lia.
Qed.

(* [comment removed for export] *)
Definition kn_mem (K : kentry) (cs : acs) : bool := existsb (kentry_eqb K) (kn cs).
Lemma kn_mem_In : forall K cs, kn_mem K cs = true -> In K (kn cs).
Proof. intros K cs H. unfold kn_mem in H. apply existsb_exists in H as (X & HX & HE). apply kentry_eqb_eq in HE. subst X. exact HX. Qed.
Definition blob_mem (cs : acs) : bool := existsb (fun K => match K with KBlob _ n k => (expr_eqb n (EVar LV) && Nat.eqb k 32)%bool | _ => false end) (kn cs).
Lemma blob_mem_In : forall cs, blob_mem cs = true -> exists a, In (KBlob a (EVar LV) 32%nat) (kn cs).
Proof.
  intros cs H. unfold blob_mem in H. apply existsb_exists in H as (X & HX & HE). destruct X; try discriminate HE.
  apply andb_prop in HE as [H1 H2]. apply expr_eqb_eq in H1. apply Nat.eqb_eq in H2. subst. eexists. exact HX.
Qed.
Lemma know_in : forall E M k K, know_ok HASEGS E M k -> In K k -> kentry_ok HASEGS E M K.
Proof. intros E M k K H HI. exact (proj1 (Forall_forall _ _) H K HI). Qed.

Definition rng (lo hi a b : Z) : bool := (Z.leb lo a && Z.leb b hi)%bool.      (* [comment removed for export] *)
Lemma rng_in : forall lo hi a b x, rng lo hi a b = true -> a <= x <= b -> lo <= x /\ x <= hi.
Proof. intros lo hi a b x H Hx. unfold rng in H. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1, H2. lia. Qed.
Definition modrng (m a b : Z) : Z * Z := if a / m =? b / m then (a mod m, b mod m) else (0, m - 1).
Lemma modrng_in : forall m a b x, 0 < m -> a <= x <= b -> fst (modrng m a b) <= x mod m <= snd (modrng m a b).
Proof.
  intros m a b x Hm Hx. unfold modrng. pose proof (Z.mod_pos_bound x m Hm) as HB.
  destruct (a / m =? b / m) eqn:EQ; cbn [fst snd]; [|lia]. apply Z.eqb_eq in EQ.
  assert (Hq : x / m = a / m). { pose proof (Z.div_le_mono a x m Hm ltac:(lia)). pose proof (Z.div_le_mono x b m Hm ltac:(lia)). lia. }
  pose proof (Z.div_mod x m ltac:(lia)) as Dx. pose proof (Z.div_mod a m ltac:(lia)) as Da. pose proof (Z.div_mod b m ltac:(lia)) as Db.
  rewrite Hq in Dx. rewrite <- EQ in Db. nia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint cover_ok (tab : list (Z * Z)) (a b : Z) : bool :=
  match tab with
  | [] => Z.ltb b a
  | (lo, hi) :: r => (Z.ltb b a || (if (Z.leb lo a && Z.leb a hi)%bool then (Z.leb b hi || cover_ok r (hi + 1) b)%bool else cover_ok r a b))%bool
  end.
Lemma cover_ok_sound : forall tab a b, cover_ok tab a b = true -> forall n, a <= n <= b -> exists p, In p tab /\ fst p <= n <= snd p.
Proof.
  induction tab as [|[lo hi] r IH]; intros a b H n Hn; cbn [cover_ok] in H.
  - apply Z.ltb_lt in H. lia.
  - apply orb_prop in H as [H|H]; [apply Z.ltb_lt in H; lia|].
    destruct (Z.leb lo a && Z.leb a hi)%bool eqn:Hc.
    + apply andb_prop in Hc as [H1 H1']. apply Z.leb_le in H1. apply Z.leb_le in H1'.
      destruct (Z_le_gt_dec n hi) as [Hle|Hgt]; [exists (lo, hi); split; [left; reflexivity | cbn; lia]|].
      apply orb_prop in H as [H2|H2]; [apply Z.leb_le in H2; lia|].
      destruct (IH (hi + 1) b H2 n ltac:(lia)) as [p [Hp Hr]]. exists p. split; [right; exact Hp | exact Hr].
    + destruct (IH a b H n Hn) as [p [Hp Hr]]. exists p. split; [right; exact Hp | exact Hr].
Qed.

(* [comment removed for export] *)
Definition cellq : Type := (Z * Z * Z * Z)%type.
Definition c_qlo (c : cellq) : Z := fst (fst (fst c)).
Definition c_qhi (c : cellq) : Z := snd (fst (fst c)).
Definition c_rlo (c : cellq) : Z := snd (fst c).
Definition c_rhi (c : cellq) : Z := snd c.
Definition cover2 (cells : list cellq) (a b : Z) : bool :=
  forallb (fun r => cover_ok (map (fun c => (c_qlo c, c_qhi c)) (List.filter (fun c => (c_rlo c <=? r) && (r <=? c_rhi c))%bool cells)) ((a - r + 7) / 8) ((b - r) / 8)) [0; 1; 2; 3; 4; 5; 6; 7].
Lemma cover2_sound : forall cells a b, cover2 cells a b = true -> forall n, a <= n <= b ->
  exists c, In c cells /\ c_qlo c <= n / 8 <= c_qhi c /\ c_rlo c <= n mod 8 <= c_rhi c.
Proof.
  intros cells a b H n Hn. pose proof (Z.mod_pos_bound n 8 ltac:(lia)) as Hr. pose proof (Z.div_mod n 8 ltac:(lia)) as Dn.
  set (q := n / 8) in *. set (r := n mod 8) in *.
  assert (Hin : In r [0; 1; 2; 3; 4; 5; 6; 7]).
  { assert (X : r = 0 \/ r = 1 \/ r = 2 \/ r = 3 \/ r = 4 \/ r = 5 \/ r = 6 \/ r = 7) by lia. cbn. intuition lia. }
  pose proof (proj1 (forallb_forall _ _) H r Hin) as C.
  assert (Hq : (a - r + 7) / 8 <= q <= (b - r) / 8).
  { split.
    - replace q with ((8 * q + 7) / 8). { apply Z.div_le_mono; lia. }
      symmetry. apply (Z.div_unique _ _ _ 7); lia.
    - apply Z.div_le_lower_bound; lia. }
  destruct (cover_ok_sound _ _ _ C q Hq) as (p & Hp & Hpq). apply in_map_iff in Hp as (c & <- & Hc). cbn [fst snd] in Hpq.
  apply filter_In in Hc as [Hc Hf]. apply andb_prop in Hf as [F1 F2]. apply Z.leb_le in F1, F2. exists c. repeat split; try assumption; lia.
Qed.

(* [comment removed for export] *)
Section Ext.
  Variables (VK VQ VR VN V1 NQ NR : nat).
  Variable NB : nat.                                   (* [comment removed for export] *)
  Definition e_cfgq : expr := eadd (escale 64 (EVar VQ)) (EVar VR).
  Definition e_nq : expr := eadd (escale 8 (EVar NQ)) (EVar NR).
  Definition s_ext (cl0 : bool) : list (nat * expr) :=
    [(VK, if cl0 then ELit 1 else EAlu ALU_ADD e_cm (ELit 1)); (VQ, EAlu ALU_SRL e_cl (ELit 6)); (VR, EAlu ALU_AND e_cl (ELit 63));
     (VN, e_n); (V1, ELit 1); (NQ, EAlu ALU_SRL e_n (ELit 3)); (NR, EAlu ALU_AND e_n (ELit 7))].
  Hypothesis Hext : forall b, sig_ok NB (s_ext b) = true.
  Hypothesis Hvars : forallb (expr_vars_lt NB) [e_cl; e_n; e_cm; e_b1s; EVar LV] = true.

  (* [comment removed for export] *)
  Record numok (E : env) : Prop := NUMOK {
    nm_L : 6 <= uE E (EVar LV) <= 65535;
    nm_cl : 0 <= cl_of E <= 32767;
    nm_n : 0 <= uE E e_n <= 65529;
    nm_blob : Z.of_nat (length (eb E 32%nat)) = uE E (EVar LV) }.

  Lemma num_n : forall E, numok E -> uE E e_n = nb_of E /\ uE E (EVar LV) = 6 + cl_of E + uE E e_n.
  Proof.
    intros E [HL Hcl Hn Hb]. unfold nb_of. rewrite Hb. unfold cl_of in *.
    assert (X : uE E e_n = ((uE E (EVar LV) - 6) mod 2 ^ 64 - uE E e_cl) mod 2 ^ 64).
    { unfold e_n, ION.XROOM, esub, uE. rewrite !mkAlu_denot, !u_sub64. cbn [edenot]. rewrite u_lit64. change (6 mod two64) with 6. reflexivity. }
    rewrite (Z.mod_small (uE E (EVar LV) - 6)) in X by lia.
    destruct (Z_lt_ge_dec (uE E (EVar LV) - 6 - uE E e_cl) 0) as [Hneg|Hpos].
    - exfalso. assert (Y : (uE E (EVar LV) - 6 - uE E e_cl) mod 2 ^ 64 = uE E (EVar LV) - 6 - uE E e_cl + 2 ^ 64).
      { symmetry. apply (Z.mod_unique _ _ (-1)); lia. }
      rewrite Y in X. lia.
    - rewrite Z.mod_small in X by lia. lia.
  Qed.

  Lemma cm_range : forall E, 0 <= uE E e_cm <= 3.
  Proof.
    intros E. unfold e_cm, ION.XCM, uE. cbn [edenot]. rewrite u_and64, u_lit64. change (3 mod two64) with (Z.ones 2).
    rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound (bv_unsigned (edenot E (ION.XB2 32))) (2 ^ 2) ltac:(lia)). lia.
  Qed.

  Lemma vk_val : forall (E1 : env) (bb : bool) (cmv : Z), bv_unsigned (edenot E1 e_cm) = cmv -> 0 <= cmv <= 3 ->
    bv_unsigned (edenot E1 (if bb then ELit 1 else EAlu ALU_ADD e_cm (ELit 1))) = if bb then 1 else cmv + 1.
  Proof.
    intros E1 bb cmv H1 H2. destruct bb; cbn [edenot].
    - rewrite u_lit64. reflexivity.
    - rewrite u_add64, u_lit64, H1. change (1 mod two64) with 1. apply Z.mod_small. lia.
  Qed.

  Section Vals.
    Variable E : env. Variable b : bool.
    Hypothesis HN : numok E.
    Let E' := apply_sig E (s_ext b).
    Lemma ext_agree : env_agree NB E E'.
    Proof. apply apply_sig_agree. exact (sig_ok_dom NB (s_ext b) (Hext b)). Qed.
    Lemma ext_closed : forall e, expr_vars_lt NB e = true -> uE E' e = uE E e.
    Proof. intros e He. unfold uE. rewrite (edenot_agree' NB E E' e ext_agree He). reflexivity. Qed.
    Lemma ext_vars : expr_vars_lt NB e_cl = true /\ expr_vars_lt NB e_n = true /\ expr_vars_lt NB e_cm = true /\ expr_vars_lt NB e_b1s = true /\ expr_vars_lt NB (EVar LV) = true.
    Proof. pose proof Hvars as H. cbn [forallb] in H. repeat (apply andb_prop in H; destruct H as [? H]). repeat split; assumption. Qed.
    Lemma ext_holds : sig_holds E' (s_ext b).
    Proof. exact (apply_sig_holds NB (s_ext b) E (Hext b)). Qed.

    Let cl := cl_of E. Let n := uE E e_n.
    Lemma ev_cl : bv_unsigned (edenot E' e_cl) = cl. Proof. exact (ext_closed e_cl (proj1 ext_vars)). Qed.
    Lemma ev_n : bv_unsigned (edenot E' e_n) = n. Proof. exact (ext_closed e_n (proj1 (proj2 ext_vars))). Qed.
    Lemma ev_cm : bv_unsigned (edenot E' e_cm) = uE E e_cm. Proof. exact (ext_closed e_cm (proj1 (proj2 (proj2 ext_vars)))). Qed.
    Lemma ev_b1s : uE E' e_b1s = uE E e_b1s. Proof. exact (ext_closed e_b1s (proj1 (proj2 (proj2 (proj2 ext_vars))))). Qed.
    Lemma ev_L : bv_unsigned (ev E' LV) = uE E (EVar LV). Proof. exact (ext_closed (EVar LV) (proj2 (proj2 (proj2 (proj2 ext_vars))))). Qed.
    Lemma cl_rng : 0 <= cl <= 32767. Proof. exact (nm_cl E HN). Qed.
    Lemma n_rng : 0 <= n <= 65529. Proof. exact (nm_n E HN). Qed.

    Lemma vals : bv_unsigned (ev E' VK) = (if b then 1 else uE E e_cm + 1) /\ bv_unsigned (ev E' VQ) = cl / 64 /\ bv_unsigned (ev E' VR) = cl mod 64
                 /\ bv_unsigned (ev E' VN) = n /\ bv_unsigned (ev E' V1) = 1 /\ bv_unsigned (ev E' NQ) = n / 8 /\ bv_unsigned (ev E' NR) = n mod 8.
    Proof.
      pose proof ext_holds as H. unfold s_ext, sig_holds in H.
      pose proof (Forall_inv H) as HK. apply Forall_inv_tail in H. pose proof (Forall_inv H) as HQ. apply Forall_inv_tail in H.
      pose proof (Forall_inv H) as HR. apply Forall_inv_tail in H. pose proof (Forall_inv H) as HVN. apply Forall_inv_tail in H.
      pose proof (Forall_inv H) as H1. apply Forall_inv_tail in H. pose proof (Forall_inv H) as HNQ. apply Forall_inv_tail in H. pose proof (Forall_inv H) as HNR.
      cbn [fst snd] in *.
      pose proof cl_rng as Hc. pose proof n_rng as Hn. pose proof (cm_range E) as Hm.
      repeat split.
      - rewrite HK. exact (vk_val E' b (uE E e_cm) ev_cm Hm).
      - rewrite HQ. cbn [edenot]. rewrite u_srl64, u_lit64, ev_cl. reflexivity.
      - rewrite HR. cbn [edenot]. rewrite u_and64, u_lit64, ev_cl. change (63 mod two64) with (Z.ones 6). rewrite Z.land_ones by lia. reflexivity.
      - rewrite HVN. exact ev_n.
      - rewrite H1. cbn [edenot]. rewrite u_lit64. reflexivity.
      - rewrite HNQ. cbn [edenot]. rewrite u_srl64, u_lit64, ev_n. reflexivity.
      - rewrite HNR. cbn [edenot]. rewrite u_and64, u_lit64, ev_n. change (7 mod two64) with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity.
    Qed.

    (* [comment removed for export] *)
    Definition cllo : Z := if b then 0 else 1.
    Definition clhi : Z := if b then 0 else 32767.
    Definition fact_ok (qlo qhi rlo rhi : Z) (F : kentry) : bool :=
      let nlo := 8 * qlo + rlo in let nhi := Z.min (8 * qhi + rhi) 65529 in      (* [comment removed for export] *)
      match F with
      | KRange e lo hi =>
          if expr_eqb e e_cl then rng lo hi cllo clhi
          else if expr_eqb e e_n then rng lo hi nlo nhi
          else if expr_eqb e (EVar VQ) then (rng lo hi (cllo / 64) (clhi / 64) || rng lo hi 0 ((65529 - nlo) / 64))%bool      (* [comment removed for export] *)
          else if expr_eqb e (EVar VR) then rng lo hi (fst (modrng 64 cllo clhi)) (snd (modrng 64 cllo clhi))
          else if expr_eqb e (EVar VN) then rng lo hi nlo nhi
          else if expr_eqb e (EVar NQ) then rng lo hi qlo qhi
          else if expr_eqb e (EVar NR) then rng lo hi rlo rhi
          else if expr_eqb e (EVar VK) then rng lo hi 1 (if b then 1 else 4)
          else if expr_eqb e (EVar V1) then rng lo hi 1 1
          else if expr_eqb e (esub e_cl e_cfgq) then rng lo hi 0 0
          else if expr_eqb e (esub e_n (EVar VN)) then rng lo hi 0 0
          else if expr_eqb e (esub (EVar LV) (eaddz (eadd e_cfgq (EVar VN)) 6)) then rng lo hi 0 0
          else if expr_eqb e (esub (EVar LV) (eaddz e_cfgq 6)) then rng lo hi nlo nhi      (* [comment removed for export] *)
          else if expr_eqb e (esub (EVar VN) e_nq) then rng lo hi 0 0
          else if expr_eqb e (esub (eaddz e_cm 1) (EVar VK)) then (negb b && rng lo hi 0 0)%bool
          else if expr_eqb e (esub (EVar VN) (eaddz (EVar NR) (8 * qlo))) then ((qlo =? qhi) && rng lo hi 0 0)%bool
          else false
      | _ => false
      end.

    Lemma fact_ok_sound : forall qlo qhi rlo rhi F, cllo <= cl <= clhi -> qlo <= n / 8 <= qhi -> rlo <= n mod 8 <= rhi -> fact_ok qlo qhi rlo rhi F = true -> pure_holds E' F.
    Proof.
      intros qlo qhi rlo rhi F Hcl Hq Hr HF. destruct F as [| | | | |e lo hi| | | |]; try discriminate HF.
      cbn [fact_ok] in HF. cbn [pure_holds].
      destruct vals as (XK & XQ & XR & XN & X1 & XNQ & XNR).
      pose proof cl_rng as Hc. pose proof n_rng as Hnr. pose proof (cm_range E) as Hm.
      pose proof (Z.div_mod cl 64 ltac:(lia)) as Dc. pose proof (Z.mod_pos_bound cl 64 ltac:(lia)) as Bc.
      pose proof (Z.div_mod n 8 ltac:(lia)) as Dn. pose proof (Z.mod_pos_bound n 8 ltac:(lia)) as Bn.
      assert (Qc : 0 <= cl / 64) by (apply Z.div_pos; lia). assert (Qn : 0 <= n / 8) by (apply Z.div_pos; lia).
      assert (Hn : 8 * qlo + rlo <= n <= Z.min (8 * qhi + rhi) 65529) by lia.
      destruct (expr_eqb e e_cl) eqn:Q1; [apply expr_eqb_eq in Q1; subst e; rewrite ev_cl; exact (rng_in _ _ _ _ cl HF Hcl)|].
      destruct (expr_eqb e e_n) eqn:Q2; [apply expr_eqb_eq in Q2; subst e; rewrite ev_n; exact (rng_in _ _ _ _ n HF Hn)|].
      destruct (expr_eqb e (EVar VQ)) eqn:Q3.
      { apply expr_eqb_eq in Q3; subst e. cbn [edenot]. rewrite XQ. apply orb_prop in HF as [HF|HF].
        - apply (rng_in _ _ _ _ _ HF). split; apply Z.div_le_mono; lia.
        - apply (rng_in _ _ _ _ _ HF). destruct (num_n E HN) as [HNn HLn]. fold cl in HLn. rewrite HNn in HLn. fold n in HLn. pose proof (nm_L E HN) as HLr.
          split; [exact Qc | apply Z.div_le_mono; lia]. }
      destruct (expr_eqb e (EVar VR)) eqn:Q4.
      { apply expr_eqb_eq in Q4; subst e. cbn [edenot]. rewrite XR. apply (rng_in _ _ _ _ _ HF). apply modrng_in; lia. }
      destruct (expr_eqb e (EVar VN)) eqn:Q5; [apply expr_eqb_eq in Q5; subst e; cbn [edenot]; rewrite XN; exact (rng_in _ _ _ _ n HF Hn)|].
      destruct (expr_eqb e (EVar NQ)) eqn:Q6.
      { apply expr_eqb_eq in Q6; subst e. cbn [edenot]. rewrite XNQ. exact (rng_in _ _ _ _ _ HF Hq). }
      destruct (expr_eqb e (EVar NR)) eqn:Q7.
      { apply expr_eqb_eq in Q7; subst e. cbn [edenot]. rewrite XNR. exact (rng_in _ _ _ _ _ HF Hr). }
      destruct (expr_eqb e (EVar VK)) eqn:Q8.
      { apply expr_eqb_eq in Q8; subst e. cbn [edenot]. rewrite XK. apply (rng_in _ _ _ _ _ HF). clear -Hm. destruct b; lia. }
      destruct (expr_eqb e (EVar V1)) eqn:Q9; [apply expr_eqb_eq in Q9; subst e; cbn [edenot]; rewrite X1; apply (rng_in _ _ _ _ _ HF); lia|].
      destruct (expr_eqb e (esub e_cl e_cfgq)) eqn:Q10.
      { apply expr_eqb_eq in Q10; subst e. apply (rng_in _ _ 0 0 _ HF).
        unfold esub, e_cfgq, eadd, escale. rewrite mkAlu_denot, u_sub64, mkAlu_denot, u_add64, mkMd_denot, u_mul64. cbn [edenot]. rewrite u_lit64, ev_cl, XQ, XR.
        change (64 mod two64) with 64. rewrite (Z.mod_small (64 * (cl / 64))) by lia. rewrite (Z.mod_small (64 * (cl / 64) + cl mod 64)) by lia.
        replace (cl - (64 * (cl / 64) + cl mod 64)) with 0 by lia. rewrite Z.mod_0_l by lia. lia. }
      destruct (expr_eqb e (esub e_n (EVar VN))) eqn:Q11.
      { apply expr_eqb_eq in Q11; subst e. apply (rng_in _ _ 0 0 _ HF). unfold esub. rewrite mkAlu_denot, u_sub64. cbn [edenot]. rewrite ev_n, XN.
        rewrite Z.sub_diag, Z.mod_0_l by lia. lia. }
      destruct (expr_eqb e (esub (EVar LV) (eaddz (eadd e_cfgq (EVar VN)) 6))) eqn:Q12.
      { apply expr_eqb_eq in Q12; subst e. apply (rng_in _ _ 0 0 _ HF). destruct (num_n E HN) as [_ HLn]. fold cl n in HLn.
        unfold esub, eaddz, e_cfgq, eadd, escale. rewrite mkAlu_denot, u_sub64, !mkAlu_denot, !u_add64, mkMd_denot, u_mul64. cbn [edenot]. rewrite !u_lit64, ev_L, XQ, XR, XN.
        change (64 mod two64) with 64. change (6 mod two64) with 6. rewrite (Z.mod_small (64 * (cl / 64))) by lia. rewrite (Z.mod_small (64 * (cl / 64) + cl mod 64)) by lia.
        rewrite (Z.mod_small (64 * (cl / 64) + cl mod 64 + n)) by lia. rewrite (Z.mod_small (64 * (cl / 64) + cl mod 64 + n + 6)) by lia.
        replace (uE E (EVar LV) - (64 * (cl / 64) + cl mod 64 + n + 6)) with 0 by lia. rewrite Z.mod_0_l by lia. lia. }
      destruct (expr_eqb e (esub (EVar LV) (eaddz e_cfgq 6))) eqn:Q12b.
      { apply expr_eqb_eq in Q12b; subst e. destruct (num_n E HN) as [_ HLn]. fold cl n in HLn.
        unfold esub, eaddz, e_cfgq, eadd, escale. rewrite mkAlu_denot, u_sub64, !mkAlu_denot, !u_add64, mkMd_denot, u_mul64. cbn [edenot]. rewrite !u_lit64, ev_L, XQ, XR.
        change (64 mod two64) with 64. change (6 mod two64) with 6. rewrite (Z.mod_small (64 * (cl / 64))) by lia. rewrite (Z.mod_small (64 * (cl / 64) + cl mod 64)) by lia.
        rewrite (Z.mod_small (64 * (cl / 64) + cl mod 64 + 6)) by lia.
        replace (uE E (EVar LV) - (64 * (cl / 64) + cl mod 64 + 6)) with n by lia. rewrite (Z.mod_small n) by (unfold two64; lia). exact (rng_in _ _ _ _ n HF Hn). }
      destruct (expr_eqb e (esub (EVar VN) e_nq)) eqn:Q13.
      { apply expr_eqb_eq in Q13; subst e. apply (rng_in _ _ 0 0 _ HF).
        unfold esub, e_nq, eadd, escale. rewrite mkAlu_denot, u_sub64, mkAlu_denot, u_add64, mkMd_denot, u_mul64. cbn [edenot]. rewrite u_lit64, XN, XNQ, XNR.
        change (8 mod two64) with 8. rewrite (Z.mod_small (8 * (n / 8))) by lia. rewrite (Z.mod_small (8 * (n / 8) + n mod 8)) by lia.
        replace (n - (8 * (n / 8) + n mod 8)) with 0 by lia. rewrite Z.mod_0_l by lia. lia. }
      destruct (expr_eqb e (esub (eaddz e_cm 1) (EVar VK))) eqn:Q14.
      { apply expr_eqb_eq in Q14; subst e. apply andb_prop in HF as [Hb HF]. apply (rng_in _ _ 0 0 _ HF).
        unfold esub, eaddz. rewrite mkAlu_denot, u_sub64, mkAlu_denot, u_add64. cbn [edenot]. rewrite u_lit64, ev_cm, XK. change (1 mod two64) with 1.
        rewrite (Z.mod_small (uE E e_cm + 1)) by lia.
        assert (Y : (if b then 1 else uE E e_cm + 1) = uE E e_cm + 1) by (clear -Hb; destruct b; [discriminate Hb | reflexivity]).
        rewrite Y, Z.sub_diag, Z.mod_0_l by lia. lia. }
      destruct (expr_eqb e (esub (EVar VN) (eaddz (EVar NR) (8 * qlo)))) eqn:Q15; [|discriminate HF].
      apply expr_eqb_eq in Q15; subst e. apply andb_prop in HF as [Hqq HF]. apply Z.eqb_eq in Hqq. apply (rng_in _ _ 0 0 _ HF).
      assert (Hqn : n / 8 = qlo) by lia.
      unfold esub, eaddz. rewrite mkAlu_denot, u_sub64, mkAlu_denot, u_add64. cbn [edenot]. rewrite u_lit64, XN, XNR. rewrite <- Hqn.
      unfold two64. rewrite (Z.mod_small (8 * (n / 8))) by lia. rewrite (Z.mod_small (n mod 8 + 8 * (n / 8))) by lia.
      replace (n - (n mod 8 + 8 * (n / 8))) with 0 by lia. rewrite Z.mod_0_l by lia. lia.
    Qed.
  End Vals.
End Ext.

(* [comment removed for export] *)
Definition dfact (d : nat * nat * Z * Z * Z) : kentry :=
  let '(P, Q, c, lo, hi) := d in KRange (esub (escale c (EVar P)) (escale c (EVar Q))) lo hi.
Definition rng_of (cs : acs) (v : nat) : option (Z * Z) :=
  match List.find (fun K => match K with KRange (EVar v') _ _ => Nat.eqb v v' | _ => false end) (kn cs) with
  | Some (KRange _ lo hi) => Some (lo, hi) | _ => None end.
Lemma rng_of_In : forall cs v lo hi, rng_of cs v = Some (lo, hi) -> In (KRange (EVar v) lo hi) (kn cs).
Proof.
  intros cs v lo hi H. unfold rng_of in H. destruct (List.find _ (kn cs)) as [K|] eqn:EF; [|discriminate].
  apply List.find_some in EF as [HI HK]. destruct K; try discriminate H. destruct e; try discriminate HK. apply Nat.eqb_eq in HK. subst. injection H as <- <-. exact HI.
Qed.
Definition dside (cs : acs) (d : nat * nat * Z * Z * Z) : bool :=
  let '(P, Q, c, lo, hi) := d in
  match rng_of cs P, rng_of cs Q with
  | Some (plo, phi), Some (qlo, qhi) =>
      ((0 <? c) && (c <? 2 ^ 64) && (0 <=? qlo) && (qlo <=? qhi) && (plo <=? phi) && (c * phi <? 2 ^ 64) && (c * qhi <=? c * plo)
       && (lo <=? c * plo - c * qhi) && (c * phi - c * qlo <=? hi))%bool
  | _, _ => false
  end.
Lemma dfact_sound : forall cs d E M, know_ok HASEGS E M (kn cs) -> dside cs d = true -> pure_holds E (dfact d).
Proof.
  intros cs [[[[P Q] c] lo] hi] E M HK HS. unfold dside in HS.
  destruct (rng_of cs P) as [[plo phi]|] eqn:EP; [|discriminate]. destruct (rng_of cs Q) as [[qlo qhi]|] eqn:EQ; [|discriminate].
  repeat (apply andb_prop in HS; destruct HS as [HS ?]).
  repeat match goal with X : (_ <? _) = true |- _ => apply Z.ltb_lt in X | X : (_ <=? _) = true |- _ => apply Z.leb_le in X end.
  pose proof (know_in E M _ _ HK (rng_of_In _ _ _ _ EP)) as [HP1 HP2]. pose proof (know_in E M _ _ HK (rng_of_In _ _ _ _ EQ)) as [HQ1 HQ2].
  cbn [edenot] in HP1, HP2, HQ1, HQ2. set (p := bv_unsigned (ev E P)) in *. set (q := bv_unsigned (ev E Q)) in *.
  unfold dfact. cbn [pure_holds]. unfold esub, escale. rewrite mkAlu_denot, u_sub64, !mkMd_denot, !u_mul64. cbn [edenot]. rewrite u_lit64. fold p q.
  unfold two64. rewrite (Z.mod_small c) by lia.
  assert (A1 : c * plo <= c * p) by (apply Z.mul_le_mono_nonneg_l; lia). assert (A2 : c * p <= c * phi) by (apply Z.mul_le_mono_nonneg_l; lia).
  assert (A3 : c * qlo <= c * q) by (apply Z.mul_le_mono_nonneg_l; lia). assert (A4 : c * q <= c * qhi) by (apply Z.mul_le_mono_nonneg_l; lia).
  assert (A5 : 0 <= c * qlo) by (apply Z.mul_nonneg_nonneg; lia).
  rewrite (Z.mod_small (c * p)) by lia. rewrite (Z.mod_small (c * q)) by lia. rewrite Z.mod_small by lia. lia.
Qed.

(* [comment removed for export] *)
Section Drv.
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variables argv envp : list (list byte).
  Variables uid hw : word.
  Variable fs : Fs.Fs.
  #[local] Notation argH := (argH0 HAPH sp rdraw argv envp uid hw).
  #[local] Notation ISP := (bv_unsigned sp).
  #[local] Notation LIM := AsanInit.LIMIT.
  Variable SV : env -> (word -> option byte) -> Prop.
  Hypothesis SV_agree : forall E E' M, env_agree NX0 E E' -> SV E M -> SV E' M.
  #[local] Notation CSOK PHI := (cs_ok HASEGS HAT LIM (SVG PHI SV) argH ISP fs).

  Variables (VK VQ VR VN V1 NQ NR : nat).
  Variables (BASE S0 : acs) (NB N0 : nat).
  Hypothesis HNB : nxt BASE = NB.
  Hypothesis HNB0 : (NX0 <= NB)%nat.
  Hypothesis NB_spw : CAP.expr_vars_lt NB e_spw = true.
  Hypothesis Hfresh : fresh_ok NB BASE = true.
  (* [comment removed for export] *)
  Hypothesis Hsub : forallb (fun K => kn_mem K BASE) (kn S0) = true.
  Hypothesis Hbump : node_bump (set_kn BASE (kn S0)) N0 = Some S0.
  Hypothesis Hext : forall b, sig_ok NB (s_ext VK VQ VR VN V1 NQ NR b) = true.
  Hypothesis Hvars : forallb (expr_vars_lt NB) [e_cl; e_n; e_cm; e_b1s; EVar LV] = true.
  Hypothesis HKN : (kn_mem (KRange (EVar LV) 6 65535) BASE && kn_mem (KRange e_cl 0 32767) BASE && kn_mem (KRange e_n 0 65529) BASE && blob_mem BASE)%bool = true.

  Variables (a0s : list a0d) (leaves : list leafd) (lnums : list cellq).
  Variables (shapeB : shape) (sC2s : list shape) (sXs : list (list shape)) (neg : bool).
  Hypothesis Hshapes : shapeB = shapeB_of VK neg /\ sC2s = sC2s_can /\ sXs = sXs_of neg.
  Variable DL : list (nat * nat * Z * Z * Z).
  Variables GLO GHI : Z.

  (* [comment removed for export] *)
  Hypothesis HG : forall v l, In v a0s -> In l leaves -> forall PHI0 : env -> Prop,
    (forall E E', env_agree N0 E E' -> PHI0 E -> PHI0 E') ->
    (forall E, PHI0 E -> Forall (pure_holds E) (a0_F v) /\ Forall (pure_holds E) (ld_F l)) ->
    forall E R FULL model, CSOK PHI0 E (stA0 S0 v) R FULL model ->
      crz HASEGS (cfg_of HASEGS R (pc S0) FULL model) (DEN shapeB sC2s sXs E (m_fs model)).

  Definition dflt_a0 : a0d := A0D [] PExit [] [].
  Definition ctx_ok (F : kentry) : bool :=
    (pure_fact F && CAP.kn_vars_lt NB [F] && (kn_mem F BASE || existsb (fun d => kentry_eqb F (dfact d) && dside BASE d) DL))%bool.
  Definition var_of (bb : bool) : a0d := nth (if bb then 0 else 1)%nat a0s dflt_a0.
  Definition cell_ok (bb : bool) (x : cellq * leafd) : bool :=
    forallb (fun F => (fact_ok VK VQ VR VN V1 NQ NR bb (c_qlo (fst x)) (c_qhi (fst x)) (c_rlo (fst x)) (c_rhi (fst x)) F || ctx_ok F)%bool) (a0_F (var_of bb) ++ ld_F (snd x)).
  Definition chk : bool :=
    (Nat.eqb (length a0s) 2 && Nat.eqb (length lnums) (length leaves) && cover2 lnums GLO GHI && (0 <=? GLO) && (GHI <=? 65529)
     && forallb (fun bb => forallb (cell_ok bb) (combine lnums leaves)) [true; false]
     && forallb (fun v => forallb (fun l => F_ok N0 (a0_F v ++ ld_F l)) leaves) a0s && Nat.leb NB N0)%bool.
  Hypothesis CHK : chk = true.

  Lemma ctx_ok_sound : forall E E' M F, know_ok HASEGS E M (kn BASE) -> env_agree NB E E' -> ctx_ok F = true -> pure_holds E' F.
  Proof.
    intros E E' M F HK Hag H. unfold ctx_ok in H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
    assert (HE : pure_holds E F).
    { apply orb_prop in H3 as [H3|H3].
      - pose proof (know_in E M _ _ HK (kn_mem_In _ _ H3)) as X. destruct F; try discriminate H1; exact X.
      - apply existsb_exists in H3 as (d & _ & Hd). apply andb_prop in Hd as [Hd1 Hd2]. apply kentry_eqb_eq in Hd1. subst F. exact (dfact_sound BASE d E M HK Hd2). }
    assert (FO : F_ok NB [F] = true) by (unfold F_ok; cbn [forallb]; rewrite H1, H2; reflexivity).
    assert (HL1 : Forall (pure_holds E) [F]) by (constructor; [exact HE | constructor]).
    exact (Forall_inv (pure_agree NB [F] E E' Hag FO HL1)).
  Qed.

  Lemma base_numok : forall (PHIb : env -> Prop) E R FULL model, CSOK PHIb E BASE R FULL model -> numok E.
  Proof.
    intros PHIb E R FULL model HC.
    pose proof HKN as K. repeat (apply andb_prop in K; destruct K as [K ?]).
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) as HKO. match type of HKO with know_ok _ _ ?m _ => set (M := m) in * end.
    destruct (blob_mem_In BASE ltac:(assumption)) as [ab Hab].
    pose proof (know_in E M _ _ HKO (kn_mem_In _ _ K)) as [L1 L2].
    constructor.
    - split; assumption.
    - match goal with Y : kn_mem (KRange e_cl 0 32767) BASE = true |- _ => pose proof (know_in E M _ _ HKO (kn_mem_In _ _ Y)) as [? ?] end. unfold cl_of, uE. split; assumption.
    - match goal with Y : kn_mem (KRange e_n 0 65529) BASE = true |- _ => pose proof (know_in E M _ _ HKO (kn_mem_In _ _ Y)) as [? ?] end. unfold uE. split; assumption.
    - pose proof (know_in E M _ _ HKO Hab) as (_ & Hlen & _). exact Hlen.
  Qed.
  Lemma nb_range : forall (PHIb : env -> Prop) E R FULL model, CSOK PHIb E BASE R FULL model -> 0 <= nb_of E <= 65529.
  Proof. intros PHIb E R FULL model HC. pose proof (base_numok PHIb E R FULL model HC) as HN. destruct (num_n E HN) as [<- _]. exact (nm_n E HN). Qed.

  Theorem grp_drive : forall (PHIb : env -> Prop) E R FULL model,
    CSOK PHIb E BASE R FULL model -> GLO <= nb_of E <= GHI ->
    crz HASEGS (cfg_of HASEGS R (pc BASE) FULL model) (TGT neg (calls_of E) (cnt_of E) (m_fs model)).
  Proof.
    intros PHIb E R FULL model HC Hnb.
    pose proof CHK as C. unfold chk in C. repeat (apply andb_prop in C; destruct C as [C ?]).
    repeat match goal with X : (_ <=? _) = true |- _ => apply Z.leb_le in X | X : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in X | X : Nat.leb _ _ = true |- _ => apply Nat.leb_le in X end.
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) as HKO. match type of HKO with know_ok _ _ ?m _ => set (M := m) in * end.
    pose proof (base_numok PHIb E R FULL model HC) as HN.
    destruct (num_n E HN) as [Hn_eq HL_eq]. set (n := uE E e_n) in *. set (b := cl_of E =? 0).
    (* [comment removed for export] *)
    assert (Hnr : GLO <= n <= GHI) by lia.
    destruct (cover2_sound lnums GLO GHI ltac:(assumption) n Hnr) as (cq & Hp & Hpq & Hpr).
    destruct (In_nth lnums cq (0, 0, 0, 0) Hp) as (i & Hi & Hnth).
    set (l := nth i leaves (LDX [] PExit [] [] PExit [] [])).
    assert (Hl : In l leaves) by (apply nth_In; lia).
    assert (Hx : In (cq, l) (combine lnums leaves)).
    { rewrite <- Hnth. unfold l. rewrite <- (combine_nth lnums leaves i (0, 0, 0, 0) (LDX [] PExit [] [] PExit [] [])) by assumption. apply nth_In. rewrite length_combine. lia. }
    set (v := var_of b). assert (Hv : In v a0s) by (unfold v, var_of; apply nth_In; destruct b; lia).
    (* [comment removed for export] *)
    set (s := s_ext VK VQ VR VN V1 NQ NR b). set (E' := apply_sig E s).
    pose proof (ext_agree VK VQ VR VN V1 NQ NR NB Hext E b) as Hag. fold s E' in Hag.
    assert (Hcl : cllo b <= cl_of E <= clhi b).
    { pose proof (nm_cl E HN) as X. unfold cllo, clhi, b. destruct (cl_of E =? 0) eqn:EZ; [apply Z.eqb_eq in EZ | apply Z.eqb_neq in EZ]; lia. }
    assert (HF : Forall (pure_holds E') (a0_F v ++ ld_F l)).
    { match goal with Y : forallb (fun bb => forallb (cell_ok bb) _) _ = true |- _ => pose proof (proj1 (forallb_forall _ _) Y b ltac:(destruct b; cbn; tauto)) as Cb end.
      pose proof (proj1 (forallb_forall _ _) Cb _ Hx) as Cx. unfold cell_ok in Cx. cbn [fst snd] in Cx. fold v in Cx.
      apply Forall_forall. intros F HFin. pose proof (proj1 (forallb_forall _ _) Cx F HFin) as CF. apply orb_prop in CF as [CF|CF].
      - exact (fact_ok_sound VK VQ VR VN V1 NQ NR NB Hext Hvars E b HN _ _ _ _ F Hcl Hpq Hpr CF).
      - exact (ctx_ok_sound E E' M F HKO Hag CF). }
    (* [comment removed for export] *)
    assert (SA : forall (P : env -> Prop), (forall E1 E2, env_agree NB E1 E2 -> P E1 -> P E2) -> forall E1 E2 M1, env_agree NB E1 E2 -> SVG P SV E1 M1 -> SVG P SV E2 M1).
    { intros P HP E1 E2 M1 A [X1 X2]. split; [exact (SV_agree E1 E2 M1 (env_agree_le NX0 NB E1 E2 A HNB0) X1) | exact (HP E1 E2 A X2)]. }
    assert (AA : forall E1 E2 (a : word), env_agree NB E1 E2 -> argH E1 a = argH E2 a).
    { intros E1 E2 a A. exact (argH0_agree HAPH sp rdraw argv envp uid hw E1 E2 a (env_agree_le NX0 NB E1 E2 A HNB0)). }
    pose proof (cs_ok_sinv HASEGS HAT LIM argH ISP fs (SVG PHIb SV) (SVG (fun _ => True) SV) E BASE R FULL model ltac:(intros [X _]; split; [exact X | exact I]) HC) as HC0.
    pose proof (cs_ok_agree HASEGS HAT NB LIM NB_spw (SVG (fun _ => True) SV) argH ISP AA (SA (fun _ => True) (fun _ _ _ _ => I)) fs E E' BASE R FULL model
                  ltac:(rewrite HNB; exact Hag) Hfresh HC0) as HC1.
    assert (HC1w : CSOK (fun _ => True) E' (set_kn BASE (kn S0)) R FULL model).
    { apply cs_ok_set_kn; [exact HC1|]. pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC1) as HK1.
      apply Forall_forall. intros K HKin. exact (proj1 (Forall_forall _ _) HK1 K (kn_mem_In K BASE (proj1 (forallb_forall _ _) Hsub K HKin))). }
    destruct (bump_sound HASEGS HAT LIM (SVG (fun _ => True) SV) argH ISP fs E' (set_kn BASE (kn S0)) R FULL model N0 S0 HC1w Hbump) as [HC2 Hpc].
    change (pc (set_kn BASE (kn S0))) with (pc BASE) in Hpc.
    set (PHI0 := fun E1 : env => Forall (pure_holds E1) (a0_F v ++ ld_F l)).
    pose proof (cs_ok_sinv HASEGS HAT LIM argH ISP fs (SVG (fun _ => True) SV) (SVG PHI0 SV) E' S0 R FULL model ltac:(intros [X _]; split; [exact X | exact HF]) HC2) as HC3.
    assert (HFa : Forall (pure_holds E') (a0_F v)) by (apply Forall_app in HF; exact (proj1 HF)).
    pose proof (cs_ok_add_pure HASEGS HAT LIM argH ISP fs (SVG PHI0 SV) E' S0 R FULL model (a0_F v) HC3 HFa) as HC4.
    assert (PA : forall E1 E2, env_agree N0 E1 E2 -> PHI0 E1 -> PHI0 E2).
    { intros E1 E2 A X. unfold PHI0 in *.
      match goal with Y : forallb (fun v0 => forallb _ leaves) a0s = true |- _ => pose proof (proj1 (forallb_forall _ _) (proj1 (forallb_forall _ _) Y v Hv) l Hl) as FO end.
      exact (pure_agree N0 _ E1 E2 A FO X). }
    pose proof (HG v l Hv Hl PHI0 PA ltac:(intros E1 X; apply Forall_app in X; exact X) E' R FULL model HC4) as HR.
    rewrite Hpc in HR.
    (* [comment removed for export] *)
    destruct Hshapes as (-> & -> & ->).
    refine (crz_conseq HASEGS _ _ _ HR _).
    pose proof (vals VK VQ VR VN V1 NQ NR NB Hext Hvars E b HN) as (XK & _). fold s E' in XK.
    pose proof (cm_range E) as Hm.
    assert (Hcalls : (1 <= calls_of E <= 4)%nat /\ uE E' (EVar VK) = Z.of_nat (calls_of E)).
    { unfold uE. cbn [edenot]. rewrite XK. unfold calls_of. fold b. destruct b; [split; [lia | reflexivity]|]. split; [lia|]. rewrite Z2Nat.id by lia. reflexivity. }
    assert (Hcnt : cnt_of E' = cnt_of E).
    { unfold cnt_of, E', s. rewrite (ev_b1s VK VQ VR VN V1 NQ NR NB Hext Hvars E b). reflexivity. }
    rewrite <- Hcnt. exact (den_tgt VK neg E' (m_fs model) (calls_of E) (proj1 Hcalls) (proj2 Hcalls)).
  Qed.
End Drv.
