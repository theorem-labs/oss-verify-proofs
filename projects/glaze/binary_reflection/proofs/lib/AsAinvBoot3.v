(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.
From OSSVerify.glaze.binary_reflection.images Require Import Asan.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Notation u := bv_unsigned.
#[local] Abbreviation ASEGS := Asan.M.loaded_segments.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Record bvars := BVARS {
  b_g6 : Z;     (* [comment removed for export] *)
  b_w6 : Z;     (* [comment removed for export] *)
  b_g8 : Z;     (* [comment removed for export] *)
  b_g9 : Z;     (* [comment removed for export] *)
  b_g10 : Z;    (* [comment removed for export] *)
  b_g12 : Z;    (* [comment removed for export] *)
  b_g16 : Z;    (* [comment removed for export] *)
  b_g21 : Z;    (* [comment removed for export] *)
  b_g22 : Z;    (* [comment removed for export] *)
  b_top : Z;    (* [comment removed for export] *)
  b_hash : Z;   (* [comment removed for export] *)
  b_sz : Z;     (* [comment removed for export] *)
  b_aa : list (Z * Z);             (* [comment removed for export] *)
  b_maps0 : list (word * word);    (* [comment removed for export] *)
  b_noacc : list (word * word);    (* [comment removed for export] *)
  b_lazy : list (word * word);     (* [comment removed for export] *)
  b_mat : list word;               (* [comment removed for export] *)
  b_eager : Z;                     (* [comment removed for export] *)
  b_brk : word; b_sbrk : word; b_mbase : word; b_isp : word; b_resv : list (word * word)
}.

Section Boot.
  Context {RUN : run_ceil}.
  Variable h : bvars.
  #[local] Abbreviation P6 := (4096 * b_g6 h).
  Definition SPB : Z := 4096 * (b_g6 h + b_w6 h).
  #[local] Abbreviation E6 := 0x2000011000.

  (* [comment removed for export] *)
  Definition asan_dep0 : depot :=
    DEP 1 (fun b => if b =? b_hash h mod 2 ^ 20 then 1 else 0)
        (fun id => if id =? 1 then b_hash h else 0) (fun _ => 0) (fun id => if id =? 1 then 1 else 0)
        [] [] (b_sz h) (fun i => if i =? 0 then b_sz h else 0).

  (* [comment removed for export] *)
  Definition asan_fixed : list (Z * Z) :=
    [(P6, P6 + E6); (4096 * b_g8 h, 4096 * b_g8 h + 2 ^ 23); (4096 * b_g16 h, 4096 * b_g16 h + FAKE_SIZE);
     (4096 * b_g9 h, 4096 * b_g9 h + PG); (4096 * b_g21 h, 4096 * b_g21 h + 2 ^ 20); (4096 * b_g22 h, 4096 * b_g22 h + 2 ^ 23);
     (4096 * b_g10 h, 4096 * b_g10 h + 0x10000); (4096 * b_g12 h, 4096 * b_g12 h + PG)].

  Definition asan_bt : as_boot :=
    ASBOOT ASEGS asan_addrs SPB P6 E6 (4096 * b_g8 h) (4096 * b_g9 h) (4096 * b_g10 h) (4096 * b_g16 h)
           (ia_tp asan_addrs) (b_top h) (b_top h - 0x800000) (4096 * b_g21 h) (4096 * b_g22 h) asan_dep0 (b_aa h) (ia_tp asan_addrs) (4096 * b_g12 h)
           (asan_consts P6 SPB (4096 * b_g8 h) (4096 * b_g10 h))
           (b_maps0 h) (b_noacc h) (b_lazy h) (b_mat h) (b_eager h) (b_brk h) (b_sbrk h) (b_mbase h) (b_isp h) (b_resv h)
           asan_fixed.

  (* [comment removed for export] *)
  Definition apart (a n b m : Z) : Prop := a + n <= b \/ b + m <= a.
  (* [comment removed for export] *)
  Definition rng_ok (lo hi : Z) : Prop :=
    0 < lo /\ hi <= CEIL /\ (hi <= ia_img_lo asan_addrs \/ ia_img_hi asan_addrs <= lo) /\ (hi <= AS_LO \/ AS_HEAPLO <= lo).

  Definition vars_ok : Prop :=
    (* [comment removed for export] *)
    rng_ok P6 (P6 + E6) /\ rng_ok (4096 * b_g8 h) (4096 * b_g8 h + 2 ^ 23) /\ rng_ok (4096 * b_g16 h) (4096 * b_g16 h + FAKE_SIZE)
    /\ rng_ok (4096 * b_g9 h) (4096 * b_g9 h + PG) /\ rng_ok (4096 * b_g21 h) (4096 * b_g21 h + 2 ^ 20)
    /\ rng_ok (4096 * b_g22 h) (4096 * b_g22 h + 2 ^ 23) /\ rng_ok (4096 * b_g10 h) (4096 * b_g10 h + 0x10000)
    (* [comment removed for export] *)
    /\ apart (4096 * b_g21 h) 0x100000 (4096 * b_g22 h) 0x800000 /\ apart (4096 * b_g16 h) 0xb09000 (4096 * b_g22 h) 0x800000
    /\ apart (4096 * b_g10 h) 0x10000 (4096 * b_g22 h) 0x800000 /\ apart (4096 * b_g9 h) 0x1000 (4096 * b_g22 h) 0x800000
    /\ apart (4096 * b_g8 h) 0x800000 (4096 * b_g22 h) 0x800000 /\ apart P6 E6 (4096 * b_g22 h) 0x800000
    /\ apart (4096 * b_g16 h) 0xb09000 (4096 * b_g21 h) 0x100000 /\ apart (4096 * b_g10 h) 0x10000 (4096 * b_g21 h) 0x100000
    /\ apart (4096 * b_g9 h) 0x1000 (4096 * b_g21 h) 0x100000 /\ apart (4096 * b_g8 h) 0x800000 (4096 * b_g21 h) 0x100000
    /\ apart P6 E6 (4096 * b_g21 h) 0x100000
    /\ apart (4096 * b_g10 h) 0x10000 (4096 * b_g16 h) 0xb09000 /\ apart (4096 * b_g9 h) 0x1000 (4096 * b_g16 h) 0xb09000
    /\ apart (4096 * b_g8 h) 0x800000 (4096 * b_g16 h) 0xb09000 /\ apart P6 E6 (4096 * b_g16 h) 0xb09000
    /\ apart (4096 * b_g9 h) 0x1000 (4096 * b_g10 h) 0x10000 /\ apart (4096 * b_g8 h) 0x800000 (4096 * b_g10 h) 0x10000
    /\ apart P6 E6 (4096 * b_g10 h) 0x10000
    /\ apart (4096 * b_g8 h) 0x800000 (4096 * b_g9 h) 0x1000 /\ apart P6 E6 (4096 * b_g9 h) 0x1000
    /\ apart P6 E6 (4096 * b_g8 h) 0x800000
    (* [comment removed for export] *)
    /\ SPB mod 2 ^ 16 = 0 /\ 1 <= b_w6 h <= 16
    (* [comment removed for export] *)
    /\ (forall a, pg_in_ivz (b_lazy h) a -> 0 <= a < CEIL -> ~ in_band a ->
          (P6 <= a < P6 + E6) \/ (4096 * b_g8 h <= a < 4096 * b_g8 h + 2 ^ 23) \/ (4096 * b_g22 h <= a < 4096 * b_g22 h + 2 ^ 23))
    /\ (forall a, pg_in_ivz (b_lazy h) a -> 0 <= a < CEIL -> in_band a -> shmaps a \/ (AS_GAPLO <= a < AS_GAPHI))
    /\ (forall a, SPB + KSPACE <= a < SPB + KSPACE + PG -> ~ pg_in_ivz (b_lazy h) a)
    (* [comment removed for export] *)
    /\ (forall b n a, In (b, n) (b_maps0 h) -> u b <= a < u b + u n -> ~ (P6 <= a < P6 + E6))
    /\ Forall (fun e : word * word => 0 < u (snd e)) (b_maps0 h)
    (* [comment removed for export] *)
    /\ 0 <= b_hash h < 2 ^ 64 /\ 1 <= b_sz h <= 2 ^ 20
    (* [comment removed for export] *)
    /\ A_wf (b_aa h)
    /\ (forall lo hi, In (lo, hi) (SHC asan_addrs (4096 * b_g16 h)) -> range_allowed (b_aa h) lo hi)
    /\ range_allowed (b_aa h) (4096 * b_g22 h) (4096 * b_g22 h + 2 ^ 23)
    (* [comment removed for export] *)
    /\ rng_ok (4096 * b_g12 h) (4096 * b_g12 h + PG)
    /\ apart P6 E6 (4096 * b_g12 h) 0x1000 /\ apart (4096 * b_g8 h) 0x800000 (4096 * b_g12 h) 0x1000
    /\ apart (4096 * b_g16 h) 0xb09000 (4096 * b_g12 h) 0x1000 /\ apart (4096 * b_g9 h) 0x1000 (4096 * b_g12 h) 0x1000
    /\ apart (4096 * b_g21 h) 0x100000 (4096 * b_g12 h) 0x1000 /\ apart (4096 * b_g22 h) 0x800000 (4096 * b_g12 h) 0x1000
    /\ apart (4096 * b_g10 h) 0x10000 (4096 * b_g12 h) 0x1000.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition inb (ws : list (Z * Z)) (lo hi : Z) : bool := existsb (fun w => (fst w <=? lo) && (hi <=? snd w)) ws.
  Lemma inb_priv : forall IA lo hi, inb (ia_priv IA) lo hi = true -> priv_cover IA lo hi.
  Proof.
    intros IA lo hi Hb. unfold inb in Hb. apply existsb_exists in Hb. destruct Hb as ([plo phi] & Hin & Hc). cbn in Hc.
    apply andb_prop in Hc. destruct Hc as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. exists plo, phi. split; [exact Hin | lia].
  Qed.
  Lemma inb_const : forall IA lo hi, inb (ia_const IA) lo hi = true -> const_cover IA lo hi.
  Proof.
    intros IA lo hi Hb. unfold inb in Hb. apply existsb_exists in Hb. destruct Hb as ([plo phi] & Hin & Hc). cbn in Hc.
    apply andb_prop in Hc. destruct Hc as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. exists plo, phi. split; [exact Hin | lia].
  Qed.
  (* [comment removed for export] *)
  Definition coverb (IA : as_addrs) (c : Z * nat * Z) : bool :=
    inb (ia_priv IA) (fst (fst c)) (fst (fst c) + Z.of_nat (snd (fst c))) || inb (ia_const IA) (fst (fst c)) (fst (fst c) + Z.of_nat (snd (fst c))).
  Lemma coverb_ok : forall IA (cs : list (Z * nat * Z)), forallb (coverb IA) cs = true ->
    Forall (fun c => priv_cover IA (fst (fst c)) (fst (fst c) + Z.of_nat (snd (fst c))) \/ const_cover IA (fst (fst c)) (fst (fst c) + Z.of_nat (snd (fst c)))) cs.
  Proof.
    intros IA cs H. apply Forall_forall. intros c Hc. rewrite forallb_forall in H. specialize (H c Hc). unfold coverb in H.
    apply Bool.orb_prop in H. destruct H as [H|H]; [left; apply inb_priv; exact H | right; apply inb_const; exact H].
  Qed.
  (* [comment removed for export] *)
  Definition dyn_ivs (IA : as_addrs) : list (Z * Z) :=
    [(ia_instance IA + 112, ia_instance IA + 728); (ia_instance IA + 880, ia_instance IA + 888); (ia_instance IA + 888, ia_instance IA + 920);
     (ia_instance IA + 984, ia_instance IA + 992); (ia_depot_tab IA, ia_depot_tab IA + 0x400010 + 8 * 2 ^ 15);
     (ia_stackstore IA, ia_stackstore IA + 16 + 16 * 2 ^ 12); (ia_ialloc_flag IA, ia_ialloc_flag IA + 8); (ia_ialloc_inst IA, ia_ialloc_inst IA + IASZ)].
  Definition apartb (ivs : list (Z * Z)) (lo hi : Z) : bool := forallb (fun iv => (hi <=? fst iv) || (snd iv <=? lo)) ivs.
  Lemma apartb_dyn : forall IA lo hi, apartb (dyn_ivs IA) lo hi = true -> forall a, lo <= a < hi -> ~ img_dyn IA a.
  Proof.
    intros IA lo hi Hb a Ha Hd. unfold apartb, dyn_ivs in Hb. cbn [forallb fst snd] in Hb.
    repeat (apply andb_prop in Hb; destruct Hb as [?X Hb]);
    repeat match goal with H : (_ || _)%bool = true |- _ => apply Bool.orb_prop in H; destruct H as [H|H]; apply Z.leb_le in H end;
    unfold img_dyn in Hd; lia.
  Qed.
  Lemma apartb_consts : forall IA (cs : list (Z * nat * Z)), forallb (fun c : Z * nat * Z => apartb (dyn_ivs IA) (fst (fst c)) (fst (fst c) + Z.of_nat (snd (fst c)))) cs = true ->
    Forall (fun c => forall a, fst (fst c) <= a < fst (fst c) + Z.of_nat (snd (fst c)) -> ~ img_dyn IA a) cs.
  Proof.
    intros IA cs H. apply Forall_forall. intros c Hc. rewrite forallb_forall in H. exact (apartb_dyn IA _ _ (H c Hc)).
  Qed.
  (* [comment removed for export] *)
  Fixpoint sepsb (x : Z * Z) (l : list (Z * Z)) : bool :=
    match l with [] => true | y :: t => ((snd x <=? fst y) || (snd y <=? fst x)) && sepsb x t end.
  Fixpoint PWb (l : list (Z * Z)) : bool := match l with [] => true | x :: t => sepsb x t && PWb t end.
  Lemma sepsb_seps : forall x l, sepsb x l = true -> seps x l.
  Proof.
    intros x l; induction l as [|y t IH]; intros H; [exact I|]. cbn in H. apply andb_prop in H. destruct H as [H1 H2].
    split; [| exact (IH H2)]. apply Bool.orb_prop in H1. destruct H1 as [H1|H1]; apply Z.leb_le in H1; lia.
  Qed.
  Lemma PWb_PW : forall l, PWb l = true -> PW l.
  Proof. induction l as [|x t IH]; intros H; [exact I|]. cbn in H. apply andb_prop in H. destruct H as [H1 H2]. split; [exact (sepsb_seps _ _ H1) | exact (IH H2)]. Qed.
  Lemma seps_In : forall x l y, seps x l -> In y l -> snd x <= fst y \/ snd y <= fst x.
  Proof. intros x l; induction l as [|z t IH]; intros y Hs Hy; [destruct Hy|]. destruct Hs as [H1 H2]. destruct Hy as [<-|Hy]; [exact H1 | exact (IH y H2 Hy)]. Qed.
  Lemma splits_of_PW : forall l : list (Z * Z), PW l ->
    forall l1 x l2 y, l = l1 ++ x :: l2 -> In y (l1 ++ l2) -> snd x <= fst y \/ snd y <= fst x.
  Proof.
    induction l as [|z t IH]; intros HP l1 x l2 y E Hy.
    - destruct l1; discriminate E.
    - destruct HP as [Hz Ht]. destruct l1 as [|w l1'].
      + cbn in E. injection E as <- <-. cbn in Hy. exact (seps_In _ _ _ Hz Hy).
      + cbn in E. injection E as <- E'. destruct Hy as [<-|Hy].
        * pose proof (seps_In z t x Hz ltac:(rewrite E'; apply in_app_iff; right; left; reflexivity)). lia.
        * exact (IH Ht l1' x l2 y E' Hy).
  Qed.
  Lemma splits_of_PW' : forall l : list (Z * Z), PW l ->
    forall l1 l2 lo hi lo' hi', l = l1 ++ (lo, hi) :: l2 -> In (lo', hi') (l1 ++ l2) -> hi <= lo' \/ hi' <= lo.
  Proof. intros l HP l1 l2 lo hi lo' hi' E Hy. exact (splits_of_PW l HP l1 (lo, hi) l2 (lo', hi') E Hy). Qed.

  (* [comment removed for export] *)
  Hypothesis HOK : vars_ok.

  Lemma SPB_facts : SPB mod 2 ^ 16 = 0 /\ P6 + PG <= SPB <= P6 + 0x10000 /\ AS_HEAPLO <= SPB /\ SPB + KSPACE + PG <= CEIL /\ SPB + KSPACE + PG <= P6 + E6.
  Proof.
    pose proof HOK as ((A1 & A2 & A3 & A4) & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & AL & W6 & _).
    unfold SPB, AS_HEAPLO, AS_LO, KSPACE, PG in *. split; [exact AL|]. lia.
  Qed.

  Lemma asan_bt_ok : bt_ok asan_bt.
  Proof.
    (lazymatch goal with |- ?G => let G' := eval unfold bt_ok in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [bt_ia bt_tls_fs bt_consts asan_bt] in G in change_no_check G' end).
    split; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]. split; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval unfold AS_LO in G in change_no_check G' end); lia|].
    split. { intros plo phi [Hin|Hin]; cbn in Hin; intuition (try (match goal with H : (_, _) = (_, _) |- _ => injection H as <- <- end; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)). }
    split; [apply inb_priv; vm_compute; reflexivity|].
    split; [apply inb_priv; vm_compute; reflexivity|].
    split; [apply inb_priv; vm_compute; reflexivity|].
    split; [apply inb_priv; vm_compute; reflexivity|].
    split; [apply inb_priv; vm_compute; reflexivity|].
    split; [apply inb_priv; vm_compute; reflexivity|].
    split; [apply coverb_ok; vm_compute; reflexivity|].
    split; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]. split; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]. split; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]. split; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|].
    split; [apply apartb_consts; vm_compute; reflexivity|].
    split; [apply apartb_dyn; vm_compute; reflexivity|].
    split. { intros a [Ha|Ha]; revert a Ha; apply apartb_dyn; vm_compute; reflexivity. }
    apply splits_of_PW. apply PWb_PW. vm_compute. reflexivity.
  Qed.

  Lemma pg_mult : forall x, (4096 * x) mod 4096 = 0.
  Proof. intros x. rewrite Z.mul_comm. apply Z_mod_mult. Qed.
  Lemma pg_lin : forall x c, c mod 4096 = 0 -> (4096 * x + c) mod 4096 = 0.
  Proof. intros x c Hc. rewrite Z.add_comm, Z.mul_comm, Z_mod_plus_full. exact Hc. Qed.

  (* [comment removed for export] *)
  Ltac try_aparts :=
    match goal with
    | K : apart _ _ _ _ |- _ => first [ solve [generalize K; clear; (lazymatch goal with |- ?G => let G' := eval unfold apart, FAKE_SIZE, PG in G in change_no_check G' end); intros; lia] | clear K; try_aparts ]
    end.

  Lemma asan_wf_maps : wf_maps asan_bt (st0 asan_bt).
  Proof.
    pose proof HOK as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & REST).
    pose proof REST as (_ & _ & _ & _ & KS8 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R8 & D1 & D2 & D3 & D4 & D5 & D6 & D7).
    pose proof SPB_facts as (S1 & S2 & S3 & S4 & S5).
    (lazymatch goal with |- ?G => let G' := eval unfold wf_maps in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold all_ranges, dyn_ranges in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [bt_fixed asan_bt a_sec a_dep st0 dp_nodeblocks dp_storeblocks map app bt_dep0 asan_dep0] in G in change_no_check G' end).
    rewrite app_nil_r.
    (lazymatch goal with |- ?G => let G' := eval cbn [bt_resv6 bt_resv6_len bt_spacebeg bt_ptrarr bt_fs bt_thread bt_nodes0 bt_store0 bt_tctx bt_lazy0 bt_maps0 bt_ia bt_dtls asan_bt] in G in change_no_check G' end).
    split. { clear REST.
             intros lo hi Hin. unfold asan_fixed in Hin. cbn [In] in Hin. unfold dyn_ok, rng_ok in *.
             destruct Hin as [E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]; injection E as <- <-; unfold AS_HEAPLO, AS_LO, FAKE_SIZE, PG, KSPACE in *;
               (split; [lia|]); (split; [lia|]); (split; [apply pg_mult|]); apply pg_lin; reflexivity. }
    split. { destruct REST as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15 & K16 & K17 & K18 & K19 & K20 & K21 & _).
             clear R1 R2 R3 R4 R5 R6 R7 R8 S1 S2 S3 S4 S5 KS8.
             apply splits_of_PW'. (lazymatch goal with |- ?G => let G' := eval unfold asan_fixed in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [PW seps fst snd] in G in change_no_check G' end). repeat split; try exact I; try_aparts. }
    destruct REST as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LZ1 & LZ2 & LZ3 & M06 & M0K & _).
    split; [left; reflexivity|].
    split; [unfold PG in *; lia|]. split; [exact S5|].
    split; [right; left; reflexivity|].
    split; [right; right; left; reflexivity|].
    split; [do 3 right; left; reflexivity|].
    split; [do 4 right; left; reflexivity|]. split; [do 5 right; left; reflexivity|].
    split; [do 6 right; left; reflexivity|].
    split; [exact LZ1|]. split; [exact LZ2|]. split; [exact LZ3|]. split; [exact M06|]. split; [exact M0K|].
    split; [do 7 right; left; reflexivity|].
    split; [clear -KS8; unfold apart in KS8; lia|].
    split; [clear -D4; unfold apart, PG in *; lia|].
    intros b n lo hi _ [].
  Qed.

  Theorem asan_boot_ok : boot_ok asan_bt.
  Proof.
    pose proof HOK as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15
                      & K16 & K17 & K18 & K19 & K20 & K21 & AL & W6 & LZ1 & LZ2 & LZ3 & M06 & M0K & HH & HS & AW & ASHC & AST & _).
    pose proof SPB_facts as (S1 & S2 & S3 & S4 & S5).
    (lazymatch goal with |- ?G => let G' := eval unfold boot_ok in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [bt_spacebeg bt_fs bt_dep0 bt_aa0 bt_ia bt_store0 bt_thread bt_tctx bt_nodes0 bt_tls_fs bt_resv6_len asan_bt
                         dp_nids dp_tab dp_link dp_hash dp_store dp_nodeblocks dp_storeblocks dp_frames dp_stored asan_dep0
                         ia_instance ia_ialloc_inst ia_stackstore ia_depot_tab ia_ialloc_flag ia_tp asan_addrs] in G in change_no_check G' end).
    split; [exact S1|].
    split; [exact asan_wf_maps|].
    split; [(lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end); apply pg_mult|].
    split; [reflexivity|].
    split; [intros i; destruct (i =? b_hash h mod 2 ^ 20); lia|].
    split; [reflexivity|].
    split; [rewrite Z.eqb_refl; lia|].
    split; [rewrite Z.eqb_refl; lia|].
    split; [reflexivity|]. split; [reflexivity|].
    split; [lia|].
    split; [intros i; destruct (i =? 0); lia|].
    split; [intros i Hi; destruct (Z.eqb_spec i 0); [lia | reflexivity]|].
    split; [exact AW|]. split; [exact ASHC|]. split; [exact AST|].
    (lazymatch goal with |- ?G => let G' := eval unfold AS_LO, IASZ in G in change_no_check G' end). repeat (split; [lia|]).
    exact asan_bt_ok.
  Qed.


  Lemma asan_bt_consts : bt_consts asan_bt = asan_consts P6 SPB (4096 * b_g8 h) (4096 * b_g10 h). Proof. reflexivity. Qed.
  Lemma asan_bt_tctx : bt_tctx asan_bt = 4096 * b_g10 h. Proof. reflexivity. Qed.




End Boot.

(* [comment removed for export] *)
Ltac in_consts := rewrite ?asan_bt_consts; (lazymatch goal with |- ?G => let G' := eval unfold asan_consts in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [SPB] in G in change_no_check G' end);
  repeat (first [left; reflexivity | left; f_equal; lia | right]).
