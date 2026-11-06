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
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6 OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvHoleP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys7b. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsanNodesMmLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsanNodesLibE OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvFacts3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvLedger OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvHoleP3.AsAinvLedger2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvHoleP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys7 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys7b.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Notation u := bv_unsigned.

Definition noacc0_sub (bt : as_boot) : Prop :=
  forall a, in_ivz (bt_noacc0 bt) a -> in_resv6 bt a \/ in_ivz (bt_maps0 bt) a.

(* [comment removed for export] *)
Lemma Permutation_filter' : forall {A} (f : A -> bool) l l', Permutation l l' -> Permutation (List.filter f l) (List.filter f l').
Proof.
  intros A f l l' HP. induction HP; (lazymatch goal with |- ?G => let G' := eval cbn [List.filter] in G in change_no_check G' end).
  - constructor.
  - destruct (f x); [constructor; exact IHHP | exact IHHP].
  - destruct (f x), (f y); try apply Permutation_refl. constructor.
  - eapply Permutation_trans; eassumption.
Qed.
Lemma filter_all : forall {A} (f : A -> bool) l, (forall x, In x l -> f x = true) -> List.filter f l = l.
Proof. induction l as [|x t IH]; intros H; [reflexivity|]. (lazymatch goal with |- ?G => let G' := eval cbn [List.filter] in G in change_no_check G' end). rewrite (H x (or_introl eq_refl)). f_equal. apply IH. intros y Hy. apply H. right. exact Hy. Qed.

(* [comment removed for export] *)
Lemma munmap_vmmaps : forall addr n m, vm_maps (m_vmmaps (munmap_model addr n m)) = map_remove (vm_maps (m_vmmaps m)) addr
  /\ vm_noaccess (m_vmmaps (munmap_model addr n m)) = maps_subtract (vm_noaccess (m_vmmaps m)) (u addr) (u addr + u n)
  /\ vm_reserved (m_vmmaps (munmap_model addr n m)) = vm_reserved (m_vmmaps m) /\ vm_brk (m_vmmaps (munmap_model addr n m)) = vm_brk (m_vmmaps m)
  /\ vm_start_brk (m_vmmaps (munmap_model addr n m)) = vm_start_brk (m_vmmaps m) /\ vm_mmap_base (m_vmmaps (munmap_model addr n m)) = vm_mmap_base (m_vmmaps m)
  /\ vm_init_sp (m_vmmaps (munmap_model addr n m)) = vm_init_sp (m_vmmaps m) /\ vm_limit (m_vmmaps (munmap_model addr n m)) = vm_limit (m_vmmaps m).
Proof. intros. (lazymatch goal with |- ?G => let G' := eval unfold munmap_model, with_mmap_destroyed in G in change_no_check G' end). model_proj. (lazymatch goal with |- ?G => let G' := eval cbn [vm_maps vm_noaccess vm_reserved vm_brk vm_start_brk vm_mmap_base vm_init_sp vm_limit] in G in change_no_check G' end). repeat split; reflexivity. Qed.
Lemma munmap_lazy : forall addr n m, m_vm_lazy (munmap_model addr n m) = maps_subtract (m_vm_lazy m) (u addr) (u addr + u n).
Proof. intros. (lazymatch goal with |- ?G => let G' := eval unfold munmap_model, with_mmap_destroyed in G in change_no_check G' end). model_proj. reflexivity. Qed.
Lemma munmap_mat : forall addr n m,
  m_vm_materialized (munmap_model addr n m) = List.filter (page_outside_range (u addr) (u addr + u n)) (m_vm_materialized m).
Proof. intros. (lazymatch goal with |- ?G => let G' := eval unfold munmap_model, with_mmap_destroyed in G in change_no_check G' end). model_proj. reflexivity. Qed.

Definition w2 (r : Z * Z) : word * word := (Z_to_bv 64 (fst r), Z_to_bv 64 (snd r - fst r)).
Lemma dyn_maps_w2 : forall st, dyn_maps st = map w2 (dyn_ranges st).
Proof.
  intros st. (lazymatch goal with |- ?G => let G' := eval unfold dyn_maps, dyn_ranges in G in change_no_check G' end). rewrite !map_app, !map_map. f_equal; [| f_equal]; apply map_ext; intros x; (lazymatch goal with |- ?G => let G' := eval unfold w2 in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [fst snd] in G in change_no_check G' end); f_equal; f_equal; lia.
Qed.

Lemma sum_count_ext_in : forall P Q l,
  (forall e x, In e l -> u (fst e) <= x < u (fst e) + u (snd e) -> P x = Q x) -> sum_count P l = sum_count Q l.
Proof.
  induction l as [|e t IH]; intros H; [reflexivity|]. (lazymatch goal with |- ?G => let G' := eval cbn [sum_count] in G in change_no_check G' end). rewrite IH by (intros e' x He' Hx; exact (H e' x (or_intror He') Hx)).
  f_equal. (lazymatch goal with |- ?G => let G' := eval unfold iv_count in G in change_no_check G' end). apply zcount_ext. intros x Hx. apply (H e x (or_introl eq_refl)). unfold B, S in Hx.
  pose proof (bv_unsigned_in_range 64 (snd e)). rewrite Z2Nat.id in Hx by lia. exact Hx.
Qed.

Section SecFree.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  #[local] Abbreviation IA := (bt_ia bt).
  Variables (st : ast) (Lc FF : list (Z * Z)) (M0 : mem) (mdl : Model) (s : schunk).
  Context {qt qg : Z}.
  Hypothesis W : WFq bt st Lc FF qt qg.
  Hypothesis R : Rep bt st Lc FF M0 mdl.
  Hypothesis MW : model_ivs_wf mdl.
  Hypothesis Hs : In s (a_sec st).
  Hypothesis NS : noacc0_sub bt.
  #[local] Notation lo := (sc_map s).
  #[local] Notation hi := (sc_map s + sc_mapsz s).
  #[local] Notation addr := (Z_to_bv 64 (sc_map s)).
  #[local] Notation n := (Z_to_bv 64 (sc_mapsz s)).

  Lemma sec_lits : 0 < lo /\ hi <= CEIL /\ hi < 2 ^ 64 /\ lo mod 4096 = 0 /\ hi mod 4096 = 0 /\ 0 < sc_mapsz s /\ u addr = lo /\ u n = sc_mapsz s.
  Proof.
    destruct (sec_facts bt st Lc FF W s Hs) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8). pose proof ceil_rng as CR. unfold PG in *.
    assert (P : 0 < sc_mapsz s) by lia.
    repeat split; try lia; try (rewrite u64_lit; lia). apply mod0_add; [lia | exact A3 | exact A4].
  Qed.

  (* [comment removed for export] *)
  Lemma sec_rest : exists REST, Permutation (vm_maps (m_vmmaps mdl)) ((addr, n) :: REST)
    /\ (forall e, In e REST -> 0 < u (snd e) /\ (u (fst e) + u (snd e) <= lo \/ hi <= u (fst e))).
  Proof.
    destruct sec_lits as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8).
    destruct (ledger_R bt st Lc FF M0 mdl R) as ((F6 & PM & FOK & FSEP & FCOV) & _).
    pose proof W as (_ & _ & _ & _ & _ & _ & _ & _ & WM & _).
    destruct WM as (RNG & PWS & IN6 & R6a & R6b & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & M0POS & _ & _ & _ & M0DYN).
    assert (HD : In (lo, hi) (dyn_ranges st)) by exact (sec_dyn st s Hs).
    destruct (in_split s (a_sec st) Hs) as (s1 & s2 & ES).
    set (g := fun s0 : schunk => (sc_map s0, sc_map s0 + sc_mapsz s0)).
    set (D1 := map g s1).
    set (D2 := map g s2 ++ map (fun b => (b, b + 2 ^ 20)) (dp_nodeblocks (a_dep st)) ++ map (fun b => (b, b + 2 ^ 23)) (dp_storeblocks (a_dep st))).
    assert (ED : dyn_ranges st = D1 ++ (lo, hi) :: D2).
    { (lazymatch goal with |- ?G => let G' := eval unfold dyn_ranges, D1, D2 in G in change_no_check G' end). rewrite ES, map_app. (lazymatch goal with |- ?G => let G' := eval cbn [map] in G in change_no_check G' end). rewrite <- app_assoc. reflexivity. }
    exists (F6 ++ bt_maps0 bt ++ map w2 D1 ++ map w2 D2). split.
    - eapply Permutation_trans; [exact PM|]. rewrite dyn_maps_w2, ED, map_app. (lazymatch goal with |- ?G => let G' := eval cbn [map] in G in change_no_check G' end). unfold w2 at 2. (lazymatch goal with |- ?G => let G' := eval cbn [fst snd] in G in change_no_check G' end).
      replace (lo + sc_mapsz s - lo) with (sc_mapsz s) by lia.
      rewrite !app_assoc. apply Permutation_sym. apply Permutation_middle.
    - intros [b m] He. (lazymatch goal with |- ?G => let G' := eval cbn [fst snd] in G in change_no_check G' end). apply in_app_iff in He as [He | He]; [| apply in_app_iff in He as [He | He]].
      + rewrite Forall_forall in FOK. destruct (FOK (b, m) He) as (F1 & F2 & F3 & _). cbn [fst snd] in F1, F2, F3.
        split; [lia|]. destruct (fixed_dyn_sep bt st Lc FF W _ _ _ _ IN6 HD) as [S|S]; [left; lia | right; lia].
      + rewrite Forall_forall in M0POS. pose proof (M0POS (b, m) He) as Pn. cbn [snd] in Pn. split; [exact Pn|].
        destruct (M0DYN b m lo hi He HD) as [S|S]; [right; exact S | left; exact S].
      + assert (HR : exists dl dh, In (dl, dh) (D1 ++ D2) /\ b = Z_to_bv 64 dl /\ m = Z_to_bv 64 (dh - dl)).
        { rewrite <- map_app in He. apply in_map_iff in He as ([dl dh] & E & Hin). unfold w2 in E. cbn [fst snd] in E. injection E as <- <-. exists dl, dh. repeat split; [exact Hin|..]; reflexivity. }
        destruct HR as (dl & dh & Hin & -> & ->).
        assert (HDI : In (dl, dh) (dyn_ranges st)) by (rewrite ED; apply in_app_iff in Hin as [H|H]; apply in_app_iff; [left; exact H | right; right; exact H]).
        destruct (RNG dl dh (all_ranges_dyn bt st _ HDI)) as ((D1' & D2' & D3' & _) & D6 & _).
        pose proof ceil_rng as CR. rewrite !u64_lit by lia. split; [lia|].
        assert (EA : all_ranges bt st = (bt_fixed bt ++ D1) ++ (lo, hi) :: D2) by ((lazymatch goal with |- ?G => let G' := eval unfold all_ranges in G in change_no_check G' end); rewrite ED, <- app_assoc; reflexivity).
        assert (HIN2 : In (dl, dh) ((bt_fixed bt ++ D1) ++ D2)).
        { apply in_app_iff in Hin as [H|H]; apply in_app_iff; [left; apply in_app_iff; right; exact H | right; exact H]. }
        destruct (PWS _ _ lo hi dl dh EA HIN2) as [S|S]; [right; lia | left; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma sec_map_has : map_has (vm_maps (m_vmmaps mdl)) addr n = true.
  Proof.
    destruct sec_rest as (REST & PM & _). apply map_has_intro. apply (Permutation_in _ (Permutation_sym PM)). left. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma sec_no_noacc : forall a, lo <= a < hi -> ~ in_ivz (vm_noaccess (m_vmmaps mdl)) a.
  Proof.
    intros a Ha Hn. destruct (ledger_R bt st Lc FF M0 mdl R) as (_ & NA & _). destruct (proj1 (NA a) Hn) as (N0 & _ & _).
    pose proof W as (_ & _ & _ & _ & _ & _ & _ & _ & WM & _).
    destruct WM as (RNG & PWS & IN6 & R6a & R6b & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & M0POS & _ & _ & _ & M0DYN).
    assert (HD : In (lo, hi) (dyn_ranges st)) by exact (sec_dyn st s Hs).
    destruct (NS a N0) as [I6 | (b & m & Hin & Hr)].
    - unfold in_resv6 in I6. destruct (fixed_dyn_sep bt st Lc FF W _ _ _ _ IN6 HD) as [S|S]; lia.
    - destruct (M0DYN b m lo hi Hin HD) as [S|S]; lia.
  Qed.
  Lemma sec_no_lazy : forall a, lo <= a < hi -> ~ pg_in_ivz (m_vm_lazy mdl) a.
  Proof.
    intros a Ha [Hr Hl]. pose proof (rep_nolazy_sec bt st Lc FF M0 mdl W R s a Hs Ha) as NL. unfold lzb in NL. rewrite NL in Hl. discriminate Hl.
  Qed.

  (* [comment removed for export] *)
  Section Child.
    Variables mdlk mdl' : Model.
    Hypothesis EKV : m_vmmaps mdlk = m_vmmaps mdl.
    Hypothesis EKL : m_vm_lazy mdlk = m_vm_lazy mdl.
    Hypothesis SBM' : same_but_materialized (munmap_model addr n mdlk) mdl'.

    Lemma child_eqs : vm_maps (m_vmmaps mdl') = map_remove (vm_maps (m_vmmaps mdl)) addr
      /\ vm_noaccess (m_vmmaps mdl') = maps_subtract (vm_noaccess (m_vmmaps mdl)) lo hi
      /\ m_vm_lazy mdl' = maps_subtract (m_vm_lazy mdl) lo hi.
    Proof.
      destruct sec_lits as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8).
      destruct (sbm_vmmaps _ mdl' SBM') as [E3 E4]. destruct (munmap_vmmaps addr n mdlk) as (V1 & V2 & _).
      rewrite E3, E4, V1, V2, munmap_lazy, EKV, EKL, L7, L8. repeat split; reflexivity.
    Qed.

    Lemma secfree_perm : Permutation ((addr, n) :: vm_maps (m_vmmaps mdl')) (vm_maps (m_vmmaps mdl)).
    Proof.
      destruct sec_lits as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8). destruct child_eqs as (E1 & _). rewrite E1.
      destruct sec_rest as (REST & PM & AP). (lazymatch goal with |- ?G => let G' := eval unfold map_remove in G in change_no_check G' end).
      apply Permutation_sym. eapply Permutation_trans; [exact PM|]. constructor.
      eapply Permutation_trans; [| apply Permutation_filter'; apply Permutation_sym; exact PM].
      (lazymatch goal with |- ?G => let G' := eval cbn [List.filter fst] in G in change_no_check G' end). rewrite bv_eqb_refl. (lazymatch goal with |- ?G => let G' := eval cbn [negb] in G in change_no_check G' end).
      rewrite filter_all; [apply Permutation_refl|]. intros [b m] He. (lazymatch goal with |- ?G => let G' := eval cbn [fst] in G in change_no_check G' end). destruct (AP _ He) as [P0 AP']. cbn [fst snd] in P0, AP'.
      rewrite bv_eqb_neq; [reflexivity|]. intros E. subst b. rewrite L7 in AP'. lia.
    Qed.

    Lemma secfree_ledger :
      (forall a, in_ivz (vm_noaccess (m_vmmaps mdl')) a <-> in_ivz (vm_noaccess (m_vmmaps mdl)) a)
      /\ Forall (fun e : word * word => 0 < bv_unsigned (snd e)) (vm_noaccess (m_vmmaps mdl'))
      /\ (forall a, pg_in_ivz (m_vm_lazy mdl') a <-> pg_in_ivz (m_vm_lazy mdl) a)
      /\ Forall (fun iv : word * word => bv_unsigned (fst iv) mod PG = 0 /\ bv_unsigned (snd iv) mod PG = 0
                                     /\ 0 < bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= CEIL
                                     /\ (bv_unsigned (fst iv) + bv_unsigned (snd iv) <= ia_img_lo (bt_ia bt) \/ ia_img_hi (bt_ia bt) <= bv_unsigned (fst iv)))
                (m_vm_lazy mdl')
      /\ vm_reserved (m_vmmaps mdl') = vm_reserved (m_vmmaps mdl) /\ vm_brk (m_vmmaps mdl') = vm_brk (m_vmmaps mdl)
      /\ vm_start_brk (m_vmmaps mdl') = vm_start_brk (m_vmmaps mdl) /\ vm_mmap_base (m_vmmaps mdl') = vm_mmap_base (m_vmmaps mdl)
      /\ vm_init_sp (m_vmmaps mdl') = vm_init_sp (m_vmmaps mdl) /\ vm_limit (m_vmmaps mdl') = vm_limit (m_vmmaps mdl).
    Proof.
      destruct sec_lits as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8). destruct child_eqs as (_ & E2 & E3).
      destruct MW as (Wm & Wn & Wl & _). destruct (ledger_R bt st Lc FF M0 mdl R) as (_ & _ & _ & LOK & _ & _ & _ & _ & _ & _ & _ & NPOS).
      split. { intros a. rewrite E2. rewrite in_ivz_maps_subtract by lia. split; [intros [H _]; exact H | intros H; split; [exact H | intros Ha; exact (sec_no_noacc a Ha H)]]. }
      split. { rewrite E2. apply ivs_pos_subtract. exact NPOS. }
      split. { intros a. rewrite E3. rewrite (pg_in_ivz_subtract _ lo hi a Wl L4 L5 ltac:(lia)). split; [intros [H _]; exact H | intros H; split; [exact H | intros Ha; exact (sec_no_lazy a Ha H)]]. }
      split. { rewrite E3. apply (lazy_ok_subtract CEIL (ia_img_lo IA) (ia_img_hi IA)); [exact Wl | exact L4 | exact L5 | lia | lia | lia | exact LOK]. }
      destruct (sbm_vmmaps _ mdl' SBM') as [E5 _]. destruct (munmap_vmmaps addr n mdlk) as (_ & _ & V3 & V4 & V5 & V6 & V7 & V8).
      rewrite E5, V3, V4, V5, V6, V7, V8, EKV. repeat split; reflexivity.
    Qed.

    (* [comment removed for export] *)
    Lemma sec_no_lazy_byte : forall x, lo <= x < hi -> covered (m_vm_lazy mdl) x = false.
    Proof.
      intros x Hx. destruct sec_lits as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8).
      destruct (covered (m_vm_lazy mdl) x) eqn:C; [exfalso | reflexivity].
      apply in_ivz_covered in C. destruct C as (b & m & Hin & Hr).
      destruct (ledger_R bt st Lc FF M0 mdl R) as (_ & _ & _ & LOK & _). rewrite Forall_forall in LOK.
      destruct (LOK (b, m) Hin) as (A1 & A2 & A3 & A4 & _). cbn [fst snd] in *. unfold PG in *.
      apply (sec_no_lazy x Hx). split; [lia|].
      pose proof (page_of_byte_in_aligned (Z_to_bv 64 x) (u b) (u b + u m) A1 (mod0_add _ _ 4096 ltac:(lia) A1 A2) ltac:(rewrite u64_lit by lia; exact Hr)) as [P1 P2].
      apply page_in_ranges_true. exists (b, m). split; [exact Hin|]. (lazymatch goal with |- ?G => let G' := eval cbn [fst snd] in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold page_size in G in change_no_check G' end). lia.
    Qed.

    Lemma child_wf : model_ivs_wf mdl'.
    Proof.
      destruct sec_lits as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8). destruct child_eqs as (E1 & E2 & E3). destruct MW as (Wm & Wn & Wl & Wsp).
      destruct secfree_ledger as (_ & _ & _ & _ & _ & _ & _ & _ & ESP & _).
      (lazymatch goal with |- ?G => let G' := eval unfold model_ivs_wf in G in change_no_check G' end). rewrite E1, E2, E3. (lazymatch goal with |- ?G => let G' := eval unfold map_remove in G in change_no_check G' end).
      split; [apply ivs_wf_filter; exact Wm|]. split; [apply maps_subtract_wf; [exact Wn | lia]|]. split; [apply maps_subtract_wf; [exact Wl | lia]|].
      eapply BackingAlgebra.AsanCeil.init_sp_ok_same; [| exact Wsp]. exact ESP.
    Qed.

    (* [comment removed for export] *)
    Theorem secfree_eager : eager_used mdl' + sc_mapsz s <= eager_used mdl.
    Proof.
      destruct sec_lits as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8). destruct child_eqs as (E1 & E2 & E3). pose proof MW as (Wm & Wn & Wl & Wsp).
      rewrite (eager_used_sem _ child_wf), (eager_used_sem _ MW).
      destruct sec_rest as (REST & PM & AP).
      assert (PM' : Permutation (vm_maps (m_vmmaps mdl')) REST).
      { apply (Permutation_cons_inv (a := (addr, n))). eapply Permutation_trans; [exact secfree_perm | exact PM]. }
      rewrite (sum_count_perm _ _ _ PM'), (sum_count_perm _ _ _ PM). (lazymatch goal with |- ?G => let G' := eval cbn [sum_count] in G in change_no_check G' end). rewrite E2, E3.
      destruct (maps_subtract_sem _ lo hi Wn ltac:(lia)) as (_ & _ & Cn). destruct (maps_subtract_sem _ lo hi Wl ltac:(lia)) as (_ & _ & Cl).
      assert (EQR : sum_count (fun x => negb (covered (maps_subtract (vm_noaccess (m_vmmaps mdl)) lo hi ++ maps_subtract (m_vm_lazy mdl) lo hi) x)) REST
                    = sum_count (fun x => negb (covered (vm_noaccess (m_vmmaps mdl) ++ m_vm_lazy mdl) x)) REST).
      { apply sum_count_ext_in. intros e x He Hx. destruct (AP e He) as [_ AP']. rewrite !covered_app, Cn, Cl.
        assert (IR : in_rng lo hi x = false) by ((lazymatch goal with |- ?G => let G' := eval unfold in_rng in G in change_no_check G' end); apply andb_false_iff; destruct AP'; [left; apply Z.leb_gt; lia | right; apply Z.ltb_ge; lia]).
        rewrite IR. (lazymatch goal with |- ?G => let G' := eval cbn [negb] in G in change_no_check G' end). rewrite !andb_true_r. reflexivity. }
      rewrite EQR.
      assert (FULL : iv_count (fun x => negb (covered (vm_noaccess (m_vmmaps mdl) ++ m_vm_lazy mdl) x)) (addr, n) = sc_mapsz s).
      { (lazymatch goal with |- ?G => let G' := eval unfold iv_count, B, S in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [fst snd] in G in change_no_check G' end). rewrite L7, L8. rewrite zcount_true; [apply Z2Nat.id; lia|].
        intros x Hx. rewrite Z2Nat.id in Hx by lia. rewrite covered_app, (sec_no_lazy_byte x Hx), orb_false_r.
        destruct (covered (vm_noaccess (m_vmmaps mdl)) x) eqn:C; [exfalso | reflexivity].
        apply in_ivz_covered in C. exact (sec_no_noacc x Hx C). }
      rewrite FULL. lia.
    Qed.
  End Child.

  (* [comment removed for export] *)
  Theorem child_MInv : forall A mdlk, m_vmmaps mdlk = m_vmmaps mdl -> m_vm_lazy mdlk = m_vm_lazy mdl ->
    MInv A mdlk -> MInv A (munmap_model addr n mdlk).
  Proof.
    intros A mdlk EKV EKL [N1 N2 N3 N4 N5]. destruct sec_lits as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8). pose proof MW as (_ & _ & Wl & _).
    pose proof (secfree_eager mdlk _ EKV EKL (same_but_materialized_refl _)) as EG.
    constructor; rewrite ?munmap_mat, ?munmap_lazy.
    - apply NoDup_filter. exact N1.
    - intros p Hp. apply filter_In in Hp as [Hp _]. exact (N2 p Hp).
    - intros p Hp. apply filter_In in Hp as [Hp _]. exact (N3 p Hp).
    - intros p Hp. apply filter_In in Hp as [Hin Hout]. rewrite EKL.
      rewrite page_in_ranges_subtract_out; [rewrite <- EKL; exact (N4 p Hin) | exact Wl | rewrite L7, L8; lia |].
      unfold page_outside_range in Hout. apply negb_true_iff in Hout. pose proof (N2 p Hin) as Ap. unfold page_size in *. rewrite L7, L8 in *.
      apply andb_false_iff in Hout as [Hout|Hout]; [apply Z.leb_gt in Hout | apply Z.ltb_ge in Hout].
      + left. apply aligned_lt_step; assumption.
      + right. exact Hout.
    - destruct (munmap_vmmaps addr n mdlk) as (_ & _ & _ & _ & _ & _ & _ & V8). rewrite V8.
      assert (eager_used mdlk = eager_used mdl) by (apply eager_used_ext; assumption). lia.
  Qed.
End SecFree.
