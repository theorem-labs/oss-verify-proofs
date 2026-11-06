(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import AsanAcct.   (* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatSim Scfg ShapeAlg SpinAlg MmapSim RefNodes AsanAcctShape KitNodesS.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require BackingAlgebra AsanCeil AsanPlacement.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Madvise.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import AsanNodesLibEK AsanNodesMmLibK AsanNodesMadvK ArtRuns.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module BA := BackingAlgebra.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma eager_used_ext : forall m1 m2,
  m_vmmaps m1 = m_vmmaps m2 -> m_vm_lazy m1 = m_vm_lazy m2 -> eager_used m1 = eager_used m2.
Proof. intros m1 m2 H1 H2. unfold eager_used. rewrite H1, H2. reflexivity. Qed.

Lemma vbu_nomat : forall m, m_vm_materialized m = [] -> vm_backing_used m = eager_used m.
Proof. intros m H. rewrite vm_backing_used_split, H. cbn [length Z.of_nat]. lia. Qed.

Lemma eager_used_as_vbu : forall m,
  eager_used m = vm_backing_used (with_vm_backing (m_vm_lazy m) [] m).
Proof. intros m. rewrite vbu_nomat by reflexivity. apply eager_used_ext; reflexivity. Qed.

(* [comment removed for export] *)
Lemma eager_grant_le : forall m (a n : word) h',
  BA.model_ivs_wf m ->
  bv_unsigned a + bv_unsigned n <= 2 ^ 64 ->
  vm_maps h' = (a, n) :: vm_maps (m_vmmaps m) ->
  vm_noaccess h' = vm_noaccess (m_vmmaps m) ->
  eager_used (with_vmmaps h' m) <= eager_used m + bv_unsigned n.
Proof.
  intros m a n h' (Wm & Wn & Wl) Hend Hmaps Hna.
  unfold eager_used, vm_backed_maps. rewrite BA.m_vmmaps_with_vmmaps, BA.m_vm_lazy_with_vmmaps.
  rewrite Hmaps, Hna.
  rewrite BA.maps_subtract_all_cons_l, BA.maps_subtract_all_app, BA.live_bytes_app.
  match goal with |- ?x + ?y <= ?y' + ?nn => enough (x <= nn) by lia end.
  rewrite <- BA.maps_subtract_all_app_cuts.
  assert (W1 : BA.ivs_wf [(a, n)]) by (apply BA.ivs_wf_cons; [exact Hend|apply BA.ivs_wf_nil]).
  destruct (BA.live_msa (vm_noaccess (m_vmmaps m) ++ m_vm_lazy m) [(a, n)] W1) as [-> _].
  cbn [BA.sum_count]. unfold BA.iv_count, BA.B, BA.S. cbn [fst snd].
  pose proof (BA.zcount_le_len (fun x => negb (BA.covered (vm_noaccess (m_vmmaps m) ++ m_vm_lazy m) x)) (bv_unsigned a) (Z.to_nat (bv_unsigned n))) as Hz.
  pose proof (bv_unsigned_in_range 64 n). rewrite Z2Nat.id in Hz by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma eager_commit_le : forall m h' lo hi,
  BA.model_ivs_wf m -> lo <= hi ->
  vm_maps h' = vm_maps (m_vmmaps m) ->
  vm_noaccess h' = maps_subtract (vm_noaccess (m_vmmaps m)) lo hi ->
  eager_used (vm_forget_range lo hi (with_vmmaps h' m)) <= eager_used m + BA.overlap_sum (vm_maps (m_vmmaps m)) lo hi.
Proof.
  intros m h' lo hi Hwf Hlh Hmaps Hna.
  rewrite (eager_used_as_vbu m).
  pose proof (BA.backing_forget_commit_le (with_vm_backing (m_vm_lazy m) [] m) h' lo hi Hwf Hlh Hmaps Hna) as HB.
  eapply Z.le_trans; [|exact HB].
  rewrite vbu_nomat by reflexivity. apply Z.eq_le_incl. apply eager_used_ext; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma eager_recommit_le : forall m h' (a n : word),
  BA.model_ivs_wf m ->
  bv_unsigned a mod page_size = 0 -> bv_unsigned n mod page_size = 0 ->
  0 < bv_unsigned n -> bv_unsigned a + bv_unsigned n <= 2 ^ 64 ->
  vm_maps h' = vm_maps (m_vmmaps m) ->
  vm_noaccess h' = maps_subtract (vm_noaccess (m_vmmaps m)) (bv_unsigned a) (bv_unsigned a + bv_unsigned n) ->
  eager_used (vm_add_lazy a n (vm_forget_range (bv_unsigned a) (bv_unsigned a + bv_unsigned n) (with_vmmaps h' m)))
  <= eager_used m.
Proof.
  intros m h' a n Hwf Hal Hnl Hpos Hend Hmaps Hna.
  rewrite (eager_used_as_vbu m).
  pose proof (BA.backing_recommit_lazy_le (with_vm_backing (m_vm_lazy m) [] m) h' a n Hwf Hal Hnl Hpos Hend Hmaps Hna) as HB.
  eapply Z.le_trans; [|exact HB].
  rewrite vbu_nomat by reflexivity. apply Z.eq_le_incl. apply eager_used_ext; reflexivity.
Qed.

(* [comment removed for export] *)
Definition munmap_vmmaps (a n : word) (h : VmMaps) : VmMaps :=
  mkVmMapsFull (vm_reserved h) (map_remove (vm_maps h) a)
    (maps_subtract (vm_noaccess h) (bv_unsigned a) (bv_unsigned a + bv_unsigned n))
    (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h).

Lemma munmap_model_eq : forall a n m,
  munmap_model a n m = vm_forget_range (bv_unsigned a) (bv_unsigned a + bv_unsigned n) (with_vmmaps (munmap_vmmaps a n (m_vmmaps m)) m).
Proof. reflexivity. Qed.

Lemma munmap_model_wf : forall a n m, BA.model_ivs_wf m -> BA.model_ivs_wf (munmap_model a n m).
Proof.
  intros a n m Hwf. rewrite munmap_model_eq.
  pose proof (bv_unsigned_in_range 64 n) as Hn.
  apply BA.model_ivs_wf_vm_forget_range; [lia|].
  destruct Hwf as (Wm & Wn & Wl & Wsp).
  apply BA.model_ivs_wf_with_vmmaps; [repeat split; assumption | | | reflexivity].
  - cbn [munmap_vmmaps vm_maps]. unfold map_remove. apply BA.ivs_wf_filter. exact Wm.
  - cbn [munmap_vmmaps vm_noaccess]. apply BA.maps_subtract_wf; [exact Wn | lia].
Qed.

Lemma eager_unmap_le : forall m (a n : word),
  BA.model_ivs_wf m ->
  (forall q, In q (vm_maps (m_vmmaps m)) -> bv_eqb (fst q) a = false ->
     BA.B q + BA.S q <= bv_unsigned a \/ bv_unsigned a + bv_unsigned n <= BA.B q) ->
  eager_used (munmap_model a n m) <= eager_used m.
Proof.
  intros m a n Hwf Hap.
  pose proof (munmap_model_wf a n m Hwf) as Hwf'.
  rewrite (eager_used_sem _ Hwf'), (eager_used_sem _ Hwf).
  rewrite munmap_model_eq. BA.model_proj. cbn [munmap_vmmaps vm_maps vm_noaccess].
  pose proof (bv_unsigned_in_range 64 n) as Hn.
  destruct Hwf as (Wm & Wn & Wl & Wsp).
  set (lo := bv_unsigned a). set (hi := lo + bv_unsigned n).
  destruct (BA.maps_subtract_sem _ lo hi Wn ltac:(subst hi; lia)) as (_ & _ & Cn).
  destruct (BA.maps_subtract_sem _ lo hi Wl ltac:(subst hi; lia)) as (_ & _ & Cl).
  unfold map_remove. apply sum_count_filter_le.
  intros q Hq Hf x Hx. apply negb_true_iff in Hf.
  assert (Hout : BA.in_rng lo hi x = false).
  { unfold BA.in_rng. destruct (Hap q Hq Hf) as [H|H]; subst lo hi.
    - apply andb_false_iff. left. apply Z.leb_gt. lia.
    - apply andb_false_iff. right. apply Z.ltb_ge. lia. }
  rewrite !BA.covered_app, Cn, Cl, Hout. cbn [negb]. rewrite !andb_true_r. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Grows.
Variable segs : list Segment.

Lemma interp_eff_accesses_grows : forall (t : Sem.eff) m c m' rs,
  interp_eff_accesses segs t m = MachineOk (@mkAccessReport _ (c, m') rs) -> StoreOk.mem_grows m m'.
Proof.
  intros t. induction t as [c0 | c0 | c0 | c0 | c0 | c0 | n a k IH | n a v k IH];
    intros m c m' rs Hi; cbn [interp_eff_accesses] in Hi; try discriminate.
  - injection Hi as <- <- <-. apply StoreOk.mem_grows_refl.
  - destruct (ov_read_bytes segs m a (width_bytes n)) as [bs|]; [|discriminate].
    destruct (interp_eff_accesses segs (k (bv_extract 0 n (le_bytes_to_word bs))) m) as [[[c1 m1] rs1]| |] eqn:Hk; try discriminate.
    cbn [access_value accessed_ranges] in Hi. injection Hi as <- <- <-. exact (IH _ m c1 m1 rs1 Hk).
  - destruct (store_ok segs m a (width_bytes n)); [|discriminate].
    destruct (interp_eff_accesses segs k (write_to_mem m a (Z_to_le_bytes (width_bytes n) (bv_unsigned v)))) as [[[c1 m1] rs1]| |] eqn:Hk; try discriminate.
    cbn [access_value accessed_ranges] in Hi. injection Hi as <- <- <-.
    eapply StoreOk.mem_grows_trans; [apply StoreOk.write_to_mem_grows | exact (IH _ c1 m1 rs1 Hk)].
Qed.

Lemma step_mem_grows : forall ms ms',
  RiscvSemantics.step segs ms = MachineOk ms' -> StoreOk.mem_grows (ms_mem ms) (ms_mem ms').
Proof.
  intros ms ms' Hs. unfold RiscvSemantics.step, drop_access_report in Hs.
  destruct (step_accesses segs ms) as [[v rs]| |] eqn:Hsa; try discriminate. injection Hs as ->.
  unfold step_accesses in Hsa.
  assert (HD : forall w, decode_exec_accesses segs ms w = MachineOk (@mkAccessReport _ ms' rs) -> StoreOk.mem_grows (ms_mem ms) (ms_mem ms')).
  { intros w Hd. unfold decode_exec_accesses in Hd. destruct (is_ecall w).
    - injection Hd as <- <-. cbn. apply StoreOk.mem_grows_refl.
    - destruct (decode_any w) as [[i isz]|]; [|destruct (is_defined_illegal w); discriminate].
      match type of Hd with context [interp_eff_accesses segs ?t ?m] =>
        destruct (interp_eff_accesses segs t m) as [[[c1 m1] rs1]| |] eqn:Hint; try discriminate end.
      cbn [access_value accessed_ranges] in Hd. injection Hd as <- <-. cbn [ms_mem].
      exact (interp_eff_accesses_grows _ _ c1 m1 rs1 Hint). }
  destruct (fetch_word segs (ms_pc ms)) as [w|]; [exact (HD w Hsa)|].
  destruct (fetch_word_ov segs (ms_mem ms) (ms_pc ms)) as [w|]; [exact (HD w Hsa)|].
  destruct (fetch_tail_any segs (ms_mem ms) (ms_pc ms)) as [w|]; [exact (HD w Hsa)|].
  exfalso. unfold fetch_failure in Hsa.
  destruct (negb (bv_unsigned (ms_pc ms) mod 2 =? 0)%Z); [discriminate|].
  destruct (fetch_byte_traps segs (ms_pc ms) || fetch_byte_traps segs (ms_pc ms + 1)
            || match fetch_half_any segs (ms_mem ms) (ms_pc ms) with
               | Some _ => fetch_byte_traps segs (ms_pc ms + 2) || fetch_byte_traps segs (ms_pc ms + 3)
               | None => false end); discriminate.
Qed.

Lemma msteps_mem_grows : forall ms ms', msteps segs ms ms' -> StoreOk.mem_grows (ms_mem ms) (ms_mem ms').
Proof.
  intros ms ms' H. induction H as [ms | ms ms1 ms2 _ Hs _ IH]; [apply StoreOk.mem_grows_refl|].
  eapply StoreOk.mem_grows_trans; [exact (step_mem_grows _ _ Hs) | exact IH].
Qed.
End Grows.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition art_ev_live (ev : aev) (l : list (Z * Z)) : list (Z * Z) :=
  match ev with
  | AMmapNull len r => (r, len) :: l
  | AMunmap addr len => List.filter (fun p => negb (fst p =? addr)) l
  | _ => l
  end.
Definition art_live (log : list aev) : list (Z * Z) := fold_left (fun l ev => art_ev_live ev l) log [].

Lemma art_live_snoc : forall log ev, art_live (log ++ [ev]) = art_ev_live ev (art_live log).
Proof. intros. unfold art_live. rewrite fold_left_app. reflexivity. Qed.

(* [comment removed for export] *)
Definition art_cost (ev : aev) : Z :=
  match ev with
  | AMmapFixed _ len => len
  | AMmapNull len _ => len + len / 8 + 8192
  | _ => 0
  end.
Definition art_cost_sum (log : list aev) : Z := fold_right (fun ev z => art_cost ev + z) 0 log.

Lemma art_cost_sum_snoc : forall log ev, art_cost_sum (log ++ [ev]) = art_cost_sum log + art_cost ev.
Proof. intros log ev. unfold art_cost_sum. induction log as [|e l IH]; cbn [app fold_right]; [lia | rewrite IH; lia]. Qed.

(* [comment removed for export] *)
Definition art_windows (log : list aev) : list (Z * Z) :=
  flat_map (fun ev => match ev with AMmapNull len r => [(art_shlo r, art_shhi r len)] | _ => [] end) log.

Lemma art_windows_snoc : forall log ev,
  art_windows (log ++ [ev]) = art_windows log ++ match ev with AMmapNull len r => [(art_shlo r, art_shhi r len)] | _ => [] end.
Proof. intros. unfold art_windows. rewrite flat_map_app. cbn [flat_map]. rewrite app_nil_r. reflexivity. Qed.

Definition toW (p : Z * Z) : word * word := (Z_to_bv 64 (fst p), Z_to_bv 64 (snd p)).
Definition live_sum (L : list (Z * Z)) : Z := fold_right (fun p z => snd p + z) 0 L.

(* [comment removed for export] *)
Definition SHLO : Z := 0x7fff7000.
Definition SHHI : Z := 0x10007fff8000.
Definition LSH_LO : Z := 0x7fff8000.      Definition LSH_HI : Z := 0x8fff7000.          (* [comment removed for export] *)
Definition HSH_LO : Z := 0x02008fff7000.  Definition HSH_HI : Z := 0x10007fff8000.      (* [comment removed for export] *)
Definition in_shadow_rw (x : Z) : Prop := LSH_LO <= x < LSH_HI \/ HSH_LO <= x < HSH_HI.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Seam.
Variable RES : list (Z * Z).      (* [comment removed for export] *)
Variable KN0 : list (Z * Z).      (* [comment removed for export] *)
Variable CEIL : Z.                (* [comment removed for export] *)
Variable BUDGET : Z.
Variable LENMAX KMAX : Z.         (* [comment removed for export] *)

Definition art_EVOK (log : list aev) (ev : aev) : Prop :=
  match ev with
  | AMmapFixed addr len =>
      addr mod 4096 = 0 /\ len mod 4096 = 0 /\ 0 < len
      /\ (exists R, In R RES /\ fst R <= addr /\ addr + len <= fst R + snd R)
      /\ art_cost_sum (log ++ [ev]) <= BUDGET
  | AMmapNull len _ =>
      0 < len /\ len mod 4096 = 0 /\ len <= LENMAX
      /\ Z.of_nat (length (art_live log)) < KMAX
      /\ art_cost_sum (log ++ [ev]) <= BUDGET
  | AMmapFixedNR addr len =>
      addr mod 4096 = 0 /\ len mod 4096 = 0 /\ 0 < len
      /\ (exists w, In w (art_windows log) /\ fst w <= addr /\ addr + len <= snd w)
  | AMunmap addr len => In (addr, len) (art_live log)
  | AMadvise addr len =>
      addr mod 4096 = 0 /\ len mod 4096 = 0 /\ 0 < len
      /\ (exists w, In w (art_windows log) /\ fst w <= addr /\ addr + len <= snd w)
  end.

Definition art_GR (log : list aev) (M : word -> option byte) (len r : Z) : Prop :=
  r mod 4096 = 0 /\ 4096 <= r /\ r + len <= CEIL /\ r + len <= 2 ^ 47
  /\ (r + len <= SHLO \/ SHHI <= r)
  /\ (forall q, In q KN0 -> r + len <= fst q \/ snd q <= r)
  /\ (forall p, In p (art_live log) -> r + len <= fst p \/ fst p + snd p <= r).
End Seam.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Bridge.
Context {fx : PropExec.FPState}.
Variable segs : list Segment.
Variable scfg : SpuriousCfg.
Hypothesis Halloc : sc_alloc scfg = false.
Hypothesis Hwx : wx_segs_nowrap segs.

(* [comment removed for export] *)
Variable MAPS0 : list (word * word).      (* [comment removed for export] *)
Variable RESV0 : list (word * word).      (* [comment removed for export] *)
Variable NOACC0 : list (word * word).     (* [comment removed for export] *)
Variable RES : list (Z * Z).              (* [comment removed for export] *)
Variable CEIL BASE BUDGET : Z.
Variable LENMAX KMAX : Z.                 (* [comment removed for export] *)

(* [comment removed for export] *)
Definition ivZ (e : word * word) : Z * Z := (bv_unsigned (fst e), bv_unsigned (fst e) + bv_unsigned (snd e)).
Definition KN0 : list (Z * Z) := map ivZ (RESV0 ++ MAPS0).

(* [comment removed for export] *)
Record bridge_static : Prop := BS {
  bs_maps_wf : BA.ivs_wf MAPS0;
  bs_maps_pos : forall q, In q MAPS0 -> 0 < BA.S q;
  bs_resv_pos : forall b s, In (b, s) RESV0 -> 0 < bv_unsigned s;
  bs_maps_nodup : List.NoDup MAPS0;
  bs_maps_apart : forall q q', In q MAPS0 -> In q' MAPS0 -> q <> q' -> BA.B q + BA.S q <= BA.B q' \/ BA.B q' + BA.S q' <= BA.B q;
  bs_shrw_off_segs : forall x, in_shadow_rw x -> find_segment segs x 1 = None;
  bs_res_in : forall R, In R RES -> In (toW R) MAPS0 /\ 0 < fst R /\ 0 < snd R /\ fst R + snd R <= CEIL /\ fst R + snd R < 2 ^ 64;
  bs_res_off_resv : forall R b s, In R RES -> In (b, s) RESV0 ->
                      fst R + snd R <= bv_unsigned b \/ bv_unsigned b + bv_unsigned s <= fst R;
  bs_sh_in : forall x, SHLO <= x < SHHI -> BA.covered MAPS0 x = true;              (* [comment removed for export] *)
  bs_shrw_entry : forall lo hi, lo < hi -> ((LSH_LO <= lo /\ hi <= LSH_HI) \/ (HSH_LO <= lo /\ hi <= HSH_HI)) ->
                    exists b s, In (b, s) MAPS0 /\ bv_unsigned b <= lo /\ hi <= bv_unsigned b + bv_unsigned s;
  bs_shrw_off_resv : forall x b s, in_shadow_rw x -> In (b, s) RESV0 -> ~ (bv_unsigned b <= x < bv_unsigned b + bv_unsigned s);
  bs_shrw_acc : forall x, in_shadow_rw x -> BA.covered NOACC0 x = false;            (* [comment removed for export] *)
  bs_gap : AsanCeil.bottomup_floor + LENMAX + (AsanPlacement.gw_sizes (RESV0 ++ MAPS0) + BUDGET)
           + (Z.of_nat (length (RESV0 ++ MAPS0)) + KMAX) * (LENMAX + 4095) <= AsanCeil.alloc_ceiling;
  bs_ceil : SHHI <= CEIL /\ CEIL + stack_max_size < 2 ^ 64 /\ CEIL <= 2 ^ 47;
  bs_budget : 0 <= BUDGET /\ 0 <= KMAX /\ 0 <= LENMAX < 2 ^ 62
}.
Hypothesis STATIC : bridge_static.

Notation EVOK := (art_EVOK RES BUDGET LENMAX KMAX).
Notation GR := (art_GR KN0 CEIL).

Definition grants (log : list aev) : list (word * word) := map toW (art_live log).

(* [comment removed for export] *)
Definition window_ok (w : Z * Z) : Prop :=
  fst w mod 4096 = 0 /\ snd w mod 4096 = 0 /\ fst w <= snd w
  /\ ((LSH_LO <= fst w /\ snd w <= LSH_HI) \/ (HSH_LO <= fst w /\ snd w <= HSH_HI)).

(* [comment removed for export] *)
Definition bhid (A : list (Z * Z)) (m : Model) : word -> bool := mkH (m_vm_lazy m) A.

(* [comment removed for export] *)
Definition live_ok (L : list (Z * Z)) : Prop :=
  (forall p, In p L -> 0 < fst p /\ 0 < snd p /\ fst p mod 4096 = 0 /\ snd p mod 4096 = 0 /\ fst p + snd p <= CEIL
                       /\ (fst p + snd p <= SHLO \/ SHHI <= fst p)
                       /\ (forall q, In q KN0 -> fst p + snd p <= fst q \/ snd q <= fst p))
  /\ List.NoDup (map fst L)
  /\ (forall p p', In p L -> In p' L -> fst p <> fst p' -> fst p + snd p <= fst p' \/ fst p' + snd p' <= fst p).

Record BInv (log : list aev) (A : list (Z * Z)) (M : word -> option byte) (model : Model) : Prop := BI {
  bi_halt : m_halted model = None;
  bi_awf : A_wf A;
  bi_minv : MInv A model;
  bi_wf : BA.model_ivs_wf model;
  bi_maps : vm_maps (m_vmmaps model) = grants log ++ MAPS0;
  bi_resv : vm_reserved (m_vmmaps model) = RESV0;
  bi_top : alloc_top (m_vmmaps model) = CEIL;
  bi_limit : BASE + BUDGET <= vm_limit (m_vmmaps model);
  bi_noacc : forall x, BA.covered (vm_noaccess (m_vmmaps model)) x = true -> BA.covered NOACC0 x = true;
  bi_noacc_pos : forall q, In q (vm_noaccess (m_vmmaps model)) -> 0 < bv_unsigned (snd q);   (* [comment removed for export] *)
  bi_lazy_in : forall a : word, page_in_ranges (page_base a) (m_vm_lazy model) = true ->
                 BA.covered MAPS0 (bv_unsigned a) = true /\ find_segment segs (bv_unsigned a) 1 = None;
  bi_live : live_ok (art_live log);
  bi_zero : forall a : word, bhid A model a = true -> BA.covered (vm_noaccess (m_vmmaps model)) (bv_unsigned a) = false ->
              M a = Some (Z_to_bv 8 0);
  bi_shdef : forall a : word, in_shadow_rw (bv_unsigned a) -> M a <> None;
  bi_windows : forall w, In w (art_windows log) -> In w A /\ window_ok w;
  bi_budget : eager_used model + A_bytes A <= BASE + art_cost_sum log;
  bi_cost : art_cost_sum log <= BUDGET;
  bi_livesum : live_sum (art_live log) <= art_cost_sum log
}.

(* [comment removed for export] *)
Definition bmodel_rt (m m' : Model) : Prop :=
  m' = mkModelOf (m_fd m) (m_vm m') (m_io m) (m_fsys m) (m_proc m) (m_lim m) (m_time m).
Lemma bmodel_rt_refl : forall m, bmodel_rt m m.
Proof. intros m. unfold bmodel_rt. destruct m; reflexivity. Qed.
Lemma bmodel_rt_trans : forall m1 m2 m3, bmodel_rt m1 m2 -> bmodel_rt m2 m3 -> bmodel_rt m1 m3.
Proof. unfold bmodel_rt. intros m1 m2 m3 -> ->. destruct m1; reflexivity. Qed.
Lemma bmodel_rt_sbm : forall m m', same_but_materialized m m' -> bmodel_rt m m'.
Proof. intros m m' ->. destruct m as [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.

(* [comment removed for export] *)
Definition bstep (A : list (Z * Z)) (M : word -> option byte) (model : Model)
                 (A' : list (Z * Z)) (M' : word -> option byte) (model' : Model) (lo hi : Z) (nr : bool) : Prop :=
  incl A A'
  /\ (forall x : word, bhid A' model' x = true -> bhid A model x = true /\ M' x = M x)
  /\ (forall x : word, bhid A model x = true -> bhid A' model' x = false -> lo <= bv_unsigned x < hi)
  /\ (forall w, In w A' -> In w A \/ w = (lo, hi))
  /\ (forall x : word, page_in_ranges (page_base x) (m_vm_lazy model') = true ->
        page_in_ranges (page_base x) (m_vm_lazy model) = true \/ (nr = true /\ lo <= bv_unsigned x < hi)).
     (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma binv_hoff : forall log A M model, BInv log A M model -> H_off_segments segs (bhid A model).
Proof.
  intros log A M model B a Ha. unfold bhid, mkH in Ha. apply andb_prop in Ha as [Hp _].
  exact (proj2 (bi_lazy_in _ _ _ _ B a Hp)).
Qed.

Lemma bhid_lazy_cover : forall A model, lazy_cover (bhid A model) (m_vm_lazy model) A.
Proof. intros. unfold bhid. apply lazy_cover_mkH. intros r Hr; exact Hr. Qed.

Lemma binv_sbm : forall log A M model M' model',
  BInv log A M model -> MInv A model' -> same_but_materialized model model' ->
  (forall a, bhid A model a = true -> M' a = M a) ->
  (forall a : word, in_shadow_rw (bv_unsigned a) -> M' a <> None) ->
  BInv log A M' model'.
Proof.
  intros log A M model M' model' B Hminv Hs Hhid Hdef.
  destruct (same_but_materialized_frame _ _ Hs) as (_ & Hvm & Hlz & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hh & _).
  assert (Heu : eager_used model' = eager_used model) by (apply eager_used_ext; assumption).
  destruct B. constructor; rewrite ?Hvm, ?Hlz, ?Hh, ?Heu; try assumption.
  - destruct bi_wf0 as (W1 & W2 & W3 & W4). unfold BA.model_ivs_wf. rewrite Hvm, Hlz. repeat split; assumption.
  - intros a Ha Hna. unfold bhid in Ha. rewrite Hlz in Ha. rewrite (Hhid a Ha). apply bi_zero0; [exact Ha | exact Hna].
Qed.

Lemma bridge_msteps : forall log A ms model msr' K,
  BInv log A (ms_mem ms) model ->
  msteps segs (restrict (bhid A model) ms) msr' ->
  (forall ms' model', restrict (bhid A model') ms' = msr' -> BInv log A (ms_mem ms') model' -> bmodel_rt model model' ->
     bstep A (ms_mem ms) model A (ms_mem ms') model' 0 0 false ->
     srealizes segs scfg (mkCfg ms' model') K) ->
  srealizes segs scfg (mkCfg ms model) K.
Proof.
  intros log A ms model msr' K B MS HK.
  apply (srz_msteps_restricted_T segs scfg (bhid A model) (binv_hoff _ _ _ _ B) Hwx A ms msr' model K
           (bhid_lazy_cover A model) (bi_awf _ _ _ _ B) (bi_minv _ _ _ _ B) (bi_halt _ _ _ _ B) MS).
  intros model' Hminv Hs Hcl.
  destruct (same_but_materialized_frame _ _ Hs) as (_ & _ & Hlz & _).
  assert (EH : bhid A model' = bhid A model) by (unfold bhid; rewrite Hlz; reflexivity).
  apply HK.
  - rewrite EH. apply restrict_unrestrict_clean. exact Hcl.
  - rewrite unrestrict_mem. apply (binv_sbm log A (ms_mem ms) model); [exact B | exact Hminv | exact Hs | |].
    + intros a Ha. unfold munrestrict. rewrite Ha. reflexivity.
    + intros a Ha. unfold munrestrict. destruct (bhid A model a) eqn:E; [exact (bi_shdef _ _ _ _ B a Ha)|].
      apply (msteps_mem_grows segs _ _ MS). cbn [restrict ms_mem]. unfold mrestrict. rewrite E.
      exact (bi_shdef _ _ _ _ B a Ha).
  - apply bmodel_rt_sbm. exact Hs.
  - split; [apply incl_refl|]. split; [|split; [|split]].
    + intros x Hx. rewrite EH in Hx. split; [exact Hx|]. rewrite unrestrict_mem. unfold munrestrict. rewrite Hx. reflexivity.
    + intros x Hx Hx'. rewrite EH, Hx in Hx'. discriminate.
    + intros w0 Hw0. left. exact Hw0.
    + intros x Hx. left. rewrite <- Hlz. exact Hx.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma restrict_eq_mkst : forall (H : word -> bool) ms regs pc Mv rom,
  restrict H ms = mkst regs pc Mv rom -> ms = mkst regs pc (ms_mem ms) rom /\ Mv = mrestrict H (ms_mem ms).
Proof.
  intros H ms regs pc Mv rom E. destruct ms. unfold restrict, mkst in *. cbn in *.
  injection E as -> -> -> -> -> -> <- ->. split; reflexivity.
Qed.

Lemma u64z : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros. apply BA.fg_lit. assumption. Qed.

Lemma view_zfill : forall (H H' : word -> bool) M (r len : Z),
  0 <= r -> 0 <= len -> r + len <= 2 ^ 64 -> len < 2 ^ 64 ->
  (forall a : word, r <= bv_unsigned a < r + len -> H' a = false) ->
  (forall a : word, ~ (r <= bv_unsigned a < r + len) -> H' a = H a) ->
  mrestrict H' (zfill (Z_to_bv 64 r) (Z_to_bv 64 len) M) = art_zfill (mrestrict H M) r len.
Proof.
  intros H H' M r len Hr Hl Hend Hl64 Hin Hout. apply functional_extensionality. intro a.
  pose proof (bv_unsigned_in_range 64 a) as Ra. unfold bv_modulus in Ra.
  destruct (Z_lt_ge_dec r (2 ^ 64)) as [Hr64|Hr64].
  2:{ (* [comment removed for export] *)
      rewrite art_zfill_out by lia. unfold mrestrict. rewrite (Hout a) by lia.
      destruct (H a); [reflexivity|]. apply zfill_out. rewrite (u64z len) by lia.
      assert (len = 0) by lia. subst len. pose proof (bv_unsigned_in_range 64 (Z_to_bv 64 r)). lia. }
  destruct (Z_le_dec r (bv_unsigned a)) as [H1|H1]; [destruct (Z_lt_dec (bv_unsigned a) (r + len)) as [H2|H2]|].
  - rewrite art_zfill_in by lia. unfold mrestrict. rewrite (Hin a) by lia.
    apply zfill_in. rewrite (u64z r), (u64z len) by lia. lia.
  - rewrite art_zfill_out by lia. unfold mrestrict. rewrite (Hout a) by lia.
    destruct (H a); [reflexivity|]. apply zfill_out. rewrite (u64z r), (u64z len) by lia. lia.
  - rewrite art_zfill_out by lia. unfold mrestrict. rewrite (Hout a) by lia.
    destruct (H a); [reflexivity|]. apply zfill_out. rewrite (u64z r), (u64z len) by lia. lia.
Qed.

Lemma view_unfill : forall (H H' : word -> bool) M (r len : Z),
  0 <= r < 2 ^ 64 -> 0 <= len < 2 ^ 64 ->
  (forall a : word, ~ (r <= bv_unsigned a < r + len) -> H' a = H a) ->
  mrestrict H' (unfill (Z_to_bv 64 r) (Z_to_bv 64 len) M) = art_unmap (mrestrict H M) r len.
Proof.
  intros H H' M r len Hr Hl Hout. apply functional_extensionality. intro a.
  unfold mrestrict, unfill, art_unmap. rewrite (u64z r), (u64z len) by lia.
  destruct ((r <=? bv_unsigned a) && (bv_unsigned a <? r + len))%bool eqn:E.
  - destruct (H' a); reflexivity.
  - rewrite (Hout a); [reflexivity|]. intros [H1 H2].
    apply andb_false_iff in E as [E|E]; [apply Z.leb_gt in E | apply Z.ltb_ge in E]; lia.
Qed.

Lemma view_reveal : forall (H H' : word -> bool) M (lo hi : Z),
  (forall a : word, lo <= bv_unsigned a < hi -> H' a = false /\ M a <> None /\ (H a = true -> M a = Some (Z_to_bv 8 0))) ->
  (forall a : word, ~ (lo <= bv_unsigned a < hi) -> H' a = H a) ->
  mrestrict H' M = art_reveal (mrestrict H M) lo hi.
Proof.
  intros H H' M lo hi Hin Hout. apply functional_extensionality. intro a.
  unfold art_reveal, mrestrict.
  destruct ((lo <=? bv_unsigned a) && (bv_unsigned a <? hi))%bool eqn:E.
  - apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
    destruct (Hin a ltac:(lia)) as (H1 & H2 & H3). rewrite H1.
    destruct (H a); [rewrite (H3 eq_refl); reflexivity|]. destruct (M a); [reflexivity | contradiction].
  - rewrite (Hout a); [reflexivity|]. intros [H1 H2].
    apply andb_false_iff in E as [E|E]; [apply Z.leb_gt in E | apply Z.ltb_ge in E]; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma page_allowed_in : forall A (w : Z * Z) (x : word),
  In w A -> fst w mod 4096 = 0 -> snd w mod 4096 = 0 -> fst w <= bv_unsigned x < snd w ->
  page_allowedb A (page_base x) = true.
Proof.
  intros A w x Hin H1 H2 Hx. unfold page_allowedb. apply existsb_exists. exists w. split; [exact Hin|].
  destruct (page_of_byte_in_aligned x (fst w) (snd w) H1 H2 Hx) as [P1 P2].
  unfold page_size. apply andb_true_intro. split; apply Z.leb_le; lia.
Qed.

Lemma page_in_ranges_subtract_le : forall (p : word) l lo hi,
  BA.ivs_wf l -> page_in_ranges p (maps_subtract l lo hi) = true -> page_in_ranges p l = true.
Proof.
  intros p l lo hi Hwf H. apply page_in_ranges_true in H as (q & Hq & H1 & H2).
  destruct (maps_subtract_pieces l lo hi q Hwf Hq) as (r & Hr & R1 & R2 & _).
  apply page_in_ranges_true. exists r. split; [exact Hr|]. lia.
Qed.

(* [comment removed for export] *)
Lemma lazy_forget_out : forall lazy (extra : list (word * word)) lo hi (x : word),
  BA.ivs_wf lazy -> lo mod 4096 = 0 -> hi mod 4096 = 0 -> lo <= hi ->
  (forall q, In q extra -> lo <= bv_unsigned (fst q) /\ bv_unsigned (fst q) + bv_unsigned (snd q) <= hi) ->
  ~ (lo <= bv_unsigned x < hi) ->
  page_in_ranges (page_base x) (extra ++ maps_subtract lazy lo hi) = page_in_ranges (page_base x) lazy.
Proof.
  intros lazy extra lo hi x Hwf Hlo Hhi Hle Hex Hx.
  destruct (page_of_byte_out_aligned x lo hi Hlo Hhi ltac:(lia)) as [P|P].
  - rewrite page_in_ranges_app.
    replace (page_in_ranges (page_base x) extra) with false.
    + cbn [orb]. apply page_in_ranges_subtract_out; [exact Hwf | exact Hle | unfold page_size; lia].
    + symmetry. apply page_in_ranges_false. intros q Hq [Q1 Q2]. destruct (Hex q Hq). unfold page_size in *. lia.
  - rewrite page_in_ranges_app.
    replace (page_in_ranges (page_base x) extra) with false.
    + cbn [orb]. apply page_in_ranges_subtract_out; [exact Hwf | exact Hle | unfold page_size; lia].
    + symmetry. apply page_in_ranges_false. intros q Hq [Q1 Q2]. destruct (Hex q Hq). unfold page_size in *. lia.
Qed.

Definition forget_model (extra : list (word * word)) (lo hi : Z) (h' : VmMaps) (m : Model) : Model :=
  with_vm_backing (extra ++ maps_subtract (m_vm_lazy m) lo hi)
                  (List.filter (page_outside_range lo hi) (m_vm_materialized m)) (with_vmmaps h' m).

Lemma minv_forget : forall A m extra lo hi h' delta,
  MInv A m -> BA.ivs_wf (m_vm_lazy m) -> lo mod 4096 = 0 -> hi mod 4096 = 0 -> lo <= hi ->
  (forall q, In q extra -> lo <= bv_unsigned (fst q) /\ bv_unsigned (fst q) + bv_unsigned (snd q) <= hi) ->
  vm_limit h' = vm_limit (m_vmmaps m) ->
  eager_used (forget_model extra lo hi h' m) <= eager_used m + delta ->
  eager_used m + delta + A_bytes A <= vm_limit (m_vmmaps m) ->
  MInv A (forget_model extra lo hi h' m).
Proof.
  intros A m extra lo hi h' delta [Hnd Hal Hall Hlz Hbud] Hwf Hlo Hhi Hle Hex Hlim He Hb.
  constructor.
  - cbn. apply NoDup_filter. exact Hnd.
  - intros p Hp. cbn in Hp. apply filter_In in Hp as [Hp _]. exact (Hal p Hp).
  - intros p Hp. cbn in Hp. apply filter_In in Hp as [Hp _]. exact (Hall p Hp).
  - intros p Hp. cbn in Hp. apply filter_In in Hp as [Hp Ho].
    change (m_vm_lazy (forget_model extra lo hi h' m)) with (extra ++ maps_subtract (m_vm_lazy m) lo hi).
    rewrite page_in_ranges_app. apply orb_true_iff. right.
    rewrite page_in_ranges_subtract_out; [exact (Hlz p Hp) | exact Hwf | exact Hle |].
    pose proof (Hal p Hp) as Hpa. unfold page_size in *.
    unfold page_outside_range in Ho. apply negb_true_iff in Ho. apply andb_false_iff in Ho as [Ho|Ho];
      [apply Z.leb_gt in Ho | apply Z.ltb_ge in Ho]; [left | right; lia].
    (* [comment removed for export] *)
    assert (E1 : bv_unsigned p = 4096 * (bv_unsigned p / 4096)) by (apply Z.div_exact; lia).
    assert (E2 : lo = 4096 * (lo / 4096)) by (apply Z.div_exact; lia).
    assert (bv_unsigned p / 4096 < lo / 4096) by (apply Z.div_lt_upper_bound; lia). lia.
  - change (vm_limit (m_vmmaps (forget_model extra lo hi h' m))) with (vm_limit h'). rewrite Hlim. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma maps_subtract_pos : forall l lo hi,
  (forall q, In q l -> 0 < bv_unsigned (snd q)) -> BA.ivs_wf l -> lo <= hi ->
  forall q, In q (maps_subtract l lo hi) -> 0 < bv_unsigned (snd q).
Proof.
  induction l as [|[a sz] l IH]; intros lo hi Hpos Hwf Hle q Hq; [destruct Hq|].
  cbn [maps_subtract] in Hq. apply in_app_or in Hq as [Hq|Hq].
  - pose proof (Hpos (a, sz) (or_introl eq_refl)) as Hs. cbn [snd] in Hs.
    pose proof (Hwf (a, sz) (or_introl eq_refl)) as Hw. unfold BA.iv_wf, BA.B, BA.S in Hw. cbn [fst snd] in Hw.
    pose proof (u64_range a) as Ra. pose proof (u64_range sz) as Rs.
    unfold iv_subtract in Hq. apply in_app_or in Hq as [Hq|Hq].
    + destruct (bv_unsigned a <? lo) eqn:E; [|destruct Hq]. apply Z.ltb_lt in E. destruct Hq as [<-|[]]. cbn [snd].
      rewrite u64z by lia. lia.
    + destruct (hi <? bv_unsigned a + bv_unsigned sz) eqn:E; [|destruct Hq]. apply Z.ltb_lt in E. destruct Hq as [<-|[]]. cbn [snd].
      rewrite u64z by lia. lia.
  - apply (IH lo hi); [intros q' Hq'; apply Hpos; right; exact Hq' | intros q' Hq'; apply Hwf; right; exact Hq' | exact Hle | exact Hq].
Qed.

Lemma binv_forget : forall log log' A M M' model extra lo hi h' delta,
  BInv log A M model ->
  lo mod 4096 = 0 -> hi mod 4096 = 0 -> lo <= hi ->
  BA.ivs_wf extra ->
  (forall q, In q extra -> lo <= bv_unsigned (fst q) /\ bv_unsigned (fst q) + bv_unsigned (snd q) <= hi) ->
  (forall a : word, page_in_ranges (page_base a) extra = true ->
     BA.covered MAPS0 (bv_unsigned a) = true /\ find_segment segs (bv_unsigned a) 1 = None) ->
  vm_maps h' = grants log' ++ MAPS0 -> BA.ivs_wf (vm_maps h') ->
  vm_reserved h' = vm_reserved (m_vmmaps model) -> vm_limit h' = vm_limit (m_vmmaps model) ->
  vm_init_sp h' = vm_init_sp (m_vmmaps model) ->
  vm_noaccess h' = maps_subtract (vm_noaccess (m_vmmaps model)) lo hi ->
  live_ok (art_live log') -> live_sum (art_live log') <= live_sum (art_live log) -> art_windows log' = art_windows log ->
  art_cost_sum log' = art_cost_sum log + delta -> 0 <= delta -> art_cost_sum log' <= BUDGET ->
  eager_used (forget_model extra lo hi h' model) <= eager_used model + delta ->
  (forall a : word, lo <= bv_unsigned a < hi -> bhid A (forget_model extra lo hi h' model) a = false) ->
  (forall a : word, lo <= bv_unsigned a < hi -> in_shadow_rw (bv_unsigned a) -> M' a <> None) ->
  (forall a : word, ~ (lo <= bv_unsigned a < hi) -> M' a = M a) ->
  BInv log' A M' (forget_model extra lo hi h' model)
  /\ (forall a : word, ~ (lo <= bv_unsigned a < hi) -> bhid A (forget_model extra lo hi h' model) a = bhid A model a)
  /\ bstep A M model A M' (forget_model extra lo hi h' model) lo hi (match extra with [] => false | _ => true end).
Proof.
  intros log log' A M M' model extra lo hi h' delta B Hlo Hhi Hle Wex Hex HexIn Hmaps Wmaps Hresv Hlim Hisp Hna
         Hlive Hls Hwin Hcost Hd Hcb He Hvis Hdef Hout.
  set (m' := forget_model extra lo hi h' model) in *.
  destruct (bi_wf _ _ _ _ B) as (W1 & W2 & W3 & W4).
  destruct (BA.maps_subtract_sem _ lo hi W2 Hle) as (Wn' & _ & Cn).
  assert (HOUT : forall a : word, ~ (lo <= bv_unsigned a < hi) -> bhid A m' a = bhid A model a).
  { intros a Ha. unfold bhid, mkH. change (m_vm_lazy m') with (extra ++ maps_subtract (m_vm_lazy model) lo hi).
    rewrite (lazy_forget_out _ extra lo hi a W3 Hlo Hhi Hle Hex Ha). reflexivity. }
  split; [|split; [exact HOUT|]].
  2:{ split; [apply incl_refl|]. split; [|split; [|split]].
      4:{ intros x Hx. change (m_vm_lazy m') with (extra ++ maps_subtract (m_vm_lazy model) lo hi) in Hx.
          rewrite page_in_ranges_app in Hx. apply orb_prop in Hx as [Hx|Hx].
          - right. split; [destruct extra; [discriminate Hx | reflexivity]|].
            apply page_in_ranges_true in Hx as (q & Hq & Q1 & Q2). destruct (Hex q Hq) as [E1 E2].
            destruct (page_base_facts x) as (P1 & P2 & P3). unfold page_size in Q2. lia.
          - left. exact (page_in_ranges_subtract_le _ _ lo hi W3 Hx). }
      - intros x Hx. assert (Hn : ~ (lo <= bv_unsigned x < hi)) by (intros Hin; rewrite (Hvis x Hin) in Hx; discriminate).
        split; [rewrite <- (HOUT x Hn); exact Hx | exact (Hout x Hn)].
      - intros x Hx Hx'. destruct (Z_le_dec lo (bv_unsigned x)) as [L|L]; [destruct (Z_lt_dec (bv_unsigned x) hi) as [U|U]|].
        + lia.
        + rewrite (HOUT x ltac:(lia)), Hx in Hx'. discriminate.
        + rewrite (HOUT x ltac:(lia)), Hx in Hx'. discriminate.
      - intros w0 Hw0. left. exact Hw0. }
  constructor.
  - change (m_halted m') with (m_halted model). exact (bi_halt _ _ _ _ B).
  - exact (bi_awf _ _ _ _ B).
  - apply (minv_forget A model extra lo hi h' delta (bi_minv _ _ _ _ B) W3 Hlo Hhi Hle Hex Hlim He).
    pose proof (bi_budget _ _ _ _ B). pose proof (bi_limit _ _ _ _ B). lia.
  - unfold BA.model_ivs_wf. change (m_vmmaps m') with h'. change (m_vm_lazy m') with (extra ++ maps_subtract (m_vm_lazy model) lo hi).
    rewrite Hna. split; [exact Wmaps|]. split; [exact Wn'|]. split.
    + apply BA.ivs_wf_app; [exact Wex | apply BA.maps_subtract_wf; assumption].
    + exact (AsanCeil.init_sp_ok_same _ _ Hisp W4).
  - change (m_vmmaps m') with h'. exact Hmaps.
  - change (m_vmmaps m') with h'. rewrite Hresv. exact (bi_resv _ _ _ _ B).
  - change (m_vmmaps m') with h'. unfold alloc_top. rewrite Hisp. exact (bi_top _ _ _ _ B).
  - change (m_vmmaps m') with h'. rewrite Hlim. exact (bi_limit _ _ _ _ B).
  - change (m_vmmaps m') with h'. intros x Hx. rewrite Hna, Cn in Hx. apply andb_prop in Hx as [Hx _].
    exact (bi_noacc _ _ _ _ B x Hx).
  - change (m_vmmaps m') with h'. rewrite Hna. apply maps_subtract_pos; [exact (bi_noacc_pos _ _ _ _ B) | exact W2 | exact Hle].
  - intros a Ha. change (m_vm_lazy m') with (extra ++ maps_subtract (m_vm_lazy model) lo hi) in Ha.
    rewrite page_in_ranges_app in Ha. apply orb_prop in Ha as [Ha|Ha]; [exact (HexIn a Ha)|].
    apply (bi_lazy_in _ _ _ _ B a). exact (page_in_ranges_subtract_le _ _ lo hi W3 Ha).
  - exact Hlive.
  - intros a Ha Hnoa.
    destruct (Z_le_dec lo (bv_unsigned a)) as [L|L]; [destruct (Z_lt_dec (bv_unsigned a) hi) as [U|U]|].
    + rewrite (Hvis a (conj L U)) in Ha. discriminate.
    + rewrite (Hout a) by lia. apply (bi_zero _ _ _ _ B a); [rewrite <- (HOUT a) by lia; exact Ha|].
      change (m_vmmaps m') with h' in Hnoa. rewrite Hna, Cn in Hnoa.
      destruct (BA.covered (vm_noaccess (m_vmmaps model)) (bv_unsigned a)); [|reflexivity].
      cbn [andb] in Hnoa. apply negb_false_iff in Hnoa. unfold BA.in_rng in Hnoa. apply andb_prop in Hnoa as [N1 N2].
      apply Z.leb_le in N1. apply Z.ltb_lt in N2. lia.
    + rewrite (Hout a) by lia. apply (bi_zero _ _ _ _ B a); [rewrite <- (HOUT a) by lia; exact Ha|].
      change (m_vmmaps m') with h' in Hnoa. rewrite Hna, Cn in Hnoa.
      destruct (BA.covered (vm_noaccess (m_vmmaps model)) (bv_unsigned a)); [|reflexivity].
      cbn [andb] in Hnoa. apply negb_false_iff in Hnoa. unfold BA.in_rng in Hnoa. apply andb_prop in Hnoa as [N1 N2].
      apply Z.leb_le in N1. apply Z.ltb_lt in N2. lia.
  - intros a Ha.
    destruct (Z_le_dec lo (bv_unsigned a)) as [L|L]; [destruct (Z_lt_dec (bv_unsigned a) hi) as [U|U]|].
    + exact (Hdef a (conj L U) Ha).
    + rewrite (Hout a) by lia. exact (bi_shdef _ _ _ _ B a Ha).
    + rewrite (Hout a) by lia. exact (bi_shdef _ _ _ _ B a Ha).
  - rewrite Hwin. exact (bi_windows _ _ _ _ B).
  - pose proof (bi_budget _ _ _ _ B). lia.
  - exact Hcb.
  - pose proof (bi_livesum _ _ _ _ B). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma shadow_rw_facts : forall lo hi, lo < hi -> ((LSH_LO <= lo /\ hi <= LSH_HI) \/ (HSH_LO <= lo /\ hi <= HSH_HI)) ->
  0 < lo /\ hi <= SHHI /\ SHLO <= lo /\ (forall x, lo <= x < hi -> in_shadow_rw x).
Proof.
  intros lo hi Hlt H. unfold LSH_LO, LSH_HI, HSH_LO, HSH_HI, SHHI, SHLO, in_shadow_rw in *.
  repeat split; try lia. intros x Hx. unfold LSH_LO, LSH_HI, HSH_LO, HSH_HI. lia.
Qed.

Lemma region_free_resv_shadow : forall lo hi, 0 <= lo -> lo < hi -> hi < 2 ^ 64 -> (forall x, lo <= x < hi -> in_shadow_rw x) ->
  region_free RESV0 (Z_to_bv 64 lo) (Z_to_bv 64 (hi - lo)) = true.
Proof.
  intros lo hi H0 Hlt Hhi Hsh. apply region_free_intro. intros b s Hin.
  rewrite (u64z lo), (u64z (hi - lo)) by lia.
  destruct (Z_le_dec (lo + (hi - lo)) (bv_unsigned b)) as [L|L]; [left; exact L|].
  destruct (Z_le_dec (bv_unsigned b + bv_unsigned s) lo) as [R|R]; [right; exact R|].
  exfalso. pose proof (bv_unsigned_in_range 64 b) as Rb. pose proof (bv_unsigned_in_range 64 s) as Rs.
  pose proof (bs_resv_pos STATIC b s Hin) as Hs.
  apply (bs_shrw_off_resv STATIC (Z.max lo (bv_unsigned b)) b s); [apply Hsh; lia | exact Hin | lia].
Qed.

Lemma mm1_eq : Z_to_bv 64 (2 ^ 64 - 1) = Z_to_bv 64 (-1).
Proof. apply bv_eq. rewrite !Z_to_bv_unsigned. reflexivity. Qed.

Lemma bridge_fixed_nr : forall log A regs pc M rom model addr len K,
  BInv log A M model -> art_at_ecall segs pc -> art_mmap_args regs addr len 16434 ->
  EVOK log (AMmapFixedNR addr len) ->
  (forall M' model', BInv (log ++ [AMmapFixedNR addr len]) A M' model' -> bmodel_rt model model' ->
     bstep A M model A M' model' addr (addr + len) true ->
     mrestrict (bhid A model') M' = art_zfill (mrestrict (bhid A model) M) addr len ->
     srealizes segs scfg (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 addr)) (Z_to_bv 64 (bv_unsigned pc + 4)) M' rom) model') K) ->
  srealizes segs scfg (mkCfg (mkst regs pc M rom) model) K.
Proof.
  intros log A regs pc M rom model addr len K B (w & HF & HE) (H17 & H10 & H11 & H12 & H13 & H14 & H15)
         (Hal & Hll & Hlen & (win & Hwin & W1 & W2)) HK.
  destruct (bi_windows _ _ _ _ B win Hwin) as [HwA (Wa & Wb & Wle & Wsh)].
  assert (Hsub : (LSH_LO <= addr /\ addr + len <= LSH_HI) \/ (HSH_LO <= addr /\ addr + len <= HSH_HI)) by lia.
  destruct (shadow_rw_facts addr (addr + len) ltac:(lia) Hsub) as (Hpos & Hhi & Hlo & Hsh).
  destruct (bs_ceil STATIC) as (Hc1 & Hc2 & Hc3).
  assert (Hend : addr + len < 2 ^ 64) by (unfold stack_max_size in Hc2; lia).
  set (aW := Z_to_bv 64 addr). set (nW := Z_to_bv 64 len). set (flags := Z_to_bv 64 16434).
  assert (Ua : bv_unsigned aW = addr) by (apply u64z; lia).
  assert (Un : bv_unsigned nW = len) by (apply u64z; lia).
  assert (Hpr : page_round_up_Z len = len) by (apply AllocSim.page_round_up_Z_aligned; [lia | exact Hll]).
  set (h := m_vmmaps model).
  set (h' := mmap_fixed_rw_next h aW nW).
  assert (Em : fixedin_ok_model 3 flags aW nW model = forget_model [(aW, nW)] addr (addr + len) h' model).
  { unfold fixedin_ok_model, fixedin_ok_vmmaps, with_mmap_replacement, with_mmap_backing. cbn [Z.eqb].
    replace (mmap_noreserve_b flags) with true by (symmetry; apply mmap_noreserve_b_4032).
    unfold vm_add_lazy. rewrite (BA.lazy_interior_aligned aW nW) by (rewrite ?Ua, ?Un; unfold page_size; lia).
    rewrite Ua, Un. reflexivity. }
  destruct (bi_wf _ _ _ _ B) as (Wm & Wn & Wl & Wsp).
  destruct (binv_forget log (log ++ [AMmapFixedNR addr len]) A M (zfill aW nW M) model [(aW, nW)] addr (addr + len) h' 0 B) as (B' & HOUT & HST).
  - exact Hal.
  - rewrite Z.add_mod, Hal, Hll by lia. reflexivity.
  - lia.
  - apply BA.ivs_wf_cons; [unfold BA.iv_wf, BA.B, BA.S; cbn [fst snd]; rewrite Ua, Un; lia | apply BA.ivs_wf_nil].
  - intros q [<-|[]]. cbn [fst snd]. rewrite Ua, Un. lia.
  - intros a Ha. apply page_in_ranges_true in Ha as (q & [<-|[]] & Q1 & Q2). cbn [fst snd] in Q1, Q2. rewrite ?Ua, ?Un in Q1, Q2.
    destruct (page_base_facts a) as (P1 & P2 & P3). unfold page_size in Q2.
    assert (Hin : addr <= bv_unsigned a < addr + len) by lia.
    split; [apply (bs_sh_in STATIC); lia|].
    exact (bs_shrw_off_segs STATIC (bv_unsigned a) (Hsh _ Hin)).
  - unfold h', mmap_fixed_rw_next, grants. cbn [vm_maps]. rewrite art_live_snoc. cbn [art_ev_live]. exact (bi_maps _ _ _ _ B).
  - unfold h', mmap_fixed_rw_next. cbn [vm_maps]. exact Wm.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - unfold h', mmap_fixed_rw_next. cbn [vm_noaccess]. rewrite Ua, Un. reflexivity.
  - rewrite art_live_snoc. cbn [art_ev_live]. exact (bi_live _ _ _ _ B).
  - rewrite art_live_snoc. cbn [art_ev_live]. lia.
  - rewrite art_windows_snoc, app_nil_r. reflexivity.
  - rewrite art_cost_sum_snoc. cbn [art_cost]. reflexivity.
  - lia.
  - rewrite art_cost_sum_snoc. cbn [art_cost]. pose proof (bi_cost _ _ _ _ B). lia.
  - rewrite <- Em. unfold fixedin_ok_model, fixedin_ok_vmmaps, with_mmap_replacement, with_mmap_backing. cbn [Z.eqb].
    replace (mmap_noreserve_b flags) with true by (symmetry; apply mmap_noreserve_b_4032).
    rewrite Z.add_0_r.
    apply (eager_recommit_le model (mmap_fixed_rw_next h aW nW) aW nW (bi_wf _ _ _ _ B));
      [rewrite Ua; unfold page_size; lia | rewrite Un; unfold page_size; lia | rewrite Un; lia | rewrite Ua, Un; lia
      | reflexivity | reflexivity].
  - intros a Ha. unfold bhid, mkH. rewrite (page_allowed_in A win a HwA Wa Wb ltac:(lia)). apply andb_false_r.
  - intros a Ha _. rewrite zfill_in by (rewrite Ua, Un; lia). discriminate.
  - intros a Ha. apply zfill_out. rewrite Ua, Un. lia.
  - (* [comment removed for export] *)
    apply (srz_mmap_fixedin_lazy segs scfg Halloc regs pc M rom model w 3 flags aW len K HF HE (bi_halt _ _ _ _ B) H17
             (or_intror eq_refl) mmap_flags_core_4032 H10 ltac:(rewrite Ua; unfold page_size; exact Hal) ltac:(rewrite Ua; exact Hpos)
             H11 Hlen ltac:(rewrite Ua, Hpr, (bi_top _ _ _ _ B); lia) H12 H13 ltac:(rewrite H14; exact mm1_eq) H15).
    + rewrite Hpr. fold nW. rewrite (bi_resv _ _ _ _ B).
      replace nW with (Z_to_bv 64 (addr + len - addr)) by (unfold nW; f_equal; lia).
      apply region_free_resv_shadow; try lia. exact Hsh.
    + rewrite Hpr. fold nW. rewrite (bi_maps _ _ _ _ B).
      destruct (bs_shrw_entry STATIC addr (addr + len) ltac:(lia) Hsub) as (b & s & Hbs & B1 & B2).
      apply (map_contains_intro _ aW nW b s); [apply in_or_app; right; exact Hbs | rewrite Ua; exact B1 | rewrite Ua, Un; exact B2].
    + intros _. rewrite Hpr. fold nW.
      apply BA.mmap_fixed_rw_budget_ok_recommit_intro; rewrite ?Ua, ?Un; unfold page_size; try lia;
        [apply mmap_noreserve_b_4032 | exact (bi_wf _ _ _ _ B) | exact (vm_backing_used_limit A model (bi_minv _ _ _ _ B) (bi_awf _ _ _ _ B))].
    + rewrite Hpr. fold nW. cbn [Z.eqb]. rewrite Em.
      apply HK; [exact B' | rewrite <- Em; unfold bmodel_rt; destruct model as [fd [maps lazy mat] io fs proc lim tm]; reflexivity | exact HST |].
      apply view_zfill; try lia.
      * intros a Ha. unfold bhid, mkH. rewrite (page_allowed_in A win a HwA Wa Wb ltac:(lia)). apply andb_false_r.
      * exact HOUT.
Qed.

(* [comment removed for export] *)
Lemma overlap_sum_apart0 : forall l lo hi,
  (forall q, In q l -> BA.B q + BA.S q <= lo \/ hi <= BA.B q) -> BA.overlap_sum l lo hi = 0.
Proof.
  induction l as [|q l IH]; intros lo hi H; [reflexivity|].
  rewrite BA.overlap_sum_cons, (BA.iv_count_in_rng_disjoint q lo hi (H q (or_introl eq_refl))).
  rewrite IH; [reflexivity | intros q' Hq'; apply H; right; exact Hq'].
Qed.

Lemma ww_dec : forall q r : word * word, q = r \/ q <> r.
Proof.
  intros [a b] [c d]. destruct (bv_eqb a c) eqn:E1; [destruct (bv_eqb b d) eqn:E2|].
  - left. apply bv_eqb_eq in E1. apply bv_eqb_eq in E2. subst. reflexivity.
  - right. intros E. injection E as _ ->. rewrite bv_eqb_refl in E2. discriminate.
  - right. intros E. injection E as -> _. rewrite bv_eqb_refl in E1. discriminate.
Qed.

Lemma overlap_sum_one : forall l R lo hi,
  List.NoDup l -> lo <= hi ->
  (forall q, In q l -> q <> R -> BA.B q + BA.S q <= lo \/ hi <= BA.B q) ->
  BA.overlap_sum l lo hi <= hi - lo.
Proof.
  induction l as [|q l IH]; intros R lo hi Hnd Hle H; [rewrite BA.overlap_sum_nil; lia|].
  rewrite BA.overlap_sum_cons. inversion Hnd as [|q0 l0 Hnin Hnd']; subst.
  destruct (ww_dec q R) as [E|E].
  - subst q. rewrite (overlap_sum_apart0 l lo hi).
    + pose proof (BA.iv_count_in_rng_le R lo hi Hle). lia.
    + intros q' Hq'. apply H; [right; exact Hq' | intros E'; subst q'; exact (Hnin Hq')].
  - rewrite (BA.iv_count_in_rng_disjoint q lo hi (H q (or_introl eq_refl) E)).
    pose proof (IH R lo hi Hnd' Hle ltac:(intros q' Hq'; apply H; right; exact Hq')). lia.
Qed.

(* [comment removed for export] *)
Lemma live_word : forall L p, live_ok L -> In p L ->
  BA.B (toW p) = fst p /\ BA.S (toW p) = snd p /\ 0 < fst p /\ 0 < snd p /\ fst p + snd p < 2 ^ 64.
Proof.
  intros L p (Hl & _ & _) Hp. destruct (Hl p Hp) as (H1 & H2 & _ & _ & H5 & _).
  destruct (bs_ceil STATIC) as (_ & Hc2 & _). unfold stack_max_size in Hc2.
  unfold BA.B, BA.S, toW. cbn [fst snd]. rewrite !u64z by lia. repeat split; lia.
Qed.

Lemma res_word : forall R, In R RES ->
  BA.B (toW R) = fst R /\ BA.S (toW R) = snd R.
Proof.
  intros R HR. destruct (bs_res_in STATIC R HR) as (_ & H1 & H2 & _ & H4).
  unfold BA.B, BA.S, toW. cbn [fst snd]. rewrite !u64z by lia. split; reflexivity.
Qed.

Lemma overlap_in_res : forall log R lo hi,
  live_ok (art_live log) -> In R RES -> fst R <= lo -> lo <= hi -> hi <= fst R + snd R ->
  BA.overlap_sum (grants log ++ MAPS0) lo hi <= hi - lo.
Proof.
  intros log R lo hi HL HR H1 Hle H2.
  destruct (bs_res_in STATIC R HR) as (HRin & _). destruct (res_word R HR) as (ER1 & ER2).
  rewrite BA.overlap_sum_app. rewrite (overlap_sum_apart0 (grants log)).
  - apply (overlap_sum_one MAPS0 (toW R) lo hi (bs_maps_nodup STATIC) Hle).
    intros q Hq Hne. destruct (bs_maps_apart STATIC q (toW R) Hq HRin Hne) as [A1|A1]; rewrite ?ER1, ?ER2 in A1; lia.
  - intros q Hq. unfold grants in Hq. apply in_map_iff in Hq as (p & <- & Hp).
    destruct (live_word _ p HL Hp) as (E1 & E2 & _). rewrite E1, E2.
    destruct HL as (Hl & _ & _). destruct (Hl p Hp) as (_ & _ & _ & _ & _ & _ & Hk).
    assert (Hkin : In (ivZ (toW R)) KN0) by (unfold KN0; apply in_map; apply in_or_app; right; exact HRin).
    destruct (Hk _ Hkin) as [K|K]; unfold ivZ in K; cbn [fst snd] in K;
      fold (BA.B (toW R)) in K; fold (BA.S (toW R)) in K; rewrite ?ER1, ?ER2 in K; lia.
Qed.

Lemma bridge_fixed : forall log A regs pc M rom model addr len K,
  BInv log A M model -> art_at_ecall segs pc -> art_mmap_args regs addr len 50 ->
  EVOK log (AMmapFixed addr len) ->
  (forall M' model', BInv (log ++ [AMmapFixed addr len]) A M' model' -> bmodel_rt model model' ->
     bstep A M model A M' model' addr (addr + len) false ->
     mrestrict (bhid A model') M' = art_zfill (mrestrict (bhid A model) M) addr len ->
     srealizes segs scfg (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 addr)) (Z_to_bv 64 (bv_unsigned pc + 4)) M' rom) model') K) ->
  srealizes segs scfg (mkCfg (mkst regs pc M rom) model) K.
Proof.
  intros log A regs pc M rom model addr len K B (w & HF & HE) (H17 & H10 & H11 & H12 & H13 & H14 & H15)
         (Hal & Hll & Hlen & (R & HR & R1 & R2) & Hcb) HK.
  destruct (bs_res_in STATIC R HR) as (HRin & Rp & Rs & Rc & R64).
  destruct (res_word R HR) as (ER1 & ER2).
  destruct (bs_ceil STATIC) as (Hc1 & Hc2 & Hc3).
  set (aW := Z_to_bv 64 addr). set (nW := Z_to_bv 64 len). set (flags := Z_to_bv 64 50).
  assert (Ua : bv_unsigned aW = addr) by (apply u64z; lia).
  assert (Un : bv_unsigned nW = len) by (apply u64z; lia).
  assert (Hpr : page_round_up_Z len = len) by (apply AllocSim.page_round_up_Z_aligned; [lia | exact Hll]).
  set (h := m_vmmaps model).
  set (h' := mmap_fixed_rw_next h aW nW).
  assert (Em : fixedin_ok_model 3 flags aW nW model = forget_model [] addr (addr + len) h' model).
  { unfold fixedin_ok_model, fixedin_ok_vmmaps, with_mmap_replacement, with_mmap_backing. cbn [Z.eqb].
    replace (mmap_noreserve_b flags) with false by (symmetry; apply mmap_noreserve_b_32).
    rewrite Ua, Un. reflexivity. }
  destruct (bi_wf _ _ _ _ B) as (Wm & Wn & Wl & Wsp).
  assert (Hov : BA.overlap_sum (vm_maps h) addr (addr + len) <= len).
  { unfold h. rewrite (bi_maps _ _ _ _ B).
    pose proof (overlap_in_res log R addr (addr + len) (bi_live _ _ _ _ B) HR R1 ltac:(lia) R2). lia. }
  assert (He : eager_used (forget_model [] addr (addr + len) h' model) <= eager_used model + len).
  { pose proof (eager_commit_le model h' (bv_unsigned aW) (bv_unsigned aW + bv_unsigned nW)
                  (bi_wf _ _ _ _ B) ltac:(rewrite Un; lia) eq_refl eq_refl) as HE'.
    rewrite Ua, Un in HE'. eapply Z.le_trans; [exact HE'|]. unfold h in Hov. lia. }
  destruct (binv_forget log (log ++ [AMmapFixed addr len]) A M (zfill aW nW M) model [] addr (addr + len) h' len B) as (B' & HOUT & HST).
  - exact Hal.
  - rewrite Z.add_mod, Hal, Hll by lia. reflexivity.
  - lia.
  - apply BA.ivs_wf_nil.
  - intros q [].
  - intros a Ha. cbn in Ha. discriminate.
  - unfold h', mmap_fixed_rw_next, grants. cbn [vm_maps]. rewrite art_live_snoc. cbn [art_ev_live]. exact (bi_maps _ _ _ _ B).
  - unfold h', mmap_fixed_rw_next. cbn [vm_maps]. exact Wm.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - unfold h', mmap_fixed_rw_next. cbn [vm_noaccess]. rewrite Ua, Un. reflexivity.
  - rewrite art_live_snoc. cbn [art_ev_live]. exact (bi_live _ _ _ _ B).
  - rewrite art_live_snoc. cbn [art_ev_live]. lia.
  - rewrite art_windows_snoc, app_nil_r. reflexivity.
  - rewrite art_cost_sum_snoc. cbn [art_cost]. reflexivity.
  - lia.
  - exact Hcb.
  - exact He.
  - intros a Ha. unfold bhid, mkH. change (m_vm_lazy (forget_model [] addr (addr + len) h' model)) with (maps_subtract (m_vm_lazy model) addr (addr + len)).
    rewrite page_in_ranges_subtract_in; [reflexivity | exact Wl |].
    destruct (page_of_byte_in_aligned a addr (addr + len) Hal ltac:(rewrite Z.add_mod, Hal, Hll by lia; reflexivity) Ha) as [P1 P2]. lia.
  - intros a Ha _. rewrite zfill_in by (rewrite Ua, Un; lia). discriminate.
  - intros a Ha. apply zfill_out. rewrite Ua, Un. lia.
  - (* [comment removed for export] *)
    apply (srz_mmap_fixedin_lazy segs scfg Halloc regs pc M rom model w 3 flags aW len K HF HE (bi_halt _ _ _ _ B) H17
             (or_intror eq_refl) mmap_flags_core_32 H10 ltac:(rewrite Ua; unfold page_size; exact Hal) ltac:(rewrite Ua; lia)
             H11 Hlen ltac:(rewrite Ua, Hpr, (bi_top _ _ _ _ B); lia) H12 H13 ltac:(rewrite H14; exact mm1_eq) H15).
    + rewrite Hpr. fold nW. rewrite (bi_resv _ _ _ _ B). apply region_free_intro. intros b s Hbs. rewrite Ua, Un.
      destruct (bs_res_off_resv STATIC R b s HR Hbs); lia.
    + rewrite Hpr. fold nW. rewrite (bi_maps _ _ _ _ B).
      apply (map_contains_intro _ aW nW (fst (toW R)) (snd (toW R))).
      * apply in_or_app. right. destruct (toW R); exact HRin.
      * fold (BA.B (toW R)). rewrite ER1, Ua. exact R1.
      * fold (BA.B (toW R)). fold (BA.S (toW R)). rewrite ER1, ER2, Ua, Un. exact R2.
    + intros _. rewrite Hpr. fold nW.
      apply BA.mmap_fixed_rw_budget_ok_commit_intro; [apply mmap_noreserve_b_32 | exact (bi_wf _ _ _ _ B) |].
      rewrite Ua, Un. fold h.
      pose proof (vm_backing_used_le A model (bi_minv _ _ _ _ B) (bi_awf _ _ _ _ B)).
      pose proof (bi_budget _ _ _ _ B). pose proof (bi_limit _ _ _ _ B).
      rewrite art_cost_sum_snoc in Hcb. cbn [art_cost] in Hcb. unfold h in *. lia.
    + rewrite Hpr. fold nW. cbn [Z.eqb]. rewrite Em.
      apply HK; [exact B' | rewrite <- Em; unfold bmodel_rt; destruct model as [fd [maps lazy mat] io fs proc lim tm]; reflexivity | exact HST |].
      apply view_zfill; try lia.
      * intros a Ha. unfold bhid, mkH. change (m_vm_lazy (forget_model [] addr (addr + len) h' model)) with (maps_subtract (m_vm_lazy model) addr (addr + len)).
        rewrite page_in_ranges_subtract_in; [reflexivity | exact Wl |].
        destruct (page_of_byte_in_aligned a addr (addr + len) Hal ltac:(rewrite Z.add_mod, Hal, Hll by lia; reflexivity) Ha) as [P1 P2]. lia.
      * exact HOUT.
Qed.

(* [comment removed for export] *)
Lemma filter_all_true : forall {T} (f : T -> bool) l, (forall x, In x l -> f x = true) -> List.filter f l = l.
Proof.
  intros T f l H. induction l as [|x l IH]; [reflexivity|]. cbn. rewrite (H x (or_introl eq_refl)).
  f_equal. apply IH. intros y Hy. apply H. right. exact Hy.
Qed.

Lemma live_sum_filter : forall (f : Z * Z -> bool) L, (forall p, In p L -> 0 <= snd p) -> live_sum (List.filter f L) <= live_sum L.
Proof.
  intros f L H. unfold live_sum. induction L as [|q L IH]; cbn [List.filter fold_right]; [lia|].
  pose proof (IH ltac:(intros p Hp; apply H; right; exact Hp)) as IH'. pose proof (H q (or_introl eq_refl)).
  destruct (f q); cbn [fold_right]; lia.
Qed.

Lemma live_ok_filter : forall (f : Z * Z -> bool) L, live_ok L -> live_ok (List.filter f L).
Proof.
  intros f L (H1 & H2 & H3). split; [|split].
  - intros p Hp. apply filter_In in Hp as [Hp _]. exact (H1 p Hp).
  - clear H1 H3. induction L as [|q L IH]; cbn; [constructor|]. inversion H2 as [|x l Hnin Hnd]; subst.
    destruct (f q); cbn; [constructor; [|exact (IH Hnd)] | exact (IH Hnd)].
    intros Hin. apply Hnin. apply in_map_iff in Hin as (p & E & Hp). apply filter_In in Hp as [Hp _].
    apply in_map_iff. exists p. split; assumption.
  - intros p p' Hp Hp'. apply filter_In in Hp as [Hp _]. apply filter_In in Hp' as [Hp' _]. exact (H3 p p' Hp Hp').
Qed.

(* [comment removed for export] *)
Lemma maps0_apart_live : forall L p q, live_ok L -> In p L -> In q MAPS0 ->
  BA.B q + BA.S q <= fst p \/ fst p + snd p <= BA.B q.
Proof.
  intros L p q (Hl & _ & _) Hp Hq. destruct (Hl p Hp) as (_ & _ & _ & _ & _ & _ & Hk).
  assert (Hkin : In (ivZ q) KN0) by (unfold KN0; apply in_map; apply in_or_app; right; exact Hq).
  unfold BA.B, BA.S. destruct (Hk _ Hkin) as [K|K]; unfold ivZ in K; cbn [fst snd] in K; lia.
Qed.

Lemma map_remove_live : forall log addr len,
  live_ok (art_live log) -> In (addr, len) (art_live log) ->
  map_remove (grants log ++ MAPS0) (Z_to_bv 64 addr) = grants (log ++ [AMunmap addr len]) ++ MAPS0.
Proof.
  intros log addr len HL Hin. unfold map_remove, grants. rewrite filter_app, art_live_snoc. cbn [art_ev_live].
  destruct (live_word _ _ HL Hin) as (E1 & E2 & P1 & P2 & P3). cbn [fst snd] in *.
  f_equal.
  - apply filter_map_ext. intros p Hp. destruct (live_word _ _ HL Hp) as (F1 & _ & Q1 & Q2 & Q3).
    unfold toW. cbn [fst]. f_equal. unfold bv_eqb. rewrite !u64z by lia. reflexivity.
  - apply filter_all_true. intros q Hq. apply negb_true_iff. apply bv_eqb_neq. intros E.
    pose proof (maps0_apart_live _ _ q HL Hin Hq) as Hap. pose proof (bs_maps_pos STATIC q Hq) as Hs.
    unfold BA.B in Hap. rewrite E, (u64z addr) in Hap by lia. cbn [fst snd] in Hap. lia.
Qed.

Lemma bridge_munmap : forall log A regs pc M rom model addr len K,
  BInv log A M model -> art_at_ecall segs pc -> art_munmap_args regs addr len ->
  EVOK log (AMunmap addr len) ->
  (forall M' model', BInv (log ++ [AMunmap addr len]) A M' model' -> bmodel_rt model model' ->
     bstep A M model A M' model' addr (addr + len) false ->
     mrestrict (bhid A model') M' = art_unmap (mrestrict (bhid A model) M) addr len ->
     srealizes segs scfg (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (Z_to_bv 64 (bv_unsigned pc + 4)) M' rom) model') K) ->
  srealizes segs scfg (mkCfg (mkst regs pc M rom) model) K.
Proof.
  intros log A regs pc M rom model addr len K B (w & HF & HE) (H17 & H10 & H11) Hlive HK.
  cbn [art_EVOK] in Hlive.
  pose proof (bi_live _ _ _ _ B) as HL.
  destruct (live_word _ _ HL Hlive) as (E1 & E2 & Hpos & Hlen & H64). cbn [fst snd] in *.
  destruct HL as (Hl & Hnd & Hap). destruct (Hl _ Hlive) as (_ & _ & Hal & Hll & Hce & Hsh & Hk). cbn [fst snd] in *.
  destruct (bs_ceil STATIC) as (Hc1 & Hc2 & Hc3).
  set (aW := Z_to_bv 64 addr). set (nW := Z_to_bv 64 len).
  assert (Ua : bv_unsigned aW = addr) by (apply u64z; lia).
  assert (Un : bv_unsigned nW = len) by (apply u64z; lia).
  assert (Hpr : page_round_up_Z len = len) by (apply AllocSim.page_round_up_Z_aligned; [lia | exact Hll]).
  set (h := m_vmmaps model).
  set (h' := munmap_vmmaps aW nW h).
  assert (Em : munmap_model aW nW model = forget_model [] addr (addr + len) h' model).
  { rewrite munmap_model_eq, Ua, Un. reflexivity. }
  destruct (bi_wf _ _ _ _ B) as (Wm & Wn & Wl & Wsp).
  assert (Hmaps' : vm_maps h' = grants (log ++ [AMunmap addr len]) ++ MAPS0).
  { unfold h', munmap_vmmaps. cbn [vm_maps]. unfold h. rewrite (bi_maps _ _ _ _ B).
    apply map_remove_live; [exact (bi_live _ _ _ _ B) | exact Hlive]. }
  destruct (binv_forget log (log ++ [AMunmap addr len]) A M (unfill aW nW M) model [] addr (addr + len) h' 0 B) as (B' & HOUT & HST).
  - exact Hal.
  - rewrite Z.add_mod, Hal, Hll by lia. reflexivity.
  - lia.
  - apply BA.ivs_wf_nil.
  - intros q [].
  - intros a Ha. cbn in Ha. discriminate.
  - exact Hmaps'.
  - unfold h', munmap_vmmaps. cbn [vm_maps]. unfold map_remove. apply BA.ivs_wf_filter. exact Wm.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - unfold h', munmap_vmmaps. cbn [vm_noaccess]. rewrite Ua, Un. reflexivity.
  - rewrite art_live_snoc. cbn [art_ev_live]. apply live_ok_filter. exact (bi_live _ _ _ _ B).
  - rewrite art_live_snoc. cbn [art_ev_live]. apply live_sum_filter. intros p Hp. destruct (Hl p Hp) as (_ & Hp2 & _). lia.
  - rewrite art_windows_snoc, app_nil_r. reflexivity.
  - rewrite art_cost_sum_snoc. cbn [art_cost]. reflexivity.
  - lia.
  - rewrite art_cost_sum_snoc. cbn [art_cost]. pose proof (bi_cost _ _ _ _ B). lia.
  - rewrite <- Em, Z.add_0_r. apply eager_unmap_le; [exact (bi_wf _ _ _ _ B)|].
    intros q Hq Hne. rewrite (bi_maps _ _ _ _ B) in Hq. rewrite Ua, Un. apply in_app_or in Hq as [Hq|Hq].
    + unfold grants in Hq. apply in_map_iff in Hq as (p & <- & Hp).
      destruct (live_word _ _ (bi_live _ _ _ _ B) Hp) as (F1 & F2 & Q1 & Q2 & Q3). rewrite F1, F2.
      assert (Hne' : fst p <> addr).
      { intros E. unfold toW, aW in Hne. cbn [fst] in Hne. rewrite E, bv_eqb_refl in Hne. discriminate. }
      destruct (Hap p (addr, len) Hp Hlive Hne'); cbn [fst snd] in *; lia.
    + pose proof (maps0_apart_live _ _ q (bi_live _ _ _ _ B) Hlive Hq) as Hq'. cbn [fst snd] in Hq'. lia.
  - intros a Ha. unfold bhid, mkH. change (m_vm_lazy (forget_model [] addr (addr + len) h' model)) with (maps_subtract (m_vm_lazy model) addr (addr + len)).
    rewrite page_in_ranges_subtract_in; [reflexivity | exact Wl |].
    destruct (page_of_byte_in_aligned a addr (addr + len) Hal ltac:(rewrite Z.add_mod, Hal, Hll by lia; reflexivity) Ha) as [P1 P2]. lia.
  - intros a Ha Hs. exfalso. unfold in_shadow_rw, LSH_LO, LSH_HI, HSH_LO, HSH_HI, SHLO, SHHI in *. lia.
  - intros a Ha. unfold unfill. rewrite Ua, Un.
    destruct ((addr <=? bv_unsigned a) && (bv_unsigned a <? addr + len))%bool eqn:E; [|reflexivity].
    apply andb_prop in E as [E3 E4]. apply Z.leb_le in E3. apply Z.ltb_lt in E4. lia.
  - (* [comment removed for export] *)
    apply (AsanNodesLibEK.srz_munmap_lazy segs scfg regs pc M rom model w aW len K HF HE (bi_halt _ _ _ _ B) H17 H10
             ltac:(rewrite Ua; unfold page_size; exact Hal) H11 Hlen ltac:(rewrite Ua, Hpr; unfold TASK_SIZE; lia)).
    + rewrite Hpr. fold nW. rewrite (bi_maps _ _ _ _ B). apply map_has_intro. apply in_or_app. left.
      unfold grants. apply in_map_iff. exists (addr, len). split; [reflexivity | exact Hlive].
    + rewrite Hpr. fold nW. rewrite Em.
      apply HK; [exact B' | rewrite <- Em; unfold bmodel_rt; destruct model as [fd [maps lazy mat] io fs proc lim tm]; reflexivity | exact HST |].
      apply view_unfill; [lia | lia | exact HOUT].
Qed.

(* [comment removed for export] *)
Lemma window_facts : forall r len,
  r mod 4096 = 0 -> len mod 4096 = 0 -> 0 < len -> 4096 <= r -> r + len <= 2 ^ 47 ->
  (r + len <= SHLO \/ SHHI <= r) ->
  window_ok (art_shlo r, art_shhi r len)
  /\ art_shhi r len - art_shlo r <= len / 8 + 8192
  /\ (forall x, art_shlo r <= x < art_shhi r len -> ~ (r <= x < r + len)).
Proof.
  intros r len Hr Hl Hlen H4 H47 Hsh. unfold window_ok, art_shlo, art_shhi, SHLO, SHHI, LSH_LO, LSH_HI, HSH_LO, HSH_HI in *.
  cbn [fst snd].
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  repeat split; try lia.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

Lemma gw_sizes_app : forall l1 l2, AsanPlacement.gw_sizes (l1 ++ l2) = AsanPlacement.gw_sizes l1 + AsanPlacement.gw_sizes l2.
Proof. induction l1 as [|q l1 IH]; intros l2; cbn [app AsanPlacement.gw_sizes]; [lia | rewrite IH; lia]. Qed.

Lemma gw_sizes_grants : forall L, live_ok L -> AsanPlacement.gw_sizes (map toW L) = live_sum L.
Proof.
  intros L HL. assert (H : forall p, In p L -> BA.S (toW p) = snd p) by (intros p Hp; apply (live_word L p HL Hp)).
  clear HL. unfold live_sum. induction L as [|q L IH]; cbn [map AsanPlacement.gw_sizes fold_right]; [reflexivity|].
  rewrite IH by (intros p Hp; apply H; right; exact Hp).
  pose proof (H q (or_introl eq_refl)) as Hq. unfold BA.S in Hq. rewrite Hq. reflexivity.
Qed.

Lemma grant_exists : forall log A M model len,
  BInv log A M model -> 0 < len <= LENMAX -> Z.of_nat (length (art_live log)) < KMAX ->
  exists a : word, grant_ok_na_pin model a len = true.
Proof.
  intros log A M model len B Hlen HK.
  destruct (bs_budget STATIC) as (HB0 & HK0 & HL0). pose proof (bs_gap STATIC) as Hgap.
  set (h := m_vmmaps model).
  assert (EL : vm_reserved h ++ vm_maps h = RESV0 ++ grants log ++ MAPS0)
    by (unfold h; rewrite (bi_resv _ _ _ _ B), (bi_maps _ _ _ _ B); reflexivity).
  assert (Hsz : AsanPlacement.gw_sizes (vm_reserved h ++ vm_maps h) <= AsanPlacement.gw_sizes (RESV0 ++ MAPS0) + BUDGET).
  { rewrite EL, !gw_sizes_app. unfold grants. rewrite (gw_sizes_grants _ (bi_live _ _ _ _ B)).
    pose proof (bi_livesum _ _ _ _ B). pose proof (bi_cost _ _ _ _ B). lia. }
  assert (Hlen' : Z.of_nat (length (vm_reserved h ++ vm_maps h)) <= Z.of_nat (length (RESV0 ++ MAPS0)) + KMAX).
  { rewrite EL, !length_app. unfold grants. rewrite length_map. lia. }
  destruct (AsanPlacement.free_gap_of_totals h len (AsanPlacement.gw_sizes (RESV0 ++ MAPS0) + BUDGET) ltac:(lia) Hsz)
    as (g & Hal & Hfl & Hc & Hfree & _).
  { assert (Hm : Z.of_nat (length (vm_reserved h ++ vm_maps h)) * (len + 4095)
                 <= (Z.of_nat (length (RESV0 ++ MAPS0)) + KMAX) * (LENMAX + 4095)).
    { apply Z.mul_le_mono_nonneg; lia. }
    lia. }
  destruct (bi_wf _ _ _ _ B) as (_ & _ & _ & Wsp).
  pose proof (AsanCeil.alloc_ceiling_le_alloc_top h Wsp) as Htop.
  pose proof AsanCeil.bottomup_floor_val as Hfv. pose proof AsanCeil.alloc_ceiling_val as Hcv.
  exists (Z_to_bv 64 g). unfold grant_ok_na_pin. fold h. rewrite (u64z g) by lia.
  rewrite Hfree. unfold page_size in Hal |- *.
  rewrite (proj2 (Z.eqb_eq _ _) Hal), (proj2 (Z.ltb_lt 0 g)) by lia.
  rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity.
Qed.

Lemma aligned_pos_ge : forall r, r mod 4096 = 0 -> 0 < r -> 4096 <= r.
Proof.
  intros r H1 H2.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  lia.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

Lemma grant_parts : forall model (a : word) n,
  grant_ok_na_pin model a n = true ->
  bv_unsigned a mod 4096 = 0 /\ 0 < bv_unsigned a /\ bv_unsigned a + n <= alloc_top (m_vmmaps model)
  /\ region_free (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) a (Z_to_bv 64 n) = true.
Proof.
  intros model a n H. unfold grant_ok_na_pin in H.
  apply andb_true_iff in H as [H Hrf]. apply andb_true_iff in H as [H Htop]. apply andb_true_iff in H as [Hal Hpos].
  apply Z.eqb_eq in Hal. apply Z.ltb_lt in Hpos. apply Z.leb_le in Htop. unfold page_size in Hal. auto.
Qed.

(* [comment removed for export] *)
Lemma apart_of_covered : forall l (a n : word) lo hi,
  region_free l a n = true -> 0 < bv_unsigned n -> lo < hi ->
  (forall x, lo <= x < hi -> BA.covered l x = true) ->
  bv_unsigned a + bv_unsigned n <= lo \/ hi <= bv_unsigned a.
Proof.
  intros l a n lo hi Hrf Hn Hlh Hcov.
  destruct (Z_le_dec (bv_unsigned a + bv_unsigned n) lo) as [L|L]; [left; exact L|].
  destruct (Z_le_dec hi (bv_unsigned a)) as [R|R]; [right; exact R|]. exfalso.
  set (x := Z.max (bv_unsigned a) lo).
  pose proof (Hcov x ltac:(unfold x; lia)) as Hc. rewrite <- in_ivs_covered in Hc.
  rewrite (region_free_sem l a n x Hrf Hn ltac:(unfold x; lia)) in Hc. discriminate.
Qed.

Lemma binv_null : forall log A M model len (a : word),
  BInv log A M model -> EVOK log (AMmapNull len 0) -> grant_ok_na_pin model a len = true ->
  let r := bv_unsigned a in
  let nW := Z_to_bv 64 len in
  let w := (art_shlo r, art_shhi r len) in
  let model' := mmap_model a nW model in
  GR log (mrestrict (bhid A model) M) len r
  /\ BInv (log ++ [AMmapNull len r]) (A ++ [w]) (zfill a nW M) model'
  /\ bmodel_rt model model'
  /\ mrestrict (bhid (A ++ [w]) model') (zfill a nW M)
     = art_reveal (art_zfill (mrestrict (bhid A model) M) r len) (art_shlo r) (art_shhi r len)
  /\ bstep A M model (A ++ [w]) (zfill a nW M) model' (art_shlo r) (art_shhi r len) false.
Proof.
  intros log A M model len a B (Hlen & Hll & Hmax & HKc & Hcb) Hg r nW w model'.
  destruct (grant_parts model a len Hg) as (Hal & Hpos & Htop & Hrf). fold r in Hal, Hpos, Htop.
  rewrite (bi_top _ _ _ _ B) in Htop. rewrite (bi_resv _ _ _ _ B), (bi_maps _ _ _ _ B) in Hrf.
  destruct (bs_ceil STATIC) as (Hc1 & Hc2 & Hc3). destruct (bs_budget STATIC) as (HB0 & HK0 & HL0).
  unfold stack_max_size in Hc2.
  assert (Un : bv_unsigned nW = len) by (apply u64z; lia).
  assert (Ea : Z_to_bv 64 r = a) by (apply Z_to_bv_u_eq'; reflexivity).
  fold nW in Hrf.
  (* [comment removed for export] *)
  assert (Hent : forall b s, In (b, s) (RESV0 ++ grants log ++ MAPS0) ->
            r + len <= bv_unsigned b \/ bv_unsigned b + bv_unsigned s <= r).
  { intros b s Hin. pose proof (region_free_In _ a nW b s Hrf Hin) as H. rewrite Un in H. exact H. }
  assert (Hsh : r + len <= SHLO \/ SHHI <= r).
  { assert (Hrf0 : region_free MAPS0 a nW = true).
    { rewrite !region_free_app in Hrf. apply andb_prop in Hrf as [_ Hrf]. apply andb_prop in Hrf as [_ Hrf]. exact Hrf. }
    pose proof (apart_of_covered MAPS0 a nW SHLO SHHI Hrf0 ltac:(lia) ltac:(unfold SHLO, SHHI; lia) (bs_sh_in STATIC)) as H.
    rewrite Un in H. exact H. }
  pose proof (aligned_pos_ge r Hal Hpos) as H4k.
  destruct (window_facts r len Hal Hll Hlen H4k ltac:(lia) Hsh) as (Wok & Wsz & Wdis).
  destruct Wok as (Wa & Wb & Wle & Wsh). cbn [fst snd] in Wa, Wb, Wle, Wsh.
  assert (Hlive_ap : forall p, In p (art_live log) -> r + len <= fst p \/ fst p + snd p <= r).
  { intros p Hp. destruct (live_word _ _ (bi_live _ _ _ _ B) Hp) as (F1 & F2 & _).
    pose proof (Hent (fst (toW p)) (snd (toW p))) as H. fold (BA.B (toW p)) in H. fold (BA.S (toW p)) in H.
    rewrite F1, F2 in H. apply H. apply in_or_app. right. apply in_or_app. left. unfold grants.
    apply in_map_iff. exists p. split; [destruct (toW p); reflexivity | exact Hp]. }
  assert (Hkn_ap : forall q, In q KN0 -> r + len <= fst q \/ snd q <= r).
  { intros q Hq. unfold KN0 in Hq. apply in_map_iff in Hq as ([b s] & <- & Hin). unfold ivZ. cbn [fst snd].
    apply Hent. apply in_app_or in Hin as [Hin|Hin]; apply in_or_app; [left; exact Hin | right; apply in_or_app; right; exact Hin]. }
  (* [comment removed for export] *)
  assert (Hnl : forall x : word, r <= bv_unsigned x < r + len -> page_in_ranges (page_base x) (m_vm_lazy model) = false).
  { intros x Hx. destruct (page_in_ranges (page_base x) (m_vm_lazy model)) eqn:E; [|reflexivity]. exfalso.
    destruct (bi_lazy_in _ _ _ _ B x E) as [Hcov _]. rewrite <- in_ivs_covered in Hcov.
    apply in_ivs_true' in Hcov as ([b s] & Hin & Hb). cbn [fst snd] in Hb.
    destruct (Hent b s ltac:(apply in_or_app; right; apply in_or_app; right; exact Hin)); lia. }
  assert (HW2 : forall x : word, ~ (art_shlo r <= bv_unsigned x < art_shhi r len) ->
                  bhid (A ++ [w]) model' x = bhid A model x).
  { intros x Hx. unfold bhid, mkH. change (m_vm_lazy model') with (m_vm_lazy model). f_equal. f_equal.
    unfold page_allowedb. rewrite existsb_app. cbn [existsb]. rewrite orb_false_r.
    replace ((fst w <=? bv_unsigned (page_base x)) && (bv_unsigned (page_base x) + page_size <=? snd w))%bool with false;
      [apply orb_false_r|].
    symmetry. apply andb_false_iff. unfold page_size, w. cbn [fst snd].
    destruct (page_of_byte_out_aligned x (art_shlo r) (art_shhi r len) Wa Wb ltac:(lia)) as [P|P];
      [left; apply Z.leb_gt; lia | right; apply Z.leb_gt; lia]. }
  assert (HW1 : forall x : word, art_shlo r <= bv_unsigned x < art_shhi r len -> bhid (A ++ [w]) model' x = false).
  { intros x Hx. unfold bhid, mkH.
    rewrite (page_allowed_in (A ++ [w]) w x); [apply andb_false_r | apply in_or_app; right; left; reflexivity | exact Wa | exact Wb | exact Hx]. }
  split; [|split; [|split; [|split]]].
  - (* [comment removed for export] *) unfold art_GR. repeat split; try assumption; lia.
  - (* [comment removed for export] *)
    destruct (bi_wf _ _ _ _ B) as (Wm & Wn & Wl & Wsp).
    assert (Ecost : art_cost_sum (log ++ [AMmapNull len r]) = art_cost_sum log + (len + len / 8 + 8192))
      by (rewrite art_cost_sum_snoc; reflexivity).
    assert (Ecost0 : art_cost_sum (log ++ [AMmapNull len 0]) = art_cost_sum log + (len + len / 8 + 8192))
      by (rewrite art_cost_sum_snoc; reflexivity).
    assert (He : eager_used model' <= eager_used model + len).
    { rewrite <- Un. unfold model', mmap_model.
      apply (eager_grant_le model a nW); [exact (bi_wf _ _ _ _ B) | fold r; rewrite Un; lia | reflexivity | reflexivity]. }
    constructor.
    + exact (bi_halt _ _ _ _ B).
    + unfold A_wf. apply Forall_app. split; [exact (bi_awf _ _ _ _ B)|]. constructor; [|constructor].
      unfold w, page_size. cbn [fst snd]. repeat split; assumption.
    + destruct (bi_minv _ _ _ _ B) as [Hnd Hal' Hall Hlz Hbud]. constructor.
      * exact Hnd.
      * exact Hal'.
      * intros p Hp. unfold page_allowedb. rewrite existsb_app. apply orb_true_iff. left. exact (Hall p Hp).
      * exact Hlz.
      * rewrite A_bytes_app'. unfold w. cbn [A_bytes fst snd]. change (vm_limit (m_vmmaps model')) with (vm_limit (m_vmmaps model)).
        pose proof (bi_budget _ _ _ _ B). pose proof (bi_limit _ _ _ _ B). lia.
    + unfold BA.model_ivs_wf. change (m_vm_lazy model') with (m_vm_lazy model).
      split; [|split; [exact Wn | split; [exact Wl | exact Wsp]]].
      apply BA.ivs_wf_cons; [|exact Wm]. unfold BA.iv_wf, BA.B, BA.S. cbn [fst snd]. fold r. rewrite Un. lia.
    + change (vm_maps (m_vmmaps model')) with ((a, nW) :: vm_maps (m_vmmaps model)). rewrite (bi_maps _ _ _ _ B).
      unfold grants. rewrite art_live_snoc. cbn [art_ev_live map].
      change (toW (r, len)) with (Z_to_bv 64 r, nW). rewrite Ea. reflexivity.
    + exact (bi_resv _ _ _ _ B).
    + exact (bi_top _ _ _ _ B).
    + exact (bi_limit _ _ _ _ B).
    + exact (bi_noacc _ _ _ _ B).
    + exact (bi_noacc_pos _ _ _ _ B).
    + exact (bi_lazy_in _ _ _ _ B).
    + rewrite art_live_snoc. cbn [art_ev_live]. destruct (bi_live _ _ _ _ B) as (L1 & L2 & L3). split; [|split].
      * intros p [<-|Hp]; [cbn [fst snd]; repeat split; try assumption; lia | exact (L1 p Hp)].
      * cbn [map fst]. constructor; [|exact L2]. intros Hin. apply in_map_iff in Hin as (p & E & Hp).
        destruct (L1 p Hp) as (_ & P2 & _). destruct (Hlive_ap p Hp); lia.
      * intros p p' [<-|Hp] [<-|Hp'] Hne; cbn [fst snd] in *.
        -- contradiction.
        -- destruct (Hlive_ap p' Hp'); lia.
        -- destruct (Hlive_ap p Hp); lia.
        -- exact (L3 p p' Hp Hp' Hne).
    + intros x Hx Hna.
      assert (Hx0 : bhid A model x = true).
      { unfold bhid, mkH in Hx |- *. change (m_vm_lazy model') with (m_vm_lazy model) in Hx.
        apply andb_prop in Hx as [X1 X2]. rewrite X1. cbn [andb]. apply negb_true_iff. apply negb_true_iff in X2.
        unfold page_allowedb in X2 |- *. rewrite existsb_app in X2. apply orb_false_iff in X2 as [X2 _]. exact X2. }
      assert (Hout : ~ (r <= bv_unsigned x < r + len)).
      { intros Hin. unfold bhid, mkH in Hx0. rewrite (Hnl x Hin) in Hx0. discriminate. }
      rewrite zfill_out by (fold r; rewrite Un; lia). exact (bi_zero _ _ _ _ B x Hx0 Hna).
    + intros x Hx. destruct (Z_le_dec r (bv_unsigned x)) as [L|L]; [destruct (Z_lt_dec (bv_unsigned x) (r + len)) as [U|U]|].
      * rewrite zfill_in by (fold r; rewrite Un; lia). discriminate.
      * rewrite zfill_out by (fold r; rewrite Un; lia). exact (bi_shdef _ _ _ _ B x Hx).
      * rewrite zfill_out by (fold r; rewrite Un; lia). exact (bi_shdef _ _ _ _ B x Hx).
    + intros w0 Hw0. rewrite art_windows_snoc in Hw0. apply in_app_or in Hw0 as [Hw0|[<-|[]]].
      * destruct (bi_windows _ _ _ _ B w0 Hw0) as [H1 H2]. split; [apply in_or_app; left; exact H1 | exact H2].
      * split; [apply in_or_app; right; left; reflexivity|]. unfold window_ok. cbn [fst snd]. auto.
    + rewrite A_bytes_app'. unfold w. cbn [A_bytes fst snd]. pose proof (bi_budget _ _ _ _ B). lia.
    + lia.
    + rewrite art_live_snoc. cbn [art_ev_live]. unfold live_sum. cbn [fold_right snd]. fold (live_sum (art_live log)).
      pose proof (bi_livesum _ _ _ _ B). assert (0 <= len / 8) by (apply Z.div_pos; lia). lia.
  - unfold bmodel_rt, model', mmap_model. destruct model as [fd [maps lazy mat] io fs proc lim tm]. reflexivity.
  - (* [comment removed for export] *)
    set (H0 := bhid A model). set (H1 := bhid A model'). set (H2 := bhid (A ++ [w]) model').
    assert (E1 : mrestrict H1 (zfill a nW M) = art_zfill (mrestrict H0 M) r len).
    { rewrite <- Ea at 1. unfold nW. apply view_zfill; try lia.
      - intros x Hx. unfold H1, bhid, mkH. change (m_vm_lazy model') with (m_vm_lazy model). rewrite (Hnl x Hx). reflexivity.
      - intros x _. reflexivity. }
    rewrite <- E1. apply view_reveal.
    + intros x Hx.
      assert (Hxs : in_shadow_rw (bv_unsigned x)) by (unfold in_shadow_rw; lia).
      assert (Hxo : ~ (r <= bv_unsigned x < r + len)) by (apply Wdis; exact Hx).
      split; [|split].
      * unfold H2, bhid, mkH. rewrite (page_allowed_in (A ++ [w]) w x); [apply andb_false_r | apply in_or_app; right; left; reflexivity | exact Wa | exact Wb | exact Hx].
      * rewrite zfill_out by (fold r; rewrite Un; lia). exact (bi_shdef _ _ _ _ B x Hxs).
      * intros Hh. rewrite zfill_out by (fold r; rewrite Un; lia). apply (bi_zero _ _ _ _ B x Hh).
        destruct (BA.covered (vm_noaccess (m_vmmaps model)) (bv_unsigned x)) eqn:E; [|reflexivity].
        pose proof (bi_noacc _ _ _ _ B _ E) as E'. rewrite (bs_shrw_acc STATIC _ Hxs) in E'. discriminate.
    + intros x Hx. unfold H2, H1, bhid, mkH. f_equal. f_equal. unfold page_allowedb. rewrite existsb_app. cbn [existsb].
      rewrite orb_false_r.
      replace ((fst w <=? bv_unsigned (page_base x)) && (bv_unsigned (page_base x) + page_size <=? snd w))%bool with false;
        [apply orb_false_r|].
      symmetry. apply andb_false_iff. unfold page_size, w. cbn [fst snd].
      destruct (page_of_byte_out_aligned x (art_shlo r) (art_shhi r len) Wa Wb ltac:(lia)) as [P|P];
        [left; apply Z.leb_gt; lia | right; apply Z.leb_gt; lia].
  - (* [comment removed for export] *)
    split; [intros q Hq; apply in_or_app; left; exact Hq|]. split; [|split; [|split]].
    3:{ intros w0 Hw0. apply in_app_or in Hw0 as [Hw0|[<-|[]]]; [left; exact Hw0 | right; reflexivity]. }
    3:{ intros x Hx. left. exact Hx. }
    + intros x Hx.
      assert (Hnw : ~ (art_shlo r <= bv_unsigned x < art_shhi r len)) by (intros Hin; rewrite (HW1 x Hin) in Hx; discriminate).
      rewrite (HW2 x Hnw) in Hx. split; [exact Hx|].
      apply zfill_out. fold r. rewrite Un.
      destruct (Z_lt_dec (bv_unsigned x) r) as [L|L]; [left; exact L|].
      destruct (Z_le_dec (r + len) (bv_unsigned x)) as [U|U]; [right; exact U|].
      exfalso. unfold bhid, mkH in Hx. rewrite (Hnl x ltac:(lia)) in Hx. discriminate.
    + intros x Hx Hx'. destruct (Z_le_dec (art_shlo r) (bv_unsigned x)) as [L|L]; [destruct (Z_lt_dec (bv_unsigned x) (art_shhi r len)) as [U|U]|].
      * lia.
      * rewrite (HW2 x ltac:(lia)), Hx in Hx'. discriminate.
      * rewrite (HW2 x ltac:(lia)), Hx in Hx'. discriminate.
Qed.

(* [comment removed for export] *)
Lemma bridge_null : forall log A regs pc M rom model len K,
  BInv log A M model -> art_at_ecall segs pc -> art_mmap_args regs 0 len 34 ->
  EVOK log (AMmapNull len 0) ->
  (forall r A' M' model', GR log (mrestrict (bhid A model) M) len r ->
     BInv (log ++ [AMmapNull len r]) A' M' model' -> bmodel_rt model model' ->
     bstep A M model A' M' model' (art_shlo r) (art_shhi r len) false ->
     mrestrict (bhid A' model') M'
       = art_reveal (art_zfill (mrestrict (bhid A model) M) r len) (art_shlo r) (art_shhi r len) ->
     srealizes segs scfg (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 r)) (Z_to_bv 64 (bv_unsigned pc + 4)) M' rom) model') K) ->
  srealizes segs scfg (mkCfg (mkst regs pc M rom) model) K.
Proof.
  intros log A regs pc M rom model len K B (w & HF & HE) (H17 & H10 & H11 & H12 & H13 & H14 & H15) Hev HK.
  pose proof Hev as (Hlen & Hll & Hmax & HKc & Hcb).
  destruct (bs_budget STATIC) as (HB0 & HK0 & HL0).
  assert (Hpr : page_round_up_Z len = len) by (apply AllocSim.page_round_up_Z_aligned; [lia | exact Hll]).
  apply (srz_mmap_rw1 segs scfg Halloc regs pc M rom model w len (Z_to_bv 64 34) K HF HE (bi_halt _ _ _ _ B) H17 H11
           ltac:(lia) H12 H13 mmap_flags_core_22 ltac:(rewrite H14; exact mm1_eq) H15).
  - rewrite Hpr. exact (grant_exists log A M model len B ltac:(lia) HKc).
  - rewrite Hpr. unfold mmap_noreserve_backed_ok. rewrite mmap_noreserve_b_22. apply Z.leb_le.
    pose proof (vm_backing_used_le A model (bi_minv _ _ _ _ B) (bi_awf _ _ _ _ B)).
    pose proof (bi_budget _ _ _ _ B). pose proof (bi_limit _ _ _ _ B).
    rewrite art_cost_sum_snoc in Hcb. cbn [art_cost] in Hcb.
    assert (0 <= len / 8) by (apply Z.div_pos; lia). lia.
  - rewrite Hpr. intros a Hg.
    destruct (binv_null log A M model len a B Hev Hg) as (HGR & B' & Hrt & Hview & HST).
    unfold with_mmap_backing. rewrite mmap_noreserve_b_22.
    pose proof (HK (bv_unsigned a) _ _ _ HGR B' Hrt HST Hview) as HK'.
    replace (Z_to_bv 64 (bv_unsigned a)) with a in HK' by (symmetry; apply Z_to_bv_u_eq'; reflexivity).
    exact HK'.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma sbm_madvise : forall m (a n : word), same_but_materialized m (madvise_dontneed_next m a n).
Proof. intros m a n. unfold same_but_materialized, madvise_dontneed_next. destruct m as [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.

Lemma minv_madvise : forall A m (a n : word), MInv A m -> MInv A (madvise_dontneed_next m a n).
Proof.
  intros A m a n [N1 N2 N3 N4 N5].
  destruct (same_but_materialized_frame _ _ (sbm_madvise m a n)) as (_ & Hvm & Hlz & _).
  assert (Hmat : m_vm_materialized (madvise_dontneed_next m a n)
                 = List.filter (page_outside_range (bv_unsigned a) (bv_unsigned a + bv_unsigned n)) (m_vm_materialized m)).
  { unfold madvise_dontneed_next. destruct m as [fd [maps lazy mat] io fs proc lim tm]. reflexivity. }
  constructor.
  - rewrite Hmat. apply NoDup_filter. exact N1.
  - intros p Hp. rewrite Hmat in Hp. apply filter_In in Hp as [Hp _]. exact (N2 p Hp).
  - intros p Hp. rewrite Hmat in Hp. apply filter_In in Hp as [Hp _]. exact (N3 p Hp).
  - intros p Hp. rewrite Hmat in Hp. apply filter_In in Hp as [Hp _]. rewrite Hlz. exact (N4 p Hp).
  - rewrite Hvm. rewrite (eager_used_ext (madvise_dontneed_next m a n) m) by assumption. exact N5.
Qed.

Lemma binv_snoc_madvise : forall log A M model addr len,
  BInv log A M model -> BInv (log ++ [AMadvise addr len]) A M model.
Proof.
  intros log A M model addr len B. destruct B. constructor; try assumption.
  - unfold grants. rewrite art_live_snoc. exact bi_maps0.
  - rewrite art_live_snoc. exact bi_live0.
  - intros w Hw. rewrite art_windows_snoc, app_nil_r in Hw. exact (bi_windows0 w Hw).
  - rewrite art_cost_sum_snoc. cbn [art_cost]. lia.
  - rewrite art_cost_sum_snoc. cbn [art_cost]. lia.
  - rewrite art_live_snoc, art_cost_sum_snoc. cbn [art_ev_live art_cost]. lia.
Qed.

Lemma bridge_madvise : forall log A regs pc M rom model addr len K,
  BInv log A M model -> art_at_ecall segs pc -> art_madvise_args regs addr len ->
  EVOK log (AMadvise addr len) ->
  (forall M' model', BInv (log ++ [AMadvise addr len]) A M' model' -> bmodel_rt model model' ->
     bstep A M model A M' model' addr (addr + len) false ->
     mrestrict (bhid A model') M' = art_zfill (mrestrict (bhid A model) M) addr len ->
     srealizes segs scfg (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (Z_to_bv 64 (bv_unsigned pc + 4)) M' rom) model') K) ->
  srealizes segs scfg (mkCfg (mkst regs pc M rom) model) K.
Proof.
  intros log A regs pc M rom model addr len K B (w & HF & HE) (H17 & H10 & H11 & H12)
         (Hal & Hll & Hlen & (win & Hwin & W1 & W2)) HK.
  destruct (bi_windows _ _ _ _ B win Hwin) as [HwA (Wa & Wb & Wle & Wsh)].
  assert (Hsub : (LSH_LO <= addr /\ addr + len <= LSH_HI) \/ (HSH_LO <= addr /\ addr + len <= HSH_HI)) by lia.
  destruct (shadow_rw_facts addr (addr + len) ltac:(lia) Hsub) as (Hpos & Hhi & Hlo & Hsh).
  destruct (bs_ceil STATIC) as (Hc1 & Hc2 & Hc3).
  assert (Hend : addr + len < 2 ^ 64) by (unfold stack_max_size in Hc2; lia).
  set (aW := Z_to_bv 64 addr). set (nW := Z_to_bv 64 len).
  assert (Ua : bv_unsigned aW = addr) by (apply u64z; lia).
  assert (Un : bv_unsigned nW = len) by (apply u64z; lia).
  set (model' := madvise_dontneed_next model aW nW).
  assert (Hs : same_but_materialized model model') by apply sbm_madvise.
  destruct (same_but_materialized_frame _ _ Hs) as (_ & _ & Hlz & _).
  assert (EH : bhid A model' = bhid A model) by (unfold bhid; rewrite Hlz; reflexivity).
  assert (Hvis : forall a : word, addr <= bv_unsigned a < addr + len -> bhid A model a = false).
  { intros a Ha. unfold bhid, mkH. rewrite (page_allowed_in A win a HwA Wa Wb ltac:(lia)). apply andb_false_r. }
  assert (B' : BInv (log ++ [AMadvise addr len]) A (zfill aW nW M) model').
  { apply binv_snoc_madvise. apply (binv_sbm log A M model); [exact B | apply minv_madvise; exact (bi_minv _ _ _ _ B) | exact Hs | |].
    - intros a Ha. apply zfill_out. rewrite Ua, Un.
      destruct (Z_lt_dec (bv_unsigned a) addr) as [L|L]; [left; exact L|].
      destruct (Z_le_dec (addr + len) (bv_unsigned a)) as [U|U]; [right; exact U|].
      exfalso. rewrite (Hvis a ltac:(lia)) in Ha. discriminate.
    - intros a Ha. destruct (Z_le_dec addr (bv_unsigned a)) as [L|L]; [destruct (Z_lt_dec (bv_unsigned a) (addr + len)) as [U|U]|].
      + rewrite zfill_in by (rewrite Ua, Un; lia). discriminate.
      + rewrite zfill_out by (rewrite Ua, Un; lia). exact (bi_shdef _ _ _ _ B a Ha).
      + rewrite zfill_out by (rewrite Ua, Un; lia). exact (bi_shdef _ _ _ _ B a Ha). }
  apply (srz_madvise_lazy segs scfg regs pc M rom model w aW len K HF HE (bi_halt _ _ _ _ B) H17 H10
           ltac:(rewrite Ua; unfold page_size; exact Hal) H11 Hlen Hll ltac:(rewrite Ua; exact Hend) H12).
  - fold nW. unfold madvise_dontneed_ok. apply andb_true_intro. split; [apply andb_true_intro; split|].
    + rewrite (bi_resv _ _ _ _ B).
      replace nW with (Z_to_bv 64 (addr + len - addr)) by (unfold nW; f_equal; lia).
      apply region_free_resv_shadow; try lia. exact Hsh.
    + rewrite (bi_maps _ _ _ _ B).
      destruct (bs_shrw_entry STATIC addr (addr + len) ltac:(lia) Hsub) as (b & s & Hbs & B1 & B2).
      apply (map_contains_intro _ aW nW b s); [apply in_or_app; right; exact Hbs | rewrite Ua; exact B1 | rewrite Ua, Un; exact B2].
    + apply region_free_intro. intros b s Hbs. rewrite Ua, Un.
      pose proof (bi_noacc_pos _ _ _ _ B (b, s) Hbs) as Hsp. cbn [snd] in Hsp.
      destruct (bi_wf _ _ _ _ B) as (_ & Wn & _). pose proof (Wn (b, s) Hbs) as Hwf. unfold BA.iv_wf, BA.B, BA.S in Hwf. cbn [fst snd] in Hwf.
      destruct (Z_le_dec (addr + len) (bv_unsigned b)) as [L|L]; [left; exact L|].
      destruct (Z_le_dec (bv_unsigned b + bv_unsigned s) addr) as [R|R]; [right; exact R|]. exfalso.
      (* [comment removed for export] *)
      set (x := Z.max (bv_unsigned b) addr).
      assert (Hx : addr <= x < addr + len) by (unfold x; lia).
      assert (Hcov : BA.covered (vm_noaccess (m_vmmaps model)) x = true).
      { rewrite <- in_ivs_covered. apply in_ivs_true'. exists (b, s). split; [exact Hbs | cbn [fst snd]; unfold x; lia]. }
      pose proof (bi_noacc _ _ _ _ B x Hcov) as E'. rewrite (bs_shrw_acc STATIC x (Hsh x Hx)) in E'. discriminate.
  - fold nW. fold model'.
    apply HK; [exact B' | apply bmodel_rt_sbm; exact Hs | |].
    { split; [apply incl_refl|]. split; [|split; [|split]]; [| |intros w0 Hw0; left; exact Hw0 | intros x Hx; left; rewrite <- Hlz; exact Hx].
      - intros x Hx. rewrite EH in Hx. split; [exact Hx|]. apply zfill_out. rewrite Ua, Un.
        destruct (Z_lt_dec (bv_unsigned x) addr) as [L|L]; [left; exact L|].
        destruct (Z_le_dec (addr + len) (bv_unsigned x)) as [U|U]; [right; exact U|].
        exfalso. rewrite (Hvis x ltac:(lia)) in Hx. discriminate.
      - intros x Hx Hx'. rewrite EH, Hx in Hx'. discriminate. }
    rewrite EH. apply view_zfill; try lia.
    + exact Hvis.
    + intros a _. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma restrict_mkst : forall (H : word -> bool) regs pc M rom,
  restrict H (mkst regs pc M rom) = mkst regs pc (mrestrict H M) rom.
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
Definition art_ev_range (ev : aev) : Z * Z :=
  match ev with
  | AMmapFixed a l => (a, a + l) | AMmapFixedNR a l => (a, a + l) | AMunmap a l => (a, a + l) | AMadvise a l => (a, a + l)
  | AMmapNull len r => (art_shlo r, art_shhi r len)
  end.
Definition in_ev_ranges (sfx : list aev) (x : Z) : Prop :=
  exists ev, In ev sfx /\ fst (art_ev_range ev) <= x < snd (art_ev_range ev).
Definition bhist (A0 : list (Z * Z)) (M0 : word -> option byte) (model0 : Model) (log0 : list aev)
                 (log : list aev) (A : list (Z * Z)) (M : word -> option byte) (model : Model) : Prop :=
  exists sfx, log = log0 ++ sfx /\ incl A0 A
  /\ (forall x : word, bhid A model x = true -> bhid A0 model0 x = true /\ M x = M0 x)
  /\ (forall x : word, bhid A0 model0 x = true -> bhid A model x = false -> in_ev_ranges sfx (bv_unsigned x))
  /\ (forall w, In w A -> In w A0 \/ exists len r, In (AMmapNull len r) sfx /\ w = (art_shlo r, art_shhi r len))
     (* [comment removed for export] *)
  /\ (forall x : word, page_in_ranges (page_base x) (m_vm_lazy model) = true ->
        page_in_ranges (page_base x) (m_vm_lazy model0) = true
        \/ exists a l, In (AMmapFixedNR a l) sfx /\ a <= bv_unsigned x < a + l).
     (* [comment removed for export] *)

Lemma bhist_refl : forall A M model log, bhist A M model log log A M model.
Proof.
  intros A M model log. exists []. rewrite app_nil_r. split; [reflexivity|]. split; [apply incl_refl|]. split; [|split; [|split]].
  - intros x Hx. split; [exact Hx | reflexivity].
  - intros x Hx Hx'. rewrite Hx in Hx'. discriminate.
  - intros w Hw. left. exact Hw.
  - intros x Hx. left. exact Hx.
Qed.

(* [comment removed for export] *)
Lemma bhist_step0 : forall A0 M0 model0 log0 log A M model M' model',
  bhist A0 M0 model0 log0 log A M model -> bstep A M model A M' model' 0 0 false ->
  bhist A0 M0 model0 log0 log A M' model'.
Proof.
  intros A0 M0 model0 log0 log A M model M' model' (sfx & El & Hi & H2 & H3 & H4 & H5) (S1 & S2 & S3 & _ & S5).
  exists sfx. split; [exact El|]. split; [exact Hi|]. split; [|split; [|split; [exact H4|]]].
  3:{ intros x Hx. destruct (S5 x Hx) as [Hl|[Hc _]]; [exact (H5 x Hl) | discriminate Hc]. }
  - intros x Hx. destruct (S2 x Hx) as [Hx1 E1]. destruct (H2 x Hx1) as [Hx0 E0]. split; [exact Hx0 | rewrite E1; exact E0].
  - intros x Hx0 Hx'. destruct (bhid A model x) eqn:E.
    + pose proof (S3 x E Hx'). lia.
    + exact (H3 x Hx0 E).
Qed.

(* [comment removed for export] *)
Definition art_ev_nr (ev : aev) : bool := match ev with AMmapFixedNR _ _ => true | _ => false end.
Lemma bhist_step_same : forall A0 M0 model0 log0 log A M model M' model' ev,
  bhist A0 M0 model0 log0 log A M model ->
  bstep A M model A M' model' (fst (art_ev_range ev)) (snd (art_ev_range ev)) (art_ev_nr ev) ->
  bhist A0 M0 model0 log0 (log ++ [ev]) A M' model'.
Proof.
  intros A0 M0 model0 log0 log A M model M' model' ev (sfx & El & Hi & H2 & H3 & H4 & H5) (S1 & S2 & S3 & _ & S5).
  exists (sfx ++ [ev]). split; [rewrite El, app_assoc; reflexivity|]. split; [exact Hi|]. split; [|split; [|split]].
  4:{ intros x Hx. destruct (S5 x Hx) as [Hl|[Hc Hr]].
      - destruct (H5 x Hl) as [H0|(a & l & Hin & Hal)]; [left; exact H0|].
        right. exists a, l. split; [apply in_or_app; left; exact Hin | exact Hal].
      - right. destruct ev as [a l|len r|a l|a l|a l]; try discriminate Hc. cbn [art_ev_range fst snd] in Hr.
        exists a, l. split; [apply in_or_app; right; left; reflexivity | exact Hr]. }
  - intros x Hx. destruct (S2 x Hx) as [Hx1 E1]. destruct (H2 x Hx1) as [Hx0 E0]. split; [exact Hx0 | rewrite E1; exact E0].
  - intros x Hx0 Hx'. destruct (bhid A model x) eqn:E.
    + exists ev. split; [apply in_or_app; right; left; reflexivity | exact (S3 x E Hx')].
    + destruct (H3 x Hx0 E) as (e & He & Hr). exists e. split; [apply in_or_app; left; exact He | exact Hr].
  - intros w Hw. destruct (H4 w Hw) as [Hw0|(len & r & Hin & Ew)]; [left; exact Hw0|].
    right. exists len, r. split; [apply in_or_app; left; exact Hin | exact Ew].
Qed.

(* [comment removed for export] *)
Lemma bhist_step_null : forall A0 M0 model0 log0 log A M model A' M' model' len r,
  bhist A0 M0 model0 log0 log A M model ->
  bstep A M model A' M' model' (art_shlo r) (art_shhi r len) false ->
  bhist A0 M0 model0 log0 (log ++ [AMmapNull len r]) A' M' model'.
Proof.
  intros A0 M0 model0 log0 log A M model A' M' model' len r (sfx & El & Hi & H2 & H3 & H4 & H5) (S1 & S2 & S3 & S4 & S5).
  exists (sfx ++ [AMmapNull len r]). split; [rewrite El, app_assoc; reflexivity|]. split; [exact (incl_tran Hi S1)|]. split; [|split; [|split]].
  4:{ intros x Hx. destruct (S5 x Hx) as [Hl|[Hc _]]; [|discriminate Hc].
      destruct (H5 x Hl) as [H0|(a & l & Hin & Hal)]; [left; exact H0|].
      right. exists a, l. split; [apply in_or_app; left; exact Hin | exact Hal]. }
  - intros x Hx. destruct (S2 x Hx) as [Hx1 E1]. destruct (H2 x Hx1) as [Hx0 E0]. split; [exact Hx0 | rewrite E1; exact E0].
  - intros x Hx0 Hx'. destruct (bhid A model x) eqn:E.
    + exists (AMmapNull len r). split; [apply in_or_app; right; left; reflexivity | exact (S3 x E Hx')].
    + destruct (H3 x Hx0 E) as (e & He & Hr). exists e. split; [apply in_or_app; left; exact He | exact Hr].
  - intros w Hw. destruct (S4 w Hw) as [HwA|Ew].
    + destruct (H4 w HwA) as [Hw0|(len' & r' & Hin & Ew)]; [left; exact Hw0|].
      right. exists len', r'. split; [apply in_or_app; left; exact Hin | exact Ew].
    + right. exists len, r. split; [apply in_or_app; right; left; reflexivity | exact Ew].
Qed.

Theorem aruns_srealizes_h : forall (Q : list aev -> machine_state -> Prop) K model0 A0 M0 modelE log0,
  (forall log A ms model, BInv log A (ms_mem ms) model -> bmodel_rt model0 model ->
     bhist A0 M0 modelE log0 log A (ms_mem ms) model ->
     Q log (restrict (bhid A model) ms) -> srealizes segs scfg (mkCfg ms model) K) ->
  forall log s, aruns segs EVOK GR Q log s ->
  forall A ms model, restrict (bhid A model) ms = s -> BInv log A (ms_mem ms) model -> bmodel_rt model0 model ->
  bhist A0 M0 modelE log0 log A (ms_mem ms) model ->
  srealizes segs scfg (mkCfg ms model) K.
Proof.
  intros Q K model0 A0 M0 modelE log0 HQ log s R. induction R as
    [ log s Hq
    | log s s' MS R IH
    | log regs pc pc' M rom addr len Hpc Epc Hargs Hev R IH
    | log regs pc pc' M rom len Hpc Epc Hargs Hev R IH
    | log regs pc pc' M rom addr len Hpc Epc Hargs Hev R IH
    | log regs pc pc' M rom addr len Hpc Epc Hargs Hev R IH
    | log regs pc pc' M rom addr len Hpc Epc Hargs Hev R IH ];
    intros A ms model Es B Hrt HH.
  - apply (HQ log A ms model B Hrt HH). rewrite Es. exact Hq.
  - subst s. apply (bridge_msteps log A ms model s' K B MS).
    intros ms' model' Es' B' Hrt' HST.
    exact (IH A ms' model' Es' B' (bmodel_rt_trans _ _ _ Hrt Hrt') (bhist_step0 _ _ _ _ _ _ _ _ _ _ HH HST)).
  - destruct (restrict_eq_mkst _ _ _ _ _ _ Es) as [Ems EM]. rewrite Ems. rewrite Ems in B, HH. cbn [ms_mem mkst] in B, HH.
    subst pc'. apply (bridge_fixed log A regs pc (ms_mem ms) rom model addr len K); try assumption.
    intros M' model' B' Hrt' HST Hview.
    apply (IH A (mkst (regupd regs 10 (Z_to_bv 64 addr)) (Z_to_bv 64 (bv_unsigned pc + 4)) M' rom) model').
    + rewrite restrict_mkst, Hview, <- EM. reflexivity.
    + exact B'.
    + exact (bmodel_rt_trans _ _ _ Hrt Hrt').
    + exact (bhist_step_same _ _ _ _ _ _ _ _ _ _ (AMmapFixed addr len) HH HST).
  - destruct (restrict_eq_mkst _ _ _ _ _ _ Es) as [Ems EM]. rewrite Ems. rewrite Ems in B, HH. cbn [ms_mem mkst] in B, HH.
    subst pc'. apply (bridge_null log A regs pc (ms_mem ms) rom model len K); try assumption.
    intros r A' M' model' HGR B' Hrt' HST Hview.
    apply (IH r ltac:(rewrite EM; exact HGR) A' (mkst (regupd regs 10 (Z_to_bv 64 r)) (Z_to_bv 64 (bv_unsigned pc + 4)) M' rom) model').
    + rewrite restrict_mkst, Hview, <- EM. reflexivity.
    + exact B'.
    + exact (bmodel_rt_trans _ _ _ Hrt Hrt').
    + exact (bhist_step_null _ _ _ _ _ _ _ _ _ _ _ len r HH HST).
  - destruct (restrict_eq_mkst _ _ _ _ _ _ Es) as [Ems EM]. rewrite Ems. rewrite Ems in B, HH. cbn [ms_mem mkst] in B, HH.
    subst pc'. apply (bridge_fixed_nr log A regs pc (ms_mem ms) rom model addr len K); try assumption.
    intros M' model' B' Hrt' HST Hview.
    apply (IH A (mkst (regupd regs 10 (Z_to_bv 64 addr)) (Z_to_bv 64 (bv_unsigned pc + 4)) M' rom) model').
    + rewrite restrict_mkst, Hview, <- EM. reflexivity.
    + exact B'.
    + exact (bmodel_rt_trans _ _ _ Hrt Hrt').
    + exact (bhist_step_same _ _ _ _ _ _ _ _ _ _ (AMmapFixedNR addr len) HH HST).
  - destruct (restrict_eq_mkst _ _ _ _ _ _ Es) as [Ems EM]. rewrite Ems. rewrite Ems in B, HH. cbn [ms_mem mkst] in B, HH.
    subst pc'. apply (bridge_munmap log A regs pc (ms_mem ms) rom model addr len K); try assumption.
    intros M' model' B' Hrt' HST Hview.
    apply (IH A (mkst (regupd regs 10 (Z_to_bv 64 0)) (Z_to_bv 64 (bv_unsigned pc + 4)) M' rom) model').
    + rewrite restrict_mkst, Hview, <- EM. reflexivity.
    + exact B'.
    + exact (bmodel_rt_trans _ _ _ Hrt Hrt').
    + exact (bhist_step_same _ _ _ _ _ _ _ _ _ _ (AMunmap addr len) HH HST).
  - destruct (restrict_eq_mkst _ _ _ _ _ _ Es) as [Ems EM]. rewrite Ems. rewrite Ems in B, HH. cbn [ms_mem mkst] in B, HH.
    subst pc'. apply (bridge_madvise log A regs pc (ms_mem ms) rom model addr len K); try assumption.
    intros M' model' B' Hrt' HST Hview.
    apply (IH A (mkst (regupd regs 10 (Z_to_bv 64 0)) (Z_to_bv 64 (bv_unsigned pc + 4)) M' rom) model').
    + rewrite restrict_mkst, Hview, <- EM. reflexivity.
    + exact B'.
    + exact (bmodel_rt_trans _ _ _ Hrt Hrt').
    + exact (bhist_step_same _ _ _ _ _ _ _ _ _ _ (AMadvise addr len) HH HST).
Qed.

(* [comment removed for export] *)
Theorem aruns_srealizes : forall (Q : list aev -> machine_state -> Prop) K model0,
  (forall log A ms model, BInv log A (ms_mem ms) model -> bmodel_rt model0 model ->
     Q log (restrict (bhid A model) ms) -> srealizes segs scfg (mkCfg ms model) K) ->
  forall log s, aruns segs EVOK GR Q log s ->
  forall A ms model, restrict (bhid A model) ms = s -> BInv log A (ms_mem ms) model -> bmodel_rt model0 model ->
  srealizes segs scfg (mkCfg ms model) K.
Proof.
  intros Q K model0 HQ log s R A ms model Es B Hrt.
  apply (aruns_srealizes_h Q K model0 A (ms_mem ms) model log (fun log' A' ms' model' B' Hrt' _ Hq => HQ log' A' ms' model' B' Hrt' Hq)
           log s R A ms model Es B Hrt). apply bhist_refl.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma binv_ext : forall log A M m1 m2,
  BInv log A M m1 -> m_vmmaps m2 = m_vmmaps m1 -> m_vm_lazy m2 = m_vm_lazy m1 ->
  m_halted m2 = None -> MInv A m2 -> BInv log A M m2.
Proof.
  intros log A M m1 m2 B Hvm Hlz Hh Hminv.
  assert (Heu : eager_used m2 = eager_used m1) by (apply eager_used_ext; assumption).
  assert (EH : bhid A m2 = bhid A m1) by (unfold bhid; rewrite Hlz; reflexivity).
  destruct B. constructor; rewrite ?Hvm, ?Hlz, ?Heu, ?EH; try assumption.
  destruct bi_wf0 as (W1 & W2 & W3 & W4). unfold BA.model_ivs_wf. rewrite Hvm, Hlz. repeat split; assumption.
Qed.

(* [comment removed for export] *)
Definition BINV (log : list aev) (A : list (Z * Z)) (M : word -> option byte) (h : VmMaps) (lz : list (word * word)) : Prop :=
  A_wf A /\ live_ok (art_live log)
  /\ forall model, m_vmmaps model = h -> m_vm_lazy model = lz -> m_halted model = None -> MInv A model -> BInv log A M model.

Lemma BINV_elim : forall log A M model,
  BINV log A M (m_vmmaps model) (m_vm_lazy model) -> m_halted model = None -> MInv A model -> BInv log A M model.
Proof. intros log A M model (_ & _ & H) Hh Hm. exact (H model eq_refl eq_refl Hh Hm). Qed.

Lemma BINV_intro : forall log A M model,
  BInv log A M model -> BINV log A M (m_vmmaps model) (m_vm_lazy model).
Proof.
  intros log A M model B. split; [exact (bi_awf _ _ _ _ B)|]. split; [exact (bi_live _ _ _ _ B)|].
  intros m2 Hvm Hlz Hh Hm. exact (binv_ext log A M model m2 B Hvm Hlz Hh Hm).
Qed.

Lemma BINV_awf : forall log A M h lz, BINV log A M h lz -> A_wf A.
Proof. intros log A M h lz (H & _). exact H. Qed.
Lemma BINV_live : forall log A M h lz, BINV log A M h lz -> live_ok (art_live log).
Proof. intros log A M h lz (_ & H & _). exact H. Qed.

End Bridge.
