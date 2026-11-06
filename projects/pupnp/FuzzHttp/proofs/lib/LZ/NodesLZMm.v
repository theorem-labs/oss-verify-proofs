(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Cfg.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import PropExec MState Mem Exec ITree RelSpec RelSpecX Nodes Decode.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.ASN Require Import AsanAcct BackingAlgebra.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import Realize SafeReach Bridge.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.LZ Require Import ITreeLZ BridgeLZ NodesLZ LZPages NodesLZSound RelSpecMm2.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Lemma strip_vm_forget_vmmaps : forall lo hi h mo,
  strip_vm (vm_forget_range lo hi (with_vmmaps h mo)) = with_vmmaps h (strip_vm mo).
Proof. intros lo hi h [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.

Lemma strip_vm_wvb : forall l X mo, strip_vm (with_vm_backing l X mo) = strip_vm mo.
Proof. intros l X [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.

Lemma strip_vm_vm_add_lazy : forall a n mo, strip_vm (vm_add_lazy a n mo) = strip_vm mo.
Proof. intros a n [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.

Lemma minv_strip_vmmaps : forall h mo,
  vm_init_sp h = vm_init_sp (m_vmmaps mo) -> m_halted mo = None ->
  minv (strip_vm mo) -> minv (with_vmmaps h (strip_vm mo)).
Proof.
  intros h mo Hsp Hh Hm.
  apply (mm_frame_minv (strip_vm mo)); [| rewrite m_halted_strip_vm; exact Hh| exact Hm].
  apply mm_frame_with_vmmaps. rewrite m_vmmaps_strip_vm. exact Hsp.
Qed.

Lemma nret_mem_zu : forall ms r zs us x,
  ms_mem (nret ms (mkEffectU r [] zs us [] [])) x
  = if zeros_cover zs x then Some (Z_to_bv 8 0) else if zeros_cover us x then None else ms_mem ms x.
Proof.
  intros ms r zs us x. unfold nret, advance_past_svc, apply_effect. cbn -[set_reg apply_zeros apply_unmaps].
  rewrite ms_mem_set_reg, apply_zeros_pw, apply_unmaps_pw. reflexivity.
Qed.

Lemma zeros_cover_1 : forall (a n : word) x,
  zeros_cover [(a, n)] x = in_rangeb (bv_unsigned a) (bv_unsigned a + bv_unsigned n) x.
Proof. intros a n x. unfold zeros_cover, in_rangeb. cbn. rewrite orb_false_r. reflexivity. Qed.

Lemma hzero_unhide_zu : forall H ms r (a n : word) zs us,
  (zs = [(a, n)] /\ us = [] \/ zs = [] /\ us = [(a, n)]) ->
  hzero H ms -> hzero (unhide_range (bv_unsigned a) (bv_unsigned a + bv_unsigned n) H) (nret ms (mkEffectU r [] zs us [] [])).
Proof.
  intros H ms r a n zs us Hzu HZ x Hx. unfold unhide_range in Hx. apply andb_prop in Hx as [Hx Hout].
  apply negb_true_iff in Hout.
  rewrite nret_mem_zu. destruct Hzu as [[-> ->]|[-> ->]]; rewrite zeros_cover_1, Hout; cbn [zeros_cover existsb]; exact (HZ x Hx).
Qed.

Lemma cov_unhide_zu : forall H (a n : word) zs us x,
  (zs = [(a, n)] /\ us = [] \/ zs = [] /\ us = [(a, n)]) ->
  H x = true -> unhide_range (bv_unsigned a) (bv_unsigned a + bv_unsigned n) H x = false ->
  zb x = true \/ zeros_cover zs x = true \/ zeros_cover us x = true.
Proof.
  intros H a n zs us x Hzu Hx Hu. unfold unhide_range in Hu. rewrite Hx in Hu. cbn [andb] in Hu. apply negb_false_iff in Hu.
  right. destruct Hzu as [[-> ->]|[-> ->]]; [left| right]; rewrite zeros_cover_1; exact Hu.
Qed.

Lemma cov_unhide_win : forall H (a n : word) wlo whi x,
  H x = true -> unhide_zb wlo whi (unhide_range (bv_unsigned a) (bv_unsigned a + bv_unsigned n) H) x = false ->
  zb x = true \/ zeros_cover [(a, n)] x = true \/ zeros_cover [] x = true.
Proof.
  intros H a n wlo whi x Hx Hu. unfold unhide_zb, unhide_range in Hu. rewrite Hx in Hu. cbn [andb] in Hu.
  destruct (in_rangeb (bv_unsigned a) (bv_unsigned a + bv_unsigned n) x) eqn:IR.
  - right; left. rewrite zeros_cover_1. exact IR.
  - cbn [negb andb] in Hu. apply negb_false_iff in Hu. apply andb_prop in Hu as [_ Z]. left. exact Z.
Qed.

Lemma map_has_In : forall l (a n : word), map_has l a n = true -> In (a, n) l.
Proof.
  intros l a n Hm. unfold map_has in Hm. apply existsb_exists in Hm as ([b s] & Hin & E). cbn [fst snd] in E.
  apply andb_prop in E as [E1 E2]. apply bv_eqb_eq in E1. apply bv_eqb_eq in E2. subst. exact Hin.
Qed.

Lemma fixed_flag_facts : forall flags, flags = MAPF_FIXED \/ flags = MAPF_FIXED_NR ->
  let FL := Z_to_bv 64 flags in let PR := Z_to_bv 64 PROT_RW in let z := Z_to_bv 64 0 in
  mmap_anon_b FL = true /\ mmap_modeled_b PR FL z = false /\ mmap_noaccess_b PR FL z = false
  /\ mmap_fixed_noaccess_b PR FL z = false /\ mmap_fixed_rw_b PR FL z = true
  /\ mmap_noreserve_b FL = (flags =? MAPF_FIXED_NR).
Proof. intros flags [-> | ->]; cbv zeta; vm_compute; repeat split; reflexivity. Qed.

Lemma m_halted_with_mmap_replacement : forall flags a n m,
  m_halted (with_mmap_replacement flags a n m) = m_halted m.
Proof.
  intros flags a n m. unfold with_mmap_replacement, with_mmap_backing, vm_add_lazy, vm_forget_range.
  destruct (mmap_noreserve_b flags); rewrite ?m_halted_wvb; reflexivity.
Qed.

Lemma m_halted_with_mmap_backing : forall flags a n m,
  m_halted (with_mmap_backing flags a n m) = m_halted m.
Proof.
  intros flags a n m. unfold with_mmap_backing, vm_add_lazy.
  destruct (mmap_noreserve_b flags); rewrite ?m_halted_wvb; reflexivity.
Qed.

Lemma m_halted_with_mmap_destroyed : forall a n h m,
  m_halted (with_mmap_destroyed a n h m) = m_halted m.
Proof. intros a n h m. destruct m; reflexivity. Qed.

Lemma strip_vm_with_mmap_replacement : forall flags a n h m,
  strip_vm (with_mmap_replacement flags a n (with_vmmaps h m)) = with_vmmaps h (strip_vm m).
Proof.
  intros flags a n h m. unfold with_mmap_replacement, with_mmap_backing.
  destruct (mmap_noreserve_b flags); rewrite ?strip_vm_vm_add_lazy, strip_vm_forget_vmmaps; reflexivity.
Qed.

Lemma perase_with_mmap_replacement : forall P flags a n h mo,
  perase (cut_pages (bv_unsigned a) (bv_unsigned a + bv_unsigned n) P) (with_mmap_replacement flags a n (with_vmmaps h mo))
  = with_mmap_replacement flags a n (with_vmmaps h (perase P mo)).
Proof.
  intros P flags a n h mo. unfold with_mmap_replacement, with_mmap_backing, cut_pages.
  destruct (mmap_noreserve_b flags); rewrite ?perase_vm_add_lazy, perase_vm_forget_range, perase_with_vmmaps; reflexivity.
Qed.

Lemma map_contains_covers : forall l (lo n : word) x,
  map_contains l lo n = true -> bv_unsigned lo <= x < bv_unsigned lo + bv_unsigned n -> covered l x = true.
Proof.
  intros l lo n x Hm Hx. unfold map_contains in Hm. apply existsb_exists in Hm as ([b s] & Hin & E). cbn [fst snd] in E.
  apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
  unfold covered. apply existsb_exists. exists (b, s). split; [exact Hin|]. unfold in_iv, in_rng, B, S. cbn [fst snd].
  apply andb_true_intro. split; [apply Z.leb_le| apply Z.ltb_lt]; lia.
Qed.

Lemma null_flag_facts :
  let PR := Z_to_bv 64 PROT_RW in let z := Z_to_bv 64 0 in
  (mmap_anon_b (Z_to_bv 64 MAPF_ANON_PRIVATE) = true /\ mmap_modeled_b PR (Z_to_bv 64 MAPF_ANON_PRIVATE) z = true
   /\ mmap_noreserve_b (Z_to_bv 64 MAPF_ANON_PRIVATE) = false)
  /\ (mmap_anon_b (Z_to_bv 64 MAPF_NR) = true /\ mmap_modeled_b PR (Z_to_bv 64 MAPF_NR) z = true
   /\ mmap_noreserve_b (Z_to_bv 64 MAPF_NR) = true).
Proof. cbv zeta. vm_compute. repeat split; reflexivity. Qed.

Lemma hzero_subset : forall (H1 H2 : word -> bool) ms,
  (forall a, H2 a = true -> H1 a = true) -> hzero H1 ms -> hzero H2 ms.
Proof. intros H1 H2 ms Hs HZ a Ha. exact (HZ a (Hs a Ha)). Qed.

Lemma perase_app_with_vmmaps : forall W P G mo,
  perase (W ++ P) (with_vmmaps G mo) = with_vm_backing (m_vm_lazy (perase P mo)) (W ++ m_vm_materialized (perase P mo)) (with_vmmaps G (perase P mo)).
Proof. intros W P G [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.

Lemma perase_app_vm_add_lazy : forall W P a n G mo,
  perase (W ++ P) (vm_add_lazy a n (with_vmmaps G mo))
  = with_vm_backing (lazy_interior a n ++ m_vm_lazy (perase P mo)) (W ++ m_vm_materialized (perase P mo)) (with_vmmaps G (perase P mo)).
Proof. intros W P a n G [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.

Lemma shw_bounds : forall off a nZ,
  0 <= off -> 0 <= a -> 0 <= nZ ->
  shw_lo off a mod page_size = 0 /\ shw_hi off a nZ mod page_size = 0 /\ 0 <= shw_lo off a
  /\ shw_lo off a <= shw_hi off a nZ /\ shw_hi off a nZ - shw_lo off a <= nZ / 8 + 2 * page_size
  /\ shw_hi off a nZ <= (a + nZ) / 8 + off + page_size.
Proof.
  intros off a nZ Hoff Ha Hn. unfold shw_lo, shw_hi, page_size.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  repeat split; try (rewrite Z.mod_mul by lia; reflexivity); nia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section PerKindMm.
Variable segs : list Segment.
Variable H : word -> bool.
Variable P : list word.
Variable msF : machine_state.
Variable mo : Model.
Hypothesis HF : lzframe segs minvL H P mo.
Hypothesis HZ : hzero H msF.

Let Hh : m_halted mo = None := lf_halt _ _ _ _ _ HF.
Let HO : H_off_segments segs H := lf_off _ _ _ _ _ HF.
Let HI : MInv (ivl P) mo := lf_MInv _ _ _ _ _ HF.
Let HC : lazy_cover H (m_vm_lazy mo) (ivl P) := lf_cover _ _ _ _ _ HF.
Let HA : P_aligned P := lf_al _ _ _ _ _ HF.

#[using="segs H P HF"] Lemma HMLm : minvL mo.
Proof. apply (minvL_perase P). exact (lf_minv _ _ _ _ _ HF). Qed.

#[using="Type"] Lemma grant_lazy_free : forall (a n : word) (w : word),
  lazy_in_maps mo -> region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) a n = true ->
  bv_unsigned a mod page_size = 0 -> bv_unsigned n mod page_size = 0 ->
  bv_unsigned a <= bv_unsigned w < bv_unsigned a + bv_unsigned n ->
  page_in_ranges (page_base w) (m_vm_lazy mo) = false.
Proof.
  intros a n w HLm Hrf Hal Hnl Hw. pose proof (page_base_facts w) as (B1 & B2 & B3).
  destruct (page_in_ranges (page_base w) (m_vm_lazy mo)) eqn:E; [| reflexivity]. exfalso.
  assert (Hhi : (bv_unsigned a + bv_unsigned n) mod page_size = 0) by (rewrite <- Zplus_mod_idemp_l, Hal, Z.add_0_l; exact Hnl).
  destruct (page_of_byte_in_aligned w (bv_unsigned a) (bv_unsigned a + bv_unsigned n) Hal Hhi Hw) as [Q1 Q2].
  pose proof (page_in_lazy_meets_maps mo (page_base w) (bv_unsigned (page_base w)) HLm E ltac:(unfold page_size; lia)) as C.
  unfold covered in C. apply existsb_exists in C as ([e sz] & He & Hx). unfold in_iv, in_rng, B, S in Hx. cbn [fst snd] in Hx.
  apply andb_prop in Hx as [X1 X2]. apply Z.leb_le in X1. apply Z.ltb_lt in X2.
  assert (Hrf' : region_free (vm_maps (m_vmmaps mo)) a n = true).
  { eapply Decode.region_free_incl; [| exact Hrf]. intros e0 He0. apply in_app_iff. right. exact He0. }
  pose proof (Decode.region_free_In _ a n e sz Hrf' He) as D. unfold page_size in *. lia.
Qed.

#[using="Type"] Lemma lazy_cover_unhide_free : forall lo hi (Hd : word -> bool) lazy Pg,
  lazy_cover Hd lazy (ivl Pg) ->
  (forall w : word, lo <= bv_unsigned w < hi -> page_in_ranges (page_base w) lazy = false) ->
  lazy_cover (unhide_range lo hi Hd) lazy (ivl Pg).
Proof.
  intros lo hi Hd lazy Pg HCv Hfree w Hpl Hw. unfold unhide_range in Hw. apply andb_false_iff in Hw as [Hw|Hw].
  - exact (HCv w Hpl Hw).
  - apply negb_false_iff in Hw. unfold in_rangeb in Hw. apply andb_prop in Hw as [W1 W2]. apply Z.leb_le in W1. apply Z.ltb_lt in W2.
    rewrite (Hfree w ltac:(lia)) in Hpl. discriminate.
Qed.

#[using="HF HZ Hh HO HI HC HA"] Lemma munmap_factsL : forall addr len,
  at_node segs (NMunmap addr len) (restrict H msF) -> nsafeL (LNode (NMunmap addr len)) (perase P mo) ->
  factsL segs (LNode (NMunmap addr len)) H P msF mo (Z_to_bv 64 215).
Proof.
  intros addr len HatR Hsafe. pose proof (at_node_unrestrict segs H HO _ _ HatR) as Hat.
  destruct Hat as (Hsvc & Ha0 & Ha1 & Hal & Hlen & Hnw). cbn [nsafeL nsafe] in Hsafe. destruct Hsafe as [Hhas _].
  rewrite m_vmmaps_perase in Hhas.
  pose proof HMLm as (HM0 & HL & HW & HS). pose proof HW as (Wm & Wn & Wl & Wsp).
  set (A := Z_to_bv 64 addr) in *. set (n := Z_to_bv 64 (page_round_up_Z (bv_unsigned (Z_to_bv 64 len)))) in *.
  set (h := m_vmmaps mo) in *.
  set (lo := bv_unsigned A). set (hi := lo + bv_unsigned n).
  assert (Hn : bv_unsigned n = lenZ len).
  { subst n. unfold lenZ. apply u64_lit. pose proof (lenZ_nonneg len). unfold lenZ in *. pose proof (u64_range A). lia. }
  assert (Hnpos : 0 < bv_unsigned n).
  { rewrite Hn. unfold lenZ, page_round_up_Z. pose proof (u64_range (Z_to_bv 64 len)) as R.
    assert (bv_unsigned (Z_to_bv 64 len) <> 0).
    { intros E. unfold w_is0 in Hlen. assert (EE : Z_to_bv 64 len = Z_to_bv 64 0) by (apply bv_eq; rewrite E; reflexivity).
      rewrite EE, bv_eqb_refl in Hlen. discriminate. }
    unfold page_size. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). nia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  assert (Hlo : lo mod 4096 = 0) by exact Hal.
  assert (Hhi : hi mod 4096 = 0).
  { subst hi. rewrite Hn. rewrite <- Zplus_mod_idemp_l, Hlo. apply lenZ_aligned. }
  pose proof (map_has_In _ _ _ Hhas) as Hin.
  set (h' := mkVmMapsFull (vm_reserved h) (map_remove (vm_maps h) A)
               (maps_subtract (vm_noaccess h) lo hi)
               (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)).
  set (mo1 := with_mmap_destroyed A n h' mo).
  assert (OUT : forall o, syscall_spec (sys_input segs msF (Z_to_bv 64 215)) mo o <->
            o = Ok (mkEffectU (Z_to_bv 64 0) [] [] [(A, n)] [] []) mo1 []).
  { intros o. rewrite (syscall_spec_215 _ _ _ (sysno_of segs msF _ 215 ltac:(lia) eq_refl)).
    rewrite in_a0_si, in_a1_si, Ha0, Ha1. apply (munmap_exact_outcome _ _ _ _ _ Hal Hlen Hnw Hhas). }
  set (P' := cut_pages (addrZ addr) (addrZ addr + lenZ len) P).
  assert (EP : allowL (LNode (NMunmap addr len)) (mkEffectU (Z_to_bv 64 0) [] [] [(A, n)] [] []) P = P') by reflexivity.
  assert (Elo : addrZ addr = lo) by reflexivity.
  assert (Ehi : addrZ addr + lenZ len = hi) by (subst hi; rewrite Hn; reflexivity).
  assert (Hlh : lo <= hi) by (unfold hi; lia).

  assert (Eper : perase P' mo1 = with_mmap_destroyed A n
            (mkVmMapsFull (vm_reserved (m_vmmaps (perase P mo))) (map_remove (vm_maps (m_vmmaps (perase P mo))) A)
               (maps_subtract (vm_noaccess (m_vmmaps (perase P mo))) (bv_unsigned A) (bv_unsigned A + bv_unsigned n))
               (vm_start_brk (m_vmmaps (perase P mo))) (vm_brk (m_vmmaps (perase P mo))) (vm_limit (m_vmmaps (perase P mo)))
               (vm_mmap_base (m_vmmaps (perase P mo))) (vm_init_sp (m_vmmaps (perase P mo)))) (perase P mo)).
  { rewrite m_vmmaps_perase. unfold with_mmap_destroyed. rewrite <- perase_with_vmmaps, <- perase_vm_forget_range.
    subst P' mo1. unfold cut_pages. rewrite Ehi. reflexivity. }
  split.
  - exact Hsvc.
  - intros eff mo' evs Hs. apply OUT in Hs. apply Ok_inj in Hs as (-> & -> & ->). rewrite EP.
    cbn [hideL]. rewrite Ehi, Elo.
    split. { cbn [nstepL nstep]. split; [reflexivity|]. split; [reflexivity|]. exact Eper. }
    split. { subst mo1. unfold with_mmap_destroyed, vm_forget_range. rewrite m_halted_wvb, m_halted_with_vmmaps. exact Hh. }
    split.
    {
      pose proof HI as [N1 N2 N3 N4 N5]. subst mo1 P'. unfold with_mmap_destroyed. constructor; model_proj.
      + apply NoDup_filter. exact N1.
      + intros p Hp. apply filter_In in Hp as [Hp _]. exact (N2 p Hp).
      + intros p Hp. apply filter_In in Hp as [Hp Hout]. pose proof (N2 p Hp) as Hpal.
        apply (proj2 (page_allowedb_ivl _ p Hpal (cut_pages_aligned _ _ _ HA))). apply cut_pages_in.
        split; [exact (proj1 (page_allowedb_ivl _ p Hpal HA) (N3 p Hp))|].
        unfold page_outside_range in Hout. apply negb_true_iff in Hout. apply andb_false_iff in Hout as [Hout|Hout];
          [left; apply Z.leb_gt in Hout| right; apply Z.ltb_ge in Hout]; rewrite Ehi, Elo in *; lia.
      + intros p Hp. apply filter_In in Hp as [Hp Hout]. pose proof (N2 p Hp) as Hpal.
        unfold page_outside_range in Hout. apply negb_true_iff in Hout.
        rewrite page_in_ranges_subtract_out; [exact (N4 p Hp)| exact Wl| lia|].
        apply andb_false_iff in Hout as [Hout|Hout]; [apply Z.leb_gt in Hout| apply Z.ltb_ge in Hout].
        * left. destruct (aligned_in_or_out (bv_unsigned p) lo hi Hpal Hlo Hhi); unfold page_size; lia.
        * right. exact Hout.
      + cbn [vm_limit]. rewrite A_bytes_ivl in N5 |- *.
        pose proof (eager_used_munmap_le mo A n HW HS Hin) as LE. cbv zeta in LE.
        fold h in LE. fold lo in LE. fold hi in LE. fold h' in LE. unfold lo, hi in LE. unfold lo in LE.
        change (vm_limit h') with (vm_limit (m_vmmaps mo)).
        pose proof (cut_pages_length (addrZ addr) (addrZ addr + lenZ len) P) as CL.
        unfold page_size in *. nia. }
    split.
    {
      intros w Hpl Hw. subst mo1. unfold with_mmap_destroyed in Hpl. revert Hpl. model_proj. intros Hpl.
      pose proof (page_base_facts w) as (B1 & B2 & B3).
      assert (Hout : bv_unsigned (page_base w) + page_size <= lo \/ hi <= bv_unsigned (page_base w)).
      { destruct (aligned_in_or_out (bv_unsigned (page_base w)) lo hi B3 Hlo Hhi) as [Hinr|Houtr]; [| unfold page_size; lia].
        exfalso. fold lo in Hpl. fold hi in Hpl. rewrite (page_in_ranges_subtract_in (page_base w) _ lo hi Wl ltac:(lia)) in Hpl. discriminate. }
      fold lo in Hpl. fold hi in Hpl.
      rewrite (page_in_ranges_subtract_out _ _ _ _ Wl Hlh Hout) in Hpl.
      unfold unhide_range in Hw. apply andb_false_iff in Hw as [Hw|Hw].
      * pose proof (HC w Hpl Hw) as Hal0. apply (proj2 (page_allowedb_ivl _ _ B3 (cut_pages_aligned _ _ _ HA))).
        apply cut_pages_in. split; [exact (proj1 (page_allowedb_ivl _ _ B3 HA) Hal0)|]. rewrite Ehi, Elo. unfold page_size in *. lia.
      * exfalso. apply negb_false_iff in Hw. unfold in_rangeb in Hw. apply andb_prop in Hw as [W1 W2].
        apply Z.leb_le in W1. apply Z.ltb_lt in W2.
        destruct (page_of_byte_in_aligned w lo hi Hlo Hhi ltac:(lia)). unfold page_size in *. lia. }
    split. { apply cut_pages_aligned. exact HA. }
    split.
    {
      apply minvL_perase. subst mo1. unfold with_mmap_destroyed. split; [| split; [| split]].
      + rewrite strip_vm_forget_vmmaps. apply minv_strip_vmmaps; [reflexivity| exact Hh| exact HM0].
      +
        intros r x Hr Hx. revert Hr. model_proj. cbn [vm_maps]. intros Hr.
        fold lo in Hr. fold hi in Hr.
        destruct (maps_subtract_sem (m_vm_lazy mo) lo hi Wl Hlh) as (_ & _ & Cv).
        assert (Cx : covered (maps_subtract (m_vm_lazy mo) lo hi) x = true).
        { unfold covered. apply existsb_exists. exists r. split; [exact Hr|]. unfold in_iv, in_rng, B, S.
          apply andb_true_intro. split; [apply Z.leb_le| apply Z.ltb_lt]; lia. }
        rewrite Cv in Cx. apply andb_prop in Cx as [C1 C2]. apply negb_true_iff in C2.
        unfold covered in C1. apply existsb_exists in C1 as (r0 & Hr0 & Hx0). unfold in_iv, in_rng, B, S in Hx0.
        apply andb_prop in Hx0 as [X1 X2]. apply Z.leb_le in X1. apply Z.ltb_lt in X2.
        pose proof (HL r0 x Hr0 ltac:(lia)) as Cm. unfold covered in Cm. apply existsb_exists in Cm as (e & He & Hxe).
        unfold in_iv, in_rng, B, S in Hxe. apply andb_prop in Hxe as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
        unfold covered. apply existsb_exists. exists e. split.
        * unfold map_remove. apply filter_In. split; [exact He|]. apply negb_true_iff.
          destruct (bv_eqb (fst e) A) eqn:EA; [| reflexivity]. exfalso. apply bv_eqb_eq in EA.
          destruct (seps_in_disjoint _ _ _ HS He Hin) as [Ee|D].
          -- subst e. cbn [fst snd] in E1, E2. unfold in_rng in C2. apply andb_false_iff in C2 as [C2|C2];
               [apply Z.leb_gt in C2| apply Z.ltb_ge in C2]; unfold lo, hi in *; lia.
          -- unfold iv_disjoint in D. rewrite EA in D. cbn [fst snd] in D. destruct e as [ea es]. cbn [fst snd] in *. subst ea. lia.
        * unfold in_iv, in_rng, B, S. apply andb_true_intro. split; [apply Z.leb_le| apply Z.ltb_lt]; lia.
      + apply model_ivs_wf_vm_forget_range; [pose proof (u64_range n); lia|]. apply model_ivs_wf_with_vmmaps; [exact HW| | | reflexivity]; cbn [vm_maps vm_noaccess].
        * unfold map_remove. apply ivs_wf_filter. exact Wm.
        * apply maps_subtract_wf; [exact Wn| pose proof (u64_range n); lia].
      + model_proj. cbn [vm_maps]. unfold map_remove. apply seps_filter. exact HS. }
    split. { cbn. apply AsanAcct.ranges_avoid_nil. }
    split. { reflexivity. }
    split. { unfold lo, hi. apply hzero_unhide_zu; [right; split; reflexivity| exact HZ]. }
    split. { apply hide_ok_mono. intros a Ha. unfold unhide_range in Ha. apply andb_prop in Ha as [Ha _]. exact Ha. }
    intros x0 Hx0 Hu0. unfold lo, hi in Hu0. cbn [eff_zeros eff_unmaps]. eapply cov_unhide_zu; [right; split; reflexivity| exact Hx0| exact Hu0].
  - intros Hs. apply OUT in Hs. discriminate.
  - intros eff moE' evs Hst. cbn [nstepL nstep] in Hst. destruct Hst as (-> & Hs & ->).
    eexists (mkEffectU (Z_to_bv 64 0) [] [] [(A, n)] [] []), mo1. split; [rewrite Hs; reflexivity|]. split; [apply OUT; reflexivity|].
    change (allowL (LNode (NMunmap addr len)) eff P) with P'. exact Eper.
  - eexists (mkEffectU (Z_to_bv 64 0) [] [] [(A, n)] [] []), _, []. cbn [nstepL nstep]. repeat split; reflexivity.
Qed.

#[using="HF HZ Hh HI HC HA"] Lemma mmap_fixed_factsL : forall addr len flags,
  at_nodeL segs (LMmapFixed addr len flags) (restrict H msF) -> nsafeL (LMmapFixed addr len flags) (perase P mo) ->
  factsL_ns segs (LMmapFixed addr len flags) H P msF mo (Z_to_bv 64 222).
Proof.
  intros addr len flags HatR Hsafe.
  destruct HatR as ((Hsvc & Ha0 & Ha1 & Ha2 & Ha3 & Ha4 & Ha5 & Hlen) & Hflags & Hal & Hpos & Hub).
  unfold areg in Ha0, Ha1, Ha2, Ha3, Ha4, Ha5. cbn [AsanAcct.restrict ms_regs ms_svc_pending] in Hsvc, Ha0, Ha1, Ha2, Ha3, Ha4, Ha5.
  fold (areg msF 10) in Ha0. fold (areg msF 11) in Ha1. fold (areg msF 12) in Ha2. fold (areg msF 13) in Ha3.
  fold (areg msF 14) in Ha4. fold (areg msF 15) in Ha5.
  cbn [nsafeL] in Hsafe. rewrite m_vmmaps_perase in Hsafe. destruct Hsafe as (Hce & Hrf & Hmc & Hbud).
  pose proof HMLm as (HM0 & HL & HW & HS). pose proof HW as (Wm & Wn & Wl & Wsp).
  destruct (fixed_flag_facts flags Hflags) as (Fanon & Fmod & Fna & Ffna & Ffrw & Fnr).
  set (FL := Z_to_bv 64 flags) in *. set (A := Z_to_bv 64 addr) in *. set (n := lenW len) in *.
  set (h := m_vmmaps mo) in *.
  pose proof (lenZ_nonneg len) as Hn0.
  assert (EA : bv_unsigned A = addr) by (subst A; apply u64_lit; lia).
  assert (Hn : bv_unsigned n = lenZ len) by (subst n; unfold lenW; apply u64_lit; lia).
  assert (Hhi : (addr + lenZ len) mod page_size = 0) by (rewrite <- Zplus_mod_idemp_l, Hal, Z.add_0_l; apply lenZ_aligned).
  set (mo1 := with_mmap_replacement FL A n (with_vmmaps (mmap_fixed_rw_next h A n) mo)).
  set (P' := (if mmap_noreserve_b FL then pages_of addr (addr + lenZ len) else []) ++ cut_pages addr (addr + lenZ len) P).
  assert (EP : forall eff, allowL (LMmapFixed addr len flags) eff P = P').
  { intros eff. cbn [allowL]. unfold addrZ. fold A. rewrite EA. reflexivity. }
  assert (EH : forall eff, hideL (LMmapFixed addr len flags) eff H = unhide_range addr (addr + lenZ len) H).
  { intros eff. cbn [hideL]. unfold addrZ. fold A. rewrite EA. reflexivity. }

  assert (Eper : perase P' mo1 = lmfixed_post (perase P mo) addr len flags).
  { unfold lmfixed_post. rewrite m_vmmaps_perase. fold FL A n h. unfold lmfixed_next. rewrite Hmc.
    rewrite <- perase_with_mmap_replacement. rewrite EA, Hn.
    subst mo1 P'. rewrite (perase_app _ (cut_pages addr (addr + lenZ len) P)). rewrite m_vm_materialized_perase.
    unfold addrZ. fold A. rewrite EA. reflexivity. }

  pose proof HI as [N1 N2 N3 N4 N5].
  assert (Emat : m_vm_materialized mo1 = List.filter (page_outside_range addr (addr + lenZ len)) (m_vm_materialized mo)).
  { subst mo1. unfold with_mmap_replacement, with_mmap_backing. rewrite EA, Hn.
    destruct (mmap_noreserve_b FL); unfold vm_add_lazy; model_proj; reflexivity. }
  assert (Elazy : m_vm_lazy mo1 = (if mmap_noreserve_b FL then lazy_interior A n else []) ++ maps_subtract (m_vm_lazy mo) addr (addr + lenZ len)).
  { subst mo1. unfold with_mmap_replacement, with_mmap_backing. rewrite EA, Hn.
    destruct (mmap_noreserve_b FL); unfold vm_add_lazy; model_proj; reflexivity. }
  assert (Emaps : m_vmmaps mo1 = mmap_fixed_rw_next h A n).
  { subst mo1. unfold with_mmap_replacement, with_mmap_backing. destruct (mmap_noreserve_b FL); unfold vm_add_lazy; model_proj; reflexivity. }
  assert (HP'al : P_aligned P').
  { subst P'. apply P_aligned_app; [| apply cut_pages_aligned; exact HA].
    destruct (mmap_noreserve_b FL); [apply pages_of_aligned; try exact Hal; lia| constructor]. }
  assert (M1 : List.NoDup (m_vm_materialized mo1)) by (rewrite Emat; apply NoDup_filter; exact N1).
  assert (M2 : forall p, In p (m_vm_materialized mo1) -> bv_unsigned p mod page_size = 0).
  { rewrite Emat. intros p Hp. apply filter_In in Hp as [Hp _]. exact (N2 p Hp). }
  assert (M3 : forall p, In p (m_vm_materialized mo1) -> In p P').
  { rewrite Emat. intros p Hp. apply filter_In in Hp as [Hp Hout]. subst P'. apply in_app_iff. right.
    apply cut_pages_in. split; [exact (proj1 (page_allowedb_ivl _ p (N2 p Hp) HA) (N3 p Hp))|].
    unfold page_outside_range in Hout. apply negb_true_iff in Hout. apply andb_false_iff in Hout as [Hout|Hout];
      [left; apply Z.leb_gt in Hout| right; apply Z.ltb_ge in Hout]; lia. }

  assert (Hreal : mmap_fixed_rw_budget_ok FL mo A n = true).
  { unfold mmap_fixed_rw_budget_ok, vm_backing_within_limit. fold h. fold mo1. apply Z.leb_le.
    rewrite <- Eper in Hbud. unfold vm_backing_within_limit in Hbud. apply Z.leb_le in Hbud. rewrite m_vmmaps_perase in Hbud.
    etransitivity; [| exact Hbud]. rewrite vm_backing_used_perase, vm_backing_used_split.
    enough (length (m_vm_materialized mo1) <= length P')%nat by (unfold page_size; nia).
    apply NoDup_incl_length; [exact M1|]. intros p Hp. exact (M3 p Hp). }
  assert (D : forall o, syscall_spec (sys_input segs msF (Z_to_bv 64 222)) mo o <->
     mmap_spec A (Z_to_bv 64 len) (Z_to_bv 64 PROT_RW) FL (Z_to_bv 64 (-1)) (Z_to_bv 64 0)
               (sys_input segs msF (Z_to_bv 64 222)) mo o).
  { intros o. rewrite (syscall_spec_222 _ _ _ (sysno_of segs msF _ 222 ltac:(lia) eq_refl)).
    rewrite in_a0_si, in_a1_si, in_a2_si, in_a3_si, in_a4_si, in_a5_si, Ha0, Ha1, Ha2, Ha3, Ha4, Ha5. reflexivity. }
  pose proof (fun o => mmap_fixed_rw_outcome_raw A (Z_to_bv 64 len) (Z_to_bv 64 PROT_RW) FL (Z_to_bv 64 (-1)) (Z_to_bv 64 0)
                (sys_input segs msF (Z_to_bv 64 222)) mo o
                eq_refl Fanon Hlen Fmod Fna Ffna Ffrw ltac:(rewrite EA; exact Hce) ltac:(rewrite EA; exact Hal)
                ltac:(rewrite EA; exact Hpos) Hrf Hmc) as RAW.
  cbv zeta in RAW.
  assert (OUT : forall eff mo' evs,
     (syscall_spec (sys_input segs msF (Z_to_bv 64 222)) mo (Ok eff mo' evs)
      /\ ~ spurious_refusal_cfg ACFG (sys_input segs msF (Z_to_bv 64 222)) mo eff)
     <-> Ok eff mo' evs = Ok (mkEffect A [] [(A, n)]) mo1 []).
  { intros eff mo' evs.
    rewrite D, <- (mmap_forced_iff_ns _ _ _ _ _ _ _ _ eff mo' evs (sysno_of segs msF _ 222 ltac:(lia) eq_refl) D).
    rewrite (mmap_fixed_rw_outcome A (Z_to_bv 64 len) (Z_to_bv 64 PROT_RW) FL (Z_to_bv 64 (-1)) (Z_to_bv 64 0) _ mo (Ok eff mo' evs)
               eq_refl Fanon Hlen Fmod Fna Ffna Ffrw ltac:(rewrite EA; exact Hce) ltac:(rewrite EA; exact Hal)
               ltac:(rewrite EA; exact Hpos) Hrf Hmc Hreal).
    change (Z_to_bv 64 (page_round_up_Z (bv_unsigned (Z_to_bv 64 len)))) with n.
    unfold mmap_err_out_when, mmap_fixed_commit_refusable. rewrite Hreal. cbn [negb mmap_errnos_when]. split.
    - intros [(e & [] & _)|[[_ E]|(e & He & _)]]; [exact E| exfalso; exact (mmap_destructive_errnos_In e He)].
    - intros E. right; left. split; [reflexivity| exact E]. }
  assert (Hwf_an : bv_unsigned A + bv_unsigned n <= 2 ^ 64) by (rewrite EA, Hn; lia).
  assert (Hnpos : 0 < lenZ len).
  { unfold lenZ, page_round_up_Z. pose proof (u64_range (Z_to_bv 64 len)) as R.
    assert (bv_unsigned (Z_to_bv 64 len) <> 0).
    { intros E. unfold w_is0 in Hlen. assert (EE : Z_to_bv 64 len = Z_to_bv 64 0) by (apply bv_eq; rewrite E; reflexivity).
      rewrite EE, bv_eqb_refl in Hlen. discriminate. }
    unfold page_size. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). nia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  assert (Eli : mmap_noreserve_b FL = true -> lazy_interior A n = [(A, n)]).
  { intros _. apply (lazy_interior_aligned A n ltac:(rewrite EA; exact Hal) ltac:(rewrite Hn; apply lenZ_aligned) ltac:(rewrite Hn; lia) Hwf_an). }
  split.
  - exact Hsvc.
  - intros eff mo' evs Hs0 Hns0. pose proof (proj1 (OUT _ _ _) (conj Hs0 Hns0)) as Hs. clear Hs0 Hns0.
    apply Ok_inj in Hs as (-> & -> & ->). rewrite EP, EH.
    split. { cbn [nstepL]. split; [reflexivity|]. split; [reflexivity|]. exact Eper. }
    split. { subst mo1. rewrite m_halted_with_mmap_replacement, m_halted_with_vmmaps. exact Hh. }
    split.
    { constructor.
      + exact M1.
      + exact M2.
      + intros p Hp. apply (proj2 (page_allowedb_ivl _ p (M2 p Hp) HP'al)). exact (M3 p Hp).
      + intros p Hp. rewrite Elazy, page_in_ranges_app. apply orb_true_iff. right.
        rewrite Emat in Hp. apply filter_In in Hp as [Hp Hout]. pose proof (N2 p Hp) as Hpal.
        unfold page_outside_range in Hout. apply negb_true_iff in Hout.
        rewrite page_in_ranges_subtract_out; [exact (N4 p Hp)| exact Wl| lia|].
        apply andb_false_iff in Hout as [Hout|Hout]; [apply Z.leb_gt in Hout| apply Z.ltb_ge in Hout].
        * left. destruct (aligned_in_or_out (bv_unsigned p) addr (addr + lenZ len) Hpal Hal Hhi); unfold page_size in *; lia.
        * right. exact Hout.
      + rewrite Emaps. cbn [vm_limit mmap_fixed_rw_next].
        rewrite <- Eper in Hbud. unfold vm_backing_within_limit in Hbud. apply Z.leb_le in Hbud.
        rewrite vm_backing_used_perase, m_vmmaps_perase, Emaps in Hbud. cbn [vm_limit mmap_fixed_rw_next] in Hbud.
        rewrite A_bytes_ivl. exact Hbud. }
    split.
    {
      intros w Hpl Hw. rewrite Elazy in Hpl. pose proof (page_base_facts w) as (B1 & B2 & B3).
      destruct (aligned_in_or_out (bv_unsigned (page_base w)) addr (addr + lenZ len) B3 Hal Hhi) as [Hin|Hout].
      *
        destruct (mmap_noreserve_b FL) eqn:ENR.
        -- apply (proj2 (page_allowedb_ivl _ _ B3 HP'al)). subst P'. apply in_app_iff. left.
           apply page_base_in_pages_of; [exact Hal| exact Hhi| lia| lia| unfold page_size in *; lia].
        -- exfalso. cbn [app] in Hpl.
           rewrite (page_in_ranges_subtract_in (page_base w) (m_vm_lazy mo) addr (addr + lenZ len) Wl) in Hpl; [discriminate| unfold page_size in *; lia].
      *
        assert (Hpl' : page_in_ranges (page_base w) (m_vm_lazy mo) = true).
        { rewrite page_in_ranges_app in Hpl. apply orb_prop in Hpl as [Hpl|Hpl].
          - exfalso. destruct (mmap_noreserve_b FL); [| cbn in Hpl; discriminate]. rewrite (Eli eq_refl) in Hpl.
            rewrite page_in_ranges_cons_out in Hpl; [cbn in Hpl; discriminate| rewrite EA, Hn; unfold page_size in *; lia| rewrite Hn; lia].
          - rewrite page_in_ranges_subtract_out in Hpl; [exact Hpl| exact Wl| lia| exact Hout]. }
        unfold unhide_range in Hw. apply andb_false_iff in Hw as [Hw|Hw].
        -- pose proof (HC w Hpl' Hw) as Hal0. apply (proj2 (page_allowedb_ivl _ _ B3 HP'al)). subst P'. apply in_app_iff. right.
           apply cut_pages_in. split; [exact (proj1 (page_allowedb_ivl _ _ B3 HA) Hal0)|]. unfold page_size in *. lia.
        -- exfalso. apply negb_false_iff in Hw. unfold in_rangeb in Hw. apply andb_prop in Hw as [W1 W2].
           apply Z.leb_le in W1. apply Z.ltb_lt in W2.
           destruct (page_of_byte_in_aligned w addr (addr + lenZ len) Hal Hhi ltac:(lia)). unfold page_size in *. lia. }
    split. { exact HP'al. }
    split.
    {
      apply minvL_perase. split; [| split; [| split]].
      + subst mo1. rewrite strip_vm_with_mmap_replacement. apply minv_strip_vmmaps; [reflexivity| exact Hh| exact HM0].
      + intros r x Hr Hx. rewrite Emaps. cbn [vm_maps mmap_fixed_rw_next]. rewrite Elazy in Hr. apply in_app_iff in Hr as [Hr|Hr].
        * destruct (mmap_noreserve_b FL); [| destruct Hr]. rewrite (Eli eq_refl) in Hr.
          destruct Hr as [<-|[]]. cbn [fst snd] in Hx. eapply map_contains_covers; [exact Hmc| exact Hx].
        * destruct (maps_subtract_sem (m_vm_lazy mo) addr (addr + lenZ len) Wl ltac:(lia)) as (_ & _ & Cv).
          assert (Cx : covered (maps_subtract (m_vm_lazy mo) addr (addr + lenZ len)) x = true).
          { unfold covered. apply existsb_exists. exists r. split; [exact Hr|]. unfold in_iv, in_rng, B, S.
            apply andb_true_intro. split; [apply Z.leb_le| apply Z.ltb_lt]; lia. }
          rewrite Cv in Cx. apply andb_prop in Cx as [C1 _].
          unfold covered in C1. apply existsb_exists in C1 as (r0 & Hr0 & Hx0). unfold in_iv, in_rng, B, S in Hx0.
          apply andb_prop in Hx0 as [X1 X2]. apply Z.leb_le in X1. apply Z.ltb_lt in X2.
          exact (HL r0 x Hr0 ltac:(lia)).
      + subst mo1. apply model_ivs_wf_with_mmap_replacement; [rewrite EA, Hn; lia|].
        apply model_ivs_wf_with_vmmaps; [exact HW| exact Wm| | reflexivity]. cbn [vm_noaccess mmap_fixed_rw_next].
        apply maps_subtract_wf; [exact Wn| pose proof (u64_range n); lia].
      + rewrite Emaps. cbn [vm_maps mmap_fixed_rw_next]. exact HS. }
    split. { cbn. apply AsanAcct.ranges_avoid_nil. }
    split. { reflexivity. }
    split. { rewrite <- EA, <- Hn. apply hzero_unhide_zu; [left; split; reflexivity| exact HZ]. }
    split. { apply hide_ok_mono. intros a Ha. unfold unhide_range in Ha. apply andb_prop in Ha as [Ha _]. exact Ha. }
    intros x0 Hx0 Hu0. rewrite <- EA, <- Hn in Hu0. cbn [eff_zeros eff_unmaps]. eapply cov_unhide_zu; [left; split; reflexivity| exact Hx0| exact Hu0].
  - intros Hs. apply D, RAW in Hs. destruct Hs as [(e & _ & Hs)|[(_ & Hs)|(e & _ & Hs)]]; discriminate.
  - intros eff moE' evs Hst. cbn [nstepL] in Hst. destruct Hst as (-> & Hs & ->).
    eexists (mkEffect A [] [(A, n)]), mo1. split; [rewrite Hs; reflexivity|]. split; [apply (proj2 (OUT _ _ _)); reflexivity|]. rewrite EP. exact Eper.
  - eexists (mkEffect A [] [(A, n)]), _, []. cbn [nstepL]. repeat split; reflexivity.
  - intros eff' mo1' evs' Hs. apply D, RAW in Hs.
    destruct Hs as [(e & _ & Hs)|[(_ & Hs)|(e & _ & Hs)]]; apply Ok_inj in Hs as (_ & -> & _).
    + exact Hh.
    + rewrite m_halted_with_mmap_replacement, m_halted_with_vmmaps. exact Hh.
    + rewrite m_halted_with_mmap_destroyed. exact Hh.
Qed.

#[using="HF HZ Hh HI HC HA"] Lemma mmap_commit_factsL : forall addr len off,
  at_nodeL segs (LMmapCommit addr len off) (restrict H msF) -> nsafeL (LMmapCommit addr len off) (perase P mo) ->
  factsL_ns segs (LMmapCommit addr len off) H P msF mo (Z_to_bv 64 222).
Proof.
  intros addr len off HatR Hsafe.
  destruct HatR as ((Hsvc & Ha0 & Ha1 & Ha2 & Ha3 & Ha4 & Ha5 & Hlen) & Hal & Hpos & Hub & Hoff).
  unfold areg in Ha0, Ha1, Ha2, Ha3, Ha4, Ha5. cbn [AsanAcct.restrict ms_regs ms_svc_pending] in Hsvc, Ha0, Ha1, Ha2, Ha3, Ha4, Ha5.
  fold (areg msF 10) in Ha0. fold (areg msF 11) in Ha1. fold (areg msF 12) in Ha2. fold (areg msF 13) in Ha3.
  fold (areg msF 14) in Ha4. fold (areg msF 15) in Ha5.
  cbn [nsafeL] in Hsafe. rewrite m_vmmaps_perase in Hsafe. destruct Hsafe as (Hce & Hrf & Hmc & Hbud).
  pose proof HMLm as (HM0 & HL & HW & HS). pose proof HW as (Wm & Wn & Wl & Wsp).
  destruct (fixed_flag_facts MAPF_FIXED (or_introl eq_refl)) as (Fanon & Fmod & Fna & Ffna & Ffrw & Fnr). cbn [Z.eqb Pos.eqb] in Fnr.
  set (FL := Z_to_bv 64 MAPF_FIXED) in *. set (A := Z_to_bv 64 addr) in *. set (n := lenW len) in *.
  set (h := m_vmmaps mo) in *.
  pose proof (lenZ_nonneg len) as Hn0.
  assert (EA : bv_unsigned A = addr) by (subst A; apply u64_lit; lia).
  assert (Hn : bv_unsigned n = lenZ len) by (subst n; unfold lenW; apply u64_lit; lia).
  assert (Hhi : (addr + lenZ len) mod page_size = 0) by (rewrite <- Zplus_mod_idemp_l, Hal, Z.add_0_l; apply lenZ_aligned).
  set (wlo := shw_lo off addr). set (whi := shw_hi off addr (lenZ len)).
  destruct (shw_bounds off addr (lenZ len) ltac:(lia) ltac:(lia) Hn0) as (W1 & W2 & W3 & W4 & W5 & W6). fold wlo whi in W1, W2, W3, W4, W5, W6.
  assert (W7 : whi <= 2 ^ 64).
  { assert (X : (addr + lenZ len) / 8 < 2 ^ 61) by (apply Z.div_lt_upper_bound; lia). unfold page_size in *. lia. }
  set (mo1 := with_mmap_replacement FL A n (with_vmmaps (mmap_fixed_rw_next h A n) mo)).
  set (P' := pages_of wlo whi ++ cut_pages addr (addr + lenZ len) P).
  assert (EP : forall eff, allowL (LMmapCommit addr len off) eff P = P').
  { intros eff. cbn [allowL]. unfold addrZ. fold A. rewrite EA. reflexivity. }
  assert (EH : forall eff, hideL (LMmapCommit addr len off) eff H = unhide_zb wlo whi (unhide_range addr (addr + lenZ len) H)).
  { intros eff. cbn [hideL]. unfold addrZ. fold A. rewrite EA. reflexivity. }

  assert (Eper : perase P' mo1 = lmcommit_post (perase P mo) addr len off).
  { unfold lmcommit_post. rewrite m_vmmaps_perase. fold FL A n h. unfold lmfixed_next. rewrite Hmc.
    rewrite <- perase_with_mmap_replacement. rewrite EA, Hn.
    subst mo1 P'. rewrite (perase_app _ (cut_pages addr (addr + lenZ len) P)). rewrite m_vm_materialized_perase.
    unfold addrZ. fold A. rewrite EA. reflexivity. }

  pose proof HI as [N1 N2 N3 N4 N5].
  assert (Emat : m_vm_materialized mo1 = List.filter (page_outside_range addr (addr + lenZ len)) (m_vm_materialized mo)).
  { subst mo1. unfold with_mmap_replacement, with_mmap_backing. rewrite EA, Hn, Fnr. model_proj; reflexivity. }
  assert (Elazy : m_vm_lazy mo1 = maps_subtract (m_vm_lazy mo) addr (addr + lenZ len)).
  { subst mo1. unfold with_mmap_replacement, with_mmap_backing. rewrite EA, Hn, Fnr. model_proj; reflexivity. }
  assert (Emaps : m_vmmaps mo1 = mmap_fixed_rw_next h A n).
  { subst mo1. unfold with_mmap_replacement, with_mmap_backing. rewrite Fnr. model_proj; reflexivity. }
  assert (HP'al : P_aligned P').
  { subst P'. apply P_aligned_app; [apply pages_of_aligned; [exact W1| exact W3| exact W7]| apply cut_pages_aligned; exact HA]. }
  assert (M1 : List.NoDup (m_vm_materialized mo1)) by (rewrite Emat; apply NoDup_filter; exact N1).
  assert (M2 : forall p, In p (m_vm_materialized mo1) -> bv_unsigned p mod page_size = 0).
  { rewrite Emat. intros p Hp. apply filter_In in Hp as [Hp _]. exact (N2 p Hp). }
  assert (M3 : forall p, In p (m_vm_materialized mo1) -> In p P').
  { rewrite Emat. intros p Hp. apply filter_In in Hp as [Hp Hout]. subst P'. apply in_app_iff. right.
    apply cut_pages_in. split; [exact (proj1 (page_allowedb_ivl _ p (N2 p Hp) HA) (N3 p Hp))|].
    unfold page_outside_range in Hout. apply negb_true_iff in Hout. apply andb_false_iff in Hout as [Hout|Hout];
      [left; apply Z.leb_gt in Hout| right; apply Z.ltb_ge in Hout]; lia. }

  assert (Hreal : mmap_fixed_rw_budget_ok FL mo A n = true).
  { unfold mmap_fixed_rw_budget_ok, vm_backing_within_limit. fold h. fold mo1. apply Z.leb_le.
    rewrite <- Eper in Hbud. unfold vm_backing_within_limit in Hbud. apply Z.leb_le in Hbud. rewrite m_vmmaps_perase in Hbud.
    etransitivity; [| exact Hbud]. rewrite vm_backing_used_perase, vm_backing_used_split.
    enough (length (m_vm_materialized mo1) <= length P')%nat by (unfold page_size; nia).
    apply NoDup_incl_length; [exact M1|]. intros p Hp. exact (M3 p Hp). }
  assert (D : forall o, syscall_spec (sys_input segs msF (Z_to_bv 64 222)) mo o <->
     mmap_spec A (Z_to_bv 64 len) (Z_to_bv 64 PROT_RW) FL (Z_to_bv 64 (-1)) (Z_to_bv 64 0)
               (sys_input segs msF (Z_to_bv 64 222)) mo o).
  { intros o. rewrite (syscall_spec_222 _ _ _ (sysno_of segs msF _ 222 ltac:(lia) eq_refl)).
    rewrite in_a0_si, in_a1_si, in_a2_si, in_a3_si, in_a4_si, in_a5_si, Ha0, Ha1, Ha2, Ha3, Ha4, Ha5. reflexivity. }
  pose proof (fun o => mmap_fixed_rw_outcome_raw A (Z_to_bv 64 len) (Z_to_bv 64 PROT_RW) FL (Z_to_bv 64 (-1)) (Z_to_bv 64 0)
                (sys_input segs msF (Z_to_bv 64 222)) mo o
                eq_refl Fanon Hlen Fmod Fna Ffna Ffrw ltac:(rewrite EA; exact Hce) ltac:(rewrite EA; exact Hal)
                ltac:(rewrite EA; exact Hpos) Hrf Hmc) as RAW.
  cbv zeta in RAW.
  assert (OUT : forall eff mo' evs,
     (syscall_spec (sys_input segs msF (Z_to_bv 64 222)) mo (Ok eff mo' evs)
      /\ ~ spurious_refusal_cfg ACFG (sys_input segs msF (Z_to_bv 64 222)) mo eff)
     <-> Ok eff mo' evs = Ok (mkEffect A [] [(A, n)]) mo1 []).
  { intros eff mo' evs.
    rewrite D, <- (mmap_forced_iff_ns _ _ _ _ _ _ _ _ eff mo' evs (sysno_of segs msF _ 222 ltac:(lia) eq_refl) D).
    rewrite (mmap_fixed_rw_outcome A (Z_to_bv 64 len) (Z_to_bv 64 PROT_RW) FL (Z_to_bv 64 (-1)) (Z_to_bv 64 0) _ mo (Ok eff mo' evs)
               eq_refl Fanon Hlen Fmod Fna Ffna Ffrw ltac:(rewrite EA; exact Hce) ltac:(rewrite EA; exact Hal)
               ltac:(rewrite EA; exact Hpos) Hrf Hmc Hreal).
    change (Z_to_bv 64 (page_round_up_Z (bv_unsigned (Z_to_bv 64 len)))) with n.
    unfold mmap_err_out_when, mmap_fixed_commit_refusable. rewrite Hreal. cbn [negb mmap_errnos_when]. split.
    - intros [(e & [] & _)|[[_ E]|(e & He & _)]]; [exact E| exfalso; exact (mmap_destructive_errnos_In e He)].
    - intros E. right; left. split; [reflexivity| exact E]. }
  assert (Hwf_an : bv_unsigned A + bv_unsigned n <= 2 ^ 64) by (rewrite EA, Hn; lia).
  assert (SUBH : forall a, unhide_zb wlo whi (unhide_range addr (addr + lenZ len) H) a = true -> H a = true).
  { intros a Ha. unfold unhide_zb, unhide_range in Ha. apply andb_prop in Ha as [Ha _]. apply andb_prop in Ha as [Ha _]. exact Ha. }
  split.
  - exact Hsvc.
  - intros eff mo' evs Hs0 Hns0. pose proof (proj1 (OUT _ _ _) (conj Hs0 Hns0)) as Hs. clear Hs0 Hns0.
    apply Ok_inj in Hs as (-> & -> & ->). rewrite EP, EH.
    split. { cbn [nstepL]. split; [reflexivity|]. split; [reflexivity|]. exact Eper. }
    split. { subst mo1. rewrite m_halted_with_mmap_replacement, m_halted_with_vmmaps. exact Hh. }
    split.
    { constructor.
      + exact M1.
      + exact M2.
      + intros p Hp. apply (proj2 (page_allowedb_ivl _ p (M2 p Hp) HP'al)). exact (M3 p Hp).
      + intros p Hp. rewrite Elazy.
        rewrite Emat in Hp. apply filter_In in Hp as [Hp Hout]. pose proof (N2 p Hp) as Hpal.
        unfold page_outside_range in Hout. apply negb_true_iff in Hout.
        rewrite page_in_ranges_subtract_out; [exact (N4 p Hp)| exact Wl| lia|].
        apply andb_false_iff in Hout as [Hout|Hout]; [apply Z.leb_gt in Hout| apply Z.ltb_ge in Hout].
        * left. destruct (aligned_in_or_out (bv_unsigned p) addr (addr + lenZ len) Hpal Hal Hhi); unfold page_size in *; lia.
        * right. exact Hout.
      + rewrite Emaps. cbn [vm_limit mmap_fixed_rw_next].
        rewrite <- Eper in Hbud. unfold vm_backing_within_limit in Hbud. apply Z.leb_le in Hbud.
        rewrite vm_backing_used_perase, m_vmmaps_perase, Emaps in Hbud. cbn [vm_limit mmap_fixed_rw_next] in Hbud.
        rewrite A_bytes_ivl. exact Hbud. }
    split.
    {
      intros w Hpl Hw. rewrite Elazy in Hpl. pose proof (page_base_facts w) as (B1 & B2 & B3).
      unfold unhide_zb in Hw. apply andb_false_iff in Hw as [Hw|Hw].
      2:{
          apply negb_false_iff in Hw. apply andb_prop in Hw as [Hw _]. unfold in_rangeb in Hw. apply andb_prop in Hw as [X1 X2]. apply Z.leb_le in X1. apply Z.ltb_lt in X2.
          apply (proj2 (page_allowedb_ivl _ _ B3 HP'al)). subst P'. apply in_app_iff. left.
          apply page_base_in_pages_of; [exact W1| exact W2| exact W3| exact W7| lia]. }
      destruct (aligned_in_or_out (bv_unsigned (page_base w)) addr (addr + lenZ len) B3 Hal Hhi) as [Hin|Hout].
      *
        exfalso.
        rewrite (page_in_ranges_subtract_in (page_base w) (m_vm_lazy mo) addr (addr + lenZ len) Wl) in Hpl; [discriminate| unfold page_size in *; lia].
      *
        assert (Hpl' : page_in_ranges (page_base w) (m_vm_lazy mo) = true).
        { rewrite page_in_ranges_subtract_out in Hpl; [exact Hpl| exact Wl| lia| exact Hout]. }
        unfold unhide_range in Hw. apply andb_false_iff in Hw as [Hw|Hw].
        -- pose proof (HC w Hpl' Hw) as Hal0. apply (proj2 (page_allowedb_ivl _ _ B3 HP'al)). subst P'. apply in_app_iff. right.
           apply cut_pages_in. split; [exact (proj1 (page_allowedb_ivl _ _ B3 HA) Hal0)|]. unfold page_size in *. lia.
        -- exfalso. apply negb_false_iff in Hw. unfold in_rangeb in Hw. apply andb_prop in Hw as [X1 X2].
           apply Z.leb_le in X1. apply Z.ltb_lt in X2.
           destruct (page_of_byte_in_aligned w addr (addr + lenZ len) Hal Hhi ltac:(lia)). unfold page_size in *. lia. }
    split. { exact HP'al. }
    split.
    {
      apply minvL_perase. split; [| split; [| split]].
      + subst mo1. rewrite strip_vm_with_mmap_replacement. apply minv_strip_vmmaps; [reflexivity| exact Hh| exact HM0].
      + intros r x Hr Hx. rewrite Emaps. cbn [vm_maps mmap_fixed_rw_next]. rewrite Elazy in Hr.
        destruct (maps_subtract_sem (m_vm_lazy mo) addr (addr + lenZ len) Wl ltac:(lia)) as (_ & _ & Cv).
        assert (Cx : covered (maps_subtract (m_vm_lazy mo) addr (addr + lenZ len)) x = true).
        { unfold covered. apply existsb_exists. exists r. split; [exact Hr|]. unfold in_iv, in_rng, B, S.
          apply andb_true_intro. split; [apply Z.leb_le| apply Z.ltb_lt]; lia. }
        rewrite Cv in Cx. apply andb_prop in Cx as [C1 _].
        unfold covered in C1. apply existsb_exists in C1 as (r0 & Hr0 & Hx0). unfold in_iv, in_rng, B, S in Hx0.
        apply andb_prop in Hx0 as [X1 X2]. apply Z.leb_le in X1. apply Z.ltb_lt in X2.
        exact (HL r0 x Hr0 ltac:(lia)).
      + subst mo1. apply model_ivs_wf_with_mmap_replacement; [rewrite EA, Hn; lia|].
        apply model_ivs_wf_with_vmmaps; [exact HW| exact Wm| | reflexivity]. cbn [vm_noaccess mmap_fixed_rw_next].
        apply maps_subtract_wf; [exact Wn| pose proof (u64_range n); lia].
      + rewrite Emaps. cbn [vm_maps mmap_fixed_rw_next]. exact HS. }
    split. { cbn. apply AsanAcct.ranges_avoid_nil. }
    split. { reflexivity. }
    split. { eapply hzero_subset; [| apply hzero_unhide_zu; [left; split; reflexivity| exact HZ]].
             intros x Hx. rewrite EA, Hn. unfold unhide_zb in Hx. apply andb_prop in Hx as [Hx _]. exact Hx. }
    split. { apply hide_ok_mono. intros a Ha. cbn [hideL] in Ha. unfold unhide_zb, unhide_range in Ha. apply andb_prop in Ha as [Ha _]. apply andb_prop in Ha as [Ha _]. exact Ha. }
    intros x0 Hx0 Hu0. cbn [eff_zeros eff_unmaps]. rewrite <- EA, <- Hn in Hu0. eapply cov_unhide_win; [exact Hx0| exact Hu0].
  - intros Hs. apply D, RAW in Hs. destruct Hs as [(e & _ & Hs)|[(_ & Hs)|(e & _ & Hs)]]; discriminate.
  - intros eff moE' evs Hst. cbn [nstepL] in Hst. destruct Hst as (-> & Hs & ->).
    eexists (mkEffect A [] [(A, n)]), mo1. split; [rewrite Hs; reflexivity|]. split; [apply (proj2 (OUT _ _ _)); reflexivity|]. rewrite EP. exact Eper.
  - eexists (mkEffect A [] [(A, n)]), _, []. cbn [nstepL]. repeat split; reflexivity.
  - intros eff' mo1' evs' Hs. apply D, RAW in Hs.
    destruct Hs as [(e & _ & Hs)|[(_ & Hs)|(e & _ & Hs)]]; apply Ok_inj in Hs as (_ & -> & _).
    + exact Hh.
    + rewrite m_halted_with_mmap_replacement, m_halted_with_vmmaps. exact Hh.
    + rewrite m_halted_with_mmap_destroyed. exact Hh.
Qed.

#[using="HF HZ Hh HO HI HC HA"] Lemma mmap_factsL : forall addr len prot flags,
  at_node segs (NMmap addr len prot flags) (restrict H msF) -> nsafeL (LNode (NMmap addr len prot flags)) (perase P mo) ->
  factsL_ns segs (LNode (NMmap addr len prot flags)) H P msF mo (Z_to_bv 64 222).
Proof.
  intros addr len prot flags HatR Hsafe. pose proof (at_node_unrestrict segs H HO _ _ HatR) as Hat.
  destruct Hat as (Hsvc & Ha0 & Ha1 & Ha2 & Ha3 & Ha4 & Ha5 & Hlen & Hnr & Hanon & Hshape).
  cbv zeta in Hshape. cbn [nsafeL nsafe] in Hsafe. rewrite m_vmmaps_perase in Hsafe. destruct Hsafe as [Hsafe Hpess].
  pose proof HMLm as (HM0 & HL & HW & HS). pose proof HW as (Wm & Wn & Wl & Wsp).
  pose proof (minv_alloc_top _ HM0) as [_ Htop]. rewrite m_vmmaps_strip_vm in Htop.
  assert (Hoff : mmap_off_aligned_b (Z_to_bv 64 0) = true) by reflexivity.
  set (FL := Z_to_bv 64 flags) in *. set (PR := Z_to_bv 64 prot) in *.
  set (nZ := page_round_up_Z (bv_unsigned (Z_to_bv 64 len))) in *. set (n := Z_to_bv 64 nZ) in *.
  set (h := m_vmmaps mo) in *.
  pose proof (lenZ_nonneg len) as Hn0. change (lenZ len) with nZ in Hn0.
  change (lenZ len) with nZ in Hpess.
  assert (HnZal : nZ mod page_size = 0) by (subst nZ; apply page_round_up_Z_aligned).
  assert (D : forall o, syscall_spec (sys_input segs msF (Z_to_bv 64 222)) mo o <->
     mmap_spec (Z_to_bv 64 addr) (Z_to_bv 64 len) PR FL (Z_to_bv 64 (-1)) (Z_to_bv 64 0)
               (sys_input segs msF (Z_to_bv 64 222)) mo o).
  { intros o. rewrite (syscall_spec_222 _ _ _ (sysno_of segs msF _ 222 ltac:(lia) eq_refl)).
    rewrite in_a0_si, in_a1_si, in_a2_si, in_a3_si, in_a4_si, in_a5_si, Ha0, Ha1, Ha2, Ha3, Ha4, Ha5. reflexivity. }

  assert (Hback : mmap_noreserve_backed_ok FL (perase P mo) nZ = true -> mmap_noreserve_backed_ok FL mo nZ = true).
  { intros Hb. unfold mmap_noreserve_backed_ok in *. rewrite Hnr in Hb |- *. apply Z.leb_le. apply Z.leb_le in Hb.
    rewrite m_vmmaps_perase in Hb. pose proof (vm_backing_used_perase_ge P mo HI HA). lia. }
  assert (Hfnx : mmap_modeled_b PR FL (Z_to_bv 64 0) = true -> mmap_fixed_noaccess_b PR FL (Z_to_bv 64 0) = false).
  { intros Hm. unfold mmap_modeled_b in Hm. unfold mmap_fixed_noaccess_b.
    apply andb_prop in Hm as [Hm _]. apply andb_prop in Hm as [Hm _]. apply Z.eqb_eq in Hm.
    rewrite Hm. reflexivity. }
  assert (Hnax : mmap_noaccess_b PR FL (Z_to_bv 64 0) = true -> mmap_fixed_noaccess_b PR FL (Z_to_bv 64 0) = false).
  { intros Hm. unfold mmap_noaccess_b in Hm. unfold mmap_fixed_noaccess_b.
    apply andb_prop in Hm as [Hm _]. apply andb_prop in Hm as [_ Hm]. apply Z.eqb_eq in Hm.
    rewrite Hm. cbn. rewrite andb_false_r. reflexivity. }
  assert (Herr_al : ret_alignedb (efferr ENOMEM) = false) by (vm_compute; reflexivity).

  assert (ERRF : forall c e, In e (mmap_errnos_when c) -> mmap_fixed_noaccess_b PR FL (Z_to_bv 64 0) = false ->
     m_halted mo = None
     /\ MInv (ivl (allowL (LNode (NMmap addr len prot flags)) (efferr e) P)) mo
     /\ lazy_cover (hideL (LNode (NMmap addr len prot flags)) (efferr e) H) (m_vm_lazy mo) (ivl (allowL (LNode (NMmap addr len prot flags)) (efferr e) P))
     /\ P_aligned (allowL (LNode (NMmap addr len prot flags)) (efferr e) P)
     /\ minvL (perase (allowL (LNode (NMmap addr len prot flags)) (efferr e) P) mo)
     /\ AsanAcct.ranges_avoid H (syscall_effect_accesses (efferr e))
     /\ eff_copies (efferr e) = []
     /\ hzero (hideL (LNode (NMmap addr len prot flags)) (efferr e) H) (nret msF (efferr e))
     /\ hide_ok segs (LNode (NMmap addr len prot flags)) (efferr e) H (syscall_effect_accesses (efferr e))
     /\ (forall x0, H x0 = true -> hideL (LNode (NMmap addr len prot flags)) (efferr e) H x0 = false ->
           zb x0 = true \/ zeros_cover (eff_zeros (efferr e)) x0 = true \/ zeros_cover (eff_unmaps (efferr e)) x0 = true)).
  { intros c e He Hfx0. pose proof (proj2 (mmap_errnos_when_In c e He)) as ->.
    apply (fdkind_frame segs H P msF mo HF); try reflexivity.
    - cbn [allowL]. change (Z_to_bv 64 prot) with PR. change (Z_to_bv 64 flags) with FL. rewrite Hfx0. reflexivity.
    - exact HM0.
    - cbn. apply AsanAcct.ranges_avoid_nil.
    - apply hzero_nret_nomem. exact HZ. }
  assert (HnQ : forall a : word, bv_unsigned a + nZ <= alloc_top h -> bv_unsigned n = nZ).
  { intros a Ha. subst n. apply u64_lit. pose proof (alloc_top_lt h). pose proof (u64_range a). unfold two_pow_64 in *. lia. }

  assert (GRANTF : forall a : word,
     mmap_modeled_b PR FL (Z_to_bv 64 0) = true ->
     mmap_noreserve_backed_ok FL (perase P mo) nZ = true ->
     (bv_unsigned a mod page_size = 0) -> 0 < bv_unsigned a -> bv_unsigned a + nZ <= alloc_top h ->
     region_free (vm_reserved h ++ vm_maps h) a n = true ->
     let eff := mkEffect a [] [(a, n)] in
     let mo1 := with_vmmaps (grant_maps h a n) mo in
     m_halted mo1 = None
     /\ MInv (ivl (allowL (LNode (NMmap addr len prot flags)) eff P)) mo1
     /\ lazy_cover (hideL (LNode (NMmap addr len prot flags)) eff H) (m_vm_lazy mo1) (ivl (allowL (LNode (NMmap addr len prot flags)) eff P))
     /\ P_aligned (allowL (LNode (NMmap addr len prot flags)) eff P)
     /\ minvL (perase (allowL (LNode (NMmap addr len prot flags)) eff P) mo1)
     /\ AsanAcct.ranges_avoid H (syscall_effect_accesses eff)
     /\ eff_copies eff = []
     /\ hzero (hideL (LNode (NMmap addr len prot flags)) eff H) (nret msF eff)
     /\ hide_ok segs (LNode (NMmap addr len prot flags)) eff H (syscall_effect_accesses eff)
     /\ (forall x0, H x0 = true -> hideL (LNode (NMmap addr len prot flags)) eff H x0 = false ->
           zb x0 = true \/ zeros_cover (eff_zeros eff) x0 = true \/ zeros_cover (eff_unmaps eff) x0 = true)).
  { intros a Hm Hpm Q1 Q2 Q3 Q4. cbv zeta. pose proof (HnQ a Q3) as Hn.
    assert (EH : hideL (LNode (NMmap addr len prot flags)) (mkEffect a [] [(a, n)]) H
                 = unhide_range (bv_unsigned a) (bv_unsigned a + bv_unsigned n) H).
    { cbn [hideL]. unfold ret_alignedb. cbn [eff_ret]. rewrite (proj2 (Z.eqb_eq _ _) Q1). rewrite Hn. reflexivity. }
    assert (EP : allowL (LNode (NMmap addr len prot flags)) (mkEffect a [] [(a, n)]) P = P).
    { cbn [allowL]. change (Z_to_bv 64 prot) with PR. change (Z_to_bv 64 flags) with FL. rewrite (Hfnx Hm). reflexivity. }
    rewrite EH, EP.
    assert (Hwf_an : iv_wf (a, n)) by (unfold iv_wf, B, S; cbn [fst snd]; pose proof (alloc_top_lt h); unfold two_pow_64 in *; lia).
    split. { rewrite m_halted_with_vmmaps. exact Hh. }
    split.
    { eapply AsanAcct.MInv_transport; [exact HI| reflexivity| reflexivity|].
      cbn [m_vmmaps with_vmmaps vm_limit grant_maps]. rewrite A_bytes_ivl.
      pose proof (eager_used_grant_rw_le mo a n Wm Hwf_an) as LE.
      unfold mmap_noreserve_backed_ok in Hpm. rewrite Hnr in Hpm. apply Z.leb_le in Hpm.
      rewrite vm_backing_used_perase, m_vmmaps_perase in Hpm. fold h in Hpm, LE. rewrite Hn in LE.
      change (vm_limit (m_vmmaps (with_vmmaps (grant_maps h a n) mo))) with (vm_limit h). lia. }
    split.
    { cbn [m_vm_lazy with_vmmaps]. change (m_vm_lazy (with_vmmaps (grant_maps h a n) mo)) with (m_vm_lazy mo).
      apply lazy_cover_unhide_free; [exact HC|]. intros w Hw. eapply (grant_lazy_free a n); [exact HL| exact Q4| exact Q1| rewrite Hn; exact HnZal| exact Hw]. }
    split. { exact HA. }
    split.
    { apply minvL_perase. split; [| split; [| split]].
      + rewrite strip_vm_with_vmmaps. apply minv_strip_vmmaps; [reflexivity| exact Hh| exact HM0].
      + intros r x Hr Hx. cbn [m_vmmaps with_vmmaps vm_maps grant_maps].
        change (covered ((a, n) :: vm_maps h) x = true). change (m_vm_lazy (with_vmmaps (grant_maps h a n) mo)) with (m_vm_lazy mo) in Hr.
        unfold covered. cbn [existsb]. apply orb_true_iff. right. exact (HL r x Hr Hx).
      + apply model_ivs_wf_with_vmmaps; [exact HW| cbn [vm_maps grant_maps]; apply ivs_wf_cons; [exact Hwf_an| exact Wm]| exact Wn| reflexivity].
      + cbn [m_vmmaps with_vmmaps vm_maps grant_maps]. apply seps_cons_free; [| exact HS].
        eapply Decode.region_free_incl; [| exact Q4]. intros e0 He0. apply in_app_iff. right. exact He0. }
    split. { cbn. apply AsanAcct.ranges_avoid_nil. }
    split. { reflexivity. }
    split. { apply hzero_unhide_zu; [left; split; reflexivity| exact HZ]. }
    split. { apply hide_ok_mono. intros x Hx. try rewrite EH in Hx. cbn [hideL] in Hx. unfold unhide_range in Hx. apply andb_prop in Hx as [Hx _]. exact Hx. }
    intros x0 Hx0 Hu0. cbn [eff_zeros eff_unmaps]. eapply cov_unhide_zu; [left; split; reflexivity| exact Hx0| exact Hu0]. }
  destruct Hshape as [Hm | [[Hm Hna] | (Hm & Hna & Hfx)]].
  -
    pose proof (Hpess Hm) as Hpm. pose proof (Hback Hpm) as Hbk.
    assert (HRE : nmmap_refusable (perase P mo) len prot flags = negb (vm_gap_available h nZ)).
    { unfold nmmap_refusable. change (Z_to_bv 64 prot) with PR. change (Z_to_bv 64 flags) with FL. rewrite Hm.
      unfold mmap_grant_refusable. fold nZ. rewrite Hpm, m_vmmaps_perase. reflexivity. }
    assert (HRr : mmap_grant_refusable FL mo nZ = negb (vm_gap_available h nZ)).
    { unfold mmap_grant_refusable. rewrite Hbk. reflexivity. }
    pose proof (fun o => mmap_rw_outcome_raw (Z_to_bv 64 addr) _ PR FL (Z_to_bv 64 (-1)) _ (sys_input segs msF (Z_to_bv 64 222)) mo o Hoff Hanon Hlen Hm) as RAW.
    cbv zeta in RAW.
    assert (OUT := fun eff mo' evs (Hs0 : syscall_spec (sys_input segs msF (Z_to_bv 64 222)) mo (Ok eff mo' evs))
                      (Hns0 : ~ spurious_refusal_cfg ACFG (sys_input segs msF (Z_to_bv 64 222)) mo eff) =>
      proj1 (mmap_rw_outcome (Z_to_bv 64 addr) _ PR FL (Z_to_bv 64 (-1)) _ (sys_input segs msF (Z_to_bv 64 222)) mo (Ok eff mo' evs) Hoff Hanon Hlen Hm)
        (conj (proj1 (D _) Hs0) (proj2 (mmap_forced_iff_ns _ _ _ _ _ _ _ _ eff mo' evs (sysno_of segs msF _ 222 ltac:(lia) eq_refl) D) Hns0))).
    assert (OUT' := fun eff mo' evs H0 =>
      let HH0 := proj2 (mmap_rw_outcome (Z_to_bv 64 addr) _ PR FL (Z_to_bv 64 (-1)) _ (sys_input segs msF (Z_to_bv 64 222)) mo (Ok eff mo' evs) Hoff Hanon Hlen Hm) H0 in
      conj (proj2 (D _) (proj1 HH0)) (proj1 (mmap_forced_iff_ns _ _ _ _ _ _ _ _ eff mo' evs (sysno_of segs msF _ 222 ltac:(lia) eq_refl) D) (proj2 HH0))).
    cbv zeta in OUT, OUT'. unfold mmap_err_out_when in OUT, OUT'. fold nZ n h in OUT, OUT'. rewrite HRr in OUT, OUT'.
    split.
    + exact Hsvc.
    + intros eff mo' evs Hs0 Hns0. pose proof (OUT _ _ _ Hs0 Hns0) as Hs. clear Hs0 Hns0. destruct Hs as [(e & He & Hs)|(a & (Q1 & Q2 & Q3 & Q4 & Q5) & Hs)];
        apply Ok_inj in Hs as (-> & -> & ->).
      * split; [| exact (ERRF _ e He (Hfnx Hm))].
        pose proof (proj2 (mmap_errnos_when_In _ e He)) as ->.
        cbn [nstepL nstep allowL]. change (Z_to_bv 64 prot) with PR. change (Z_to_bv 64 flags) with FL. rewrite (Hfnx Hm).
        split; [reflexivity|]. left. exists ENOMEM. rewrite HRE. repeat split; auto.
      * unfold with_mmap_backing. rewrite Hnr. split; [| exact (GRANTF a Hm Hpm Q1 Q2 Q3 Q4)].
        cbn [nstepL nstep]. split; [reflexivity|]. right; left. split; [exact Hm|]. exists a.
        assert (EP : allowL (LNode (NMmap addr len prot flags)) (mkEffect a [] [(a, n)]) P = P).
        { cbn [allowL]. change (Z_to_bv 64 prot) with PR. change (Z_to_bv 64 flags) with FL. rewrite (Hfnx Hm). reflexivity. }
        rewrite EP. split.
        { unfold mmap_placed. rewrite m_vmmaps_perase. fold nZ n h. repeat split; try assumption. lia. }
        split; [exact Hpm|]. split; [reflexivity|]. unfold with_mmap_backing. change (Z_to_bv 64 flags) with FL. rewrite Hnr.
        rewrite perase_with_vmmaps, m_vmmaps_perase. reflexivity.
    + intros Hs. apply D, RAW in Hs. destruct Hs as [(e & _ & Hs)|(a & _ & Hs)]; discriminate.
    + intros eff moE' evs Hst. cbn [nstepL nstep] in Hst.
      destruct Hst as (-> & [(e & He & Hs & ->)|[(Hm' & a & (Q1 & Q2 & Q3 & Q4 & Q6) & Q5 & Hs & ->)|[(Hm' & _)|(Hm' & _)]]]).
      * rewrite HRE in He. pose proof (proj2 (mmap_errnos_when_In _ e He)) as ->.
        eexists (efferr ENOMEM), mo. split; [rewrite Hs; reflexivity|]. split; [apply OUT'; left; exists ENOMEM; split; [exact He|reflexivity]|].
        cbn [allowL]. change (Z_to_bv 64 prot) with PR. change (Z_to_bv 64 flags) with FL. rewrite (Hfnx Hm). reflexivity.
      * rewrite m_vmmaps_perase in Q4, Q6 |- *. fold h nZ n in Q3, Q4, Q6, Hs |- *.
        eexists (mkEffect a [] [(a, n)]), _. split; [rewrite Hs; reflexivity|].
        split; [apply OUT'; right; exists a; split; [repeat split; [exact Q1| exact Q2| exact Q6| exact Q4| exact Hbk]|reflexivity]|].
        cbn [allowL]. change (Z_to_bv 64 prot) with PR. change (Z_to_bv 64 flags) with FL. rewrite (Hfnx Hm).
        unfold with_mmap_backing. rewrite Hnr. rewrite perase_with_vmmaps. reflexivity.
      * exfalso. change (Z_to_bv 64 prot) with PR in Hm'. change (Z_to_bv 64 flags) with FL in Hm'. congruence.
      * exfalso. change (Z_to_bv 64 prot) with PR in Hm'. change (Z_to_bv 64 flags) with FL in Hm'. congruence.
    + destruct (vm_gap_available h nZ) eqn:HG.
      * destruct (mmap_grant_unforced FL mo nZ ltac:(rewrite HRr; reflexivity)) as (HB & a & Q1 & Q2 & Q3 & Q4).
        eexists (mkEffect a [] [(a, n)]), _, []. cbn [nstepL nstep]. split; [reflexivity|]. right; left. split; [exact Hm|].
        exists a. split.
        { unfold mmap_placed. rewrite m_vmmaps_perase. fold nZ n h. repeat split; try assumption.
          all: fold h in Q3, Q4; try exact Q4; lia. }
        split; [exact Hpm|]. split; reflexivity.
      * exists (efferr ENOMEM), (perase P mo), []. cbn [nstepL nstep]. split; [reflexivity|]. left. exists ENOMEM.
        rewrite HRE. cbn [negb]. split; [exact mmap_errnos_when_true|]. split; reflexivity.
    +
      intros eff' mo1' evs' Hs. apply D, RAW in Hs.
      destruct Hs as [(e & _ & Hs)|(a & _ & Hs)]; apply Ok_inj in Hs as (_ & -> & _); [exact Hh|].
      rewrite m_halted_with_mmap_backing, m_halted_with_vmmaps. exact Hh.
  -
    set (h' := fun a : word => mkVmMapsFull (vm_reserved h) ((a, n) :: vm_maps h) ((a, n) :: vm_noaccess h)
                                 (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)).
    assert (GRANTN : forall a : word,
       (bv_unsigned a mod page_size = 0) -> 0 < bv_unsigned a -> bv_unsigned a + nZ <= alloc_top h ->
       region_free (vm_reserved h ++ vm_maps h) a n = true ->
       let eff := mkEffectU a [] [] [(a, n)] [] [] in
       let mo1 := with_vmmaps (h' a) mo in
       m_halted mo1 = None
       /\ MInv (ivl (allowL (LNode (NMmap addr len prot flags)) eff P)) mo1
       /\ lazy_cover (hideL (LNode (NMmap addr len prot flags)) eff H) (m_vm_lazy mo1) (ivl (allowL (LNode (NMmap addr len prot flags)) eff P))
       /\ P_aligned (allowL (LNode (NMmap addr len prot flags)) eff P)
       /\ minvL (perase (allowL (LNode (NMmap addr len prot flags)) eff P) mo1)
       /\ AsanAcct.ranges_avoid H (syscall_effect_accesses eff)
       /\ eff_copies eff = []
       /\ hzero (hideL (LNode (NMmap addr len prot flags)) eff H) (nret msF eff)
       /\ hide_ok segs (LNode (NMmap addr len prot flags)) eff H (syscall_effect_accesses eff)
       /\ (forall x0, H x0 = true -> hideL (LNode (NMmap addr len prot flags)) eff H x0 = false ->
             zb x0 = true \/ zeros_cover (eff_zeros eff) x0 = true \/ zeros_cover (eff_unmaps eff) x0 = true)).
    { intros a Q1 Q2 Q3 Q4. cbv zeta. pose proof (HnQ a Q3) as Hn.
      assert (EH : hideL (LNode (NMmap addr len prot flags)) (mkEffectU a [] [] [(a, n)] [] []) H
                   = unhide_range (bv_unsigned a) (bv_unsigned a + bv_unsigned n) H).
      { cbn [hideL]. unfold ret_alignedb. cbn [eff_ret]. rewrite (proj2 (Z.eqb_eq _ _) Q1). rewrite Hn. reflexivity. }
      assert (EP : allowL (LNode (NMmap addr len prot flags)) (mkEffectU a [] [] [(a, n)] [] []) P = P).
      { cbn [allowL]. change (Z_to_bv 64 prot) with PR. change (Z_to_bv 64 flags) with FL. rewrite (Hnax Hna). reflexivity. }
      rewrite EH, EP.
      assert (Hwf_an : iv_wf (a, n)) by (unfold iv_wf, B, S; cbn [fst snd]; pose proof (alloc_top_lt h); unfold two_pow_64 in *; lia).
      split. { rewrite m_halted_with_vmmaps. exact Hh. }
      split.
      { eapply AsanAcct.MInv_transport; [exact HI| reflexivity| reflexivity|].
        pose proof (eager_used_grant_none_le mo a n Wm Hwf_an) as LE. cbv zeta in LE. fold h in LE.
        change (vm_limit (m_vmmaps (with_vmmaps (h' a) mo))) with (vm_limit h).
        pose proof (AsanAcct.minv_budget _ _ HI) as B0. fold h in B0. subst h'. cbv beta. cbv beta in LE. lia. }
      split.
      { cbv beta. change (m_vm_lazy (with_vmmaps _ mo)) with (m_vm_lazy mo).
        apply lazy_cover_unhide_free; [exact HC|]. intros w Hw. eapply (grant_lazy_free a n); [exact HL| exact Q4| exact Q1| rewrite Hn; exact HnZal| exact Hw]. }
      split. { exact HA. }
      split.
      { apply minvL_perase. split; [| split; [| split]].
        + rewrite strip_vm_with_vmmaps. apply minv_strip_vmmaps; [reflexivity| exact Hh| exact HM0].
        + intros r x Hr Hx. subst h'. change (covered ((a, n) :: vm_maps h) x = true). change (m_vm_lazy (with_vmmaps _ mo)) with (m_vm_lazy mo) in Hr.
          unfold covered. cbn [existsb]. apply orb_true_iff. right. exact (HL r x Hr Hx).
        + apply model_ivs_wf_with_vmmaps; [exact HW| cbn [vm_maps]; apply ivs_wf_cons; [exact Hwf_an| exact Wm]| cbn [vm_noaccess]; apply ivs_wf_cons; [exact Hwf_an| exact Wn]| reflexivity].
        + subst h'. change (seps ((a, n) :: vm_maps h)). apply seps_cons_free; [| exact HS].
          eapply Decode.region_free_incl; [| exact Q4]. intros e0 He0. apply in_app_iff. right. exact He0. }
      split. { cbn. apply AsanAcct.ranges_avoid_nil. }
      split. { reflexivity. }
      split. { apply hzero_unhide_zu; [right; split; reflexivity| exact HZ]. }
      split. { apply hide_ok_mono. intros x Hx. try rewrite EH in Hx. cbn [hideL] in Hx. unfold unhide_range in Hx. apply andb_prop in Hx as [Hx _]. exact Hx. }
      intros x0 Hx0 Hu0. cbn [eff_zeros eff_unmaps]. eapply cov_unhide_zu; [right; split; reflexivity| exact Hx0| exact Hu0]. }
    assert (HRE : nmmap_refusable (perase P mo) len prot flags = negb (vm_gap_available h nZ)).
    { unfold nmmap_refusable. change (Z_to_bv 64 prot) with PR. change (Z_to_bv 64 flags) with FL. rewrite Hm, Hna.
      unfold mmap_reserve_refusable. rewrite m_vmmaps_perase. reflexivity. }
    assert (HRr : mmap_reserve_refusable mo nZ = negb (vm_gap_available h nZ)) by reflexivity.
    pose proof (fun o => mmap_noaccess_outcome_raw (Z_to_bv 64 addr) _ PR FL (Z_to_bv 64 (-1)) _ (sys_input segs msF (Z_to_bv 64 222)) mo o Hoff Hanon Hlen Hm Hna) as RAW.
    cbv zeta in RAW.
    assert (OUT := fun eff mo' evs (Hs0 : syscall_spec (sys_input segs msF (Z_to_bv 64 222)) mo (Ok eff mo' evs))
                      (Hns0 : ~ spurious_refusal_cfg ACFG (sys_input segs msF (Z_to_bv 64 222)) mo eff) =>
      proj1 (mmap_noaccess_outcome (Z_to_bv 64 addr) _ PR FL (Z_to_bv 64 (-1)) _ (sys_input segs msF (Z_to_bv 64 222)) mo (Ok eff mo' evs) Hoff Hanon Hlen Hm Hna)
        (conj (proj1 (D _) Hs0) (proj2 (mmap_forced_iff_ns _ _ _ _ _ _ _ _ eff mo' evs (sysno_of segs msF _ 222 ltac:(lia) eq_refl) D) Hns0))).
    assert (OUT' := fun eff mo' evs H0 =>
      let HH0 := proj2 (mmap_noaccess_outcome (Z_to_bv 64 addr) _ PR FL (Z_to_bv 64 (-1)) _ (sys_input segs msF (Z_to_bv 64 222)) mo (Ok eff mo' evs) Hoff Hanon Hlen Hm Hna) H0 in
      conj (proj2 (D _) (proj1 HH0)) (proj1 (mmap_forced_iff_ns _ _ _ _ _ _ _ _ eff mo' evs (sysno_of segs msF _ 222 ltac:(lia) eq_refl) D) (proj2 HH0))).
    cbv zeta in OUT, OUT'. unfold mmap_err_out_when in OUT, OUT'. fold nZ n h in OUT, OUT'. rewrite HRr in OUT, OUT'.
    split.
    + exact Hsvc.
    + intros eff mo' evs Hs0 Hns0. pose proof (OUT _ _ _ Hs0 Hns0) as Hs. clear Hs0 Hns0. destruct Hs as [(e & He & Hs)|(a & (Q1 & Q2 & Q3 & Q4) & Hs)];
        apply Ok_inj in Hs as (-> & -> & ->).
      * split; [| exact (ERRF _ e He (Hnax Hna))].
        pose proof (proj2 (mmap_errnos_when_In _ e He)) as ->.
        cbn [nstepL nstep allowL]. change (Z_to_bv 64 prot) with PR. change (Z_to_bv 64 flags) with FL. rewrite (Hnax Hna).
        split; [reflexivity|]. left. exists ENOMEM. rewrite HRE. repeat split; auto.
      * unfold with_mmap_backing. rewrite Hnr. split; [| exact (GRANTN a Q1 Q2 Q3 Q4)].
        cbn [nstepL nstep]. split; [reflexivity|]. right; right; left. split; [exact Hm|]. split; [exact Hna|]. exists a.
        assert (EP : allowL (LNode (NMmap addr len prot flags)) (mkEffectU a [] [] [(a, n)] [] []) P = P).
        { cbn [allowL]. change (Z_to_bv 64 prot) with PR. change (Z_to_bv 64 flags) with FL. rewrite (Hnax Hna). reflexivity. }
        rewrite EP. split.
        { unfold mmap_placed. rewrite m_vmmaps_perase. fold nZ n h. repeat split; try assumption. lia. }
        split; [reflexivity|]. unfold with_mmap_backing. change (Z_to_bv 64 flags) with FL. rewrite Hnr.
        rewrite perase_with_vmmaps, m_vmmaps_perase. reflexivity.
    + intros Hs. apply D, RAW in Hs. destruct Hs as [(e & _ & Hs)|(a & _ & Hs)]; discriminate.
    + intros eff moE' evs Hst. cbn [nstepL nstep] in Hst.
      destruct Hst as (-> & [(e & He & Hs & ->)|[(Hm' & _)|[(_ & _ & a & (Q1 & Q2 & Q3 & Q4 & Q6) & Hs & ->)|(_ & Hna' & _)]]]).
      * rewrite HRE in He. pose proof (proj2 (mmap_errnos_when_In _ e He)) as ->.
        eexists (efferr ENOMEM), mo. split; [rewrite Hs; reflexivity|]. split; [apply OUT'; left; exists ENOMEM; split; [exact He|reflexivity]|].
        cbn [allowL]. change (Z_to_bv 64 prot) with PR. change (Z_to_bv 64 flags) with FL. rewrite (Hnax Hna). reflexivity.
      * exfalso. change (Z_to_bv 64 prot) with PR in Hm'. change (Z_to_bv 64 flags) with FL in Hm'. congruence.
      * rewrite m_vmmaps_perase in Q4, Q6 |- *. fold h nZ n in Q3, Q4, Q6, Hs |- *.
        eexists (mkEffectU a [] [] [(a, n)] [] []), _. split; [rewrite Hs; reflexivity|].
        split; [apply OUT'; right; exists a; split; [repeat split; [exact Q1| exact Q2| exact Q6| exact Q4]|reflexivity]|].
        cbn [allowL]. change (Z_to_bv 64 prot) with PR. change (Z_to_bv 64 flags) with FL. rewrite (Hnax Hna).
        unfold with_mmap_backing. rewrite Hnr. rewrite perase_with_vmmaps. reflexivity.
      * exfalso. change (Z_to_bv 64 prot) with PR in Hna'. change (Z_to_bv 64 flags) with FL in Hna'. congruence.
    + destruct (vm_gap_available h nZ) eqn:HG.
      * destruct (mmap_reserve_unforced mo nZ ltac:(rewrite HRr; reflexivity)) as (a & Q1 & Q2 & Q3 & Q4).
        eexists (mkEffectU a [] [] [(a, n)] [] []), _, []. cbn [nstepL nstep]. split; [reflexivity|]. right; right; left.
        split; [exact Hm|]. split; [exact Hna|]. exists a. split.
        { unfold mmap_placed. rewrite m_vmmaps_perase. fold nZ n h. repeat split; try assumption.
          all: fold h in Q3, Q4; try exact Q4; lia. }
        rewrite strip_mk. split; reflexivity.
      * exists (efferr ENOMEM), (perase P mo), []. cbn [nstepL nstep]. split; [reflexivity|]. left. exists ENOMEM.
        rewrite HRE. cbn [negb]. split; [exact mmap_errnos_when_true|]. split; reflexivity.
    +
      intros eff' mo1' evs' Hs. apply D, RAW in Hs.
      destruct Hs as [(e & _ & Hs)|(a & _ & Hs)]; apply Ok_inj in Hs as (_ & -> & _); [exact Hh|].
      rewrite m_halted_with_mmap_backing, m_halted_with_vmmaps. exact Hh.
  -
    destruct (Hsafe Hfx) as (S1 & S2 & S3 & S4 & S5).
    set (A := Z_to_bv 64 addr) in *.
    pose proof (HnQ A S1) as Hn.
    set (lo := bv_unsigned A). set (hi := lo + bv_unsigned n).
    assert (Hlh : lo <= hi) by (unfold hi; pose proof (u64_range n); lia).
    assert (Hlo : lo mod page_size = 0) by exact S2.
    assert (Hhi : hi mod page_size = 0) by (unfold hi; rewrite <- Zplus_mod_idemp_l, Hlo, Z.add_0_l, Hn; exact HnZal).
    set (hg := mkVmMapsFull (vm_reserved h) (vm_maps h) ((A, n) :: maps_subtract (vm_noaccess h) lo hi)
                 (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)).
    set (mo1 := with_mmap_replacement FL A n (with_vmmaps hg mo)).
    assert (Emo1 : mo1 = vm_forget_range lo hi (with_vmmaps hg mo)).
    { subst mo1. unfold with_mmap_replacement, with_mmap_backing. rewrite Hnr. reflexivity. }
    set (P' := cut_pages lo hi P).
    assert (EP : allowL (LNode (NMmap addr len prot flags)) (mkEffectU A [] [] [(A, n)] [] []) P = P').
    { cbn [allowL]. change (Z_to_bv 64 prot) with PR. change (Z_to_bv 64 flags) with FL. rewrite Hfx.
      unfold addrZ. fold A lo. change (lenZ len) with nZ. rewrite <- Hn. reflexivity. }
    assert (EH : hideL (LNode (NMmap addr len prot flags)) (mkEffectU A [] [] [(A, n)] [] []) H = unhide_range lo hi H).
    { cbn [hideL]. unfold ret_alignedb. cbn [eff_ret].
      rewrite (proj2 (Z.eqb_eq _ _) S2).
      change (lenZ len) with nZ.
      rewrite <- Hn.
      reflexivity. }
    assert (HRE : nmmap_refusable (perase P mo) len prot flags = false).
    { unfold nmmap_refusable. change (Z_to_bv 64 prot) with PR. change (Z_to_bv 64 flags) with FL. rewrite Hm, Hna. reflexivity. }
    pose proof (fun o => mmap_fixed_noaccess_outcome_raw A (Z_to_bv 64 len) PR FL (Z_to_bv 64 (-1)) (Z_to_bv 64 0)
                  (sys_input segs msF (Z_to_bv 64 222)) mo o Hoff Hanon Hlen Hm Hna Hfx S1 S2 S3 S4 S5) as RAW.
    cbv zeta in RAW.
    assert (OUT : forall eff mo' evs,
       (syscall_spec (sys_input segs msF (Z_to_bv 64 222)) mo (Ok eff mo' evs)
        /\ ~ spurious_refusal_cfg ACFG (sys_input segs msF (Z_to_bv 64 222)) mo eff)
       <-> Ok eff mo' evs = Ok (mkEffectU A [] [] [(A, n)] [] []) mo1 []).
    { intros eff mo' evs.
      rewrite D, <- (mmap_forced_iff_ns _ _ _ _ _ _ _ _ eff mo' evs (sysno_of segs msF _ 222 ltac:(lia) eq_refl) D).
      rewrite (mmap_fixed_noaccess_outcome A (Z_to_bv 64 len) PR FL (Z_to_bv 64 (-1)) (Z_to_bv 64 0) _ mo (Ok eff mo' evs)
                 Hoff Hanon Hlen Hm Hna Hfx S1 S2 S3 S4 S5).
      fold n h. split.
      - intros [HE|[E|(e & He & _)]]; [exfalso; exact (mmap_err_out_when_false _ _ HE)| exact E| exfalso; exact (mmap_destructive_errnos_In e He)].
      - intros E. right; left. exact E. }
    assert (Eper : perase P' mo1 = with_mmap_replacement FL A n
              (with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps (perase P mo))) (vm_maps (m_vmmaps (perase P mo)))
                 ((A, n) :: maps_subtract (vm_noaccess (m_vmmaps (perase P mo))) (bv_unsigned A) (bv_unsigned A + bv_unsigned n))
                 (vm_start_brk (m_vmmaps (perase P mo))) (vm_brk (m_vmmaps (perase P mo))) (vm_limit (m_vmmaps (perase P mo)))
                 (vm_mmap_base (m_vmmaps (perase P mo))) (vm_init_sp (m_vmmaps (perase P mo)))) (perase P mo))).
    { rewrite m_vmmaps_perase. subst P' mo1. unfold lo, hi. rewrite perase_with_mmap_replacement. reflexivity. }
    split.
    + exact Hsvc.
    + intros eff mo' evs Hs0 Hns0. pose proof (proj1 (OUT _ _ _) (conj Hs0 Hns0)) as Hs. clear Hs0 Hns0.
    apply Ok_inj in Hs as (-> & -> & ->). rewrite EP, EH.
      split. { cbn [nstepL nstep]. split; [reflexivity|]. right; right; right. split; [exact Hm|]. split; [exact Hna|]. split; [exact Hfx|]. left. split; [reflexivity|]. exact Eper. }
      split. { rewrite Emo1. unfold vm_forget_range. rewrite m_halted_wvb, m_halted_with_vmmaps. exact Hh. }
      split.
      { pose proof HI as [N1 N2 N3 N4 N5]. rewrite Emo1. subst P'. constructor; model_proj.
        * apply NoDup_filter. exact N1.
        * intros p Hp. apply filter_In in Hp as [Hp _]. exact (N2 p Hp).
        * intros p Hp. apply filter_In in Hp as [Hp Hout]. pose proof (N2 p Hp) as Hpal.
          apply (proj2 (page_allowedb_ivl _ p Hpal (cut_pages_aligned _ _ _ HA))). apply cut_pages_in.
          split; [exact (proj1 (page_allowedb_ivl _ p Hpal HA) (N3 p Hp))|].
          unfold page_outside_range in Hout. apply negb_true_iff in Hout. apply andb_false_iff in Hout as [Hout|Hout];
            [left; apply Z.leb_gt in Hout| right; apply Z.ltb_ge in Hout]; lia.
        * intros p Hp. apply filter_In in Hp as [Hp Hout]. pose proof (N2 p Hp) as Hpal.
          unfold page_outside_range in Hout. apply negb_true_iff in Hout.
          rewrite page_in_ranges_subtract_out; [exact (N4 p Hp)| exact Wl| exact Hlh|].
          apply andb_false_iff in Hout as [Hout|Hout]; [apply Z.leb_gt in Hout| apply Z.ltb_ge in Hout].
          -- left. destruct (aligned_in_or_out (bv_unsigned p) lo hi Hpal Hlo Hhi); unfold page_size; lia.
          -- right. exact Hout.
        * cbn [vm_limit]. rewrite A_bytes_ivl in N5 |- *.
          pose proof (eager_used_guard_le mo A n HW) as LE. cbv zeta in LE. fold h lo in LE. fold hi in LE. fold hg in LE.
          change (vm_limit hg) with (vm_limit (m_vmmaps mo)).
          pose proof (cut_pages_length lo hi P) as CL. unfold page_size in *. nia. }
      split.
      { intros w Hpl Hw. rewrite Emo1 in Hpl. revert Hpl. model_proj. intros Hpl.
        pose proof (page_base_facts w) as (B1 & B2 & B3).
        assert (Hout : bv_unsigned (page_base w) + page_size <= lo \/ hi <= bv_unsigned (page_base w)).
        { destruct (aligned_in_or_out (bv_unsigned (page_base w)) lo hi B3 Hlo Hhi) as [Hinr|Houtr]; [| unfold page_size; lia].
          exfalso. rewrite (page_in_ranges_subtract_in (page_base w) _ lo hi Wl ltac:(lia)) in Hpl. discriminate. }
        rewrite (page_in_ranges_subtract_out _ _ _ _ Wl Hlh Hout) in Hpl.
        unfold unhide_range in Hw. apply andb_false_iff in Hw as [Hw|Hw].
        * pose proof (HC w Hpl Hw) as Hal0. apply (proj2 (page_allowedb_ivl _ _ B3 (cut_pages_aligned _ _ _ HA))).
          apply cut_pages_in. split; [exact (proj1 (page_allowedb_ivl _ _ B3 HA) Hal0)|]. unfold page_size in *. lia.
        * exfalso. apply negb_false_iff in Hw. unfold in_rangeb in Hw. apply andb_prop in Hw as [W1 W2].
          apply Z.leb_le in W1. apply Z.ltb_lt in W2.
          destruct (page_of_byte_in_aligned w lo hi Hlo Hhi ltac:(lia)). unfold page_size in *. lia. }
      split. { apply cut_pages_aligned. exact HA. }
      split.
      { apply minvL_perase. rewrite Emo1. split; [| split; [| split]].
        * rewrite strip_vm_forget_vmmaps. apply minv_strip_vmmaps; [reflexivity| exact Hh| exact HM0].
        * intros r x Hr Hx. revert Hr. model_proj. cbn [vm_maps]. intros Hr.
          destruct (maps_subtract_sem (m_vm_lazy mo) lo hi Wl Hlh) as (_ & _ & Cv).
          assert (Cx : covered (maps_subtract (m_vm_lazy mo) lo hi) x = true).
          { unfold covered. apply existsb_exists. exists r. split; [exact Hr|]. unfold in_iv, in_rng, B, S.
            apply andb_true_intro. split; [apply Z.leb_le| apply Z.ltb_lt]; lia. }
          rewrite Cv in Cx. apply andb_prop in Cx as [C1 _].
          unfold covered in C1. apply existsb_exists in C1 as (r0 & Hr0 & Hx0). unfold in_iv, in_rng, B, S in Hx0.
          apply andb_prop in Hx0 as [X1 X2]. apply Z.leb_le in X1. apply Z.ltb_lt in X2.
          exact (HL r0 x Hr0 ltac:(lia)).
        * apply model_ivs_wf_vm_forget_range; [exact Hlh|]. apply model_ivs_wf_with_vmmaps; [exact HW| exact Wm| | reflexivity]. cbn [vm_noaccess].
          apply ivs_wf_cons; [| apply maps_subtract_wf; [exact Wn| exact Hlh]].
          unfold iv_wf, B, S. cbn [fst snd]. pose proof (alloc_top_lt h). unfold two_pow_64 in *. fold lo in S1. lia.
        * model_proj. cbn [vm_maps]. exact HS. }
      split. { cbn. apply AsanAcct.ranges_avoid_nil. }
      split. { reflexivity. }
      split. { unfold lo, hi. apply hzero_unhide_zu; [right; split; reflexivity| exact HZ]. }
      split. { apply hide_ok_mono. intros a Ha. assert (Hb : unhide_range lo hi H a = true) by (rewrite <- EH; exact Ha). unfold unhide_range in Hb. apply andb_prop in Hb as [Hb _]. exact Hb. }
      intros x0 Hx0 Hu0. unfold lo, hi in Hu0. cbn [eff_zeros eff_unmaps]. eapply cov_unhide_zu; [right; split; reflexivity| exact Hx0| exact Hu0].
    + intros Hs. apply D, RAW in Hs. destruct Hs as [(e & _ & Hs)|[Hs|(e & _ & Hs)]]; discriminate.
    + intros eff moE' evs Hst. cbn [nstepL nstep] in Hst.
      destruct Hst as (-> & [(e & He & _)|[(Hm' & _)|[(_ & Hna' & _)|(_ & _ & _ & [(Hs & ->)|(e & He & _)])]]]).
      * rewrite HRE in He. destruct He.
      * exfalso. change (Z_to_bv 64 prot) with PR in Hm'. change (Z_to_bv 64 flags) with FL in Hm'. congruence.
      * exfalso. change (Z_to_bv 64 prot) with PR in Hna'. change (Z_to_bv 64 flags) with FL in Hna'. congruence.
      * eexists (mkEffectU A [] [] [(A, n)] [] []), mo1. split; [rewrite Hs; reflexivity|]. split; [apply (proj2 (OUT _ _ _)); reflexivity|].
        change (allowL (LNode (NMmap addr len prot flags)) eff P) with (allowL (LNode (NMmap addr len prot flags)) (mkEffectU A [] [] [(A, n)] [] []) P).
        rewrite EP. exact Eper.
      * exfalso. exact (mmap_destructive_errnos_In e He).
    + eexists (mkEffectU A [] [] [(A, n)] [] []), _, []. cbn [nstepL nstep]. split; [reflexivity|]. right; right; right.
      split; [exact Hm|]. split; [exact Hna|]. split; [exact Hfx|]. left. split; [reflexivity|]. exact Eper.
    + intros eff' mo1' evs' Hs. apply D, RAW in Hs.
      destruct Hs as [(e & _ & Hs)|[Hs|(e & _ & Hs)]]; apply Ok_inj in Hs as (_ & -> & _).
      * exact Hh.
      * rewrite m_halted_with_mmap_replacement, m_halted_with_vmmaps. exact Hh.
      * rewrite m_halted_with_mmap_destroyed. exact Hh.
Qed.

#[using="HF HZ Hh HI HC HA"] Lemma mmap_heap_factsL : forall len off,
  at_nodeL segs (LMmapHeap len off) (restrict H msF) -> nsafeL (LMmapHeap len off) (perase P mo) ->
  factsL_ns segs (LMmapHeap len off) H P msF mo (Z_to_bv 64 222).
Proof.
  intros len off HatR Hsafe.
  destruct HatR as ((Hsvc & Ha0 & Ha1 & Ha2 & Ha3 & Ha4 & Ha5 & Hlen) & Hoff & Hoffhi).
  unfold areg in Ha0, Ha1, Ha2, Ha3, Ha4, Ha5. cbn [AsanAcct.restrict ms_regs ms_svc_pending] in Hsvc, Ha0, Ha1, Ha2, Ha3, Ha4, Ha5.
  fold (areg msF 10) in Ha0. fold (areg msF 11) in Ha1. fold (areg msF 12) in Ha2. fold (areg msF 13) in Ha3.
  fold (areg msF 14) in Ha4. fold (areg msF 15) in Ha5.
  cbn [nsafeL] in Hsafe. unfold lz_room in Hsafe. rewrite m_vmmaps_perase in Hsafe.
  pose proof HMLm as (HM0 & HL & HW & HS). pose proof HW as (Wm & Wn & Wl & Wsp).
  pose proof (minv_alloc_top _ HM0) as [_ Htop]. rewrite m_vmmaps_strip_vm in Htop.
  destruct null_flag_facts as [(Fanon & Fmod & Fnr) _].
  set (FL := Z_to_bv 64 MAPF_ANON_PRIVATE) in *. set (PR := Z_to_bv 64 PROT_RW) in *.
  set (nZ := lenZ len) in *. set (n := lenW len) in *. set (h := m_vmmaps mo) in *.
  pose proof (lenZ_nonneg len) as Hn0. fold nZ in Hn0.
  assert (HnZal : nZ mod page_size = 0) by (subst nZ; apply lenZ_aligned).
  assert (Hoffal : mmap_off_aligned_b (Z_to_bv 64 0) = true) by reflexivity.
  assert (D : forall o, syscall_spec (sys_input segs msF (Z_to_bv 64 222)) mo o <->
     mmap_spec (Z_to_bv 64 0) (Z_to_bv 64 len) PR FL (Z_to_bv 64 (-1)) (Z_to_bv 64 0)
               (sys_input segs msF (Z_to_bv 64 222)) mo o).
  { intros o. rewrite (syscall_spec_222 _ _ _ (sysno_of segs msF _ 222 ltac:(lia) eq_refl)).
    rewrite in_a0_si, in_a1_si, in_a2_si, in_a3_si, in_a4_si, in_a5_si, Ha0, Ha1, Ha2, Ha3, Ha4, Ha5. reflexivity. }

  assert (Hpm : mmap_noreserve_backed_ok FL (perase P mo) nZ = true).
  { unfold mmap_noreserve_backed_ok. rewrite Fnr, m_vmmaps_perase. apply Z.leb_le.
    fold h. assert (0 <= nZ / 8) by (apply Z.div_pos; lia). unfold page_size in *. lia. }
  assert (Hbk : mmap_noreserve_backed_ok FL mo nZ = true).
  { unfold mmap_noreserve_backed_ok in *. rewrite Fnr in Hpm |- *. apply Z.leb_le. apply Z.leb_le in Hpm.
    rewrite m_vmmaps_perase in Hpm. pose proof (vm_backing_used_perase_ge P mo HI HA). lia. }
  assert (HRr : mmap_grant_refusable FL mo nZ = negb (vm_gap_available h nZ)).
  { unfold mmap_grant_refusable. rewrite Hbk. reflexivity. }
  assert (HnQ : forall a : word, bv_unsigned a + nZ <= alloc_top h -> bv_unsigned n = nZ).
  { intros a Ha. subst n. unfold lenW. fold nZ. apply u64_lit. pose proof (alloc_top_lt h). pose proof (u64_range a). unfold two_pow_64 in *. lia. }
  pose proof (fun o => mmap_rw_outcome_raw (Z_to_bv 64 0) _ PR FL (Z_to_bv 64 (-1)) _ (sys_input segs msF (Z_to_bv 64 222)) mo o Hoffal Fanon Hlen Fmod) as RAW.
  cbv zeta in RAW.
  assert (OUT := fun eff mo' evs (Hs0 : syscall_spec (sys_input segs msF (Z_to_bv 64 222)) mo (Ok eff mo' evs))
                    (Hns0 : ~ spurious_refusal_cfg ACFG (sys_input segs msF (Z_to_bv 64 222)) mo eff) =>
    proj1 (mmap_rw_outcome (Z_to_bv 64 0) _ PR FL (Z_to_bv 64 (-1)) _ (sys_input segs msF (Z_to_bv 64 222)) mo (Ok eff mo' evs) Hoffal Fanon Hlen Fmod)
      (conj (proj1 (D _) Hs0) (proj2 (mmap_forced_iff_ns _ _ _ _ _ _ _ _ eff mo' evs (sysno_of segs msF _ 222 ltac:(lia) eq_refl) D) Hns0))).
  assert (OUT' := fun eff mo' evs H0 =>
    let HH0 := proj2 (mmap_rw_outcome (Z_to_bv 64 0) _ PR FL (Z_to_bv 64 (-1)) _ (sys_input segs msF (Z_to_bv 64 222)) mo (Ok eff mo' evs) Hoffal Fanon Hlen Fmod) H0 in
    conj (proj2 (D _) (proj1 HH0)) (proj1 (mmap_forced_iff_ns _ _ _ _ _ _ _ _ eff mo' evs (sysno_of segs msF _ 222 ltac:(lia) eq_refl) D) (proj2 HH0))).
  cbv zeta in OUT, OUT'. unfold mmap_err_out_when in OUT, OUT'. change (page_round_up_Z (bv_unsigned (Z_to_bv 64 len))) with nZ in OUT, OUT'.
  fold n h in OUT, OUT'. rewrite HRr in OUT, OUT'.

  assert (Herr_al : ret_alignedb (efferr ENOMEM) = false) by (vm_compute; reflexivity).
  assert (ERRF : forall c e, In e (mmap_errnos_when c) ->
     m_halted mo = None
     /\ MInv (ivl (allowL (LMmapHeap len off) (efferr e) P)) mo
     /\ lazy_cover (hideL (LMmapHeap len off) (efferr e) H) (m_vm_lazy mo) (ivl (allowL (LMmapHeap len off) (efferr e) P))
     /\ P_aligned (allowL (LMmapHeap len off) (efferr e) P)
     /\ minvL (perase (allowL (LMmapHeap len off) (efferr e) P) mo)
     /\ AsanAcct.ranges_avoid H (syscall_effect_accesses (efferr e))
     /\ eff_copies (efferr e) = []
     /\ hzero (hideL (LMmapHeap len off) (efferr e) H) (nret msF (efferr e))
     /\ hide_ok segs (LMmapHeap len off) (efferr e) H (syscall_effect_accesses (efferr e))
     /\ (forall x0, H x0 = true -> hideL (LMmapHeap len off) (efferr e) H x0 = false ->
           zb x0 = true \/ zeros_cover (eff_zeros (efferr e)) x0 = true \/ zeros_cover (eff_unmaps (efferr e)) x0 = true)).
  { intros c e He. pose proof (proj2 (mmap_errnos_when_In c e He)) as ->.
    apply (fdkind_frame segs H P msF mo HF); try reflexivity.
    - exact HM0.
    - cbn. apply AsanAcct.ranges_avoid_nil.
    - apply hzero_nret_nomem. exact HZ. }

  assert (GRANTH : forall a : word,
     (bv_unsigned a mod page_size = 0) -> 0 < bv_unsigned a -> bv_unsigned a + nZ <= alloc_top h ->
     region_free (vm_reserved h ++ vm_maps h) a n = true ->
     let eff := mkEffect a [] [(a, n)] in
     let mo1 := with_vmmaps (grant_maps h a n) mo in
     m_halted mo1 = None
     /\ MInv (ivl (allowL (LMmapHeap len off) eff P)) mo1
     /\ lazy_cover (hideL (LMmapHeap len off) eff H) (m_vm_lazy mo1) (ivl (allowL (LMmapHeap len off) eff P))
     /\ P_aligned (allowL (LMmapHeap len off) eff P)
     /\ minvL (perase (allowL (LMmapHeap len off) eff P) mo1)
     /\ AsanAcct.ranges_avoid H (syscall_effect_accesses eff)
     /\ eff_copies eff = []
     /\ hzero (hideL (LMmapHeap len off) eff H) (nret msF eff)
     /\ hide_ok segs (LMmapHeap len off) eff H (syscall_effect_accesses eff)
     /\ (forall x0, H x0 = true -> hideL (LMmapHeap len off) eff H x0 = false ->
           zb x0 = true \/ zeros_cover (eff_zeros eff) x0 = true \/ zeros_cover (eff_unmaps eff) x0 = true)).
  { intros a Q1 Q2 Q3 Q4. cbv zeta. pose proof (HnQ a Q3) as Hn. pose proof (u64_range a) as Ra.
    set (wlo := shw_lo off (bv_unsigned a)). set (whi := shw_hi off (bv_unsigned a) nZ).
    destruct (shw_bounds off (bv_unsigned a) nZ ltac:(lia) ltac:(lia) Hn0) as (W1 & W2 & W3 & W4 & W5 & W6). fold wlo whi in W1, W2, W3, W4, W5, W6.
    assert (W7 : whi <= 2 ^ 64).
    { pose proof (alloc_top_lt h). assert (X : (bv_unsigned a + nZ) / 8 < 2 ^ 61) by (apply Z.div_lt_upper_bound; unfold two_pow_64 in *; lia).
      unfold two_pow_64, page_size in *. lia. }
    assert (EH : hideL (LMmapHeap len off) (mkEffect a [] [(a, n)]) H
                 = unhide_zb wlo whi (unhide_range (bv_unsigned a) (bv_unsigned a + bv_unsigned n) H)).
    { cbn [hideL]. unfold ret_alignedb. cbn [eff_ret]. rewrite (proj2 (Z.eqb_eq _ _) Q1). fold nZ wlo whi. rewrite Hn. reflexivity. }
    assert (EP : allowL (LMmapHeap len off) (mkEffect a [] [(a, n)]) P = pages_of wlo whi ++ P).
    { cbn [allowL]. unfold ret_alignedb. cbn [eff_ret]. rewrite (proj2 (Z.eqb_eq _ _) Q1). reflexivity. }
    rewrite EH, EP.
    assert (Hwf_an : iv_wf (a, n)) by (unfold iv_wf, B, S; cbn [fst snd]; pose proof (alloc_top_lt h); unfold two_pow_64 in *; lia).
    assert (HWal : P_aligned (pages_of wlo whi ++ P)).
    { apply P_aligned_app; [apply pages_of_aligned; [exact W1| exact W3| exact W7]| exact HA]. }
    split. { rewrite m_halted_with_vmmaps. exact Hh. }
    split.
    { pose proof HI as [N1 N2 N3 N4 N5]. constructor.
      + exact N1.
      + exact N2.
      + intros p Hp. apply (proj2 (page_allowedb_ivl _ p (N2 p Hp) HWal)). apply in_app_iff. right.
        exact (proj1 (page_allowedb_ivl _ p (N2 p Hp) HA) (N3 p Hp)).
      + exact N4.
      + change (vm_limit (m_vmmaps (with_vmmaps (grant_maps h a n) mo))) with (vm_limit h).
        rewrite A_bytes_ivl, length_app, Nat2Z.inj_add, Z.mul_add_distr_r, (pages_of_length wlo whi W1 W2 W4).
        rewrite A_bytes_ivl in N5.
        pose proof (eager_used_grant_rw_le mo a n Wm Hwf_an) as LE. fold h in LE. rewrite Hn in LE.
        rewrite vm_backing_used_perase in Hsafe. fold h in Hsafe. unfold page_size in *. lia. }
    split.
    { change (m_vm_lazy (with_vmmaps (grant_maps h a n) mo)) with (m_vm_lazy mo).
      intros w Hpl Hw. pose proof (page_base_facts w) as (B1 & B2 & B3).
      unfold unhide_zb, unhide_range in Hw. apply andb_false_iff in Hw as [Hw|Hw].
      * apply andb_false_iff in Hw as [Hw|Hw].
        -- apply (proj2 (page_allowedb_ivl _ _ B3 HWal)). apply in_app_iff. right.
           exact (proj1 (page_allowedb_ivl _ _ B3 HA) (HC w Hpl Hw)).
        -- exfalso. apply negb_false_iff in Hw. unfold in_rangeb in Hw. apply andb_prop in Hw as [X1 X2]. apply Z.leb_le in X1. apply Z.ltb_lt in X2.
           rewrite (grant_lazy_free a n w HL Q4 Q1 ltac:(rewrite Hn; exact HnZal) ltac:(lia)) in Hpl. discriminate.
      * apply negb_false_iff in Hw. apply andb_prop in Hw as [Hw _]. unfold in_rangeb in Hw. apply andb_prop in Hw as [X1 X2]. apply Z.leb_le in X1. apply Z.ltb_lt in X2.
        apply (proj2 (page_allowedb_ivl _ _ B3 HWal)). apply in_app_iff. left.
        apply page_base_in_pages_of; [exact W1| exact W2| exact W3| exact W7| lia]. }
    split. { exact HWal. }
    split.
    { apply minvL_perase. split; [| split; [| split]].
      + rewrite strip_vm_with_vmmaps. apply minv_strip_vmmaps; [reflexivity| exact Hh| exact HM0].
      + intros r x Hr Hx. change (covered ((a, n) :: vm_maps h) x = true). change (m_vm_lazy (with_vmmaps (grant_maps h a n) mo)) with (m_vm_lazy mo) in Hr.
        unfold covered. cbn [existsb]. apply orb_true_iff. right. exact (HL r x Hr Hx).
      + apply model_ivs_wf_with_vmmaps; [exact HW| cbn [vm_maps grant_maps]; apply ivs_wf_cons; [exact Hwf_an| exact Wm]| exact Wn| reflexivity].
      + change (seps ((a, n) :: vm_maps h)). apply seps_cons_free; [| exact HS].
        eapply Decode.region_free_incl; [| exact Q4]. intros e0 He0. apply in_app_iff. right. exact He0. }
    split. { cbn. apply AsanAcct.ranges_avoid_nil. }
    split. { reflexivity. }
    split. { eapply hzero_subset; [| apply hzero_unhide_zu; [left; split; reflexivity| exact HZ]].
             intros x Hx. unfold unhide_zb in Hx. apply andb_prop in Hx as [Hx _]. exact Hx. }
    split. { apply hide_ok_mono. intros x Hx. try rewrite EH in Hx. cbn [hideL] in Hx. unfold unhide_zb, unhide_range in Hx. apply andb_prop in Hx as [Hx _]. apply andb_prop in Hx as [Hx _]. exact Hx. }
    intros x0 Hx0 Hu0. cbn [eff_zeros eff_unmaps]. eapply cov_unhide_win; [exact Hx0| exact Hu0]. }
  split.
  - exact Hsvc.
  - intros eff mo' evs Hs0 Hns0. pose proof (OUT _ _ _ Hs0 Hns0) as Hs. clear Hs0 Hns0. destruct Hs as [(e & He & Hs)|(a & (Q1 & Q2 & Q3 & Q4 & Q5) & Hs)];
      apply Ok_inj in Hs as (-> & -> & ->).
    + split; [| exact (ERRF _ e He)].
      pose proof (proj2 (mmap_errnos_when_In _ e He)) as ->.
      cbn [nstepL allowL]. replace (ret_alignedb (mkEffect (errno_ret ENOMEM) [] [])) with false by (symmetry; exact Herr_al).
      split; [reflexivity|]. left. exists ENOMEM. rewrite m_vmmaps_perase. fold nZ h.
      repeat split; auto.
    + unfold with_mmap_backing. rewrite Fnr. split; [| exact (GRANTH a Q1 Q2 Q3 Q4)].
      cbn [nstepL]. split; [reflexivity|]. right. exists a.
      assert (EP : allowL (LMmapHeap len off) (mkEffect a [] [(a, n)]) P = pages_of (shw_lo off (bv_unsigned a)) (shw_hi off (bv_unsigned a) nZ) ++ P).
      { cbn [allowL]. unfold ret_alignedb. cbn [eff_ret]. rewrite (proj2 (Z.eqb_eq _ _) Q1). reflexivity. }
      change (Z_to_bv 64 nZ) with n in *.
      rewrite EP. split.
      { unfold mmap_placed. rewrite m_vmmaps_perase. change (page_round_up_Z (bv_unsigned (Z_to_bv 64 len))) with nZ. change (Z_to_bv 64 nZ) with n. fold h. repeat split; try assumption. lia. }
      split; [reflexivity|]. unfold lmheap_post. rewrite m_vmmaps_perase. change (lenZ len) with nZ. change (lenW len) with n. fold h. apply perase_app_with_vmmaps.
  - intros Hs. apply D, RAW in Hs. destruct Hs as [(e & _ & Hs)|(a & _ & Hs)]; discriminate.
  - intros eff moE' evs Hst. cbn [nstepL] in Hst. destruct Hst as [-> [(e & He & Hs & ->)|(a & (Q1 & Q2 & Q3 & Q4 & Q6) & Hs & ->)]].
    + rewrite m_vmmaps_perase in He. change (lenZ len) with nZ in He. fold h in He. pose proof (proj2 (mmap_errnos_when_In _ e He)) as ->.
      eexists (efferr ENOMEM), mo. split; [rewrite Hs; reflexivity|]. split; [apply OUT'; left; exists ENOMEM; split; [exact He|reflexivity]|].
      rewrite (allowL_strip (LMmapHeap len off) (efferr ENOMEM) eff P) by (rewrite Hs; reflexivity).
      cbn [allowL]. rewrite Herr_al. reflexivity.
    + rewrite m_vmmaps_perase in Q4, Q6. change (page_round_up_Z (bv_unsigned (Z_to_bv 64 len))) with nZ in Q3, Q4, Q6.
      change (Z_to_bv 64 nZ) with n in Q4. fold h in Q4, Q6.
      eexists (mkEffect a [] [(a, n)]), _. split; [rewrite Hs; reflexivity|].
      split; [apply OUT'; right; exists a; split; [repeat split; [exact Q1| exact Q2| exact Q6| exact Q4| exact Hbk]|reflexivity]|].
      rewrite (allowL_strip (LMmapHeap len off) (mkEffect a [] [(a, n)]) eff P) by (rewrite Hs; reflexivity).
      cbn [allowL]. unfold ret_alignedb. cbn [eff_ret]. rewrite (proj2 (Z.eqb_eq _ _) Q1).
      unfold with_mmap_backing. rewrite Fnr. unfold lmheap_post. rewrite m_vmmaps_perase. change (lenZ len) with nZ. change (lenW len) with n. fold h.
      symmetry. apply perase_app_with_vmmaps.
  - destruct (vm_gap_available h nZ) eqn:HG.
    + destruct (mmap_grant_unforced FL mo nZ ltac:(rewrite HRr; reflexivity)) as (HB & a & Q1 & Q2 & Q3 & Q4).
      eexists (mkEffect a [] [(a, n)]), _, []. cbn [nstepL]. split; [reflexivity|]. right.
      exists a. split.
      { unfold mmap_placed. rewrite m_vmmaps_perase. change (page_round_up_Z (bv_unsigned (Z_to_bv 64 len))) with nZ. change (Z_to_bv 64 nZ) with n. fold h.
        repeat split; try assumption. all: fold h in Q3, Q4; try exact Q4; lia. }
      split; reflexivity.
    + exists (efferr ENOMEM), (perase P mo), []. cbn [nstepL]. split; [reflexivity|]. left. exists ENOMEM.
      rewrite m_vmmaps_perase. change (lenZ len) with nZ. fold h. rewrite HG. cbn [negb]. split; [exact mmap_errnos_when_true|]. split; reflexivity.
  - intros eff' mo1' evs' Hs. apply D, RAW in Hs.
    destruct Hs as [(e & _ & Hs)|(a & _ & Hs)]; apply Ok_inj in Hs as (_ & -> & _); [exact Hh|].
    rewrite m_halted_with_mmap_backing, m_halted_with_vmmaps. exact Hh.
Qed.

#[using="HF HZ Hh HI HC HA"] Lemma mmap_nr_factsL : forall len,
  at_nodeL segs (LMmapNR len) (restrict H msF) -> nsafeL (LMmapNR len) (perase P mo) ->
  factsL_ns segs (LMmapNR len) H P msF mo (Z_to_bv 64 222).
Proof.
  intros len HatR Hsafe.
  destruct HatR as (Hsvc & Ha0 & Ha1 & Ha2 & Ha3 & Ha4 & Ha5 & Hlen).
  unfold areg in Ha0, Ha1, Ha2, Ha3, Ha4, Ha5. cbn [AsanAcct.restrict ms_regs ms_svc_pending] in Hsvc, Ha0, Ha1, Ha2, Ha3, Ha4, Ha5.
  fold (areg msF 10) in Ha0. fold (areg msF 11) in Ha1. fold (areg msF 12) in Ha2. fold (areg msF 13) in Ha3.
  fold (areg msF 14) in Ha4. fold (areg msF 15) in Ha5.
  cbn [nsafeL] in Hsafe. unfold lz_room in Hsafe. rewrite m_vmmaps_perase in Hsafe.
  pose proof HMLm as (HM0 & HL & HW & HS). pose proof HW as (Wm & Wn & Wl & Wsp).
  pose proof (minv_alloc_top _ HM0) as [_ Htop]. rewrite m_vmmaps_strip_vm in Htop.
  destruct null_flag_facts as [_ (Fanon & Fmod & Fnr)].
  set (FL := Z_to_bv 64 MAPF_NR) in *. set (PR := Z_to_bv 64 PROT_RW) in *.
  set (nZ := lenZ len) in *. set (n := lenW len) in *. set (h := m_vmmaps mo) in *.
  pose proof (lenZ_nonneg len) as Hn0. fold nZ in Hn0.
  assert (HnZal : nZ mod page_size = 0) by (subst nZ; apply lenZ_aligned).
  assert (Hnpos : 0 < nZ).
  { subst nZ. unfold lenZ, page_round_up_Z. pose proof (u64_range (Z_to_bv 64 len)) as R.
    assert (bv_unsigned (Z_to_bv 64 len) <> 0).
    { intros E. unfold w_is0 in Hlen. assert (EE : Z_to_bv 64 len = Z_to_bv 64 0) by (apply bv_eq; rewrite E; reflexivity).
      rewrite EE, bv_eqb_refl in Hlen. discriminate. }
    unfold page_size. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). nia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  assert (Hoffal : mmap_off_aligned_b (Z_to_bv 64 0) = true) by reflexivity.
  assert (D : forall o, syscall_spec (sys_input segs msF (Z_to_bv 64 222)) mo o <->
     mmap_spec (Z_to_bv 64 0) (Z_to_bv 64 len) PR FL (Z_to_bv 64 (-1)) (Z_to_bv 64 0)
               (sys_input segs msF (Z_to_bv 64 222)) mo o).
  { intros o. rewrite (syscall_spec_222 _ _ _ (sysno_of segs msF _ 222 ltac:(lia) eq_refl)).
    rewrite in_a0_si, in_a1_si, in_a2_si, in_a3_si, in_a4_si, in_a5_si, Ha0, Ha1, Ha2, Ha3, Ha4, Ha5. reflexivity. }
  assert (Hbk : forall m, mmap_noreserve_backed_ok FL m nZ = true).
  { intros m. unfold mmap_noreserve_backed_ok. rewrite Fnr. reflexivity. }
  assert (HRr : mmap_grant_refusable FL mo nZ = negb (vm_gap_available h nZ)).
  { unfold mmap_grant_refusable. rewrite Hbk. reflexivity. }
  assert (HnQ : forall a : word, bv_unsigned a + nZ <= alloc_top h -> bv_unsigned n = nZ).
  { intros a Ha. subst n. unfold lenW. fold nZ. apply u64_lit. pose proof (alloc_top_lt h). pose proof (u64_range a). unfold two_pow_64 in *. lia. }
  pose proof (fun o => mmap_rw_outcome_raw (Z_to_bv 64 0) _ PR FL (Z_to_bv 64 (-1)) _ (sys_input segs msF (Z_to_bv 64 222)) mo o Hoffal Fanon Hlen Fmod) as RAW.
  cbv zeta in RAW.
  assert (OUT := fun eff mo' evs (Hs0 : syscall_spec (sys_input segs msF (Z_to_bv 64 222)) mo (Ok eff mo' evs))
                    (Hns0 : ~ spurious_refusal_cfg ACFG (sys_input segs msF (Z_to_bv 64 222)) mo eff) =>
    proj1 (mmap_rw_outcome (Z_to_bv 64 0) _ PR FL (Z_to_bv 64 (-1)) _ (sys_input segs msF (Z_to_bv 64 222)) mo (Ok eff mo' evs) Hoffal Fanon Hlen Fmod)
      (conj (proj1 (D _) Hs0) (proj2 (mmap_forced_iff_ns _ _ _ _ _ _ _ _ eff mo' evs (sysno_of segs msF _ 222 ltac:(lia) eq_refl) D) Hns0))).
  assert (OUT' := fun eff mo' evs H0 =>
    let HH0 := proj2 (mmap_rw_outcome (Z_to_bv 64 0) _ PR FL (Z_to_bv 64 (-1)) _ (sys_input segs msF (Z_to_bv 64 222)) mo (Ok eff mo' evs) Hoffal Fanon Hlen Fmod) H0 in
    conj (proj2 (D _) (proj1 HH0)) (proj1 (mmap_forced_iff_ns _ _ _ _ _ _ _ _ eff mo' evs (sysno_of segs msF _ 222 ltac:(lia) eq_refl) D) (proj2 HH0))).
  cbv zeta in OUT, OUT'. unfold mmap_err_out_when in OUT, OUT'. change (page_round_up_Z (bv_unsigned (Z_to_bv 64 len))) with nZ in OUT, OUT'.
  change (Z_to_bv 64 nZ) with n in OUT, OUT'. fold h in OUT, OUT'. rewrite HRr in OUT, OUT'.
  assert (Herr_al : ret_alignedb (efferr ENOMEM) = false) by (vm_compute; reflexivity).
  assert (ERRF : forall c e, In e (mmap_errnos_when c) ->
     m_halted mo = None
     /\ MInv (ivl (allowL (LMmapNR len) (efferr e) P)) mo
     /\ lazy_cover (hideL (LMmapNR len) (efferr e) H) (m_vm_lazy mo) (ivl (allowL (LMmapNR len) (efferr e) P))
     /\ P_aligned (allowL (LMmapNR len) (efferr e) P)
     /\ minvL (perase (allowL (LMmapNR len) (efferr e) P) mo)
     /\ AsanAcct.ranges_avoid H (syscall_effect_accesses (efferr e))
     /\ eff_copies (efferr e) = []
     /\ hzero (hideL (LMmapNR len) (efferr e) H) (nret msF (efferr e))
     /\ hide_ok segs (LMmapNR len) (efferr e) H (syscall_effect_accesses (efferr e))
     /\ (forall x0, H x0 = true -> hideL (LMmapNR len) (efferr e) H x0 = false ->
           zb x0 = true \/ zeros_cover (eff_zeros (efferr e)) x0 = true \/ zeros_cover (eff_unmaps (efferr e)) x0 = true)).
  { intros c e He. pose proof (proj2 (mmap_errnos_when_In c e He)) as ->.
    apply (fdkind_frame segs H P msF mo HF); try reflexivity.
    - exact HM0.
    - cbn. apply AsanAcct.ranges_avoid_nil.
    - apply hzero_nret_nomem. exact HZ. }

  assert (GRANTR : forall a : word,
     (bv_unsigned a mod page_size = 0) -> 0 < bv_unsigned a -> bv_unsigned a + nZ <= alloc_top h ->
     region_free (vm_reserved h ++ vm_maps h) a n = true ->
     let eff := mkEffect a [] [(a, n)] in
     let mo1 := vm_add_lazy a n (with_vmmaps (grant_maps h a n) mo) in
     m_halted mo1 = None
     /\ MInv (ivl (allowL (LMmapNR len) eff P)) mo1
     /\ lazy_cover (hideL (LMmapNR len) eff H) (m_vm_lazy mo1) (ivl (allowL (LMmapNR len) eff P))
     /\ P_aligned (allowL (LMmapNR len) eff P)
     /\ minvL (perase (allowL (LMmapNR len) eff P) mo1)
     /\ AsanAcct.ranges_avoid H (syscall_effect_accesses eff)
     /\ eff_copies eff = []
     /\ hzero (hideL (LMmapNR len) eff H) (nret msF eff)
     /\ hide_ok segs (LMmapNR len) eff H (syscall_effect_accesses eff)
     /\ (forall x0, H x0 = true -> hideL (LMmapNR len) eff H x0 = false ->
           zb x0 = true \/ zeros_cover (eff_zeros eff) x0 = true \/ zeros_cover (eff_unmaps eff) x0 = true)).
  { intros a Q1 Q2 Q3 Q4. cbv zeta. pose proof (HnQ a Q3) as Hn. pose proof (u64_range a) as Ra.
    set (lo := bv_unsigned a). set (hi := lo + nZ).
    assert (Hhi : hi mod page_size = 0) by (unfold hi, lo; rewrite <- Zplus_mod_idemp_l, Q1, Z.add_0_l; exact HnZal).
    assert (Hhi64 : hi <= 2 ^ 64) by (pose proof (alloc_top_lt h); unfold hi, lo, two_pow_64 in *; lia).
    assert (Hwf_an : iv_wf (a, n)) by (unfold iv_wf, B, S; cbn [fst snd]; pose proof (alloc_top_lt h); unfold two_pow_64 in *; lia).
    assert (Eli : lazy_interior a n = [(a, n)]).
    { apply (lazy_interior_aligned a n Q1 ltac:(rewrite Hn; exact HnZal) ltac:(rewrite Hn; lia)). unfold iv_wf, B, S in Hwf_an. exact Hwf_an. }
    assert (EH : hideL (LMmapNR len) (mkEffect a [] [(a, n)]) H = unhide_range lo hi H).
    { cbn [hideL]. unfold ret_alignedb. cbn [eff_ret]. rewrite (proj2 (Z.eqb_eq _ _) Q1). reflexivity. }
    assert (EP : allowL (LMmapNR len) (mkEffect a [] [(a, n)]) P = pages_of lo hi ++ P).
    { cbn [allowL]. unfold ret_alignedb. cbn [eff_ret]. rewrite (proj2 (Z.eqb_eq _ _) Q1). reflexivity. }
    rewrite EH, EP.
    assert (HWal : P_aligned (pages_of lo hi ++ P)).
    { apply P_aligned_app; [apply pages_of_aligned; [exact Q1| lia| exact Hhi64]| exact HA]. }
    split. { unfold vm_add_lazy. rewrite m_halted_wvb, m_halted_with_vmmaps. exact Hh. }
    split.
    { pose proof HI as [N1 N2 N3 N4 N5]. unfold vm_add_lazy. constructor;
        rewrite ?AsanAcct.m_vm_materialized_wvb, ?AsanAcct.m_vm_lazy_wvb, ?AsanAcct.m_vmmaps_wvb; model_proj.
      + exact N1.
      + exact N2.
      + intros p Hp. apply (proj2 (page_allowedb_ivl _ p (N2 p Hp) HWal)). apply in_app_iff. right.
        exact (proj1 (page_allowedb_ivl _ p (N2 p Hp) HA) (N3 p Hp)).
      + intros p Hp. rewrite page_in_ranges_app. apply orb_true_iff. right. exact (N4 p Hp).
      + match goal with |- _ <= vm_limit ?X => change (vm_limit X) with (vm_limit h) end.
        rewrite A_bytes_ivl, length_app, Nat2Z.inj_add, Z.mul_add_distr_r, (pages_of_length lo hi Q1 Hhi ltac:(unfold hi; lia)).
        rewrite A_bytes_ivl in N5.
        pose proof (eager_used_grant_nr_le mo a n Wm Hwf_an Q1 ltac:(rewrite Hn; exact HnZal) ltac:(rewrite Hn; lia)) as LE.
        unfold vm_add_lazy in LE. fold h in LE.
        change (m_vm_lazy (with_vmmaps (grant_maps h a n) mo)) with (m_vm_lazy mo) in LE.
        change (m_vm_materialized (with_vmmaps (grant_maps h a n) mo)) with (m_vm_materialized mo) in LE.
        rewrite vm_backing_used_perase in Hsafe. fold h in Hsafe. unfold hi, lo. unfold page_size in *. lia. }
    split.
    { unfold vm_add_lazy. rewrite AsanAcct.m_vm_lazy_wvb. change (m_vm_lazy (with_vmmaps (grant_maps h a n) mo)) with (m_vm_lazy mo).
      rewrite Eli. cbn [app].
      intros w Hpl Hw. pose proof (page_base_facts w) as (B1 & B2 & B3).
      destruct (aligned_in_or_out (bv_unsigned (page_base w)) lo hi B3 Q1 Hhi) as [Hin|Hout].
      * apply (proj2 (page_allowedb_ivl _ _ B3 HWal)). apply in_app_iff. left.
        apply page_base_in_pages_of; [exact Q1| exact Hhi| lia| exact Hhi64| unfold page_size in *; lia].
      * rewrite page_in_ranges_cons_out in Hpl; [| rewrite Hn; unfold hi, page_size in *; lia| rewrite Hn; lia].
        unfold unhide_range in Hw. apply andb_false_iff in Hw as [Hw|Hw].
        -- apply (proj2 (page_allowedb_ivl _ _ B3 HWal)). apply in_app_iff. right.
           exact (proj1 (page_allowedb_ivl _ _ B3 HA) (HC w Hpl Hw)).
        -- exfalso. apply negb_false_iff in Hw. unfold in_rangeb in Hw. apply andb_prop in Hw as [X1 X2]. apply Z.leb_le in X1. apply Z.ltb_lt in X2.
           destruct (page_of_byte_in_aligned w lo hi Q1 Hhi ltac:(lia)). unfold page_size in *. lia. }
    split. { exact HWal. }
    split.
    { apply minvL_perase. split; [| split; [| split]].
      + rewrite strip_vm_vm_add_lazy, strip_vm_with_vmmaps. apply minv_strip_vmmaps; [reflexivity| exact Hh| exact HM0].
      + intros r x Hr Hx. unfold vm_add_lazy in Hr |- *. rewrite AsanAcct.m_vm_lazy_wvb in Hr. rewrite AsanAcct.m_vmmaps_wvb.
        change (m_vm_lazy (with_vmmaps (grant_maps h a n) mo)) with (m_vm_lazy mo) in Hr. rewrite Eli in Hr. cbn [app] in Hr.
        change (covered ((a, n) :: vm_maps h) x = true). destruct Hr as [<-|Hr].
        * cbn [fst snd] in Hx. unfold covered. cbn [existsb]. apply orb_true_iff. left.
          unfold in_iv, in_rng, B, S. cbn [fst snd]. apply andb_true_intro. split; [apply Z.leb_le| apply Z.ltb_lt]; lia.
        * unfold covered. cbn [existsb]. apply orb_true_iff. right. exact (HL r x Hr Hx).
      + apply model_ivs_wf_vm_add_lazy; [unfold iv_wf, B, S in Hwf_an; exact Hwf_an|].
        apply model_ivs_wf_with_vmmaps; [exact HW| cbn [vm_maps grant_maps]; apply ivs_wf_cons; [exact Hwf_an| exact Wm]| exact Wn| reflexivity].
      + unfold vm_add_lazy. rewrite AsanAcct.m_vmmaps_wvb. change (seps ((a, n) :: vm_maps h)). apply seps_cons_free; [| exact HS].
        eapply Decode.region_free_incl; [| exact Q4]. intros e0 He0. apply in_app_iff. right. exact He0. }
    split. { cbn. apply AsanAcct.ranges_avoid_nil. }
    split. { reflexivity. }
    split. { unfold lo, hi. rewrite <- Hn. apply hzero_unhide_zu; [left; split; reflexivity| exact HZ]. }
    split. { apply hide_ok_mono. intros x Hx. try rewrite EH in Hx. cbn [hideL] in Hx. unfold unhide_range in Hx. apply andb_prop in Hx as [Hx _]. exact Hx. }
    intros x0 Hx0 Hu0. unfold lo, hi in Hu0. rewrite <- Hn in Hu0. cbn [eff_zeros eff_unmaps]. eapply cov_unhide_zu; [left; split; reflexivity| exact Hx0| exact Hu0]. }
  split.
  - exact Hsvc.
  - intros eff mo' evs Hs0 Hns0. pose proof (OUT _ _ _ Hs0 Hns0) as Hs. clear Hs0 Hns0. destruct Hs as [(e & He & Hs)|(a & (Q1 & Q2 & Q3 & Q4 & Q5) & Hs)];
      apply Ok_inj in Hs as (-> & -> & ->).
    + split; [| exact (ERRF _ e He)].
      pose proof (proj2 (mmap_errnos_when_In _ e He)) as ->.
      cbn [nstepL allowL]. replace (ret_alignedb (mkEffect (errno_ret ENOMEM) [] [])) with false by (symmetry; exact Herr_al).
      split; [reflexivity|]. left. exists ENOMEM. rewrite m_vmmaps_perase. fold nZ h.
      repeat split; auto.
    + unfold with_mmap_backing. rewrite Fnr. split; [| exact (GRANTR a Q1 Q2 Q3 Q4)].
      cbn [nstepL]. split; [reflexivity|]. right. exists a.
      assert (EP : allowL (LMmapNR len) (mkEffect a [] [(a, n)]) P = pages_of (bv_unsigned a) (bv_unsigned a + nZ) ++ P).
      { cbn [allowL]. unfold ret_alignedb. cbn [eff_ret]. rewrite (proj2 (Z.eqb_eq _ _) Q1). reflexivity. }
      change (Z_to_bv 64 nZ) with n in *.
      rewrite EP. split.
      { unfold mmap_placed. rewrite m_vmmaps_perase. change (page_round_up_Z (bv_unsigned (Z_to_bv 64 len))) with nZ. change (Z_to_bv 64 nZ) with n. fold h. repeat split; try assumption. lia. }
      split; [reflexivity|]. unfold lmnr_post. rewrite m_vmmaps_perase. change (lenZ len) with nZ. change (lenW len) with n. fold h. apply perase_app_vm_add_lazy.
  - intros Hs. apply D, RAW in Hs. destruct Hs as [(e & _ & Hs)|(a & _ & Hs)]; discriminate.
  - intros eff moE' evs Hst. cbn [nstepL] in Hst. destruct Hst as [-> [(e & He & Hs & ->)|(a & (Q1 & Q2 & Q3 & Q4 & Q6) & Hs & ->)]].
    + rewrite m_vmmaps_perase in He. change (lenZ len) with nZ in He. fold h in He. pose proof (proj2 (mmap_errnos_when_In _ e He)) as ->.
      eexists (efferr ENOMEM), mo. split; [rewrite Hs; reflexivity|]. split; [apply OUT'; left; exists ENOMEM; split; [exact He|reflexivity]|].
      rewrite (allowL_strip (LMmapNR len) (efferr ENOMEM) eff P) by (rewrite Hs; reflexivity).
      cbn [allowL]. rewrite Herr_al. reflexivity.
    + rewrite m_vmmaps_perase in Q4, Q6. change (page_round_up_Z (bv_unsigned (Z_to_bv 64 len))) with nZ in Q3, Q4, Q6.
      change (Z_to_bv 64 nZ) with n in Q4. fold h in Q4, Q6.
      eexists (mkEffect a [] [(a, n)]), _. split; [rewrite Hs; reflexivity|].
      split; [apply OUT'; right; exists a; split; [repeat split; first [exact Q1| exact Q2| exact Q6| exact Q4| apply Hbk]|reflexivity]|].
      rewrite (allowL_strip (LMmapNR len) (mkEffect a [] [(a, n)]) eff P) by (rewrite Hs; reflexivity).
      cbn [allowL]. unfold ret_alignedb. cbn [eff_ret]. rewrite (proj2 (Z.eqb_eq _ _) Q1).
      unfold with_mmap_backing. rewrite Fnr. unfold lmnr_post. rewrite m_vmmaps_perase. change (lenZ len) with nZ. change (lenW len) with n. fold h.
      symmetry. apply perase_app_vm_add_lazy.
  - destruct (vm_gap_available h nZ) eqn:HG.
    + destruct (mmap_grant_unforced FL mo nZ ltac:(rewrite HRr; reflexivity)) as (HB & a & Q1 & Q2 & Q3 & Q4).
      eexists (mkEffect a [] [(a, n)]), _, []. cbn [nstepL]. split; [reflexivity|]. right.
      exists a. split.
      { unfold mmap_placed. rewrite m_vmmaps_perase. change (page_round_up_Z (bv_unsigned (Z_to_bv 64 len))) with nZ. change (Z_to_bv 64 nZ) with n. fold h.
        repeat split; try assumption. all: fold h in Q3, Q4; try exact Q4; lia. }
      split; reflexivity.
    + exists (efferr ENOMEM), (perase P mo), []. cbn [nstepL]. split; [reflexivity|]. left. exists ENOMEM.
      rewrite m_vmmaps_perase. change (lenZ len) with nZ. fold h. rewrite HG. cbn [negb]. split; [exact mmap_errnos_when_true|]. split; reflexivity.
  - intros eff' mo1' evs' Hs. apply D, RAW in Hs.
    destruct Hs as [(e & _ & Hs)|(a & _ & Hs)]; apply Ok_inj in Hs as (_ & -> & _); [exact Hh|].
    rewrite m_halted_with_mmap_backing, m_halted_with_vmmaps. exact Hh.
Qed.

#[using="HF HZ HI HA HC"] Lemma madvise_factsL : forall addr len,
  at_nodeL segs (LMadvise addr len) (restrict H msF) -> nsafeL (LMadvise addr len) (perase P mo) ->
  factsL segs (LMadvise addr len) H P msF mo (Z_to_bv 64 233).
Proof.
  intros addr len HatR Hsafe.
  destruct HatR as ((Hsvc & Ha0 & Ha1 & Ha2 & Hlen) & Hal & Hpos & Hub & Hoff).
  unfold areg in Ha0, Ha1, Ha2. cbn [AsanAcct.restrict ms_regs ms_svc_pending] in Hsvc, Ha0, Ha1, Ha2.
  fold (areg msF 10) in Ha0. fold (areg msF 11) in Ha1. fold (areg msF 12) in Ha2.
  cbn [nsafeL] in Hsafe. rewrite m_vmmaps_perase in Hsafe.
  set (A := Z_to_bv 64 addr) in *. set (n := lenW len) in *.
  pose proof (lenZ_nonneg len) as Hn0.
  assert (EA : bv_unsigned A = addr) by (subst A; apply u64_lit; lia).
  assert (Hn : bv_unsigned n = lenZ len).
  { subst n. unfold lenW. apply u64_lit. lia. }
  set (lo := addrZ addr). set (hi := lo + lenZ len).
  assert (Elo : lo = addr) by (unfold lo, addrZ; fold A; exact EA).
  assert (Ehi : hi = addr + lenZ len) by (unfold hi; rewrite Elo; reflexivity).
  assert (Hlo : lo mod 4096 = 0) by (rewrite Elo; exact Hal).
  assert (Hhi : hi mod 4096 = 0).
  { rewrite Ehi. rewrite <- Zplus_mod_idemp_l. change 4096 with page_size. rewrite Hal. apply lenZ_aligned. }
  assert (Hlh : lo <= hi) by (rewrite Elo, Ehi; lia).
  set (mo1 := madvise_dontneed_next mo A n).
  set (eff0 := mkEffect (Z_to_bv 64 0) [] [(A, n)]).
  assert (OUT : forall o, syscall_spec (sys_input segs msF (Z_to_bv 64 233)) mo o <-> o = Ok eff0 mo1 []).
  { intros o. rewrite (syscall_spec_233 _ _ _ (sysno_of segs msF _ 233 ltac:(lia) eq_refl)).
    rewrite in_a0_si, in_a1_si, in_a2_si, Ha0, Ha1, Ha2.
    apply (madvise_dontneed_outcome A (Z_to_bv 64 len) (int32 (Z_to_bv 64 MADV_DONTNEED)) _ mo o);
      [rewrite EA; exact Hal| vm_compute; reflexivity| exact Hlen| | exact Hsafe].
    rewrite EA. fold (lenZ len). unfold two_pow_64. lia. }
  assert (Emo1 : mo1 = with_vm_backing (m_vm_lazy mo) (cut_pages lo hi (m_vm_materialized mo)) mo).
  { unfold mo1, madvise_dontneed_next, cut_pages. rewrite EA, Hn, Elo, Ehi. reflexivity. }
  set (P' := cut_pages lo hi P).
  assert (Eper : perase P' mo1 = with_vm_backing (m_vm_lazy (perase P mo)) (cut_pages lo hi (m_vm_materialized (perase P mo))) (perase P mo)).
  { rewrite Emo1. destruct mo as [fd [maps lazy mat] io fs proc lim tm]. reflexivity. }
  pose proof HI as [N1 N2 N3 N4 N5].
  split.
  - exact Hsvc.
  - intros eff mo' evs Hs. apply OUT in Hs. apply Ok_inj in Hs as (-> & -> & ->). cbn [allowL hideL]. fold lo hi P'.
    split. { cbn [nstepL]. fold lo hi. split; [reflexivity|]. split; [reflexivity| exact Eper]. }
    split. { rewrite Emo1. destruct mo; exact Hh. }
    split.
    { rewrite Emo1. apply MInv_wvb.
      + apply NoDup_filter. exact N1.
      + intros p Hp. apply filter_In in Hp as [Hp _]. exact (N2 p Hp).
      + intros p Hp. apply cut_pages_in in Hp as [Hp Hout]. pose proof (N2 p Hp) as Hpal.
        apply (proj2 (page_allowedb_ivl _ p Hpal (cut_pages_aligned _ _ _ HA))). apply cut_pages_in.
        split; [exact (proj1 (page_allowedb_ivl _ p Hpal HA) (N3 p Hp))| exact Hout].
      + intros p Hp. apply filter_In in Hp as [Hp _]. exact (N4 p Hp).
      + rewrite A_bytes_ivl in N5 |- *. pose proof (cut_pages_length lo hi P) as CL. fold P' in CL. apply Nat2Z.inj_le in CL. unfold page_size in *. lia. }
    split.
    {
      intros w Hpl Hw. rewrite Emo1 in Hpl. revert Hpl. model_proj. intros Hpl.
      pose proof (page_base_facts w) as (B1 & B2 & B3).
      unfold hide_range in Hw. apply orb_false_iff in Hw as [Hw1 Hw2].
      pose proof (HC w Hpl Hw1) as Hal0.
      apply (proj2 (page_allowedb_ivl _ _ B3 (cut_pages_aligned _ _ _ HA))). apply cut_pages_in.
      split; [exact (proj1 (page_allowedb_ivl _ _ B3 HA) Hal0)|].
      unfold in_rangeb in Hw2. fold lo hi in Hw2.
      destruct (aligned_in_or_out (bv_unsigned (page_base w)) lo hi B3 Hlo Hhi) as [Hinr|Houtr]; [| unfold page_size in *; lia].
      exfalso. apply andb_false_iff in Hw2 as [W|W]; [apply Z.leb_gt in W| apply Z.ltb_ge in W]; unfold page_size in *; lia. }
    split. { apply cut_pages_aligned. exact HA. }
    split. { apply minvL_perase. rewrite Emo1. change (minvL (perase (cut_pages lo hi (m_vm_materialized mo)) mo)). apply minvL_perase. exact (proj1 (minvL_perase _ _) (lf_minv _ _ _ _ _ HF)). }
    split. { cbn. apply AsanAcct.ranges_avoid_nil. }
    split. { reflexivity. }
    split.
    {
      intros x Hx Hzb. unfold eff0. change (mkEffect (Z_to_bv 64 0) [] [(A, n)]) with (mkEffectU (Z_to_bv 64 0) [] [(A, n)] [] [] []).
      rewrite nret_mem_zu. destruct (zeros_cover [(A, n)] x) eqn:ZC; [reflexivity|]. cbn [zeros_cover existsb].
      unfold hide_range in Hx. apply orb_true_iff in Hx as [Hx|Hx]; [exact (HZ x Hx Hzb)|].
      exfalso. unfold in_rangeb in Hx. apply andb_prop in Hx as [X1 X2]. apply Z.leb_le in X1. apply Z.ltb_lt in X2.
      cbn [zeros_cover existsb] in ZC. rewrite orb_false_r in ZC. unfold in_iv, in_rng, B, S in ZC. cbn [fst snd] in ZC.
      rewrite EA, Hn in ZC. apply andb_false_iff in ZC as [ZC|ZC]; [apply Z.leb_gt in ZC| apply Z.ltb_ge in ZC]; rewrite Elo, Ehi in *; lia. }
    split.
    {
      right. split; [reflexivity|]. intros a Ha. unfold hide_range in Ha. apply orb_true_iff in Ha as [Ha|Ha]; [left; exact Ha| right].
      unfold in_rangeb in Ha. apply andb_prop in Ha as [X1 X2]. apply Z.leb_le in X1. apply Z.ltb_lt in X2. apply Hoff. rewrite Elo, Ehi in *. lia. }
    intros x0 Hx0 Hu0. unfold hide_range in Hu0. rewrite Hx0 in Hu0. discriminate.
  - intros Hs. apply OUT in Hs. discriminate.
  - intros eff moE' evs Hst. cbn [nstepL] in Hst. fold lo hi in Hst. destruct Hst as (-> & Hs & ->).
    exists eff0, mo1. split; [rewrite Hs; reflexivity|]. split; [apply OUT; reflexivity|]. cbn [allowL]. fold lo hi P'. exact Eper.
  - exists eff0, (with_vm_backing (m_vm_lazy (perase P mo)) (cut_pages lo hi (m_vm_materialized (perase P mo))) (perase P mo)), [].
    cbn [nstepL]. fold lo hi. repeat split; reflexivity.
Qed.

End PerKindMm.

Theorem mm_factsL_all : forall segs, mm_factsL segs.
Proof.
  intros segs. constructor; intros H P msF mo.
  - intros addr len HF HZ. exact (munmap_factsL segs H P msF mo HF HZ addr len).
  - intros addr len prot flags HF HZ. exact (mmap_factsL segs H P msF mo HF HZ addr len prot flags).
  - intros len off HF HZ. exact (mmap_heap_factsL segs H P msF mo HF HZ len off).
  - intros len HF HZ. exact (mmap_nr_factsL segs H P msF mo HF HZ len).
  - intros addr len flags HF HZ. exact (mmap_fixed_factsL segs H P msF mo HF HZ addr len flags).
  - intros addr len off HF HZ. exact (mmap_commit_factsL segs H P msF mo HF HZ addr len off).
  - intros addr len HF HZ. exact (madvise_factsL segs H P msF mo HF HZ addr len).
Qed.

Theorem nodesL_sound : forall segs,
  node_soundL nodeL segs (at_nodeL segs) nstepL nexitL minvL nsafeL hideL allowL.
Proof. intros segs. exact (nodesL_sound_of segs (mm_factsL_all segs)). Qed.
