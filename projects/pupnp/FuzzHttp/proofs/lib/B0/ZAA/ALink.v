(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Madvise.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import LiaTuning ITree Nodes Decode Ceiling VmGap.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Bridge.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.ASN Require Import BackingAlgebra.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.LZ Require Import ITreeLZ NodesLZ.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.LZ Require LZPages NodesLZMm.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAA Require Import LJ ALinkPg ALinkVm.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Record vabs := mkVA {
  va_prim : Z;
  va_chunks : list (Z * Z);
  va_nsec : Z;
  va_aux : Z
}.

Record vmbase := mkVB {
  vb_maps : list (word * word);
  vb_used : Z;
  vb_space : Z;
  vb_gapB : Z;
  vb_gapN : Z
}.

Definition sc_ent (c : Z * Z) : word * word := (Z_to_bv 64 (fst c), Z_to_bv 64 (snd c)).

Definition hull_bytes (a n : Z) : Z :=
  Z.of_nat (length (pages_of (shw_lo SHADOW_OFF a) (shw_hi SHADOW_OFF a n))) * page_size.

Definition chunks_weight (l : list (Z * Z)) : Z :=
  fold_right (fun c acc => snd c + hull_bytes (fst c) (snd c) + acc) 0 l.

Lemma hull_bytes_bound : forall a n, 0 <= a -> 0 <= n -> 0 <= hull_bytes a n <= n / 8 + 2 * page_size.
Proof.
  intros a n Ha Hn. unfold hull_bytes. split; [unfold page_size; lia|].
  apply win_pages_bound; [unfold SHADOW_OFF; lia| exact Ha| exact Hn].
Qed.

Lemma hull_bytes_aligned : forall a n, 0 <= a -> 0 <= n -> a mod 32768 = 0 -> n mod 32768 = 0 -> hull_bytes a n = n / 8.
Proof.
  intros a n Ha Hn Ma Mn. unfold hull_bytes.
  assert (Elo : shw_lo SHADOW_OFF a = a / 8 + SHADOW_OFF).
  { unfold shw_lo, SHADOW_OFF, page_size. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). nia. }
  assert (Ehi : shw_hi SHADOW_OFF a n = (a + n) / 8 + SHADOW_OFF).
  { unfold shw_hi, SHADOW_OFF, page_size. nia. }
  rewrite Elo, Ehi. rewrite LZPages.pages_of_length.
  - nia.
  - unfold SHADOW_OFF, page_size. nia.
  - unfold SHADOW_OFF, page_size. nia.
  - nia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma a0_reserved_eq : segments_reserved asegs =
  [(Z_to_bv 64 65536, Z_to_bv 64 139264); (Z_to_bv 64 204800, Z_to_bv 64 491520);
   (Z_to_bv 64 696320, Z_to_bv 64 8192); (Z_to_bv 64 704512, Z_to_bv 64 5623808)].
Proof. vm_compute. reflexivity. Qed.

Lemma region_free_above : forall l (a n : word) top,
  Forall (fun e => vhi e <= top) l -> top <= bv_unsigned a -> region_free l a n = true.
Proof.
  induction l as [|[b s] l IH]; intros a n top HF Ha; [reflexivity|].
  inversion HF as [|e l' He Hl]; subst. cbn [region_free]. rewrite (IH a n top Hl Ha), andb_true_r.
  apply negb_true_iff. unfold iv_overlap. apply andb_false_iff. left. apply Z.ltb_ge.
  unfold vhi, vlo, vsz in He. cbn [fst snd] in He. lia.
Qed.

Lemma a0_reserved_free_above : forall a n : word, 0x609000 <= bv_unsigned a -> region_free (segments_reserved asegs) a n = true.
Proof.
  intros a n Ha. rewrite a0_reserved_eq. apply (region_free_above _ a n 0x609000); [| exact Ha].
  repeat constructor; vm_compute; discriminate.
Qed.

Lemma a0_reserved_free_below : forall a n : word, bv_unsigned a + bv_unsigned n <= 0x10000 -> region_free (segments_reserved asegs) a n = true.
Proof.
  intros a n Ha. rewrite a0_reserved_eq. cbn [region_free]. unfold iv_overlap. cbn [fst snd].
  rewrite !fg_lit by lia. pose proof (bv_unsigned_in_range 64 a). pose proof (bv_unsigned_in_range 64 n).
  replace (65536 <? bv_unsigned a + bv_unsigned n) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (204800 <? bv_unsigned a + bv_unsigned n) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (696320 <? bv_unsigned a + bv_unsigned n) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (704512 <? bv_unsigned a + bv_unsigned n) with false by (symmetry; apply Z.ltb_ge; lia).
  rewrite !andb_false_r. reflexivity.
Qed.

Notation K_SPACE1 := 137438957568%Z.

Definition cuts_in_maps (mo : Model) : Prop :=
  forall x, covered (vm_noaccess (m_vmmaps mo) ++ m_vm_lazy mo) x = true -> covered (vm_maps (m_vmmaps mo)) x = true.
Definition pos_maps (mo : Model) : Prop := Forall (fun q => 0 < S q) (vm_maps (m_vmmaps mo)).

Definition chunk_sane (ch : Z * Z) : Prop :=
  0x609000 <= fst ch /\ 0 < snd ch /\ fst ch + snd ch <= 2^47 /\ fst ch mod 4096 = 0 /\ snd ch mod 4096 = 0
  /\ (fst ch + snd ch <= 0x7fff7000 \/ 0x10007fff8000 <= fst ch).
Definition chunks_sane (l : list (Z * Z)) : Prop := Forall chunk_sane l.

Section Link.
Context {HC : HasCeiling}.
Variable Bs : vmbase.

Record LINK (v : vabs) (mo : Model) : Prop := mkLINK {
  lk_wf : vmwf mo;
  lk_pos : pos_maps mo;
  lk_cuts : cuts_in_maps mo;
  lk_res : vm_reserved (m_vmmaps mo) = segments_reserved asegs;
  lk_lim : vm_limit (m_vmmaps mo) = target_alloc_limit;
  lk_top : alloc_top (m_vmmaps mo) = alloc_ceiling;
  lk_maps : Permutation (vm_maps (m_vmmaps mo)) (map sc_ent (va_chunks v) ++ vb_maps Bs);
  lk_back : Forall (fun c => fully_backed mo (sc_ent c)) (va_chunks v);
  lk_pal : va_prim v mod 32768 = 0 /\ 0 <= va_prim v;
  lk_sane : chunks_sane (va_chunks v);

  lk_inner : Forall (fun c => forall q, In q (inner_pages (fst c) (snd c)) -> In q (m_vm_materialized mo)) (va_chunks v);

  lk_noacc : Forall (off_band 0x7fff7000 0x8fff7000) (vm_noaccess (m_vmmaps mo))
             /\ Forall (off_band 0x2008fff7000 0x10007fff8000) (vm_noaccess (m_vmmaps mo));
  lk_used : vm_backing_used mo + 8192 * Z.of_nat (length (va_chunks v))
            <= vb_used Bs + va_prim v + va_prim v / 8 + chunks_weight (va_chunks v) + 8192 * va_nsec v + va_aux v
}.

Record base_ok : Prop := mkBO {

  bo_space : exists e, In e (vb_maps Bs) /\ vlo e <= vb_space Bs /\ vb_space Bs + K_SPACE1 <= vhi e;
  bo_space_lo : 0x10007fff8000 <= vb_space Bs;
  bo_space_hi : vb_space Bs + K_SPACE1 <= alloc_ceiling;

  bo_band : forall a n : word, 0 < bv_unsigned n -> region_free (vb_maps Bs) a n = true ->
            bv_unsigned a + bv_unsigned n <= 0x7fff7000 \/ 0x10007fff8000 <= bv_unsigned a;
  bo_gap : forall n, 0 < n -> gap_cost n 0x10007fff8000 (vb_maps Bs) <= vb_gapB Bs + vb_gapN Bs * (n + 4095);

  bo_lowsh : In (Z_to_bv 64 0x7fff7000, Z_to_bv 64 0x10000000) (vb_maps Bs);
  bo_highsh : In (Z_to_bv 64 0x2008fff7000, Z_to_bv 64 0xdfff0001000) (vb_maps Bs)
}.

Definition vroom (v : vabs) (extra : Z) : Prop :=
  vb_used Bs + va_prim v + va_prim v / 8 + chunks_weight (va_chunks v) + 8192 * va_nsec v + va_aux v + extra <= target_alloc_limit.

#[using="Type"] Lemma div8_add_aligned : forall p n, p mod 32768 = 0 -> n mod 32768 = 0 -> (p + n) / 8 = p / 8 + n / 8.
Proof.
  intros p n Hp Hn. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[using="Type"] Lemma link_commit : forall v mo addr len (Q : exc unit -> Model -> Prop),
  base_ok -> LINK v mo ->
  vb_space Bs <= addr -> addr + lenZ len <= vb_space Bs + K_SPACE1 ->
  addr mod 32768 = 0 -> lenZ len mod 32768 = 0 -> 0 < lenZ len ->
  vroom v (lenZ len + lenZ len / 8 + 2 * page_size) ->
  (forall mo', LINK (mkVA (va_prim v + lenZ len) (va_chunks v) (va_nsec v) (va_aux v)) mo' ->
               m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo -> Q (Ok tt) mo') ->
  stwfL (t_commit addr len) mo Q.
Proof.
  intros v mo addr len Q [(es & BO1 & BO1a & BO1b) BO2 BO3 _ _ _ _] LK Hlo Hhi Ma Mn Hn Hroom HQ.
  pose proof LK as [Hwf Hpos Hcuts Hres Hlim Htop Hperm Hback [Hpal Hp0] Hsane Hinner [Hna1 Hna2] Hused].
  pose proof (@alloc_ceiling_lt47 HC) as Hc47.
  assert (En : bv_unsigned (lenW len) = lenZ len) by (apply lenW_unsigned; lia).
  assert (Ea : bv_unsigned (Z_to_bv 64 addr) = addr) by (apply addr_unsigned; lia).
  assert (Hmc : map_contains (vm_maps (m_vmmaps mo)) (Z_to_bv 64 addr) (lenW len) = true).
  { unfold map_contains. apply existsb_exists. exists es. split.
    - apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. exact BO1.
    - cbv zeta. rewrite Ea, En. unfold vhi, vlo, vsz in BO1a, BO1b. apply andb_true_iff. split; apply Z.leb_le; lia. }
  apply stwf_commit.
  - apply nsafeL_commit; try assumption; try lia.
    + unfold SHADOW_OFF. lia.
    + rewrite Hres. apply a0_reserved_free_above. rewrite Ea. lia.
    + rewrite Hlim. unfold vroom in Hroom. cbn [va_prim va_chunks va_nsec va_aux] in Hroom. lia.
  - apply HQ; [| apply commit_post_fds; exact Hmc].
    pose proof Hwf as [(_ & Wn & _ & _) _]. pose proof (bv_unsigned_in_range 64 (lenW len)) as Rn.
    constructor; cbn [va_prim va_chunks va_nsec va_aux].
    + apply commit_post_vmwf; assumption.
    + unfold pos_maps. rewrite (commit_post_maps _ _ _ _ Hmc). exact Hpos.
    + intros x Hx. rewrite (commit_post_maps _ _ _ _ Hmc). apply Hcuts.
      rewrite (commit_post_cuts _ _ _ _ Hmc Hwf) in Hx. apply andb_true_iff in Hx as [Hx _]. exact Hx.
    + rewrite (commit_post_reserved _ _ _ _ Hmc). exact Hres.
    + rewrite (commit_post_limit _ _ _ _ Hmc). exact Hlim.
    + unfold alloc_top. rewrite (commit_post_init_sp _ _ _ _ Hmc). exact Htop.
    + rewrite (commit_post_maps _ _ _ _ Hmc). exact Hperm.
    + apply Forall_forall. intros c Hc x Hx. pose proof (proj1 (Forall_forall _ _) Hback c Hc x Hx) as Hb.
      rewrite (commit_post_cuts _ _ _ _ Hmc Hwf). rewrite Hb. reflexivity.
    + split; [| lia]. rewrite <- Z.add_mod_idemp_l, Hpal by lia. rewrite Z.add_0_l. exact Mn.
    + exact Hsane.
    +
      apply Forall_forall. intros c Hc q Hq.
      pose proof (proj1 (Forall_forall _ _) Hinner c Hc q Hq) as Hin.
      pose proof (proj1 (Forall_forall _ _) Hsane c Hc) as (S1 & S2 & S3 & _).
      destruct (inner_pages_in (fst c) (snd c) q ltac:(lia) ltac:(lia) Hq) as (z & -> & Z1 & Z2 & Z3).
      rewrite (lmcommit_post_eq _ _ _ _ Hmc). rewrite m_vm_materialized_with_vm_backing. apply in_or_app. right.
      rewrite m_vm_materialized_vm_forget_range, m_vm_materialized_with_vmmaps. apply filter_In. split; [exact Hin|].
      assert (Hz : 0 <= z < 0x10007fff8000).
      { pose proof (Z.div_pos (fst c) 8 ltac:(lia) ltac:(lia)).
        pose proof (Z.div_le_mono (fst c + snd c) (2^47) 8 ltac:(lia) S3). change (2^47 / 8) with (2^44) in *.
        unfold shZ, SHOFF in *. lia. }
      unfold page_outside_range. rewrite !fg_lit by lia.
      apply negb_true_iff. apply andb_false_iff. left. apply Z.leb_gt. lia.
    + split; (rewrite (commit_post_vmmaps _ _ _ _ Hmc); cbn [mmap_fixed_rw_next vm_noaccess];
              apply maps_subtract_off_band; [exact Wn| lia| assumption]).
    + pose proof (commit_post_used mo addr len SHADOW_OFF Hmc Hwf ltac:(lia)) as Hu. rewrite En in Hu.
      assert (Eaz : addrZ addr = addr) by (unfold addrZ; apply addr_unsigned; lia). rewrite Eaz in Hu.
      pose proof (hull_bytes_aligned addr (lenZ len) ltac:(lia) ltac:(lia) Ma Mn) as Hh. unfold hull_bytes in Hh. rewrite Hh in Hu.
      rewrite (div8_add_aligned _ _ Hpal Mn). lia.
Qed.

#[using="Type"] Lemma link_commit_aux : forall v mo addr len (Q : exc unit -> Model -> Prop),
  LINK v mo ->
  (exists e, In e (vb_maps Bs) /\ vlo e <= addr /\ addr + lenZ len <= vhi e) ->
  0 < addr -> 0 < lenZ len -> addr + lenZ len <= alloc_ceiling ->
  (addr + lenZ len <= 0x10000 \/ 0x609000 <= addr) ->
  (addr + lenZ len <= 0x7fff7000 \/ 0x10007fff8000 <= addr) ->
  vroom v (lenZ len + lenZ len / 8 + 2 * page_size) ->
  (forall mo', LINK (mkVA (va_prim v) (va_chunks v) (va_nsec v) (va_aux v + (lenZ len + lenZ len / 8 + 2 * page_size))) mo' ->
               m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo -> Q (Ok tt) mo') ->
  stwfL (t_commit addr len) mo Q.
Proof.
  intros v mo addr len Q LK (es & BO1 & BO1a & BO1b) Ha Hn Hce Himg Hband Hroom HQ.
  pose proof LK as [Hwf Hpos Hcuts Hres Hlim Htop Hperm Hback [Hpal Hp0] Hsane Hinner [Hna1 Hna2] Hused].
  pose proof (@alloc_ceiling_lt47 HC) as Hc47.
  assert (En : bv_unsigned (lenW len) = lenZ len) by (apply lenW_unsigned; lia).
  assert (Ea : bv_unsigned (Z_to_bv 64 addr) = addr) by (apply addr_unsigned; lia).
  assert (Hmc : map_contains (vm_maps (m_vmmaps mo)) (Z_to_bv 64 addr) (lenW len) = true).
  { unfold map_contains. apply existsb_exists. exists es. split.
    - apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. exact BO1.
    - cbv zeta. rewrite Ea, En. unfold vhi, vlo, vsz in BO1a, BO1b. apply andb_true_iff. split; apply Z.leb_le; lia. }
  apply stwf_commit.
  - apply nsafeL_commit; try assumption; try lia.
    + unfold SHADOW_OFF. lia.
    + rewrite Hres. destruct Himg; [apply a0_reserved_free_below; rewrite Ea, En; lia| apply a0_reserved_free_above; rewrite Ea; lia].
    + rewrite Hlim. unfold vroom in Hroom. lia.
  - apply HQ; [| apply commit_post_fds; exact Hmc].
    pose proof Hwf as [(_ & Wn & _ & _) _]. pose proof (bv_unsigned_in_range 64 (lenW len)) as Rn.
    constructor; cbn [va_prim va_chunks va_nsec va_aux].
    + apply commit_post_vmwf; assumption.
    + unfold pos_maps. rewrite (commit_post_maps _ _ _ _ Hmc). exact Hpos.
    + intros x Hx. rewrite (commit_post_maps _ _ _ _ Hmc). apply Hcuts.
      rewrite (commit_post_cuts _ _ _ _ Hmc Hwf) in Hx. apply andb_true_iff in Hx as [Hx _]. exact Hx.
    + rewrite (commit_post_reserved _ _ _ _ Hmc). exact Hres.
    + rewrite (commit_post_limit _ _ _ _ Hmc). exact Hlim.
    + unfold alloc_top. rewrite (commit_post_init_sp _ _ _ _ Hmc). exact Htop.
    + rewrite (commit_post_maps _ _ _ _ Hmc). exact Hperm.
    + apply Forall_forall. intros c Hc x Hx. pose proof (proj1 (Forall_forall _ _) Hback c Hc x Hx) as Hb.
      rewrite (commit_post_cuts _ _ _ _ Hmc Hwf). rewrite Hb. reflexivity.
    + split; assumption.
    + exact Hsane.
    + apply Forall_forall. intros c Hc q Hq.
      pose proof (proj1 (Forall_forall _ _) Hinner c Hc q Hq) as Hin.
      pose proof (proj1 (Forall_forall _ _) Hsane c Hc) as (S1 & S2 & S3 & _).
      destruct (inner_pages_in (fst c) (snd c) q ltac:(lia) ltac:(lia) Hq) as (z & -> & Z1 & Z2 & Z3).
      rewrite (lmcommit_post_eq _ _ _ _ Hmc). rewrite m_vm_materialized_with_vm_backing. apply in_or_app. right.
      rewrite m_vm_materialized_vm_forget_range, m_vm_materialized_with_vmmaps. apply filter_In. split; [exact Hin|].
      assert (Hz : 0x7fff8000 <= z < 0x10007fff8000).
      { pose proof (Z.div_pos (fst c) 8 ltac:(lia) ltac:(lia)).
        pose proof (Z.div_le_mono (fst c + snd c) (2^47) 8 ltac:(lia) S3). change (2^47 / 8) with (2^44) in *.
        unfold shZ, SHOFF in *. lia. }
      unfold page_outside_range. rewrite !fg_lit by lia. rewrite En.
      apply negb_true_iff. apply andb_false_iff. destruct Hband; [right; apply Z.ltb_ge| left; apply Z.leb_gt]; lia.
    + split; (rewrite (commit_post_vmmaps _ _ _ _ Hmc); cbn [mmap_fixed_rw_next vm_noaccess];
              apply maps_subtract_off_band; [exact Wn| lia| assumption]).
    + pose proof (commit_post_used mo addr len SHADOW_OFF Hmc Hwf ltac:(lia)) as Hu. rewrite En in Hu.
      assert (Eaz : addrZ addr = addr) by (unfold addrZ; apply addr_unsigned; lia). rewrite Eaz in Hu.
      pose proof (win_pages_bound SHADOW_OFF addr (lenZ len) ltac:(unfold SHADOW_OFF; lia) ltac:(lia) ltac:(lia)) as Hw.
      lia.
Qed.

#[using="Type"] Lemma region_free_not_covered : forall l (a n : word) x,
  region_free l a n = true -> bv_unsigned a <= x < bv_unsigned a + bv_unsigned n -> covered l x = false.
Proof.
  induction l as [|[b s] l IH]; intros a n x Hrf Hx; [reflexivity|].
  cbn [region_free] in Hrf. apply andb_true_iff in Hrf as [H1 H2].
  change (covered ((b, s) :: l) x) with (in_iv (b, s) x || covered l x). rewrite (IH a n x H2 Hx), orb_false_r.
  apply negb_true_iff in H1. unfold iv_overlap in H1. unfold in_iv, in_rng, B, S. cbn [fst snd].
  apply andb_false_iff in H1 as [H1|H1]; apply Z.ltb_ge in H1; apply andb_false_iff; [right; apply Z.ltb_ge| left; apply Z.leb_gt]; lia.
Qed.

#[using="Type"] Lemma region_free_perm : forall l l' (a n : word), Permutation l l' -> region_free l a n = region_free l' a n.
Proof.
  intros l l' a n HP. induction HP as [| [b s] l l' HP IH | [b s] [b' s'] l | l l' l'' _ IH1 _ IH2]; cbn [region_free].
  - reflexivity.
  - rewrite IH. reflexivity.
  - rewrite !andb_assoc, (andb_comm (negb (iv_overlap a n b' s'))). reflexivity.
  - congruence.
Qed.

#[using="Type"] Lemma gap_cost_perm : forall n c l l', Permutation l l' -> gap_cost n c l = gap_cost n c l'.
Proof. intros n c l l' HP. induction HP; cbn [gap_cost]; lia. Qed.

#[using="Type"] Lemma gap_cost_below : forall n c l, Forall (fun e => vhi e <= c) l -> gap_cost n c l = 0.
Proof.
  intros n c l HF. induction HF as [|e l He Hl IH]; cbn [gap_cost]; [reflexivity|].
  rewrite IH. destruct (Z.ltb_spec c (vhi e)); lia.
Qed.

Definition chunks_bytes (l : list (Z * Z)) : Z := fold_right (fun c acc => snd c + acc) 0 l.

#[using="Type"] Lemma gap_cost_chunks : forall n c l, 0 < n -> chunks_sane l ->
  gap_cost n c (map sc_ent l) <= chunks_bytes l + Z.of_nat (length l) * (n + 4095).
Proof.
  intros n c l Hn HF. induction HF as [|ch l (H1 & H2 & H3 & _) Hl IH]; cbn [map gap_cost chunks_bytes fold_right length]; [lia|].
  fold (chunks_bytes l). unfold vhi, vlo, vsz, sc_ent at 1 2 3. cbn [fst snd]. rewrite !fg_lit by lia.
  destruct (c <? fst ch + snd ch); lia.
Qed.

#[using="Type"] Lemma lenZ_mod : forall len, lenZ len mod 4096 = 0.
Proof. intros len. unfold lenZ, page_round_up_Z, page_size. apply Z.mod_mul. lia. Qed.

Definition avoid_ok (mo : Model) (avoid : list (Z * Z)) : Prop :=
  Forall (fun iv => alloc_ceiling <= fst iv \/
                    exists e, In e (vm_maps (m_vmmaps mo)) /\ vlo e <= fst iv /\ snd iv <= vhi e) avoid.

#[using="Type"] Lemma avoids_all_of_free : forall mo avoid (a n : word),
  avoid_ok mo avoid -> region_free (vm_maps (m_vmmaps mo)) a n = true -> bv_unsigned a + bv_unsigned n <= alloc_ceiling ->
  avoids_all (bv_unsigned a) (bv_unsigned n) avoid = true.
Proof.
  intros mo avoid a n HA Hrf Htop. induction HA as [|[lo hi] l Hiv Hl IH]; [reflexivity|].
  cbn [avoids_all]. rewrite IH, andb_true_r. apply orb_true_iff. cbn [fst snd] in Hiv.
  destruct Hiv as [Hc|([e sz] & Hin & H1 & H2)].
  - left. apply Z.leb_le. lia.
  - destruct (Decode.region_free_In _ _ _ _ _ Hrf Hin) as [D|D]; unfold vhi, vlo, vsz in H1, H2; cbn [fst snd] in H1, H2;
      [left| right]; apply Z.leb_le; clear - D H1 H2; lia.
Qed.

Definition gap_room (v : vabs) (n : Z) : Prop :=
  0x10007fff8000 + n + (chunks_bytes (va_chunks v) + Z.of_nat (length (va_chunks v)) * (n + 4095))
  + (vb_gapB Bs + vb_gapN Bs * (n + 4095)) <= alloc_ceiling.

#[using="Type"] Lemma link_anon : forall v mo len avoid (Q : exc Z -> Model -> Prop),
  base_ok -> LINK v mo ->
  69632 <= lenZ len -> avoid_ok mo avoid ->
  vroom v (lenZ len + (lenZ len / 8 + 2 * page_size) + 8192) -> gap_room v (lenZ len) ->
  (forall a mo', chunk_sane (a, lenZ len) -> a + lenZ len <= alloc_ceiling ->
                 LINK (mkVA (va_prim v) ((a, lenZ len) :: va_chunks v) (va_nsec v + 1) (va_aux v)) mo' ->
                 m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo -> Q (Ok a) mo') ->
  stwfL (t_anon len avoid) mo Q.
Proof.
  intros v mo len avoid Q [_ _ _ BO4 BO5 _ _] LK Hn Hav Hroom Hgap HQ.
  pose proof LK as [Hwf Hpos Hcuts Hres Hlim Htop Hperm Hback [Hpal Hp0] Hsane Hinner [Hna1 Hna2] Hused].
  pose proof (@alloc_ceiling_lt47 HC) as Hc47.

  assert (PL : forall a : word, mmap_placed mo 0 len MAPF_ANON_PRIVATE a ->
             bv_unsigned a mod page_size = 0 /\ 0x609000 <= bv_unsigned a /\ bv_unsigned a + lenZ len <= alloc_ceiling /\
             region_free (vm_maps (m_vmmaps mo)) a (lenW len) = true /\ bv_unsigned (lenW len) = lenZ len /\
             (bv_unsigned a + lenZ len <= 0x7fff7000 \/ 0x10007fff8000 <= bv_unsigned a)).
  { intros a Hp. destruct (anon_placed_facts mo len a Hp ltac:(lia)) as (F1 & F2 & F3 & F4 & F5 & F6).
    rewrite Htop in F3. rewrite Hres, a0_reserved_eq in F4.
    assert (Hlow : 0x609000 <= bv_unsigned a).
    { pose proof (Decode.region_free_In _ _ _ _ _ F4 (or_introl eq_refl)) as D1.
      pose proof (Decode.region_free_In _ _ _ _ _ F4 (or_intror (or_introl eq_refl))) as D2.
      pose proof (Decode.region_free_In _ _ _ _ _ F4 (or_intror (or_intror (or_introl eq_refl)))) as D3.
      pose proof (Decode.region_free_In _ _ _ _ _ F4 (or_intror (or_intror (or_intror (or_introl eq_refl))))) as D4.
      rewrite !fg_lit in D1, D2, D3, D4 by lia. rewrite F6 in D1, D2, D3, D4. lia. }
    assert (Hband : bv_unsigned a + lenZ len <= 0x7fff7000 \/ 0x10007fff8000 <= bv_unsigned a).
    { rewrite <- F6. apply BO4; [lia|].
      rewrite (region_free_perm _ _ a (lenW len) Hperm), region_free_app in F5. apply andb_true_iff in F5 as [_ F5]. exact F5. }
    repeat split; try assumption; lia. }
  apply stwf_anon.
  - unfold lz_room. rewrite Hlim. unfold vroom in Hroom. lia.
  - apply (vm_gap_available_of_cost _ _ 0x10007fff8000); [lia| reflexivity| lia|].
    rewrite gap_cost_app, Hres, a0_reserved_eq.
    rewrite (gap_cost_below (lenZ len) _ _) by (repeat constructor; vm_compute; discriminate).
    rewrite (gap_cost_perm _ _ _ _ Hperm), gap_cost_app.
    pose proof (gap_cost_chunks (lenZ len) 0x10007fff8000 _ ltac:(lia) Hsane). pose proof (BO5 (lenZ len) ltac:(lia)).
    rewrite Htop. unfold gap_room in Hgap. lia.
  - intros a Hp. destruct (PL a Hp) as (P1 & P2 & P3 & P4 & P5 & P6).
    split; [exact P2|]. split; [| split; [exact P3|]].
    + unfold app_memb. apply orb_true_iff. destruct P6; [left; apply Z.ltb_lt; lia|].
      right. apply andb_true_iff. split; [apply Z.leb_le; lia| apply Z.ltb_lt; lia].
    + rewrite <- P5. apply (avoids_all_of_free mo); [exact Hav| exact P4| rewrite P5; exact P3].
  - intros a Hp. destruct (PL a Hp) as (P1 & P2 & P3 & P4 & P5 & P6).
    assert (CS : chunk_sane (bv_unsigned a, lenZ len)).
    { unfold chunk_sane. cbn [fst snd]. pose proof (lenZ_mod len). unfold page_size in P1. repeat split; try assumption; lia. }
    apply (HQ (bv_unsigned a)); [exact CS| exact P3| | apply anon_post_fds].
    constructor; cbn [va_prim va_chunks va_nsec va_aux].
    + apply anon_post_vmwf; [exact Hp| lia| exact Hwf].
    + unfold pos_maps. rewrite anon_post_maps. constructor; [unfold S; cbn [snd]; lia| exact Hpos].
    + intros x Hx. rewrite anon_post_maps.
      change (covered ((a, lenW len) :: vm_maps (m_vmmaps mo)) x) with (in_iv (a, lenW len) x || covered (vm_maps (m_vmmaps mo)) x).
      apply orb_true_iff. right. apply Hcuts. exact Hx.
    + exact Hres.
    + exact Hlim.
    + exact Htop.
    + rewrite anon_post_maps. cbn [map app]. unfold sc_ent at 1. cbn [fst snd]. rewrite Z_to_bv_bv_unsigned.
      change (Z_to_bv 64 (lenZ len)) with (lenW len). apply perm_skip. exact Hperm.
    + constructor.
      * intros x Hx. unfold sc_ent, B, S in Hx. cbn [fst snd] in Hx. rewrite Z_to_bv_bv_unsigned in Hx.
        change (Z_to_bv 64 (lenZ len)) with (lenW len) in Hx.
        change (vm_noaccess (m_vmmaps (lmheap_post mo a len SHADOW_OFF)) ++ m_vm_lazy (lmheap_post mo a len SHADOW_OFF))
          with (vm_noaccess (m_vmmaps mo) ++ m_vm_lazy mo).
        destruct (covered (vm_noaccess (m_vmmaps mo) ++ m_vm_lazy mo) x) eqn:E; [| reflexivity].
        pose proof (region_free_not_covered _ _ _ x P4 Hx) as Hnc. pose proof (Hcuts x E). congruence.
      * apply Forall_forall. intros c Hc. exact (proj1 (Forall_forall _ _) Hback c Hc).
    + split; assumption.
    + constructor; [exact CS| exact Hsane].
    +
      change (m_vm_materialized (lmheap_post mo a len SHADOW_OFF))
        with (hull_pages (bv_unsigned a) (lenZ len) ++ m_vm_materialized mo).
      constructor.
      * cbn [fst snd]. intros q Hq. apply in_or_app. left. apply inner_in_hull; [lia| lia| exact Hq].
      * apply Forall_forall. intros c Hc q Hq. apply in_or_app. right. exact (proj1 (Forall_forall _ _) Hinner c Hc q Hq).
    + split; assumption.
    + pose proof (anon_post_used mo len SHADOW_OFF a Hp ltac:(lia) Hwf) as Hu.
      cbn [length chunks_weight fold_right fst snd]. fold (chunks_weight (va_chunks v)). unfold hull_bytes.
      rewrite Nat2Z.inj_succ. lia.
Qed.

#[using="Type"] Lemma chunks_weight_perm : forall l l', Permutation l l' -> chunks_weight l = chunks_weight l'.
Proof. intros l l' HP. induction HP; cbn [chunks_weight fold_right]; try fold (chunks_weight l); try fold (chunks_weight l'); lia. Qed.

#[using="Type"] Lemma Forall_perm {A} : forall (P : A -> Prop) l l', Permutation l l' -> Forall P l -> Forall P l'.
Proof. intros P l l' HP HF. apply Forall_forall. intros x Hx. apply (proj1 (Forall_forall _ _) HF). apply (Permutation_in _ (Permutation_sym HP)). exact Hx. Qed.

#[using="Type"] Lemma LINK_perm : forall v mo l, LINK v mo -> Permutation (va_chunks v) l -> LINK (mkVA (va_prim v) l (va_nsec v) (va_aux v)) mo.
Proof.
  intros v mo l [Hwf Hpos Hcuts Hres Hlim Htop Hperm Hback Hpal Hsane Hinner Hna Hused] HP.
  constructor; cbn [va_prim va_chunks va_nsec va_aux]; try assumption.
  - eapply perm_trans; [exact Hperm|]. apply Permutation_app_tail. apply Permutation_map. exact HP.
  - exact (Forall_perm _ _ _ HP Hback).
  - exact (Forall_perm _ _ _ HP Hsane).
  - exact (Forall_perm _ _ _ HP Hinner).
  - rewrite <- (Permutation_length HP), <- (chunks_weight_perm _ _ HP). exact Hused.
Qed.

#[using="Type"] Lemma lenZ_id : forall n, 0 <= n < 2^64 -> n mod 4096 = 0 -> lenZ n = n.
Proof.
  intros n Hn Hm. unfold lenZ, page_round_up_Z, page_size. rewrite fg_lit by lia.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition flush_treeL (p n : Z) : itree nodeL (exc unit) :=
  match inner_range p n with None => Ret (Ok tt) | Some (pb, pe) => t_madv pb (pe - pb) end.

Definition flush_post (mo : Model) (p n : Z) : Model :=
  match inner_range p n with None => mo | Some (pb, pe) => madv_post mo pb pe end.

#[using="Type"] Lemma sh_band_low : forall x, 0 <= x -> x <= 0x7fff7000 -> 0x7fff8000 <= shZ x /\ shZ x <= 0x8fff7000.
Proof.
  intros x H0 H1. unfold shZ, SHOFF. pose proof (Z.div_pos x 8 H0 ltac:(lia)).
  pose proof (Z.div_le_mono x 0x7fff7000 8 ltac:(lia) H1). change (0x7fff7000 / 8) with 268430848 in *. lia.
Qed.
#[using="Type"] Lemma sh_band_high : forall x, 0x10007fff8000 <= x -> x <= 2^47 -> 0x2008fff7000 <= shZ x /\ shZ x <= 0x10007fff8000.
Proof.
  intros x H0 H1. unfold shZ, SHOFF.
  pose proof (Z.div_le_mono 0x10007fff8000 x 8 ltac:(lia) H0). pose proof (Z.div_le_mono x (2^47) 8 ltac:(lia) H1).
  change (0x10007fff8000 / 8) with 2199291686912 in *. change (2^47 / 8) with 17592186044416 in *. lia.
Qed.

#[using="Type"] Lemma stwf_flush : forall v mo p n (Q : exc unit -> Model -> Prop),
  base_ok -> LINK v mo -> In (p, n) (va_chunks v) ->
  Q (Ok tt) (flush_post mo p n) ->
  stwfL (flush_treeL p n) mo Q.
Proof.
  intros v mo p n Q [_ _ _ _ _ BOl BOh] LK Hin HQ.
  pose proof LK as [Hwf Hpos Hcuts Hres Hlim Htop Hperm Hback Hpal Hsane Hinner [Hna1 Hna2] Hused].
  pose proof (proj1 (Forall_forall _ _) Hsane _ Hin) as (S1 & S2 & S3 & S4 & S5 & S6). cbn [fst snd] in *.
  unfold flush_treeL, flush_post in *. unfold inner_range in *. cbv zeta in *.
  assert (Hs : 0 <= shZ p) by (unfold shZ, SHOFF; pose proof (Z.div_pos p 8 ltac:(lia) ltac:(lia)); lia).
  assert (He : 0 <= shZ (p + n)) by (unfold shZ, SHOFF; pose proof (Z.div_pos (p + n) 8 ltac:(lia) ltac:(lia)); lia).
  destruct (pg_facts (shZ p) Hs) as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
  destruct (pg_facts (shZ (p + n)) He) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8).
  pose proof (shZ_mono p (p + n) ltac:(lia)) as Hm.
  destruct (Z.leb_spec (pgdnZ (shZ (p + n))) (pgupZ (shZ p))) as [Hle|Hlt]; [exact HQ|].
  set (pb := pgupZ (shZ p)) in *. set (pe := pgdnZ (shZ (p + n))) in *.
  assert (Hl : lenZ (pe - pb) = pe - pb).
  { apply lenZ_id; [destruct S6; [destruct (sh_band_low (p + n) ltac:(lia) ltac:(lia))| destruct (sh_band_high (p + n) ltac:(lia) ltac:(lia))]; lia|].
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. }
  assert (Hpb47 : 0 < pb /\ pe <= 2^47).
  { destruct S6; [destruct (sh_band_low p ltac:(lia) ltac:(lia)); destruct (sh_band_low (p + n) ltac:(lia) ltac:(lia))
                 | destruct (sh_band_high p ltac:(lia) ltac:(lia)); destruct (sh_band_high (p + n) ltac:(lia) ltac:(lia))]; lia. }
  assert (Eab : addrZ pb = pb) by (unfold addrZ; apply addr_unsigned; lia).
  assert (En : bv_unsigned (lenW (pe - pb)) = pe - pb) by (rewrite lenW_unsigned; lia).
  assert (Ea : bv_unsigned (Z_to_bv 64 pb) = pb) by (apply addr_unsigned; lia).
  apply stwf_madv.
  - unfold madvise_dontneed_ok. apply andb_true_iff. split; [apply andb_true_iff; split|].
    + rewrite Hres. apply a0_reserved_free_above. rewrite Ea. destruct S6; [destruct (sh_band_low p ltac:(lia) ltac:(lia))| destruct (sh_band_high p ltac:(lia) ltac:(lia))]; lia.
    + unfold map_contains. apply existsb_exists. destruct S6 as [S6|S6].
      * exists (Z_to_bv 64 0x7fff7000, Z_to_bv 64 0x10000000). split.
        -- apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. exact BOl.
        -- cbv zeta. cbn [fst snd]. rewrite Ea, En, !fg_lit by lia.
           destruct (sh_band_low p ltac:(lia) ltac:(lia)); destruct (sh_band_low (p + n) ltac:(lia) ltac:(lia)).
           apply andb_true_iff. split; apply Z.leb_le; lia.
      * exists (Z_to_bv 64 0x2008fff7000, Z_to_bv 64 0xdfff0001000). split.
        -- apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. exact BOh.
        -- cbv zeta. cbn [fst snd]. rewrite Ea, En, !fg_lit by lia.
           destruct (sh_band_high p ltac:(lia) ltac:(lia)); destruct (sh_band_high (p + n) ltac:(lia) ltac:(lia)).
           apply andb_true_iff. split; apply Z.leb_le; lia.
    + destruct S6 as [S6|S6].
      * apply (region_free_off_band 0x7fff7000 0x8fff7000); [exact Hna1| |]; rewrite ?Ea, ?En;
          destruct (sh_band_low p ltac:(lia) ltac:(lia)); destruct (sh_band_low (p + n) ltac:(lia) ltac:(lia)); lia.
      * apply (region_free_off_band 0x2008fff7000 0x10007fff8000); [exact Hna2| |]; rewrite ?Ea, ?En;
          destruct (sh_band_high p ltac:(lia) ltac:(lia)); destruct (sh_band_high (p + n) ltac:(lia) ltac:(lia)); lia.
  - rewrite Eab, Hl. replace (pb + (pe - pb)) with pe by lia. exact HQ.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[using="Type"] Lemma flush_post_same : forall mo p n,
  m_vmmaps (flush_post mo p n) = m_vmmaps mo /\ m_vm_lazy (flush_post mo p n) = m_vm_lazy mo /\
  m_fds (flush_post mo p n) = m_fds mo /\ m_fs (flush_post mo p n) = m_fs mo.
Proof. intros mo p n. unfold flush_post. destruct (inner_range p n) as [[pb pe]|]; repeat split; reflexivity. Qed.

#[using="Type"] Lemma flush_post_mat_in : forall mo p n q,
  In q (m_vm_materialized (flush_post mo p n)) -> In q (m_vm_materialized mo).
Proof.
  intros mo p n q. unfold flush_post. destruct (inner_range p n) as [[pb pe]|]; [| trivial].
  cbn. intros H. apply LZPages.cut_pages_in in H. tauto.
Qed.

#[using="Type"] Lemma flush_post_used : forall mo p n, 0 <= p -> 0 <= n -> p + n <= 2^47 ->
  (forall q, In q (inner_pages p n) -> In q (m_vm_materialized mo)) ->
  vm_backing_used (flush_post mo p n) + inner_bytes p n <= vm_backing_used mo.
Proof.
  intros mo p n Hp Hn H47 Hin. unfold flush_post, inner_bytes. pose proof (inner_pages_NoDup p n Hp Hn H47) as ND.
  unfold inner_pages in *. destruct (inner_range p n) as [[pb pe]|] eqn:E; [| cbn [length]; lia].
  pose proof (madv_post_used mo pb pe) as Hu.
  assert (Hge : Z.of_nat (length (pages_of pb pe)) <= Z.of_nat (length (pages_in pb pe (m_vm_materialized mo)))).
  { apply pages_in_ge; [exact ND|]. intros q Hq. split; [exact (Hin q Hq)|].
    unfold inner_range in E. cbv zeta in E.
    assert (Hs : 0 <= shZ p) by (unfold shZ, SHOFF; pose proof (Z.div_pos p 8 Hp ltac:(lia)); lia).
    assert (He : 0 <= shZ (p + n) <= 2^45) by (unfold shZ, SHOFF; pose proof (Z.div_pos (p + n) 8 ltac:(lia) ltac:(lia));
       pose proof (Z.div_le_mono (p + n) (2^47) 8 ltac:(lia) H47); change (2^47 / 8) with (2^44) in *; lia).
    destruct (pg_facts (shZ p) Hs) as (_ & S2 & _ & _ & _ & S6 & _ & _).
    destruct (pg_facts (shZ (p + n)) ltac:(lia)) as (E1 & _ & _ & _ & E5 & _ & _ & _).
    destruct (Z.leb_spec (pgdnZ (shZ (p + n))) (pgupZ (shZ p))) as [|Hlt]; [discriminate|]. injection E as <- <-.
    apply LZPages.pages_of_in in Hq; [| exact S6| exact E5| lia]. destruct Hq as (z & Z1 & Z2 & Z3 & ->).
    unfold page_size in *. rewrite fg_lit by lia. lia. }
  unfold page_size in *. lia.
Qed.

#[using="Type"] Lemma sc_ent_unsigned : forall c, chunk_sane c -> bv_unsigned (fst (sc_ent c)) = fst c /\ bv_unsigned (snd (sc_ent c)) = snd c.
Proof. intros c (S1 & S2 & S3 & _). unfold sc_ent. cbn [fst snd]. rewrite !fg_lit by lia. split; reflexivity. Qed.

#[using="Type"] Lemma link_dealloc_head : forall v mo p n l' (Q : exc unit -> Model -> Prop),
  base_ok -> LINK v mo -> va_chunks v = (p, n) :: l' ->
  (forall mo', LINK (mkVA (va_prim v) l' (va_nsec v) (va_aux v)) mo' -> m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo -> Q (Ok tt) mo') ->
  stwfL (ebind (flush_treeL p n) (fun _ => t_unmap p n)) mo Q.
Proof.
  intros v mo p n l' Q BO LK Ev HQ.
  pose proof LK as [Hwf Hpos Hcuts Hres Hlim Htop Hperm Hback Hpal Hsane Hinner [Hna1 Hna2] Hused].
  rewrite Ev in *. inversion Hsane as [|c0 l0 CS Hsane']; subst c0 l0.
  inversion Hback as [|c0 l0 FB Hback']; subst c0 l0. inversion Hinner as [|c0 l0 IN Hinner']; subst c0 l0.
  pose proof CS as (S1 & S2 & S3 & S4 & S5 & S6). cbn [fst snd] in *.
  set (A := Z_to_bv 64 p) in *. set (nW := Z_to_bv 64 n) in *.
  assert (EA : bv_unsigned A = p) by (unfold A; apply fg_lit; lia).
  assert (EN : bv_unsigned nW = n) by (unfold nW; apply fg_lit; lia).
  assert (Hl : lenZ n = n) by (apply lenZ_id; lia).
  assert (EnW : lenW n = nW) by (unfold lenW; rewrite Hl; reflexivity).
  assert (HinE : In (A, nW) (vm_maps (m_vmmaps mo))).
  { apply (Permutation_in _ (Permutation_sym Hperm)). cbn [map app]. left. reflexivity. }
  apply stwf_ebind. apply (stwf_flush v mo p n); [exact BO| exact LK| rewrite Ev; left; reflexivity|].
  set (mo1 := flush_post mo p n).
  destruct (flush_post_same mo p n) as (M1 & M2 & M3 & M4). fold mo1 in M1, M2, M3, M4.
  assert (Hwf1 : vmwf mo1).
  { destruct Hwf as [(W1 & W2 & W3 & W4) W5]. unfold vmwf, model_ivs_wf. rewrite M1, M2. repeat split; assumption. }
  assert (Hhas : map_has (vm_maps (m_vmmaps mo1)) A (lenW n) = true).
  { rewrite M1, EnW. unfold map_has. apply existsb_exists. exists (A, nW). split; [exact HinE|]. cbn [fst snd]. rewrite !bv_eqb_refl. reflexivity. }
  apply stwf_unmap; [lia| exact Hhas|].
  apply HQ; [| destruct (unmap_post_fds mo1 p n) as [F1 F2]; rewrite F1, F2; split; assumption].
  pose proof (unmap_post_vmwf mo1 p n Hwf1) as Hwf2.
  assert (FB1 : fully_backed mo1 (A, lenW n)).
  { rewrite EnW. intros x Hx. rewrite M1, M2. exact (FB x Hx). }
  pose proof (unmap_post_used mo1 p n Hhas Hwf1 FB1) as Hu2. rewrite EnW, EN in Hu2.
  pose proof (flush_post_used mo p n ltac:(lia) ltac:(lia) S3 IN) as Hu1. fold mo1 in Hu1.
  destruct Hwf as [Hivs Hseps].
  constructor; cbn [va_prim va_chunks va_nsec va_aux].
  - exact Hwf2.
  - unfold pos_maps. rewrite unmap_post_maps, M1. unfold map_remove. apply incl_Forall with (l1 := vm_maps (m_vmmaps mo)); [apply incl_filter| exact Hpos].
  -
    intros x Hx. rewrite (unmap_post_cuts mo1 p n Hwf1) in Hx. apply andb_true_iff in Hx as [Hx Hout].
    rewrite M1, M2 in Hx. pose proof (Hcuts x Hx) as Hc. rewrite unmap_post_maps, M1.
    unfold covered in Hc |- *. apply existsb_exists in Hc as (e & He & Hxe). apply existsb_exists. exists e. split; [| exact Hxe].
    unfold map_remove. apply filter_In. split; [exact He|]. apply negb_true_iff. unfold bv_eqb. apply Z.eqb_neq. intros Eb.
    assert (e = (A, nW)) by (apply (seps_same_base _ e (A, nW) Hseps Hpos He HinE); apply bv_eq; exact Eb). subst e.
    apply negb_true_iff in Hout. unfold in_iv, in_rng, B, S in Hxe, Hout. cbn [fst snd] in Hxe. rewrite EnW in Hout. fold A in Hout. congruence.
  - rewrite unmap_post_reserved, M1. exact Hres.
  - rewrite unmap_post_limit, M1. exact Hlim.
  - unfold alloc_top. rewrite unmap_post_init_sp, M1. exact Htop.
  - rewrite unmap_post_maps, M1. cbn [map app] in Hperm.
    apply (Permutation_cons_inv (a := (A, nW))). eapply perm_trans; [| exact Hperm].
    apply Permutation_sym. apply map_remove_perm; assumption.
  - apply Forall_forall. intros c Hc x Hx. rewrite (unmap_post_cuts mo1 p n Hwf1), M1, M2.
    rewrite (proj1 (Forall_forall _ _) Hback' c Hc x Hx). reflexivity.
  - exact Hpal.
  - exact Hsane'.
  -
    apply Forall_forall. intros c Hc q Hq.
    pose proof (proj1 (Forall_forall _ _) Hinner' c Hc q Hq) as Hqm.
    pose proof (proj1 (Forall_forall _ _) Hsane' c Hc) as CSc. pose proof CSc as (C1 & C2 & C3 & C4 & C5 & C6).
    destruct (inner_pages_in (fst c) (snd c) q ltac:(lia) ltac:(lia) Hq) as (z & -> & Z1 & Z2 & Z3).

    assert (Hap : fst c + snd c <= p \/ p + n <= fst c).
    { assert (HcE : In (sc_ent c) (vm_maps (m_vmmaps mo))).
      { apply (Permutation_in _ (Permutation_sym Hperm)). cbn [map app]. right. apply in_or_app. left. apply in_map. exact Hc. }
      destruct (sc_ent_unsigned _ CSc) as [Ec1 Ec2].
      destruct (LZPages.seps_in_disjoint _ (sc_ent c) (A, nW) Hseps HcE HinE) as [Eq|D].
      - exfalso.
        assert (Hs2 : seps ((A, nW) :: (map sc_ent l' ++ vb_maps Bs))) by (exact (seps_perm _ _ Hperm Hseps)).
        apply (seps_head_notin _ _ Hs2); [unfold S; cbn [snd]; lia|]. rewrite <- Eq. apply in_or_app. left. apply in_map. exact Hc.
      - unfold iv_disjoint in D. cbn [fst snd] in D. rewrite Ec1, Ec2, EA, EN in D. lia. }
    assert (Hz : 0 <= z < 0x10007fff8000).
    { pose proof (Z.div_pos (fst c) 8 ltac:(lia) ltac:(lia)).
      pose proof (Z.div_le_mono (fst c + snd c) (2^47) 8 ltac:(lia) C3). change (2^47 / 8) with (2^44) in *. unfold shZ, SHOFF in *. lia. }
    assert (Hzlo : 0x7fff8000 <= z) by (pose proof (Z.div_pos (fst c) 8 ltac:(lia) ltac:(lia)); unfold shZ, SHOFF in *; lia).
    unfold unmap_post, with_mmap_destroyed. rewrite m_vm_materialized_vm_forget_range, m_vm_materialized_with_vmmaps. apply filter_In. split.
    +
      unfold mo1, flush_post. destruct (inner_range p n) as [[pb pe]|] eqn:Ei; [| exact Hqm].
      cbn. apply LZPages.cut_pages_in. split; [exact Hqm|]. rewrite fg_lit by lia.
      unfold inner_range in Ei. cbv zeta in Ei.
      destruct (Z.leb_spec (pgdnZ (shZ (p + n))) (pgupZ (shZ p))) as [|Hlt]; [discriminate|]. injection Ei as <- <-.
      assert (Hs : 0 <= shZ p) by (unfold shZ, SHOFF; pose proof (Z.div_pos p 8 ltac:(lia) ltac:(lia)); lia).
      assert (He : 0 <= shZ (p + n)) by (unfold shZ, SHOFF; pose proof (Z.div_pos (p + n) 8 ltac:(lia) ltac:(lia)); lia).
      destruct (pg_facts (shZ p) Hs) as (_ & P2 & _). destruct (pg_facts (shZ (p + n)) He) as (E1 & _).
      destruct Hap as [Hap|Hap]; [left; pose proof (shZ_mono _ _ Hap)| right; pose proof (shZ_mono _ _ Hap)]; lia.
    + unfold page_outside_range. rewrite EnW. fold A. rewrite EA, EN. rewrite fg_lit by lia.
      apply negb_true_iff. apply andb_false_iff. destruct S6; [right; apply Z.ltb_ge| left; apply Z.leb_gt]; lia.
  - pose proof (bv_unsigned_in_range 64 (lenW n)) as Rn. destruct Hivs as (_ & Wn & _).
    split; (unfold unmap_post, with_mmap_destroyed; rewrite m_vmmaps_vm_forget_range, m_vmmaps_with_vmmaps; cbn [vm_noaccess];
            rewrite M1; apply maps_subtract_off_band; [exact Wn| lia| assumption]).
  - pose proof (hull_inner_edge p n ltac:(lia) ltac:(lia)) as Hedge.
    cbn [length chunks_weight fold_right fst snd] in Hused. fold (chunks_weight l') in Hused.
    unfold hull_bytes in Hused. change (pages_of (shw_lo SHADOW_OFF p) (shw_hi SHADOW_OFF p n)) with (hull_pages p n) in Hused.
    rewrite Nat2Z.inj_succ in Hused. lia.
Qed.

#[using="Type"] Theorem link_dealloc : forall v mo p n l' (Q : exc unit -> Model -> Prop),
  base_ok -> LINK v mo -> Permutation (va_chunks v) ((p, n) :: l') ->
  (forall mo', LINK (mkVA (va_prim v) l' (va_nsec v) (va_aux v)) mo' -> m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo -> Q (Ok tt) mo') ->
  stwfL (ebind (flush_treeL p n) (fun _ => t_unmap p n)) mo Q.
Proof.
  intros v mo p n l' Q BO LK HP HQ.
  apply (link_dealloc_head (mkVA (va_prim v) ((p, n) :: l') (va_nsec v) (va_aux v)) mo p n l' Q BO (LINK_perm v mo _ LK HP) eq_refl).
  exact HQ.
Qed.

#[using="Type"] Lemma vm_backing_used_vm : forall mo mo', m_vm mo' = m_vm mo -> vm_backing_used mo' = vm_backing_used mo.
Proof. intros mo mo' E. unfold vm_backing_used, m_vmmaps, m_vm_lazy, m_vm_materialized. rewrite E. reflexivity. Qed.

#[using="Type"] Lemma LINK_vm_eq : forall v mo mo', m_vm mo' = m_vm mo -> LINK v mo -> LINK v mo'.
Proof.
  intros v mo mo' E [Hwf Hpos Hcuts Hres Hlim Htop Hperm Hback Hpal Hsane Hinner Hna Hused].
  assert (E1 : m_vmmaps mo' = m_vmmaps mo) by (unfold m_vmmaps; rewrite E; reflexivity).
  assert (E2 : m_vm_lazy mo' = m_vm_lazy mo) by (unfold m_vm_lazy; rewrite E; reflexivity).
  assert (E3 : m_vm_materialized mo' = m_vm_materialized mo) by (unfold m_vm_materialized; rewrite E; reflexivity).
  constructor.
  - destruct Hwf as [(W1 & W2 & W3 & W4) W5]. unfold vmwf, model_ivs_wf. rewrite E1, E2. repeat split; assumption.
  - unfold pos_maps. rewrite E1. exact Hpos.
  - unfold cuts_in_maps. rewrite E1, E2. exact Hcuts.
  - rewrite E1. exact Hres.
  - rewrite E1. exact Hlim.
  - rewrite E1. exact Htop.
  - rewrite E1. exact Hperm.
  - apply Forall_forall. intros c Hc. pose proof (proj1 (Forall_forall _ _) Hback c Hc) as Hb. unfold fully_backed in *. rewrite E1, E2. exact Hb.
  - exact Hpal.
  - exact Hsane.
  - rewrite E3. exact Hinner.
  - rewrite E1. exact Hna.
  - rewrite (vm_backing_used_vm mo mo' E). exact Hused.
Qed.

Definition LINKvm (v : vabs) (vm : VmState) : Prop := forall mo, m_vm mo = vm -> LINK v mo.

#[using="Type"] Lemma LINKvm_of_LINK : forall v mo, LINK v mo -> LINKvm v (m_vm mo).
Proof. intros v mo LK mo' E. exact (LINK_vm_eq v mo mo' E LK). Qed.
#[using="Type"] Lemma LINK_of_LINKvm : forall v mo, LINKvm v (m_vm mo) -> LINK v mo.
Proof. intros v mo H. exact (H mo eq_refl). Qed.

End Link.

