(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Ceiling VmGap.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.ASN Require Import AsanAcct BackingAlgebra MainExport MainFactsAsan A0Img MainEntry A0LZ.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.LZ Require Import ITreeLZ NodesLZ BridgeLZ.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAA Require Import LJ ALinkPg ALinkVm ALink.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section Init.
Context {HC : HasCeiling}.
Variables (V : nat -> Z) (sp : word) (fs : Fs.Fs) (mo : Model).
Hypothesis AM : amodel V sp fs mo.
Hypothesis CEIL : alloc_ceiling = bv_unsigned sp - 8388608.

Notation P0 := (a0_P0 V).
Notation moE := (perase P0 mo).

#[using="Type"] Lemma covered_in_ivs : forall l x, BackingAlgebra.covered l x = true <-> MainExport.in_ivs x l.
Proof.
  intros l x. unfold BackingAlgebra.covered, MainExport.in_ivs. rewrite existsb_exists. split.
  - intros (c & Hc & Hx). exists c. split; [exact Hc|]. unfold in_iv in Hx. apply andb_prop in Hx as [H1 H2].
    apply Z.leb_le in H1. apply Z.ltb_lt in H2. unfold B, S in *. lia.
  - intros (c & Hc & Hx). exists c. split; [exact Hc|]. unfold in_iv. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; unfold B, S; lia.
Qed.
#[using="sp fs AM"] Lemma moE_vmmaps : m_vmmaps moE = m_vmmaps mo. Proof. destruct mo as [fd [maps lazy mat] io fs0 proc lim tm]. reflexivity. Qed.
#[using="sp fs AM"] Lemma moE_lazy : m_vm_lazy moE = m_vm_lazy mo. Proof. destruct mo as [fd [maps lazy mat] io fs0 proc lim tm]. reflexivity. Qed.
#[using="sp fs AM"] Lemma moE_mat : m_vm_materialized moE = P0. Proof. destruct mo as [fd [maps lazy mat] io fs0 proc lim tm]. reflexivity. Qed.

#[using="sp fs AM"] Lemma init_vmwf : vmwf moE.
Proof.
  split.
  - pose proof (am_wf _ _ _ _ AM) as W. unfold model_ivs_wf in *. rewrite moE_vmmaps, moE_lazy. exact W.
  - rewrite moE_vmmaps. exact (a0_seps V sp fs mo AM).
Qed.
#[using="V sp fs AM"] Lemma kinds_off_band : forall bl n, 0 <= bl -> 0 < n -> bl + n <= 2^64 ->
  (forall a : word, bl <= bv_unsigned a < bl + n -> ~ MainExport.in_ivs (bv_unsigned a) (vm_noaccess (m_vmmaps mo))) ->
  Forall (off_band bl (bl + n)) (vm_noaccess (m_vmmaps mo)).
Proof.
  intros bl n Hbl Hn Hw K. apply Forall_forall. intros e He.
  pose proof (proj1 (Forall_forall _ _) (am_noaccess_pos _ _ _ _ AM) e He) as Pe. cbv beta in Pe.
  pose proof (proj1 (Forall_forall _ _) (am_noaccess_wf _ _ _ _ AM) e He) as We. cbv beta in We.
  unfold off_band, vlo, vhi, vsz.
  destruct (Z_le_gt_dec (bv_unsigned (fst e) + bv_unsigned (snd e)) bl) as [L|L]; [left; exact L|].
  destruct (Z_le_gt_dec (bl + n) (bv_unsigned (fst e))) as [R|R]; [right; exact R|]. exfalso.
  pose proof (bv_unsigned_in_range 64 (fst e)) as Rb. unfold bv_modulus in Rb.
  set (z := Z.max (bv_unsigned (fst e)) bl).
  assert (Hz : bl <= z < bl + n /\ bv_unsigned (fst e) <= z < bv_unsigned (fst e) + bv_unsigned (snd e)) by (unfold z; lia).
  assert (Uz : bv_unsigned (Z_to_bv 64 z) = z).
  { rewrite Z_to_bv_unsigned. apply (bv_wrap_small 64). unfold bv_modulus. change (2 ^ Z.of_N 64) with (2^64). lia. }
  apply (K (Z_to_bv 64 z)); rewrite Uz; [lia|]. exists e. split; [exact He| lia].
Qed.
#[using="V sp fs AM"] Lemma init_noacc : Forall (off_band 0x7fff7000 0x8fff7000) (vm_noaccess (m_vmmaps mo))
                   /\ Forall (off_band 0x2008fff7000 0x10007fff8000) (vm_noaccess (m_vmmaps mo)).
Proof.
  pose proof (am_kinds _ _ _ _ AM) as K. rewrite Forall_forall in K. split.
  - assert (I : In (LMap (ZLit 2147446784) 268435456 AsanPlan.AP.KRWLAZY) asan_ledger) by (unfold asan_ledger; repeat first [left; reflexivity | right]).
    pose proof (K _ I) as KK. cbn [lentry_kind_ok zv] in KK.
    change 0x8fff7000 with (0x7fff7000 + 268435456). apply kinds_off_band; [lia | lia | lia |].
    intros a Ha. exact (proj1 (KK a Ha)).
  - assert (I : In (LMap (ZLit 2201439137792) 15392894357504 AsanPlan.AP.KRWLAZY) asan_ledger) by (unfold asan_ledger; repeat first [left; reflexivity | right]).
    pose proof (K _ I) as KK. cbn [lentry_kind_ok zv] in KK.
    change 0x10007fff8000 with (0x2008fff7000 + 15392894357504). apply kinds_off_band; [lia | lia | lia |].
    intros a Ha. exact (proj1 (KK a Ha)).
Qed.
#[using="sp fs AM"] Lemma init_cuts : cuts_in_maps moE.
Proof.
  unfold cuts_in_maps. rewrite moE_vmmaps, moE_lazy. intros x Hx.
  rewrite BackingAlgebra.covered_app in Hx. apply orb_prop in Hx as [Hx|Hx].
  - apply covered_in_ivs. apply (am_noaccess_sub _ _ _ _ AM). apply covered_in_ivs. exact Hx.
  - apply covered_in_ivs in Hx. destruct Hx as (r & Hr & Hx). exact (a0_lazy_in_maps V sp fs mo AM r x Hr Hx).
Qed.

#[using="sp fs AM"] Lemma init_pos : pos_maps moE.
Proof.
  unfold pos_maps. rewrite moE_vmmaps. eapply Forall_impl; [|exact (am_bounds _ _ _ _ AM)]. cbv beta. intros q (Q & _). exact Q.
Qed.

#[using="sp fs AM"] Lemma init_used : vm_backing_used moE <= asan_eager + asan_abytes.
Proof.
  rewrite vm_backing_used_perase. pose proof (am_nonlazy _ _ _ _ AM) as E. pose proof (am_abytes _ _ _ _ AM) as Ab.
  unfold a0_P0. pose proof (ivz_bytes_pages _ (am_allow_wf _ _ _ _ AM)) as (E1 & E2 & E3). rewrite E1. unfold page_size.
  assert (X : ivz_bytes (allow_of ASHOFF V asan_vis) / 4096 * 4096 = ivz_bytes (allow_of ASHOFF V asan_vis)).
  { pose proof (Z.div_mod (ivz_bytes (allow_of ASHOFF V asan_vis)) 4096 ltac:(lia)) as DM. rewrite E3 in DM. lia. }
  lia.
Qed.
Definition vb0 (space : Z) : vmbase := mkVB (vm_maps (m_vmmaps mo)) (asan_eager + asan_abytes) space 137478443008 16.

#[using="sp fs AM CEIL"] Theorem link_init : forall space, LINK (vb0 space) (mkVA 0 [] 0 0) moE.
Proof.
  intros space. constructor; cbn [va_prim va_chunks va_nsec va_aux vb0 vb_maps vb_used map app length].
  - exact init_vmwf.
  - exact init_pos.
  - exact init_cuts.
  - rewrite moE_vmmaps. exact (am_reserved _ _ _ _ AM).
  - rewrite moE_vmmaps. exact (am_limit _ _ _ _ AM).
  - rewrite moE_vmmaps. unfold alloc_top. rewrite (am_top _ _ _ _ AM), CEIL. reflexivity.
  - rewrite moE_vmmaps. apply Permutation_refl.
  - constructor.
  - split; [reflexivity | lia].
  - constructor.
  - constructor.
  - rewrite moE_vmmaps. exact init_noacc.
  - pose proof init_used. unfold chunks_weight. cbn [fold_right]. change (0 / 8) with 0. lia.
Qed.
Notation HIGHMEM := 0x10007fff8000%Z.
Notation eLOW := (Z_to_bv 64 0x7fff7000, Z_to_bv 64 0x10000000).
Notation eGAP := (Z_to_bv 64 0x8fff7000, Z_to_bv 64 0x20000000000).
Notation eHIGH := (Z_to_bv 64 0x2008fff7000, Z_to_bv 64 0xdfff0001000).

#[using="Type"] Lemma wa_lit : forall z, 0 <= z < 2^64 -> bv_unsigned (wa z) = z.
Proof. intros z Hz. unfold wa. rewrite Z_to_bv_unsigned. apply (bv_wrap_small 64). unfold bv_modulus. change (2 ^ Z.of_N 64) with (2^64). lia. Qed.

#[using="Type"] Lemma gap_step : forall c (b n : word) l k B N, bv_unsigned n <= k ->
  (bytes_above c l <= B /\ Z.of_nat (nabove c l) <= N) ->
  bytes_above c ((b, n) :: l) <= k + B /\ Z.of_nat (nabove c ((b, n) :: l)) <= 1 + N.
Proof.
  intros c b n l k B N Hk [HB HN]. unfold nabove in *. cbn [bytes_above List.filter]. unfold vsz. cbn [snd].
  pose proof (bv_unsigned_in_range 64 n). destruct (c <? vhi (b, n)); cbn [length]; split; lia.
Qed.
#[using="Type"] Lemma gap_weaken : forall c l B N B' N', (bytes_above c l <= B /\ Z.of_nat (nabove c l) <= N) -> B <= B' -> N <= N' ->
  bytes_above c l <= B' /\ Z.of_nat (nabove c l) <= N'.
Proof. intros c l B N B' N' [H1 H2] HB HN. split; lia. Qed.

Ltac ledger_cases LD :=
  repeat (cbn [ledger_den] in LD; match type of LD with
         | ex _ => let E := fresh "E" in destruct LD as (? & E & LD); subst
         | _ \/ _ => destruct LD as [LD | (? & ? & ? & ? & LD)]; subst
         end);
  cbn [ledger_den zv] in LD; subst;
  repeat match goal with x : (word * word)%type |- _ => destruct x as [? ?] end; cbn [snd] in *.

#[using="Type"] Lemma ledger_gap : forall maps, ledger_den V asan_ledger maps ->
  bytes_above HIGHMEM maps <= 137472315392 /\ Z.of_nat (nabove HIGHMEM maps) <= 15.
Proof.
  intros maps LD. unfold asan_ledger in LD.
  assert (TAIL : forall t, t = [eHIGH; eGAP; eLOW] -> bytes_above HIGHMEM t <= 0 /\ Z.of_nat (nabove HIGHMEM t) <= 0).
  { intros t ->. split; vm_compute; intros X; discriminate X. }
  ledger_cases LD.
  all: eapply gap_weaken;
       [ repeat (lazymatch goal with |- bytes_above _ ((wa (zv V (ZLit _)), _) :: _) <= _ /\ _ => fail | _ => idtac end;
                 eapply gap_step; [ first [ eassumption | rewrite wa_lit by lia; apply Z.le_refl ] | ]); apply TAIL; reflexivity
       | lia | lia ].
Qed.
Notation e208 := (wa (zv V (ZMul (ZLit 4096) (ZV 208))), wa 137439023104).

#[using="sp fs AM"] Lemma In_fixed : In eLOW (vm_maps (m_vmmaps mo)) /\ In eGAP (vm_maps (m_vmmaps mo)) /\ In eHIGH (vm_maps (m_vmmaps mo))
                 /\ In e208 (vm_maps (m_vmmaps mo)).
Proof.
  pose proof (am_maps _ _ _ _ AM) as LD.
  repeat split.
  - exact (ledger_den_In V asan_ledger _ (ZLit 2147446784) 268435456 AsanPlan.AP.KRWLAZY LD ltac:(unfold asan_ledger; repeat first [left; reflexivity | right])).
  - exact (ledger_den_In V asan_ledger _ (ZLit 2415882240) 2199023255552 AsanPlan.AP.KNONELAZY LD ltac:(unfold asan_ledger; repeat first [left; reflexivity | right])).
  - exact (ledger_den_In V asan_ledger _ (ZLit 2201439137792) 15392894357504 AsanPlan.AP.KRWLAZY LD ltac:(unfold asan_ledger; repeat first [left; reflexivity | right])).
  - exact (ledger_den_In V asan_ledger _ (ZMul (ZLit 4096) (ZV 208)) 137439023104 AsanPlan.AP.KRW LD ltac:(unfold asan_ledger; repeat first [left; reflexivity | right])).
Qed.

#[using="Type"] Lemma fixed_vals : vlo eLOW = 0x7fff7000 /\ vhi eLOW = 0x8fff7000 /\ vlo eGAP = 0x8fff7000 /\ vhi eGAP = 0x2008fff7000
                   /\ vlo eHIGH = 0x2008fff7000 /\ vhi eHIGH = HIGHMEM.
Proof. repeat split; vm_compute; reflexivity. Qed.

#[using="V sp fs AM"] Lemma band_free : forall a n : word, 0 < bv_unsigned n -> region_free (vm_maps (m_vmmaps mo)) a n = true ->
  bv_unsigned a + bv_unsigned n <= 0x7fff7000 \/ HIGHMEM <= bv_unsigned a.
Proof.
  intros a n Hn RF. destruct In_fixed as (I1 & I2 & I3 & _).
  pose proof (region_free_In _ _ _ _ _ RF I1) as O1. pose proof (region_free_In _ _ _ _ _ RF I2) as O2. pose proof (region_free_In _ _ _ _ _ RF I3) as O3.
  unfold iv_overlap in O1, O2, O3.
  change (bv_unsigned (Z_to_bv 64 0x7fff7000)) with 0x7fff7000 in O1. change (bv_unsigned (Z_to_bv 64 0x10000000)) with 0x10000000 in O1.
  change (bv_unsigned (Z_to_bv 64 0x8fff7000)) with 0x8fff7000 in O2. change (bv_unsigned (Z_to_bv 64 0x20000000000)) with 0x20000000000 in O2.
  change (bv_unsigned (Z_to_bv 64 0x2008fff7000)) with 0x2008fff7000 in O3. change (bv_unsigned (Z_to_bv 64 0xdfff0001000)) with 0xdfff0001000 in O3.
  apply andb_false_iff in O1, O2, O3. rewrite !Z.ltb_ge in O1, O2, O3. lia.
Qed.
#[using="sp fs mo AM CEIL"] Lemma e208_high : HIGHMEM <= vlo e208 /\ vhi e208 <= alloc_ceiling /\ vsz e208 = 137439023104.
Proof.
  destruct In_fixed as (I1 & I2 & I3 & I4). destruct fixed_vals as (F1 & F2 & F3 & F4 & F5 & F6).
  pose proof (a0_seps V sp fs mo AM) as SP.
  assert (SZ : vsz e208 = 137439023104) by (unfold vsz; cbn [snd]; apply wa_lit; lia).
  pose proof (proj1 (Forall_forall _ _) (am_bounds _ _ _ _ AM) _ I4) as (B1 & _ & _ & B4 & _ & B6). cbn [fst snd] in B1, B4, B6.
  assert (D : forall q, In q (vm_maps (m_vmmaps mo)) -> vlo q <> vlo e208 -> vhi e208 <= vlo q \/ vhi q <= vlo e208).
  { intros q Hq Hne. destruct (LZPages.seps_in_disjoint _ _ _ SP I4 Hq) as [E|Dj]; [exfalso; apply Hne; rewrite <- E; reflexivity|].
    unfold NodesLZ.iv_disjoint in Dj. unfold vhi, vlo, vsz. exact Dj. }
  unfold vhi, vlo, vsz in *. cbn [fst snd] in *. rewrite SZ in *.
  change (bv_unsigned (Z_to_bv 64 0x7fff7000)) with 0x7fff7000 in *. change (bv_unsigned (Z_to_bv 64 0x10000000)) with 0x10000000 in *.
  change (bv_unsigned (Z_to_bv 64 0x8fff7000)) with 0x8fff7000 in *. change (bv_unsigned (Z_to_bv 64 0x20000000000)) with 0x20000000000 in *.
  change (bv_unsigned (Z_to_bv 64 0x2008fff7000)) with 0x2008fff7000 in *. change (bv_unsigned (Z_to_bv 64 0xdfff0001000)) with 0xdfff0001000 in *.
  pose proof (D _ I1) as D1. pose proof (D _ I2) as D2. pose proof (D _ I3) as D3. cbn [fst snd] in D1, D2, D3.
  change (bv_unsigned (Z_to_bv 64 0x7fff7000)) with 0x7fff7000 in *. change (bv_unsigned (Z_to_bv 64 0x10000000)) with 0x10000000 in *.
  change (bv_unsigned (Z_to_bv 64 0x8fff7000)) with 0x8fff7000 in *. change (bv_unsigned (Z_to_bv 64 0x20000000000)) with 0x20000000000 in *.
  change (bv_unsigned (Z_to_bv 64 0x2008fff7000)) with 0x2008fff7000 in *. change (bv_unsigned (Z_to_bv 64 0xdfff0001000)) with 0xdfff0001000 in *.
  rewrite CEIL. split; [|split; [lia | reflexivity]].

  destruct (Z.eq_dec 0x7fff7000 (bv_unsigned (wa (zv V (ZMul (ZLit 4096) (ZV 208)))))) as [E1|N1].
  { exfalso.
    destruct (LZPages.seps_in_disjoint _ _ _ SP I4 I1) as [E|Dj].
    - apply (f_equal (fun p => bv_unsigned (snd p))) in E. cbn [snd] in E. rewrite SZ in E. vm_compute in E. discriminate E.
    - unfold NodesLZ.iv_disjoint in Dj. cbn [fst snd] in Dj. rewrite SZ in Dj.
      change (bv_unsigned (Z_to_bv 64 0x7fff7000)) with 0x7fff7000 in Dj. change (bv_unsigned (Z_to_bv 64 0x10000000)) with 0x10000000 in Dj. lia. }
  destruct (Z.eq_dec 0x8fff7000 (bv_unsigned (wa (zv V (ZMul (ZLit 4096) (ZV 208)))))) as [E2|N2].
  { exfalso. destruct (LZPages.seps_in_disjoint _ _ _ SP I4 I2) as [E|Dj].
    - apply (f_equal (fun p => bv_unsigned (snd p))) in E. cbn [snd] in E. rewrite SZ in E. vm_compute in E. discriminate E.
    - unfold NodesLZ.iv_disjoint in Dj. cbn [fst snd] in Dj. rewrite SZ in Dj.
      change (bv_unsigned (Z_to_bv 64 0x8fff7000)) with 0x8fff7000 in Dj. change (bv_unsigned (Z_to_bv 64 0x20000000000)) with 0x20000000000 in Dj. lia. }
  destruct (Z.eq_dec 0x2008fff7000 (bv_unsigned (wa (zv V (ZMul (ZLit 4096) (ZV 208)))))) as [E3|N3].
  { exfalso. destruct (LZPages.seps_in_disjoint _ _ _ SP I4 I3) as [E|Dj].
    - apply (f_equal (fun p => bv_unsigned (snd p))) in E. cbn [snd] in E. rewrite SZ in E. vm_compute in E. discriminate E.
    - unfold NodesLZ.iv_disjoint in Dj. cbn [fst snd] in Dj. rewrite SZ in Dj.
      change (bv_unsigned (Z_to_bv 64 0x2008fff7000)) with 0x2008fff7000 in Dj. change (bv_unsigned (Z_to_bv 64 0xdfff0001000)) with 0xdfff0001000 in Dj. lia. }
  specialize (D1 N1). specialize (D2 N2). specialize (D3 N3). lia.
Qed.
#[using="sp fs AM CEIL"] Theorem base_ok_init : forall space, vlo e208 <= space -> space + K_SPACE1 <= vhi e208 -> base_ok (vb0 space).
Proof.
  intros space S1 S2. destruct In_fixed as (I1 & I2 & I3 & I4). destruct e208_high as (H1 & H2 & H3).
  constructor; cbn [vb0 vb_maps vb_space vb_gapB vb_gapN].
  - exists e208. split; [exact I4|]. split; [exact S1 | exact S2].
  - lia.
  - lia.
  - exact band_free.
  - intros n Hn. destruct (ledger_gap _ (am_maps _ _ _ _ AM)) as [GB GN].
    pose proof (gap_cost_le n HIGHMEM (vm_maps (m_vmmaps mo)) 137472315392 15 Hn GB GN). lia.
  - exact I1.
  - exact I3.
Qed.
End Init.
