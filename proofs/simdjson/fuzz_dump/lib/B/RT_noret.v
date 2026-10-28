(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS MState.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout RT_iface RT_iface5 D_defs D_kit R_cache_defs R_prim_defs R_glue_defs R_thread R_m2s R_poison R_leaves R_setshadow R_fs_defs R_tlsgetaddr R_noret R_prim_kit RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep RT_facts RT_geo0 RT_release RT_stackmalloc RT_freelift D_clx RT_anndefs RT_maltail RT_setshadow RT_artfacts RT_win.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.
Notation mem := (word -> option byte).

Lemma rw_C1_of_u8arr : forall (m : mem) A b, u8arr bsegs m A [b] -> rw_cells bsegs m A [C1 b].
Proof.
  intros m A b [Hb Hw]. split; [split; [cbn; split; [reflexivity | exact I]|]|]; cbn [cells_bytes cbytes cells_size csize app Nat.add]; [exact Hb | exact Hw].
Qed.
Lemma u8arr_of_rw_C1 : forall (m : mem) A b, rw_cells bsegs m A [C1 b] -> u8arr bsegs m A [b].
Proof. intros m A b [[_ Hb] Hw]. split; [exact Hb | exact Hw]. Qed.

Section Gen. Context {G0 : OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A.Shadow.GW}.

Lemma munch_shrink_shadow : forall Σ (m m' : mem) (b : Z) (k : nat) W,
  ART_A Σ m -> l_ACEIL (lay Σ) <= b -> b mod 8 = 0 -> b + 8 * Z.of_nat k <= 2 ^ 47 ->
  munch ((shad b, shad b + Z.of_nat k) :: W) m m' ->
  rw_cells bsegs m' (shad b) [CB k (repeat (Z_to_bv 8 0) k)] ->
  munch W m m'.
Proof.
  intros Σ m m' b k W HA Hlo Hb8 Hhi MU SH x Hx.
  destruct (Z_lt_le_dec (bv_unsigned x) (shad b)) as [L|GE]; [apply MU; cbn; split; [lia | exact Hx]|].
  destruct (Z_lt_le_dec (bv_unsigned x) (shad b + Z.of_nat k)) as [L2|GE2]; [|apply MU; cbn; split; [lia | exact Hx]].

  pose proof (ART_shadow Σ m HA) as (Z0 & _). pose proof (rta_sp0_range Σ m HA) as SR. pose proof (rta_sp0_win Σ m HA) as SW.
  assert (AC8 : l_ACEIL (lay Σ) mod 8 = 0).
  { pose proof (rta_sp0 Σ m HA) as ((_ & _) & M16). unfold l_ACEIL, rtA_sp0, STACK_WIN in *.
    apply Z.mod_divide in M16; [|lia]. destruct M16 as [q Hq]. apply Z.mod_divide; [lia|]. exists (2 * q - 2 ^ 20). lia. }
  unfold l_ACEIL, rtA_sp0, STACK_WIN, SEGTOP_A, USTACK_TOP in *.
  set (i := Z.to_nat (bv_unsigned x - shad b)).
  assert (Ex : x = wa (shad b + Z.of_nat i)) by (unfold wa, i; rewrite Z2Nat.id by lia; replace (shad b + (bv_unsigned x - shad b)) with (bv_unsigned x) by lia; symmetry; apply Z_to_bv_bv_unsigned).
  assert (NS : seg_rom bsegs x = None).
  { apply fn_seg_rom_off. right. unfold img_hull_hi. unfold shad, SHB in *. lia. }
  assert (V' : mrd bsegs m' x = Some (Z_to_bv 8 0)).
  { destruct SH as [[_ HB] _]. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB. destruct HB as (_ & _ & HB).
    rewrite repeat_length in HB. rewrite Ex. rewrite (HB i ltac:(unfold i; lia)). apply nth_error_repeat. unfold i; lia. }
  assert (V : mrd bsegs m x = Some (Z_to_bv 8 0)).
  { destruct Z0 as (_ & _ & HB). unfold zrun in HB. rewrite repeat_length in HB.
    set (j := Z.to_nat (bv_unsigned x - shad (l_sp0 (lay Σ) - 8388608))).
    assert (Hj : (j < Z.to_nat ((2 ^ 47 - (l_sp0 (lay Σ) - 8388608)) / 8))%nat).
    { unfold j. unfold shad in *. apply Nat2Z.inj_lt. rewrite !Z2Nat.id by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations. lia. }
    assert (Ex2 : x = wa (shad (l_sp0 (lay Σ) - 8388608) + Z.of_nat j)).
    { unfold wa, j. rewrite Z2Nat.id by (unfold shad in *; Z.div_mod_to_equations; lia).
      replace (shad (l_sp0 (lay Σ) - 8388608) + (bv_unsigned x - shad (l_sp0 (lay Σ) - 8388608))) with (bv_unsigned x) by lia. symmetry; apply Z_to_bv_bv_unsigned. }
    rewrite Ex2, (HB j Hj). unfold z8. apply nth_error_repeat. exact Hj. }
  unfold mrd in V, V'. rewrite NS in V, V'. destruct (m x); destruct (m' x); congruence.
Qed.

Section AfterNoret.
Variables (c : Z) (Σ : rtsA) (m m' : mem) (lo usp : Z).
Hypothesis HA : ART_A Σ m.
Hypothesis HC : credit Σ = c.
#[local] Notation L := (lay Σ).
#[local] Notation FSB := (l_FSB (lay Σ)).
#[local] Notation Wn := [(l_FSB (lay Σ) + 0x60, l_FSB (lay Σ) + 0x61); (lo, usp)].
Hypothesis MU : munch Wn m m'.
Hypothesis WM : wmono bsegs m m'.

Variable gbit : bool.
Hypothesis GB : u8arr bsegs m' (FSB + 0x60) [Z_to_bv 8 (if gbit then 1 else 0)].
Hypothesis Hlo : l_ACEIL L <= lo.
Hypothesis Husp : usp <= USTACK_TOP.

Lemma nr_fsb : grant_ok L FSB 0xb09000.
Proof. exact (geo_grant Σ m HA FSB 0xb09000 ltac:(unfold startup_grants; right; right; right; right; right; left; reflexivity)). Qed.
Lemma nr_aceil : 2 ^ 44 + SHB <= l_ACEIL L /\ l_ACEIL L <= 2 ^ 47 /\ SEGTOP_A <= l_ACEIL L.
Proof. pose proof (rta_sp0_win Σ m HA) as X. pose proof (rta_sp0_range Σ m HA) as Y. unfold l_ACEIL, rtA_sp0, STACK_WIN, SHB, USTACK_TOP in *. lia. Qed.

Lemma nr_img : forall a n, 0x10000 <= a -> a + n <= SEGTOP_A -> disjoint_from CS_W a n -> disjoint_from Wn a n.
Proof.
  intros a n H1 H2 _. pose proof nr_fsb as (G1 & _ & G3 & _ & G5). pose proof nr_aceil as (_ & _ & A3). cbn. unfold SEGTOP_A in *.
  split; [lia|]. split; [lia | exact I].
Qed.
Lemma nr_grant : forall b gn a n, In (b, gn) (startup_grants L) -> apart b gn (l_PRB L) 0x2000011000 -> apart b gn FSB 0xb09000 ->
  b <= a -> a + n <= b + gn -> disjoint_from Wn a n.
Proof.
  intros b gn a n Hin _ HF H1 H2. pose proof (geo_grant Σ m HA b gn Hin) as (_ & _ & G3 & _). cbn. unfold apart in HF.
  split; [lia|]. split; [lia | exact I].
Qed.
Lemma nr_shad : forall lo' hi' a n, lo' mod 8 = 0 -> hi' mod 8 = 0 -> 0 <= lo' -> hi' <= 2 ^ 47 -> shad lo' <= a -> a + n <= shad hi' ->
  disjoint_from Wn a n.
Proof.
  intros lo' hi' a n _ _ H0 H47 H1 H2. pose proof nr_fsb as (_ & _ & _ & G4 & _). pose proof nr_aceil as (A1 & _). cbn.
  assert (Hs : shad hi' <= 2 ^ 44 + SHB) by (unfold shad; assert (hi' / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia); lia).
  assert (Hs0 : SHB <= shad lo') by (unfold shad; pose proof (Z.div_pos lo' 8 ltac:(lia) ltac:(lia)); lia).
  unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *. split; [lia|]. split; [lia | exact I].
Qed.
Lemma nr_fsb' : forall a n, FSB <= a -> a + n <= FSB + 0xb09000 -> (a + n <= FSB + 0x60 \/ FSB + 0x61 <= a) -> disjoint_from Wn a n.
Proof. intros a n H1 H2 H3. pose proof nr_fsb as (_ & _ & G3 & _). cbn. split; [lia|]. split; [lia | exact I]. Qed.

Lemma nr_but_fs : ART_but_fs Σ m'.
Proof.
  apply (ART_transport_but_fs ([(FSB, FSB + 0xb09000)] ++ [(l_ACEIL L, USTACK_TOP)]) Σ m m' HA); [| exact WM | exact (art_avoid_but_fs_app _ _ Σ (fsb_avoid Σ m HA) (stack_avoid Σ m HA))].
  eapply munch_weaken; [| exact MU]. intros x Hx. cbn [app outside] in Hx |- *. destruct Hx as (X1 & X2 & _). split; [lia|]. split; [lia | exact I].
Qed.

Lemma nr_fs_cls : forall k, (k = 5 \/ k = 0 \/ k = 4 \/ k = 1 \/ k = 3 \/ k = 2)%nat -> fs_cls_avoid Wn FSB (Z.of_nat k) (fs_of Σ k).
Proof.
  intros k Hk. pose proof (geo_wf Σ m HA) as (_ & _ & _ & _ & _ & HF & _). destruct HF as (F0 & F2 & F4 & Fc1 & Fc3 & Fc2 & HFr & _).
  assert (Hwf : flags_ok (Z.of_nat k) (fss_flags (fs_of Σ k))) by (destruct Hk as [ -> | [ -> | [ -> | [ -> | [ -> | -> ] ] ] ] ]; [exact (proj1 F0) | exact (proj1 F2) | exact (proj1 F4) | exact (proj1 Fc1) | exact (proj1 Fc3) | exact (proj1 Fc2)]).
  destruct Hwf as [Hlen _].
  assert (Hc : Z.of_nat k = 5 \/ Z.of_nat k = 0 \/ Z.of_nat k = 4 \/ Z.of_nat k = 1 \/ Z.of_nat k = 3 \/ Z.of_nat k = 2) by (destruct Hk as [ -> | [ -> | [ -> | [ -> | [ -> | -> ] ] ] ] ]; cbn; lia).
  pose proof nr_fsb as (G1 & G2 & G3 & G4 & G5).
  unfold fs_cls_avoid. split; [apply nr_fsb'; destruct Hc as [ -> | [ -> | [ -> | [ -> | [ -> | -> ] ] ] ] ]; lia|]. split.
  - apply nr_fsb'; [unfold fl_base, flags_off; destruct Hc as [ -> | [ -> | [ -> | [ -> | [ -> | -> ] ] ] ] ]; cbn; lia| |].
    + rewrite Hlen. unfold fl_base, flags_off, NF. destruct Hc as [ -> | [ -> | [ -> | [ -> | [ -> | -> ] ] ] ] ]; cbn; lia.
    + right. unfold fl_base, flags_off. destruct Hc as [ -> | [ -> | [ -> | [ -> | [ -> | -> ] ] ] ] ]; cbn; lia.
  - intros p Hp Hfl.
    pose proof (frame_addr_range FSB (Z.of_nat k) p Hc Hp) as (R1 & R2). unfold kFakeStackSize in R2.
    split; [apply nr_fsb'; lia|].
    assert (M1 : frame_addr FSB (Z.of_nat k) p mod 8 = 0).
    { unfold frame_addr, fsz. apply (mod8_of _ 64 ltac:(lia)); [|exists 8; reflexivity].
      apply Z.mod_divide in G2; [|lia]. apply Z.mod_divide; [lia|]. destruct G2 as [q Hq]. rewrite Hq.
      destruct Hc as [E|[E|[E|[E|[E|E]]]]]; rewrite E; cbn; [exists (q * 64 + 576 + 5 * 2 ^ 14 + 32 * p) | exists (q * 64 + 576 + 0 * 2 ^ 14 + 1 * p) | exists (q * 64 + 576 + 4 * 2 ^ 14 + 16 * p) | exists (q * 64 + 576 + 1 * 2 ^ 14 + 2 * p) | exists (q * 64 + 576 + 3 * 2 ^ 14 + 8 * p) | exists (q * 64 + 576 + 2 * 2 ^ 14 + 4 * p)]; lia. }
    assert (M2 : fsz (Z.of_nat k) mod 8 = 0) by (unfold fsz; destruct Hc as [ -> | [ -> | [ -> | [ -> | [ -> | -> ] ] ] ] ]; reflexivity).
    apply Z.mod_divide in M1; [|lia]. destruct M1 as [a0 E1]. apply Z.mod_divide in M2; [|lia]. destruct M2 as [b0 E2].
    apply (nr_shad (frame_addr FSB (Z.of_nat k) p) (frame_addr FSB (Z.of_nat k) p + fsz (Z.of_nat k)));
      [rewrite E1; apply Z.mod_mul; lia | rewrite E1, E2, <- Z.mul_add_distr_r; apply Z.mod_mul; lia | lia | | lia |].
    + pose proof nr_aceil as (_ & A2 & _). lia.
    + unfold shad. rewrite E1, E2, <- Z.mul_add_distr_r, !Z.div_mul by lia. lia.
Qed.

Lemma nr_fs_rep_gen : forall Gx : OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A.Shadow.GW,
  (@gw Gx = false -> gbit = true -> frames Σ = []) -> (@gw Gx = true -> @gcredit Gx Σ = @gwc Gx) -> @fs_rep Gx Σ m'.
Proof.
  intros Gx HG1 HG2.
  pose proof nr_fsb as (G1 & G2 & G3 & G4 & G5). pose proof nr_aceil as (A1 & A2 & A3).
  pose proof (ART_wf Σ m HA) as (_ & _ & _ & _ & _ & HFw & _). destruct HFw as (F0w & F2w & F4w & Fc1w & Fc3w & Fc2w & HFr & _).
  pose proof (ART_fs Σ m HA) as FS.
  destruct FS as (F1 & F05 & F00 & F04 & F01 & F03 & F02 & FT & (dtvbeg & Hdb & TG) & (tb & te & TT) & FB).

  destruct F1 as ((g & CG & _ & _) & OFL). unfold fs_constg in CG.
  apply (proj1 (rwc_app bsegs m _ [C8 (Z_to_bv 64 20)] [C1 (Z_to_bv 8 (if g then 1 else 0))])) in CG. destruct CG as (CG8 & _).
  assert (CG8' : rw_cells bsegs m' (FSB + 0x58) [C8 (Z_to_bv 64 20)]).
  { apply (rw_cells_transport bsegs _ m m' _ _ CG8 MU WM). cbn [cells_size csize Nat.add]. apply nr_fsb'; lia. }
  assert (CG' : fs_constg FSB gbit m').
  { unfold fs_constg. apply (proj2 (rwc_app bsegs m' _ [C8 (Z_to_bv 64 20)] [C1 (Z_to_bv 8 (if gbit then 1 else 0))])). split; [exact CG8'|].
    cbn [cells_size csize Nat.add]. replace (FSB + 88 + Z.of_nat 8) with (FSB + 0x60) by lia. exact (rw_C1_of_u8arr m' _ _ GB). }
  assert (OFL' : fs_oflags_zero FSB m').
  { intros k Hk. pose proof (OFL k Hk) as X. pose proof (oflags_range k Hk) as (O1 & O2 & O3).
    apply (u8arr_transport bsegs _ m m' _ _ X MU WM). rewrite repeat_length, Z2Nat.id by lia. unfold fl_base. apply nr_fsb'; lia. }

  assert (CLS : forall k, (k = 5 \/ k = 0 \/ k = 4 \/ k = 1 \/ k = 3 \/ k = 2)%nat -> fs_cls_rep FSB (Z.of_nat k) (fs_of Σ k) m').
  { intros k Hk. exact (fs_cls_rep_transport _ _ _ _ m m' (fs_rep_cls Σ m k (ART_fs Σ m HA) Hk) MU WM (nr_fs_cls k Hk)). }

  assert (DIMG : forall a n, 0x10000 <= a -> a + n <= SEGTOP_A -> disjoint_from Wn a n).
  { intros a n H1 H2. cbn. unfold SEGTOP_A in *. split; [lia|]. split; [lia | exact I]. }
  assert (T' : rw_cells bsegs m' tpA [C8 (Z_to_bv 64 FSB)]).
  { apply (rw_cells_transport bsegs _ m m' _ _ FT MU WM). apply DIMG; unfold tpA, SEGTOP_A; cbn; lia. }
  assert (TG' : tga_cells (l_DTV L) dtvbeg m').
  { unfold tga_cells, dtls_cells in *. destruct TG as (X1 & X2 & X3 & X4 & (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8)).
    repeat (split; [eapply (rw_cells_transport bsegs _ m m'); [eassumption | exact MU | exact WM | apply DIMG;
                      unfold g_real_tls_get_addr, g_dtv_ptr, g_dtv1, g_got_common_flags, g_intercept_tls_get_addr, g_got_verbosity,
                        g_current_verbosity, g_tls_index, g_got_dtls_off, g_tls_dtls, SEGTOP_A; cbn; lia]|]).
    apply (rw_cells_transport bsegs _ m m' _ _ D8 MU WM). cbn [cells_size csize Nat.add].
    pose proof (geo_apart Σ m HA 0 4 _ _ ltac:(lia) eq_refl eq_refl) as A04. pose proof (geo_apart Σ m HA 4 5 _ _ ltac:(lia) eq_refl eq_refl) as A45.
    cbn [fst snd] in A04, A45.
    apply (nr_grant (l_DTV L) 4096); [unfold startup_grants; do 4 right; left; reflexivity | unfold apart in *; lia | exact A45 | lia | lia]. }
  assert (TT' : ttls_cells (l_T L) m' tb te).
  { unfold ttls_cells in *. apply (rw_cells_transport bsegs _ m m' _ _ TT MU WM). cbn [cells_size csize Nat.add].
    pose proof (geo_apart Σ m HA 0 2 _ _ ltac:(lia) eq_refl eq_refl) as A02. pose proof (geo_apart Σ m HA 2 5 _ _ ltac:(lia) eq_refl eq_refl) as A25.
    cbn [fst snd] in A02, A25.
    apply (nr_grant (l_T L) 4096); [unfold startup_grants; do 2 right; left; reflexivity | unfold apart in *; lia | exact A25 | lia | lia]. }

  assert (FB' : fs_busy L (frames Σ) m').
  { unfold fs_busy in *. apply Forall_forall. intros [f k] Hin. destruct (proj1 (Forall_forall _ _) FB (f, k) Hin) as (p & Hp & W1 & W2 & Cw).
    exists p. split; [exact Hp|]. split; [exact (wr_at_wmono m m' _ _ W1 WM)|]. split; [exact (wr_at_wmono m m' _ _ W2 WM)|].
    apply (rw_cells_transport bsegs _ m m' _ _ Cw MU WM). cbn [cells_size csize Nat.add fst snd]. cbn [fst snd] in Hp.
    destruct (proj1 (Forall_forall _ _) HFr (f, k) Hin) as (Hk & p' & Hp' & Hf & _). cbn [fst snd] in *.
    assert (Hc : Z.of_nat k = 5 \/ Z.of_nat k = 0 \/ Z.of_nat k = 4 \/ Z.of_nat k = 1 \/ Z.of_nat k = 3 \/ Z.of_nat k = 2) by (destruct Hk as [ -> | [ -> | [ -> | [ -> | [ -> | -> ] ] ] ] ]; cbn; lia).
    pose proof (frame_addr_range FSB (Z.of_nat k) p' Hc Hp') as (R1 & R2). unfold kFakeStackSize in R2. rewrite fs_size_fsz, Hf in *.
    assert (Hfz : 8 <= fsz (Z.of_nat k)) by (unfold fsz; destruct Hc as [ -> | [ -> | [ -> | [ -> | [ -> | -> ] ] ] ] ]; cbn; lia).
    apply nr_fsb'; lia. }
  unfold fs_rep. lazy zeta. split.
  { split; [|exact OFL']. exists gbit. split; [exact CG'|]. split; [exact HG1 | exact HG2]. }
  split; [exact (CLS 5%nat ltac:(lia))|]. split; [exact (CLS 0%nat ltac:(lia))|]. split; [exact (CLS 4%nat ltac:(lia))|]. split; [exact (CLS 1%nat ltac:(lia))|]. split; [exact (CLS 3%nat ltac:(lia))|]. split; [exact (CLS 2%nat ltac:(lia))|].
  split; [exact T'|]. split; [exists dtvbeg; split; [exact Hdb | exact TG']|]. split; [exists tb, te; exact TT' | exact FB'].
Qed.

Lemma nr_fs_rep : @fs_rep (GWt c) Σ m'.
Proof. apply nr_fs_rep_gen; [intros X; discriminate X | intros _; cbn; exact HC]. Qed.
Theorem art_after_noret : @ART_A (GWt c) Σ m'.
Proof. exact (@ART_of_but_fs (GWt c) Σ m' (ART_wf Σ m HA) nr_but_fs nr_fs_rep). Qed.

Theorem art_after_gen : forall Gx : OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A.Shadow.GW,
  (@gw Gx = false -> gbit = true -> frames Σ = []) -> (@gw Gx = true -> @gcredit Gx Σ = @gwc Gx) -> @ART_A Gx Σ m'.
Proof. intros Gx HG1 HG2. exact (@ART_of_but_fs Gx Σ m' (ART_wf Σ m HA) nr_but_fs (nr_fs_rep_gen Gx HG1 HG2)). Qed.

Lemma nr_aclient_split : forall sp x, aclient (rt_live RTA Σ) (rt_frames RTA Σ) sp x -> sp <= x \/ x < l_ACEIL L.
Proof.
  intros sp x Hx. pose proof (rta_art_facts) as AF. unfold l_ACEIL.
  pose proof (af_sp0_range RTA AF Σ m HA) as R0. pose proof (af_sp0_win RTA AF Σ m HA) as W0. cbn [rt_sp0 RTA] in R0, W0. unfold rtA_sp0 in R0, W0.
  destruct Hx as [H|[H|[H|[H|H]]]].
  - left; lia.
  - right. pose proof (client_static_range x H). unfold SEGTOP_A, STACK_WIN in *. lia.
  - right. destruct H as (p & n & Hin & Hp). pose proof (af_live_range RTA AF Σ m p n HA Hin) as X. cbn [rt_sp0 RTA] in X. unfold rtA_sp0 in X. lia.
  - right. destruct H as (f & k & Hin & Hf). pose proof (af_frames_range RTA AF Σ m f k HA Hin) as (_ & X & _). cbn [rt_sp0 RTA] in X. unfold rtA_sp0 in X.
    unfold fs_size in *. pose proof (Z.shiftl_nonneg 64 (Z.of_nat k)) as E. lia.
  - right. destruct H as (f & k & Hin & Hf). pose proof (af_frames_range RTA AF Σ m f k HA Hin) as (_ & X & _). cbn [rt_sp0 RTA] in X. unfold rtA_sp0 in X.
    unfold shad, SHB in Hf. unfold STACK_WIN, USTACK_TOP, SEGTOP_A in *. Z.div_mod_to_equations. lia.
Qed.

Lemma nr_pres : forall sp, lo <= sp -> usp <= sp -> rt_pres (rt_live RTA Σ) (rt_frames RTA Σ) sp m m'.
Proof.
  intros sp H1 H2 a Ha. apply MU. pose proof (nr_aclient_split sp (bv_unsigned a) Ha) as CS.
  cbn [rt_live rt_frames RTA] in Ha. unfold rtA_live, rtA_frames in Ha. apply aclient_vis in Ha.
  pose proof nr_fsb as (_ & _ & G3 & _).
  cbn. split; [| split; [lia | exact I]].
  intros Hx.
  assert (Hsp : rtA_sp0 Σ - STACK_WIN <= sp) by (clear - Hlo H1; unfold l_ACEIL in *; unfold rtA_sp0; lia).
  pose proof (art_avoid_client Σ m sp HA Hsp) as (_ & _ & _ & _ & _ & _ & _ & ((GA & _) & _) & _).
  assert (YY : FSB + 88 <= bv_unsigned a < FSB + 88 + 9) by (clear - Hx; lia).
  exact (W_client_cover Σ sp (bv_unsigned a) Ha (disjoint_outside _ _ _ _ GA YY)).
Qed.

End AfterNoret.

Ltac pick X := first [ exact X | exact (proj1 X) | let Y := fresh "PK" in pose proof (proj2 X) as Y; clear X; pick Y ].

Section Core.
Variables (c : Z) (Σ : rtsA) (PMc : Model -> Prop).
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z).
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.
Hypothesis HTP : tp = Z_to_bv 64 0x6ab368.
Hypothesis HA : ART_A Σ m.
Hypothesis HC : credit Σ = c.
Hypothesis MI : mem_inv bsegs m.
Hypothesis CALL : call_ok (@RTA GWf) Σ m sp lo.
Hypothesis DEPTH : rt_sp0 (@RTA GWf) Σ - bv_unsigned sp <= NORET_DEPTH.
Hypothesis TOPR : bv_unsigned sp + 0xb0 <= rt_sp0 (@RTA GWf) Σ.
#[local] Notation L := (lay Σ).
#[local] Notation FSB := (l_FSB (lay Σ)).
#[local] Notation usp := (bv_unsigned sp).

Lemma nc_facts : exists (g : byte) (shj shj2 : list byte),
  noret_cells (l_T L) FSB m /\ thread_cells (l_TCX L) (l_T L) m /\ stack_cells (l_T L) (l_top L) (l_top L - 0x800000) m /\ ps_cells m
  /\ u8arr bsegs m (FSB + 0x60) [g] /\ ro_cells bsegs m g_real_unwind_raise [C8 (Z_to_bv 64 real_unwind_raise_A)]
  /\ (l_TCX L + 0x10000 <= K_LOW_SHADOW_lo \/ K_HIGH_SHADOW_hi <= l_TCX L) /\ 0 < l_TCX L /\ l_TCX L + 0xa0 <= lo
  /\ (l_T L + 4096 <= K_LOW_SHADOW_lo \/ K_HIGH_SHADOW_hi <= l_T L) /\ 0 < l_T L /\ l_T L + 4096 <= lo
  /\ (FSB + 0xb09000 <= 0x7fff7000 \/ kHighShadowEnd < FSB) /\ 0x6cd000 <= FSB /\ FSB + 0xb09000 <= lo
  /\ l_top L mod 4096 = 0 /\ usp + 16 <= l_top L /\ l_top L <= 2 ^ 47 /\ l_top L - 0x800000 <= usp - 32
  /\ rw_cells bsegs m (shad (noret_bottom usp)) [CB (Z.to_nat ((l_top L - noret_bottom usp) / 8)) shj]
  /\ rw_cells bsegs m (shad (noret_bottom (usp - 32))) [CB (Z.to_nat ((l_top L - noret_bottom (usp - 32)) / 8)) shj2]
  /\ stk bsegs m lo usp /\ lo + 0x3020 <= usp /\ 0x6cd000 <= lo /\ kHighShadowEnd + 8 <= lo /\ usp mod 16 = 0
  /\ l_ACEIL L <= lo /\ usp <= USTACK_TOP /\ l_ACEIL L <= noret_bottom usp /\ l_ACEIL L <= noret_bottom (usp - 32)
  /\ noret_bottom usp mod 8 = 0 /\ noret_bottom (usp - 32) mod 8 = 0
  /\ noret_bottom usp <= usp - 4160 /\ noret_bottom (usp - 32) <= usp - 32 - 4160.
Proof.
  destruct CALL as (ST & LOW & LOR & SPT & SPA). cbn [rt_sp0 RTA] in LOW, DEPTH, TOPR. unfold rtA_sp0, NORET_DEPTH, RT_STACK in *.
  pose proof (ART_consts Σ m HA) as (_ & MMG & TC & _ & PS & SC & _ & ICR).
  pose proof MMG as (G60 & _ & PSZ & _).
  assert (GPU : rw_cells bsegs m 0x16e210 [C8 (Z_to_bv 64 1)]) by (pose proof ICR as X; pick X).
  assert (TF : rw_cells bsegs m (l_T L + 72) [C8 (Z_to_bv 64 FSB)]) by (pose proof ICR as X; pick X).
  assert (UR : ro_cells bsegs m 0x170170 [C8 (Z_to_bv 64 0x147724)]) by (pose proof ICR as X; pick X).
  pose proof (ART_fs Σ m HA) as (((g & CG & _) & _) & _ & _ & _ & _ & _ & _ & _ & (dtvbeg & _ & (AI & _)) & _).
  unfold fs_constg in CG. apply (proj1 (rwc_app bsegs m _ [C8 (Z_to_bv 64 20)] [C1 (Z_to_bv 8 (if g then 1 else 0))])) in CG.
  destruct CG as (_ & CG1). cbn [cells_size csize Nat.add] in CG1. replace (FSB + 88 + Z.of_nat 8) with (FSB + 0x60) in CG1 by lia.
  pose proof (geo_grant Σ m HA (l_T L) 4096 ltac:(unfold startup_grants; do 2 right; left; reflexivity)) as (T1 & _ & T3 & T4 & T5).
  pose proof (geo_grant Σ m HA (l_TCX L) 0x10000 ltac:(unfold startup_grants; do 3 right; left; reflexivity)) as (X1 & _ & X3 & X4 & X5).
  pose proof (geo_grant Σ m HA FSB 0xb09000 ltac:(unfold startup_grants; do 5 right; left; reflexivity)) as (F1 & _ & F3 & F4 & F5).
  pose proof (geo_layout Σ m HA) as ((W1 & W2) & M16 & (TL1 & TL2) & TL4 & _).
  pose proof (rta_sp0_win Σ m HA) as SW. pose proof (rta_sp0_range Σ m HA) as SR. unfold rtA_sp0 in SW, SR.
  assert (TOP47 : l_top L <= 2 ^ 47) by (clear - TL2 TL4 SR; unfold USTACK_TOP in SR; Z.div_mod_to_equations; lia).
  assert (HB1 : noret_bottom usp mod 4096 = 0 /\ usp - 4160 - 4095 <= noret_bottom usp <= usp - 4160) by (unfold noret_bottom; Z.div_mod_to_equations; lia).
  assert (HB2 : noret_bottom (usp - 32) mod 4096 = 0 /\ usp - 32 - 4160 - 4095 <= noret_bottom (usp - 32) <= usp - 32 - 4160) by (unfold noret_bottom; Z.div_mod_to_equations; lia).
  pose proof (ART_shadow Σ m HA) as (_ & SSTK & _).
  assert (AC8 : l_ACEIL L mod 8 = 0).
  { clear - M16. unfold l_ACEIL, STACK_WIN. apply Z.mod_divide in M16; [|lia]. destruct M16 as [q Hq]. apply Z.mod_divide; [lia|]. exists (2 * q - 2 ^ 20). lia. }
  assert (CARVE : forall b, l_ACEIL L <= b -> b mod 8 = 0 -> b <= l_top L -> exists bs, rw_cells bsegs m (shad b) [CB (Z.to_nat ((l_top L - b) / 8)) bs]).
  { intros b Hb1 Hb2 Hb3. apply stk_CB; [| apply Z.div_pos; lia].
    assert (E : shad b + (l_top L - b) / 8 = shad (l_top L)).
    { clear - Hb2 TL4 Hb3. unfold shad. apply Z.mod_divide in Hb2; [|lia]. destruct Hb2 as [q ->].
      apply Z.mod_divide in TL4; [|lia]. destruct TL4 as [r ->]. replace (r * 4096) with ((r * 512) * 8) by lia.
      rewrite !Z.div_mul by lia. replace (r * 512 * 8 - q * 8) with ((r * 512 - q) * 8) by lia. rewrite Z.div_mul by lia. lia. }
    rewrite E. unfold l_ACEIL, STACK_WIN, USTACK_TOP in *.
    destruct (stk_split bsegs m _ (shad b) _ SSTK ltac:(unfold shad; Z.div_mod_to_equations; lia)) as [_ X].
    exact (proj1 (stk_split bsegs m _ (shad (l_top L)) _ X ltac:(unfold shad; Z.div_mod_to_equations; lia))). }
  destruct (CARVE (noret_bottom usp) ltac:(unfold l_ACEIL, STACK_WIN in *; lia) ltac:(clear - HB1; Z.div_mod_to_equations; lia) ltac:(lia)) as (shj & SHJ).
  destruct (CARVE (noret_bottom (usp - 32)) ltac:(unfold l_ACEIL, STACK_WIN in *; lia) ltac:(clear - HB2; Z.div_mod_to_equations; lia) ltac:(lia)) as (shj2 & SHJ2).
  exists (Z_to_bv 8 (if g then 1 else 0)), shj, shj2.
  split; [split; [exact AI|]; split; [exact GPU|]; split; [exact G60|]; split; [exact PSZ | exact TF]|].
  split; [exact TC|]. split; [exact SC|]. split; [exact PS|]. split; [exact (u8arr_of_rw_C1 m _ _ CG1)|]. split; [exact UR|].
  unfold l_ACEIL, STACK_WIN, USTACK_TOP, kHighShadowEnd, K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SEGTOP_A, SHB in *.
  repeat (split; [lia|]). split; [exact SHJ|]. split; [exact SHJ2|]. split; [exact ST|].
  repeat (split; [lia|]). split; [clear - HB1; Z.div_mod_to_equations; lia|]. split; [clear - HB2; Z.div_mod_to_equations; lia|]. lia.
Qed.

Theorem noret_core :
  cps bsegs (ASTA (@RTA GWf) Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_handle_no_return m)))
            (RT_iface5.noret_post (@RTA GWf) (ARTW_A c) Σ PMc fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo m).
Proof.
  destruct nc_facts as (g & shj & shj2 & NC & TC & SC & PS & GBm & UR & X1 & X2 & X3 & T1 & T2 & T3 & F1 & F2 & F3 & TL4 & TOPLO & TOP47 & BOT
                        & SHJ & SHJ2 & ST & LOR & LO6 & LOH & SPA & LOW & SPT & BA1 & BA2 & B81 & B82 & BU1 & BU2).
  intros TT cf Hc Hk. subst tp.
  assert (W1 : forall ms, eq (entry_st ra sp gp (Z_to_bv 64 0x6ab368) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_handle_no_return m) ms ->
                 evt bsegs (R_noret.noret_post ra sp gp (Z_to_bv 64 tpA) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc FSB (noret_bottom usp) (l_top L) lo m) ms).
  { intros ms <-. unfold entry_st, e_handle_no_return. change (Z_to_bv 64 0x6ab368) with (Z_to_bv 64 tpA).
    exact (handle_no_return_spec ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
             (l_TCX L) (l_T L) (l_top L) FSB (noret_bottom usp) lo g shj eq_refl NC TC SC PS GBm X1 X2 X3 T1 T2 T3 F1 F2 F3 TL4 TOPLO TOP47 ltac:(lia)
             SHJ ST ltac:(lia) LO6 LOH SPA MI). }
  apply (cps_realizes bsegs _ _ _ cf (ast_evt bsegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ) _ _ _ (rta_ASTA_mat_stable Σ PMc MST) W1) Hc).
  intros c1 Hc1. apply Hk.
  unfold RT_iface5.noret_post, ASTA in *. eapply AST_conseq; [exact Hc1 | | auto]. intros ms PO.
  destruct PO as (u0 & u1 & u2 & v & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & -> & MU & WM & MI' & SH & GB & ST').
  exists v, m'. split; [do 15 eexists; reflexivity|].
  assert (MUn : munch [(FSB + 0x60, FSB + 0x61); (lo, usp)] m m').
  { apply (munch_shrink_shadow Σ m m' (noret_bottom usp) (Z.to_nat ((l_top L - noret_bottom usp) / 8)) _ HA BA1 B81);
      [| rewrite Z2Nat.id by (apply Z.div_pos; lia); exact MU | exact SH].
    rewrite Z2Nat.id by (apply Z.div_pos; lia). clear - B81 TL4 TOP47 TOPLO. Z.div_mod_to_equations. lia. }
  split; [exact (art_after_noret c Σ m m' lo usp HA HC MUn WM true GB LOW SPT)|].
  split; [exact MI'|]. split; [exact WM|]. split; [exact ST'|].
  exact (nr_pres Σ m m' lo usp HA MUn LOW usp ltac:(lia) ltac:(lia)).
Qed.

Theorem unwind_core :
  cps bsegs (ASTA (@RTA GWf) Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_unwind_raise m)))
            (ASTA (@RTA GWf) Σ PMc (unwind_entry_st (@RTA GWf) (ARTW_A c) Σ ra sp gp tp s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)).
Proof.
  destruct nc_facts as (g & shj & shj2 & NC & TC & SC & PS & GBm & UR & X1 & X2 & X3 & T1 & T2 & T3 & F1 & F2 & F3 & TL4 & TOPLO & TOP47 & BOT
                        & SHJ & SHJ2 & ST & LOR & LO6 & LOH & SPA & LOW & SPT & BA1 & BA2 & B81 & B82 & BU1 & BU2).
  intros TT cf Hc Hk. subst tp.
  assert (W1 : forall ms, eq (entry_st ra sp gp (Z_to_bv 64 0x6ab368) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_unwind_raise m) ms ->
                 evt bsegs (unwicpt_post ra sp gp (Z_to_bv 64 tpA) s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc FSB (l_top L) lo m) ms).
  { intros ms <-. unfold entry_st, e_unwind_raise. change (Z_to_bv 64 0x6ab368) with (Z_to_bv 64 tpA).
    exact (unwind_icpt_spec ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
             (l_TCX L) (l_T L) (l_top L) FSB lo g shj2 NC TC SC PS GBm UR X1 X2 X3 T1 T2 T3 F1 F2 F3 TL4 TOPLO TOP47 BOT
             SHJ2 ST LOR LO6 LOH SPA MI). }
  apply (cps_realizes bsegs _ _ _ cf (ast_evt bsegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ) _ _ _ (rta_ASTA_mat_stable Σ PMc MST) W1) Hc).
  intros c1 Hc1. apply Hk.
  unfold ASTA in *. eapply AST_conseq; [exact Hc1 | | auto]. intros ms PO.
  destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & -> & MU & WM & MI' & SH & GB & ST').
  unfold unwind_entry_st. do 15 eexists. split; [unfold real_unwind_raise, real_unwind_raise_A; reflexivity|].
  assert (MUn : munch [(FSB + 0x60, FSB + 0x61); (lo, usp)] m m').
  { apply (munch_shrink_shadow Σ m m' (noret_bottom (usp - 32)) (Z.to_nat ((l_top L - noret_bottom (usp - 32)) / 8)) _ HA BA2 B82);
      [| rewrite Z2Nat.id by (apply Z.div_pos; lia); exact MU | exact SH].
    rewrite Z2Nat.id by (apply Z.div_pos; lia). clear - B82 TL4 TOP47 TOPLO. Z.div_mod_to_equations. lia. }
  split; [exact (art_after_noret c Σ m m' lo usp HA HC MUn WM true GB LOW SPT)|].
  split; [exact MI'|]. split; [exact WM|]. split; [exact ST'|].
  exact (nr_pres Σ m m' lo usp HA MUn LOW usp ltac:(lia) ltac:(lia)).
Qed.
End Core.
End Gen.

Theorem rta_noret_enter : noret_enter_stmt.
Proof.
  intros c Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo FDO MST HTP (HA & HCR) MI CALL DEPTH TOPR.
  cbn [ART rt_credit RTA] in HA, HCR. unfold rtA_credit in HCR.
  exact (@noret_core GWf c Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo MST HTP HA HCR MI CALL DEPTH TOPR).
Qed.

Theorem rta_noret_again : noret_again_stmt.
Proof.
  intros c Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo FDO MST HTP HA MI CALL DEPTH TOPR.
  unfold ARTW_A in HA.
  assert (HCR : credit Σ = c).
  { pose proof (@ART_fs (GWt c) Σ m HA) as (((g & _ & _ & G3) & _) & _). exact (G3 eq_refl). }
  exact (@noret_core (GWt c) c Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo MST HTP HA HCR MI CALL DEPTH TOPR).
Qed.

Theorem rta_unwind_icpt : unwind_icpt_stmt.
Proof.
  intros c Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo FDO MST HTP HA MI CALL DEPTH TOPR.
  unfold ARTW_A in HA.
  assert (HCR : credit Σ = c).
  { pose proof (@ART_fs (GWt c) Σ m HA) as (((g & _ & _ & G3) & _) & _). exact (G3 eq_refl). }
  exact (@unwind_core (GWt c) c Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo MST HTP HA HCR MI CALL DEPTH TOPR).
Qed.

Theorem rta_win_closed : rt_win (@RTA GWf).
Proof. exact (rta_win rta_noret_enter rta_noret_again rta_unwind_icpt). Qed.
