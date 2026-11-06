(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import
  PropExec AgentLib AsanAcct BackingAlgebra AsanPlacement AxSymExec3K AxSymExec3SoundK AxSymRun3K
  AsanPlanCoreK AsanPlanK AsanPlanSoundK AsanInitK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AxSymExec3K.AX2K AxSymExec3SoundK.AX2SK AsanPlanK.APK AsanPlanSoundK.APSK.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition VZ (E : env) (n : nat) : Z := bv_unsigned (ev E n).
(* [comment removed for export] *)
Definition LZ (E : env) (e : expr) : Z := lden E (lin_of e).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Generic.
Variable SEGS : list Segment.
Variable A : atable.
Variable LIMIT : Z.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Variable FS0 : Fs.Fs.
Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : hull_ok A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a /\ uE E e_sp0 <= bv_unsigned a.   (* [comment removed for export] *)

#[local] Notation CSOK := (cs_ok SEGS A LIMIT SINV argH FS0).
#[local] Notation MR := (Mr A argH).
#[local] Notation HID := (hid A argH).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma hb_kn : forall E cs R FULL model K,
  CSOK E cs R FULL model -> In K (kn cs) -> kentry_ok SEGS E (MR E cs model FULL) K.
Proof. intros E cs R FULL model K HC Hin. exact (proj1 (Forall_forall _ _) (co_know _ _ _ _ _ _ _ _ _ _ _ HC) K Hin). Qed.

(* [comment removed for export] *)
Lemma hb_knb_In : forall K k, existsb (kentry_eqb K) k = true -> In K k.
Proof.
  intros K k H. apply existsb_exists in H as (K' & Hin & Heq). apply kentry_eqb_eq in Heq. subst K'. exact Hin.
Qed.

Lemma hb_knb : forall E cs R FULL model K,
  CSOK E cs R FULL model -> existsb (kentry_eqb K) (kn cs) = true -> kentry_ok SEGS E (MR E cs model FULL) K.
Proof. intros E cs R FULL model K HC H. exact (hb_kn E cs R FULL model K HC (hb_knb_In K _ H)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma hb_mr_some : forall E cs model FULL (a : word) b,
  MR E cs model FULL a = Some b -> FULL a = Some b.
Proof. intros E cs model FULL a b H. unfold Mr, mrestrict in H. destruct (HID E cs model a); [discriminate| exact H]. Qed.

Lemma hb_mr_visible : forall E cs model FULL (a : word) b,
  MR E cs model FULL a = Some b -> HID E cs model a = false.
Proof. intros E cs model FULL a b H. unfold Mr, mrestrict in H. destruct (HID E cs model a); [discriminate| reflexivity]. Qed.

Lemma hb_mr_rdn : forall E cs model FULL (a : word) n bs,
  rdn SEGS (MR E cs model FULL) a n = Some bs ->
  rdn SEGS FULL a n = Some bs /\ range_avoids (HID E cs model) a n.
Proof.
  intros E cs model FULL a n bs H. unfold Mr in H. rewrite <- ov_rdn in H |- *.
  exact (ov_read_bytes_restrict SEGS _ (H_off_segments_cs SEGS A SEGS_in_hull HULL_ok argH argH_high E cs model) n FULL a bs H).
Qed.

Lemma hb_mr_store_ok : forall E cs model FULL (a : word) n,
  store_ok SEGS (MR E cs model FULL) a n = true ->
  store_ok SEGS FULL a n = true /\ range_avoids (HID E cs model) a n.
Proof.
  intros E cs model FULL a n H. unfold Mr in H.
  exact (store_ok_restrict SEGS _ (H_off_segments_cs SEGS A SEGS_in_hull HULL_ok argH argH_high E cs model) n FULL a H).
Qed.

(* [comment removed for export] *)
Lemma hb_mr_hull : forall E cs model FULL (a : word),
  in_hull A (bv_unsigned a) = true -> MR E cs model FULL a = FULL a.
Proof. intros E cs model FULL a H. unfold Mr, mrestrict. rewrite (hid_hull A HULL_ok argH argH_high E cs model a H). reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma hb_lin : forall E cs R FULL model e,
  CSOK E cs R FULL model -> lin_nowrapR (kn cs) e = true -> bv_unsigned (edenot E e) = LZ E e.
Proof. intros E cs R FULL model e HC H. exact (lin_nowrapR_sound SEGS E _ (kn cs) e (co_know _ _ _ _ _ _ _ _ _ _ _ HC) H). Qed.

Lemma hb_xlo : forall E cs R FULL model e lo,
  CSOK E cs R FULL model -> xlo (kn cs) e = Some lo -> lo <= bv_unsigned (edenot E e).
Proof. intros E cs R FULL model e lo HC H. exact (xlo_sound SEGS E _ (kn cs) e lo (co_know _ _ _ _ _ _ _ _ _ _ _ HC) H). Qed.

Lemma hb_xhi : forall E cs R FULL model e hi,
  CSOK E cs R FULL model -> xhi (kn cs) e = Some hi -> bv_unsigned (edenot E e) <= hi.
Proof. intros E cs R FULL model e hi HC H. exact (xhi_sound SEGS E _ (kn cs) e hi (co_know _ _ _ _ _ _ _ _ _ _ _ HC) H). Qed.

(* [comment removed for export] *)
Lemma hb_bounds_e : forall E cs R FULL model e lo hi,
  CSOK E cs R FULL model -> xlo (kn cs) e = Some lo -> xhi (kn cs) e = Some hi ->
  lo <= bv_unsigned (edenot E e) <= hi.
Proof. intros E cs R FULL model e lo hi HC H1 H2. split; [eapply hb_xlo; eassumption | eapply hb_xhi; eassumption]. Qed.

Lemma hb_estart : forall E b off, estart E (SA b off) = bv_unsigned (edenot E b) + off.
Proof. reflexivity. Qed.

Lemma hb_adenot : forall E a n, flat E a n -> adenot E a = Z_to_bv 64 (estart E a).
Proof.
  intros E a n Hf. apply bv_eq. rewrite (flat_u E a n Hf). destruct Hf as (H1 & H2 & _).
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. rewrite Z.mod_small; [reflexivity|]. cbn. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma hb_word : forall E cs R FULL model a w v,
  CSOK E cs R FULL model -> In (KWord a w v) (kn cs) ->
  (w <= 8)%nat /\ flat E a (Z.of_nat w)
  /\ rdn SEGS FULL (adenot E a) w = Some (word_to_le_bytes w (edenot E v))
  /\ range_avoids (HID E cs model) (adenot E a) w.
Proof.
  intros E cs R FULL model a w v HC Hin. destruct (hb_kn E cs R FULL model _ HC Hin) as (Hw & Hf & Hr).
  destruct (hb_mr_rdn E cs model FULL _ _ _ Hr) as [H1 H2]. auto.
Qed.

(* [comment removed for export] *)
Lemma hb_rdn_bytes : forall FULL n (a0 : word) bs,
  rdn SEGS FULL a0 n = Some bs ->
  (forall j, (j < n)%nat -> in_hull A (bv_unsigned a0 + Z.of_nat j) = false) ->
  bv_unsigned a0 + Z.of_nat n <= 2 ^ 64 ->
  forall j, (j < n)%nat -> FULL (Z_to_bv 64 (bv_unsigned a0 + Z.of_nat j)) = Some (nth j bs (Z_to_bv 8 0)).
Proof.
  intros FULL n. induction n as [|n IH]; intros a0 bs Hrd Hh Hnw j Hj; [lia|].
  cbn [rdn] in Hrd.
  destruct (FULL a0) as [b|] eqn:Hb.
  - destruct (rdn SEGS FULL (a0 + 1)%bv n) as [rest|] eqn:Hr2; [|discriminate]. injection Hrd as <-.
    destruct j as [|j].
    + cbn [nth]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact Hb.
    + cbn [nth]. pose proof (u64_range a0).
      assert (Hu1 : bv_unsigned (a0 + 1)%bv = bv_unsigned a0 + 1) by (apply u_add1; lia).
      replace (bv_unsigned a0 + Z.of_nat (Datatypes.S j)) with (bv_unsigned (a0 + 1)%bv + Z.of_nat j) by lia.
      apply (IH (a0 + 1)%bv rest Hr2); [| lia | lia].
      intros j' Hj'. rewrite Hu1. replace (bv_unsigned a0 + 1 + Z.of_nat j') with (bv_unsigned a0 + Z.of_nat (Datatypes.S j')) by lia. apply Hh. lia.
  - (* [comment removed for export] *)
    exfalso. pose proof (Hh 0%nat ltac:(lia)) as H0. rewrite Z.add_0_r in H0.
    unfold seg_rom, memory_read in Hrd. cbn [Z.of_N] in Hrd. rewrite (SEGS_in_hull a0 H0) in Hrd. discriminate.
Qed.

(* [comment removed for export] *)
Lemma hb_word_bytes : forall E cs R FULL model a w v,
  CSOK E cs R FULL model -> In (KWord a w v) (kn cs) ->
  (forall j, (j < w)%nat -> in_hull A (estart E a + Z.of_nat j) = false) ->
  forall j, (j < w)%nat ->
    FULL (Z_to_bv 64 (estart E a + Z.of_nat j)) = Some (nth j (word_to_le_bytes w (edenot E v)) (Z_to_bv 8 0)).
Proof.
  intros E cs R FULL model a w v HC Hin Hoff j Hj.
  destruct (hb_word E cs R FULL model a w v HC Hin) as (Hw & Hf & Hr & _).
  pose proof (flat_u E a _ Hf) as Hu. rewrite <- Hu. rewrite <- Hu in Hoff.
  apply (hb_rdn_bytes FULL w (adenot E a) _ Hr Hoff); [|exact Hj].
  destruct Hf as (?&?&?&?). rewrite Hu. lia.
Qed.

(* [comment removed for export] *)
Lemma hb_zero_k : forall E cs R FULL model a n,
  CSOK E cs R FULL model -> In (KZero a n) (kn cs) ->
  flat E a (elenZ E n) /\ forall i, 0 <= i < elenZ E n -> FULL (Z_to_bv 64 (estart E a + i)) = Some (Z_to_bv 8 0).
Proof.
  intros E cs R FULL model a n HC Hin. destruct (hb_kn E cs R FULL model _ HC Hin) as [Hf Hz].
  split; [exact Hf|]. intros i Hi. exact (hb_mr_some E cs model FULL _ _ (Hz i Hi)).
Qed.

(* [comment removed for export] *)
Lemma hb_fill : forall E cs R FULL model a n c,
  CSOK E cs R FULL model -> In (KFill a n c) (kn cs) ->
  flat E a (elenZ E n) /\ forall i, 0 <= i < elenZ E n -> FULL (Z_to_bv 64 (estart E a + i)) = Some (Z_to_bv 8 c).
Proof.
  intros E cs R FULL model a n c HC Hin. destruct (hb_kn E cs R FULL model _ HC Hin) as [Hf Hz].
  split; [exact Hf|]. intros i Hi. exact (hb_mr_some E cs model FULL _ _ (Hz i Hi)).
Qed.

(* [comment removed for export] *)
Lemma hb_unk : forall E cs R FULL model a n,
  CSOK E cs R FULL model -> In (KUnk a n) (kn cs) ->
  flat E a (elenZ E n) /\ forall i, 0 <= i < elenZ E n -> FULL (Z_to_bv 64 (estart E a + i)) <> None.
Proof.
  intros E cs R FULL model a n HC Hin. destruct (hb_kn E cs R FULL model _ HC Hin) as [Hf Hz].
  split; [exact Hf|]. intros i Hi Hn. apply (Hz i Hi). unfold Mr, mrestrict. rewrite Hn. destruct (HID E cs model _); reflexivity.
Qed.

(* [comment removed for export] *)
Lemma hb_img : forall E cs R FULL model lo hi,
  CSOK E cs R FULL model -> In (KImg lo hi) (kn cs) ->
  forall i, lo <= i < hi -> in_hull A i = true -> FULL (Z_to_bv 64 i) = None.
Proof.
  intros E cs R FULL model lo hi HC Hin i Hi Hh. destruct (hb_kn E cs R FULL model _ HC Hin) as (H0 & H1 & Hn).
  rewrite <- (hb_mr_hull E cs model FULL (Z_to_bv 64 i)); [exact (Hn i Hi)|].
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. rewrite Z.mod_small; [exact Hh| cbn; lia].
Qed.

(* [comment removed for export] *)
Lemma hb_wr : forall E cs R FULL model a n,
  CSOK E cs R FULL model -> In (KWr a n) (kn cs) ->
  flat E a (elenZ E n)
  /\ forall d m, 0 <= d -> d + Z.of_nat m <= elenZ E n ->
       store_ok SEGS FULL (Z_to_bv 64 (estart E a + d)) m = true
       /\ range_avoids (HID E cs model) (Z_to_bv 64 (estart E a + d)) m.
Proof.
  intros E cs R FULL model a n HC Hin. destruct (hb_kn E cs R FULL model _ HC Hin) as [Hf Hs].
  split; [exact Hf|]. intros d m Hd Hm. exact (hb_mr_store_ok E cs model FULL _ _ (Hs d m Hd Hm)).
Qed.

(* [comment removed for export] *)
Lemma hb_range : forall E cs R FULL model e lo hi,
  CSOK E cs R FULL model -> In (KRange e lo hi) (kn cs) -> lo <= bv_unsigned (edenot E e) <= hi.
Proof. intros E cs R FULL model e lo hi HC Hin. destruct (hb_kn E cs R FULL model _ HC Hin) as [H1 H2]. lia. Qed.

Lemma hb_disj : forall E cs R FULL model a1 n1 a2 n2,
  CSOK E cs R FULL model -> In (KDisj a1 n1 a2 n2) (kn cs) ->
  estart E a1 + elenZ E n1 <= estart E a2 \/ estart E a2 + elenZ E n2 <= estart E a1.
Proof. intros E cs R FULL model a1 n1 a2 n2 HC Hin. exact (hb_kn E cs R FULL model _ HC Hin). Qed.

Lemma hb_align : forall E cs R FULL model e m,
  CSOK E cs R FULL model -> In (KAlign e m) (kn cs) -> 0 < m /\ bv_unsigned (edenot E e) mod m = 0.
Proof. intros E cs R FULL model e m HC Hin. exact (hb_kn E cs R FULL model _ HC Hin). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma hb_reg : forall E cs R FULL model (r : bv 5),
  CSOK E cs R FULL model -> getr R r = edenot E (sr_get (s_regs (a_ss cs)) r).
Proof. intros E cs R FULL model r HC. exact (co_regs _ _ _ _ _ _ _ _ _ _ _ HC r). Qed.

Lemma hb_regZ : forall E cs R FULL model (r : bv 5),
  CSOK E cs R FULL model -> lin_nowrapR (kn cs) (sr_get (s_regs (a_ss cs)) r) = true ->
  bv_unsigned (getr R r) = LZ E (sr_get (s_regs (a_ss cs)) r).
Proof. intros E cs R FULL model r HC H. rewrite (hb_reg E cs R FULL model r HC). exact (hb_lin E cs R FULL model _ HC H). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma hb_maps : forall E cs R FULL model,
  CSOK E cs R FULL model -> no_fog (a_maps cs) = true ->
  vm_maps (m_vmmaps model) = map (amap_den E) (a_maps cs).
Proof.
  intros E cs R FULL model HC Hnf.
  exact (proj1 (maps_match_exact 0%nat (fun _ => None) (fun _ _ _ => None) (fun _ _ _ => None) (fun _ _ _ => None) E (a_maps cs) _ Hnf)
               (co_maps _ _ _ _ _ _ _ _ _ _ _ HC)).
Qed.

(* [comment removed for export] *)
Definition amapZ (E : env) (m : amap) : Z * Z := (LZ E (am_base m), LZ E (am_base m) + LZ E (am_len m)).
Definition amaps_lin (k : list kentry) (ms : list amap) : bool :=
  forallb (fun m => lin_nowrapR k (am_base m) && lin_nowrapR k (am_len m)) ms.

Lemma hb_maps_Z : forall E cs R FULL model,
  CSOK E cs R FULL model -> no_fog (a_maps cs) = true -> amaps_lin (kn cs) (a_maps cs) = true ->
  map (fun e => (B e, B e + S e)) (vm_maps (m_vmmaps model)) = map (amapZ E) (a_maps cs).
Proof.
  intros E cs R FULL model HC Hnf Hl. rewrite (hb_maps E cs R FULL model HC Hnf). rewrite map_map. apply map_ext_in.
  intros m Hm. unfold amaps_lin in Hl. pose proof (proj1 (forallb_forall _ _) Hl m Hm) as Hb. apply andb_prop in Hb as [H1 H2].
  unfold amapZ, amap_den, B, S. cbn [fst snd].
  rewrite (hb_lin E cs R FULL model _ HC H1), (hb_lin E cs R FULL model _ HC H2). reflexivity.
Qed.

Lemma hb_res : forall E cs R FULL model, CSOK E cs R FULL model -> vm_reserved (m_vmmaps model) = segments_reserved SEGS.
Proof. intros E cs R FULL model HC. exact (co_res _ _ _ _ _ _ _ _ _ _ _ HC). Qed.

Lemma hb_limit : forall E cs R FULL model, CSOK E cs R FULL model -> vm_limit (m_vmmaps model) = LIMIT.
Proof. intros E cs R FULL model HC. exact (co_limit _ _ _ _ _ _ _ _ _ _ _ HC). Qed.

Lemma hb_brk : forall E cs R FULL model, CSOK E cs R FULL model -> vm_brk (m_vmmaps model) = edenot E (a_brk cs).
Proof. intros E cs R FULL model HC. exact (co_brk _ _ _ _ _ _ _ _ _ _ _ HC). Qed.

Lemma hb_brkZ : forall E cs R FULL model,
  CSOK E cs R FULL model -> lin_nowrapR (kn cs) (a_brk cs) = true -> bv_unsigned (vm_brk (m_vmmaps model)) = LZ E (a_brk cs).
Proof. intros E cs R FULL model HC H. rewrite (hb_brk E cs R FULL model HC). exact (hb_lin E cs R FULL model _ HC H). Qed.

Lemma hb_sbrk : forall E cs R FULL model,
  CSOK E cs R FULL model -> bv_unsigned (vm_start_brk (m_vmmaps model)) <= bv_unsigned (vm_brk (m_vmmaps model)).
Proof. intros E cs R FULL model HC. exact (co_sbrk _ _ _ _ _ _ _ _ _ _ _ HC). Qed.

(* [comment removed for export] *)
Lemma hb_isp : forall E cs R FULL model,
  CSOK E cs R FULL model ->
  bv_unsigned (vm_init_sp (m_vmmaps model)) = uE E e_sp0 /\ sp_window_lo <= uE E e_sp0 <= sp_window_hi
  /\ uE E e_sppg = pagedown (uE E e_sp0).
Proof. intros E cs R FULL model HC. exact (co_isp _ _ _ _ _ _ _ _ _ _ _ HC). Qed.

Lemma hb_seps : forall E cs R FULL model, CSOK E cs R FULL model -> seps (vm_maps (m_vmmaps model)).
Proof. intros E cs R FULL model HC. exact (co_seps _ _ _ _ _ _ _ _ _ _ _ HC). Qed.

Lemma hb_wf : forall E cs R FULL model, CSOK E cs R FULL model -> model_ivs_wf model.
Proof. intros E cs R FULL model HC. exact (co_wf _ _ _ _ _ _ _ _ _ _ _ HC). Qed.

Lemma hb_bounds : forall E cs R FULL model,
  CSOK E cs R FULL model ->
  Forall (fun iv => 0 < bv_unsigned (snd iv) /\ bv_unsigned (fst iv) mod 4096 = 0 /\ bv_unsigned (snd iv) mod 4096 = 0
                    /\ (bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_lo A \/ img_hi A <= bv_unsigned (fst iv))
                    /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= utop E)
         (vm_maps (m_vmmaps model)).   (* [comment removed for export] *)
Proof. intros E cs R FULL model HC. exact (co_bounds _ _ _ _ _ _ _ _ _ _ _ HC). Qed.

Lemma hb_lazyb : forall E cs R FULL model,
  CSOK E cs R FULL model ->
  Forall (fun iv => (bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_lo A \/ img_hi A <= bv_unsigned (fst iv))
                    /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= utop E) (m_vm_lazy model).
Proof. intros E cs R FULL model HC. exact (co_lazyb _ _ _ _ _ _ _ _ _ _ _ HC). Qed.

Lemma hb_nasub : forall E cs R FULL model z,
  CSOK E cs R FULL model -> in_ivs z (vm_noaccess (m_vmmaps model)) = true -> in_ivs z (vm_maps (m_vmmaps model)) = true.
Proof. intros E cs R FULL model z HC. exact (co_nasub _ _ _ _ _ _ _ _ _ _ _ HC z). Qed.

Lemma hb_totsz : forall E cs R FULL model,
  CSOK E cs R FULL model -> sum_sizes (vm_reserved (m_vmmaps model) ++ vm_maps (m_vmmaps model)) <= a_totsz cs.
Proof. intros E cs R FULL model HC. exact (co_totsz _ _ _ _ _ _ _ _ _ _ _ HC). Qed.

(* [comment removed for export] *)
Lemma hb_none : forall E cs R FULL model m,
  CSOK E cs R FULL model -> In m (a_maps cs) -> am_kind m = KNONE \/ am_kind m = KNONELAZY ->
  In (amap_den E m) (vm_noaccess (m_vmmaps model)).
Proof. intros E cs R FULL model m HC Hm Hk. exact (proj1 (Forall_forall _ _) (co_none _ _ _ _ _ _ _ _ _ _ _ HC) m Hm Hk). Qed.

(* [comment removed for export] *)
Lemma hb_lazykind : forall E cs R FULL model m (a : word),
  CSOK E cs R FULL model -> In m (a_maps cs) -> am_kind m = KRWLAZY ->
  bv_unsigned (edenot E (am_base m)) <= bv_unsigned a < bv_unsigned (edenot E (am_base m)) + bv_unsigned (edenot E (am_len m)) ->
  in_ivs (bv_unsigned a) (vm_noaccess (m_vmmaps model)) = false /\ page_in_ranges (page_base a) (m_vm_lazy model) = true.
Proof. intros E cs R FULL model m a HC Hm Hk Ha. exact (proj1 (Forall_forall _ _) (co_kinds _ _ _ _ _ _ _ _ _ _ _ HC) m Hm Hk a Ha). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma hb_noacc : forall E cs R FULL model, CSOK E cs R FULL model -> vm_noaccess (m_vmmaps model) = hreplay E (a_hna cs).
Proof. intros E cs R FULL model HC. exact (co_hna _ _ _ _ _ _ _ _ _ _ _ HC). Qed.

Lemma hb_lazy : forall E cs R FULL model, CSOK E cs R FULL model -> m_vm_lazy model = hreplay E (a_hlz cs).
Proof. intros E cs R FULL model HC. exact (co_hlz _ _ _ _ _ _ _ _ _ _ _ HC). Qed.

Lemma hb_tid : forall E cs R FULL model, CSOK E cs R FULL model -> a_tidset cs = true ->
  exists t, m_tid model = Some t /\ 0 < bv_unsigned t < PID_MAX.
Proof. intros E cs R FULL model HC Ht. exact (co_tidv _ _ _ _ _ _ _ _ _ _ _ HC Ht). Qed.

(* [comment removed for export] *)
Lemma hb_tid_range : forall E cs R FULL model, CSOK E cs R FULL model -> a_tidset cs = true ->
  forall t, m_tid model = Some t -> 0 < bv_unsigned t < 4194304.
Proof.
  intros E cs R FULL model HC Ht t Hm. destruct (hb_tid E cs R FULL model HC Ht) as (t' & Hm' & Hr).
  rewrite Hm in Hm'. injection Hm' as ->. unfold PID_MAX in Hr. exact Hr.
Qed.

(* [comment removed for export] *)
Lemma hreplay_nil : forall E, hreplay E [] = []. Proof. reflexivity. Qed.
Lemma hreplay_cons : forall E b n h, hreplay E (HCons b n :: h) = (edenot E b, edenot E n) :: hreplay E h. Proof. reflexivity. Qed.
Lemma hreplay_sub : forall E b n h,
  hreplay E (HSub b n :: h) = maps_subtract (hreplay E h) (bv_unsigned (edenot E b)) (bv_unsigned (edenot E b) + bv_unsigned (edenot E n)).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma hb_eager : forall E cs R FULL model, CSOK E cs R FULL model -> eager_used model <= a_eager cs.
Proof. intros E cs R FULL model HC. exact (co_eager _ _ _ _ _ _ _ _ _ _ _ HC). Qed.

Lemma hb_abytes : forall E cs R FULL model, CSOK E cs R FULL model -> A_bytes (allowA A E cs) <= a_abytes cs.
Proof. intros E cs R FULL model HC. exact (co_abytes _ _ _ _ _ _ _ _ _ _ _ HC). Qed.

Lemma hb_minv : forall E cs R FULL model, CSOK E cs R FULL model -> MInv (allowA A E cs) model.
Proof. intros E cs R FULL model HC. exact (co_minv _ _ _ _ _ _ _ _ _ _ _ HC). Qed.

Lemma hb_allowA_wf : forall E cs, A_wf (allowA A E cs).
Proof. intros E cs. exact (A_wf_allowA A (fun _ => None) (fun _ _ _ => None) (fun _ _ _ => None) (fun _ _ _ => None) 0%nat E cs). Qed.

(* [comment removed for export] *)
Definition allow1Z (E : env) (p : expr * expr) : list (Z * Z) :=
  let b := LZ E (fst p) in let n := LZ E (snd p) in
  [(pagedown b, pageup (b + n)); (pagedown (shadow_off A + b / 8), pageup (shadow_off A + (b + n) / 8))].
Definition vis_lin (k : list kentry) (ps : list (expr * expr)) : bool :=
  forallb (fun p => lin_nowrapR k (fst p) && lin_nowrapR k (snd p)) ps.

Lemma flat_map_ext_In {X Y} : forall (f g : X -> list Y) l, (forall x, In x l -> f x = g x) -> flat_map f l = flat_map g l.
Proof. intros f g l H. induction l as [|x l IH]; [reflexivity|]. cbn. rewrite (H x (or_introl eq_refl)), IH; [reflexivity|]. intros y Hy. apply H. right. exact Hy. Qed.

Lemma hb_allowA_Z : forall E cs R FULL model,
  CSOK E cs R FULL model -> vis_lin (kn cs) (a_vis cs ++ a_ghost cs) = true ->
  allowA A E cs = flat_map (allow1Z E) (a_vis cs ++ a_ghost cs).
Proof.
  intros E cs R FULL model HC Hl. unfold allowA. apply flat_map_ext_In.
  intros p Hp. pose proof (proj1 (forallb_forall _ _) Hl p Hp) as Hb. apply andb_prop in Hb as [H1 H2].
  unfold allow1, allow1Z, sh_lo, sh_hi, APSK.uE. rewrite (hb_lin E cs R FULL model _ HC H1), (hb_lin E cs R FULL model _ HC H2). reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma hb_halt : forall E cs R FULL model, CSOK E cs R FULL model -> m_halted model = None.
Proof. intros E cs R FULL model HC. exact (co_halt _ _ _ _ _ _ _ _ _ _ _ HC). Qed.

Lemma hb_fds_std : forall E cs R FULL model, CSOK E cs R FULL model -> a_fd cs = FdStd -> m_fds model = fds_std.
Proof. intros E cs R FULL model HC Hfd. pose proof (co_fds _ _ _ _ _ _ _ _ _ _ _ HC) as H. rewrite Hfd in H. exact H. Qed.

Lemma hb_fs : forall E cs R FULL model, CSOK E cs R FULL model -> m_fs model = FS0.
Proof. intros E cs R FULL model HC. exact (co_fs _ _ _ _ _ _ _ _ _ _ _ HC). Qed.

(* [comment removed for export] *)
Lemma hb_tid_none : forall E cs R FULL model, CSOK E cs R FULL model -> a_tidset cs = false -> m_tid model = None.
Proof. intros E cs R FULL model HC. exact (co_tid _ _ _ _ _ _ _ _ _ _ _ HC). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma hb_zero : forall E cs R FULL model (a : word),
  CSOK E cs R FULL model ->
  HID E cs model a = true ->
  in_ivs (bv_unsigned a) (vm_maps (m_vmmaps model)) = true ->
  in_ivs (bv_unsigned a) (vm_noaccess (m_vmmaps model)) = false ->
  page_in_ranges (page_base a) (m_vm_lazy model) = true ->
  in_ghost E cs (bv_unsigned a) = false ->
  FULL a = Some (Z_to_bv 8 0).
Proof. intros E cs R FULL model a HC. exact (co_zero _ _ _ _ _ _ _ _ _ _ _ HC a). Qed.

(* [comment removed for export] *)
Lemma hb_hid_unfold : forall E cs model (a : word),
  HID E cs model a = (argH E a || negb (vis A E cs model a))%bool.
Proof. reflexivity. Qed.

Lemma hb_sinv : forall E cs R FULL model, CSOK E cs R FULL model -> SINV E FULL.
Proof. intros E cs R FULL model HC. exact (co_sinv _ _ _ _ _ _ _ _ _ _ _ HC). Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition kfind_word (k : list kentry) (b : expr) (off : Z) (w : nat) : option expr :=
  match List.find (fun K => match K with
                            | KWord a w' _ => (expr_eqb (a_base a) b && Z.eqb (a_off a) off && Nat.eqb w' w)%bool
                            | _ => false end) k with
  | Some (KWord _ _ v) => Some v
  | _ => None
  end.

Lemma kfind_word_In : forall k b off w v, kfind_word k b off w = Some v -> In (KWord (SA b off) w v) k.
Proof.
  intros k b off w v H. unfold kfind_word in H.
  destruct (List.find _ k) as [K|] eqn:Hf; [|discriminate].
  apply find_some in Hf as [Hin HK]. destruct K as [a w' v'| | | | | | | | |]; try discriminate.
  injection H as <-. apply andb_prop in HK as [HK H3]. apply andb_prop in HK as [H1 H2].
  apply expr_eqb_eq in H1. apply Z.eqb_eq in H2. apply Nat.eqb_eq in H3. destruct a as [ab ao]. cbn in H1, H2. subst. exact Hin.
Qed.

Lemma hb_word_at : forall E cs R FULL model b off w v,
  CSOK E cs R FULL model -> kfind_word (kn cs) b off w = Some v ->
  (w <= 8)%nat /\ flat E (SA b off) (Z.of_nat w)
  /\ rdn SEGS FULL (adenot E (SA b off)) w = Some (word_to_le_bytes w (edenot E v))
  /\ range_avoids (HID E cs model) (adenot E (SA b off)) w.
Proof. intros E cs R FULL model b off w v HC H. exact (hb_word E cs R FULL model _ w v HC (kfind_word_In _ _ _ _ _ H)). Qed.

(* [comment removed for export] *)
Definition kfind_zero (k : list kentry) (b : expr) (off : Z) : option expr :=
  match List.find (fun K => match K with
                            | KZero a _ => (expr_eqb (a_base a) b && Z.eqb (a_off a) off)%bool
                            | _ => false end) k with
  | Some (KZero _ n) => Some n
  | _ => None
  end.
Lemma kfind_zero_In : forall k b off n, kfind_zero k b off = Some n -> In (KZero (SA b off) n) k.
Proof.
  intros k b off n H. unfold kfind_zero in H.
  destruct (List.find _ k) as [K|] eqn:Hf; [|discriminate].
  apply find_some in Hf as [Hin HK]. destruct K as [ |a n'| | | | | | | |]; try discriminate.
  injection H as <-. apply andb_prop in HK as [H1 H2].
  apply expr_eqb_eq in H1. apply Z.eqb_eq in H2. destruct a as [ab ao]. cbn in H1, H2. subst. exact Hin.
Qed.
Lemma hb_zero_at : forall E cs R FULL model b off n,
  CSOK E cs R FULL model -> kfind_zero (kn cs) b off = Some n ->
  flat E (SA b off) (elenZ E n) /\ forall i, 0 <= i < elenZ E n -> FULL (Z_to_bv 64 (estart E (SA b off) + i)) = Some (Z_to_bv 8 0).
Proof. intros E cs R FULL model b off n HC H. exact (hb_zero_k E cs R FULL model _ n HC (kfind_zero_In _ _ _ _ H)). Qed.

Definition kfind_fill (k : list kentry) (b : expr) (off : Z) : option (expr * Z) :=
  match List.find (fun K => match K with
                            | KFill a _ _ => (expr_eqb (a_base a) b && Z.eqb (a_off a) off)%bool
                            | _ => false end) k with
  | Some (KFill _ n c) => Some (n, c)
  | _ => None
  end.
Lemma kfind_fill_In : forall k b off n c, kfind_fill k b off = Some (n, c) -> In (KFill (SA b off) n c) k.
Proof.
  intros k b off n c H. unfold kfind_fill in H.
  destruct (List.find _ k) as [K|] eqn:Hf; [|discriminate].
  apply find_some in Hf as [Hin HK]. destruct K as [ | | | | | | | |a n' c'| ]; try discriminate.
  injection H as <- <-. apply andb_prop in HK as [H1 H2].
  apply expr_eqb_eq in H1. apply Z.eqb_eq in H2. destruct a as [ab ao]. cbn in H1, H2. subst. exact Hin.
Qed.
Lemma hb_fill_at : forall E cs R FULL model b off n c,
  CSOK E cs R FULL model -> kfind_fill (kn cs) b off = Some (n, c) ->
  flat E (SA b off) (elenZ E n) /\ forall i, 0 <= i < elenZ E n -> FULL (Z_to_bv 64 (estart E (SA b off) + i)) = Some (Z_to_bv 8 c).
Proof. intros E cs R FULL model b off n c HC H. exact (hb_fill E cs R FULL model _ n c HC (kfind_fill_In _ _ _ _ _ H)). Qed.

Definition kfind_wr (k : list kentry) (b : expr) (off : Z) : option expr :=
  match List.find (fun K => match K with
                            | KWr a _ => (expr_eqb (a_base a) b && Z.eqb (a_off a) off)%bool
                            | _ => false end) k with
  | Some (KWr _ n) => Some n
  | _ => None
  end.
Lemma kfind_wr_In : forall k b off n, kfind_wr k b off = Some n -> In (KWr (SA b off) n) k.
Proof.
  intros k b off n H. unfold kfind_wr in H.
  destruct (List.find _ k) as [K|] eqn:Hf; [|discriminate].
  apply find_some in Hf as [Hin HK]. destruct K as [ | | | | | |a n'| | | ]; try discriminate.
  injection H as <-. apply andb_prop in HK as [H1 H2].
  apply expr_eqb_eq in H1. apply Z.eqb_eq in H2. destruct a as [ab ao]. cbn in H1, H2. subst. exact Hin.
Qed.
Lemma hb_wr_at : forall E cs R FULL model b off n,
  CSOK E cs R FULL model -> kfind_wr (kn cs) b off = Some n ->
  flat E (SA b off) (elenZ E n)
  /\ forall d m, 0 <= d -> d + Z.of_nat m <= elenZ E n ->
       store_ok SEGS FULL (Z_to_bv 64 (estart E (SA b off) + d)) m = true
       /\ range_avoids (HID E cs model) (Z_to_bv 64 (estart E (SA b off) + d)) m.
Proof. intros E cs R FULL model b off n HC H. exact (hb_wr E cs R FULL model _ n HC (kfind_wr_In _ _ _ _ H)). Qed.

(* [comment removed for export] *)
Definition kfind_img (k : list kentry) (z : Z) : option (Z * Z) :=
  match List.find (fun K => match K with KImg lo hi => (Z.leb lo z && Z.ltb z hi)%bool | _ => false end) k with
  | Some (KImg lo hi) => Some (lo, hi)
  | _ => None
  end.
Lemma kfind_img_In : forall k z lo hi, kfind_img k z = Some (lo, hi) -> In (KImg lo hi) k /\ lo <= z < hi.
Proof.
  intros k z lo hi H. unfold kfind_img in H.
  destruct (List.find _ k) as [K|] eqn:Hf; [|discriminate].
  apply find_some in Hf as [Hin HK]. destruct K as [ | | |lo' hi'| | | | | | ]; try discriminate.
  injection H as <- <-. apply andb_prop in HK as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. auto.
Qed.
Lemma hb_img_at : forall E cs R FULL model z lo hi,
  CSOK E cs R FULL model -> kfind_img (kn cs) z = Some (lo, hi) ->
  forall i, lo <= i < hi -> in_hull A i = true -> FULL (Z_to_bv 64 i) = None.
Proof. intros E cs R FULL model z lo hi HC H. destruct (kfind_img_In _ _ _ _ H) as [Hin _]. exact (hb_img E cs R FULL model lo hi HC Hin). Qed.

(* [comment removed for export] *)
Definition kfind_at (k : list kentry) (b : expr) (off : Z) : list kentry :=
  List.filter (fun K => match K with
                        | KWord a _ _ | KZero a _ | KBlob a _ _ | KWr a _ | KFill a _ _ | KUnk a _ => (expr_eqb (a_base a) b && Z.eqb (a_off a) off)%bool
                        | _ => false end) k.
Lemma kfind_at_In : forall k b off K, In K (kfind_at k b off) -> In K k.
Proof. intros k b off K H. unfold kfind_at in H. apply filter_In in H as [H _]. exact H. Qed.

(* [comment removed for export] *)
Definition kfind_ranges (k : list kentry) (e : expr) : list (Z * Z) :=
  flat_map (fun K => match K with KRange e' lo hi => if expr_eqb e' e then [(lo, hi)] else [] | _ => [] end) k.
Lemma hb_ranges_of : forall E cs R FULL model e,
  CSOK E cs R FULL model -> Forall (fun r => fst r <= bv_unsigned (edenot E e) <= snd r) (kfind_ranges (kn cs) e).
Proof.
  intros E cs R FULL model e HC. unfold kfind_ranges. apply Forall_forall. intros r Hr.
  apply in_flat_map in Hr as (K & Hin & Hr). destruct K as [ | | | | |e' lo hi| | | | ]; try (destruct Hr; fail); try contradiction.
  destruct (expr_eqb e' e) eqn:He; [|destruct Hr]. destruct Hr as [<-|[]]. apply expr_eqb_eq in He. subst e'. cbn.
  exact (hb_range E cs R FULL model e lo hi HC Hin).
Qed.
End Generic.

(* [comment removed for export] *)
Ltac hb_linZ :=
  unfold LZ;
  repeat (match goal with |- context [lin_of ?e] => let l := eval vm_compute in (lin_of e) in change (lin_of e) with l end);
  cbv [AX2SK.lden AX2SK.tden fst snd AX2SK.uE edenot];
  repeat (match goal with |- context [bv_unsigned (ev ?E ?n)] => change (bv_unsigned (ev E n)) with (VZ E n) end);
  rewrite ?Z.add_0_r.

(* [comment removed for export] *)
Ltac hb_in := apply hb_knb_In; vm_compute; reflexivity.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Image.
Variable SEGS : list Segment.
Variable A : atable.
Variable ph : PhdrInfo.
Hypothesis IMG : img_facts SEGS A ph.
Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : hull_ok A.
(* [comment removed for export] *)
Variable HSf : nat -> option acs.
Variable HSc : nat -> acs.
Hypothesis HSf_some : forall h, (h < 2)%nat -> HSf h = Some (HSc h).
Hypothesis HSf_none : forall h, (2 <= h)%nat -> HSf h = None.
(* [comment removed for export] *)
Hypothesis NOFOG : forall h, (h < 2)%nat -> no_fog (a_maps (HSc h)) = true.
Hypothesis MAPSLIN : forall h, (h < 2)%nat -> amaps_lin (kn (HSc h)) (a_maps (HSc h)) = true.
Hypothesis VISLIN : forall h, (h < 2)%nat -> vis_lin (kn (HSc h)) (a_vis (HSc h) ++ a_ghost (HSc h)) = true.
Hypothesis BRKLIN : forall h, (h < 2)%nat -> lin_nowrapR (kn (HSc h)) (a_brk (HSc h)) = true.
Hypothesis FDSTD : forall h, (h < 2)%nat -> a_fd (HSc h) = FdStd.
(* [comment removed for export] *)
Variables (sp : word) (rdraw : EntryDraw) (brk0 : word) (argv envp : list (list byte)) (uid hw : word) (fs : Fs.Fs).   (* [comment removed for export] *)
Hypothesis Hsp : valid_sp sp.
Hypothesis Hbrk : valid_brk SEGS brk0.
Hypothesis Hva : valid_argv argv.
Hypothesis Hve : valid_envp envp.
Hypothesis Hfit : entry_stack_fits sp argv envp.

#[local] Notation SINV := (SINV0 ph sp rdraw brk0 argv envp uid hw).
#[local] Notation argH := (argH0 ph sp rdraw argv envp uid hw).
#[local] Notation CSOK := (cs_ok SEGS A AsanInitK.LIMIT SINV argH fs).

Let argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a /\ uE E e_sp0 <= bv_unsigned a := argH0_high ph sp rdraw argv envp uid hw Hsp Hva.

(* [comment removed for export] *)
Lemma hbi_ch : forall h ch, HSf h = Some ch -> ch = HSc h /\ (h < 2)%nat.
Proof.
  intros h ch H. destruct (Nat.lt_ge_cases h 2) as [Hl|Hl].
  - rewrite (HSf_some h Hl) in H. injection H as <-. auto.
  - rewrite (HSf_none h Hl) in H. discriminate.
Qed.

(* [comment removed for export] *)
Definition MAPS (h : nat) (E : env) : list (word * word) := map (amap_den E) (a_maps (HSc h)).

Lemma hbi_maps : forall h E R FULL model, (h < 2)%nat -> CSOK E (HSc h) R FULL model ->
  vm_maps (m_vmmaps model) = MAPS h E.
Proof. intros h E R FULL model Hh HC. exact (hb_maps SEGS A _ _ _ _ E _ R FULL model HC (NOFOG h Hh)). Qed.

Lemma hbi_maps_Z : forall h E R FULL model, (h < 2)%nat -> CSOK E (HSc h) R FULL model ->
  map (fun e => (B e, B e + S e)) (vm_maps (m_vmmaps model)) = map (amapZ E) (a_maps (HSc h)).
Proof. intros h E R FULL model Hh HC. exact (hb_maps_Z SEGS A _ _ _ _ E _ R FULL model HC (NOFOG h Hh) (MAPSLIN h Hh)). Qed.

Lemma hbi_maps_len : forall h E R FULL model, (h < 2)%nat -> CSOK E (HSc h) R FULL model ->
  length (vm_maps (m_vmmaps model)) = length (a_maps (HSc h)).
Proof. intros h E R FULL model Hh HC. rewrite (hbi_maps h E R FULL model Hh HC). apply length_map. Qed.

Lemma hbi_brkZ : forall h E R FULL model, (h < 2)%nat -> CSOK E (HSc h) R FULL model ->
  bv_unsigned (vm_brk (m_vmmaps model)) = LZ E (a_brk (HSc h)).
Proof. intros h E R FULL model Hh HC. exact (hb_brkZ SEGS A _ _ _ _ E _ R FULL model HC (BRKLIN h Hh)). Qed.

Lemma hbi_allowA_Z : forall h E R FULL model, (h < 2)%nat -> CSOK E (HSc h) R FULL model ->
  allowA A E (HSc h) = flat_map (allow1Z A E) (a_vis (HSc h) ++ a_ghost (HSc h)).
Proof. intros h E R FULL model Hh HC. exact (hb_allowA_Z SEGS A _ _ _ _ E _ R FULL model HC (VISLIN h Hh)). Qed.

Lemma hbi_fds : forall h E R FULL model, (h < 2)%nat -> CSOK E (HSc h) R FULL model -> m_fds model = fds_std.
Proof. intros h E R FULL model Hh HC. exact (hb_fds_std SEGS A _ _ _ _ E _ R FULL model HC (FDSTD h Hh)). Qed.

(* [comment removed for export] *)
Lemma hbi_E0 : forall E cs R FULL model, CSOK E cs R FULL model ->
  forall n, (n < NX0)%nat -> ev E n = ev (E0 ph sp rdraw brk0 argv envp uid hw) n.
Proof. intros E cs R FULL model HC. exact (proj1 (hb_sinv SEGS A _ _ _ _ E cs R FULL model HC)). Qed.

#[local] Notation usp := (bv_unsigned sp).
#[local] Notation argc := (Z.of_nat (length argv)).
#[local] Notation envc := (Z.of_nat (length envp)).
(* [comment removed for export] *)
Definition Wsb : Z := (Z.of_nat (length (build_stack_bytes ph sp argv envp uid hw rdraw)) - 16 - (8 * argc + 8 * envc + 184)) / 8.   (* [comment removed for export] *)

Lemma hbi_vals : forall E cs R FULL model, CSOK E cs R FULL model ->
  VZ E 0 (* [comment removed for export] *) = usp / 32768 /\ VZ E 6 (* [comment removed for export] *) = (usp mod 4096) / 16
  /\ VZ E 1 (* [comment removed for export] *) = argc /\ VZ E 2 (* [comment removed for export] *) = envc
  /\ VZ E 3 (* [comment removed for export] *) = Z.of_nat (length (nth 0 argv [])) /\ VZ E 7 (* [comment removed for export] *) = Z.of_nat (length (nth 1 argv []))
  /\ VZ E 4 (* [comment removed for export] *) = Wsb /\ VZ E 5 (* [comment removed for export] *) = bv_unsigned brk0 / 4096 /\ ev E 8 (* [comment removed for export] *) = uid
  /\ ev E 9 (* [comment removed for export] *) = hw /\ VZ E 10 (* [comment removed for export] *) = (usp mod 32768) / 4096.   (* [comment removed for export] *)
Proof.
  intros E cs R FULL model HC. pose proof (hbi_E0 E cs R FULL model HC) as HE.
  pose proof (uE0 ph sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit) as (U1 & U2 & U3 & U4 & U5 & U6 & U7).
  pose proof (uE0_L1 ph sp rdraw brk0 argv envp uid hw Hva) as U8.
  pose proof (uE0_s2a ph sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit) as U9.
  unfold APSK.uE in *. cbn [edenot] in U1, U2, U3, U4, U5, U6, U7, U8, U9.
  unfold V_S1, V_S2, V_S2A, V_ARGC, V_ENVC, V_L0, V_L1, V_W, V_BRK, V_UID, V_HW in *. unfold VZ. rewrite !HE by (unfold NX0; lia).
  repeat split; try assumption; try reflexivity.
Qed.

(* [comment removed for export] *)
Lemma hbi_sp0 : forall E cs R FULL model, CSOK E cs R FULL model -> 32768 * VZ E 0 + 16 * VZ E 6 + 4096 * VZ E 10 = usp.
Proof.
  intros E cs R FULL model HC. destruct (hbi_vals E cs R FULL model HC) as (U1 & U2 & _ & _ & _ & _ & _ & _ & _ & _ & U3). rewrite U1, U2, U3.
  pose proof Hsp as (_ & _ & Hal). pose proof (u64_range sp).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Lemma hbi_sppg : forall E cs R FULL model, CSOK E cs R FULL model -> 32768 * VZ E 0 + 4096 * VZ E 10 = usp / 4096 * 4096.
Proof.
  intros E cs R FULL model HC. destruct (hbi_vals E cs R FULL model HC) as (U1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & U3). rewrite U1, U3.
  pose proof Hsp as (_ & _ & Hal). pose proof (u64_range sp).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma hbi_brk0 : forall E cs R FULL model, CSOK E cs R FULL model -> 4096 * VZ E 5 = bv_unsigned brk0.
Proof.
  intros E cs R FULL model HC. destruct (hbi_vals E cs R FULL model HC) as (_ & _ & _ & _ & _ & _ & _ & U & _). rewrite U.
  pose proof (brk_range SEGS A ph sp rdraw brk0 argv envp uid hw IMG Hbrk) as [_ Hm].
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma hbi_sp_range : sp_window_lo <= usp <= sp_window_hi /\ usp mod 16 = 0.
Proof. pose proof Hsp as (H1 & H2 & H3). auto. Qed.

(* [comment removed for export] *)
Lemma hbi_argblock : forall E cs R FULL model, CSOK E cs R FULL model ->
  forall a : word, argH E a = true -> FULL a = wrap_mem ph sp argv envp uid hw rdraw a.
Proof. intros E cs R FULL model HC. exact (proj2 (hb_sinv SEGS A _ _ _ _ E cs R FULL model HC)). Qed.

Lemma hbi_argH : forall E (a : word),
  argH E a = ((uE E e_sp0 <=? bv_unsigned a) &&
              (((usp + 24 <=? bv_unsigned a) && (bv_unsigned a <? usp + 8 * argc + 8 * envc + 24))
              || ((usp + 8 * argc + 8 * envc + 184 <=? bv_unsigned a) && (bv_unsigned a <? usp + 8 * argc + 8 * envc + 184 + 8 * Wsb))
              || ((usp + Z.of_nat (length (build_stack_bytes ph sp argv envp uid hw rdraw)) <=? bv_unsigned a)
                  && (bv_unsigned a <? usp + Z.of_nat (length (entry_stack_image ph sp argv envp uid hw rdraw))))))%bool.   (* [comment removed for export] *)
Proof. reflexivity. Qed.
End Image.

