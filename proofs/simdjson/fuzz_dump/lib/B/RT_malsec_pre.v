(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS MState ITree.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require BackingAlgebra.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout RT_iface D_defs R_cache_defs R_prim_defs R_glue_defs R_thread R_m2s R_sec_defs R_fs_defs R_mmapordie R_secalloc R_comballoc2 R_asan_defs R_allocate1 RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep RT_freelift RT_geo0 RT_fkit RT_maltail RT_malcore_stmt RT_malcore_m RT_sys_stmt RT_vis RT_malsec_state RT_malsec_front RT_malsec_front2 RT_malsec_tail RT_malsec_rev.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.

#[local] Existing Instance OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A.Shadow.GWf.
Lemma nretA_mem_zeros : forall (ms : machine_state) (P len : word),
  ms_mem (nretA ms (mkEffect P [] [(P, len)])) = apply_zeros (ms_mem ms) [(P, len)].
Proof. intros ms P len. reflexivity. Qed.

Lemma zeros_munch : forall (m : mem) P len, 0 <= P -> 0 <= len -> P + len < 2 ^ 64 ->
  munch [(P, P + len)] m (apply_zeros m [(Z_to_bv 64 P, Z_to_bv 64 len)]).
Proof.
  intros m P len H1 H2 H3 x Hx. cbn [outside] in Hx. destruct Hx as [Hx _]. unfold apply_zeros, zeros_cover. cbn [existsb fst snd].
  rewrite !unsigned_lit by lia. rewrite orb_false_r.
  replace ((P <=? bv_unsigned x) && (bv_unsigned x <? P + len)) with false by (symmetry; apply andb_false_iff; lia). reflexivity.
Qed.

Lemma zeros_wmono : forall (m : mem) zs, wmono bsegs m (apply_zeros m zs).
Proof.
  intros m zs x Hx. unfold apply_zeros. destruct zs as [|z zs]; [exact Hx|]. unfold wview in *.
  destruct (zeros_cover (z :: zs) x); [discriminate | exact Hx].
Qed.

Lemma ro_addr_above : forall a : word, SEGTOP_A <= bv_unsigned a -> ro_addr bsegs a = false.
Proof. intros a H. unfold ro_addr. rewrite (find_segment1_none_above bsegs SEGTOP_A _ asegs_below H). reflexivity. Qed.

Lemma zeros_mem_inv : forall (m : mem) P len, mem_inv bsegs m -> SEGTOP_A <= P -> P + len <= 2 ^ 47 -> 0 <= len ->
  mem_inv bsegs (apply_zeros m [(Z_to_bv 64 P, Z_to_bv 64 len)]).
Proof.
  intros m P len MI H1 H2 H3. apply mem_inv_intro; [intros a Ha; exact (mem_inv_seg_below bsegs m a MI Ha)|].
  intros a b Hb. unfold apply_zeros, zeros_cover in Hb. cbn [existsb fst snd] in Hb. rewrite orb_false_r in Hb.
  rewrite !unsigned_lit in Hb by (unfold SEGTOP_A in *; lia).
  destruct ((P <=? bv_unsigned a) && (bv_unsigned a <? P + len)) eqn:E.
  - apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
    split; [apply ro_addr_above; lia | unfold UTOP; lia].
  - split; [exact (mem_inv_ro bsegs m a b MI Hb) | exact (mem_inv_ov_below bsegs m a b MI Hb)].
Qed.

Section Reveal.
Variables (A A' : list (Z * Z)) (mo : Model) (ms0 ms : machine_state).
Hypothesis HR : revealed A A' mo ms0 ms.
Hypothesis HH0 : forall a, HID A mo a = true -> ms_mem ms0 a = None /\ SEGTOP_A <= bv_unsigned a.
Hypothesis HH1 : forall a, HID A' mo a = true -> ms_mem ms a = None.

Lemma reveal_mem_inv : mem_inv bsegs (ms_mem ms0) -> mem_inv bsegs (ms_mem ms).
Proof using HR HH0 HH1.
  intros MI. destruct HR as (_ & Hv & _).
  apply mem_inv_intro; [intros a Ha; exact (mem_inv_seg_below bsegs _ a MI Ha)|].
  intros a b Hb. destruct (HID A mo a) eqn:E1.
  - destruct (HID A' mo a) eqn:E2; [rewrite (HH1 a E2) in Hb; discriminate|].
    destruct (HH0 a E1) as (_ & Ht). unfold HID in E2. apply orb_false_iff in E2 as [_ E3]. apply Z.leb_gt in E3.
    split; [exact (ro_addr_above a Ht) | unfold UTOP; lia].
  - rewrite (Hv a E1) in Hb. split; [exact (mem_inv_ro bsegs _ a b MI Hb) | exact (mem_inv_ov_below bsegs _ a b MI Hb)].
Qed.
End Reveal.

Section Map.
Variables (Σ : rtsA) (m : mem) (P n : Z).
Hypothesis HA : ART_A Σ m.
Hypothesis HG : sgrant_ok Σ P (smsz n).
Hypothesis Hn : 64512 < n <= 0x20001000.
#[local] Notation L := (lay Σ).
#[local] Notation msz := (smsz n).

Lemma mp_avoid : art_avoid [(P, P + msz)] Σ.
Proof using HA HG Hn.
  pose proof (rv_map Σ m P n HA HG Hn) as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9).
  assert (R_img : forall a k, 0x10000 <= a -> a + k <= SEGTOP_A -> disjoint_from CS_W a k -> disjoint_from [(P, P + msz)] a k)
    by (intros a k H1 H2 _; cbn [disjoint_from]; split; [lia | exact I]).
  assert (R_grant : forall b gn a k, In (b, gn) (startup_grants L) -> apart b gn (l_PRB L) 0x2000011000 -> apart b gn (l_FSB L) 0xb09000 ->
            b <= a -> a + k <= b + gn -> disjoint_from [(P, P + msz)] a k).
  { intros b gn a k Hin _ _ H1 H2. pose proof (rv_grant_apart Σ m P n HA HG b gn Hin) as X. unfold apart in X.
    cbn [disjoint_from]. split; [lia | exact I]. }
  assert (R_shad : forall lo hi a k, lo mod 8 = 0 -> hi mod 8 = 0 -> 0 <= lo -> hi <= 2 ^ 47 -> shad lo <= a -> a + k <= shad hi ->
            (forall f k', In (f, k') (frames Σ) -> hi <= f \/ f + fs_size k' <= lo) -> disjoint_from [(P, P + msz)] a k).
  { intros lo hi a k H1 H2 H3 H4 H5 H6 _. cbn [disjoint_from]. split; [|exact I].
    assert (shad hi <= 2 ^ 44 + SHB) by (unfold shad; assert (hi / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia); lia).
    assert (SHB <= shad lo) by (unfold shad; pose proof (Z.div_pos lo 8 ltac:(lia) ltac:(lia)); lia).
    unfold SHB, K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi in *. lia. }
  assert (R_prb : forall a k, l_PRB L <= a -> a + k <= l_PRB L + 0x2000011000 ->
            (forall c i n', 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some (CkAlloc n') ->
               a + k <= p_ubeg (l_SB L) c i n' \/ p_ubeg (l_SB L) c i n' + n' <= a) -> disjoint_from [(P, P + msz)] a k).
  { intros a k H1 H2 _. pose proof (rv_grant_apart Σ m P n HA HG (l_PRB L) 0x2000011000 ltac:(unfold startup_grants; left; reflexivity)) as X.
    unfold apart in X. cbn [disjoint_from]. split; [lia | exact I]. }
  assert (R_secmap : forall k0 s0 a k, nth_error (sec Σ) k0 = Some s0 -> s_mb s0 <= a -> a + k <= s_mb s0 + smsz (s_n s0) ->
            (s_quar s0 = false -> a + k <= s_ubeg s0 \/ s_ubeg s0 + s_n s0 <= a) -> disjoint_from [(P, P + msz)] a k).
  { intros k0 s0 a k Hk H1 H2 _. destruct HG as (_ & Hap).
    pose proof (proj1 (Forall_forall _ _) Hap (secmap s0) ltac:(unfold rt_maps; apply in_or_app; left;
      apply in_map; apply (proj1 (in_rev (sec Σ) s0)); exact (nth_error_In _ _ Hk))) as Y.
    pose proof (rv_sec_app Σ m HA k0 s0 Hk) as (_ & Z1 & Z2). pose proof (fk_map Σ (geo_of_ART Σ m HA) k0 s0 Hk) as (_ & _ & Z3 & _).
    pose proof (fk_aceil Σ (geo_of_ART Σ m HA)) as (_ & Z4).
    unfold secmap in Y. cbn [fst snd] in Y. rewrite !unsigned_lit in Y by lia. unfold apart in Y.
    cbn [disjoint_from]. split; [lia | exact I]. }
  assert (R_fsb : forall a k, l_FSB L <= a -> a + k <= l_FSB L + 0xb09000 ->
            (forall f k', In (f, k') (frames Σ) -> a + k <= f \/ f + fs_size k' - 8 <= a) -> disjoint_from [(P, P + msz)] a k).
  { intros a k H1 H2 _. pose proof (rv_grant_apart Σ m P n HA HG (l_FSB L) 0xb09000 ltac:(unfold startup_grants; right; right; right; right; right; left; reflexivity)) as X.
    unfold apart in X. cbn [disjoint_from]. split; [lia | exact I]. }
  destruct (art_avoid_gen Σ m [(P, P + msz)] HA R_img R_grant (fun lo hi a k H1 H2 H3 H4 H5 H6 H7 _ => R_shad lo hi a k H1 H2 H3 H4 H5 H6 H7)
              R_prb R_secmap) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
  pose proof (av_fs Σ m [(P, P + msz)] HA R_img R_grant R_shad R_fsb) as A10.
  split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|]. split; [exact A5|]. split; [exact A6|].
  split; [exact A7|]. split; [exact A10|]. split; [exact A8 | exact A9].
Qed.
End Map.

Section Client.
Variables (Σ : rtsA) (m : mem) (P n sp : Z).
Hypothesis HA : ART_A Σ m.
Hypothesis HG : sgrant_ok Σ P (smsz n).
Hypothesis Hn : 64512 < n <= 0x20001000.
Hypothesis Hsp : l_ACEIL (lay Σ) <= sp.
#[local] Notation L := (lay Σ).
#[local] Notation msz := (smsz n).

Lemma cl_live : forall p k x, In (p, k) (live Σ) -> p <= x < p + k ->
  (x < K_LOW_SHADOW_lo \/ K_HIGH_SHADOW_hi <= x) /\ (x < P \/ P + msz <= x).
Proof using HA HG Hn.
  intros p k x Hin Hx. pose proof (geo_of_ART Σ m HA) as HGo.
  destruct (geo_live Σ m HA p k Hin) as [(c & i & Hc & Hi & Ep & Y1 & Y2 & Y3 & Y4 & Y5)|(s & Hs & Hq & Hsn & Ep & Y1 & Y5)].
  - pose proof (g_grant Σ HGo (l_PRB L) 0x2000011000 ltac:(unfold startup_grants; left; reflexivity)) as (_ & _ & _ & G4 & _).
    pose proof (g_prb Σ HGo) as (P1 & P2 & P3).
    pose proof (rv_grant_apart Σ m P n HA HG (l_PRB L) 0x2000011000 ltac:(unfold startup_grants; left; reflexivity)) as Ap.
    unfold rb, kUserCap, apart in *. assert (c * 2 ^ 32 + 2 ^ 32 <= 2 ^ 37) by lia. lia.
  - destruct (In_nth_error _ _ Hs) as (k0 & Hk0). pose proof (rv_sec_app Σ m HA k0 s Hk0) as (X & _ & _).
    destruct HG as (_ & Hap).
    pose proof (proj1 (Forall_forall _ _) Hap (secmap s) ltac:(unfold rt_maps; apply in_or_app; left;
      apply in_map; apply (proj1 (in_rev (sec Σ) s)); exact Hs)) as Y.
    pose proof (fk_map Σ HGo k0 s Hk0) as (_ & Z1 & Z3 & _). pose proof (fk_aceil Σ HGo) as (_ & Z4).
    unfold secmap in Y. cbn [fst snd] in Y. rewrite !unsigned_lit in Y by (pose proof (rv_sec_app Σ m HA k0 s Hk0); lia).
    unfold apart, s_ubeg in *. rewrite <- Hsn in *. lia.
Qed.

Lemma cl_outside : forall x, aclient (live Σ) (frames Σ) sp x -> (x < P \/ P + msz <= x) /\ outside (W_rev Σ P n) x.
Proof using HA HG Hn Hsp.
  intros x Hx. pose proof (geo_of_ART Σ m HA) as HGo. pose proof (rv_map Σ m P n HA HG Hn) as (M1 & M2 & M3 & M4 & M5 & _).
  pose proof (fk_aceil Σ HGo) as (X1 & X2).
  assert (APP : forall y, (y < K_LOW_SHADOW_lo \/ K_HIGH_SHADOW_hi <= y) -> outside (W_rev Σ P n) y).
  { intros y Hy. apply (disjoint_outside _ y 1); [apply (rv_app Σ m P n HA HG Hn); lia | lia]. }
  destruct Hx as [H|[H|[H|[H|H]]]].
  - split; [lia|]. apply APP. unfold K_HIGH_SHADOW_hi, SHB in *. lia.
  - destruct H as ((lo & hi & Hin & Hlh) & _). unfold CLIENT_STATIC in Hin.
    assert (x < SEGTOP_A) by (destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; unfold SEGTOP_A; lia).
    split; [lia|]. apply APP. unfold SEGTOP_A, K_LOW_SHADOW_lo in *. lia.
  - destruct H as (p & k & Hin & Hpx). destruct (cl_live p k x Hin Hpx) as (Y1 & Y2). split; [exact Y2 | apply APP; exact Y1].
  - destruct H as (f & k & Hin & Hfx). destruct (g_frame Σ HGo f k Hin) as (Y1 & Y2 & Y3).
    pose proof (g_grant Σ HGo (l_FSB L) 0xb09000 ltac:(unfold startup_grants; right; right; right; right; right; left; reflexivity)) as (_ & _ & _ & G4 & _).
    pose proof (rv_grant_apart Σ m P n HA HG (l_FSB L) 0xb09000 ltac:(unfold startup_grants; right; right; right; right; right; left; reflexivity)) as Ap.
    unfold apart in Ap. split; [lia|]. apply APP. lia.
  - destruct H as (f & k & Hin & Hfx). destruct (g_frame Σ HGo f k Hin) as (Y1 & Y2 & Y3).
    pose proof (rv_grant_apart Σ m P n HA HG (l_FSB L) 0xb09000 ltac:(unfold startup_grants; right; right; right; right; right; left; reflexivity)) as Ap.
    pose proof (g_grant Σ HGo (l_FSB L) 0xb09000 ltac:(unfold startup_grants; right; right; right; right; right; left; reflexivity)) as (G1 & _ & G3 & G4 & _).
    assert (Hf8 : f mod 8 = 0 /\ fs_size k mod 8 = 0).
    { pose proof (g_frame_in Σ HGo f k Hin) as (Hk & _). pose proof HGo as (_ & _ & _ & HF). destruct HF as (_ & _ & _ & _ & _ & _ & HF & _).
      pose proof (proj1 (Forall_forall _ _) HF (f, k) Hin) as (_ & (p & Hp & Hfa & _)). cbn [fst snd] in Hfa.
      pose proof (g_grant Σ HGo (l_FSB L) 0xb09000 ltac:(unfold startup_grants; right; right; right; right; right; left; reflexivity)) as (_ & G2 & _).
      apply Z.mod_divide in G2; [|lia]. destruct G2 as [q Eq]. split.
      - rewrite Hfa. unfold frame_addr, fsz. rewrite Eq. apply Z.mod_divide; [lia|].
        exists (512 * q + 4608 + Z.of_nat k * 2 ^ 17 + p * 8 * 2 ^ Z.of_nat k). ring.
      - unfold fs_size. rewrite Z.shiftl_mul_pow2 by lia. apply Z.mod_divide; [lia|]. exists (8 * 2 ^ Z.of_nat k). ring. }
    destruct Hf8 as (Hf8 & Hk8).
    pose proof (rv_fshad Σ m P n HA HG Hn f (fs_size k) ltac:(lia) ltac:(lia) ltac:(lia)) as D.
    pose proof (shad_add8 f (fs_size k) Hf8 Hk8) as E.
    assert (SH : SHB <= shad f) by (unfold shad; pose proof (Z.div_pos f 8 ltac:(lia) ltac:(lia)); lia).
    assert (shad (f + fs_size k) <= K_HIGH_SHADOW_hi).
    { unfold shad, K_HIGH_SHADOW_hi, SHB. assert ((f + fs_size k) / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia). lia. }
    split; [unfold SHB, K_HIGH_SHADOW_hi, K_LOW_SHADOW_lo in *; lia|].
    apply (disjoint_outside _ (shad f) (fs_size k / 8) x D). lia.
Qed.
End Client.

Section BPre.
Variables (Σ : rtsA) (PMc : Model -> Prop) (mX : mem) (B : Z) (gp s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A : word)
          (F : bvmap 5 word) (fc : bv 32) (n lo P : Z) (tr : list Z) (tb : list word) (j0 : list byte).
Hypothesis Hn : 64512 < n <= 0x20001000.
Hypothesis HA : ART_A Σ mX.
Hypothesis MI : mem_inv bsegs mX.
Hypothesis LOW : l_ACEIL (lay Σ) <= lo.
Hypothesis LOR : lo + 0x1000 <= B + -144.
Hypothesis SPT : B + 2144 <= USTACK_TOP.
Hypothesis Htrl : (1 <= length tr <= 30)%nat.
Hypothesis TRC : trc_cells B tr mX tb.
Hypothesis AFC : af_cells B s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A mX j0.
Hypothesis HG : sgrant_ok Σ P (smsz n).
#[local] Notation L := (lay Σ).
#[local] Notation T := (l_T (lay Σ)).
#[local] Notation msz := (smsz n).
#[local] Notation SZ := (needed2 n).

Definition bpre (ms : machine_state) : Prop :=
  exists (t0' t1' t2' a6' t3' t4' t5' t6' : word) (mA : mem),
    ms = nret (MSsvc (mod_regs (Z_to_bv 64 sa_retA) (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (B + -192)) - 96)) gp (Z_to_bv 64 tpA)
                       t0' t1' t2' a6' (sa_msz SZ) (Z_to_bv 64 sec_name) (Z_to_bv 64 SZ) (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 8)
                       (Z_to_bv 64 INST) (Z_to_bv 64 B) (Z_to_bv 64 7) (Z_to_bv 64 7) (Z_to_bv 64 T) (Z_to_bv 64 1) t3' t4' t5' t6')
                     F (Z_to_bv 64 sec_mmap_ecall) (Z_to_bv 64 222) fc None mA (seg_rom bsegs))
              (mkEffect (Z_to_bv 64 P) [] [(Z_to_bv 64 P, Z_to_bv 64 (roundup4k (sa_msz SZ)))])
    /\ ART_A Σ mA /\ mem_inv bsegs mA /\ wmono bsegs mX mA
    /\ (forall a : word, aclient (live Σ) (frames Σ) (B + -16) (bv_unsigned a) -> mA a = mX a)
    /\ vis_rep (lay Σ) (shw P n :: rtA_allow Σ) mA
    /\ rw_cells bsegs mA (B + -192) [C8 (Z_to_bv 64 (rz_size n)); C8 (Z_to_bv 64 SZ); C8 (Z_to_bv 64 8);
                                      C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 (Z.b2z (from_primary n))); C8 (Z_to_bv 64 0x59274)]
    /\ sa_frame mA (Z_to_bv 64 (B + -192)) (Z_to_bv 64 comballoc_retS) (Z_to_bv 64 8) (Z_to_bv 64 n) (Z_to_bv 64 8) (Z_to_bv 64 SZ)
         (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n) (Z_to_bv 64 INST) (Z_to_bv 64 B) (Z_to_bv 64 (0 + - (8))) (Z_to_bv 64 7)
    /\ mod_frame mA (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (B + -192)) - 96)) (Z_to_bv 64 sa_retA) (Z_to_bv 64 GSTAT) (Z_to_bv 64 SEC)
         (Z_to_bv 64 (sa_msz SZ))
    /\ stk bsegs mA lo (bv_unsigned (Z_to_bv 64 (B + -192)) - 144)
    /\ mm_gcells mA /\ sec_page mA /\ name_cells mA
    /\ af_cells B s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A mA j0 /\ trc_cells B tr mA tb.

Lemma bp_pre : forall ms, fA Σ PMc mX B gp F fc n lo P ms -> bpre ms.
Proof using Hn HA MI LOW LOR SPT Htrl TRC AFC HG.
  intros ms (ms0 & mo & (HM & _) & (ms1 & (m1 & MU1 & WM1 & FR1 & HA1) & E0) & HRev & HH0 & HH1).
  destruct HA1 as (t0' & t1' & t2' & a6' & t3' & t4' & t5' & t6' & m1e & E1 & MU2 & WM2 & MI2 & SAF & MODF & ST2 & MM2 & PG2 & NM2).
  pose proof (rv_map Σ mX P n HA HG Hn) as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9).
  pose proof (smsz_sa n Hn) as (Z1 & Z2 & Z3).
  assert (RS : 0 <= B + -192 < 2 ^ 64) by (unfold l_ACEIL, USTACK_TOP in *; lia).
  rewrite unsigned_lit in MU2 by exact RS.

  assert (Hsp1 : rtA_sp0 Σ - STACK_WIN <= B + -640) by (unfold l_ACEIL, rtA_sp0 in *; lia).
  assert (MUC : munch (W_client Σ (B + -640)) mX m1e).
  { apply (munch_trans _ mX m1 m1e).
    - eapply (munch_weaken _ _ mX m1); [|exact MU1]. intros x Hx. unfold W_client in Hx. cbn [app outside] in Hx |- *.
      destruct Hx as (X1 & _). split; [lia | exact I].
    - eapply (munch_weaken _ _ m1 m1e); [|exact MU2]. intros x Hx. unfold W_client in Hx. cbn [app outside] in Hx |- *.
      destruct Hx as (X1 & _). split; [lia | exact I]. }
  pose proof (wmono_trans bsegs _ _ _ WM1 WM2) as WMe.
  pose proof (ART_transport _ Σ mX m1e HA MUC WMe (art_avoid_client Σ mX (B + -640) HA Hsp1)) as ART1.

  assert (E0m : ms_mem ms0 = apply_zeros m1e [(Z_to_bv 64 P, Z_to_bv 64 msz)]) by (rewrite E0, nretA_mem_zeros, E1; reflexivity).
  pose proof (zeros_munch m1e P msz ltac:(lia) ltac:(lia) ltac:(lia)) as MU3. rewrite <- E0m in MU3.
  pose proof (zeros_wmono m1e [(Z_to_bv 64 P, Z_to_bv 64 msz)]) as WM3. rewrite <- E0m in WM3.
  pose proof (ART_transport _ Σ m1e (ms_mem ms0) ART1 MU3 WM3 (mp_avoid Σ m1e P n ART1 HG Hn)) as ART0.

  pose proof (reveal_munch (rtA_allow Σ) [shw P n] mo ms0 ms HRev HH0 HH1 (W_rev Σ P n) (rev_munch_hyp Σ (ms_mem ms0) P n ART0 HG Hn)) as MU4.
  pose proof (reveal_wmono (rtA_allow Σ) [shw P n] mo ms0 ms HRev HH0) as WM4.
  pose proof (ART_transport _ Σ (ms_mem ms0) (ms_mem ms) ART0 MU4 WM4 (rev_avoid Σ (ms_mem ms0) P n ART0 HG Hn)) as ARTA.
  pose proof (ART_wf Σ mX HA) as (HL & _).

  assert (E5 : ms = nretA (set_mem ms1 (ms_mem ms)) (mkEffect (Z_to_bv 64 P) [] [(Z_to_bv 64 P, Z_to_bv 64 msz)]))
    by (apply (nret_revealed (rtA_allow Σ) (shw P n :: rtA_allow Σ) mo ms0 ms1 ms P msz ltac:(lia) ltac:(lia) ltac:(lia) E0 HRev);
        intros a Ha; exact (map_range_visible Σ P n mo a HL HM HG Ha)).

  assert (TR : forall a cs, rw_cells bsegs m1e a cs -> (a + Z.of_nat (cells_size cs) <= P \/ P + msz <= a) ->
            (a + Z.of_nat (cells_size cs) <= K_LOW_SHADOW_lo \/ K_HIGH_SHADOW_hi <= a) -> rw_cells bsegs (ms_mem ms) a cs).
  { intros a cs X D1 D2. apply (rw_cells_transport bsegs _ (ms_mem ms0) _ _ _ (rw_cells_transport bsegs _ m1e _ _ _ X MU3 WM3
      ltac:(cbn [disjoint_from]; split; [lia | exact I])) MU4 WM4). exact (rv_app Σ (ms_mem ms0) P n ART0 HG Hn _ _ D2). }
  pose proof (fk_aceil Σ (geo_of_ART Σ mX HA)) as (X1 & X2).
  assert (SP : K_HIGH_SHADOW_hi <= B + -640 /\ P + msz <= B + -640) by (unfold K_HIGH_SHADOW_hi, SHB in *; lia).
  assert (M5' : 0x6cd000 <= P) by exact M5.
  exists t0', t1', t2', a6', t3', t4', t5', t6', (ms_mem ms). split.
  { rewrite E5 at 1. rewrite E1, <- Z2. reflexivity. }
  split; [exact ARTA|].
  split; [apply (reveal_mem_inv (rtA_allow Σ) (shw P n :: rtA_allow Σ) mo ms0 ms HRev HH0 HH1); rewrite E0m;
          apply zeros_mem_inv; [exact MI2 | exact M5 | lia | lia]|].
  split; [exact (wmono_trans bsegs _ _ _ WMe (wmono_trans bsegs _ _ _ WM3 WM4))|].
  split.
  { intros a Ha. destruct (cl_outside Σ mX P n (B + -16) HA HG Hn ltac:(lia) _ Ha) as (Y1 & Y2).
    rewrite (MU4 a Y2). rewrite (MU3 a ltac:(cbn [outside]; split; [lia | exact I])).
    destruct (aclient_split Σ mX (B + -16) _ HA Ha) as [Y|Y].
    - rewrite (MU2 a ltac:(cbn [outside]; split; [lia | exact I])). apply MU1. cbn [outside]. split; [lia | exact I].
    - rewrite (MU2 a ltac:(cbn [outside]; split; [lia | exact I])). apply MU1. cbn [outside]. split; [lia | exact I]. }
  split.
  { pose proof HM as (_ & _ & _ & _ & (_ & _ & _ & _ & _ & SL & _)).
    exact (vis_rep_reveal (rtA_allow Σ) [shw P n] mo ms0 ms HRev (lay Σ) SL (ART_vis Σ (ms_mem ms0) ART0)). }
  split.
  { apply TR; [|cs_size; lia | cs_size; lia]. apply (rw_cells_transport bsegs _ m1 m1e _ _ FR1 MU2 WM2). cs_size.
    cbn [disjoint_from]. split; [lia | exact I]. }
  split; [destruct SAF as (j & SAF); exists j; apply TR; [exact SAF | rewrite unsigned_lit by exact RS; cs_size; lia
                                                          | rewrite unsigned_lit by exact RS; cs_size; lia]|].
  split; [destruct MODF as (j & MODF); exists j; apply TR; [exact MODF | rewrite (unsigned_lit (B + -192)) by exact RS;
             rewrite unsigned_lit by lia; cs_size; lia | rewrite (unsigned_lit (B + -192)) by exact RS; rewrite unsigned_lit by lia; cs_size; lia]|].
  split; [exact (stk_wmono _ _ _ _ (stk_wmono _ _ _ _ ST2 WM3) WM4)|].
  split.
  { unfold mm_gcells in *. destruct MM2 as (G1 & G2 & G3 & G4 & G5).
    split; [apply TR; [exact G1 | cs_size; lia | cs_size; unfold K_LOW_SHADOW_lo; lia]|].
    split; [apply TR; [exact G2 | cs_size; lia | cs_size; unfold K_LOW_SHADOW_lo; lia]|].
    split; [apply TR; [exact G3 | cs_size; lia | cs_size; unfold K_LOW_SHADOW_lo; lia]|].
    split; [apply TR; [exact G4 | cs_size; lia | cs_size; unfold K_LOW_SHADOW_lo; lia]|].
    apply TR; [exact G5 | cs_size; lia | cs_size; unfold K_LOW_SHADOW_lo; lia]. }
  split; [unfold sec_page in *; apply TR; [exact PG2 | cs_size; unfold i_sec_page, INST, g_instance, SEGTOP_A in *; lia
                                           | cs_size; unfold i_sec_page, INST, g_instance, K_LOW_SHADOW_lo; lia]|].
  split; [unfold name_cells in *; destruct NM2 as (N1 & N2); split; [apply TR; [exact N1 | cs_size; lia | cs_size; unfold K_LOW_SHADOW_lo; lia]
                                                                   | apply TR; [exact N2 | cs_size; lia | cs_size; unfold K_LOW_SHADOW_lo; lia]]|].
  assert (D4 : forall a k, K_HIGH_SHADOW_hi <= a -> disjoint_from (W_rev Σ P n) a k)
    by (intros a k H; exact (rv_app Σ (ms_mem ms0) P n ART0 HG Hn _ _ (or_intror H))).
  split.
  { pose proof (af_transport B s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A tr Htrl _ mX m1 j0 AFC MU1 WM1
                  ltac:(cbn [disjoint_from]; split; [lia | exact I])) as AF1.
    pose proof (af_transport B s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A tr Htrl _ m1 m1e j0 AF1 MU2 WM2
                  ltac:(cbn [disjoint_from]; split; [lia | exact I])) as AF2.
    pose proof (af_transport B s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A tr Htrl _ m1e (ms_mem ms0) j0 AF2 MU3 WM3
                  ltac:(cbn [disjoint_from]; split; [lia | exact I])) as AF3.
    exact (af_transport B s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A tr Htrl _ (ms_mem ms0) (ms_mem ms) j0 AF3 MU4 WM4
             (D4 (B + -144) 128 ltac:(lia))). }
  destruct TRC as (T1 & T2 & T3). split; [|split; [|exact T3]].
  - pose proof (rw_cells_transport bsegs _ mX _ _ _ T1 MU1 WM1 ltac:(cs_size; cbn [disjoint_from]; split; [lia | exact I])) as X.
    pose proof (rw_cells_transport bsegs _ m1 _ _ _ X MU2 WM2 ltac:(cs_size; cbn [disjoint_from]; split; [lia | exact I])) as X'.
    pose proof (rw_cells_transport bsegs _ m1e _ _ _ X' MU3 WM3 ltac:(cs_size; cbn [disjoint_from]; split; [lia | exact I])) as X''.
    exact (rw_cells_transport bsegs _ (ms_mem ms0) _ _ _ X'' MU4 WM4 (D4 B _ ltac:(lia))).
  - pose proof (u64arr_transport bsegs _ mX _ _ _ T2 MU1 WM1 ltac:(cbn [disjoint_from]; split; [lia | exact I])) as X.
    pose proof (u64arr_transport bsegs _ m1 _ _ _ X MU2 WM2 ltac:(cbn [disjoint_from]; split; [lia | exact I])) as X'.
    pose proof (u64arr_transport bsegs _ m1e _ _ _ X' MU3 WM3 ltac:(cbn [disjoint_from]; split; [lia | exact I])) as X''.
    exact (u64arr_transport bsegs _ (ms_mem ms0) _ _ _ X'' MU4 WM4 (D4 (B + 16) _ ltac:(lia))).
Qed.
End BPre.
