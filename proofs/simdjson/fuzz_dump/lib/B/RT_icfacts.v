(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout RT_iface R_cache_defs R_prim_defs R_m2s R_fs_defs R_tlsgetaddr RT_state RT_rep RT_facts0 RT_sep RT_facts I_memcpyw I_memsetw I_memchrw I_strnlenw I_strlen I_qck I_consts HandoffImage.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A.Shadow.GW}.
Section IC.
Variables (Σ : rtsA) (m : mem).
Hypothesis HA : ART_A Σ m.

Lemma ro_join2 : forall a c1 c2, ro_cells bsegs m a [c1] -> ro_cells bsegs m (a + Z.of_nat (csize c1)) [c2] -> ro_cells bsegs m a [c1; c2].
Proof.
  intros a c1 c2 [[W1 _] B1] [[W2 _] B2]. split; [split; [exact W1 | split; [exact W2 | exact I]]|].
  cbn [cells_bytes] in *. rewrite app_nil_r in B1, B2. apply bytes_at_app. split; [exact B1|]. rewrite cbytes_length by exact W1. rewrite app_nil_r. exact B2.
Qed.

Lemma rta_icells_all : icells m /\ icells_ms m /\ icells_mc m /\ icells_sn m /\ m2s_cells m.
Proof.
  pose proof (ART_consts Σ m HA) as (_ & (G1 & G2 & G3 & G4 & G5) & _ & MC & _ & _ & _ & (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15 & X16 & X17 & X18 & _)).
  pose proof (ART_fs Σ m HA) as (_ & _ & _ & _ & _ & _ & _ & _ & (dtvbeg & _ & (T1 & _)) & _).
  pose proof MC as (M1 & M2 & M3).
  assert (C80 : ro_cells bsegs m 0x16e1d0 [C8 (Z_to_bv 64 0x177138)]) by exact (ro_head _ _ _ _ (ro_of_rw _ _ _ M1)).
  assert (C38 : ro_cells bsegs m 0x177138 [C8 (Z_to_bv 64 0x7fff8000)]) by exact (ro_of_rw _ _ _ M2).
  split; [unfold icells; split; [exact C80|]; split; [exact X12|]; split; [exact X6|]; split; [exact C38 | exact X13]|].
  split; [unfold icells_ms; split; [exact C80|]; split; [exact X12|]; split; [exact X14|]; split; [exact C38 | exact X13]|].
  split; [unfold icells_mc; split; [exact C80|]; split; [exact X15|]; split; [exact C38 | exact T1]|]. split; [|exact MC].
  unfold icells_sn. split; [apply ro_join2; [exact (ro_of_rw _ _ _ G2) | exact X4]|].
  split; [exact C80|]. split; [exact X15|]. split; [exact X16|]. split; [exact C38|]. split; [exact T1 | exact X18].
Qed.

Lemma rta_icells_sl : icells_sl m.
Proof.
  pose proof (ART_consts Σ m HA) as (_ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X17 & _)).
  exact X17.
Qed.

End IC.

Lemma al8_in : forall L0 H0 x, L0 mod 8 = 0 -> H0 mod 8 = 0 -> L0 <= x < H0 -> L0 <= al8 x /\ al8 x + 8 <= H0.
Proof.
  intros L0 H0 x H1 H2 Hx. unfold al8. apply Z.mod_divide in H1, H2; try (clear; lia). destruct H1 as [a Ha]. destruct H2 as [b Hb]. subst L0 H0.
  assert (a <= x / 8) by (apply Z.div_le_lower_bound; lia). assert (x / 8 < b) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.

Lemma al8_ge : forall x, x - 7 <= al8 x <= x.
Proof. intros x. unfold al8. pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.mod_pos_bound x 8 ltac:(lia)). lia. Qed.

Lemma word_of_stk : forall (m : mem) lo hi a, stk bsegs m lo hi -> lo <= a -> a + 8 <= hi -> exists w, ro_cells bsegs m a [C8 w].
Proof.
  intros m lo hi a S H1 H2. destruct (stk_split bsegs m lo a hi S ltac:(lia)) as [_ S2]. destruct (stk_split bsegs m a (a + 8) hi S2 ltac:(lia)) as [S3 _].
  destruct (HandoffImage.stk_bytes bsegs m a 8%nat S3) as (bs & Hl & Hb).
  destruct (cells_c8_of bsegs m a bs Hl Hb) as (v & Hv). exists v. exact Hv.
Qed.

Lemma qc_of_range : forall (m : mem) L0 H0 p n, stk bsegs m L0 H0 -> L0 mod 8 = 0 -> H0 mod 8 = 0 -> L0 <= shad p -> shad (p + n - 1) < H0 -> 1 <= n ->
  qc_words m p n.
Proof.
  intros m L0 H0 p n S M1 M2 H1 H2 Hn _.
  assert (Hm : shad p <= shad (p + n - 1)) by (unfold shad; apply Z.add_le_mono_r; apply Z.div_le_mono; lia).
  destruct (al8_in L0 H0 (shad p) M1 M2 ltac:(lia)) as (A1 & A2). destruct (al8_in L0 H0 (shad (p + n - 1)) M1 M2 ltac:(lia)) as (B1 & B2).
  destruct (word_of_stk m L0 H0 _ S A1 A2) as (w1 & W1). destruct (word_of_stk m L0 H0 _ S B1 B2) as (w2 & W2). exists w1, w2. split; assumption.
Qed.

Lemma SHB_mod8 : SHB mod 8 = 0. Proof. reflexivity. Qed.

Section SHW.
Variables (Σ : rtsA) (m : mem).
Hypothesis HA : ART_A Σ m.
#[local] Notation L := (lay Σ).
#[local] Notation SB := (l_SB (lay Σ)).

Lemma rta_shw_live : forall p0 k0 s n, In (p0, k0) (live Σ) -> p0 <= s -> s + n <= p0 + k0 -> 1 <= n -> qc_words m s n /\ region_in_mem s n.
Proof.
  intros p0 k0 s n Hin H1 H2 Hn. pose proof (rta_sp0 Σ m HA) as ((X1 & X2) & _). unfold rtA_sp0, sp_window_hi in *.
  destruct (geo_live Σ m HA p0 k0 Hin) as [(c & i & Hc & Hi & -> & Y1 & Y2 & Y3 & Y4 & Y5)|(sc & Hs & Hq & Hn' & -> & Y1 & Y5)].
  - pose proof (ART_prim Σ m HA c Hc) as (_ & _ & _ & _ & _ & _ & SR).
    pose proof (geo_grant Σ m HA (l_PRB L) 0x2000011000 ltac:(unfold startup_grants; left; reflexivity)) as (G1 & G2 & G3 & G4 & G5).
    pose proof (geo_prb Σ m HA) as (P1 & P2 & P3). unfold l_ACEIL, STACK_WIN, rb, kUserCap in *.
    assert (Hrb : (SB + c * 2 ^ 32) mod 64 = 0).
    { apply Z.mod_divide; [lia|]. apply Z.divide_add_r; [apply Z.mod_divide in P3; [|lia]; apply (Z.divide_trans 64 (2 ^ 16)); [exists 1024; reflexivity | exact P3]|].
      exists (c * 2 ^ 26). lia. }
    assert (Ms : forall x, x mod 64 = 0 -> shad x mod 8 = 0).
    { intros x Hx. unfold shad. apply Z.mod_divide in Hx; [|lia]. destruct Hx as [q Hq]. rewrite Hq. replace (q * 64) with ((8 * q) * 8) by ring.
      rewrite Z.div_mul by lia. rewrite Z.add_mod, SHB_mod8 by lia. replace (8 * q) with (q * 8) by ring. rewrite Z.mod_mul by lia. reflexivity. }
    assert (c * 2 ^ 32 + 2 ^ 32 <= 2 ^ 37) by lia.
    split.
    + assert (Hrb2 : (SB + c * 2 ^ 32 + 2 ^ 32) mod 64 = 0) by (rewrite Z.add_mod, Hrb by lia; reflexivity).
      apply (qc_of_range m _ _ s n SR (Ms _ Hrb) (Ms _ Hrb2)); [| | exact Hn].
      * unfold shad. apply Z.add_le_mono_r. apply Z.div_le_mono; lia.
      * unfold shad. assert ((s + n - 1) / 8 < (SB + c * 2 ^ 32 + 2 ^ 32) / 8); [|lia].
        apply Z.div_lt_upper_bound; [lia|]. pose proof (Z.mul_div_le (SB + c * 2 ^ 32 + 2 ^ 32) 8 ltac:(lia)).
        pose proof (Z.div_mod (SB + c * 2 ^ 32 + 2 ^ 32) 8 ltac:(lia)).
        assert ((SB + c * 2 ^ 32 + 2 ^ 32) mod 8 = 0) by (apply (mod8_of _ 64 ltac:(lia)); [exact Hrb2 | exists 8; reflexivity]). lia.
    + unfold region_in_mem; right. unfold kHighShadowEnd, kHighMemEnd, K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi in *. destruct G4 as [G4|G4]; lia.
  - destruct (In_nth_error _ _ Hs) as (k & Hk). pose proof (ART_chunk Σ m HA) as (_ & HS). pose proof (HS k sc Hk) as (_ & _ & _ & _ & SR & _).
    destruct (map_geo Σ m HA k sc Hk) as (Hn0 & (G1 & G2 & G3 & G4 & G5) & _ & M2 & Hroom). unfold s_ubeg in *. rewrite <- Hn' in *.
    unfold l_ACEIL, STACK_WIN in *.

    assert (Ms : forall x, x mod 64 = 0 -> shad x mod 8 = 0).
    { intros x Hx. unfold shad. apply Z.mod_divide in Hx; [|lia]. destruct Hx as [q Hqx]. rewrite Hqx. replace (q * 64) with ((8 * q) * 8) by ring.
      rewrite Z.div_mul by lia. rewrite Z.add_mod, SHB_mod8 by lia. replace (8 * q) with (q * 8) by ring. rewrite Z.mod_mul by lia. reflexivity. }
    assert (Mb : s_mb sc mod 64 = 0).
    { pose proof G2 as X. apply Z.mod_divide; [lia|]. apply Z.mod_divide in X; [|lia]. apply (Z.divide_trans 64 4096); [exists 64; reflexivity | exact X]. }
    assert (Me : (s_mb sc + smsz (s_n sc)) mod 64 = 0).
    { assert (X : (s_mb sc + smsz (s_n sc)) mod 4096 = 0) by (rewrite Z.add_mod, G2, M2 by lia; reflexivity).
      apply Z.mod_divide; [lia|]. apply Z.mod_divide in X; [|lia]. apply (Z.divide_trans 64 4096); [exists 64; reflexivity | exact X]. }
    split.
    + apply (qc_of_range m _ _ s n SR (Ms _ Mb) (Ms _ Me)); [| | exact Hn].
      * unfold shad. apply Z.add_le_mono_r. apply Z.div_le_mono; lia.
      * unfold shad. assert ((s + n - 1) / 8 < (s_mb sc + smsz (s_n sc)) / 8); [|lia].
        apply Z.div_lt_upper_bound; [lia|]. pose proof (Z.div_mod (s_mb sc + smsz (s_n sc)) 8 ltac:(lia)).
        assert ((s_mb sc + smsz (s_n sc)) mod 8 = 0) by (apply (mod8_of _ 64 ltac:(lia)); [exact Me | exists 8; reflexivity]). lia.
    + unfold region_in_mem, kLowMemEnd, kHighShadowEnd, kHighMemEnd, K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi in *. destruct G4 as [G4|G4]; [left | right]; lia.
Qed.

Lemma rta_shw_frame : forall f k s n, In (f, k) (frames Σ) -> f <= s -> s + n <= f + fs_size k - 8 -> 1 <= n -> qc_words m s n /\ region_in_mem s n.
Proof.
  intros f k s n Hin H1 H2 Hn. destruct (rta_frames_align Σ m HA f k Hin) as (Al & Hseg).
  destruct (sep_frame Σ m HA f k Hin) as (X1 & X2 & X3). pose proof (rta_sp0 Σ m HA) as ((Y1 & Y2) & _). unfold rtA_sp0, sp_window_hi in *.
  pose proof (geo_grant Σ m HA (l_FSB L) 0xb09000 ltac:(unfold startup_grants; right; right; right; right; right; left; reflexivity)) as (G1 & G2 & G3 & G4 & G5).
  unfold l_ACEIL, STACK_WIN in *.
  pose proof (ART_fs Σ m HA) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FB). unfold fs_busy in FB.
  destruct (proj1 (Forall_forall _ _) FB (f, k) Hin) as (p & _ & _ & Ws & _). cbn [fst snd] in Ws.
  assert (Hfs : fs_size k mod 64 = 0 /\ 64 <= fs_size k).
  { destruct (rta_frame_in Σ m f k HA Hin) as (Hk & _). unfold fs_size. rewrite Z.shiftl_mul_pow2 by lia.
    destruct Hk as [ -> | [ -> | [ -> | [ -> | [ -> | -> ] ] ] ] ]; cbn; split; [reflexivity | lia | reflexivity | lia | reflexivity | lia | reflexivity | lia | reflexivity | lia | reflexivity | lia]. }
  assert (Ms : shad f mod 8 = 0).
  { unfold shad. apply Z.mod_divide in Al; [|lia]. destruct Al as [q Hq]. rewrite Hq. replace (q * 64) with ((8 * q) * 8) by ring.
    rewrite Z.div_mul by lia. rewrite Z.add_mod, SHB_mod8 by lia. replace (8 * q) with (q * 8) by ring. rewrite Z.mod_mul by lia. reflexivity. }
  assert (Ms2 : (shad f + fs_size k / 8) mod 8 = 0).
  { destruct Hfs as [Hm _]. apply Z.mod_divide in Hm; [|lia]. destruct Hm as [q Hq]. rewrite Hq. replace (q * 64) with ((8 * q) * 8) by ring.
    rewrite Z.div_mul by lia. rewrite Z.add_mod, Ms by lia. replace (8 * q) with (q * 8) by ring. rewrite Z.mod_mul by lia. reflexivity. }
  assert (Hsh : forall x, f <= x < f + fs_size k -> shad f <= shad x < shad f + fs_size k / 8).
  { intros x Hx. destruct Hfs as [Hm _]. apply Z.mod_divide in Hm, Al; try (clear; lia). destruct Al as [a Ha]. destruct Hm as [b Hb].
    unfold shad. rewrite Ha. rewrite Hb in *. replace (b * 64) with ((8 * b) * 8) by ring. rewrite Z.div_mul by lia.
    replace (a * 64) with ((8 * a) * 8) by ring. rewrite Z.div_mul by lia.
    assert (8 * a <= x / 8) by (apply Z.div_le_lower_bound; lia). assert (x / 8 < 8 * a + 8 * b) by (apply Z.div_lt_upper_bound; lia). lia. }
  split.
  - apply (qc_of_range m _ _ s n (wr_at_stk m _ _ Ws ltac:(apply Z.div_pos; lia)) Ms Ms2); [apply (Hsh s); lia | apply (Hsh (s + n - 1)); lia | exact Hn].
  - unfold region_in_mem, kLowMemEnd, kHighShadowEnd, kHighMemEnd, K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi in *. destruct G4 as [G4|G4]; [left | right]; lia.
Qed.

Lemma rta_shw_stack : forall s n, rtA_sp0 Σ - STACK_WIN + 64 <= s -> s + n <= USTACK_TOP - 16 -> 1 <= n -> qc_words m s n /\ region_in_mem s n.
Proof.
  intros s n H1 H2 Hn. pose proof (ART_shadow Σ m HA) as (_ & S & _ & _). pose proof (rta_sp0 Σ m HA) as ((Y1 & Y2) & _).
  unfold rtA_sp0, sp_window_hi, sp_window_lo, l_ACEIL, STACK_WIN, USTACK_TOP in *.
  split.
  - intros _. pose proof (Z.mul_div_le (l_sp0 L - 8388608) 8 ltac:(lia)) as MD.
    assert (A1 : shad (l_sp0 L - 8388608) + 8 <= shad s) by (unfold shad; assert ((l_sp0 L - 8388608) / 8 + 8 <= s / 8) by (apply Z.div_le_lower_bound; lia); lia).
    assert (A2 : shad (s + n - 1) < shad (2 ^ 47)) by (unfold shad; assert ((s + n - 1) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia); change (2 ^ 47 / 8) with (2 ^ 44); lia).
    assert (Hm : shad s <= shad (s + n - 1)) by (unfold shad; apply Z.add_le_mono_r; apply Z.div_le_mono; lia).
    pose proof (al8_ge (shad s)) as B1. pose proof (al8_ge (shad (s + n - 1))) as B2.
    assert (H47 : shad (2 ^ 47) mod 8 = 0) by reflexivity.
    destruct (al8_in (al8 (shad s)) (shad (2 ^ 47)) (shad (s + n - 1))) as (_ & C2); [unfold al8; rewrite Z.mul_comm; apply Z.mod_mul; lia | exact H47 | lia|].
    destruct (al8_in (al8 (shad s)) (shad (2 ^ 47)) (shad s)) as (_ & C1); [unfold al8; rewrite Z.mul_comm; apply Z.mod_mul; lia | exact H47 | lia|].
    destruct (word_of_stk m _ _ (al8 (shad s)) S ltac:(lia) C1) as (w1 & W1). destruct (word_of_stk m _ _ (al8 (shad (s + n - 1))) S ltac:(lia) C2) as (w2 & W2).
    exists w1, w2. split; assumption.
  - unfold region_in_mem, kHighShadowEnd, kHighMemEnd. right. lia.
Qed.

Lemma rta_shw_img : forall s n, 0x10000 <= s -> s + n <= SEGTOP_A -> 1 <= n -> qc_words m s n /\ region_in_mem s n.
Proof.
  intros s n H1 H2 Hn. pose proof (ART_shadow Σ m HA) as (_ & _ & S & _). unfold SEGTOP_A in *.
  split.
  - apply (qc_of_range m _ _ s n S); [reflexivity | reflexivity | | | exact Hn].
    + unfold pg_dn, shad, SHB. assert (8192 <= s / 8) by (apply Z.div_le_lower_bound; lia). change ((0x10000 / 8 + 2147450880) / 4096 * 4096) with 2147459072. lia.
    + unfold shad, SHB. assert ((s + n - 1) / 8 < 0xd9a00) by (apply Z.div_lt_upper_bound; lia). change (0x6cd000 / 8 + 2147450880) with 2148342272. lia.
  - unfold region_in_mem, kLowMemEnd. left. lia.
Qed.

End SHW.

End GWIN.
