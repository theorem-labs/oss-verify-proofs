(* check_latest_sent_seg_kit: the machine-level lemmas the ASan image-B walk of check_latest_sent shares between
   its footprint runs (lib/B/Prog/check_latest_sent_seg_runs*.v) and its caller-journal glue (check_latest_sent_cgW.v).
   Nothing here is a walk and nothing here mentions a journal.
     - the world relation at the machine's view (B/Prog/check_state_wake_c.v csw_view): a load inside one payload
       (cls_rd), a store inside one payload (cls_tw_wr and its 4-byte form), and a store that misses every payload
       (cls_tw_out, over the hull [G_HARNESS_B_LO, G_HARNESS_B_HI) of B/TransportGB.v);
     - the writable bytes the walk stores into (cls_wrange / cls_wok) and the store_ok each store needs;
     - what an instrumented check reads (cls_sh_load, the ASan shape of fuzz_decode's check_cursor_step_F.v),
       and the footprint entry of one shadow byte of g_cmd's or g_q's payload (cls_shc, cls_shq);
     - `addressable` kept by a store into application memory (cls_addr_store);
     - the machine words of the comparisons the code makes. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK1b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import
  PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge ExecF StepF.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
  AsanKA AsanKAProof TWorldB check_state_wake_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TWorldLemmas TCb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Module TWK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TCK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TGK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TWLK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module DSK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.

(* ------------------------------------------------------------------ *)
(* the world at the machine's view                                     *)
(* ------------------------------------------------------------------ *)

(* a load of c bytes at b + k inside ONE payload, in the form the kit's load step reads *)
Lemma cls_rd : forall (m : word -> option byte) Bw o b n k (c : nat),
  tw_at TMAP_B (csw_view m) Bw -> In (o, b, n) TMAP_B -> 0 <= k -> k + Z.of_nat c <= n ->
  ov_read_bytes rsegs m (wa (b + k)) c = Some (TWK.sub Bw (o + k) c).
Proof.
  intros m Bw o b n k c HW Hin Hk Hkc.
  pose proof (tw_row TMAP_B o b n TMAP_B_ok Hin) as (Ho & Hn & HoW & Hb & Hb64).
  pose proof (tw_bytes_at rsegs m TMAP_B Bw o b n k c TMAP_B_ok HW Hin Hk Hkc) as BF.
  assert (LB : Z.of_nat (length Bw) = TWK.W_LEN).
  { rewrite (tw_len TMAP_B _ Bw HW). apply Z2Nat.id. unfold TWK.W_LEN. lia. }
  assert (L : length (TWK.sub Bw (o + k) c) = c) by (apply TWLK.length_sub; lia).
  replace (wa (b + k)) with (wa (b + k + 0)) by (unfold wa; f_equal; lia).
  rewrite (bytes_at_read rsegs m (b + k) _ 0 c BF ltac:(lia)) by (rewrite L; lia).
  cbn [Z.to_nat skipn]. f_equal. apply firstn_all2. rewrite L. lia.
Qed.

(* a store of the bytes bs at b + k inside ONE payload: the world takes upd *)
Lemma cls_tw_wr : forall (m : word -> option byte) Bw o b n k (bs : list byte),
  tw_at TMAP_B (csw_view m) Bw -> In (o, b, n) TMAP_B -> 0 <= k ->
  k + Z.of_nat (length bs) <= n ->
  tw_at TMAP_B (csw_view (write_to_mem m (wa (b + k)) bs)) (TWK.upd Bw (o + k) bs).
Proof.
  intros m Bw o b n k bs HW Hin Hk Hkl.
  pose proof (tw_row TMAP_B o b n TMAP_B_ok Hin) as (Ho & Hn & HoW & Hb & Hb64).
  apply (tw_upd TMAP_B (csw_view m) (csw_view (write_to_mem m (wa (b + k)) bs)) Bw o b n k bs
           TMAP_B_ok HW Hin Hk Hkl).
  - intros j Hj.
    destruct (bytes_at_write_same rsegs m (b + k) bs ltac:(lia) ltac:(lia)) as (_ & _ & HB).
    unfold csw_view. rewrite (HB j Hj).
    replace (nth_error bs j) with (Some (nth j bs (Z_to_bv 8 0)))
      by (symmetry; apply nth_error_nth'; exact Hj).
    reflexivity.
  - intros x Hx Hnx.
    assert (Hr : 0 <= x < 2 ^ 64).
    { destruct Hx as (o' & b' & n' & Hin' & Hx').
      pose proof (tw_row TMAP_B o' b' n' TMAP_B_ok Hin') as (_ & _ & _ & Hb' & Hb64'). lia. }
    assert (E : write_to_mem m (wa (b + k)) bs (wa x) = m (wa x)).
    { rewrite (write_to_mem_spec bs m (b + k) (wa x)) by lia.
      rewrite (wa_unsigned x Hr).
      destruct (Z.leb_spec (b + k) x) as [H1|H1];
        destruct (Z.ltb_spec x (b + k + Z.of_nat (length bs))) as [H2|H2];
        cbn [andb]; try reflexivity.
      exfalso. apply Hnx. lia. }
    unfold csw_view, mrd. rewrite E. reflexivity.
Qed.

(* the 4-byte form: the machine stores le4 (Z_to_bv 64 v), the world takes put 4 v *)
Lemma cls_tw_wr4 : forall (m : word -> option byte) Bw o b n k (v : Z),
  tw_at TMAP_B (csw_view m) Bw -> In (o, b, n) TMAP_B -> 0 <= k -> k + 4 <= n ->
  tw_at TMAP_B (csw_view (write_to_mem m (wa (b + k)) (le4 (Z_to_bv 64 v)))) (TWK.upd Bw (o + k) (TWK.put 4 v)).
Proof.
  intros m Bw o b n k v HW Hin Hk Hkn.
  replace (le4 (Z_to_bv 64 v)) with (TWK.put 4 v) by (unfold TWK.put; apply Z_to_le_bytes_lit4).
  apply (cls_tw_wr m Bw o b n k (TWK.put 4 v) HW Hin Hk).
  rewrite TWLK.length_put. lia.
Qed.

(* a store that misses every payload keeps the world *)
Lemma cls_tw_out : forall (m : word -> option byte) Bw (a : Z) (bs : list byte),
  tw_at TMAP_B (csw_view m) Bw -> 0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  (a + Z.of_nat (length bs) <= TGK.G_HARNESS_B_LO \/ TGK.G_HARNESS_B_HI <= a) ->
  tw_at TMAP_B (csw_view (write_to_mem m (wa a) bs)) Bw.
Proof.
  intros m Bw a bs HW Ha Hl Hd.
  apply (tw_kept TMAP_B (csw_view m) _ Bw HW).
  intros x Hx.
  pose proof (TMAP_B_hull x Hx) as Hh.
  assert (Hr : 0 <= x < 2 ^ 64) by (unfold TGK.G_HARNESS_B_LO, TGK.G_HARNESS_B_HI in Hh; lia).
  assert (E : write_to_mem m (wa a) bs (wa x) = m (wa x)).
  { rewrite (write_to_mem_spec bs m a (wa x)) by lia.
    rewrite (wa_unsigned x Hr).
    destruct (Z.leb_spec a x) as [H1|H1];
      destruct (Z.ltb_spec x (a + Z.of_nat (length bs))) as [H2|H2];
      cbn [andb]; try reflexivity.
    exfalso. unfold TGK.G_HARNESS_B_LO, TGK.G_HARNESS_B_HI in Hh, Hd. lia. }
  unfold csw_view, mrd. rewrite E. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* the bytes the walk stores into                                      *)
(* ------------------------------------------------------------------ *)

(* g_cmd's payload [0x5e5080, + 40960), g_q's payload [0x5f1880, + 4096), g_nq [0x5df5e0, + 4) and the caller's
   int at dp: every byte the function stores lies here. *)
Definition cls_wrange (dp a : Z) : Prop :=
  (6180992 <= a < 6180992 + 40960) \/ (6232192 <= a < 6232192 + 4096) \/
  (6157792 <= a < 6157792 + 4) \/ (dp <= a < dp + 4).

Definition cls_wok (dp : Z) (m : word -> option byte) : Prop :=
  forall a, cls_wrange dp a -> wview rsegs m (wa a) <> None.

Lemma cls_wok_write : forall dp (m : word -> option byte) (a : word) (bs : list byte),
  cls_wok dp m -> cls_wok dp (write_to_mem m a bs).
Proof. intros dp m a bs H x Hx. apply wview_write_mono. exact (H x Hx). Qed.

Lemma cls_wok_store_ok : forall dp (m : word -> option byte) (a : Z) (n : nat),
  cls_wok dp m -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (forall i, 0 <= i < Z.of_nat n -> cls_wrange dp (a + i)) ->
  store_ok rsegs m (wa a) n = true.
Proof.
  intros dp m a n HW Ha Hn Hr.
  destruct n as [|n']; [reflexivity|].
  assert (Ha64 : 0 <= a < 2 ^ 64) by (pose proof (Nat2Z.is_nonneg n'); rewrite Nat2Z.inj_succ in Hn; lia).
  apply (store_ok_of_all rsegs (S n') m (wa a)).
  { rewrite (wa_unsigned a Ha64). exact Hn. }
  rewrite (wa_unsigned a Ha64).
  intros x Hx.
  pose proof (bv_unsigned_in_range 64 x) as Rx. unfold bv_modulus in Rx.
  change (2 ^ Z.of_N 64) with (2 ^ 64) in Rx.
  replace x with (wa (bv_unsigned x)) by (unfold wa; apply Z_to_bv_bv_unsigned).
  apply HW. replace (bv_unsigned x) with (a + (bv_unsigned x - a)) by lia.
  apply Hr. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* the shadow map                                                      *)
(* ------------------------------------------------------------------ *)

(* The check of a w-byte load at A + o reads the shadow byte of A + o and compares it with (A + o) mod 8 + (w - 1).
   The byte at A + o + min (w - 1) (7 - (A + o) mod 8) lies in the load and in the granule of A + o, so that
   shadow byte is either 0 or above (A + o) mod 8 + (w - 1). *)
Lemma cls_sh_load : forall (m : word -> option byte) (A n o w : Z),
  addressable m A n -> 0 <= o -> 0 < w -> o + w <= n ->
  exists k : byte,
    mrd rsegs m (wa ((A + o) / 8 + ASAN_K)) = Some k /\
    (bv_signed k = 0 \/ ((A + o) mod 8 + (w - 1) < bv_signed k /\ bv_signed k <= 7)).
Proof.
  intros m A n o w (HA & HN & HE & AB) Ho Hw Hon.
  pose proof (Z.mod_pos_bound (A + o) 8 ltac:(lia)) as MB.
  destruct (Z_le_dec ((A + o) mod 8 + (w - 1)) 7) as [LE|GT].
  - destruct (AB (o + (w - 1)) ltac:(lia)) as (APP & k & MK & SK).
    exists k. unfold shadow_addr in MK. unfold shadow_ok in SK.
    assert (D : (A + (o + (w - 1))) / 8 = (A + o) / 8) by (Z.div_mod_to_equations; lia).
    assert (E : (A + (o + (w - 1))) mod 8 = (A + o) mod 8 + (w - 1)) by (Z.div_mod_to_equations; lia).
    rewrite D in MK. rewrite E in SK. split; [exact MK | exact SK].
  - destruct (AB (o + (7 - (A + o) mod 8)) ltac:(lia)) as (APP & k & MK & SK).
    exists k. unfold shadow_addr in MK. unfold shadow_ok in SK.
    assert (D : (A + (o + (7 - (A + o) mod 8))) / 8 = (A + o) / 8) by (Z.div_mod_to_equations; lia).
    assert (E : (A + (o + (7 - (A + o) mod 8))) mod 8 = 7) by (Z.div_mod_to_equations; lia).
    rewrite D in MK. rewrite E in SK. split; [exact MK|].
    left. destruct SK as [K0|K]; [exact K0 | lia].
Qed.

(* the shadow byte of g_q + o lies in the shadow range of g_q's payload (base 8-aligned, length a multiple of 8) *)
Lemma cls_shq : forall RNG o, ExecF.rng RNG 2148229904 512 -> 0 <= o < 4096 ->
  ExecF.rng RNG ((6232192 + o) / 8 + ASAN_K) 1.
Proof.
  intros RNG o H Ho. apply (rng_sub' RNG 2148229904 512); [exact H|].
  unfold ASAN_K. Z.div_mod_to_equations. lia.
Qed.

(* the same for g_cmd's payload *)
Lemma cls_shc : forall RNG o, ExecF.rng RNG 2148223504 5120 -> 0 <= o < 40960 ->
  ExecF.rng RNG ((6180992 + o) / 8 + ASAN_K) 1.
Proof.
  intros RNG o H Ho. apply (rng_sub' RNG 2148223504 5120); [exact H|].
  unfold ASAN_K. Z.div_mod_to_equations. lia.
Qed.

(* a shadow address of application memory is never application memory *)
Lemma cls_shadow_not_app : forall x, app_mem x -> ~ app_mem (shadow_addr x).
Proof.
  intros x Hx Hs. unfold app_mem, shadow_addr, ASAN_K, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *.
  destruct Hx as [Hx|Hx]; destruct Hs as [Hs|Hs]; Z.div_mod_to_equations; lia.
Qed.

(* a store into application memory keeps every shadow byte, so it keeps `addressable` *)
Lemma cls_addr_store : forall (m : word -> option byte) p n (a : Z) (bs : list byte),
  addressable m p n -> 0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> app_mem (a + i)) ->
  addressable (write_to_mem m (wa a) bs) p n.
Proof.
  intros m p n a bs (HP & HN & HE & AB) Ha Hl Happ.
  split; [exact HP|]. split; [exact HN|]. split; [exact HE|].
  intros i Hi. destruct (AB i Hi) as (APP & k & MK & SK).
  split; [exact APP|]. exists k. split; [|exact SK].
  pose proof (cls_shadow_not_app (p + i) APP) as HNA.
  assert (Hr : 0 <= shadow_addr (p + i) < 2 ^ 64).
  { unfold app_mem, shadow_addr, ASAN_K, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in APP |- *.
    destruct APP as [H1|H1]; Z.div_mod_to_equations; lia. }
  assert (E : write_to_mem m (wa a) bs (wa (shadow_addr (p + i))) = m (wa (shadow_addr (p + i)))).
  { rewrite (write_to_mem_spec bs m a (wa (shadow_addr (p + i)))) by lia.
    rewrite (wa_unsigned (shadow_addr (p + i)) Hr).
    destruct (Z.leb_spec a (shadow_addr (p + i))) as [H1|H1];
      destruct (Z.ltb_spec (shadow_addr (p + i)) (a + Z.of_nat (length bs))) as [H2|H2];
      cbn [andb]; try reflexivity.
    exfalso. apply HNA.
    replace (shadow_addr (p + i)) with (a + (shadow_addr (p + i) - a)) by lia.
    apply Happ. lia. }
  unfold mrd. rewrite E. exact MK.
Qed.

(* every byte of the three harness ranges the walk stores into, and of the caller's int at dp, is application
   memory: the three ranges lie in low memory, dp where its own placement puts it. *)
Lemma cls_wrange_app : forall dp a,
  (0 <= dp /\ dp + 4 <= LOWMEM_END) \/ (HIGHMEM_BEG <= dp /\ dp + 4 <= APPMEM_END) ->
  cls_wrange dp a -> app_mem a.
Proof.
  intros dp a Hd [H|[H|[H|H]]]; unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *;
    try (left; lia).
  destruct Hd as [Hd|Hd]; [left; lia | right; lia].
Qed.

(* ------------------------------------------------------------------ *)
(* the machine words of the comparisons                                *)
(* ------------------------------------------------------------------ *)

Lemma cls_shr3 : forall z, Z.shiftr z 3 = z / 8.
Proof. intros z. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.

Lemma cls_eqb_lit : forall x y, -2^63 <= x < 2^63 -> -2^63 <= y < 2^63 ->
  bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof.
  intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit_wrap.
  destruct (Z.eqb_spec x y) as [->|N]; [apply Z.eqb_refl|].
  apply Z.eqb_neq. intros E.
  assert (E2 : (x - y) mod 2^64 = 0) by (rewrite Zminus_mod, E, Z.sub_diag; reflexivity).
  apply Z.mod_divide in E2; [|lia]. destruct E2 as [c Ec]. nia.
Qed.

Lemma cls_eqb0 : forall v, -2^63 <= v < 2^63 -> bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 0) = (v =? 0).
Proof. intros v Hv. apply cls_eqb_lit; lia. Qed.

Lemma cls_ltu_lit : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 ->
  bv_ltu (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof. intros a b Ha Hb. unfold bv_ltu. rewrite !unsigned_lit by assumption. reflexivity. Qed.

Lemma cls_lts_lit : forall (x : Z) (k : byte), -2^63 <= x < 2^63 ->
  bv_lts (Z_to_bv 64 x) (sxb k) = (x <? bv_signed k).
Proof.
  intros x k Hx. unfold bv_lts, sxb. pose proof (byte_signed_range k).
  rewrite !signed_lit by lia. reflexivity.
Qed.

Lemma cls_wrap64_1 : bv_wrap 64 1 = 1.
Proof. reflexivity. Qed.
Lemma cls_wrap64_7 : bv_wrap 64 7 = 7.
Proof. reflexivity. Qed.

(* ---- the signed / unsigned readings of a 32-bit world field ---- *)

Lemma cls_s32_mod : forall B k, TWK.s32_at B k mod 2^32 = TWK.u_at B k 4.
Proof.
  intros B k. pose proof (TWLK.u_at_range B k 4) as R. change (8 * Z.of_nat 4) with 32 in R.
  unfold TWK.s32_at, bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2^31).
  change (bv_modulus 32) with (2^32). Z.div_mod_to_equations. lia.
Qed.

Lemma cls_s32_small : forall B k, TWK.u_at B k 4 < 2^31 -> TWK.s32_at B k = TWK.u_at B k 4.
Proof.
  intros B k H. pose proof (TWLK.u_at_range B k 4) as R. change (8 * Z.of_nat 4) with 32 in R.
  unfold TWK.s32_at, bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2^31).
  change (bv_modulus 32) with (2^32). rewrite Z.mod_small by lia. lia.
Qed.

Lemma cls_s32_eqb : forall B k v, 0 <= v < 2^31 -> (TWK.s32_at B k =? v) = (TWK.u_at B k 4 =? v).
Proof.
  intros B k v Hv. pose proof (TWLK.u_at_range B k 4) as R. change (8 * Z.of_nat 4) with 32 in R.
  destruct (Z.eqb_spec (TWK.u_at B k 4) v) as [E|E].
  - rewrite cls_s32_small by lia. rewrite E. apply Z.eqb_refl.
  - apply Z.eqb_neq. intros C. apply E. rewrite <- cls_s32_mod, C. apply Z.mod_small. lia.
Qed.

Lemma cls_ltu_s32 : forall B k v, 0 <= v < 2^31 -> v < TWK.u_at B k 4 ->
  bv_ltu (Z_to_bv 64 v) (Z_to_bv 64 (TWK.s32_at B k)) = true.
Proof.
  intros B k v Hv Hlt. pose proof (TWLK.u_at_range B k 4) as R. change (8 * Z.of_nat 4) with 32 in R.
  unfold bv_ltu. rewrite !unsigned_lit_wrap. rewrite (Z.mod_small v) by lia. apply Z.ltb_lt.
  destruct (Z_lt_le_dec (TWK.u_at B k 4) (2^31)) as [L|L].
  - rewrite cls_s32_small by lia. rewrite Z.mod_small by lia. lia.
  - assert (S32 : TWK.s32_at B k = TWK.u_at B k 4 - 2^32).
    { unfold TWK.s32_at, bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2^31).
      change (bv_modulus 32) with (2^32). Z.div_mod_to_equations. lia. }
    rewrite S32. rewrite <- (Z.mod_add (TWK.u_at B k 4 - 2^32) 1 (2^64)) by lia.
    rewrite Z.mod_small by lia. lia.
Qed.

Lemma cls_mod64_32 : forall z, (z mod 2^64) mod 2^32 = z mod 2^32.
Proof.
  intros z. rewrite (Z.mod_eq z (2^64)) by lia.
  replace (z - 2^64 * (z / 2^64)) with (z + (- (2^32 * (z / 2^64))) * 2^32) by lia.
  apply Z.mod_add. lia.
Qed.

Lemma cls_le4_mod : forall x y, x mod 2^32 = y mod 2^32 -> le4 (Z_to_bv 64 x) = le4 (Z_to_bv 64 y).
Proof.
  intros x y H. unfold le4. rewrite !unsigned_lit_wrap.
  rewrite <- (Z_to_le_bytes_mod 4 (x mod 2^64) 32) by (cbn; lia).
  rewrite <- (Z_to_le_bytes_mod 4 (y mod 2^64) 32) by (cbn; lia).
  rewrite !cls_mod64_32, H. reflexivity.
Qed.

Lemma cls_put_s32 : forall B k, TWK.put 4 (TWK.s32_at B k) = TWK.put 4 (TWK.u_at B k 4).
Proof.
  intros B k. pose proof (TWLK.u_at_range B k 4) as R. change (8 * Z.of_nat 4) with 32 in R.
  unfold TWK.put. rewrite <- (Z_to_le_bytes_mod 4 (TWK.s32_at B k) 32) by (cbn; lia).
  rewrite <- (Z_to_le_bytes_mod 4 (TWK.u_at B k 4) 32) by (cbn; lia).
  rewrite cls_s32_mod, (Z.mod_small (TWK.u_at B k 4)) by lia. reflexivity.
Qed.

Lemma cls_lor_mod : forall a b c d, a mod 2^32 = b mod 2^32 -> c mod 2^32 = d mod 2^32 ->
  Z.lor a c mod 2^32 = Z.lor b d mod 2^32.
Proof.
  intros a b c d H1 H2. rewrite <- !(Z.land_ones _ 32) by lia. rewrite !Z.land_lor_distr_l.
  rewrite !(Z.land_ones _ 32) by lia. rewrite H1, H2. reflexivity.
Qed.

Lemma cls_swrap_mod : forall d, bv_swrap 32 d mod 2^32 = d mod 2^32.
Proof.
  intros d. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32).
  rewrite Zminus_mod, Zmod_mod, <- Zminus_mod. f_equal. lia.
Qed.

(* the display word the machine stores back has the model's low 32 bits *)
Lemma cls_disp_le4 : forall d cd,
  le4 (Z_to_bv 64 (Z.lor (bv_unsigned (sx32 (Z_to_bv 64 d))) (bv_unsigned (Z_to_bv 64 cd))))
  = le4 (Z_to_bv 64 (Z.lor d cd)).
Proof.
  intros d cd. apply cls_le4_mod. unfold sx32. rewrite !unsigned_lit_wrap.
  apply cls_lor_mod.
  - rewrite cls_mod64_32, cls_swrap_mod. apply cls_mod64_32.
  - apply cls_mod64_32.
Qed.

Lemma cls_shl32_shr30 : forall k, 0 <= k < 2^32 ->
  Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 k)) 32))) 30 = 4 * k.
Proof.
  intros k Hk. rewrite (unsigned_lit k) by lia. rewrite Z.shiftl_mul_pow2 by lia.
  rewrite unsigned_lit by nia. rewrite Z.shiftr_div_pow2 by lia.
  replace (k * 2^32) with (4 * k * 2^30) by lia. apply Z.div_mul. lia.
Qed.

Lemma cls_addiw : forall k, 0 <= k < 2^30 ->
  Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 k) + 1)) = Z_to_bv 64 (k + 1).
Proof.
  intros k Hk. rewrite unsigned_lit by lia. f_equal.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32).
  rewrite Z.mod_small by lia. lia.
Qed.

(* ---- list bridges ---- *)

Lemma cls_firstn1 : forall (l : list byte) n,
  firstn 1 (skipn n l) = match nth_error l n with Some x => [x] | None => [] end.
Proof.
  intros l n. revert l. induction n as [|n IH]; intros [|x l]; cbn; try reflexivity. apply IH.
Qed.

Lemma cls_at8_ne : forall (l : list byte) n,
  DSK.at8 l n = match nth_error l n with Some x => bv_unsigned x | None => 0 end.
Proof.
  intros l n. revert l. unfold DSK.at8, DSK.bz.
  induction n as [|n IH]; intros [|x l]; cbn; try reflexivity. apply IH.
Qed.

Lemma cls_beq : forall l r, TCK.beq_bytes l r = true -> l = r.
Proof.
  intros l r H. unfold TCK.beq_bytes in H.
  destruct (list_eq_dec Z.eq_dec (TWK.zs l) (TWK.zs r)) as [E|E]; [|discriminate].
  clear H. unfold TWK.zs in E. revert r E. induction l as [|a l IH]; intros [|b r] E; cbn in E; try discriminate.
  - reflexivity.
  - injection E as E1 E2. f_equal; [apply bv_eq; exact E1 | apply IH; exact E2].
Qed.
