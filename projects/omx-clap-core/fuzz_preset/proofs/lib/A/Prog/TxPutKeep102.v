(* fuzz_preset, harness fix #102 (pins A' asan 1be0f53d96cb9d6c, B' asan-ubsan d663f82d7f488d30): the IMAGE-FREE KEEP
   LEMMAS of the tx_put walks, shared by the A' and B' walks (lanes TxPutA102 / TxPutB102 of h-rw-pre-7). Owner of
   this file: TxPutB102; the A' lane takes it BY PATH.
   K0 text served: ttx_put_specX, lib/A/PRH_FnTx.v blob b6f264e13647 (cold/h-hpreset-7-walkkit-next eee71ebe8d49),
   over its predicates prhtx_inv / prhtx_place / prhtx_trace and PRH_Base.v's src_rd / bytes_at / prh_ledger /
   prh_own / arodata_okP.
   rule 24: proves no function (kind: shared lemmas)

   WHAT IS HERE. Each lemma carries one tx_put predicate from (W, mem) to (W', mem') under the keep hypotheses below,
   each lemma taking only the ones it reads:
   - tpk_alo (KA-lo): the view below YM05.alloc_ceiling is unchanged;
   - tpk_mlo (KM-lo): its mrestrict twin at the word level (writable_at reads the restricted memory through wview,
     not the view, so only prhtx_inv and the record's writability need it; tpk_alo_of_mlo derives KA-lo from it);
   - tpk_ahi lo t (KA-hi): the view on [lo, 2 ^ 64) outside the record's 28 bytes [t, t + 28) is unchanged, with its
     twin tpk_mhi and tpk_ahi_of_mhi.
   THE WORLD (Wl). Every predicate here reads W only through w_H W (aview segs (w_H W) mem and
   mrestrict (w_H W) mem), and each keep hypothesis is stated between (w_H W, mem) and (w_H W', mem'). So every
   lemma is W'-GENERAL and NONE needs wle W W' or W' = W. wle W W' (YA0n.v:23, hsub (w_H W') (w_H W)) only GROWS the
   view (YG0n.v aview_ext: rd_ext (aview segs H mem) (aview segs H' mem)), so it never gives a keep hypothesis by
   itself: a walk gets KA-lo / KM-lo / KA-hi from a frame fact (keep_bundle_frame, W' = W) or from a journal.
   WHERE THE BYTES LIE (why KA-lo reaches them): the buffer and its shadow (b + cap + 8 <= alloc_ceiling in
   prhtx_inv; a shadow address is SHADOW_OFF + x / 8, below the ceiling for x < 2 ^ 47: tpk_shadow_lo, tpk_hull_lo);
   a src_rd window likewise; the record's shadow (t + 28 <= 2 ^ 47, which fwin's spZ regs + dw <= ly_top ly and
   astk_ok's ly_top ly <= ly_stk_hi ly <= 2 ^ 47 give); the read-only image bytes and the alloc.c statics (in_img,
   below kLowMemEnd by PAImg's pa_segs_low; a static's in_img is the walk's PST_ok, YCbqG.v Section l); the harness
   heads (tpk_heads_lo: from ARx's blocks law and prh_head_wide).
   THE REFUSED ARM (second cut, added for h-cmd-b1 / h-rw-ide-2): tx_put's NULL arm stores ONE byte to
   g_own_ran_out, a prh_pst cell in the image below the ceiling, so KA-lo / KM-lo fail across it. The *_pst variants
   (tpk_alo_pst r / tpk_mlo_pst r: off ONE region r, an entry of prh_pst) keep every predicate but prh_own, whose
   cell IS r (no keep). keep_prhtx_trace reads nothing below the ceiling, so it serves the NULL arm unchanged through
   keep_bundle_frame_pst's KA-hi.
   No address, no image constant. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG YP0b YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG0dcf YGcfRoomLive.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger TxModel.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnTx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos PresetLiveBounds PresetRun PresetReqAt.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ---- pure facts ---- *)

Lemma tpk_word_small : forall a, 0 <= a < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 a) = a.
Proof.
intros a Ha.
assert (E : bv_unsigned (Z_to_bv 64 a) = a mod 2 ^ 64) by (rewrite Z_to_bv_unsigned; reflexivity).
rewrite E. apply Z.mod_small. exact Ha.
Qed.

(* the shadow byte of an address below 2 ^ 47 is below the ceiling *)
Lemma tpk_shadow_lo {rc : YM05.RunCeil} : forall x, 0 <= x < 2 ^ 47 ->
  0 <= shadow_of_addr SHADOW_OFF x < YM05.alloc_ceiling.
Proof.
intros x Hx. pose proof YM05.alloc_ceiling_value as [C _]. unfold shadow_of_addr, SHADOW_OFF.
Z.div_mod_to_equations. lia.
Qed.

(* every byte of the shadow hull of [x, x + n) is below the ceiling when x + n <= 2 ^ 47 *)
Lemma tpk_hull_lo {rc : YM05.RunCeil} : forall x n s, 0 <= x -> 0 <= n -> x + n <= 2 ^ 47 ->
  shadow_addr x / 8 * 8 <= s < shadow_addr (x + n - 1) / 8 * 8 + 8 -> 0 <= s < YM05.alloc_ceiling.
Proof.
intros x n s H0 Hn Hx Hs. pose proof YM05.alloc_ceiling_value as [C _]. unfold shadow_addr, SHADOW_OFF in Hs.
Z.div_mod_to_equations. lia.
Qed.

(* the shadow facts of a reader carry to a reader that agrees on the shadow bytes they read *)
Lemma tpk_ra_keep : forall (rd rd' : reader) a n,
  (forall x, a <= x < a + n -> rd' (shadow_of_addr SHADOW_OFF x) = rd (shadow_of_addr SHADOW_OFF x)) ->
  range_addressable rd SHADOW_OFF a n -> range_addressable rd' SHADOW_OFF a n.
Proof. intros rd rd' a n Hk Hr x Hx. rewrite (Hk x Hx). exact (Hr x Hx). Qed.

Lemma tpk_hull_keep : forall (rd rd' : reader) x n,
  (forall s, shadow_addr x / 8 * 8 <= s < shadow_addr (x + n - 1) / 8 * 8 + 8 -> rd' s = rd s) ->
  shadow_hull_vis rd x n -> shadow_hull_vis rd' x n.
Proof. intros rd rd' x n Hk Hh s Hs. rewrite (Hk s Hs). exact (Hh s Hs). Qed.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PI : PrhImg}
  {RL : PrhRoomLive}.
Context {L : ptable asym} {PA : PAImg L}.
#[local] Abbreviation segs := pa_segs.
Variable B : asyms.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* ---- the keep hypotheses ---- *)
(* KA-lo: the view below the ceiling *)
Definition tpk_alo (W W' : world segs) (mem mem' : word -> option byte) : Prop :=
  forall a, 0 <= a < YM05.alloc_ceiling -> aview segs (w_H W') mem' a = aview segs (w_H W) mem a.
(* KM-lo: the restricted memory below the ceiling, at the word level *)
Definition tpk_mlo (W W' : world segs) (mem mem' : word -> option byte) : Prop :=
  forall x : word, bv_unsigned x < YM05.alloc_ceiling -> mrestrict (w_H W') mem' x = mrestrict (w_H W) mem x.
(* KA-hi: the view on [lo, 2 ^ 64) outside the record's 28 bytes at t *)
Definition tpk_ahi (lo t : Z) (W W' : world segs) (mem mem' : word -> option byte) : Prop :=
  forall a, lo <= a < 2 ^ 64 -> ~ (t <= a < t + 28) -> aview segs (w_H W') mem' a = aview segs (w_H W) mem a.
(* KM-hi: its mrestrict twin *)
Definition tpk_mhi (lo t : Z) (W W' : world segs) (mem mem' : word -> option byte) : Prop :=
  forall x : word, lo <= bv_unsigned x -> ~ (t <= bv_unsigned x < t + 28) ->
    mrestrict (w_H W') mem' x = mrestrict (w_H W) mem x.

(* ---- bytes: restricted memory -> view / mbyte / writable_at; view -> bytes_at ---- *)
Lemma tpk_aview_of_m : forall (H H' : word -> bool) (mem mem' : word -> option byte) a,
  mrestrict H' mem' (Z_to_bv 64 a) = mrestrict H mem (Z_to_bv 64 a) -> aview segs H' mem' a = aview segs H mem a.
Proof. intros H H' mem mem' a E. unfold aview, mbyte. rewrite E. reflexivity. Qed.

Lemma tpk_writable_of_m : forall (m m' : word -> option byte) a,
  m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) -> writable_at segs m a -> writable_at segs m' a.
Proof. intros m m' a E Hw. unfold writable_at, wview in *. rewrite E. exact Hw. Qed.

Lemma tpk_alo_of_mlo : forall W W' mem mem', tpk_mlo W W' mem mem' -> tpk_alo W W' mem mem'.
Proof.
intros W W' mem mem' KM a Ha. pose proof YM05.alloc_ceiling_lt as CL. apply tpk_aview_of_m. apply KM.
rewrite tpk_word_small by lia. lia.
Qed.

Lemma tpk_ahi_of_mhi : forall lo t W W' mem mem', 0 <= lo -> tpk_mhi lo t W W' mem mem' -> tpk_ahi lo t W W' mem mem'.
Proof.
intros lo t W W' mem mem' Hlo KM a Ha Hn. apply tpk_aview_of_m.
apply KM; rewrite tpk_word_small by lia; [lia | exact Hn].
Qed.

(* the word-level keep gives writable_at below the ceiling *)
Lemma tpk_writable_lo : forall W W' mem mem' a, tpk_mlo W W' mem mem' -> 0 <= a < YM05.alloc_ceiling ->
  writable_at segs (rdW W mem) a -> writable_at segs (rdW W' mem') a.
Proof.
intros W W' mem mem' a KM Ha Hw. pose proof YM05.alloc_ceiling_lt as CL.
apply (tpk_writable_of_m (rdW W mem)); [|exact Hw]. apply KM. rewrite tpk_word_small by lia. lia.
Qed.

(* bytes_at on a window whose view is unchanged (the core of keep_bytes_at / keep_src_rd / keep_prhtx_inv) *)
Lemma tpk_bytes_at_rng : forall (W W' : world segs) mem mem' p l,
  (forall a, p <= a < p + Z.of_nat (length l) -> aview segs (w_H W') mem' a = aview segs (w_H W) mem a) ->
  bytes_at W mem p l -> bytes_at W' mem' p l.
Proof.
intros W W' mem mem' p l Hk Hb. unfold bytes_at, garr8 in *. intros j Hj.
destruct (Hb j Hj) as [Hv Hr]. split; [|exact Hr].
apply (prh_val_mem_keep _ _ _ _ _ Hv). intros k Hk1. apply prh_mbyte_of_aview. apply Hk. lia.
Qed.

(* ---- 1. the buffer ---- *)
Lemma keep_prhtx_inv : forall Lam ly S W W' mem mem' b len cap txt,
  prhtx_inv B Lam ly S W mem b len cap txt -> tpk_alo W W' mem mem' -> tpk_mlo W W' mem mem' ->
  prhtx_inv B Lam ly S W' mem' b len cap txt.
Proof.
intros Lam ly S W W' mem mem' b len cap txt (Hl & Hc) KA KM. split; [exact Hl|].
destruct Hc as [Hz | (Hcap & Hlt & Hin & Hby & H4 & Hce & Ham & Hwr & Hra & Hhu & Hlam)]; [left; exact Hz | right].
pose proof YM05.alloc_ceiling_lt as CL.
assert (Hlen : Z.of_nat (length (txt ++ [0])) = len + 1) by (rewrite length_app; cbn [length]; lia).
split; [exact Hcap|]. split; [exact Hlt|]. split; [exact Hin|].
split; [apply (tpk_bytes_at_rng W W' mem mem'); [intros a Ha; apply KA; lia | exact Hby]|].
split; [exact H4|]. split; [exact Hce|]. split; [exact Ham|].
split; [intros a Ha; apply (tpk_writable_lo W W' mem mem' a KM); [lia | exact (Hwr a Ha)]|].
split; [apply (tpk_ra_keep (aview segs (w_H W) mem)); [|exact Hra]; intros x Hx; apply KA; apply tpk_shadow_lo; lia|].
split; [apply (tpk_hull_keep (aview segs (w_H W) mem)); [|exact Hhu]; intros s Hs; apply KA;
  exact (tpk_hull_lo b cap s ltac:(lia) ltac:(lia) ltac:(lia) Hs)|].
exact Hlam.
Qed.

(* ---- 2. a source window, a byte window ---- *)
Lemma keep_src_rd : forall W W' mem mem' p l,
  src_rd W mem p l -> tpk_alo W W' mem mem' -> src_rd W' mem' p l.
Proof.
intros W W' mem mem' p l (Hb & H4 & Hce & Ham & Hra & Hhu) KA. pose proof YM05.alloc_ceiling_lt as CL.
split; [apply (tpk_bytes_at_rng W W' mem mem'); [intros a Ha; apply KA; lia | exact Hb]|].
split; [exact H4|]. split; [exact Hce|]. split; [exact Ham|].
split; [apply (tpk_ra_keep (aview segs (w_H W) mem)); [|exact Hra]; intros x Hx; apply KA; apply tpk_shadow_lo; lia|].
intros Hn. apply (tpk_hull_keep (aview segs (w_H W) mem)); [|exact (Hhu Hn)]. intros s Hs. apply KA.
exact (tpk_hull_lo p (Z.of_nat (length l)) s ltac:(lia) ltac:(lia) ltac:(lia) Hs).
Qed.

Lemma keep_bytes_at : forall W W' mem mem' p l,
  bytes_at W mem p l -> 0 <= p -> p + Z.of_nat (length l) <= YM05.alloc_ceiling -> tpk_alo W W' mem mem' ->
  bytes_at W' mem' p l.
Proof.
intros W W' mem mem' p l Hb H0 Hce KA. apply (tpk_bytes_at_rng W W' mem mem'); [|exact Hb].
intros a Ha. apply KA. lia.
Qed.

(* ---- 3. the ledger and g_own_ran_out ---- *)
(* the alloc.c statics (prh_pst) lie in the image, hence below kLowMemEnd and the ceiling (PAImg's pa_segs_low) *)
Lemma tpk_pst_lo : forall a, (forall a, Exists (in_zr a) prh_pst -> in_img segs a) ->
  Exists (in_zr a) prh_pst -> 0 <= a < YM05.alloc_ceiling.
Proof.
intros a HP Ha. pose proof (pa_segs_low a (HP a Ha)) as Hl. pose proof YM05.alloc_ceiling_value as [C _].
unfold kLowMemEnd in Hl. lia.
Qed.

(* the harness heads lie below the ceiling: from the allocator's blocks law (ARx_blocks_law's bound) and a head at
   least 8 bytes wide (prh_head_wide) *)
Lemma tpk_heads_lo : forall ly S Hp W mem Lam peak cnt fail ran most own,
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own -> prh_head_wide ->
  (forall p n, In (p, n) (ablocks B ly S) -> 4096 <= p /\ p + req_size n <= YM05.alloc_ceiling) ->
  forall a k, In (a, k) Lam -> 0 <= a - cf_head /\ a - cf_head + 8 <= YM05.alloc_ceiling.
Proof.
intros ly S Hp W mem Lam peak cnt fail ran most own HL HW HB a k Hin.
destruct (prh_ledger_hblock B ly S Hp W mem Lam peak cnt fail ran a k most own HL Hin) as (Hk & Hab & _).
destruct (HB _ _ Hab) as [H1 H2]. unfold prh_head_wide in HW.
assert (k + cf_head <= req_size (k + cf_head)) by (unfold req_size; destruct (Z.eqb_spec (k + cf_head) 0); lia).
lia.
Qed.

(* the ledger at a new allocator state whose blocks keep Lam's and whose Hp is a permutation *)
Lemma keep_prh_ledger_st : forall ly S Hp W mem ly' S' Hp' W' mem' Lam peak cnt fail ran most own,
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own -> tpk_alo W W' mem mem' ->
  (forall a, Exists (in_zr a) prh_pst -> in_img segs a) ->
  (forall a k, In (a, k) Lam -> 0 <= a - cf_head /\ a - cf_head + 8 <= YM05.alloc_ceiling) ->
  (forall a k, In (a, k) Lam -> In (a - cf_head, k + cf_head) (ablocks B ly S) ->
     In (a - cf_head, k + cf_head) (ablocks B ly' S')) ->
  Permutation Hp' Hp ->
  prh_ledger B ly' S' Hp' W' mem' Lam peak cnt fail ran most own.
Proof.
intros ly S Hp W mem ly' S' Hp' W' mem' Lam peak cnt fail ran most own HL KA HP HH Hb Hpp.
apply (prh_ledger_kept_aview B ly S Hp W mem ly' S' Hp' W' mem' Lam peak cnt fail ran most own HL); [| | exact Hb | exact Hpp].
- intros a Ha. apply KA. exact (tpk_pst_lo a HP Ha).
- intros a k i Hin Hi. apply KA. pose proof (HH a k Hin). lia.
Qed.

Lemma keep_prh_ledger : forall ly S Hp W W' mem mem' Lam peak cnt fail ran most own,
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own -> tpk_alo W W' mem mem' ->
  (forall a, Exists (in_zr a) prh_pst -> in_img segs a) ->
  (forall a k, In (a, k) Lam -> 0 <= a - cf_head /\ a - cf_head + 8 <= YM05.alloc_ceiling) ->
  prh_ledger B ly S Hp W' mem' Lam peak cnt fail ran most own.
Proof.
intros ly S Hp W W' mem mem' Lam peak cnt fail ran most own HL KA HP HH.
exact (keep_prh_ledger_st ly S Hp W mem ly S Hp W' mem' Lam peak cnt fail ran most own HL KA HP HH
  (fun _ _ _ H => H) (Permutation_refl Hp)).
Qed.

Lemma keep_prh_own : forall W W' mem mem' own,
  prh_own W mem own -> tpk_alo W W' mem mem' -> (forall a, Exists (in_zr a) prh_pst -> in_img segs a) ->
  prh_own W' mem' own.
Proof.
intros W W' mem mem' own [Hv Ho] KA HP. split; [|exact Ho].
apply (prh_val_mem_keep _ _ _ _ _ Hv). intros k Hk. apply prh_mbyte_of_aview. apply KA. apply (tpk_pst_lo _ HP).
unfold prh_pst. do 6 apply Exists_cons_tl. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
Qed.

(* g_most (prh_most of d7c502629be9; prh_pst's 6th cell) is kept below the ceiling *)
Lemma keep_prh_most : forall W W' mem mem' m,
  prh_most W mem m -> tpk_alo W W' mem mem' -> (forall a, Exists (in_zr a) prh_pst -> in_img segs a) ->
  prh_most W' mem' m.
Proof.
intros W W' mem mem' m [Hv Hm] KA HP. split; [|exact Hm].
apply (prh_val_mem_keep _ _ _ _ _ Hv). intros k Hk. apply prh_mbyte_of_aview. apply KA. apply (tpk_pst_lo _ HP).
unfold prh_pst. do 5 apply Exists_cons_tl. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
Qed.

(* ---- 4. the read-only image bytes (fpre's second conjunct) ---- *)
Lemma keep_arodata_okP : forall W W' mem mem',
  arodata_okP segs pa_relro_lo pa_relro_hi B (aview segs (w_H W) mem) -> tpk_alo W W' mem mem' ->
  arodata_okP segs pa_relro_lo pa_relro_hi B (aview segs (w_H W') mem').
Proof.
intros W W' mem mem' Hro KA. unfold PresetRodata.arodata_okP in *. intros a Ha Ho He.
assert (Hi : in_img segs a).
{ destruct Ha as [(sg & Hs & _ & Hr) | Hr]; [exists sg; split; [exact Hs | exact Hr] | exact (pa_relro_img a Hr)]. }
pose proof (pa_segs_low a Hi) as Hl. pose proof YM05.alloc_ceiling_value as [C _]. unfold kLowMemEnd in Hl.
rewrite KA by lia. exact (Hro a Ha Ho He).
Qed.

(* ---- 5. where the record lies: its 28 bytes writable at mem' (the walk's fact), its shadow below the ceiling ---- *)
Lemma keep_prhtx_place : forall ly S W W' regs mem mem' dw t,
  prhtx_place ly S W regs mem dw t -> t + 28 <= 2 ^ 47 ->
  (forall a, t <= a < t + 28 -> writable_at segs (rdW W' mem') a) ->
  tpk_alo W W' mem mem' -> prhtx_place ly S W' regs mem' dw t.
Proof.
intros ly S W W' regs mem mem' dw t (Hal & Hlo & Hhi & _ & Hra) Ht Hw KA.
pose proof (bv_unsigned_in_range 64 (getr regs 2)) as [R _]. fold (spZ regs) in R.
split; [exact Hal|]. split; [exact Hlo|]. split; [exact Hhi|]. split; [exact Hw|].
apply (tpk_ra_keep (aview segs (w_H W) mem)); [|exact Hra]. intros x Hx. apply KA. apply tpk_shadow_lo. lia.
Qed.

(* ---- 6. the realloc trace: the region [t - 16, ly_top ly) outside the record is kept, the record present ---- *)
Lemma keep_prhtx_trace : forall lo ly W W' mem mem' t,
  prhtx_trace B ly W mem t -> tpk_ahi lo t W W' mem mem' -> lo <= t - 16 -> ly_top ly <= 2 ^ 64 ->
  (forall a, t <= a < t + 28 -> aview segs (w_H W') mem' a <> None) ->
  prhtx_trace B ly W' mem' t.
Proof.
intros lo ly W W' mem mem' t Htr KH Hlo Htop Hrec Hc.
destruct (Htr Hc) as [Hpres Hun]. split.
- intros a Ha. destruct (Z_lt_ge_dec a t) as [Hlt | Hge].
  + rewrite (KH a ltac:(lia) ltac:(lia)). exact (Hpres a Ha).
  + destruct (Z_lt_ge_dec a (t + 28)) as [Hlt2 | Hge2]; [exact (Hrec a ltac:(lia))|].
    rewrite (KH a ltac:(lia) ltac:(lia)). exact (Hpres a Ha).
- intros rd ch Hrd Hch. apply (Hun rd ch); [|exact Hch].
  intros a Ha Hn. rewrite (Hrd a Ha Hn). exact (KH a ltac:(lia) Hn).
Qed.

(* ---- 7. the walk's common case: no allocator call, only the frame [sp0 - STK, sp0) and the record written ---- *)
Lemma keep_bundle_frame : forall W mem mem' STK sp0 t,
  (forall x : word, ~ (sp0 - STK <= bv_unsigned x < sp0) -> ~ (t <= bv_unsigned x < t + 28) ->
     mrestrict (w_H W) mem' x = mrestrict (w_H W) mem x) ->
  0 <= STK -> YM05.alloc_ceiling <= sp0 - STK -> sp0 + 16 <= t ->
  tpk_mlo W W mem mem' /\ tpk_alo W W mem mem' /\ tpk_ahi sp0 t W W mem mem' /\ tpk_mhi sp0 t W W mem mem'.
Proof.
intros W mem mem' STK sp0 t Hf H0 Hce Ht.
assert (KM : tpk_mlo W W mem mem') by (intros x Hx; apply Hf; lia).
assert (KH : tpk_mhi sp0 t W W mem mem') by (intros x Hx Hn; apply Hf; [lia | exact Hn]).
pose proof YM05.alloc_ceiling_value as [C _].
split; [exact KM|]. split; [exact (tpk_alo_of_mlo _ _ _ _ KM)|].
split; [exact (tpk_ahi_of_mhi sp0 t W W mem mem' ltac:(lia) KH)|].
exact KH.
Qed.

(* ==== 8. OFF ONE PST REGION (the REFUSED arm's byte store to g_own_ran_out). r lies in the image (tpk_pst_entry_img
   for an entry of prh_pst). What keeps each predicate off r:
   - a shadow address is >= SHADOW_OFF = kLowMemEnd, above every image byte (pa_segs_low): tpk_shadow_not_img,
     tpk_hull_not_img;
   - a heap block, so the buffer and a harness head, holds no image byte (ARx_client_img_law): tpk_blocks_not_img,
     tpk_inv_blk_off_r, tpk_heads_off_r;
   - the five statics prh_glob reads (tpk_glob_cells) avoid r when the cells are disjoint, which the image instance
     decides by computation (tpk_cells_off_of_check; PrhImg states no disjointness, so it is a premise here);
   - a read-only byte is not in r when r is no read-only byte (tp_img's tpi_pst_rw);
   - a src_rd / bytes_at window avoids r by premise (its bytes are a harness block, a read-only global or a frame). ==== *)
Definition tpk_alo_pst (r : Z * Z) (W W' : world segs) (mem mem' : word -> option byte) : Prop :=
  forall a, 0 <= a < YM05.alloc_ceiling -> ~ in_zr a r -> aview segs (w_H W') mem' a = aview segs (w_H W) mem a.
Definition tpk_mlo_pst (r : Z * Z) (W W' : world segs) (mem mem' : word -> option byte) : Prop :=
  forall x : word, bv_unsigned x < YM05.alloc_ceiling -> ~ in_zr (bv_unsigned x) r ->
    mrestrict (w_H W') mem' x = mrestrict (w_H W) mem x.

Lemma tpk_alo_pst_of_mlo_pst : forall r W W' mem mem', tpk_mlo_pst r W W' mem mem' -> tpk_alo_pst r W W' mem mem'.
Proof.
intros r W W' mem mem' KM a Ha Hn. pose proof YM05.alloc_ceiling_lt as CL. apply tpk_aview_of_m.
apply KM; rewrite tpk_word_small by lia; [lia | exact Hn].
Qed.

Lemma tpk_alo_pst_of_alo : forall r W W' mem mem', tpk_alo W W' mem mem' -> tpk_alo_pst r W W' mem mem'.
Proof. intros r W W' mem mem' KA a Ha _. exact (KA a Ha). Qed.

Lemma tpk_mlo_pst_of_mlo : forall r W W' mem mem', tpk_mlo W W' mem mem' -> tpk_mlo_pst r W W' mem mem'.
Proof. intros r W W' mem mem' KM x Hx _. exact (KM x Hx). Qed.

(* g_own_ran_out's cell is an entry of prh_pst *)
Lemma tpk_own_cell_pst : In (pi_g_own_ran_out, Z.of_nat pi_gz_own_ran_out) prh_pst.
Proof. unfold prh_pst. do 6 right. left. reflexivity. Qed.

(* an entry of prh_pst lies in the image when every static does (the walk's PST_ok, tp_img's tpi_pst_img) *)
Lemma tpk_pst_entry_img : forall r, In r prh_pst -> (forall a, Exists (in_zr a) prh_pst -> in_img segs a) ->
  forall a, in_zr a r -> in_img segs a.
Proof. intros r Hr HP a Ha. apply HP. apply Exists_exists. exists r. split; [exact Hr | exact Ha]. Qed.

(* a byte that is no image byte is not in r *)
Lemma tpk_off_r_of_not_img : forall (r : Z * Z) a, (forall a, in_zr a r -> in_img segs a) -> ~ in_img segs a ->
  ~ in_zr a r.
Proof. intros r a RI Hn Ha. exact (Hn (RI a Ha)). Qed.

Lemma tpk_shadow_not_img : forall x, 0 <= x -> ~ in_img segs (shadow_of_addr SHADOW_OFF x).
Proof.
intros x Hx Hi. pose proof (pa_segs_low _ Hi) as Hl. unfold kLowMemEnd, shadow_of_addr, SHADOW_OFF in *.
pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma tpk_hull_not_img : forall x s, 0 <= x -> shadow_addr x / 8 * 8 <= s -> ~ in_img segs s.
Proof.
intros x s Hx Hs Hi. pose proof (pa_segs_low _ Hi) as Hl. unfold kLowMemEnd in Hl.
unfold shadow_addr, SHADOW_OFF in Hs. Z.div_mod_to_equations. lia.
Qed.

(* an allocator block holds no image byte (ARx's client-image law, YCbqG.v field alx_client_img) *)
Lemma tpk_blocks_not_img :
  forall (ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop)
    ly S Hp W mem md p n a,
  ARx_client_img_law segs B ARx -> ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> p <= a < p + req_size n ->
  ~ in_img segs a.
Proof.
intros ARx ly S Hp W mem md p n a HL HAR Hin Ha. refine (proj2 (HL ly S Hp W mem md a HAR _)).
left. exists p, n. split; [exact Hin | exact Ha].
Qed.

(* the buffer of prhtx_inv avoids r *)
Lemma tpk_inv_blk_off_r :
  forall (ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop)
    ly S Hp W mem md Lam W0 mem0 b len cap txt r,
  ARx_client_img_law segs B ARx -> ARx ly S Hp W mem md -> prhtx_inv B Lam ly S W0 mem0 b len cap txt ->
  (forall a, in_zr a r -> in_img segs a) -> forall a, b <= a < b + cap -> ~ in_zr a r.
Proof.
intros ARx ly S Hp W mem md Lam W0 mem0 b len cap txt r HL HAR (_ & Hc) RI a Ha.
apply (tpk_off_r_of_not_img r a RI).
destruct Hc as [(-> & _ & _) | (Hcap & _ & Hin & _)]; [lia|].
apply (tpk_blocks_not_img ARx ly S Hp W mem md b cap a HL HAR Hin).
unfold req_size. destruct (Z.eqb_spec cap 0); lia.
Qed.

(* the harness heads avoid r *)
Lemma tpk_heads_off_r :
  forall (ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop)
    ly S Hp0 W0 mem0 md Hp W mem Lam peak cnt fail ran most own r,
  ARx_client_img_law segs B ARx -> ARx ly S Hp0 W0 mem0 md ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own -> prh_head_wide ->
  (forall a, in_zr a r -> in_img segs a) ->
  forall a k i, In (a, k) Lam -> 0 <= i < 8 -> ~ in_zr (a - cf_head + i) r.
Proof.
intros ARx ly S Hp0 W0 mem0 md Hp W mem Lam peak cnt fail ran most own r HL HAR HLG HW RI a k i Hin Hi.
apply (tpk_off_r_of_not_img r _ RI).
destruct (prh_ledger_hblock B ly S Hp W mem Lam peak cnt fail ran a k most own HLG Hin) as (Hk & Hab & _).
apply (tpk_blocks_not_img ARx ly S Hp0 W0 mem0 md _ _ _ HL HAR Hab). unfold prh_head_wide in HW.
assert (k + cf_head <= req_size (k + cf_head)) by (unfold req_size; destruct (Z.eqb_spec (k + cf_head) 0); lia).
lia.
Qed.

(* the five statics prh_glob reads (prh_pst without g_most and g_own_ran_out) *)
Definition tpk_glob_cells : list (Z * Z) :=
  [(pi_g_live, Z.of_nat pi_gz_live); (pi_g_peak, Z.of_nat pi_gz_peak); (pi_g_count, Z.of_nat pi_gz_count);
   (pi_g_fail, Z.of_nat pi_gz_fail); (pi_g_ran_out, Z.of_nat pi_gz_ran_out)].

(* interval disjointness, decided: the image instance proves `forallb (fun c => tpk_zr_disj c r) cs = true` by
   computation on its generated cells *)
Definition tpk_zr_disj (c r : Z * Z) : bool := (fst c + snd c <=? fst r) || (fst r + snd r <=? fst c).

Lemma tpk_cells_off_of_check : forall (cs : list (Z * Z)) (r : Z * Z),
  forallb (fun c => tpk_zr_disj c r) cs = true -> forall a, Exists (in_zr a) cs -> ~ in_zr a r.
Proof.
intros cs r H a Ha Hr. apply Exists_exists in Ha as (c & Hc & Hac). rewrite forallb_forall in H.
specialize (H c Hc). unfold tpk_zr_disj in H. apply orb_true_iff in H. unfold in_zr in *.
destruct H as [H|H]; apply Z.leb_le in H; lia.
Qed.

Lemma keep_prhtx_inv_pst : forall r Lam ly S W W' mem mem' b len cap txt,
  prhtx_inv B Lam ly S W mem b len cap txt -> tpk_alo_pst r W W' mem mem' -> tpk_mlo_pst r W W' mem mem' ->
  (forall a, in_zr a r -> in_img segs a) -> (forall a, b <= a < b + cap -> ~ in_zr a r) ->
  prhtx_inv B Lam ly S W' mem' b len cap txt.
Proof.
intros r Lam ly S W W' mem mem' b len cap txt (Hl & Hc) KA KM RI Hoff. split; [exact Hl|].
destruct Hc as [Hz | (Hcap & Hlt & Hin & Hby & H4 & Hce & Ham & Hwr & Hra & Hhu & Hlam)]; [left; exact Hz | right].
pose proof YM05.alloc_ceiling_lt as CL.
assert (Hlen : Z.of_nat (length (txt ++ [0])) = len + 1) by (rewrite length_app; cbn [length]; lia).
split; [exact Hcap|]. split; [exact Hlt|]. split; [exact Hin|].
split; [apply (tpk_bytes_at_rng W W' mem mem'); [intros a Ha; apply KA; [lia | apply Hoff; lia] | exact Hby]|].
split; [exact H4|]. split; [exact Hce|]. split; [exact Ham|].
split; [intros a Ha; apply (tpk_writable_of_m (rdW W mem)); [|exact (Hwr a Ha)];
  apply KM; rewrite tpk_word_small by lia; [lia | apply Hoff; lia]|].
split; [apply (tpk_ra_keep (aview segs (w_H W) mem)); [|exact Hra]; intros x Hx; apply KA;
  [apply tpk_shadow_lo; lia | apply (tpk_off_r_of_not_img r _ RI); apply tpk_shadow_not_img; lia]|].
split; [apply (tpk_hull_keep (aview segs (w_H W) mem)); [|exact Hhu]; intros s Hs; apply KA;
  [exact (tpk_hull_lo b cap s ltac:(lia) ltac:(lia) ltac:(lia) Hs) |
   apply (tpk_off_r_of_not_img r _ RI); exact (tpk_hull_not_img b s ltac:(lia) (proj1 Hs))]|].
exact Hlam.
Qed.

Lemma keep_src_rd_pst : forall r W W' mem mem' p l,
  src_rd W mem p l -> tpk_alo_pst r W W' mem mem' -> (forall a, in_zr a r -> in_img segs a) ->
  (forall a, p <= a < p + Z.of_nat (length l) -> ~ in_zr a r) -> src_rd W' mem' p l.
Proof.
intros r W W' mem mem' p l (Hb & H4 & Hce & Ham & Hra & Hhu) KA RI Hoff. pose proof YM05.alloc_ceiling_lt as CL.
split; [apply (tpk_bytes_at_rng W W' mem mem'); [intros a Ha; apply KA; [lia | apply Hoff; lia] | exact Hb]|].
split; [exact H4|]. split; [exact Hce|]. split; [exact Ham|].
split; [apply (tpk_ra_keep (aview segs (w_H W) mem)); [|exact Hra]; intros x Hx; apply KA;
  [apply tpk_shadow_lo; lia | apply (tpk_off_r_of_not_img r _ RI); apply tpk_shadow_not_img; lia]|].
intros Hn. apply (tpk_hull_keep (aview segs (w_H W) mem)); [|exact (Hhu Hn)]. intros s Hs. apply KA.
- exact (tpk_hull_lo p (Z.of_nat (length l)) s ltac:(lia) ltac:(lia) ltac:(lia) Hs).
- apply (tpk_off_r_of_not_img r _ RI). exact (tpk_hull_not_img p s ltac:(lia) (proj1 Hs)).
Qed.

Lemma keep_bytes_at_pst : forall r W W' mem mem' p l,
  bytes_at W mem p l -> 0 <= p -> p + Z.of_nat (length l) <= YM05.alloc_ceiling -> tpk_alo_pst r W W' mem mem' ->
  (forall a, p <= a < p + Z.of_nat (length l) -> ~ in_zr a r) -> bytes_at W' mem' p l.
Proof.
intros r W W' mem mem' p l Hb H0 Hce KA Hoff. apply (tpk_bytes_at_rng W W' mem mem'); [|exact Hb].
intros a Ha. apply KA; [lia | exact (Hoff a Ha)].
Qed.

(* g_most across a write of ONE other PST region r (the NULL arm's g_own_ran_out byte): kept when its cell avoids r *)
Lemma keep_prh_most_pst : forall r W W' mem mem' m,
  prh_most W mem m -> tpk_alo_pst r W W' mem mem' -> (forall a, Exists (in_zr a) prh_pst -> in_img segs a) ->
  (forall a, pi_g_most <= a < pi_g_most + Z.of_nat pi_gz_most -> ~ in_zr a r) ->
  prh_most W' mem' m.
Proof.
intros r W W' mem mem' m [Hv Hm] KA HP Hr. split; [|exact Hm].
apply (prh_val_mem_keep _ _ _ _ _ Hv). intros k Hk. apply prh_mbyte_of_aview. apply KA; [|apply Hr; lia].
apply (tpk_pst_lo _ HP).
unfold prh_pst. do 5 apply Exists_cons_tl. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
Qed.

Lemma keep_prh_ledger_st_pst : forall r ly S Hp W mem ly' S' Hp' W' mem' Lam peak cnt fail ran most own own',
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own -> tpk_alo_pst r W W' mem mem' ->
  (forall a, Exists (in_zr a) prh_pst -> in_img segs a) ->
  (forall a k, In (a, k) Lam -> 0 <= a - cf_head /\ a - cf_head + 8 <= YM05.alloc_ceiling) ->
  (forall a, Exists (in_zr a) tpk_glob_cells -> ~ in_zr a r) ->
  (forall a, pi_g_most <= a < pi_g_most + Z.of_nat pi_gz_most -> ~ in_zr a r) ->
  (forall a k i, In (a, k) Lam -> 0 <= i < 8 -> ~ in_zr (a - cf_head + i) r) ->
  (forall a k, In (a, k) Lam -> In (a - cf_head, k + cf_head) (ablocks B ly S) ->
     In (a - cf_head, k + cf_head) (ablocks B ly' S')) ->
  Permutation Hp' Hp ->
  prh_own W' mem' own' ->
  prh_ledger B ly' S' Hp' W' mem' Lam peak cnt fail ran most own'.
Proof.
intros r ly S Hp W mem ly' S' Hp' W' mem' Lam peak cnt fail ran most own own' HL KA HP HH GC GM HR Hb Hpp HO.
apply (prh_ledger_iff B) in HL as [HG HB]. apply (prh_ledger_iff B). split.
- destruct HG as (H1 & H2 & H3 & H4 & H5 & HM & _ & R). unfold prh_glob.
  split; [apply (prh_val_mem_keep _ _ _ _ _ H1); intros k Hk; apply prh_mbyte_of_aview; apply KA;
    [exact (tpk_pst_lo _ HP (prh_pst_live k Hk)) |
     apply GC; apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia]|].
  split; [apply (prh_val_mem_keep _ _ _ _ _ H2); intros k Hk; apply prh_mbyte_of_aview; apply KA;
    [exact (tpk_pst_lo _ HP (prh_pst_peak k Hk)) |
     apply GC; do 1 apply Exists_cons_tl; apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia]|].
  split; [apply (prh_val_mem_keep _ _ _ _ _ H3); intros k Hk; apply prh_mbyte_of_aview; apply KA;
    [exact (tpk_pst_lo _ HP (prh_pst_count k Hk)) |
     apply GC; do 2 apply Exists_cons_tl; apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia]|].
  split; [apply (prh_val_mem_keep _ _ _ _ _ H4); intros k Hk; apply prh_mbyte_of_aview; apply KA;
    [exact (tpk_pst_lo _ HP (prh_pst_fail k Hk)) |
     apply GC; do 3 apply Exists_cons_tl; apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia]|].
  split; [apply (prh_val_mem_keep _ _ _ _ _ H5); intros k Hk; apply prh_mbyte_of_aview; apply KA;
    [exact (tpk_pst_lo _ HP (prh_pst_ran k Hk)) |
     apply GC; do 4 apply Exists_cons_tl; apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia]|].
  split; [exact (keep_prh_most_pst r W W' mem mem' most HM KA HP GM)|].
  split; [exact HO | exact R].
- apply (prh_lblocks_kept B ly S Hp W mem ly' S' Hp' W' mem' Lam HB); [| exact Hb | exact Hpp].
  intros a k i Hin Hi. apply prh_mbyte_of_aview. apply KA; [pose proof (HH a k Hin); lia | exact (HR a k i Hin Hi)].
Qed.

Lemma keep_prh_ledger_pst : forall r ly S Hp W W' mem mem' Lam peak cnt fail ran most own own',
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own -> tpk_alo_pst r W W' mem mem' ->
  (forall a, Exists (in_zr a) prh_pst -> in_img segs a) ->
  (forall a k, In (a, k) Lam -> 0 <= a - cf_head /\ a - cf_head + 8 <= YM05.alloc_ceiling) ->
  (forall a, Exists (in_zr a) tpk_glob_cells -> ~ in_zr a r) ->
  (forall a, pi_g_most <= a < pi_g_most + Z.of_nat pi_gz_most -> ~ in_zr a r) ->
  (forall a k i, In (a, k) Lam -> 0 <= i < 8 -> ~ in_zr (a - cf_head + i) r) ->
  prh_own W' mem' own' ->
  prh_ledger B ly S Hp W' mem' Lam peak cnt fail ran most own'.
Proof.
intros r ly S Hp W W' mem mem' Lam peak cnt fail ran most own own' HL KA HP HH GC GM HR HO.
exact (keep_prh_ledger_st_pst r ly S Hp W mem ly S Hp W' mem' Lam peak cnt fail ran most own own' HL KA HP HH GC GM HR
  (fun _ _ _ H => H) (Permutation_refl Hp) HO).
Qed.

Lemma keep_arodata_okP_pst : forall r W W' mem mem',
  arodata_okP segs pa_relro_lo pa_relro_hi B (aview segs (w_H W) mem) -> tpk_alo_pst r W W' mem mem' ->
  (forall a, in_zr a r -> ~ in_roP segs pa_relro_lo pa_relro_hi a) ->
  arodata_okP segs pa_relro_lo pa_relro_hi B (aview segs (w_H W') mem').
Proof.
intros r W W' mem mem' Hro KA Hrw. unfold PresetRodata.arodata_okP in *. intros a Ha Ho He.
assert (Hi : in_img segs a).
{ destruct Ha as [(sg & Hs & _ & Hr) | Hr]; [exists sg; split; [exact Hs | exact Hr] | exact (pa_relro_img a Hr)]. }
pose proof (pa_segs_low a Hi) as Hl. pose proof YM05.alloc_ceiling_value as [C _]. unfold kLowMemEnd in Hl.
rewrite KA; [exact (Hro a Ha Ho He) | lia | intros Hr; exact (Hrw a Hr Ha)].
Qed.

Lemma keep_prhtx_place_pst : forall r ly S W W' regs mem mem' dw t,
  prhtx_place ly S W regs mem dw t -> t + 28 <= 2 ^ 47 ->
  (forall a, t <= a < t + 28 -> writable_at segs (rdW W' mem') a) ->
  tpk_alo_pst r W W' mem mem' -> (forall a, in_zr a r -> in_img segs a) -> prhtx_place ly S W' regs mem' dw t.
Proof.
intros r ly S W W' regs mem mem' dw t (Hal & Hlo & Hhi & _ & Hra) Ht Hw KA RI.
pose proof (bv_unsigned_in_range 64 (getr regs 2)) as [R _]. fold (spZ regs) in R.
split; [exact Hal|]. split; [exact Hlo|]. split; [exact Hhi|]. split; [exact Hw|].
apply (tpk_ra_keep (aview segs (w_H W) mem)); [|exact Hra]. intros x Hx. apply KA.
- apply tpk_shadow_lo. lia.
- apply (tpk_off_r_of_not_img r _ RI). apply tpk_shadow_not_img. lia.
Qed.

(* the NULL arm's frame fact: the frame, the record and ONE PST region r written *)
Lemma keep_bundle_frame_pst : forall r W mem mem' STK sp0 t,
  (forall x : word, ~ (sp0 - STK <= bv_unsigned x < sp0) -> ~ (t <= bv_unsigned x < t + 28) ->
     ~ in_zr (bv_unsigned x) r -> mrestrict (w_H W) mem' x = mrestrict (w_H W) mem x) ->
  (forall a, in_zr a r -> in_img segs a) ->
  0 <= STK -> YM05.alloc_ceiling <= sp0 - STK -> sp0 + 16 <= t ->
  tpk_mlo_pst r W W mem mem' /\ tpk_alo_pst r W W mem mem' /\ tpk_ahi sp0 t W W mem mem' /\
  tpk_mhi sp0 t W W mem mem'.
Proof.
intros r W mem mem' STK sp0 t Hf RI H0 Hce Ht. pose proof YM05.alloc_ceiling_value as [C _].
assert (KM : tpk_mlo_pst r W W mem mem') by (intros x Hx Hn; apply Hf; [lia | lia | exact Hn]).
assert (KH : tpk_mhi sp0 t W W mem mem').
{ intros x Hx Hn. apply Hf; [lia | exact Hn |]. intros Hr. pose proof (pa_segs_low _ (RI _ Hr)) as Hl.
  unfold kLowMemEnd in Hl. lia. }
split; [exact KM|]. split; [exact (tpk_alo_pst_of_mlo_pst _ _ _ _ _ KM)|].
split; [exact (tpk_ahi_of_mhi sp0 t W W mem mem' ltac:(lia) KH)|].
exact KH.
Qed.



End c.
