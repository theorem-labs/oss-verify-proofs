(* fuzz_preset asan-ubsan build, image B' (#102 pin d663f82d7f48, unstripped twin c90d4fa54d43): the image facts, the
   alloc.c ledger and the symbolic cells that the walks of parse_noting, fuzz_alloc_ran_out and
   fuzz_alloc_ran_out_reset share. Every image number comes from the generated PwSymsB.v; the instruction words come
   from the image itself (YP02.build_table over tfibsegs, = lib/B/Img0.v rsegs = the pinned image's loaded segments).
   The B' twin of lib/A/Prog/PwBase.v (A' blob f521a87c2d46). Relocated 2026-10-29 from the old-pin file
   (a working branch 5f6a2b85e1b9, image f8f98a95): no statement or proof changed; the numbers changed only
   in the regenerated PwSymsB.v. PR_PST / pr_glob below are this file's own five alloc.c cells (the generator's set),
   NOT the kit's prh_pst, which on #102 also has g_most and g_own_ran_out (PRH_Base.v prh_pst, prh_img_B's seven cells);
   PwAllocSurfB.v uses only pw_rcell / pw_wcell and their region_ok lemmas. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YI16 YM05 YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PwSymsB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Lemma pw_wx : wx_segs_nowrap tfibsegs.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.

Lemma pw_segs_low : forall a, in_img tfibsegs a -> 0 <= a < kLowMemEnd.
Proof.
intros a (sg & Hin & Hr).
assert (Hb : forallb (fun s => (0 <=? Z.of_N (seg_base s)) && (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? kLowMemEnd))
  tfibsegs = true) by (vm_compute; reflexivity).
pose proof (proj1 (forallb_forall _ _) Hb sg Hin) as H. apply andb_prop in H as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.

(* alloc.c's statics (source alloc.c:33-34): the bytes the program itself writes in the image, exempt from the
   journal's image clause (YCbqG ajournal_x, PST) and named in each walk that writes them. Lengths are the
   asan_globals descriptor sizes (PwSymsB.v), without the redzones. *)
Definition PR_PST : list (Z * Z) :=
  [(G_FAIL_AT, G_FAIL_AT_LEN); (G_LIVE, G_LIVE_LEN); (G_PEAK, G_PEAK_LEN); (G_COUNT, G_COUNT_LEN);
   (G_RAN_OUT, G_RAN_OUT_LEN)].

Definition in_img_rng_b (lo len : Z) : bool :=
  existsb (fun sg => (Z.of_N (seg_base sg) <=? lo) && (lo + len <=? Z.of_N (seg_base sg) + Z.of_N (seg_size sg))) tfibsegs.
Lemma in_img_rng_b_ok : forall lo len a, in_img_rng_b lo len = true -> lo <= a < lo + len -> in_img tfibsegs a.
Proof.
intros lo len a Hb Ha. unfold in_img_rng_b in Hb. apply existsb_exists in Hb as (sg & Hin & Hs).
apply andb_prop in Hs as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
exists sg. split; [exact Hin | lia].
Qed.
Lemma PR_PST_img : forall a, Exists (in_zr a) PR_PST -> in_img tfibsegs a.
Proof.
intros a H.
assert (Hb : forallb (fun r => in_img_rng_b (fst r) (snd r)) PR_PST = true) by (vm_compute; reflexivity).
apply Exists_exists in H as (r & Hr & Ha).
exact (in_img_rng_b_ok (fst r) (snd r) a (proj1 (forallb_forall _ _) Hb r Hr) Ha).
Qed.
Lemma PR_PST_low : forall a, Exists (in_zr a) PR_PST -> 0 <= a < kLowMemEnd.
Proof. intros a H. exact (pw_segs_low a (PR_PST_img a H)). Qed.

(* a function with no frame of its own (the three alloc.c accessors) needs no stack below its sp *)
Definition PW_LEAF_STK : Z := 0.

(* lbu of a byte below 256 gives the byte back *)
Lemma zext8_small : forall v, 0 <= v < 256 -> zext 64 (bv_extract 0 8 (Z_to_bv 64 v)) = Z_to_bv 64 v.
Proof.
intros v Hv. apply bv_eq. unfold zext. rewrite bv_zero_extend_unsigned by lia.
rewrite bv_extract_unsigned, !Z_to_bv_unsigned, Z.shiftr_0_r.
rewrite (bv_wrap_small 64 v) by (unfold bv_modulus; cbn; lia).
apply bv_wrap_small. unfold bv_modulus. cbn. lia.
Qed.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* the ledger (alloc.c:33-34): g_live, g_peak, g_count, g_fail_at (8 bytes each) and g_ran_out (one byte: the
   asan_globals descriptor says 1 and the code reads it with lbu / writes it with sb), as the walks read it, each value
   in its width's range; every PST byte is writable. *)
Definition pr_glob (W : world tfibsegs) (mem : word -> option byte) (live peak cnt fail ro : Z) : Prop :=
  val_mem tfibsegs (rdW W mem) G_LIVE (Z.to_nat G_LIVE_LEN) live /\
  val_mem tfibsegs (rdW W mem) G_PEAK (Z.to_nat G_PEAK_LEN) peak /\
  val_mem tfibsegs (rdW W mem) G_COUNT (Z.to_nat G_COUNT_LEN) cnt /\
  val_mem tfibsegs (rdW W mem) G_FAIL_AT (Z.to_nat G_FAIL_AT_LEN) fail /\
  val_mem tfibsegs (rdW W mem) G_RAN_OUT (Z.to_nat G_RAN_OUT_LEN) ro /\
  (forall a, Exists (in_zr a) PR_PST -> writable_at tfibsegs (rdW W mem) a) /\
  0 <= live < 2 ^ (8 * G_LIVE_LEN) /\ 0 <= peak < 2 ^ (8 * G_PEAK_LEN) /\ 0 <= cnt < 2 ^ (8 * G_COUNT_LEN) /\
  0 <= fail < 2 ^ (8 * G_FAIL_AT_LEN) /\ 0 <= ro < 2 ^ (8 * G_RAN_OUT_LEN).

(* the ledger rides through any step that leaves the five statics' bytes alone *)
Lemma pr_glob_frame : forall W (mem mem' : word -> option byte) live peak cnt fail ro,
  pr_glob W mem live peak cnt fail ro ->
  (forall a, Exists (in_zr a) PR_PST ->
     mrestrict (w_H W) mem' (Z_to_bv 64 a) = mrestrict (w_H W) mem (Z_to_bv 64 a)) ->
  pr_glob W mem' live peak cnt fail ro.
Proof.
intros W mem mem' live peak cnt fail ro (GL & GP & GC & GF & GR & GW & R) Hk.
assert (Hb : forall a n v, (forall k, (k < n)%nat -> Exists (in_zr (a + Z.of_nat k)) PR_PST) ->
  val_mem tfibsegs (mrestrict (w_H W) mem) a n v -> val_mem tfibsegs (mrestrict (w_H W) mem') a n v).
{ intros a n v Hin Hv k Hkn. unfold mbyte. rewrite (Hk (a + Z.of_nat k) (Hin k Hkn)). exact (Hv k Hkn). }
assert (Hr5 : forall b l k, In (b, l) PR_PST -> Z.of_nat k < l -> Exists (in_zr (b + Z.of_nat k)) PR_PST)
  by (intros b l k Hin Hk5; apply Exists_exists; exists (b, l); split;
      [exact Hin | unfold in_zr; cbn [fst snd]; lia]).
split; [|split; [|split; [|split; [|split; [|split]]]]].
- apply Hb; [intros k Hk5; apply (Hr5 G_LIVE G_LIVE_LEN k); [cbn; tauto | unfold G_LIVE_LEN in *; cbn in Hk5; lia] | exact GL].
- apply Hb; [intros k Hk5; apply (Hr5 G_PEAK G_PEAK_LEN k); [cbn; tauto | unfold G_PEAK_LEN in *; cbn in Hk5; lia] | exact GP].
- apply Hb; [intros k Hk5; apply (Hr5 G_COUNT G_COUNT_LEN k); [cbn; tauto | unfold G_COUNT_LEN in *; cbn in Hk5; lia] | exact GC].
- apply Hb; [intros k Hk5; apply (Hr5 G_FAIL_AT G_FAIL_AT_LEN k); [cbn; tauto | unfold G_FAIL_AT_LEN in *; cbn in Hk5; lia] | exact GF].
- apply Hb; [intros k Hk5; apply (Hr5 G_RAN_OUT G_RAN_OUT_LEN k); [cbn; tauto | unfold G_RAN_OUT_LEN in *; cbn in Hk5; lia] | exact GR].
- intros a Ha. unfold writable_at, wview in *. rewrite (Hk a Ha). exact (GW a Ha).
- exact R.
Qed.

(* the ledger is read through absolute-address regions (YP09 base None): a read cell holding the env atom n, and a
   write cell with an empty chunk list *)
Definition pw_rcell (a len : Z) (n : nat) : YP09.region :=
  YP09.mkRegion None a (a + len) 0 0 [YP09.mkChunk a (CVal (Z.to_N len) (SOff n 0))].
Definition pw_wcell (a len : Z) : YP09.region := YP09.mkRegion None a (a + len) a (a + len) [].

Lemma region_ok_pw_rcell : forall E (m : word -> option byte) a len k v,
  val_mem tfibsegs m a (Z.to_nat len) v -> ew E k = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * len) -> 0 < len <= 8 ->
  0 <= a -> a + len <= 2 ^ 64 ->
  region_ok tfibsegs E m (pw_rcell a len k).
Proof.
intros E m a len k v Hv Hk Hr Hl Ha Hh. unfold region_ok, pw_rcell.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
assert (H64 : 2 ^ (8 * len) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. apply Forall_cons; [|apply Forall_nil].
apply (chunk_ok_val tfibsegs E m 0 a (Z.to_N len) (SOff k 0) v).
- cbn [sv_denot]. rewrite Hk, unsigned_lit_small by lia. f_equal. lia.
- rewrite Z2N.id by lia. exact Hr.
- rewrite Z2N.id by lia. lia.
- rewrite Z.add_0_l. replace (N.to_nat (Z.to_N len)) with (Z.to_nat len) by (destruct len; reflexivity). exact Hv.
Qed.
(* a read cell at the value of atom nn, holding the value of atom k: the shadow-base cell, which the code reaches
   through the address it read from the .got slot *)
Definition pw_rbase (nn : nat) (len : Z) (k : nat) : YP09.region :=
  YP09.mkRegion (Some nn) 0 len 0 0 [YP09.mkChunk 0 (CVal (Z.to_N len) (SOff k 0))].
Lemma region_ok_pw_rbase : forall E (m : word -> option byte) (nn : nat) p len k v,
  bv_unsigned (ew E nn) = p -> val_mem tfibsegs m p (Z.to_nat len) v -> ew E k = Z_to_bv 64 v ->
  0 <= v < 2 ^ (8 * len) -> 0 < len <= 8 -> 0 <= p -> p + len <= 2 ^ 64 ->
  region_ok tfibsegs E m (pw_rbase nn len k).
Proof.
intros E m nn p len k v Hn Hv Hk Hr Hl Ha Hh. unfold region_ok, pw_rbase.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Hn.
assert (H64 : 2 ^ (8 * len) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. apply Forall_cons; [|apply Forall_nil].
apply (chunk_ok_val tfibsegs E m p 0 (Z.to_N len) (SOff k 0) v).
- cbn [sv_denot]. rewrite Hk, unsigned_lit_small by lia. f_equal. lia.
- rewrite Z2N.id by lia. exact Hr.
- rewrite Z2N.id by lia. lia.
- rewrite Z.add_0_r. replace (N.to_nat (Z.to_N len)) with (Z.to_nat len) by (destruct len; reflexivity). exact Hv.
Qed.
Lemma region_ok_pw_wcell : forall E (m : word -> option byte) a len,
  (forall x, a <= x < a + len -> writable_at tfibsegs m x) -> 0 <= a -> a + len <= 2 ^ 64 -> 0 <= len ->
  region_ok tfibsegs E m (pw_wcell a len).
Proof.
intros E m a len Hw Ha Hh Hl. unfold region_ok, pw_wcell.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
intros o Ho. rewrite Z.add_0_l. apply Hw. lia.
Qed.
(* a writable window of len bytes at the value of atom nn (an output the caller passes by pointer) *)
Lemma region_ok_wbase : forall E (m : word -> option byte) (nn : nat) p len,
  bv_unsigned (ew E nn) = p -> 0 <= p -> p + len <= 2 ^ 64 -> 0 <= len ->
  (forall a, p <= a < p + len -> writable_at tfibsegs m a) ->
  region_ok tfibsegs E m (YP09.mkRegion (Some nn) 0 len 0 len []).
Proof.
intros E m nn p len Hn Hlo Hhi Hl Hw. unfold region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite Hn. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
intros o Ho. apply Hw. lia.
Qed.
Lemma in_wrange_wcell : forall E a lo len, in_wrange E [pw_wcell lo len] a -> lo <= a < lo + len.
Proof.
intros E a lo len (r & [<-|[]] & Ha). cbn [pw_wcell YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. lia.
Qed.
(* a byte outside a write cell is the same byte after the run *)
Lemma wcell_kept_at : forall E (m m' : word -> option byte) lo len a,
  frame_of E [pw_wcell lo len] m m' -> ~ (lo <= a < lo + len) -> 0 <= a < 2 ^ 64 ->
  m' (Z_to_bv 64 a) = m (Z_to_bv 64 a).
Proof.
intros E m m' lo len a HF Hn Ha. apply HF. rewrite unsigned_lit_small by lia.
intros Hw. exact (Hn (in_wrange_wcell E a lo len Hw)).
Qed.
Lemma val_mem_wcell_kept : forall E (m m' : word -> option byte) lo len a (n : nat) v,
  frame_of E [pw_wcell lo len] m m' -> (a + Z.of_nat n <= lo \/ lo + len <= a) -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  val_mem tfibsegs m a n v -> val_mem tfibsegs m' a n v.
Proof.
intros E m m' lo len a n v HF Hd Ha Hh Hv k Hk. pose proof (Hv k Hk) as Hb. unfold mbyte in *.
rewrite (wcell_kept_at E m m' lo len (a + Z.of_nat k) HF ltac:(lia) ltac:(lia)). exact Hb.
Qed.
Lemma writable_wcell_kept : forall E (m m' : word -> option byte) lo len a,
  frame_of E [pw_wcell lo len] m m' -> ~ (lo <= a < lo + len) -> 0 <= a < 2 ^ 64 ->
  writable_at tfibsegs m a -> writable_at tfibsegs m' a.
Proof.
intros E m m' lo len a HF Hn Ha Hw. unfold writable_at, wview in *.
rewrite (wcell_kept_at E m m' lo len a HF Hn Ha). exact Hw.
Qed.
End c.
