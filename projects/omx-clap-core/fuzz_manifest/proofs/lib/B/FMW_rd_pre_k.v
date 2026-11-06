(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/AF0x.v, with its module paths and module names changed; 571 of its 675 lines of code are new or changed and 468 lines of the source are left out. *)
(* B twin (fm.asan-ubsan, pin ca61e5c9eabc0050) of lib/A/FMW_rd_pre_k.v on a working branch e2e59892bef: adapted to B's entry segment (registers, the one-record frame chain helpers). *)
(* lv2_locate_manifest_readings, entry segment (0x81e94 .. RD_R / RD_L): the segment's own lemmas.
   The poison window: fuzz_malloc returns whole with its 16-byte head user-poisoned (U = [(whole - 16, 16)]); the
   journal is kept over `unpoison U mem` (FMupoison.v), the runtime contracts inside the window (snprintf, strstr) take
   the real memory. These lemmas move facts between the two views (they differ only on the head's two shadow bytes),
   carry the journal across a call inside the window, carry a caller's C strings across a program call (cstr_kept,
   suffix-closed image arm), and give the whole string's room below alloc_ceiling (a primary chunk). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q YCbm.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0q YG0s YC20 YI00 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require Import YB1v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMPstat FMH_Base FMH_Rt FMH_Fn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMW_g3kit FMW_rd_base.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require Import YCej.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require Import ManifestModel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- small list facts ---- *)
Lemma rdp_nth_skipn : forall (l : list Z) k j, nth j (skipn k l) 0 = nth (k + j) l 0.
Proof.
induction l as [|x l IH]; intros [|k] j; cbn; try reflexivity; [destruct j; reflexivity | apply IH].
Qed.
Lemma rdp_Forall_skipn : forall (P : Z -> Prop) (l : list Z) k, Forall P l -> Forall P (skipn k l).
Proof.
intros P l k H. revert k. induction H as [|x l Hx Hl IH]; intros [|k]; cbn; try constructor; auto.
Qed.

(* ---- the whole string and strstr's answer (ManifestModel.whole) ---- *)
Definition rdp_out (ub : list Z) : list Z := 60 :: ub ++ [62].
Lemma rdp_out_len : forall ub, length (rdp_out ub) = (length ub + 2)%nat.
Proof. intros ub. unfold rdp_out. cbn [length]. rewrite length_app. cbn [length]. lia. Qed.
Lemma rdp_whole_occ : forall tb ub j, occ_at tb (rdp_out ub) j -> ManifestModel.whole tb ub = true.
Proof.
intros tb ub j [Hj Heq]. rewrite rdp_out_len in Hj, Heq. unfold ManifestModel.whole. apply existsb_exists.
exists j. split; [apply in_seq; lia|]. unfold ManifestModel.whole_at. apply ManifestModel.zl_eqb_eq. exact Heq.
Qed.
Lemma rdp_whole_no : forall tb ub, no_occ tb (rdp_out ub) -> ManifestModel.whole tb ub = false.
Proof.
intros tb ub H. unfold ManifestModel.whole. apply Bool.not_true_iff_false. intros Hx.
apply existsb_exists in Hx as (j & Hj & Hw). apply (H j). unfold ManifestModel.whole_at in Hw.
apply ManifestModel.zl_eqb_eq in Hw. unfold occ_at. rewrite rdp_out_len. split; [|exact Hw].
assert (L := f_equal (@length Z) Hw). rewrite length_firstn, length_skipn in L. fold (rdp_out ub) in L.
rewrite rdp_out_len in L. lia.
Qed.

(* ---- fm's read-only strings lie in the image (one load segment covers 0x20d00 .. 0x21000) ---- *)
Lemma rdp_img_rng : forall lo hi x, lo <= x < hi ->
  existsb (fun s => (Z.of_N (seg_base s) <=? lo) && (hi <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) tfibsegs = true ->
  in_img tfibsegs x.
Proof.
intros lo hi x Hx Hb. apply existsb_exists in Hb as (s & Hs & Hss). apply andb_prop in Hss as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2. exists s. split; [exact Hs | lia].
Qed.
Lemma rdp_img_ro : forall x, 0x20d00 <= x < 0x21000 -> in_img tfibsegs x.
Proof. intros x Hx. apply (rdp_img_rng 0x20d00 0x21000 x Hx). vm_compute. reflexivity. Qed.
Lemma rdp_img_canary : forall x, FM_canary <= x < FM_canary + 8 -> in_img tfibsegs x.
Proof. intros x Hx. apply (rdp_img_rng FM_canary (FM_canary + 8) x Hx). vm_compute. reflexivity. Qed.
Ltac rdp_zlen := lazymatch goal with |- context [Z.of_nat (length ?l)] =>
  let v := eval vm_compute in (Z.of_nat (length l)) in change (Z.of_nat (length l)) with v end.
Lemma rdp_ro_bounds : forall p0 l0, (In (p0, l0) FM_RO_STRS \/ (exists ps, In (p0, ps) FM_SN_FMTS /\ l0 = fmt_bytes ps)) ->
  0x20d00 <= p0 /\ p0 + Z.of_nat (length l0) < 0x21000.
Proof.
intros p0 l0 [H | (ps & H & ->)].
- cbv [FM_RO_STRS In] in H.
  repeat (destruct H as [H|H]; [injection H as <- <-; unfold STR_empty; rdp_zlen; lia|]). destruct H.
- cbv [FM_SN_FMTS In] in H.
  repeat (destruct H as [H|H]; [injection H as <- <-;
    unfold FMT_whole, FMT_tw, FMT_tx, FMT_t1, FMT_t2, FMT_t3, FMT_t1x; rdp_zlen; lia|]). destruct H.
Qed.

(* ---- the allocator: a small block is a primary chunk, a page and more below alloc_ceiling ---- *)
Lemma rdp_from_primary : forall n, 0 <= n <= 4096 -> from_primary n = true.
Proof.
intros n Hn. unfold from_primary, needed_primary. apply Z.leb_le.
pose proof (rounded_size_bounds n ltac:(lia)) as [R1 _].
assert (Rz : rz_size n <= 2048).
{ unfold rz_size, rz_log. repeat (destruct (_ <=? _)); apply Z.leb_le; vm_compute; reflexivity. }
unfold kMaxSize. lia.
Qed.

(* ---- an 8-byte value in memory read as a word (rdword): B's frame-pointer chain at the fuzz_malloc / fuzz_free calls
   reads readings' saved ra / s0 (copied from cgif_file_fuzzer lib/YF0x.v:473-512 as ReusableB/YF0x.v has them; that
   module reaches YF0m, which G3 does not import) ---- *)
Lemma rdp_ulit8 : forall z, 0 <= z < 256 -> bv_unsigned (Z_to_bv 8 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. apply Z.mod_small. exact Hz. Qed.
Lemma rdp_le_bytes8_sum : forall z, 0 <= z < 2 ^ 64 ->
  let b := fun k => YG0f.le_byte z 8 k in
  b 0%nat + 256 * (b 1%nat + 256 * (b 2%nat + 256 * (b 3%nat + 256 * (b 4%nat + 256 * (b 5%nat + 256 * (b 6%nat + 256 * b 7%nat)))))) = z.
Proof.
intros z Hz. cbn beta. unfold YG0f.le_byte. rewrite !Z.shiftr_div_pow2 by lia.
rewrite (Z.mod_small z) by (change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64); lia).
change (2 ^ (8 * Z.of_nat 0)) with 1. change (2 ^ (8 * Z.of_nat 1)) with 256. change (2 ^ (8 * Z.of_nat 2)) with (256 * 256).
change (2 ^ (8 * Z.of_nat 3)) with (256 * 256 * 256). change (2 ^ (8 * Z.of_nat 4)) with (256 * 256 * 256 * 256).
change (2 ^ (8 * Z.of_nat 5)) with (256 * 256 * 256 * 256 * 256). change (2 ^ (8 * Z.of_nat 6)) with (256 * 256 * 256 * 256 * 256 * 256).
change (2 ^ (8 * Z.of_nat 7)) with (256 * 256 * 256 * 256 * 256 * 256 * 256).
rewrite Z.div_1_r. rewrite <- !Z.div_div by lia.
assert (H7 : z / 256 / 256 / 256 / 256 / 256 / 256 / 256 < 256).
{ change (2 ^ 64) with (256 * 256 * 256 * 256 * 256 * 256 * 256 * 256) in Hz.
  repeat (apply Z.div_lt_upper_bound; [lia|]). lia. }
rewrite (Z.mod_small (z / 256 / 256 / 256 / 256 / 256 / 256 / 256)) by (split; [repeat (apply Z.div_pos; [|lia]); lia | exact H7]).
pose proof (Z.div_mod z 256 ltac:(lia)) as E0.
pose proof (Z.div_mod (z / 256) 256 ltac:(lia)) as E1.
pose proof (Z.div_mod (z / 256 / 256) 256 ltac:(lia)) as E2.
pose proof (Z.div_mod (z / 256 / 256 / 256) 256 ltac:(lia)) as E3.
pose proof (Z.div_mod (z / 256 / 256 / 256 / 256) 256 ltac:(lia)) as E4.
pose proof (Z.div_mod (z / 256 / 256 / 256 / 256 / 256) 256 ltac:(lia)) as E5.
pose proof (Z.div_mod (z / 256 / 256 / 256 / 256 / 256 / 256) 256 ltac:(lia)) as E6.
lia.
Qed.
Lemma rdp_val_mem_rdword {fx : YK11.FPState} {rc : YM05.RunCeil} : forall (H : word -> bool) mem a v,
  0 <= v < 2 ^ 64 -> val_mem tfibsegs (mrestrict H mem) a 8 v -> rdword (aview tfibsegs H mem) a = Some v.
Proof.
intros H mem a v Hv Hm. unfold rdword, aview.
assert (B : forall k, (k < 8)%nat -> mbyte tfibsegs (mrestrict H mem) (a + Z.of_nat k) = Some (Z_to_bv 8 (YG0f.le_byte v 8 k))).
{ intros k Hk. exact (Hm k Hk). }
assert (R : forall k, 0 <= YG0f.le_byte v 8 k < 256) by (intros k; unfold YG0f.le_byte; apply Z.mod_pos_bound; lia).
replace a with (a + Z.of_nat 0) at 1 by lia.
replace (a + 1) with (a + Z.of_nat 1) by lia. replace (a + 2) with (a + Z.of_nat 2) by lia. replace (a + 3) with (a + Z.of_nat 3) by lia.
replace (a + 4) with (a + Z.of_nat 4) by lia. replace (a + 5) with (a + Z.of_nat 5) by lia. replace (a + 6) with (a + Z.of_nat 6) by lia.
replace (a + 7) with (a + Z.of_nat 7) by lia.
rewrite !B by lia. cbn [option_map]. rewrite !rdp_ulit8 by apply R.
f_equal. apply rdp_le_bytes8_sum. exact Hv.
Qed.

Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

Lemma rdp_blk_slack : forall ly S W mem md p n, AR tfibsegs B ly S W mem md -> In (p, n) (ablocks B ly S) ->
  0 <= n <= 4096 -> kHighMemBeg <= p /\ p + n + 4096 <= alloc_ceiling.
Proof.
intros ly S W mem md p n HAR Hin Hn. destruct HAR as (M & _).
apply In_ablocks in Hin as (k & Hk & _ & Hu & Hq).
pose proof (chunk_facts B ly S _ k M Hk) as (_ & _ & _ & Huser & Hrz & _ & _ & Hext & Hbeg).
pose proof (am_layout B ly S _ M) as LO.
pose proof (lo_space_in ly LO) as [SP1 SP2]. pose proof (lo_high ly LO) as [HI1 HI2].
pose proof (req_size_bounds n ltac:(lia)) as (_ & _ & Rq & _).
rewrite Hq in Hext. rewrite <- Hu, Huser.
revert Hbeg. destruct (ck_beg k) eqn:Eb; intros Hbeg; cbv beta iota zeta in Hbeg; try contradiction.
- destruct Hbeg as (Hc & _ & _ & Hextc & Hbase & Hx0 & _ & Hxu & Hrg1 & Hrg2).
  rewrite Hextc in Hext. rewrite Hbase. unfold region_base, region_off in *.
  rewrite Z.shiftl_mul_pow2 in * by lia. change (2 ^ 32) with 4294967296 in *.
  unfold kSpaceSize, kFreeArrayOffset, ASAN_CEIL in *. change (2 ^ 37) with 137438953472 in *. lia.
- destruct Hbeg as (_ & Hfp & _). rewrite Hq, rdp_from_primary in Hfp by lia. discriminate.
Qed.

(* ---- one user-poisoned head: the two views differ only on its two shadow bytes ---- *)
Lemma rdp_ush1 : forall h s, 0 <= h -> h + 16 <= kHighMemEnd -> in_ush [(h, 16)] s = true ->
  shadow_addr h <= s < shadow_addr h + 2 /\ SHADOW_OFF <= s < kHighMemBeg.
Proof.
intros h s H0 H1 Hs. rewrite in_ush_cons16 in Hs. change (in_ush [] s) with false in Hs.
rewrite Bool.orb_false_r in Hs. apply andb_prop in Hs as [A1 A2]. apply Z.leb_le in A1. apply Z.ltb_lt in A2.
split; [lia|].
assert (D : (h + 2 * 8) / 8 = h / 8 + 2) by (apply Z.div_add; lia).
assert (D2 : (h + 2 * 8) / 8 <= kHighMemEnd / 8) by (apply Z.div_le_mono; lia).
pose proof (Z.div_pos h 8 ltac:(lia) ltac:(lia)).
unfold shadow_addr, SHADOW_OFF, kHighMemBeg, kHighMemEnd in *.
change (0x800000000000 / 8) with 17592186044416 in D2. lia.
Qed.
Lemma rdp_ush_app : forall h s, 0 <= h -> h + 16 <= kHighMemEnd -> (s < SHADOW_OFF \/ kHighMemBeg <= s) ->
  in_ush [(h, 16)] s = false.
Proof.
intros h s H0 H1 Hs. destruct (in_ush [(h, 16)] s) eqn:E; [|reflexivity].
apply rdp_ush1 in E; [lia | lia | lia].
Qed.
Lemma rdp_ush_x : forall h x, h mod 8 = 0 -> ~ (h <= x < h + 16) -> in_ush [(h, 16)] (shadow_addr x) = false.
Proof.
intros h x H8 Hx. rewrite in_ush_cons16. change (in_ush [] (shadow_addr x)) with false. rewrite Bool.orb_false_r.
apply andb_false_iff. unfold shadow_addr.
pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.mod_pos_bound x 8 ltac:(lia)).
pose proof (Z.div_mod h 8 ltac:(lia)).
destruct (Z.leb_spec (SHADOW_OFF + h / 8) (SHADOW_OFF + x / 8)); [right | left; reflexivity].
apply Z.ltb_ge. lia.
Qed.
Lemma rdp_aview_unp : forall H h m a, 0 <= h -> h + 16 <= kHighMemEnd -> 0 <= a < 2 ^ 64 ->
  (a < SHADOW_OFF \/ kHighMemBeg <= a) -> aview tfibsegs H (unpoison [(h, 16)] m) a = aview tfibsegs H m a.
Proof.
intros H h m a H0 H1 Ha Hs. apply aview_unpoison_out. rewrite unsigned_lit_small by lia.
apply rdp_ush_app; assumption.
Qed.
Lemma rdp_apresent_unp : forall H U m a, in_ush U (bv_unsigned (Z_to_bv 64 a)) = false ->
  (apresent H (unpoison U m) a <-> apresent H m a).
Proof. intros H U m a E. unfold apresent. rewrite (unpoison_out U m _ E). tauto. Qed.
(* the unpoisoned view of a stack byte (U = [] or one head) *)
Definition rdp_U1 (U : list (Z * Z)) : Prop := U = [] \/ exists h, U = [(h, 16)] /\ 0 <= h /\ h + 16 <= kHighMemEnd.
Lemma rdp_aview_unp_hi : forall H U m a, rdp_U1 U -> kHighMemBeg <= a < 2 ^ 64 ->
  aview tfibsegs H (unpoison U m) a = aview tfibsegs H m a.
Proof.
intros H U m a [-> | (h & -> & H0 & H1)] Ha; [reflexivity|]. pose proof asan_consts as (_ & _ & C3 & _).
apply rdp_aview_unp; [lia | lia | lia | right; lia].
Qed.
Lemma rdp_apresent_unp_hi : forall H U m a, rdp_U1 U -> kHighMemBeg <= a < 2 ^ 64 ->
  (apresent H (unpoison U m) a <-> apresent H m a).
Proof.
intros H U m a [-> | (h & -> & H0 & H1)] Ha; [tauto|]. pose proof asan_consts as (_ & _ & C3 & _).
apply rdp_apresent_unp. rewrite unsigned_lit_small by lia.
apply rdp_ush_app; [lia | lia | right; lia].
Qed.

(* ---- fm_img_facts' answers out of the unpoisoned view ---- *)
Lemma rdp_in_rom_low : forall a, in_rom tfibsegs a -> 0 <= a < kLowMemEnd.
Proof. intros a (s & Hs & _ & Hr). apply g3_segs_low. exists s. split; [exact Hs | exact Hr]. Qed.
Lemma rdp_rom_view_unp : forall (W : world tfibsegs) h m, 0 <= h -> h + 16 <= kHighMemEnd ->
  rom_viewN tfibsegs B W (unpoison [(h, 16)] m) -> rom_viewN tfibsegs B W m.
Proof.
intros W h m H0 H1 HR a Ha Ho He. pose proof (rdp_in_rom_low a Ha) as Hl. pose proof asan_consts as (_ & _ & _ & _ & C5).
rewrite <- (rdp_aview_unp (w_H W) h m a H0 H1); [exact (HR a Ha Ho He) | lia | left; unfold SHADOW_OFF; lia].
Qed.
Lemma rdp_rom_viewO_unp : forall (W : world tfibsegs) h m, 0 <= h -> h + 16 <= kHighMemEnd ->
  rom_viewO tfibsegs B W (unpoison [(h, 16)] m) -> rom_viewO tfibsegs B W m.
Proof.
intros W h m H0 H1 HR a Ha Ho. pose proof (rdp_in_rom_low a Ha) as Hl. pose proof asan_consts as (_ & _ & _ & _ & C5).
rewrite <- (rdp_aview_unp (w_H W) h m a H0 H1); [exact (HR a Ha Ho) | lia | left; unfold SHADOW_OFF; lia].
Qed.
(* a heap block holds no image byte, hence no read-only one *)
Lemma rdp_blk_not_rom : forall ly S W mem md p n a, AR tfibsegs B ly S W mem md -> In (p, n) (ablocks B ly S) ->
  p <= a < p + req_size n -> ~ in_rom tfibsegs a.
Proof.
intros ly S W mem md p n a HAR Hin Ha (s & Hs & _ & Hr).
apply (blk_img tfibsegs B LAWS ly S W mem md p n a HAR Hin Ha). exists s. split; [exact Hs | exact Hr].
Qed.
Lemma rdp_val_mem_unp_low : forall (W : world tfibsegs) h m a n v, 0 <= h -> h + 16 <= kHighMemEnd -> 0 <= a -> a + Z.of_nat n <= kLowMemEnd ->
  val_mem tfibsegs (rdW W (unpoison [(h, 16)] m)) a n v -> val_mem tfibsegs (rdW W m) a n v.
Proof.
intros W h m a n v H0 H1 Ha Hn Hv. apply (g3_val_mem_kept W W (unpoison [(h, 16)] m) m); [exact Hv|].
intros i Hi. symmetry. apply rdp_aview_unp; [lia | lia | unfold kLowMemEnd in *; lia | left; unfold SHADOW_OFF, kLowMemEnd in *; lia].
Qed.
Lemma rdp_canary_unp : forall W h m, 0 <= h -> h + 16 <= kHighMemEnd ->
  fm_canary tfibsegs W (unpoison [(h, 16)] m) -> fm_canary tfibsegs W m.
Proof.
intros W h m H0 H1 (cv & C1 & C2 & C3). exists cv. split; [|split; [|exact C3]];
  (eapply rdp_val_mem_unp_low; [exact H0 | exact H1 | | | eassumption]); unfold FM_GOT_canary, FM_canary, kLowMemEnd; cbn; lia.
Qed.
(* a C string whose bytes miss the head: cstr_ok out of the unpoisoned view *)
Lemma rdp_cstr_unp : forall W m h p l, 0 <= h -> h mod 8 = 0 -> h + 16 <= kHighMemEnd ->
  (forall x, p <= x <= p + Z.of_nat (length l) -> ~ (h <= x < h + 16)) ->
  upoisoned tfibsegs W m [(h, 16)] ->
  cstr_ok tfibsegs W (unpoison [(h, 16)] m) p l -> cstr_ok tfibsegs W m p l.
Proof.
intros W m h p l H0 H8 Hh Hdj HP ((Hg & Hnz) & H4 & Hc & H32 & Ham & Hra & Hhv & Htl).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (APP : forall a, p <= a < p + Z.of_nat (length l) + 8 ->
  aview tfibsegs (w_H W) (unpoison [(h, 16)] m) a = aview tfibsegs (w_H W) m a).
{ intros a Ha. apply rdp_aview_unp; [exact H0 | exact Hh | |];
    unfold amem_range in Ham; unfold kLowMemEnd, kHighMemBeg, kHighMemEnd, SHADOW_OFF in *; lia. }
assert (SH : forall x, p <= x < p + Z.of_nat (length l) + 1 ->
  aview tfibsegs (w_H W) m (shadow_of_addr SHADOW_OFF x) = aview tfibsegs (w_H W) (unpoison [(h, 16)] m) (shadow_of_addr SHADOW_OFF x)).
{ intros x Hx. symmetry. apply aview_unpoison_out. change (shadow_of_addr SHADOW_OFF x) with (shadow_addr x).
  rewrite unsigned_lit_small; [apply rdp_ush_x; [exact H8 | apply Hdj; lia]|].
  unfold shadow_addr, SHADOW_OFF. pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)).
  assert (x / 8 < 2 ^ 47) by (apply Z.div_lt_upper_bound; lia). lia. }
split; [split; [|exact Hnz]|].
{ apply (g3_garr8_kept W W (unpoison [(h, 16)] m) m p (l ++ [0]) Hg). intros i Hi. rewrite length_app in Hi.
  cbn [length] in Hi. symmetry. apply APP. lia. }
split; [exact H4|]. split; [exact Hc|]. split; [exact H32|]. split; [exact Ham|]. split.
{ eapply range_addressable_agree; [|exact Hra]. intros x Hx. apply SH. lia. }
split.
{ intros s Hs.
  assert (Hs64 : 0 <= s < 2 ^ 64).
  { unfold shadow_addr, SHADOW_OFF in Hs.
    assert (Q0 : 0 <= p / 8) by (apply Z.div_pos; lia).
    assert (Q1 : 0 <= (2147450880 + p / 8) / 8 * 8) by (apply Z.mul_nonneg_nonneg; [apply Z.div_pos; lia | lia]).
    assert (Q2 : (2147450880 + (p + Z.of_nat (length l) + 1 - 1) / 8) / 8 * 8 <=
                 2147450880 + (p + Z.of_nat (length l) + 1 - 1) / 8) by (rewrite Z.mul_comm; apply Z.mul_div_le; lia).
    assert (Q3 : (p + Z.of_nat (length l) + 1 - 1) / 8 < 2 ^ 47) by (apply Z.div_lt_upper_bound; lia).
    lia. }
  destruct (in_ush [(h, 16)] s) eqn:E.
  - rewrite (HP s E). discriminate.
  - rewrite <- (aview_unpoison_out tfibsegs (w_H W) [(h, 16)] m s ltac:(rewrite unsigned_lit_small by exact Hs64; exact E)).
    exact (Hhv s Hs). }
intros a Ha. rewrite <- APP by (pose proof (Z.mod_pos_bound (p + Z.of_nat (length l)) 8); lia). exact (Htl a Ha).
Qed.

(* ---- a suffix of a C string ---- *)
Lemma rdp_shadow_hull_vis_sub : forall rd x n x' n',
  shadow_hull_vis rd x n -> x <= x' -> x' + n' <= x + n -> 0 < n' -> shadow_hull_vis rd x' n'.
Proof.
intros rd x n x' n' H H1 H2 H3 s Hs. apply H. unfold shadow_addr, SHADOW_OFF in *.
assert (M1 : (2147450880 + x / 8) / 8 <= (2147450880 + x' / 8) / 8)
  by (apply Z.div_le_mono; [lia|]; pose proof (Z.div_le_mono x x' 8 ltac:(lia) H1); lia).
assert (M2 : (2147450880 + (x' + n' - 1) / 8) / 8 <= (2147450880 + (x + n - 1) / 8) / 8)
  by (apply Z.div_le_mono; [lia|]; pose proof (Z.div_le_mono (x' + n' - 1) (x + n - 1) 8 ltac:(lia) ltac:(lia)); lia).
lia.
Qed.
Lemma rdp_cstr_suffix : forall W m p l k, cstr_ok tfibsegs W m p l -> (k <= length l)%nat ->
  cstr_ok tfibsegs W m (p + Z.of_nat k) (skipn k l).
Proof.
intros W m p l k ((Hg & Hnz) & H4 & Hc & H32 & Ham & Hra & Hhv & Htl) Hk.
assert (Hlen : Z.of_nat (length (skipn k l)) = Z.of_nat (length l) - Z.of_nat k) by (rewrite length_skipn; lia).
split; [split|].
- intros j Hj. rewrite length_app, length_skipn in Hj. cbn [length] in Hj.
  destruct (Hg (k + j)%nat ltac:(rewrite length_app; cbn [length]; lia)) as [Hv Hr].
  replace (p + Z.of_nat k + Z.of_nat j) with (p + Z.of_nat (k + j)) by lia.
  assert (E : nth j (skipn k l ++ [0]) 0 = nth (k + j) (l ++ [0]) 0).
  { rewrite <- rdp_nth_skipn. f_equal. rewrite skipn_app. replace (k - length l)%nat with 0%nat by lia. reflexivity. }
  rewrite E. exact (conj Hv Hr).
- apply rdp_Forall_skipn. exact Hnz.
- rewrite Hlen. split; [lia|]. split; [lia|]. split; [lia|]. split; [unfold amem_range in *; lia|]. split.
  + intros x Hx. apply Hra. lia.
  + split.
    * apply (rdp_shadow_hull_vis_sub _ p (Z.of_nat (length l) + 1)); [exact Hhv | lia | lia | lia].
    * intros a Ha. apply Htl. replace (p + Z.of_nat k + (Z.of_nat (length l) - Z.of_nat k)) with (p + Z.of_nat (length l)) in Ha by lia.
      exact Ha.
Qed.

(* ---- a heap block is visible to the end of the word holding its last byte (G6 FMW_kit.v block_word_tail_vis) ---- *)
Lemma rdp_word_end_le : forall x base ext, base mod 16 = 0 -> ext mod 8 = 0 -> x < base + ext ->
  x - x mod 8 + 8 <= base + ext.
Proof.
intros x base ext H1 H2 H3.
pose proof (Z.div_mod base 16 ltac:(lia)) as D1. pose proof (Z.div_mod ext 8 ltac:(lia)) as D2.
pose proof (Z.div_mod x 8 ltac:(lia)) as D3. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as D4.
lia.
Qed.
Lemma rdp_extent_mod8 : forall k, 0 <= ck_req k -> ck_extent k mod 8 = 0.
Proof.
intros k Hq. unfold ck_extent. destruct (from_primary (ck_req k)) eqn:Ep.
- pose proof (primary_geometry (ck_req k) Hq Ep) as (_ & _ & _ & H32 & _).
  set (c := class_size (chunk_class (ck_req k))) in *.
  pose proof (Z.div_mod c 32 ltac:(lia)) as D. pose proof (Z.div_mod c 8 ltac:(lia)) as D8.
  pose proof (Z.mod_pos_bound c 8 ltac:(lia)) as R8. lia.
- pose proof (secondary_geometry (ck_req k) Hq Ep) as (_ & _ & _ & _ & HP & _).
  set (s := sec_map_size (ck_req k)) in *. unfold kPage in *.
  pose proof (Z.div_mod s 4096 ltac:(lia)) as D. pose proof (Z.div_mod (s - 4096) 8 ltac:(lia)) as D8.
  pose proof (Z.mod_pos_bound (s - 4096) 8 ltac:(lia)) as R8. lia.
Qed.
Lemma rdp_block_tail_vis : forall ly S (W : world tfibsegs) mem md b m,
  AR tfibsegs B ly S W mem md -> In (b, m) (ablocks B ly S) -> 0 < m ->
  forall a, b <= a < (b + m - 1) - (b + m - 1) mod 8 + 8 -> aview tfibsegs (w_H W) mem a <> None.
Proof.
intros ly S W mem md b m HAR Hin Hm a Ha.
assert (Hrq : req_size m = m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
destruct (Z_lt_le_dec a (b + m)) as [Hlt | Hge].
- destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & _ & _ & _ & Hpres & _).
  apply (aview_some_of_apresent tfibsegs). exact (proj1 (Hpres a ltac:(lia))).
- destruct HAR as (M & _).
  apply In_ablocks in Hin as (k & Hk & Hst & Hu & Hn).
  pose proof (chunk_facts B ly S _ k M Hk) as (_ & _ & Hb16 & Huser & _ & _ & Hreq & Hext & _).
  rewrite Hn, Hrq in Hext.
  assert (Hcn : ck_n k = m) by (unfold ck_n; rewrite Hn; exact Hrq).
  pose proof (rdp_extent_mod8 k ltac:(lia)) as Hx8.
  pose proof (rdp_word_end_le (b + m - 1) (ck_base B ly k) (ck_extent k) Hb16 Hx8 ltac:(lia)) as Hend.
  pose proof (am_junk B ly S _ M) as HJ. rewrite Forall_forall in HJ.
  specialize (HJ (aoff (sptr_exp (ck_beg k)) (ck_rz k + ck_n k), ck_extent k - ck_rz k - ck_n k)).
  unfold range_vis in HJ. cbn [fst snd] in HJ.
  assert (NSH : forall e', sptr_exp (ck_beg k) <> ASh e') by (intros e'; destruct (ck_beg k); cbn; discriminate).
  rewrite (aeval_aoff B ly (sptr_exp (ck_beg k)) (ck_rz k + ck_n k) NSH) in HJ.
  assert (Eb : aeval B ly (sptr_exp (ck_beg k)) = ck_base B ly k) by reflexivity.
  replace a with (aeval B ly (sptr_exp (ck_beg k)) + (ck_rz k + ck_n k) + (a - (b + m))) by lia.
  apply HJ; [|lia].
  unfold ajunk. apply in_cons. apply in_cons.
  apply in_or_app; right. apply in_or_app; right. apply in_or_app; left.
  apply in_flat_map. exists k. split; [exact Hk|].
  unfold chunk_junk. cbv zeta.
  apply in_or_app; right. apply in_or_app; right. apply in_or_app; right. apply in_eq.
Qed.

(* ---- a caller's C string across a program call (G5 FMW_kitS.v cstr_ok_kept; cstr_kept's image arm is
   suffix-closed, hdesign cce35be4cf7) ---- *)
Lemma rdp_word_end_mono : forall x y, x <= y -> x - x mod 8 + 8 <= y - y mod 8 + 8.
Proof.
intros x y H. pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. pose proof (Z.div_mod y 8 ltac:(lia)) as Dy.
pose proof (Z.mod_pos_bound x 8 ltac:(lia)). pose proof (Z.mod_pos_bound y 8 ltac:(lia)).
assert (x / 8 <= y / 8) by (apply Z.div_le_mono; lia). lia.
Qed.
Lemma rdp_cstr_kept_blk : forall STK sp0 FP ly S W mem md own ly' S' W' mem' md' k p l b m,
  ajournal tfibsegs B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
  In (b, m) (ablocks B ly S) -> In (b, m) (ablocks B ly' S') -> b <= p -> p + Z.of_nat (length l) + 1 <= b + m ->
  (forall a, p <= a < p + Z.of_nat (length l) + 1 -> ~ inFP FP a) ->
  cstr_ok tfibsegs W mem p l -> cstr_ok tfibsegs W' mem' p l.
Proof.
intros STK sp0 FP ly S W mem md own ly' S' W' mem' md' k p l b m HJ Hin Hin' Hb Hbm HnF
  ((Hg & Hnz) & H4096 & Hcl & H32 & Ham & Hra & Hhv & Htl).
pose proof HJ as (HAR' & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
assert (Hm : 0 < m) by lia.
assert (Hrq : req_size m = m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
split; [split; [|exact Hnz]|].
{ apply (garr8_frame tfibsegs _ _ p (l ++ [0]) Hg). intros a Ha. rewrite length_app in Ha. cbn [length] in Ha.
  apply (mbyte_of_aview tfibsegs). replace a with (b + (a - b)) by lia.
  apply (F2 b m (a - b) Hin Hin'); [rewrite Hrq; lia | replace (b + (a - b)) with a by lia; apply HnF; lia]. }
split; [exact H4096|]. split; [exact Hcl|]. split; [exact H32|]. split; [exact Ham|].
split.
{ apply (range_addressable_of_block tfibsegs B LAWS ly' S' W' mem' md' b m p _ HAR' Hin' Hb). rewrite Hrq. lia. }
split.
{ destruct (al_shadow _ _ LAWS ly' S' W' mem' md' b m HAR' Hin') as (_ & Hhv').
  apply (rdp_shadow_hull_vis_sub _ b (req_size m) p _ Hhv' Hb); rewrite ?Hrq; lia. }
intros a Ha. apply (rdp_block_tail_vis ly' S' W' mem' md' b m HAR' Hin' Hm).
pose proof (rdp_word_end_mono (p + Z.of_nat (length l)) (b + m - 1) ltac:(lia)). lia.
Qed.
Lemma rdp_cstr_kept : forall STK sp0 FP ly S W mem md own ly' S' W' mem' md' k p l,
  fm_img_facts tfibsegs B ->
  ajournal tfibsegs B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
  (forall x, In x (ablocks B ly S) -> In x (ablocks B ly' S')) ->
  (forall a, inFP FP a -> in_img tfibsegs a) ->
  arodata_okP tfibsegs FM_RLO FM_RHI B (aview tfibsegs (w_H W') mem') ->
  cstr_kept B ly S p l -> cstr_ok tfibsegs W mem p l -> cstr_ok tfibsegs W' mem' p l.
Proof.
intros STK sp0 FP ly S W mem md own ly' S' W' mem' md' k p l IMG HJ Hinc HFP HRO' Hk Hc.
pose proof HJ as (HAR' & _).
destruct Hk as [(b & m & Hin & Hb & Hbm) | (p0 & l0 & k0 & Hsrc & Hk0 & -> & ->)].
- apply (rdp_cstr_kept_blk STK sp0 FP ly S W mem md own ly' S' W' mem' md' k p l b m HJ Hin (Hinc _ Hin) Hb Hbm);
    [|exact Hc].
  intros a Ha Hf. apply (blk_img tfibsegs B LAWS ly' S' W' mem' md' b m a HAR' (Hinc _ Hin)); [|exact (HFP a Hf)].
  assert (req_size m = m) as -> by (unfold req_size; destruct (Z.eqb_spec m 0); lia). lia.
- apply rdp_cstr_suffix; [|exact Hk0].
  destruct (IMG ly' S' W' mem' md' HAR' HRO') as (_ & _ & _ & HS & HF).
  destruct Hsrc as [Hro | (ps & Hf & ->)].
  + exact (proj1 (proj1 (Forall_forall _ _) HS (p0, l0) Hro)).
  + exact (proj1 (HF p0 ps Hf)).
Qed.
Lemma rdp_cstr_kept_kept : forall ly S ly' S' p l,
  (forall x, In x (ablocks B ly S) -> In x (ablocks B ly' S')) ->
  cstr_kept B ly S p l -> cstr_kept B ly' S' p l.
Proof.
intros ly S ly' S' p l Hinc [(b & m & Hin & H1 & H2) | Himg].
- left. exists b, m. split; [exact (Hinc _ Hin) | split; assumption].
- right. exact Himg.
Qed.

(* ---- the relro view and fm's statics footprint (G6 FMW_K.v) ---- *)
Lemma rdp_pstat_closed : ~ YI16.sink_open_fp FM_PSTAT_FP.
Proof.
intros (r & Hr & Ha). cbv [FM_PSTAT_FP In] in Hr.
repeat (destruct Hr as [<-|Hr]; [cbn [fst snd] in Ha; lia|]). destruct Hr.
Qed.
Lemma rdp_roP_img : forall a, in_roP tfibsegs FM_RLO FM_RHI a -> in_img tfibsegs a.
Proof.
intros a [(s & Hs & _ & Hr) | Hr]; [exists s; split; [exact Hs | exact Hr]|].
apply (rdp_img_rng FM_RLO FM_RHI a Hr). vm_compute. reflexivity.
Qed.
Lemma rdp_pstat_not_roP : forall a, in_roP tfibsegs FM_RLO FM_RHI a -> ~ inFP FM_PSTAT_FP a.
Proof.
intros a Hro (r & Hr & Ha).
assert (Hb : forallb (fun r : Z * Z =>
  forallb (fun s => seg_writable s || (snd r <=? Z.of_N (seg_base s)) || (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? fst r))
    tfibsegs && ((snd r <=? FM_RLO) || (FM_RHI <=? fst r))) FM_PSTAT_FP = true) by (vm_compute; reflexivity).
pose proof (proj1 (forallb_forall _ _) Hb r Hr) as H. apply andb_prop in H as [Hs Hrl].
destruct Hro as [(s & Hin & Hw & Hsr) | Hr2].
- pose proof (proj1 (forallb_forall _ _) Hs s Hin) as Hq. cbv beta in Hq. rewrite Hw in Hq. cbn [orb] in Hq.
  apply Bool.orb_true_iff in Hq as [Hq|Hq]; apply Z.leb_le in Hq; lia.
- apply Bool.orb_true_iff in Hrl as [Hq|Hq]; apply Z.leb_le in Hq; lia.
Qed.
Lemma rdp_arodata_kept : forall STK sp0 ly S W mem md own ly' S' W' mem' md' k,
  ajournal tfibsegs B STK sp0 FM_PSTAT_FP ly S W mem md own ly' S' W' mem' md' k ->
  arodata_okP tfibsegs FM_RLO FM_RHI B (aview tfibsegs (w_H W) mem) ->
  arodata_okP tfibsegs FM_RLO FM_RHI B (aview tfibsegs (w_H W') mem').
Proof.
intros STK sp0 ly S W mem md own ly' S' W' mem' md' k HJ HR a Ha Ho He.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
rewrite (F3 a (rdp_roP_img a Ha) Ho He (rdp_pstat_not_roP a Ha) (fp_spares_closed FM_PSTAT_FP a rdp_pstat_closed)).
exact (HR a Ha Ho He).
Qed.
Lemma rdp_arodata_unp : forall (W : world tfibsegs) h m, 0 <= h -> h + 16 <= kHighMemEnd ->
  arodata_okP tfibsegs FM_RLO FM_RHI B (aview tfibsegs (w_H W) (unpoison [(h, 16)] m)) ->
  arodata_okP tfibsegs FM_RLO FM_RHI B (aview tfibsegs (w_H W) m).
Proof.
intros W h m H0 H1 HR a Ha Ho He. pose proof (g3_in_roP_low a Ha) as Hl.
rewrite <- (rdp_aview_unp (w_H W) h m a H0 H1); [exact (HR a Ha Ho He) | unfold kLowMemEnd in Hl; lia
  | left; unfold SHADOW_OFF, kLowMemEnd in *; lia].
Qed.

(* ---- a kept string and a fresh block ---- *)
Lemma rdp_new_notin : forall ly S lyc Sc Wc memc mdc b0 n0,
  AR tfibsegs B lyc Sc Wc memc mdc -> ablocks B lyc Sc = ablocks B ly S ++ [(b0, n0)] ->
  ~ In (b0, n0) (ablocks B ly S).
Proof.
intros ly S lyc Sc Wc memc mdc b0 n0 HAR Eab Hin. apply in_split in Hin as (l1 & l2 & El).
assert (E2 : ablocks B lyc Sc = l1 ++ (b0, n0) :: l2 ++ (b0, n0) :: []) by (rewrite Eab, El, <- app_assoc; reflexivity).
pose proof (sep_blocks_pos tfibsegs B LAWS lyc Sc Wc memc mdc (b0, n0) (b0, n0) l1 l2 [] HAR E2) as D.
unfold zdisjoint, block_rng in D. cbn [fst snd] in D. pose proof (req_size_pos n0) as Rq.
destruct (al_blocks _ _ LAWS _ _ _ _ _ b0 n0 HAR ltac:(rewrite Eab; apply in_or_app; right; left; reflexivity))
  as (_ & _ & _ & _ & _ & _ & Hn0). specialize (Rq ltac:(lia)). lia.
Qed.
Lemma rdp_kept_disj : forall ly S lyc Sc Wc memc mdc p l b0 n0,
  AR tfibsegs B lyc Sc Wc memc mdc -> ablocks B lyc Sc = ablocks B ly S ++ [(b0, n0)] -> 0 < n0 ->
  cstr_kept B ly S p l ->
  forall x, p <= x <= p + Z.of_nat (length l) -> ~ (b0 <= x < b0 + n0).
Proof.
intros ly S lyc Sc Wc memc mdc p l b0 n0 HAR Eab Hn0 Hk x Hx Hb.
assert (Hrq0 : req_size n0 = n0) by (unfold req_size; destruct (Z.eqb_spec n0 0); lia).
assert (Hin0 : In (b0, n0) (ablocks B lyc Sc)) by (rewrite Eab; apply in_or_app; right; left; reflexivity).
destruct Hk as [(b & m & Hin & H1 & H2) | (p0 & l0 & k & Hsrc & Hk & -> & ->)].
- apply in_split in Hin as (l1 & l2 & El).
  assert (E2 : ablocks B lyc Sc = l1 ++ (b, m) :: l2 ++ (b0, n0) :: []) by (rewrite Eab, El, <- app_assoc; reflexivity).
  pose proof (sep_blocks_pos tfibsegs B LAWS lyc Sc Wc memc mdc (b, m) (b0, n0) l1 l2 [] HAR E2) as D.
  unfold zdisjoint, block_rng in D. cbn [fst snd] in D.
  assert (req_size m = m) as Hrq by (unfold req_size; destruct (Z.eqb_spec m 0); lia). lia.
- pose proof (rdp_ro_bounds p0 l0 Hsrc) as [R1 R2]. rewrite length_skipn in Hx.
  apply (blk_img tfibsegs B LAWS lyc Sc Wc memc mdc b0 n0 x HAR Hin0); [lia|].
  apply rdp_img_ro. lia.
Qed.
(* a block holds no image byte, so it misses a range of image bytes as a whole *)
Lemma rdp_blk_img_rng : forall ly S W mem md b n c len, AR tfibsegs B ly S W mem md -> In (b, n) (ablocks B ly S) ->
  (forall x, c <= x < c + len -> in_img tfibsegs x) -> 0 < len ->
  forall d m, 0 < m -> b <= d -> d + m <= b + req_size n -> d + m <= c \/ c + len <= d.
Proof.
intros ly S W mem md b n c len HAR Hin Hc Hlen d m Hm0 Hd Hm.
destruct (Z_le_gt_dec (d + m) c) as [H1|H1]; [left; exact H1|].
destruct (Z_le_gt_dec (c + len) d) as [H2|H2]; [right; exact H2|].
exfalso. apply (blk_img tfibsegs B LAWS ly S W mem md b n (Z.max d c) HAR Hin); [lia|]. apply Hc. lia.
Qed.

(* ---- readings' journal at its entry (window [sp - STK_readings, sp + 16)) ---- *)
Lemma rdp_jinit : forall CTX cx, rd_base B CTX cx ->
  ajournal tfibsegs B (STK_readings + 16) (cx_sp cx + 16) FM_PSTAT_FP (cx_ly cx) (cx_S cx) (cx_W cx) (cx_mem cx) (cx_md cx)
    [] (cx_ly cx) (cx_S cx) (cx_W cx) (cx_mem cx) (cx_md cx) 0.
Proof.
intros CTX cx HB.
destruct HB as (HAN & _ & _ & _ & _ & _ & Hpr16 & Htop16 & _).
pose proof HAN as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
unfold cx_sp in *.
split; [exact HAR|]. split; [apply layout_le_refl|]. split; [lia|]. split; [apply wle_refl|]. split; [apply aos_step_refl|].
split; [reflexivity|]. split; [lia|]. split; [lia|].
split; [intros; reflexivity|]. split; [intros; reflexivity|]. split; [intros; reflexivity|]. split; [intros; reflexivity|].
split; [intros p n i H1 H2; exfalso; exact (H2 H1)|].
split.
{ intros a Ha. destruct (Z_lt_le_dec a (spZ (cx_regs cx))); [apply Hpres; lia | apply Hpr16; lia]. }
split.
{ unfold astk_ok. split; [rewrite Z.add_mod, Hal16 by lia; reflexivity|]. repeat split; lia. }
split; [intros; reflexivity | exact HQT].
Qed.

(* ---- a write inside the poison window: the journal over the unpoisoned view ---- *)
Lemma rdp_aj_write_U : forall STK sp0 FP ly S W mem md own lyc Sc Wc U memc mdc k memc' mdc' (Wr : Z -> Prop),
  ajournal tfibsegs B STK sp0 FP ly S W mem md own lyc Sc Wc (unpoison U memc) mdc k ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview tfibsegs (w_H Wc) memc' a = aview tfibsegs (w_H Wc) memc a) ->
  (forall a, apresent (w_H Wc) memc a -> apresent (w_H Wc) memc' a) ->
  same_but_materialized mdc mdc' ->
  (forall a, Wr a -> awr_byte tfibsegs B STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) ->
  AR tfibsegs B lyc Sc Wc (unpoison U memc') mdc' ->
  ajournal tfibsegs B STK sp0 FP ly S W mem md own lyc Sc Wc (unpoison U memc') mdc' k.
Proof.
intros STK sp0 FP ly S W mem md own lyc Sc Wc U memc mdc k memc' mdc' Wr HJ Heq Hpr Hsame HW HAR'.
pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HQT).
eapply (ajournal_after_write tfibsegs B LAWS g3_segs_low STK sp0 FP ly S W mem md own lyc Sc Wc (unpoison U memc) mdc k
  (unpoison U memc') mdc' Wr Sc own HJ).
- intros a Ha HWa. destruct (in_ush U (bv_unsigned (Z_to_bv 64 a))) eqn:E.
  + apply aview_unpoison_in. exact E.
  + rewrite !aview_unpoison_out by exact E. exact (Heq a Ha HWa).
- intros a Hp. destruct (in_ush U (bv_unsigned (Z_to_bv 64 a))) eqn:E.
  + destruct Hp as [Hh _]. split; [exact Hh|]. exists (Z_to_bv 8 0). apply unpoison_in. exact E.
  + apply (rdp_apresent_unp _ U memc' a E). apply Hpr. apply (rdp_apresent_unp _ U memc a E). exact Hp.
- exact Hsame.
- intros a Ha. left. exact (HW a Ha).
- exact HAR'.
- reflexivity.
- reflexivity.
- lia.
- exact Hfrs.
- exact HQT.
Qed.

(* ---- a runtime call inside the window: ecall_preU_k from the journal ---- *)
Lemma rdp_ecall_preU_k : forall STK sp0 FP ly S W0 mem md own lyc Sc W h memc mdc k regsc (o : Z) STKr,
  ajournal tfibsegs B STK sp0 FP ly S W0 mem md own lyc Sc W (unpoison [(h, 16)] memc) mdc k ->
  0 <= h -> h + 16 <= kHighMemEnd ->
  upoison_ok B lyc Sc [(h, 16)] -> upoisoned tfibsegs W memc [(h, 16)] ->
  spZ regsc = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK <= STKr -> STKr - o <= STK ->
  YK0s.ret_ok (getr regsc 1) -> getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
  ecall_preU_k tfibsegs B STKr lyc Sc [(h, 16)] W regsc memc mdc.
Proof.
intros STK sp0 FP ly S W0 mem md own lyc Sc W h memc mdc k regsc o STKr HJ H0 H1 Hok Hpo Hsp Hal Hneg Hes Hbud Hra Hgp Htp.
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstatic & _).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (ESTACK = 4096) as HE4 by reflexivity.
split; [split; [|split; [exact Hok | exact Hpo]]|].
- exact (ecall_pre_at tfibsegs B STK sp0 FP ly S W0 mem md own lyc Sc W _ mdc k regsc o HJ Hsp Hal Hneg
    ltac:(lia) Hra Hgp Htp).
- split; [rewrite Eslo; exact Hceil|]. split; [rewrite Eslo, Hsp; lia|].
  intros a Ha. rewrite Hsp in Ha.
  apply (proj1 (rdp_apresent_unp _ [(h, 16)] memc a ltac:(rewrite unsigned_lit_small by lia;
    apply rdp_ush_app; [lia | lia | right; lia]))).
  apply Hpres. lia.
Qed.

(* the post of a call that writes nothing but its stack window, inside the window (strstr) *)
Lemma rdp_aj_roU : forall pc STKr (R : Z -> Prop) h,
  forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k (o : Z) raw,
  ajournal tfibsegs B STK sp0 FP ly S W0 mem md own lyc Sc W (unpoison [(h, 16)] memT) mdc k ->
  0 <= h -> h + 16 <= kHighMemEnd -> upoison_ok B lyc Sc [(h, 16)] -> upoisoned tfibsegs W memT [(h, 16)] ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK <= STKr -> STKr - o <= STK ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
  (ecall_preU_k tfibsegs B STKr lyc Sc [(h, 16)] W regsT memT mdc ->
   SRr tfibsegs W (cfg_at tfibsegs pc regsT memT mdc) (rt_post_roU tfibsegs B STKr lyc Sc [(h, 16)] W regsT memT mdc R)) ->
  SRr tfibsegs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom tfibsegs)) mdc)
    (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2 (v : Z),
       c2 = mkCfg (mkst regs2 raw mem2 (seg_rom tfibsegs)) md2 /\
       ajournal tfibsegs B STK sp0 FP ly S W0 mem md own lyc Sc W (unpoison [(h, 16)] mem2) md2 k /\
       upoisoned tfibsegs W mem2 [(h, 16)] /\
       aregs_preserved regsT regs2 /\ getr regs2 10 = w64 v /\ 0 <= v < 2 ^ 64 /\ R v /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - STKr <= a < sp0 + o) ->
          aview tfibsegs (w_H W) mem2 a = aview tfibsegs (w_H W) memT a) /\
       (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
intros pc STKr R h W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o raw HJ H0 H1 Hok Hpo
  Hsp' Hal Hneg Hes Hbud Hgp Htp Hra Hraw HC.
assert (HPK : ecall_preU_k tfibsegs B STKr lyc Sc [(h, 16)] W regsT memT mdc).
{ apply (rdp_ecall_preU_k STK sp0 FP ly S W0 mem md own lyc Sc W h memT mdc k regsT o STKr HJ H0 H1 Hok Hpo
    Hsp' Hal Hneg Hes Hbud); [rewrite Hra; exact Hraw | exact Hgp | exact Htp]. }
eapply SRr_mono; [exact (HC HPK)|].
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HAR2 & HPo2 & HP & Hsame & Hres & Hv & HR & Hfr & Hpres2).
rewrite Hsp' in Hfr.
split; [reflexivity|]. exists regs2, mem2, md2, v.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ apply (rdp_aj_write_U STK sp0 FP ly S W0 mem md own lyc Sc W [(h, 16)] memT mdc k mem2 md2
    (fun a => sp0 + o - STKr <= a < sp0 + o) HJ); [exact Hfr | exact Hpres2 | exact Hsame | | exact HAR2].
  intros a Ha. left. left. lia. }
split; [exact HPo2|]. split; [exact HP|]. split; [exact Hres|]. split; [exact Hv|]. split; [exact HR|].
split; [exact Hfr | exact Hpres2].
Qed.

(* the snprintf call inside the window: it writes its stack window and the destination, a block made after the
   journal's entry *)
Lemma rdp_aj_snU : forall pc h (d : Z) (out : list Z) b0 n0,
  forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k (o : Z) raw,
  ajournal tfibsegs B STK sp0 FP ly S W0 mem md own lyc Sc W (unpoison [(h, 16)] memT) mdc k ->
  0 <= h -> h + 16 <= kHighMemEnd -> upoison_ok B lyc Sc [(h, 16)] -> upoisoned tfibsegs W memT [(h, 16)] ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> STK_RT_PRINTF - o <= STK ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
  In (b0, n0) (ablocks B lyc Sc) -> ~ In (b0, n0) (ablocks B ly S) -> b0 <= d ->
  d + Z.of_nat (length out) + 1 <= b0 + req_size n0 ->
  (ecall_preU_k tfibsegs B STK_RT_PRINTF lyc Sc [(h, 16)] W regsT memT mdc ->
   SRr tfibsegs W (cfg_at tfibsegs pc regsT memT mdc)
    (fun W' c' => W' = W /\ exists regs' mem' md',
       c' = cfg_at tfibsegs (raZ regsT) regs' mem' md' /\
       AR tfibsegs B lyc Sc W (unpoison [(h, 16)] mem') md' /\ upoisoned tfibsegs W mem' [(h, 16)] /\
       aregs_preserved regsT regs' /\ same_but_materialized mdc md' /\
       getr regs' 10 = w64 (Z.of_nat (length out)) /\
       bytes_at tfibsegs W mem' d (out ++ [0]) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + Z.of_nat (length out) + 1) ->
          ~ (spZ regsT - STK_RT_PRINTF <= a < spZ regsT) -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) memT a) /\
       (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem' a))) ->
  SRr tfibsegs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom tfibsegs)) mdc)
    (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
       c2 = mkCfg (mkst regs2 raw mem2 (seg_rom tfibsegs)) md2 /\
       ajournal tfibsegs B STK sp0 FP ly S W0 mem md own lyc Sc W (unpoison [(h, 16)] mem2) md2 k /\
       upoisoned tfibsegs W mem2 [(h, 16)] /\
       aregs_preserved regsT regs2 /\ getr regs2 10 = w64 (Z.of_nat (length out)) /\
       bytes_at tfibsegs W mem2 d (out ++ [0]) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + Z.of_nat (length out) + 1) ->
          ~ (sp0 + o - STK_RT_PRINTF <= a < sp0 + o) -> aview tfibsegs (w_H W) mem2 a = aview tfibsegs (w_H W) memT a) /\
       (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
intros pc h d out b0 n0 W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o raw HJ H0 H1 Hok Hpo
  Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hb0 Hnb0 Hd1 Hd2 HC.
assert (HPK : ecall_preU_k tfibsegs B STK_RT_PRINTF lyc Sc [(h, 16)] W regsT memT mdc).
{ apply (rdp_ecall_preU_k STK sp0 FP ly S W0 mem md own lyc Sc W h memT mdc k regsT o STK_RT_PRINTF HJ H0 H1 Hok Hpo
    Hsp' Hal Hneg ltac:(unfold STK_RT_PRINTF, ESTACK; lia) Hbud); [rewrite Hra; exact Hraw | exact Hgp | exact Htp]. }
eapply SRr_mono; [exact (HC HPK)|].
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HPo2 & HP & Hsame & Hres & Hby & Hfr & Hpres2).
rewrite Hsp' in Hfr.
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ apply (rdp_aj_write_U STK sp0 FP ly S W0 mem md own lyc Sc W [(h, 16)] memT mdc k mem2 md2
    (fun a => (d <= a < d + Z.of_nat (length out) + 1) \/ (sp0 + o - STK_RT_PRINTF <= a < sp0 + o)) HJ).
  - intros a Ha Hn. apply Hfr; [exact Ha | intros Hx; apply Hn; left; exact Hx | intros Hx; apply Hn; right; exact Hx].
  - exact Hpres2.
  - exact Hsame.
  - intros a [Ha|Ha].
    + left. right. right. left. exists b0, n0. split; [exact Hb0|]. split; [exact Hnb0|]. lia.
    + left. left. lia.
  - exact HAR2. }
split; [exact HPo2|]. split; [exact HP|]. split; [exact Hres|]. split; [exact Hby|].
split; [exact Hfr | exact Hpres2].
Qed.

(* ---- symbolic states at the walk's resumption points ---- *)
Lemma rdp_SOff0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof.
intros E n. apply bv_eq. rewrite denot_SOff, Z.add_0_r. apply zcanon_id. unfold M64. apply u64_range.
Qed.
Lemma rdp_pres : forall regs regs' (r : bv 5), aregs_preserved regs regs' -> acallee_saved (bv_unsigned r) ->
  getr regs' r = getr regs r.
Proof. intros regs regs' r HP Hc. pose proof (HP _ Hc) as E. rewrite Z_to_bv_bv_unsigned in E. exact E. Qed.
End k.

(* the state after a call when the next stretch reads no memory: every register its own atom *)
Definition rdp_ssn (pc : Z) : sstate := mkSS pc sr_atoms [] None (mkFacts [] [] []).
(* the state after fuzz_free: the frame's locals [F, F + 0x68) writable (B's stores at 0x81f44 .. 0x81fa0) *)
Definition rdp_ss5 : sstate :=
  mkSS RD_C5 sr_atoms [YP09.mkRegion (Some 2%nat) 0 0x68 0 0x68 []] None (mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] []).

Section r. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Lemma rdp_ssn_ok : forall (W : world tfibsegs) regs extra mem pc,
  st_ok tfibsegs (Ereg regs extra) (rdp_ssn pc) (restrict (w_H W) (mkst regs (Z_to_bv 64 pc) mem (seg_rom tfibsegs))).
Proof.
intros W regs extra mem pc. rewrite restrict_mkst_fx. unfold rdp_ssn. apply (entry_st_ok_full tfibsegs).
- apply regs_ok_Ereg.
- reflexivity.
- constructor.
- cbn. tauto.
- split; [exact I | split; exact I].
Qed.
Lemma rdp_ss5_ok : forall (W : world tfibsegs) regs extra mem (F : Z),
  getr regs 2 = w64 F -> 2 ^ 46 <= F <= 2 ^ 47 - 0x68 -> F mod 16 = 0 ->
  (forall a, F <= a < F + 0x68 -> apresent (w_H W) mem a) ->
  st_ok tfibsegs (Ereg regs extra) rdp_ss5 (restrict (w_H W) (mkst regs (Z_to_bv 64 RD_C5) mem (seg_rom tfibsegs))).
Proof.
intros W regs extra mem F R2 HF HF16 Hpr. rewrite restrict_mkst_fx. unfold rdp_ss5. apply (entry_st_ok_full tfibsegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- assert (E2 : bv_unsigned (ew (Ereg regs extra) 2) = F).
  { rewrite (ew_Ereg_nat regs extra 2 2%bv eq_refl), R2. apply unsigned_lit_small. lia. }
  constructor; [|constructor]. unfold region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E2.
  split; [lia|]. split; [lia|]. split; [|constructor].
  intros o Ho. apply (apresent_writable tfibsegs). apply Hpr. lia.
- cbn. tauto.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite (ew_Ereg_nat regs extra 2 2%bv eq_refl), R2. unfold w64. rewrite unsigned_lit_small by lia.
  change (2 ^ 4) with 16. split; [|exact I]. split; [lia|]. split; [exact HF16 | lia].
Qed.
End r.
