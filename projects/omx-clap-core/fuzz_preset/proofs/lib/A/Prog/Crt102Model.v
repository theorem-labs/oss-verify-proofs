(* fuzz_preset, walk of check_round_trip on the #102 pins, part MODEL: every
   IMAGE-FREE, ALLOCATOR-FREE fact the walk needs about the pure models, so that no segment proof re-derives one.
   Nothing here mentions a pc, a register, a listing, a journal, ARx or the ledger: each lemma is over PjTree /
   PjGrammar / PjRoundTrip / WriterSpec / WriterValue / WriterApp / PjWriteHyp, over the model functions of the contract
   texts (PRH_FnCheck.v ck_*, LIVE_*, RQ_*, RQA_*, RQW, FR_*; PRH_FnPj.v / PRH_FnWriter.v / PRH_FnTx.v rooms and the
   writer's prhWriter_putN), or over plain integers and lists the walk instantiates (blocks_bytes S, frames S, g_count).
   Section 9 alone reads the reader's tree predicates (PRH_Reader.v pj_nodeR / pj_hdrR / rd_u64, over any segs and
   memory, still no image and no allocator): the copy's header cap against the model's block list.

   INPUTS OF RECORD (taken BY PATH):
   - pins: A' asan 1be0f53d96cb9d6c (unstripped twin bff8519bbe3ea0e4), B' asan-ubsan d663f82d7f488d30 (twin
     c90d4fa54d43160b). No fact here depends on either image.
   - base: its first commit 3971724b617 (= commit
     c52965a03881 (the #102 pins) + the contract texts at 3438f3406f33 + the engine whole set at
     459129c18903; then 0c9201c7d87d / d8962d407fde, which re-take the contract texts by path
     from 00b50c5745fb: lib/A/PRH_FnCheck.v 6f6bc83d7420, PRH_FnPj.v 5798c50485c7, PRH_FnWriter.v
     6a0afeb80142, PRH_FnTx.v c798df739d78; lib/A/PRH_Base.v stays 016934fdc1af). The model definitions this file
     reads (ck_*, LIVE_*, RQ_*, RQA_*, RQW, FR_*, LIVE_pj_set, LIVE_pj_string, prhPj_set_trace, LIVE_pj_write,
     prhWriter_put1 / putN / k, LIVE_tx) are byte-identical in 37d8e4d0072e and 6f6bc83d7420 (and in the PRH_FnPj /
     PRH_FnWriter / PRH_FnTx pairs).
   - listings of record (none is read here): lib/A/Listing_prog.v 1ab147923c5d, lib/A/PAImg_prog.v 47eeb54e93be,
     lib/B/Listing_prog.v 8bcc2c9e7809, lib/B/PAImg_prog.v 4392ab2c09ba, lib/Reusable/YPsym.v b6f5a85d234d.
   - the segment cut: the walk's internal file DESIGN.md (the arm table C1, C2, C3, C4a, C4c, C4).
   - the source: fuzz_preset.c (836 lines, sha256 c7b4007bba7bab3e),
     round_trip_rewrite new:713-768, check_round_trip new:771-780.
   - structure copied from the closed S10 walk's lib/A/Prog (S10TxKit.v).
   Cited: the pure model files' own lemmas (lib/Spec PjTree / PjGrammar / PjRoundTrip: wf_good, read_json, G9,
   G9_calls, G9_trace, G7_1, G7_2, G7_4, G12_1, depth_member, wv_obj, wv_arr, wstr_eq, good_arr, good_obj,
   tblocks_read; lib/Spec/PjReqBound.v jr_req_bound_56; lib/Prog/ReaderRes.v lsz_counts; lib/Spec/PresetReqAtNoMiss.v
   f949715d7a12 ncap_eq; stdpp's Z_to_bv_unsigned, bv_wrap_small). lib/Spec/PresetReqAt.v (379c33e9e482) is read for
   its definitions (MOD_KEY, MOD_VAL, copy_set, wcalls, ncap, arrz, HEAD), PresetReqAtNoMiss for tblk / capf. No lemma of a
   released proof of a FUNCTION (lib/Prog/<fn>*.v, lib/U) is cited: the rewrite's model facts (cm_at, cm_set_*,
   cm_crt_wlen, cm_set_depth) are written new after lib/Prog/check_round_trip_m.v's statements, and the writer-run
   facts (cm_dbl_ge .. cm_gcalls_le, cm_wput, cm_wput_fail) after commit 841830f5dcb
   lib/A/Prog/H5RttS1.v's (rt1_dbl_ge .. rt1_wfail), neither Required.

   NUMERALS (no ADDRESS literal occurs in this file):
   - WORD: 6 (PjTree.tag of an object, PJ_OBJECT), 4 (PjTree.tag of a string, PJ_STRING); 2 ^ 62, 2 ^ 64, 2 ^ 64 - 1
     (the counter ranges of the texts: g_count is a size_t).
   - LENGTH: 10 (length ck_MOD_AT, "modifiedAt"), 20 (length ck_STAMP, "2026-10-25T00:00:00Z"), 12 / 22 (their
     rendered pieces with quotes), 3 / 2 (the pretty indent at depth 1 and the pretty separator), 3 * 2 ^ 20 (the
     text's input bound), 2 ^ 28 (prhWriter_WMAX, round_trip_text's wlen premise), 2 ^ 40 (parse_noting's len
     premise), 2 ^ 30 (parse_noting's maxrun premise), 4096 (newcap's first page), 8 / 56 (the keys / kids cell sizes
     of cap2R), 64 (ck_FRAMES_CAP), 16384 (fs_frames 0 = 2 ^ (kStackSizeLog - 6)).
   - DERIVED: 11 / 21 (the key's and the stamp's strdup requests, length + 1), 40 (the most bytes the rewrite adds to
     the pretty text: comma 1 + indent 3 + key 12 + separator 2 + stamp 22 - (the closing indent the members had
     already, 0 or 1)), 3 (the most allocations pj_set makes: two grow reallocs and the key's strdup), 1 (pj_string's
     strdup), 2 ^ 30 (the counter slack of the text, `cnt < 2 ^ 62 - 2 ^ 30`), 3 / 56 / 54 (the text's wlen factors),
     2 (the reader's calls per byte, PjGrammar.G7_4), 36 (the most bytes the rewrite adds to the compact text: comma
     1 + key 12 + separator 1 + stamp 22), 56 / 448 (PjReqBound.jr_req_bound_56's request bound 56 |x| + 448).
   - WORD (more): 2 ^ 32 (the block-size bound of PRH_FnWriter.v prhWriter_tree_vis), 16 (the radix of the writer's
     \u00XX escape, WriterSpec.esc / hexd), 8 / 256 (the bytes of a 64-bit word and the values of a byte,
     cm_rd_u64_det), 48 (the offset of cap in struct pj, PRH_Reader.v pj_hdrR), 6 (PJ_OBJECT in pj_hdrR's type).
   *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation Arith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YO0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG01 YGcfNames.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require
  PjTree PjGrammar PjRoundTrip PjReqBound PresetReqAt PresetReqAtNoMiss.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes WriterSpec WriterValue WriterApp PjWriteHyp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_FnPj PRH_FnTx PRH_FnWriter PRH_FnReader.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ======================================================================================================== *)
(* 0. the two strings of the rewrite                                                                          *)
(* ======================================================================================================== *)

Lemma cm_MOD_AT_len : length ck_MOD_AT = 10%nat.
Proof. reflexivity. Qed.

Lemma cm_STAMP_len : length ck_STAMP = 20%nat.
Proof. reflexivity. Qed.

Lemma cm_MOD_AT_bytes : Forall (fun b => 0 < b < 256) ck_MOD_AT.
Proof. unfold ck_MOD_AT. repeat (apply Forall_cons; [cbv beta; lia|]). apply Forall_nil. Qed.

Lemma cm_STAMP_bytes : Forall (fun b => 0 < b < 256) ck_STAMP.
Proof. unfold ck_STAMP. repeat (apply Forall_cons; [cbv beta; lia|]). apply Forall_nil. Qed.

Lemma cm_STAMP_wf : forall sm, PjRoundTrip.pj_wf sm (PjTree.JStr ck_STAMP).
Proof. intros sm. apply PjRoundTrip.wf_string. exact cm_STAMP_bytes. Qed.

(* ======================================================================================================== *)
(* 1. the type tag the body tests (T: `lw doc->type`, `bne 6`)                                                *)
(* ======================================================================================================== *)

Lemma cm_tag_range : forall t, 0 <= PjTree.tag t <= 6.
Proof. intros t. destruct t; cbn [PjTree.tag]; lia. Qed.

Lemma cm_tag_obj : forall t, PjTree.tag t = 6 -> exists ms, t = PjTree.JObj ms.
Proof.
intros t H. destruct t as [| | | txt bits | s | items | ms]; cbn [PjTree.tag] in H; try lia.
exists ms. reflexivity.
Qed.

Lemma cm_tag_nobj : forall t, PjTree.tag t <> 6 -> forall ms, t <> PjTree.JObj ms.
Proof. intros t H ms E. subst t. cbn [PjTree.tag] in H. lia. Qed.

Lemma cm_tag_of_obj : forall ms, PjTree.tag (PjTree.JObj ms) = 6.
Proof. reflexivity. Qed.

Lemma cm_tag_STAMP : PjTree.tag (PjTree.JStr ck_STAMP) = 4.
Proof. reflexivity. Qed.

Lemma cm_obj_dec : forall t, (exists ms, t = PjTree.JObj ms) \/ (forall ms, t <> PjTree.JObj ms).
Proof.
intros t. destruct t as [| | | txt bits | s | items | ms];
  try (right; intros ms' E; discriminate E).
left. exists ms. reflexivity.
Qed.

(* ======================================================================================================== *)
(* 2. the count split: ck_crt_count in the five pieces the body runs, in order                                 *)
(*    rtt(doc, 0): wcalls t false + tcalls t; rtt(doc, 1): wcalls t true + tcalls t; for an object, pj_string's *)
(*    strdup and pj_set's cset: 1 + cset; the rewrite's pj_write: wcalls (ck_crt_tree t) true; its read-back:     *)
(*    tcalls (ck_crt_tree t)                                                                                    *)
(* ======================================================================================================== *)

Lemma cm_wcalls_nonneg : forall t p, 0 <= PjWriteHyp.wcalls t p.
Proof. intros t p. unfold PjWriteHyp.wcalls. lia. Qed.

Lemma cm_tcalls_nonneg : forall t, 0 <= Z.of_nat (PjRoundTrip.tcalls t).
Proof. intros t. lia. Qed.

Lemma cm_count_obj : forall t ms cset, t = PjTree.JObj ms ->
  ck_crt_count t cset =
  (PjWriteHyp.wcalls t false + Z.of_nat (PjRoundTrip.tcalls t)) +
  (PjWriteHyp.wcalls t true + Z.of_nat (PjRoundTrip.tcalls t)) +
  (1 + cset) + PjWriteHyp.wcalls (ck_crt_tree t) true + Z.of_nat (PjRoundTrip.tcalls (ck_crt_tree t)).
Proof. intros t ms cset ->. cbv beta iota delta [ck_crt_count]. lia. Qed.

Lemma cm_count_nobj : forall t cset, (forall ms, t <> PjTree.JObj ms) ->
  ck_crt_count t cset =
  PjWriteHyp.wcalls t false + Z.of_nat (PjRoundTrip.tcalls t) +
  PjWriteHyp.wcalls t true + Z.of_nat (PjRoundTrip.tcalls t).
Proof.
intros t cset H. destruct t as [| | | txt bits | s | items | ms];
  try (cbv beta iota delta [ck_crt_count]; lia).
exfalso. exact (H ms eq_refl).
Qed.

(* the running totals after rtt(doc, 0) and rtt(doc, 1) *)
Lemma cm_cnt1_eq : forall c t, ck_cnt1 c t = c + PjWriteHyp.wcalls t false + Z.of_nat (PjRoundTrip.tcalls t).
Proof. reflexivity. Qed.

Lemma cm_cnt2_eq : forall c t, ck_cnt2 c t =
  c + PjWriteHyp.wcalls t false + Z.of_nat (PjRoundTrip.tcalls t) +
  PjWriteHyp.wcalls t true + Z.of_nat (PjRoundTrip.tcalls t).
Proof. reflexivity. Qed.

Lemma cm_cnt_obj : forall c t ms cset, t = PjTree.JObj ms ->
  c + ck_crt_count t cset =
  ck_cnt2 c t + (1 + cset) + PjWriteHyp.wcalls (ck_crt_tree t) true + Z.of_nat (PjRoundTrip.tcalls (ck_crt_tree t)).
Proof. intros c t ms cset E. rewrite (cm_count_obj t ms cset E), cm_cnt2_eq. lia. Qed.

Lemma cm_cnt_nobj : forall c t cset, (forall ms, t <> PjTree.JObj ms) -> c + ck_crt_count t cset = ck_cnt2 c t.
Proof. intros c t cset N. rewrite (cm_count_nobj t cset N), cm_cnt2_eq. lia. Qed.

(* ---- 2a. each prefix of that order lies between 0 and the whole count ---- *)

Lemma cm_pre1 : forall t cset, 0 <= cset ->
  0 <= PjWriteHyp.wcalls t false + Z.of_nat (PjRoundTrip.tcalls t) <= ck_crt_count t cset.
Proof.
intros t cset Hc. pose proof (cm_wcalls_nonneg t false). pose proof (cm_wcalls_nonneg t true).
destruct (cm_obj_dec t) as [[ms E]|N].
- rewrite (cm_count_obj t ms cset E). pose proof (cm_wcalls_nonneg (ck_crt_tree t) true). lia.
- rewrite (cm_count_nobj t cset N). lia.
Qed.

Lemma cm_pre2 : forall t cset, 0 <= cset ->
  0 <= PjWriteHyp.wcalls t false + Z.of_nat (PjRoundTrip.tcalls t) +
       (PjWriteHyp.wcalls t true + Z.of_nat (PjRoundTrip.tcalls t)) <= ck_crt_count t cset.
Proof.
intros t cset Hc. pose proof (cm_wcalls_nonneg t false). pose proof (cm_wcalls_nonneg t true).
destruct (cm_obj_dec t) as [[ms E]|N].
- rewrite (cm_count_obj t ms cset E). pose proof (cm_wcalls_nonneg (ck_crt_tree t) true). lia.
- rewrite (cm_count_nobj t cset N). lia.
Qed.

Lemma cm_pre3 : forall t ms cset, t = PjTree.JObj ms -> 0 <= cset -> forall a, 0 <= a <= 1 + cset ->
  0 <= PjWriteHyp.wcalls t false + Z.of_nat (PjRoundTrip.tcalls t) +
       (PjWriteHyp.wcalls t true + Z.of_nat (PjRoundTrip.tcalls t)) + a <= ck_crt_count t cset.
Proof.
intros t ms cset E Hc a Ha. rewrite (cm_count_obj t ms cset E).
pose proof (cm_wcalls_nonneg t false). pose proof (cm_wcalls_nonneg t true).
pose proof (cm_wcalls_nonneg (ck_crt_tree t) true). lia.
Qed.

Lemma cm_pre4 : forall t ms cset k, t = PjTree.JObj ms -> 0 <= cset ->
  0 <= k <= PjWriteHyp.wcalls (ck_crt_tree t) true ->
  0 <= PjWriteHyp.wcalls t false + Z.of_nat (PjRoundTrip.tcalls t) +
       (PjWriteHyp.wcalls t true + Z.of_nat (PjRoundTrip.tcalls t)) + (1 + cset) + k <= ck_crt_count t cset.
Proof.
intros t ms cset k E Hc Hk. rewrite (cm_count_obj t ms cset E).
pose proof (cm_wcalls_nonneg t false). pose proof (cm_wcalls_nonneg t true). lia.
Qed.

Lemma cm_pre5 : forall t ms cset j, t = PjTree.JObj ms -> 0 <= cset ->
  0 <= j <= Z.of_nat (PjRoundTrip.tcalls (ck_crt_tree t)) ->
  0 <= PjWriteHyp.wcalls t false + Z.of_nat (PjRoundTrip.tcalls t) +
       (PjWriteHyp.wcalls t true + Z.of_nat (PjRoundTrip.tcalls t)) + (1 + cset) +
       PjWriteHyp.wcalls (ck_crt_tree t) true + j <= ck_crt_count t cset.
Proof.
intros t ms cset j E Hc Hj. rewrite (cm_count_obj t ms cset E).
pose proof (cm_wcalls_nonneg t false). pose proof (cm_wcalls_nonneg t true).
pose proof (cm_wcalls_nonneg (ck_crt_tree t) true). lia.
Qed.

(* ---- 2b. the arms of the post (DESIGN's arm table), from the callees' own count conjuncts ---- *)

(* C1: rtt(doc, 0) returned 1: its r = 1 arm `cnt <= cnt' <= cnt + wcalls t false + tcalls t` *)
Lemma cm_arm_C1 : forall t cset cnt cnt', 0 <= cset ->
  cnt <= cnt' <= cnt + PjWriteHyp.wcalls t false + Z.of_nat (PjRoundTrip.tcalls t) ->
  cnt <= cnt' <= cnt + ck_crt_count t cset.
Proof. intros t cset cnt cnt' Hc H. pose proof (cm_pre1 t cset Hc). lia. Qed.

(* C2: rtt(doc, 0)'s r = 0 arm (exact), then rtt(doc, 1)'s r = 1 arm *)
Lemma cm_arm_C2 : forall t cset cnt cnt1 cnt', 0 <= cset ->
  cnt1 = cnt + PjWriteHyp.wcalls t false + Z.of_nat (PjRoundTrip.tcalls t) ->
  cnt1 <= cnt' <= cnt1 + PjWriteHyp.wcalls t true + Z.of_nat (PjRoundTrip.tcalls t) ->
  cnt <= cnt' <= cnt + ck_crt_count t cset.
Proof. intros t cset cnt cnt1 cnt' Hc E H. pose proof (cm_pre2 t cset Hc). pose proof (cm_wcalls_nonneg t false). lia. Qed.

(* C3: both r = 0 arms, t not an object: the exact count, any cset (the object term is absent) *)
Lemma cm_arm_C3 : forall t cset cnt cnt1 cnt2, (forall ms, t <> PjTree.JObj ms) ->
  cnt1 = cnt + PjWriteHyp.wcalls t false + Z.of_nat (PjRoundTrip.tcalls t) ->
  cnt2 = cnt1 + PjWriteHyp.wcalls t true + Z.of_nat (PjRoundTrip.tcalls t) ->
  cnt2 = cnt + ck_crt_count t cset.
Proof. intros t cset cnt cnt1 cnt2 N E1 E2. rewrite (cm_count_nobj t cset N). lia. Qed.

(* C4a: both r = 0 arms, an object, then a = 1 (pj_string's strdup) + pj_set's c calls (a <= 1 + cset) *)
Lemma cm_arm_C4a : forall t ms cset cnt cnt1 cnt2 a, t = PjTree.JObj ms -> 0 <= cset ->
  cnt1 = cnt + PjWriteHyp.wcalls t false + Z.of_nat (PjRoundTrip.tcalls t) ->
  cnt2 = cnt1 + PjWriteHyp.wcalls t true + Z.of_nat (PjRoundTrip.tcalls t) ->
  0 <= a <= 1 + cset ->
  cnt <= cnt2 + a <= cnt + ck_crt_count t cset.
Proof.
intros t ms cset cnt cnt1 cnt2 a E Hc E1 E2 Ha. pose proof (cm_pre3 t ms cset E Hc a Ha).
pose proof (cm_wcalls_nonneg t false). pose proof (cm_wcalls_nonneg t true). lia.
Qed.

(* C4c: then the rewrite's pj_write made k <= wcalls (ck_crt_tree t) true calls and its read-back j <=
   tcalls (ck_crt_tree t) (cm_pjw_k_le, cm_noting_calls) *)
Lemma cm_arm_C4c : forall t ms cset cnt cnt1 cnt2 k j, t = PjTree.JObj ms -> 0 <= cset ->
  cnt1 = cnt + PjWriteHyp.wcalls t false + Z.of_nat (PjRoundTrip.tcalls t) ->
  cnt2 = cnt1 + PjWriteHyp.wcalls t true + Z.of_nat (PjRoundTrip.tcalls t) ->
  0 <= k <= PjWriteHyp.wcalls (ck_crt_tree t) true ->
  0 <= j <= Z.of_nat (PjRoundTrip.tcalls (ck_crt_tree t)) ->
  cnt <= cnt2 + 1 + cset + k + j <= cnt + ck_crt_count t cset.
Proof.
intros t ms cset cnt cnt1 cnt2 k j E Hc E1 E2 Hk Hj. rewrite (cm_count_obj t ms cset E).
pose proof (cm_wcalls_nonneg t false). pose proof (cm_wcalls_nonneg t true). lia.
Qed.

(* C4 (the whole rewrite, r = 0): the exact count *)
Lemma cm_arm_C4 : forall t ms cset cnt cnt1 cnt2 cnt', t = PjTree.JObj ms ->
  cnt1 = cnt + PjWriteHyp.wcalls t false + Z.of_nat (PjRoundTrip.tcalls t) ->
  cnt2 = cnt1 + PjWriteHyp.wcalls t true + Z.of_nat (PjRoundTrip.tcalls t) ->
  cnt' = cnt2 + 1 + cset + PjWriteHyp.wcalls (ck_crt_tree t) true + Z.of_nat (PjRoundTrip.tcalls (ck_crt_tree t)) ->
  cnt' = cnt + ck_crt_count t cset.
Proof. intros t ms cset cnt cnt1 cnt2 cnt' E E1 E2 E3. rewrite (cm_count_obj t ms cset E). lia. Qed.

(* pj_set's cset: c calls, at most its trace's length, which is 1 or 3 *)
Lemma cm_set_trace_len : forall (n cap : Z) kname,
  length (PRH_FnPj.prhPj_set_trace n cap kname) = (if Z.eqb n cap then 3%nat else 1%nat).
Proof.
intros n cap kname. unfold PRH_FnPj.prhPj_set_trace. rewrite length_app.
destruct (n =? cap); reflexivity.
Qed.

Lemma cm_cset_range : forall n cap kname (c : nat), (c <= length (PRH_FnPj.prhPj_set_trace n cap kname))%nat ->
  0 <= Z.of_nat c <= 3.
Proof. intros n cap kname c H. rewrite cm_set_trace_len in H. destruct (n =? cap); lia. Qed.

(* every allocator call adds one to g_count, read mod 2 ^ 64 (PRH_FnAlloc.v prh_alloc_post); below the top it is + 1 *)
Lemma cm_inc_mod : forall c, 0 <= c < 2 ^ 64 - 1 -> (c + 1) mod 2 ^ 64 = c + 1.
Proof. intros c H. apply Z.mod_small. lia. Qed.

(* ======================================================================================================== *)
(* 3. the writer's run (PRH_FnWriter.v prhWriter_putN): g_count grows by the run's calls, at most the         *)
(*    accepting run's (wcalls), exactly those when the run ends unfailed                                       *)
(* ======================================================================================================== *)

Lemma cm_dbl_ge : forall f c need, 0 <= c -> c <= WriterSpec.dbl f c need.
Proof.
induction f as [|f IH]; intros c need Hc; cbn [WriterSpec.dbl]; [lia|].
destruct (need <=? c); [lia|]. specialize (IH (2 * c) need ltac:(lia)). lia.
Qed.

Lemma cm_dbl_reach : forall f c need, 1 <= c -> need <= c * 2 ^ Z.of_nat f -> need <= WriterSpec.dbl f c need.
Proof.
induction f as [|f IH]; intros c need Hc Hn; cbn [WriterSpec.dbl].
- change (2 ^ Z.of_nat 0) with 1 in Hn. lia.
- destruct (Z.leb_spec need c) as [H|H]; [exact H|]. apply IH; [lia|].
  rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hn by lia. lia.
Qed.

Lemma cm_newcap_reach : forall c need, 0 <= c -> need <= 2 ^ 64 -> need <= WriterSpec.newcap c need.
Proof.
intros c need Hc Hn. unfold WriterSpec.newcap. apply cm_dbl_reach.
- destruct (Z.eqb_spec c 0); lia.
- change (Z.of_nat 64) with 64. destruct (Z.eqb_spec c 0); lia.
Qed.

Lemma cm_newcap0_ge : forall need, 4096 <= WriterSpec.newcap 0 need.
Proof. intros need. unfold WriterSpec.newcap. rewrite Z.eqb_refl. apply cm_dbl_ge. lia. Qed.

Lemma cm_gc_len : forall ls x c, 0 <= x -> x + 1 <= c -> Forall (fun l => 0 <= l) ls ->
  x + fold_right Z.add 0 ls + 1 <= 2 ^ 62 ->
  Z.of_nat (length (WriterSpec.grow_calls x c ls)) <= fold_right Z.add 0 ls.
Proof.
induction ls as [|l ls IH]; intros x c Hx Hc Hf Hs; [cbn; lia|].
apply Forall_cons_iff in Hf as [Hl Hf]. cbn [WriterSpec.grow_calls fold_right] in *.
assert (Hr : 0 <= fold_right Z.add 0 ls).
{ clear -Hf. induction Hf as [|a l' Ha _ IH]; cbn [fold_right]; lia. }
destruct (Z.ltb_spec c (x + l + 1)) as [H|H].
- pose proof (cm_newcap_reach c (x + l + 1) ltac:(lia) ltac:(lia)) as Hn.
  specialize (IH (x + l) (WriterSpec.newcap c (x + l + 1)) ltac:(lia) ltac:(lia) Hf ltac:(lia)).
  cbn [length]. lia.
- specialize (IH (x + l) c ltac:(lia) ltac:(lia) Hf ltac:(lia)). lia.
Qed.

Lemma cm_lens_sum : forall P, fold_right Z.add 0 (WriterSpec.piece_lens P) = Z.of_nat (length (concat P)).
Proof.
induction P as [|bs P IH]; [reflexivity|]. unfold WriterSpec.piece_lens in *. cbn [map fold_right concat].
rewrite IH, length_app. lia.
Qed.

Lemma cm_lens_nn : forall P, Forall (fun l => 0 <= l) (WriterSpec.piece_lens P).
Proof.
intros P. unfold WriterSpec.piece_lens. apply Forall_forall. intros l Hl.
apply in_map_iff in Hl as (b & <- & _). lia.
Qed.

Lemma cm_gcalls_le : forall P, Z.of_nat (length (concat P)) + 1 <= 2 ^ 62 ->
  Z.of_nat (length (WriterSpec.grow_calls 0 0 (WriterSpec.piece_lens P))) <= Z.of_nat (length (concat P)) + 1.
Proof.
intros P Hs. pose proof (cm_lens_nn P) as Hf. rewrite <- cm_lens_sum in *.
revert Hs Hf. generalize (WriterSpec.piece_lens P). intros ls0 Hs Hf.
destruct ls0 as [|l ls]; [cbn; lia|].
apply Forall_cons_iff in Hf as [Hl Hf]. cbn [WriterSpec.grow_calls fold_right] in *.
assert (Hr : 0 <= fold_right Z.add 0 ls).
{ clear -Hf. induction Hf as [|a l' Ha _ IH]; cbn [fold_right]; lia. }
rewrite (proj2 (Z.ltb_lt 0 (0 + l + 1))) by lia.
pose proof (cm_newcap_reach 0 (0 + l + 1) ltac:(lia) ltac:(lia)) as Hn.
pose proof (cm_gc_len ls (0 + l) (WriterSpec.newcap 0 (0 + l + 1)) ltac:(lia) ltac:(lia) Hf ltac:(lia)) as H.
cbn [length]. lia.
Qed.

(* the accepting run makes at most one call per byte of its text, plus one *)
Lemma cm_wcalls_wlen : forall t p, PjWriteHyp.wlen t p + 1 <= 2 ^ 62 ->
  PjWriteHyp.wcalls t p <= PjWriteHyp.wlen t p + 1.
Proof.
intros t p H. unfold PjWriteHyp.wcalls, PjWriteHyp.wlen, WriterValue.wdoc in *. apply cm_gcalls_le. exact H.
Qed.

(* a failed writer stays as it is *)
Lemma cm_wput_failed : forall P ok st, WriterApp.w_failed st <> 0 -> PRH_FnWriter.prhWriter_putN ok st P = st.
Proof.
induction P as [|b P IH]; intros ok st H; [reflexivity|].
cbn [PRH_FnWriter.prhWriter_putN]. unfold PRH_FnWriter.prhWriter_grows. rewrite (proj2 (Z.eqb_neq _ 0) H).
cbn [andb].
assert (E1 : WriterApp.put1 st b = st).
{ unfold WriterApp.put1. destruct (Z.eqb_spec (WriterApp.w_failed st) 0); [lia | reflexivity]. }
rewrite E1. apply IH. exact H.
Qed.

(* ONE RUN, ONE INDUCTION: the calls the run appends (l), g_count grown by them (mod 2 ^ 64), at most the accepting
   run's grow_calls, and exactly those when the run ends unfailed *)
Lemma cm_wput : forall P ok st, 0 <= WriterApp.w_cnt st < 2 ^ 64 ->
  exists l,
    WriterApp.w_calls (PRH_FnWriter.prhWriter_putN ok st P) = WriterApp.w_calls st ++ l /\
    WriterApp.w_cnt (PRH_FnWriter.prhWriter_putN ok st P) = (WriterApp.w_cnt st + Z.of_nat (length l)) mod 2 ^ 64 /\
    (WriterApp.w_failed st = 0 ->
       (length l <= length (WriterSpec.grow_calls (Z.of_nat (length (WriterApp.w_text st))) (WriterApp.w_cap st)
                              (WriterSpec.piece_lens P)))%nat /\
       (WriterApp.w_failed (PRH_FnWriter.prhWriter_putN ok st P) = 0 ->
          l = WriterSpec.grow_calls (Z.of_nat (length (WriterApp.w_text st))) (WriterApp.w_cap st)
                (WriterSpec.piece_lens P))).
Proof.
induction P as [|b P IH]; intros ok [f tx c n fl cs] Hn;
  cbn [WriterApp.w_failed WriterApp.w_text WriterApp.w_cap WriterApp.w_cnt WriterApp.w_fail WriterApp.w_calls] in *.
- exists []. cbn [PRH_FnWriter.prhWriter_putN WriterApp.w_calls WriterApp.w_cnt WriterApp.w_failed length].
  split; [rewrite app_nil_r; reflexivity|]. split; [rewrite Z.add_0_r, Z.mod_small by lia; reflexivity|].
  intros _. split; [cbn; lia|]. intros _. reflexivity.
- destruct (Z.eqb_spec f 0) as [->|F].
  2:{ exists []. rewrite cm_wput_failed by (cbn [WriterApp.w_failed]; exact F).
      cbn [WriterApp.w_calls WriterApp.w_cnt length]. split; [rewrite app_nil_r; reflexivity|].
      split; [rewrite Z.add_0_r, Z.mod_small by lia; reflexivity|]. intros H; contradiction. }
  unfold WriterSpec.piece_lens. cbn [map]. fold (WriterSpec.piece_lens P). cbn [WriterSpec.grow_calls].
  cbn [PRH_FnWriter.prhWriter_putN].
  unfold PRH_FnWriter.prhWriter_grows, PRH_FnWriter.prhWriter_need.
  cbn [WriterApp.w_failed WriterApp.w_text WriterApp.w_cap]. rewrite Z.eqb_refl. cbn [andb].
  destruct (Z.ltb_spec c (Z.of_nat (length tx) + Z.of_nat (length b) + 1)) as [Hg|Hg].
  + set (c1 := WriterSpec.newcap c (Z.of_nat (length tx) + Z.of_nat (length b) + 1)).
    unfold PRH_FnWriter.prhWriter_put1, PRH_FnWriter.prhWriter_grows, PRH_FnWriter.prhWriter_need.
    cbn [WriterApp.w_failed WriterApp.w_text WriterApp.w_cap WriterApp.w_cnt WriterApp.w_fail WriterApp.w_calls].
    rewrite Z.eqb_refl, (proj2 (Z.ltb_lt _ _) Hg). cbn [andb]. cbv zeta. fold c1.
    assert (Hn1 : 0 <= (n + 1) mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
    destruct (Z.eqb_spec n fl) as [Enf|Enf]; [|destruct (hd true ok) eqn:Hh].
    * exists [c1]. rewrite cm_wput_failed by (cbn [WriterApp.w_failed]; lia).
      cbn [WriterApp.w_calls WriterApp.w_cnt WriterApp.w_failed length].
      split; [reflexivity|]. split; [f_equal|]. intros _. split; [cbn [length]; lia|]. intros H; lia.
    * destruct (IH (tl ok) (WriterApp.mkW 0 (tx ++ b) c1 ((n + 1) mod 2 ^ 64) fl (cs ++ [c1])) Hn1)
        as (l1 & I1 & I2 & I3).
      cbn [WriterApp.w_failed WriterApp.w_text WriterApp.w_cap WriterApp.w_cnt WriterApp.w_fail WriterApp.w_calls]
        in I1, I2, I3.
      rewrite length_app, Nat2Z.inj_add in I3. destruct (I3 eq_refl) as [I4 I5].
      exists (c1 :: l1). split; [rewrite I1, <- app_assoc; reflexivity|].
      split; [rewrite I2; cbn [length]; rewrite Zplus_mod_idemp_l; f_equal; lia|].
      intros _. split; [cbn [length]; lia|]. intros H. rewrite (I5 H). reflexivity.
    * exists [c1]. rewrite cm_wput_failed by (cbn [WriterApp.w_failed]; lia).
      cbn [WriterApp.w_calls WriterApp.w_cnt WriterApp.w_failed length].
      split; [reflexivity|]. split; [f_equal|]. intros _. split; [cbn [length]; lia|]. intros H; lia.
  + unfold WriterApp.put1.
    cbn [WriterApp.w_failed WriterApp.w_text WriterApp.w_cap WriterApp.w_cnt WriterApp.w_fail WriterApp.w_calls].
    cbn [negb Z.eqb]. cbv zeta. rewrite (proj2 (Z.leb_le _ _) Hg).
    destruct (IH ok (WriterApp.mkW 0 (tx ++ b) c n fl cs) Hn) as (l1 & I1 & I2 & I3).
    cbn [WriterApp.w_failed WriterApp.w_text WriterApp.w_cap WriterApp.w_cnt WriterApp.w_fail WriterApp.w_calls]
      in I1, I2, I3.
    rewrite length_app, Nat2Z.inj_add in I3.
    exists l1. split; [exact I1|]. split; [exact I2|]. intros _. exact (I3 eq_refl).
Qed.

Lemma cm_wput_k : forall P ok st, 0 <= WriterApp.w_cnt st < 2 ^ 64 ->
  exists l, WriterApp.w_calls (PRH_FnWriter.prhWriter_putN ok st P) = WriterApp.w_calls st ++ l /\
    PRH_FnWriter.prhWriter_k ok st P = length l.
Proof.
intros P ok st Hn. destruct (cm_wput P ok st Hn) as (l & E & _). exists l. split; [exact E|].
unfold PRH_FnWriter.prhWriter_k. rewrite E, length_app. lia.
Qed.

(* the three facts at pj_write's run, from w0 cnt fail over wdpieces t p (PRH_FnWriter.v tpj_write_specX's st') *)
Lemma cm_pjw_k_le : forall ok cnt fail t p, 0 <= cnt < 2 ^ 64 ->
  Z.of_nat (PRH_FnWriter.prhWriter_k ok (WriterApp.w0 cnt fail) (WriterValue.wdpieces t p)) <= PjWriteHyp.wcalls t p.
Proof.
intros ok cnt fail t p Hn.
destruct (cm_wput (WriterValue.wdpieces t p) ok (WriterApp.w0 cnt fail) Hn) as (l & E & _ & I).
destruct (I eq_refl) as [I1 _].
assert (Ek : PRH_FnWriter.prhWriter_k ok (WriterApp.w0 cnt fail) (WriterValue.wdpieces t p) = length l).
{ unfold PRH_FnWriter.prhWriter_k. rewrite E, length_app. lia. }
rewrite Ek. unfold PjWriteHyp.wcalls.
change (Z.of_nat (length (WriterApp.w_text (WriterApp.w0 cnt fail)))) with 0 in I1.
change (WriterApp.w_cap (WriterApp.w0 cnt fail)) with 0 in I1.
apply Nat2Z.inj_le. exact I1.
Qed.

Lemma cm_pjw_cnt : forall ok cnt fail t p, 0 <= cnt -> cnt + PjWriteHyp.wcalls t p < 2 ^ 64 ->
  WriterApp.w_cnt (PRH_FnWriter.prhWriter_putN ok (WriterApp.w0 cnt fail) (WriterValue.wdpieces t p)) =
    cnt + Z.of_nat (PRH_FnWriter.prhWriter_k ok (WriterApp.w0 cnt fail) (WriterValue.wdpieces t p)) /\
  cnt <= WriterApp.w_cnt (PRH_FnWriter.prhWriter_putN ok (WriterApp.w0 cnt fail) (WriterValue.wdpieces t p))
      <= cnt + PjWriteHyp.wcalls t p.
Proof.
intros ok cnt fail t p H0 H1. pose proof (cm_wcalls_nonneg t p).
assert (Hn : 0 <= WriterApp.w_cnt (WriterApp.w0 cnt fail) < 2 ^ 64) by (cbn; lia).
pose proof (cm_pjw_k_le ok cnt fail t p ltac:(lia)) as K.
destruct (cm_wput (WriterValue.wdpieces t p) ok (WriterApp.w0 cnt fail) Hn) as (l & E & C & _).
assert (Ek : PRH_FnWriter.prhWriter_k ok (WriterApp.w0 cnt fail) (WriterValue.wdpieces t p) = length l).
{ unfold PRH_FnWriter.prhWriter_k. rewrite E, length_app. lia. }
rewrite Ek in K |- *. rewrite C. cbn [WriterApp.w0 WriterApp.w_cnt]. rewrite Z.mod_small by lia. lia.
Qed.

Lemma cm_pjw_succ : forall ok cnt fail t p, 0 <= cnt -> cnt + PjWriteHyp.wcalls t p < 2 ^ 64 ->
  WriterApp.w_failed (PRH_FnWriter.prhWriter_putN ok (WriterApp.w0 cnt fail) (WriterValue.wdpieces t p)) = 0 ->
  Z.of_nat (PRH_FnWriter.prhWriter_k ok (WriterApp.w0 cnt fail) (WriterValue.wdpieces t p)) = PjWriteHyp.wcalls t p /\
  WriterApp.w_cnt (PRH_FnWriter.prhWriter_putN ok (WriterApp.w0 cnt fail) (WriterValue.wdpieces t p)) =
    cnt + PjWriteHyp.wcalls t p.
Proof.
intros ok cnt fail t p H0 H1 Hs.
assert (Hn : 0 <= WriterApp.w_cnt (WriterApp.w0 cnt fail) < 2 ^ 64) by (pose proof (cm_wcalls_nonneg t p); cbn; lia).
destruct (cm_wput (WriterValue.wdpieces t p) ok (WriterApp.w0 cnt fail) Hn) as (l & E & C & I).
destruct (I eq_refl) as [_ I2]. specialize (I2 Hs).
change (Z.of_nat (length (WriterApp.w_text (WriterApp.w0 cnt fail)))) with 0 in I2.
change (WriterApp.w_cap (WriterApp.w0 cnt fail)) with 0 in I2.
assert (Ek0 : PRH_FnWriter.prhWriter_k ok (WriterApp.w0 cnt fail) (WriterValue.wdpieces t p) = length l).
{ unfold PRH_FnWriter.prhWriter_k. rewrite E, length_app. lia. }
assert (Ek : Z.of_nat (PRH_FnWriter.prhWriter_k ok (WriterApp.w0 cnt fail) (WriterValue.wdpieces t p)) =
             PjWriteHyp.wcalls t p).
{ rewrite Ek0, I2. reflexivity. }
split; [exact Ek|]. rewrite C. cbn [WriterApp.w0 WriterApp.w_cnt].
replace (Z.of_nat (length l)) with (PjWriteHyp.wcalls t p) by (unfold PjWriteHyp.wcalls; rewrite I2; reflexivity).
apply Z.mod_small. pose proof (cm_wcalls_nonneg t p). lia.
Qed.

Lemma cm_nth_tl : forall (ok : list bool) i, nth (Datatypes.S i) ok true = nth i (tl ok) true.
Proof. intros [|b ok] i; [destruct i|]; reflexivity. Qed.

Lemma cm_nth_hd : forall (ok : list bool), nth 0 ok true = hd true ok.
Proof. intros [|b ok]; reflexivity. Qed.

(* A RUN THAT ENDS FAILED: some call i of it (i < prhWriter_k) is the injected one or a refusal *)
Lemma cm_wput_fail : forall P ok st, 0 <= WriterApp.w_cnt st < 2 ^ 64 -> WriterApp.w_failed st = 0 ->
  WriterApp.w_failed (PRH_FnWriter.prhWriter_putN ok st P) <> 0 ->
  exists i, (i < PRH_FnWriter.prhWriter_k ok st P)%nat /\
    ((WriterApp.w_cnt st + Z.of_nat i) mod 2 ^ 64 = WriterApp.w_fail st \/ nth i ok true = false).
Proof.
induction P as [|b P IH]; intros ok [f tx c n fl cs] Hn Hf Hend;
  cbn [WriterApp.w_failed WriterApp.w_text WriterApp.w_cap WriterApp.w_cnt WriterApp.w_fail WriterApp.w_calls] in *;
  subst f.
- cbn [PRH_FnWriter.prhWriter_putN WriterApp.w_failed] in Hend. lia.
- unfold PRH_FnWriter.prhWriter_k. revert Hend.
  cbn [PRH_FnWriter.prhWriter_putN].
  unfold PRH_FnWriter.prhWriter_grows, PRH_FnWriter.prhWriter_need.
  cbn [WriterApp.w_failed WriterApp.w_text WriterApp.w_cap WriterApp.w_calls]. rewrite Z.eqb_refl. cbn [andb].
  destruct (Z.ltb_spec c (Z.of_nat (length tx) + Z.of_nat (length b) + 1)) as [Hg|Hg].
  + set (c1 := WriterSpec.newcap c (Z.of_nat (length tx) + Z.of_nat (length b) + 1)).
    unfold PRH_FnWriter.prhWriter_put1, PRH_FnWriter.prhWriter_grows, PRH_FnWriter.prhWriter_need.
    cbn [WriterApp.w_failed WriterApp.w_text WriterApp.w_cap WriterApp.w_cnt WriterApp.w_fail WriterApp.w_calls].
    rewrite Z.eqb_refl, (proj2 (Z.ltb_lt _ _) Hg). cbn [andb]. cbv zeta. fold c1.
    assert (Hn1 : 0 <= (n + 1) mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
    destruct (Z.eqb_spec n fl) as [Enf|Enf]; [|destruct (hd true ok) eqn:Hh]; intros Hend.
    * exists 0%nat. rewrite cm_wput_failed by (cbn [WriterApp.w_failed]; lia).
      cbn [WriterApp.w_calls]. rewrite length_app. cbn [length].
      split; [lia|]. left. rewrite Z.add_0_r, Z.mod_small by lia. exact Enf.
    * destruct (IH (tl ok) (WriterApp.mkW 0 (tx ++ b) c1 ((n + 1) mod 2 ^ 64) fl (cs ++ [c1])) Hn1 eq_refl Hend)
        as (i & I1 & I2).
      destruct (cm_wput_k P (tl ok) (WriterApp.mkW 0 (tx ++ b) c1 ((n + 1) mod 2 ^ 64) fl (cs ++ [c1])) Hn1)
        as (l & El & Ek).
      unfold PRH_FnWriter.prhWriter_k in I1, Ek.
      cbn [WriterApp.w_failed WriterApp.w_text WriterApp.w_cap WriterApp.w_cnt WriterApp.w_fail WriterApp.w_calls]
        in I1, I2, El, Ek.
      rewrite El in I1 |- *. rewrite !length_app in I1 |- *. cbn [length] in I1 |- *.
      exists (Datatypes.S i). split; [lia|].
      destruct I2 as [I2|I2]; [left|right].
      -- rewrite <- I2, Zplus_mod_idemp_l. f_equal. lia.
      -- rewrite cm_nth_tl. exact I2.
    * exists 0%nat. rewrite cm_wput_failed by (cbn [WriterApp.w_failed]; lia).
      cbn [WriterApp.w_calls]. rewrite length_app. cbn [length].
      split; [lia|]. right. rewrite cm_nth_hd. exact Hh.
  + unfold WriterApp.put1.
    cbn [WriterApp.w_failed WriterApp.w_text WriterApp.w_cap WriterApp.w_cnt WriterApp.w_fail WriterApp.w_calls].
    cbn [negb Z.eqb]. cbv zeta. rewrite (proj2 (Z.leb_le _ _) Hg). intros Hend.
    destruct (IH ok (WriterApp.mkW 0 (tx ++ b) c n fl cs) Hn eq_refl Hend) as (i & I1 & I2).
    unfold PRH_FnWriter.prhWriter_k in I1.
    cbn [WriterApp.w_failed WriterApp.w_text WriterApp.w_cap WriterApp.w_cnt WriterApp.w_fail WriterApp.w_calls]
      in I1, I2.
    exists i. split; [exact I1|exact I2].
Qed.

(* at pj_write's run: a failed write had a call i < prhWriter_k at g_count = cnt + i that was the injected one
   (cnt + i = fail) or refused (nth i ok true = false) - prh_oks' third conjunct then gives ran' = 1 *)
Lemma cm_pjw_fail : forall ok cnt fail t p, 0 <= cnt -> cnt + PjWriteHyp.wcalls t p < 2 ^ 64 ->
  WriterApp.w_failed (PRH_FnWriter.prhWriter_putN ok (WriterApp.w0 cnt fail) (WriterValue.wdpieces t p)) <> 0 ->
  exists i, (i < PRH_FnWriter.prhWriter_k ok (WriterApp.w0 cnt fail) (WriterValue.wdpieces t p))%nat /\
    (cnt + Z.of_nat i = fail \/ nth i ok true = false).
Proof.
intros ok cnt fail t p H0 H1 Hf. pose proof (cm_wcalls_nonneg t p).
assert (Hn : 0 <= WriterApp.w_cnt (WriterApp.w0 cnt fail) < 2 ^ 64) by (cbn; lia).
pose proof (cm_pjw_k_le ok cnt fail t p ltac:(lia)) as K.
destruct (cm_wput_fail (WriterValue.wdpieces t p) ok (WriterApp.w0 cnt fail) Hn eq_refl Hf) as (i & I1 & I2).
exists i. split; [exact I1|]. cbn [WriterApp.w0 WriterApp.w_cnt WriterApp.w_fail] in I2.
rewrite Z.mod_small in I2 by lia. exact I2.
Qed.

(* A RUN THAT ENDS UNFAILED holds grow_cap's capacity *)
Lemma cm_wput_cap : forall P ok st, WriterApp.w_failed st = 0 ->
  WriterApp.w_failed (PRH_FnWriter.prhWriter_putN ok st P) = 0 ->
  WriterApp.w_cap (PRH_FnWriter.prhWriter_putN ok st P) =
    WriterSpec.grow_cap (Z.of_nat (length (WriterApp.w_text st))) (WriterApp.w_cap st) (WriterSpec.piece_lens P).
Proof.
induction P as [|b P IH]; intros ok [f tx c n fl cs] Hf Hend;
  cbn [WriterApp.w_failed WriterApp.w_text WriterApp.w_cap WriterApp.w_cnt WriterApp.w_fail WriterApp.w_calls] in *;
  subst f.
- reflexivity.
- revert Hend. unfold WriterSpec.piece_lens. cbn [map]. fold (WriterSpec.piece_lens P). cbn [WriterSpec.grow_cap].
  cbn [PRH_FnWriter.prhWriter_putN].
  unfold PRH_FnWriter.prhWriter_grows, PRH_FnWriter.prhWriter_need.
  cbn [WriterApp.w_failed WriterApp.w_text WriterApp.w_cap]. rewrite Z.eqb_refl. cbn [andb].
  destruct (Z.ltb_spec c (Z.of_nat (length tx) + Z.of_nat (length b) + 1)) as [Hg|Hg].
  + set (c1 := WriterSpec.newcap c (Z.of_nat (length tx) + Z.of_nat (length b) + 1)).
    unfold PRH_FnWriter.prhWriter_put1, PRH_FnWriter.prhWriter_grows, PRH_FnWriter.prhWriter_need.
    cbn [WriterApp.w_failed WriterApp.w_text WriterApp.w_cap WriterApp.w_cnt WriterApp.w_fail WriterApp.w_calls].
    rewrite Z.eqb_refl, (proj2 (Z.ltb_lt _ _) Hg). cbn [andb]. cbv zeta. fold c1.
    destruct (Z.eqb_spec n fl) as [Enf|Enf]; [|destruct (hd true ok) eqn:Hh]; intros Hend.
    * rewrite cm_wput_failed in Hend by (cbn [WriterApp.w_failed]; lia). cbn [WriterApp.w_failed] in Hend. lia.
    * rewrite (IH (tl ok) (WriterApp.mkW 0 (tx ++ b) c1 ((n + 1) mod 2 ^ 64) fl (cs ++ [c1])) eq_refl Hend).
      cbn [WriterApp.w_text WriterApp.w_cap]. rewrite length_app, Nat2Z.inj_add. reflexivity.
    * rewrite cm_wput_failed in Hend by (cbn [WriterApp.w_failed]; lia). cbn [WriterApp.w_failed] in Hend. lia.
  + unfold WriterApp.put1.
    cbn [WriterApp.w_failed WriterApp.w_text WriterApp.w_cap WriterApp.w_cnt WriterApp.w_fail WriterApp.w_calls].
    cbn [negb Z.eqb]. cbv zeta. rewrite (proj2 (Z.leb_le _ _) Hg). intros Hend.
    rewrite (IH ok (WriterApp.mkW 0 (tx ++ b) c n fl cs) eq_refl Hend).
    cbn [WriterApp.w_text WriterApp.w_cap]. rewrite length_app, Nat2Z.inj_add. reflexivity.
Qed.

Lemma cm_dbl_le : forall f c need, WriterSpec.dbl f c need <= Z.max c (2 * need - 1).
Proof.
induction f as [|f IH]; intros c need; cbn [WriterSpec.dbl]; [lia|].
destruct (Z.leb_spec need c); [lia|]. specialize (IH (2 * c) need). lia.
Qed.

Lemma cm_newcap_le : forall c need, 0 <= c -> c < need -> WriterSpec.newcap c need <= Z.max 4096 (2 * need).
Proof.
intros c need H0 H. unfold WriterSpec.newcap. destruct (c =? 0) eqn:E.
- pose proof (cm_dbl_le 64 4096 need). lia.
- pose proof (cm_dbl_le 64 c need). lia.
Qed.

Lemma cm_newcap_nn : forall c need, 0 <= c -> 0 <= WriterSpec.newcap c need.
Proof.
intros c need H0. unfold WriterSpec.newcap. destruct (c =? 0).
- pose proof (cm_dbl_ge 64 4096 need ltac:(lia)). lia.
- pose proof (cm_dbl_ge 64 c need H0). lia.
Qed.

(* the capacity a run of grows reaches: at most twice the final need, or the first page *)
Lemma cm_gcap_le : forall ls x c, 0 <= x -> 0 <= c -> Forall (fun l => 0 <= l) ls ->
  c <= Z.max 4096 (2 * (x + 1)) ->
  WriterSpec.grow_cap x c ls <= Z.max 4096 (2 * (x + fold_right Z.add 0 ls + 1)).
Proof.
induction ls as [|l ls IH]; intros x c Hx Hc Hf Hcb; cbn [WriterSpec.grow_cap fold_right]; [lia|].
apply Forall_cons_iff in Hf as [Hl Hf].
assert (Hn : 0 <= fold_right Z.add 0 ls) by (clear -Hf; induction Hf; cbn [fold_right]; lia).
destruct (Z.ltb_spec c (x + l + 1)) as [Hlt|Hge].
- pose proof (cm_newcap_le c (x + l + 1) Hc Hlt) as N.
  pose proof (cm_newcap_nn c (x + l + 1) Hc) as N0.
  specialize (IH (x + l) (WriterSpec.newcap c (x + l + 1)) ltac:(lia) N0 Hf ltac:(lia)). lia.
- specialize (IH (x + l) c ltac:(lia) Hc Hf ltac:(lia)). lia.
Qed.

Lemma cm_gcap_nn : forall ls x c, 0 <= c -> 0 <= WriterSpec.grow_cap x c ls.
Proof.
induction ls as [|l ls IH]; intros x c Hc; cbn [WriterSpec.grow_cap]; [lia|].
destruct (c <? x + l + 1); apply IH; first [apply cm_newcap_nn; lia | lia].
Qed.

(* the capacity of an unfailed pj_write: at most twice its text and the NUL, or the first page *)
Lemma cm_pjw_cap_le : forall ok cnt fail t p,
  WriterApp.w_failed (PRH_FnWriter.prhWriter_putN ok (WriterApp.w0 cnt fail) (WriterValue.wdpieces t p)) = 0 ->
  0 <= WriterApp.w_cap (PRH_FnWriter.prhWriter_putN ok (WriterApp.w0 cnt fail) (WriterValue.wdpieces t p)) <=
    Z.max 4096 (2 * (Z.of_nat (length (WriterValue.wdoc t p)) + 1)).
Proof.
intros ok cnt fail t p Hs.
rewrite (cm_wput_cap (WriterValue.wdpieces t p) ok (WriterApp.w0 cnt fail) eq_refl Hs).
change (Z.of_nat (length (WriterApp.w_text (WriterApp.w0 cnt fail)))) with 0.
change (WriterApp.w_cap (WriterApp.w0 cnt fail)) with 0.
pose proof (cm_gcap_le (WriterSpec.piece_lens (WriterValue.wdpieces t p)) 0 0 ltac:(lia) ltac:(lia)
  (cm_lens_nn _) ltac:(lia)) as G.
rewrite cm_lens_sum in G.
pose proof (cm_gcap_nn (WriterSpec.piece_lens (WriterValue.wdpieces t p)) 0 0 ltac:(lia)) as Gn.
unfold WriterValue.wdoc. lia.
Qed.

(* ======================================================================================================== *)
(* 4. the rewrite's tree (ck_crt_tree): the index `at` the at-search loop (cut L1) computes, the member list   *)
(*    the member loop (L3) and the final checks (C) compare against                                           *)
(* ======================================================================================================== *)

(* at: the FIRST index of ck_MOD_AT among the keys, else length ms (new:739-741) *)
Fixpoint cm_at (ms : list (list Z * PjTree.jv)) : nat :=
  match ms with
  | [] => O
  | (k, _) :: r => if list_eq_dec Z.eq_dec k ck_MOD_AT then O else Datatypes.S (cm_at r)
  end.

Lemma cm_at_le : forall ms, (cm_at ms <= length ms)%nat.
Proof.
induction ms as [|[k v] r IH]; cbn [cm_at length]; [lia|].
destruct (list_eq_dec Z.eq_dec k ck_MOD_AT); lia.
Qed.

Lemma cm_at_in : forall ms, (cm_at ms < length ms)%nat <-> In ck_MOD_AT (map fst ms).
Proof.
induction ms as [|[k v] r IH]; cbn [cm_at length map fst In].
- split; [intros H; lia|contradiction].
- destruct (list_eq_dec Z.eq_dec k ck_MOD_AT) as [E|E].
  + split; [intros _; left; exact E|intros _; lia].
  + split.
    * intros H. right. apply IH. lia.
    * intros [H|H]; [contradiction|]. apply IH in H. lia.
Qed.

Lemma cm_at_out : forall ms, cm_at ms = length ms <-> ~ In ck_MOD_AT (map fst ms).
Proof.
intros ms. pose proof (cm_at_le ms). rewrite <- cm_at_in. lia.
Qed.

Lemma cm_at_before : forall ms j nm u, (j < cm_at ms)%nat -> nth_error ms j = Some (nm, u) -> nm <> ck_MOD_AT.
Proof.
induction ms as [|[k v] r IH]; intros j nm u Hj He; cbn [cm_at] in Hj; [lia|].
destruct (list_eq_dec Z.eq_dec k ck_MOD_AT) as [E|E]; [lia|].
destruct j as [|j]; cbn [nth_error] in He.
- injection He as <- <-. exact E.
- apply (IH j nm u); [lia|exact He].
Qed.

Lemma cm_at_key : forall ms, (cm_at ms < length ms)%nat -> exists u, nth_error ms (cm_at ms) = Some (ck_MOD_AT, u).
Proof.
induction ms as [|[k v] r IH]; intros H; [cbn in H; lia|].
cbn [cm_at length] in H |- *. destruct (list_eq_dec Z.eq_dec k ck_MOD_AT) as [E|E]; cbn [nth_error] in H |- *.
- exists v. rewrite E. reflexivity.
- apply IH. lia.
Qed.

(* the characterisation: an index i <= length ms with no ck_MOD_AT before it, and ck_MOD_AT at it when i < length ms,
   IS cm_at ms *)
Lemma cm_at_unique : forall ms i, (i <= length ms)%nat ->
  (forall j nm u, (j < i)%nat -> nth_error ms j = Some (nm, u) -> nm <> ck_MOD_AT) ->
  ((i < length ms)%nat -> exists u, nth_error ms i = Some (ck_MOD_AT, u)) ->
  cm_at ms = i.
Proof.
intros ms i Hi Hb Hk. pose proof (cm_at_le ms) as Ha.
destruct (Nat.lt_trichotomy (cm_at ms) i) as [Hlt|[Heq|Hgt]]; [|exact Heq|].
- destruct (cm_at_key ms ltac:(lia)) as [u Hu]. exfalso. exact (Hb _ _ _ Hlt Hu eq_refl).
- destruct (Hk ltac:(lia)) as [u Hu]. exfalso. exact (cm_at_before ms i _ _ Hgt Hu eq_refl).
Qed.

(* ---- the at-search loop (L1, new:739-741: `for (i = 0; i < doc->n && at == doc->n; i++) if (strcmp (doc->keys[i],
   REWRITTEN) == 0) at = i;`) as an invariant on (i, at): either nothing found yet and no key before i is
   ck_MOD_AT, or at is already cm_at ms ---- *)
Definition cm_at_inv (ms : list (list Z * PjTree.jv)) (i a : nat) : Prop :=
  (i <= length ms)%nat /\
  ((a = length ms /\ forall j nm u, (j < i)%nat -> nth_error ms j = Some (nm, u) -> nm <> ck_MOD_AT) \/
   (a = cm_at ms /\ (cm_at ms < length ms)%nat)).

Lemma cm_at_inv_start : forall ms, cm_at_inv ms 0 (length ms).
Proof. intros ms. split; [lia|]. left. split; [reflexivity|]. intros j nm u Hj. lia. Qed.

Lemma cm_at_inv_hit : forall ms i a u, cm_at_inv ms i a -> a = length ms ->
  nth_error ms i = Some (ck_MOD_AT, u) -> i = cm_at ms /\ cm_at_inv ms (Datatypes.S i) i.
Proof.
intros ms i a u [Hi H] Ha He.
assert (Hl : (i < length ms)%nat) by (apply nth_error_Some; rewrite He; discriminate).
destruct H as [[_ Hb]|[Ea Hlt]]; [|lia].
assert (E : cm_at ms = i) by (apply cm_at_unique; [lia|exact Hb|intros _; exists u; exact He]).
split; [symmetry; exact E|]. split; [lia|]. right. split; [symmetry; exact E|lia].
Qed.

Lemma cm_at_inv_miss : forall ms i a nm u, cm_at_inv ms i a -> a = length ms ->
  nth_error ms i = Some (nm, u) -> nm <> ck_MOD_AT -> cm_at_inv ms (Datatypes.S i) a.
Proof.
intros ms i a nm u [Hi H] Ha He Hne.
assert (Hl : (i < length ms)%nat) by (apply nth_error_Some; rewrite He; discriminate).
split; [lia|]. destruct H as [[Ea Hb]|[Ea Hlt]]; [|lia].
left. split; [exact Ea|]. intros j nm' u' Hj Hj'.
destruct (Nat.eq_dec j i) as [->|Hji].
- rewrite He in Hj'. injection Hj' as <- <-. exact Hne.
- apply (Hb j nm' u'); [lia|exact Hj'].
Qed.

Lemma cm_at_inv_exit : forall ms i a, cm_at_inv ms i a -> (i = length ms \/ a <> length ms) -> a = cm_at ms.
Proof.
intros ms i a [Hi H] Hx. destruct H as [[Ea Hb]|[Ea _]]; [|exact Ea].
destruct Hx as [->|Hx]; [|contradiction].
rewrite Ea. symmetry. apply cm_at_unique; [lia|exact Hb|intros Hl; lia].
Qed.

(* ---- pj_set_model at ck_MOD_AT, read through cm_at ---- *)
Lemma cm_set_len : forall ms v, length (PjTree.pj_set_model ms ck_MOD_AT v) =
  (if Nat.eqb (cm_at ms) (length ms) then Datatypes.S (length ms) else length ms).
Proof.
induction ms as [|[k u] r IH]; intros v; cbn [PjTree.pj_set_model cm_at length]; [reflexivity|].
destruct (list_eq_dec Z.eq_dec k ck_MOD_AT) as [E|E]; cbn [length].
- reflexivity.
- rewrite IH. cbn [Nat.eqb]. destruct (Nat.eqb (cm_at r) (length r)); reflexivity.
Qed.

Lemma cm_set_len_in : forall ms v, In ck_MOD_AT (map fst ms) -> length (PjTree.pj_set_model ms ck_MOD_AT v) = length ms.
Proof.
intros ms v H. rewrite cm_set_len. apply cm_at_in in H.
destruct (Nat.eqb_spec (cm_at ms) (length ms)); [lia|reflexivity].
Qed.

Lemma cm_set_len_out : forall ms v, ~ In ck_MOD_AT (map fst ms) ->
  length (PjTree.pj_set_model ms ck_MOD_AT v) = Datatypes.S (length ms).
Proof. intros ms v H. rewrite cm_set_len. apply cm_at_out in H. rewrite H, Nat.eqb_refl. reflexivity. Qed.

(* the index at carries the key and the value *)
Lemma cm_set_at : forall ms v, nth_error (PjTree.pj_set_model ms ck_MOD_AT v) (cm_at ms) = Some (ck_MOD_AT, v).
Proof.
induction ms as [|[k u] r IH]; intros v; [reflexivity|].
cbn [PjTree.pj_set_model cm_at]. destruct (list_eq_dec Z.eq_dec k ck_MOD_AT) as [E|E]; cbn [nth_error].
- rewrite E. reflexivity.
- exact (IH v).
Qed.

(* every other index keeps its entry (in particular each i < length ms, i <> at, keeps its key and its value) *)
Lemma cm_set_keep : forall ms v i, i <> cm_at ms ->
  nth_error (PjTree.pj_set_model ms ck_MOD_AT v) i = nth_error ms i.
Proof.
induction ms as [|[k u] r IH]; intros v i Hi.
- cbn [cm_at] in Hi. destruct i as [|i]; [lia|]. destruct i; reflexivity.
- revert Hi. cbn [PjTree.pj_set_model cm_at].
  destruct (list_eq_dec Z.eq_dec k ck_MOD_AT) as [E|E]; intros Hi.
  + destruct i as [|i]; [lia|]. reflexivity.
  + destruct i as [|i]; [reflexivity|]. cbn [nth_error]. apply IH. lia.
Qed.

(* the member loop's compare, index by index: for i < length ms the key is kept, and the value too unless i = at *)
Lemma cm_set_member : forall ms v i nm u, nth_error ms i = Some (nm, u) ->
  exists u', nth_error (PjTree.pj_set_model ms ck_MOD_AT v) i = Some (nm, u') /\ (i <> cm_at ms -> u' = u) /\
    (i = cm_at ms -> nm = ck_MOD_AT /\ u' = v).
Proof.
intros ms v i nm u He. destruct (Nat.eq_dec i (cm_at ms)) as [->|Hne].
- assert (Hl : (cm_at ms < length ms)%nat) by (apply nth_error_Some; rewrite He; discriminate).
  destruct (cm_at_key ms Hl) as [u0 Hu0]. rewrite He in Hu0. injection Hu0 as -> _.
  exists v. split; [apply cm_set_at|]. split; [intros N; contradiction N; reflexivity|]. intros _. split; reflexivity.
- exists u. rewrite (cm_set_keep ms v i Hne). split; [exact He|]. split; [intros _; reflexivity|]. intros E; contradiction.
Qed.

(* ---- the tree ---- *)
Lemma cm_crt_tree_obj : forall ms,
  ck_crt_tree (PjTree.JObj ms) = PjTree.JObj (PjTree.pj_set_model ms ck_MOD_AT (PjTree.JStr ck_STAMP)).
Proof. reflexivity. Qed.

Lemma cm_crt_tree_nobj : forall t, (forall ms, t <> PjTree.JObj ms) -> ck_crt_tree t = t.
Proof.
intros t H. destruct t as [| | | txt bits | s | items | ms]; try reflexivity. exfalso. exact (H ms eq_refl).
Qed.

(* the rewrite's tree IS the model's copy_set (lib/Spec/PresetReqAt.v 379c33e9e482 :322): the two strings are the
   same literals (MOD_KEY :184, MOD_VAL :185) *)
Lemma cm_MOD_KEY : ck_MOD_AT = PresetReqAt.MOD_KEY.
Proof. reflexivity. Qed.

Lemma cm_MOD_VAL : ck_STAMP = PresetReqAt.MOD_VAL.
Proof. reflexivity. Qed.

Lemma cm_crt_tree_copy_set : forall ms, ck_crt_tree (PjTree.JObj ms) = PresetReqAt.copy_set ms.
Proof. intros ms. reflexivity. Qed.

Lemma cm_crt_tree_copy_set_eq : forall t ms, t = PjTree.JObj ms -> ck_crt_tree t = PresetReqAt.copy_set ms.
Proof. intros t ms ->. reflexivity. Qed.

Lemma cm_crt_tag : forall t, PjTree.tag (ck_crt_tree t) = PjTree.tag t.
Proof. intros t. destruct t; reflexivity. Qed.

Lemma cm_members_obj : forall ms, ck_members (PjTree.JObj ms) = Z.of_nat (length ms).
Proof. reflexivity. Qed.

Lemma cm_members_nonneg : forall t, 0 <= ck_members t.
Proof. intros t. destruct t; cbn [ck_members]; lia. Qed.

(* back.n = doc->n + (at == doc->n ? 1 : 0) (the test at L2, new:746) *)
Lemma cm_members_crt : forall t ms, t = PjTree.JObj ms ->
  ck_members (ck_crt_tree t) = ck_members t + (if Nat.eqb (cm_at ms) (length ms) then 1 else 0).
Proof.
intros t ms ->. rewrite cm_crt_tree_obj, !cm_members_obj, cm_set_len.
destruct (Nat.eqb (cm_at ms) (length ms)); lia.
Qed.

Lemma cm_crt_at : forall t ms, t = PjTree.JObj ms ->
  exists ms', ck_crt_tree t = PjTree.JObj ms' /\
    nth_error ms' (cm_at ms) = Some (ck_MOD_AT, PjTree.JStr ck_STAMP) /\
    (forall i, i <> cm_at ms -> nth_error ms' i = nth_error ms i) /\
    length ms' = (if Nat.eqb (cm_at ms) (length ms) then Datatypes.S (length ms) else length ms).
Proof.
intros t ms ->. exists (PjTree.pj_set_model ms ck_MOD_AT (PjTree.JStr ck_STAMP)).
split; [reflexivity|]. split; [apply cm_set_at|]. split; [intros i Hi; apply cm_set_keep; exact Hi|].
apply cm_set_len.
Qed.

(* ---- the same facts through nth (any default d), the form a loop over keys[i] / kids[i] reads ---- *)
Lemma cm_nth_of_error : forall (A : Type) (l l' : list A) i d, nth_error l i = nth_error l' i -> nth i l d = nth i l' d.
Proof.
intros A l l' i d E. destruct (nth_error l i) as [x|] eqn:E1.
- assert (H1 : nth i l d = x) by (apply nth_error_nth; exact E1).
  assert (H2 : nth i l' d = x) by (apply nth_error_nth; rewrite <- E; reflexivity).
  rewrite H1, H2. reflexivity.
- assert (H1 : (length l <= i)%nat) by (apply nth_error_None; exact E1).
  assert (H2 : (length l' <= i)%nat) by (apply nth_error_None; rewrite <- E; reflexivity).
  rewrite nth_overflow by exact H1. rewrite nth_overflow by exact H2. reflexivity.
Qed.

Lemma cm_at_before_nth : forall ms d i, (i < cm_at ms)%nat -> fst (nth i ms d) <> ck_MOD_AT.
Proof.
intros ms d i Hi. pose proof (cm_at_le ms) as Ha. assert (Hl : (i < length ms)%nat) by lia.
destruct (nth i ms d) as [nm u] eqn:E. cbn [fst].
apply (cm_at_before ms i nm u Hi). rewrite <- E. apply nth_error_nth'. exact Hl.
Qed.

Lemma cm_at_key_nth : forall ms d, (cm_at ms < length ms)%nat -> fst (nth (cm_at ms) ms d) = ck_MOD_AT.
Proof.
intros ms d Hl. destruct (cm_at_key ms Hl) as [u Hu].
assert (E : nth_error ms (cm_at ms) = Some (nth (cm_at ms) ms d)) by (apply nth_error_nth'; exact Hl).
rewrite E in Hu. injection Hu as Hu. rewrite Hu. reflexivity.
Qed.

Lemma cm_set_nth_keep : forall ms v i d, i <> cm_at ms ->
  nth i (PjTree.pj_set_model ms ck_MOD_AT v) d = nth i ms d.
Proof. intros ms v i d Hi. apply cm_nth_of_error. apply cm_set_keep. exact Hi. Qed.

Lemma cm_set_nth_at : forall ms v d, nth (cm_at ms) (PjTree.pj_set_model ms ck_MOD_AT v) d = (ck_MOD_AT, v).
Proof. intros ms v d. apply nth_error_nth. apply cm_set_at. Qed.

(* the member loop's key compare (every i < doc->n) and value compare (i <> at) *)
Lemma cm_set_key_nth : forall ms v i d, (i < length ms)%nat ->
  fst (nth i (PjTree.pj_set_model ms ck_MOD_AT v) d) = fst (nth i ms d).
Proof.
intros ms v i d Hl. destruct (Nat.eq_dec i (cm_at ms)) as [->|Hne].
- rewrite cm_set_nth_at, (cm_at_key_nth ms d Hl). reflexivity.
- rewrite (cm_set_nth_keep ms v i d Hne). reflexivity.
Qed.

Lemma cm_set_val_nth : forall ms v i d, i <> cm_at ms ->
  snd (nth i (PjTree.pj_set_model ms ck_MOD_AT v) d) = snd (nth i ms d).
Proof. intros ms v i d Hi. rewrite (cm_set_nth_keep ms v i d Hi). reflexivity. Qed.

(* ======================================================================================================== *)
(* 5. depth and well-formedness of the rewrite; what the read-back of each text gives                          *)
(* ======================================================================================================== *)

Lemma cm_set_depth : forall ms k tv, (PjTree.depth (PjTree.JObj (PjTree.pj_set_model ms k tv)) <=
  Nat.max (PjTree.depth (PjTree.JObj ms)) (Datatypes.S (PjTree.depth tv)))%nat.
Proof.
induction ms as [|[k0 v0] r IH]; intros k tv; cbn [PjTree.pj_set_model].
- cbn [PjTree.depth map list_max fold_right]. lia.
- specialize (IH k tv). destruct (list_eq_dec Z.eq_dec k0 k);
    cbn [PjTree.depth map list_max fold_right] in *; unfold list_max in *; lia.
Qed.

Lemma cm_crt_depth_max : forall t, (PjTree.depth (ck_crt_tree t) <= Nat.max (PjTree.depth t) 1)%nat.
Proof.
intros t. destruct t as [| | | txt bits | s | items | ms]; cbn [ck_crt_tree]; try lia.
pose proof (cm_set_depth ms ck_MOD_AT (PjTree.JStr ck_STAMP)) as D.
change (PjTree.depth (PjTree.JStr ck_STAMP)) with 0%nat in D. lia.
Qed.

Lemma cm_crt_depth : forall t, (PjTree.depth t <= PjGrammar.MAXD)%nat ->
  (PjTree.depth (ck_crt_tree t) <= PjGrammar.MAXD)%nat.
Proof. intros t H. pose proof (cm_crt_depth_max t). unfold PjGrammar.MAXD in *. lia. Qed.

Lemma cm_crt_depth_doc : forall t, (PjTree.depth t <= PjGrammar.MAXD)%nat -> (PjTree.depth (ck_crt_tree t) <= DOC_D)%nat.
Proof. intros t H. pose proof (cm_crt_depth t H). unfold DOC_D. lia. Qed.

(* every member value of an object of depth <= MAXD is below DOC_D (same's nesting at each member compare) *)
Lemma cm_member_depth : forall ms k u, (PjTree.depth (PjTree.JObj ms) <= PjGrammar.MAXD)%nat -> In (k, u) ms ->
  (PjTree.depth u < PjGrammar.MAXD)%nat /\ (PjTree.depth u < DOC_D)%nat.
Proof.
intros ms k u H Hin. pose proof (PjTree.depth_member ms k u Hin). unfold DOC_D, PjGrammar.MAXD in *. lia.
Qed.

Lemma cm_member_depth_nth : forall ms i d, (PjTree.depth (PjTree.JObj ms) <= PjGrammar.MAXD)%nat ->
  (i < length ms)%nat -> (PjTree.depth (snd (nth i ms d)) < DOC_D)%nat.
Proof.
intros ms i d H Hl. destruct (nth i ms d) as [k u] eqn:E. cbn [snd].
apply (cm_member_depth ms k u H). rewrite <- E. apply nth_In. exact Hl.
Qed.

Lemma cm_crt_member_depth : forall t ms, (PjTree.depth t <= PjGrammar.MAXD)%nat -> t = PjTree.JObj ms ->
  forall i d, (i < length (PjTree.pj_set_model ms ck_MOD_AT (PjTree.JStr ck_STAMP)))%nat ->
  (PjTree.depth (snd (nth i (PjTree.pj_set_model ms ck_MOD_AT (PjTree.JStr ck_STAMP)) d)) < DOC_D)%nat.
Proof.
intros t ms H E i d Hl. apply cm_member_depth_nth; [|exact Hl].
pose proof (cm_crt_depth t H) as D. rewrite E in D. exact D.
Qed.

(* the two strtod oracles are one (PRH_Reader.v prh_jr_strtod has ReaderRes.jr_strtod's body), so pj_parse's granted
   trace of a well-formed tree's text is the tree's own ttrace *)
Lemma cm_strtod_eq : prh_jr_strtod = ReaderRes.jr_strtod.
Proof. reflexivity. Qed.

Lemma cm_ptrace_wf : forall t p, PjRoundTrip.pj_wf ReaderRes.jr_strtod t ->
  PRH_FnPj.prhPj_ptrace (WriterValue.wdoc t p) = PjRoundTrip.ttrace t.
Proof.
intros t p Hw. unfold PRH_FnPj.prhPj_ptrace. rewrite cm_strtod_eq. exact (PjRoundTrip.G9_trace _ t Hw p).
Qed.

(* a trace's live bytes at its end are at most its peak; its live blocks at most its calls *)
Lemma cm_held_le_hpeakR : forall tr, PjGrammar.held tr <= hpeakR tr.
Proof. induction tr as [|e r IH]; cbn [PjGrammar.held hpeakR]; lia. Qed.

Lemma cm_nlive_le_calls : forall tr, ReaderRes.nlive tr <= Z.of_nat (PjGrammar.calls tr).
Proof.
induction tr as [|e r IH]; cbn [ReaderRes.nlive PjGrammar.calls]; [lia|].
destruct e as [n|[|m] n|n|n]; cbn [ReaderRes.nlive_ev PjGrammar.is_call]; lia.
Qed.

(* ---- every live size of a trace is one of its requests (ReaderRes.lsz: an EAlloc / EGrow pushes its new size, a
   free or a grow removes one), so it is within the trace's request bound (PjReqBound.jr_req_bound_56) ---- *)
Lemma cm_rm1n_in : forall k s n, In n (ReaderRes.rm1n k s) -> In n s.
Proof.
induction s as [|y s IH]; intros n H; cbn [ReaderRes.rm1n] in H; [exact H|].
destruct (Nat.eqb y k); [right; exact H|]. destruct H as [H|H]; [left; exact H|right; exact (IH n H)].
Qed.

Lemma cm_lszf_bound : forall (bd : Z) tr s, (forall n, In n s -> Z.of_nat n <= bd) ->
  (forall e, In e tr -> PjReqBound.ev_req e <= bd) ->
  forall n, In n (fold_left ReaderRes.lsz_ev tr s) -> Z.of_nat n <= bd.
Proof.
intros bd. induction tr as [|e tr IH]; intros s Hs He; cbn [fold_left]; [exact Hs|].
apply IH; [|intros e' H'; apply He; right; exact H'].
assert (Ee := He e (or_introl eq_refl)).
intros n Hn. destruct e as [m|[|j] m|m|m]; cbn [ReaderRes.lsz_ev PjReqBound.ev_req] in Hn, Ee.
- destruct Hn as [<-|Hn]; [exact Ee|exact (Hs n Hn)].
- destruct Hn as [<-|Hn]; [exact Ee|exact (Hs n Hn)].
- destruct Hn as [<-|Hn]; [exact Ee|exact (Hs n (cm_rm1n_in _ _ _ Hn))].
- exact (Hs n Hn).
- exact (Hs n (cm_rm1n_in _ _ _ Hn)).
Qed.

Lemma cm_lsz_bound : forall sm t, PjRoundTrip.pj_wf sm t ->
  forall n, In n (ReaderRes.lsz (PjRoundTrip.ttrace t)) ->
  Z.of_nat n <= 56 * Z.of_nat (length (WriterValue.wdoc t false)) + 448.
Proof.
intros sm t Hw n Hn. unfold ReaderRes.lsz in Hn.
refine (cm_lszf_bound _ (PjRoundTrip.ttrace t) [] _ _ n Hn).
- intros k Hk. destruct Hk.
- intros e He. rewrite <- (PjRoundTrip.G9_trace sm t Hw false) in He.
  exact (PjReqBound.jr_req_bound_56 sm [] (WriterValue.wdoc t false) e He).
Qed.

(* ---- no NUL inside a written text: every byte of a well-formed tree's text is positive. The byte range itself is
   bytes_at's (PRH_Base.v bytes_at = YI00.garr8, 0 <= b < 256 per byte), which pj_write's success arm gives; the
   tree alone does not bound the bytes above (the text tcheck_round_trip_specX puts no range on x) ---- *)
Lemma cm_numch_pos : forall b, PjGrammar.numch b = true -> 0 < b.
Proof.
intros b. unfold PjGrammar.numch, PjGrammar.digit.
destruct (Z.leb_spec 48 b), (Z.eqb_spec b 46), (Z.eqb_spec b 101), (Z.eqb_spec b 69), (Z.eqb_spec b 43),
  (Z.eqb_spec b 45); cbn [andb orb]; intros Hnb; first [lia | discriminate Hnb].
Qed.

Lemma cm_hexd_pos : forall x, 0 <= x -> 0 < WriterSpec.hexd x.
Proof. intros x H. unfold WriterSpec.hexd. destruct (x <? 10); lia. Qed.

Ltac cm_fpos := repeat (apply Forall_cons; [cbv beta; lia|]); apply Forall_nil.

Lemma cm_ech_pos : forall c, 0 < c -> Forall (fun b => 0 < b) (PjRoundTrip.ech c).
Proof.
intros c Hc. unfold PjRoundTrip.ech. destruct (WriterSpec.special c); [|cm_fpos].
unfold WriterSpec.esc.
destruct (c =? 34); [cm_fpos|]. destruct (c =? 92); [cm_fpos|]. destruct (c =? 10); [cm_fpos|].
destruct (c =? 9); [cm_fpos|]. destruct (c =? 13); [cm_fpos|].
pose proof (cm_hexd_pos (c / 16) (Z.div_pos c 16 ltac:(lia) ltac:(lia))).
pose proof (cm_hexd_pos (c mod 16) (proj1 (Z.mod_pos_bound c 16 ltac:(lia)))).
cm_fpos.
Qed.

Lemma cm_flat_ech_pos : forall s, PjRoundTrip.strok s -> Forall (fun b => 0 < b) (flat_map PjRoundTrip.ech s).
Proof.
unfold PjRoundTrip.strok. induction s as [|c s IH]; intros H; cbn [flat_map]; [constructor|].
apply Forall_cons_iff in H as [Hc Hs]. apply Forall_app. split; [exact (cm_ech_pos c Hc)|exact (IH Hs)].
Qed.

Lemma cm_spieces_pos : forall k, PjRoundTrip.strok k -> Forall (fun b => 0 < b) (concat (WriterSpec.spieces k)).
Proof.
intros k H. rewrite PjRoundTrip.wstr_eq. apply Forall_cons; [cbv beta; lia|]. apply Forall_app.
split; [exact (cm_flat_ech_pos k H)|cm_fpos].
Qed.

Lemma cm_wind_pos : forall p d, Forall (fun b => 0 < b) (concat (WriterValue.wind p d)).
Proof.
intros [|] d; unfold WriterValue.wind; cbn [concat app]; [|constructor].
apply Forall_cons; [cbv beta; lia|].
induction (Z.to_nat d) as [|n IH]; cbn [repeat concat app]; [constructor|].
apply Forall_cons; [cbv beta; lia|]. apply Forall_cons; [cbv beta; lia|]. exact IH.
Qed.

Lemma cm_wcomma_pos : forall i, Forall (fun b => 0 < b) (concat (WriterValue.wcomma i)).
Proof. intros [|i]; cbn [WriterValue.wcomma Nat.eqb concat app]; cm_fpos. Qed.

Lemma cm_wsep_pos : forall p, Forall (fun b => 0 < b) (WriterValue.wsep p).
Proof. intros [|]; cbn [WriterValue.wsep]; cm_fpos. Qed.

Lemma cm_wv_pos : forall sm t, PjRoundTrip.good sm t ->
  forall p d, Forall (fun b => 0 < b) (concat (WriterValue.wvpieces t p d)).
Proof.
intros sm t. induction t as [| | | txt bits | s | items IH | ms IH] using PjTree.jv_ind'; intros Hg p d.
- cbn [WriterValue.wvpieces concat app]. cm_fpos.
- cbn [WriterValue.wvpieces concat app]. cm_fpos.
- cbn [WriterValue.wvpieces concat app]. cm_fpos.
- cbn [WriterValue.wvpieces concat]. rewrite app_nil_r.
  cbn [PjRoundTrip.good] in Hg. destruct Hg as [Hn _]. unfold PjRoundTrip.numtok in Hn.
  destruct Hn as (sg & c & a & -> & Hsg & Hc & Ha & _).
  apply Forall_app. split.
  + destruct Hsg as [->| ->]; cm_fpos.
  + unfold PjGrammar.digit in Hc. apply andb_true_iff in Hc as [Hc1 _]. apply Z.leb_le in Hc1.
    apply Forall_cons; [cbv beta; lia|].
    apply Forall_forall. intros b Hb. apply cm_numch_pos. rewrite forallb_forall in Ha. exact (Ha b Hb).
- cbn [WriterValue.wvpieces]. exact (cm_spieces_pos s Hg).
- apply PjRoundTrip.good_arr in Hg. rewrite PjRoundTrip.wv_arr, concat_cons, !concat_app.
  apply Forall_app. split; [cm_fpos|]. apply Forall_app. split.
  + revert IH Hg. generalize 0%nat. induction items as [|u r IHr]; intros i IH Hg;
      cbn [PjRoundTrip.wgo_arr concat]; [constructor|].
    apply Forall_cons_iff in IH as [IHu IHr']. apply Forall_cons_iff in Hg as [Hgu Hgr].
    rewrite !concat_app. apply Forall_app. split; [apply cm_wcomma_pos|].
    apply Forall_app. split; [apply cm_wind_pos|]. apply Forall_app. split; [exact (IHu Hgu p (d + 1))|].
    exact (IHr (Datatypes.S i) IHr' Hgr).
  + apply Forall_app. split; [destruct items as [|j l]; cbn [concat]; [constructor|apply cm_wind_pos]|].
    cbn [concat app]. cm_fpos.
- apply PjRoundTrip.good_obj in Hg. rewrite PjRoundTrip.wv_obj, concat_cons, !concat_app.
  apply Forall_app. split; [cm_fpos|]. apply Forall_app. split.
  + revert IH Hg. generalize 0%nat. induction ms as [|[k u] r IHr]; intros i IH Hg;
      cbn [PjRoundTrip.wgo_obj concat]; [constructor|].
    apply Forall_cons_iff in IH as [IHu IHr']. apply Forall_cons_iff in Hg as [[Hk Hgu] Hgr].
    cbn [fst snd] in IHu, Hk, Hgu.
    rewrite !concat_app. apply Forall_app. split; [apply cm_wcomma_pos|].
    apply Forall_app. split; [apply cm_wind_pos|]. apply Forall_app. split; [exact (cm_spieces_pos k Hk)|].
    apply Forall_app. split; [cbn [concat]; rewrite app_nil_r; apply cm_wsep_pos|].
    apply Forall_app. split; [exact (IHu Hgu p (d + 1))|].
    exact (IHr (Datatypes.S i) IHr' Hgr).
  + apply Forall_app. split; [destruct ms as [|m l]; cbn [concat]; [constructor|apply cm_wind_pos]|].
    cbn [concat app]. cm_fpos.
Qed.

Lemma cm_wdoc_pos : forall sm t p, PjRoundTrip.pj_wf sm t -> Forall (fun b => 0 < b) (WriterValue.wdoc t p).
Proof.
intros sm t p Hw. destruct (PjRoundTrip.wf_good sm t Hw) as [Hg _].
unfold WriterValue.wdoc, WriterValue.wdpieces. rewrite concat_app. apply Forall_app.
split; [exact (cm_wv_pos sm t Hg p 0)|]. destruct p; cbn [concat app]; cm_fpos.
Qed.

(* pj_wf of the original gives pj_wf of the rewrite: the stamp is a well-formed string, the key has no NUL *)
Lemma cm_crt_wf : forall sm t, PjRoundTrip.pj_wf sm t -> PjRoundTrip.pj_wf sm (ck_crt_tree t).
Proof.
intros sm t Hw. destruct t as [| | | txt bits | s | items | ms]; cbn [ck_crt_tree]; try exact Hw.
destruct (PjRoundTrip.wf_good sm _ Hw) as [_ Hd].
apply PjRoundTrip.wf_set.
- exact Hw.
- apply cm_STAMP_wf.
- exact cm_MOD_AT_bytes.
- pose proof (cm_set_depth ms ck_MOD_AT (PjTree.JStr ck_STAMP)) as D.
  change (PjTree.depth (PjTree.JStr ck_STAMP)) with 0%nat in D. unfold PjGrammar.MAXD in *. lia.
Qed.

(* the reader's calls on any outcome list are at most the granted run's (PjGrammar.G7_1 / G7_2) *)
Lemma cm_calls_le_ncalls : forall sm x ok,
  (PjGrammar.calls (snd (PjGrammar.jr_run sm x ok)) <= PjGrammar.ncalls sm x)%nat.
Proof.
intros sm x ok. destruct (PjGrammar.ok_upto_dec ok (PjGrammar.ncalls sm x)) as [H|(j & Hj & Hf & Hu)].
- rewrite (PjGrammar.G7_1_calls sm x ok H). lia.
- rewrite (proj2 (PjGrammar.G7_2 sm x ok j Hj Hf Hu)). lia.
Qed.

(* a well-formed tree's text: the reader's calls are tcalls, at most two per byte plus two *)
Lemma cm_tcalls_wlen : forall sm t p, PjRoundTrip.pj_wf sm t ->
  Z.of_nat (PjRoundTrip.tcalls t) <= 2 * PjWriteHyp.wlen t p + 2.
Proof.
intros sm t p Hw. rewrite <- (PjRoundTrip.G9_calls sm t Hw p).
unfold PjGrammar.ncalls, PjWriteHyp.wlen.
pose proof (PjGrammar.G7_4 sm (WriterValue.wdoc t p) []) as H. lia.
Qed.

(* ---- the rewrite's pretty text is at most 40 bytes longer than the original's ---- *)
Lemma cm_wcomma_len : forall i, length (concat (WriterValue.wcomma i)) = (if Nat.eqb i 0 then 0 else 1)%nat.
Proof. intros [|i]; reflexivity. Qed.

Lemma cm_wgo_set : forall p d k tv ms i,
  (length (concat (PjRoundTrip.wgo_obj p d i (PjTree.pj_set_model ms k tv))) <=
   length (concat (PjRoundTrip.wgo_obj p d i ms)) + length (concat (WriterValue.wcomma (i + length ms))) +
   length (concat (WriterValue.wind p (d + 1))) + length (concat (WriterSpec.spieces k)) +
   length (WriterValue.wsep p) + length (concat (WriterValue.wvpieces tv p (d + 1))))%nat.
Proof.
intros p d k tv ms. induction ms as [|[k0 v0] r IH]; intros i; cbn [PjTree.pj_set_model].
- cbn [PjRoundTrip.wgo_obj length]. rewrite Nat.add_0_r, !concat_app, concat_cons, !length_app.
  cbn [concat length]. lia.
- destruct (list_eq_dec Z.eq_dec k0 k) as [E|E]; cbn [PjRoundTrip.wgo_obj length].
  + rewrite !concat_app, !concat_cons, !length_app. lia.
  + specialize (IH (Datatypes.S i)). rewrite Nat.add_succ_r. rewrite Nat.add_succ_l in IH.
    rewrite !concat_app, !concat_cons, !length_app. lia.
Qed.

Lemma cm_wdoc1_len : forall t, length (WriterValue.wdoc t true) = (length (concat (WriterValue.wvpieces t true 0)) + 1)%nat.
Proof. intros t. unfold WriterValue.wdoc, WriterValue.wdpieces. rewrite concat_app, length_app. reflexivity. Qed.

Lemma cm_obj1_len : forall ms, length (concat (WriterValue.wvpieces (PjTree.JObj ms) true 0)) =
  (2 + length (concat (PjRoundTrip.wgo_obj true 0 0 ms)) + match ms with [] => 0 | _ :: _ => 1 end)%nat.
Proof.
intros ms. rewrite PjRoundTrip.wv_obj, concat_cons, !concat_app, !length_app.
destruct ms as [|m r]; cbn [length concat app].
- lia.
- assert (W : length (concat (WriterValue.wind true 0)) = 1%nat) by reflexivity. rewrite W. lia.
Qed.

Lemma cm_crt_wlen : forall t, (length (WriterValue.wdoc (ck_crt_tree t) true) <= length (WriterValue.wdoc t true) + 40)%nat.
Proof.
intros t. destruct t as [| | | txt bits | s | items | ms]; cbn [ck_crt_tree]; try lia.
rewrite !cm_wdoc1_len, !cm_obj1_len.
pose proof (cm_wgo_set true 0 ck_MOD_AT (PjTree.JStr ck_STAMP) ms 0) as H.
assert (L1 : length (concat (WriterValue.wind true (0 + 1))) = 3%nat) by reflexivity.
assert (L2 : length (concat (WriterSpec.spieces ck_MOD_AT)) = 12%nat) by reflexivity.
assert (L3 : length (WriterValue.wsep true) = 2%nat) by reflexivity.
assert (L4 : length (concat (WriterValue.wvpieces (PjTree.JStr ck_STAMP) true (0 + 1))) = 22%nat) by reflexivity.
rewrite L1, L2, L3, L4, cm_wcomma_len in H.
destruct ms as [|[k v] r]; cbn [PjTree.pj_set_model length Nat.add Nat.eqb] in *.
- lia.
- destruct (list_eq_dec Z.eq_dec k ck_MOD_AT); cbn [length] in *; lia.
Qed.

(* ---- the same for the compact text: at most 36 bytes longer ---- *)
Lemma cm_wdoc0_len : forall t, length (WriterValue.wdoc t false) = length (concat (WriterValue.wvpieces t false 0)).
Proof. intros t. unfold WriterValue.wdoc, WriterValue.wdpieces. rewrite concat_app, length_app. cbn [concat length]. lia. Qed.

Lemma cm_obj0_len : forall ms, length (concat (WriterValue.wvpieces (PjTree.JObj ms) false 0)) =
  (2 + length (concat (PjRoundTrip.wgo_obj false 0 0 ms)))%nat.
Proof.
intros ms. rewrite PjRoundTrip.wv_obj, concat_cons, !concat_app, !length_app.
destruct ms as [|m r]; cbn [length concat app WriterValue.wind]; lia.
Qed.

Lemma cm_crt_wlen0 : forall t,
  (length (WriterValue.wdoc (ck_crt_tree t) false) <= length (WriterValue.wdoc t false) + 36)%nat.
Proof.
intros t. destruct t as [| | | txt bits | s | items | ms]; cbn [ck_crt_tree]; try lia.
rewrite !cm_wdoc0_len, !cm_obj0_len.
pose proof (cm_wgo_set false 0 ck_MOD_AT (PjTree.JStr ck_STAMP) ms 0) as H.
assert (L1 : length (concat (WriterValue.wind false (0 + 1))) = 0%nat) by reflexivity.
assert (L2 : length (concat (WriterSpec.spieces ck_MOD_AT)) = 12%nat) by reflexivity.
assert (L3 : length (WriterValue.wsep false) = 1%nat) by reflexivity.
assert (L4 : length (concat (WriterValue.wvpieces (PjTree.JStr ck_STAMP) false (0 + 1))) = 22%nat) by reflexivity.
rewrite L1, L2, L3, L4, cm_wcomma_len in H.
destruct ms as [|[k v] r]; cbn [PjTree.pj_set_model length Nat.add Nat.eqb] in *.
- lia.
- destruct (list_eq_dec Z.eq_dec k ck_MOD_AT); cbn [length] in *; lia.
Qed.

(* ======================================================================================================== *)
(* 6. the entry's model premises (tcheck_round_trip_specX: ck_read x = Some t, |x| <= 3 * 2 ^ 20, the two     *)
(*    wlen bounds) and what each call needs of them                                                            *)
(* ======================================================================================================== *)

Definition cm_in (x : list Z) (t : PjTree.jv) : Prop :=
  ck_read x = Some t /\ Z.of_nat (length x) <= 3 * 2 ^ 20 /\
  PjWriteHyp.wlen t false <= 3 * Z.of_nat (length x) /\ PjWriteHyp.wlen t true <= 56 * Z.of_nat (length x) - 54.

Lemma cm_in_intro : forall x t, ck_read x = Some t -> Z.of_nat (length x) <= 3 * 2 ^ 20 ->
  PjWriteHyp.wlen t false <= 3 * Z.of_nat (length x) -> PjWriteHyp.wlen t true <= 56 * Z.of_nat (length x) - 54 ->
  cm_in x t.
Proof. intros x t H1 H2 H3 H4. split; [exact H1|]. split; [exact H2|]. split; [exact H3|exact H4]. Qed.

(* round_trip_text's model premises, at both calls *)
Lemma cm_in_wf : forall x t, cm_in x t -> PjRoundTrip.pj_wf ReaderRes.jr_strtod t.
Proof. intros x t (H & _). exact (PjRoundTrip.wf_read ReaderRes.jr_strtod x t H). Qed.

Lemma cm_in_depth : forall x t, cm_in x t -> (PjTree.depth t <= PjGrammar.MAXD)%nat.
Proof. intros x t (H & _). exact (proj1 (proj2 (PjRoundTrip.read_json ReaderRes.jr_strtod x t H))). Qed.

Lemma cm_in_depth32 : forall x t, cm_in x t -> (PjTree.depth t <= 32)%nat.
Proof. intros x t H. exact (cm_in_depth x t H). Qed.

Lemma cm_in_depth_doc : forall x t, cm_in x t -> (PjTree.depth t <= DOC_D)%nat.
Proof. intros x t H. pose proof (cm_in_depth x t H). unfold DOC_D. lia. Qed.

Lemma cm_in_wlen : forall x t p, cm_in x t -> PjWriteHyp.wlen t p + 1 <= 2 ^ 28.
Proof. intros x t p (_ & H1 & H2 & H3). destruct p; lia. Qed.

(* the rewrite's pj_write and its read-back (parse_noting) *)
Lemma cm_in_crt_wf : forall x t, cm_in x t -> PjRoundTrip.pj_wf ReaderRes.jr_strtod (ck_crt_tree t).
Proof. intros x t H. exact (cm_crt_wf _ t (cm_in_wf x t H)). Qed.

Lemma cm_in_crt_depth : forall x t, cm_in x t -> (PjTree.depth (ck_crt_tree t) <= PjGrammar.MAXD)%nat.
Proof. intros x t H. exact (cm_crt_depth t (cm_in_depth x t H)). Qed.

Lemma cm_in_wlen_crt : forall x t, cm_in x t ->
  Z.of_nat (length (WriterValue.wdoc (ck_crt_tree t) true)) <= PjWriteHyp.wlen t true + 40 /\
  Z.of_nat (length (WriterValue.wdoc (ck_crt_tree t) true)) + 1 <= PRH_FnWriter.prhWriter_WMAX /\
  Z.of_nat (length (WriterValue.wdoc (ck_crt_tree t) true)) < 2 ^ 40.
Proof.
intros x t (_ & H1 & H2 & H3). pose proof (cm_crt_wlen t) as L. unfold PjWriteHyp.wlen in *.
unfold PRH_FnWriter.prhWriter_WMAX. lia.
Qed.

Lemma cm_in_maxrun_crt : forall x t, cm_in x t ->
  Z.of_nat (PjRoundTrip.maxrun (WriterValue.wdoc (ck_crt_tree t) true)) < 2 ^ 30.
Proof.
intros x t H. pose proof (PjRoundTrip.G12_1 (WriterValue.wdoc (ck_crt_tree t) true)) as M.
destruct (cm_in_wlen_crt x t H) as (_ & L & _). unfold PRH_FnWriter.prhWriter_WMAX in L. lia.
Qed.

(* the read-backs: each text reads back to its tree, with tcalls calls and ttrace as trace *)
Lemma cm_read_t : forall x t p, cm_in x t -> ck_read (WriterValue.wdoc t p) = Some t.
Proof. intros x t p H. exact (PjRoundTrip.G9 _ t (cm_in_wf x t H) p). Qed.

Lemma cm_ncalls_t : forall x t p, cm_in x t -> ck_ncalls (WriterValue.wdoc t p) = Z.of_nat (PjRoundTrip.tcalls t).
Proof. intros x t p H. unfold ck_ncalls. rewrite (PjRoundTrip.G9_calls _ t (cm_in_wf x t H) p). reflexivity. Qed.

Lemma cm_read_crt : forall x t p, cm_in x t -> ck_read (WriterValue.wdoc (ck_crt_tree t) p) = Some (ck_crt_tree t).
Proof. intros x t p H. exact (PjRoundTrip.G9 _ _ (cm_in_crt_wf x t H) p). Qed.

Lemma cm_ncalls_crt : forall x t p, cm_in x t ->
  ck_ncalls (WriterValue.wdoc (ck_crt_tree t) p) = Z.of_nat (PjRoundTrip.tcalls (ck_crt_tree t)).
Proof. intros x t p H. unfold ck_ncalls. rewrite (PjRoundTrip.G9_calls _ _ (cm_in_crt_wf x t H) p). reflexivity. Qed.

(* parse_noting's run on the rewrite's text: at most tcalls (ck_crt_tree t) calls whatever the outcomes (C4c), and
   the tree with its trace when every one of them is granted (C4) *)
Lemma cm_noting_calls : forall x t ok res tr, cm_in x t ->
  PjGrammar.jr_run ReaderRes.jr_strtod (WriterValue.wdoc (ck_crt_tree t) true) ok = (res, tr) ->
  (PjGrammar.calls tr <= PjRoundTrip.tcalls (ck_crt_tree t))%nat.
Proof.
intros x t ok res tr H E.
pose proof (cm_calls_le_ncalls ReaderRes.jr_strtod (WriterValue.wdoc (ck_crt_tree t) true) ok) as C.
rewrite E in C. cbn [snd] in C. rewrite (PjRoundTrip.G9_calls _ _ (cm_in_crt_wf x t H) true) in C. exact C.
Qed.

Lemma cm_noting_ok : forall x t ok, cm_in x t ->
  (forall i, (i < PjRoundTrip.tcalls (ck_crt_tree t))%nat -> nth i ok true = true) ->
  PjGrammar.jr_run ReaderRes.jr_strtod (WriterValue.wdoc (ck_crt_tree t) true) ok =
    (Some (ck_crt_tree t), PjRoundTrip.ttrace (ck_crt_tree t)).
Proof.
intros x t ok H Hu. pose proof (cm_in_crt_wf x t H) as Hw.
rewrite (PjGrammar.G7_1 ReaderRes.jr_strtod (WriterValue.wdoc (ck_crt_tree t) true) ok).
- rewrite (PjRoundTrip.G9 _ _ Hw true), (PjRoundTrip.G9_trace _ _ Hw true). reflexivity.
- rewrite (PjRoundTrip.G9_calls _ _ Hw true). exact Hu.
Qed.

(* ---- the sizes of the blocks the walk hands to pj_write's tree_vis (each 0 <= k < 2 ^ 32): the copy's (rtt (doc,
   0)'s read-back of the compact text, ttrace t), the rewrite's read-back (ttrace (ck_crt_tree t)), pj_set's grown
   arrays, and the saved text's buffer ---- *)
Lemma cm_lsz_small : forall x t, cm_in x t ->
  Forall (fun s => 0 <= s < 2 ^ 32) (map Z.of_nat (ReaderRes.lsz (PjRoundTrip.ttrace t))).
Proof.
intros x t Hin. apply Forall_forall. intros s Hs. apply in_map_iff in Hs as (n & <- & Hn).
pose proof (cm_lsz_bound _ t (cm_in_wf x t Hin) n Hn) as B.
destruct Hin as (_ & H1 & H2 & _). unfold PjWriteHyp.wlen in H2. lia.
Qed.

Lemma cm_db_small : forall x t (Db : list (Z * Z)), cm_in x t ->
  Permutation (map snd Db) (map Z.of_nat (ReaderRes.lsz (PjRoundTrip.ttrace t))) ->
  forall a k, In (a, k) Db -> 0 <= k < 2 ^ 32.
Proof.
intros x t Db Hin HP a k Hk. pose proof (cm_lsz_small x t Hin) as S. rewrite Forall_forall in S.
apply S. apply (Permutation_in _ HP). apply in_map_iff. exists (a, k). split; [reflexivity|exact Hk].
Qed.

Lemma cm_lsz_small_crt : forall x t, cm_in x t ->
  Forall (fun s => 0 <= s < 2 ^ 32) (map Z.of_nat (ReaderRes.lsz (PjRoundTrip.ttrace (ck_crt_tree t)))).
Proof.
intros x t Hin. apply Forall_forall. intros s Hs. apply in_map_iff in Hs as (n & <- & Hn).
pose proof (cm_lsz_bound _ (ck_crt_tree t) (cm_in_crt_wf x t Hin) n Hn) as B.
pose proof (cm_crt_wlen0 t) as L.
destruct Hin as (_ & H1 & H2 & _). unfold PjWriteHyp.wlen in H2. lia.
Qed.

(* an object read from x has at most |x| members (PjRoundTrip.tblocks_read) *)
Lemma cm_members_le : forall x t, ck_read x = Some t -> ck_members t <= Z.of_nat (length x).
Proof.
intros x t H. pose proof (PjRoundTrip.tblocks_read ReaderRes.jr_strtod x t H) as B.
destruct t as [| | | txt bits | s | items | ms]; cbn [ck_members]; try lia.
cbn [PjRoundTrip.tblocks] in B. lia.
Qed.

(* pj_set's grown kids and keys arrays at n = cap = ck_members t *)
Lemma cm_grow_small : forall x t, cm_in x t ->
  0 <= 56 * cap2R (ck_members t) < 2 ^ 32 /\ 0 <= 8 * cap2R (ck_members t) < 2 ^ 32.
Proof.
intros x t Hin. destruct Hin as (H0 & H1 & _). pose proof (cm_members_le x t H0) as M.
pose proof (cm_members_nonneg t) as N. unfold cap2R. destruct (Z.eqb_spec (ck_members t) 0); lia.
Qed.

(* the saved text's buffer: an unfailed pj_write of the rewrite holds less than 2 ^ 32 bytes *)
Lemma cm_pjw_cap_crt : forall x t ok cnt fail, cm_in x t ->
  WriterApp.w_failed (PRH_FnWriter.prhWriter_putN ok (WriterApp.w0 cnt fail)
    (WriterValue.wdpieces (ck_crt_tree t) true)) = 0 ->
  0 <= WriterApp.w_cap (PRH_FnWriter.prhWriter_putN ok (WriterApp.w0 cnt fail)
         (WriterValue.wdpieces (ck_crt_tree t) true)) < 2 ^ 32.
Proof.
intros x t ok cnt fail Hin Hs. pose proof (cm_pjw_cap_le ok cnt fail (ck_crt_tree t) true Hs) as C.
destruct (cm_in_wlen_crt x t Hin) as (_ & L & _). unfold PRH_FnWriter.prhWriter_WMAX in L. lia.
Qed.

(* ---- the side conditions of pj_write's event supply (the kit lemma PRH_Supply.prhWriter_pjw_evs_w_evs,
   commit 5d79c60634b, blob 392e316eeb02: `cf_head = PresetReqAt.HEAD -> 0 <= cnt < 2 ^ 64 ->
   (forall j, (j < PresetReqAt.wcalls t p)%nat -> (cnt + Z.of_nat j) mod 2 ^ 64 <> fail) ->
   prhWriter_pjw_evs [] cnt fail (wdpieces t p) = PresetReqAt.w_evs t p`), at fail = SIZE_MAXZ. The supply itself is
   that lemma's, not restated here ---- *)
Lemma cm_wcalls_req : forall t p, Z.of_nat (PresetReqAt.wcalls t p) = PjWriteHyp.wcalls t p.
Proof. reflexivity. Qed.

Lemma cm_pjw_nofail : forall t p c, 0 <= c -> c + PjWriteHyp.wcalls t p < 2 ^ 64 ->
  0 <= c < 2 ^ 64 /\
  (forall j, (j < PresetReqAt.wcalls t p)%nat -> (c + Z.of_nat j) mod 2 ^ 64 <> SIZE_MAXZ).
Proof.
intros t p c H0 H1. pose proof (cm_wcalls_nonneg t p). split; [lia|].
intros j Hj. rewrite <- cm_wcalls_req in H1. rewrite Z.mod_small by lia. unfold SIZE_MAXZ. lia.
Qed.

(* ---- the counter at each call stays far below the top: the whole count is below 2 ^ 30 ---- *)
Lemma cm_in_count : forall x t cset, cm_in x t -> 0 <= cset <= 3 -> 0 <= ck_crt_count t cset < 2 ^ 30.
Proof.
intros x t cset Hin Hc. pose proof (cm_in_wf x t Hin) as Hw. pose proof (cm_in_crt_wf x t Hin) as Hw'.
pose proof (cm_tcalls_wlen _ t false Hw) as T0.
pose proof (cm_tcalls_wlen _ (ck_crt_tree t) true Hw') as T1.
pose proof (cm_wcalls_nonneg t false) as N0. pose proof (cm_wcalls_nonneg t true) as N1.
pose proof (cm_wcalls_nonneg (ck_crt_tree t) true) as N2.
destruct (cm_in_wlen_crt x t Hin) as (Lc & _).
destruct Hin as (_ & X1 & X2 & X3).
assert (W0 := cm_wcalls_wlen t false ltac:(lia)). assert (W1 := cm_wcalls_wlen t true ltac:(lia)).
assert (W2 := cm_wcalls_wlen (ck_crt_tree t) true ltac:(unfold PjWriteHyp.wlen; lia)).
unfold PjWriteHyp.wlen in *.
destruct (cm_obj_dec t) as [[ms E]|N].
- rewrite (cm_count_obj t ms cset E). lia.
- rewrite (cm_count_nobj t cset N). lia.
Qed.

Lemma cm_cnt_room : forall x t cset cnt c, cm_in x t -> 0 <= cset <= 3 -> 0 <= cnt < 2 ^ 62 - 2 ^ 30 ->
  cnt <= c <= cnt + ck_crt_count t cset -> 0 <= c < 2 ^ 62.
Proof. intros x t cset cnt c Hin Hc Hn H. pose proof (cm_in_count x t cset Hin Hc). lia. Qed.

(* the whole count from the entry's g_count stays below 2 ^ 62 *)
Lemma cm_cnt_total : forall x t cset cnt, cm_in x t -> 0 <= cset <= 3 -> 0 <= cnt < 2 ^ 62 - 2 ^ 30 ->
  0 <= cnt + ck_crt_count t cset < 2 ^ 62.
Proof. intros x t cset cnt Hin Hc Hn. pose proof (cm_in_count x t cset Hin Hc). lia. Qed.

(* rtt(doc, 1)'s `cnt < 2 ^ 62` at ck_cnt1 *)
Lemma cm_cnt_rtt1 : forall x t cnt, cm_in x t -> 0 <= cnt < 2 ^ 62 - 2 ^ 30 ->
  0 <= cnt + PjWriteHyp.wcalls t false + Z.of_nat (PjRoundTrip.tcalls t) < 2 ^ 62.
Proof.
intros x t cnt Hin Hn. pose proof (cm_pre1 t 0 ltac:(lia)). pose proof (cm_in_count x t 0 Hin ltac:(lia)). lia.
Qed.

(* pj_string's strdup at ck_cnt2 (no wrap), pj_set's `cnt + 3 < 2 ^ 64 - 1` at ck_cnt2 + 1 *)
Lemma cm_cnt_string_set : forall x t ms cnt, cm_in x t -> t = PjTree.JObj ms -> 0 <= cnt < 2 ^ 62 - 2 ^ 30 ->
  0 <= ck_cnt2 cnt t < 2 ^ 64 - 1 /\ ck_cnt2 cnt t + 1 + 3 < 2 ^ 64 - 1.
Proof.
intros x t ms cnt Hin E Hn. pose proof (cm_pre3 t ms 0 E ltac:(lia) 1 ltac:(lia)).
pose proof (cm_in_count x t 0 Hin ltac:(lia)). pose proof (cm_wcalls_nonneg t false). pose proof (cm_wcalls_nonneg t true).
rewrite cm_cnt2_eq. repeat split; lia.
Qed.

(* the rewrite's pj_write from g_count = ck_cnt2 + 1 + cset: its whole run stays below 2 ^ 64 (cm_pjw_cnt's premise) *)
Lemma cm_cnt_write : forall x t ms cset cnt, cm_in x t -> t = PjTree.JObj ms -> 0 <= cset <= 3 ->
  0 <= cnt < 2 ^ 62 - 2 ^ 30 ->
  0 <= ck_cnt2 cnt t + 1 + cset /\ ck_cnt2 cnt t + 1 + cset + PjWriteHyp.wcalls (ck_crt_tree t) true < 2 ^ 64.
Proof.
intros x t ms cset cnt Hin E Hc Hn.
pose proof (cm_pre4 t ms cset (PjWriteHyp.wcalls (ck_crt_tree t) true) E ltac:(lia)
  ltac:(pose proof (cm_wcalls_nonneg (ck_crt_tree t) true); lia)).
pose proof (cm_in_count x t cset Hin Hc). pose proof (cm_wcalls_nonneg t false). pose proof (cm_wcalls_nonneg t true).
rewrite cm_cnt2_eq. repeat split; lia.
Qed.

(* parse_noting's `cnt + 2 * len + 2 < 2 ^ 64 - 1` on the rewrite's text, after k <= wcalls writes *)
Lemma cm_cnt_noting : forall x t ms cset cnt k, cm_in x t -> t = PjTree.JObj ms -> 0 <= cset <= 3 ->
  0 <= cnt < 2 ^ 62 - 2 ^ 30 -> 0 <= k <= PjWriteHyp.wcalls (ck_crt_tree t) true ->
  ck_cnt2 cnt t + 1 + cset + k + 2 * Z.of_nat (length (WriterValue.wdoc (ck_crt_tree t) true)) + 2 < 2 ^ 64 - 1.
Proof.
intros x t ms cset cnt k Hin E Hc Hn Hk. pose proof (cm_pre4 t ms cset k E ltac:(lia) Hk).
pose proof (cm_in_count x t cset Hin Hc). destruct (cm_in_wlen_crt x t Hin) as (_ & L & _).
unfold PRH_FnWriter.prhWriter_WMAX in L. rewrite cm_cnt2_eq. lia.
Qed.

(* the rewrite's pj_write from g_count = ck_cnt2 cnt t + 1 + cset sees no SIZE_MAXZ: pj_write's event supply at the
   model's copy_set *)
Lemma cm_pjw_nofail_crt : forall x t ms cset cnt, cm_in x t -> t = PjTree.JObj ms -> 0 <= cset <= 3 ->
  0 <= cnt < 2 ^ 62 - 2 ^ 30 ->
  0 <= ck_cnt2 cnt t + 1 + cset < 2 ^ 64 /\
  (forall j, (j < PresetReqAt.wcalls (PresetReqAt.copy_set ms) true)%nat ->
     (ck_cnt2 cnt t + 1 + cset + Z.of_nat j) mod 2 ^ 64 <> SIZE_MAXZ).
Proof.
intros x t ms cset cnt Hin E Hc Hn. destruct (cm_cnt_write x t ms cset cnt Hin E Hc Hn) as [W0 W1].
rewrite (cm_crt_tree_copy_set_eq t ms E) in W1.
exact (cm_pjw_nofail (PresetReqAt.copy_set ms) true (ck_cnt2 cnt t + 1 + cset) W0 W1).
Qed.

(* ======================================================================================================== *)
(* 7. the request bounds carried to each call: each callee's request is a zmaxl member of RQA_crt / RQ_crt    *)
(*    (prh_oks' third conjunct and the peak equalities are false above g_most until the E sweep, so each is a    *)
(*    NAMED lemma, applied at its call site)                                                                     *)
(* ======================================================================================================== *)

Lemma zmaxl_nonneg : forall l, 0 <= zmaxl l.
Proof. intros l. unfold zmaxl. induction l as [|a l IH]; cbn [fold_right]; lia. Qed.

Lemma zmaxl_in : forall x l, In x l -> x <= zmaxl l.
Proof.
intros x l. unfold zmaxl. induction l as [|a l IH]; intros H; [contradiction|].
cbn [fold_right]. destruct H as [<-|H]; [lia|]. specialize (IH H). lia.
Qed.

Lemma cm_cap2R_nonneg : forall c, 0 <= c -> 0 <= cap2R c.
Proof. intros c Hc. unfold cap2R. destruct (Z.eqb_spec c 0); lia. Qed.

(* ---- RQA_crt t <= most (the ledger's requests against g_most) ---- *)
Lemma cm_rqa_rtt0 : forall t most, RQA_crt t <= most -> RQA_rtt t false <= most.
Proof.
intros t most H. assert (I : RQA_rtt t false <= RQA_crt t) by (unfold RQA_crt; apply zmaxl_in; left; reflexivity).
lia.
Qed.

Lemma cm_rqa_rtt1 : forall t most, RQA_crt t <= most -> RQA_rtt t true <= most.
Proof.
intros t most H.
assert (I : RQA_rtt t true <= RQA_crt t) by (unfold RQA_crt; apply zmaxl_in; right; left; reflexivity).
lia.
Qed.

(* pj_set's grow: the kids realloc 56 * cap2R n and the keys realloc 8 * cap2R n (n = cap = ck_members t) *)
Lemma cm_rqa_grow : forall t most, RQA_crt t <= most -> 56 * cap2R (ck_members t) <= most.
Proof.
intros t most H.
assert (I : 56 * cap2R (ck_members t) <= RQA_crt t)
  by (unfold RQA_crt; apply zmaxl_in; right; right; left; reflexivity).
lia.
Qed.

Lemma cm_rqa_grow_keys : forall t most, RQA_crt t <= most -> 8 * cap2R (ck_members t) <= most.
Proof.
intros t most H. pose proof (cm_rqa_grow t most H). pose proof (cm_cap2R_nonneg _ (cm_members_nonneg t)). lia.
Qed.

(* pj_string's strdup of the stamp *)
Lemma cm_rqa_stamp : forall t most, RQA_crt t <= most -> Z.of_nat (length ck_STAMP) + 1 <= most.
Proof.
intros t most H.
assert (I : Z.of_nat (length ck_STAMP) + 1 <= RQA_crt t)
  by (unfold RQA_crt; apply zmaxl_in; right; right; right; left; reflexivity).
lia.
Qed.

(* pj_set's strdup of the key (11 <= 21) *)
Lemma cm_rqa_key : forall t most, RQA_crt t <= most -> Z.of_nat (length ck_MOD_AT) + 1 <= most.
Proof.
intros t most H. pose proof (cm_rqa_stamp t most H) as S1.
change (Z.of_nat (length ck_STAMP)) with 20 in S1. change (Z.of_nat (length ck_MOD_AT)) with 10. lia.
Qed.

(* the rewrite's pj_write *)
Lemma cm_rqa_write : forall t most, RQA_crt t <= most -> RQW (ck_crt_tree t) true <= most.
Proof.
intros t most H.
assert (I : RQW (ck_crt_tree t) true <= RQA_crt t)
  by (unfold RQA_crt; apply zmaxl_in; right; right; right; right; left; reflexivity).
lia.
Qed.

(* the rewrite's read-back *)
Lemma cm_rqa_read : forall t most, RQA_crt t <= most ->
  PRH_FnPj.RQ_pj_parse (WriterValue.wdoc (ck_crt_tree t) true) <= most.
Proof.
intros t most H.
assert (I : PRH_FnPj.RQ_pj_parse (WriterValue.wdoc (ck_crt_tree t) true) <= RQA_crt t)
  by (unfold RQA_crt; apply zmaxl_in; right; right; right; right; right; left; reflexivity).
lia.
Qed.

Lemma cm_rqa_nonneg : forall t most, RQA_crt t <= most -> 0 <= most.
Proof. intros t most H. pose proof (zmaxl_nonneg [RQA_rtt t false; RQA_rtt t true; 56 * cap2R (ck_members t);
  Z.of_nat (length ck_STAMP) + 1; RQW (ck_crt_tree t) true;
  PRH_FnPj.RQ_pj_parse (WriterValue.wdoc (ck_crt_tree t) true)]). unfold RQA_crt in H. lia. Qed.

Section rooms. Context {cp : CfParams}.

(* ---- RQ_crt t + cf_head < cf_malloc_max (every request below the allocator's bound), in each callee's own form ---- *)
Lemma cm_rq_rtt0 : forall t, RQ_crt t + cf_head < cf_malloc_max -> RQ_rtt t false + cf_head < cf_malloc_max.
Proof.
intros t H. assert (I : RQ_rtt t false <= RQ_crt t) by (unfold RQ_crt; apply zmaxl_in; left; reflexivity). lia.
Qed.

Lemma cm_rq_rtt1 : forall t, RQ_crt t + cf_head < cf_malloc_max -> RQ_rtt t true + cf_head < cf_malloc_max.
Proof.
intros t H. assert (I : RQ_rtt t true <= RQ_crt t) by (unfold RQ_crt; apply zmaxl_in; right; left; reflexivity).
lia.
Qed.

(* pj_set's `(n = cap -> 56 * cap2R cap + cf_head < cf_malloc_max)` at n = ck_members t *)
Lemma cm_rq_grow : forall t, RQ_crt t + cf_head < cf_malloc_max ->
  forall n cap, n = ck_members t -> n = cap -> 56 * cap2R cap + cf_head < cf_malloc_max.
Proof.
intros t H n cap En Ec. subst cap n.
assert (I : 56 * cap2R (ck_members t) <= RQ_crt t) by (unfold RQ_crt; apply zmaxl_in; right; right; left; reflexivity).
lia.
Qed.

(* pj_string's `Z.of_nat (length cs) + 1 + cf_head < cf_malloc_max` at cs = ck_STAMP *)
Lemma cm_rq_stamp : forall t, RQ_crt t + cf_head < cf_malloc_max ->
  Z.of_nat (length ck_STAMP) + 1 + cf_head < cf_malloc_max.
Proof.
intros t H. assert (I : Z.of_nat (length ck_STAMP) + 1 <= RQ_crt t)
  by (unfold RQ_crt; apply zmaxl_in; right; right; right; left; reflexivity).
lia.
Qed.

(* pj_set's `Z.of_nat (length kname) + 1 + cf_head < cf_malloc_max` at kname = ck_MOD_AT *)
Lemma cm_rq_key : forall t, RQ_crt t + cf_head < cf_malloc_max ->
  Z.of_nat (length ck_MOD_AT) + 1 + cf_head < cf_malloc_max.
Proof.
intros t H. pose proof (cm_rq_stamp t H) as S1.
change (Z.of_nat (length ck_STAMP)) with 20 in S1. change (Z.of_nat (length ck_MOD_AT)) with 10. lia.
Qed.

(* pj_write's `prhWriter_WMAX + cf_head < cf_malloc_max` (a member of RQ_rtt t false) *)
Lemma cm_rq_wmax : forall t, RQ_crt t + cf_head < cf_malloc_max ->
  PRH_FnWriter.prhWriter_WMAX + cf_head < cf_malloc_max.
Proof.
intros t H. pose proof (cm_rq_rtt0 t H) as R.
assert (I : PRH_FnWriter.prhWriter_WMAX <= RQ_rtt t false) by (unfold RQ_rtt; apply zmaxl_in; left; reflexivity).
lia.
Qed.

(* parse_noting's `RQ_pj_parse tb + cf_head < cf_malloc_max` at tb = the rewrite's text *)
Lemma cm_rq_read : forall t, RQ_crt t + cf_head < cf_malloc_max ->
  PRH_FnPj.RQ_pj_parse (WriterValue.wdoc (ck_crt_tree t) true) + cf_head < cf_malloc_max.
Proof.
intros t H. assert (I : PRH_FnPj.RQ_pj_parse (WriterValue.wdoc (ck_crt_tree t) true) <= RQ_crt t)
  by (unfold RQ_crt; apply zmaxl_in; right; right; right; right; left; reflexivity).
lia.
Qed.

(* ---- the live room: the six terms of LIVE_check_round_trip are non-negative, from the callees' own rooms ---- *)
Lemma cm_hpeakR_nonneg : forall tr, 0 <= hpeakR tr.
Proof. intros [|e r]; cbn [hpeakR]; lia. Qed.

Lemma cm_LIVE_pj_parse_nonneg : forall tl, 0 <= PRH_FnPj.LIVE_pj_parse tl.
Proof.
intros tl. unfold PRH_FnPj.LIVE_pj_parse. pose proof (cm_hpeakR_nonneg (PRH_FnPj.prhPj_ptrace tl)).
pose proof cf_head_nonneg. assert (0 <= cf_head * (Z.of_nat (PjGrammar.calls (PRH_FnPj.prhPj_ptrace tl)) + 1)).
{ apply Z.mul_nonneg_nonneg; lia. }
lia.
Qed.

Lemma cm_LIVE_pj_write_nonneg : forall t p, 0 <= PRH_FnWriter.LIVE_pj_write t p.
Proof.
intros t p. unfold PRH_FnWriter.LIVE_pj_write.
pose proof (cm_newcap0_ge (Z.of_nat (length (WriterValue.wdoc t p)) + 1)). pose proof cf_head_nonneg. lia.
Qed.

Lemma cm_LIVE_rtt_nonneg : forall t p, 0 <= LIVE_round_trip_text t p.
Proof.
intros t p. unfold LIVE_round_trip_text, PRH_FnTx.LIVE_tx.
pose proof (cm_LIVE_pj_write_nonneg t p). pose proof (cm_LIVE_pj_parse_nonneg (WriterValue.wdoc t p)). lia.
Qed.

Lemma cm_LIVE_string_nonneg : forall len, 0 <= len -> 0 <= PRH_FnPj.LIVE_pj_string len.
Proof. intros len H. unfold PRH_FnPj.LIVE_pj_string. pose proof cf_head_nonneg. lia. Qed.

Lemma cm_LIVE_grow_nonneg : forall cap, 0 <= cap -> 0 <= PRH_FnReader.LIVE_grow 6 cap.
Proof.
intros cap H. unfold PRH_FnReader.LIVE_grow. rewrite Z.eqb_refl. pose proof (cm_cap2R_nonneg cap H).
pose proof cf_head_nonneg. lia.
Qed.

Lemma cm_LIVE_set_nonneg : forall n cap klen, 0 <= cap -> 0 <= klen -> 0 <= PRH_FnPj.LIVE_pj_set n cap klen.
Proof.
intros n cap klen Hc Hk. unfold PRH_FnPj.LIVE_pj_set. pose proof (cm_LIVE_grow_nonneg cap Hc).
pose proof cf_head_nonneg. destruct (n =? cap); lia.
Qed.

(* pj_set's room is largest when the slots are full (cap = n) *)
Lemma cm_LIVE_set_le : forall n cap klen, 0 <= n -> PRH_FnPj.LIVE_pj_set n cap klen <= PRH_FnPj.LIVE_pj_set n n klen.
Proof.
intros n cap klen Hn. unfold PRH_FnPj.LIVE_pj_set at 2. rewrite Z.eqb_refl. unfold PRH_FnPj.LIVE_pj_set.
destruct (Z.eqb_spec n cap) as [<-|_]; [lia|]. pose proof (cm_LIVE_grow_nonneg n Hn). lia.
Qed.

Lemma cm_LIVE_crt_terms : forall t,
  0 <= LIVE_round_trip_text t false /\ 0 <= LIVE_round_trip_text t true /\
  0 <= PRH_FnPj.LIVE_pj_string (Z.of_nat (length ck_STAMP)) /\
  0 <= PRH_FnPj.LIVE_pj_set (ck_members t) (ck_members t) (Z.of_nat (length ck_MOD_AT)) /\
  0 <= PRH_FnWriter.LIVE_pj_write (ck_crt_tree t) true /\
  0 <= PRH_FnPj.LIVE_pj_parse (WriterValue.wdoc (ck_crt_tree t) true).
Proof.
intros t. split; [apply cm_LIVE_rtt_nonneg|]. split; [apply cm_LIVE_rtt_nonneg|].
split; [apply cm_LIVE_string_nonneg; lia|].
split; [apply cm_LIVE_set_nonneg; [apply cm_members_nonneg|lia]|].
split; [apply cm_LIVE_pj_write_nonneg|]. apply cm_LIVE_pj_parse_nonneg.
Qed.

(* the six terms, as an equation: rewriting with it keeps the kernel off a conversion of LIVE_check_round_trip
   against a sum, which unfolds Z.add first and costs half a minute per use (measured) *)
Lemma cm_LIVE_crt_eq : forall t, LIVE_check_round_trip t =
  LIVE_round_trip_text t false + LIVE_round_trip_text t true +
  PRH_FnPj.LIVE_pj_string (Z.of_nat (length ck_STAMP)) +
  PRH_FnPj.LIVE_pj_set (ck_members t) (ck_members t) (Z.of_nat (length ck_MOD_AT)) +
  PRH_FnWriter.LIVE_pj_write (ck_crt_tree t) true + PRH_FnPj.LIVE_pj_parse (WriterValue.wdoc (ck_crt_tree t) true).
Proof. intros t. unfold LIVE_check_round_trip. reflexivity. Qed.

(* ---- the live room at each call: from `b + LIVE_check_round_trip t <= LIVE_MAX` (b = blocks_bytes S at entry)
   and the bytes live at the call (b'), bounded by b plus the rooms of the calls already made in the body's order
   (the walk's own obligation) ---- *)
Lemma cm_live_rtt0 : forall t b b', b + LIVE_check_round_trip t <= LIVE_MAX -> b' <= b ->
  b' + LIVE_round_trip_text t false <= LIVE_MAX.
Proof.
intros t b b' H Hb. pose proof (cm_LIVE_crt_terms t) as (N1 & N2 & N3 & N4 & N5 & N6).
rewrite cm_LIVE_crt_eq in H. lia.
Qed.

Lemma cm_live_rtt1 : forall t b b', b + LIVE_check_round_trip t <= LIVE_MAX ->
  b' <= b + LIVE_round_trip_text t false ->
  b' + LIVE_round_trip_text t true <= LIVE_MAX.
Proof.
intros t b b' H Hb. pose proof (cm_LIVE_crt_terms t) as (N1 & N2 & N3 & N4 & N5 & N6).
rewrite cm_LIVE_crt_eq in H. lia.
Qed.

Lemma cm_live_string : forall t b b', b + LIVE_check_round_trip t <= LIVE_MAX ->
  b' <= b + LIVE_round_trip_text t false + LIVE_round_trip_text t true ->
  b' + PRH_FnPj.LIVE_pj_string (Z.of_nat (length ck_STAMP)) <= LIVE_MAX.
Proof.
intros t b b' H Hb. pose proof (cm_LIVE_crt_terms t) as (N1 & N2 & N3 & N4 & N5 & N6).
rewrite cm_LIVE_crt_eq in H. lia.
Qed.

(* pj_set at the copy's header (n, cap), n = ck_members t: any cap *)
Lemma cm_live_set : forall t b b', b + LIVE_check_round_trip t <= LIVE_MAX ->
  b' <= b + LIVE_round_trip_text t false + LIVE_round_trip_text t true +
        PRH_FnPj.LIVE_pj_string (Z.of_nat (length ck_STAMP)) ->
  forall n cap, n = ck_members t -> b' + PRH_FnPj.LIVE_pj_set n cap (Z.of_nat (length ck_MOD_AT)) <= LIVE_MAX.
Proof.
intros t b b' H Hb n cap En. pose proof (cm_LIVE_crt_terms t) as (N1 & N2 & N3 & N4 & N5 & N6).
pose proof (cm_LIVE_set_le n cap (Z.of_nat (length ck_MOD_AT)) ltac:(subst n; apply cm_members_nonneg)) as Le.
subst n. rewrite cm_LIVE_crt_eq in H. lia.
Qed.

Lemma cm_live_write : forall t b b', b + LIVE_check_round_trip t <= LIVE_MAX ->
  b' <= b + LIVE_round_trip_text t false + LIVE_round_trip_text t true +
        PRH_FnPj.LIVE_pj_string (Z.of_nat (length ck_STAMP)) +
        PRH_FnPj.LIVE_pj_set (ck_members t) (ck_members t) (Z.of_nat (length ck_MOD_AT)) ->
  b' + PRH_FnWriter.LIVE_pj_write (ck_crt_tree t) true <= LIVE_MAX.
Proof.
intros t b b' H Hb. pose proof (cm_LIVE_crt_terms t) as (N1 & N2 & N3 & N4 & N5 & N6).
rewrite cm_LIVE_crt_eq in H. lia.
Qed.

Lemma cm_live_read : forall t b b', b + LIVE_check_round_trip t <= LIVE_MAX ->
  b' <= b + LIVE_round_trip_text t false + LIVE_round_trip_text t true +
        PRH_FnPj.LIVE_pj_string (Z.of_nat (length ck_STAMP)) +
        PRH_FnPj.LIVE_pj_set (ck_members t) (ck_members t) (Z.of_nat (length ck_MOD_AT)) +
        PRH_FnWriter.LIVE_pj_write (ck_crt_tree t) true ->
  b' + PRH_FnPj.LIVE_pj_parse (WriterValue.wdoc (ck_crt_tree t) true) <= LIVE_MAX.
Proof.
intros t b b' H Hb. pose proof (cm_LIVE_crt_terms t) as (N1 & N2 & N3 & N4 & N5 & N6).
rewrite cm_LIVE_crt_eq in H. lia.
Qed.

(* ---- the bytes harness blocks occupy as allocator blocks (heads included, YCbq.bsum (ck_hblks D); with
   YCbq.blocks_bytes_bsum and a boundary's `Permutation (ablocks ..) (ablocks B ly S ++ ck_hblks Dx)` this is
   blocks_bytes Sc - blocks_bytes S), and the bound of each Dx the body holds at a call ---- *)
Lemma cm_lsum_perm : forall D D', Permutation D D' -> Ledger.lsum D = Ledger.lsum D'.
Proof.
intros D D' P. induction P as [|[a k] l l' P IH|[a k] [b j] l|l l' l'' P1 IH1 P2 IH2]; cbn [Ledger.lsum]; lia.
Qed.

Lemma cm_lsum_app : forall D1 D2, Ledger.lsum (D1 ++ D2) = Ledger.lsum D1 + Ledger.lsum D2.
Proof. induction D1 as [|[a k] D1 IH]; intros D2; cbn [app Ledger.lsum]; [lia|]. rewrite IH. lia. Qed.

Lemma cm_bsum_hblks : forall D, YCbq.bsum (ck_hblks D) = Ledger.lsum D + cf_head * Z.of_nat (length D).
Proof.
unfold ck_hblks, YCbq.bsum. induction D as [|[a k] D IH]; cbn [map fold_right Ledger.lsum length fst snd]; [lia|].
rewrite IH, Nat2Z.inj_succ, Z.mul_succ_r. lia.
Qed.

Lemma cm_bsum_hblks_app : forall D1 D2,
  YCbq.bsum (ck_hblks (D1 ++ D2)) = YCbq.bsum (ck_hblks D1) + YCbq.bsum (ck_hblks D2).
Proof.
intros D1 D2. rewrite !cm_bsum_hblks, cm_lsum_app, length_app, Nat2Z.inj_add, Z.mul_add_distr_l. lia.
Qed.

Lemma cm_bsum_hblks_perm : forall D D', Permutation D D' -> YCbq.bsum (ck_hblks D) = YCbq.bsum (ck_hblks D').
Proof. intros D D' P. rewrite !cm_bsum_hblks, (cm_lsum_perm D D' P), (Permutation_length P). reflexivity. Qed.

(* the compact copy rtt(doc, 0) leaves in `copy` (its blocks Db: the read-back's live sizes, ttrace t) fits in
   rtt(doc, 0)'s own read-back room *)
Lemma cm_copy_room : forall t Db, PjRoundTrip.pj_wf ReaderRes.jr_strtod t ->
  Permutation (map snd Db) (map Z.of_nat (ReaderRes.lsz (PjRoundTrip.ttrace t))) ->
  Z.of_nat (length Db) = ReaderRes.nlive (PjRoundTrip.ttrace t) ->
  YCbq.bsum (ck_hblks Db) <= PRH_FnPj.LIVE_pj_parse (WriterValue.wdoc t false).
Proof.
intros t Db Hw HP HN. rewrite cm_bsum_hblks, (ReaderRes.lsz_counts Db _ HP HN), HN.
unfold PRH_FnPj.LIVE_pj_parse. rewrite (cm_ptrace_wf t false Hw).
pose proof (cm_held_le_hpeakR (PjRoundTrip.ttrace t)). pose proof (cm_hpeakR_nonneg (PjRoundTrip.ttrace t)).
pose proof (cm_nlive_le_calls (PjRoundTrip.ttrace t)). pose proof cf_head_nonneg.
assert (cf_head * ReaderRes.nlive (PjRoundTrip.ttrace t) <=
        cf_head * (Z.of_nat (PjGrammar.calls (PjRoundTrip.ttrace t)) + 1)) by (apply Z.mul_le_mono_nonneg_l; lia).
lia.
Qed.

Lemma cm_copy_room_rtt : forall t Db, PjRoundTrip.pj_wf ReaderRes.jr_strtod t ->
  Permutation (map snd Db) (map Z.of_nat (ReaderRes.lsz (PjRoundTrip.ttrace t))) ->
  Z.of_nat (length Db) = ReaderRes.nlive (PjRoundTrip.ttrace t) ->
  YCbq.bsum (ck_hblks Db) <= LIVE_round_trip_text t false.
Proof.
intros t Db Hw HP HN. pose proof (cm_copy_room t Db Hw HP HN).
unfold LIVE_round_trip_text, PRH_FnTx.LIVE_tx. pose proof (cm_LIVE_pj_write_nonneg t false). lia.
Qed.

Lemma cm_live_le_rtt0 : forall t, LIVE_round_trip_text t false <= LIVE_check_round_trip t.
Proof. intros t. pose proof (cm_LIVE_crt_terms t) as (N1 & N2 & N3 & N4 & N5 & N6). rewrite cm_LIVE_crt_eq. lia. Qed.

(* rtt(doc, 1) runs with the copy live *)
Lemma cm_live_rtt1_copy : forall t Db, PjRoundTrip.pj_wf ReaderRes.jr_strtod t ->
  Permutation (map snd Db) (map Z.of_nat (ReaderRes.lsz (PjRoundTrip.ttrace t))) ->
  Z.of_nat (length Db) = ReaderRes.nlive (PjRoundTrip.ttrace t) ->
  YCbq.bsum (ck_hblks Db) + LIVE_round_trip_text t true <= LIVE_check_round_trip t.
Proof.
intros t Db Hw HP HN. pose proof (cm_copy_room_rtt t Db Hw HP HN).
pose proof (cm_LIVE_crt_terms t) as (N1 & N2 & N3 & N4 & N5 & N6). rewrite cm_LIVE_crt_eq. lia.
Qed.

(* pj_string's new block is exactly pj_string's room *)
Lemma cm_stamp_block : forall a,
  YCbq.bsum (ck_hblks [(a, Z.of_nat (length ck_STAMP) + 1)]) = PRH_FnPj.LIVE_pj_string (Z.of_nat (length ck_STAMP)).
Proof.
intros a. rewrite cm_bsum_hblks. cbn [Ledger.lsum length]. change (Z.of_nat 1) with 1.
unfold PRH_FnPj.LIVE_pj_string. lia.
Qed.

(* pj_set's new blocks: the two grown arrays and the key (n = cap) are exactly pj_set's room at n = cap; the key
   alone (n < cap) is within it at any cap *)
Lemma cm_set_grow_blocks : forall cap k' y' a',
  YCbq.bsum (ck_hblks [(k', 56 * cap2R cap); (y', 8 * cap2R cap); (a', Z.of_nat (length ck_MOD_AT) + 1)]) =
  PRH_FnPj.LIVE_pj_set cap cap (Z.of_nat (length ck_MOD_AT)).
Proof.
intros cap k' y' a'. rewrite cm_bsum_hblks. cbn [Ledger.lsum length]. change (Z.of_nat 3) with 3.
unfold PRH_FnPj.LIVE_pj_set, PRH_FnReader.LIVE_grow. rewrite !Z.eqb_refl. lia.
Qed.

Lemma cm_set_key_block : forall n cap a', 0 <= cap ->
  YCbq.bsum (ck_hblks [(a', Z.of_nat (length ck_MOD_AT) + 1)]) <= PRH_FnPj.LIVE_pj_set n cap (Z.of_nat (length ck_MOD_AT)).
Proof.
intros n cap a' Hc. rewrite cm_bsum_hblks. cbn [Ledger.lsum length]. change (Z.of_nat 1) with 1.
unfold PRH_FnPj.LIVE_pj_set. pose proof (cm_LIVE_grow_nonneg cap Hc). destruct (n =? cap); lia.
Qed.

(* the saved text's buffer (saved, w_cap) of an unfailed pj_write is within pj_write's room (parse_noting's room at
   the rewrite's read-back holds it beside the copy) *)
Lemma cm_pjw_cap : forall ok cnt fail t p, Z.of_nat (length (WriterValue.wdoc t p)) + 1 <= 2 ^ 62 ->
  WriterApp.w_failed (PRH_FnWriter.prhWriter_putN ok (WriterApp.w0 cnt fail) (WriterValue.wdpieces t p)) = 0 ->
  0 <= WriterApp.w_cap (PRH_FnWriter.prhWriter_putN ok (WriterApp.w0 cnt fail) (WriterValue.wdpieces t p)) /\
  WriterApp.w_cap (PRH_FnWriter.prhWriter_putN ok (WriterApp.w0 cnt fail) (WriterValue.wdpieces t p)) + cf_head <=
    PRH_FnWriter.LIVE_pj_write t p.
Proof.
intros ok cnt fail t p Hl Hs.
rewrite (cm_wput_cap (WriterValue.wdpieces t p) ok (WriterApp.w0 cnt fail) eq_refl Hs).
change (Z.of_nat (length (WriterApp.w_text (WriterApp.w0 cnt fail)))) with 0.
change (WriterApp.w_cap (WriterApp.w0 cnt fail)) with 0.
pose proof (cm_gcap_le (WriterSpec.piece_lens (WriterValue.wdpieces t p)) 0 0 ltac:(lia) ltac:(lia)
  (cm_lens_nn _) ltac:(lia)) as G.
rewrite cm_lens_sum in G.
pose proof (cm_gcap_nn (WriterSpec.piece_lens (WriterValue.wdpieces t p)) 0 0 ltac:(lia)) as Gn.
unfold PRH_FnWriter.LIVE_pj_write. unfold WriterValue.wdoc in *.
pose proof (cm_newcap0_ge (Z.of_nat (length (concat (WriterValue.wdpieces t p))) + 1)) as N1.
pose proof (cm_newcap_reach 0 (Z.of_nat (length (concat (WriterValue.wdpieces t p))) + 1) ltac:(lia) ltac:(lia)) as N2.
pose proof cf_head_nonneg. split; lia.
Qed.

End rooms.

(* ======================================================================================================== *)
(* 8. the frames bound: FR_check_round_trip = 1 + FR_round_trip_text, so the text's bound leaves room for the   *)
(*    function's own frame (__asan_stack_malloc_3) and then gives each callee's                                *)
(* ======================================================================================================== *)

Lemma cm_FR_crt : FR_check_round_trip = 1 + FR_round_trip_text.
Proof. reflexivity. Qed.

(* BEFORE the frame is pushed: one more frame still leaves round_trip_text's bound *)
Lemma cm_frames_before : forall n : nat, Z.of_nat n <= ck_FRAMES_CAP - FR_check_round_trip ->
  Z.of_nat n + 1 <= ck_FRAMES_CAP - FR_round_trip_text.
Proof. intros n H. rewrite cm_FR_crt in H. lia. Qed.

(* AFTER it is pushed (one more frame in the list): round_trip_text's bound, at both calls *)
Lemma cm_frames_after : forall (A : Type) (fr fr' : list A),
  Z.of_nat (length fr) <= ck_FRAMES_CAP - FR_check_round_trip -> length fr' = Datatypes.S (length fr) ->
  Z.of_nat (length fr') <= ck_FRAMES_CAP - FR_round_trip_text.
Proof. intros A fr fr' H E. rewrite E. pose proof (cm_frames_before (length fr) H). lia. Qed.

Lemma cm_frames_after_perm : forall (A : Type) (fr fr' : list A) (f : A),
  Z.of_nat (length fr) <= ck_FRAMES_CAP - FR_check_round_trip -> Permutation fr' (f :: fr) ->
  Z.of_nat (length fr') <= ck_FRAMES_CAP - FR_round_trip_text.
Proof.
intros A fr fr' f H P. apply (cm_frames_after A fr fr' H). rewrite (Permutation_length P). reflexivity.
Qed.

(* the rewrite's read-back (parse_noting) with the function's own frame held *)
Lemma cm_frames_noting : forall n : Z, n <= ck_FRAMES_CAP - FR_round_trip_text -> n <= ck_FRAMES_CAP - FR_parse_noting.
Proof. intros n H. unfold FR_round_trip_text, FR_parse_noting in *. lia. Qed.

(* the fake-stack class-0 capacity the reader's and the writer's texts ask (pj_parse:
   `length (frames S) + DOC_D <= fs_frames 0`; pj_write: `length (frames S) < fs_frames 0`) *)
Lemma cm_frames_fs0 : forall n : Z, n <= ck_FRAMES_CAP -> n < fs_frames 0 /\ n + Z.of_nat DOC_D <= fs_frames 0.
Proof.
intros n H. assert (E : fs_frames 0 = 16384) by reflexivity. rewrite E.
change (Z.of_nat DOC_D) with 33. unfold ck_FRAMES_CAP in H. lia.
Qed.

(* ======================================================================================================== *)
(* 9. the copy's capacity, read off its blocks: a tree whose blocks (with their heads) are the model's tblk has  *)
(*    the model's capacity in its header (PresetReqAtNoMiss.tblk f949715d7a12 :628-636, its first two blocks the  *)
(*    kids and keys arrays of capacity capf 0 0 |ms| = PresetReqAt.ncap |ms|, PresetReqAtNoMiss.ncap_eq :620)     *)
(* ======================================================================================================== *)

(* a value below 2 ^ (8 w) is fixed by its w low bytes *)
Lemma cm_bytes_det : forall (w : nat) z1 z2, 0 <= z1 < 2 ^ (8 * Z.of_nat w) -> 0 <= z2 < 2 ^ (8 * Z.of_nat w) ->
  (forall k, (k < w)%nat -> (z1 / 2 ^ (8 * Z.of_nat k)) mod 256 = (z2 / 2 ^ (8 * Z.of_nat k)) mod 256) -> z1 = z2.
Proof.
induction w as [|w IH]; intros z1 z2 H1 H2 Hk.
- change (2 ^ (8 * Z.of_nat 0)) with 1 in H1, H2. lia.
- assert (E : forall j : nat, 2 ^ (8 * Z.of_nat (Datatypes.S j)) = 256 * 2 ^ (8 * Z.of_nat j)).
  { intros j. rewrite Nat2Z.inj_succ, Z.mul_succ_r, Z.pow_add_r by lia. change (2 ^ 8) with 256. lia. }
  assert (Pw : 0 < 2 ^ (8 * Z.of_nat w)) by (apply Z.pow_pos_nonneg; lia).
  pose proof (Hk 0%nat ltac:(lia)) as H0. change (2 ^ (8 * Z.of_nat 0)) with 1 in H0. rewrite !Z.div_1_r in H0.
  rewrite E in H1, H2.
  assert (Q : z1 / 256 = z2 / 256).
  { apply IH.
    - split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia.
    - split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia.
    - intros k Hkw.
      assert (Pk : 0 < 2 ^ (8 * Z.of_nat k)) by (apply Z.pow_pos_nonneg; lia).
      rewrite !Z.div_div by lia. rewrite <- E. exact (Hk (Datatypes.S k) ltac:(lia)). }
  pose proof (Z.div_mod z1 256 ltac:(lia)). pose proof (Z.div_mod z2 256 ltac:(lia)). lia.
Qed.

(* a word read twice is one value *)
Lemma cm_rd_u64_det : forall segs m a v1 v2, rd_u64 segs m a v1 -> rd_u64 segs m a v2 -> v1 = v2.
Proof.
intros segs m a v1 v2 [R1 V1] [R2 V2].
apply (cm_bytes_det 8); [exact R1|exact R2|]. intros k Hk.
pose proof (V1 k Hk) as B1. pose proof (V2 k Hk) as B2. rewrite B1 in B2.
assert (B : Z_to_bv 8 (YO0f.le_byte v1 8 k) = Z_to_bv 8 (YO0f.le_byte v2 8 k)) by congruence.
apply (f_equal bv_unsigned) in B. rewrite !Z_to_bv_unsigned in B.
rewrite !bv_wrap_small in B by (unfold YO0f.le_byte, bv_modulus; apply Z.mod_pos_bound; lia).
unfold YO0f.le_byte in B. change (8 * Z.of_nat 8) with 64 in B.
rewrite (Z.mod_small v1 (2 ^ 64)), (Z.mod_small v2 (2 ^ 64)) in B by lia.
rewrite !Z.shiftr_div_pow2 in B by lia. first [exact B | symmetry; exact B].
Qed.

Lemma cm_gcap_pos : forall n cap, (1 <= PjRoundTrip.gcap n cap)%nat.
Proof.
intros n cap. unfold PjRoundTrip.gcap. destruct (Nat.ltb_spec n cap); [lia|]. destruct (Nat.eqb_spec cap 0); lia.
Qed.

Lemma cm_capf_pos : forall k, (1 <= PresetReqAtNoMiss.capf 0 0 (Datatypes.S k))%nat.
Proof. intros k. rewrite <- PresetReqAtNoMiss.ncap_eq. cbn [PresetReqAt.ncap]. apply cm_gcap_pos. Qed.

Lemma cm_arrz_pos : forall c, (1 <= c)%nat ->
  PresetReqAt.arrz true c = [Z.of_nat (56 * c) + PresetReqAt.HEAD; Z.of_nat (8 * c) + PresetReqAt.HEAD].
Proof. intros [|c] H; [lia|]. reflexivity. Qed.

Section rep. Context {cp : CfParams}.

(* pj_set's cap at the copy: the header's cap is the model's capacity of an object of |ms| members *)
Lemma cm_cap_of_tblk : forall segs m lblk p ms D num str kids keys n cap,
  cf_head = PresetReqAt.HEAD ->
  pj_nodeR segs m lblk p (PjTree.JObj ms) D ->
  map (fun b => snd b + cf_head) D = PresetReqAtNoMiss.tblk (PjTree.JObj ms) ->
  pj_hdrR segs m p 6 num str kids keys n cap ->
  cap = Z.of_nat (PresetReqAt.ncap (length ms)).
Proof.
intros segs m lblk p ms D num str kids keys n cap Hh HN HT HH.
cbn [pj_nodeR] in HN.
destruct HN as (_ & _ & num' & str' & kids' & keys' & n' & cap' & HH' & _ & En & Hnc & _ & Di & ED & _).
assert (Ecap : cap = cap').
{ destruct HH as (_ & _ & _ & _ & _ & _ & _ & C). destruct HH' as (_ & _ & _ & _ & _ & _ & _ & C').
  exact (cm_rd_u64_det segs m (p + 48) cap cap' C C'). }
subst cap'. rewrite PresetReqAtNoMiss.ncap_eq.
cbn [PresetReqAtNoMiss.tblk] in HT. rewrite ED, map_app in HT.
destruct ms as [|m0 ms'].
- destruct (Z.eqb_spec cap 0) as [->|Hne]; [reflexivity|].
  try rewrite (proj2 (Z.eqb_neq cap 0) Hne) in HT. cbn [map app snd] in HT. discriminate HT.
- cbn [length] in En, HT |- *.
  rewrite (proj2 (Z.eqb_neq cap 0)) in HT by lia.
  pose proof (cm_capf_pos (length ms')) as Hp. rewrite (cm_arrz_pos _ Hp) in HT.
  remember (PresetReqAtNoMiss.capf 0 0 (Datatypes.S (length ms'))) as c eqn:Ec.
  cbn [map app snd] in HT. apply (f_equal (@hd Z 0)) in HT. cbn [hd] in HT. lia.
Qed.

End rep.
