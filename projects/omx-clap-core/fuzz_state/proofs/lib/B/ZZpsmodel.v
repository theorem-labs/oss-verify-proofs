(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: IMAGE B (fs.asan-ubsan) walk of parse_value 0x82fcc, stage lemmas. HEADER: see
   FSW_parse_value_holds.v (the composition into parse_value_spec k, the rule-24 line, the reuse search, the port
   sources, every pc walked and every report site). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/B/Prog/FSW_parse_value.v, with its module names and numbers changed; 1163 of its 1272 lines of code are new or changed and 1247 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: lib/B (fs.asan-ubsan, image B) twin of lib/A/FSW_put_string.v at
   a working branch ca67007c8c2 (a Theorem Labs lane), and another Theorem Labs lane: same lemma names and statement shapes;
   imports point at lib/B's image files and walk kit (YB1v, YB1w, FSH_Base, FSH_Rt, FSPstat, FSH_Fn_writer,
   FSW_K, FSW_K3, FSW_ret, FSW_frame, FSW_frame3, FSW_rd, FSW_strkit and lib/B's put_string files); the
   image-agnostic FSupoison, FSupoisonU, FSupoisonStack, FSH_YC20, FSH_Gen and FSW_writer_model stay lib/A's.
   Every address, cut, branch, offset and register of put_string's own code is RE-MEASURED on image B
   (A_put_string 0x85fc8, 928 bytes; the neutral excerpt put_string.fuzz_state.asan-ubsan.s), never copied.
   rule 24: proves no function (kind: segment lemma). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/B/FSW_put_string.v; 537 of its 624 lines of code are new or changed and 1185 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: lib/B (fs.asan-ubsan, image B) twin of lib/A/ZZpsmodel.v at
   a working branch ca67007c8c2 (a Theorem Labs lane), and another Theorem Labs lane: same lemma names and statement shapes;
   imports point at lib/B's image files and walk kit (YB1v, YB1w, FSH_Base, FSH_Rt, FSPstat, FSH_Fn_writer,
   FSW_K, FSW_K3, FSW_ret, FSW_frame, FSW_frame3, FSW_rd, FSW_strkit and lib/B's put_string files); the
   image-agnostic FSupoison, FSupoisonU, FSupoisonStack, FSH_YC20, FSH_Gen and FSW_writer_model stay lib/A's.
   Every address, cut, branch, offset and register of put_string's own code is RE-MEASURED on image B
   (A_put_string 0x85fc8, 928 bytes; the neutral excerpt put_string.fuzz_state.asan-ubsan.s), never copied.
   rule 24: proves no function (kind: segment lemma). *)
(* put_string, a Theorem Labs lane, piece R6 (image-agnostic text, used unchanged on image B):
   the MODEL ALGEBRA that glues the walk's three put calls into put_string_spec's single post (lib/B/FSH_Fn_writer.v).

   put_string_spec states its post for ONE model state
     st = WriterApp.putN (WriterApp.mkW failed text cap cnt fail []) (WriterSpec.spieces bs)
   and ONE journal count `wevk cap st`. The walk reaches it through three put calls (the opening quote [34], the
   bytes bs, the closing quote [34]); each call's post (put_spec, via FSW_put_string.ps_put_call) reports
     s_i = WriterApp.put1 (WriterApp.mkW failed_i text_i cap_i cnt_i fail_i []) b_i
   with a FRESH call list, where the i-th call starts from the fields of s_(i-1). Every lemma below takes that chain
   as three equations (E1 E2 E3, the form put's post hands back), so the walk can pass its own equations.

   What is here (all `psm_`):
   1. psm_put1_calls   put1 never reads its incoming call list and only extends it.
   2. psm_three        the composite is the three-fold put1; psm_three_chain / psm_fields read it as s3's fields
                       with the call lists of s1, s2, s3 appended.
   3. psm_wcalls_add   wcalls of the composite is the sum.
   4. psm_wevk_add     the journal count telescopes. PURE MODEL: no AR, no premise beyond the chain.
   5. psm_wbudget_pre  the spec's one budget premise gives each call's (psm_wbudget_pre1/2/3, one per call site).
   6. psm_wbudget_kept the three kept facts compose into the spec's one.
   7. psm_bswap        bswap composes (psm_bswap2: two calls; psm_bswap_mid: the per-MIDDLE-state premises from AR).
   8. psm_uswap        uswap composes (psm_uswap2: two calls; psm_uswap_mid: the per-MIDDLE-state premises from ARU).
   9. psm_peak         the peak clause composes, fs_glob included.

   FINDING (items 7 and 8, reported to a Theorem Labs lane 2026-10-29, accepted): neither swap relation composes on its own.
   - uswap with only `pairwise zdisjoint U1`: cap = 0, U0 = [], call 1 takes arm 3 (U1 = [(b1 - 16, 16)], pairwise
     holds), call 2 at cap1 = 0 takes arm 3 again (U2 = [(b1 - 16, 16); (b2 - 16, 16)]); `uswap U0 U2 b0 b2 0` is
     false (arm 3 appends exactly one head). Also arm 1 then arm 3 needs cap1 = 0 -> cap0 = 0, which uswap does not
     record (cap monotonicity of the model gives it).
   - bswap: arm 2 then arm 2 at cap1 = 0 inserts two blocks (false by length); arm 2/3 then arm 3 needs the middle
     block (b1 - 16, cap1 + 16) to occur ONCE in the middle list (A1 = [x; y; x] is a counter-case).
   The extra premises are facts the walk holds at each MIDDLE state: `w_cap s_i = 0 -> buf_i = 0` (put's wout_ok),
   AR / ARU there (live blocks start at 4096 or above and are pairwise disjoint; every head lies in a live block).
   uswap and bswap themselves are unchanged.

   Templates (case structure only; every proof here is written fresh): a Theorem Labs lane's ZZwv_comp.v:351-421
   (wv_bswap_trans / wv_uswap_trans, a working branch b28b3e2d1bd) and a Theorem Labs lane's
   FSW_pj_write.v:2571-2755 (pjw_c_wev_split, pjw_c_split_uniq, pjw_c_bswap_comp, pjw_c_uswap_comp,
   a working branch f5d78102c21). Released lemmas reused by name: FSW_writer_model.spieces_plain,
   WriterRet.put1_cap, WriterRet.put1_failed, WriterApp.putN_cons / putN_nil, YG0d.al_blocks through
   YG0q.AR_laws_ok, YCbq.req_size_pos.
   Rule 24 (2026-10-29, git grep -n -w -E 'psm_[a-z0-9_]+' -- 'proofs/*', each ref's own exit code, output to a
   file): origin/main f4cc67298b7, origin/ossv/recipes e5e7eba2cc0, origin/ossv/candidates ee89628c997,
   origin/release/pau-projects-recipes b6a0088adcb have NO hit for any name defined here; the only psm_ names
   there are psm_sm / psm_facts / psm_grows / psm_in / psm_out (boost-beast, glaze), unrelated.
   Sink probes (Fail Definition probe_SK / probe_SH at top level) compiled in this file at commit time and were
   removed before it, as the lane asks. *)

From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0s YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
FSupoison FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
FSH_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require
FSW_writer_model.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require
FSH_Fn_writer.
(* lib/Prog modules are Required, never Imported (a Theorem Labs lane 21:43Z) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec WriterApp WriterRet.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* ================= 1. put1 and the incoming call list ================= *)
(* the same state with an empty call list: what each put call of the walk starts from *)
Definition psm_rs (st : WriterApp.wst) : WriterApp.wst :=
  WriterApp.mkW (WriterApp.w_failed st) (WriterApp.w_text st) (WriterApp.w_cap st)
    (WriterApp.w_cnt st) (WriterApp.w_fail st) [].

Lemma psm_put1_eq : forall st b,
  WriterApp.put1 st b =
  WriterApp.mkW (WriterApp.w_failed (WriterApp.put1 (psm_rs st) b))
    (WriterApp.w_text (WriterApp.put1 (psm_rs st) b)) (WriterApp.w_cap (WriterApp.put1 (psm_rs st) b))
    (WriterApp.w_cnt (WriterApp.put1 (psm_rs st) b)) (WriterApp.w_fail (WriterApp.put1 (psm_rs st) b))
    (WriterApp.w_calls st ++ WriterApp.w_calls (WriterApp.put1 (psm_rs st) b)).
Proof.
  intros [f t c n fl cs] b. unfold psm_rs, WriterApp.put1.
  cbn [WriterApp.w_failed WriterApp.w_text WriterApp.w_cap WriterApp.w_cnt WriterApp.w_fail WriterApp.w_calls].
  destruct (negb (f =? 0)).
  - cbn [WriterApp.w_failed WriterApp.w_text WriterApp.w_cap WriterApp.w_cnt WriterApp.w_fail WriterApp.w_calls].
    rewrite app_nil_r. reflexivity.
  - destruct (Z.of_nat (length t) + Z.of_nat (length b) + 1 <=? c).
    + cbn [WriterApp.w_failed WriterApp.w_text WriterApp.w_cap WriterApp.w_cnt WriterApp.w_fail WriterApp.w_calls].
      rewrite app_nil_r. reflexivity.
    + destruct (n =? fl);
        cbn [WriterApp.w_failed WriterApp.w_text WriterApp.w_cap WriterApp.w_cnt WriterApp.w_fail WriterApp.w_calls
             app]; reflexivity.
Qed.

(* ITEM 1 *)
Lemma psm_put1_calls : forall f t c n fl (calls : list Z) b,
  WriterApp.w_failed (WriterApp.put1 (WriterApp.mkW f t c n fl calls) b)
    = WriterApp.w_failed (WriterApp.put1 (WriterApp.mkW f t c n fl []) b) /\
  WriterApp.w_text (WriterApp.put1 (WriterApp.mkW f t c n fl calls) b)
    = WriterApp.w_text (WriterApp.put1 (WriterApp.mkW f t c n fl []) b) /\
  WriterApp.w_cap (WriterApp.put1 (WriterApp.mkW f t c n fl calls) b)
    = WriterApp.w_cap (WriterApp.put1 (WriterApp.mkW f t c n fl []) b) /\
  WriterApp.w_cnt (WriterApp.put1 (WriterApp.mkW f t c n fl calls) b)
    = WriterApp.w_cnt (WriterApp.put1 (WriterApp.mkW f t c n fl []) b) /\
  WriterApp.w_fail (WriterApp.put1 (WriterApp.mkW f t c n fl calls) b)
    = WriterApp.w_fail (WriterApp.put1 (WriterApp.mkW f t c n fl []) b) /\
  WriterApp.w_calls (WriterApp.put1 (WriterApp.mkW f t c n fl calls) b)
    = calls ++ WriterApp.w_calls (WriterApp.put1 (WriterApp.mkW f t c n fl []) b).
Proof.
  intros f t c n fl calls b. rewrite (psm_put1_eq (WriterApp.mkW f t c n fl calls) b). unfold psm_rs.
  cbn [WriterApp.w_failed WriterApp.w_text WriterApp.w_cap WriterApp.w_cnt WriterApp.w_fail WriterApp.w_calls].
  repeat split; reflexivity.
Qed.

Lemma psm_rs_put1 : forall st b, psm_rs (WriterApp.put1 st b) = psm_rs (WriterApp.put1 (psm_rs st) b).
Proof. intros st b. rewrite (psm_put1_eq st b). reflexivity. Qed.

(* ================= 2. the composite is the walk's three calls ================= *)
(* ITEM 2 *)
Lemma psm_three : forall failed text cap cnt fail bs, plain_bytes bs ->
  WriterApp.putN (WriterApp.mkW failed text cap cnt fail []) (WriterSpec.spieces bs) =
  WriterApp.put1 (WriterApp.put1 (WriterApp.put1 (WriterApp.mkW failed text cap cnt fail []) [34]) bs) [34].
Proof.
  intros failed text cap cnt fail bs H. rewrite (FSW_writer_model.spieces_plain bs H).
  rewrite !WriterApp.putN_cons, WriterApp.putN_nil. reflexivity.
Qed.

(* any three pieces: the composite of the chain s1 -> s2 -> s3 (each from the previous one's fields, with no calls)
   is s3's fields with the three call lists appended *)
Lemma psm_chain : forall failed text cap cnt fail (b1 b2 b3 : list Z) s1 s2 s3,
  s1 = WriterApp.put1 (WriterApp.mkW failed text cap cnt fail []) b1 ->
  s2 = WriterApp.put1 (WriterApp.mkW (WriterApp.w_failed s1) (WriterApp.w_text s1) (WriterApp.w_cap s1)
                         (WriterApp.w_cnt s1) (WriterApp.w_fail s1) []) b2 ->
  s3 = WriterApp.put1 (WriterApp.mkW (WriterApp.w_failed s2) (WriterApp.w_text s2) (WriterApp.w_cap s2)
                         (WriterApp.w_cnt s2) (WriterApp.w_fail s2) []) b3 ->
  WriterApp.put1 (WriterApp.put1 s1 b2) b3 =
  WriterApp.mkW (WriterApp.w_failed s3) (WriterApp.w_text s3) (WriterApp.w_cap s3)
    (WriterApp.w_cnt s3) (WriterApp.w_fail s3)
    (WriterApp.w_calls s1 ++ WriterApp.w_calls s2 ++ WriterApp.w_calls s3).
Proof.
  intros failed text cap cnt fail b1 b2 b3 s1 s2 s3 _ E2 E3. subst s3 s2.
  rewrite (psm_put1_eq (WriterApp.put1 s1 b2) b3), (psm_put1_eq s1 b2). unfold psm_rs.
  cbn [WriterApp.w_failed WriterApp.w_text WriterApp.w_cap WriterApp.w_cnt WriterApp.w_fail WriterApp.w_calls].
  rewrite <- app_assoc. reflexivity.
Qed.

Lemma psm_three_chain : forall failed text cap cnt fail bs s1 s2 s3, plain_bytes bs ->
  s1 = WriterApp.put1 (WriterApp.mkW failed text cap cnt fail []) [34] ->
  s2 = WriterApp.put1 (WriterApp.mkW (WriterApp.w_failed s1) (WriterApp.w_text s1) (WriterApp.w_cap s1)
                         (WriterApp.w_cnt s1) (WriterApp.w_fail s1) []) bs ->
  s3 = WriterApp.put1 (WriterApp.mkW (WriterApp.w_failed s2) (WriterApp.w_text s2) (WriterApp.w_cap s2)
                         (WriterApp.w_cnt s2) (WriterApp.w_fail s2) []) [34] ->
  WriterApp.putN (WriterApp.mkW failed text cap cnt fail []) (WriterSpec.spieces bs) =
  WriterApp.mkW (WriterApp.w_failed s3) (WriterApp.w_text s3) (WriterApp.w_cap s3)
    (WriterApp.w_cnt s3) (WriterApp.w_fail s3)
    (WriterApp.w_calls s1 ++ WriterApp.w_calls s2 ++ WriterApp.w_calls s3).
Proof.
  intros failed text cap cnt fail bs s1 s2 s3 H E1 E2 E3.
  rewrite (psm_three failed text cap cnt fail bs H), <- E1.
  exact (psm_chain failed text cap cnt fail [34] bs [34] s1 s2 s3 E1 E2 E3).
Qed.

(* the five fields the spec's post reads are the last call's *)
Lemma psm_fields : forall failed text cap cnt fail bs s1 s2 s3, plain_bytes bs ->
  s1 = WriterApp.put1 (WriterApp.mkW failed text cap cnt fail []) [34] ->
  s2 = WriterApp.put1 (WriterApp.mkW (WriterApp.w_failed s1) (WriterApp.w_text s1) (WriterApp.w_cap s1)
                         (WriterApp.w_cnt s1) (WriterApp.w_fail s1) []) bs ->
  s3 = WriterApp.put1 (WriterApp.mkW (WriterApp.w_failed s2) (WriterApp.w_text s2) (WriterApp.w_cap s2)
                         (WriterApp.w_cnt s2) (WriterApp.w_fail s2) []) [34] ->
  WriterApp.w_failed (WriterApp.putN (WriterApp.mkW failed text cap cnt fail []) (WriterSpec.spieces bs))
    = WriterApp.w_failed s3 /\
  WriterApp.w_text (WriterApp.putN (WriterApp.mkW failed text cap cnt fail []) (WriterSpec.spieces bs))
    = WriterApp.w_text s3 /\
  WriterApp.w_cap (WriterApp.putN (WriterApp.mkW failed text cap cnt fail []) (WriterSpec.spieces bs))
    = WriterApp.w_cap s3 /\
  WriterApp.w_cnt (WriterApp.putN (WriterApp.mkW failed text cap cnt fail []) (WriterSpec.spieces bs))
    = WriterApp.w_cnt s3 /\
  WriterApp.w_fail (WriterApp.putN (WriterApp.mkW failed text cap cnt fail []) (WriterSpec.spieces bs))
    = WriterApp.w_fail s3 /\
  WriterApp.w_calls (WriterApp.putN (WriterApp.mkW failed text cap cnt fail []) (WriterSpec.spieces bs))
    = WriterApp.w_calls s1 ++ WriterApp.w_calls s2 ++ WriterApp.w_calls s3.
Proof.
  intros failed text cap cnt fail bs s1 s2 s3 H E1 E2 E3.
  rewrite (psm_three_chain failed text cap cnt fail bs s1 s2 s3 H E1 E2 E3).
  cbn [WriterApp.w_failed WriterApp.w_text WriterApp.w_cap WriterApp.w_cnt WriterApp.w_fail WriterApp.w_calls].
  repeat split; reflexivity.
Qed.

(* ================= 3. the request count adds up ================= *)
Lemma psm_wcalls_nonneg : forall st, 0 <= FSH_Fn_writer.wcalls st.
Proof. intros st. unfold FSH_Fn_writer.wcalls. lia. Qed.

(* ITEM 3 *)
Lemma psm_wcalls_add : forall failed text cap cnt fail bs s1 s2 s3, plain_bytes bs ->
  s1 = WriterApp.put1 (WriterApp.mkW failed text cap cnt fail []) [34] ->
  s2 = WriterApp.put1 (WriterApp.mkW (WriterApp.w_failed s1) (WriterApp.w_text s1) (WriterApp.w_cap s1)
                         (WriterApp.w_cnt s1) (WriterApp.w_fail s1) []) bs ->
  s3 = WriterApp.put1 (WriterApp.mkW (WriterApp.w_failed s2) (WriterApp.w_text s2) (WriterApp.w_cap s2)
                         (WriterApp.w_cnt s2) (WriterApp.w_fail s2) []) [34] ->
  FSH_Fn_writer.wcalls (WriterApp.putN (WriterApp.mkW failed text cap cnt fail []) (WriterSpec.spieces bs)) =
  FSH_Fn_writer.wcalls s1 + FSH_Fn_writer.wcalls s2 + FSH_Fn_writer.wcalls s3.
Proof.
  intros failed text cap cnt fail bs s1 s2 s3 H E1 E2 E3. unfold FSH_Fn_writer.wcalls.
  rewrite (psm_three_chain failed text cap cnt fail bs s1 s2 s3 H E1 E2 E3).
  cbn [WriterApp.w_calls]. rewrite !length_app, !Nat2Z.inj_add. lia.
Qed.

(* ================= 4. the journal count telescopes (pure model) ================= *)
Lemma psm_dbl_nz : forall f c need, c <> 0 -> WriterSpec.dbl f c need <> 0.
Proof.
  induction f as [|f IH]; intros c need Hc; cbn [WriterSpec.dbl]; [exact Hc|].
  destruct (need <=? c); [exact Hc | apply IH; lia].
Qed.

Lemma psm_newcap_nz : forall c need, WriterSpec.newcap c need <> 0.
Proof.
  intros c need. unfold WriterSpec.newcap. apply psm_dbl_nz. destruct (Z.eqb_spec c 0); lia.
Qed.

(* what a call list says about the cap, relative to the cap c the composite started from: a nonzero cap stays
   nonzero; at c = 0, no request yet means the cap is still 0, and a request that left the cap at 0 was refused
   (failed is set, so every later put1 is the identity) *)
Definition psm_inv (c : Z) (st : WriterApp.wst) : Prop :=
  (c <> 0 -> WriterApp.w_cap st <> 0) /\
  (c = 0 -> WriterApp.w_calls st = [] -> WriterApp.w_cap st = 0) /\
  (c = 0 -> WriterApp.w_calls st <> [] -> WriterApp.w_cap st = 0 -> WriterApp.w_failed st <> 0).

Lemma psm_inv_init : forall f t c n fl, psm_inv c (WriterApp.mkW f t c n fl []).
Proof.
  intros f t c n fl. unfold psm_inv.
  cbn [WriterApp.w_failed WriterApp.w_text WriterApp.w_cap WriterApp.w_cnt WriterApp.w_fail WriterApp.w_calls].
  split; [intros H; exact H|]. split; [intros H _; exact H|]. intros _ H; exfalso; apply H; reflexivity.
Qed.

Lemma psm_inv_step : forall c st b, psm_inv c st -> psm_inv c (WriterApp.put1 st b).
Proof.
  intros c [f t cp n fl cs] b H. unfold WriterApp.put1.
  cbn [WriterApp.w_failed WriterApp.w_text WriterApp.w_cap WriterApp.w_cnt WriterApp.w_fail WriterApp.w_calls].
  destruct (negb (f =? 0)) eqn:Ef; [exact H|].
  apply negb_false_iff, Z.eqb_eq in Ef. subst f.
  destruct H as (I1 & I2 & I3).
  cbn [WriterApp.w_failed WriterApp.w_text WriterApp.w_cap WriterApp.w_cnt WriterApp.w_fail WriterApp.w_calls]
    in I1, I2, I3.
  destruct (Z.of_nat (length t) + Z.of_nat (length b) + 1 <=? cp).
  - unfold psm_inv.
    cbn [WriterApp.w_failed WriterApp.w_text WriterApp.w_cap WriterApp.w_cnt WriterApp.w_fail WriterApp.w_calls].
    split; [exact I1|]. split; [exact I2|].
    intros Hc Hcs Hcp. exfalso. exact (I3 Hc Hcs Hcp eq_refl).
  - destruct (n =? fl); unfold psm_inv;
      cbn [WriterApp.w_failed WriterApp.w_text WriterApp.w_cap WriterApp.w_cnt WriterApp.w_fail WriterApp.w_calls].
    + split; [exact I1|]. split; [intros _ E; destruct cs; discriminate E|]. intros _ _ _. lia.
    + split; [intros _; apply psm_newcap_nz|]. split; [intros _ E; destruct cs; discriminate E|].
      intros _ _ E. exfalso. exact (psm_newcap_nz _ _ E).
Qed.

Lemma psm_wevk_step : forall c st b, psm_inv c st ->
  FSH_Fn_writer.wevk c (WriterApp.put1 st b) =
  FSH_Fn_writer.wevk c st + FSH_Fn_writer.wevk (WriterApp.w_cap st) (WriterApp.put1 (psm_rs st) b).
Proof.
  intros c st b (I1 & I2 & I3).
  rewrite (psm_put1_eq st b).
  set (s' := WriterApp.put1 (psm_rs st) b).
  unfold FSH_Fn_writer.wevk, FSH_Fn_writer.wev0, FSH_Fn_writer.wcalls.
  cbn [WriterApp.w_calls]. unfold EV_fuzz_malloc, EV_fuzz_realloc.
  destruct (Z.eqb_spec c 0) as [Hc|Hc]; cbv beta iota.
  - destruct (WriterApp.w_calls st) as [|x r] eqn:Ecs.
    + rewrite (I2 Hc eq_refl), Z.eqb_refl. cbv beta iota. cbn [app].
      destruct (WriterApp.w_calls s'); cbv beta iota; lia.
    + cbn [app]. destruct (Z.eqb_spec (WriterApp.w_cap st) 0) as [Hcap|Hcap]; cbv beta iota.
      * assert (Hf : WriterApp.w_failed st <> 0)
          by (apply (I3 Hc); [try rewrite Ecs; discriminate | exact Hcap]).
        assert (Es : WriterApp.w_calls s' = []).
        { unfold s'. rewrite (WriterRet.put1_failed (psm_rs st) b) by (unfold psm_rs; exact Hf).
          unfold psm_rs. reflexivity. }
        rewrite Es, app_nil_r. cbv beta iota. lia.
      * rewrite length_app, Nat2Z.inj_add. lia.
  - rewrite (proj2 (Z.eqb_neq _ _) (I1 Hc)). cbv beta iota.
    rewrite length_app, Nat2Z.inj_add. lia.
Qed.

Lemma psm_wevk_nonneg : forall c st, 0 <= FSH_Fn_writer.wevk c st.
Proof.
  intros c st. unfold FSH_Fn_writer.wevk, FSH_Fn_writer.wev0, FSH_Fn_writer.wcalls, EV_fuzz_malloc, EV_fuzz_realloc.
  destruct (c =? 0); [destruct (WriterApp.w_calls st)|]; cbv beta iota; lia.
Qed.

(* ITEM 4. No premise beyond the chain: at cap <> 0 every call is at a nonzero cap; at cap = 0 either the first put
   allocates (and every later call is at a nonzero cap) or it is refused (failed is set and the later calls make no
   request) or failed was already set (no call makes a request). psm_inv carries all three orders. *)
Lemma psm_wevk_add : forall failed text cap cnt fail bs s1 s2 s3, plain_bytes bs ->
  s1 = WriterApp.put1 (WriterApp.mkW failed text cap cnt fail []) [34] ->
  s2 = WriterApp.put1 (WriterApp.mkW (WriterApp.w_failed s1) (WriterApp.w_text s1) (WriterApp.w_cap s1)
                         (WriterApp.w_cnt s1) (WriterApp.w_fail s1) []) bs ->
  s3 = WriterApp.put1 (WriterApp.mkW (WriterApp.w_failed s2) (WriterApp.w_text s2) (WriterApp.w_cap s2)
                         (WriterApp.w_cnt s2) (WriterApp.w_fail s2) []) [34] ->
  FSH_Fn_writer.wevk cap (WriterApp.putN (WriterApp.mkW failed text cap cnt fail []) (WriterSpec.spieces bs)) =
  FSH_Fn_writer.wevk cap s1 + FSH_Fn_writer.wevk (WriterApp.w_cap s1) s2
    + FSH_Fn_writer.wevk (WriterApp.w_cap s2) s3.
Proof.
  intros failed text cap cnt fail bs s1 s2 s3 H E1 E2 E3.
  rewrite (psm_three failed text cap cnt fail bs H), <- E1.
  assert (I1 : psm_inv cap s1) by (rewrite E1; apply psm_inv_step, psm_inv_init).
  assert (I2 : psm_inv cap (WriterApp.put1 s1 bs)) by (apply psm_inv_step; exact I1).
  rewrite (psm_wevk_step cap (WriterApp.put1 s1 bs) [34] I2), (psm_wevk_step cap s1 bs I1).
  rewrite (psm_rs_put1 s1 bs).
  assert (Es2 : WriterApp.put1 (psm_rs s1) bs = s2) by (rewrite E2; reflexivity).
  assert (Ec2 : WriterApp.w_cap (WriterApp.put1 s1 bs) = WriterApp.w_cap s2)
    by (rewrite (psm_put1_eq s1 bs), Es2; reflexivity).
  assert (Es3 : WriterApp.put1 (psm_rs s2) [34] = s3) by (rewrite E3; reflexivity).
  rewrite Ec2, Es2, Es3. reflexivity.
Qed.

(* ================= 5. the budget premise at each call site ================= *)
(* the count rises by the requests one put makes (no wrap: the budget premise bounds it) *)
Lemma psm_cnt1 : forall f t c n fl b, 0 <= n ->
  n + FSH_Fn_writer.wcalls (WriterApp.put1 (WriterApp.mkW f t c n fl []) b) < 2 ^ 64 ->
  WriterApp.w_cnt (WriterApp.put1 (WriterApp.mkW f t c n fl []) b) =
  n + FSH_Fn_writer.wcalls (WriterApp.put1 (WriterApp.mkW f t c n fl []) b).
Proof.
  intros f t c n fl b Hn. unfold FSH_Fn_writer.wcalls, WriterApp.put1.
  cbn [WriterApp.w_failed WriterApp.w_text WriterApp.w_cap WriterApp.w_cnt WriterApp.w_fail WriterApp.w_calls].
  destruct (negb (f =? 0));
    [cbn [WriterApp.w_failed WriterApp.w_text WriterApp.w_cap WriterApp.w_cnt WriterApp.w_fail WriterApp.w_calls
          length]; lia|].
  destruct (Z.of_nat (length t) + Z.of_nat (length b) + 1 <=? c);
    [cbn [WriterApp.w_failed WriterApp.w_text WriterApp.w_cap WriterApp.w_cnt WriterApp.w_fail WriterApp.w_calls
          length]; lia|].
  destruct (n =? fl);
    cbn [WriterApp.w_failed WriterApp.w_text WriterApp.w_cap WriterApp.w_cnt WriterApp.w_fail WriterApp.w_calls
         app length]; intros Hb; rewrite Z.mod_small by lia; lia.
Qed.

(* the caps along the chain never fall (from a nonnegative start: newcap doubles) *)
Lemma psm_caps : forall failed text cap cnt fail (b1 b2 b3 : list Z) s1 s2 s3, 0 <= cap ->
  s1 = WriterApp.put1 (WriterApp.mkW failed text cap cnt fail []) b1 ->
  s2 = WriterApp.put1 (WriterApp.mkW (WriterApp.w_failed s1) (WriterApp.w_text s1) (WriterApp.w_cap s1)
                         (WriterApp.w_cnt s1) (WriterApp.w_fail s1) []) b2 ->
  s3 = WriterApp.put1 (WriterApp.mkW (WriterApp.w_failed s2) (WriterApp.w_text s2) (WriterApp.w_cap s2)
                         (WriterApp.w_cnt s2) (WriterApp.w_fail s2) []) b3 ->
  cap <= WriterApp.w_cap s1 /\ WriterApp.w_cap s1 <= WriterApp.w_cap s2 /\
  WriterApp.w_cap s2 <= WriterApp.w_cap s3.
Proof.
  intros failed text cap cnt fail b1 b2 b3 s1 s2 s3 Hc E1 E2 E3.
  assert (C1 : cap <= WriterApp.w_cap s1)
    by (rewrite E1; exact (WriterRet.put1_cap (WriterApp.mkW failed text cap cnt fail []) b1 Hc)).
  assert (C2 : WriterApp.w_cap s1 <= WriterApp.w_cap s2).
  { rewrite E2. exact (WriterRet.put1_cap (WriterApp.mkW (WriterApp.w_failed s1) (WriterApp.w_text s1)
      (WriterApp.w_cap s1) (WriterApp.w_cnt s1) (WriterApp.w_fail s1) []) b2 ltac:(cbn [WriterApp.w_cap]; lia)). }
  assert (C3 : WriterApp.w_cap s2 <= WriterApp.w_cap s3).
  { rewrite E3. exact (WriterRet.put1_cap (WriterApp.mkW (WriterApp.w_failed s2) (WriterApp.w_text s2)
      (WriterApp.w_cap s2) (WriterApp.w_cnt s2) (WriterApp.w_fail s2) []) b3 ltac:(cbn [WriterApp.w_cap]; lia)). }
  split; [exact C1|]. split; [exact C2 | exact C3].
Qed.

(* call 1 (the opening quote), at the state S1 of the call: put_string's own steps before it journal nothing
   and allocate nothing (FSW_put_string.ps_to_put1 gives st_nev S1 = st_nev S, blocks_bytes S1 = blocks_bytes S) *)
Lemma psm_wbudget_pre1 : forall S S1 failed text cap cnt fail live bs s1 s2 s3,
  plain_bytes bs -> 0 <= cap ->
  s1 = WriterApp.put1 (WriterApp.mkW failed text cap cnt fail []) [34] ->
  s2 = WriterApp.put1 (WriterApp.mkW (WriterApp.w_failed s1) (WriterApp.w_text s1) (WriterApp.w_cap s1)
                         (WriterApp.w_cnt s1) (WriterApp.w_fail s1) []) bs ->
  s3 = WriterApp.put1 (WriterApp.mkW (WriterApp.w_failed s2) (WriterApp.w_text s2) (WriterApp.w_cap s2)
                         (WriterApp.w_cnt s2) (WriterApp.w_fail s2) []) [34] ->
  FSH_Fn_writer.wbudget_pre S cap cnt live
    (WriterApp.putN (WriterApp.mkW failed text cap cnt fail []) (WriterSpec.spieces bs)) ->
  st_nev S1 <= st_nev S -> blocks_bytes S1 <= blocks_bytes S ->
  FSH_Fn_writer.wbudget_pre S1 cap cnt live s1.
Proof.
  intros S S1 failed text cap cnt fail live bs s1 s2 s3 Hpb Hc E1 E2 E3 (H1 & H2 & H3 & H4) Hn Hb.
  rewrite (psm_wevk_add failed text cap cnt fail bs s1 s2 s3 Hpb E1 E2 E3) in H1.
  rewrite (psm_wcalls_add failed text cap cnt fail bs s1 s2 s3 Hpb E1 E2 E3) in H4.
  destruct (psm_fields failed text cap cnt fail bs s1 s2 s3 Hpb E1 E2 E3) as (_ & _ & Ecap & _).
  rewrite Ecap in H2, H3.
  destruct (psm_caps failed text cap cnt fail [34] bs [34] s1 s2 s3 Hc E1 E2 E3) as (C1 & C2 & C3).
  pose proof (psm_wevk_nonneg (WriterApp.w_cap s1) s2). pose proof (psm_wevk_nonneg (WriterApp.w_cap s2) s3).
  pose proof (psm_wcalls_nonneg s2). pose proof (psm_wcalls_nonneg s3).
  unfold FSH_Fn_writer.wbudget_pre. split; [lia|]. split; [lia|]. split; lia.
Qed.

(* call 2 (the bytes), at its state S2, with the live count put #1 returned *)
Lemma psm_wbudget_pre2 : forall S S2 failed text cap cnt fail live L2 bs s1 s2 s3,
  plain_bytes bs -> 0 <= cap -> 0 <= cnt ->
  s1 = WriterApp.put1 (WriterApp.mkW failed text cap cnt fail []) [34] ->
  s2 = WriterApp.put1 (WriterApp.mkW (WriterApp.w_failed s1) (WriterApp.w_text s1) (WriterApp.w_cap s1)
                         (WriterApp.w_cnt s1) (WriterApp.w_fail s1) []) bs ->
  s3 = WriterApp.put1 (WriterApp.mkW (WriterApp.w_failed s2) (WriterApp.w_text s2) (WriterApp.w_cap s2)
                         (WriterApp.w_cnt s2) (WriterApp.w_fail s2) []) [34] ->
  FSH_Fn_writer.wbudget_pre S cap cnt live
    (WriterApp.putN (WriterApp.mkW failed text cap cnt fail []) (WriterSpec.spieces bs)) ->
  L2 = live + WriterApp.w_cap s1 - cap ->
  st_nev S2 <= st_nev S + FSH_Fn_writer.wevk cap s1 ->
  blocks_bytes S2 - FSH_Fn_writer.bsz (WriterApp.w_cap s1) <= blocks_bytes S - FSH_Fn_writer.bsz cap ->
  FSH_Fn_writer.wbudget_pre S2 (WriterApp.w_cap s1) (WriterApp.w_cnt s1) L2 s2.
Proof.
  intros S S2 failed text cap cnt fail live L2 bs s1 s2 s3 Hpb Hc Hn0 E1 E2 E3 (H1 & H2 & H3 & H4) EL Hn Hb.
  rewrite (psm_wevk_add failed text cap cnt fail bs s1 s2 s3 Hpb E1 E2 E3) in H1.
  rewrite (psm_wcalls_add failed text cap cnt fail bs s1 s2 s3 Hpb E1 E2 E3) in H4.
  destruct (psm_fields failed text cap cnt fail bs s1 s2 s3 Hpb E1 E2 E3) as (_ & _ & Ecap & _).
  rewrite Ecap in H2, H3.
  destruct (psm_caps failed text cap cnt fail [34] bs [34] s1 s2 s3 Hc E1 E2 E3) as (C1 & C2 & C3).
  pose proof (psm_wevk_nonneg (WriterApp.w_cap s2) s3).
  pose proof (psm_wcalls_nonneg s1). pose proof (psm_wcalls_nonneg s2). pose proof (psm_wcalls_nonneg s3).
  assert (Ecnt : WriterApp.w_cnt s1 = cnt + FSH_Fn_writer.wcalls s1).
  { pose proof (psm_cnt1 failed text cap cnt fail [34] Hn0) as K. rewrite <- E1 in K. apply K. lia. }
  unfold FSH_Fn_writer.wbudget_pre. split; [lia|]. split; [lia|]. split; lia.
Qed.

(* call 3 (the closing quote), at its state S3, with the live count put #2 returned *)
Lemma psm_wbudget_pre3 : forall S S3 failed text cap cnt fail live L2 L3 bs s1 s2 s3,
  plain_bytes bs -> 0 <= cap -> 0 <= cnt ->
  s1 = WriterApp.put1 (WriterApp.mkW failed text cap cnt fail []) [34] ->
  s2 = WriterApp.put1 (WriterApp.mkW (WriterApp.w_failed s1) (WriterApp.w_text s1) (WriterApp.w_cap s1)
                         (WriterApp.w_cnt s1) (WriterApp.w_fail s1) []) bs ->
  s3 = WriterApp.put1 (WriterApp.mkW (WriterApp.w_failed s2) (WriterApp.w_text s2) (WriterApp.w_cap s2)
                         (WriterApp.w_cnt s2) (WriterApp.w_fail s2) []) [34] ->
  FSH_Fn_writer.wbudget_pre S cap cnt live
    (WriterApp.putN (WriterApp.mkW failed text cap cnt fail []) (WriterSpec.spieces bs)) ->
  L2 = live + WriterApp.w_cap s1 - cap -> L3 = L2 + WriterApp.w_cap s2 - WriterApp.w_cap s1 ->
  st_nev S3 <= st_nev S + FSH_Fn_writer.wevk cap s1 + FSH_Fn_writer.wevk (WriterApp.w_cap s1) s2 ->
  blocks_bytes S3 - FSH_Fn_writer.bsz (WriterApp.w_cap s2) <= blocks_bytes S - FSH_Fn_writer.bsz cap ->
  FSH_Fn_writer.wbudget_pre S3 (WriterApp.w_cap s2) (WriterApp.w_cnt s2) L3 s3.
Proof.
  intros S S3 failed text cap cnt fail live L2 L3 bs s1 s2 s3 Hpb Hc Hn0 E1 E2 E3 (H1 & H2 & H3 & H4) EL2 EL3
    Hn Hb.
  rewrite (psm_wevk_add failed text cap cnt fail bs s1 s2 s3 Hpb E1 E2 E3) in H1.
  rewrite (psm_wcalls_add failed text cap cnt fail bs s1 s2 s3 Hpb E1 E2 E3) in H4.
  destruct (psm_fields failed text cap cnt fail bs s1 s2 s3 Hpb E1 E2 E3) as (_ & _ & Ecap & _).
  rewrite Ecap in H2, H3.
  destruct (psm_caps failed text cap cnt fail [34] bs [34] s1 s2 s3 Hc E1 E2 E3) as (C1 & C2 & C3).
  pose proof (psm_wcalls_nonneg s1). pose proof (psm_wcalls_nonneg s2). pose proof (psm_wcalls_nonneg s3).
  assert (Ecnt1 : WriterApp.w_cnt s1 = cnt + FSH_Fn_writer.wcalls s1).
  { pose proof (psm_cnt1 failed text cap cnt fail [34] Hn0) as K. rewrite <- E1 in K. apply K. lia. }
  assert (Ecnt2 : WriterApp.w_cnt s2 = WriterApp.w_cnt s1 + FSH_Fn_writer.wcalls s2).
  { pose proof (psm_cnt1 (WriterApp.w_failed s1) (WriterApp.w_text s1) (WriterApp.w_cap s1)
      (WriterApp.w_cnt s1) (WriterApp.w_fail s1) bs ltac:(lia)) as K. rewrite <- E2 in K. apply K. lia. }
  unfold FSH_Fn_writer.wbudget_pre. split; [lia|]. split; [lia|]. split; lia.
Qed.

(* ITEM 5: the three, one per call site (each conjunct takes only what is known at its own call) *)
Lemma psm_wbudget_pre : forall S failed text cap cnt fail live bs s1 s2 s3,
  plain_bytes bs -> 0 <= cap -> 0 <= cnt ->
  s1 = WriterApp.put1 (WriterApp.mkW failed text cap cnt fail []) [34] ->
  s2 = WriterApp.put1 (WriterApp.mkW (WriterApp.w_failed s1) (WriterApp.w_text s1) (WriterApp.w_cap s1)
                         (WriterApp.w_cnt s1) (WriterApp.w_fail s1) []) bs ->
  s3 = WriterApp.put1 (WriterApp.mkW (WriterApp.w_failed s2) (WriterApp.w_text s2) (WriterApp.w_cap s2)
                         (WriterApp.w_cnt s2) (WriterApp.w_fail s2) []) [34] ->
  FSH_Fn_writer.wbudget_pre S cap cnt live
    (WriterApp.putN (WriterApp.mkW failed text cap cnt fail []) (WriterSpec.spieces bs)) ->
  (forall S1, st_nev S1 <= st_nev S -> blocks_bytes S1 <= blocks_bytes S ->
     FSH_Fn_writer.wbudget_pre S1 cap cnt live s1) /\
  (forall S2 L2, L2 = live + WriterApp.w_cap s1 - cap ->
     st_nev S2 <= st_nev S + FSH_Fn_writer.wevk cap s1 ->
     blocks_bytes S2 - FSH_Fn_writer.bsz (WriterApp.w_cap s1) <= blocks_bytes S - FSH_Fn_writer.bsz cap ->
     FSH_Fn_writer.wbudget_pre S2 (WriterApp.w_cap s1) (WriterApp.w_cnt s1) L2 s2) /\
  (forall S3 L2 L3, L2 = live + WriterApp.w_cap s1 - cap -> L3 = L2 + WriterApp.w_cap s2 - WriterApp.w_cap s1 ->
     st_nev S3 <= st_nev S + FSH_Fn_writer.wevk cap s1 + FSH_Fn_writer.wevk (WriterApp.w_cap s1) s2 ->
     blocks_bytes S3 - FSH_Fn_writer.bsz (WriterApp.w_cap s2) <= blocks_bytes S - FSH_Fn_writer.bsz cap ->
     FSH_Fn_writer.wbudget_pre S3 (WriterApp.w_cap s2) (WriterApp.w_cnt s2) L3 s3).
Proof.
  intros S failed text cap cnt fail live bs s1 s2 s3 Hpb Hc Hn0 E1 E2 E3 HB.
  split; [intros S1; exact (psm_wbudget_pre1 S S1 failed text cap cnt fail live bs s1 s2 s3 Hpb Hc E1 E2 E3 HB)|].
  split; [intros S2 L2;
          exact (psm_wbudget_pre2 S S2 failed text cap cnt fail live L2 bs s1 s2 s3 Hpb Hc Hn0 E1 E2 E3 HB)|].
  intros S3 L2 L3. exact (psm_wbudget_pre3 S S3 failed text cap cnt fail live L2 L3 bs s1 s2 s3 Hpb Hc Hn0 E1 E2 E3 HB).
Qed.

(* ================= 6. the kept budget facts compose ================= *)
(* two calls, the second starting from a state S2 that holds no more allocated bytes than the first one's return *)
Lemma psm_wbudget_kept2 : forall S1 R1 S2 R2 f0 c0 n0 f1 c1 n1 f2 c2 n2,
  FSH_Fn_writer.wbudget_kept S1 R1 f0 c0 n0 f1 c1 n1 -> blocks_bytes S2 <= blocks_bytes R1 ->
  FSH_Fn_writer.wbudget_kept S2 R2 f1 c1 n1 f2 c2 n2 ->
  FSH_Fn_writer.wbudget_kept S1 R2 f0 c0 n0 f2 c2 n2.
Proof.
  unfold FSH_Fn_writer.wbudget_kept.
  intros S1 R1 S2 R2 f0 c0 n0 f1 c1 n1 f2 c2 n2 (A1 & A2 & A3) Hb (B1 & B2 & B3).
  split; [exact B1|]. split; lia.
Qed.

(* ITEM 6: the walk's three kept facts (S_i the state at call i, R_i its return, S' the state the spec's post reads)
   give the spec's one *)
Lemma psm_wbudget_kept : forall S S1 R1 S2 R2 S3 R3 S' failed text cap cnt fail bs s1 s2 s3,
  plain_bytes bs ->
  s1 = WriterApp.put1 (WriterApp.mkW failed text cap cnt fail []) [34] ->
  s2 = WriterApp.put1 (WriterApp.mkW (WriterApp.w_failed s1) (WriterApp.w_text s1) (WriterApp.w_cap s1)
                         (WriterApp.w_cnt s1) (WriterApp.w_fail s1) []) bs ->
  s3 = WriterApp.put1 (WriterApp.mkW (WriterApp.w_failed s2) (WriterApp.w_text s2) (WriterApp.w_cap s2)
                         (WriterApp.w_cnt s2) (WriterApp.w_fail s2) []) [34] ->
  blocks_bytes S1 <= blocks_bytes S ->
  FSH_Fn_writer.wbudget_kept S1 R1 failed cap cnt
    (WriterApp.w_failed s1) (WriterApp.w_cap s1) (WriterApp.w_cnt s1) ->
  blocks_bytes S2 <= blocks_bytes R1 ->
  FSH_Fn_writer.wbudget_kept S2 R2 (WriterApp.w_failed s1) (WriterApp.w_cap s1) (WriterApp.w_cnt s1)
    (WriterApp.w_failed s2) (WriterApp.w_cap s2) (WriterApp.w_cnt s2) ->
  blocks_bytes S3 <= blocks_bytes R2 ->
  FSH_Fn_writer.wbudget_kept S3 R3 (WriterApp.w_failed s2) (WriterApp.w_cap s2) (WriterApp.w_cnt s2)
    (WriterApp.w_failed s3) (WriterApp.w_cap s3) (WriterApp.w_cnt s3) ->
  blocks_bytes S' <= blocks_bytes R3 ->
  FSH_Fn_writer.wbudget_kept S S' failed cap cnt
    (WriterApp.w_failed (WriterApp.putN (WriterApp.mkW failed text cap cnt fail []) (WriterSpec.spieces bs)))
    (WriterApp.w_cap (WriterApp.putN (WriterApp.mkW failed text cap cnt fail []) (WriterSpec.spieces bs)))
    (WriterApp.w_cnt (WriterApp.putN (WriterApp.mkW failed text cap cnt fail []) (WriterSpec.spieces bs))).
Proof.
  intros S S1 R1 S2 R2 S3 R3 S' failed text cap cnt fail bs s1 s2 s3 Hpb E1 E2 E3 L1 K1 L2 K2 L3 K3 L4.
  destruct (psm_fields failed text cap cnt fail bs s1 s2 s3 Hpb E1 E2 E3) as (Ef & _ & Ecap & Ecnt & _).
  rewrite Ef, Ecap, Ecnt.
  pose proof (psm_wbudget_kept2 _ _ _ _ _ _ _ _ _ _ _ _ _
    (psm_wbudget_kept2 _ _ _ _ _ _ _ _ _ _ _ _ _ K1 L2 K2) L3 K3) as (A1 & A2 & A3).
  unfold FSH_Fn_writer.wbudget_kept. split; [exact A1|]. split; lia.
Qed.

(* ================= 7, 8: the swap relations (pure cores) ================= *)
Lemma psm_split_uniq : forall (x : Z * Z) l1 l2 C1 C2, ~ In x (C1 ++ C2) ->
  l1 ++ x :: l2 = C1 ++ x :: C2 -> l1 = C1 /\ l2 = C2.
Proof.
  intros x l1. induction l1 as [|a l1 IH]; intros l2 C1 C2 Hn E; destruct C1 as [|c C1]; cbn [app] in *.
  - injection E as E. split; [reflexivity | exact E].
  - injection E as E1 E2. subst c. exfalso. apply Hn. left. reflexivity.
  - injection E as E1 E2. subst a. exfalso. apply Hn. rewrite <- E2. apply in_or_app. right. left. reflexivity.
  - injection E as E1 E2. subst c.
    destruct (IH l2 C1 C2 (fun H => Hn (or_intror H)) E2) as [-> ->]. split; reflexivity.
Qed.

(* a non-empty range sits once in a pairwise-disjoint list *)
Lemma psm_pw_once : forall (h : Z * Z) l1 l2, pairwise zdisjoint (l1 ++ h :: l2) -> 0 < snd h ->
  ~ In h (l1 ++ l2).
Proof.
  intros h l1. induction l1 as [|a l1 IH]; intros l2 HP Hpos Hin; cbn [app pairwise] in HP, Hin.
  - destruct HP as (F & _). rewrite Forall_forall in F. pose proof (F h Hin) as Hd.
    unfold zdisjoint in Hd. lia.
  - destruct HP as (F & HP). destruct Hin as [<- | Hin].
    + rewrite Forall_forall in F.
      assert (Hh : In a (l1 ++ a :: l2)) by (apply in_or_app; right; left; reflexivity).
      pose proof (F a Hh) as Hd. unfold zdisjoint in Hd. lia.
    + exact (IH l2 HP Hpos Hin).
Qed.

(* two calls of bswap compose when, at the MIDDLE list A1, the middle buffer's block occurs once and a call that
   left the cap at 0 put no block there *)
Lemma psm_bswap2 : forall A0 A1 A2 b0 b1 b2 c0 c1 c2,
  List.NoDup A1 -> (c1 = 0 -> ~ In (b1 - HEAD, c1 + HEAD) A1) ->
  FSH_Fn_writer.bswap A0 A1 b0 b1 c0 c1 -> FSH_Fn_writer.bswap A1 A2 b1 b2 c1 c2 ->
  FSH_Fn_writer.bswap A0 A2 b0 b2 c0 c2.
Proof.
  intros A0 A1 A2 b0 b1 b2 c0 c1 c2 HND HZ H1 H2.
  destruct H1 as [(Eb & Ec & EA) | [(Ec0 & C1 & C2 & EA & EC) | (X1 & X2 & C1 & C2 & EX & EA & EC)]].
  - subst b1 c1 A1. exact H2.
  - assert (Hnot : ~ In (b1 - HEAD, c1 + HEAD) (C1 ++ C2)) by (apply NoDup_remove_2; rewrite <- EA; exact HND).
    destruct H2 as [(Eb2 & Ec2 & EA2) | [(Ec1 & D1 & D2 & EA2 & ED) | (Y1 & Y2 & D1 & D2 & EY & EA2 & ED)]].
    + subst b2 c2 A2. right; left. split; [exact Ec0|]. exists C1, C2. split; [exact EA | exact EC].
    + exfalso. apply (HZ Ec1). rewrite EA. apply in_or_app. right. left. reflexivity.
    + rewrite EA in EY. destruct (psm_split_uniq _ Y1 Y2 C1 C2 Hnot (eq_sym EY)) as [-> ->].
      right; left. split; [exact Ec0|]. exists D1, D2. split; [exact EA2|]. rewrite ED. exact EC.
  - assert (Hnot : ~ In (b1 - HEAD, c1 + HEAD) (C1 ++ C2)) by (apply NoDup_remove_2; rewrite <- EA; exact HND).
    destruct H2 as [(Eb2 & Ec2 & EA2) | [(Ec1 & D1 & D2 & EA2 & ED) | (Y1 & Y2 & D1 & D2 & EY & EA2 & ED)]].
    + subst b2 c2 A2. right; right. exists X1, X2, C1, C2. split; [exact EX|]. split; [exact EA | exact EC].
    + exfalso. apply (HZ Ec1). rewrite EA. apply in_or_app. right. left. reflexivity.
    + rewrite EA in EY. destruct (psm_split_uniq _ Y1 Y2 C1 C2 Hnot (eq_sym EY)) as [-> ->].
      right; right. exists X1, X2, D1, D2. split; [exact EX|]. split; [exact EA2|]. rewrite ED. exact EC.
Qed.

(* two calls of uswap compose when, at the MIDDLE list U1, the heads are pairwise disjoint, a call that left the
   cap at 0 put no head there, and a middle cap of 0 means the first call started at 0 (cap monotonicity) *)
Lemma psm_uswap2 : forall U0 U1 U2 b0 b1 b2 c0 c1,
  pairwise zdisjoint U1 -> (c1 = 0 -> ~ In (b1 - HEAD, HEAD) U1) -> (c1 = 0 -> c0 = 0) ->
  FSH_Fn_writer.uswap U0 U1 b0 b1 c0 -> FSH_Fn_writer.uswap U1 U2 b1 b2 c1 ->
  FSH_Fn_writer.uswap U0 U2 b0 b2 c0.
Proof.
  intros U0 U1 U2 b0 b1 b2 c0 c1 HPW HZ Hc H1 H2.
  assert (Hpos : 0 < snd (b1 - HEAD, HEAD)) by (cbn [snd]; unfold HEAD; lia).
  destruct H1 as [(EU & Eb) | [(V1 & V2 & EV & EU1) | (Ec0 & EU1)]].
  - subst U1 b1. destruct H2 as [(EU2 & Eb2) | [(W1 & W2 & EW & EU2) | (Ec1 & EU2)]].
    + left. split; [exact EU2 | exact Eb2].
    + right; left. exists W1, W2. split; [exact EW | exact EU2].
    + right; right. split; [exact (Hc Ec1) | exact EU2].
  - assert (EU1' : U1 = (V1 ++ V2) ++ (b1 - HEAD, HEAD) :: []) by (rewrite EU1, app_assoc; reflexivity).
    assert (Hnot : ~ In (b1 - HEAD, HEAD) ((V1 ++ V2) ++ [])).
    { rewrite EU1' in HPW. exact (psm_pw_once _ _ _ HPW Hpos). }
    destruct H2 as [(EU2 & Eb2) | [(W1 & W2 & EW & EU2) | (Ec1 & EU2)]].
    + subst U2 b2. right; left. exists V1, V2. split; [exact EV | exact EU1].
    + rewrite EU1' in EW. destruct (psm_split_uniq _ W1 W2 (V1 ++ V2) [] Hnot (eq_sym EW)) as [-> ->].
      right; left. exists V1, V2. split; [exact EV|]. rewrite EU2, app_nil_l, app_assoc. reflexivity.
    + exfalso. apply (HZ Ec1). rewrite EU1. apply in_or_app. right. apply in_or_app. right. left. reflexivity.
  - assert (EU1' : U1 = U0 ++ (b1 - HEAD, HEAD) :: []) by exact EU1.
    assert (Hnot : ~ In (b1 - HEAD, HEAD) (U0 ++ [])).
    { rewrite EU1' in HPW. exact (psm_pw_once _ _ _ HPW Hpos). }
    destruct H2 as [(EU2 & Eb2) | [(W1 & W2 & EW & EU2) | (Ec1 & EU2)]].
    + subst U2 b2. right; right. split; [exact Ec0 | exact EU1].
    + rewrite EU1' in EW. destruct (psm_split_uniq _ W1 W2 U0 [] Hnot (eq_sym EW)) as [-> ->].
      right; right. split; [exact Ec0|]. rewrite EU2, app_nil_l. reflexivity.
    + exfalso. apply (HZ Ec1). rewrite EU1. apply in_or_app. right. left. reflexivity.
Qed.

(* ITEM 7: bswap over the walk's three calls, into the spec's one (caps from the model; the premises are per
   MIDDLE list: A1 after put #1, A2 after put #2; psm_bswap_mid gives each from AR at that state) *)
Lemma psm_bswap : forall A0 A1 A2 A3 buf b1 b2 b3 failed text cap cnt fail bs s1 s2 s3,
  plain_bytes bs ->
  s1 = WriterApp.put1 (WriterApp.mkW failed text cap cnt fail []) [34] ->
  s2 = WriterApp.put1 (WriterApp.mkW (WriterApp.w_failed s1) (WriterApp.w_text s1) (WriterApp.w_cap s1)
                         (WriterApp.w_cnt s1) (WriterApp.w_fail s1) []) bs ->
  s3 = WriterApp.put1 (WriterApp.mkW (WriterApp.w_failed s2) (WriterApp.w_text s2) (WriterApp.w_cap s2)
                         (WriterApp.w_cnt s2) (WriterApp.w_fail s2) []) [34] ->
  List.NoDup A1 -> (WriterApp.w_cap s1 = 0 -> ~ In (b1 - HEAD, WriterApp.w_cap s1 + HEAD) A1) ->
  List.NoDup A2 -> (WriterApp.w_cap s2 = 0 -> ~ In (b2 - HEAD, WriterApp.w_cap s2 + HEAD) A2) ->
  FSH_Fn_writer.bswap A0 A1 buf b1 cap (WriterApp.w_cap s1) ->
  FSH_Fn_writer.bswap A1 A2 b1 b2 (WriterApp.w_cap s1) (WriterApp.w_cap s2) ->
  FSH_Fn_writer.bswap A2 A3 b2 b3 (WriterApp.w_cap s2) (WriterApp.w_cap s3) ->
  FSH_Fn_writer.bswap A0 A3 buf b3 cap
    (WriterApp.w_cap (WriterApp.putN (WriterApp.mkW failed text cap cnt fail []) (WriterSpec.spieces bs))).
Proof.
  intros A0 A1 A2 A3 buf b1 b2 b3 failed text cap cnt fail bs s1 s2 s3 Hpb E1 E2 E3 N1 Z1 N2 Z2 H1 H2 H3.
  destruct (psm_fields failed text cap cnt fail bs s1 s2 s3 Hpb E1 E2 E3) as (_ & _ & Ecap & _).
  rewrite Ecap.
  exact (psm_bswap2 A0 A2 A3 buf b2 b3 cap _ _ N2 Z2 (psm_bswap2 A0 A1 A2 buf b1 b2 cap _ _ N1 Z1 H1 H2) H3).
Qed.

(* ITEM 8: uswap over the walk's three calls (premises per MIDDLE list: U1 after put #1, U2 after put #2;
   psm_uswap_mid gives each from ARU at that state). Only the first two calls' models matter (the caps they leave). *)
Lemma psm_uswap : forall U0 U1 U2 U3 buf b1 b2 b3 failed text cap cnt fail bs s1 s2,
  0 <= cap ->
  s1 = WriterApp.put1 (WriterApp.mkW failed text cap cnt fail []) [34] ->
  s2 = WriterApp.put1 (WriterApp.mkW (WriterApp.w_failed s1) (WriterApp.w_text s1) (WriterApp.w_cap s1)
                         (WriterApp.w_cnt s1) (WriterApp.w_fail s1) []) bs ->
  pairwise zdisjoint U1 -> (WriterApp.w_cap s1 = 0 -> ~ In (b1 - HEAD, HEAD) U1) ->
  pairwise zdisjoint U2 -> (WriterApp.w_cap s2 = 0 -> ~ In (b2 - HEAD, HEAD) U2) ->
  FSH_Fn_writer.uswap U0 U1 buf b1 cap -> FSH_Fn_writer.uswap U1 U2 b1 b2 (WriterApp.w_cap s1) ->
  FSH_Fn_writer.uswap U2 U3 b2 b3 (WriterApp.w_cap s2) ->
  FSH_Fn_writer.uswap U0 U3 buf b3 cap.
Proof.
  intros U0 U1 U2 U3 buf b1 b2 b3 failed text cap cnt fail bs s1 s2 Hc E1 E2 P1 Z1 P2 Z2 H1 H2 H3.
  destruct (psm_caps failed text cap cnt fail [34] bs [34] s1 s2 _ Hc E1 E2 eq_refl) as (C1 & C2 & _).
  assert (K1 : WriterApp.w_cap s1 = 0 -> cap = 0) by lia.
  assert (K2 : WriterApp.w_cap s2 = 0 -> cap = 0) by lia.
  exact (psm_uswap2 U0 U2 U3 buf b2 b3 cap _ P2 Z2 K2 (psm_uswap2 U0 U1 U2 buf b1 b2 cap _ P1 Z1 K1 H1 H2) H3).
Qed.

(* ================= 9. the peak clause ================= *)
Lemma psm_max_chain : forall peak p1 p2 p3 a b c,
  a <= b -> b <= c ->
  peak <= p1 <= Z.max peak a -> p1 <= p2 <= Z.max p1 b -> p2 <= p3 <= Z.max p2 c ->
  peak <= p3 <= Z.max peak c.
Proof. intros peak p1 p2 p3 a b c Hab Hbc H1 H2 H3. lia. Qed.

Section psm. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.

(* ---- the premises of psm_bswap2 / psm_uswap2 at ONE middle state, from what the walk holds there ---- *)
Lemma psm_pw_nodup : forall l : list (Z * Z),
  pairwise zdisjoint (map (fun b => (fst b, req_size (snd b))) l) -> (forall x, In x l -> 0 <= snd x) ->
  List.NoDup l.
Proof.
  induction l as [|x l IH]; intros HPW Hpos; [constructor|].
  cbn [map pairwise] in HPW. destruct HPW as (HF & HPW). constructor.
  - intros Hin. rewrite Forall_forall in HF.
    assert (Hm : In (fst x, req_size (snd x)) (map (fun b => (fst b, req_size (snd b))) l))
      by exact (in_map (fun b => (fst b, req_size (snd b))) l x Hin).
    pose proof (HF _ Hm) as Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd.
    pose proof (req_size_pos (snd x) (Hpos x (or_introl eq_refl))) as (Hr & _). lia.
  - apply IH; [exact HPW | intros y Hy; apply Hpos; right; exact Hy].
Qed.

(* the live block list carries no repeat (AR_blocks_law: the blocks are pairwise disjoint and non-empty) *)
Lemma psm_ablocks_nodup : forall ly S W mem md, AR segs B ly S W mem md -> List.NoDup (ablocks B ly S).
Proof.
  intros ly S W mem md HAR.
  destruct (ablocks B ly S) as [|[p n] l] eqn:E; [constructor|].
  assert (Hin : In (p, n) (ablocks B ly S)) by (rewrite E; left; reflexivity).
  destruct (al_blocks segs B (AR_laws_ok segs B) ly S W mem md p n HAR Hin) as (_ & _ & _ & _ & _ & HPW & _).
  rewrite E in HPW. apply psm_pw_nodup; [exact HPW|].
  intros [q k] Hq. rewrite <- E in Hq.
  destruct (al_blocks segs B (AR_laws_ok segs B) ly S W mem md q k HAR Hq) as (_ & _ & _ & _ & _ & _ & Hk).
  cbn [snd]. lia.
Qed.

(* bswap's premises at a middle state (ly, S) with buffer b and cap c, from AR there and put's wout_ok
   (cap = 0 -> buf = 0) *)
Lemma psm_bswap_mid : forall ly S W mem md b c,
  AR segs B ly S W mem md -> (c = 0 -> b = 0) ->
  List.NoDup (ablocks B ly S) /\ (c = 0 -> ~ In (b - HEAD, c + HEAD) (ablocks B ly S)).
Proof.
  intros ly S W mem md b c HAR Hb. split; [exact (psm_ablocks_nodup ly S W mem md HAR)|].
  intros Hc Hin. rewrite (Hb Hc) in Hin.
  destruct (al_blocks segs B (AR_laws_ok segs B) ly S W mem md _ _ HAR Hin) as (_ & H4 & _).
  unfold HEAD in H4. lia.
Qed.

(* uswap's premises at a middle state (ly, S, U), from ARU there (upoison_ok: every head lies in a live block,
   which starts at 4096 or above, and the heads are pairwise disjoint) and put's wout_ok *)
Lemma psm_uswap_mid : forall ly S U W mem md b c,
  ARU segs B ly S U W mem md -> (c = 0 -> b = 0) ->
  pairwise zdisjoint U /\ (c = 0 -> ~ In (b - HEAD, HEAD) U).
Proof.
  intros ly S U W mem md b c (HAR & (HF & HPW) & _) Hb. split; [exact HPW|].
  intros Hc Hin. rewrite (Hb Hc) in Hin. rewrite Forall_forall in HF.
  destruct (HF _ Hin) as (_ & _ & _ & p & n & Hpn & Hp & _).
  destruct (al_blocks segs B (AR_laws_ok segs B) ly S W (unpoison U mem) md p n HAR Hpn) as (_ & H4 & _).
  cbn [fst] in Hp. unfold HEAD in Hp. lia.
Qed.

(* the two-call compositions with the middle state's own facts (one application per middle state: after put #2
   with the state after put #1, after put #3 with the state after put #2) *)
Lemma psm_bswap2_ar : forall ly1 S1 W1 m1 md1 A0 A2 b0 b1 b2 c0 c1 c2,
  AR segs B ly1 S1 W1 m1 md1 -> (c1 = 0 -> b1 = 0) ->
  FSH_Fn_writer.bswap A0 (ablocks B ly1 S1) b0 b1 c0 c1 -> FSH_Fn_writer.bswap (ablocks B ly1 S1) A2 b1 b2 c1 c2 ->
  FSH_Fn_writer.bswap A0 A2 b0 b2 c0 c2.
Proof.
  intros ly1 S1 W1 m1 md1 A0 A2 b0 b1 b2 c0 c1 c2 HAR Hb H1 H2.
  destruct (psm_bswap_mid ly1 S1 W1 m1 md1 b1 c1 HAR Hb) as (N & Z0).
  exact (psm_bswap2 A0 _ A2 b0 b1 b2 c0 c1 c2 N Z0 H1 H2).
Qed.

Lemma psm_uswap2_ar : forall ly1 S1 U1 W1 m1 md1 U0 U2 b0 b1 b2 c0 c1,
  ARU segs B ly1 S1 U1 W1 m1 md1 -> (c1 = 0 -> b1 = 0) -> (c1 = 0 -> c0 = 0) ->
  FSH_Fn_writer.uswap U0 U1 b0 b1 c0 -> FSH_Fn_writer.uswap U1 U2 b1 b2 c1 ->
  FSH_Fn_writer.uswap U0 U2 b0 b2 c0.
Proof.
  intros ly1 S1 U1 W1 m1 md1 U0 U2 b0 b1 b2 c0 c1 HARU Hb Hc H1 H2.
  destruct (psm_uswap_mid ly1 S1 U1 W1 m1 md1 b1 c1 HARU Hb) as (P & Z0).
  exact (psm_uswap2 U0 U1 U2 b0 b1 b2 c0 c1 P Z0 Hc H1 H2).
Qed.

(* ITEM 9: the three calls' peak clauses (each in put's post form, at the live count the previous call returned:
   L2 after put #1, L3 after put #2) and the last call's fs_glob give the spec's clause *)
Lemma psm_peak : forall (W : world segs) mem failed text cap cnt fail bs s1 s2 s3 live L2 L3 peak p1 p2 p3,
  plain_bytes bs -> 0 <= cap ->
  s1 = WriterApp.put1 (WriterApp.mkW failed text cap cnt fail []) [34] ->
  s2 = WriterApp.put1 (WriterApp.mkW (WriterApp.w_failed s1) (WriterApp.w_text s1) (WriterApp.w_cap s1)
                         (WriterApp.w_cnt s1) (WriterApp.w_fail s1) []) bs ->
  s3 = WriterApp.put1 (WriterApp.mkW (WriterApp.w_failed s2) (WriterApp.w_text s2) (WriterApp.w_cap s2)
                         (WriterApp.w_cnt s2) (WriterApp.w_fail s2) []) [34] ->
  L2 = live + WriterApp.w_cap s1 - cap -> L3 = L2 + WriterApp.w_cap s2 - WriterApp.w_cap s1 ->
  peak <= p1 <= Z.max peak (live - cap + WriterApp.w_cap s1) ->
  p1 <= p2 <= Z.max p1 (L2 - WriterApp.w_cap s1 + WriterApp.w_cap s2) ->
  p2 <= p3 <= Z.max p2 (L3 - WriterApp.w_cap s2 + WriterApp.w_cap s3) ->
  fs_glob segs W mem (L3 + WriterApp.w_cap s3 - WriterApp.w_cap s2) p3 (WriterApp.w_cnt s3) (WriterApp.w_fail s3) ->
  exists peak', peak <= peak' <= Z.max peak (live - cap +
      WriterApp.w_cap (WriterApp.putN (WriterApp.mkW failed text cap cnt fail []) (WriterSpec.spieces bs))) /\
    fs_glob segs W mem
      (live + WriterApp.w_cap (WriterApp.putN (WriterApp.mkW failed text cap cnt fail []) (WriterSpec.spieces bs))
         - cap) peak'
      (WriterApp.w_cnt (WriterApp.putN (WriterApp.mkW failed text cap cnt fail []) (WriterSpec.spieces bs)))
      (WriterApp.w_fail (WriterApp.putN (WriterApp.mkW failed text cap cnt fail []) (WriterSpec.spieces bs))).
Proof.
  intros W mem failed text cap cnt fail bs s1 s2 s3 live L2 L3 peak p1 p2 p3 Hpb Hc E1 E2 E3 EL2 EL3 P1 P2 P3 HG.
  destruct (psm_fields failed text cap cnt fail bs s1 s2 s3 Hpb E1 E2 E3) as (_ & _ & Ecap & Ecnt & Efail & _).
  rewrite Ecap, Ecnt, Efail.
  destruct (psm_caps failed text cap cnt fail [34] bs [34] s1 s2 s3 Hc E1 E2 E3) as (C1 & C2 & C3).
  exists p3. split.
  - assert (B2 : L2 - WriterApp.w_cap s1 + WriterApp.w_cap s2 = live - cap + WriterApp.w_cap s2) by lia.
    assert (B3 : L3 - WriterApp.w_cap s2 + WriterApp.w_cap s3 = live - cap + WriterApp.w_cap s3) by lia.
    rewrite B2 in P2. rewrite B3 in P3.
    exact (psm_max_chain peak p1 p2 p3 (live - cap + WriterApp.w_cap s1) (live - cap + WriterApp.w_cap s2)
      (live - cap + WriterApp.w_cap s3) ltac:(lia) ltac:(lia) P1 P2 P3).
  - assert (BL : L3 + WriterApp.w_cap s3 - WriterApp.w_cap s2 = live + WriterApp.w_cap s3 - cap) by lia.
    rewrite BL in HG. exact HG.
Qed.

End psm.
