(* omx-clap-core/fuzz_preset (one file for both images: the texts lib/A/PRH_Fn*.v are shared): THE PER-TEXT ARITHMETIC
   of row ENTRY-SUMS (a Theorem Labs lane; statement owner another Theorem Labs lane). Nothing here is a function's proof (rule 24); kind: model
   bound lemma.

   WHAT IT SAYS. The texts (d6318e886fd9) take `blocks_bytes S + LIVE_<fn> args <= LIVE_MAX` at their entry. For each
   text whose LIVE_<fn> is bounded, the lemma below states `0 <= LIVE_<fn> args <= ENTRY_ROOM` AT THE ARGUMENT
   EXPRESSION ITS CONSUMER PASSES (file:line at d6318e886fd9 in each comment), from the text's own premises or the
   consumer's facts (|x| <= MAXB, ck_read x = Some t). With lib/Spec/PresetLiveBytes.v
     entry_sum_ok    (Wf_cf, iface_room_pos at i, an event at i, 0 <= n <= ENTRY_ROOM)
     entry_sum_pos   (Wf_cf, iface_room_pos at i,                 0 <= n <= ENTRY_ROOM)
   the consumer's premise closes by `apply`: ENTRY_ROOM = LIVE_MAX - LIVE_PEAK_PRESET (the peak of
   blocks_bytes_bound_preset_peak), so blocks_bytes S <= LIVE_PEAK_PRESET at the position gives the sum.
   The tx texts' RELATIVE premise `blocks_bytes S - cap0 + LIVE_tx <= LIVE_MAX` is closed whole (tx_entry_sum): those
   texts carry iface_room_pos at entry and cap0 >= 0 (prhtx_rec).
   The texts whose request is bounded only through cf_malloc_max (the allocator wrappers, parse_string, grow, pj_set,
   pj_string) are stated at the unit's instance CfParams_preset. The rest (Section G) are generic in CfParams under
   the hypothesis cf_head = PresetReqAt.HEAD. Of the texts only tpj_set_specX states that as an entry premise
   (PRH_FnPj.v:1003 at d6318e886fd9); the check texts do not take it. The consumers use the Section G lemmas at
   CfParams_preset, where preset_head discharges the hypothesis.

   NOT HERE, AND WHY (the row's recorded gaps, the internal file entry-sums-table.md last section): check_round_trip (its LIVE sum,
   9.0e9 at MAXB, exceeds ENTRY_ROOM; it closes through the walk's cut budget from the harness entry: entry_sum_closed
   and lib/A/PresetEntryLib.v); the writer callees put / indent / put_string / write_value (w_cap st unbounded) and
   LIVE_rd (a Theorem Labs lane restates both in per-event form).

   PROVED HERE OR CITED: PjGrammar.G10 / G7_4 (a reading's peak and calls), PjRoundTrip.G9_trace (every read-back of
   wdoc t p has the trace of reading wdoc t false), PresetLiveBytes.Lf_read / Lt_read / copy_len_false / dbl_le /
   dbl_ge, PresetReqAtNoMiss.wf_copy. hpeakR_prefix is a Theorem Labs lane's PjLiveBound.hpeak_prefix (d6318e886fd9
   lib/Spec/PjLiveBound.v:118) over the hpeakR. *)
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG01 YGcfNames YG01cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require
  PresetReqAt PresetReqAtNoMiss PresetRun PresetRoomPos PresetLiveBytes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require WriterSpec WriterValue ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfParamsPreset PRH_Reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_FnReader PRH_FnPj PRH_FnWriter PRH_FnTx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_FnCheck.
Import ListNotations.
Local Open Scope Z_scope.

(* the two rooms and the input bound as numbers, inside proofs only *)
Local Ltac rooms :=
  try unfold PresetLiveBytes.ENTRY_ROOM in *; try unfold PresetLiveBytes.CLOSED_ROOM in *;
  try unfold PresetLiveBytes.LIVE_PEAK_PRESET in *; try unfold PresetLiveBytes.DRV_BYTES in *;
  try unfold PresetReqAt.MAXB in *; try unfold PresetReqAt.HEAD in *;
  let LM := fresh "LM" in
  assert (LM : LIVE_MAX = 17179869184) by reflexivity; try rewrite LM in *.

(* ================================================================ a reading's live room *)

(* the live room of one granted reading of a text of m bytes: the LIVE_pj_parse (PRH_FnPj.v:239-240 at
   d6318e886fd9) with PjGrammar.G10's peak bound 224 m + 16384 and G7_4's call bound 2 m + 2 *)
Definition LIVE_RD_BOUND (m : Z) : Z := 2 * (224 * m + 16384) + PresetReqAt.HEAD * (2 * m + 3).

Lemma hpeakR_nn : forall tr, 0 <= PRH_Reader.hpeakR tr.
Proof. intros [|e r]; cbn [PRH_Reader.hpeakR]; lia. Qed.

(* the most a trace holds at once is what one of its prefixes holds *)
Lemma hpeakR_prefix : forall tr, exists p rest, tr = p ++ rest /\ PRH_Reader.hpeakR tr = PjGrammar.held p.
Proof.
  induction tr as [|e r IH].
  - exists [], []. split; reflexivity.
  - destruct IH as (p & rest & E & H). cbn [PRH_Reader.hpeakR]. rewrite H.
    destruct (Z.max_spec 0 (PjGrammar.held_ev e + PjGrammar.held p)) as [[_ M]|[_ M]]; rewrite M.
    + exists (e :: p), rest. rewrite E. split; reflexivity.
    + exists [], (e :: r). split; reflexivity.
Qed.

(* every read-back of the writer's text of a well-formed tree has the trace of reading its compact text *)
Lemma ptrace_wdoc : forall t p, PjRoundTrip.pj_wf ReaderRes.jr_strtod t ->
  PRH_FnPj.prhPj_ptrace (WriterValue.wdoc t p) = PRH_FnPj.prhPj_ptrace (WriterValue.wdoc t false).
Proof.
  intros t p Hw. unfold PRH_FnPj.prhPj_ptrace.
  change PRH_Reader.prh_jr_strtod with ReaderRes.jr_strtod.
  rewrite (PjRoundTrip.G9_trace ReaderRes.jr_strtod t Hw p), (PjRoundTrip.G9_trace ReaderRes.jr_strtod t Hw false).
  reflexivity.
Qed.

Section G.
Context {cp : CfParams}.
(* THE HEAD IS THE MODEL'S: tpj_set_specX's entry premise (PRH_FnPj.v:1003 at d6318e886fd9; no other text takes it
   at entry); preset_head below discharges it at CfParams_preset *)
Hypothesis HHD : cf_head = PresetReqAt.HEAD.

Lemma live_pj_parse_lin : forall tl, 0 <= PRH_FnPj.LIVE_pj_parse tl <= LIVE_RD_BOUND (Z.of_nat (length tl)).
Proof.
  intros tl. unfold PRH_FnPj.LIVE_pj_parse, PRH_FnPj.prhPj_ptrace.
  destruct (hpeakR_prefix (snd (PjGrammar.jr_run PRH_Reader.prh_jr_strtod tl []))) as (p & rest & E & H).
  pose proof (PjGrammar.G10 PRH_Reader.prh_jr_strtod tl [] p rest E) as G.
  pose proof (PjGrammar.G7_4 PRH_Reader.prh_jr_strtod tl []) as C.
  pose proof (hpeakR_nn (snd (PjGrammar.jr_run PRH_Reader.prh_jr_strtod tl []))) as N.
  rewrite HHD. unfold LIVE_RD_BOUND, PresetReqAt.HEAD. lia.
Qed.

Lemma live_pj_parse_wdoc_eq : forall t p, PjRoundTrip.pj_wf ReaderRes.jr_strtod t ->
  PRH_FnPj.LIVE_pj_parse (WriterValue.wdoc t p) = PRH_FnPj.LIVE_pj_parse (WriterValue.wdoc t false).
Proof. intros t p Hw. unfold PRH_FnPj.LIVE_pj_parse. rewrite (ptrace_wdoc t p Hw). reflexivity. Qed.

(* the read-back of wdoc t p for the tree t read from x: the compact text is at most 3 |x| (Lf_read) *)
Lemma live_pj_parse_wdoc : forall x t p, PRH_FnCheck.ck_read x = Some t ->
  0 <= PRH_FnPj.LIVE_pj_parse (WriterValue.wdoc t p) <= LIVE_RD_BOUND (3 * Z.of_nat (length x)).
Proof.
  intros x t p Hr. unfold PRH_FnCheck.ck_read in Hr.
  rewrite (live_pj_parse_wdoc_eq t p (PjRoundTrip.wf_read ReaderRes.jr_strtod x t Hr)).
  pose proof (live_pj_parse_lin (WriterValue.wdoc t false)) as B.
  pose proof (PresetLiveBytes.Lf_read ReaderRes.jr_strtod x t Hr) as L. unfold PresetLiveBytes.Lf in L.
  unfold LIVE_RD_BOUND, PresetReqAt.HEAD in *. lia.
Qed.

(* pj_write's room: twice its last buffer and head; its last buffer is newcap 0 (len + 1) <= WCAP (dbl_le) *)
Lemma live_pj_write_wcap : forall t p,
  0 <= PRH_FnWriter.LIVE_pj_write t p <= 2 * (PresetLiveBytes.WCAP t p + PresetReqAt.HEAD).
Proof.
  intros t p. unfold PRH_FnWriter.LIVE_pj_write, WriterSpec.newcap. rewrite HHD. cbn [Z.eqb].
  pose proof (PresetLiveBytes.dbl_le 64%nat 4096 (Z.of_nat (length (WriterValue.wdoc t p)) + 1)) as L.
  pose proof (PresetLiveBytes.dbl_ge 64%nat 4096 (Z.of_nat (length (WriterValue.wdoc t p)) + 1) ltac:(lia)) as G.
  unfold PresetLiveBytes.WCAP, PresetReqAt.HEAD. lia.
Qed.

(* ---------------------------------------------------------------- the sites, generic in CfParams *)

(* check_no_overread: PRH_FnCheck.v:768 `blocks_bytes S + LIVE_check_no_overread x <= LIVE_MAX` (def :506), its
   exact form Ent102CutsA.v:157 / Ent102GrantA.v:303, and the walk's argument (e_x E) (ecov_cno, Ent102CutsA.v:615;
   Ent102L1A.v:449-450). The text has size <= 3 * 2 ^ 20 (:753), which is |x| <= MAXB. *)
Lemma live_cno_fits : forall x, Z.of_nat (length x) <= PresetReqAt.MAXB ->
  0 <= PRH_FnCheck.LIVE_check_no_overread x <= PresetLiveBytes.ENTRY_ROOM.
Proof.
  intros x HX. pose proof (live_pj_parse_lin x) as B.
  unfold PRH_FnCheck.LIVE_check_no_overread, LIVE_RD_BOUND in *. rooms. lia.
Qed.

(* parse_noting: PRH_FnCheck.v:636 `blocks_bytes S + PRH_FnPj.LIVE_pj_parse tb <= LIVE_MAX`, its exact form
   Ent102CutsA.v:205 / Ent102GrantA.v:195, the walk's argument (e_x E) (Ent102L2A.v:618, ecov_pno Ent102CutsA.v:617);
   pj_parse: PRH_FnPj.v:630 `blocks_bytes S + LIVE_pj_parse tl <= LIVE_MAX` at tl = x (PRH_FnCheck.v:506, :512) *)
Lemma live_pj_parse_fits : forall tl, Z.of_nat (length tl) <= PresetReqAt.MAXB ->
  0 <= PRH_FnPj.LIVE_pj_parse tl <= PresetLiveBytes.ENTRY_ROOM.
Proof. intros tl HX. pose proof (live_pj_parse_lin tl) as B. unfold LIVE_RD_BOUND in B. rooms. lia. Qed.

(* pj_parse at round_trip_text's read-back: serves pj_parse's own premise PRH_FnPj.v:630 `blocks_bytes S +
   LIVE_pj_parse tl <= LIVE_MAX` at tl := WriterValue.wdoc t p (the call round_trip_text makes). The same term is a
   summand of the DEFINITION LIVE_round_trip_text (PRH_FnCheck.v:516-517), whose premise :1199 live_rtt_fits serves *)
Lemma live_pj_parse_wdoc_fits : forall x t p, Z.of_nat (length x) <= PresetReqAt.MAXB ->
  PRH_FnCheck.ck_read x = Some t ->
  0 <= PRH_FnPj.LIVE_pj_parse (WriterValue.wdoc t p) <= PresetLiveBytes.ENTRY_ROOM.
Proof. intros x t p HX Hr. pose proof (live_pj_parse_wdoc x t p Hr) as B. unfold LIVE_RD_BOUND in B. rooms. lia. Qed.

(* pj_parse at the rewrite's read-back: serves pj_parse's own premise PRH_FnPj.v:630 at
   tl := WriterValue.wdoc (ck_crt_tree t) true (the call check_round_trip's rewrite makes). The same term is a summand
   of the DEFINITION LIVE_check_round_trip (PRH_FnCheck.v:523-527). The copy's compact text is at most 36 bytes
   longer (copy_len_false) *)
Lemma live_pj_parse_crt_fits : forall x t, Z.of_nat (length x) <= PresetReqAt.MAXB ->
  PRH_FnCheck.ck_read x = Some t ->
  0 <= PRH_FnPj.LIVE_pj_parse (WriterValue.wdoc (PRH_FnCheck.ck_crt_tree t) true) <= PresetLiveBytes.ENTRY_ROOM.
Proof.
  intros x t HX Hr. pose proof Hr as Hr'. unfold PRH_FnCheck.ck_read in Hr'.
  pose proof (PresetLiveBytes.Lf_read ReaderRes.jr_strtod x t Hr') as Lf0. unfold PresetLiveBytes.Lf in Lf0.
  assert (B : forall u, PjRoundTrip.pj_wf ReaderRes.jr_strtod u ->
    0 <= PRH_FnPj.LIVE_pj_parse (WriterValue.wdoc u true) <=
      LIVE_RD_BOUND (Z.of_nat (length (WriterValue.wdoc u false)))).
  { intros u Hu. rewrite (live_pj_parse_wdoc_eq u true Hu). apply live_pj_parse_lin. }
  pose proof (PjRoundTrip.wf_read ReaderRes.jr_strtod x t Hr') as Hw.
  destruct t as [| | | txt bits | s | items | ms]; cbn [PRH_FnCheck.ck_crt_tree];
    try (pose proof (B _ Hw) as Bt; unfold LIVE_RD_BOUND in Bt; rooms; lia).
  change (PjTree.JObj (PjTree.pj_set_model ms PRH_FnCheck.ck_MOD_AT (PjTree.JStr PRH_FnCheck.ck_STAMP)))
    with (PresetReqAt.copy_set ms).
  pose proof (B _ (PresetReqAtNoMiss.wf_copy ReaderRes.jr_strtod ms Hw)) as Bc.
  pose proof (PresetLiveBytes.copy_len_false ms) as CL.
  unfold LIVE_RD_BOUND in Bc. rooms. lia.
Qed.

(* check_as_written: PRH_FnCheck.v:855 `blocks_bytes S + LIVE_check_as_written size <= LIVE_MAX` (def :509),
   size = Z.of_nat (length x) <= 3 * 2 ^ 20 (:846); Ent102GrantA.v:262; the walk's argument (e_n E) (ecov_caw,
   Ent102CutsA.v:623, with e_n E <= EC_NMAX) *)
Lemma live_caw_fits : forall size, 0 <= size <= PresetReqAt.MAXB ->
  0 <= PRH_FnCheck.LIVE_check_as_written size <= PresetLiveBytes.ENTRY_ROOM.
Proof. intros size HX. unfold PRH_FnCheck.LIVE_check_as_written. rooms. lia. Qed.

(* check_reject_clean_starved on the accepted tree: PRH_FnCheck.v:1110
   `blocks_bytes S + LIVE_check_reject_clean_starved tb t <= LIVE_MAX` (def :511-512) at tb = the input, t = its tree
   (Ent102L5cA.v:375-376 `(e_x E) .. t`; ecov_crs1 Ent102CutsA.v:629) *)
Lemma live_crcs_fits : forall x t, Z.of_nat (length x) <= PresetReqAt.MAXB -> PRH_FnCheck.ck_read x = Some t ->
  0 <= PRH_FnCheck.LIVE_check_reject_clean_starved x t <= PresetLiveBytes.ENTRY_ROOM.
Proof.
  intros x t HX Hr. pose proof Hr as Hr'. unfold PRH_FnCheck.ck_read in Hr'.
  pose proof (live_pj_parse_lin x) as P.
  pose proof (live_pj_write_wcap t true) as W1. pose proof (live_pj_write_wcap t false) as W0.
  pose proof (PresetLiveBytes.Lf_read ReaderRes.jr_strtod x t Hr') as Lf0.
  pose proof (PresetLiveBytes.Lt_read ReaderRes.jr_strtod x t Hr') as Lt0.
  unfold PRH_FnCheck.LIVE_check_reject_clean_starved, LIVE_RD_BOUND, PresetLiveBytes.WCAP, PresetLiveBytes.Lf in *.
  rooms. lia.
Qed.

(* the same text on the refused arm, at the tree it fixes there: Ent102L4A.v:669-670 `(e_x E) .. PjTree.JNull`
   (ecov_crs0 Ent102CutsA.v:625) *)
Lemma live_crcs_null_fits : forall x, Z.of_nat (length x) <= PresetReqAt.MAXB ->
  0 <= PRH_FnCheck.LIVE_check_reject_clean_starved x PjTree.JNull <= PresetLiveBytes.ENTRY_ROOM.
Proof.
  intros x HX. pose proof (live_pj_parse_lin x) as P.
  pose proof (live_pj_write_wcap PjTree.JNull true) as W1. pose proof (live_pj_write_wcap PjTree.JNull false) as W0.
  assert (N : forall p, (length (WriterValue.wdoc PjTree.JNull p) <= 5)%nat) by (intros []; vm_compute; lia).
  pose proof (N true) as N1. pose proof (N false) as N0.
  unfold PRH_FnCheck.LIVE_check_reject_clean_starved, LIVE_RD_BOUND, PresetLiveBytes.WCAP in *. rooms. lia.
Qed.

(* round_trip_text: PRH_FnCheck.v:1199 `blocks_bytes S + LIVE_round_trip_text t p <= LIVE_MAX` (def :516-517), with
   its caller's facts (check_round_trip, :1313: ck_read x = Some t, |x| <= 3 * 2 ^ 20); arguments t false / t true
   (:524) *)
Lemma live_rtt_fits : forall x t p, Z.of_nat (length x) <= PresetReqAt.MAXB -> PRH_FnCheck.ck_read x = Some t ->
  0 <= PRH_FnCheck.LIVE_round_trip_text t p <= PresetLiveBytes.ENTRY_ROOM.
Proof.
  intros x t p HX Hr. pose proof Hr as Hr'. unfold PRH_FnCheck.ck_read in Hr'.
  pose proof (live_pj_parse_wdoc x t p Hr) as P. pose proof (live_pj_write_wcap t p) as W.
  pose proof (PresetLiveBytes.Lf_read ReaderRes.jr_strtod x t Hr') as Lf0.
  pose proof (PresetLiveBytes.Lt_read ReaderRes.jr_strtod x t Hr') as Lt0.
  assert (TX : PRH_FnTx.LIVE_tx = 1073741824) by reflexivity.
  unfold PRH_FnCheck.LIVE_round_trip_text. rewrite TX.
  unfold LIVE_RD_BOUND, PresetLiveBytes.WCAP, PresetLiveBytes.Lf in *. destruct p; rooms; lia.
Qed.

(* pj_write: PRH_FnWriter.v:795 `blocks_bytes S + LIVE_pj_write t (negb (pretty =? 0)) <= LIVE_MAX` (def :258-259),
   from the text's own :793 `Z.of_nat (length (WriterValue.wdoc t (negb (pretty =? 0)))) + 1 <= prhWriter_WMAX` *)
Lemma live_pj_write_fits : forall (t : PjTree.jv) (pretty : Z),
  Z.of_nat (length (WriterValue.wdoc t (negb (pretty =? 0)))) + 1 <= PRH_FnWriter.prhWriter_WMAX ->
  0 <= PRH_FnWriter.LIVE_pj_write t (negb (pretty =? 0)) <= PresetLiveBytes.ENTRY_ROOM.
Proof.
  intros t pretty H. pose proof (live_pj_write_wcap t (negb (pretty =? 0))) as B.
  assert (WM : PRH_FnWriter.prhWriter_WMAX = 268435456) by reflexivity. rewrite WM in H.
  unfold PresetLiveBytes.WCAP in B. rooms. lia.
Qed.

End G.

(* padded: PRH_FnCheck.v:966 `blocks_bytes S + (size + 16) <= LIVE_MAX`, size = Z.of_nat (length x) <= 3 * 2 ^ 20
   (:964); the sum `size + 16` is the text's own *)
Lemma padded_room_fits : forall size, 0 <= size <= PresetReqAt.MAXB ->
  0 <= size + 16 <= PresetLiveBytes.ENTRY_ROOM.
Proof. intros size HX. rooms. lia. Qed.

(* ---------------------------------------------------------------- the tx texts *)

Lemma live_tx_fits : 0 <= PRH_FnTx.LIVE_tx <= PresetLiveBytes.ENTRY_ROOM.
Proof. assert (TX : PRH_FnTx.LIVE_tx = 1073741824) by reflexivity. rewrite TX. rooms. lia. Qed.

(* tx_put / tx_string / tx_line / tx_value: PRH_FnTx.v:352 / :403 / :456 / :522
   `blocks_bytes S - cap0 + LIVE_tx <= LIVE_MAX` (LIVE_tx :154), WHOLE: each text has iface_room_pos at entry
   (:331 / :388 / :442 / :502) and cap0 >= 0 (prhtx_rec :181); no event is needed (entry_sum_pos) *)
Theorem tx_entry_sum :
  forall U (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat))
         (i : nat) (H0 : list Z) (hist : list YG00.chunk) (S : astate) (cap0 : Z),
  @Wf_cf CfParamsPreset.CfParams_preset U S ->
  PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
  0 <= cap0 ->
  blocks_bytes S - cap0 + PRH_FnTx.LIVE_tx <= LIVE_MAX.
Proof.
  intros U sm x os i H0 hist S cap0 HW HP Hc.
  pose proof (PresetLiveBytes.entry_sum_pos U sm x os i H0 hist S PRH_FnTx.LIVE_tx HW HP live_tx_fits). lia.
Qed.

(* ================================================================ the sites bounded through cf_malloc_max *)

Section P.
#[local] Abbreviation CP := CfParamsPreset.CfParams_preset.

Lemma preset_head : @cf_head CP = PresetReqAt.HEAD.
Proof. reflexivity. Qed.

(* `preset` fixes cf_head = 16 and cf_malloc_max = 402653184 by reflexivity: true for int102's lib/A/CfParamsPreset.v
   blob b60d0f63c926 (:94, cf_malloc_max = 2 ^ 28 + 2 ^ 27). If that value changes, rebuild the six proofs that use it:
   alloc_req_fits, strdup_req_fits, live_parse_string_fits, live_grow_fits, live_pj_set_fits, live_pj_string_fits. *)
Local Ltac preset := let HD := fresh "HD" in let CM := fresh "CM" in
  assert (HD : @cf_head CP = 16) by reflexivity; assert (CM : @cf_malloc_max CP = 402653184) by reflexivity;
  rewrite ?HD, ?CM in *.

(* fuzz_malloc / fuzz_realloc: PRH_FnAlloc.v:276 / :394 `blocks_bytes S + (n + cf_head) <= LIVE_MAX`, from the
   texts' own :274 / :391 `0 <= n -> n + cf_head < cf_malloc_max` *)
Lemma alloc_req_fits : forall n, 0 <= n -> n + @cf_head CP < @cf_malloc_max CP ->
  0 <= n + @cf_head CP <= PresetLiveBytes.ENTRY_ROOM.
Proof. intros n Hn H. preset. rooms. lia. Qed.

(* fuzz_strdup: PRH_FnAlloc.v:491 `blocks_bytes S + (Z.of_nat (length cs) + 1 + cf_head) <= LIVE_MAX`, from :489 *)
Lemma strdup_req_fits : forall cs : list Z, Z.of_nat (length cs) + 1 + @cf_head CP < @cf_malloc_max CP ->
  0 <= Z.of_nat (length cs) + 1 + @cf_head CP <= PresetLiveBytes.ENTRY_ROOM.
Proof. intros cs H. preset. rooms. lia. Qed.

(* parse_string: PRH_FnReader.v:549 `LIVE_parse_string Q < cf_malloc_max /\ blocks_bytes S + LIVE_parse_string Q <=
   LIVE_MAX` (def :356): the second conjunct from the first *)
Lemma live_parse_string_fits : forall Q : nat, @PRH_FnReader.LIVE_parse_string CP Q < @cf_malloc_max CP ->
  0 <= @PRH_FnReader.LIVE_parse_string CP Q <= PresetLiveBytes.ENTRY_ROOM.
Proof. intros Q H. unfold PRH_FnReader.LIVE_parse_string in *. preset. rooms. lia. Qed.

(* grow: PRH_FnReader.v:818 `n = cap -> 56 * cap2R cap + cf_head < cf_malloc_max /\ blocks_bytes S + LIVE_grow ty cap
   <= LIVE_MAX` (def :658): the second conjunct from the first; 0 <= cap from pj_hdrR (:806, PRH_Reader.rd_u64) *)
Lemma live_grow_fits : forall ty cap, 0 <= cap -> 56 * PRH_Reader.cap2R cap + @cf_head CP < @cf_malloc_max CP ->
  0 <= @PRH_FnReader.LIVE_grow CP ty cap <= PresetLiveBytes.ENTRY_ROOM.
Proof.
  intros ty cap Hc H. unfold PRH_FnReader.LIVE_grow, PRH_Reader.cap2R in *. preset. rooms.
  destruct (cap =? 0); destruct (ty =? 6); cbn [Z.eqb] in *; lia.
Qed.

(* pj_set: PRH_FnPj.v:976 `blocks_bytes S + LIVE_pj_set n cap (Z.of_nat (length kname)) <= LIVE_MAX` (def :264-265),
   from the text's own :973 and :975; 0 <= cap from pj_hdrR (:961) *)
Lemma live_pj_set_fits : forall n cap (kname : list Z), 0 <= cap ->
  Z.of_nat (length kname) + 1 + @cf_head CP < @cf_malloc_max CP ->
  (n = cap -> 56 * PRH_Reader.cap2R cap + @cf_head CP < @cf_malloc_max CP) ->
  0 <= @PRH_FnPj.LIVE_pj_set CP n cap (Z.of_nat (length kname)) <= PresetLiveBytes.ENTRY_ROOM.
Proof.
  intros n cap kname Hc Hk Hg. unfold PRH_FnPj.LIVE_pj_set, PRH_FnReader.LIVE_grow.
  destruct (Z.eqb_spec n cap) as [E|E].
  - specialize (Hg E). unfold PRH_Reader.cap2R in *. preset. rooms.
    destruct (cap =? 0); cbn [Z.eqb Pos.eqb] in *; lia.
  - cbn [Z.eqb] in *. preset. rooms. lia.
Qed.

(* pj_string: PRH_FnPj.v:1237 `blocks_bytes S + LIVE_pj_string (Z.of_nat (length cs)) <= LIVE_MAX` (def :268), from
   the text's own :1235 *)
Lemma live_pj_string_fits : forall cs : list Z, Z.of_nat (length cs) + 1 + @cf_head CP < @cf_malloc_max CP ->
  0 <= @PRH_FnPj.LIVE_pj_string CP (Z.of_nat (length cs)) <= PresetLiveBytes.ENTRY_ROOM.
Proof. intros cs H. unfold PRH_FnPj.LIVE_pj_string. preset. rooms. lia. Qed.

End P.

Print Assumptions hpeakR_nn.
Print Assumptions hpeakR_prefix.
Print Assumptions ptrace_wdoc.
Print Assumptions live_pj_parse_wdoc_eq.
Print Assumptions live_pj_parse_wdoc.
Locate live_pj_parse_lin.
Print Assumptions live_pj_parse_lin.
Locate live_pj_write_wcap.
Print Assumptions live_pj_write_wcap.
Locate live_cno_fits.
Print Assumptions live_cno_fits.
Locate live_pj_parse_fits.
Print Assumptions live_pj_parse_fits.
Locate live_pj_parse_wdoc_fits.
Print Assumptions live_pj_parse_wdoc_fits.
Locate live_pj_parse_crt_fits.
Print Assumptions live_pj_parse_crt_fits.
Locate live_caw_fits.
Print Assumptions live_caw_fits.
Locate live_crcs_fits.
Print Assumptions live_crcs_fits.
Locate live_crcs_null_fits.
Print Assumptions live_crcs_null_fits.
Locate live_rtt_fits.
Print Assumptions live_rtt_fits.
Locate live_pj_write_fits.
Print Assumptions live_pj_write_fits.
Locate padded_room_fits.
Print Assumptions padded_room_fits.
Locate live_tx_fits.
Print Assumptions live_tx_fits.
Locate tx_entry_sum.
Print Assumptions tx_entry_sum.
Locate preset_head.
Print Assumptions preset_head.
Locate alloc_req_fits.
Print Assumptions alloc_req_fits.
Locate strdup_req_fits.
Print Assumptions strdup_req_fits.
Locate live_parse_string_fits.
Print Assumptions live_parse_string_fits.
Locate live_grow_fits.
Print Assumptions live_grow_fits.
Locate live_pj_set_fits.
Print Assumptions live_pj_set_fits.
Locate live_pj_string_fits.
Print Assumptions live_pj_string_fits.
