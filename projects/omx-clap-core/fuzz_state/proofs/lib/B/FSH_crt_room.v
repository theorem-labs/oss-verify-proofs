(* check_round_trip (fs.asan-ubsan 0x81b9c), build B: its two room premises crt_room_D1 (HROOM) and crt_room_C2
   (HROOM2) of lib/B/FSH_crt_base.v hold for every cx that satisfies crt_base, so a lane takes them from
   crt_room_D1_holds / crt_room_C2_holds instead of a Section hypothesis. The B twin of a working branch
   532ce6e842d proofs/omx-clap-core/fuzz_state/lib/A/FSH_crt_room.v (blob a4f26d4b21f, a Theorem Labs lane), with the same names,
   statements and proofs over the B base (v33) and S0's lib/B statements.
   rule 24: proves no function (kind: segment lemma / room lemma of check_round_trip's walk, PORTED from 532ce6e842d)
   Nothing here reads the image: the lemmas are about the shared writer / reader models (lib/Prog WriterSpec,
   WriterApp, WriterValue, check_round_trip_stages_b, lib/Spec PjRoundTrip) and the budget constants. B's constants are
   S0's lib/B statements' own (lib/B/FSH_Fn_crt.v EV_check_round_trip / LIVE_check_round_trip, FSH_Fn_alloc.v
   EV_fuzz_malloc / EV_fuzz_free / EV_fuzz_realloc, FSH_Fn_writer.v wev0 / wcalls / enc_size / dec_size, FSH_Fn_reader.v
   rd_ev / rd_live, FSH_Fn_crt.v CRT_ALLOCS, and the EV_ / HEAD terms of K / CNT / LIVE_82218); their definitions are
   textually A's (checked against lib/A on S0 a9edd281227), so every closed value below (K_82218 = 19, CNT_82218 = 17,
   crtr_LC <= 4096, 78 / LIVE_check_round_trip) is the same number on B, and B makes the same calls (crt.calls.tsv).
   The A file's notes:
   - crtr_wcalls: pj_write's run makes at most 3 requests. Base64 has no `special` byte, so es is ONE piece; 140 bytes
     come before it and 8 after it; the first put allocates 4096, es grows the buffer at most once, the tail at most
     once more (the buffer is then at least 141 + |es| and doubles past 149 + |es|).
   - crtr_wcap: its buffer is at most 2 ^ 22 (newcap stops at the least 4096 * 2 ^ j that holds the text, and
     check_round_trip_stages_b.crt_doc_ok gives |wdoc| + 1 < 2 ^ 22).
   - crtr_rd_live: pj_parse's live bytes are |es| + 1352 (ech is the identity on base64 bytes).
   - crtr_es_len / crtr_tb_len: |es| <= 3 * 2 ^ 20 and |tb| <= 3 * 2 ^ 20 (crt_base's text bound and b64_dec).
   Clause 1 of crt_room_C2 is tight: 71 + wev0 <= 78, and wev0 = 7 on the 3-request path.
   Ported from (A's): crtr_six_len / crtr_dec_len are FSH_crt_segC2.v c2_six_len / c2_dec_len (a working branch
   be1fe777656, which port lib/Prog/check_no_overread.v:125-139); crtr_newcap22 / crtr_pow22 are
   lib/Prog/WriterSpecFacts.v newcap_le28 / pow4096_le with the bound 2 ^ 22. A new file: no licence lines. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
FSH_Base FSH_Rt FSPstat FSW_K FSW_K3 FSW_rres FSW_frame FSH_Fn_reader FSH_Fn_writer FSH_Fn_alloc FSH_Fn_crt.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0s YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import FSH_Base FSH_Rt FSPstat.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import FSH_crt_base.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec WriterSpecFacts HState pj_set_c
  check_round_trip_stages_b WriterValue WriterApp WriterAppFacts.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require PjTree PjGrammar PjRoundTrip.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
(* SINK GUARD (S0): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

(* ================= 1. the writer model over a list of piece lengths ================= *)
Definition crtr_sum (ls : list Z) : Z := fold_right Z.add 0 ls.

Lemma crtr_sum_nn : forall ls, Forall (fun l => 0 <= l) ls -> 0 <= crtr_sum ls.
Proof.
unfold crtr_sum. induction ls as [|l ls IH]; intros H; cbn [fold_right]; [lia|].
apply Forall_cons_iff in H as [H1 H2]. cbv beta in H1. specialize (IH H2). lia.
Qed.

Lemma crtr_sum_lens : forall P, crtr_sum (WriterSpec.piece_lens P) = Z.of_nat (length (concat P)).
Proof.
induction P as [|b P IH]; [reflexivity|].
rewrite WriterAppFacts.piece_lens_cons. unfold crtr_sum in *. cbn [fold_right concat].
rewrite IH, length_app, Nat2Z.inj_add. reflexivity.
Qed.

Lemma crtr_lens_nn : forall P, Forall (fun l => 0 <= l) (WriterSpec.piece_lens P).
Proof.
intros P. unfold WriterSpec.piece_lens. apply Forall_forall. intros l Hl.
apply in_map_iff in Hl as (b & <- & _). cbv beta. lia.
Qed.

Lemma crtr_gc_app : forall L1 L2 x c,
  WriterSpec.grow_calls x c (L1 ++ L2) =
  WriterSpec.grow_calls x c L1 ++ WriterSpec.grow_calls (x + crtr_sum L1) (WriterSpec.grow_cap x c L1) L2.
Proof.
unfold crtr_sum. induction L1 as [|l L1 IH]; intros L2 x c.
- cbn [app fold_right WriterSpec.grow_calls WriterSpec.grow_cap]. rewrite Z.add_0_r. reflexivity.
- cbn [app fold_right]. rewrite !WriterAppFacts.grow_calls_cons, WriterAppFacts.grow_cap_cons.
  replace (x + (l + fold_right Z.add 0 L1)) with (x + l + fold_right Z.add 0 L1) by lia.
  destruct (c <? x + l + 1); cbn [app]; rewrite IH; reflexivity.
Qed.

Lemma crtr_dbl_ge : forall f c need, 0 <= c -> c <= WriterSpec.dbl f c need.
Proof.
induction f as [|f IH]; intros c need Hc; cbn [WriterSpec.dbl]; [lia|].
destruct (need <=? c); cbv iota; [lia|]. specialize (IH (2 * c) need ltac:(lia)). lia.
Qed.

(* a grow from a live buffer at least doubles it *)
Lemma crtr_newcap_2x : forall c need, 0 < c -> c < need -> 2 * c <= WriterSpec.newcap c need.
Proof.
intros c need Hc Hn.
assert (E : WriterSpec.newcap c need = if need <=? c then c else WriterSpec.dbl 63 (2 * c) need).
{ unfold WriterSpec.newcap. destruct (Z.eqb_spec c 0); [lia | reflexivity]. }
rewrite E. destruct (Z.leb_spec need c); [lia|].
exact (crtr_dbl_ge 63 (2 * c) need ltac:(lia)).
Qed.

(* pieces that all fit make no request *)
Lemma crtr_calls_fit : forall ls x c, Forall (fun l => 0 <= l) ls -> x + crtr_sum ls + 1 <= c ->
  WriterSpec.grow_calls x c ls = [].
Proof.
induction ls as [|l ls IH]; intros x c Hl Hs; [reflexivity|].
apply Forall_cons_iff in Hl as [H1 H2]. cbv beta in H1.
pose proof (crtr_sum_nn ls H2) as H3. unfold crtr_sum in Hs, H3. cbn [fold_right] in Hs.
rewrite WriterAppFacts.grow_calls_cons.
destruct (Z.ltb_spec c (x + l + 1)) as [Hg|Hg]; cbv iota; [lia|].
apply IH; [exact H2 | unfold crtr_sum; lia].
Qed.

(* pieces that start inside a live buffer and end within twice it make at most one request *)
Lemma crtr_calls_one : forall ls x c, 0 < c -> Forall (fun l => 0 <= l) ls -> x + 1 <= c ->
  x + crtr_sum ls + 1 <= 2 * c -> (length (WriterSpec.grow_calls x c ls) <= 1)%nat.
Proof.
induction ls as [|l ls IH]; intros x c Hc Hl Hx Hs; [cbn [WriterSpec.grow_calls length]; lia|].
apply Forall_cons_iff in Hl as [H1 H2]. cbv beta in H1.
pose proof (crtr_sum_nn ls H2) as H3. unfold crtr_sum in Hs, H3. cbn [fold_right] in Hs.
rewrite WriterAppFacts.grow_calls_cons.
destruct (Z.ltb_spec c (x + l + 1)) as [Hg|Hg]; cbv iota.
- pose proof (crtr_newcap_2x c (x + l + 1) Hc Hg) as H4.
  rewrite (crtr_calls_fit ls (x + l) (WriterSpec.newcap c (x + l + 1)) H2 ltac:(unfold crtr_sum; lia)).
  cbn [length]. lia.
- apply IH; [exact Hc | exact H2 | lia | unfold crtr_sum; lia].
Qed.

(* the buffer bound (WriterSpecFacts.v pow4096_le / newcap_le28 at 2 ^ 22) *)
Lemma crtr_pow22 : forall j, 0 <= j -> 4096 * 2 ^ j < 2 ^ 23 -> 4096 * 2 ^ j <= 2 ^ 22.
Proof.
  intros j Hj H. destruct (Z_le_gt_dec j 10) as [Hle|Hgt].
  - assert (2 ^ j <= 2 ^ 10) by (apply Z.pow_le_mono_r; lia).
    assert (E : 2 ^ 22 = 4096 * 2 ^ 10) by reflexivity. lia.
  - assert (2 ^ 11 <= 2 ^ j) by (apply Z.pow_le_mono_r; lia).
    assert (E : 2 ^ 23 = 4096 * 2 ^ 11) by reflexivity. lia.
Qed.

Lemma crtr_newcap22 : forall c need,
  (c = 0 \/ exists j, 0 <= j <= 51 /\ c = 4096 * 2 ^ j) -> c < need <= 2 ^ 22 -> WriterSpec.newcap c need <= 2 ^ 22.
Proof.
  intros c need Hc Hn.
  assert (Hc0 : 0 <= c).
  { destruct Hc as [->|(j & Hj & ->)]; [lia|]. assert (0 < 2 ^ j) by (apply Z.pow_pos_nonneg; lia). lia. }
  assert (H63 : 2 ^ 22 <= 2 ^ 63) by (apply Z.pow_le_mono_r; lia).
  destruct (WriterSpecFacts.newcap_bound c need Hc ltac:(lia)) as (k & Hk & Ek & _ & _ & _).
  set (c0 := if c =? 0 then 4096 else c).
  assert (Hc1 : 0 < c0 <= 2 ^ 22).
  { assert (E : 2 ^ 22 = 4194304) by reflexivity. unfold c0. destruct (Z.eqb_spec c 0); lia. }
  assert (H64 : 2 ^ 22 <= 2 ^ Z.of_nat 64) by (apply Z.pow_le_mono_r; lia).
  assert (Hpre : need <= c0 * 2 ^ Z.of_nat 64) by nia.
  destruct (WriterSpecFacts.dbl_spec 64 c0 need ltac:(lia) Hpre) as (j & Hj & Ed & Hnd & Hmin).
  assert (Enc : WriterSpec.newcap c need = WriterSpec.dbl 64 c0 need) by reflexivity.
  destruct j as [|j'].
  - rewrite Enc, Ed. cbn [Z.of_nat]. rewrite Z.pow_0_r. lia.
  - destruct Hmin as [Hz|Hlt]; [discriminate|].
    assert (Hlt2 : WriterSpec.newcap c need < 2 ^ 23).
    { rewrite Enc, Ed. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
      rewrite Nat2Z.inj_succ in Hlt. replace (Z.succ (Z.of_nat j') - 1) with (Z.of_nat j') in Hlt by lia.
      assert (E : 2 ^ 23 = 2 * 2 ^ 22) by reflexivity. nia. }
    rewrite Ek in *. apply crtr_pow22; lia.
Qed.

Lemma crtr_gcap22 : forall ls x c, (c = 0 \/ exists j, 0 <= j <= 51 /\ c = 4096 * 2 ^ j) -> 0 <= c <= 2 ^ 22 ->
  0 <= x -> Forall (fun l => 0 <= l) ls -> x + crtr_sum ls + 1 <= 2 ^ 22 -> WriterSpec.grow_cap x c ls <= 2 ^ 22.
Proof.
assert (E22 : 2 ^ 22 = 4194304) by reflexivity. assert (E63 : 2 ^ 63 = 9223372036854775808) by reflexivity.
induction ls as [|l ls IH]; intros x c Hc Hc22 Hx Hl Hs; [cbn [WriterSpec.grow_cap]; lia|].
apply Forall_cons_iff in Hl as [H1 H2]. cbv beta in H1.
pose proof (crtr_sum_nn ls H2) as H3. unfold crtr_sum in Hs, H3. cbn [fold_right] in Hs.
rewrite WriterAppFacts.grow_cap_cons.
destruct (Z.ltb_spec c (x + l + 1)) as [Hg|Hg]; cbv iota.
- destruct (WriterSpecFacts.newcap_bound c (x + l + 1) Hc ltac:(lia)) as (j & Hj & Ej & _ & _ & Hle).
  pose proof (crtr_newcap22 c (x + l + 1) Hc ltac:(lia)) as H4.
  apply IH; [right; exists j; split; [exact Hj | exact Ej] | lia | lia | exact H2 | unfold crtr_sum; lia].
- apply IH; [exact Hc | lia | lia | exact H2 | unfold crtr_sum; lia].
Qed.

(* ================= 2. the document's pieces: 140 bytes, es as ONE piece, 8 bytes ================= *)
Lemma crtr_spieces_run : forall s run, Forall (fun c => WriterSpec.special c = false) s ->
  WriterSpec.spieces_run run s = [run ++ s].
Proof.
induction s as [|c s IH]; intros run H; cbn [WriterSpec.spieces_run].
- rewrite app_nil_r. reflexivity.
- apply Forall_cons_iff in H as [H1 H2]. rewrite H1. rewrite (IH (run ++ [c]) H2). rewrite <- app_assoc.
  reflexivity.
Qed.

Lemma crtr_spieces : forall s, Forall (fun c => WriterSpec.special c = false) s ->
  WriterSpec.spieces s = [[34]; s; [34]].
Proof.
intros s H. unfold WriterSpec.spieces. rewrite (crtr_spieces_run s [] H). reflexivity.
Qed.

(* the piece lengths of wdpieces (crt_doc es) true before and after es (MEASURED by a copy of WriterValue.wvpieces) *)
Definition crtr_pre : list Z :=
  [1; 1; 2; 1; 6; 1; 2; 1; 22; 1; 1; 1; 2; 1; 7; 1; 2; 1; 5; 1; 1; 1; 2; 1; 5; 1; 2; 1; 1; 2; 2; 1; 8; 1; 2; 1;
   6; 1; 1; 1; 2; 2; 1; 7; 1; 2; 1; 6; 1; 1; 1; 2; 2; 1; 5; 1; 2; 1].
Definition crtr_post : list Z := [1; 1; 2; 1; 1; 1; 1].

Lemma crtr_lens : forall es, Forall (fun c => WriterSpec.special c = false) es ->
  WriterSpec.piece_lens (WriterValue.wdpieces (PjTree.JObj (check_round_trip_stages_b.crt_doc es)) true) =
  crtr_pre ++ Z.of_nat (length es) :: crtr_post.
Proof.
intros es H.
unfold WriterValue.wdpieces, check_round_trip_stages_b.crt_doc, check_round_trip_stages_b.crt_st.
cbn [WriterValue.wvpieces]. rewrite (crtr_spieces es H). reflexivity.
Qed.

Lemma crtr_pre_vals : WriterSpec.grow_calls 0 0 crtr_pre = [4096] /\ WriterSpec.grow_cap 0 0 crtr_pre = 4096 /\
  crtr_sum crtr_pre = 140.
Proof. split; [|split]; vm_compute; reflexivity. Qed.

(* es and the tail: at most one request from es, at most one from the tail *)
Lemma crtr_tail_calls : forall n, 0 <= n <= 3 * 2 ^ 20 ->
  (length (WriterSpec.grow_calls 140 4096 (n :: crtr_post)) <= 2)%nat.
Proof.
intros n Hn.
assert (E20 : 2 ^ 20 = 1048576) by reflexivity. assert (E63 : 2 ^ 63 = 9223372036854775808) by reflexivity.
assert (Fp : Forall (fun l => 0 <= l) crtr_post).
{ unfold crtr_post. repeat (apply Forall_cons; [cbv beta; lia|]). apply Forall_nil. }
assert (Sp : crtr_sum crtr_post = 8) by reflexivity.
assert (H4096 : 4096 = 0 \/ exists j, 0 <= j <= 51 /\ 4096 = 4096 * 2 ^ j)
  by (right; exists 0; split; [lia | reflexivity]).
rewrite WriterAppFacts.grow_calls_cons.
destruct (Z.ltb_spec 4096 (140 + n + 1)) as [Hg|Hg]; cbv iota.
- destruct (WriterSpecFacts.newcap_bound 4096 (140 + n + 1) H4096 ltac:(lia)) as (j & Hj & Ej & Hneed & _ & _).
  pose proof (crtr_newcap_2x 4096 (140 + n + 1) ltac:(lia) Hg) as H2x.
  pose proof (crtr_calls_one crtr_post (140 + n) (WriterSpec.newcap 4096 (140 + n + 1)) ltac:(lia) Fp
    ltac:(lia) ltac:(rewrite Sp; lia)) as H1.
  cbn [length]. lia.
- pose proof (crtr_calls_one crtr_post (140 + n) 4096 ltac:(lia) Fp ltac:(lia) ltac:(rewrite Sp; lia)) as H1.
  lia.
Qed.

Lemma crtr_doc_calls : forall es, Forall (fun c => WriterSpec.special c = false) es ->
  Z.of_nat (length es) <= 3 * 2 ^ 20 ->
  (length (WriterSpec.grow_calls 0 0 (WriterSpec.piece_lens
     (WriterValue.wdpieces (PjTree.JObj (check_round_trip_stages_b.crt_doc es)) true))) <= 3)%nat.
Proof.
intros es H Hl. rewrite (crtr_lens es H), crtr_gc_app.
destruct crtr_pre_vals as (E1 & E2 & E3). rewrite E1, E2, E3. change (0 + 140) with 140.
pose proof (crtr_tail_calls (Z.of_nat (length es)) ltac:(lia)) as T.
rewrite length_app. cbn [length]. lia.
Qed.

(* ================= 3. pj_parse's trace over the document ================= *)
Definition crtr_tpre : list PjGrammar.ev :=
  Eval vm_compute in removelast (PjRoundTrip.ttrace (PjTree.JObj (check_round_trip_stages_b.crt_doc []))).

(* es's string block is the trace's last event *)
Lemma crtr_TR_split : forall es,
  PjRoundTrip.ttrace (PjTree.JObj (check_round_trip_stages_b.crt_doc es)) =
  crtr_tpre ++ [PjGrammar.EAlloc (S (length (flat_map PjRoundTrip.ech es)))].
Proof. intros es. reflexivity. Qed.

Lemma crtr_rd_live_app : forall a b, rd_live (a ++ b) = rd_live a + rd_live b.
Proof.
induction a as [|e a IH]; intros b; [reflexivity|].
change ((e :: a) ++ b) with (e :: (a ++ b)).
cbn [rd_live fold_right]. fold (rd_live (a ++ b)) (rd_live a) (rd_live b). rewrite IH. lia.
Qed.

Lemma crtr_TR_live : forall es, Forall (fun c => WriterSpec.special c = false) es ->
  rd_live (PjRoundTrip.ttrace (PjTree.JObj (check_round_trip_stages_b.crt_doc es))) = Z.of_nat (length es) + 1352.
Proof.
intros es H. rewrite crtr_TR_split, crtr_rd_live_app, (check_round_trip_stages_b.crt_ns_ech es H).
assert (E : rd_live crtr_tpre = 1335) by (vm_compute; reflexivity).
rewrite E. cbn [rd_live fold_right PjGrammar.esize]. unfold HEAD. lia.
Qed.

Lemma crtr_TR15 : forall es,
  rd_ev (PjRoundTrip.ttrace (PjTree.JObj (check_round_trip_stages_b.crt_doc es))) = 15 /\
  crt_trlen (PjRoundTrip.ttrace (PjTree.JObj (check_round_trip_stages_b.crt_doc es))) = 15.
Proof. intros es. split; vm_compute; reflexivity. Qed.

(* ================= 4. the decoded body (FSH_crt_segC2.v c2_six_len / c2_dec_len) ================= *)
Lemma crtr_six_len : forall six, (length (WriterSpec.six_bytes six) * 4 <= length six * 3)%nat.
Proof.
  fix IH 1. intros [|a [|b [|c [|e r]]]]; cbn [WriterSpec.six_bytes length]; try lia.
  specialize (IH r). lia.
Qed.
Lemma crtr_dec_len : forall tb bs, WriterSpec.b64_dec tb = Some bs -> (length bs * 4 <= length tb * 3)%nat.
Proof.
  intros tb bs H. unfold WriterSpec.b64_dec in H.
  destruct (WriterSpec.b64_scan 0 [] tb) as [[six pad]|] eqn:E; [|discriminate].
  destruct ((pad <=? 2) && WriterSpec.six_tail_ok six); [|discriminate]. injection H as <-.
  destruct (WriterSpecFacts.scan_inv tb 0 [] six pad E) as [H1 _]. cbn [length] in H1.
  pose proof (crtr_six_len six). lia.
Qed.

(* the closed part of LIVE_82218 *)
Definition crtr_LC : Z :=
  157 + rd_live (pj_set_c.set_trace 0 0 6) + 2 * rd_live (pj_set_c.set_trace 1 8 7) +
  rd_live (pj_set_c.set_trace 0 0 8) + 2 * rd_live (pj_set_c.set_trace 2 8 5).
Lemma crtr_LC_le : crtr_LC <= 4096.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.

Lemma crtr_wev0_le : forall w, FSH_Fn_writer.wcalls w <= 3 -> 0 <= FSH_Fn_writer.wev0 w <= 7.
Proof.
intros w H. unfold FSH_Fn_writer.wcalls, FSH_Fn_writer.wev0 in *.
destruct (WriterApp.w_calls w) as [|c r]; cbn [length] in *; unfold EV_fuzz_malloc, EV_fuzz_realloc; lia.
Qed.

(* the budget constants these lemmas unfold (KERNEL TRAP: let the kernel unfold them first) *)
Local Strategy expand [K_822ac K_82268 K_82218 CNT_82268 CNT_82218 LIVE_82268 LIVE_82218 LIVE_821ac LIVE_82068
  crt_room_D1 crt_room_C2 crtr_LC].

Lemma crtr_K18 : forall cx, K_82218 cx = 19 /\ CNT_82218 cx = 17.
Proof. intros cx. split; vm_compute; reflexivity. Qed.

Lemma crtr_LIVE18 : forall cx, LIVE_82218 cx =
  3 * Z.of_nat (length (crt_es cx)) + 2 + Z.of_nat (length (c_tb cx)) + FSH_Fn_writer.dec_size (crt_es cx) + crtr_LC.
Proof.
intros cx.
assert (Henc : FSH_Fn_writer.enc_size (crt_len cx) = Z.of_nat (length (crt_es cx)) + 1).
{ unfold FSH_Fn_writer.enc_size, crt_len, crt_es.
  rewrite WriterSpecFacts.b64_enc_length, Nat2Z.inj_mul, Nat2Z.inj_div, Nat2Z.inj_add. reflexivity. }
unfold LIVE_82218, LIVE_821ac, LIVE_82068, crtr_LC. rewrite Henc. unfold HEAD. lia.
Qed.

(* ================= 5. the facts at check_round_trip's entry (crt_base) ================= *)
Section r. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.

Lemma crtr_bs : forall cx, crt_base B cx ->
  WriterSpec.bytes_ok (c_bs cx) /\ Z.of_nat (length (c_bs cx)) <= 9 * 2 ^ 18.
Proof.
intros cx HB. destruct HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Htb & _ & _ & Hdec & _).
assert (E18 : 2 ^ 18 = 262144) by reflexivity. assert (E20 : 2 ^ 20 = 1048576) by reflexivity.
split; [exact (WriterSpecFacts.b64_dec_ok _ _ Hdec)|].
pose proof (crtr_dec_len _ _ Hdec) as Hl. unfold HState.zs in Hl. rewrite length_map in Hl. lia.
Qed.

Lemma crtr_tb_len : forall cx, crt_base B cx -> Z.of_nat (length (c_tb cx)) <= 3 * 2 ^ 20.
Proof.
intros cx HB. destruct HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Htb & _). exact Htb.
Qed.

Lemma crtr_es_len : forall cx, crt_base B cx -> Z.of_nat (length (crt_es cx)) <= 3 * 2 ^ 20.
Proof.
intros cx HB. destruct (crtr_bs cx HB) as (_ & Hbl).
assert (E18 : 2 ^ 18 = 262144) by reflexivity. assert (E20 : 2 ^ 20 = 1048576) by reflexivity.
unfold crt_es. rewrite WriterSpecFacts.b64_enc_length, Nat2Z.inj_mul, Nat2Z.inj_div, Nat2Z.inj_add.
Z.div_mod_to_equations. lia.
Qed.

Lemma crtr_es_ns : forall cx, crt_base B cx -> Forall (fun c => WriterSpec.special c = false) (crt_es cx).
Proof.
intros cx HB. destruct (crtr_bs cx HB) as (Hbo & _). exact (check_round_trip_stages_b.crt_enc_ns (c_bs cx) Hbo).
Qed.

Lemma crtr_wcalls : forall cx, crt_base B cx -> FSH_Fn_writer.wcalls (crt_wst cx) <= 3.
Proof.
intros cx HB.
assert (E : FSH_Fn_writer.wcalls (crt_wst cx) =
  Z.of_nat (length (WriterSpec.grow_calls 0 0 (WriterSpec.piece_lens (crt_wpieces cx))))) by reflexivity.
rewrite E. unfold crt_wpieces.
pose proof (crtr_doc_calls (crt_es cx) (crtr_es_ns cx HB) (crtr_es_len cx HB)) as H. lia.
Qed.

Lemma crtr_wcap : forall cx, crt_base B cx -> WriterApp.w_cap (crt_wst cx) <= 2 ^ 22.
Proof.
intros cx HB. destruct (crtr_bs cx HB) as (Hbo & Hbl).
assert (E18 : 2 ^ 18 = 262144) by reflexivity. assert (E22 : 2 ^ 22 = 4194304) by reflexivity.
destruct (check_round_trip_stages_b.crt_doc_ok (c_bs cx) Hbo ltac:(lia)) as (_ & _ & _ & _ & Hw & _).
assert (E : WriterApp.w_cap (crt_wst cx) = WriterSpec.grow_cap 0 0 (WriterSpec.piece_lens (crt_wpieces cx)))
  by reflexivity.
rewrite E. apply crtr_gcap22.
- left. reflexivity.
- lia.
- lia.
- apply crtr_lens_nn.
- rewrite crtr_sum_lens. unfold crt_wpieces, crt_es. unfold WriterValue.wdoc in Hw. lia.
Qed.

Lemma crtr_rd_live : forall cx, crt_base B cx -> rd_live (crt_TR cx) = Z.of_nat (length (crt_es cx)) + 1352.
Proof. intros cx HB. unfold crt_TR. exact (crtr_TR_live (crt_es cx) (crtr_es_ns cx HB)). Qed.

Lemma crtr_dec : forall cx, crt_base B cx -> FSH_Fn_writer.dec_size (crt_es cx) <= 2359299.
Proof.
intros cx HB. pose proof (crtr_es_len cx HB) as H. assert (E20 : 2 ^ 20 = 1048576) by reflexivity.
unfold FSH_Fn_writer.dec_size. Z.div_mod_to_equations. lia.
Qed.

(* ================= 6. the two room premises ================= *)
Lemma crt_room_D1_holds : forall cx, crt_base B cx -> crt_room_D1 cx.
Proof.
intros cx HB.
destruct (crtr_K18 cx) as (EK & _).
assert (ER : rd_ev (crt_TR cx) = 15) by exact (proj1 (crtr_TR15 (crt_es cx))).
pose proof (crtr_wev0_le (crt_wst cx) (crtr_wcalls cx HB)) as Hev.
pose proof (crtr_wcap cx HB) as Hcap. pose proof (crtr_rd_live cx HB) as HL.
pose proof (crtr_es_len cx HB) as Hes. pose proof (crtr_tb_len cx HB) as Htb.
pose proof (crtr_dec cx HB) as Hdec. pose proof (crtr_LIVE18 cx) as H18. pose proof crtr_LC_le as HLC.
assert (E20 : 2 ^ 20 = 1048576) by reflexivity. assert (E22 : 2 ^ 22 = 4194304) by reflexivity.
assert (E25 : 2 ^ 25 = 33554432) by reflexivity.
unfold crt_room_D1, K_822ac, K_82268, LIVE_82268. change (WriterSpec.b64_enc (c_bs cx)) with (crt_es cx).
rewrite EK, ER.
unfold EV_check_round_trip, EV_fuzz_malloc, EV_fuzz_free, LIVE_check_round_trip, HEAD.
split; lia.
Qed.

Lemma crt_room_C2_holds : forall cx, crt_base B cx -> crt_room_C2 cx.
Proof.
intros cx HB.
destruct (crtr_K18 cx) as (EK & EC).
assert (ER : rd_ev (crt_TR cx) = 15) by exact (proj1 (crtr_TR15 (crt_es cx))).
assert (ET : crt_trlen (crt_TR cx) = 15) by exact (proj2 (crtr_TR15 (crt_es cx))).
pose proof (crtr_wcalls cx HB) as Hw. pose proof (crtr_wev0_le (crt_wst cx) Hw) as Hev.
pose proof (crtr_wcap cx HB) as Hcap. pose proof (crtr_rd_live cx HB) as HL.
pose proof (crtr_es_len cx HB) as Hes. pose proof (crtr_tb_len cx HB) as Htb.
pose proof (crtr_dec cx HB) as Hdec. pose proof (crtr_LIVE18 cx) as H18. pose proof crtr_LC_le as HLC.
assert (E20 : 2 ^ 20 = 1048576) by reflexivity. assert (E22 : 2 ^ 22 = 4194304) by reflexivity.
assert (E25 : 2 ^ 25 = 33554432) by reflexivity.
unfold crt_room_C2. rewrite EK, EC, ER, ET.
unfold EV_check_round_trip, EV_fuzz_malloc, EV_fuzz_free, CRT_EV_WRAP, LIVE_check_round_trip, HEAD.
split; [lia|]. split; lia.
Qed.
End r.
