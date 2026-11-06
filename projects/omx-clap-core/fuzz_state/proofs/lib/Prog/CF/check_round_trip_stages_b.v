(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cjson/cjson_read_fuzzer/lib/A/RTW_q_rec2.v, with its module paths and module names changed; 648 of its 746 lines of code are new or changed and 1953 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/Prog/check_round_trip_runs.v, with its module paths, module names, addresses and numbers changed; 556 of its 631 lines of code are new or changed and 671 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/Prog/CF/past_nul.v, with its module names changed; 711 of its 786 lines of code are new or changed and 556 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/Prog/CF/check_as_written.v, with its module names, addresses and numbers changed; 1716 of its 1784 lines of code are new or changed and 718 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/Prog/CF/check_no_overread.v, with its module paths, module names and numbers changed; 1316 of its 1472 lines of code are new or changed and 1628 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/Prog/CF/check_round_trip_calls.v; 242 of its 427 lines of code are new or changed and 1287 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/Prog/CF/check_round_trip_sd7.v, with its addresses changed; 999 of its 1126 lines of code are new or changed and 300 lines of the source are left out. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require Import Img0.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YL01 YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require Import Contract MemNorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require Import AllocSlots AllocRoom.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import Ledger LedgerFacts HState ReaderRes WriterSpec PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog.CF Require Import KindBGlue HStateRoom fuzz_free_c fuzz_malloc_c preset_base64_encode_c preset_base64_decode_c pj_string_c pj_set_c pj_free_c pj_parse_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import WriterApp WriterAppFacts WriterValue.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog.CF Require Import put_c put_string_c indent_c write_value_c pj_write_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require strtod_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import check_round_trip_runs.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog.CF Require Import check_round_trip_c check_round_trip_glue check_round_trip_calls check_round_trip_stages_a.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require HsKindB.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog.CF Require check_reject_clean_starved past_nul.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog.CF Require Import CFS ContractCF FrameCF ReaderResCF.
Import ListNotations.
Local Open Scope Z_scope.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import strlen_c strcmp_c bcmp_c pj_object_c pj_get_c pj_get_str_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpecFacts.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog.CF Require put.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog.CF Require Import check_round_trip_st8.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog.CF Require Import CFS ContractCF FrameCF ReaderResCF.

(* check_round_trip (check_4, plain, 0x138ac): the stages from c8 (pj_string(&v, "base64"), the statement St8 of
   check_round_trip_st8.v) to c16 (pj_parse), on the frame invariant and the stages of check_round_trip_stages_a.v. *)

#[local] Set Default Proof Using "All".

(* The document the function builds and writes: {"format": "org.openmixer.preset/2", "carries": "state",
   "state": {"encoding": "base64", "context": "preset", "bytes": <the encoded body>}}. The members of "format" and
   "carries" (CRT_FORMAT, CRT_FMT2, CRT_CARRIES, crt_doc8) are those of check_round_trip_st8.v. *)
Definition K_ENCODING : list Z := [101; 110; 99; 111; 100; 105; 110; 103].
Definition V_BASE64 : list Z := [98; 97; 115; 101; 54; 52].
Definition K_CONTEXT : list Z := [99; 111; 110; 116; 101; 120; 116].
Definition V_PRESET : list Z := [112; 114; 101; 115; 101; 116].

Definition crt_s1 : list (list Z * jv) := [(K_ENCODING, JStr V_BASE64)].
Definition crt_s2 : list (list Z * jv) := [(K_ENCODING, JStr V_BASE64); (K_CONTEXT, JStr V_PRESET)].
Definition crt_st (es : list Z) : list (list Z * jv) :=
  [(K_ENCODING, JStr V_BASE64); (K_CONTEXT, JStr V_PRESET); (CRT_BYTES, JStr es)].
Definition crt_doc (es : list Z) : list (list Z * jv) :=
  [(CRT_FORMAT, JStr CRT_FMT2); (CRT_CARRIES, JStr CRT_STATE); (CRT_STATE, JObj (crt_st es))].

Ltac crt_flit := repeat (apply Forall_cons; [cbv beta; lia|]); apply Forall_nil.
Ltac crt_notin := let H := fresh in intro H; cbv [crt_doc8 crt_s1 crt_s2] in H; cbn [map fst In] in H;
  unfold CRT_FORMAT, CRT_CARRIES, K_ENCODING, K_CONTEXT, CRT_STATE, CRT_BYTES in H;
  repeat (destruct H as [H|H]; [discriminate H|]); destruct H.
Ltac crt_dep := apply Nat.leb_le; vm_compute; reflexivity.
Ltac crt_vm := apply Z.leb_le; vm_compute; reflexivity.
Ltac crt_lits := unfold bytes_ok, no_zero, CRT_FORMAT, CRT_FMT2, CRT_CARRIES, CRT_STATE, K_ENCODING, V_BASE64, K_CONTEXT,
  V_PRESET, CRT_BYTES; crt_flit.

(* Bytes of the read-only image: a literal with its nul and the slack up to the next 8-byte boundary. *)
Fixpoint crt_chk (a : Z) (l : list byte) : bool :=
  match l with
  | [] => true
  | x :: r => Mem.ro_addr rsegs (Mem.wa a) &&
      match seg_rom rsegs (Mem.wa a) with Some y => bv_eqb y x | None => false end && crt_chk (a + 1) r
  end.

Lemma crt_chk_ok : forall l a, crt_chk a l = true -> forall i, (i < length l)%nat ->
  Mem.ro_addr rsegs (Mem.wa (a + Z.of_nat i)) = true /\ seg_rom rsegs (Mem.wa (a + Z.of_nat i)) = nth_error l i.
Proof.
  induction l as [|x l IH]; intros a H i Hi; cbn [length] in Hi; [lia|].
  cbn [crt_chk] in H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  destruct i as [|i].
  - replace (a + Z.of_nat 0) with a by lia. split; [exact H1|].
    destruct (seg_rom rsegs (Mem.wa a)) as [y|]; [|discriminate]. cbn [nth_error]. f_equal.
    unfold bv_eqb in H2. apply Z.eqb_eq in H2. apply bv_eq. exact H2.
  - destruct (IH (a + 1) H3 i ltac:(lia)) as [G1 G2]. replace (a + Z.of_nat (S i)) with (a + 1 + Z.of_nat i) by lia.
    split; [exact G1 | exact G2].
Qed.

Definition crt_slk (k : Z) (K : list Z) : list byte :=
  map (fun i => match seg_rom rsegs (Mem.wa (k + Z.of_nat (length K) + 1 + Z.of_nat i)) with
                | Some y => y | None => Z_to_bv 8 0 end)
    (seq 0 (Z.to_nat ((- (k + Z.of_nat (length K) + 1)) mod 8))).

Lemma crt_key : forall m k K, ro_agree rsegs m -> 0 <= k -> k + Z.of_nat (length K) + 9 <= 2 ^ 64 ->
  crt_chk k (map (Z_to_bv 8) K ++ Z_to_bv 8 0 :: crt_slk k K) = true ->
  Mem.bytes_at rsegs m k (map (Z_to_bv 8) K ++ Z_to_bv 8 0 :: crt_slk k K) /\
  (- (k + Z.of_nat (length (map (Z_to_bv 8) K)) + 1)) mod 8 <= Z.of_nat (length (crt_slk k K)) /\
  (forall i, 0 <= i < Z.of_nat (length (map (Z_to_bv 8) K)) + 1 + Z.of_nat (length (crt_slk k K)) ->
     Mem.ro_addr rsegs (Z_to_bv 64 (k + i)) = true).
Proof.
  intros m k K RA Hk Hb HC.
  pose proof (Z.mod_pos_bound (- (k + Z.of_nat (length K) + 1)) 8 ltac:(lia)) as Hr.
  assert (HS : Z.of_nat (length (crt_slk k K)) = (- (k + Z.of_nat (length K) + 1)) mod 8).
  { unfold crt_slk. rewrite length_map, length_seq. apply Z2Nat.id. lia. }
  assert (HL : length (map (Z_to_bv 8) K ++ Z_to_bv 8 0 :: crt_slk k K) = (length K + 1 + length (crt_slk k K))%nat).
  { rewrite length_app, length_map. cbn [length]. lia. }
  pose proof (crt_chk_ok _ k HC) as HO. rewrite length_map. split; [|split].
  - split; [exact Hk|]. split; [rewrite HL; lia|]. intros i Hi. destruct (HO i Hi) as [H1 H2].
    rewrite <- H2. exact (RA _ H1).
  - lia.
  - intros i Hi. destruct (HO (Z.to_nat i) ltac:(rewrite HL; lia)) as [H1 _]. rewrite Z2Nat.id in H1 by lia. exact H1.
Qed.

Ltac crt_keyt RA k K :=
  destruct (crt_key _ k K RA ltac:(lia) ltac:(crt_vm) ltac:(vm_compute; reflexivity)) as (KB & KS & KRO).

Lemma perm_swap3 : forall {T : Type} (A B C : list T), Permutation (A ++ B ++ C) (B ++ A ++ C).
Proof. intros T A B C. rewrite !app_assoc. apply Permutation_app_tail, Permutation_app_comm. Qed.

Lemma crt_psm : forall ms k v, ~ In k (map fst ms) -> pj_set_model ms k v = ms ++ [(k, v)].
Proof.
  induction ms as [|[k' v'] ms IH]; intros k v H; [reflexivity|]. cbn [pj_set_model].
  destruct (list_eq_dec Z.eq_dec k' k) as [E|E]; [exfalso; apply H; left; exact E|].
  cbn [app]. f_equal. apply IH. intros H'. apply H. right. exact H'.
Qed.

Lemma crt_wf_snoc : forall ms k tv, PjRoundTrip.pj_wf jr_strtod (JObj ms) -> PjRoundTrip.pj_wf jr_strtod tv ->
  Forall (fun b => 0 < b < 256) k -> ~ In k (map fst ms) -> (depth (JObj (ms ++ [(k, tv)])) <= MAXD)%nat ->
  PjRoundTrip.pj_wf jr_strtod (JObj (ms ++ [(k, tv)])).
Proof.
  intros ms k tv W1 W2 Hk Hn Hd. rewrite <- (crt_psm ms k tv Hn) in *. apply PjRoundTrip.wf_set; assumption.
Qed.

Lemma crt_b64c_ns : forall v, 0 <= v < 64 -> special (b64c v) = false.
Proof.
  intros v Hv.
  assert (A : forallb (fun n => negb (special (b64c (Z.of_nat n)))) (seq 0 64) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in A. specialize (A (Z.to_nat v) ltac:(apply in_seq; lia)).
  rewrite Z2Nat.id in A by lia. destruct (special (b64c v)); [discriminate | reflexivity].
Qed.

Lemma crt_enc_ns : forall bs, bytes_ok bs -> Forall (fun c => special c = false) (b64_enc bs).
Proof.
  intros bs. induction bs as [|a|a b|a b c l IH] using WriterSpecFacts.list3_ind; intros Hb.
  - constructor.
  - destruct (WriterSpecFacts.bytes_ok_cons _ _ Hb) as [Ha _]. cbn [b64_enc].
    repeat constructor; apply crt_b64c_ns; Z.div_mod_to_equations; lia.
  - destruct (WriterSpecFacts.bytes_ok_cons _ _ Hb) as [Ha Hb1].
    destruct (WriterSpecFacts.bytes_ok_cons _ _ Hb1) as [Hb2 _]. cbn [b64_enc].
    repeat constructor; apply crt_b64c_ns; Z.div_mod_to_equations; lia.
  - destruct (WriterSpecFacts.bytes_ok_cons _ _ Hb) as [Ha Hb1].
    destruct (WriterSpecFacts.bytes_ok_cons _ _ Hb1) as [Hb2 Hb3].
    destruct (WriterSpecFacts.bytes_ok_cons _ _ Hb3) as [Hc Hl]. cbn [b64_enc].
    constructor; [apply crt_b64c_ns; Z.div_mod_to_equations; lia|].
    constructor; [apply crt_b64c_ns; Z.div_mod_to_equations; lia|].
    constructor; [apply crt_b64c_ns; Z.div_mod_to_equations; lia|].
    constructor; [apply crt_b64c_ns; Z.div_mod_to_equations; lia|].
    exact (IH Hl).
Qed.

Lemma crt_ns_ech : forall es, Forall (fun c => special c = false) es -> flat_map PjRoundTrip.ech es = es.
Proof.
  induction es as [|c es IH]; intros H; [reflexivity|]. apply Forall_cons_iff in H as [H1 H2].
  cbn [flat_map]. unfold PjRoundTrip.ech at 1. rewrite H1. cbn [app]. f_equal. exact (IH H2).
Qed.

Lemma crt_ns_esc : forall es, Forall (fun c => special c = false) es -> WriterSpecFacts.escaped es = es.
Proof.
  induction es as [|c es IH]; intros H; [reflexivity|]. apply Forall_cons_iff in H as [H1 H2].
  unfold WriterSpecFacts.escaped in *. cbn [flat_map]. rewrite H1. cbn [app]. f_equal. exact (IH H2).
Qed.

Lemma crt_zb_map : forall l, bytes_ok l -> zb (map (Z_to_bv 8) l) = l.
Proof.
  intros l H. unfold zb. rewrite map_map. rewrite <- (map_id l) at 2. apply map_ext_in.
  intros c Hc. unfold bytes_ok in H. rewrite Forall_forall in H. pose proof (H c Hc) as Hr. cbv beta in Hr.
  rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. lia.
Qed.

Lemma crt_map_nz : forall l, no_zero l -> bytes_ok l -> ~ In (Z_to_bv 8 0) (map (Z_to_bv 8) l).
Proof.
  intros l NZ BO H. apply in_map_iff in H as (c & E & Hc). unfold no_zero, bytes_ok in *.
  rewrite Forall_forall in NZ, BO. pose proof (NZ c Hc) as H1. pose proof (BO c Hc) as H2. cbv beta in *.
  assert (U : bv_unsigned (Z_to_bv 8 c) = c).
  { rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. lia. }
  rewrite E in U. change (bv_unsigned (Z_to_bv 8 0)) with 0 in U. lia.
Qed.

Lemma crt_es_len : forall bs, Z.of_nat (length bs) <= 9 * 2 ^ 18 + 2 -> Z.of_nat (length (b64_enc bs)) <= 3145732.
Proof.
  intros bs HL. rewrite WriterSpecFacts.b64_enc_length, Nat2Z.inj_mul, Nat2Z.inj_div, Nat2Z.inj_add.
  Z.div_mod_to_equations. lia.
Qed.

(* What pj_write and pj_parse need of the document. *)
Lemma crt_doc_ok : forall bs, bytes_ok bs -> Z.of_nat (length bs) <= 9 * 2 ^ 18 + 2 ->
  PjRoundTrip.pj_wf jr_strtod (JObj (crt_doc (b64_enc bs))) /\ (depth (JObj (crt_doc (b64_enc bs))) <= 2)%nat /\
  length (PjRoundTrip.ttrace (JObj (crt_doc (b64_enc bs)))) = 15%nat /\
  Forall (fun e => Z.of_nat (esize e) + 16 <= CRT_SIZE) (PjRoundTrip.ttrace (JObj (crt_doc (b64_enc bs)))) /\
  Z.of_nat (length (wdoc (JObj (crt_doc (b64_enc bs))) true)) + 1 < 2 ^ 22 /\
  no_zero (wdoc (JObj (crt_doc (b64_enc bs))) true) /\ bytes_ok (wdoc (JObj (crt_doc (b64_enc bs))) true) /\
  Z.of_nat (length (b64_enc bs)) <= 2 ^ 28 /\ dec_size (b64_enc bs) + 16 <= CRT_SIZE.
Proof.
  intros bs HB HL.
  pose proof (crt_enc_ns bs HB) as NS. pose proof (WriterSpecFacts.b64_enc_chars bs HB) as CH.
  pose proof (WriterSpecFacts.b64_enc_ok bs HB) as EOK. pose proof (WriterSpecFacts.b64_enc_no_zero bs HB) as ENZ.
  pose proof (crt_es_len bs HL) as Hes.
  set (es := b64_enc bs) in *.
  assert (WS : PjRoundTrip.pj_wf jr_strtod (JObj (crt_st es))).
  { unfold crt_st.
    apply (crt_wf_snoc [(K_ENCODING, JStr V_BASE64); (K_CONTEXT, JStr V_PRESET)] CRT_BYTES (JStr es)).
    - apply (crt_wf_snoc [(K_ENCODING, JStr V_BASE64)] K_CONTEXT (JStr V_PRESET)).
      + apply (crt_wf_snoc [] K_ENCODING (JStr V_BASE64)).
        * apply PjRoundTrip.wf_object.
        * apply PjRoundTrip.wf_string. unfold V_BASE64. crt_flit.
        * unfold K_ENCODING. crt_flit.
        * crt_notin.
        * crt_dep.
      + apply PjRoundTrip.wf_string. unfold V_PRESET. crt_flit.
      + unfold K_CONTEXT. crt_flit.
      + crt_notin.
      + crt_dep.
    - apply PjRoundTrip.wf_string. eapply Forall_impl; [|exact CH]. intros c Hc. cbv beta in *. lia.
    - unfold CRT_BYTES. crt_flit.
    - crt_notin.
    - crt_dep. }
  split.
  { unfold crt_doc.
    apply (crt_wf_snoc [(CRT_FORMAT, JStr CRT_FMT2); (CRT_CARRIES, JStr CRT_STATE)] CRT_STATE (JObj (crt_st es))).
    - apply (crt_wf_snoc [(CRT_FORMAT, JStr CRT_FMT2)] CRT_CARRIES (JStr CRT_STATE)).
      + apply (crt_wf_snoc [] CRT_FORMAT (JStr CRT_FMT2)).
        * apply PjRoundTrip.wf_object.
        * apply PjRoundTrip.wf_string. unfold CRT_FMT2. crt_flit.
        * unfold CRT_FORMAT. crt_flit.
        * crt_notin.
        * crt_dep.
      + apply PjRoundTrip.wf_string. unfold CRT_STATE. crt_flit.
      + unfold CRT_CARRIES. crt_flit.
      + crt_notin.
      + crt_dep.
    - exact WS.
    - unfold CRT_STATE. crt_flit.
    - crt_notin.
    - crt_dep. }
  split; [crt_dep|].
  split; [vm_compute; reflexivity|].
  split.
  { apply Forall_forall. intros e He. unfold crt_doc, crt_st in He. cbn in He.
    rewrite (crt_ns_ech es NS) in He.
    repeat (destruct He as [<-|He]; [cbn [esize]; unfold CRT_SIZE; lia|]). destruct He. }
  assert (JB : jv_bytes_ok (JObj (crt_doc es))).
  { unfold crt_doc, crt_st. cbn [jv_bytes_ok].
    repeat split; try exact EOK; try exact ENZ; crt_lits. }
  split.
  { assert (WL : (length (wdoc (JObj (crt_doc es)) true) <= length es + 1000)%nat).
    { unfold wdoc, wdpieces, crt_doc, crt_st. cbn.
      repeat match goal with |- context [Z.to_nat ?x] =>
        let v := eval vm_compute in (Z.to_nat x) in replace (Z.to_nat x) with v by (vm_compute; reflexivity) end.
      cbn. rewrite !concat_app, WriterSpecFacts.concat_spieces_run, (crt_ns_esc es NS), !length_app. cbn. lia. }
    lia. }
  destruct (wdoc_no_zero (JObj (crt_doc es)) true JB) as [W1 W2].
  split; [exact W1|]. split; [exact W2|]. split; [lia|]. unfold dec_size, CRT_SIZE. Z.div_mod_to_equations. lia.
Qed.

Section ST.
Context {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let MR := aa_MR API.
Hypothesis SEG : ms_segs B = rsegs.
Hypothesis MAL : ms_malloc B = 0x16594.
Hypothesis FRE : ms_free B = 0x16454.
Hypothesis ERR : errno_addr B + 4 <= alloc_ceiling.
Hypothesis GF : globals_free B API [(G_FAIL, 8); (G_LIVE, 24)].
Hypothesis AX : YL01.AllocExtra B MR.
Hypothesis CO : ctx_owned B API.
Hypothesis BSP : block_slack_present B API.
Hypothesis RTP : ms_tp B = strtod_c.STRTOD_TP.
Hypothesis RER : errno_addr B = strtod_c.STRTOD_ERRNO.
Hypothesis RGG : ms_got_guard B = strtod_c.STRTOD_GOT_GUARD.
Hypothesis RGD : ms_guard B = strtod_c.STRTOD_GUARD.
Hypothesis STRLEN : strlen_contract.
Hypothesis STRCMP : strcmp_contract.
Hypothesis BCMP : bcmp_contract.
Hypothesis PJO : pj_object_contract.
Hypothesis PJG : pj_get_contract.
Hypothesis PJGS : pj_get_str_contract.
Hypothesis MALLOC : forall fx' : YK11.FPState, malloc_contract (fx := fx') B API.
Hypothesis FREE : forall fx' : YK11.FPState, free_contract (fx := fx') B API.
Hypothesis FFREE : forall fx' : YK11.FPState, fuzz_free_contract (fx := fx') B API sb_form.
Hypothesis ENC : forall fx' : YK11.FPState, preset_base64_encode_contract (fx := fx') B API sb_form.
Hypothesis DEC : forall fx' : YK11.FPState, preset_base64_decode_contract (fx := fx') B API sb_form.
Hypothesis PJS : forall fx' : YK11.FPState, pj_string_contract (fx := fx') B API sb_form.
Hypothesis PJSET : forall fx' : YK11.FPState, pj_set_contract (fx := fx') B API sb_form.
Hypothesis PJF : forall fx' : YK11.FPState, pj_free_contract (fx := fx') B API sb_form.
Hypothesis PJW : forall fx' : YK11.FPState, pj_write_contract_sb (fx := fx') B API.
Hypothesis PJP : forall fx' : YK11.FPState, pj_parse_contract (fx := fx') B API sb_form.
Variables (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model).
Hypothesis PRE : call_pre_k B MR CRT_STK L A regs mem md.
Variables (Lam : list (Z * Z)) (peak cnt : Z) (bnd : sbound).
Hypothesis LG0 : ledger B L A mem Lam peak cnt (2 ^ 64 - 1).
Hypothesis HCNT : cnt + CRT_ALLOCS < 2 ^ 63.
Hypothesis RSP : spZ regs <= 2 ^ 47.
Hypothesis RGT : strtod_c.STRTOD_GLOBALS_TOP <= spZ regs - CRT_STK.
Variable fx0 : YK11.FPState.

Local Notation CRs := (CR B API L A regs mem md Lam peak cnt bnd).
Local Notation post := (crt_post B API L A regs mem md Lam peak cnt bnd fx0).
Local Notation RFs := (RF regs).
(* A lemma of check_round_trip_stages_a.v at this section's variables. *)
Local Notation PFX f := (f B API SEG MAL FRE ERR GF AX CO BSP RTP RER RGG RGD STRLEN STRCMP BCMP PJO PJG PJGS MALLOC
  FREE FFREE ENC DEC PJS PJSET PJF PJW PJP L A regs mem md PRE Lam peak cnt bnd LG0 HCNT RSP RGT fx0) (only parsing).

Ltac retok R1 := rewrite R1; vm_compute; reflexivity.
Ltac kbr HM := first [ exact (proj1 (kb_md B API _ _ _ _ HM)) | exact (proj2 (kb_md B API _ _ _ _ HM)) ].
Ltac sv RP R' H E n :=
  lazymatch type of H with getr _ ?k = ?v =>
    assert (E : getr R' k = v) by (rewrite <- H; exact (RP n ltac:(unfold callee_saved; lia))) end.
Ltac kfin R' RF' :=
  do 3 eexists; split; [reflexivity|];
  split; [apply ((PFX RF_mk) R'); [exact RF' | reflexivity ..]|];
  repeat (split; [first [reflexivity | apply (PFX crt_spo); lia]|]); first [reflexivity | apply (PFX crt_spo); lia].

(* The frame below the saved registers is readable and writable. *)
Lemma crt_gi_stk : forall Lc Ac memc mdc, GI B API L A regs mem md Lc Ac memc mdc ->
  stk rsegs memc (spZ regs - CRT_STK) (spZ regs - 336).
Proof.
  intros Lc Ac memc mdc ((_ & _ & _ & _ & _ & _ & _ & _ & S) & _).
  pose proof (crt_sp B API L A regs mem md PRE) as (Hsp1 & Hsp2 & _). pose proof alloc_ceiling_val as Hacv.
  split; [unfold CRT_STK, ALLOC_STACK; lia|]. split; [lia|]. intros a Ha.
  assert (W : writable_at (ms_segs B) memc a) by (apply S; left; unfold CRT_STK, ALLOC_STACK in *; lia).
  rewrite SEG in W. unfold writable_at in W. split; [exact W | exact (past_nul.pn_rd memc _ W)].
Qed.

Lemma stk_normalize : forall m lo hi, ro_agree rsegs m -> stk rsegs m lo hi -> 0x55000 <= lo ->
  stk rsegs (normalize rsegs m) lo hi.
Proof.
  intros m lo hi RA (H0 & H1 & H) Hlo. split; [exact H0|]. split; [exact H1|]. intros a Ha.
  destruct (H a Ha) as [W R].
  pose proof (mem_rel_normalize rsegs m RA) as HR.
  assert (Hro : ro_addr rsegs (wa a) = false).
  { unfold ro_addr. rewrite wa_unsigned by lia.
    rewrite (HsKindB.find_segment_above rsegs 0x55000 a 1 HsKindB.rsegs_top) by lia. reflexivity. }
  split.
  - rewrite (wview_rel_rw rsegs m (normalize rsegs m) _ HR Hro). exact W.
  - rewrite <- (mrd_rel rsegs m (normalize rsegs m) _ HR). exact R.
Qed.

(* A tree in the frame, on the normalized memory. *)
Lemma node_norm : forall X P Lc Ac memc mdc Lamc pk cn Nc p t D,
  CRs X P Lc Ac memc mdc Lamc pk cn Nc -> pj_node rsegs memc (lin Lamc) p t D -> incl D X -> spZ regs - 336 <= p ->
  pj_node rsegs (normalize rsegs memc) (lin Lamc) p t D.
Proof.
  intros X P Lc Ac memc mdc Lamc pk cn Nc p t D CRc ND HI Hp.
  apply (pj_node_frame rsegs t memc (lin Lamc) (normalize rsegs memc) (lin Lamc) p D ND
    ((PFX cr_lin) X P Lc Ac memc mdc Lamc pk cn Nc D CRc HI)).
  intros w Hw. unfold normalize.
  pose proof (PFX crt_spr) as (Hs1 & Hs2 & Hs3).
  pose proof (bv_unsigned_in_range 64 w) as Rw. unfold bv_modulus in Rw. change (2 ^ Z.of_N 64) with (2 ^ 64) in Rw.
  assert (Hro : ro_addr rsegs w = false).
  { unfold ro_addr. rewrite (crt_fs_none B SEG (bv_unsigned w)); [reflexivity|].
    destruct Hw as [Hw|([a k] & Hb & Hh)].
    - left. lia.
    - right. unfold pj_holds in Hh. cbn [fst snd] in Hh.
      destruct ((PFX cr_xin) X P Lc Ac memc mdc Lamc pk cn Nc a k (bv_unsigned w) CRc (HI _ Hb) ltac:(lia))
        as (_ & _ & NI & _).
      split; [lia | exact NI]. }
  rewrite Hro. reflexivity.
Qed.

(* Trees and caller bytes across a stretch that writes only below the frame. *)
Lemma node_munch_lo : forall X P Lc Ac memc mdc Lamc pk cn Nc p t D lo m',
  CRs X P Lc Ac memc mdc Lamc pk cn Nc -> pj_node rsegs memc (lin Lamc) p t D -> incl D X -> spZ regs - 336 <= p ->
  alloc_ceiling <= lo -> munch [(lo, spZ regs - 336)] memc m' -> pj_node rsegs m' (lin Lamc) p t D.
Proof.
  intros X P Lc Ac memc mdc Lamc pk cn Nc p t D lo m' CRc ND HI Hp Hlo MU.
  apply (pj_node_munch rsegs [(lo, spZ regs - 336)] memc (lin Lamc) m' (lin Lamc) p t D ND
    ((PFX cr_lin) X P Lc Ac memc mdc Lamc pk cn Nc D CRc HI) MU).
  pose proof (PFX crt_spr) as (_ & _ & Hs3).
  intros z [Hz|([a k] & Hb & Hh)]; cbn [outside]; (split; [|exact I]).
  - lia.
  - unfold pj_holds in Hh. cbn [fst snd] in Hh.
    destruct ((PFX cr_xin) X P Lc Ac memc mdc Lamc pk cn Nc a k z CRc (HI _ Hb) ltac:(lia)) as (_ & R & _).
    lia.
Qed.

Lemma lam_munch_lo : forall X P Lc Ac memc mdc Lamc pk cn Nc a k y bs lo m',
  CRs X P Lc Ac memc mdc Lamc pk cn Nc -> In (a, k) Lam -> Mem.bytes_at rsegs memc y bs -> a <= y ->
  y + Z.of_nat (length bs) <= a + k -> alloc_ceiling <= lo -> munch [(lo, spZ regs - 336)] memc m' ->
  Mem.bytes_at rsegs m' y bs.
Proof.
  intros X P Lc Ac memc mdc Lamc pk cn Nc a k y bs lo m' CRc Hin BS H1 H2 Hlo MU.
  pose proof PRE as (HM0 & _).
  destruct (ledger_block_range B API L A mem md Lam peak cnt _ a k HM0 LG0 Hin) as (Ha1 & _).
  apply (crt_bytes_keep memc m' y bs BS). intros i Hi.
  destruct ((PFX cr_lam_x) X P Lc Ac memc mdc Lamc pk cn Nc a k i CRc Hin ltac:(lia)) as (_ & R & _).
  pose proof alloc_ceiling_val as Hacv.
  apply (mbyte_munch rsegs _ memc m' i MU); [lia|]. cbn [outside]. split; [lia | exact I].
Qed.

Section F2.
Context {fx : YK11.FPState}.
Hypothesis FK : fregs_kept fx0 fx.
Hypothesis FRM : frm_zero (@fp_csr fx).

(* c16: pj_parse(file, strlen(file), &back), pj_get_str(pj_get(&back, "state"), "bytes"), then the decode *)
Lemma st16 : forall Y Lc Ac regsc memc mdc Lamc peakc cntc Nc same sn want wn q kq b1 k1 Dd f kf tbf ms i ms2 j s
    bs b kb,
  CRs ((f, kf) :: Y) [(same, sn); (want, wn)] Lc Ac memc mdc Lamc peakc cntc Nc ->
  cntc + Z.of_nat (length (PjRoundTrip.ttrace (JObj ms))) + 1 <= cnt + CRT_ALLOCS ->
  (length (PjRoundTrip.ttrace (JObj ms)) + 1 <= Nc)%nat ->
  Forall (fun e => Z.of_nat (esize e) + 16 <= CRT_SIZE) (PjRoundTrip.ttrace (JObj ms)) ->
  Permutation Y (Dd ++ [(b1, k1); (q, kq)]) ->
  pj_node rsegs memc (lin Lamc) (spZ regs - 336 + 192) (JObj ms) Dd -> (depth (JObj ms) <= 2)%nat ->
  PjRoundTrip.pj_wf jr_strtod (JObj ms) ->
  Mem.bytes_at rsegs memc f tbf -> zb tbf = wdoc (JObj ms) true -> Z.of_nat (length tbf) < 2 ^ 22 ->
  Z.of_nat (length tbf) <= kf ->
  nth_error ms i = Some (CRT_STATE, JObj ms2) ->
  (forall j' nm u, (j' < i)%nat -> nth_error ms j' = Some (nm, u) -> nm <> CRT_STATE) ->
  nth_error ms2 j = Some (CRT_BYTES, JStr s) ->
  (forall j' nm u, (j' < j)%nat -> nth_error ms2 j' = Some (nm, u) -> nm <> CRT_BYTES) ->
  Z.of_nat (length s) <= 2 ^ 28 -> dec_size s + 16 <= CRT_SIZE ->
  b64_dec s = Some bs -> Mem.bytes_at rsegs memc b (bz bs) -> In (b, kb) Lam -> Z.of_nat (length bs) <= kb ->
  RFs regsc -> getr regsc 1 = Z_to_bv 64 0x13cb8 -> getr regsc 10 = Z_to_bv 64 f ->
  getr regsc 11 = Z_to_bv 64 (Z.of_nat (length tbf)) -> getr regsc 12 = Z_to_bv 64 (spZ regs - 336 + 24) ->
  getr regsc 19 = Z_to_bv 64 (Z.of_nat (length bs)) -> getr regsc 20 = Z_to_bv 64 b ->
  getr regsc 22 = Z_to_bv 64 f -> getr regsc 21 = Z_to_bv 64 b1 -> getr regsc 8 = Z_to_bv 64 q ->
  getr regsc 9 = Z_to_bv 64 want -> getr regsc 18 = Z_to_bv 64 same -> 0 < sn -> 0 < wn ->
  SR (ms_segs B) (mkCfg (mkst regsc (Z_to_bv 64 PJ_PARSE) memc (seg_rom (ms_segs B))) mdc) post.
Proof.
  intros Y Lc Ac regsc memc mdc Lamc peakc cntc Nc same sn want wn q kq b1 k1 Dd f kf tbf ms i ms2 j s bs b kb CRc HC HN
    TF PY ND Hdd WF TB Ezb Htl Hkf Hi Fi Hj Fj Hsl Hsz HD BB Hbin Hbk RFc R1 R10 R11 R12 R19 R20 R22 R21 R8 R9 R18 Hsn
    Hwn.
  pose proof RFc as (R2 & RG). pose proof (PFX crt_spr) as (Hs1 & Hs2 & Hs3).
  pose proof (crt_sp B API L A regs mem md PRE) as (Hsp0 & _ & Hsp16).
  pose proof alloc_ceiling_val as Hacv. pose proof HCNT as Hcnt. unfold CRT_ALLOCS in *.
  assert (Hfl : In (f, kf) Lamc)
    by exact (cr_in_lam B API L A regs mem md Lam peak cnt bnd _ _ _ _ _ _ _ _ _ _ f kf CRc (or_introl eq_refl)).
  apply (w_parse B API SEG ERR GF AX CO L A regs mem md PRE Lam peak cnt bnd RTP RER RGG RGD RSP RGT (PJP fx)
    ((f, kf) :: Y) [(same, sn); (want, wn)] Lc Ac regsc memc mdc Lamc peakc cntc Nc f tbf (spZ regs - 336 + 24)
    (JObj ms) post FRM CRc R2 (RG 4 ltac:(lia)) ltac:(retok R1) R10 R11 R12).
  { lia. }
  { lia. }
  { lia. }
  { rewrite SEG. exact TB. }
  { exact Ezb. }
  { exact WF. }
  { exists f, kf. split; [exact Hfl | lia]. }
  { exact Htl. }
  { lia. }
  { exact TF. }
  { lia. }
  intros fx' Lc' Ac' regs' memc' mdc' Lamc' peakc' cntc' D FK' FRM' RP R10' CR' HCN' CS RDC NODE.
  assert (ID : incl Dd ((f, kf) :: Y)) by (intros y Hy; right; exact ((PFX incl_perm_l) Y Dd _ PY _ Hy)).
  assert (EO : forall p, spZ regs - 336 + 80 <= p ->
     Eok regs ((f, kf) :: Y) [(same, sn); (want, wn)] (D ++ (f, kf) :: Y) [(same, sn); (want, wn)] p []
       (pj_parse_writes (spZ regs - 336 + 24))).
  { intros p Hp x [Hx|Hx]; [right; left; split; lia | left; exact Hx]. }
  assert (ND1 : pj_node rsegs memc' (lin Lamc') (spZ regs - 336 + 192) (JObj ms) Dd).
  { apply ((PFX cr_keep_node) ((f, kf) :: Y) _ Lc Ac memc mdc Lamc peakc cntc Nc (D ++ (f, kf) :: Y) _ Lc' Ac' memc'
      mdc' Lamc' peakc' cntc' _ _ _ _ _ _ Dd CRc CR' CS ND ID (fun y Hy => in_or_app _ _ _ (or_intror (ID y Hy)))).
    - lia.
    - intros x [Hx|Hx]; [right; left; split; lia | left; exact Hx].
    - intros a k _ []. }
  assert (BB1 : Mem.bytes_at rsegs memc' b (bz bs)).
  { apply ((PFX cr_keep_lam) ((f, kf) :: Y) _ Lc Ac memc mdc Lamc peakc cntc Nc (D ++ (f, kf) :: Y) _ Lc' Ac' memc'
      mdc' Lamc' peakc' cntc' _ _ _ _ (spZ regs - 336 + 192) [] b kb b (bz bs) CRc CR' CS
      (EO (spZ regs - 336 + 192) ltac:(lia)) (fun H => H) Hbin BB ltac:(lia)).
    unfold bz. rewrite length_map. lia. }
  pose proof ((PFX RF_pres) _ _ RP RFc) as RF'.
  sv RP regs' R19 S19 19. sv RP regs' R20 S20 20. sv RP regs' R22 S22 22. sv RP regs' R21 S21 21.
  sv RP regs' R8 S8 8. sv RP regs' R9 S9 9. sv RP regs' R18 S18 18.
  pose proof CR' as (GI' & _ & LG' & _). pose proof GI' as ((HM' & _) & _ & _ & _ & RA' & _).
  rewrite R1.
  eapply (kb_run B regs' (Z_to_bv 64 0x13cb8) memc' mdc'
    (fun R pc' m' => exists m0, (exists z n, RFs R /\ getr R 1 = Z_to_bv 64 0x13ce4 /\ getr R 10 = Z_to_bv 64 z /\
       getr R 11 = Z_to_bv 64 (spZ regs - 336 + 16) /\ getr R 19 = Z_to_bv 64 (Z.of_nat (length bs)) /\
       getr R 20 = Z_to_bv 64 b /\ getr R 22 = Z_to_bv 64 f /\ getr R 21 = Z_to_bv 64 b1 /\
       getr R 8 = Z_to_bv 64 q /\ getr R 9 = Z_to_bv 64 want /\ getr R 18 = Z_to_bv 64 same /\
       pc' = Z_to_bv 64 0x14e90 /\
       munch [(spZ regs - 336 - 64, spZ regs - 336)] (normalize rsegs memc') m0 /\
       wmono rsegs (normalize rsegs memc') m0 /\ pj_cstr rsegs m0 (lin Lamc') z n s /\ In (z, n) D) /\
       mem_rel rsegs m' m0 /\ ro_same rsegs memc' m'));
    [kbr HM' | kbr HM' | |].
  { rewrite SEG. unfold rmk. pose proof RF' as (P2 & _). rewrite P2, R10', S19, S20, S22, S21, S8, S9, S18.
    apply (PFX crt_evn); [exact RA'|].
    eapply Exec.evt_mono.
    - eapply (crt_r17 PJG PJGS) with (lblk := lin Lamc') (lo := spZ regs - CRT_STK) (D := D) (i := i) (j := j).
      + reflexivity.
      + rewrite MState.unsigned_lit by lia. lia.
      + rewrite MState.unsigned_lit by lia. apply stk_normalize; [exact RA' | exact (crt_gi_stk _ _ _ _ GI') |].
        unfold CRT_STK, ALLOC_STACK. lia.
      + unfold CRT_STK, ALLOC_STACK. lia.
      + rewrite MState.unsigned_lit by lia. unfold CRT_STK, ALLOC_STACK. lia.
      + rewrite MState.unsigned_lit by lia. lia.
      + rewrite MState.unsigned_lit by lia.
        exact (node_norm (D ++ (f, kf) :: Y) _ _ _ _ _ _ _ _ _ _ _ D CR' NODE (fun y Hy => in_or_app _ _ _ (or_introl Hy))
          ltac:(lia)).
      + exact Hi.
      + exact Fi.
      + exact Hj.
      + exact Fj.
      + intros a n Hl. destruct (ledger_block_range B API Lc' Ac' memc' mdc' Lamc' peakc' cntc' _ a n HM' LG' Hl)
          as (H1 & H2 & H3).
        pose proof (ledger_block_aligned B API Lc' Ac' memc' mdc' Lamc' peakc' cntc' _ a n HM' LG' Hl) as H4.
        unfold CRT_STK, ALLOC_STACK. split; [lia|]. split; [lia|]. split; lia.
      + exact ((PFX cr_lin) _ _ _ _ _ _ _ _ _ _ D CR' (fun y Hy => in_or_app _ _ _ (or_introl Hy))).
      + apply mem_inv_normalize.
    - intros ms' (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & m1 & z & n & -> & MU & WM & _ & _ &
        _ & CSZ & HZD).
      do 3 eexists. split; [reflexivity|]. exists z, n.
      split; [apply ((PFX RF_mk) regs'); [exact RF' | reflexivity ..]|].
      split; [reflexivity|]. split; [reflexivity|]. split; [apply (PFX crt_spo); lia|].
      do 8 (split; [reflexivity|]).
      rewrite MState.unsigned_lit in MU by lia.
      split; [exact MU|]. split; [exact WM|]. split; [exact CSZ | exact HZD]. }
  intros RR pc2 mem2 regs2 (m0 & (z & n & RF2 & Q1 & Q10 & Q11 & Q19 & Q20 & Q22 & Q21 & Q8 & Q9 & Q18 & -> & MU & WM &
    CSZ & HZD) & HR & ROS) HG.
  apply ((PFX RF_getr) _ _ HG) in RF2. rewrite <- HG in Q1, Q10, Q11, Q19, Q20, Q22, Q21, Q8, Q9, Q18.
  pose proof (mem_rel_normalize rsegs memc' RA') as HR0.
  pose proof (munch_rel rsegs _ memc' (normalize rsegs memc') mem2 m0 HR0 HR ROS MU) as MU2.
  pose proof (wmono_rel rsegs memc' (normalize rsegs memc') mem2 m0 HR0 HR ROS WM) as WM2.
  pose proof (ro_agree_same rsegs memc' mem2 RA' ROS) as RA2.
  pose proof ((PFX cr_munch) _ _ _ _ _ _ _ _ _ _ _ mem2 CR' MU2 WM2 RA2) as CR2.
  assert (CR3 : CRs ((f, kf) :: D ++ Y) [(same, sn); (want, wn)] Lc' Ac' mem2 mdc' Lamc' peakc' cntc'
    (S (Nc - length (PjRoundTrip.ttrace (JObj ms)) - 1))).
  { replace (S (Nc - length (PjRoundTrip.ttrace (JObj ms)) - 1)) with (Nc - length (PjRoundTrip.ttrace (JObj ms)))%nat
      by lia.
    apply ((PFX cr_perm) (D ++ (f, kf) :: Y)); [exact (Permutation_sym (Permutation_middle D Y (f, kf)))|].
    apply CR2. intros x Hx. cbn [outside] in Hx. unfold CRT_STK, ALLOC_STACK.
    destruct (Z_le_gt_dec (spZ regs - 336 - 64) x) as [H1|H1];
      [destruct (Z_lt_ge_dec x (spZ regs - 336)) as [H2|H2]|]; [lia| |]; exfalso; apply Hx; (split; [lia | exact I]). }
  pose proof (node_munch_lo _ _ _ _ _ _ _ _ _ _ _ _ _ (spZ regs - 336 - 64) mem2 CR' NODE
    (fun y Hy => in_or_app _ _ _ (or_introl Hy)) ltac:(lia) ltac:(lia) MU2) as NB2.
  pose proof (node_munch_lo _ _ _ _ _ _ _ _ _ _ _ _ _ (spZ regs - 336 - 64) mem2 CR' ND1
    (fun y Hy => in_or_app _ _ _ (or_intror (ID y Hy))) ltac:(lia) ltac:(lia) MU2) as ND2.
  pose proof (lam_munch_lo _ _ _ _ _ _ _ _ _ _ b kb b (bz bs) (spZ regs - 336 - 64) mem2 CR' Hbin BB1 ltac:(lia)
    ltac:(unfold bz; rewrite length_map; lia) ltac:(lia) MU2) as BB2.
  assert (CSZ2 : pj_cstr rsegs mem2 (lin Lamc') z n s).
  { destruct CSZ as (C1 & C2 & C3 & C4). split; [exact C1|]. split; [exact C2|]. split; [exact C3|].
    exact (proj2 (bytes_at_rel rsegs mem2 m0 z _ HR) C4). }
  exact ((PFX st17) (fk_trans _ _ _ FK FK') FRM' (D ++ Y) Y Lc' Ac' regs2 mem2 mdc' Lamc' peakc' cntc'
    (Nc - length (PjRoundTrip.ttrace (JObj ms)) - 1) same sn want wn q kq b1 k1 (JObj ms) Dd (JObj ms) D f kf z n s bs b
    kb CR3 ltac:(unfold CRT_ALLOCS; lia) (Permutation_refl _) PY NB2 Hdd ND2 Hdd CSZ2 Hsl Hsz HD BB2 Hbin Hbk RF2 Q1 Q10
    Q11 Q19 Q20 Q22 Q21 Q8 Q9 Q18 Hsn Hwn).
Qed.

End F2.

(* Trees, entry bytes and caller bytes across pj_set: its write set and freed blocks miss what the call's trees
   (D, Dw) do not hold. *)
Lemma crt_keepT : forall X P Lc Ac memc mdc Lamc pk cn Nc X' Lc' Ac' memc' mdc' Lamc' pk' cn' Nc' K o w D Dw Y,
  CRs X P Lc Ac memc mdc Lamc pk cn Nc -> CRs X' P Lc' Ac' memc' mdc' Lamc' pk' cn' Nc' ->
  cs B API (spZ regs - 336) K (pj_set_writes o w D Dw) (freed (D ++ Dw)) Lc Ac memc mdc Lc' Ac' memc' mdc' ->
  Permutation X (D ++ Dw ++ Y) -> incl Y X' ->
  spZ regs - 336 <= o -> o + 56 <= spZ regs -> spZ regs - 336 <= w -> w + 56 <= spZ regs ->
  (forall p t D', pj_node rsegs memc (lin Lamc) p t D' -> incl D' Y -> spZ regs - 336 <= p ->
     (p + 56 <= o \/ o + 56 <= p) -> (p + 56 <= w \/ w + 56 <= p) -> pj_node rsegs memc' (lin Lamc') p t D') /\
  (forall a k y bs, In (a, k) Y -> Mem.bytes_at rsegs memc y bs -> a <= y -> y + Z.of_nat (length bs) <= a + k ->
     Mem.bytes_at rsegs memc' y bs) /\
  (forall a k y bs, In (a, k) Lam -> Mem.bytes_at rsegs memc y bs -> a <= y -> y + Z.of_nat (length bs) <= a + k ->
     Mem.bytes_at rsegs memc' y bs).
Proof.
  intros X P Lc Ac memc mdc Lamc pk cn Nc X' Lc' Ac' memc' mdc' Lamc' pk' cn' Nc' K o w D Dw Y CRc CR' CS PX HY Ho1 Ho2
    Hw1 Hw2.
  assert (ND : List.NoDup ((D ++ Dw) ++ Y)).
  { rewrite <- app_assoc. exact (Permutation_NoDup PX ((PFX crt_nd) _ _ _ _ _ _ _ _ _ _ CRc)). }
  assert (HX : forall y, In y ((D ++ Dw) ++ Y) -> In y X).
  { intros y Hy. rewrite <- app_assoc in Hy. exact ((PFX perm_in) X _ y PX Hy). }
  assert (EO : forall p D', incl D' Y -> (p + 56 <= o \/ o + 56 <= p) -> (p + 56 <= w \/ w + 56 <= p) ->
    Eok regs X P X' P p D' (pj_set_writes o w D Dw)).
  { intros p D' HI Hpo Hpw x [Hx|[Hx|[(a & k & Hb & Hbx)|Hx]]].
    - right. left. split; lia.
    - right. left. split; lia.
    - right. right. left. exists a, k. split; [left; apply HX; apply in_or_app; left; exact Hb|].
      split; [|exact Hbx]. intros Hd. exact (crt_nd_app_not _ _ _ ND Hb (HI _ Hd)).
    - left. exact Hx. }
  assert (NF : forall a k, In (a, k) Y -> ~ freed (D ++ Dw) (a - 16) (k + 16)).
  { intros a k Hy Hf. unfold freed in Hf. replace (a - 16 + 16) with a in Hf by lia.
    replace (k + 16 - 16) with k in Hf by lia. exact (crt_nd_app_not _ _ _ ND Hf Hy). }
  split; [|split].
  - intros p t D' NDp HI Hp Hpo Hpw.
    apply ((PFX cr_keep_node) X P Lc Ac memc mdc Lamc pk cn Nc X' P Lc' Ac' memc' mdc' Lamc' pk' cn' Nc' K _ _ p t D'
      CRc CR' CS NDp (fun y H => HX y (in_or_app _ _ _ (or_intror (HI y H)))) (fun y H => HY y (HI y H)) Hp
      (EO p D' HI Hpo Hpw)).
    intros a k Hak. exact (NF a k (HI _ Hak)).
  - intros a k y bs Hy BS H1 H2.
    apply ((PFX cr_keep_bytes) X P Lc Ac memc mdc Lamc pk cn Nc X' P Lc' Ac' memc' mdc' Lamc' pk' cn' Nc' K _ _
      (spZ regs) a k y bs CRc CR' CS (HX _ (in_or_app _ _ _ (or_intror Hy))) (HY _ Hy));
      [| exact (NF a k Hy) | exact BS | exact H1 | exact H2].
    apply EO; [intros z [<-|[]]; exact Hy | lia | lia].
  - intros a k y bs Hin BS H1 H2.
    apply ((PFX cr_keep_lam) X P Lc Ac memc mdc Lamc pk cn Nc X' P Lc' Ac' memc' mdc' Lamc' pk' cn' Nc' K _ _
      (spZ regs) [] a k y bs CRc CR' CS); [| | exact Hin | exact BS | exact H1 | exact H2].
    + apply EO; [intros z [] | lia | lia].
    + intros Hf. unfold freed in Hf. replace (a - 16 + 16) with a in Hf by lia.
      replace (k + 16 - 16) with k in Hf by lia.
      destruct (crt_lam_blk B L A mem Lam peak cnt (2 ^ 64 - 1) a k LG0 Hin) as (_ & Hk0 & _).
      destruct ((PFX cr_lam_x) X P Lc Ac memc mdc Lamc pk cn Nc a k (a - 16) CRc Hin ltac:(lia))
        as (_ & _ & _ & HN & _).
      exact (HN a k (HX _ (in_or_app _ _ _ (or_introl Hf))) ltac:(lia)).
Qed.

(* The same across pj_string, which writes only its node and the allocator's statics. *)
Lemma crt_keepS : forall X P Lc Ac memc mdc Lamc pk cn Nc X' Lc' Ac' memc' mdc' Lamc' pk' cn' Nc' K v,
  CRs X P Lc Ac memc mdc Lamc pk cn Nc -> CRs X' P Lc' Ac' memc' mdc' Lamc' pk' cn' Nc' ->
  cs B API (spZ regs - 336) K (pj_string_writes v) (fun _ _ => False) Lc Ac memc mdc Lc' Ac' memc' mdc' ->
  incl X X' -> spZ regs - 336 <= v -> v + 56 <= spZ regs ->
  (forall p t D', pj_node rsegs memc (lin Lamc) p t D' -> incl D' X -> spZ regs - 336 <= p ->
     (p + 56 <= v \/ v + 56 <= p) -> pj_node rsegs memc' (lin Lamc') p t D') /\
  (forall a k y bs, In (a, k) X -> Mem.bytes_at rsegs memc y bs -> a <= y -> y + Z.of_nat (length bs) <= a + k ->
     Mem.bytes_at rsegs memc' y bs) /\
  (forall a k y bs, In (a, k) Lam -> Mem.bytes_at rsegs memc y bs -> a <= y -> y + Z.of_nat (length bs) <= a + k ->
     Mem.bytes_at rsegs memc' y bs).
Proof.
  intros X P Lc Ac memc mdc Lamc pk cn Nc X' Lc' Ac' memc' mdc' Lamc' pk' cn' Nc' K v CRc CR' CS HXX Hv1 Hv2.
  assert (EO : forall p D', (p + 56 <= v \/ v + 56 <= p) -> Eok regs X P X' P p D' (pj_string_writes v)).
  { intros p D' Hp x [Hx|Hx]; [right; left; split; lia | left; exact Hx]. }
  split; [|split].
  - intros p t D' NDp HI Hp Hpv.
    apply ((PFX cr_keep_node) X P Lc Ac memc mdc Lamc pk cn Nc X' P Lc' Ac' memc' mdc' Lamc' pk' cn' Nc' K _ _ p t D'
      CRc CR' CS NDp HI (fun y H => HXX y (HI y H)) Hp (EO p D' Hpv)).
    intros a k _ [].
  - intros a k y bs Hx BS H1 H2.
    exact ((PFX cr_keep_bytes) X P Lc Ac memc mdc Lamc pk cn Nc X' P Lc' Ac' memc' mdc' Lamc' pk' cn' Nc' K _ _
      (spZ regs) a k y bs CRc CR' CS Hx (HXX _ Hx) (EO (spZ regs) [(a, k)] ltac:(lia)) (fun H => H) BS H1 H2).
  - intros a k y bs Hin BS H1 H2.
    exact ((PFX cr_keep_lam) X P Lc Ac memc mdc Lamc pk cn Nc X' P Lc' Ac' memc' mdc' Lamc' pk' cn' Nc' K _ _
      (spZ regs) [] a k y bs CRc CR' CS (EO (spZ regs) [] ltac:(lia)) (fun H => H) Hin BS H1 H2).
Qed.

Section F3.
Context {fx : YK11.FPState}.
Hypothesis FK : fregs_kept fx0 fx.
Hypothesis FRM : frm_zero (@fp_csr fx).

(* c15: pj_write(&doc, 1), strlen of the text, then pj_parse *)
Lemma st15 : forall X Lc Ac regsc memc mdc Lamc peakc cntc Nc same sn want wn q kq b1 k1 Dd bs b kb,
  CRs X [(same, sn); (want, wn)] Lc Ac memc mdc Lamc peakc cntc Nc -> (18 <= Nc)%nat ->
  cntc + 27 <= cnt + CRT_ALLOCS -> Permutation X (Dd ++ [(b1, k1); (q, kq)]) ->
  pj_node rsegs memc (lin Lamc) (spZ regs - 336 + 192) (JObj (crt_doc (b64_enc bs))) Dd ->
  bytes_ok bs -> Z.of_nat (length bs) <= 9 * 2 ^ 18 + 2 ->
  Mem.bytes_at rsegs memc b (bz bs) -> In (b, kb) Lam -> Z.of_nat (length bs) <= kb ->
  RFs regsc -> getr regsc 1 = Z_to_bv 64 0x13c9c -> getr regsc 10 = Z_to_bv 64 (spZ regs - 336 + 192) ->
  getr regsc 11 = Z_to_bv 64 1 ->
  getr regsc 19 = Z_to_bv 64 (Z.of_nat (length bs)) -> getr regsc 20 = Z_to_bv 64 b ->
  getr regsc 21 = Z_to_bv 64 b1 -> getr regsc 8 = Z_to_bv 64 q -> getr regsc 9 = Z_to_bv 64 want ->
  getr regsc 18 = Z_to_bv 64 same -> 0 < sn -> 0 < wn ->
  SR (ms_segs B) (mkCfg (mkst regsc (Z_to_bv 64 PJ_WRITE_PC) memc (seg_rom (ms_segs B))) mdc) post.
Proof.
  intros X Lc Ac regsc memc mdc Lamc peakc cntc Nc same sn want wn q kq b1 k1 Dd bs b kb CRc HN HC PX ND HBO Hbl BB
    Hbin Hbk RFc R1 R10 R11 R19 R20 R21 R8 R9 R18 Hsn Hwn.
  pose proof RFc as (R2 & RG). pose proof (PFX crt_spr) as (Hs1 & Hs2 & Hs3).
  pose proof alloc_ceiling_val as Hacv. pose proof HCNT as Hcnt. unfold CRT_ALLOCS in *.
  destruct (crt_doc_ok bs HBO Hbl) as (WF & Hdd & TL & TF & WL & WNZ & WBO & Hsl & Hsz).
  pose proof (WriterSpecFacts.b64_dec_enc bs HBO) as HD.
  set (es := b64_enc bs) in *.
  set (wd := wdoc (JObj (crt_doc es)) true) in *.
  destruct Nc as [|[|Nc]]; [lia | lia |].
  apply (w_write B API SEG ERR GF AX CO L A regs mem md PRE Lam peak cnt bnd RGG RGD RSP (PJW fx) X
    [(same, sn); (want, wn)] Lc Ac regsc memc mdc Lamc peakc cntc Nc (spZ regs - 336 + 192) (JObj (crt_doc es)) Dd
    [(b1, k1); (q, kq)] post FRM CRc R2 (RG 4 ltac:(lia)) ltac:(retok R1) R10 R11 ltac:(lia) ltac:(lia) ND PX Hdd
    (Z.lt_le_incl _ _ WL) ltac:(lia)).
  intros fx' Lc' Ac' regs' memc' mdc' f c peakc' cntc' FK' FRM' RP R10' CR' HCN' Hc1 Hc2 Hc3 CS NODE ZB.
  change (wdoc (JObj (crt_doc es)) true) with wd in Hc1, ZB.
  pose proof ((PFX RF_pres) _ _ RP RFc) as RF'.
  sv RP regs' R19 S19 19. sv RP regs' R20 S20 20. sv RP regs' R21 S21 21.
  sv RP regs' R8 S8 8. sv RP regs' R9 S9 9. sv RP regs' R18 S18 18.
  pose proof CR' as (GI' & _). pose proof GI' as ((HM' & _) & _ & _ & _ & RA' & _).
  destruct ((PFX cr_x_lo) _ _ _ _ _ _ _ _ _ _ f c CR' (or_introl eq_refl)) as (Hf1 & Hf2 & Hf3).
  assert (TB0 : Mem.bytes_at rsegs memc' f (map (Z_to_bv 8) (wd ++ [0]))).
  { apply (proj1 (put.zbytes_iff B SEG memc' f (wd ++ [0]) ltac:(lia) ltac:(rewrite length_app; cbn [length]; lia))).
    exact ZB. }
  destruct ((PFX crt_slack) _ _ _ _ _ _ _ _ _ _ f c wd CR' (or_introl eq_refl) ltac:(lia) TB0) as (slack & TB & SLL).
  pose proof (crt_map_nz wd WNZ WBO) as NZ.
  assert (BB1 : Mem.bytes_at rsegs memc' b (bz bs)).
  { apply ((PFX cr_keep_lam) X _ Lc Ac memc mdc Lamc peakc cntc _ ((f, c) :: X) _ Lc' Ac' memc' mdc' ((f, c) :: Lamc)
      peakc' cntc' Nc _ _ _ (spZ regs - 336 + 192) [] b kb b (bz bs) CRc CR' CS).
    - intros x Hx. left. exact Hx.
    - exact (fun H => H).
    - exact Hbin.
    - exact BB.
    - lia.
    - unfold bz. rewrite length_map. lia. }
  rewrite R1.
  eapply (kb_run B regs' (Z_to_bv 64 0x13c9c) memc' mdc'
    (fun R pc' m' => exists m0, (RFs R /\ getr R 1 = Z_to_bv 64 0x13cb8 /\ getr R 10 = Z_to_bv 64 f /\
       getr R 11 = Z_to_bv 64 (Z.of_nat (length (map (Z_to_bv 8) wd))) /\
       getr R 12 = Z_to_bv 64 (spZ regs - 336 + 24) /\ getr R 19 = Z_to_bv 64 (Z.of_nat (length bs)) /\
       getr R 20 = Z_to_bv 64 b /\ getr R 22 = Z_to_bv 64 f /\ getr R 21 = Z_to_bv 64 b1 /\
       getr R 8 = Z_to_bv 64 q /\ getr R 9 = Z_to_bv 64 want /\ getr R 18 = Z_to_bv 64 same /\
       pc' = Z_to_bv 64 0x1428c /\ munch [] (normalize rsegs memc') m0) /\
       mem_rel rsegs m' m0 /\ ro_same rsegs memc' m'));
    [kbr HM' | kbr HM' | |].
  { rewrite SEG. unfold rmk. pose proof RF' as (P2 & _). rewrite P2, R10', S19, S20, S21, S8, S9, S18.
    apply (PFX crt_evn); [exact RA'|].
    eapply Exec.evt_mono.
    - eapply (crt_r16 STRLEN) with (doc := map (Z_to_bv 8) wd) (slack := slack).
      + reflexivity.
      + lia.
      + rewrite MState.unsigned_lit by lia. lia.
      + apply bytes_at_normalize; [exact RA'|]. rewrite map_app, <- app_assoc in TB. exact TB.
      + exact NZ.
      + rewrite length_map, SLL. lia.
      + apply mem_inv_normalize.
    - intros ms' (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & m1 & -> & MU & _ & _).
      do 3 eexists. split; [reflexivity|].
      split; [apply ((PFX RF_mk) regs'); [exact RF' | reflexivity ..]|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [apply (PFX crt_spo); lia|].
      do 8 (split; [reflexivity|]). exact MU. }
  intros RR pc2 mem2 regs2 (m0 & (RF2 & Q1 & Q10 & Q11 & Q12 & Q19 & Q20 & Q22 & Q21 & Q8 & Q9 & Q18 & -> & MU) & HR &
    ROS) HG.
  apply ((PFX RF_getr) _ _ HG) in RF2. rewrite <- HG in Q1, Q10, Q11, Q12, Q19, Q20, Q22, Q21, Q8, Q9, Q18.
  assert (EQ : forall x, mem2 x = memc' x).
  { apply (mem_unchanged_rel rsegs memc' (normalize rsegs memc') mem2 m0 (mem_rel_normalize rsegs memc' RA') HR ROS).
    intros x. apply MU. exact I. }
  pose proof ((PFX cr_eqm) _ _ _ _ _ _ _ _ _ _ mem2 CR' EQ) as CR2.
  assert (ID : incl Dd ((f, c) :: X)) by (intros y Hy; right; exact ((PFX incl_perm_l) X Dd _ PX _ Hy)).
  pose proof ((PFX node_eqm) _ mem2 _ _ _ _ NODE ((PFX cr_lin) _ _ _ _ _ _ _ _ _ _ Dd CR' ID) EQ) as ND2.
  assert (TB2 : Mem.bytes_at rsegs mem2 f (map (Z_to_bv 8) wd)).
  { apply (pj_bytes_eq rsegs memc' mem2 f _); [|intros x _; exact (EQ x)].
    rewrite map_app in TB0. apply Mem.bytes_at_app in TB0. destruct TB0 as [TBa _]. exact TBa. }
  pose proof (pj_bytes_eq rsegs memc' mem2 b _ BB1 (fun x _ => EQ x)) as BB2.
  exact (st16 (fk_trans _ _ _ FK FK') FRM' X Lc' Ac' regs2 mem2 mdc' ((f, c) :: Lamc) peakc' cntc' Nc same sn want wn
    q kq b1 k1 Dd f c (map (Z_to_bv 8) wd) (crt_doc es) 2 (crt_st es) 2 es bs b kb CR2
    ltac:(rewrite TL; unfold CRT_ALLOCS; lia) ltac:(rewrite TL; lia) TF PX ND2 Hdd WF TB2 (crt_zb_map wd WBO)
    ltac:(rewrite length_map; lia) ltac:(rewrite length_map; lia) eq_refl
    ltac:(intros j' nm u Hj E; destruct j' as [|[|j']]; [| |lia]; cbn in E; injection E as <- _;
      unfold CRT_FORMAT, CRT_CARRIES, CRT_STATE; discriminate)
    eq_refl
    ltac:(intros j' nm u Hj E; destruct j' as [|[|j']]; [| |lia]; cbn in E; injection E as <- _;
      unfold K_ENCODING, K_CONTEXT, CRT_BYTES; discriminate)
    Hsl Hsz HD BB2 Hbin Hbk RF2 Q1 Q10 Q11 Q12 Q19 Q20 Q22 Q21 Q8 Q9 Q18 Hsn Hwn).
Qed.

(* c14: pj_set(&doc, "state", &st), then pj_write *)
Lemma st14 : forall X Lc Ac regsc memc mdc Lamc peakc cntc Nc same sn want wn q kq b1 k1 Dd Ds bs b kb,
  CRs X [(same, sn); (want, wn)] Lc Ac memc mdc Lamc peakc cntc Nc -> (21 <= Nc)%nat ->
  cntc + 30 <= cnt + CRT_ALLOCS -> Permutation X (Dd ++ Ds ++ [(b1, k1); (q, kq)]) ->
  pj_node rsegs memc (lin Lamc) (spZ regs - 336 + 192) (JObj crt_doc8) Dd ->
  pj_node rsegs memc (lin Lamc) (spZ regs - 336 + 136) (JObj (crt_st (b64_enc bs))) Ds ->
  bytes_ok bs -> Z.of_nat (length bs) <= 9 * 2 ^ 18 + 2 ->
  Mem.bytes_at rsegs memc b (bz bs) -> In (b, kb) Lam -> Z.of_nat (length bs) <= kb ->
  RFs regsc -> getr regsc 1 = Z_to_bv 64 0x13c8c -> getr regsc 10 = Z_to_bv 64 (spZ regs - 336 + 192) ->
  getr regsc 11 = Z_to_bv 64 0x102f8 -> getr regsc 12 = Z_to_bv 64 (spZ regs - 336 + 136) ->
  getr regsc 19 = Z_to_bv 64 (Z.of_nat (length bs)) -> getr regsc 20 = Z_to_bv 64 b ->
  getr regsc 21 = Z_to_bv 64 b1 -> getr regsc 8 = Z_to_bv 64 q -> getr regsc 9 = Z_to_bv 64 want ->
  getr regsc 18 = Z_to_bv 64 same -> 0 < sn -> 0 < wn ->
  SR (ms_segs B) (mkCfg (mkst regsc (Z_to_bv 64 PJ_SET) memc (seg_rom (ms_segs B))) mdc) post.
Proof.
  intros X Lc Ac regsc memc mdc Lamc peakc cntc Nc same sn want wn q kq b1 k1 Dd Ds bs b kb CRc HN HC PX NDd NDs HBO
    Hbl BB Hbin Hbk RFc R1 R10 R11 R12 R19 R20 R21 R8 R9 R18 Hsn Hwn.
  pose proof RFc as (R2 & RG). pose proof (PFX crt_spr) as (Hs1 & Hs2 & Hs3).
  pose proof alloc_ceiling_val as Hacv. pose proof HCNT as Hcnt. unfold CRT_ALLOCS in *.
  pose proof CRc as ((_ & _ & _ & _ & RAc & _) & _).
  crt_keyt RAc 0x102f8 CRT_STATE.
  destruct Nc as [|[|[|Nc]]]; [lia | lia | lia |].
  apply (w_set B API SEG ERR GF AX CO L A regs mem md PRE Lam peak cnt bnd RTP RER RGG RGD RSP RGT (PJSET fx) X
    [(same, sn); (want, wn)] Lc Ac regsc memc mdc Lamc peakc cntc Nc (spZ regs - 336 + 192) (spZ regs - 336 + 136)
    0x102f8 crt_doc8 (JObj (crt_st (b64_enc bs))) Dd Ds [(b1, k1); (q, kq)] (map (Z_to_bv 8) CRT_STATE)
    (crt_slk 0x102f8 CRT_STATE) post FRM CRc R2 (RG 4 ltac:(lia)) ltac:(retok R1) R10 R11 R12 ltac:(lia) ltac:(lia)
    ltac:(lia) ltac:(lia) ltac:(lia) NDd NDs PX ltac:(crt_dep) ltac:(crt_dep) ltac:(crt_dep)
    ltac:(rewrite crt_zb_map by crt_lits; crt_notin) ltac:(rewrite SEG; exact KB)
    (crt_map_nz CRT_STATE ltac:(crt_lits) ltac:(crt_lits)) KS KRO ltac:(crt_vm) ltac:(lia)).
  intros Lc' Ac' regs' memc' mdc' Lamc' peakc' cntc' Do RP R10' CR' HCN' CS RDC NODE ZW.
  rewrite crt_zb_map in NODE by crt_lits. rewrite crt_psm in NODE by crt_notin.
  destruct (crt_keepT X _ Lc Ac memc mdc Lamc peakc cntc _ (Do ++ [(b1, k1); (q, kq)]) Lc' Ac' memc' mdc' Lamc'
    peakc' cntc' Nc _ (spZ regs - 336 + 192) (spZ regs - 336 + 136) Dd Ds [(b1, k1); (q, kq)] CRc CR' CS PX
    (fun y Hy => in_or_app _ _ _ (or_intror Hy)) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (_ & _ & KL).
  pose proof (KL b kb b (bz bs) Hbin BB ltac:(lia) ltac:(unfold bz; rewrite length_map; lia)) as BB1.
  pose proof ((PFX RF_pres) _ _ RP RFc) as RF'.
  sv RP regs' R19 S19 19. sv RP regs' R20 S20 20. sv RP regs' R21 S21 21.
  sv RP regs' R8 S8 8. sv RP regs' R9 S9 9. sv RP regs' R18 S18 18.
  pose proof CR' as ((MID' & _) & _). pose proof MID' as (HM' & _).
  rewrite R1.
  eapply (kb_run B regs' (Z_to_bv 64 0x13c8c) memc' mdc'
    (fun R pc' m' => RFs R /\ getr R 1 = Z_to_bv 64 0x13c9c /\ getr R 10 = Z_to_bv 64 (spZ regs - 336 + 192) /\
       getr R 11 = Z_to_bv 64 1 /\ getr R 19 = Z_to_bv 64 (Z.of_nat (length bs)) /\ getr R 20 = Z_to_bv 64 b /\
       getr R 21 = Z_to_bv 64 b1 /\ getr R 8 = Z_to_bv 64 q /\ getr R 9 = Z_to_bv 64 want /\
       getr R 18 = Z_to_bv 64 same /\ pc' = Z_to_bv 64 0x14928 /\ m' = memc'));
    [kbr HM' | kbr HM' | |].
  { rewrite SEG. unfold rmk. pose proof RF' as (P2 & _). rewrite P2, R10', S19, S20, S21, S8, S9, S18.
    eapply Exec.evt_mono; [apply crt_r15; [reflexivity | rewrite MState.unsigned_lit by lia; lia]|].
    intros ms' ->. kfin regs' RF'. }
  intros RR pc2 mem2 regs2 (RF2 & Q1 & Q10 & Q11 & Q19 & Q20 & Q21 & Q8 & Q9 & Q18 & -> & ->) HG.
  apply ((PFX RF_getr) _ _ HG) in RF2. rewrite <- HG in Q1, Q10, Q11, Q19, Q20, Q21, Q8, Q9, Q18.
  exact (st15 (Do ++ [(b1, k1); (q, kq)]) Lc' Ac' regs2 memc' mdc' Lamc' peakc' cntc' Nc same sn want wn q kq b1 k1
    Do bs b kb CR' ltac:(lia) ltac:(unfold CRT_ALLOCS; lia) (Permutation_refl _) NODE HBO Hbl BB1 Hbin Hbk RF2 Q1 Q10
    Q11 Q19 Q20 Q21 Q8 Q9 Q18 Hsn Hwn).
Qed.

(* c13: pj_set(&st, "bytes", &v), then pj_set(&doc, "state", &st) *)
Lemma st13 : forall X Lc Ac regsc memc mdc Lamc peakc cntc Nc same sn want wn q kq b1 k1 Dd Ds Dv bs b kb,
  CRs X [(same, sn); (want, wn)] Lc Ac memc mdc Lamc peakc cntc Nc -> (24 <= Nc)%nat ->
  cntc + 33 <= cnt + CRT_ALLOCS -> Permutation X (Ds ++ Dv ++ Dd ++ [(b1, k1); (q, kq)]) ->
  pj_node rsegs memc (lin Lamc) (spZ regs - 336 + 192) (JObj crt_doc8) Dd ->
  pj_node rsegs memc (lin Lamc) (spZ regs - 336 + 136) (JObj crt_s2) Ds ->
  pj_node rsegs memc (lin Lamc) (spZ regs - 336 + 80) (JStr (b64_enc bs)) Dv ->
  bytes_ok bs -> Z.of_nat (length bs) <= 9 * 2 ^ 18 + 2 ->
  Mem.bytes_at rsegs memc b (bz bs) -> In (b, kb) Lam -> Z.of_nat (length bs) <= kb ->
  RFs regsc -> getr regsc 1 = Z_to_bv 64 0x13c74 -> getr regsc 10 = Z_to_bv 64 (spZ regs - 336 + 136) ->
  getr regsc 11 = Z_to_bv 64 0x103fc -> getr regsc 12 = Z_to_bv 64 (spZ regs - 336 + 80) ->
  getr regsc 19 = Z_to_bv 64 (Z.of_nat (length bs)) -> getr regsc 20 = Z_to_bv 64 b ->
  getr regsc 21 = Z_to_bv 64 b1 -> getr regsc 8 = Z_to_bv 64 q -> getr regsc 9 = Z_to_bv 64 want ->
  getr regsc 18 = Z_to_bv 64 same -> 0 < sn -> 0 < wn ->
  SR (ms_segs B) (mkCfg (mkst regsc (Z_to_bv 64 PJ_SET) memc (seg_rom (ms_segs B))) mdc) post.
Proof.
  intros X Lc Ac regsc memc mdc Lamc peakc cntc Nc same sn want wn q kq b1 k1 Dd Ds Dv bs b kb CRc HN HC PX NDd NDs
    NDv HBO Hbl BB Hbin Hbk RFc R1 R10 R11 R12 R19 R20 R21 R8 R9 R18 Hsn Hwn.
  pose proof RFc as (R2 & RG). pose proof (PFX crt_spr) as (Hs1 & Hs2 & Hs3).
  pose proof alloc_ceiling_val as Hacv. pose proof HCNT as Hcnt. unfold CRT_ALLOCS in *.
  pose proof CRc as ((_ & _ & _ & _ & RAc & _) & _).
  crt_keyt RAc 0x103fc CRT_BYTES.
  destruct Nc as [|[|[|Nc]]]; [lia | lia | lia |].
  apply (w_set B API SEG ERR GF AX CO L A regs mem md PRE Lam peak cnt bnd RTP RER RGG RGD RSP RGT (PJSET fx) X
    [(same, sn); (want, wn)] Lc Ac regsc memc mdc Lamc peakc cntc Nc (spZ regs - 336 + 136) (spZ regs - 336 + 80)
    0x103fc crt_s2 (JStr (b64_enc bs)) Ds Dv (Dd ++ [(b1, k1); (q, kq)]) (map (Z_to_bv 8) CRT_BYTES)
    (crt_slk 0x103fc CRT_BYTES) post FRM CRc R2 (RG 4 ltac:(lia)) ltac:(retok R1) R10 R11 R12 ltac:(lia) ltac:(lia)
    ltac:(lia) ltac:(lia) ltac:(lia) NDs NDv PX ltac:(crt_dep) ltac:(crt_dep) ltac:(crt_dep)
    ltac:(rewrite crt_zb_map by crt_lits; crt_notin) ltac:(rewrite SEG; exact KB)
    (crt_map_nz CRT_BYTES ltac:(crt_lits) ltac:(crt_lits)) KS KRO ltac:(crt_vm) ltac:(lia)).
  intros Lc' Ac' regs' memc' mdc' Lamc' peakc' cntc' Do RP R10' CR' HCN' CS RDC NODE ZW.
  rewrite crt_zb_map in NODE by crt_lits. rewrite crt_psm in NODE by crt_notin.
  destruct (crt_keepT X _ Lc Ac memc mdc Lamc peakc cntc _ (Do ++ Dd ++ [(b1, k1); (q, kq)]) Lc' Ac' memc' mdc'
    Lamc' peakc' cntc' Nc _ (spZ regs - 336 + 136) (spZ regs - 336 + 80) Ds Dv (Dd ++ [(b1, k1); (q, kq)]) CRc CR'
    CS PX (fun y Hy => in_or_app _ _ _ (or_intror Hy)) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (KN & _ & KL).
  pose proof (KN _ _ Dd NDd (fun y Hy => in_or_app _ _ _ (or_introl Hy)) ltac:(lia) ltac:(lia) ltac:(lia)) as NDd1.
  pose proof (KL b kb b (bz bs) Hbin BB ltac:(lia) ltac:(unfold bz; rewrite length_map; lia)) as BB1.
  pose proof ((PFX RF_pres) _ _ RP RFc) as RF'.
  sv RP regs' R19 S19 19. sv RP regs' R20 S20 20. sv RP regs' R21 S21 21.
  sv RP regs' R8 S8 8. sv RP regs' R9 S9 9. sv RP regs' R18 S18 18.
  pose proof CR' as ((MID' & _) & _). pose proof MID' as (HM' & _).
  rewrite R1.
  eapply (kb_run B regs' (Z_to_bv 64 0x13c74) memc' mdc'
    (fun R pc' m' => RFs R /\ getr R 1 = Z_to_bv 64 0x13c8c /\ getr R 10 = Z_to_bv 64 (spZ regs - 336 + 192) /\
       getr R 11 = Z_to_bv 64 0x102f8 /\ getr R 12 = Z_to_bv 64 (spZ regs - 336 + 136) /\
       getr R 19 = Z_to_bv 64 (Z.of_nat (length bs)) /\ getr R 20 = Z_to_bv 64 b /\
       getr R 21 = Z_to_bv 64 b1 /\ getr R 8 = Z_to_bv 64 q /\ getr R 9 = Z_to_bv 64 want /\
       getr R 18 = Z_to_bv 64 same /\ pc' = Z_to_bv 64 0x14718 /\ m' = memc'));
    [kbr HM' | kbr HM' | |].
  { rewrite SEG. unfold rmk. pose proof RF' as (P2 & _). rewrite P2, R10', S19, S20, S21, S8, S9, S18.
    eapply Exec.evt_mono; [apply crt_r14; [reflexivity | rewrite MState.unsigned_lit by lia; lia]|].
    intros ms' ->. kfin regs' RF'. }
  intros RR pc2 mem2 regs2 (RF2 & Q1 & Q10 & Q11 & Q12 & Q19 & Q20 & Q21 & Q8 & Q9 & Q18 & -> & ->) HG.
  apply ((PFX RF_getr) _ _ HG) in RF2. rewrite <- HG in Q1, Q10, Q11, Q12, Q19, Q20, Q21, Q8, Q9, Q18.
  exact (st14 (Do ++ Dd ++ [(b1, k1); (q, kq)]) Lc' Ac' regs2 memc' mdc' Lamc' peakc' cntc' Nc same sn want wn q kq
    b1 k1 Dd Do bs b kb CR' ltac:(lia) ltac:(unfold CRT_ALLOCS; lia) (perm_swap3 Do Dd _) NDd1 NODE HBO Hbl BB1 Hbin
    Hbk RF2 Q1 Q10 Q11 Q12 Q19 Q20 Q21 Q8 Q9 Q18 Hsn Hwn).
Qed.

(* c12: pj_string(&v, text), then pj_set(&st, "bytes", &v) *)
Lemma st12 : forall X Lc Ac regsc memc mdc Lamc peakc cntc Nc same sn want wn q kq b1 k1 Dd Ds bs b kb,
  CRs X [(same, sn); (want, wn)] Lc Ac memc mdc Lamc peakc cntc Nc -> (25 <= Nc)%nat ->
  cntc + 34 <= cnt + CRT_ALLOCS -> Permutation X (Ds ++ Dd ++ [(b1, k1); (q, kq)]) ->
  pj_node rsegs memc (lin Lamc) (spZ regs - 336 + 192) (JObj crt_doc8) Dd ->
  pj_node rsegs memc (lin Lamc) (spZ regs - 336 + 136) (JObj crt_s2) Ds ->
  Mem.bytes_at rsegs memc q (map (Z_to_bv 8) (b64_enc bs ++ [0])) -> Z.of_nat (length (b64_enc bs)) + 1 <= kq ->
  bytes_ok bs -> Z.of_nat (length bs) <= 9 * 2 ^ 18 + 2 ->
  Mem.bytes_at rsegs memc b (bz bs) -> In (b, kb) Lam -> Z.of_nat (length bs) <= kb ->
  RFs regsc -> getr regsc 1 = Z_to_bv 64 0x13c5c -> getr regsc 10 = Z_to_bv 64 (spZ regs - 336 + 80) ->
  getr regsc 11 = Z_to_bv 64 q ->
  getr regsc 19 = Z_to_bv 64 (Z.of_nat (length bs)) -> getr regsc 20 = Z_to_bv 64 b ->
  getr regsc 21 = Z_to_bv 64 b1 -> getr regsc 8 = Z_to_bv 64 q -> getr regsc 9 = Z_to_bv 64 want ->
  getr regsc 18 = Z_to_bv 64 same -> 0 < sn -> 0 < wn ->
  SR (ms_segs B) (mkCfg (mkst regsc (Z_to_bv 64 PJ_STRING) memc (seg_rom (ms_segs B))) mdc) post.
Proof.
  intros X Lc Ac regsc memc mdc Lamc peakc cntc Nc same sn want wn q kq b1 k1 Dd Ds bs b kb CRc HN HC PX NDd NDs TQ Hqk
    HBO Hbl BB Hbin Hbk RFc R1 R10 R11 R19 R20 R21 R8 R9 R18 Hsn Hwn.
  pose proof RFc as (R2 & RG). pose proof (PFX crt_spr) as (Hs1 & Hs2 & Hs3).
  pose proof (crt_sp B API L A regs mem md PRE) as (_ & _ & Hsp16).
  pose proof alloc_ceiling_val as Hacv. pose proof HCNT as Hcnt. unfold CRT_ALLOCS in *.
  assert (HKs : PJ_STRING_K = 8288) by reflexivity.
  pose proof (WriterSpecFacts.b64_enc_ok bs HBO) as EOK. pose proof (WriterSpecFacts.b64_enc_no_zero bs HBO) as ENZ.
  pose proof (crt_es_len bs Hbl) as Hes.
  set (es := b64_enc bs) in *.
  assert (HqX : In (q, kq) X).
  { apply ((PFX perm_in) X _ _ PX). apply in_or_app. right. apply in_or_app. right. right. left. reflexivity. }
  pose proof (cr_in_lam B API L A regs mem md Lam peak cnt bnd X _ Lc Ac memc mdc Lamc peakc cntc Nc q kq CRc HqX)
    as HqL.
  destruct ((PFX cr_x_lo) _ _ _ _ _ _ _ _ _ _ q kq CRc HqX) as (Hq1 & Hq2 & Hq3).
  destruct ((PFX crt_slack) _ _ _ _ _ _ _ _ _ _ q kq es CRc HqL Hqk TQ) as (slack & TQ' & SLL).
  rewrite map_app, <- app_assoc in TQ'.
  destruct Nc as [|Nc]; [lia|].
  apply (w_string B API SEG ERR GF AX CO L A regs mem md PRE Lam peak cnt bnd RTP RER RGG RGD RSP RGT (PJS fx) X
    [(same, sn); (want, wn)] Lc Ac regsc memc mdc Lamc peakc cntc Nc (spZ regs - 336 + 80) q (map (Z_to_bv 8) es)
    slack post FRM CRc R2 (RG 4 ltac:(lia)) ltac:(retok R1) R10 R11 ltac:(lia) ltac:(lia)
    ltac:(Z.div_mod_to_equations; lia) ltac:(lia) ltac:(rewrite SEG; exact TQ') (crt_map_nz es ENZ EOK)
    ltac:(rewrite length_map, SLL; lia)
    ltac:(unfold cstr_ok; right; exists q, kq; split; [exact HqL | rewrite length_map; lia])
    ltac:(cbn [Frame.disjoint_from]; rewrite length_map; split; [lia | exact I])
    ltac:(cbn [Frame.disjoint_from]; rewrite length_map; split; [lia | exact I])
    ltac:(rewrite length_map; unfold CRT_SIZE; lia) ltac:(lia)).
  intros Lc' Ac' regs' memc' mdc' a RP R10' CR' CS RDC NODE.
  rewrite (crt_zb_map es EOK) in NODE.
  set (n := Z.of_nat (length (map (Z_to_bv 8) es)) + 1) in *.
  destruct (crt_keepS X _ Lc Ac memc mdc Lamc peakc cntc _ _ Lc' Ac' memc' mdc' _ _ _ Nc _ (spZ regs - 336 + 80) CRc
    CR' CS (fun y Hy => or_intror Hy) ltac:(lia) ltac:(lia)) as (KN & _ & KL).
  assert (IDd : incl Dd X).
  { intros y Hy. apply ((PFX perm_in) X _ _ PX). apply in_or_app. right. apply in_or_app. left. exact Hy. }
  assert (IDs : incl Ds X) by (intros y Hy; apply ((PFX perm_in) X _ _ PX); apply in_or_app; left; exact Hy).
  pose proof (KN _ _ Dd NDd IDd ltac:(lia) ltac:(lia)) as NDd1.
  pose proof (KN _ _ Ds NDs IDs ltac:(lia) ltac:(lia)) as NDs1.
  pose proof (KL b kb b (bz bs) Hbin BB ltac:(lia) ltac:(unfold bz; rewrite length_map; lia)) as BB1.
  pose proof ((PFX RF_pres) _ _ RP RFc) as RF'.
  sv RP regs' R19 S19 19. sv RP regs' R20 S20 20. sv RP regs' R21 S21 21.
  sv RP regs' R8 S8 8. sv RP regs' R9 S9 9. sv RP regs' R18 S18 18.
  pose proof CR' as ((MID' & _) & _). pose proof MID' as (HM' & _).
  rewrite R1.
  eapply (kb_run B regs' (Z_to_bv 64 0x13c5c) memc' mdc'
    (fun R pc' m' => RFs R /\ getr R 1 = Z_to_bv 64 0x13c74 /\ getr R 10 = Z_to_bv 64 (spZ regs - 336 + 136) /\
       getr R 11 = Z_to_bv 64 0x103fc /\ getr R 12 = Z_to_bv 64 (spZ regs - 336 + 80) /\
       getr R 19 = Z_to_bv 64 (Z.of_nat (length bs)) /\ getr R 20 = Z_to_bv 64 b /\
       getr R 21 = Z_to_bv 64 b1 /\ getr R 8 = Z_to_bv 64 q /\ getr R 9 = Z_to_bv 64 want /\
       getr R 18 = Z_to_bv 64 same /\ pc' = Z_to_bv 64 0x14718 /\ m' = memc'));
    [kbr HM' | kbr HM' | |].
  { rewrite SEG. unfold rmk. pose proof RF' as (P2 & _). rewrite P2, R10', S19, S20, S21, S8, S9, S18.
    eapply Exec.evt_mono; [apply crt_r13; [reflexivity | rewrite MState.unsigned_lit by lia; lia]|].
    intros ms' ->. kfin regs' RF'. }
  intros RR pc2 mem2 regs2 (RF2 & Q1 & Q10 & Q11 & Q12 & Q19 & Q20 & Q21 & Q8 & Q9 & Q18 & -> & ->) HG.
  apply ((PFX RF_getr) _ _ HG) in RF2. rewrite <- HG in Q1, Q10, Q11, Q12, Q19, Q20, Q21, Q8, Q9, Q18.
  exact (st13 ((a, n) :: X) Lc' Ac' regs2 memc' mdc' ((a, n) :: Lamc) (Z.max peakc (lsum ((a, n) :: Lamc))) (cntc + 1)
    Nc same sn want wn q kq b1 k1 Dd Ds [(a, n)] bs b kb CR' ltac:(lia) ltac:(unfold CRT_ALLOCS; lia)
    (Permutation_trans (perm_skip _ PX) (Permutation_middle Ds _ _)) NDd1 NDs1 NODE HBO Hbl BB1 Hbin Hbk RF2 Q1 Q10
    Q11 Q12 Q19 Q20 Q21 Q8 Q9 Q18 Hsn Hwn).
Qed.

(* c11: pj_set(&st, "context", &v), then pj_string(&v, text) *)
Lemma st11 : forall X Lc Ac regsc memc mdc Lamc peakc cntc Nc same sn want wn q kq b1 k1 Dd Ds Dv bs b kb,
  CRs X [(same, sn); (want, wn)] Lc Ac memc mdc Lamc peakc cntc Nc -> (28 <= Nc)%nat ->
  cntc + 37 <= cnt + CRT_ALLOCS -> Permutation X (Ds ++ Dv ++ Dd ++ [(b1, k1); (q, kq)]) ->
  pj_node rsegs memc (lin Lamc) (spZ regs - 336 + 192) (JObj crt_doc8) Dd ->
  pj_node rsegs memc (lin Lamc) (spZ regs - 336 + 136) (JObj crt_s1) Ds ->
  pj_node rsegs memc (lin Lamc) (spZ regs - 336 + 80) (JStr V_PRESET) Dv ->
  Mem.bytes_at rsegs memc q (map (Z_to_bv 8) (b64_enc bs ++ [0])) -> Z.of_nat (length (b64_enc bs)) + 1 <= kq ->
  bytes_ok bs -> Z.of_nat (length bs) <= 9 * 2 ^ 18 + 2 ->
  Mem.bytes_at rsegs memc b (bz bs) -> In (b, kb) Lam -> Z.of_nat (length bs) <= kb ->
  RFs regsc -> getr regsc 1 = Z_to_bv 64 0x13c4c -> getr regsc 10 = Z_to_bv 64 (spZ regs - 336 + 136) ->
  getr regsc 11 = Z_to_bv 64 0x102c2 -> getr regsc 12 = Z_to_bv 64 (spZ regs - 336 + 80) ->
  getr regsc 19 = Z_to_bv 64 (Z.of_nat (length bs)) -> getr regsc 20 = Z_to_bv 64 b ->
  getr regsc 21 = Z_to_bv 64 b1 -> getr regsc 8 = Z_to_bv 64 q -> getr regsc 9 = Z_to_bv 64 want ->
  getr regsc 18 = Z_to_bv 64 same -> 0 < sn -> 0 < wn ->
  SR (ms_segs B) (mkCfg (mkst regsc (Z_to_bv 64 PJ_SET) memc (seg_rom (ms_segs B))) mdc) post.
Proof.
  intros X Lc Ac regsc memc mdc Lamc peakc cntc Nc same sn want wn q kq b1 k1 Dd Ds Dv bs b kb CRc HN HC PX NDd NDs
    NDv TQ Hqk HBO Hbl BB Hbin Hbk RFc R1 R10 R11 R12 R19 R20 R21 R8 R9 R18 Hsn Hwn.
  pose proof RFc as (R2 & RG). pose proof (PFX crt_spr) as (Hs1 & Hs2 & Hs3).
  pose proof alloc_ceiling_val as Hacv. pose proof HCNT as Hcnt. unfold CRT_ALLOCS in *.
  pose proof CRc as ((_ & _ & _ & _ & RAc & _) & _).
  crt_keyt RAc 0x102c2 K_CONTEXT.
  destruct Nc as [|[|[|Nc]]]; [lia | lia | lia |].
  apply (w_set B API SEG ERR GF AX CO L A regs mem md PRE Lam peak cnt bnd RTP RER RGG RGD RSP RGT (PJSET fx) X
    [(same, sn); (want, wn)] Lc Ac regsc memc mdc Lamc peakc cntc Nc (spZ regs - 336 + 136) (spZ regs - 336 + 80)
    0x102c2 crt_s1 (JStr V_PRESET) Ds Dv (Dd ++ [(b1, k1); (q, kq)]) (map (Z_to_bv 8) K_CONTEXT)
    (crt_slk 0x102c2 K_CONTEXT) post FRM CRc R2 (RG 4 ltac:(lia)) ltac:(retok R1) R10 R11 R12 ltac:(lia) ltac:(lia)
    ltac:(lia) ltac:(lia) ltac:(lia) NDs NDv PX ltac:(crt_dep) ltac:(crt_dep) ltac:(crt_dep)
    ltac:(rewrite crt_zb_map by crt_lits; crt_notin) ltac:(rewrite SEG; exact KB)
    (crt_map_nz K_CONTEXT ltac:(crt_lits) ltac:(crt_lits)) KS KRO ltac:(crt_vm) ltac:(lia)).
  intros Lc' Ac' regs' memc' mdc' Lamc' peakc' cntc' Do RP R10' CR' HCN' CS RDC NODE ZW.
  rewrite crt_zb_map in NODE by crt_lits. rewrite crt_psm in NODE by crt_notin.
  destruct (crt_keepT X _ Lc Ac memc mdc Lamc peakc cntc _ (Do ++ Dd ++ [(b1, k1); (q, kq)]) Lc' Ac' memc' mdc'
    Lamc' peakc' cntc' Nc _ (spZ regs - 336 + 136) (spZ regs - 336 + 80) Ds Dv (Dd ++ [(b1, k1); (q, kq)]) CRc CR'
    CS PX (fun y Hy => in_or_app _ _ _ (or_intror Hy)) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
    as (KN & KB2 & KL).
  pose proof (KN _ _ Dd NDd (fun y Hy => in_or_app _ _ _ (or_introl Hy)) ltac:(lia) ltac:(lia) ltac:(lia)) as NDd1.
  pose proof (KB2 q kq q _ ltac:(apply in_or_app; right; right; left; reflexivity) TQ ltac:(lia)
    ltac:(rewrite length_map, length_app; cbn [length]; lia)) as TQ1.
  pose proof (KL b kb b (bz bs) Hbin BB ltac:(lia) ltac:(unfold bz; rewrite length_map; lia)) as BB1.
  pose proof ((PFX RF_pres) _ _ RP RFc) as RF'.
  sv RP regs' R19 S19 19. sv RP regs' R20 S20 20. sv RP regs' R21 S21 21.
  sv RP regs' R8 S8 8. sv RP regs' R9 S9 9. sv RP regs' R18 S18 18.
  pose proof CR' as ((MID' & _) & _). pose proof MID' as (HM' & _).
  rewrite R1.
  eapply (kb_run B regs' (Z_to_bv 64 0x13c4c) memc' mdc'
    (fun R pc' m' => RFs R /\ getr R 1 = Z_to_bv 64 0x13c5c /\ getr R 10 = Z_to_bv 64 (spZ regs - 336 + 80) /\
       getr R 11 = Z_to_bv 64 q /\ getr R 19 = Z_to_bv 64 (Z.of_nat (length bs)) /\ getr R 20 = Z_to_bv 64 b /\
       getr R 21 = Z_to_bv 64 b1 /\ getr R 8 = Z_to_bv 64 q /\ getr R 9 = Z_to_bv 64 want /\
       getr R 18 = Z_to_bv 64 same /\ pc' = Z_to_bv 64 0x14890 /\ m' = memc'));
    [kbr HM' | kbr HM' | |].
  { rewrite SEG. unfold rmk. pose proof RF' as (P2 & _). rewrite P2, R10', S19, S20, S21, S8, S9, S18.
    eapply Exec.evt_mono; [apply crt_r12; [reflexivity | rewrite MState.unsigned_lit by lia; lia]|].
    intros ms' ->. kfin regs' RF'. }
  intros RR pc2 mem2 regs2 (RF2 & Q1 & Q10 & Q11 & Q19 & Q20 & Q21 & Q8 & Q9 & Q18 & -> & ->) HG.
  apply ((PFX RF_getr) _ _ HG) in RF2. rewrite <- HG in Q1, Q10, Q11, Q19, Q20, Q21, Q8, Q9, Q18.
  exact (st12 (Do ++ Dd ++ [(b1, k1); (q, kq)]) Lc' Ac' regs2 memc' mdc' Lamc' peakc' cntc' Nc same sn want wn q kq
    b1 k1 Dd Do bs b kb CR' ltac:(lia) ltac:(unfold CRT_ALLOCS; lia) (Permutation_refl _) NDd1 NODE TQ1 Hqk HBO Hbl
    BB1 Hbin Hbk RF2 Q1 Q10 Q11 Q19 Q20 Q21 Q8 Q9 Q18 Hsn Hwn).
Qed.

(* c10: pj_string(&v, "preset"), then pj_set(&st, "context", &v) *)
Lemma st10 : forall X Lc Ac regsc memc mdc Lamc peakc cntc Nc same sn want wn q kq b1 k1 Dd Ds bs b kb,
  CRs X [(same, sn); (want, wn)] Lc Ac memc mdc Lamc peakc cntc Nc -> (29 <= Nc)%nat ->
  cntc + 38 <= cnt + CRT_ALLOCS -> Permutation X (Ds ++ Dd ++ [(b1, k1); (q, kq)]) ->
  pj_node rsegs memc (lin Lamc) (spZ regs - 336 + 192) (JObj crt_doc8) Dd ->
  pj_node rsegs memc (lin Lamc) (spZ regs - 336 + 136) (JObj crt_s1) Ds ->
  Mem.bytes_at rsegs memc q (map (Z_to_bv 8) (b64_enc bs ++ [0])) -> Z.of_nat (length (b64_enc bs)) + 1 <= kq ->
  bytes_ok bs -> Z.of_nat (length bs) <= 9 * 2 ^ 18 + 2 ->
  Mem.bytes_at rsegs memc b (bz bs) -> In (b, kb) Lam -> Z.of_nat (length bs) <= kb ->
  RFs regsc -> getr regsc 1 = Z_to_bv 64 0x13c34 -> getr regsc 10 = Z_to_bv 64 (spZ regs - 336 + 80) ->
  getr regsc 11 = Z_to_bv 64 0x102b3 ->
  getr regsc 19 = Z_to_bv 64 (Z.of_nat (length bs)) -> getr regsc 20 = Z_to_bv 64 b ->
  getr regsc 21 = Z_to_bv 64 b1 -> getr regsc 8 = Z_to_bv 64 q -> getr regsc 9 = Z_to_bv 64 want ->
  getr regsc 18 = Z_to_bv 64 same -> 0 < sn -> 0 < wn ->
  SR (ms_segs B) (mkCfg (mkst regsc (Z_to_bv 64 PJ_STRING) memc (seg_rom (ms_segs B))) mdc) post.
Proof.
  intros X Lc Ac regsc memc mdc Lamc peakc cntc Nc same sn want wn q kq b1 k1 Dd Ds bs b kb CRc HN HC PX NDd NDs TQ Hqk
    HBO Hbl BB Hbin Hbk RFc R1 R10 R11 R19 R20 R21 R8 R9 R18 Hsn Hwn.
  pose proof RFc as (R2 & RG). pose proof (PFX crt_spr) as (Hs1 & Hs2 & Hs3).
  pose proof (crt_sp B API L A regs mem md PRE) as (_ & _ & Hsp16).
  pose proof alloc_ceiling_val as Hacv. pose proof HCNT as Hcnt. unfold CRT_ALLOCS in *.
  assert (HKs : PJ_STRING_K = 8288) by reflexivity.
  pose proof CRc as ((_ & _ & _ & _ & RAc & _) & _).
  crt_keyt RAc 0x102b3 V_PRESET.
  assert (LK : Z.of_nat (length (map (Z_to_bv 8) V_PRESET)) = 6) by reflexivity.
  destruct Nc as [|Nc]; [lia|].
  apply (w_string B API SEG ERR GF AX CO L A regs mem md PRE Lam peak cnt bnd RTP RER RGG RGD RSP RGT (PJS fx) X
    [(same, sn); (want, wn)] Lc Ac regsc memc mdc Lamc peakc cntc Nc (spZ regs - 336 + 80) 0x102b3
    (map (Z_to_bv 8) V_PRESET) (crt_slk 0x102b3 V_PRESET) post FRM CRc R2 (RG 4 ltac:(lia)) ltac:(retok R1) R10 R11
    ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia) ltac:(lia) ltac:(rewrite SEG; exact KB)
    (crt_map_nz V_PRESET ltac:(crt_lits) ltac:(crt_lits)) KS
    ltac:(unfold cstr_ok; left; intros i Hi; rewrite SEG; apply KRO; lia)
    ltac:(cbn [Frame.disjoint_from]; split; [lia | exact I]) ltac:(cbn [Frame.disjoint_from]; split; [lia | exact I])
    ltac:(crt_vm) ltac:(lia)).
  intros Lc' Ac' regs' memc' mdc' a RP R10' CR' CS RDC NODE.
  rewrite crt_zb_map in NODE by crt_lits.
  set (n := Z.of_nat (length (map (Z_to_bv 8) V_PRESET)) + 1) in *.
  destruct (crt_keepS X _ Lc Ac memc mdc Lamc peakc cntc _ _ Lc' Ac' memc' mdc' _ _ _ Nc _ (spZ regs - 336 + 80) CRc
    CR' CS (fun y Hy => or_intror Hy) ltac:(lia) ltac:(lia)) as (KN & KB2 & KL).
  assert (IDd : incl Dd X).
  { intros y Hy. apply ((PFX perm_in) X _ _ PX). apply in_or_app. right. apply in_or_app. left. exact Hy. }
  assert (IDs : incl Ds X) by (intros y Hy; apply ((PFX perm_in) X _ _ PX); apply in_or_app; left; exact Hy).
  assert (HqX : In (q, kq) X).
  { apply ((PFX perm_in) X _ _ PX). apply in_or_app. right. apply in_or_app. right. right. left. reflexivity. }
  pose proof (KN _ _ Dd NDd IDd ltac:(lia) ltac:(lia)) as NDd1.
  pose proof (KN _ _ Ds NDs IDs ltac:(lia) ltac:(lia)) as NDs1.
  pose proof (KB2 q kq q _ HqX TQ ltac:(lia) ltac:(rewrite length_map, length_app; cbn [length]; lia)) as TQ1.
  pose proof (KL b kb b (bz bs) Hbin BB ltac:(lia) ltac:(unfold bz; rewrite length_map; lia)) as BB1.
  pose proof ((PFX RF_pres) _ _ RP RFc) as RF'.
  sv RP regs' R19 S19 19. sv RP regs' R20 S20 20. sv RP regs' R21 S21 21.
  sv RP regs' R8 S8 8. sv RP regs' R9 S9 9. sv RP regs' R18 S18 18.
  pose proof CR' as ((MID' & _) & _). pose proof MID' as (HM' & _).
  rewrite R1.
  eapply (kb_run B regs' (Z_to_bv 64 0x13c34) memc' mdc'
    (fun R pc' m' => RFs R /\ getr R 1 = Z_to_bv 64 0x13c4c /\ getr R 10 = Z_to_bv 64 (spZ regs - 336 + 136) /\
       getr R 11 = Z_to_bv 64 0x102c2 /\ getr R 12 = Z_to_bv 64 (spZ regs - 336 + 80) /\
       getr R 19 = Z_to_bv 64 (Z.of_nat (length bs)) /\ getr R 20 = Z_to_bv 64 b /\
       getr R 21 = Z_to_bv 64 b1 /\ getr R 8 = Z_to_bv 64 q /\ getr R 9 = Z_to_bv 64 want /\
       getr R 18 = Z_to_bv 64 same /\ pc' = Z_to_bv 64 0x14718 /\ m' = memc'));
    [kbr HM' | kbr HM' | |].
  { rewrite SEG. unfold rmk. pose proof RF' as (P2 & _). rewrite P2, R10', S19, S20, S21, S8, S9, S18.
    eapply Exec.evt_mono; [apply crt_r11; [reflexivity | rewrite MState.unsigned_lit by lia; lia]|].
    intros ms' ->. kfin regs' RF'. }
  intros RR pc2 mem2 regs2 (RF2 & Q1 & Q10 & Q11 & Q12 & Q19 & Q20 & Q21 & Q8 & Q9 & Q18 & -> & ->) HG.
  apply ((PFX RF_getr) _ _ HG) in RF2. rewrite <- HG in Q1, Q10, Q11, Q12, Q19, Q20, Q21, Q8, Q9, Q18.
  exact (st11 ((a, n) :: X) Lc' Ac' regs2 memc' mdc' ((a, n) :: Lamc) (Z.max peakc (lsum ((a, n) :: Lamc))) (cntc + 1)
    Nc same sn want wn q kq b1 k1 Dd Ds [(a, n)] bs b kb CR' ltac:(lia) ltac:(unfold CRT_ALLOCS; lia)
    (Permutation_trans (perm_skip _ PX) (Permutation_middle Ds _ _)) NDd1 NDs1 NODE TQ1 Hqk HBO Hbl BB1 Hbin Hbk RF2
    Q1 Q10 Q11 Q12 Q19 Q20 Q21 Q8 Q9 Q18 Hsn Hwn).
Qed.

(* c9: pj_set(&st, "encoding", &v), then pj_string(&v, "preset") *)
Lemma st9 : forall X Lc Ac regsc memc mdc Lamc peakc cntc Nc same sn want wn q kq b1 k1 Dd Ds Dv bs b kb,
  CRs X [(same, sn); (want, wn)] Lc Ac memc mdc Lamc peakc cntc Nc -> (32 <= Nc)%nat ->
  cntc + 41 <= cnt + CRT_ALLOCS -> Permutation X (Ds ++ Dv ++ Dd ++ [(b1, k1); (q, kq)]) ->
  pj_node rsegs memc (lin Lamc) (spZ regs - 336 + 192) (JObj crt_doc8) Dd ->
  pj_node rsegs memc (lin Lamc) (spZ regs - 336 + 136) (JObj []) Ds ->
  pj_node rsegs memc (lin Lamc) (spZ regs - 336 + 80) (JStr V_BASE64) Dv ->
  Mem.bytes_at rsegs memc q (map (Z_to_bv 8) (b64_enc bs ++ [0])) -> Z.of_nat (length (b64_enc bs)) + 1 <= kq ->
  bytes_ok bs -> Z.of_nat (length bs) <= 9 * 2 ^ 18 + 2 ->
  Mem.bytes_at rsegs memc b (bz bs) -> In (b, kb) Lam -> Z.of_nat (length bs) <= kb ->
  RFs regsc -> getr regsc 1 = Z_to_bv 64 0x13c20 -> getr regsc 10 = Z_to_bv 64 (spZ regs - 336 + 136) ->
  getr regsc 11 = Z_to_bv 64 0x102aa -> getr regsc 12 = Z_to_bv 64 (spZ regs - 336 + 80) ->
  getr regsc 19 = Z_to_bv 64 (Z.of_nat (length bs)) -> getr regsc 20 = Z_to_bv 64 b ->
  getr regsc 21 = Z_to_bv 64 b1 -> getr regsc 8 = Z_to_bv 64 q -> getr regsc 9 = Z_to_bv 64 want ->
  getr regsc 18 = Z_to_bv 64 same -> 0 < sn -> 0 < wn ->
  SR (ms_segs B) (mkCfg (mkst regsc (Z_to_bv 64 PJ_SET) memc (seg_rom (ms_segs B))) mdc) post.
Proof.
  intros X Lc Ac regsc memc mdc Lamc peakc cntc Nc same sn want wn q kq b1 k1 Dd Ds Dv bs b kb CRc HN HC PX NDd NDs
    NDv TQ Hqk HBO Hbl BB Hbin Hbk RFc R1 R10 R11 R12 R19 R20 R21 R8 R9 R18 Hsn Hwn.
  pose proof RFc as (R2 & RG). pose proof (PFX crt_spr) as (Hs1 & Hs2 & Hs3).
  pose proof alloc_ceiling_val as Hacv. pose proof HCNT as Hcnt. unfold CRT_ALLOCS in *.
  pose proof CRc as ((_ & _ & _ & _ & RAc & _) & _).
  crt_keyt RAc 0x102aa K_ENCODING.
  destruct Nc as [|[|[|Nc]]]; [lia | lia | lia |].
  apply (w_set B API SEG ERR GF AX CO L A regs mem md PRE Lam peak cnt bnd RTP RER RGG RGD RSP RGT (PJSET fx) X
    [(same, sn); (want, wn)] Lc Ac regsc memc mdc Lamc peakc cntc Nc (spZ regs - 336 + 136) (spZ regs - 336 + 80)
    0x102aa [] (JStr V_BASE64) Ds Dv (Dd ++ [(b1, k1); (q, kq)]) (map (Z_to_bv 8) K_ENCODING)
    (crt_slk 0x102aa K_ENCODING) post FRM CRc R2 (RG 4 ltac:(lia)) ltac:(retok R1) R10 R11 R12 ltac:(lia) ltac:(lia)
    ltac:(lia) ltac:(lia) ltac:(lia) NDs NDv PX ltac:(crt_dep) ltac:(crt_dep) ltac:(crt_dep)
    ltac:(rewrite crt_zb_map by crt_lits; crt_notin) ltac:(rewrite SEG; exact KB)
    (crt_map_nz K_ENCODING ltac:(crt_lits) ltac:(crt_lits)) KS KRO ltac:(crt_vm) ltac:(lia)).
  intros Lc' Ac' regs' memc' mdc' Lamc' peakc' cntc' Do RP R10' CR' HCN' CS RDC NODE ZW.
  rewrite crt_zb_map in NODE by crt_lits. rewrite crt_psm in NODE by crt_notin.
  destruct (crt_keepT X _ Lc Ac memc mdc Lamc peakc cntc _ (Do ++ Dd ++ [(b1, k1); (q, kq)]) Lc' Ac' memc' mdc'
    Lamc' peakc' cntc' Nc _ (spZ regs - 336 + 136) (spZ regs - 336 + 80) Ds Dv (Dd ++ [(b1, k1); (q, kq)]) CRc CR'
    CS PX (fun y Hy => in_or_app _ _ _ (or_intror Hy)) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
    as (KN & KB2 & KL).
  pose proof (KN _ _ Dd NDd (fun y Hy => in_or_app _ _ _ (or_introl Hy)) ltac:(lia) ltac:(lia) ltac:(lia)) as NDd1.
  pose proof (KB2 q kq q _ ltac:(apply in_or_app; right; right; left; reflexivity) TQ ltac:(lia)
    ltac:(rewrite length_map, length_app; cbn [length]; lia)) as TQ1.
  pose proof (KL b kb b (bz bs) Hbin BB ltac:(lia) ltac:(unfold bz; rewrite length_map; lia)) as BB1.
  pose proof ((PFX RF_pres) _ _ RP RFc) as RF'.
  sv RP regs' R19 S19 19. sv RP regs' R20 S20 20. sv RP regs' R21 S21 21.
  sv RP regs' R8 S8 8. sv RP regs' R9 S9 9. sv RP regs' R18 S18 18.
  pose proof CR' as ((MID' & _) & _). pose proof MID' as (HM' & _).
  rewrite R1.
  eapply (kb_run B regs' (Z_to_bv 64 0x13c20) memc' mdc'
    (fun R pc' m' => RFs R /\ getr R 1 = Z_to_bv 64 0x13c34 /\ getr R 10 = Z_to_bv 64 (spZ regs - 336 + 80) /\
       getr R 11 = Z_to_bv 64 0x102b3 /\ getr R 19 = Z_to_bv 64 (Z.of_nat (length bs)) /\ getr R 20 = Z_to_bv 64 b /\
       getr R 21 = Z_to_bv 64 b1 /\ getr R 8 = Z_to_bv 64 q /\ getr R 9 = Z_to_bv 64 want /\
       getr R 18 = Z_to_bv 64 same /\ pc' = Z_to_bv 64 0x14890 /\ m' = memc'));
    [kbr HM' | kbr HM' | |].
  { rewrite SEG. unfold rmk. pose proof RF' as (P2 & _). rewrite P2, R10', S19, S20, S21, S8, S9, S18.
    eapply Exec.evt_mono; [apply crt_r10; [reflexivity | rewrite MState.unsigned_lit by lia; lia]|].
    intros ms' ->. kfin regs' RF'. }
  intros RR pc2 mem2 regs2 (RF2 & Q1 & Q10 & Q11 & Q19 & Q20 & Q21 & Q8 & Q9 & Q18 & -> & ->) HG.
  apply ((PFX RF_getr) _ _ HG) in RF2. rewrite <- HG in Q1, Q10, Q11, Q19, Q20, Q21, Q8, Q9, Q18.
  exact (st10 (Do ++ Dd ++ [(b1, k1); (q, kq)]) Lc' Ac' regs2 memc' mdc' Lamc' peakc' cntc' Nc same sn want wn q kq
    b1 k1 Dd Do bs b kb CR' ltac:(lia) ltac:(unfold CRT_ALLOCS; lia) (Permutation_refl _) NDd1 NODE TQ1 Hqk HBO Hbl
    BB1 Hbin Hbk RF2 Q1 Q10 Q11 Q19 Q20 Q21 Q8 Q9 Q18 Hsn Hwn).
Qed.

(* c8: pj_string(&v, "base64"), then pj_set(&st, "encoding", &v); the statement St8 of check_round_trip_st8.v *)
Lemma st8s : forall X Lc Ac regsc memc mdc Lamc peakc cntc Nc same sn want wn q kq b1 k1 Dd bs b kb,
  CRs X [(same, sn); (want, wn)] Lc Ac memc mdc Lamc peakc cntc Nc ->
  cntc + 56 <= cnt + CRT_ALLOCS -> (148 <= Nc)%nat ->
  Permutation X (Dd ++ [(b1, k1); (q, kq)]) ->
  pj_node rsegs memc (lin Lamc) (spZ regs - 336 + 192) (JObj crt_doc8) Dd ->
  pj_node rsegs memc (lin Lamc) (spZ regs - 336 + 136) (JObj []) [] ->
  pj_cstr rsegs memc (lin Lamc) q kq (b64_enc bs) -> bytes_ok bs -> Z.of_nat (length bs) <= 9 * 2 ^ 18 ->
  Mem.bytes_at rsegs memc b (bz bs) -> In (b, kb) Lam -> Z.of_nat (length bs) <= kb ->
  RF regs regsc -> getr regsc 1 = Z_to_bv 64 0x13c08 -> getr regsc 10 = Z_to_bv 64 (spZ regs - 336 + 80) ->
  getr regsc 11 = Z_to_bv 64 0x103c5 ->
  getr regsc 19 = Z_to_bv 64 (Z.of_nat (length bs)) -> getr regsc 20 = Z_to_bv 64 b ->
  getr regsc 21 = Z_to_bv 64 b1 -> getr regsc 8 = Z_to_bv 64 q ->
  getr regsc 9 = Z_to_bv 64 want -> getr regsc 18 = Z_to_bv 64 same -> 0 < sn -> 0 < wn ->
  SR (ms_segs B) (mkCfg (@mkst fx regsc (Z_to_bv 64 PJ_STRING) memc (seg_rom (ms_segs B))) mdc) post.
Proof.
  intros X Lc Ac regsc memc mdc Lamc peakc cntc Nc same sn want wn q kq b1 k1 Dd bs b kb CRc HC HN PX NDd NDs CQ HBO
    Hbl BB Hbin Hbk RFc R1 R10 R11 R19 R20 R21 R8 R9 R18 Hsn Hwn.
  pose proof RFc as (R2 & RG). pose proof (PFX crt_spr) as (Hs1 & Hs2 & Hs3).
  pose proof (crt_sp B API L A regs mem md PRE) as (_ & _ & Hsp16).
  pose proof alloc_ceiling_val as Hacv. pose proof HCNT as Hcnt. unfold CRT_ALLOCS in *.
  assert (HKs : PJ_STRING_K = 8288) by reflexivity.
  pose proof CQ as (_ & Hqk & _ & TQ).
  pose proof CRc as ((_ & _ & _ & _ & RAc & _) & _).
  crt_keyt RAc 0x103c5 V_BASE64.
  assert (LK : Z.of_nat (length (map (Z_to_bv 8) V_BASE64)) = 6) by reflexivity.
  destruct Nc as [|Nc]; [lia|].
  apply (w_string B API SEG ERR GF AX CO L A regs mem md PRE Lam peak cnt bnd RTP RER RGG RGD RSP RGT (PJS fx) X
    [(same, sn); (want, wn)] Lc Ac regsc memc mdc Lamc peakc cntc Nc (spZ regs - 336 + 80) 0x103c5
    (map (Z_to_bv 8) V_BASE64) (crt_slk 0x103c5 V_BASE64) post FRM CRc R2 (RG 4 ltac:(lia)) ltac:(retok R1) R10 R11
    ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia) ltac:(lia) ltac:(rewrite SEG; exact KB)
    (crt_map_nz V_BASE64 ltac:(crt_lits) ltac:(crt_lits)) KS
    ltac:(unfold cstr_ok; left; intros i Hi; rewrite SEG; apply KRO; lia)
    ltac:(cbn [Frame.disjoint_from]; split; [lia | exact I]) ltac:(cbn [Frame.disjoint_from]; split; [lia | exact I])
    ltac:(crt_vm) ltac:(lia)).
  intros Lc' Ac' regs' memc' mdc' a RP R10' CR' CS RDC NODE.
  rewrite crt_zb_map in NODE by crt_lits.
  set (n := Z.of_nat (length (map (Z_to_bv 8) V_BASE64)) + 1) in *.
  destruct (crt_keepS X _ Lc Ac memc mdc Lamc peakc cntc _ _ Lc' Ac' memc' mdc' _ _ _ Nc _ (spZ regs - 336 + 80) CRc
    CR' CS (fun y Hy => or_intror Hy) ltac:(lia) ltac:(lia)) as (KN & KB2 & KL).
  assert (IDd : incl Dd X) by (intros y Hy; exact ((PFX incl_perm_l) X Dd _ PX _ Hy)).
  assert (HqX : In (q, kq) X).
  { apply ((PFX perm_in) X _ _ PX). apply in_or_app. right. right. left. reflexivity. }
  pose proof (KN _ _ Dd NDd IDd ltac:(lia) ltac:(lia)) as NDd1.
  pose proof (KN _ _ [] NDs (fun y (H : In y []) => match H with end) ltac:(lia) ltac:(lia)) as NDs1.
  pose proof (KB2 q kq q _ HqX TQ ltac:(lia) ltac:(rewrite length_map, length_app; cbn [length]; lia)) as TQ1.
  pose proof (KL b kb b (bz bs) Hbin BB ltac:(lia) ltac:(unfold bz; rewrite length_map; lia)) as BB1.
  pose proof ((PFX RF_pres) _ _ RP RFc) as RF'.
  sv RP regs' R19 S19 19. sv RP regs' R20 S20 20. sv RP regs' R21 S21 21.
  sv RP regs' R8 S8 8. sv RP regs' R9 S9 9. sv RP regs' R18 S18 18.
  pose proof CR' as ((MID' & _) & _). pose proof MID' as (HM' & _).
  rewrite R1.
  eapply (kb_run B regs' (Z_to_bv 64 0x13c08) memc' mdc'
    (fun R pc' m' => RFs R /\ getr R 1 = Z_to_bv 64 0x13c20 /\ getr R 10 = Z_to_bv 64 (spZ regs - 336 + 136) /\
       getr R 11 = Z_to_bv 64 0x102aa /\ getr R 12 = Z_to_bv 64 (spZ regs - 336 + 80) /\
       getr R 19 = Z_to_bv 64 (Z.of_nat (length bs)) /\ getr R 20 = Z_to_bv 64 b /\
       getr R 21 = Z_to_bv 64 b1 /\ getr R 8 = Z_to_bv 64 q /\ getr R 9 = Z_to_bv 64 want /\
       getr R 18 = Z_to_bv 64 same /\ pc' = Z_to_bv 64 0x14718 /\ m' = memc'));
    [kbr HM' | kbr HM' | |].
  { rewrite SEG. unfold rmk. pose proof RF' as (P2 & _). rewrite P2, R10', S19, S20, S21, S8, S9, S18.
    eapply Exec.evt_mono; [apply crt_r9; [reflexivity | rewrite MState.unsigned_lit by lia; lia]|].
    intros ms' ->. kfin regs' RF'. }
  intros RR pc2 mem2 regs2 (RF2 & Q1 & Q10 & Q11 & Q12 & Q19 & Q20 & Q21 & Q8 & Q9 & Q18 & -> & ->) HG.
  apply ((PFX RF_getr) _ _ HG) in RF2. rewrite <- HG in Q1, Q10, Q11, Q12, Q19, Q20, Q21, Q8, Q9, Q18.
  exact (st9 ((a, n) :: X) Lc' Ac' regs2 memc' mdc' ((a, n) :: Lamc) (Z.max peakc (lsum ((a, n) :: Lamc))) (cntc + 1)
    Nc same sn want wn q kq b1 k1 Dd [] [(a, n)] bs b kb CR' ltac:(lia) ltac:(unfold CRT_ALLOCS; lia) (perm_skip _ PX)
    NDd1 NDs1 NODE TQ1 Hqk HBO ltac:(lia) BB1 Hbin Hbk RF2 Q1 Q10 Q11 Q12 Q19 Q20 Q21 Q8 Q9 Q18 Hsn Hwn).
Qed.

End F3.
End ST.

(* Stage 8 of check_round_trip, as stated in check_round_trip_st8.v. *)
Theorem st8 : St8.
Proof.
  intros rc B API SEG MAL FRE ERR GF AX CO BSP RTP RER RGG RGD STRLEN STRCMP BCMP PJO PJG PJGS MALLOC FREE FFREE ENC DEC
    PJS PJSET PJF PJW PJP L A regs mem md PRE Lam peak cnt bnd LG0 HCNT RSP RGT fx0 fx FK FRM.
  exact (@st8s rc B API SEG MAL FRE ERR GF AX CO BSP RTP RER RGG RGD STRLEN STRCMP BCMP PJO PJG PJGS MALLOC FREE FFREE
    ENC DEC PJS PJSET PJF PJW PJP L A regs mem md PRE Lam peak cnt bnd LG0 HCNT RSP RGT fx0 fx FK FRM).
Qed.
