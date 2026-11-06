(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA L5Defs L5Core PmHeapIfaceA PmIcptIfaceA
  PmLibDefs PmLibDefsA PmLibSpecsA PmEncSpecs PmLibSpecsXA PmLibSpecsW PmLibSpecsXAW PmRef PmRefFacts PmRefAllow PmRefNonneg PmRefRead PmRefXA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutHeapA CutL5A.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmAsanKit Require Import PtKitA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import TopSpecsXB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmTopBW Require Import TopSpecsBW.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PKAW.
Section K.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Abbreviation segs := (hl_segs L).
Abbreviation mem := PMSA.mem.

Definition wstA (M : mem) (P : Z) (ps : PML.pstate) (c : PMR.ctrl) (w : list Z) : Prop := PMRXA.rm_matchA L c M P ps /\ PMXAW.win_bytesA L M ps w.

(* [comment removed for export] *)
Lemma wstA_rm : forall M P ps c w, wstA M P ps c w -> PMRXA.rm_matchA L c M P ps.  Proof. intros M P ps c w [H _]; exact H. Qed.
Lemma wstA_wb : forall M P ps c w, wstA M P ps c w -> PMXAW.win_bytesA L M ps w.  Proof. intros M P ps c w [_ H]; exact H. Qed.
Lemma wstA_core : forall M P ps c w, wstA M P ps c w -> PMR.c_st c = PML.ps_st ps /\ PMR.c_more c = PML.ps_more ps /\ PMR.c_done c = PML.ps_done ps.
Proof. intros M P ps c w [((A & B & C & _) & _) _]. split; [exact A | split; [exact B | exact C]]. Qed.
Lemma wstA_rm_core : forall M P ps c w, wstA M P ps c w -> PMR.rm_core c ps.
Proof. intros M P ps c w [[A _] _]. exact A. Qed.
Lemma win_bytesA_len : forall M ps w, PMXAW.win_bytesA L M ps w -> Z.of_nat (length w) = PML.winlen ps.
Proof. intros M ps w H. unfold PMXAW.win_bytesA, PML.winlen in *. destruct (PML.ps_win ps) as [[p e]|]; [exact (proj1 (proj2 H)) | rewrite H; reflexivity]. Qed.
Lemma wstA_len : forall M P ps c w, wstA M P ps c w -> Z.of_nat (length w) = PML.winlen ps.
Proof. intros M P ps c w [_ H]. exact (win_bytesA_len M ps w H). Qed.
Lemma wstA_nil : forall M P ps c w, wstA M P ps c w -> PMSA.win_exhausted ps -> w = [].
Proof.
  intros M P ps c w WS EX. pose proof (wstA_len M P ps c w WS) as LEN. unfold PMSA.win_exhausted, PML.winlen in *.
  destruct (PML.ps_win ps) as [[p e]|]; [subst p|]; (destruct w; [reflexivity | cbn [length] in LEN; lia]).
Qed.
Lemma wstA_exh : forall M P ps c, wstA M P ps c [] -> PMSA.win_exhausted ps.
Proof. intros M P ps c WS. pose proof (wstA_len M P ps c [] WS) as LEN. cbn [length Z.of_nat] in LEN. unfold PMSA.win_exhausted, PML.winlen in *. destruct (PML.ps_win ps) as [[p e]|]; [lia | exact I]. Qed.
Lemma wstA_cons : forall M P ps c w, wstA M P ps c w -> ~ PMSA.win_exhausted ps -> w <> [].
Proof. intros M P ps c w WS NE ->. exact (NE (wstA_exh M P ps c WS)). Qed.
Lemma wstA_range : forall M P ps c w, wstA M P ps c w -> Forall (fun b => 0 <= b <= 255) w.
Proof. intros M P ps c w [_ H]. unfold PMXAW.win_bytesA in H. destruct (PML.ps_win ps) as [[p e]|]; [exact (proj2 (proj2 H)) | rewrite H; constructor]. Qed.
(* [comment removed for export] *)
Lemma wf_stack_nots : forall ps1, PML.wf_ps ps1 -> PML.ps_more ps1 = true -> Forall PMRA.nots (PML.ps_stack ps1).
Proof.
  intros ps1 WF Hm. destruct WF as (_ & _ & _ & _ & C & T & HS & HC & HM). destruct (HM Hm) as (_ & _ & _ & HT & _). rewrite HS. unfold PMRA.nots.
  constructor; [unfold PML.ST_ROOT, PML.ST_STRING, PML.ST_NUMBER; lia|]. apply Forall_app. split.
  - apply Forall_impl with (P := PML.is_container); [|exact HC]. intros a [-> | ->]; unfold PML.ST_OBJECT, PML.ST_ARRAY, PML.ST_STRING, PML.ST_NUMBER; lia.
  - destruct HT as [[-> _] | [[-> _] | [(S & HS1 & -> & _) | (S & HS1 & -> & _)]]];
      repeat first [apply Forall_nil | apply Forall_cons]; try (destruct HS1 as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]); cbv; lia.
Qed.
Lemma wstA_SIq : forall M P ps c w, wstA M P ps c w -> PML.wf_ps ps -> PML.ps_more ps = true -> PMRN.SIq c.
Proof.
  intros M P ps c w [[CO [HS HN]] _] WF Hm. apply (PMRN.SIq_intro c ps CO); [| exact (wf_stack_nots ps WF Hm)].
  pose proof CO as (Cst & _). unfold PMRN.tok. rewrite Cst. intros [X|X]; [exact (proj1 (proj2 (HS X))) | exact (proj2 (HN X))].
Qed.
Lemma SIq_ctrl0 : PMRN.SIq PMR.ctrl0.
Proof. split; [intros _; cbn; lia | cbn; constructor; [unfold PMRA.nots, PML.ST_ROOT, PML.ST_STRING, PML.ST_NUMBER; lia | constructor]]. Qed.

(* [comment removed for export] *)
Lemma st_small : forall ps, PML.wf_ps ps -> PML.ws_ok ps -> 0 <= PML.ps_st ps < 256.
Proof.
  intros ps WF WS. destruct (PML.ps_more ps) eqn:MO.
  - destruct WF as (_ & _ & _ & _ & C & T & _ & _ & HM). destruct (HM MO) as (_ & _ & HD & _). unfold PML.handled in HD. lia.
  - destruct (WS MO) as (C & _ & _ & [[X _]|[X _]] & _); rewrite X; unfold PML.ST_DONE, PML.ST_CR; lia.
Qed.
Lemma st_mod : forall ps, PML.wf_ps ps -> PML.ws_ok ps -> PML.ps_st ps mod 256 = PML.ps_st ps.
Proof. intros ps WF WS. apply Z.mod_small. exact (st_small ps WF WS). Qed.

(* [comment removed for export] *)
Section Ag.
Variables (M M' : mem) (S : Z -> Prop).
Hypothesis AG : forall a, S a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a).
Abbreviation out := (PTA.out S).
Lemma rm_matchA_ag : forall c P ps, out (P + 148) 8 -> out (P + 220) 1 -> PMRXA.rm_matchA L c M P ps -> PMRXA.rm_matchA L c M' P ps.
Proof.
  intros c P ps O1 O2 (CO & HS & HN). split; [exact CO|]. split; [|exact HN]. intros X. destruct (HS X) as (A & B & C & D & E & (t & F & G)).
  split; [exact A|]. split; [exact B|]. split; [exact C|].
  split; [intros Y; apply (PTA.u32_ag segs M M' S AG); [apply (PTA.out_sub _ _ _ _ _ O1); lia | exact (D Y)]|].
  split; [intros Y; apply (PTA.u32_ag segs M M' S AG); [apply (PTA.out_sub _ _ _ _ _ O1); lia | exact (E Y)]|].
  exists t. split; [apply (PTA.u8_ag segs M M' S AG); [exact O2 | exact F] | exact G].
Qed.
Lemma win_bytesA_ag : forall ps w, (forall p e, PML.ps_win ps = Some (p, e) -> out p (e - p)) -> PMXAW.win_bytesA L M ps w -> PMXAW.win_bytesA L M' ps w.
Proof.
  intros ps w OW H. unfold PMXAW.win_bytesA in *. destruct (PML.ps_win ps) as [[p e]|]; [|exact H]. destruct H as (B & LEN & R).
  split; [|split; [exact LEN | exact R]]. apply (PTA.bytes_ag segs M M' S AG); [rewrite LEN; exact (OW p e eq_refl) | exact B].
Qed.
Lemma wstA_ag : forall P ps c w, out (P + 148) 8 -> out (P + 220) 1 -> (forall p e, PML.ps_win ps = Some (p, e) -> out p (e - p)) -> wstA M P ps c w -> wstA M' P ps c w.
Proof. intros P ps c w O1 O2 OW [RM WB]. split; [exact (rm_matchA_ag c P ps O1 O2 RM) | exact (win_bytesA_ag ps w OW WB)]. Qed.
(* [comment removed for export] *)
Lemma wstA_ag_exh : forall P ps c, out (P + 148) 8 -> out (P + 220) 1 -> wstA M P ps c [] -> wstA M' P ps c [].
Proof.
  intros P ps c O1 O2 [RM WB]. split; [exact (rm_matchA_ag c P ps O1 O2 RM)|].
  unfold PMXAW.win_bytesA in *. destruct (PML.ps_win ps) as [[p e]|]; [|exact WB]. destruct WB as (B & LEN & R). split; [intros i Hi; cbn [length] in Hi; lia | split; [exact LEN | exact R]].
Qed.
End Ag.

(* [comment removed for export] *)
Lemma rm_matchA_set_win : forall c M P ps mw, PMRXA.rm_matchA L c M P ps -> PMRXA.rm_matchA L c M P (PML.ps_set_win ps mw).
Proof. intros c M P ps mw H. destruct ps. exact H. Qed.
Lemma rm_matchA_set_win_inv : forall c M P ps mw, PMRXA.rm_matchA L c M P (PML.ps_set_win ps mw) -> PMRXA.rm_matchA L c M P ps.
Proof. intros c M P ps mw H. destruct ps. exact H. Qed.
Lemma win_bytesA_set_win : forall M ps p k w, L5.bytes_at segs M p w -> Z.of_nat (length w) = k -> Forall (fun b => 0 <= b <= 255) w ->
  PMXAW.win_bytesA L M (PML.ps_set_win ps (Some (p, p + k))) w.
Proof. intros M ps p k w B LEN R. unfold PMXAW.win_bytesA. destruct ps. cbn [PML.ps_win PML.ps_set_win]. split; [exact B | split; [lia | exact R]]. Qed.
Lemma wstA_set_win : forall M P ps c w p k, PMRXA.rm_matchA L c M P ps -> L5.bytes_at segs M p w -> Z.of_nat (length w) = k -> Forall (fun b => 0 <= b <= 255) w ->
  wstA M P (PML.ps_set_win ps (Some (p, p + k))) c w.
Proof. intros M P ps c w p k RM B LEN R. split; [exact (rm_matchA_set_win c M P ps _ RM) | exact (win_bytesA_set_win M ps p k w B LEN R)]. Qed.
(* [comment removed for export] *)
Lemma wstA_reset : forall M P ps, PML.ps_win ps = None -> wstA M P (TPSA.ps_reset ps) PMR.ctrl0 [].
Proof.
  intros M P ps HW. split.
  - unfold PMRXA.rm_matchA, PMR.rm_core, TPSA.ps_reset. cbn [PML.ps_st PML.ps_more PML.ps_done PML.ps_level PML.ps_stack PMR.c_st PMR.c_more PMR.c_done PMR.c_level PMR.c_stack PMR.ctrl0].
    split; [repeat split; reflexivity|]. split; intros X; cbv in X; discriminate X.
  - unfold PMXAW.win_bytesA, TPSA.ps_reset. cbn [PML.ps_win]. rewrite HW. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma bytes_at_nil_len : forall (M : mem) p w, length w = 0%nat -> L5.bytes_at segs M p w.
Proof. intros M p [|b w] H; [intros i Hi; cbn in Hi; lia | discriminate H]. Qed.
Lemma bytes_at_skipn : forall (M : mem) p w k, L5.bytes_at segs M p w -> L5.bytes_at segs M (p + Z.of_nat k) (skipn k w).
Proof.
  intros M p w k H i Hi. rewrite length_skipn in Hi. rewrite nth_skipn. replace (p + Z.of_nat k + Z.of_nat i) with (p + Z.of_nat (k + i)) by lia. apply H. lia.
Qed.
Lemma bytes_at_firstn : forall (M : mem) p w k, L5.bytes_at segs M p w -> L5.bytes_at segs M p (firstn k w).
Proof.
  intros M p w k H i Hi. rewrite length_firstn in Hi. rewrite nth_firstn. replace (i <? k)%nat with true by (symmetry; apply Nat.ltb_lt; lia). apply H. lia.
Qed.
Lemma isrc_text_bytes : forall IC (M : mem) IS rep g rd, PMLA.isrc_at segs IC M IS rep g rd -> L5.bytes_at segs M (PML.srep_data (IS + 80) rep) (PML.srep_chars rep).
Proof.
  intros IC M IS rep g rd H. unfold PMLA.isrc_at in H. cbv zeta in H. destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & STR & _).
  unfold PMLA.str_at in STR. destruct rep as [s|cap p s]; cbn [PML.srep_data PML.srep_chars].
  - destruct STR as (_ & _ & B & _). exact B.
  - destruct STR as ((_ & _ & _ & _ & B & _) & _). exact B.
Qed.
Lemma chunk_len : forall IS rep gp, PML.srep_data (IS + 80) rep <= gp <= PML.srep_data (IS + 80) rep + Z.of_nat (length (PML.srep_chars rep)) ->
  Z.of_nat (length (TPSAW.chunk_of IS rep gp)) = Z.min 16384 (PML.srep_data (IS + 80) rep + Z.of_nat (length (PML.srep_chars rep)) - gp).
Proof.
  intros IS rep gp H. unfold TPSAW.chunk_of, TPSAW.rest_of. rewrite length_firstn, length_skipn. unfold PMR.CHUNK. lia.
Qed.
Lemma chunk_bytes : forall IC (M : mem) IS rep g rd gp, PMLA.isrc_at segs IC M IS rep g rd ->
  PML.srep_data (IS + 80) rep <= gp <= PML.srep_data (IS + 80) rep + Z.of_nat (length (PML.srep_chars rep)) -> L5.bytes_at segs M gp (TPSAW.chunk_of IS rep gp).
Proof.
  intros IC M IS rep g rd gp H Hgp. unfold TPSAW.chunk_of, TPSAW.rest_of. apply bytes_at_firstn.
  replace gp with (PML.srep_data (IS + 80) rep + Z.of_nat (Z.to_nat (gp - PML.srep_data (IS + 80) rep))) at 1 by lia. apply bytes_at_skipn. exact (isrc_text_bytes IC M IS rep g rd H).
Qed.
Lemma chunk_range : forall IS rep gp, Forall (fun b => 0 <= b <= 255) (PML.srep_chars rep) -> Forall (fun b => 0 <= b <= 255) (TPSAW.chunk_of IS rep gp).
Proof. intros IS rep gp H. unfold TPSAW.chunk_of, TPSAW.rest_of. apply PMRR.Forall_firstn. apply PMRR.Forall_skipn. exact H. Qed.
Lemma memcpy_bytes : forall (M2 : mem) dst n bs, Z.of_nat (length bs) = n -> Forall (fun b => 0 <= b <= 255) bs ->
  (forall i, 0 <= i < n -> exists v, (nth_error (map (fun z => Z_to_bv 8 z) bs) (Z.to_nat i) = Some (Z_to_bv 8 v) /\ 0 <= v < 256) /\ byte_at M2 (dst + i) v) ->
  L5.bytes_at segs M2 dst bs.
Proof.
  intros M2 dst n bs LEN FA H i Hi. destruct (H (Z.of_nat i) ltac:(lia)) as (v & [Hn Hv] & Hb). rewrite Nat2Z.id in Hn.
  rewrite nth_error_map in Hn. destruct (nth_error bs i) as [b|] eqn:Hi2; [|discriminate Hn]. cbn [option_map] in Hn.
  pose proof (proj1 (Forall_forall _ _) FA b (nth_error_In _ _ Hi2)) as Rb. cbn beta in Rb.
  assert (Hbv : b = v).
  { apply (f_equal (fun o : option (bv 8) => match o with Some x => bv_unsigned x | None => 0 end)) in Hn. cbn beta iota in Hn.
    rewrite !Z_to_bv_unsigned in Hn. unfold bv_wrap in Hn. change (bv_modulus 8) with 256 in Hn. rewrite !Z.mod_small in Hn by lia. exact Hn. }
  rewrite (nth_error_nth' bs 0 Hi) in Hi2. injection Hi2 as <-. apply CL5A.byte_at_u8. rewrite Hbv. exact Hb.
Qed.
End K.
End PKAW.
