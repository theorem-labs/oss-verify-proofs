(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LBase LSCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require LiaOn.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn.SepM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import CJ_bandM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_skipws.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_skipws.CJ_band2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_skipws.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_skipws.CJ_band.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import BImg RT_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_kit.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit.RT_shlem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import CJ_iface AShadow CJ_tree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_phex4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_phex4.CJ_pbuf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import CJ_conv CJ_skipws.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_phex4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_phex4.CJ_parse_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_phex4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_phex4.CJ_parse_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import CJ_pvalue_lemmas ICPT_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StoreCache.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import StoreCache.
Local Ltac mem_after_store ::= mem_after_store_cached.
Local Ltac addr_eq_tac ::= addr_eq_tac_cached.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Lemma bytes_of_present : forall m E (k : nat),
  0 <= E -> E + Z.of_nat k <= 2^64 ->
  (forall i, 0 <= i < Z.of_nat k -> m (wa (E + i)) <> None) ->
  exists bs, length bs = k /\ bytes_at bsegs m E bs.
Proof.
  intros m E k HE HK H.
  assert (G : forall j, (j <= k)%nat -> exists bs, length bs = j /\ forall i, (i < j)%nat -> mrd bsegs m (wa (E + Z.of_nat i)) = nth_error bs i).
  { induction j as [|j IH]; intros Hj.
    - exists []. split; [reflexivity|]. intros i Hi; lia.
    - (nelim (IH ltac:(lia)) 3%nat; intros bs Hlen Hbs).
      destruct (m (wa (E + Z.of_nat j))) as [b|] eqn:Eb; [| exfalso; apply (H (Z.of_nat j)); [lia| exact Eb]].
      exists (bs ++ [b]). split; [rewrite length_app; cbn; lia|].
      intros i Hi. destruct (Nat.eqb_spec i j).
      + subst i. rewrite nth_error_app2 by lia. rewrite Hlen, Nat.sub_diag. cbn. unfold mrd. rewrite Eb. reflexivity.
      + rewrite nth_error_app1 by lia. apply Hbs. lia. }
  (nelim (G k ltac:(lia)) 3%nat; intros bs Hlen Hbs). exists bs. split; [exact Hlen|].
  split; [lia|]. split; [rewrite Hlen; lia|]. intros i Hi. apply Hbs. lia.
Qed.

(* [comment removed for export] *)
Lemma block_slack_bytes : forall (AI : art_iface) sp0 SPB LB LF TRS B m mo g D n E,
  ART AI sp0 SPB LB LF TRS B m mo g -> In (D, n) LB -> D <= E <= D + n ->
  exists slack, bytes_at bsegs m E slack /\ Z.of_nat (length slack) = (- E) mod 8.
Proof.
  intros AI sp0 SPB LB LF TRS B m mo g D n E HL HIN HE.
  (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL HIN) 4%nat; intros R1 R2 R3 R4). try rewrite alloc_ceiling_eq in R4. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in R1. bandM. sepM.
  (nelimp (art_block_wr AI _ _ _ _ _ _ _ _ _ _ _ HL HIN) 3%nat; intros _ _ WR).
  destruct (bytes_of_present m E (Z.to_nat ((- E) mod 8)) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as (bs & Hlen & HB). (* [comment removed for export] *)
  2:{ exists bs. split; [exact HB| lia]. }
  intros i Hi. destruct (Z.lt_ge_cases (E + i) (D + n)) as [LT|GE].
  - intros Hm. apply (WR (E + i - D) ltac:(lia)). replace (D + (E + i - D)) with (E + i) by lia.
    unfold wview. rewrite Hm.
    rewrite (find_segment_noseg bsegs (wa (E + i)) 1); [reflexivity| | lia].
    apply rt_noseg_high. rewrite wa_unsigned by lia. unfold AIMG_HI. lia.
  - replace (E + i) with (D + n + (E + i - (D + n))) by lia. eapply (art_block_slack AI); [exact HL| exact HIN| lia|].
    unfold roundup. Z.div_mod_to_equations. lia.
Qed.

Section WO.
  Variable AI : art_iface.
  Variable TI : trs_iface.
  Hypothesis STRLEN : strlen_icpt_spec.
  Hypothesis PWLO : parse_wlopts_stmt AI TI.

  Theorem parse_wopts_spec : parse_wopts_stmt AI TI.
  Proof.
    unfold parse_wopts_stmt. intros until errv. intros PRE DV VD BY NN BLEN -> ->.
    pose proof PRE as (HL & TV & IND & ERR & MI & ST & CEIL & BOT & LO & SP1 & SP2 & SP3 & SP4 & SP5 & AL & S0LE & RA1 & RA2 & FRM & TP & STW & STPV & STPO & STC & BPRE). (* [comment removed for export] *)
    pose proof (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL IND) as (D1 & D2 & D3 & D4). (* [comment removed for export] *)
    try rewrite alloc_ceiling_eq in D4, CEIL. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in D1. bandM. sepM. unfold PARSE_DOC_STACK, PARSE_STACK in LO.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
    pose proof (bytes_at_bound _ _ _ _ BY) as BYB. rewrite length_app in BYB. cbn [length] in BYB.
    set (len := Z.of_nat (length str)) in *.
    (nelim (block_slack_bytes AI _ _ _ _ _ _ _ _ _ D n (V + len + 1) HL IND ltac:(lia)) 3%nat; intros slack SLK SLL).
    assert (BYS : bytes_at bsegs m V (str ++ Z_to_bv 8 0 :: slack)).
    { change (str ++ Z_to_bv 8 0 :: slack) with (str ++ [wb 0] ++ slack). rewrite app_assoc. apply (proj2 (bytes_at_app _ _ _ _ _)).
      split; [exact BY|]. rewrite length_app. cbn [length]. replace (V + Z.of_nat (length str + 1)) with (V + len + 1) by lia. exact SLK. }
    pose proof (art_shadow AI _ _ _ _ _ _ _ _ _ _ _ HL IND) as [_ SOD].
    unfold PARSE_WOPTS, wz. pose proof ERR as ERR'. unfold AERRNO, ATP in ERR'.
    eapply lscps_step_evt.
    pose proof (munch_refl [(bv_unsigned sp + -32 - ASTRFN_STACK, bv_unsigned sp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    unfold ASTRFN_STACK in MU.
    zstep. carve_frame 32%nat ST. do 4 zstep.
    zstep. if_cases KV; zify_cond KV; [exfalso; lia|].
    zstep. zstep. zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m0' end.
    assert (HL1 : ART AI sp0 SPB LB [] TRS B m0' mo g).
    { eapply (art_frame_store AI); [exact HL| exact MU| exact WM| try rewrite alloc_ceiling_eq; lia| lia]. }
    pose proof (art_shadow AI _ _ _ _ _ _ _ _ _ _ _ HL1 IND) as [_ SOD1].
    (* [comment removed for export] *)
    eapply evt_cut.
    { pose proof STRLEN as SL. unfold strlen_icpt_spec in SL.
      eapply SL with (lo := lo) (s := V) (str := str) (slack := slack); clear SL; rewrite ?unsigned_lit by lia;
        first [ lazymatch goal with |- icpt_cells _ => eapply art_icpt_cells; exact HL1 end | exact MI | exact ST | exact BYS | exact NN | reflexivity
              | unfold ASTRFN_STACK; lia
              | app_rng AI
              | eapply shadow_ok_sub; [exact SOD1| lia| lia| lia]
              | rewrite ?alloc_ceiling_eq; lia ]. }
    cbv beta. intros ms' PO.
    (nelim PO 21%nat; intros u0 u1 u2 ua1 ua2 ua3 ua4 ua5 ua6 ua7 u3 u4 u5 u6 m1 -> MU1 WM1 MI1 BY1 ST1).
    rewrite ?unsigned_lit in MU1, ST1 by lia. unfold ASTRFN_STACK in MU1.
    replace (ret_pc (Z_to_bv 64 0x8281c)) with (Z_to_bv 64 0x8281c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    eapply rw_cells_transport in FR; [| exact MU1| exact WM1| cbn [disjoint_from cells_size Cells.csize Nat.add length]; lia].
    eapply rw_cells_transport in ERR'; [| exact MU1| exact WM1| cbn [disjoint_from cells_size Cells.csize Nat.add length]; lia].
    assert (MU2 : munch [(bv_unsigned sp + -32 - 2400, bv_unsigned sp)] m m1).
    { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU1]. intros x Hx. cbn in Hx |- *. lia. }
    pose proof (wmono_trans _ _ _ _ WM WM1) as WM2.
    clear SOD SOD1 HL MU WM.
    assert (HL2 : ART AI sp0 SPB LB [] TRS B m1 mo g).
    { eapply (art_frame_store AI); [exact HL1| exact MU1| exact WM1| try rewrite alloc_ceiling_eq; lia| lia]. }
    do 9 zstep. zstep.
    release_frame FR ST1 (bv_unsigned sp).
    apply evt_done. change (Z_to_bv 64 534620) with (wz PARSE_WLOPTS).
    assert (BY2 : bytes_at bsegs m1 V ((str ++ [wb 0]) ++ slack)) by (rewrite <- app_assoc; exact BY1).
    apply (proj1 (bytes_at_app _ _ _ _ _)) in BY2. destruct BY2 as [BY2 _].
    eapply lscps_mono.
    { pose proof PWLO as X. unfold parse_wlopts_stmt in X.
      eapply X with (D := D) (n := n) (CA := V) (blen := len + 1) (bs := str ++ [wb 0]) (lo := lo); clear X; rewrite ?unsigned_lit by lia;
        first [ reflexivity | exact BLEN | lia
              | exact BY2
              | rewrite length_app; cbn [length]; lia
              | idtac ].
      unfold parse_doc_pre. repeat (split; [first [eassumption | reflexivity | rewrite ?alloc_ceiling_eq; unfold PARSE_DOC_STACK, PARSE_STACK; lia] |]).
      exact BPRE. }
    cbv beta. intros ms' mo' g' PO. unfold parse_doc_post in PO |- *.
    (nelim PO 25%nat; intros v0 v1 v2 w0 w1 w2 w3 w4 w5 w6 w7 v3 v4 v5 v6 F' fc' m' r LB' TRS' B' errv' E REST).
    exists v0, v1, v2, w0, w1, w2, w3, w4, w5, w6, w7, v3, v4, v5, v6, F', fc', m', r, LB', TRS', B', errv'.
    split; [exact E|].
    (nelim REST 13%nat; intros A0 FA FRM' MI' ST' ERR2 HL' TV' GM' HB' BY' DP' RES).
    repeat (split; [assumption|]). split; [| exact RES].
    eapply dpres_trans; [| exact DP']. eapply magree_of_munch; [exact MU2| exact WM2|].
    intros a Ha (Hc & _). apply (doc_addr_lits sp sp0 LB a) in Hc || idtac. cbn.
    destruct Hc as [Hs|[Hi|[(A & n0 & Hin & Hr)|[(Fr' & k & [] & _)|Hsh]]]]; try lia.
    - pose proof (aclient_image_lt a Hi). lia.
    - (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL2 Hin) 4%nat; intros _ _ _ R4). try rewrite alloc_ceiling_eq in R4. lia.
    - unfold astack_shadow, SH, SHADOW_OFFSET in Hsh. try rewrite alloc_ceiling_eq in Hsh. Z.div_mod_to_equations. lia.
  Qed.
End WO.


End CeilWrap.
