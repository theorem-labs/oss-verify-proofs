(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Step Arr Tac Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Ledger Hull Restrict EvtAcct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState ADepotM.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic ARtStmts ARtSscs AMTac AMallocA AMalmys.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AQWf.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AQWf AQPart.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AQWf.AQOps OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AQWf OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AQPart.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
#[local] Notation WF := (WF AL_pboth).   (* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Notation wz z := (Z_to_bv 64 z) (only parsing).

(* [comment removed for export] *)
Lemma mapped_C8 : forall (m : mem) a, mapped m a 8 -> 0 <= a -> a + 8 <= 2^64 -> exists w : word, rw_cells rsegs m a [C8 w].
Proof.
  intros m a M H0 H1. exists (le_bytes_to_word (rdbytes m a 8)).
  apply ro_rw; [| cbn; exact M]. apply bytes_ro_C8. rewrite le8_of_bytes by apply rdbytes_length.
  apply rdbytes_bytes_at; [exact M| lia| cbn; lia].
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma batches_repr_app_inv : forall (mm : mem) sb l1 l2,
  batches_repr LPA mm sb (l1 ++ l2) ->
  batches_repr LPA mm sb l2 /\
  (forall b, In b l1 -> mapped mm (batch_addr sb b) kQuarantineBatchBytes).
Proof.
  intros mm sb l1. induction l1 as [|b l1 IH]; intros l2 H; [split; [exact H| intros b []]|].
  cbn [batches_repr app] in H. (first [ dand6 H as Hn Hs Hc He Hm Hr | destruct H as (Hn & Hs & Hc & He & Hm & Hr) ]).
  destruct (IH l2 Hr) as [R M]. split; [exact R|].
  intros b' [<-|Hb']; [exact Hm| exact (M b' Hb')].
Qed.

Lemma batches_repr_last : forall (mm : mem) sb l b,
  batches_repr LPA mm sb (l ++ [b]) ->
  let a := batch_addr sb b in
  u64_at rsegs mm (a + off_qb_next) 0 /\ u64_at rsegs mm (a + off_qb_size) (batch_bytes b) /\
  u64_at rsegs mm (a + off_qb_count) (Z.of_nat (length (ba_entries b))) /\
  (forall i e, nth_error (ba_entries b) i = Some e -> u64_at rsegs mm (a + off_qb_batch (Z.of_nat i)) (hdr_of sb (qe_chunk e) (qe_n e))) /\
  mapped mm a kQuarantineBatchBytes.
Proof.
  intros mm sb l b H. destruct (batches_repr_app_inv mm sb l [b] H) as [R _]. cbn [batches_repr] in R.
  (first [ dand6 R as Hn Hs Hc He Hm _ | destruct R as (Hn & Hs & Hc & He & Hm & _) ]). cbv zeta. cbn [batch_addr] in Hn.
  split; [exact Hn| split; [exact Hs| split; [exact Hc| split; [exact He| exact Hm]]]].
Qed.

(* [comment removed for export] *)
Lemma batches_repr_relast : forall (mm mm' : mem) sb l b b',
  batches_repr LPA mm sb (l ++ [b]) -> ba_idx b' = ba_idx b ->
  (forall x, In x l \/ x = b -> forall i, (i < length (ba_entries x))%nat -> Z.of_nat i < 1021) ->
  (forall x a', In x l -> batch_addr sb x <= a' < batch_addr sb x + kQuarantineBatchBytes -> mm' (Z_to_bv 64 a') = mm (Z_to_bv 64 a')) ->
  (let a := batch_addr sb b' in
   u64_at rsegs mm' (a + off_qb_next) 0 /\ u64_at rsegs mm' (a + off_qb_size) (batch_bytes b') /\
   u64_at rsegs mm' (a + off_qb_count) (Z.of_nat (length (ba_entries b'))) /\
   (forall i e, nth_error (ba_entries b') i = Some e -> u64_at rsegs mm' (a + off_qb_batch (Z.of_nat i)) (hdr_of sb (qe_chunk e) (qe_n e))) /\
   mapped mm' a kQuarantineBatchBytes) ->
  batches_repr LPA mm' sb (l ++ [b']).
Proof.
  intros mm mm' sb l. induction l as [|x l IH]; intros b b' H EI LEN AG NEW.
  - cbn [batches_repr app]. cbv zeta in NEW. (first [ dand5 NEW as N1 N2 N3 N4 N5 | destruct NEW as (N1 & N2 & N3 & N4 & N5) ]).
    split; [exact N1| split; [exact N2| split; [exact N3| split; [exact N4| split; [exact N5| exact I]]]]].
  - cbn [batches_repr app] in H |- *. (first [ dand6 H as Hn Hs Hc He Hm Hr | destruct H as (Hn & Hs & Hc & He & Hm & Hr) ]).
    assert (AGx : forall a', batch_addr sb x <= a' < batch_addr sb x + 8192 -> mm' (Z_to_bv 64 a') = mm (Z_to_bv 64 a'))
      by (intros a' Ha'; apply (AG x); [left; reflexivity| unfold kQuarantineBatchBytes; exact Ha']).
    unfold batch_addr in AGx.
    split; [| split; [| split; [| split; [| split]]]].
    + destruct l as [|y l']; cbn [app] in Hn |- *.
      * unfold batch_addr. rewrite EI. eapply u64_at_agree; [exact Hn|]. intros i Hi. apply AGx. unfold batch_addr, off_qb_next in *. lia.
      * eapply u64_at_agree; [exact Hn|]. intros i Hi. apply AGx. unfold batch_addr, off_qb_next in *. lia.
    + eapply u64_at_agree; [exact Hs|]. intros i Hi. apply AGx. unfold batch_addr, off_qb_size in *. lia.
    + eapply u64_at_agree; [exact Hc|]. intros i Hi. apply AGx. unfold batch_addr, off_qb_count in *. lia.
    + intros i e Hi. eapply u64_at_agree; [exact (He i e Hi)|]. intros j Hj.
      pose proof (nth_error_Some_lt _ _ _ Hi) as IL.
      assert (Z.of_nat i < 1021) by (apply (LEN x); [left; left; reflexivity| exact IL]).
      apply AGx. unfold batch_addr, off_qb_batch in *. lia.
    + eapply mapped_agree_gen; [exact Hm|]. intros i Hi. apply AGx. unfold batch_addr, kQuarantineBatchBytes in *. lia.
    + apply (IH b b' Hr EI); [| | exact NEW].
      * intros y Hy. apply LEN. destruct Hy as [Hy| ->]; [left; right; exact Hy| right; reflexivity].
      * intros y a' Hy Ha'. apply (AG y); [right; exact Hy| exact Ha'].
Qed.

Section Live.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {DR : DepotRep}.
  Variables (A : AState) (m : mem) (md : Model) (p n0 : Z).
  Hypothesis AI : pa_ainv A m md.
  Hypothesis HL : as_live A p = Some n0.
  Let v := aview_of (pa_hull A) m.
  Let W : WF A. Proof. exact (ai_wf _ _ _ _ _ _ _ AI). Qed.

  #[using="HL"] Lemma free_li : exists li, a_livemap A !! p = Some li /\ li_n li = n0.
  Proof.
    unfold as_live, as_live_ in HL. destruct (a_livemap A !! p) as [li|] eqn:E; [| discriminate]. cbn in HL.
    exists li. split; [reflexivity| congruence].
  Qed.

  #[using="W HL AI p md m A DR Clg"] Lemma free_n0 : 1 <= n0 < REQ_MAX /\ user_size n0 = n0.
  Proof.
    (first [ dex1 free_li as li; destruct free_li as [Hl Hn] | dand3 free_li as li Hl Hn | destruct free_li as (li & Hl & Hn) ]). (first [ pose proof ((wfV A W)) as dR_6; dand3 dR_6 as V1 _ _ | destruct (wfV A W) as (V1 & _ & _) ]). pose proof (V1 p li Hl) as (N & _). cbv zeta in N.
    subst n0. split; [exact N|]. unfold user_size. destruct (Z.eqb_spec (li_n li) 0); lia.
  Qed.

  (* [comment removed for export] *)
  #[using="W HL AI md DR"] Lemma free_HDR : exists (b1 id : Z), 0 <= b1 < 256 /\ Z.land b1 3 = 1 /\ Z.land b1 0x7f = kHdrByte1Malloc /\ 0 <= id < 2^32 /\
    rw_cells rsegs v (p + -16) [C1 (Z_to_bv 8 CHUNK_ALLOCATED); C1 (Z_to_bv 8 b1); C2 (wz (size_hi n0)); C4 (wz n0)] /\
    rw_cells rsegs v (p + -8) [C8 (wz id)].
  Proof.
    (first [ dex1 free_li as li; destruct free_li as [Hl Hn] | dand3 free_li as li Hl Hn | destruct free_li as (li & Hl & Hn) ]). destruct free_n0 as [NR US].
    (first [ pose proof ((wfV A W)) as dR_8; dand3 dR_8 as V1 _ _ | destruct (wfV A W) as (V1 & _ & _) ]). (first [ pose proof ((V1 p li Hl)) as dR_9; dand3 dR_9 as N U _ | pose proof (V1 p li Hl) as (N & U & _) ]). cbv zeta in U.
    (first [ pose proof ((ar_live _ _ _ _ _ (ai_repr _ _ _ _ _ _ _ AI) p li Hl)) as dR_10; dand3 dR_10 as HR MU MC | pose proof (ar_live _ _ _ _ _ (ai_repr _ _ _ _ _ _ _ AI) p li Hl) as (HR & MU & MC) ]).
    destruct HR as [(id & b1 & IDR & B1R & B1M & CEL) _]. change (p_sb (a_pl A)) with (a_sb A) in CEL. rewrite <- U, Hn in CEL.
    exists b1, id. split; [exact B1R|]. split.
    { replace (Z.land b1 3) with (Z.land (Z.land b1 127) 3) by (rewrite <- Z.land_assoc; reflexivity). rewrite B1M. reflexivity. }
    split; [exact B1M|]. split; [exact IDR|].
    unfold chunk_hdr_cells in CEL. cbn [ch_state ch_b1 ch_size ch_ctx] in CEL. rewrite US in CEL.
    apply (rw_cells_app_split _ _ [C1 (Z_to_bv 8 CHUNK_ALLOCATED); C1 (Z_to_bv 8 b1); C2 (wz (size_hi n0)); C4 (wz n0)] [C8 (wz id)]) in CEL as [C1' C2'].
    cbn [cells_size csize Nat.add] in C2'. replace (p - 16 + Z.of_nat 8) with (p + -8) in C2' by lia. replace (p - 16) with (p + -16) in C1' by lia.
    split; [exact C1'| exact C2'].
  Qed.

  (* [comment removed for export] *)
  Lemma roundup8_le : forall u n E, u mod 8 = 0 -> E mod 8 = 0 -> u + n <= E -> u + 8 * ((n + 7) / 8) <= E.
  Proof.
    intros u n E Hu HE H.
    pose proof (Z_div_mod_eq_full (n + 7) 8). pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(lia)).
    pose proof (Z_div_mod_eq_full u 8). pose proof (Z_div_mod_eq_full E 8). nia.
  Qed.

  Let ch_lo (li : liveinfo) := chunk_lo (a_sb A) (li_chunk li).
  Let ch_hi (li : liveinfo) := chunk_hi (a_sb A) (li_chunk li).

  #[using="W HL AI md DR"] Lemma free_span : forall li, a_livemap A !! p = Some li ->
    p mod 16 = 0 /\ aobj (ch_lo li) (ch_hi li - ch_lo li) /\ ch_lo li <= p + -16 /\ p + 8 * ((n0 + 7) / 8) <= ch_hi li /\
    ch_hi li <= alloc_ceiling /\ mapped v (ch_lo li) (ch_hi li - ch_lo li).
  Proof.
    intros li Hl. (first [ dex1 free_li as li'; destruct free_li as [Hl' Hn] | dand3 free_li as li' Hl' Hn | destruct free_li as (li' & Hl' & Hn) ]). rewrite Hl in Hl'. injection Hl' as <-. destruct free_n0 as [NR US].
    (first [ pose proof ((asI_live_ok A m md p n0 AI HL)) as dR_12; dand5 dR_12 as _ PM HB CE _ | pose proof (asI_live_ok A m md p n0 AI HL) as (_ & PM & HB & CE & _) ]).
    (first [ pose proof ((wfV A W)) as dR_13; dand3 dR_13 as V1 _ _ | destruct (wfV A W) as (V1 & _ & _) ]). (first [ pose proof ((V1 p li Hl)) as dR_14; dand3 dR_14 as N U C | pose proof (V1 p li Hl) as (N & U & C) ]). cbv zeta in U, C.
    (first [ pose proof ((ar_live _ _ _ _ _ (ai_repr _ _ _ _ _ _ _ AI) p li Hl)) as dR_15; dand3 dR_15 as _ _ MC | pose proof (ar_live _ _ _ _ _ (ai_repr _ _ _ _ _ _ _ AI) p li Hl) as (_ & _ & MC) ]). change (p_sb (a_pl A)) with (a_sb A) in MC.
    pose proof alloc_ceiling_val as HC. (first [ pose proof ((sb_facts A W)) as dR_16; dand5 dR_16 as _ SBA HB6 RSB SCE | pose proof (sb_facts A W) as (_ & SBA & HB6 & RSB & SCE) ]).
    split; [exact PM|]. subst ch_lo ch_hi.
    destruct li as [[[c k]|[mb nn]] n]; cbn [li_chunk li_n chunk_lo chunk_hi alloc_beg] in *; subst n.
    - (first [ dand3 C as N2 Hc Hk | destruct C as (N2 & Hc & Hk) ]). pose proof (class_of_range n0 ltac:(lia)) as CR. rewrite <- Hc in CR.
      (first [ pose proof ((primary_layout (a_sb A) c k n0 CR ltac:(lia) Hc)) as dR_18; dand5 dR_18 as L1 L2 L3 L5 L4 | pose proof (primary_layout (a_sb A) c k n0 CR ltac:(lia) Hc) as (L1 & L2 & L3 & L5 & L4) ]). cbn [user_of alloc_beg] in *.
      (first [ pose proof ((carved_chunk_bounds A c k W CR Hk)) as dR_19; dand4 dR_19 as B1 B2 B3 B4 | pose proof (carved_chunk_bounds A c k W CR Hk) as (B1 & B2 & B3 & B4) ]). pose proof (region_piece_bounds A c W CR) as RB. cbv zeta in RB.
      (first [ dand12 RB as R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12 | destruct RB as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12) ]).
      pose proof (class_size_mod32 c CR) as CM. rewrite <- U in *.
      split; [apply aobj_hi; unfold kHighMemBeg, kFreeArrayOffset, kRegionSize, kSpaceSize in *; lia|]. split; [lia|]. split.
      + apply roundup8_le; [apply (mod0_down _ 16 8); [exists 2; reflexivity| exact PM] | | exact L2].
        rewrite Z.add_mod by lia. rewrite (mod0_down _ 32 8 ltac:(exists 4; reflexivity) B3), (mod0_down _ 32 8 ltac:(exists 4; reflexivity) CM). reflexivity.
      + split; [unfold kFreeArrayOffset, kRegionSize, kSpaceSize in *; lia| exact MC].
    - (first [ dand3 C as N2 -> Hin | destruct C as (N2 & -> & Hin) ]). (first [ pose proof ((secondary_layout mb n0 N2)) as dR_22; dand7 dR_22 as S1 S2 S3 S4 S5 S6 S7 | pose proof (secondary_layout mb n0 N2) as (S1 & S2 & S3 & S4 & S5 & S6 & S7) ]). cbn [user_of alloc_beg] in *.
      (first [ pose proof ((sec_chunk_bounds A _ W Hin)) as dR_23; dand5 dR_23 as B1 B2 B3 B4 B5 | pose proof (sec_chunk_bounds A _ W Hin) as (B1 & B2 & B3 & B4 & B5) ]). cbn [cs_map cs_n] in *.
      pose proof (map_size_page n0) as MP. rewrite <- U in *.
      split; [replace (mb + map_size n0 - mb) with (map_size n0) by lia; apply (proj1 (aobj_app_rangeA _ _)); exact B3|]. split; [unfold kPageSize in *; lia|]. split.
      + apply roundup8_le; [apply (mod0_down _ 16 8); [exists 2; reflexivity| exact PM] | | lia].
        rewrite Z.add_mod by lia. rewrite (mod0_down _ 4096 8 ltac:(exists 512; reflexivity) B2), (mod0_down _ kPageSize 8 ltac:(exists 512; reflexivity) MP). reflexivity.
      + split; [first [assumption | unfold kHighMemBeg, kPageSize in *; lia] | exact MC].
  Qed.

  #[using="ch_hi ch_lo W v HL AI md m A DR"] Lemma free_geom : p mod 16 = 0 /\ aobj (p + -16) (16 + 8 * ((n0 + 7) / 8)) /\ p + n0 <= alloc_ceiling /\ p + 8 * ((n0 + 7) / 8) <= alloc_ceiling.
  Proof.
    (first [ dex1 free_li as li; destruct free_li as [Hl Hn] | dand3 free_li as li Hl Hn | destruct free_li as (li & Hl & Hn) ]). (first [ pose proof ((free_span li Hl)) as dR_25; dand6 dR_25 as PM H1 H2 H3 H4 _ | destruct (free_span li Hl) as (PM & H1 & H2 & H3 & H4 & _) ]). destruct free_n0 as [NR _].
    pose proof (Z_div_mod_eq_full (n0 + 7) 8). pose proof (Z.mod_pos_bound (n0 + 7) 8 ltac:(lia)).
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; [exact PM| apply (aobj_sub _ _ _ _ H1); lia| lia| lia].
  Qed.

  (* [comment removed for export] *)
  #[using="ch_hi ch_lo W HL AI n0 md DR"] Lemma free_CTX0 : exists w : word, rw_cells rsegs v p [C8 w].
  Proof.
    (first [ dex1 free_li as li; destruct free_li as [Hl Hn] | dand3 free_li as li Hl Hn | destruct free_li as (li & Hl & Hn) ]). (first [ pose proof ((free_span li Hl)) as dR_27; dand6 dR_27 as PM H1 H2 H3 H4 MC | destruct (free_span li Hl) as (PM & H1 & H2 & H3 & H4 & MC) ]). destruct free_n0 as [NR _].
    pose proof (Z_div_mod_eq_full (n0 + 7) 8). pose proof (Z.mod_pos_bound (n0 + 7) 8 ltac:(lia)). pose proof alloc_ceiling_val.
    apply mapped_C8; [| pose proof (aobj_facts _ _ H1); lia| lia].
    intros i Hi. replace (p + i) with (ch_lo li + (p - ch_lo li + i)) by lia. apply MC. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma bytes_rw_CB : forall (mm : mem) a bs n, bytes_at rsegs mm a bs -> length bs = n -> 0x60a000 <= a -> rw_cells rsegs mm a [CB n bs].
  Proof.
    intros mm a bs n B L Ha. pose proof (bytes_at_mapped_high mm a bs B Ha) as M. rewrite L in M.
    (first [ dand3 B as B0 B1 B2 | destruct B as (B0 & B1 & B2) ]). rewrite L in B1.
    split; [split; [cbn; rewrite L; split; [reflexivity| exact I] |]|].
    - cbn [cells_bytes cbytes]. rewrite app_nil_r. split; [exact B0|]. split; [rewrite L; exact B1|]. intros i Hi. apply B2. first [exact Hi | rewrite L; exact Hi | rewrite <- L; exact Hi].
    - cbn [cells_size csize]. rewrite Nat.add_0_r. apply mapped_wr_at; [exact M| lia| lia].
  Qed.

  #[using="ch_hi ch_lo W HL AI md DR"] Lemma free_SHC : rw_cells rsegs v (sh p) [CB (Z.to_nat ((n0 + 7) / 8)) (shpat n0)].
  Proof.
    destruct free_n0 as [NR _]. (first [ dand4 free_geom as PM HB CE _ | destruct free_geom as (PM & HB & CE & _) ]).
    pose proof (asI_live_shadow A m md p n0 AI HL) as SB. fold v in SB.
    pose proof (Z_div_mod_eq_full (n0 + 7) 8). pose proof (Z.mod_pos_bound (n0 + 7) 8 ltac:(lia)).
    apply bytes_rw_CB; [exact SB| apply shpat_length_nat; lia|].
    (first [ pose proof ((aobj_facts _ _ HB)) as dR_30; dand5 dR_30 as AF1 AF2 AF3 AF4 [AF5|AF5] | pose proof (aobj_facts _ _ HB) as (AF1 & AF2 & AF3 & AF4 & [AF5|AF5]) ]).
    - pose proof (sh_lowapp_range p ltac:(unfold kLowShadowMapBeg in *; lia)). lia.
    - pose proof (sh_high_range p ltac:(pose proof alloc_ceiling_val; unfold kHighMemBeg in *; lia)). unfold kHighShadowMapBeg in *. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="ch_hi ch_lo W HL AI n0 md DR"] Lemma free_IAM : ro_cells rsegs v (0xb5dc8 + 8 * Z.shiftr p 32) [C8 (wz 0)].
  Proof.
    (first [ dand4 free_geom as PM HB CE _ | destruct free_geom as (PM & HB & CE & _) ]). pose proof alloc_ceiling_val as HC. destruct free_n0 as [NR _]. pose proof (aobj_facts _ _ HB) as AF.
    destruct (ar_ia _ _ _ _ _ (ai_repr _ _ _ _ _ _ _ AI)) as [MAP1 _].
    assert (IR : 0 <= Z.shiftr p 32 < kDepotNodesL1).
    { rewrite Z.shiftr_div_pow2 by lia. unfold kDepotNodesL1, kHighMemBeg in *. split; [apply Z.div_pos; lia|].
      apply Z.div_lt_upper_bound; [lia|]. change (2^32 * 2^15) with (2^47). lia. }
    specialize (MAP1 (Z.shiftr p 32) IR). change (al_internal_allocator_inst AL_pboth) with 0xb5dc0 in MAP1.
    replace (0xb5dc0 + 8 + 8 * Z.shiftr p 32) with (0xb5dc8 + 8 * Z.shiftr p 32) in MAP1 by lia.
    exact (u64_ro _ _ _ MAP1).
  Qed.

  (* [comment removed for export] *)
  #[using="AI md DR"] Lemma free_QLIM : ro_cells rsegs v (0xb1830 + 64) [C8 (wz (2^28))] /\ ro_cells rsegs v (0xb1830 + 80) [C8 (wz (2^20))].
  Proof.
    pose proof (ar_consts _ _ _ _ _ (ai_repr _ _ _ _ _ _ _ AI)) as CO. unfold consts_repr_ in CO. cbv zeta in CO.
    (first [ dand15 CO as _ _ _ _ _ _ _ _ _ _ _ QMAX QMIN QCACHE _ | destruct CO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & QMAX & QMIN & QCACHE & _) ]).
    change (al_instance AL_pboth) with 0xb1558 in QMAX, QCACHE.
    unfold off_q_max_size, off_q_max_cache_size, kQuarantineMaxSize, kQuarantineCacheSize in *.
    split.
    - replace (0xb1830 + 64) with (0xb1558 + 792) by reflexivity. exact (u64_ro _ _ _ QMAX).
    - replace (0xb1830 + 80) with (0xb1558 + 808) by reflexivity. exact (u64_ro _ _ _ QCACHE).
  Qed.

  (* [comment removed for export] *)
  #[using="AI md DR"] Lemma free_FCo :
       ro_cells rsegs v 0xb5898 [C1 (Z_to_bv 8 1)]
    /\ ro_cells rsegs v 0xb58bc [C4 (wz 30)]
    /\ ro_cells rsegs v 0xa8b60 [C8 (wz 0x1466e8)] /\ ro_cells rsegs v (0x1466e8 + 34) [C1 (Z_to_bv 8 1)]
    /\ ro_cells rsegs v 0x146688 [C8 (wz 0)]
    /\ ro_cells rsegs v 0xa8b68 [C8 (wz 0xb23b8)] /\ ro_cells rsegs v (0xb23b8 + 48) [C4 (wz 0)]
    /\ ro_cells rsegs v (0xb1830 + 64) [C8 (wz (2^28))] /\ ro_cells rsegs v (0xb1830 + 80) [C8 (wz (2^20))].
  Proof.
    pose proof (proj1 (ar_consts _ _ _ _ _ (ai_repr _ _ _ _ _ _ _ AI))) as CF. fold v in CF.
    pose proof (ar_consts _ _ _ _ _ (ai_repr _ _ _ _ _ _ _ AI)) as CR. fold v in CR.
    split; [exact (hit_INI A m md AI)|]. split; [exact (hit_CMCS A m md AI)|]. split.
    { pose proof (consts_cell v 0xa8b60 (le8 (Z_to_bv 64 0x1466e8)) CF eq_refl) as H. apply bytes_ro_C8. exact H. }
    split; [exact (hit_CFU A m md AI)|]. split.
    { unfold consts_repr_ in CR. cbv zeta in CR. cbn [al_malloc_hooks AL_pboth] in CR.
      assert (X : fill_at rsegs v 1336960 80 0) by tauto. unfold fill_at in X.
      change (repeat (Z_to_bv 8 0) (Z.to_nat 80)) with (repeat (Z_to_bv 8 0) 8 ++ (le8 (Z_to_bv 64 0) ++ repeat (Z_to_bv 8 0) 64)) in X.
      apply bytes_at_app in X as [_ X]. apply bytes_at_app in X as [X _]. cbn [length repeat Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add] in X.
      apply bytes_ro_C8. exact X. }
    split; [exact (hit_AF1 A m md AI)|]. split.
    { pose proof (consts_cell v 0xb23b8 pa_asan_flags_bytes CF eq_refl) as H. apply bytes_ro_C4.
      apply (bytes_at_as v _ _ _ (bytes_at_mid v 0xb23b8 pa_asan_flags_bytes 48 4 H ltac:(cbn; lia))). byteseq. }
    exact free_QLIM.
  Qed.

  (* [comment removed for export] *)
  #[using="W AI md DR"] Lemma free_TST : exists fr fd, 0 <= fr < 2^64 /\ 0 <= fd < 2^64 /\ rw_cells rsegs v (p_thr (a_pl A) + 2824) [C8 (wz fr); C8 (wz fd)].
  Proof.
    (first [ pose proof ((ar_cache _ _ _ _ _ (ai_repr _ _ _ _ _ _ _ AI))) as dR_33; dand5 dR_33 as _ _ _ TM _ | destruct (ar_cache _ _ _ _ _ (ai_repr _ _ _ _ _ _ _ AI)) as (_ & _ & _ & TM & _) ]). fold v in TM.
    pose proof (place_facts A W) as (Pthr & _). cbv zeta in Pthr. pose proof alloc_ceiling_val as CE. pose proof (app_facts _ _ (proj1 Pthr)) as PthrF.
    destruct (mapped_C8 v (p_thr (a_pl A) + 2824) ltac:(intros i Hi; replace (p_thr (a_pl A) + 2824 + i) with (p_thr (a_pl A) + (2824 + i)) by lia; apply TM; lia)
                ltac:(unfold kHighMemBeg in *; lia) ltac:(lia)) as [w1 R1].
    destruct (mapped_C8 v (p_thr (a_pl A) + 2832) ltac:(intros i Hi; replace (p_thr (a_pl A) + 2832 + i) with (p_thr (a_pl A) + (2832 + i)) by lia; apply TM; lia)
                ltac:(unfold kHighMemBeg in *; lia) ltac:(lia)) as [w2 R2].
    exists (bv_unsigned w1), (bv_unsigned w2). pose proof (zr_word w1) as Z1. pose proof (zr_word w2) as Z2. unfold inr64 in Z1, Z2.
    split; [lia|]. split; [lia|]. rewrite !Z_to_bv_bv_unsigned.
    apply (rw_cells_app_join _ _ [C8 w1] [C8 w2]); [exact R1|]. cbn [cells_size csize Nat.add]. replace (p_thr (a_pl A) + 2824 + Z.of_nat 8) with (p_thr (a_pl A) + 2832) by lia. exact R2.
  Qed.

  (* [comment removed for export] *)
  #[using="ch_hi ch_lo W v HL AI md m DR Clg"] Lemma free_sep : let lo := p + -16 in let sz := 8 * ((n0 + 7) / 8) + 16 in
    apart lo sz (p_ctx (a_pl A)) 0x10000 /\ apart lo sz (p_thr (a_pl A)) 4096 /\
    apart lo sz (p_nodes0 (a_pl A)) kDepotNodesBlock /\ apart lo sz (p_frames0 (a_pl A)) kStackStoreBlockBytes.
  Proof.
    cbv zeta. (first [ dex1 free_li as li; destruct free_li as [Hl Hn] | dand3 free_li as li Hl Hn | destruct free_li as (li & Hl & Hn) ]). (first [ pose proof ((free_span li Hl)) as dR_35; dand6 dR_35 as PM H1 H2 H3 H4 MC | destruct (free_span li Hl) as (PM & H1 & H2 & H3 & H4 & MC) ]). destruct free_n0 as [NR _].
    (first [ pose proof ((bm_nth_fixed A)) as dR_36; dand10 dR_36 as E0 E1 E2 E3 E4 E5 E6 E7 E8 _ | pose proof (bm_nth_fixed A) as (E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & _) ]).
    (first [ pose proof ((sb_facts A W)) as dR_37; dand5 dR_37 as _ SBA HB6 RSB SCE | pose proof (sb_facts A W) as (_ & SBA & HB6 & RSB & SCE) ]). pose proof alloc_ceiling_val as CE.
    unfold a_thr, a_ctx, a_nodes0, a_frames0, a_b6, a_sb in *.
    (* [comment removed for export] *)
    assert (CH : exists i b s, nth_error (big_maps A) i = Some (b, s) /\ i <> 4%nat /\ i <> 5%nat /\ i <> 7%nat /\ i <> 8%nat /\
                  b <= ch_lo li /\ ch_hi li <= b + s).
    { (first [ pose proof ((wfV A W)) as dR_38; dand3 dR_38 as V1 _ _ | destruct (wfV A W) as (V1 & _ & _) ]). (first [ pose proof ((V1 p li Hl)) as dR_39; dand3 dR_39 as N U C | pose proof (V1 p li Hl) as (N & U & C) ]). cbv zeta in C.
      subst ch_lo ch_hi. destruct li as [[[c k]|[mb nn]] n]; cbn [li_chunk li_n chunk_lo chunk_hi alloc_beg] in *.
      - (first [ dand3 C as N2 Hc Hk | destruct C as (N2 & Hc & Hk) ]). pose proof (class_of_range n ltac:(lia)) as CR. rewrite <- Hc in CR.
        (first [ pose proof ((carved_chunk_bounds A c k W CR Hk)) as dR_41; dand4 dR_41 as B1 B2 B3 B4 | pose proof (carved_chunk_bounds A c k W CR Hk) as (B1 & B2 & B3 & B4) ]). pose proof (region_piece_bounds A c W CR) as RB. cbv zeta in RB.
        (first [ dand12 RB as R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12 | destruct RB as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12) ]).
        exists 0%nat, (p_b6 (a_pl A)), kSpaceReserve. split; [exact E0|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
        pose proof (primary_in_b6 A (chunk_addr (p_sb (a_pl A)) c k) W) as IB1.
        pose proof (primary_in_b6 A (chunk_addr (p_sb (a_pl A)) c k + class_size c - 1) W) as IB2.
        unfold a_b6, a_sb, kFreeArrayOffset, kRegionSize, kSpaceSize in *. pose proof (class_size_range c CR). unfold kMaxSize in *.
        split; [apply IB1; lia|]. enough (chunk_addr (p_sb (a_pl A)) c k + class_size c - 1 < p_b6 (a_pl A) + kSpaceReserve) by lia. apply IB2; lia.
      - (first [ dand3 C as N2 -> Hin | destruct C as (N2 & -> & Hin) ]). destruct (In_nth_error' _ _ Hin) as [i Hi].
        exists (15 + i)%nat, mb, (map_size n). split; [exact (bm_nth_sec A i _ Hi)|]. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia. }
    (first [ dex3 CH as i b s; dand7 CH as Hi N4 N5 N7 N8 LO HI | dand10 CH as i b s Hi N4 N5 N7 N8 LO HI | destruct CH as (i & b & s & Hi & N4 & N5 & N7 & N8 & LO & HI) ]).
    pose proof (bm_sep A i 5 _ _ _ _ W Hi E5 N5) as S5. pose proof (bm_sep A i 4 _ _ _ _ W Hi E4 N4) as S4.
    pose proof (bm_sep A i 7 _ _ _ _ W Hi E7 N7) as S7. pose proof (bm_sep A i 8 _ _ _ _ W Hi E8 N8) as S8.
    unfold apart. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia.
  Qed.

  (* [comment removed for export] *)
  Definition qc_first (qt : list batch) : Z := match qt with [] => 0 | b :: _ => batch_addr (a_sb A) b end.
  Definition qc_last (qt : list batch) : Z := match qt with [] => 0 | _ => batch_addr (a_sb A) (last qt (BA 0 [])) end.

  (* [comment removed for export] *)
  Lemma ro_u64x4 : forall (mm : mem) a v0 v1 v2 v3,
    u64_at rsegs mm a v0 -> u64_at rsegs mm (a + 8) v1 -> u64_at rsegs mm (a + 16) v2 -> u64_at rsegs mm (a + 24) v3 ->
    ro_cells rsegs mm a [C8 (wz v0); C8 (wz v1); C8 (wz v2); C8 (wz v3)].
  Proof.
    intros mm a v0 v1 v2 v3 X0 X1 X2 X3. split; [exact (conj I (conj I (conj I (conj I I))))|].
    cbn [cells_bytes cbytes]. rewrite app_nil_r.
    apply bytes_at_app. split; [exact X0|]. rewrite length_le8. replace (a + Z.of_nat 8) with (a + 8) by lia.
    apply bytes_at_app. split; [exact X1|]. rewrite length_le8. replace (a + 8 + Z.of_nat 8) with (a + 16) by lia.
    apply bytes_at_app. split; [exact X2|]. rewrite length_le8. replace (a + 16 + Z.of_nat 8) with (a + 24) by lia. exact X3.
  Qed.
  Lemma ro_u64x3 : forall (mm : mem) a v0 v1 v2,
    u64_at rsegs mm a v0 -> u64_at rsegs mm (a + 8) v1 -> u64_at rsegs mm (a + 16) v2 ->
    ro_cells rsegs mm a [C8 (wz v0); C8 (wz v1); C8 (wz v2)].
  Proof.
    intros mm a v0 v1 v2 X0 X1 X2. split; [exact (conj I (conj I (conj I I)))|].
    cbn [cells_bytes cbytes]. rewrite app_nil_r.
    apply bytes_at_app. split; [exact X0|]. rewrite length_le8. replace (a + Z.of_nat 8) with (a + 8) by lia.
    apply bytes_at_app. split; [exact X1|]. rewrite length_le8. replace (a + 8 + Z.of_nat 8) with (a + 16) by lia. exact X2.
  Qed.

  #[using="AI md DR"] Lemma free_QC : rw_cells rsegs v (p_thr (a_pl A) + 80)
      [C8 (wz (Z.of_nat (length (a_qthread A)))); C8 (wz (qc_first (a_qthread A))); C8 (wz (qc_last (a_qthread A))); C8 (wz (q_bytes (a_qthread A)))].
  Proof.
    (first [ pose proof ((ar_quar _ _ _ _ _ (ai_repr _ _ _ _ _ _ _ AI))) as dR_45; dand3 dR_45 as QT _ _ | destruct (ar_quar _ _ _ _ _ (ai_repr _ _ _ _ _ _ _ AI)) as (QT & _ & _) ]). (first [ dand5 QT as Q1 Q2 Q3 Q4 _ | destruct QT as (Q1 & Q2 & Q3 & Q4 & _) ]).
    change (p_sb (a_pl A)) with (a_sb A) in Q2, Q3. unfold off_th_qcache in *.
    (first [ pose proof ((ar_cache _ _ _ _ _ (ai_repr _ _ _ _ _ _ _ AI))) as dR_47; dand5 dR_47 as _ _ _ TM _ | destruct (ar_cache _ _ _ _ _ (ai_repr _ _ _ _ _ _ _ AI)) as (_ & _ & _ & TM & _) ]).
    apply ro_rw.
    2:{ cbn [cells_size csize Nat.add]. intros i Hi. replace (p_thr (a_pl A) + 80 + i) with (p_thr (a_pl A) + (80 + i)) by lia. apply TM. lia. }
    apply ro_u64x4.
    - replace (p_thr (a_pl A) + 80) with (p_thr (a_pl A) + 80 + 0) by lia. exact Q1.
    - unfold qc_first. exact Q2.
    - unfold qc_last. exact Q3.
    - exact Q4.
  Qed.

  (* [comment removed for export] *)
  #[using="W AI md DR"] Lemma free_LB : forall l b, a_qthread A = l ++ [b] ->
    let lb := batch_addr (a_sb A) b in let cnt := Z.of_nat (length (ba_entries b)) in
    rw_cells rsegs v lb [C8 (wz 0); C8 (wz (batch_bytes b)); C8 (wz cnt)] /\
    (cnt < kQuarantineBatchCount -> exists w : word, rw_cells rsegs v (lb + 24 + 8 * cnt) [C8 w]) /\
    mapped v lb kQuarantineBatchBytes /\ 1 <= cnt <= kQuarantineBatchCount /\
    kHighMemBeg <= lb /\ lb + kQuarantineBatchBytes <= alloc_ceiling /\ lb mod 16 = 0.   (* [comment removed for export] *)
  Proof.
    intros l b E. cbv zeta.
    (first [ pose proof ((ar_quar _ _ _ _ _ (ai_repr _ _ _ _ _ _ _ AI))) as dR_48; dand3 dR_48 as QT _ _ | destruct (ar_quar _ _ _ _ _ (ai_repr _ _ _ _ _ _ _ AI)) as (QT & _ & _) ]). (first [ dand5 QT as _ _ _ _ BR | destruct QT as (_ & _ & _ & _ & BR) ]).
    change (p_sb (a_pl A)) with (a_sb A) in BR. rewrite E in BR.
    (first [ pose proof ((batches_repr_last _ _ l b BR)) as dR_50; dand5 dR_50 as Hn Hs Hc He Hm | pose proof (batches_repr_last _ _ l b BR) as (Hn & Hs & Hc & He & Hm) ]). cbv zeta in Hn, Hs, Hc, He, Hm.
    unfold off_qb_next, off_qb_size, off_qb_count in *.
    destruct (wfQ A W) as (QW1 & _). rewrite E in QW1. apply Forall_app in QW1 as [_ QWb]. inversion QWb as [|? ? WB _]; subst.
    (first [ dand3 WB as CNT IDX _ | destruct WB as (CNT & IDX & _) ]).
    (first [ pose proof ((carved_chunk_bounds A kQuarantineBatchClass (ba_idx b) W ltac:(unfold kQuarantineBatchClass; lia) IDX)) as dR_52; dand4 dR_52 as B1 B2 B3 B4 | pose proof (carved_chunk_bounds A kQuarantineBatchClass (ba_idx b) W ltac:(unfold kQuarantineBatchClass; lia) IDX) as (B1 & B2 & B3 & B4) ]).
    pose proof (region_piece_bounds A kQuarantineBatchClass W ltac:(unfold kQuarantineBatchClass; lia)) as RB. cbv zeta in RB.
    (first [ dand12 RB as R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12 | destruct RB as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12) ]).
    (first [ pose proof ((sb_facts A W)) as dR_54; dand5 dR_54 as _ SBA HB6 RSB SCE | pose proof (sb_facts A W) as (_ & SBA & HB6 & RSB & SCE) ]). pose proof alloc_ceiling_val as HC.
    rewrite class_size_24 in *. unfold batch_addr, kQuarantineBatchBytes in *.
    split; [| split; [| split; [exact Hm| split; [exact CNT| ]]]].
    - apply ro_rw; [| cbn [cells_size csize Nat.add]; intros i Hi; apply Hm; lia].
      apply ro_u64x3; [replace (chunk_addr (a_sb A) kQuarantineBatchClass (ba_idx b)) with (chunk_addr (a_sb A) kQuarantineBatchClass (ba_idx b) + 0) at 1 by lia; exact Hn| exact Hs| exact Hc].
    - intros LT. apply mapped_C8; [| unfold kHighMemBeg, kFreeArrayOffset, kRegionSize, kSpaceSize in *; lia| unfold kQuarantineBatchCount, kFreeArrayOffset, kRegionSize, kSpaceSize in *; lia].
      intros i Hi. replace (chunk_addr (a_sb A) kQuarantineBatchClass (ba_idx b) + 24 + 8 * Z.of_nat (length (ba_entries b)) + i)
        with (chunk_addr (a_sb A) kQuarantineBatchClass (ba_idx b) + (24 + 8 * Z.of_nat (length (ba_entries b)) + i)) by lia.
      apply Hm. unfold kQuarantineBatchCount in *. lia.
    - unfold kHighMemBeg, kFreeArrayOffset, kRegionSize, kSpaceSize in *. split; [lia|]. split; [lia|].
      apply (mod0_down _ 32 16); [exists 2; reflexivity| exact B3].
  Qed.
End Live.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CacheLine.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {DR : DepotRep}.
  Variables (A : AState) (m : mem) (md : Model) (c : Z).
  Hypothesis AI : pa_ainv A m md.
  Hypothesis CR : 1 <= c <= 30.
  Let v := aview_of (pa_hull A) m.
  Let W : WF A. Proof. exact (ai_wf _ _ _ _ _ _ _ AI). Qed.
  Let P := a_pl A.
  (* [comment removed for export] *)
  Local Notation ks' := (pk_chunks (a_cache A c)).
  Local Notation cnt := (Z.of_nat (length ks')).
  Local Notation kidx := (nth (length ks' - 1) ks' 0).
  Hypothesis NE : ks' <> [].

  #[using="NE W CR AI c md m DR Clg"] Lemma cl_ci : a_cache_inited A = true.
  Proof.
    destruct (wfC A W) as (C1 & _). (first [ pose proof ((C1 c ltac:(lia))) as dR_55; dand4 dR_55 as _ _ _ CI | destruct (C1 c ltac:(lia)) as (_ & _ & _ & CI) ]). cbv zeta in CI.
    destruct (a_cache_inited A); [reflexivity|]. exfalso. apply NE. exact (CI eq_refl).
  Qed.
  #[using="NE W CR AI md m DR Clg"] Lemma cl_kidx : nth_error ks' (Z.to_nat (cnt - 1)) = Some kidx /\ In kidx ks' /\ 0 <= kidx < carved_count A c /\ 1 <= cnt <= 16 /\ NoDup ks'.
  Proof.
    destruct (wfC A W) as (C1 & _). (first [ pose proof ((C1 c ltac:(lia))) as dR_56; dand4 dR_56 as L1 ND B _ | destruct (C1 c ltac:(lia)) as (L1 & ND & B & _) ]). cbv zeta in L1, B, ND.
    pose proof (ar_cache _ _ _ _ _ (ai_repr _ _ _ _ _ _ _ AI)) as C. unfold cache_repr_ in C. cbv zeta in C. destruct C as (C & _).
    destruct (C c ltac:(lia)) as (L16 & _).
    assert (LP : (0 < length ks')%nat) by (destruct ks'; [exfalso; apply NE; reflexivity| cbn; lia]).
    assert (E : nth_error ks' (Z.to_nat (cnt - 1)) = Some kidx).
    { replace (Z.to_nat (Z.of_nat (length ks') - 1)) with (length ks' - 1)%nat by lia. apply nth_error_nth'. lia. }
    pose proof (nth_error_In _ _ E) as IN. split; [exact E|]. split; [exact IN|]. split; [exact (B _ IN)|]. split; [lia| exact ND].
  Qed.

  #[using="NE W CR AI md DR"] Lemma cl_PC : exists ks, length ks = 16%nat /\
    nth_error ks (Z.to_nat (cnt - 1)) = Some (Z_to_bv 64 (kidx * class_size c / kCompactPtrScale)) /\
    Forall (fun w => bv_unsigned w < 2^32) ks /\
    firstn (length ks') ks = map (fun k => Z_to_bv 64 (k * class_size c / kCompactPtrScale)) ks' /\
    rw_cells rsegs v (p_thr P + 208 + 80 * c) [C4 (Z_to_bv 64 cnt); C4 (Z_to_bv 64 (max_count c)); C8 (Z_to_bv 64 (class_size c)); CB 64 (u32s ks)].
  Proof.
    pose proof (class_size_range c CR) as CSR. (first [ dand5 cl_kidx as KE KIN KB CB16 _ | destruct cl_kidx as (KE & KIN & KB & CB16 & _) ]). pose proof cl_ci as CI.
    pose proof (ar_cache _ _ _ _ _ (ai_repr _ _ _ _ _ _ _ AI)) as C. unfold cache_repr_ in C. cbv zeta in C. (first [ dand5 C as C _ _ TM _ | destruct C as (C & _ & _ & TM & _) ]).
    (first [ pose proof ((C c ltac:(lia))) as dR_59; dand5 dR_59 as L16 Hcnt Hmax Hent Hjunk | destruct (C c ltac:(lia)) as (L16 & Hcnt & Hmax & Hent & Hjunk) ]). rewrite CI in Hmax. cbn [andb negb] in Hmax.
    destruct (Z.eqb_spec c 0); [lia|]. destruct Hmax as [Hmax Hsz]. (first [ dex1 Hjunk as jb; destruct Hjunk as [Ljb Bjb] | dand3 Hjunk as jb Ljb Bjb | destruct Hjunk as (jb & Ljb & Bjb) ]).
    pose proof (place_facts A W) as (Pthr & _). cbv zeta in Pthr. pose proof alloc_ceiling_val as CE.
    unfold off_th_per_class, off_th_alloc_cache, off_pc_count, off_pc_max_count, off_pc_class_size, off_pc_chunk, kPerClassSize in *.
    set (e := p_thr P + 208 + 80 * c). replace (p_thr (a_pl A) + (208 + 80 * c)) with e in * by (subst e P; lia).
    set (ks := map (fun k => Z_to_bv 64 (k * class_size c / kCompactPtrScale)) ks' ++ words4 jb (16 - length ks')).
    assert (SMALL : forall k, In k ks' -> 0 <= k * class_size c / kCompactPtrScale < 2^32).
    { intros k Hk. destruct (wfC A W) as (C1 & _). (first [ pose proof ((C1 c ltac:(lia))) as dR_61; dand4 dR_61 as _ _ B _ | destruct (C1 c ltac:(lia)) as (_ & _ & B & _) ]). cbv zeta in B. specialize (B k Hk).
      (first [ pose proof ((carved_chunk_bounds A c k W CR B)) as dR_62; dand3 dR_62 as B1 B2 _ | pose proof (carved_chunk_bounds A c k W CR B) as (B1 & B2 & _) ]). pose proof (region_piece_bounds A c W CR) as RB. cbv zeta in *.
      unfold chunk_addr, kCompactPtrScale, kFreeArrayOffset in *.
      split; [apply Z.div_pos; nia|]. apply Z.div_lt_upper_bound; [lia|]. nia. }
    exists ks. assert (LK : length ks = 16%nat).
    { subst ks. rewrite app_length, map_length, words4_length. lia. }
    split; [exact LK|]. split.
    { subst ks. rewrite nth_error_app1 by (rewrite map_length; lia). rewrite nth_error_map, KE. reflexivity. }
    split.
    { subst ks. apply Forall_app. split; [| apply words4_small]. apply Forall_forall. intros w Hw. apply in_map_iff in Hw as (k & <- & Hk).
      pose proof (SMALL k Hk). rewrite unsigned_lit by lia. lia. }
    split.
    { subst ks. rewrite firstn_app, map_length, Nat.sub_diag, firstn_O, app_nil_r. rewrite firstn_all2 by (rewrite map_length; lia). reflexivity. }
    apply ro_rw.
    - split; [cbn; rewrite u32s_length, LK; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; exact I || reflexivity|].
      cbn [cells_bytes cbytes]. rewrite app_nil_r.
      apply bytes_at_app. split; [rewrite Z.add_0_r in Hcnt; exact Hcnt|]. rewrite length_le4.
      apply bytes_at_app. split; [replace (e + Z.of_nat 4) with (e + 4) by lia; exact Hmax|]. rewrite length_le4.
      apply bytes_at_app. split; [replace (e + Z.of_nat 4 + Z.of_nat 4) with (e + 8) by lia; exact Hsz|]. rewrite length_le8.
      replace (e + Z.of_nat 4 + Z.of_nat 4 + Z.of_nat 8) with (e + 16) by lia.
      subst ks. rewrite u32s_app. apply bytes_at_app. split.
      + apply u32s_of_entries; [| | ].
        2:{ subst e P. pose proof (app_facts _ _ (proj1 Pthr)). lia. }
        2:{ subst e P. pose proof (app_facts _ _ (proj1 Pthr)). lia. }
        intros i k Hk. replace (e + 16 + 4 * Z.of_nat i) with (e + (16 + 4 * Z.of_nat i)) by lia. apply Hent. exact Hk.
      + rewrite u32s_length, map_length. rewrite u32s_words4 by lia.
        replace (e + 16 + Z.of_nat (4 * length ks')) with (e + (16 + 4 * Z.of_nat (length ks'))) by lia. exact Bjb.
    - cbn [cells_size csize Nat.add]. intros i Hi. subst e P. replace (p_thr (a_pl A) + 208 + 80 * c + i) with (p_thr (a_pl A) + (208 + 80 * c + i)) by lia.
      apply TM. lia.
  Qed.
End CacheLine.
