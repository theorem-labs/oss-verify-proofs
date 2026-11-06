(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.A10 Require Import ImageA.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.A10 Require Import Layout.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.A10 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit Lept_leaf LeptL_kit Gm_iface Fh_iface Fh_sel_iface Fh_statics Fh_selkit.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Lemma tr_selDestroy_1 : In [0xa7294] CLIENT_TRACES. Proof. apply ct_mem_In; vm_compute; reflexivity. Qed.
Lemma tr_selDestroy_2 : In [0xa72d4] CLIENT_TRACES. Proof. apply ct_mem_In; vm_compute; reflexivity. Qed.
Lemma tr_selDestroy_3 : In [0xa72f4] CLIENT_TRACES. Proof. apply ct_mem_In; vm_compute; reflexivity. Qed.
Lemma tr_selDestroy_4 : In [0xa72fc] CLIENT_TRACES. Proof. apply ct_mem_In; vm_compute; reflexivity. Qed.

Section SELD.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.

Theorem selDestroy_ok : selDestroy_cps RT.
Proof using AF GP.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo pp sel v nm q qn l1 l2
    FDO MST -> -> QINF QLO QHI PP8 PPC SO SHAPE POS ENV.
  unfold lpost_f, lenv, keeps, keepsL in *. destruct ENV as (LH & SSP & ART0 & MI & ST & LOW & LOR & SPT & SPA & SPB).
  destruct (af_client_consts RT AF Σ m ART0) as (G1 & G2 & G3 & G4).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  unfold entry_st, e_selDestroy, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (USP : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range).
  unfold LSTK, STDERR_STACK in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. unfold SHB in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  pose proof ST as (STa & STb & _).
  pose proof SO as (SB & NMB & (NIN & N0 & N16 & _) & NML).
  pose proof SB as (SC & (SIN & S0 & S16 & _) & HSY & HSX & HLEN & DC & (DIN & D0 & D16 & _) & ROWS & _).
  unfold sel_cells in SC.
  set (rows := s_rows v) in *. set (data := s_data v) in *. set (name := s_name v) in *. set (sy := s_sy v) in *. set (sx := s_sx v) in *.
  (* [comment removed for export] *)
  pose proof (live_nodup_seg RT AF Σ m (sel_live sel v) l1 l2 ART0 SHAPE ltac:(intros p n Hp; apply (POS p n); rewrite SHAPE; apply in_or_app; right; apply in_or_app; left; exact Hp)) as NDS.
  destruct (sel_live_nodup_facts sel v NDS) as (NDR & NDD & NDSL & NDN & NEDS & NEND & NENS).
  fold rows data name in NDR, NDD, NDSL, NDN, NEDS, NEND, NENS.
  apply live_remove_all_In in QINF. destruct QINF as (QIN & QNF). cbn [fst] in QNF. unfold sel_frees in QNF. fold rows data name in QNF.
  set (LVF := live_remove_all (sel_frees sel v) (rt_live RT Σ)) in *.
  set (PF := fun a => aclient LVF (rt_frames RT Σ) usp a /\ outside [(pp, pp + 8)] a).
  pose proof (agree_refl PF m) as AGF.
  assert (LVFS : forall e, In e LVF -> In e (rt_live RT Σ)) by (intros e He; apply live_remove_all_In in He; exact (proj1 He)).
  assert (PFS : forall a, PF a -> usp <= a \/ a < lo).
  { intros a [Ha _]. destruct (aclient_split RT AF Σ m usp a ART0) as [H|H]; [| left; exact H| right; unfold STACK_WIN in H; lia].
    apply (aclient_mono LVF (rt_frames RT Σ) usp _ _ usp a Ha); [exact LVFS| auto| lia]. }
  assert (PPLO : pp + 8 <= lo /\ 0 < q) by (pose proof (af_live_range RT AF Σ m q qn ART0 QIN) as (R0 & R & _); unfold STACK_WIN in R; lia).
  destruct PPLO as (PPLO & Q0).
  hide SHAPE.
  chunk_facts RT AF GP sel 32. chunk_facts RT AF GP q qn. chunk_facts RT AF GP data (8 * sy).
  (* [comment removed for export] *)
  assert (PPSEG : pp + 8 <= 65536 \/ 6578176 <= pp) by (lazymatch goal with H : q + qn <= 65536 \/ _ |- _ => clear - H QLO QHI; lia end).
  assert (PPSH : pp + 8 <= 2147446784 \/ 17594333495296 <= pp) by (lazymatch goal with H : q + qn <= 2147446784 \/ _ |- _ => clear - H QLO QHI; lia end).
  rewrite <- (map_map (Z_to_bv 64) C8) in DC. apply rw_cells_C8s_u64arr in DC.
  remember (map (Z_to_bv 64) rows) as ws eqn:EWS.
  assert (ULEN : Z.of_nat (length ws) = sy) by (rewrite EWS, length_map; exact HLEN).
  refresh RT AF. unfold SHB in *. park_disj.
  walk_to AF MST [(usp - 96, usp)] [0xa726c].
  sx32_fix. brF.
  awalk [0xa726c].
  cps_stop.
  art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I]).
  lazymatch goal with
  | AGFx : agree_on ?PFx _ ?mm, MUx : munch _ ?mm _ |- _ =>
      is_var PFx; agf_munch AGFx MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I])
  end.
  assert (INF : forall (X : Type) (l : list X) (n : nat) (x : X), In x (firstn n l) -> In x l).
  { clear. intros X l n x H. rewrite <- (firstn_skipn n l). apply in_or_app. left. exact H. }
  lazymatch goal with FRx : rw_cells asegs _ (usp + -96) ?frcs |- _ =>
  assert (LOOP : forall (k : nat) (i c6 : Z) (Σk : rts RT) (mc : mem)
                 (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32),
     Z.of_nat k = sy - i -> (1 <= k)%nat -> 0 <= i -> c6 = 8 * i ->
     hid (rt_live RT Σk = live_remove_all (firstn (Z.to_nat i) rows) (rt_live RT Σ)) ->
     rt_frames RT Σk = rt_frames RT Σ -> rt_sp0 RT Σk = rt_sp0 RT Σ -> rt_credit RT Σk = rt_credit RT Σ ->
     ART RT Σk mc -> mem_inv asegs mc -> stk asegs mc lo (usp + -96) -> LIBH mc -> io_ssp mc -> agree_on PF m mc ->
     rw_cells asegs mc (usp + -96) frcs ->
     rw_cells asegs mc sel [C4 (Z_to_bv 64 sy); C4 (Z_to_bv 64 sx); C4 (Z_to_bv 64 (s_cy v)); C4 (Z_to_bv 64 (s_cx v)); C8 (Z_to_bv 64 data); C8 (Z_to_bv 64 name)] ->
     u64arr asegs mc data ws -> rw_cells asegs mc pp [C8 (Z_to_bv 64 sel)] ->
     cps asegs (ASTA RT Σk PMc (eq (MS (mkR ra' (Z_to_bv 64 (usp + -96)) gp (Z_to_bv 64 D_defs.TP_A) t0' t1' t2' (Z_to_bv 64 pp) (Z_to_bv 64 sel)
          a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 (sel + 16)) (Z_to_bv 64 (pp / 8 + 2147450880)) (Z_to_bv 64 2147450880)
          (Z_to_bv 64 (sel / 8 + 2147450880)) (Z_to_bv 64 c6) (Z_to_bv 64 i) (Z_to_bv 64 ((sel + 16) / 8 + 2147450880))
          (Z_to_bv 64 (Z.land sel 7 + 3)) s10 s11 t3' t4' t5' t6') F' (Z_to_bv 64 0xa726c) fc' None mc (seg_rom asegs)))) QF) end.
  { clear AGF.
    repeat match goal with H : rw_cells asegs _ _ _ |- _ => clear H end.
    repeat match goal with H : ro_cells asegs _ _ _ |- _ => clear H end.
    repeat match goal with H : u64arr asegs _ _ _ |- _ => clear H end.
    repeat match goal with H : bytes_at asegs _ _ _ |- _ => clear H end.
    repeat match goal with H : munch _ _ _ |- _ => clear H end.
    repeat match goal with H : acc asegs _ _ _ |- _ => clear H end.
    repeat match goal with H : ART RT _ _ |- _ => lazymatch type of H with ART RT Σ m => fail | _ => clear H end end.
    repeat match goal with H : wmono asegs _ _ |- _ => clear H end.
    repeat match goal with H : mem_inv asegs _ |- _ => clear H end.
    repeat match goal with H : stk asegs _ _ _ |- _ => clear H end.
    repeat match goal with H : LIBH _ |- _ => clear H end.
    repeat match goal with H : io_ssp _ |- _ => clear H end.
    clear SO SB.
    induction k as [|k IH]; intros i c6 Σk mc ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc'
      HK HK1 HI -> LVK FRK SPK CRK ARTk MIk STk LHk SSPk AGFk FRc SELC DC PPC.
    { lia. }
    set (row := nth (Z.to_nat i) rows 0).
    assert (RIN0 : In row rows) by (apply nth_In; lia).
    pose proof (proj1 (Forall_forall _ _) ROWS row RIN0) as (RINL & R0 & R16 & _).
    assert (NER : row <> sel /\ row <> data /\ row <> name /\ row <> q).
    { repeat split; intros E; [apply NDSL| apply NDD| apply NDN| apply QNF; apply in_or_app; left]; rewrite <- E; exact RIN0. }
    destruct NER as (NERS & NERD & NERN & NERQ).
    assert (KEEP : forall x, In x (rt_live RT Σ) -> ~ In (fst x) (firstn (Z.to_nat i) rows) -> In x (rt_live RT Σk))
      by (intros x Hx Nx; unfold hid in LVK; rewrite LVK; apply live_remove_all_In; split; assumption).
    assert (INRk : In (row, 4 * sx) (rt_live RT Σk)) by (apply KEEP; [exact RINL| cbn [fst]; apply nodup_nth_notin_firstn; [exact NDR| lia]]).
    assert (INSk : In (sel, 32) (rt_live RT Σk)) by (apply KEEP; [exact SIN| cbn [fst]; intros H; apply NDSL; exact (INF _ _ _ _ H)]).
    assert (INDk : In (data, 8 * sy) (rt_live RT Σk)) by (apply KEEP; [exact DIN| cbn [fst]; intros H; apply NDD; exact (INF _ _ _ _ H)]).
    assert (INQk : In (q, qn) (rt_live RT Σk)) by (apply KEEP; [exact QIN| cbn [fst]; intros H; apply QNF; apply in_or_app; left; exact (INF _ _ _ _ H)]).
    assert (SUBk : forall e, In e LVF -> In e (rt_live RT Σk)).
    { intros e He. apply live_remove_all_In in He. destruct He as (He1 & He2). apply KEEP; [exact He1|].
      intros H. apply He2. unfold sel_frees. apply in_or_app. left. exact (INF _ _ _ _ H). }
    assert (NTH : nth_error ws (Z.to_nat i) = Some (Z_to_bv 64 row)) by (rewrite EWS; apply map_nth_error; unfold row; apply nth_error_nth'; lia).
    refresh RT AF. unfold SHB in *. park_disj.
    walk_to AF MST [(usp - 96, usp)] [0xa728c].

    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u64arr_read asegs mm data ws i (Z_to_bv 64 row) (Z_to_bv 64 (data + 8 * i)) DC NTH ltac:(lia)
                    ltac:(unfold wa; f_equal; lia)) as RD end.
    lstep. clear RD.
    awalk [e_free].
    hide PPC.
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
    eapply cps_seq.
    { pose proof (gp_free RT GP) as FREE; unfold free_contractC in FREE.
      eapply FREE with (lo := lo) (p := row) (n := 4 * sx); rt_side idtac.
      all: lazymatch goal with
           | |- In _ _ => exact INRk
           | |- call_ok _ _ _ _ _ => call_ok_tac
           | |- _ => idtac
           end.
      apply unwind_okC_of_ok; rewrite ?unsigned_lit by lia; [exact tr_selDestroy_1| left; ul]. }
    after_call RT AF.
    lazymatch goal with H : rt_live RT ?S = live_remove row _ |- _ => rename H into LVN; rename S into Σn end.
    assert (INSn : In (sel, 32) (rt_live RT Σn)) by (rewrite LVN; apply live_remove_keep; [exact INSk| cbn [fst]; congruence]).
    assert (INDn : In (data, 8 * sy) (rt_live RT Σn)) by (rewrite LVN; apply live_remove_keep; [exact INDk| cbn [fst]; congruence]).
    assert (INQn : In (q, qn) (rt_live RT Σn)) by (rewrite LVN; apply live_remove_keep; [exact INQk| cbn [fst]; congruence]).
    assert (SUBn : forall e, In e LVF -> In e (rt_live RT Σn)).
    { intros e He. rewrite LVN. apply live_remove_keep; [exact (SUBk e He)|]. apply live_remove_all_In in He. destruct He as (_ & He2).
      intros E. apply He2. unfold sel_frees. apply in_or_app. left. fold rows. rewrite E. exact RIN0. }
    lazymatch goal with AG : agree_on ?P2 mc ?m1 |- _ =>
      pose proof (u64arr_agree P2 mc m1 data ws DC AG ltac:(intros zz Hzz; right; right; left; exists data, (8 * sy); split; [exact INDn| lia])) as DC1;
      unfold hid in PPC;
      apply (rw_cells_agree_nw asegs mc m1 pp _) in PPC;
        [| eapply agree_sub; [exact AG|]; intros zz Hzz; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Hzz;
           right; right; left; exists q, qn; split; [exact INQn| lia]] end.
    clear DC.
    agf_call AGFk AG ltac:(fun Hx => destruct Hx as [Hx _]; apply (aclient_mono LVF _ usp _ _ _ _ Hx); [exact SUBn| intros e He; rewrite FRK; exact He| lia]).
    clear AG.
    assert (LVN' : hid (rt_live RT Σn = live_remove_all (firstn (Z.to_nat (i + 1)) rows) (rt_live RT Σ))).
    { unfold hid in *. rewrite LVN, LVK. replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
      rewrite (firstn_S_nth rows (Z.to_nat i) 0) by lia. rewrite live_remove_all_snoc. reflexivity. }
    clear INRk INSk INDk INQk SUBk KEEP.
    hide LVN.
    repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H in * end.
    unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *.
    refresh RT AF. unfold SHB in *. park_disj.
    walk_to AF MST [(usp - 96, usp); (pp, pp + 8)] [0xa7298].
    lstep. shbr8_zero.
    sx32_fix.
    awalk [0xa72a8].
    sx32_fix.
    destruct k as [|k'].
    2:{ (* [comment removed for export] *)
      lstep. brT.
      cps_stop.
      art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [| exact I]];
                          intros zz Hzz; right; right; left; exists q, qn; split; [exact INQn| lia]).
      lazymatch goal with
      | AGFx : agree_on ?PFx _ ?mm, MUx : munch _ ?mm _ |- _ =>
          is_var PFx; agf_munch AGFx MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct Hx as [_ Ho]; cbn [outside] in Ho; repeat split; first [lia| tauto])
      end.
      eapply (IH (i + 1)); try eassumption.
      - clear - HK; lia.
      - lia.
      - lia.
      - lia.
      - congruence.
      - congruence. }
    (* [comment removed for export] *)
    assert (ILAST : i + 1 = sy) by (clear - HK; lia).
    lstep. brF.
    awalk [e_free].
    assert (KEEPn : forall x, In x (rt_live RT Σ) -> ~ In (fst x) rows -> In x (rt_live RT Σn)).
    { intros x Hx Nx. unfold hid in LVN'. rewrite LVN'. apply live_remove_all_In. split; [exact Hx| intros H; apply Nx; exact (INF _ _ _ _ H)]. }
    assert (INNn : In (name, 8) (rt_live RT Σn)) by (apply KEEPn; [exact NIN| exact NDN]).
    hide PPC.
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [| exact I]];
                        intros zz Hzz; right; right; left; exists q, qn; split; [exact INQn| lia])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct Hx as [_ Ho]; cbn [outside] in Ho; repeat split; first [lia| tauto]).
    eapply cps_seq.
    { pose proof (gp_free RT GP) as FREE; unfold free_contractC in FREE.
      eapply FREE with (lo := lo) (p := data) (n := 8 * sy); rt_side idtac.
      all: lazymatch goal with
           | |- In _ _ => exact INDn
           | |- call_ok _ _ _ _ _ => call_ok_tac
           | |- _ => idtac
           end.
      apply unwind_okC_of_ok; rewrite ?unsigned_lit by lia; [exact tr_selDestroy_2| left; ul]. }
    clear DC1.
    after_call RT AF.
    lazymatch goal with H : rt_live RT ?S = live_remove data _ |- _ => rename H into LVD; rename S into Σd end.
    assert (INSd : In (sel, 32) (rt_live RT Σd)) by (rewrite LVD; apply live_remove_keep; [exact INSn| cbn [fst]; congruence]).
    assert (INNd : In (name, 8) (rt_live RT Σd)) by (rewrite LVD; apply live_remove_keep; [exact INNn| cbn [fst]; congruence]).
    assert (INQd : In (q, qn) (rt_live RT Σd)).
    { rewrite LVD; apply live_remove_keep; [exact INQn| cbn [fst]]. intros E. apply QNF. apply in_or_app. right. left. symmetry. exact E. }
    assert (SUBd : forall e, In e LVF -> In e (rt_live RT Σd)).
    { intros e He. rewrite LVD. apply live_remove_keep; [exact (SUBn e He)|]. apply live_remove_all_In in He. destruct He as (_ & He2).
      intros E. apply He2. unfold sel_frees. apply in_or_app. right. left. fold data. symmetry. exact E. }
    lazymatch goal with AG : agree_on ?P2 ?ma ?m1 |- _ =>
      unfold hid in PPC;
      apply (rw_cells_agree_nw asegs ma m1 pp _) in PPC;
        [| eapply agree_sub; [exact AG|]; intros zz Hzz; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Hzz;
           right; right; left; exists q, qn; split; [exact INQd| lia]] end.
    agf_call AGFk AG ltac:(fun Hx => destruct Hx as [Hx _]; apply (aclient_mono LVF _ usp _ _ _ _ Hx); [exact SUBd| intros e He; repeat match goal with H : rt_frames RT _ = _ |- _ => rewrite H end; exact He| lia]).
    clear AG INSn INDn INQn INNn SUBn KEEPn.
    hide LVD.
    repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H in * end.
    unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *.
    refresh RT AF. unfold SHB in *. park_disj.
    walk_to AF MST [(usp - 96, usp); (pp, pp + 8)] [e_free].
    lazymatch goal with A : ART RT Σd ?mm |- _ => pose proof (af_live_range RT AF Σd mm name 8 A INNd) as (_ & NMHI & _) end.
    repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H in NMHI end. unfold STACK_WIN in NMHI.
    brF.
    awalk [e_free].
    hide PPC.
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [| exact I]];
                        intros zz Hzz; right; right; left; exists q, qn; split; [exact INQd| lia])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct Hx as [_ Ho]; cbn [outside] in Ho; repeat split; first [lia| tauto]).
    eapply cps_seq.
    { pose proof (gp_free RT GP) as FREE; unfold free_contractC in FREE.
      eapply FREE with (lo := lo) (p := name) (n := 8); rt_side idtac.
      all: lazymatch goal with
           | |- In _ _ => exact INNd
           | |- call_ok _ _ _ _ _ => call_ok_tac
           | |- _ => idtac
           end.
      apply unwind_okC_of_ok; rewrite ?unsigned_lit by lia; [exact tr_selDestroy_3| left; ul]. }
    after_call RT AF.
    lazymatch goal with H : rt_live RT ?S = live_remove name _ |- _ => rename H into LVM; rename S into Σm end.
    assert (INSm : In (sel, 32) (rt_live RT Σm)) by (rewrite LVM; apply live_remove_keep; [exact INSd| cbn [fst]; congruence]).
    assert (INQm : In (q, qn) (rt_live RT Σm)).
    { rewrite LVM; apply live_remove_keep; [exact INQd| cbn [fst]]. intros E. apply QNF. apply in_or_app. right. right. left. symmetry. exact E. }
    assert (SUBm : forall e, In e LVF -> In e (rt_live RT Σm)).
    { intros e He. rewrite LVM. apply live_remove_keep; [exact (SUBd e He)|]. apply live_remove_all_In in He. destruct He as (_ & He2).
      intros E. apply He2. unfold sel_frees. apply in_or_app. right. right. left. fold name. symmetry. exact E. }
    lazymatch goal with AG : agree_on ?P2 ?ma ?m1 |- _ =>
      unfold hid in PPC;
      apply (rw_cells_agree_nw asegs ma m1 pp _) in PPC;
        [| eapply agree_sub; [exact AG|]; intros zz Hzz; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Hzz;
           right; right; left; exists q, qn; split; [exact INQm| lia]] end.
    agf_call AGFk AG ltac:(fun Hx => destruct Hx as [Hx _]; apply (aclient_mono LVF _ usp _ _ _ _ Hx); [exact SUBm| intros e He; repeat match goal with H : rt_frames RT _ = _ |- _ => rewrite H end; exact He| lia]).
    clear AG INSd INNd INQd SUBd NMHI.
    hide LVM.
    repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H in * end.
    unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *.
    refresh RT AF. unfold SHB in *. park_disj.
    walk_to AF MST [(usp - 96, usp); (pp, pp + 8)] [e_free].
    hide PPC.
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [| exact I]];
                        intros zz Hzz; right; right; left; exists q, qn; split; [exact INQm| lia])
                  ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct Hx as [_ Ho]; cbn [outside] in Ho; repeat split; first [lia| tauto]).
    eapply cps_seq.
    { pose proof (gp_free RT GP) as FREE; unfold free_contractC in FREE.
      eapply FREE with (lo := lo) (p := sel) (n := 32); rt_side idtac.
      all: lazymatch goal with
           | |- In _ _ => exact INSm
           | |- call_ok _ _ _ _ _ => call_ok_tac
           | |- _ => idtac
           end.
      apply unwind_okC_of_ok; rewrite ?unsigned_lit by lia; [exact tr_selDestroy_4| left; ul]. }
    repeat match goal with H : rw_cells asegs _ sel _ |- _ => clear H end.
    after_call RT AF.
    lazymatch goal with H : rt_live RT ?S = live_remove sel _ |- _ => rename H into LVS; rename S into Σs end.
    assert (INQs : In (q, qn) (rt_live RT Σs)).
    { rewrite LVS; apply live_remove_keep; [exact INQm| cbn [fst]]. intros E. apply QNF. apply in_or_app. right. right. right. left. symmetry. exact E. }
    assert (SUBs : forall e, In e LVF -> In e (rt_live RT Σs)).
    { intros e He. rewrite LVS. apply live_remove_keep; [exact (SUBm e He)|]. apply live_remove_all_In in He. destruct He as (_ & He2).
      intros E. apply He2. unfold sel_frees. apply in_or_app. right. right. right. left. symmetry. exact E. }
    lazymatch goal with AG : agree_on ?P2 ?ma ?m1 |- _ =>
      unfold hid in PPC;
      apply (rw_cells_agree_nw asegs ma m1 pp _) in PPC;
        [| eapply agree_sub; [exact AG|]; intros zz Hzz; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Hzz;
           right; right; left; exists q, qn; split; [exact INQs| lia]] end.
    agf_call AGFk AG ltac:(fun Hx => destruct Hx as [Hx _]; apply (aclient_mono LVF _ usp _ _ _ _ Hx); [exact SUBs| intros e He; repeat match goal with H : rt_frames RT _ = _ |- _ => rewrite H end; exact He| lia]).
    clear AG INSm.
    assert (LVFIN : rt_live RT Σs = LVF).
    { unfold hid in *. rewrite LVS, LVM, LVD, LVN'. unfold LVF, sel_frees. fold rows data name.
      replace (Z.to_nat (i + 1)) with (length rows) by lia. rewrite firstn_all. rewrite live_remove_all_app. reflexivity. }
    hide LVS. hide LVFIN.
    repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H in * end.
    unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *.
    refresh RT AF. unfold SHB in *. park_disj.
    walk_to AF MST [(usp - 96, usp); (pp, pp + 8)] (@nil Z).
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [| exact I]];
                        intros zz Hzz; right; right; left; exists q, qn; split; [exact INQs| lia]).
    lazymatch goal with
    | AGFx : agree_on ?PFx _ ?mm, MUx : munch _ ?mm _ |- _ =>
        is_var PFx; agf_munch AGFx MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct Hx as [_ Ho]; cbn [outside] in Ho; repeat split; first [lia| tauto])
    end.
    apply cps_finish; intros c Hc; subst QF; cbv beta. unfold hid in LVFIN.
    exists Σs. eexists.
    split; [| split; [exact LVFIN| split; [congruence| split; [congruence|]]]].
    2:{ repeat match goal with H : rt_credit RT _ = _ |- _ => rewrite H end. lia. }
    eapply (ASTA_conseq RT); [exact Hc|]; intros ms <-; eexists.
    split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
    split; [split; [split; [assumption| split; assumption]| split; assumption]|].
    split; [| assumption].
    intros a Ha Ho. apply AGFk. split; [| exact Ho]. rewrite LVFIN in Ha. exact Ha. }
  eapply (LOOP (Z.to_nat sy) 0 0); try eassumption.
  all: first [lia | reflexivity | idtac].
Qed.
End SELD.
