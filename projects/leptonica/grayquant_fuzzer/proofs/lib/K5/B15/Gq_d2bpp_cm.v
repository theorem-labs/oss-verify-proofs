(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import Tac RzCPS NodesA SysStep Arr StoreFast.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import ImageA Layout RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit D_iface D_defs D_libiface
  Lept_iface Lept_env LeptC_kit Lept_leaf Lept_chain Lept_objkit LeptL_kit Gm_iface Gm_kit Gm_livekit Gq_obj Gq_iface Gq_dbin_defs Gq_cmaplin Gq_d2bpp_cmdefs
  LeptB_guard LeptB_guard2.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac park_ne := repeat match goal with H : (?a <> ?b) |- _ => lazymatch type of a with Z => change (a <> b) with (parked (a <> b)) in H end end.

(* [comment removed for export] *)
Ltac carry AG H acl side :=
  unfold hid in H;
  lazymatch type of AG with agree_on _ ?ma ?mb => lazymatch type of H with rw_cells _ ma ?A ?cs =>
    apply (rw_cells_agree_nw asegs ma mb A cs) in H;
    [| eapply agree_sub; [exact AG|]; cbv beta; let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx;
       unfold pix_cells_rc, pix_cells, cmap_cells in Hx; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Hx;
       first [split; [acl x Hx| cbn [outside]; side Hx] | acl x Hx] ] end end.

(* [comment removed for export] *)
Definition D2CM_RAS : list Z := [RA_FUZZ_OP1; RA_TOP].
Lemma tr_d2cm_cml : In (RA_CMAPLIN_CALLOC1 :: D2CM_RAS) CLIENT_TRACES. Proof. apply ct_mem_In; vm_compute; reflexivity. Qed.
Lemma tr_d2cm_f1 : In (0xa0374 :: D2CM_RAS) CLIENT_TRACES. Proof. apply ct_mem_In; vm_compute; reflexivity. Qed.
Lemma tr_d2cm_f2 : In (0xa037c :: D2CM_RAS) CLIENT_TRACES. Proof. apply ct_mem_In; vm_compute; reflexivity. Qed.
Lemma tr_d2cm_f3 : In (0xa0384 :: D2CM_RAS) CLIENT_TRACES. Proof. apply ct_mem_In; vm_compute; reflexivity. Qed.
Lemma tr_d2cm_f4 : In (0xa038c :: D2CM_RAS) CLIENT_TRACES. Proof. apply ct_mem_In; vm_compute; reflexivity. Qed.
Lemma tr_d2cm_f5 : In (0xa0394 :: D2CM_RAS) CLIENT_TRACES. Proof. apply ct_mem_In; vm_compute; reflexivity. Qed.

(* [comment removed for export] *)
Lemma NoDup5 : forall a b c d e : Z, base.NoDup [a; b; c; d; e] ->
  a <> b /\ a <> c /\ a <> d /\ a <> e /\ b <> c /\ b <> d /\ b <> e /\ c <> d /\ c <> e /\ d <> e.
Proof.
  intros a b c d e H.
  apply list_relations.list.NoDup_cons in H. destruct H as [Ha H]. apply list_relations.list.NoDup_cons in H. destruct H as [Hb H].
  apply list_relations.list.NoDup_cons in H. destruct H as [Hc H]. apply list_relations.list.NoDup_cons in H. destruct H as [Hd _].
  apply list_basics.list.not_elem_of_cons in Ha. destruct Ha as [Hab Ha]. apply list_basics.list.not_elem_of_cons in Ha. destruct Ha as [Hac Ha].
  apply list_basics.list.not_elem_of_cons in Ha. destruct Ha as [Had Ha]. apply list_basics.list.not_elem_of_cons in Ha. destruct Ha as [Hae _].
  apply list_basics.list.not_elem_of_cons in Hb. destruct Hb as [Hbc Hb]. apply list_basics.list.not_elem_of_cons in Hb. destruct Hb as [Hbd Hb].
  apply list_basics.list.not_elem_of_cons in Hb. destruct Hb as [Hbe _].
  apply list_basics.list.not_elem_of_cons in Hc. destruct Hc as [Hcd Hc]. apply list_basics.list.not_elem_of_cons in Hc. destruct Hc as [Hce _].
  apply list_basics.list.not_elem_of_cons in Hd. destruct Hd as [Hde _].
  repeat split; assumption.
Qed.

(* [comment removed for export] *)
Ltac sigma_gc RT S0 Sx :=
  repeat match goal with S : rts RT |- _ =>
    tryif constr_eq S S0 then fail else tryif constr_eq S Sx then fail else
      (repeat match goal with H : context [S] |- _ => clear H end; clear S) end.

Section D2CM.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis CML : pixcmapCreateLinear24_cps RT.
Hypothesis SCM : pixSetColormap_cps RT.

(* [comment removed for export] *)
Lemma new_chunk_apart_mid : forall Σ' (m : mem) l1 p n live0 frs usp a,
  ART RT Σ' m -> rt_live RT Σ' = l1 ++ (p, n) :: live0 -> rt_frames RT Σ' = frs ->
  rt_sp0 RT Σ' - STACK_WIN <= usp ->
  aclient live0 frs usp a -> a < p \/ p + n <= a.
Proof using AF.
  intros Σ' m l1 p n live0 frs usp a HA LV FRS SPL Ha.
  assert (INL : In (p, n) (rt_live RT Σ')) by (rewrite LV; apply in_or_app; right; left; reflexivity).
  pose proof (af_live_range RT AF Σ' m p n HA INL) as (P0 & PHI & PSEG).
  unfold STACK_WIN, USTACK_TOP, SEGTOP_A in *.
  destruct Ha as [H|[H|[H|[H|H]]]].
  - right. lia.
  - pose proof (client_static_below a H) as HB. unfold SEGTOP_A in HB.
    destruct H as ((l & h & Hin & Hx) & _). unfold CLIENT_STATIC in Hin. cbn [In] in Hin.
    assert (X : 0x10000 <= a) by (repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
    lia.
  - destruct H as (p' & n' & Hin & Hp).
    assert (Hin' : In (p', n') (l1 ++ live0)) by (apply in_or_app; right; exact Hin).
    pose proof (af_live_disj RT AF Σ' m p n p' n' l1 live0 HA LV Hin') as D. lia.
  - destruct H as (f & k & Hin & Hf). rewrite <- FRS in Hin.
    pose proof (af_frames_range RT AF Σ' m f k HA Hin) as (_ & _ & _ & FLV). specialize (FLV p n INL). lia.
  - destruct H as (f & k & Hin & Hf). rewrite <- FRS in Hin.
    pose proof (af_fshadow_apart RT AF Σ' m f k HA Hin) as (SA1 & _). specialize (SA1 p n INL). lia.
Qed.

Theorem d2_cmfree_ok : d2_cmfree_cps RT.
Proof using AF GP CML SCM.
  intros Σ PMc m ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s10 s11 t3 t4 t5 t6 F fc sa usp lo fr pixd bufs1 bufs2 n1 tv t38 t14 fp1 s6v s7v vd L0 frs0
    FDO MST LV0 N1 FRS LVP0 FRESH5 ND LVB FRB CRB POD PDL0 DDL0 VCM VDATA FP1 UCX LOW LO0 LOR SA32 SAU USA SPA SPT SPB FR0 FR64 FRHI ART0 MI ST LH SSP UREC S32 S48 S112 FPD.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  destruct (af_client_consts RT AF Σ m ART0) as (G1 & G2 & G3 & G4).
  (* [comment removed for export] *)
  pose proof POD as (PXD & (PDIN & PD0 & PD16 & _) & HOKD & PDDATA & _).
  destruct PDDATA as [PDZ|((DDIN & DD0 & DD16 & DDN) & DDNE)]; [exfalso; exact (VDATA PDZ)|].
  set (dat := p_data vd) in *. set (rs := rsize vd) in *.
  unfold pix_cells in PXD. rewrite VCM in PXD.
  chunk_facts RT AF GP pixd 64. chunk_facts RT AF GP dat rs.
  hide POD. hide HOKD.
  unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
  unfold LSTK, STDERR_STACK in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. unfold SHB in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  (* [comment removed for export] *)
  assert (LVP : forall p n, In (p, n) (rt_live RT Σ) -> 0 < n).
  { intros p n Hp. rewrite LV0 in Hp. cbn [In] in Hp.
    destruct Hp as [E|[E|[E|[E|[E|Hp]]]]]; [injection E as <- <-; clear; lia| injection E as <- <-; clear; lia| injection E as <- <-; clear; lia
      | injection E as <- <-; exact N1| injection E as <- <-; exact N1| exact (LVP0 p n Hp)]. }
  destruct (NoDup5 _ _ _ _ _ ND) as (N12 & N1v & N18 & N14 & N2v & N28 & N24 & Nv8 & Nv4 & N84).
  (* [comment removed for export] *)
  assert (LSUB0 : forall e, In e L0 -> In e (rt_live RT Σ)) by (intros e He; rewrite LV0; do 5 right; exact He).
  set (PF := d2cm_keep L0 (rt_frames RT Σ) sa pixd).
  pose proof (agree_refl PF m) as AGF.
  assert (PFS : forall a, PF a -> sa <= a \/ a < lo).
  { intros a [Ha _]. assert (Ha' : aclient (rt_live RT Σ) (rt_frames RT Σ) sa a) by (apply (aclient_mono _ _ sa _ _ _ _ Ha); [exact LSUB0| intros e He; exact He| clear; lia]).
    destruct (aclient_split RT AF Σ m sa a ART0 Ha') as [H|H]; [left; exact H| right; unfold STACK_WIN in H; clear - H LOW; lia]. }
  assert (USP0 : 0 <= sa) by (clear - LOR LO0; lia). assert (USP1 : sa < 2^64) by (clear - SPB SAU SP0R; lia).
  assert (SA16 : sa mod 16 = 0) by (clear - SA32; Z.div_mod_to_equations; lia).
  assert (FP1h : hid (0 <= fp1 < 2^64)) by exact FP1. clear FP1.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  assert (PFU : forall a, usp + -16 <= a < 140737488355328 -> PF a).
  { intros a Ha. unfold PF, d2cm_keep. split; [left; unfold USTACK_TOP; clear - Ha SAU; lia|]. cbn [outside].
    lazymatch goal with H : pixd + 64 <= rt_sp0 RT Σ - _ |- _ => clear - Ha SAU H LOW LOR; lia end. }
  clear_acc. refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj. park_ne.
  idtac "MARK cm: setup".
  (* [comment removed for export] *)
  walk_to AF MST (@nil (Z * Z)) [e_pixcmapCreateLinear].
  idtac "MARK cm: at cmaplin".
  at_call RT AF ltac:(cbn [ivls_client]; exact I) ltac:(fun Hx => cbn [outside]; exact I).
  lazymatch goal with UR : rw_cells asegs ?mc (usp + -16) _ |- cps _ (ASTA RT _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
    assert (UCC : chain_ok mc sa usp D2CM_RAS)
      by (apply (chain_ok_push mc sa usp RA_FUZZ_OP1 fp1 [RA_TOP]);
          [ clear - SAU; lia | clear - SPA; Z.div_mod_to_equations; lia | unfold USTACK_TOP; clear - SPT; lia | unfold RA_FUZZ_OP1; clear; lia
          | let X := fresh "X" in pose proof FP1h as X; unfold hid in X; exact X | exact UR
          | apply (chain_ok_keep [RA_TOP] m _ usp fp1 UCX); eapply agree_sub; [exact AGF|]; cbv beta; intros zx Hzx; apply PFU; unfold USTACK_TOP in Hzx; clear - Hzx; lia ]) end.
  eapply cps_seq.
  { eapply CML with (lo := lo) (ras := D2CM_RAS).
    all: lazymatch goal with
         | |- fdfs_only _ => exact FDO
         | |- mat_stable _ => exact MST
         | |- uctx _ _ _ _ => unfold uctx; rewrite !unsigned_lit by (clear - USP0 USP1 SAU SPT; lia); exact UCC
         | |- In _ CLIENT_TRACES => exact tr_d2cm_cml
         | |- lenv _ _ _ _ _ _ => lenv_tac
         | |- lres _ _ _ _ _ => unfold lres; split; [clear - FRB; lia| split; [clear - LVB; unfold LIVE_MAX in *; lia| split; [clear - CRB; lia| exact LVP]]]
         | |- _ => first [reflexivity | lazymatch goal with |- ?g => idtac "CML SIDE LEFT:" g end]
         end. }
  idtac "MARK cm: cmaplin applied".
  clear UCC.
  hide PXD. hide UREC. hide S112. hide FPD. clear S32 S48.
  after_call RT AF.
  idtac "MARK cm: after cmaplin".
  lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ => rename S into Σc; rename A into ARTC; rename mm into mc end.
  lazymatch goal with H : rt_live RT Σc = (?ca, 16) :: (?cm, 24) :: rt_live RT Σ |- _ => rename H into LVc; rename ca into carr; rename cm into cmap end.
  lazymatch goal with H : rt_frames RT Σc = rt_frames RT Σ |- _ => rename H into FRSc end.
  lazymatch goal with H : rt_credit RT Σ <= rt_credit RT Σc |- _ => rename H into CRc end.
  lazymatch goal with H : cmap_obj _ mc cmap _ |- _ => rename H into CMO end.
  lazymatch goal with H : rw_cells asegs mc carr cmaplin24_cells |- _ => clear H end.
  pose proof CMO as ((cpad & CMC) & (CMIN & CM0 & CM16 & _) & (CAIN & CA0 & CA16 & _) & COK & CANE).
  unfold cmap_cells in CMC. cbn [c_arr c_depth c_nalloc c_n] in CMC, CAIN, CA0, CA16, CANE. hide CMC.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  lazymatch goal with AGx : agree_on _ m mc |- _ =>
    carry AGx PXD ltac:(fun x Hx => right; right; left; exists pixd, 64; split; [exact PDIN| exact Hx]) ltac:(fun Hx => exact I);
    carry AGx UREC ltac:(fun x Hx => left; unfold USTACK_TOP; clear - Hx SAU SPT; lia) ltac:(fun Hx => exact I);
    carry AGx S112 ltac:(fun x Hx => left; unfold USTACK_TOP; clear - Hx SAU SPT; lia) ltac:(fun Hx => exact I);
    carry AGx FPD ltac:(fun x Hx => right; right; right; left; exists fr, 2%nat; split; [rewrite FRS; left; reflexivity| change (fs_size 2%nat) with 256; clear - Hx; lia]) ltac:(fun Hx => exact I) end.
  hide PXD. hide UREC. hide S112.
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ sa _ _ _ _ (proj1 Hx)); [exact LSUB0| intros e He; exact He| clear; lia]| exact I]).
  idtac "MARK cm: carried c".
  (* [comment removed for export] *)
  assert (FZ : forall e, In e (rt_live RT Σ) -> fst e <> cmap /\ fst e <> carr).
  { intros e He. assert (Hk : 0 < snd e) by (destruct e as [q k]; exact (LVP q k He)). split.
    - apply (fresh_chunk_ne RT AF Σc mc [(carr, 16)] cmap 24 (rt_live RT Σ) e ARTC); [rewrite LVc; reflexivity| cbn [app]; right; exact He| clear; lia| exact Hk].
    - apply (fresh_chunk_ne RT AF Σc mc [] carr 16 ((cmap, 24) :: rt_live RT Σ) e ARTC); [rewrite LVc; reflexivity| cbn [app]; right; exact He| clear; lia| exact Hk]. }
  assert (NCX : forall a, aclient (rt_live RT Σ) (rt_frames RT Σ) sa a -> (a < cmap \/ cmap + 24 <= a) /\ (a < carr \/ carr + 16 <= a)).
  { intros a Ha. split.
    - apply (new_chunk_apart_mid Σc mc [(carr, 16)] cmap 24 (rt_live RT Σ) (rt_frames RT Σ) sa a ARTC); [rewrite LVc; reflexivity| exact FRSc| repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; clear - LOW LOR; unfold STACK_WIN; lia| exact Ha].
    - apply (new_chunk_apart_mid Σc mc [] carr 16 ((cmap, 24) :: rt_live RT Σ) (rt_frames RT Σ) sa a ARTC); [rewrite LVc; reflexivity| exact FRSc| repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; clear - LOW LOR; unfold STACK_WIN; lia|].
      apply (aclient_mono _ _ sa _ _ _ _ Ha); [intros e He; right; exact He| intros e He; exact He| clear; lia]. }
  assert (LSUBc : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σc)) by (intros e He; rewrite LVc; right; right; exact He).
  destruct (FZ _ PDIN) as [NCMP NCAP]. destruct (FZ _ DDIN) as [NCMD NCAD]. cbn [fst] in NCMP, NCAP, NCMD, NCAD.
  repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H in * end.
  clear_acc. refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj. park_ne.
  idtac "MARK cm: names c".
  (* [comment removed for export] *)
  unfold hid in FPD.
  walk_to AF MST (@nil (Z * Z)) [e_pixSetColormap].
  idtac "MARK cm: at setcmap".
  at_call RT AF ltac:(cbn [ivls_client]; exact I) ltac:(fun Hx => cbn [outside]; exact I).
  unfold hid in PXD.
  lazymatch goal with PX : rw_cells asegs ?mx pixd _ |- cps _ (ASTA RT Σc _ (eq (MS _ _ _ _ _ ?mx _))) _ =>
    assert (POD3 : pix_obj (rt_live RT Σc) mx pixd vd (mkCmapv carr 2 4 4))
      by (unfold hid in POD, HOKD; destruct POD as (_ & CH & _ & _ & _);
          split; [unfold pix_cells; rewrite VCM; exact PX|]; split; [exact (chunk_mono _ _ _ _ LSUBc CH)|]; split; [exact HOKD|];
          split; [right; split; [refine (chunk_mono _ _ _ _ LSUBc _); split; [exact DDIN| split; [exact DD0| split; [exact DD16| exact DDN]]]| unpark DDNE; exact DDNE]| left; exact VCM]) end.
  eapply cps_seq.
  { pose proof SCM as SC; unfold pixSetColormap_cps in SC.
    eapply SC with (lo := lo) (pix := pixd) (cmap := cmap) (v := vd) (cv := mkCmapv carr 2 4 4).
    all: lazymatch goal with
         | |- fdfs_only _ => exact FDO
         | |- mat_stable _ => exact MST
         | |- pix_obj _ _ _ _ _ => exact POD3
         | |- cmap_obj _ _ _ _ => exact CMO
         | |- p_cmap _ = 0 => exact VCM
         | |- p_data _ <> 0 => exact VDATA
         | |- lenv _ _ _ _ _ _ => lenv_tac
         | |- lres _ _ _ _ _ => unfold lres; rewrite FRSc; split; [clear - FRB; lia| split; [rewrite LVc; cbn [length]; clear - LVB; unfold LIVE_MAX in *; lia| split; [clear - CRB CRc; lia|
                                  intros p n Hp; rewrite LVc in Hp; cbn [In] in Hp; destruct Hp as [E|[E|Hp]]; [injection E as <- <-; clear; lia| injection E as <- <-; clear; lia| exact (LVP p n Hp)]]]]
         | |- _ => first [ reflexivity
                         | unpark NCMP; clear - NCMP; congruence | cbn [c_arr]; unpark NCAP; clear - NCAP; congruence
                         | unpark NCMD; clear - NCMD; unfold dat in *; congruence | cbn [c_arr]; unpark NCAD; clear - NCAD; unfold dat in *; congruence
                         | lazymatch goal with |- ?g => idtac "SCM SIDE LEFT:" g end ]
         end. }
  idtac "MARK cm: setcmap applied".
  clear POD3 FPD.
  hide UREC. hide S112.
  after_call RT AF.
  idtac "MARK cm: after setcmap".
  lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ => rename S into Σs; rename A into ARTS; rename mm into ms end.
  lazymatch goal with H : rw_cells asegs ms pixd (pix_cells _) |- _ => rename H into PXD end.
  assert (LVs : rt_live RT Σs = (carr, 16) :: (cmap, 24) :: (t14, 1024) :: (t38, 1024) :: (tv, 1024) :: (bufs2, n1) :: (bufs1, n1) :: L0)
    by (repeat match goal with E : rt_live RT Σs = _ |- _ => rewrite E end; rewrite LVc, LV0; reflexivity).
  assert (FRSs : rt_frames RT Σs = rt_frames RT Σ) by (repeat match goal with E : rt_frames RT Σs = _ |- _ => rewrite E end; exact FRSc).
  assert (SP0s : rt_sp0 RT Σs = rt_sp0 RT Σ) by (repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; reflexivity).
  assert (CRs : rt_credit RT Σ - 6 <= rt_credit RT Σs) by (lazymatch goal with E : rt_credit RT Σc - 6 <= rt_credit RT Σs |- _ => clear - E CRc; lia end).
  assert (LSUBs : forall e, In e L0 -> In e (rt_live RT Σs)) by (intros e He; rewrite LVs; do 7 right; exact He).
  (* [comment removed for export] *)
  lazymatch goal with AGx : agree_on _ mc ms |- _ =>
    carry AGx UREC ltac:(fun x Hx => left; unfold USTACK_TOP; clear - Hx SAU SPT; lia) ltac:(fun Hx => lazymatch goal with H : pixd + 64 <= rt_sp0 RT Σ - _ |- _ => clear - Hx SAU H LOW LOR; lia end);
    carry AGx S112 ltac:(fun x Hx => left; unfold USTACK_TOP; clear - Hx SAU SPT; lia) ltac:(fun Hx => lazymatch goal with H : pixd + 64 <= rt_sp0 RT Σ - _ |- _ => clear - Hx SAU H LOW LOR; lia end);
    (* [comment removed for export] *)
    carry AGx CMC ltac:(fun x Hx => right; right; left; exists cmap, 24; split; [rewrite LVs; right; left; reflexivity| exact Hx])
                  ltac:(fun Hx => split; [intros Hr; destruct (NCX x ltac:(right; right; left; exists pixd, 64; split; [exact PDIN| clear - Hr; lia])) as [X _]; clear - X Hx; lia| exact I]) end.
  hide UREC. hide S112. hide PXD. hide CMC.
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono _ _ sa _ _ _ _ (proj1 Hx)); [exact LSUBs| intros e He; rewrite FRSc; exact He| clear; lia]| exact (proj2 Hx)]).
  sigma_gc RT Σ Σs.
  try clear CMO. try clear CMIN. try clear CAIN.
  repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H in * end.
  clear_acc. refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj. park_ne.
  idtac "MARK cm: names s".
  (* [comment removed for export] *)
  walk_to AF MST (@nil (Z * Z)) [e_free].
  at_call RT AF ltac:(cbn [ivls_client]; exact I) ltac:(fun Hx => cbn [outside]; exact I).
  unfold hid in UREC.
  lazymatch goal with |- cps _ (ASTA RT _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
    assert (UCC : chain_ok mc sa usp D2CM_RAS)
      by (apply (chain_ok_push mc sa usp RA_FUZZ_OP1 fp1 [RA_TOP]);
          [ clear - SAU; lia | clear - SPA; Z.div_mod_to_equations; lia | unfold USTACK_TOP; clear - SPT; lia | unfold RA_FUZZ_OP1; clear; lia
          | let X := fresh "X" in pose proof FP1h as X; unfold hid in X; exact X | exact UREC
          | apply (chain_ok_keep [RA_TOP] m _ usp fp1 UCX); eapply agree_sub; [exact AGF|]; cbv beta; intros zx Hzx; apply PFU; unfold USTACK_TOP in Hzx; clear - Hzx; lia ]) end.
  hide UREC. hide S112.
  eapply cps_seq.
  { pose proof (gp_free RT GP) as FC; unfold free_contractC in FC; eapply FC with (lo := lo) (p := bufs1) (n := n1); rt_side idtac.
    all: lazymatch goal with
         | |- In _ _ => rewrite LVs; right; right; right; right; right; right; left; reflexivity
         | |- unwind_okC _ _ _ _ => exists D2CM_RAS; rewrite ?unsigned_lit by (clear - USP0 USP1 SAU SPT; lia); split; [exact UCC| exact tr_d2cm_f1]
         | |- ?g => idtac "FREE SIDE LEFT:" g
         end. }
  idtac "MARK cm: free 1 applied".
  clear UCC.
  after_call RT AF.
  lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ => rename S into Σf1; rename A into ARTF1; rename mm into mf1 end.
  assert (LVf1 : rt_live RT Σf1 = (carr, 16) :: (cmap, 24) :: (t14, 1024) :: (t38, 1024) :: (tv, 1024) :: (bufs2, n1) :: L0).
  { repeat match goal with E : rt_live RT Σf1 = _ |- _ => rewrite E end. rewrite LVs.
    rewrite (live_remove_other bufs1 carr 16) by (exact (not_eq_sym (proj2 (FZ (bufs1, n1) ltac:(rewrite LV0; right; right; right; right; left; reflexivity))))).
    rewrite (live_remove_other bufs1 cmap 24) by (exact (not_eq_sym (proj1 (FZ (bufs1, n1) ltac:(rewrite LV0; right; right; right; right; left; reflexivity))))).
    rewrite (live_remove_other bufs1 t14 1024) by (unpark N14; exact (not_eq_sym N14)).
    rewrite (live_remove_other bufs1 t38 1024) by (unpark N18; exact (not_eq_sym N18)).
    rewrite (live_remove_other bufs1 tv 1024) by (unpark N1v; exact (not_eq_sym N1v)).
    rewrite (live_remove_other bufs1 bufs2 n1) by (unpark N12; exact (not_eq_sym N12)).
    rewrite live_remove_hd; [reflexivity|]. intros e He. exact (proj1 (FRESH5 e He)). }
  assert (FRSf1 : rt_frames RT Σf1 = rt_frames RT Σ) by (repeat match goal with E : rt_frames RT Σf1 = _ |- _ => rewrite E end; exact FRSs).
  assert (SP0f1 : rt_sp0 RT Σf1 = rt_sp0 RT Σ) by (repeat match goal with E : rt_sp0 RT Σf1 = _ |- _ => rewrite E end; first [reflexivity | exact SP0s]).
  assert (CRf1 : rt_credit RT Σ - 6 <= rt_credit RT Σf1) by (repeat match goal with E : rt_credit RT Σf1 = _ |- _ => rewrite E end; exact CRs).
  assert (LSUBf1 : forall e, In e L0 -> In e (rt_live RT Σf1)) by (intros e He; rewrite LVf1; right; right; right; right; right; right; exact He).
  lazymatch goal with AGx : agree_on _ _ mf1 |- _ =>
    carry AGx PXD ltac:(fun x Hx => right; right; left; exists pixd, 64; split; [apply LSUBf1; exact PDL0| exact Hx]) ltac:(fun Hx => exact I);
    carry AGx UREC ltac:(fun x Hx => left; unfold USTACK_TOP; clear - Hx SAU SPT; lia) ltac:(fun Hx => exact I);
    carry AGx CMC ltac:(fun x Hx => right; right; left; exists cmap, 24; split; [rewrite LVf1; right; left; reflexivity| exact Hx]) ltac:(fun Hx => exact I);
    carry AGx S112 ltac:(fun x Hx => left; unfold USTACK_TOP; clear - Hx SAU SPT; lia) ltac:(fun Hx => exact I) end.
  hide PXD. hide UREC. hide CMC. hide S112.
  fold_ag ltac:(fun Hx => apply (aclient_mono _ _ sa _ _ _ _ (proj1 Hx)); [exact LSUBf1| intros e He; rewrite FRSs; exact He| clear; lia]).
  sigma_gc RT Σ Σf1.
  repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H in * end.
  clear_acc. refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj. park_ne.
  idtac "MARK cm: after free 1".
  (* [comment removed for export] *)
  walk_to AF MST (@nil (Z * Z)) [e_free].
  at_call RT AF ltac:(cbn [ivls_client]; exact I) ltac:(fun Hx => cbn [outside]; exact I).
  unfold hid in UREC.
  lazymatch goal with |- cps _ (ASTA RT _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
    assert (UCC : chain_ok mc sa usp D2CM_RAS)
      by (apply (chain_ok_push mc sa usp RA_FUZZ_OP1 fp1 [RA_TOP]);
          [ clear - SAU; lia | clear - SPA; Z.div_mod_to_equations; lia | unfold USTACK_TOP; clear - SPT; lia | unfold RA_FUZZ_OP1; clear; lia
          | let X := fresh "X" in pose proof FP1h as X; unfold hid in X; exact X | exact UREC
          | apply (chain_ok_keep [RA_TOP] m _ usp fp1 UCX); eapply agree_sub; [exact AGF|]; cbv beta; intros zx Hzx; apply PFU; unfold USTACK_TOP in Hzx; clear - Hzx; lia ]) end.
  hide UREC. hide S112.
  eapply cps_seq.
  { pose proof (gp_free RT GP) as FC; unfold free_contractC in FC; eapply FC with (lo := lo) (p := bufs2) (n := n1); rt_side idtac.
    all: lazymatch goal with
         | |- In _ _ => rewrite LVf1; right; right; right; right; right; left; reflexivity
         | |- unwind_okC _ _ _ _ => exists D2CM_RAS; rewrite ?unsigned_lit by (clear - USP0 USP1 SAU SPT; lia); split; [exact UCC| exact tr_d2cm_f2]
         | |- ?g => idtac "FREE SIDE LEFT:" g
         end. }
  idtac "MARK cm: free 2 applied".
  clear UCC.
  after_call RT AF.
  lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ => rename S into Σf2; rename A into ARTF2; rename mm into mf2 end.
  assert (LVf2 : rt_live RT Σf2 = (carr, 16) :: (cmap, 24) :: (t14, 1024) :: (t38, 1024) :: (tv, 1024) :: L0).
  { repeat match goal with E : rt_live RT Σf2 = _ |- _ => rewrite E end. rewrite LVf1.
    rewrite (live_remove_other bufs2 carr 16) by (exact (not_eq_sym (proj2 (FZ (bufs2, n1) ltac:(rewrite LV0; right; right; right; left; reflexivity))))).
    rewrite (live_remove_other bufs2 cmap 24) by (exact (not_eq_sym (proj1 (FZ (bufs2, n1) ltac:(rewrite LV0; right; right; right; left; reflexivity))))).
    rewrite (live_remove_other bufs2 t14 1024) by (unpark N24; exact (not_eq_sym N24)).
    rewrite (live_remove_other bufs2 t38 1024) by (unpark N28; exact (not_eq_sym N28)).
    rewrite (live_remove_other bufs2 tv 1024) by (unpark N2v; exact (not_eq_sym N2v)).
    rewrite live_remove_hd; [reflexivity|]. intros e He. exact (proj1 (proj2 (FRESH5 e He))). }
  assert (FRSf2 : rt_frames RT Σf2 = rt_frames RT Σ) by (repeat match goal with E : rt_frames RT Σf2 = _ |- _ => rewrite E end; exact FRSf1).
  assert (SP0f2 : rt_sp0 RT Σf2 = rt_sp0 RT Σ) by (repeat match goal with E : rt_sp0 RT Σf2 = _ |- _ => rewrite E end; first [reflexivity | exact SP0f1]).
  assert (CRf2 : rt_credit RT Σ - 6 <= rt_credit RT Σf2) by (repeat match goal with E : rt_credit RT Σf2 = _ |- _ => rewrite E end; exact CRf1).
  assert (LSUBf2 : forall e, In e L0 -> In e (rt_live RT Σf2)) by (intros e He; rewrite LVf2; right; right; right; right; right; exact He).
  lazymatch goal with AGx : agree_on _ _ mf2 |- _ =>
    carry AGx PXD ltac:(fun x Hx => right; right; left; exists pixd, 64; split; [apply LSUBf2; exact PDL0| exact Hx]) ltac:(fun Hx => exact I);
    carry AGx UREC ltac:(fun x Hx => left; unfold USTACK_TOP; clear - Hx SAU SPT; lia) ltac:(fun Hx => exact I);
    carry AGx CMC ltac:(fun x Hx => right; right; left; exists cmap, 24; split; [rewrite LVf2; right; left; reflexivity| exact Hx]) ltac:(fun Hx => exact I);
    carry AGx S112 ltac:(fun x Hx => left; unfold USTACK_TOP; clear - Hx SAU SPT; lia) ltac:(fun Hx => exact I) end.
  hide PXD. hide UREC. hide CMC. hide S112.
  fold_ag ltac:(fun Hx => apply (aclient_mono _ _ sa _ _ _ _ (proj1 Hx)); [exact LSUBf2| intros e He; rewrite FRSf1; exact He| clear; lia]).
  sigma_gc RT Σ Σf2.
  repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H in * end.
  clear_acc. refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj. park_ne.
  idtac "MARK cm: after free 2".
  (* [comment removed for export] *)
  unfold hid in S112.
  walk_to AF MST (@nil (Z * Z)) [e_free].
  at_call RT AF ltac:(cbn [ivls_client]; exact I) ltac:(fun Hx => cbn [outside]; exact I).
  unfold hid in UREC.
  lazymatch goal with |- cps _ (ASTA RT _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
    assert (UCC : chain_ok mc sa usp D2CM_RAS)
      by (apply (chain_ok_push mc sa usp RA_FUZZ_OP1 fp1 [RA_TOP]);
          [ clear - SAU; lia | clear - SPA; Z.div_mod_to_equations; lia | unfold USTACK_TOP; clear - SPT; lia | unfold RA_FUZZ_OP1; clear; lia
          | let X := fresh "X" in pose proof FP1h as X; unfold hid in X; exact X | exact UREC
          | apply (chain_ok_keep [RA_TOP] m _ usp fp1 UCX); eapply agree_sub; [exact AGF|]; cbv beta; intros zx Hzx; apply PFU; unfold USTACK_TOP in Hzx; clear - Hzx; lia ]) end.
  hide UREC. hide S112.
  eapply cps_seq.
  { pose proof (gp_free RT GP) as FC; unfold free_contractC in FC; eapply FC with (lo := lo) (p := tv) (n := 1024); rt_side idtac.
    all: lazymatch goal with
         | |- In _ _ => rewrite LVf2; right; right; right; right; left; reflexivity
         | |- unwind_okC _ _ _ _ => exists D2CM_RAS; rewrite ?unsigned_lit by (clear - USP0 USP1 SAU SPT; lia); split; [exact UCC| exact tr_d2cm_f3]
         | |- ?g => idtac "FREE SIDE LEFT:" g
         end. }
  idtac "MARK cm: free 3 applied".
  clear UCC.
  after_call RT AF.
  lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ => rename S into Σf3; rename A into ARTF3; rename mm into mf3 end.
  assert (LVf3 : rt_live RT Σf3 = (carr, 16) :: (cmap, 24) :: (t14, 1024) :: (t38, 1024) :: L0).
  { repeat match goal with E : rt_live RT Σf3 = _ |- _ => rewrite E end. rewrite LVf2.
    rewrite (live_remove_other tv carr 16) by (exact (not_eq_sym (proj2 (FZ (tv, 1024) ltac:(rewrite LV0; right; right; left; reflexivity))))).
    rewrite (live_remove_other tv cmap 24) by (exact (not_eq_sym (proj1 (FZ (tv, 1024) ltac:(rewrite LV0; right; right; left; reflexivity))))).
    rewrite (live_remove_other tv t14 1024) by (unpark Nv4; exact (not_eq_sym Nv4)).
    rewrite (live_remove_other tv t38 1024) by (unpark Nv8; exact (not_eq_sym Nv8)).
    rewrite live_remove_hd; [reflexivity|]. intros e He. exact (proj1 (proj2 (proj2 (FRESH5 e He)))). }
  assert (FRSf3 : rt_frames RT Σf3 = rt_frames RT Σ) by (repeat match goal with E : rt_frames RT Σf3 = _ |- _ => rewrite E end; exact FRSf2).
  assert (SP0f3 : rt_sp0 RT Σf3 = rt_sp0 RT Σ) by (repeat match goal with E : rt_sp0 RT Σf3 = _ |- _ => rewrite E end; first [reflexivity | exact SP0f2]).
  assert (CRf3 : rt_credit RT Σ - 6 <= rt_credit RT Σf3) by (repeat match goal with E : rt_credit RT Σf3 = _ |- _ => rewrite E end; exact CRf2).
  assert (LSUBf3 : forall e, In e L0 -> In e (rt_live RT Σf3)) by (intros e He; rewrite LVf3; right; right; right; right; exact He).
  lazymatch goal with AGx : agree_on _ _ mf3 |- _ =>
    carry AGx PXD ltac:(fun x Hx => right; right; left; exists pixd, 64; split; [apply LSUBf3; exact PDL0| exact Hx]) ltac:(fun Hx => exact I);
    carry AGx UREC ltac:(fun x Hx => left; unfold USTACK_TOP; clear - Hx SAU SPT; lia) ltac:(fun Hx => exact I);
    carry AGx CMC ltac:(fun x Hx => right; right; left; exists cmap, 24; split; [rewrite LVf3; right; left; reflexivity| exact Hx]) ltac:(fun Hx => exact I);
    carry AGx S112 ltac:(fun x Hx => left; unfold USTACK_TOP; clear - Hx SAU SPT; lia) ltac:(fun Hx => exact I) end.
  hide PXD. hide UREC. hide CMC. hide S112.
  fold_ag ltac:(fun Hx => apply (aclient_mono _ _ sa _ _ _ _ (proj1 Hx)); [exact LSUBf3| intros e He; rewrite FRSf2; exact He| clear; lia]).
  sigma_gc RT Σ Σf3.
  repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H in * end.
  clear_acc. refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj. park_ne.
  idtac "MARK cm: after free 3".
  (* [comment removed for export] *)
  unfold hid in S112.
  walk_to AF MST (@nil (Z * Z)) [e_free].
  at_call RT AF ltac:(cbn [ivls_client]; exact I) ltac:(fun Hx => cbn [outside]; exact I).
  unfold hid in UREC.
  lazymatch goal with |- cps _ (ASTA RT _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
    assert (UCC : chain_ok mc sa usp D2CM_RAS)
      by (apply (chain_ok_push mc sa usp RA_FUZZ_OP1 fp1 [RA_TOP]);
          [ clear - SAU; lia | clear - SPA; Z.div_mod_to_equations; lia | unfold USTACK_TOP; clear - SPT; lia | unfold RA_FUZZ_OP1; clear; lia
          | let X := fresh "X" in pose proof FP1h as X; unfold hid in X; exact X | exact UREC
          | apply (chain_ok_keep [RA_TOP] m _ usp fp1 UCX); eapply agree_sub; [exact AGF|]; cbv beta; intros zx Hzx; apply PFU; unfold USTACK_TOP in Hzx; clear - Hzx; lia ]) end.
  hide UREC. hide S112.
  eapply cps_seq.
  { pose proof (gp_free RT GP) as FC; unfold free_contractC in FC; eapply FC with (lo := lo) (p := t38) (n := 1024); rt_side idtac.
    all: lazymatch goal with
         | |- In _ _ => rewrite LVf3; right; right; right; left; reflexivity
         | |- unwind_okC _ _ _ _ => exists D2CM_RAS; rewrite ?unsigned_lit by (clear - USP0 USP1 SAU SPT; lia); split; [exact UCC| exact tr_d2cm_f4]
         | |- ?g => idtac "FREE SIDE LEFT:" g
         end. }
  idtac "MARK cm: free 4 applied".
  clear UCC.
  after_call RT AF.
  lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ => rename S into Σf4; rename A into ARTF4; rename mm into mf4 end.
  assert (LVf4 : rt_live RT Σf4 = (carr, 16) :: (cmap, 24) :: (t14, 1024) :: L0).
  { repeat match goal with E : rt_live RT Σf4 = _ |- _ => rewrite E end. rewrite LVf3.
    rewrite (live_remove_other t38 carr 16) by (exact (not_eq_sym (proj2 (FZ (t38, 1024) ltac:(rewrite LV0; right; left; reflexivity))))).
    rewrite (live_remove_other t38 cmap 24) by (exact (not_eq_sym (proj1 (FZ (t38, 1024) ltac:(rewrite LV0; right; left; reflexivity))))).
    rewrite (live_remove_other t38 t14 1024) by (unpark N84; exact (not_eq_sym N84)).
    rewrite live_remove_hd; [reflexivity|]. intros e He. exact (proj1 (proj2 (proj2 (proj2 (FRESH5 e He))))). }
  assert (FRSf4 : rt_frames RT Σf4 = rt_frames RT Σ) by (repeat match goal with E : rt_frames RT Σf4 = _ |- _ => rewrite E end; exact FRSf3).
  assert (SP0f4 : rt_sp0 RT Σf4 = rt_sp0 RT Σ) by (repeat match goal with E : rt_sp0 RT Σf4 = _ |- _ => rewrite E end; first [reflexivity | exact SP0f3]).
  assert (CRf4 : rt_credit RT Σ - 6 <= rt_credit RT Σf4) by (repeat match goal with E : rt_credit RT Σf4 = _ |- _ => rewrite E end; exact CRf3).
  assert (LSUBf4 : forall e, In e L0 -> In e (rt_live RT Σf4)) by (intros e He; rewrite LVf4; right; right; right; exact He).
  lazymatch goal with AGx : agree_on _ _ mf4 |- _ =>
    carry AGx PXD ltac:(fun x Hx => right; right; left; exists pixd, 64; split; [apply LSUBf4; exact PDL0| exact Hx]) ltac:(fun Hx => exact I);
    carry AGx UREC ltac:(fun x Hx => left; unfold USTACK_TOP; clear - Hx SAU SPT; lia) ltac:(fun Hx => exact I);
    carry AGx CMC ltac:(fun x Hx => right; right; left; exists cmap, 24; split; [rewrite LVf4; right; left; reflexivity| exact Hx]) ltac:(fun Hx => exact I);
    carry AGx S112 ltac:(fun x Hx => left; unfold USTACK_TOP; clear - Hx SAU SPT; lia) ltac:(fun Hx => exact I) end.
  hide PXD. hide UREC. hide CMC. hide S112.
  fold_ag ltac:(fun Hx => apply (aclient_mono _ _ sa _ _ _ _ (proj1 Hx)); [exact LSUBf4| intros e He; rewrite FRSf3; exact He| clear; lia]).
  sigma_gc RT Σ Σf4.
  repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H in * end.
  clear_acc. refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj. park_ne.
  idtac "MARK cm: after free 4".
  (* [comment removed for export] *)
  walk_to AF MST (@nil (Z * Z)) [e_free].
  at_call RT AF ltac:(cbn [ivls_client]; exact I) ltac:(fun Hx => cbn [outside]; exact I).
  unfold hid in UREC.
  lazymatch goal with |- cps _ (ASTA RT _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
    assert (UCC : chain_ok mc sa usp D2CM_RAS)
      by (apply (chain_ok_push mc sa usp RA_FUZZ_OP1 fp1 [RA_TOP]);
          [ clear - SAU; lia | clear - SPA; Z.div_mod_to_equations; lia | unfold USTACK_TOP; clear - SPT; lia | unfold RA_FUZZ_OP1; clear; lia
          | let X := fresh "X" in pose proof FP1h as X; unfold hid in X; exact X | exact UREC
          | apply (chain_ok_keep [RA_TOP] m _ usp fp1 UCX); eapply agree_sub; [exact AGF|]; cbv beta; intros zx Hzx; apply PFU; unfold USTACK_TOP in Hzx; clear - Hzx; lia ]) end.
  hide UREC.
  eapply cps_seq.
  { pose proof (gp_free RT GP) as FC; unfold free_contractC in FC; eapply FC with (lo := lo) (p := t14) (n := 1024); rt_side idtac.
    all: lazymatch goal with
         | |- In _ _ => rewrite LVf4; right; right; left; reflexivity
         | |- unwind_okC _ _ _ _ => exists D2CM_RAS; rewrite ?unsigned_lit by (clear - USP0 USP1 SAU SPT; lia); split; [exact UCC| exact tr_d2cm_f5]
         | |- ?g => idtac "FREE SIDE LEFT:" g
         end. }
  idtac "MARK cm: free 5 applied".
  clear UCC.
  after_call RT AF.
  lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ => rename S into Σf5; rename A into ARTF5; rename mm into mf5 end.
  assert (LVf5 : rt_live RT Σf5 = (carr, 16) :: (cmap, 24) :: L0).
  { repeat match goal with E : rt_live RT Σf5 = _ |- _ => rewrite E end. rewrite LVf4.
    rewrite (live_remove_other t14 carr 16) by (exact (not_eq_sym (proj2 (FZ (t14, 1024) ltac:(rewrite LV0; left; reflexivity))))).
    rewrite (live_remove_other t14 cmap 24) by (exact (not_eq_sym (proj1 (FZ (t14, 1024) ltac:(rewrite LV0; left; reflexivity))))).
    rewrite live_remove_hd; [reflexivity|]. intros e He. exact (proj2 (proj2 (proj2 (proj2 (FRESH5 e He))))). }
  assert (FRSf5 : rt_frames RT Σf5 = rt_frames RT Σ) by (repeat match goal with E : rt_frames RT Σf5 = _ |- _ => rewrite E end; exact FRSf4).
  assert (SP0f5 : rt_sp0 RT Σf5 = rt_sp0 RT Σ) by (repeat match goal with E : rt_sp0 RT Σf5 = _ |- _ => rewrite E end; first [reflexivity | exact SP0f4]).
  assert (CRf5 : rt_credit RT Σ - 6 <= rt_credit RT Σf5) by (repeat match goal with E : rt_credit RT Σf5 = _ |- _ => rewrite E end; exact CRf4).
  assert (LSUBf5 : forall e, In e L0 -> In e (rt_live RT Σf5)) by (intros e He; rewrite LVf5; right; right; exact He).
  lazymatch goal with AGx : agree_on _ _ mf5 |- _ =>
    carry AGx PXD ltac:(fun x Hx => right; right; left; exists pixd, 64; split; [apply LSUBf5; exact PDL0| exact Hx]) ltac:(fun Hx => exact I);
    carry AGx UREC ltac:(fun x Hx => left; unfold USTACK_TOP; clear - Hx SAU SPT; lia) ltac:(fun Hx => exact I);
    carry AGx CMC ltac:(fun x Hx => right; right; left; exists cmap, 24; split; [rewrite LVf5; right; left; reflexivity| exact Hx]) ltac:(fun Hx => exact I) end.
  hide PXD. hide UREC. hide CMC.
  fold_ag ltac:(fun Hx => apply (aclient_mono _ _ sa _ _ _ _ (proj1 Hx)); [exact LSUBf5| intros e He; rewrite FRSf4; exact He| clear; lia]).
  sigma_gc RT Σ Σf5.
  repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H in * end.
  clear_acc. refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj. park_ne.
  idtac "MARK cm: after free 5".
  (* [comment removed for export] *)
  unfold hid in PXD, CMC.
  apply cps_finish. intros c Hc. subst QF. unfold d2cm_post.
  exists Σf5, mf5, cmap, carr. do 25 eexists.
  split; [exact Hc|].
  split; [exact ARTF5|].
  split; [assumption|].
  split; [assumption|].
  split; [assumption|].
  split; [assumption|].
  split; [exact LVf5|].
  split; [exact FRSf5|].
  split; [first [assumption | reflexivity]|].
  split; [exact CRf5|].
  split.
  { split; [exists cpad; unfold cmap_cells; cbn [c_arr c_depth c_nalloc c_n]; exact CMC|].
    split; [split; [rewrite LVf5; right; left; reflexivity| split; [exact CM0| split; [exact CM16| clear; lia]]]|].
    split; [cbn [c_arr c_nalloc]; split; [rewrite LVf5; left; reflexivity| split; [exact CA0| split; [exact CA16| clear; lia]]]|].
    split; [exact COK| cbn [c_arr]; unpark CANE; exact CANE]. }
  split; [exact CM0|]. split; [exact CA0|]. split; [unpark CANE; clear - CANE; congruence|].
  split; [exact FZ|].
  split; [exact NCX|].
  split; [exact PXD|].
  exact AGF.
Qed.
End D2CM.
