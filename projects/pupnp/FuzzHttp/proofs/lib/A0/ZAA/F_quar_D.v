(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge Frame ITree.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.LZ Require Import ITreeLZ NodesLZ.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import STRW_tac STRW_merge Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac CellConv.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts AllocA0 ATac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAA Require Import AEnv ADepot ALayout APrim ATacA ACells LJ LJU PEnv APrimSpec APrimSpec2 APrimLem AFrame APrimPop APrimPopR APrimQ APrimFrame AFrameM
                        APrimDealloc ASec ASecD AQuar AQuarM AHeap AFoot F_prim_cdealloc F_quar_A AQuarR AQuarS ATacFix F_quar_M F_quar_DR F_quar_R F_sec_A.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Definition qdrain_entry : Z := 0x3526c.
Definition DRAIN_STACK : Z := QREC_STACK.

Section DRAIN.
  Context {HC : HasCeiling}.
  Variables (AL : alayout) (E : penv).
  Notation L := (al_thread AL).
  Notation THR := (at_thr (al_thread AL)).
  Notation CACHE := (at_thr (al_thread AL) + CACHE_OFF).
  Notation TQ := (at_thr (al_thread AL) + TQ_OFF).
  Hypothesis AO : alayout_ok AL.
  Variables (gp s10 s11 : word) (F_ : bvmap 5 word) (fc : bv 32).
  Variables (q lo : Z) (stackw : word).
  Hypothesis LOH : 0x10007fff8000 <= lo.
  Hypothesis CLO : alloc_ceiling <= lo.
  Hypothesis LOQ : lo <= q - DRAIN_STACK.
  Hypothesis QH : q <= 2^47.
  Hypothesis Q16 : q mod 16 = 0.

  Definition drain_rest (gl : list qbatch) : list qbatch := if Q_MAX <? qbytes gl then fst (q_recycle_sel gl) else gl.
  Definition drain_todo (gl : list qbatch) : list qbatch := if Q_MAX <? qbytes gl then snd (q_recycle_sel gl) else [].

  Definition drain_post (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 : word) (X : pstate) (H : word -> bool) (m : mem) (gl : list qbatch) (hrest : list (Z * Z))
    : unit -> (word -> bool) -> machine_state -> Prop :=
    fun _ H' ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' W,
      let rest := drain_rest gl in let todo := drain_todo gl in
      ms' = MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F_ (ret_pc ra) fc None m' (seg_rom asegs)
      /\ H' = H_dorecycle AL X todo H
      /\ munch ((QUAR_MTX, QUAR_MTX + 4) :: (QUAR_GQ, QUAR_GQ + 32) :: (TQ, TQ + 32) :: W) m m'
      /\ Forall (atouch AL lo q (fst X) (snd X) (tc_of gl) (tsc_of gl)) W
      /\ dr_inv AL E (dorecycle X todo) H' m' rest (flat_map qb_chunks rest) hrest
      /\ xle X (dorecycle X todo)
      /\ stk asegs m' lo q
      /\ qlist_rep AL m' rest 0 /\ rw_cells asegs m' QUAR_GQ (qcells AL rest) /\ rw_cells asegs m' TQ (qcells AL [])
      /\ rw_cells asegs m' QUAR_MTX [CB 4 [b8 0; b8 0; b8 0; b8 0]].

  Notation WD gl := ((lo, q) :: (QUAR_MTX, QUAR_MTX + 4) :: (QUAR_GQ, QUAR_GQ + 32) :: (TQ, TQ + 32) :: map (biv AL) gl).

  #[using="AO LOH CLO LOQ QH Q16"] Lemma drain_tail : forall (X : pstate) (H : word -> bool) (m mT : mem) (glob loc : list qbatch) (hrest : list (Z * Z))
        (junk : list byte) (r3 r2 r1 r0 rra : word) (xra t0 t1 t2 x0 x1 a4 a5 a6 a7 x2 x3 s4 s5 s6 s7 s8 s9 t3 t4 t5 t6 : word),
    mclean H mT ->
    dr_inv AL E X H m (glob ++ loc) (flat_map qb_chunks (glob ++ loc)) hrest ->
    munch (WD (glob ++ loc)) m mT -> wmono asegs m mT -> mem_inv asegs mT ->
    qlist_rep AL mT (glob ++ loc) 0 ->
    rw_cells asegs mT QUAR_GQ [C8 (wz (Z.of_nat (length (glob ++ loc)))); C8 (wz (qfirst AL (glob ++ loc))); C8 (wz (qlast AL (glob ++ loc))); C8 (wz (qbytes glob))] ->
    rw_cells asegs mT TQ [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz (qbytes loc))] ->
    rw_cells asegs mT QUAR_MTX [CB 4 [Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]] ->
    rw_cells asegs mT QUAR_CONST [C8 (wz Q_MAX); C8 (wz Q_MIN); C8 (wz Q_CACHE)] ->
    rw_cells asegs mT (q - 48) [CB 8 junk; C8 r3; C8 r2; C8 r1; C8 r0; C8 rra] -> stk asegs mT lo (q - 48) ->
    Forall qbatch_wf (glob ++ loc) -> qbytes (glob ++ loc) < 2^56 ->
    implA H (t_dorecycle AL X (drain_todo (glob ++ loc)))
      (drain_post rra r0 r1 r2 r3 s4 s5 s6 s7 s8 s9 X H m (glob ++ loc) hrest)
      (MS (mkR xra (wz (q - 48)) gp (wz A0_TP) t0 t1 t2 x0 x1 (wz QUAR) (wz TQ) (wz CACHE) stackw a4 a5 a6 a7
               x2 x3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz 0x35314) fc None mT (seg_rom asegs)).
  Proof.
    intros X H m mT glob loc hrest junk r3 r2 r1 r0 rra xra t0 t1 t2 x0 x1 a4 a5 a6 a7 x2 x3 s4 s5 s6 s7 s8 s9 t3 t4 t5 t6
      MC INV MUT WMT MIT QLT GCT TCT MTX CST FRS ST FWF QB.
    set (gl := glob ++ loc) in *.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    assert (LQ' : lo <= q - 48) by (unfold DRAIN_STACK, QREC_STACK, DOREC_STACK, AREC_STACK, CDEALLOC_STACK, MF_STACK in LOQ; lia).
    pose proof INV as (RP & POK & RS & MI & PE & TE & SV & WFS & REPS & HKS & HOK & NDS & BWF & BREP).
    pose proof AO as (_ & _ & _ & TLO & _). pose proof TLO as (T1 & T2 & T3 & T4 & T5 & _).
    hide MUT. hide WMT. hide INV. hide QLT.
    pose proof (munch_refl [(QUAR_MTX, QUAR_MTX + 4); (QUAR_GQ, QUAR_GQ + 32); (TQ, TQ + 32)] mT) as MUx. pose proof (wmono_refl asegs mT) as WMx.
    lz_go.
    do 4 zstep.
    sstep.
    zstep.
    sstep.
    do 2 zstep.

    unhide MUT. unhide WMT. unhide INV. unhide QLT.
    destruct (clear_ctx AL X m RP RS) as (WF0 & SOK & SSEP).
    layout_facts AO 0%nat SPF. destruct SPF as (SP1 & SP2 & SPM & _ & SP5 & _ & _).
    layout_apart_fact AO 0%nat 3%nat AP03.
    assert (BG : forall b, In b gl -> al_space AL <= qb_addr AL b /\ qb_addr AL b + 8192 <= al_space AL + K_SPACE
                                     /\ 2147450880 <= sh (qb_addr AL b) /\ sh (qb_addr AL b) + 1024 <= 17594333495296).
    { intros b Hb. assert (HBb : held1 (fst X) (bpair b)) by (destruct HOK as [_ FH]; apply (proj1 (Forall_forall _ _) FH); apply in_or_app; left; apply in_map; exact Hb).
      pose proof (held_geo AL (fst X) AO WF0 K_BCLASS (qb_v b) HBb) as G. cbv zeta in G.
      destruct G as (_ & G1 & G2 & G3 & _ & G5 & G6 & G7). pose proof (region_range AL K_BCLASS ltac:(lia)) as [R1 R2].
      change (class_size K_BCLASS) with 8192 in *. change (8192 / 8) with 1024 in G5. fold (qb_addr AL b) in G1, G2, G5, G6, G7.
      rewrite G5 in G7. clear - G1 G2 G3 G6 G7 R1 R2. lia. }
    assert (REQ : forall mE : mem, munch [(QUAR_MTX, QUAR_MTX + 4); (QUAR_GQ, QUAR_GQ + 32); (TQ, TQ + 32)] mT mE -> wmono asegs mT mE -> mem_inv asegs mE ->
              qlist_rep AL mE gl 0 /\ munch (WD gl) m mE /\ wmono asegs m mE /\ dr_inv AL E X H mE gl (flat_map qb_chunks gl) hrest).
    { intros mE MUE WME MIE.
      assert (QLE : qlist_rep AL mE gl 0).
      { eapply (qlist_rep_frame AL _ mT mE gl 0 QLT MUE WME). apply Forall_forall. intros b Hb. destruct (BG b Hb) as (B1 & B2 & B3 & B4).
        cbn [disjoint_from]. clear - B1 B2 B3 B4 SP1 AP03 T3. lia. }
      assert (MUA : munch (WD gl) m mE).
      { eapply munch_trans; [exact MUT|]. eapply munch_weaken; [| exact MUE]. apply sub_fp_incl.
        intros iv [<-|[<-|[<-|[]]]]; [right; left; reflexivity| right; right; left; reflexivity| right; right; right; left; reflexivity]. }
      pose proof (wmono_trans asegs _ _ _ WMT WME) as WMA.
      split; [exact QLE|]. split; [exact MUA|]. split; [exact WMA|].
      assert (EACH : forall l nxt (mm : mem), qlist_rep AL mm l nxt -> Forall (fun b => exists nx, qbatch_rep AL mm b nx) l).
      { induction l as [|b l IHl]; intros nxt mm QLl; [constructor|]. cbn [qlist_rep] in QLl. destruct QLl as [RB QLl].
        constructor; [eexists; exact RB| exact (IHl nxt mm QLl)]. }
      eapply (dr_inv_requeue AL E X H m mE gl gl _ hrest lo q [(QUAR_MTX, QUAR_MTX + 4); (QUAR_GQ, QUAR_GQ + 32); (TQ, TQ + 32)] ((lo, q) :: map (biv AL) gl) AO LOH CLO INV).
      - eapply munch_weaken; [| exact MUA]. apply sub_fp_incl. intros iv Hiv. cbn [app].
        destruct Hiv as [<-|[<-|[<-|[<-|Hiv]]]]; [right; right; right; left; reflexivity| left; reflexivity| right; left; reflexivity| right; right; left; reflexivity| right; right; right; right; exact Hiv].
      - exact WMA.
      - exact MIE.
      - constructor; [left; unfold qstat; cbn [fst snd]; lia|]. constructor; [left; unfold qstat; cbn [fst snd]; lia|]. constructor; [right; unfold sub_iv; cbn [fst snd]; lia| constructor].
      - constructor; [left; unfold sub_iv; cbn [fst snd]; clear - LQ'; lia|].
        apply Forall_forall. intros iv Hiv. apply in_map_iff in Hiv as (b & <- & Hb). right. exists b. split; [exact Hb|].
        unfold chunk_iv, biv, qb_addr. cbn [fst snd]. change (class_size K_BCLASS) with 8192. lia.
      - apply Permutation_refl.
      - exact BWF.
      - exact (EACH _ _ _ QLE). }
    assert (FBW : Forall bwf gl).
    { eapply Forall_impl; [| exact FWF]. intros b' (_ & _ & W3 & W4 & W5). unfold bwf. split; [| exact W3]. rewrite W4.
      assert (S0 : forall l : list qchunk, Forall qchunk_wf l -> 0 <= fold_right (fun ch acc => qc_n ch + acc) 0 l)
        by (induction 1 as [|c l (_ & _ & N1 & _) _ IHl]; cbn [fold_right]; lia).
      pose proof (S0 _ W5). lia. }
    pose proof (bwf_qbytes_nonneg gl FBW) as QB0.
    assert (QBE : qbytes glob + qbytes loc = qbytes gl) by (unfold gl; rewrite qbytes_app; reflexivity).
    rewrite QBE in *.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mf _) =>
      apply (rw_cells_rebytes mf QUAR_MTX _ [CB 4 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]) in MTX;
        [| cbn; tauto| cbn; repeat first [ reflexivity | apply (f_equal2 cons); [apply bv_eq; vm_compute; reflexivity|] ]| reflexivity] end.
    zstep. if_cases KD; zify_cond KD.

    -
      do 5 zstep.
      zstep. replace (q - 48 + 48) with q by lia. zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mE end.
      release_frame FRS ST q.
      destruct (REQ mE MUx WMx ltac:(assumption)) as (QLE & MUA & WMA & INVE).
      unfold drain_post. cbv zeta. unfold drain_todo, drain_rest. rewrite (proj2 (Z.ltb_ge Q_MAX (qbytes gl)) KD). cbn [t_dorecycle].
      lz_ret. apply evt_done. cbn [H_dorecycle dorecycle].
      do 15 eexists. exists mE, ((lo, q) :: map (biv AL) gl).
      split; [reflexivity|]. split; [reflexivity|].
      split. { eapply munch_weaken; [| exact MUA]. apply sub_fp_incl. intros iv Hiv.
               destruct Hiv as [<-|[<-|[<-|[<-|Hiv]]]]; [right; right; right; left; reflexivity| left; reflexivity| right; left; reflexivity| right; right; left; reflexivity| right; right; right; right; exact Hiv]. }
      split.
      { constructor; [left; unfold sub_iv; cbn [fst snd]; clear - LQ'; lia|].
        apply Forall_forall. intros iv Hiv. apply in_map_iff in Hiv as (b & <- & Hb). right; right; right; right; left.
        exists (bpair b). split; [unfold tc_of; apply in_or_app; left; apply in_map; exact Hb|]. left.
        unfold chunk_iv, biv, qb_addr, bpair. cbn [fst snd]. change (class_size K_BCLASS) with 8192. lia. }
      split; [exact INVE|]. split; [apply xle_refl|]. split; [exact ST|]. split; [exact QLE|].
      split; [unfold qcells; exact GCT|]. split; [exact TCT| exact MTX].

    -
      do 6 zstep.
      zstep.
      zstep.
      change (bv_swrap 32 256) with 256.
      amo_step.   try fold_cb_load.
      do 4 zstep.
      amo_step.
      zstep. if_false.
      do 2 zstep.

      zstep. if_true.
      zstep.
      do 5 zstep.
      zstep. replace (q - 48 + 48) with q by lia. zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mR end.
      release_frame FRS ST q.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mf _) =>
        apply (rw_cells_rebytes mf QUAR_MTX _ [CB 4 [b8 0; b8 1; b8 0; b8 0]]) in MTX;
          [| cbn; tauto| cbn; repeat first [ reflexivity | apply (f_equal2 cons); [apply bv_eq; vm_compute; reflexivity|] ]| reflexivity] end.
      destruct (REQ mR MUx WMx ltac:(assumption)) as (QLR & MUA & WMA & INVR).
      assert (KD' : (Q_MAX <? qbytes gl) = true) by (apply Z.ltb_lt; clear - KD; lia).
      unfold drain_todo. rewrite KD'.
      lz_here.
      eapply implA_mono.
      { eapply (qrecycle_spec AL E AO gp s10 s11 F_ fc q lo stackw LOH CLO LOQ QH Q16 rra _ _ _ r0 r1 _ _ _ _ r2 r3 s4 s5 s6 s7 s8 s9 _ _ _ _ X H mR gl hrest);
          [ assumption | exact ST | exact INVR | exact QLR | unfold qcells; exact GCT | exact MTX | exact FWF | exact QB ]. }

      intros u H' ms' PO. unfold qrecycle_post, qrec_post_gen in PO.
      destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & W & -> & -> & MU2 & FW2 & INV2 & XL2 & ST2 & QL2 & GC2 & MTX2).
      unfold drain_post. cbv zeta. unfold drain_todo, drain_rest. rewrite KD'.
      exists u0, u1, u2, b0, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m', ((lo, q) :: map (biv AL) gl ++ W).
      split; [reflexivity|]. split; [reflexivity|].
      split.
      { eapply munch_trans; [eapply munch_weaken; [| exact MUA]| eapply munch_weaken; [| exact MU2]]; apply sub_fp_incl.
        - intros iv Hiv. destruct Hiv as [<-|[<-|[<-|[<-|Hiv]]]]; [right; right; right; left; reflexivity| left; reflexivity| right; left; reflexivity| right; right; left; reflexivity|].
          right; right; right; right. apply in_or_app. left. exact Hiv.
        - intros iv Hiv. destruct Hiv as [<-|[<-|Hiv]]; [left; reflexivity| right; left; reflexivity|].
          right; right; right; right. apply in_or_app. right. exact Hiv. }
      split.
      { constructor; [left; unfold sub_iv; cbn [fst snd]; clear - LQ'; lia|]. apply Forall_app. split; [| exact FW2].
        apply Forall_forall. intros iv Hiv. apply in_map_iff in Hiv as (b & <- & Hb). right; right; right; right; left.
        exists (bpair b). split; [unfold tc_of; apply in_or_app; left; apply in_map; exact Hb|]. left.
        unfold chunk_iv, biv, qb_addr, bpair. cbn [fst snd]. change (class_size K_BCLASS) with 8192. lia. }
      split; [exact INV2|]. split; [exact XL2|]. split; [exact ST2|]. split; [exact QL2|]. split; [exact GC2|]. split; [| exact MTX2].
      pose proof INVR as (RPR & _ & RSR & _ & _ & _ & _ & _ & _ & _ & [_ FHR] & _).
      unfold qcells. cbn [length qfirst qlast qbytes rev fold_right Z.of_nat].
      eapply (rw_cells_transport_m _ mR m'); [exact TCT| exact MU2|]. cbn [cells_size csize Nat.add disjoint_from].
      split; [clear - T3; lia|]. split; [clear - T3; lia|].
      eapply (atouch_tq_dj AL X mR lo q W (tc_of gl) (tsc_of gl) TQ 32 AO LOH CLO RPR RSR); [| | exact FW2| lia| lia].
      + apply Forall_forall. intros cv Hcv. apply (proj1 (Forall_forall _ _) FHR). unfold tc_of in Hcv.
        apply in_app_or in Hcv as [Hcv|Hcv]; [apply in_or_app; left; exact Hcv| apply in_or_app; right; apply in_or_app; left; exact Hcv].
      + destruct (dr_inv_tc AL E X H mR gl (flat_map qb_chunks gl) [] hrest ltac:(rewrite app_nil_r; exact INVR)) as [_ TSI]. exact TSI.
  Qed.

  #[using="Type"] Lemma qlast_app : forall l1 l2, l2 <> [] -> qlast AL (l1 ++ l2) = qlast AL l2.
  Proof.
    intros l1 l2 NE. destruct (exists_last NE) as (l' & z & ->). rewrite app_assoc, !qlast_snoc. reflexivity.
  Qed.

  #[using="AO LOH CLO LOQ QH Q16"] Theorem drain_spec : forall (ra t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 t3 t4 t5 t6 : word)
        (X : pstate) (H : word -> bool) (m : mem) (glob loc : list qbatch) (hrest : list (Z * Z)),
    mclean H m -> stk asegs m lo q ->
    dr_inv AL E X H m (glob ++ loc) (flat_map qb_chunks (glob ++ loc)) hrest ->
    qlist_rep AL m glob 0 -> rw_cells asegs m QUAR_GQ (qcells AL glob) ->
    qlist_rep AL m loc 0 -> rw_cells asegs m TQ (qcells AL loc) ->
    rw_cells asegs m QUAR_MTX [CB 4 [b8 0; b8 0; b8 0; b8 0]] ->
    rw_cells asegs m QUAR_CONST [C8 (wz Q_MAX); C8 (wz Q_MIN); C8 (wz Q_CACHE)] ->
    Forall qbatch_wf (glob ++ loc) -> qbytes (glob ++ loc) < 2^56 ->
    implA H (t_dorecycle AL X (drain_todo (glob ++ loc)))
      (drain_post ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 X H m (glob ++ loc) hrest)
      (MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 (wz QUAR) (wz TQ) (wz CACHE) stackw a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz qdrain_entry) fc None m (seg_rom asegs)).
  Proof.
    intros ra t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 t3 t4 t5 t6 X H m glob loc hrest
      MC ST INV QLG GC QLL TC MTX CST FWF QB.
    unfold qdrain_entry.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    assert (LQ' : lo <= q - 48) by (unfold DRAIN_STACK, QREC_STACK, DOREC_STACK, AREC_STACK, CDEALLOC_STACK, MF_STACK in LOQ; lia).
    pose proof INV as (RP & POK & RS & MI & PE & TE & SV & WFS & REPS & HKS & HOK & NDS & BWF & BREP).
    pose proof AO as (_ & _ & _ & TLO & _). pose proof TLO as (T1 & T2 & T3 & T4 & T5 & _).
    destruct (clear_ctx AL X m RP RS) as (WF0 & SOK & SSEP).
    layout_facts AO 0%nat SPF. destruct SPF as (SP1 & SP2 & SPM & _ & SP5 & _ & _).
    layout_apart_fact AO 0%nat 3%nat AP03.
    assert (BG : forall b, In b (glob ++ loc) -> al_space AL <= qb_addr AL b /\ qb_addr AL b + 8192 <= al_space AL + K_SPACE
                                     /\ 2147450880 <= sh (qb_addr AL b) /\ sh (qb_addr AL b) + 1024 <= 17594333495296 /\ (16 * qb_v b) mod 8192 = 0).
    { intros b Hb. assert (HBb : held1 (fst X) (bpair b)) by (destruct HOK as [_ FH]; apply (proj1 (Forall_forall _ _) FH); apply in_or_app; left; apply in_map; exact Hb).
      pose proof (held_geo AL (fst X) AO WF0 K_BCLASS (qb_v b) HBb) as G. cbv zeta in G.
      destruct G as (_ & G1 & G2 & G3 & _ & G5 & G6 & G7). pose proof (region_range AL K_BCLASS ltac:(lia)) as [R1 R2].
      destruct HBb as (_ & _ & _ & VAL & _). cbn [fst snd bpair] in VAL.
      change (class_size K_BCLASS) with 8192 in *. change (8192 / 8) with 1024 in G5. fold (qb_addr AL b) in G1, G2, G5, G6, G7.
      rewrite G5 in G7. clear - G1 G2 G3 G6 G7 R1 R2 VAL. lia. }
    unfold qcells in GC, TC. unfold b8 in MTX.
    pose proof (munch_refl [(lo, q); (QUAR_MTX, QUAR_MTX + 4); (QUAR_GQ, QUAR_GQ + 32); (TQ, TQ + 32)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    lz_go.
    zstep. carve_frame 48%nat ST.
    do 5 zstep.
    do 4 zstep.
    amo_step.   try fold_cb_load.
    do 4 zstep.
    amo_step.
    zstep. if_false.
    zstep.
    zstep. if_false.
    zstep.
    zstep. if_cases KSAME; zify_cond KSAME. { exfalso. clear - KSAME T3. lia. } clear KSAME.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mA end.
    replace (q + -48) with (q - 48) in * by lia.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mf _) =>
      apply (rw_cells_rebytes mf QUAR_MTX _ [CB 4 [Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]) in MTX;
        [| cbn; tauto| cbn; repeat first [ reflexivity | apply (f_equal2 cons); [apply bv_eq; vm_compute; reflexivity|] ]| reflexivity] end.

    assert (DJB : forall (W : list (Z * Z)) b, In b (glob ++ loc) ->
              Forall (fun iv => (lo <= fst iv) \/ (snd iv <= 2147450880) \/ (THR <= fst iv /\ snd iv <= THR + 4096)) W ->
              0 <= qb_addr AL b /\ disjoint_from W (qb_addr AL b) Q_BBYTES /\ disjoint_from W (sh (qb_addr AL b)) 1024).
    { intros W b Hb FW. destruct (BG b Hb) as (B1 & B2 & B3 & B4 & _). split; [clear - B1 SP1; lia|].
      split; apply dj_of_Forall; (eapply Forall_impl; [| exact FW]); intros iv Hiv; cbn beta in Hiv |- *; clear - Hiv B1 B2 B3 B4 SP1 SP2 CLO LOH AP03 T3; lia. }
    assert (FW4 : Forall (fun iv : Z * Z => (lo <= fst iv) \/ (snd iv <= 2147450880) \/ (THR <= fst iv /\ snd iv <= THR + 4096))
                    [(lo, q); (QUAR_MTX, QUAR_MTX + 4); (QUAR_GQ, QUAR_GQ + 32); (TQ, TQ + 32)]).
    { repeat (apply Forall_cons || apply Forall_nil); cbn [fst snd]; clear; lia. }
    assert (FBW : Forall bwf (glob ++ loc)).
    { eapply Forall_impl; [| exact FWF]. intros b' (_ & _ & W3 & W4 & W5). unfold bwf. split; [| exact W3]. rewrite W4.
      assert (S0 : forall l : list qchunk, Forall qchunk_wf l -> 0 <= fold_right (fun ch acc => qc_n ch + acc) 0 l)
        by (induction 1 as [|c l (_ & _ & N1 & _) _ IHl]; cbn [fold_right]; lia).
      pose proof (S0 _ W5). lia. }
    pose proof (bwf_qbytes_len _ FBW) as LBG. rewrite length_app, Nat2Z.inj_add in LBG.
    zstep. if_cases KL; zify_cond KL.
    -
      assert (EL : loc = []) by (destruct loc; [reflexivity| cbn [length] in KL; clear - KL; lia]). subst loc.
      cbn [length qfirst qlast qbytes rev fold_right Z.of_nat] in TC.
      assert (QLA : qlist_rep AL mA (glob ++ []) 0).
      { rewrite app_nil_r. eapply (qlist_rep_frame AL _ m mA glob 0 QLG MU WM). apply Forall_forall. intros b Hb.
        apply DJB; [rewrite app_nil_r; exact Hb| exact FW4]. }
      lz_here.
      eapply (drain_tail X H m mA glob [] hrest _ s3 s2 s1 s0 ra); try eassumption.
      + eapply munch_weaken; [| exact MU]. apply sub_fp_incl. intros iv Hiv.
        destruct Hiv as [<-|[<-|[<-|[<-|[]]]]]; [left; reflexivity| right; left; reflexivity| right; right; left; reflexivity| right; right; right; left; reflexivity].
      + rewrite app_nil_r. exact GC.

    -
      assert (NEL : loc <> []) by (intros ->; apply KL; reflexivity).
      zstep.
      zstep. if_cases KG; zify_cond KG.
      +
        assert (EG : glob = []) by (destruct glob; [reflexivity| cbn [length] in KG; clear - KG; lia]). subst glob.
        cbn [length qfirst qlast qbytes rev fold_right Z.of_nat app] in *.
        do 6 zstep.
        do 3 sstep.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mB end.
        assert (QLB : qlist_rep AL mB loc 0).
        { eapply (qlist_rep_frame AL _ m mB loc 0 QLL MU WM). apply Forall_forall. intros b Hb. apply DJB; [exact Hb| exact FW4]. }
        lz_here.
        eapply (drain_tail X H m mB [] loc hrest _ s3 s2 s1 s0 ra); try eassumption.
        eapply munch_weaken; [| exact MU]. apply sub_fp_incl. intros iv Hiv.
        destruct Hiv as [<-|[<-|[<-|[<-|[]]]]]; [left; reflexivity| right; left; reflexivity| right; right; left; reflexivity| right; right; right; left; reflexivity].

      +
        assert (NEG : glob <> []) by (intros ->; apply KG; reflexivity).
        destruct (exists_last NEG) as (gi & gz & EGL). subst glob.
        apply qlist_rep_snoc in QLG as [QLGi (GZH & GZA' & GZS)].
        assert (INgz : In gz ((gi ++ [gz]) ++ loc)) by (apply in_or_app; left; apply in_or_app; right; left; reflexivity).
        destruct (BG gz INgz) as (Z1 & Z2 & Z3 & Z4 & Z5).
        assert (NDV : List.NoDup (map qb_v ((gi ++ [gz]) ++ loc))).
        { destruct HOK as [ND _]. apply NoDup_app_remove_r in ND. unfold bpair in ND. rewrite <- (map_map qb_v (fun v => (K_BCLASS, v))) in ND. apply NoDup_map_inv in ND. exact ND. }
        assert (APZ : forall b, In b (gi ++ loc) -> qb_addr AL b + 8192 <= qb_addr AL gz \/ qb_addr AL gz + 8192 <= qb_addr AL b).
        { intros b Hb. assert (Hb' : In b ((gi ++ [gz]) ++ loc)) by (apply in_app_or in Hb as [Hb|Hb]; [apply in_or_app; left; apply in_or_app; left; exact Hb| apply in_or_app; right; exact Hb]).
          destruct (BG b Hb') as (_ & _ & _ & _ & B5).
          assert (VNE : qb_v b <> qb_v gz).
          { intros C. rewrite <- app_assoc, map_app in NDV. cbn [app map] in NDV.
            apply in_app_or in Hb as [Hb|Hb].
            - apply (NoDup_app_disj_s _ _ (qb_v b) NDV); [apply in_map; exact Hb| left; symmetry; exact C].
            - apply NoDup_app_remove_l in NDV. apply NoDup_cons_iff in NDV as [NI _]. apply NI. rewrite <- C. apply in_map. exact Hb. }
          unfold qb_addr. clear - B5 Z5 VNE. Z.div_mod_to_equations. lia. }
        eapply (rw_cells_transport asegs _ m mA) in GZH; [| exact MU| exact WM| cbn [cells_size csize Nat.add disjoint_from]; clear - Z1 Z2 SP1 SP2 CLO AP03 T3; lia].
        rewrite qlast_snoc in *.
        assert (MU' : munch [(lo, q); (QUAR_MTX, QUAR_MTX + 4); (QUAR_GQ, QUAR_GQ + 32); (TQ, TQ + 32); (qb_addr AL gz, qb_addr AL gz + 24)] m mA).
        { eapply munch_weaken; [| exact MU]. apply sub_fp_incl. intros iv Hiv.
          destruct Hiv as [<-|[<-|[<-|[<-|[]]]]]; [left; reflexivity| right; left; reflexivity| right; right; left; reflexivity| right; right; right; left; reflexivity]. }
        clear MU. rename MU' into MU.
        remember (qb_addr AL gz) as GZA eqn:HGZA.
        do 4 zstep.
        do 3 zstep.
        zstep.
        do 3 sstep.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mC end.

        subst GZA.
        change ((fix app (l m : list qbatch) {struct l} : list qbatch := match l with [] => m | a :: l1 => a :: app l1 m end) gi [gz]) with (gi ++ [gz]) in *.
        assert (FW5 : Forall (fun iv : Z * Z => (lo <= fst iv) \/ (snd iv <= 2147450880) \/ (THR <= fst iv /\ snd iv <= THR + 4096))
                        [(lo, q); (QUAR_MTX, QUAR_MTX + 4); (QUAR_GQ, QUAR_GQ + 32); (TQ, TQ + 32)]) by exact FW4.
        assert (DJC : forall b, In b (gi ++ loc) ->
                  0 <= qb_addr AL b /\ disjoint_from [(lo, q); (QUAR_MTX, QUAR_MTX + 4); (QUAR_GQ, QUAR_GQ + 32); (TQ, TQ + 32); (qb_addr AL gz, qb_addr AL gz + 24)] (qb_addr AL b) Q_BBYTES
                  /\ disjoint_from [(lo, q); (QUAR_MTX, QUAR_MTX + 4); (QUAR_GQ, QUAR_GQ + 32); (TQ, TQ + 32); (qb_addr AL gz, qb_addr AL gz + 24)] (sh (qb_addr AL b)) 1024).
        { intros b Hb. assert (Hb' : In b ((gi ++ [gz]) ++ loc)) by (apply in_app_or in Hb as [Hb|Hb]; [apply in_or_app; left; apply in_or_app; left; exact Hb| apply in_or_app; right; exact Hb]).
          destruct (DJB _ b Hb' FW5) as (D0 & D1 & D2). destruct (BG b Hb') as (B1 & B2 & B3 & B4 & _). pose proof (APZ b Hb) as AZ.
          split; [exact D0|]. cbn [disjoint_from] in D1, D2 |- *. clear - D1 D2 AZ B4 Z1 SP1. lia. }
        assert (QLC : qlist_rep AL mC ((gi ++ [gz]) ++ loc) 0).
        { apply qlist_rep_app. split.
          - apply qlist_rep_snoc. split.
            + eapply (qlist_rep_frame AL _ m mC gi _ QLGi MU WM). apply Forall_forall. intros b Hb. apply DJC. apply in_or_app. left. exact Hb.
            + unfold qbatch_rep. split; [| split].
              * destruct loc as [|l0 lr]; [contradiction|]. exact GZH.
              * destruct GZA' as (ws & AR & LW & FWs). exists ws. split; [| split; assumption].
                eapply u64arr_transport; [exact AR| exact MU| exact WM|]. rewrite LW. cbn [disjoint_from]. clear - Z1 Z2 SP1 SP2 CLO AP03 T3. lia.
              * eapply rw_cells_transport; [exact GZS| exact MU| exact WM|]. cbn [cells_size csize Nat.add disjoint_from].
                clear - Z1 Z3 Z4 SP1 LOH T3. lia.
          - eapply (qlist_rep_frame AL _ m mC loc 0 QLL MU WM). apply Forall_forall. intros b Hb. apply DJC. apply in_or_app. right. exact Hb. }
        lz_here.
        eapply (drain_tail X H m mC (gi ++ [gz]) loc hrest _ s3 s2 s1 s0 ra); try eassumption.
        * eapply munch_weaken; [| exact MU]. intros x O. cbn [outside].
          pose proof (outside_In _ x (lo, q) O ltac:(left; reflexivity)) as O1.
          pose proof (outside_In _ x (QUAR_MTX, QUAR_MTX + 4) O ltac:(right; left; reflexivity)) as O2.
          pose proof (outside_In _ x (QUAR_GQ, QUAR_GQ + 32) O ltac:(right; right; left; reflexivity)) as O3.
          pose proof (outside_In _ x (TQ, TQ + 32) O ltac:(right; right; right; left; reflexivity)) as O4.
          pose proof (outside_In _ x (biv AL gz) O ltac:(right; right; right; right; apply in_map; exact INgz)) as O5.
          unfold biv in O5. cbn [fst snd] in *. repeat split; try assumption. clear - O5. lia.
        * rewrite length_app, Nat2Z.inj_add, (qfirst_app AL (gi ++ [gz]) loc ltac:(intros C; apply app_eq_nil in C as [_ C]; discriminate)), (qlast_app _ loc NEL). exact GC.
  Qed.
End DRAIN.

