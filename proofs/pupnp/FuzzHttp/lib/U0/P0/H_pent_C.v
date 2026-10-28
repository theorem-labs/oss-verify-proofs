(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From stdpp Require Import base list.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Arr.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Top Require Import AllocIF AllocSpec SReach.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac HttpAlloc HttpAllocX CellConv.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs F_syscalls H_scanner_get_token H_vfmatch_A H_obj H_membuffer_assign
     H_UpnpPrintf H_entity_read_method H_prep H_map_str_to_int H_phdr_A H_phdr_B H_phdr_C.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import H_phdr_D.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import H_pent_A H_pent_B.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Ceiling.
Import ListNotations.
Open Scope Z_scope.
Set Printing Width 1000.
Set Printing Depth 100.

Section W.
Context {HCEIL : HasCeiling}.
  Variable AI : alloc_if rsegs.
  Variable AC : alloc_contracts AI.
  Notation L_ := (ai_L rsegs AI).
  Notation K := (ai_K rsegs AI).
  Notation BLK := (block K).
  Notation hdr := (hdr AI).
  Hypothesis LOK : layout_ok AI.
  Hypothesis REALLOCPC : al_realloc_pc L_ = 0x1995c.
  Hypothesis TPV : al_tp L_ = 0x3b820.
  Hypothesis ERRNOV : al_errno L_ = 0x3b77c.
  Hypothesis CAN : canary_ok AI.
  Hypothesis ERRNC : forall lo hi, al_client_static L_ lo hi -> hi <= al_errno L_ \/ al_errno L_ + 4 <= lo.
  Hypothesis BLK4096 : blk4096_ok AI.
  Hypothesis BLKIMG : blk_img_ok AI.
  Hypothesis GERM : germ_stmt AI.
  Hypothesis PH : parse_headers_stmt AI.
  Hypothesis GMST : exists lo hi, al_client_static L_ lo hi /\ lo <= GMAXA /\ GMAXA + 8 <= hi.
  Hypothesis IWST : exists lo hi, al_client_static L_ lo hi /\ lo <= INITWASCALLED /\ INITWASCALLED + 1 <= hi.
  Hypothesis TABST : exists lo hi, al_client_static L_ lo hi /\ lo <= TAB_HDR /\ TAB_HDR + 528 <= hi.
  Hypothesis ZST : exists lo hi, al_client_static L_ lo hi /\ lo <= ZERO_ADDR /\ ZERO_ADDR + 1 <= hi.

  Variables (P q lo B gmax : Z) (LBK : list BLK) (isreq maj min rm sc : Z) (m0 : mem) (ws : list word).
  Variables (ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e : word).
  Notation S := (P + 480)%Z.
  Notation MB := (P + 400)%Z.
  Hypothesis QLO : (lo + 2432 <= q)%Z.
  Hypothesis QLO2 : (lo <= q - 304 - al_stack L_)%Z.
  Hypothesis STK0 : (0 <= al_stack L_)%Z.
  Hypothesis LO0 : (0x5d000 <= lo)%Z.
  Hypothesis CEIL : (alloc_ceiling <= lo)%Z.
  Hypothesis QP : (q + 144 <= P)%Z.
  Hypothesis PB : (P + 504 <= B)%Z.
  Hypothesis BHI : (B < 2^62)%Z.
  Hypothesis GMX : (0 < gmax < 2^32)%Z.
  Hypothesis P8 : pmod8 P.
  Hypothesis Q8 : pmod8 q.

  Hypothesis WSL : length ws = 66%nat.
  Hypothesis HID : forall i, (0 <= i < 33)%Z -> exists id, nth_error ws (Z.to_nat (2 * i + 1)) = Some (wz id) /\ (0 <= id < 64)%Z.
  Hypothesis TS : table_strings ws 33 lo.

  #[using="ws QLO2 WSL"] Lemma QLO2' : (lo <= q - 32 - al_stack L_)%Z. Proof. lia. Qed.

  Notation PHS := (ph_statics ws).
  Notation PCx := (PC AI PHS P q lo B gmax LBK isreq maj min rm sc m0 ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e).
  Notation POSTx := (pent_post AI P q lo B gmax LBK isreq maj min rm sc m0 ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e).

  #[using="LOK BLK4096 BLKIMG PH GMST IWST QLO QLO2 STK0 LO0 CEIL QP PB BHI P8 Q8 WSL HID TS"] Lemma hcall_ok : hdrs_call AI PHS P q lo B gmax LBK isreq maj min rm sc m0 ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e.
  Proof.
    unfold hdrs_call. intros gp F fc s LB m A len cap km bs ebw elw err hack pos entp clen csz esp ns hs X meth scur rpc
      t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2v s7 t3 t4 t5 t6 PCI SCUR RPC HK.
    pose proof Q8 as Q8'. unfold pmod8 in Q8'.
    unfold PC in PCI.
    destruct PCI as (HR & HE & MI & ST & [errv ERR] & FSH & FX & PSC & PMSG & PENT & PCTL & PHL & XV & PMETH & PVER & PRS_ & BSUB & ND & GM & IW & HPX & PHST).
    pose proof alloc_ceiling_bounds as CE. pose proof alloc_ceiling_aligned8 as CE8.
    destruct (msg_facts AI BLK4096 BLKIMG P _ _ _ _ _ _ _ _ HR PMSG) as (HL & HC & A0 & AHI & OKS & _). unfold LMAX in HC.
    destruct (OKS km eq_refl) as (HIN & BLKM & A4 & AW).
    pose proof PMETH as [_ METHR]. pose proof PHL as (_ & _ & _ & _ & _ & _ & _ & _ & X0').
    replace (wz q) with (wz (q - 240 + 240)) by (f_equal; lia).
    eapply sreach_bind.
    { eapply (PH P (q - 240) lo B ws isreq maj min scur X len meth A cap (Some km) bs (okb AI (Some km) A cap ++ LBK) err hack pos entp clen csz esp ns hs LB s);
        try eassumption; try exact P8; try lia.
      - replace (q - 240 + 240)%Z with q by lia. exact ST.
      - intros k Ek. injection Ek as <-. apply in_or_app. left. left. reflexivity. }
    intros s' LB' ms' PO. unfold ph_post in PO.
    destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & r & cur' & meth' & err' & pos' & ns' & hs'
                    & -> & MI' & ST' & HE' & [e' ERR'] & HP' & HR' & PSC' & CUR' & PMSG' & PMETH' & MD & PVER' & PCTL' & ED & PHL' & BSUB' & ND' & TAB' & ZB' & RR & _ & _).
    replace (q - 240 + 240)%Z with q in * by lia. rewrite RPC.
    eapply (HK s' LB' m' r cur' meth' err' pos' (X + 2 * (cur' - scur))%Z ns' hs'); [| exact RR| lia].

    assert (TR : forall X0 cs, rw_cells rsegs m X0 cs -> (q <= X0)%Z ->
                 (X0 + Z.of_nat (cells_size cs) <= P + 4 \/ (P + 8 <= X0 /\ X0 + Z.of_nat (cells_size cs) <= P + 288) \/ (P + 384 <= X0 /\ X0 + Z.of_nat (cells_size cs) <= P + 440)
                  \/ (P + 452 <= X0 /\ X0 + Z.of_nat (cells_size cs) <= P + 488) \/ P + 496 <= X0)%Z ->
                 (X0 + Z.of_nat (cells_size cs) <= P + 504)%Z -> rw_cells rsegs m' X0 cs).
    { intros X0 cs H H1 H2 H3. eapply (hpx_rw_cells rsegs AI); [exact HP'| exact H| apply client_range_above; lia|].
      unfold WH, mwin. cbn. repeat split; lia. }
    assert (TRS : forall X0 cs, rw_cells rsegs m X0 cs -> (exists slo shi, al_client_static L_ slo shi /\ slo <= X0 /\ X0 + Z.of_nat (cells_size cs) <= shi)%Z ->
                  (X0 + Z.of_nat (cells_size cs) <= lo)%Z -> rw_cells rsegs m' X0 cs).
    { intros X0 cs H (slo & shi & Hst & S1 & S2) H3. eapply (hpx_rw_cells rsegs AI); [exact HP'| exact H| eapply client_range_static; [exact Hst| lia| lia]|].
      destruct (lo_static_img rsegs AI LOK slo shi Hst) as (w & Hw & W1 & W2).
      destruct (ai_block_range rsegs AI _ _ _ _ HR HIN) as (_ & _ & _ & _ & RF). pose proof (proj1 (List.Forall_forall _ _) RF w Hw) as X1. cbn in X1.
      unfold WH, mwin. cbn. repeat split; lia. }
    split; [exact HR'|]. split; [exact HE'|]. split; [exact MI'|]. split; [exact ST'|]. split; [eexists; exact ERR'|].
    split; [apply (TR _ _ FSH); cbn; lia|].
    split. { destruct FX as (Q0 & [j16 Q16] & [cz Q20] & (da & db & Q24)).
             split; [apply (TR _ _ Q0); cbn; lia|]. split; [eexists; apply (TR _ _ Q16); cbn; lia|].
             split; [eexists; apply (TR _ _ Q20); cbn; lia| do 2 eexists; apply (TR _ _ Q24); cbn; lia]. }
    split; [exact PSC'|]. split; [exact PMSG'|].
    split; [unfold p_ent in *; apply (TR _ _ PENT); cbn; lia|].
    split; [exact PCTL'|]. split; [exact PHL'|]. split; [lia|].
    split; [exact PMETH'|]. split; [exact PVER'|].
    split; [destruct PRS_ as [RC RRs]; split; [apply (TR _ _ RC); cbn; lia| exact RRs]|].
    split; [exact BSUB'|]. split; [exact ND'|].
    split. { apply (TRS _ _ GM); [| cbn; lia]. destruct GMST as (slo & shi & Hst & G1 & G2). exists slo, shi. split; [exact Hst| cbn; lia]. }
    split. { apply (TRS _ _ IW); [| cbn; lia]. destruct IWST as (slo & shi & Hst & G1 & G2). exists slo, shi. split; [exact Hst| cbn; lia]. }
    split; [| split; [exact TAB'| exact ZB']].

    eapply (hpx_trans rsegs AI); [exact HPX|].
    intros a Ha Hc Ho. apply (HP' a Ha).
    - destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [left; lia| right; left; exact Hc| right; right]. exists b. split; [apply in_or_app; right; exact Hb| exact Hr].
    - unfold WH, mwin, WE in *. cbn [outside fst snd] in Ho |- *. destruct Ho as (O1 & O2 & O3 & O4 & _).
      repeat split; try lia.

      destruct (ai_block_range rsegs AI _ _ _ _ HR HIN) as (R1 & R2 & R3 & R4 & RF). cbn in R1, R4, RF.
      destruct Hc as [Hc|[(slo & shi & Hst & Hr)|(b & Hb & Hr)]]; [lia| |].
      + destruct (lo_static_img rsegs AI LOK slo shi Hst) as (w & Hw & W1 & W2).
        pose proof (proj1 (List.Forall_forall _ _) RF w Hw) as X1. cbn in X1. lia.
      + destruct (proj1 (bsub_app AI _ _ _) BSUB) as [_ BSUB2]. destruct (proj1 (bsub_app AI _ _ _) BSUB2) as [_ SUBK].
        assert (NE : b <> (km, A, cap + 1)%Z).
        { intros ->. pose proof ND as ND2. rewrite app_assoc in ND2.
          assert (INM : In (km, A, cap + 1)%Z (okb AI (Some km) A cap)) by (left; reflexivity).
          exact (nodup_in_neq AI _ _ _ _ ND2 (in_or_app _ _ _ (or_intror INM)) Hb eq_refl). }
        pose proof (ai_blocks_disjoint rsegs AI _ _ _ _ _ HR (SUBK b Hb) HIN NE) as DJ. cbn in DJ. unfold in_block in Hr. lia.
  Qed.

  #[using="AC LOK REALLOCPC TPV ERRNOV CAN ERRNC BLK4096 BLKIMG GERM PH GMST IWST TABST ZST QLO QLO2 STK0 LO0 CEIL QP PB BHI GMX P8 Q8 WSL HID TS"] Theorem parser_parse_entity_spec : forall gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F : bvmap 5 word) fc s LB
      (cur A len cap : Z) (km : K) (bs : list byte) (ebw elw : word) (err hack pos entp clen csz esp X meth : Z) (ns : list (BLK * Z)) (hs : list hdr) (errv : word),
    RHEAP rsegs AI s LB m0 -> RENV rsegs AI m0 B -> mem_inv rsegs m0 -> stk rsegs m0 lo (q + 144) ->
    rw_cells rsegs m0 (al_errno L_) [C4 errv] ->
    p_scan m0 P cur -> p_msg AI m0 LB P A len cap (Some km) bs -> (0 <= cur <= len)%Z ->
    p_ent m0 P ebw elw -> p_ctl m0 P err hack pos entp clen csz esp -> p_hlist AI m0 P ns hs X -> (X + 2 * (len - cur) <= VMAX)%Z ->
    p_meth m0 P meth -> p_ver m0 P isreq maj min -> p_rs m0 P rm sc ->
    bsub AI (hl_blocks AI ns hs ++ okb AI (Some km) A cap ++ LBK) LB -> NoDup (map blk_id (hl_blocks AI ns hs ++ okb AI (Some km) A cap ++ LBK)) ->
    rw_cells rsegs m0 GMAXA [C8 (wz gmax)] -> rw_cells rsegs m0 INITWASCALLED [C1 (Z_to_bv 8 0)] -> bytes_at rsegs m0 GOT_GMAX (le8 (wz GMAXA)) -> ph_statics ws m0 ->
    ent_ok gmax entp cur esp csz elw ->
    SREACH AI (POSTx gp F fc)
      (MS (mkR ra (wz (q + 144)) gp (wz (al_tp L_)) t0 t1 t2 s0e s1e (wz P) a1 a2 a3 a4 a5 a6 a7 s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e t3 t4 t5 t6)
          F (wz parse_entity_entry) fc None m0 (seg_rom rsegs)) s LB.
  Proof.
    intros.
    eapply (parser_parse_entity_B AI AC LOK REALLOCPC TPV ERRNOV CAN ERRNC BLK4096 BLKIMG GERM GMST IWST (ph_statics ws) TAB_HDR ZERO_ADDR);
      try eassumption; try exact QLO2'; try exact hcall_ok.

    all: [> intros W m m' MU WM D1 D2 PS; eapply ph_statics_munch; try exact MU; try exact WM; try exact D1; try exact D2; try exact PS
         | intros LB0 SP m m' HPR PS; eapply ph_statics_hp; try exact HPR; try exact PS ]; eauto;
         repeat match goal with |- context [?x] => is_evar x; unify x (q - 240)%Z end; try lia; eauto.
  Qed.
End W.
