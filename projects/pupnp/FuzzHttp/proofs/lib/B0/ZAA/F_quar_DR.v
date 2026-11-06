(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge Frame ITree.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.LZ Require Import ITreeLZ NodesLZ.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import STRW_tac STRW_merge Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac CellConv.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts AllocA0 ATac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAA Require Import AEnv ADepot ALayout APrim ATacA ACells LJ LJU PEnv APrimSpec APrimSpec2 APrimLem AFrame APrimPop APrimPopR APrimQ APrimFrame AFrameM
                        APrimDealloc ASec ASecD AQuar AQuarM AHeap AFoot F_prim_cdealloc F_quar_A AQuarR ATacFix.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Definition dorecycle_entry : Z := 0x35760.
Definition DOREC_STACK : Z := 112 + AREC_STACK.

Section DOREC.
  Context {HC : HasCeiling}.
  Variables (AL : alayout) (E : penv).
  Notation L := (al_thread AL).
  Notation THR := (at_thr (al_thread AL)).
  Notation CACHE := (at_thr (al_thread AL) + CACHE_OFF).
  Notation PARR := (al_parr AL).
  Hypothesis AO : alayout_ok AL.

  Definition tc_of (bs : list qbatch) : list (Z * Z) := map bpair bs ++ flat_map prim_of (flat_map qb_chunks bs).
  Definition tsc_of (bs : list qbatch) : list schunk := flat_map sec_of (flat_map qb_chunks bs).

  Variables (gp s10 s11 : word) (F_ : bvmap 5 word) (fc : bv 32).
  Variables (q lo C : Z) (stackw : word).
  Hypothesis LOH : 0x10007fff8000 <= lo.
  Hypothesis CLO : alloc_ceiling <= lo.
  Hypothesis LOQ : lo <= q - DOREC_STACK.
  Hypothesis QH : q <= 2^47.
  Hypothesis Q16 : q mod 16 = 0.
  Hypothesis QC : q <= C.
  Hypothesis C47 : C + 32 <= 2^47.

  Definition dr_frame (m : mem) (junk : list byte) (r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 rra : word) : Prop :=
    rw_cells asegs m (q - 112) [CB 8 junk]
    /\ rw_cells asegs m (q - 104) [C8 (wz CACHE); C8 stackw]
    /\ rw_cells asegs m (q - 88) [C8 r9; C8 r8; C8 r7; C8 r6; C8 r5; C8 r4; C8 r3; C8 r2; C8 r1; C8 r0; C8 rra].

  Definition dr_mach (m : mem) (junk : list byte) (r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 rra : word) (cells : list cell) : Prop :=
    stk asegs m lo (q - 112) /\ dr_frame m junk r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 rra /\ rw_cells asegs m C cells.

  #[using="AO LOH CLO LOQ QC"] Lemma dr_cross : forall X (m m' : mem) W tc tsc junk r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 rra cells,
    RPRIM AL (fst X) m -> RSEC AL (snd X) m -> Forall (held1 (fst X)) tc -> incl tsc (se_chunks (snd X)) ->
    munch W m m' -> Forall (atouch AL lo (q - 112) (fst X) (snd X) tc tsc) W ->
    dr_frame m junk r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 rra -> rw_cells asegs m C cells ->
    dr_frame m' junk r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 rra /\ rw_cells asegs m' C cells.
  Proof.
    intros X m m' W tc tsc junk r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 rra cells RP RS TCH TSI MU FW (F1 & F2 & F3) CC.
    assert (LQ : lo <= q - 112) by (unfold DOREC_STACK, AREC_STACK, CDEALLOC_STACK, MF_STACK in LOQ; lia).
    assert (AB : forall A n, q - 112 <= A -> disjoint_from W A n)
      by (intros A n HA; exact (atouch_above AL X m lo (q - 112) W tc tsc A n AO LOH CLO LQ RP RS TCH TSI FW HA)).
    split; [split; [| split]|]; (eapply rw_cells_transport_m; [eassumption| exact MU| apply AB; lia]).
  Qed.

  Definition xle (X X' : pstate) : Prop :=
    (forall c, 1 <= c <= 31 -> p_au (get_cls (fst X) c) <= p_au (get_cls (fst X') c)) /\ incl (se_chunks (snd X')) (se_chunks (snd X)).
  #[using="Type"] Lemma xle_refl : forall X, xle X X. Proof. intros X. split; [intros c _; apply Z.le_refl| apply incl_refl]. Qed.
  #[using="Type"] Lemma xle_trans : forall X1 X2 X3, xle X1 X2 -> xle X2 X3 -> xle X1 X3.
  Proof. intros X1 X2 X3 [A1 B1] [A2 B2]. split; [intros c Hc; exact (Z.le_trans _ _ _ (A1 c Hc) (A2 c Hc))| exact (incl_tran B2 B1)]. Qed.

  #[using="q"] Lemma p_au_cdealloc : forall P c v c', length (pr_cls P) = 32%nat -> 1 <= c <= 31 ->
    p_au (get_cls (cache_dealloc P c v) c') = p_au (get_cls P c').
  Proof.
    intros P c v c' LEN Hc. destruct (Z.eq_dec c' c) as [->|NE]; [| rewrite (get_cls_cdealloc_other P c v c' Hc NE); reflexivity].
    unfold cache_dealloc. destruct P as [cls ini ca cm]. cbn [pr_cls pr_inited pr_calloc pr_cmapped] in *.
    rewrite get_cls_set_same by (try exact LEN; lia). apply cache_push_au.
  Qed.

  #[using="q"] Lemma xle_recycle1 : forall X (m : mem) ch, RPRIM AL (fst X) m -> RSEC AL (snd X) m -> qchunk_wf ch -> held_kind X ch -> xle X (recycle1 X ch).
  Proof.
    intros X m ch RP RS WF HK. pose proof RP as (LEN & _). destruct ch as [[c v|sc] rz n]; unfold xle, recycle1, held_kind in *; cbn [qc_kind fst snd] in *.
    - destruct HK as (Hc & _). cbn [fst] in Hc. split; [| apply incl_refl]. intros c' _. rewrite (p_au_cdealloc (fst X) c v c' LEN Hc). lia.
    - split; [intros; lia|]. cbn [sec_dealloc se_chunks]. intros d Hd.
      pose proof RS as (SWF & _). destruct SWF as (_ & _ & _ & _ & _ & COK & CSEP).
      assert (POSM : Forall (fun d => 0 < sc_msize d) (se_chunks (snd X))).
      { apply Forall_forall. intros d' Hd'. pose proof (chunk_ok_msize AL d' (proj1 (Forall_forall _ _) COK d' Hd')) as [DM _]. lia. }
      eapply remove_at_In; [| exact Hd]. exact (nth_error_lt _ _ _ (F_quar_As.sc_index_nth _ sc CSEP POSM HK)).
  Qed.

  #[using="q"] Lemma atouch_xle : forall X X' lo1 q1 tc tsc tc1 tsc1 W,
    xle X X' -> incl tc1 tc -> incl tsc1 tsc ->
    Forall (atouch AL lo1 q1 (fst X') (snd X') tc1 tsc1) W -> Forall (atouch AL lo1 q1 (fst X) (snd X) tc tsc) W.
  Proof.
    intros X X' lo1 q1 tc tsc tc1 tsc1 W [A B] I1 I2 FW.
    eapply (Forall_atouch_mono AL lo1 q1 (fst X) (snd X) tc tsc lo1 q1 (fst X') (snd X') tc1 tsc1 W); try assumption; lia.
  Qed.

  #[using="AO LOH CLO"] Lemma dr_inv_stack : forall X H (m m' : mem) WB WC hrest A n,
    lo <= A -> 0 <= n ->
    dr_inv AL E X H m WB WC hrest -> munch [(A, A + n)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
    dr_inv AL E X H m' WB WC hrest.
  Proof.
    intros X H m m' WB WC hrest A n LA N0 INV MU WM MI'.
    destruct INV as (RP & POK & RS & MI & PE & TE & SV & WFS & REPS & HKS & HOK & NDS & BWF & BREP).
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof AO as (_ & _ & _ & TLO & _). pose proof TLO as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & _).
    layout_facts AO 0%nat SPF. destruct SPF as (SP1 & SP2 & SPM & _ & SP5 & _ & _).
    assert (SHS : sh (al_space AL + K_SPACE + 4096) <= 17594333495296) by (unfold sh, SHADOW_OFF; clear - SP5; Z.div_mod_to_equations; lia).
    assert (FW : Forall (atouch AL lo (A + n) (fst X) (snd X) [] []) [(A, A + n)]).
    { constructor; [| constructor]. left. unfold sub_iv. cbn [fst snd]. clear - LA N0. lia. }
    assert (TCH : Forall (held1 (fst X)) []) by constructor.
    assert (TSI : incl (@nil schunk) (se_chunks (snd X))) by (intros d []).
    unfold dr_inv.
    split. { apply (RPRIM_frame AL AO (fst X) _ m m' RP MU WM). unfold prim_clear. repeat (apply Forall_cons || apply Forall_nil). left. unfold prim_out. cbn [fst snd].
             clear - LA N0 LOH CLO ACR T3 T4 SP2 SHS. repeat split; lia. }
    split; [exact POK|].
    split. { eapply (RSEC_frame_pzone AL (snd X) _ m m' lo AO LOH CLO RS MU WM). constructor; [| constructor]. unfold pzone. cbn [fst snd]. right. right. right. exact LA. }
    split; [exact MI'|].
    split. { eapply poison_env_frame; [exact PE| exact MU| exact WM|]. clear - LA N0 CLO ACR. env_clear. }
    split. { eapply thread_env_frame; [exact TE| exact MU| exact WM|]. clear - LA N0 CLO ACR T1 T2 T3 T4 T5. env_clear. }
    split; [eapply shvis_wmono; [exact SV| exact WM]|].
    split; [exact WFS|].
    split.
    { apply Forall_forall. intros ch' Hin.
      eapply (qchunk_rep_other AL X m m' lo (A + n) _ [] [] ch' AO LOH CLO RP RS TCH TSI MU FW).
      - exact (proj1 (Forall_forall _ _) WFS ch' Hin).
      - exact (proj1 (Forall_forall _ _) REPS ch' Hin).
      - exact (proj1 (Forall_forall _ _) HKS ch' Hin).
      - intros cv _ [].
      - intros sc _ []. }
    split; [exact HKS|]. split; [exact HOK|]. split; [exact NDS|]. split; [exact BWF|].
    apply Forall_forall. intros b' Hb. destruct (proj1 (Forall_forall _ _) BREP b' Hb) as [nx RB]. exists nx.
    eapply (qbatch_rep_other AL X m m' lo (A + n) _ [] [] b' nx AO LOH CLO RP RS TCH TSI MU FW RB).
    - destruct HOK as [_ FH]. apply (proj1 (Forall_forall _ _) FH). apply in_or_app. left. apply in_map. exact Hb.
    - intros [].
  Qed.

  Definition dr_inner_post (X : pstate) (H : word -> bool) (m : mem) (b : qbatch) (WB : list qbatch) (WCo : list qchunk) (hrest : list (Z * Z))
      (rest : list qchunk) (junk : list byte) (r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 rra : word) (cells : list cell)
    : unit -> (word -> bool) -> machine_state -> Prop :=
    fun _ H' ms' => exists xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' W,
      ms' = MS (mkR xra (wz (q - 112)) gp (wz A0_TP) t0 t1 t2 (wz C) (wz INSTANCE) a0 a1 a2 a3 a4 a5 a6 a7
                    (wz SEC) (wz GSTATS) (wz (qb_addr AL b)) (wz 137438953472) (wz (qb_count b)) (wz (qb_addr AL b + 152 + 8 * qb_count b))
                    (wz (qb_count b + 16)) (wz (16 + qb_count b)) s10 s11 t3 t4 t5 t6)
               F_ (wz 0x35830) fc None m' (seg_rom asegs)
      /\ H' = H_recycle_chunks AL X rest H
      /\ munch W m m' /\ Forall (atouch AL lo (q - 112) (fst X) (snd X) (flat_map prim_of rest) (flat_map sec_of rest)) W
      /\ dr_inv AL E (recycle_chunks X rest) H' m' (b :: WB) WCo hrest
      /\ xle X (recycle_chunks X rest)
      /\ dr_mach m' junk r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 rra cells.

  #[using="AO LOH CLO LOQ QH Q16 QC"] Lemma dr_inner : forall (rest pre : list qchunk) (X : pstate) (H : word -> bool) (m : mem) (b : qbatch) (WB : list qbatch) (WCo : list qchunk)
        (hrest : list (Z * Z)) (junk : list byte) (r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 rra : word) (cells : list cell)
        (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    qb_chunks b = pre ++ rest -> rest <> [] -> qb_count b <= Q_BATCH -> mclean H m ->
    dr_inv AL E X H m (b :: WB) (rest ++ WCo) hrest ->
    dr_mach m junk r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 rra cells ->
    implA H (t_recycle_chunks AL X rest)
      (dr_inner_post X H m b WB WCo hrest rest junk r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 rra cells)
      (MS (mkR xra (wz (q - 112)) gp (wz A0_TP) t0 t1 t2 (wz C) (wz INSTANCE) a0 a1 a2 a3 a4 a5 a6 a7
               (wz SEC) (wz GSTATS) (wz (qb_addr AL b)) (wz 137438953472) (wz (qb_count b)) (wz (qb_addr AL b + 152 + 8 * Z.of_nat (length pre)))
               (wz (qb_count b + 16)) (wz (16 + Z.of_nat (length pre))) s10 s11 t3 t4 t5 t6)
          F_ (wz 0x35818) fc None m (seg_rom asegs)).
  Proof.
    induction rest as [|ch rest IH]; intros pre X H m b WB WCo hrest junk r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 rra cells
      xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 ECH NE CNT MC INV MACH; [contradiction|]. clear NE.
    assert (LQ : lo <= q - 112 - AREC_STACK) by (unfold DOREC_STACK in LOQ; lia).
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof INV as (RP & POK & RS & MI & PE & TE & SV & WFS & REPS & HKS & HOK & NDS & BWF & BREP).
    destruct MACH as (ST & (F1 & F2 & F3) & CC).
    apply Forall_cons_iff in BREP as [(nx & RB) BREP']. pose proof RB as (RB1 & (ws & RB2 & LW & FW) & RB3).
    set (i := Z.of_nat (length pre)) in *.
    assert (CNTE : qb_count b = i + 1 + Z.of_nat (length rest)) by (unfold qb_count, i; rewrite ECH, length_app; cbn [length]; lia).

    assert (NTH : nth_error ws (Z.to_nat i) = Some (wz (qc_hdr AL ch))).
    { assert (N1 : nth_error (firstn (length (qb_chunks b)) ws) (Z.to_nat i) = Some (wz (qc_hdr AL ch))).
      { rewrite FW, ECH. rewrite nth_error_map. unfold i. rewrite Nat2Z.id. rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity. }
      rewrite nth_error_firstn in N1. destruct (Nat.ltb_spec (Z.to_nat i) (length (qb_chunks b))); [exact N1| discriminate]. }

    cbn [t_recycle_chunks].
    pose proof (u64arr_read asegs m (qb_addr AL b + 24) ws i _ (wa (qb_addr AL b + 24 + 8 * i)) RB2 NTH ltac:(unfold i; lia) eq_refl) as HR.
    assert (HB : held1 (fst X) (bpair b)) by (destruct HOK as [_ FH]; apply (proj1 (Forall_forall _ _) FH); left; reflexivity).
    assert (BA : al_space AL <= qb_addr AL b /\ qb_addr AL b + 8192 <= al_space AL + K_SPACE).
    { destruct (clear_ctx AL X m RP RS) as (WF0 & _). pose proof (held_geo AL (fst X) AO WF0 K_BCLASS (qb_v b) HB) as G. cbv zeta in G.
      destruct G as (_ & G1 & G2 & G3 & _). pose proof (region_range AL K_BCLASS ltac:(lia)) as [R1 R2].
      change (class_size K_BCLASS) with 8192 in G2. unfold qb_addr. clear - G1 G2 G3 R1 R2. lia. }
    layout_facts AO 0%nat SPF. destruct SPF as (SP1 & SP2 & _ & _ & SP5 & _ & _).
    lz_go.
    replace (qb_addr AL b + 152 + 8 * i) with (qb_addr AL b + 24 + 8 * i + 128) by lia.
    zstep.

    zstep.
    zstep.
    replace (q - 112 + 8) with (q - 104) by lia.

    apply Forall_cons_iff in WFS as [WFc WFS']. apply Forall_cons_iff in REPS as [REPc REPS']. apply Forall_cons_iff in HKS as [HKc HKS'].
    assert (Q16' : (q - 112) mod 16 = 0) by (clear - Q16; Z.div_mod_to_equations; lia).
    lz_here.
    eapply implA_ebind.
    { eapply implA_mclean; [exact MC|].
      eapply (arec_any AL E (wz 219172) gp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F_ fc m H (q - 112) lo (q - 104) X ch stackw);
        [ exact AO | exact MI | exact MC | exact SV | exact PE | exact TE | exact ST | exact LOH | exact CLO | exact LQ | clear - QH; lia | exact Q16'
        | exact RP | exact POK | exact RS | exact WFc | exact REPc | exact HKc | exact F2 | clear; lia | clear - QH; lia ]. }
    intros u H1 ms1 [PO MC1]. unfold arec_post in PO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & W1 & -> & -> & MUd & FWd & MId & STd & PEd & TEd & SVd & RPd & POKd & RSd).
    clean_ms_mem MC1.
    pose proof (dr_inv_chunk AL E X H _ m m1 ch (rest ++ WCo) (b :: WB) hrest lo (q - 112) W1 AO LOH CLO INV MUd FWd MId PEd TEd SVd RPd POKd RSd) as INV1.
    assert (TCH : Forall (held1 (fst X)) (prim_of ch)).
    { destruct ch as [[c v|sc] rz n]; cbn [prim_of qc_kind]; [| constructor]. constructor; [exact HKc| constructor]. }
    assert (TSI : incl (sec_of ch) (se_chunks (snd X))).
    { destruct ch as [[c v|sc] rz n]; cbn [sec_of qc_kind]; intros d Hd; [destruct Hd|]. destruct Hd as [<-|[]]. exact HKc. }
    destruct (dr_cross X m m1 W1 (prim_of ch) (sec_of ch) junk r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 rra cells RP RS TCH TSI MUd FWd (conj F1 (conj F2 F3)) CC) as [FR1 CC1].
    pose proof (xle_recycle1 X m ch RP RS WFc HKc) as XL1.
    lz_go.
    replace (ret_pc (Z_to_bv 64 219172)) with (Z_to_bv 64 219172) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    do 2 zstep.
    zstep. if_cases KB; zify_cond KB.

    -
      assert (NE : rest <> []) by (intros ->; cbn [length] in CNTE; clear - CNTE KB; lia).
      assert (EL : Z.of_nat (length (pre ++ [ch])) = i + 1) by (rewrite length_app; cbn [length]; unfold i; lia).
      replace (qb_addr AL b + 24 + 8 * i + 136) with (qb_addr AL b + 152 + 8 * Z.of_nat (length (pre ++ [ch]))) by (rewrite EL; lia).
      replace (16 + i + 1) with (16 + Z.of_nat (length (pre ++ [ch]))) by (rewrite EL; lia).
      lz_here.
      eapply implA_mono.
      { eapply (IH (pre ++ [ch]) (recycle1 X ch) _ m1 b WB WCo hrest junk r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 rra cells);
          [ rewrite <- app_assoc; exact ECH | exact NE | exact CNT | assumption | exact INV1 | exact (conj STd (conj FR1 CC1)) ]. }
      intros u' H2 ms2 PO. unfold dr_inner_post in PO |- *.
      destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & y15 & m2 & W2 & -> & -> & MU2 & FW2 & INV2 & XL2 & MACH2).
      exists y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, m2, (W1 ++ W2).
      split; [reflexivity|]. split; [reflexivity|].
      split. { eapply munch_trans; [eapply munch_weaken; [| exact MUd]| eapply munch_weaken; [| exact MU2]]; unfold sub_fp; intros xo O; apply outside_app in O as [O1 O2]; assumption. }
      split.
      { apply Forall_app. split.
        - eapply (atouch_xle X X lo (q - 112) _ _ (prim_of ch) (sec_of ch) W1 (xle_refl X)); [| | exact FWd]; cbn [flat_map]; apply incl_appl; apply incl_refl.
        - eapply (atouch_xle X (recycle1 X ch) lo (q - 112) _ _ _ _ W2 XL1); [| | exact FW2]; cbn [flat_map]; apply incl_appr; apply incl_refl. }
      split; [exact INV2|]. split; [exact (xle_trans _ _ _ XL1 XL2)| exact MACH2].
    -
      assert (EN : rest = []) by (destruct rest as [|x l]; [reflexivity| cbn [length] in CNTE; clear - CNTE KB; lia]).
      subst rest. cbn [t_recycle_chunks length] in *.
      replace (qb_addr AL b + 24 + 8 * i + 136) with (qb_addr AL b + 152 + 8 * qb_count b) by (clear - CNTE; lia).
      replace (16 + i + 1) with (16 + qb_count b) by (clear - CNTE; lia).
      lz_ret. apply evt_done. unfold dr_inner_post.
      do 16 eexists. exists m1, W1. split; [reflexivity|]. split; [reflexivity|].
      split; [exact MUd|]. split; [cbn [flat_map]; rewrite !app_nil_r; exact FWd|].
      split; [exact INV1|]. split; [exact XL1| exact (conj STd (conj FR1 CC1))].
  Qed.

  Definition dr_btail_post (X1 : pstate) (H1 : word -> bool) (m1 : mem) (b : qbatch) (WB : list qbatch) (WCo : list qchunk) (hrest : list (Z * Z))
      (junk : list byte) (r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 rra : word) (n : Z) (crest : list cell) (x6 x7 x8 x9 : word)
    : unit -> (word -> bool) -> machine_state -> Prop :=
    fun _ H' ms' => exists xra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      let P' := cache_dealloc (fst X1) K_BCLASS (qb_v b) in
      let W := prim_W AL lo (q - 112) K_BCLASS (get_cls (fst X1) K_BCLASS) (get_cls P' K_BCLASS) in
      ms' = MS (mkR xra (wz (q - 112)) gp (wz A0_TP) t0 t1 t2 (wz C) (wz INSTANCE) (wz n) a1 a2 a3 a4 a5 a6 a7
                    (wz SEC) (wz GSTATS) (wz (qb_addr AL b)) (wz 137438953472) x6 x7 x8 x9 s10 s11 t3 t4 t5 t6)
               F_ (wz 0x35860) fc None m' (seg_rom asegs)
      /\ H' = H_cdealloc AL (fst X1) K_BCLASS H1
      /\ munch W m1 m' /\ Forall (atouch AL lo (q - 112) (fst X1) (snd X1) [bpair b] []) W
      /\ dr_inv AL E (P', snd X1) H' m' WB WCo hrest
      /\ dr_mach m' junk r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 rra (C8 (wz n) :: crest).

  #[using="AO LOH CLO LOQ QH Q16 QC"] Lemma dr_btail : forall (X1 : pstate) (H1 : word -> bool) (m1 : mem) (b : qbatch) (WB : list qbatch) (WCo : list qchunk) (hrest : list (Z * Z))
        (junk : list byte) (r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 rra : word) (n : Z) (crest : list cell)
        (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x6 x7 x8 x9 t3 t4 t5 t6 : word),
    mclean H1 m1 ->
    dr_inv AL E X1 H1 m1 (b :: WB) WCo hrest ->
    dr_mach m1 junk r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 rra (C8 (wz n) :: crest) ->
    implA H1 (t_cdealloc AL K_BCLASS (get_cls (fst X1) K_BCLASS))
      (dr_btail_post X1 H1 m1 b WB WCo hrest junk r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 rra n crest x6 x7 x8 x9)
      (MS (mkR xra (wz (q - 112)) gp (wz A0_TP) t0 t1 t2 (wz C) (wz INSTANCE) a0 a1 a2 a3 a4 a5 a6 a7
               (wz SEC) (wz GSTATS) (wz (qb_addr AL b)) (wz 137438953472) x6 x7 x8 x9 s10 s11 t3 t4 t5 t6)
          F_ (wz 0x35830) fc None m1 (seg_rom asegs)).
  Proof.
    intros X1 H1 m1 b WB WCo hrest junk r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 rra n crest
      xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x6 x7 x8 x9 t3 t4 t5 t6 MC INV MACH.
    assert (LQ : lo <= q - 112 - CDEALLOC_STACK) by (unfold DOREC_STACK, AREC_STACK in LOQ; lia).
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof INV as (RP & POK & RS & MI & PE & TE & SV & WFS & REPS & HKS & HOK & NDS & BWF & BREP).
    destruct MACH as (ST & (F1 & F2 & F3) & CC).
    apply Forall_cons_iff in BREP as [(nx & RB) BREP'].
    assert (HB : held1 (fst X1) (bpair b)) by (destruct HOK as [_ FH]; apply (proj1 (Forall_forall _ _) FH); left; reflexivity).
    destruct (clear_ctx AL X1 m1 RP RS) as (WF0 & _).
    pose proof (held_geo AL (fst X1) AO WF0 K_BCLASS (qb_v b) HB) as G. cbv zeta in G.
    destruct G as (_ & G1 & G2 & G3 & _). pose proof (region_range AL K_BCLASS ltac:(lia)) as [R1 R2].
    change (class_size K_BCLASS) with 8192 in G2. fold (qb_addr AL b) in G1, G2.
    destruct HB as (_ & V0 & VAU & VAL & VNI). cbn [fst snd bpair] in V0, VAU, VAL, VNI.
    layout_facts AO 0%nat SPF. destruct SPF as (SP1 & SP2 & _ & _ & SP5 & _ & _).
    pose proof RP as (LEN & PENV & _). pose proof PENV as PENVC. unfold prim_env in PENVC.
    assert (Q16' : (q - 112) mod 16 = 0) by (clear - Q16; Z.div_mod_to_equations; lia).
    pose proof (qbatch_free_chunk AL m1 b nx RB) as FCB.
    rewrite <- (ebind_ret_r (t_cdealloc AL K_BCLASS (get_cls (fst X1) K_BCLASS))).
    lz_go.
    zstep.

    zstep. if_cases K1; zify_cond K1. { exfalso. clear - K1 G1 R1 SP1 SP5. lia. } clear K1.
    zstep.
    zstep. if_cases K2; zify_cond K2. { exfalso. clear - K2 G1 G2 G3 R1 R2 SP1 SP5. lia. } clear K2.
    assert (FRJ : rw_cells asegs m1 (q - 112) [CB 8 junk; C8 (wz CACHE); C8 stackw; C8 r9; C8 r8; C8 r7; C8 r6; C8 r5; C8 r4; C8 r3; C8 r2; C8 r1; C8 r0; C8 rra]).
    { apply (rw_cells_put3 asegs m1 (q - 112) [CB 8 junk] [C8 (wz CACHE); C8 stackw] _ F1); cbn [cells_size csize Nat.add].
      - replace (q - 112 + Z.of_nat 8) with (q - 104) by lia. exact F2.
      - replace (q - 112 + Z.of_nat 8 + Z.of_nat 16) with (q - 88) by lia. exact F3. }
    zstep.
    do 3 zstep.

    assert (ECL : Z.shiftr ((Z.shiftl (qb_addr AL b - al_space AL) 27) mod 18446744073709551616) 59 = K_BCLASS).
    { unfold qb_addr, region. replace (al_space AL + K_BCLASS * K_REGION + 16 * qb_v b - al_space AL) with (K_BCLASS * 4294967296 + 16 * qb_v b) by lia.
      rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
      assert (V32 : 0 <= 16 * qb_v b < 4294967296) by (clear - V0 VAU G3; change (class_size K_BCLASS) with 8192 in VAU; lia).
      rewrite Z.mod_small by (change (2^27) with 134217728; clear - V32; lia).
      replace ((K_BCLASS * 4294967296 + 16 * qb_v b) * 2 ^ 27) with (K_BCLASS * 2^59 + 16 * qb_v b * 2^27) by (change (2^59) with (4294967296 * 2^27); lia).
      rewrite Z.div_add_l by lia. rewrite Z.div_small by (change (2^27) with 134217728; change (2^59) with 576460752303423488; clear - V32; lia). lia. }
    rewrite ECL. clear ECL.
    do 2 zstep.
    zstep.
    lz_here.
    eapply implA_ebind.
    { eapply implA_mclean; [exact MC|].
      eapply (cdealloc_spec AL E (wz 219228) gp _ _ _ (wz C) (wz INSTANCE) _ _ _ _ (wz SEC) (wz GSTATS) (wz (qb_addr AL b)) (wz 137438953472) x6 x7 x8 x9 s10 s11 _ _ _ _ F_ fc m1 H1 (q - 112) lo K_BCLASS (qb_v b) (fst X1) AO);
        [ exact MI | exact MC | exact SV | exact PE | exact TE | exact ST | exact LOH | exact CLO | exact LQ | clear - QH; lia | exact Q16'
        | clear; lia | exact RP | exact POK | exact V0 | exact VAU | exact VAL | exact VNI | exact FCB ]. }
    intros u H2 ms2 [PO MC2]. unfold cache_dealloc_post in PO. cbv zeta in PO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & -> & -> & MUd & WMd & MId & STd & PEd & TEd & SVd & RPd & POKd).
    clean_ms_mem MC2.

    destruct (dr_inv_batch AL E X1 H1 _ m1 m2 b WB WCo hrest lo (q - 112) AO LOH CLO INV MUd WMd MId PEd TEd SVd RPd POKd) as [INV2 FW2].
    assert (TCH : Forall (held1 (fst X1)) [bpair b]).
    { constructor; [| constructor]. destruct HOK as [_ FH]. apply (proj1 (Forall_forall _ _) FH). left. reflexivity. }
    assert (TSI : incl (@nil schunk) (se_chunks (snd X1))) by (intros d []).
    destruct (dr_cross X1 m1 m2 _ [bpair b] [] junk r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 rra (C8 (wz n) :: crest) RP RS TCH TSI MUd FW2 (conj F1 (conj F2 F3)) CC) as [FR2 CC2].
    clear FRJ.
    lz_go.
    replace (ret_pc (Z_to_bv 64 219228)) with (Z_to_bv 64 219228) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    zstep.

    lz_ret. apply evt_done. unfold dr_btail_post. cbv zeta.
    do 15 eexists. exists m2. split; [reflexivity|]. split; [reflexivity|].
    split; [exact MUd|]. split; [exact FW2|]. split; [exact INV2|]. exact (conj STd (conj FR2 CC2)).
  Qed.

  #[using="Type"] Lemma NoDup_app_disj : forall {T} (l1 l2 : list T) x, List.NoDup (l1 ++ l2) -> In x l1 -> ~ In x l2.
  Proof.
    induction l1 as [|y l1 IH]; intros l2 x ND H1; [destruct H1|]. cbn [app] in ND. apply NoDup_cons_iff in ND as [NI ND].
    destruct H1 as [->|H1]; [intros H2; apply NI; apply in_or_app; right; exact H2| exact (IH l2 x ND H1)].
  Qed.

  #[using="Type"] Lemma dr_inv_tc : forall X H (m : mem) WB chs WCo hrest, dr_inv AL E X H m WB (chs ++ WCo) hrest ->
    Forall (held1 (fst X)) (flat_map prim_of chs) /\ incl (flat_map sec_of chs) (se_chunks (snd X)).
  Proof.
    intros X H m WB chs WCo hrest (_ & _ & _ & _ & _ & _ & _ & _ & _ & HKS & _).
    apply Forall_app in HKS as [HK _]. split.
    - apply Forall_forall. intros cv Hin. apply in_flat_map in Hin as (ch & Hch & Hcv). pose proof (proj1 (Forall_forall _ _) HK ch Hch) as K.
      destruct ch as [[c v|sc] rz n]; unfold held_kind in K; cbn [prim_of sec_of qc_kind] in *; [destruct Hcv as [<-|[]]; exact K| destruct Hcv].
    - intros sc Hin. apply in_flat_map in Hin as (ch & Hch & Hsc). pose proof (proj1 (Forall_forall _ _) HK ch Hch) as K.
      destruct ch as [[c v|sc'] rz n]; unfold held_kind in K; cbn [prim_of sec_of qc_kind] in *; [destruct Hsc| destruct Hsc as [<-|[]]; exact K].
  Qed.

  #[using="Type"] Lemma dr_inv_bheld : forall X H (m : mem) WB chs WCo hrest b', dr_inv AL E X H m WB (chs ++ WCo) hrest -> In b' WB ->
    held1 (fst X) (bpair b') /\ ~ In (bpair b') (flat_map prim_of chs).
  Proof.
    intros X H m WB chs WCo hrest b' (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & [ND FH] & _) Hb.
    split. { apply (proj1 (Forall_forall _ _) FH). apply in_or_app. left. apply in_map. exact Hb. }
    intros Hin. rewrite flat_map_app in ND.
    apply (NoDup_app_disj (map bpair WB) ((flat_map prim_of chs ++ flat_map prim_of WCo) ++ hrest) (bpair b') ND); [apply in_map; exact Hb|].
    apply in_or_app. left. apply in_or_app. left. exact Hin.
  Qed.

  #[using="AO"] Lemma dr_qlist_other : forall X H (m m' : mem) WB WC hrest lo1 q1 W tc tsc l nxt,
    dr_inv AL E X H m WB WC hrest -> Forall (held1 (fst X)) tc -> incl tsc (se_chunks (snd X)) ->
    munch W m m' -> Forall (atouch AL lo1 q1 (fst X) (snd X) tc tsc) W -> 0x10007fff8000 <= lo1 -> alloc_ceiling <= lo1 ->
    qlist_rep AL m l nxt -> (forall b', In b' l -> held1 (fst X) (bpair b') /\ ~ In (bpair b') tc) -> qlist_rep AL m' l nxt.
  Proof.
    intros X H m m' WB WC hrest lo1 q1 W tc tsc l nxt (RP & _ & RS & _) TCH TSI MU FW L1 L2 QL HB.
    eapply (qlist_rep_other AL X m m' lo1 q1 W tc tsc l nxt AO L1 L2 RP RS TCH TSI MU FW QL). apply Forall_forall. exact HB.
  Qed.

  Variables (RQB : list qbatch) (RQC : list qchunk).

  Definition dr_batch_post (X : pstate) (H : word -> bool) (m : mem) (b : qbatch) (bs : list qbatch) (hrest : list (Z * Z))
      (junk : list byte) (r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 rra : word) (n : Z) (crest : list cell) (Wpre : list (Z * Z))
    : unit -> (word -> bool) -> machine_state -> Prop :=
    fun _ H' ms' => exists xra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x6 x7 x8 x9 t3 t4 t5 t6 m' W,
      ms' = MS (mkR xra (wz (q - 112)) gp (wz A0_TP) t0 t1 t2 (wz C) (wz INSTANCE) (wz n) a1 a2 a3 a4 a5 a6 a7
                    (wz SEC) (wz GSTATS) (wz (qb_addr AL b)) (wz 137438953472) x6 x7 x8 x9 s10 s11 t3 t4 t5 t6)
               F_ (wz 0x35860) fc None m' (seg_rom asegs)
      /\ H' = H_recycle_batch AL X b H
      /\ munch (Wpre ++ W) m m'
      /\ Forall (atouch AL lo (q - 112) (fst X) (snd X) (bpair b :: flat_map prim_of (qb_chunks b)) (flat_map sec_of (qb_chunks b))) W
      /\ dr_inv AL E (recycle_batch X b) H' m' (bs ++ RQB) (flat_map qb_chunks bs ++ RQC) hrest
      /\ xle X (recycle_batch X b)
      /\ qlist_rep AL m' bs 0
      /\ dr_mach m' junk r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 rra (C8 (wz n) :: crest).

  #[using="AO LOH CLO LOQ QH Q16 QC"] Lemma dr_batch3 : forall (X : pstate) (H : word -> bool) (m m1 : mem) (W1 : list (Z * Z)) (b : qbatch) (bs : list qbatch) (hrest : list (Z * Z))
        (junk : list byte) (r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 rra : word) (n : Z) (crest : list cell)
        (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x6 x7 x8 x9 t3 t4 t5 t6 : word),
    let X1 := recycle_chunks X (qb_chunks b) in let H1 := H_recycle_chunks AL X (qb_chunks b) H in
    mclean H1 m1 ->
    munch W1 m m1 -> Forall (atouch AL lo (q - 112) (fst X) (snd X) (flat_map prim_of (qb_chunks b)) (flat_map sec_of (qb_chunks b))) W1 ->
    dr_inv AL E X1 H1 m1 (b :: bs ++ RQB) (flat_map qb_chunks bs ++ RQC) hrest -> xle X X1 -> qlist_rep AL m1 bs 0 ->
    dr_mach m1 junk r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 rra (C8 (wz n) :: crest) ->
    implA H1 (t_cdealloc AL K_BCLASS (get_cls (fst X1) K_BCLASS))
      (dr_batch_post X H m b bs hrest junk r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 rra n crest [])
      (MS (mkR xra (wz (q - 112)) gp (wz A0_TP) t0 t1 t2 (wz C) (wz INSTANCE) a0 a1 a2 a3 a4 a5 a6 a7
               (wz SEC) (wz GSTATS) (wz (qb_addr AL b)) (wz 137438953472) x6 x7 x8 x9 s10 s11 t3 t4 t5 t6)
          F_ (wz 0x35830) fc None m1 (seg_rom asegs)).
  Proof.
    intros X H m m1 W1 b bs hrest junk r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 rra n crest
      xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x6 x7 x8 x9 t3 t4 t5 t6 X1 H1 MC MU1 FW1 INV XL QL MACH.
    eapply implA_mono.
    { exact (dr_btail X1 H1 m1 b (bs ++ RQB) (flat_map qb_chunks bs ++ RQC) hrest junk r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 rra n crest
               xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x6 x7 x8 x9 t3 t4 t5 t6 MC INV MACH). }
    intros u H2 ms2 PO. unfold dr_btail_post in PO. cbv zeta in PO.
    destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m2 & -> & -> & MU2 & FW2 & INV2 & MACH2).
    set (W2 := prim_W AL lo (q - 112) K_BCLASS (get_cls (fst X1) K_BCLASS) (get_cls (cache_dealloc (fst X1) K_BCLASS (qb_v b)) K_BCLASS)) in *.
    unfold dr_batch_post.
    exists y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, x6, x7, x8, x9, y11, y12, y13, y14, m2, (W1 ++ W2).
    split; [reflexivity|]. split; [reflexivity|].
    split. { cbn [app]. eapply munch_trans; [eapply munch_weaken; [| exact MU1]| eapply munch_weaken; [| exact MU2]]; unfold sub_fp; intros xo O; apply outside_app in O as [O1 O2]; assumption. }
    split.
    { apply Forall_app. split.
      - eapply (atouch_xle X X lo (q - 112) _ _ _ _ W1 (xle_refl X)); [| | exact FW1]; [apply incl_tl|]; apply incl_refl.
      - eapply (atouch_xle X X1 lo (q - 112) _ _ [bpair b] [] W2 XL); [| | exact FW2]; [intros cv [<-|[]]; left; reflexivity| intros d []]. }
    split; [exact INV2|].
    split.
    { pose proof INV as (RP1 & _). pose proof RP1 as (LEN1 & _). eapply xle_trans; [exact XL|]. unfold recycle_batch. fold X1. split; cbn [fst snd]; [| apply incl_refl].
      intros c Hc. rewrite (p_au_cdealloc (fst X1) K_BCLASS (qb_v b) c LEN1 ltac:(lia)). lia. }
    split; [| exact MACH2].
    assert (TCH : Forall (held1 (fst X1)) [bpair b]).
    { constructor; [| constructor]. destruct INV as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & [_ FH] & _). apply (proj1 (Forall_forall _ _) FH). left. reflexivity. }
    eapply (dr_qlist_other X1 H1 m1 m2 (b :: bs ++ RQB) _ hrest lo (q - 112) W2 [bpair b] [] bs 0 INV TCH ltac:(intros d []) MU2 FW2 LOH CLO QL).
    intros b' Hb. destruct INV as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & [ND FH] & _).
    split. { apply (proj1 (Forall_forall _ _) FH). right. apply in_or_app. left. apply in_map. apply in_or_app. left. exact Hb. }
    intros [EQ|[]]. cbn [map app] in ND. apply NoDup_cons_iff in ND as [NI _]. apply NI. rewrite EQ. apply in_or_app. left. apply in_map. apply in_or_app. left. exact Hb.
  Qed.

  #[using="AO LOH CLO LOQ QH Q16 QC C47"] Lemma dr_batch2 : forall (X : pstate) (H : word -> bool) (m : mem) (b : qbatch) (bs : list qbatch) (hrest : list (Z * Z))
        (junk : list byte) (r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 rra : word) (c1 lw bw : word)
        (xra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x6 x7 x8 x9 t3 t4 t5 t6 : word),
    let nb := Z.of_nat (length bs) in
    mclean H m ->
    dr_inv AL E X H m (b :: bs ++ RQB) (qb_chunks b ++ flat_map qb_chunks bs ++ RQC) hrest -> qlist_rep AL m (b :: bs) 0 ->
    dr_mach m junk r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 rra [C8 (wz (nb + 1)); C8 c1; C8 lw; C8 bw] ->
    implA H (t_recycle_batch AL X b)
      (fun u H' ms' => exists bw', dr_batch_post X H m b bs hrest junk r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 rra nb [C8 c1; C8 lw; C8 bw'] [(C, C + 32)] u H' ms')
      (MS (mkR xra (wz (q - 112)) gp (wz A0_TP) t0 t1 t2 (wz C) (wz INSTANCE) (wz (nb + 1)) a1 a2 a3 a4 a5 a6 a7
               (wz SEC) (wz GSTATS) (wz (qb_addr AL b)) (wz 137438953472) x6 x7 x8 x9 s10 s11 t3 t4 t5 t6)
          F_ (wz 0x357ec) fc None m (seg_rom asegs)).
  Proof.
    intros X H m b bs hrest junk r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 rra c1 lw bw
      xra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x6 x7 x8 x9 t3 t4 t5 t6 nb MC INV QL MACH.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    assert (LQ : lo <= q - 112) by (unfold DOREC_STACK, AREC_STACK, CDEALLOC_STACK, MF_STACK in LOQ; lia).
    pose proof INV as (RP & POK & RS & MI & PE & TE & SV & WFS & REPS & HKS & HOK & NDS & BWF & BREP).
    destruct MACH as (ST & (F1 & F2 & F3) & CC).
    pose proof QL as [RB QL']. cbn [qlist_rep] in QL'. pose proof RB as (RB1 & _).
    apply Forall_cons_iff in BWF as [(_ & _ & CNT & _) _].
    assert (HB : held1 (fst X) (bpair b)) by (destruct HOK as [_ FH]; apply (proj1 (Forall_forall _ _) FH); left; reflexivity).
    assert (BA : al_space AL <= qb_addr AL b /\ qb_addr AL b + 8192 <= al_space AL + K_SPACE).
    { destruct (clear_ctx AL X m RP RS) as (WF0 & _). pose proof (held_geo AL (fst X) AO WF0 K_BCLASS (qb_v b) HB) as G. cbv zeta in G.
      destruct G as (_ & G1 & G2 & G3 & _). pose proof (region_range AL K_BCLASS ltac:(lia)) as [R1 R2].
      change (class_size K_BCLASS) with 8192 in G2. unfold qb_addr. clear - G1 G2 G3 R1 R2. lia. }
    layout_facts AO 0%nat SPF. destruct SPF as (SP1 & SP2 & _ & _ & SP5 & _ & _).
    clear RP POK RS PE TE SV WFS REPS HKS HOK NDS BREP RB HB.
    pose proof (munch_refl [(C, C + 32)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    remember (qb_addr AL b) as BB eqn:HBB in *.
    unfold t_recycle_batch.
    lz_go.
    zstep.

    zstep.
    zstep.
    zstep.
    zstep.
    zstep.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mA end.

    assert (INVA : dr_inv AL E X H mA (b :: bs ++ RQB) (qb_chunks b ++ flat_map qb_chunks bs ++ RQC) hrest)
      by (apply (dr_inv_stack X H m mA _ _ hrest C 32 ltac:(clear - LQ QC; lia) ltac:(lia) INV MU WM MI)).
    assert (QLA : qlist_rep AL mA bs 0).
    { eapply (dr_qlist_other X H m mA _ _ hrest lo (C + 32) [(C, C + 32)] [] [] bs 0 INV ltac:(constructor) ltac:(intros d []) MU); [| exact LOH| exact CLO| exact QL'|].
      - constructor; [| constructor]. left. unfold sub_iv. cbn [fst snd]. clear - LQ QC. lia.
      - intros b' Hb. split; [| intros []]. destruct (dr_inv_bheld X H m (b :: bs ++ RQB) _ _ hrest b' INV (or_intror (in_or_app _ _ _ (or_introl Hb)))) as [HB' _]. exact HB'. }
    assert (CONV : forall u H' ms',
      dr_batch_post X H mA b bs hrest junk r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 rra nb [C8 c1; C8 lw; C8 (Z_to_bv 64 (bv_unsigned bw - qb_size b mod 18446744073709551616))] [] u H' ms' ->
      exists bw', dr_batch_post X H m b bs hrest junk r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 rra nb [C8 c1; C8 lw; C8 bw'] [(C, C + 32)] u H' ms').
    { intros u H' ms' PO. eexists. unfold dr_batch_post in PO |- *.
      destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y18 & m2 & W2 & EQ & EH & MU2 & REST).
      exists y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, m2, W2.
      split; [exact EQ|]. split; [exact EH|]. split; [| exact REST].
      cbn [app] in MU2 |- *. eapply munch_trans; [eapply munch_weaken; [| exact MU]| eapply munch_weaken; [| exact MU2]]; unfold sub_fp; cbn [outside]; intros xo O; tauto. }

    subst BB.
    zstep. if_cases KB; zify_cond KB.
    -
      assert (ECH : qb_chunks b = []) by (unfold qb_count in KB; destruct (qb_chunks b); [reflexivity| cbn [length] in KB; clear - KB; lia]).
      pose proof (dr_batch3 X H mA mA [] b bs hrest junk r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 rra nb
                    [C8 c1; C8 lw; C8 (Z_to_bv 64 (bv_unsigned bw - qb_size b mod 18446744073709551616))]) as B3.
      cbv zeta in B3. rewrite ECH in B3, INVA |- *. cbn [t_recycle_chunks recycle_chunks H_recycle_chunks flat_map app] in B3, INVA |- *.
      lz_here.

      change (ebind (Ret (Ok tt)) (fun _ : unit => t_cdealloc AL 24 (get_cls (fst X) 24))) with (t_cdealloc AL 24 (get_cls (fst X) 24)).
      eapply implA_mono; [| exact CONV].
      eapply B3; [ assumption | apply munch_refl | constructor | exact INVA | apply xle_refl | exact QLA | exact (conj ST (conj (conj F1 (conj F2 F3)) CC)) ].

    -
      assert (NE : qb_chunks b <> []) by (intros EN; unfold qb_count in KB; rewrite EN in KB; cbn [length] in KB; clear - KB; lia).
      do 3 zstep.
      replace (qb_addr AL b + 152) with (qb_addr AL b + 152 + 8 * Z.of_nat (@length qchunk [])) by (cbn [length]; lia).
      lz_here.
      eapply implA_ebind.
      { eapply implA_mclean; [eassumption|].
        eapply (dr_inner (qb_chunks b) [] X H mA b (bs ++ RQB) (flat_map qb_chunks bs ++ RQC) hrest junk r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 rra
                  [C8 (wz nb); C8 c1; C8 lw; C8 (Z_to_bv 64 (bv_unsigned bw - qb_size b mod 18446744073709551616))]);
          [ reflexivity | exact NE | clear - CNT; lia | assumption | exact INVA | exact (conj ST (conj (conj F1 (conj F2 F3)) CC)) ]. }
      intros u H1 ms1 [PO MC1]. unfold dr_inner_post in PO.
      destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & y15 & m1 & W1 & -> & -> & MU1 & FW1 & INV1 & XL1 & MACH1).
      clean_ms_mem MC1.
      destruct (dr_inv_tc X H mA (b :: bs ++ RQB) (qb_chunks b) _ hrest INVA) as [TCH TSI].
      assert (QL1 : qlist_rep AL m1 bs 0).
      { eapply (dr_qlist_other X H mA m1 _ _ hrest lo (q - 112) W1 _ _ bs 0 INVA TCH TSI MU1 FW1 LOH CLO QLA).
        intros b' Hb. exact (dr_inv_bheld X H mA (b :: bs ++ RQB) _ _ hrest b' INVA (or_intror (in_or_app _ _ _ (or_introl Hb)))). }
      eapply implA_mono; [| exact CONV].
      eapply (dr_batch3 X H mA m1 W1 b bs hrest junk r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 rra nb _); [ exact MC1 | exact MU1 | exact FW1 | exact INV1 | exact XL1 | exact QL1 | exact MACH1 ].
  Qed.

  #[using="AO LOH CLO LOQ QH Q16 QC C47"] Lemma dr_batch2s : forall (X : pstate) (H : word -> bool) (m0 m : mem) (b : qbatch) (bs : list qbatch) (hrest : list (Z * Z))
        (junk : list byte) (r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 rra : word) (c1 lw bw : word)
        (xra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x6 x7 x8 x9 t3 t4 t5 t6 : word),
    let nb := Z.of_nat (length bs) in
    mclean H m -> munch [(C, C + 32)] m0 m -> wmono asegs m0 m -> mem_inv asegs m ->
    dr_inv AL E X H m0 (b :: bs ++ RQB) (qb_chunks b ++ flat_map qb_chunks bs ++ RQC) hrest -> qlist_rep AL m0 (b :: bs) 0 ->
    dr_mach m junk r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 rra [C8 (wz (nb + 1)); C8 c1; C8 lw; C8 bw] ->
    implA H (t_recycle_batch AL X b)
      (fun u H' ms' => exists bw', dr_batch_post X H m0 b bs hrest junk r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 rra nb [C8 c1; C8 lw; C8 bw'] [(C, C + 32)] u H' ms')
      (MS (mkR xra (wz (q - 112)) gp (wz A0_TP) t0 t1 t2 (wz C) (wz INSTANCE) (wz (nb + 1)) a1 a2 a3 a4 a5 a6 a7
               (wz SEC) (wz GSTATS) (wz (qb_addr AL b)) (wz 137438953472) x6 x7 x8 x9 s10 s11 t3 t4 t5 t6)
          F_ (wz 0x357ec) fc None m (seg_rom asegs)).
  Proof.
    intros X H m0 m b bs hrest junk r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 rra c1 lw bw
      xra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x6 x7 x8 x9 t3 t4 t5 t6 nb MC MU WM MI INV QL MACH.
    assert (LQ : lo <= q - 112) by (unfold DOREC_STACK, AREC_STACK, CDEALLOC_STACK, MF_STACK in LOQ; lia).
    assert (INVA : dr_inv AL E X H m (b :: bs ++ RQB) (qb_chunks b ++ flat_map qb_chunks bs ++ RQC) hrest)
      by (apply (dr_inv_stack X H m0 m _ _ hrest C 32 ltac:(clear - LQ QC; lia) ltac:(lia) INV MU WM MI)).
    assert (QLA : qlist_rep AL m (b :: bs) 0).
    { eapply (dr_qlist_other X H m0 m _ _ hrest lo (C + 32) [(C, C + 32)] [] [] (b :: bs) 0 INV ltac:(constructor) ltac:(intros d []) MU); [| exact LOH| exact CLO| exact QL|].
      - constructor; [| constructor]. left. unfold sub_iv. cbn [fst snd]. clear - LQ QC. lia.
      - intros b' Hb. split; [| intros []]. destruct INV as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & [_ FH] & _).
        apply (proj1 (Forall_forall _ _) FH). apply in_or_app. left. apply in_map. change (In b' ((b :: bs) ++ RQB)). apply in_or_app. left. exact Hb. }
    eapply implA_mono.
    { exact (dr_batch2 X H m b bs hrest junk r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 rra c1 lw bw
               xra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x6 x7 x8 x9 t3 t4 t5 t6 MC INVA QLA MACH). }
    intros u H' ms' [bw' PO]. exists bw'. unfold dr_batch_post in PO |- *.
    destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y18 & m2 & W2 & EQ & EH & MU2 & REST).
    exists y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, m2, W2.
    split; [exact EQ|]. split; [exact EH|]. split; [| exact REST].
    cbn [app] in MU2 |- *. eapply munch_trans; [eapply munch_weaken; [| exact MU]| exact MU2]. unfold sub_fp; cbn [outside]; intros xo O; tauto.
  Qed.

  #[using="AO LOH CLO LOQ QH Q16 QC C47"] Lemma dr_batch : forall (X : pstate) (H : word -> bool) (m : mem) (b : qbatch) (bs : list qbatch) (hrest : list (Z * Z))
        (junk : list byte) (r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 rra : word) (lw bw : word)
        (xra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x4 x6 x7 x8 x9 t3 t4 t5 t6 : word),
    let nb := Z.of_nat (length bs) in
    mclean H m ->
    dr_inv AL E X H m (b :: bs ++ RQB) (qb_chunks b ++ flat_map qb_chunks bs ++ RQC) hrest -> qlist_rep AL m (b :: bs) 0 ->
    dr_mach m junk r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 rra [C8 (wz (nb + 1)); C8 (wz (qb_addr AL b)); C8 lw; C8 bw] ->
    implA H (t_recycle_batch AL X b)
      (fun u H' ms' => exists lw' bw', dr_batch_post X H m b bs hrest junk r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 rra nb
                                          [C8 (wz (qfirst AL bs)); C8 lw'; C8 bw'] [(C, C + 32)] u H' ms')
      (MS (mkR xra (wz (q - 112)) gp (wz A0_TP) t0 t1 t2 (wz C) (wz INSTANCE) (wz (nb + 1)) a1 a2 a3 a4 a5 a6 a7
               (wz SEC) (wz GSTATS) x4 (wz 137438953472) x6 x7 x8 x9 s10 s11 t3 t4 t5 t6)
          F_ (wz 0x357d8) fc None m (seg_rom asegs)).
  Proof.
    intros X H m b bs hrest junk r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 rra lw bw
      xra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x4 x6 x7 x8 x9 t3 t4 t5 t6 nb MC INV QL MACH.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    assert (LQ : lo <= q - 112) by (unfold DOREC_STACK, AREC_STACK, CDEALLOC_STACK, MF_STACK in LOQ; lia).
    pose proof INV as (RP & _ & RS & MI & _ & _ & _ & _ & _ & _ & HOK & _).
    pose proof MACH as (ST & (F1 & F2 & F3) & CC).
    pose proof QL as [(RB1 & _) _].
    assert (HB : held1 (fst X) (bpair b)) by (destruct HOK as [_ FH]; apply (proj1 (Forall_forall _ _) FH); left; reflexivity).
    assert (BA : al_space AL <= qb_addr AL b /\ qb_addr AL b + 8192 <= al_space AL + K_SPACE).
    { destruct (clear_ctx AL X m RP RS) as (WF0 & _). pose proof (held_geo AL (fst X) AO WF0 K_BCLASS (qb_v b) HB) as G. cbv zeta in G.
      destruct G as (_ & G1 & G2 & G3 & _). pose proof (region_range AL K_BCLASS ltac:(lia)) as [R1 R2].
      change (class_size K_BCLASS) with 8192 in G2. unfold qb_addr. clear - G1 G2 G3 R1 R2. lia. }
    layout_facts AO 0%nat SPF. destruct SPF as (SP1 & SP2 & _ & _ & SP5 & _ & _).
    clear RP RS HOK HB MACH.
    pose proof (munch_refl [(C, C + 32)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    fold (qfirst AL bs) in RB1.
    remember (qb_addr AL b) as BB eqn:HBB in *.
    lz_go.
    zstep.
    zstep.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mA end.
    subst BB.
    zstep. if_cases KB.
    -
      lz_here.
      eapply implA_mono.
      { eapply (dr_batch2s X H m mA b bs hrest junk r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 rra (wz (qfirst AL bs)) lw bw); try eassumption.
        exact (conj ST (conj (conj F1 (conj F2 F3)) CC)). }
      intros u H' ms' [bw' PO]. exists lw, bw'. exact PO.
    -
      sstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mB end.
      lz_here.
      eapply implA_mono.
      { eapply (dr_batch2s X H m mB b bs hrest junk r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 rra (wz (qfirst AL bs)) (wz 0) bw); try eassumption.
        exact (conj ST (conj (conj F1 (conj F2 F3)) CC)). }
      intros u H' ms' [bw' PO]. exists (wz 0), bw'. exact PO.
  Qed.

  #[using="Type"] Lemma dr_frame_join : forall (m : mem) junk r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 rra, dr_frame m junk r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 rra ->
    rw_cells asegs m (q - 112) [CB 8 junk; C8 (wz CACHE); C8 stackw; C8 r9; C8 r8; C8 r7; C8 r6; C8 r5; C8 r4; C8 r3; C8 r2; C8 r1; C8 r0; C8 rra].
  Proof.
    intros m junk r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 rra (F1 & F2 & F3).
    apply (rw_cells_put3 asegs m (q - 112) [CB 8 junk] [C8 (wz CACHE); C8 stackw] _ F1); cbn [cells_size csize Nat.add].
    - replace (q - 112 + Z.of_nat 8) with (q - 104) by lia. exact F2.
    - replace (q - 112 + Z.of_nat 8 + Z.of_nat 16) with (q - 88) by lia. exact F3.
  Qed.

  #[using="LOQ"] Lemma dr_epilogue : forall (m : mem) junk r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 rra
        (xra t0 t1 t2 x0 x1 a0 a1 a2 a3 a4 a5 a6 a7 x2 x3 x4 x5 x6 x7 x8 x9 t3 t4 t5 t6 : word),
    stk asegs m lo (q - 112) -> dr_frame m junk r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 rra ->
    stk asegs m lo q /\
    evt asegs (fun ms' => ms' = MS (mkR rra (wz q) gp (wz A0_TP) t0 t1 t2 r0 r1 a0 a1 a2 a3 a4 a5 a6 a7 r2 r3 r4 r5 r6 r7 r8 r9 s10 s11 t3 t4 t5 t6)
                                   F_ (ret_pc rra) fc None m (seg_rom asegs))
        (MS (mkR xra (wz (q - 112)) gp (wz A0_TP) t0 t1 t2 x0 x1 a0 a1 a2 a3 a4 a5 a6 a7 x2 x3 x4 x5 x6 x7 x8 x9 s10 s11 t3 t4 t5 t6)
            F_ (wz 0x35864) fc None m (seg_rom asegs)).
  Proof.
    intros m junk r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 rra xra t0 t1 t2 x0 x1 a0 a1 a2 a3 a4 a5 a6 a7 x2 x3 x4 x5 x6 x7 x8 x9 t3 t4 t5 t6 ST FR.
    pose proof (dr_frame_join m junk r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 rra FR) as FRJ. clear FR.
    assert (LQ : lo <= q - 112) by (unfold DOREC_STACK, AREC_STACK, CDEALLOC_STACK, MF_STACK in LOQ; lia).
    split.
    { release_frame FRJ ST q. exact ST. }
    do 11 zstep.
    zstep. replace (q - 112 + 112) with q by lia.
    zstep.
    apply evt_done. reflexivity.
  Qed.

  #[using="Type"] Lemma tc_of_head : forall b bs, incl (bpair b :: flat_map prim_of (qb_chunks b)) (tc_of (b :: bs)).
  Proof.
    intros b bs cv [<-|Hin]; unfold tc_of; cbn [map flat_map app]; [left; reflexivity|].
    right. apply in_or_app. right. rewrite flat_map_app. apply in_or_app. left. exact Hin.
  Qed.
  #[using="Type"] Lemma tc_of_tail : forall b bs, incl (tc_of bs) (tc_of (b :: bs)).
  Proof.
    intros b bs cv Hin. unfold tc_of in *. cbn [map flat_map app]. right. apply in_app_or in Hin as [Hin|Hin]; apply in_or_app; [left; exact Hin| right].
    rewrite flat_map_app. apply in_or_app. right. exact Hin.
  Qed.
  #[using="Type"] Lemma tsc_of_head : forall b bs, incl (flat_map sec_of (qb_chunks b)) (tsc_of (b :: bs)).
  Proof. intros b bs sc Hin. unfold tsc_of. cbn [flat_map]. rewrite flat_map_app. apply in_or_app. left. exact Hin. Qed.
  #[using="Type"] Lemma tsc_of_tail : forall b bs, incl (tsc_of bs) (tsc_of (b :: bs)).
  Proof. intros b bs sc Hin. unfold tsc_of in *. cbn [flat_map]. rewrite flat_map_app. apply in_or_app. right. exact Hin. Qed.

  Definition dr_outer_post (X : pstate) (H : word -> bool) (m : mem) (bs : list qbatch) (hrest : list (Z * Z))
      (r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 rra : word) : unit -> (word -> bool) -> machine_state -> Prop :=
    fun _ H' ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' W lw bw,
      ms' = MS (mkR rra (wz q) gp (wz A0_TP) t0 t1 t2 r0 r1 a0 a1 a2 a3 a4 a5 a6 a7 r2 r3 r4 r5 r6 r7 r8 r9 s10 s11 t3 t4 t5 t6)
               F_ (ret_pc rra) fc None m' (seg_rom asegs)
      /\ H' = H_dorecycle AL X bs H
      /\ munch ((C, C + 32) :: W) m m'
      /\ Forall (atouch AL lo (q - 112) (fst X) (snd X) (tc_of bs) (tsc_of bs)) W
      /\ dr_inv AL E (dorecycle X bs) H' m' RQB RQC hrest
      /\ xle X (dorecycle X bs)
      /\ stk asegs m' lo q
      /\ rw_cells asegs m' C [C8 (wz 0); C8 (wz 0); C8 lw; C8 bw].

  #[using="AO LOH CLO LOQ QH Q16 QC C47"] Lemma dr_outer : forall (bs : list qbatch) (b : qbatch) (X : pstate) (H : word -> bool) (m : mem) (hrest : list (Z * Z))
        (junk : list byte) (r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 rra : word) (lw bw : word)
        (xra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x4 x6 x7 x8 x9 t3 t4 t5 t6 : word),
    Z.of_nat (length bs) + 1 < 2^64 ->
    mclean H m ->
    dr_inv AL E X H m (b :: bs ++ RQB) (flat_map qb_chunks (b :: bs) ++ RQC) hrest -> qlist_rep AL m (b :: bs) 0 ->
    dr_mach m junk r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 rra [C8 (wz (Z.of_nat (length bs) + 1)); C8 (wz (qb_addr AL b)); C8 lw; C8 bw] ->
    implA H (t_dorecycle AL X (b :: bs))
      (dr_outer_post X H m (b :: bs) hrest r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 rra)
      (MS (mkR xra (wz (q - 112)) gp (wz A0_TP) t0 t1 t2 (wz C) (wz INSTANCE) (wz (Z.of_nat (length bs) + 1)) a1 a2 a3 a4 a5 a6 a7
               (wz SEC) (wz GSTATS) x4 (wz 137438953472) x6 x7 x8 x9 s10 s11 t3 t4 t5 t6)
          F_ (wz 0x357d8) fc None m (seg_rom asegs)).
  Proof.
    induction bs as [|b' bs IH]; intros b X H m hrest junk r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 rra lw bw
      xra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x4 x6 x7 x8 x9 t3 t4 t5 t6 NB MC INV QL MACH.
    -
      cbn [t_dorecycle]. cbn [flat_map] in INV. rewrite <- app_assoc in INV.
      eapply implA_ebind.
      { eapply implA_mclean; [exact MC|].
        exact (dr_batch X H m b [] hrest junk r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 rra lw bw
                 xra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x4 x6 x7 x8 x9 t3 t4 t5 t6 MC INV QL MACH). }
      intros u H1 ms1 [(lw' & bw' & PO) MC1]. unfold dr_batch_post in PO.
      destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y18 & m1 & W1 & -> & -> & MU1 & FW1 & INV1 & XL1 & QL1 & MACH1).
      clean_ms_mem MC1. destruct MACH1 as (ST1 & FR1 & CC1).
      destruct (dr_epilogue m1 junk r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 rra y0 y1 y2 y3 (wz C) (wz INSTANCE) (wz (Z.of_nat (@length qbatch [])))
                  y4 y5 y6 y7 y8 y9 y10 (wz SEC) (wz GSTATS) (wz (qb_addr AL b)) (wz 137438953472) y11 y12 y13 y14 y15 y16 y17 y18 ST1 FR1) as [STq EV].
      lz_go.
      zstep. if_cases KB; zify_cond KB. { exfalso. cbn [length] in KB. clear - KB. lia. } clear KB.
      lz_here. eapply implA_evt; [exact EV|]. intros ms' ->. cbn [t_dorecycle]. apply implA_ret. apply evt_done.
      unfold dr_outer_post. do 15 eexists. exists m1, W1, lw', bw'.
      split; [reflexivity|]. split; [reflexivity|]. split; [exact MU1|].
      split. { eapply (atouch_xle X X lo (q - 112) _ _ _ _ W1 (xle_refl X)); [apply tc_of_head| apply tsc_of_head| exact FW1]. }
      split; [exact INV1|]. split; [exact XL1|]. split; [exact STq| exact CC1].

    -
      cbn [t_dorecycle]. cbn [flat_map] in INV. rewrite <- app_assoc in INV.
      assert (NB' : Z.of_nat (length bs) + 1 < 2^64) by (cbn [length] in NB; clear - NB; lia).
      eapply implA_ebind.
      { eapply implA_mclean; [exact MC|].
        exact (dr_batch X H m b (b' :: bs) hrest junk r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 rra lw bw
                 xra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x4 x6 x7 x8 x9 t3 t4 t5 t6 MC INV QL MACH). }
      intros u H1 ms1 [(lw' & bw' & PO) MC1]. unfold dr_batch_post in PO.
      destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y18 & m1 & W1 & -> & -> & MU1 & FW1 & INV1 & XL1 & QL1 & MACH1).
      clean_ms_mem MC1.
      assert (EL : Z.of_nat (length (b' :: bs)) = Z.of_nat (length bs) + 1) by (cbn [length]; lia).
      rewrite EL in *. cbn [qfirst] in MACH1.
      lz_go.
      zstep. if_cases KB; zify_cond KB; [| exfalso; clear - KB; lia]. clear KB.
      lz_here.
      eapply implA_mono.
      { eapply (IH b' (recycle_batch X b) _ m1 hrest junk r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 rra lw' bw'); [ exact NB' | assumption | exact INV1 | exact QL1 | exact MACH1 ]. }
      intros u' H2 ms2 PO. unfold dr_outer_post in PO |- *.
      destruct PO as (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & z14 & m2 & W2 & lw2 & bw2 & -> & -> & MU2 & FW2 & INV2 & XL2 & STq & CC2).
      exists z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, m2, (W1 ++ W2), lw2, bw2.
      split; [reflexivity|]. split; [reflexivity|].
      split. { cbn [app] in MU1. eapply munch_trans; [eapply munch_weaken; [| exact MU1]| eapply munch_weaken; [| exact MU2]]; unfold sub_fp; cbn [outside]; intros xo [O0 O]; apply outside_app in O as [O1 O2]; tauto. }
      split.
      { apply Forall_app. split.
        - eapply (atouch_xle X X lo (q - 112) _ _ _ _ W1 (xle_refl X)); [apply tc_of_head| apply tsc_of_head| exact FW1].
        - eapply (atouch_xle X (recycle_batch X b) lo (q - 112) _ _ _ _ W2 XL1); [apply tc_of_tail| apply tsc_of_tail| exact FW2]. }
      split; [exact INV2|]. split; [exact (xle_trans _ _ _ XL1 XL2)|]. split; [exact STq| exact CC2].
  Qed.

  Definition dorecycle_post (X : pstate) (H : word -> bool) (m : mem) (bs : list qbatch) (hrest : list (Z * Z))
      (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 : word) : unit -> (word -> bool) -> machine_state -> Prop :=
    fun _ H' ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' W lw bw,
      ms' = MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F_ (ret_pc ra) fc None m' (seg_rom asegs)
      /\ H' = H_dorecycle AL X bs H
      /\ munch ((C, C + 32) :: W) m m'
      /\ Forall (atouch AL lo q (fst X) (snd X) (tc_of bs) (tsc_of bs)) W
      /\ dr_inv AL E (dorecycle X bs) H' m' RQB RQC hrest
      /\ xle X (dorecycle X bs)
      /\ stk asegs m' lo q
      /\ rw_cells asegs m' C [C8 (wz 0); C8 (wz 0); C8 lw; C8 bw].

  #[using="AO LOH CLO LOQ QH Q16 QC C47"] Theorem dorecycle_spec : forall (ra t0 t1 t2 s0 s1 a0 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 t3 t4 t5 t6 : word)
        (X : pstate) (H : word -> bool) (m : mem) (bs : list qbatch) (hrest : list (Z * Z)) (lw bw : word),
    Z.of_nat (length bs) < 2^64 ->
    mclean H m -> stk asegs m lo q ->
    dr_inv AL E X H m (bs ++ RQB) (flat_map qb_chunks bs ++ RQC) hrest -> qlist_rep AL m bs 0 ->
    rw_cells asegs m C [C8 (wz (Z.of_nat (length bs))); C8 (wz (qfirst AL bs)); C8 lw; C8 bw] ->
    implA H (t_dorecycle AL X bs)
      (dorecycle_post X H m bs hrest ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9)
      (MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 a0 (wz C) (wz CACHE) stackw a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz dorecycle_entry) fc None m (seg_rom asegs)).
  Proof.
    intros ra t0 t1 t2 s0 s1 a0 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 t3 t4 t5 t6 X H m bs hrest lw bw NB MC ST INV QL CC.
    unfold dorecycle_entry.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    assert (LQ : lo <= q - 112) by (unfold DOREC_STACK, AREC_STACK, CDEALLOC_STACK, MF_STACK in LOQ; lia).
    pose proof INV as (_ & _ & _ & MI & _).
    pose proof (munch_refl [(q - 112, q)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    lz_go.
    zstep. carve_frame 112%nat ST.
    do 11 zstep.
    zstep.
    do 2 zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mA end.

    replace (q + -112) with (q - 112) in * by lia.
    match type of FR with rw_cells _ _ _ (CB 8 ?j :: _) => set (jk := j) in FR end.
    assert (FRD : dr_frame mA jk s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra).
    { destruct (rw_cells_take3 asegs mA (q - 112) [CB 8 jk] [C8 (wz CACHE); C8 stackw] _ FR) as (G1 & G2 & G3).
      cbn [cells_size csize Nat.add] in G2, G3.
      replace (q - 112 + Z.of_nat 8) with (q - 104) in G2 by lia. replace (q - 112 + Z.of_nat 8 + Z.of_nat 16) with (q - 88) in G3 by lia.
      exact (conj G1 (conj G2 G3)). }
    replace (q - 112 + 112) with q in MU by lia.
    assert (INVA : dr_inv AL E X H mA (bs ++ RQB) (flat_map qb_chunks bs ++ RQC) hrest)
      by (apply (dr_inv_stack X H m mA _ _ hrest (q - 112) 112 LQ ltac:(lia)); [exact INV| replace (q - 112 + 112) with q by lia; exact MU| exact WM| exact MI]).
    assert (FWA : Forall (atouch AL lo q (fst X) (snd X) [] []) [(q - 112, q)]).
    { constructor; [| constructor]. left. unfold sub_iv. cbn [fst snd]. clear - LQ. lia. }
    assert (QLA : qlist_rep AL mA bs 0).
    { eapply (dr_qlist_other X H m mA _ _ hrest lo q [(q - 112, q)] [] [] bs 0 INV ltac:(constructor) ltac:(intros d []) MU FWA LOH CLO QL).
      intros b' Hb. split; [| intros []]. destruct INV as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & [_ FH] & _).
      apply (proj1 (Forall_forall _ _) FH). apply in_or_app. left. apply in_map. apply in_or_app. left. exact Hb. }
    zstep. if_cases KB; zify_cond KB.

    -
      assert (EB : bs = []) by (destruct bs; [reflexivity| cbn [length] in KB; clear - KB; lia]). subst bs.
      cbn [length qfirst flat_map t_dorecycle] in *.
      lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) => idtac end.
      lz_here.
      eapply implA_evt.
      { eapply (proj2 (dr_epilogue mA jk s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST FRD)). }
      intros ms' ->. apply implA_ret. apply evt_done.
      unfold dorecycle_post. do 15 eexists. exists mA, [(q - 112, q)], lw, bw.
      split; [reflexivity|]. split; [reflexivity|].
      split. { eapply munch_weaken; [| exact MU]. unfold sub_fp; cbn [outside]; intros xo O; tauto. }
      split; [exact FWA|]. split; [exact INVA|]. split; [apply xle_refl|].
      split; [exact (proj1 (dr_epilogue mA jk s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra ra ra ra ra ra ra ra ra ra ra ra ra ra ra ra ra ra ra ra ra ra ra ra ra ra ra ST FRD))| exact CC].

    -
      destruct bs as [|b bs]; [exfalso; cbn [length] in KB; clear - KB; lia|].
      assert (EL : Z.of_nat (length (b :: bs)) = Z.of_nat (length bs) + 1) by (cbn [length]; lia).
      rewrite EL in *. cbn [qfirst] in CC.
      do 8 zstep.
      lz_here.
      eapply implA_mono.
      { eapply (dr_outer bs b X H mA hrest jk s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra lw bw); [ exact NB | assumption | exact INVA | exact QLA | exact (conj ST (conj FRD CC)) ]. }
      intros u' H2 ms2 PO. unfold dr_outer_post in PO. unfold dorecycle_post.
      destruct PO as (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & z14 & m2 & W2 & lw2 & bw2 & -> & -> & MU2 & FW2 & INV2 & XL2 & STq & CC2).
      exists z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, m2, ((q - 112, q) :: W2), lw2, bw2.
      split; [reflexivity|]. split; [reflexivity|].
      split. { eapply munch_trans; [eapply munch_weaken; [| exact MU]| eapply munch_weaken; [| exact MU2]]; unfold sub_fp; cbn [outside]; intros xo O; tauto. }
      split.
      { constructor.
        - left. unfold sub_iv. cbn [fst snd]. clear - LQ. lia.
        - eapply (Forall_atouch_mono AL lo q (fst X) (snd X) _ _ lo (q - 112) (fst X) (snd X) _ _ W2); [lia| lia| intros; lia| apply incl_refl| apply incl_refl| apply incl_refl| exact FW2]. }
      split; [exact INV2|]. split; [exact XL2|]. split; [exact STq| exact CC2].
  Qed.

End DOREC.

