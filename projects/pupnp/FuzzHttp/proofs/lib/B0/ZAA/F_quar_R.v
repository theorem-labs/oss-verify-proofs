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
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts AllocA0 ATac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAA Require Import AEnv ADepot ALayout APrim ATacA ACells LJ LJU PEnv APrimSpec APrimSpec2 APrimLem AFrame APrimPop APrimPopR APrimQ APrimFrame AFrameM
                        APrimDealloc ASec ASecD AQuar AQuarM AHeap AFoot F_prim_cdealloc F_quar_A AQuarR AQuarS ATacFix F_quar_M F_quar_DR F_sec_A.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Definition qrecycle_entry : Z := 0x353f8.
Notation QUAR := 725424%Z.

Section DSTEP.
  Variable T : Z.

  Definition dstep_post (ra gp tp s0 s1 a2 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32)
      (m : mem) (mn BA bnx bs : Z) (bc : word) (gc : Z) (gl : word) (gb : Z) (c0 tf l0 : word) (tb tc EA : Z) (es ec : word) : machine_state -> Prop :=
    fun ms' => exists m',
      ms' = MS (mkR ra (wz T) gp tp (wz bnx) (wz BA) (wz (gb - bs)) s0 s1 (wz QUAR) (wz mn) a2 a3 (wz (tc + 1)) (wz BA) (wz (gc - 1)) (wz bnx)
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
               F (wz 0x354f0) fc None m' (seg_rom asegs)
      /\ munch [(QUAR_GQ, QUAR_GQ + 32); (T, T + 32); (BA, BA + 24); (EA, EA + 24)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ rw_cells asegs m' BA [C8 (wz 0); C8 (wz bs); C8 bc]
      /\ rw_cells asegs m' QUAR_GQ [C8 (wz (gc - 1)); C8 (wz bnx); C8 (if bnx =? 0 then wz 0 else gl); C8 (wz (gb - bs))]
      /\ rw_cells asegs m' T [C8 c0; C8 (if tc =? 0 then wz BA else tf); C8 l0; C8 (wz (tb + bs))]
      /\ (tc <> 0 -> rw_cells asegs m' EA [C8 (wz BA); C8 es; C8 ec]).

  #[using="Type"] Lemma deq_step : forall (ra gp tp x5a x6 x7 s0 s1 a2 a3 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32)
      (m : mem) (mn BA bnx bs : Z) (bc : word) (gc : Z) (gl : word) (gb : Z) (c0 tf l0 : word) (tb tc EA : Z) (enx es ec : word) (a5w : word),
    mem_inv asegs m ->
    rw_cells asegs m BA [C8 (wz bnx); C8 (wz bs); C8 bc] ->
    rw_cells asegs m QUAR_GQ [C8 (wz gc); C8 (wz BA); C8 gl; C8 (wz gb)] ->
    rw_cells asegs m T [C8 c0; C8 tf; C8 l0; C8 (wz tb)] ->
    (tc <> 0 -> a5w = wz EA /\ rw_cells asegs m EA [C8 enx; C8 es; C8 ec]) ->
    (tc <> 0 -> QUAR_GQ + 32 <= EA /\ EA + 24 <= T /\ (EA + 24 <= BA \/ BA + 8192 <= EA)) ->
    1 <= gc < 2^64 -> 0 <= tc < 2^63 -> 0 <= bnx < 2^64 -> 0 <= bs < 2^63 -> 0 <= gb < 2^63 -> 0 <= tb < 2^63 ->
    QUAR_GQ + 32 <= BA -> BA + 8192 <= T -> T + 32 < 2^64 -> x5a = wz BA ->
    evt asegs (dstep_post ra gp tp s0 s1 a2 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 F fc m mn BA bnx bs bc gc gl gb c0 tf l0 tb tc EA es ec)
      (MS (mkR ra (wz T) gp tp x5a x6 x7 s0 s1 (wz QUAR) (wz mn) a2 a3 (wz tc) a5w (wz gc) a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (wz 0x354f4) fc None m (seg_rom asegs)).
  Proof.
    intros ra gp tp x5a x6 x7 s0 s1 a2 a3 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 F fc m mn BA bnx bs bc gc gl gb c0 tf l0 tb tc EA enx es ec a5w
      MI BH GC TC EL EG GC1 TC0 BNX BS GB TB GBA BAT TH ->.
    pose proof (munch_refl [(QUAR_GQ, QUAR_GQ + 32); (T, T + 32); (BA, BA + 24); (EA, EA + 24)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (EH : tc = 0 \/ (tc <> 0 /\ a5w = wz EA /\ rw_cells asegs m EA [C8 enx; C8 es; C8 ec])) by (destruct (Z.eq_dec tc 0) as [E0|N0]; [left; exact E0| right; split; [exact N0| exact (EL N0)]]).
    clear EL. destruct EH as [TC0'|(TCN & ETL & EH)]; [subst tc; clear EG| subst a5w; destruct (EG TCN) as (GEA & EAT & SEPB); clear EG].
    all: zstep; if_cases KB; zify_cond KB; [exfalso; clear - KB GC1; lia|]; clear KB.
    all: do 2 zstep.
    all: zstep; if_cases KN; zify_cond KN.

    -
      do 2 zstep.
      do 4 zstep.
      zstep.
      sstep.
      zstep. if_cases KT; zify_cond KT. { exfalso. clear - KT. lia. } clear KT.
      zstep.
      do 2 zstep.
      do 4 zstep.
      do 4 zstep.
      unfold dstep_post. rewrite (proj2 (Z.eqb_neq bnx 0) KN). cbn [Z.eqb].
      finish.
      intros C0. exfalso. apply C0. reflexivity.

    -
      sstep.
      do 2 zstep.
      do 4 zstep.
      zstep.
      sstep.
      zstep. if_cases KT; zify_cond KT. { exfalso. clear - KT. lia. } clear KT.
      zstep.
      do 2 zstep.
      do 4 zstep.
      do 4 zstep.
      unfold dstep_post. rewrite (proj2 (Z.eqb_eq bnx 0) KN). cbn [Z.eqb].
      subst bnx. finish.
      intros C0. exfalso. apply C0. reflexivity.

    -
      do 2 zstep.
      do 4 zstep.
      zstep.
      sstep.
      zstep. if_cases KT; zify_cond KT; [| exfalso; clear - KT TCN TC0; lia]. clear KT.
      zstep.
      do 4 zstep.
      do 4 zstep.
      unfold dstep_post. rewrite (proj2 (Z.eqb_neq bnx 0) KN). rewrite (proj2 (Z.eqb_neq tc 0) TCN).
      finish.
      intros _. exact EH.
    -
      sstep.
      do 2 zstep.
      do 4 zstep.
      zstep.
      sstep.
      zstep. if_cases KT; zify_cond KT; [| exfalso; clear - KT TCN TC0; lia]. clear KT.
      zstep.
      do 4 zstep.
      do 4 zstep.
      unfold dstep_post. rewrite (proj2 (Z.eqb_eq bnx 0) KN). rewrite (proj2 (Z.eqb_neq tc 0) TCN).
      subst bnx. finish.
      intros _. exact EH.
  Qed.
End DSTEP.

Lemma q_dequeue_step : forall b l bytes mn, mn < bytes ->
  q_dequeue (b :: l) bytes mn = (b :: fst (q_dequeue l (bytes - qb_size b) mn), snd (q_dequeue l (bytes - qb_size b) mn)).
Proof. intros b l bytes mn K. cbn [q_dequeue]. replace (mn <? bytes) with true by (symmetry; apply Z.ltb_lt; exact K). destruct (q_dequeue l (bytes - qb_size b) mn). reflexivity. Qed.
Lemma q_dequeue_stop : forall l bytes mn, bytes <= mn -> q_dequeue l bytes mn = ([], l).
Proof. intros [|b l] bytes mn K; cbn [q_dequeue]; [reflexivity|]. replace (mn <? bytes) with false by (symmetry; apply Z.ltb_ge; exact K). reflexivity. Qed.

Section DEQ.
  Context {HC : HasCeiling}.
  Variable AL : alayout.
  Variable T : Z.
  Hypothesis TH : T + 32 < 2^64.
  Notation bgeoR := (bgeo AL QUAR_GQ T).
  Notation bivR := (biv AL).

  Definition dloop_post (ra gp tp s0 s1 a2 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32)
      (m : mem) (mn : Z) (l tk : list qbatch) : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 a4 a5 a6 a7 m',
      let taken := fst (q_dequeue l (qbytes l) mn) in let rest := snd (q_dequeue l (qbytes l) mn) in
      ms' = MS (mkR ra (wz T) gp tp x5 x6 x7 s0 s1 (wz QUAR) (wz mn) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
               F (wz 0x35550) fc None m' (seg_rom asegs)
      /\ munch ((QUAR_GQ, QUAR_GQ + 32) :: (T, T + 32) :: map bivR (l ++ tk)) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ qmain_list AL m' rest 0 /\ qmain_list AL m' (tk ++ taken) 0
      /\ rw_cells asegs m' QUAR_GQ (qcells AL rest) /\ rw_cells asegs m' T (qcells AL (tk ++ taken)).

  #[using="TH"] Lemma deq_loop : forall (l tk : list qbatch)
      (ra gp tp x6 x7 s0 s1 a2 a3 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32)
      (m : mem) (mn : Z) (c0 l0 : word),
    mem_inv asegs m -> qmain_list AL m l 0 -> qmain_list AL m tk 0 ->
    rw_cells asegs m QUAR_GQ (qcells AL l) -> rw_cells asegs m T [C8 c0; C8 (wz (qfirst AL tk)); C8 l0; C8 (wz (qbytes tk))] ->
    List.NoDup (map qb_v (l ++ tk)) -> Forall bgeoR (l ++ tk) -> Forall bwf l -> Forall (fun b => 0 <= qb_size b) tk ->
    qbytes l + qbytes tk < 2^62 -> Z.of_nat (length l) + Z.of_nat (length tk) < 2^62 -> 0 <= mn -> mn < qbytes l ->
    evt asegs (dloop_post ra gp tp s0 s1 a2 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 F fc m mn l tk)
      (MS (mkR ra (wz T) gp tp (wz (qfirst AL l)) x6 x7 s0 s1 (wz QUAR) (wz mn) a2 a3 (wz (Z.of_nat (length tk))) (wz (qlast AL tk))
               (wz (Z.of_nat (length l))) a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (wz 0x354f4) fc None m (seg_rom asegs)).
  Proof.
    induction l as [|b l IH]; intros tk ra gp tp x6 x7 s0 s1 a2 a3 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 F fc m mn c0 l0
      MI QL QT GC TC ND FG FW FT QB LN MN0 MNB.
    { exfalso. cbn in MNB. lia. }
    pose proof QL as QLc; cbn [qmain_list] in QLc; destruct QLc as ((BH & (bws & BW & LBW & FBW)) & QL').
    pose proof FG as FGc; cbn [app] in FGc; apply Forall_cons_iff in FGc as [GB FGr].
    pose proof FW as FWc; apply Forall_cons_iff in FWc as [(BS8 & BC1 & BC2) FWr].
    pose proof (bwf_qbytes_nonneg _ FWr) as QR0. pose proof (qbytes_nonneg tk FT) as QT0. rewrite qbytes_cons in QB, MNB.
    cbn [map app] in ND. pose proof ND as NDc. apply NoDup_cons_iff in NDc as [NI1 NDr].
    pose proof GB as (GB1 & GB2 & _).
    assert (APO : forall b', In b' (l ++ tk) -> bgeoR b' /\ (qb_addr AL b' + 8192 <= qb_addr AL b \/ qb_addr AL b + 8192 <= qb_addr AL b')).
    { intros b' Hb. pose proof (proj1 (Forall_forall _ _) FGr b' Hb) as GB'. split; [exact GB'|].
      apply (bapart_of AL QUAR_GQ T b' b GB' GB). intros C. apply NI1. rewrite <- C. apply in_map. exact Hb. }
    set (BA := qb_addr AL b) in *. set (tc := Z.of_nat (length tk)) in *.
    set (W4 := fun EA : Z => [(QUAR_GQ, QUAR_GQ + 32); (T, T + 32); (BA, BA + 24); (EA, EA + 24)]).

    assert (EXF : exists (EA : Z) (es ec : word),
              (tc <> 0 -> wz (qlast AL tk) = wz EA /\ rw_cells asegs m EA [C8 (wz 0); C8 es; C8 ec])
              /\ (tc <> 0 -> QUAR_GQ + 32 <= EA /\ EA + 24 <= T /\ (EA + 24 <= BA \/ BA + 8192 <= EA))
              /\ (exists iv, In iv ((QUAR_GQ, QUAR_GQ + 32) :: (T, T + 32) :: map bivR ((b :: l) ++ tk)) /\ fst iv <= EA /\ EA + 24 <= snd iv)
              /\ (forall b', In b' l -> qb_addr AL b' + 8192 <= EA \/ EA + 24 <= qb_addr AL b')
              /\ (forall m1, munch (W4 EA) m m1 -> wmono asegs m m1 -> (tc <> 0 -> rw_cells asegs m1 EA [C8 (wz BA); C8 es; C8 ec]) ->
                             qb_main AL m1 b 0 -> qmain_list AL m1 (tk ++ [b]) 0)
              /\ (if tc =? 0 then wz BA else wz (qfirst AL tk)) = wz (qfirst AL (tk ++ [b]))
              /\ (EA + 24 <= BA \/ BA + 8192 <= EA)).
    { destruct tk as [|e0 tk0].
      - exists T, (wz 0), (wz 0). subst tc. cbn [length Z.of_nat].
        split; [intros C; exfalso; apply C; reflexivity|]. split; [intros C; exfalso; apply C; reflexivity|].
        split. { exists (T, T + 32). split; [right; left; reflexivity| cbn [fst snd]; lia]. }
        split. { intros b' Hb. destruct (APO b' ltac:(apply in_or_app; left; exact Hb)) as ((_ & B2 & _) & _). left. lia. }
        split. { intros m1 _ _ _ NM. cbn [app qmain_list]. split; [exact NM| exact I]. }
        split; [reflexivity|]. right. exact GB2.
      - destruct (exists_last (l := e0 :: tk0) ltac:(discriminate)) as (tki & el & ETK). unfold tc in *. clear tc. rewrite ETK in *. clear ETK e0 tk0.
        set (tc := Z.of_nat (length (tki ++ [el]))) in *.
        apply qmain_list_snoc in QT as [QTi (ELc & (ews & EW & LEW & FEW))].
        assert (TCN : tc <> 0) by (subst tc; rewrite length_app; cbn [length]; lia).
        assert (INel : In el (l ++ tki ++ [el])) by (apply in_or_app; right; apply in_or_app; right; left; reflexivity).
        destruct (APO el INel) as (GEL & APB). pose proof GEL as (GE1 & GE2 & _).
        assert (APE : forall b', In b' (l ++ tki) -> bgeoR b' /\ (qb_addr AL b' + 8192 <= qb_addr AL el \/ qb_addr AL el + 8192 <= qb_addr AL b')).
        { intros b' Hb. assert (Hb' : In b' (l ++ tki ++ [el])) by (rewrite app_assoc; apply in_or_app; left; exact Hb).
          destruct (APO b' Hb') as (GB' & _). split; [exact GB'|]. apply (bapart_of AL QUAR_GQ T b' el GB' GEL). intros C.
          rewrite app_assoc, map_app in NDr. apply (NoDup_app_disj _ _ (qb_v b') NDr); [apply in_map; exact Hb| rewrite C; left; reflexivity]. }
        exists (qb_addr AL el), (wz (qb_size el)), (wz (qb_count el)).
        split. { intros _. split; [rewrite qlast_snoc; reflexivity| exact ELc]. }
        split. { intros _. clear - GE1 GE2 APB. lia. }
        split. { exists (bivR el). split; [| unfold biv; cbn [fst snd]; lia]. right. right. apply in_map. right. exact INel. }
        split. { intros b' Hb. destruct (APE b' ltac:(apply in_or_app; left; exact Hb)) as (_ & A). clear - A. lia. }
        split.
        { intros m1 MU1 WM1 EL1 NM. apply qmain_list_snoc. split; [| exact NM]. apply qmain_list_snoc. split.
          - eapply (qmain_list_frame AL (W4 (qb_addr AL el)) m m1 tki _ QTi MU1 WM1). apply Forall_forall. intros b' Hb.
            destruct (APE b' ltac:(apply in_or_app; right; exact Hb)) as ((B1 & B2 & _) & A3).
            destruct (APO b' ltac:(apply in_or_app; right; apply in_or_app; left; exact Hb)) as (_ & A1).
            unfold W4. cbn [disjoint_from]. clear - B1 B2 A1 A3. lia.
          - split; [exact (EL1 TCN)|]. exists ews. split; [| split; [exact LEW| exact FEW]].
            eapply u64arr_transport; [exact EW| exact MU1| exact WM1|]. rewrite LEW.
            unfold W4. cbn [disjoint_from]. clear - GE1 GE2 APB. lia. }
        split; [rewrite (proj2 (Z.eqb_neq tc 0) TCN); rewrite (qfirst_app AL (tki ++ [el]) [b] ltac:(intros C; apply app_eq_nil in C as [_ C]; discriminate)); reflexivity|].
        clear - APB. lia. }
    destruct EXF as (EA & es & ec & ELH & EGH & (ivE & INE & IVE1 & IVE2) & EDJ & EPUSH & EFST & EAB).

    assert (BNX : 0 <= qfirst AL l < 2^64 /\ (qfirst AL l = 0 <-> l = [])).
    { destruct l as [|b' l']; [cbn [qfirst]; split; [lia| split; reflexivity]|].
      destruct (APO b' ltac:(left; reflexivity)) as ((B1 & B2 & _) & _). cbn [qfirst]. split; [lia|]. split; [intros C; exfalso; lia| discriminate]. }
    destruct BNX as [BNX BNZ].
    eapply evt_cut.
    { eapply (deq_step T ra gp tp (wz BA) x6 x7 s0 s1 a2 a3 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 F fc m mn BA (qfirst AL l)
                (qb_size b) (wz (qb_count b)) (Z.of_nat (length (b :: l))) (wz (qlast AL (b :: l))) (qbytes (b :: l)) c0 (wz (qfirst AL tk)) l0
                (qbytes tk) tc EA (wz 0) es ec (wz (qlast AL tk)) MI BH GC TC ELH EGH);
        try reflexivity; try exact BNX; try (subst tc BA; cbn [length] in *; rewrite ?qbytes_cons; clear - TH GB1 GB2 BS8 QB QR0 QT0 LN; lia). }
    cbv beta. unfold dstep_post.
    intros ms1 (m1 & -> & MU1 & WM1 & MI1 & BH1 & GC1 & TC1 & EL1).
    fold (W4 EA) in MU1.

    assert (NM : qb_main AL m1 b 0).
    { split; [exact BH1|]. exists bws. split; [| split; [exact LBW| exact FBW]].
      eapply u64arr_transport; [exact BW| exact MU1| exact WM1|]. rewrite LBW. unfold W4. cbn [disjoint_from]. clear - GB1 GB2 EAB. lia. }
    assert (RM : qmain_list AL m1 l 0).
    { eapply (qmain_list_frame AL (W4 EA) m m1 l 0 QL' MU1 WM1). apply Forall_forall. intros b' Hb.
      destruct (APO b' ltac:(apply in_or_app; left; exact Hb)) as ((B1 & B2 & _) & A1). pose proof (EDJ b' Hb) as A3.
      unfold W4. cbn [disjoint_from]. clear - B1 B2 A1 A3. lia. }
    pose proof (EPUSH m1 MU1 WM1 EL1 NM) as TM.
    assert (GCL : rw_cells asegs m1 QUAR_GQ (qcells AL l)).
    { unfold qcells. replace (Z.of_nat (length l)) with (Z.of_nat (length (b :: l)) - 1) by (cbn [length]; lia).
      replace (wz (qlast AL l)) with (if qfirst AL l =? 0 then wz 0 else wz (qlast AL (b :: l))).
      2:{ destruct l as [|b' l']; [reflexivity|]. rewrite (proj2 (Z.eqb_neq _ 0)) by (intros C; apply BNZ in C; discriminate). rewrite qlast_cons2. reflexivity. }
      replace (qbytes l) with (qbytes (b :: l) - qb_size b) by (rewrite qbytes_cons; lia). exact GC1. }
    assert (TCL : rw_cells asegs m1 T [C8 c0; C8 (wz (qfirst AL (tk ++ [b]))); C8 l0; C8 (wz (qbytes (tk ++ [b])))]).
    { rewrite <- EFST, qbytes_app, qbytes_cons. cbn [qbytes fold_right]. rewrite Z.add_0_r. exact TC1. }
    assert (MUW : munch ((QUAR_GQ, QUAR_GQ + 32) :: (T, T + 32) :: map bivR ((b :: l) ++ tk)) m m1).
    { eapply munch_weaken; [| exact MU1]. intros x O. unfold W4. cbn [outside].
      pose proof (outside_In _ x (QUAR_GQ, QUAR_GQ + 32) O ltac:(left; reflexivity)) as O1.
      pose proof (outside_In _ x (T, T + 32) O ltac:(right; left; reflexivity)) as O2.
      pose proof (outside_In _ x (bivR b) O ltac:(right; right; left; reflexivity)) as O3.
      pose proof (outside_In _ x ivE O INE) as O5. unfold biv in O3. cbn [fst snd] in O1, O2, O3. fold BA in O3.
      split; [exact O1|]. split; [exact O2|]. split; [clear - O3; lia|]. split; [clear - O5 IVE1 IVE2; lia| exact I]. }

    assert (ELN : Z.of_nat (length (tk ++ [b])) = tc + 1) by (rewrite length_app; cbn [length]; subst tc; lia).
    unfold dloop_post. cbv zeta. rewrite (q_dequeue_step b l (qbytes (b :: l)) mn ltac:(rewrite qbytes_cons; exact MNB)). cbn [fst snd].
    replace (qbytes (b :: l) - qb_size b) with (qbytes l) in * by (rewrite qbytes_cons; lia).
    clear GC1 TC1 BH1 EL1. unfold qcells in GCL.
    hide MU1. hide MUW. hide WM1.
    pose proof (munch_refl [(T, T + 32)] m1) as MUx. pose proof (wmono_refl asegs m1) as WMx.
    zstep. if_cases KE; zify_cond KE.
    -
      do 2 zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mB end.
      unhide MUW. unhide WM1.
      rewrite (q_dequeue_stop l (qbytes l) mn KE). cbn [fst snd].
      assert (DJT : forall b', In b' ((b :: l) ++ tk) -> disjoint_from [(T, T + 32)] (qb_addr AL b') 8192).
      { intros b' Hb. pose proof (proj1 (Forall_forall _ _) FG b' Hb) as (_ & B2 & _). cbn [disjoint_from]. lia. }
      apply evt_done. do 7 eexists. exists mB. split; [reflexivity|].
      split; [eapply munch_trans; [exact MUW|]; eapply munch_weaken; [| exact MUx]; apply sub_fp_incl; intros iv [<-|[]]; right; left; reflexivity|].
      split; [exact (wmono_trans asegs _ _ _ WM1 WMx)|]. split; [assumption|].
      split. { eapply (qmain_list_frame AL _ m1 mB l 0 RM MUx WMx). apply Forall_forall. intros b' Hb. apply DJT. right. apply in_or_app. left. exact Hb. }
      split. { eapply (qmain_list_frame AL _ m1 mB (tk ++ [b]) 0 TM MUx WMx). apply Forall_forall. intros b' Hb. apply DJT.
               apply in_app_or in Hb as [Hb|[<-|[]]]; [right; apply in_or_app; right; exact Hb| left; reflexivity]. }
      split; [exact GCL|]. unfold qcells. rewrite ELN, qlast_snoc. exact TCL.

    -
      unhide MUW. unhide WM1.
      replace (Z.of_nat (length (b :: l)) - 1) with (Z.of_nat (length l)) by (cbn [length]; lia).
      rewrite <- ELN. replace (wz BA) with (wz (qlast AL (tk ++ [b]))) by (rewrite qlast_snoc; reflexivity).
      eapply evt_cut.
      { eapply (IH (tk ++ [b]) ra gp tp _ _ s0 s1 a2 a3 _ s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 F fc m1 mn c0 l0 MI1 RM TM GCL TCL).
        - rewrite app_assoc, map_app. cbn [map]. eapply Permutation_NoDup; [| exact ND]. apply (Permutation_cons_append (map qb_v (l ++ tk)) (qb_v b)).
        - rewrite app_assoc. apply Forall_app. split; [exact FGr| constructor; [exact GB| constructor]].
        - exact FWr.
        - apply Forall_app. split; [exact FT| constructor; [clear - BS8; lia| constructor]].
        - rewrite qbytes_app, qbytes_cons. cbn [qbytes fold_right]. clear - QB. lia.
        - rewrite length_app. cbn [length] in LN |- *. clear - LN. lia.
        - exact MN0.
        - clear - KE. lia. }
      cbv beta. unfold dloop_post. cbv zeta.
      intros ms2 (z5 & z6 & z7 & z4 & z5' & z6' & z7' & m2 & -> & MU2 & WM2 & MI2 & RM2 & TM2 & GC2 & TC2).
      apply evt_done. set (TK2 := fst (q_dequeue l (qbytes l) mn)) in *.
      replace (tk ++ b :: TK2) with ((tk ++ [b]) ++ TK2) by (rewrite <- app_assoc; reflexivity).
      exists z5, z6, z7, z4, z5', z6', z7', m2. split; [reflexivity|].
      split.
      { eapply munch_trans; [exact MUW|]. eapply munch_weaken; [| exact MU2]. apply sub_fp_incl.
        intros iv [<-|[<-|Hin]]; [left; reflexivity| right; left; reflexivity|]. right. right.
        apply in_map_iff in Hin as (b' & <- & Hb). apply in_map.
        apply in_app_or in Hb as [Hb|Hb]; [right; apply in_or_app; left; exact Hb|].
        apply in_app_or in Hb as [Hb|[<-|[]]]; [right; apply in_or_app; right; exact Hb| left; reflexivity]. }
      split; [exact (wmono_trans asegs _ _ _ WM1 WM2)|]. split; [exact MI2|].
      split; [exact RM2|]. split; [exact TM2|]. split; [exact GC2| exact TC2].
  Qed.

End DEQ.

Lemma q_merge_perm : forall rest cur, Permutation (map qb_v (fst (q_merge cur rest) ++ snd (q_merge cur rest))) (map qb_v (cur :: rest)).
Proof.
  induction rest as [|nx rest IH]; intros cur; [cbn; apply Permutation_refl|].
  destruct (Z.leb_spec (qb_count cur + qb_count nx) Q_BATCH) as [K|K].
  - rewrite (q_merge_take cur nx rest K). cbn [fst snd]. specialize (IH (merged cur nx)). cbn [map merged qb_v] in IH |- *.
    rewrite map_app in *. cbn [map emptied qb_v].
    eapply Permutation_trans; [apply Permutation_sym; apply Permutation_middle|].
    eapply Permutation_trans; [apply perm_skip; exact IH|]. apply perm_swap.
  - rewrite (q_merge_keep cur nx rest K). cbn [fst snd app map]. apply perm_skip. exact (IH nx).
Qed.
Lemma q_merge_chunks : forall rest cur,
  flat_map qb_chunks (fst (q_merge cur rest)) = flat_map qb_chunks (cur :: rest) /\ flat_map qb_chunks (snd (q_merge cur rest)) = [].
Proof.
  induction rest as [|nx rest IH]; intros cur; [split; reflexivity|].
  destruct (Z.leb_spec (qb_count cur + qb_count nx) Q_BATCH) as [K|K].
  - rewrite (q_merge_take cur nx rest K). cbn [fst snd]. destruct (IH (merged cur nx)) as [E1 E2]. split.
    + rewrite E1. cbn [flat_map merged qb_chunks]. rewrite <- app_assoc. reflexivity.
    + cbn [flat_map emptied qb_chunks app]. exact E2.
  - rewrite (q_merge_keep cur nx rest K). cbn [fst snd]. destruct (IH nx) as [E1 E2]. split; [cbn [flat_map] in *; rewrite E1; reflexivity| exact E2].
Qed.
Lemma q_dequeue_app : forall l bytes mn, fst (q_dequeue l bytes mn) ++ snd (q_dequeue l bytes mn) = l.
Proof.
  induction l as [|b l IH]; intros bytes mn; [reflexivity|].
  destruct (Z.ltb_spec mn bytes) as [K|K].
  - rewrite (q_dequeue_step b l bytes mn K). cbn [fst snd app]. rewrite IH. reflexivity.
  - rewrite (q_dequeue_stop (b :: l) bytes mn K). reflexivity.
Qed.
Lemma q_merge_wf : forall rest cur, Forall qbatch_wf (cur :: rest) -> Forall qbatch_wf (fst (q_merge cur rest)).
Proof.
  induction rest as [|nx rest IH]; intros cur FW; [exact FW|].
  pose proof FW as FWc. apply Forall_cons_iff in FWc as [WC FWc]. apply Forall_cons_iff in FWc as [WN FWr].
  destruct (Z.leb_spec (qb_count cur + qb_count nx) Q_BATCH) as [K|K].
  - rewrite (q_merge_take cur nx rest K). cbn [fst]. apply IH. constructor; [| exact FWr].
    destruct WC as (C1 & C2 & C3 & C4 & C5). destruct WN as (N1 & N2 & N3 & N4 & N5).
    unfold qbatch_wf, merged. cbn [qb_v qb_size qb_chunks]. unfold qb_count in *. cbn [qb_chunks]. rewrite length_app, Nat2Z.inj_add.
    split; [exact C1|]. split; [exact C2|]. split; [lia|]. split; [| apply Forall_app; split; assumption].
    rewrite C4, N4, fold_right_app.
    assert (FR : forall (l : list qchunk) a, fold_right (fun ch acc => qc_n ch + acc) a l = fold_right (fun ch acc => qc_n ch + acc) 0 l + a)
      by (induction l as [|x l IHl]; intros a; cbn [fold_right]; [lia| rewrite IHl; lia]).
    rewrite (FR (qb_chunks cur) (fold_right (fun ch acc => qc_n ch + acc) 0 (qb_chunks nx))). lia.
  - rewrite (q_merge_keep cur nx rest K). cbn [fst]. constructor; [exact WC|]. apply IH. constructor; assumption.
Qed.
Lemma q_recycle_sel_eq : forall gl,
  let d := if (Q_BBYTES * Z.of_nat (length gl) <? qbytes gl) && (qbytes gl * 100 <? Q_BBYTES * Z.of_nat (length gl) * 200) then q_merge_list gl else (gl, []) in
  q_recycle_sel gl = (snd (q_dequeue (fst d) (qbytes (fst d)) Q_MIN), snd d ++ fst (q_dequeue (fst d) (qbytes (fst d)) Q_MIN)).
Proof.
  intros gl. unfold q_recycle_sel. cbv zeta.
  destruct ((Q_BBYTES * Z.of_nat (length gl) <? qbytes gl) && (qbytes gl * 100 <? Q_BBYTES * Z.of_nat (length gl) * 200)).
  - destruct (q_merge_list gl) as [g1 e1]. cbn [fst snd]. destruct (q_dequeue g1 (qbytes g1) Q_MIN). reflexivity.
  - cbn [fst snd]. destruct (q_dequeue gl (qbytes gl) Q_MIN). reflexivity.
Qed.

Definition QREC_STACK : Z := 80 + DOREC_STACK.

Section QREC.
  Context {HC : HasCeiling}.
  Variables (AL : alayout) (E : penv).
  Notation L := (al_thread AL).
  Notation THR := (at_thr (al_thread AL)).
  Notation CACHE := (at_thr (al_thread AL) + CACHE_OFF).
  Hypothesis AO : alayout_ok AL.
  Variables (gp s10 s11 : word) (F_ : bvmap 5 word) (fc : bv 32).
  Variables (q lo : Z) (stackw : word).
  Hypothesis LOH : 0x10007fff8000 <= lo.
  Hypothesis CLO : alloc_ceiling <= lo.
  Hypothesis LOQ : lo <= q - QREC_STACK.
  Hypothesis QH : q <= 2^47.
  Hypothesis Q16 : q mod 16 = 0.

  Definition qrec_post_gen (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 : word) (X : pstate) (H : word -> bool) (m : mem) (gl : list qbatch) (hrest : list (Z * Z))
      (rest todo : list qbatch) : unit -> (word -> bool) -> machine_state -> Prop :=
    fun _ H' ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' W,
      ms' = MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F_ (ret_pc ra) fc None m' (seg_rom asegs)
      /\ H' = H_dorecycle AL X todo H
      /\ munch ((QUAR_MTX, QUAR_MTX + 4) :: (QUAR_GQ, QUAR_GQ + 32) :: W) m m'
      /\ Forall (atouch AL lo q (fst X) (snd X) (tc_of gl) (tsc_of gl)) W
      /\ dr_inv AL E (dorecycle X todo) H' m' rest (flat_map qb_chunks rest) hrest
      /\ xle X (dorecycle X todo)
      /\ stk asegs m' lo q
      /\ qlist_rep AL m' rest 0 /\ rw_cells asegs m' QUAR_GQ (qcells AL rest)
      /\ rw_cells asegs m' QUAR_MTX [CB 4 [b8 0; b8 0; b8 0; b8 0]].
  Definition qrecycle_post (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 : word) (X : pstate) (H : word -> bool) (m : mem) (gl : list qbatch) (hrest : list (Z * Z)) :=
    qrec_post_gen ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 X H m gl hrest (fst (q_recycle_sel gl)) (snd (q_recycle_sel gl)).

  Notation WJ gl := ((lo, q) :: (QUAR_MTX, QUAR_MTX + 4) :: (QUAR_GQ, QUAR_GQ + 32) :: map (biv AL) gl).

  #[using="AO LOH CLO LOQ QH Q16"] Lemma qrec_tail2 : forall (X : pstate) (H : word -> bool) (m mK : mem) (gl rest todo : list qbatch) (hrest : list (Z * Z))
        (r4 r3 r2 r1 r0 rra : word) (xra t0 t1 t2 x0 x1 a1 a4 a5 a6 a7 x2 x3 x4 s5 s6 s7 s8 s9 t3 t4 t5 t6 : word),
    mclean H mK ->
    dr_inv AL E X H m gl (flat_map qb_chunks gl) hrest -> qlist_rep AL m gl 0 ->
    munch (WJ gl) m mK -> wmono asegs m mK -> mem_inv asegs mK ->
    qmain_list AL mK rest 0 -> qmain_list AL mK todo 0 ->
    rw_cells asegs mK QUAR_GQ (qcells AL rest) -> rw_cells asegs mK (q - 80) (qcells AL todo) ->
    rw_cells asegs mK (q - 48) [C8 r4; C8 r3; C8 r2; C8 r1; C8 r0; C8 rra] -> stk asegs mK lo (q - 80) ->
    rw_cells asegs mK QUAR_MTX [CB 4 [Z_to_bv 8 1; Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 0]] ->
    Permutation (map qb_v (todo ++ rest)) (map qb_v gl) -> flat_map qb_chunks todo ++ flat_map qb_chunks rest = flat_map qb_chunks gl ->
    Forall qbatch_wf0 (todo ++ rest) -> Z.of_nat (length todo) < 2^64 ->
    implA H (t_dorecycle AL X todo)
      (qrec_post_gen rra r0 r1 r2 r3 r4 s5 s6 s7 s8 s9 X H m gl hrest rest todo)
      (MS (mkR xra (wz (q - 80)) gp (wz A0_TP) t0 t1 t2 x0 x1 (wz QUAR) a1 (wz CACHE) stackw a4 a5 a6 a7
               x2 x3 x4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz 0x35550) fc None mK (seg_rom asegs)).
  Proof.
    intros X H m mK gl rest todo hrest r4 r3 r2 r1 r0 rra xra t0 t1 t2 x0 x1 a1 a4 a5 a6 a7 x2 x3 x4 s5 s6 s7 s8 s9 t3 t4 t5 t6
      MC INV QLR MUK WMK MIK QMR QMT GCK TCK FRS ST MTX PERM ECH BWF0 LNT.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    assert (LQ : lo <= q - 80 - DOREC_STACK) by (unfold QREC_STACK in LOQ; lia).
    assert (LQ' : lo <= q - 80) by (unfold DOREC_STACK, AREC_STACK, CDEALLOC_STACK, MF_STACK in LQ; lia).
    pose proof INV as (RP & POK & RS & MI & PE & TE & SV & WFS & REPS & HKS & HOK & NDS & BWF & BREP).
    unfold qcells in GCK, TCK.
    hide MUK. hide WMK.
    pose proof (munch_refl [(QUAR_MTX, QUAR_MTX + 4)] mK) as MUx. pose proof (wmono_refl asegs mK) as WMx.
    lz_go.
    zstep.
    sstep.
    zstep.
    sstep.
    zstep.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mU end.

    unhide MUK. unhide WMK.
    assert (MUT : munch (WJ gl) m mU).
    { eapply munch_trans; [exact MUK|]. eapply munch_weaken; [| exact MUx]. apply sub_fp_incl. intros iv [<-|[]]. right. left. reflexivity. }
    pose proof (wmono_trans asegs _ _ _ WMK WMx) as WMT.
    destruct (clear_ctx AL X m RP RS) as (WF0 & SOK & SSEP).
    layout_facts AO 0%nat SPF. destruct SPF as (SP1 & SP2 & SPM & _ & SP5 & _ & _).

    assert (HB : forall b, In b gl -> held1 (fst X) (bpair b)).
    { intros b Hb. destruct HOK as [_ FH]. apply (proj1 (Forall_forall _ _) FH). apply in_or_app. left. apply in_map. exact Hb. }
    assert (BG : forall b, In b gl -> al_space AL <= qb_addr AL b /\ qb_addr AL b + 8192 <= al_space AL + K_SPACE
                                     /\ 2147450880 <= sh (qb_addr AL b) /\ sh (qb_addr AL b) + 1024 <= 17594333495296).
    { intros b Hb. pose proof (held_geo AL (fst X) AO WF0 K_BCLASS (qb_v b) (HB b Hb)) as G. cbv zeta in G.
      destruct G as (_ & G1 & G2 & G3 & _ & G5 & G6 & G7). pose proof (region_range AL K_BCLASS ltac:(lia)) as [R1 R2].
      change (class_size K_BCLASS) with 8192 in *. change (8192 / 8) with 1024 in G5. fold (qb_addr AL b) in G1, G2, G5, G6, G7.
      rewrite G5 in G7. clear - G1 G2 G3 G6 G7 R1 R2. lia. }
    assert (VB : forall b', In (qb_v b') (map qb_v gl) -> exists b0, In b0 gl /\ qb_addr AL b' = qb_addr AL b0).
    { intros b' Hv. apply in_map_iff in Hv as (b0 & EV & Hb0). exists b0. split; [exact Hb0| apply qb_addr_v; symmetry; exact EV]. }
    assert (SHD : forall b', In (qb_v b') (map qb_v gl) -> bshadow AL mU b').
    { intros b' Hv. destruct (VB b' Hv) as (b0 & Hb0 & EA). unfold bshadow. rewrite EA.
      pose proof (proj2 (proj1 (qlist_rep_main AL m gl 0) QLR)) as FS. pose proof (proj1 (Forall_forall _ _) FS b0 Hb0) as S0. unfold bshadow in S0.
      destruct (BG b0 Hb0) as (B1 & B2 & B3 & B4).
      eapply rw_cells_transport; [exact S0| exact MUT| exact WMT|]. cbn [cells_size csize Nat.add disjoint_from].
      split; [clear - B4 LOH LQ'; lia|]. split; [clear - B3; lia|]. split; [clear - B3; lia|].
      apply dj_of_Forall. apply Forall_forall. intros iv Hiv. apply in_map_iff in Hiv as (b1 & <- & Hb1). destruct (BG b1 Hb1) as (C1 & _).
      unfold biv. cbn [fst snd]. left. clear - B4 C1 SP1. lia. }
    assert (INV_V : forall b', In b' (todo ++ rest) -> In (qb_v b') (map qb_v gl)).
    { intros b' Hb'. eapply Permutation_in; [exact PERM|]. apply in_map. exact Hb'. }
    assert (DJM : forall b', In b' (todo ++ rest) -> disjoint_from [(QUAR_MTX, QUAR_MTX + 4)] (qb_addr AL b') 8192).
    { intros b' Hb'. destruct (VB b' (INV_V b' Hb')) as (b0 & Hb0 & EA). rewrite EA. destruct (BG b0 Hb0) as (B1 & _). cbn [disjoint_from]. clear - B1 SP1. lia. }
    assert (QLT : qlist_rep AL mU todo 0).
    { apply (qlist_rep_main AL). split.
      - eapply (qmain_list_frame AL _ mK mU todo 0 QMT MUx WMx). apply Forall_forall. intros b' Hb'. apply DJM. apply in_or_app. left. exact Hb'.
      - apply Forall_forall. intros b' Hb'. apply SHD. apply INV_V. apply in_or_app. left. exact Hb'. }
    assert (QLRe : qlist_rep AL mU rest 0).
    { apply (qlist_rep_main AL). split.
      - eapply (qmain_list_frame AL _ mK mU rest 0 QMR MUx WMx). apply Forall_forall. intros b' Hb'. apply DJM. apply in_or_app. right. exact Hb'.
      - apply Forall_forall. intros b' Hb'. apply SHD. apply INV_V. apply in_or_app. right. exact Hb'. }

    assert (EACH : forall l nxt (mm : mem), qlist_rep AL mm l nxt -> Forall (fun b => exists nx, qbatch_rep AL mm b nx) l).
    { induction l as [|b l IHl]; intros nxt mm QLl; [constructor|]. cbn [qlist_rep] in QLl. destruct QLl as [RB QLl].
      constructor; [eexists; exact RB| exact (IHl nxt mm QLl)]. }
    assert (INVU : dr_inv AL E X H mU (todo ++ rest) (flat_map qb_chunks todo ++ flat_map qb_chunks rest) hrest).
    { rewrite ECH.
      eapply (dr_inv_requeue AL E X H m mU gl (todo ++ rest) _ hrest lo q [(QUAR_MTX, QUAR_MTX + 4); (QUAR_GQ, QUAR_GQ + 32)] ((lo, q) :: map (biv AL) gl) AO LOH CLO INV).
      - eapply munch_weaken; [| exact MUT]. apply sub_fp_incl. intros iv Hiv. cbn [app] in Hiv |- *.
        destruct Hiv as [<-|[<-|[<-|Hiv]]]; [right; right; left; reflexivity| left; reflexivity| right; left; reflexivity| right; right; right; exact Hiv].
      - exact WMT.
      - assumption.
      - constructor; [left; unfold qstat; cbn [fst snd]; lia| constructor; [left; unfold qstat; cbn [fst snd]; lia| constructor]].
      - constructor; [left; unfold sub_iv; cbn [fst snd]; clear - LQ'; lia|].
        apply Forall_forall. intros iv Hiv. apply in_map_iff in Hiv as (b & <- & Hb). right. exists b. split; [exact Hb|].
        unfold chunk_iv, biv, qb_addr. cbn [fst snd]. change (class_size K_BCLASS) with 8192. lia.
      - unfold bpair. rewrite <- !(map_map qb_v (fun v => (K_BCLASS, v))). apply Permutation_map. exact PERM.
      - exact BWF0.
      - apply Forall_app. split; [exact (EACH _ _ _ QLT)| exact (EACH _ _ _ QLRe)]. }
    replace (ret_pc (Z_to_bv 64 218472)) with (Z_to_bv 64 218472) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    assert (Q16' : (q - 80) mod 16 = 0) by (clear - Q16; Z.div_mod_to_equations; lia).
    lz_here.
    rewrite <- (ebind_ret_r (t_dorecycle AL X todo)).
    eapply implA_ebind.
    { eapply implA_mclean; [eassumption|].
      eapply (dorecycle_spec AL E AO gp s10 s11 F_ fc (q - 80) lo (q - 80) stackw LOH CLO LQ ltac:(clear - QH; lia) Q16' ltac:(lia) ltac:(clear - QH; lia)
                rest (flat_map qb_chunks rest) (wz 218472) _ _ _ x0 x1 (wz QUAR) _ _ _ _ x2 x3 x4 s5 s6 s7 s8 s9 _ _ _ _ X H mU todo hrest
                (wz (qlast AL todo)) (wz (qbytes todo)) LNT);
        [ assumption | exact ST | exact INVU | exact QLT | exact TCK ]. }

    intros u H1 ms1 [PO MC1]. unfold dorecycle_post in PO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & W1 & lw1 & bw1 & -> & -> & MU1 & FW1 & INV1 & XL1 & ST1 & TC1).
    clean_ms_mem MC1.
    pose proof INVU as (RPU & _ & RSU & _ & _ & _ & _ & _ & _ & _ & [NDU FHU] & _).

    assert (TCHt : Forall (held1 (fst X)) (tc_of todo)).
    { apply Forall_forall. intros cv Hcv. apply (proj1 (Forall_forall _ _) FHU). unfold tc_of in Hcv. rewrite map_app, flat_map_app.
      apply in_app_or in Hcv as [Hcv|Hcv]; [apply in_or_app; left; apply in_or_app; left; exact Hcv| apply in_or_app; right; apply in_or_app; left; apply in_or_app; left; exact Hcv]. }
    assert (TSIt : incl (tsc_of todo) (se_chunks (snd X))).
    { destruct (dr_inv_tc AL E X H mU (todo ++ rest) (flat_map qb_chunks todo) _ hrest INVU) as [_ TSI]. exact TSI. }
    assert (FWq : Forall (atouch AL lo q (fst X) (snd X) (tc_of todo) (tsc_of todo)) ((q - 80, q - 80 + 32) :: W1)).
    { constructor; [left; unfold sub_iv; cbn [fst snd]; clear - LQ'; lia|].
      eapply (Forall_atouch_mono AL lo q (fst X) (snd X) _ _ lo (q - 80) (fst X) (snd X) _ _ W1); [lia| lia| intros; lia| apply incl_refl| apply incl_refl| apply incl_refl| exact FW1]. }
    assert (DJA : forall A n, q - 48 <= A -> disjoint_from ((q - 80, q - 80 + 32) :: W1) A n).
    { intros A n HA. cbn [disjoint_from]. split; [lia|].
      exact (atouch_above AL X mU lo (q - 80) W1 _ _ A n AO LOH CLO LQ' RPU RSU TCHt TSIt FW1 ltac:(lia)). }
    assert (DJQ : forall A n, QUAR_MTX <= A -> A + n <= QUAR_GQ + 32 -> disjoint_from ((q - 80, q - 80 + 32) :: W1) A n).
    { intros A n HA HN. cbn [disjoint_from]. split; [clear - HN LOH LQ'; lia|].
      exact (atouch_qstat_dj AL X mU lo (q - 80) W1 _ _ A n AO LOH CLO RPU RSU TCHt TSIt FW1 HA HN). }
    eapply (rw_cells_transport_m _ mU m1) in FRS; [| exact MU1| apply DJA; lia].
    eapply (rw_cells_transport_m _ mU m1) in GCK; [| exact MU1| apply DJQ; cbn [cells_size csize Nat.add]; lia].
    eapply (rw_cells_transport_m _ mU m1) in MTX; [| exact MU1| apply DJQ; cbn [cells_size csize Nat.add]; lia].

    assert (QLR1 : qlist_rep AL m1 rest 0).
    { eapply (qlist_rep_other AL X mU m1 lo q _ (tc_of todo) (tsc_of todo) rest 0 AO LOH CLO RPU RSU TCHt TSIt MU1 FWq QLRe).
      apply Forall_forall. intros b Hb.
      rewrite map_app in NDU, FHU.
      split. { apply (proj1 (Forall_forall _ _) FHU). apply in_or_app. left. apply in_or_app. right. apply in_map. exact Hb. }
      unfold tc_of. intros Hin. apply in_app_or in Hin as [Hin|Hin].
      - apply NoDup_app_remove_r in NDU. apply (NoDup_app_disj_s _ _ (bpair b) NDU Hin). apply in_map. exact Hb.
      - rewrite flat_map_app in NDU. apply (NoDup_app_disj_s _ _ (bpair b) NDU); [apply in_or_app; right; apply in_map; exact Hb|].
        apply in_or_app. left. apply in_or_app. left. exact Hin. }
    lz_go.
    replace (ret_pc (Z_to_bv 64 218472)) with (Z_to_bv 64 218472) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    replace (q - 48) with (q - 80 + 32) in FRS by lia.
    pose proof (proj2 (rw_cells_app asegs m1 (q - 80) [C8 (wz 0); C8 (wz 0); C8 lw1; C8 bw1] _) (conj TC1 FRS)) as FRJ. cbn [app] in FRJ.
    do 6 zstep.
    zstep. replace (q - 80 + 80) with q by lia. zstep.
    release_frame FRJ ST1 q.

    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mf _) =>
      apply (rw_cells_rebytes mf QUAR_MTX _ [CB 4 [b8 0; b8 0; b8 0; b8 0]]) in MTX; [| cbn; tauto| cbn; repeat first [ reflexivity | apply (f_equal2 cons); [apply bv_eq; vm_compute; reflexivity|] ]| reflexivity] end.
    lz_ret. apply evt_done. unfold qrec_post_gen.
    do 15 eexists. exists m1, ((lo, q) :: map (biv AL) gl ++ W1).
    split; [reflexivity|]. split; [reflexivity|].
    split.
    { eapply munch_trans; [eapply munch_weaken; [| exact MUT]| eapply munch_weaken; [| exact MU1]].
      - apply sub_fp_incl. intros iv [<-|[<-|[<-|Hiv]]]; [right; right; left; reflexivity| left; reflexivity| right; left; reflexivity|].
        right; right; right. apply in_or_app. left. exact Hiv.
      - intros x O. cbn [outside] in O. destruct O as (_ & _ & O3 & O4). apply outside_app in O4 as [_ O6].
        cbn [outside]. split; [cbn [fst snd] in O3; clear - O3 LQ'; lia| exact O6]. }
    split.
    { constructor; [left; unfold sub_iv; cbn [fst snd]; clear - LQ'; lia|]. apply Forall_app. split.
      - apply Forall_forall. intros iv Hiv. apply in_map_iff in Hiv as (b & <- & Hb). right; right; right; right; left.
        exists (bpair b). split; [unfold tc_of; apply in_or_app; left; apply in_map; exact Hb|]. left.
        unfold chunk_iv, biv, qb_addr, bpair. cbn [fst snd]. change (class_size K_BCLASS) with 8192. lia.
      - eapply (Forall_atouch_mono AL lo q (fst X) (snd X) _ _ lo (q - 80) (fst X) (snd X) _ _ W1); [lia| lia| intros; lia| apply incl_refl| | | exact FW1].
        + unfold tc_of. intros cv Hcv. apply in_app_or in Hcv as [Hcv|Hcv]; apply in_or_app.
          * left. apply in_map_iff in Hcv as (b' & <- & Hb'). pose proof (INV_V b' ltac:(apply in_or_app; left; exact Hb')) as HV.
            apply in_map_iff in HV as (b0' & EV & Hb0'). apply in_map_iff. exists b0'. split; [unfold bpair; rewrite EV; reflexivity| exact Hb0'].
          * right. rewrite <- ECH, flat_map_app. apply in_or_app. left. exact Hcv.
        + unfold tsc_of. intros sc Hsc. rewrite <- ECH, flat_map_app. apply in_or_app. left. exact Hsc. }
    split; [exact INV1|]. split; [exact XL1|]. split; [exact ST1|]. split; [exact QLR1|]. split; [exact GCK| exact MTX].
  Qed.

  #[using="AO LOH CLO LOQ QH Q16"] Lemma qrec_tail : forall (X : pstate) (H : word -> bool) (m mJ : mem) (gl gl1 ex : list qbatch) (hrest : list (Z * Z))
        (r4 r3 r2 r1 r0 rra : word) (xra t0 t1 t2 x0 x1 a4 a5 a7 x2 x3 x4 s5 s6 s7 s8 s9 t3 t4 t5 t6 : word),
    mclean H mJ ->
    dr_inv AL E X H m gl (flat_map qb_chunks gl) hrest -> qlist_rep AL m gl 0 ->
    munch (WJ gl) m mJ -> wmono asegs m mJ -> mem_inv asegs mJ ->
    qmain_list AL mJ gl1 0 -> qmain_list AL mJ ex 0 ->
    rw_cells asegs mJ QUAR_GQ (qcells AL gl1) -> rw_cells asegs mJ (q - 80) (qcells AL ex) ->
    rw_cells asegs mJ (q - 48) [C8 r4; C8 r3; C8 r2; C8 r1; C8 r0; C8 rra] -> stk asegs mJ lo (q - 80) ->
    rw_cells asegs mJ QUAR_MTX [CB 4 [Z_to_bv 8 1; Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 0]] ->
    Permutation (map qb_v (gl1 ++ ex)) (map qb_v gl) -> flat_map qb_chunks gl1 = flat_map qb_chunks gl ->
    Forall qbatch_wf gl1 -> Forall bex ex -> qbytes gl1 + qbytes ex < 2^62 ->
    let taken := fst (q_dequeue gl1 (qbytes gl1) Q_MIN) in let rest := snd (q_dequeue gl1 (qbytes gl1) Q_MIN) in
    implA H (t_dorecycle AL X (ex ++ taken))
      (qrec_post_gen rra r0 r1 r2 r3 r4 s5 s6 s7 s8 s9 X H m gl hrest rest (ex ++ taken))
      (MS (mkR xra (wz (q - 80)) gp (wz A0_TP) t0 t1 t2 x0 x1 (wz QUAR) (wz Q_MIN) (wz CACHE) stackw a4 a5 (wz (Z.of_nat (length gl1))) a7
               x2 x3 x4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz 0x354b4) fc None mJ (seg_rom asegs)).
  Proof.
    intros X H m mJ gl gl1 ex hrest r4 r3 r2 r1 r0 rra xra t0 t1 t2 x0 x1 a4 a5 a7 x2 x3 x4 s5 s6 s7 s8 s9 t3 t4 t5 t6
      MC INV QLR MUJ WMJ MIJ QM1 QME GCJ TCJ FRS ST MTX PERM ECH1 FWF1 FEX QBS taken rest.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    assert (LQ' : lo <= q - 80) by (unfold QREC_STACK, DOREC_STACK, AREC_STACK, CDEALLOC_STACK, MF_STACK in LOQ; lia).
    pose proof INV as (RP & POK & RS & MI & PE & TE & SV & WFS & REPS & HKS & HOK & NDS & BWF & BREP).
    destruct (clear_ctx AL X m RP RS) as (WF0 & SOK & SSEP).
    layout_facts AO 0%nat SPF. destruct SPF as (SP1 & SP2 & SPM & _ & SP5 & _ & _).
    assert (HB : forall b, In b gl -> held1 (fst X) (bpair b)).
    { intros b Hb. destruct HOK as [_ FH]. apply (proj1 (Forall_forall _ _) FH). apply in_or_app. left. apply in_map. exact Hb. }
    assert (BG : forall b, In b gl -> al_space AL <= qb_addr AL b /\ qb_addr AL b + 8192 <= al_space AL + K_SPACE /\ 0 <= qb_v b /\ (16 * qb_v b) mod 8192 = 0).
    { intros b Hb. pose proof (HB b Hb) as HBb. pose proof (held_geo AL (fst X) AO WF0 K_BCLASS (qb_v b) HBb) as G. cbv zeta in G.
      destruct G as (_ & G1 & G2 & G3 & _). pose proof (region_range AL K_BCLASS ltac:(lia)) as [R1 R2].
      destruct HBb as (_ & V0 & _ & VAL & _). cbn [fst snd bpair] in V0, VAL.
      change (class_size K_BCLASS) with 8192 in *. fold (qb_addr AL b) in G1, G2. clear - G1 G2 G3 R1 R2 V0 VAL. lia. }
    assert (BG1 : forall b', In b' (gl1 ++ ex) -> al_space AL <= qb_addr AL b' /\ qb_addr AL b' + 8192 <= al_space AL + K_SPACE /\ 0 <= qb_v b' /\ (16 * qb_v b') mod 8192 = 0
                                               /\ exists b0, In b0 gl /\ qb_v b0 = qb_v b').
    { intros b' Hb'. assert (HV : In (qb_v b') (map qb_v gl)) by (eapply Permutation_in; [exact PERM| apply in_map; exact Hb']).
      apply in_map_iff in HV as (b0 & EV & Hb0). destruct (BG b0 Hb0) as (B1 & B2 & B3 & B4). rewrite (qb_addr_v AL b' b0 (eq_sym EV)), <- EV.
      repeat split; try assumption. exists b0. split; [exact Hb0| reflexivity]. }

    assert (EAPP : taken ++ rest = gl1) by apply q_dequeue_app.
    assert (CHX : forall l, Forall bex l -> flat_map qb_chunks l = []).
    { induction 1 as [|b l [_ EC] _ IHl]; [reflexivity|]. cbn [flat_map]. rewrite EC, IHl. reflexivity. }
    assert (PERM2 : Permutation (map qb_v ((ex ++ taken) ++ rest)) (map qb_v gl)).
    { rewrite <- app_assoc, EAPP. eapply Permutation_trans; [| exact PERM]. apply Permutation_map. apply Permutation_app_comm. }
    assert (ECH2 : flat_map qb_chunks (ex ++ taken) ++ flat_map qb_chunks rest = flat_map qb_chunks gl).
    { rewrite flat_map_app, (CHX ex FEX). cbn [app]. rewrite <- flat_map_app, EAPP. exact ECH1. }
    assert (BWF0 : Forall qbatch_wf0 ((ex ++ taken) ++ rest)).
    { rewrite <- app_assoc, EAPP. apply Forall_app. split.
      - apply Forall_forall. intros b' Hb'. destruct (BG1 b' ltac:(apply in_or_app; right; exact Hb')) as (_ & _ & V0 & VAL & _).
        destruct (proj1 (Forall_forall _ _) FEX b' Hb') as [_ EC]. unfold qbatch_wf0, qb_count. rewrite EC. cbn [length Z.of_nat].
        split; [exact V0|]. split; [exact VAL|]. split; [lia| constructor].
      - eapply Forall_impl; [| exact FWF1]. intros b' (W1 & W2 & W3 & _ & W5). unfold qbatch_wf0. split; [exact W1|]. split; [exact W2|]. split; [lia| exact W5]. }
    assert (FBW1 : Forall bwf gl1).
    { eapply Forall_impl; [| exact FWF1]. intros b' (_ & _ & W3 & W4 & W5). unfold bwf. split; [| exact W3]. rewrite W4.
      assert (S0 : forall l : list qchunk, Forall qchunk_wf l -> 0 <= fold_right (fun ch acc => qc_n ch + acc) 0 l)
        by (induction 1 as [|c l (_ & _ & N1 & _) _ IHl]; cbn [fold_right]; lia).
      pose proof (S0 _ W5). lia. }
    pose proof (bwf_qbytes_len gl1 FBW1) as LB1. pose proof (qbytes_bex ex FEX) as LBX. pose proof (bwf_qbytes_nonneg gl1 FBW1) as QB10.
    unfold qcells in GCJ, TCJ.
    lz_go.
    do 3 zstep.
    zstep. if_cases KD; zify_cond KD.

    -
      unfold taken, rest in *. clear taken rest. rewrite (q_dequeue_stop gl1 _ _ KD) in *. cbn [fst snd] in *.
      lz_here.
      eapply (qrec_tail2 X H m mJ gl gl1 (ex ++ []) hrest r4 r3 r2 r1 r0 rra); try eassumption.
      + rewrite app_nil_r. exact QME.
      + rewrite app_nil_r. unfold qcells. exact TCJ.
      + rewrite app_nil_r. rewrite LBX in QBS. clear - QBS QB10. lia.

    -
      do 2 zstep.
      assert (TH' : q - 80 + 32 < 2^64) by (clear - QH; lia).
      assert (NDV : List.NoDup (map qb_v (gl1 ++ ex))).
      { eapply Permutation_NoDup; [apply Permutation_sym; exact PERM|]. destruct HOK as [ND _]. apply NoDup_app_remove_r in ND.
        unfold bpair in ND. rewrite <- (map_map qb_v (fun v => (K_BCLASS, v))) in ND. apply NoDup_map_inv in ND. exact ND. }
      assert (FGE : Forall (bgeo AL QUAR_GQ (q - 80)) (gl1 ++ ex)).
      { apply Forall_forall. intros b' Hb'. destruct (BG1 b' Hb') as (B1 & B2 & _ & B4 & _). unfold bgeo. clear - B1 B2 B4 SP1 SP2 CLO LQ'. lia. }
      eapply evt_cut.
      { eapply (deq_loop AL (q - 80) TH' gl1 ex xra gp (wz A0_TP) _ _ x0 x1 (wz CACHE) stackw _ x2 x3 x4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F_ fc mJ Q_MIN
                  (wz (Z.of_nat (length ex))) (wz (qlast AL ex)) MIJ QM1 QME);
          [ unfold qcells; exact GCJ | exact TCJ | exact NDV | exact FGE | exact FBW1
          | eapply Forall_impl; [| exact FEX]; intros b' [S8 _]; lia | exact QBS | rewrite LBX in QBS; clear - QBS LB1 QB10; lia | lia | clear - KD; lia ]. }
      cbv beta. unfold dloop_post. cbv zeta. fold taken rest.
      intros msK (y5 & y6 & y7 & y4 & y5' & y6' & y7' & mK & -> & MUK & WMK & MIK & QMR & QMT & GCK & TCK).

      assert (DJK : forall A n, (q - 80 + 32 <= A \/ (A + n <= QUAR_GQ) \/ (lo <= A /\ A + n <= q - 80)) ->
                      disjoint_from ((QUAR_GQ, QUAR_GQ + 32) :: (q - 80, q - 80 + 32) :: map (biv AL) (gl1 ++ ex)) A n).
      { intros A n HA. cbn [disjoint_from]. split; [clear - HA LOH LQ'; lia|]. split; [clear - HA LOH LQ'; lia|].
        apply dj_of_Forall. apply Forall_forall. intros iv Hiv. apply in_map_iff in Hiv as (b' & <- & Hb'). destruct (BG1 b' Hb') as (B1 & B2 & _).
        unfold biv. cbn [fst snd]. clear - HA B1 B2 SP1 SP2 CLO LQ'. lia. }
      eapply (rw_cells_transport asegs _ mJ mK) in FRS; [| exact MUK| exact WMK| apply DJK; cbn [cells_size csize Nat.add]; lia].
      eapply (rw_cells_transport asegs _ mJ mK) in MTX; [| exact MUK| exact WMK| apply DJK; cbn [cells_size csize Nat.add]; lia].
      eapply (stk_transport_disjoint asegs _ mJ mK) in ST; [| exact MUK| exact WMK| apply DJK; clear - LQ'; lia].
      assert (MUT : munch (WJ gl) m mK).
      { eapply munch_trans; [exact MUJ|]. eapply munch_weaken; [| exact MUK]. intros x O. apply outside_of_In. intros iv Hiv.
        destruct Hiv as [<-|[<-|Hiv]].
        - exact (outside_In _ x _ O ltac:(right; right; left; reflexivity)).
        - pose proof (outside_In _ x (lo, q) O ltac:(left; reflexivity)) as O1. cbn [fst snd] in O1 |- *. clear - O1 LQ'. lia.
        - apply in_map_iff in Hiv as (b' & <- & Hb'). destruct (BG1 b' Hb') as (_ & _ & _ & _ & (b0 & Hb0 & EV)).
          pose proof (outside_In _ x (biv AL b0) O ltac:(right; right; right; apply in_map; exact Hb0)) as O1.
          unfold biv in *. rewrite (qb_addr_v AL b' b0 (eq_sym EV)). exact O1. }
      lz_here.
      eapply (qrec_tail2 X H m mK gl rest (ex ++ taken) hrest r4 r3 r2 r1 r0 rra); try eassumption.
      + exact (wmono_trans asegs _ _ _ WMJ WMK).
      + rewrite length_app. rewrite LBX in QBS.
        assert (LTK : (length taken <= length gl1)%nat) by (rewrite <- EAPP, length_app; lia). clear - QBS LB1 QB10 LTK. lia.
  Qed.

  #[using="AO LOH CLO LOQ QH Q16"] Theorem qrecycle_spec : forall (ra t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 t3 t4 t5 t6 : word)
        (X : pstate) (H : word -> bool) (m : mem) (gl : list qbatch) (hrest : list (Z * Z)),
    mclean H m -> stk asegs m lo q ->
    dr_inv AL E X H m gl (flat_map qb_chunks gl) hrest ->
    qlist_rep AL m gl 0 -> rw_cells asegs m QUAR_GQ (qcells AL gl) ->
    rw_cells asegs m QUAR_MTX [CB 4 [b8 0; b8 1; b8 0; b8 0]] ->
    Forall qbatch_wf gl -> qbytes gl < 2^56 ->
    implA H (t_dorecycle AL X (snd (q_recycle_sel gl)))
      (qrecycle_post ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 X H m gl hrest)
      (MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 (wz QUAR) (wz Q_MIN) (wz CACHE) stackw a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz qrecycle_entry) fc None m (seg_rom asegs)).
  Proof.
    intros ra t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 t3 t4 t5 t6 X H m gl hrest MC ST INV QLR GC MTX FWF QB.
    unfold qrecycle_entry.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    assert (LQ : lo <= q - 80 - 16) by (unfold QREC_STACK, DOREC_STACK, AREC_STACK, CDEALLOC_STACK, MF_STACK in LOQ; lia).
    pose proof INV as (RP & POK & RS & MI & PE & TE & SV & WFS & REPS & HKS & HOK & NDS & BWF & BREP).
    unfold qcells in GC. unfold b8 in MTX.
    pose proof (munch_refl [(lo, q); (QUAR_MTX, QUAR_MTX + 4); (QUAR_GQ, QUAR_GQ + 32)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    lz_go.
    zstep. carve_frame 80%nat ST.
    do 6 zstep.
    do 4 sstep.
    do 4 zstep.

    amo_step.   try fold_cb_load.
    do 4 zstep.
    amo_step.
    zstep. if_false.
    zstep.

    zstep. if_false.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mA end.
    replace (q + -80) with (q - 80) in * by lia.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mf _) =>
      apply (rw_cells_rebytes mf QUAR_MTX _ [CB 4 [Z_to_bv 8 1; Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 0]]) in MTX;
        [| cbn; tauto| cbn; repeat first [ reflexivity | apply (f_equal2 cons); [apply bv_eq; vm_compute; reflexivity|] ]| reflexivity] end.
    destruct (proj1 (rw_cells_app asegs mA (q - 80) [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)] [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) FR) as [TCC FRS].
    cbn [cells_size csize Nat.add] in FRS. replace (q - 80 + Z.of_nat 32) with (q - 48) in FRS by lia. clear FR.

    destruct (clear_ctx AL X m RP RS) as (WF0 & SOK & SSEP).
    layout_facts AO 0%nat SPF. destruct SPF as (SP1 & SP2 & SPM & _ & SP5 & _ & _).
    assert (FBW : Forall bwf gl).
    { eapply Forall_impl; [| exact FWF]. intros b' (_ & _ & W3 & W4 & W5). unfold bwf. split; [| exact W3]. rewrite W4.
      assert (S0 : forall l : list qchunk, Forall qchunk_wf l -> 0 <= fold_right (fun ch acc => qc_n ch + acc) 0 l)
        by (induction 1 as [|c l (_ & _ & N1 & _) _ IHl]; cbn [fold_right]; lia).
      pose proof (S0 _ W5). lia. }
    pose proof (bwf_qbytes_len gl FBW) as LBG. pose proof (bwf_qbytes_nonneg gl FBW) as QB0.
    assert (BG : forall b, In b gl -> al_space AL <= qb_addr AL b /\ qb_addr AL b + 8192 <= al_space AL + K_SPACE /\ (16 * qb_v b) mod 8192 = 0).
    { intros b Hb. assert (HBb : held1 (fst X) (bpair b)) by (destruct HOK as [_ FH]; apply (proj1 (Forall_forall _ _) FH); apply in_or_app; left; apply in_map; exact Hb).
      pose proof (held_geo AL (fst X) AO WF0 K_BCLASS (qb_v b) HBb) as G. cbv zeta in G.
      destruct G as (_ & G1 & G2 & G3 & _). pose proof (region_range AL K_BCLASS ltac:(lia)) as [R1 R2].
      destruct HBb as (_ & _ & _ & VAL & _). cbn [fst snd bpair] in VAL.
      change (class_size K_BCLASS) with 8192 in *. fold (qb_addr AL b) in G1, G2. clear - G1 G2 G3 R1 R2 VAL. lia. }
    assert (QMA : qmain_list AL mA gl 0).
    { pose proof (proj1 (proj1 (qlist_rep_main AL m gl 0) QLR)) as QM0.
      eapply (qmain_list_frame AL _ m mA gl 0 QM0 MU WM). apply Forall_forall. intros b Hb. destruct (BG b Hb) as (B1 & B2 & _).
      cbn [disjoint_from]. clear - B1 B2 SP1 SP2 CLO. lia. }
    rewrite (q_recycle_sel_eq gl). unfold qrecycle_post. rewrite (q_recycle_sel_eq gl). cbv zeta.
    do 3 zstep.
    zstep. if_cases KC; zify_cond KC.

    { exfalso. rewrite Z.shiftl_mul_pow2, Z.mod_small in KC by (change (2^13) with 8192; clear - LBG QB QB0; lia). change (2^13) with 8192 in KC. clear - KC LBG. lia. }
    clear KC.
    rewrite (Z.shiftl_mul_pow2 (Z.of_nat (length gl)) 13) by lia. change (2^13) with 8192.

    assert (SKIP : (8192 * Z.of_nat (length gl) <? qbytes gl) && (qbytes gl * 100 <? 8192 * Z.of_nat (length gl) * 200) = false ->
              forall y4 y5 y7 : word,
              evt asegs
                (lzk H (t_dorecycle AL X
                          (snd (if (8192 * Z.of_nat (length gl) <? qbytes gl) && (qbytes gl * 100 <? 8192 * Z.of_nat (length gl) * 200) then q_merge_list gl else (gl, []))
                           ++ fst (q_dequeue (fst (if (8192 * Z.of_nat (length gl) <? qbytes gl) && (qbytes gl * 100 <? 8192 * Z.of_nat (length gl) * 200) then q_merge_list gl else (gl, [])))
                                             (qbytes (fst (if (8192 * Z.of_nat (length gl) <? qbytes gl) && (qbytes gl * 100 <? 8192 * Z.of_nat (length gl) * 200) then q_merge_list gl else (gl, [])))) Q_MIN)))
                   (qrec_post_gen ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 X H m gl hrest
                      (snd (q_dequeue (fst (if (8192 * Z.of_nat (length gl) <? qbytes gl) && (qbytes gl * 100 <? 8192 * Z.of_nat (length gl) * 200) then q_merge_list gl else (gl, [])))
                                      (qbytes (fst (if (8192 * Z.of_nat (length gl) <? qbytes gl) && (qbytes gl * 100 <? 8192 * Z.of_nat (length gl) * 200) then q_merge_list gl else (gl, [])))) Q_MIN))
                      (snd (if (8192 * Z.of_nat (length gl) <? qbytes gl) && (qbytes gl * 100 <? 8192 * Z.of_nat (length gl) * 200) then q_merge_list gl else (gl, []))
                       ++ fst (q_dequeue (fst (if (8192 * Z.of_nat (length gl) <? qbytes gl) && (qbytes gl * 100 <? 8192 * Z.of_nat (length gl) * 200) then q_merge_list gl else (gl, [])))
                                         (qbytes (fst (if (8192 * Z.of_nat (length gl) <? qbytes gl) && (qbytes gl * 100 <? 8192 * Z.of_nat (length gl) * 200) then q_merge_list gl else (gl, [])))) Q_MIN))))
                (MS (mkR ra (wz (q - 80)) gp (wz A0_TP) (wz 256) (wz 0) t2 s0 s1 (wz QUAR) (wz Q_MIN) (wz CACHE) stackw y4 y5 (wz (Z.of_nat (length gl))) y7
                         s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F_ (wz 0x354b4) fc None mA (seg_rom asegs))).
    { intros CF y4 y5 y7. rewrite CF. cbn [fst snd].
      lz_here.
      eapply (qrec_tail X H m mA gl gl [] hrest s4 s3 s2 s1 s0 ra); try eassumption.
      - eapply munch_weaken; [| exact MU]. apply sub_fp_incl. intros iv [<-|[<-|[<-|[]]]]; [left; reflexivity| right; left; reflexivity| right; right; left; reflexivity].
      - exact I.
      - rewrite app_nil_r. apply Permutation_refl.
      - reflexivity.
      - constructor.
      - cbn [qbytes fold_right]. clear - QB. lia. }
    zstep. if_cases KS1; zify_cond KS1.
    { apply SKIP. apply andb_false_iff. left. apply Z.ltb_ge. clear - KS1. lia. }

    do 4 zstep.
    zstep. if_cases KS2; zify_cond KS2.
    { apply SKIP. apply andb_false_iff. right. apply Z.ltb_ge. clear - KS2. lia. }

    do 7 zstep.
    zstep.

    assert (CT : (8192 * Z.of_nat (length gl) <? qbytes gl) && (qbytes gl * 100 <? 8192 * Z.of_nat (length gl) * 200) = true)
      by (apply andb_true_iff; split; apply Z.ltb_lt; clear - KS1 KS2; lia).
    rewrite CT. clear SKIP.
    assert (PF : Permutation (map qb_v (fst (q_merge_list gl) ++ snd (q_merge_list gl))) (map qb_v gl)
                 /\ flat_map qb_chunks (fst (q_merge_list gl)) = flat_map qb_chunks gl
                 /\ Forall qbatch_wf (fst (q_merge_list gl)) /\ Forall bex (snd (q_merge_list gl))
                 /\ qbytes (fst (q_merge_list gl)) + qbytes (snd (q_merge_list gl)) = qbytes gl).
    { destruct gl as [|b r]; [cbn; repeat split; try constructor|]. cbn [q_merge_list].
      split; [apply q_merge_perm|]. split; [apply (q_merge_chunks r b)|]. split; [apply q_merge_wf; exact FWF|]. split; [apply q_merge_ex|].
      rewrite (q_merge_bytes r b), (qbytes_bex _ (q_merge_ex r b)). lia. }
    destruct PF as (PF1 & PF2 & PF3 & PF4 & PF5).
    assert (NDV : List.NoDup (map qb_v gl)).
    { destruct HOK as [ND _]. apply NoDup_app_remove_r in ND. unfold bpair in ND. rewrite <- (map_map qb_v (fun v => (K_BCLASS, v))) in ND. apply NoDup_map_inv in ND. exact ND. }
    eapply evt_cut.
    { eapply (merge_spec AL QUAR_GQ (q - 80) ltac:(lia) ltac:(clear - QH; lia) (wz 218272) gp (wz A0_TP) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F_ fc mA gl lo (q - 80));
        [ assumption | exact ST | exact LQ | lia | clear - LOH; lia | intros b Hb; destruct (BG b Hb) as (B1 & B2 & _); clear - B2 SP2 CLO; lia
        | exact QMA | unfold qcells; exact GC | exact TCC | exact NDV
        | apply Forall_forall; intros b Hb; destruct (BG b Hb) as (B1 & B2 & B3); unfold bgeo; clear - B1 B2 B3 SP1 SP2 CLO LQ; lia
        | exact FBW | clear - QB; lia | clear - QB LBG; lia ]. }
    cbv beta. unfold merge_post.
    intros ms1 (y5 & y6 & y7 & y1 & y2 & y3 & y4 & y5' & y6' & y7' & y28 & y29 & y30 & m1 & -> & MU1 & WM1 & MI1 & ST1 & QL1 & QE1 & GC1 & TC1).

    assert (DJ1 : forall A n, (q - 48 <= A \/ A + n <= QUAR_GQ) ->
                    disjoint_from ((q - 80 - 16, q - 80) :: (QUAR_GQ, QUAR_GQ + 32) :: (q - 80, q - 80 + 32) :: map (biv AL) gl) A n).
    { intros A n HA. cbn [disjoint_from]. split; [clear - HA LOH LQ; lia|]. split; [clear - HA LOH LQ; lia|]. split; [clear - HA LOH LQ; lia|].
      apply dj_of_Forall. apply Forall_forall. intros iv Hiv. apply in_map_iff in Hiv as (b' & <- & Hb'). destruct (BG b' Hb') as (B1 & B2 & _).
      unfold biv. cbn [fst snd]. clear - HA B1 B2 SP1 SP2 CLO LQ. lia. }
    eapply (rw_cells_transport asegs _ mA m1) in FRS; [| exact MU1| exact WM1| apply DJ1; cbn [cells_size csize Nat.add]; lia].
    eapply (rw_cells_transport asegs _ mA m1) in MTX; [| exact MU1| exact WM1| apply DJ1; cbn [cells_size csize Nat.add]; lia].
    assert (MUT : munch (WJ gl) m m1).
    { eapply munch_trans; [eapply munch_weaken; [| exact MU]| eapply munch_weaken; [| exact MU1]].
      - apply sub_fp_incl. intros iv [<-|[<-|[<-|[]]]]; [left; reflexivity| right; left; reflexivity| right; right; left; reflexivity].
      - intros x O. cbn [outside] in O. destruct O as (O1 & O2 & O3 & O4). cbn [fst snd] in O1. cbn [outside].
        split; [clear - O1 LQ; lia|]. split; [exact O3|]. split; [clear - O1 LQ; lia| exact O4]. }
    replace (ret_pc (Z_to_bv 64 218272)) with (Z_to_bv 64 218272) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    unfold qcells in GC1.
    do 4 zstep.
    zstep.
    lz_here.
    eapply (qrec_tail X H m m1 gl (fst (q_merge_list gl)) (snd (q_merge_list gl)) hrest s4 s3 s2 s1 s0 ra); try eassumption.
    - exact (wmono_trans asegs _ _ _ WM WM1).
    - rewrite PF5. clear - QB. lia.
  Qed.
End QREC.

