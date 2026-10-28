(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Sj Require Import SjNumber SjNumU SjNumN.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.P Require Import Rnd Sj_num_kit Sj_num_walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout RT_iface D_defs D_kit D_clx D_rlkit I_lkit Sj_akit Sj_acps Sj_hkit Sj_rtf
  Sj_num_akit Sj_num_amem Sj_num_iface Sj_num_abig Sj_num_acall Sj_num_acall2 Sj_num_aframe Sj_num_lits Sj_num_bkit Sj_num_bdefs Sj_num_lm_kit
  Sj_num_fc_stmt Sj_num_fc_defs Sj_num_fc_rel Sj_num_fc_pro Sj_num_fc_pro2 Sj_num_fc_tail Sj_num_fc_k14 Sj_num_fc_dc Sj_num_fc_top14 Sj_num_fc_tkit Sj_num_fc_ctop1 Sj_num_fc_ctop2 Sj_num_fc_ctop3 Sj_num_fc_ctop4 Sj_num_fc_pp1.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Ltac fcb_at_simpl :=
  repeat match goal with
  | H : context [fcb_W (fcb_at ?E0 ?m0)] |- _ => change (fcb_W (fcb_at E0 m0)) with (fcb_W E0) in H
  | |- context [fcb_W (fcb_at ?E0 ?m0)] => change (fcb_W (fcb_at E0 m0)) with (fcb_W E0)
  | H : context [fcb_saved (fcb_at ?E0 ?m0)] |- _ => change (fcb_saved (fcb_at E0 m0)) with (fcb_saved E0) in H
  | |- context [fcb_saved (fcb_at ?E0 ?m0)] => change (fcb_saved (fcb_at E0 m0)) with (fcb_saved E0)
  end;
  cbn [fcb_at q_ra q_sp q_gp q_tp q_s0 q_s1 q_s2 q_s3 q_s4 q_s5 q_s6 q_s7 q_s8 q_s9 q_s10 q_s11 q_A q_FIRST q_LAST q_OUT q_lo q_spq q_f q_txt q_m0] in *.

Ltac fc_close_at :=
  unfold FCINV; fcb_at_simpl;
  split; [unfold fcb_spill; fcb_at_simpl; eassumption|]; split; [do 4 eexists; unfold fcb_pns; eassumption|]; split; [lia|]; split; [lia|];
  split; [fcp_forget_obj|]; split; [fcp_forget_obj|];
  split; [first [ intros BGF; discriminate BGF | intros _; fcp_forget_obj ]|];
  split; [eassumption|]; split; [eexists; eassumption|];
  split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; eassumption.

Section FCTOP.
  Variable RT : rt_sig.
  Hypothesis AF : art_facts RT.
  Hypothesis RTF : rt_contracts_f RT.
  Variable PMc : Model -> Prop.
  Hypothesis FDO : fdfs_only PMc.
  Hypothesis MST : mat_stable PMc.
  Hypothesis HPDC : pdcb_stmt RT PMc.
  Hypothesis HNDC : ndcb_stmt RT PMc.

  Variables (Σ0 : rts RT) (K : config -> Prop).

  Variable E : fcbenv.
  Variables (p n : Z) (me : mem).
  Notation SP := (q_SP E).
  Notation S := (q_S E).
  Notation f := (q_f E).
  Notation lo := (q_lo E).
  Notation spq := (q_spq E).
  Notation OUT := (q_OUT E).
  Notation A := (q_A E).
  Notation FIRST := (q_FIRST E).
  Notation LAST := (q_LAST E).
  Notation TL := (q_TL E).
  Hypothesis OK : fcb_ok E.
  Hypothesis ETP : q_tp E = Z_to_bv 64 B_TP.
  Hypothesis SP16 : (SP mod 16 = 0)%Z.
  Hypothesis LOR : (rt_sp0 RT Σ0 - STACK_WIN <= lo)%Z.
  Hypothesis FRL : (length (rt_frames RT Σ0) + FFB_FRAMES <= FRAMES_MAX)%nat.
  Hypothesis CRD : (FFB_CREDIT <= rt_credit RT Σ0)%Z.

  Hypothesis PIN : In (p, n) (rt_live RT Σ0).
  Hypothesis PCH : (p mod 8 = 0 /\ p <= A /\ LAST + 8 <= p + n /\ A + TL <= p + n)%Z.

  Hypothesis HK : forall (Σ' : rts RT) t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' (v : word), frm0 fc' ->
     rt_after RT Σ' SP lo me m' -> rt_pres_ex (rt_live RT Σ0) (rt_frames RT Σ0) SP OUT 8 me m' ->
     rw_cells bsegs m' OUT [C8 v] ->
     rt_frames RT Σ' = rt_frames RT Σ0 -> rt_live RT Σ' = rt_live RT Σ0 -> rt_sp0 RT Σ' = rt_sp0 RT Σ0 ->
     (rt_credit RT Σ0 - FFB_CREDIT <= rt_credit RT Σ')%Z ->
     aevt RT PMc Σ' K (MS (mkR (q_ra E) (q_sp E) (q_gp E) (q_tp E) t0' t1' t2' (q_s0 E) (q_s1 E) a0' a1' a2' a3' a4' a5' a6' a7'
                               (q_s2 E) (q_s3 E) (q_s4 E) (q_s5 E) (q_s6 E) (q_s7 E) (q_s8 E) (q_s9 E) (q_s10 E) (q_s11 E) t3' t4' t5' t6')
                          F' (ret_pc (q_ra E)) fc' None m' (seg_rom bsegs)).
  Collection TOPH := AF RTF FDO MST HPDC HNDC OK ETP SP16 LOR FRL CRD PIN PCH HK.

  Notation MREL := (fc_mrel RT Σ0 E me).
  Notation PARK := (fc_park E).
  Notation W := (fcb_W E).
  Notation QΣ Σ := (fun ms' => aevt RT PMc Σ K ms').
  Notation EB mb := (fcb_at E mb).

  Notation T1 L := (L RT AF RTF PMc FDO MST HPDC HNDC Σ0 K E p n me OK ETP SP16 LOR FRL CRD PIN PCH HK) (only parsing).
  Notation fc_srel := (Sj_num_fc_ctop1.fc_srel RT Σ0 E).
  Notation fc_ctx := (Sj_num_fc_ctop1.fc_ctx RT Σ0 E me).
  Notation TK L Σ SR := (L RT AF Σ0 Σ E OK LOR (proj1 SR) (proj1 (proj2 SR)) (proj1 (proj2 (proj2 SR)))) (only parsing).
  Notation TKm L Σ SR := (L RT AF Σ0 Σ E me OK LOR (proj1 SR) (proj1 (proj2 SR)) (proj1 (proj2 (proj2 SR)))) (only parsing).

  Ltac top_env Σ SR :=
    pose proof OK as OK'; destruct OK' as [ROOM TOP [SPQ1 SPQ2] (F64 & FLO1 & FLO2) FSH FS0 (TX1 & TX2 & TX3) (FL1 & FL2 & FL3) (TS1 & TS2) (O1 & O2 & O3)];
    unfold SPB_STACK, NDCB_STACK, P5B_STACK, LMB_STACK, RT_STACK, FCB_GTOP, NUM_TXT_MAX, USTACK_TOP in *;
    pose proof (bv_unsigned_in_range 64 (q_sp E)) as SPR; unfold bv_modulus in SPR; cbn in SPR;
    pose proof (T1 top_inF Σ _ SR) as HinF; pose proof (T1 top_inP Σ _ SR) as HinP; pose proof PCH as (PC1 & PC2 & PC3 & PC4);
    pose proof (f64_8 f F64) as F8; pose proof (eq_refl : fs_size 4 = 1024%Z) as FS4.

  Ltac err_after_call mm m' AG WM' :=
    rt_transport_with mm m' AG WM' ltac:(intros x Hx; cbn [cells_size csize Nat.add length] in Hx; rewrite ?repeat_length in Hx; cbv beta; split; [aclient_tac | lia]).

  Lemma fc_stk_chk : forall Σ used (mm : mem) (jp : list byte) dd nn, fc_srel Σ used -> ART RT Σ mm ->
    rw_cells bsegs mm (spq + 72) [CB 72 jp] -> (spq + 72 <= dd)%Z -> (0 <= nn)%Z -> (dd + nn <= spq + 144)%Z ->
    checked_dst RT Σ mm (Z_to_bv 64 spq) dd nn.
  Proof using TOPH.
    intros Σ used mm jp dd nn SR HA PNS D0 N0 DN. top_env Σ SR. clear FSH TS1 TS2.
    pose proof (T1 top_lor1 Σ used SR) as L1. unfold STACK_WIN in L1.
    unfold checked_dst. rewrite unsigned_lit by lia.
    split; [intros _; split|split].
    - apply (af_acc_stack RT AF Σ mm dd nn HA); unfold STACK_WIN, USTACK_TOP; lia.
    - right; right; left. unfold STACK_WIN, USTACK_TOP. lia.
    - intros i Hi. left. unfold USTACK_TOP. lia.
    - pose proof (rw_cells_wr_at bsegs mm (spq + 72) [CB 72 jp] 72 PNS ltac:(cbn [cells_size csize Nat.add]; lia)) as WR.
      exact (wr_at_sub mm _ _ dd nn WR D0 ltac:(lia) N0).
  Qed.

  Lemma fc_pns_memset : forall Σ used fc (mm : mem) (jp : list byte) (dz nz : Z)
      (xra xgp xtp xt0 xt1 xt2 xs0 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 : word) xF xfc,
    fc_ctx Σ used fc mm -> rw_cells bsegs mm (spq + 72) [CB 72 jp] -> forall a : Z, (a = spq + 72 + dz)%Z ->
    mem_inv bsegs mm -> stk bsegs mm lo spq -> frm0 xfc ->
    (0 <= dz)%Z -> (0 <= nz)%Z -> (dz + nz <= 72)%Z ->
    (forall t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m', fc_ctx Σ used fc' m' -> frm0 fc' ->
       rt_after RT Σ spq lo mm m' -> rt_pres_ex (rt_live RT Σ) (rt_frames RT Σ) spq a nz mm m' ->
       rw_cells bsegs m' a [CB (Z.to_nat nz) (repeat (Z_to_bv 8 0) (Z.to_nat nz))] ->
       aevt RT PMc Σ K (MS (mkR xra (Z_to_bv 64 spq) xgp xtp t0' t1' t2' xs0 (Z_to_bv 64 spq) (Z_to_bv 64 a) a1' a2' a3' a4' a5' a6' a7' xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9
                               xs10 xs11 t3' t4' t5' t6') F' (ret_pc xra) fc' None m' (seg_rom bsegs))) ->
    aevt RT PMc Σ K (MS (mkR xra (Z_to_bv 64 spq) xgp xtp xt0 xt1 xt2 xs0 (Z_to_bv 64 spq) (Z_to_bv 64 a) (Z_to_bv 64 0) (Z_to_bv 64 nz) xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9
                            xs10 xs11 xt3 xt4 xt5 xt6) xF (Z_to_bv 64 0x7f338) xfc None mm (seg_rom bsegs)).
  Proof using TOPH.
    intros Σ used fc mm jp dz nz. intros until xfc. intros CTXm PNS a -> MI ST FRMx D0 N0 DN HKc.
    pose proof CTXm as (SR & HU & FRM & ARTm & MRm & PKm).
    pose proof (fc_stk_chk Σ used mm jp (spq + 72 + dz)%Z nz SR ARTm PNS ltac:(lia) N0 ltac:(lia)) as CD.
    top_env Σ SR. clear FSH TS1 TS2.
    eapply (aevt_memset RT RTF PMc FDO MST Σ K) with (d := (spq + 72 + dz)%Z) (n := nz) (cb := Z_to_bv 8 0) (lo := lo);
      [reflexivity | reflexivity | reflexivity | lia | lia | exact CD | exact ARTm | exact MI | exact (T1 top_cok Σ used mm SR ST) | exact FRMx |].
    intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' FRM' RA PR BY.
    rewrite ?unsigned_lit in RA, PR by lia.
    pose proof (T1 fc_ctx_call Σ used fc fc' mm m' _ _ CTXm FRM' RA PR ltac:(right; lia)) as CTX'.
    pose proof RA as (_ & _ & WM' & _).
    assert (MID : rw_cells bsegs m' (spq + 72 + dz) [CB (Z.to_nat nz) (repeat (Z_to_bv 8 0) (Z.to_nat nz))]).
    { pose proof (rw_cells_CB_intro m' (spq + 72 + dz) (repeat (Z_to_bv 8 0) (Z.to_nat nz)) BY) as H. rewrite repeat_length in H. apply H.
      rewrite Z2Nat.id by lia. exact (wr_at_transport bsegs mm m' _ _ (proj2 (proj2 CD)) WM'). }
    exact (HKc t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' CTX' FRM' RA PR MID).
  Qed.

  Lemma fc_kerr2 : forall Σ fc mb, fc_ctx Σ 0 fc mb -> fcb_kerr2 (EB mb) (QΣ Σ).
  Proof using TOPH.
    intros Σ fc mb CTX. unfold fcb_kerr2. intros ra2 HIN. intros until je. intros INV FRM1 KIND.
    fce_open INV. fcb_at_simpl.
    pose proof (T1 top_ctx_step Σ 0%Z fc mb mm CTX MU WM) as CTXm. clear CTX MU WM.
    pose proof CTXm as (SR & HU & FRM & ARTm & MRm & PKm). top_env Σ SR. clear FSH TS1 TS2.

    destruct (rw_cells_forget bsegs mm _ _ PNS) as (jp1 & PNSF). cbn [cells_size csize Nat.add] in PNSF.
    change [CB 32 jp; CB 32 Z32; CB 8 je] with ([CB 32 jp] ++ [CB 32 Z32] ++ [CB 8 je]) in PNS.
    apply num_rw_cells_app in PNS. destruct PNS as [Q12 PNS]. apply num_rw_cells_app in PNS. destruct PNS as [Q3 Q4].
    cbn [cells_size csize Nat.add] in Q3, Q4.
    replace (spq + 72 + Z.of_nat 32)%Z with (spq + 104)%Z in * by lia. replace (spq + 104 + Z.of_nat 32)%Z with (spq + 136)%Z in * by lia.
    apply (rw_cells_split_CB bsegs mm _ [] 32 jp [] [27; 5]%nat) in Q12; [| reflexivity]. cbn [mk_CB_cells app] in Q12.
    repeat match type of Q12 with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in Q12; clearbody j end.
    lazymatch type of Q12 with rw_cells _ _ _ [?c1; ?c2] => change [c1; c2] with ([c1] ++ [c2]) in Q12 end.
    apply num_rw_cells_app in Q12. destruct Q12 as [Q1 Q2]. cbn [cells_size csize Nat.add] in Q2. replace (spq + 72 + Z.of_nat 27)%Z with (spq + 99)%Z in * by lia.
    apply evt_done.
    eapply (fc_pns_memset Σ 0%Z fc mm jp1 0 27); [exact CTXm | exact PNSF | lia | exact MI | exact ST | exact FRM1 | lia | lia | lia |].
    intros t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' F'' fc'' m'' CTX'' FRM'' RA2 PR2 MID2.
    destruct RA2 as (ART'' & MI'' & WM'' & ST'').
    pose proof (agree_of_pres_ex _ _ _ _ _ mm m'' _ PR2 (fun x H => H)) as AG2.
    clear Q1 PNSF ST MI PKm.
    err_after_call mm m'' AG2 WM''.
    change (Z.to_nat 27) with 27%nat in MID2.
    lazymatch type of Q2 with rw_cells _ _ _ [CB 5 ?j5] =>
      assert (PNS2 : rw_cells bsegs m'' (spq + 72) [CB 27 Z27; CB 5 j5; CB 32 Z32; CB 8 je])
        by (change [CB 27 Z27; CB 5 j5; CB 32 Z32; CB 8 je] with ([CB 27 Z27] ++ [CB 5 j5] ++ [CB 32 Z32] ++ [CB 8 je]);
            apply num_rw_cells_app; split; [exact MID2|]; cbn [cells_size csize Nat.add]; replace (spq + 72 + Z.of_nat 27)%Z with (spq + 99)%Z by lia;
            apply num_rw_cells_app; split; [exact Q2|]; cbn [cells_size csize Nat.add]; replace (spq + 99 + Z.of_nat 5)%Z with (spq + 104)%Z by lia;
            apply num_rw_cells_app; split; [exact Q3|]; cbn [cells_size csize Nat.add]; replace (spq + 104 + Z.of_nat 32)%Z with (spq + 136)%Z by lia; exact Q4);
      assert (L5 : length j5 = 5%nat) by exact (proj1 (proj1 (proj1 Q2)))
    end.
    assert (L8 : length je = 8%nat) by exact (proj1 (proj1 (proj1 Q4))).
    pose proof CTX'' as (SR'' & HU'' & FRMc'' & ARTc'' & MRc'' & PKc'').
    pose proof (munch_refl (fcb_W (EB m'')) m'') as MU2. pose proof (wmono_refl bsegs m'') as WM2.
    lazymatch type of PNS2 with rw_cells _ _ _ ?pl =>
      assert (INV2 : FCEINV (EB m'') m'' c0 c8 c16 c24 c32 c40 c48 c56 pl)
        by (unfold FCEINV; fcb_at_simpl;
            split; [unfold fcb_spill; fcb_at_simpl; eassumption|]; split; [exact PNS2|]; split; [eexists; eassumption|]; split; [eexists; eassumption|];
            split; [eexists; eassumption|]; split; [eexists; eassumption|]; split; [eexists; eassumption|];
            split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; eassumption)
    end.
    apply (aevt_evt RT AF PMc MST).
    unfold FCB_ERR2 in HIN. cbn [In] in HIN.
    destruct HIN as [<- | [<- | [<- | [<- | [<- | []]]]]]; num_ret_pc;
      (eapply evt_eq; [| eapply (fcb_err_tail (EB m'') (T1 top_okb m'') (QΣ Σ)
                                   (fcb_f14 (EB m'') (T1 top_okb m'') (T1 top_prov Σ 0%Z m'' SR'' ARTc'') (QΣ Σ) (T1 fc_kf5 Σ 0%Z fc'' m'' CTX'') (T1 fc_kmset Σ fc'' m'' CTX'')))];
         [num_st_eq | unfold FCB_ERR2; cbn [In]; repeat (first [left; reflexivity | right]) | exact INV2 | exact FRM'' | exact L5 | exact L8 | exact KIND]).
  Qed.

  Lemma fc_kerr1 : forall Σ fc mb, fc_ctx Σ 0 fc mb -> fcb_kerr1 (EB mb) (QΣ Σ).
  Proof using TOPH.
    intros Σ fc mb CTX. unfold fcb_kerr1. intros ra1 HIN. intros until c56. intros INV FRM1 KIND.
    fcp_open INV. fcb_at_simpl.
    pose proof (T1 top_ctx_step Σ 0%Z fc mb mm CTX MU WM) as CTXm. clear CTX MU WM.
    pose proof CTXm as (SR & HU & FRM & ARTm & MRm & PKm). top_env Σ SR. clear FSH TS1 TS2.
    apply evt_done.
    eapply (fc_pns_memset Σ 0%Z fc mm jp 32 32); [exact CTXm | exact PNS | lia | exact MI | exact ST | exact FRM1 | lia | lia | lia |].
    intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' CTX' FRM' RA PR MID.

    apply (rw_cells_split_CB bsegs mm _ [] 72 jp [] [32; 32; 8]%nat) in PNS; [| reflexivity]. cbn [mk_CB_cells app] in PNS.
    repeat match type of PNS with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in PNS; clearbody j end.
    lazymatch type of PNS with rw_cells _ _ _ [?c1; ?c2; ?c3] => change [c1; c2; c3] with ([c1] ++ [c2] ++ [c3]) in PNS end.
    apply num_rw_cells_app in PNS. destruct PNS as [Q1 PNS]. apply num_rw_cells_app in PNS. destruct PNS as [Q3 Q4].
    cbn [cells_size csize Nat.add] in Q3, Q4.
    replace (spq + 72 + Z.of_nat 32)%Z with (spq + 104)%Z in * by lia. replace (spq + 104 + Z.of_nat 32)%Z with (spq + 136)%Z in * by lia.
    destruct RA as (ART' & MI' & WM' & ST').
    pose proof (agree_of_pres_ex _ _ _ _ _ mm m' _ PR (fun x H => H)) as AG.
    clear Q3 ST MI PKm.
    err_after_call mm m' AG WM'.
    change (Z.to_nat 32) with 32%nat in MID. replace (spq + 72 + 32)%Z with (spq + 104)%Z in MID by lia.
    lazymatch type of Q1 with rw_cells _ _ _ [CB 32 ?ja] => lazymatch type of Q4 with rw_cells _ _ _ [CB 8 ?jc] =>
      assert (PNS1 : rw_cells bsegs m' (spq + 72) [CB 32 ja; CB 32 Z32; CB 8 jc])
        by (change [CB 32 ja; CB 32 Z32; CB 8 jc] with ([CB 32 ja] ++ [CB 32 Z32] ++ [CB 8 jc]);
            apply num_rw_cells_app; split; [exact Q1|]; cbn [cells_size csize Nat.add]; replace (spq + 72 + Z.of_nat 32)%Z with (spq + 104)%Z by lia;
            apply num_rw_cells_app; split; [exact MID|]; cbn [cells_size csize Nat.add]; replace (spq + 104 + Z.of_nat 32)%Z with (spq + 136)%Z by lia; exact Q4)
    end end.
    pose proof (munch_refl (fcb_W (EB m')) m') as MU1. pose proof (wmono_refl bsegs m') as WM1.
    lazymatch type of PNS1 with rw_cells _ _ _ ?pl =>
      assert (INV1 : FCEINV (EB m') m' c0 c8 c16 c24 c32 c40 c48 c56 pl)
        by (unfold FCEINV; fcb_at_simpl;
            split; [unfold fcb_spill; fcb_at_simpl; eassumption|]; split; [exact PNS1|]; split; [eexists; eassumption|]; split; [eexists; eassumption|];
            split; [eexists; eassumption|]; split; [eexists; eassumption|]; split; [eexists; eassumption|];
            split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; eassumption)
    end.
    apply (aevt_evt RT AF PMc MST).
    unfold FCB_ERR1 in HIN. cbn [In] in HIN.
    destruct HIN as [<- | [<- | [<- | [<- | [<- | []]]]]]; num_ret_pc;
      (eapply evt_eq; [| eapply (fcb_err_mid (EB m') (T1 top_okb m') (QΣ Σ) (fc_kerr2 Σ fc' m' CTX'))];
         [num_st_eq | unfold FCB_ERR1; cbn [In]; repeat (first [left; reflexivity | right]) | exact INV1 | exact FRM' | exact KIND]).
  Qed.
End FCTOP.
