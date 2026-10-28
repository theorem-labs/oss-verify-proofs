From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_FseDecompRT
  HufPure_HufStats HufPure_HufStatsRT HufPure_HufX1 HufPure_HufTableX1 HufPure_HufTableX1RT HufPure_FseReadBridge.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge InitMem RunConst Step Frame.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit FseWalkMem FseWalkArith StrFun HufWalkKit FseRdKit2 WStr.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RF_huf_iface RF_huf_h_iface RF_huf_tbl_iface RF_huf_tbl_iface2
  RF_huf_tbl_kit RF_huf_fdw_kit RF_huf_fdw_tk RF_huf_bdt_model RF_huf_x1t_model RF_huf_x1t_cls RF_huf_x1t_wk RF_huf_x1t_top RF_huf_x1t_fw.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma sob_nth_bound : forall (l : list Z) j, Forall (fun v => 0 <= v <= 256) l -> 0 <= nth j l 0 <= 256.
Proof.
  induction l as [|a l IH]; intros j H; destruct j as [|j]; cbn; try lia.
  - inversion H; subst; assumption.
  - inversion H; subst; apply IH; assumption.
Qed.

Lemma sob_sort_len : forall f n ws rs syms r, sort_loop f n ws rs syms = Ok r -> length (snd r) = length syms.
Proof.
  induction f as [|f IH]; intros n ws rs syms r H.
  - cbn [sort_loop] in H. injection H as <-. reflexivity.
  - rewrite sort_loop_S in H.
    apply bind_Ok_inv in H as (w & _ & H). apply bind_Ok_inv in H as (p & _ & H).
    apply bind_Ok_inv in H as (rs' & _ & H). apply bind_Ok_inv in H as (syms' & OS & H).
    rewrite (IH _ _ _ _ _ H). revert OS. unfold ostore. destruct (_ && _); intros OS; [| discriminate].
    injection OS as <-. apply oupd_nat_length.
Qed.

Section CANSEC. Context {rc : runConstT}.
Section TOP.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : fmem) (DT W S mtl lo : Z) (src : list Z).
  Notation SP := (bv_unsigned sp).
  Notation POST := (huf_rdt_post huf_dt_ok ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc DT W S mtl src lo m).
  Notation WALL := [(bv_unsigned sp - HUF_RDT_STACK, bv_unsigned sp); (DT, DT + DTABLE_BYTES mtl); (W, W + 8704)].
  Lemma x1_1520 : forall m5 h ws rank tl rs rs2 syms jdt jsy j8 (c1 c2 cw cc x1 x5 x6 x7 x8 x10 x12 x14 x15 x17 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    read_stats src = Ok h -> stats_ok h -> 1 <= hs_ret h <= 129 -> Forall (fun c => 0 <= c < 256) src ->
    1 <= mtl <= 12 -> 0 < DT -> DT mod 8 = 0 -> DT + 4 * (1 + 2 ^ mtl) <= lo -> 0 < W -> W mod 8 = 0 -> W + 8704 <= lo ->
    lo <= SP - 4096 -> SP <= 2 ^ 47 -> SP mod 16 = 0 ->
    hk (DT + 4 * (1 + 2 ^ mtl) <= W \/ W + 8704 <= DT) ->
    rescale (hs_weights h) (hs_rank h) (hs_nbSymbols h) (hs_tableLog h) (Z.min (mtl + 1) 11) = Ok (ws, rank, tl) ->
    tl <= mtl + 1 ->
    rank_start_loop (Z.to_nat (tl + 1)) 0 0 rank (repeat 0 13) = Ok rs ->
    sort_loop (Z.to_nat (hs_nbSymbols h)) 0 ws rs (repeat None 256) = Ok (rs2, syms) ->
    rw_cells usegs m5 DT [C4 (Z_to_bv 64 (mtl * 0x01000001 + tl * 65536))] ->
    u8arr usegs m5 (DT + 4) jdt -> zlen jdt = 4 * 2 ^ mtl ->
    u32arr usegs m5 W (map (Z_to_bv 64) rank) ->
    u8arr usegs m5 (W + 980) (omerge jsy syms) -> zlen jsy = 256 ->
    rw_cells usegs m5 (SP + -240) [C8 c1; C8 c2; CB 8 j8; C8 (Z_to_bv 64 (hs_ret h))] ->
    rw_cells usegs m5 (SP + -208) (x1_fr DT tl W (Z_to_bv 64 0) (Z_to_bv 64 (Znth 0 rank)) cw cc) ->
    rw_cells usegs m5 (SP + -112) [C4 (Z_to_bv 64 (hs_nbSymbols h))] ->
    rw_cells usegs m5 (SP + -108) [C4 (Z_to_bv 64 tl)] ->
    rw_cells usegs m5 (SP + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk usegs m5 lo (SP + -240) ->
    munch WALL m m5 -> wmono usegs m m5 -> mem_inv usegs m5 ->
    evt usegs POST (MS (mkR x1 (Z_to_bv 64 (SP + -240)) gp tp x5 x6 x7 x8 (Z_to_bv 64 (-9)) x10 (Z_to_bv 64 1) x12
                            (Z_to_bv 64 (W + 980)) x14 x15 (Z_to_bv 64 (2^64 - 1 - (W + 980))) x17 (Z_to_bv 64 (-17)) (Z_to_bv 64 (DT + 4))
                            (Z_to_bv 64 (-25)) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                       F (Z_to_bv 64 (PHUF_RDT_X1 + 1520)) fc None m5 (seg_rom usegs)).
  Proof using All.
    intros m5 h ws rank tl rs rs2 syms jdt jsy j8 c1 c2 cw cc x1 x5 x6 x7 x8 x10 x12 x14 x15 x17 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
      RS SOK RET1 SRCB MTL DT0 DTA DTL W0 WA WL LOS SPB SPA DJ RSC TLM RSL SOL RDT DTJ LJD RKA SYA LSY FRa FRm NSr TLr FRb ST MU WM MI.
    unfold hk in DJ.
    pose proof SOK as (TL1 & LWS & NBS & WSR & LRK1 & RKC & KS).
    unfold HufPure_HufStats.HUF_TABLELOG_MAX, HufPure_HufStats.HUF_SYMBOLVALUE_MAX in TL1, NBS, LRK1, RKC.
    unfold FseNCount.Zlength in LWS, LRK1.
    assert (P2 : 2 <= 2^mtl <= 4096) by (split; [change 2 with (2^1); apply Z.pow_le_mono_r; lia | change 4096 with (2^12); apply Z.pow_le_mono_r; lia]).
    assert (NCZ : Z.of_nat (Z.to_nat (2 ^ (mtl + 1))) = 2 * 2 ^ mtl)
      by (rewrite Z2Nat.id by (apply Z.pow_nonneg; lia); rewrite Z.pow_add_r by lia; change (2 ^ 1) with 2; lia).
    destruct (rescale_spec _ _ _ _ (Z.min (mtl + 1) 11) (WF_of_stats h SOK) ltac:(lia)) as (ws' & rank' & tl' & RSC' & WF' & TLM').
    rewrite RSC in RSC'. injection RSC' as <- <- <-.
    pose proof WF' as (TLW & LWS' & NBS' & WSR' & LRK' & RKC' & KS'). unfold FseNCount.Zlength in LWS', LRK'.
    unfold HufPure_HufStats.HUF_TABLELOG_MAX in TLW.
    pose proof (wf_rank_bounds _ _ _ _ WF') as RB.
    destruct (x1_model_path mtl src h ws rank tl MTL SRCB RS RSC TLM ltac:(lia)) as (rs' & rs2' & syms' & cells & RSL' & SOL' & FWL & TOK & LC & COV).
    rewrite RSL in RSL'. injection RSL' as <-. rewrite SOL in SOL'. injection SOL' as <- <-.
    assert (S0 : 0 <= Znth 0 rank <= 256) by (unfold FseNCount.Znth; apply sob_nth_bound; exact RB).
    assert (LSYm : length syms = 256%nat)
      by (pose proof (sob_sort_len _ _ _ _ _ _ SOL) as E; cbn [snd] in E; rewrite repeat_length in E; exact E).
    assert (HSYR : forall i v, nth i syms None = Some v -> 0 <= v < 256).
    { intros i v Hv. refine (sort_syms_range _ _ _ _ _ _ SOL _ _ _ i v Hv); [lia | lia |].
      intros j u Hu. rewrite nth_repeat in Hu. discriminate. }
    assert (INV0 : x1w_inv m5 m5 (bv_unsigned sp) DT (W + 980) jsy jdt syms (Z.to_nat (2 ^ (mtl + 1)))
                     (repeat None (Z.to_nat (2 ^ (mtl + 1))))).
    { unfold x1w_inv. rewrite ox1_none, repeat_length. split; [exact DTJ|]. split; [reflexivity|].
      split; [exact (proj1 SYA)|]. split; [apply munch_refl|]. split; [apply wmono_refl | exact MI]. }
    eapply (fw_loop sp gp tp F fc m5 W DT (W + 980) tl rank syms jsy jdt (Z.to_nat (2 ^ (mtl + 1))) POST)
      with (f := Z.to_nat tl) (cells := repeat None (Z.to_nat (2 ^ (mtl + 1)))) (u := 0) (sym := Znth 0 rank) (r := cells).
    all: try first [ exact FWL | exact FRm | assumption | lia ].
    intros m2 cu cs cw' cc' y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 INV2 FR2.
    destruct INV2 as (DTC2 & LC2 & SY2 & MU2 & WM2 & MI2).
    pose (Wi := [(DT + 4, DT + 4 + 2 * Z.of_nat (Z.to_nat (2 ^ (mtl + 1)))); (bv_unsigned sp + -208, bv_unsigned sp + -112)]).
    assert (MU3 : munch WALL m m2).
    { eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MU2].
      unfold sub_fp; intros x Hx; cbn [outside] in *. unfold HUF_RDT_STACK, DTABLE_BYTES, HufHarness.DT_BYTES in Hx.
      repeat split; lia. }
    pose proof (wmono_trans usegs _ _ _ WM WM2) as WM3.
    apply (rw_cells_transport usegs Wi m5 m2 _ _) in FRa;
      [| exact MU2 | exact WM2 | unfold Wi; cbn [disjoint_from cells_size csize Nat.add]; repeat split; lia].
    apply (rw_cells_transport usegs Wi m5 m2 _ _) in RDT;
      [| exact MU2 | exact WM2 | unfold Wi; cbn [disjoint_from cells_size csize Nat.add]; repeat split; lia].
    apply (rw_cells_transport usegs Wi m5 m2 _ _) in NSr;
      [| exact MU2 | exact WM2 | unfold Wi; cbn [disjoint_from cells_size csize Nat.add]; repeat split; lia].
    apply (rw_cells_transport usegs Wi m5 m2 _ _) in TLr;
      [| exact MU2 | exact WM2 | unfold Wi; cbn [disjoint_from cells_size csize Nat.add]; repeat split; lia].
    apply (rw_cells_transport usegs Wi m5 m2 _ _) in FRb;
      [| exact MU2 | exact WM2 | unfold Wi; cbn [disjoint_from cells_size csize Nat.add]; repeat split; lia].
    apply (stk_transport_disjoint usegs Wi m5 m2 lo (bv_unsigned sp + -240)) in ST;
      [| exact MU2 | exact WM2 | unfold Wi; cbn [disjoint_from]; repeat split; lia].
    eapply x1_fin.
    all: try first [ eassumption | reflexivity | lia ].
  Qed.
End TOP.
End CANSEC.
