From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_HufBits HufPure_HufX1.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit FseWalkMem FseRdKit FseRdKit2 HufWalkKit HufWalkKit2 HufWalkKit3.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RunDraw RF_huf_iface RF_huf_h_iface RF_huf_dec_iface RF_huf_fa_iface
  RF_huf_x4s RF_huf_x4s31_kit RF_huf_y4_kit_reload RF_huf_y4s31_kit RF_huf_x4s1.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.


Section CANSEC1. Context {rc : runConstT}.
Section X4S1C.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem).
  Variables (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX1) (cbs : list byte).
  Notation SP := (bv_unsigned sp).
  Notation n := (zlen src).
  Hypothesis TOK : x1_table_ok cells tl.
  Hypothesis ECB : cbs = firstn (Z.to_nat (2 * 2^tl)) (x1_bytes' cells).
  Hypothesis LCB : zlen cbs = 2 * 2^tl.
  Hypothesis MTL : 1 <= mtl <= 12.
  Hypothesis TLM : tl <= mtl + 1.
  Hypothesis D0 : 0 <= DST.
  Hypothesis DP : 0 < dcap -> 8 <= DST.
  Hypothesis DC : 0 <= dcap < 2^32.
  Hypothesis DL : DST + dcap <= lo.
  Hypothesis S0 : 16 <= SS.
  Hypothesis SL : SS + n <= lo.
  Hypothesis NSM : n < 2^26.
  Hypothesis BYS : Forall (fun c => 0 <= c < 256) src.
  Hypothesis DT0 : 0 < DT.
  Hypothesis CBL : DT + 4 + 2 * 2^tl <= lo.
  Hypothesis DJ1 : DT + 4 + 2 * 2^tl <= DST \/ DST + dcap <= DT.
  Hypothesis DJ3 : DST + dcap <= SS \/ SS + n <= DST.
  Hypothesis LOS : lo <= SP - 4096.
  Hypothesis SP16 : SP mod 16 = 0.
  Hypothesis SP47 : SP <= 2^47.
  Hypothesis DTA : DT mod 4 = 0.

  Notation POST := (huf_dec_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc DST dcap lo m0).
  Notation XB l := (l ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 DST dcap SS DT mtl tl lo src cells cbs
                      TOK ECB LCB MTL TLM D0 DP DC DL S0 SL NSM BYS DT0 CBL DJ1 DJ3 LOS SP16 SP47 DTA) (only parsing).
  Notation X4F' mm spl bd1 bd2 bd3 bd4 :=
    (X4F ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT lo src cbs mm spl bd1 bd2 bd3 bd4).

  Variables (L1 L2 L3 L4 SEG : Z).
  Notation O2 := (6 + L1). Notation O3 := (6 + L1 + L2). Notation O4 := (6 + L1 + L2 + L3).
  Hypothesis HL : 1 <= L1 /\ 1 <= L2 /\ 1 <= L3 /\ 1 <= L4 /\ 6 + L1 + L2 + L3 + L4 <= n.
  Hypothesis HQ : 0 < SEG /\ 3 * SEG <= dcap /\ 4 <= dcap.
  Hypothesis CHK : forall (L1 L2 L3 L4 SEG Q2 Q3 : Z),
    1 <= L1 /\ 1 <= L2 /\ 1 <= L3 /\ 1 <= L4 /\ 6 + L1 + L2 + L3 + L4 <= n ->
    0 < SEG <= Q2 /\ Q2 <= Q3 /\ Q3 <= dcap /\ 4 <= dcap ->
    forall q1 q2 q3 q4 pt1 pt2 pt3 pt4 c1 b1 c2 b2 c3 b3 c4 b4 v8 v16 v24 v32 v40 v48 v56 v128 mm j0 j96 j120
           jp1 jp2 jp3 jp4 (xra t0 t1 x8 x9 a0 a1 a2 a4 a5 a6 a7 x20 t3 t4 t5 t6 : word),
    X4F' mm (SPL3 v8 v16 v24 v32 v40 v48 v56 (DST + dcap) (DST + SEG) (DST + dcap - 3) (DST + Q2) dcap DST v128 j0 j96 j120)
            (BD4 c1 b1 (SS + 6 + pt1) (SS + 6) jp1) (BD4 c2 b2 (SS + (6 + L1) + pt2) (SS + (6 + L1)) jp2)
            (BD4 c3 b3 (SS + (6 + L1 + L2) + pt3) (SS + (6 + L1 + L2)) jp3)
            (BD4 c4 b4 (SS + (6 + L1 + L2 + L3) + pt4) (SS + (6 + L1 + L2 + L3)) jp4) ->
    0 <= q1 -> 0 <= q2 -> 0 <= q3 -> 0 <= q4 <= dcap ->
    DST + q1 < 2^64 -> DST + q2 < 2^64 -> DST + q3 < 2^64 ->
    0 <= pt1 -> (pt1 = 0 \/ pt1 + 8 <= L1) -> 0 <= pt2 -> (pt2 = 0 \/ pt2 + 8 <= L2) ->
    0 <= pt3 -> (pt3 = 0 \/ pt3 + 8 <= L3) -> 0 <= pt4 -> (pt4 = 0 \/ pt4 + 8 <= L4) ->
    0 <= b1 < 2^31 -> 0 <= b2 < 2^31 -> 0 <= b3 < 2^31 -> 0 <= b4 < 2^31 ->
    evt usegs POST (MS (mkR xra (Z_to_bv 64 (SP + -512)) gp tp t0 t1 (Z_to_bv 64 DST) x8 x9 a0 a1 a2 (Z_to_bv 64 (DST + SEG))
                           a4 a5 a6 a7 (Z_to_bv 64 (DST + q1)) (Z_to_bv 64 (tl + 256 * mtl)) x20 (Z_to_bv 64 (DST + q4))
                           (Z_to_bv 64 (DST + q3)) (Z_to_bv 64 (DST + q2)) (Z_to_bv 64 (DST + Q3)) (Z_to_bv 64 (DT + 4))
                           (Z_to_bv 64 SEG) (Z_to_bv 64 (DST + dcap)) t3 t4 t5 t6)
                       F (Z_to_bv 64 0x18cfc) fc None mm (seg_rom usegs)).

  Notation SPL1 st1 c1 v128 j0 :=
    [CB 8 j0; C8 (Z_to_bv 64 (DST + 3 * SEG)); C8 (Z_to_bv 64 (tl + 256 * mtl)); C8 (Z_to_bv 64 (SS + O4 + 8));
     C8 (Z_to_bv 64 (SS + O3 + 8)); C8 (Z_to_bv 64 (SS + O2 + 8)); C8 (Z_to_bv 64 (3 * SEG)); C8 (Z_to_bv 64 (2 * SEG));
     C8 (Z_to_bv 64 (DST + dcap)); C8 (Z_to_bv 64 (DST + SEG)); C8 (Z_to_bv 64 (DST + dcap - 3)); C8 (Z_to_bv 64 (DST + 2 * SEG));
     C8 (Z_to_bv 64 st1); C8 (Z_to_bv 64 dcap); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 c1); C8 (Z_to_bv 64 v128)].
  Notation LOOPK' q := (LOOPK ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 DST dcap SS DT mtl tl lo src cbs L1 L2 L3 L4 SEG q).
  Notation X4BK' q := (X4BK ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 DST dcap SS DT mtl tl lo src cbs L1 L2 L3 L4 SEG q).
  Notation X4R4' q := (X4R4 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 DST dcap SS DT mtl tl lo src cbs L1 L2 L3 L4 SEG q).
  Notation X4N3' q := (X4N3 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 DST dcap SS DT mtl tl lo src cbs L1 L2 L3 L4 SEG q).
  Notation X4R3' q := (X4R3 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 DST dcap SS DT mtl tl lo src cbs L1 L2 L3 L4 SEG q).

  Ltac x4c_open H :=
    destruct H as ((buf & OUT & LB) & SRC & CBS & STK & SPC & L0 & BDa & LBa & (jj & JJ) & BDd & LDd & BDc & LDc & BDb & LDb & FR & MI & MU & WM);
    unfold BD4 in BDa, BDb, BDc, BDd;
    pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn in RSP.
  Ltac x4c_zw stops := repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
    lazymatch eval vm_compute in (existsb (Z.eqb pc) stops) with true => fail | false => zstep end end).
  Ltac x4c_br B := if_cases B; zify_cond B; hnorm B.

  Lemma x4c_recast : forall mm st1 c1 v128 j0 bd1 bd2 bd3 bd4,
    X4F' mm (SPL1 st1 c1 v128 j0) bd1 bd2 bd3 bd4 ->
    X4F' mm (SPL3 (DST + 3 * SEG) (tl + 256 * mtl) (SS + O4 + 8) (SS + O3 + 8) (SS + O2 + 8) (3 * SEG) (2 * SEG)
                  (DST + dcap) (DST + SEG) (DST + dcap - 3) (DST + 2 * SEG) dcap DST v128 j0
                  (le8 (Z_to_bv 64 st1)) (le8 (Z_to_bv 64 c1))) bd1 bd2 bd3 bd4.
  Proof using All.
    intros mm st1 c1 v128 j0 bd1 bd2 bd3 bd4 XF. unfold X4F in *.
    destruct XF as (A & B & C & D & E & F1 & R).
    lazymatch type of E with rw_cells _ _ _ ?l =>
      let pre := eval cbv [firstn] in (firstn 12 l) in let post := eval cbv [skipn] in (skipn 13 l) in
      apply (rw_cells_forget8 usegs mm _ pre (Z_to_bv 64 st1) post) in E; cbn [app] in E end.
    lazymatch type of E with rw_cells _ _ _ ?l =>
      let pre := eval cbv [firstn] in (firstn 15 l) in let post := eval cbv [skipn] in (skipn 16 l) in
      apply (rw_cells_forget8 usegs mm _ pre (Z_to_bv 64 c1) post) in E; cbn [app] in E end.
    unfold SPL3.
    refine (conj A (conj B (conj C (conj D (conj E (conj _ R)))))).
    exact F1.
  Qed.

  Ltac x4c_chk q XR HL HQ :=
    replace (DST + q + 4 + 3 * SEG) with (DST + (q + 4 + 3 * SEG)) by lia;
    replace (DST + q + 4 + 2 * SEG) with (DST + (q + 4 + 2 * SEG)) by lia;
    replace (DST + q + 4 + SEG) with (DST + (q + 4 + SEG)) by lia;
    replace (DST + q + 4) with (DST + (q + 4)) by lia;
    eapply (CHK L1 L2 L3 L4 SEG (2 * SEG) (3 * SEG));
    [ exact HL | lia | exact XR | .. ];
    first [ eassumption | lia ].

  Lemma x4s1_back : forall q, LOOPK' q -> X4BK' q.
  Proof using All.
    intros q LK. unfold X4BK.
    intros p1 p2 p3 p4 b1 b2 b3 b4 c1 c2 c3 c4 st1 st2 st3 st4 mm j0 jp1 jp2 jp3 jp4 t2 x8 a0 a2 x20 x27
      XF Q0 QD A1 A2 A3 A4 C1 C2 C3 C4.
    pose proof (x4c_recast _ _ _ _ _ _ _ _ _ XF) as XR.
    pose proof A1 as (F1a & F1b & F1c & _). pose proof A2 as (F2a & F2b & F2c & _).
    pose proof A3 as (F3a & F3b & F3c & _). pose proof A4 as (F4a & F4b & F4c & _).
    pose proof HL as HL'. pose proof HQ as HQ'.
    x4c_open XF.
    x4c_zw [101628; 96976]. x4c_br B1.
    - x4c_zw [101628; 96976]. x4c_chk q XR HL HQ.
    - x4c_zw [101628; 96976]. x4c_br B2.
      + pose proof A1 as (_ & _ & _ & F1d). pose proof A2 as (_ & _ & _ & F2d).
        pose proof A3 as (_ & _ & _ & F3d). pose proof A4 as (_ & _ & _ & F4d).
        apply Z.lor_eq_0_iff in B2. destruct B2 as [B21 B22].
        apply Z.lor_eq_0_iff in B21. destruct B21 as [E2 E1].
        apply Z.lor_eq_0_iff in B22. destruct B22 as [E3 E4].
        try rewrite Z.mod_small in E1 by (destruct F1d as [[-> _] | ->]; lia).
        try rewrite Z.mod_small in E2 by (destruct F2d as [[-> _] | ->]; lia).
        try rewrite Z.mod_small in E3 by (destruct F3d as [[-> _] | ->]; lia).
        try rewrite Z.mod_small in E4 by (destruct F4d as [[-> _] | ->]; lia).
        subst st1 st2 st3 st4. clear F1d F2d F3d F4d.
        x4c_zw [101628; 96976].
        replace (DST + q + 4) with (DST + (q + 4)) by lia.
        eapply LK; first [ exact XR | (apply aft_hdi; assumption) | lia ].
      + x4c_zw [101628; 96976]. x4c_chk q XR HL HQ.
  Qed.

  Ltac r4n :=
    rewrite ?u_srl3 in * by lia;
    repeat match goal with
    | H : context [?x mod 18446744073709551616] |- _ =>
        lazymatch x with _ mod _ => fail | _ => rewrite (Z.mod_small x) in H by lia end
    | |- context [?x mod 18446744073709551616] =>
        lazymatch x with _ mod _ => fail | _ => rewrite (Z.mod_small x) by lia end
    end.
  Ltac srd8 SRC :=
    lazymatch type of SRC with bytes_at usegs ?mm ?S ?bs =>
      let E := u_mem_addr in
      let R := fresh "R8" in
      pose proof (bytes_at_read usegs mm S bs (E - S) 8 SRC ltac:(lia) ltac:(rewrite ?length_map; unfold zlen in *; lia)) as R;
      replace (S + (E - S)) with E in R by lia end.
  Ltac r4pack H := ubdnorm H; unfold X4F, BD4; upack.
  Ltac r4close BK BD A1 A2 A3 :=
    try (replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 (2^64 - 1)) by (apply bv_eq; vm_compute; reflexivity));
    lazymatch goal with H : context [SS + O4 + ?p - ?b / 8] |- _ =>
      replace (SS + O4 + p - b / 8) with (SS + O4 + (p - b / 8)) in * by lia end;
    lazymatch type of BD with rw_cells _ _ _ (C8 (Z_to_bv 64 ?cw) :: _) =>
      rewrite <- (Z_to_bv_bv_unsigned (Z_to_bv 64 cw)) in BD |- *;
      let CWR := fresh "CWR" in
      pose proof (bv_unsigned_in_range 64 (Z_to_bv 64 cw)) as CWR; unfold bv_modulus in CWR; cbn in CWR;
      unfold X4BK in BK; eapply BK with (st4 := 0);
      [ r4pack BD | lia | lia | exact A1 | exact A2 | exact A3 | unfold AFT; lia | lia | lia | lia | lia ] end.
  Ltac r4open H :=
    destruct H as ((buf & OUT & LB) & SRC & CBS & STK & SPC & L0 & BDa & LBa & (jj & JJ) & BDd & LDd & BDc & LDc & BDb & LDb & FR & MI & MU & WM);
    change (zlen buf) with (Z.of_nat (length buf)) in LB;
    pose proof TOK as (TL1 & TLN & TCK); cbv [HUF_TABLELOG_MAX] in TL1; cbv [FseNCount.Zlength] in TLN;
    pose proof (DP ltac:(lia)) as D8; pose proof (length_map (Z_to_bv 8) src) as LMS; unfold BD4 in *;
    pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn in RSP.

  Lemma x4s1_r4 : forall q, X4BK' q -> X4R4' q.
  Proof using All.
    intros q BK. unfold X4R4.
    intros p1 p2 p3 p4 b1 b2 b3 b4 c1 c2 c3 c4 st1 st2 st3 mm j0 jp1 jp2 jp3 jp4 t2 x8 x9 a0 a2 a7 x27 t3
      XF Q0 QD A1 A2 A3 B4 P48 C1 C2 C3 C4.
    pose proof HL as HL'. pose proof HQ as HQ'.
    r4open XF.
    clear DP.
    pose proof B4 as B4r; unfold BEF in B4r; destruct B4r as (P4a & _ & B4b & _).
    assert (P4b : p4 <= L4) by (unfold BEF in B4; lia).
    assert (P4c : p4 + 8 <= L4) by (unfold BEF in B4; lia).
    assert (B4c : b4 <= 56) by (unfold BEF in B4; lia).
    pose proof A1 as A1r; unfold AFT in A1r; destruct A1r as (P1a & _ & B1b & _).
    pose proof A2 as A2r; unfold AFT in A2r; destruct A2r as (P2a & _ & B2b & _).
    pose proof A3 as A3r; unfold AFT in A3r; destruct A3r as (P3a & _ & B3b & _).
    xwalk [98808] tl DT cells cbs ECB TCK OUT LB SRC.
    all: r4n.
    all: try solve [exfalso; lia].
    all: try (srd8 SRC; zstep).
    all: xwalk [98808] tl DT cells cbs ECB TCK OUT LB SRC.
    all: try (r4n; solve [exfalso; lia]).
    all: r4close BK BDd A1 A2 A3.
  Qed.





  Lemma x4s1_n3k : forall q, LOOPK' q -> X4N3' q.
  Proof using All.
    intros q LK. pose proof (x4s1_back q LK) as BK. pose proof (x4s1_r4 q BK) as R4.
    eapply x4s1_n3; eassumption.
  Qed.

  Lemma x4s1_r3k : forall q, LOOPK' q -> X4R3' q.
  Proof using All.
    intros q LK. pose proof (x4s1_back q LK) as BK. pose proof (x4s1_r4 q BK) as R4.
    eapply x4s1_r3; eassumption.
  Qed.
End X4S1C.
End CANSEC1.
