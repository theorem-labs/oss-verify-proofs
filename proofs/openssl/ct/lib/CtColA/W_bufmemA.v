(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem RzCPS. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Monad Stdio Prog LibProg ProgG CtSizes CtWire CtModel ApBase ApState ApLogic ApInv ApErr ApParse ApBridge.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnAsan Require Import AsKit AsLoop.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface RT_client_kit D_defs D_cs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import R_unwind_chain.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import RT_iface2 LibKitA ARun BnHeapA BnRepDefs BnRepA ImplA ImplAX BnIfaceA AsStruct RtCallA W_cryptoA UnwindA EdgesA UnwindX.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtFrameA Require Import AFrameKit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells ApErrKit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApATac ApATacX ApBImg ApWalkTac ApRepDefs ApRep ApIface ApFrame W_akit ApErrKitA2 W_get_objectA W_check_tlenA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctA Require Import SctRepA O2iKitA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtColP Require ColDefs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtColA Require Import ColDefsA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeA Require Import BTacX.                (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac step := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.
Local Ltac zstep := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
Local Ltac alia := unfold BnHeapA.ACEIL, SEGTOP_A, SHHI, SHLO, STACK_WIN, USTACK_TOP in *; lia.
Import ListNotations.
Open Scope Z_scope.

Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 (zxb ?b) => constr:(C1 b)
  | Z_to_le_bytes 8 ?z => constr:(C8 (Z_to_bv 64 z))
  | Z_to_le_bytes 4 ?z => constr:(C4 (Z_to_bv 64 z))
  end.
Ltac zc H := rewrite ?bv_lts_zero_r, ?bv_lts_zero_l in H; unfold bv_eqb, bv_ltu, bv_lts, bv_leu in H; fold_lit_ux_in H; try zsimp_in H; zify_bool H.
Local Definition hidden (P : Prop) : Prop := P.
Local Ltac hide H := lazymatch type of H with ?T => change T with (hidden T) in H end.
Local Ltac unhide H := unfold hidden in H.
Local Ltac freeze H := lazymatch type of H with ?T => change T with (frozen T) in H end.
Local Ltac thaw H := unfold frozen in H.
(* [comment removed for export] *)
Local Ltac xportby H MU WM tac :=
  eapply rw_cells_transport in H; [| exact MU| exact WM| cbn [cells_size csize Nat.add disjoint_from fst snd]; tac].

(* [comment removed for export] *)
Local Notation E_grow_crea := (E_BUF_MEM_grow_clean_24eab8 : uk_call 0x24b32c 0x24b4c0 0x1fd378).     (* [comment removed for export] *)
Local Notation E_crea_tail := (E_CRYPTO_clear_realloc_1fc7a0 : uk_tail 0x1fd378 0x1fce24).            (* [comment removed for export] *)
Local Notation E_crea_malloc := (E_CRYPTO_clear_realloc_1fc7c8 : uk_call 0x1fd378 0x1fd420 0x1fce24). (* [comment removed for export] *)
Local Notation E_crea_cfree := (E_CRYPTO_clear_realloc_1fc7f0 : uk_call 0x1fd378 0x1fd448 0x1fd47c).  (* [comment removed for export] *)

(* [comment removed for export] *)
Definition grow_costA (b : bufm bptr) (len : Z) : Z := if len <=? bm_max b then 0 else mcost ((len + 3) / 3 * 4).
(* [comment removed for export] *)
Definition grow_capA (b : bufm bptr) (len : Z) : Z := if len <=? bm_max b then bm_max b else (len + 3) / 3 * 4.

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

Section Act.
  (* [comment removed for export] *)
  Variables (sp : word) (m : mem) (Σ : rts RT) (LB : list block) (E : ap_env) (lo : Z) (K : list block).
  Variables (c : list Z) (D : Z) (XP : list (Z * Z)) (OFS STK CST FRM : Z).
  Hypothesis KH : kit_hyps sp LB lo c D XP OFS STK.

  Local Notation oinvK := (oinv sp m Σ LB E lo K c D XP OFS STK CST FRM).
  Local Ltac kit L := eapply (L AR sp m Σ LB E lo K c D XP OFS STK CST FRM KH).
  Local Ltac kitp L H := pose proof (L AR sp m Σ LB E lo K c D XP OFS STK CST FRM KH) as H.
  Local Ltac kh := pose proof KH as (DF & CEIL & LO0 & LO & STK0 & OFS0 & TOP & SP16 & OFS16 & XPok & XPD & PBX & D0).

  (* [comment removed for export] *)
  Definition grow_postA (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
      (stX : ap_st bptr) (OWX : list block) (boX : Z * Z) (mX : mem) (NEW1 : list block) (b : bufm bptr) (len BUF : Z) (bytes : list (bv 8)) (CX : Z)
      (r : bufm bptr * ap_st bptr) (ΣY : rts RT) : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (FY : bvmap 5 word) (fcY : bv 32) mY OWY (q : bptr) (A n : Z) (rest : list (bv 8)),
      ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + OFS)) gp (wz TP_A) t0 t1 t2 s0 s1 (wz len) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               FY (ret_pc ra) fcY None mY (seg_rom ctasegs)
      /\ snd r = stX /\ fst r = mkBuf len (Some (q, n)) (bm_bytes b)
      /\ oinvK ΣY stX mY OWY boX ((q, A, n) :: NEW1) (CX - grow_costA b len)
      /\ (forall bb, In bb OWX -> In bb OWY)
      /\ rw_cells ctasegs mY BUF [C8 (wz len); C8 (wz A); C8 (wz n); C8 (wz 0)]
      /\ rw_cells ctasegs mY A [CB (Z.to_nat (bm_len b)) (firstn (Z.to_nat (bm_len b)) bytes); CB (Z.to_nat (n - bm_len b)) rest]
      /\ len <= n /\ 4 <= n < 2 ^ 31 /\ 0 < A /\ A mod 16 = 0 /\ A + n <= ACEIL /\ n = grow_capA b len
      /\ ax_pres (NEW1 ++ LB) (bv_unsigned sp + OFS) ([(BUF, BUF + 32)] ++ LIBW_A) mX mY.
  (* [comment removed for export] *)

  Lemma BUF_MEM_grow_clean_walkA : forall
      (ra gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (FX : bvmap 5 word) (fcX : bv 32)
      ΣX stX mX OWX boX NEW1 (b : bufm bptr) (len BUF A0 : Z) (bytes : list (bv 8)) (CX : Z) (ras : list Z),
    GROW_STACK_A <= STK ->
    oinvK ΣX stX mX OWX boX (buf_blk b A0 ++ NEW1) CX ->
    In (BUF, BUF + 32) XP -> BUF mod 8 = 0 ->
    rw_cells ctasegs mX BUF (buf_cells b A0) ->
    0 <= bm_len b <= bm_max b -> bm_len b < len -> len <= 2 ^ 30 ->
    match bm_data b with None => A0 = 0 | Some (q, n) => 4 <= n < 2 ^ 31 /\ rw_cells ctasegs mX A0 [CB (Z.to_nat n) bytes] end ->
    grow_costA b len <= CX ->
    uw_chain USTACK_TOP mX (bv_unsigned sp + OFS) (bv_unsigned s0) ras -> uk_ctx BUF_GROW_CLEAN_A (bv_unsigned ra :: ras) ->
    implAp (buf_grow_clean b len stX) ΣX
           (grow_postA ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 stX OWX boX mX NEW1 b len BUF bytes CX)
           (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + OFS)) gp (wz TP_A) t0 t1 t2 s0 s1 (wz BUF) (wz len) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               FX (wz BUF_GROW_CLEAN_A) fcX None mX (seg_rom ctasegs)).
  Proof.
    intros until ras. intros STKG OI XBUF AL8 HBUF LENB LTL LEN30 HDATA CRG UW CTX. kh.
    pose proof (SPR sp LB lo c D XP OFS STK KH) as SPR. pose proof (ESP sp LB lo c D XP OFS STK KH) as ESP.
    unfold GROW_STACK_A, CRYPTO_CLEAR_FREE_STACK, OPENSSL_CLEANSE_STACK, RT_STACK in STKG.
    kitp @oinv_facts OFc. pose proof (OFc _ _ _ _ _ _ _ OI) as (HEAPX & NDX & BND & FRESH & DJL & DJO). clear OFc.
    kitp @oinv_call OCc. pose proof (OCc _ _ _ _ _ _ _ OI) as (_ & STX & _ & _ & TOPX & AL16X & MIX & CSX & ASX & CRX & _). clear OCc.
    pose proof (AH_ceil _ _ _ _ HEAPX) as (C1 & C2 & C3).
    pose proof C1 as CN1. pose proof C2 as CN2. pose proof C3 as CN3. unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in CN1, CN2, CN3.
    (* [comment removed for export] *)
    pose proof (proj1 (Forall_forall _ _) XPok _ XBUF) as (bB & HbB & BB1 & BB2). cbn [fst snd] in BB1, BB2.
    assert (HbB3 : In bB (OWX ++ (buf_blk b A0 ++ NEW1) ++ LB)) by (apply in_app_iff; right; apply in_app_iff; right; exact HbB).
    pose proof (BND bB HbB3) as (BB3 & BB4 & BB5 & BB6).
    assert (HbB2 : In bB (OWX ++ (buf_blk b A0 ++ NEW1) ++ LB)) by exact HbB3.
    ablock HEAPX HbB2 ACCB OFFB. clear HbB2.
    assert (EBUF : bv_unsigned (Z_to_bv 64 BUF) = BUF) by (apply unsigned_lit; clear - BB1 BB2 BB3 BB5 CEIL LO STK0 OFS0 SPR; alia).
    unfold BUF_GROW_CLEAN_A, MallocRep.wz in *. rewrite ?ESP in STX, TOPX, AL16X.
    destruct b as [L0 [[q0 n0]|] bys]; unfold CtColP.ColDefs.buf_blk, CtColP.ColDefs.buf_cells, bm_max, grow_costA in *; cbn [bm_len bm_data bm_bytes app] in *;
      unfold buf_grow_clean, bm_max; cbn [bm_len bm_data bm_bytes];
      replace (len <=? L0) with false by (symmetry; apply Z.leb_gt; lia);
      cut_hd HBUF HLEN (BUF + 8); cut_hd HBUF HDAT (BUF + 16); cut_hd HBUF HMAX (BUF + 24); rename HBUF into HFLG; unfold MallocRep.wz in *.
    + (* [comment removed for export] *)
      destruct HDATA as [N4 HBLK].
      pose proof (BND (q0, A0, n0) ltac:(apply in_app_iff; right; left; reflexivity)) as (BA0 & _ & BAC & BAI). cbn [blk_addr blk_size fst snd] in BA0, BAC, BAI.
      pose proof (munch_refl [(bv_unsigned sp + OFS - 144, bv_unsigned sp + OFS)]%Z mX) as MU. pose proof (wmono_refl ctasegs mX) as WM.
      assert (OFFW : offshW [(bv_unsigned sp + OFS - 144, bv_unsigned sp + OFS)]%Z) by (cbn [offshW]; clear - CEIL LO STK0 STKG C2; alia).
      apply implAp_from_evt.
      (* [comment removed for export] *)
      carve_frame 80%nat STX. do 11 step.
      step. step. step.
      step. if_cases K0; zc K0; [exfalso; revert K0; rewrite ?unsigned_lit by lia; lia|]. clear K0.
      step.
      step. if_cases KR; zc KR.
      * (* [comment removed for export] *)
        replace (len <=? n0) with true by (symmetry; apply Z.leb_le; lia).
        step. step. setreg 10%Z (Z_to_bv 64 (A0 + L0)) ltac:(f_equal; clear; lia). step. setreg 12%Z (Z_to_bv 64 (len - L0)) ltac:(rewrite (unsigned_lit L0) by lia; f_equal; lia).
        (* [comment removed for export] *)
        pose proof (cb_len_a _ _ _ _ HBLK) as BL.
        step. name_mem m1.   (* [comment removed for export] *)
        match goal with H : stk ctasegs m1 lo _ |- _ => rename H into ST1 end. match goal with H : mem_inv ctasegs m1 |- _ => rename H into MI1 end.
        assert (E80 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + OFS + -80)) = bv_unsigned sp + OFS + -80) by (apply unsigned_lit; clear - SPR LO LO0 STK0 STKG OFS0; lia).
        assert (HEAP1 : AHEAP ΣX OWX (((q0, A0, n0) :: NEW1) ++ LB) m1).
        { eapply AH_frame; [exact HEAPX| exact MU| exact WM|]. constructor; [left; cbn [fst snd]; clear - CEIL LO STK0 STKG OFS0 TOP; alia| constructor]. }
        pose proof (DJL (q0, A0, n0) bB ltac:(left; reflexivity) HbB) as DJB. cbn [blk_addr blk_size fst snd] in DJB.
        assert (ALEN : A0 + len <= lo /\ lo + 144 <= bv_unsigned sp + OFS - 80) by (clear - BAC CEIL KR LO STKG; lia).
        assert (OI1 : oinvK ΣX stX m1 OWX boX ((q0, A0, n0) :: NEW1) CX).
        { kit @oinv_munch; [exact OI| exact MU| exact WM| exact MI1| | constructor; [left; cbn [fst snd]; clear - ALEN LO STK0 OFS0; lia| constructor]].
          stk_join ST1 FR STF (bv_unsigned sp + OFS). exact STF. }
        apply evt_done. eapply implAp_step_same.
        { eapply (asan_memset_cpsA) with (d := A0 + L0) (n := len - L0) (c := z8) (bd := (q0, A0, n0)) (lo := lo) (OW := OWX) (LB := ((q0, A0, n0) :: NEW1) ++ LB);
            try reflexivity; rewrite ?E80.
          - exact HEAP1.
          - exact ST1.
          - exact CEIL.
          - unfold RT_STACK; clear - LO STKG; lia.
          - clear - TOP OFS0; unfold USTACK_TOP in *; lia.
          - uchk_open; clear - SP16 OFS16; Z.div_mod_to_equations; lia.
          - exact MI1.
          - apply in_app_iff; right; left; reflexivity.
          - cbn [blk_addr blk_size fst snd]. clear - LENB; lia.
          - cbn [blk_addr blk_size fst snd]. clear - KR LTL; rewrite ?unsigned_lit in KR by lia; lia.
          - clear - LENB LTL LEN30; lia. }
        intros msM PO. unfold icall_post in PO. rewrite ?E80 in PO.
        destruct PO as (w0 & w1 & w2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & w3 & w4 & w5 & w6 & F4 & fc4 & m4 & -> & MI4 & ST4 & HEAP4 & WM4 & AG4 & BZ & WR4).
        rewrite (ret_pc_even 0x24b440) by (clear; lia).
        (* [comment removed for export] *)
        apply (rw_cells_agree _ _ _ _ _ AG4) in FR; [| intros xa Hxa; cbn in Hxa; split; [left; clear - Hxa TOP OFS0; unfold USTACK_TOP in *; lia| clear - Hxa ALEN; lia]].
        apply (rw_cells_agree _ _ _ _ _ AG4) in HLEN; [| intros xa Hxa; cbn in Hxa; split; [right; right; exists bB; split; [apply in_app_iff; right; apply in_app_iff; right; exact HbB| clear - Hxa BB1 BB2; lia]| clear - Hxa BB1 BB2 DJB LENB KR; lia]].
        apply (rw_cells_agree _ _ _ _ _ AG4) in HDAT; [| intros xa Hxa; cbn in Hxa; split; [right; right; exists bB; split; [apply in_app_iff; right; apply in_app_iff; right; exact HbB| clear - Hxa BB1 BB2; lia]| clear - Hxa BB1 BB2 DJB LENB KR; lia]].
        apply (rw_cells_agree _ _ _ _ _ AG4) in HMAX; [| intros xa Hxa; cbn in Hxa; split; [right; right; exists bB; split; [apply in_app_iff; right; apply in_app_iff; right; exact HbB| clear - Hxa BB1 BB2; lia]| clear - Hxa BB1 BB2 DJB LENB KR; lia]].
        apply (rw_cells_agree _ _ _ _ _ AG4) in HFLG; [| intros xa Hxa; cbn in Hxa; split; [right; right; exists bB; split; [apply in_app_iff; right; apply in_app_iff; right; exact HbB| clear - Hxa BB1 BB2; lia]| clear - Hxa BB1 BB2 DJB LENB KR; lia]].
        assert (OI4 : oinvK ΣX stX m4 OWX boX ((q0, A0, n0) :: NEW1) (CX - 0)).
        { kit @oinv_heap; [exact OI1| | intros b' [Hb'|Hb']; apply in_app_iff; [left; exact Hb'| right; exact Hb']| exact HEAP4| pose proof OI1 as (_ & _ & _ & _ & _ & _ & _ & LBOK1); exact LBOK1| exact MI4| | clear; lia| clear - CRX; lia].
          - eapply agree_on_mono; [exact AG4|]. intros a [Ha HXa]. split.
            + destruct Ha as [Ha|[Ha|(b' & Hb' & Hr')]]; [left; clear - Ha; lia| right; left; exact Ha| right; right; exists b'; split; [| exact Hr']].
              apply in_app_iff in Hb'. apply in_app_iff. destruct Hb' as [Hb'|Hb']; [left; exact Hb'| right; apply in_app_iff; right; exact Hb'].
            + destruct Ha as [Ha|[Ha|(b' & Hb' & Hr')]]; [clear - Ha ALEN LO STK0; lia| intros Hx; exact (ApErrKitA2.blk_not_static _ _ _ _ (q0, A0, n0) a HEAP1 ltac:(apply in_app_iff; right; left; reflexivity) ltac:(cbn; clear - Hx LENB KR; lia) Ha)|].
              apply in_app_iff in Hb'. destruct Hb' as [Hb'|Hb'].
              ++ pose proof (DJO (q0, A0, n0) b' ltac:(left; reflexivity) Hb') as DJ. cbn [blk_addr blk_size fst snd] in DJ. clear - DJ Hr' LENB KR LTL. lia.
              ++ pose proof (DJL (q0, A0, n0) b' ltac:(left; reflexivity) Hb') as DJ. cbn [blk_addr blk_size fst snd] in DJ. clear - DJ Hr' LENB KR LTL. lia.
          - stk_join ST4 FR STF (bv_unsigned sp + OFS). exact STF. }
        (* [comment removed for export] *)
        replace (Z.to_nat n0) with (Z.to_nat L0 + Z.to_nat (n0 - L0))%nat in HBLK by (clear - LENB KR LTL; lia).
        apply cb_split_a in HBLK. cut_hd HBLK HB1 (A0 + L0).
        replace (Z.to_nat (n0 - L0)) with (Z.to_nat (len - L0) + Z.to_nat (n0 - len))%nat in HBLK by (clear - LENB KR LTL; rewrite ?unsigned_lit in KR by lia; lia).
        apply cb_split_a in HBLK. cut_hd HBLK HB2 (A0 + len). rename HBLK into HB3.
        clear HB2.
        apply (rw_cells_agree _ _ _ _ _ AG4) in HB1; [| intros xa Hxa; cbn in Hxa; split; [right; right; exists (q0, A0, n0); split; [apply in_app_iff; right; left; reflexivity| cbn; clear - Hxa BL LENB; lia]| clear - Hxa BL LENB; lia]].
        apply (rw_cells_agree _ _ _ _ _ AG4) in HB3; [| intros xa Hxa; cbn in Hxa; split; [right; right; exists (q0, A0, n0); split; [apply in_app_iff; right; left; reflexivity| cbn; clear - Hxa BL LENB KR LTL; rewrite ?unsigned_lit in KR by lia; lia]| clear - Hxa BL LENB KR LTL; rewrite ?unsigned_lit in KR by lia; lia]].
        assert (HZ : rw_cells ctasegs m4 (A0 + L0) [CB (Z.to_nat (len - L0)) (repeat z8 (Z.to_nat (len - L0)))]).
        { pose proof (rw_cells_of_bytes_a m4 (A0 + L0) _ BZ) as HZ0. rewrite repeat_length in HZ0. apply HZ0. rewrite Z2Nat.id by (clear - LTL; lia). exact WR4. }
        ablock HEAP4 HbB3 ACC4 OFF4.
        pose proof (munch_refl [(bv_unsigned sp + OFS - 80, bv_unsigned sp + OFS); (BUF, BUF + 32)]%Z m4) as MU4. pose proof (wmono_refl ctasegs m4) as WM4'.
        assert (OFFW4 : offshW [(bv_unsigned sp + OFS - 80, bv_unsigned sp + OFS); (BUF, BUF + 32)]%Z) by (cbn [offshW]; clear - CEIL LO STK0 STKG C2 OFFB BB1 BB2; alia).
        rename MU into MU0. rename WM into WM0. clear OFFW.
        apply implAp_from_evt.
        (* [comment removed for export] *)
        step. step. do 9 step. release_frame FR ST4 (bv_unsigned sp + OFS). step. step.
        name_mem m9.
        match goal with H : stk ctasegs m9 lo _ |- _ => rename H into ST9 end. match goal with H : mem_inv ctasegs m9 |- _ => rename H into MI9 end.
        match goal with H : munch _ m4 m9 |- _ => rename H into MU9 end. match goal with H : wmono ctasegs m4 m9 |- _ => rename H into WM9 end.
        apply evt_done. cbn [aret]. apply implAp_ret.
        (* [comment removed for export] *)
        join2 HZ HB3. apply cb_join_a in HZ. replace (Z.to_nat (len - L0) + Z.to_nat (n0 - len))%nat with (Z.to_nat (n0 - L0)) in HZ by (clear - LENB KR LTL; lia). join2 HB1 HZ.
        join2 HLEN HDAT. join2 HLEN HMAX. join2 HLEN HFLG.
        unfold grow_postA. cbn [fst snd]. unfold grow_costA, grow_capA, bm_max; cbn [bm_len bm_data bm_bytes]. replace (len <=? n0) with true by (symmetry; apply Z.leb_le; exact KR).
        eexists w0, w1, w2, _, _, _, _, _, _, _, w3, w4, w5, w6, F4, fc4, m9, OWX, q0, A0, n0, _.
        split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
        split. { kit @oinv_munch; [exact OI4| exact MU9| exact WM9| exact MI9| exact ST9|].
                 constructor; [left; cbn [fst snd]; clear - ALEN LO STK0 OFS0; lia|]. constructor; [right; left; exists (BUF, BUF + 32); split; [exact XBUF| cbn; clear; lia]| constructor]. }
        split; [intros bb Hbb; exact Hbb|].
        split; [exact HLEN|]. split; [exact HB1|].
        pose proof OI as (_ & _ & _ & _ & _ & _ & _ & LBOK). apply Forall_cons_iff in LBOK as [[[A16 _] _] _]. cbn [blk_addr] in A16.
        split; [exact KR|]. split; [exact N4|]. split; [exact BA0|]. split; [exact A16|]. split; [exact BAC|]. split; [reflexivity|].
        (* [comment removed for export] *)
        eapply agree_on_trans; [| eapply agree_on_trans].
        -- eapply agree_on_mono; [exact (agree_on_of_munch_nw _ _ _ MU0)|]. intros a [HX Ha]. cbn [outside fst snd]. split; [| exact I].
           destruct Ha as [Ha|[Ha|(b' & Hb' & Hr')]]; [clear - Ha; lia| pose proof (client_static_below a Ha) as Hlow; clear - Hlow CN1 CEIL ALEN; lia|].
           pose proof (BND b' ltac:(apply in_app_iff; right; right; exact Hb')) as (_ & _ & Hc' & _). clear - Hr' Hc' ALEN CEIL LO STK0; lia.
        -- eapply agree_on_mono; [exact AG4|]. intros a [HX Ha]. split.
           ++ destruct Ha as [Ha|[Ha|(b' & Hb' & Hr')]]; [left; clear - Ha; lia| right; left; exact Ha| right; right; exists b'; split; [apply in_app_iff; right; right; exact Hb'| exact Hr']].
           ++ destruct Ha as [Ha|[Ha|(b' & Hb' & Hr')]]; [clear - Ha ALEN LO STK0; lia| intros Hx; exact (ApErrKitA2.blk_not_static _ _ _ _ (q0, A0, n0) a HEAP1 ltac:(apply in_app_iff; right; left; reflexivity) ltac:(cbn; clear - Hx LENB KR; lia) Ha)|].
              assert (Hb3 : In b' (OWX ++ ((q0, A0, n0) :: NEW1) ++ LB)) by (apply in_app_iff; right; right; exact Hb').
              assert (NEb : blk_id (q0, A0, n0) <> blk_id b').
              { intros Ei. apply (FRESH (q0, A0, n0) ltac:(left; reflexivity)). cbn [blk_id fst]. cbn [blk_id fst] in Ei. rewrite Ei, map_app. apply in_app_iff.
                apply in_app_iff in Hb'. destruct Hb' as [Hb'|Hb']; [| right; exact (in_map blk_id _ _ Hb')].
                exfalso. pose proof NDX as ND'. rewrite map_app in ND'. apply nodup_app_r in ND'. cbn [map app] in ND'. apply NoDup_cons_iff in ND' as [NI _].
                apply NI. cbn [blk_id fst] in *. rewrite Ei, map_app. apply in_app_iff. left. exact (in_map blk_id _ _ Hb'). }
              pose proof (AH_disjoint_gen _ _ _ _ (q0, A0, n0) b' HEAPX ltac:(apply in_app_iff; right; left; reflexivity) Hb3 NEb) as DJ.
              cbn [blk_addr blk_size fst snd] in DJ. clear - DJ Hr' LENB KR LTL. lia.
        -- eapply agree_on_mono; [exact (agree_on_of_munch_nw _ _ _ MU9)|]. intros a [HX Ha]. cbn [outside fst snd]. split; [| split; [| exact I]].
           ++ destruct Ha as [Ha|[Ha|(b' & Hb' & Hr')]]; [clear - Ha; lia| pose proof (client_static_below a Ha) as Hlow; clear - Hlow CN1 CEIL ALEN; lia|].
              pose proof (BND b' ltac:(apply in_app_iff; right; right; exact Hb')) as (_ & _ & Hc' & _). clear - Hr' Hc' ALEN CEIL LO STK0; lia.
           ++ intros Hx. apply HX. cbn [rin_ivs fst snd app]. left. exact Hx.
      * (* [comment removed for export] *)
        replace (len <=? n0) with false by (symmetry; apply Z.leb_gt; lia).
        replace (LIMIT_BEFORE_EXPANSION <? len) with false by (symmetry; apply Z.ltb_ge; unfold LIMIT_BEFORE_EXPANSION; lia).
        pose proof (grow_size_bounds len ltac:(clear - LENB LTL LEN30; lia)) as GB. cbv zeta in GB. set (n := (len + 3) / 3 * 4) in *.
        assert (CRn : mcost n <= CX) by (revert CRG; replace (len <=? n0) with false by (symmetry; apply Z.leb_gt; lia); intros CRG; exact CRG).
        step. step. step. if_cases KL; zc KL; [| exfalso; revert KL; rewrite ?unsigned_lit by lia; clear - LEN30 LTL LENB; lia]. clear KL.
        apply c8_zero_bytes_a in HFLG. cut_hd HFLG HFL0 (BUF + 25).
        step. step. step. step. step. step. step. step. step. step. step.
        setreg 20%Z (Z_to_bv 64 n) ltac:(f_equal; symmetry; subst n; apply magic_div3_word; clear - LENB LTL LEN30; lia).
        step. if_false.
        join2 HFL0 HFLG. apply c8_zero_of_bytes_a in HFL0. rename HFL0 into HFLG.
        (* [comment removed for export] *)
        step. step. step. step. step. step.
        (* [comment removed for export] *)
        match goal with H : stk ctasegs _ lo (bv_unsigned sp + OFS + -80) |- _ => rename H into STg end.
        carve_frame 64%nat STg. do 9 step. step. step.
        step. if_cases KN; zc KN; [exfalso; revert KN; rewrite ?unsigned_lit by (clear - BA0 BAC CN3 CEIL LO STK0 OFS0 SPR; alia); clear - BA0; lia|]. clear KN.
        step. step.
        step. if_cases KZ; zc KZ; [exfalso; revert KZ; rewrite ?unsigned_lit by lia; clear - GB; lia|]. clear KZ.
        step. if_cases KG; zc KG; [| exfalso; revert KG; rewrite ?unsigned_lit by lia; clear - GB KR; lia]. clear KG.
        step. step. step. step.
        name_mem mc.
        match goal with H : stk ctasegs mc lo _ |- _ => rename H into STc end. match goal with H : mem_inv ctasegs mc |- _ => rename H into MIc end.
        match goal with H : rw_cells ctasegs mc (bv_unsigned sp + OFS + -144) _ |- _ => rename H into FR2 end.
        assert (E144 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + OFS + -144)) = bv_unsigned sp + OFS + -144) by (apply unsigned_lit; clear - SPR LO LO0 STK0 STKG OFS0; lia).
        assert (E80 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + OFS + -80)) = bv_unsigned sp + OFS + -80) by (apply unsigned_lit; clear - SPR LO LO0 STK0 STKG OFS0; lia).
        assert (ALO : A0 + n0 <= lo /\ lo + 144 <= bv_unsigned sp + OFS - 80) by (clear - BAC CEIL LO STKG; lia).
        pose proof (DJL (q0, A0, n0) bB ltac:(left; reflexivity) HbB) as DJB. cbn [blk_addr blk_size fst snd] in DJB.
        (* [comment removed for export] *)
        assert (OIc : oinvK ΣX stX mc OWX boX ((q0, A0, n0) :: NEW1) CX).
        { kit @oinv_munch; [exact OI| exact MU| exact WM| exact MIc| | constructor; [left; cbn [fst snd]; clear - ALO LO STK0 OFS0; lia| constructor]].
          stk_join STc FR2 STf (bv_unsigned sp + OFS + -80). stk_join STf FR STF (bv_unsigned sp + OFS). exact STF. }
        kitp @oinv_call OCc. pose proof (OCc _ _ _ _ _ _ _ OIc) as (HEAPc & _ & _ & _ & _ & _ & _ & CSc & _). clear OCc.
        assert (UW1 : uw_chain USTACK_TOP mc (bv_unsigned sp + OFS + -80) (bv_unsigned sp + OFS) (bv_unsigned ra :: ras)).
        { uw_call_mu_tac mX 80 UW MU FR; [intros a Ha; cbn [outside fst snd]; clear - Ha; lia | clear; lia | uchk_open; clear - SP16 OFS16; Z.div_mod_to_equations; lia | clear - TOP OFS0; unfold USTACK_TOP in *; lia]. }
        assert (UW2 : uw_chain USTACK_TOP mc (bv_unsigned sp + OFS + -144) (bv_unsigned sp + OFS + -80) (0x24b4c0 :: bv_unsigned ra :: ras)).
        { lazymatch type of FR2 with rw_cells _ _ _ ?cs =>
            let pre := eval cbn [List.removelast] in (List.removelast (List.removelast cs)) in
            eapply (uw_call_mu [] mc mc _ _ 64 pre 0x24b4c0 (bv_unsigned sp + OFS));
              [exact UW1| apply munch_refl| intros a Ha; cbn; exact I| reflexivity| clear; lia| uchk_open; clear - SP16 OFS16; Z.div_mod_to_equations; lia
              | clear - TOP OFS0; unfold USTACK_TOP in *; lia| clear - SPR LO LO0 STK0 OFS0; lia
              | replace (bv_unsigned sp + OFS + -80 + -64) with (bv_unsigned sp + OFS + -144) by (clear; lia); exact FR2] end. }
        apply evt_done. cbn [abind apbind amalloc aret afree_opt afree option_map fst snd].
        eapply CRYPTO_malloc_walkAp with (n := n) (lo := lo) (OW := OWX) (LB := ((q0, A0, n0) :: NEW1) ++ LB) (ras := 0x24b4c0 :: bv_unsigned ra :: ras); rewrite ?E144.
        - exact HEAPc.
        - exact STc.
        - exact CEIL.
        - unfold CRYPTO_MALLOC_STACK, RT_STACK. clear - LO STKG. lia.
        - clear - TOP OFS0. unfold USTACK_TOP in *. lia.
        - uchk_open. clear - SP16 OFS16. Z.div_mod_to_equations. lia.
        - exact MIc.
        - reflexivity.
        - exact CSc.
        - reflexivity.
        - clear - GB. lia.
        - pose proof OIc as (PREc & _). pose proof PREc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CRc & _). clear - CRc CRn. lia.
        - rewrite E80. exact UW2.
        - rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_crea_malloc (uk_ctx_call _ _ _ _ E_grow_crea CTX)).
        - intros pn ΣN msN NIp PON.
          destruct PON as (w0 & w1 & w2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & w3 & w4 & w5 & w6 & F3 & fc3 & mN & A & -> & MIN & STN & AGN & CRN & BRN & HEAPN & ACCN & (junkN & BLKN)).
          rewrite ?E144 in STN, AGN. rewrite (ret_pc_even 0x1fd420) by (clear; lia).
          pose proof BRN as (BA0' & BA16' & _ & BAC' & BAI').
          assert (EA : bv_unsigned (Z_to_bv 64 A) = A) by (apply unsigned_lit; clear - BA0' BAC' CN3 GB; alia).
          pose proof (cb_len_a _ _ _ _ BLKN) as JL.
          (* [comment removed for export] *)
          assert (CLs : forall a, bv_unsigned sp + OFS - 144 <= a < bv_unsigned sp + OFS -> aclient_addr (OWX ++ ((q0, A0, n0) :: NEW1) ++ LB) (bv_unsigned sp + OFS + -144) a).
          { intros a Ha. left. clear - Ha TOP OFS0. unfold USTACK_TOP in *. lia. }
          assert (CLb : forall a, BUF <= a < BUF + 32 -> aclient_addr (OWX ++ ((q0, A0, n0) :: NEW1) ++ LB) (bv_unsigned sp + OFS + -144) a).
          { intros a Ha. right; right. exists bB. split; [exact HbB3| clear - Ha BB1 BB2; lia]. }
          assert (CLo : forall a, A0 <= a < A0 + n0 -> aclient_addr (OWX ++ ((q0, A0, n0) :: NEW1) ++ LB) (bv_unsigned sp + OFS + -144) a).
          { intros a Ha. right; right. exists (q0, A0, n0). split; [apply in_app_iff; right; left; reflexivity| cbn; exact Ha]. }
          apply (rw_cells_agree _ _ _ _ _ AGN) in FR; [| intros xa Hxa; cbn in Hxa; apply CLs; clear - Hxa; lia].
          apply (rw_cells_agree _ _ _ _ _ AGN) in FR2; [| intros xa Hxa; cbn in Hxa; apply CLs; clear - Hxa; lia].
          apply (rw_cells_agree _ _ _ _ _ AGN) in HLEN; [| intros xa Hxa; cbn in Hxa; apply CLb; clear - Hxa; lia].
          apply (rw_cells_agree _ _ _ _ _ AGN) in HDAT; [| intros xa Hxa; cbn in Hxa; apply CLb; clear - Hxa; lia].
          apply (rw_cells_agree _ _ _ _ _ AGN) in HMAX; [| intros xa Hxa; cbn in Hxa; apply CLb; clear - Hxa; lia].
          apply (rw_cells_agree _ _ _ _ _ AGN) in HFLG; [| intros xa Hxa; cbn in Hxa; apply CLb; clear - Hxa; lia].
          apply (rw_cells_agree _ _ _ _ _ AGN) in HBLK; [| intros xa Hxa; cbn in Hxa; apply CLo; clear - Hxa LENB; lia].
          (* [comment removed for export] *)
          assert (OIN : oinvK ΣN stX mN OWX boX ((pn, A, n) :: (q0, A0, n0) :: NEW1) (CX - mcost n)).
          { kit @oinv_alloc; [exact OIc| | exact HEAPN| exact MIN| | exact CRN| split; [apply mcost_nonneg_a; clear - GB; lia| exact CRn]].
            - eapply agree_on_mono; [exact AGN|]. intros a [Ha|[Ha|Ha]]; [left; clear - Ha; lia| right; left; exact Ha| right; right; exact Ha].
            - stk_join STN FR2 STf (bv_unsigned sp + OFS + -80). stk_join STf FR STF (bv_unsigned sp + OFS). exact STF. }
          kitp @oinv_facts OFN. pose proof (OFN _ _ _ _ _ _ _ OIN) as (HEAPN' & NDN & BNDN & FRESHN & DJLN & DJON). clear OFN.
          pose proof (DJON (pn, A, n)) as DJAN. pose proof (DJLN (pn, A, n) bB ltac:(left; reflexivity) HbB) as DJAB. cbn [blk_addr blk_size fst snd] in DJAB.
          assert (DJA0 : A + n <= A0 \/ A0 + n0 <= A).
          { pose proof (AH_disjoint_gen _ _ _ _ (pn, A, n) (q0, A0, n0) HEAPN ltac:(left; reflexivity) ltac:(apply in_app_iff; right; cbn; left; reflexivity)
                          ltac:(cbn; intros Ei; apply NIp; rewrite Ei, map_app; apply in_app_iff; right; apply (in_map blk_id _ (q0, A0, n0)); apply in_app_iff; left; left; reflexivity)) as DJ.
            cbn [blk_addr blk_size fst snd] in DJ. exact DJ. }
          pose proof HBLK as [[_ SRC] _]. cbn [cells_bytes cbytes app] in SRC. rewrite app_nil_r in SRC.
          pose proof (cb_len_a _ _ _ _ HBLK) as BL. assert (JLz : Z.of_nat (length bytes) = n0) by (rewrite BL; clear - N4; lia).
          destruct (AH_shb _ _ _ _ HEAPN) as [SHBn1 SHBn2].
          pose proof (munch_refl [(bv_unsigned sp + OFS - 144, bv_unsigned sp + OFS)]%Z mN) as MUN. pose proof (wmono_refl ctasegs mN) as WMN.
          apply implAp_from_evt.
          (* [comment removed for export] *)
          step. if_cases KA; zc KA; [exfalso; revert KA; rewrite ?EA; clear - BA0'; lia|]. clear KA.
          step. step. step. step.
          apply evt_done. eapply implAp_step_same.
          { eapply (asan_memcpy_cpsA) with (d := A) (s := A0) (bs := bytes) (bd := (pn, A, n)) (bsrc := (q0, A0, n0)) (lo := lo) (OW := (pn, A, n) :: OWX) (LB := ((q0, A0, n0) :: NEW1) ++ LB);
              try reflexivity; rewrite ?E144, ?JLz.
            - exact HEAPN.
            - exact STN.
            - exact CEIL.
            - unfold RT_STACK. clear - LO STKG. lia.
            - clear - TOP OFS0. unfold USTACK_TOP in *. lia.
            - uchk_open. clear - SP16 OFS16. Z.div_mod_to_equations. lia.
            - exact MIN.
            - left. reflexivity.
            - cbn [blk_addr blk_size fst snd]. clear - GB KR LENB; lia.
            - apply in_app_iff. right. cbn. left. reflexivity.
            - cbn [blk_addr blk_size fst snd]. clear; lia.
            - exact SRC.
            - clear - DJA0 GB KR LENB N4. lia.
            - clear - N4. lia.
            - unfold MallocRep.wz. reflexivity. }
          intros msM PO. unfold icall_post in PO. rewrite ?E144, ?JLz in PO.
          destruct PO as (v0 & v1 & v2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & v3 & v4 & v5 & v6 & F4 & fc4 & m4 & -> & MI4 & ST4 & HEAP4 & WM4 & AG4 & HCP & WR4).
          rewrite (ret_pc_even 0x1fd434) by (clear; lia).
          assert (CL4 : forall a, aclient_addr (OWX ++ ((q0, A0, n0) :: NEW1) ++ LB) (bv_unsigned sp + OFS + -144) a -> ~ (A <= a < A + n) ->
                        aclient_addr (((pn, A, n) :: OWX) ++ ((q0, A0, n0) :: NEW1) ++ LB) (bv_unsigned sp + OFS + -144) a /\ ~ (A <= a < A + n0)).
          { intros a Ha Hn. split; [| clear - Hn GB KR LENB; lia].
            destruct Ha as [Ha|[Ha|(b' & Hb' & Hr')]]; [left; exact Ha| right; left; exact Ha| right; right; exists b'; split; [right; exact Hb'| exact Hr']]. }
          apply (rw_cells_agree _ _ _ _ _ AG4) in FR; [| intros xa Hxa; cbn in Hxa; apply CL4; [apply CLs; clear - Hxa; lia| clear - Hxa ALO BAC' CEIL; lia]].
          apply (rw_cells_agree _ _ _ _ _ AG4) in FR2; [| intros xa Hxa; cbn in Hxa; apply CL4; [apply CLs; clear - Hxa; lia| clear - Hxa ALO BAC' CEIL; lia]].
          apply (rw_cells_agree _ _ _ _ _ AG4) in HLEN; [| intros xa Hxa; cbn in Hxa; apply CL4; [apply CLb; clear - Hxa; lia| clear - Hxa DJAB BB1 BB2 GB KR; lia]].
          apply (rw_cells_agree _ _ _ _ _ AG4) in HDAT; [| intros xa Hxa; cbn in Hxa; apply CL4; [apply CLb; clear - Hxa; lia| clear - Hxa DJAB BB1 BB2 GB KR; lia]].
          apply (rw_cells_agree _ _ _ _ _ AG4) in HMAX; [| intros xa Hxa; cbn in Hxa; apply CL4; [apply CLb; clear - Hxa; lia| clear - Hxa DJAB BB1 BB2 GB KR; lia]].
          apply (rw_cells_agree _ _ _ _ _ AG4) in HFLG; [| intros xa Hxa; cbn in Hxa; apply CL4; [apply CLb; clear - Hxa; lia| clear - Hxa DJAB BB1 BB2 GB KR; lia]].
          apply (rw_cells_agree _ _ _ _ _ AG4) in HBLK; [| intros xa Hxa; cbn in Hxa; apply CL4; [apply CLo; clear - Hxa LENB; lia| clear - Hxa DJA0 LENB; lia]].
          assert (HN1 : rw_cells ctasegs m4 A [CB (Z.to_nat n0) bytes]).
          { rewrite <- BL. apply rw_cells_of_bytes_a; [exact HCP| rewrite JLz; exact WR4]. }
          (* [comment removed for export] *)
          assert (OI4 : oinvK ΣN stX m4 OWX boX ((pn, A, n) :: (q0, A0, n0) :: NEW1) (CX - mcost n - 0)).
          { kit @oinv_heap; [exact OIN| | intros b' [Hb'|Hb']; apply in_app_iff; [left; exact Hb'| right; exact Hb']| destruct (AH_release _ _ _ _ _ HEAP4) as [H4 _]; exact H4| pose proof OIN as (_ & _ & _ & _ & _ & _ & _ & LBOKN); exact LBOKN| exact MI4| | clear; lia| split; [clear; lia| clear - CRn CRX; pose proof (mcost_nonneg_a n); lia]].
            - eapply agree_on_mono; [exact AG4|]. intros a [Ha HXa]. split.
              + destruct Ha as [Ha|[Ha|(b' & Hb' & Hr')]]; [left; clear - Ha; lia| right; left; exact Ha| right; right; exists b'; split; [| exact Hr']].
                apply in_app_iff in Hb'. apply in_app_iff. destruct Hb' as [Hb'|Hb']; [left; right; exact Hb'| right; apply in_app_iff; right; exact Hb'].
              + destruct Ha as [Ha|[Ha|(b' & Hb' & Hr')]]; [clear - Ha BAC' CEIL STK0 LO GB KR; lia| intros Hx; exact (ApErrKitA2.blk_not_static _ _ _ _ (pn, A, n) a HEAPN ltac:(left; reflexivity) ltac:(cbn; clear - Hx GB KR; lia) Ha)|].
                apply in_app_iff in Hb'. destruct Hb' as [Hb'|Hb'].
                ++ pose proof (DJON (pn, A, n) b' ltac:(left; reflexivity) Hb') as DJ. cbn [blk_addr blk_size fst snd] in DJ. clear - DJ Hr' GB KR LENB. lia.
                ++ pose proof (DJLN (pn, A, n) b' ltac:(left; reflexivity) Hb') as DJ. cbn [blk_addr blk_size fst snd] in DJ. clear - DJ Hr' GB KR LENB. lia.
            - stk_join ST4 FR2 STf (bv_unsigned sp + OFS + -80). stk_join STf FR STF (bv_unsigned sp + OFS). exact STF. }
          replace (CX - mcost n - 0) with (CX - mcost n) in OI4 by (clear; lia).
          (* [comment removed for export] *)
          kitp @oinv_facts OF4. pose proof (OF4 _ _ _ _ _ _ _ OI4) as (HEAP4' & ND4 & _). clear OF4.
          pose proof OI4 as (_ & _ & _ & _ & _ & _ & _ & LBOK4). pose proof LBOK4 as LBOK4c. apply Forall_cons_iff in LBOK4c as [OKa LBOK4c]. apply Forall_cons_iff in LBOK4c as [OKo LBOK1].
          pose proof (AH_adopt _ _ _ _ (q0, A0, n0) HEAP4' ltac:(apply in_app_iff; left; right; left; reflexivity) OKo) as HEAPa.
          cbn [blk_id fst app] in HEAPa. rewrite lb_remove_cons in HEAPa.
          replace (bptr_eqb pn q0) with false in HEAPa by (symmetry; apply bptr_eqb_neq; intros Ei; apply NIp; rewrite Ei, map_app; apply in_app_iff; right; apply (in_map blk_id _ (q0, A0, n0)); apply in_app_iff; left; left; reflexivity).
          rewrite lb_remove_cons, bptr_eqb_refl in HEAPa.
          rewrite (lb_remove_notin q0 (NEW1 ++ LB)) in HEAPa by (intros Hin; pose proof ND4 as ND'; rewrite map_app in ND'; apply nodup_app_r in ND'; cbn [map app] in ND';
               apply NoDup_cons_iff in ND' as [_ ND']; apply NoDup_cons_iff in ND' as [NI _]; exact (NI Hin)).
          destruct (AH_shb _ _ _ _ HEAP4) as [SHB41 SHB42].
          pose proof (munch_refl [(bv_unsigned sp + OFS - 144, bv_unsigned sp + OFS)]%Z m4) as MU4. pose proof (wmono_refl ctasegs m4) as WM4'.
          apply implAp_from_evt.
          (* [comment removed for export] *)
          step. step. step. step. step.
          apply evt_done. cbn [apbind aret fst snd].
          eapply CRYPTO_clear_free_walkAp with (p := q0) (A := A0) (n := n0) (num := n0) (lo := lo) (OW := (q0, A0, n0) :: OWX) (LB := ((pn, A, n) :: NEW1) ++ LB) (ras := 0x24b4c0 :: bv_unsigned ra :: ras); rewrite ?E144.
          -- exact HEAPa.
          -- left. reflexivity.
          -- exact ST4.
          -- exact CEIL.
          -- unfold CRYPTO_CLEAR_FREE_STACK, OPENSSL_CLEANSE_STACK, RT_STACK. clear - LO STKG. lia.
          -- clear - TOP OFS0. unfold USTACK_TOP in *. lia.
          -- uchk_open. clear - SP16 OFS16. Z.div_mod_to_equations. lia.
          -- exact MI4.
          -- reflexivity.
          -- kitp @oinv_call OC4. pose proof (OC4 _ _ _ _ _ _ _ OI4) as (_ & _ & _ & _ & _ & _ & _ & CS4 & _). clear OC4. exact CS4.
          -- clear - N4. lia.
          -- clear - N4. lia.
          -- reflexivity.
          -- unfold MallocRep.wz. reflexivity.
          -- (* [comment removed for export] *)
            rewrite E80. eapply uw_chain_agree; [eapply uw_chain_agree; [exact UW2|]|].
             ++ eapply agree_on_mono; [exact AGN|]. intros a Ha. cbv beta in Ha. left. exact Ha.
             ++ eapply agree_on_mono; [exact AG4|]. intros a Ha. cbv beta in Ha. apply CL4; [left; exact Ha| clear - Ha BAC' CEIL LO STK0 STKG GB KR; lia].
          -- rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_crea_cfree (uk_ctx_call _ _ _ _ E_grow_crea CTX)).
          -- intros ΣF msF POF. unfold cfree_postA in POF. rewrite ?E144 in POF.
             destruct POF as (z0 & z1 & z2 & z10 & z11 & z12 & z13 & z14 & z15 & z16 & z17 & z3 & z4 & z5 & z6 & F5 & fc5 & mF & -> & MIF & STF' & AGF & CRF & HEAPF).
             rewrite (ret_pc_even 0x1fd448) by (clear; lia).
             assert (NIq : ~ In q0 (map blk_id OWX)).
             { intros Hin. apply (FRESH (q0, A0, n0) ltac:(left; reflexivity)). rewrite map_app. apply in_app_iff. left. exact Hin. }
             assert (NIq2 : ~ In q0 (map blk_id (((pn, A, n) :: NEW1) ++ LB))).
             { cbn [map app blk_id fst]. intros [Ei|Hin]; [apply NIp; rewrite Ei, map_app; apply in_app_iff; right; apply (in_map blk_id _ (q0, A0, n0)); apply in_app_iff; left; left; reflexivity|].
               pose proof NDX as ND'. rewrite map_app in ND'. apply nodup_app_r in ND'. cbn [map app] in ND'. apply NoDup_cons_iff in ND' as [NI _]. exact (NI Hin). }
             rewrite lb_remove_cons, bptr_eqb_refl, (lb_remove_notin _ _ NIq) in HEAPF.
             cbn [app] in AGF. rewrite lb_remove_cons, bptr_eqb_refl, lb_remove_app, (lb_remove_notin _ _ NIq), (lb_remove_notin _ _ NIq2) in AGF.
             (* [comment removed for export] *)
             assert (CLf : forall a, aclient_addr (OWX ++ ((q0, A0, n0) :: NEW1) ++ LB) (bv_unsigned sp + OFS + -144) a -> ~ (A0 <= a < A0 + n0) ->
                           aclient_addr (OWX ++ ((pn, A, n) :: NEW1) ++ LB) (bv_unsigned sp + OFS + -144) a).
             { intros a Ha Hn. destruct Ha as [Ha|[Ha|(b' & Hb' & Hr')]]; [left; exact Ha| right; left; exact Ha| right; right].
               apply in_app_iff in Hb'. destruct Hb' as [Hb'|Hb']; [exists b'; split; [apply in_app_iff; left; exact Hb'| exact Hr']|].
               cbn [app] in Hb'. destruct Hb' as [<-|Hb']; [exfalso; exact (Hn Hr')|].
               exists b'; split; [apply in_app_iff; right; right; exact Hb'| exact Hr']. }
             apply (rw_cells_agree _ _ _ _ _ AGF) in FR; [| intros xa Hxa; cbn in Hxa; apply CLf; [apply CLs; clear - Hxa; lia| clear - Hxa ALO; lia]].
             apply (rw_cells_agree _ _ _ _ _ AGF) in FR2; [| intros xa Hxa; cbn in Hxa; apply CLf; [apply CLs; clear - Hxa; lia| clear - Hxa ALO; lia]].
             apply (rw_cells_agree _ _ _ _ _ AGF) in HLEN; [| intros xa Hxa; cbn in Hxa; apply CLf; [apply CLb; clear - Hxa; lia| clear - Hxa DJB BB1 BB2; lia]].
             apply (rw_cells_agree _ _ _ _ _ AGF) in HDAT; [| intros xa Hxa; cbn in Hxa; apply CLf; [apply CLb; clear - Hxa; lia| clear - Hxa DJB BB1 BB2; lia]].
             apply (rw_cells_agree _ _ _ _ _ AGF) in HMAX; [| intros xa Hxa; cbn in Hxa; apply CLf; [apply CLb; clear - Hxa; lia| clear - Hxa DJB BB1 BB2; lia]].
             apply (rw_cells_agree _ _ _ _ _ AGF) in HFLG; [| intros xa Hxa; cbn in Hxa; apply CLf; [apply CLb; clear - Hxa; lia| clear - Hxa DJB BB1 BB2; lia]].
             apply (rw_cells_agree _ _ _ _ _ AGF) in HN1; [| intros xa Hxa; cbn in Hxa; right; right; exists (pn, A, n); split; [apply in_app_iff; right; cbn; left; reflexivity| cbn; clear - Hxa GB KR LENB; lia]].
             (* [comment removed for export] *)
             assert (OIF : oinvK ΣF stX mF OWX boX ((pn, A, n) :: NEW1) (CX - mcost n - 0)).
             { kit @oinv_heap; [exact OI4| | intros b' [Hb'|Hb']; apply in_app_iff; [left; exact Hb'| right; exact Hb']| exact HEAPF| constructor; [exact OKa| exact LBOK1]| exact MIF| | rewrite CRF; clear; lia| clear - CRn CRX; pose proof (mcost_nonneg_a n); lia].
               - eapply agree_on_mono; [exact AGF|]. intros a [Ha HXa].
                 destruct Ha as [Ha|[Ha|(b' & Hb' & Hr')]]; [left; clear - Ha; lia| right; left; exact Ha| right; right; exists b'; split; [| exact Hr']].
                 apply in_app_iff in Hb'. apply in_app_iff. destruct Hb' as [Hb'|Hb']; [left; exact Hb'| right; right; apply in_app_iff; right; exact Hb'].
               - stk_join STF' FR2 STf (bv_unsigned sp + OFS + -80). stk_join STf FR STF (bv_unsigned sp + OFS). exact STF. }
             replace (CX - mcost n - 0) with (CX - mcost n) in OIF by (clear; lia).
             kitp @oinv_facts OFF. pose proof (OFF _ _ _ _ _ _ _ OIF) as (HEAPF' & NDF & BNDF & FRESHF & DJLF & DJOF). clear OFF.
             assert (HbBF : In bB (OWX ++ ((pn, A, n) :: NEW1) ++ LB)) by (apply in_app_iff; right; apply in_app_iff; right; exact HbB).
             ablock HEAPF' HbBF ACCF OFFF.
             destruct (AH_shb _ _ _ _ HEAPF) as [SHBF1 SHBF2].
             pose proof (munch_refl [(bv_unsigned sp + OFS - 144, bv_unsigned sp + OFS); (BUF, BUF + 32)]%Z mF) as MUF. pose proof (wmono_refl ctasegs mF) as WMF.
             assert (OFFWF : offshW [(bv_unsigned sp + OFS - 144, bv_unsigned sp + OFS); (BUF, BUF + 32)]%Z) by (cbn [offshW]; clear - CEIL LO STK0 STKG C2 OFFB BB1 BB2; alia).
             apply implAp_from_evt.
             (* [comment removed for export] *)
             step. step. step. do 7 step. release_frame FR2 STF' (bv_unsigned sp + OFS + -80). step. step.
             step. if_cases KA; zc KA; [| exfalso; revert KA; rewrite ?EA; clear - BA0'; lia]. clear KA.
             step. step. step. step. step.
             step. setreg 12%Z (Z_to_bv 64 (len - L0)) ltac:(rewrite (unsigned_lit L0) by (clear - LENB N4; lia); f_equal; clear; lia).
             step. name_mem m5.
             match goal with H : stk ctasegs m5 lo _ |- _ => rename H into ST5 end. match goal with H : mem_inv ctasegs m5 |- _ => rename H into MI5 end.
             match goal with H : munch _ mF m5 |- _ => rename H into MU5 end. match goal with H : wmono ctasegs mF m5 |- _ => rename H into WM5 end.
             assert (HEAP5 : AHEAP ΣF OWX (((pn, A, n) :: NEW1) ++ LB) m5).
             { eapply AH_frame; [exact HEAPF'| exact MU5| exact WM5|]. constructor; [left; cbn [fst snd]; clear - CEIL LO STK0 STKG OFS0 TOP; alia|].
               constructor; [right; right; exists bB; split; [exact HbBF| cbn [fst snd]; clear - BB1 BB2; lia]| constructor]. }
             assert (OI5 : oinvK ΣF stX m5 OWX boX ((pn, A, n) :: NEW1) (CX - mcost n)).
             { kit @oinv_munch; [exact OIF| exact MU5| exact WM5| exact MI5| | constructor; [left; cbn [fst snd]; clear - ALO LO STK0 OFS0; lia| constructor; [right; left; exists (BUF, BUF + 32); split; [exact XBUF| cbn; clear; lia]| constructor]]].
               stk_join ST5 FR STF (bv_unsigned sp + OFS). exact STF. }
             (* [comment removed for export] *)
             replace (Z.to_nat n0) with (Z.to_nat L0 + Z.to_nat (n0 - L0))%nat in HN1 by (clear - LENB; lia).
             apply cb_split_a in HN1. cut_hd HN1 HB1 (A + L0). clear HN1.
             pose proof (cb_len_a _ _ _ _ BLKN) as JL'.
             replace (Z.to_nat n) with (Z.to_nat len + Z.to_nat (n - len))%nat in BLKN by (clear - GB LENB LTL; lia).
             apply cb_split_a in BLKN. cut_hd BLKN HB2 (A + len). rename BLKN into HB3. clear HB2.
             apply (rw_cells_agree _ _ _ _ _ AG4) in HB3; [| intros xa Hxa; cbn in Hxa; split; [right; right; exists (pn, A, n); split; [left; reflexivity| cbn; clear - Hxa GB LTL LENB; lia]| clear - Hxa GB KR; lia]].
             apply (rw_cells_agree _ _ _ _ _ AGF) in HB3; [| intros xa Hxa; cbn in Hxa; right; right; exists (pn, A, n); split; [apply in_app_iff; right; cbn; left; reflexivity| cbn; clear - Hxa GB LTL LENB; lia]].
             eapply rw_cells_transport in HB3; [| exact MU5| exact WM5| cbn [cells_size csize Nat.add disjoint_from fst snd]; clear - BAC' CEIL LO STKG DJAB BB1 BB2 GB; alia].
             apply evt_done. eapply implAp_step_same.
             { eapply (asan_memset_cpsA) with (d := A + L0) (n := len - L0) (c := z8) (bd := (pn, A, n)) (lo := lo) (OW := OWX) (LB := ((pn, A, n) :: NEW1) ++ LB);
                 try reflexivity; rewrite ?E80.
               - exact HEAP5.
               - exact ST5.
               - exact CEIL.
               - unfold RT_STACK; clear - LO STKG; lia.
               - clear - TOP OFS0; unfold USTACK_TOP in *; lia.
               - uchk_open; clear - SP16 OFS16; Z.div_mod_to_equations; lia.
               - exact MI5.
               - apply in_app_iff; right; cbn; left; reflexivity.
               - cbn [blk_addr blk_size fst snd]. clear - LENB; lia.
               - cbn [blk_addr blk_size fst snd]. clear - GB LTL; lia.
               - clear - LENB LTL LEN30; lia. }
             intros msM PO. unfold icall_post in PO. rewrite ?E80 in PO.
             destruct PO as (u0 & u1 & u2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & u3 & u4 & u5 & u6 & F6 & fc6 & m6 & -> & MI6 & ST6 & HEAP6 & WM6 & AG6 & BZ & WR6).
             rewrite (ret_pc_even 0x24b51c) by (clear; lia).
             assert (CL6 : forall a, (bv_unsigned sp + OFS - 80 <= a < bv_unsigned sp + OFS \/ BUF <= a < BUF + 32) ->
                           aclient_addr (OWX ++ ((pn, A, n) :: NEW1) ++ LB) (bv_unsigned sp + OFS + -80) a /\ ~ (A + L0 <= a < A + L0 + (len - L0))).
             { intros a [Ha|Ha].
               - split; [left; clear - Ha TOP OFS0; unfold USTACK_TOP in *; lia| clear - Ha BAC' CEIL LO STK0 STKG GB LENB LTL; lia].
               - split; [right; right; exists bB; split; [exact HbBF| clear - Ha BB1 BB2; lia]| clear - Ha DJAB BB1 BB2 GB LENB LTL; lia]. }
             apply (rw_cells_agree _ _ _ _ _ AG6) in FR; [| intros xa Hxa; cbn in Hxa; apply CL6; clear - Hxa; lia].
             apply (rw_cells_agree _ _ _ _ _ AG6) in HLEN; [| intros xa Hxa; cbn in Hxa; apply CL6; clear - Hxa; lia].
             apply (rw_cells_agree _ _ _ _ _ AG6) in HDAT; [| intros xa Hxa; cbn in Hxa; apply CL6; clear - Hxa; lia].
             apply (rw_cells_agree _ _ _ _ _ AG6) in HMAX; [| intros xa Hxa; cbn in Hxa; apply CL6; clear - Hxa; lia].
             apply (rw_cells_agree _ _ _ _ _ AG6) in HFLG; [| intros xa Hxa; cbn in Hxa; apply CL6; clear - Hxa; lia].
             apply (rw_cells_agree _ _ _ _ _ AG6) in HB1; [| intros xa Hxa; cbn in Hxa; split; [right; right; exists (pn, A, n); split; [apply in_app_iff; right; cbn; left; reflexivity| cbn; clear - Hxa LENB GB LTL; lia]| clear - Hxa; lia]].
             apply (rw_cells_agree _ _ _ _ _ AG6) in HB3; [| intros xa Hxa; cbn in Hxa; split; [right; right; exists (pn, A, n); split; [apply in_app_iff; right; cbn; left; reflexivity| cbn; clear - Hxa LENB GB LTL; lia]| clear - Hxa; lia]].
             assert (HZ : rw_cells ctasegs m6 (A + L0) [CB (Z.to_nat (len - L0)) (repeat z8 (Z.to_nat (len - L0)))]).
             { pose proof (rw_cells_of_bytes_a m6 (A + L0) _ BZ) as HZ0. rewrite repeat_length in HZ0. apply HZ0. rewrite Z2Nat.id by (clear - LTL; lia). exact WR6. }
             assert (OI6 : oinvK ΣF stX m6 OWX boX ((pn, A, n) :: NEW1) (CX - mcost n - 0)).
             { kit @oinv_heap; [exact OI5| | intros b' [Hb'|Hb']; apply in_app_iff; [left; exact Hb'| right; exact Hb']| exact HEAP6| constructor; [exact OKa| exact LBOK1]| exact MI6| | clear; lia| clear - CRn CRX; pose proof (mcost_nonneg_a n); lia].
               - eapply agree_on_mono; [exact AG6|]. intros a [Ha HXa]. split.
                 + destruct Ha as [Ha|[Ha|(b' & Hb' & Hr')]]; [left; clear - Ha; lia| right; left; exact Ha| right; right; exists b'; split; [| exact Hr']].
                   apply in_app_iff in Hb'. apply in_app_iff. destruct Hb' as [Hb'|Hb']; [left; exact Hb'| right; apply in_app_iff; right; exact Hb'].
                 + destruct Ha as [Ha|[Ha|(b' & Hb' & Hr')]]; [clear - Ha BAC' CEIL STK0 LO GB LTL; lia| intros Hx; exact (ApErrKitA2.blk_not_static _ _ _ _ (pn, A, n) a HEAP6 ltac:(apply in_app_iff; right; cbn; left; reflexivity) ltac:(cbn; clear - Hx GB LTL LENB; lia) Ha)|].
                   apply in_app_iff in Hb'. destruct Hb' as [Hb'|Hb'].
                   ** pose proof (DJOF (pn, A, n) b' ltac:(left; reflexivity) Hb') as DJ. cbn [blk_addr blk_size fst snd] in DJ. clear - DJ Hr' GB LTL LENB. lia.
                   ** pose proof (DJLF (pn, A, n) b' ltac:(left; reflexivity) Hb') as DJ. cbn [blk_addr blk_size fst snd] in DJ. clear - DJ Hr' GB LTL LENB. lia.
               - stk_join ST6 FR STF (bv_unsigned sp + OFS). exact STF. }
             replace (CX - mcost n - 0) with (CX - mcost n) in OI6 by (clear; lia).
             ablock HEAP6 HbBF ACC6 OFF6.
             pose proof (munch_refl [(bv_unsigned sp + OFS - 80, bv_unsigned sp + OFS); (BUF, BUF + 32)]%Z m6) as MU6. pose proof (wmono_refl ctasegs m6) as WM6'.
             assert (OFFW6 : offshW [(bv_unsigned sp + OFS - 80, bv_unsigned sp + OFS); (BUF, BUF + 32)]%Z) by (cbn [offshW]; clear - CEIL LO STK0 STKG C2 OFF6 BB1 BB2; alia).   (* [comment removed for export] *)
             rename MU5 into MU5o. rename WM5 into WM5o.
             apply implAp_from_evt.
             (* [comment removed for export] *)
             step. step. do 9 step. release_frame FR ST6 (bv_unsigned sp + OFS). step. step.
             name_mem m9.
             match goal with H : stk ctasegs m9 lo _ |- _ => rename H into ST9 end. match goal with H : mem_inv ctasegs m9 |- _ => rename H into MI9 end.
             match goal with H : munch _ m6 m9 |- _ => rename H into MU9 end. match goal with H : wmono ctasegs m6 m9 |- _ => rename H into WM9 end.
             apply evt_done. cbn [aret]. apply implAp_ret.
             (* [comment removed for export] *)
             join2 HZ HB3. apply cb_join_a in HZ. replace (Z.to_nat (len - L0) + Z.to_nat (n - len))%nat with (Z.to_nat (n - L0)) in HZ by (clear - LENB GB LTL; lia). join2 HB1 HZ.
             join2 HLEN HDAT. join2 HLEN HMAX. join2 HLEN HFLG.
             unfold grow_postA. cbn [fst snd]. unfold grow_costA, grow_capA, bm_max; cbn [bm_len bm_data bm_bytes]. replace (len <=? n0) with false by (symmetry; apply Z.leb_gt; exact KR).
             eexists u0, u1, u2, _, _, _, _, _, _, _, u3, u4, u5, u6, F6, fc6, m9, OWX, pn, A, n, _.
             split; [reflexivity|]. split; [reflexivity|]. split; [subst n; reflexivity|].
             split. { kit @oinv_munch; [exact OI6| exact MU9| exact WM9| exact MI9| exact ST9|].
                      constructor; [left; cbn [fst snd]; clear - ALO LO STK0 OFS0; lia|]. constructor; [right; left; exists (BUF, BUF + 32); split; [exact XBUF| cbn; clear; lia]| constructor]. }
             split; [intros bb Hbb; exact Hbb|].
             split; [exact HLEN|].
             split; [exact HB1|].
             split; [clear - GB; lia|]. split; [clear - GB; lia|]. split; [exact BA0'|]. split; [exact BA16'|]. split; [exact BAC'|]. split; [subst n; reflexivity|].
             (* [comment removed for export] *)
             assert (XCL : forall a, ax_client (NEW1 ++ LB) (bv_unsigned sp + OFS) ([(BUF, BUF + 32)] ++ LIBW_A) a ->
                       outside [(bv_unsigned sp + OFS - 144, bv_unsigned sp + OFS); (BUF, BUF + 32)]%Z a
                       /\ aclient_addr (OWX ++ ((q0, A0, n0) :: NEW1) ++ LB) (bv_unsigned sp + OFS + -144) a /\ ~ (A <= a < A + n) /\ ~ (A0 <= a < A0 + n0)).
             { intros a [HX Ha]. assert (NB : ~ (BUF <= a < BUF + 32)) by (intros Hx; apply HX; cbn [rin_ivs fst snd app]; left; exact Hx).
               destruct Ha as [Ha|[Ha|(b' & Hb' & Hr')]].
               - cbn [outside fst snd]. split; [clear - Ha NB; lia|]. split; [left; clear - Ha; lia|]. clear - Ha BAC' CEIL LO STK0 ALO. lia.
               - pose proof (client_static_below a Ha) as Hlow. cbn [outside fst snd]. split; [clear - Hlow CN1 CEIL ALO NB; lia|]. split; [right; left; exact Ha|].
                 split; intros Hx; [exact (ApErrKitA2.blk_not_static _ _ _ _ (pn, A, n) a HEAPN ltac:(left; reflexivity) ltac:(cbn; exact Hx) Ha)
                                  | exact (ApErrKitA2.blk_not_static _ _ _ _ (q0, A0, n0) a HEAPX ltac:(apply in_app_iff; right; left; reflexivity) ltac:(cbn; exact Hx) Ha)].
               - assert (Hb3 : In b' (OWX ++ ((q0, A0, n0) :: NEW1) ++ LB)) by (apply in_app_iff; right; right; exact Hb').
                 pose proof (BND b' Hb3) as (_ & _ & Hc' & _).
                 cbn [outside fst snd]. split; [clear - Hr' Hc' CEIL ALO NB; lia|]. split; [right; right; exists b'; split; [exact Hb3| exact Hr']|]. split.
                 + pose proof (DJLN (pn, A, n) b' ltac:(left; reflexivity)) as DJ1. pose proof (DJON (pn, A, n) b' ltac:(left; reflexivity)) as DJ2.
                   apply in_app_iff in Hb'. destruct Hb' as [Hb'|Hb'].
                   * assert (NE1 : blk_id (pn, A, n) <> blk_id b') by (cbn; intros Ei; apply NIp; rewrite Ei, map_app; apply in_app_iff; right; apply in_map; apply in_app_iff; left; right; exact Hb').
                     pose proof (AH_disjoint_gen _ _ _ _ (pn, A, n) b' HEAPN ltac:(left; reflexivity) ltac:(apply in_app_iff; right; apply in_app_iff; left; right; exact Hb') NE1) as DJ.
                     cbn [blk_addr blk_size fst snd] in DJ. clear - DJ Hr'. lia.
                   * specialize (DJ1 Hb'). cbn [blk_addr blk_size fst snd] in DJ1. clear - DJ1 Hr'. lia.
                 + assert (NEb : blk_id (q0, A0, n0) <> blk_id b').
                   { cbn. intros Ei. apply in_app_iff in Hb'. destruct Hb' as [Hb'|Hb'].
                     - pose proof NDX as ND'. rewrite map_app in ND'. apply nodup_app_r in ND'. cbn [map app] in ND'. apply NoDup_cons_iff in ND' as [NI _].
                       apply NI. cbn [blk_id fst]. rewrite Ei, map_app. apply in_app_iff. left. exact (in_map blk_id _ _ Hb').
                     - apply (FRESH (q0, A0, n0) ltac:(left; reflexivity)). cbn [blk_id fst]. rewrite Ei, map_app. apply in_app_iff. right. exact (in_map blk_id _ _ Hb'). }
                   pose proof (AH_disjoint_gen _ _ _ _ (q0, A0, n0) b' HEAPX ltac:(apply in_app_iff; right; left; reflexivity) Hb3 NEb) as DJ.
                   cbn [blk_addr blk_size fst snd] in DJ. clear - DJ Hr'. lia. }
             intros a HXa Hc. destruct (XCL a Hc) as (O1 & C1' & NA & NO). cbn [outside fst snd] in O1. destruct O1 as (O1 & O2 & _).
             assert (C2' : aclient_addr (OWX ++ ((pn, A, n) :: NEW1) ++ LB) (bv_unsigned sp + OFS + -80) a).
             { destruct (CLf a C1' NO) as [H|[H|H]]; [left; clear - H O1; lia| right; left; exact H| right; right; exact H]. }
             rewrite (agree_on_of_munch_nw _ _ _ MU9 a HXa ltac:(cbn [outside fst snd]; split; [clear - O1; lia| split; [exact O2| exact I]])).
             rewrite (AG6 a HXa ltac:(split; [exact C2'| clear - NA GB LTL LENB; lia])).
             rewrite (agree_on_of_munch_nw _ _ _ MU5o a HXa ltac:(cbn [outside fst snd]; split; [exact O1| split; [exact O2| exact I]])).
             rewrite (AGF a HXa (CLf a C1' NO)).
             rewrite (AG4 a HXa (CL4 a C1' ltac:(clear - NA GB KR; lia))).
             rewrite (AGN a HXa C1').
             rewrite (agree_on_of_munch_nw _ _ _ MU a HXa ltac:(cbn [outside fst snd]; split; [exact O1| exact I])).
             reflexivity.
    + (* [comment removed for export] *)
      assert (L00 : L0 = 0) by (clear - LENB; lia). subst A0. rewrite L00 in *. clear LENB L00.
      pose proof (munch_refl [(bv_unsigned sp + OFS - 144, bv_unsigned sp + OFS)]%Z mX) as MU. pose proof (wmono_refl ctasegs mX) as WM.
      assert (OFFW : offshW [(bv_unsigned sp + OFS - 144, bv_unsigned sp + OFS)]%Z) by (cbn [offshW]; clear - CEIL LO STK0 STKG C2; alia).
      replace (len <=? 0) with false by (symmetry; apply Z.leb_gt; clear - LTL; lia).
      replace (LIMIT_BEFORE_EXPANSION <? len) with false by (symmetry; apply Z.ltb_ge; unfold LIMIT_BEFORE_EXPANSION; clear - LEN30; lia).
      pose proof (grow_size_bounds len ltac:(clear - LTL LEN30; lia)) as GB. cbv zeta in GB. set (n := (len + 3) / 3 * 4) in *.
      assert (CRn : mcost n <= CX) by (revert CRG; replace (len <=? 0) with false by (symmetry; apply Z.leb_gt; clear - LTL; lia); intros CRG; exact CRG).
      apply implAp_from_evt.
      (* [comment removed for export] *)
      carve_frame 80%nat STX. do 11 step.
      step. step. step.
      step. if_cases K0; zc K0; [exfalso; revert K0; rewrite ?unsigned_lit by lia; clear - LTL; lia|]. clear K0.
      step.
      step. if_cases KR; zc KR; [exfalso; revert KR; rewrite ?unsigned_lit by lia; clear - LTL; lia|]. clear KR.
      step. step. step. if_cases KL; zc KL; [| exfalso; revert KL; rewrite ?unsigned_lit by lia; clear - LEN30 LTL; lia]. clear KL.
      apply c8_zero_bytes_a in HFLG. cut_hd HFLG HFL0 (BUF + 25).
      step. step. step. step. step. step. step. step. step. step. step.
      setreg 20%Z (Z_to_bv 64 n) ltac:(f_equal; symmetry; subst n; apply magic_div3_word; clear - LTL LEN30; lia).
      step. if_false.
      join2 HFL0 HFLG. apply c8_zero_of_bytes_a in HFL0. rename HFL0 into HFLG.
      (* [comment removed for export] *)
      step. step. step. step. step. step.
      match goal with H : stk ctasegs _ lo (bv_unsigned sp + OFS + -80) |- _ => rename H into STg end.
      carve_frame 64%nat STg. do 9 step. step. step.
      step. if_cases KN; zc KN; [| exfalso; revert KN; rewrite ?unsigned_lit by (clear; lia); clear; lia]. clear KN.
      step. step. step. do 7 step.
      match goal with H : rw_cells ctasegs _ (bv_unsigned sp + OFS + -144) _ |- _ => rename H into FR2 end.
      match goal with H : stk ctasegs _ lo (bv_unsigned sp + OFS + -144) |- _ => release_frame FR2 H (bv_unsigned sp + OFS + -80) end.
      step. step.
      name_mem mc.
      match goal with H : stk ctasegs mc lo _ |- _ => rename H into STc end. match goal with H : mem_inv ctasegs mc |- _ => rename H into MIc end.
      assert (E80 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + OFS + -80)) = bv_unsigned sp + OFS + -80) by (apply unsigned_lit; clear - SPR LO LO0 STK0 STKG OFS0; lia).
      assert (ALO : lo + 144 <= bv_unsigned sp + OFS - 80) by (clear - LO STKG; lia).
      (* [comment removed for export] *)
      assert (OIc : oinvK ΣX stX mc OWX boX NEW1 CX).
      { kit @oinv_munch; [exact OI| exact MU| exact WM| exact MIc| | constructor; [left; cbn [fst snd]; clear - ALO LO STK0 OFS0; lia| constructor]].
        stk_join STc FR STF (bv_unsigned sp + OFS). exact STF. }
      kitp @oinv_call OCc. pose proof (OCc _ _ _ _ _ _ _ OIc) as (HEAPc & _ & _ & _ & _ & _ & _ & CSc & _). clear OCc.
      assert (UW1 : uw_chain USTACK_TOP mc (bv_unsigned sp + OFS + -80) (bv_unsigned sp + OFS) (bv_unsigned ra :: ras)).
      { uw_call_mu_tac mX 80 UW MU FR; [intros a Ha; cbn [outside fst snd]; clear - Ha; lia | clear; lia | uchk_open; clear - SP16 OFS16; Z.div_mod_to_equations; lia | clear - TOP OFS0; unfold USTACK_TOP in *; lia]. }
      apply evt_done. cbn [abind apbind amalloc aret afree_opt afree option_map fst snd].
      eapply CRYPTO_malloc_walkAp with (n := n) (lo := lo) (OW := OWX) (LB := NEW1 ++ LB) (ras := bv_unsigned ra :: ras); rewrite ?E80.
      * exact HEAPc.
      * exact STc.
      * exact CEIL.
      * unfold CRYPTO_MALLOC_STACK, RT_STACK. clear - LO STKG. lia.
      * clear - TOP OFS0. unfold USTACK_TOP in *. lia.
      * uchk_open. clear - SP16 OFS16. Z.div_mod_to_equations. lia.
      * exact MIc.
      * reflexivity.
      * exact CSc.
      * reflexivity.
      * clear - GB. lia.
      * pose proof OIc as (PREc & _). pose proof PREc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CRc & _). clear - CRc CRn. lia.
      * rewrite ?ESP. exact UW1.
      * exact (uk_ctx_tail _ _ _ E_crea_tail (uk_ctx_call _ _ _ _ E_grow_crea CTX)).
      * intros pn ΣN msN NIp PON.
        destruct PON as (w0 & w1 & w2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & w3 & w4 & w5 & w6 & F3 & fc3 & mN & A & -> & MIN & STN & AGN & CRN & BRN & HEAPN & ACCN & (junkN & BLKN)).
        rewrite ?E80 in STN, AGN. rewrite (ret_pc_even 0x24b4c0) by (clear; lia).
        pose proof BRN as (BA0' & BA16' & _ & BAC' & BAI').
        assert (EA : bv_unsigned (Z_to_bv 64 A) = A) by (apply unsigned_lit; clear - BA0' BAC' CN3 GB; alia).
        pose proof (cb_len_a _ _ _ _ BLKN) as JL'.
        (* [comment removed for export] *)
        assert (CLs : forall a, bv_unsigned sp + OFS - 80 <= a < bv_unsigned sp + OFS -> aclient_addr (OWX ++ NEW1 ++ LB) (bv_unsigned sp + OFS + -80) a).
        { intros a Ha. left. clear - Ha TOP OFS0. unfold USTACK_TOP in *. lia. }
        assert (CLb : forall a, BUF <= a < BUF + 32 -> aclient_addr (OWX ++ NEW1 ++ LB) (bv_unsigned sp + OFS + -80) a).
        { intros a Ha. right; right. exists bB. split; [exact HbB3| clear - Ha BB1 BB2; lia]. }
        apply (rw_cells_agree _ _ _ _ _ AGN) in FR; [| intros xa Hxa; cbn in Hxa; apply CLs; clear - Hxa; lia].
        apply (rw_cells_agree _ _ _ _ _ AGN) in HLEN; [| intros xa Hxa; cbn in Hxa; apply CLb; clear - Hxa; lia].
        apply (rw_cells_agree _ _ _ _ _ AGN) in HDAT; [| intros xa Hxa; cbn in Hxa; apply CLb; clear - Hxa; lia].
        apply (rw_cells_agree _ _ _ _ _ AGN) in HMAX; [| intros xa Hxa; cbn in Hxa; apply CLb; clear - Hxa; lia].
        apply (rw_cells_agree _ _ _ _ _ AGN) in HFLG; [| intros xa Hxa; cbn in Hxa; apply CLb; clear - Hxa; lia].
        (* [comment removed for export] *)
        assert (OIN : oinvK ΣN stX mN OWX boX ((pn, A, n) :: NEW1) (CX - mcost n)).
        { kit @oinv_alloc; [exact OIc| | exact HEAPN| exact MIN| | exact CRN| split; [apply mcost_nonneg_a; clear - GB; lia| exact CRn]].
          - eapply agree_on_mono; [exact AGN|]. intros a [Ha|[Ha|Ha]]; [left; clear - Ha; lia| right; left; exact Ha| right; right; exact Ha].
          - stk_join STN FR STF (bv_unsigned sp + OFS). exact STF. }
        kitp @oinv_facts OFN. pose proof (OFN _ _ _ _ _ _ _ OIN) as (HEAPN' & NDN & BNDN & FRESHN & DJLN & DJON). clear OFN.
        pose proof (DJLN (pn, A, n) bB ltac:(left; reflexivity) HbB) as DJAB. cbn [blk_addr blk_size fst snd] in DJAB.
        assert (HbBF : In bB (OWX ++ ((pn, A, n) :: NEW1) ++ LB)) by (apply in_app_iff; right; apply in_app_iff; right; exact HbB).
        ablock HEAPN' HbBF ACCNB OFFNB.
        destruct (AH_shb _ _ _ _ HEAPN) as [SHBn1 SHBn2].
        pose proof (munch_refl [(bv_unsigned sp + OFS - 80, bv_unsigned sp + OFS); (BUF, BUF + 32)]%Z mN) as MUN. pose proof (wmono_refl ctasegs mN) as WMN.
        assert (OFFWN : offshW [(bv_unsigned sp + OFS - 80, bv_unsigned sp + OFS); (BUF, BUF + 32)]%Z) by (cbn [offshW]; clear - CEIL LO STK0 STKG C2 OFFB BB1 BB2; alia).
        rename MU into MU0. rename WM into WM0. clear OFFW.
        apply implAp_from_evt.
        (* [comment removed for export] *)
        unfold MallocRep.wz.   (* [comment removed for export] *)
        step. if_cases KA; zc KA; [| exfalso; revert KA; rewrite ?EA; clear - BA0'; lia]. clear KA.
        step. step. step. step. step.
        step. setreg 12%Z (Z_to_bv 64 len) ltac:(f_equal; rewrite ?unsigned_lit by (clear; lia); clear; lia). setreg 10%Z (Z_to_bv 64 A) ltac:(f_equal; clear; lia).
        step. name_mem m5.
        match goal with H : stk ctasegs m5 lo _ |- _ => rename H into ST5 end. match goal with H : mem_inv ctasegs m5 |- _ => rename H into MI5 end.
        match goal with H : munch _ mN m5 |- _ => rename H into MU5 end. match goal with H : wmono ctasegs mN m5 |- _ => rename H into WM5 end.
        assert (HEAP5 : AHEAP ΣN OWX (((pn, A, n) :: NEW1) ++ LB) m5).
        { eapply AH_frame; [exact HEAPN'| exact MU5| exact WM5|]. constructor; [left; cbn [fst snd]; clear - CEIL LO STK0 STKG OFS0 TOP; alia|].
          constructor; [right; right; exists bB; split; [apply in_app_iff; right; apply in_app_iff; right; exact HbB| cbn [fst snd]; clear - BB1 BB2; lia]| constructor]. }
        assert (OI5 : oinvK ΣN stX m5 OWX boX ((pn, A, n) :: NEW1) (CX - mcost n)).
        { kit @oinv_munch; [exact OIN| exact MU5| exact WM5| exact MI5| | constructor; [left; cbn [fst snd]; clear - ALO LO STK0 OFS0; lia| constructor; [right; left; exists (BUF, BUF + 32); split; [exact XBUF| cbn; clear; lia]| constructor]]].
          stk_join ST5 FR STF (bv_unsigned sp + OFS). exact STF. }
        (* [comment removed for export] *)
        replace (Z.to_nat n) with (Z.to_nat len + Z.to_nat (n - len))%nat in BLKN by (clear - GB LTL; lia).
        apply cb_split_a in BLKN. cut_hd BLKN HB2 (A + len). rename BLKN into HB3. clear HB2.
        apply evt_done. eapply implAp_step_same.
        { eapply (asan_memset_cpsA) with (d := A) (n := len) (c := z8) (bd := (pn, A, n)) (lo := lo) (OW := OWX) (LB := ((pn, A, n) :: NEW1) ++ LB);
            try reflexivity; rewrite ?E80.
          - exact HEAP5.
          - exact ST5.
          - exact CEIL.
          - unfold RT_STACK; clear - LO STKG; lia.
          - clear - TOP OFS0; unfold USTACK_TOP in *; lia.
          - uchk_open; clear - SP16 OFS16; Z.div_mod_to_equations; lia.
          - exact MI5.
          - apply in_app_iff; right; cbn; left; reflexivity.
          - cbn [blk_addr blk_size fst snd]. clear - GB LTL; lia.
          - clear - LTL LEN30; lia. }
        intros msM PO. unfold icall_post in PO. rewrite ?E80 in PO.
        destruct PO as (u0 & u1 & u2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & u3 & u4 & u5 & u6 & F6 & fc6 & m6 & -> & MI6 & ST6 & HEAP6 & WM6 & AG6 & BZ & WR6).
        rewrite (ret_pc_even 0x24b51c) by (clear; lia).
        assert (CL6 : forall a, (bv_unsigned sp + OFS - 80 <= a < bv_unsigned sp + OFS \/ BUF <= a < BUF + 32) ->
                      aclient_addr (OWX ++ ((pn, A, n) :: NEW1) ++ LB) (bv_unsigned sp + OFS + -80) a /\ ~ (A <= a < A + len)).
        { intros a [Ha|Ha].
          - split; [left; clear - Ha TOP OFS0; unfold USTACK_TOP in *; lia| clear - Ha BAC' CEIL LO STK0 STKG GB LTL; lia].
          - split; [right; right; exists bB; split; [exact HbBF| clear - Ha BB1 BB2; lia]| clear - Ha DJAB BB1 BB2 GB LTL; lia]. }
        apply (rw_cells_agree _ _ _ _ _ AG6) in FR; [| intros xa Hxa; cbn in Hxa; apply CL6; clear - Hxa; lia].
        apply (rw_cells_agree _ _ _ _ _ AG6) in HLEN; [| intros xa Hxa; cbn in Hxa; apply CL6; clear - Hxa; lia].
        apply (rw_cells_agree _ _ _ _ _ AG6) in HDAT; [| intros xa Hxa; cbn in Hxa; apply CL6; clear - Hxa; lia].
        apply (rw_cells_agree _ _ _ _ _ AG6) in HMAX; [| intros xa Hxa; cbn in Hxa; apply CL6; clear - Hxa; lia].
        apply (rw_cells_agree _ _ _ _ _ AG6) in HFLG; [| intros xa Hxa; cbn in Hxa; apply CL6; clear - Hxa; lia].
        apply (rw_cells_agree _ _ _ _ _ AG6) in HB3; [| intros xa Hxa; cbn in Hxa; split; [right; right; exists (pn, A, n); split; [apply in_app_iff; right; cbn; left; reflexivity| cbn; clear - Hxa GB LTL; lia]| clear - Hxa; lia]].
        assert (HZ : rw_cells ctasegs m6 A [CB (Z.to_nat len) (repeat z8 (Z.to_nat len))]).
        { pose proof (rw_cells_of_bytes_a m6 A _ BZ) as HZ0. rewrite repeat_length in HZ0. apply HZ0. rewrite Z2Nat.id by (clear - LTL; lia). exact WR6. }
        pose proof OIN as (_ & _ & _ & _ & _ & _ & _ & LBOKN). pose proof LBOKN as LBc. apply Forall_cons_iff in LBc as [OKa LBOK1].
        assert (OI6 : oinvK ΣN stX m6 OWX boX ((pn, A, n) :: NEW1) (CX - mcost n - 0)).
        { kit @oinv_heap; [exact OI5| | intros b' [Hb'|Hb']; apply in_app_iff; [left; exact Hb'| right; exact Hb']| exact HEAP6| exact LBOKN| exact MI6| | clear; lia| clear - CRn CRX; pose proof (mcost_nonneg_a n); lia].
          - eapply agree_on_mono; [exact AG6|]. intros a [Ha HXa]. split.
            + destruct Ha as [Ha|[Ha|(b' & Hb' & Hr')]]; [left; clear - Ha; lia| right; left; exact Ha| right; right; exists b'; split; [| exact Hr']].
              apply in_app_iff in Hb'. apply in_app_iff. destruct Hb' as [Hb'|Hb']; [left; exact Hb'| right; apply in_app_iff; right; exact Hb'].
            + destruct Ha as [Ha|[Ha|(b' & Hb' & Hr')]]; [clear - Ha BAC' CEIL STK0 LO GB LTL; lia| intros Hx; exact (ApErrKitA2.blk_not_static _ _ _ _ (pn, A, n) a HEAP6 ltac:(apply in_app_iff; right; cbn; left; reflexivity) ltac:(cbn; clear - Hx GB LTL; lia) Ha)|].
              apply in_app_iff in Hb'. destruct Hb' as [Hb'|Hb'].
              -- pose proof (DJON (pn, A, n) b' ltac:(left; reflexivity) Hb') as DJ. cbn [blk_addr blk_size fst snd] in DJ. clear - DJ Hr' GB LTL. lia.
              -- pose proof (DJLN (pn, A, n) b' ltac:(left; reflexivity) Hb') as DJ. cbn [blk_addr blk_size fst snd] in DJ. clear - DJ Hr' GB LTL. lia.
          - stk_join ST6 FR STF (bv_unsigned sp + OFS). exact STF. }
        replace (CX - mcost n - 0) with (CX - mcost n) in OI6 by (clear; lia).
        kitp @oinv_facts OF6. pose proof (OF6 _ _ _ _ _ _ _ OI6) as (HEAP6' & _). clear OF6.
        ablock HEAP6 HbBF ACC6 OFF6.
        pose proof (munch_refl [(bv_unsigned sp + OFS - 80, bv_unsigned sp + OFS); (BUF, BUF + 32)]%Z m6) as MU6. pose proof (wmono_refl ctasegs m6) as WM6'.
        assert (OFFW6 : offshW [(bv_unsigned sp + OFS - 80, bv_unsigned sp + OFS); (BUF, BUF + 32)]%Z) by (cbn [offshW]; clear - CEIL LO STK0 STKG C2 OFF6 BB1 BB2; alia).   (* [comment removed for export] *)
        rename MU5 into MU5o. rename WM5 into WM5o.
        apply implAp_from_evt.
        (* [comment removed for export] *)
        step. step. do 9 step. release_frame FR ST6 (bv_unsigned sp + OFS). step. step.
        name_mem m9.
        match goal with H : stk ctasegs m9 lo _ |- _ => rename H into ST9 end. match goal with H : mem_inv ctasegs m9 |- _ => rename H into MI9 end.
        match goal with H : munch _ m6 m9 |- _ => rename H into MU9 end. match goal with H : wmono ctasegs m6 m9 |- _ => rename H into WM9 end.
        apply evt_done. cbn [aret]. apply implAp_ret.
        (* [comment removed for export] *)
        join2 HZ HB3. apply cb_join_a in HZ.
        assert (HB1 : rw_cells ctasegs m9 A [CB (Z.to_nat 0) (firstn (Z.to_nat 0) bytes); CB (Z.to_nat (n - 0)) (repeat z8 (Z.to_nat len) ++ drop (Z.to_nat len) junkN)]).
        { eapply rw_cells_recast; [exact HZ| cbn; rewrite length_app, repeat_length, length_drop, JL'; repeat split; clear - GB LTL; lia| reflexivity| cbn; clear - GB LTL; lia]. }
        join2 HLEN HDAT. join2 HLEN HMAX. join2 HLEN HFLG.
        unfold grow_postA. cbn [fst snd]. unfold grow_costA, grow_capA, bm_max; cbn [bm_len bm_data bm_bytes]. replace (len <=? 0) with false by (symmetry; apply Z.leb_gt; exact LTL).
        eexists u0, u1, u2, _, _, _, _, _, _, _, u3, u4, u5, u6, F6, fc6, m9, OWX, pn, A, n, _.
        split; [reflexivity|]. split; [reflexivity|]. split; [subst n; reflexivity|].
        split. { kit @oinv_munch; [exact OI6| exact MU9| exact WM9| exact MI9| exact ST9|].
                 constructor; [left; cbn [fst snd]; clear - ALO LO STK0 OFS0; lia|]. constructor; [right; left; exists (BUF, BUF + 32); split; [exact XBUF| cbn; clear; lia]| constructor]. }
        split; [intros bb Hbb; exact Hbb|].
        split; [exact HLEN|]. split; [exact HB1|].
        split; [clear - GB; lia|]. split; [clear - GB; lia|]. split; [exact BA0'|]. split; [exact BA16'|]. split; [exact BAC'|]. split; [subst n; reflexivity|].
        (* [comment removed for export] *)
        assert (XCL : forall a, ax_client (NEW1 ++ LB) (bv_unsigned sp + OFS) ([(BUF, BUF + 32)] ++ LIBW_A) a ->
                  outside [(bv_unsigned sp + OFS - 144, bv_unsigned sp + OFS); (BUF, BUF + 32)]%Z a
                  /\ aclient_addr (OWX ++ NEW1 ++ LB) (bv_unsigned sp + OFS + -80) a /\ ~ (A <= a < A + n)).
        { intros a [HX Ha]. assert (NB : ~ (BUF <= a < BUF + 32)) by (intros Hx; apply HX; cbn [rin_ivs fst snd app]; left; exact Hx).
          destruct Ha as [Ha|[Ha|(b' & Hb' & Hr')]].
          - cbn [outside fst snd]. split; [clear - Ha NB; lia|]. split; [left; clear - Ha; lia|]. clear - Ha BAC' CEIL LO STK0 ALO. lia.
          - pose proof (client_static_below a Ha) as Hlow. cbn [outside fst snd]. split; [clear - Hlow CN1 CEIL ALO NB; lia|]. split; [right; left; exact Ha|].
            intros Hx. exact (ApErrKitA2.blk_not_static _ _ _ _ (pn, A, n) a HEAPN ltac:(left; reflexivity) ltac:(cbn; exact Hx) Ha).
          - assert (Hb3 : In b' (OWX ++ NEW1 ++ LB)) by (apply in_app_iff; right; exact Hb').
            pose proof (BND b' Hb3) as (_ & _ & Hc' & _).
            cbn [outside fst snd]. split; [clear - Hr' Hc' CEIL ALO NB; lia|]. split; [right; right; exists b'; split; [exact Hb3| exact Hr']|].
            assert (NE1 : blk_id (pn, A, n) <> blk_id b') by (cbn; intros Ei; apply NIp; rewrite Ei, map_app; apply in_app_iff; right; exact (in_map blk_id _ _ Hb')).
            pose proof (AH_disjoint_gen _ _ _ _ (pn, A, n) b' HEAPN ltac:(left; reflexivity) ltac:(apply in_app_iff; right; exact Hb') NE1) as DJ.
            cbn [blk_addr blk_size fst snd] in DJ. clear - DJ Hr'. lia. }
        intros a HXa Hc. destruct (XCL a Hc) as (O1 & C1' & NA). cbn [outside fst snd] in O1. destruct O1 as (O1 & O2 & _).
        assert (C2' : aclient_addr (OWX ++ ((pn, A, n) :: NEW1) ++ LB) (bv_unsigned sp + OFS + -80) a).
        { destruct C1' as [H|[H|(b' & Hb' & Hr')]]; [left; exact H| right; left; exact H| right; right; exists b'; split; [| exact Hr']].
          apply in_app_iff in Hb'. apply in_app_iff. destruct Hb' as [Hb'|Hb']; [left; exact Hb'| right; right; exact Hb']. }
        rewrite (agree_on_of_munch_nw _ _ _ MU9 a HXa ltac:(cbn [outside fst snd]; split; [clear - O1; lia| split; [exact O2| exact I]])).
        rewrite (AG6 a HXa ltac:(split; [exact C2'| clear - NA GB LTL; lia])).
        rewrite (agree_on_of_munch_nw _ _ _ MU5o a HXa ltac:(cbn [outside fst snd]; split; [clear - O1; lia| split; [exact O2| exact I]])).
        rewrite (AGN a HXa C1').
        rewrite (agree_on_of_munch_nw _ _ _ MU0 a HXa ltac:(cbn [outside fst snd]; split; [exact O1| exact I])).
        reflexivity.
  Qed.
  (* [comment removed for export] *)
  Goal True. idtac "Assumptions of BUF_MEM_grow_clean_walkA:". Print Assumptions BUF_MEM_grow_clean_walkA. exact I. Qed.
End Act.
End WithRT.
