(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BW_0Gc.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From Stdlib Require Import FMapPositive.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BImage BZBridge BSysStep BSFModel BellsX BArr BacX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BReach BAllocSim BMmapSim BazyRestrict BazyLedger BazySR BazyNodes BothAllocModel.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BllocWf BllocKit BllocBudget BllocRep BllocRepFacts BllocRepFacts2 BllocRepX BsDepotInv BW_DepotFrame BllocWalkKit BW_LargeAlloc1 BW_PoisonRemap1 BecLazy BecLazy2 BS_PoisonRemap BS_SecRecycle1 BS_SecRecycle2 BS_SecRecycle BG_WFHit BG_Malloc BG_Malloc2 BG_MallocModel BG_MallocLarge2 BG_RepQ BG_RepQFacts BG_RepQFacts2 BG_RecycleModel BG_WriteSet BG_RecycleDefs BG_RecycleSecModel BG_RecycleSec1 BG_RecycleSec2.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Lemma map_has_of_In : forall (l : list (word * word)) (lo n : word), In (lo, n) l -> map_has l lo n = true.
Proof.
  intros l lo n H. unfold map_has. apply existsb_exists. exists (lo, n). split; [exact H|]. cbn [fst snd].
  rewrite !bv_eqb_refl. reflexivity.
Qed.

Lemma secondary_needed : forall n, 0 <= n -> rq_primary (compute_req n) = false -> kMaxSize + 2048 < rq_needed (compute_req n).
Proof.
  intros n Hn H. pose proof (secondary_rz n H) as RZ. pose proof (compute_req_facts n Hn) as (_ & _ & _ & _ & RN & _). cbv zeta in RN.
  rewrite H, RZ in RN.
  assert (P : rq_primary (compute_req n) = (rq_rounded (compute_req n) + rq_rz (compute_req n) <=? kMaxSize)) by reflexivity.
  rewrite H, RZ in P. symmetry in P. apply Z.leb_gt in P. lia.
Qed.

Section HCW.
  Context {HCEIL : HeapCeil}.

Section PreCells.
  Variables (s : ast) (XC XB : list Z) (m : mem).
  Hypothesis RQ : AREPQ s XC XB m.
  Let st := a_st s.

  Lemma senv_of_arepq : SENV (wz ATP) ATSD (a_ctx s) (a_thr s) m.
  Proof.
    destruct RQ as (PL & WQ & INST & FL & THR & _).
    destruct FL as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & F17 & F18 & F19 & F20 & F21 & F22 & F23 & F24 & F25 & F26 & F27).
    destruct THR as (T1 & T2 & T2b & _).
    unfold AFLAGS, ACFLAGS, ASHBASE_CELL, ASHADOW_BASE, AHIGHMEMEND, ACANPOISON, ATSDINIT, AREALMEMSET, AMEMSET, AGOT_LO, APAGESZ, ASECNAME, ATLSSLOT, ATSD in *.
    constructor; try assumption; unfold wz, ATP; rewrite ?unsigned_lit by lia; assumption.
  Qed.
  Lemma renv_of_arepqx : flagsx_rep m -> exists g b, RENV g b m.
  Proof.
    intros (X1 & X2 & [g X3] & X4 & [b X5]). destruct RQ as (PL & WQ & INST & FL & _).
    destruct FL as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & F17 & F18 & F19 & F20 & F21 & F22 & F23 & F24 & F25 & F26 & F27).
    exists g, b. unfold AFLAGS, ACFLAGS, ASHBASE_CELL, ASHADOW_BASE, AHIGHMEMEND, AREALMEMSET, AMEMSET, AGOT_LO, APAGESZ, ALIBCPGSZ, AGOT_SSP, ASSPGUARD in *.
    constructor; try assumption.
  Qed.
  Lemma large_cells_of_arepq :
       rw_cells asegs m (AINST + 32) [C8 (wz (a_sb s))]
    /\ rw_cells asegs m (AINST + 64) [C8 (wz 4096); C8 (wz (a_pa s)); C8 (wz (a_pa s))]
    /\ rw_cells asegs m (AINST + 112) [C8 (wz (as_n_reserved st)); C8 (wz (zlen (as_sec st))); C8 (wz 0)]
    /\ stk asegs m (AINST + 136) (AINST + 680)
    /\ rw_cells asegs m (AINST + 680) [C8 (wz 0)]
    /\ stk asegs m (AINST + 688) (AINST + 728)
    /\ stk asegs m (a_thr s + 2800) (a_thr s + 3168)
    /\ u64arr asegs m (a_pa s) (wlist (map sc_map_beg (as_sec st))).
  Proof.
    destruct RQ as (PL & WQ & INST & FL & THR & SEC & _).
    destruct INST as (A1 & J1 & A2 & J2 & A3 & J3 & J4 & _).
    destruct THR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Jst & Tunw).
    destruct SEC as (U & J & _).
    pose proof WQ as W'. destruct W' as (_ & _ & _ & _ & _ & _ & Wn & Wr & _).
    pose proof PL as (S1 & S2 & S3 & P1 & P2 & P3 & T1 & T2 & T3 & _).
    apply akobj_env in T2; [| unfold kPageSize; clear; lia]. apply aapp_env in P2; [| unfold kPtrArrayReserve; clear; lia].
    assert (NN : 0 <= zlen (as_sec (a_st s))) by (unfold zlen; lia).
    unfold OI_SPACEBEG, OI_NRESERVED, OI_SECMUTEX, OI_GSTATS, OI_Q, OT_STATS, OT_UNWINDING, AINST in *.
    acb. unfold AHI_LO, kPtrArrayReserve, kPageSize, kChunksBlockCount in *. unfold st.
    pose proof A1 as A0.
    apply (rw_cells_app asegs _ _ [C8 (wz (a_sb s))] [C4 (wz 4294967295); C4 (wz 0); C8 (wz (a_ri s)); C8 (wz 0); C8 (wz 4096); C8 (wz (a_pa s)); C8 (wz (a_pa s)); C8 (wz 8388608)]) in A0.
    destruct A0 as [A0 _].
    apply (rw_cells_app asegs _ _ [C8 (wz (a_sb s)); C4 (wz 4294967295); C4 (wz 0); C8 (wz (a_ri s)); C8 (wz 0)] [C8 (wz 4096); C8 (wz (a_pa s)); C8 (wz (a_pa s)); C8 (wz 8388608)]) in A1.
    destruct A1 as [_ A1]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in A1.
    apply (rw_cells_app asegs _ _ [C8 (wz 4096); C8 (wz (a_pa s)); C8 (wz (a_pa s))] [C8 (wz 8388608)]) in A1. destruct A1 as [A1 _].
    replace (1628632 + 32 + 32) with (1628632 + 64) in A1 by lia.
    split; [exact A0|]. split; [exact A1|]. split; [exact A2|].
    split; [pose proof (junk_stk' _ _ _ J2 ltac:(lia) ltac:(lia) ltac:(lia)) as K; replace (1628632 + 136 + (680 - 136)) with (1628632 + 680) in K by lia; exact K|].
    split; [exact A3|].
    split; [pose proof (junk_stk' _ _ _ J3 ltac:(lia) ltac:(lia) ltac:(lia)) as K; replace (1628632 + 688 + (728 - 688)) with (1628632 + 728) in K by lia; exact K|].
    split; [pose proof (junk_stk' _ _ _ Jst ltac:(lia) ltac:(lia) ltac:(lia)) as K; replace (a_thr s + 2800 + (3168 - 2800)) with (a_thr s + 3168) in K by lia; exact K|].
    exact U.
  Qed.
End PreCells.

Section RSStep.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (msF : machine_state) (mo : Model) (Q : config -> Prop).
  Variables (s : ast) (XC XB : list Z) (ch : chunk) (d : depot) (lo cb : Z).
  Let st := a_st s.
  Let mch := ch_chunk_beg ch.

  Hypothesis RQ : AREPQ s (mch :: XC) XB m.
  Hypothesis CHIN : In ch (chunk_list st).
  Hypothesis SEC : ch_primary ch = false.
  Hypothesis QUAR : ch_state ch = CQuarantine.
  Hypothesis INIT : as_cache_inited st = true.
  Hypothesis AX : awin_vis s m /\ flagsx_rep m.
  Hypothesis AMX : AMODELX s mo.
  Hypothesis DEP : DEPOT asegs d m.
  Hypothesis DPL : depot_placed s d.
  Hypothesis DCOV : depot_cov d mo.
  Hypothesis MI : mem_inv asegs m.
  Hypothesis LO : aceil <= lo.
  Hypothesis HI : lo + 800 <= bv_unsigned sp.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis TP : bv_unsigned tp = ATP.
  Hypothesis OK : lzok asegs (a_L s) (a_S s) (a_Zr s) (mkCfg msF mo).
  Hypothesis VISE : restrict (a_L s) (a_S s) msF
                    = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz cb) (wz mch) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 0x947ac) fc None m (seg_rom asegs).

  Definition rs_model_clause (stX : astate) : Prop :=
    forall stA, same_but_shadow stA st -> exists stA' ev, cb_recycle stA mch = Some (stA', ev) /\ same_but_shadow stA' stX.
  Definition rs_gpost : machine_state -> Model -> Prop :=
    rstep_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s d lo m mo XC XB XB rs_model_clause.

  Section At.
    Variables (idx : nat) (h lsth : schunk).
    Hypothesis HIDX : nth_error (as_sec st) idx = Some h.
    Hypothesis HMAP : sc_map_beg h = sec_map_beg ch.
    Hypothesis HLAST : nth_error (as_sec st) (length (as_sec st) - 1)%nat = Some lsth.
    Let T := a_thr s.
    Let CTX := a_ctx s.
    Let sb := a_sb s.
    Let pa := a_pa s.
    Let nch := zlen (as_sec st).
    Let nres := as_n_reserved st.
    Let U := ch_user_beg ch.
    Let a := sc_map_beg h.
    Let msz := sc_map_size h.
    Let lst := sc_map_beg lsth.
    Let chunks := List.map sc_map_beg (as_sec st).
    Let l1 := secdel_l1 (as_sec st) idx.
    Let st2 := remove_map (set_sec (del_state st ch) nres l1) a.
    Let L2 := rs_L (a_L s) a msz.
    Let sN := mkAst st2 T CTX (a_fsb s) L2 (a_S s) (a_Zr s) (a_AL s) (a_top s) (a_bot s).

    Let PL : placed_ok s. Proof. exact (AREPQ_placed _ _ _ _ RQ). Qed.
    Let WQ : WFQ st (mch :: XC) XB. Proof. exact (AREPQ_WFQ _ _ _ _ RQ). Qed.
    Let MEM : ARmem s m. Proof. exact (AREPQ_mem _ _ _ _ RQ). Qed.
    Let SND : List.NoDup (List.map sc_map_beg (as_sec st)). Proof. pose proof WQ as WW. destruct WW as (_ & _ & _ & _ & _ & W6 & _). exact W6. Qed.
    Let HIN : In h (as_sec st). Proof. eapply nth_error_In. exact HIDX. Qed.
    Let LIN : In lsth (as_sec st). Proof. eapply nth_error_In. exact HLAST. Qed.
    Ltac placed := pose proof PL as (S1 & S2 & S3 & P1 & P2 & P3 & T1 & T2 & T3 & X1 & X2 & X3 & D1 & D2 & D3 & D4 & D5 & F1 & F2 & D6 & D7 & D8 & D9 & SECP & SEC2 & TCX).

    Let ENT : sc_map_beg h = a /\ sc_size h = rq_needed (compute_req (ch_used ch)) /\ msz = round_up (sc_size h) kPageSize + kPageSize
              /\ find_sec_idx (as_sec st) a 0%nat = Some idx /\ rq_primary (compute_req (ch_used ch)) = false /\ in_primary st (ch_alloc_beg ch) = false
              /\ ch_rz ch = 2048 /\ U = ch_alloc_beg ch + 2048 /\ mch = ch_alloc_beg ch + 2032 /\ ch_alloc_beg ch = a + kPageSize
              /\ ch_lo ch = a /\ ch_end ch = a + msz /\ 1 <= ch_used ch.
    Proof. eapply rs_ent; eassumption. Qed.
    Let BND : aceil <= lo /\ 4096 <= T /\ T + 4096 <= aceil /\ 0x10007fff8000 <= sb /\ sb + 137438953472 + 4096 <= aceil
              /\ 7241728 <= CTX /\ CTX + 160 <= aceil /\ 7241728 <= pa /\ pa + 8388608 <= aceil
              /\ 7241728 <= d_nb d /\ d_nb d + 16 * 65536 <= aceil /\ 7241728 <= d_sb d /\ d_sb d + 8 * 32768 <= aceil
              /\ 7241728 <= a /\ a + msz <= aceil /\ 8192 <= msz /\ 2148356096 <= sh a /\ sh a + msz / 8 <= sh aceil
              /\ 1 <= nch <= nres /\ nres <= 16384 /\ 7241728 <= a_fsb s /\ a_fsb s + AFS_SIZE <= aceil
              /\ a mod 4096 = 0 /\ msz mod 4096 = 0 /\ (idx < length (as_sec st))%nat /\ 7241728 <= lst /\ lst + 8192 <= aceil /\ lst mod 4096 = 0.
    Proof. eapply rs_bnd; eassumption. Qed.
    Let BANDS : hidden ((T + 4096 <= 65536 \/ (7241728 <= T /\ T + 4096 <= 2147446784) \/ 17594333495296 <= T)
                     /\ (CTX + 160 <= 2147446784 \/ 17594333495296 <= CTX)
                     /\ (pa + 8388608 <= 2147446784 \/ 17594333495296 <= pa)
                     /\ (d_nb d + 16 * 65536 <= 2147446784 \/ 17594333495296 <= d_nb d)
                     /\ (d_sb d + 8 * 32768 <= 2147446784 \/ 17594333495296 <= d_sb d)
                     /\ (a + msz <= 2147446784 \/ 17594333495296 <= a)
                     /\ (sh a + msz / 8 <= 2415881728 \/ 2201439137792 <= sh a)
                     /\ (a_fsb s + AFS_SIZE <= 2147446784 \/ 17594333495296 <= a_fsb s)
                     /\ (lst + 8192 <= 2147446784 \/ 17594333495296 <= lst)).
    Proof. eapply rs_bands; eassumption. Qed.
    Tactic Notation "bands_as" simple_intropattern(p) := (let X := fresh "BX" in pose proof BANDS as X; destruct X as [p]).
    Let PNEW : disj a msz sb (kSpaceSize + kPageSize) /\ disj a msz pa kPtrArrayReserve /\ disj a msz T kPageSize /\ disj a msz CTX 160
              /\ disj a msz (a_fsb s) AFS_SIZE /\ disj a msz (d_nb d) (16 * 65536) /\ disj a msz (d_sb d) (8 * 32768)
              /\ (forall sc, In sc (as_sec st) -> sc_map_beg sc <> a -> disj a msz (sc_map_beg sc) (sc_map_size sc)).
    Proof. eapply rs_pnew; eassumption. Qed.
    Let L1IN : forall y, In y l1 <-> In y (as_sec st) /\ sc_map_beg y <> a.
    Proof. eapply rs_l1in; eassumption. Qed.

    Ltac post L := first [ eapply L with (idx := idx) (h := h) (lsth := lsth) (spv := bv_unsigned sp)
                         | eapply L with (idx := idx) (h := h) (lsth := lsth)
                         | eapply L with (idx := idx) (h := h) ]; eassumption.

    Lemma recycle_sec_arepq_at :
      (forall msF' mo', rs_gpost msF' mo' -> sreach asegs Q (mkCfg msF' mo')) -> sreach asegs Q (mkCfg msF mo).
    Proof.
      intros K. pose proof BND as B. pose proof ENT as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13).
      pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
      destruct AX as [AWV FXR]. pose proof AMX as AMX'. destruct AMX' as [AM AK]. pose proof AM as AM'. destruct AM' as (AIL & ASV & AB0).
      destruct AIL as (IL1 & IL2 & IL3 & NOV & NW & NWA).
      pose proof AK as AK'. destruct AK' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & K10 & _). destruct K10 as (_ & _ & K10c).
      placed. pose proof (SECP h HIN) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9). pose proof (SECP lsth LIN) as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9).
      fold a msz in Q1, Q2, Q3, Q4, Q5, Q6, Q7, Q8, Q9. fold lst in R1, R2, R3, R4, R5, R6, R7, R8, R9.
      fold T CTX sb pa in S1, S2, S3, P1, P2, P3, T1, T2, T3, X1, X2, X3, D1, D2, D3, D4, D5, TCX, Q5, Q6, Q7, Q8, R5, R6, R7, R8.
      destruct PNEW as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8).

      assert (MSZ : 0x11000 <= msz < 2 ^ 40).
      { pose proof (secondary_needed (ch_used ch) ltac:(clear - E13; lia) E5) as ND. rewrite <- E2 in ND. pose proof (K10c h HIN) as KS. fold msz in KS.
        rewrite E3. rewrite E3 in KS. unfold ASECMAX in KS. unfold round_up, kPageSize, kMaxSize in *. clear - ND KS. Z.div_mod_to_equations. lia. }

      destruct (large_cells_of_arepq s _ _ m RQ) as (SB32 & INST64 & NRES & SST & MTX & GST & TST & PA).
      pose proof (senv_of_arepq s _ _ m RQ) as SEN. destruct (renv_of_arepqx s _ _ m RQ FXR) as (g & b244 & REN).
      pose proof MEM as (_ & _ & _ & SECR & _ & _ & CHR & _). destruct SECR as (_ & _ & SHDR).
      pose proof (SHDR idx h HIDX) as [HDR _]. pose proof (SHDR _ lsth HLAST) as [LHDR _]. fold a msz in HDR. fold lst in LHDR.
      pose proof (CHR ch CHIN) as CR. destruct CR as ((b1 & actx & HD & Hb1 & Hb1') & LC & STQ & JR & PL' & PR' & PH'). rewrite QUAR in HD, STQ. destruct STQ as [JU SHU].
      rewrite SEC in PH'. fold U in HD, JU, SHU, JR, PR'.
      assert (LEN : length chunks = length (as_sec st)) by (unfold chunks; apply length_map).
      assert (ZL : zlen chunks = nch) by (unfold zlen, nch, zlen; rewrite LEN; reflexivity).
      assert (NCHL : Z.of_nat (length (as_sec st)) = nch) by reflexivity.
      assert (LTI : (idx < length (as_sec st))%nat) by (clear - B; tauto).

      assert (APART : forall sc, In sc (as_sec st) -> sc_map_beg sc <> a -> a + msz <= sc_map_beg sc \/ sc_map_beg sc + sc_map_size sc <= a).
      { intros sc Hin NE. pose proof (N8 sc Hin NE) as D. unfold disj in D. exact D. }

      pose proof (compute_req_facts (ch_used ch) ltac:(clear - E13; lia)) as (_ & _ & RR & RR8 & RN & _). cbv zeta in RR, RR8, RN. rewrite E5, (secondary_rz _ E5) in RN.
      assert (MSZU : msz = round_up (rq_rounded (compute_req (ch_used ch)) + 4096) 4096 + 4096) by (rewrite E3, E2, RN; unfold kPageSize; f_equal; f_equal; clear; lia).
      set (rd := rq_rounded (compute_req (ch_used ch))) in *.

      assert (SHDX : exists sbs, u8arr asegs m (sh a) sbs /\ Z.of_nat (length sbs) = msz / 8).
      { destruct PH' as (_ & _ & PH). destruct PL' as (_ & _ & PLz). destruct SHU as (_ & _ & SHUz). destruct PR' as (_ & _ & PRz).
        unfold poison_bytes in *. rewrite E10 in PH. replace (a + kPageSize - kPageSize) with a in PH by (clear; lia).
        exists (repeat (b8 kAsanHeapLeftRedzoneMagic) 512 ++ repeat (b8 kAsanHeapLeftRedzoneMagic) (Z.to_nat (ch_rz ch / 8))
                ++ repeat (b8 kAsanHeapFreeMagic) (Z.to_nat (nsh (ch_used ch)))
                ++ repeat (b8 kAsanHeapLeftRedzoneMagic) (Z.to_nat ((ch_end ch - (U + round_up (ch_used ch) 8)) / 8))).
        assert (A8 : a mod 8 = 0) by (clear - B; Z.div_mod_to_equations; lia).
        split.
        - apply (proj2 (u8arr_app2 m _ _ _)). split; [exact PH|]. rewrite repeat_length.
          replace (sh a + Z.of_nat 512) with (sh (ch_alloc_beg ch)) by (rewrite E10; unfold sh, kPageSize; clear - A8; Z.div_mod_to_equations; lia).
          apply (proj2 (u8arr_app2 m _ _ _)). split; [exact PLz|]. rewrite repeat_length.
          replace (sh (ch_alloc_beg ch) + Z.of_nat (Z.to_nat (ch_rz ch / 8))) with (sh U) by (rewrite E8, E7, E10; unfold sh, kPageSize; clear - A8; Z.div_mod_to_equations; lia).
          apply (proj2 (u8arr_app2 m _ _ _)). split; [exact SHUz|]. rewrite repeat_length.
          replace (sh U + Z.of_nat (Z.to_nat (nsh (ch_used ch)))) with (sh (U + round_up (ch_used ch) 8))
            by (rewrite E8, E10; unfold sh, nsh, round_up, kPageSize; clear - A8 E13; Z.div_mod_to_equations; lia).
          exact PRz.
        - rewrite !length_app, !repeat_length. rewrite E12, E8, E7, E10. rewrite MSZU. unfold nsh, round_up, kPageSize. clear - RR RR8 E13 A8. Z.div_mod_to_equations. lia. }
      destruct SHDX as (sbs & SHD & SHDL).

      assert (hSPA : hidden (bv_unsigned sp mod 16 = 0)) by (constructor; exact SPA).
      assert (hAR : aapp a msz /\ a + msz <= aceil /\ a mod 4096 = 0 /\ msz mod 4096 = 0 /\ 0x11000 <= msz < 2^40).
      { split; [exact Q2|]. split; [exact Q3|]. split; [clear - B; tauto|]. split; [clear - B; tauto| exact MSZ]. }
      assert (hSBX : hidden (a + msz <= sb \/ sb + kSpaceSize <= a)).
      { constructor. unfold disj, kSpaceSize, kPageSize in *. clear - N1. lia. }
      assert (hSBR : hidden (AHI_LO <= sb /\ sb + kSpaceSize <= aceil)).
      { constructor. unfold kSpaceSize, kPageSize in *. clear - S2 S3. lia. }
      assert (hTPR : hidden (6762376 <= bv_unsigned tp /\ bv_unsigned tp + 4096 <= AIMG_TOP)).
      { constructor. rewrite TP. unfold ATP, AIMG_TOP. clear. lia. }
      assert (hRNG : hidden (6762288 <= ATSD /\ ATSD + 8 <= AIMG_TOP /\ aapp CTX 160 /\ CTX + 160 <= aceil /\ akobj T 4096 /\ T + 4096 <= aceil /\ T mod 16 = 0)).
      { constructor. unfold ATSD, AIMG_TOP. unfold kPageSize in T1, T2, T3.
        split; [clear; lia|]. split; [clear; lia|]. split; [exact X2|]. split; [exact X3|]. split; [exact T2|]. split; [exact T3|].
        clear - T1. Z.div_mod_to_equations. lia. }
      assert (hPLC : hidden ((CTX + 160 <= T \/ T + 4096 <= CTX) /\ (pa + kPtrArrayReserve <= T \/ T + 4096 <= pa) /\ (pa + kPtrArrayReserve <= CTX \/ CTX + 160 <= pa)
                        /\ (a + msz <= T \/ T + 4096 <= a) /\ (a + msz <= CTX \/ CTX + 160 <= a) /\ (a + msz <= pa \/ pa + kPtrArrayReserve <= a))).
      { constructor. destruct TCX as (TCX & _). unfold disj, kPageSize in *. clear - TCX D4 D5 N2 N3 N4. repeat split; lia. }
      assert (hPAR : aapp pa kPtrArrayReserve /\ pa + kPtrArrayReserve <= aceil /\ pa mod 4096 = 0).
      { split; [exact P2|]. split; [exact P3|]. unfold kPageSize in P1. exact P1. }
      assert (hNCH : zlen chunks = nch /\ 0 <= Z.of_nat idx < nch /\ nch <= nres <= 2^20).
      { split; [exact ZL|]. clear - B LTI NCHL. lia. }
      assert (hIDX : nth_error chunks (Z.to_nat (Z.of_nat idx)) = Some a).
      { rewrite Nat2Z.id. unfold chunks. rewrite nth_error_map, HIDX. reflexivity. }
      assert (hLNTH : nth_error chunks (Z.to_nat (nch - 1)) = Some lst).
      { replace (Z.to_nat (nch - 1)) with (length (as_sec st) - 1)%nat by (clear - NCHL LTI; lia). unfold chunks. rewrite nth_error_map, HLAST. reflexivity. }
      assert (hLR : aapp lst 4096 /\ lst + 4096 <= aceil).
      { unfold kPageSize in R4. split; [eapply aapp_sub; [exact R2| clear; lia| clear - R4; lia]| clear - R3 R4; lia]. }
      assert (NELAST : Z.of_nat idx < nch - 1 -> lst <> a).
      { intros LTn E. assert (EI : idx = (length (as_sec st) - 1)%nat); [| clear - EI LTn NCHL; lia].
        apply (proj1 (NoDup_nth_error (List.map sc_map_beg (as_sec st))) SND idx (length (as_sec st) - 1)%nat); [rewrite length_map; exact LTI|].
        rewrite !nth_error_map, HIDX, HLAST. cbn. fold a lst. rewrite E. reflexivity. }
      assert (hPLCL : Z.of_nat idx < nch - 1 -> hidden ((a + msz <= lst \/ lst + 4096 <= a) /\ (lst + 4096 <= pa \/ pa + kPtrArrayReserve <= lst) /\ (lst + 4096 <= T \/ T + 4096 <= lst) /\ (lst + 4096 <= CTX \/ CTX + 160 <= lst))).
      { intros LTn. constructor. pose proof (APART lsth LIN (NELAST LTn)) as D. fold lst in D. unfold disj, kPageSize in *. clear - D R4 R6 R7 R8. repeat split; lia. }
      assert (hLSTA : Z.of_nat idx = nch - 1 -> lst = a).
      { intros E. assert (EI : idx = (length (as_sec st) - 1)%nat) by (clear - E NCHL LTI; lia). rewrite <- EI in HLAST. rewrite HIDX in HLAST. injection HLAST as <-. reflexivity. }
      assert (hDISJ : Forall (fun c => 0 <= c < 2^47 /\ (c <= a + 6128 -> c <= a)) chunks).
      { apply Forall_forall. intros c Hc. unfold chunks in Hc. apply in_map_iff in Hc as (sc & <- & Hin).
        pose proof (SECP sc Hin) as (_ & G2 & G3 & G4 & _). apply aapp_env in G2; [| unfold kPageSize in G4; clear - G4; lia].
        split; [clear - G2 G3 G4; unfold kPageSize in *; acb; lia|]. intros LE.
        destruct (Z.eq_dec (sc_map_beg sc) a) as [E|NE]; [clear - E; lia|]. pose proof (APART sc Hin NE) as D. unfold kPageSize in G4. clear - D LE G4 B. lia. }

      assert (hSEN : SENV tp ATSD CTX T m).
      { replace tp with (wz ATP); [exact SEN| unfold wz; rewrite <- TP; apply Z_to_bv_bv_unsigned]. }
      assert (hLSTC : Z.of_nat idx < nch - 1 -> rw_cells asegs m (lst + 24) [C8 (wz (nch - 1))]).
      { intros _. apply (rw_cells_app asegs _ _ [C8 (wz lst); C8 (wz (sc_map_size lsth)); C8 (wz (sc_size lsth))] [C8 (wz (Z.of_nat (length (as_sec st) - 1)))]) in LHDR.
        destruct LHDR as [_ LH]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in LH.
        replace (Z.of_nat (length (as_sec st) - 1)) with (nch - 1) in LH by (clear - NCHL LTI; lia). exact LH. }
      assert (hCHDR : rw_cells asegs m (a + 6128) [C1 (b8 3); C1 (b8 b1); C2 (wz 0); C4 (wz (ch_used ch)); C8 (wz actx)]).
      { replace (a + 6128) with (U - kChunkHeaderSize) by (rewrite E8, E10; unfold kChunkHeaderSize, kPageSize; clear; lia). exact HD. }
      assert (hVISE : restrict (a_L s) (a_S s) msF
                      = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz cb) (wz (a + 6128)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           F (Z_to_bv 64 0x947ac) fc None m (seg_rom asegs)).
      { replace (a + 6128) with mch by (rewrite E9, E10; unfold kPageSize; clear; lia). exact VISE. }

      assert (hWIN : forall x : word, sh a <= bv_unsigned x < sh a + msz / 8 -> in_rangesb x (a_S s) = true).
      { intros x Hx. destruct ASV as [_ V2]. exact (V2 h x HIN Hx). }
      assert (hHAS : map_has (vm_maps (m_vmmaps mo)) (wz a) (wz msz) = true) by (apply map_has_of_In; exact (ak_secmaps s mo AK h HIN)).
      assert (hNOL : forall x : word, a <= bv_unsigned x < a + msz -> in_rangesb x (a_L s) = false) by (intros x Hx; exact (IL3 h x HIN Hx)).
      assert (hNOACC : forall x : word, a <= bv_unsigned x < a + msz -> in_rangesb x (vm_noaccess (m_vmmaps mo)) = false) by (intros x Hx; exact (ak_sec_noacc s mo AK h x HIN Hx)).
      unfold AINST in SB32, INST64, NRES, SST, MTX, GST.
      change (1628632 + 32) with 1628664 in SB32. change (1628632 + 64) with 1628696 in INST64. change (1628632 + 112) with 1628744 in NRES.
      change (1628632 + 136) with 1628768 in SST. change (1628632 + 680) with 1629312 in SST, MTX. change (1628632 + 688) with 1629320 in GST. change (1628632 + 728) with 1629360 in GST.

      eapply (recycle_sec_sreach (a_L s) (a_S s) (a_Zr s) msF mo Q ra sp gp tp t0 t1 t2 s0 s1 (wz cb) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
                lo a msz (sc_size h) (Z.of_nat idx) pa nres nch lst (nch - 1) ATSD CTX T sb (ch_used ch) actx chunks (b8 3) (b8 b1) sbs g b244
                MI ST LO HI hSPA hAR hSBX hSBR hTPR hRNG hPLC hPAR hNCH hIDX hLNTH hLR hPLCL hLSTA hDISJ hSEN REN SB32 INST64 NRES SST MTX GST PA HDR hLSTC hCHDR TST SHD SHDL OK hVISE
                NW NWA NOV (ak_zrsh2 s mo AK) (ak_shrf2 s mo AK) (ak_shmc2 s mo AK) (ak_shna s mo AK) hWIN hHAS hNOL hNOACC).

      cbv beta. intros msF' mo' P.
      destruct P as (y0 & y1 & y2 & ya0 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & m' & OK2 & VIS2 & MO2 & MU & WMO & MI2 & SEN2 & REN2 & ST2
                     & INST2 & NRES2 & SST2 & MTX2 & GST2 & PA2 & LSTC2 & TST2 & SH2 & GONE).
      assert (SPV : 0 <= bv_unsigned sp < 2 ^ 64) by exact SPR.
      assert (WSP : wz (bv_unsigned sp) = sp) by (unfold wz; apply Z_to_bv_bv_unsigned).
      assert (MU' : munch (rs_W lo (wz (bv_unsigned sp)) a msz pa nch lst T) m m') by (rewrite WSP; exact MU).
      assert (INST2' : rw_cells asegs m' (AINST + 64) [C8 (wz 4096); C8 (wz pa); C8 (wz pa)]) by exact INST2.
      assert (NRES2' : rw_cells asegs m' (AINST + 112) [C8 (wz nres); C8 (wz (nch - 1)); C8 (wz 0)]) by exact NRES2.
      assert (SST2' : stk asegs m' (AINST + 136) (AINST + 680)) by exact SST2.
      assert (MTX2' : rw_cells asegs m' (AINST + 680) [C8 (wz 0)]) by exact MTX2.
      assert (GST2' : stk asegs m' (AINST + 688) (AINST + 728)) by exact GST2.
      assert (NWL : entries_nowrap (a_L s)) by (apply (lazy_ranges_okb_nowrap asegs); exact (lzok_ranges OK)).
      assert (SL : forall x : word, in_rangesb x (a_S s) = true -> in_rangesb x (a_L s) = true).
      { intros x Hx. apply (lzok_ZrL OK). apply (lzok_SZr OK). exact Hx. }
      assert (AMXD : AMODELX sN mo' /\ depot_cov d mo') by (eapply (amodelx_after_rs s m XC XB ch idx h lsth d lo); eassumption).
      destruct AMXD as [AMX2 DCOV2].
      apply K. unfold rs_gpost, rstep_post.
      exists sN, y0, y1, y2, ya0, ya1, ya2, ya3, ya4, ya5, ya6, ya7, y3, y4, y5, y6, m'.
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [intros sc Hin; change (as_sec (a_st sN)) with l1 in Hin; exact (proj1 (proj1 (L1IN sc) Hin))|].
      split; [exact INIT|].
      split; [intros c0 _; reflexivity|].
      split; [exact OK2|]. split; [exact VIS2|].
      split; [post arepq_after_rs|].
      split; [post awin_after_rs|].
      split; [post flagsx_after_rs|].
      split; [exact AMX2|].
      split; [pose proof MO2 as M; unfold rs_model in M; cbv beta iota zeta in M; exact (proj1 M)|].
      split; [post avmx_after_rs|].
      split; [exact DCOV2|].
      split; [post depot_after_rs|].
      split; [post depot_placed_after|].
      split; [exact MI2|]. split; [exact ST2|].
      split; [post acompl_after_rs|].
      split; [post avis_after_rs|].
      split; [post pendz_after_rs|].
      split; [post alive_kept_rs|].
      split; [post alive_after_rs|].

      intros stA SBS. change (a_st sN) with st2.
      assert (EQ2 : secdel st ch = st2) by (rewrite (secdel_eq st XC XB ch WQ idx h HIDX HMAP); unfold st2, a; rewrite HMAP; reflexivity).
      rewrite <- EQ2.
      apply (cb_recycle_sec_eval stA st XC XB ch idx h SBS WQ CHIN SEC QUAR HIDX HMAP); rewrite <- ?HMAP; fold a msz mch.
      - unfold kPageSize. clear - B. tauto.
      - bands_as (_ & _ & _ & _ & _ & BA & _). unfold addr_is_in_mem, kLowMemEnd, kShadowOffset, kHighMemBeg, kHighMemEnd.
        clear - BA B MSZ. acb. repeat split; apply orb_true_iff; (destruct BA as [BA|BA]; [left| right]); apply andb_true_iff; split; apply Z.leb_le; lia.
      - unfold in_primary. apply andb_false_iff. rewrite E9, E10. unfold disj, kSpaceSize, kPageSize in *. unfold sb, a_sb in N1. unfold st.
        clear - N1 MSZ. destruct N1 as [N1|N1]; [left; apply Z.leb_gt; lia| right; apply Z.ltb_ge; lia].
      - intros h' Hin LE. destruct (Z.eq_dec (sc_map_beg h') a) as [E|NE].
        + left.
          destruct (In_nth_error _ _ Hin) as (j & Hj).
          assert (EJ : j = idx); [| subst j; rewrite HIDX in Hj; injection Hj as <-; reflexivity].
          apply (proj1 (NoDup_nth_error (List.map sc_map_beg (as_sec st))) SND j idx); [rewrite length_map; exact (nth_error_lt _ _ _ Hj)|].
          rewrite !nth_error_map, HIDX, Hj. cbn. fold a. rewrite E. reflexivity.
        + right. pose proof (APART h' Hin NE) as D. pose proof (SECP h' Hin) as (_ & _ & _ & G4 & _). unfold kPageSize in G4.
          rewrite E9, E10 in LE. unfold kPageSize in LE. clear - D LE G4 MSZ. lia.
    Qed.
  End At.

  Theorem recycle_sec_arepq :
    (forall msF' mo', rs_gpost msF' mo' -> sreach asegs Q (mkCfg msF' mo')) -> sreach asegs Q (mkCfg msF mo).
  Proof.
    intros K. pose proof (AREPQ_WFQ _ _ _ _ RQ) as WQ.
    destruct (sec_entry st XC XB ch WQ CHIN SEC) as (idx & h & HIDX & HMAP & _).
    assert (NE : as_sec st <> []) by (intros E; rewrite E in HIDX; destruct idx; discriminate).
    destruct (exists_last NE) as (l0 & lsth & EL).
    assert (HLAST : nth_error (as_sec st) (length (as_sec st) - 1)%nat = Some lsth).
    { rewrite EL, length_app. cbn [length]. replace (length l0 + 1 - 1)%nat with (length l0) by lia. rewrite nth_error_app2, Nat.sub_diag by lia. reflexivity. }
    exact (recycle_sec_arepq_at idx h lsth HIDX HMAP HLAST K).
  Qed.
End RSStep.
End HCW.
