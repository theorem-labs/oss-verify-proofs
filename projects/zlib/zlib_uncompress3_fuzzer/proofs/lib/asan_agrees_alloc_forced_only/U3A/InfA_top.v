(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Bytes.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed AsanProgDeps.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import ExecF ITreeA SysStepF Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.AsanW Require Import AImg RtCells AProto ABase ABytes AMalloc_iface AUri_kit.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AArr InfPure InfPure_entry.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.U3A Require Import U2AObj U2AIface U2AGlue InfABase InfAIface InfAGlueE AdlUIface AdlU U2AIfaceS InfAGlueU InfPure_leave InfAEpiK InfA_pro InfA_hdr InfA_entry InfA_loop InfA_leave_dt InfA_leave InfA_fin InfA_uw InfA_w7base InfA_type InfA_head InfA_head2 InfA_dict InfA_dictid InfA_dictid2.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Common Require Import DrvAgree RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
Section T.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variable fflag : alayout -> Z -> Z -> Z.
  Variable rng_fs : alayout -> footprint -> Prop.
  Notation FB0 F := (mkABlock (ABFake 0) F 64).
  Hypothesis AI_fake_flag : forall L RNG st LB m cls F N,
    AHEAP AI L RNG st LB m -> In (mkABlock (ABFake cls) F N) LB ->
    rw_cells asegs m (fflag L cls F) [C1 (Z_to_bv 8 1)] /\ rng RNG (fflag L cls F) 1
    /\ ablk (fflag L cls F) (fflag L cls F + 1) /\ fflag L cls F + 1 <= ATOP
    /\ (forall b, In b LB -> fflag L cls F + 1 <= ab_addr b \/ ab_addr b + ab_size b <= fflag L cls F)
    /\ ~ in_ranges CI (fflag L cls F).
  Hypothesis AI_fake_release : forall L RNG st LB m cls F N,
    AHEAP AI L RNG st (mkABlock (ABFake cls) F N :: LB) m ->
    AHEAP AI L RNG st LB (write_to_mem m (wa (fflag L cls F)) [Z_to_bv 8 0]).
  Hypothesis SM0 : SM0_stmt AI fflag rng_fs.
  Hypothesis UWO : updatewindow_old_stmtA AI.
  Hypothesis UWN : updatewindow_new_stmtA AI.

  Notation ARMG Lb X :=
    (forall L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh, rng_fs L RNG -> atmost1_c2 LB -> tp = Z_to_bv 64 ATP ->
     forall cx ly, l_SP ly + 16 < al_top L -> rng RNG (l_lo ly) (al_top L - l_lo ly) ->
     arm_stmtA cx ly AI L RNG stA LB gp tp FR fc POST LBc m0 payload fw saved fk fksh Lb X).
  Hypothesis A_STORED : ARMG 0x8e93c STORED.
  Hypothesis A_COPY_ : ARMG 0x8f03c COPY_.
  Hypothesis A_COPY : ARMG 0x8f054 COPY.
  Hypothesis A_TABLE : ARMG 0x8e3c4 TABLE.
  Hypothesis A_LENLENS : ARMG 0x8eb0c LENLENS.
  Hypothesis A_CODELENS : ARMG 0x8f4cc CODELENS.
  Hypothesis A_LEN_ : ARMG 0x90cac LEN_.
  Hypothesis A_LEN : ARMG 0x90cc4 LEN.
  Hypothesis A_LENEXT : ARMG 0x8e450 LENEXT.
  Hypothesis A_DIST : ARMG 0x91224 DIST.
  Hypothesis A_DISTEXT : ARMG 0x8e430 DISTEXT.
  Hypothesis A_MATCH : ARMG 0x91680 MATCH.
  Hypothesis A_LIT : ARMG 0x8e814 LIT.
  Hypothesis A_CHECK : ARMG 0x8e9b4 CHECK.
  Hypothesis A_LENGTH : ARMG 0x90240 LENGTH.

  Theorem inflate_core : forall haswin, inflate_stmtA AI rng_fs haswin.
  Proof.
    intros haswin. unfold inflate_stmtA. intros until pad.
    intros AH OBJ HW AINV MNE CIN0 COUT0 CW0 EM UIMG ST LOC LOS SP16 TOPS MI TP A0 A1 RA4 RANE UNW RSTK RI RISH RFS APS. subst a0 a1.
    set (POST := fun ms1 : machine_state =>
         inf_ret AI L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc (aps_m s) LB cx Fu Zs lo payload m ms1
      \/ (haswin = false /\
          implMA RNG (amalloc_M 32768) s
                 (inf_retW AI L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc s LB cx Fu Zs lo payload m) ms1)).
    pose proof OBJ as (SHOME & _ & _ & _ & NOL & _ & OSZ & _ & _ & _ & _ & _ & NR & _ & PAYR & PLEN & _ & _ & _ & _ & AM1 & _ & _ & _ & PAYW).
    eapply (inf_entry AI fflag rng_fs SM0 AI_fake_flag L RNG ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                      FR fc m (aps_m s) LB cx Fu Zs lo payload st lf cf wf fo zti zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total back was pad POST);
      try eassumption.
    intros F0 SPA fw jk v0 v8 v16 v240 v504 j512 j520 y1 y5 y6 y11 y12 y13 y14 y15 y16 y17 y21 y27 m1 CTX RF0 RSF0 ESPA VIS HID.
    set (SAVED := inf_SAVED ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) in *.
    set (FKC := F0_cells jk (Z_to_bv 64 (fflag L 0 F0))) in *. set (FKS := F0_shadow) in *.
    assert (AM2 : atmost1_c2 (FB0 F0 :: LB)).
    { intros F1 n1 F2 n2 [X|H1] [Y|H2]; try discriminate X; try discriminate Y. exact (AM1 F1 n1 F2 n2 H1 H2). }
    assert (SI : sinv cx (st_load cx st) lf cf) by (apply sinv_load; assumption).
    assert (ARR : inf_arr_ok cx wf fo) by (destruct EM as (_ & _ & _ & _ & _ & _ & _ & _ & X & _); exact X).
    assert (CIN0R : 0 <= c_cin0 cx <= c_n cx).
    { destruct AINV as (RN & _). unfold IDefs.RNG in RN. cbv zeta in RN. destruct RN as (R1 & R2 & _). lia. }
    assert (KEPI : LV_KEPI AI L RNG (aps_m s) (FB0 F0 :: LB) gp tp FR fc POST LB m payload fw SAVED FKC FKS cx (ILAY (bv_unsigned sp) SPA Zs F0 lo)).
    { unfold LV_KEPI, L_EPI. intros st1 rv1 lf1 cf1 wf1 fo1 g0 g8 g16 g240 g504 gnext h512 h520 zti1 zto1 zmsg1 zopq1 zdt1 zadl1 zres1 zr1 zr2 zr3
                                  havedict1 dmax1 check1 total1 back1 was1 pad1 e1 e5 e6 e7 e11 e12 e13 e14 e15 e16 e17 e18 e19 e21 e22 e24 e25 e26 e28 e29 e30 e31 mK
                                  SIK ARRK RVK VISK HIDK.
      cbn [l_SP l_SPA l_Zs l_F0 l_lo]. rewrite Z_to_bv_bv_unsigned.
      eapply evtF_mono; [| intros ms' X; left; exact X].
      subst SAVED FKC FKS. unfold F0_cells, F0_shadow in HIDK.
      eapply (inf_fin_epi AI fflag AI_fake_flag AI_fake_release L RNG (aps_m s) LB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m payload
                cx SPA Zs F0 lo Fu st1 rv1 lf1 cf1 wf1 fo1 fw);
        [exact CTX| exact NOL| exact AM1| exact SHOME| exact PAYW| exact PAYR| exact PLEN| exact RF0| exact RSF0| exact SIK| exact ARRK| clear - RVK; lia
        | intros X; exfalso; clear - X RVK; lia| exact VISK| exact HIDK]. }
    assert (ARMS : arms_ok AI L RNG (aps_m s) (FB0 F0 :: LB) gp tp FR fc POST LB m payload fw SAVED FKC FKS cx (ILAY (bv_unsigned sp) SPA Zs F0 lo)).
    { unfold arms_ok.
      split; [exact (head_arm AI L RNG (aps_m s) (FB0 F0 :: LB) gp tp FR fc POST LB m payload fw SAVED FKC FKS adler32_null_U cx _)|].
      split; [exact (dictid_arm AI L RNG (aps_m s) (FB0 F0 :: LB) gp tp FR fc POST LB m payload fw SAVED FKC FKS adler32_null_U cx _
                       (type_garm AI L RNG (aps_m s) (FB0 F0 :: LB) gp tp FR fc POST LB m payload fw SAVED FKC FKS cx _) KEPI)|].
      split; [exact (dict_arm AI L RNG (aps_m s) (FB0 F0 :: LB) gp tp FR fc POST LB m payload fw SAVED FKC FKS adler32_null_U cx _
                       (type_garm AI L RNG (aps_m s) (FB0 F0 :: LB) gp tp FR fc POST LB m payload fw SAVED FKC FKS cx _) KEPI)|].
      split; [exact (type_arm AI L RNG (aps_m s) (FB0 F0 :: LB) gp tp FR fc POST LB m payload fw SAVED FKC FKS cx _)|].
      split; [exact (typedo_arm AI L RNG (aps_m s) (FB0 F0 :: LB) gp tp FR fc POST LB m payload fw SAVED FKC FKS cx _)|].
      split; [exact (A_STORED L RNG (aps_m s) (FB0 F0 :: LB) gp tp FR fc POST LB m payload fw SAVED FKC FKS RFS AM2 TP cx (ILAY (bv_unsigned sp) SPA Zs F0 lo) TOPS RSTK)|].
      split; [exact (A_COPY_ L RNG (aps_m s) (FB0 F0 :: LB) gp tp FR fc POST LB m payload fw SAVED FKC FKS RFS AM2 TP cx (ILAY (bv_unsigned sp) SPA Zs F0 lo) TOPS RSTK)|].
      split; [exact (A_COPY L RNG (aps_m s) (FB0 F0 :: LB) gp tp FR fc POST LB m payload fw SAVED FKC FKS RFS AM2 TP cx (ILAY (bv_unsigned sp) SPA Zs F0 lo) TOPS RSTK)|].
      split; [exact (A_TABLE L RNG (aps_m s) (FB0 F0 :: LB) gp tp FR fc POST LB m payload fw SAVED FKC FKS RFS AM2 TP cx (ILAY (bv_unsigned sp) SPA Zs F0 lo) TOPS RSTK)|].
      split; [exact (A_LENLENS L RNG (aps_m s) (FB0 F0 :: LB) gp tp FR fc POST LB m payload fw SAVED FKC FKS RFS AM2 TP cx (ILAY (bv_unsigned sp) SPA Zs F0 lo) TOPS RSTK)|].
      split; [exact (A_CODELENS L RNG (aps_m s) (FB0 F0 :: LB) gp tp FR fc POST LB m payload fw SAVED FKC FKS RFS AM2 TP cx (ILAY (bv_unsigned sp) SPA Zs F0 lo) TOPS RSTK)|].
      split; [exact (A_LEN_ L RNG (aps_m s) (FB0 F0 :: LB) gp tp FR fc POST LB m payload fw SAVED FKC FKS RFS AM2 TP cx (ILAY (bv_unsigned sp) SPA Zs F0 lo) TOPS RSTK)|].
      split; [exact (A_LEN L RNG (aps_m s) (FB0 F0 :: LB) gp tp FR fc POST LB m payload fw SAVED FKC FKS RFS AM2 TP cx (ILAY (bv_unsigned sp) SPA Zs F0 lo) TOPS RSTK)|].
      split; [exact (A_LENEXT L RNG (aps_m s) (FB0 F0 :: LB) gp tp FR fc POST LB m payload fw SAVED FKC FKS RFS AM2 TP cx (ILAY (bv_unsigned sp) SPA Zs F0 lo) TOPS RSTK)|].
      split; [exact (A_DIST L RNG (aps_m s) (FB0 F0 :: LB) gp tp FR fc POST LB m payload fw SAVED FKC FKS RFS AM2 TP cx (ILAY (bv_unsigned sp) SPA Zs F0 lo) TOPS RSTK)|].
      split; [exact (A_DISTEXT L RNG (aps_m s) (FB0 F0 :: LB) gp tp FR fc POST LB m payload fw SAVED FKC FKS RFS AM2 TP cx (ILAY (bv_unsigned sp) SPA Zs F0 lo) TOPS RSTK)|].
      split; [exact (A_MATCH L RNG (aps_m s) (FB0 F0 :: LB) gp tp FR fc POST LB m payload fw SAVED FKC FKS RFS AM2 TP cx (ILAY (bv_unsigned sp) SPA Zs F0 lo) TOPS RSTK)|].
      split; [exact (A_LIT L RNG (aps_m s) (FB0 F0 :: LB) gp tp FR fc POST LB m payload fw SAVED FKC FKS RFS AM2 TP cx (ILAY (bv_unsigned sp) SPA Zs F0 lo) TOPS RSTK)|].
      split; [exact (A_CHECK L RNG (aps_m s) (FB0 F0 :: LB) gp tp FR fc POST LB m payload fw SAVED FKC FKS RFS AM2 TP cx (ILAY (bv_unsigned sp) SPA Zs F0 lo) TOPS RSTK)|].
      exact (A_LENGTH L RNG (aps_m s) (FB0 F0 :: LB) gp tp FR fc POST LB m payload fw SAVED FKC FKS RFS AM2 TP cx (ILAY (bv_unsigned sp) SPA Zs F0 lo) TOPS RSTK). }
    eapply (loop_kdisp AI L RNG (aps_m s) (FB0 F0 :: LB) gp tp FR fc POST LB m payload fw SAVED FKC FKS PAYR
              cx (ILAY (bv_unsigned sp) SPA Zs F0 lo) (meas cx (st_load cx st) + 1) CTX PLEN);
      [| exact ARMS| exact SI| lia| exact ARR| exact VIS| exact HID].
    unfold KLEAVE. intros st' rv lf' cf' wf' fo' w0 w8 w16 w240 w504 wnext k512 k520 zni' zai' zti' zno' zao' zto' zmsg' zopq' zdt' zadl' zres' zq1 zq2 zq3
                          havedict' dmax' check' total' shold' sbits' back' was' pad' q1 q5 q6 q11 q12 q13 q14 q15 q16 q17 q28 q31 m2 SI' ARR' VIS' HID'.
    rewrite <- (Z_to_bv_mod64 rv).
    assert (RRV : 0 <= rv mod 2 ^ 64 < 18446744073709551616) by (apply Z.mod_pos_bound; lia).
    eapply (inf_leave_main AI L RNG (aps_m s) (FB0 F0 :: LB) gp tp FR fc POST LB m payload fw SAVED FKC FKS adler32_U
              cx (ILAY (bv_unsigned sp) SPA Zs F0 lo) st' (rv mod 2 ^ 64) lf' cf' wf' fo'); [exact CTX| exact PLEN| exact SI'| exact ARR'| exact RRV| exact VIS'| exact HID'| |].
    -
      intros zti2 zto2 zadl2 check2 total2. unfold LV_K1. intros zdt2 u1 u5 u6 u7 u11 u12 u13 u14 u15 u16 u17 u18 u19 u21 u22 u25 u28 u29 u31 m3 VIS3 HID3.
      cbn [l_SP l_SPA l_Zs l_F0 l_lo]. rewrite Z_to_bv_bv_unsigned.
      eapply evtF_mono; [| intros ms' X; left; exact X].
      subst SAVED FKC FKS. unfold F0_cells, F0_shadow in HID3.
      eapply (inf_fin AI fflag AI_fake_flag AI_fake_release L RNG (aps_m s) LB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m payload
                cx SPA Zs F0 lo Fu st' (rv mod 2 ^ 64) lf' cf' wf' fo' fw);
        [exact CTX| exact NOL| exact AM1| exact SHOME| exact PAYW| exact PAYR| exact PLEN| exact CIN0R| exact RF0| exact RSF0| exact SI'| exact ARR'| exact RRV| exact VIS3| exact HID3].
    -
      intros zti2 zto2 zadl2 check2 total2. unfold LV_K2. intros zdt2 u5 u6 u7 u13 u14 u15 u16 u17 u28 u29 u30 u31 m3 VIS3 HID3 DEC.
      cbn [l_SP l_SPA l_Zs l_F0 l_lo].
      pose proof CTX as (S16 & SB & (ps & HPS & PAYH) & _ & RZ & RSZ & HF0 & F064 & F0B & RS & RSS & OBE & OSZ' & OCI & ROB & ROBS & WDC
                       & D1 & NR' & D16 & RD & RSD & LOC' & LOS' & SPAR & SPA32 & SP16' & SPT & RSTK' & RI' & RISH' & RSFU & TABC1 & TABC2 & LBABLK).
      cbn [l_SP l_SPA l_Zs l_F0 l_lo] in *.
      pose proof VIS3 as (FRM3 & STRM3 & SSC3 & LENS3 & WORK3 & CODES3 & TAIL3 & OUT3 & PAYB3 & STK3 & MI3 & MNE3). cbn [l_SP l_SPA l_Zs l_F0 l_lo] in *.
      pose proof HID3 as (AH3 & SHZ3 & SHS3 & SHO3 & WIN3 & UNP3 & SAVED3 & _ & FK3 & _ & FKSH3 & _ & _ & CAG3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & GAP3 & (obr & OBR3) & WFU3).
      cbn [l_SP l_SPA l_Zs l_F0 l_lo] in *.
      pose proof SHOME as (HFUr & ZSE & FU256 & FUB).
      pose proof SI' as (RN' & WI' & _ & _). pose proof (rng_win _ _ _ _ RN') as RWIN. unfold IDefs.RNG in RN'. cbv zeta in RN'.
      destruct RN' as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & _).
      atop_facts. unfold KEND in SPT. unfold A_OUTBUF in OBE.
      pose proof (AI_layout AI _ _ _ _ _ AH) as (_ & _ & TOP47 & _).
      assert (USPA : bv_unsigned (Z_to_bv 64 SPA) = SPA) by (apply unsigned_lit; clear - SPAR LOC' LOS' H SPT; lia).
      assert (SHFU : shad Fu = Z.shiftr Zs 3 + 2147450880 - 4).
      { pose proof (ablk_lin _ _ FUB) as (_ & FUB2 & _). rewrite shad_div. unfold ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
        clear - ZSE FU256 FUB2. Z.div_mod_to_equations. lia. }
      assert (OBOK : outbuf_ok m3).
      { unfold outbuf_ok. unfold A_OUTBUF. rewrite <- OBE. split; [| split; [exact SHO3|]].
        - pose proof (blob_join2 m3 (c_ob cx) (Z.to_nat (c_osz cx)) (Z.to_nat (262144 - c_osz cx)) _ obr (f8arr_blob m3 _ _ _ OUT3)) as X.
          rewrite Z2Nat.id in X by (clear - OSZ'; lia). specialize (X OBR3).
          replace (Z.to_nat (c_osz cx) + Z.to_nat (262144 - c_osz cx))%nat with (Z.to_nat 262144) in X by (clear - OSZ'; lia). eexists. exact X.
        - pose proof (wr_at_of_shadow_bytes asegs m3 _ _ _ SHO3) as X.
          replace (Z.shiftr (c_ob cx) 3 + 2147450880 + 32768 - (Z.shiftr (c_ob cx) 3 + 2147450880)) with 32768 in X by (clear; lia).
          rewrite shadE. exact X. }
      assert (SSH3 : strm_sh RNG m3 Fu Zs).
      { split; [exact SHZ3|]. split; [exact RZ|]. rewrite SHFU. split; [exact WFU3| exact RSFU]. }
      destruct haswin.
      +
        destruct WDC as [W0|(W16 & WB & (pw & HPW) & RW & RSW)]; [contradiction|].
        destruct (WIN3 HW) as (SHW3 & FW3).
        assert (WSZ : wsz cx = 32768) by (unfold wsz; destruct (Z.eqb_spec (c_w cx) 0); [contradiction| reflexivity]).
        rewrite WSZ in SSC3.
        destruct WI' as (_ & WI'). specialize (WI' HW). unfold WIN_SIZE in WI'. destruct WI' as (WI1 & WI2 & WI3).
        pose proof UWO as UWO'. unfold updatewindow_old_stmtA in UWO'.
        eapply evtF_cut.
        { rewrite OBE. unfold strm_cells, istate_cells in STRM3, SSC3.
          eapply UWO' with (Fu := Fu) (Zs := Zs) (S := c_p cx) (Wd := c_w cx) (lo := lo) (pw := pw) (ps := ps) (mode := t_mode st') (cout := t_cout st')
                           (copy := t_out st' - (c_osz cx - t_cout st')) (wn := t_wnext st') (wh := t_whave st') (LB := FB0 F0 :: LB) (st := aps_m s).
          all: rewrite ?USPA.
          - exact AH3.
          - split; [right; exact HFUr| split; [exact ZSE| split; [exact FU256| exact FUB]]].
          - exact SSH3.
          - exact HPS.
          - exact HPW.
          - exact STRM3.
          - exact SSC3.
          - exact (f8arr_blob m3 _ _ _ FW3).
          - exact OBOK.
          - clear - R11 R13. lia.
          - clear - R4 OSZ'. lia.
          - clear - WI2 RWIN. lia.
          - clear - WI1 RWIN. lia.
          - exact STK3.
          - exact LOC'.
          - unfold UW_STACK. clear - LOS'. lia.
          - clear - SPA32. Z.div_mod_to_equations. lia.
          - clear - SPAR TOPS. lia.
          - exact MI3.
          - exact TP.
          - reflexivity.
          - reflexivity.
          - reflexivity.
          - exact RSTK.
          - exact RI.
          - exact RISH. }
        cbv beta. unfold uw_post_core. rewrite USPA.
        intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m4 & wbytes' & -> & MI4 & STK4 & CAGU & AH4 & SSC4 & WBLOB).
        set (copy := t_out st' - (c_osz cx - t_cout st')) in *.
        pose proof (uw_next_win 32768 (t_wnext st') (t_whave st') copy ltac:(subst copy; clear - R11; lia)
                      ltac:(right; clear - WI1 WI2 WI3 RWIN; lia)) as (UW1 & UW2 & UW3).
        set (wn' := fst (uw_next 32768 (t_wnext st') (t_whave st') copy)) in *. set (wh' := snd (uw_next 32768 (t_wnext st') (t_whave st') copy)) in *.
        destruct (uw_rebuild AI L RNG RNG (aps_m s) (aps_m s) LB LB m payload cx (bv_unsigned sp) SPA Zs F0 lo Fu st' lf' cf' wf' fo' fw
                    w0 w8 w16 w240 w504 wnext k512 k520 zti2 zto2 zmsg' zopq' zdt2 zadl2 zres' zq1 zq2 zq3 havedict' dmax' check2 total2 back' was' pad'
                    SAVED FKC FKS m3 m4 (c_w cx) wn' wh' wbytes' CTX SI' VIS3 HID3 SHOME PLEN (fp_le_refl RNG) HW ltac:(left; reflexivity)
                    ltac:(exists pw; destruct HPW as [X|X]; [discriminate X| exact X]) ltac:(intros b Hb; exact Hb) ltac:(intros b Hb; left; exact Hb)
                    UW1 UW2 UW3 (PAYW HW) MI4 STK4 CAGU AH4 SSC4 WBLOB) as (CTX4 & SI4 & VIS4 & HID4).
        assert (WWE : with_win cx (c_w cx) = cx) by (destruct cx; reflexivity).
        rewrite WWE in CTX4, SI4, VIS4, HID4.
        replace (ret_pc (Z_to_bv 64 601184)) with (Z_to_bv 64 601184) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        pose proof VIS4 as (FRM4 & _). cbn [l_SP l_SPA l_Zs l_F0 l_lo] in FRM4.
        eapply (inf_uwret RNG gp tp FR fc POST SPA Zs F0 (c_p cx)); [| eapply rng_sub'; [exact RSTK'| clear - SPAR LOS'; lia]| exact FRM4].
        intros y12' y13'. rewrite Z_to_bv_bv_unsigned. (* inf_uwret's K frees a2 / a3 at 1.4 and keeps out in a1 *)
        eapply evtF_mono; [| intros ms' X; left; exact X].
        subst SAVED FKC FKS. unfold F0_cells, F0_shadow in HID4.
        eapply (inf_fin AI fflag AI_fake_flag AI_fake_release L RNG (aps_m s) LB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m payload
                  cx SPA Zs F0 lo Fu (set_win st' wh' wn') (rv mod 2 ^ 64) lf' cf' wf' fo');
          [exact CTX| exact NOL| exact AM1| exact SHOME| exact PAYW| exact PAYR| exact PLEN| exact CIN0R| exact RF0| exact RSF0| exact SI4| exact ARR'| exact RRV
          | exact VIS4| exact HID4].
      +
        apply evtF_done. right. split; [reflexivity|].
        assert (WSZ0 : wsz cx = 0) by (unfold wsz; rewrite HW; reflexivity).
        rewrite WSZ0, HW in SSC3.
        destruct (UNW eq_refl) as (UCH & LTR & INU & S0GE).
        pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. change (2 ^ Z.of_N 64) with (2^64) in RSP.
        pose proof (bv_unsigned_in_range 64 ra) as RRA. unfold bv_modulus in RRA. change (2 ^ Z.of_N 64) with (2^64) in RRA.
        pose proof (bv_unsigned_in_range 64 s0) as RS0. unfold bv_modulus in RS0. change (2 ^ Z.of_N 64) with (2^64) in RS0.
        assert (USP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp)) = bv_unsigned sp) by (apply unsigned_lit; exact RSP).
        pose proof (ablk_lin _ _ SB) as (SB1 & SB2 & SB3 & SB4). pose proof (ablk_lin _ _ FUB) as (FUB1 & FUB2 & FUB3 & FUB4).
        assert (UCH3 : uchain m3 (al_top L) AMALLOC_PC (SPA - 112) (bv_unsigned sp) UDEPTH (bv_unsigned ra :: tr)).
        { assert (E : (bv_unsigned ra =? AMALLOC_PC) = false) by (apply Z.eqb_neq; exact RANE).
          subst SAVED. unfold inf_SAVED in SAVED3. rw_split SAVED3 11%nat SAVA SAVB.
          destruct SAVB as [[_ SAVB] _]. cbn [cells_bytes cbytes] in SAVB. rewrite app_nil_r in SAVB.
          apply bytes_at_app in SAVB. destruct SAVB as [BS0 BRA]. rewrite length_le8 in BRA.
          replace (bv_unsigned sp + -16 + Z.of_nat 8) with (bv_unsigned sp - 8) in BRA by lia.
          replace (bv_unsigned sp + -16) with (bv_unsigned sp - 16) in BS0 by lia.
          rewrite <- (Z_to_bv_bv_unsigned s0) in BS0. rewrite <- (Z_to_bv_bv_unsigned ra) in BRA.
          pose proof (uc_step m3 (al_top L) AMALLOC_PC (SPA - 112) (bv_unsigned sp) UDEPTH (bv_unsigned s0) (bv_unsigned ra) tr
                        ltac:(clear - SPAR; lia) ltac:(clear - TOPS; lia) ltac:(clear - SP16; Z.div_mod_to_equations; lia) ltac:(unfold UDEPTH; lia)
                        BS0 BRA ltac:(clear - RA4 RRA; lia) RS0) as X.
          rewrite E in X. cbn [app] in X. apply X.
          eapply uchain_frame; [exact UCH|]. intros a Ha.
          unfold client_agree in CAG3.
          destruct (CAG3 a ltac:(clear - Ha S0GE RSP TOP47; lia)) as [EQ _]; [| exact EQ].
          split; [left; clear - Ha S0GE TOP47; lia|].
          unfold inf_WR. cbn [l_SP l_SPA l_Zs l_F0 l_lo]. rewrite HW.
          intros (iv & [<-|[<-|[<-|[<-|[<-|[]]]]]] & Hr); cbn [fst snd] in Hr.
          - clear - Hr Ha S0GE ZSE FUB3 H LOC' LOS' SPAR. lia.
          - clear - Hr Ha S0GE SB3 H LOC' LOS' SPAR. lia.
          - clear - Hr Ha S0GE OBE OSZ' H LOC' LOS' SPAR. lia.
          - clear - Hr Ha S0GE H LOC' LOS' SPAR. lia.
          - clear - Hr Ha S0GE H LOC' LOS' SPAR. lia. }
        pose proof UWN as UWN'. unfold updatewindow_new_stmtA in UWN'.
        eapply implMA_post_evtF.
        { rewrite OBE. unfold strm_cells, istate_cells in STRM3, SSC3.
          eapply UWN' with (Fu := Fu) (Zs := Zs) (S := c_p cx) (lo := lo) (ps := ps) (mode := t_mode st') (cout := t_cout st')
                           (copy := t_out st' - (c_osz cx - t_cout st')) (tr := bv_unsigned ra :: tr) (LB := FB0 F0 :: LB) (s := s).
          all: rewrite ?USPA, ?USP.
          - exact AH3.
          - split; [right; exact HFUr| split; [exact ZSE| split; [exact FU256| exact FUB]]].
          - exact SSH3.
          - exact HPS.
          - unfold outbuf_client, A_OUTBUF. rewrite <- OBE. exact OCI.
          - exact STRM3.
          - exact SSC3.
          - exact OBOK.
          - clear - R11 R13. lia.
          - clear - R4 OSZ'. lia.
          - exact STK3.
          - exact LOC'.
          - unfold UW_STACK. clear - LOS'. lia.
          - clear - SPA32. Z.div_mod_to_equations. lia.
          - exact MI3.
          - exact TP.
          - reflexivity.
          - reflexivity.
          - reflexivity.
          - clear - SPAR TOPS. lia.
          - exact UCH3.
          - cbn [length]. clear - LTR. lia.
          - exact INU.
          - clear - SPAR. lia.
          - exact RSTK.
          - exact RI.
          - exact RISH.
          - exact APS. }
        cbv beta. intros r s' RNG' ms' POSTW. unfold uw_new_post in POSTW. destruct POSTW as (FPLE & REST & CASE).
        destruct r as [pw|]; [| contradiction]. destruct CASE as (Wd & W16 & WB & CORE).
        unfold uw_post_core in CORE. rewrite USPA in CORE.
        destruct CORE as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m4 & wbytes' & -> & MI4 & STK4 & CAGU & AH4 & SSC4 & WBLOB).
        pose proof (ablk_lin _ _ WB) as (WB1 & WB2 & WB3 & WB4). unfold AIMG_HI in WB1.
        assert (WN0 : Wd <> 0) by (clear - WB1; lia).
        set (copy := t_out st' - (c_osz cx - t_cout st')) in *.
        pose proof (uw_next_win 0 0 0 copy ltac:(subst copy; clear - R11; lia) ltac:(left; reflexivity)) as (UW1 & UW2 & UW3).
        set (wn' := fst (uw_next 0 0 0 copy)) in *. set (wh' := snd (uw_next 0 0 0 copy)) in *.
        assert (AH4' : AHEAP AI L RNG' (aps_m s') (FB0 F0 :: HB pw Wd 32768 :: LB) m4) by (eapply (AI_perm AI); [apply Permutation.perm_swap| exact AH4]).
        assert (NEWNI : ~ In (HB pw Wd 32768) (FB0 F0 :: LB)).
        { pose proof (AI_blocks_nodup AI _ _ _ _ _ AH4) as ND. inversion ND as [|x l NI0 N3]. exact NI0. }
        assert (DWP : c_q cx + c_n cx <= Wd \/ Wd + 32768 <= c_q cx).
        { destruct PAYH as [(pd & HPD & NP & PNE)|(N0 & DE)]; [| clear - N0 DE WB1; lia].
          pose proof (AI_blocks_disjoint AI _ _ _ _ _ (HB pd (c_q cx) (c_n cx)) (HB pw Wd 32768) AH4 ltac:(right; exact HPD) ltac:(left; reflexivity)
                        ltac:(intros E; apply NEWNI; rewrite <- E; exact HPD)) as X. cbn [ab_addr ab_size] in X. clear - X. lia. }
        destruct (uw_rebuild AI L RNG RNG' (aps_m s) (aps_m s') LB (HB pw Wd 32768 :: LB) m payload cx (bv_unsigned sp) SPA Zs F0 lo Fu st' lf' cf' wf' fo' fw
                    w0 w8 w16 w240 w504 wnext k512 k520 zti2 zto2 zmsg' zopq' zdt2 zadl2 zres' zq1 zq2 zq3 havedict' dmax' check2 total2 back' was' pad'
                    SAVED FKC FKS m3 m4 Wd wn' wh' wbytes' CTX SI' VIS3 HID3 SHOME PLEN FPLE WN0 ltac:(right; exact HW)
                    ltac:(exists pw; left; reflexivity) ltac:(intros b Hb; right; exact Hb)
                    ltac:(intros b [<-|Hb]; [right; exists pw; reflexivity| left; exact Hb])
                    UW1 UW2 UW3 DWP MI4 STK4 CAGU AH4' SSC4 WBLOB) as (CTX4 & SI4 & VIS4 & HID4).
        replace (ret_pc (Z_to_bv 64 601184)) with (Z_to_bv 64 601184) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        eapply evtF_mono; [| intros ms'' X; unfold inf_retW; split; [exact FPLE| split; [exact REST| exists Wd; split; [exact W16| split; [exact WB| exact X]]]]].
        pose proof VIS4 as (FRM4 & _). cbn [l_SP l_SPA l_Zs l_F0 l_lo] in FRM4.
        eapply (inf_uwret RNG' gp tp FR fc _ SPA Zs F0 (c_p cx)); [| eapply rng_fp_le; [exact FPLE| eapply rng_sub'; [exact RSTK'| clear - SPAR LOS'; lia]]| exact FRM4].
        intros y12' y13'. rewrite Z_to_bv_bv_unsigned. (* inf_uwret's K frees a2 / a3 at 1.4 and keeps out in a1 *)
        subst SAVED FKC FKS. unfold F0_cells, F0_shadow in HID4.
        eapply (inf_fin AI fflag AI_fake_flag AI_fake_release L RNG' (aps_m s') (HB pw Wd 32768 :: LB) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m payload
                  (with_win cx Wd) SPA Zs F0 lo Fu (set_win st' wh' wn') (rv mod 2 ^ 64) lf' cf' wf' fo');
          [exact CTX4| | | | | exact PAYR| exact PLEN| exact CIN0R| eapply rng_fp_le; [exact FPLE| exact RF0]| eapply rng_fp_le; [exact FPLE| exact RSF0]
          | exact SI4| exact ARR'| exact RRV| exact VIS4| exact HID4].
        * intros F n [X|X]; [discriminate X| exact (NOL F n X)].
        * intros F1 n1 F2 n2 [X|H1] [Y|H2]; try discriminate X; try discriminate Y. exact (AM1 F1 n1 F2 n2 H1 H2).
        * destruct SHOME as (A1 & A2 & A3 & A4). split; [right; exact A1| split; [exact A2| split; [exact A3| exact A4]]].
        * intros _. exact DWP.
  Qed.
End T.
End CANSEC1.
