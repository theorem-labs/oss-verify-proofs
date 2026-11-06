(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require TP_0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX Bytes Exec.
From OSSVerify.Proofs.boost_beast.http_request.lib.Spec Require Import Prelim.
From OSSVerify.Proofs.boost_beast.http_request.lib.RB Require Import RBMem RBShape DList.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import ASegs AsShadow AsConst AsImgSh AsIface AsIface5 AsIface6 AsIface8 AsCXXHeap AsWalk AsStack0 AXPres AXKit AXRep AXRep2 AXPRep AXPRep2
     AXRep_fields AXRep_mbuf X8_F_insert2 X8_F_insert4 AsTRList.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import X8Kit X8SRKit X8_A_kit13 AXImgKit X8_cobj X8_rsfree
     X8_asio_stmt_alloc X8_asio_stmt_reg X8_asio_stmt_reg2 X8_asio_stmt_reg3 X8_asio_stmt_sched3 X8_asio_stmt_sp2 X8_asio_stmt_use
     X8_stream_stmt X8_stream_stmt2 X8_sct_stmt X8_state1_stmt X8_state2_stmt X8_P_ftab_rep X8_pst X8_put_stmt X8_read_stmt X8_sro_stmt X8_dtor_stmt X8_D_dl X8_D_mb
     AXFuzz_stmt X8_H_stmt X8_H_C X8_H_D X8_H_E X8_H_F X8_H_G X8_H_G2 X8_H_H X8_H_cost.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section HCW.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  Hypothesis H8 : asan_rt_hyps8 H.
  Variable MA : Z.

  (* [comment removed for export] *)
  Definition hzK4p (gp tp s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : as_St H) (LB : list block) (LF : list fframe) (D N lo B shi : Z) (sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 : word)
      (m0 : mem) (mo : Model) : config -> Prop :=
    fun cf => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem) (errv : word) (s' : as_St H) (spa ff fp : Z) (gap : list cell) (p1 : bptr) (allocb : Z) (p2 : bptr) (regb : Z) (p3 : bptr) (cfgb : Z) (p4 : bptr) (schedb : Z) (j8 j4 j16 j40 j40b j472 pad7 pad2 : list byte) (XS : list (Z * Z)) (q1 : bptr) (v : Z) (q2 : bptr) (q : Z) (q3 : bptr) (stb : Z) (q4 : bptr) (va : Z) (q5 : bptr) (A : Z) (PBn PB FBB : list block) (FB Fs : fbv) (fds sds : list byte) (nr : Z) (c : pcore) (S L : list Z) (ns : NS) (ls : LS) (em : gmap Z elt) (h : hdrv) (es : list mbe) (out insz outpos outend : Z),
      as_VIS H s' (cfg_ms cf) = MS (mkR (Z_to_bv 64 P_HZ_RET_SRO) (Z_to_bv 64 spa) gp tp t0 t1 t2 sp (Z_to_bv 64 spa) a0 a1 a2 a3 a4 a5 a6 a7
                                       (Z_to_bv 64 ff) (Z_to_bv 64 (Z.shiftr ff 3 + 2147450880)) (Z_to_bv 64 (ff + 128)) (Z_to_bv 64 (ff + 64))
                                       (Z_to_bv 64 (ff + 192)) (Z_to_bv 64 (ff + 272)) (Z_to_bv 64 (ff + 280)) (Z_to_bv 64 ff) (Z_to_bv 64 2147450880) s11 t3 t4 t5 t6)
                                  F (ret_pc (Z_to_bv 64 P_HZ_RET_SRO)) fc None m (seg_rom asegs)
      /\ (spa = bv_unsigned sp + -192 \/ spa = bv_unsigned sp + -208)
      /\ fresh_frame H LF 4 ff fp
      /\ as_AKREL H s' cf
      /\ as_MPRES H mo (cfg_model cf)
      /\ as_RHEAP H s LB m0
      (* [comment removed for export] *)
      /\ as_RHEAP H s' (PBn ++ (hz_LB2 N q5 A q1 v q2 q q3 stb q4 va p1 allocb p2 regb p3 cfgb p4 schedb LB)) m
      /\ Permutation PBn (PB ++ FBB)
      /\ (forall b, In b PB -> apowned em h es b)
      /\ (forall b, In b (FBB ++ (hz_LB2 N q5 A q1 v q2 q q3 stb q4 va p1 allocb p2 regb p3 cfgb p4 schedb LB)) -> ~ apowned em h es b)
      /\ fbb_ok FB FBB
      (* [comment removed for export] *)
      /\ rw_cells asegs m (ff + 192) (ParserCoreCells c pad7 pad2)
      /\ rw_cells asegs m (ff + 480) [C8 (wz 0)]
      /\ rw_cells asegs m (ff + 528) [C8 (wz 0)]
      /\ AFieldsC m (ff + 272) S L ns ls em
      /\ AFieldsOwn (PBn ++ (hz_LB2 N q5 A q1 v q2 q q3 stb q4 va p1 allocb p2 regb p3 cfgb p4 schedb LB)) em
      /\ rw_cells asegs m (ff + 320) (HdrCells h)
      /\ HdrOwnA (PBn ++ (hz_LB2 N q5 A q1 v q2 q q3 stb q4 va p1 allocb p2 regb p3 cfgb p4 schedb LB)) m h
      /\ HdrDisjP em h
      /\ AMBraw m (ff + 360) es out insz outpos outend
      /\ AMBufOwn (PBn ++ (hz_LB2 N q5 A q1 v q2 q q3 stb q4 va p1 allocb p2 regb p3 cfgb p4 schedb LB)) es
      /\ BodyDisjP em h es
      /\ (forall x sz, In (x, sz) es -> 512 <= sz)
      /\ hdrs_off h (ff + 192) PARSER_SIZE
      /\ accessible m (ff + 192) PARSER_SIZE
      /\ mb_cost H es + bf_cost H L em h <= as_Cf H (sro_phi0 N)
      (* [comment removed for export] *)
      /\ AFlatBuf (PBn ++ (hz_LB2 N q5 A q1 v q2 q q3 stb q4 va p1 allocb p2 regb p3 cfgb p4 schedb LB)) m (spa + 48) FB fds
      /\ fb_cap FB <= CAPMAX N
      /\ (FB <> FB_empty -> blk_fresh H (hz_LB2 N q5 A q1 v q2 q q3 stb q4 va p1 allocb p2 regb p3 cfgb p4 schedb LB) spa (fb_begin FB) (fb_cap FB))
      /\ rw_cells asegs m (spa + 16) (BasicStreamCells stb)
      /\ AStateBlock (PBn ++ (hz_LB2 N q5 A q1 v q2 q q3 stb q4 va p1 allocb p2 regb p3 cfgb p4 schedb LB)) m stb (ff + 128) q (mkST (mkSPC AVP_SPCI_STATE 1 1 1) 0 Fs STREAM_EOF nr (N - zlength sds)) sds
      /\ ((N = 0 /\ Fs = FB_empty) \/ (1 <= N /\ fb_begin Fs = A /\ fb_end Fs = A + N))
      (* [comment removed for export] *)
      /\ rw_cells asegs m spa [CB 8 j8; C8 (Z_to_bv 64 ff)]
      /\ rw_cells asegs m (spa + 96) gap
      /\ Z.of_nat (cells_size gap) = bv_unsigned sp + -96 - (spa + 96)
      /\ rw_cells asegs m (bv_unsigned sp + -96) (hz_saved s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)
      /\ rw_cells asegs m ff (hz_hdr spa ++ [C8 (Z_to_bv 64 AVP_CFGMAKER); C4 (wz 4294967295); CB 4 j4] ++ [CB 16 j16])
      /\ rw_cells asegs m (ff + 88) ([CB 40 j40] ++ [C8 (Z_to_bv 64 allocb); C8 (Z_to_bv 64 regb); C8 (Z_to_bv 64 schedb)] ++ [CB 40 j40b])
      /\ rw_cells asegs m (ff + 544) [CB 472 j472; C8 (Z_to_bv 64 fp)]
      /\ rw_cells asegs m (Z.shiftr ff 3 + 2147450880) hz_sh3
      /\ rw_cells asegs m fp [C1 (b8 1)]
      (* [comment removed for export] *)
      /\ AScheduler (PBn ++ (hz_LB2 N q5 A q1 v q2 q q3 stb q4 va p1 allocb p2 regb p3 cfgb p4 schedb LB)) m schedb (mkSCH (sched_hdr (ff + 128) cfgb) 0 0 0)
      /\ ARegistry (PBn ++ (hz_LB2 N q5 A q1 v q2 q q3 stb q4 va p1 allocb p2 regb p3 cfgb p4 schedb LB)) m regb (ff + 128) v 0
      /\ AConfigSvc (PBn ++ (hz_LB2 N q5 A q1 v q2 q q3 stb q4 va p1 allocb p2 regb p3 cfgb p4 schedb LB)) m cfgb (cfg_hdr (ff + 128))
      /\ AAllocImpl (PBn ++ (hz_LB2 N q5 A q1 v q2 q q3 stb q4 va p1 allocb p2 regb p3 cfgb p4 schedb LB)) m allocb
      /\ AStreamSvc (PBn ++ (hz_LB2 N q5 A q1 v q2 q q3 stb q4 va p1 allocb p2 regb p3 cfgb p4 schedb LB)) m v (mkSVC AVP_SSVC 0 AG_ID_SSVC (ff + 128) schedb P_A_DESTROY_ALLOC_SSVC) q
      /\ AImplBlock (PBn ++ (hz_LB2 N q5 A q1 v q2 q q3 stb q4 va p1 allocb p2 regb p3 cfgb p4 schedb LB)) m q (impl_after va stb)
      /\ rblock_range v NEWSZ_SSVC
      /\ rblock_range q SZ_SPCI_IMPL
      /\ rblock_range stb SZ_SPCI_STATE
      /\ rblock_range va 8
      /\ (1 <= N -> rblock_range A N /\ (A + N <= stb \/ stb + SZ_SPCI_STATE <= A))
      (* [comment removed for export] *)
      /\ AXImg m
      /\ acanary m
      /\ AHStat FT m
      /\ rw_cells asegs m AERRNO [C4 errv]
      /\ as_rauxv_ok H m B
      /\ mem_inv asegs m
      /\ stk asegs m lo spa
      /\ as_RFS H ((4, ff, fp) :: LF) m
      /\ ACONST m
      /\ stack0 m lo shi
      /\ athr_cells m
      /\ accessible m (spa + 16) 32
      /\ accessible m (spa + 48) 48
      /\ Forall (fs_scratch H ((4, ff, fp) :: LF)) XS
      /\ xpres H LB (bv_unsigned sp) ((fr4_XS H ff fp ++ [(AERRNO, AERRNO + 4); (AXH_LO, AXH_HI)]%Z) ++ XS) m0 m
      /\ as_AL H s' >= as_AL H s - (hz_cost2 H N + (as_Cm H MA - as_Cm H 0)).


  Lemma hz_E4p : forall (gp s11 : word) (F : bvmap 5 word) (fc : bv 32) (s : as_St H) (LB : list block) (LF : list fframe)
      (D N lo B shi : Z) (sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 : word) (m0 : mem) (mo : Model) (cf : config),
    hz_pure H sp ra D N lo B shi LB LF ->
    hzK4 H MA gp (Z_to_bv 64 ATP) s11 F fc s LB LF D N lo B shi sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m0 mo cf ->
    hzK4p gp (Z_to_bv 64 ATP) s11 F fc s LB LF D N lo B shi sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 m0 mo cf.
  Proof.
    intros until cf. intros PU K.
    pose proof PU as (SPAL & CEIL & LO & SPB & BHI & SP47 & RAE & NR & DAL & D0 & DNH & SHI & INB & DEMP & LFN & BUD & BUDC).
    unfold AFUZZ_STACK in LO.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
    pose proof aceil_facts as (AF1 & AF2 & AF3). pose proof (ah_costs H HH) as (CM0 & CMM & CF0 & CFM & CMS & CFS).
    destruct cf as [msF4 mo4]. unfold hzK4 in K. cbn [cfg_ms cfg_model] in K.
    destruct K as (z0 & z1 & z2 & g0 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & z3 & z4 & z5 & z6 & m4 & errv4 & s4' & spa & ff & fp & gap
                 & p1 & allocb & p2 & regb & p3 & cfgb & p4 & schedb & j8 & j4 & j16 & j40 & j40b & j472 & pad7 & pad2 & j13 & j32a & j8a & j32b & j8b & XS
                 & q1 & v & q2 & q & q3 & stb & q4 & va & q5 & A & m3 & mo3 & w & E'
                 & VIS & SPA & FF & KREL & MP & HP0 & ST & RWM & RWP & ECOK & EALT & EDONE & LOCh & GAP & GSZ & SAVED & FRMh & FRMi & FRMB & SH & FL
                 & SCH & REG & CFG & AI & SSV & IMP & RBV & RBQ & RBS & RBA & RBAN & XI & CA & FXS & X0 & AL).
    assert (SPAR : bv_unsigned sp + -208 <= spa <= bv_unsigned sp + -192) by (clear - SPA; lia).
    set (LB2 := hz_LB2 N q5 A q1 v q2 q q3 stb q4 va p1 allocb p2 regb p3 cfgb p4 schedb LB) in *.
    (* [comment removed for export] *)
    unfold RWm, sro_C in RWM. cbn_w_all.
    destruct RWM as (PC & UW & HOWN & RDI & J13 & J32a & J8a & J32b & J8b & HC & FTS & MV & FBU & EC & BS & SB & HP & ERR & AUX & MI
                     & RF & AC & SK & THR & PACC & EACC & ESV & BACC & FACC & ASV).
    unfold RWp, sro_C in RWP. cbn_w_all.
    destruct RWP as (PCOK & OWN & MOWN & DISJ & EH & U01 & CAP & LES & INZ & LEN1 & HDJ & HL8 & SK62 & AOWN & PERM & FOK & FRL & FRB & FRT & FRM & FRF
                     & DJL & DJB & DJT & DJM & OFFP & OFFE & STRM & SZS & NRK & CPM & BY & CN & IZ & A0 & AMA).
    destruct w as [d PB FBB FB fds Fs sds nr]. destruct d as [c S L ns ls em h u es insz g rdi PBn Aw]. cbn_w_all.
    destruct UW as (FC & HDR & USED & MB & RD & MRG & CBH & CBB & PFT & FI & XS2). cbn_w_all.
    pose proof FC as (_ & _ & _ & _ & _ & _ & _ & LEQ & _).
    destruct MB as [MBR MOK]. destruct HDJ as (J1 & J2 & J3 & J4 & J5).
    assert (EA : errno_addr (Z_to_bv 64 ATP) = AERRNO) by (unfold AERRNO, ATP; rewrite unsigned_lit; lia). rewrite EA in ERR.
    unfold O_PR_HDR in HDR.
    replace (ff + 192 + 80) with (ff + 272) in FC by (clear; lia). replace (ff + 192 + 128) with (ff + 320) in HDR by (clear; lia).
    replace (ff + 192 + 168) with (ff + 360) in MBR by (clear; lia).
    replace (ff + 192 + 288) with (ff + 480) in CBH by (clear; lia). replace (ff + 192 + 336) with (ff + 528) in CBB by (clear; lia).
    idtac "E4p unpacked".
    (* [comment removed for export] *)
    assert (INPB : forall b, In b PB -> In b (PBn ++ LB2)).
    { intros b Hb. apply in_or_app. left. eapply Permutation_in; [apply Permutation_sym; exact PERM|]. apply in_or_app. left. exact Hb. }
    assert (MSZ : forall x sz, In (x, sz) es -> 512 <= sz) by (intros x sz IN; exact (proj1 (mb_ok_size _ _ _ _ MOK IN))).
    assert (PBO : forall b, In b PB -> apowned em h es b).
    { intros b Hb. destruct (AOWN b Hb) as [[KL KS] | [K | [K | K]]].
      - left. left. destruct (proj1 (LEQ _) KL) as [dd Ld]. exists dd. split; [exact Ld|].
        destruct (OWN _ _ Ld) as [pe [INe _]].
        pose proof (ablk_same H HH _ _ _ b (pe, blk_addr b, esize dd) HP (INPB _ Hb) INe eq_refl) as EQ.
        rewrite EQ. reflexivity.
      - left. right. left. exact K.
      - left. right. right. exact K.
      - right. exact K. }
    assert (NPO : forall b, In b (FBB ++ LB2) -> ~ apowned em h es b).
    { intros b Hb K. apply in_app_or in Hb. destruct Hb as [Hb | Hb].
      - (* [comment removed for export] *)
        destruct FOK as [[_ ->] | (NE & pf & ->)]; [exact Hb|]. destruct Hb as [<- | []]. cbn in K.
        destruct FBU as (_ & FBOK & _). destruct FBOK as [K0 | (pf' & _ & _ & BCP & _)]; [exfalso; exact (NE K0)|].
        destruct K as [[(dd & Ld & SZ) | [(ML1 & AB & SB1) | (TL1 & AB & SB1)]] | (sz & IN & SZ)]; cbn [blk_addr blk_size fst snd] in *.
        + destruct (DJL NE (fb_begin FB) ltac:(apply (proj2 (LEQ _)); rewrite Ld; eexists; reflexivity)); unfold fb_cap in BCP; clear - H0 BCP; lia.
        + destruct (DJM NE ltac:(clear - ML1; lia)); unfold fb_cap in BCP; clear - H0 BCP ML1 AB; lia.
        + destruct (DJT NE ltac:(clear - TL1; lia)); unfold fb_cap in BCP; clear - H0 BCP TL1 AB; lia.
        + pose proof (MSZ _ _ IN) as SZ'. destruct (DJB NE _ _ IN); unfold fb_cap in BCP; clear - H0 BCP SZ'; lia.
      - (* [comment removed for export] *)
        assert (RC : aclient_range H LB2 spa (blk_addr b) (blk_size b)) by (right; right; left; exists b; split; [exact Hb | clear; lia]).
        destruct (ah_blocks H HH _ _ _ b HP ltac:(apply in_or_app; right; exact Hb)) as (_ & _ & Q3 & _).
        destruct K as [[(dd & Ld & SZ) | [(ML1 & AB & SB1) | (TL1 & AB & SB1)]] | (sz & IN & SZ)].
        + pose proof (esize_ge dd) as EG.
          destruct (FRL (blk_addr b) ltac:(apply (proj2 (LEQ _)); rewrite Ld; eexists; reflexivity) _ _ RC ltac:(clear - SZ EG; lia)); clear - H0 SZ EG; lia.
        + rewrite <- AB in FRM. destruct (FRM ltac:(clear - ML1; lia) _ _ RC ltac:(clear - SB1 ML1; lia)); clear - H0 ML1 SB1; lia.
        + rewrite <- AB in FRT. destruct (FRT ltac:(clear - TL1; lia) _ _ RC ltac:(clear - SB1 TL1; lia)); clear - H0 TL1 SB1; lia.
        + pose proof (MSZ _ _ IN) as SZ'. pose proof (mb_block_size_range sz ltac:(clear - SZ'; lia)) as [BR _].
          destruct (FRB _ _ IN _ _ RC ltac:(clear - SZ SZ' BR; lia)); clear - H0 SZ SZ' BR; lia. }
    idtac "E4p owned".
    assert (HDJ' : HdrDisjP em h).
    { split; [| split].
      - intros ML. destruct (em !! hv_mp h) as [dd|] eqn:Ld; [exfalso | reflexivity].
        destruct (J2 ltac:(clear - ML; lia) (hv_mp h) ltac:(apply (proj2 (LEQ _)); rewrite Ld; eexists; reflexivity)); clear - ML H0; lia.
      - intros TL. destruct (em !! hv_tp h) as [dd|] eqn:Ld; [exfalso | reflexivity].
        destruct (J1 ltac:(clear - TL; lia) (hv_tp h) ltac:(apply (proj2 (LEQ _)); rewrite Ld; eexists; reflexivity)); clear - TL H0; lia.
      - intros ML TL. destruct (J5 ltac:(clear - ML; lia) ltac:(clear - TL; lia)); clear - ML TL H0; lia. }
    assert (BDJ : BodyDisjP em h es).
    { intros x sz IN. pose proof (MSZ _ _ IN) as SZ. split; [| split].
      - destruct (em !! x) as [dd|] eqn:Ld; [exfalso | reflexivity]. pose proof (esize_ge dd) as EG.
        pose proof (mb_block_size_range sz ltac:(clear - SZ; lia)) as [BR _].
        destruct (DISJ x dd Ld x sz IN); clear - SZ EG BR H0; lia.
      - intros ML. destruct (J4 ltac:(clear - ML; lia) x sz IN); clear - SZ ML H0; lia.
      - intros TL. destruct (J3 ltac:(clear - TL; lia) x sz IN); clear - SZ TL H0; lia. }
    (* [comment removed for export] *)
    assert (COST : mb_cost H es + bf_cost H L em h <= as_Cf H (sro_phi0 N)).
    { assert (OPB : forall b, In b (PBn ++ LB2) -> apowned em h es b -> In b PBn).
      { intros b Hb K. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [exact Hb|]. exfalso. apply (NPO b); [apply in_or_app; right; exact Hb| exact K]. }
      assert (PBL : forall b, In b PBn -> In b (PBn ++ LB2)) by (intros b Hb; apply in_or_app; left; exact Hb).
      pose proof (pd_cost_le H HH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PBn HP FC OWN MBR MOWN ltac:(intros x sz IN; pose proof (MSZ _ _ IN); clear - H0; lia)
                    HOWN DISJ (conj J1 (conj J2 (conj J3 (conj J4 J5)))) OPB PBL) as W1.
      (* [comment removed for export] *)
      rewrite lb_bytes_app in BY.
      assert (FBBN : lb_bytes FBB <= CAPMAX N).
      { destruct FOK as [[_ ->] | (NE & pf & ->)]; cbn; [unfold CAPMAX; clear - NR; lia|]. rewrite Z.add_0_r. exact CPM. }
      pose proof (pot_if_range (pc_state c)) as (PI & _). unfold body_res in BY.
      pose proof PCOK as (_ & _ & _ & _ & _ & HLR & _).
      assert (ZL : 0 <= zlength fds + zlength sds) by (unfold zlength; clear; lia).
      pose proof (lb_bytes_nonneg H HH _ _ _ PBn HP PBL) as NN.
      apply (Z.le_trans _ _ _ W1). apply CFM. clear - BY FBBN PI HLR ZL NN CAP LES INZ NR. unfold CAPMAX in *. lia. }
    idtac "E4p cost".
    unfold hzK4p. cbn [cfg_ms cfg_model]. fold LB2.
    exists z0, z1, z2, g0, g1, g2, g3, g4, g5, g6, g7, z3, z4, z5, z6, m4, errv4, s4', spa, ff, fp, gap.
    exists p1, allocb, p2, regb, p3, cfgb, p4, schedb, j8, j4, j16, j40, j40b, j472, pad7, pad2, XS, q1, v, q2, q, q3, stb, q4, va, q5, A.
    exists PBn, PB, FBB, FB, Fs, fds, sds, nr, c, S, L, ns, ls, em, h, es, (mb_out (ff + 360) es insz), insz, (mb_outpos es insz), (mb_outpos es insz).
    split; [exact VIS|]. split; [exact SPA|]. split; [exact FF|]. split; [exact KREL|]. split; [exact MP|]. split; [exact HP0|].
    split; [exact HP|]. split; [exact PERM|]. split; [exact PBO|]. split; [exact NPO|]. split; [exact FOK|].
    split; [exact PC|]. split; [exact CBH|]. split; [exact CBB|]. split; [exact FC|]. split; [exact OWN|].
    split; [exact HDR|]. split; [exact HOWN|]. split; [exact HDJ'|]. split; [exact MBR|]. split; [exact MOWN|]. split; [exact BDJ|]. split; [exact MSZ|].
    split; [exact (proj2 (proj2 OFFP))|]. split; [exact PACC|]. split; [exact COST|].
    split; [exact FBU|]. split; [exact CPM|]. split; [exact FRF|]. split; [exact BS|]. split; [exact SB|].
    split; [clear - STRM; destruct STRM as [K|(K1 & K2 & K3)]; [left; exact K| right; repeat split; assumption]|].
    split; [exact LOCh|]. split; [exact GAP|]. split; [exact GSZ|]. split; [exact SAVED|]. split; [exact FRMh|]. split; [exact FRMi|]. split; [exact FRMB|].
    split; [exact SH|]. split; [exact FL|].
    split; [exact SCH|]. split; [exact REG|]. split; [exact CFG|]. split; [exact AI|]. split; [exact SSV|]. split; [exact IMP|].
    split; [exact RBV|]. split; [exact RBQ|]. split; [exact RBS|]. split; [exact RBA|]. split; [exact RBAN|].
    split; [exact XI|]. split; [exact CA|]. split; [split; [exists g; exact HC| exact FTS]|].
    split; [exact ERR|]. split; [exact AUX|]. split; [exact MI|]. split; [exact ST|].
    split; [exact RF|]. split; [exact AC|]. split; [exact SK|]. split; [exact THR|]. split; [exact BACC|]. split; [exact FACC|].
    split; [exact FXS|]. split; [exact X0| exact AL].
  Qed.
End HCW.
