(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm ZdDCtx ZdSeqTable.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk InitMem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import DrvAgree FseWalkKit FseRdKit FseRdKit2 MemRange SepHide ZdWalkKit ZdDctxRep ZdSeqW ZdTbl.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase RtCells AProto AMalloc_iface AProg_kit AFake_iface AFakeK_iface AZ_kit AZ_kx AZ_globals AZ_globalsR AZ_fkit
     AZ_libc_iface AZ_seq_iface AZ_huf_iface AZ_seq_bit_iface AZ_dbs_iface AZ_seq_kit AZ_seq_gkit AZ_seq_l_base AZ_seq_l_lbase AZ_seq_l_lkit AZ_seq_l_akit AZ_seq_l_okit AZ_seq_l_ibase
     AZ_seq_l_sbase AZ_seq_l_fin AZ_seq_l_last2 AZ_seq_l_lastx AZ_seq_l_body AZ_seq_l_iat AZ_seq_l_ikit AZ_seq_l_ibody AZ_seq_l_ekit2 AZ_seq_l_akit2 AZ_seq_l_ent AZ_seq_l_open.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKitF.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac rd_retlit := lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
  replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end.
Notation FB2 F := (mkABlock (ABFake 2) F 256).
Notation SHB := 2147450880.

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Lemma aheap_pres_stk_blk : forall CI LB SP (m m' : amem) lo hi,
  aheap_pres CI LB SP m m' -> stk bsegs m lo hi -> aclient_range CI LB SP lo (hi - lo) -> stk bsegs m' lo hi.
Proof.
  intros CI LB SP m m' lo hi HP ST HR. destruct ST as (H0 & H1 & HW). split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct (HP i ltac:(lia) ltac:(eapply aclient_range_addr; [exact HR | lia])) as [E W]. destruct (HW i Hi) as [W0 [b Hb]].
  split; [apply W, W0|]. exists b. unfold mrd in *. rewrite E. exact Hb.
Qed.
Lemma aheap_pres_rdbl_blk : forall CI LB SP (m m' : amem) lo hi,
  aheap_pres CI LB SP m m' -> rdbl bsegs m lo hi -> aclient_range CI LB SP lo (hi - lo) -> rdbl bsegs m' lo hi.
Proof.
  intros CI LB SP m m' lo hi HP (H0 & H1 & HR') HR. split; [exact H0|]. split; [exact H1|].
  intros x Hx. destruct (HP x ltac:(lia) ltac:(eapply aclient_range_addr; [exact HR | lia])) as [E _].
  destruct (HR' x Hx) as [b Hb]. exists b. unfold mrd in *. rewrite E. exact Hb.
Qed.

Section Thm.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variable fflag : alayout -> Z -> Z -> Z.
  Variable rng_fs : alayout -> footprint -> Prop.
  Hypothesis SM2K : forall k, (k < 4096)%nat -> stack_malloc_2k_stmt AI fflag rng_fs k.
  Hypothesis FFLAG : fake_flag_law AI fflag.
  Hypothesis FRL : fake_release_law AI fflag.
  Hypothesis FHL : fake_heap_law AI.

  Theorem zd_seq_long_proofA : zd_execend_stmtA -> zd_execend_split_stmtA -> zd_memmoveZ_stmtA -> zd_seq_long_stmtA AI rng_fs.
  Proof.
    intros EXE EXS MMV.
    intros L RNG st LB ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m
           SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws.
    intros DCX LIT R1 R2 D8M SQB AB R3 R4 R5 TB BUF R6 PF R7 R8 R9 DZ DNZ LOCD R10 R11 HLSZ R12 LRD PLACED STK R15 R13 R14 O1 O2 O3 O4 OT A1 A2 AT A3 A4 ATB
           BB1 CAPNZ AFP TP AZS ARD AHD IND ARS INS INT AROT ACL TM8 AOUT ARL AHL INL MI.
    intros -> -> -> -> -> ->.
    cbv beta in LOCD.
    unfold off_stack in O1, O2, O3, O4. unfold apart in A1, A2, A3, A4.
    unfold DCTX_SIZEOF, WILDCOPY_OVERLENGTH, DCTX_entropy_rep, DCTX_litExtraBuffer, DCTX_litExtraBuffer_sz in *.
    unfold seq_lit_placed, ZSTD_split, ZSTD_in_dst, ZSTD_not_in_dst, apart, WILDCOPY_OVERLENGTH, DCTX_litExtraBuffer, DCTX_litExtraBuffer_sz in PLACED. unfold ZSTD_split, ZSTD_in_dst, ZSTD_not_in_dst in LOCD, A4.
    (* [comment removed for export] *)
    assert (Y7 : LOC = 1 -> DST <= LITB <= DST + CAP /\ LITB <= LITP /\ LBE + 32 <= B1) by (intros E; destruct PLACED as [(E' & _) | [(_ & P1 & P2 & P3) | (E' & _)]]; [exfalso; clear - E E'; lia | split; [exact P1 | split; [exact P2 | exact P3]] | exfalso; clear - E E'; lia]).
    assert (Y8 : LOC = 0 -> LITP + (LBE + 32 - LITP) <= B0 \/ B0 + (B1 - B0) <= LITP) by (intros E; destruct PLACED as [(_ & P1) | [(E' & _) | (E' & _)]]; [exact P1 | exfalso; clear - E E'; lia | exfalso; clear - E E'; lia]).
    assert (Y9 : LOC = 2 -> DST <= LITP /\ LBE + 32 <= DST + CAP) by (intros E; destruct PLACED as [(E' & _) | [(E' & _) | (_ & P1 & P2 & _)]]; [exfalso; clear - E E'; lia | exfalso; clear - E E'; lia | split; [exact P1 | exact P2]]).
    assert (XRD : LOC = 2 -> rdbl bsegs m (DCTX + 30372) (DCTX + 30372 + 65568)) by (intros E; destruct PLACED as [(E' & _) | [(E' & _) | (_ & _ & _ & XR)]]; [exfalso; clear - E E'; lia | exfalso; clear - E E'; lia | exact XR]).
    clear PLACED.
    hide_all_disj.
    destruct AFP as (AH & ASH & ART & (KHI & RSTK & RI) & RFS & BOT & SPT & SP16 & RSTKT & LBH).
    pose proof atop_range as ATR.
    pose proof (AI_layout AI _ _ _ _ _ AH) as (LY1 & LY2 & LY3 & LY4 & LY5).
    destruct (FHL _ _ _ _ _ AH) as [FAB _]. pose proof (fk_ablk_lits _ _ FAB) as FABL.
    pose proof (AI_rtcells AI _ _ _ _ _ AH) as RTC. unfold artcells in RTC.
    destruct RTC as (C0 & GOT & RIC & REAL & SHBc & SUA & _).
    destruct (sl_got_cells m (AI_relro AI _ _ _ _ _ AH)) as [G1 G2].
    assert (LOC' : ATOP <= lo) by (clear - BOT; lia).
    assert (SPK : SPV + 16 < KEND) by (unfold KEND; clear - SPT LY3; lia).
    assert (LO0 : 0 <= lo) by (clear - R15; lia).
    assert (LOSb : lo <= SPV - 768 - 4096) by (clear - R13; lia).
    assert (LOSa : lo <= SPV - 704 - 4096) by (clear - LOSb; lia).
    assert (SPAB : SPV - 704 <= SLFRB SPV <= SPV - 672) by (clear; unfold SLFRB; Z.div_mod_to_equations; lia).
    assert (SPA32 : SLFRB SPV mod 32 = 0) by (clear; unfold SLFRB; Z.div_mod_to_equations; lia).
    assert (KHI' : 17594333495296 <= lo) by (unfold KHIGH in KHI; exact KHI).
    unfold APZD_SEQ_LONG.
    (* [comment removed for export] *)
    eapply evtF_cut.
    { eapply (sl_pro ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc SPV lo);
        first [exact STK| exact MI| exact SHBc| exact G1| exact G2| exact SUA| exact SP16| exact SPK| exact LOSa| exact LOC'| exact RSTK| exact RI]. }
    cbv beta. intros ms' (m1 & jA & jB & -> & MU1' & WM1 & MI1 & SAV1 & FRA1 & STL1 & STG1).
    assert (MU1 : munch [(SPV - 768, SPV)] m m1) by (eapply munch_weaken; [| exact MU1']; unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx; lia).
    clear C0 GOT RIC REAL SHBc SUA G1 G2.
    assert (AH1 : AHEAP AI L RNG st LB m1).
    { eapply (AI_frame AI); [exact AH| exact MU1| exact WM1|]. constructor; [| constructor]. left; left. cbn. clear - BOT LOSb SPT LY3; lia. }
    (* [comment removed for export] *)
    pose proof (ASH 2 ltac:(clear; lia)) as FLE.
    assert (USF : bv_unsigned (Z_to_bv 64 (SLFRB SPV)) = SLFRB SPV) by (apply unsigned_lit; clear - SPAB R14 LOSb R15; lia).
    eapply evtF_cut.
    { pose proof (SM2K (Z.to_nat (4096 - 1)) ltac:(apply (proj1 (Nat.ltb_lt _ _)); vm_compute; reflexivity)) as SMC. unfold stack_malloc_2k_stmt in SMC.
      eapply SMC with (lo := lo); clear SMC; rewrite ?USF;
        [exact AH1| exact FLE| exact MI1| exact STL1| clear - BOT; lia| unfold SMK_STACK; clear - SPAB LOSb; lia| clear - SPAB SPT; lia| exact TP| exact RSTKT| exact RI| exact RFS]. }
    cbv beta. intros ms' PO.
    destruct PO as (FF & z5 & z6 & z7 & e11 & e12 & e13 & e14 & e15 & e16 & e17 & z28 & z29 & z30 & z31 & m2 & j0 & j1 & j2 & junk
                    & -> & MI2 & ST2 & HPR2 & AH2 & F256 & FH & FC & FFC2 & SHF2 & RFF & RSFF & MUF2 & WM2 & FFA1 & FFA2).
    rewrite ?USF in ST2, HPR2, MUF2.
    rd_retlit.
    pose proof (ablk_lin _ _ FH) as (FHa & FHb & FHc & FHd). unfold AIMG_HI in FHa.
    pose proof (fk_frame_apart AI _ _ _ _ _ _ _ _ AH2) as FFD.
    pose proof (aheap_pres_rw_cells _ _ _ _ _ _ _ HPR2 SAV1 ltac:(left; left; cbn; clear - SPAB SPT LY3; lia)) as SAV2.
    pose proof (aheap_pres_rw_cells _ _ _ _ _ _ _ HPR2 FRA1 ltac:(left; left; cbn; clear - SPAB SPT LY3; lia)) as FRA2.
    pose proof (aheap_pres_stk _ _ _ _ _ _ _ HPR2 STG1 ltac:(clear; lia) ltac:(clear - SPT LY3; lia)) as STG2.
    pose proof (ARD ltac:(clear; lia)) as (ABD & UD0 & RD1 & RD2). pose proof (fk_ablk_lits _ _ ABD) as DL.
    pose proof (fk_inblk_apart AI _ _ _ _ _ _ _ _ DCTX 95992 AH2 IND ltac:(clear; lia)) as APD.
    assert (INLB : forall b, In b LB -> In b (FB2 FF :: LB)) by (intros b Hb; right; exact Hb).
    assert (DS1 : forall X n, 0 <= X -> 0 <= n -> X + n <= 2^47 -> disjoint_from [(SPV - 768, SPV)] (shad X) (shad (X + n - 1) + 1 - shad X)).
    { intros X nn X0 Hn Hb. cbn [disjoint_from]. split; [| exact I]. left. rewrite !shad_div. unfold ASHOFF in *. clear - X0 Hn Hb ATR BOT LOSb. Z.div_mod_to_equations. lia. }
    assert (UD2 : unpoisoned m2 DCTX (DCTX + 95992)).
    { eapply (fk_unp_pres AI); [exact AH2| exact INLB| exact HPR2| exact IND| clear; lia|].
      eapply unpoisoned_munch; [exact UD0| exact MU1| apply DS1; [clear - R1; lia| clear; lia| clear - R2; lia]]. }
    pose proof (fk_unp_shadow_zero m2 DCTX 95992 (DCTX + 30368) UD2 ltac:(clear; lia) ltac:(clear; Z.div_mod_to_equations; lia)) as D8A.
    assert (DRS : rng RNG (shad (DCTX + 30368)) 1) by (eapply rng_sub'; [exact RD2|]; unfold shspan; rewrite !shad_div; clear; Z.div_mod_to_equations; lia).
    (* [comment removed for export] *)
    eapply evtF_cut.
    { eapply (sl_hdr gp tp FR fc SPV lo);
        first [exact FRA2| exact ST2| exact FFC2| exact SHF2| exact MI2| exact FH| exact FC| exact F256| exact RFF| exact RSFF| exact D8A| exact DRS| exact APD|
               exact SP16| exact SPK| exact LOSa| exact LOC'| exact RSTK| exact RI| clear - R1; lia| clear - R2; lia]. }
    cbv beta. intros ms' (m3 & jds & jp & j144 & j8 & jA1 & jA2 & jB1 & jB2 & -> & MU3' & WM3 & MI3 & FRA3 & STL3 & FFC3 & SHF3).
    (* [comment removed for export] *)
    set (D8 := DCTX / 8).
    assert (ED8 : DCTX = 8 * D8) by (subst D8; clear - D8M R1; Z.div_mod_to_equations; lia).
    (* [comment removed for export] *)
    lazymatch type of FRA3 with rw_cells _ ?mx _ (CB 232 ?ja :: ?cs) =>
      apply (rw_cells_split_CB bsegs mx _ [] 232 ja cs [8; 224]%nat) in FRA3; [| reflexivity]; cbn [mk_CB_cells app] in FRA3 end.
    lazymatch type of FRA3 with rw_cells _ ?mx _ [?c0; ?c1; ?c2; ?c3; ?c4; ?c5; ?c6; CB 64 ?jb; ?c8; ?c9] =>
      apply (rw_cells_split_CB bsegs mx _ [c0; c1; c2; c3; c4; c5; c6] 64 jb [c8; c9] [48; 16]%nat) in FRA3; [| reflexivity]; cbn [mk_CB_cells app] in FRA3 end.
    lazymatch type of FRA3 with rw_cells _ ?mx _ [?c0; ?c1; ?c2; ?c3; ?c4; ?c5; ?c6; ?c7; CB 16 ?j6; C8 ?w7; ?c10] =>
      change (rw_cells bsegs mx (SLFRB SPV) ([c0; c1; c2; c3; c4; c5; c6; c7] ++ [CB 16 j6; C8 w7] ++ [c10])) in FRA3;
      apply (rw_cells_merge bsegs mx (SLFRB SPV)) in FRA3; cbn [app cells_size csize Nat.add length] in FRA3 end.
    replace (Z.shiftr (DCTX + 30368) 3 + SHB) with (2147450880 + D8 + 3796) in FRA3
      by (rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; clear - ED8; Z.div_mod_to_equations; lia).
    set (SHF := Z.shiftr FF 3 + SHB) in *.
    assert (ESHF : SHF = shad FF) by (subst SHF; unfold shad, ASHOFF; clear; lia).
    (* [comment removed for export] *)
    assert (MU3 : munch [(FF, FF + 24); (SHF, SHF + 32); (SPV - 768, SPV)] m2 m3).
    { eapply munch_weaken; [| exact MU3']. unfold sub_fp; cbn [outside]. intros x Hx. clear - Hx SPAB. lia. }
    rename MU3' into MU3''.
    assert (BSF : SHB + 788992 <= SHF /\ SHF + 32 <= 17594333495296) by (subst SHF; rewrite Z.shiftr_div_pow2 by lia; clear - FHa FHd; Z.div_mod_to_equations; lia).
    pose proof (fk_ablk_lits _ _ FH) as FL.
    destruct (FFLAG _ _ _ _ _ 2 FF 256 AH2 ltac:(left; reflexivity)) as (XL2 & RL & LBK & LTOP & LAP & _ & LFA).
    (* [comment removed for export] *)
    pose proof (ARL ltac:(clear - R11; lia)) as (ABL & UL0 & RLT1 & RLT2). pose proof (fk_ablk_lits _ _ ABL) as LL.
    pose proof (fk_inblk_apart AI _ _ _ _ _ _ _ _ LITP (LBE + 32 - LITP) AH2 INL ltac:(clear - R11; lia)) as APL.
    assert (INBd : forall A n, DCTX <= A -> A + n <= DCTX + 95992 -> ainblk LB A n).
    { intros A n HA HB. destruct IND as (bd & Hbd & Bd1 & Bd2). exists bd. split; [exact Hbd|]. clear - HA HB Bd1 Bd2. lia. }
    (* [comment removed for export] *)
    assert (D1 : forall X n, (X + n <= lo \/ SPV <= X) -> 0 <= n -> disjoint_from [(SPV - 768, SPV)] X n).
    { intros X nn HX Hn. cbn [disjoint_from]. split; [clear - HX Hn LOSb; lia| exact I]. }
    assert (D3 : forall X n, (X + n <= FF \/ FF + 256 <= X) ->
                 (X + n <= 6443008 \/ (6443008 <= X /\ X + n <= 2147446784) \/ (17594333495296 <= X /\ X + n <= ATOP) \/ lo <= X) -> 0 <= n ->
                 (X + n <= lo \/ SPV <= X) ->
                 disjoint_from [(FF, FF + 24); (SHF, SHF + 32); (SPV - 768, SPV)] X n).
    { intros X nn HF HB Hn HX. cbn [disjoint_from]. split; [clear - HF Hn; lia|]. split; [clear - HB BSF ATR Hn KHI'; lia|]. split; [clear - HX Hn LOSb; lia| exact I]. }
    assert (DS3 : forall X n, 0 <= X -> 0 <= n -> X + n <= 2^47 -> (X + n <= FF \/ FF + 256 <= X) ->
                 disjoint_from [(FF, FF + 24); (SHF, SHF + 32); (SPV - 768, SPV)] (shad X) (shad (X + n - 1) + 1 - shad X)).
    { intros X nn X0 Hn Hb HF. cbn [disjoint_from]. subst SHF. rewrite !shad_div. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. unfold ASHOFF in *.
      split; [clear - X0 Hn Hb FL ATR; Z.div_mod_to_equations; lia|].
      split; [clear - X0 Hn Hb HF F256; Z.div_mod_to_equations; lia|].
      split; [clear - X0 Hn Hb ATR BOT LOSb; Z.div_mod_to_equations; lia| exact I]. }
    assert (MU13 : munch ([(SPV - 768, SPV)] ++ (fake_area L ++ [(SLFRB SPV - SMK_STACK, SLFRB SPV)]) ++ [(FF, FF + 24); (SHF, SHF + 32); (SPV - 768, SPV)]) m m3).
    { eapply munch_trans; [eapply munch_weaken; [| exact MU1]; intros x Hx; clear - Hx; cbn [outside app fake_area] in *; tauto|].
      eapply munch_trans; [eapply munch_weaken; [| exact MUF2]; intros x Hx; clear - Hx; cbn [outside app fake_area] in *; tauto|].
      eapply munch_weaken; [| exact MU3]; intros x Hx; clear - Hx; cbn [outside app fake_area] in *; tauto. }
    assert (WM13 : wmono bsegs m m3) by exact (wmono_trans _ _ _ _ WM1 (wmono_trans _ _ _ _ WM2 WM3)).
    assert (DI13 : forall X n, 0 <= X -> 0 <= n -> X + n <= 6443008 ->
                 disjoint_from ([(SPV - 768, SPV)] ++ (fake_area L ++ [(SLFRB SPV - SMK_STACK, SLFRB SPV)]) ++ [(FF, FF + 24); (SHF, SHF + 32); (SPV - 768, SPV)]) X n
                 /\ disjoint_from ([(SPV - 768, SPV)] ++ (fake_area L ++ [(SLFRB SPV - SMK_STACK, SLFRB SPV)]) ++ [(FF, FF + 24); (SHF, SHF + 32); (SPV - 768, SPV)]) (shad X) (shad (X + n - 1) + 1 - shad X)).
    { intros X nn X0 Hn XH. destruct LY5 as (_ & _ & FA1 & FA2). cbn [disjoint_from fake_area app]. subst SHF. rewrite !shad_div. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
      unfold ASHOFF, AIMG_HI, SMK_STACK, FAKESZ in *.
      split; repeat split; try exact I; clear - X0 Hn XH FL FABL FA1 FA2 ATR BOT LOSb SPAB KHI'; Z.div_mod_to_equations; lia. }
    (* [comment removed for export] *)
    assert (TCb : forall A cs, rw_cells bsegs m A cs -> ainblk LB A (Z.of_nat (cells_size cs)) -> (A + Z.of_nat (cells_size cs) <= lo \/ SPV <= A) ->
                 (A + Z.of_nat (cells_size cs) <= FF \/ FF + 256 <= A) -> ablk A (A + Z.of_nat (cells_size cs)) \/ (exists A0 B0', ablk A0 B0' /\ A0 <= A /\ A + Z.of_nat (cells_size cs) <= B0') ->
                 rw_cells bsegs m3 A cs).
    { intros A cs H IB HX HF HB.
      assert (XL : (6443008 <= A /\ A + Z.of_nat (cells_size cs) <= 2147446784) \/ (17594333495296 <= A /\ A + Z.of_nat (cells_size cs) <= ATOP)).
      { destruct HB as [HB|(A0 & B0' & HB & HA1 & HA2)].
        - pose proof (fk_ablk_lits _ _ HB) as XL; clear - XL; lia.
        - pose proof (fk_ablk_lits _ _ HB) as XL; clear - XL HA1 HA2; lia. }
      eapply rw_cells_transport; [| exact MU3| exact WM3| apply D3; [exact HF| right; clear - XL; lia| clear; lia| exact HX]].
      eapply (fk_cells_pres AI); [exact HPR2| exact IB|].
      eapply rw_cells_transport; [exact H| exact MU1| exact WM1| apply D1; [exact HX| clear; lia]]. }
    assert (UNT : forall X n, unpoisoned m X (X + n) -> ainblk LB X n -> 0 <= n -> 0 <= X -> X + n <= 2^47 -> (X + n <= FF \/ FF + 256 <= X) -> unpoisoned m3 X (X + n)).
    { intros X nn U IB Hn X0 Hb HF.
      eapply unpoisoned_munch; [| exact MU3| apply DS3; [exact X0| exact Hn| exact Hb| exact HF]].
      eapply (fk_unp_pres AI); [exact AH2| exact INLB| exact HPR2| exact IB| exact Hn|].
      eapply unpoisoned_munch; [exact U| exact MU1| apply DS1; [exact X0| exact Hn| exact Hb]]. }
    assert (UNI : forall X n, unpoisoned m X (X + n) -> 0 <= n -> 0 <= X -> X + n <= 6443008 -> unpoisoned m3 X (X + n)).
    { intros X nn U Hn X0 XH. eapply unpoisoned_munch; [exact U| exact MU13| apply (proj2 (DI13 X nn X0 Hn XH))]. }
    assert (BAT : forall T bs, bytes_at bsegs m T bs -> (T + zlen bs <= lo \/ SPV <= T) -> (ainblk LB T (zlen bs) \/ T + zlen bs <= AIMG_HI) -> 4096 <= T ->
                 ablk T (T + zlen bs) \/ T + zlen bs <= AIMG_HI ->
                 bytes_at bsegs m3 T bs /\ (T + zlen bs <= FF \/ FF + 256 <= T)).
    { intros T bs B HX IN T0 HB. unfold AIMG_HI in *. destruct IN as [IB|IM].
      - pose proof (fk_inblk_apart AI _ _ _ _ _ _ _ _ T (zlen bs) AH2 IB ltac:(clear; lia)) as AP.
        assert (XL : (6443008 <= T /\ T + zlen bs <= 2147446784) \/ (17594333495296 <= T /\ T + zlen bs <= ATOP) \/ T + zlen bs <= 6443008).
        { destruct HB as [HB|HB]; [pose proof (fk_ablk_lits _ _ HB) as XL; clear - XL; lia | clear - HB; lia]. }
        split; [| exact AP].
        eapply bytes_at_transport; [| exact MU3| apply D3; [exact AP| clear - XL; lia| clear; lia| exact HX]].
        eapply (fk_bytes_pres AI); [exact HPR2| exact IB|].
        eapply bytes_at_transport; [exact B| exact MU1| apply D1; [exact HX| clear; lia]].
      - split; [| left; clear - IM FHa; lia].
        eapply bytes_at_transport; [exact B| exact MU13| apply (proj1 (DI13 T (zlen bs) ltac:(clear - T0; lia) ltac:(clear; lia) IM))]. }
    (* [comment removed for export] *)
    unfold hidden in O1. unfold hidden in O2. unfold hidden in O3. unfold hidden in O4.
    destruct DCX as (PT0 & REP0 & H10 & H30 & H50 & H5L). unfold dctx_ptrs, dctx_h1, dctx_h3 in PT0, H10, H30.
    assert (DBLK : forall A n, DCTX <= A -> A + n <= DCTX + 95992 -> ablk A (A + n) \/ (exists A0 B0', ablk A0 B0' /\ A0 <= A /\ A + n <= B0')).
    { intros A n HA HB. right. exists DCTX, (DCTX + 95992). split; [exact ABD | clear - HA HB; lia]. }
    assert (PT3 : rw_cells bsegs m3 DCTX [C8 (Z_to_bv 64 LLT); C8 (Z_to_bv 64 MLT); C8 (Z_to_bv 64 OFT); C8 huf]).
    { apply TCb; cbn [cells_size csize Nat.add]; [exact PT0 | apply INBd; clear; lia | clear - O1; lia | clear - APD; lia | apply DBLK; clear; lia]. }
    assert (REP3 : rw_cells bsegs m3 (DCTX + 26684) [C4 r0; C4 r1; C4 r2]).
    { apply TCb; cbn [cells_size csize Nat.add]; [exact REP0 | apply INBd; clear; lia | clear - O1; lia | clear - APD; lia | apply DBLK; clear; lia]. }
    assert (H13 : rw_cells bsegs m3 (DCTX + 29888) [C8 pde; C8 (Z_to_bv 64 PFX); C8 (Z_to_bv 64 PFX); C8 dend; C8 expd]).
    { apply TCb; cbn [cells_size csize Nat.add]; [exact H10 | apply INBd; clear; lia | clear - O1; lia | clear - APD; lia | apply DBLK; clear; lia]. }
    assert (H33 : rw_cells bsegs m3 (DCTX + 29976) [C8 pcs; C8 dsz; C4 bt; C4 stg; C4 le; C4 fe]).
    { apply TCb; cbn [cells_size csize Nat.add]; [exact H30 | apply INBd; clear; lia | clear - O1; lia | clear - APD; lia | apply DBLK; clear; lia]. }
    assert (H53 : rw_cells bsegs m3 (DCTX + 30096) (h5_cells ws)).
    { apply TCb; rewrite ?(h5_cells_size ws H5L); [exact H50 | apply INBd; clear; lia | clear - O1; lia | clear - APD; lia | apply DBLK; clear; lia]. }
    assert (UD3 : unpoisoned m3 DCTX (DCTX + 95992)) by (apply (UNT DCTX 95992 UD0 IND); [clear; lia | clear - R1; lia | clear - R2; lia | exact APD]).
    assert (UL3 : unpoisoned m3 LITP (LITP + (LBE + 32 - LITP))) by (apply (UNT LITP (LBE + 32 - LITP) UL0 INL); [clear - R11; lia | clear - R10; lia | clear - R12; lia | exact APL]).
    (* [comment removed for export] *)
    assert (SQB3 : bytes_at bsegs m3 SEQ (map (Z_to_bv 8) sq) /\ (0 < zlen sq -> unpoisoned m3 SEQ (SEQ + zlen sq) /\ (SEQ + zlen sq <= FF \/ FF + 256 <= SEQ))).
    { destruct (Z.eq_dec (zlen sq) 0) as [Z0|NZ].
      - split; [| intros Hn; exfalso; clear - Hn Z0; lia].
        destruct sq as [|b sq']; [| exfalso; cbn [length] in Z0; clear - Z0; lia]. cbn [map]. apply bytes_at_nil. clear - R3 R4; lia.
      - pose proof (INS ltac:(clear - NZ; lia)) as IB. destruct (ARS ltac:(clear - NZ; lia)) as (ABS & US0 & RS1 & RS2).
        destruct (BAT SEQ (map (Z_to_bv 8) sq) SQB ltac:(rewrite length_map; exact O3) ltac:(left; rewrite length_map; exact IB) R3 ltac:(left; rewrite length_map; exact ABS)) as [SB3 APS].
        rewrite length_map in APS.
        split; [exact SB3|]. intros _. split; [| exact APS]. pose proof (fk_ablk_lits _ _ ABS) as SL.
        apply (UNT SEQ (zlen sq) US0 IB); [clear; lia | clear - R3; lia | clear - R4; lia | exact APS]. }
    destruct SQB3 as [SB3 SQU3].
    (* [comment removed for export] *)
    assert (BUF3 : stk bsegs m3 B0 B1 /\ (B0 < B1 -> unpoisoned m3 B0 (B0 + (B1 - B0)) /\ (B1 <= FF \/ FF + 256 <= B0) /\ ((6443008 <= B0 /\ B1 <= 2147446784) \/ (17594333495296 <= B0 /\ B1 <= ATOP)))).
    { destruct (Z_lt_le_dec B0 B1) as [BB|BB]; [| split; [exact (stk_keep_empty m m3 _ _ BUF BB) | intros BB'; exfalso; clear - BB BB'; lia]].
      destruct (AOUT BB) as (AO & AH0 & IB). destruct (AO ltac:(clear - BB; lia)) as (BO & UO & RO1 & RO2). pose proof (fk_ablk_lits _ _ BO) as BOL.
      pose proof (fk_inblk_apart AI _ _ _ _ _ _ _ _ B0 (B1 - B0) AH2 IB ltac:(clear - BB; lia)) as APB.
      split.
      + eapply stk_transport_disjoint; [| exact MU3| exact WM3| apply D3; [clear - APB; lia | right; clear - BOL; lia | clear - BB; lia | clear - O2 BB; lia]].
        eapply aheap_pres_stk_blk; [exact HPR2 | | apply (fk_acr_inblk AI); exact IB].
        eapply stk_transport_disjoint; [exact BUF| exact MU1| exact WM1| apply D1; [exact O2 | clear - BB; lia]].
      + intros _. split; [| split; [clear - APB; lia | replace (B0 + (B1 - B0)) with B1 in BOL by (clear; lia); exact BOL]].
        apply (UNT B0 (B1 - B0) UO IB); [clear - BB; lia | clear - BOL; lia | clear - R9; lia | exact APB]. }
    destruct BUF3 as [BUF3 BUFU].
    (* [comment removed for export] *)
    assert (LRD3 : rdbl bsegs m3 LITP (LBE + 32)).
    { eapply rdbl_transport; [| exact MU3 | intros x Hx; left; cbn [outside]; split; [clear - Hx APL; lia | split; [clear - Hx LL BSF; lia | split; [clear - Hx O4 LOSb; lia | exact I]]]].
      eapply aheap_pres_rdbl_blk; [exact HPR2 | | apply (fk_acr_inblk AI); exact INL].
      eapply rdbl_transport; [exact LRD | exact MU1 | intros x Hx; left; cbn [outside]; split; [clear - Hx O4 LOSb; lia | exact I]]. }
    (* [comment removed for export] *)
    assert (XRD3 : LOC = 2 -> rdbl bsegs m3 (DCTX + 30372) (DCTX + 30372 + 65568)).
    { intros HL2. eapply rdbl_transport; [| exact MU3 | intros x Hx; left; cbn [outside]; split; [clear - Hx APD; lia | split; [clear - Hx DL BSF; lia | split; [clear - Hx O1 LOSb; lia | exact I]]]].
      eapply aheap_pres_rdbl_blk; [exact HPR2 | | replace (DCTX + 30372 + 65568 - (DCTX + 30372)) with 65568 by (clear; lia); apply (fk_acr_inblk AI); apply INBd; clear; lia].
      eapply rdbl_transport; [exact (XRD HL2) | exact MU1 | intros x Hx; left; cbn [outside]; split; [clear - Hx O1 LOSb; lia | exact I]]. }
    (* [comment removed for export] *)
    assert (TONE : forall T bs lg N, bytes_at bsegs m T bs -> zlen bs <= N -> 8 * (1 + 2 ^ lg) <= N -> 1 <= 2 ^ lg -> unpoisoned m T (T + 8 * (1 + 2 ^ lg)) ->
              4096 <= T -> (T + N <= lo \/ SPV <= T) -> (ainblk LB T N \/ T + N <= AIMG_HI) ->
              bytes_at bsegs m3 T bs /\ unpoisoned m3 T (T + 8 * (1 + 2 ^ lg)) /\ (FF + 256 <= T \/ T + N <= FF) /\ (T + N <= 2147446784 \/ 17594333495296 <= T) /\ T + N < 2^47).
    { intros T bs lg N B LN LP P1 U T0 HX IN. pose proof (bytes_at_bound _ _ _ _ B) as BL0. unfold AIMG_HI in *.
      destruct IN as [IB | IM].
      - destruct IB as (b & Hb & Hb1 & Hb2). pose proof (fk_ablk_lits _ _ (LBH b Hb)) as BL. pose proof (FFD b Hb) as BF.
        assert (APT : FF + 256 <= T \/ T + N <= FF) by (clear - BF Hb1 Hb2; lia).
        split.
        + eapply bytes_at_transport; [| exact MU3| apply D3; [clear - APT LN BL0; lia| right; clear - BL Hb1 Hb2 LN BL0; lia| clear; lia| clear - HX LN BL0; lia]].
          eapply (fk_bytes_pres AI); [exact HPR2| exists b; split; [exact Hb | clear - Hb1 Hb2 LN BL0; lia]|].
          eapply bytes_at_transport; [exact B| exact MU1| apply D1; [clear - HX LN BL0; lia| clear; lia]].
        + split; [| split; [exact APT | clear - BL Hb1 Hb2 ATR; lia]].
          apply (UNT T (8 * (1 + 2 ^ lg)) U); [exists b; split; [exact Hb | clear - Hb1 Hb2 LP P1; lia] | clear - P1; lia | clear - T0; lia | clear - BL Hb1 Hb2 LP ATR; lia | clear - APT LP P1; lia].
      - split; [| split; [| split; [clear - IM FHa; lia | clear - IM T0; lia]]].
        + eapply bytes_at_transport; [exact B| exact MU13| apply (proj1 (DI13 T (zlen bs) ltac:(clear - T0; lia) ltac:(clear; lia) ltac:(clear - IM LN; lia)))].
        + apply UNI; [exact U | clear - P1; lia | clear - T0; lia | clear - IM LP; lia]. }
    assert (TBL3 : nbSeq <> 0 ->
      (seq_table_at m3 K_LL LLT tLL /\ seq_table_at m3 K_OF OFT tOF /\ seq_table_at m3 K_ML MLT tML)
      /\ (aro RNG m3 LLT (8 * (1 + 2 ^ st_log tLL)) /\ aro RNG m3 OFT (8 * (1 + 2 ^ st_log tOF)) /\ aro RNG m3 MLT (8 * (1 + 2 ^ st_log tML)))
      /\ ((FF + 256 <= LLT \/ LLT + 4104 <= FF) /\ (FF + 256 <= OFT \/ OFT + 2056 <= FF) /\ (FF + 256 <= MLT \/ MLT + 4104 <= FF))
      /\ ((LLT + 4104 <= 2147446784 \/ 17594333495296 <= LLT) /\ (OFT + 2056 <= 2147446784 \/ 17594333495296 <= OFT) /\ (MLT + 4104 <= 2147446784 \/ 17594333495296 <= MLT))
      /\ (LLT + 4104 < 2^47 /\ OFT + 2056 < 2^47 /\ MLT + 4104 < 2^47)).
    { intros NZ. destruct (TB NZ) as ((BLL & OKLL) & (BOF & OKOF) & (BML & OKML) & T4 & T5 & T6). destruct (OT NZ) as (OT1 & OT2 & OT3). unfold off_stack in OT1, OT2, OT3.
      destruct (INT NZ) as (IN1 & IN2 & IN3). destruct (AROT NZ) as ((UT1 & QT1 & QS1) & (UT2 & QT2 & QS2) & (UT3 & QT3 & QS3)).
      pose proof (seq_pow_le _ _ OKLL) as P1. pose proof (seq_pow_le _ _ OKML) as P3.
      assert (P2 : 1 <= 2 ^ st_log tOF <= 256).
      { destruct OKOF as ((Q1 & Q2) & _). cbn [kind_maxLog] in Q2. split; [pose proof (Z.pow_pos_nonneg 2 (st_log tOF)); clear - Q1 H; lia|].
        change 256 with (2^8). apply Z.pow_le_mono_r; clear - Q1 Q2; lia. }
      pose proof (tbl_len_LL _ OKLL) as L1. pose proof (tbl_len_OF _ OKOF) as L2. pose proof (tbl_len_ML _ OKML) as L3.
      destruct (TONE LLT _ (st_log tLL) 4104 BLL L1 ltac:(clear - P1; lia) ltac:(clear - P1; lia) UT1 ltac:(clear - T4; lia) ltac:(clear - OT1; lia) IN1) as (B1' & U1' & F1' & X1' & Y1').
      destruct (TONE OFT _ (st_log tOF) 2056 BOF L2 ltac:(clear - P2; lia) ltac:(clear - P2; lia) UT2 ltac:(clear - T5; lia) ltac:(clear - OT2; lia) IN2) as (B2' & U2' & F2' & X2' & Y2').
      destruct (TONE MLT _ (st_log tML) 4104 BML L3 ltac:(clear - P3; lia) ltac:(clear - P3; lia) UT3 ltac:(clear - T6; lia) ltac:(clear - OT3; lia) IN3) as (B3' & U3' & F3' & X3' & Y3').
      split; [split; [split; [exact B1' | exact OKLL] | split; [split; [exact B2' | exact OKOF] | split; [exact B3' | exact OKML]]]|].
      split; [split; [split; [exact U1' | split; [exact QT1 | exact QS1]] | split; [split; [exact U2' | split; [exact QT2 | exact QS2]] | split; [exact U3' | split; [exact QT3 | exact QS3]]]]|].
      split; [split; [exact F1' | split; [exact F2' | exact F3']]|].
      split; [split; [exact X1' | split; [exact X2' | exact X3']]|].
      split; [exact Y1' | split; [exact Y2' | exact Y3']]. }
    (* [comment removed for export] *)
    assert (ACL3 : aro_client RNG m3).
    { apply (aro_client_transport_gen RNG m m3 _ WM13 ACL MU13). intros A n HIn.
      destruct (aclient_bounds A n HIn) as (Ba & Bb & Bc). apply (proj2 (DI13 A n ltac:(clear - Ba; lia) ltac:(clear - Bb; lia) ltac:(clear - Bc; lia))). }
    assert (ART3 : art m3).
    { assert (TC : forall A cs, rw_cells bsegs m A cs -> 0 <= A -> A + Z.of_nat (cells_size cs) <= 6443008 -> rw_cells bsegs m3 A cs).
      { intros A cs H H1 H2. eapply rw_cells_transport; [exact H | exact MU13 | exact WM13 | apply (proj1 (DI13 A (Z.of_nat (cells_size cs)) H1 (Nat2Z.is_nonneg _) H2))]. }
      destruct ART as (G1 & G2 & G3 & G4 & G5 & G6). unfold art.
      split; [apply TC; [exact G1 | clear; lia | cbn; clear; lia]|].
      split; [apply TC; [exact G2 | clear; lia | cbn; clear; lia]|].
      split; [apply TC; [exact G3 | clear; lia | cbn; clear; lia]|].
      split; [apply TC; [exact G4 | clear; lia | cbn; clear; lia]|].
      split; [apply TC; [exact G5 | clear; lia | cbn; clear; lia]|].
      apply TC; [exact G6 | clear; lia | cbn; clear; lia]. }
    assert (AZS3 : azstk RNG m3 lo SPV).
    { destruct AZS as (RLO & RHI & U & HB & W0 & ABK & R). exists RLO, RHI.
      split; [| split; [exact HB | split; [eapply wr_at_transport; [exact W0 | exact WM13] | split; [exact ABK | exact R]]]].
      eapply unpoisoned_munch; [exact U | exact MU13 |].
      destruct LY5 as (_ & _ & FA1 & FA2). cbn [disjoint_from fake_area app]. subst SHF. rewrite !shad_div. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
      unfold ASHOFF, AIMG_HI, SMK_STACK, FAKESZ in *.
      split; repeat split; try exact I; clear - FL FABL FA1 FA2 ATR BOT LOSb SPAB KHI' R14 R13; Z.div_mod_to_equations; lia. }
    (* [comment removed for export] *)
    assert (AH3 : AHEAP AI L RNG st (FB2 FF :: LB) m3).
    { eapply (AI_frame AI); [exact AH2| exact MU3| exact WM3|].
      constructor; [cbn [fst snd]; eapply fk_acr_frame; [left; reflexivity | clear; lia | clear; lia]|].
      constructor; [cbn [fst snd] | constructor; [cbn [fst snd]; left; left; cbn; clear - BOT LOSb SPT LY3; lia | constructor]].
      replace (SHF + 32 - SHF) with 32 by (clear; lia). rewrite ESHF.
      eapply (fk_acr_fshadow AI _ 2 FF 256 FF 32); [left; reflexivity | clear; lia | clear; lia | clear - F256; Z.div_mod_to_equations; lia | clear - FL; lia]. }
    assert (FFR02 : ffr_pres [] LB m m2).
    { eapply ffr_pres_trans; [eapply (fk_ffr_stack AI); [exact AH| exact MU1| exact WM1| constructor; [cbn; clear - BOT LOSb; lia| constructor]]|].
      eapply (fk_ffr_of_pres AI); exact HPR2. }
    assert (FFR03 : ffr_pres [] LB m m3).
    { assert (MU3r : munch [(FF, FF + 24); (SPV - 768, SPV); (SHF, SHF + 32)] m2 m3)
        by (eapply munch_weaken; [| exact MU3]; unfold sub_fp; cbn [outside]; intros x Hx; clear - Hx; lia).
      eapply (fk_ffr_fin AI L RNG st LB m m2 m3 2 FF 256 SHF 32 [] [(FF, FF + 24); (SPV - 768, SPV)]);
        [ exact AH2 | exact LBH | exact FH | clear - F256; Z.div_mod_to_equations; lia | exact ESHF | clear; lia | clear; lia
        | constructor; [cbn [fst snd]; split; [clear; lia | right; split; [intros b Hb; pose proof (FFD b Hb) as HB'; clear - HB'; lia
                                                              | exists FF, (FF + 256); split; [exact FH | clear; lia]]]
                       | constructor; [cbn [fst snd]; split; [clear; lia | left; clear - BOT LOSb R14 ATR; lia] | constructor]]
        | constructor
        | exact FFR02
        | cbn [app]; exact MU3r
        | exact WM3 ]. }
    assert (FA8 : al_fake L mod 8 = 0) by (clear; unfold al_fake; Z.div_mod_to_equations; lia).
    assert (MU03 : munch (fake_area L ++ [(SPV - 5056, SPV)]) m m3).
    { eapply munch_trans; [eapply munch_weaken; [| exact MU1]; intros x Hx; clear - Hx SPAB LOSb; cbn [outside app fake_area] in *; lia|].
      eapply munch_trans; [eapply munch_weaken; [| exact MUF2]; intros x Hx; clear - Hx SPAB LOSb; cbn [outside app fake_area] in *; unfold SMK_STACK in *; lia|].
      eapply munch_weaken; [| exact MU3]; intros x Hx; clear - Hx FFA1 FFA2 SPAB LOSb BOT F256 FHb FA8;
        cbn [outside app fake_area] in *; subst SHF; rewrite ?shad_div in *; rewrite ?Z.shiftr_div_pow2 in * by lia; change (2^3) with 8 in *; unfold FAKESZ, ASHOFF in *;
        Z.div_mod_to_equations; lia. }
    (* [comment removed for export] *)
    set (P := mkSLQ ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m3 SPV lo DCTX DST CAP B0 B1 SEQ nbSeq LLT MLT OFT PFX LITP LBE LITB LOC sq tLL tOF tML
                      huf r0 r1 r2 pde dend expd pcs dsz bt stg le fe ws AI fflag L RNG st LB m (SLFRB SPV) FF SHF D8
                      (firstn 8 jA) (cells_bytes [CB 16 (firstn 16 (skipn 48 jB1)); C8 (Z_to_bv 64 FF)]) (SLJFH j8) j144 SLJSH0 SLJSH1).
    assert (MEM : sql_mem P).
    { unfold P, sql_mem, DCTX_litExtraBuffer, DCTX_litExtraBuffer_sz, WILDCOPY_OVERLENGTH.
      split; [split; [exact PT3 | split; [exact REP3 | split; [exact H13 | split; [exact H33 | split; [exact H53 | exact H5L]]]]] |].
      split; [exact LIT|]. split; [exact SB3|]. split; [exact BUF3|]. split; [exact LRD3|]. split; [intros HL2; exact (XRD3 HL2)| exact MI3]. }
    assert (RG : sql_ranges P).
    { unfold P, sql_ranges, DCTX_SIZEOF, WILDCOPY_OVERLENGTH. unfold hidden in R5, R14.
      split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. split; [exact R4|]. split; [exact R5|]. split; [exact R6|]. split; [exact R7|].
      split; [exact R8|]. split; [exact R9|]. split; [exact R10|]. split; [exact R11|]. split; [exact R12|]. split; [exact R13|]. split; [exact R14| exact R15]. }
    assert (SD : sql_side P).
    { unfold P, sql_side, WILDCOPY_OVERLENGTH, apart.
      unfold hidden in LOCD. unfold ZSTD_split, ZSTD_in_dst, ZSTD_not_in_dst.
      split; [exact D8M|]. split; [exact AB|]. split; [exact DZ|]. split; [exact DNZ|]. split; [exact PF|].
      split; [exact LOCD|]. split; [exact Y7|]. split; [unfold hidden in Y8; exact Y8|]. split; [exact Y9|].
      split; [exact SP16|]. split; [exact TM8|]. split; [exact CAPNZ| exact BB1]. }
    assert (SEP : sql_sep P).
    { unfold P, sql_sep, DCTX_SIZEOF, WILDCOPY_OVERLENGTH, DCTX_entropy_rep, DCTX_litExtraBuffer, off_stack, apart, ZSTD_split. unfold hidden in A1, A2, A3.
      split; [exact O1|]. split; [exact O2|]. split; [exact O3|]. split; [exact O4|]. split; [exact A1|]. split; [exact A2|]. split; [exact A3| intros HL; unfold hidden in A4; exact (A4 HL)]. }
    assert (TBL : nbSeq <> 0 -> sql_tables P).
    { intros NZ. destruct (TBL3 NZ) as (TS & _). destruct (TB NZ) as (_ & _ & _ & T4 & T5 & T6).
      unfold P, sql_tables, DCTX_SIZEOF, DCTX_entropy_rep.
      split; [exact (proj1 TS)|]. split; [exact (proj1 (proj2 TS))|]. split; [exact (proj2 (proj2 TS))|].
      split; [exact T4|]. split; [exact T5|]. split; [exact T6|].
      destruct (OT NZ) as (OT1 & OT2 & OT3). destruct (AT NZ) as (AT1 & AT2 & AT3). destruct (ATB NZ) as (AB1 & AB2 & AB3).
      split; [exact OT1|]. split; [exact OT2|]. split; [exact OT3|]. split; [exact AT1|]. split; [exact AT2|]. split; [exact AT3|].
      split; [exact AB1|]. split; [exact AB2| exact AB3]. }
    assert (AS : sql_astat P).
    { unfold P, sql_astat, DCTX_SIZEOF, WILDCOPY_OVERLENGTH, apart, astk, AIMG_HI.
      split; [split; [exact KHI | split; [exact RSTK | exact RI]]|]. split; [exact TP|]. split; [exact BOT|]. split; [exact SPT|]. split; [exact ED8|].
      split; [clear - SPAB SP16; unfold SLFRB in *; Z.div_mod_to_equations; lia|]. split; [exact SPA32|]. split; [clear - FHa; lia|]. split; [exact FC|]. split; [exact F256|]. split; [exact ESHF|]. split; [exact RFF|].
      split; [rewrite ESHF; exact RSFF|].
      split; [clear - APD; lia|]. split; [intros BB; destruct (BUFU BB) as (_ & HB & _); clear - HB; lia|]. split; [intros Hn; destruct (SQU3 Hn) as [_ HS]; clear - HS; lia|].
      split; [clear - APL; lia|].
      intros NZ. destruct (TBL3 NZ) as (_ & _ & (F1 & F2 & F3) & _). split; [clear - F1; lia|]. split; [clear - F2; lia| clear - F3; lia]. }
    assert (ASN : sql_asan P m3).
    { unfold P, sql_asan, DCTX_SIZEOF, WILDCOPY_OVERLENGTH.
      split; [intros _; split; [exact ABD|]; split; [exact UD3|]; split; [exact RD1| exact RD2]|].
      split; [exact (fk_ahull_pres _ _ _ _ _ WM13 AHD)|].
      split; [intros Hn; destruct (ARS Hn) as (B & U & Q1 & Q2); destruct (SQU3 Hn) as [U3 _]; split; [exact B|]; split; [exact U3|]; split; [exact Q1| exact Q2]|].
      split; [intros NZ; destruct (TBL3 NZ) as (_ & TA & _); exact TA|].
      split; [exact ACL3|].
      split; [intros BB; destruct (AOUT BB) as (AO & AH0 & _); destruct (BUFU BB) as (U3 & _); split; [intros Hn; destruct (AO Hn) as (B & U & Q1 & Q2); split; [exact B|]; split; [exact U3|]; split; [exact Q1| exact Q2] | exact (fk_ahull_pres _ _ _ _ _ WM13 AH0)]|].
      split; [intros _; split; [exact ABL|]; split; [exact UL3|]; split; [exact RLT1| exact RLT2]|].
      split; [exact (fk_ahull_pres _ _ _ _ _ WM13 AHL)|].
      split; [exact AZS3| exact ART3]. }
    assert (PRO : sql_pro P).
    { unfold P, sql_pro, DCTX_SIZEOF.
      split; [exact AH3|]. split; [exact MU03|]. split; [exact WM13|]. split; [exact FFR03|]. split; [exact FFLAG|]. split; [exact FRL|].
      split; [exact FFA1|]. split; [exact FFA2|]. split; [exact FFD|]. split; [exact IND|]. split; [intros BB; destruct (AOUT BB) as (_ & _ & IB); exact IB|].
      split; [exact LBH| exact FH]. }
    (* [comment removed for export] *)
    assert (HLSZ' : l_LBE P - l_LITP P < 2^32) by (cbn [l_LBE l_LITP P]; exact HLSZ).
    assert (HLBE : l_LOC P = 2 -> wnth (l_ws P) H5_litBufferEnd = Z_to_bv 64 (l_LBE P)) by (intros _; cbn [l_ws l_LBE P]; destruct LIT as (_ & HL & _); exact HL).
    pose proof (sql_fin_ok P RG AS PRO) as FINK.
    pose proof (sql_last2_ok P RG SD SEP AS PRO MMV FINK) as L2K.
    pose proof (sql_lastx_ok P RG SD SEP AS PRO HLSZ' MMV FINK L2K) as LASTK.
    assert (TH3 : l_nbSeq P <> 0 -> l_LLT P + 4104 <= 2^47 /\ l_OFT P + 2056 <= 2^47 /\ l_MLT P + 4104 <= 2^47).
    { cbn [l_nbSeq l_LLT l_OFT l_MLT P]. intros NZ. destruct (TBL3 NZ) as (_ & _ & _ & _ & (Y1 & Y2 & Y3)). clear - Y1 Y2 Y3. lia. }
    assert (TST : l_nbSeq P <> 0 -> l_LLT P + 4104 < 2^47 /\ l_OFT P + 2056 < 2^47 /\ l_MLT P + 4104 < 2^47).
    { cbn [l_nbSeq l_LLT l_OFT l_MLT P]. intros NZ. destruct (TBL3 NZ) as (_ & _ & _ & _ & Y). exact Y. }
    assert (TB3 : l_nbSeq P <> 0 -> (l_LLT P + 4104 <= 2147446784 \/ 17594333495296 <= l_LLT P) /\ (l_OFT P + 2056 <= 2147446784 \/ 17594333495296 <= l_OFT P) /\
                                    (l_MLT P + 4104 <= 2147446784 \/ 17594333495296 <= l_MLT P)).
    { cbn [l_nbSeq l_LLT l_OFT l_MLT P]. intros NZ. destruct (TBL3 NZ) as (_ & _ & _ & X & _). exact X. }
    assert (INITK : forall OEND, sql_static P OEND (l_LITP P) (l_LBE P) (l_LOC P) -> ai_I0 P OEND).
    { intros OEND ST. pose proof (proj1 (st16 _ _ _ _ _ ST)) as NZ1. cbn [l_nbSeq P] in NZ1.
      exact (sql_init_ok P OEND ST RG SD SEP HLBE HLSZ' MMV (TST ltac:(cbn [l_nbSeq P]; clear - NZ1; lia))). }
    (* [comment removed for export] *)
    replace (Z_to_bv 64 18446744073709551601) with (Z_to_bv 64 (-15)) by (apply Z_to_bv_eqm; reflexivity).
    replace (Z_to_bv 64 18446744073709551603) with (Z_to_bv 64 (-13)) by (apply Z_to_bv_eqm; reflexivity).
    eapply (sql_ent_ok P MEM RG SD SEP TBL AS ASN PRO MMV EXE EXS TH3 TB3 LASTK FINK INITK).
    - exact FRA3.
    - exact FFC3.
    - exact SHF3.
    - exact STL3.
    - eapply stk_transport_disjoint; [exact STG2| exact MU3'' | exact WM3| cbn; clear - SPAB LOSb BOT FHc BSF KHI'; lia].
    - eapply rw_cells_transport; [exact SAV2| exact MU3'' | exact WM3| unfold SLSAVED; cbn; clear - SPAB LOSb BOT FHc BSF KHI'; lia].
  Qed.
End Thm.
End CANSEC1.
