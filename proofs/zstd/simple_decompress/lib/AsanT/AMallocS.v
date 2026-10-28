(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF ITreeA StepF SysStepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg AProto ABase ABytes ASecFacts AMalloc_iface ADepot_iface APoisonR_iface ARep ALayout AHeapP
     ARepKit ARepFrame ARepExt ARepExt2 AKit AKit2 AKitQ AModelFacts APrimFacts ASec ASecFrame ASecModel ASecStore
     F_apoison F_ammap F_aalloc1 F_amalloc_icpt F_amalloc_preS F_alarge F_acallocS F_amalloc_tailS F_amalloc_arep.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
(* [comment removed for export] *)
Local Lemma ablk_int : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6443008 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof. intros a n H G1 G2. unfold sclr, KLS in H. destruct H; [exists 0 | exists 1]; lia. Qed.
Local Lemma iclr_int : forall a n, iclr a n -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ 4096 <= a /\ a + n <= 65536 + k * 18446744073709551616 /\ 6443008 * k <= a.
Proof. intros a n H G2. unfold iclr, AIMG_LO, AIMG_HI in H. destruct H as [? [?|?]]; [exists 0 | exists 1]; lia. Qed.
(* [comment removed for export] *)
Local Lemma ablk_shad_int : forall a ms, ablk a (a + ms) -> a mod 8 = 0 -> 0 <= ms ->
  exists k, 0 <= k <= 1 /\ a + ms <= shad a + k * 18446744073709551616 /\ shad a + ms / 8 + 8 <= a + (1 - k) * 18446744073709551616
            /\ 2148256256 <= shad a /\ shad a + ms / 8 <= 17594333495296.
Proof.
  intros a ms H A8 M0. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. rewrite !Shadow.shad_div. unfold AsanEmbed.ASHOFF.
  destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; Z.div_mod_to_equations; lia.
Qed.
Local Lemma aobj_int : forall a n, aobj a n -> 0x10000 <= n ->
  6443008 <= a /\ a + n <= ATOP /\ exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof.
  intros a n H Hn. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. destruct H as (H1 & H2 & H3 & H4 & H5).
  split; [lia|]. split; [lia|]. destruct H4; [exists 0 | exists 1]; lia.
Qed.
Local Lemma aobj4_int : forall a, aobj a 4096 ->
  4096 <= a /\ a + 4096 <= ATOP
  /\ (exists k, 0 <= k <= 1 /\ a + 4096 <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a)
  /\ (exists j, 0 <= j <= 1 /\ a + 4096 <= 65536 + j * 18446744073709551616 /\ 6443008 * j <= a).
Proof.
  intros a H. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. destruct H as (H1 & H2 & H3 & H4 & H5).
  split; [lia|]. split; [lia|]. split; [destruct H4; [exists 0 | exists 1]; lia | destruct H5 as [_ [H5|H5]]; [exists 0 | exists 1]; lia].
Qed.
(* [comment removed for export] *)
Local Ltac dlia := repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
Lemma premap_of_rt' : forall L m, arep_rt L m -> arep_rt2 m -> arep_rt3 m -> premap_cells m.
Proof.
  intros L m RT RT2 RT3.
  destruct RT3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R11 & R12 & R13 & R14 & R15 & R16 & R17).
  destruct RT2 as (_ & Q2 & _).
  pose proof R11 as R11a. rw_split R11a 1%nat R11h R11t.
  unfold premap_cells. split; [exact R11h|]. split; [exact R13|]. split; [exact Q2|].
  split; [apply premap_word_212a00; exact R14|]. split; [apply premap_word_212a18; exact R15|]. split; [exact R16| exact R17].
Qed.
Lemma poison_cells_of_rt' : forall L m, arep_rt L m -> poison_cells m.
Proof.
  intros L m RT.
  destruct RT as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15 & R16 & R17 & R18
                  & R19 & R20 & R21 & R22 & R23 & R24 & R25 & R26 & R27 & R28).
  unfold poison_cells. repeat lazymatch goal with |- _ /\ _ => split end; assumption.
Qed.

Lemma Z_to_bv8_bv_unsigned : forall (b : byte), Z_to_bv 8 (bv_unsigned b) = b.
Proof. intros. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

Section S.
Variable DI : ADepotIface.
Variables (AQ : alayout -> astate -> aconc -> amem -> Prop) (AFK : alayout -> list ablock -> amem -> Prop).
Hypothesis HL : ahole_laws (AH DI AQ ASEC_of AFK).
Hypothesis PR : poison_remap_stmt.
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI) CI.
Hypothesis CI_OK2 : Forall (fun iv => snd iv <= AINSTANCE \/ AINSTANCE + 728 <= fst iv) CI.

Theorem amalloc_sec : forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (n lo : Z) (tr : list Z) (RESV : list (Z * Z)),
  is_primary n = false ->
  (* [comment removed for export] *)
  AHEAP_P (AH DI AQ ASEC_of AFK) L RNG st LB m ->
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AMALLOC_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 n -> 1 <= n <= AREQMAX ->
  aunw m L RNG lo AMALLOC_PC sp s0 ra tr ->
  bv_unsigned s0 <> bv_unsigned sp + 8 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AMALLOC_PC ->
  bv_unsigned sp mod 16 = 0 ->
  rng RNG lo (bv_unsigned sp - lo) ->
  aresv_ok L RESV ->
  implS bsegs RNG (aembed ATOP (amalloc ATOP RESV st n))
        (epostF (amalloc_post CI (AHEAP_P (AH DI AQ ASEC_of AFK)) L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB n lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AMALLOC_SYM) fc None m (seg_rom bsegs)).
Proof.
  intros until RESV. intros PRIM AHP MI ST BOT LO TP Ha0 NR AUNW S0NE RA4 RANE SP16 RSTK ROK.
  assert (N : 1 <= n <= AREQMAX) by exact NR.
  (* [comment removed for export] *)
  assert (EXARM : exists trc,
      ((bv_unsigned sp + 16 < al_top L /\ uchain m (al_top L) AMALLOC_PC (bv_unsigned sp) (bv_unsigned s0) 28%nat tr /\ (length tr <= 28)%nat /\ trc = bv_unsigned ra :: tr
        /\ rng RNG lo (al_top L - lo))
       \/ (al_top L <= bv_unsigned sp + 16 /\ bv_unsigned sp < 2^47 /\ trc = []))
      /\ In (AMALLOC_PC :: trc) (al_U L) /\ (length trc <= 29)%nat /\ bv_unsigned sp < 2^47).
  { pose proof (alayout_stack L (proj1 AHP)) as (K1 & K2 & K3).
    destruct AUNW as [(T1 & U1 & L1 & I1 & R1)|(T1 & T2 & I1)].
    - exists (bv_unsigned ra :: tr). split; [left; split; [exact T1|]; split; [exact U1|]; split; [exact L1|]; split; [reflexivity| exact R1]|].
      split; [exact I1|]. split; [cbn [length]; clear -L1; lia | clear -T1 K2; lia].
    - exists (@nil Z). split; [right; split; [exact T1|]; split; [exact T2| reflexivity]|]. split; [exact I1|]. split; [cbn [length]; clear; lia | exact T2]. }
  destruct EXARM as (trc & ARM & TRU & LTRC & SP47).
  destruct AHP as (ALO & ARNG & [X [AR BL]] & HFK).
  pose proof (sec_facts n N PRIM) as (NB & RZ & RSE & RSR & RSM & NSE & MSE & MSR & MSM & MSB).
  set (ms := sec_map_size n) in *.
  (* [comment removed for export] *)
  pose proof AR as AR0. destruct AR0 as (WF & RT & INST & THR & CLS & HQ & HS & HD & HRO & RT2 & AVL & RT3).
  destruct THR as (T0 & T40 & CACHES & CSTATS & [sj [STATS LSJ]] & UNW).
  pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVE & FRESH & UNIQ).
  pose proof (alayout_space L ALO) as (SP1 & SP2 & SP3 & SP4).
  pose proof (alayout_t L ALO) as (TL1 & TL2 & TL3 & TL4).
  pose proof (alayout_ctx L ALO) as (CL1 & CL2 & CL3 & CL4 & CL5).
  pose proof (alayout_depot L ALO) as (DL1 & DL2 & DL3 & DL4 & DL5 & DL6 & DL7 & DL8 & DL9 & DL10).
  pose proof (alayout_stack L ALO) as (STK1 & STK2 & STK3).
  pose proof (ao_ptr L ALO) as OP. unfold aobj in OP. pose proof (ad_t_ptr L ALO) as D_t_p. pose proof (ad_ctx_ptr L ALO) as D_c_p. unfold adisj in D_t_p, D_c_p.
  pose proof (aobj4_int _ (ao_t L ALO)) as (_ & _ & (kT & TBND & TBNDa & TBNDb) & (jT & TIMG & TIMGa & TIMGb)).   (* [comment removed for export] *)
  pose proof (aobj_int _ _ (ao_ctx L ALO) ltac:(clear; lia)) as (CTXi & _ & (kC & CBND & CBNDa & CBNDb)).
  pose proof (aobj_int _ _ (ao_nodes L ALO) ltac:(clear; lia)) as (NODi & _ & (kN & NBND & NBNDa & NBNDb)).
  pose proof (aobj_int _ _ (ao_store L ALO) ltac:(clear; lia)) as (STOi & _ & (kR & SBND & SBNDa & SBNDb)).
  pose proof (aobj_int _ _ (ao_ptr L ALO) ltac:(clear; lia)) as (OPi & _ & (kP & OPs & OPsa & OPsb)).
  pose proof (aobj_int _ _ (ao_fake L ALO) ltac:(clear; lia)) as (OFKi & _ & (kF & OFKs & OFKsa & OFKsb)).
  pose proof (ao_res_hi L ALO) as RHI.
  pose proof RT as RT0.
  destruct RT0 as (GPG & GOT & GOT80 & RIC & LS1 & REAL & IMAX4 & FLG5 & FLG & HPP & SHB & CANP & TI & TK & INI2 & LAY & MCS & OOM3
                    & PGC & HK2 & CF8 & CF34 & CSMT & T88 & TSD & LS2 & CT8 & CT).
  pose proof INI2 as INI. rw_split INI 1%nat INI1 INIx. clear INIx.
  pose proof OOM3 as OOM. rw_split OOM 2%nat OOMx RSS. clear OOMx.
  pose proof IMAX4 as IMAX. rw_split IMAX 3%nat IMAX3 IMAXx. clear IMAXx.
  pose proof T0 as TT0. rw_split TT0 1%nat TTctx TT.
  pose proof ARNG as ARNG0. destruct ARNG as (RIMG & RT4 & RCTX & RNO & RSTO & RRI & RFK & RSFK & RDTLS & RCLS & RPA & RSECS & RPSH).
  assert (RCTX4 : rng RNG (al_ctx L) 4096) by (eapply rng_sub'; [exact RCTX|]; clear; lia).
  word_range sp SPR.
  box CL5. box DL7. box DL8. box DL9. box DL10. box D_t_p. box D_c_p.
  (* [comment removed for export] *)
  rewrite (amalloc_sec_eq RESV st n N PRIM). fold ms.
  (* [comment removed for export] *)
  iprefix. eapply evtF_cut.
  { eapply (malloc_pre_spec_sec L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n (al_t L) lo (al_top L) (al_bot L) tr trc).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => exact ST
         | |- mem_inv _ _ => exact MI
         | |- allocA_cells _ _ _ => unfold allocA_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end)
         | |- poison_cells _ => unfold poison_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end)
         | |- (_ /\ _) \/ (_ /\ _) => exact ARM
         | |- _ \/ _ => unboxed CL5
         | |- @eq word _ _ => first [exact TP | exact Ha0]
         | |- is_primary _ = _ => exact PRIM
         end.
    all: try lazymatch goal with
         | |- rw_cells _ _ _ _ => assumption
         | |- rng _ _ _ => assumption
         end.
    all: try assumption.
    all: try (generalize N NR LO BOT SP47 STK1 STK2 STK3 SP1 SP2 SP4 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 LTRC RA4 SP16;
              clear; intros; unfold AIMG_HI, AMALLOC_STACK, AREQMAX, UDEPTH in *; lia).
    all: match goal with |- ?G => idtac "REMPRE" G end. }
  cbv beta. intros ms4 P4. unfold malloc_pre_postS in P4.
  destruct P4 as (spA & t0c & t1c & t2c & a4c & a5c & a6c & a7c & t3c & t4c & t5c & t6c & s0A & s1A & s2A & s3A & s4A & s5A & s0i & fr0 & junk2 & tb & m4
                  & -> & HspA & MU4 & WM4 & MI4 & ST4 & FRa & FR16 & SS & TB & LTB & TRF & FRS & UW4).
  apply evtF_done.
  assert (AR4 : AREP (AH DI AQ ASEC_of AFK) L st X m4).
  { eapply (AREP_frame_pre _ HL L st X m m4); [exact ALO | exact AR | exact MU4 | exact WM4 | | exact UW4].
    apply Forall_cons; [unfold apre; cbn [fst snd]; intros _; left; unfold AMALLOC_STACK in *; clear -LO BOT STK3; lia|].
    apply Forall_cons; [unfold apre; cbn [fst snd]; intros _; right; split; reflexivity| apply Forall_nil]. }
  (* [comment removed for export] *)
  pose proof AR4 as AR0. destruct AR0 as (_ & RT' & INST' & THR' & _ & _ & HS' & HD' & HRO' & RT2' & _ & RT3').
  destruct THR' as (T0' & _ & _ & _ & [sj4 [STATS' LSJ']] & _).
  destruct INST' as (I32' & I48' & I64' & I72' & I112' & I680' & I984' & I40' & I56').
  pose proof HS' as HS0. unfold AH in HS0. cbn [ah_sec] in HS0. unfold ASEC_of in HS0.
  destruct HS0 as (WFS & ARR & INST2 & PZ & SHZ). pose proof WFS as (_ & WP & WR & WL & WB & WF1 & WD).
  destruct INST2 as (J80 & [srt J128] & J136 & J168 & J681 & J704).
  destruct ARR as (order & PO & U64 & JK & PER).
  pose proof RT' as RT0.
  destruct RT0 as (GPG' & GOT' & GOT80' & RIC' & LS1' & REAL' & IMAX4' & FLG5' & FLG' & HPP' & SHB' & CANP' & TI' & TK' & INI2' & LAY' & MCS' & OOM3'
                    & PGC' & HK2' & CF8' & CF34' & CSMT' & T88' & TSD' & LS2' & CT8' & CT').
  pose proof T0' as TT0'. rw_split TT0' 1%nat TTctx' TT'.
  (* [comment removed for export] *)
  destruct J136 as [jstats J136]. destruct J168 as [jbsl J168]. destruct J704 as [jglob J704].
  cbn [Z.to_nat Pos.to_nat Pos.iter_op Nat.add Nat.mul] in J136, J168, J704.
  (* [comment removed for export] *)
  assert (MTX : rw_cells bsegs m4 0xcc940 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]).
  { apply (proj2 (rw_cells_app bsegs m4 0xcc940 [C1 (Z_to_bv 8 0)] [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)])). split; [exact I680'| exact J681]. }
  (* [comment removed for export] *)
  assert (JSL : exists jslot, a_nsec st < a_nres st -> rw_cells bsegs m4 (al_ptr_array L + 8 * a_nsec st) [CB 8 jslot]).
  { destruct (Z_lt_le_dec (a_nsec st) (a_nres st)) as [LT|GE].
    - destruct (junk_split m4 (al_ptr_array L + 8 * a_nsec st) 8 (8 * (a_nres st - a_nsec st) - 8)
                 ltac:(replace (8 + (8 * (a_nres st - a_nsec st) - 8)) with (8 * (a_nres st - a_nsec st)) by (clear; lia); exact JK)
                 ltac:(clear; lia) ltac:(clear -LT; lia)) as [[js J8] _].
      exists js. intros _. exact J8.
    - exists (repeat (Z_to_bv 8 0) 8). intros LT. exfalso. clear -LT GE. lia. }
  destruct JSL as [jslot JSL].
  (* [comment removed for export] *)
  destruct RT2' as (Q1' & Q2' & Q3').
  pose proof RT3' as RT30. destruct RT30 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R11' & R12' & _).
  pose proof R11' as R11a. rw_split R11a 1%nat R11h NAMEP. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add] in NAMEP.
  assert (I64x : rw_cells bsegs m4 0xcc6d8 [C8 (Z_to_bv 64 4096); C8 (Z_to_bv 64 (al_ptr_array L)); C8 (Z_to_bv 64 (al_ptr_array L))]).
  { apply (proj2 (rw_cells_app bsegs m4 0xcc6d8 [C8 (Z_to_bv 64 4096)] [C8 (Z_to_bv 64 (al_ptr_array L)); C8 (Z_to_bv 64 (al_ptr_array L))])).
    split; [exact I64'|]. apply (proj2 (rw_cells_app bsegs m4 _ [C8 (Z_to_bv 64 (al_ptr_array L))] [C8 (Z_to_bv 64 (al_ptr_array L))])).
    split; [exact I72'| exact J80]. }
  assert (LC4 : large_cells (al_ctx L) (al_t L) (al_ptr_array L) m4).
  { unfold large_cells. split; [unfold rmap_cells; split; [exact GPG'| split; [exact PGC'| split; [exact GOT'| split; [exact Q1'| exact Q2']]]]|].
    split; [eapply poison_cells_of_rt'; exact RT'|]. split; [exact NAMEP|]. split; [exact R12'|].
    split; [exact TI'|]. split; [exact TK'|]. split; [exact T88'|]. split; [exact TSD'|]. split; [exact CT'| exact I64x]. }
  (* [comment removed for export] *)
  assert (FROK : forall a, sfresh RESV st n a = true ->
        ablk a (a + ms) /\ a + ms <= ATOP
     /\ (a + ms <= al_t L \/ al_t L + 4096 <= a) /\ (a + ms <= al_ctx L \/ al_ctx L + 4096 <= a) /\ (a + ms <= al_ptr_array L \/ al_ptr_array L + 8388608 <= a)
     /\ fill_at m4 (shad a) (ms / 8) 0).
  { intros a HF.
    pose proof (valid_geo L RESV st n a N PRIM HF ROK) as (AAL & AHI0 & ACE & MSP & _). fold ms in ACE, MSP.
    destruct (ablk_int _ _ AHI0) as (kA & ABND & ABNDa & ABNDb & ABNDc & ABNDd). pose proof (sec_facts n N PRIM) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & MSBx). fold ms in MSBx.   (* [comment removed for export] *)
    destruct (ablk_shad_int _ _ AHI0 ltac:(clear -AAL; Z.div_mod_to_equations; lia) ltac:(clear -MSBx; lia)) as (kS & ASD & ASDa & ASDb & SA1 & SA3).   (* [comment removed for export] *)
    pose proof (valid_clear L RESV st n a N PRIM HF ROK) as (C_t & C_c & C_r & C_p & _). fold ms in C_t, C_c, C_p.
    unfold K_HIGH_MEM in AHI0. split; [exact AHI0|]. split; [exact ACE|]. split; [exact C_t|]. split; [clear -C_c; lia|]. split; [exact C_p|].
    unfold fill_at. apply (azero_cb m4 (shad a) (ms / 8) (ms / 8)); [| clear -MSB; Z.div_mod_to_equations; lia].
    eapply (ashz_azero L _ m4 a ms SHZ); [clear -AAL; Z.div_mod_to_equations; lia| exact AHI0| exact ACE| clear -MSB; lia
      | exact (valid_hulls L RESV st n a N PRIM HF ROK)| exact (valid_chunks L RESV st n a N PRIM HF ROK)]. }
  (* [comment removed for export] *)
  assert (TS : forall (a nres' : Z) RNG' (m1 m' : amem) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
    sfresh RESV st n a = true ->
    munch [(bv_unsigned sp - 2320, bv_unsigned sp - 2272)]%Z m4 m1 -> wmono bsegs m4 m1 ->
    large_post RNG (Z_to_bv 64 (bv_unsigned sp - 2320)) a n (al_ctx L) (al_t L) (al_ptr_array L) (a_nres st) (a_nsec st) nres' lo m1 RNG' m' ->
    stk bsegs m' lo (bv_unsigned sp - 2272) ->
    implS bsegs RNG' (aembed ATOP (poison0 (a + PG + rz_size n) (Z.land n (Z.lnot 7)) (aret (st_sec st nres' a ms n, Some (a_next st)))))
          (epostF (amalloc_post CI (AHEAP_P (AH DI AQ ASEC_of AFK)) L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB n lo m))
          (MS (mkR (Z_to_bv 64 0x33da8) (Z_to_bv 64 (bv_unsigned spA + -128)) gp tp t0' t1' t2'
                   (Z_to_bv 64 0) (Z_to_bv 64 n) (Z_to_bv 64 (a + 4096)) a1' a2' a3' a4' a5' a6' a7'
                   (Z_to_bv 64 8) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n)
                   (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 (-8)) (Z_to_bv 64 7) (Z_to_bv 64 (al_t L)) (Z_to_bv 64 1)
                   t3' t4' t5' t6')
              F (Z_to_bv 64 0x33da8) fc None m' (seg_rom bsegs))).
  { intros a nres' RNG' m1 m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' HF MU1 WM1 LP STc.
    pose proof (valid_geo L RESV st n a N PRIM HF ROK) as (AAL & AHI0 & ACE & MSP & _). fold ms in ACE, MSP.
    destruct (ablk_int _ _ AHI0) as (kA & ABND & ABNDa & ABNDb & ABNDc & ABNDd). pose proof (sec_facts n N PRIM) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & MSBx). fold ms in MSBx.   (* [comment removed for export] *)
    destruct (ablk_shad_int _ _ AHI0 ltac:(clear -AAL; Z.div_mod_to_equations; lia) ltac:(clear -MSBx; lia)) as (kS & ASD & ASDa & ASDb & SA1 & SA3).   (* [comment removed for export] *) unfold K_HIGH_MEM in AHI0.
    pose proof (valid_clear L RESV st n a N PRIM HF ROK) as VC. fold ms in VC. pose proof VC as (C_t & C_c & C_r & C_p & C_n & C_s & C_f & C_d).
    unfold large_post in LP. cbv zeta in LP. fold ms in LP.
    destruct LP as (FPLE & BW & _ & _ & _ & MUL & WML & MIL & STL & HDRP & ZB & SHF1 & SHZ0 & SHF2 & RCH & RSCH & INS & SRT & JST & JBS & MTX9 & JGL
                    & [sj9 [STATS9 LSJ9]] & PAS & DISJ & NRB' & LC').
    rewrite unsigned_lit in MUL, STL by (clear -SPR LO BOT STK3; unfold AMALLOC_STACK in *; lia).
    unfold AINSTANCE in MUL.
    assert (NR' : (a_nsec st <> a_nres st /\ nres' = a_nres st)
                  \/ (a_nsec st = a_nres st /\ nres' = a_nres st + 16384
                      /\ rw_cells bsegs m' (al_ptr_array L + 8 * a_nres st + 8) [CB (Z.to_nat (131072 - 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (131072 - 8)))])).
    { destruct DISJ as [D|(D1 & D2 & D3 & _)]; [left; exact D| right; split; [exact D1| split; [exact D2| exact D3]]]. }
    assert (RPA' : rng RNG' (al_ptr_array L) (8 * nres')).
    { destruct DISJ as [[_ ->]|(D1 & -> & _ & RPC)]; [eapply rng_fp_le; [exact FPLE| exact RPA]|].
      replace (8 * (a_nres st + 16384)) with (8 * a_nres st + 131072) by (clear; lia).
      apply rng_merge; [exact BW| clear -WB; lia| clear; lia| eapply rng_fp_le; [exact FPLE| exact RPA]| exact RPC]. }
    clear DISJ.
    assert (WTF : wt_facts L (bv_unsigned sp) lo a ms (a_nsec st) (a_nres st) nres').
    { unfold wt_facts. assert (NSX : 0 <= a_nsec st /\ a_nsec st + 1 <= nres' /\ a_nres st <= nres') by (destruct NR' as [(A1 & A2)|(A1 & A2 & _)]; clear -A1 A2 WB; lia).
      repeat lazymatch goal with |- _ /\ _ => split end; try assumption; try (clear -NSX NRB' WB LO BOT STK3; unfold AMALLOC_STACK in *; lia). }
    (* [comment removed for export] *)
    set (WS := ((bv_unsigned sp - 2816, bv_unsigned sp - 2272) :: (a, a + ms) :: (shad a, shad a + ms / 8) :: (837272 + 112, 837272 + 720)
                :: (al_t L + 2800, al_t L + 3168) :: (al_ptr_array L + 8 * a_nsec st, al_ptr_array L + 8 * a_nsec st + 8)
                :: (al_ptr_array L + 8 * a_nres st, al_ptr_array L + 8 * nres') :: nil)%Z).
    assert (MUS : munch WS m4 m').
    { subst WS. eapply munch_trans; [eapply munch_weaken; [| exact MU1] | eapply munch_weaken; [| exact MUL]]; unfold sub_fp; cbn [outside]; clear; intros q Hq; lia. }
    assert (WMS : wmono bsegs m4 m') by (eapply wmono_trans; [exact WM1| exact WML]).
    assert (MUT : munch (List.filter nonempty (WT L (bv_unsigned sp) a ms (a_nsec st) (a_nres st) nres')) m4 m').
    { apply munch_filter_nonempty. eapply munch_weaken; [| exact MUS]. subst WS. unfold WT, sub_fp, AINSTANCE. cbn [outside]. clear. intros q Hq. lia. }
    (* [comment removed for export] *)
    pose proof (KT_rt L _ lo a ms _ _ _ WTF m4 m' MUT WMS RT') as RTL.
    pose proof (KT_rt2 L _ lo a ms _ _ _ WTF m4 m' MUT WMS (conj Q1' (conj Q2' Q3'))) as RT2L.
    pose proof (KT_rt3 L _ lo a ms _ _ _ WTF m4 m' MUT WMS RT3') as RT3L.
    pose proof (KT_relro L _ lo a ms _ _ _ WTF m4 m' MUT HRO') as HROL.
    pose proof (premap_of_rt' L m' RTL RT2L RT3L) as PMC.
    pose proof RTL as RT0.
    destruct RT0 as (_ & _ & _ & _ & LS1L & _ & _ & _ & FLGL & HPPL & _ & _ & _ & _ & _ & _ & _ & _ & _ & HK2L & _ & _ & _ & _ & _ & LS2L & CT8L & _).
    pose proof HK2L as HKL. rw_split HKL 1%nat HK1L HKx. clear HKx.
    destruct LC' as (_ & PCL & _ & _ & TIL & TKL & T88L & TSDL & CTL & I64L).
    pose proof I64L as I64h. rw_split I64h 1%nat I64a I64b. clear I64b.
    assert (I32L : rw_cells bsegs m' 0xcc6b8 [C8 (Z_to_bv 64 (al_space_beg L))]).
    { eapply cells_frame; [exact I32'| exact MUT| exact WMS|]. cbn. eapply KT_img; [exact WTF| | | | |]; clear; unfold AIMG_HI, AINSTANCE; lia. }
    assert (TTL : rw_cells bsegs m' (al_t L) [C8 (Z_to_bv 64 (al_ctx L))]).
    { eapply cells_frame; [exact TTctx'| exact MUT| exact WMS|]. cbn. eapply KT_t; [exact WTF| | |]; clear; lia. }
    assert (DEPL : ADEPOT DI L m').
    { pose proof (hd_frame _ HL L m4 m' WS) as HDF. cbn [ah_depot AH] in HDF. apply HDF; [exact HD'| exact MUS| exact WMS|].
      subst WS. pose proof (ad_nodes_ptr L ALO) as D_n_p. pose proof (ad_store_ptr L ALO) as D_s_p. unfold adisj in D_n_p, D_s_p. ub DL7. ub DL8.
      repeat (apply Forall_cons; [cbn [fst snd]; intros x Hx;
        clear -Hx Y Y0 SPR LO BOT STK3 AHI0 ACE TL1 DL1 DL2 DL4 DL5 OP WB NRB' C_n C_s D_n_p D_s_p SA1 SA3 WTF TBND TBNDa TBNDb TIMG TIMGa TIMGb NBND NBNDa NBNDb NODi SBND SBNDa SBNDb STOi OPs OPsa OPsb OPi ABND ABNDa ABNDb ABNDc ABNDd ASD ASDa ASDb; unfold wt_facts, AMALLOC_STACK in *; lia|]).
      apply Forall_nil. }
    subst WS.
    (* [comment removed for export] *)
    xport FRa MUS WMS ltac:(clear -SPR LO BOT STK3 AHI0 ACE TL1 TL2 OP WB NRB' WTF TBND TBNDa TBNDb TIMG TIMGa TIMGb OPs OPsa OPsb OPi ABND ABNDa ABNDb ABNDc ABNDd; unfold wt_facts, AMALLOC_STACK in *; rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; dlia).
    xport FR16 MUS WMS ltac:(clear -SPR LO BOT STK3 AHI0 ACE TL1 TL2 OP WB NRB' WTF TBND TBNDa TBNDb TIMG TIMGa TIMGb OPs OPsa OPsb OPi ABND ABNDa ABNDb ABNDc ABNDd; unfold wt_facts, AMALLOC_STACK in *; rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; dlia).
    xport SS MUS WMS ltac:(clear -SPR LO BOT STK3 AHI0 ACE TL1 TL2 OP WB NRB' WTF TBND TBNDa TBNDb TIMG TIMGa TIMGb OPs OPsa OPsb OPi ABND ABNDa ABNDb ABNDc ABNDd; unfold wt_facts, AMALLOC_STACK in *; rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; dlia).
    xport TB MUS WMS ltac:(rewrite LTB; clear -SPR LO BOT STK3 AHI0 ACE TL1 TL2 OP WB NRB' WTF TBND TBNDa TBNDb TIMG TIMGa TIMGb OPs OPsa OPsb OPi ABND ABNDa ABNDb ABNDc ABNDd; unfold wt_facts, AMALLOC_STACK in *; rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; dlia).
    xport FRS MUS WMS ltac:(clear -SPR LO BOT STK3 AHI0 ACE TL1 TL2 OP WB NRB' WTF TBND TBNDa TBNDb TIMG TIMGa TIMGb OPs OPsa OPsb OPi ABND ABNDa ABNDb ABNDc ABNDd; unfold wt_facts, AMALLOC_STACK in *; rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; dlia).
    xport UW4 MUS WMS ltac:(ub D_t_p; clear -Y SPR LO BOT STK3 AHI0 ACE TL1 TL2 OP WB NRB' WTF C_t TBND TBNDa TBNDb TIMG TIMGa TIMGb OPs OPsa OPsb OPi ABND ABNDa ABNDb ABNDc ABNDd; unfold wt_facts, AMALLOC_STACK in *; rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; dlia).
    (* [comment removed for export] *)
    pose proof (ao_res L ALO) as ORS. unfold aobj in ORS. pose proof (ao_space L ALO) as RSP.
    assert (DJSB : a + ms <= al_space_beg L \/ al_space_beg L + 137438953472 <= a) by (clear -C_r RSP; lia).
    apply (rng_fp_le _ _ _ _ FPLE) in RIMG. 
    assert (RSTK' : rng RNG' lo (bv_unsigned sp - lo)) by (eapply rng_fp_le; [exact FPLE| exact RSTK]).
    assert (RCTX' : rng RNG' (al_ctx L) 4096) by (eapply rng_fp_le; [exact FPLE| exact RCTX4]).
    assert (RT4' : rng RNG' (al_t L) 4096) by (eapply rng_fp_le; [exact FPLE| exact RT4]).
    assert (RNO' : rng RNG' (al_nodes L) 1048576) by (eapply rng_fp_le; [exact FPLE| exact RNO]).
    assert (RSTO' : rng RNG' (al_store L) 8388608) by (eapply rng_fp_le; [exact FPLE| exact RSTO]).
    replace (a + PG + rz_size n) with (a + 6144) by (unfold PG; rewrite RZ; clear; lia).
    (* [comment removed for export] *)
    eapply (malloc_tail_sec DI PR L RNG' _ _ _ ra sp gp tp spA t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6'
              s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0A s1A s2A s3A s4A s5A s0i F fc m' n (al_t L) a ms (a_nsec st) (al_space_beg L) lo
              (1 + Z.of_nat (length trc)) fr0 junk2 tb trc).
    all: try lazymatch goal with
         | |- forall x, _ => first [exact HROL | idtac]
         | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
         | |- stk _ _ _ _ => exact STc
         | |- bv_unsigned _ = _ => exact HspA
         | |- mem_inv _ _ => exact MIL
         | |- poison_cells _ => exact PCL
         | |- premap_cells _ => exact PMC
         | |- ADEPOT _ _ _ => exact DEPL
         | |- @eq word _ _ => first [reflexivity | exact TP | exact HspA]
         | |- @eq bool _ _ => exact PRIM
         | |- @eq nat _ _ => first [exact LTB | exact LSJ9]
         | |- u64arr _ _ _ _ => exact TB
         | |- exists sjx, _ => exists sj9; split; [exact STATS9| exact LSJ9]
         | |- map _ _ = _ => exact TRF
         | |- In _ _ => exact TRU
         | |- fill_at _ (shad _) 512 _ => exact SHF1
         | |- fill_at _ (shad _ + 512) _ 0 => exact SHZ0
         | |- fill_at _ _ _ _ => exact SHF2
         | |- rw_cells _ _ (shad _) _ => idtac
         | |- rw_cells _ _ _ [C8 _; C8 _; C8 _; C8 _; CB _ _] => exact HDRP
         | |- rw_cells _ _ (_ + 4096) [CB _ _] => exact ZB
         | |- rw_cells _ _ _ [C8 (Z_to_bv 64 (al_space_beg _))] => exact I32L
         | |- rw_cells _ _ _ [C8 (Z_to_bv 64 4096)] => exact I64a
         | |- rw_cells _ _ (al_t _) _ => exact TTL
         | |- rw_cells _ _ _ _ => assumption
         | |- rng _ _ _ => first [assumption | exact RCH | exact RSCH]
         | |- _ \/ _ => first [exact DJSB | exact C_t | exact C_n | exact C_s | clear -C_c; lia | unboxed CL5 | unboxed DL7 | unboxed DL8 | unboxed DL9 | unboxed DL10]
         | |- _ = sec_map_size _ => reflexivity
         end.
    all: try lazymatch goal with
         | |- forall x, _ => idtac
         | |- _ => clear -SPR LO BOT STK3 SP47 AAL AHI0 ACE TL1 TL2 TL3 CL1 CL2 CL3 DL1 DL2 DL3 DL4 DL5 DL6 SP1 SP2 SP4 N LTRC TBND TBNDa TBNDb TIMG TIMGa TIMGb CBND CBNDa CBNDb CTXi NBND NBNDa NBNDb NODi SBND SBNDa SBNDb STOi ABND ABNDa ABNDb ABNDc ABNDd;
                unfold AIMG_HI, AMALLOC_STACK, K_SPACE_SIZE, K_SPACE_EXTRA in *; lia
         end.
    all: match goal with |- forall x, _ => idtac | |- ?G => idtac "REMTS" G end.
    (* [comment removed for export] *)
    intros RNG5 m5 id sj5 t0d t1d t2d a1d a2d a3d a4d a5d a6d a7d t3d t4d t5d t6d PM.
    unfold malloc_postS in PM. cbv zeta in PM.
    destruct PM as (FPLE5 & MU5 & WM5 & MI5 & ST5 & IDR & STATS5 & LSJ5 & HDR5 & PGJ5 & MAG5 & LCJ5 & AHD5 & USR5 & TLJ5 & SHF5 & SHU5 & SHT5 & DEP5 & PC5 & PMC5).
    apply implS_ret. apply evtF_done.
    pose proof (ad_nodes_ptr L ALO) as D_n_p. pose proof (ad_store_ptr L ALO) as D_s_p. unfold adisj in D_n_p, D_s_p.
    (* [comment removed for export] *)
    xport UW4 MU5 WM5 ltac:(ub DL7; ub DL8; clear -Y Y0 SPR LO BOT STK3 AHI0 ACE TL1 TL2 SA1 SA3 DL1 DL2 DL4 DL5 C_t TBND TBNDa TBNDb TIMG TIMGa TIMGb NBND NBNDa NBNDb NODi SBND SBNDa SBNDb STOi ABND ABNDa ABNDb ABNDc ABNDd ASD ASDa ASDb; unfold AMALLOC_STACK in *; dlia).
    xport INS MU5 WM5 ltac:(clear -SPR LO BOT STK3 AHI0 ACE TL1 SA1 SA3 DL1 DL4 TBND TBNDa TBNDb TIMG TIMGa TIMGb NBND NBNDa NBNDb NODi SBND SBNDa SBNDb STOi ABND ABNDa ABNDb ABNDc ABNDd ASD ASDa ASDb; unfold AMALLOC_STACK in *; dlia).
    xport SRT MU5 WM5 ltac:(clear -SPR LO BOT STK3 AHI0 ACE TL1 SA1 SA3 DL1 DL4 TBND TBNDa TBNDb TIMG TIMGa TIMGb NBND NBNDa NBNDb NODi SBND SBNDa SBNDb STOi ABND ABNDa ABNDb ABNDc ABNDd ASD ASDa ASDb; unfold AMALLOC_STACK in *; dlia).
    xport MTX9 MU5 WM5 ltac:(clear -SPR LO BOT STK3 AHI0 ACE TL1 SA1 SA3 DL1 DL4 TBND TBNDa TBNDb TIMG TIMGa TIMGb NBND NBNDa NBNDb NODi SBND SBNDa SBNDb STOi ABND ABNDa ABNDb ABNDc ABNDd ASD ASDa ASDb; unfold AMALLOC_STACK in *; dlia).
    xport PAS MU5 WM5 ltac:(ub D_t_p; clear -Y SPR LO BOT STK3 AHI0 ACE TL1 SA1 SA3 DL1 DL2 DL4 DL5 OP WB C_p D_n_p D_s_p WTF TBND TBNDa TBNDb TIMG TIMGa TIMGb NBND NBNDa NBNDb NODi SBND SBNDa SBNDb STOi OPs OPsa OPsb OPi ABND ABNDa ABNDb ABNDc ABNDd ASD ASDa ASDb; unfold wt_facts, AMALLOC_STACK in *; dlia).
    assert (JSTq : junk_at m5 837408 32).
    { eapply junk_frame; [exact JST| exact MU5| exact WM5| intros _]. cbn [disjoint_from fst snd]. clear -SPR LO BOT STK3 AHI0 ACE TL1 SA1 SA3 DL1 DL4 TBND TBNDa TBNDb TIMG TIMGa TIMGb NBND NBNDa NBNDb NODi SBND SBNDa SBNDb STOi ABND ABNDa ABNDb ABNDc ABNDd ASD ASDa ASDb; unfold AMALLOC_STACK in *; dlia. }
    assert (JBSq : junk_at m5 837440 512).
    { eapply junk_frame; [exact JBS| exact MU5| exact WM5| intros _]. cbn [disjoint_from fst snd]. clear -SPR LO BOT STK3 AHI0 ACE TL1 SA1 SA3 DL1 DL4 TBND TBNDa TBNDb TIMG TIMGa TIMGb NBND NBNDa NBNDb NODi SBND SBNDa SBNDb STOi ABND ABNDa ABNDb ABNDc ABNDd ASD ASDa ASDb; unfold AMALLOC_STACK in *; dlia. }
    assert (JGLq : junk_at m5 837976 16).
    { eapply junk_frame; [exact JGL| exact MU5| exact WM5| intros _]. cbn [disjoint_from fst snd]. clear -SPR LO BOT STK3 AHI0 ACE TL1 SA1 SA3 DL1 DL4 TBND TBNDa TBNDb TIMG TIMGa TIMGb NBND NBNDa NBNDb NODi SBND SBNDa SBNDb STOi ABND ABNDa ABNDb ABNDc ABNDd ASD ASDa ASDb; unfold AMALLOC_STACK in *; dlia. }
    assert (NR5 : (a_nsec st <> a_nres st /\ nres' = a_nres st)
                  \/ (a_nsec st = a_nres st /\ nres' = a_nres st + 16384
                      /\ rw_cells bsegs m5 (al_ptr_array L + 8 * a_nres st + 8) [CB (Z.to_nat (131072 - 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (131072 - 8)))])).
    { destruct NR' as [D|(D1 & D2 & ZC)]; [left; exact D| right]. split; [exact D1|]. split; [exact D2|].
      xport ZC MU5 WM5 ltac:(ub D_t_p; clear -Y SPR LO BOT STK3 AHI0 ACE TL1 SA1 SA3 DL1 DL2 DL4 DL5 OP WB NRB' D2 C_p D_n_p D_s_p WTF TBND TBNDa TBNDb TIMG TIMGa TIMGb NBND NBNDa NBNDb NODi SBND SBNDa SBNDb STOi OPs OPsa OPsb OPi ABND ABNDa ABNDb ABNDc ABNDd ASD ASDa ASDb; unfold wt_facts, AMALLOC_STACK in *; dlia). exact ZC. }
    (* [comment removed for export] *)
    assert (MUW : munch (WT L (bv_unsigned sp) a ms (a_nsec st) (a_nres st) nres') m m5).
    { eapply munch_trans; [eapply munch_weaken; [| exact MU4]|].
      2: eapply munch_trans; [eapply munch_weaken; [| exact MUS]| eapply munch_weaken; [| exact MU5]].
      all: unfold WT, sub_fp, AINSTANCE; cbn [outside]; clear -MSB; intros q Hq; lia. }
    assert (WMW : wmono bsegs m m5). { eapply wmono_trans; [exact WM4|]. eapply wmono_trans; [exact WMS| exact WM5]. }
    assert (USR : junk_at m5 (a + 6144) (ms - 6144)).
    { replace (ms - 6144) with (Z.of_nat (cells_size [CB (Z.to_nat n) (repeat (Z_to_bv 8 190) (Z.to_nat (Z.min n 4096)) ++ repeat (Z_to_bv 8 0) (Z.to_nat n - Z.to_nat (Z.min n 4096)))]) + (ms - 6144 - n))
        by (cbn [cells_size csize]; clear -N; lia).
      apply junk_merge; [eapply junk_of_cells; exact USR5| cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by (clear -N; lia); exact TLJ5| clear; lia| clear -MSR NSE RSR N; lia]. }
    destruct (store_sec DI AQ AFK HL CI CI_OK CI_OK2 L RNG RNG5 (bv_unsigned sp) lo m m5 st X LB n a nres' id sj5 RESV
                ALO ARNG0 AR BL HFK N PRIM HF ROK) as [PRES AHP5].
    all: try lazymatch goal with
         | |- fp_le _ _ => eapply fp_le_trans; [exact FPLE| exact FPLE5]
         | |- munch _ _ _ => exact MUW
         | |- wmono _ _ _ => exact WMW
         | |- u64arr _ _ _ _ => exact STATS5
         | |- ADEPOT _ _ _ => exact DEP5
         | |- junk_at _ (_ + 6144) _ => exact USR
         | |- junk_at _ _ _ => assumption
         | |- fill_at _ _ _ _ => assumption
         | |- rng _ (shad _) _ => eapply rng_fp_le; [exact FPLE5| exact RSCH]
         | |- rng _ (al_ptr_array _) _ => eapply rng_fp_le; [exact FPLE5| exact RPA']
         | |- rng _ _ _ => eapply rng_fp_le; [exact FPLE5| exact RCH]
         | |- _ \/ _ => exact NR5
         | |- rw_cells _ _ _ _ => assumption
         | |- @eq nat _ _ => exact LSJ5
         | |- _ => clear -LO BOT STK3 SP47 IDR NRB'; unfold AMALLOC_STACK in *; lia
         end.
    all: match goal with |- amalloc_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => idtac | |- ?G => idtac "REMST" G end.
    unfold amalloc_post. split; [eapply fp_le_trans; [exact FPLE| exact FPLE5]|].
    do 15 eexists. exists m5. split; [reflexivity|]. split; [exact MI5|]. split; [exact ST5|]. split; [exact PRES|].
    cbn [fst snd]. eexists (a + 6144), _. split; [reflexivity|].
    split. { unfold ablock_range. atop_facts. pose proof (sec_facts n N PRIM) as (_ & _ & _ & RSRx & _ & NSEx & MSEx & _). fold ms in MSEx. clear -AHI0 ACE AAL N MSR NSE RSR RSRx NSEx MSEx ABND ABNDa ABNDb ABNDc ABNDd.
             split; [eapply ablk_sub; [exact AHI0| lia| lia]|]. split; [lia|]. split; [lia|]. Z.div_mod_to_equations. lia. }   (* [comment removed for export] *)
    split; [exact AHP5|]. split; [exact USR5|].
    split; [eapply rng_sub'; [eapply rng_fp_le; [exact FPLE5| exact RCH]|]; clear -N MSR NSE RSR; lia|].
    split. { eapply rng_sub'; [eapply rng_fp_le; [exact FPLE5| exact RSCH]|]. rewrite !shad_div, shlen_div. clear -N MSR NSE RSE RSR AAL MSM. Z.div_mod_to_equations. lia. }
    intros _. unfold aptr_addr. pose proof (st_sec_fields st nres' a ms n) as (_ & _ & _ & _ & _ & _ & E7 & _). rewrite E7, lookup_insert_eq.
    cbn [chunk_user_beg]. unfold PG. rewrite RZ. clear; lia. }
  (* [comment removed for export] *)
  eapply (calloc_sec_spec RNG (KS RESV st n) (KS2 st n) _ (sfresh RESV st n) _ _ gp tp t0c t1c t2c _ _ _ _ _ _ a4c a5c a6c a7c _ _ _ _ _ _ _ _ _ _ t3c t4c t5c t6c F fc m4 n
            (al_ctx L) (al_t L) (a_ptr_array st) (a_nres st) (a_nsec st) lo sj4 (bv_unsigned srt) jstats jbsl jglob jslot).
  all: rewrite ?PAE.
  all: try lazymatch goal with
       | |- forall x, _ => idtac
       | |- stk _ _ _ _ => rewrite unsigned_lit by (clear -SPR HspA LO BOT STK3; unfold AMALLOC_STACK in *; lia);
                           replace (bv_unsigned spA + -128) with (bv_unsigned sp - 2272) by (clear -HspA; lia); exact ST4
       | |- mem_inv _ _ => exact MI4
       | |- large_cells _ _ _ _ => exact LC4
       | |- u64arr _ _ _ _ => exact STATS'
       | |- @eq word _ _ => first [exact TP | reflexivity]
       | |- @eq bool _ _ => exact PRIM
       | |- @eq nat _ _ => exact LSJ'
       | |- rw_cells _ _ _ [C1 (Z_to_bv 8 (bv_unsigned _))] => rewrite Z_to_bv8_bv_unsigned; exact J128
       | |- rw_cells _ _ _ [C1 _; C1 _; C1 _; C1 _] => exact MTX
       | |- rw_cells _ _ _ [C8 _; C8 _] => exact I112'
       | |- rw_cells _ _ _ [CB 32 _] => exact J136
       | |- rw_cells _ _ _ [CB 512 _] => exact J168
       | |- rw_cells _ _ _ [CB 16 _] => exact J704
       | |- _ mod 16384 = 0 => exact (proj1 WR)
       | |- iclr _ _ => exact TL4 | |- AIMG_HI <= al_ctx _ => exact CL3   (* [comment removed for export] *)
       | |- sclr (al_ctx _) _ => exact CL1 | |- sclr (al_t _) _ => exact TL1   (* [comment removed for export] *)
       | |- ablk (al_ptr_array _) _ => pose proof (ao_ptr L ALO) as OPx; unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in OPx; unfold ablk, KLS, AIMG_HI; clear -OPx; lia
       | |- ablk _ _ => assumption
       | |- _ \/ _ => first [ub D_t_p; clear -Y; lia | ub D_c_p; clear -Y; lia | unboxed CL5]
       | |- rng _ _ (bv_unsigned _ - _) => rewrite unsigned_lit by (clear -SPR HspA LO BOT STK3; unfold AMALLOC_STACK in *; lia);
                         eapply rng_sub'; [exact RSTK|]; clear -LO HspA SP47 BOT STK3; unfold AMALLOC_STACK in *; lia
       | |- rng _ _ _ => assumption
       end.
  all: try lazymatch goal with
       | |- forall x, _ => idtac
       | |- _ => rewrite ?unsigned_lit by (clear -SPR HspA LO BOT STK3; unfold AMALLOC_STACK in *; lia);
              unfold AIMG_HI, AREQMAX, AMALLOC_STACK in *; clear -N LO HspA BOT STK3 SPR TL1 TL2 TL4 CL1 CL2 CL3 OP WB WR TBND TBNDa TBNDb TIMG TIMGa TIMGb CBND CBNDa CBNDb CTXi OPs OPsa OPsb OPi; lia
       end.
  all: match goal with |- forall x, _ => idtac | |- ?G => idtac "REMCS" G end.
  - (* [comment removed for export] *) exact JSL.
  - (* [comment removed for export] *) exact FROK.
  - (* [comment removed for export] *)
    intros a RNG' ms' HF A0 AAL ACE LE.
    destruct (sfresh_false_cases RESV st n a HF) as [B|[E|(B1 & B2 & B3)]].
    + rewrite (KS_unr_bad RESV st n a B). apply implF_ret_unr.
    + exfalso. unfold is_err, TWO64 in E. apply Z.ltb_lt in E. atop_facts. clear -E ACE MSB. lia.
    + rewrite (KS_unr_phantom RESV st n a B1 B2 B3). apply implF_ret_unr.
  - (* [comment removed for export] *)
    intros a RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' HF HNE (m1 & MU1 & WM1 & LP) STc.
    rewrite unsigned_lit in MU1, LP, STc by (clear -SPR HspA LO BOT STK3; unfold AMALLOC_STACK in *; lia).
    replace (bv_unsigned spA + -128 - 48) with (bv_unsigned sp - 2320) in MU1, LP by (clear -HspA; lia).
    replace (bv_unsigned spA + -128) with (bv_unsigned sp - 2272) in MU1, STc by (clear -HspA; lia).
    rewrite ?PAE in LP. rewrite ?PAE in HNE.
    rewrite (KS_fresh_nocommit RESV st n a HF HNE), fin_sec_nocommit. fold ms.
    eapply (TS a (a_nres st) RNG' m1 m'); [exact HF| exact MU1| exact WM1| exact LP| exact STc].
  - (* [comment removed for export] *)
    intros a HF HE NRB. rewrite <- ?PAE. apply (KS_fresh_commit RESV st n a HF HE NRB).
  - (* [comment removed for export] *)
    intros a RNG' ms' HF HE OV. rewrite (KS_fresh_overflow RESV st n a HF HE OV). apply implF_ret_unr.
  - (* [comment removed for export] *)
    intros a r RNG' ms' NE R0 RCE. rewrite <- ?PAE in NE. rewrite (KS2_other st n a r NE R0 ltac:(unfold alloc_ceiling; atop_facts; exact RCE)). apply implF_ret_unr.
  - (* [comment removed for export] *)
    intros a RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' HF HE (m1 & MU1 & WM1 & LP) STc.
    rewrite unsigned_lit in MU1, LP, STc by (clear -SPR HspA LO BOT STK3; unfold AMALLOC_STACK in *; lia).
    replace (bv_unsigned spA + -128 - 48) with (bv_unsigned sp - 2320) in MU1, LP by (clear -HspA; lia).
    replace (bv_unsigned spA + -128) with (bv_unsigned sp - 2272) in MU1, STc by (clear -HspA; lia).
    rewrite ?PAE in LP. rewrite ?PAE in HE.
    pose proof LP as LP0. unfold large_post in LP0. cbv zeta in LP0.
    destruct LP0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NRB' & _).
    rewrite <- ?PAE. rewrite (KS2_granted st n a) by (rewrite PAE; unfold alloc_ceiling; atop_facts; clear -OP WB NRB' OPs OPsa OPsb OPi; lia).
    rewrite fin_sec_commit. fold ms. unfold K_CHUNKS_BLOCK.
    eapply (TS a (a_nres st + 16384) RNG' m1 m'); [exact HF| exact MU1| exact WM1| exact LP| exact STc].
Qed.
End S.
End CANSEC1.
