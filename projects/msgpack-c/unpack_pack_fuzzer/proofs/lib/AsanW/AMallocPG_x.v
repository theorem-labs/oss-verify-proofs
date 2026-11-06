(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require ExecF ITreeA StepF SysStepF.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AImg AProto ABase ABytes ASecFacts AMalloc_iface ADepot_iface ARep ALayout AHeapP ARepKit ARepFrame ARepExt ARepExt2 AKit AKit2 AModelFacts APrimFacts.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_apoison.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_aalloc1.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_aalloc2.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_aalloc F_amalloc_icpt.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_amalloc_pre.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_aalloc3.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_aaligned_tail.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_amalloc_arep.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require ARepStore.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require ARefill_iface.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require ARefillP.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require ACallocG.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require RunDraw.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AAlignedPG.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AEmbRep AFrameD AEmbFrame.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_arefill.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require ARefill_iface_x ARefillP_x.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_acache_x.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_amalloc_null ANullKit AC6Frame ANullPres.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AMalloc_iface2.
Module AMallocPG_x.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Exec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Tac. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ITreeA. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.SysStepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABytes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ASecFacts. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AMalloc_iface. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ADepot_iface. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARep. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ALayout. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AHeapP. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepKit. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepFrame. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepExt. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepExt2. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit2. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AModelFacts. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.APrimFacts.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apoison.F_apoison.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc1.F_aalloc1.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc2.F_aalloc2. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_amalloc_icpt.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_amalloc_pre.F_amalloc_pre.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc2.F_aalloc2g.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc3.F_aalloc3g.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aaligned_tail.F_amalloc_tailg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_amalloc_arep.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepStore.ARepStore.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepStore.ARepStoreG. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARefill_iface.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARefillP.ARefillP.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ACallocG.ACallocG.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

 Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AAlignedPG.AMallocPG. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AEmbRep. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFrameD. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AEmbFrame.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_arefill.F_arefill_x. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARefill_iface_x. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARefillP_x.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARefillP.ARefillP_e. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_acache_x.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ACallocG.ACallocG_x. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_amalloc_null. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ANullKit. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AC6Frame. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ANullPres.
Export OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AMalloc_iface2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSECX0. Context {rc : runConstT} {ov : annOV}.

Definition c6_at (RESV : list (Z * Z)) (L : alayout) (RNG' : footprint) (st' : astate) (ms' : machine_state) : Prop :=
  axg RESV RNG' st' (ms_mem ms') /\ axflags L st' (ms_mem ms').

Definition amalloc_post_x (CI : list (Z * Z)) (AHEAP : alayout -> footprint -> astate -> list ablock -> amem -> Prop)
    (L : alayout) (RESV : list (Z * Z)) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (n lo : Z) (m : amem)
    (r : astate * option aptr) (RNG' : footprint) : machine_state -> Prop :=
  fun ms' => c6_at RESV L RNG' (fst r) ms' /\
    match snd r with
    | Some _ => amalloc_post CI AHEAP L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB n lo m r RNG' ms'
    | None => fp_le RNG RNG' /\ exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (ret_pc ra) fc None m' (seg_rom asegs)
        /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
        /\ aheap_pres_e CI LB (bv_unsigned sp) m m'
        /\ AHEAP L RNG' (fst r) LB m'
        /\ rw_cells asegs m' AERRNO [C4 (Z_to_bv 64 12)]
    end.
End CANSECX0.

Section CANSEC1. Context {rc : runConstT} {ov : annOV}.

Local Lemma ablk_int : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6483968 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
Local Lemma aobj_int : forall a n, aobj a n -> 0x10000 <= n ->
  6483968 <= a /\ a + n <= ATOP /\ exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof.
  intros a n H Hn. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. destruct H as (H1 & H2 & H3 & H4 & H5).
  split; [lia|]. split; [lia|]. destruct H4; [exists 0 | exists 1]; lia.
Qed.
Local Lemma aobj4_int : forall a, aobj a 4096 ->
  4096 <= a /\ a + 4096 <= ATOP
  /\ (exists k, 0 <= k <= 1 /\ a + 4096 <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a)
  /\ (exists j, 0 <= j <= 1 /\ a + 4096 <= 65536 + j * 18446744073709551616 /\ 6483968 * j <= a).
Proof.
  intros a H. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. destruct H as (H1 & H2 & H3 & H4 & H5).
  split; [lia|]. split; [lia|]. split; [destruct H4; [exists 0 | exists 1]; lia | destruct H5 as [_ [H5|H5]]; [exists 0 | exists 1]; lia].
Qed.

Local Ltac dlia := repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
Section S.
Variable DI : ADepotIface.
Variables (AQ ASEC : alayout -> astate -> aconc -> amem -> Prop) (AFK : alayout -> list ablock -> amem -> Prop).
Hypothesis HL : ahole_laws (AH DI AQ ASEC AFK).
Hypothesis HLD : ahole_lawsD (AH DI AQ ASEC AFK).
Hypothesis EXHW : exh_first_stmt.
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI) CI.

Hypothesis CI_OK2 : Forall (fun iv => snd iv <= AINSTANCE \/ AINSTANCE + 728 <= fst iv) CI.

Hypothesis CI_OK3 : Forall (fun iv => (snd iv <= AEMB \/ AEMB + 56 <= fst iv) /\ (snd iv <= 0x15bd20 \/ 0x15bd21 <= fst iv)) CI.

Theorem amalloc_prim_x : forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (n lo : Z) (tr : list Z) (RESV : list (Z * Z)),
  ann_ov (a_next st) = None ->

  is_primary n = true ->

  AHEAP_P (AH DI AQ ASEC AFK) L RNG st LB m ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - 4608 ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 n -> 1 <= n <= AREQMAX ->
  aunw m L RNG lo AMALLOC_PC sp s0 ra tr ->
  bv_unsigned s0 <> bv_unsigned sp + 8 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AMALLOC_PC ->
  bv_unsigned sp mod 16 = 0 ->
  rng RNG lo (bv_unsigned sp - lo) ->
  aresv_ok L RESV ->

  bv_unsigned fc < 32 -> axg RESV RNG st m -> axflags L st m -> (let '(_, cap0, _) := a_emb st in cap0 <= 2 ^ 23) ->
  (exists e0 : word, rw_cells asegs m AERRNO [C4 e0]) ->
  implS asegs RNG (aembed ATOP (amalloc ATOP RESV st n))
        (epostF (amalloc_post_x CI (AHEAP_P (AH DI AQ ASEC AFK)) L RESV RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB n lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AMALLOC_SYM) fc None m (seg_rom asegs)).
Proof.
  intros until RESV. intros OVF PRIM AHP MI ST BOT LO TP Ha0 NR AUNW S0NE RA4 RANE SP16 RSTK ROK FC C6G C6F CAPB ERRC.
  assert (N : 1 <= n <= AREQMAX) by exact NR. assert (N1 : 1 <= n) by (clear -NR; lia).

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
  remember (class_id (needed_size n)) as c eqn:HC0. symmetry in HC0.
  pose proof (prim_facts n N1 PRIM) as (NS & RZR & RZE & RZM & RLR & RSR & RSM & NSR).
  pose proof (prim_class_facts n c N1 PRIM HC0) as (C16 & NSZ & SM16 & SMALL & MCB). clear SMALL.
  pose proof (cls_facts c C16) as (SZB & _ & _ & _).
  assert (HCK : 1 <= c < K_NUM_CLASSES) by (unfold K_NUM_CLASSES; clear -C16; lia).
  assert (NM8 : needed_size n mod 8 = 0) by (rewrite NS; clear -RSM RZM; Z.div_mod_to_equations; lia).

  pose proof AR as AR0. destruct AR0 as (WF & RT & INST & THR & CLS & HQ & HS & HD & HRO & RT2 & AVL & RT3).
  destruct THR as (T0 & T40 & CACHES & CSTATS & [sj [STATS LSJ]] & UNW).
  pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVE & FRESH & UNIQ).
  destruct (PERC c HCK) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & LENF & LENC & CNTB & ND & RANGE).
  pose proof (alayout_space L ALO) as (SP1 & SP2 & SP3 & SP4).
  pose proof (alayout_t L ALO) as (TL1 & TL2 & TL3 & TL4).
  pose proof (alayout_ctx L ALO) as (CL1 & CL2 & CL3 & CL4 & CL5).
  pose proof (alayout_depot L ALO) as (DL1 & DL2 & DL3 & DL4 & DL5 & DL6 & DL7 & DL8 & DL9 & DL10).
  pose proof (aobj4_int _ (ao_t L ALO)) as (_ & _ & (kT & TBND & TBNDa & TBNDb) & (jT & TIMG & TIMGa & TIMGb)).
  pose proof (aobj_int _ _ (ao_ctx L ALO) ltac:(clear; lia)) as (CTXi & _ & (kC & CBND & CBNDa & CBNDb)).
  pose proof (aobj_int _ _ (ao_nodes L ALO) ltac:(clear; lia)) as (NODi & _ & (kN & NBND & NBNDa & NBNDb)).
  pose proof (aobj_int _ _ (ao_store L ALO) ltac:(clear; lia)) as (STOi & _ & (kR & SBND & SBNDa & SBNDb)).
  pose proof (aobj_int _ _ (ao_fake L ALO) ltac:(clear; lia)) as (OFKi & _ & (kF & OFKs & OFKsa & OFKsb)).
  pose proof (aobj4_int _ (ao_dtls L ALO)) as (_ & _ & (kD & DBND & DBNDa & DBNDb) & (jD & DIMG & DIMGa & DIMGb)).
  pose proof (alayout_stack L ALO) as (STK1 & STK2 & STK3).
  pose proof (alayout_res_disj L ALO) as [SCX TSP].
  pose proof RT as RT0.
  destruct RT0 as (GPG & GOT & GOT80 & RIC & LS1 & REAL & IMAX4 & FLG5 & FLG & HPP & SHB & CANP & TI & TK & INI2 & LAY & MCS & OOM3
                    & PGC & HK2 & CF8 & CF34 & CSMT & T88 & TSD & LS2 & CT8 & CT).
  pose proof INI2 as INI. rw_split INI 1%nat INI1 INIx. clear INIx.
  destruct OOM3 as [oomb OOM]. rw_split OOM 2%nat OOMx RSS. clear OOMx.
  pose proof IMAX4 as IMAX. rw_split IMAX 3%nat IMAX3 IMAXx. clear IMAXx.
  pose proof T0 as TT0. rw_split TT0 1%nat TTctx TT.
  pose proof ARNG as ARNG0. destruct ARNG as (RIMG & RT4 & RCTX & RNO & RSTO & RRI & RFK & RSFK & RDTLS & RCLS).
  assert (RCTX4 : rng RNG (al_ctx L) 4096) by (eapply rng_sub'; [exact RCTX|]; clear; lia).
  word_range sp SPR.
  box CL5. box DL7. box DL8. box DL9. box DL10. box TSP. box SCX.

  rewrite (amalloc_prim_eq RESV st n c N1 PRIM HC0).

  iprefix. eapply evtF_cut.
  { eapply (malloc_pre_spec L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n (al_t L) lo (al_top L) (al_bot L) tr trc).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => exact ST
         | |- mem_inv _ _ => exact MI
         | |- allocA_cells _ _ _ => unfold allocA_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end)
         | |- poison_cells _ => unfold poison_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end)
         | |- u64arr _ _ _ _ => exact STATS
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
  cbv beta. intros ms4 P4. unfold malloc_pre_post in P4.
  destruct P4 as (spA & t0c & t1c & t2c & a4c & a5c & a6c & a7c & t3c & t4c & t5c & t6c & s0A & s1A & s2A & s3A & s4A & s5A & s0i & fr0 & junk2 & tb & m4
                  & -> & HspA & MU4 & WM4 & MI4 & ST4 & FRa & FR16 & SS & TB & LTB & TRF & FRS & UW4).
  apply evtF_done.
  assert (AR4 : AREP (AH DI AQ ASEC AFK) L st X m4).
  { eapply (AREP_frame_pre _ HL L st X m m4); [exact ALO | exact AR | exact MU4 | exact WM4 | | exact UW4].
    apply Forall_cons; [unfold apre; cbn [fst snd]; intros _; left; unfold AMALLOC_STACK in *; clear -LO BOT STK3; lia|].
    apply Forall_cons; [unfold apre; cbn [fst snd]; intros _; right; split; reflexivity| apply Forall_nil]. }

  destruct (c6_frame L RESV RNG st m m4 _ ALO ROK C6G C6F MU4) as [C6G4 C6F4].
  { apply Forall_cons; [unfold c6_piece; cbn [fst snd]; intros _; left; unfold AMALLOC_STACK in *; clear -LO BOT STK3; lia|].
    apply Forall_cons; [unfold c6_piece; cbn [fst snd]; intros _; right; left; clear; lia| apply Forall_nil]. }

  eapply (@calloc_arep_gen_x _ _ _ HL HLD _ RESV _ _ L RNG _ _ gp tp t0c t1c t2c _ _ _ _ _ _ a4c a5c a6c a7c _ _ _ _ _ _ _ _ _ _ t3c t4c t5c t6c F fc m4 st X c lo (needed_size n)
            ALO ARNG0 AR4 MI4).
  all: try lazymatch goal with
       | |- arng _ _ _ => exact ARNG0
       | |- stk _ _ _ _ => rewrite unsigned_lit by (clear -SPR HspA LO BOT STK3; unfold AMALLOC_STACK in *; lia);
                           replace (bv_unsigned spA + -128) with (bv_unsigned sp - 2272) by (clear -HspA; lia); exact ST4
       | |- ATOP <= _ => clear -LO BOT STK3; unfold AMALLOC_STACK in *; lia
       | |- _ <= bv_unsigned _ - _ => rewrite unsigned_lit by (clear -SPR HspA LO BOT STK3; unfold AMALLOC_STACK in *; lia);
                                    clear -LO HspA BOT STK3; unfold AMALLOC_STACK in *; lia
       | |- @eq word _ _ => first [exact TP | reflexivity]
       | |- 16 <= _ <= 65536 => clear -NSR; lia
       | |- _ mod 8 = 0 => exact NM8
       | |- class_id _ = _ => exact HC0
       | |- rng _ _ _ => rewrite unsigned_lit by (clear -SPR HspA LO BOT STK3; unfold AMALLOC_STACK in *; lia);
                         eapply rng_sub'; [exact RSTK|]; clear -LO HspA SP47 BOT STK3; unfold AMALLOC_STACK in *; lia
       | |- exh_first_stmt => exact EXHW
       | |- aresv_ok _ _ => exact ROK
       | |- bv_unsigned _ < 2 ^ 63 => rewrite unsigned_lit by (clear -SPR HspA LO BOT STK3; unfold AMALLOC_STACK in *; lia); clear -SP47 HspA; lia
       | |- bv_unsigned _ < 32 => exact FC
       | |- _ -> axflag _ _ _ _ => intros NC24x; exact (C6F4 c HCK NC24x)
       | |- axg _ _ _ _ => exact C6G4
       | |- context [a_emb _] => exact CAPB
       | |- forall _, _ => idtac
       end.
  1: {
       intros st2 RNG' ms' RF. unfold aret_xf in RF. cbv zeta in RF. pose proof atop_range as ATR.
       pose proof C6G4 as (_ & ECp & _ & ECLp). unfold emb_cells in ECp. unfold emb_clr in ECLp.
       destruct (a_emb st) as [[d0 cap0] sz0] eqn:EA. destruct (a_emb st2) as [[d2 cap2] sz2] eqn:EA2.
       destruct RF as (FPLE & t0r & t1r & t2r & a1r & a2r & a3r & a4r & a5r & a6r & a7r & t3r & t4r & t5r & t6r & mr
                       & -> & MIr & STr & STEQ & ARr & ARNGr & AXFr & AXGr & (d1 & cap1 & MUr & PV1 & PV2 & TOP1)).
       assert (USP : bv_unsigned (Z_to_bv 64 (bv_unsigned spA + -128)) = bv_unsigned sp - 2272)
         by (rewrite unsigned_lit by (clear -SPR HspA LO BOT ATR; lia); clear -HspA; lia).
       rewrite USP in MUr, STr.

       assert (B0 : bufok RESV st d0 cap0).
       { unfold bufok. destruct (Z.eqb_spec cap0 0) as [E0|NZ]; [left; lia|]. right.
         destruct ECp as (_ & _ & _ & _ & _ & _ & _ & _ & TOP & _). split; [exact TOP|]. destruct ECLp as [Q|Q]; [exfalso; exact (NZ Q)| exact Q]. }
       assert (B1 : bufok RESV st d1 cap1).
       { destruct (Z_le_gt_dec cap1 0) as [LE|GT]; [left; exact LE|]. destruct PV1 as [[E1 E2]|AV]; [rewrite E1, E2; exact B0|].
         right. split; [destruct TOP1 as [Q|Q]; [lia| exact Q]| exact AV]. }
       assert (B2 : bufok RESV st d2 cap2).
       { destruct PV2 as [[E1 E2]|AV]; [rewrite E1, E2; exact B0|].
         pose proof AXGr as (_ & EC2 & _). unfold emb_cells in EC2. rewrite EA2 in EC2. destruct (Z.eqb_spec cap2 0) as [E0|NZ]; [left; lia|]. right.
         destruct EC2 as (_ & _ & _ & _ & _ & _ & _ & _ & TOP & _). split; [exact TOP| exact AV]. }

       set (SPc := bv_unsigned sp - 2272) in *.
       assert (SPHIc : ATOP <= SPc) by (subst SPc; clear -LO BOT; lia).
       assert (SPHI : ATOP <= bv_unsigned sp) by (clear -LO BOT; lia).
       set (Wf := [(SPc - 2096, SPc); (al_t L + 208, al_t L + 2768); (aregion_info L c, aregion_info L c + 8);
                   (aregion_info L c + 68, aregion_info L c + 69); (AEMB, AEMB + 56); (d0, d0 + cap0); (d1, d1 + cap1); (d2, d2 + cap2)]%Z).
       change (munch Wf m4 mr) in MUr.
       assert (PCSf : Forall (nf_piece L RESV st SPc c) Wf).
       { assert (BK : forall d cap, bufok RESV st d cap -> nf_piece L RESV st SPc c (d, d + cap)).
         { intros d cap [B|[Bt Ba]] LT; cbn [fst snd] in LT; [lia|]. unfold nf_kind. cbn [fst snd]. do 4 right. left.
           replace (d + cap - d) with cap by lia. split; assumption. }
         subst Wf. repeat (apply Forall_cons); try apply Forall_nil; try (apply BK; assumption); intros _; unfold nf_kind; cbn [fst snd].
         - left. subst SPc. clear -LO BOT. lia.
         - right; left. clear. lia.
         - right; right; left. clear. lia.
         - right; right; left. clear. lia.
         - right; right; right; left. clear. lia. }
       assert (OUTS : forall x, SPc <= x -> outside Wf x)
         by (intros x Hx; apply (nf_outside L RESV st SPc c ALO ROK HCK SPHIc Wf x PCSf); left; exact Hx).

       apply rw_cells_of_u64arr in TB. rewrite LTB in TB.
       assert (FRar : rw_cells asegs mr (bv_unsigned spA + -128)
                        [CB 8 fr0; C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 16); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5A;
                         C8 s4A; C8 s3A; C8 s2A; C8 s1A; C8 s0A; C8 (Z_to_bv 64 0x3cc98)]).
       { replace (bv_unsigned spA + -128) with (bv_unsigned sp - 2272) by (clear -HspA; lia).
         eapply cells_frameO; [exact FRa| exact MUr|]. intros x Hx. apply OUTS. subst SPc. clear -Hx. lia. }
       assert (FR16r : rw_cells asegs mr (bv_unsigned sp + -2144) [C8 s0i; C8 (Z_to_bv 64 0x5e728)])
         by (eapply cells_frameO; [exact FR16| exact MUr|]; intros x Hx; apply OUTS; subst SPc; clear -Hx; lia).
       assert (SSr : rw_cells asegs mr (bv_unsigned sp + -2128) [C8 (Z_to_bv 64 (bv_unsigned sp + -2128 + 16)); C8 (Z_to_bv 64 (1 + Z.of_nat (length trc)))])
         by (eapply cells_frameO; [exact SS| exact MUr|]; intros x Hx; apply OUTS; subst SPc; clear -Hx; lia).
       assert (TBr : rw_cells asegs mr (bv_unsigned sp + -2128 + 16) [CB (8 * 255) (u64s tb)])
         by (eapply cells_frameO; [exact TB| exact MUr|]; intros x Hx; apply OUTS; subst SPc; clear -Hx; lia).
       assert (FRSr : rw_cells asegs mr (bv_unsigned sp + -72) [C8 sp; CB 8 junk2; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
         by (eapply cells_frameO; [exact FRS| exact MUr|]; intros x Hx; apply OUTS; subst SPc; clear -Hx; lia).
       destruct ERRC as [e0 ERR0].
       assert (ERR4 : rw_cells asegs m4 AERRNO [C4 e0]).
       { eapply cells_frameO; [exact ERR0| exact MU4|]. cbn [cells_size csize Nat.add]. intros x Hx. cbn [outside].
         unfold AERRNO, ATP in Hx. clear -Hx ATR LO BOT TIMG TIMGa TIMGb. repeat split; lia. }
       assert (ERRr : rw_cells asegs mr AERRNO [C4 e0]).
       { eapply cells_frameO; [exact ERR4| exact MUr|]. cbn [cells_size csize Nat.add]. intros x Hx.
         assert (BI : forall d cap, bufok RESV st d cap -> ~ (d <= x < d + cap)).
         { intros d cap [B|[_ AV]]; [clear -B; lia|]. unfold avoids_all in AV. rewrite forallb_app in AV. apply andb_prop in AV as [AV _].
           destruct ROK as (PCI & _). apply (avoids_pcov_out RESV d cap 0x10000 AIMG_HI x PCI AV). unfold AIMG_HI, AERRNO, ATP in *. clear -Hx. lia. }
         pose proof (BI _ _ B0) as Q0. pose proof (BI _ _ B1) as Q1. pose proof (BI _ _ B2) as Q2.
         subst Wf. cbn [outside]. unfold aregion_info, K_SPACE_SIZE, ARI_STRIDE. change (2^37) with 137438953472.
         unfold AEMB, AERRNO, ATP in *. subst SPc.
         clear -Hx Q0 Q1 Q2 ATR LO BOT TIMG TIMGa TIMGb SP1 C16. repeat split; lia. }
       pose proof ARr as (_ & RTr & _).
       destruct RTr as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & OOM3r & _).
       destruct OOM3r as [oombr OOMr]. rw_split OOMr 2%nat OOMxr RSSr. clear RSSr.

       apply implS_ret.
       replace (ret_pc (Z_to_bv 64 0x3cf68)) with (Z_to_bv 64 0x3cf68) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
       pose proof ARNGr as (RIMGr & _).
       assert (RSTKr : rng RNG' lo (bv_unsigned sp - lo)) by (eapply rng_fp_leG; [exact FPLE | exact RSTK]).
       eapply evtF_cut.
       { eapply (allocN_spec RNG' spA gp tp t0r t1r t2r _ _ a1r a2r a3r a4r a5r a6r a7r _ _ _ _ _ _ _ _ _ _ t3r t4r t5r t6r
                   s0A s1A s2A s3A s4A s5A s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0x3cc98) _ _ fr0 oombr F fc mr lo);
           first [ exact FRar | exact MIr | exact OOMxr | exact RIMGr
                 | replace (bv_unsigned spA + -128) with (bv_unsigned sp - 2272) by (clear -HspA; lia); exact STr
                 | eapply rng_sub'; [exact RSTKr|]; clear -HspA LO; lia
                 | clear -BOT ATR; lia
                 | clear -LO HspA; lia ]. }
       cbv beta. intros ms1 P1.
       destruct P1 as (t0n & t1n & t2n & a1n & a2n & a3n & a4n & a5n & a6n & a7n & t3n & t4n & t5n & t6n & m1 & -> & MU1 & WM1 & MI1 & ST1 & OOM1).
       assert (OUT1 : forall x, AIMG_HI <= x -> outside [(AOOM, AOOM + 1)]%Z x)
         by (intros x Hx; cbn [outside]; unfold AOOM, AIMG_HI in *; clear -Hx; lia).
       assert (FR16n : rw_cells asegs m1 (bv_unsigned sp + -2144) [C8 s0i; C8 (Z_to_bv 64 0x5e728)])
         by (eapply cells_frameO; [exact FR16r| exact MU1|]; intros x Hx; apply OUT1; unfold AIMG_HI; clear -Hx ATR LO BOT; lia).
       assert (SSn : rw_cells asegs m1 (bv_unsigned sp + -2128) [C8 (Z_to_bv 64 (bv_unsigned sp + -2128 + 16)); C8 (Z_to_bv 64 (1 + Z.of_nat (length trc)))])
         by (eapply cells_frameO; [exact SSr| exact MU1|]; intros x Hx; apply OUT1; unfold AIMG_HI; clear -Hx ATR LO BOT; lia).
       assert (TBn : rw_cells asegs m1 (bv_unsigned sp + -2112) [CB (8 * 255) (u64s tb)]).
       { replace (bv_unsigned sp + -2112) with (bv_unsigned sp + -2128 + 16) by (clear; lia).
         eapply cells_frameO; [exact TBr| exact MU1|]. intros x Hx. apply OUT1. unfold AIMG_HI. clear -Hx ATR LO BOT. lia. }
       assert (FRSn : rw_cells asegs m1 (bv_unsigned sp + -72) [C8 sp; CB 8 junk2; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
         by (eapply cells_frameO; [exact FRSr| exact MU1|]; intros x Hx; apply OUT1; unfold AIMG_HI; clear -Hx ATR LO BOT; lia).
       assert (ERRn : rw_cells asegs m1 AERRNO [C4 e0]).
       { eapply cells_frameO; [exact ERRr| exact MU1|]. cbn [cells_size csize Nat.add]. intros x Hx. cbn [outside]. unfold AOOM, AERRNO, ATP in *. clear -Hx. lia. }

       replace (ret_pc (Z_to_bv 64 0x3cc98)) with (Z_to_bv 64 0x3cc98) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
       assert (EspA : spA = Z_to_bv 64 (bv_unsigned sp + -2144)).
       { enough (E : Z_to_bv 64 (bv_unsigned spA) = Z_to_bv 64 (bv_unsigned sp + -2144)) by (rewrite Z_to_bv_bv_unsigned in E; exact E).
         apply Z_to_bv_eqm. rewrite HspA. zeq. }
       rewrite HspA in ST1. replace (bv_unsigned sp - 2144) with (bv_unsigned sp + -2144) in ST1 by (clear; lia). rewrite EspA.
       eapply evtF_mono.
       { eapply (icptN_spec RNG' sp gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s6 s7 s8 s9 s10 s11 _ _ _ _ ra s0 s1 s2 s3 s4 s5 s0i F fc m1 lo junk2 e0);
           first [ exact ST1 | exact MI1 | exact TP | exact ERRn | exact FR16n | exact FRSn | exact RIMGr | exact RSTKr
                 | eexists; split; [exact SSn| reflexivity]
                 | eexists; split; [exact TBn| reflexivity]
                 | clear -BOT ATR; lia
                 | clear -LO; lia ]. }
       cbv beta. intros ms2 P2.
       destruct P2 as (t0e & t1e & t2e & a1e & a2e & a3e & a4e & a5e & a6e & a7e & t3e & t4e & t5e & t6e & m2 & -> & MU2 & WM2 & MI2 & ST2 & ERR2).

       pose proof (munch_app _ _ _ _ _ MU1 MU2) as MUn. pose proof (wmono_trans asegs _ _ _ WM1 WM2) as WMn.
       assert (AXFSr : axflags L st2 mr).
       { intros c' Hc' NC'. destruct (Z.eq_dec c' c) as [->|NE]; [exact AXFr|].
         pose proof (C6F4 c' Hc' NC') as F4. unfold axflag in *.
         assert (EXE : exh_mem c' st2 = exh_mem c' st).
         { destruct STEQ as [[_ ->]|[_ [e2 ->]]]; [apply init_cache_exh|]. rewrite exh_mem_set_emb, (exh_mem_set_other c c' _ NE). apply init_cache_exh. }
         rewrite EXE. eapply cells_frameO; [exact F4| exact MUr|]. cbn [cells_size csize Nat.add]. intros x Hx.
         apply (nf_flag_outside L RESV st SPc c ALO ROK HCK SPHIc Wf c' x PCSf Hc' NE). clear -Hx. lia. }
       destruct (c6_frame L RESV RNG' st2 mr m2 _ ALO ROK AXGr AXFSr MUn) as [C6G2 C6F2].
       { cbn [app]. apply Forall_cons; [unfold c6_piece, AOOM; cbn [fst snd]; intros _; do 8 right; left; clear; lia|].
         apply Forall_cons; [unfold c6_piece; cbn [fst snd]; intros _; left; clear -LO BOT; lia|].
         apply Forall_cons; [unfold c6_piece; cbn [fst snd]; intros _; do 9 right; clear; lia| apply Forall_nil]. }

       assert (AR2 : AREP (AH DI AQ ASEC AFK) L st2 X m2).
       { eapply (AREP_frame_null _ HL L st2 X mr m2 (bv_unsigned sp) ALO ARr); [exact MUn| exact WMn| clear -LO BOT; lia|].
         exists (Z_to_bv 8 1). eapply cells_frameO; [exact OOM1| exact MU2|]. cbn [cells_size csize Nat.add]. intros x Hx. cbn [outside].
         unfold AOOM, AERRNO, ATP in *. clear -Hx ATR LO BOT. repeat split; lia. }
       assert (LIVE2 : a_live st2 = a_live st).
       { pose proof (init_cache_fields st) as (E1 & _). destruct STEQ as [[_ ->]|[_ [e2 ->]]]; [exact E1|]. rewrite <- E1. destruct (init_cache st); reflexivity. }
       pose proof (ablocks_same L st st2 X X LB BL eq_refl LIVE2) as BL2.
       pose proof (munch_app _ _ _ _ _ MU4 (munch_app _ _ _ _ _ MUr MUn)) as MUt.
       assert (PCSt : Forall (nf_piece L RESV st (bv_unsigned sp) c)
                        ([(bv_unsigned sp - 2320, bv_unsigned sp); (al_t L + 3168, al_t L + 3169)] ++ Wf ++ [(AOOM, AOOM + 1)] ++ [(bv_unsigned sp - 2160, bv_unsigned sp - 2144); (AERRNO, AERRNO + 4)])%Z).
       { apply Forall_app. split; [| apply Forall_app; split].
         - apply Forall_cons; [intros _; unfold nf_kind; cbn [fst snd]; left; clear -LO BOT; lia|].
           apply Forall_cons; [intros _; unfold nf_kind; cbn [fst snd]; right; left; clear; lia| apply Forall_nil].
         - eapply Forall_impl; [| exact PCSf]. intros iv K. apply (nf_piece_SP L RESV st SPc (bv_unsigned sp) c iv); [subst SPc; clear; lia| exact K].
         - cbn [app]. apply Forall_cons; [intros _; unfold nf_kind, AOOM; cbn [fst snd]; do 5 right; left; clear; lia|].
           apply Forall_cons; [intros _; unfold nf_kind; cbn [fst snd]; left; clear -LO BOT; lia|].
           apply Forall_cons; [intros _; unfold nf_kind; cbn [fst snd]; do 6 right; clear; lia| apply Forall_nil]. }
       destruct (nf_fake L RESV st (bv_unsigned sp) c _ ALO ROK HCK SPHI (nzl_pieces _ _ _ _ _ _ PCSt)) as (D72 & FU & D48).
       pose proof (hfD _ HLD L LB m m2 _ HFK (munch_nzl _ _ _ MUt) D72 FU D48) as HFK2.
       assert (PRESe : aheap_pres_e CI LB (bv_unsigned sp) m m2).
       { intros a Ha CL NERR.
         pose proof (nf_client_outside L RESV st X (bv_unsigned sp) c ALO ROK HCK SPHI CI CI_OK CI_OK3 WF LB _ a BL PCSt Ha CL NERR) as OUT.
         assert (E : m2 (wa a) = m (wa a)) by (apply MUt; rewrite wa_unsigned by exact Ha; exact OUT).
         split; [exact E|]. intros Hw. rewrite (AFrameD.wview_agree asegs m m2 (wa a) E). exact Hw. }

       unfold amalloc_post_x. cbn [fst snd]. split.
       { unfold c6_at. cbn [ms_mem]. split; [exact C6G2| exact C6F2]. }
       split; [exact FPLE|]. do 14 eexists. exists m2. split; [reflexivity|]. split; [exact MI2|]. split; [exact ST2|]. split; [exact PRESe|].
       split; [| exact ERR2].
       split; [exact ALO|]. split; [exact ARNGr|]. split; [exists X; split; [exact AR2| exact BL2]| exact HFK2]. }

  intros st_pre X_pre RNG1 m_pre cnt k ms1 CRET. destruct CRET as (CRET & EMBp & EXHp & AXFp & AXGp). unfold calloc_retG in CRET.
  destruct CRET as (FPLE & ARp & ARNGp & HCNT & POS & NK & NB & KR & XB & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & MUc & WMc & MIp
                    & t0d & t1d & t2d & a1d & a2d & a3d & a4d & a5d & a6d & a7d & t3d & t4d & t5d & t6d & m1 & stj1 & -> & MU1 & WM1 & MI1 & ST1 & CR1 & STS1).
  rewrite ?unsigned_lit in MUc by (clear -SPR HspA LO BOT STK3; unfold AMALLOC_STACK in *; lia).
  rewrite ?unsigned_lit in MU1 by (clear -SPR HspA LO BOT STK3; unfold AMALLOC_STACK in *; lia).
  rewrite ?unsigned_lit in ST1 by (clear -SPR HspA LO BOT STK3; unfold AMALLOC_STACK in *; lia).
  replace (bv_unsigned spA + -128) with (bv_unsigned sp - 2272) in ST1 by (clear -HspA; lia).
  cbn beta iota. apply implS_ret.
  replace (ret_pc (Z_to_bv 64 0x3cf68)) with (Z_to_bv 64 0x3cf68) by (symmetry; apply ret_pc_even; [lia|reflexivity]).

  pose proof ARp as AR0. destruct AR0 as (WF' & RT' & INST' & THR' & CLS' & HQ' & HS' & HD' & HRO' & RT2' & AVL' & RT3').
  destruct THR' as (T0' & T40' & CACHES' & CSTATS' & [sj' [STATS' LSJ']] & UNW').
  pose proof WF' as WF0. destruct WF0 as (SBE' & PAE' & SAL' & SLO' & SHI' & PERC' & OUTC' & BUSY' & LIVE' & FRESH' & UNIQ').
  destruct (PERC' c HCK) as (B1' & B2' & B3' & B4' & B5' & B6' & B7' & LENF' & LENC' & CNTB' & ND' & RANGE').
  destruct (kit_cache_pop _ L st_pre X_pre m_pre c cnt ARp HCK HCNT POS) as (k' & chunks & NK' & _ & _ & CR & CH & LCH & NTH & JK & FSH).
  assert (EK : k' = k) by (rewrite NK in NK'; injection NK'; intros E; symmetry; exact E). subst k'.

  set (S := size_of_class c) in *.
  set (AB := aslot_addr L c k) in *.
  assert (KSF : 0 <= k * S /\ k * S + S <= c_allocated_user (get_cls st_pre c) /\ (k * S) mod 16 = 0).
  { unfold ndist in KR. fold S in KR. fold S in SZB. fold S in SM16.
    assert (P0 : 0 <= k * S) by (clear -KR SZB; apply Z.mul_nonneg_nonneg; lia).
    assert (Q1 : k + 1 <= c_allocated_user (get_cls st_pre c) / S) by (clear -KR; lia).
    assert (M1 : (k + 1) * S <= c_allocated_user (get_cls st_pre c) / S * S) by (apply Z.mul_le_mono_nonneg_r; clear -Q1 SZB; lia).
    pose proof (Z.mul_div_le (c_allocated_user (get_cls st_pre c)) S ltac:(clear -SZB; lia)) as M2.
    split; [exact P0|]. split.
    - rewrite Z.mul_add_distr_r, Z.mul_1_l in M1. rewrite (Z.mul_comm S) in M2. clear -M1 M2 P0 SZB. lia.
    - destruct (proj1 (Z.mod_divide S 16 ltac:(clear; lia)) SM16) as [q Hq]. rewrite Hq.
      replace (k * (q * 16)) with ((k * q) * 16) by (clear; lia). apply Z_mod_mult. }
  destruct KSF as (KS0 & KS1 & KS2).
  assert (GEO : al_space_beg L <= AB /\ AB + S <= al_space_beg L + K_SPACE_SIZE /\ AB mod 16 = 0
                /\ AB + S <= aregion L c + c_allocated_user (get_cls st_pre c) /\ aregion L c <= AB).
  { subst AB. unfold aslot_addr, aregion, K_REGION, K_SPACE_SIZE, K_FREEARR_OFF, K_ALIGN in *. fold S.
    remember (k * S) as KS eqn:HKS. clear HKS.
    change (2^37) with 137438953472. change (2^32) with 4294967296 in *.
    split; [clear -KS0 C16; lia|]. split; [clear -KS1 B1' B2' C16 NSZ; lia|]. split; [| clear -KS0 KS1 B1'; lia].
    clear -SP3 C16 KS2. Z.div_mod_to_equations; lia. }
  destruct GEO as (G1 & G2 & G3 & G4 & G5). unfold K_SPACE_SIZE in G2. change (2^37) with 137438953472 in G2.
  assert (EAB : AB = aslot_addr L c k) by reflexivity. clearbody AB.
  assert (ES : S = size_of_class c) by reflexivity.

  assert (RZC : rz_size n = 16 \/ 32 <= rz_size n) by (clear -RZR RZM; Z.div_mod_to_equations; lia).
  destruct (slot_carveG m_pre AB S n (rz_size n) JK RZC ltac:(clear -N; lia) ltac:(fold S in NSZ; clear -NSZ NS RSR; lia))
    as (b0 & b1 & szh & szl & ctxj & uj & j1 & j2 & HDR & B1 & UJ & LH & TL).
  set (UB := AB + rz_size n) in *. assert (EUB : UB = AB + rz_size n) by reflexivity. clearbody UB.

  set (grz := shlen (rz_size n)). set (g := shlen (n - n mod 8)). set (room := if n mod 8 =? 0 then 0 else 1).
  assert (GR12 : grz = rz_size n / 8 /\ g = (n - n mod 8) / 8).
  { subst grz g. unfold shlen. rewrite !Z.shiftr_div_pow2 by lia. split; reflexivity. }
  destruct GR12 as [GR1 GR2].
  assert (GR3 : 2 <= grz) by (rewrite GR1; generalize RZR; clear; intros; Z.div_mod_to_equations; lia).
  assert (GR4 : 0 <= g) by (rewrite GR2; generalize N; clear; intros; Z.div_mod_to_equations; lia).
  assert (GR5 : 0 <= room <= 1) by (subst room; clear; destruct (n mod 8 =? 0); lia).
  assert (GR6 : grz + g + room <= shlen S).
  { rewrite GR1, GR2. subst room. unfold shlen. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
    fold S in NSZ. fold S in SM16. generalize NSZ NS RSR RSM SM16 RZM RZR N. clear. intros.
    destruct (Z.eqb_spec (n mod 8) 0) as [M0|M0]; Z.div_mod_to_equations; lia. }
  assert (GR7 : shad UB = shad AB + grz).
  { rewrite GR1, EUB. unfold shad, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
    generalize G3 RZM RZR. clear. intros. Z.div_mod_to_equations. lia. }
  assert (GR89 : 0x2008fff7000 <= shad AB /\ shad AB + shlen S <= 0x10007fef8000).
  { unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
    unfold K_SPACE_SIZE, K_SPACE_EXTRA in *. generalize G1 G2 SP1 SP2. clear. intros. Z.div_mod_to_equations. lia. }
  destruct GR89 as [GR8 GR9].
  destruct (shadow_carve m_pre (shad AB) (shlen S) grz g room FSH GR3 GR4 GR6 GR5) as (SHA & SHpre & [sjunk SHU] & SHP & SHsuf).
  rewrite <- GR7 in SHU, SHP, SHsuf.
  set (PG := shad UB + g) in *.

  pose proof RT' as RT0.
  destruct RT0 as (GPG' & GOT' & GOT80' & RIC' & LS1' & REAL' & IMAX4' & FLG5' & FLG' & HPP' & SHB' & CANP' & TI' & TK' & INI2' & LAY' & MCS' & OOM3'
                    & PGC' & HK2' & CF8' & CF34' & CSMT' & T88' & TSD' & LS2' & CT8' & CT').
  pose proof INI2' as INI'. rw_split INI' 1%nat INI1' INIx. clear INIx.
  destruct OOM3' as [oomb' OOM']. rw_split OOM' 2%nat OOMx RSS'. clear OOMx.
  pose proof IMAX4' as IMAX'. rw_split IMAX' 3%nat IMAX3' IMAXx. clear IMAXx.
  pose proof HK2' as HK'. rw_split HK' 1%nat HK1' HKx. clear HKx.
  pose proof T0' as TT0'. rw_split TT0' 1%nat TTctx' TT'.
  destruct (junk_split m_pre (al_t L + 2768) 16 16 CSTATS' ltac:(lia) ltac:(lia)) as [CSa CSb].
  destruct (junk_split m_pre (al_t L + 2768 + 16) 8 8 CSb ltac:(lia) ltac:(lia)) as [CS8 CSc].
  replace (al_t L + 2768 + 16) with (al_t L + 2784) in CS8 by lia.
  replace (al_t L + 2768 + 16 + 8) with (al_t L + 2792) in CSc by lia.
  destruct INST' as (I32' & I48' & I64' & I72' & I112' & I680' & I984' & I40' & I56').
  pose proof ARNGp as ARNGp0. destruct ARNGp as (RIMG' & RT4' & RCTX' & RNO' & RST' & RRI' & RFK' & RSFK' & RDTLS' & RCLS' & RPA' & RSECS' & RPSH').
  destruct (RCLS' c HCK) as (RREG & RSREG & RFA & RSFA).

  destruct (alayout_slot_disj L AB 65536 ALO G1 ltac:(unfold K_SPACE_SIZE, K_FREEARR_OFF, aregion, K_REGION in *; generalize G4 B1' B2' C16 SP1 SZB; clear; intros; change (2^37) with 137438953472; lia) ltac:(clear; lia))
    as (DJT & DJC & DJN & DJS & DJF).
  assert (RUf : rng RNG1 (UB - 16) (n + 16)) by (eapply rng_sub'; [exact RREG|]; generalize G4 G5 B1' RZR N EUB KS0 NSZ NS RSR; clear; intros; lia).
  assert (RABf : rng RNG1 AB 16) by (eapply rng_sub'; [exact RREG|]; generalize G4 G5 B1' RZR N NSZ NS RSR; clear; intros; lia).
  assert (REG8 : aregion L c mod 8 = 0 /\ c_mapped_user (get_cls st_pre c) mod 8 = 0).
  { unfold aregion, K_REGION, K_USER_MAP, K_ALIGN in *. generalize SP3 B4'; clear; intros. Z.div_mod_to_equations; lia. }
  assert (SHM : shad (aregion L c) <= shad AB /\ shad UB + g + room <= shad (aregion L c) + shlen (c_mapped_user (get_cls st_pre c))).
  { rewrite GR7, GR2, GR1. unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
    fold S in NSZ. fold S in SM16. subst room. generalize G4 G5 B1' N NSZ RSR RSM NS RZR RZM SM16 G3 EUB REG8; clear; intros.
    destruct (Z.eqb_spec (n mod 8) 0); Z.div_mod_to_equations; lia. }
  destruct SHM as [SHM1 SHM2].
  assert (RSAf : rng RNG1 (shad AB) 1) by (eapply rng_sub'; [exact RSREG|]; generalize SHM1 SHM2 GR3 GR4 GR5 GR7; clear; intros; lia).
  assert (RSUf : rng RNG1 (shad UB) (shlen (n - n mod 8))).
  { eapply rng_sub'; [exact RSREG|]. fold g. generalize SHM1 SHM2 GR3 GR4 GR5 GR7. clear. intros. lia. }
  assert (RSPf : n mod 8 <> 0 -> rng RNG1 PG 1).
  { intros NE. eapply rng_sub'; [exact RSREG|]. subst PG.
    assert (R1 : room = 1) by (subst room; generalize NE; clear; intros NE; destruct (Z.eqb_spec (n mod 8) 0); [exfalso; exact (NE ltac:(assumption)) | reflexivity]).
    rewrite R1 in SHM2. generalize SHM1 SHM2 GR3 GR4 GR7; clear; intros. lia. }
  assert (SLS : shlen S <= 8192) by (fold S in NSZ; unfold shlen; rewrite Z.shiftr_div_pow2 by (clear; lia); change (2^3) with 8; clear -NSZ; Z.div_mod_to_equations; lia).
  assert (SB34 : 0 <= shlen (n - n mod 8) <= 8192 /\ PG + 1 <= 0x10007fff8000).
  { subst PG. fold g. rewrite GR7. generalize GR4 GR6 GR9 GR3 GR5 SLS; clear; intros; lia. }
  destruct SB34 as [SB3 SB4].
  assert (RCTX4' : rng RNG1 (al_ctx L) 4096) by (eapply rng_sub'; [exact RCTX'|]; clear; lia).
  assert (DJC4 : al_ctx L + 4096 <= AB \/ AB + 65536 <= al_ctx L) by (generalize DJC; clear; intros; lia).
  assert (CNT16 : 0 < cnt <= 16).
  { unfold max_count in CNTB'. generalize POS HCNT CNTB' MCB; clear. destruct (a_cinit st_pre); intros; lia. }
  assert (PGE : PG = shad UB + shlen (n - n mod 8)) by reflexivity.
  assert (RSTK1 : rng RNG1 lo (bv_unsigned sp - lo)) by (eapply rng_fp_le; [exact FPLE | exact RSTK]).

  set (mu0 := c_mapped_user (get_cls st c)) in *.
  assert (OBJ : aregion_info L c = al_space_beg L + 137438953472 + c * 128 /\ aregion L c = al_space_beg L + c * 4294967296
                /\ shad (al_space_beg L + c * 4294967296) + 536870912 <= 17594333495296).
  { unfold aregion_info, aregion, K_REGION, K_SPACE_SIZE, ARI_STRIDE. change (2^37) with 137438953472. change (2^32) with 4294967296.
    split; [reflexivity|]. split; [reflexivity|]. rewrite shad_div. clear -SP1 SP2 C16. unfold ASHOFF, K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^37) with 137438953472 in *.
    Z.div_mod_to_equations. lia. }
  destruct OBJ as (RIE & RBE & SHHI).
  assert (MU41 : munch [(bv_unsigned sp - 3856, bv_unsigned sp - 2272); (al_t L + 208, al_t L + 3168); (AINSTANCE, AINSTANCE + 728);
                        (al_space_beg L + 137438953472 + c * 128, al_space_beg L + 137438953472 + c * 128 + 128);
                        (al_space_beg L + c * 4294967296 + mu0, al_space_beg L + c * 4294967296 + 4294967296);
                        (shad (al_space_beg L + c * 4294967296 + mu0), shad (al_space_beg L + c * 4294967296) + 536870912)]%Z m4 m1).
  { eapply munch_trans; [eapply munch_weaken; [| exact MUc] | eapply munch_weaken; [| exact MU1]];
      unfold sub_fp; cbn [outside]; intros q Hq; rewrite ?RIE, ?RBE in *; unfold K_REGION, acache_addr in *; change (2^32) with 4294967296 in *;
      rewrite ?shlen_div in *; change (4294967296 / 8) with 536870912 in *; clear -Hq HspA C16; lia. }
  assert (WM41 : wmono asegs m4 m1) by (eapply wmono_trans; [exact WMc | exact WM1]).
  unfold K_SPACE_SIZE, K_SPACE_EXTRA in SP2. change (2^37) with 137438953472 in SP2.
  xport FRa MU41 WM41 ltac:(clear -SPR LO BOT STK3 TL1 TL2 SP1 SP2 C16 SHHI TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold AMALLOC_STACK, AINSTANCE in *; lia).
  xport FR16 MU41 WM41 ltac:(clear -SPR LO BOT STK3 TL1 TL2 SP1 SP2 C16 SHHI TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold AMALLOC_STACK, AINSTANCE in *; lia).
  xport SS MU41 WM41 ltac:(clear -SPR LO BOT STK3 TL1 TL2 SP1 SP2 C16 SHHI TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold AMALLOC_STACK, AINSTANCE in *; lia).
  xport TB MU41 WM41 ltac:(rewrite LTB; clear -SPR LO BOT STK3 TL1 TL2 SP1 SP2 C16 SHHI TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold AMALLOC_STACK, AINSTANCE in *; lia).
  xport FRS MU41 WM41 ltac:(clear -SPR LO BOT STK3 TL1 TL2 SP1 SP2 C16 SHHI TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold AMALLOC_STACK, AINSTANCE in *; lia).

  xport HDR MU1 WM1 ltac:(clear -HspA DJT SPR SP2 G1 G2 EUB RZR N NSZ NS RSR LO BOT STK3 C16; unfold acache_addr, AMALLOC_STACK, K_SPACE_SIZE in *; lia).
  xport UJ MU1 WM1 ltac:(clear -HspA DJT SPR SP2 G1 G2 EUB RZR N NSZ NS RSR LO BOT STK3 C16; unfold acache_addr, AMALLOC_STACK, K_SPACE_SIZE in *; lia).
  xport SHA MU1 WM1 ltac:(cbv delta [g grz room PG] in *; clear -HspA SPR GR1 GR2 GR3 GR4 GR5 GR6 GR7 GR8 GR9 LO BOT STK3 TL1 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport SHU MU1 WM1 ltac:(cbv delta [g grz room PG] in *; clear -HspA SPR GR1 GR2 GR3 GR4 GR5 GR6 GR7 GR8 GR9 SB3 LO BOT STK3 TL1 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  assert (SHP1 : n mod 8 <> 0 -> rw_cells asegs m1 PG [C1 (Z_to_bv 8 250)]).
  { intros NE. specialize (SHP ltac:(subst room; generalize NE; clear; intros NE; destruct (Z.eqb_spec (n mod 8) 0); [exfalso; exact (NE ltac:(assumption)) | reflexivity])).
    xport SHP MU1 WM1 ltac:(cbv delta [g grz room PG] in *; clear -HspA SPR GR1 GR2 GR3 GR4 GR5 GR6 GR7 GR8 GR9 SB3 SB4 LO BOT STK3 TL1 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia). exact SHP. }
  assert (LH1 : 16 < rz_size n -> rw_cells asegs m1 AB [C8 j1; C8 j2]).
  { intros R16. pose proof (proj1 (LH R16)) as LH0.
    xport LH0 MU1 WM1 ltac:(clear -HspA DJT SPR SP2 G1 G2 EUB RZR N NSZ NS RSR LO BOT STK3 C16; unfold acache_addr, AMALLOC_STACK, K_SPACE_SIZE in *; lia). exact LH0. }
  xport GOT' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport GOT80' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport REAL' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport SHB' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport CANP' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport HPP' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport CSMT' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport FLG5' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport FLG' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport HK1' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport LS1' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport LS2' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport LAY' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport MCS' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport CF34' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport INI1' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport RSS' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport IMAX3' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport TI' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport TK' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport T88' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, ATP88, AMALLOC_STACK in *; lia).
  xport TSD' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, ATSD, AMALLOC_STACK in *; lia).
  xport CT' MU1 WM1 ltac:(ub CL5; clear -HspA Y SPR TL1 CL1 CL2 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb CTXi CBND CBNDa CBNDb; unfold acache_addr, AMALLOC_STACK, AIMG_HI in *; lia).
  xport CT8' MU1 WM1 ltac:(ub CL5; clear -HspA Y SPR TL1 CL1 CL2 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb CTXi CBND CBNDa CBNDb; unfold acache_addr, AMALLOC_STACK, AIMG_HI in *; lia).
  xport TTctx' MU1 WM1 ltac:(clear -HspA SPR TL1 TL2 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport UNW' MU1 WM1 ltac:(clear -HspA SPR TL1 TL2 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport STATS' MU1 WM1 ltac:(rewrite LSJ'; clear -HspA SPR TL1 TL2 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, ASTATS_WORDS, AMALLOC_STACK in *; lia).
  assert (DEP1 : ADEPOT DI L m1).
  { eapply (adi_frame DI); [exact HD' | exact MU1 | exact WM1 |]. unfold acache_addr.
    repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq; ub DL7; ub DL8; clear -Hq Y Y0 HspA SPR TL1 TL2 DL1 DL2 DL3 DL4 DL5 DL6 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb NODi NBND NBNDa NBNDb STOi SBND SBNDa SBNDb; unfold AMALLOC_STACK, AIMG_HI in *; lia|]).
    apply Forall_nil. }

  assert (PF : pfactsG (bv_unsigned sp) (al_t L) (al_space_beg L) c mu0 ATOP lo).
  { unfold pfactsG. pose proof (ao_t L ALO) as OT. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in OT.
    unfold AMALLOC_STACK, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN, K_FREEARR_OFF, K_USER_MAP in *. change (2^37) with 137438953472 in *.
    ub TSP. generalize LO BOT SP47 STK2 STK3 OT SP1 SP2 SAL C16 A1 A2 A4 Y. clear. intros.
    repeat match goal with H : _ /\ _ |- _ => destruct H end.
    repeat split; first [reflexivity | assumption | lia | Z.div_mod_to_equations; lia]. }
  assert (MUall : munch [(bv_unsigned sp - 4096, bv_unsigned sp); (al_t L + 208, al_t L + 3169); (AINSTANCE, AINSTANCE + 728);
                         (al_space_beg L + 137438953472 + c * 128, al_space_beg L + 137438953472 + c * 128 + 128);
                         (al_space_beg L + c * 4294967296 + mu0, al_space_beg L + c * 4294967296 + 4294967296);
                         (shad (al_space_beg L + c * 4294967296 + mu0), shad (al_space_beg L + c * 4294967296) + 536870912)]%Z m m_pre).
  { eapply munch_trans; [eapply munch_weaken; [| exact MU4] | eapply munch_weaken; [| exact MUc]];
      unfold sub_fp; cbn [outside]; intros q Hq; rewrite ?RIE, ?RBE in *; unfold K_REGION in *; change (2^32) with 4294967296 in *;
      rewrite ?shlen_div in *; change (4294967296 / 8) with 536870912 in *; clear -Hq HspA; lia. }
  assert (WMall : wmono asegs m m_pre) by (eapply wmono_trans; [exact WM4 | exact WMc]).

  assert (BB : forall b, In b (x_busy X) ->
      al_space_beg L <= xb_alloc L b /\ xb_alloc L b + size_of_class (xb_class b) <= al_space_beg L + 137438953472
      /\ (xb_alloc L b + size_of_class (xb_class b) <= al_space_beg L + c * 4294967296 + mu0 \/ al_space_beg L + c * 4294967296 + 4294967296 <= xb_alloc L b)).
  { intros b Hb. destruct (BUSY b Hb) as [CLB _].
    destruct (PERC (xb_class b) CLB) as (Q1 & Q2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & QR).
    pose proof (size_of_class_facts (xb_class b) CLB) as [QS _].
    assert (KB : 0 <= xb_slot b < ndist st (xb_class b)).
    { apply QR. apply in_app_iff. right. apply in_app_iff. right. unfold busy_slots. apply in_map_iff. exists b. split; [reflexivity|].
      apply filter_In. split; [exact Hb| apply Z.eqb_refl]. }
    pose proof (slot_in_region L st (xb_class b) (xb_slot b) ltac:(clear -QS; lia) (proj1 Q1) KB) as (P5 & P4 & P0).
    unfold xb_alloc. unfold K_NUM_CLASSES in CLB. unfold K_FREEARR_OFF in Q2.
    destruct (Z.eq_dec (xb_class b) c) as [EC|NC].
    - rewrite EC in P5, P4, Q1, Q2 |- *. rewrite RBE in P5, P4. change (c_mapped_user (get_cls st c)) with mu0 in Q1, Q2.
      clear -P5 P4 Q1 Q2 A1 A2 C16. unfold K_FREEARR_OFF in *. lia.
    - pose proof (region_other_geo L c (xb_class b) ALO ltac:(clear -C16; lia) CLB NC) as (R1 & R2 & R3 & _). rewrite RBE in R2.
      clear -P5 P4 Q1 Q2 R1 R2 R3 A1. lia. }
  pose proof (ao_fake L ALO) as FKO. unfold aobj in FKO. pose proof (ao_res L ALO) as ORS. unfold aobj in ORS. pose proof (ao_space L ALO) as RSP.
  pose proof (ad_fake_res L ALO) as D_f_res. pose proof (ad_t_fake L ALO) as D_t_f. pose proof (ad_dtls_res L ALO) as D_d_res. pose proof (ad_t_dtls L ALO) as D_t_d.
  pose proof (ao_dtls L ALO) as ODT. unfold aobj in ODT. unfold adisj in D_f_res, D_t_f, D_d_res, D_t_d.
  assert (FKD : forall cls FA sz, In (mkABlock (ABFake cls) FA sz) LB -> al_fake L <= FA /\ 0 <= sz /\ FA + sz <= al_fake L + 11571200)
    by (intros cls FA sz Hin; exact (proj1 (proj2 BL) cls FA sz Hin)).
  assert (PRES : aheap_pres CI LB (bv_unsigned sp) m m_pre).
  { intros a Ha CL. split; [| intros Hw; apply WMall; exact Hw].
    apply MUall. rewrite wa_unsigned by exact Ha.
    destruct CL as [STa | [CIa | [BLK | SH]]].
    - eapply disjoint_outside; [eapply (Q_stack _ _ _ _ _ _ _ PF a 1); clear -STa; lia | clear; lia].
    - destruct CIa as (iv & Hiv & R). pose proof (proj1 (Forall_forall _ _) CI_OK iv Hiv) as (Q1 & Q2 & Q3).
      pose proof (proj1 (Forall_forall _ _) CI_OK2 iv Hiv) as Q4. cbn [fst snd] in *.
      eapply disjoint_outside; [eapply (Q_img _ _ _ _ _ _ _ PF a 1); unfold AIMG_HI in *; clear -R Q1 Q3 Q4; lia | clear; lia].
    - destruct BLK as (b & Hb & R). destruct b as [[p|cls] A n']; cbn [ab_addr ab_size] in R.
      + destruct (proj1 BL p A n' Hb) as [(xb & Hxb & Sb & Ub & Nb)|(mb0 & ms0 & Lp & EUA & Gs)].
        * destruct (BB xb Hxb) as (Bb1 & Bb2 & Bb3).
          pose proof (awf_fits L st X xb WF Hxb) as FIT. unfold xb_fits in FIT. rewrite Sb in FIT. unfold xb_user in Ub. subst A n'.
          eapply disjoint_outside; [eapply (Q_slot _ _ _ _ _ _ _ PF a 1) | clear; lia]; clear -R Bb1 Bb2 Bb3 FIT; lia.
        *
          cbn [sec_wf1] in Gs. destruct Gs as (Gs1 & Gs2 & Gs3 & Gs4 & Gs5 & Gs6 & (Ct & Cc & Cr & Cp & Cn & Cs & Cf & Cd)).
          pose proof (sec_facts n' ltac:(clear -Gs5; lia) Gs6) as SF. subst A. unfold SEC_UOFF, K_HIGH_MEM in *.
          unfold ablk, KLS, AIMG_HI in Gs2.
          eapply disjoint_outside; [eapply (Q_obj _ _ _ _ _ _ _ PF a 1) | clear; lia]; clear -R Gs2 Gs3 Gs4 Gs5 SF Ct Cr RSP ORS; lia.
      + destruct (FKD cls A n' Hb) as (K1 & K2 & K3). atop_facts.
        eapply disjoint_outside; [eapply (Q_obj _ _ _ _ _ _ _ PF a 1) | clear; lia];
          clear -R K1 K3 FKO D_t_f D_f_res RSP OFKi OFKs OFKsa OFKsb; lia.
    - destruct SH as (a' & Ha' & ->).
      destruct Ha' as [STa | [CIa | FK]].
      + eapply disjoint_outside; [eapply (Q_shad_hi _ _ _ _ _ _ _ PF a'); unfold AMALLOC_STACK in *; clear -STa LO BOT STK3; lia | clear; lia].
      + destruct CIa as (iv & Hiv & R). pose proof (proj1 (Forall_forall _ _) CI_OK iv Hiv) as (Q1 & Q2 & Q3). cbn [fst snd] in *.
        eapply disjoint_outside; [eapply (Q_shad_img _ _ _ _ _ _ _ PF a'); unfold AIMG_HI in *; clear -R Q1 Q3; lia | clear; lia].
      + destruct FK as (cls & FA & sz & Hin & R). destruct (FKD cls FA sz Hin) as (K1 & K2 & K3). atop_facts.
        eapply disjoint_outside; [eapply (Q_shad_obj _ _ _ _ _ _ _ PF a') | clear; lia]; clear -R K1 K3 FKO D_f_res RSP OFKi OFKs OFKsa OFKsb; lia. }
  assert (HFKp : AFK L LB m_pre).
  { eapply (hf_frame _ HL L LB m m_pre); [exact HFK | exact MUall | exact WMall | exact (Q_tfs _ _ _ _ _ _ _ PF) |].
    unfold fake_untouched. pose proof (ao_t L ALO) as OT. unfold aobj in OT.
    assert (SHF : 2148261376 <= shad (al_fake L) /\ shad (al_fake L) + shlen 11571200 <= 17594332446720
                  /\ (shad (al_space_beg L + c * 4294967296) + 536870912 <= shad (al_fake L)
                      \/ shad (al_fake L) + shlen 11571200 <= shad (al_space_beg L + c * 4294967296 + mu0))
                  /\ shad (al_space_beg L + c * 4294967296) <= shad (al_space_beg L + c * 4294967296 + mu0)
                  /\ 2201439137792 <= shad (al_space_beg L + c * 4294967296)).
    { rewrite !shad_div, !shlen_div. unfold ASHOFF in *. destruct PF as (_ & _ & (F1 & F2 & F3 & F4 & F5 & F6) & _).
      clear -FKO F1 F2 F3 F4 F5 F6 D_f_res RSP OFKi OFKs OFKsa OFKsb. Z.div_mod_to_equations. dlia. }
    destruct SHF as (SF1 & SF2 & SF3 & SF4 & SF5).
    unfold AMALLOC_STACK, AINSTANCE in *. destruct PF as (PF1 & PF2 & PF3 & PF4).
    repeat (apply Forall_cons; [cbn [fst snd];
      clear -LO BOT STK3 SP47 STK2 OT FKO ORS RSP ODT D_f_res D_t_f D_d_res D_t_d C16 PF3 PF4 SF1 SF2 SF3 SF4 SF5 SHHI TL1 TBND TBNDa TBNDb TIMG TIMGa TIMGb OFKi OFKs OFKsa OFKsb DBND DBNDa DBNDb DIMG DIMGa DIMGb;
      repeat (split; [lia|]); lia |]).
    apply Forall_nil. }

  eapply evtF_mono.
  { eapply (malloc_tail_gen DI L RNG1 ra sp gp tp spA t0d t1d t2d a1d a2d a3d a4d a5d a6d a7d t3d t4d t5d t6d
              s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0A s1A s2A s3A s4A s5A s0i F fc m1
              n (al_t L) c cnt AB UB PG room lo b0 b1 szh szl ctxj (1 + Z.of_nat (length trc))
              (Z_to_bv 64 (max_count st_pre c)) (Z_to_bv 64 S) stj1 j1 j2 (Z_to_bv 8 250) sj' sjunk uj fr0 junk2 tb trc).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => exact ST1
         | |- mem_inv _ _ => exact MI1
         | |- allocA_cells _ _ _ => unfold allocA_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end)
         | |- poison_cells _ => unfold poison_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end)
         | |- ADEPOT _ _ _ => exact DEP1
         | |- In _ _ => exact TRU
         | |- u64arr _ _ (_ + 2800) _ => exact STATS'
         | |- u64arr _ _ _ _ => exact TB
         | |- map _ _ = _ => exact TRF
         | |- (16 < _) -> _ => exact LH1
         | |- ~ _ -> rng _ _ _ => exact RSPf
         | |- ~ _ -> _ => exact SHP1
         | |- is_primary _ = _ => exact PRIM
         end.
    all: try lazymatch goal with
         | |- rw_cells _ _ (_ + -16) _ => exact HDR
         | |- rw_cells _ _ (shad _) [C1 _] => exact SHA
         | |- rw_cells _ _ (shad _) [CB _ _] => exact SHU
         | |- rw_cells _ _ _ [CB _ _] => exact UJ
         | |- rw_cells _ _ (_ + 2784) _ => exact STS1
         | |- rw_cells _ _ (_ + 208 + _ * 80) _ => exact CR1
         | |- rw_cells _ _ _ _ => assumption
         | |- rng _ _ _ => assumption
         | |- _ \/ _ => first [exact DJT | exact DJN | exact DJS | exact DJC4 | unboxed CL5 | unboxed DL7 | unboxed DL8 | unboxed DL9 | unboxed DL10]
         | |- @eq Z _ _ => first [assumption | reflexivity | exact PGE | subst room; reflexivity]
         | |- @eq word _ _ => first [assumption | reflexivity]
         | |- @eq nat _ _ => first [exact LSJ' | exact LTB | assumption]
         end.
    all: try assumption.
    all: try (generalize N NR LO BOT SP47 STK1 STK2 STK3 SP1 SP2 SP4 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6
                         G1 G2 G3 G4 G5 EUB ES SM16 NSZ NS RSR RZR GR3 GR7 GR8 GR9 SB3 SB4 B1 POS HCNT CNT16 KS0 KS1 HC0 C16 LTRC RA4 HspA;
              clear; intros; rewrite ?HC0 in *; unfold AIMG_HI, AMALLOC_STACK, AREQMAX, UDEPTH, K_SPACE_SIZE, K_SPACE_EXTRA in *; lia).
    all: try (eapply rng_sub'; [exact RSTK1|]; clear -LO SP47 BOT STK3 SPR; unfold AMALLOC_STACK in *; lia).
    all: try (clear -LTRC; lia).
    all: match goal with |- ?G => idtac "REMT" G end. }

  cbv beta. intros ms' PM.
  unfold amalloc_post_x. cbn [snd fst]. split.
  {
    pose proof PM as PM0. unfold malloc_post_gen in PM0.
    destruct PM0 as (id0 & t0e & t1e & t2e & a1e & a2e & a3e & a4e & a5e & a6e & a7e & t3e & t4e & t5e & t6e & m5 & sj5 & stj5 & EMS & MUt & _).

    assert (AXFall : axflags L st_pre m_pre).
    { intros c' Hc' NC'. destruct (Z.eq_dec c' c) as [->|NE]; [exact (AXFp NC')|].
      pose proof (C6F4 c' Hc' NC') as F4. unfold axflag in *.
      replace (exh_mem c' st_pre) with (exh_mem c' st)
        by (destruct EXHp as [E|E]; [symmetry; apply exh_mem_eq_list; exact E| rewrite (exh_mem_eq_list c' _ _ E); symmetry; apply exh_mem_clear_other; exact NE]).
      eapply cells_frameO; [exact F4| exact MUc|]. cbn [cells_size csize Nat.add]. intros x Hx. cbn [outside].
      assert (RIEj : forall j, aregion_info L j = al_space_beg L + 137438953472 + j * 128) by (intros j; unfold aregion_info, K_SPACE_SIZE, ARI_STRIDE; change (2^37) with 137438953472; reflexivity).
      rewrite (RIEj c') in Hx. rewrite (RIEj c). unfold aregion, K_REGION, AINSTANCE, K_NUM_CLASSES in *. change (2^32) with 4294967296.
      pose proof atop_range as ATRx.
      assert (SHT : shad (al_space_beg L + c * 4294967296) + shlen 4294967296 <= 17594333495296)
        by (rewrite shad_div, shlen_div; unfold ASHOFF, K_SPACE_SIZE, K_SPACE_EXTRA in *; change (2^37) with 137438953472 in *; clear -SP1 SP2 C16 ATRx; Z.div_mod_to_equations; lia).
      rewrite ?unsigned_lit by (clear -SPR HspA LO BOT STK3; lia).
      pose proof TSP as TSPx. unbox TSPx.
      unfold K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^37) with 137438953472 in *.
      clear -Hx Hc' NE C16 SP1 SP2 TL1 TL2 TL4 LO BOT STK3 HspA SHT A1 A2 ATRx SPR TSPx. unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in *. repeat split; lia. }
    destruct (c6_frame L RESV RNG1 st_pre m_pre m1 _ ALO ROK AXGp AXFall MU1) as [G1x F1x].
    { rewrite ?unsigned_lit by (clear -SPR HspA LO BOT STK3; lia).
      apply Forall_cons; [unfold c6_piece; cbn [fst snd]; intros _; left; clear -LO BOT STK3 HspA; lia|].
      apply Forall_cons; [unfold c6_piece, acache_addr; cbn [fst snd]; intros _; right; left; clear -C16; lia|].
      apply Forall_cons; [unfold c6_piece; cbn [fst snd]; intros _; right; left; clear; lia| apply Forall_nil]. }
    destruct (c6_frame L RESV RNG1 st_pre m1 m5 _ ALO ROK G1x F1x MUt) as [G5x F5x].
    { pose proof (ao_res L ALO) as (_ & _ & ORSx & _). pose proof (ao_space L ALO) as RSPx. pose proof atop_range as ATRx.
      assert (UBN : UB + n <= AB + S) by (clear -EUB NS NSZ RSR ES; lia).
      repeat (apply Forall_cons; [unfold c6_piece; cbn [fst snd]; intros NEk;
        first [ left; clear -LO BOT; lia
              | right; left; clear -C16; lia
              | do 2 right; left; clear -G1 G2 EUB UBN RSPx RZR SZB ES; subst S; lia
              | do 3 right; left; clear -NEk GR3 GR4 GR5 GR6 GR7 GR8 GR9 PGE SB3; subst g grz; lia
              | do 5 right; left; clear; lia
              | do 6 right; left; clear; lia
              | do 7 right; left; clear; lia ]|]).
      apply Forall_nil. }
    rewrite EMS. unfold c6_at. cbn [ms_mem MS].
    destruct G5x as (XC5 & EC5 & ER5 & ECL5).
    split.
    - split; [exact XC5|]. split; [exact EC5|]. split; [exact ER5|].
      eapply (emb_clr_sub RESV st_pre); [reflexivity| | exact ECL5].
      apply (achunks_new_prim st_pre _ (a_next (apop c st_pre)) c n); reflexivity.
    - intros c' Hc' NC'. exact (F5x c' Hc' NC'). }
  unfold apop. rewrite HCNT, !a_next_put_cls, !a_live_put_cls.
  apply (malloc_post_gen_shift DI L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc n (al_t L) c cnt AB UB PG room lo b1 _ _ uj m_pre m1 ms') in PM;
    [| eapply munch_weaken; [| exact MU1]; unfold sub_fp, acache_addr; cbn [outside]; intros q Hq; clear -Hq HspA; lia | exact WM1].
  cbv delta [PG g grz room] in PM, SHpre, SHsuf. subst UB. subst AB.
  eapply (amalloc_post_shiftG CI _ L RNG RNG1 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st st_pre LB n lo m m_pre); [| exact FPLE |].
  { eapply (store_prim DI AQ ASEC AFK HL CI CI_OK L RNG1 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m_pre st_pre LB X_pre n lo c cnt k b1
              (Z_to_bv 64 (max_count st_pre c)) (Z_to_bv 64 (size_of_class c)) uj).
    all: try exact PM.
    all: try lazymatch goal with
         | |- is_primary _ = _ => exact PRIM
         | |- ann_ov _ = None => rewrite L2; exact OVF
         | |- alayout_ok _ => exact ALO
         | |- arng _ _ _ => exact ARNGp0
         | |- AFK _ _ _ => idtac
         | |- AREP _ _ _ _ _ => exact ARp
         | |- ablocks _ _ _ _ => eapply ablocks_xbusyG; [exact BL | exact XB | exact L1]
         | |- nth_error _ _ = _ => exact NK
         | |- busy_of _ _ _ = _ => exact NB
         | |- (16 < _) -> _ => let R16 := fresh in intros R16; exact (proj2 (LH R16))
         | |- junk_at _ (_ + 2768) _ => exact CSa
         | |- junk_at _ (_ + 2792) _ => exact CSc
         | |- junk_at _ _ _ => first [exact TL | rewrite ES; exact TL]
         | |- fill_at _ (_ + 1) _ _ => exact SHpre
         | |- fill_at _ _ _ _ => first [exact SHsuf | rewrite ES; exact SHsuf]
         end.
    all: try assumption.
    all: try reflexivity.
    all: try (generalize N KR B1 LO BOT STK3 POS; clear; intros; unfold AMALLOC_STACK in *; lia).
    all: try exact HFKp.
    all: match goal with |- ?G => idtac "REMS" G end. }
  exact PRES.
Qed.
End S.
End CANSEC1.
End AMallocPG_x.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_aaligned_iseg F_aaligned_pre.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_aaligned_null.
Module AAlignedPG_x.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Exec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Tac. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ITreeA. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.SysStepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABytes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ASecFacts. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AMalloc_iface. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ADepot_iface. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARep. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ALayout. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AHeapP. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepKit. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepFrame. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepExt. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepExt2. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit2. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AModelFacts. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.APrimFacts.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apoison.F_apoison.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc1.F_aalloc1.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc2.F_aalloc2. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_amalloc_icpt.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_amalloc_pre.F_amalloc_pre.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc2.F_aalloc2g.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc3.F_aalloc3g.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aaligned_tail.F_amalloc_tailg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_amalloc_arep.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepStore.ARepStore.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepStore.ARepStoreG. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARefill_iface.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARefillP.ARefillP.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ACallocG.ACallocG.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc1.F_aalloc1_16.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc2.F_aalloc2g_16.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc3.F_aalloc3g_16. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aaligned_iseg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aaligned_pre.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aaligned_tail.F_aaligned_tail.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepStore.ARepStoreG_16.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

 Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AAlignedPG.AMallocPG. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AEmbRep. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFrameD. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AEmbFrame.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_arefill.F_arefill_x. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARefill_iface_x. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARefillP_x.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARefillP.ARefillP_e. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_acache_x.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ACallocG.ACallocG_x. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_amalloc_null. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ANullKit. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AC6Frame. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ANullPres.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AAlignedPG.AAlignedPG. Import AMallocPG_x. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aaligned_null.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC1. Context {rc : runConstT} {ov : annOV}.

Local Lemma ablk_int : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6483968 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
Local Lemma aobj_int : forall a n, aobj a n -> 0x10000 <= n ->
  6483968 <= a /\ a + n <= ATOP /\ exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof.
  intros a n H Hn. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. destruct H as (H1 & H2 & H3 & H4 & H5).
  split; [lia|]. split; [lia|]. destruct H4; [exists 0 | exists 1]; lia.
Qed.
Local Lemma aobj4_int : forall a, aobj a 4096 ->
  4096 <= a /\ a + 4096 <= ATOP
  /\ (exists k, 0 <= k <= 1 /\ a + 4096 <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a)
  /\ (exists j, 0 <= j <= 1 /\ a + 4096 <= 65536 + j * 18446744073709551616 /\ 6483968 * j <= a).
Proof.
  intros a H. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. destruct H as (H1 & H2 & H3 & H4 & H5).
  split; [lia|]. split; [lia|]. split; [destruct H4; [exists 0 | exists 1]; lia | destruct H5 as [_ [H5|H5]]; [exists 0 | exists 1]; lia].
Qed.

Local Ltac dlia := repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
Section S.
Variable DI : ADepotIface.
Variables (AQ ASEC : alayout -> astate -> aconc -> amem -> Prop) (AFK : alayout -> list ablock -> amem -> Prop).
Hypothesis HL : ahole_laws (AH DI AQ ASEC AFK).
Hypothesis HLD : ahole_lawsD (AH DI AQ ASEC AFK).
Hypothesis EXHW : exh_first_stmt.
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI) CI.

Hypothesis CI_OK2 : Forall (fun iv => snd iv <= AINSTANCE \/ AINSTANCE + 728 <= fst iv) CI.

Hypothesis CI_OK3 : Forall (fun iv => (snd iv <= AEMB \/ AEMB + 56 <= fst iv) /\ (snd iv <= 0x15bd20 \/ 0x15bd21 <= fst iv)) CI.

Theorem aaligned_prim16_x : forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (n lo : Z) (tr : list Z) (RESV : list (Z * Z)),
  ann_ov (a_next st) = None ->

  is_primary16 n = true -> n mod 16 = 0 ->

  AHEAP_P (AH DI AQ ASEC AFK) L RNG st LB m ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - 4608 ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 16 -> a1 = Z_to_bv 64 n -> 1 <= n <= AREQMAX ->
  aunw m L RNG lo AALIGNED_PC sp s0 ra tr ->
  bv_unsigned s0 <> bv_unsigned sp + 8 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AALIGNED_PC ->
  bv_unsigned sp mod 16 = 0 ->
  rng RNG lo (bv_unsigned sp - lo) ->
  aresv_ok L RESV ->

  bv_unsigned fc < 32 -> axg RESV RNG st m -> axflags L st m -> (let '(_, cap0, _) := a_emb st in cap0 <= 2 ^ 23) ->
  (exists e0 : word, rw_cells asegs m AERRNO [C4 e0]) ->
  implS asegs RNG (aembed ATOP (aaligned16x ATOP RESV st n))
        (epostF (amalloc_post_x CI (AHEAP_P (AH DI AQ ASEC AFK)) L RESV RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB n lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AALIGNED_SYM) fc None m (seg_rom asegs)).
Proof.
  intros until RESV. intros OVF PRIM N16 AHP MI ST BOT LO TP Ha0 Ha1 NR AUNW S0NE RA4 RANE SP16 RSTK ROK FC C6G C6F CAPB ERRC.
  assert (N : 1 <= n <= AREQMAX) by exact NR. assert (N1 : 1 <= n) by (clear -NR; lia).

  assert (EXARM : exists trc,
      ((bv_unsigned sp + 16 < al_top L /\ uchain m (al_top L) AALIGNED_PC (bv_unsigned sp) (bv_unsigned s0) 28%nat tr /\ (length tr <= 28)%nat /\ trc = bv_unsigned ra :: tr
        /\ rng RNG lo (al_top L - lo))
       \/ (al_top L <= bv_unsigned sp + 16 /\ bv_unsigned sp < 2^47 /\ trc = []))
      /\ In (AALIGNED_PC :: trc) (al_U L) /\ (length trc <= 29)%nat /\ bv_unsigned sp < 2^47).
  { pose proof (alayout_stack L (proj1 AHP)) as (K1 & K2 & K3).
    destruct AUNW as [(T1 & U1 & L1 & I1 & R1)|(T1 & T2 & I1)].
    - exists (bv_unsigned ra :: tr). split; [left; split; [exact T1|]; split; [exact U1|]; split; [exact L1|]; split; [reflexivity| exact R1]|].
      split; [exact I1|]. split; [cbn [length]; clear -L1; lia | clear -T1 K2; lia].
    - exists (@nil Z). split; [right; split; [exact T1|]; split; [exact T2| reflexivity]|]. split; [exact I1|]. split; [cbn [length]; clear; lia | exact T2]. }
  destruct EXARM as (trc & ARM & TRU & LTRC & SP47).
  destruct AHP as (ALO & ARNG & [X [AR BL]] & HFK).
  remember (class_id (needed16 n)) as c eqn:HC0. symmetry in HC0.
  pose proof (prim16_facts' n N1 PRIM) as (NS & RZR & RZE & RZM & RLR & RSR & RSM & NSR).
  pose proof (prim_class_facts16 n c N1 PRIM HC0) as (C16 & NSZ & SM16 & SMALL & MCB). clear SMALL.
  pose proof (cls_facts c C16) as (SZB & _ & _ & _).
  assert (HCK : 1 <= c < K_NUM_CLASSES) by (unfold K_NUM_CLASSES; clear -C16; lia).
  assert (NM8 : needed16 n mod 8 = 0) by (rewrite NS; clear -RSM RZM; Z.div_mod_to_equations; lia).

  pose proof AR as AR0. destruct AR0 as (WF & RT & INST & THR & CLS & HQ & HS & HD & HRO & RT2 & AVL & RT3).
  destruct THR as (T0 & T40 & CACHES & CSTATS & [sj [STATS LSJ]] & UNW).
  pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVE & FRESH & UNIQ).
  destruct (PERC c HCK) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & LENF & LENC & CNTB & ND & RANGE).
  pose proof (alayout_space L ALO) as (SP1 & SP2 & SP3 & SP4).
  pose proof (alayout_t L ALO) as (TL1 & TL2 & TL3 & TL4).
  pose proof (alayout_ctx L ALO) as (CL1 & CL2 & CL3 & CL4 & CL5).
  pose proof (alayout_depot L ALO) as (DL1 & DL2 & DL3 & DL4 & DL5 & DL6 & DL7 & DL8 & DL9 & DL10).
  pose proof (aobj4_int _ (ao_t L ALO)) as (_ & _ & (kT & TBND & TBNDa & TBNDb) & (jT & TIMG & TIMGa & TIMGb)).
  pose proof (aobj_int _ _ (ao_ctx L ALO) ltac:(clear; lia)) as (CTXi & _ & (kC & CBND & CBNDa & CBNDb)).
  pose proof (aobj_int _ _ (ao_nodes L ALO) ltac:(clear; lia)) as (NODi & _ & (kN & NBND & NBNDa & NBNDb)).
  pose proof (aobj_int _ _ (ao_store L ALO) ltac:(clear; lia)) as (STOi & _ & (kR & SBND & SBNDa & SBNDb)).
  pose proof (aobj_int _ _ (ao_fake L ALO) ltac:(clear; lia)) as (OFKi & _ & (kF & OFKs & OFKsa & OFKsb)).
  pose proof (aobj4_int _ (ao_dtls L ALO)) as (_ & _ & (kD & DBND & DBNDa & DBNDb) & (jD & DIMG & DIMGa & DIMGb)).
  pose proof (alayout_stack L ALO) as (STK1 & STK2 & STK3).
  pose proof (alayout_res_disj L ALO) as [SCX TSP].
  pose proof RT as RT0.
  destruct RT0 as (GPG & GOT & GOT80 & RIC & LS1 & REAL & IMAX4 & FLG5 & FLG & HPP & SHB & CANP & TI & TK & INI2 & LAY & MCS & OOM3
                    & PGC & HK2 & CF8 & CF34 & CSMT & T88 & TSD & LS2 & CT8 & CT).
  pose proof INI2 as INI. rw_split INI 1%nat INI1 INIx. clear INIx.
  destruct OOM3 as [oomb OOM]. rw_split OOM 2%nat OOMx RSS. clear OOMx.
  pose proof IMAX4 as IMAX. rw_split IMAX 3%nat IMAX3 IMAXx. clear IMAXx.
  pose proof T0 as TT0. rw_split TT0 1%nat TTctx TT.
  pose proof ARNG as ARNG0. destruct ARNG as (RIMG & RT4 & RCTX & RNO & RSTO & RRI & RFK & RSFK & RDTLS & RCLS).
  assert (RCTX4 : rng RNG (al_ctx L) 4096) by (eapply rng_sub'; [exact RCTX|]; clear; lia).
  word_range sp SPR.
  box CL5. box DL7. box DL8. box DL9. box DL10. box TSP. box SCX.

  rewrite (aaligned16x_eq RESV st n c HC0).

  iprefix. eapply evtF_cut.
  { eapply (aligned_pre_spec16 L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n (al_t L) lo (al_top L) (al_bot L) tr trc).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => exact ST
         | |- mem_inv _ _ => exact MI
         | |- allocA_cells _ _ _ => unfold allocA_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end)
         | |- poison_cells _ => unfold poison_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end)
         | |- u64arr _ _ _ _ => exact STATS
         | |- (_ /\ _) \/ (_ /\ _) => exact ARM
         | |- _ \/ _ => unboxed CL5
         | |- @eq word _ _ => first [exact TP | exact Ha0 | exact Ha1]
         | |- is_primary16 _ = _ => exact PRIM
         end.
    all: try lazymatch goal with
         | |- rw_cells _ _ _ _ => assumption
         | |- rng _ _ _ => assumption
         end.
    all: try assumption.
    all: try (generalize N NR LO BOT SP47 STK1 STK2 STK3 SP1 SP2 SP4 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 LTRC RA4 SP16;
              clear; intros; unfold AIMG_HI, AMALLOC_STACK, AREQMAX, UDEPTH in *; lia).
    all: match goal with |- ?G => idtac "REMPRE" G end. }
  cbv beta. intros ms4 P4. unfold aligned_pre_post16 in P4.
  destruct P4 as (spA & t0c & t1c & t2c & a4c & a5c & a6c & a7c & t3c & t4c & t5c & t6c & s0A & s1A & s2A & s3A & s4A & s5A & s6A & fr0 & junk0 & junk2 & tb & m4
                  & -> & HspA & MU4 & WM4 & MI4 & ST4 & FRa & FR16 & FRP0 & SS & TB & LTB & TRF & FRS & UW4).
  apply evtF_done.
  assert (AR4 : AREP (AH DI AQ ASEC AFK) L st X m4).
  { eapply (AREP_frame_pre _ HL L st X m m4); [exact ALO | exact AR | exact MU4 | exact WM4 | | exact UW4].
    apply Forall_cons; [unfold apre; cbn [fst snd]; intros _; left; unfold AMALLOC_STACK in *; clear -LO BOT STK3; lia|].
    apply Forall_cons; [unfold apre; cbn [fst snd]; intros _; right; split; reflexivity| apply Forall_nil]. }

  destruct (c6_frame L RESV RNG st m m4 _ ALO ROK C6G C6F MU4) as [C6G4 C6F4].
  { apply Forall_cons; [unfold c6_piece; cbn [fst snd]; intros _; left; unfold AMALLOC_STACK in *; clear -LO BOT STK3; lia|].
    apply Forall_cons; [unfold c6_piece; cbn [fst snd]; intros _; right; left; clear; lia| apply Forall_nil]. }

  eapply (@calloc_arep_gen_x _ _ _ HL HLD _ RESV _ _ L RNG _ _ gp tp t0c t1c t2c _ _ _ _ _ _ a4c a5c a6c a7c _ _ _ _ _ _ _ _ _ _ t3c t4c t5c t6c F fc m4 st X c lo (needed16 n)
            ALO ARNG0 AR4 MI4).
  all: try lazymatch goal with
       | |- arng _ _ _ => exact ARNG0
       | |- stk _ _ _ _ => rewrite unsigned_lit by (clear -SPR HspA LO BOT STK3; unfold AMALLOC_STACK in *; lia);
                           replace (bv_unsigned spA + -128) with (bv_unsigned sp - 2304) by (clear -HspA; lia); exact ST4
       | |- ATOP <= _ => clear -LO BOT STK3; unfold AMALLOC_STACK in *; lia
       | |- _ <= bv_unsigned _ - _ => rewrite unsigned_lit by (clear -SPR HspA LO BOT STK3; unfold AMALLOC_STACK in *; lia);
                                    clear -LO HspA BOT STK3; unfold AMALLOC_STACK in *; lia
       | |- @eq word _ _ => first [exact TP | reflexivity]
       | |- 16 <= _ <= 65536 => clear -NSR; lia
       | |- _ mod 8 = 0 => exact NM8
       | |- class_id _ = _ => exact HC0
       | |- rng _ _ _ => rewrite unsigned_lit by (clear -SPR HspA LO BOT STK3; unfold AMALLOC_STACK in *; lia);
                         eapply rng_sub'; [exact RSTK|]; clear -LO HspA SP47 BOT STK3; unfold AMALLOC_STACK in *; lia
       | |- exh_first_stmt => exact EXHW
       | |- aresv_ok _ _ => exact ROK
       | |- bv_unsigned _ < 2 ^ 63 => rewrite unsigned_lit by (clear -SPR HspA LO BOT STK3; unfold AMALLOC_STACK in *; lia); clear -SP47 HspA; lia
       | |- bv_unsigned _ < 32 => exact FC
       | |- _ -> axflag _ _ _ _ => intros NC24x; exact (C6F4 c HCK NC24x)
       | |- axg _ _ _ _ => exact C6G4
       | |- context [a_emb _] => exact CAPB
       | |- forall _, _ => idtac
       end.
  1: {
       intros st2 RNG' ms' RF. unfold aret_xf in RF. cbv zeta in RF. pose proof atop_range as ATR.
       pose proof C6G4 as (_ & ECp & _ & ECLp). unfold emb_cells in ECp. unfold emb_clr in ECLp.
       destruct (a_emb st) as [[d0 cap0] sz0] eqn:EA. destruct (a_emb st2) as [[d2 cap2] sz2] eqn:EA2.
       destruct RF as (FPLE & t0r & t1r & t2r & a1r & a2r & a3r & a4r & a5r & a6r & a7r & t3r & t4r & t5r & t6r & mr
                       & -> & MIr & STr & STEQ & ARr & ARNGr & AXFr & AXGr & (d1 & cap1 & MUr & PV1 & PV2 & TOP1)).
       assert (USP : bv_unsigned (Z_to_bv 64 (bv_unsigned spA + -128)) = bv_unsigned sp - 2304)
         by (rewrite unsigned_lit by (clear -SPR HspA LO BOT ATR; lia); clear -HspA; lia).
       rewrite USP in MUr, STr.

       assert (B0 : bufok RESV st d0 cap0).
       { unfold bufok. destruct (Z.eqb_spec cap0 0) as [E0|NZ]; [left; lia|]. right.
         destruct ECp as (_ & _ & _ & _ & _ & _ & _ & _ & TOP & _). split; [exact TOP|]. destruct ECLp as [Q|Q]; [exfalso; exact (NZ Q)| exact Q]. }
       assert (B1 : bufok RESV st d1 cap1).
       { destruct (Z_le_gt_dec cap1 0) as [LE|GT]; [left; exact LE|]. destruct PV1 as [[E1 E2]|AV]; [rewrite E1, E2; exact B0|].
         right. split; [destruct TOP1 as [Q|Q]; [lia| exact Q]| exact AV]. }
       assert (B2 : bufok RESV st d2 cap2).
       { destruct PV2 as [[E1 E2]|AV]; [rewrite E1, E2; exact B0|].
         pose proof AXGr as (_ & EC2 & _). unfold emb_cells in EC2. rewrite EA2 in EC2. destruct (Z.eqb_spec cap2 0) as [E0|NZ]; [left; lia|]. right.
         destruct EC2 as (_ & _ & _ & _ & _ & _ & _ & _ & TOP & _). split; [exact TOP| exact AV]. }

       set (SPc := bv_unsigned sp - 2304) in *.
       assert (SPHIc : ATOP <= SPc) by (subst SPc; clear -LO BOT; lia).
       assert (SPHI : ATOP <= bv_unsigned sp) by (clear -LO BOT; lia).
       set (Wf := [(SPc - 2096, SPc); (al_t L + 208, al_t L + 2768); (aregion_info L c, aregion_info L c + 8);
                   (aregion_info L c + 68, aregion_info L c + 69); (AEMB, AEMB + 56); (d0, d0 + cap0); (d1, d1 + cap1); (d2, d2 + cap2)]%Z).
       change (munch Wf m4 mr) in MUr.
       assert (PCSf : Forall (nf_piece L RESV st SPc c) Wf).
       { assert (BK : forall d cap, bufok RESV st d cap -> nf_piece L RESV st SPc c (d, d + cap)).
         { intros d cap [B|[Bt Ba]] LT; cbn [fst snd] in LT; [lia|]. unfold nf_kind. cbn [fst snd]. do 4 right. left.
           replace (d + cap - d) with cap by lia. split; assumption. }
         subst Wf. repeat (apply Forall_cons); try apply Forall_nil; try (apply BK; assumption); intros _; unfold nf_kind; cbn [fst snd].
         - left. subst SPc. clear -LO BOT. lia.
         - right; left. clear. lia.
         - right; right; left. clear. lia.
         - right; right; left. clear. lia.
         - right; right; right; left. clear. lia. }
       assert (OUTS : forall x, SPc <= x -> outside Wf x)
         by (intros x Hx; apply (nf_outside L RESV st SPc c ALO ROK HCK SPHIc Wf x PCSf); left; exact Hx).

       apply rw_cells_of_u64arr in TB. rewrite LTB in TB.
       assert (FRar : rw_cells asegs mr (bv_unsigned spA + -128)
                        [CB 8 fr0; C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 32); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6A; C8 s5A;
                         C8 s4A; C8 s3A; C8 s2A; C8 s1A; C8 s0A; C8 (Z_to_bv 64 0x3d8a8)]).
       { replace (bv_unsigned spA + -128) with (bv_unsigned sp - 2304) by (clear -HspA; lia).
         eapply cells_frameO; [exact FRa| exact MUr|]. intros x Hx. apply OUTS. subst SPc. clear -Hx. lia. }
       assert (FR16r : rw_cells asegs mr (bv_unsigned sp + -2176) [C8 (Z_to_bv 64 16); C8 (Z_to_bv 64 n); C8 sp; C8 (Z_to_bv 64 0x5ec68)])
         by (eapply cells_frameO; [exact FR16| exact MUr|]; intros x Hx; apply OUTS; subst SPc; clear -Hx; lia).
       assert (FRP0r : rw_cells asegs mr (bv_unsigned sp + -2144) [CB 8 junk0])
         by (eapply cells_frameO; [exact FRP0| exact MUr|]; intros x Hx; apply OUTS; subst SPc; clear -Hx; lia).
       assert (SSr : rw_cells asegs mr (bv_unsigned sp + -2136) [C8 (Z_to_bv 64 (bv_unsigned sp + -2136 + 16)); C8 (Z_to_bv 64 (1 + Z.of_nat (length trc)))])
         by (eapply cells_frameO; [exact SS| exact MUr|]; intros x Hx; apply OUTS; subst SPc; clear -Hx; lia).
       assert (TBr : rw_cells asegs mr (bv_unsigned sp + -2136 + 16) [CB (8 * 255) (u64s tb)])
         by (eapply cells_frameO; [exact TB| exact MUr|]; intros x Hx; apply OUTS; subst SPc; clear -Hx; lia).
       assert (FRSr : rw_cells asegs mr (bv_unsigned sp + -80) [C8 sp; CB 8 junk2; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
         by (eapply cells_frameO; [exact FRS| exact MUr|]; intros x Hx; apply OUTS; subst SPc; clear -Hx; lia).
       destruct ERRC as [e0 ERR0].
       assert (ERR4 : rw_cells asegs m4 AERRNO [C4 e0]).
       { eapply cells_frameO; [exact ERR0| exact MU4|]. cbn [cells_size csize Nat.add]. intros x Hx. cbn [outside].
         unfold AERRNO, ATP in Hx. clear -Hx ATR LO BOT TIMG TIMGa TIMGb. repeat split; lia. }
       assert (ERRr : rw_cells asegs mr AERRNO [C4 e0]).
       { eapply cells_frameO; [exact ERR4| exact MUr|]. cbn [cells_size csize Nat.add]. intros x Hx.
         assert (BI : forall d cap, bufok RESV st d cap -> ~ (d <= x < d + cap)).
         { intros d cap [B|[_ AV]]; [clear -B; lia|]. unfold avoids_all in AV. rewrite forallb_app in AV. apply andb_prop in AV as [AV _].
           destruct ROK as (PCI & _). apply (avoids_pcov_out RESV d cap 0x10000 AIMG_HI x PCI AV). unfold AIMG_HI, AERRNO, ATP in *. clear -Hx. lia. }
         pose proof (BI _ _ B0) as Q0. pose proof (BI _ _ B1) as Q1. pose proof (BI _ _ B2) as Q2.
         subst Wf. cbn [outside]. unfold aregion_info, K_SPACE_SIZE, ARI_STRIDE. change (2^37) with 137438953472.
         unfold AEMB, AERRNO, ATP in *. subst SPc.
         clear -Hx Q0 Q1 Q2 ATR LO BOT TIMG TIMGa TIMGb SP1 C16. repeat split; lia. }
       pose proof ARr as (_ & RTr & _).
       destruct RTr as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & OOM3r & _).
       destruct OOM3r as [oombr OOMr]. rw_split OOMr 2%nat OOMxr RSSr. clear RSSr.

       apply implS_ret.
       replace (ret_pc (Z_to_bv 64 0x3cf68)) with (Z_to_bv 64 0x3cf68) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
       pose proof ARNGr as (RIMGr & _).
       assert (RSTKr : rng RNG' lo (bv_unsigned sp - lo)) by (eapply rng_fp_leG; [exact FPLE | exact RSTK]).
       eapply evtF_cut.
       { eapply (allocN_spec RNG' spA gp tp t0r t1r t2r _ _ a1r a2r a3r a4r a5r a6r a7r _ _ _ _ _ _ _ _ _ _ t3r t4r t5r t6r
                   s0A s1A s2A s3A s4A s5A s6A s7 s8 s9 s10 s11 (Z_to_bv 64 0x3d8a8) _ _ fr0 oombr F fc mr lo);
           first [ exact FRar | exact MIr | exact OOMxr | exact RIMGr
                 | replace (bv_unsigned spA + -128) with (bv_unsigned sp - 2304) by (clear -HspA; lia); exact STr
                 | eapply rng_sub'; [exact RSTKr|]; clear -HspA LO; lia
                 | clear -BOT ATR; lia
                 | clear -LO HspA; lia ]. }
       cbv beta. intros ms1 P1.
       destruct P1 as (t0n & t1n & t2n & a1n & a2n & a3n & a4n & a5n & a6n & a7n & t3n & t4n & t5n & t6n & m1 & -> & MU1 & WM1 & MI1 & ST1 & OOM1).
       assert (OUT1 : forall x, AIMG_HI <= x -> outside [(AOOM, AOOM + 1)]%Z x)
         by (intros x Hx; cbn [outside]; unfold AOOM, AIMG_HI in *; clear -Hx; lia).
       assert (FR16n : rw_cells asegs m1 (bv_unsigned sp + -2176) [C8 (Z_to_bv 64 16); C8 (Z_to_bv 64 n); C8 sp; C8 (Z_to_bv 64 0x5ec68)])
         by (eapply cells_frameO; [exact FR16r| exact MU1|]; intros x Hx; apply OUT1; unfold AIMG_HI; clear -Hx ATR LO BOT; lia).
       assert (FRP0n : rw_cells asegs m1 (bv_unsigned sp + -2144) [CB 8 junk0])
         by (eapply cells_frameO; [exact FRP0r| exact MU1|]; intros x Hx; apply OUT1; unfold AIMG_HI; clear -Hx ATR LO BOT; lia).
       assert (SSn : rw_cells asegs m1 (bv_unsigned sp + -2136) [C8 (Z_to_bv 64 (bv_unsigned sp + -2136 + 16)); C8 (Z_to_bv 64 (1 + Z.of_nat (length trc)))])
         by (eapply cells_frameO; [exact SSr| exact MU1|]; intros x Hx; apply OUT1; unfold AIMG_HI; clear -Hx ATR LO BOT; lia).
       assert (TBn : rw_cells asegs m1 (bv_unsigned sp + -2120) [CB (8 * 255) (u64s tb)]).
       { replace (bv_unsigned sp + -2120) with (bv_unsigned sp + -2136 + 16) by (clear; lia).
         eapply cells_frameO; [exact TBr| exact MU1|]. intros x Hx. apply OUT1. unfold AIMG_HI. clear -Hx ATR LO BOT. lia. }
       assert (FRSn : rw_cells asegs m1 (bv_unsigned sp + -80) [C8 sp; CB 8 junk2; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
         by (eapply cells_frameO; [exact FRSr| exact MU1|]; intros x Hx; apply OUT1; unfold AIMG_HI; clear -Hx ATR LO BOT; lia).
       assert (ERRn : rw_cells asegs m1 AERRNO [C4 e0]).
       { eapply cells_frameO; [exact ERRr| exact MU1|]. cbn [cells_size csize Nat.add]. intros x Hx. cbn [outside]. unfold AOOM, AERRNO, ATP in *. clear -Hx. lia. }

       replace (ret_pc (Z_to_bv 64 0x3d8a8)) with (Z_to_bv 64 0x3d8a8) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
       assert (EspA : spA = Z_to_bv 64 (bv_unsigned sp + -2176)).
       { enough (E : Z_to_bv 64 (bv_unsigned spA) = Z_to_bv 64 (bv_unsigned sp + -2176)) by (rewrite Z_to_bv_bv_unsigned in E; exact E).
         apply Z_to_bv_eqm. rewrite HspA. zeq. }
       rewrite HspA in ST1. replace (bv_unsigned sp - 2176) with (bv_unsigned sp + -2176) in ST1 by (clear; lia). rewrite EspA.
       eapply evtF_mono.
       { eapply (icptN16_spec RNG' sp gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s7 s8 s9 s10 s11 _ _ _ _ ra s0 s1 s2 s3 s4 s5 s6 F fc m1 lo n junk0 junk2 e0);
           first [ exact ST1 | exact MI1 | exact TP | exact ERRn | exact FR16n | exact FRP0n | exact FRSn | exact RIMGr | exact RSTKr
                 | eexists; split; [exact SSn| reflexivity]
                 | eexists; split; [exact TBn| reflexivity]
                 | clear -BOT ATR; lia
                 | clear -LO; lia ]. }
       cbv beta. intros ms2 P2.
       destruct P2 as (t0e & t1e & t2e & a1e & a2e & a3e & a4e & a5e & a6e & a7e & t3e & t4e & t5e & t6e & m2 & -> & MU2 & WM2 & MI2 & ST2 & ERR2).

       pose proof (munch_app _ _ _ _ _ MU1 MU2) as MUn. pose proof (wmono_trans asegs _ _ _ WM1 WM2) as WMn.
       assert (AXFSr : axflags L st2 mr).
       { intros c' Hc' NC'. destruct (Z.eq_dec c' c) as [->|NE]; [exact AXFr|].
         pose proof (C6F4 c' Hc' NC') as F4. unfold axflag in *.
         assert (EXE : exh_mem c' st2 = exh_mem c' st).
         { destruct STEQ as [[_ ->]|[_ [e2 ->]]]; [apply init_cache_exh|]. rewrite exh_mem_set_emb, (exh_mem_set_other c c' _ NE). apply init_cache_exh. }
         rewrite EXE. eapply cells_frameO; [exact F4| exact MUr|]. cbn [cells_size csize Nat.add]. intros x Hx.
         apply (nf_flag_outside L RESV st SPc c ALO ROK HCK SPHIc Wf c' x PCSf Hc' NE). clear -Hx. lia. }
       destruct (c6_frame L RESV RNG' st2 mr m2 _ ALO ROK AXGr AXFSr MUn) as [C6G2 C6F2].
       { cbn [app]. apply Forall_cons; [unfold c6_piece, AOOM; cbn [fst snd]; intros _; do 8 right; left; clear; lia|].
         apply Forall_cons; [unfold c6_piece; cbn [fst snd]; intros _; left; clear -LO BOT; lia|].
         apply Forall_cons; [unfold c6_piece; cbn [fst snd]; intros _; do 9 right; clear; lia| apply Forall_nil]. }

       assert (AR2 : AREP (AH DI AQ ASEC AFK) L st2 X m2).
       { eapply (AREP_frame_null _ HL L st2 X mr m2 (bv_unsigned sp - 32) ALO ARr); [| exact WMn| clear -LO BOT; lia|].
         { eapply munch_weaken; [| exact MUn]. unfold sub_fp, AOOM, AERRNO, ATP. cbn [app outside]. intros q Hq. clear -Hq. repeat split; lia. }
         exists (Z_to_bv 8 1). eapply cells_frameO; [exact OOM1| exact MU2|]. cbn [cells_size csize Nat.add]. intros x Hx. cbn [outside].
         unfold AOOM, AERRNO, ATP in *. clear -Hx ATR LO BOT. repeat split; lia. }
       assert (LIVE2 : a_live st2 = a_live st).
       { pose proof (init_cache_fields st) as (E1 & _). destruct STEQ as [[_ ->]|[_ [e2 ->]]]; [exact E1|]. rewrite <- E1. destruct (init_cache st); reflexivity. }
       pose proof (ablocks_same L st st2 X X LB BL eq_refl LIVE2) as BL2.
       pose proof (munch_app _ _ _ _ _ MU4 (munch_app _ _ _ _ _ MUr MUn)) as MUt.
       assert (PCSt : Forall (nf_piece L RESV st (bv_unsigned sp) c)
                        ([(bv_unsigned sp - 2352, bv_unsigned sp); (al_t L + 3168, al_t L + 3169)] ++ Wf ++ [(AOOM, AOOM + 1)] ++ [(bv_unsigned sp - 2192, bv_unsigned sp - 2176); (AERRNO, AERRNO + 4)])%Z).
       { apply Forall_app. split; [| apply Forall_app; split].
         - apply Forall_cons; [intros _; unfold nf_kind; cbn [fst snd]; left; clear -LO BOT; lia|].
           apply Forall_cons; [intros _; unfold nf_kind; cbn [fst snd]; right; left; clear; lia| apply Forall_nil].
         - eapply Forall_impl; [| exact PCSf]. intros iv K. apply (nf_piece_SP L RESV st SPc (bv_unsigned sp) c iv); [subst SPc; clear; lia| exact K].
         - cbn [app]. apply Forall_cons; [intros _; unfold nf_kind, AOOM; cbn [fst snd]; do 5 right; left; clear; lia|].
           apply Forall_cons; [intros _; unfold nf_kind; cbn [fst snd]; left; clear -LO BOT; lia|].
           apply Forall_cons; [intros _; unfold nf_kind; cbn [fst snd]; do 6 right; clear; lia| apply Forall_nil]. }
       destruct (nf_fake L RESV st (bv_unsigned sp) c _ ALO ROK HCK SPHI (nzl_pieces _ _ _ _ _ _ PCSt)) as (D72 & FU & D48).
       pose proof (hfD _ HLD L LB m m2 _ HFK (munch_nzl _ _ _ MUt) D72 FU D48) as HFK2.
       assert (PRESe : aheap_pres_e CI LB (bv_unsigned sp) m m2).
       { intros a Ha CL NERR.
         pose proof (nf_client_outside L RESV st X (bv_unsigned sp) c ALO ROK HCK SPHI CI CI_OK CI_OK3 WF LB _ a BL PCSt Ha CL NERR) as OUT.
         assert (E : m2 (wa a) = m (wa a)) by (apply MUt; rewrite wa_unsigned by exact Ha; exact OUT).
         split; [exact E|]. intros Hw. rewrite (AFrameD.wview_agree asegs m m2 (wa a) E). exact Hw. }

       unfold amalloc_post_x. cbn [fst snd]. split.
       { unfold c6_at. cbn [ms_mem]. split; [exact C6G2| exact C6F2]. }
       split; [exact FPLE|]. do 14 eexists. exists m2. split; [reflexivity|]. split; [exact MI2|]. split; [exact ST2|]. split; [exact PRESe|].
       split; [| exact ERR2].
       split; [exact ALO|]. split; [exact ARNGr|]. split; [exists X; split; [exact AR2| exact BL2]| exact HFK2]. }

  intros st_pre X_pre RNG1 m_pre cnt k ms1 CRET. destruct CRET as (CRET & EMBp & EXHp & AXFp & AXGp). unfold calloc_retG in CRET.
  destruct CRET as (FPLE & ARp & ARNGp & HCNT & POS & NK & NB & KR & XB & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & MUc & WMc & MIp
                    & t0d & t1d & t2d & a1d & a2d & a3d & a4d & a5d & a6d & a7d & t3d & t4d & t5d & t6d & m1 & stj1 & -> & MU1 & WM1 & MI1 & ST1 & CR1 & STS1).
  rewrite ?unsigned_lit in MUc by (clear -SPR HspA LO BOT STK3; unfold AMALLOC_STACK in *; lia).
  rewrite ?unsigned_lit in MU1 by (clear -SPR HspA LO BOT STK3; unfold AMALLOC_STACK in *; lia).
  rewrite ?unsigned_lit in ST1 by (clear -SPR HspA LO BOT STK3; unfold AMALLOC_STACK in *; lia).
  replace (bv_unsigned spA + -128) with (bv_unsigned sp - 2304) in ST1 by (clear -HspA; lia).
  cbn beta iota. apply implS_ret.
  replace (ret_pc (Z_to_bv 64 0x3cf68)) with (Z_to_bv 64 0x3cf68) by (symmetry; apply ret_pc_even; [lia|reflexivity]).

  pose proof ARp as AR0. destruct AR0 as (WF' & RT' & INST' & THR' & CLS' & HQ' & HS' & HD' & HRO' & RT2' & AVL' & RT3').
  destruct THR' as (T0' & T40' & CACHES' & CSTATS' & [sj' [STATS' LSJ']] & UNW').
  pose proof WF' as WF0. destruct WF0 as (SBE' & PAE' & SAL' & SLO' & SHI' & PERC' & OUTC' & BUSY' & LIVE' & FRESH' & UNIQ').
  destruct (PERC' c HCK) as (B1' & B2' & B3' & B4' & B5' & B6' & B7' & LENF' & LENC' & CNTB' & ND' & RANGE').
  destruct (kit_cache_pop _ L st_pre X_pre m_pre c cnt ARp HCK HCNT POS) as (k' & chunks & NK' & _ & _ & CR & CH & LCH & NTH & JK & FSH).
  assert (EK : k' = k) by (rewrite NK in NK'; injection NK'; intros E; symmetry; exact E). subst k'.

  set (S := size_of_class c) in *.
  set (AB := aslot_addr L c k) in *.
  assert (KSF : 0 <= k * S /\ k * S + S <= c_allocated_user (get_cls st_pre c) /\ (k * S) mod 16 = 0).
  { unfold ndist in KR. fold S in KR. fold S in SZB. fold S in SM16.
    assert (P0 : 0 <= k * S) by (clear -KR SZB; apply Z.mul_nonneg_nonneg; lia).
    assert (Q1 : k + 1 <= c_allocated_user (get_cls st_pre c) / S) by (clear -KR; lia).
    assert (M1 : (k + 1) * S <= c_allocated_user (get_cls st_pre c) / S * S) by (apply Z.mul_le_mono_nonneg_r; clear -Q1 SZB; lia).
    pose proof (Z.mul_div_le (c_allocated_user (get_cls st_pre c)) S ltac:(clear -SZB; lia)) as M2.
    split; [exact P0|]. split.
    - rewrite Z.mul_add_distr_r, Z.mul_1_l in M1. rewrite (Z.mul_comm S) in M2. clear -M1 M2 P0 SZB. lia.
    - destruct (proj1 (Z.mod_divide S 16 ltac:(clear; lia)) SM16) as [q Hq]. rewrite Hq.
      replace (k * (q * 16)) with ((k * q) * 16) by (clear; lia). apply Z_mod_mult. }
  destruct KSF as (KS0 & KS1 & KS2).
  assert (GEO : al_space_beg L <= AB /\ AB + S <= al_space_beg L + K_SPACE_SIZE /\ AB mod 16 = 0
                /\ AB + S <= aregion L c + c_allocated_user (get_cls st_pre c) /\ aregion L c <= AB).
  { subst AB. unfold aslot_addr, aregion, K_REGION, K_SPACE_SIZE, K_FREEARR_OFF, K_ALIGN in *. fold S.
    remember (k * S) as KS eqn:HKS. clear HKS.
    change (2^37) with 137438953472. change (2^32) with 4294967296 in *.
    split; [clear -KS0 C16; lia|]. split; [clear -KS1 B1' B2' C16 NSZ; lia|]. split; [| clear -KS0 KS1 B1'; lia].
    clear -SP3 C16 KS2. Z.div_mod_to_equations; lia. }
  destruct GEO as (G1 & G2 & G3 & G4 & G5). unfold K_SPACE_SIZE in G2. change (2^37) with 137438953472 in G2.
  assert (EAB : AB = aslot_addr L c k) by reflexivity. clearbody AB.
  assert (ES : S = size_of_class c) by reflexivity.

  assert (RZC : rz_size n = 16 \/ 32 <= rz_size n) by (clear -RZR RZM; Z.div_mod_to_equations; lia).
  destruct (slot_carveG m_pre AB S n (rz_size n) JK RZC ltac:(clear -N; lia) ltac:(fold S in NSZ; clear -NSZ NS RSR; lia))
    as (b0 & b1 & szh & szl & ctxj & uj & j1 & j2 & HDR & B1 & UJ & LH & TL).
  set (UB := AB + rz_size n) in *. assert (EUB : UB = AB + rz_size n) by reflexivity. clearbody UB.

  set (grz := shlen (rz_size n)). set (g := shlen (n - n mod 8)). set (room := if n mod 8 =? 0 then 0 else 1).
  assert (GR12 : grz = rz_size n / 8 /\ g = (n - n mod 8) / 8).
  { subst grz g. unfold shlen. rewrite !Z.shiftr_div_pow2 by lia. split; reflexivity. }
  destruct GR12 as [GR1 GR2].
  assert (GR3 : 2 <= grz) by (rewrite GR1; generalize RZR; clear; intros; Z.div_mod_to_equations; lia).
  assert (GR4 : 0 <= g) by (rewrite GR2; generalize N; clear; intros; Z.div_mod_to_equations; lia).
  assert (GR5 : 0 <= room <= 1) by (subst room; clear; destruct (n mod 8 =? 0); lia).
  assert (GR6 : grz + g + room <= shlen S).
  { rewrite GR1, GR2. subst room. unfold shlen. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
    fold S in NSZ. fold S in SM16. generalize NSZ NS RSR RSM SM16 RZM RZR N. clear. intros.
    destruct (Z.eqb_spec (n mod 8) 0) as [M0|M0]; Z.div_mod_to_equations; lia. }
  assert (GR7 : shad UB = shad AB + grz).
  { rewrite GR1, EUB. unfold shad, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
    generalize G3 RZM RZR. clear. intros. Z.div_mod_to_equations. lia. }
  assert (GR89 : 0x2008fff7000 <= shad AB /\ shad AB + shlen S <= 0x10007fef8000).
  { unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
    unfold K_SPACE_SIZE, K_SPACE_EXTRA in *. generalize G1 G2 SP1 SP2. clear. intros. Z.div_mod_to_equations. lia. }
  destruct GR89 as [GR8 GR9].
  destruct (shadow_carve m_pre (shad AB) (shlen S) grz g room FSH GR3 GR4 GR6 GR5) as (SHA & SHpre & [sjunk SHU] & SHP & SHsuf).
  rewrite <- GR7 in SHU, SHP, SHsuf.
  set (PG := shad UB + g) in *.

  pose proof RT' as RT0.
  destruct RT0 as (GPG' & GOT' & GOT80' & RIC' & LS1' & REAL' & IMAX4' & FLG5' & FLG' & HPP' & SHB' & CANP' & TI' & TK' & INI2' & LAY' & MCS' & OOM3'
                    & PGC' & HK2' & CF8' & CF34' & CSMT' & T88' & TSD' & LS2' & CT8' & CT').
  pose proof INI2' as INI'. rw_split INI' 1%nat INI1' INIx. clear INIx.
  destruct OOM3' as [oomb' OOM']. rw_split OOM' 2%nat OOMx RSS'. clear OOMx.
  pose proof IMAX4' as IMAX'. rw_split IMAX' 3%nat IMAX3' IMAXx. clear IMAXx.
  pose proof HK2' as HK'. rw_split HK' 1%nat HK1' HKx. clear HKx.
  pose proof T0' as TT0'. rw_split TT0' 1%nat TTctx' TT'.
  destruct (junk_split m_pre (al_t L + 2768) 16 16 CSTATS' ltac:(lia) ltac:(lia)) as [CSa CSb].
  destruct (junk_split m_pre (al_t L + 2768 + 16) 8 8 CSb ltac:(lia) ltac:(lia)) as [CS8 CSc].
  replace (al_t L + 2768 + 16) with (al_t L + 2784) in CS8 by lia.
  replace (al_t L + 2768 + 16 + 8) with (al_t L + 2792) in CSc by lia.
  destruct INST' as (I32' & I48' & I64' & I72' & I112' & I680' & I984' & I40' & I56').
  pose proof ARNGp as ARNGp0. destruct ARNGp as (RIMG' & RT4' & RCTX' & RNO' & RST' & RRI' & RFK' & RSFK' & RDTLS' & RCLS' & RPA' & RSECS' & RPSH').
  destruct (RCLS' c HCK) as (RREG & RSREG & RFA & RSFA).

  destruct (alayout_slot_disj L AB 65536 ALO G1 ltac:(unfold K_SPACE_SIZE, K_FREEARR_OFF, aregion, K_REGION in *; generalize G4 B1' B2' C16 SP1 SZB; clear; intros; change (2^37) with 137438953472; lia) ltac:(clear; lia))
    as (DJT & DJC & DJN & DJS & DJF).
  assert (RUf : rng RNG1 (UB - 16) (n + 16)) by (eapply rng_sub'; [exact RREG|]; generalize G4 G5 B1' RZR N EUB KS0 NSZ NS RSR; clear; intros; lia).
  assert (RABf : rng RNG1 AB 16) by (eapply rng_sub'; [exact RREG|]; generalize G4 G5 B1' RZR N NSZ NS RSR; clear; intros; lia).
  assert (REG8 : aregion L c mod 8 = 0 /\ c_mapped_user (get_cls st_pre c) mod 8 = 0).
  { unfold aregion, K_REGION, K_USER_MAP, K_ALIGN in *. generalize SP3 B4'; clear; intros. Z.div_mod_to_equations; lia. }
  assert (SHM : shad (aregion L c) <= shad AB /\ shad UB + g + room <= shad (aregion L c) + shlen (c_mapped_user (get_cls st_pre c))).
  { rewrite GR7, GR2, GR1. unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
    fold S in NSZ. fold S in SM16. subst room. generalize G4 G5 B1' N NSZ RSR RSM NS RZR RZM SM16 G3 EUB REG8; clear; intros.
    destruct (Z.eqb_spec (n mod 8) 0); Z.div_mod_to_equations; lia. }
  destruct SHM as [SHM1 SHM2].
  assert (RSAf : rng RNG1 (shad AB) 1) by (eapply rng_sub'; [exact RSREG|]; generalize SHM1 SHM2 GR3 GR4 GR5 GR7; clear; intros; lia).
  assert (RSUf : rng RNG1 (shad UB) (shlen (n - n mod 8))).
  { eapply rng_sub'; [exact RSREG|]. fold g. generalize SHM1 SHM2 GR3 GR4 GR5 GR7. clear. intros. lia. }
  assert (RSPf : n mod 8 <> 0 -> rng RNG1 PG 1).
  { intros NE. eapply rng_sub'; [exact RSREG|]. subst PG.
    assert (R1 : room = 1) by (subst room; generalize NE; clear; intros NE; destruct (Z.eqb_spec (n mod 8) 0); [exfalso; exact (NE ltac:(assumption)) | reflexivity]).
    rewrite R1 in SHM2. generalize SHM1 SHM2 GR3 GR4 GR7; clear; intros. lia. }
  assert (SLS : shlen S <= 8192) by (fold S in NSZ; unfold shlen; rewrite Z.shiftr_div_pow2 by (clear; lia); change (2^3) with 8; clear -NSZ; Z.div_mod_to_equations; lia).
  assert (SB34 : 0 <= shlen (n - n mod 8) <= 8192 /\ PG + 1 <= 0x10007fff8000).
  { subst PG. fold g. rewrite GR7. generalize GR4 GR6 GR9 GR3 GR5 SLS; clear; intros; lia. }
  destruct SB34 as [SB3 SB4].
  assert (RCTX4' : rng RNG1 (al_ctx L) 4096) by (eapply rng_sub'; [exact RCTX'|]; clear; lia).
  assert (DJC4 : al_ctx L + 4096 <= AB \/ AB + 65536 <= al_ctx L) by (generalize DJC; clear; intros; lia).
  assert (CNT16 : 0 < cnt <= 16).
  { unfold max_count in CNTB'. generalize POS HCNT CNTB' MCB; clear. destruct (a_cinit st_pre); intros; lia. }
  assert (PGE : PG = shad UB + shlen (n - n mod 8)) by reflexivity.
  assert (RSTK1 : rng RNG1 lo (bv_unsigned sp - lo)) by (eapply rng_fp_le; [exact FPLE | exact RSTK]).

  set (mu0 := c_mapped_user (get_cls st c)) in *.
  assert (OBJ : aregion_info L c = al_space_beg L + 137438953472 + c * 128 /\ aregion L c = al_space_beg L + c * 4294967296
                /\ shad (al_space_beg L + c * 4294967296) + 536870912 <= 17594333495296).
  { unfold aregion_info, aregion, K_REGION, K_SPACE_SIZE, ARI_STRIDE. change (2^37) with 137438953472. change (2^32) with 4294967296.
    split; [reflexivity|]. split; [reflexivity|]. rewrite shad_div. clear -SP1 SP2 C16. unfold ASHOFF, K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^37) with 137438953472 in *.
    Z.div_mod_to_equations. lia. }
  destruct OBJ as (RIE & RBE & SHHI).
  assert (MU41 : munch [(bv_unsigned sp - 3888, bv_unsigned sp - 2304); (al_t L + 208, al_t L + 3168); (AINSTANCE, AINSTANCE + 728);
                        (al_space_beg L + 137438953472 + c * 128, al_space_beg L + 137438953472 + c * 128 + 128);
                        (al_space_beg L + c * 4294967296 + mu0, al_space_beg L + c * 4294967296 + 4294967296);
                        (shad (al_space_beg L + c * 4294967296 + mu0), shad (al_space_beg L + c * 4294967296) + 536870912)]%Z m4 m1).
  { eapply munch_trans; [eapply munch_weaken; [| exact MUc] | eapply munch_weaken; [| exact MU1]];
      unfold sub_fp; cbn [outside]; intros q Hq; rewrite ?RIE, ?RBE in *; unfold K_REGION, acache_addr in *; change (2^32) with 4294967296 in *;
      rewrite ?shlen_div in *; change (4294967296 / 8) with 536870912 in *; clear -Hq HspA C16; lia. }
  assert (WM41 : wmono asegs m4 m1) by (eapply wmono_trans; [exact WMc | exact WM1]).
  unfold K_SPACE_SIZE, K_SPACE_EXTRA in SP2. change (2^37) with 137438953472 in SP2.
  xport FRa MU41 WM41 ltac:(clear -SPR LO BOT STK3 TL1 TL2 SP1 SP2 C16 SHHI TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold AMALLOC_STACK, AINSTANCE in *; lia).
  xport FR16 MU41 WM41 ltac:(clear -SPR LO BOT STK3 TL1 TL2 SP1 SP2 C16 SHHI TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold AMALLOC_STACK, AINSTANCE in *; lia).
  xport FRP0 MU41 WM41 ltac:(clear -SPR LO BOT STK3 TL1 TL2 SP1 SP2 C16 SHHI TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold AMALLOC_STACK, AINSTANCE in *; lia).
  xport SS MU41 WM41 ltac:(clear -SPR LO BOT STK3 TL1 TL2 SP1 SP2 C16 SHHI TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold AMALLOC_STACK, AINSTANCE in *; lia).
  xport TB MU41 WM41 ltac:(rewrite LTB; clear -SPR LO BOT STK3 TL1 TL2 SP1 SP2 C16 SHHI TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold AMALLOC_STACK, AINSTANCE in *; lia).
  xport FRS MU41 WM41 ltac:(clear -SPR LO BOT STK3 TL1 TL2 SP1 SP2 C16 SHHI TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold AMALLOC_STACK, AINSTANCE in *; lia).

  xport HDR MU1 WM1 ltac:(clear -HspA DJT SPR SP2 G1 G2 EUB RZR N NSZ NS RSR LO BOT STK3 C16; unfold acache_addr, AMALLOC_STACK, K_SPACE_SIZE in *; lia).
  xport UJ MU1 WM1 ltac:(clear -HspA DJT SPR SP2 G1 G2 EUB RZR N NSZ NS RSR LO BOT STK3 C16; unfold acache_addr, AMALLOC_STACK, K_SPACE_SIZE in *; lia).
  xport SHA MU1 WM1 ltac:(cbv delta [g grz room PG] in *; clear -HspA SPR GR1 GR2 GR3 GR4 GR5 GR6 GR7 GR8 GR9 LO BOT STK3 TL1 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport SHU MU1 WM1 ltac:(cbv delta [g grz room PG] in *; clear -HspA SPR GR1 GR2 GR3 GR4 GR5 GR6 GR7 GR8 GR9 SB3 LO BOT STK3 TL1 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  assert (SHP1 : n mod 8 <> 0 -> rw_cells asegs m1 PG [C1 (Z_to_bv 8 250)]).
  { intros NE. specialize (SHP ltac:(subst room; generalize NE; clear; intros NE; destruct (Z.eqb_spec (n mod 8) 0); [exfalso; exact (NE ltac:(assumption)) | reflexivity])).
    xport SHP MU1 WM1 ltac:(cbv delta [g grz room PG] in *; clear -HspA SPR GR1 GR2 GR3 GR4 GR5 GR6 GR7 GR8 GR9 SB3 SB4 LO BOT STK3 TL1 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia). exact SHP. }
  assert (LH1 : 16 < rz_size n -> rw_cells asegs m1 AB [C8 j1; C8 j2]).
  { intros R16. pose proof (proj1 (LH R16)) as LH0.
    xport LH0 MU1 WM1 ltac:(clear -HspA DJT SPR SP2 G1 G2 EUB RZR N NSZ NS RSR LO BOT STK3 C16; unfold acache_addr, AMALLOC_STACK, K_SPACE_SIZE in *; lia). exact LH0. }
  xport GOT' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport GOT80' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport REAL' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport SHB' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport CANP' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport HPP' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport CSMT' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport FLG5' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport FLG' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport HK1' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport LS1' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport LS2' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport LAY' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport MCS' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport CF34' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport INI1' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport RSS' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport IMAX3' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport TI' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport TK' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport T88' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, ATP88, AMALLOC_STACK in *; lia).
  xport TSD' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, ATSD, AMALLOC_STACK in *; lia).
  xport CT' MU1 WM1 ltac:(ub CL5; clear -HspA Y SPR TL1 CL1 CL2 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb CTXi CBND CBNDa CBNDb; unfold acache_addr, AMALLOC_STACK, AIMG_HI in *; lia).
  xport CT8' MU1 WM1 ltac:(ub CL5; clear -HspA Y SPR TL1 CL1 CL2 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb CTXi CBND CBNDa CBNDb; unfold acache_addr, AMALLOC_STACK, AIMG_HI in *; lia).
  xport TTctx' MU1 WM1 ltac:(clear -HspA SPR TL1 TL2 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport UNW' MU1 WM1 ltac:(clear -HspA SPR TL1 TL2 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport STATS' MU1 WM1 ltac:(rewrite LSJ'; clear -HspA SPR TL1 TL2 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, ASTATS_WORDS, AMALLOC_STACK in *; lia).
  assert (DEP1 : ADEPOT DI L m1).
  { eapply (adi_frame DI); [exact HD' | exact MU1 | exact WM1 |]. unfold acache_addr.
    repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq; ub DL7; ub DL8; clear -Hq Y Y0 HspA SPR TL1 TL2 DL1 DL2 DL3 DL4 DL5 DL6 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb NODi NBND NBNDa NBNDb STOi SBND SBNDa SBNDb; unfold AMALLOC_STACK, AIMG_HI in *; lia|]).
    apply Forall_nil. }

  assert (PF : pfactsG (bv_unsigned sp) (al_t L) (al_space_beg L) c mu0 ATOP lo).
  { unfold pfactsG. pose proof (ao_t L ALO) as OT. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in OT.
    unfold AMALLOC_STACK, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN, K_FREEARR_OFF, K_USER_MAP in *. change (2^37) with 137438953472 in *.
    ub TSP. generalize LO BOT SP47 STK2 STK3 OT SP1 SP2 SAL C16 A1 A2 A4 Y. clear. intros.
    repeat match goal with H : _ /\ _ |- _ => destruct H end.
    repeat split; first [reflexivity | assumption | lia | Z.div_mod_to_equations; lia]. }
  assert (MUall : munch [(bv_unsigned sp - 4096, bv_unsigned sp); (al_t L + 208, al_t L + 3169); (AINSTANCE, AINSTANCE + 728);
                         (al_space_beg L + 137438953472 + c * 128, al_space_beg L + 137438953472 + c * 128 + 128);
                         (al_space_beg L + c * 4294967296 + mu0, al_space_beg L + c * 4294967296 + 4294967296);
                         (shad (al_space_beg L + c * 4294967296 + mu0), shad (al_space_beg L + c * 4294967296) + 536870912)]%Z m m_pre).
  { eapply munch_trans; [eapply munch_weaken; [| exact MU4] | eapply munch_weaken; [| exact MUc]];
      unfold sub_fp; cbn [outside]; intros q Hq; rewrite ?RIE, ?RBE in *; unfold K_REGION in *; change (2^32) with 4294967296 in *;
      rewrite ?shlen_div in *; change (4294967296 / 8) with 536870912 in *; clear -Hq HspA; lia. }
  assert (WMall : wmono asegs m m_pre) by (eapply wmono_trans; [exact WM4 | exact WMc]).

  assert (BB : forall b, In b (x_busy X) ->
      al_space_beg L <= xb_alloc L b /\ xb_alloc L b + size_of_class (xb_class b) <= al_space_beg L + 137438953472
      /\ (xb_alloc L b + size_of_class (xb_class b) <= al_space_beg L + c * 4294967296 + mu0 \/ al_space_beg L + c * 4294967296 + 4294967296 <= xb_alloc L b)).
  { intros b Hb. destruct (BUSY b Hb) as [CLB _].
    destruct (PERC (xb_class b) CLB) as (Q1 & Q2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & QR).
    pose proof (size_of_class_facts (xb_class b) CLB) as [QS _].
    assert (KB : 0 <= xb_slot b < ndist st (xb_class b)).
    { apply QR. apply in_app_iff. right. apply in_app_iff. right. unfold busy_slots. apply in_map_iff. exists b. split; [reflexivity|].
      apply filter_In. split; [exact Hb| apply Z.eqb_refl]. }
    pose proof (slot_in_region L st (xb_class b) (xb_slot b) ltac:(clear -QS; lia) (proj1 Q1) KB) as (P5 & P4 & P0).
    unfold xb_alloc. unfold K_NUM_CLASSES in CLB. unfold K_FREEARR_OFF in Q2.
    destruct (Z.eq_dec (xb_class b) c) as [EC|NC].
    - rewrite EC in P5, P4, Q1, Q2 |- *. rewrite RBE in P5, P4. change (c_mapped_user (get_cls st c)) with mu0 in Q1, Q2.
      clear -P5 P4 Q1 Q2 A1 A2 C16. unfold K_FREEARR_OFF in *. lia.
    - pose proof (region_other_geo L c (xb_class b) ALO ltac:(clear -C16; lia) CLB NC) as (R1 & R2 & R3 & _). rewrite RBE in R2.
      clear -P5 P4 Q1 Q2 R1 R2 R3 A1. lia. }
  pose proof (ao_fake L ALO) as FKO. unfold aobj in FKO. pose proof (ao_res L ALO) as ORS. unfold aobj in ORS. pose proof (ao_space L ALO) as RSP.
  pose proof (ad_fake_res L ALO) as D_f_res. pose proof (ad_t_fake L ALO) as D_t_f. pose proof (ad_dtls_res L ALO) as D_d_res. pose proof (ad_t_dtls L ALO) as D_t_d.
  pose proof (ao_dtls L ALO) as ODT. unfold aobj in ODT. unfold adisj in D_f_res, D_t_f, D_d_res, D_t_d.
  assert (FKD : forall cls FA sz, In (mkABlock (ABFake cls) FA sz) LB -> al_fake L <= FA /\ 0 <= sz /\ FA + sz <= al_fake L + 11571200)
    by (intros cls FA sz Hin; exact (proj1 (proj2 BL) cls FA sz Hin)).
  assert (PRES : aheap_pres CI LB (bv_unsigned sp) m m_pre).
  { intros a Ha CL. split; [| intros Hw; apply WMall; exact Hw].
    apply MUall. rewrite wa_unsigned by exact Ha.
    destruct CL as [STa | [CIa | [BLK | SH]]].
    - eapply disjoint_outside; [eapply (Q_stack _ _ _ _ _ _ _ PF a 1); clear -STa; lia | clear; lia].
    - destruct CIa as (iv & Hiv & R). pose proof (proj1 (Forall_forall _ _) CI_OK iv Hiv) as (Q1 & Q2 & Q3).
      pose proof (proj1 (Forall_forall _ _) CI_OK2 iv Hiv) as Q4. cbn [fst snd] in *.
      eapply disjoint_outside; [eapply (Q_img _ _ _ _ _ _ _ PF a 1); unfold AIMG_HI in *; clear -R Q1 Q3 Q4; lia | clear; lia].
    - destruct BLK as (b & Hb & R). destruct b as [[p|cls] A n']; cbn [ab_addr ab_size] in R.
      + destruct (proj1 BL p A n' Hb) as [(xb & Hxb & Sb & Ub & Nb)|(mb0 & ms0 & Lp & EUA & Gs)].
        * destruct (BB xb Hxb) as (Bb1 & Bb2 & Bb3).
          pose proof (awf_fits L st X xb WF Hxb) as FIT. unfold xb_fits in FIT. rewrite Sb in FIT. unfold xb_user in Ub. subst A n'.
          eapply disjoint_outside; [eapply (Q_slot _ _ _ _ _ _ _ PF a 1) | clear; lia]; clear -R Bb1 Bb2 Bb3 FIT; lia.
        *
          cbn [sec_wf1] in Gs. destruct Gs as (Gs1 & Gs2 & Gs3 & Gs4 & Gs5 & Gs6 & (Ct & Cc & Cr & Cp & Cn & Cs & Cf & Cd)).
          pose proof (sec_facts n' ltac:(clear -Gs5; lia) Gs6) as SF. subst A. unfold SEC_UOFF, K_HIGH_MEM in *.
          unfold ablk, KLS, AIMG_HI in Gs2.
          eapply disjoint_outside; [eapply (Q_obj _ _ _ _ _ _ _ PF a 1) | clear; lia]; clear -R Gs2 Gs3 Gs4 Gs5 SF Ct Cr RSP ORS; lia.
      + destruct (FKD cls A n' Hb) as (K1 & K2 & K3). atop_facts.
        eapply disjoint_outside; [eapply (Q_obj _ _ _ _ _ _ _ PF a 1) | clear; lia];
          clear -R K1 K3 FKO D_t_f D_f_res RSP OFKi OFKs OFKsa OFKsb; lia.
    - destruct SH as (a' & Ha' & ->).
      destruct Ha' as [STa | [CIa | FK]].
      + eapply disjoint_outside; [eapply (Q_shad_hi _ _ _ _ _ _ _ PF a'); unfold AMALLOC_STACK in *; clear -STa LO BOT STK3; lia | clear; lia].
      + destruct CIa as (iv & Hiv & R). pose proof (proj1 (Forall_forall _ _) CI_OK iv Hiv) as (Q1 & Q2 & Q3). cbn [fst snd] in *.
        eapply disjoint_outside; [eapply (Q_shad_img _ _ _ _ _ _ _ PF a'); unfold AIMG_HI in *; clear -R Q1 Q3; lia | clear; lia].
      + destruct FK as (cls & FA & sz & Hin & R). destruct (FKD cls FA sz Hin) as (K1 & K2 & K3). atop_facts.
        eapply disjoint_outside; [eapply (Q_shad_obj _ _ _ _ _ _ _ PF a') | clear; lia]; clear -R K1 K3 FKO D_f_res RSP OFKi OFKs OFKsa OFKsb; lia. }
  assert (HFKp : AFK L LB m_pre).
  { eapply (hf_frame _ HL L LB m m_pre); [exact HFK | exact MUall | exact WMall | exact (Q_tfs _ _ _ _ _ _ _ PF) |].
    unfold fake_untouched. pose proof (ao_t L ALO) as OT. unfold aobj in OT.
    assert (SHF : 2148261376 <= shad (al_fake L) /\ shad (al_fake L) + shlen 11571200 <= 17594332446720
                  /\ (shad (al_space_beg L + c * 4294967296) + 536870912 <= shad (al_fake L)
                      \/ shad (al_fake L) + shlen 11571200 <= shad (al_space_beg L + c * 4294967296 + mu0))
                  /\ shad (al_space_beg L + c * 4294967296) <= shad (al_space_beg L + c * 4294967296 + mu0)
                  /\ 2201439137792 <= shad (al_space_beg L + c * 4294967296)).
    { rewrite !shad_div, !shlen_div. unfold ASHOFF in *. destruct PF as (_ & _ & (F1 & F2 & F3 & F4 & F5 & F6) & _).
      clear -FKO F1 F2 F3 F4 F5 F6 D_f_res RSP OFKi OFKs OFKsa OFKsb. Z.div_mod_to_equations. dlia. }
    destruct SHF as (SF1 & SF2 & SF3 & SF4 & SF5).
    unfold AMALLOC_STACK, AINSTANCE in *. destruct PF as (PF1 & PF2 & PF3 & PF4).
    repeat (apply Forall_cons; [cbn [fst snd];
      clear -LO BOT STK3 SP47 STK2 OT FKO ORS RSP ODT D_f_res D_t_f D_d_res D_t_d C16 PF3 PF4 SF1 SF2 SF3 SF4 SF5 SHHI TL1 TBND TBNDa TBNDb TIMG TIMGa TIMGb OFKi OFKs OFKsa OFKsb DBND DBNDa DBNDb DIMG DIMGa DIMGb;
      repeat (split; [lia|]); lia |]).
    apply Forall_nil. }

  eapply evtF_mono.
  { eapply (aligned_tail_gen16 DI L RNG1 ra sp gp tp spA t0d t1d t2d a1d a2d a3d a4d a5d a6d a7d t3d t4d t5d t6d
              s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0A s1A s2A s3A s4A s5A s6A sp (Z_to_bv 64 n) (Z_to_bv 64 16) F fc m1
              n (al_t L) c cnt AB UB PG room lo b0 b1 szh szl ctxj (1 + Z.of_nat (length trc))
              (Z_to_bv 64 (max_count st_pre c)) (Z_to_bv 64 S) stj1 j1 j2 (Z_to_bv 8 250) sj' sjunk uj fr0 junk0 junk2 tb trc).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => exact ST1
         | |- mem_inv _ _ => exact MI1
         | |- allocA_cells _ _ _ => unfold allocA_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end)
         | |- poison_cells _ => unfold poison_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end)
         | |- ADEPOT _ _ _ => exact DEP1
         | |- In _ _ => exact TRU
         | |- u64arr _ _ (_ + 2800) _ => exact STATS'
         | |- u64arr _ _ _ _ => exact TB
         | |- map _ _ = _ => exact TRF
         | |- (16 < _) -> _ => exact LH1
         | |- ~ _ -> rng _ _ _ => exact RSPf
         | |- ~ _ -> _ => exact SHP1
         | |- is_primary16 _ = _ => exact PRIM
         end.
    all: try lazymatch goal with
         | |- rw_cells _ _ (_ + -16) _ => exact HDR
         | |- rw_cells _ _ (shad _) [C1 _] => exact SHA
         | |- rw_cells _ _ (shad _) [CB _ _] => exact SHU
         | |- rw_cells _ _ _ [CB _ _] => exact UJ
         | |- rw_cells _ _ (_ + 2784) _ => exact STS1
         | |- rw_cells _ _ (_ + 208 + _ * 80) _ => exact CR1
         | |- rw_cells _ _ _ _ => assumption
         | |- rng _ _ _ => assumption
         | |- _ \/ _ => first [exact DJT | exact DJN | exact DJS | exact DJC4 | unboxed CL5 | unboxed DL7 | unboxed DL8 | unboxed DL9 | unboxed DL10]
         | |- @eq Z _ _ => first [assumption | reflexivity | exact PGE | subst room; reflexivity]
         | |- @eq word _ _ => first [assumption | reflexivity]
         | |- @eq nat _ _ => first [exact LSJ' | exact LTB | assumption]
         end.
    all: try assumption.
    all: try (generalize N NR LO BOT SP47 STK1 STK2 STK3 SP1 SP2 SP4 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6
                         G1 G2 G3 G4 G5 EUB ES SM16 NSZ NS RSR RZR GR3 GR7 GR8 GR9 SB3 SB4 B1 POS HCNT CNT16 KS0 KS1 HC0 C16 LTRC RA4 HspA;
              clear; intros; rewrite ?HC0 in *; unfold AIMG_HI, AMALLOC_STACK, AREQMAX, UDEPTH, K_SPACE_SIZE, K_SPACE_EXTRA in *; lia).
    all: try (eapply rng_sub'; [exact RSTK1|]; clear -LO SP47 BOT STK3 SPR; unfold AMALLOC_STACK in *; lia).
    all: try (clear -LTRC; lia).
    all: match goal with |- ?G => idtac "REMT" G end. }

  cbv beta. intros ms' PM.
  unfold amalloc_post_x. cbn [snd fst]. split.
  {
    pose proof PM as PM0. unfold aligned_post_gen16 in PM0.
    destruct PM0 as (id0 & t0e & t1e & t2e & a1e & a2e & a3e & a4e & a5e & a6e & a7e & t3e & t4e & t5e & t6e & m5 & sj5 & stj5 & EMS & MUt & _).

    assert (AXFall : axflags L st_pre m_pre).
    { intros c' Hc' NC'. destruct (Z.eq_dec c' c) as [->|NE]; [exact (AXFp NC')|].
      pose proof (C6F4 c' Hc' NC') as F4. unfold axflag in *.
      replace (exh_mem c' st_pre) with (exh_mem c' st)
        by (destruct EXHp as [E|E]; [symmetry; apply exh_mem_eq_list; exact E| rewrite (exh_mem_eq_list c' _ _ E); symmetry; apply exh_mem_clear_other; exact NE]).
      eapply cells_frameO; [exact F4| exact MUc|]. cbn [cells_size csize Nat.add]. intros x Hx. cbn [outside].
      assert (RIEj : forall j, aregion_info L j = al_space_beg L + 137438953472 + j * 128) by (intros j; unfold aregion_info, K_SPACE_SIZE, ARI_STRIDE; change (2^37) with 137438953472; reflexivity).
      rewrite (RIEj c') in Hx. rewrite (RIEj c). unfold aregion, K_REGION, AINSTANCE, K_NUM_CLASSES in *. change (2^32) with 4294967296.
      pose proof atop_range as ATRx.
      assert (SHT : shad (al_space_beg L + c * 4294967296) + shlen 4294967296 <= 17594333495296)
        by (rewrite shad_div, shlen_div; unfold ASHOFF, K_SPACE_SIZE, K_SPACE_EXTRA in *; change (2^37) with 137438953472 in *; clear -SP1 SP2 C16 ATRx; Z.div_mod_to_equations; lia).
      rewrite ?unsigned_lit by (clear -SPR HspA LO BOT STK3; lia).
      pose proof TSP as TSPx. unbox TSPx.
      unfold K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^37) with 137438953472 in *.
      clear -Hx Hc' NE C16 SP1 SP2 TL1 TL2 TL4 LO BOT STK3 HspA SHT A1 A2 ATRx SPR TSPx. unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in *. repeat split; lia. }
    destruct (c6_frame L RESV RNG1 st_pre m_pre m1 _ ALO ROK AXGp AXFall MU1) as [G1x F1x].
    { rewrite ?unsigned_lit by (clear -SPR HspA LO BOT STK3; lia).
      apply Forall_cons; [unfold c6_piece; cbn [fst snd]; intros _; left; clear -LO BOT STK3 HspA; lia|].
      apply Forall_cons; [unfold c6_piece, acache_addr; cbn [fst snd]; intros _; right; left; clear -C16; lia|].
      apply Forall_cons; [unfold c6_piece; cbn [fst snd]; intros _; right; left; clear; lia| apply Forall_nil]. }
    destruct (c6_frame L RESV RNG1 st_pre m1 m5 _ ALO ROK G1x F1x MUt) as [G5x F5x].
    { pose proof (ao_res L ALO) as (_ & _ & ORSx & _). pose proof (ao_space L ALO) as RSPx. pose proof atop_range as ATRx.
      assert (UBN : UB + n <= AB + S) by (clear -EUB NS NSZ RSR ES; lia).
      repeat (apply Forall_cons; [unfold c6_piece; cbn [fst snd]; intros NEk;
        first [ left; clear -LO BOT; lia
              | right; left; clear -C16; lia
              | do 2 right; left; clear -G1 G2 EUB UBN RSPx RZR SZB ES; subst S; lia
              | do 3 right; left; clear -NEk GR3 GR4 GR5 GR6 GR7 GR8 GR9 PGE SB3; subst g grz; lia
              | do 5 right; left; clear; lia
              | do 6 right; left; clear; lia
              | do 7 right; left; clear; lia ]|]).
      apply Forall_nil. }
    rewrite EMS. unfold c6_at. cbn [ms_mem MS].
    destruct G5x as (XC5 & EC5 & ER5 & ECL5).
    split.
    - split; [exact XC5|]. split; [exact EC5|]. split; [exact ER5|].
      eapply (emb_clr_sub RESV st_pre); [reflexivity| | exact ECL5].
      apply (achunks_new_prim st_pre _ (a_next (apop c st_pre)) c n); reflexivity.
    - intros c' Hc' NC'. exact (F5x c' Hc' NC'). }
  unfold apop. rewrite HCNT, !a_next_put_cls, !a_live_put_cls.
  apply (aligned_post_gen16_shift DI L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc n (al_t L) c cnt AB UB PG room lo b1 _ _ uj m_pre m1 ms') in PM;
    [| eapply munch_weaken; [| exact MU1]; unfold sub_fp, acache_addr; cbn [outside]; intros q Hq; clear -Hq HspA; lia | exact WM1].
  cbv delta [PG g grz room] in PM, SHpre, SHsuf. subst UB. subst AB.
  eapply (amalloc_post_shiftG CI _ L RNG RNG1 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st st_pre LB n lo m m_pre); [| exact FPLE |].
  { eapply (store_prim16 DI AQ ASEC AFK HL CI CI_OK L RNG1 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m_pre st_pre LB X_pre n lo c cnt k b1
              (Z_to_bv 64 (max_count st_pre c)) (Z_to_bv 64 (size_of_class c)) uj).
    all: try exact PM.
    all: try lazymatch goal with
         | |- is_primary16 _ = _ => exact PRIM
         | |- ann_ov _ = None => rewrite L2; exact OVF
         | |- alayout_ok _ => exact ALO
         | |- arng _ _ _ => exact ARNGp0
         | |- AFK _ _ _ => idtac
         | |- AREP _ _ _ _ _ => exact ARp
         | |- ablocks _ _ _ _ => eapply ablocks_xbusyG; [exact BL | exact XB | exact L1]
         | |- nth_error _ _ = _ => exact NK
         | |- busy_of _ _ _ = _ => exact NB
         | |- (16 < _) -> _ => let R16 := fresh in intros R16; exact (proj2 (LH R16))
         | |- junk_at _ (_ + 2768) _ => exact CSa
         | |- junk_at _ (_ + 2792) _ => exact CSc
         | |- junk_at _ _ _ => first [exact TL | rewrite ES; exact TL]
         | |- fill_at _ (_ + 1) _ _ => exact SHpre
         | |- fill_at _ _ _ _ => first [exact SHsuf | rewrite ES; exact SHsuf]
         end.
    all: try assumption.
    all: try reflexivity.
    all: try (generalize N KR B1 LO BOT STK3 POS; clear; intros; unfold AMALLOC_STACK in *; lia).
    all: try exact HFKp.
    all: match goal with |- ?G => idtac "REMS" G end. }
  exact PRES.
Qed.
End S.
End CANSEC1.
End AAlignedPG_x.

Module AAllocatePG_x.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Exec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Tac. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ITreeA. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.SysStepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABytes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ASecFacts. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AMalloc_iface. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ADepot_iface. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARep. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ALayout. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AHeapP. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepKit. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepFrame. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepExt. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepExt2. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit2. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AModelFacts. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.APrimFacts.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apoison.F_apoison.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc1.F_aalloc1.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc2.F_aalloc2. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_amalloc_icpt.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_amalloc_pre.F_amalloc_pre.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc2.F_aalloc2g.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc3.F_aalloc3g.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aaligned_tail.F_amalloc_tailg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_amalloc_arep.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepStore.ARepStore.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepStore.ARepStoreG. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARefill_iface.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARefillP.ARefillP.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ACallocG.ACallocG.
 Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc1.F_aalloc1b.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aaligned_tail.F_aallocate_tailg.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AAlignedPG.AMallocPG.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

 Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AAlignedPG.AMallocPG. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AEmbRep. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFrameD. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AEmbFrame.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_arefill.F_arefill_x. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARefill_iface_x. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARefillP_x.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARefillP.ARefillP_e. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_acache_x.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ACallocG.ACallocG_x. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_amalloc_null. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ANullKit. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AC6Frame. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ANullPres. Import AMallocPG_x.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSECX0. Context {rc : runConstT} {ov : annOV}.
Definition aallocate_post_x (CI : list (Z * Z)) (AHEAP : alayout -> footprint -> astate -> list ablock -> amem -> Prop)
    (L : alayout) (RESV : list (Z * Z)) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (n lo : Z) (m : amem)
    (r : astate * option aptr) (RNG' : footprint) : machine_state -> Prop :=
  fun ms' => c6_at RESV L RNG' (fst r) ms' /\
    match snd r with
    | Some _ => amalloc_post CI AHEAP L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB n lo m r RNG' ms'
    | None => fp_le RNG RNG' /\ exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (ret_pc ra) fc None m' (seg_rom asegs)
        /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
        /\ aheap_pres CI LB (bv_unsigned sp) m m'
        /\ AHEAP L RNG' (fst r) LB m'
    end.
End CANSECX0.

Section CANSEC1. Context {rc : runConstT} {ov : annOV}.

Local Lemma ablk_int : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6483968 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
Local Lemma aobj_int : forall a n, aobj a n -> 0x10000 <= n ->
  6483968 <= a /\ a + n <= ATOP /\ exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof.
  intros a n H Hn. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. destruct H as (H1 & H2 & H3 & H4 & H5).
  split; [lia|]. split; [lia|]. destruct H4; [exists 0 | exists 1]; lia.
Qed.
Local Lemma aobj4_int : forall a, aobj a 4096 ->
  4096 <= a /\ a + 4096 <= ATOP
  /\ (exists k, 0 <= k <= 1 /\ a + 4096 <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a)
  /\ (exists j, 0 <= j <= 1 /\ a + 4096 <= 65536 + j * 18446744073709551616 /\ 6483968 * j <= a).
Proof.
  intros a H. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. destruct H as (H1 & H2 & H3 & H4 & H5).
  split; [lia|]. split; [lia|]. split; [destruct H4; [exists 0 | exists 1]; lia | destruct H5 as [_ [H5|H5]]; [exists 0 | exists 1]; lia].
Qed.

Local Ltac dlia := repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
Section S.
Variable DI : ADepotIface.
Variables (AQ ASEC : alayout -> astate -> aconc -> amem -> Prop) (AFK : alayout -> list ablock -> amem -> Prop).
Hypothesis HL : ahole_laws (AH DI AQ ASEC AFK).
Hypothesis HLD : ahole_lawsD (AH DI AQ ASEC AFK).
Hypothesis EXHW : exh_first_stmt.
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI) CI.

Hypothesis CI_OK2 : Forall (fun iv => snd iv <= AINSTANCE \/ AINSTANCE + 728 <= fst iv) CI.

Hypothesis CI_OK3 : Forall (fun iv => (snd iv <= AEMB \/ AEMB + 56 <= fst iv) /\ (snd iv <= 0x15bd20 \/ 0x15bd21 <= fst iv)) CI.

Theorem aallocate_prim_x : forall (L : alayout) (RNG : footprint)
    (ra spA gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (n lo SO pc : Z) (trc : list Z) (tb : list word) (RESV : list (Z * Z)),
  ann_ov (a_next st) = None ->

  is_primary n = true ->
  AHEAP_P (AH DI AQ ASEC AFK) L RNG st LB m ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned spA) -> ATOP + 4096 <= lo -> lo <= bv_unsigned spA - AMALLOC_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 AINSTANCE -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 8 -> a3 = Z_to_bv 64 SO -> a4 = Z_to_bv 64 1 -> a5 = Z_to_bv 64 1 ->
  1 <= n <= AREQMAX ->

  rw_cells asegs m SO [C8 (Z_to_bv 64 (SO + 16)); C8 (Z_to_bv 64 (1 + Z.of_nat (length trc)))] ->
  u64arr asegs m (SO + 16) tb -> length tb = 255%nat ->
  map bv_unsigned (firstn (Datatypes.S (length trc)) tb) = pc :: trc ->
  In (pc :: trc) (al_U L) -> (length trc <= 29)%nat ->
  bv_unsigned spA <= SO -> SO + 2056 <= 2^47 -> bv_unsigned spA + 2144 < 2^47 -> rng RNG SO 2056 ->
  rng RNG lo (bv_unsigned spA - lo) ->
  aresv_ok L RESV ->

  bv_unsigned fc < 32 -> axg RESV RNG st m -> axflags L st m -> (let '(_, cap0, _) := a_emb st in cap0 <= 2 ^ 23) ->
  implS asegs RNG (aembed ATOP (amalloc ATOP RESV st n))
        (epostF (aallocate_post_x CI (AHEAP_P (AH DI AQ ASEC AFK)) L RESV RNG ra spA gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB n lo m))
        (MS (mkR ra spA gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 allocate_entry) fc None m (seg_rom asegs)).
Proof.
  intros until RESV. intros OVF PRIM AHP MI STA BOT LOA TP Ha0 Ha1 Ha2 Ha3 Ha4 Ha5 NR SS TB LTB TRF TRU LTRC SPS STOP SPV RS RSTKA ROK FC C6G C6F CAPB.
  assert (N : 1 <= n <= AREQMAX) by exact NR. assert (N1 : 1 <= n) by (clear -NR; lia).

  assert (EXSP : exists sp : word, bv_unsigned spA = bv_unsigned sp - 2144).
  { exists (Z_to_bv 64 (bv_unsigned spA + 2144)). rewrite unsigned_lit; [lia|]. pose proof (bv_unsigned_in_range 64 spA) as R. unfold bv_modulus in R. clear -R SPV. lia. }
  destruct EXSP as [sp HspA].
  assert (LO : lo <= bv_unsigned sp - 4608) by (unfold AMALLOC_STACK in *; clear -LOA HspA; lia).
  assert (SP47 : bv_unsigned sp < 2^47) by (clear -SPV HspA; lia).
  assert (RSTK : rng RNG lo (bv_unsigned spA - lo)) by exact RSTKA.
  assert (S64 : 0 < SO < 2^64) by (atop_facts; clear -SPS STOP LOA BOT; unfold AMALLOC_STACK in *; lia).
  destruct AHP as (ALO & ARNG & [X [AR BL]] & HFK).
  remember (class_id (needed_size n)) as c eqn:HC0. symmetry in HC0.
  pose proof (prim_facts n N1 PRIM) as (NS & RZR & RZE & RZM & RLR & RSR & RSM & NSR).
  pose proof (prim_class_facts n c N1 PRIM HC0) as (C16 & NSZ & SM16 & SMALL & MCB). clear SMALL.
  pose proof (cls_facts c C16) as (SZB & _ & _ & _).
  assert (HCK : 1 <= c < K_NUM_CLASSES) by (unfold K_NUM_CLASSES; clear -C16; lia).
  assert (NM8 : needed_size n mod 8 = 0) by (rewrite NS; clear -RSM RZM; Z.div_mod_to_equations; lia).

  pose proof AR as AR0. destruct AR0 as (WF & RT & INST & THR & CLS & HQ & HS & HD & HRO & RT2 & AVL & RT3).
  destruct THR as (T0 & T40 & CACHES & CSTATS & [sj [STATS LSJ]] & UNW).
  pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVE & FRESH & UNIQ).
  destruct (PERC c HCK) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & LENF & LENC & CNTB & ND & RANGE).
  pose proof (alayout_space L ALO) as (SP1 & SP2 & SP3 & SP4).
  pose proof (alayout_t L ALO) as (TL1 & TL2 & TL3 & TL4).
  pose proof (alayout_ctx L ALO) as (CL1 & CL2 & CL3 & CL4 & CL5).
  pose proof (alayout_depot L ALO) as (DL1 & DL2 & DL3 & DL4 & DL5 & DL6 & DL7 & DL8 & DL9 & DL10).
  pose proof (aobj4_int _ (ao_t L ALO)) as (_ & _ & (kT & TBND & TBNDa & TBNDb) & (jT & TIMG & TIMGa & TIMGb)).
  pose proof (aobj_int _ _ (ao_ctx L ALO) ltac:(clear; lia)) as (CTXi & _ & (kC & CBND & CBNDa & CBNDb)).
  pose proof (aobj_int _ _ (ao_nodes L ALO) ltac:(clear; lia)) as (NODi & _ & (kN & NBND & NBNDa & NBNDb)).
  pose proof (aobj_int _ _ (ao_store L ALO) ltac:(clear; lia)) as (STOi & _ & (kR & SBND & SBNDa & SBNDb)).
  pose proof (aobj_int _ _ (ao_fake L ALO) ltac:(clear; lia)) as (OFKi & _ & (kF & OFKs & OFKsa & OFKsb)).
  pose proof (aobj4_int _ (ao_dtls L ALO)) as (_ & _ & (kD & DBND & DBNDa & DBNDb) & (jD & DIMG & DIMGa & DIMGb)).
  pose proof (alayout_stack L ALO) as (STK1 & STK2 & STK3).
  pose proof (alayout_res_disj L ALO) as [SCX TSP].
  pose proof RT as RT0.
  destruct RT0 as (GPG & GOT & GOT80 & RIC & LS1 & REAL & IMAX4 & FLG5 & FLG & HPP & SHB & CANP & TI & TK & INI2 & LAY & MCS & OOM3
                    & PGC & HK2 & CF8 & CF34 & CSMT & T88 & TSD & LS2 & CT8 & CT).
  pose proof INI2 as INI. rw_split INI 1%nat INI1 INIx. clear INIx.
  destruct OOM3 as [oomb OOM]. rw_split OOM 2%nat OOMx RSS. clear OOMx.
  pose proof IMAX4 as IMAX. rw_split IMAX 3%nat IMAX3 IMAXx. clear IMAXx.
  pose proof T0 as TT0. rw_split TT0 1%nat TTctx TT.
  pose proof ARNG as ARNG0. destruct ARNG as (RIMG & RT4 & RCTX & RNO & RSTO & RRI & RFK & RSFK & RDTLS & RCLS).
  assert (RCTX4 : rng RNG (al_ctx L) 4096) by (eapply rng_sub'; [exact RCTX|]; clear; lia).
  word_range sp SPR.
  box CL5. box DL7. box DL8. box DL9. box DL10. box TSP. box SCX.

  rewrite (amalloc_prim_eq RESV st n c N1 PRIM HC0).

  iprefix. eapply evtF_cut.
  { eapply (allocA_pre_spec RNG ra spA gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n SO (al_ctx L) (al_t L) lo).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => exact STA
         | |- mem_inv _ _ => exact MI
         | |- allocA_cells _ _ _ => unfold allocA_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end)
         | |- _ \/ _ => unboxed CL5
         | |- @eq word _ _ => first [exact TP | exact Ha0 | exact Ha1 | exact Ha2 | exact Ha3 | exact Ha4 | exact Ha5]
         | |- is_primary _ = _ => exact PRIM
         | |- 0 < _ < _ => exact S64
         end.
    all: try lazymatch goal with
         | |- rw_cells _ _ _ _ => assumption
         | |- rng _ _ _ => assumption
         end.
    all: try assumption.
    all: try (generalize N NR LO LOA HspA BOT SP47 STK1 STK2 STK3 SP1 SP2 SP4 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 LTRC;
              clear; intros; unfold AIMG_HI, AMALLOC_STACK, AREQMAX, UDEPTH in *; lia).
    all: match goal with |- ?G => idtac "REMPRE" G end. }
  cbv beta. intros ms4 P4. unfold allocA_pre_post in P4.
  destruct P4 as (t0c & t1c & t2c & a4c & a5c & a6c & a7c & t3c & t4c & t5c & t6c & m4 & -> & MU4 & WM4 & MI4 & ST4 & [fr0 FRa]).
  apply evtF_done.
  replace (bv_unsigned spA - 128) with (bv_unsigned sp - 2272) in ST4, FRa by (clear -HspA; lia).

  pose proof UNW as UW4.
  xport UW4 MU4 WM4 ltac:(clear -HspA SPR LO BOT STK3 TL1 TL2; unfold AMALLOC_STACK in *; lia).
  xport SS MU4 WM4 ltac:(clear -HspA SPS STOP SPR; lia).
  xport TB MU4 WM4 ltac:(rewrite LTB; clear -HspA SPS STOP SPR; lia).
  assert (AR4 : AREP (AH DI AQ ASEC AFK) L st X m4).
  { eapply (AREP_frame_pre _ HL L st X m m4); [exact ALO | exact AR | exact MU4 | exact WM4 | | exact UW4].
    apply Forall_cons; [unfold apre; cbn [fst snd]; intros _; left; unfold AMALLOC_STACK in *; clear -HspA LO BOT STK3; lia| apply Forall_nil]. }

  destruct (c6_frame L RESV RNG st m m4 _ ALO ROK C6G C6F MU4) as [C6G4 C6F4].
  { apply Forall_cons; [unfold c6_piece; cbn [fst snd]; intros _; left; unfold AMALLOC_STACK in *; clear -HspA LO BOT STK3; lia| apply Forall_nil]. }

  eapply (@calloc_arep_gen_x _ _ _ HL HLD _ RESV _ _ L RNG _ _ gp tp t0c t1c t2c _ _ _ _ _ _ a4c a5c a6c a7c _ _ _ _ _ _ _ _ _ _ t3c t4c t5c t6c F fc m4 st X c lo (needed_size n)
            ALO ARNG0 AR4 MI4).
  all: try lazymatch goal with
       | |- arng _ _ _ => exact ARNG0
       | |- stk _ _ _ _ => rewrite unsigned_lit by (clear -SPR HspA LO BOT STK3; unfold AMALLOC_STACK in *; lia);
                           replace (bv_unsigned spA + -128) with (bv_unsigned sp - 2272) by (clear -HspA; lia); exact ST4
       | |- ATOP <= _ => clear -LO BOT STK3; unfold AMALLOC_STACK in *; lia
       | |- _ <= bv_unsigned _ - _ => rewrite unsigned_lit by (clear -SPR HspA LO BOT STK3; unfold AMALLOC_STACK in *; lia);
                                    clear -LO HspA BOT STK3; unfold AMALLOC_STACK in *; lia
       | |- @eq word _ _ => first [exact TP | reflexivity]
       | |- 16 <= _ <= 65536 => clear -NSR; lia
       | |- _ mod 8 = 0 => exact NM8
       | |- class_id _ = _ => exact HC0
       | |- rng _ _ _ => rewrite unsigned_lit by (clear -SPR HspA LO BOT STK3; unfold AMALLOC_STACK in *; lia);
                         eapply rng_sub'; [exact RSTK|]; clear -LO HspA SP47 BOT STK3; unfold AMALLOC_STACK in *; lia
       | |- exh_first_stmt => exact EXHW
       | |- aresv_ok _ _ => exact ROK
       | |- bv_unsigned _ < 2 ^ 63 => rewrite unsigned_lit by (clear -SPR HspA LO BOT STK3; unfold AMALLOC_STACK in *; lia); clear -SP47 HspA; lia
       | |- bv_unsigned _ < 32 => exact FC
       | |- _ -> axflag _ _ _ _ => intros NC24x; exact (C6F4 c HCK NC24x)
       | |- axg _ _ _ _ => exact C6G4
       | |- context [a_emb _] => exact CAPB
       | |- forall _, _ => idtac
       end.
  1: {
       intros st2 RNG' ms' RF. unfold aret_xf in RF. cbv zeta in RF. pose proof atop_range as ATR.
       pose proof C6G4 as (_ & ECp & _ & ECLp). unfold emb_cells in ECp. unfold emb_clr in ECLp.
       destruct (a_emb st) as [[d0 cap0] sz0] eqn:EA. destruct (a_emb st2) as [[d2 cap2] sz2] eqn:EA2.
       destruct RF as (FPLE & t0r & t1r & t2r & a1r & a2r & a3r & a4r & a5r & a6r & a7r & t3r & t4r & t5r & t6r & mr
                       & -> & MIr & STr & STEQ & ARr & ARNGr & AXFr & AXGr & (d1 & cap1 & MUr & PV1 & PV2 & TOP1)).
       assert (USP : bv_unsigned (Z_to_bv 64 (bv_unsigned spA + -128)) = bv_unsigned sp - 2272)
         by (rewrite unsigned_lit by (clear -SPR HspA LO BOT ATR; lia); clear -HspA; lia).
       rewrite USP in MUr, STr.

       assert (B0 : bufok RESV st d0 cap0).
       { unfold bufok. destruct (Z.eqb_spec cap0 0) as [E0|NZ]; [left; lia|]. right.
         destruct ECp as (_ & _ & _ & _ & _ & _ & _ & _ & TOP & _). split; [exact TOP|]. destruct ECLp as [Q|Q]; [exfalso; exact (NZ Q)| exact Q]. }
       assert (B1 : bufok RESV st d1 cap1).
       { destruct (Z_le_gt_dec cap1 0) as [LE|GT]; [left; exact LE|]. destruct PV1 as [[E1 E2]|AV]; [rewrite E1, E2; exact B0|].
         right. split; [destruct TOP1 as [Q|Q]; [lia| exact Q]| exact AV]. }
       assert (B2 : bufok RESV st d2 cap2).
       { destruct PV2 as [[E1 E2]|AV]; [rewrite E1, E2; exact B0|].
         pose proof AXGr as (_ & EC2 & _). unfold emb_cells in EC2. rewrite EA2 in EC2. destruct (Z.eqb_spec cap2 0) as [E0|NZ]; [left; lia|]. right.
         destruct EC2 as (_ & _ & _ & _ & _ & _ & _ & _ & TOP & _). split; [exact TOP| exact AV]. }

       set (SPc := bv_unsigned sp - 2272) in *.
       assert (SPHIc : ATOP <= SPc) by (subst SPc; clear -LO BOT; lia).
       assert (SPHI : ATOP <= bv_unsigned spA) by (clear -LO BOT HspA; lia).
       set (Wf := [(SPc - 2096, SPc); (al_t L + 208, al_t L + 2768); (aregion_info L c, aregion_info L c + 8);
                   (aregion_info L c + 68, aregion_info L c + 69); (AEMB, AEMB + 56); (d0, d0 + cap0); (d1, d1 + cap1); (d2, d2 + cap2)]%Z).
       change (munch Wf m4 mr) in MUr.
       assert (PCSfA : Forall (nf_pieceA L RESV st SPc c) Wf).
       { assert (BK : forall d cap, bufok RESV st d cap -> nf_pieceA L RESV st SPc c (d, d + cap)).
         { intros d cap [B|[Bt Ba]] LT; cbn [fst snd] in LT; [lia|]. unfold nf_kindA, nf_kind. cbn [fst snd].
           replace (d + cap - d) with cap by lia. split; [do 4 right; left; split; assumption|]. right; right. split; [exact Bt|].
           unfold avoids_all in *. rewrite forallb_app in Ba. apply andb_prop in Ba as [Ba _]. exact Ba. }
         subst Wf. repeat (apply Forall_cons); try apply Forall_nil; try (apply BK; assumption); intros _; unfold nf_kindA, nf_kind; cbn [fst snd].
         - split; [left; subst SPc; clear -LO BOT; lia| right; left; subst SPc; unfold AERRNO, ATP; clear -LO BOT ATR; lia].
         - split; [right; left; clear; lia| unfold AERRNO, ATP; clear -TIMG TIMGa TIMGb; lia].
         - split; [right; right; left; clear; lia| right; left; unfold aregion_info, K_SPACE_SIZE, ARI_STRIDE, AERRNO, ATP; change (2^37) with 137438953472; clear -SP1 C16; lia].
         - split; [right; right; left; clear; lia| right; left; unfold aregion_info, K_SPACE_SIZE, ARI_STRIDE, AERRNO, ATP; change (2^37) with 137438953472; clear -SP1 C16; lia].
         - split; [right; right; right; left; clear; lia| left; unfold AEMB, AERRNO, ATP; clear; lia]. }
       pose proof (nf_pieceA_piece _ _ _ _ _ _ PCSfA) as PCSf.
       assert (OUTS : forall x, SPc <= x -> outside Wf x)
         by (intros x Hx; apply (nf_outside L RESV st SPc c ALO ROK HCK SPHIc Wf x PCSf); left; exact Hx).

       assert (FRar : rw_cells asegs mr (bv_unsigned spA + -128)
                        [CB 8 fr0; C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 16); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5;
                         C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
       { replace (bv_unsigned spA + -128) with (bv_unsigned sp - 2272) by (clear -HspA; lia).
         eapply cells_frameO; [exact FRa| exact MUr|]. intros x Hx. apply OUTS. subst SPc. clear -Hx. lia. }
       pose proof ARr as (_ & RTr & _).
       destruct RTr as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & OOM3r & _).
       destruct OOM3r as [oombr OOMr]. rw_split OOMr 2%nat OOMxr RSSr. clear RSSr.

       apply implS_ret.
       replace (ret_pc (Z_to_bv 64 0x3cf68)) with (Z_to_bv 64 0x3cf68) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
       pose proof ARNGr as (RIMGr & _).
       assert (RSTKr : rng RNG' lo (bv_unsigned spA - lo)) by (eapply rng_fp_leG; [exact FPLE | exact RSTK]).
       eapply evtF_mono.
       { eapply (allocN_spec RNG' spA gp tp t0r t1r t2r _ _ a1r a2r a3r a4r a5r a6r a7r _ _ _ _ _ _ _ _ _ _ t3r t4r t5r t6r
                   s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra _ _ fr0 oombr F fc mr lo);
           first [ exact FRar | exact MIr | exact OOMxr | exact RIMGr | exact RSTKr
                 | replace (bv_unsigned spA + -128) with (bv_unsigned sp - 2272) by (clear -HspA; lia); exact STr
                 | clear -BOT ATR; lia
                 | clear -LO HspA; lia ]. }
       cbv beta. intros ms1 P1.
       destruct P1 as (t0n & t1n & t2n & a1n & a2n & a3n & a4n & a5n & a6n & a7n & t3n & t4n & t5n & t6n & m1 & -> & MU1 & WM1 & MI1 & ST1 & OOM1).

       assert (AXFSr : axflags L st2 mr).
       { intros c' Hc' NC'. destruct (Z.eq_dec c' c) as [->|NE]; [exact AXFr|].
         pose proof (C6F4 c' Hc' NC') as F4. unfold axflag in *.
         assert (EXE : exh_mem c' st2 = exh_mem c' st).
         { destruct STEQ as [[_ ->]|[_ [e2 ->]]]; [apply init_cache_exh|]. rewrite exh_mem_set_emb, (exh_mem_set_other c c' _ NE). apply init_cache_exh. }
         rewrite EXE. eapply cells_frameO; [exact F4| exact MUr|]. cbn [cells_size csize Nat.add]. intros x Hx.
         apply (nf_flag_outside L RESV st SPc c ALO ROK HCK SPHIc Wf c' x PCSf Hc' NE). clear -Hx. lia. }
       destruct (c6_frame L RESV RNG' st2 mr m1 _ ALO ROK AXGr AXFSr MU1) as [C6G2 C6F2].
       { apply Forall_cons; [unfold c6_piece, AOOM; cbn [fst snd]; intros _; do 8 right; left; clear; lia| apply Forall_nil]. }

       assert (AR2 : AREP (AH DI AQ ASEC AFK) L st2 X m1).
       { eapply (AREP_frame_null _ HL L st2 X mr m1 (bv_unsigned sp) ALO ARr); [| exact WM1| clear -LO BOT; lia| exists (Z_to_bv 8 1); exact OOM1].
         eapply munch_weaken; [| exact MU1]. unfold sub_fp, AOOM. cbn [outside]. intros q Hq. clear -Hq. split; [lia| exact I]. }
       assert (LIVE2 : a_live st2 = a_live st).
       { pose proof (init_cache_fields st) as (E1 & _). destruct STEQ as [[_ ->]|[_ [e2 ->]]]; [exact E1|]. rewrite <- E1. destruct (init_cache st); reflexivity. }
       pose proof (ablocks_same L st st2 X X LB BL eq_refl LIVE2) as BL2.
       pose proof (munch_app _ _ _ _ _ MU4 (munch_app _ _ _ _ _ MUr MU1)) as MUt.
       assert (PCSt : Forall (nf_pieceA L RESV st (bv_unsigned spA) c)
                        ([(bv_unsigned spA - 176, bv_unsigned spA)] ++ Wf ++ [(AOOM, AOOM + 1)])%Z).
       { apply Forall_app. split; [| apply Forall_app; split].
         - apply Forall_cons; [| apply Forall_nil]. intros _. unfold nf_kindA, nf_kind. cbn [fst snd].
           split; [left; clear -LO BOT HspA; lia| right; left; unfold AERRNO, ATP; clear -LO BOT HspA ATR; lia].
         - eapply Forall_impl; [| exact PCSfA]. intros iv K. apply (nf_pieceA_SP L RESV st SPc (bv_unsigned spA) c iv); [subst SPc; clear -HspA; lia| exact K].
         - apply Forall_cons; [| apply Forall_nil]. intros _. unfold nf_kindA, nf_kind, AOOM. cbn [fst snd].
           split; [do 5 right; left; clear; lia| left; unfold AERRNO, ATP; clear; lia]. }
       destruct (nf_fake L RESV st (bv_unsigned spA) c _ ALO ROK HCK SPHI (nzl_pieces _ _ _ _ _ _ (nf_pieceA_piece _ _ _ _ _ _ PCSt))) as (D72 & FU & D48).
       pose proof (hfD _ HLD L LB m m1 _ HFK (munch_nzl _ _ _ MUt) D72 FU D48) as HFK2.
       assert (PRESf : aheap_pres CI LB (bv_unsigned spA) m m1).
       { intros a Ha CL.
         pose proof (nf_client_outsideA L RESV st X (bv_unsigned spA) c ALO ROK HCK SPHI CI CI_OK CI_OK3 WF LB _ a BL PCSt Ha CL) as OUT.
         assert (E : m1 (wa a) = m (wa a)) by (apply MUt; rewrite wa_unsigned by exact Ha; exact OUT).
         split; [exact E|]. intros Hw. rewrite (AFrameD.wview_agree asegs m m1 (wa a) E). exact Hw. }

       unfold aallocate_post_x. cbn [fst snd]. split.
       { unfold c6_at. cbn [ms_mem]. split; [exact C6G2| exact C6F2]. }
       split; [exact FPLE|]. do 14 eexists. exists m1. split; [reflexivity|]. split; [exact MI1|]. split; [exact ST1|]. split; [exact PRESf|].
       split; [exact ALO|]. split; [exact ARNGr|]. split; [exists X; split; [exact AR2| exact BL2]| exact HFK2]. }

  intros st_pre X_pre RNG1 m_pre cnt k ms1 CRET. destruct CRET as (CRET & EMBp & EXHp & AXFp & AXGp). unfold calloc_retG in CRET.
  destruct CRET as (FPLE & ARp & ARNGp & HCNT & POS & NK & NB & KR & XB & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & MUc & WMc & MIp
                    & t0d & t1d & t2d & a1d & a2d & a3d & a4d & a5d & a6d & a7d & t3d & t4d & t5d & t6d & m1 & stj1 & -> & MU1 & WM1 & MI1 & ST1 & CR1 & STS1).
  rewrite ?unsigned_lit in MUc by (clear -SPR HspA LO BOT STK3; unfold AMALLOC_STACK in *; lia).
  rewrite ?unsigned_lit in MU1 by (clear -SPR HspA LO BOT STK3; unfold AMALLOC_STACK in *; lia).
  rewrite ?unsigned_lit in ST1 by (clear -SPR HspA LO BOT STK3; unfold AMALLOC_STACK in *; lia).
  replace (bv_unsigned spA + -128) with (bv_unsigned sp - 2272) in ST1 by (clear -HspA; lia).
  cbn beta iota. apply implS_ret.
  replace (ret_pc (Z_to_bv 64 0x3cf68)) with (Z_to_bv 64 0x3cf68) by (symmetry; apply ret_pc_even; [lia|reflexivity]).

  pose proof ARp as AR0. destruct AR0 as (WF' & RT' & INST' & THR' & CLS' & HQ' & HS' & HD' & HRO' & RT2' & AVL' & RT3').
  destruct THR' as (T0' & T40' & CACHES' & CSTATS' & [sj' [STATS' LSJ']] & UNW').
  pose proof WF' as WF0. destruct WF0 as (SBE' & PAE' & SAL' & SLO' & SHI' & PERC' & OUTC' & BUSY' & LIVE' & FRESH' & UNIQ').
  destruct (PERC' c HCK) as (B1' & B2' & B3' & B4' & B5' & B6' & B7' & LENF' & LENC' & CNTB' & ND' & RANGE').
  destruct (kit_cache_pop _ L st_pre X_pre m_pre c cnt ARp HCK HCNT POS) as (k' & chunks & NK' & _ & _ & CR & CH & LCH & NTH & JK & FSH).
  assert (EK : k' = k) by (rewrite NK in NK'; injection NK'; intros E; symmetry; exact E). subst k'.

  set (S := size_of_class c) in *.
  set (AB := aslot_addr L c k) in *.
  assert (KSF : 0 <= k * S /\ k * S + S <= c_allocated_user (get_cls st_pre c) /\ (k * S) mod 16 = 0).
  { unfold ndist in KR. fold S in KR. fold S in SZB. fold S in SM16.
    assert (P0 : 0 <= k * S) by (clear -KR SZB; apply Z.mul_nonneg_nonneg; lia).
    assert (Q1 : k + 1 <= c_allocated_user (get_cls st_pre c) / S) by (clear -KR; lia).
    assert (M1 : (k + 1) * S <= c_allocated_user (get_cls st_pre c) / S * S) by (apply Z.mul_le_mono_nonneg_r; clear -Q1 SZB; lia).
    pose proof (Z.mul_div_le (c_allocated_user (get_cls st_pre c)) S ltac:(clear -SZB; lia)) as M2.
    split; [exact P0|]. split.
    - rewrite Z.mul_add_distr_r, Z.mul_1_l in M1. rewrite (Z.mul_comm S) in M2. clear -M1 M2 P0 SZB. lia.
    - destruct (proj1 (Z.mod_divide S 16 ltac:(clear; lia)) SM16) as [q Hq]. rewrite Hq.
      replace (k * (q * 16)) with ((k * q) * 16) by (clear; lia). apply Z_mod_mult. }
  destruct KSF as (KS0 & KS1 & KS2).
  assert (GEO : al_space_beg L <= AB /\ AB + S <= al_space_beg L + K_SPACE_SIZE /\ AB mod 16 = 0
                /\ AB + S <= aregion L c + c_allocated_user (get_cls st_pre c) /\ aregion L c <= AB).
  { subst AB. unfold aslot_addr, aregion, K_REGION, K_SPACE_SIZE, K_FREEARR_OFF, K_ALIGN in *. fold S.
    remember (k * S) as KS eqn:HKS. clear HKS.
    change (2^37) with 137438953472. change (2^32) with 4294967296 in *.
    split; [clear -KS0 C16; lia|]. split; [clear -KS1 B1' B2' C16 NSZ; lia|]. split; [| clear -KS0 KS1 B1'; lia].
    clear -SP3 C16 KS2. Z.div_mod_to_equations; lia. }
  destruct GEO as (G1 & G2 & G3 & G4 & G5). unfold K_SPACE_SIZE in G2. change (2^37) with 137438953472 in G2.
  assert (EAB : AB = aslot_addr L c k) by reflexivity. clearbody AB.
  assert (ES : S = size_of_class c) by reflexivity.

  assert (RZC : rz_size n = 16 \/ 32 <= rz_size n) by (clear -RZR RZM; Z.div_mod_to_equations; lia).
  destruct (slot_carveG m_pre AB S n (rz_size n) JK RZC ltac:(clear -N; lia) ltac:(fold S in NSZ; clear -NSZ NS RSR; lia))
    as (b0 & b1 & szh & szl & ctxj & uj & j1 & j2 & HDR & B1 & UJ & LH & TL).
  set (UB := AB + rz_size n) in *. assert (EUB : UB = AB + rz_size n) by reflexivity. clearbody UB.

  set (grz := shlen (rz_size n)). set (g := shlen (n - n mod 8)). set (room := if n mod 8 =? 0 then 0 else 1).
  assert (GR12 : grz = rz_size n / 8 /\ g = (n - n mod 8) / 8).
  { subst grz g. unfold shlen. rewrite !Z.shiftr_div_pow2 by lia. split; reflexivity. }
  destruct GR12 as [GR1 GR2].
  assert (GR3 : 2 <= grz) by (rewrite GR1; generalize RZR; clear; intros; Z.div_mod_to_equations; lia).
  assert (GR4 : 0 <= g) by (rewrite GR2; generalize N; clear; intros; Z.div_mod_to_equations; lia).
  assert (GR5 : 0 <= room <= 1) by (subst room; clear; destruct (n mod 8 =? 0); lia).
  assert (GR6 : grz + g + room <= shlen S).
  { rewrite GR1, GR2. subst room. unfold shlen. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
    fold S in NSZ. fold S in SM16. generalize NSZ NS RSR RSM SM16 RZM RZR N. clear. intros.
    destruct (Z.eqb_spec (n mod 8) 0) as [M0|M0]; Z.div_mod_to_equations; lia. }
  assert (GR7 : shad UB = shad AB + grz).
  { rewrite GR1, EUB. unfold shad, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
    generalize G3 RZM RZR. clear. intros. Z.div_mod_to_equations. lia. }
  assert (GR89 : 0x2008fff7000 <= shad AB /\ shad AB + shlen S <= 0x10007fef8000).
  { unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
    unfold K_SPACE_SIZE, K_SPACE_EXTRA in *. generalize G1 G2 SP1 SP2. clear. intros. Z.div_mod_to_equations. lia. }
  destruct GR89 as [GR8 GR9].
  destruct (shadow_carve m_pre (shad AB) (shlen S) grz g room FSH GR3 GR4 GR6 GR5) as (SHA & SHpre & [sjunk SHU] & SHP & SHsuf).
  rewrite <- GR7 in SHU, SHP, SHsuf.
  set (PG := shad UB + g) in *.

  pose proof RT' as RT0.
  destruct RT0 as (GPG' & GOT' & GOT80' & RIC' & LS1' & REAL' & IMAX4' & FLG5' & FLG' & HPP' & SHB' & CANP' & TI' & TK' & INI2' & LAY' & MCS' & OOM3'
                    & PGC' & HK2' & CF8' & CF34' & CSMT' & T88' & TSD' & LS2' & CT8' & CT').
  pose proof INI2' as INI'. rw_split INI' 1%nat INI1' INIx. clear INIx.
  destruct OOM3' as [oomb' OOM']. rw_split OOM' 2%nat OOMx RSS'. clear OOMx.
  pose proof IMAX4' as IMAX'. rw_split IMAX' 3%nat IMAX3' IMAXx. clear IMAXx.
  pose proof HK2' as HK'. rw_split HK' 1%nat HK1' HKx. clear HKx.
  pose proof T0' as TT0'. rw_split TT0' 1%nat TTctx' TT'.
  destruct (junk_split m_pre (al_t L + 2768) 16 16 CSTATS' ltac:(lia) ltac:(lia)) as [CSa CSb].
  destruct (junk_split m_pre (al_t L + 2768 + 16) 8 8 CSb ltac:(lia) ltac:(lia)) as [CS8 CSc].
  replace (al_t L + 2768 + 16) with (al_t L + 2784) in CS8 by lia.
  replace (al_t L + 2768 + 16 + 8) with (al_t L + 2792) in CSc by lia.
  destruct INST' as (I32' & I48' & I64' & I72' & I112' & I680' & I984' & I40' & I56').
  pose proof ARNGp as ARNGp0. destruct ARNGp as (RIMG' & RT4' & RCTX' & RNO' & RST' & RRI' & RFK' & RSFK' & RDTLS' & RCLS' & RPA' & RSECS' & RPSH').
  destruct (RCLS' c HCK) as (RREG & RSREG & RFA & RSFA).

  destruct (alayout_slot_disj L AB 65536 ALO G1 ltac:(unfold K_SPACE_SIZE, K_FREEARR_OFF, aregion, K_REGION in *; generalize G4 B1' B2' C16 SP1 SZB; clear; intros; change (2^37) with 137438953472; lia) ltac:(clear; lia))
    as (DJT & DJC & DJN & DJS & DJF).
  assert (RUf : rng RNG1 (UB - 16) (n + 16)) by (eapply rng_sub'; [exact RREG|]; generalize G4 G5 B1' RZR N EUB KS0 NSZ NS RSR; clear; intros; lia).
  assert (RABf : rng RNG1 AB 16) by (eapply rng_sub'; [exact RREG|]; generalize G4 G5 B1' RZR N NSZ NS RSR; clear; intros; lia).
  assert (REG8 : aregion L c mod 8 = 0 /\ c_mapped_user (get_cls st_pre c) mod 8 = 0).
  { unfold aregion, K_REGION, K_USER_MAP, K_ALIGN in *. generalize SP3 B4'; clear; intros. Z.div_mod_to_equations; lia. }
  assert (SHM : shad (aregion L c) <= shad AB /\ shad UB + g + room <= shad (aregion L c) + shlen (c_mapped_user (get_cls st_pre c))).
  { rewrite GR7, GR2, GR1. unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
    fold S in NSZ. fold S in SM16. subst room. generalize G4 G5 B1' N NSZ RSR RSM NS RZR RZM SM16 G3 EUB REG8; clear; intros.
    destruct (Z.eqb_spec (n mod 8) 0); Z.div_mod_to_equations; lia. }
  destruct SHM as [SHM1 SHM2].
  assert (RSAf : rng RNG1 (shad AB) 1) by (eapply rng_sub'; [exact RSREG|]; generalize SHM1 SHM2 GR3 GR4 GR5 GR7; clear; intros; lia).
  assert (RSUf : rng RNG1 (shad UB) (shlen (n - n mod 8))).
  { eapply rng_sub'; [exact RSREG|]. fold g. generalize SHM1 SHM2 GR3 GR4 GR5 GR7. clear. intros. lia. }
  assert (RSPf : n mod 8 <> 0 -> rng RNG1 PG 1).
  { intros NE. eapply rng_sub'; [exact RSREG|]. subst PG.
    assert (R1 : room = 1) by (subst room; generalize NE; clear; intros NE; destruct (Z.eqb_spec (n mod 8) 0); [exfalso; exact (NE ltac:(assumption)) | reflexivity]).
    rewrite R1 in SHM2. generalize SHM1 SHM2 GR3 GR4 GR7; clear; intros. lia. }
  assert (SLS : shlen S <= 8192) by (fold S in NSZ; unfold shlen; rewrite Z.shiftr_div_pow2 by (clear; lia); change (2^3) with 8; clear -NSZ; Z.div_mod_to_equations; lia).
  assert (SB34 : 0 <= shlen (n - n mod 8) <= 8192 /\ PG + 1 <= 0x10007fff8000).
  { subst PG. fold g. rewrite GR7. generalize GR4 GR6 GR9 GR3 GR5 SLS; clear; intros; lia. }
  destruct SB34 as [SB3 SB4].
  assert (RCTX4' : rng RNG1 (al_ctx L) 4096) by (eapply rng_sub'; [exact RCTX'|]; clear; lia).
  assert (DJC4 : al_ctx L + 4096 <= AB \/ AB + 65536 <= al_ctx L) by (generalize DJC; clear; intros; lia).
  assert (CNT16 : 0 < cnt <= 16).
  { unfold max_count in CNTB'. generalize POS HCNT CNTB' MCB; clear. destruct (a_cinit st_pre); intros; lia. }
  assert (PGE : PG = shad UB + shlen (n - n mod 8)) by reflexivity.
  assert (RSTK1 : rng RNG1 lo (bv_unsigned spA - lo)) by (eapply rng_fp_le; [exact FPLE | exact RSTK]).

  set (mu0 := c_mapped_user (get_cls st c)) in *.
  assert (OBJ : aregion_info L c = al_space_beg L + 137438953472 + c * 128 /\ aregion L c = al_space_beg L + c * 4294967296
                /\ shad (al_space_beg L + c * 4294967296) + 536870912 <= 17594333495296).
  { unfold aregion_info, aregion, K_REGION, K_SPACE_SIZE, ARI_STRIDE. change (2^37) with 137438953472. change (2^32) with 4294967296.
    split; [reflexivity|]. split; [reflexivity|]. rewrite shad_div. clear -SP1 SP2 C16. unfold ASHOFF, K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^37) with 137438953472 in *.
    Z.div_mod_to_equations. lia. }
  destruct OBJ as (RIE & RBE & SHHI).
  assert (MU41 : munch [(bv_unsigned sp - 3856, bv_unsigned sp - 2272); (al_t L + 208, al_t L + 3168); (AINSTANCE, AINSTANCE + 728);
                        (al_space_beg L + 137438953472 + c * 128, al_space_beg L + 137438953472 + c * 128 + 128);
                        (al_space_beg L + c * 4294967296 + mu0, al_space_beg L + c * 4294967296 + 4294967296);
                        (shad (al_space_beg L + c * 4294967296 + mu0), shad (al_space_beg L + c * 4294967296) + 536870912)]%Z m4 m1).
  { eapply munch_trans; [eapply munch_weaken; [| exact MUc] | eapply munch_weaken; [| exact MU1]];
      unfold sub_fp; cbn [outside]; intros q Hq; rewrite ?RIE, ?RBE in *; unfold K_REGION, acache_addr in *; change (2^32) with 4294967296 in *;
      rewrite ?shlen_div in *; change (4294967296 / 8) with 536870912 in *; clear -Hq HspA C16; lia. }
  assert (WM41 : wmono asegs m4 m1) by (eapply wmono_trans; [exact WMc | exact WM1]).
  unfold K_SPACE_SIZE, K_SPACE_EXTRA in SP2. change (2^37) with 137438953472 in SP2.
  xport FRa MU41 WM41 ltac:(clear -HspA SPS STOP SPR LO BOT STK3 TL1 TL2 SP1 SP2 C16 SHHI TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold AMALLOC_STACK, AINSTANCE in *; lia).
  xport SS MU41 WM41 ltac:(clear -HspA SPS STOP SPR LO BOT STK3 TL1 TL2 SP1 SP2 C16 SHHI TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold AMALLOC_STACK, AINSTANCE in *; lia).
  xport TB MU41 WM41 ltac:(rewrite LTB; clear -HspA SPS STOP SPR LO BOT STK3 TL1 TL2 SP1 SP2 C16 SHHI TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold AMALLOC_STACK, AINSTANCE in *; lia).

  xport HDR MU1 WM1 ltac:(clear -HspA DJT SPR SP2 G1 G2 EUB RZR N NSZ NS RSR LO BOT STK3 C16; unfold acache_addr, AMALLOC_STACK, K_SPACE_SIZE in *; lia).
  xport UJ MU1 WM1 ltac:(clear -HspA DJT SPR SP2 G1 G2 EUB RZR N NSZ NS RSR LO BOT STK3 C16; unfold acache_addr, AMALLOC_STACK, K_SPACE_SIZE in *; lia).
  xport SHA MU1 WM1 ltac:(cbv delta [g grz room PG] in *; clear -HspA SPR GR1 GR2 GR3 GR4 GR5 GR6 GR7 GR8 GR9 LO BOT STK3 TL1 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport SHU MU1 WM1 ltac:(cbv delta [g grz room PG] in *; clear -HspA SPR GR1 GR2 GR3 GR4 GR5 GR6 GR7 GR8 GR9 SB3 LO BOT STK3 TL1 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  assert (SHP1 : n mod 8 <> 0 -> rw_cells asegs m1 PG [C1 (Z_to_bv 8 250)]).
  { intros NE. specialize (SHP ltac:(subst room; generalize NE; clear; intros NE; destruct (Z.eqb_spec (n mod 8) 0); [exfalso; exact (NE ltac:(assumption)) | reflexivity])).
    xport SHP MU1 WM1 ltac:(cbv delta [g grz room PG] in *; clear -HspA SPR GR1 GR2 GR3 GR4 GR5 GR6 GR7 GR8 GR9 SB3 SB4 LO BOT STK3 TL1 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia). exact SHP. }
  assert (LH1 : 16 < rz_size n -> rw_cells asegs m1 AB [C8 j1; C8 j2]).
  { intros R16. pose proof (proj1 (LH R16)) as LH0.
    xport LH0 MU1 WM1 ltac:(clear -HspA DJT SPR SP2 G1 G2 EUB RZR N NSZ NS RSR LO BOT STK3 C16; unfold acache_addr, AMALLOC_STACK, K_SPACE_SIZE in *; lia). exact LH0. }
  xport GOT' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport GOT80' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport REAL' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport SHB' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport CANP' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport HPP' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport CSMT' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport FLG5' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport FLG' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport HK1' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport LS1' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport LS2' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport LAY' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport MCS' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport CF34' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport INI1' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport RSS' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport IMAX3' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport TI' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport TK' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport T88' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, ATP88, AMALLOC_STACK in *; lia).
  xport TSD' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, ATSD, AMALLOC_STACK in *; lia).
  xport CT' MU1 WM1 ltac:(ub CL5; clear -HspA Y SPR TL1 CL1 CL2 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb CTXi CBND CBNDa CBNDb; unfold acache_addr, AMALLOC_STACK, AIMG_HI in *; lia).
  xport CT8' MU1 WM1 ltac:(ub CL5; clear -HspA Y SPR TL1 CL1 CL2 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb CTXi CBND CBNDa CBNDb; unfold acache_addr, AMALLOC_STACK, AIMG_HI in *; lia).
  xport TTctx' MU1 WM1 ltac:(clear -HspA SPR TL1 TL2 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport UNW' MU1 WM1 ltac:(clear -HspA SPR TL1 TL2 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport STATS' MU1 WM1 ltac:(rewrite LSJ'; clear -HspA SPR TL1 TL2 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, ASTATS_WORDS, AMALLOC_STACK in *; lia).
  assert (DEP1 : ADEPOT DI L m1).
  { eapply (adi_frame DI); [exact HD' | exact MU1 | exact WM1 |]. unfold acache_addr.
    repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq; ub DL7; ub DL8; clear -Hq Y Y0 HspA SPR TL1 TL2 DL1 DL2 DL3 DL4 DL5 DL6 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb NODi NBND NBNDa NBNDb STOi SBND SBNDa SBNDb; unfold AMALLOC_STACK, AIMG_HI in *; lia|]).
    apply Forall_nil. }

  assert (PF : pfactsG (bv_unsigned spA) (al_t L) (al_space_beg L) c mu0 ATOP lo).
  { unfold pfactsG. pose proof (ao_t L ALO) as OT. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in OT.
    unfold AMALLOC_STACK, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN, K_FREEARR_OFF, K_USER_MAP in *. change (2^37) with 137438953472 in *.
    ub TSP. generalize LOA SPV LO BOT SP47 STK2 STK3 OT SP1 SP2 SAL C16 A1 A2 A4 Y. clear. intros.
    repeat match goal with H : _ /\ _ |- _ => destruct H end.
    repeat split; first [reflexivity | assumption | lia | Z.div_mod_to_equations; lia]. }
  assert (MUall : munch [(bv_unsigned spA - 4096, bv_unsigned spA); (al_t L + 208, al_t L + 3169); (AINSTANCE, AINSTANCE + 728);
                         (al_space_beg L + 137438953472 + c * 128, al_space_beg L + 137438953472 + c * 128 + 128);
                         (al_space_beg L + c * 4294967296 + mu0, al_space_beg L + c * 4294967296 + 4294967296);
                         (shad (al_space_beg L + c * 4294967296 + mu0), shad (al_space_beg L + c * 4294967296) + 536870912)]%Z m m_pre).
  { eapply munch_trans; [eapply munch_weaken; [| exact MU4] | eapply munch_weaken; [| exact MUc]];
      unfold sub_fp; cbn [outside]; intros q Hq; rewrite ?RIE, ?RBE in *; unfold K_REGION in *; change (2^32) with 4294967296 in *;
      rewrite ?shlen_div in *; change (4294967296 / 8) with 536870912 in *; clear -Hq HspA; lia. }
  assert (WMall : wmono asegs m m_pre) by (eapply wmono_trans; [exact WM4 | exact WMc]).

  assert (BB : forall b, In b (x_busy X) ->
      al_space_beg L <= xb_alloc L b /\ xb_alloc L b + size_of_class (xb_class b) <= al_space_beg L + 137438953472
      /\ (xb_alloc L b + size_of_class (xb_class b) <= al_space_beg L + c * 4294967296 + mu0 \/ al_space_beg L + c * 4294967296 + 4294967296 <= xb_alloc L b)).
  { intros b Hb. destruct (BUSY b Hb) as [CLB _].
    destruct (PERC (xb_class b) CLB) as (Q1 & Q2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & QR).
    pose proof (size_of_class_facts (xb_class b) CLB) as [QS _].
    assert (KB : 0 <= xb_slot b < ndist st (xb_class b)).
    { apply QR. apply in_app_iff. right. apply in_app_iff. right. unfold busy_slots. apply in_map_iff. exists b. split; [reflexivity|].
      apply filter_In. split; [exact Hb| apply Z.eqb_refl]. }
    pose proof (slot_in_region L st (xb_class b) (xb_slot b) ltac:(clear -QS; lia) (proj1 Q1) KB) as (P5 & P4 & P0).
    unfold xb_alloc. unfold K_NUM_CLASSES in CLB. unfold K_FREEARR_OFF in Q2.
    destruct (Z.eq_dec (xb_class b) c) as [EC|NC].
    - rewrite EC in P5, P4, Q1, Q2 |- *. rewrite RBE in P5, P4. change (c_mapped_user (get_cls st c)) with mu0 in Q1, Q2.
      clear -P5 P4 Q1 Q2 A1 A2 C16. unfold K_FREEARR_OFF in *. lia.
    - pose proof (region_other_geo L c (xb_class b) ALO ltac:(clear -C16; lia) CLB NC) as (R1 & R2 & R3 & _). rewrite RBE in R2.
      clear -P5 P4 Q1 Q2 R1 R2 R3 A1. lia. }
  pose proof (ao_fake L ALO) as FKO. unfold aobj in FKO. pose proof (ao_res L ALO) as ORS. unfold aobj in ORS. pose proof (ao_space L ALO) as RSP.
  pose proof (ad_fake_res L ALO) as D_f_res. pose proof (ad_t_fake L ALO) as D_t_f. pose proof (ad_dtls_res L ALO) as D_d_res. pose proof (ad_t_dtls L ALO) as D_t_d.
  pose proof (ao_dtls L ALO) as ODT. unfold aobj in ODT. unfold adisj in D_f_res, D_t_f, D_d_res, D_t_d.
  assert (FKD : forall cls FA sz, In (mkABlock (ABFake cls) FA sz) LB -> al_fake L <= FA /\ 0 <= sz /\ FA + sz <= al_fake L + 11571200)
    by (intros cls FA sz Hin; exact (proj1 (proj2 BL) cls FA sz Hin)).
  assert (PRES : aheap_pres CI LB (bv_unsigned spA) m m_pre).
  { intros a Ha CL. split; [| intros Hw; apply WMall; exact Hw].
    apply MUall. rewrite wa_unsigned by exact Ha.
    destruct CL as [STa | [CIa | [BLK | SH]]].
    - eapply disjoint_outside; [eapply (Q_stack _ _ _ _ _ _ _ PF a 1); clear -STa; lia | clear; lia].
    - destruct CIa as (iv & Hiv & R). pose proof (proj1 (Forall_forall _ _) CI_OK iv Hiv) as (Q1 & Q2 & Q3).
      pose proof (proj1 (Forall_forall _ _) CI_OK2 iv Hiv) as Q4. cbn [fst snd] in *.
      eapply disjoint_outside; [eapply (Q_img _ _ _ _ _ _ _ PF a 1); unfold AIMG_HI in *; clear -R Q1 Q3 Q4; lia | clear; lia].
    - destruct BLK as (b & Hb & R). destruct b as [[p|cls] A n']; cbn [ab_addr ab_size] in R.
      + destruct (proj1 BL p A n' Hb) as [(xb & Hxb & Sb & Ub & Nb)|(mb0 & ms0 & Lp & EUA & Gs)].
        * destruct (BB xb Hxb) as (Bb1 & Bb2 & Bb3).
          pose proof (awf_fits L st X xb WF Hxb) as FIT. unfold xb_fits in FIT. rewrite Sb in FIT. unfold xb_user in Ub. subst A n'.
          eapply disjoint_outside; [eapply (Q_slot _ _ _ _ _ _ _ PF a 1) | clear; lia]; clear -R Bb1 Bb2 Bb3 FIT; lia.
        *
          cbn [sec_wf1] in Gs. destruct Gs as (Gs1 & Gs2 & Gs3 & Gs4 & Gs5 & Gs6 & (Ct & Cc & Cr & Cp & Cn & Cs & Cf & Cd)).
          pose proof (sec_facts n' ltac:(clear -Gs5; lia) Gs6) as SF. subst A. unfold SEC_UOFF, K_HIGH_MEM in *.
          unfold ablk, KLS, AIMG_HI in Gs2.
          eapply disjoint_outside; [eapply (Q_obj _ _ _ _ _ _ _ PF a 1) | clear; lia]; clear -R Gs2 Gs3 Gs4 Gs5 SF Ct Cr RSP ORS; lia.
      + destruct (FKD cls A n' Hb) as (K1 & K2 & K3). atop_facts.
        eapply disjoint_outside; [eapply (Q_obj _ _ _ _ _ _ _ PF a 1) | clear; lia];
          clear -R K1 K3 FKO D_t_f D_f_res RSP OFKi OFKs OFKsa OFKsb; lia.
    - destruct SH as (a' & Ha' & ->).
      destruct Ha' as [STa | [CIa | FK]].
      + eapply disjoint_outside; [eapply (Q_shad_hi _ _ _ _ _ _ _ PF a'); unfold AMALLOC_STACK in *; clear -STa LO BOT STK3; lia | clear; lia].
      + destruct CIa as (iv & Hiv & R). pose proof (proj1 (Forall_forall _ _) CI_OK iv Hiv) as (Q1 & Q2 & Q3). cbn [fst snd] in *.
        eapply disjoint_outside; [eapply (Q_shad_img _ _ _ _ _ _ _ PF a'); unfold AIMG_HI in *; clear -R Q1 Q3; lia | clear; lia].
      + destruct FK as (cls & FA & sz & Hin & R). destruct (FKD cls FA sz Hin) as (K1 & K2 & K3). atop_facts.
        eapply disjoint_outside; [eapply (Q_shad_obj _ _ _ _ _ _ _ PF a') | clear; lia]; clear -R K1 K3 FKO D_f_res RSP OFKi OFKs OFKsa OFKsb; lia. }
  assert (HFKp : AFK L LB m_pre).
  { eapply (hf_frame _ HL L LB m m_pre); [exact HFK | exact MUall | exact WMall | exact (Q_tfs _ _ _ _ _ _ _ PF) |].
    unfold fake_untouched. pose proof (ao_t L ALO) as OT. unfold aobj in OT.
    assert (SHF : 2148261376 <= shad (al_fake L) /\ shad (al_fake L) + shlen 11571200 <= 17594332446720
                  /\ (shad (al_space_beg L + c * 4294967296) + 536870912 <= shad (al_fake L)
                      \/ shad (al_fake L) + shlen 11571200 <= shad (al_space_beg L + c * 4294967296 + mu0))
                  /\ shad (al_space_beg L + c * 4294967296) <= shad (al_space_beg L + c * 4294967296 + mu0)
                  /\ 2201439137792 <= shad (al_space_beg L + c * 4294967296)).
    { rewrite !shad_div, !shlen_div. unfold ASHOFF in *. destruct PF as (_ & _ & (F1 & F2 & F3 & F4 & F5 & F6) & _).
      clear -FKO F1 F2 F3 F4 F5 F6 D_f_res RSP OFKi OFKs OFKsa OFKsb. Z.div_mod_to_equations. dlia. }
    destruct SHF as (SF1 & SF2 & SF3 & SF4 & SF5).
    unfold AMALLOC_STACK, AINSTANCE in *. destruct PF as (PF1 & PF2 & PF3 & PF4).
    repeat (apply Forall_cons; [cbn [fst snd];
      clear -HspA LOA SPV LO BOT STK3 SP47 STK2 OT FKO ORS RSP ODT D_f_res D_t_f D_d_res D_t_d C16 PF3 PF4 SF1 SF2 SF3 SF4 SF5 SHHI TL1 TBND TBNDa TBNDb TIMG TIMGa TIMGb OFKi OFKs OFKsa OFKsb DBND DBNDa DBNDb DIMG DIMGa DIMGb;
      repeat (split; [lia|]); lia |]).
    apply Forall_nil. }

  eapply evtF_mono.
  { replace (bv_unsigned sp - 2272) with (bv_unsigned spA + -128) in ST1, FRa by (clear -HspA; lia).
    eapply (alloc_tail_D DI L RNG1 ra gp tp spA t0d t1d t2d a1d a2d a3d a4d a5d a6d a7d t3d t4d t5d t6d
              s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m1
              n (al_t L) c cnt AB UB PG room lo b0 b1 szh szl ctxj (1 + Z.of_nat (length trc)) SO pc
              (Z_to_bv 64 (max_count st_pre c)) (Z_to_bv 64 S) stj1 j1 j2 (Z_to_bv 8 250) sj' sjunk uj fr0 tb trc).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => exact ST1
         | |- mem_inv _ _ => exact MI1
         | |- allocA_cells _ _ _ => unfold allocA_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end)
         | |- poison_cells _ => unfold poison_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end)
         | |- ADEPOT _ _ _ => exact DEP1
         | |- In _ _ => exact TRU
         | |- u64arr _ _ (_ + 2800) _ => exact STATS'
         | |- u64arr _ _ _ _ => exact TB
         | |- map _ _ = _ => exact TRF
         | |- (16 < _) -> _ => exact LH1
         | |- ~ _ -> rng _ _ _ => exact RSPf
         | |- ~ _ -> _ => exact SHP1
         | |- is_primary _ = _ => exact PRIM
         end.
    all: try lazymatch goal with
         | |- rw_cells _ _ (_ + -16) _ => exact HDR
         | |- rw_cells _ _ (shad _) [C1 _] => exact SHA
         | |- rw_cells _ _ (shad _) [CB _ _] => exact SHU
         | |- rw_cells _ _ _ [CB _ _] => exact UJ
         | |- rw_cells _ _ (_ + 2784) _ => exact STS1
         | |- rw_cells _ _ (_ + 208 + _ * 80) _ => exact CR1
         | |- rw_cells _ _ _ _ => assumption
         | |- rng _ _ _ => assumption
         | |- _ \/ _ => first [exact DJT | exact DJN | exact DJS | exact DJC4 | unboxed CL5 | unboxed DL7 | unboxed DL8 | unboxed DL9 | unboxed DL10]
         | |- @eq Z _ _ => first [assumption | reflexivity | exact PGE | subst room; reflexivity]
         | |- @eq word _ _ => first [assumption | reflexivity]
         | |- @eq nat _ _ => first [exact LSJ' | exact LTB | assumption]
         end.
    all: try assumption.
    all: try (generalize N NR LO BOT SP47 STK1 STK2 STK3 SP1 SP2 SP4 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6
                         G1 G2 G3 G4 G5 EUB ES SM16 NSZ NS RSR RZR GR3 GR7 GR8 GR9 SB3 SB4 B1 POS HCNT CNT16 KS0 KS1 HC0 C16 LTRC HspA LOA SPV SPS STOP;
              clear; intros; rewrite ?HC0 in *; unfold AIMG_HI, AMALLOC_STACK, AREQMAX, UDEPTH, K_SPACE_SIZE, K_SPACE_EXTRA in *; lia).
    all: try (eapply rng_fp_le; [exact FPLE | exact RS]).
    all: try (clear -LTRC; lia).
    all: match goal with |- ?G => idtac "REMT" G end. }

  cbv beta. intros ms' PM.
  unfold aallocate_post_x. cbn [snd fst]. split.
  {
    pose proof PM as PM0. unfold malloc_post_gen in PM0.
    destruct PM0 as (id0 & t0e & t1e & t2e & a1e & a2e & a3e & a4e & a5e & a6e & a7e & t3e & t4e & t5e & t6e & m5 & sj5 & stj5 & EMS & MUt & _).

    assert (AXFall : axflags L st_pre m_pre).
    { intros c' Hc' NC'. destruct (Z.eq_dec c' c) as [->|NE]; [exact (AXFp NC')|].
      pose proof (C6F4 c' Hc' NC') as F4. unfold axflag in *.
      replace (exh_mem c' st_pre) with (exh_mem c' st)
        by (destruct EXHp as [E|E]; [symmetry; apply exh_mem_eq_list; exact E| rewrite (exh_mem_eq_list c' _ _ E); symmetry; apply exh_mem_clear_other; exact NE]).
      eapply cells_frameO; [exact F4| exact MUc|]. cbn [cells_size csize Nat.add]. intros x Hx. cbn [outside].
      assert (RIEj : forall j, aregion_info L j = al_space_beg L + 137438953472 + j * 128) by (intros j; unfold aregion_info, K_SPACE_SIZE, ARI_STRIDE; change (2^37) with 137438953472; reflexivity).
      rewrite (RIEj c') in Hx. rewrite (RIEj c). unfold aregion, K_REGION, AINSTANCE, K_NUM_CLASSES in *. change (2^32) with 4294967296.
      pose proof atop_range as ATRx.
      assert (SHT : shad (al_space_beg L + c * 4294967296) + shlen 4294967296 <= 17594333495296)
        by (rewrite shad_div, shlen_div; unfold ASHOFF, K_SPACE_SIZE, K_SPACE_EXTRA in *; change (2^37) with 137438953472 in *; clear -SP1 SP2 C16 ATRx; Z.div_mod_to_equations; lia).
      rewrite ?unsigned_lit by (clear -SPR HspA LO BOT STK3; lia).
      pose proof TSP as TSPx. unbox TSPx.
      unfold K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^37) with 137438953472 in *.
      clear -Hx Hc' NE C16 SP1 SP2 TL1 TL2 TL4 LO BOT STK3 HspA SHT A1 A2 ATRx SPR TSPx. unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in *. repeat split; lia. }
    destruct (c6_frame L RESV RNG1 st_pre m_pre m1 _ ALO ROK AXGp AXFall MU1) as [G1x F1x].
    { rewrite ?unsigned_lit by (clear -SPR HspA LO BOT STK3; lia).
      apply Forall_cons; [unfold c6_piece; cbn [fst snd]; intros _; left; clear -LO BOT STK3 HspA; lia|].
      apply Forall_cons; [unfold c6_piece, acache_addr; cbn [fst snd]; intros _; right; left; clear -C16; lia|].
      apply Forall_cons; [unfold c6_piece; cbn [fst snd]; intros _; right; left; clear; lia| apply Forall_nil]. }
    destruct (c6_frame L RESV RNG1 st_pre m1 m5 _ ALO ROK G1x F1x MUt) as [G5x F5x].
    { pose proof (ao_res L ALO) as (_ & _ & ORSx & _). pose proof (ao_space L ALO) as RSPx. pose proof atop_range as ATRx.
      assert (UBN : UB + n <= AB + S) by (clear -EUB NS NSZ RSR ES; lia).
      repeat (apply Forall_cons; [unfold c6_piece; cbn [fst snd]; intros NEk;
        first [ left; clear -LO LOA HspA BOT; unfold AMALLOC_STACK in *; lia
              | right; left; clear -C16; lia
              | do 2 right; left; clear -G1 G2 EUB UBN RSPx RZR SZB ES; subst S; lia
              | do 3 right; left; clear -NEk GR3 GR4 GR5 GR6 GR7 GR8 GR9 PGE SB3; subst g grz; lia
              | do 5 right; left; clear; lia
              | do 6 right; left; clear; lia
              | do 7 right; left; clear; lia ]|]).
      apply Forall_nil. }
    rewrite EMS. unfold c6_at. cbn [ms_mem MS].
    destruct G5x as (XC5 & EC5 & ER5 & ECL5).
    split.
    - split; [exact XC5|]. split; [exact EC5|]. split; [exact ER5|].
      eapply (emb_clr_sub RESV st_pre); [reflexivity| | exact ECL5].
      apply (achunks_new_prim st_pre _ (a_next (apop c st_pre)) c n); reflexivity.
    - intros c' Hc' NC'. exact (F5x c' Hc' NC'). }
  unfold apop. rewrite HCNT, !a_next_put_cls, !a_live_put_cls.
  apply (malloc_post_gen_shift DI L ra spA gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc n (al_t L) c cnt AB UB PG room lo b1 _ _ uj m_pre m1 ms') in PM;
    [| eapply munch_weaken; [| exact MU1]; unfold sub_fp, acache_addr; cbn [outside]; intros q Hq; clear -Hq HspA; lia | exact WM1].
  cbv delta [PG g grz room] in PM, SHpre, SHsuf. subst UB. subst AB.
  eapply (amalloc_post_shiftG CI _ L RNG RNG1 ra spA gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st st_pre LB n lo m m_pre); [| exact FPLE |].
  { eapply (store_prim DI AQ ASEC AFK HL CI CI_OK L RNG1 ra spA gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m_pre st_pre LB X_pre n lo c cnt k b1
              (Z_to_bv 64 (max_count st_pre c)) (Z_to_bv 64 (size_of_class c)) uj).
    all: try exact PM.
    all: try lazymatch goal with
         | |- is_primary _ = _ => exact PRIM
         | |- ann_ov _ = None => rewrite L2; exact OVF
         | |- alayout_ok _ => exact ALO
         | |- arng _ _ _ => exact ARNGp0
         | |- AFK _ _ _ => idtac
         | |- AREP _ _ _ _ _ => exact ARp
         | |- ablocks _ _ _ _ => eapply ablocks_xbusyG; [exact BL | exact XB | exact L1]
         | |- nth_error _ _ = _ => exact NK
         | |- busy_of _ _ _ = _ => exact NB
         | |- (16 < _) -> _ => let R16 := fresh in intros R16; exact (proj2 (LH R16))
         | |- junk_at _ (_ + 2768) _ => exact CSa
         | |- junk_at _ (_ + 2792) _ => exact CSc
         | |- junk_at _ _ _ => first [exact TL | rewrite ES; exact TL]
         | |- fill_at _ (_ + 1) _ _ => exact SHpre
         | |- fill_at _ _ _ _ => first [exact SHsuf | rewrite ES; exact SHsuf]
         end.
    all: try assumption.
    all: try reflexivity.
    all: try (generalize N KR B1 LO LOA BOT STK3 POS; clear; intros; unfold AMALLOC_STACK in *; lia).
    all: try exact HFKp.
    all: match goal with |- ?G => idtac "REMS" G end. }
  exact PRES.
Qed.
End S.
End CANSEC1.
End AAllocatePG_x.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require BImg.
Module TwinB.
Import stdpp.gmap.

Module AMallocPG_x.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Exec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Tac. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ITreeA. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.SysStepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW.BImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABytes.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ASecFacts.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AMalloc_iface.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ADepot_iface.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARep.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ALayout.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AHeapP.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepKit.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepFrame.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepExt.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepExt2.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit2.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AModelFacts.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.APrimFacts.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apoison.TwinB.F_apoison.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc1.TwinB.F_aalloc1.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc2.TwinB.F_aalloc2. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_amalloc_icpt.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_amalloc_pre.TwinB.F_amalloc_pre.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc2.TwinB.F_aalloc2g.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc3.TwinB.F_aalloc3g.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aaligned_tail.TwinB.F_amalloc_tailg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_amalloc_arep.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepStore.TwinB.ARepStore.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepStore.TwinB.ARepStoreG. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARefill_iface.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARefillP.TwinB.ARefillP.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ACallocG.TwinB.ACallocG.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

 Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AAlignedPG.TwinB.AMallocPG. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AEmbRep.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFrameD.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AEmbFrame.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_arefill.TwinB.F_arefill_x. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARefill_iface_x.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARefillP_x.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARefillP.TwinB.ARefillP_e. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_acache_x.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ACallocG.TwinB.ACallocG_x. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_amalloc_null.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ANullKit.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AC6Frame.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ANullPres.TwinB.
Export OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AMalloc_iface2.TwinB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSECX0. Context {rc : runConstT} {ov : annOV}.

Definition c6_at (RESV : list (Z * Z)) (L : alayout) (RNG' : footprint) (st' : astate) (ms' : machine_state) : Prop :=
  axg RESV RNG' st' (ms_mem ms') /\ axflags L st' (ms_mem ms').

Definition amalloc_post_x (CI : list (Z * Z)) (AHEAP : alayout -> footprint -> astate -> list ablock -> amem -> Prop)
    (L : alayout) (RESV : list (Z * Z)) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (n lo : Z) (m : amem)
    (r : astate * option aptr) (RNG' : footprint) : machine_state -> Prop :=
  fun ms' => c6_at RESV L RNG' (fst r) ms' /\
    match snd r with
    | Some _ => amalloc_post CI AHEAP L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB n lo m r RNG' ms'
    | None => fp_le RNG RNG' /\ exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (ret_pc ra) fc None m' (seg_rom bsegs)
        /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
        /\ aheap_pres_e CI LB (bv_unsigned sp) m m'
        /\ AHEAP L RNG' (fst r) LB m'
        /\ rw_cells bsegs m' AERRNO [C4 (Z_to_bv 64 12)]
    end.
End CANSECX0.

Section CANSEC1. Context {rc : runConstT} {ov : annOV}.

Local Lemma ablk_int : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6492160 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
Local Lemma aobj_int : forall a n, aobj a n -> 0x10000 <= n ->
  6492160 <= a /\ a + n <= ATOP /\ exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof.
  intros a n H Hn. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. destruct H as (H1 & H2 & H3 & H4 & H5).
  split; [lia|]. split; [lia|]. destruct H4; [exists 0 | exists 1]; lia.
Qed.
Local Lemma aobj4_int : forall a, aobj a 4096 ->
  4096 <= a /\ a + 4096 <= ATOP
  /\ (exists k, 0 <= k <= 1 /\ a + 4096 <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a)
  /\ (exists j, 0 <= j <= 1 /\ a + 4096 <= 65536 + j * 18446744073709551616 /\ 6492160 * j <= a).
Proof.
  intros a H. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. destruct H as (H1 & H2 & H3 & H4 & H5).
  split; [lia|]. split; [lia|]. split; [destruct H4; [exists 0 | exists 1]; lia | destruct H5 as [_ [H5|H5]]; [exists 0 | exists 1]; lia].
Qed.

Local Ltac dlia := repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
Section S.
Variable DI : ADepotIface.
Variables (AQ ASEC : alayout -> astate -> aconc -> amem -> Prop) (AFK : alayout -> list ablock -> amem -> Prop).
Hypothesis HL : ahole_laws (AH DI AQ ASEC AFK).
Hypothesis HLD : ahole_lawsD (AH DI AQ ASEC AFK).
Hypothesis EXHW : exh_first_stmt.
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI) CI.

Hypothesis CI_OK2 : Forall (fun iv => snd iv <= AINSTANCE \/ AINSTANCE + 728 <= fst iv) CI.

Hypothesis CI_OK3 : Forall (fun iv => (snd iv <= AEMB \/ AEMB + 56 <= fst iv) /\ (snd iv <= 0x15dee0 \/ 0x15dee1 <= fst iv)) CI.

Theorem amalloc_prim_x : forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (n lo : Z) (tr : list Z) (RESV : list (Z * Z)),
  ann_ov (a_next st) = None ->

  is_primary n = true ->

  AHEAP_P (AH DI AQ ASEC AFK) L RNG st LB m ->
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - 4608 ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 n -> 1 <= n <= AREQMAX ->
  aunw m L RNG lo AMALLOC_PC sp s0 ra tr ->
  bv_unsigned s0 <> bv_unsigned sp + 8 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AMALLOC_PC ->
  bv_unsigned sp mod 16 = 0 ->
  rng RNG lo (bv_unsigned sp - lo) ->
  aresv_ok L RESV ->

  bv_unsigned fc < 32 -> axg RESV RNG st m -> axflags L st m -> (let '(_, cap0, _) := a_emb st in cap0 <= 2 ^ 23) ->
  (exists e0 : word, rw_cells bsegs m AERRNO [C4 e0]) ->
  implS bsegs RNG (aembed ATOP (amalloc ATOP RESV st n))
        (epostF (amalloc_post_x CI (AHEAP_P (AH DI AQ ASEC AFK)) L RESV RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB n lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AMALLOC_SYM) fc None m (seg_rom bsegs)).
Proof.
  intros until RESV. intros OVF PRIM AHP MI ST BOT LO TP Ha0 NR AUNW S0NE RA4 RANE SP16 RSTK ROK FC C6G C6F CAPB ERRC.
  assert (N : 1 <= n <= AREQMAX) by exact NR. assert (N1 : 1 <= n) by (clear -NR; lia).

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
  remember (class_id (needed_size n)) as c eqn:HC0. symmetry in HC0.
  pose proof (prim_facts n N1 PRIM) as (NS & RZR & RZE & RZM & RLR & RSR & RSM & NSR).
  pose proof (prim_class_facts n c N1 PRIM HC0) as (C16 & NSZ & SM16 & SMALL & MCB). clear SMALL.
  pose proof (cls_facts c C16) as (SZB & _ & _ & _).
  assert (HCK : 1 <= c < K_NUM_CLASSES) by (unfold K_NUM_CLASSES; clear -C16; lia).
  assert (NM8 : needed_size n mod 8 = 0) by (rewrite NS; clear -RSM RZM; Z.div_mod_to_equations; lia).

  pose proof AR as AR0. destruct AR0 as (WF & RT & INST & THR & CLS & HQ & HS & HD & HRO & RT2 & AVL & RT3).
  destruct THR as (T0 & T40 & CACHES & CSTATS & [sj [STATS LSJ]] & UNW).
  pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVE & FRESH & UNIQ).
  destruct (PERC c HCK) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & LENF & LENC & CNTB & ND & RANGE).
  pose proof (alayout_space L ALO) as (SP1 & SP2 & SP3 & SP4).
  pose proof (alayout_t L ALO) as (TL1 & TL2 & TL3 & TL4).
  pose proof (alayout_ctx L ALO) as (CL1 & CL2 & CL3 & CL4 & CL5).
  pose proof (alayout_depot L ALO) as (DL1 & DL2 & DL3 & DL4 & DL5 & DL6 & DL7 & DL8 & DL9 & DL10).
  pose proof (aobj4_int _ (ao_t L ALO)) as (_ & _ & (kT & TBND & TBNDa & TBNDb) & (jT & TIMG & TIMGa & TIMGb)).
  pose proof (aobj_int _ _ (ao_ctx L ALO) ltac:(clear; lia)) as (CTXi & _ & (kC & CBND & CBNDa & CBNDb)).
  pose proof (aobj_int _ _ (ao_nodes L ALO) ltac:(clear; lia)) as (NODi & _ & (kN & NBND & NBNDa & NBNDb)).
  pose proof (aobj_int _ _ (ao_store L ALO) ltac:(clear; lia)) as (STOi & _ & (kR & SBND & SBNDa & SBNDb)).
  pose proof (aobj_int _ _ (ao_fake L ALO) ltac:(clear; lia)) as (OFKi & _ & (kF & OFKs & OFKsa & OFKsb)).
  pose proof (aobj4_int _ (ao_dtls L ALO)) as (_ & _ & (kD & DBND & DBNDa & DBNDb) & (jD & DIMG & DIMGa & DIMGb)).
  pose proof (alayout_stack L ALO) as (STK1 & STK2 & STK3).
  pose proof (alayout_res_disj L ALO) as [SCX TSP].
  pose proof RT as RT0.
  destruct RT0 as (GPG & GOT & GOT80 & RIC & LS1 & REAL & IMAX4 & FLG5 & FLG & HPP & SHB & CANP & TI & TK & INI2 & LAY & MCS & OOM3
                    & PGC & HK2 & CF8 & CF34 & CSMT & T88 & TSD & LS2 & CT8 & CT).
  pose proof INI2 as INI. rw_split INI 1%nat INI1 INIx. clear INIx.
  destruct OOM3 as [oomb OOM]. rw_split OOM 2%nat OOMx RSS. clear OOMx.
  pose proof IMAX4 as IMAX. rw_split IMAX 3%nat IMAX3 IMAXx. clear IMAXx.
  pose proof T0 as TT0. rw_split TT0 1%nat TTctx TT.
  pose proof ARNG as ARNG0. destruct ARNG as (RIMG & RT4 & RCTX & RNO & RSTO & RRI & RFK & RSFK & RDTLS & RCLS).
  assert (RCTX4 : rng RNG (al_ctx L) 4096) by (eapply rng_sub'; [exact RCTX|]; clear; lia).
  word_range sp SPR.
  box CL5. box DL7. box DL8. box DL9. box DL10. box TSP. box SCX.

  rewrite (amalloc_prim_eq RESV st n c N1 PRIM HC0).

  iprefix. eapply evtF_cut.
  { eapply (malloc_pre_spec L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n (al_t L) lo (al_top L) (al_bot L) tr trc).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => exact ST
         | |- mem_inv _ _ => exact MI
         | |- allocA_cells _ _ _ => unfold allocA_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end)
         | |- poison_cells _ => unfold poison_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end)
         | |- u64arr _ _ _ _ => exact STATS
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
  cbv beta. intros ms4 P4. unfold malloc_pre_post in P4.
  destruct P4 as (spA & t0c & t1c & t2c & a4c & a5c & a6c & a7c & t3c & t4c & t5c & t6c & s0A & s1A & s2A & s3A & s4A & s5A & s0i & fr0 & junk2 & tb & m4
                  & -> & HspA & MU4 & WM4 & MI4 & ST4 & FRa & FR16 & SS & TB & LTB & TRF & FRS & UW4).
  apply evtF_done.
  assert (AR4 : AREP (AH DI AQ ASEC AFK) L st X m4).
  { eapply (AREP_frame_pre _ HL L st X m m4); [exact ALO | exact AR | exact MU4 | exact WM4 | | exact UW4].
    apply Forall_cons; [unfold apre; cbn [fst snd]; intros _; left; unfold AMALLOC_STACK in *; clear -LO BOT STK3; lia|].
    apply Forall_cons; [unfold apre; cbn [fst snd]; intros _; right; split; reflexivity| apply Forall_nil]. }

  destruct (c6_frame L RESV RNG st m m4 _ ALO ROK C6G C6F MU4) as [C6G4 C6F4].
  { apply Forall_cons; [unfold c6_piece; cbn [fst snd]; intros _; left; unfold AMALLOC_STACK in *; clear -LO BOT STK3; lia|].
    apply Forall_cons; [unfold c6_piece; cbn [fst snd]; intros _; right; left; clear; lia| apply Forall_nil]. }

  eapply (@calloc_arep_gen_x _ _ _ HL HLD _ RESV _ _ L RNG _ _ gp tp t0c t1c t2c _ _ _ _ _ _ a4c a5c a6c a7c _ _ _ _ _ _ _ _ _ _ t3c t4c t5c t6c F fc m4 st X c lo (needed_size n)
            ALO ARNG0 AR4 MI4).
  all: try lazymatch goal with
       | |- arng _ _ _ => exact ARNG0
       | |- stk _ _ _ _ => rewrite unsigned_lit by (clear -SPR HspA LO BOT STK3; unfold AMALLOC_STACK in *; lia);
                           replace (bv_unsigned spA + -128) with (bv_unsigned sp - 2272) by (clear -HspA; lia); exact ST4
       | |- ATOP <= _ => clear -LO BOT STK3; unfold AMALLOC_STACK in *; lia
       | |- _ <= bv_unsigned _ - _ => rewrite unsigned_lit by (clear -SPR HspA LO BOT STK3; unfold AMALLOC_STACK in *; lia);
                                    clear -LO HspA BOT STK3; unfold AMALLOC_STACK in *; lia
       | |- @eq word _ _ => first [exact TP | reflexivity]
       | |- 16 <= _ <= 65536 => clear -NSR; lia
       | |- _ mod 8 = 0 => exact NM8
       | |- class_id _ = _ => exact HC0
       | |- rng _ _ _ => rewrite unsigned_lit by (clear -SPR HspA LO BOT STK3; unfold AMALLOC_STACK in *; lia);
                         eapply rng_sub'; [exact RSTK|]; clear -LO HspA SP47 BOT STK3; unfold AMALLOC_STACK in *; lia
       | |- exh_first_stmt => exact EXHW
       | |- aresv_ok _ _ => exact ROK
       | |- bv_unsigned _ < 2 ^ 63 => rewrite unsigned_lit by (clear -SPR HspA LO BOT STK3; unfold AMALLOC_STACK in *; lia); clear -SP47 HspA; lia
       | |- bv_unsigned _ < 32 => exact FC
       | |- _ -> axflag _ _ _ _ => intros NC24x; exact (C6F4 c HCK NC24x)
       | |- axg _ _ _ _ => exact C6G4
       | |- context [a_emb _] => exact CAPB
       | |- forall _, _ => idtac
       end.
  1: {
       intros st2 RNG' ms' RF. unfold aret_xf in RF. cbv zeta in RF. pose proof atop_range as ATR.
       pose proof C6G4 as (_ & ECp & _ & ECLp). unfold emb_cells in ECp. unfold emb_clr in ECLp.
       destruct (a_emb st) as [[d0 cap0] sz0] eqn:EA. destruct (a_emb st2) as [[d2 cap2] sz2] eqn:EA2.
       destruct RF as (FPLE & t0r & t1r & t2r & a1r & a2r & a3r & a4r & a5r & a6r & a7r & t3r & t4r & t5r & t6r & mr
                       & -> & MIr & STr & STEQ & ARr & ARNGr & AXFr & AXGr & (d1 & cap1 & MUr & PV1 & PV2 & TOP1)).
       assert (USP : bv_unsigned (Z_to_bv 64 (bv_unsigned spA + -128)) = bv_unsigned sp - 2272)
         by (rewrite unsigned_lit by (clear -SPR HspA LO BOT ATR; lia); clear -HspA; lia).
       rewrite USP in MUr, STr.

       assert (B0 : bufok RESV st d0 cap0).
       { unfold bufok. destruct (Z.eqb_spec cap0 0) as [E0|NZ]; [left; lia|]. right.
         destruct ECp as (_ & _ & _ & _ & _ & _ & _ & _ & TOP & _). split; [exact TOP|]. destruct ECLp as [Q|Q]; [exfalso; exact (NZ Q)| exact Q]. }
       assert (B1 : bufok RESV st d1 cap1).
       { destruct (Z_le_gt_dec cap1 0) as [LE|GT]; [left; exact LE|]. destruct PV1 as [[E1 E2]|AV]; [rewrite E1, E2; exact B0|].
         right. split; [destruct TOP1 as [Q|Q]; [lia| exact Q]| exact AV]. }
       assert (B2 : bufok RESV st d2 cap2).
       { destruct PV2 as [[E1 E2]|AV]; [rewrite E1, E2; exact B0|].
         pose proof AXGr as (_ & EC2 & _). unfold emb_cells in EC2. rewrite EA2 in EC2. destruct (Z.eqb_spec cap2 0) as [E0|NZ]; [left; lia|]. right.
         destruct EC2 as (_ & _ & _ & _ & _ & _ & _ & _ & TOP & _). split; [exact TOP| exact AV]. }

       set (SPc := bv_unsigned sp - 2272) in *.
       assert (SPHIc : ATOP <= SPc) by (subst SPc; clear -LO BOT; lia).
       assert (SPHI : ATOP <= bv_unsigned sp) by (clear -LO BOT; lia).
       set (Wf := [(SPc - 2096, SPc); (al_t L + 208, al_t L + 2768); (aregion_info L c, aregion_info L c + 8);
                   (aregion_info L c + 68, aregion_info L c + 69); (AEMB, AEMB + 56); (d0, d0 + cap0); (d1, d1 + cap1); (d2, d2 + cap2)]%Z).
       change (munch Wf m4 mr) in MUr.
       assert (PCSf : Forall (nf_piece L RESV st SPc c) Wf).
       { assert (BK : forall d cap, bufok RESV st d cap -> nf_piece L RESV st SPc c (d, d + cap)).
         { intros d cap [B|[Bt Ba]] LT; cbn [fst snd] in LT; [lia|]. unfold nf_kind. cbn [fst snd]. do 4 right. left.
           replace (d + cap - d) with cap by lia. split; assumption. }
         subst Wf. repeat (apply Forall_cons); try apply Forall_nil; try (apply BK; assumption); intros _; unfold nf_kind; cbn [fst snd].
         - left. subst SPc. clear -LO BOT. lia.
         - right; left. clear. lia.
         - right; right; left. clear. lia.
         - right; right; left. clear. lia.
         - right; right; right; left. clear. lia. }
       assert (OUTS : forall x, SPc <= x -> outside Wf x)
         by (intros x Hx; apply (nf_outside L RESV st SPc c ALO ROK HCK SPHIc Wf x PCSf); left; exact Hx).

       apply rw_cells_of_u64arr in TB. rewrite LTB in TB.
       assert (FRar : rw_cells bsegs mr (bv_unsigned spA + -128)
                        [CB 8 fr0; C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 16); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5A;
                         C8 s4A; C8 s3A; C8 s2A; C8 s1A; C8 s0A; C8 (Z_to_bv 64 0x3d628)]).
       { replace (bv_unsigned spA + -128) with (bv_unsigned sp - 2272) by (clear -HspA; lia).
         eapply cells_frameO; [exact FRa| exact MUr|]. intros x Hx. apply OUTS. subst SPc. clear -Hx. lia. }
       assert (FR16r : rw_cells bsegs mr (bv_unsigned sp + -2144) [C8 s0i; C8 (Z_to_bv 64 0x5f0b8)])
         by (eapply cells_frameO; [exact FR16| exact MUr|]; intros x Hx; apply OUTS; subst SPc; clear -Hx; lia).
       assert (SSr : rw_cells bsegs mr (bv_unsigned sp + -2128) [C8 (Z_to_bv 64 (bv_unsigned sp + -2128 + 16)); C8 (Z_to_bv 64 (1 + Z.of_nat (length trc)))])
         by (eapply cells_frameO; [exact SS| exact MUr|]; intros x Hx; apply OUTS; subst SPc; clear -Hx; lia).
       assert (TBr : rw_cells bsegs mr (bv_unsigned sp + -2128 + 16) [CB (8 * 255) (u64s tb)])
         by (eapply cells_frameO; [exact TB| exact MUr|]; intros x Hx; apply OUTS; subst SPc; clear -Hx; lia).
       assert (FRSr : rw_cells bsegs mr (bv_unsigned sp + -72) [C8 sp; CB 8 junk2; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
         by (eapply cells_frameO; [exact FRS| exact MUr|]; intros x Hx; apply OUTS; subst SPc; clear -Hx; lia).
       destruct ERRC as [e0 ERR0].
       assert (ERR4 : rw_cells bsegs m4 AERRNO [C4 e0]).
       { eapply cells_frameO; [exact ERR0| exact MU4|]. cbn [cells_size csize Nat.add]. intros x Hx. cbn [outside].
         unfold AERRNO, ATP in Hx. clear -Hx ATR LO BOT TIMG TIMGa TIMGb. repeat split; lia. }
       assert (ERRr : rw_cells bsegs mr AERRNO [C4 e0]).
       { eapply cells_frameO; [exact ERR4| exact MUr|]. cbn [cells_size csize Nat.add]. intros x Hx.
         assert (BI : forall d cap, bufok RESV st d cap -> ~ (d <= x < d + cap)).
         { intros d cap [B|[_ AV]]; [clear -B; lia|]. unfold avoids_all in AV. rewrite forallb_app in AV. apply andb_prop in AV as [AV _].
           destruct ROK as (PCI & _). apply (avoids_pcov_out RESV d cap 0x10000 AIMG_HI x PCI AV). unfold AIMG_HI, AERRNO, ATP in *. clear -Hx. lia. }
         pose proof (BI _ _ B0) as Q0. pose proof (BI _ _ B1) as Q1. pose proof (BI _ _ B2) as Q2.
         subst Wf. cbn [outside]. unfold aregion_info, K_SPACE_SIZE, ARI_STRIDE. change (2^37) with 137438953472.
         unfold AEMB, AERRNO, ATP in *. subst SPc.
         clear -Hx Q0 Q1 Q2 ATR LO BOT TIMG TIMGa TIMGb SP1 C16. repeat split; lia. }
       pose proof ARr as (_ & RTr & _).
       destruct RTr as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & OOM3r & _).
       destruct OOM3r as [oombr OOMr]. rw_split OOMr 2%nat OOMxr RSSr. clear RSSr.

       apply implS_ret.
       replace (ret_pc (Z_to_bv 64 0x3d8f8)) with (Z_to_bv 64 0x3d8f8) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
       pose proof ARNGr as (RIMGr & _).
       assert (RSTKr : rng RNG' lo (bv_unsigned sp - lo)) by (eapply rng_fp_leG; [exact FPLE | exact RSTK]).
       eapply evtF_cut.
       { eapply (allocN_spec RNG' spA gp tp t0r t1r t2r _ _ a1r a2r a3r a4r a5r a6r a7r _ _ _ _ _ _ _ _ _ _ t3r t4r t5r t6r
                   s0A s1A s2A s3A s4A s5A s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0x3d628) _ _ fr0 oombr F fc mr lo);
           first [ exact FRar | exact MIr | exact OOMxr | exact RIMGr
                 | replace (bv_unsigned spA + -128) with (bv_unsigned sp - 2272) by (clear -HspA; lia); exact STr
                 | eapply rng_sub'; [exact RSTKr|]; clear -HspA LO; lia
                 | clear -BOT ATR; lia
                 | clear -LO HspA; lia ]. }
       cbv beta. intros ms1 P1.
       destruct P1 as (t0n & t1n & t2n & a1n & a2n & a3n & a4n & a5n & a6n & a7n & t3n & t4n & t5n & t6n & m1 & -> & MU1 & WM1 & MI1 & ST1 & OOM1).
       assert (OUT1 : forall x, AIMG_HI <= x -> outside [(AOOM, AOOM + 1)]%Z x)
         by (intros x Hx; cbn [outside]; unfold AOOM, AIMG_HI in *; clear -Hx; lia).
       assert (FR16n : rw_cells bsegs m1 (bv_unsigned sp + -2144) [C8 s0i; C8 (Z_to_bv 64 0x5f0b8)])
         by (eapply cells_frameO; [exact FR16r| exact MU1|]; intros x Hx; apply OUT1; unfold AIMG_HI; clear -Hx ATR LO BOT; lia).
       assert (SSn : rw_cells bsegs m1 (bv_unsigned sp + -2128) [C8 (Z_to_bv 64 (bv_unsigned sp + -2128 + 16)); C8 (Z_to_bv 64 (1 + Z.of_nat (length trc)))])
         by (eapply cells_frameO; [exact SSr| exact MU1|]; intros x Hx; apply OUT1; unfold AIMG_HI; clear -Hx ATR LO BOT; lia).
       assert (TBn : rw_cells bsegs m1 (bv_unsigned sp + -2112) [CB (8 * 255) (u64s tb)]).
       { replace (bv_unsigned sp + -2112) with (bv_unsigned sp + -2128 + 16) by (clear; lia).
         eapply cells_frameO; [exact TBr| exact MU1|]. intros x Hx. apply OUT1. unfold AIMG_HI. clear -Hx ATR LO BOT. lia. }
       assert (FRSn : rw_cells bsegs m1 (bv_unsigned sp + -72) [C8 sp; CB 8 junk2; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
         by (eapply cells_frameO; [exact FRSr| exact MU1|]; intros x Hx; apply OUT1; unfold AIMG_HI; clear -Hx ATR LO BOT; lia).
       assert (ERRn : rw_cells bsegs m1 AERRNO [C4 e0]).
       { eapply cells_frameO; [exact ERRr| exact MU1|]. cbn [cells_size csize Nat.add]. intros x Hx. cbn [outside]. unfold AOOM, AERRNO, ATP in *. clear -Hx. lia. }

       replace (ret_pc (Z_to_bv 64 0x3d628)) with (Z_to_bv 64 0x3d628) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
       assert (EspA : spA = Z_to_bv 64 (bv_unsigned sp + -2144)).
       { enough (E : Z_to_bv 64 (bv_unsigned spA) = Z_to_bv 64 (bv_unsigned sp + -2144)) by (rewrite Z_to_bv_bv_unsigned in E; exact E).
         apply Z_to_bv_eqm. rewrite HspA. zeq. }
       rewrite HspA in ST1. replace (bv_unsigned sp - 2144) with (bv_unsigned sp + -2144) in ST1 by (clear; lia). rewrite EspA.
       eapply evtF_mono.
       { eapply (icptN_spec RNG' sp gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s6 s7 s8 s9 s10 s11 _ _ _ _ ra s0 s1 s2 s3 s4 s5 s0i F fc m1 lo junk2 e0);
           first [ exact ST1 | exact MI1 | exact TP | exact ERRn | exact FR16n | exact FRSn | exact RIMGr | exact RSTKr
                 | eexists; split; [exact SSn| reflexivity]
                 | eexists; split; [exact TBn| reflexivity]
                 | clear -BOT ATR; lia
                 | clear -LO; lia ]. }
       cbv beta. intros ms2 P2.
       destruct P2 as (t0e & t1e & t2e & a1e & a2e & a3e & a4e & a5e & a6e & a7e & t3e & t4e & t5e & t6e & m2 & -> & MU2 & WM2 & MI2 & ST2 & ERR2).

       pose proof (munch_app _ _ _ _ _ MU1 MU2) as MUn. pose proof (wmono_trans bsegs _ _ _ WM1 WM2) as WMn.
       assert (AXFSr : axflags L st2 mr).
       { intros c' Hc' NC'. destruct (Z.eq_dec c' c) as [->|NE]; [exact AXFr|].
         pose proof (C6F4 c' Hc' NC') as F4. unfold axflag in *.
         assert (EXE : exh_mem c' st2 = exh_mem c' st).
         { destruct STEQ as [[_ ->]|[_ [e2 ->]]]; [apply init_cache_exh|]. rewrite exh_mem_set_emb, (exh_mem_set_other c c' _ NE). apply init_cache_exh. }
         rewrite EXE. eapply cells_frameO; [exact F4| exact MUr|]. cbn [cells_size csize Nat.add]. intros x Hx.
         apply (nf_flag_outside L RESV st SPc c ALO ROK HCK SPHIc Wf c' x PCSf Hc' NE). clear -Hx. lia. }
       destruct (c6_frame L RESV RNG' st2 mr m2 _ ALO ROK AXGr AXFSr MUn) as [C6G2 C6F2].
       { cbn [app]. apply Forall_cons; [unfold c6_piece, AOOM; cbn [fst snd]; intros _; do 8 right; left; clear; lia|].
         apply Forall_cons; [unfold c6_piece; cbn [fst snd]; intros _; left; clear -LO BOT; lia|].
         apply Forall_cons; [unfold c6_piece; cbn [fst snd]; intros _; do 9 right; clear; lia| apply Forall_nil]. }

       assert (AR2 : AREP (AH DI AQ ASEC AFK) L st2 X m2).
       { eapply (AREP_frame_null _ HL L st2 X mr m2 (bv_unsigned sp) ALO ARr); [exact MUn| exact WMn| clear -LO BOT; lia|].
         exists (Z_to_bv 8 1). eapply cells_frameO; [exact OOM1| exact MU2|]. cbn [cells_size csize Nat.add]. intros x Hx. cbn [outside].
         unfold AOOM, AERRNO, ATP in *. clear -Hx ATR LO BOT. repeat split; lia. }
       assert (LIVE2 : a_live st2 = a_live st).
       { pose proof (init_cache_fields st) as (E1 & _). destruct STEQ as [[_ ->]|[_ [e2 ->]]]; [exact E1|]. rewrite <- E1. destruct (init_cache st); reflexivity. }
       pose proof (ablocks_same L st st2 X X LB BL eq_refl LIVE2) as BL2.
       pose proof (munch_app _ _ _ _ _ MU4 (munch_app _ _ _ _ _ MUr MUn)) as MUt.
       assert (PCSt : Forall (nf_piece L RESV st (bv_unsigned sp) c)
                        ([(bv_unsigned sp - 2320, bv_unsigned sp); (al_t L + 3168, al_t L + 3169)] ++ Wf ++ [(AOOM, AOOM + 1)] ++ [(bv_unsigned sp - 2160, bv_unsigned sp - 2144); (AERRNO, AERRNO + 4)])%Z).
       { apply Forall_app. split; [| apply Forall_app; split].
         - apply Forall_cons; [intros _; unfold nf_kind; cbn [fst snd]; left; clear -LO BOT; lia|].
           apply Forall_cons; [intros _; unfold nf_kind; cbn [fst snd]; right; left; clear; lia| apply Forall_nil].
         - eapply Forall_impl; [| exact PCSf]. intros iv K. apply (nf_piece_SP L RESV st SPc (bv_unsigned sp) c iv); [subst SPc; clear; lia| exact K].
         - cbn [app]. apply Forall_cons; [intros _; unfold nf_kind, AOOM; cbn [fst snd]; do 5 right; left; clear; lia|].
           apply Forall_cons; [intros _; unfold nf_kind; cbn [fst snd]; left; clear -LO BOT; lia|].
           apply Forall_cons; [intros _; unfold nf_kind; cbn [fst snd]; do 6 right; clear; lia| apply Forall_nil]. }
       destruct (nf_fake L RESV st (bv_unsigned sp) c _ ALO ROK HCK SPHI (nzl_pieces _ _ _ _ _ _ PCSt)) as (D72 & FU & D48).
       pose proof (hfD _ HLD L LB m m2 _ HFK (munch_nzl _ _ _ MUt) D72 FU D48) as HFK2.
       assert (PRESe : aheap_pres_e CI LB (bv_unsigned sp) m m2).
       { intros a Ha CL NERR.
         pose proof (nf_client_outside L RESV st X (bv_unsigned sp) c ALO ROK HCK SPHI CI CI_OK CI_OK3 WF LB _ a BL PCSt Ha CL NERR) as OUT.
         assert (E : m2 (wa a) = m (wa a)) by (apply MUt; rewrite wa_unsigned by exact Ha; exact OUT).
         split; [exact E|]. intros Hw. rewrite (AFrameD.TwinB.wview_agree bsegs m m2 (wa a) E). exact Hw. }

       unfold amalloc_post_x. cbn [fst snd]. split.
       { unfold c6_at. cbn [ms_mem]. split; [exact C6G2| exact C6F2]. }
       split; [exact FPLE|]. do 14 eexists. exists m2. split; [reflexivity|]. split; [exact MI2|]. split; [exact ST2|]. split; [exact PRESe|].
       split; [| exact ERR2].
       split; [exact ALO|]. split; [exact ARNGr|]. split; [exists X; split; [exact AR2| exact BL2]| exact HFK2]. }

  intros st_pre X_pre RNG1 m_pre cnt k ms1 CRET. destruct CRET as (CRET & EMBp & EXHp & AXFp & AXGp). unfold calloc_retG in CRET.
  destruct CRET as (FPLE & ARp & ARNGp & HCNT & POS & NK & NB & KR & XB & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & MUc & WMc & MIp
                    & t0d & t1d & t2d & a1d & a2d & a3d & a4d & a5d & a6d & a7d & t3d & t4d & t5d & t6d & m1 & stj1 & -> & MU1 & WM1 & MI1 & ST1 & CR1 & STS1).
  rewrite ?unsigned_lit in MUc by (clear -SPR HspA LO BOT STK3; unfold AMALLOC_STACK in *; lia).
  rewrite ?unsigned_lit in MU1 by (clear -SPR HspA LO BOT STK3; unfold AMALLOC_STACK in *; lia).
  rewrite ?unsigned_lit in ST1 by (clear -SPR HspA LO BOT STK3; unfold AMALLOC_STACK in *; lia).
  replace (bv_unsigned spA + -128) with (bv_unsigned sp - 2272) in ST1 by (clear -HspA; lia).
  cbn beta iota. apply implS_ret.
  replace (ret_pc (Z_to_bv 64 0x3d8f8)) with (Z_to_bv 64 0x3d8f8) by (symmetry; apply ret_pc_even; [lia|reflexivity]).

  pose proof ARp as AR0. destruct AR0 as (WF' & RT' & INST' & THR' & CLS' & HQ' & HS' & HD' & HRO' & RT2' & AVL' & RT3').
  destruct THR' as (T0' & T40' & CACHES' & CSTATS' & [sj' [STATS' LSJ']] & UNW').
  pose proof WF' as WF0. destruct WF0 as (SBE' & PAE' & SAL' & SLO' & SHI' & PERC' & OUTC' & BUSY' & LIVE' & FRESH' & UNIQ').
  destruct (PERC' c HCK) as (B1' & B2' & B3' & B4' & B5' & B6' & B7' & LENF' & LENC' & CNTB' & ND' & RANGE').
  destruct (kit_cache_pop _ L st_pre X_pre m_pre c cnt ARp HCK HCNT POS) as (k' & chunks & NK' & _ & _ & CR & CH & LCH & NTH & JK & FSH).
  assert (EK : k' = k) by (rewrite NK in NK'; injection NK'; intros E; symmetry; exact E). subst k'.

  set (S := size_of_class c) in *.
  set (AB := aslot_addr L c k) in *.
  assert (KSF : 0 <= k * S /\ k * S + S <= c_allocated_user (get_cls st_pre c) /\ (k * S) mod 16 = 0).
  { unfold ndist in KR. fold S in KR. fold S in SZB. fold S in SM16.
    assert (P0 : 0 <= k * S) by (clear -KR SZB; apply Z.mul_nonneg_nonneg; lia).
    assert (Q1 : k + 1 <= c_allocated_user (get_cls st_pre c) / S) by (clear -KR; lia).
    assert (M1 : (k + 1) * S <= c_allocated_user (get_cls st_pre c) / S * S) by (apply Z.mul_le_mono_nonneg_r; clear -Q1 SZB; lia).
    pose proof (Z.mul_div_le (c_allocated_user (get_cls st_pre c)) S ltac:(clear -SZB; lia)) as M2.
    split; [exact P0|]. split.
    - rewrite Z.mul_add_distr_r, Z.mul_1_l in M1. rewrite (Z.mul_comm S) in M2. clear -M1 M2 P0 SZB. lia.
    - destruct (proj1 (Z.mod_divide S 16 ltac:(clear; lia)) SM16) as [q Hq]. rewrite Hq.
      replace (k * (q * 16)) with ((k * q) * 16) by (clear; lia). apply Z_mod_mult. }
  destruct KSF as (KS0 & KS1 & KS2).
  assert (GEO : al_space_beg L <= AB /\ AB + S <= al_space_beg L + K_SPACE_SIZE /\ AB mod 16 = 0
                /\ AB + S <= aregion L c + c_allocated_user (get_cls st_pre c) /\ aregion L c <= AB).
  { subst AB. unfold aslot_addr, aregion, K_REGION, K_SPACE_SIZE, K_FREEARR_OFF, K_ALIGN in *. fold S.
    remember (k * S) as KS eqn:HKS. clear HKS.
    change (2^37) with 137438953472. change (2^32) with 4294967296 in *.
    split; [clear -KS0 C16; lia|]. split; [clear -KS1 B1' B2' C16 NSZ; lia|]. split; [| clear -KS0 KS1 B1'; lia].
    clear -SP3 C16 KS2. Z.div_mod_to_equations; lia. }
  destruct GEO as (G1 & G2 & G3 & G4 & G5). unfold K_SPACE_SIZE in G2. change (2^37) with 137438953472 in G2.
  assert (EAB : AB = aslot_addr L c k) by reflexivity. clearbody AB.
  assert (ES : S = size_of_class c) by reflexivity.

  assert (RZC : rz_size n = 16 \/ 32 <= rz_size n) by (clear -RZR RZM; Z.div_mod_to_equations; lia).
  destruct (slot_carveG m_pre AB S n (rz_size n) JK RZC ltac:(clear -N; lia) ltac:(fold S in NSZ; clear -NSZ NS RSR; lia))
    as (b0 & b1 & szh & szl & ctxj & uj & j1 & j2 & HDR & B1 & UJ & LH & TL).
  set (UB := AB + rz_size n) in *. assert (EUB : UB = AB + rz_size n) by reflexivity. clearbody UB.

  set (grz := shlen (rz_size n)). set (g := shlen (n - n mod 8)). set (room := if n mod 8 =? 0 then 0 else 1).
  assert (GR12 : grz = rz_size n / 8 /\ g = (n - n mod 8) / 8).
  { subst grz g. unfold shlen. rewrite !Z.shiftr_div_pow2 by lia. split; reflexivity. }
  destruct GR12 as [GR1 GR2].
  assert (GR3 : 2 <= grz) by (rewrite GR1; generalize RZR; clear; intros; Z.div_mod_to_equations; lia).
  assert (GR4 : 0 <= g) by (rewrite GR2; generalize N; clear; intros; Z.div_mod_to_equations; lia).
  assert (GR5 : 0 <= room <= 1) by (subst room; clear; destruct (n mod 8 =? 0); lia).
  assert (GR6 : grz + g + room <= shlen S).
  { rewrite GR1, GR2. subst room. unfold shlen. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
    fold S in NSZ. fold S in SM16. generalize NSZ NS RSR RSM SM16 RZM RZR N. clear. intros.
    destruct (Z.eqb_spec (n mod 8) 0) as [M0|M0]; Z.div_mod_to_equations; lia. }
  assert (GR7 : shad UB = shad AB + grz).
  { rewrite GR1, EUB. unfold shad, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
    generalize G3 RZM RZR. clear. intros. Z.div_mod_to_equations. lia. }
  assert (GR89 : 0x2008fff7000 <= shad AB /\ shad AB + shlen S <= 0x10007fef8000).
  { unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
    unfold K_SPACE_SIZE, K_SPACE_EXTRA in *. generalize G1 G2 SP1 SP2. clear. intros. Z.div_mod_to_equations. lia. }
  destruct GR89 as [GR8 GR9].
  destruct (shadow_carve m_pre (shad AB) (shlen S) grz g room FSH GR3 GR4 GR6 GR5) as (SHA & SHpre & [sjunk SHU] & SHP & SHsuf).
  rewrite <- GR7 in SHU, SHP, SHsuf.
  set (PG := shad UB + g) in *.

  pose proof RT' as RT0.
  destruct RT0 as (GPG' & GOT' & GOT80' & RIC' & LS1' & REAL' & IMAX4' & FLG5' & FLG' & HPP' & SHB' & CANP' & TI' & TK' & INI2' & LAY' & MCS' & OOM3'
                    & PGC' & HK2' & CF8' & CF34' & CSMT' & T88' & TSD' & LS2' & CT8' & CT').
  pose proof INI2' as INI'. rw_split INI' 1%nat INI1' INIx. clear INIx.
  destruct OOM3' as [oomb' OOM']. rw_split OOM' 2%nat OOMx RSS'. clear OOMx.
  pose proof IMAX4' as IMAX'. rw_split IMAX' 3%nat IMAX3' IMAXx. clear IMAXx.
  pose proof HK2' as HK'. rw_split HK' 1%nat HK1' HKx. clear HKx.
  pose proof T0' as TT0'. rw_split TT0' 1%nat TTctx' TT'.
  destruct (junk_split m_pre (al_t L + 2768) 16 16 CSTATS' ltac:(lia) ltac:(lia)) as [CSa CSb].
  destruct (junk_split m_pre (al_t L + 2768 + 16) 8 8 CSb ltac:(lia) ltac:(lia)) as [CS8 CSc].
  replace (al_t L + 2768 + 16) with (al_t L + 2784) in CS8 by lia.
  replace (al_t L + 2768 + 16 + 8) with (al_t L + 2792) in CSc by lia.
  destruct INST' as (I32' & I48' & I64' & I72' & I112' & I680' & I984' & I40' & I56').
  pose proof ARNGp as ARNGp0. destruct ARNGp as (RIMG' & RT4' & RCTX' & RNO' & RST' & RRI' & RFK' & RSFK' & RDTLS' & RCLS' & RPA' & RSECS' & RPSH').
  destruct (RCLS' c HCK) as (RREG & RSREG & RFA & RSFA).

  destruct (alayout_slot_disj L AB 65536 ALO G1 ltac:(unfold K_SPACE_SIZE, K_FREEARR_OFF, aregion, K_REGION in *; generalize G4 B1' B2' C16 SP1 SZB; clear; intros; change (2^37) with 137438953472; lia) ltac:(clear; lia))
    as (DJT & DJC & DJN & DJS & DJF).
  assert (RUf : rng RNG1 (UB - 16) (n + 16)) by (eapply rng_sub'; [exact RREG|]; generalize G4 G5 B1' RZR N EUB KS0 NSZ NS RSR; clear; intros; lia).
  assert (RABf : rng RNG1 AB 16) by (eapply rng_sub'; [exact RREG|]; generalize G4 G5 B1' RZR N NSZ NS RSR; clear; intros; lia).
  assert (REG8 : aregion L c mod 8 = 0 /\ c_mapped_user (get_cls st_pre c) mod 8 = 0).
  { unfold aregion, K_REGION, K_USER_MAP, K_ALIGN in *. generalize SP3 B4'; clear; intros. Z.div_mod_to_equations; lia. }
  assert (SHM : shad (aregion L c) <= shad AB /\ shad UB + g + room <= shad (aregion L c) + shlen (c_mapped_user (get_cls st_pre c))).
  { rewrite GR7, GR2, GR1. unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
    fold S in NSZ. fold S in SM16. subst room. generalize G4 G5 B1' N NSZ RSR RSM NS RZR RZM SM16 G3 EUB REG8; clear; intros.
    destruct (Z.eqb_spec (n mod 8) 0); Z.div_mod_to_equations; lia. }
  destruct SHM as [SHM1 SHM2].
  assert (RSAf : rng RNG1 (shad AB) 1) by (eapply rng_sub'; [exact RSREG|]; generalize SHM1 SHM2 GR3 GR4 GR5 GR7; clear; intros; lia).
  assert (RSUf : rng RNG1 (shad UB) (shlen (n - n mod 8))).
  { eapply rng_sub'; [exact RSREG|]. fold g. generalize SHM1 SHM2 GR3 GR4 GR5 GR7. clear. intros. lia. }
  assert (RSPf : n mod 8 <> 0 -> rng RNG1 PG 1).
  { intros NE. eapply rng_sub'; [exact RSREG|]. subst PG.
    assert (R1 : room = 1) by (subst room; generalize NE; clear; intros NE; destruct (Z.eqb_spec (n mod 8) 0); [exfalso; exact (NE ltac:(assumption)) | reflexivity]).
    rewrite R1 in SHM2. generalize SHM1 SHM2 GR3 GR4 GR7; clear; intros. lia. }
  assert (SLS : shlen S <= 8192) by (fold S in NSZ; unfold shlen; rewrite Z.shiftr_div_pow2 by (clear; lia); change (2^3) with 8; clear -NSZ; Z.div_mod_to_equations; lia).
  assert (SB34 : 0 <= shlen (n - n mod 8) <= 8192 /\ PG + 1 <= 0x10007fff8000).
  { subst PG. fold g. rewrite GR7. generalize GR4 GR6 GR9 GR3 GR5 SLS; clear; intros; lia. }
  destruct SB34 as [SB3 SB4].
  assert (RCTX4' : rng RNG1 (al_ctx L) 4096) by (eapply rng_sub'; [exact RCTX'|]; clear; lia).
  assert (DJC4 : al_ctx L + 4096 <= AB \/ AB + 65536 <= al_ctx L) by (generalize DJC; clear; intros; lia).
  assert (CNT16 : 0 < cnt <= 16).
  { unfold max_count in CNTB'. generalize POS HCNT CNTB' MCB; clear. destruct (a_cinit st_pre); intros; lia. }
  assert (PGE : PG = shad UB + shlen (n - n mod 8)) by reflexivity.
  assert (RSTK1 : rng RNG1 lo (bv_unsigned sp - lo)) by (eapply rng_fp_le; [exact FPLE | exact RSTK]).

  set (mu0 := c_mapped_user (get_cls st c)) in *.
  assert (OBJ : aregion_info L c = al_space_beg L + 137438953472 + c * 128 /\ aregion L c = al_space_beg L + c * 4294967296
                /\ shad (al_space_beg L + c * 4294967296) + 536870912 <= 17594333495296).
  { unfold aregion_info, aregion, K_REGION, K_SPACE_SIZE, ARI_STRIDE. change (2^37) with 137438953472. change (2^32) with 4294967296.
    split; [reflexivity|]. split; [reflexivity|]. rewrite shad_div. clear -SP1 SP2 C16. unfold ASHOFF, K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^37) with 137438953472 in *.
    Z.div_mod_to_equations. lia. }
  destruct OBJ as (RIE & RBE & SHHI).
  assert (MU41 : munch [(bv_unsigned sp - 3856, bv_unsigned sp - 2272); (al_t L + 208, al_t L + 3168); (AINSTANCE, AINSTANCE + 728);
                        (al_space_beg L + 137438953472 + c * 128, al_space_beg L + 137438953472 + c * 128 + 128);
                        (al_space_beg L + c * 4294967296 + mu0, al_space_beg L + c * 4294967296 + 4294967296);
                        (shad (al_space_beg L + c * 4294967296 + mu0), shad (al_space_beg L + c * 4294967296) + 536870912)]%Z m4 m1).
  { eapply munch_trans; [eapply munch_weaken; [| exact MUc] | eapply munch_weaken; [| exact MU1]];
      unfold sub_fp; cbn [outside]; intros q Hq; rewrite ?RIE, ?RBE in *; unfold K_REGION, acache_addr in *; change (2^32) with 4294967296 in *;
      rewrite ?shlen_div in *; change (4294967296 / 8) with 536870912 in *; clear -Hq HspA C16; lia. }
  assert (WM41 : wmono bsegs m4 m1) by (eapply wmono_trans; [exact WMc | exact WM1]).
  unfold K_SPACE_SIZE, K_SPACE_EXTRA in SP2. change (2^37) with 137438953472 in SP2.
  xport FRa MU41 WM41 ltac:(clear -SPR LO BOT STK3 TL1 TL2 SP1 SP2 C16 SHHI TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold AMALLOC_STACK, AINSTANCE in *; lia).
  xport FR16 MU41 WM41 ltac:(clear -SPR LO BOT STK3 TL1 TL2 SP1 SP2 C16 SHHI TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold AMALLOC_STACK, AINSTANCE in *; lia).
  xport SS MU41 WM41 ltac:(clear -SPR LO BOT STK3 TL1 TL2 SP1 SP2 C16 SHHI TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold AMALLOC_STACK, AINSTANCE in *; lia).
  xport TB MU41 WM41 ltac:(rewrite LTB; clear -SPR LO BOT STK3 TL1 TL2 SP1 SP2 C16 SHHI TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold AMALLOC_STACK, AINSTANCE in *; lia).
  xport FRS MU41 WM41 ltac:(clear -SPR LO BOT STK3 TL1 TL2 SP1 SP2 C16 SHHI TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold AMALLOC_STACK, AINSTANCE in *; lia).

  xport HDR MU1 WM1 ltac:(clear -HspA DJT SPR SP2 G1 G2 EUB RZR N NSZ NS RSR LO BOT STK3 C16; unfold acache_addr, AMALLOC_STACK, K_SPACE_SIZE in *; lia).
  xport UJ MU1 WM1 ltac:(clear -HspA DJT SPR SP2 G1 G2 EUB RZR N NSZ NS RSR LO BOT STK3 C16; unfold acache_addr, AMALLOC_STACK, K_SPACE_SIZE in *; lia).
  xport SHA MU1 WM1 ltac:(cbv delta [g grz room PG] in *; clear -HspA SPR GR1 GR2 GR3 GR4 GR5 GR6 GR7 GR8 GR9 LO BOT STK3 TL1 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport SHU MU1 WM1 ltac:(cbv delta [g grz room PG] in *; clear -HspA SPR GR1 GR2 GR3 GR4 GR5 GR6 GR7 GR8 GR9 SB3 LO BOT STK3 TL1 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  assert (SHP1 : n mod 8 <> 0 -> rw_cells bsegs m1 PG [C1 (Z_to_bv 8 250)]).
  { intros NE. specialize (SHP ltac:(subst room; generalize NE; clear; intros NE; destruct (Z.eqb_spec (n mod 8) 0); [exfalso; exact (NE ltac:(assumption)) | reflexivity])).
    xport SHP MU1 WM1 ltac:(cbv delta [g grz room PG] in *; clear -HspA SPR GR1 GR2 GR3 GR4 GR5 GR6 GR7 GR8 GR9 SB3 SB4 LO BOT STK3 TL1 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia). exact SHP. }
  assert (LH1 : 16 < rz_size n -> rw_cells bsegs m1 AB [C8 j1; C8 j2]).
  { intros R16. pose proof (proj1 (LH R16)) as LH0.
    xport LH0 MU1 WM1 ltac:(clear -HspA DJT SPR SP2 G1 G2 EUB RZR N NSZ NS RSR LO BOT STK3 C16; unfold acache_addr, AMALLOC_STACK, K_SPACE_SIZE in *; lia). exact LH0. }
  xport GOT' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport GOT80' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport REAL' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport SHB' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport CANP' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport HPP' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport CSMT' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport FLG5' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport FLG' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport HK1' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport LS1' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport LS2' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport LAY' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport MCS' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport CF34' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport INI1' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport RSS' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport IMAX3' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport TI' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport TK' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport T88' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, ATP88, AMALLOC_STACK in *; lia).
  xport TSD' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, ATSD, AMALLOC_STACK in *; lia).
  xport CT' MU1 WM1 ltac:(ub CL5; clear -HspA Y SPR TL1 CL1 CL2 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb CTXi CBND CBNDa CBNDb; unfold acache_addr, AMALLOC_STACK, AIMG_HI in *; lia).
  xport CT8' MU1 WM1 ltac:(ub CL5; clear -HspA Y SPR TL1 CL1 CL2 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb CTXi CBND CBNDa CBNDb; unfold acache_addr, AMALLOC_STACK, AIMG_HI in *; lia).
  xport TTctx' MU1 WM1 ltac:(clear -HspA SPR TL1 TL2 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport UNW' MU1 WM1 ltac:(clear -HspA SPR TL1 TL2 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport STATS' MU1 WM1 ltac:(rewrite LSJ'; clear -HspA SPR TL1 TL2 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, ASTATS_WORDS, AMALLOC_STACK in *; lia).
  assert (DEP1 : ADEPOT DI L m1).
  { eapply (adi_frame DI); [exact HD' | exact MU1 | exact WM1 |]. unfold acache_addr.
    repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq; ub DL7; ub DL8; clear -Hq Y Y0 HspA SPR TL1 TL2 DL1 DL2 DL3 DL4 DL5 DL6 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb NODi NBND NBNDa NBNDb STOi SBND SBNDa SBNDb; unfold AMALLOC_STACK, AIMG_HI in *; lia|]).
    apply Forall_nil. }

  assert (PF : pfactsG (bv_unsigned sp) (al_t L) (al_space_beg L) c mu0 ATOP lo).
  { unfold pfactsG. pose proof (ao_t L ALO) as OT. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in OT.
    unfold AMALLOC_STACK, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN, K_FREEARR_OFF, K_USER_MAP in *. change (2^37) with 137438953472 in *.
    ub TSP. generalize LO BOT SP47 STK2 STK3 OT SP1 SP2 SAL C16 A1 A2 A4 Y. clear. intros.
    repeat match goal with H : _ /\ _ |- _ => destruct H end.
    repeat split; first [reflexivity | assumption | lia | Z.div_mod_to_equations; lia]. }
  assert (MUall : munch [(bv_unsigned sp - 4096, bv_unsigned sp); (al_t L + 208, al_t L + 3169); (AINSTANCE, AINSTANCE + 728);
                         (al_space_beg L + 137438953472 + c * 128, al_space_beg L + 137438953472 + c * 128 + 128);
                         (al_space_beg L + c * 4294967296 + mu0, al_space_beg L + c * 4294967296 + 4294967296);
                         (shad (al_space_beg L + c * 4294967296 + mu0), shad (al_space_beg L + c * 4294967296) + 536870912)]%Z m m_pre).
  { eapply munch_trans; [eapply munch_weaken; [| exact MU4] | eapply munch_weaken; [| exact MUc]];
      unfold sub_fp; cbn [outside]; intros q Hq; rewrite ?RIE, ?RBE in *; unfold K_REGION in *; change (2^32) with 4294967296 in *;
      rewrite ?shlen_div in *; change (4294967296 / 8) with 536870912 in *; clear -Hq HspA; lia. }
  assert (WMall : wmono bsegs m m_pre) by (eapply wmono_trans; [exact WM4 | exact WMc]).

  assert (BB : forall b, In b (x_busy X) ->
      al_space_beg L <= xb_alloc L b /\ xb_alloc L b + size_of_class (xb_class b) <= al_space_beg L + 137438953472
      /\ (xb_alloc L b + size_of_class (xb_class b) <= al_space_beg L + c * 4294967296 + mu0 \/ al_space_beg L + c * 4294967296 + 4294967296 <= xb_alloc L b)).
  { intros b Hb. destruct (BUSY b Hb) as [CLB _].
    destruct (PERC (xb_class b) CLB) as (Q1 & Q2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & QR).
    pose proof (size_of_class_facts (xb_class b) CLB) as [QS _].
    assert (KB : 0 <= xb_slot b < ndist st (xb_class b)).
    { apply QR. apply in_app_iff. right. apply in_app_iff. right. unfold busy_slots. apply in_map_iff. exists b. split; [reflexivity|].
      apply filter_In. split; [exact Hb| apply Z.eqb_refl]. }
    pose proof (slot_in_region L st (xb_class b) (xb_slot b) ltac:(clear -QS; lia) (proj1 Q1) KB) as (P5 & P4 & P0).
    unfold xb_alloc. unfold K_NUM_CLASSES in CLB. unfold K_FREEARR_OFF in Q2.
    destruct (Z.eq_dec (xb_class b) c) as [EC|NC].
    - rewrite EC in P5, P4, Q1, Q2 |- *. rewrite RBE in P5, P4. change (c_mapped_user (get_cls st c)) with mu0 in Q1, Q2.
      clear -P5 P4 Q1 Q2 A1 A2 C16. unfold K_FREEARR_OFF in *. lia.
    - pose proof (region_other_geo L c (xb_class b) ALO ltac:(clear -C16; lia) CLB NC) as (R1 & R2 & R3 & _). rewrite RBE in R2.
      clear -P5 P4 Q1 Q2 R1 R2 R3 A1. lia. }
  pose proof (ao_fake L ALO) as FKO. unfold aobj in FKO. pose proof (ao_res L ALO) as ORS. unfold aobj in ORS. pose proof (ao_space L ALO) as RSP.
  pose proof (ad_fake_res L ALO) as D_f_res. pose proof (ad_t_fake L ALO) as D_t_f. pose proof (ad_dtls_res L ALO) as D_d_res. pose proof (ad_t_dtls L ALO) as D_t_d.
  pose proof (ao_dtls L ALO) as ODT. unfold aobj in ODT. unfold adisj in D_f_res, D_t_f, D_d_res, D_t_d.
  assert (FKD : forall cls FA sz, In (mkABlock (ABFake cls) FA sz) LB -> al_fake L <= FA /\ 0 <= sz /\ FA + sz <= al_fake L + 11571200)
    by (intros cls FA sz Hin; exact (proj1 (proj2 BL) cls FA sz Hin)).
  assert (PRES : aheap_pres CI LB (bv_unsigned sp) m m_pre).
  { intros a Ha CL. split; [| intros Hw; apply WMall; exact Hw].
    apply MUall. rewrite wa_unsigned by exact Ha.
    destruct CL as [STa | [CIa | [BLK | SH]]].
    - eapply disjoint_outside; [eapply (Q_stack _ _ _ _ _ _ _ PF a 1); clear -STa; lia | clear; lia].
    - destruct CIa as (iv & Hiv & R). pose proof (proj1 (Forall_forall _ _) CI_OK iv Hiv) as (Q1 & Q2 & Q3).
      pose proof (proj1 (Forall_forall _ _) CI_OK2 iv Hiv) as Q4. cbn [fst snd] in *.
      eapply disjoint_outside; [eapply (Q_img _ _ _ _ _ _ _ PF a 1); unfold AIMG_HI in *; clear -R Q1 Q3 Q4; lia | clear; lia].
    - destruct BLK as (b & Hb & R). destruct b as [[p|cls] A n']; cbn [ab_addr ab_size] in R.
      + destruct (proj1 BL p A n' Hb) as [(xb & Hxb & Sb & Ub & Nb)|(mb0 & ms0 & Lp & EUA & Gs)].
        * destruct (BB xb Hxb) as (Bb1 & Bb2 & Bb3).
          pose proof (awf_fits L st X xb WF Hxb) as FIT. unfold xb_fits in FIT. rewrite Sb in FIT. unfold xb_user in Ub. subst A n'.
          eapply disjoint_outside; [eapply (Q_slot _ _ _ _ _ _ _ PF a 1) | clear; lia]; clear -R Bb1 Bb2 Bb3 FIT; lia.
        *
          cbn [sec_wf1] in Gs. destruct Gs as (Gs1 & Gs2 & Gs3 & Gs4 & Gs5 & Gs6 & (Ct & Cc & Cr & Cp & Cn & Cs & Cf & Cd)).
          pose proof (sec_facts n' ltac:(clear -Gs5; lia) Gs6) as SF. subst A. unfold SEC_UOFF, K_HIGH_MEM in *.
          unfold ablk, KLS, AIMG_HI in Gs2.
          eapply disjoint_outside; [eapply (Q_obj _ _ _ _ _ _ _ PF a 1) | clear; lia]; clear -R Gs2 Gs3 Gs4 Gs5 SF Ct Cr RSP ORS; lia.
      + destruct (FKD cls A n' Hb) as (K1 & K2 & K3). atop_facts.
        eapply disjoint_outside; [eapply (Q_obj _ _ _ _ _ _ _ PF a 1) | clear; lia];
          clear -R K1 K3 FKO D_t_f D_f_res RSP OFKi OFKs OFKsa OFKsb; lia.
    - destruct SH as (a' & Ha' & ->).
      destruct Ha' as [STa | [CIa | FK]].
      + eapply disjoint_outside; [eapply (Q_shad_hi _ _ _ _ _ _ _ PF a'); unfold AMALLOC_STACK in *; clear -STa LO BOT STK3; lia | clear; lia].
      + destruct CIa as (iv & Hiv & R). pose proof (proj1 (Forall_forall _ _) CI_OK iv Hiv) as (Q1 & Q2 & Q3). cbn [fst snd] in *.
        eapply disjoint_outside; [eapply (Q_shad_img _ _ _ _ _ _ _ PF a'); unfold AIMG_HI in *; clear -R Q1 Q3; lia | clear; lia].
      + destruct FK as (cls & FA & sz & Hin & R). destruct (FKD cls FA sz Hin) as (K1 & K2 & K3). atop_facts.
        eapply disjoint_outside; [eapply (Q_shad_obj _ _ _ _ _ _ _ PF a') | clear; lia]; clear -R K1 K3 FKO D_f_res RSP OFKi OFKs OFKsa OFKsb; lia. }
  assert (HFKp : AFK L LB m_pre).
  { eapply (hf_frame _ HL L LB m m_pre); [exact HFK | exact MUall | exact WMall | exact (Q_tfs _ _ _ _ _ _ _ PF) |].
    unfold fake_untouched. pose proof (ao_t L ALO) as OT. unfold aobj in OT.
    assert (SHF : 2148262400 <= shad (al_fake L) /\ shad (al_fake L) + shlen 11571200 <= 17594332446720
                  /\ (shad (al_space_beg L + c * 4294967296) + 536870912 <= shad (al_fake L)
                      \/ shad (al_fake L) + shlen 11571200 <= shad (al_space_beg L + c * 4294967296 + mu0))
                  /\ shad (al_space_beg L + c * 4294967296) <= shad (al_space_beg L + c * 4294967296 + mu0)
                  /\ 2201439137792 <= shad (al_space_beg L + c * 4294967296)).
    { rewrite !shad_div, !shlen_div. unfold ASHOFF in *. destruct PF as (_ & _ & (F1 & F2 & F3 & F4 & F5 & F6) & _).
      clear -FKO F1 F2 F3 F4 F5 F6 D_f_res RSP OFKi OFKs OFKsa OFKsb. Z.div_mod_to_equations. dlia. }
    destruct SHF as (SF1 & SF2 & SF3 & SF4 & SF5).
    unfold AMALLOC_STACK, AINSTANCE in *. destruct PF as (PF1 & PF2 & PF3 & PF4).
    repeat (apply Forall_cons; [cbn [fst snd];
      clear -LO BOT STK3 SP47 STK2 OT FKO ORS RSP ODT D_f_res D_t_f D_d_res D_t_d C16 PF3 PF4 SF1 SF2 SF3 SF4 SF5 SHHI TL1 TBND TBNDa TBNDb TIMG TIMGa TIMGb OFKi OFKs OFKsa OFKsb DBND DBNDa DBNDb DIMG DIMGa DIMGb;
      repeat (split; [lia|]); lia |]).
    apply Forall_nil. }

  eapply evtF_mono.
  { eapply (malloc_tail_gen DI L RNG1 ra sp gp tp spA t0d t1d t2d a1d a2d a3d a4d a5d a6d a7d t3d t4d t5d t6d
              s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0A s1A s2A s3A s4A s5A s0i F fc m1
              n (al_t L) c cnt AB UB PG room lo b0 b1 szh szl ctxj (1 + Z.of_nat (length trc))
              (Z_to_bv 64 (max_count st_pre c)) (Z_to_bv 64 S) stj1 j1 j2 (Z_to_bv 8 250) sj' sjunk uj fr0 junk2 tb trc).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => exact ST1
         | |- mem_inv _ _ => exact MI1
         | |- allocA_cells _ _ _ => unfold allocA_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end)
         | |- poison_cells _ => unfold poison_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end)
         | |- ADEPOT _ _ _ => exact DEP1
         | |- In _ _ => exact TRU
         | |- u64arr _ _ (_ + 2800) _ => exact STATS'
         | |- u64arr _ _ _ _ => exact TB
         | |- map _ _ = _ => exact TRF
         | |- (16 < _) -> _ => exact LH1
         | |- ~ _ -> rng _ _ _ => exact RSPf
         | |- ~ _ -> _ => exact SHP1
         | |- is_primary _ = _ => exact PRIM
         end.
    all: try lazymatch goal with
         | |- rw_cells _ _ (_ + -16) _ => exact HDR
         | |- rw_cells _ _ (shad _) [C1 _] => exact SHA
         | |- rw_cells _ _ (shad _) [CB _ _] => exact SHU
         | |- rw_cells _ _ _ [CB _ _] => exact UJ
         | |- rw_cells _ _ (_ + 2784) _ => exact STS1
         | |- rw_cells _ _ (_ + 208 + _ * 80) _ => exact CR1
         | |- rw_cells _ _ _ _ => assumption
         | |- rng _ _ _ => assumption
         | |- _ \/ _ => first [exact DJT | exact DJN | exact DJS | exact DJC4 | unboxed CL5 | unboxed DL7 | unboxed DL8 | unboxed DL9 | unboxed DL10]
         | |- @eq Z _ _ => first [assumption | reflexivity | exact PGE | subst room; reflexivity]
         | |- @eq word _ _ => first [assumption | reflexivity]
         | |- @eq nat _ _ => first [exact LSJ' | exact LTB | assumption]
         end.
    all: try assumption.
    all: try (generalize N NR LO BOT SP47 STK1 STK2 STK3 SP1 SP2 SP4 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6
                         G1 G2 G3 G4 G5 EUB ES SM16 NSZ NS RSR RZR GR3 GR7 GR8 GR9 SB3 SB4 B1 POS HCNT CNT16 KS0 KS1 HC0 C16 LTRC RA4 HspA;
              clear; intros; rewrite ?HC0 in *; unfold AIMG_HI, AMALLOC_STACK, AREQMAX, UDEPTH, K_SPACE_SIZE, K_SPACE_EXTRA in *; lia).
    all: try (eapply rng_sub'; [exact RSTK1|]; clear -LO SP47 BOT STK3 SPR; unfold AMALLOC_STACK in *; lia).
    all: try (clear -LTRC; lia).
    all: match goal with |- ?G => idtac "REMT" G end. }

  cbv beta. intros ms' PM.
  unfold amalloc_post_x. cbn [snd fst]. split.
  {
    pose proof PM as PM0. unfold malloc_post_gen in PM0.
    destruct PM0 as (id0 & t0e & t1e & t2e & a1e & a2e & a3e & a4e & a5e & a6e & a7e & t3e & t4e & t5e & t6e & m5 & sj5 & stj5 & EMS & MUt & _).

    assert (AXFall : axflags L st_pre m_pre).
    { intros c' Hc' NC'. destruct (Z.eq_dec c' c) as [->|NE]; [exact (AXFp NC')|].
      pose proof (C6F4 c' Hc' NC') as F4. unfold axflag in *.
      replace (exh_mem c' st_pre) with (exh_mem c' st)
        by (destruct EXHp as [E|E]; [symmetry; apply exh_mem_eq_list; exact E| rewrite (exh_mem_eq_list c' _ _ E); symmetry; apply exh_mem_clear_other; exact NE]).
      eapply cells_frameO; [exact F4| exact MUc|]. cbn [cells_size csize Nat.add]. intros x Hx. cbn [outside].
      assert (RIEj : forall j, aregion_info L j = al_space_beg L + 137438953472 + j * 128) by (intros j; unfold aregion_info, K_SPACE_SIZE, ARI_STRIDE; change (2^37) with 137438953472; reflexivity).
      rewrite (RIEj c') in Hx. rewrite (RIEj c). unfold aregion, K_REGION, AINSTANCE, K_NUM_CLASSES in *. change (2^32) with 4294967296.
      pose proof atop_range as ATRx.
      assert (SHT : shad (al_space_beg L + c * 4294967296) + shlen 4294967296 <= 17594333495296)
        by (rewrite shad_div, shlen_div; unfold ASHOFF, K_SPACE_SIZE, K_SPACE_EXTRA in *; change (2^37) with 137438953472 in *; clear -SP1 SP2 C16 ATRx; Z.div_mod_to_equations; lia).
      rewrite ?unsigned_lit by (clear -SPR HspA LO BOT STK3; lia).
      pose proof TSP as TSPx. unbox TSPx.
      unfold K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^37) with 137438953472 in *.
      clear -Hx Hc' NE C16 SP1 SP2 TL1 TL2 TL4 LO BOT STK3 HspA SHT A1 A2 ATRx SPR TSPx. unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in *. repeat split; lia. }
    destruct (c6_frame L RESV RNG1 st_pre m_pre m1 _ ALO ROK AXGp AXFall MU1) as [G1x F1x].
    { rewrite ?unsigned_lit by (clear -SPR HspA LO BOT STK3; lia).
      apply Forall_cons; [unfold c6_piece; cbn [fst snd]; intros _; left; clear -LO BOT STK3 HspA; lia|].
      apply Forall_cons; [unfold c6_piece, acache_addr; cbn [fst snd]; intros _; right; left; clear -C16; lia|].
      apply Forall_cons; [unfold c6_piece; cbn [fst snd]; intros _; right; left; clear; lia| apply Forall_nil]. }
    destruct (c6_frame L RESV RNG1 st_pre m1 m5 _ ALO ROK G1x F1x MUt) as [G5x F5x].
    { pose proof (ao_res L ALO) as (_ & _ & ORSx & _). pose proof (ao_space L ALO) as RSPx. pose proof atop_range as ATRx.
      assert (UBN : UB + n <= AB + S) by (clear -EUB NS NSZ RSR ES; lia).
      repeat (apply Forall_cons; [unfold c6_piece; cbn [fst snd]; intros NEk;
        first [ left; clear -LO BOT; lia
              | right; left; clear -C16; lia
              | do 2 right; left; clear -G1 G2 EUB UBN RSPx RZR SZB ES; subst S; lia
              | do 3 right; left; clear -NEk GR3 GR4 GR5 GR6 GR7 GR8 GR9 PGE SB3; subst g grz; lia
              | do 5 right; left; clear; lia
              | do 6 right; left; clear; lia
              | do 7 right; left; clear; lia ]|]).
      apply Forall_nil. }
    rewrite EMS. unfold c6_at. cbn [ms_mem MS].
    destruct G5x as (XC5 & EC5 & ER5 & ECL5).
    split.
    - split; [exact XC5|]. split; [exact EC5|]. split; [exact ER5|].
      eapply (emb_clr_sub RESV st_pre); [reflexivity| | exact ECL5].
      apply (achunks_new_prim st_pre _ (a_next (apop c st_pre)) c n); reflexivity.
    - intros c' Hc' NC'. exact (F5x c' Hc' NC'). }
  unfold apop. rewrite HCNT, !a_next_put_cls, !a_live_put_cls.
  apply (malloc_post_gen_shift DI L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc n (al_t L) c cnt AB UB PG room lo b1 _ _ uj m_pre m1 ms') in PM;
    [| eapply munch_weaken; [| exact MU1]; unfold sub_fp, acache_addr; cbn [outside]; intros q Hq; clear -Hq HspA; lia | exact WM1].
  cbv delta [PG g grz room] in PM, SHpre, SHsuf. subst UB. subst AB.
  eapply (amalloc_post_shiftG CI _ L RNG RNG1 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st st_pre LB n lo m m_pre); [| exact FPLE |].
  { eapply (store_prim DI AQ ASEC AFK HL CI CI_OK L RNG1 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m_pre st_pre LB X_pre n lo c cnt k b1
              (Z_to_bv 64 (max_count st_pre c)) (Z_to_bv 64 (size_of_class c)) uj).
    all: try exact PM.
    all: try lazymatch goal with
         | |- is_primary _ = _ => exact PRIM
         | |- ann_ov _ = None => rewrite L2; exact OVF
         | |- alayout_ok _ => exact ALO
         | |- arng _ _ _ => exact ARNGp0
         | |- AFK _ _ _ => idtac
         | |- AREP _ _ _ _ _ => exact ARp
         | |- ablocks _ _ _ _ => eapply ablocks_xbusyG; [exact BL | exact XB | exact L1]
         | |- nth_error _ _ = _ => exact NK
         | |- busy_of _ _ _ = _ => exact NB
         | |- (16 < _) -> _ => let R16 := fresh in intros R16; exact (proj2 (LH R16))
         | |- junk_at _ (_ + 2768) _ => exact CSa
         | |- junk_at _ (_ + 2792) _ => exact CSc
         | |- junk_at _ _ _ => first [exact TL | rewrite ES; exact TL]
         | |- fill_at _ (_ + 1) _ _ => exact SHpre
         | |- fill_at _ _ _ _ => first [exact SHsuf | rewrite ES; exact SHsuf]
         end.
    all: try assumption.
    all: try reflexivity.
    all: try (generalize N KR B1 LO BOT STK3 POS; clear; intros; unfold AMALLOC_STACK in *; lia).
    all: try exact HFKp.
    all: match goal with |- ?G => idtac "REMS" G end. }
  exact PRES.
Qed.
End S.
End CANSEC1.
End AMallocPG_x.

Module AAlignedPG_x.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Exec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Tac. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ITreeA. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.SysStepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW.BImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABytes.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ASecFacts.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AMalloc_iface.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ADepot_iface.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARep.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ALayout.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AHeapP.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepKit.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepFrame.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepExt.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepExt2.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit2.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AModelFacts.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.APrimFacts.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apoison.TwinB.F_apoison.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc1.TwinB.F_aalloc1.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc2.TwinB.F_aalloc2. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_amalloc_icpt.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_amalloc_pre.TwinB.F_amalloc_pre.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc2.TwinB.F_aalloc2g.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc3.TwinB.F_aalloc3g.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aaligned_tail.TwinB.F_amalloc_tailg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_amalloc_arep.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepStore.TwinB.ARepStore.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepStore.TwinB.ARepStoreG. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARefill_iface.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARefillP.TwinB.ARefillP.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ACallocG.TwinB.ACallocG.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc1.TwinB.F_aalloc1_16.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc2.TwinB.F_aalloc2g_16.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc3.TwinB.F_aalloc3g_16. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aaligned_iseg.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aaligned_pre.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aaligned_tail.TwinB.F_aaligned_tail.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepStore.TwinB.ARepStoreG_16.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

 Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AAlignedPG.TwinB.AMallocPG. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AEmbRep.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFrameD.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AEmbFrame.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_arefill.TwinB.F_arefill_x. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARefill_iface_x.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARefillP_x.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARefillP.TwinB.ARefillP_e. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_acache_x.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ACallocG.TwinB.ACallocG_x. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_amalloc_null.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ANullKit.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AC6Frame.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ANullPres.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AAlignedPG.TwinB.AAlignedPG. Import AMallocPG_x. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aaligned_null.TwinB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC1. Context {rc : runConstT} {ov : annOV}.

Local Lemma ablk_int : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6492160 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
Local Lemma aobj_int : forall a n, aobj a n -> 0x10000 <= n ->
  6492160 <= a /\ a + n <= ATOP /\ exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof.
  intros a n H Hn. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. destruct H as (H1 & H2 & H3 & H4 & H5).
  split; [lia|]. split; [lia|]. destruct H4; [exists 0 | exists 1]; lia.
Qed.
Local Lemma aobj4_int : forall a, aobj a 4096 ->
  4096 <= a /\ a + 4096 <= ATOP
  /\ (exists k, 0 <= k <= 1 /\ a + 4096 <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a)
  /\ (exists j, 0 <= j <= 1 /\ a + 4096 <= 65536 + j * 18446744073709551616 /\ 6492160 * j <= a).
Proof.
  intros a H. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. destruct H as (H1 & H2 & H3 & H4 & H5).
  split; [lia|]. split; [lia|]. split; [destruct H4; [exists 0 | exists 1]; lia | destruct H5 as [_ [H5|H5]]; [exists 0 | exists 1]; lia].
Qed.

Local Ltac dlia := repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
Section S.
Variable DI : ADepotIface.
Variables (AQ ASEC : alayout -> astate -> aconc -> amem -> Prop) (AFK : alayout -> list ablock -> amem -> Prop).
Hypothesis HL : ahole_laws (AH DI AQ ASEC AFK).
Hypothesis HLD : ahole_lawsD (AH DI AQ ASEC AFK).
Hypothesis EXHW : exh_first_stmt.
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI) CI.

Hypothesis CI_OK2 : Forall (fun iv => snd iv <= AINSTANCE \/ AINSTANCE + 728 <= fst iv) CI.

Hypothesis CI_OK3 : Forall (fun iv => (snd iv <= AEMB \/ AEMB + 56 <= fst iv) /\ (snd iv <= 0x15dee0 \/ 0x15dee1 <= fst iv)) CI.

Theorem aaligned_prim16_x : forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (n lo : Z) (tr : list Z) (RESV : list (Z * Z)),
  ann_ov (a_next st) = None ->

  is_primary16 n = true -> n mod 16 = 0 ->

  AHEAP_P (AH DI AQ ASEC AFK) L RNG st LB m ->
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - 4608 ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 16 -> a1 = Z_to_bv 64 n -> 1 <= n <= AREQMAX ->
  aunw m L RNG lo AALIGNED_PC sp s0 ra tr ->
  bv_unsigned s0 <> bv_unsigned sp + 8 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AALIGNED_PC ->
  bv_unsigned sp mod 16 = 0 ->
  rng RNG lo (bv_unsigned sp - lo) ->
  aresv_ok L RESV ->

  bv_unsigned fc < 32 -> axg RESV RNG st m -> axflags L st m -> (let '(_, cap0, _) := a_emb st in cap0 <= 2 ^ 23) ->
  (exists e0 : word, rw_cells bsegs m AERRNO [C4 e0]) ->
  implS bsegs RNG (aembed ATOP (aaligned16x ATOP RESV st n))
        (epostF (amalloc_post_x CI (AHEAP_P (AH DI AQ ASEC AFK)) L RESV RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB n lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AALIGNED_SYM) fc None m (seg_rom bsegs)).
Proof.
  intros until RESV. intros OVF PRIM N16 AHP MI ST BOT LO TP Ha0 Ha1 NR AUNW S0NE RA4 RANE SP16 RSTK ROK FC C6G C6F CAPB ERRC.
  assert (N : 1 <= n <= AREQMAX) by exact NR. assert (N1 : 1 <= n) by (clear -NR; lia).

  assert (EXARM : exists trc,
      ((bv_unsigned sp + 16 < al_top L /\ uchain m (al_top L) AALIGNED_PC (bv_unsigned sp) (bv_unsigned s0) 28%nat tr /\ (length tr <= 28)%nat /\ trc = bv_unsigned ra :: tr
        /\ rng RNG lo (al_top L - lo))
       \/ (al_top L <= bv_unsigned sp + 16 /\ bv_unsigned sp < 2^47 /\ trc = []))
      /\ In (AALIGNED_PC :: trc) (al_U L) /\ (length trc <= 29)%nat /\ bv_unsigned sp < 2^47).
  { pose proof (alayout_stack L (proj1 AHP)) as (K1 & K2 & K3).
    destruct AUNW as [(T1 & U1 & L1 & I1 & R1)|(T1 & T2 & I1)].
    - exists (bv_unsigned ra :: tr). split; [left; split; [exact T1|]; split; [exact U1|]; split; [exact L1|]; split; [reflexivity| exact R1]|].
      split; [exact I1|]. split; [cbn [length]; clear -L1; lia | clear -T1 K2; lia].
    - exists (@nil Z). split; [right; split; [exact T1|]; split; [exact T2| reflexivity]|]. split; [exact I1|]. split; [cbn [length]; clear; lia | exact T2]. }
  destruct EXARM as (trc & ARM & TRU & LTRC & SP47).
  destruct AHP as (ALO & ARNG & [X [AR BL]] & HFK).
  remember (class_id (needed16 n)) as c eqn:HC0. symmetry in HC0.
  pose proof (prim16_facts' n N1 PRIM) as (NS & RZR & RZE & RZM & RLR & RSR & RSM & NSR).
  pose proof (prim_class_facts16 n c N1 PRIM HC0) as (C16 & NSZ & SM16 & SMALL & MCB). clear SMALL.
  pose proof (cls_facts c C16) as (SZB & _ & _ & _).
  assert (HCK : 1 <= c < K_NUM_CLASSES) by (unfold K_NUM_CLASSES; clear -C16; lia).
  assert (NM8 : needed16 n mod 8 = 0) by (rewrite NS; clear -RSM RZM; Z.div_mod_to_equations; lia).

  pose proof AR as AR0. destruct AR0 as (WF & RT & INST & THR & CLS & HQ & HS & HD & HRO & RT2 & AVL & RT3).
  destruct THR as (T0 & T40 & CACHES & CSTATS & [sj [STATS LSJ]] & UNW).
  pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVE & FRESH & UNIQ).
  destruct (PERC c HCK) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & LENF & LENC & CNTB & ND & RANGE).
  pose proof (alayout_space L ALO) as (SP1 & SP2 & SP3 & SP4).
  pose proof (alayout_t L ALO) as (TL1 & TL2 & TL3 & TL4).
  pose proof (alayout_ctx L ALO) as (CL1 & CL2 & CL3 & CL4 & CL5).
  pose proof (alayout_depot L ALO) as (DL1 & DL2 & DL3 & DL4 & DL5 & DL6 & DL7 & DL8 & DL9 & DL10).
  pose proof (aobj4_int _ (ao_t L ALO)) as (_ & _ & (kT & TBND & TBNDa & TBNDb) & (jT & TIMG & TIMGa & TIMGb)).
  pose proof (aobj_int _ _ (ao_ctx L ALO) ltac:(clear; lia)) as (CTXi & _ & (kC & CBND & CBNDa & CBNDb)).
  pose proof (aobj_int _ _ (ao_nodes L ALO) ltac:(clear; lia)) as (NODi & _ & (kN & NBND & NBNDa & NBNDb)).
  pose proof (aobj_int _ _ (ao_store L ALO) ltac:(clear; lia)) as (STOi & _ & (kR & SBND & SBNDa & SBNDb)).
  pose proof (aobj_int _ _ (ao_fake L ALO) ltac:(clear; lia)) as (OFKi & _ & (kF & OFKs & OFKsa & OFKsb)).
  pose proof (aobj4_int _ (ao_dtls L ALO)) as (_ & _ & (kD & DBND & DBNDa & DBNDb) & (jD & DIMG & DIMGa & DIMGb)).
  pose proof (alayout_stack L ALO) as (STK1 & STK2 & STK3).
  pose proof (alayout_res_disj L ALO) as [SCX TSP].
  pose proof RT as RT0.
  destruct RT0 as (GPG & GOT & GOT80 & RIC & LS1 & REAL & IMAX4 & FLG5 & FLG & HPP & SHB & CANP & TI & TK & INI2 & LAY & MCS & OOM3
                    & PGC & HK2 & CF8 & CF34 & CSMT & T88 & TSD & LS2 & CT8 & CT).
  pose proof INI2 as INI. rw_split INI 1%nat INI1 INIx. clear INIx.
  destruct OOM3 as [oomb OOM]. rw_split OOM 2%nat OOMx RSS. clear OOMx.
  pose proof IMAX4 as IMAX. rw_split IMAX 3%nat IMAX3 IMAXx. clear IMAXx.
  pose proof T0 as TT0. rw_split TT0 1%nat TTctx TT.
  pose proof ARNG as ARNG0. destruct ARNG as (RIMG & RT4 & RCTX & RNO & RSTO & RRI & RFK & RSFK & RDTLS & RCLS).
  assert (RCTX4 : rng RNG (al_ctx L) 4096) by (eapply rng_sub'; [exact RCTX|]; clear; lia).
  word_range sp SPR.
  box CL5. box DL7. box DL8. box DL9. box DL10. box TSP. box SCX.

  rewrite (aaligned16x_eq RESV st n c HC0).

  iprefix. eapply evtF_cut.
  { eapply (aligned_pre_spec16 L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n (al_t L) lo (al_top L) (al_bot L) tr trc).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => exact ST
         | |- mem_inv _ _ => exact MI
         | |- allocA_cells _ _ _ => unfold allocA_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end)
         | |- poison_cells _ => unfold poison_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end)
         | |- u64arr _ _ _ _ => exact STATS
         | |- (_ /\ _) \/ (_ /\ _) => exact ARM
         | |- _ \/ _ => unboxed CL5
         | |- @eq word _ _ => first [exact TP | exact Ha0 | exact Ha1]
         | |- is_primary16 _ = _ => exact PRIM
         end.
    all: try lazymatch goal with
         | |- rw_cells _ _ _ _ => assumption
         | |- rng _ _ _ => assumption
         end.
    all: try assumption.
    all: try (generalize N NR LO BOT SP47 STK1 STK2 STK3 SP1 SP2 SP4 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 LTRC RA4 SP16;
              clear; intros; unfold AIMG_HI, AMALLOC_STACK, AREQMAX, UDEPTH in *; lia).
    all: match goal with |- ?G => idtac "REMPRE" G end. }
  cbv beta. intros ms4 P4. unfold aligned_pre_post16 in P4.
  destruct P4 as (spA & t0c & t1c & t2c & a4c & a5c & a6c & a7c & t3c & t4c & t5c & t6c & s0A & s1A & s2A & s3A & s4A & s5A & s6A & fr0 & junk0 & junk2 & tb & m4
                  & -> & HspA & MU4 & WM4 & MI4 & ST4 & FRa & FR16 & FRP0 & SS & TB & LTB & TRF & FRS & UW4).
  apply evtF_done.
  assert (AR4 : AREP (AH DI AQ ASEC AFK) L st X m4).
  { eapply (AREP_frame_pre _ HL L st X m m4); [exact ALO | exact AR | exact MU4 | exact WM4 | | exact UW4].
    apply Forall_cons; [unfold apre; cbn [fst snd]; intros _; left; unfold AMALLOC_STACK in *; clear -LO BOT STK3; lia|].
    apply Forall_cons; [unfold apre; cbn [fst snd]; intros _; right; split; reflexivity| apply Forall_nil]. }

  destruct (c6_frame L RESV RNG st m m4 _ ALO ROK C6G C6F MU4) as [C6G4 C6F4].
  { apply Forall_cons; [unfold c6_piece; cbn [fst snd]; intros _; left; unfold AMALLOC_STACK in *; clear -LO BOT STK3; lia|].
    apply Forall_cons; [unfold c6_piece; cbn [fst snd]; intros _; right; left; clear; lia| apply Forall_nil]. }

  eapply (@calloc_arep_gen_x _ _ _ HL HLD _ RESV _ _ L RNG _ _ gp tp t0c t1c t2c _ _ _ _ _ _ a4c a5c a6c a7c _ _ _ _ _ _ _ _ _ _ t3c t4c t5c t6c F fc m4 st X c lo (needed16 n)
            ALO ARNG0 AR4 MI4).
  all: try lazymatch goal with
       | |- arng _ _ _ => exact ARNG0
       | |- stk _ _ _ _ => rewrite unsigned_lit by (clear -SPR HspA LO BOT STK3; unfold AMALLOC_STACK in *; lia);
                           replace (bv_unsigned spA + -128) with (bv_unsigned sp - 2304) by (clear -HspA; lia); exact ST4
       | |- ATOP <= _ => clear -LO BOT STK3; unfold AMALLOC_STACK in *; lia
       | |- _ <= bv_unsigned _ - _ => rewrite unsigned_lit by (clear -SPR HspA LO BOT STK3; unfold AMALLOC_STACK in *; lia);
                                    clear -LO HspA BOT STK3; unfold AMALLOC_STACK in *; lia
       | |- @eq word _ _ => first [exact TP | reflexivity]
       | |- 16 <= _ <= 65536 => clear -NSR; lia
       | |- _ mod 8 = 0 => exact NM8
       | |- class_id _ = _ => exact HC0
       | |- rng _ _ _ => rewrite unsigned_lit by (clear -SPR HspA LO BOT STK3; unfold AMALLOC_STACK in *; lia);
                         eapply rng_sub'; [exact RSTK|]; clear -LO HspA SP47 BOT STK3; unfold AMALLOC_STACK in *; lia
       | |- exh_first_stmt => exact EXHW
       | |- aresv_ok _ _ => exact ROK
       | |- bv_unsigned _ < 2 ^ 63 => rewrite unsigned_lit by (clear -SPR HspA LO BOT STK3; unfold AMALLOC_STACK in *; lia); clear -SP47 HspA; lia
       | |- bv_unsigned _ < 32 => exact FC
       | |- _ -> axflag _ _ _ _ => intros NC24x; exact (C6F4 c HCK NC24x)
       | |- axg _ _ _ _ => exact C6G4
       | |- context [a_emb _] => exact CAPB
       | |- forall _, _ => idtac
       end.
  1: {
       intros st2 RNG' ms' RF. unfold aret_xf in RF. cbv zeta in RF. pose proof atop_range as ATR.
       pose proof C6G4 as (_ & ECp & _ & ECLp). unfold emb_cells in ECp. unfold emb_clr in ECLp.
       destruct (a_emb st) as [[d0 cap0] sz0] eqn:EA. destruct (a_emb st2) as [[d2 cap2] sz2] eqn:EA2.
       destruct RF as (FPLE & t0r & t1r & t2r & a1r & a2r & a3r & a4r & a5r & a6r & a7r & t3r & t4r & t5r & t6r & mr
                       & -> & MIr & STr & STEQ & ARr & ARNGr & AXFr & AXGr & (d1 & cap1 & MUr & PV1 & PV2 & TOP1)).
       assert (USP : bv_unsigned (Z_to_bv 64 (bv_unsigned spA + -128)) = bv_unsigned sp - 2304)
         by (rewrite unsigned_lit by (clear -SPR HspA LO BOT ATR; lia); clear -HspA; lia).
       rewrite USP in MUr, STr.

       assert (B0 : bufok RESV st d0 cap0).
       { unfold bufok. destruct (Z.eqb_spec cap0 0) as [E0|NZ]; [left; lia|]. right.
         destruct ECp as (_ & _ & _ & _ & _ & _ & _ & _ & TOP & _). split; [exact TOP|]. destruct ECLp as [Q|Q]; [exfalso; exact (NZ Q)| exact Q]. }
       assert (B1 : bufok RESV st d1 cap1).
       { destruct (Z_le_gt_dec cap1 0) as [LE|GT]; [left; exact LE|]. destruct PV1 as [[E1 E2]|AV]; [rewrite E1, E2; exact B0|].
         right. split; [destruct TOP1 as [Q|Q]; [lia| exact Q]| exact AV]. }
       assert (B2 : bufok RESV st d2 cap2).
       { destruct PV2 as [[E1 E2]|AV]; [rewrite E1, E2; exact B0|].
         pose proof AXGr as (_ & EC2 & _). unfold emb_cells in EC2. rewrite EA2 in EC2. destruct (Z.eqb_spec cap2 0) as [E0|NZ]; [left; lia|]. right.
         destruct EC2 as (_ & _ & _ & _ & _ & _ & _ & _ & TOP & _). split; [exact TOP| exact AV]. }

       set (SPc := bv_unsigned sp - 2304) in *.
       assert (SPHIc : ATOP <= SPc) by (subst SPc; clear -LO BOT; lia).
       assert (SPHI : ATOP <= bv_unsigned sp) by (clear -LO BOT; lia).
       set (Wf := [(SPc - 2096, SPc); (al_t L + 208, al_t L + 2768); (aregion_info L c, aregion_info L c + 8);
                   (aregion_info L c + 68, aregion_info L c + 69); (AEMB, AEMB + 56); (d0, d0 + cap0); (d1, d1 + cap1); (d2, d2 + cap2)]%Z).
       change (munch Wf m4 mr) in MUr.
       assert (PCSf : Forall (nf_piece L RESV st SPc c) Wf).
       { assert (BK : forall d cap, bufok RESV st d cap -> nf_piece L RESV st SPc c (d, d + cap)).
         { intros d cap [B|[Bt Ba]] LT; cbn [fst snd] in LT; [lia|]. unfold nf_kind. cbn [fst snd]. do 4 right. left.
           replace (d + cap - d) with cap by lia. split; assumption. }
         subst Wf. repeat (apply Forall_cons); try apply Forall_nil; try (apply BK; assumption); intros _; unfold nf_kind; cbn [fst snd].
         - left. subst SPc. clear -LO BOT. lia.
         - right; left. clear. lia.
         - right; right; left. clear. lia.
         - right; right; left. clear. lia.
         - right; right; right; left. clear. lia. }
       assert (OUTS : forall x, SPc <= x -> outside Wf x)
         by (intros x Hx; apply (nf_outside L RESV st SPc c ALO ROK HCK SPHIc Wf x PCSf); left; exact Hx).

       apply rw_cells_of_u64arr in TB. rewrite LTB in TB.
       assert (FRar : rw_cells bsegs mr (bv_unsigned spA + -128)
                        [CB 8 fr0; C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 32); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6A; C8 s5A;
                         C8 s4A; C8 s3A; C8 s2A; C8 s1A; C8 s0A; C8 (Z_to_bv 64 0x3e238)]).
       { replace (bv_unsigned spA + -128) with (bv_unsigned sp - 2304) by (clear -HspA; lia).
         eapply cells_frameO; [exact FRa| exact MUr|]. intros x Hx. apply OUTS. subst SPc. clear -Hx. lia. }
       assert (FR16r : rw_cells bsegs mr (bv_unsigned sp + -2176) [C8 (Z_to_bv 64 16); C8 (Z_to_bv 64 n); C8 sp; C8 (Z_to_bv 64 0x5f5f8)])
         by (eapply cells_frameO; [exact FR16| exact MUr|]; intros x Hx; apply OUTS; subst SPc; clear -Hx; lia).
       assert (FRP0r : rw_cells bsegs mr (bv_unsigned sp + -2144) [CB 8 junk0])
         by (eapply cells_frameO; [exact FRP0| exact MUr|]; intros x Hx; apply OUTS; subst SPc; clear -Hx; lia).
       assert (SSr : rw_cells bsegs mr (bv_unsigned sp + -2136) [C8 (Z_to_bv 64 (bv_unsigned sp + -2136 + 16)); C8 (Z_to_bv 64 (1 + Z.of_nat (length trc)))])
         by (eapply cells_frameO; [exact SS| exact MUr|]; intros x Hx; apply OUTS; subst SPc; clear -Hx; lia).
       assert (TBr : rw_cells bsegs mr (bv_unsigned sp + -2136 + 16) [CB (8 * 255) (u64s tb)])
         by (eapply cells_frameO; [exact TB| exact MUr|]; intros x Hx; apply OUTS; subst SPc; clear -Hx; lia).
       assert (FRSr : rw_cells bsegs mr (bv_unsigned sp + -80) [C8 sp; CB 8 junk2; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
         by (eapply cells_frameO; [exact FRS| exact MUr|]; intros x Hx; apply OUTS; subst SPc; clear -Hx; lia).
       destruct ERRC as [e0 ERR0].
       assert (ERR4 : rw_cells bsegs m4 AERRNO [C4 e0]).
       { eapply cells_frameO; [exact ERR0| exact MU4|]. cbn [cells_size csize Nat.add]. intros x Hx. cbn [outside].
         unfold AERRNO, ATP in Hx. clear -Hx ATR LO BOT TIMG TIMGa TIMGb. repeat split; lia. }
       assert (ERRr : rw_cells bsegs mr AERRNO [C4 e0]).
       { eapply cells_frameO; [exact ERR4| exact MUr|]. cbn [cells_size csize Nat.add]. intros x Hx.
         assert (BI : forall d cap, bufok RESV st d cap -> ~ (d <= x < d + cap)).
         { intros d cap [B|[_ AV]]; [clear -B; lia|]. unfold avoids_all in AV. rewrite forallb_app in AV. apply andb_prop in AV as [AV _].
           destruct ROK as (PCI & _). apply (avoids_pcov_out RESV d cap 0x10000 AIMG_HI x PCI AV). unfold AIMG_HI, AERRNO, ATP in *. clear -Hx. lia. }
         pose proof (BI _ _ B0) as Q0. pose proof (BI _ _ B1) as Q1. pose proof (BI _ _ B2) as Q2.
         subst Wf. cbn [outside]. unfold aregion_info, K_SPACE_SIZE, ARI_STRIDE. change (2^37) with 137438953472.
         unfold AEMB, AERRNO, ATP in *. subst SPc.
         clear -Hx Q0 Q1 Q2 ATR LO BOT TIMG TIMGa TIMGb SP1 C16. repeat split; lia. }
       pose proof ARr as (_ & RTr & _).
       destruct RTr as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & OOM3r & _).
       destruct OOM3r as [oombr OOMr]. rw_split OOMr 2%nat OOMxr RSSr. clear RSSr.

       apply implS_ret.
       replace (ret_pc (Z_to_bv 64 0x3d8f8)) with (Z_to_bv 64 0x3d8f8) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
       pose proof ARNGr as (RIMGr & _).
       assert (RSTKr : rng RNG' lo (bv_unsigned sp - lo)) by (eapply rng_fp_leG; [exact FPLE | exact RSTK]).
       eapply evtF_cut.
       { eapply (allocN_spec RNG' spA gp tp t0r t1r t2r _ _ a1r a2r a3r a4r a5r a6r a7r _ _ _ _ _ _ _ _ _ _ t3r t4r t5r t6r
                   s0A s1A s2A s3A s4A s5A s6A s7 s8 s9 s10 s11 (Z_to_bv 64 0x3e238) _ _ fr0 oombr F fc mr lo);
           first [ exact FRar | exact MIr | exact OOMxr | exact RIMGr
                 | replace (bv_unsigned spA + -128) with (bv_unsigned sp - 2304) by (clear -HspA; lia); exact STr
                 | eapply rng_sub'; [exact RSTKr|]; clear -HspA LO; lia
                 | clear -BOT ATR; lia
                 | clear -LO HspA; lia ]. }
       cbv beta. intros ms1 P1.
       destruct P1 as (t0n & t1n & t2n & a1n & a2n & a3n & a4n & a5n & a6n & a7n & t3n & t4n & t5n & t6n & m1 & -> & MU1 & WM1 & MI1 & ST1 & OOM1).
       assert (OUT1 : forall x, AIMG_HI <= x -> outside [(AOOM, AOOM + 1)]%Z x)
         by (intros x Hx; cbn [outside]; unfold AOOM, AIMG_HI in *; clear -Hx; lia).
       assert (FR16n : rw_cells bsegs m1 (bv_unsigned sp + -2176) [C8 (Z_to_bv 64 16); C8 (Z_to_bv 64 n); C8 sp; C8 (Z_to_bv 64 0x5f5f8)])
         by (eapply cells_frameO; [exact FR16r| exact MU1|]; intros x Hx; apply OUT1; unfold AIMG_HI; clear -Hx ATR LO BOT; lia).
       assert (FRP0n : rw_cells bsegs m1 (bv_unsigned sp + -2144) [CB 8 junk0])
         by (eapply cells_frameO; [exact FRP0r| exact MU1|]; intros x Hx; apply OUT1; unfold AIMG_HI; clear -Hx ATR LO BOT; lia).
       assert (SSn : rw_cells bsegs m1 (bv_unsigned sp + -2136) [C8 (Z_to_bv 64 (bv_unsigned sp + -2136 + 16)); C8 (Z_to_bv 64 (1 + Z.of_nat (length trc)))])
         by (eapply cells_frameO; [exact SSr| exact MU1|]; intros x Hx; apply OUT1; unfold AIMG_HI; clear -Hx ATR LO BOT; lia).
       assert (TBn : rw_cells bsegs m1 (bv_unsigned sp + -2120) [CB (8 * 255) (u64s tb)]).
       { replace (bv_unsigned sp + -2120) with (bv_unsigned sp + -2136 + 16) by (clear; lia).
         eapply cells_frameO; [exact TBr| exact MU1|]. intros x Hx. apply OUT1. unfold AIMG_HI. clear -Hx ATR LO BOT. lia. }
       assert (FRSn : rw_cells bsegs m1 (bv_unsigned sp + -80) [C8 sp; CB 8 junk2; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
         by (eapply cells_frameO; [exact FRSr| exact MU1|]; intros x Hx; apply OUT1; unfold AIMG_HI; clear -Hx ATR LO BOT; lia).
       assert (ERRn : rw_cells bsegs m1 AERRNO [C4 e0]).
       { eapply cells_frameO; [exact ERRr| exact MU1|]. cbn [cells_size csize Nat.add]. intros x Hx. cbn [outside]. unfold AOOM, AERRNO, ATP in *. clear -Hx. lia. }

       replace (ret_pc (Z_to_bv 64 0x3e238)) with (Z_to_bv 64 0x3e238) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
       assert (EspA : spA = Z_to_bv 64 (bv_unsigned sp + -2176)).
       { enough (E : Z_to_bv 64 (bv_unsigned spA) = Z_to_bv 64 (bv_unsigned sp + -2176)) by (rewrite Z_to_bv_bv_unsigned in E; exact E).
         apply Z_to_bv_eqm. rewrite HspA. zeq. }
       rewrite HspA in ST1. replace (bv_unsigned sp - 2176) with (bv_unsigned sp + -2176) in ST1 by (clear; lia). rewrite EspA.
       eapply evtF_mono.
       { eapply (icptN16_spec RNG' sp gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s7 s8 s9 s10 s11 _ _ _ _ ra s0 s1 s2 s3 s4 s5 s6 F fc m1 lo n junk0 junk2 e0);
           first [ exact ST1 | exact MI1 | exact TP | exact ERRn | exact FR16n | exact FRP0n | exact FRSn | exact RIMGr | exact RSTKr
                 | eexists; split; [exact SSn| reflexivity]
                 | eexists; split; [exact TBn| reflexivity]
                 | clear -BOT ATR; lia
                 | clear -LO; lia ]. }
       cbv beta. intros ms2 P2.
       destruct P2 as (t0e & t1e & t2e & a1e & a2e & a3e & a4e & a5e & a6e & a7e & t3e & t4e & t5e & t6e & m2 & -> & MU2 & WM2 & MI2 & ST2 & ERR2).

       pose proof (munch_app _ _ _ _ _ MU1 MU2) as MUn. pose proof (wmono_trans bsegs _ _ _ WM1 WM2) as WMn.
       assert (AXFSr : axflags L st2 mr).
       { intros c' Hc' NC'. destruct (Z.eq_dec c' c) as [->|NE]; [exact AXFr|].
         pose proof (C6F4 c' Hc' NC') as F4. unfold axflag in *.
         assert (EXE : exh_mem c' st2 = exh_mem c' st).
         { destruct STEQ as [[_ ->]|[_ [e2 ->]]]; [apply init_cache_exh|]. rewrite exh_mem_set_emb, (exh_mem_set_other c c' _ NE). apply init_cache_exh. }
         rewrite EXE. eapply cells_frameO; [exact F4| exact MUr|]. cbn [cells_size csize Nat.add]. intros x Hx.
         apply (nf_flag_outside L RESV st SPc c ALO ROK HCK SPHIc Wf c' x PCSf Hc' NE). clear -Hx. lia. }
       destruct (c6_frame L RESV RNG' st2 mr m2 _ ALO ROK AXGr AXFSr MUn) as [C6G2 C6F2].
       { cbn [app]. apply Forall_cons; [unfold c6_piece, AOOM; cbn [fst snd]; intros _; do 8 right; left; clear; lia|].
         apply Forall_cons; [unfold c6_piece; cbn [fst snd]; intros _; left; clear -LO BOT; lia|].
         apply Forall_cons; [unfold c6_piece; cbn [fst snd]; intros _; do 9 right; clear; lia| apply Forall_nil]. }

       assert (AR2 : AREP (AH DI AQ ASEC AFK) L st2 X m2).
       { eapply (AREP_frame_null _ HL L st2 X mr m2 (bv_unsigned sp - 32) ALO ARr); [| exact WMn| clear -LO BOT; lia|].
         { eapply munch_weaken; [| exact MUn]. unfold sub_fp, AOOM, AERRNO, ATP. cbn [app outside]. intros q Hq. clear -Hq. repeat split; lia. }
         exists (Z_to_bv 8 1). eapply cells_frameO; [exact OOM1| exact MU2|]. cbn [cells_size csize Nat.add]. intros x Hx. cbn [outside].
         unfold AOOM, AERRNO, ATP in *. clear -Hx ATR LO BOT. repeat split; lia. }
       assert (LIVE2 : a_live st2 = a_live st).
       { pose proof (init_cache_fields st) as (E1 & _). destruct STEQ as [[_ ->]|[_ [e2 ->]]]; [exact E1|]. rewrite <- E1. destruct (init_cache st); reflexivity. }
       pose proof (ablocks_same L st st2 X X LB BL eq_refl LIVE2) as BL2.
       pose proof (munch_app _ _ _ _ _ MU4 (munch_app _ _ _ _ _ MUr MUn)) as MUt.
       assert (PCSt : Forall (nf_piece L RESV st (bv_unsigned sp) c)
                        ([(bv_unsigned sp - 2352, bv_unsigned sp); (al_t L + 3168, al_t L + 3169)] ++ Wf ++ [(AOOM, AOOM + 1)] ++ [(bv_unsigned sp - 2192, bv_unsigned sp - 2176); (AERRNO, AERRNO + 4)])%Z).
       { apply Forall_app. split; [| apply Forall_app; split].
         - apply Forall_cons; [intros _; unfold nf_kind; cbn [fst snd]; left; clear -LO BOT; lia|].
           apply Forall_cons; [intros _; unfold nf_kind; cbn [fst snd]; right; left; clear; lia| apply Forall_nil].
         - eapply Forall_impl; [| exact PCSf]. intros iv K. apply (nf_piece_SP L RESV st SPc (bv_unsigned sp) c iv); [subst SPc; clear; lia| exact K].
         - cbn [app]. apply Forall_cons; [intros _; unfold nf_kind, AOOM; cbn [fst snd]; do 5 right; left; clear; lia|].
           apply Forall_cons; [intros _; unfold nf_kind; cbn [fst snd]; left; clear -LO BOT; lia|].
           apply Forall_cons; [intros _; unfold nf_kind; cbn [fst snd]; do 6 right; clear; lia| apply Forall_nil]. }
       destruct (nf_fake L RESV st (bv_unsigned sp) c _ ALO ROK HCK SPHI (nzl_pieces _ _ _ _ _ _ PCSt)) as (D72 & FU & D48).
       pose proof (hfD _ HLD L LB m m2 _ HFK (munch_nzl _ _ _ MUt) D72 FU D48) as HFK2.
       assert (PRESe : aheap_pres_e CI LB (bv_unsigned sp) m m2).
       { intros a Ha CL NERR.
         pose proof (nf_client_outside L RESV st X (bv_unsigned sp) c ALO ROK HCK SPHI CI CI_OK CI_OK3 WF LB _ a BL PCSt Ha CL NERR) as OUT.
         assert (E : m2 (wa a) = m (wa a)) by (apply MUt; rewrite wa_unsigned by exact Ha; exact OUT).
         split; [exact E|]. intros Hw. rewrite (AFrameD.TwinB.wview_agree bsegs m m2 (wa a) E). exact Hw. }

       unfold amalloc_post_x. cbn [fst snd]. split.
       { unfold c6_at. cbn [ms_mem]. split; [exact C6G2| exact C6F2]. }
       split; [exact FPLE|]. do 14 eexists. exists m2. split; [reflexivity|]. split; [exact MI2|]. split; [exact ST2|]. split; [exact PRESe|].
       split; [| exact ERR2].
       split; [exact ALO|]. split; [exact ARNGr|]. split; [exists X; split; [exact AR2| exact BL2]| exact HFK2]. }

  intros st_pre X_pre RNG1 m_pre cnt k ms1 CRET. destruct CRET as (CRET & EMBp & EXHp & AXFp & AXGp). unfold calloc_retG in CRET.
  destruct CRET as (FPLE & ARp & ARNGp & HCNT & POS & NK & NB & KR & XB & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & MUc & WMc & MIp
                    & t0d & t1d & t2d & a1d & a2d & a3d & a4d & a5d & a6d & a7d & t3d & t4d & t5d & t6d & m1 & stj1 & -> & MU1 & WM1 & MI1 & ST1 & CR1 & STS1).
  rewrite ?unsigned_lit in MUc by (clear -SPR HspA LO BOT STK3; unfold AMALLOC_STACK in *; lia).
  rewrite ?unsigned_lit in MU1 by (clear -SPR HspA LO BOT STK3; unfold AMALLOC_STACK in *; lia).
  rewrite ?unsigned_lit in ST1 by (clear -SPR HspA LO BOT STK3; unfold AMALLOC_STACK in *; lia).
  replace (bv_unsigned spA + -128) with (bv_unsigned sp - 2304) in ST1 by (clear -HspA; lia).
  cbn beta iota. apply implS_ret.
  replace (ret_pc (Z_to_bv 64 0x3d8f8)) with (Z_to_bv 64 0x3d8f8) by (symmetry; apply ret_pc_even; [lia|reflexivity]).

  pose proof ARp as AR0. destruct AR0 as (WF' & RT' & INST' & THR' & CLS' & HQ' & HS' & HD' & HRO' & RT2' & AVL' & RT3').
  destruct THR' as (T0' & T40' & CACHES' & CSTATS' & [sj' [STATS' LSJ']] & UNW').
  pose proof WF' as WF0. destruct WF0 as (SBE' & PAE' & SAL' & SLO' & SHI' & PERC' & OUTC' & BUSY' & LIVE' & FRESH' & UNIQ').
  destruct (PERC' c HCK) as (B1' & B2' & B3' & B4' & B5' & B6' & B7' & LENF' & LENC' & CNTB' & ND' & RANGE').
  destruct (kit_cache_pop _ L st_pre X_pre m_pre c cnt ARp HCK HCNT POS) as (k' & chunks & NK' & _ & _ & CR & CH & LCH & NTH & JK & FSH).
  assert (EK : k' = k) by (rewrite NK in NK'; injection NK'; intros E; symmetry; exact E). subst k'.

  set (S := size_of_class c) in *.
  set (AB := aslot_addr L c k) in *.
  assert (KSF : 0 <= k * S /\ k * S + S <= c_allocated_user (get_cls st_pre c) /\ (k * S) mod 16 = 0).
  { unfold ndist in KR. fold S in KR. fold S in SZB. fold S in SM16.
    assert (P0 : 0 <= k * S) by (clear -KR SZB; apply Z.mul_nonneg_nonneg; lia).
    assert (Q1 : k + 1 <= c_allocated_user (get_cls st_pre c) / S) by (clear -KR; lia).
    assert (M1 : (k + 1) * S <= c_allocated_user (get_cls st_pre c) / S * S) by (apply Z.mul_le_mono_nonneg_r; clear -Q1 SZB; lia).
    pose proof (Z.mul_div_le (c_allocated_user (get_cls st_pre c)) S ltac:(clear -SZB; lia)) as M2.
    split; [exact P0|]. split.
    - rewrite Z.mul_add_distr_r, Z.mul_1_l in M1. rewrite (Z.mul_comm S) in M2. clear -M1 M2 P0 SZB. lia.
    - destruct (proj1 (Z.mod_divide S 16 ltac:(clear; lia)) SM16) as [q Hq]. rewrite Hq.
      replace (k * (q * 16)) with ((k * q) * 16) by (clear; lia). apply Z_mod_mult. }
  destruct KSF as (KS0 & KS1 & KS2).
  assert (GEO : al_space_beg L <= AB /\ AB + S <= al_space_beg L + K_SPACE_SIZE /\ AB mod 16 = 0
                /\ AB + S <= aregion L c + c_allocated_user (get_cls st_pre c) /\ aregion L c <= AB).
  { subst AB. unfold aslot_addr, aregion, K_REGION, K_SPACE_SIZE, K_FREEARR_OFF, K_ALIGN in *. fold S.
    remember (k * S) as KS eqn:HKS. clear HKS.
    change (2^37) with 137438953472. change (2^32) with 4294967296 in *.
    split; [clear -KS0 C16; lia|]. split; [clear -KS1 B1' B2' C16 NSZ; lia|]. split; [| clear -KS0 KS1 B1'; lia].
    clear -SP3 C16 KS2. Z.div_mod_to_equations; lia. }
  destruct GEO as (G1 & G2 & G3 & G4 & G5). unfold K_SPACE_SIZE in G2. change (2^37) with 137438953472 in G2.
  assert (EAB : AB = aslot_addr L c k) by reflexivity. clearbody AB.
  assert (ES : S = size_of_class c) by reflexivity.

  assert (RZC : rz_size n = 16 \/ 32 <= rz_size n) by (clear -RZR RZM; Z.div_mod_to_equations; lia).
  destruct (slot_carveG m_pre AB S n (rz_size n) JK RZC ltac:(clear -N; lia) ltac:(fold S in NSZ; clear -NSZ NS RSR; lia))
    as (b0 & b1 & szh & szl & ctxj & uj & j1 & j2 & HDR & B1 & UJ & LH & TL).
  set (UB := AB + rz_size n) in *. assert (EUB : UB = AB + rz_size n) by reflexivity. clearbody UB.

  set (grz := shlen (rz_size n)). set (g := shlen (n - n mod 8)). set (room := if n mod 8 =? 0 then 0 else 1).
  assert (GR12 : grz = rz_size n / 8 /\ g = (n - n mod 8) / 8).
  { subst grz g. unfold shlen. rewrite !Z.shiftr_div_pow2 by lia. split; reflexivity. }
  destruct GR12 as [GR1 GR2].
  assert (GR3 : 2 <= grz) by (rewrite GR1; generalize RZR; clear; intros; Z.div_mod_to_equations; lia).
  assert (GR4 : 0 <= g) by (rewrite GR2; generalize N; clear; intros; Z.div_mod_to_equations; lia).
  assert (GR5 : 0 <= room <= 1) by (subst room; clear; destruct (n mod 8 =? 0); lia).
  assert (GR6 : grz + g + room <= shlen S).
  { rewrite GR1, GR2. subst room. unfold shlen. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
    fold S in NSZ. fold S in SM16. generalize NSZ NS RSR RSM SM16 RZM RZR N. clear. intros.
    destruct (Z.eqb_spec (n mod 8) 0) as [M0|M0]; Z.div_mod_to_equations; lia. }
  assert (GR7 : shad UB = shad AB + grz).
  { rewrite GR1, EUB. unfold shad, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
    generalize G3 RZM RZR. clear. intros. Z.div_mod_to_equations. lia. }
  assert (GR89 : 0x2008fff7000 <= shad AB /\ shad AB + shlen S <= 0x10007fef8000).
  { unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
    unfold K_SPACE_SIZE, K_SPACE_EXTRA in *. generalize G1 G2 SP1 SP2. clear. intros. Z.div_mod_to_equations. lia. }
  destruct GR89 as [GR8 GR9].
  destruct (shadow_carve m_pre (shad AB) (shlen S) grz g room FSH GR3 GR4 GR6 GR5) as (SHA & SHpre & [sjunk SHU] & SHP & SHsuf).
  rewrite <- GR7 in SHU, SHP, SHsuf.
  set (PG := shad UB + g) in *.

  pose proof RT' as RT0.
  destruct RT0 as (GPG' & GOT' & GOT80' & RIC' & LS1' & REAL' & IMAX4' & FLG5' & FLG' & HPP' & SHB' & CANP' & TI' & TK' & INI2' & LAY' & MCS' & OOM3'
                    & PGC' & HK2' & CF8' & CF34' & CSMT' & T88' & TSD' & LS2' & CT8' & CT').
  pose proof INI2' as INI'. rw_split INI' 1%nat INI1' INIx. clear INIx.
  destruct OOM3' as [oomb' OOM']. rw_split OOM' 2%nat OOMx RSS'. clear OOMx.
  pose proof IMAX4' as IMAX'. rw_split IMAX' 3%nat IMAX3' IMAXx. clear IMAXx.
  pose proof HK2' as HK'. rw_split HK' 1%nat HK1' HKx. clear HKx.
  pose proof T0' as TT0'. rw_split TT0' 1%nat TTctx' TT'.
  destruct (junk_split m_pre (al_t L + 2768) 16 16 CSTATS' ltac:(lia) ltac:(lia)) as [CSa CSb].
  destruct (junk_split m_pre (al_t L + 2768 + 16) 8 8 CSb ltac:(lia) ltac:(lia)) as [CS8 CSc].
  replace (al_t L + 2768 + 16) with (al_t L + 2784) in CS8 by lia.
  replace (al_t L + 2768 + 16 + 8) with (al_t L + 2792) in CSc by lia.
  destruct INST' as (I32' & I48' & I64' & I72' & I112' & I680' & I984' & I40' & I56').
  pose proof ARNGp as ARNGp0. destruct ARNGp as (RIMG' & RT4' & RCTX' & RNO' & RST' & RRI' & RFK' & RSFK' & RDTLS' & RCLS' & RPA' & RSECS' & RPSH').
  destruct (RCLS' c HCK) as (RREG & RSREG & RFA & RSFA).

  destruct (alayout_slot_disj L AB 65536 ALO G1 ltac:(unfold K_SPACE_SIZE, K_FREEARR_OFF, aregion, K_REGION in *; generalize G4 B1' B2' C16 SP1 SZB; clear; intros; change (2^37) with 137438953472; lia) ltac:(clear; lia))
    as (DJT & DJC & DJN & DJS & DJF).
  assert (RUf : rng RNG1 (UB - 16) (n + 16)) by (eapply rng_sub'; [exact RREG|]; generalize G4 G5 B1' RZR N EUB KS0 NSZ NS RSR; clear; intros; lia).
  assert (RABf : rng RNG1 AB 16) by (eapply rng_sub'; [exact RREG|]; generalize G4 G5 B1' RZR N NSZ NS RSR; clear; intros; lia).
  assert (REG8 : aregion L c mod 8 = 0 /\ c_mapped_user (get_cls st_pre c) mod 8 = 0).
  { unfold aregion, K_REGION, K_USER_MAP, K_ALIGN in *. generalize SP3 B4'; clear; intros. Z.div_mod_to_equations; lia. }
  assert (SHM : shad (aregion L c) <= shad AB /\ shad UB + g + room <= shad (aregion L c) + shlen (c_mapped_user (get_cls st_pre c))).
  { rewrite GR7, GR2, GR1. unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
    fold S in NSZ. fold S in SM16. subst room. generalize G4 G5 B1' N NSZ RSR RSM NS RZR RZM SM16 G3 EUB REG8; clear; intros.
    destruct (Z.eqb_spec (n mod 8) 0); Z.div_mod_to_equations; lia. }
  destruct SHM as [SHM1 SHM2].
  assert (RSAf : rng RNG1 (shad AB) 1) by (eapply rng_sub'; [exact RSREG|]; generalize SHM1 SHM2 GR3 GR4 GR5 GR7; clear; intros; lia).
  assert (RSUf : rng RNG1 (shad UB) (shlen (n - n mod 8))).
  { eapply rng_sub'; [exact RSREG|]. fold g. generalize SHM1 SHM2 GR3 GR4 GR5 GR7. clear. intros. lia. }
  assert (RSPf : n mod 8 <> 0 -> rng RNG1 PG 1).
  { intros NE. eapply rng_sub'; [exact RSREG|]. subst PG.
    assert (R1 : room = 1) by (subst room; generalize NE; clear; intros NE; destruct (Z.eqb_spec (n mod 8) 0); [exfalso; exact (NE ltac:(assumption)) | reflexivity]).
    rewrite R1 in SHM2. generalize SHM1 SHM2 GR3 GR4 GR7; clear; intros. lia. }
  assert (SLS : shlen S <= 8192) by (fold S in NSZ; unfold shlen; rewrite Z.shiftr_div_pow2 by (clear; lia); change (2^3) with 8; clear -NSZ; Z.div_mod_to_equations; lia).
  assert (SB34 : 0 <= shlen (n - n mod 8) <= 8192 /\ PG + 1 <= 0x10007fff8000).
  { subst PG. fold g. rewrite GR7. generalize GR4 GR6 GR9 GR3 GR5 SLS; clear; intros; lia. }
  destruct SB34 as [SB3 SB4].
  assert (RCTX4' : rng RNG1 (al_ctx L) 4096) by (eapply rng_sub'; [exact RCTX'|]; clear; lia).
  assert (DJC4 : al_ctx L + 4096 <= AB \/ AB + 65536 <= al_ctx L) by (generalize DJC; clear; intros; lia).
  assert (CNT16 : 0 < cnt <= 16).
  { unfold max_count in CNTB'. generalize POS HCNT CNTB' MCB; clear. destruct (a_cinit st_pre); intros; lia. }
  assert (PGE : PG = shad UB + shlen (n - n mod 8)) by reflexivity.
  assert (RSTK1 : rng RNG1 lo (bv_unsigned sp - lo)) by (eapply rng_fp_le; [exact FPLE | exact RSTK]).

  set (mu0 := c_mapped_user (get_cls st c)) in *.
  assert (OBJ : aregion_info L c = al_space_beg L + 137438953472 + c * 128 /\ aregion L c = al_space_beg L + c * 4294967296
                /\ shad (al_space_beg L + c * 4294967296) + 536870912 <= 17594333495296).
  { unfold aregion_info, aregion, K_REGION, K_SPACE_SIZE, ARI_STRIDE. change (2^37) with 137438953472. change (2^32) with 4294967296.
    split; [reflexivity|]. split; [reflexivity|]. rewrite shad_div. clear -SP1 SP2 C16. unfold ASHOFF, K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^37) with 137438953472 in *.
    Z.div_mod_to_equations. lia. }
  destruct OBJ as (RIE & RBE & SHHI).
  assert (MU41 : munch [(bv_unsigned sp - 3888, bv_unsigned sp - 2304); (al_t L + 208, al_t L + 3168); (AINSTANCE, AINSTANCE + 728);
                        (al_space_beg L + 137438953472 + c * 128, al_space_beg L + 137438953472 + c * 128 + 128);
                        (al_space_beg L + c * 4294967296 + mu0, al_space_beg L + c * 4294967296 + 4294967296);
                        (shad (al_space_beg L + c * 4294967296 + mu0), shad (al_space_beg L + c * 4294967296) + 536870912)]%Z m4 m1).
  { eapply munch_trans; [eapply munch_weaken; [| exact MUc] | eapply munch_weaken; [| exact MU1]];
      unfold sub_fp; cbn [outside]; intros q Hq; rewrite ?RIE, ?RBE in *; unfold K_REGION, acache_addr in *; change (2^32) with 4294967296 in *;
      rewrite ?shlen_div in *; change (4294967296 / 8) with 536870912 in *; clear -Hq HspA C16; lia. }
  assert (WM41 : wmono bsegs m4 m1) by (eapply wmono_trans; [exact WMc | exact WM1]).
  unfold K_SPACE_SIZE, K_SPACE_EXTRA in SP2. change (2^37) with 137438953472 in SP2.
  xport FRa MU41 WM41 ltac:(clear -SPR LO BOT STK3 TL1 TL2 SP1 SP2 C16 SHHI TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold AMALLOC_STACK, AINSTANCE in *; lia).
  xport FR16 MU41 WM41 ltac:(clear -SPR LO BOT STK3 TL1 TL2 SP1 SP2 C16 SHHI TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold AMALLOC_STACK, AINSTANCE in *; lia).
  xport FRP0 MU41 WM41 ltac:(clear -SPR LO BOT STK3 TL1 TL2 SP1 SP2 C16 SHHI TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold AMALLOC_STACK, AINSTANCE in *; lia).
  xport SS MU41 WM41 ltac:(clear -SPR LO BOT STK3 TL1 TL2 SP1 SP2 C16 SHHI TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold AMALLOC_STACK, AINSTANCE in *; lia).
  xport TB MU41 WM41 ltac:(rewrite LTB; clear -SPR LO BOT STK3 TL1 TL2 SP1 SP2 C16 SHHI TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold AMALLOC_STACK, AINSTANCE in *; lia).
  xport FRS MU41 WM41 ltac:(clear -SPR LO BOT STK3 TL1 TL2 SP1 SP2 C16 SHHI TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold AMALLOC_STACK, AINSTANCE in *; lia).

  xport HDR MU1 WM1 ltac:(clear -HspA DJT SPR SP2 G1 G2 EUB RZR N NSZ NS RSR LO BOT STK3 C16; unfold acache_addr, AMALLOC_STACK, K_SPACE_SIZE in *; lia).
  xport UJ MU1 WM1 ltac:(clear -HspA DJT SPR SP2 G1 G2 EUB RZR N NSZ NS RSR LO BOT STK3 C16; unfold acache_addr, AMALLOC_STACK, K_SPACE_SIZE in *; lia).
  xport SHA MU1 WM1 ltac:(cbv delta [g grz room PG] in *; clear -HspA SPR GR1 GR2 GR3 GR4 GR5 GR6 GR7 GR8 GR9 LO BOT STK3 TL1 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport SHU MU1 WM1 ltac:(cbv delta [g grz room PG] in *; clear -HspA SPR GR1 GR2 GR3 GR4 GR5 GR6 GR7 GR8 GR9 SB3 LO BOT STK3 TL1 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  assert (SHP1 : n mod 8 <> 0 -> rw_cells bsegs m1 PG [C1 (Z_to_bv 8 250)]).
  { intros NE. specialize (SHP ltac:(subst room; generalize NE; clear; intros NE; destruct (Z.eqb_spec (n mod 8) 0); [exfalso; exact (NE ltac:(assumption)) | reflexivity])).
    xport SHP MU1 WM1 ltac:(cbv delta [g grz room PG] in *; clear -HspA SPR GR1 GR2 GR3 GR4 GR5 GR6 GR7 GR8 GR9 SB3 SB4 LO BOT STK3 TL1 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia). exact SHP. }
  assert (LH1 : 16 < rz_size n -> rw_cells bsegs m1 AB [C8 j1; C8 j2]).
  { intros R16. pose proof (proj1 (LH R16)) as LH0.
    xport LH0 MU1 WM1 ltac:(clear -HspA DJT SPR SP2 G1 G2 EUB RZR N NSZ NS RSR LO BOT STK3 C16; unfold acache_addr, AMALLOC_STACK, K_SPACE_SIZE in *; lia). exact LH0. }
  xport GOT' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport GOT80' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport REAL' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport SHB' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport CANP' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport HPP' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport CSMT' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport FLG5' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport FLG' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport HK1' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport LS1' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport LS2' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport LAY' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport MCS' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport CF34' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport INI1' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport RSS' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport IMAX3' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport TI' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport TK' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport T88' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, ATP88, AMALLOC_STACK in *; lia).
  xport TSD' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, ATSD, AMALLOC_STACK in *; lia).
  xport CT' MU1 WM1 ltac:(ub CL5; clear -HspA Y SPR TL1 CL1 CL2 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb CTXi CBND CBNDa CBNDb; unfold acache_addr, AMALLOC_STACK, AIMG_HI in *; lia).
  xport CT8' MU1 WM1 ltac:(ub CL5; clear -HspA Y SPR TL1 CL1 CL2 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb CTXi CBND CBNDa CBNDb; unfold acache_addr, AMALLOC_STACK, AIMG_HI in *; lia).
  xport TTctx' MU1 WM1 ltac:(clear -HspA SPR TL1 TL2 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport UNW' MU1 WM1 ltac:(clear -HspA SPR TL1 TL2 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport STATS' MU1 WM1 ltac:(rewrite LSJ'; clear -HspA SPR TL1 TL2 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, ASTATS_WORDS, AMALLOC_STACK in *; lia).
  assert (DEP1 : ADEPOT DI L m1).
  { eapply (adi_frame DI); [exact HD' | exact MU1 | exact WM1 |]. unfold acache_addr.
    repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq; ub DL7; ub DL8; clear -Hq Y Y0 HspA SPR TL1 TL2 DL1 DL2 DL3 DL4 DL5 DL6 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb NODi NBND NBNDa NBNDb STOi SBND SBNDa SBNDb; unfold AMALLOC_STACK, AIMG_HI in *; lia|]).
    apply Forall_nil. }

  assert (PF : pfactsG (bv_unsigned sp) (al_t L) (al_space_beg L) c mu0 ATOP lo).
  { unfold pfactsG. pose proof (ao_t L ALO) as OT. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in OT.
    unfold AMALLOC_STACK, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN, K_FREEARR_OFF, K_USER_MAP in *. change (2^37) with 137438953472 in *.
    ub TSP. generalize LO BOT SP47 STK2 STK3 OT SP1 SP2 SAL C16 A1 A2 A4 Y. clear. intros.
    repeat match goal with H : _ /\ _ |- _ => destruct H end.
    repeat split; first [reflexivity | assumption | lia | Z.div_mod_to_equations; lia]. }
  assert (MUall : munch [(bv_unsigned sp - 4096, bv_unsigned sp); (al_t L + 208, al_t L + 3169); (AINSTANCE, AINSTANCE + 728);
                         (al_space_beg L + 137438953472 + c * 128, al_space_beg L + 137438953472 + c * 128 + 128);
                         (al_space_beg L + c * 4294967296 + mu0, al_space_beg L + c * 4294967296 + 4294967296);
                         (shad (al_space_beg L + c * 4294967296 + mu0), shad (al_space_beg L + c * 4294967296) + 536870912)]%Z m m_pre).
  { eapply munch_trans; [eapply munch_weaken; [| exact MU4] | eapply munch_weaken; [| exact MUc]];
      unfold sub_fp; cbn [outside]; intros q Hq; rewrite ?RIE, ?RBE in *; unfold K_REGION in *; change (2^32) with 4294967296 in *;
      rewrite ?shlen_div in *; change (4294967296 / 8) with 536870912 in *; clear -Hq HspA; lia. }
  assert (WMall : wmono bsegs m m_pre) by (eapply wmono_trans; [exact WM4 | exact WMc]).

  assert (BB : forall b, In b (x_busy X) ->
      al_space_beg L <= xb_alloc L b /\ xb_alloc L b + size_of_class (xb_class b) <= al_space_beg L + 137438953472
      /\ (xb_alloc L b + size_of_class (xb_class b) <= al_space_beg L + c * 4294967296 + mu0 \/ al_space_beg L + c * 4294967296 + 4294967296 <= xb_alloc L b)).
  { intros b Hb. destruct (BUSY b Hb) as [CLB _].
    destruct (PERC (xb_class b) CLB) as (Q1 & Q2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & QR).
    pose proof (size_of_class_facts (xb_class b) CLB) as [QS _].
    assert (KB : 0 <= xb_slot b < ndist st (xb_class b)).
    { apply QR. apply in_app_iff. right. apply in_app_iff. right. unfold busy_slots. apply in_map_iff. exists b. split; [reflexivity|].
      apply filter_In. split; [exact Hb| apply Z.eqb_refl]. }
    pose proof (slot_in_region L st (xb_class b) (xb_slot b) ltac:(clear -QS; lia) (proj1 Q1) KB) as (P5 & P4 & P0).
    unfold xb_alloc. unfold K_NUM_CLASSES in CLB. unfold K_FREEARR_OFF in Q2.
    destruct (Z.eq_dec (xb_class b) c) as [EC|NC].
    - rewrite EC in P5, P4, Q1, Q2 |- *. rewrite RBE in P5, P4. change (c_mapped_user (get_cls st c)) with mu0 in Q1, Q2.
      clear -P5 P4 Q1 Q2 A1 A2 C16. unfold K_FREEARR_OFF in *. lia.
    - pose proof (region_other_geo L c (xb_class b) ALO ltac:(clear -C16; lia) CLB NC) as (R1 & R2 & R3 & _). rewrite RBE in R2.
      clear -P5 P4 Q1 Q2 R1 R2 R3 A1. lia. }
  pose proof (ao_fake L ALO) as FKO. unfold aobj in FKO. pose proof (ao_res L ALO) as ORS. unfold aobj in ORS. pose proof (ao_space L ALO) as RSP.
  pose proof (ad_fake_res L ALO) as D_f_res. pose proof (ad_t_fake L ALO) as D_t_f. pose proof (ad_dtls_res L ALO) as D_d_res. pose proof (ad_t_dtls L ALO) as D_t_d.
  pose proof (ao_dtls L ALO) as ODT. unfold aobj in ODT. unfold adisj in D_f_res, D_t_f, D_d_res, D_t_d.
  assert (FKD : forall cls FA sz, In (mkABlock (ABFake cls) FA sz) LB -> al_fake L <= FA /\ 0 <= sz /\ FA + sz <= al_fake L + 11571200)
    by (intros cls FA sz Hin; exact (proj1 (proj2 BL) cls FA sz Hin)).
  assert (PRES : aheap_pres CI LB (bv_unsigned sp) m m_pre).
  { intros a Ha CL. split; [| intros Hw; apply WMall; exact Hw].
    apply MUall. rewrite wa_unsigned by exact Ha.
    destruct CL as [STa | [CIa | [BLK | SH]]].
    - eapply disjoint_outside; [eapply (Q_stack _ _ _ _ _ _ _ PF a 1); clear -STa; lia | clear; lia].
    - destruct CIa as (iv & Hiv & R). pose proof (proj1 (Forall_forall _ _) CI_OK iv Hiv) as (Q1 & Q2 & Q3).
      pose proof (proj1 (Forall_forall _ _) CI_OK2 iv Hiv) as Q4. cbn [fst snd] in *.
      eapply disjoint_outside; [eapply (Q_img _ _ _ _ _ _ _ PF a 1); unfold AIMG_HI in *; clear -R Q1 Q3 Q4; lia | clear; lia].
    - destruct BLK as (b & Hb & R). destruct b as [[p|cls] A n']; cbn [ab_addr ab_size] in R.
      + destruct (proj1 BL p A n' Hb) as [(xb & Hxb & Sb & Ub & Nb)|(mb0 & ms0 & Lp & EUA & Gs)].
        * destruct (BB xb Hxb) as (Bb1 & Bb2 & Bb3).
          pose proof (awf_fits L st X xb WF Hxb) as FIT. unfold xb_fits in FIT. rewrite Sb in FIT. unfold xb_user in Ub. subst A n'.
          eapply disjoint_outside; [eapply (Q_slot _ _ _ _ _ _ _ PF a 1) | clear; lia]; clear -R Bb1 Bb2 Bb3 FIT; lia.
        *
          cbn [sec_wf1] in Gs. destruct Gs as (Gs1 & Gs2 & Gs3 & Gs4 & Gs5 & Gs6 & (Ct & Cc & Cr & Cp & Cn & Cs & Cf & Cd)).
          pose proof (sec_facts n' ltac:(clear -Gs5; lia) Gs6) as SF. subst A. unfold SEC_UOFF, K_HIGH_MEM in *.
          unfold ablk, KLS, AIMG_HI in Gs2.
          eapply disjoint_outside; [eapply (Q_obj _ _ _ _ _ _ _ PF a 1) | clear; lia]; clear -R Gs2 Gs3 Gs4 Gs5 SF Ct Cr RSP ORS; lia.
      + destruct (FKD cls A n' Hb) as (K1 & K2 & K3). atop_facts.
        eapply disjoint_outside; [eapply (Q_obj _ _ _ _ _ _ _ PF a 1) | clear; lia];
          clear -R K1 K3 FKO D_t_f D_f_res RSP OFKi OFKs OFKsa OFKsb; lia.
    - destruct SH as (a' & Ha' & ->).
      destruct Ha' as [STa | [CIa | FK]].
      + eapply disjoint_outside; [eapply (Q_shad_hi _ _ _ _ _ _ _ PF a'); unfold AMALLOC_STACK in *; clear -STa LO BOT STK3; lia | clear; lia].
      + destruct CIa as (iv & Hiv & R). pose proof (proj1 (Forall_forall _ _) CI_OK iv Hiv) as (Q1 & Q2 & Q3). cbn [fst snd] in *.
        eapply disjoint_outside; [eapply (Q_shad_img _ _ _ _ _ _ _ PF a'); unfold AIMG_HI in *; clear -R Q1 Q3; lia | clear; lia].
      + destruct FK as (cls & FA & sz & Hin & R). destruct (FKD cls FA sz Hin) as (K1 & K2 & K3). atop_facts.
        eapply disjoint_outside; [eapply (Q_shad_obj _ _ _ _ _ _ _ PF a') | clear; lia]; clear -R K1 K3 FKO D_f_res RSP OFKi OFKs OFKsa OFKsb; lia. }
  assert (HFKp : AFK L LB m_pre).
  { eapply (hf_frame _ HL L LB m m_pre); [exact HFK | exact MUall | exact WMall | exact (Q_tfs _ _ _ _ _ _ _ PF) |].
    unfold fake_untouched. pose proof (ao_t L ALO) as OT. unfold aobj in OT.
    assert (SHF : 2148262400 <= shad (al_fake L) /\ shad (al_fake L) + shlen 11571200 <= 17594332446720
                  /\ (shad (al_space_beg L + c * 4294967296) + 536870912 <= shad (al_fake L)
                      \/ shad (al_fake L) + shlen 11571200 <= shad (al_space_beg L + c * 4294967296 + mu0))
                  /\ shad (al_space_beg L + c * 4294967296) <= shad (al_space_beg L + c * 4294967296 + mu0)
                  /\ 2201439137792 <= shad (al_space_beg L + c * 4294967296)).
    { rewrite !shad_div, !shlen_div. unfold ASHOFF in *. destruct PF as (_ & _ & (F1 & F2 & F3 & F4 & F5 & F6) & _).
      clear -FKO F1 F2 F3 F4 F5 F6 D_f_res RSP OFKi OFKs OFKsa OFKsb. Z.div_mod_to_equations. dlia. }
    destruct SHF as (SF1 & SF2 & SF3 & SF4 & SF5).
    unfold AMALLOC_STACK, AINSTANCE in *. destruct PF as (PF1 & PF2 & PF3 & PF4).
    repeat (apply Forall_cons; [cbn [fst snd];
      clear -LO BOT STK3 SP47 STK2 OT FKO ORS RSP ODT D_f_res D_t_f D_d_res D_t_d C16 PF3 PF4 SF1 SF2 SF3 SF4 SF5 SHHI TL1 TBND TBNDa TBNDb TIMG TIMGa TIMGb OFKi OFKs OFKsa OFKsb DBND DBNDa DBNDb DIMG DIMGa DIMGb;
      repeat (split; [lia|]); lia |]).
    apply Forall_nil. }

  eapply evtF_mono.
  { eapply (aligned_tail_gen16 DI L RNG1 ra sp gp tp spA t0d t1d t2d a1d a2d a3d a4d a5d a6d a7d t3d t4d t5d t6d
              s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0A s1A s2A s3A s4A s5A s6A sp (Z_to_bv 64 n) (Z_to_bv 64 16) F fc m1
              n (al_t L) c cnt AB UB PG room lo b0 b1 szh szl ctxj (1 + Z.of_nat (length trc))
              (Z_to_bv 64 (max_count st_pre c)) (Z_to_bv 64 S) stj1 j1 j2 (Z_to_bv 8 250) sj' sjunk uj fr0 junk0 junk2 tb trc).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => exact ST1
         | |- mem_inv _ _ => exact MI1
         | |- allocA_cells _ _ _ => unfold allocA_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end)
         | |- poison_cells _ => unfold poison_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end)
         | |- ADEPOT _ _ _ => exact DEP1
         | |- In _ _ => exact TRU
         | |- u64arr _ _ (_ + 2800) _ => exact STATS'
         | |- u64arr _ _ _ _ => exact TB
         | |- map _ _ = _ => exact TRF
         | |- (16 < _) -> _ => exact LH1
         | |- ~ _ -> rng _ _ _ => exact RSPf
         | |- ~ _ -> _ => exact SHP1
         | |- is_primary16 _ = _ => exact PRIM
         end.
    all: try lazymatch goal with
         | |- rw_cells _ _ (_ + -16) _ => exact HDR
         | |- rw_cells _ _ (shad _) [C1 _] => exact SHA
         | |- rw_cells _ _ (shad _) [CB _ _] => exact SHU
         | |- rw_cells _ _ _ [CB _ _] => exact UJ
         | |- rw_cells _ _ (_ + 2784) _ => exact STS1
         | |- rw_cells _ _ (_ + 208 + _ * 80) _ => exact CR1
         | |- rw_cells _ _ _ _ => assumption
         | |- rng _ _ _ => assumption
         | |- _ \/ _ => first [exact DJT | exact DJN | exact DJS | exact DJC4 | unboxed CL5 | unboxed DL7 | unboxed DL8 | unboxed DL9 | unboxed DL10]
         | |- @eq Z _ _ => first [assumption | reflexivity | exact PGE | subst room; reflexivity]
         | |- @eq word _ _ => first [assumption | reflexivity]
         | |- @eq nat _ _ => first [exact LSJ' | exact LTB | assumption]
         end.
    all: try assumption.
    all: try (generalize N NR LO BOT SP47 STK1 STK2 STK3 SP1 SP2 SP4 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6
                         G1 G2 G3 G4 G5 EUB ES SM16 NSZ NS RSR RZR GR3 GR7 GR8 GR9 SB3 SB4 B1 POS HCNT CNT16 KS0 KS1 HC0 C16 LTRC RA4 HspA;
              clear; intros; rewrite ?HC0 in *; unfold AIMG_HI, AMALLOC_STACK, AREQMAX, UDEPTH, K_SPACE_SIZE, K_SPACE_EXTRA in *; lia).
    all: try (eapply rng_sub'; [exact RSTK1|]; clear -LO SP47 BOT STK3 SPR; unfold AMALLOC_STACK in *; lia).
    all: try (clear -LTRC; lia).
    all: match goal with |- ?G => idtac "REMT" G end. }

  cbv beta. intros ms' PM.
  unfold amalloc_post_x. cbn [snd fst]. split.
  {
    pose proof PM as PM0. unfold aligned_post_gen16 in PM0.
    destruct PM0 as (id0 & t0e & t1e & t2e & a1e & a2e & a3e & a4e & a5e & a6e & a7e & t3e & t4e & t5e & t6e & m5 & sj5 & stj5 & EMS & MUt & _).

    assert (AXFall : axflags L st_pre m_pre).
    { intros c' Hc' NC'. destruct (Z.eq_dec c' c) as [->|NE]; [exact (AXFp NC')|].
      pose proof (C6F4 c' Hc' NC') as F4. unfold axflag in *.
      replace (exh_mem c' st_pre) with (exh_mem c' st)
        by (destruct EXHp as [E|E]; [symmetry; apply exh_mem_eq_list; exact E| rewrite (exh_mem_eq_list c' _ _ E); symmetry; apply exh_mem_clear_other; exact NE]).
      eapply cells_frameO; [exact F4| exact MUc|]. cbn [cells_size csize Nat.add]. intros x Hx. cbn [outside].
      assert (RIEj : forall j, aregion_info L j = al_space_beg L + 137438953472 + j * 128) by (intros j; unfold aregion_info, K_SPACE_SIZE, ARI_STRIDE; change (2^37) with 137438953472; reflexivity).
      rewrite (RIEj c') in Hx. rewrite (RIEj c). unfold aregion, K_REGION, AINSTANCE, K_NUM_CLASSES in *. change (2^32) with 4294967296.
      pose proof atop_range as ATRx.
      assert (SHT : shad (al_space_beg L + c * 4294967296) + shlen 4294967296 <= 17594333495296)
        by (rewrite shad_div, shlen_div; unfold ASHOFF, K_SPACE_SIZE, K_SPACE_EXTRA in *; change (2^37) with 137438953472 in *; clear -SP1 SP2 C16 ATRx; Z.div_mod_to_equations; lia).
      rewrite ?unsigned_lit by (clear -SPR HspA LO BOT STK3; lia).
      pose proof TSP as TSPx. unbox TSPx.
      unfold K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^37) with 137438953472 in *.
      clear -Hx Hc' NE C16 SP1 SP2 TL1 TL2 TL4 LO BOT STK3 HspA SHT A1 A2 ATRx SPR TSPx. unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in *. repeat split; lia. }
    destruct (c6_frame L RESV RNG1 st_pre m_pre m1 _ ALO ROK AXGp AXFall MU1) as [G1x F1x].
    { rewrite ?unsigned_lit by (clear -SPR HspA LO BOT STK3; lia).
      apply Forall_cons; [unfold c6_piece; cbn [fst snd]; intros _; left; clear -LO BOT STK3 HspA; lia|].
      apply Forall_cons; [unfold c6_piece, acache_addr; cbn [fst snd]; intros _; right; left; clear -C16; lia|].
      apply Forall_cons; [unfold c6_piece; cbn [fst snd]; intros _; right; left; clear; lia| apply Forall_nil]. }
    destruct (c6_frame L RESV RNG1 st_pre m1 m5 _ ALO ROK G1x F1x MUt) as [G5x F5x].
    { pose proof (ao_res L ALO) as (_ & _ & ORSx & _). pose proof (ao_space L ALO) as RSPx. pose proof atop_range as ATRx.
      assert (UBN : UB + n <= AB + S) by (clear -EUB NS NSZ RSR ES; lia).
      repeat (apply Forall_cons; [unfold c6_piece; cbn [fst snd]; intros NEk;
        first [ left; clear -LO BOT; lia
              | right; left; clear -C16; lia
              | do 2 right; left; clear -G1 G2 EUB UBN RSPx RZR SZB ES; subst S; lia
              | do 3 right; left; clear -NEk GR3 GR4 GR5 GR6 GR7 GR8 GR9 PGE SB3; subst g grz; lia
              | do 5 right; left; clear; lia
              | do 6 right; left; clear; lia
              | do 7 right; left; clear; lia ]|]).
      apply Forall_nil. }
    rewrite EMS. unfold c6_at. cbn [ms_mem MS].
    destruct G5x as (XC5 & EC5 & ER5 & ECL5).
    split.
    - split; [exact XC5|]. split; [exact EC5|]. split; [exact ER5|].
      eapply (emb_clr_sub RESV st_pre); [reflexivity| | exact ECL5].
      apply (achunks_new_prim st_pre _ (a_next (apop c st_pre)) c n); reflexivity.
    - intros c' Hc' NC'. exact (F5x c' Hc' NC'). }
  unfold apop. rewrite HCNT, !a_next_put_cls, !a_live_put_cls.
  apply (aligned_post_gen16_shift DI L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc n (al_t L) c cnt AB UB PG room lo b1 _ _ uj m_pre m1 ms') in PM;
    [| eapply munch_weaken; [| exact MU1]; unfold sub_fp, acache_addr; cbn [outside]; intros q Hq; clear -Hq HspA; lia | exact WM1].
  cbv delta [PG g grz room] in PM, SHpre, SHsuf. subst UB. subst AB.
  eapply (amalloc_post_shiftG CI _ L RNG RNG1 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st st_pre LB n lo m m_pre); [| exact FPLE |].
  { eapply (store_prim16 DI AQ ASEC AFK HL CI CI_OK L RNG1 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m_pre st_pre LB X_pre n lo c cnt k b1
              (Z_to_bv 64 (max_count st_pre c)) (Z_to_bv 64 (size_of_class c)) uj).
    all: try exact PM.
    all: try lazymatch goal with
         | |- is_primary16 _ = _ => exact PRIM
         | |- ann_ov _ = None => rewrite L2; exact OVF
         | |- alayout_ok _ => exact ALO
         | |- arng _ _ _ => exact ARNGp0
         | |- AFK _ _ _ => idtac
         | |- AREP _ _ _ _ _ => exact ARp
         | |- ablocks _ _ _ _ => eapply ablocks_xbusyG; [exact BL | exact XB | exact L1]
         | |- nth_error _ _ = _ => exact NK
         | |- busy_of _ _ _ = _ => exact NB
         | |- (16 < _) -> _ => let R16 := fresh in intros R16; exact (proj2 (LH R16))
         | |- junk_at _ (_ + 2768) _ => exact CSa
         | |- junk_at _ (_ + 2792) _ => exact CSc
         | |- junk_at _ _ _ => first [exact TL | rewrite ES; exact TL]
         | |- fill_at _ (_ + 1) _ _ => exact SHpre
         | |- fill_at _ _ _ _ => first [exact SHsuf | rewrite ES; exact SHsuf]
         end.
    all: try assumption.
    all: try reflexivity.
    all: try (generalize N KR B1 LO BOT STK3 POS; clear; intros; unfold AMALLOC_STACK in *; lia).
    all: try exact HFKp.
    all: match goal with |- ?G => idtac "REMS" G end. }
  exact PRES.
Qed.
End S.
End CANSEC1.
End AAlignedPG_x.

Module AAllocatePG_x.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Exec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Tac. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ITreeA. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.SysStepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW.BImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABytes.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ASecFacts.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AMalloc_iface.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ADepot_iface.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARep.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ALayout.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AHeapP.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepKit.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepFrame.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepExt.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepExt2.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit2.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AModelFacts.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.APrimFacts.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apoison.TwinB.F_apoison.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc1.TwinB.F_aalloc1.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc2.TwinB.F_aalloc2. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_amalloc_icpt.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_amalloc_pre.TwinB.F_amalloc_pre.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc2.TwinB.F_aalloc2g.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc3.TwinB.F_aalloc3g.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aaligned_tail.TwinB.F_amalloc_tailg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_amalloc_arep.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepStore.TwinB.ARepStore.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepStore.TwinB.ARepStoreG. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARefill_iface.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARefillP.TwinB.ARefillP.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ACallocG.TwinB.ACallocG.
 Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc1.TwinB.F_aalloc1b.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aaligned_tail.TwinB.F_aallocate_tailg.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AAlignedPG.TwinB.AMallocPG.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

 Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AAlignedPG.TwinB.AMallocPG. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AEmbRep.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFrameD.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AEmbFrame.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_arefill.TwinB.F_arefill_x. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARefill_iface_x.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARefillP_x.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARefillP.TwinB.ARefillP_e. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_acache_x.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ACallocG.TwinB.ACallocG_x. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_amalloc_null.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ANullKit.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AC6Frame.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ANullPres.TwinB. Import AMallocPG_x.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSECX0. Context {rc : runConstT} {ov : annOV}.
Definition aallocate_post_x (CI : list (Z * Z)) (AHEAP : alayout -> footprint -> astate -> list ablock -> amem -> Prop)
    (L : alayout) (RESV : list (Z * Z)) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (n lo : Z) (m : amem)
    (r : astate * option aptr) (RNG' : footprint) : machine_state -> Prop :=
  fun ms' => c6_at RESV L RNG' (fst r) ms' /\
    match snd r with
    | Some _ => amalloc_post CI AHEAP L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB n lo m r RNG' ms'
    | None => fp_le RNG RNG' /\ exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (ret_pc ra) fc None m' (seg_rom bsegs)
        /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
        /\ aheap_pres CI LB (bv_unsigned sp) m m'
        /\ AHEAP L RNG' (fst r) LB m'
    end.
End CANSECX0.

Section CANSEC1. Context {rc : runConstT} {ov : annOV}.

Local Lemma ablk_int : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6492160 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
Local Lemma aobj_int : forall a n, aobj a n -> 0x10000 <= n ->
  6492160 <= a /\ a + n <= ATOP /\ exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof.
  intros a n H Hn. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. destruct H as (H1 & H2 & H3 & H4 & H5).
  split; [lia|]. split; [lia|]. destruct H4; [exists 0 | exists 1]; lia.
Qed.
Local Lemma aobj4_int : forall a, aobj a 4096 ->
  4096 <= a /\ a + 4096 <= ATOP
  /\ (exists k, 0 <= k <= 1 /\ a + 4096 <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a)
  /\ (exists j, 0 <= j <= 1 /\ a + 4096 <= 65536 + j * 18446744073709551616 /\ 6492160 * j <= a).
Proof.
  intros a H. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. destruct H as (H1 & H2 & H3 & H4 & H5).
  split; [lia|]. split; [lia|]. split; [destruct H4; [exists 0 | exists 1]; lia | destruct H5 as [_ [H5|H5]]; [exists 0 | exists 1]; lia].
Qed.

Local Ltac dlia := repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
Section S.
Variable DI : ADepotIface.
Variables (AQ ASEC : alayout -> astate -> aconc -> amem -> Prop) (AFK : alayout -> list ablock -> amem -> Prop).
Hypothesis HL : ahole_laws (AH DI AQ ASEC AFK).
Hypothesis HLD : ahole_lawsD (AH DI AQ ASEC AFK).
Hypothesis EXHW : exh_first_stmt.
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI) CI.

Hypothesis CI_OK2 : Forall (fun iv => snd iv <= AINSTANCE \/ AINSTANCE + 728 <= fst iv) CI.

Hypothesis CI_OK3 : Forall (fun iv => (snd iv <= AEMB \/ AEMB + 56 <= fst iv) /\ (snd iv <= 0x15dee0 \/ 0x15dee1 <= fst iv)) CI.

Theorem aallocate_prim_x : forall (L : alayout) (RNG : footprint)
    (ra spA gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (n lo SO pc : Z) (trc : list Z) (tb : list word) (RESV : list (Z * Z)),
  ann_ov (a_next st) = None ->

  is_primary n = true ->
  AHEAP_P (AH DI AQ ASEC AFK) L RNG st LB m ->
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned spA) -> ATOP + 4096 <= lo -> lo <= bv_unsigned spA - AMALLOC_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 AINSTANCE -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 8 -> a3 = Z_to_bv 64 SO -> a4 = Z_to_bv 64 1 -> a5 = Z_to_bv 64 1 ->
  1 <= n <= AREQMAX ->

  rw_cells bsegs m SO [C8 (Z_to_bv 64 (SO + 16)); C8 (Z_to_bv 64 (1 + Z.of_nat (length trc)))] ->
  u64arr bsegs m (SO + 16) tb -> length tb = 255%nat ->
  map bv_unsigned (firstn (Datatypes.S (length trc)) tb) = pc :: trc ->
  In (pc :: trc) (al_U L) -> (length trc <= 29)%nat ->
  bv_unsigned spA <= SO -> SO + 2056 <= 2^47 -> bv_unsigned spA + 2144 < 2^47 -> rng RNG SO 2056 ->
  rng RNG lo (bv_unsigned spA - lo) ->
  aresv_ok L RESV ->

  bv_unsigned fc < 32 -> axg RESV RNG st m -> axflags L st m -> (let '(_, cap0, _) := a_emb st in cap0 <= 2 ^ 23) ->
  implS bsegs RNG (aembed ATOP (amalloc ATOP RESV st n))
        (epostF (aallocate_post_x CI (AHEAP_P (AH DI AQ ASEC AFK)) L RESV RNG ra spA gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB n lo m))
        (MS (mkR ra spA gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 allocate_entry) fc None m (seg_rom bsegs)).
Proof.
  intros until RESV. intros OVF PRIM AHP MI STA BOT LOA TP Ha0 Ha1 Ha2 Ha3 Ha4 Ha5 NR SS TB LTB TRF TRU LTRC SPS STOP SPV RS RSTKA ROK FC C6G C6F CAPB.
  assert (N : 1 <= n <= AREQMAX) by exact NR. assert (N1 : 1 <= n) by (clear -NR; lia).

  assert (EXSP : exists sp : word, bv_unsigned spA = bv_unsigned sp - 2144).
  { exists (Z_to_bv 64 (bv_unsigned spA + 2144)). rewrite unsigned_lit; [lia|]. pose proof (bv_unsigned_in_range 64 spA) as R. unfold bv_modulus in R. clear -R SPV. lia. }
  destruct EXSP as [sp HspA].
  assert (LO : lo <= bv_unsigned sp - 4608) by (unfold AMALLOC_STACK in *; clear -LOA HspA; lia).
  assert (SP47 : bv_unsigned sp < 2^47) by (clear -SPV HspA; lia).
  assert (RSTK : rng RNG lo (bv_unsigned spA - lo)) by exact RSTKA.
  assert (S64 : 0 < SO < 2^64) by (atop_facts; clear -SPS STOP LOA BOT; unfold AMALLOC_STACK in *; lia).
  destruct AHP as (ALO & ARNG & [X [AR BL]] & HFK).
  remember (class_id (needed_size n)) as c eqn:HC0. symmetry in HC0.
  pose proof (prim_facts n N1 PRIM) as (NS & RZR & RZE & RZM & RLR & RSR & RSM & NSR).
  pose proof (prim_class_facts n c N1 PRIM HC0) as (C16 & NSZ & SM16 & SMALL & MCB). clear SMALL.
  pose proof (cls_facts c C16) as (SZB & _ & _ & _).
  assert (HCK : 1 <= c < K_NUM_CLASSES) by (unfold K_NUM_CLASSES; clear -C16; lia).
  assert (NM8 : needed_size n mod 8 = 0) by (rewrite NS; clear -RSM RZM; Z.div_mod_to_equations; lia).

  pose proof AR as AR0. destruct AR0 as (WF & RT & INST & THR & CLS & HQ & HS & HD & HRO & RT2 & AVL & RT3).
  destruct THR as (T0 & T40 & CACHES & CSTATS & [sj [STATS LSJ]] & UNW).
  pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVE & FRESH & UNIQ).
  destruct (PERC c HCK) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & LENF & LENC & CNTB & ND & RANGE).
  pose proof (alayout_space L ALO) as (SP1 & SP2 & SP3 & SP4).
  pose proof (alayout_t L ALO) as (TL1 & TL2 & TL3 & TL4).
  pose proof (alayout_ctx L ALO) as (CL1 & CL2 & CL3 & CL4 & CL5).
  pose proof (alayout_depot L ALO) as (DL1 & DL2 & DL3 & DL4 & DL5 & DL6 & DL7 & DL8 & DL9 & DL10).
  pose proof (aobj4_int _ (ao_t L ALO)) as (_ & _ & (kT & TBND & TBNDa & TBNDb) & (jT & TIMG & TIMGa & TIMGb)).
  pose proof (aobj_int _ _ (ao_ctx L ALO) ltac:(clear; lia)) as (CTXi & _ & (kC & CBND & CBNDa & CBNDb)).
  pose proof (aobj_int _ _ (ao_nodes L ALO) ltac:(clear; lia)) as (NODi & _ & (kN & NBND & NBNDa & NBNDb)).
  pose proof (aobj_int _ _ (ao_store L ALO) ltac:(clear; lia)) as (STOi & _ & (kR & SBND & SBNDa & SBNDb)).
  pose proof (aobj_int _ _ (ao_fake L ALO) ltac:(clear; lia)) as (OFKi & _ & (kF & OFKs & OFKsa & OFKsb)).
  pose proof (aobj4_int _ (ao_dtls L ALO)) as (_ & _ & (kD & DBND & DBNDa & DBNDb) & (jD & DIMG & DIMGa & DIMGb)).
  pose proof (alayout_stack L ALO) as (STK1 & STK2 & STK3).
  pose proof (alayout_res_disj L ALO) as [SCX TSP].
  pose proof RT as RT0.
  destruct RT0 as (GPG & GOT & GOT80 & RIC & LS1 & REAL & IMAX4 & FLG5 & FLG & HPP & SHB & CANP & TI & TK & INI2 & LAY & MCS & OOM3
                    & PGC & HK2 & CF8 & CF34 & CSMT & T88 & TSD & LS2 & CT8 & CT).
  pose proof INI2 as INI. rw_split INI 1%nat INI1 INIx. clear INIx.
  destruct OOM3 as [oomb OOM]. rw_split OOM 2%nat OOMx RSS. clear OOMx.
  pose proof IMAX4 as IMAX. rw_split IMAX 3%nat IMAX3 IMAXx. clear IMAXx.
  pose proof T0 as TT0. rw_split TT0 1%nat TTctx TT.
  pose proof ARNG as ARNG0. destruct ARNG as (RIMG & RT4 & RCTX & RNO & RSTO & RRI & RFK & RSFK & RDTLS & RCLS).
  assert (RCTX4 : rng RNG (al_ctx L) 4096) by (eapply rng_sub'; [exact RCTX|]; clear; lia).
  word_range sp SPR.
  box CL5. box DL7. box DL8. box DL9. box DL10. box TSP. box SCX.

  rewrite (amalloc_prim_eq RESV st n c N1 PRIM HC0).

  iprefix. eapply evtF_cut.
  { eapply (allocA_pre_spec RNG ra spA gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n SO (al_ctx L) (al_t L) lo).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => exact STA
         | |- mem_inv _ _ => exact MI
         | |- allocA_cells _ _ _ => unfold allocA_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end)
         | |- _ \/ _ => unboxed CL5
         | |- @eq word _ _ => first [exact TP | exact Ha0 | exact Ha1 | exact Ha2 | exact Ha3 | exact Ha4 | exact Ha5]
         | |- is_primary _ = _ => exact PRIM
         | |- 0 < _ < _ => exact S64
         end.
    all: try lazymatch goal with
         | |- rw_cells _ _ _ _ => assumption
         | |- rng _ _ _ => assumption
         end.
    all: try assumption.
    all: try (generalize N NR LO LOA HspA BOT SP47 STK1 STK2 STK3 SP1 SP2 SP4 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 LTRC;
              clear; intros; unfold AIMG_HI, AMALLOC_STACK, AREQMAX, UDEPTH in *; lia).
    all: match goal with |- ?G => idtac "REMPRE" G end. }
  cbv beta. intros ms4 P4. unfold allocA_pre_post in P4.
  destruct P4 as (t0c & t1c & t2c & a4c & a5c & a6c & a7c & t3c & t4c & t5c & t6c & m4 & -> & MU4 & WM4 & MI4 & ST4 & [fr0 FRa]).
  apply evtF_done.
  replace (bv_unsigned spA - 128) with (bv_unsigned sp - 2272) in ST4, FRa by (clear -HspA; lia).

  pose proof UNW as UW4.
  xport UW4 MU4 WM4 ltac:(clear -HspA SPR LO BOT STK3 TL1 TL2; unfold AMALLOC_STACK in *; lia).
  xport SS MU4 WM4 ltac:(clear -HspA SPS STOP SPR; lia).
  xport TB MU4 WM4 ltac:(rewrite LTB; clear -HspA SPS STOP SPR; lia).
  assert (AR4 : AREP (AH DI AQ ASEC AFK) L st X m4).
  { eapply (AREP_frame_pre _ HL L st X m m4); [exact ALO | exact AR | exact MU4 | exact WM4 | | exact UW4].
    apply Forall_cons; [unfold apre; cbn [fst snd]; intros _; left; unfold AMALLOC_STACK in *; clear -HspA LO BOT STK3; lia| apply Forall_nil]. }

  destruct (c6_frame L RESV RNG st m m4 _ ALO ROK C6G C6F MU4) as [C6G4 C6F4].
  { apply Forall_cons; [unfold c6_piece; cbn [fst snd]; intros _; left; unfold AMALLOC_STACK in *; clear -HspA LO BOT STK3; lia| apply Forall_nil]. }

  eapply (@calloc_arep_gen_x _ _ _ HL HLD _ RESV _ _ L RNG _ _ gp tp t0c t1c t2c _ _ _ _ _ _ a4c a5c a6c a7c _ _ _ _ _ _ _ _ _ _ t3c t4c t5c t6c F fc m4 st X c lo (needed_size n)
            ALO ARNG0 AR4 MI4).
  all: try lazymatch goal with
       | |- arng _ _ _ => exact ARNG0
       | |- stk _ _ _ _ => rewrite unsigned_lit by (clear -SPR HspA LO BOT STK3; unfold AMALLOC_STACK in *; lia);
                           replace (bv_unsigned spA + -128) with (bv_unsigned sp - 2272) by (clear -HspA; lia); exact ST4
       | |- ATOP <= _ => clear -LO BOT STK3; unfold AMALLOC_STACK in *; lia
       | |- _ <= bv_unsigned _ - _ => rewrite unsigned_lit by (clear -SPR HspA LO BOT STK3; unfold AMALLOC_STACK in *; lia);
                                    clear -LO HspA BOT STK3; unfold AMALLOC_STACK in *; lia
       | |- @eq word _ _ => first [exact TP | reflexivity]
       | |- 16 <= _ <= 65536 => clear -NSR; lia
       | |- _ mod 8 = 0 => exact NM8
       | |- class_id _ = _ => exact HC0
       | |- rng _ _ _ => rewrite unsigned_lit by (clear -SPR HspA LO BOT STK3; unfold AMALLOC_STACK in *; lia);
                         eapply rng_sub'; [exact RSTK|]; clear -LO HspA SP47 BOT STK3; unfold AMALLOC_STACK in *; lia
       | |- exh_first_stmt => exact EXHW
       | |- aresv_ok _ _ => exact ROK
       | |- bv_unsigned _ < 2 ^ 63 => rewrite unsigned_lit by (clear -SPR HspA LO BOT STK3; unfold AMALLOC_STACK in *; lia); clear -SP47 HspA; lia
       | |- bv_unsigned _ < 32 => exact FC
       | |- _ -> axflag _ _ _ _ => intros NC24x; exact (C6F4 c HCK NC24x)
       | |- axg _ _ _ _ => exact C6G4
       | |- context [a_emb _] => exact CAPB
       | |- forall _, _ => idtac
       end.
  1: {
       intros st2 RNG' ms' RF. unfold aret_xf in RF. cbv zeta in RF. pose proof atop_range as ATR.
       pose proof C6G4 as (_ & ECp & _ & ECLp). unfold emb_cells in ECp. unfold emb_clr in ECLp.
       destruct (a_emb st) as [[d0 cap0] sz0] eqn:EA. destruct (a_emb st2) as [[d2 cap2] sz2] eqn:EA2.
       destruct RF as (FPLE & t0r & t1r & t2r & a1r & a2r & a3r & a4r & a5r & a6r & a7r & t3r & t4r & t5r & t6r & mr
                       & -> & MIr & STr & STEQ & ARr & ARNGr & AXFr & AXGr & (d1 & cap1 & MUr & PV1 & PV2 & TOP1)).
       assert (USP : bv_unsigned (Z_to_bv 64 (bv_unsigned spA + -128)) = bv_unsigned sp - 2272)
         by (rewrite unsigned_lit by (clear -SPR HspA LO BOT ATR; lia); clear -HspA; lia).
       rewrite USP in MUr, STr.

       assert (B0 : bufok RESV st d0 cap0).
       { unfold bufok. destruct (Z.eqb_spec cap0 0) as [E0|NZ]; [left; lia|]. right.
         destruct ECp as (_ & _ & _ & _ & _ & _ & _ & _ & TOP & _). split; [exact TOP|]. destruct ECLp as [Q|Q]; [exfalso; exact (NZ Q)| exact Q]. }
       assert (B1 : bufok RESV st d1 cap1).
       { destruct (Z_le_gt_dec cap1 0) as [LE|GT]; [left; exact LE|]. destruct PV1 as [[E1 E2]|AV]; [rewrite E1, E2; exact B0|].
         right. split; [destruct TOP1 as [Q|Q]; [lia| exact Q]| exact AV]. }
       assert (B2 : bufok RESV st d2 cap2).
       { destruct PV2 as [[E1 E2]|AV]; [rewrite E1, E2; exact B0|].
         pose proof AXGr as (_ & EC2 & _). unfold emb_cells in EC2. rewrite EA2 in EC2. destruct (Z.eqb_spec cap2 0) as [E0|NZ]; [left; lia|]. right.
         destruct EC2 as (_ & _ & _ & _ & _ & _ & _ & _ & TOP & _). split; [exact TOP| exact AV]. }

       set (SPc := bv_unsigned sp - 2272) in *.
       assert (SPHIc : ATOP <= SPc) by (subst SPc; clear -LO BOT; lia).
       assert (SPHI : ATOP <= bv_unsigned spA) by (clear -LO BOT HspA; lia).
       set (Wf := [(SPc - 2096, SPc); (al_t L + 208, al_t L + 2768); (aregion_info L c, aregion_info L c + 8);
                   (aregion_info L c + 68, aregion_info L c + 69); (AEMB, AEMB + 56); (d0, d0 + cap0); (d1, d1 + cap1); (d2, d2 + cap2)]%Z).
       change (munch Wf m4 mr) in MUr.
       assert (PCSfA : Forall (nf_pieceA L RESV st SPc c) Wf).
       { assert (BK : forall d cap, bufok RESV st d cap -> nf_pieceA L RESV st SPc c (d, d + cap)).
         { intros d cap [B|[Bt Ba]] LT; cbn [fst snd] in LT; [lia|]. unfold nf_kindA, nf_kind. cbn [fst snd].
           replace (d + cap - d) with cap by lia. split; [do 4 right; left; split; assumption|]. right; right. split; [exact Bt|].
           unfold avoids_all in *. rewrite forallb_app in Ba. apply andb_prop in Ba as [Ba _]. exact Ba. }
         subst Wf. repeat (apply Forall_cons); try apply Forall_nil; try (apply BK; assumption); intros _; unfold nf_kindA, nf_kind; cbn [fst snd].
         - split; [left; subst SPc; clear -LO BOT; lia| right; left; subst SPc; unfold AERRNO, ATP; clear -LO BOT ATR; lia].
         - split; [right; left; clear; lia| unfold AERRNO, ATP; clear -TIMG TIMGa TIMGb; lia].
         - split; [right; right; left; clear; lia| right; left; unfold aregion_info, K_SPACE_SIZE, ARI_STRIDE, AERRNO, ATP; change (2^37) with 137438953472; clear -SP1 C16; lia].
         - split; [right; right; left; clear; lia| right; left; unfold aregion_info, K_SPACE_SIZE, ARI_STRIDE, AERRNO, ATP; change (2^37) with 137438953472; clear -SP1 C16; lia].
         - split; [right; right; right; left; clear; lia| left; unfold AEMB, AERRNO, ATP; clear; lia]. }
       pose proof (nf_pieceA_piece _ _ _ _ _ _ PCSfA) as PCSf.
       assert (OUTS : forall x, SPc <= x -> outside Wf x)
         by (intros x Hx; apply (nf_outside L RESV st SPc c ALO ROK HCK SPHIc Wf x PCSf); left; exact Hx).

       assert (FRar : rw_cells bsegs mr (bv_unsigned spA + -128)
                        [CB 8 fr0; C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 16); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5;
                         C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
       { replace (bv_unsigned spA + -128) with (bv_unsigned sp - 2272) by (clear -HspA; lia).
         eapply cells_frameO; [exact FRa| exact MUr|]. intros x Hx. apply OUTS. subst SPc. clear -Hx. lia. }
       pose proof ARr as (_ & RTr & _).
       destruct RTr as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & OOM3r & _).
       destruct OOM3r as [oombr OOMr]. rw_split OOMr 2%nat OOMxr RSSr. clear RSSr.

       apply implS_ret.
       replace (ret_pc (Z_to_bv 64 0x3d8f8)) with (Z_to_bv 64 0x3d8f8) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
       pose proof ARNGr as (RIMGr & _).
       assert (RSTKr : rng RNG' lo (bv_unsigned spA - lo)) by (eapply rng_fp_leG; [exact FPLE | exact RSTK]).
       eapply evtF_mono.
       { eapply (allocN_spec RNG' spA gp tp t0r t1r t2r _ _ a1r a2r a3r a4r a5r a6r a7r _ _ _ _ _ _ _ _ _ _ t3r t4r t5r t6r
                   s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra _ _ fr0 oombr F fc mr lo);
           first [ exact FRar | exact MIr | exact OOMxr | exact RIMGr | exact RSTKr
                 | replace (bv_unsigned spA + -128) with (bv_unsigned sp - 2272) by (clear -HspA; lia); exact STr
                 | clear -BOT ATR; lia
                 | clear -LO HspA; lia ]. }
       cbv beta. intros ms1 P1.
       destruct P1 as (t0n & t1n & t2n & a1n & a2n & a3n & a4n & a5n & a6n & a7n & t3n & t4n & t5n & t6n & m1 & -> & MU1 & WM1 & MI1 & ST1 & OOM1).

       assert (AXFSr : axflags L st2 mr).
       { intros c' Hc' NC'. destruct (Z.eq_dec c' c) as [->|NE]; [exact AXFr|].
         pose proof (C6F4 c' Hc' NC') as F4. unfold axflag in *.
         assert (EXE : exh_mem c' st2 = exh_mem c' st).
         { destruct STEQ as [[_ ->]|[_ [e2 ->]]]; [apply init_cache_exh|]. rewrite exh_mem_set_emb, (exh_mem_set_other c c' _ NE). apply init_cache_exh. }
         rewrite EXE. eapply cells_frameO; [exact F4| exact MUr|]. cbn [cells_size csize Nat.add]. intros x Hx.
         apply (nf_flag_outside L RESV st SPc c ALO ROK HCK SPHIc Wf c' x PCSf Hc' NE). clear -Hx. lia. }
       destruct (c6_frame L RESV RNG' st2 mr m1 _ ALO ROK AXGr AXFSr MU1) as [C6G2 C6F2].
       { apply Forall_cons; [unfold c6_piece, AOOM; cbn [fst snd]; intros _; do 8 right; left; clear; lia| apply Forall_nil]. }

       assert (AR2 : AREP (AH DI AQ ASEC AFK) L st2 X m1).
       { eapply (AREP_frame_null _ HL L st2 X mr m1 (bv_unsigned sp) ALO ARr); [| exact WM1| clear -LO BOT; lia| exists (Z_to_bv 8 1); exact OOM1].
         eapply munch_weaken; [| exact MU1]. unfold sub_fp, AOOM. cbn [outside]. intros q Hq. clear -Hq. split; [lia| exact I]. }
       assert (LIVE2 : a_live st2 = a_live st).
       { pose proof (init_cache_fields st) as (E1 & _). destruct STEQ as [[_ ->]|[_ [e2 ->]]]; [exact E1|]. rewrite <- E1. destruct (init_cache st); reflexivity. }
       pose proof (ablocks_same L st st2 X X LB BL eq_refl LIVE2) as BL2.
       pose proof (munch_app _ _ _ _ _ MU4 (munch_app _ _ _ _ _ MUr MU1)) as MUt.
       assert (PCSt : Forall (nf_pieceA L RESV st (bv_unsigned spA) c)
                        ([(bv_unsigned spA - 176, bv_unsigned spA)] ++ Wf ++ [(AOOM, AOOM + 1)])%Z).
       { apply Forall_app. split; [| apply Forall_app; split].
         - apply Forall_cons; [| apply Forall_nil]. intros _. unfold nf_kindA, nf_kind. cbn [fst snd].
           split; [left; clear -LO BOT HspA; lia| right; left; unfold AERRNO, ATP; clear -LO BOT HspA ATR; lia].
         - eapply Forall_impl; [| exact PCSfA]. intros iv K. apply (nf_pieceA_SP L RESV st SPc (bv_unsigned spA) c iv); [subst SPc; clear -HspA; lia| exact K].
         - apply Forall_cons; [| apply Forall_nil]. intros _. unfold nf_kindA, nf_kind, AOOM. cbn [fst snd].
           split; [do 5 right; left; clear; lia| left; unfold AERRNO, ATP; clear; lia]. }
       destruct (nf_fake L RESV st (bv_unsigned spA) c _ ALO ROK HCK SPHI (nzl_pieces _ _ _ _ _ _ (nf_pieceA_piece _ _ _ _ _ _ PCSt))) as (D72 & FU & D48).
       pose proof (hfD _ HLD L LB m m1 _ HFK (munch_nzl _ _ _ MUt) D72 FU D48) as HFK2.
       assert (PRESf : aheap_pres CI LB (bv_unsigned spA) m m1).
       { intros a Ha CL.
         pose proof (nf_client_outsideA L RESV st X (bv_unsigned spA) c ALO ROK HCK SPHI CI CI_OK CI_OK3 WF LB _ a BL PCSt Ha CL) as OUT.
         assert (E : m1 (wa a) = m (wa a)) by (apply MUt; rewrite wa_unsigned by exact Ha; exact OUT).
         split; [exact E|]. intros Hw. rewrite (AFrameD.TwinB.wview_agree bsegs m m1 (wa a) E). exact Hw. }

       unfold aallocate_post_x. cbn [fst snd]. split.
       { unfold c6_at. cbn [ms_mem]. split; [exact C6G2| exact C6F2]. }
       split; [exact FPLE|]. do 14 eexists. exists m1. split; [reflexivity|]. split; [exact MI1|]. split; [exact ST1|]. split; [exact PRESf|].
       split; [exact ALO|]. split; [exact ARNGr|]. split; [exists X; split; [exact AR2| exact BL2]| exact HFK2]. }

  intros st_pre X_pre RNG1 m_pre cnt k ms1 CRET. destruct CRET as (CRET & EMBp & EXHp & AXFp & AXGp). unfold calloc_retG in CRET.
  destruct CRET as (FPLE & ARp & ARNGp & HCNT & POS & NK & NB & KR & XB & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & MUc & WMc & MIp
                    & t0d & t1d & t2d & a1d & a2d & a3d & a4d & a5d & a6d & a7d & t3d & t4d & t5d & t6d & m1 & stj1 & -> & MU1 & WM1 & MI1 & ST1 & CR1 & STS1).
  rewrite ?unsigned_lit in MUc by (clear -SPR HspA LO BOT STK3; unfold AMALLOC_STACK in *; lia).
  rewrite ?unsigned_lit in MU1 by (clear -SPR HspA LO BOT STK3; unfold AMALLOC_STACK in *; lia).
  rewrite ?unsigned_lit in ST1 by (clear -SPR HspA LO BOT STK3; unfold AMALLOC_STACK in *; lia).
  replace (bv_unsigned spA + -128) with (bv_unsigned sp - 2272) in ST1 by (clear -HspA; lia).
  cbn beta iota. apply implS_ret.
  replace (ret_pc (Z_to_bv 64 0x3d8f8)) with (Z_to_bv 64 0x3d8f8) by (symmetry; apply ret_pc_even; [lia|reflexivity]).

  pose proof ARp as AR0. destruct AR0 as (WF' & RT' & INST' & THR' & CLS' & HQ' & HS' & HD' & HRO' & RT2' & AVL' & RT3').
  destruct THR' as (T0' & T40' & CACHES' & CSTATS' & [sj' [STATS' LSJ']] & UNW').
  pose proof WF' as WF0. destruct WF0 as (SBE' & PAE' & SAL' & SLO' & SHI' & PERC' & OUTC' & BUSY' & LIVE' & FRESH' & UNIQ').
  destruct (PERC' c HCK) as (B1' & B2' & B3' & B4' & B5' & B6' & B7' & LENF' & LENC' & CNTB' & ND' & RANGE').
  destruct (kit_cache_pop _ L st_pre X_pre m_pre c cnt ARp HCK HCNT POS) as (k' & chunks & NK' & _ & _ & CR & CH & LCH & NTH & JK & FSH).
  assert (EK : k' = k) by (rewrite NK in NK'; injection NK'; intros E; symmetry; exact E). subst k'.

  set (S := size_of_class c) in *.
  set (AB := aslot_addr L c k) in *.
  assert (KSF : 0 <= k * S /\ k * S + S <= c_allocated_user (get_cls st_pre c) /\ (k * S) mod 16 = 0).
  { unfold ndist in KR. fold S in KR. fold S in SZB. fold S in SM16.
    assert (P0 : 0 <= k * S) by (clear -KR SZB; apply Z.mul_nonneg_nonneg; lia).
    assert (Q1 : k + 1 <= c_allocated_user (get_cls st_pre c) / S) by (clear -KR; lia).
    assert (M1 : (k + 1) * S <= c_allocated_user (get_cls st_pre c) / S * S) by (apply Z.mul_le_mono_nonneg_r; clear -Q1 SZB; lia).
    pose proof (Z.mul_div_le (c_allocated_user (get_cls st_pre c)) S ltac:(clear -SZB; lia)) as M2.
    split; [exact P0|]. split.
    - rewrite Z.mul_add_distr_r, Z.mul_1_l in M1. rewrite (Z.mul_comm S) in M2. clear -M1 M2 P0 SZB. lia.
    - destruct (proj1 (Z.mod_divide S 16 ltac:(clear; lia)) SM16) as [q Hq]. rewrite Hq.
      replace (k * (q * 16)) with ((k * q) * 16) by (clear; lia). apply Z_mod_mult. }
  destruct KSF as (KS0 & KS1 & KS2).
  assert (GEO : al_space_beg L <= AB /\ AB + S <= al_space_beg L + K_SPACE_SIZE /\ AB mod 16 = 0
                /\ AB + S <= aregion L c + c_allocated_user (get_cls st_pre c) /\ aregion L c <= AB).
  { subst AB. unfold aslot_addr, aregion, K_REGION, K_SPACE_SIZE, K_FREEARR_OFF, K_ALIGN in *. fold S.
    remember (k * S) as KS eqn:HKS. clear HKS.
    change (2^37) with 137438953472. change (2^32) with 4294967296 in *.
    split; [clear -KS0 C16; lia|]. split; [clear -KS1 B1' B2' C16 NSZ; lia|]. split; [| clear -KS0 KS1 B1'; lia].
    clear -SP3 C16 KS2. Z.div_mod_to_equations; lia. }
  destruct GEO as (G1 & G2 & G3 & G4 & G5). unfold K_SPACE_SIZE in G2. change (2^37) with 137438953472 in G2.
  assert (EAB : AB = aslot_addr L c k) by reflexivity. clearbody AB.
  assert (ES : S = size_of_class c) by reflexivity.

  assert (RZC : rz_size n = 16 \/ 32 <= rz_size n) by (clear -RZR RZM; Z.div_mod_to_equations; lia).
  destruct (slot_carveG m_pre AB S n (rz_size n) JK RZC ltac:(clear -N; lia) ltac:(fold S in NSZ; clear -NSZ NS RSR; lia))
    as (b0 & b1 & szh & szl & ctxj & uj & j1 & j2 & HDR & B1 & UJ & LH & TL).
  set (UB := AB + rz_size n) in *. assert (EUB : UB = AB + rz_size n) by reflexivity. clearbody UB.

  set (grz := shlen (rz_size n)). set (g := shlen (n - n mod 8)). set (room := if n mod 8 =? 0 then 0 else 1).
  assert (GR12 : grz = rz_size n / 8 /\ g = (n - n mod 8) / 8).
  { subst grz g. unfold shlen. rewrite !Z.shiftr_div_pow2 by lia. split; reflexivity. }
  destruct GR12 as [GR1 GR2].
  assert (GR3 : 2 <= grz) by (rewrite GR1; generalize RZR; clear; intros; Z.div_mod_to_equations; lia).
  assert (GR4 : 0 <= g) by (rewrite GR2; generalize N; clear; intros; Z.div_mod_to_equations; lia).
  assert (GR5 : 0 <= room <= 1) by (subst room; clear; destruct (n mod 8 =? 0); lia).
  assert (GR6 : grz + g + room <= shlen S).
  { rewrite GR1, GR2. subst room. unfold shlen. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
    fold S in NSZ. fold S in SM16. generalize NSZ NS RSR RSM SM16 RZM RZR N. clear. intros.
    destruct (Z.eqb_spec (n mod 8) 0) as [M0|M0]; Z.div_mod_to_equations; lia. }
  assert (GR7 : shad UB = shad AB + grz).
  { rewrite GR1, EUB. unfold shad, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
    generalize G3 RZM RZR. clear. intros. Z.div_mod_to_equations. lia. }
  assert (GR89 : 0x2008fff7000 <= shad AB /\ shad AB + shlen S <= 0x10007fef8000).
  { unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
    unfold K_SPACE_SIZE, K_SPACE_EXTRA in *. generalize G1 G2 SP1 SP2. clear. intros. Z.div_mod_to_equations. lia. }
  destruct GR89 as [GR8 GR9].
  destruct (shadow_carve m_pre (shad AB) (shlen S) grz g room FSH GR3 GR4 GR6 GR5) as (SHA & SHpre & [sjunk SHU] & SHP & SHsuf).
  rewrite <- GR7 in SHU, SHP, SHsuf.
  set (PG := shad UB + g) in *.

  pose proof RT' as RT0.
  destruct RT0 as (GPG' & GOT' & GOT80' & RIC' & LS1' & REAL' & IMAX4' & FLG5' & FLG' & HPP' & SHB' & CANP' & TI' & TK' & INI2' & LAY' & MCS' & OOM3'
                    & PGC' & HK2' & CF8' & CF34' & CSMT' & T88' & TSD' & LS2' & CT8' & CT').
  pose proof INI2' as INI'. rw_split INI' 1%nat INI1' INIx. clear INIx.
  destruct OOM3' as [oomb' OOM']. rw_split OOM' 2%nat OOMx RSS'. clear OOMx.
  pose proof IMAX4' as IMAX'. rw_split IMAX' 3%nat IMAX3' IMAXx. clear IMAXx.
  pose proof HK2' as HK'. rw_split HK' 1%nat HK1' HKx. clear HKx.
  pose proof T0' as TT0'. rw_split TT0' 1%nat TTctx' TT'.
  destruct (junk_split m_pre (al_t L + 2768) 16 16 CSTATS' ltac:(lia) ltac:(lia)) as [CSa CSb].
  destruct (junk_split m_pre (al_t L + 2768 + 16) 8 8 CSb ltac:(lia) ltac:(lia)) as [CS8 CSc].
  replace (al_t L + 2768 + 16) with (al_t L + 2784) in CS8 by lia.
  replace (al_t L + 2768 + 16 + 8) with (al_t L + 2792) in CSc by lia.
  destruct INST' as (I32' & I48' & I64' & I72' & I112' & I680' & I984' & I40' & I56').
  pose proof ARNGp as ARNGp0. destruct ARNGp as (RIMG' & RT4' & RCTX' & RNO' & RST' & RRI' & RFK' & RSFK' & RDTLS' & RCLS' & RPA' & RSECS' & RPSH').
  destruct (RCLS' c HCK) as (RREG & RSREG & RFA & RSFA).

  destruct (alayout_slot_disj L AB 65536 ALO G1 ltac:(unfold K_SPACE_SIZE, K_FREEARR_OFF, aregion, K_REGION in *; generalize G4 B1' B2' C16 SP1 SZB; clear; intros; change (2^37) with 137438953472; lia) ltac:(clear; lia))
    as (DJT & DJC & DJN & DJS & DJF).
  assert (RUf : rng RNG1 (UB - 16) (n + 16)) by (eapply rng_sub'; [exact RREG|]; generalize G4 G5 B1' RZR N EUB KS0 NSZ NS RSR; clear; intros; lia).
  assert (RABf : rng RNG1 AB 16) by (eapply rng_sub'; [exact RREG|]; generalize G4 G5 B1' RZR N NSZ NS RSR; clear; intros; lia).
  assert (REG8 : aregion L c mod 8 = 0 /\ c_mapped_user (get_cls st_pre c) mod 8 = 0).
  { unfold aregion, K_REGION, K_USER_MAP, K_ALIGN in *. generalize SP3 B4'; clear; intros. Z.div_mod_to_equations; lia. }
  assert (SHM : shad (aregion L c) <= shad AB /\ shad UB + g + room <= shad (aregion L c) + shlen (c_mapped_user (get_cls st_pre c))).
  { rewrite GR7, GR2, GR1. unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
    fold S in NSZ. fold S in SM16. subst room. generalize G4 G5 B1' N NSZ RSR RSM NS RZR RZM SM16 G3 EUB REG8; clear; intros.
    destruct (Z.eqb_spec (n mod 8) 0); Z.div_mod_to_equations; lia. }
  destruct SHM as [SHM1 SHM2].
  assert (RSAf : rng RNG1 (shad AB) 1) by (eapply rng_sub'; [exact RSREG|]; generalize SHM1 SHM2 GR3 GR4 GR5 GR7; clear; intros; lia).
  assert (RSUf : rng RNG1 (shad UB) (shlen (n - n mod 8))).
  { eapply rng_sub'; [exact RSREG|]. fold g. generalize SHM1 SHM2 GR3 GR4 GR5 GR7. clear. intros. lia. }
  assert (RSPf : n mod 8 <> 0 -> rng RNG1 PG 1).
  { intros NE. eapply rng_sub'; [exact RSREG|]. subst PG.
    assert (R1 : room = 1) by (subst room; generalize NE; clear; intros NE; destruct (Z.eqb_spec (n mod 8) 0); [exfalso; exact (NE ltac:(assumption)) | reflexivity]).
    rewrite R1 in SHM2. generalize SHM1 SHM2 GR3 GR4 GR7; clear; intros. lia. }
  assert (SLS : shlen S <= 8192) by (fold S in NSZ; unfold shlen; rewrite Z.shiftr_div_pow2 by (clear; lia); change (2^3) with 8; clear -NSZ; Z.div_mod_to_equations; lia).
  assert (SB34 : 0 <= shlen (n - n mod 8) <= 8192 /\ PG + 1 <= 0x10007fff8000).
  { subst PG. fold g. rewrite GR7. generalize GR4 GR6 GR9 GR3 GR5 SLS; clear; intros; lia. }
  destruct SB34 as [SB3 SB4].
  assert (RCTX4' : rng RNG1 (al_ctx L) 4096) by (eapply rng_sub'; [exact RCTX'|]; clear; lia).
  assert (DJC4 : al_ctx L + 4096 <= AB \/ AB + 65536 <= al_ctx L) by (generalize DJC; clear; intros; lia).
  assert (CNT16 : 0 < cnt <= 16).
  { unfold max_count in CNTB'. generalize POS HCNT CNTB' MCB; clear. destruct (a_cinit st_pre); intros; lia. }
  assert (PGE : PG = shad UB + shlen (n - n mod 8)) by reflexivity.
  assert (RSTK1 : rng RNG1 lo (bv_unsigned spA - lo)) by (eapply rng_fp_le; [exact FPLE | exact RSTK]).

  set (mu0 := c_mapped_user (get_cls st c)) in *.
  assert (OBJ : aregion_info L c = al_space_beg L + 137438953472 + c * 128 /\ aregion L c = al_space_beg L + c * 4294967296
                /\ shad (al_space_beg L + c * 4294967296) + 536870912 <= 17594333495296).
  { unfold aregion_info, aregion, K_REGION, K_SPACE_SIZE, ARI_STRIDE. change (2^37) with 137438953472. change (2^32) with 4294967296.
    split; [reflexivity|]. split; [reflexivity|]. rewrite shad_div. clear -SP1 SP2 C16. unfold ASHOFF, K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^37) with 137438953472 in *.
    Z.div_mod_to_equations. lia. }
  destruct OBJ as (RIE & RBE & SHHI).
  assert (MU41 : munch [(bv_unsigned sp - 3856, bv_unsigned sp - 2272); (al_t L + 208, al_t L + 3168); (AINSTANCE, AINSTANCE + 728);
                        (al_space_beg L + 137438953472 + c * 128, al_space_beg L + 137438953472 + c * 128 + 128);
                        (al_space_beg L + c * 4294967296 + mu0, al_space_beg L + c * 4294967296 + 4294967296);
                        (shad (al_space_beg L + c * 4294967296 + mu0), shad (al_space_beg L + c * 4294967296) + 536870912)]%Z m4 m1).
  { eapply munch_trans; [eapply munch_weaken; [| exact MUc] | eapply munch_weaken; [| exact MU1]];
      unfold sub_fp; cbn [outside]; intros q Hq; rewrite ?RIE, ?RBE in *; unfold K_REGION, acache_addr in *; change (2^32) with 4294967296 in *;
      rewrite ?shlen_div in *; change (4294967296 / 8) with 536870912 in *; clear -Hq HspA C16; lia. }
  assert (WM41 : wmono bsegs m4 m1) by (eapply wmono_trans; [exact WMc | exact WM1]).
  unfold K_SPACE_SIZE, K_SPACE_EXTRA in SP2. change (2^37) with 137438953472 in SP2.
  xport FRa MU41 WM41 ltac:(clear -HspA SPS STOP SPR LO BOT STK3 TL1 TL2 SP1 SP2 C16 SHHI TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold AMALLOC_STACK, AINSTANCE in *; lia).
  xport SS MU41 WM41 ltac:(clear -HspA SPS STOP SPR LO BOT STK3 TL1 TL2 SP1 SP2 C16 SHHI TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold AMALLOC_STACK, AINSTANCE in *; lia).
  xport TB MU41 WM41 ltac:(rewrite LTB; clear -HspA SPS STOP SPR LO BOT STK3 TL1 TL2 SP1 SP2 C16 SHHI TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold AMALLOC_STACK, AINSTANCE in *; lia).

  xport HDR MU1 WM1 ltac:(clear -HspA DJT SPR SP2 G1 G2 EUB RZR N NSZ NS RSR LO BOT STK3 C16; unfold acache_addr, AMALLOC_STACK, K_SPACE_SIZE in *; lia).
  xport UJ MU1 WM1 ltac:(clear -HspA DJT SPR SP2 G1 G2 EUB RZR N NSZ NS RSR LO BOT STK3 C16; unfold acache_addr, AMALLOC_STACK, K_SPACE_SIZE in *; lia).
  xport SHA MU1 WM1 ltac:(cbv delta [g grz room PG] in *; clear -HspA SPR GR1 GR2 GR3 GR4 GR5 GR6 GR7 GR8 GR9 LO BOT STK3 TL1 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport SHU MU1 WM1 ltac:(cbv delta [g grz room PG] in *; clear -HspA SPR GR1 GR2 GR3 GR4 GR5 GR6 GR7 GR8 GR9 SB3 LO BOT STK3 TL1 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  assert (SHP1 : n mod 8 <> 0 -> rw_cells bsegs m1 PG [C1 (Z_to_bv 8 250)]).
  { intros NE. specialize (SHP ltac:(subst room; generalize NE; clear; intros NE; destruct (Z.eqb_spec (n mod 8) 0); [exfalso; exact (NE ltac:(assumption)) | reflexivity])).
    xport SHP MU1 WM1 ltac:(cbv delta [g grz room PG] in *; clear -HspA SPR GR1 GR2 GR3 GR4 GR5 GR6 GR7 GR8 GR9 SB3 SB4 LO BOT STK3 TL1 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia). exact SHP. }
  assert (LH1 : 16 < rz_size n -> rw_cells bsegs m1 AB [C8 j1; C8 j2]).
  { intros R16. pose proof (proj1 (LH R16)) as LH0.
    xport LH0 MU1 WM1 ltac:(clear -HspA DJT SPR SP2 G1 G2 EUB RZR N NSZ NS RSR LO BOT STK3 C16; unfold acache_addr, AMALLOC_STACK, K_SPACE_SIZE in *; lia). exact LH0. }
  xport GOT' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport GOT80' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport REAL' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport SHB' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport CANP' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport HPP' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport CSMT' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport FLG5' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport FLG' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport HK1' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport LS1' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport LS2' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport LAY' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport MCS' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport CF34' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport INI1' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport RSS' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport IMAX3' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport TI' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport TK' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport T88' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, ATP88, AMALLOC_STACK in *; lia).
  xport TSD' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, ATSD, AMALLOC_STACK in *; lia).
  xport CT' MU1 WM1 ltac:(ub CL5; clear -HspA Y SPR TL1 CL1 CL2 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb CTXi CBND CBNDa CBNDb; unfold acache_addr, AMALLOC_STACK, AIMG_HI in *; lia).
  xport CT8' MU1 WM1 ltac:(ub CL5; clear -HspA Y SPR TL1 CL1 CL2 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb CTXi CBND CBNDa CBNDb; unfold acache_addr, AMALLOC_STACK, AIMG_HI in *; lia).
  xport TTctx' MU1 WM1 ltac:(clear -HspA SPR TL1 TL2 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport UNW' MU1 WM1 ltac:(clear -HspA SPR TL1 TL2 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport STATS' MU1 WM1 ltac:(rewrite LSJ'; clear -HspA SPR TL1 TL2 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, ASTATS_WORDS, AMALLOC_STACK in *; lia).
  assert (DEP1 : ADEPOT DI L m1).
  { eapply (adi_frame DI); [exact HD' | exact MU1 | exact WM1 |]. unfold acache_addr.
    repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq; ub DL7; ub DL8; clear -Hq Y Y0 HspA SPR TL1 TL2 DL1 DL2 DL3 DL4 DL5 DL6 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb NODi NBND NBNDa NBNDb STOi SBND SBNDa SBNDb; unfold AMALLOC_STACK, AIMG_HI in *; lia|]).
    apply Forall_nil. }

  assert (PF : pfactsG (bv_unsigned spA) (al_t L) (al_space_beg L) c mu0 ATOP lo).
  { unfold pfactsG. pose proof (ao_t L ALO) as OT. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in OT.
    unfold AMALLOC_STACK, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN, K_FREEARR_OFF, K_USER_MAP in *. change (2^37) with 137438953472 in *.
    ub TSP. generalize LOA SPV LO BOT SP47 STK2 STK3 OT SP1 SP2 SAL C16 A1 A2 A4 Y. clear. intros.
    repeat match goal with H : _ /\ _ |- _ => destruct H end.
    repeat split; first [reflexivity | assumption | lia | Z.div_mod_to_equations; lia]. }
  assert (MUall : munch [(bv_unsigned spA - 4096, bv_unsigned spA); (al_t L + 208, al_t L + 3169); (AINSTANCE, AINSTANCE + 728);
                         (al_space_beg L + 137438953472 + c * 128, al_space_beg L + 137438953472 + c * 128 + 128);
                         (al_space_beg L + c * 4294967296 + mu0, al_space_beg L + c * 4294967296 + 4294967296);
                         (shad (al_space_beg L + c * 4294967296 + mu0), shad (al_space_beg L + c * 4294967296) + 536870912)]%Z m m_pre).
  { eapply munch_trans; [eapply munch_weaken; [| exact MU4] | eapply munch_weaken; [| exact MUc]];
      unfold sub_fp; cbn [outside]; intros q Hq; rewrite ?RIE, ?RBE in *; unfold K_REGION in *; change (2^32) with 4294967296 in *;
      rewrite ?shlen_div in *; change (4294967296 / 8) with 536870912 in *; clear -Hq HspA; lia. }
  assert (WMall : wmono bsegs m m_pre) by (eapply wmono_trans; [exact WM4 | exact WMc]).

  assert (BB : forall b, In b (x_busy X) ->
      al_space_beg L <= xb_alloc L b /\ xb_alloc L b + size_of_class (xb_class b) <= al_space_beg L + 137438953472
      /\ (xb_alloc L b + size_of_class (xb_class b) <= al_space_beg L + c * 4294967296 + mu0 \/ al_space_beg L + c * 4294967296 + 4294967296 <= xb_alloc L b)).
  { intros b Hb. destruct (BUSY b Hb) as [CLB _].
    destruct (PERC (xb_class b) CLB) as (Q1 & Q2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & QR).
    pose proof (size_of_class_facts (xb_class b) CLB) as [QS _].
    assert (KB : 0 <= xb_slot b < ndist st (xb_class b)).
    { apply QR. apply in_app_iff. right. apply in_app_iff. right. unfold busy_slots. apply in_map_iff. exists b. split; [reflexivity|].
      apply filter_In. split; [exact Hb| apply Z.eqb_refl]. }
    pose proof (slot_in_region L st (xb_class b) (xb_slot b) ltac:(clear -QS; lia) (proj1 Q1) KB) as (P5 & P4 & P0).
    unfold xb_alloc. unfold K_NUM_CLASSES in CLB. unfold K_FREEARR_OFF in Q2.
    destruct (Z.eq_dec (xb_class b) c) as [EC|NC].
    - rewrite EC in P5, P4, Q1, Q2 |- *. rewrite RBE in P5, P4. change (c_mapped_user (get_cls st c)) with mu0 in Q1, Q2.
      clear -P5 P4 Q1 Q2 A1 A2 C16. unfold K_FREEARR_OFF in *. lia.
    - pose proof (region_other_geo L c (xb_class b) ALO ltac:(clear -C16; lia) CLB NC) as (R1 & R2 & R3 & _). rewrite RBE in R2.
      clear -P5 P4 Q1 Q2 R1 R2 R3 A1. lia. }
  pose proof (ao_fake L ALO) as FKO. unfold aobj in FKO. pose proof (ao_res L ALO) as ORS. unfold aobj in ORS. pose proof (ao_space L ALO) as RSP.
  pose proof (ad_fake_res L ALO) as D_f_res. pose proof (ad_t_fake L ALO) as D_t_f. pose proof (ad_dtls_res L ALO) as D_d_res. pose proof (ad_t_dtls L ALO) as D_t_d.
  pose proof (ao_dtls L ALO) as ODT. unfold aobj in ODT. unfold adisj in D_f_res, D_t_f, D_d_res, D_t_d.
  assert (FKD : forall cls FA sz, In (mkABlock (ABFake cls) FA sz) LB -> al_fake L <= FA /\ 0 <= sz /\ FA + sz <= al_fake L + 11571200)
    by (intros cls FA sz Hin; exact (proj1 (proj2 BL) cls FA sz Hin)).
  assert (PRES : aheap_pres CI LB (bv_unsigned spA) m m_pre).
  { intros a Ha CL. split; [| intros Hw; apply WMall; exact Hw].
    apply MUall. rewrite wa_unsigned by exact Ha.
    destruct CL as [STa | [CIa | [BLK | SH]]].
    - eapply disjoint_outside; [eapply (Q_stack _ _ _ _ _ _ _ PF a 1); clear -STa; lia | clear; lia].
    - destruct CIa as (iv & Hiv & R). pose proof (proj1 (Forall_forall _ _) CI_OK iv Hiv) as (Q1 & Q2 & Q3).
      pose proof (proj1 (Forall_forall _ _) CI_OK2 iv Hiv) as Q4. cbn [fst snd] in *.
      eapply disjoint_outside; [eapply (Q_img _ _ _ _ _ _ _ PF a 1); unfold AIMG_HI in *; clear -R Q1 Q3 Q4; lia | clear; lia].
    - destruct BLK as (b & Hb & R). destruct b as [[p|cls] A n']; cbn [ab_addr ab_size] in R.
      + destruct (proj1 BL p A n' Hb) as [(xb & Hxb & Sb & Ub & Nb)|(mb0 & ms0 & Lp & EUA & Gs)].
        * destruct (BB xb Hxb) as (Bb1 & Bb2 & Bb3).
          pose proof (awf_fits L st X xb WF Hxb) as FIT. unfold xb_fits in FIT. rewrite Sb in FIT. unfold xb_user in Ub. subst A n'.
          eapply disjoint_outside; [eapply (Q_slot _ _ _ _ _ _ _ PF a 1) | clear; lia]; clear -R Bb1 Bb2 Bb3 FIT; lia.
        *
          cbn [sec_wf1] in Gs. destruct Gs as (Gs1 & Gs2 & Gs3 & Gs4 & Gs5 & Gs6 & (Ct & Cc & Cr & Cp & Cn & Cs & Cf & Cd)).
          pose proof (sec_facts n' ltac:(clear -Gs5; lia) Gs6) as SF. subst A. unfold SEC_UOFF, K_HIGH_MEM in *.
          unfold ablk, KLS, AIMG_HI in Gs2.
          eapply disjoint_outside; [eapply (Q_obj _ _ _ _ _ _ _ PF a 1) | clear; lia]; clear -R Gs2 Gs3 Gs4 Gs5 SF Ct Cr RSP ORS; lia.
      + destruct (FKD cls A n' Hb) as (K1 & K2 & K3). atop_facts.
        eapply disjoint_outside; [eapply (Q_obj _ _ _ _ _ _ _ PF a 1) | clear; lia];
          clear -R K1 K3 FKO D_t_f D_f_res RSP OFKi OFKs OFKsa OFKsb; lia.
    - destruct SH as (a' & Ha' & ->).
      destruct Ha' as [STa | [CIa | FK]].
      + eapply disjoint_outside; [eapply (Q_shad_hi _ _ _ _ _ _ _ PF a'); unfold AMALLOC_STACK in *; clear -STa LO BOT STK3; lia | clear; lia].
      + destruct CIa as (iv & Hiv & R). pose proof (proj1 (Forall_forall _ _) CI_OK iv Hiv) as (Q1 & Q2 & Q3). cbn [fst snd] in *.
        eapply disjoint_outside; [eapply (Q_shad_img _ _ _ _ _ _ _ PF a'); unfold AIMG_HI in *; clear -R Q1 Q3; lia | clear; lia].
      + destruct FK as (cls & FA & sz & Hin & R). destruct (FKD cls FA sz Hin) as (K1 & K2 & K3). atop_facts.
        eapply disjoint_outside; [eapply (Q_shad_obj _ _ _ _ _ _ _ PF a') | clear; lia]; clear -R K1 K3 FKO D_f_res RSP OFKi OFKs OFKsa OFKsb; lia. }
  assert (HFKp : AFK L LB m_pre).
  { eapply (hf_frame _ HL L LB m m_pre); [exact HFK | exact MUall | exact WMall | exact (Q_tfs _ _ _ _ _ _ _ PF) |].
    unfold fake_untouched. pose proof (ao_t L ALO) as OT. unfold aobj in OT.
    assert (SHF : 2148262400 <= shad (al_fake L) /\ shad (al_fake L) + shlen 11571200 <= 17594332446720
                  /\ (shad (al_space_beg L + c * 4294967296) + 536870912 <= shad (al_fake L)
                      \/ shad (al_fake L) + shlen 11571200 <= shad (al_space_beg L + c * 4294967296 + mu0))
                  /\ shad (al_space_beg L + c * 4294967296) <= shad (al_space_beg L + c * 4294967296 + mu0)
                  /\ 2201439137792 <= shad (al_space_beg L + c * 4294967296)).
    { rewrite !shad_div, !shlen_div. unfold ASHOFF in *. destruct PF as (_ & _ & (F1 & F2 & F3 & F4 & F5 & F6) & _).
      clear -FKO F1 F2 F3 F4 F5 F6 D_f_res RSP OFKi OFKs OFKsa OFKsb. Z.div_mod_to_equations. dlia. }
    destruct SHF as (SF1 & SF2 & SF3 & SF4 & SF5).
    unfold AMALLOC_STACK, AINSTANCE in *. destruct PF as (PF1 & PF2 & PF3 & PF4).
    repeat (apply Forall_cons; [cbn [fst snd];
      clear -HspA LOA SPV LO BOT STK3 SP47 STK2 OT FKO ORS RSP ODT D_f_res D_t_f D_d_res D_t_d C16 PF3 PF4 SF1 SF2 SF3 SF4 SF5 SHHI TL1 TBND TBNDa TBNDb TIMG TIMGa TIMGb OFKi OFKs OFKsa OFKsb DBND DBNDa DBNDb DIMG DIMGa DIMGb;
      repeat (split; [lia|]); lia |]).
    apply Forall_nil. }

  eapply evtF_mono.
  { replace (bv_unsigned sp - 2272) with (bv_unsigned spA + -128) in ST1, FRa by (clear -HspA; lia).
    eapply (alloc_tail_D DI L RNG1 ra gp tp spA t0d t1d t2d a1d a2d a3d a4d a5d a6d a7d t3d t4d t5d t6d
              s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m1
              n (al_t L) c cnt AB UB PG room lo b0 b1 szh szl ctxj (1 + Z.of_nat (length trc)) SO pc
              (Z_to_bv 64 (max_count st_pre c)) (Z_to_bv 64 S) stj1 j1 j2 (Z_to_bv 8 250) sj' sjunk uj fr0 tb trc).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => exact ST1
         | |- mem_inv _ _ => exact MI1
         | |- allocA_cells _ _ _ => unfold allocA_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end)
         | |- poison_cells _ => unfold poison_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end)
         | |- ADEPOT _ _ _ => exact DEP1
         | |- In _ _ => exact TRU
         | |- u64arr _ _ (_ + 2800) _ => exact STATS'
         | |- u64arr _ _ _ _ => exact TB
         | |- map _ _ = _ => exact TRF
         | |- (16 < _) -> _ => exact LH1
         | |- ~ _ -> rng _ _ _ => exact RSPf
         | |- ~ _ -> _ => exact SHP1
         | |- is_primary _ = _ => exact PRIM
         end.
    all: try lazymatch goal with
         | |- rw_cells _ _ (_ + -16) _ => exact HDR
         | |- rw_cells _ _ (shad _) [C1 _] => exact SHA
         | |- rw_cells _ _ (shad _) [CB _ _] => exact SHU
         | |- rw_cells _ _ _ [CB _ _] => exact UJ
         | |- rw_cells _ _ (_ + 2784) _ => exact STS1
         | |- rw_cells _ _ (_ + 208 + _ * 80) _ => exact CR1
         | |- rw_cells _ _ _ _ => assumption
         | |- rng _ _ _ => assumption
         | |- _ \/ _ => first [exact DJT | exact DJN | exact DJS | exact DJC4 | unboxed CL5 | unboxed DL7 | unboxed DL8 | unboxed DL9 | unboxed DL10]
         | |- @eq Z _ _ => first [assumption | reflexivity | exact PGE | subst room; reflexivity]
         | |- @eq word _ _ => first [assumption | reflexivity]
         | |- @eq nat _ _ => first [exact LSJ' | exact LTB | assumption]
         end.
    all: try assumption.
    all: try (generalize N NR LO BOT SP47 STK1 STK2 STK3 SP1 SP2 SP4 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6
                         G1 G2 G3 G4 G5 EUB ES SM16 NSZ NS RSR RZR GR3 GR7 GR8 GR9 SB3 SB4 B1 POS HCNT CNT16 KS0 KS1 HC0 C16 LTRC HspA LOA SPV SPS STOP;
              clear; intros; rewrite ?HC0 in *; unfold AIMG_HI, AMALLOC_STACK, AREQMAX, UDEPTH, K_SPACE_SIZE, K_SPACE_EXTRA in *; lia).
    all: try (eapply rng_fp_le; [exact FPLE | exact RS]).
    all: try (clear -LTRC; lia).
    all: match goal with |- ?G => idtac "REMT" G end. }

  cbv beta. intros ms' PM.
  unfold aallocate_post_x. cbn [snd fst]. split.
  {
    pose proof PM as PM0. unfold malloc_post_gen in PM0.
    destruct PM0 as (id0 & t0e & t1e & t2e & a1e & a2e & a3e & a4e & a5e & a6e & a7e & t3e & t4e & t5e & t6e & m5 & sj5 & stj5 & EMS & MUt & _).

    assert (AXFall : axflags L st_pre m_pre).
    { intros c' Hc' NC'. destruct (Z.eq_dec c' c) as [->|NE]; [exact (AXFp NC')|].
      pose proof (C6F4 c' Hc' NC') as F4. unfold axflag in *.
      replace (exh_mem c' st_pre) with (exh_mem c' st)
        by (destruct EXHp as [E|E]; [symmetry; apply exh_mem_eq_list; exact E| rewrite (exh_mem_eq_list c' _ _ E); symmetry; apply exh_mem_clear_other; exact NE]).
      eapply cells_frameO; [exact F4| exact MUc|]. cbn [cells_size csize Nat.add]. intros x Hx. cbn [outside].
      assert (RIEj : forall j, aregion_info L j = al_space_beg L + 137438953472 + j * 128) by (intros j; unfold aregion_info, K_SPACE_SIZE, ARI_STRIDE; change (2^37) with 137438953472; reflexivity).
      rewrite (RIEj c') in Hx. rewrite (RIEj c). unfold aregion, K_REGION, AINSTANCE, K_NUM_CLASSES in *. change (2^32) with 4294967296.
      pose proof atop_range as ATRx.
      assert (SHT : shad (al_space_beg L + c * 4294967296) + shlen 4294967296 <= 17594333495296)
        by (rewrite shad_div, shlen_div; unfold ASHOFF, K_SPACE_SIZE, K_SPACE_EXTRA in *; change (2^37) with 137438953472 in *; clear -SP1 SP2 C16 ATRx; Z.div_mod_to_equations; lia).
      rewrite ?unsigned_lit by (clear -SPR HspA LO BOT STK3; lia).
      pose proof TSP as TSPx. unbox TSPx.
      unfold K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^37) with 137438953472 in *.
      clear -Hx Hc' NE C16 SP1 SP2 TL1 TL2 TL4 LO BOT STK3 HspA SHT A1 A2 ATRx SPR TSPx. unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in *. repeat split; lia. }
    destruct (c6_frame L RESV RNG1 st_pre m_pre m1 _ ALO ROK AXGp AXFall MU1) as [G1x F1x].
    { rewrite ?unsigned_lit by (clear -SPR HspA LO BOT STK3; lia).
      apply Forall_cons; [unfold c6_piece; cbn [fst snd]; intros _; left; clear -LO BOT STK3 HspA; lia|].
      apply Forall_cons; [unfold c6_piece, acache_addr; cbn [fst snd]; intros _; right; left; clear -C16; lia|].
      apply Forall_cons; [unfold c6_piece; cbn [fst snd]; intros _; right; left; clear; lia| apply Forall_nil]. }
    destruct (c6_frame L RESV RNG1 st_pre m1 m5 _ ALO ROK G1x F1x MUt) as [G5x F5x].
    { pose proof (ao_res L ALO) as (_ & _ & ORSx & _). pose proof (ao_space L ALO) as RSPx. pose proof atop_range as ATRx.
      assert (UBN : UB + n <= AB + S) by (clear -EUB NS NSZ RSR ES; lia).
      repeat (apply Forall_cons; [unfold c6_piece; cbn [fst snd]; intros NEk;
        first [ left; clear -LO LOA HspA BOT; unfold AMALLOC_STACK in *; lia
              | right; left; clear -C16; lia
              | do 2 right; left; clear -G1 G2 EUB UBN RSPx RZR SZB ES; subst S; lia
              | do 3 right; left; clear -NEk GR3 GR4 GR5 GR6 GR7 GR8 GR9 PGE SB3; subst g grz; lia
              | do 5 right; left; clear; lia
              | do 6 right; left; clear; lia
              | do 7 right; left; clear; lia ]|]).
      apply Forall_nil. }
    rewrite EMS. unfold c6_at. cbn [ms_mem MS].
    destruct G5x as (XC5 & EC5 & ER5 & ECL5).
    split.
    - split; [exact XC5|]. split; [exact EC5|]. split; [exact ER5|].
      eapply (emb_clr_sub RESV st_pre); [reflexivity| | exact ECL5].
      apply (achunks_new_prim st_pre _ (a_next (apop c st_pre)) c n); reflexivity.
    - intros c' Hc' NC'. exact (F5x c' Hc' NC'). }
  unfold apop. rewrite HCNT, !a_next_put_cls, !a_live_put_cls.
  apply (malloc_post_gen_shift DI L ra spA gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc n (al_t L) c cnt AB UB PG room lo b1 _ _ uj m_pre m1 ms') in PM;
    [| eapply munch_weaken; [| exact MU1]; unfold sub_fp, acache_addr; cbn [outside]; intros q Hq; clear -Hq HspA; lia | exact WM1].
  cbv delta [PG g grz room] in PM, SHpre, SHsuf. subst UB. subst AB.
  eapply (amalloc_post_shiftG CI _ L RNG RNG1 ra spA gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st st_pre LB n lo m m_pre); [| exact FPLE |].
  { eapply (store_prim DI AQ ASEC AFK HL CI CI_OK L RNG1 ra spA gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m_pre st_pre LB X_pre n lo c cnt k b1
              (Z_to_bv 64 (max_count st_pre c)) (Z_to_bv 64 (size_of_class c)) uj).
    all: try exact PM.
    all: try lazymatch goal with
         | |- is_primary _ = _ => exact PRIM
         | |- ann_ov _ = None => rewrite L2; exact OVF
         | |- alayout_ok _ => exact ALO
         | |- arng _ _ _ => exact ARNGp0
         | |- AFK _ _ _ => idtac
         | |- AREP _ _ _ _ _ => exact ARp
         | |- ablocks _ _ _ _ => eapply ablocks_xbusyG; [exact BL | exact XB | exact L1]
         | |- nth_error _ _ = _ => exact NK
         | |- busy_of _ _ _ = _ => exact NB
         | |- (16 < _) -> _ => let R16 := fresh in intros R16; exact (proj2 (LH R16))
         | |- junk_at _ (_ + 2768) _ => exact CSa
         | |- junk_at _ (_ + 2792) _ => exact CSc
         | |- junk_at _ _ _ => first [exact TL | rewrite ES; exact TL]
         | |- fill_at _ (_ + 1) _ _ => exact SHpre
         | |- fill_at _ _ _ _ => first [exact SHsuf | rewrite ES; exact SHsuf]
         end.
    all: try assumption.
    all: try reflexivity.
    all: try (generalize N KR B1 LO LOA BOT STK3 POS; clear; intros; unfold AMALLOC_STACK in *; lia).
    all: try exact HFKp.
    all: match goal with |- ?G => idtac "REMS" G end. }
  exact PRES.
Qed.
End S.
End CANSEC1.
End AAllocatePG_x.
End TwinB.
