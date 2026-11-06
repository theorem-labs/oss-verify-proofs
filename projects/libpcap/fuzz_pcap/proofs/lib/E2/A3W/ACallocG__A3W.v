(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require MM_syscalls WStr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require SysStepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitR__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARealloc_iface__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARefillP.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_acache3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecSlog__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require NDestr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require ExecF ITreeA StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecFacts AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepExt2.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_apoison__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_agbb__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc3g0__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc3g.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_amalloc_arep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepStore__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepStoreG0.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_acalloc_iseg__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_acalloc_tailg.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepStoreG.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc1b__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASec__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_acallocS__A3W.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module ACallocG.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import MM_syscalls WStr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import SysStepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitR__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARealloc_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARefillP. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_acache3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecSlog__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepExt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.ARefill_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARefillP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.APrimFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_acache OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_acache2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acache3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.F_acache4.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
#[using="Type"] Lemma rng_fp_leG : forall RNG RNG' lo n, fp_le RNG RNG' -> rng RNG lo n -> rng RNG' lo n.
Proof. intros RNG RNG' lo n LE (R1 & R2 & R3). split; [exact R1|]. split; [exact R2|]. intros b j Hb Hj. apply LE. apply R3; assumption. Qed.

(* [comment removed for export] *)
End CANSEC1.
Notation CALLOC_STACK := 1584 (only parsing).
Notation calloc_W L st c sp :=
  ([(sp - CALLOC_STACK, sp);
    (al_t L + 208, al_t L + 3168);
    (AINSTANCE, AINSTANCE + 728);
    (aregion_info L c, aregion_info L c + 128);
    (aregion L c + c_mapped_user (get_cls st c), aregion L c + K_REGION);
    (shad (aregion L c + c_mapped_user (get_cls st c)), shad (aregion L c) + shlen K_REGION)]%Z) (only parsing).

Section CANSEC2. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section Calloc.
Variable H : aholes.
Hypothesis HL : ahole_laws H.

(* [comment removed for export] *)
Definition calloc_retG (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : astate) (X : aconc) (c lo : Z) (m : amem)
    (st_pre : astate) (X_pre : aconc) (RNG1 : footprint) (m_pre : amem) (cnt k : Z) (ms1 : machine_state) : Prop :=
     fp_le RNG RNG1 /\ AREP H L st_pre X_pre m_pre /\ arng L RNG1 st_pre
  /\ c_count (get_cls st_pre c) = cnt /\ 0 < cnt
  /\ nth_error (xc_cache (x_cls X_pre c)) (Z.to_nat (cnt - 1)) = Some k /\ busy_of X_pre c k = None /\ 0 <= k < ndist st_pre c
  /\ x_busy X_pre = x_busy X
  /\ a_live st_pre = a_live st /\ a_next st_pre = a_next st /\ a_qloc st_pre = a_qloc st /\ a_qloc_bytes st_pre = a_qloc_bytes st
  /\ a_qglob st_pre = a_qglob st /\ a_qglob_bytes st_pre = a_qglob_bytes st /\ a_nsec st_pre = a_nsec st /\ a_nres st_pre = a_nres st
  /\ munch (calloc_W L st c (bv_unsigned sp)) m m_pre /\ wmono asegs m m_pre /\ mem_inv asegs m_pre
  /\ exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m1 (stj' : word),
       ms1 = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (aslot_addr L c k)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (ret_pc ra) fc None m1 (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (acache_addr L c, acache_addr L c + 4); (al_t L + 2784, al_t L + 2792)]%Z m_pre m1
    /\ wmono asegs m_pre m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (bv_unsigned sp)
    /\ rw_cells asegs m1 (acache_addr L c) [C4 (Z_to_bv 64 (cnt - 1)); C4 (Z_to_bv 64 (max_count st_pre c)); C8 (Z_to_bv 64 (size_of_class c))]
    /\ rw_cells asegs m1 (al_t L + 2784) [C8 stj'].

(* [comment removed for export] *)
#[using="Type"] Lemma calloc_read_gen : forall L st X m c cnt,
  alayout_ok L -> AREP H L st X m -> 1 <= c <= 30 -> c_count (get_cls st c) = cnt -> 0 < cnt ->
  exists k chunks stj,
       nth_error (xc_cache (x_cls X c)) (Z.to_nat (cnt - 1)) = Some k /\ busy_of X c k = None /\ 0 <= k < ndist st c
    /\ rw_cells asegs m (al_t L + 208 + c * 80) [C4 (Z_to_bv 64 cnt); C4 (Z_to_bv 64 (max_count st c)); C8 (Z_to_bv 64 (size_of_class c))]
    /\ u32arr asegs m (al_t L + 208 + c * 80 + 16) chunks /\ length chunks = 16%nat
    /\ nth_error chunks (Z.to_nat (cnt - 1)) = Some (Z_to_bv 64 (acompact c k)) /\ bv_unsigned (Z_to_bv 64 (acompact c k)) < 2^32
    /\ aslot_addr L c k = al_space_beg L + c * 2^32 + 16 * bv_unsigned (Z_to_bv 64 (acompact c k))
    /\ rw_cells asegs m 0xaafb8 [C8 (Z_to_bv 64 (al_space_beg L))]
    /\ rw_cells asegs m (al_t L + 2784) [C8 stj]
    /\ cnt <= 16
    /\ iclr (al_t L) 4096 /\ (al_t L + 4096 <= ATOP /\ tlsfarb kt_t (al_t L) 4096 = true) /\ al_t L mod 4096 = 0 /\ 0 <= al_space_beg L < 2^47.   (* [comment removed for export] *)
Proof.
  intros L st X m c cnt ALO AR C16 HCNT POS.
  assert (HCK : 1 <= c < K_NUM_CLASSES) by (unfold K_NUM_CLASSES; lia).
  (nd_pre (kit_cache_pop H L st X m c cnt AR HCK HCNT POS) 11%nat; intros k chunks NK NB KR CR CH LCH NTH JK FSH; nd_post).
  pose proof AR as AR0. (nd_pre AR0 12%nat; intros WF RT INST THR CLS HQ HS HD HRO RT2 AVL RT3; nd_post).
  (nd_pre THR 6%nat; intros T0 T40 CACHES CSTATS STATS UNW; nd_post).
  pose proof WF as WF0. (nd_pre WF0 11%nat; intros SBE PAE SAL SLO SHI PERC OUTC BUSY LIVE FRESH UNIQ; nd_post).
  (nd_pre (PERC c HCK) 12%nat; intros A1 A2 A3 A4 A5 A6 A7 LENF LENC CNTB ND RANGE; nd_post).
  (pose proof (alayout_space L ALO) as ndP__; nd_pre ndP__ 4%nat; intros SP1 SP2 SP3 SP4; nd_post). (pose proof (alayout_t L ALO) as ndP__; nd_pre ndP__ 4%nat; intros TL1 TL2 TL3 TL4; nd_post).
  destruct INST as (I32 & _). unfold AINSTANCE in I32.
  destruct (junk_split m (al_t L + 2768) 16 16 CSTATS ltac:(lia) ltac:(lia)) as [_ CSb].
  destruct (junk_split m (al_t L + 2768 + 16) 8 8 CSb ltac:(lia) ltac:(lia)) as [CS8 _].
  replace (al_t L + 2768 + 16) with (al_t L + 2784) in CS8 by lia. destruct (c8_of_junk m _ CS8) as [stj STS].
  (pose proof (cls_facts c C16) as ndP__; nd_pre ndP__ 4%nat; intros SZB SZM MCB _; nd_post). set (S := size_of_class c) in *.
  assert (KS : 0 <= k * S /\ k * S + S <= c_allocated_user (get_cls st c)).
  { unfold ndist in KR. fold S in KR.
    assert (P0 : 0 <= k * S) by (apply Z.mul_nonneg_nonneg; lia).
    assert (Q1 : k + 1 <= c_allocated_user (get_cls st c) / S) by lia.
    assert (M1 : (k + 1) * S <= c_allocated_user (get_cls st c) / S * S) by (apply Z.mul_le_mono_nonneg_r; lia).
    pose proof (Z.mul_div_le (c_allocated_user (get_cls st c)) S ltac:(lia)) as M2.
    rewrite Z.mul_add_distr_r, Z.mul_1_l in M1. rewrite (Z.mul_comm S) in M2. split; [exact P0| lia]. }
  assert (ACK : bv_unsigned (Z_to_bv 64 (acompact c k)) = k * (S / 16) /\ 0 <= k * (S / 16) < 2^32 /\ 16 * (k * (S / 16)) = k * S).
  { unfold acompact. fold S.
    assert (B : 0 <= k * (S / 16) < 2^32 /\ 16 * (k * (S / 16)) = k * S).
    { unfold K_FREEARR_OFF in A2. generalize KS A1 A2 SZM SZB KR; clear; intros. Z.div_mod_to_equations. nia. }
    rewrite unsigned_lit by (clear -B; lia). split; [reflexivity| exact B]. }
  (nd_pre ACK 3%nat; intros ACK1 ACK2 ACK3; nd_post).
  exists k, chunks, stj.
  split; [exact NK|]. split; [exact NB|]. split; [exact KR|]. split; [exact CR|]. split; [exact CH|]. split; [exact LCH|]. split; [exact NTH|].
  split; [rewrite ACK1; lia|].
  split; [rewrite ACK1; unfold aslot_addr, aregion, K_REGION; fold S; rewrite ACK3; clear; lia|].
  split; [exact I32|]. split; [exact STS|].
  split; [unfold max_count in CNTB; generalize CNTB MCB HCNT; clear; destruct (a_cinit st); intros; lia|].
  clear -TL1 TL2 TL3 TL4 SP4. split; [exact TL4|]. split; [exact TL2|]. split; [exact TL3| exact SP4].
Qed.

Definition calloc_arep_gen__stmt : Prop := forall {R} (k : astate -> bool -> AM R) (Q : R -> footprint -> machine_state -> Prop)
    (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (X : aconc) (c lo size : Z),
  alayout_ok L -> arng L RNG st -> AREP H L st X m -> mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - CALLOC_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 AINSTANCE -> a1 = Z_to_bv 64 (al_t L + 208) -> a2 = Z_to_bv 64 size -> a3 = Z_to_bv 64 8 ->
  16 <= size <= 65536 -> size mod 8 = 0 -> class_id size = c ->
  rng RNG lo (bv_unsigned sp - lo) ->
  (forall st_pre X_pre RNG1 m_pre cnt kk ms1,
     calloc_retG L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st X c lo m st_pre X_pre RNG1 m_pre cnt kk ms1 ->
     implS asegs RNG1 (aembed ATOP (k (apop c st_pre) true)) (epostF Q) ms1) ->
  implS asegs RNG (aembed ATOP (cache_alloc st c k)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x38388) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable R : ltac2:(SecDietF.SzSecF.ty 'calloc_arep_gen__stmt 0).
Variable k : ltac2:(SecDietF.SzSecF.ty 'calloc_arep_gen__stmt 1).
Variable Q : ltac2:(SecDietF.SzSecF.ty 'calloc_arep_gen__stmt 2).
Variable L : ltac2:(SecDietF.SzSecF.ty 'calloc_arep_gen__stmt 3).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'calloc_arep_gen__stmt 4).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'calloc_arep_gen__stmt 5).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'calloc_arep_gen__stmt 6).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'calloc_arep_gen__stmt 7).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'calloc_arep_gen__stmt 8).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'calloc_arep_gen__stmt 9).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'calloc_arep_gen__stmt 10).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'calloc_arep_gen__stmt 11).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'calloc_arep_gen__stmt 12).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'calloc_arep_gen__stmt 13).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'calloc_arep_gen__stmt 14).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'calloc_arep_gen__stmt 15).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'calloc_arep_gen__stmt 16).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'calloc_arep_gen__stmt 17).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'calloc_arep_gen__stmt 18).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'calloc_arep_gen__stmt 19).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'calloc_arep_gen__stmt 20).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'calloc_arep_gen__stmt 21).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'calloc_arep_gen__stmt 22).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'calloc_arep_gen__stmt 23).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'calloc_arep_gen__stmt 24).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'calloc_arep_gen__stmt 25).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'calloc_arep_gen__stmt 26).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'calloc_arep_gen__stmt 27).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'calloc_arep_gen__stmt 28).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'calloc_arep_gen__stmt 29).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'calloc_arep_gen__stmt 30).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'calloc_arep_gen__stmt 31).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'calloc_arep_gen__stmt 32).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'calloc_arep_gen__stmt 33).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'calloc_arep_gen__stmt 34).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'calloc_arep_gen__stmt 35).
Variable F : ltac2:(SecDietF.SzSecF.ty 'calloc_arep_gen__stmt 36).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'calloc_arep_gen__stmt 37).
Variable m : ltac2:(SecDietF.SzSecF.ty 'calloc_arep_gen__stmt 38).
Variable st : ltac2:(SecDietF.SzSecF.ty 'calloc_arep_gen__stmt 39).
Variable X : ltac2:(SecDietF.SzSecF.ty 'calloc_arep_gen__stmt 40).
Variable c : ltac2:(SecDietF.SzSecF.ty 'calloc_arep_gen__stmt 41).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'calloc_arep_gen__stmt 42).
Variable size : ltac2:(SecDietF.SzSecF.ty 'calloc_arep_gen__stmt 43).
#[using="HL"] Lemma calloc_arep_gen__body : ltac:(let T := type of (fun (h : calloc_arep_gen__stmt) => h R k Q L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st X c lo size) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (R, (k, (Q, (L, (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (st, (X, (c, (lo, size)))))))))))))))))))))))))))))))))))))))))))) as _.
  intros ALO ARNG AR MI ST CEIL LO TP Ha0 Ha1 Ha2 Ha3 SZ M8 HC RSTK KONT.
  assert (C16 : 1 <= c <= 30) by (pose proof (class_facts size ltac:(clear -SZ; lia)) as CF; cbv zeta in CF; rewrite HC in CF; clear -CF; lia).
  assert (HCK : 1 <= c < K_NUM_CLASSES) by (unfold K_NUM_CLASSES; lia).
  pose proof AR as AR0. (nd_pre AR0 12%nat; intros WF RT INST THR CLS HQ HS HD HRO RT2 AVL RT3; nd_post).
  (nd_pre THR 6%nat; intros T0 T40 CACHES CSTATS STATS UNW; nd_post).
  pose proof WF as WF0. (nd_pre WF0 11%nat; intros SBE PAE SAL SLO SHI PERC OUTC BUSY LIVE FRESH UNIQ; nd_post).
  (nd_pre (PERC c HCK) 12%nat; intros A1 A2 A3 A4 A5 A6 A7 LENF LENC CNTB ND RANGE; nd_post).
  (pose proof (alayout_space L ALO) as ndP__; nd_pre ndP__ 4%nat; intros SP1 SP2 SP3 SP4; nd_post). (pose proof (alayout_t L ALO) as ndP__; nd_pre ndP__ 4%nat; intros TL1 TL2 TL3 TL4; nd_post).
  pose proof ARNG as ARNG0. (nd_pre ARNG 14%nat; intros RIMG RT4 RCTX RNO RSTO RRI RFK RSFK RDTLS RCLS RPA RSECS RPSH RTLS; nd_post).
  word_range sp SPR.
  assert (ACE : acache_addr L c = al_t L + 208 + c * 80) by reflexivity.
  rewrite cache_alloc_unfold.
  destruct (Z.ltb_spec 0 (c_count (get_cls st c))) as [POS|NPOS].
  - (* [comment removed for export] *)
    change (put_cls c (cls_set_count (c_count (get_cls st c) - 1) (get_cls st c)) st) with (apop c st).
    (nd_pre (calloc_read_gen L st X m c (c_count (get_cls st c)) ALO AR C16 eq_refl POS) 19%nat; intros kk chunks stj NK NB KR CR CH LCH NTH IXS HAB I32 STS CNT16 T0' T1' TAL SBR; nd_post).
    iprefix. eapply evtF_cut.
    { eapply (calloc_hit_gen RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                F fc m (al_t L) size c (c_count (get_cls st c)) (al_space_beg L) lo _ _ stj chunks (Z_to_bv 64 (acompact c kk)));
        first [exact ST | exact CEIL | exact MI | exact Ha0 | exact Ha1 | exact Ha2 | exact Ha3 | exact SZ | exact M8 | exact HC | exact I32 | exact CR | exact CH
              | exact LCH | exact NTH | exact IXS | exact STS | exact T0' | exact T1' | exact TAL | exact SBR | exact RIMG | exact RTLS | exact RSTK | exact RT4 | lia]. }
    cbv beta. intros ms1 P1. apply evtF_done. apply (KONT st X RNG m (c_count (get_cls st c)) kk).
    unfold cache_hit_post in P1.
    (nd_pre P1 16%nat; intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m1 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 6%nat; intros MU1 WM1 MI1 ST1 CR1 [stj' STS1]; nd_post).
    replace (al_t L + 2784 + 8) with (al_t L + 2792) in MU1 by lia.
    unfold calloc_retG.
    split; [apply fp_le_refl|]. split; [exact AR|]. split; [exact ARNG0|].
    split; [reflexivity|]. split; [exact POS|]. split; [exact NK|]. split; [exact NB|]. split; [exact KR|].
    split; [reflexivity|]. do 8 (split; [reflexivity|]).
    split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact MI|].
    do 14 eexists. exists m1, stj'. split; [rewrite HAB; reflexivity|].
    split; [rewrite ACE; exact MU1|]. split; [exact WM1|]. split; [exact MI1|]. split; [exact ST1|]. split; [rewrite ACE; exact CR1| exact STS1].
  - (* [comment removed for export] *)
    assert (CNT0 : c_count (get_cls st c) = 0) by lia.
    destruct (CACHES c HCK) as [tl (RH & RCH & RLEN)]. rewrite CNT0 in RH. rewrite ACE in RH.
    iprefix. eapply evtF_cut.
    { eapply (calloc_pre_gen RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                F fc m (al_t L) size c lo);
        first [exact ST | exact CEIL | exact MI | exact Ha0 | exact Ha1 | exact Ha2 | exact Ha3 | exact SZ | exact M8 | exact HC | exact RH | exact TL4 | exact TL2 | exact RIMG | exact RTLS | exact RSTK | exact RT4
              | clear -LO; lia]. }
    cbv beta. intros msp Pp. apply evtF_done. unfold calloc_pre_post in Pp.
    (nd_pre Pp 13%nat; intros t0p t1p t2p a4p a5p a6p a7p t3p t4p t5p t6p mp ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 5%nat; intros MUp WMp MIp STp FRp; nd_post).
    assert (ARp : AREP H L st X mp).
    { eapply (AREP_frame_ext H HL L st X m mp); [exact ALO | exact AR | exact MUp | exact WMp |].
      apply Forall_cons; [cbn [fst snd]; intros _; right; right; atop_facts; lia | apply Forall_nil]. }
    eapply (arefillP H HL _ k Q L RNG _ _ gp tp t0p t1p t2p _ _ _ _ _ _ a4p a5p a6p a7p _ _ _ s5 s6 s7 s8 s9 s10 s11 t3p t4p t5p t6p F fc mp st X c lo
              ALO ARNG0 ARp MIp).
    all: try lazymatch goal with
         | |- arng _ _ _ => exact ARNG0
         | |- stk _ _ _ _ => rewrite unsigned_lit by lia; replace (bv_unsigned sp + -48) with (bv_unsigned sp - 48) by lia; exact STp
         | |- ATOP <= _ => exact CEIL
         | |- _ <= bv_unsigned _ - _ => rewrite unsigned_lit by lia; lia
         | |- @eq word _ _ => first [exact TP | reflexivity | rewrite ACE; reflexivity]
         | |- 1 <= _ < _ => exact HCK
         | |- c_count _ = 0 => exact CNT0
         | |- rng _ _ _ => rewrite unsigned_lit by lia; eapply rng_sub'; [exact RSTK|]; lia
         end.
    (* [comment removed for export] *)
    intros st_r X' RNG' ms' RR. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.ARefill_iface.refill_ret in RR.
    (nd_pre RR 17%nat; intros FPLE t0r t1r t2r a1r a2r a3r a4r a5r a6r a7r t3r t4r t5r t6r mr ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 20%nat; intros MUr WMr MIr STr ARr ARNGr CIN CCNT NPOS' XB XC L1 L2 L3 L4 L5 L6 L7 L8 GC; nd_post).
    rewrite ?unsigned_lit in MUr by lia. rewrite ?unsigned_lit in STr by lia.
    replace (ret_pc (Z_to_bv 64 0x38638)) with (Z_to_bv 64 0x38638) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    remember (c_count (get_cls st_r c)) as cnt eqn:HCNT. symmetry in HCNT.
    (nd_pre (calloc_read_gen L st_r X' mr c cnt ALO ARr C16 HCNT ltac:(lia)) 19%nat; intros kk chunks stj NK NB KR CR CH LCH NTH IXS HAB I32 STS CNT16 T0' T1' TAL SBR; nd_post).
    pose proof ARNGr as ARNGr0. (nd_pre ARNGr 14%nat; intros RIMG' RT4' RCTX' RNO' RSTO' RRI' RFK' RSFK' RDTLS' RCLS' RPA' RSECS' RPSH' RTLS'; nd_post).
    assert (OBJ : aregion_info L c + 128 <= ATOP /\ aregion L c + K_REGION <= ATOP /\ shad (aregion L c) + shlen K_REGION <= 17594333495296).
    { unfold aregion_info, aregion, K_REGION, K_SPACE_SIZE, K_SPACE_EXTRA, ARI_STRIDE in *. change (2^37) with 137438953472 in *. change (2^32) with 4294967296 in *.
      rewrite shad_div, shlen_div. unfold ASHOFF. clear -SP1 SP2 C16. Z.div_mod_to_equations. lia. }
    (nd_pre OBJ 3%nat; intros OB1 OB2 OB3; nd_post).
    xport FRp MUr WMr ltac:(unfold AINSTANCE in *; clear -SPR CEIL LO TL1 TL2 OB1 OB2 OB3; lia).
    iprefix. eapply evtF_cut.
    { eapply (calloc_popj_gen RNG' sp gp tp t0r t1r t2r a1r a2r a3r a4r a5r a6r a7r s5 s6 s7 s8 s9 s10 s11 t3r t4r t5r t6r
                ra s0 s1 s2 s3 s4 (Z_to_bv 64 1) F fc mr (al_t L) c cnt (al_space_beg L) lo _ _ stj chunks (Z_to_bv 64 (acompact c kk)));
        first [ replace (bv_unsigned sp - 48) with (bv_unsigned sp + -48) by lia; exact STr
              | exact CEIL | exact MIr | exact C16 | exact FRp | exact I32 | exact CR | exact CH | exact LCH | exact NTH | exact IXS | exact STS
              | exact T0' | exact T1' | exact TAL | exact SBR | exact RIMG' | exact RTLS' | exact RT4'
              | rewrite unsigned_lit by lia; lia
              | eapply rng_fp_leG; [exact FPLE | exact RSTK]
              | lia ]. }
    cbv beta. intros ms1 P1. apply evtF_done. apply (KONT st_r X' RNG' mr cnt kk).
    unfold cache_hit_post in P1.
    (nd_pre P1 16%nat; intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m1 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 6%nat; intros MU1 WM1 MI1 ST1 CR1 [stj' STS1]; nd_post).
    replace (al_t L + 2784 + 8) with (al_t L + 2792) in MU1 by lia.
    unfold calloc_retG.
    split; [exact FPLE|]. split; [exact ARr|].
    split; [exact ARNGr0|].
    split; [exact HCNT|]. split; [lia|]. split; [exact NK|]. split; [exact NB|]. split; [exact KR|].
    split; [exact XB|]. split; [exact L1|]. split; [exact L2|]. split; [exact L3|]. split; [exact L4|]. split; [exact L5|]. split; [exact L6|]. split; [exact L7|]. split; [exact L8|].
    split.
    { eapply munch_trans; [eapply munch_weaken; [| exact MUp] | eapply munch_weaken; [| exact MUr]];
        unfold sub_fp; cbn [outside]; intros q Hq; clear -Hq; lia. }
    split; [eapply wmono_trans; [exact WMp | exact WMr]|]. split; [exact MIr|].
    do 14 eexists. exists m1, stj'. split; [rewrite HAB; reflexivity|].
    split; [rewrite ACE; exact MU1|]. split; [exact WM1|]. split; [exact MI1|]. split; [exact ST1|]. split; [rewrite ACE; exact CR1| exact STS1].
Qed.
End Zd1.
#[using="HL"] Theorem calloc_arep_gen : forall {R} (k : astate -> bool -> AM R) (Q : R -> footprint -> machine_state -> Prop)
    (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (X : aconc) (c lo size : Z),
  alayout_ok L -> arng L RNG st -> AREP H L st X m -> mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - CALLOC_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 AINSTANCE -> a1 = Z_to_bv 64 (al_t L + 208) -> a2 = Z_to_bv 64 size -> a3 = Z_to_bv 64 8 ->
  16 <= size <= 65536 -> size mod 8 = 0 -> class_id size = c ->
  rng RNG lo (bv_unsigned sp - lo) ->
  (forall st_pre X_pre RNG1 m_pre cnt kk ms1,
     calloc_retG L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st X c lo m st_pre X_pre RNG1 m_pre cnt kk ms1 ->
     implS asegs RNG1 (aembed ATOP (k (apop c st_pre) true)) (epostF Q) ms1) ->
  implS asegs RNG (aembed ATOP (cache_alloc st c k)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x38388) fc None m (seg_rom asegs)).
Proof. exact calloc_arep_gen__body. Qed.
End Calloc.
End CANSEC2.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Exec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.MM_syscalls.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.WStr.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepExt.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.ARefill_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARefillP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.APrimFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_acache.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.F_acache2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acache3.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.F_acache4.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
#[using="Type"] Lemma rng_fp_leG : forall RNG RNG' lo n, fp_le RNG RNG' -> rng RNG lo n -> rng RNG' lo n.
Proof. intros RNG RNG' lo n LE (R1 & R2 & R3). split; [exact R1|]. split; [exact R2|]. intros b j Hb Hj. apply LE. apply R3; assumption. Qed.

(* [comment removed for export] *)
End CANSEC1.
Notation CALLOC_STACK := 1584 (only parsing).
Notation calloc_W L st c sp :=
  ([(sp - CALLOC_STACK, sp);
    (al_t L + 208, al_t L + 3168);
    (AINSTANCE, AINSTANCE + 728);
    (aregion_info L c, aregion_info L c + 128);
    (aregion L c + c_mapped_user (get_cls st c), aregion L c + K_REGION);
    (shad (aregion L c + c_mapped_user (get_cls st c)), shad (aregion L c) + shlen K_REGION)]%Z) (only parsing).

Section CANSEC2. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section Calloc.
Variable H : aholes.
Hypothesis HL : ahole_laws H.

(* [comment removed for export] *)
Definition calloc_retG (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : astate) (X : aconc) (c lo : Z) (m : amem)
    (st_pre : astate) (X_pre : aconc) (RNG1 : footprint) (m_pre : amem) (cnt k : Z) (ms1 : machine_state) : Prop :=
     fp_le RNG RNG1 /\ AREP H L st_pre X_pre m_pre /\ arng L RNG1 st_pre
  /\ c_count (get_cls st_pre c) = cnt /\ 0 < cnt
  /\ nth_error (xc_cache (x_cls X_pre c)) (Z.to_nat (cnt - 1)) = Some k /\ busy_of X_pre c k = None /\ 0 <= k < ndist st_pre c
  /\ x_busy X_pre = x_busy X
  /\ a_live st_pre = a_live st /\ a_next st_pre = a_next st /\ a_qloc st_pre = a_qloc st /\ a_qloc_bytes st_pre = a_qloc_bytes st
  /\ a_qglob st_pre = a_qglob st /\ a_qglob_bytes st_pre = a_qglob_bytes st /\ a_nsec st_pre = a_nsec st /\ a_nres st_pre = a_nres st
  /\ munch (calloc_W L st c (bv_unsigned sp)) m m_pre /\ wmono asegs m m_pre /\ mem_inv asegs m_pre
  /\ exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m1 (stj' : word),
       ms1 = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (aslot_addr L c k)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (ret_pc ra) fc None m1 (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (acache_addr L c, acache_addr L c + 4); (al_t L + 2784, al_t L + 2792)]%Z m_pre m1
    /\ wmono asegs m_pre m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (bv_unsigned sp)
    /\ rw_cells asegs m1 (acache_addr L c) [C4 (Z_to_bv 64 (cnt - 1)); C4 (Z_to_bv 64 (max_count st_pre c)); C8 (Z_to_bv 64 (size_of_class c))]
    /\ rw_cells asegs m1 (al_t L + 2784) [C8 stj'].

(* [comment removed for export] *)
#[using="Type"] Lemma calloc_read_gen : forall L st X m c cnt,
  alayout_ok L -> AREP H L st X m -> 1 <= c <= 30 -> c_count (get_cls st c) = cnt -> 0 < cnt ->
  exists k chunks stj,
       nth_error (xc_cache (x_cls X c)) (Z.to_nat (cnt - 1)) = Some k /\ busy_of X c k = None /\ 0 <= k < ndist st c
    /\ rw_cells asegs m (al_t L + 208 + c * 80) [C4 (Z_to_bv 64 cnt); C4 (Z_to_bv 64 (max_count st c)); C8 (Z_to_bv 64 (size_of_class c))]
    /\ u32arr asegs m (al_t L + 208 + c * 80 + 16) chunks /\ length chunks = 16%nat
    /\ nth_error chunks (Z.to_nat (cnt - 1)) = Some (Z_to_bv 64 (acompact c k)) /\ bv_unsigned (Z_to_bv 64 (acompact c k)) < 2^32
    /\ aslot_addr L c k = al_space_beg L + c * 2^32 + 16 * bv_unsigned (Z_to_bv 64 (acompact c k))
    /\ rw_cells asegs m 0xab3b8 [C8 (Z_to_bv 64 (al_space_beg L))]
    /\ rw_cells asegs m (al_t L + 2784) [C8 stj]
    /\ cnt <= 16
    /\ iclr (al_t L) 4096 /\ (al_t L + 4096 <= ATOP /\ tlsfarb kt_t (al_t L) 4096 = true) /\ al_t L mod 4096 = 0 /\ 0 <= al_space_beg L < 2^47.   (* [comment removed for export] *)
Proof.
  intros L st X m c cnt ALO AR C16 HCNT POS.
  assert (HCK : 1 <= c < K_NUM_CLASSES) by (unfold K_NUM_CLASSES; lia).
  (nd_pre (kit_cache_pop H L st X m c cnt AR HCK HCNT POS) 11%nat; intros k chunks NK NB KR CR CH LCH NTH JK FSH; nd_post).
  pose proof AR as AR0. (nd_pre AR0 12%nat; intros WF RT INST THR CLS HQ HS HD HRO RT2 AVL RT3; nd_post).
  (nd_pre THR 6%nat; intros T0 T40 CACHES CSTATS STATS UNW; nd_post).
  pose proof WF as WF0. (nd_pre WF0 11%nat; intros SBE PAE SAL SLO SHI PERC OUTC BUSY LIVE FRESH UNIQ; nd_post).
  (nd_pre (PERC c HCK) 12%nat; intros A1 A2 A3 A4 A5 A6 A7 LENF LENC CNTB ND RANGE; nd_post).
  (pose proof (alayout_space L ALO) as ndP__; nd_pre ndP__ 4%nat; intros SP1 SP2 SP3 SP4; nd_post). (pose proof (alayout_t L ALO) as ndP__; nd_pre ndP__ 4%nat; intros TL1 TL2 TL3 TL4; nd_post).
  destruct INST as (I32 & _). unfold AINSTANCE in I32.
  destruct (junk_split m (al_t L + 2768) 16 16 CSTATS ltac:(lia) ltac:(lia)) as [_ CSb].
  destruct (junk_split m (al_t L + 2768 + 16) 8 8 CSb ltac:(lia) ltac:(lia)) as [CS8 _].
  replace (al_t L + 2768 + 16) with (al_t L + 2784) in CS8 by lia. destruct (c8_of_junk m _ CS8) as [stj STS].
  (pose proof (cls_facts c C16) as ndP__; nd_pre ndP__ 4%nat; intros SZB SZM MCB _; nd_post). set (S := size_of_class c) in *.
  assert (KS : 0 <= k * S /\ k * S + S <= c_allocated_user (get_cls st c)).
  { unfold ndist in KR. fold S in KR.
    assert (P0 : 0 <= k * S) by (apply Z.mul_nonneg_nonneg; lia).
    assert (Q1 : k + 1 <= c_allocated_user (get_cls st c) / S) by lia.
    assert (M1 : (k + 1) * S <= c_allocated_user (get_cls st c) / S * S) by (apply Z.mul_le_mono_nonneg_r; lia).
    pose proof (Z.mul_div_le (c_allocated_user (get_cls st c)) S ltac:(lia)) as M2.
    rewrite Z.mul_add_distr_r, Z.mul_1_l in M1. rewrite (Z.mul_comm S) in M2. split; [exact P0| lia]. }
  assert (ACK : bv_unsigned (Z_to_bv 64 (acompact c k)) = k * (S / 16) /\ 0 <= k * (S / 16) < 2^32 /\ 16 * (k * (S / 16)) = k * S).
  { unfold acompact. fold S.
    assert (B : 0 <= k * (S / 16) < 2^32 /\ 16 * (k * (S / 16)) = k * S).
    { unfold K_FREEARR_OFF in A2. generalize KS A1 A2 SZM SZB KR; clear; intros. Z.div_mod_to_equations. nia. }
    rewrite unsigned_lit by (clear -B; lia). split; [reflexivity| exact B]. }
  (nd_pre ACK 3%nat; intros ACK1 ACK2 ACK3; nd_post).
  exists k, chunks, stj.
  split; [exact NK|]. split; [exact NB|]. split; [exact KR|]. split; [exact CR|]. split; [exact CH|]. split; [exact LCH|]. split; [exact NTH|].
  split; [rewrite ACK1; lia|].
  split; [rewrite ACK1; unfold aslot_addr, aregion, K_REGION; fold S; rewrite ACK3; clear; lia|].
  split; [exact I32|]. split; [exact STS|].
  split; [unfold max_count in CNTB; generalize CNTB MCB HCNT; clear; destruct (a_cinit st); intros; lia|].
  clear -TL1 TL2 TL3 TL4 SP4. split; [exact TL4|]. split; [exact TL2|]. split; [exact TL3| exact SP4].
Qed.

Definition calloc_arep_gen__stmt : Prop := forall {R} (k : astate -> bool -> AM R) (Q : R -> footprint -> machine_state -> Prop)
    (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (X : aconc) (c lo size : Z),
  alayout_ok L -> arng L RNG st -> AREP H L st X m -> mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - CALLOC_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 AINSTANCE -> a1 = Z_to_bv 64 (al_t L + 208) -> a2 = Z_to_bv 64 size -> a3 = Z_to_bv 64 8 ->
  16 <= size <= 65536 -> size mod 8 = 0 -> class_id size = c ->
  rng RNG lo (bv_unsigned sp - lo) ->
  (forall st_pre X_pre RNG1 m_pre cnt kk ms1,
     calloc_retG L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st X c lo m st_pre X_pre RNG1 m_pre cnt kk ms1 ->
     implS asegs RNG1 (aembed ATOP (k (apop c st_pre) true)) (epostF Q) ms1) ->
  implS asegs RNG (aembed ATOP (cache_alloc st c k)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x383f0) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable R : ltac2:(SecDietF.SzSecF.ty 'calloc_arep_gen__stmt 0).
Variable k : ltac2:(SecDietF.SzSecF.ty 'calloc_arep_gen__stmt 1).
Variable Q : ltac2:(SecDietF.SzSecF.ty 'calloc_arep_gen__stmt 2).
Variable L : ltac2:(SecDietF.SzSecF.ty 'calloc_arep_gen__stmt 3).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'calloc_arep_gen__stmt 4).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'calloc_arep_gen__stmt 5).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'calloc_arep_gen__stmt 6).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'calloc_arep_gen__stmt 7).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'calloc_arep_gen__stmt 8).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'calloc_arep_gen__stmt 9).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'calloc_arep_gen__stmt 10).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'calloc_arep_gen__stmt 11).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'calloc_arep_gen__stmt 12).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'calloc_arep_gen__stmt 13).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'calloc_arep_gen__stmt 14).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'calloc_arep_gen__stmt 15).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'calloc_arep_gen__stmt 16).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'calloc_arep_gen__stmt 17).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'calloc_arep_gen__stmt 18).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'calloc_arep_gen__stmt 19).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'calloc_arep_gen__stmt 20).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'calloc_arep_gen__stmt 21).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'calloc_arep_gen__stmt 22).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'calloc_arep_gen__stmt 23).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'calloc_arep_gen__stmt 24).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'calloc_arep_gen__stmt 25).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'calloc_arep_gen__stmt 26).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'calloc_arep_gen__stmt 27).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'calloc_arep_gen__stmt 28).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'calloc_arep_gen__stmt 29).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'calloc_arep_gen__stmt 30).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'calloc_arep_gen__stmt 31).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'calloc_arep_gen__stmt 32).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'calloc_arep_gen__stmt 33).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'calloc_arep_gen__stmt 34).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'calloc_arep_gen__stmt 35).
Variable F : ltac2:(SecDietF.SzSecF.ty 'calloc_arep_gen__stmt 36).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'calloc_arep_gen__stmt 37).
Variable m : ltac2:(SecDietF.SzSecF.ty 'calloc_arep_gen__stmt 38).
Variable st : ltac2:(SecDietF.SzSecF.ty 'calloc_arep_gen__stmt 39).
Variable X : ltac2:(SecDietF.SzSecF.ty 'calloc_arep_gen__stmt 40).
Variable c : ltac2:(SecDietF.SzSecF.ty 'calloc_arep_gen__stmt 41).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'calloc_arep_gen__stmt 42).
Variable size : ltac2:(SecDietF.SzSecF.ty 'calloc_arep_gen__stmt 43).
#[using="HL"] Lemma calloc_arep_gen__body : ltac:(let T := type of (fun (h : calloc_arep_gen__stmt) => h R k Q L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st X c lo size) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (R, (k, (Q, (L, (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (st, (X, (c, (lo, size)))))))))))))))))))))))))))))))))))))))))))) as _.
  intros ALO ARNG AR MI ST CEIL LO TP Ha0 Ha1 Ha2 Ha3 SZ M8 HC RSTK KONT.
  assert (C16 : 1 <= c <= 30) by (pose proof (class_facts size ltac:(clear -SZ; lia)) as CF; cbv zeta in CF; rewrite HC in CF; clear -CF; lia).
  assert (HCK : 1 <= c < K_NUM_CLASSES) by (unfold K_NUM_CLASSES; lia).
  pose proof AR as AR0. (nd_pre AR0 12%nat; intros WF RT INST THR CLS HQ HS HD HRO RT2 AVL RT3; nd_post).
  (nd_pre THR 6%nat; intros T0 T40 CACHES CSTATS STATS UNW; nd_post).
  pose proof WF as WF0. (nd_pre WF0 11%nat; intros SBE PAE SAL SLO SHI PERC OUTC BUSY LIVE FRESH UNIQ; nd_post).
  (nd_pre (PERC c HCK) 12%nat; intros A1 A2 A3 A4 A5 A6 A7 LENF LENC CNTB ND RANGE; nd_post).
  (pose proof (alayout_space L ALO) as ndP__; nd_pre ndP__ 4%nat; intros SP1 SP2 SP3 SP4; nd_post). (pose proof (alayout_t L ALO) as ndP__; nd_pre ndP__ 4%nat; intros TL1 TL2 TL3 TL4; nd_post).
  pose proof ARNG as ARNG0. (nd_pre ARNG 14%nat; intros RIMG RT4 RCTX RNO RSTO RRI RFK RSFK RDTLS RCLS RPA RSECS RPSH RTLS; nd_post).
  word_range sp SPR.
  assert (ACE : acache_addr L c = al_t L + 208 + c * 80) by reflexivity.
  rewrite cache_alloc_unfold.
  destruct (Z.ltb_spec 0 (c_count (get_cls st c))) as [POS|NPOS].
  - (* [comment removed for export] *)
    change (put_cls c (cls_set_count (c_count (get_cls st c) - 1) (get_cls st c)) st) with (apop c st).
    (nd_pre (calloc_read_gen L st X m c (c_count (get_cls st c)) ALO AR C16 eq_refl POS) 19%nat; intros kk chunks stj NK NB KR CR CH LCH NTH IXS HAB I32 STS CNT16 T0' T1' TAL SBR; nd_post).
    iprefix. eapply evtF_cut.
    { eapply (calloc_hit_gen RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                F fc m (al_t L) size c (c_count (get_cls st c)) (al_space_beg L) lo _ _ stj chunks (Z_to_bv 64 (acompact c kk)));
        first [exact ST | exact CEIL | exact MI | exact Ha0 | exact Ha1 | exact Ha2 | exact Ha3 | exact SZ | exact M8 | exact HC | exact I32 | exact CR | exact CH
              | exact LCH | exact NTH | exact IXS | exact STS | exact T0' | exact T1' | exact TAL | exact SBR | exact RIMG | exact RTLS | exact RSTK | exact RT4 | lia]. }
    cbv beta. intros ms1 P1. apply evtF_done. apply (KONT st X RNG m (c_count (get_cls st c)) kk).
    unfold cache_hit_post in P1.
    (nd_pre P1 16%nat; intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m1 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 6%nat; intros MU1 WM1 MI1 ST1 CR1 [stj' STS1]; nd_post).
    replace (al_t L + 2784 + 8) with (al_t L + 2792) in MU1 by lia.
    unfold calloc_retG.
    split; [apply fp_le_refl|]. split; [exact AR|]. split; [exact ARNG0|].
    split; [reflexivity|]. split; [exact POS|]. split; [exact NK|]. split; [exact NB|]. split; [exact KR|].
    split; [reflexivity|]. do 8 (split; [reflexivity|]).
    split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact MI|].
    do 14 eexists. exists m1, stj'. split; [rewrite HAB; reflexivity|].
    split; [rewrite ACE; exact MU1|]. split; [exact WM1|]. split; [exact MI1|]. split; [exact ST1|]. split; [rewrite ACE; exact CR1| exact STS1].
  - (* [comment removed for export] *)
    assert (CNT0 : c_count (get_cls st c) = 0) by lia.
    destruct (CACHES c HCK) as [tl (RH & RCH & RLEN)]. rewrite CNT0 in RH. rewrite ACE in RH.
    iprefix. eapply evtF_cut.
    { eapply (calloc_pre_gen RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                F fc m (al_t L) size c lo);
        first [exact ST | exact CEIL | exact MI | exact Ha0 | exact Ha1 | exact Ha2 | exact Ha3 | exact SZ | exact M8 | exact HC | exact RH | exact TL4 | exact TL2 | exact RIMG | exact RTLS | exact RSTK | exact RT4
              | clear -LO; lia]. }
    cbv beta. intros msp Pp. apply evtF_done. unfold calloc_pre_post in Pp.
    (nd_pre Pp 13%nat; intros t0p t1p t2p a4p a5p a6p a7p t3p t4p t5p t6p mp ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 5%nat; intros MUp WMp MIp STp FRp; nd_post).
    assert (ARp : AREP H L st X mp).
    { eapply (AREP_frame_ext H HL L st X m mp); [exact ALO | exact AR | exact MUp | exact WMp |].
      apply Forall_cons; [cbn [fst snd]; intros _; right; right; atop_facts; lia | apply Forall_nil]. }
    eapply (arefillP H HL _ k Q L RNG _ _ gp tp t0p t1p t2p _ _ _ _ _ _ a4p a5p a6p a7p _ _ _ s5 s6 s7 s8 s9 s10 s11 t3p t4p t5p t6p F fc mp st X c lo
              ALO ARNG0 ARp MIp).
    all: try lazymatch goal with
         | |- arng _ _ _ => exact ARNG0
         | |- stk _ _ _ _ => rewrite unsigned_lit by lia; replace (bv_unsigned sp + -48) with (bv_unsigned sp - 48) by lia; exact STp
         | |- ATOP <= _ => exact CEIL
         | |- _ <= bv_unsigned _ - _ => rewrite unsigned_lit by lia; lia
         | |- @eq word _ _ => first [exact TP | reflexivity | rewrite ACE; reflexivity]
         | |- 1 <= _ < _ => exact HCK
         | |- c_count _ = 0 => exact CNT0
         | |- rng _ _ _ => rewrite unsigned_lit by lia; eapply rng_sub'; [exact RSTK|]; lia
         end.
    (* [comment removed for export] *)
    intros st_r X' RNG' ms' RR. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.ARefill_iface.TwB.refill_ret in RR.
    (nd_pre RR 17%nat; intros FPLE t0r t1r t2r a1r a2r a3r a4r a5r a6r a7r t3r t4r t5r t6r mr ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 20%nat; intros MUr WMr MIr STr ARr ARNGr CIN CCNT NPOS' XB XC L1 L2 L3 L4 L5 L6 L7 L8 GC; nd_post).
    rewrite ?unsigned_lit in MUr by lia. rewrite ?unsigned_lit in STr by lia.
    replace (ret_pc (Z_to_bv 64 0x386a0)) with (Z_to_bv 64 0x386a0) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    remember (c_count (get_cls st_r c)) as cnt eqn:HCNT. symmetry in HCNT.
    (nd_pre (calloc_read_gen L st_r X' mr c cnt ALO ARr C16 HCNT ltac:(lia)) 19%nat; intros kk chunks stj NK NB KR CR CH LCH NTH IXS HAB I32 STS CNT16 T0' T1' TAL SBR; nd_post).
    pose proof ARNGr as ARNGr0. (nd_pre ARNGr 14%nat; intros RIMG' RT4' RCTX' RNO' RSTO' RRI' RFK' RSFK' RDTLS' RCLS' RPA' RSECS' RPSH' RTLS'; nd_post).
    assert (OBJ : aregion_info L c + 128 <= ATOP /\ aregion L c + K_REGION <= ATOP /\ shad (aregion L c) + shlen K_REGION <= 17594333495296).
    { unfold aregion_info, aregion, K_REGION, K_SPACE_SIZE, K_SPACE_EXTRA, ARI_STRIDE in *. change (2^37) with 137438953472 in *. change (2^32) with 4294967296 in *.
      rewrite shad_div, shlen_div. unfold ASHOFF. clear -SP1 SP2 C16. Z.div_mod_to_equations. lia. }
    (nd_pre OBJ 3%nat; intros OB1 OB2 OB3; nd_post).
    xport FRp MUr WMr ltac:(unfold AINSTANCE in *; clear -SPR CEIL LO TL1 TL2 OB1 OB2 OB3; lia).
    iprefix. eapply evtF_cut.
    { eapply (calloc_popj_gen RNG' sp gp tp t0r t1r t2r a1r a2r a3r a4r a5r a6r a7r s5 s6 s7 s8 s9 s10 s11 t3r t4r t5r t6r
                ra s0 s1 s2 s3 s4 (Z_to_bv 64 1) F fc mr (al_t L) c cnt (al_space_beg L) lo _ _ stj chunks (Z_to_bv 64 (acompact c kk)));
        first [ replace (bv_unsigned sp - 48) with (bv_unsigned sp + -48) by lia; exact STr
              | exact CEIL | exact MIr | exact C16 | exact FRp | exact I32 | exact CR | exact CH | exact LCH | exact NTH | exact IXS | exact STS
              | exact T0' | exact T1' | exact TAL | exact SBR | exact RIMG' | exact RTLS' | exact RT4'
              | rewrite unsigned_lit by lia; lia
              | eapply rng_fp_leG; [exact FPLE | exact RSTK]
              | lia ]. }
    cbv beta. intros ms1 P1. apply evtF_done. apply (KONT st_r X' RNG' mr cnt kk).
    unfold cache_hit_post in P1.
    (nd_pre P1 16%nat; intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m1 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 6%nat; intros MU1 WM1 MI1 ST1 CR1 [stj' STS1]; nd_post).
    replace (al_t L + 2784 + 8) with (al_t L + 2792) in MU1 by lia.
    unfold calloc_retG.
    split; [exact FPLE|]. split; [exact ARr|].
    split; [exact ARNGr0|].
    split; [exact HCNT|]. split; [lia|]. split; [exact NK|]. split; [exact NB|]. split; [exact KR|].
    split; [exact XB|]. split; [exact L1|]. split; [exact L2|]. split; [exact L3|]. split; [exact L4|]. split; [exact L5|]. split; [exact L6|]. split; [exact L7|]. split; [exact L8|].
    split.
    { eapply munch_trans; [eapply munch_weaken; [| exact MUp] | eapply munch_weaken; [| exact MUr]];
        unfold sub_fp; cbn [outside]; intros q Hq; clear -Hq; lia. }
    split; [eapply wmono_trans; [exact WMp | exact WMr]|]. split; [exact MIr|].
    do 14 eexists. exists m1, stj'. split; [rewrite HAB; reflexivity|].
    split; [rewrite ACE; exact MU1|]. split; [exact WM1|]. split; [exact MI1|]. split; [exact ST1|]. split; [rewrite ACE; exact CR1| exact STS1].
Qed.
End Zd1.
#[using="HL"] Theorem calloc_arep_gen : forall {R} (k : astate -> bool -> AM R) (Q : R -> footprint -> machine_state -> Prop)
    (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (X : aconc) (c lo size : Z),
  alayout_ok L -> arng L RNG st -> AREP H L st X m -> mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - CALLOC_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 AINSTANCE -> a1 = Z_to_bv 64 (al_t L + 208) -> a2 = Z_to_bv 64 size -> a3 = Z_to_bv 64 8 ->
  16 <= size <= 65536 -> size mod 8 = 0 -> class_id size = c ->
  rng RNG lo (bv_unsigned sp - lo) ->
  (forall st_pre X_pre RNG1 m_pre cnt kk ms1,
     calloc_retG L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st X c lo m st_pre X_pre RNG1 m_pre cnt kk ms1 ->
     implS asegs RNG1 (aembed ATOP (k (apop c st_pre) true)) (epostF Q) ms1) ->
  implS asegs RNG (aembed ATOP (cache_alloc st c k)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x383f0) fc None m (seg_rom asegs)).
Proof. exact calloc_arep_gen__body. Qed.
End Calloc.
End CANSEC2.
End TwB.
End ACallocG.

(* [comment removed for export] *)
Module ALCallocPG.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA StepF SysStepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.ATlsKit.   (* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecFacts AMalloc_iface. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitR__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepExt2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_apoison__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecSlog__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_agbb__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc3g0__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc3g. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_amalloc_arep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepStore__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepStoreG0. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARealloc_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARefillP. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_acalloc_iseg__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_acalloc_tailg. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepExt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepExt2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.APrimFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.F_aalloc1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agbb__A3W.F_aalloc2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc__A3W.F_aalloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc__A3W.F_amalloc_icpt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3g0__A3W.F_amalloc_pre OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agbb__A3W.F_aalloc2g OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3g OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3g0__A3W.F_amalloc_tailg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_amalloc_arep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepStore__A3W.ARepStore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepStoreG0 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.ARefill_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARefillP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ACallocG__A3W.ACallocG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acalloc_iseg__A3W.F_acalloc_iseg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3g0__A3W.F_acalloc_pre OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acalloc_tailg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acalloc_iseg__A3W.ACalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac fu_drop_fake := repeat match goal with H : context [al_fake _] |- _ => clear H end.
Ltac fu_drop_dtls := repeat match goal with H : context [al_dtls _] |- _ => clear H end.
Ltac fu_drop_tls := repeat match goal with H : context [ATPv] |- _ => clear H | H : context [kt_img] |- _ => clear H end.
Ltac fu_focus :=
  lazymatch goal with
  | |- context [al_fake _] => fu_drop_dtls; fu_drop_tls
  | |- context [al_dtls _] => fu_drop_fake; fu_drop_tls
  | |- context [ATPv] => fu_drop_fake; fu_drop_dtls
  | |- _ => fu_drop_fake; fu_drop_dtls; fu_drop_tls
  end.
Ltac fu_lia := first [solve [fu_focus; lia] | lia].
(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
(* [comment removed for export] *)
#[using="Type"] Local Lemma ablk_int : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6303744 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
#[using="Type"] Local Lemma aobj_int : forall a n, aobj a n -> 0x10000 <= n ->
  6303744 <= a /\ a + n <= ATOP /\ exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof.
  intros a n H Hn. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. (nd_pre H 5%nat; intros H1 H2 H3 H4 H5; nd_post).
  split; [lia|]. split; [lia|]. destruct H4; [exists 0 | exists 1]; lia.
Qed.
#[using="Type"] Local Lemma aobj4_int : forall a, aobj a 4096 ->
  4096 <= a /\ a + 4096 <= ATOP
  /\ (exists k, 0 <= k <= 1 /\ a + 4096 <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a)
  /\ (exists j, 0 <= j <= 1 /\ a + 4096 <= 65536 + j * 18446744073709551616 /\ 6303744 * j <= a).
Proof.
  intros a H. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. (nd_pre H 5%nat; intros H1 H2 H3 H4 H5; nd_post).
  split; [lia|]. split; [lia|]. split; [destruct H4; [exists 0 | exists 1]; lia | destruct H5 as [_ [H5|H5]]; [exists 0 | exists 1]; lia].
Qed.
(* [comment removed for export] *)
Local Ltac dlia := repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
#[using="Type"] Lemma acalloc_eq : forall RESV st qn qs, 0 <= qn -> 0 <= qs -> qn * qs < 18446744073709551616 ->
  acalloc ATOP RESV st qn qs = amalloc ATOP RESV st (qn * qs).
Proof.
  intros RESV st qn qs H1 H2 H3. unfold acalloc, TWO64.
  replace (qn <? 0) with false by (symmetry; apply Z.ltb_ge; exact H1). replace (qs <? 0) with false by (symmetry; apply Z.ltb_ge; exact H2).
  replace (2 ^ 64 <=? qn * qs) with false by (symmetry; apply Z.leb_gt; exact H3). reflexivity.
Qed.
#[using="Type"] Lemma amalloc_prim_eq : forall RESV st n c,
  1 <= n -> is_primary n = true -> class_id (needed_size n) = c ->
  amalloc ATOP RESV st n =
    cache_alloc st c (fun st1 (ok : bool) =>
      if ok then SRet (set_next (N.succ (a_next st1)) (set_live (<[ a_next st1 := CPrim c n ]> (a_live st1)) st1), Some (a_next st1))
      else SRet (st1, None)).
Proof.
  intros RESV st n c N PRIM HC. (pose proof (prim_facts n N PRIM) as ndP__; nd_pre ndP__ 8%nat; intros NS RZR RZE RZM RLR RSR RSM NSR; nd_post).
  unfold amalloc.
  replace (2 ^ 40 <? n) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (2 ^ 40 <? needed_size n) with false by (symmetry; apply Z.ltb_ge; lia). cbn [orb].
  rewrite PRIM, HC. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma slot_carveG : forall m AB S n rz,
  junk_at m AB S -> (rz = 16 \/ 32 <= rz) -> 0 <= n -> rz + n <= S ->
  exists b0 b1 szh szl ctxj uj (j1 j2 : word),
       rw_cells asegs m (AB + rz + -16) [C1 (Z_to_bv 8 b0); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 szh); C4 (Z_to_bv 64 szl); C8 (Z_to_bv 64 ctxj)]
    /\ 0 <= b1 < 256
    /\ rw_cells asegs m (AB + rz) [CB (Z.to_nat n) uj]
    /\ (16 < rz -> rw_cells asegs m AB [C8 j1; C8 j2] /\ junk_at m (AB + 16) (rz - 32))
    /\ junk_at m (AB + rz + n) (S - rz - n).
Proof.
  intros m AB S n rz JK RZ N FIT.
  destruct (Z.eq_dec rz 16) as [->|NE].
  - destruct (junk_split m AB 16 (S - 16) ltac:(replace (16 + (S - 16)) with S by lia; exact JK) ltac:(lia) ltac:(lia)) as [HJ R1].
    destruct (junk_split m (AB + 16) n (S - 16 - n) ltac:(replace (n + (S - 16 - n)) with (S - 16) by lia; exact R1) ltac:(lia) ltac:(lia)) as [[uj UJ] TL].
    (nd_pre (hdr_of_junk m AB HJ) 8%nat; intros b0 b1 szh szl ctxj HDR B0 B1; nd_post).
    exists b0, b1, szh, szl, ctxj, uj, w0, w0.
    replace (AB + 16 + -16) with AB by lia. split; [exact HDR|]. split; [exact B1|]. split; [exact UJ|].
    split; [intros; exfalso; lia|]. exact TL.
  - assert (RZ2 : 32 <= rz) by lia.
    destruct (junk_split m AB 16 (S - 16) ltac:(replace (16 + (S - 16)) with S by lia; exact JK) ltac:(lia) ltac:(lia)) as [LHJ R1].
    destruct (junk_split m (AB + 16) (rz - 32) (S - rz + 16) ltac:(replace (rz - 32 + (S - rz + 16)) with (S - 16) by lia; exact R1) ltac:(lia) ltac:(lia)) as [MID R2].
    destruct (junk_split m (AB + 16 + (rz - 32)) 16 (S - rz) ltac:(replace (16 + (S - rz)) with (S - rz + 16) by lia; exact R2) ltac:(lia) ltac:(lia)) as [HJ R3].
    destruct (junk_split m (AB + 16 + (rz - 32) + 16) n (S - rz - n) ltac:(replace (n + (S - rz - n)) with (S - rz) by lia; exact R3) ltac:(lia) ltac:(lia)) as [[uj UJ] TL].
    (nd_pre (hdr_of_junk m _ HJ) 8%nat; intros b0 b1 szh szl ctxj HDR B0 B1; nd_post).
    (nd_pre (c8c8_of_junk m AB LHJ) 3%nat; intros j1 j2 LH; nd_post).
    exists b0, b1, szh, szl, ctxj, uj, j1, j2.
    replace (AB + 16 + (rz - 32)) with (AB + rz + -16) in HDR by lia.
    replace (AB + 16 + (rz - 32) + 16) with (AB + rz) in UJ, TL by lia.
    split; [exact HDR|]. split; [exact B1|]. split; [exact UJ|]. split; [intros _; split; [exact LH| exact MID]|]. exact TL.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma malloc_post_genU_shift : forall DI L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc n t c cnt AB UB PG pgw lo b1 maxc csz uj m0 m1 ms',
  malloc_post_genU DI L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc n t c cnt AB UB PG pgw lo b1 maxc csz uj m1 ms' ->
  munch [(bv_unsigned sp - 4096, bv_unsigned sp); (t + 208 + c * 80, t + 208 + c * 80 + 4); (t + 2784, t + 2792)]%Z m0 m1 -> wmono asegs m0 m1 ->
  malloc_post_genU DI L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc n t c cnt AB UB PG pgw lo b1 maxc csz uj m0 ms'.
Proof.
  intros until ms'. intros PM MU0 WM0. unfold malloc_post_genU in *.
  (nd_pre PM 21%nat; intros id t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' sj' stj' E MU REST; nd_post).
  exists id, t0, t1, t2, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m', sj', stj'. split; [exact E|]. split; [| split; [eapply wmono_trans; [exact WM0 | exact (proj1 REST)] | exact (proj2 REST)]].
  eapply munch_trans; [eapply munch_weaken; [| exact MU0] | exact MU]. unfold sub_fp. cbn [outside]. intros q Hq. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma amalloc_postU_shiftG : forall CI AHEAP L RNG RNG1 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st st' LB n lo m m_pre ub r RNG2 ms',
  amalloc_postU CI AHEAP L RNG1 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st' LB n lo m_pre ub r RNG2 ms' ->
  fp_le RNG RNG1 -> aheap_pres CI LB (bv_unsigned sp) m m_pre ->
  amalloc_postU CI AHEAP L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB n lo m ub r RNG2 ms'.
Proof.
  intros until ms'. intros PM LE PRES. unfold amalloc_postU in *.
  (nd_pre PM 22%nat; intros FP t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' E MI ST PR REST; nd_post).
  split; [eapply fp_le_trans; [exact LE | exact FP]|].
  exists t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m'. split; [exact E|]. split; [exact MI|]. split; [exact ST|].
  split; [eapply aheap_pres_trans; [exact PRES | exact PR] | exact REST].
Qed.

#[using="Type"] Lemma ablocks_xbusyG : forall L st st' X X' LB, ablocks L st X LB -> x_busy X' = x_busy X -> a_live st' = a_live st -> ablocks L st' X' LB.
Proof. intros. eapply ablocks_same; eassumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Pres.
Variables (sp t SB c mu ACL lo : Z).
(* [comment removed for export] *)
Notation Wp := ([(sp - 4096, sp); (t + 208, t + 3169); (AINSTANCE, AINSTANCE + 728); (SB + 137438953472 + c * 128, SB + 137438953472 + c * 128 + 128);
                 (SB + c * 4294967296 + mu, SB + c * 4294967296 + 4294967296);
                 (shad (SB + c * 4294967296 + mu), shad (SB + c * 4294967296) + 536870912)]%Z) (only parsing).
Definition pfactsG : Prop :=
     (ACL = ATOP /\ ACL <= lo /\ lo <= sp - 4096 /\ sp <= 2^47)
  /\ (4096 <= t /\ t + 4096 <= ACL /\ (t + 4096 <= 2147446784 \/ 17594333495296 <= t) /\ (t + 4096 <= 65536 \/ 6303744 <= t))   (* [comment removed for export] *)
  /\ (17594333495296 <= SB /\ SB + 137438957568 <= ACL /\ SB mod 65536 = 0 /\ 1 <= c <= 31 /\ 0 <= mu <= 3758096384 /\ mu mod 8 = 0)
  /\ (t + 4096 <= SB \/ SB + 137438957568 <= t).
Hypothesis PF : pfactsG.

#[using="rc ACL lo PF"] Lemma Q_stack : forall A k, sp <= A -> 0 <= k -> disjoint_from Wp A k.
Proof. intros. (pose proof PF as ndP__; nd_pre ndP__ 4%nat; intros F1 F2 F3 F4; nd_post). unfold AINSTANCE in *. cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF. repeat split; try exact I; Z.div_mod_to_equations; lia. Qed.
#[using="rc ACL lo PF"] Lemma Q_img : forall A k, 0x10000 <= A -> 0 <= k -> A + k <= 6303744 -> (A + k <= AINSTANCE \/ AINSTANCE + 728 <= A) -> disjoint_from Wp A k.   (* [comment removed for export] *)
Proof. intros. (pose proof PF as ndP__; nd_pre ndP__ 4%nat; intros F1 F2 F3 F4; nd_post). unfold AINSTANCE in *. cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF. repeat split; try exact I; Z.div_mod_to_equations; lia. Qed.
(* [comment removed for export] *)
#[using="rc ACL lo PF"] Lemma Q_slot : forall A k, SB <= A -> 0 <= k -> A + k <= SB + 137438953472 ->
  (A + k <= SB + c * 4294967296 + mu \/ SB + c * 4294967296 + 4294967296 <= A) -> disjoint_from Wp A k.
Proof. intros. (pose proof PF as ndP__; nd_pre ndP__ 4%nat; intros F1 F2 F3 F4; nd_post). unfold AINSTANCE in *. cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF. repeat split; try exact I; Z.div_mod_to_equations; lia. Qed.
#[using="rc lo PF"] Lemma Q_obj : forall A k, ((6303744 <= A /\ A + k <= 2147446784) \/ 17594333495296 <= A) -> 0 <= k -> A + k <= ACL ->   (* [comment removed for export] *) (A + k <= t \/ t + 4096 <= A) -> (A + k <= SB \/ SB + 137438957568 <= A) -> disjoint_from Wp A k.
Proof. intros. (pose proof PF as ndP__; nd_pre ndP__ 4%nat; intros F1 F2 F3 F4; nd_post). unfold AINSTANCE in *. cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF. repeat split; try exact I; Z.div_mod_to_equations; lia. Qed.
(* [comment removed for export] *)
#[using="rc lo PF"] Lemma Q_shad_hi : forall a, ACL <= a < 2^47 -> disjoint_from Wp (shad a) 1.
Proof. intros. (pose proof PF as ndP__; nd_pre ndP__ 4%nat; intros F1 F2 F3 F4; nd_post). unfold AINSTANCE in *. cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF. repeat split; try exact I; Z.div_mod_to_equations; lia. Qed.
#[using="rc ACL lo PF"] Lemma Q_shad_img : forall a, 0x10000 <= a < 6303744 -> disjoint_from Wp (shad a) 1.   (* [comment removed for export] *)
Proof. intros. (pose proof PF as ndP__; nd_pre ndP__ 4%nat; intros F1 F2 F3 F4; nd_post). unfold AINSTANCE in *. cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF. repeat split; try exact I; Z.div_mod_to_equations; lia. Qed.
#[using="rc lo PF"] Lemma Q_shad_obj : forall a, ((6303744 <= a /\ a + 1 <= 2147446784) \/ 17594333495296 <= a) -> a < ACL -> (a + 1 <= SB \/ SB + 137438957568 <= a) -> disjoint_from Wp (shad a) 1.   (* [comment removed for export] *)
Proof. intros. (pose proof PF as ndP__; nd_pre ndP__ 4%nat; intros F1 F2 F3 F4; nd_post). unfold AINSTANCE in *. cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF. repeat split; try exact I; Z.div_mod_to_equations; lia. Qed.
(* [comment removed for export] *)
#[using="rc lo PF"] Lemma Q_objL : forall A k, ((A + k <= 65536 \/ 6303744 <= A) /\ (A + k <= 2147446784 \/ 17594333495296 <= A)) -> 0 <= k -> A + k <= ACL ->
  (A + k <= t \/ t + 4096 <= A) -> (A + k <= SB \/ SB + 137438957568 <= A) -> disjoint_from Wp A k.
Proof. intros. (pose proof PF as ndP__; nd_pre ndP__ 4%nat; intros F1 F2 F3 F4; nd_post). unfold AINSTANCE in *. cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF. repeat split; try exact I; Z.div_mod_to_equations; lia. Qed.
#[using="rc lo PF"] Lemma Q_shad_objL : forall a, 0 <= a -> a < ACL -> (a + 1 <= SB \/ SB + 137438957568 <= a) -> disjoint_from Wp (shad a) 1.
Proof. intros. (pose proof PF as ndP__; nd_pre ndP__ 4%nat; intros F1 F2 F3 F4; nd_post). unfold AINSTANCE in *. cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF. repeat split; try exact I; Z.div_mod_to_equations; lia. Qed.
#[using="rc ACL lo PF"] Lemma Q_imsh : forall A k, 2147450880 <= A -> A + k <= 2148238848 -> 0 <= k -> disjoint_from Wp A k.      (* [comment removed for export] *)
Proof. intros. (pose proof PF as ndP__; nd_pre ndP__ 4%nat; intros F1 F2 F3 F4; nd_post). unfold AINSTANCE in *. cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF. repeat split; try exact I; Z.div_mod_to_equations; lia. Qed.
End Pres.

Section S.
Variable DI : ADepotIface.
Variables (AQ ASEC : alayout -> astate -> aconc -> amem -> Prop) (AFK : alayout -> list ablock -> amem -> Prop).
Hypothesis HL : ahole_laws (AH DI AQ ASEC AFK).
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI) CI.
(* [comment removed for export] *)
Hypothesis CI_OK2 : Forall (fun iv => snd iv <= AINSTANCE \/ AINSTANCE + 728 <= fst iv) CI.

Definition acalloc_prim__stmt : Prop := forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (qn qs n lo : Z) (tr : list Z) (RESV : list (Z * Z)),
  (* [comment removed for export] *)
  AHEAP_P (AH DI AQ ASEC AFK) L RNG st LB m ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - ACALLOC_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 qn -> a1 = Z_to_bv 64 qs -> 1 <= qn -> 1 <= qs -> n = qn * qs -> 1 <= n <= AREQMAX -> is_primary n = true ->
  aunw m L RNG lo ACALLOC_PC sp s0 ra tr ->
  bv_unsigned s0 <> bv_unsigned sp + 8 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> ACALLOC_PC ->
  bv_unsigned sp mod 16 = 0 ->
  rng RNG lo (bv_unsigned sp - lo) ->
  aresv_ok L RESV ->
  implS asegs RNG (aembed ATOP (acalloc ATOP RESV st qn qs))
        (epostF (amalloc_postU CI (AHEAP_P (AH DI AQ ASEC AFK)) L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB n lo m (repeat (Z_to_bv 8 0) (Z.to_nat n))))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ACALLOC_SYM) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'acalloc_prim__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'acalloc_prim__stmt 1).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'acalloc_prim__stmt 2).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'acalloc_prim__stmt 3).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'acalloc_prim__stmt 4).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'acalloc_prim__stmt 5).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'acalloc_prim__stmt 6).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'acalloc_prim__stmt 7).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'acalloc_prim__stmt 8).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'acalloc_prim__stmt 9).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'acalloc_prim__stmt 10).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'acalloc_prim__stmt 11).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'acalloc_prim__stmt 12).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'acalloc_prim__stmt 13).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'acalloc_prim__stmt 14).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'acalloc_prim__stmt 15).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'acalloc_prim__stmt 16).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'acalloc_prim__stmt 17).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'acalloc_prim__stmt 18).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'acalloc_prim__stmt 19).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'acalloc_prim__stmt 20).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'acalloc_prim__stmt 21).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'acalloc_prim__stmt 22).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'acalloc_prim__stmt 23).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'acalloc_prim__stmt 24).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'acalloc_prim__stmt 25).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'acalloc_prim__stmt 26).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'acalloc_prim__stmt 27).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'acalloc_prim__stmt 28).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'acalloc_prim__stmt 29).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'acalloc_prim__stmt 30).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'acalloc_prim__stmt 31).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'acalloc_prim__stmt 32).
Variable F : ltac2:(SecDietF.SzSecF.ty 'acalloc_prim__stmt 33).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'acalloc_prim__stmt 34).
Variable m : ltac2:(SecDietF.SzSecF.ty 'acalloc_prim__stmt 35).
Variable st : ltac2:(SecDietF.SzSecF.ty 'acalloc_prim__stmt 36).
Variable LB : ltac2:(SecDietF.SzSecF.ty 'acalloc_prim__stmt 37).
Variable qn : ltac2:(SecDietF.SzSecF.ty 'acalloc_prim__stmt 38).
Variable qs : ltac2:(SecDietF.SzSecF.ty 'acalloc_prim__stmt 39).
Variable n : ltac2:(SecDietF.SzSecF.ty 'acalloc_prim__stmt 40).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'acalloc_prim__stmt 41).
Variable tr : ltac2:(SecDietF.SzSecF.ty 'acalloc_prim__stmt 42).
Variable RESV : ltac2:(SecDietF.SzSecF.ty 'acalloc_prim__stmt 43).
#[using="HL CI_OK CI_OK2"] Lemma acalloc_prim__body : ltac:(let T := type of (fun (h : acalloc_prim__stmt) => h L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st LB qn qs n lo tr RESV) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (st, (LB, (qn, (qs, (n, (lo, (tr, RESV)))))))))))))))))))))))))))))))))))))))))))) as _.
 intros AHP MI ST BOT LO TP Ha0 Ha1 NM1 SZ1 EN NR PRIM AUNW S0NE RA4 RANE SP16 RSTK ROK. unfold ACALLOC_STACK in LO. change 4096 with AMALLOC_STACK in LO.
  assert (N : 1 <= n <= AREQMAX) by exact NR. assert (N1 : 1 <= n) by (clear -NR; lia).
  (* [comment removed for export] *)
  assert (EXARM : exists trc,
      ((bv_unsigned sp + 16 < al_top L /\ uchain m (al_top L) ACALLOC_PC (bv_unsigned sp) (bv_unsigned s0) 28%nat tr /\ (length tr <= 28)%nat /\ trc = bv_unsigned ra :: tr
        /\ rng RNG lo (al_top L - lo))
       \/ (al_top L <= bv_unsigned sp + 16 /\ bv_unsigned sp < 2^47 /\ trc = []))
      /\ In (ACALLOC_PC :: trc) (al_U L) /\ (length trc <= 29)%nat /\ bv_unsigned sp < 2^47).
  { (pose proof (alayout_stack L (proj1 AHP)) as ndP__; nd_pre ndP__ 3%nat; intros K1 K2 K3; nd_post).
    destruct AUNW as [(T1 & U1 & L1 & I1 & R1)|(T1 & T2 & I1)].
    - exists (bv_unsigned ra :: tr). split; [left; split; [exact T1|]; split; [exact U1|]; split; [exact L1|]; split; [reflexivity| exact R1]|].
      split; [exact I1|]. split; [cbn [length]; clear -L1; lia | clear -T1 K2; lia].
    - exists (@nil Z). split; [right; split; [exact T1|]; split; [exact T2| reflexivity]|]. split; [exact I1|]. split; [cbn [length]; clear; lia | exact T2]. }
  (nd_pre EXARM 5%nat; intros trc ARM TRU LTRC SP47; nd_post).
  (nd_pre AHP 4%nat; intros ALO ARNG [X [AR BL]] HFK; nd_post).
  remember (class_id (needed_size n)) as c eqn:HC0. symmetry in HC0.
  (pose proof (prim_facts n N1 PRIM) as ndP__; nd_pre ndP__ 8%nat; intros NS RZR RZE RZM RLR RSR RSM NSR; nd_post).
  (pose proof (prim_class_facts n c N1 PRIM HC0) as ndP__; nd_pre ndP__ 5%nat; intros C16 NSZ SM16 SMALL MCB; nd_post). clear SMALL.
  (pose proof (cls_facts c C16) as ndP__; nd_pre ndP__ 4%nat; intros SZB _ _ _; nd_post).
  assert (HCK : 1 <= c < K_NUM_CLASSES) by (unfold K_NUM_CLASSES; clear -C16; lia).
  assert (NM8 : needed_size n mod 8 = 0) by (rewrite NS; clear -RSM RZM; Z.div_mod_to_equations; lia).
  (* [comment removed for export] *)
  pose proof AR as AR0. (nd_pre AR0 12%nat; intros WF RT INST THR CLS HQ HS HD HRO RT2 AVL RT3; nd_post).
  (nd_pre THR 6%nat; intros T0 T40 CACHES CSTATS [sj [STATS LSJ]] UNW; nd_post).
  pose proof WF as WF0. (nd_pre WF0 11%nat; intros SBE PAE SAL SLO SHI PERC OUTC BUSY LIVE FRESH UNIQ; nd_post).
  (nd_pre (PERC c HCK) 12%nat; intros A1 A2 A3 A4 A5 A6 A7 LENF LENC CNTB ND RANGE; nd_post).
  (pose proof (alayout_space L ALO) as ndP__; nd_pre ndP__ 4%nat; intros SP1 SP2 SP3 SP4; nd_post).
  (pose proof (alayout_t L ALO) as ndP__; nd_pre ndP__ 4%nat; intros TL1 TL2 TL3 TL4; nd_post).
  (pose proof (alayout_ctx L ALO) as ndP__; nd_pre ndP__ 5%nat; intros CL1 CL2 CL3 CL4 CL5; nd_post).
  (pose proof (alayout_depot L ALO) as ndP__; nd_pre ndP__ 10%nat; intros DL1 DL2 DL3 DL4 DL5 DL6 DL7 DL8 DL9 DL10; nd_post).
  (pose proof (aobj4_int _ (ao_t L ALO)) as ndP__; nd_pre ndP__ 4%nat; intros _ _ (kT & TBND & TBNDa & TBNDb) (jT & TIMG & TIMGa & TIMGb); nd_post).   (* [comment removed for export] *)
  (pose proof (aobj_int _ _ (ao_ctx L ALO) ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros CTXi _ (kC & CBND & CBNDa & CBNDb); nd_post).
  (pose proof (aobj_int _ _ (ao_nodes L ALO) ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros NODi _ (kN & NBND & NBNDa & NBNDb); nd_post).
  (pose proof (aobj_int _ _ (ao_store L ALO) ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros STOi _ (kR & SBND & SBNDa & SBNDb); nd_post).
  (pose proof (aobj_int _ _ (ao_fake L ALO) ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros OFKi _ (kF & OFKs & OFKsa & OFKsb); nd_post).
  (pose proof (aobj4_int _ (ao_dtls L ALO)) as ndP__; nd_pre ndP__ 4%nat; intros _ _ (kD & DBND & DBNDa & DBNDb) (jD & DIMG & DIMGa & DIMGb); nd_post).
  (pose proof (alayout_stack L ALO) as ndP__; nd_pre ndP__ 3%nat; intros STK1 STK2 STK3; nd_post).
  pose proof (alayout_res_disj L ALO) as [SCX TSP].
  pose proof RT as RT0.
  (nd_pre RT0 28%nat; intros GPG GOT GOT80 RIC LS1 REAL IMAX4 FLG5 FLG HPP SHB CANP TI TK INI2 LAY MCS OOM3 PGC HK2 CF8 CF34 CSMT T88 TSD LS2 CT8 CT; nd_post).
  pose proof INI2 as INI. rw_split INI 1%nat INI1 INIx. clear INIx.
  pose proof OOM3 as OOM. rw_split OOM 2%nat OOMx RSS. clear OOMx.
  pose proof IMAX4 as IMAX. rw_split IMAX 3%nat IMAX3 IMAXx. clear IMAXx.
  pose proof T0 as TT0. rw_split TT0 1%nat TTctx TT.
  pose proof ARNG as ARNG0. (nd_pre ARNG 10%nat; intros RIMG RT4 RCTX RNO RSTO RRI RFK RSFK RDTLS RCLS; nd_post).
  assert (RTLS : rng_atls RNG) by ((nd_pre ARNG0 14%nat; intros _ _ _ _ _ _ _ _ _ _ _ _ _ RTLSx; nd_post); exact RTLSx).      (* [comment removed for export] *)
  assert (RCTX4 : rng RNG (al_ctx L) 4096) by (eapply rng_sub'; [exact RCTX|]; clear; lia).
  word_range sp SPR.
  box CL5. box DL7. box DL8. box DL9. box DL10. box TSP. box SCX.
  (* [comment removed for export] *)
  rewrite (acalloc_eq RESV st qn qs ltac:(clear -NM1; lia) ltac:(clear -SZ1; lia) ltac:(rewrite <- EN; clear -NR; unfold AREQMAX in NR; lia)). rewrite <- EN.
  rewrite (amalloc_prim_eq RESV st n c N1 PRIM HC0).
  (* [comment removed for export] *)
  iprefix. eapply evtF_cut.
  { eapply (calloc_pre_spec L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m qn qs n (al_t L) lo (al_top L) (al_bot L) tr trc).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => exact ST
         | |- mem_inv _ _ => exact MI
         | |- allocA_cells _ _ _ => unfold allocA_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end)
         | |- poison_cells _ => unfold poison_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end)
         | |- u64arr _ _ _ _ => exact STATS
         | |- (_ /\ _) \/ (_ /\ _) => exact ARM
         | |- _ \/ _ => unboxed CL5
         | |- @eq word _ _ => first [exact TP | exact Ha0 | exact Ha1]
         | |- @eq Z _ (_ * _) => exact EN
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
  cbv beta. intros ms4 P4. unfold calloc_pre_post in P4.
  (nd_pre P4 23%nat; intros spA t0c t1c t2c a4c a5c a6c a7c t3c t4c t5c t6c s4A s5A s6A s3i fr0 frc junk0 junk2 tb m4 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 14%nat; intros HspA MU4 WM4 MI4 ST4 FRa FR16 FRP SS TB LTB TRF FRS UW4; nd_post).
  apply evtF_done.
  assert (AR4 : AREP (AH DI AQ ASEC AFK) L st X m4).
  { eapply (AREP_frame_pre _ HL L st X m m4); [exact ALO | exact AR | exact MU4 | exact WM4 | | exact UW4].
    apply Forall_cons; [unfold apre; cbn [fst snd]; intros _; left; unfold AMALLOC_STACK in *; clear -LO BOT STK3; lia|].
    apply Forall_cons; [unfold apre; cbn [fst snd]; intros _; right; split; reflexivity| apply Forall_nil]. }
  (* [comment removed for export] *)
  eapply (@calloc_arep_gen _ _ _ HL _ _ _ L RNG _ _ gp tp t0c t1c t2c _ _ _ _ _ _ a4c a5c a6c a7c _ _ _ _ _ _ _ _ _ _ t3c t4c t5c t6c F fc m4 st X c lo (needed_size n)
            ALO ARNG0 AR4 MI4).
  all: try lazymatch goal with
       | |- arng _ _ _ => exact ARNG0
       | |- stk _ _ _ _ => rewrite unsigned_lit by (clear -SPR HspA LO BOT STK3; unfold AMALLOC_STACK in *; lia);
                           replace (bv_unsigned spA + -128) with (bv_unsigned sp - 2320) by (clear -HspA; lia); exact ST4
       | |- ATOP <= _ => clear -LO BOT STK3; unfold AMALLOC_STACK in *; lia
       | |- _ <= bv_unsigned _ - _ => rewrite unsigned_lit by (clear -SPR HspA LO BOT STK3; unfold AMALLOC_STACK in *; lia);
                                    clear -LO HspA BOT STK3; unfold AMALLOC_STACK in *; lia
       | |- @eq word _ _ => first [exact TP | reflexivity]
       | |- 16 <= _ <= 65536 => clear -NSR; lia
       | |- _ mod 8 = 0 => exact NM8
       | |- class_id _ = _ => exact HC0
       | |- rng _ _ _ => rewrite unsigned_lit by (clear -SPR HspA LO BOT STK3; unfold AMALLOC_STACK in *; lia);
                         eapply rng_sub'; [exact RSTK|]; clear -LO HspA SP47 BOT STK3; unfold AMALLOC_STACK in *; lia
       end.
  (* [comment removed for export] *)
  intros st_pre X_pre RNG1 m_pre cnt k ms1 CRET. unfold calloc_retG in CRET.
  (nd_pre CRET 37%nat; intros FPLE ARp ARNGp HCNT POS NK NB KR XB L1 L2 L3 L4 L5 L6 L7 L8 MUc WMc MIp t0d t1d t2d a1d a2d a3d a4d a5d a6d a7d t3d t4d t5d t6d m1 stj1 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 6%nat; intros MU1 WM1 MI1 ST1 CR1 STS1; nd_post).
  rewrite ?unsigned_lit in MUc by (clear -SPR HspA LO BOT STK3; unfold AMALLOC_STACK in *; lia).
  rewrite ?unsigned_lit in MU1 by (clear -SPR HspA LO BOT STK3; unfold AMALLOC_STACK in *; lia).
  rewrite ?unsigned_lit in ST1 by (clear -SPR HspA LO BOT STK3; unfold AMALLOC_STACK in *; lia).
  replace (bv_unsigned spA + -128) with (bv_unsigned sp - 2320) in ST1 by (clear -HspA; lia).
  cbn beta iota. apply implS_ret.
  replace (ret_pc (Z_to_bv 64 0x33ea8)) with (Z_to_bv 64 0x33ea8) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  (* [comment removed for export] *)
  pose proof ARp as AR0. (nd_pre AR0 12%nat; intros WF' RT' INST' THR' CLS' HQ' HS' HD' HRO' RT2' AVL' RT3'; nd_post).
  (nd_pre THR' 6%nat; intros T0' T40' CACHES' CSTATS' [sj' [STATS' LSJ']] UNW'; nd_post).
  pose proof WF' as WF0. (nd_pre WF0 11%nat; intros SBE' PAE' SAL' SLO' SHI' PERC' OUTC' BUSY' LIVE' FRESH' UNIQ'; nd_post).
  (nd_pre (PERC' c HCK) 12%nat; intros B1' B2' B3' B4' B5' B6' B7' LENF' LENC' CNTB' ND' RANGE'; nd_post).
  (nd_pre (kit_cache_pop _ L st_pre X_pre m_pre c cnt ARp HCK HCNT POS) 11%nat; intros k' chunks NK' _ _ CR CH LCH NTH JK FSH; nd_post).
  assert (EK : k' = k) by (rewrite NK in NK'; injection NK'; intros E; symmetry; exact E). subst k'.
  (* [comment removed for export] *)
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
  (nd_pre KSF 3%nat; intros KS0 KS1 KS2; nd_post).
  assert (GEO : al_space_beg L <= AB /\ AB + S <= al_space_beg L + K_SPACE_SIZE /\ AB mod 16 = 0
                /\ AB + S <= aregion L c + c_allocated_user (get_cls st_pre c) /\ aregion L c <= AB).
  { subst AB. unfold aslot_addr, aregion, K_REGION, K_SPACE_SIZE, K_FREEARR_OFF, K_ALIGN in *. fold S.
    remember (k * S) as KS eqn:HKS. clear HKS.
    change (2^37) with 137438953472. change (2^32) with 4294967296 in *.
    split; [clear -KS0 C16; lia|]. split; [clear -KS1 B1' B2' C16 NSZ; lia|]. split; [| clear -KS0 KS1 B1'; lia].
    clear -SP3 C16 KS2. Z.div_mod_to_equations; lia. }
  (nd_pre GEO 5%nat; intros G1 G2 G3 G4 G5; nd_post). unfold K_SPACE_SIZE in G2. change (2^37) with 137438953472 in G2.
  assert (EAB : AB = aslot_addr L c k) by reflexivity. clearbody AB.
  assert (ES : S = size_of_class c) by reflexivity.
  (* [comment removed for export] *)
  assert (RZC : rz_size n = 16 \/ 32 <= rz_size n) by (clear -RZR RZM; Z.div_mod_to_equations; lia).
  (nd_pre (slot_carveG m_pre AB S n (rz_size n) JK RZC ltac:(clear -N; lia) ltac:(fold S in NSZ; clear -NSZ NS RSR; lia)) 13%nat; intros b0 b1 szh szl ctxj uj j1 j2 HDR B1 UJ LH TL; nd_post).
  set (UB := AB + rz_size n) in *. assert (EUB : UB = AB + rz_size n) by reflexivity. clearbody UB.
  (* [comment removed for export] *)
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
  (nd_pre (shadow_carve m_pre (shad AB) (shlen S) grz g room FSH GR3 GR4 GR6 GR5) 5%nat; intros SHA SHpre [sjunk SHU] SHP SHsuf; nd_post).
  rewrite <- GR7 in SHU, SHP, SHsuf.
  set (PG := shad UB + g) in *.
  (* [comment removed for export] *)
  pose proof RT' as RT0.
  (nd_pre RT0 28%nat; intros GPG' GOT' GOT80' RIC' LS1' REAL' IMAX4' FLG5' FLG' HPP' SHB' CANP' TI' TK' INI2' LAY' MCS' OOM3' PGC' HK2' CF8' CF34' CSMT' T88' TSD' LS2' CT8' CT'; nd_post).
  pose proof INI2' as INI'. rw_split INI' 1%nat INI1' INIx. clear INIx.
  pose proof OOM3' as OOM'. rw_split OOM' 2%nat OOMx RSS'. clear OOMx.
  pose proof IMAX4' as IMAX'. rw_split IMAX' 3%nat IMAX3' IMAXx. clear IMAXx.
  pose proof HK2' as HK'. rw_split HK' 1%nat HK1' HKx. clear HKx.
  pose proof T0' as TT0'. rw_split TT0' 1%nat TTctx' TT'.
  destruct (junk_split m_pre (al_t L + 2768) 16 16 CSTATS' ltac:(lia) ltac:(lia)) as [CSa CSb].
  destruct (junk_split m_pre (al_t L + 2768 + 16) 8 8 CSb ltac:(lia) ltac:(lia)) as [CS8 CSc].
  replace (al_t L + 2768 + 16) with (al_t L + 2784) in CS8 by lia.
  replace (al_t L + 2768 + 16 + 8) with (al_t L + 2792) in CSc by lia.
  (nd_pre INST' 9%nat; intros I32' I48' I64' I72' I112' I680' I984' I40' I56'; nd_post).
  pose proof ARNGp as ARNGp0. (nd_pre ARNGp 14%nat; intros RIMG' RT4' RCTX' RNO' RST' RRI' RFK' RSFK' RDTLS' RCLS' RPA' RSECS' RPSH' RTLS'; nd_post).
  (nd_pre (RCLS' c HCK) 4%nat; intros RREG RSREG RFA RSFA; nd_post).
  (* [comment removed for export] *)
  (nd_pre (alayout_slot_disj L AB 65536 ALO G1 ltac:(unfold K_SPACE_SIZE, K_FREEARR_OFF, aregion, K_REGION in *; generalize G4 B1' B2' C16 SP1 SZB; clear; intros; change (2^37) with 137438953472; lia) ltac:(clear; lia)) 5%nat; intros DJT DJC DJN DJS DJF; nd_post).
  (* [comment removed for export] *)
  assert (XTAB : tclr AB 65536).
  { apply (tclr_space L AB 65536 ALO); [exact G1|]. unfold K_SPACE_SIZE, K_FREEARR_OFF, aregion, K_REGION in *. generalize G4 B1' B2' C16 SP1 SZB; clear; intros. change (2^37) with 137438953472 in *. lia. }
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
  (* [comment removed for export] *)
  set (mu0 := c_mapped_user (get_cls st c)) in *.
  assert (OBJ : aregion_info L c = al_space_beg L + 137438953472 + c * 128 /\ aregion L c = al_space_beg L + c * 4294967296
                /\ shad (al_space_beg L + c * 4294967296) + 536870912 <= 17594333495296).
  { unfold aregion_info, aregion, K_REGION, K_SPACE_SIZE, ARI_STRIDE. change (2^37) with 137438953472. change (2^32) with 4294967296.
    split; [reflexivity|]. split; [reflexivity|]. rewrite shad_div. clear -SP1 SP2 C16. unfold ASHOFF, K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^37) with 137438953472 in *.
    Z.div_mod_to_equations. lia. }
  (nd_pre OBJ 3%nat; intros RIE RBE SHHI; nd_post).
  assert (MU41 : munch [(bv_unsigned sp - 3904, bv_unsigned sp - 2320); (al_t L + 208, al_t L + 3168); (AINSTANCE, AINSTANCE + 728);
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
  xport FRP MU41 WM41 ltac:(clear -SPR LO BOT STK3 TL1 TL2 SP1 SP2 C16 SHHI TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold AMALLOC_STACK, AINSTANCE in *; lia).
  xport SS MU41 WM41 ltac:(clear -SPR LO BOT STK3 TL1 TL2 SP1 SP2 C16 SHHI TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold AMALLOC_STACK, AINSTANCE in *; lia).
  xport TB MU41 WM41 ltac:(rewrite LTB; clear -SPR LO BOT STK3 TL1 TL2 SP1 SP2 C16 SHHI TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold AMALLOC_STACK, AINSTANCE in *; lia).
  xport FRS MU41 WM41 ltac:(clear -SPR LO BOT STK3 TL1 TL2 SP1 SP2 C16 SHHI TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold AMALLOC_STACK, AINSTANCE in *; lia).
  (* [comment removed for export] *)
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
  xport I32' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK, AINSTANCE in *; lia).
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
  xport LS2' MU1 WM1 ltac:(clear -HspA SPR TL1 TL2 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport LAY' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport MCS' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport CF34' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport INI1' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport RSS' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport IMAX3' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport TI' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport TK' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport T88' MU1 WM1 ltac:(clear -HspA SPR TL1 TL2 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, ATP88, AMALLOC_STACK in *; lia).
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
  (* [comment removed for export] *)
  assert (PF : pfactsG (bv_unsigned sp) (al_t L) (al_space_beg L) c mu0 ATOP lo).
  { unfold pfactsG. pose proof (ao_t L ALO) as OT. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in OT.   (* [comment removed for export] *)
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
  (* [comment removed for export] *)
  assert (BB : forall b, In b (x_busy X) ->
      al_space_beg L <= xb_alloc L b /\ xb_alloc L b + size_of_class (xb_class b) <= al_space_beg L + 137438953472
      /\ (xb_alloc L b + size_of_class (xb_class b) <= al_space_beg L + c * 4294967296 + mu0 \/ al_space_beg L + c * 4294967296 + 4294967296 <= xb_alloc L b)).
  { intros b Hb. destruct (BUSY b Hb) as [CLB _].
    (nd_pre (PERC (xb_class b) CLB) 12%nat; intros Q1 Q2 _ _ _ _ _ _ _ _ _ QR; nd_post).
    pose proof (size_of_class_facts (xb_class b) CLB) as [QS _].
    assert (KB : 0 <= xb_slot b < ndist st (xb_class b)).
    { apply QR. apply in_app_iff. right. apply in_app_iff. right. unfold busy_slots. apply in_map_iff. exists b. split; [reflexivity|].
      apply filter_In. split; [exact Hb| apply Z.eqb_refl]. }
    (pose proof (slot_in_region L st (xb_class b) (xb_slot b) ltac:(clear -QS; lia) (proj1 Q1) KB) as ndP__; nd_pre ndP__ 3%nat; intros P5 P4 P0; nd_post).
    unfold xb_alloc. unfold K_NUM_CLASSES in CLB. unfold K_FREEARR_OFF in Q2.
    destruct (Z.eq_dec (xb_class b) c) as [EC|NC].
    - rewrite EC in P5, P4, Q1, Q2 |- *. rewrite RBE in P5, P4. change (c_mapped_user (get_cls st c)) with mu0 in Q1, Q2.
      clear -P5 P4 Q1 Q2 A1 A2 C16. unfold K_FREEARR_OFF in *. lia.
    - (pose proof (region_other_geo L c (xb_class b) ALO ltac:(clear -C16; lia) CLB NC) as ndP__; nd_pre ndP__ 4%nat; intros R1 R2 R3 _; nd_post). rewrite RBE in R2.
      clear -P5 P4 Q1 Q2 R1 R2 R3 A1. lia. }
  pose proof (ao_fake L ALO) as FKO. unfold aobj in FKO. pose proof (ao_res L ALO) as ORS. unfold aobj in ORS. pose proof (ao_space L ALO) as RSP.
  pose proof (ad_fake_res L ALO) as D_f_res. pose proof (ad_t_fake L ALO) as D_t_f. pose proof (ad_dtls_res L ALO) as D_d_res. pose proof (ad_t_dtls L ALO) as D_t_d.
  pose proof (ao_dtls L ALO) as ODT. unfold aobj in ODT. unfold adisj in D_f_res, D_t_f, D_d_res, D_t_d.
  assert (FKD : forall cls FA sz, In (mkABlock (ABFake cls) FA sz) LB -> al_fake L <= FA /\ 0 <= sz /\ FA + sz <= al_fake L + 11571200)
    by (intros cls FA sz Hin; exact (proj1 (proj2 BL) cls FA sz Hin)).
  assert (PRES : aheap_pres CI LB (bv_unsigned sp) m m_pre).
  { intros a Ha CL. split; [| intros Hw; apply WMall; exact Hw].
    apply MUall. rewrite wa_unsigned by exact Ha.
    destruct CL as [CL|TLSA].
    2:{ (* [comment removed for export] *)
        pose proof (ad_tls_t L ALO) as DLT. pose proof (ad_tls_res L ALO) as DLR. unfold adisj in DLT, DLR.
        pose proof atp_lin as TLN. pose proof atop_range as ATR0. pose proof atp_below_atop as TBA.
        destruct TLSA as [[T|(ta & Hta & ->)]|[IM|IM]].
        4:{ pose proof (ao_ahm L ALO) as OAH. pose proof (aobj_img _ _ OAH ltac:(clear; lia)) as OAHI. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in OAH, OAHI.
          rewrite <- (ao_ahm_eq L ALO) in IM. unfold AAHM_SZ in IM. pose proof (ad_ahm_t L ALO) as DA1. pose proof (ad_ahm_res L ALO) as DA2. unfold adisj in DA1, DA2.
            eapply disjoint_outside; [eapply (Q_obj _ _ _ _ _ _ _ PF a 1) | clear; lia]; clear -IM OAH OAHI DA1 DA2 RSP; lia. }
        3:{ unfold AIMSH_LO, AIMSH_LEN in IM. eapply disjoint_outside; [eapply (Q_imsh _ _ _ _ _ _ _ PF a 1) | clear; lia]; clear -IM; lia. }
        - eapply disjoint_outside; [eapply (Q_img _ _ _ _ _ _ _ PF a 1) | clear; lia]; pose proof ATPv_img as TPI; clear -T TPI; unfold AINSTANCE; lia.
        - eapply disjoint_outside; [eapply (Q_shad_objL _ _ _ _ _ _ _ PF ta) | clear; lia]; clear -Hta DLT DLR TLN ATR0 TBA RSP; lia. }
    destruct CL as [STa | [CIa | [BLK | SH]]].
    - eapply disjoint_outside; [eapply (Q_stack _ _ _ _ _ _ _ PF a 1); clear -STa; lia | clear; lia].
    - (nd_pre CIa 3%nat; intros iv Hiv R; nd_post). (pose proof (proj1 (Forall_forall _ _) CI_OK iv Hiv) as ndP__; nd_pre ndP__ 3%nat; intros Q1 Q2 Q3; nd_post).
      pose proof (proj1 (Forall_forall _ _) CI_OK2 iv Hiv) as Q4. cbn [fst snd] in *.
      eapply disjoint_outside; [eapply (Q_img _ _ _ _ _ _ _ PF a 1); unfold AIMG_HI in *; clear -R Q1 Q3 Q4; lia | clear; lia].
    - (nd_pre BLK 3%nat; intros b Hb R; nd_post). destruct b as [[p|cls] A n']; cbn [ab_addr ab_size] in R.
      + destruct (proj1 BL p A n' Hb) as [(xb & Hxb & Sb & Ub & Nb)|(mb0 & ms0 & Lp & EUA & Gs)].
        * (nd_pre (BB xb Hxb) 3%nat; intros Bb1 Bb2 Bb3; nd_post).
          pose proof (awf_fits L st X xb WF Hxb) as FIT. unfold xb_fits in FIT. rewrite Sb in FIT. unfold xb_user in Ub. subst A n'.
          eapply disjoint_outside; [eapply (Q_slot _ _ _ _ _ _ _ PF a 1) | clear; lia]; clear -R Bb1 Bb2 Bb3 FIT; lia.
        * (* [comment removed for export] *)
          cbn [sec_wf1] in Gs. (nd_pre Gs 7%nat; intros Gs1 Gs2 Gs3 Gs4 Gs5 Gs6 (Ct & Cc & Cr & Cp & Cn & Cs & Cf & Cd); nd_post).
          pose proof (sec_facts n' ltac:(clear -Gs5; lia) Gs6) as SF. subst A. unfold SEC_UOFF, K_HIGH_MEM in *.
          unfold ablk, KLS, AIMG_HI in Gs2.   (* [comment removed for export] *)
          eapply disjoint_outside; [eapply (Q_obj _ _ _ _ _ _ _ PF a 1) | clear; lia]; clear -R Gs2 Gs3 Gs4 Gs5 SF Ct Cr RSP ORS; lia.
      + (nd_pre (FKD cls A n' Hb) 3%nat; intros K1 K2 K3; nd_post). atop_facts.
        eapply disjoint_outside; [eapply (Q_obj _ _ _ _ _ _ _ PF a 1) | clear; lia];
          clear -R K1 K3 FKO D_t_f D_f_res RSP OFKi OFKs OFKsa OFKsb; lia.   (* [comment removed for export] *)
    - (nd_pre SH 3%nat; intros a' Ha' ndR1__; nd_post; revert ndR1__; intros ->).
      destruct Ha' as [STa | [CIa | FK]].
      + eapply disjoint_outside; [eapply (Q_shad_hi _ _ _ _ _ _ _ PF a'); unfold AMALLOC_STACK in *; clear -STa LO BOT STK3; lia | clear; lia].
      + (nd_pre CIa 3%nat; intros iv Hiv R; nd_post). (pose proof (proj1 (Forall_forall _ _) CI_OK iv Hiv) as ndP__; nd_pre ndP__ 3%nat; intros Q1 Q2 Q3; nd_post). cbn [fst snd] in *.
        eapply disjoint_outside; [eapply (Q_shad_img _ _ _ _ _ _ _ PF a'); unfold AIMG_HI in *; clear -R Q1 Q3; lia | clear; lia].
      + (nd_pre FK 5%nat; intros cls FA sz Hin R; nd_post). (nd_pre (FKD cls FA sz Hin) 3%nat; intros K1 K2 K3; nd_post). atop_facts.
        eapply disjoint_outside; [eapply (Q_shad_obj _ _ _ _ _ _ _ PF a') | clear; lia]; clear -R K1 K3 FKO D_f_res RSP OFKi OFKs OFKsa OFKsb; lia. }
  assert (HFKp : AFK L LB m_pre).
  { eapply (hf_frame _ HL L LB m m_pre); [exact HFK | exact MUall | exact WMall |].
    unfold fake_untouched. pose proof (ao_t L ALO) as OT. unfold aobj in OT.
    assert (SHF : 2148238848 <= shad (al_fake L) /\ shad (al_fake L) + shlen 11571200 <= 17594332446720   (* [comment removed for export] *)
                  /\ (shad (al_space_beg L + c * 4294967296) + 536870912 <= shad (al_fake L)
                      \/ shad (al_fake L) + shlen 11571200 <= shad (al_space_beg L + c * 4294967296 + mu0))
                  /\ shad (al_space_beg L + c * 4294967296) <= shad (al_space_beg L + c * 4294967296 + mu0)
                  /\ 2201439137792 <= shad (al_space_beg L + c * 4294967296)).
    { rewrite !shad_div, !shlen_div. unfold ASHOFF in *. destruct PF as (_ & _ & (F1 & F2 & F3 & F4 & F5 & F6) & _).
      clear -FKO F1 F2 F3 F4 F5 F6 D_f_res RSP OFKi OFKs OFKsa OFKsb. Z.div_mod_to_equations. dlia. }
    (nd_pre SHF 5%nat; intros SF1 SF2 SF3 SF4 SF5; nd_post).
    unfold AMALLOC_STACK, AINSTANCE in *. destruct PF as (PF1 & PF2 & PF3 & PF4).
    repeat (apply Forall_cons; [cbn [fst snd];
      clear -LO BOT STK3 SP47 STK2 OT FKO ORS RSP ODT D_f_res D_t_f D_d_res D_t_d C16 PF3 PF4 SF1 SF2 SF3 SF4 SF5 SHHI TL1 TL2 SP1 TBND TBNDa TBNDb TIMG TIMGa TIMGb OFKi OFKs OFKsa OFKsb DBND DBNDa DBNDb DIMG DIMGa DIMGb;
      repeat (split; [fu_lia|]); fu_lia |]).   (* [comment removed for export] *)
    apply Forall_nil. }
  (* [comment removed for export] *)
  eapply evtF_mono.
  { eapply (calloc_tail_gen DI L RNG1 ra sp gp tp spA t0d t1d t2d a1d a2d a3d a4d a5d a6d a7d t3d t4d t5d t6d
              s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s4A s5A s6A s3i (Z_to_bv 64 qn) (Z_to_bv 64 qs) sp F fc m1
              n (al_t L) c cnt AB UB PG room lo b0 b1 szh szl ctxj (1 + Z.of_nat (length trc)) (al_space_beg L)
              (Z_to_bv 64 (max_count st_pre c)) (Z_to_bv 64 S) stj1 j1 j2 (Z_to_bv 8 250) sj' sjunk uj fr0 frc junk0 junk2 tb trc).
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
    all: try (lazymatch goal with |- tclr _ _ => first [exact XTAB | tclr_solve ALO ltac:(fail)] end).      (* [comment removed for export] *)
    all: match goal with |- ?G => idtac "REMT" G end. }
  (* [comment removed for export] *)
  cbv beta. intros ms' PM.
  unfold apop. rewrite HCNT, !a_next_put_cls, !a_live_put_cls.
  apply (malloc_post_genU_shift DI L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc n (al_t L) c cnt AB UB PG room lo b1 _ _ (repeat (Z_to_bv 8 0) (Z.to_nat n)) m_pre m1 ms') in PM;
    [| eapply munch_weaken; [| exact MU1]; unfold sub_fp, acache_addr; cbn [outside]; intros q Hq; clear -Hq HspA; lia | exact WM1].
  cbv delta [PG g grz room] in PM, SHpre, SHsuf. subst UB. subst AB.
  eapply (amalloc_postU_shiftG CI _ L RNG RNG1 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st st_pre LB n lo m m_pre); [| exact FPLE |].
  { eapply (store_primU DI AQ ASEC AFK HL CI CI_OK L RNG1 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m_pre st_pre LB X_pre n lo c cnt k b1
              (Z_to_bv 64 (max_count st_pre c)) (Z_to_bv 64 (size_of_class c)) (repeat (Z_to_bv 8 0) (Z.to_nat n))).
    all: try exact PM.
    all: try lazymatch goal with
         | |- is_primary _ = _ => exact PRIM
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
End Zd1.
#[using="HL CI_OK CI_OK2"] Theorem acalloc_prim : ltac:(let t := eval cbv delta [acalloc_prim__stmt] in acalloc_prim__stmt in exact t).
Proof. exact acalloc_prim__body. Qed.

(* [comment removed for export] *)
#[using="HL CI_OK CI_OK2"] Theorem acalloc_all : acalloc_stmt CI (AHEAP_P (AH DI AQ ASEC AFK)).
Proof. unfold acalloc_stmt. intros. eapply acalloc_prim; eassumption. Qed.
End S.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Exec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.ATlsKit.TwB.   (* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepExt.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepExt2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.APrimFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.F_aalloc1.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agbb__A3W.F_aalloc2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc__A3W.F_aalloc.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc__A3W.F_amalloc_icpt.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3g0__A3W.F_amalloc_pre.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agbb__A3W.F_aalloc2g.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3g.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3g0__A3W.F_amalloc_tailg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_amalloc_arep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepStore__A3W.ARepStore.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepStoreG0.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.ARefill_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARefillP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ACallocG__A3W.ACallocG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acalloc_iseg__A3W.F_acalloc_iseg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3g0__A3W.F_acalloc_pre.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acalloc_tailg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acalloc_iseg__A3W.ACalloc_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac fu_drop_fake := repeat match goal with H : context [al_fake _] |- _ => clear H end.
Ltac fu_drop_dtls := repeat match goal with H : context [al_dtls _] |- _ => clear H end.
Ltac fu_drop_tls := repeat match goal with H : context [ATPv] |- _ => clear H | H : context [kt_img] |- _ => clear H end.
Ltac fu_focus :=
  lazymatch goal with
  | |- context [al_fake _] => fu_drop_dtls; fu_drop_tls
  | |- context [al_dtls _] => fu_drop_fake; fu_drop_tls
  | |- context [ATPv] => fu_drop_fake; fu_drop_dtls
  | |- _ => fu_drop_fake; fu_drop_dtls; fu_drop_tls
  end.
Ltac fu_lia := first [solve [fu_focus; lia] | lia].
(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
(* [comment removed for export] *)
#[using="Type"] Local Lemma ablk_int : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6307840 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
#[using="Type"] Local Lemma aobj_int : forall a n, aobj a n -> 0x10000 <= n ->
  6307840 <= a /\ a + n <= ATOP /\ exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof.
  intros a n H Hn. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. (nd_pre H 5%nat; intros H1 H2 H3 H4 H5; nd_post).
  split; [lia|]. split; [lia|]. destruct H4; [exists 0 | exists 1]; lia.
Qed.
#[using="Type"] Local Lemma aobj4_int : forall a, aobj a 4096 ->
  4096 <= a /\ a + 4096 <= ATOP
  /\ (exists k, 0 <= k <= 1 /\ a + 4096 <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a)
  /\ (exists j, 0 <= j <= 1 /\ a + 4096 <= 65536 + j * 18446744073709551616 /\ 6307840 * j <= a).
Proof.
  intros a H. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. (nd_pre H 5%nat; intros H1 H2 H3 H4 H5; nd_post).
  split; [lia|]. split; [lia|]. split; [destruct H4; [exists 0 | exists 1]; lia | destruct H5 as [_ [H5|H5]]; [exists 0 | exists 1]; lia].
Qed.
(* [comment removed for export] *)
Local Ltac dlia := repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
#[using="Type"] Lemma acalloc_eq : forall RESV st qn qs, 0 <= qn -> 0 <= qs -> qn * qs < 18446744073709551616 ->
  acalloc ATOP RESV st qn qs = amalloc ATOP RESV st (qn * qs).
Proof.
  intros RESV st qn qs H1 H2 H3. unfold acalloc, TWO64.
  replace (qn <? 0) with false by (symmetry; apply Z.ltb_ge; exact H1). replace (qs <? 0) with false by (symmetry; apply Z.ltb_ge; exact H2).
  replace (2 ^ 64 <=? qn * qs) with false by (symmetry; apply Z.leb_gt; exact H3). reflexivity.
Qed.
#[using="Type"] Lemma amalloc_prim_eq : forall RESV st n c,
  1 <= n -> is_primary n = true -> class_id (needed_size n) = c ->
  amalloc ATOP RESV st n =
    cache_alloc st c (fun st1 (ok : bool) =>
      if ok then SRet (set_next (N.succ (a_next st1)) (set_live (<[ a_next st1 := CPrim c n ]> (a_live st1)) st1), Some (a_next st1))
      else SRet (st1, None)).
Proof.
  intros RESV st n c N PRIM HC. (pose proof (prim_facts n N PRIM) as ndP__; nd_pre ndP__ 8%nat; intros NS RZR RZE RZM RLR RSR RSM NSR; nd_post).
  unfold amalloc.
  replace (2 ^ 40 <? n) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (2 ^ 40 <? needed_size n) with false by (symmetry; apply Z.ltb_ge; lia). cbn [orb].
  rewrite PRIM, HC. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma slot_carveG : forall m AB S n rz,
  junk_at m AB S -> (rz = 16 \/ 32 <= rz) -> 0 <= n -> rz + n <= S ->
  exists b0 b1 szh szl ctxj uj (j1 j2 : word),
       rw_cells asegs m (AB + rz + -16) [C1 (Z_to_bv 8 b0); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 szh); C4 (Z_to_bv 64 szl); C8 (Z_to_bv 64 ctxj)]
    /\ 0 <= b1 < 256
    /\ rw_cells asegs m (AB + rz) [CB (Z.to_nat n) uj]
    /\ (16 < rz -> rw_cells asegs m AB [C8 j1; C8 j2] /\ junk_at m (AB + 16) (rz - 32))
    /\ junk_at m (AB + rz + n) (S - rz - n).
Proof.
  intros m AB S n rz JK RZ N FIT.
  destruct (Z.eq_dec rz 16) as [->|NE].
  - destruct (junk_split m AB 16 (S - 16) ltac:(replace (16 + (S - 16)) with S by lia; exact JK) ltac:(lia) ltac:(lia)) as [HJ R1].
    destruct (junk_split m (AB + 16) n (S - 16 - n) ltac:(replace (n + (S - 16 - n)) with (S - 16) by lia; exact R1) ltac:(lia) ltac:(lia)) as [[uj UJ] TL].
    (nd_pre (hdr_of_junk m AB HJ) 8%nat; intros b0 b1 szh szl ctxj HDR B0 B1; nd_post).
    exists b0, b1, szh, szl, ctxj, uj, w0, w0.
    replace (AB + 16 + -16) with AB by lia. split; [exact HDR|]. split; [exact B1|]. split; [exact UJ|].
    split; [intros; exfalso; lia|]. exact TL.
  - assert (RZ2 : 32 <= rz) by lia.
    destruct (junk_split m AB 16 (S - 16) ltac:(replace (16 + (S - 16)) with S by lia; exact JK) ltac:(lia) ltac:(lia)) as [LHJ R1].
    destruct (junk_split m (AB + 16) (rz - 32) (S - rz + 16) ltac:(replace (rz - 32 + (S - rz + 16)) with (S - 16) by lia; exact R1) ltac:(lia) ltac:(lia)) as [MID R2].
    destruct (junk_split m (AB + 16 + (rz - 32)) 16 (S - rz) ltac:(replace (16 + (S - rz)) with (S - rz + 16) by lia; exact R2) ltac:(lia) ltac:(lia)) as [HJ R3].
    destruct (junk_split m (AB + 16 + (rz - 32) + 16) n (S - rz - n) ltac:(replace (n + (S - rz - n)) with (S - rz) by lia; exact R3) ltac:(lia) ltac:(lia)) as [[uj UJ] TL].
    (nd_pre (hdr_of_junk m _ HJ) 8%nat; intros b0 b1 szh szl ctxj HDR B0 B1; nd_post).
    (nd_pre (c8c8_of_junk m AB LHJ) 3%nat; intros j1 j2 LH; nd_post).
    exists b0, b1, szh, szl, ctxj, uj, j1, j2.
    replace (AB + 16 + (rz - 32)) with (AB + rz + -16) in HDR by lia.
    replace (AB + 16 + (rz - 32) + 16) with (AB + rz) in UJ, TL by lia.
    split; [exact HDR|]. split; [exact B1|]. split; [exact UJ|]. split; [intros _; split; [exact LH| exact MID]|]. exact TL.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma malloc_post_genU_shift : forall DI L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc n t c cnt AB UB PG pgw lo b1 maxc csz uj m0 m1 ms',
  malloc_post_genU DI L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc n t c cnt AB UB PG pgw lo b1 maxc csz uj m1 ms' ->
  munch [(bv_unsigned sp - 4096, bv_unsigned sp); (t + 208 + c * 80, t + 208 + c * 80 + 4); (t + 2784, t + 2792)]%Z m0 m1 -> wmono asegs m0 m1 ->
  malloc_post_genU DI L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc n t c cnt AB UB PG pgw lo b1 maxc csz uj m0 ms'.
Proof.
  intros until ms'. intros PM MU0 WM0. unfold malloc_post_genU in *.
  (nd_pre PM 21%nat; intros id t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' sj' stj' E MU REST; nd_post).
  exists id, t0, t1, t2, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m', sj', stj'. split; [exact E|]. split; [| split; [eapply wmono_trans; [exact WM0 | exact (proj1 REST)] | exact (proj2 REST)]].
  eapply munch_trans; [eapply munch_weaken; [| exact MU0] | exact MU]. unfold sub_fp. cbn [outside]. intros q Hq. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma amalloc_postU_shiftG : forall CI AHEAP L RNG RNG1 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st st' LB n lo m m_pre ub r RNG2 ms',
  amalloc_postU CI AHEAP L RNG1 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st' LB n lo m_pre ub r RNG2 ms' ->
  fp_le RNG RNG1 -> aheap_pres CI LB (bv_unsigned sp) m m_pre ->
  amalloc_postU CI AHEAP L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB n lo m ub r RNG2 ms'.
Proof.
  intros until ms'. intros PM LE PRES. unfold amalloc_postU in *.
  (nd_pre PM 22%nat; intros FP t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' E MI ST PR REST; nd_post).
  split; [eapply fp_le_trans; [exact LE | exact FP]|].
  exists t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m'. split; [exact E|]. split; [exact MI|]. split; [exact ST|].
  split; [eapply aheap_pres_trans; [exact PRES | exact PR] | exact REST].
Qed.

#[using="Type"] Lemma ablocks_xbusyG : forall L st st' X X' LB, ablocks L st X LB -> x_busy X' = x_busy X -> a_live st' = a_live st -> ablocks L st' X' LB.
Proof. intros. eapply ablocks_same; eassumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Pres.
Variables (sp t SB c mu ACL lo : Z).
(* [comment removed for export] *)
Notation Wp := ([(sp - 4096, sp); (t + 208, t + 3169); (AINSTANCE, AINSTANCE + 728); (SB + 137438953472 + c * 128, SB + 137438953472 + c * 128 + 128);
                 (SB + c * 4294967296 + mu, SB + c * 4294967296 + 4294967296);
                 (shad (SB + c * 4294967296 + mu), shad (SB + c * 4294967296) + 536870912)]%Z) (only parsing).
Definition pfactsG : Prop :=
     (ACL = ATOP /\ ACL <= lo /\ lo <= sp - 4096 /\ sp <= 2^47)
  /\ (4096 <= t /\ t + 4096 <= ACL /\ (t + 4096 <= 2147446784 \/ 17594333495296 <= t) /\ (t + 4096 <= 65536 \/ 6307840 <= t))   (* [comment removed for export] *)
  /\ (17594333495296 <= SB /\ SB + 137438957568 <= ACL /\ SB mod 65536 = 0 /\ 1 <= c <= 31 /\ 0 <= mu <= 3758096384 /\ mu mod 8 = 0)
  /\ (t + 4096 <= SB \/ SB + 137438957568 <= t).
Hypothesis PF : pfactsG.

#[using="rc ACL lo PF"] Lemma Q_stack : forall A k, sp <= A -> 0 <= k -> disjoint_from Wp A k.
Proof. intros. (pose proof PF as ndP__; nd_pre ndP__ 4%nat; intros F1 F2 F3 F4; nd_post). unfold AINSTANCE in *. cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF. repeat split; try exact I; Z.div_mod_to_equations; lia. Qed.
#[using="rc ACL lo PF"] Lemma Q_img : forall A k, 0x10000 <= A -> 0 <= k -> A + k <= 6307840 -> (A + k <= AINSTANCE \/ AINSTANCE + 728 <= A) -> disjoint_from Wp A k.   (* [comment removed for export] *)
Proof. intros. (pose proof PF as ndP__; nd_pre ndP__ 4%nat; intros F1 F2 F3 F4; nd_post). unfold AINSTANCE in *. cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF. repeat split; try exact I; Z.div_mod_to_equations; lia. Qed.
(* [comment removed for export] *)
#[using="rc ACL lo PF"] Lemma Q_slot : forall A k, SB <= A -> 0 <= k -> A + k <= SB + 137438953472 ->
  (A + k <= SB + c * 4294967296 + mu \/ SB + c * 4294967296 + 4294967296 <= A) -> disjoint_from Wp A k.
Proof. intros. (pose proof PF as ndP__; nd_pre ndP__ 4%nat; intros F1 F2 F3 F4; nd_post). unfold AINSTANCE in *. cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF. repeat split; try exact I; Z.div_mod_to_equations; lia. Qed.
#[using="rc lo PF"] Lemma Q_obj : forall A k, ((6307840 <= A /\ A + k <= 2147446784) \/ 17594333495296 <= A) -> 0 <= k -> A + k <= ACL ->   (* [comment removed for export] *) (A + k <= t \/ t + 4096 <= A) -> (A + k <= SB \/ SB + 137438957568 <= A) -> disjoint_from Wp A k.
Proof. intros. (pose proof PF as ndP__; nd_pre ndP__ 4%nat; intros F1 F2 F3 F4; nd_post). unfold AINSTANCE in *. cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF. repeat split; try exact I; Z.div_mod_to_equations; lia. Qed.
(* [comment removed for export] *)
#[using="rc lo PF"] Lemma Q_shad_hi : forall a, ACL <= a < 2^47 -> disjoint_from Wp (shad a) 1.
Proof. intros. (pose proof PF as ndP__; nd_pre ndP__ 4%nat; intros F1 F2 F3 F4; nd_post). unfold AINSTANCE in *. cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF. repeat split; try exact I; Z.div_mod_to_equations; lia. Qed.
#[using="rc ACL lo PF"] Lemma Q_shad_img : forall a, 0x10000 <= a < 6307840 -> disjoint_from Wp (shad a) 1.   (* [comment removed for export] *)
Proof. intros. (pose proof PF as ndP__; nd_pre ndP__ 4%nat; intros F1 F2 F3 F4; nd_post). unfold AINSTANCE in *. cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF. repeat split; try exact I; Z.div_mod_to_equations; lia. Qed.
#[using="rc lo PF"] Lemma Q_shad_obj : forall a, ((6307840 <= a /\ a + 1 <= 2147446784) \/ 17594333495296 <= a) -> a < ACL -> (a + 1 <= SB \/ SB + 137438957568 <= a) -> disjoint_from Wp (shad a) 1.   (* [comment removed for export] *)
Proof. intros. (pose proof PF as ndP__; nd_pre ndP__ 4%nat; intros F1 F2 F3 F4; nd_post). unfold AINSTANCE in *. cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF. repeat split; try exact I; Z.div_mod_to_equations; lia. Qed.
(* [comment removed for export] *)
#[using="rc lo PF"] Lemma Q_objL : forall A k, ((A + k <= 65536 \/ 6307840 <= A) /\ (A + k <= 2147446784 \/ 17594333495296 <= A)) -> 0 <= k -> A + k <= ACL ->
  (A + k <= t \/ t + 4096 <= A) -> (A + k <= SB \/ SB + 137438957568 <= A) -> disjoint_from Wp A k.
Proof. intros. (pose proof PF as ndP__; nd_pre ndP__ 4%nat; intros F1 F2 F3 F4; nd_post). unfold AINSTANCE in *. cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF. repeat split; try exact I; Z.div_mod_to_equations; lia. Qed.
#[using="rc lo PF"] Lemma Q_shad_objL : forall a, 0 <= a -> a < ACL -> (a + 1 <= SB \/ SB + 137438957568 <= a) -> disjoint_from Wp (shad a) 1.
Proof. intros. (pose proof PF as ndP__; nd_pre ndP__ 4%nat; intros F1 F2 F3 F4; nd_post). unfold AINSTANCE in *. cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF. repeat split; try exact I; Z.div_mod_to_equations; lia. Qed.
#[using="rc ACL lo PF"] Lemma Q_imsh : forall A k, 2147450880 <= A -> A + k <= 2148239360 -> 0 <= k -> disjoint_from Wp A k.      (* [comment removed for export] *)
Proof. intros. (pose proof PF as ndP__; nd_pre ndP__ 4%nat; intros F1 F2 F3 F4; nd_post). unfold AINSTANCE in *. cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF. repeat split; try exact I; Z.div_mod_to_equations; lia. Qed.
End Pres.

Section S.
Variable DI : ADepotIface.
Variables (AQ ASEC : alayout -> astate -> aconc -> amem -> Prop) (AFK : alayout -> list ablock -> amem -> Prop).
Hypothesis HL : ahole_laws (AH DI AQ ASEC AFK).
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI) CI.
(* [comment removed for export] *)
Hypothesis CI_OK2 : Forall (fun iv => snd iv <= AINSTANCE \/ AINSTANCE + 728 <= fst iv) CI.

Definition acalloc_prim__stmt : Prop := forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (qn qs n lo : Z) (tr : list Z) (RESV : list (Z * Z)),
  (* [comment removed for export] *)
  AHEAP_P (AH DI AQ ASEC AFK) L RNG st LB m ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - ACALLOC_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 qn -> a1 = Z_to_bv 64 qs -> 1 <= qn -> 1 <= qs -> n = qn * qs -> 1 <= n <= AREQMAX -> is_primary n = true ->
  aunw m L RNG lo ACALLOC_PC sp s0 ra tr ->
  bv_unsigned s0 <> bv_unsigned sp + 8 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> ACALLOC_PC ->
  bv_unsigned sp mod 16 = 0 ->
  rng RNG lo (bv_unsigned sp - lo) ->
  aresv_ok L RESV ->
  implS asegs RNG (aembed ATOP (acalloc ATOP RESV st qn qs))
        (epostF (amalloc_postU CI (AHEAP_P (AH DI AQ ASEC AFK)) L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB n lo m (repeat (Z_to_bv 8 0) (Z.to_nat n))))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ACALLOC_SYM) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'acalloc_prim__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'acalloc_prim__stmt 1).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'acalloc_prim__stmt 2).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'acalloc_prim__stmt 3).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'acalloc_prim__stmt 4).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'acalloc_prim__stmt 5).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'acalloc_prim__stmt 6).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'acalloc_prim__stmt 7).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'acalloc_prim__stmt 8).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'acalloc_prim__stmt 9).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'acalloc_prim__stmt 10).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'acalloc_prim__stmt 11).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'acalloc_prim__stmt 12).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'acalloc_prim__stmt 13).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'acalloc_prim__stmt 14).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'acalloc_prim__stmt 15).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'acalloc_prim__stmt 16).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'acalloc_prim__stmt 17).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'acalloc_prim__stmt 18).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'acalloc_prim__stmt 19).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'acalloc_prim__stmt 20).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'acalloc_prim__stmt 21).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'acalloc_prim__stmt 22).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'acalloc_prim__stmt 23).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'acalloc_prim__stmt 24).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'acalloc_prim__stmt 25).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'acalloc_prim__stmt 26).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'acalloc_prim__stmt 27).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'acalloc_prim__stmt 28).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'acalloc_prim__stmt 29).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'acalloc_prim__stmt 30).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'acalloc_prim__stmt 31).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'acalloc_prim__stmt 32).
Variable F : ltac2:(SecDietF.SzSecF.ty 'acalloc_prim__stmt 33).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'acalloc_prim__stmt 34).
Variable m : ltac2:(SecDietF.SzSecF.ty 'acalloc_prim__stmt 35).
Variable st : ltac2:(SecDietF.SzSecF.ty 'acalloc_prim__stmt 36).
Variable LB : ltac2:(SecDietF.SzSecF.ty 'acalloc_prim__stmt 37).
Variable qn : ltac2:(SecDietF.SzSecF.ty 'acalloc_prim__stmt 38).
Variable qs : ltac2:(SecDietF.SzSecF.ty 'acalloc_prim__stmt 39).
Variable n : ltac2:(SecDietF.SzSecF.ty 'acalloc_prim__stmt 40).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'acalloc_prim__stmt 41).
Variable tr : ltac2:(SecDietF.SzSecF.ty 'acalloc_prim__stmt 42).
Variable RESV : ltac2:(SecDietF.SzSecF.ty 'acalloc_prim__stmt 43).
#[using="HL CI_OK CI_OK2"] Lemma acalloc_prim__body : ltac:(let T := type of (fun (h : acalloc_prim__stmt) => h L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st LB qn qs n lo tr RESV) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (st, (LB, (qn, (qs, (n, (lo, (tr, RESV)))))))))))))))))))))))))))))))))))))))))))) as _.
 intros AHP MI ST BOT LO TP Ha0 Ha1 NM1 SZ1 EN NR PRIM AUNW S0NE RA4 RANE SP16 RSTK ROK. unfold ACALLOC_STACK in LO. change 4096 with AMALLOC_STACK in LO.
  assert (N : 1 <= n <= AREQMAX) by exact NR. assert (N1 : 1 <= n) by (clear -NR; lia).
  (* [comment removed for export] *)
  assert (EXARM : exists trc,
      ((bv_unsigned sp + 16 < al_top L /\ uchain m (al_top L) ACALLOC_PC (bv_unsigned sp) (bv_unsigned s0) 28%nat tr /\ (length tr <= 28)%nat /\ trc = bv_unsigned ra :: tr
        /\ rng RNG lo (al_top L - lo))
       \/ (al_top L <= bv_unsigned sp + 16 /\ bv_unsigned sp < 2^47 /\ trc = []))
      /\ In (ACALLOC_PC :: trc) (al_U L) /\ (length trc <= 29)%nat /\ bv_unsigned sp < 2^47).
  { (pose proof (alayout_stack L (proj1 AHP)) as ndP__; nd_pre ndP__ 3%nat; intros K1 K2 K3; nd_post).
    destruct AUNW as [(T1 & U1 & L1 & I1 & R1)|(T1 & T2 & I1)].
    - exists (bv_unsigned ra :: tr). split; [left; split; [exact T1|]; split; [exact U1|]; split; [exact L1|]; split; [reflexivity| exact R1]|].
      split; [exact I1|]. split; [cbn [length]; clear -L1; lia | clear -T1 K2; lia].
    - exists (@nil Z). split; [right; split; [exact T1|]; split; [exact T2| reflexivity]|]. split; [exact I1|]. split; [cbn [length]; clear; lia | exact T2]. }
  (nd_pre EXARM 5%nat; intros trc ARM TRU LTRC SP47; nd_post).
  (nd_pre AHP 4%nat; intros ALO ARNG [X [AR BL]] HFK; nd_post).
  remember (class_id (needed_size n)) as c eqn:HC0. symmetry in HC0.
  (pose proof (prim_facts n N1 PRIM) as ndP__; nd_pre ndP__ 8%nat; intros NS RZR RZE RZM RLR RSR RSM NSR; nd_post).
  (pose proof (prim_class_facts n c N1 PRIM HC0) as ndP__; nd_pre ndP__ 5%nat; intros C16 NSZ SM16 SMALL MCB; nd_post). clear SMALL.
  (pose proof (cls_facts c C16) as ndP__; nd_pre ndP__ 4%nat; intros SZB _ _ _; nd_post).
  assert (HCK : 1 <= c < K_NUM_CLASSES) by (unfold K_NUM_CLASSES; clear -C16; lia).
  assert (NM8 : needed_size n mod 8 = 0) by (rewrite NS; clear -RSM RZM; Z.div_mod_to_equations; lia).
  (* [comment removed for export] *)
  pose proof AR as AR0. (nd_pre AR0 12%nat; intros WF RT INST THR CLS HQ HS HD HRO RT2 AVL RT3; nd_post).
  (nd_pre THR 6%nat; intros T0 T40 CACHES CSTATS [sj [STATS LSJ]] UNW; nd_post).
  pose proof WF as WF0. (nd_pre WF0 11%nat; intros SBE PAE SAL SLO SHI PERC OUTC BUSY LIVE FRESH UNIQ; nd_post).
  (nd_pre (PERC c HCK) 12%nat; intros A1 A2 A3 A4 A5 A6 A7 LENF LENC CNTB ND RANGE; nd_post).
  (pose proof (alayout_space L ALO) as ndP__; nd_pre ndP__ 4%nat; intros SP1 SP2 SP3 SP4; nd_post).
  (pose proof (alayout_t L ALO) as ndP__; nd_pre ndP__ 4%nat; intros TL1 TL2 TL3 TL4; nd_post).
  (pose proof (alayout_ctx L ALO) as ndP__; nd_pre ndP__ 5%nat; intros CL1 CL2 CL3 CL4 CL5; nd_post).
  (pose proof (alayout_depot L ALO) as ndP__; nd_pre ndP__ 10%nat; intros DL1 DL2 DL3 DL4 DL5 DL6 DL7 DL8 DL9 DL10; nd_post).
  (pose proof (aobj4_int _ (ao_t L ALO)) as ndP__; nd_pre ndP__ 4%nat; intros _ _ (kT & TBND & TBNDa & TBNDb) (jT & TIMG & TIMGa & TIMGb); nd_post).   (* [comment removed for export] *)
  (pose proof (aobj_int _ _ (ao_ctx L ALO) ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros CTXi _ (kC & CBND & CBNDa & CBNDb); nd_post).
  (pose proof (aobj_int _ _ (ao_nodes L ALO) ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros NODi _ (kN & NBND & NBNDa & NBNDb); nd_post).
  (pose proof (aobj_int _ _ (ao_store L ALO) ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros STOi _ (kR & SBND & SBNDa & SBNDb); nd_post).
  (pose proof (aobj_int _ _ (ao_fake L ALO) ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros OFKi _ (kF & OFKs & OFKsa & OFKsb); nd_post).
  (pose proof (aobj4_int _ (ao_dtls L ALO)) as ndP__; nd_pre ndP__ 4%nat; intros _ _ (kD & DBND & DBNDa & DBNDb) (jD & DIMG & DIMGa & DIMGb); nd_post).
  (pose proof (alayout_stack L ALO) as ndP__; nd_pre ndP__ 3%nat; intros STK1 STK2 STK3; nd_post).
  pose proof (alayout_res_disj L ALO) as [SCX TSP].
  pose proof RT as RT0.
  (nd_pre RT0 28%nat; intros GPG GOT GOT80 RIC LS1 REAL IMAX4 FLG5 FLG HPP SHB CANP TI TK INI2 LAY MCS OOM3 PGC HK2 CF8 CF34 CSMT T88 TSD LS2 CT8 CT; nd_post).
  pose proof INI2 as INI. rw_split INI 1%nat INI1 INIx. clear INIx.
  pose proof OOM3 as OOM. rw_split OOM 2%nat OOMx RSS. clear OOMx.
  pose proof IMAX4 as IMAX. rw_split IMAX 3%nat IMAX3 IMAXx. clear IMAXx.
  pose proof T0 as TT0. rw_split TT0 1%nat TTctx TT.
  pose proof ARNG as ARNG0. (nd_pre ARNG 10%nat; intros RIMG RT4 RCTX RNO RSTO RRI RFK RSFK RDTLS RCLS; nd_post).
  assert (RTLS : rng_atls RNG) by ((nd_pre ARNG0 14%nat; intros _ _ _ _ _ _ _ _ _ _ _ _ _ RTLSx; nd_post); exact RTLSx).      (* [comment removed for export] *)
  assert (RCTX4 : rng RNG (al_ctx L) 4096) by (eapply rng_sub'; [exact RCTX|]; clear; lia).
  word_range sp SPR.
  box CL5. box DL7. box DL8. box DL9. box DL10. box TSP. box SCX.
  (* [comment removed for export] *)
  rewrite (acalloc_eq RESV st qn qs ltac:(clear -NM1; lia) ltac:(clear -SZ1; lia) ltac:(rewrite <- EN; clear -NR; unfold AREQMAX in NR; lia)). rewrite <- EN.
  rewrite (amalloc_prim_eq RESV st n c N1 PRIM HC0).
  (* [comment removed for export] *)
  iprefix. eapply evtF_cut.
  { eapply (calloc_pre_spec L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m qn qs n (al_t L) lo (al_top L) (al_bot L) tr trc).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => exact ST
         | |- mem_inv _ _ => exact MI
         | |- allocA_cells _ _ _ => unfold allocA_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end)
         | |- poison_cells _ => unfold poison_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end)
         | |- u64arr _ _ _ _ => exact STATS
         | |- (_ /\ _) \/ (_ /\ _) => exact ARM
         | |- _ \/ _ => unboxed CL5
         | |- @eq word _ _ => first [exact TP | exact Ha0 | exact Ha1]
         | |- @eq Z _ (_ * _) => exact EN
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
  cbv beta. intros ms4 P4. unfold calloc_pre_post in P4.
  (nd_pre P4 23%nat; intros spA t0c t1c t2c a4c a5c a6c a7c t3c t4c t5c t6c s4A s5A s6A s3i fr0 frc junk0 junk2 tb m4 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 14%nat; intros HspA MU4 WM4 MI4 ST4 FRa FR16 FRP SS TB LTB TRF FRS UW4; nd_post).
  apply evtF_done.
  assert (AR4 : AREP (AH DI AQ ASEC AFK) L st X m4).
  { eapply (AREP_frame_pre _ HL L st X m m4); [exact ALO | exact AR | exact MU4 | exact WM4 | | exact UW4].
    apply Forall_cons; [unfold apre; cbn [fst snd]; intros _; left; unfold AMALLOC_STACK in *; clear -LO BOT STK3; lia|].
    apply Forall_cons; [unfold apre; cbn [fst snd]; intros _; right; split; reflexivity| apply Forall_nil]. }
  (* [comment removed for export] *)
  eapply (@calloc_arep_gen _ _ _ HL _ _ _ L RNG _ _ gp tp t0c t1c t2c _ _ _ _ _ _ a4c a5c a6c a7c _ _ _ _ _ _ _ _ _ _ t3c t4c t5c t6c F fc m4 st X c lo (needed_size n)
            ALO ARNG0 AR4 MI4).
  all: try lazymatch goal with
       | |- arng _ _ _ => exact ARNG0
       | |- stk _ _ _ _ => rewrite unsigned_lit by (clear -SPR HspA LO BOT STK3; unfold AMALLOC_STACK in *; lia);
                           replace (bv_unsigned spA + -128) with (bv_unsigned sp - 2320) by (clear -HspA; lia); exact ST4
       | |- ATOP <= _ => clear -LO BOT STK3; unfold AMALLOC_STACK in *; lia
       | |- _ <= bv_unsigned _ - _ => rewrite unsigned_lit by (clear -SPR HspA LO BOT STK3; unfold AMALLOC_STACK in *; lia);
                                    clear -LO HspA BOT STK3; unfold AMALLOC_STACK in *; lia
       | |- @eq word _ _ => first [exact TP | reflexivity]
       | |- 16 <= _ <= 65536 => clear -NSR; lia
       | |- _ mod 8 = 0 => exact NM8
       | |- class_id _ = _ => exact HC0
       | |- rng _ _ _ => rewrite unsigned_lit by (clear -SPR HspA LO BOT STK3; unfold AMALLOC_STACK in *; lia);
                         eapply rng_sub'; [exact RSTK|]; clear -LO HspA SP47 BOT STK3; unfold AMALLOC_STACK in *; lia
       end.
  (* [comment removed for export] *)
  intros st_pre X_pre RNG1 m_pre cnt k ms1 CRET. unfold calloc_retG in CRET.
  (nd_pre CRET 37%nat; intros FPLE ARp ARNGp HCNT POS NK NB KR XB L1 L2 L3 L4 L5 L6 L7 L8 MUc WMc MIp t0d t1d t2d a1d a2d a3d a4d a5d a6d a7d t3d t4d t5d t6d m1 stj1 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 6%nat; intros MU1 WM1 MI1 ST1 CR1 STS1; nd_post).
  rewrite ?unsigned_lit in MUc by (clear -SPR HspA LO BOT STK3; unfold AMALLOC_STACK in *; lia).
  rewrite ?unsigned_lit in MU1 by (clear -SPR HspA LO BOT STK3; unfold AMALLOC_STACK in *; lia).
  rewrite ?unsigned_lit in ST1 by (clear -SPR HspA LO BOT STK3; unfold AMALLOC_STACK in *; lia).
  replace (bv_unsigned spA + -128) with (bv_unsigned sp - 2320) in ST1 by (clear -HspA; lia).
  cbn beta iota. apply implS_ret.
  replace (ret_pc (Z_to_bv 64 0x33f10)) with (Z_to_bv 64 0x33f10) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  (* [comment removed for export] *)
  pose proof ARp as AR0. (nd_pre AR0 12%nat; intros WF' RT' INST' THR' CLS' HQ' HS' HD' HRO' RT2' AVL' RT3'; nd_post).
  (nd_pre THR' 6%nat; intros T0' T40' CACHES' CSTATS' [sj' [STATS' LSJ']] UNW'; nd_post).
  pose proof WF' as WF0. (nd_pre WF0 11%nat; intros SBE' PAE' SAL' SLO' SHI' PERC' OUTC' BUSY' LIVE' FRESH' UNIQ'; nd_post).
  (nd_pre (PERC' c HCK) 12%nat; intros B1' B2' B3' B4' B5' B6' B7' LENF' LENC' CNTB' ND' RANGE'; nd_post).
  (nd_pre (kit_cache_pop _ L st_pre X_pre m_pre c cnt ARp HCK HCNT POS) 11%nat; intros k' chunks NK' _ _ CR CH LCH NTH JK FSH; nd_post).
  assert (EK : k' = k) by (rewrite NK in NK'; injection NK'; intros E; symmetry; exact E). subst k'.
  (* [comment removed for export] *)
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
  (nd_pre KSF 3%nat; intros KS0 KS1 KS2; nd_post).
  assert (GEO : al_space_beg L <= AB /\ AB + S <= al_space_beg L + K_SPACE_SIZE /\ AB mod 16 = 0
                /\ AB + S <= aregion L c + c_allocated_user (get_cls st_pre c) /\ aregion L c <= AB).
  { subst AB. unfold aslot_addr, aregion, K_REGION, K_SPACE_SIZE, K_FREEARR_OFF, K_ALIGN in *. fold S.
    remember (k * S) as KS eqn:HKS. clear HKS.
    change (2^37) with 137438953472. change (2^32) with 4294967296 in *.
    split; [clear -KS0 C16; lia|]. split; [clear -KS1 B1' B2' C16 NSZ; lia|]. split; [| clear -KS0 KS1 B1'; lia].
    clear -SP3 C16 KS2. Z.div_mod_to_equations; lia. }
  (nd_pre GEO 5%nat; intros G1 G2 G3 G4 G5; nd_post). unfold K_SPACE_SIZE in G2. change (2^37) with 137438953472 in G2.
  assert (EAB : AB = aslot_addr L c k) by reflexivity. clearbody AB.
  assert (ES : S = size_of_class c) by reflexivity.
  (* [comment removed for export] *)
  assert (RZC : rz_size n = 16 \/ 32 <= rz_size n) by (clear -RZR RZM; Z.div_mod_to_equations; lia).
  (nd_pre (slot_carveG m_pre AB S n (rz_size n) JK RZC ltac:(clear -N; lia) ltac:(fold S in NSZ; clear -NSZ NS RSR; lia)) 13%nat; intros b0 b1 szh szl ctxj uj j1 j2 HDR B1 UJ LH TL; nd_post).
  set (UB := AB + rz_size n) in *. assert (EUB : UB = AB + rz_size n) by reflexivity. clearbody UB.
  (* [comment removed for export] *)
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
  (nd_pre (shadow_carve m_pre (shad AB) (shlen S) grz g room FSH GR3 GR4 GR6 GR5) 5%nat; intros SHA SHpre [sjunk SHU] SHP SHsuf; nd_post).
  rewrite <- GR7 in SHU, SHP, SHsuf.
  set (PG := shad UB + g) in *.
  (* [comment removed for export] *)
  pose proof RT' as RT0.
  (nd_pre RT0 28%nat; intros GPG' GOT' GOT80' RIC' LS1' REAL' IMAX4' FLG5' FLG' HPP' SHB' CANP' TI' TK' INI2' LAY' MCS' OOM3' PGC' HK2' CF8' CF34' CSMT' T88' TSD' LS2' CT8' CT'; nd_post).
  pose proof INI2' as INI'. rw_split INI' 1%nat INI1' INIx. clear INIx.
  pose proof OOM3' as OOM'. rw_split OOM' 2%nat OOMx RSS'. clear OOMx.
  pose proof IMAX4' as IMAX'. rw_split IMAX' 3%nat IMAX3' IMAXx. clear IMAXx.
  pose proof HK2' as HK'. rw_split HK' 1%nat HK1' HKx. clear HKx.
  pose proof T0' as TT0'. rw_split TT0' 1%nat TTctx' TT'.
  destruct (junk_split m_pre (al_t L + 2768) 16 16 CSTATS' ltac:(lia) ltac:(lia)) as [CSa CSb].
  destruct (junk_split m_pre (al_t L + 2768 + 16) 8 8 CSb ltac:(lia) ltac:(lia)) as [CS8 CSc].
  replace (al_t L + 2768 + 16) with (al_t L + 2784) in CS8 by lia.
  replace (al_t L + 2768 + 16 + 8) with (al_t L + 2792) in CSc by lia.
  (nd_pre INST' 9%nat; intros I32' I48' I64' I72' I112' I680' I984' I40' I56'; nd_post).
  pose proof ARNGp as ARNGp0. (nd_pre ARNGp 14%nat; intros RIMG' RT4' RCTX' RNO' RST' RRI' RFK' RSFK' RDTLS' RCLS' RPA' RSECS' RPSH' RTLS'; nd_post).
  (nd_pre (RCLS' c HCK) 4%nat; intros RREG RSREG RFA RSFA; nd_post).
  (* [comment removed for export] *)
  (nd_pre (alayout_slot_disj L AB 65536 ALO G1 ltac:(unfold K_SPACE_SIZE, K_FREEARR_OFF, aregion, K_REGION in *; generalize G4 B1' B2' C16 SP1 SZB; clear; intros; change (2^37) with 137438953472; lia) ltac:(clear; lia)) 5%nat; intros DJT DJC DJN DJS DJF; nd_post).
  (* [comment removed for export] *)
  assert (XTAB : tclr AB 65536).
  { apply (tclr_space L AB 65536 ALO); [exact G1|]. unfold K_SPACE_SIZE, K_FREEARR_OFF, aregion, K_REGION in *. generalize G4 B1' B2' C16 SP1 SZB; clear; intros. change (2^37) with 137438953472 in *. lia. }
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
  (* [comment removed for export] *)
  set (mu0 := c_mapped_user (get_cls st c)) in *.
  assert (OBJ : aregion_info L c = al_space_beg L + 137438953472 + c * 128 /\ aregion L c = al_space_beg L + c * 4294967296
                /\ shad (al_space_beg L + c * 4294967296) + 536870912 <= 17594333495296).
  { unfold aregion_info, aregion, K_REGION, K_SPACE_SIZE, ARI_STRIDE. change (2^37) with 137438953472. change (2^32) with 4294967296.
    split; [reflexivity|]. split; [reflexivity|]. rewrite shad_div. clear -SP1 SP2 C16. unfold ASHOFF, K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^37) with 137438953472 in *.
    Z.div_mod_to_equations. lia. }
  (nd_pre OBJ 3%nat; intros RIE RBE SHHI; nd_post).
  assert (MU41 : munch [(bv_unsigned sp - 3904, bv_unsigned sp - 2320); (al_t L + 208, al_t L + 3168); (AINSTANCE, AINSTANCE + 728);
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
  xport FRP MU41 WM41 ltac:(clear -SPR LO BOT STK3 TL1 TL2 SP1 SP2 C16 SHHI TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold AMALLOC_STACK, AINSTANCE in *; lia).
  xport SS MU41 WM41 ltac:(clear -SPR LO BOT STK3 TL1 TL2 SP1 SP2 C16 SHHI TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold AMALLOC_STACK, AINSTANCE in *; lia).
  xport TB MU41 WM41 ltac:(rewrite LTB; clear -SPR LO BOT STK3 TL1 TL2 SP1 SP2 C16 SHHI TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold AMALLOC_STACK, AINSTANCE in *; lia).
  xport FRS MU41 WM41 ltac:(clear -SPR LO BOT STK3 TL1 TL2 SP1 SP2 C16 SHHI TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold AMALLOC_STACK, AINSTANCE in *; lia).
  (* [comment removed for export] *)
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
  xport I32' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK, AINSTANCE in *; lia).
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
  xport LS2' MU1 WM1 ltac:(clear -HspA SPR TL1 TL2 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport LAY' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport MCS' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport CF34' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport INI1' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport RSS' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport IMAX3' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport TI' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport TK' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport T88' MU1 WM1 ltac:(clear -HspA SPR TL1 TL2 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, ATP88, AMALLOC_STACK in *; lia).
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
  (* [comment removed for export] *)
  assert (PF : pfactsG (bv_unsigned sp) (al_t L) (al_space_beg L) c mu0 ATOP lo).
  { unfold pfactsG. pose proof (ao_t L ALO) as OT. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in OT.   (* [comment removed for export] *)
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
  (* [comment removed for export] *)
  assert (BB : forall b, In b (x_busy X) ->
      al_space_beg L <= xb_alloc L b /\ xb_alloc L b + size_of_class (xb_class b) <= al_space_beg L + 137438953472
      /\ (xb_alloc L b + size_of_class (xb_class b) <= al_space_beg L + c * 4294967296 + mu0 \/ al_space_beg L + c * 4294967296 + 4294967296 <= xb_alloc L b)).
  { intros b Hb. destruct (BUSY b Hb) as [CLB _].
    (nd_pre (PERC (xb_class b) CLB) 12%nat; intros Q1 Q2 _ _ _ _ _ _ _ _ _ QR; nd_post).
    pose proof (size_of_class_facts (xb_class b) CLB) as [QS _].
    assert (KB : 0 <= xb_slot b < ndist st (xb_class b)).
    { apply QR. apply in_app_iff. right. apply in_app_iff. right. unfold busy_slots. apply in_map_iff. exists b. split; [reflexivity|].
      apply filter_In. split; [exact Hb| apply Z.eqb_refl]. }
    (pose proof (slot_in_region L st (xb_class b) (xb_slot b) ltac:(clear -QS; lia) (proj1 Q1) KB) as ndP__; nd_pre ndP__ 3%nat; intros P5 P4 P0; nd_post).
    unfold xb_alloc. unfold K_NUM_CLASSES in CLB. unfold K_FREEARR_OFF in Q2.
    destruct (Z.eq_dec (xb_class b) c) as [EC|NC].
    - rewrite EC in P5, P4, Q1, Q2 |- *. rewrite RBE in P5, P4. change (c_mapped_user (get_cls st c)) with mu0 in Q1, Q2.
      clear -P5 P4 Q1 Q2 A1 A2 C16. unfold K_FREEARR_OFF in *. lia.
    - (pose proof (region_other_geo L c (xb_class b) ALO ltac:(clear -C16; lia) CLB NC) as ndP__; nd_pre ndP__ 4%nat; intros R1 R2 R3 _; nd_post). rewrite RBE in R2.
      clear -P5 P4 Q1 Q2 R1 R2 R3 A1. lia. }
  pose proof (ao_fake L ALO) as FKO. unfold aobj in FKO. pose proof (ao_res L ALO) as ORS. unfold aobj in ORS. pose proof (ao_space L ALO) as RSP.
  pose proof (ad_fake_res L ALO) as D_f_res. pose proof (ad_t_fake L ALO) as D_t_f. pose proof (ad_dtls_res L ALO) as D_d_res. pose proof (ad_t_dtls L ALO) as D_t_d.
  pose proof (ao_dtls L ALO) as ODT. unfold aobj in ODT. unfold adisj in D_f_res, D_t_f, D_d_res, D_t_d.
  assert (FKD : forall cls FA sz, In (mkABlock (ABFake cls) FA sz) LB -> al_fake L <= FA /\ 0 <= sz /\ FA + sz <= al_fake L + 11571200)
    by (intros cls FA sz Hin; exact (proj1 (proj2 BL) cls FA sz Hin)).
  assert (PRES : aheap_pres CI LB (bv_unsigned sp) m m_pre).
  { intros a Ha CL. split; [| intros Hw; apply WMall; exact Hw].
    apply MUall. rewrite wa_unsigned by exact Ha.
    destruct CL as [CL|TLSA].
    2:{ (* [comment removed for export] *)
        pose proof (ad_tls_t L ALO) as DLT. pose proof (ad_tls_res L ALO) as DLR. unfold adisj in DLT, DLR.
        pose proof atp_lin as TLN. pose proof atop_range as ATR0. pose proof atp_below_atop as TBA.
        destruct TLSA as [[T|(ta & Hta & ->)]|[IM|IM]].
        4:{ pose proof (ao_ahm L ALO) as OAH. pose proof (aobj_img _ _ OAH ltac:(clear; lia)) as OAHI. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in OAH, OAHI.
          rewrite <- (ao_ahm_eq L ALO) in IM. unfold AAHM_SZ in IM. pose proof (ad_ahm_t L ALO) as DA1. pose proof (ad_ahm_res L ALO) as DA2. unfold adisj in DA1, DA2.
            eapply disjoint_outside; [eapply (Q_obj _ _ _ _ _ _ _ PF a 1) | clear; lia]; clear -IM OAH OAHI DA1 DA2 RSP; lia. }
        3:{ unfold AIMSH_LO, AIMSH_LEN in IM. eapply disjoint_outside; [eapply (Q_imsh _ _ _ _ _ _ _ PF a 1) | clear; lia]; clear -IM; lia. }
        - eapply disjoint_outside; [eapply (Q_img _ _ _ _ _ _ _ PF a 1) | clear; lia]; pose proof ATPv_img as TPI; clear -T TPI; unfold AINSTANCE; lia.
        - eapply disjoint_outside; [eapply (Q_shad_objL _ _ _ _ _ _ _ PF ta) | clear; lia]; clear -Hta DLT DLR TLN ATR0 TBA RSP; lia. }
    destruct CL as [STa | [CIa | [BLK | SH]]].
    - eapply disjoint_outside; [eapply (Q_stack _ _ _ _ _ _ _ PF a 1); clear -STa; lia | clear; lia].
    - (nd_pre CIa 3%nat; intros iv Hiv R; nd_post). (pose proof (proj1 (Forall_forall _ _) CI_OK iv Hiv) as ndP__; nd_pre ndP__ 3%nat; intros Q1 Q2 Q3; nd_post).
      pose proof (proj1 (Forall_forall _ _) CI_OK2 iv Hiv) as Q4. cbn [fst snd] in *.
      eapply disjoint_outside; [eapply (Q_img _ _ _ _ _ _ _ PF a 1); unfold AIMG_HI in *; clear -R Q1 Q3 Q4; lia | clear; lia].
    - (nd_pre BLK 3%nat; intros b Hb R; nd_post). destruct b as [[p|cls] A n']; cbn [ab_addr ab_size] in R.
      + destruct (proj1 BL p A n' Hb) as [(xb & Hxb & Sb & Ub & Nb)|(mb0 & ms0 & Lp & EUA & Gs)].
        * (nd_pre (BB xb Hxb) 3%nat; intros Bb1 Bb2 Bb3; nd_post).
          pose proof (awf_fits L st X xb WF Hxb) as FIT. unfold xb_fits in FIT. rewrite Sb in FIT. unfold xb_user in Ub. subst A n'.
          eapply disjoint_outside; [eapply (Q_slot _ _ _ _ _ _ _ PF a 1) | clear; lia]; clear -R Bb1 Bb2 Bb3 FIT; lia.
        * (* [comment removed for export] *)
          cbn [sec_wf1] in Gs. (nd_pre Gs 7%nat; intros Gs1 Gs2 Gs3 Gs4 Gs5 Gs6 (Ct & Cc & Cr & Cp & Cn & Cs & Cf & Cd); nd_post).
          pose proof (sec_facts n' ltac:(clear -Gs5; lia) Gs6) as SF. subst A. unfold SEC_UOFF, K_HIGH_MEM in *.
          unfold ablk, KLS, AIMG_HI in Gs2.   (* [comment removed for export] *)
          eapply disjoint_outside; [eapply (Q_obj _ _ _ _ _ _ _ PF a 1) | clear; lia]; clear -R Gs2 Gs3 Gs4 Gs5 SF Ct Cr RSP ORS; lia.
      + (nd_pre (FKD cls A n' Hb) 3%nat; intros K1 K2 K3; nd_post). atop_facts.
        eapply disjoint_outside; [eapply (Q_obj _ _ _ _ _ _ _ PF a 1) | clear; lia];
          clear -R K1 K3 FKO D_t_f D_f_res RSP OFKi OFKs OFKsa OFKsb; lia.   (* [comment removed for export] *)
    - (nd_pre SH 3%nat; intros a' Ha' ndR1__; nd_post; revert ndR1__; intros ->).
      destruct Ha' as [STa | [CIa | FK]].
      + eapply disjoint_outside; [eapply (Q_shad_hi _ _ _ _ _ _ _ PF a'); unfold AMALLOC_STACK in *; clear -STa LO BOT STK3; lia | clear; lia].
      + (nd_pre CIa 3%nat; intros iv Hiv R; nd_post). (pose proof (proj1 (Forall_forall _ _) CI_OK iv Hiv) as ndP__; nd_pre ndP__ 3%nat; intros Q1 Q2 Q3; nd_post). cbn [fst snd] in *.
        eapply disjoint_outside; [eapply (Q_shad_img _ _ _ _ _ _ _ PF a'); unfold AIMG_HI in *; clear -R Q1 Q3; lia | clear; lia].
      + (nd_pre FK 5%nat; intros cls FA sz Hin R; nd_post). (nd_pre (FKD cls FA sz Hin) 3%nat; intros K1 K2 K3; nd_post). atop_facts.
        eapply disjoint_outside; [eapply (Q_shad_obj _ _ _ _ _ _ _ PF a') | clear; lia]; clear -R K1 K3 FKO D_f_res RSP OFKi OFKs OFKsa OFKsb; lia. }
  assert (HFKp : AFK L LB m_pre).
  { eapply (hf_frame _ HL L LB m m_pre); [exact HFK | exact MUall | exact WMall |].
    unfold fake_untouched. pose proof (ao_t L ALO) as OT. unfold aobj in OT.
    assert (SHF : 2148239360 <= shad (al_fake L) /\ shad (al_fake L) + shlen 11571200 <= 17594332446720   (* [comment removed for export] *)
                  /\ (shad (al_space_beg L + c * 4294967296) + 536870912 <= shad (al_fake L)
                      \/ shad (al_fake L) + shlen 11571200 <= shad (al_space_beg L + c * 4294967296 + mu0))
                  /\ shad (al_space_beg L + c * 4294967296) <= shad (al_space_beg L + c * 4294967296 + mu0)
                  /\ 2201439137792 <= shad (al_space_beg L + c * 4294967296)).
    { rewrite !shad_div, !shlen_div. unfold ASHOFF in *. destruct PF as (_ & _ & (F1 & F2 & F3 & F4 & F5 & F6) & _).
      clear -FKO F1 F2 F3 F4 F5 F6 D_f_res RSP OFKi OFKs OFKsa OFKsb. Z.div_mod_to_equations. dlia. }
    (nd_pre SHF 5%nat; intros SF1 SF2 SF3 SF4 SF5; nd_post).
    unfold AMALLOC_STACK, AINSTANCE in *. destruct PF as (PF1 & PF2 & PF3 & PF4).
    repeat (apply Forall_cons; [cbn [fst snd];
      clear -LO BOT STK3 SP47 STK2 OT FKO ORS RSP ODT D_f_res D_t_f D_d_res D_t_d C16 PF3 PF4 SF1 SF2 SF3 SF4 SF5 SHHI TL1 TL2 SP1 TBND TBNDa TBNDb TIMG TIMGa TIMGb OFKi OFKs OFKsa OFKsb DBND DBNDa DBNDb DIMG DIMGa DIMGb;
      repeat (split; [fu_lia|]); fu_lia |]).   (* [comment removed for export] *)
    apply Forall_nil. }
  (* [comment removed for export] *)
  eapply evtF_mono.
  { eapply (calloc_tail_gen DI L RNG1 ra sp gp tp spA t0d t1d t2d a1d a2d a3d a4d a5d a6d a7d t3d t4d t5d t6d
              s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s4A s5A s6A s3i (Z_to_bv 64 qn) (Z_to_bv 64 qs) sp F fc m1
              n (al_t L) c cnt AB UB PG room lo b0 b1 szh szl ctxj (1 + Z.of_nat (length trc)) (al_space_beg L)
              (Z_to_bv 64 (max_count st_pre c)) (Z_to_bv 64 S) stj1 j1 j2 (Z_to_bv 8 250) sj' sjunk uj fr0 frc junk0 junk2 tb trc).
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
    all: try (lazymatch goal with |- tclr _ _ => first [exact XTAB | tclr_solve ALO ltac:(fail)] end).      (* [comment removed for export] *)
    all: match goal with |- ?G => idtac "REMT" G end. }
  (* [comment removed for export] *)
  cbv beta. intros ms' PM.
  unfold apop. rewrite HCNT, !a_next_put_cls, !a_live_put_cls.
  apply (malloc_post_genU_shift DI L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc n (al_t L) c cnt AB UB PG room lo b1 _ _ (repeat (Z_to_bv 8 0) (Z.to_nat n)) m_pre m1 ms') in PM;
    [| eapply munch_weaken; [| exact MU1]; unfold sub_fp, acache_addr; cbn [outside]; intros q Hq; clear -Hq HspA; lia | exact WM1].
  cbv delta [PG g grz room] in PM, SHpre, SHsuf. subst UB. subst AB.
  eapply (amalloc_postU_shiftG CI _ L RNG RNG1 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st st_pre LB n lo m m_pre); [| exact FPLE |].
  { eapply (store_primU DI AQ ASEC AFK HL CI CI_OK L RNG1 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m_pre st_pre LB X_pre n lo c cnt k b1
              (Z_to_bv 64 (max_count st_pre c)) (Z_to_bv 64 (size_of_class c)) (repeat (Z_to_bv 8 0) (Z.to_nat n))).
    all: try exact PM.
    all: try lazymatch goal with
         | |- is_primary _ = _ => exact PRIM
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
End Zd1.
#[using="HL CI_OK CI_OK2"] Theorem acalloc_prim : ltac:(let t := eval cbv delta [acalloc_prim__stmt] in acalloc_prim__stmt in exact t).
Proof. exact acalloc_prim__body. Qed.

(* [comment removed for export] *)
#[using="HL CI_OK CI_OK2"] Theorem acalloc_all : acalloc_stmt CI (AHEAP_P (AH DI AQ ASEC AFK)).
Proof. unfold acalloc_stmt. intros. eapply acalloc_prim; eassumption. Qed.
End S.
End CANSEC1.
End TwB.
End ALCallocPG.

(* [comment removed for export] *)
Module AMallocPG.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA StepF SysStepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.ATlsKit.   (* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecFacts AMalloc_iface. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitR__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepExt2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_apoison__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecSlog__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_agbb__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc3g0__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc3g. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_amalloc_arep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepStore__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepStoreG. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARealloc_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARefillP. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepExt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepExt2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.APrimFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.F_aalloc1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agbb__A3W.F_aalloc2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc__A3W.F_aalloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc__A3W.F_amalloc_icpt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3g0__A3W.F_amalloc_pre OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agbb__A3W.F_aalloc2g OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3g OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3g0__A3W.F_amalloc_tailg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_amalloc_arep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepStore__A3W.ARepStore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepStoreG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.ARefill_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARefillP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ACallocG__A3W.ACallocG.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac fu_drop_fake := repeat match goal with H : context [al_fake _] |- _ => clear H end.
Ltac fu_drop_dtls := repeat match goal with H : context [al_dtls _] |- _ => clear H end.
Ltac fu_drop_tls := repeat match goal with H : context [ATPv] |- _ => clear H | H : context [kt_img] |- _ => clear H end.
Ltac fu_focus :=
  lazymatch goal with
  | |- context [al_fake _] => fu_drop_dtls; fu_drop_tls
  | |- context [al_dtls _] => fu_drop_fake; fu_drop_tls
  | |- context [ATPv] => fu_drop_fake; fu_drop_dtls
  | |- _ => fu_drop_fake; fu_drop_dtls; fu_drop_tls
  end.
Ltac fu_lia := first [solve [fu_focus; lia] | lia].
(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
(* [comment removed for export] *)
#[using="Type"] Local Lemma ablk_int : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6303744 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
#[using="Type"] Local Lemma aobj_int : forall a n, aobj a n -> 0x10000 <= n ->
  6303744 <= a /\ a + n <= ATOP /\ exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof.
  intros a n H Hn. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. (nd_pre H 5%nat; intros H1 H2 H3 H4 H5; nd_post).
  split; [lia|]. split; [lia|]. destruct H4; [exists 0 | exists 1]; lia.
Qed.
#[using="Type"] Local Lemma aobj4_int : forall a, aobj a 4096 ->
  4096 <= a /\ a + 4096 <= ATOP
  /\ (exists k, 0 <= k <= 1 /\ a + 4096 <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a)
  /\ (exists j, 0 <= j <= 1 /\ a + 4096 <= 65536 + j * 18446744073709551616 /\ 6303744 * j <= a).
Proof.
  intros a H. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. (nd_pre H 5%nat; intros H1 H2 H3 H4 H5; nd_post).
  split; [lia|]. split; [lia|]. split; [destruct H4; [exists 0 | exists 1]; lia | destruct H5 as [_ [H5|H5]]; [exists 0 | exists 1]; lia].
Qed.
(* [comment removed for export] *)
Local Ltac dlia := repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
#[using="Type"] Lemma amalloc_prim_eq : forall RESV st n c,
  1 <= n -> is_primary n = true -> class_id (needed_size n) = c ->
  amalloc ATOP RESV st n =
    cache_alloc st c (fun st1 (ok : bool) =>
      if ok then SRet (set_next (N.succ (a_next st1)) (set_live (<[ a_next st1 := CPrim c n ]> (a_live st1)) st1), Some (a_next st1))
      else SRet (st1, None)).
Proof.
  intros RESV st n c N PRIM HC. (pose proof (prim_facts n N PRIM) as ndP__; nd_pre ndP__ 8%nat; intros NS RZR RZE RZM RLR RSR RSM NSR; nd_post).
  unfold amalloc.
  replace (2 ^ 40 <? n) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (2 ^ 40 <? needed_size n) with false by (symmetry; apply Z.ltb_ge; lia). cbn [orb].
  rewrite PRIM, HC. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma slot_carveG : forall m AB S n rz,
  junk_at m AB S -> (rz = 16 \/ 32 <= rz) -> 0 <= n -> rz + n <= S ->
  exists b0 b1 szh szl ctxj uj (j1 j2 : word),
       rw_cells asegs m (AB + rz + -16) [C1 (Z_to_bv 8 b0); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 szh); C4 (Z_to_bv 64 szl); C8 (Z_to_bv 64 ctxj)]
    /\ 0 <= b1 < 256
    /\ rw_cells asegs m (AB + rz) [CB (Z.to_nat n) uj]
    /\ (16 < rz -> rw_cells asegs m AB [C8 j1; C8 j2] /\ junk_at m (AB + 16) (rz - 32))
    /\ junk_at m (AB + rz + n) (S - rz - n).
Proof.
  intros m AB S n rz JK RZ N FIT.
  destruct (Z.eq_dec rz 16) as [->|NE].
  - destruct (junk_split m AB 16 (S - 16) ltac:(replace (16 + (S - 16)) with S by lia; exact JK) ltac:(lia) ltac:(lia)) as [HJ R1].
    destruct (junk_split m (AB + 16) n (S - 16 - n) ltac:(replace (n + (S - 16 - n)) with (S - 16) by lia; exact R1) ltac:(lia) ltac:(lia)) as [[uj UJ] TL].
    (nd_pre (hdr_of_junk m AB HJ) 8%nat; intros b0 b1 szh szl ctxj HDR B0 B1; nd_post).
    exists b0, b1, szh, szl, ctxj, uj, w0, w0.
    replace (AB + 16 + -16) with AB by lia. split; [exact HDR|]. split; [exact B1|]. split; [exact UJ|].
    split; [intros; exfalso; lia|]. exact TL.
  - assert (RZ2 : 32 <= rz) by lia.
    destruct (junk_split m AB 16 (S - 16) ltac:(replace (16 + (S - 16)) with S by lia; exact JK) ltac:(lia) ltac:(lia)) as [LHJ R1].
    destruct (junk_split m (AB + 16) (rz - 32) (S - rz + 16) ltac:(replace (rz - 32 + (S - rz + 16)) with (S - 16) by lia; exact R1) ltac:(lia) ltac:(lia)) as [MID R2].
    destruct (junk_split m (AB + 16 + (rz - 32)) 16 (S - rz) ltac:(replace (16 + (S - rz)) with (S - rz + 16) by lia; exact R2) ltac:(lia) ltac:(lia)) as [HJ R3].
    destruct (junk_split m (AB + 16 + (rz - 32) + 16) n (S - rz - n) ltac:(replace (n + (S - rz - n)) with (S - rz) by lia; exact R3) ltac:(lia) ltac:(lia)) as [[uj UJ] TL].
    (nd_pre (hdr_of_junk m _ HJ) 8%nat; intros b0 b1 szh szl ctxj HDR B0 B1; nd_post).
    (nd_pre (c8c8_of_junk m AB LHJ) 3%nat; intros j1 j2 LH; nd_post).
    exists b0, b1, szh, szl, ctxj, uj, j1, j2.
    replace (AB + 16 + (rz - 32)) with (AB + rz + -16) in HDR by lia.
    replace (AB + 16 + (rz - 32) + 16) with (AB + rz) in UJ, TL by lia.
    split; [exact HDR|]. split; [exact B1|]. split; [exact UJ|]. split; [intros _; split; [exact LH| exact MID]|]. exact TL.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma malloc_post_gen_shift : forall DI L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc n t c cnt AB UB PG pgw lo b1 maxc csz uj m0 m1 ms',
  malloc_post_gen DI L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc n t c cnt AB UB PG pgw lo b1 maxc csz uj m1 ms' ->
  munch [(bv_unsigned sp - 4096, bv_unsigned sp); (t + 208 + c * 80, t + 208 + c * 80 + 4); (t + 2784, t + 2792)]%Z m0 m1 -> wmono asegs m0 m1 ->
  malloc_post_gen DI L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc n t c cnt AB UB PG pgw lo b1 maxc csz uj m0 ms'.
Proof.
  intros until ms'. intros PM MU0 WM0. unfold malloc_post_gen in *.
  (nd_pre PM 21%nat; intros id t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' sj' stj' E MU REST; nd_post).
  exists id, t0, t1, t2, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m', sj', stj'. split; [exact E|]. split; [| split; [eapply wmono_trans; [exact WM0 | exact (proj1 REST)] | exact (proj2 REST)]].
  eapply munch_trans; [eapply munch_weaken; [| exact MU0] | exact MU]. unfold sub_fp. cbn [outside]. intros q Hq. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma amalloc_post_shiftG : forall CI AHEAP L RNG RNG1 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st st' LB n lo m m_pre r RNG2 ms',
  amalloc_post CI AHEAP L RNG1 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st' LB n lo m_pre r RNG2 ms' ->
  fp_le RNG RNG1 -> aheap_pres CI LB (bv_unsigned sp) m m_pre ->
  amalloc_post CI AHEAP L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB n lo m r RNG2 ms'.
Proof.
  intros until ms'. intros PM LE PRES. unfold amalloc_post in *.
  (nd_pre PM 22%nat; intros FP t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' E MI ST PR REST; nd_post).
  split; [eapply fp_le_trans; [exact LE | exact FP]|].
  exists t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m'. split; [exact E|]. split; [exact MI|]. split; [exact ST|].
  split; [eapply aheap_pres_trans; [exact PRES | exact PR] | exact REST].
Qed.

#[using="Type"] Lemma ablocks_xbusyG : forall L st st' X X' LB, ablocks L st X LB -> x_busy X' = x_busy X -> a_live st' = a_live st -> ablocks L st' X' LB.
Proof. intros. eapply ablocks_same; eassumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Pres.
Variables (sp t SB c mu ACL lo : Z).
(* [comment removed for export] *)
Notation Wp := ([(sp - 4096, sp); (t + 208, t + 3169); (AINSTANCE, AINSTANCE + 728); (SB + 137438953472 + c * 128, SB + 137438953472 + c * 128 + 128);
                 (SB + c * 4294967296 + mu, SB + c * 4294967296 + 4294967296);
                 (shad (SB + c * 4294967296 + mu), shad (SB + c * 4294967296) + 536870912)]%Z) (only parsing).
Definition pfactsG : Prop :=
     (ACL = ATOP /\ ACL <= lo /\ lo <= sp - 4096 /\ sp <= 2^47)
  /\ (4096 <= t /\ t + 4096 <= ACL /\ (t + 4096 <= 2147446784 \/ 17594333495296 <= t) /\ (t + 4096 <= 65536 \/ 6303744 <= t))   (* [comment removed for export] *)
  /\ (17594333495296 <= SB /\ SB + 137438957568 <= ACL /\ SB mod 65536 = 0 /\ 1 <= c <= 31 /\ 0 <= mu <= 3758096384 /\ mu mod 8 = 0)
  /\ (t + 4096 <= SB \/ SB + 137438957568 <= t).
Hypothesis PF : pfactsG.

#[using="rc ACL lo PF"] Lemma Q_stack : forall A k, sp <= A -> 0 <= k -> disjoint_from Wp A k.
Proof. intros. (pose proof PF as ndP__; nd_pre ndP__ 4%nat; intros F1 F2 F3 F4; nd_post). unfold AINSTANCE in *. cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF. repeat split; try exact I; Z.div_mod_to_equations; lia. Qed.
#[using="rc ACL lo PF"] Lemma Q_img : forall A k, 0x10000 <= A -> 0 <= k -> A + k <= 6303744 -> (A + k <= AINSTANCE \/ AINSTANCE + 728 <= A) -> disjoint_from Wp A k.   (* [comment removed for export] *)
Proof. intros. (pose proof PF as ndP__; nd_pre ndP__ 4%nat; intros F1 F2 F3 F4; nd_post). unfold AINSTANCE in *. cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF. repeat split; try exact I; Z.div_mod_to_equations; lia. Qed.
(* [comment removed for export] *)
#[using="rc ACL lo PF"] Lemma Q_slot : forall A k, SB <= A -> 0 <= k -> A + k <= SB + 137438953472 ->
  (A + k <= SB + c * 4294967296 + mu \/ SB + c * 4294967296 + 4294967296 <= A) -> disjoint_from Wp A k.
Proof. intros. (pose proof PF as ndP__; nd_pre ndP__ 4%nat; intros F1 F2 F3 F4; nd_post). unfold AINSTANCE in *. cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF. repeat split; try exact I; Z.div_mod_to_equations; lia. Qed.
#[using="rc lo PF"] Lemma Q_obj : forall A k, ((6303744 <= A /\ A + k <= 2147446784) \/ 17594333495296 <= A) -> 0 <= k -> A + k <= ACL ->   (* [comment removed for export] *) (A + k <= t \/ t + 4096 <= A) -> (A + k <= SB \/ SB + 137438957568 <= A) -> disjoint_from Wp A k.
Proof. intros. (pose proof PF as ndP__; nd_pre ndP__ 4%nat; intros F1 F2 F3 F4; nd_post). unfold AINSTANCE in *. cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF. repeat split; try exact I; Z.div_mod_to_equations; lia. Qed.
(* [comment removed for export] *)
#[using="rc lo PF"] Lemma Q_shad_hi : forall a, ACL <= a < 2^47 -> disjoint_from Wp (shad a) 1.
Proof. intros. (pose proof PF as ndP__; nd_pre ndP__ 4%nat; intros F1 F2 F3 F4; nd_post). unfold AINSTANCE in *. cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF. repeat split; try exact I; Z.div_mod_to_equations; lia. Qed.
#[using="rc ACL lo PF"] Lemma Q_shad_img : forall a, 0x10000 <= a < 6303744 -> disjoint_from Wp (shad a) 1.   (* [comment removed for export] *)
Proof. intros. (pose proof PF as ndP__; nd_pre ndP__ 4%nat; intros F1 F2 F3 F4; nd_post). unfold AINSTANCE in *. cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF. repeat split; try exact I; Z.div_mod_to_equations; lia. Qed.
#[using="rc lo PF"] Lemma Q_shad_obj : forall a, ((6303744 <= a /\ a + 1 <= 2147446784) \/ 17594333495296 <= a) -> a < ACL -> (a + 1 <= SB \/ SB + 137438957568 <= a) -> disjoint_from Wp (shad a) 1.   (* [comment removed for export] *)
Proof. intros. (pose proof PF as ndP__; nd_pre ndP__ 4%nat; intros F1 F2 F3 F4; nd_post). unfold AINSTANCE in *. cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF. repeat split; try exact I; Z.div_mod_to_equations; lia. Qed.
(* [comment removed for export] *)
#[using="rc lo PF"] Lemma Q_objL : forall A k, ((A + k <= 65536 \/ 6303744 <= A) /\ (A + k <= 2147446784 \/ 17594333495296 <= A)) -> 0 <= k -> A + k <= ACL ->
  (A + k <= t \/ t + 4096 <= A) -> (A + k <= SB \/ SB + 137438957568 <= A) -> disjoint_from Wp A k.
Proof. intros. (pose proof PF as ndP__; nd_pre ndP__ 4%nat; intros F1 F2 F3 F4; nd_post). unfold AINSTANCE in *. cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF. repeat split; try exact I; Z.div_mod_to_equations; lia. Qed.
#[using="rc lo PF"] Lemma Q_shad_objL : forall a, 0 <= a -> a < ACL -> (a + 1 <= SB \/ SB + 137438957568 <= a) -> disjoint_from Wp (shad a) 1.
Proof. intros. (pose proof PF as ndP__; nd_pre ndP__ 4%nat; intros F1 F2 F3 F4; nd_post). unfold AINSTANCE in *. cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF. repeat split; try exact I; Z.div_mod_to_equations; lia. Qed.
#[using="rc ACL lo PF"] Lemma Q_imsh : forall A k, 2147450880 <= A -> A + k <= 2148238848 -> 0 <= k -> disjoint_from Wp A k.      (* [comment removed for export] *)
Proof. intros. (pose proof PF as ndP__; nd_pre ndP__ 4%nat; intros F1 F2 F3 F4; nd_post). unfold AINSTANCE in *. cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF. repeat split; try exact I; Z.div_mod_to_equations; lia. Qed.
End Pres.

Section S.
Variable DI : ADepotIface.
Variables (AQ ASEC : alayout -> astate -> aconc -> amem -> Prop) (AFK : alayout -> list ablock -> amem -> Prop).
Hypothesis HL : ahole_laws (AH DI AQ ASEC AFK).
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI) CI.
(* [comment removed for export] *)
Hypothesis CI_OK2 : Forall (fun iv => snd iv <= AINSTANCE \/ AINSTANCE + 728 <= fst iv) CI.

Definition amalloc_prim__stmt : Prop := forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (n lo : Z) (tr : list Z) (RESV : list (Z * Z)),
  (* [comment removed for export] *)
  is_primary n = true ->
  (* [comment removed for export] *)
  AHEAP_P (AH DI AQ ASEC AFK) L RNG st LB m ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AMALLOC_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 n -> 1 <= n <= AREQMAX ->
  aunw m L RNG lo AMALLOC_PC sp s0 ra tr ->
  bv_unsigned s0 <> bv_unsigned sp + 8 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AMALLOC_PC ->
  bv_unsigned sp mod 16 = 0 ->
  rng RNG lo (bv_unsigned sp - lo) ->
  aresv_ok L RESV ->
  implS asegs RNG (aembed ATOP (amalloc ATOP RESV st n))
        (epostF (amalloc_post CI (AHEAP_P (AH DI AQ ASEC AFK)) L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB n lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AMALLOC_SYM) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'amalloc_prim__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'amalloc_prim__stmt 1).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'amalloc_prim__stmt 2).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'amalloc_prim__stmt 3).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'amalloc_prim__stmt 4).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'amalloc_prim__stmt 5).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'amalloc_prim__stmt 6).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'amalloc_prim__stmt 7).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'amalloc_prim__stmt 8).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'amalloc_prim__stmt 9).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'amalloc_prim__stmt 10).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'amalloc_prim__stmt 11).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'amalloc_prim__stmt 12).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'amalloc_prim__stmt 13).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'amalloc_prim__stmt 14).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'amalloc_prim__stmt 15).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'amalloc_prim__stmt 16).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'amalloc_prim__stmt 17).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'amalloc_prim__stmt 18).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'amalloc_prim__stmt 19).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'amalloc_prim__stmt 20).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'amalloc_prim__stmt 21).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'amalloc_prim__stmt 22).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'amalloc_prim__stmt 23).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'amalloc_prim__stmt 24).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'amalloc_prim__stmt 25).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'amalloc_prim__stmt 26).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'amalloc_prim__stmt 27).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'amalloc_prim__stmt 28).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'amalloc_prim__stmt 29).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'amalloc_prim__stmt 30).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'amalloc_prim__stmt 31).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'amalloc_prim__stmt 32).
Variable F : ltac2:(SecDietF.SzSecF.ty 'amalloc_prim__stmt 33).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'amalloc_prim__stmt 34).
Variable m : ltac2:(SecDietF.SzSecF.ty 'amalloc_prim__stmt 35).
Variable st : ltac2:(SecDietF.SzSecF.ty 'amalloc_prim__stmt 36).
Variable LB : ltac2:(SecDietF.SzSecF.ty 'amalloc_prim__stmt 37).
Variable n : ltac2:(SecDietF.SzSecF.ty 'amalloc_prim__stmt 38).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'amalloc_prim__stmt 39).
Variable tr : ltac2:(SecDietF.SzSecF.ty 'amalloc_prim__stmt 40).
Variable RESV : ltac2:(SecDietF.SzSecF.ty 'amalloc_prim__stmt 41).
#[using="HL CI_OK CI_OK2"] Lemma amalloc_prim__body : ltac:(let T := type of (fun (h : amalloc_prim__stmt) => h L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st LB n lo tr RESV) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (st, (LB, (n, (lo, (tr, RESV)))))))))))))))))))))))))))))))))))))))))) as _.
 intros PRIM AHP MI ST BOT LO TP Ha0 NR AUNW S0NE RA4 RANE SP16 RSTK ROK.
  assert (N : 1 <= n <= AREQMAX) by exact NR. assert (N1 : 1 <= n) by (clear -NR; lia).
  (* [comment removed for export] *)
  assert (EXARM : exists trc,
      ((bv_unsigned sp + 16 < al_top L /\ uchain m (al_top L) AMALLOC_PC (bv_unsigned sp) (bv_unsigned s0) 28%nat tr /\ (length tr <= 28)%nat /\ trc = bv_unsigned ra :: tr
        /\ rng RNG lo (al_top L - lo))
       \/ (al_top L <= bv_unsigned sp + 16 /\ bv_unsigned sp < 2^47 /\ trc = []))
      /\ In (AMALLOC_PC :: trc) (al_U L) /\ (length trc <= 29)%nat /\ bv_unsigned sp < 2^47).
  { (pose proof (alayout_stack L (proj1 AHP)) as ndP__; nd_pre ndP__ 3%nat; intros K1 K2 K3; nd_post).
    destruct AUNW as [(T1 & U1 & L1 & I1 & R1)|(T1 & T2 & I1)].
    - exists (bv_unsigned ra :: tr). split; [left; split; [exact T1|]; split; [exact U1|]; split; [exact L1|]; split; [reflexivity| exact R1]|].
      split; [exact I1|]. split; [cbn [length]; clear -L1; lia | clear -T1 K2; lia].
    - exists (@nil Z). split; [right; split; [exact T1|]; split; [exact T2| reflexivity]|]. split; [exact I1|]. split; [cbn [length]; clear; lia | exact T2]. }
  (nd_pre EXARM 5%nat; intros trc ARM TRU LTRC SP47; nd_post).
  (nd_pre AHP 4%nat; intros ALO ARNG [X [AR BL]] HFK; nd_post).
  remember (class_id (needed_size n)) as c eqn:HC0. symmetry in HC0.
  (pose proof (prim_facts n N1 PRIM) as ndP__; nd_pre ndP__ 8%nat; intros NS RZR RZE RZM RLR RSR RSM NSR; nd_post).
  (pose proof (prim_class_facts n c N1 PRIM HC0) as ndP__; nd_pre ndP__ 5%nat; intros C16 NSZ SM16 SMALL MCB; nd_post). clear SMALL.
  (pose proof (cls_facts c C16) as ndP__; nd_pre ndP__ 4%nat; intros SZB _ _ _; nd_post).
  assert (HCK : 1 <= c < K_NUM_CLASSES) by (unfold K_NUM_CLASSES; clear -C16; lia).
  assert (NM8 : needed_size n mod 8 = 0) by (rewrite NS; clear -RSM RZM; Z.div_mod_to_equations; lia).
  (* [comment removed for export] *)
  pose proof AR as AR0. (nd_pre AR0 12%nat; intros WF RT INST THR CLS HQ HS HD HRO RT2 AVL RT3; nd_post).
  (nd_pre THR 6%nat; intros T0 T40 CACHES CSTATS [sj [STATS LSJ]] UNW; nd_post).
  pose proof WF as WF0. (nd_pre WF0 11%nat; intros SBE PAE SAL SLO SHI PERC OUTC BUSY LIVE FRESH UNIQ; nd_post).
  (nd_pre (PERC c HCK) 12%nat; intros A1 A2 A3 A4 A5 A6 A7 LENF LENC CNTB ND RANGE; nd_post).
  (pose proof (alayout_space L ALO) as ndP__; nd_pre ndP__ 4%nat; intros SP1 SP2 SP3 SP4; nd_post).
  (pose proof (alayout_t L ALO) as ndP__; nd_pre ndP__ 4%nat; intros TL1 TL2 TL3 TL4; nd_post).
  (pose proof (alayout_ctx L ALO) as ndP__; nd_pre ndP__ 5%nat; intros CL1 CL2 CL3 CL4 CL5; nd_post).
  (pose proof (alayout_depot L ALO) as ndP__; nd_pre ndP__ 10%nat; intros DL1 DL2 DL3 DL4 DL5 DL6 DL7 DL8 DL9 DL10; nd_post).
  (pose proof (aobj4_int _ (ao_t L ALO)) as ndP__; nd_pre ndP__ 4%nat; intros _ _ (kT & TBND & TBNDa & TBNDb) (jT & TIMG & TIMGa & TIMGb); nd_post).   (* [comment removed for export] *)
  (pose proof (aobj_int _ _ (ao_ctx L ALO) ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros CTXi _ (kC & CBND & CBNDa & CBNDb); nd_post).
  (pose proof (aobj_int _ _ (ao_nodes L ALO) ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros NODi _ (kN & NBND & NBNDa & NBNDb); nd_post).
  (pose proof (aobj_int _ _ (ao_store L ALO) ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros STOi _ (kR & SBND & SBNDa & SBNDb); nd_post).
  (pose proof (aobj_int _ _ (ao_fake L ALO) ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros OFKi _ (kF & OFKs & OFKsa & OFKsb); nd_post).
  (pose proof (aobj4_int _ (ao_dtls L ALO)) as ndP__; nd_pre ndP__ 4%nat; intros _ _ (kD & DBND & DBNDa & DBNDb) (jD & DIMG & DIMGa & DIMGb); nd_post).
  (pose proof (alayout_stack L ALO) as ndP__; nd_pre ndP__ 3%nat; intros STK1 STK2 STK3; nd_post).
  pose proof (alayout_res_disj L ALO) as [SCX TSP].
  pose proof RT as RT0.
  (nd_pre RT0 28%nat; intros GPG GOT GOT80 RIC LS1 REAL IMAX4 FLG5 FLG HPP SHB CANP TI TK INI2 LAY MCS OOM3 PGC HK2 CF8 CF34 CSMT T88 TSD LS2 CT8 CT; nd_post).
  pose proof INI2 as INI. rw_split INI 1%nat INI1 INIx. clear INIx.
  pose proof OOM3 as OOM. rw_split OOM 2%nat OOMx RSS. clear OOMx.
  pose proof IMAX4 as IMAX. rw_split IMAX 3%nat IMAX3 IMAXx. clear IMAXx.
  pose proof T0 as TT0. rw_split TT0 1%nat TTctx TT.
  pose proof ARNG as ARNG0. (nd_pre ARNG 10%nat; intros RIMG RT4 RCTX RNO RSTO RRI RFK RSFK RDTLS RCLS; nd_post).
  assert (RTLS : rng_atls RNG) by ((nd_pre ARNG0 14%nat; intros _ _ _ _ _ _ _ _ _ _ _ _ _ RTLSx; nd_post); exact RTLSx).      (* [comment removed for export] *)
  assert (RCTX4 : rng RNG (al_ctx L) 4096) by (eapply rng_sub'; [exact RCTX|]; clear; lia).
  word_range sp SPR.
  box CL5. box DL7. box DL8. box DL9. box DL10. box TSP. box SCX.
  (* [comment removed for export] *)
  rewrite (amalloc_prim_eq RESV st n c N1 PRIM HC0).
  (* [comment removed for export] *)
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
  (nd_pre P4 24%nat; intros spA t0c t1c t2c a4c a5c a6c a7c t3c t4c t5c t6c s0A s1A s2A s3A s4A s5A s0i fr0 junk2 tb m4 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 13%nat; intros HspA MU4 WM4 MI4 ST4 FRa FR16 SS TB LTB TRF FRS UW4; nd_post).
  apply evtF_done.
  assert (AR4 : AREP (AH DI AQ ASEC AFK) L st X m4).
  { eapply (AREP_frame_pre _ HL L st X m m4); [exact ALO | exact AR | exact MU4 | exact WM4 | | exact UW4].
    apply Forall_cons; [unfold apre; cbn [fst snd]; intros _; left; unfold AMALLOC_STACK in *; clear -LO BOT STK3; lia|].
    apply Forall_cons; [unfold apre; cbn [fst snd]; intros _; right; split; reflexivity| apply Forall_nil]. }
  (* [comment removed for export] *)
  eapply (@calloc_arep_gen _ _ _ HL _ _ _ L RNG _ _ gp tp t0c t1c t2c _ _ _ _ _ _ a4c a5c a6c a7c _ _ _ _ _ _ _ _ _ _ t3c t4c t5c t6c F fc m4 st X c lo (needed_size n)
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
       end.
  (* [comment removed for export] *)
  intros st_pre X_pre RNG1 m_pre cnt k ms1 CRET. unfold calloc_retG in CRET.
  (nd_pre CRET 37%nat; intros FPLE ARp ARNGp HCNT POS NK NB KR XB L1 L2 L3 L4 L5 L6 L7 L8 MUc WMc MIp t0d t1d t2d a1d a2d a3d a4d a5d a6d a7d t3d t4d t5d t6d m1 stj1 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 6%nat; intros MU1 WM1 MI1 ST1 CR1 STS1; nd_post).
  rewrite ?unsigned_lit in MUc by (clear -SPR HspA LO BOT STK3; unfold AMALLOC_STACK in *; lia).
  rewrite ?unsigned_lit in MU1 by (clear -SPR HspA LO BOT STK3; unfold AMALLOC_STACK in *; lia).
  rewrite ?unsigned_lit in ST1 by (clear -SPR HspA LO BOT STK3; unfold AMALLOC_STACK in *; lia).
  replace (bv_unsigned spA + -128) with (bv_unsigned sp - 2272) in ST1 by (clear -HspA; lia).
  cbn beta iota. apply implS_ret.
  replace (ret_pc (Z_to_bv 64 0x33ea8)) with (Z_to_bv 64 0x33ea8) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  (* [comment removed for export] *)
  pose proof ARp as AR0. (nd_pre AR0 12%nat; intros WF' RT' INST' THR' CLS' HQ' HS' HD' HRO' RT2' AVL' RT3'; nd_post).
  (nd_pre THR' 6%nat; intros T0' T40' CACHES' CSTATS' [sj' [STATS' LSJ']] UNW'; nd_post).
  pose proof WF' as WF0. (nd_pre WF0 11%nat; intros SBE' PAE' SAL' SLO' SHI' PERC' OUTC' BUSY' LIVE' FRESH' UNIQ'; nd_post).
  (nd_pre (PERC' c HCK) 12%nat; intros B1' B2' B3' B4' B5' B6' B7' LENF' LENC' CNTB' ND' RANGE'; nd_post).
  (nd_pre (kit_cache_pop _ L st_pre X_pre m_pre c cnt ARp HCK HCNT POS) 11%nat; intros k' chunks NK' _ _ CR CH LCH NTH JK FSH; nd_post).
  assert (EK : k' = k) by (rewrite NK in NK'; injection NK'; intros E; symmetry; exact E). subst k'.
  (* [comment removed for export] *)
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
  (nd_pre KSF 3%nat; intros KS0 KS1 KS2; nd_post).
  assert (GEO : al_space_beg L <= AB /\ AB + S <= al_space_beg L + K_SPACE_SIZE /\ AB mod 16 = 0
                /\ AB + S <= aregion L c + c_allocated_user (get_cls st_pre c) /\ aregion L c <= AB).
  { subst AB. unfold aslot_addr, aregion, K_REGION, K_SPACE_SIZE, K_FREEARR_OFF, K_ALIGN in *. fold S.
    remember (k * S) as KS eqn:HKS. clear HKS.
    change (2^37) with 137438953472. change (2^32) with 4294967296 in *.
    split; [clear -KS0 C16; lia|]. split; [clear -KS1 B1' B2' C16 NSZ; lia|]. split; [| clear -KS0 KS1 B1'; lia].
    clear -SP3 C16 KS2. Z.div_mod_to_equations; lia. }
  (nd_pre GEO 5%nat; intros G1 G2 G3 G4 G5; nd_post). unfold K_SPACE_SIZE in G2. change (2^37) with 137438953472 in G2.
  assert (EAB : AB = aslot_addr L c k) by reflexivity. clearbody AB.
  assert (ES : S = size_of_class c) by reflexivity.
  (* [comment removed for export] *)
  assert (RZC : rz_size n = 16 \/ 32 <= rz_size n) by (clear -RZR RZM; Z.div_mod_to_equations; lia).
  (nd_pre (slot_carveG m_pre AB S n (rz_size n) JK RZC ltac:(clear -N; lia) ltac:(fold S in NSZ; clear -NSZ NS RSR; lia)) 13%nat; intros b0 b1 szh szl ctxj uj j1 j2 HDR B1 UJ LH TL; nd_post).
  set (UB := AB + rz_size n) in *. assert (EUB : UB = AB + rz_size n) by reflexivity. clearbody UB.
  (* [comment removed for export] *)
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
  (nd_pre (shadow_carve m_pre (shad AB) (shlen S) grz g room FSH GR3 GR4 GR6 GR5) 5%nat; intros SHA SHpre [sjunk SHU] SHP SHsuf; nd_post).
  rewrite <- GR7 in SHU, SHP, SHsuf.
  set (PG := shad UB + g) in *.
  (* [comment removed for export] *)
  pose proof RT' as RT0.
  (nd_pre RT0 28%nat; intros GPG' GOT' GOT80' RIC' LS1' REAL' IMAX4' FLG5' FLG' HPP' SHB' CANP' TI' TK' INI2' LAY' MCS' OOM3' PGC' HK2' CF8' CF34' CSMT' T88' TSD' LS2' CT8' CT'; nd_post).
  pose proof INI2' as INI'. rw_split INI' 1%nat INI1' INIx. clear INIx.
  pose proof OOM3' as OOM'. rw_split OOM' 2%nat OOMx RSS'. clear OOMx.
  pose proof IMAX4' as IMAX'. rw_split IMAX' 3%nat IMAX3' IMAXx. clear IMAXx.
  pose proof HK2' as HK'. rw_split HK' 1%nat HK1' HKx. clear HKx.
  pose proof T0' as TT0'. rw_split TT0' 1%nat TTctx' TT'.
  destruct (junk_split m_pre (al_t L + 2768) 16 16 CSTATS' ltac:(lia) ltac:(lia)) as [CSa CSb].
  destruct (junk_split m_pre (al_t L + 2768 + 16) 8 8 CSb ltac:(lia) ltac:(lia)) as [CS8 CSc].
  replace (al_t L + 2768 + 16) with (al_t L + 2784) in CS8 by lia.
  replace (al_t L + 2768 + 16 + 8) with (al_t L + 2792) in CSc by lia.
  (nd_pre INST' 9%nat; intros I32' I48' I64' I72' I112' I680' I984' I40' I56'; nd_post).
  pose proof ARNGp as ARNGp0. (nd_pre ARNGp 14%nat; intros RIMG' RT4' RCTX' RNO' RST' RRI' RFK' RSFK' RDTLS' RCLS' RPA' RSECS' RPSH' RTLS'; nd_post).
  (nd_pre (RCLS' c HCK) 4%nat; intros RREG RSREG RFA RSFA; nd_post).
  (* [comment removed for export] *)
  (nd_pre (alayout_slot_disj L AB 65536 ALO G1 ltac:(unfold K_SPACE_SIZE, K_FREEARR_OFF, aregion, K_REGION in *; generalize G4 B1' B2' C16 SP1 SZB; clear; intros; change (2^37) with 137438953472; lia) ltac:(clear; lia)) 5%nat; intros DJT DJC DJN DJS DJF; nd_post).
  (* [comment removed for export] *)
  assert (XTAB : tclr AB 65536).
  { apply (tclr_space L AB 65536 ALO); [exact G1|]. unfold K_SPACE_SIZE, K_FREEARR_OFF, aregion, K_REGION in *. generalize G4 B1' B2' C16 SP1 SZB; clear; intros. change (2^37) with 137438953472 in *. lia. }
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
  (* [comment removed for export] *)
  set (mu0 := c_mapped_user (get_cls st c)) in *.
  assert (OBJ : aregion_info L c = al_space_beg L + 137438953472 + c * 128 /\ aregion L c = al_space_beg L + c * 4294967296
                /\ shad (al_space_beg L + c * 4294967296) + 536870912 <= 17594333495296).
  { unfold aregion_info, aregion, K_REGION, K_SPACE_SIZE, ARI_STRIDE. change (2^37) with 137438953472. change (2^32) with 4294967296.
    split; [reflexivity|]. split; [reflexivity|]. rewrite shad_div. clear -SP1 SP2 C16. unfold ASHOFF, K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^37) with 137438953472 in *.
    Z.div_mod_to_equations. lia. }
  (nd_pre OBJ 3%nat; intros RIE RBE SHHI; nd_post).
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
  (* [comment removed for export] *)
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
  xport LS2' MU1 WM1 ltac:(clear -HspA SPR TL1 TL2 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport LAY' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport MCS' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport CF34' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport INI1' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport RSS' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport IMAX3' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport TI' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport TK' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport T88' MU1 WM1 ltac:(clear -HspA SPR TL1 TL2 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, ATP88, AMALLOC_STACK in *; lia).
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
  (* [comment removed for export] *)
  assert (PF : pfactsG (bv_unsigned sp) (al_t L) (al_space_beg L) c mu0 ATOP lo).
  { unfold pfactsG. pose proof (ao_t L ALO) as OT. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in OT.   (* [comment removed for export] *)
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
  (* [comment removed for export] *)
  assert (BB : forall b, In b (x_busy X) ->
      al_space_beg L <= xb_alloc L b /\ xb_alloc L b + size_of_class (xb_class b) <= al_space_beg L + 137438953472
      /\ (xb_alloc L b + size_of_class (xb_class b) <= al_space_beg L + c * 4294967296 + mu0 \/ al_space_beg L + c * 4294967296 + 4294967296 <= xb_alloc L b)).
  { intros b Hb. destruct (BUSY b Hb) as [CLB _].
    (nd_pre (PERC (xb_class b) CLB) 12%nat; intros Q1 Q2 _ _ _ _ _ _ _ _ _ QR; nd_post).
    pose proof (size_of_class_facts (xb_class b) CLB) as [QS _].
    assert (KB : 0 <= xb_slot b < ndist st (xb_class b)).
    { apply QR. apply in_app_iff. right. apply in_app_iff. right. unfold busy_slots. apply in_map_iff. exists b. split; [reflexivity|].
      apply filter_In. split; [exact Hb| apply Z.eqb_refl]. }
    (pose proof (slot_in_region L st (xb_class b) (xb_slot b) ltac:(clear -QS; lia) (proj1 Q1) KB) as ndP__; nd_pre ndP__ 3%nat; intros P5 P4 P0; nd_post).
    unfold xb_alloc. unfold K_NUM_CLASSES in CLB. unfold K_FREEARR_OFF in Q2.
    destruct (Z.eq_dec (xb_class b) c) as [EC|NC].
    - rewrite EC in P5, P4, Q1, Q2 |- *. rewrite RBE in P5, P4. change (c_mapped_user (get_cls st c)) with mu0 in Q1, Q2.
      clear -P5 P4 Q1 Q2 A1 A2 C16. unfold K_FREEARR_OFF in *. lia.
    - (pose proof (region_other_geo L c (xb_class b) ALO ltac:(clear -C16; lia) CLB NC) as ndP__; nd_pre ndP__ 4%nat; intros R1 R2 R3 _; nd_post). rewrite RBE in R2.
      clear -P5 P4 Q1 Q2 R1 R2 R3 A1. lia. }
  pose proof (ao_fake L ALO) as FKO. unfold aobj in FKO. pose proof (ao_res L ALO) as ORS. unfold aobj in ORS. pose proof (ao_space L ALO) as RSP.
  pose proof (ad_fake_res L ALO) as D_f_res. pose proof (ad_t_fake L ALO) as D_t_f. pose proof (ad_dtls_res L ALO) as D_d_res. pose proof (ad_t_dtls L ALO) as D_t_d.
  pose proof (ao_dtls L ALO) as ODT. unfold aobj in ODT. unfold adisj in D_f_res, D_t_f, D_d_res, D_t_d.
  assert (FKD : forall cls FA sz, In (mkABlock (ABFake cls) FA sz) LB -> al_fake L <= FA /\ 0 <= sz /\ FA + sz <= al_fake L + 11571200)
    by (intros cls FA sz Hin; exact (proj1 (proj2 BL) cls FA sz Hin)).
  assert (PRES : aheap_pres CI LB (bv_unsigned sp) m m_pre).
  { intros a Ha CL. split; [| intros Hw; apply WMall; exact Hw].
    apply MUall. rewrite wa_unsigned by exact Ha.
    destruct CL as [CL|TLSA].
    2:{ (* [comment removed for export] *)
        pose proof (ad_tls_t L ALO) as DLT. pose proof (ad_tls_res L ALO) as DLR. unfold adisj in DLT, DLR.
        pose proof atp_lin as TLN. pose proof atop_range as ATR0. pose proof atp_below_atop as TBA.
        destruct TLSA as [[T|(ta & Hta & ->)]|[IM|IM]].
        4:{ pose proof (ao_ahm L ALO) as OAH. pose proof (aobj_img _ _ OAH ltac:(clear; lia)) as OAHI. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in OAH, OAHI.
          rewrite <- (ao_ahm_eq L ALO) in IM. unfold AAHM_SZ in IM. pose proof (ad_ahm_t L ALO) as DA1. pose proof (ad_ahm_res L ALO) as DA2. unfold adisj in DA1, DA2.
            eapply disjoint_outside; [eapply (Q_obj _ _ _ _ _ _ _ PF a 1) | clear; lia]; clear -IM OAH OAHI DA1 DA2 RSP; lia. }
        3:{ unfold AIMSH_LO, AIMSH_LEN in IM. eapply disjoint_outside; [eapply (Q_imsh _ _ _ _ _ _ _ PF a 1) | clear; lia]; clear -IM; lia. }
        - eapply disjoint_outside; [eapply (Q_img _ _ _ _ _ _ _ PF a 1) | clear; lia]; pose proof ATPv_img as TPI; clear -T TPI; unfold AINSTANCE; lia.
        - eapply disjoint_outside; [eapply (Q_shad_objL _ _ _ _ _ _ _ PF ta) | clear; lia]; clear -Hta DLT DLR TLN ATR0 TBA RSP; lia. }
    destruct CL as [STa | [CIa | [BLK | SH]]].
    - eapply disjoint_outside; [eapply (Q_stack _ _ _ _ _ _ _ PF a 1); clear -STa; lia | clear; lia].
    - (nd_pre CIa 3%nat; intros iv Hiv R; nd_post). (pose proof (proj1 (Forall_forall _ _) CI_OK iv Hiv) as ndP__; nd_pre ndP__ 3%nat; intros Q1 Q2 Q3; nd_post).
      pose proof (proj1 (Forall_forall _ _) CI_OK2 iv Hiv) as Q4. cbn [fst snd] in *.
      eapply disjoint_outside; [eapply (Q_img _ _ _ _ _ _ _ PF a 1); unfold AIMG_HI in *; clear -R Q1 Q3 Q4; lia | clear; lia].
    - (nd_pre BLK 3%nat; intros b Hb R; nd_post). destruct b as [[p|cls] A n']; cbn [ab_addr ab_size] in R.
      + destruct (proj1 BL p A n' Hb) as [(xb & Hxb & Sb & Ub & Nb)|(mb0 & ms0 & Lp & EUA & Gs)].
        * (nd_pre (BB xb Hxb) 3%nat; intros Bb1 Bb2 Bb3; nd_post).
          pose proof (awf_fits L st X xb WF Hxb) as FIT. unfold xb_fits in FIT. rewrite Sb in FIT. unfold xb_user in Ub. subst A n'.
          eapply disjoint_outside; [eapply (Q_slot _ _ _ _ _ _ _ PF a 1) | clear; lia]; clear -R Bb1 Bb2 Bb3 FIT; lia.
        * (* [comment removed for export] *)
          cbn [sec_wf1] in Gs. (nd_pre Gs 7%nat; intros Gs1 Gs2 Gs3 Gs4 Gs5 Gs6 (Ct & Cc & Cr & Cp & Cn & Cs & Cf & Cd); nd_post).
          pose proof (sec_facts n' ltac:(clear -Gs5; lia) Gs6) as SF. subst A. unfold SEC_UOFF, K_HIGH_MEM in *.
          unfold ablk, KLS, AIMG_HI in Gs2.   (* [comment removed for export] *)
          eapply disjoint_outside; [eapply (Q_obj _ _ _ _ _ _ _ PF a 1) | clear; lia]; clear -R Gs2 Gs3 Gs4 Gs5 SF Ct Cr RSP ORS; lia.
      + (nd_pre (FKD cls A n' Hb) 3%nat; intros K1 K2 K3; nd_post). atop_facts.
        eapply disjoint_outside; [eapply (Q_obj _ _ _ _ _ _ _ PF a 1) | clear; lia];
          clear -R K1 K3 FKO D_t_f D_f_res RSP OFKi OFKs OFKsa OFKsb; lia.   (* [comment removed for export] *)
    - (nd_pre SH 3%nat; intros a' Ha' ndR1__; nd_post; revert ndR1__; intros ->).
      destruct Ha' as [STa | [CIa | FK]].
      + eapply disjoint_outside; [eapply (Q_shad_hi _ _ _ _ _ _ _ PF a'); unfold AMALLOC_STACK in *; clear -STa LO BOT STK3; lia | clear; lia].
      + (nd_pre CIa 3%nat; intros iv Hiv R; nd_post). (pose proof (proj1 (Forall_forall _ _) CI_OK iv Hiv) as ndP__; nd_pre ndP__ 3%nat; intros Q1 Q2 Q3; nd_post). cbn [fst snd] in *.
        eapply disjoint_outside; [eapply (Q_shad_img _ _ _ _ _ _ _ PF a'); unfold AIMG_HI in *; clear -R Q1 Q3; lia | clear; lia].
      + (nd_pre FK 5%nat; intros cls FA sz Hin R; nd_post). (nd_pre (FKD cls FA sz Hin) 3%nat; intros K1 K2 K3; nd_post). atop_facts.
        eapply disjoint_outside; [eapply (Q_shad_obj _ _ _ _ _ _ _ PF a') | clear; lia]; clear -R K1 K3 FKO D_f_res RSP OFKi OFKs OFKsa OFKsb; lia. }
  assert (HFKp : AFK L LB m_pre).
  { eapply (hf_frame _ HL L LB m m_pre); [exact HFK | exact MUall | exact WMall |].
    unfold fake_untouched. pose proof (ao_t L ALO) as OT. unfold aobj in OT.
    assert (SHF : 2148238848 <= shad (al_fake L) /\ shad (al_fake L) + shlen 11571200 <= 17594332446720   (* [comment removed for export] *)
                  /\ (shad (al_space_beg L + c * 4294967296) + 536870912 <= shad (al_fake L)
                      \/ shad (al_fake L) + shlen 11571200 <= shad (al_space_beg L + c * 4294967296 + mu0))
                  /\ shad (al_space_beg L + c * 4294967296) <= shad (al_space_beg L + c * 4294967296 + mu0)
                  /\ 2201439137792 <= shad (al_space_beg L + c * 4294967296)).
    { rewrite !shad_div, !shlen_div. unfold ASHOFF in *. destruct PF as (_ & _ & (F1 & F2 & F3 & F4 & F5 & F6) & _).
      clear -FKO F1 F2 F3 F4 F5 F6 D_f_res RSP OFKi OFKs OFKsa OFKsb. Z.div_mod_to_equations. dlia. }
    (nd_pre SHF 5%nat; intros SF1 SF2 SF3 SF4 SF5; nd_post).
    unfold AMALLOC_STACK, AINSTANCE in *. destruct PF as (PF1 & PF2 & PF3 & PF4).
    repeat (apply Forall_cons; [cbn [fst snd];
      clear -LO BOT STK3 SP47 STK2 OT FKO ORS RSP ODT D_f_res D_t_f D_d_res D_t_d C16 PF3 PF4 SF1 SF2 SF3 SF4 SF5 SHHI TL1 TL2 SP1 TBND TBNDa TBNDb TIMG TIMGa TIMGb OFKi OFKs OFKsa OFKsb DBND DBNDa DBNDb DIMG DIMGa DIMGb;
      repeat (split; [fu_lia|]); fu_lia |]).   (* [comment removed for export] *)
    apply Forall_nil. }
  (* [comment removed for export] *)
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
    all: try (lazymatch goal with |- tclr _ _ => first [exact XTAB | tclr_solve ALO ltac:(fail)] end).      (* [comment removed for export] *)
    all: match goal with |- ?G => idtac "REMT" G end. }
  (* [comment removed for export] *)
  cbv beta. intros ms' PM.
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
End Zd1.
#[using="HL CI_OK CI_OK2"] Theorem amalloc_prim : ltac:(let t := eval cbv delta [amalloc_prim__stmt] in amalloc_prim__stmt in exact t).
Proof. exact amalloc_prim__body. Qed.
End S.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Exec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.ATlsKit.TwB.   (* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepExt.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepExt2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.APrimFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.F_aalloc1.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agbb__A3W.F_aalloc2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc__A3W.F_aalloc.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc__A3W.F_amalloc_icpt.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3g0__A3W.F_amalloc_pre.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agbb__A3W.F_aalloc2g.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3g.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3g0__A3W.F_amalloc_tailg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_amalloc_arep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepStore__A3W.ARepStore.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepStoreG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.ARefill_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARefillP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ACallocG__A3W.ACallocG.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac fu_drop_fake := repeat match goal with H : context [al_fake _] |- _ => clear H end.
Ltac fu_drop_dtls := repeat match goal with H : context [al_dtls _] |- _ => clear H end.
Ltac fu_drop_tls := repeat match goal with H : context [ATPv] |- _ => clear H | H : context [kt_img] |- _ => clear H end.
Ltac fu_focus :=
  lazymatch goal with
  | |- context [al_fake _] => fu_drop_dtls; fu_drop_tls
  | |- context [al_dtls _] => fu_drop_fake; fu_drop_tls
  | |- context [ATPv] => fu_drop_fake; fu_drop_dtls
  | |- _ => fu_drop_fake; fu_drop_dtls; fu_drop_tls
  end.
Ltac fu_lia := first [solve [fu_focus; lia] | lia].
(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
(* [comment removed for export] *)
#[using="Type"] Local Lemma ablk_int : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6307840 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
#[using="Type"] Local Lemma aobj_int : forall a n, aobj a n -> 0x10000 <= n ->
  6307840 <= a /\ a + n <= ATOP /\ exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof.
  intros a n H Hn. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. (nd_pre H 5%nat; intros H1 H2 H3 H4 H5; nd_post).
  split; [lia|]. split; [lia|]. destruct H4; [exists 0 | exists 1]; lia.
Qed.
#[using="Type"] Local Lemma aobj4_int : forall a, aobj a 4096 ->
  4096 <= a /\ a + 4096 <= ATOP
  /\ (exists k, 0 <= k <= 1 /\ a + 4096 <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a)
  /\ (exists j, 0 <= j <= 1 /\ a + 4096 <= 65536 + j * 18446744073709551616 /\ 6307840 * j <= a).
Proof.
  intros a H. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. (nd_pre H 5%nat; intros H1 H2 H3 H4 H5; nd_post).
  split; [lia|]. split; [lia|]. split; [destruct H4; [exists 0 | exists 1]; lia | destruct H5 as [_ [H5|H5]]; [exists 0 | exists 1]; lia].
Qed.
(* [comment removed for export] *)
Local Ltac dlia := repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
#[using="Type"] Lemma amalloc_prim_eq : forall RESV st n c,
  1 <= n -> is_primary n = true -> class_id (needed_size n) = c ->
  amalloc ATOP RESV st n =
    cache_alloc st c (fun st1 (ok : bool) =>
      if ok then SRet (set_next (N.succ (a_next st1)) (set_live (<[ a_next st1 := CPrim c n ]> (a_live st1)) st1), Some (a_next st1))
      else SRet (st1, None)).
Proof.
  intros RESV st n c N PRIM HC. (pose proof (prim_facts n N PRIM) as ndP__; nd_pre ndP__ 8%nat; intros NS RZR RZE RZM RLR RSR RSM NSR; nd_post).
  unfold amalloc.
  replace (2 ^ 40 <? n) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (2 ^ 40 <? needed_size n) with false by (symmetry; apply Z.ltb_ge; lia). cbn [orb].
  rewrite PRIM, HC. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma slot_carveG : forall m AB S n rz,
  junk_at m AB S -> (rz = 16 \/ 32 <= rz) -> 0 <= n -> rz + n <= S ->
  exists b0 b1 szh szl ctxj uj (j1 j2 : word),
       rw_cells asegs m (AB + rz + -16) [C1 (Z_to_bv 8 b0); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 szh); C4 (Z_to_bv 64 szl); C8 (Z_to_bv 64 ctxj)]
    /\ 0 <= b1 < 256
    /\ rw_cells asegs m (AB + rz) [CB (Z.to_nat n) uj]
    /\ (16 < rz -> rw_cells asegs m AB [C8 j1; C8 j2] /\ junk_at m (AB + 16) (rz - 32))
    /\ junk_at m (AB + rz + n) (S - rz - n).
Proof.
  intros m AB S n rz JK RZ N FIT.
  destruct (Z.eq_dec rz 16) as [->|NE].
  - destruct (junk_split m AB 16 (S - 16) ltac:(replace (16 + (S - 16)) with S by lia; exact JK) ltac:(lia) ltac:(lia)) as [HJ R1].
    destruct (junk_split m (AB + 16) n (S - 16 - n) ltac:(replace (n + (S - 16 - n)) with (S - 16) by lia; exact R1) ltac:(lia) ltac:(lia)) as [[uj UJ] TL].
    (nd_pre (hdr_of_junk m AB HJ) 8%nat; intros b0 b1 szh szl ctxj HDR B0 B1; nd_post).
    exists b0, b1, szh, szl, ctxj, uj, w0, w0.
    replace (AB + 16 + -16) with AB by lia. split; [exact HDR|]. split; [exact B1|]. split; [exact UJ|].
    split; [intros; exfalso; lia|]. exact TL.
  - assert (RZ2 : 32 <= rz) by lia.
    destruct (junk_split m AB 16 (S - 16) ltac:(replace (16 + (S - 16)) with S by lia; exact JK) ltac:(lia) ltac:(lia)) as [LHJ R1].
    destruct (junk_split m (AB + 16) (rz - 32) (S - rz + 16) ltac:(replace (rz - 32 + (S - rz + 16)) with (S - 16) by lia; exact R1) ltac:(lia) ltac:(lia)) as [MID R2].
    destruct (junk_split m (AB + 16 + (rz - 32)) 16 (S - rz) ltac:(replace (16 + (S - rz)) with (S - rz + 16) by lia; exact R2) ltac:(lia) ltac:(lia)) as [HJ R3].
    destruct (junk_split m (AB + 16 + (rz - 32) + 16) n (S - rz - n) ltac:(replace (n + (S - rz - n)) with (S - rz) by lia; exact R3) ltac:(lia) ltac:(lia)) as [[uj UJ] TL].
    (nd_pre (hdr_of_junk m _ HJ) 8%nat; intros b0 b1 szh szl ctxj HDR B0 B1; nd_post).
    (nd_pre (c8c8_of_junk m AB LHJ) 3%nat; intros j1 j2 LH; nd_post).
    exists b0, b1, szh, szl, ctxj, uj, j1, j2.
    replace (AB + 16 + (rz - 32)) with (AB + rz + -16) in HDR by lia.
    replace (AB + 16 + (rz - 32) + 16) with (AB + rz) in UJ, TL by lia.
    split; [exact HDR|]. split; [exact B1|]. split; [exact UJ|]. split; [intros _; split; [exact LH| exact MID]|]. exact TL.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma malloc_post_gen_shift : forall DI L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc n t c cnt AB UB PG pgw lo b1 maxc csz uj m0 m1 ms',
  malloc_post_gen DI L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc n t c cnt AB UB PG pgw lo b1 maxc csz uj m1 ms' ->
  munch [(bv_unsigned sp - 4096, bv_unsigned sp); (t + 208 + c * 80, t + 208 + c * 80 + 4); (t + 2784, t + 2792)]%Z m0 m1 -> wmono asegs m0 m1 ->
  malloc_post_gen DI L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc n t c cnt AB UB PG pgw lo b1 maxc csz uj m0 ms'.
Proof.
  intros until ms'. intros PM MU0 WM0. unfold malloc_post_gen in *.
  (nd_pre PM 21%nat; intros id t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' sj' stj' E MU REST; nd_post).
  exists id, t0, t1, t2, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m', sj', stj'. split; [exact E|]. split; [| split; [eapply wmono_trans; [exact WM0 | exact (proj1 REST)] | exact (proj2 REST)]].
  eapply munch_trans; [eapply munch_weaken; [| exact MU0] | exact MU]. unfold sub_fp. cbn [outside]. intros q Hq. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma amalloc_post_shiftG : forall CI AHEAP L RNG RNG1 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st st' LB n lo m m_pre r RNG2 ms',
  amalloc_post CI AHEAP L RNG1 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st' LB n lo m_pre r RNG2 ms' ->
  fp_le RNG RNG1 -> aheap_pres CI LB (bv_unsigned sp) m m_pre ->
  amalloc_post CI AHEAP L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB n lo m r RNG2 ms'.
Proof.
  intros until ms'. intros PM LE PRES. unfold amalloc_post in *.
  (nd_pre PM 22%nat; intros FP t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' E MI ST PR REST; nd_post).
  split; [eapply fp_le_trans; [exact LE | exact FP]|].
  exists t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m'. split; [exact E|]. split; [exact MI|]. split; [exact ST|].
  split; [eapply aheap_pres_trans; [exact PRES | exact PR] | exact REST].
Qed.

#[using="Type"] Lemma ablocks_xbusyG : forall L st st' X X' LB, ablocks L st X LB -> x_busy X' = x_busy X -> a_live st' = a_live st -> ablocks L st' X' LB.
Proof. intros. eapply ablocks_same; eassumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Pres.
Variables (sp t SB c mu ACL lo : Z).
(* [comment removed for export] *)
Notation Wp := ([(sp - 4096, sp); (t + 208, t + 3169); (AINSTANCE, AINSTANCE + 728); (SB + 137438953472 + c * 128, SB + 137438953472 + c * 128 + 128);
                 (SB + c * 4294967296 + mu, SB + c * 4294967296 + 4294967296);
                 (shad (SB + c * 4294967296 + mu), shad (SB + c * 4294967296) + 536870912)]%Z) (only parsing).
Definition pfactsG : Prop :=
     (ACL = ATOP /\ ACL <= lo /\ lo <= sp - 4096 /\ sp <= 2^47)
  /\ (4096 <= t /\ t + 4096 <= ACL /\ (t + 4096 <= 2147446784 \/ 17594333495296 <= t) /\ (t + 4096 <= 65536 \/ 6307840 <= t))   (* [comment removed for export] *)
  /\ (17594333495296 <= SB /\ SB + 137438957568 <= ACL /\ SB mod 65536 = 0 /\ 1 <= c <= 31 /\ 0 <= mu <= 3758096384 /\ mu mod 8 = 0)
  /\ (t + 4096 <= SB \/ SB + 137438957568 <= t).
Hypothesis PF : pfactsG.

#[using="rc ACL lo PF"] Lemma Q_stack : forall A k, sp <= A -> 0 <= k -> disjoint_from Wp A k.
Proof. intros. (pose proof PF as ndP__; nd_pre ndP__ 4%nat; intros F1 F2 F3 F4; nd_post). unfold AINSTANCE in *. cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF. repeat split; try exact I; Z.div_mod_to_equations; lia. Qed.
#[using="rc ACL lo PF"] Lemma Q_img : forall A k, 0x10000 <= A -> 0 <= k -> A + k <= 6307840 -> (A + k <= AINSTANCE \/ AINSTANCE + 728 <= A) -> disjoint_from Wp A k.   (* [comment removed for export] *)
Proof. intros. (pose proof PF as ndP__; nd_pre ndP__ 4%nat; intros F1 F2 F3 F4; nd_post). unfold AINSTANCE in *. cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF. repeat split; try exact I; Z.div_mod_to_equations; lia. Qed.
(* [comment removed for export] *)
#[using="rc ACL lo PF"] Lemma Q_slot : forall A k, SB <= A -> 0 <= k -> A + k <= SB + 137438953472 ->
  (A + k <= SB + c * 4294967296 + mu \/ SB + c * 4294967296 + 4294967296 <= A) -> disjoint_from Wp A k.
Proof. intros. (pose proof PF as ndP__; nd_pre ndP__ 4%nat; intros F1 F2 F3 F4; nd_post). unfold AINSTANCE in *. cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF. repeat split; try exact I; Z.div_mod_to_equations; lia. Qed.
#[using="rc lo PF"] Lemma Q_obj : forall A k, ((6307840 <= A /\ A + k <= 2147446784) \/ 17594333495296 <= A) -> 0 <= k -> A + k <= ACL ->   (* [comment removed for export] *) (A + k <= t \/ t + 4096 <= A) -> (A + k <= SB \/ SB + 137438957568 <= A) -> disjoint_from Wp A k.
Proof. intros. (pose proof PF as ndP__; nd_pre ndP__ 4%nat; intros F1 F2 F3 F4; nd_post). unfold AINSTANCE in *. cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF. repeat split; try exact I; Z.div_mod_to_equations; lia. Qed.
(* [comment removed for export] *)
#[using="rc lo PF"] Lemma Q_shad_hi : forall a, ACL <= a < 2^47 -> disjoint_from Wp (shad a) 1.
Proof. intros. (pose proof PF as ndP__; nd_pre ndP__ 4%nat; intros F1 F2 F3 F4; nd_post). unfold AINSTANCE in *. cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF. repeat split; try exact I; Z.div_mod_to_equations; lia. Qed.
#[using="rc ACL lo PF"] Lemma Q_shad_img : forall a, 0x10000 <= a < 6307840 -> disjoint_from Wp (shad a) 1.   (* [comment removed for export] *)
Proof. intros. (pose proof PF as ndP__; nd_pre ndP__ 4%nat; intros F1 F2 F3 F4; nd_post). unfold AINSTANCE in *. cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF. repeat split; try exact I; Z.div_mod_to_equations; lia. Qed.
#[using="rc lo PF"] Lemma Q_shad_obj : forall a, ((6307840 <= a /\ a + 1 <= 2147446784) \/ 17594333495296 <= a) -> a < ACL -> (a + 1 <= SB \/ SB + 137438957568 <= a) -> disjoint_from Wp (shad a) 1.   (* [comment removed for export] *)
Proof. intros. (pose proof PF as ndP__; nd_pre ndP__ 4%nat; intros F1 F2 F3 F4; nd_post). unfold AINSTANCE in *. cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF. repeat split; try exact I; Z.div_mod_to_equations; lia. Qed.
(* [comment removed for export] *)
#[using="rc lo PF"] Lemma Q_objL : forall A k, ((A + k <= 65536 \/ 6307840 <= A) /\ (A + k <= 2147446784 \/ 17594333495296 <= A)) -> 0 <= k -> A + k <= ACL ->
  (A + k <= t \/ t + 4096 <= A) -> (A + k <= SB \/ SB + 137438957568 <= A) -> disjoint_from Wp A k.
Proof. intros. (pose proof PF as ndP__; nd_pre ndP__ 4%nat; intros F1 F2 F3 F4; nd_post). unfold AINSTANCE in *. cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF. repeat split; try exact I; Z.div_mod_to_equations; lia. Qed.
#[using="rc lo PF"] Lemma Q_shad_objL : forall a, 0 <= a -> a < ACL -> (a + 1 <= SB \/ SB + 137438957568 <= a) -> disjoint_from Wp (shad a) 1.
Proof. intros. (pose proof PF as ndP__; nd_pre ndP__ 4%nat; intros F1 F2 F3 F4; nd_post). unfold AINSTANCE in *. cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF. repeat split; try exact I; Z.div_mod_to_equations; lia. Qed.
#[using="rc ACL lo PF"] Lemma Q_imsh : forall A k, 2147450880 <= A -> A + k <= 2148239360 -> 0 <= k -> disjoint_from Wp A k.      (* [comment removed for export] *)
Proof. intros. (pose proof PF as ndP__; nd_pre ndP__ 4%nat; intros F1 F2 F3 F4; nd_post). unfold AINSTANCE in *. cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF. repeat split; try exact I; Z.div_mod_to_equations; lia. Qed.
End Pres.

Section S.
Variable DI : ADepotIface.
Variables (AQ ASEC : alayout -> astate -> aconc -> amem -> Prop) (AFK : alayout -> list ablock -> amem -> Prop).
Hypothesis HL : ahole_laws (AH DI AQ ASEC AFK).
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI) CI.
(* [comment removed for export] *)
Hypothesis CI_OK2 : Forall (fun iv => snd iv <= AINSTANCE \/ AINSTANCE + 728 <= fst iv) CI.

Definition amalloc_prim__stmt : Prop := forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (n lo : Z) (tr : list Z) (RESV : list (Z * Z)),
  (* [comment removed for export] *)
  is_primary n = true ->
  (* [comment removed for export] *)
  AHEAP_P (AH DI AQ ASEC AFK) L RNG st LB m ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AMALLOC_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 n -> 1 <= n <= AREQMAX ->
  aunw m L RNG lo AMALLOC_PC sp s0 ra tr ->
  bv_unsigned s0 <> bv_unsigned sp + 8 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AMALLOC_PC ->
  bv_unsigned sp mod 16 = 0 ->
  rng RNG lo (bv_unsigned sp - lo) ->
  aresv_ok L RESV ->
  implS asegs RNG (aembed ATOP (amalloc ATOP RESV st n))
        (epostF (amalloc_post CI (AHEAP_P (AH DI AQ ASEC AFK)) L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB n lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AMALLOC_SYM) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'amalloc_prim__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'amalloc_prim__stmt 1).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'amalloc_prim__stmt 2).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'amalloc_prim__stmt 3).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'amalloc_prim__stmt 4).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'amalloc_prim__stmt 5).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'amalloc_prim__stmt 6).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'amalloc_prim__stmt 7).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'amalloc_prim__stmt 8).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'amalloc_prim__stmt 9).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'amalloc_prim__stmt 10).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'amalloc_prim__stmt 11).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'amalloc_prim__stmt 12).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'amalloc_prim__stmt 13).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'amalloc_prim__stmt 14).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'amalloc_prim__stmt 15).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'amalloc_prim__stmt 16).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'amalloc_prim__stmt 17).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'amalloc_prim__stmt 18).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'amalloc_prim__stmt 19).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'amalloc_prim__stmt 20).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'amalloc_prim__stmt 21).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'amalloc_prim__stmt 22).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'amalloc_prim__stmt 23).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'amalloc_prim__stmt 24).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'amalloc_prim__stmt 25).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'amalloc_prim__stmt 26).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'amalloc_prim__stmt 27).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'amalloc_prim__stmt 28).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'amalloc_prim__stmt 29).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'amalloc_prim__stmt 30).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'amalloc_prim__stmt 31).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'amalloc_prim__stmt 32).
Variable F : ltac2:(SecDietF.SzSecF.ty 'amalloc_prim__stmt 33).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'amalloc_prim__stmt 34).
Variable m : ltac2:(SecDietF.SzSecF.ty 'amalloc_prim__stmt 35).
Variable st : ltac2:(SecDietF.SzSecF.ty 'amalloc_prim__stmt 36).
Variable LB : ltac2:(SecDietF.SzSecF.ty 'amalloc_prim__stmt 37).
Variable n : ltac2:(SecDietF.SzSecF.ty 'amalloc_prim__stmt 38).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'amalloc_prim__stmt 39).
Variable tr : ltac2:(SecDietF.SzSecF.ty 'amalloc_prim__stmt 40).
Variable RESV : ltac2:(SecDietF.SzSecF.ty 'amalloc_prim__stmt 41).
#[using="HL CI_OK CI_OK2"] Lemma amalloc_prim__body : ltac:(let T := type of (fun (h : amalloc_prim__stmt) => h L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st LB n lo tr RESV) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (st, (LB, (n, (lo, (tr, RESV)))))))))))))))))))))))))))))))))))))))))) as _.
 intros PRIM AHP MI ST BOT LO TP Ha0 NR AUNW S0NE RA4 RANE SP16 RSTK ROK.
  assert (N : 1 <= n <= AREQMAX) by exact NR. assert (N1 : 1 <= n) by (clear -NR; lia).
  (* [comment removed for export] *)
  assert (EXARM : exists trc,
      ((bv_unsigned sp + 16 < al_top L /\ uchain m (al_top L) AMALLOC_PC (bv_unsigned sp) (bv_unsigned s0) 28%nat tr /\ (length tr <= 28)%nat /\ trc = bv_unsigned ra :: tr
        /\ rng RNG lo (al_top L - lo))
       \/ (al_top L <= bv_unsigned sp + 16 /\ bv_unsigned sp < 2^47 /\ trc = []))
      /\ In (AMALLOC_PC :: trc) (al_U L) /\ (length trc <= 29)%nat /\ bv_unsigned sp < 2^47).
  { (pose proof (alayout_stack L (proj1 AHP)) as ndP__; nd_pre ndP__ 3%nat; intros K1 K2 K3; nd_post).
    destruct AUNW as [(T1 & U1 & L1 & I1 & R1)|(T1 & T2 & I1)].
    - exists (bv_unsigned ra :: tr). split; [left; split; [exact T1|]; split; [exact U1|]; split; [exact L1|]; split; [reflexivity| exact R1]|].
      split; [exact I1|]. split; [cbn [length]; clear -L1; lia | clear -T1 K2; lia].
    - exists (@nil Z). split; [right; split; [exact T1|]; split; [exact T2| reflexivity]|]. split; [exact I1|]. split; [cbn [length]; clear; lia | exact T2]. }
  (nd_pre EXARM 5%nat; intros trc ARM TRU LTRC SP47; nd_post).
  (nd_pre AHP 4%nat; intros ALO ARNG [X [AR BL]] HFK; nd_post).
  remember (class_id (needed_size n)) as c eqn:HC0. symmetry in HC0.
  (pose proof (prim_facts n N1 PRIM) as ndP__; nd_pre ndP__ 8%nat; intros NS RZR RZE RZM RLR RSR RSM NSR; nd_post).
  (pose proof (prim_class_facts n c N1 PRIM HC0) as ndP__; nd_pre ndP__ 5%nat; intros C16 NSZ SM16 SMALL MCB; nd_post). clear SMALL.
  (pose proof (cls_facts c C16) as ndP__; nd_pre ndP__ 4%nat; intros SZB _ _ _; nd_post).
  assert (HCK : 1 <= c < K_NUM_CLASSES) by (unfold K_NUM_CLASSES; clear -C16; lia).
  assert (NM8 : needed_size n mod 8 = 0) by (rewrite NS; clear -RSM RZM; Z.div_mod_to_equations; lia).
  (* [comment removed for export] *)
  pose proof AR as AR0. (nd_pre AR0 12%nat; intros WF RT INST THR CLS HQ HS HD HRO RT2 AVL RT3; nd_post).
  (nd_pre THR 6%nat; intros T0 T40 CACHES CSTATS [sj [STATS LSJ]] UNW; nd_post).
  pose proof WF as WF0. (nd_pre WF0 11%nat; intros SBE PAE SAL SLO SHI PERC OUTC BUSY LIVE FRESH UNIQ; nd_post).
  (nd_pre (PERC c HCK) 12%nat; intros A1 A2 A3 A4 A5 A6 A7 LENF LENC CNTB ND RANGE; nd_post).
  (pose proof (alayout_space L ALO) as ndP__; nd_pre ndP__ 4%nat; intros SP1 SP2 SP3 SP4; nd_post).
  (pose proof (alayout_t L ALO) as ndP__; nd_pre ndP__ 4%nat; intros TL1 TL2 TL3 TL4; nd_post).
  (pose proof (alayout_ctx L ALO) as ndP__; nd_pre ndP__ 5%nat; intros CL1 CL2 CL3 CL4 CL5; nd_post).
  (pose proof (alayout_depot L ALO) as ndP__; nd_pre ndP__ 10%nat; intros DL1 DL2 DL3 DL4 DL5 DL6 DL7 DL8 DL9 DL10; nd_post).
  (pose proof (aobj4_int _ (ao_t L ALO)) as ndP__; nd_pre ndP__ 4%nat; intros _ _ (kT & TBND & TBNDa & TBNDb) (jT & TIMG & TIMGa & TIMGb); nd_post).   (* [comment removed for export] *)
  (pose proof (aobj_int _ _ (ao_ctx L ALO) ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros CTXi _ (kC & CBND & CBNDa & CBNDb); nd_post).
  (pose proof (aobj_int _ _ (ao_nodes L ALO) ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros NODi _ (kN & NBND & NBNDa & NBNDb); nd_post).
  (pose proof (aobj_int _ _ (ao_store L ALO) ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros STOi _ (kR & SBND & SBNDa & SBNDb); nd_post).
  (pose proof (aobj_int _ _ (ao_fake L ALO) ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros OFKi _ (kF & OFKs & OFKsa & OFKsb); nd_post).
  (pose proof (aobj4_int _ (ao_dtls L ALO)) as ndP__; nd_pre ndP__ 4%nat; intros _ _ (kD & DBND & DBNDa & DBNDb) (jD & DIMG & DIMGa & DIMGb); nd_post).
  (pose proof (alayout_stack L ALO) as ndP__; nd_pre ndP__ 3%nat; intros STK1 STK2 STK3; nd_post).
  pose proof (alayout_res_disj L ALO) as [SCX TSP].
  pose proof RT as RT0.
  (nd_pre RT0 28%nat; intros GPG GOT GOT80 RIC LS1 REAL IMAX4 FLG5 FLG HPP SHB CANP TI TK INI2 LAY MCS OOM3 PGC HK2 CF8 CF34 CSMT T88 TSD LS2 CT8 CT; nd_post).
  pose proof INI2 as INI. rw_split INI 1%nat INI1 INIx. clear INIx.
  pose proof OOM3 as OOM. rw_split OOM 2%nat OOMx RSS. clear OOMx.
  pose proof IMAX4 as IMAX. rw_split IMAX 3%nat IMAX3 IMAXx. clear IMAXx.
  pose proof T0 as TT0. rw_split TT0 1%nat TTctx TT.
  pose proof ARNG as ARNG0. (nd_pre ARNG 10%nat; intros RIMG RT4 RCTX RNO RSTO RRI RFK RSFK RDTLS RCLS; nd_post).
  assert (RTLS : rng_atls RNG) by ((nd_pre ARNG0 14%nat; intros _ _ _ _ _ _ _ _ _ _ _ _ _ RTLSx; nd_post); exact RTLSx).      (* [comment removed for export] *)
  assert (RCTX4 : rng RNG (al_ctx L) 4096) by (eapply rng_sub'; [exact RCTX|]; clear; lia).
  word_range sp SPR.
  box CL5. box DL7. box DL8. box DL9. box DL10. box TSP. box SCX.
  (* [comment removed for export] *)
  rewrite (amalloc_prim_eq RESV st n c N1 PRIM HC0).
  (* [comment removed for export] *)
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
  (nd_pre P4 24%nat; intros spA t0c t1c t2c a4c a5c a6c a7c t3c t4c t5c t6c s0A s1A s2A s3A s4A s5A s0i fr0 junk2 tb m4 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 13%nat; intros HspA MU4 WM4 MI4 ST4 FRa FR16 SS TB LTB TRF FRS UW4; nd_post).
  apply evtF_done.
  assert (AR4 : AREP (AH DI AQ ASEC AFK) L st X m4).
  { eapply (AREP_frame_pre _ HL L st X m m4); [exact ALO | exact AR | exact MU4 | exact WM4 | | exact UW4].
    apply Forall_cons; [unfold apre; cbn [fst snd]; intros _; left; unfold AMALLOC_STACK in *; clear -LO BOT STK3; lia|].
    apply Forall_cons; [unfold apre; cbn [fst snd]; intros _; right; split; reflexivity| apply Forall_nil]. }
  (* [comment removed for export] *)
  eapply (@calloc_arep_gen _ _ _ HL _ _ _ L RNG _ _ gp tp t0c t1c t2c _ _ _ _ _ _ a4c a5c a6c a7c _ _ _ _ _ _ _ _ _ _ t3c t4c t5c t6c F fc m4 st X c lo (needed_size n)
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
       end.
  (* [comment removed for export] *)
  intros st_pre X_pre RNG1 m_pre cnt k ms1 CRET. unfold calloc_retG in CRET.
  (nd_pre CRET 37%nat; intros FPLE ARp ARNGp HCNT POS NK NB KR XB L1 L2 L3 L4 L5 L6 L7 L8 MUc WMc MIp t0d t1d t2d a1d a2d a3d a4d a5d a6d a7d t3d t4d t5d t6d m1 stj1 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 6%nat; intros MU1 WM1 MI1 ST1 CR1 STS1; nd_post).
  rewrite ?unsigned_lit in MUc by (clear -SPR HspA LO BOT STK3; unfold AMALLOC_STACK in *; lia).
  rewrite ?unsigned_lit in MU1 by (clear -SPR HspA LO BOT STK3; unfold AMALLOC_STACK in *; lia).
  rewrite ?unsigned_lit in ST1 by (clear -SPR HspA LO BOT STK3; unfold AMALLOC_STACK in *; lia).
  replace (bv_unsigned spA + -128) with (bv_unsigned sp - 2272) in ST1 by (clear -HspA; lia).
  cbn beta iota. apply implS_ret.
  replace (ret_pc (Z_to_bv 64 0x33f10)) with (Z_to_bv 64 0x33f10) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  (* [comment removed for export] *)
  pose proof ARp as AR0. (nd_pre AR0 12%nat; intros WF' RT' INST' THR' CLS' HQ' HS' HD' HRO' RT2' AVL' RT3'; nd_post).
  (nd_pre THR' 6%nat; intros T0' T40' CACHES' CSTATS' [sj' [STATS' LSJ']] UNW'; nd_post).
  pose proof WF' as WF0. (nd_pre WF0 11%nat; intros SBE' PAE' SAL' SLO' SHI' PERC' OUTC' BUSY' LIVE' FRESH' UNIQ'; nd_post).
  (nd_pre (PERC' c HCK) 12%nat; intros B1' B2' B3' B4' B5' B6' B7' LENF' LENC' CNTB' ND' RANGE'; nd_post).
  (nd_pre (kit_cache_pop _ L st_pre X_pre m_pre c cnt ARp HCK HCNT POS) 11%nat; intros k' chunks NK' _ _ CR CH LCH NTH JK FSH; nd_post).
  assert (EK : k' = k) by (rewrite NK in NK'; injection NK'; intros E; symmetry; exact E). subst k'.
  (* [comment removed for export] *)
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
  (nd_pre KSF 3%nat; intros KS0 KS1 KS2; nd_post).
  assert (GEO : al_space_beg L <= AB /\ AB + S <= al_space_beg L + K_SPACE_SIZE /\ AB mod 16 = 0
                /\ AB + S <= aregion L c + c_allocated_user (get_cls st_pre c) /\ aregion L c <= AB).
  { subst AB. unfold aslot_addr, aregion, K_REGION, K_SPACE_SIZE, K_FREEARR_OFF, K_ALIGN in *. fold S.
    remember (k * S) as KS eqn:HKS. clear HKS.
    change (2^37) with 137438953472. change (2^32) with 4294967296 in *.
    split; [clear -KS0 C16; lia|]. split; [clear -KS1 B1' B2' C16 NSZ; lia|]. split; [| clear -KS0 KS1 B1'; lia].
    clear -SP3 C16 KS2. Z.div_mod_to_equations; lia. }
  (nd_pre GEO 5%nat; intros G1 G2 G3 G4 G5; nd_post). unfold K_SPACE_SIZE in G2. change (2^37) with 137438953472 in G2.
  assert (EAB : AB = aslot_addr L c k) by reflexivity. clearbody AB.
  assert (ES : S = size_of_class c) by reflexivity.
  (* [comment removed for export] *)
  assert (RZC : rz_size n = 16 \/ 32 <= rz_size n) by (clear -RZR RZM; Z.div_mod_to_equations; lia).
  (nd_pre (slot_carveG m_pre AB S n (rz_size n) JK RZC ltac:(clear -N; lia) ltac:(fold S in NSZ; clear -NSZ NS RSR; lia)) 13%nat; intros b0 b1 szh szl ctxj uj j1 j2 HDR B1 UJ LH TL; nd_post).
  set (UB := AB + rz_size n) in *. assert (EUB : UB = AB + rz_size n) by reflexivity. clearbody UB.
  (* [comment removed for export] *)
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
  (nd_pre (shadow_carve m_pre (shad AB) (shlen S) grz g room FSH GR3 GR4 GR6 GR5) 5%nat; intros SHA SHpre [sjunk SHU] SHP SHsuf; nd_post).
  rewrite <- GR7 in SHU, SHP, SHsuf.
  set (PG := shad UB + g) in *.
  (* [comment removed for export] *)
  pose proof RT' as RT0.
  (nd_pre RT0 28%nat; intros GPG' GOT' GOT80' RIC' LS1' REAL' IMAX4' FLG5' FLG' HPP' SHB' CANP' TI' TK' INI2' LAY' MCS' OOM3' PGC' HK2' CF8' CF34' CSMT' T88' TSD' LS2' CT8' CT'; nd_post).
  pose proof INI2' as INI'. rw_split INI' 1%nat INI1' INIx. clear INIx.
  pose proof OOM3' as OOM'. rw_split OOM' 2%nat OOMx RSS'. clear OOMx.
  pose proof IMAX4' as IMAX'. rw_split IMAX' 3%nat IMAX3' IMAXx. clear IMAXx.
  pose proof HK2' as HK'. rw_split HK' 1%nat HK1' HKx. clear HKx.
  pose proof T0' as TT0'. rw_split TT0' 1%nat TTctx' TT'.
  destruct (junk_split m_pre (al_t L + 2768) 16 16 CSTATS' ltac:(lia) ltac:(lia)) as [CSa CSb].
  destruct (junk_split m_pre (al_t L + 2768 + 16) 8 8 CSb ltac:(lia) ltac:(lia)) as [CS8 CSc].
  replace (al_t L + 2768 + 16) with (al_t L + 2784) in CS8 by lia.
  replace (al_t L + 2768 + 16 + 8) with (al_t L + 2792) in CSc by lia.
  (nd_pre INST' 9%nat; intros I32' I48' I64' I72' I112' I680' I984' I40' I56'; nd_post).
  pose proof ARNGp as ARNGp0. (nd_pre ARNGp 14%nat; intros RIMG' RT4' RCTX' RNO' RST' RRI' RFK' RSFK' RDTLS' RCLS' RPA' RSECS' RPSH' RTLS'; nd_post).
  (nd_pre (RCLS' c HCK) 4%nat; intros RREG RSREG RFA RSFA; nd_post).
  (* [comment removed for export] *)
  (nd_pre (alayout_slot_disj L AB 65536 ALO G1 ltac:(unfold K_SPACE_SIZE, K_FREEARR_OFF, aregion, K_REGION in *; generalize G4 B1' B2' C16 SP1 SZB; clear; intros; change (2^37) with 137438953472; lia) ltac:(clear; lia)) 5%nat; intros DJT DJC DJN DJS DJF; nd_post).
  (* [comment removed for export] *)
  assert (XTAB : tclr AB 65536).
  { apply (tclr_space L AB 65536 ALO); [exact G1|]. unfold K_SPACE_SIZE, K_FREEARR_OFF, aregion, K_REGION in *. generalize G4 B1' B2' C16 SP1 SZB; clear; intros. change (2^37) with 137438953472 in *. lia. }
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
  (* [comment removed for export] *)
  set (mu0 := c_mapped_user (get_cls st c)) in *.
  assert (OBJ : aregion_info L c = al_space_beg L + 137438953472 + c * 128 /\ aregion L c = al_space_beg L + c * 4294967296
                /\ shad (al_space_beg L + c * 4294967296) + 536870912 <= 17594333495296).
  { unfold aregion_info, aregion, K_REGION, K_SPACE_SIZE, ARI_STRIDE. change (2^37) with 137438953472. change (2^32) with 4294967296.
    split; [reflexivity|]. split; [reflexivity|]. rewrite shad_div. clear -SP1 SP2 C16. unfold ASHOFF, K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^37) with 137438953472 in *.
    Z.div_mod_to_equations. lia. }
  (nd_pre OBJ 3%nat; intros RIE RBE SHHI; nd_post).
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
  (* [comment removed for export] *)
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
  xport LS2' MU1 WM1 ltac:(clear -HspA SPR TL1 TL2 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport LAY' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport MCS' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport CF34' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport INI1' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport RSS' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport IMAX3' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport TI' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport TK' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport T88' MU1 WM1 ltac:(clear -HspA SPR TL1 TL2 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, ATP88, AMALLOC_STACK in *; lia).
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
  (* [comment removed for export] *)
  assert (PF : pfactsG (bv_unsigned sp) (al_t L) (al_space_beg L) c mu0 ATOP lo).
  { unfold pfactsG. pose proof (ao_t L ALO) as OT. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in OT.   (* [comment removed for export] *)
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
  (* [comment removed for export] *)
  assert (BB : forall b, In b (x_busy X) ->
      al_space_beg L <= xb_alloc L b /\ xb_alloc L b + size_of_class (xb_class b) <= al_space_beg L + 137438953472
      /\ (xb_alloc L b + size_of_class (xb_class b) <= al_space_beg L + c * 4294967296 + mu0 \/ al_space_beg L + c * 4294967296 + 4294967296 <= xb_alloc L b)).
  { intros b Hb. destruct (BUSY b Hb) as [CLB _].
    (nd_pre (PERC (xb_class b) CLB) 12%nat; intros Q1 Q2 _ _ _ _ _ _ _ _ _ QR; nd_post).
    pose proof (size_of_class_facts (xb_class b) CLB) as [QS _].
    assert (KB : 0 <= xb_slot b < ndist st (xb_class b)).
    { apply QR. apply in_app_iff. right. apply in_app_iff. right. unfold busy_slots. apply in_map_iff. exists b. split; [reflexivity|].
      apply filter_In. split; [exact Hb| apply Z.eqb_refl]. }
    (pose proof (slot_in_region L st (xb_class b) (xb_slot b) ltac:(clear -QS; lia) (proj1 Q1) KB) as ndP__; nd_pre ndP__ 3%nat; intros P5 P4 P0; nd_post).
    unfold xb_alloc. unfold K_NUM_CLASSES in CLB. unfold K_FREEARR_OFF in Q2.
    destruct (Z.eq_dec (xb_class b) c) as [EC|NC].
    - rewrite EC in P5, P4, Q1, Q2 |- *. rewrite RBE in P5, P4. change (c_mapped_user (get_cls st c)) with mu0 in Q1, Q2.
      clear -P5 P4 Q1 Q2 A1 A2 C16. unfold K_FREEARR_OFF in *. lia.
    - (pose proof (region_other_geo L c (xb_class b) ALO ltac:(clear -C16; lia) CLB NC) as ndP__; nd_pre ndP__ 4%nat; intros R1 R2 R3 _; nd_post). rewrite RBE in R2.
      clear -P5 P4 Q1 Q2 R1 R2 R3 A1. lia. }
  pose proof (ao_fake L ALO) as FKO. unfold aobj in FKO. pose proof (ao_res L ALO) as ORS. unfold aobj in ORS. pose proof (ao_space L ALO) as RSP.
  pose proof (ad_fake_res L ALO) as D_f_res. pose proof (ad_t_fake L ALO) as D_t_f. pose proof (ad_dtls_res L ALO) as D_d_res. pose proof (ad_t_dtls L ALO) as D_t_d.
  pose proof (ao_dtls L ALO) as ODT. unfold aobj in ODT. unfold adisj in D_f_res, D_t_f, D_d_res, D_t_d.
  assert (FKD : forall cls FA sz, In (mkABlock (ABFake cls) FA sz) LB -> al_fake L <= FA /\ 0 <= sz /\ FA + sz <= al_fake L + 11571200)
    by (intros cls FA sz Hin; exact (proj1 (proj2 BL) cls FA sz Hin)).
  assert (PRES : aheap_pres CI LB (bv_unsigned sp) m m_pre).
  { intros a Ha CL. split; [| intros Hw; apply WMall; exact Hw].
    apply MUall. rewrite wa_unsigned by exact Ha.
    destruct CL as [CL|TLSA].
    2:{ (* [comment removed for export] *)
        pose proof (ad_tls_t L ALO) as DLT. pose proof (ad_tls_res L ALO) as DLR. unfold adisj in DLT, DLR.
        pose proof atp_lin as TLN. pose proof atop_range as ATR0. pose proof atp_below_atop as TBA.
        destruct TLSA as [[T|(ta & Hta & ->)]|[IM|IM]].
        4:{ pose proof (ao_ahm L ALO) as OAH. pose proof (aobj_img _ _ OAH ltac:(clear; lia)) as OAHI. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in OAH, OAHI.
          rewrite <- (ao_ahm_eq L ALO) in IM. unfold AAHM_SZ in IM. pose proof (ad_ahm_t L ALO) as DA1. pose proof (ad_ahm_res L ALO) as DA2. unfold adisj in DA1, DA2.
            eapply disjoint_outside; [eapply (Q_obj _ _ _ _ _ _ _ PF a 1) | clear; lia]; clear -IM OAH OAHI DA1 DA2 RSP; lia. }
        3:{ unfold AIMSH_LO, AIMSH_LEN in IM. eapply disjoint_outside; [eapply (Q_imsh _ _ _ _ _ _ _ PF a 1) | clear; lia]; clear -IM; lia. }
        - eapply disjoint_outside; [eapply (Q_img _ _ _ _ _ _ _ PF a 1) | clear; lia]; pose proof ATPv_img as TPI; clear -T TPI; unfold AINSTANCE; lia.
        - eapply disjoint_outside; [eapply (Q_shad_objL _ _ _ _ _ _ _ PF ta) | clear; lia]; clear -Hta DLT DLR TLN ATR0 TBA RSP; lia. }
    destruct CL as [STa | [CIa | [BLK | SH]]].
    - eapply disjoint_outside; [eapply (Q_stack _ _ _ _ _ _ _ PF a 1); clear -STa; lia | clear; lia].
    - (nd_pre CIa 3%nat; intros iv Hiv R; nd_post). (pose proof (proj1 (Forall_forall _ _) CI_OK iv Hiv) as ndP__; nd_pre ndP__ 3%nat; intros Q1 Q2 Q3; nd_post).
      pose proof (proj1 (Forall_forall _ _) CI_OK2 iv Hiv) as Q4. cbn [fst snd] in *.
      eapply disjoint_outside; [eapply (Q_img _ _ _ _ _ _ _ PF a 1); unfold AIMG_HI in *; clear -R Q1 Q3 Q4; lia | clear; lia].
    - (nd_pre BLK 3%nat; intros b Hb R; nd_post). destruct b as [[p|cls] A n']; cbn [ab_addr ab_size] in R.
      + destruct (proj1 BL p A n' Hb) as [(xb & Hxb & Sb & Ub & Nb)|(mb0 & ms0 & Lp & EUA & Gs)].
        * (nd_pre (BB xb Hxb) 3%nat; intros Bb1 Bb2 Bb3; nd_post).
          pose proof (awf_fits L st X xb WF Hxb) as FIT. unfold xb_fits in FIT. rewrite Sb in FIT. unfold xb_user in Ub. subst A n'.
          eapply disjoint_outside; [eapply (Q_slot _ _ _ _ _ _ _ PF a 1) | clear; lia]; clear -R Bb1 Bb2 Bb3 FIT; lia.
        * (* [comment removed for export] *)
          cbn [sec_wf1] in Gs. (nd_pre Gs 7%nat; intros Gs1 Gs2 Gs3 Gs4 Gs5 Gs6 (Ct & Cc & Cr & Cp & Cn & Cs & Cf & Cd); nd_post).
          pose proof (sec_facts n' ltac:(clear -Gs5; lia) Gs6) as SF. subst A. unfold SEC_UOFF, K_HIGH_MEM in *.
          unfold ablk, KLS, AIMG_HI in Gs2.   (* [comment removed for export] *)
          eapply disjoint_outside; [eapply (Q_obj _ _ _ _ _ _ _ PF a 1) | clear; lia]; clear -R Gs2 Gs3 Gs4 Gs5 SF Ct Cr RSP ORS; lia.
      + (nd_pre (FKD cls A n' Hb) 3%nat; intros K1 K2 K3; nd_post). atop_facts.
        eapply disjoint_outside; [eapply (Q_obj _ _ _ _ _ _ _ PF a 1) | clear; lia];
          clear -R K1 K3 FKO D_t_f D_f_res RSP OFKi OFKs OFKsa OFKsb; lia.   (* [comment removed for export] *)
    - (nd_pre SH 3%nat; intros a' Ha' ndR1__; nd_post; revert ndR1__; intros ->).
      destruct Ha' as [STa | [CIa | FK]].
      + eapply disjoint_outside; [eapply (Q_shad_hi _ _ _ _ _ _ _ PF a'); unfold AMALLOC_STACK in *; clear -STa LO BOT STK3; lia | clear; lia].
      + (nd_pre CIa 3%nat; intros iv Hiv R; nd_post). (pose proof (proj1 (Forall_forall _ _) CI_OK iv Hiv) as ndP__; nd_pre ndP__ 3%nat; intros Q1 Q2 Q3; nd_post). cbn [fst snd] in *.
        eapply disjoint_outside; [eapply (Q_shad_img _ _ _ _ _ _ _ PF a'); unfold AIMG_HI in *; clear -R Q1 Q3; lia | clear; lia].
      + (nd_pre FK 5%nat; intros cls FA sz Hin R; nd_post). (nd_pre (FKD cls FA sz Hin) 3%nat; intros K1 K2 K3; nd_post). atop_facts.
        eapply disjoint_outside; [eapply (Q_shad_obj _ _ _ _ _ _ _ PF a') | clear; lia]; clear -R K1 K3 FKO D_f_res RSP OFKi OFKs OFKsa OFKsb; lia. }
  assert (HFKp : AFK L LB m_pre).
  { eapply (hf_frame _ HL L LB m m_pre); [exact HFK | exact MUall | exact WMall |].
    unfold fake_untouched. pose proof (ao_t L ALO) as OT. unfold aobj in OT.
    assert (SHF : 2148239360 <= shad (al_fake L) /\ shad (al_fake L) + shlen 11571200 <= 17594332446720   (* [comment removed for export] *)
                  /\ (shad (al_space_beg L + c * 4294967296) + 536870912 <= shad (al_fake L)
                      \/ shad (al_fake L) + shlen 11571200 <= shad (al_space_beg L + c * 4294967296 + mu0))
                  /\ shad (al_space_beg L + c * 4294967296) <= shad (al_space_beg L + c * 4294967296 + mu0)
                  /\ 2201439137792 <= shad (al_space_beg L + c * 4294967296)).
    { rewrite !shad_div, !shlen_div. unfold ASHOFF in *. destruct PF as (_ & _ & (F1 & F2 & F3 & F4 & F5 & F6) & _).
      clear -FKO F1 F2 F3 F4 F5 F6 D_f_res RSP OFKi OFKs OFKsa OFKsb. Z.div_mod_to_equations. dlia. }
    (nd_pre SHF 5%nat; intros SF1 SF2 SF3 SF4 SF5; nd_post).
    unfold AMALLOC_STACK, AINSTANCE in *. destruct PF as (PF1 & PF2 & PF3 & PF4).
    repeat (apply Forall_cons; [cbn [fst snd];
      clear -LO BOT STK3 SP47 STK2 OT FKO ORS RSP ODT D_f_res D_t_f D_d_res D_t_d C16 PF3 PF4 SF1 SF2 SF3 SF4 SF5 SHHI TL1 TL2 SP1 TBND TBNDa TBNDb TIMG TIMGa TIMGb OFKi OFKs OFKsa OFKsb DBND DBNDa DBNDb DIMG DIMGa DIMGb;
      repeat (split; [fu_lia|]); fu_lia |]).   (* [comment removed for export] *)
    apply Forall_nil. }
  (* [comment removed for export] *)
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
    all: try (lazymatch goal with |- tclr _ _ => first [exact XTAB | tclr_solve ALO ltac:(fail)] end).      (* [comment removed for export] *)
    all: match goal with |- ?G => idtac "REMT" G end. }
  (* [comment removed for export] *)
  cbv beta. intros ms' PM.
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
End Zd1.
#[using="HL CI_OK CI_OK2"] Theorem amalloc_prim : ltac:(let t := eval cbv delta [amalloc_prim__stmt] in amalloc_prim__stmt in exact t).
Proof. exact amalloc_prim__body. Qed.
End S.
End CANSEC1.
End TwB.
End AMallocPG.

(* [comment removed for export] *)
Module AAllocFnPG.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA StepF SysStepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.ATlsKit.   (* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecFacts AMalloc_iface. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitR__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepExt2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_apoison__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecSlog__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_agbb__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc3g0__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc3g. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_amalloc_arep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepStore__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepStoreG. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARealloc_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARefillP. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc1b__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepExt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepExt2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.APrimFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.F_aalloc1 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agbb__A3W.F_aalloc2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc__A3W.F_aalloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc__A3W.F_amalloc_icpt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3g0__A3W.F_amalloc_pre OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agbb__A3W.F_aalloc2g OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3g OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3g0__A3W.F_amalloc_tailg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_amalloc_arep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepStore__A3W.ARepStore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepStoreG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.ARefill_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARefillP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ACallocG__A3W.ACallocG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc1b__A3W.F_aalloc1b OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3g0__A3W.F_aallocfn_tailg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ACallocG__A3W.AMallocPG.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac fu_drop_fake := repeat match goal with H : context [al_fake _] |- _ => clear H end.
Ltac fu_drop_dtls := repeat match goal with H : context [al_dtls _] |- _ => clear H end.
Ltac fu_drop_tls := repeat match goal with H : context [ATPv] |- _ => clear H | H : context [kt_img] |- _ => clear H end.
Ltac fu_focus :=
  lazymatch goal with
  | |- context [al_fake _] => fu_drop_dtls; fu_drop_tls
  | |- context [al_dtls _] => fu_drop_fake; fu_drop_tls
  | |- context [ATPv] => fu_drop_fake; fu_drop_dtls
  | |- _ => fu_drop_fake; fu_drop_dtls; fu_drop_tls
  end.
Ltac fu_lia := first [solve [fu_focus; lia] | lia].
(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
(* [comment removed for export] *)
#[using="Type"] Local Lemma ablk_int : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6303744 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
#[using="Type"] Local Lemma aobj_int : forall a n, aobj a n -> 0x10000 <= n ->
  6303744 <= a /\ a + n <= ATOP /\ exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof.
  intros a n H Hn. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. (nd_pre H 5%nat; intros H1 H2 H3 H4 H5; nd_post).
  split; [lia|]. split; [lia|]. destruct H4; [exists 0 | exists 1]; lia.
Qed.
#[using="Type"] Local Lemma aobj4_int : forall a, aobj a 4096 ->
  4096 <= a /\ a + 4096 <= ATOP
  /\ (exists k, 0 <= k <= 1 /\ a + 4096 <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a)
  /\ (exists j, 0 <= j <= 1 /\ a + 4096 <= 65536 + j * 18446744073709551616 /\ 6303744 * j <= a).
Proof.
  intros a H. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. (nd_pre H 5%nat; intros H1 H2 H3 H4 H5; nd_post).
  split; [lia|]. split; [lia|]. split; [destruct H4; [exists 0 | exists 1]; lia | destruct H5 as [_ [H5|H5]]; [exists 0 | exists 1]; lia].
Qed.
(* [comment removed for export] *)
Local Ltac dlia := repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
Section S.
Variable DI : ADepotIface.
Variables (AQ ASEC : alayout -> astate -> aconc -> amem -> Prop) (AFK : alayout -> list ablock -> amem -> Prop).
Hypothesis HL : ahole_laws (AH DI AQ ASEC AFK).
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI) CI.
(* [comment removed for export] *)
Hypothesis CI_OK2 : Forall (fun iv => snd iv <= AINSTANCE \/ AINSTANCE + 728 <= fst iv) CI.

Definition allocfn_prim__stmt : Prop := forall (L : alayout) (RNG : footprint)
    (ra spA gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (n lo SO pc : Z) (trc : list Z) (tb : list word) (RESV : list (Z * Z)),
  (* [comment removed for export] *)
  is_primary n = true ->
  (* [comment removed for export] *)
  AHEAP_P (AH DI AQ ASEC AFK) L RNG st LB m ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned spA) -> ATOP + 4096 <= lo -> lo <= bv_unsigned spA - AMALLOC_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 AINSTANCE -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 8 -> a3 = Z_to_bv 64 SO -> a4 = Z_to_bv 64 1 -> a5 = Z_to_bv 64 1 ->
  1 <= n <= AREQMAX ->
  (* [comment removed for export] *)
  bv_unsigned spA <= SO -> SO + 2056 <= 2^47 -> bv_unsigned spA + 2144 < 2^47 ->
  rw_cells asegs m SO [C8 (Z_to_bv 64 (SO + 16)); C8 (Z_to_bv 64 (1 + Z.of_nat (length trc)))] ->
  u64arr asegs m (SO + 16) tb -> length tb = 255%nat ->
  map bv_unsigned (firstn (Datatypes.S (length trc)) tb) = pc :: trc ->
  In (pc :: trc) (al_U L) -> (length trc <= 29)%nat ->
  rng RNG lo (bv_unsigned spA - lo) -> rng RNG SO 2056 ->
  aresv_ok L RESV ->
  implS asegs RNG (aembed ATOP (amalloc ATOP RESV st n))
        (epostF (amalloc_post CI (AHEAP_P (AH DI AQ ASEC AFK)) L RNG ra spA gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB n lo m))
        (MS (mkR ra spA gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 allocate_entry) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'allocfn_prim__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'allocfn_prim__stmt 1).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'allocfn_prim__stmt 2).
Variable spA : ltac2:(SecDietF.SzSecF.ty 'allocfn_prim__stmt 3).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'allocfn_prim__stmt 4).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'allocfn_prim__stmt 5).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'allocfn_prim__stmt 6).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'allocfn_prim__stmt 7).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'allocfn_prim__stmt 8).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'allocfn_prim__stmt 9).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'allocfn_prim__stmt 10).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'allocfn_prim__stmt 11).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'allocfn_prim__stmt 12).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'allocfn_prim__stmt 13).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'allocfn_prim__stmt 14).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'allocfn_prim__stmt 15).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'allocfn_prim__stmt 16).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'allocfn_prim__stmt 17).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'allocfn_prim__stmt 18).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'allocfn_prim__stmt 19).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'allocfn_prim__stmt 20).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'allocfn_prim__stmt 21).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'allocfn_prim__stmt 22).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'allocfn_prim__stmt 23).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'allocfn_prim__stmt 24).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'allocfn_prim__stmt 25).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'allocfn_prim__stmt 26).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'allocfn_prim__stmt 27).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'allocfn_prim__stmt 28).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'allocfn_prim__stmt 29).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'allocfn_prim__stmt 30).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'allocfn_prim__stmt 31).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'allocfn_prim__stmt 32).
Variable F : ltac2:(SecDietF.SzSecF.ty 'allocfn_prim__stmt 33).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'allocfn_prim__stmt 34).
Variable m : ltac2:(SecDietF.SzSecF.ty 'allocfn_prim__stmt 35).
Variable st : ltac2:(SecDietF.SzSecF.ty 'allocfn_prim__stmt 36).
Variable LB : ltac2:(SecDietF.SzSecF.ty 'allocfn_prim__stmt 37).
Variable n : ltac2:(SecDietF.SzSecF.ty 'allocfn_prim__stmt 38).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'allocfn_prim__stmt 39).
Variable SO : ltac2:(SecDietF.SzSecF.ty 'allocfn_prim__stmt 40).
Variable pc : ltac2:(SecDietF.SzSecF.ty 'allocfn_prim__stmt 41).
Variable trc : ltac2:(SecDietF.SzSecF.ty 'allocfn_prim__stmt 42).
Variable tb : ltac2:(SecDietF.SzSecF.ty 'allocfn_prim__stmt 43).
Variable RESV : ltac2:(SecDietF.SzSecF.ty 'allocfn_prim__stmt 44).
#[using="HL CI_OK CI_OK2"] Lemma allocfn_prim__body : ltac:(let T := type of (fun (h : allocfn_prim__stmt) => h L RNG ra spA gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st LB n lo SO pc trc tb RESV) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (RNG, (ra, (spA, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (st, (LB, (n, (lo, (SO, (pc, (trc, (tb, RESV))))))))))))))))))))))))))))))))))))))))))))) as _.
 intros PRIM AHP MI STA BOT LOA TP Ha0 Ha1 Ha2 Ha3 Ha4 Ha5 NR SGE S47 SPV SS0 TB0 LTB TRF0 TRU LTRC RSTKA RS ROK.
  assert (N : 1 <= n <= AREQMAX) by exact NR. assert (N1 : 1 <= n) by (clear -NR; lia).
  (* [comment removed for export] *)
  word_range spA SPRA.
  pose (sp := Z_to_bv 64 (bv_unsigned spA + 2144)).
  assert (HspA : bv_unsigned spA = bv_unsigned sp - 2144) by (subst sp; rewrite unsigned_lit by (clear -SPRA SPV; lia); clear; lia).
  clearbody sp.
  assert (LO : lo <= bv_unsigned sp - AMALLOC_STACK) by (clear -LOA HspA; unfold AMALLOC_STACK in *; lia).
  assert (SP47 : bv_unsigned sp < 2^47) by (clear -SPV HspA; lia).
  assert (RA4 : True) by exact I.
  (nd_pre AHP 4%nat; intros ALO ARNG [X [AR BL]] HFK; nd_post).
  remember (class_id (needed_size n)) as c eqn:HC0. symmetry in HC0.
  (pose proof (prim_facts n N1 PRIM) as ndP__; nd_pre ndP__ 8%nat; intros NS RZR RZE RZM RLR RSR RSM NSR; nd_post).
  (pose proof (prim_class_facts n c N1 PRIM HC0) as ndP__; nd_pre ndP__ 5%nat; intros C16 NSZ SM16 SMALL MCB; nd_post). clear SMALL.
  (pose proof (cls_facts c C16) as ndP__; nd_pre ndP__ 4%nat; intros SZB _ _ _; nd_post).
  assert (HCK : 1 <= c < K_NUM_CLASSES) by (unfold K_NUM_CLASSES; clear -C16; lia).
  assert (NM8 : needed_size n mod 8 = 0) by (rewrite NS; clear -RSM RZM; Z.div_mod_to_equations; lia).
  (* [comment removed for export] *)
  pose proof AR as AR0. (nd_pre AR0 12%nat; intros WF RT INST THR CLS HQ HS HD HRO RT2 AVL RT3; nd_post).
  (nd_pre THR 6%nat; intros T0 T40 CACHES CSTATS [sj [STATS LSJ]] UNW; nd_post).
  pose proof WF as WF0. (nd_pre WF0 11%nat; intros SBE PAE SAL SLO SHI PERC OUTC BUSY LIVE FRESH UNIQ; nd_post).
  (nd_pre (PERC c HCK) 12%nat; intros A1 A2 A3 A4 A5 A6 A7 LENF LENC CNTB ND RANGE; nd_post).
  (pose proof (alayout_space L ALO) as ndP__; nd_pre ndP__ 4%nat; intros SP1 SP2 SP3 SP4; nd_post).
  (pose proof (alayout_t L ALO) as ndP__; nd_pre ndP__ 4%nat; intros TL1 TL2 TL3 TL4; nd_post).
  (pose proof (alayout_ctx L ALO) as ndP__; nd_pre ndP__ 5%nat; intros CL1 CL2 CL3 CL4 CL5; nd_post).
  (pose proof (alayout_depot L ALO) as ndP__; nd_pre ndP__ 10%nat; intros DL1 DL2 DL3 DL4 DL5 DL6 DL7 DL8 DL9 DL10; nd_post).
  (pose proof (aobj4_int _ (ao_t L ALO)) as ndP__; nd_pre ndP__ 4%nat; intros _ _ (kT & TBND & TBNDa & TBNDb) (jT & TIMG & TIMGa & TIMGb); nd_post).   (* [comment removed for export] *)
  (pose proof (aobj_int _ _ (ao_ctx L ALO) ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros CTXi _ (kC & CBND & CBNDa & CBNDb); nd_post).
  (pose proof (aobj_int _ _ (ao_nodes L ALO) ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros NODi _ (kN & NBND & NBNDa & NBNDb); nd_post).
  (pose proof (aobj_int _ _ (ao_store L ALO) ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros STOi _ (kR & SBND & SBNDa & SBNDb); nd_post).
  (pose proof (aobj_int _ _ (ao_fake L ALO) ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros OFKi _ (kF & OFKs & OFKsa & OFKsb); nd_post).
  (pose proof (aobj4_int _ (ao_dtls L ALO)) as ndP__; nd_pre ndP__ 4%nat; intros _ _ (kD & DBND & DBNDa & DBNDb) (jD & DIMG & DIMGa & DIMGb); nd_post).
  (pose proof (alayout_stack L ALO) as ndP__; nd_pre ndP__ 3%nat; intros STK1 STK2 STK3; nd_post).
  pose proof (alayout_res_disj L ALO) as [SCX TSP].
  pose proof RT as RT0.
  (nd_pre RT0 28%nat; intros GPG GOT GOT80 RIC LS1 REAL IMAX4 FLG5 FLG HPP SHB CANP TI TK INI2 LAY MCS OOM3 PGC HK2 CF8 CF34 CSMT T88 TSD LS2 CT8 CT; nd_post).
  pose proof INI2 as INI. rw_split INI 1%nat INI1 INIx. clear INIx.
  pose proof OOM3 as OOM. rw_split OOM 2%nat OOMx RSS. clear OOMx.
  pose proof IMAX4 as IMAX. rw_split IMAX 3%nat IMAX3 IMAXx. clear IMAXx.
  pose proof T0 as TT0. rw_split TT0 1%nat TTctx TT.
  pose proof ARNG as ARNG0. (nd_pre ARNG 10%nat; intros RIMG RT4 RCTX RNO RSTO RRI RFK RSFK RDTLS RCLS; nd_post).
  assert (RTLS : rng_atls RNG) by ((nd_pre ARNG0 14%nat; intros _ _ _ _ _ _ _ _ _ _ _ _ _ RTLSx; nd_post); exact RTLSx).      (* [comment removed for export] *)
  assert (RCTX4 : rng RNG (al_ctx L) 4096) by (eapply rng_sub'; [exact RCTX|]; clear; lia).
  word_range sp SPR.
  box CL5. box DL7. box DL8. box DL9. box DL10. box TSP. box SCX.
  (* [comment removed for export] *)
  rewrite (amalloc_prim_eq RESV st n c N1 PRIM HC0).
  (* [comment removed for export] *)
  iprefix. eapply evtF_cut.
  { eapply (allocA_pre_spec RNG ra spA gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n SO (al_ctx L) (al_t L) lo).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => exact STA
         | |- mem_inv _ _ => exact MI
         | |- allocA_cells _ _ _ => unfold allocA_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end)
         | |- _ \/ _ => unboxed CL5
         | |- @eq word _ _ => first [exact TP | exact Ha0 | exact Ha1 | exact Ha2 | exact Ha3 | exact Ha4 | exact Ha5]
         | |- is_primary _ = _ => exact PRIM
         end.
    all: try lazymatch goal with
         | |- rw_cells _ _ _ _ => assumption
         | |- rng _ _ _ => assumption
         end.
    all: try assumption.
    all: try (generalize N NR LOA BOT SP47 STK1 STK2 STK3 SP1 SP2 SP4 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 SGE SPRA S47;
              clear; intros; unfold AIMG_HI, AMALLOC_STACK, AREQMAX, UDEPTH in *; lia).
    all: match goal with |- ?G => idtac "REMPRE" G end. }
  cbv beta. intros ms4 P4. unfold allocA_pre_post in P4.
  (nd_pre P4 13%nat; intros t0c t1c t2c a4c a5c a6c a7c t3c t4c t5c t6c m4 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 5%nat; intros MU4' WM4 MI4 ST4 [fr0 FRa]; nd_post).
  replace (bv_unsigned spA - 128) with (bv_unsigned sp - 2272) in ST4, FRa by (clear -HspA; lia).
  assert (MU4 : munch [(bv_unsigned sp - 2320, bv_unsigned sp - 2144); (al_t L + 3168, al_t L + 3169)]%Z m m4)
    by (eapply munch_weaken; [| exact MU4']; unfold sub_fp; cbn [outside]; intros q Hq; clear -Hq HspA; lia).
  (* [comment removed for export] *)
  pose proof SS0 as SS. pose proof TB0 as TB. pose proof TRF0 as TRF.
  xport SS MU4' WM4 ltac:(clear -SGE; lia). xport TB MU4' WM4 ltac:(rewrite LTB; clear -SGE; lia).
  pose proof UNW as UW4. xport UW4 MU4' WM4 ltac:(clear -LOA BOT TL2; unfold AMALLOC_STACK in *; lia).
  apply evtF_done.
  assert (AR4 : AREP (AH DI AQ ASEC AFK) L st X m4).
  { eapply (AREP_frame_pre _ HL L st X m m4); [exact ALO | exact AR | exact MU4 | exact WM4 | | exact UW4].
    apply Forall_cons; [unfold apre; cbn [fst snd]; intros _; left; unfold AMALLOC_STACK in *; clear -LO BOT STK3; lia|].
    apply Forall_cons; [unfold apre; cbn [fst snd]; intros _; right; split; reflexivity| apply Forall_nil]. }
  (* [comment removed for export] *)
  eapply (@calloc_arep_gen _ _ _ HL _ _ _ L RNG _ _ gp tp t0c t1c t2c _ _ _ _ _ _ a4c a5c a6c a7c _ _ _ _ _ _ _ _ _ _ t3c t4c t5c t6c F fc m4 st X c lo (needed_size n)
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
                         eapply rng_sub'; [exact RSTKA|]; clear -LO LOA HspA SP47 BOT STK3; unfold AMALLOC_STACK in *; lia
       end.
  (* [comment removed for export] *)
  intros st_pre X_pre RNG1 m_pre cnt k ms1 CRET. unfold calloc_retG in CRET.
  (nd_pre CRET 37%nat; intros FPLE ARp ARNGp HCNT POS NK NB KR XB L1 L2 L3 L4 L5 L6 L7 L8 MUc WMc MIp t0d t1d t2d a1d a2d a3d a4d a5d a6d a7d t3d t4d t5d t6d m1 stj1 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 6%nat; intros MU1 WM1 MI1 ST1 CR1 STS1; nd_post).
  rewrite ?unsigned_lit in MUc by (clear -SPR HspA LO BOT STK3; unfold AMALLOC_STACK in *; lia).
  rewrite ?unsigned_lit in MU1 by (clear -SPR HspA LO BOT STK3; unfold AMALLOC_STACK in *; lia).
  rewrite ?unsigned_lit in ST1 by (clear -SPR HspA LO BOT STK3; unfold AMALLOC_STACK in *; lia).
  replace (bv_unsigned spA + -128) with (bv_unsigned sp - 2272) in ST1 by (clear -HspA; lia).
  cbn beta iota. apply implS_ret.
  replace (ret_pc (Z_to_bv 64 0x33ea8)) with (Z_to_bv 64 0x33ea8) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  (* [comment removed for export] *)
  pose proof ARp as AR0. (nd_pre AR0 12%nat; intros WF' RT' INST' THR' CLS' HQ' HS' HD' HRO' RT2' AVL' RT3'; nd_post).
  (nd_pre THR' 6%nat; intros T0' T40' CACHES' CSTATS' [sj' [STATS' LSJ']] UNW'; nd_post).
  pose proof WF' as WF0. (nd_pre WF0 11%nat; intros SBE' PAE' SAL' SLO' SHI' PERC' OUTC' BUSY' LIVE' FRESH' UNIQ'; nd_post).
  (nd_pre (PERC' c HCK) 12%nat; intros B1' B2' B3' B4' B5' B6' B7' LENF' LENC' CNTB' ND' RANGE'; nd_post).
  (nd_pre (kit_cache_pop _ L st_pre X_pre m_pre c cnt ARp HCK HCNT POS) 11%nat; intros k' chunks NK' _ _ CR CH LCH NTH JK FSH; nd_post).
  assert (EK : k' = k) by (rewrite NK in NK'; injection NK'; intros E; symmetry; exact E). subst k'.
  (* [comment removed for export] *)
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
  (nd_pre KSF 3%nat; intros KS0 KS1 KS2; nd_post).
  assert (GEO : al_space_beg L <= AB /\ AB + S <= al_space_beg L + K_SPACE_SIZE /\ AB mod 16 = 0
                /\ AB + S <= aregion L c + c_allocated_user (get_cls st_pre c) /\ aregion L c <= AB).
  { subst AB. unfold aslot_addr, aregion, K_REGION, K_SPACE_SIZE, K_FREEARR_OFF, K_ALIGN in *. fold S.
    remember (k * S) as KS eqn:HKS. clear HKS.
    change (2^37) with 137438953472. change (2^32) with 4294967296 in *.
    split; [clear -KS0 C16; lia|]. split; [clear -KS1 B1' B2' C16 NSZ; lia|]. split; [| clear -KS0 KS1 B1'; lia].
    clear -SP3 C16 KS2. Z.div_mod_to_equations; lia. }
  (nd_pre GEO 5%nat; intros G1 G2 G3 G4 G5; nd_post). unfold K_SPACE_SIZE in G2. change (2^37) with 137438953472 in G2.
  assert (EAB : AB = aslot_addr L c k) by reflexivity. clearbody AB.
  assert (ES : S = size_of_class c) by reflexivity.
  (* [comment removed for export] *)
  assert (RZC : rz_size n = 16 \/ 32 <= rz_size n) by (clear -RZR RZM; Z.div_mod_to_equations; lia).
  (nd_pre (slot_carveG m_pre AB S n (rz_size n) JK RZC ltac:(clear -N; lia) ltac:(fold S in NSZ; clear -NSZ NS RSR; lia)) 13%nat; intros b0 b1 szh szl ctxj uj j1 j2 HDR B1 UJ LH TL; nd_post).
  set (UB := AB + rz_size n) in *. assert (EUB : UB = AB + rz_size n) by reflexivity. clearbody UB.
  (* [comment removed for export] *)
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
  (nd_pre (shadow_carve m_pre (shad AB) (shlen S) grz g room FSH GR3 GR4 GR6 GR5) 5%nat; intros SHA SHpre [sjunk SHU] SHP SHsuf; nd_post).
  rewrite <- GR7 in SHU, SHP, SHsuf.
  set (PG := shad UB + g) in *.
  (* [comment removed for export] *)
  pose proof RT' as RT0.
  (nd_pre RT0 28%nat; intros GPG' GOT' GOT80' RIC' LS1' REAL' IMAX4' FLG5' FLG' HPP' SHB' CANP' TI' TK' INI2' LAY' MCS' OOM3' PGC' HK2' CF8' CF34' CSMT' T88' TSD' LS2' CT8' CT'; nd_post).
  pose proof INI2' as INI'. rw_split INI' 1%nat INI1' INIx. clear INIx.
  pose proof OOM3' as OOM'. rw_split OOM' 2%nat OOMx RSS'. clear OOMx.
  pose proof IMAX4' as IMAX'. rw_split IMAX' 3%nat IMAX3' IMAXx. clear IMAXx.
  pose proof HK2' as HK'. rw_split HK' 1%nat HK1' HKx. clear HKx.
  pose proof T0' as TT0'. rw_split TT0' 1%nat TTctx' TT'.
  destruct (junk_split m_pre (al_t L + 2768) 16 16 CSTATS' ltac:(lia) ltac:(lia)) as [CSa CSb].
  destruct (junk_split m_pre (al_t L + 2768 + 16) 8 8 CSb ltac:(lia) ltac:(lia)) as [CS8 CSc].
  replace (al_t L + 2768 + 16) with (al_t L + 2784) in CS8 by lia.
  replace (al_t L + 2768 + 16 + 8) with (al_t L + 2792) in CSc by lia.
  (nd_pre INST' 9%nat; intros I32' I48' I64' I72' I112' I680' I984' I40' I56'; nd_post).
  pose proof ARNGp as ARNGp0. (nd_pre ARNGp 14%nat; intros RIMG' RT4' RCTX' RNO' RST' RRI' RFK' RSFK' RDTLS' RCLS' RPA' RSECS' RPSH' RTLS'; nd_post).
  (nd_pre (RCLS' c HCK) 4%nat; intros RREG RSREG RFA RSFA; nd_post).
  (* [comment removed for export] *)
  (nd_pre (alayout_slot_disj L AB 65536 ALO G1 ltac:(unfold K_SPACE_SIZE, K_FREEARR_OFF, aregion, K_REGION in *; generalize G4 B1' B2' C16 SP1 SZB; clear; intros; change (2^37) with 137438953472; lia) ltac:(clear; lia)) 5%nat; intros DJT DJC DJN DJS DJF; nd_post).
  (* [comment removed for export] *)
  assert (XTAB : tclr AB 65536).
  { apply (tclr_space L AB 65536 ALO); [exact G1|]. unfold K_SPACE_SIZE, K_FREEARR_OFF, aregion, K_REGION in *. generalize G4 B1' B2' C16 SP1 SZB; clear; intros. change (2^37) with 137438953472 in *. lia. }
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
  assert (RSTK1 : rng RNG1 lo (bv_unsigned spA - lo)) by (eapply rng_fp_le; [exact FPLE | exact RSTKA]).
  (* [comment removed for export] *)
  set (mu0 := c_mapped_user (get_cls st c)) in *.
  assert (OBJ : aregion_info L c = al_space_beg L + 137438953472 + c * 128 /\ aregion L c = al_space_beg L + c * 4294967296
                /\ shad (al_space_beg L + c * 4294967296) + 536870912 <= 17594333495296).
  { unfold aregion_info, aregion, K_REGION, K_SPACE_SIZE, ARI_STRIDE. change (2^37) with 137438953472. change (2^32) with 4294967296.
    split; [reflexivity|]. split; [reflexivity|]. rewrite shad_div. clear -SP1 SP2 C16. unfold ASHOFF, K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^37) with 137438953472 in *.
    Z.div_mod_to_equations. lia. }
  (nd_pre OBJ 3%nat; intros RIE RBE SHHI; nd_post).
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
  xport SS MU41 WM41 ltac:(clear -SGE S47 HspA SPR LO BOT STK3 TL1 TL2 SP1 SP2 C16 SHHI TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold AMALLOC_STACK, AINSTANCE in *; lia).
  xport TB MU41 WM41 ltac:(rewrite LTB; clear -SGE S47 HspA SPR LO BOT STK3 TL1 TL2 SP1 SP2 C16 SHHI TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold AMALLOC_STACK, AINSTANCE in *; lia).
  (* [comment removed for export] *)
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
  xport LS2' MU1 WM1 ltac:(clear -HspA SPR TL1 TL2 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport LAY' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport MCS' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport CF34' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport INI1' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport RSS' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport IMAX3' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport TI' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport TK' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport T88' MU1 WM1 ltac:(clear -HspA SPR TL1 TL2 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, ATP88, AMALLOC_STACK in *; lia).
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
  (* [comment removed for export] *)
  assert (PF : pfactsG (bv_unsigned spA) (al_t L) (al_space_beg L) c mu0 ATOP lo).
  { unfold pfactsG. pose proof (ao_t L ALO) as OT. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in OT.   (* [comment removed for export] *)
    unfold AMALLOC_STACK, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN, K_FREEARR_OFF, K_USER_MAP in *. change (2^37) with 137438953472 in *.
    ub TSP. generalize LOA BOT SP47 HspA STK2 STK3 OT SP1 SP2 SAL C16 A1 A2 A4 Y. clear. intros.
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
  (* [comment removed for export] *)
  assert (BB : forall b, In b (x_busy X) ->
      al_space_beg L <= xb_alloc L b /\ xb_alloc L b + size_of_class (xb_class b) <= al_space_beg L + 137438953472
      /\ (xb_alloc L b + size_of_class (xb_class b) <= al_space_beg L + c * 4294967296 + mu0 \/ al_space_beg L + c * 4294967296 + 4294967296 <= xb_alloc L b)).
  { intros b Hb. destruct (BUSY b Hb) as [CLB _].
    (nd_pre (PERC (xb_class b) CLB) 12%nat; intros Q1 Q2 _ _ _ _ _ _ _ _ _ QR; nd_post).
    pose proof (size_of_class_facts (xb_class b) CLB) as [QS _].
    assert (KB : 0 <= xb_slot b < ndist st (xb_class b)).
    { apply QR. apply in_app_iff. right. apply in_app_iff. right. unfold busy_slots. apply in_map_iff. exists b. split; [reflexivity|].
      apply filter_In. split; [exact Hb| apply Z.eqb_refl]. }
    (pose proof (slot_in_region L st (xb_class b) (xb_slot b) ltac:(clear -QS; lia) (proj1 Q1) KB) as ndP__; nd_pre ndP__ 3%nat; intros P5 P4 P0; nd_post).
    unfold xb_alloc. unfold K_NUM_CLASSES in CLB. unfold K_FREEARR_OFF in Q2.
    destruct (Z.eq_dec (xb_class b) c) as [EC|NC].
    - rewrite EC in P5, P4, Q1, Q2 |- *. rewrite RBE in P5, P4. change (c_mapped_user (get_cls st c)) with mu0 in Q1, Q2.
      clear -P5 P4 Q1 Q2 A1 A2 C16. unfold K_FREEARR_OFF in *. lia.
    - (pose proof (region_other_geo L c (xb_class b) ALO ltac:(clear -C16; lia) CLB NC) as ndP__; nd_pre ndP__ 4%nat; intros R1 R2 R3 _; nd_post). rewrite RBE in R2.
      clear -P5 P4 Q1 Q2 R1 R2 R3 A1. lia. }
  pose proof (ao_fake L ALO) as FKO. unfold aobj in FKO. pose proof (ao_res L ALO) as ORS. unfold aobj in ORS. pose proof (ao_space L ALO) as RSP.
  pose proof (ad_fake_res L ALO) as D_f_res. pose proof (ad_t_fake L ALO) as D_t_f. pose proof (ad_dtls_res L ALO) as D_d_res. pose proof (ad_t_dtls L ALO) as D_t_d.
  pose proof (ao_dtls L ALO) as ODT. unfold aobj in ODT. unfold adisj in D_f_res, D_t_f, D_d_res, D_t_d.
  assert (FKD : forall cls FA sz, In (mkABlock (ABFake cls) FA sz) LB -> al_fake L <= FA /\ 0 <= sz /\ FA + sz <= al_fake L + 11571200)
    by (intros cls FA sz Hin; exact (proj1 (proj2 BL) cls FA sz Hin)).
  assert (PRES : aheap_pres CI LB (bv_unsigned spA) m m_pre).
  { intros a Ha CL. split; [| intros Hw; apply WMall; exact Hw].
    apply MUall. rewrite wa_unsigned by exact Ha.
    destruct CL as [CL|TLSA].
    2:{ (* [comment removed for export] *)
        pose proof (ad_tls_t L ALO) as DLT. pose proof (ad_tls_res L ALO) as DLR. unfold adisj in DLT, DLR.
        pose proof atp_lin as TLN. pose proof atop_range as ATR0. pose proof atp_below_atop as TBA.
        destruct TLSA as [[T|(ta & Hta & ->)]|[IM|IM]].
        4:{ pose proof (ao_ahm L ALO) as OAH. pose proof (aobj_img _ _ OAH ltac:(clear; lia)) as OAHI. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in OAH, OAHI.
          rewrite <- (ao_ahm_eq L ALO) in IM. unfold AAHM_SZ in IM. pose proof (ad_ahm_t L ALO) as DA1. pose proof (ad_ahm_res L ALO) as DA2. unfold adisj in DA1, DA2.
            eapply disjoint_outside; [eapply (Q_obj _ _ _ _ _ _ _ PF a 1) | clear; lia]; clear -IM OAH OAHI DA1 DA2 RSP; lia. }
        3:{ unfold AIMSH_LO, AIMSH_LEN in IM. eapply disjoint_outside; [eapply (Q_imsh _ _ _ _ _ _ _ PF a 1) | clear; lia]; clear -IM; lia. }
        - eapply disjoint_outside; [eapply (Q_img _ _ _ _ _ _ _ PF a 1) | clear; lia]; pose proof ATPv_img as TPI; clear -T TPI; unfold AINSTANCE; lia.
        - eapply disjoint_outside; [eapply (Q_shad_objL _ _ _ _ _ _ _ PF ta) | clear; lia]; clear -Hta DLT DLR TLN ATR0 TBA RSP; lia. }
    destruct CL as [STa | [CIa | [BLK | SH]]].
    - eapply disjoint_outside; [eapply (Q_stack _ _ _ _ _ _ _ PF a 1); clear -STa; lia | clear; lia].
    - (nd_pre CIa 3%nat; intros iv Hiv R; nd_post). (pose proof (proj1 (Forall_forall _ _) CI_OK iv Hiv) as ndP__; nd_pre ndP__ 3%nat; intros Q1 Q2 Q3; nd_post).
      pose proof (proj1 (Forall_forall _ _) CI_OK2 iv Hiv) as Q4. cbn [fst snd] in *.
      eapply disjoint_outside; [eapply (Q_img _ _ _ _ _ _ _ PF a 1); unfold AIMG_HI in *; clear -R Q1 Q3 Q4; lia | clear; lia].
    - (nd_pre BLK 3%nat; intros b Hb R; nd_post). destruct b as [[p|cls] A n']; cbn [ab_addr ab_size] in R.
      + destruct (proj1 BL p A n' Hb) as [(xb & Hxb & Sb & Ub & Nb)|(mb0 & ms0 & Lp & EUA & Gs)].
        * (nd_pre (BB xb Hxb) 3%nat; intros Bb1 Bb2 Bb3; nd_post).
          pose proof (awf_fits L st X xb WF Hxb) as FIT. unfold xb_fits in FIT. rewrite Sb in FIT. unfold xb_user in Ub. subst A n'.
          eapply disjoint_outside; [eapply (Q_slot _ _ _ _ _ _ _ PF a 1) | clear; lia]; clear -R Bb1 Bb2 Bb3 FIT; lia.
        * (* [comment removed for export] *)
          cbn [sec_wf1] in Gs. (nd_pre Gs 7%nat; intros Gs1 Gs2 Gs3 Gs4 Gs5 Gs6 (Ct & Cc & Cr & Cp & Cn & Cs & Cf & Cd); nd_post).
          pose proof (sec_facts n' ltac:(clear -Gs5; lia) Gs6) as SF. subst A. unfold SEC_UOFF, K_HIGH_MEM in *.
          unfold ablk, KLS, AIMG_HI in Gs2.   (* [comment removed for export] *)
          eapply disjoint_outside; [eapply (Q_obj _ _ _ _ _ _ _ PF a 1) | clear; lia]; clear -R Gs2 Gs3 Gs4 Gs5 SF Ct Cr RSP ORS; lia.
      + (nd_pre (FKD cls A n' Hb) 3%nat; intros K1 K2 K3; nd_post). atop_facts.
        eapply disjoint_outside; [eapply (Q_obj _ _ _ _ _ _ _ PF a 1) | clear; lia];
          clear -R K1 K3 FKO D_t_f D_f_res RSP OFKi OFKs OFKsa OFKsb; lia.   (* [comment removed for export] *)
    - (nd_pre SH 3%nat; intros a' Ha' ndR1__; nd_post; revert ndR1__; intros ->).
      destruct Ha' as [STa | [CIa | FK]].
      + eapply disjoint_outside; [eapply (Q_shad_hi _ _ _ _ _ _ _ PF a'); unfold AMALLOC_STACK in *; clear -STa LOA BOT STK3; lia | clear; lia].
      + (nd_pre CIa 3%nat; intros iv Hiv R; nd_post). (pose proof (proj1 (Forall_forall _ _) CI_OK iv Hiv) as ndP__; nd_pre ndP__ 3%nat; intros Q1 Q2 Q3; nd_post). cbn [fst snd] in *.
        eapply disjoint_outside; [eapply (Q_shad_img _ _ _ _ _ _ _ PF a'); unfold AIMG_HI in *; clear -R Q1 Q3; lia | clear; lia].
      + (nd_pre FK 5%nat; intros cls FA sz Hin R; nd_post). (nd_pre (FKD cls FA sz Hin) 3%nat; intros K1 K2 K3; nd_post). atop_facts.
        eapply disjoint_outside; [eapply (Q_shad_obj _ _ _ _ _ _ _ PF a') | clear; lia]; clear -R K1 K3 FKO D_f_res RSP OFKi OFKs OFKsa OFKsb; lia. }
  assert (HFKp : AFK L LB m_pre).
  { eapply (hf_frame _ HL L LB m m_pre); [exact HFK | exact MUall | exact WMall |].
    unfold fake_untouched. pose proof (ao_t L ALO) as OT. unfold aobj in OT.
    assert (SHF : 2148238848 <= shad (al_fake L) /\ shad (al_fake L) + shlen 11571200 <= 17594332446720   (* [comment removed for export] *)
                  /\ (shad (al_space_beg L + c * 4294967296) + 536870912 <= shad (al_fake L)
                      \/ shad (al_fake L) + shlen 11571200 <= shad (al_space_beg L + c * 4294967296 + mu0))
                  /\ shad (al_space_beg L + c * 4294967296) <= shad (al_space_beg L + c * 4294967296 + mu0)
                  /\ 2201439137792 <= shad (al_space_beg L + c * 4294967296)).
    { rewrite !shad_div, !shlen_div. unfold ASHOFF in *. (nd_pre PF 4%nat; intros _ _ (F1 & F2 & F3 & F4 & F5 & F6) _; nd_post).
      clear -FKO F1 F2 F3 F4 F5 F6 D_f_res RSP OFKi OFKs OFKsa OFKsb. Z.div_mod_to_equations. dlia. }
    (nd_pre SHF 5%nat; intros SF1 SF2 SF3 SF4 SF5; nd_post).
    unfold AMALLOC_STACK, AINSTANCE in *. (nd_pre PF 4%nat; intros PF1 PF2 PF3 PF4; nd_post).
    repeat (apply Forall_cons; [cbn [fst snd];
      clear -LO LOA HspA BOT STK3 SP47 STK2 OT FKO ORS RSP ODT D_f_res D_t_f D_d_res D_t_d C16 PF3 PF4 SF1 SF2 SF3 SF4 SF5 SHHI TL1 TL2 SP1 TBND TBNDa TBNDb TIMG TIMGa TIMGb OFKi OFKs OFKsa OFKsb DBND DBNDa DBNDb DIMG DIMGa DIMGb;
      repeat (split; [fu_lia|]); fu_lia |]).   (* [comment removed for export] *)
    apply Forall_nil. }
  (* [comment removed for export] *)
  eapply evtF_mono.
  { replace (bv_unsigned sp - 2272) with (bv_unsigned spA + -128) in ST1, FRa by (clear -HspA; lia).
    eapply (allocfn_tail_gen DI L RNG1 ra gp tp spA t0d t1d t2d a1d a2d a3d a4d a5d a6d a7d t3d t4d t5d t6d
              s6 s7 s8 s9 s10 s11 s0 s1 s2 s3 s4 s5 F fc m1
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
                         G1 G2 G3 G4 G5 EUB ES SM16 NSZ NS RSR RZR GR3 GR7 GR8 GR9 SB3 SB4 B1 POS HCNT CNT16 KS0 KS1 HC0 C16 LTRC RA4 HspA SGE S47 LOA SPRA;
              clear; intros; rewrite ?HC0 in *; unfold AIMG_HI, AMALLOC_STACK, AREQMAX, UDEPTH, K_SPACE_SIZE, K_SPACE_EXTRA in *; lia).
    all: try (eapply rng_fp_le; [exact FPLE|]; first [exact RS | exact RSTKA]).
    all: try (eapply rng_sub'; [exact RSTK1|]; clear -LO SP47 BOT STK3 SPR HspA; unfold AMALLOC_STACK in *; lia).
    all: try (clear -LTRC; lia).
    all: try (lazymatch goal with |- tclr _ _ => first [exact XTAB | tclr_solve ALO ltac:(fail)] end).      (* [comment removed for export] *)
    all: match goal with |- ?G => idtac "REMT" G end. }
  (* [comment removed for export] *)
  cbv beta. intros ms' PM.
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
    all: try (generalize N KR B1 LOA BOT STK3 POS; clear; intros; unfold AMALLOC_STACK in *; lia).
    all: try exact HFKp.
    all: match goal with |- ?G => idtac "REMS" G end. }
  exact PRES.
Qed.
End Zd1.
#[using="HL CI_OK CI_OK2"] Theorem allocfn_prim : ltac:(let t := eval cbv delta [allocfn_prim__stmt] in allocfn_prim__stmt in exact t).
Proof. exact allocfn_prim__body. Qed.
End S.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Exec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.ATlsKit.TwB.   (* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepExt.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepExt2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.APrimFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.F_aalloc1.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agbb__A3W.F_aalloc2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc__A3W.F_aalloc.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc__A3W.F_amalloc_icpt.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3g0__A3W.F_amalloc_pre.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agbb__A3W.F_aalloc2g.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3g.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3g0__A3W.F_amalloc_tailg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_amalloc_arep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepStore__A3W.ARepStore.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepStoreG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.ARefill_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARefillP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ACallocG__A3W.ACallocG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc1b__A3W.F_aalloc1b.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3g0__A3W.F_aallocfn_tailg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ACallocG__A3W.AMallocPG.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac fu_drop_fake := repeat match goal with H : context [al_fake _] |- _ => clear H end.
Ltac fu_drop_dtls := repeat match goal with H : context [al_dtls _] |- _ => clear H end.
Ltac fu_drop_tls := repeat match goal with H : context [ATPv] |- _ => clear H | H : context [kt_img] |- _ => clear H end.
Ltac fu_focus :=
  lazymatch goal with
  | |- context [al_fake _] => fu_drop_dtls; fu_drop_tls
  | |- context [al_dtls _] => fu_drop_fake; fu_drop_tls
  | |- context [ATPv] => fu_drop_fake; fu_drop_dtls
  | |- _ => fu_drop_fake; fu_drop_dtls; fu_drop_tls
  end.
Ltac fu_lia := first [solve [fu_focus; lia] | lia].
(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
(* [comment removed for export] *)
#[using="Type"] Local Lemma ablk_int : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6307840 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
#[using="Type"] Local Lemma aobj_int : forall a n, aobj a n -> 0x10000 <= n ->
  6307840 <= a /\ a + n <= ATOP /\ exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof.
  intros a n H Hn. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. (nd_pre H 5%nat; intros H1 H2 H3 H4 H5; nd_post).
  split; [lia|]. split; [lia|]. destruct H4; [exists 0 | exists 1]; lia.
Qed.
#[using="Type"] Local Lemma aobj4_int : forall a, aobj a 4096 ->
  4096 <= a /\ a + 4096 <= ATOP
  /\ (exists k, 0 <= k <= 1 /\ a + 4096 <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a)
  /\ (exists j, 0 <= j <= 1 /\ a + 4096 <= 65536 + j * 18446744073709551616 /\ 6307840 * j <= a).
Proof.
  intros a H. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. (nd_pre H 5%nat; intros H1 H2 H3 H4 H5; nd_post).
  split; [lia|]. split; [lia|]. split; [destruct H4; [exists 0 | exists 1]; lia | destruct H5 as [_ [H5|H5]]; [exists 0 | exists 1]; lia].
Qed.
(* [comment removed for export] *)
Local Ltac dlia := repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
Section S.
Variable DI : ADepotIface.
Variables (AQ ASEC : alayout -> astate -> aconc -> amem -> Prop) (AFK : alayout -> list ablock -> amem -> Prop).
Hypothesis HL : ahole_laws (AH DI AQ ASEC AFK).
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI) CI.
(* [comment removed for export] *)
Hypothesis CI_OK2 : Forall (fun iv => snd iv <= AINSTANCE \/ AINSTANCE + 728 <= fst iv) CI.

Definition allocfn_prim__stmt : Prop := forall (L : alayout) (RNG : footprint)
    (ra spA gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (n lo SO pc : Z) (trc : list Z) (tb : list word) (RESV : list (Z * Z)),
  (* [comment removed for export] *)
  is_primary n = true ->
  (* [comment removed for export] *)
  AHEAP_P (AH DI AQ ASEC AFK) L RNG st LB m ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned spA) -> ATOP + 4096 <= lo -> lo <= bv_unsigned spA - AMALLOC_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 AINSTANCE -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 8 -> a3 = Z_to_bv 64 SO -> a4 = Z_to_bv 64 1 -> a5 = Z_to_bv 64 1 ->
  1 <= n <= AREQMAX ->
  (* [comment removed for export] *)
  bv_unsigned spA <= SO -> SO + 2056 <= 2^47 -> bv_unsigned spA + 2144 < 2^47 ->
  rw_cells asegs m SO [C8 (Z_to_bv 64 (SO + 16)); C8 (Z_to_bv 64 (1 + Z.of_nat (length trc)))] ->
  u64arr asegs m (SO + 16) tb -> length tb = 255%nat ->
  map bv_unsigned (firstn (Datatypes.S (length trc)) tb) = pc :: trc ->
  In (pc :: trc) (al_U L) -> (length trc <= 29)%nat ->
  rng RNG lo (bv_unsigned spA - lo) -> rng RNG SO 2056 ->
  aresv_ok L RESV ->
  implS asegs RNG (aembed ATOP (amalloc ATOP RESV st n))
        (epostF (amalloc_post CI (AHEAP_P (AH DI AQ ASEC AFK)) L RNG ra spA gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB n lo m))
        (MS (mkR ra spA gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 allocate_entry) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'allocfn_prim__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'allocfn_prim__stmt 1).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'allocfn_prim__stmt 2).
Variable spA : ltac2:(SecDietF.SzSecF.ty 'allocfn_prim__stmt 3).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'allocfn_prim__stmt 4).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'allocfn_prim__stmt 5).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'allocfn_prim__stmt 6).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'allocfn_prim__stmt 7).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'allocfn_prim__stmt 8).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'allocfn_prim__stmt 9).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'allocfn_prim__stmt 10).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'allocfn_prim__stmt 11).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'allocfn_prim__stmt 12).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'allocfn_prim__stmt 13).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'allocfn_prim__stmt 14).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'allocfn_prim__stmt 15).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'allocfn_prim__stmt 16).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'allocfn_prim__stmt 17).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'allocfn_prim__stmt 18).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'allocfn_prim__stmt 19).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'allocfn_prim__stmt 20).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'allocfn_prim__stmt 21).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'allocfn_prim__stmt 22).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'allocfn_prim__stmt 23).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'allocfn_prim__stmt 24).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'allocfn_prim__stmt 25).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'allocfn_prim__stmt 26).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'allocfn_prim__stmt 27).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'allocfn_prim__stmt 28).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'allocfn_prim__stmt 29).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'allocfn_prim__stmt 30).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'allocfn_prim__stmt 31).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'allocfn_prim__stmt 32).
Variable F : ltac2:(SecDietF.SzSecF.ty 'allocfn_prim__stmt 33).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'allocfn_prim__stmt 34).
Variable m : ltac2:(SecDietF.SzSecF.ty 'allocfn_prim__stmt 35).
Variable st : ltac2:(SecDietF.SzSecF.ty 'allocfn_prim__stmt 36).
Variable LB : ltac2:(SecDietF.SzSecF.ty 'allocfn_prim__stmt 37).
Variable n : ltac2:(SecDietF.SzSecF.ty 'allocfn_prim__stmt 38).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'allocfn_prim__stmt 39).
Variable SO : ltac2:(SecDietF.SzSecF.ty 'allocfn_prim__stmt 40).
Variable pc : ltac2:(SecDietF.SzSecF.ty 'allocfn_prim__stmt 41).
Variable trc : ltac2:(SecDietF.SzSecF.ty 'allocfn_prim__stmt 42).
Variable tb : ltac2:(SecDietF.SzSecF.ty 'allocfn_prim__stmt 43).
Variable RESV : ltac2:(SecDietF.SzSecF.ty 'allocfn_prim__stmt 44).
#[using="HL CI_OK CI_OK2"] Lemma allocfn_prim__body : ltac:(let T := type of (fun (h : allocfn_prim__stmt) => h L RNG ra spA gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st LB n lo SO pc trc tb RESV) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (RNG, (ra, (spA, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (st, (LB, (n, (lo, (SO, (pc, (trc, (tb, RESV))))))))))))))))))))))))))))))))))))))))))))) as _.
 intros PRIM AHP MI STA BOT LOA TP Ha0 Ha1 Ha2 Ha3 Ha4 Ha5 NR SGE S47 SPV SS0 TB0 LTB TRF0 TRU LTRC RSTKA RS ROK.
  assert (N : 1 <= n <= AREQMAX) by exact NR. assert (N1 : 1 <= n) by (clear -NR; lia).
  (* [comment removed for export] *)
  word_range spA SPRA.
  pose (sp := Z_to_bv 64 (bv_unsigned spA + 2144)).
  assert (HspA : bv_unsigned spA = bv_unsigned sp - 2144) by (subst sp; rewrite unsigned_lit by (clear -SPRA SPV; lia); clear; lia).
  clearbody sp.
  assert (LO : lo <= bv_unsigned sp - AMALLOC_STACK) by (clear -LOA HspA; unfold AMALLOC_STACK in *; lia).
  assert (SP47 : bv_unsigned sp < 2^47) by (clear -SPV HspA; lia).
  assert (RA4 : True) by exact I.
  (nd_pre AHP 4%nat; intros ALO ARNG [X [AR BL]] HFK; nd_post).
  remember (class_id (needed_size n)) as c eqn:HC0. symmetry in HC0.
  (pose proof (prim_facts n N1 PRIM) as ndP__; nd_pre ndP__ 8%nat; intros NS RZR RZE RZM RLR RSR RSM NSR; nd_post).
  (pose proof (prim_class_facts n c N1 PRIM HC0) as ndP__; nd_pre ndP__ 5%nat; intros C16 NSZ SM16 SMALL MCB; nd_post). clear SMALL.
  (pose proof (cls_facts c C16) as ndP__; nd_pre ndP__ 4%nat; intros SZB _ _ _; nd_post).
  assert (HCK : 1 <= c < K_NUM_CLASSES) by (unfold K_NUM_CLASSES; clear -C16; lia).
  assert (NM8 : needed_size n mod 8 = 0) by (rewrite NS; clear -RSM RZM; Z.div_mod_to_equations; lia).
  (* [comment removed for export] *)
  pose proof AR as AR0. (nd_pre AR0 12%nat; intros WF RT INST THR CLS HQ HS HD HRO RT2 AVL RT3; nd_post).
  (nd_pre THR 6%nat; intros T0 T40 CACHES CSTATS [sj [STATS LSJ]] UNW; nd_post).
  pose proof WF as WF0. (nd_pre WF0 11%nat; intros SBE PAE SAL SLO SHI PERC OUTC BUSY LIVE FRESH UNIQ; nd_post).
  (nd_pre (PERC c HCK) 12%nat; intros A1 A2 A3 A4 A5 A6 A7 LENF LENC CNTB ND RANGE; nd_post).
  (pose proof (alayout_space L ALO) as ndP__; nd_pre ndP__ 4%nat; intros SP1 SP2 SP3 SP4; nd_post).
  (pose proof (alayout_t L ALO) as ndP__; nd_pre ndP__ 4%nat; intros TL1 TL2 TL3 TL4; nd_post).
  (pose proof (alayout_ctx L ALO) as ndP__; nd_pre ndP__ 5%nat; intros CL1 CL2 CL3 CL4 CL5; nd_post).
  (pose proof (alayout_depot L ALO) as ndP__; nd_pre ndP__ 10%nat; intros DL1 DL2 DL3 DL4 DL5 DL6 DL7 DL8 DL9 DL10; nd_post).
  (pose proof (aobj4_int _ (ao_t L ALO)) as ndP__; nd_pre ndP__ 4%nat; intros _ _ (kT & TBND & TBNDa & TBNDb) (jT & TIMG & TIMGa & TIMGb); nd_post).   (* [comment removed for export] *)
  (pose proof (aobj_int _ _ (ao_ctx L ALO) ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros CTXi _ (kC & CBND & CBNDa & CBNDb); nd_post).
  (pose proof (aobj_int _ _ (ao_nodes L ALO) ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros NODi _ (kN & NBND & NBNDa & NBNDb); nd_post).
  (pose proof (aobj_int _ _ (ao_store L ALO) ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros STOi _ (kR & SBND & SBNDa & SBNDb); nd_post).
  (pose proof (aobj_int _ _ (ao_fake L ALO) ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros OFKi _ (kF & OFKs & OFKsa & OFKsb); nd_post).
  (pose proof (aobj4_int _ (ao_dtls L ALO)) as ndP__; nd_pre ndP__ 4%nat; intros _ _ (kD & DBND & DBNDa & DBNDb) (jD & DIMG & DIMGa & DIMGb); nd_post).
  (pose proof (alayout_stack L ALO) as ndP__; nd_pre ndP__ 3%nat; intros STK1 STK2 STK3; nd_post).
  pose proof (alayout_res_disj L ALO) as [SCX TSP].
  pose proof RT as RT0.
  (nd_pre RT0 28%nat; intros GPG GOT GOT80 RIC LS1 REAL IMAX4 FLG5 FLG HPP SHB CANP TI TK INI2 LAY MCS OOM3 PGC HK2 CF8 CF34 CSMT T88 TSD LS2 CT8 CT; nd_post).
  pose proof INI2 as INI. rw_split INI 1%nat INI1 INIx. clear INIx.
  pose proof OOM3 as OOM. rw_split OOM 2%nat OOMx RSS. clear OOMx.
  pose proof IMAX4 as IMAX. rw_split IMAX 3%nat IMAX3 IMAXx. clear IMAXx.
  pose proof T0 as TT0. rw_split TT0 1%nat TTctx TT.
  pose proof ARNG as ARNG0. (nd_pre ARNG 10%nat; intros RIMG RT4 RCTX RNO RSTO RRI RFK RSFK RDTLS RCLS; nd_post).
  assert (RTLS : rng_atls RNG) by ((nd_pre ARNG0 14%nat; intros _ _ _ _ _ _ _ _ _ _ _ _ _ RTLSx; nd_post); exact RTLSx).      (* [comment removed for export] *)
  assert (RCTX4 : rng RNG (al_ctx L) 4096) by (eapply rng_sub'; [exact RCTX|]; clear; lia).
  word_range sp SPR.
  box CL5. box DL7. box DL8. box DL9. box DL10. box TSP. box SCX.
  (* [comment removed for export] *)
  rewrite (amalloc_prim_eq RESV st n c N1 PRIM HC0).
  (* [comment removed for export] *)
  iprefix. eapply evtF_cut.
  { eapply (allocA_pre_spec RNG ra spA gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n SO (al_ctx L) (al_t L) lo).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => exact STA
         | |- mem_inv _ _ => exact MI
         | |- allocA_cells _ _ _ => unfold allocA_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end)
         | |- _ \/ _ => unboxed CL5
         | |- @eq word _ _ => first [exact TP | exact Ha0 | exact Ha1 | exact Ha2 | exact Ha3 | exact Ha4 | exact Ha5]
         | |- is_primary _ = _ => exact PRIM
         end.
    all: try lazymatch goal with
         | |- rw_cells _ _ _ _ => assumption
         | |- rng _ _ _ => assumption
         end.
    all: try assumption.
    all: try (generalize N NR LOA BOT SP47 STK1 STK2 STK3 SP1 SP2 SP4 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 SGE SPRA S47;
              clear; intros; unfold AIMG_HI, AMALLOC_STACK, AREQMAX, UDEPTH in *; lia).
    all: match goal with |- ?G => idtac "REMPRE" G end. }
  cbv beta. intros ms4 P4. unfold allocA_pre_post in P4.
  (nd_pre P4 13%nat; intros t0c t1c t2c a4c a5c a6c a7c t3c t4c t5c t6c m4 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 5%nat; intros MU4' WM4 MI4 ST4 [fr0 FRa]; nd_post).
  replace (bv_unsigned spA - 128) with (bv_unsigned sp - 2272) in ST4, FRa by (clear -HspA; lia).
  assert (MU4 : munch [(bv_unsigned sp - 2320, bv_unsigned sp - 2144); (al_t L + 3168, al_t L + 3169)]%Z m m4)
    by (eapply munch_weaken; [| exact MU4']; unfold sub_fp; cbn [outside]; intros q Hq; clear -Hq HspA; lia).
  (* [comment removed for export] *)
  pose proof SS0 as SS. pose proof TB0 as TB. pose proof TRF0 as TRF.
  xport SS MU4' WM4 ltac:(clear -SGE; lia). xport TB MU4' WM4 ltac:(rewrite LTB; clear -SGE; lia).
  pose proof UNW as UW4. xport UW4 MU4' WM4 ltac:(clear -LOA BOT TL2; unfold AMALLOC_STACK in *; lia).
  apply evtF_done.
  assert (AR4 : AREP (AH DI AQ ASEC AFK) L st X m4).
  { eapply (AREP_frame_pre _ HL L st X m m4); [exact ALO | exact AR | exact MU4 | exact WM4 | | exact UW4].
    apply Forall_cons; [unfold apre; cbn [fst snd]; intros _; left; unfold AMALLOC_STACK in *; clear -LO BOT STK3; lia|].
    apply Forall_cons; [unfold apre; cbn [fst snd]; intros _; right; split; reflexivity| apply Forall_nil]. }
  (* [comment removed for export] *)
  eapply (@calloc_arep_gen _ _ _ HL _ _ _ L RNG _ _ gp tp t0c t1c t2c _ _ _ _ _ _ a4c a5c a6c a7c _ _ _ _ _ _ _ _ _ _ t3c t4c t5c t6c F fc m4 st X c lo (needed_size n)
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
                         eapply rng_sub'; [exact RSTKA|]; clear -LO LOA HspA SP47 BOT STK3; unfold AMALLOC_STACK in *; lia
       end.
  (* [comment removed for export] *)
  intros st_pre X_pre RNG1 m_pre cnt k ms1 CRET. unfold calloc_retG in CRET.
  (nd_pre CRET 37%nat; intros FPLE ARp ARNGp HCNT POS NK NB KR XB L1 L2 L3 L4 L5 L6 L7 L8 MUc WMc MIp t0d t1d t2d a1d a2d a3d a4d a5d a6d a7d t3d t4d t5d t6d m1 stj1 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 6%nat; intros MU1 WM1 MI1 ST1 CR1 STS1; nd_post).
  rewrite ?unsigned_lit in MUc by (clear -SPR HspA LO BOT STK3; unfold AMALLOC_STACK in *; lia).
  rewrite ?unsigned_lit in MU1 by (clear -SPR HspA LO BOT STK3; unfold AMALLOC_STACK in *; lia).
  rewrite ?unsigned_lit in ST1 by (clear -SPR HspA LO BOT STK3; unfold AMALLOC_STACK in *; lia).
  replace (bv_unsigned spA + -128) with (bv_unsigned sp - 2272) in ST1 by (clear -HspA; lia).
  cbn beta iota. apply implS_ret.
  replace (ret_pc (Z_to_bv 64 0x33f10)) with (Z_to_bv 64 0x33f10) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  (* [comment removed for export] *)
  pose proof ARp as AR0. (nd_pre AR0 12%nat; intros WF' RT' INST' THR' CLS' HQ' HS' HD' HRO' RT2' AVL' RT3'; nd_post).
  (nd_pre THR' 6%nat; intros T0' T40' CACHES' CSTATS' [sj' [STATS' LSJ']] UNW'; nd_post).
  pose proof WF' as WF0. (nd_pre WF0 11%nat; intros SBE' PAE' SAL' SLO' SHI' PERC' OUTC' BUSY' LIVE' FRESH' UNIQ'; nd_post).
  (nd_pre (PERC' c HCK) 12%nat; intros B1' B2' B3' B4' B5' B6' B7' LENF' LENC' CNTB' ND' RANGE'; nd_post).
  (nd_pre (kit_cache_pop _ L st_pre X_pre m_pre c cnt ARp HCK HCNT POS) 11%nat; intros k' chunks NK' _ _ CR CH LCH NTH JK FSH; nd_post).
  assert (EK : k' = k) by (rewrite NK in NK'; injection NK'; intros E; symmetry; exact E). subst k'.
  (* [comment removed for export] *)
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
  (nd_pre KSF 3%nat; intros KS0 KS1 KS2; nd_post).
  assert (GEO : al_space_beg L <= AB /\ AB + S <= al_space_beg L + K_SPACE_SIZE /\ AB mod 16 = 0
                /\ AB + S <= aregion L c + c_allocated_user (get_cls st_pre c) /\ aregion L c <= AB).
  { subst AB. unfold aslot_addr, aregion, K_REGION, K_SPACE_SIZE, K_FREEARR_OFF, K_ALIGN in *. fold S.
    remember (k * S) as KS eqn:HKS. clear HKS.
    change (2^37) with 137438953472. change (2^32) with 4294967296 in *.
    split; [clear -KS0 C16; lia|]. split; [clear -KS1 B1' B2' C16 NSZ; lia|]. split; [| clear -KS0 KS1 B1'; lia].
    clear -SP3 C16 KS2. Z.div_mod_to_equations; lia. }
  (nd_pre GEO 5%nat; intros G1 G2 G3 G4 G5; nd_post). unfold K_SPACE_SIZE in G2. change (2^37) with 137438953472 in G2.
  assert (EAB : AB = aslot_addr L c k) by reflexivity. clearbody AB.
  assert (ES : S = size_of_class c) by reflexivity.
  (* [comment removed for export] *)
  assert (RZC : rz_size n = 16 \/ 32 <= rz_size n) by (clear -RZR RZM; Z.div_mod_to_equations; lia).
  (nd_pre (slot_carveG m_pre AB S n (rz_size n) JK RZC ltac:(clear -N; lia) ltac:(fold S in NSZ; clear -NSZ NS RSR; lia)) 13%nat; intros b0 b1 szh szl ctxj uj j1 j2 HDR B1 UJ LH TL; nd_post).
  set (UB := AB + rz_size n) in *. assert (EUB : UB = AB + rz_size n) by reflexivity. clearbody UB.
  (* [comment removed for export] *)
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
  (nd_pre (shadow_carve m_pre (shad AB) (shlen S) grz g room FSH GR3 GR4 GR6 GR5) 5%nat; intros SHA SHpre [sjunk SHU] SHP SHsuf; nd_post).
  rewrite <- GR7 in SHU, SHP, SHsuf.
  set (PG := shad UB + g) in *.
  (* [comment removed for export] *)
  pose proof RT' as RT0.
  (nd_pre RT0 28%nat; intros GPG' GOT' GOT80' RIC' LS1' REAL' IMAX4' FLG5' FLG' HPP' SHB' CANP' TI' TK' INI2' LAY' MCS' OOM3' PGC' HK2' CF8' CF34' CSMT' T88' TSD' LS2' CT8' CT'; nd_post).
  pose proof INI2' as INI'. rw_split INI' 1%nat INI1' INIx. clear INIx.
  pose proof OOM3' as OOM'. rw_split OOM' 2%nat OOMx RSS'. clear OOMx.
  pose proof IMAX4' as IMAX'. rw_split IMAX' 3%nat IMAX3' IMAXx. clear IMAXx.
  pose proof HK2' as HK'. rw_split HK' 1%nat HK1' HKx. clear HKx.
  pose proof T0' as TT0'. rw_split TT0' 1%nat TTctx' TT'.
  destruct (junk_split m_pre (al_t L + 2768) 16 16 CSTATS' ltac:(lia) ltac:(lia)) as [CSa CSb].
  destruct (junk_split m_pre (al_t L + 2768 + 16) 8 8 CSb ltac:(lia) ltac:(lia)) as [CS8 CSc].
  replace (al_t L + 2768 + 16) with (al_t L + 2784) in CS8 by lia.
  replace (al_t L + 2768 + 16 + 8) with (al_t L + 2792) in CSc by lia.
  (nd_pre INST' 9%nat; intros I32' I48' I64' I72' I112' I680' I984' I40' I56'; nd_post).
  pose proof ARNGp as ARNGp0. (nd_pre ARNGp 14%nat; intros RIMG' RT4' RCTX' RNO' RST' RRI' RFK' RSFK' RDTLS' RCLS' RPA' RSECS' RPSH' RTLS'; nd_post).
  (nd_pre (RCLS' c HCK) 4%nat; intros RREG RSREG RFA RSFA; nd_post).
  (* [comment removed for export] *)
  (nd_pre (alayout_slot_disj L AB 65536 ALO G1 ltac:(unfold K_SPACE_SIZE, K_FREEARR_OFF, aregion, K_REGION in *; generalize G4 B1' B2' C16 SP1 SZB; clear; intros; change (2^37) with 137438953472; lia) ltac:(clear; lia)) 5%nat; intros DJT DJC DJN DJS DJF; nd_post).
  (* [comment removed for export] *)
  assert (XTAB : tclr AB 65536).
  { apply (tclr_space L AB 65536 ALO); [exact G1|]. unfold K_SPACE_SIZE, K_FREEARR_OFF, aregion, K_REGION in *. generalize G4 B1' B2' C16 SP1 SZB; clear; intros. change (2^37) with 137438953472 in *. lia. }
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
  assert (RSTK1 : rng RNG1 lo (bv_unsigned spA - lo)) by (eapply rng_fp_le; [exact FPLE | exact RSTKA]).
  (* [comment removed for export] *)
  set (mu0 := c_mapped_user (get_cls st c)) in *.
  assert (OBJ : aregion_info L c = al_space_beg L + 137438953472 + c * 128 /\ aregion L c = al_space_beg L + c * 4294967296
                /\ shad (al_space_beg L + c * 4294967296) + 536870912 <= 17594333495296).
  { unfold aregion_info, aregion, K_REGION, K_SPACE_SIZE, ARI_STRIDE. change (2^37) with 137438953472. change (2^32) with 4294967296.
    split; [reflexivity|]. split; [reflexivity|]. rewrite shad_div. clear -SP1 SP2 C16. unfold ASHOFF, K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^37) with 137438953472 in *.
    Z.div_mod_to_equations. lia. }
  (nd_pre OBJ 3%nat; intros RIE RBE SHHI; nd_post).
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
  xport SS MU41 WM41 ltac:(clear -SGE S47 HspA SPR LO BOT STK3 TL1 TL2 SP1 SP2 C16 SHHI TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold AMALLOC_STACK, AINSTANCE in *; lia).
  xport TB MU41 WM41 ltac:(rewrite LTB; clear -SGE S47 HspA SPR LO BOT STK3 TL1 TL2 SP1 SP2 C16 SHHI TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold AMALLOC_STACK, AINSTANCE in *; lia).
  (* [comment removed for export] *)
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
  xport LS2' MU1 WM1 ltac:(clear -HspA SPR TL1 TL2 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport LAY' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport MCS' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport CF34' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport INI1' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport RSS' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport IMAX3' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport TI' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport TK' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
  xport T88' MU1 WM1 ltac:(clear -HspA SPR TL1 TL2 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, ATP88, AMALLOC_STACK in *; lia).
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
  (* [comment removed for export] *)
  assert (PF : pfactsG (bv_unsigned spA) (al_t L) (al_space_beg L) c mu0 ATOP lo).
  { unfold pfactsG. pose proof (ao_t L ALO) as OT. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in OT.   (* [comment removed for export] *)
    unfold AMALLOC_STACK, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN, K_FREEARR_OFF, K_USER_MAP in *. change (2^37) with 137438953472 in *.
    ub TSP. generalize LOA BOT SP47 HspA STK2 STK3 OT SP1 SP2 SAL C16 A1 A2 A4 Y. clear. intros.
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
  (* [comment removed for export] *)
  assert (BB : forall b, In b (x_busy X) ->
      al_space_beg L <= xb_alloc L b /\ xb_alloc L b + size_of_class (xb_class b) <= al_space_beg L + 137438953472
      /\ (xb_alloc L b + size_of_class (xb_class b) <= al_space_beg L + c * 4294967296 + mu0 \/ al_space_beg L + c * 4294967296 + 4294967296 <= xb_alloc L b)).
  { intros b Hb. destruct (BUSY b Hb) as [CLB _].
    (nd_pre (PERC (xb_class b) CLB) 12%nat; intros Q1 Q2 _ _ _ _ _ _ _ _ _ QR; nd_post).
    pose proof (size_of_class_facts (xb_class b) CLB) as [QS _].
    assert (KB : 0 <= xb_slot b < ndist st (xb_class b)).
    { apply QR. apply in_app_iff. right. apply in_app_iff. right. unfold busy_slots. apply in_map_iff. exists b. split; [reflexivity|].
      apply filter_In. split; [exact Hb| apply Z.eqb_refl]. }
    (pose proof (slot_in_region L st (xb_class b) (xb_slot b) ltac:(clear -QS; lia) (proj1 Q1) KB) as ndP__; nd_pre ndP__ 3%nat; intros P5 P4 P0; nd_post).
    unfold xb_alloc. unfold K_NUM_CLASSES in CLB. unfold K_FREEARR_OFF in Q2.
    destruct (Z.eq_dec (xb_class b) c) as [EC|NC].
    - rewrite EC in P5, P4, Q1, Q2 |- *. rewrite RBE in P5, P4. change (c_mapped_user (get_cls st c)) with mu0 in Q1, Q2.
      clear -P5 P4 Q1 Q2 A1 A2 C16. unfold K_FREEARR_OFF in *. lia.
    - (pose proof (region_other_geo L c (xb_class b) ALO ltac:(clear -C16; lia) CLB NC) as ndP__; nd_pre ndP__ 4%nat; intros R1 R2 R3 _; nd_post). rewrite RBE in R2.
      clear -P5 P4 Q1 Q2 R1 R2 R3 A1. lia. }
  pose proof (ao_fake L ALO) as FKO. unfold aobj in FKO. pose proof (ao_res L ALO) as ORS. unfold aobj in ORS. pose proof (ao_space L ALO) as RSP.
  pose proof (ad_fake_res L ALO) as D_f_res. pose proof (ad_t_fake L ALO) as D_t_f. pose proof (ad_dtls_res L ALO) as D_d_res. pose proof (ad_t_dtls L ALO) as D_t_d.
  pose proof (ao_dtls L ALO) as ODT. unfold aobj in ODT. unfold adisj in D_f_res, D_t_f, D_d_res, D_t_d.
  assert (FKD : forall cls FA sz, In (mkABlock (ABFake cls) FA sz) LB -> al_fake L <= FA /\ 0 <= sz /\ FA + sz <= al_fake L + 11571200)
    by (intros cls FA sz Hin; exact (proj1 (proj2 BL) cls FA sz Hin)).
  assert (PRES : aheap_pres CI LB (bv_unsigned spA) m m_pre).
  { intros a Ha CL. split; [| intros Hw; apply WMall; exact Hw].
    apply MUall. rewrite wa_unsigned by exact Ha.
    destruct CL as [CL|TLSA].
    2:{ (* [comment removed for export] *)
        pose proof (ad_tls_t L ALO) as DLT. pose proof (ad_tls_res L ALO) as DLR. unfold adisj in DLT, DLR.
        pose proof atp_lin as TLN. pose proof atop_range as ATR0. pose proof atp_below_atop as TBA.
        destruct TLSA as [[T|(ta & Hta & ->)]|[IM|IM]].
        4:{ pose proof (ao_ahm L ALO) as OAH. pose proof (aobj_img _ _ OAH ltac:(clear; lia)) as OAHI. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in OAH, OAHI.
          rewrite <- (ao_ahm_eq L ALO) in IM. unfold AAHM_SZ in IM. pose proof (ad_ahm_t L ALO) as DA1. pose proof (ad_ahm_res L ALO) as DA2. unfold adisj in DA1, DA2.
            eapply disjoint_outside; [eapply (Q_obj _ _ _ _ _ _ _ PF a 1) | clear; lia]; clear -IM OAH OAHI DA1 DA2 RSP; lia. }
        3:{ unfold AIMSH_LO, AIMSH_LEN in IM. eapply disjoint_outside; [eapply (Q_imsh _ _ _ _ _ _ _ PF a 1) | clear; lia]; clear -IM; lia. }
        - eapply disjoint_outside; [eapply (Q_img _ _ _ _ _ _ _ PF a 1) | clear; lia]; pose proof ATPv_img as TPI; clear -T TPI; unfold AINSTANCE; lia.
        - eapply disjoint_outside; [eapply (Q_shad_objL _ _ _ _ _ _ _ PF ta) | clear; lia]; clear -Hta DLT DLR TLN ATR0 TBA RSP; lia. }
    destruct CL as [STa | [CIa | [BLK | SH]]].
    - eapply disjoint_outside; [eapply (Q_stack _ _ _ _ _ _ _ PF a 1); clear -STa; lia | clear; lia].
    - (nd_pre CIa 3%nat; intros iv Hiv R; nd_post). (pose proof (proj1 (Forall_forall _ _) CI_OK iv Hiv) as ndP__; nd_pre ndP__ 3%nat; intros Q1 Q2 Q3; nd_post).
      pose proof (proj1 (Forall_forall _ _) CI_OK2 iv Hiv) as Q4. cbn [fst snd] in *.
      eapply disjoint_outside; [eapply (Q_img _ _ _ _ _ _ _ PF a 1); unfold AIMG_HI in *; clear -R Q1 Q3 Q4; lia | clear; lia].
    - (nd_pre BLK 3%nat; intros b Hb R; nd_post). destruct b as [[p|cls] A n']; cbn [ab_addr ab_size] in R.
      + destruct (proj1 BL p A n' Hb) as [(xb & Hxb & Sb & Ub & Nb)|(mb0 & ms0 & Lp & EUA & Gs)].
        * (nd_pre (BB xb Hxb) 3%nat; intros Bb1 Bb2 Bb3; nd_post).
          pose proof (awf_fits L st X xb WF Hxb) as FIT. unfold xb_fits in FIT. rewrite Sb in FIT. unfold xb_user in Ub. subst A n'.
          eapply disjoint_outside; [eapply (Q_slot _ _ _ _ _ _ _ PF a 1) | clear; lia]; clear -R Bb1 Bb2 Bb3 FIT; lia.
        * (* [comment removed for export] *)
          cbn [sec_wf1] in Gs. (nd_pre Gs 7%nat; intros Gs1 Gs2 Gs3 Gs4 Gs5 Gs6 (Ct & Cc & Cr & Cp & Cn & Cs & Cf & Cd); nd_post).
          pose proof (sec_facts n' ltac:(clear -Gs5; lia) Gs6) as SF. subst A. unfold SEC_UOFF, K_HIGH_MEM in *.
          unfold ablk, KLS, AIMG_HI in Gs2.   (* [comment removed for export] *)
          eapply disjoint_outside; [eapply (Q_obj _ _ _ _ _ _ _ PF a 1) | clear; lia]; clear -R Gs2 Gs3 Gs4 Gs5 SF Ct Cr RSP ORS; lia.
      + (nd_pre (FKD cls A n' Hb) 3%nat; intros K1 K2 K3; nd_post). atop_facts.
        eapply disjoint_outside; [eapply (Q_obj _ _ _ _ _ _ _ PF a 1) | clear; lia];
          clear -R K1 K3 FKO D_t_f D_f_res RSP OFKi OFKs OFKsa OFKsb; lia.   (* [comment removed for export] *)
    - (nd_pre SH 3%nat; intros a' Ha' ndR1__; nd_post; revert ndR1__; intros ->).
      destruct Ha' as [STa | [CIa | FK]].
      + eapply disjoint_outside; [eapply (Q_shad_hi _ _ _ _ _ _ _ PF a'); unfold AMALLOC_STACK in *; clear -STa LOA BOT STK3; lia | clear; lia].
      + (nd_pre CIa 3%nat; intros iv Hiv R; nd_post). (pose proof (proj1 (Forall_forall _ _) CI_OK iv Hiv) as ndP__; nd_pre ndP__ 3%nat; intros Q1 Q2 Q3; nd_post). cbn [fst snd] in *.
        eapply disjoint_outside; [eapply (Q_shad_img _ _ _ _ _ _ _ PF a'); unfold AIMG_HI in *; clear -R Q1 Q3; lia | clear; lia].
      + (nd_pre FK 5%nat; intros cls FA sz Hin R; nd_post). (nd_pre (FKD cls FA sz Hin) 3%nat; intros K1 K2 K3; nd_post). atop_facts.
        eapply disjoint_outside; [eapply (Q_shad_obj _ _ _ _ _ _ _ PF a') | clear; lia]; clear -R K1 K3 FKO D_f_res RSP OFKi OFKs OFKsa OFKsb; lia. }
  assert (HFKp : AFK L LB m_pre).
  { eapply (hf_frame _ HL L LB m m_pre); [exact HFK | exact MUall | exact WMall |].
    unfold fake_untouched. pose proof (ao_t L ALO) as OT. unfold aobj in OT.
    assert (SHF : 2148239360 <= shad (al_fake L) /\ shad (al_fake L) + shlen 11571200 <= 17594332446720   (* [comment removed for export] *)
                  /\ (shad (al_space_beg L + c * 4294967296) + 536870912 <= shad (al_fake L)
                      \/ shad (al_fake L) + shlen 11571200 <= shad (al_space_beg L + c * 4294967296 + mu0))
                  /\ shad (al_space_beg L + c * 4294967296) <= shad (al_space_beg L + c * 4294967296 + mu0)
                  /\ 2201439137792 <= shad (al_space_beg L + c * 4294967296)).
    { rewrite !shad_div, !shlen_div. unfold ASHOFF in *. (nd_pre PF 4%nat; intros _ _ (F1 & F2 & F3 & F4 & F5 & F6) _; nd_post).
      clear -FKO F1 F2 F3 F4 F5 F6 D_f_res RSP OFKi OFKs OFKsa OFKsb. Z.div_mod_to_equations. dlia. }
    (nd_pre SHF 5%nat; intros SF1 SF2 SF3 SF4 SF5; nd_post).
    unfold AMALLOC_STACK, AINSTANCE in *. (nd_pre PF 4%nat; intros PF1 PF2 PF3 PF4; nd_post).
    repeat (apply Forall_cons; [cbn [fst snd];
      clear -LO LOA HspA BOT STK3 SP47 STK2 OT FKO ORS RSP ODT D_f_res D_t_f D_d_res D_t_d C16 PF3 PF4 SF1 SF2 SF3 SF4 SF5 SHHI TL1 TL2 SP1 TBND TBNDa TBNDb TIMG TIMGa TIMGb OFKi OFKs OFKsa OFKsb DBND DBNDa DBNDb DIMG DIMGa DIMGb;
      repeat (split; [fu_lia|]); fu_lia |]).   (* [comment removed for export] *)
    apply Forall_nil. }
  (* [comment removed for export] *)
  eapply evtF_mono.
  { replace (bv_unsigned sp - 2272) with (bv_unsigned spA + -128) in ST1, FRa by (clear -HspA; lia).
    eapply (allocfn_tail_gen DI L RNG1 ra gp tp spA t0d t1d t2d a1d a2d a3d a4d a5d a6d a7d t3d t4d t5d t6d
              s6 s7 s8 s9 s10 s11 s0 s1 s2 s3 s4 s5 F fc m1
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
                         G1 G2 G3 G4 G5 EUB ES SM16 NSZ NS RSR RZR GR3 GR7 GR8 GR9 SB3 SB4 B1 POS HCNT CNT16 KS0 KS1 HC0 C16 LTRC RA4 HspA SGE S47 LOA SPRA;
              clear; intros; rewrite ?HC0 in *; unfold AIMG_HI, AMALLOC_STACK, AREQMAX, UDEPTH, K_SPACE_SIZE, K_SPACE_EXTRA in *; lia).
    all: try (eapply rng_fp_le; [exact FPLE|]; first [exact RS | exact RSTKA]).
    all: try (eapply rng_sub'; [exact RSTK1|]; clear -LO SP47 BOT STK3 SPR HspA; unfold AMALLOC_STACK in *; lia).
    all: try (clear -LTRC; lia).
    all: try (lazymatch goal with |- tclr _ _ => first [exact XTAB | tclr_solve ALO ltac:(fail)] end).      (* [comment removed for export] *)
    all: match goal with |- ?G => idtac "REMT" G end. }
  (* [comment removed for export] *)
  cbv beta. intros ms' PM.
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
    all: try (generalize N KR B1 LOA BOT STK3 POS; clear; intros; unfold AMALLOC_STACK in *; lia).
    all: try exact HFKp.
    all: match goal with |- ?G => idtac "REMS" G end. }
  exact PRES.
Qed.
End Zd1.
#[using="HL CI_OK CI_OK2"] Theorem allocfn_prim : ltac:(let t := eval cbv delta [allocfn_prim__stmt] in allocfn_prim__stmt in exact t).
Proof. exact allocfn_prim__body. Qed.
End S.
End CANSEC1.
End TwB.
End AAllocFnPG.

(* [comment removed for export] *)
Module AAllocFn.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Step Frame Arr ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase AMalloc_iface. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_apoison__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASec__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_amalloc_arep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_acallocS__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecSlog__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.APoisonR_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_amalloc_arep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ACallocG__A3W.AMallocPG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acallocS__A3W.AMallocS OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.AFn_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ACallocG__A3W.AAllocFnPG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acallocS__A3W.AAllocFnS.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section S.
Variable DI : ADepotIface.
Variables (AQ : alayout -> astate -> aconc -> amem -> Prop) (AFK : alayout -> list ablock -> amem -> Prop).
Hypothesis HL : ahole_laws (AH DI AQ ASEC_of AFK).
Hypothesis PR : poison_remap_stmt.
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI) CI.
Hypothesis CI_OK2 : Forall (fun iv => snd iv <= AINSTANCE \/ AINSTANCE + 728 <= fst iv) CI.

#[using="HL PR CI_OK CI_OK2"] Theorem allocfn_all : allocfn_stmt CI (AHEAP_P (AH DI AQ ASEC_of AFK)).
Proof.
  unfold allocfn_stmt. intros.
  destruct (is_primary n) eqn:P.
  - eapply (allocfn_prim DI AQ ASEC_of AFK HL CI CI_OK CI_OK2); eassumption.
  - eapply (allocfn_sec DI AQ AFK HL PR CI CI_OK CI_OK2); eassumption.
Qed.
End S.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.APoisonR_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASec.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_amalloc_arep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ACallocG__A3W.AMallocPG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acallocS__A3W.AMallocS.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.AFn_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ACallocG__A3W.AAllocFnPG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acallocS__A3W.AAllocFnS.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section S.
Variable DI : ADepotIface.
Variables (AQ : alayout -> astate -> aconc -> amem -> Prop) (AFK : alayout -> list ablock -> amem -> Prop).
Hypothesis HL : ahole_laws (AH DI AQ ASEC_of AFK).
Hypothesis PR : poison_remap_stmt.
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI) CI.
Hypothesis CI_OK2 : Forall (fun iv => snd iv <= AINSTANCE \/ AINSTANCE + 728 <= fst iv) CI.

#[using="HL PR CI_OK CI_OK2"] Theorem allocfn_all : allocfn_stmt CI (AHEAP_P (AH DI AQ ASEC_of AFK)).
Proof.
  unfold allocfn_stmt. intros.
  destruct (is_primary n) eqn:P.
  - eapply (allocfn_prim DI AQ ASEC_of AFK HL CI CI_OK CI_OK2); eassumption.
  - eapply (allocfn_sec DI AQ AFK HL PR CI CI_OK CI_OK2); eassumption.
Qed.
End S.
End CANSEC1.
End TwB.
End AAllocFn.

(* [comment removed for export] *)
Module AMalloc.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Step Frame Arr ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase AMalloc_iface. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_apoison__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASec__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_amalloc_arep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_acallocS__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.APoisonR_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_amalloc_arep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ACallocG__A3W.AMallocPG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acallocS__A3W.AMallocS.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section S.
Variable DI : ADepotIface.
Variables (AQ : alayout -> astate -> aconc -> amem -> Prop) (AFK : alayout -> list ablock -> amem -> Prop).
Hypothesis HL : ahole_laws (AH DI AQ ASEC_of AFK).
Hypothesis PR : poison_remap_stmt.
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI) CI.
Hypothesis CI_OK2 : Forall (fun iv => snd iv <= AINSTANCE \/ AINSTANCE + 728 <= fst iv) CI.

#[using="HL PR CI_OK CI_OK2"] Theorem amalloc_all : amalloc_stmt CI (AHEAP_P (AH DI AQ ASEC_of AFK)).
Proof.
  unfold amalloc_stmt. intros.
  destruct (is_primary n) eqn:P.
  - eapply (amalloc_prim DI AQ ASEC_of AFK HL CI CI_OK CI_OK2); eassumption.
  - eapply (amalloc_sec DI AQ AFK HL PR CI CI_OK CI_OK2); eassumption.
Qed.
End S.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.APoisonR_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASec.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_amalloc_arep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ACallocG__A3W.AMallocPG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acallocS__A3W.AMallocS.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section S.
Variable DI : ADepotIface.
Variables (AQ : alayout -> astate -> aconc -> amem -> Prop) (AFK : alayout -> list ablock -> amem -> Prop).
Hypothesis HL : ahole_laws (AH DI AQ ASEC_of AFK).
Hypothesis PR : poison_remap_stmt.
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI) CI.
Hypothesis CI_OK2 : Forall (fun iv => snd iv <= AINSTANCE \/ AINSTANCE + 728 <= fst iv) CI.

#[using="HL PR CI_OK CI_OK2"] Theorem amalloc_all : amalloc_stmt CI (AHEAP_P (AH DI AQ ASEC_of AFK)).
Proof.
  unfold amalloc_stmt. intros.
  destruct (is_primary n) eqn:P.
  - eapply (amalloc_prim DI AQ ASEC_of AFK HL CI CI_OK CI_OK2); eassumption.
  - eapply (amalloc_sec DI AQ AFK HL PR CI CI_OK CI_OK2); eassumption.
Qed.
End S.
End CANSEC1.
End TwB.
End AMalloc.
