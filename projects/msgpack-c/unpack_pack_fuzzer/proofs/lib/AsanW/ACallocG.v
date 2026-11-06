(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require MM_syscalls WStr.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require SysStepF.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AImg AProto ABase AKit AKit2 ABytes AModelFacts ARep ARepKit ARepFrame ALayout AHeapP ARepExt ARefill_iface.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require ARefillP.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require APrimFacts.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_acache.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require RunDraw.
Module ACallocG.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Specs. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Exec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Tac. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.SysStep.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.MM_syscalls. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.WStr.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.SysStepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit2. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABytes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AModelFacts. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARep. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepKit. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepFrame. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ALayout. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AHeapP. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepExt. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARefill_iface.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARefillP.ARefillP. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.APrimFacts.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_acache.F_acache.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_acache.F_acache2.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_acache.F_acache3.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_acache.F_acache4.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT} {ov : annOV}.
Lemma rng_fp_leG : forall RNG RNG' lo n, fp_le RNG RNG' -> rng RNG lo n -> rng RNG' lo n.
Proof. intros RNG RNG' lo n LE (R1 & R2 & R3). split; [exact R1|]. split; [exact R2|]. intros b j Hb Hj. apply LE. apply R3; assumption. Qed.

End CANSEC1.
Notation CALLOC_STACK := 1584 (only parsing).
Notation calloc_W L st c sp :=
  ([(sp - CALLOC_STACK, sp);
    (al_t L + 208, al_t L + 3168);
    (AINSTANCE, AINSTANCE + 728);
    (aregion_info L c, aregion_info L c + 128);
    (aregion L c + c_mapped_user (get_cls st c), aregion L c + K_REGION);
    (shad (aregion L c + c_mapped_user (get_cls st c)), shad (aregion L c) + shlen K_REGION)]%Z) (only parsing).

Section CANSEC2. Context {rc : runConstT} {ov : annOV}.
Section Calloc.
Variable H : aholes.
Hypothesis HL : ahole_laws H.

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

Lemma calloc_read_gen : forall L st X m c cnt,
  alayout_ok L -> AREP H L st X m -> 1 <= c <= 30 -> c_count (get_cls st c) = cnt -> 0 < cnt ->
  exists k chunks stj,
       nth_error (xc_cache (x_cls X c)) (Z.to_nat (cnt - 1)) = Some k /\ busy_of X c k = None /\ 0 <= k < ndist st c
    /\ rw_cells asegs m (al_t L + 208 + c * 80) [C4 (Z_to_bv 64 cnt); C4 (Z_to_bv 64 (max_count st c)); C8 (Z_to_bv 64 (size_of_class c))]
    /\ u32arr asegs m (al_t L + 208 + c * 80 + 16) chunks /\ length chunks = 16%nat
    /\ nth_error chunks (Z.to_nat (cnt - 1)) = Some (Z_to_bv 64 (acompact c k)) /\ bv_unsigned (Z_to_bv 64 (acompact c k)) < 2^32
    /\ aslot_addr L c k = al_space_beg L + c * 2^32 + 16 * bv_unsigned (Z_to_bv 64 (acompact c k))
    /\ rw_cells asegs m 0xd6478 [C8 (Z_to_bv 64 (al_space_beg L))]
    /\ rw_cells asegs m (al_t L + 2784) [C8 stj]
    /\ cnt <= 16
    /\ iclr (al_t L) 4096 /\ al_t L + 4096 <= ATOP /\ al_t L mod 4096 = 0 /\ 0 <= al_space_beg L < 2^47.
Proof.
  intros L st X m c cnt ALO AR C16 HCNT POS.
  assert (HCK : 1 <= c < K_NUM_CLASSES) by (unfold K_NUM_CLASSES; lia).
  destruct (kit_cache_pop H L st X m c cnt AR HCK HCNT POS) as (k & chunks & NK & NB & KR & CR & CH & LCH & NTH & JK & FSH).
  pose proof AR as AR0. destruct AR0 as (WF & RT & INST & THR & CLS & HQ & HS & HD & HRO & RT2 & AVL & RT3).
  destruct THR as (T0 & T40 & CACHES & CSTATS & STATS & UNW).
  pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVE & FRESH & UNIQ).
  destruct (PERC c HCK) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & LENF & LENC & CNTB & ND & RANGE).
  pose proof (alayout_space L ALO) as (SP1 & SP2 & SP3 & SP4). pose proof (alayout_t L ALO) as (TL1 & TL2 & TL3 & TL4).
  destruct INST as (I32 & _). unfold AINSTANCE in I32.
  destruct (junk_split m (al_t L + 2768) 16 16 CSTATS ltac:(lia) ltac:(lia)) as [_ CSb].
  destruct (junk_split m (al_t L + 2768 + 16) 8 8 CSb ltac:(lia) ltac:(lia)) as [CS8 _].
  replace (al_t L + 2768 + 16) with (al_t L + 2784) in CS8 by lia. destruct (c8_of_junk m _ CS8) as [stj STS].
  pose proof (cls_facts c C16) as (SZB & SZM & MCB & _). set (S := size_of_class c) in *.
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
  destruct ACK as (ACK1 & ACK2 & ACK3).
  exists k, chunks, stj.
  split; [exact NK|]. split; [exact NB|]. split; [exact KR|]. split; [exact CR|]. split; [exact CH|]. split; [exact LCH|]. split; [exact NTH|].
  split; [rewrite ACK1; lia|].
  split; [rewrite ACK1; unfold aslot_addr, aregion, K_REGION; fold S; rewrite ACK3; clear; lia|].
  split; [exact I32|]. split; [exact STS|].
  split; [unfold max_count in CNTB; generalize CNTB MCB HCNT; clear; destruct (a_cinit st); intros; lia|].
  clear -TL1 TL2 TL3 TL4 SP4. split; [exact TL4|]. split; [exact TL2|]. split; [exact TL3| exact SP4].
Qed.

Theorem calloc_arep_gen : forall {R} (k : astate -> bool -> AM R) (Q : R -> footprint -> machine_state -> Prop)
    (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (X : aconc) (c lo size : Z),
  alayout_ok L -> arng L RNG st -> AREP H L st X m -> mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - CALLOC_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 AINSTANCE -> a1 = Z_to_bv 64 (al_t L + 208) -> a2 = Z_to_bv 64 size -> a3 = Z_to_bv 64 8 ->
  16 <= size <= 65536 -> size mod 8 = 0 -> class_id size = c ->
  c = K_BATCH_CLASS ->
  rng RNG lo (bv_unsigned sp - lo) ->
  (forall st_pre X_pre RNG1 m_pre cnt kk ms1,
     calloc_retG L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st X c lo m st_pre X_pre RNG1 m_pre cnt kk ms1 ->
     implS asegs RNG1 (aembed ATOP (k (apop c st_pre) true)) (epostF Q) ms1) ->
  implS asegs RNG (aembed ATOP (cache_alloc st c k)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x41420) fc None m (seg_rom asegs)).
Proof.
  intros R k Q L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st X c lo size
         ALO ARNG AR MI ST CEIL LO TP Ha0 Ha1 Ha2 Ha3 SZ M8 HC HC24 RSTK KONT.
  assert (C16 : 1 <= c <= 30) by (pose proof (class_facts size ltac:(clear -SZ; lia)) as CF; cbv zeta in CF; rewrite HC in CF; clear -CF; lia).
  assert (HCK : 1 <= c < K_NUM_CLASSES) by (unfold K_NUM_CLASSES; lia).
  pose proof AR as AR0. destruct AR0 as (WF & RT & INST & THR & CLS & HQ & HS & HD & HRO & RT2 & AVL & RT3).
  destruct THR as (T0 & T40 & CACHES & CSTATS & STATS & UNW).
  pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVE & FRESH & UNIQ).
  destruct (PERC c HCK) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & LENF & LENC & CNTB & ND & RANGE).
  pose proof (alayout_space L ALO) as (SP1 & SP2 & SP3 & SP4). pose proof (alayout_t L ALO) as (TL1 & TL2 & TL3 & TL4).
  pose proof ARNG as ARNG0. destruct ARNG as (RIMG & RT4 & RCTX & RNO & RSTO & RRI & RFK & RSFK & RDTLS & RCLS & RPA & RSECS & RPSH).
  word_range sp SPR.
  assert (ACE : acache_addr L c = al_t L + 208 + c * 80) by reflexivity.
  rewrite cache_alloc_unfold.
  destruct (Z.ltb_spec 0 (c_count (get_cls st c))) as [POS|NPOS].
  -
    change (put_cls c (cls_set_count (c_count (get_cls st c) - 1) (get_cls st c)) st) with (apop c st).
    destruct (calloc_read_gen L st X m c (c_count (get_cls st c)) ALO AR C16 eq_refl POS)
      as (kk & chunks & stj & NK & NB & KR & CR & CH & LCH & NTH & IXS & HAB & I32 & STS & CNT16 & T0' & T1' & TAL & SBR).
    iprefix. eapply evtF_cut.
    { eapply (calloc_hit_gen RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                F fc m (al_t L) size c (c_count (get_cls st c)) (al_space_beg L) lo _ _ stj chunks (Z_to_bv 64 (acompact c kk)));
        first [exact ST | exact CEIL | exact MI | exact Ha0 | exact Ha1 | exact Ha2 | exact Ha3 | exact SZ | exact M8 | exact HC | exact I32 | exact CR | exact CH
              | exact LCH | exact NTH | exact IXS | exact STS | exact T0' | exact T1' | exact TAL | exact SBR | exact RIMG | exact RSTK | exact RT4 | lia]. }
    cbv beta. intros ms1 P1. apply evtF_done. apply (KONT st X RNG m (c_count (get_cls st c)) kk).
    unfold cache_hit_post in P1.
    destruct P1 as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> & MU1 & WM1 & MI1 & ST1 & CR1 & [stj' STS1]).
    replace (al_t L + 2784 + 8) with (al_t L + 2792) in MU1 by lia.
    unfold calloc_retG.
    split; [apply fp_le_refl|]. split; [exact AR|]. split; [exact ARNG0|].
    split; [reflexivity|]. split; [exact POS|]. split; [exact NK|]. split; [exact NB|]. split; [exact KR|].
    split; [reflexivity|]. do 8 (split; [reflexivity|]).
    split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact MI|].
    do 14 eexists. exists m1, stj'. split; [rewrite HAB; reflexivity|].
    split; [rewrite ACE; exact MU1|]. split; [exact WM1|]. split; [exact MI1|]. split; [exact ST1|]. split; [rewrite ACE; exact CR1| exact STS1].
  -
    assert (CNT0 : c_count (get_cls st c) = 0) by lia.
    destruct (CACHES c HCK) as [tl (RH & RCH & RLEN)]. rewrite CNT0 in RH. rewrite ACE in RH.
    iprefix. eapply evtF_cut.
    { eapply (calloc_pre_gen RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                F fc m (al_t L) size c lo);
        first [exact ST | exact CEIL | exact MI | exact Ha0 | exact Ha1 | exact Ha2 | exact Ha3 | exact SZ | exact M8 | exact HC | exact RH | exact TL4 | exact TL2 | exact RIMG | exact RSTK | exact RT4
              | clear -LO; lia]. }
    cbv beta. intros msp Pp. apply evtF_done. unfold calloc_pre_post in Pp.
    destruct Pp as (t0p & t1p & t2p & a4p & a5p & a6p & a7p & t3p & t4p & t5p & t6p & mp & -> & MUp & WMp & MIp & STp & FRp).
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
         | |- _ = K_BATCH_CLASS => exact HC24
         | |- c_count _ = 0 => exact CNT0
         | |- rng _ _ _ => rewrite unsigned_lit by lia; eapply rng_sub'; [exact RSTK|]; lia
         end.

    intros st_r X' RNG' ms' RR. unfold ARefill_iface.refill_ret in RR.
    destruct RR as (FPLE & t0r & t1r & t2r & a1r & a2r & a3r & a4r & a5r & a6r & a7r & t3r & t4r & t5r & t6r & mr
                    & -> & MUr & WMr & MIr & STr & ARr & ARNGr & CIN & CCNT & NPOS' & XB & XC & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & GC).
    rewrite ?unsigned_lit in MUr by lia. rewrite ?unsigned_lit in STr by lia.
    replace (ret_pc (Z_to_bv 64 0x416d0)) with (Z_to_bv 64 0x416d0) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    remember (c_count (get_cls st_r c)) as cnt eqn:HCNT. symmetry in HCNT.
    destruct (calloc_read_gen L st_r X' mr c cnt ALO ARr C16 HCNT ltac:(lia))
      as (kk & chunks & stj & NK & NB & KR & CR & CH & LCH & NTH & IXS & HAB & I32 & STS & CNT16 & T0' & T1' & TAL & SBR).
    pose proof ARNGr as ARNGr0. destruct ARNGr as (RIMG' & RT4' & RCTX' & RNO' & RSTO' & RRI' & RFK' & RSFK' & RDTLS' & RCLS' & RPA' & RSECS' & RPSH').
    assert (OBJ : aregion_info L c + 128 <= ATOP /\ aregion L c + K_REGION <= ATOP /\ shad (aregion L c) + shlen K_REGION <= 17594333495296).
    { unfold aregion_info, aregion, K_REGION, K_SPACE_SIZE, K_SPACE_EXTRA, ARI_STRIDE in *. change (2^37) with 137438953472 in *. change (2^32) with 4294967296 in *.
      rewrite shad_div, shlen_div. unfold ASHOFF. clear -SP1 SP2 C16. Z.div_mod_to_equations. lia. }
    destruct OBJ as (OB1 & OB2 & OB3).
    xport FRp MUr WMr ltac:(unfold AINSTANCE in *; clear -SPR CEIL LO TL1 TL2 OB1 OB2 OB3; lia).
    iprefix. eapply evtF_cut.
    { eapply (calloc_popj_gen RNG' sp gp tp t0r t1r t2r a1r a2r a3r a4r a5r a6r a7r s5 s6 s7 s8 s9 s10 s11 t3r t4r t5r t6r
                ra s0 s1 s2 s3 s4 (Z_to_bv 64 1) F fc mr (al_t L) c cnt (al_space_beg L) lo _ _ stj chunks (Z_to_bv 64 (acompact c kk)));
        first [ replace (bv_unsigned sp - 48) with (bv_unsigned sp + -48) by lia; exact STr
              | exact CEIL | exact MIr | exact C16 | exact FRp | exact I32 | exact CR | exact CH | exact LCH | exact NTH | exact IXS | exact STS
              | exact T0' | exact T1' | exact TAL | exact SBR | exact RIMG' | exact RT4'
              | rewrite unsigned_lit by lia; lia
              | eapply rng_fp_leG; [exact FPLE | exact RSTK]
              | lia ]. }
    cbv beta. intros ms1 P1. apply evtF_done. apply (KONT st_r X' RNG' mr cnt kk).
    unfold cache_hit_post in P1.
    destruct P1 as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> & MU1 & WM1 & MI1 & ST1 & CR1 & [stj' STS1]).
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
End Calloc.
End CANSEC2.
End ACallocG.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AMalloc_iface AEmbRep AFrameD AEmbFrame.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_arefill.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require ARefill_iface_x ARefillP_x.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_acache_x.
Module ACallocG_x.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Specs. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Exec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Tac. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.SysStep.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.MM_syscalls. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.WStr.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.SysStepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit2. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABytes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AModelFacts. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARep. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepKit. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepFrame. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ALayout. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AHeapP. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepExt. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARefill_iface.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARefillP.ARefillP. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.APrimFacts.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_acache.F_acache.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_acache.F_acache2.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_acache.F_acache3.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_acache.F_acache4. Import ACallocG. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AMalloc_iface. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AEmbRep. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFrameD. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AEmbFrame.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_arefill.F_arefill_x. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARefill_iface_x. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARefillP_x.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARefillP.ARefillP_e. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_acache_x.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation CALLOC_STACK_X := 2096 (only parsing).

Section CANSEC2. Context {rc : runConstT} {ov : annOV}.

Lemma axg_frame_hi : forall RESV RNG st m m' (W : list (Z * Z)), axg RESV RNG st m -> munch W m m' -> Forall (fun iv => ATOP <= fst iv) W -> axg RESV RNG st m'.
Proof.
  intros RESV RNG st m m' W (XC & EC & ER & ECL) MU HW. pose proof atop_range as AT.
  assert (HW' : Forall (fun iv : Z * Z => AIMG_HI <= fst iv) W) by (eapply Forall_impl; [| exact HW]; intros iv Hv; unfold AIMG_HI; cbn beta in *; lia).
  assert (DJ : forall A k, A + k <= ATOP -> disjoint_from W A k).
  { clear -HW. induction W as [|[lo hi] W IH]; intros A k HA; cbn; [exact I|]. inversion HW as [|? ? H1 H2]; subst. cbn [fst] in H1. split; [lia| apply IH; assumption]. }
  split; [eapply exh_cells_frameD; [exact XC| exact MU| exact HW']|]. split; [| split; [exact ER| exact ECL]].
  eapply emb_cells_frameD; [exact EC| exact MU| apply DJ; unfold AEMB; lia|].
  pose proof EC as EC1. unfold emb_cells in EC1. destruct (a_emb st) as [[d cap] sz]. destruct (Z.eqb_spec cap 0) as [E0|NZ]; [left; exact E0| right].
  destruct EC1 as (_ & _ & _ & _ & _ & _ & _ & _ & TOP & _). apply DJ. exact TOP.
Qed.
Lemma axflag_frame_hi : forall L st m m' c (W : list (Z * Z)), axflag L st m c -> munch W m m' -> Forall (fun iv => ATOP <= fst iv) W ->
  aregion_info L c + 128 <= ATOP -> axflag L st m' c.
Proof.
  intros L st m m' c W AF MU HW RIT. unfold axflag in *. eapply cells_frameD; [exact AF| exact MU|]. cbn [cells_size csize Nat.add].
  clear -HW RIT. induction W as [|[lo hi] W IH]; cbn; [exact I|]. inversion HW as [|? ? H1 H2]; subst. cbn [fst] in H1. split; [lia| apply IH; assumption].
Qed.

Section CallocX.
Variable H : aholes.
Hypothesis HL : ahole_laws H.
Hypothesis HLD : ahole_lawsD H.

Definition calloc_retG_x (L : alayout) (RESV : list (Z * Z)) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : astate) (X : aconc) (c lo : Z) (m : amem)
    (st_pre : astate) (X_pre : aconc) (RNG1 : footprint) (m_pre : amem) (cnt k : Z) (ms1 : machine_state) : Prop :=
  calloc_retG H L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st X c lo m st_pre X_pre RNG1 m_pre cnt k ms1
  /\ a_emb st_pre = a_emb st /\ (a_exh st_pre = a_exh st \/ a_exh st_pre = a_exh (exh_clear c st))
  /\ (c <> K_BATCH_CLASS -> axflag L st_pre m_pre c) /\ axg RESV RNG1 st_pre m_pre.

Theorem calloc_arep_gen_x : forall {R} (RESV : list (Z * Z)) (k : astate -> bool -> AM R) (Q : R -> footprint -> machine_state -> Prop)
    (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (X : aconc) (c lo size : Z),
  alayout_ok L -> arng L RNG st -> AREP H L st X m -> mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - CALLOC_STACK_X ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 AINSTANCE -> a1 = Z_to_bv 64 (al_t L + 208) -> a2 = Z_to_bv 64 size -> a3 = Z_to_bv 64 8 ->
  16 <= size <= 65536 -> size mod 8 = 0 -> class_id size = c ->
  rng RNG lo (bv_unsigned sp - lo) ->

  exh_first_stmt -> aresv_ok L RESV -> bv_unsigned sp < 2 ^ 63 -> bv_unsigned fc < 32 ->
  (c <> K_BATCH_CLASS -> axflag L st m c) -> axg RESV RNG st m -> (let '(_, cap0, _) := a_emb st in cap0 <= 2 ^ 23) ->
  (forall st2 RNG' ms',
     aret_xf H L RESV RNG CALLOC_STACK_X ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st X c lo m st2 RNG' ms' ->
     implS asegs RNG' (aembed ATOP (k st2 false)) (epostF Q) ms') ->
  (forall st_pre X_pre RNG1 m_pre cnt kk ms1,
     calloc_retG_x L RESV RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st X c lo m st_pre X_pre RNG1 m_pre cnt kk ms1 ->
     implS asegs RNG1 (aembed ATOP (k (apop c st_pre) true)) (epostF Q) ms1) ->
  implS asegs RNG (aembed ATOP (cache_alloc_x ATOP RESV st c k)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x41420) fc None m (seg_rom asegs)).
Proof.
  intros R RESV k Q L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st X c lo size
         ALO ARNG AR MI ST CEIL LO TP Ha0 Ha1 Ha2 Ha3 SZ M8 HC RSTK EXHW ARV SP63 FC AXF AXG CAPB KONTF KONT.
  assert (C16 : 1 <= c <= 30) by (pose proof (class_facts size ltac:(clear -SZ; lia)) as CF; cbv zeta in CF; rewrite HC in CF; clear -CF; lia).
  assert (HCK : 1 <= c < K_NUM_CLASSES) by (unfold K_NUM_CLASSES; lia).
  pose proof AR as AR0. destruct AR0 as (WF & RT & INST & THR & CLS & HQ & HS & HD & HRO & RT2 & AVL & RT3).
  destruct THR as (T0 & T40 & CACHES & CSTATS & STATS & UNW).
  pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVE & FRESH & UNIQ).
  destruct (PERC c HCK) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & LENF & LENC & CNTB & ND & RANGE).
  pose proof (alayout_space L ALO) as (SP1 & SP2 & SP3 & SP4). pose proof (alayout_t L ALO) as (TL1 & TL2 & TL3 & TL4).
  pose proof ARNG as ARNG0. destruct ARNG as (RIMG & RT4 & RCTX & RNO & RSTO & RRI & RFK & RSFK & RDTLS & RCLS & RPA & RSECS & RPSH).
  word_range sp SPR.
  assert (ACE : acache_addr L c = al_t L + 208 + c * 80) by reflexivity.
  assert (OBJ : aregion_info L c + 128 <= ATOP /\ aregion L c + K_REGION <= ATOP /\ shad (aregion L c) + shlen K_REGION <= 17594333495296).
  { unfold aregion_info, aregion, K_REGION, K_SPACE_SIZE, K_SPACE_EXTRA, ARI_STRIDE in *. change (2^37) with 137438953472 in *. change (2^32) with 4294967296 in *.
    rewrite shad_div, shlen_div. unfold ASHOFF. clear -SP1 SP2 C16. Z.div_mod_to_equations. lia. }
  destruct OBJ as (OB1 & OB2 & OB3).
  rewrite cache_alloc_x_unfold.
  destruct (Z.ltb_spec 0 (c_count (get_cls st c))) as [POS|NPOS].
  -
    change (put_cls c (cls_set_count (c_count (get_cls st c) - 1) (get_cls st c)) st) with (apop c st).
    destruct (calloc_read_gen H L st X m c (c_count (get_cls st c)) ALO AR C16 eq_refl POS)
      as (kk & chunks & stj & NK & NB & KR & CR & CH & LCH & NTH & IXS & HAB & I32 & STS & CNT16 & T0' & T1' & TAL & SBR).
    iprefix. eapply evtF_cut.
    { eapply (calloc_hit_gen RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                F fc m (al_t L) size c (c_count (get_cls st c)) (al_space_beg L) lo _ _ stj chunks (Z_to_bv 64 (acompact c kk)));
        first [exact ST | exact CEIL | exact MI | exact Ha0 | exact Ha1 | exact Ha2 | exact Ha3 | exact SZ | exact M8 | exact HC | exact I32 | exact CR | exact CH
              | exact LCH | exact NTH | exact IXS | exact STS | exact T0' | exact T1' | exact TAL | exact SBR | exact RIMG | exact RSTK | exact RT4 | lia]. }
    cbv beta. intros ms1 P1. apply evtF_done. apply (KONT st X RNG m (c_count (get_cls st c)) kk).
    unfold cache_hit_post in P1.
    destruct P1 as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> & MU1 & WM1 & MI1 & ST1 & CR1 & [stj' STS1]).
    replace (al_t L + 2784 + 8) with (al_t L + 2792) in MU1 by lia.
    unfold calloc_retG_x. split; [| split; [reflexivity| split; [left; reflexivity| split; [exact AXF| exact AXG]]]].
    unfold calloc_retG.
    split; [apply fp_le_refl|]. split; [exact AR|]. split; [exact ARNG0|].
    split; [reflexivity|]. split; [exact POS|]. split; [exact NK|]. split; [exact NB|]. split; [exact KR|].
    split; [reflexivity|]. do 8 (split; [reflexivity|]).
    split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact MI|].
    do 14 eexists. exists m1, stj'. split; [rewrite HAB; reflexivity|].
    split; [rewrite ACE; exact MU1|]. split; [exact WM1|]. split; [exact MI1|]. split; [exact ST1|]. split; [rewrite ACE; exact CR1| exact STS1].
  -
    assert (CNT0 : c_count (get_cls st c) = 0) by lia.
    destruct (CACHES c HCK) as [tl (RH & RCH & RLEN)]. rewrite CNT0 in RH. rewrite ACE in RH.
    iprefix. eapply evtF_cut.
    { eapply (calloc_pre_gen RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                F fc m (al_t L) size c lo);
        first [exact ST | exact CEIL | exact MI | exact Ha0 | exact Ha1 | exact Ha2 | exact Ha3 | exact SZ | exact M8 | exact HC | exact RH | exact TL4 | exact TL2 | exact RIMG | exact RSTK | exact RT4
              | clear -LO; lia]. }
    cbv beta. intros msp Pp. apply evtF_done. unfold calloc_pre_post in Pp.
    destruct Pp as (t0p & t1p & t2p & a4p & a5p & a6p & a7p & t3p & t4p & t5p & t6p & mp & -> & MUp & WMp & MIp & STp & FRp).
    assert (ARp : AREP H L st X mp).
    { eapply (AREP_frame_ext H HL L st X m mp); [exact ALO | exact AR | exact MUp | exact WMp |].
      apply Forall_cons; [cbn [fst snd]; intros _; right; right; atop_facts; lia | apply Forall_nil]. }
    assert (HWp : Forall (fun iv : Z * Z => ATOP <= fst iv) [(bv_unsigned sp - 48, bv_unsigned sp)]) by (constructor; [cbn [fst]; clear -CEIL LO; lia| constructor]).
    assert (AXGp : axg RESV RNG st mp) by (eapply axg_frame_hi; [exact AXG| exact MUp| exact HWp]).
    destruct (Z.eq_dec c K_BATCH_CLASS) as [C24|NC24].
    +
      assert (TREE : cache_refill_tree_x RESV st c k = cache_refill_tree st c k).
      { unfold cache_refill_tree_x, cache_refill_tree, populate_free_array_x. rewrite C24, Z.eqb_refl. reflexivity. }
      rewrite TREE.
      eapply (arefillP_e H HL _ k Q L RNG _ _ gp tp t0p t1p t2p _ _ _ _ _ _ a4p a5p a6p a7p _ _ _ s5 s6 s7 s8 s9 s10 s11 t3p t4p t5p t6p F fc mp st X c lo
                ALO ARNG0 ARp MIp).
      all: try lazymatch goal with
           | |- arng _ _ _ => exact ARNG0
           | |- stk _ _ _ _ => rewrite unsigned_lit by lia; replace (bv_unsigned sp + -48) with (bv_unsigned sp - 48) by lia; exact STp
           | |- ATOP <= _ => exact CEIL
           | |- _ <= bv_unsigned _ - _ => rewrite unsigned_lit by lia; lia
           | |- @eq word _ _ => first [exact TP | reflexivity | rewrite ACE; reflexivity]
           | |- _ = K_BATCH_CLASS => exact C24
           | |- c_count _ = 0 => exact CNT0
           | |- rng _ _ _ => rewrite unsigned_lit by lia; eapply rng_sub'; [exact RSTK|]; lia
           end.
      intros st_r X' RNG' ms' [RR [EMBr EXHr]]. unfold ARefill_iface.refill_ret in RR.
      destruct RR as (FPLE & t0r & t1r & t2r & a1r & a2r & a3r & a4r & a5r & a6r & a7r & t3r & t4r & t5r & t6r & mr
                      & -> & MUr & WMr & MIr & STr & ARr & ARNGr & CIN & CCNT & NPOS' & XB & XC & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & GC).
      rewrite ?unsigned_lit in MUr by lia. rewrite ?unsigned_lit in STr by lia.
      replace (ret_pc (Z_to_bv 64 0x416d0)) with (Z_to_bv 64 0x416d0) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      remember (c_count (get_cls st_r c)) as cnt eqn:HCNT. symmetry in HCNT.
      destruct (calloc_read_gen H L st_r X' mr c cnt ALO ARr C16 HCNT ltac:(lia))
        as (kk & chunks & stj & NK & NB & KR & CR & CH & LCH & NTH & IXS & HAB & I32 & STS & CNT16 & T0' & T1' & TAL & SBR).
      pose proof ARNGr as ARNGr0. destruct ARNGr as (RIMG' & RT4' & RCTX' & RNO' & RSTO' & RRI' & RFK' & RSFK' & RDTLS' & RCLS' & RPA' & RSECS' & RPSH').

      assert (AXGr : axg RESV RNG' st_r mr).
      { destruct AXGp as (XCp & ECp & ERp & ECLp).
        assert (MU0 : 0 <= c_mapped_user (get_cls st c)) by (clear -A1; lia).
        assert (MUK : c_mapped_user (get_cls st c) <= K_REGION) by (unfold K_REGION, K_FREEARR_OFF in *; change (2^32) with 4294967296; clear -A2; lia).
        assert (LOr : lo <= bv_unsigned sp - 48 - 1536) by (clear -LO; lia).
        pose proof (arefillW_img L st c (bv_unsigned sp - 48) lo ALO HCK CEIL LOr MU0) as KI.
        destruct (a_emb st) as [[d0 cap0] sz0] eqn:EA.
        split; [eapply exh_cells_frameK; [exact XCp| exact MUr| exact KI]|].
        assert (EC' : emb_cells st mr).
        { eapply emb_cells_frameD; [exact ECp| exact MUr| apply KI; clear; unfold AEMB, AIMG_LO, AIMG_HI, AINSTANCE; lia|]. rewrite EA.
          destruct (Z.eqb_spec cap0 0) as [E0|NZ]; [left; exact E0| right].
          pose proof ECp as EC1. unfold emb_cells in EC1. rewrite EA in EC1. replace (cap0 =? 0) with false in EC1 by (symmetry; apply Z.eqb_neq; exact NZ).
          destruct EC1 as (_ & _ & _ & _ & P2 & _ & _ & P5 & P6 & _).
          unfold emb_clr in ECLp. rewrite EA in ECLp. destruct ECLp as [QQ|AV]; [exfalso; exact (NZ QQ)|].
          unfold avoids_all in AV. rewrite forallb_app in AV. apply andb_prop in AV as [AV _].
          apply (arefillW_buf L RESV st c (bv_unsigned sp - 48) lo ALO HCK CEIL LOr MU0 d0 cap0 ARV MUK); [unfold EMB_INIT in P2; clear -P2; lia| exact P5| exact P6| exact AV]. }
        split; [unfold emb_cells in EC' |- *; rewrite EMBr; rewrite EA in EC'; exact EC'|].
        split; [unfold emb_rng in ERp |- *; rewrite EMBr; rewrite EA in ERp; destruct ERp as [QQ|QQ]; [left; exact QQ| right; exact (rng_fp_leG _ _ _ _ FPLE QQ)]|].
        unfold emb_clr in ECLp |- *. rewrite EMBr. rewrite EA in ECLp.
        assert (ACH : achunks st_r = achunks st) by (unfold achunks; rewrite L1, L3, L5; reflexivity).
        rewrite ACH. exact ECLp. }
      xport FRp MUr WMr ltac:(unfold AINSTANCE in *; clear -SPR CEIL LO TL1 TL2 OB1 OB2 OB3; lia).
      iprefix. eapply evtF_cut.
      { eapply (calloc_popj_gen RNG' sp gp tp t0r t1r t2r a1r a2r a3r a4r a5r a6r a7r s5 s6 s7 s8 s9 s10 s11 t3r t4r t5r t6r
                  ra s0 s1 s2 s3 s4 (Z_to_bv 64 1) F fc mr (al_t L) c cnt (al_space_beg L) lo _ _ stj chunks (Z_to_bv 64 (acompact c kk)));
          first [ replace (bv_unsigned sp - 48) with (bv_unsigned sp + -48) by lia; exact STr
                | exact CEIL | exact MIr | exact C16 | exact FRp | exact I32 | exact CR | exact CH | exact LCH | exact NTH | exact IXS | exact STS
                | exact T0' | exact T1' | exact TAL | exact SBR | exact RIMG' | exact RT4'
                | rewrite unsigned_lit by lia; lia
                | eapply rng_fp_leG; [exact FPLE | exact RSTK]
                | lia ]. }
      cbv beta. intros ms1 P1. apply evtF_done. apply (KONT st_r X' RNG' mr cnt kk).
      unfold cache_hit_post in P1.
      destruct P1 as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> & MU1 & WM1 & MI1 & ST1 & CR1 & [stj' STS1]).
      replace (al_t L + 2784 + 8) with (al_t L + 2792) in MU1 by lia.
      unfold calloc_retG_x. split; [| split; [exact EMBr| split; [left; exact EXHr| split; [intros NE; exfalso; exact (NE C24)| exact AXGr]]]].
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
    +
      assert (AXFp : axflag L st mp c) by (eapply axflag_frame_hi; [exact (AXF NC24)| exact MUp| exact HWp| exact OB1]).
      eapply (arefill_x H HL HLD _ RESV k Q L RNG _ _ gp tp t0p t1p t2p _ _ _ _ _ _ a4p a5p a6p a7p _ _ _ s5 s6 s7 s8 s9 s10 s11 t3p t4p t5p t6p F fc mp st X c lo
                ALO ARNG0 ARp MIp).
      all: try lazymatch goal with
           | |- implS _ _ _ _ _ => idtac
           | |- forall _, _ => idtac
           | |- arng _ _ _ => exact ARNG0
           | |- exh_first_stmt => exact EXHW
           | |- aresv_ok _ _ => exact ARV
           | |- axflag _ _ _ _ => exact AXFp
           | |- axg _ _ _ _ => exact AXGp
           | |- context [a_emb _] => exact CAPB
           | |- bv_unsigned _ < 2 ^ 63 => rewrite unsigned_lit by lia; clear -SP63 SPR; lia
           | |- bv_unsigned _ < 32 => exact FC
           | |- stk _ _ _ _ => rewrite unsigned_lit by lia; replace (bv_unsigned sp + -48) with (bv_unsigned sp - 48) by lia; exact STp
           | |- ATOP <= _ => exact CEIL
           | |- _ <= bv_unsigned _ - _ => rewrite unsigned_lit by lia; lia
           | |- @eq word _ _ => first [exact TP | reflexivity | rewrite ACE; reflexivity]
           | |- 1 <= _ < _ => exact HCK
           | |- _ <> K_BATCH_CLASS => exact NC24
           | |- c_count _ = 0 => exact CNT0
           | |- rng _ _ _ => rewrite unsigned_lit by lia; eapply rng_sub'; [exact RSTK|]; lia
           end.
      *
        intros st2 RNG' ms' RF. unfold refill_ret_xf, aret_xf in RF. cbv zeta in RF.
        pose proof AXGp as (_ & ECp & _). unfold emb_cells in ECp.
        destruct (a_emb st) as [[d0 cap0] sz0] eqn:EA. destruct (a_emb st2) as [[d2 cap2] sz2] eqn:EA2.
        destruct RF as (FPLE & t0r & t1r & t2r & a1r & a2r & a3r & a4r & a5r & a6r & a7r & t3r & t4r & t5r & t6r & mr
                        & -> & MIr & STr & STEQ & ARr & ARNGr & AXFr & AXGr & (d1 & cap1 & MUr & PV1 & PV2 & TOP1)).
        rewrite ?unsigned_lit in MUr by lia. rewrite ?unsigned_lit in STr by lia.
        replace (ret_pc (Z_to_bv 64 0x416d0)) with (Z_to_bv 64 0x416d0) by (symmetry; apply ret_pc_even; [lia|reflexivity]).

        assert (B0 : cap0 <= 0 \/ d0 + cap0 <= ATOP).
        { destruct (Z.eqb_spec cap0 0) as [E0|NZ]; [left; lia| right]. destruct ECp as (_ & _ & _ & _ & _ & _ & _ & _ & TOP & _). exact TOP. }
        assert (B2 : cap2 <= 0 \/ d2 + cap2 <= ATOP).
        { pose proof AXGr as (_ & EC2 & _). unfold emb_cells in EC2. rewrite EA2 in EC2.
          destruct (Z.eqb_spec cap2 0) as [E0|NZ]; [left; lia| right]. destruct EC2 as (_ & _ & _ & _ & _ & _ & _ & _ & TOP & _). exact TOP. }
        assert (B1 : cap1 <= 0 \/ d1 + cap1 <= ATOP) by (destruct TOP1 as [Q0|Q1]; [left; lia| right; exact Q1]).
        assert (FRr : rw_cells asegs mr (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
        { eapply cells_frameO; [exact FRp| exact MUr|]. cbn [cells_size csize Nat.add]. intros x Hx. cbn [outside].
          unfold AEMB. pose proof atop_range as AT. clear -Hx B0 B1 B2 CEIL LO TL2 OB1 AT SPR. repeat split; lia. }
        pose proof ARNGr as (RIMG' & _).
        iprefix. eapply evtF_cut.
        { eapply (calloc_nullj_gen RNG' sp gp tp t0r t1r t2r a1r a2r a3r a4r a5r a6r a7r s5 s6 s7 s8 s9 s10 s11 t3r t4r t5r t6r
                    ra s0 s1 s2 s3 s4 _ _ _ _ F fc mr lo);
            first [ replace (bv_unsigned sp - 48) with (bv_unsigned sp + -48) by lia; exact STr
                  | exact CEIL | exact MIr | exact FRr | exact RIMG'
                  | eapply rng_fp_leG; [exact FPLE | exact RSTK]
                  | clear -LO; lia ]. }
        cbv beta. intros ms1 P1. apply evtF_done. apply (KONTF st2 RNG').
        unfold calloc_null_post in P1.
        destruct P1 as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & -> & ST1).
        unfold aret_xf. cbv zeta. rewrite EA, EA2.
        split; [exact FPLE|]. do 14 eexists. exists mr. split; [reflexivity|]. split; [exact MIr|]. split; [exact ST1|].
        split; [exact STEQ|]. split; [exact ARr|]. split; [exact ARNGr|]. split; [exact AXFr|]. split; [exact AXGr|].
        exists d1, cap1. split; [| split; [exact PV1| split; [exact PV2| exact TOP1]]].
        eapply munch_trans; [eapply munch_weaken; [| exact MUp] | eapply munch_weaken; [| exact MUr]];
          unfold sub_fp; cbn [outside]; intros q Hq.
        -- clear -Hq. lia.
        -- destruct Hq as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & _). split; [clear -X1; lia|]. repeat (split; [assumption|]). exact I.
      *
        intros st_r X' RNG' ms' RR. unfold refill_ret_xt in RR.
        destruct RR as (FPLE & t0r & t1r & t2r & a1r & a2r & a3r & a4r & a5r & a6r & a7r & t3r & t4r & t5r & t6r & mr
                        & -> & MUr & WMr & MIr & STr & ARr & ARNGr & CIN & CCNT & NPOS' & XB & XC & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & GC & EMBr & EXHr & AXFr & AXGr).
        rewrite ?unsigned_lit in MUr by lia. rewrite ?unsigned_lit in STr by lia.
        replace (ret_pc (Z_to_bv 64 0x416d0)) with (Z_to_bv 64 0x416d0) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
        remember (c_count (get_cls st_r c)) as cnt eqn:HCNT. symmetry in HCNT.
        destruct (calloc_read_gen H L st_r X' mr c cnt ALO ARr C16 HCNT ltac:(lia))
          as (kk & chunks & stj & NK & NB & KR & CR & CH & LCH & NTH & IXS & HAB & I32 & STS & CNT16 & T0' & T1' & TAL & SBR).
        pose proof ARNGr as ARNGr0. destruct ARNGr as (RIMG' & RT4' & RCTX' & RNO' & RSTO' & RRI' & RFK' & RSFK' & RDTLS' & RCLS' & RPA' & RSECS' & RPSH').
        xport FRp MUr WMr ltac:(unfold AINSTANCE in *; clear -SPR CEIL LO TL1 TL2 OB1 OB2 OB3; lia).
        iprefix. eapply evtF_cut.
        { eapply (calloc_popj_gen RNG' sp gp tp t0r t1r t2r a1r a2r a3r a4r a5r a6r a7r s5 s6 s7 s8 s9 s10 s11 t3r t4r t5r t6r
                    ra s0 s1 s2 s3 s4 (Z_to_bv 64 1) F fc mr (al_t L) c cnt (al_space_beg L) lo _ _ stj chunks (Z_to_bv 64 (acompact c kk)));
            first [ replace (bv_unsigned sp - 48) with (bv_unsigned sp + -48) by lia; exact STr
                  | exact CEIL | exact MIr | exact C16 | exact FRp | exact I32 | exact CR | exact CH | exact LCH | exact NTH | exact IXS | exact STS
                  | exact T0' | exact T1' | exact TAL | exact SBR | exact RIMG' | exact RT4'
                  | rewrite unsigned_lit by lia; lia
                  | eapply rng_fp_leG; [exact FPLE | exact RSTK]
                  | lia ]. }
        cbv beta. intros ms1 P1. apply evtF_done. apply (KONT st_r X' RNG' mr cnt kk).
        unfold cache_hit_post in P1.
        destruct P1 as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> & MU1 & WM1 & MI1 & ST1 & CR1 & [stj' STS1]).
        replace (al_t L + 2784 + 8) with (al_t L + 2792) in MU1 by lia.
        unfold calloc_retG_x. split; [| split; [exact EMBr| split; [exact EXHr| split; [intros _; exact AXFr| exact AXGr]]]].
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
End CallocX.
End CANSEC2.
End ACallocG_x.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require BImg.
Module TwinB.
Import stdpp.gmap.

Module ACallocG.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Specs. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Exec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Tac. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.SysStep.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.MM_syscalls. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.WStr.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.SysStepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW.BImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit2.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABytes.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AModelFacts.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARep.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepKit.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepFrame.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ALayout.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AHeapP.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepExt.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARefill_iface.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARefillP.TwinB.ARefillP. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.APrimFacts.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_acache.TwinB.F_acache.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_acache.TwinB.F_acache2.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_acache.TwinB.F_acache3.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_acache.TwinB.F_acache4.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT} {ov : annOV}.
Lemma rng_fp_leG : forall RNG RNG' lo n, fp_le RNG RNG' -> rng RNG lo n -> rng RNG' lo n.
Proof. intros RNG RNG' lo n LE (R1 & R2 & R3). split; [exact R1|]. split; [exact R2|]. intros b j Hb Hj. apply LE. apply R3; assumption. Qed.

End CANSEC1.
Notation CALLOC_STACK := 1584 (only parsing).
Notation calloc_W L st c sp :=
  ([(sp - CALLOC_STACK, sp);
    (al_t L + 208, al_t L + 3168);
    (AINSTANCE, AINSTANCE + 728);
    (aregion_info L c, aregion_info L c + 128);
    (aregion L c + c_mapped_user (get_cls st c), aregion L c + K_REGION);
    (shad (aregion L c + c_mapped_user (get_cls st c)), shad (aregion L c) + shlen K_REGION)]%Z) (only parsing).

Section CANSEC2. Context {rc : runConstT} {ov : annOV}.
Section Calloc.
Variable H : aholes.
Hypothesis HL : ahole_laws H.

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
  /\ munch (calloc_W L st c (bv_unsigned sp)) m m_pre /\ wmono bsegs m m_pre /\ mem_inv bsegs m_pre
  /\ exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m1 (stj' : word),
       ms1 = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (aslot_addr L c k)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (ret_pc ra) fc None m1 (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (acache_addr L c, acache_addr L c + 4); (al_t L + 2784, al_t L + 2792)]%Z m_pre m1
    /\ wmono bsegs m_pre m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo (bv_unsigned sp)
    /\ rw_cells bsegs m1 (acache_addr L c) [C4 (Z_to_bv 64 (cnt - 1)); C4 (Z_to_bv 64 (max_count st_pre c)); C8 (Z_to_bv 64 (size_of_class c))]
    /\ rw_cells bsegs m1 (al_t L + 2784) [C8 stj'].

Lemma calloc_read_gen : forall L st X m c cnt,
  alayout_ok L -> AREP H L st X m -> 1 <= c <= 30 -> c_count (get_cls st c) = cnt -> 0 < cnt ->
  exists k chunks stj,
       nth_error (xc_cache (x_cls X c)) (Z.to_nat (cnt - 1)) = Some k /\ busy_of X c k = None /\ 0 <= k < ndist st c
    /\ rw_cells bsegs m (al_t L + 208 + c * 80) [C4 (Z_to_bv 64 cnt); C4 (Z_to_bv 64 (max_count st c)); C8 (Z_to_bv 64 (size_of_class c))]
    /\ u32arr bsegs m (al_t L + 208 + c * 80 + 16) chunks /\ length chunks = 16%nat
    /\ nth_error chunks (Z.to_nat (cnt - 1)) = Some (Z_to_bv 64 (acompact c k)) /\ bv_unsigned (Z_to_bv 64 (acompact c k)) < 2^32
    /\ aslot_addr L c k = al_space_beg L + c * 2^32 + 16 * bv_unsigned (Z_to_bv 64 (acompact c k))
    /\ rw_cells bsegs m 0xd8638 [C8 (Z_to_bv 64 (al_space_beg L))]
    /\ rw_cells bsegs m (al_t L + 2784) [C8 stj]
    /\ cnt <= 16
    /\ iclr (al_t L) 4096 /\ al_t L + 4096 <= ATOP /\ al_t L mod 4096 = 0 /\ 0 <= al_space_beg L < 2^47.
Proof.
  intros L st X m c cnt ALO AR C16 HCNT POS.
  assert (HCK : 1 <= c < K_NUM_CLASSES) by (unfold K_NUM_CLASSES; lia).
  destruct (kit_cache_pop H L st X m c cnt AR HCK HCNT POS) as (k & chunks & NK & NB & KR & CR & CH & LCH & NTH & JK & FSH).
  pose proof AR as AR0. destruct AR0 as (WF & RT & INST & THR & CLS & HQ & HS & HD & HRO & RT2 & AVL & RT3).
  destruct THR as (T0 & T40 & CACHES & CSTATS & STATS & UNW).
  pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVE & FRESH & UNIQ).
  destruct (PERC c HCK) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & LENF & LENC & CNTB & ND & RANGE).
  pose proof (alayout_space L ALO) as (SP1 & SP2 & SP3 & SP4). pose proof (alayout_t L ALO) as (TL1 & TL2 & TL3 & TL4).
  destruct INST as (I32 & _). unfold AINSTANCE in I32.
  destruct (junk_split m (al_t L + 2768) 16 16 CSTATS ltac:(lia) ltac:(lia)) as [_ CSb].
  destruct (junk_split m (al_t L + 2768 + 16) 8 8 CSb ltac:(lia) ltac:(lia)) as [CS8 _].
  replace (al_t L + 2768 + 16) with (al_t L + 2784) in CS8 by lia. destruct (c8_of_junk m _ CS8) as [stj STS].
  pose proof (cls_facts c C16) as (SZB & SZM & MCB & _). set (S := size_of_class c) in *.
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
  destruct ACK as (ACK1 & ACK2 & ACK3).
  exists k, chunks, stj.
  split; [exact NK|]. split; [exact NB|]. split; [exact KR|]. split; [exact CR|]. split; [exact CH|]. split; [exact LCH|]. split; [exact NTH|].
  split; [rewrite ACK1; lia|].
  split; [rewrite ACK1; unfold aslot_addr, aregion, K_REGION; fold S; rewrite ACK3; clear; lia|].
  split; [exact I32|]. split; [exact STS|].
  split; [unfold max_count in CNTB; generalize CNTB MCB HCNT; clear; destruct (a_cinit st); intros; lia|].
  clear -TL1 TL2 TL3 TL4 SP4. split; [exact TL4|]. split; [exact TL2|]. split; [exact TL3| exact SP4].
Qed.

Theorem calloc_arep_gen : forall {R} (k : astate -> bool -> AM R) (Q : R -> footprint -> machine_state -> Prop)
    (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (X : aconc) (c lo size : Z),
  alayout_ok L -> arng L RNG st -> AREP H L st X m -> mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - CALLOC_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 AINSTANCE -> a1 = Z_to_bv 64 (al_t L + 208) -> a2 = Z_to_bv 64 size -> a3 = Z_to_bv 64 8 ->
  16 <= size <= 65536 -> size mod 8 = 0 -> class_id size = c ->
  c = K_BATCH_CLASS ->
  rng RNG lo (bv_unsigned sp - lo) ->
  (forall st_pre X_pre RNG1 m_pre cnt kk ms1,
     calloc_retG L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st X c lo m st_pre X_pre RNG1 m_pre cnt kk ms1 ->
     implS bsegs RNG1 (aembed ATOP (k (apop c st_pre) true)) (epostF Q) ms1) ->
  implS bsegs RNG (aembed ATOP (cache_alloc st c k)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x41db0) fc None m (seg_rom bsegs)).
Proof.
  intros R k Q L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st X c lo size
         ALO ARNG AR MI ST CEIL LO TP Ha0 Ha1 Ha2 Ha3 SZ M8 HC HC24 RSTK KONT.
  assert (C16 : 1 <= c <= 30) by (pose proof (class_facts size ltac:(clear -SZ; lia)) as CF; cbv zeta in CF; rewrite HC in CF; clear -CF; lia).
  assert (HCK : 1 <= c < K_NUM_CLASSES) by (unfold K_NUM_CLASSES; lia).
  pose proof AR as AR0. destruct AR0 as (WF & RT & INST & THR & CLS & HQ & HS & HD & HRO & RT2 & AVL & RT3).
  destruct THR as (T0 & T40 & CACHES & CSTATS & STATS & UNW).
  pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVE & FRESH & UNIQ).
  destruct (PERC c HCK) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & LENF & LENC & CNTB & ND & RANGE).
  pose proof (alayout_space L ALO) as (SP1 & SP2 & SP3 & SP4). pose proof (alayout_t L ALO) as (TL1 & TL2 & TL3 & TL4).
  pose proof ARNG as ARNG0. destruct ARNG as (RIMG & RT4 & RCTX & RNO & RSTO & RRI & RFK & RSFK & RDTLS & RCLS & RPA & RSECS & RPSH).
  word_range sp SPR.
  assert (ACE : acache_addr L c = al_t L + 208 + c * 80) by reflexivity.
  rewrite cache_alloc_unfold.
  destruct (Z.ltb_spec 0 (c_count (get_cls st c))) as [POS|NPOS].
  -
    change (put_cls c (cls_set_count (c_count (get_cls st c) - 1) (get_cls st c)) st) with (apop c st).
    destruct (calloc_read_gen L st X m c (c_count (get_cls st c)) ALO AR C16 eq_refl POS)
      as (kk & chunks & stj & NK & NB & KR & CR & CH & LCH & NTH & IXS & HAB & I32 & STS & CNT16 & T0' & T1' & TAL & SBR).
    iprefix. eapply evtF_cut.
    { eapply (calloc_hit_gen RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                F fc m (al_t L) size c (c_count (get_cls st c)) (al_space_beg L) lo _ _ stj chunks (Z_to_bv 64 (acompact c kk)));
        first [exact ST | exact CEIL | exact MI | exact Ha0 | exact Ha1 | exact Ha2 | exact Ha3 | exact SZ | exact M8 | exact HC | exact I32 | exact CR | exact CH
              | exact LCH | exact NTH | exact IXS | exact STS | exact T0' | exact T1' | exact TAL | exact SBR | exact RIMG | exact RSTK | exact RT4 | lia]. }
    cbv beta. intros ms1 P1. apply evtF_done. apply (KONT st X RNG m (c_count (get_cls st c)) kk).
    unfold cache_hit_post in P1.
    destruct P1 as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> & MU1 & WM1 & MI1 & ST1 & CR1 & [stj' STS1]).
    replace (al_t L + 2784 + 8) with (al_t L + 2792) in MU1 by lia.
    unfold calloc_retG.
    split; [apply fp_le_refl|]. split; [exact AR|]. split; [exact ARNG0|].
    split; [reflexivity|]. split; [exact POS|]. split; [exact NK|]. split; [exact NB|]. split; [exact KR|].
    split; [reflexivity|]. do 8 (split; [reflexivity|]).
    split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact MI|].
    do 14 eexists. exists m1, stj'. split; [rewrite HAB; reflexivity|].
    split; [rewrite ACE; exact MU1|]. split; [exact WM1|]. split; [exact MI1|]. split; [exact ST1|]. split; [rewrite ACE; exact CR1| exact STS1].
  -
    assert (CNT0 : c_count (get_cls st c) = 0) by lia.
    destruct (CACHES c HCK) as [tl (RH & RCH & RLEN)]. rewrite CNT0 in RH. rewrite ACE in RH.
    iprefix. eapply evtF_cut.
    { eapply (calloc_pre_gen RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                F fc m (al_t L) size c lo);
        first [exact ST | exact CEIL | exact MI | exact Ha0 | exact Ha1 | exact Ha2 | exact Ha3 | exact SZ | exact M8 | exact HC | exact RH | exact TL4 | exact TL2 | exact RIMG | exact RSTK | exact RT4
              | clear -LO; lia]. }
    cbv beta. intros msp Pp. apply evtF_done. unfold calloc_pre_post in Pp.
    destruct Pp as (t0p & t1p & t2p & a4p & a5p & a6p & a7p & t3p & t4p & t5p & t6p & mp & -> & MUp & WMp & MIp & STp & FRp).
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
         | |- _ = K_BATCH_CLASS => exact HC24
         | |- c_count _ = 0 => exact CNT0
         | |- rng _ _ _ => rewrite unsigned_lit by lia; eapply rng_sub'; [exact RSTK|]; lia
         end.

    intros st_r X' RNG' ms' RR. unfold ARefill_iface.TwinB.refill_ret in RR.
    destruct RR as (FPLE & t0r & t1r & t2r & a1r & a2r & a3r & a4r & a5r & a6r & a7r & t3r & t4r & t5r & t6r & mr
                    & -> & MUr & WMr & MIr & STr & ARr & ARNGr & CIN & CCNT & NPOS' & XB & XC & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & GC).
    rewrite ?unsigned_lit in MUr by lia. rewrite ?unsigned_lit in STr by lia.
    replace (ret_pc (Z_to_bv 64 0x42060)) with (Z_to_bv 64 0x42060) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    remember (c_count (get_cls st_r c)) as cnt eqn:HCNT. symmetry in HCNT.
    destruct (calloc_read_gen L st_r X' mr c cnt ALO ARr C16 HCNT ltac:(lia))
      as (kk & chunks & stj & NK & NB & KR & CR & CH & LCH & NTH & IXS & HAB & I32 & STS & CNT16 & T0' & T1' & TAL & SBR).
    pose proof ARNGr as ARNGr0. destruct ARNGr as (RIMG' & RT4' & RCTX' & RNO' & RSTO' & RRI' & RFK' & RSFK' & RDTLS' & RCLS' & RPA' & RSECS' & RPSH').
    assert (OBJ : aregion_info L c + 128 <= ATOP /\ aregion L c + K_REGION <= ATOP /\ shad (aregion L c) + shlen K_REGION <= 17594333495296).
    { unfold aregion_info, aregion, K_REGION, K_SPACE_SIZE, K_SPACE_EXTRA, ARI_STRIDE in *. change (2^37) with 137438953472 in *. change (2^32) with 4294967296 in *.
      rewrite shad_div, shlen_div. unfold ASHOFF. clear -SP1 SP2 C16. Z.div_mod_to_equations. lia. }
    destruct OBJ as (OB1 & OB2 & OB3).
    xport FRp MUr WMr ltac:(unfold AINSTANCE in *; clear -SPR CEIL LO TL1 TL2 OB1 OB2 OB3; lia).
    iprefix. eapply evtF_cut.
    { eapply (calloc_popj_gen RNG' sp gp tp t0r t1r t2r a1r a2r a3r a4r a5r a6r a7r s5 s6 s7 s8 s9 s10 s11 t3r t4r t5r t6r
                ra s0 s1 s2 s3 s4 (Z_to_bv 64 1) F fc mr (al_t L) c cnt (al_space_beg L) lo _ _ stj chunks (Z_to_bv 64 (acompact c kk)));
        first [ replace (bv_unsigned sp - 48) with (bv_unsigned sp + -48) by lia; exact STr
              | exact CEIL | exact MIr | exact C16 | exact FRp | exact I32 | exact CR | exact CH | exact LCH | exact NTH | exact IXS | exact STS
              | exact T0' | exact T1' | exact TAL | exact SBR | exact RIMG' | exact RT4'
              | rewrite unsigned_lit by lia; lia
              | eapply rng_fp_leG; [exact FPLE | exact RSTK]
              | lia ]. }
    cbv beta. intros ms1 P1. apply evtF_done. apply (KONT st_r X' RNG' mr cnt kk).
    unfold cache_hit_post in P1.
    destruct P1 as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> & MU1 & WM1 & MI1 & ST1 & CR1 & [stj' STS1]).
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
End Calloc.
End CANSEC2.
End ACallocG.

Module ACallocG_x.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Specs. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Exec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Tac. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.SysStep.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.MM_syscalls. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.WStr.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.SysStepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW.BImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit2.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABytes.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AModelFacts.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARep.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepKit.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepFrame.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ALayout.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AHeapP.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepExt.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARefill_iface.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARefillP.TwinB.ARefillP. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.APrimFacts.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_acache.TwinB.F_acache.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_acache.TwinB.F_acache2.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_acache.TwinB.F_acache3.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_acache.TwinB.F_acache4. Import ACallocG. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AMalloc_iface.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AEmbRep.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFrameD.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AEmbFrame.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_arefill.TwinB.F_arefill_x. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARefill_iface_x.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARefillP_x.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARefillP.TwinB.ARefillP_e. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_acache_x.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation CALLOC_STACK_X := 2096 (only parsing).

Section CANSEC2. Context {rc : runConstT} {ov : annOV}.

Lemma axg_frame_hi : forall RESV RNG st m m' (W : list (Z * Z)), axg RESV RNG st m -> munch W m m' -> Forall (fun iv => ATOP <= fst iv) W -> axg RESV RNG st m'.
Proof.
  intros RESV RNG st m m' W (XC & EC & ER & ECL) MU HW. pose proof atop_range as AT.
  assert (HW' : Forall (fun iv : Z * Z => AIMG_HI <= fst iv) W) by (eapply Forall_impl; [| exact HW]; intros iv Hv; unfold AIMG_HI; cbn beta in *; lia).
  assert (DJ : forall A k, A + k <= ATOP -> disjoint_from W A k).
  { clear -HW. induction W as [|[lo hi] W IH]; intros A k HA; cbn; [exact I|]. inversion HW as [|? ? H1 H2]; subst. cbn [fst] in H1. split; [lia| apply IH; assumption]. }
  split; [eapply exh_cells_frameD; [exact XC| exact MU| exact HW']|]. split; [| split; [exact ER| exact ECL]].
  eapply emb_cells_frameD; [exact EC| exact MU| apply DJ; unfold AEMB; lia|].
  pose proof EC as EC1. unfold emb_cells in EC1. destruct (a_emb st) as [[d cap] sz]. destruct (Z.eqb_spec cap 0) as [E0|NZ]; [left; exact E0| right].
  destruct EC1 as (_ & _ & _ & _ & _ & _ & _ & _ & TOP & _). apply DJ. exact TOP.
Qed.
Lemma axflag_frame_hi : forall L st m m' c (W : list (Z * Z)), axflag L st m c -> munch W m m' -> Forall (fun iv => ATOP <= fst iv) W ->
  aregion_info L c + 128 <= ATOP -> axflag L st m' c.
Proof.
  intros L st m m' c W AF MU HW RIT. unfold axflag in *. eapply cells_frameD; [exact AF| exact MU|]. cbn [cells_size csize Nat.add].
  clear -HW RIT. induction W as [|[lo hi] W IH]; cbn; [exact I|]. inversion HW as [|? ? H1 H2]; subst. cbn [fst] in H1. split; [lia| apply IH; assumption].
Qed.

Section CallocX.
Variable H : aholes.
Hypothesis HL : ahole_laws H.
Hypothesis HLD : ahole_lawsD H.

Definition calloc_retG_x (L : alayout) (RESV : list (Z * Z)) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : astate) (X : aconc) (c lo : Z) (m : amem)
    (st_pre : astate) (X_pre : aconc) (RNG1 : footprint) (m_pre : amem) (cnt k : Z) (ms1 : machine_state) : Prop :=
  calloc_retG H L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st X c lo m st_pre X_pre RNG1 m_pre cnt k ms1
  /\ a_emb st_pre = a_emb st /\ (a_exh st_pre = a_exh st \/ a_exh st_pre = a_exh (exh_clear c st))
  /\ (c <> K_BATCH_CLASS -> axflag L st_pre m_pre c) /\ axg RESV RNG1 st_pre m_pre.

Theorem calloc_arep_gen_x : forall {R} (RESV : list (Z * Z)) (k : astate -> bool -> AM R) (Q : R -> footprint -> machine_state -> Prop)
    (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (X : aconc) (c lo size : Z),
  alayout_ok L -> arng L RNG st -> AREP H L st X m -> mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - CALLOC_STACK_X ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 AINSTANCE -> a1 = Z_to_bv 64 (al_t L + 208) -> a2 = Z_to_bv 64 size -> a3 = Z_to_bv 64 8 ->
  16 <= size <= 65536 -> size mod 8 = 0 -> class_id size = c ->
  rng RNG lo (bv_unsigned sp - lo) ->

  exh_first_stmt -> aresv_ok L RESV -> bv_unsigned sp < 2 ^ 63 -> bv_unsigned fc < 32 ->
  (c <> K_BATCH_CLASS -> axflag L st m c) -> axg RESV RNG st m -> (let '(_, cap0, _) := a_emb st in cap0 <= 2 ^ 23) ->
  (forall st2 RNG' ms',
     aret_xf H L RESV RNG CALLOC_STACK_X ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st X c lo m st2 RNG' ms' ->
     implS bsegs RNG' (aembed ATOP (k st2 false)) (epostF Q) ms') ->
  (forall st_pre X_pre RNG1 m_pre cnt kk ms1,
     calloc_retG_x L RESV RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st X c lo m st_pre X_pre RNG1 m_pre cnt kk ms1 ->
     implS bsegs RNG1 (aembed ATOP (k (apop c st_pre) true)) (epostF Q) ms1) ->
  implS bsegs RNG (aembed ATOP (cache_alloc_x ATOP RESV st c k)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x41db0) fc None m (seg_rom bsegs)).
Proof.
  intros R RESV k Q L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st X c lo size
         ALO ARNG AR MI ST CEIL LO TP Ha0 Ha1 Ha2 Ha3 SZ M8 HC RSTK EXHW ARV SP63 FC AXF AXG CAPB KONTF KONT.
  assert (C16 : 1 <= c <= 30) by (pose proof (class_facts size ltac:(clear -SZ; lia)) as CF; cbv zeta in CF; rewrite HC in CF; clear -CF; lia).
  assert (HCK : 1 <= c < K_NUM_CLASSES) by (unfold K_NUM_CLASSES; lia).
  pose proof AR as AR0. destruct AR0 as (WF & RT & INST & THR & CLS & HQ & HS & HD & HRO & RT2 & AVL & RT3).
  destruct THR as (T0 & T40 & CACHES & CSTATS & STATS & UNW).
  pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVE & FRESH & UNIQ).
  destruct (PERC c HCK) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & LENF & LENC & CNTB & ND & RANGE).
  pose proof (alayout_space L ALO) as (SP1 & SP2 & SP3 & SP4). pose proof (alayout_t L ALO) as (TL1 & TL2 & TL3 & TL4).
  pose proof ARNG as ARNG0. destruct ARNG as (RIMG & RT4 & RCTX & RNO & RSTO & RRI & RFK & RSFK & RDTLS & RCLS & RPA & RSECS & RPSH).
  word_range sp SPR.
  assert (ACE : acache_addr L c = al_t L + 208 + c * 80) by reflexivity.
  assert (OBJ : aregion_info L c + 128 <= ATOP /\ aregion L c + K_REGION <= ATOP /\ shad (aregion L c) + shlen K_REGION <= 17594333495296).
  { unfold aregion_info, aregion, K_REGION, K_SPACE_SIZE, K_SPACE_EXTRA, ARI_STRIDE in *. change (2^37) with 137438953472 in *. change (2^32) with 4294967296 in *.
    rewrite shad_div, shlen_div. unfold ASHOFF. clear -SP1 SP2 C16. Z.div_mod_to_equations. lia. }
  destruct OBJ as (OB1 & OB2 & OB3).
  rewrite cache_alloc_x_unfold.
  destruct (Z.ltb_spec 0 (c_count (get_cls st c))) as [POS|NPOS].
  -
    change (put_cls c (cls_set_count (c_count (get_cls st c) - 1) (get_cls st c)) st) with (apop c st).
    destruct (calloc_read_gen H L st X m c (c_count (get_cls st c)) ALO AR C16 eq_refl POS)
      as (kk & chunks & stj & NK & NB & KR & CR & CH & LCH & NTH & IXS & HAB & I32 & STS & CNT16 & T0' & T1' & TAL & SBR).
    iprefix. eapply evtF_cut.
    { eapply (calloc_hit_gen RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                F fc m (al_t L) size c (c_count (get_cls st c)) (al_space_beg L) lo _ _ stj chunks (Z_to_bv 64 (acompact c kk)));
        first [exact ST | exact CEIL | exact MI | exact Ha0 | exact Ha1 | exact Ha2 | exact Ha3 | exact SZ | exact M8 | exact HC | exact I32 | exact CR | exact CH
              | exact LCH | exact NTH | exact IXS | exact STS | exact T0' | exact T1' | exact TAL | exact SBR | exact RIMG | exact RSTK | exact RT4 | lia]. }
    cbv beta. intros ms1 P1. apply evtF_done. apply (KONT st X RNG m (c_count (get_cls st c)) kk).
    unfold cache_hit_post in P1.
    destruct P1 as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> & MU1 & WM1 & MI1 & ST1 & CR1 & [stj' STS1]).
    replace (al_t L + 2784 + 8) with (al_t L + 2792) in MU1 by lia.
    unfold calloc_retG_x. split; [| split; [reflexivity| split; [left; reflexivity| split; [exact AXF| exact AXG]]]].
    unfold calloc_retG.
    split; [apply fp_le_refl|]. split; [exact AR|]. split; [exact ARNG0|].
    split; [reflexivity|]. split; [exact POS|]. split; [exact NK|]. split; [exact NB|]. split; [exact KR|].
    split; [reflexivity|]. do 8 (split; [reflexivity|]).
    split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact MI|].
    do 14 eexists. exists m1, stj'. split; [rewrite HAB; reflexivity|].
    split; [rewrite ACE; exact MU1|]. split; [exact WM1|]. split; [exact MI1|]. split; [exact ST1|]. split; [rewrite ACE; exact CR1| exact STS1].
  -
    assert (CNT0 : c_count (get_cls st c) = 0) by lia.
    destruct (CACHES c HCK) as [tl (RH & RCH & RLEN)]. rewrite CNT0 in RH. rewrite ACE in RH.
    iprefix. eapply evtF_cut.
    { eapply (calloc_pre_gen RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                F fc m (al_t L) size c lo);
        first [exact ST | exact CEIL | exact MI | exact Ha0 | exact Ha1 | exact Ha2 | exact Ha3 | exact SZ | exact M8 | exact HC | exact RH | exact TL4 | exact TL2 | exact RIMG | exact RSTK | exact RT4
              | clear -LO; lia]. }
    cbv beta. intros msp Pp. apply evtF_done. unfold calloc_pre_post in Pp.
    destruct Pp as (t0p & t1p & t2p & a4p & a5p & a6p & a7p & t3p & t4p & t5p & t6p & mp & -> & MUp & WMp & MIp & STp & FRp).
    assert (ARp : AREP H L st X mp).
    { eapply (AREP_frame_ext H HL L st X m mp); [exact ALO | exact AR | exact MUp | exact WMp |].
      apply Forall_cons; [cbn [fst snd]; intros _; right; right; atop_facts; lia | apply Forall_nil]. }
    assert (HWp : Forall (fun iv : Z * Z => ATOP <= fst iv) [(bv_unsigned sp - 48, bv_unsigned sp)]) by (constructor; [cbn [fst]; clear -CEIL LO; lia| constructor]).
    assert (AXGp : axg RESV RNG st mp) by (eapply axg_frame_hi; [exact AXG| exact MUp| exact HWp]).
    destruct (Z.eq_dec c K_BATCH_CLASS) as [C24|NC24].
    +
      assert (TREE : cache_refill_tree_x RESV st c k = cache_refill_tree st c k).
      { unfold cache_refill_tree_x, cache_refill_tree, populate_free_array_x. rewrite C24, Z.eqb_refl. reflexivity. }
      rewrite TREE.
      eapply (arefillP_e H HL _ k Q L RNG _ _ gp tp t0p t1p t2p _ _ _ _ _ _ a4p a5p a6p a7p _ _ _ s5 s6 s7 s8 s9 s10 s11 t3p t4p t5p t6p F fc mp st X c lo
                ALO ARNG0 ARp MIp).
      all: try lazymatch goal with
           | |- arng _ _ _ => exact ARNG0
           | |- stk _ _ _ _ => rewrite unsigned_lit by lia; replace (bv_unsigned sp + -48) with (bv_unsigned sp - 48) by lia; exact STp
           | |- ATOP <= _ => exact CEIL
           | |- _ <= bv_unsigned _ - _ => rewrite unsigned_lit by lia; lia
           | |- @eq word _ _ => first [exact TP | reflexivity | rewrite ACE; reflexivity]
           | |- _ = K_BATCH_CLASS => exact C24
           | |- c_count _ = 0 => exact CNT0
           | |- rng _ _ _ => rewrite unsigned_lit by lia; eapply rng_sub'; [exact RSTK|]; lia
           end.
      intros st_r X' RNG' ms' [RR [EMBr EXHr]]. unfold ARefill_iface.TwinB.refill_ret in RR.
      destruct RR as (FPLE & t0r & t1r & t2r & a1r & a2r & a3r & a4r & a5r & a6r & a7r & t3r & t4r & t5r & t6r & mr
                      & -> & MUr & WMr & MIr & STr & ARr & ARNGr & CIN & CCNT & NPOS' & XB & XC & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & GC).
      rewrite ?unsigned_lit in MUr by lia. rewrite ?unsigned_lit in STr by lia.
      replace (ret_pc (Z_to_bv 64 0x42060)) with (Z_to_bv 64 0x42060) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      remember (c_count (get_cls st_r c)) as cnt eqn:HCNT. symmetry in HCNT.
      destruct (calloc_read_gen H L st_r X' mr c cnt ALO ARr C16 HCNT ltac:(lia))
        as (kk & chunks & stj & NK & NB & KR & CR & CH & LCH & NTH & IXS & HAB & I32 & STS & CNT16 & T0' & T1' & TAL & SBR).
      pose proof ARNGr as ARNGr0. destruct ARNGr as (RIMG' & RT4' & RCTX' & RNO' & RSTO' & RRI' & RFK' & RSFK' & RDTLS' & RCLS' & RPA' & RSECS' & RPSH').

      assert (AXGr : axg RESV RNG' st_r mr).
      { destruct AXGp as (XCp & ECp & ERp & ECLp).
        assert (MU0 : 0 <= c_mapped_user (get_cls st c)) by (clear -A1; lia).
        assert (MUK : c_mapped_user (get_cls st c) <= K_REGION) by (unfold K_REGION, K_FREEARR_OFF in *; change (2^32) with 4294967296; clear -A2; lia).
        assert (LOr : lo <= bv_unsigned sp - 48 - 1536) by (clear -LO; lia).
        pose proof (arefillW_img L st c (bv_unsigned sp - 48) lo ALO HCK CEIL LOr MU0) as KI.
        destruct (a_emb st) as [[d0 cap0] sz0] eqn:EA.
        split; [eapply exh_cells_frameK; [exact XCp| exact MUr| exact KI]|].
        assert (EC' : emb_cells st mr).
        { eapply emb_cells_frameD; [exact ECp| exact MUr| apply KI; clear; unfold AEMB, AIMG_LO, AIMG_HI, AINSTANCE; lia|]. rewrite EA.
          destruct (Z.eqb_spec cap0 0) as [E0|NZ]; [left; exact E0| right].
          pose proof ECp as EC1. unfold emb_cells in EC1. rewrite EA in EC1. replace (cap0 =? 0) with false in EC1 by (symmetry; apply Z.eqb_neq; exact NZ).
          destruct EC1 as (_ & _ & _ & _ & P2 & _ & _ & P5 & P6 & _).
          unfold emb_clr in ECLp. rewrite EA in ECLp. destruct ECLp as [QQ|AV]; [exfalso; exact (NZ QQ)|].
          unfold avoids_all in AV. rewrite forallb_app in AV. apply andb_prop in AV as [AV _].
          apply (arefillW_buf L RESV st c (bv_unsigned sp - 48) lo ALO HCK CEIL LOr MU0 d0 cap0 ARV MUK); [unfold EMB_INIT in P2; clear -P2; lia| exact P5| exact P6| exact AV]. }
        split; [unfold emb_cells in EC' |- *; rewrite EMBr; rewrite EA in EC'; exact EC'|].
        split; [unfold emb_rng in ERp |- *; rewrite EMBr; rewrite EA in ERp; destruct ERp as [QQ|QQ]; [left; exact QQ| right; exact (rng_fp_leG _ _ _ _ FPLE QQ)]|].
        unfold emb_clr in ECLp |- *. rewrite EMBr. rewrite EA in ECLp.
        assert (ACH : achunks st_r = achunks st) by (unfold achunks; rewrite L1, L3, L5; reflexivity).
        rewrite ACH. exact ECLp. }
      xport FRp MUr WMr ltac:(unfold AINSTANCE in *; clear -SPR CEIL LO TL1 TL2 OB1 OB2 OB3; lia).
      iprefix. eapply evtF_cut.
      { eapply (calloc_popj_gen RNG' sp gp tp t0r t1r t2r a1r a2r a3r a4r a5r a6r a7r s5 s6 s7 s8 s9 s10 s11 t3r t4r t5r t6r
                  ra s0 s1 s2 s3 s4 (Z_to_bv 64 1) F fc mr (al_t L) c cnt (al_space_beg L) lo _ _ stj chunks (Z_to_bv 64 (acompact c kk)));
          first [ replace (bv_unsigned sp - 48) with (bv_unsigned sp + -48) by lia; exact STr
                | exact CEIL | exact MIr | exact C16 | exact FRp | exact I32 | exact CR | exact CH | exact LCH | exact NTH | exact IXS | exact STS
                | exact T0' | exact T1' | exact TAL | exact SBR | exact RIMG' | exact RT4'
                | rewrite unsigned_lit by lia; lia
                | eapply rng_fp_leG; [exact FPLE | exact RSTK]
                | lia ]. }
      cbv beta. intros ms1 P1. apply evtF_done. apply (KONT st_r X' RNG' mr cnt kk).
      unfold cache_hit_post in P1.
      destruct P1 as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> & MU1 & WM1 & MI1 & ST1 & CR1 & [stj' STS1]).
      replace (al_t L + 2784 + 8) with (al_t L + 2792) in MU1 by lia.
      unfold calloc_retG_x. split; [| split; [exact EMBr| split; [left; exact EXHr| split; [intros NE; exfalso; exact (NE C24)| exact AXGr]]]].
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
    +
      assert (AXFp : axflag L st mp c) by (eapply axflag_frame_hi; [exact (AXF NC24)| exact MUp| exact HWp| exact OB1]).
      eapply (arefill_x H HL HLD _ RESV k Q L RNG _ _ gp tp t0p t1p t2p _ _ _ _ _ _ a4p a5p a6p a7p _ _ _ s5 s6 s7 s8 s9 s10 s11 t3p t4p t5p t6p F fc mp st X c lo
                ALO ARNG0 ARp MIp).
      all: try lazymatch goal with
           | |- implS _ _ _ _ _ => idtac
           | |- forall _, _ => idtac
           | |- arng _ _ _ => exact ARNG0
           | |- exh_first_stmt => exact EXHW
           | |- aresv_ok _ _ => exact ARV
           | |- axflag _ _ _ _ => exact AXFp
           | |- axg _ _ _ _ => exact AXGp
           | |- context [a_emb _] => exact CAPB
           | |- bv_unsigned _ < 2 ^ 63 => rewrite unsigned_lit by lia; clear -SP63 SPR; lia
           | |- bv_unsigned _ < 32 => exact FC
           | |- stk _ _ _ _ => rewrite unsigned_lit by lia; replace (bv_unsigned sp + -48) with (bv_unsigned sp - 48) by lia; exact STp
           | |- ATOP <= _ => exact CEIL
           | |- _ <= bv_unsigned _ - _ => rewrite unsigned_lit by lia; lia
           | |- @eq word _ _ => first [exact TP | reflexivity | rewrite ACE; reflexivity]
           | |- 1 <= _ < _ => exact HCK
           | |- _ <> K_BATCH_CLASS => exact NC24
           | |- c_count _ = 0 => exact CNT0
           | |- rng _ _ _ => rewrite unsigned_lit by lia; eapply rng_sub'; [exact RSTK|]; lia
           end.
      *
        intros st2 RNG' ms' RF. unfold refill_ret_xf, aret_xf in RF. cbv zeta in RF.
        pose proof AXGp as (_ & ECp & _). unfold emb_cells in ECp.
        destruct (a_emb st) as [[d0 cap0] sz0] eqn:EA. destruct (a_emb st2) as [[d2 cap2] sz2] eqn:EA2.
        destruct RF as (FPLE & t0r & t1r & t2r & a1r & a2r & a3r & a4r & a5r & a6r & a7r & t3r & t4r & t5r & t6r & mr
                        & -> & MIr & STr & STEQ & ARr & ARNGr & AXFr & AXGr & (d1 & cap1 & MUr & PV1 & PV2 & TOP1)).
        rewrite ?unsigned_lit in MUr by lia. rewrite ?unsigned_lit in STr by lia.
        replace (ret_pc (Z_to_bv 64 0x42060)) with (Z_to_bv 64 0x42060) by (symmetry; apply ret_pc_even; [lia|reflexivity]).

        assert (B0 : cap0 <= 0 \/ d0 + cap0 <= ATOP).
        { destruct (Z.eqb_spec cap0 0) as [E0|NZ]; [left; lia| right]. destruct ECp as (_ & _ & _ & _ & _ & _ & _ & _ & TOP & _). exact TOP. }
        assert (B2 : cap2 <= 0 \/ d2 + cap2 <= ATOP).
        { pose proof AXGr as (_ & EC2 & _). unfold emb_cells in EC2. rewrite EA2 in EC2.
          destruct (Z.eqb_spec cap2 0) as [E0|NZ]; [left; lia| right]. destruct EC2 as (_ & _ & _ & _ & _ & _ & _ & _ & TOP & _). exact TOP. }
        assert (B1 : cap1 <= 0 \/ d1 + cap1 <= ATOP) by (destruct TOP1 as [Q0|Q1]; [left; lia| right; exact Q1]).
        assert (FRr : rw_cells bsegs mr (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
        { eapply cells_frameO; [exact FRp| exact MUr|]. cbn [cells_size csize Nat.add]. intros x Hx. cbn [outside].
          unfold AEMB. pose proof atop_range as AT. clear -Hx B0 B1 B2 CEIL LO TL2 OB1 AT SPR. repeat split; lia. }
        pose proof ARNGr as (RIMG' & _).
        iprefix. eapply evtF_cut.
        { eapply (calloc_nullj_gen RNG' sp gp tp t0r t1r t2r a1r a2r a3r a4r a5r a6r a7r s5 s6 s7 s8 s9 s10 s11 t3r t4r t5r t6r
                    ra s0 s1 s2 s3 s4 _ _ _ _ F fc mr lo);
            first [ replace (bv_unsigned sp - 48) with (bv_unsigned sp + -48) by lia; exact STr
                  | exact CEIL | exact MIr | exact FRr | exact RIMG'
                  | eapply rng_fp_leG; [exact FPLE | exact RSTK]
                  | clear -LO; lia ]. }
        cbv beta. intros ms1 P1. apply evtF_done. apply (KONTF st2 RNG').
        unfold calloc_null_post in P1.
        destruct P1 as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & -> & ST1).
        unfold aret_xf. cbv zeta. rewrite EA, EA2.
        split; [exact FPLE|]. do 14 eexists. exists mr. split; [reflexivity|]. split; [exact MIr|]. split; [exact ST1|].
        split; [exact STEQ|]. split; [exact ARr|]. split; [exact ARNGr|]. split; [exact AXFr|]. split; [exact AXGr|].
        exists d1, cap1. split; [| split; [exact PV1| split; [exact PV2| exact TOP1]]].
        eapply munch_trans; [eapply munch_weaken; [| exact MUp] | eapply munch_weaken; [| exact MUr]];
          unfold sub_fp; cbn [outside]; intros q Hq.
        -- clear -Hq. lia.
        -- destruct Hq as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & _). split; [clear -X1; lia|]. repeat (split; [assumption|]). exact I.
      *
        intros st_r X' RNG' ms' RR. unfold refill_ret_xt in RR.
        destruct RR as (FPLE & t0r & t1r & t2r & a1r & a2r & a3r & a4r & a5r & a6r & a7r & t3r & t4r & t5r & t6r & mr
                        & -> & MUr & WMr & MIr & STr & ARr & ARNGr & CIN & CCNT & NPOS' & XB & XC & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & GC & EMBr & EXHr & AXFr & AXGr).
        rewrite ?unsigned_lit in MUr by lia. rewrite ?unsigned_lit in STr by lia.
        replace (ret_pc (Z_to_bv 64 0x42060)) with (Z_to_bv 64 0x42060) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
        remember (c_count (get_cls st_r c)) as cnt eqn:HCNT. symmetry in HCNT.
        destruct (calloc_read_gen H L st_r X' mr c cnt ALO ARr C16 HCNT ltac:(lia))
          as (kk & chunks & stj & NK & NB & KR & CR & CH & LCH & NTH & IXS & HAB & I32 & STS & CNT16 & T0' & T1' & TAL & SBR).
        pose proof ARNGr as ARNGr0. destruct ARNGr as (RIMG' & RT4' & RCTX' & RNO' & RSTO' & RRI' & RFK' & RSFK' & RDTLS' & RCLS' & RPA' & RSECS' & RPSH').
        xport FRp MUr WMr ltac:(unfold AINSTANCE in *; clear -SPR CEIL LO TL1 TL2 OB1 OB2 OB3; lia).
        iprefix. eapply evtF_cut.
        { eapply (calloc_popj_gen RNG' sp gp tp t0r t1r t2r a1r a2r a3r a4r a5r a6r a7r s5 s6 s7 s8 s9 s10 s11 t3r t4r t5r t6r
                    ra s0 s1 s2 s3 s4 (Z_to_bv 64 1) F fc mr (al_t L) c cnt (al_space_beg L) lo _ _ stj chunks (Z_to_bv 64 (acompact c kk)));
            first [ replace (bv_unsigned sp - 48) with (bv_unsigned sp + -48) by lia; exact STr
                  | exact CEIL | exact MIr | exact C16 | exact FRp | exact I32 | exact CR | exact CH | exact LCH | exact NTH | exact IXS | exact STS
                  | exact T0' | exact T1' | exact TAL | exact SBR | exact RIMG' | exact RT4'
                  | rewrite unsigned_lit by lia; lia
                  | eapply rng_fp_leG; [exact FPLE | exact RSTK]
                  | lia ]. }
        cbv beta. intros ms1 P1. apply evtF_done. apply (KONT st_r X' RNG' mr cnt kk).
        unfold cache_hit_post in P1.
        destruct P1 as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> & MU1 & WM1 & MI1 & ST1 & CR1 & [stj' STS1]).
        replace (al_t L + 2784 + 8) with (al_t L + 2792) in MU1 by lia.
        unfold calloc_retG_x. split; [| split; [exact EMBr| split; [exact EXHr| split; [intros _; exact AXFr| exact AXGr]]]].
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
End CallocX.
End CANSEC2.
End ACallocG_x.
End TwinB.
