(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode SysStep.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import MM_syscalls WStr.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import SysStepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg AProto ABase AKit AKit2 ABytes AModelFacts ARep ARepKit ARepFrame ALayout AHeapP ARepExt ARefill_iface ARefillP APrimFacts F_acache F_acache2 F_acache3 F_acache4.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
Lemma rng_fp_leG : forall RNG RNG' lo n, fp_le RNG RNG' -> rng RNG lo n -> rng RNG' lo n.
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

Section CANSEC2. Context {rc : runConstT}.
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
  /\ munch (calloc_W L st c (bv_unsigned sp)) m m_pre /\ wmono bsegs m m_pre /\ mem_inv bsegs m_pre
  /\ exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m1 (stj' : word),
       ms1 = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (aslot_addr L c k)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (ret_pc ra) fc None m1 (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (acache_addr L c, acache_addr L c + 4); (al_t L + 2784, al_t L + 2792)]%Z m_pre m1
    /\ wmono bsegs m_pre m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo (bv_unsigned sp)
    /\ rw_cells bsegs m1 (acache_addr L c) [C4 (Z_to_bv 64 (cnt - 1)); C4 (Z_to_bv 64 (max_count st_pre c)); C8 (Z_to_bv 64 (size_of_class c))]
    /\ rw_cells bsegs m1 (al_t L + 2784) [C8 stj'].

(* [comment removed for export] *)
Lemma calloc_read_gen : forall L st X m c cnt,
  alayout_ok L -> AREP H L st X m -> 1 <= c <= 30 -> c_count (get_cls st c) = cnt -> 0 < cnt ->
  exists k chunks stj,
       nth_error (xc_cache (x_cls X c)) (Z.to_nat (cnt - 1)) = Some k /\ busy_of X c k = None /\ 0 <= k < ndist st c
    /\ rw_cells bsegs m (al_t L + 208 + c * 80) [C4 (Z_to_bv 64 cnt); C4 (Z_to_bv 64 (max_count st c)); C8 (Z_to_bv 64 (size_of_class c))]
    /\ u32arr bsegs m (al_t L + 208 + c * 80 + 16) chunks /\ length chunks = 16%nat
    /\ nth_error chunks (Z.to_nat (cnt - 1)) = Some (Z_to_bv 64 (acompact c k)) /\ bv_unsigned (Z_to_bv 64 (acompact c k)) < 2^32
    /\ aslot_addr L c k = al_space_beg L + c * 2^32 + 16 * bv_unsigned (Z_to_bv 64 (acompact c k))
    /\ rw_cells bsegs m 0xcc6b8 [C8 (Z_to_bv 64 (al_space_beg L))]
    /\ rw_cells bsegs m (al_t L + 2784) [C8 stj]
    /\ cnt <= 16
    /\ iclr (al_t L) 4096 /\ al_t L + 4096 <= ATOP /\ al_t L mod 4096 = 0 /\ 0 <= al_space_beg L < 2^47.   (* [comment removed for export] *)
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
  rng RNG lo (bv_unsigned sp - lo) ->
  (forall st_pre X_pre RNG1 m_pre cnt kk ms1,
     calloc_retG L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st X c lo m st_pre X_pre RNG1 m_pre cnt kk ms1 ->
     implS bsegs RNG1 (aembed ATOP (k (apop c st_pre) true)) (epostF Q) ms1) ->
  implS bsegs RNG (aembed ATOP (cache_alloc st c k)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x37f9c) fc None m (seg_rom bsegs)).
Proof.
  intros R k Q L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st X c lo size
         ALO ARNG AR MI ST CEIL LO TP Ha0 Ha1 Ha2 Ha3 SZ M8 HC RSTK KONT.
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
  - (* [comment removed for export] *)
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
  - (* [comment removed for export] *)
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
         | |- c_count _ = 0 => exact CNT0
         | |- rng _ _ _ => rewrite unsigned_lit by lia; eapply rng_sub'; [exact RSTK|]; lia
         end.
    (* [comment removed for export] *)
    intros st_r X' RNG' ms' RR. unfold ARefill_iface.refill_ret in RR.
    destruct RR as (FPLE & t0r & t1r & t2r & a1r & a2r & a3r & a4r & a5r & a6r & a7r & t3r & t4r & t5r & t6r & mr
                    & -> & MUr & WMr & MIr & STr & ARr & ARNGr & CIN & CCNT & NPOS' & XB & XC & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & GC).
    rewrite ?unsigned_lit in MUr by lia. rewrite ?unsigned_lit in STr by lia.
    replace (ret_pc (Z_to_bv 64 0x3824c)) with (Z_to_bv 64 0x3824c) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
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
