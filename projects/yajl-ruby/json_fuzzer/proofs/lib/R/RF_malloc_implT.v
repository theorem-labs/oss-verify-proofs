(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Images.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import PortShim.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.MS Require Import F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocKit_A Malloc_iface.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Agent Require Import MallocFacts_A MallocBlocks MallocHINV.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import STree Malloc MallocCtrl Monad RawAlloc MI_Sim.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.MS Require Import Malloc_fp F_malloc_enf F_malloc_join F_malloc_small F_malloc_entry F_malloc_core F_malloc_top ASlot_I.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RMallocRep RMallocTree RF_get_meta RMallocKit_B RMallocKit_B2 RMallocKit_A RMalloc_fp RF_enframe RF_malloc_enf RAllocSlot_iface RF_malloc_entry RF_malloc_join RF_malloc_small RF_malloc_core RMalloc_iface RMalloc_ifaceP RF_malloc_top.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Agent Require Import MallocFacts_AM MallocFacts_AMP.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RASlot_I RF_alloc_slot RF_malloc_big RF_am_P RF_alloc_meta.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Agent Require MallocFacts_inv2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition rmallocT_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (o : mem) (s : PState) (st : mstate) (LB : list block) (n lo B : Z) (m : mem)
    (res : mstate * optr) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ rmrep (fst res) m' /\ ticks_ok (fst res) /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
    /\ rw_cells rsegs m' (errno_addr tp) [C4 errv']
    /\ rauxv_ok m' B
    /\ rheap_pres LB (bv_unsigned sp) m m'
    /\ rpres_except (rmalloc_fp st (fst res) lo (bv_unsigned sp)) m m'
    /\ mrel st (fst res) /\ brk_link_ps (fst res) s' /\ ps_m s' = ps_m s /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ leaf_of o (malloc st n) res
    /\ match snd res with
       | None => a0 = Z_to_bv 64 0 /\ RAREACH (fst res) LB
       | Some pf => exists (c : cptr) (cst : mstate) (rg : region) junk,
           a0 = Z_to_bv 64 (conc (fst res) pf) /\ rblock_range (conc (fst res) pf) n
           /\ RAREACH (fst res) (((c, fresh_off cst c n), conc (fst res) pf, n) :: LB)
           /\ fst c = fst pf
           /\ (s_regions (fst res)) !! (fst pf) = Some rg /\ r_kind rg = RKGroup /\ 16 <= snd pf /\ snd pf + n <= round_up_pg (r_len rg)
           /\ rw_cells rsegs m' (conc (fst res) pf) [CB (Z.to_nat n) junk]
       end.

Section TOPLEVEL.
Variables (as_pre : mstate -> mstate -> Z -> Z -> nat -> Prop) (as_inv : mstate -> mstate -> mstate -> Z -> Z -> Prop).
Hypothesis RAS : ralloc_slot_stmt as_pre as_inv.
Hypothesis AS_PRE : forall st LB t sc n, RAREACH st LB -> RMFACTS st LB -> (s_tick st < t)%N -> 0 <= sc < 48 -> 0 <= n < 2^32 ->
  n + 4 <= 16 * size_class sc -> as_pre st (set_tick t st) sc n FUEL.
Hypothesis RBIG : rbig_stmt.

Theorem rmalloc_implT_gen :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (o m : mem)
         (s : PState) (st : mstate) (LB : list block) (n lo B : Z) (errv : word),
  RAREACH st LB -> rmrep st m -> brk_link_ps st s -> unk_agree st o m ->
  rauxv_ok m B -> bv_unsigned sp <= B ->
  stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 8192 ->
  rw_cells rsegs m (errno_addr tp) [C4 errv] ->
  mem_inv rsegs m ->
  tp = Z_to_bv 64 RATP ->
  a0 = Z_to_bv 64 n -> 0 <= n < 2^32 ->
  rimplT o (malloc st n) s
        (rmallocT_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o s st LB n lo B m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 rmalloc_entry) fc None m (seg_rom rsegs)).
Proof.
  intros until errv. intros AR MR BL UA AUXB SB ST CLO LO ERR MI TP HA N.
  pose proof (bv_unsigned_in_range 64 sp) as SPR0.
  assert (AUX : rauxv_ok m (bv_unsigned sp)) by (eapply rauxv_ok_weaken; [exact AUXB| unfold alloc_ceiling in *; lia]).
  pose proof (MallocFacts_inv2.areach_facts_proof _ _ AR) as MF.
  (* [comment removed for export] *)
  set (Q0 := fun (res : mstate * optr) (s' : PState) (ms' : machine_state) =>
    exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ rmrep (fst res) m' /\ ticks_ok (fst res) /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
    /\ rw_cells rsegs m' (errno_addr tp) [C4 errv']
    /\ rauxv_ok m' B
    /\ rheap_pres LB (bv_unsigned sp) m m'
    /\ rpres_except (rmalloc_fp st (fst res) lo (bv_unsigned sp)) m m'
    /\ mrel st (fst res) /\ brk_link_ps (fst res) s' /\ ps_m s' = ps_m s /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ match snd res with
       | None => a0 = Z_to_bv 64 0
       | Some pf => exists (g : aptr) (idx : Z) (st2 : mstate) (rg : region) junk,
           strip st2 = strip (fst res) /\ slot_of st2 g idx = (fst pf, snd pf - UNIT * ((snd pf - snd (slot_of st2 g idx)) / UNIT))
           /\ (snd pf - snd (slot_of st2 g idx)) mod UNIT = 0 /\ snd (slot_of st2 g idx) <= snd pf
           /\ a0 = Z_to_bv 64 (conc (fst res) pf) /\ rblock_range (conc (fst res) pf) n
           /\ (s_regions (fst res)) !! (fst pf) = Some rg /\ r_kind rg = RKGroup /\ 16 <= snd pf /\ snd pf + n <= round_up_pg (r_len rg)
           /\ rw_cells rsegs m' (conc (fst res) pf) [CB (Z.to_nat n) junk]
       end).
  assert (MAIN : rimplT o (malloc st n) s Q0
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 rmalloc_entry) fc None m (seg_rom rsegs))).
  2:{ (* [comment removed for export] *)
    eapply rimplT_mono; [apply rimplT_reach; exact MAIN|].
    intros [st' p] s' ms' [HQ LEAF]. subst Q0. cbv beta in HQ.
    destruct HQ as (x0 & x1 & x2 & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & m' & errv' & -> & MR' & TK' & MI' & ST' & ERR' & AUX' & HP' & PE' & REL' & BL' & PSM & PSF & PSO & RES).
    destruct LEAF as (ans & o' & FF).
    destruct (strel_follow_some ans (malloc_control pans_mem pupd_mem pans_mem_range st n o) FF) as ([cst c] & FC & HREL).
    unfold MREL in HREL. cbn [fst snd] in HREL. destruct HREL as [Ecst Hpc].
    unfold rmallocT_post. do 15 eexists. exists m', errv'.
    split; [reflexivity|]. cbn [fst snd].
    repeat match goal with |- _ /\ _ => split; [assumption|] end.
    split; [exists ans, o'; exact FF|].
    destruct p as [pf|].
    - destruct c as [c|]; [|destruct Hpc]. destruct Hpc as [Hfc [off Hoff]].
      destruct RES as (g & idx & st2 & rg & junk & Est2 & Eslot & Hmod & Hle & Ha0 & BR & Hrg & Krg & P16 & PN & UCH).
      exists c, cst, rg, junk. split; [exact Ha0|]. split; [exact BR|].
      split. { exact (areach_malloc_some st LB n o o' ans st' pf cst c AR ltac:(lia) FF FC). }
      split; [symmetry; exact Hfc|]. repeat (split; [assumption|]). exact UCH.
    - destruct c as [c|]; [destruct Hpc|]. split; [exact RES|].
      exact (areach_malloc_none st LB n o o' ans st' AR ltac:(lia) FF). }
  (* [comment removed for export] *)
  subst Q0. unfold malloc.
  eapply rimplT_bind.
  { eapply (rmalloc_core_implT_o as_pre as_inv RAS AS_PRE RBIG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc
              o m st LB s n lo errv (N.succ (s_tick st)) AR MF MR BL UA AUX ST CLO ltac:(lia) ERR MI TP HA N ltac:(lia)). }
  cbv beta. intros [st2 r] s' ms' CQ.
  destruct r as [[g idx]|].
  - (* [comment removed for export] *)
    cbn [rcoreQ] in CQ.
    destruct CQ as (b & rg & m1 & errv1 & u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & s4' & u3 & u4 & u5 & u6 & ra' & -> &
                    MR2 & TK2 & UA2 & MI2 & ST2 & FR2 & ERR2 & AUX2 & PE2 & SPANFP & CTR2 & SO & EXPO & MREL & BL2 & PSM & PSF & PSO).
    pose proof SO as [Hmem Hr Hk B0 B16 IDX LI32 SPAN S16 SMOD S31 N0' NS NOGRP HDR0 Q16 SSL MSL AVr FRr FBr MPL SCr].
    pose proof (rregion_addr_facts st2 m1 (fst b) rg MR2 Hr) as (R4 & RAL & RC & RI1).
    assert (SK : 0 <= get_stride (get_meta_rec st2 g) * idx) by (apply Z.mul_nonneg_nonneg; lia).
    assert (SKL : get_stride (get_meta_rec st2 g) * idx + get_stride (get_meta_rec st2 g) <= get_stride (get_meta_rec st2 g) * (m_last_idx (get_meta_rec st2 g) + 1)).
    { rewrite Z.mul_add_distr_l, Z.mul_1_r. apply Z.add_le_mono_r. apply Z.mul_le_mono_nonneg_l; lia. }
    set (stride := get_stride (get_meta_rec st2 g)) in *.
    set (lo_s := r_base rg + snd b + 16 + stride * idx - 4) in *.
    set (hi_s := r_base rg + snd b + 16 + stride * idx + stride - 4) in *.
    set (Cf := fun a => lo <= a < bv_unsigned sp \/ lo_s <= a < hi_s).
    unfold alloc_ceiling in RC, CLO.
    pose proof (renf_implT (RC__:=RC__) sp gp tp u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 s4' s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 ra' ra s0 s1 s2 s3 s4 F fc o m1 m1 s' st2 g b rg idx n lo Cf
                  MR2 TK2 UA2 MI2 ST2 ltac:(unfold alloc_ceiling; lia) ltac:(lia) FR2 (rpres_except_refl _ _)
                  ltac:(intros a Ha; left; exact Ha) ltac:(intros a Ha; right; subst lo_s hi_s stride; exact Ha) CTR2 SO) as ENF.
    eapply rimplT_mono; [exact ENF|]. clear ENF.
    intros res s'' msf [-> EP]. unfold renf_post in EP.
    destruct EP as (st' & p & w0 & w1 & w2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & w3 & w4 & w5 & w6 & m' & -> & -> & MI' & ST' & MR' & TK' & PE' & LEAF).
    destruct LEAF as (off & OFF0 & FIT & Ep & Est' & Ep2 & Eoff).
    assert (SE : strip st' = strip st2) by (rewrite Est', strip_havoc, strip_enframe_at; reflexivity).
    pose proof (strip_eq_proj _ _ SE) as (Ec & Er & En & Em & _ & _ & Esl & Es).
    assert (HrS : (s_regions st') !! (fst p) = Some rg) by (rewrite Er, Ep; cbn [fst]; exact Hr).
    assert (EA : conc st' p = r_base rg + snd b + 16 + stride * idx + 16 * off).
    { rewrite (conc_region' st' p rg HrS). rewrite Ep. cbn [snd]. subst stride. lia. }
    set (A := conc st' p) in *.
    destruct (ruser_chunk st' m' p rg n MR' HrS Hk ltac:(rewrite Ep; cbn [snd]; lia) ltac:(rewrite Ep; cbn [snd]; subst stride; lia) ltac:(lia)) as (ujunk & UCH).
    fold A in UCH.
    cbn [fst snd]. do 15 eexists. exists m', errv1.
    split; [reflexivity|]. split; [exact MR'|]. split; [exact TK'|]. split; [exact MI'|]. split; [exact ST'|].
    split. { eapply rpres_except_rw_cells; [exact PE'| exact ERR2|]. rewrite TP. unfold RATP. rewrite unsigned_lit by lia.
             change (Z.of_nat (cells_size [C4 errv1])) with 4. intros a Ha [X|X]; subst lo_s hi_s; lia. }
    assert (MRELf : mrel st st') by (eapply mrel_trans; [exact MREL|]; apply mrel_same; assumption).
    assert (PEf : rpres_except (rmalloc_fp st st' lo (bv_unsigned sp)) m m').
    { eapply rpres_except_mono.
      + eapply rpres_except_trans; [exact PE2|].
        eapply rpres_except_mono; [exact PE'|]. intros a [X|X]; [left; left; exact X| apply SPANFP; subst lo_s hi_s stride; exact X].
      + intros a Ha. eapply rmalloc_fp_mono; [|exact Ha]. intros rid r1 H1. exists r1. rewrite Er. repeat split; auto; lia. }
    pose proof (rheap_pres_of_fp st st' LB lo (bv_unsigned sp) m m' MF MR MR' MRELf PEf CLO ltac:(lia)) as HPf.
    split. { eapply (rauxv_ok_malloc_fp st st' lo (bv_unsigned sp) m m' m m' B); [exact MR| exact MR'| exact AUXB| exact PEf| exact CLO| exact SB]. }
    split; [exact HPf|]. split; [exact PEf|]. split; [exact MRELf|].
    split. { unfold brk_link_ps in *. unfold ctx in *. rewrite Ec. unfold conc, get_region. rewrite Er. exact BL2. }
    split; [exact PSM|]. split; [exact PSF|]. split; [exact PSO|].
    exists g, idx, st2, rg, ujunk.
    split; [symmetry; exact SE|].
    split. { unfold slot_of, slot_start'. rewrite Hmem. cbn [default from_option id]. unfold aadd. cbn [fst snd]. rewrite Ep. cbn [fst snd].
             f_equal. subst stride. unfold UNIT.
             replace (snd b + 16 + get_stride (get_meta_rec st2 g) * idx + 16 * off - (snd b + (16 + get_stride (get_meta_rec st2 g) * idx)))
               with (off * 16) by lia. rewrite Z.div_mul by lia. lia. }
    split. { unfold slot_of, slot_start'. rewrite Hmem. cbn [default from_option id]. unfold aadd. cbn [fst snd]. rewrite Ep. cbn [snd].
             subst stride. unfold UNIT.
             replace (snd b + 16 + get_stride (get_meta_rec st2 g) * idx + 16 * off - (snd b + (16 + get_stride (get_meta_rec st2 g) * idx)))
               with (off * 16) by lia. apply Z_mod_mult. }
    split. { unfold slot_of, slot_start'. rewrite Hmem. cbn [default from_option id]. unfold aadd. cbn [fst snd]. rewrite Ep. cbn [snd]. subst stride. unfold UNIT. lia. }
    split; [reflexivity|].
    split. { unfold rblock_range, alloc_ceiling. subst A. rewrite EA.
             split; [lia|]. split; [apply mod16_slot; [exact RAL| exact B16| exact SMOD| lia]|]. subst lo_s hi_s.
             specialize (RI1 ltac:(pose proof (round_up_pg_ge (r_len rg)); lia)). lia. }
    split; [exact HrS|]. split; [exact Hk|]. split; [rewrite Ep; cbn [snd]; lia|]. split; [rewrite Ep; cbn [snd]; subst stride; lia|].
    exact UCH.
  - (* [comment removed for export] *)
    cbn [rcoreQ] in CQ.
    destruct CQ as (m1 & errv1 & u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & -> &
                    MR2 & TK2 & MI2 & ST2 & ERR2 & AUX2 & PE2 & MREL & BL2 & PSM & PSF & PSO).
    apply rimplT_ret. apply evt_done. cbn [fst snd]. do 15 eexists. exists m1, errv1.
    pose proof (rheap_pres_of_fp st st2 LB lo (bv_unsigned sp) m m1 MF MR MR2 MREL PE2 CLO ltac:(lia)) as HPf.
    split; [reflexivity|]. split; [exact MR2|]. split; [exact TK2|]. split; [exact MI2|]. split; [exact ST2|]. split; [exact ERR2|].
    split. { eapply (rauxv_ok_malloc_fp st st2 lo (bv_unsigned sp) m m1 m m1 B); [exact MR| exact MR2| exact AUXB| exact PE2| exact CLO| exact SB]. }
    split; [exact HPf|]. split; [exact PE2|]. split; [exact MREL|]. split; [exact BL2|].
    split; [exact PSM|]. split; [exact PSF|]. split; [exact PSO|]. reflexivity.
Qed.
End TOPLEVEL.

(* [comment removed for export] *)
Theorem rmalloc_implT :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (o m : mem)
         (s : PState) (st : mstate) (LB : list block) (n lo B : Z) (errv : word),
  RAREACH st LB -> rmrep st m -> brk_link_ps st s -> unk_agree st o m ->
  rauxv_ok m B -> bv_unsigned sp <= B ->
  stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 8192 ->
  rw_cells rsegs m (errno_addr tp) [C4 errv] ->
  mem_inv rsegs m ->
  tp = Z_to_bv 64 RATP ->
  a0 = Z_to_bv 64 n -> 0 <= n < 2^32 ->
  rimplT o (malloc st n) s
        (rmallocT_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o s st LB n lo B m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 rmalloc_entry) fc None m (seg_rom rsegs)).
Proof.
  exact (rmalloc_implT_gen ras_pre2 as_inv2 ralloc_slot_spec ras_pre2_intro (rbig_spec ram_pre ralloc_meta_spec ramp_big)).
Qed.
End RC__1.
