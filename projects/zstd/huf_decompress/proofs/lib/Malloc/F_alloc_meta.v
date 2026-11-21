(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (15 recorded proofs replaced by written proofs (magree_trans, magree_of_munch, FP_am and 12 more)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep Walk Arr ITree Nodes Decode.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require MallocKit_A2.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import F_mm_syscalls MallocRep F_malloc_free MallocTree MallocFacts_B MallocFacts_Bpres.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl Monad.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocKit_B MallocModel_B MallocKit_B2 MallocKit_B3 F_ntf_B.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import F_am_A F_am_K F_am_K2 F_am_C F_am_D F_am_E F_am_F F_am_G F_am_H F_am_P.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_F_alloc_meta () := "C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C47Corelib4Init5Logic3notK47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01c59OSSVerify5KrLib6Malloc<F_alloc_meta6magreeC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00C59OSSVerify5KrLib6Malloc:MallocTree3memC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic2eq00C47Corelib4Init5Logic8eq_ind_rI47Corelib4Init9Datatypes4list00C59OSSVerify5KrLib3Lib5Frame5munchC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc;MallocKit_B;ivs_coveredC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame7outsideC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02K47Corelib4Init5Logic3and01K47Corelib4Init9Datatypes4prod01C47Corelib4Init9Datatypes8list_indC45stdpp9bitvector;definitions;bv_unsignedK46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC59OSSVerify5KrLib3Lib3Mem;wa_unsignedC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01C59OSSVerify5KrLib3Lib5Frame3ivlC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01I47Corelib4Init9Datatypes4prod00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C59OSSVerify5KrLib6Malloc6F_am_A5am_fpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc:MallocTree8alloc_fpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc:MallocTree:fresh_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc6F_am_A>am_fp_alloc_fpC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc5rkind00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind03C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C45stdpp9bitvector;definitions7Z_to_bvK47Corelib7Numbers7BinNums1Z03C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib6Common7RunDraw:atop_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega6VarMap1t01C59OSSVerify5KrLib3Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes:comparison00I35stdpp4gmap4gmap00C35stdpp4gmap;gmap_lookupK47Corelib4Init9Datatypes6option01C59OSSVerify5KrLib4Spec6Malloc6r_kindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_baseC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5r_lenC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc<F_alloc_meta2FPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep5lr_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;round_up_pgC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00K47Corelib4Init5Logic2or02C56Stdlib6ZArith6BinInt1Z3oppC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr06K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03C56Stdlib6ZArith6BinInt1Z9land_onesK47Corelib4Init5Logic2ex01C59OSSVerify5KrLib4Spec6Malloc9s_regionsC1?~~~~~~~~~~~~~~~C35stdpp4base6lookupI47Corelib4Init5Logic2ex00K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03I47Corelib7Numbers7BinNums1N00I59OSSVerify5KrLib4Spec6Malloc6region00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep3CTXC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op201C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableK47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init5Logic5False00c59OSSVerify5KrLib6Malloc<F_alloc_meta7FP_monoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep:regions_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:s_reservedC1?~~~~~~~~~~~~~~~C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableC59OSSVerify5KrLib4Spec6Malloc7s_areasC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC59OSSVerify5KrLib4Spec6Malloc8s_groupsC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indK46Stdlib9micromega7EnvRing5PExpr04C59OSSVerify5KrLib6Malloc9MallocRepAreserved_disjointC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep8lr_lo_geC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc>MallocFacts_AM<amp_reservedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc:MallocTree;fresh_imageC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;live_rangesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;ranges_freeC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula06C59OSSVerify5KrLib6Malloc9MallocRep>agent_reservedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc:MallocTree9AUXV_CELLC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4area00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~C45stdpp7numbers1Z6eq_decC35stdpp9countable;Z_countableI59OSSVerify5KrLib4Spec6Malloc4ghdr00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc6F_am_A?am_fp_not_errnoC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc3ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5c_brkC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc8brkstate00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc1MC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7am_takeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4aaddC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc6F_am_A7am_tookC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8AREA_HDRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4concC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5s_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@c_meta_area_tailC1?~~~~~~~~~~~~~~~C35stdpp4gmapBgmap_partial_alterC35stdpp8fin_maps:map_insertC59OSSVerify5KrLib4Spec6MallocGc_avail_meta_area_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocIset_avail_meta_area_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocDset_avail_meta_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7upd_ctxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7a_checkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8a_nslotsC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc4area01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9set_areasC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBset_meta_area_headC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocBset_meta_area_tailC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8c_secretC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes2idC35stdpp6option;from_optionC59OSSVerify5KrLib4Spec6Malloc6a_nextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc6F_am_K8carve_stC1?~~~~~~~~~~~~~~~C35stdpp4base6insertI59OSSVerify5KrLib4Spec6Malloc4mctx00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6NSLOTSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc6F_am_F@carve_st_regionsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc;MallocKit_B7repfootC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc7cellval01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep9area_concC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep:group_concC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:get_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9cell_readC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep:NEED_LOCKSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep;PAGE_SIZE_AC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc7cellval00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep5MLOCKC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc<F_alloc_meta3ETPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MallocAregion_live_rangeC1?~~~~~~~~~~~~~~~C35stdpp4gmap9gmap_foldC47Corelib5Lists7ListDef3mapC47Corelib4Init9Datatypes3appC35stdpp8fin_maps;map_to_listc59OSSVerify5KrLib6Malloc<F_alloc_meta@live_ranges_sameC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc:MallocTree?ranges_free_subC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC46Stdlib5Lists4List9in_or_appC59OSSVerify5KrLib6Malloc:MallocTree>ranges_free_InC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.

Module A2 := MallocKit_A2.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section CANSEC1. Context {rc : runConstT}.
Definition magree (C : Z -> Prop) (m m' : mem) : Prop := forall a, 0 <= a < 2^64 -> ~ C a -> m' (wa a) = m (wa a).

Lemma magree_refl C m : magree C m m.
Proof.
ltac2:(KReplay.run1 (kr_t_F_alloc_meta ()) ["CANSEC1"] "h01Ch11mh22_Hh33_H0h41ap;2p;1p;3g0000j2<Tg000Lj10Tg0011j11Tg001Oj22Tg001lj2;Tg002Hj2:Tg002cj14Tg003<j13Tg003Zj15Tg004=j16Tg004_j17Tg005Nj28Tg005hj39Tg006gR0p-0[R1g007ER2g008?f0R3'<g008]#0R4#1%04#0R4#0#0#0#1'2,;3':f3R5f1R6O1#4%34#5#6P5f2#7O1'8W3W2X40A9633eX12X01P6P3O2W1W0o"). Qed.
Lemma magree_trans (C1 C2 C3 : Z -> Prop) m1 m2 m3 :
  magree C1 m1 m2 -> magree C2 m2 m3 -> (forall a, C1 a -> C3 a) -> (forall a, C2 a -> C3 a) -> magree C3 m1 m3.
Proof. intros A B I1 I2 a Ha Hc. rewrite (B a Ha) by (intros X; apply Hc, I2, X). apply A; [exact Ha|]. intros X; apply Hc, I1, X. Qed.
Lemma magree_of_munch C W m m' : munch W m m' -> ivs_covered C W -> magree C m m'.
Proof.
  intros MU COV a Ha Hc. apply MU. rewrite wa_unsigned by lia.
  revert COV Hc. clear. induction W as [|[lo hi] W IH]; cbn; intros COV Hc; [exact I|].
  destruct COV as [C1 COV]. split; [| apply IH; assumption]. intros Hin. apply Hc. apply C1. exact Hin.
Qed.

(* [comment removed for export] *)
Section ASM.
Variables (R : Type) (k : mstate -> optr -> Malloc.M R) (bail : Malloc.M R) (o : mem) (s : PState) (Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : mstate) (lo : Z) (errv : word).
Hypothesis AMP : AMpre st.
Hypothesis TK : ticks_ok st.
Hypothesis BL : brk_link_ps st s.
Hypothesis LO : ATOP <= lo.
Hypothesis LOLE : lo <= bv_unsigned sp - AM_STACK.
Hypothesis GP : gp = Z_to_bv 64 0x1a800.
Hypothesis TP : tp = Z_to_bv 64 0x1a620.

Definition FP (stX : mstate) (a : Z) : Prop := alloc_fp (fun k => k <> RKGroup) stX lo (bv_unsigned sp) a \/ fresh_addr st a.

Lemma FP_am stX a : am_fp stX lo (bv_unsigned sp) a -> FP stX a.
Proof. intros H. left. apply am_fp_alloc_fp. exact H. Qed.

Lemma ETP : errno_addr tp = 0x1a620 - 164.
Proof. rewrite TP, unsigned_lit by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma FP_mono stX stY a :
  (forall rid r, (s_regions stX) !! rid = Some r -> exists r', (s_regions stY) !! rid = Some r' /\ r_kind r' = r_kind r /\ r_base r' = r_base r /\ r_len r <= r_len r') ->
  FP stX a -> FP stY a.
Proof.
  intros HR [[X|[X|[X|(rid & r & Hr & K & X)]]]|X]; [left; left; exact X| left; right; left; exact X| left; right; right; left; exact X| | right; exact X].
  destruct (HR rid r Hr) as (r' & Hr' & K' & B' & L'). left. right. right. right. exists rid, r'. split; [exact Hr'|]. split; [rewrite K'; exact K|].
  assert (RU : round_up_pg (r_len r) <= round_up_pg (r_len r')).
  { unfold round_up_pg, PGSZ. change (4096 - 1) with (Z.ones 12). rewrite !Z.land_ones by lia. Z.div_mod_to_equations. lia. }
  unfold lr_lo in *. rewrite K', B'. lia.
Qed.

Lemma FP_same stX stY a : s_regions stY = s_regions stX -> FP stX a -> FP stY a.
Proof. intros E. apply FP_mono. intros rid r Hr. exists r. rewrite E. repeat split; auto; lia. Qed.

Lemma FP_below stX a : regions_wf stX -> FP stX a -> a < bv_unsigned sp /\ ~ (AUXV_CELL <= a < AUXV_CELL + 8).
Proof.
  intros (_ & WR & _) [[X|[X|[X|(rid & r & Hr & K & X)]]]|X]; rewrite ?TP in X; unfold AUXV_CELL, LIBC, CTX, AM_STACK in *;
    rewrite ?unsigned_lit in X by lia; [lia| lia| lia| |].
  - destruct (WR _ _ Hr) as (_ & _ & _ & RBC & RF). destruct (reserved_disjoint _ _ RF) as [D1 D2]. pose proof (lr_lo_ge r). atop_facts. lia.
  - pose proof (fresh_image st a X (amp_reserved st AMP)). destruct X as [C _]. atop_facts. lia.
Qed.

Lemma errno_not_amfp stX a : regions_wf stX -> am_fp stX lo (bv_unsigned sp) a -> ~ (errno_addr tp <= a < errno_addr tp + 4).
Proof. intros WF X. rewrite TP. eapply am_fp_not_errno; [exact X| exact WF| exact LO]. Qed.

(* [comment removed for export] *)
Lemma brk_am_took X q c : c_brk (ctx (am_took X q c)) = c_brk (ctx X).
Proof.
ltac2:(KReplay.run1 (kr_t_F_alloc_meta ()) ["CANSEC1"; "ASM"] "h01Xh11ch21qp;1p;2g01RUj12Tg01SIj11Tg005Nj20Tg00UDR0g01O0R1g006gR2g01T?f2R3#2#1'0X12X21X00P3f1f0O3W1W2W0o"). Qed.
(* [comment removed for export] *)
Lemma am_take_took {RR} (Xst : mstate) (pp : aptr) (kk : mstate -> optr -> Malloc.M RR) (bl : Malloc.M RR) :
  am_take (upd_ctx (fun c => set_avail_meta (Some (aadd pp AREA_HDR)) (set_avail_meta_count NSLOTS c)) Xst) kk bl
  = kk (am_took Xst (aadd pp AREA_HDR) 100) (Some (aadd pp AREA_HDR)).
Proof. reflexivity. Qed.
Lemma conc_am_took X q c y : conc (am_took X q c) y = conc X y.
Proof.
ltac2:(KReplay.run1 (kr_t_F_alloc_meta ()) ["CANSEC1"; "ASM"] "h01Xh11ch21qh31yp;2g01ZAj21Tg005Nj20Tg00UDR0g01O0R1g006gR2f3R3f0R4'1,02X31X12X21X00P3f2f1P4O4X31W1W2W0o"). Qed.
Lemma brk_carve stY p : c_brk (ctx (carve_st stY p)) = c_brk (ctx stY).
Proof.
  unfold carve_st. cbn [ctx upd_ctx s_ctx set_avail_meta_areas set_avail_meta_area_count c_meta_area_tail].
  destruct (c_meta_area_tail (s_ctx stY)); reflexivity.
Qed.
Lemma conc_carve stY p y : conc (carve_st stY p) y = conc stY y.
Proof. unfold conc, get_region. rewrite carve_st_regions. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma repfoot_low stY a : regions_wf stY -> repfoot stY a -> a < ATOP /\ ~ (errno_addr tp <= a < errno_addr tp + 4).
Proof.
  intros WF H. rewrite ETP. pose proof WF as (_ & WR & _ & WA & WG). atop_facts.
  destruct H as [C|[C|[C|[C|[C|[C|C]]]]]]; unfold CTX, MLOCK, NEED_LOCKS, MallocRep.PAGE_SIZE_A in *; try lia.
  - destruct C as (ak & ar & Hak & Hin). destruct (area_conc stY ak ar WF Hak) as (rra & Hra & Ca & Sa0 & Sa1 & SaL & NKa & RB0 & RBAL & RBC).
    destruct (WR _ _ Hra) as (_ & _ & _ & _ & RF). destruct (reserved_disjoint _ _ RF) as [D1 D2]. atop_facts. lia.
  - destruct C as (b & gh & Hb & Hin). destruct (group_conc stY b gh WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & Al & RB0 & RBC).
    destruct (WR _ _ Hrb) as (_ & _ & _ & _ & RF). destruct (reserved_disjoint _ _ RF) as [D1 D2]. atop_facts. lia.
  - destruct C as (rid & rg & v & Hrg & Krg & Hin & _). destruct (WR _ _ Hrg) as (_ & _ & _ & RBC & RF). destruct (reserved_disjoint _ _ RF) as [D1 D2]. atop_facts. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma live_ranges_same stA stB : s_regions stB = s_regions stA -> s_reserved stB = s_reserved stA -> live_ranges stB = live_ranges stA.
Proof. intros E1 E2. unfold live_ranges. rewrite E1, E2. reflexivity. Qed.

Lemma fresh_of_ranges_free stY x L a :
  s_regions stY = s_regions st -> s_reserved stY = s_reserved st ->
  ranges_free (live_ranges stY) x L = true -> x + L <= ATOP -> x <= a < x + L -> fresh_addr st a.
Proof.
  intros E1 E2 RF XC Ha. split; [lia|]. rewrite (live_ranges_same st stY E1 E2) in RF.
  eapply ranges_free_sub; [exact RF| lia| lia| lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma image_range_clear stY x L : s_reserved stY = agent_reserved -> ranges_free (live_ranges stY) x L = true -> 0 < L ->
  x + L <= 0x10000 \/ 0x1b000 <= x.
Proof.
  intros RS RF HL. unfold live_ranges in RF. rewrite RS in RF.
  pose proof (ranges_free_In _ _ _ _ _ RF ltac:(apply in_or_app; left; left; reflexivity)).
  pose proof (ranges_free_In _ _ _ _ _ RF ltac:(apply in_or_app; left; right; left; reflexivity)). cbn in *. lia.
Qed.
End ASM.

End CANSEC1.
