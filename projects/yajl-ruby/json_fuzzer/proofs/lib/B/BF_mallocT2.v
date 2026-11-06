(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import base decidable list gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr NodesCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import AImages AImageFacts ExecA LazyModel NodesA ImplRzA Shadow StepA StepA2 SysStepA.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import StdioBase Malloc.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanConsts AsanSizeClass AsanState AsanLayout AsanOps AsanFakeStack AsanPS AsanRep AsanKern AsanClient AsanBudget AsanBudget2 AsanRepFrame AsanDepot AsanGap AsanSlack.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import B_base B_alloc_iface B_iface BF_fakestack_rep BF_place BF_unwind BF_unwind_walk2 BF_kit BF_kit3 BF_mallocG BX_unreg BX_Exit BF_statics B_live B_policy5 B_budget5 B_slack5 B_bundle B_benv5 B_init5 B_instD5 B_balloc5 B_bpolicy5 B_rtok5 B_bframe B_bframe2 BF_tkit BF_alloc_iface BF_glue_kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
#[warnings="-notation-for-abbreviation"] Notation mem := (word -> option byte).
#[warnings="-notation-for-abbreviation"] Notation wz := (fun z : Z => Z_to_bv 64 z).

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac unset_all := repeat match goal with x := _ |- _ => subst x end.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import LiaA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac lia ::= LiaA.liaA.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.

(* [comment removed for export] *)
Lemma high_byte_eq : forall (m m' : mem) A b,
  rw_cells bsegs m A [C1 b] -> rw_cells bsegs m' A [C1 b] -> (A + 1 <= 0x10000 \/ 0x603000 <= A) -> 0 <= A < 2^64 -> m' (wa A) = m (wa A).
Proof.
  intros m m' A b [[_ (_ & _ & R1)] _] [[_ (_ & _ & R2)] _] HA HA'.
  specialize (R1 0%nat ltac:(cbn; lia)). specialize (R2 0%nat ltac:(cbn; lia)). cbn in R1, R2. rewrite Z.add_0_r in R1, R2.
  unfold mrd in R1, R2. rewrite (both_seg_rom_none (wa A)) in R1, R2 by (rewrite wa_unsigned by lia; lia).
  destruct (m (wa A)); destruct (m' (wa A)); congruence.
Qed.

Section MallocT2.
Variable E0 : aenv.
Variable FSB0 : Z.
Variable HR0 : list (Z * Z).
Variables L0 RES0 : list (word * word).
Variable EB0 : Z.
Variable PL0 : fs_plumb.
Hypothesis ENV0 : env0_ok5 E0.
Hypothesis PL0OK : pl0_ok5 E0 PL0.
Hypothesis HR0_ok : Forall (fun iv => fst iv <= snd iv) HR0 /\ A0_pages HR0 <= 8192.
Hypothesis EB0_ok : 0 <= EB0 <= 2^32.
Hypothesis ENV_depot : zlen (ae_keys0 E0) <= 1000 /\ 0 <= ae_frames0 E0 <= 4096.
Hypothesis HS_tot : gw_sizes (RES0 ++ L0) <= 2^46 /\ (length (RES0 ++ L0) <= 256)%nat.
(* [comment removed for export] *)
Hypothesis ALLOC : allocate_srz_stmt E0 FSB0 HR0 L0 RES0 EB0 PL0.

#[local] Notation AHKc := (BF_tkit.AHKc E0 FSB0 HR0 L0 RES0 EB0 PL0).
#[local] Notation SR := stdio_rep.
#[local] Notation RT := (rt_misc5 FSB0 PL0).
#[local] Notation rt_fpE := (fun E a => rt_fpc E FSB0 PL0 a).
Ltac cstat := try clear ALLOC; try clear HS_tot; try clear ENV_depot; try clear EB0_ok; try clear HR0_ok; try clear PL0OK; try clear ENV0.
Ltac wfe_open WE :=
  destruct WE as (WE1 & WE2 & WE3 & WE4 & WE5 & WE6 & WE7 & WE8 & WE9 & WE10 & WE11 & WE12 & WE13 & WE14 & WE15 & WE16 & WE17 & WE18 &
                  WE19 & WE20 & WE21 & WE22 & WE23 & WE24 & WE25 & WE26 & WE27 & WE28 & WE29 & WE30 & WE31 & WE32 & WE33 & WE34 & WE35rest).

(* [comment removed for export] *)
Definition shell_facts (m : mem) : Prop :=
  let T := ae_thread E0 in let CTX := fp_ctx PL0 in
     rw_cells bsegs m 0xaf298 [C1 (Z_to_bv 8 1)] /\ rw_cells bsegs m 0xaf2bc [C4 (wz 30)]
  /\ rw_cells bsegs m 0xa5590 [C8 (wz 0x1400e8)] /\ rw_cells bsegs m 0x14010a [C1 (Z_to_bv 8 1)]
  /\ rw_cells bsegs m 0xa5580 [C8 (wz 0x13e060)] /\ rw_cells bsegs m 0x13e060 [C8 (wz 4096)]
  /\ uthread_cells m (wz 0x5e1550) 0x6028f8 CTX T (ae_stack_top E0) (ae_stack_bottom E0)
  /\ (0x603000 <= CTX /\ CTX + 4096 <= alloc_ceiling)
  /\ ((0x1000 <= T /\ (T + 4096 <= 0x10000 \/ 0x603000 <= T)) /\ T + 4096 <= alloc_ceiling)
  /\ (CTX + 160 <= T \/ T + 4096 <= CTX)
  /\ (0 <= ae_stack_bottom E0 < ae_stack_top E0 /\ ae_stack_top E0 <= 2^47)
  /\ (exists c0 cl, resv_range_ok E0 c0 cl /\ c0 <= CTX /\ CTX + 160 <= c0 + cl).

Lemma shell_facts_of : forall s LB LF m mo, AHKc s LB LF m mo -> shell_facts m.
Proof.
  intros s LB LF m mo AH. unfold BF_tkit.AHKc in AH. pose proof AH as AH0. ahk_open AH.
  destruct (AHK_env _ _ _ _ _ _ _ _ _ _ _ _ _ AH0) as [EE EFS]. rewrite EE in *.
  pose proof Hrep as REP. destruct REP as (Rins & Rri & Rrm & Rthr & Rsec & Rch & Rbat & Rdep & Rglob & Rsh).
  pose proof Rthr as (Ttop & T40 & Tq & Tcache & Tcst & Tst & Tby & Tunw).
  pose proof Rglob as (Gfl & Gfu & Gth & Gdd & Gsh & Ghe & Gcp & Gai & Gmcs & Gps & _).
  pose proof ENV0 as EV. destruct EV as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & N13 & N14 & N15 & NB0 & NT47 & IC0 & NTD & NDP).
  rewrite IC0 in Gfu, Gai, Gmcs, Gps. cbn [aic_common_flags aic_asan_inited aic_malloc_context_size aic_page_size_cached both_ic] in Gfu, Gai, Gmcs, Gps.
  pose proof Hrt as (_ & [tX XS] & FSE & AMS & [ATH1 ATH2]). assert (US : unreg_statics m) by (unfold exit_statics in XS; decompose [and] XS; assumption).
  unreg_statics_open US.
  unfold FSEnv in FSE. pose proof FSE as (_ & _ & FAI & _ & _ & _ & FKI & FKEY & FTSD & FTSD0 & FCTXT & _). unfold FS_TP in *.
  pose proof (proj1 Hwf) as WE. wfe_open WE.
  destruct PL0OK as ((c0 & cl & RRC & CLO & CHI) & _ & RRT & TCX0 & _ & _ & [IA1 IA2]).
  destruct Henv as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & [EI1 EI2]). rewrite EE in EI1, EI2.
  unfold shell_facts. cbv zeta.
  split; [exact Gai|]. split; [unfold kMallocContextSize in Gmcs; exact Gmcs|]. split; [exact GCF|]. split; [exact Gfu|]. split; [exact GPSC|].
  split; [unfold kPageSize in Gps; exact Gps|].
  split. { split; [| split; [exact T40| split; [unfold kThrStackTop in Ttop; exact Ttop| unfold kThrUnwinding in Tunw; exact Tunw]]].
           split; [exact FKI|]. split; [exact FKEY|]. split; [| split; [exact FTSD0| exact FCTXT]].
           replace (bv_unsigned (Z_to_bv 64 0x5e1550) + -88) with 0x5e14f8 by (rewrite unsigned_lit; [reflexivity| clear; lia]). exact FTSD. }
  split. { pose proof WE35rest as IS. unfold img_sep in IS. rewrite EI1 in IS. unfold app_mem in WE25. rewrite ?kHighMemBeg_val, ?kLowAppEnd_val in WE25. unfold kIArenaLen in *.
           cstat. clear -IA1 IA2 WE25 WE26 IS EI2. lia. }
  split. { destruct RRT as (_ & (P1 & P2 & P3 & _) & _). unfold A_IMG_END in P3. cstat. clear -P1 P2 P3. lia. }
  split; [exact TCX0|]. split; [cstat; clear -WE6 NB0 NT47; lia|].
  exists c0, cl. cstat. auto.
Qed.

(* [comment removed for export] *)
Definition mid_facts (s : aps) (LB : list ablock) (LF : list fblock) (m : mem) (mo : Model) (usp lo n : Z) (m1 : mem) (mo1 : Model)
    (ws tr : list word) (bpw : word) (j1800 j8 : list byte) (ra s0 s1 s2 s3 s4 s5 : word) : Prop :=
     AHKc s LB LF m1 mo1
  /\ munch [(usp + -2400, usp)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo (usp + -2144)
  /\ rw_cells bsegs m1 (usp + -2128) [C8 (wz (usp + -2112)); C8 (wz (Z.of_nat (length tr)))]
  /\ u64arr bsegs m1 (usp + -2112) ws /\ length ws = 30%nat /\ (1 <= length tr <= 30)%nat
  /\ rw_cells bsegs m1 (usp + -2144) [C8 (wz usp); C8 (wz 0x541b4)]
  /\ rw_cells bsegs m1 (usp + -1872) [CB 1800 j1800] /\ rw_cells bsegs m1 (usp + -72) [C8 bpw] /\ rw_cells bsegs m1 (usp + -64) [CB 8 j8]
  /\ rw_cells bsegs m1 (usp + -56) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] /\ rw_cells bsegs m1 (usp + -16) [C8 s0; C8 ra]
  /\ m_fs mo1 = m_fs mo /\ m_fds mo1 = m_fds mo.

Definition fin_facts (s : aps) (LB : list ablock) (LF : list fblock) (m : mem) (mo : Model) (usp lo n : Z)
    (m3 : mem) (mo3 : Model) (s' : aps) (A : Z) (a0' : word) : Prop :=
     stk bsegs m3 lo usp /\ aheap_pres bsegs ACONSTS LB LF usp m m3 /\ wmono bsegs m m3 /\ aps_so s' = aps_so s
  /\ amalloc_rel E0 n s mo (Some A) s' mo3 /\ m_fs mo3 = m_fs mo /\ m_fds mo3 = m_fds mo /\ aps_credit s - acharge n <= aps_credit s'
  /\ a0' = wz A /\ ablock_range ACONSTS A n /\ AHKc s' (mkABlock A n :: LB) LF m3 mo3
  /\ (exists junk, length junk = Z.to_nat n /\ rw_cells bsegs m3 A [CB (Z.to_nat n) junk])
  /\ block_shadow bsegs m3 A_SB A n.

(* [comment removed for export] *)
Definition PP (s : aps) (mo : Model) : acc -> Prop := fun x => acc_ok (m_vm_lazy mo) (aS E0 FSB0 HR0 s) x.
Lemma EPOL : forall s mo a k, POL E0 FSB0 HR0 s mo a k = PP s mo (Z_to_bv 64 a, k). Proof. intros; reflexivity. Qed.

(* [comment removed for export] *)
Lemma malloc_enter :
  forall (ra sp gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : aps) (LB : list ablock) (LF : list fblock)
         (n lo : Z) (Tk : TSet),
  AHKc s LB LF m mo ->
  stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - AMALLOC_STACK -> bv_unsigned sp mod 16 = 0 -> bv_unsigned sp < 2^47 ->
  uanchor bsegs m (bv_unsigned sp) ra s0 -> 0 < n <= 2^27 ->
  (forall (t0' t1' t2' a6' a7' s2w s3w s5w t3' t4' t5' t6' : word) (m1 : mem) (mo1 : Model) (ws tr : list word) (bpw : word) (j1800 j8 : list byte),
     mid_facts s LB LF m mo (bv_unsigned sp) lo n m1 mo1 ws tr bpw j1800 j8 ra s0 s1 s2 s3 s4 s5 ->
     realizes_cfg acfg bsegs (mkCfg (MS (mkR (wz A_ALLOC_RET) (wz (bv_unsigned sp + -2144)) gp (wz 0x5e1550) t0' t1' t2' (wz (bv_unsigned sp)) (wz n)
                                     (wz 0xaaf58) (wz n) (wz 8) (wz (bv_unsigned sp + -2128)) (wz 1) (wz 1) a6' a7'
                                     s2w s3w (wz (bv_unsigned sp + -2128)) s5w s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                F (wz 0x32a0c) fc None m1 (seg_rom bsegs)) mo1) Tk) ->
  realizes_cfg acfg bsegs (mkCfg (MS (mkR ra sp gp (wz 0x5e1550) t0 t1 t2 s0 s1 (wz n) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz (c_wrap_malloc ACONSTS)) fc None m (seg_rom bsegs)) mo) Tk.
Proof.
  intros until Tk. intros AH SK LOC LO SPA SPH UA Hn2 INNER.
  destruct (shell_facts_of _ _ _ _ _ AH) as (Gai & Gmcs & GCF & Gfu & GPSC & Gps & TC & HCTX & HT & HTC & HTB & (c0 & cl & RRC & CLO & CHI)).
  pose proof AH as AH0. unfold BF_tkit.AHKc in AH. ahk_open AH.
  destruct (AHK_env _ _ _ _ _ _ _ _ _ _ _ _ _ AH0) as [EE EFS]. pose proof Henv as ENVOK0. rewrite EE in Hwf, Hkern.
  destruct Hkm as (Khalt & Kminv & Klim).
  remember (bv_unsigned sp) as usp eqn:Husp in *.
  assert (Esp : sp = wz usp) by (rewrite Husp; symmetry; apply Z_to_bv_bv_unsigned).
  assert (USPR : 0 <= usp < 2^64) by (rewrite Husp; pose proof (bv_unsigned_in_range 64 sp) as BR; unfold bv_modulus in BR; clear -BR; lia).
  rewrite Esp. clear Esp Husp. unfold AMALLOC_STACK in LO. pose proof alloc_ceiling_range as CEILB.
  pose proof (proj1 Hwf) as WE.
  (* [comment removed for export] *)
  assert (PSTK : forall a' k, lo <= a' -> a' + Z.of_nat k <= 2^64 -> PP s mo (Z_to_bv 64 a', k)).
  { intros a' k H1 H2. rewrite <- EPOL. eapply (pol_stack' E0 FSB0 HR0 s mo Hkern WE ENV0); clear -H1 H2 LOC; lia. }
  assert (PDAT : forall a' k, 0xa5000 <= a' -> a' + Z.of_nat k <= 0x603000 -> PP s mo (Z_to_bv 64 a', k)).
  { intros a' k H1 H2. rewrite <- EPOL. eapply (pol_img' E0 FSB0 HR0 s mo Hkern WE ENVOK0 ENV0); clear -H1 H2; lia. }
  assert (PCTX : PP s mo (Z_to_bv 64 (fp_ctx PL0 + 152), 8%nat)).
  { rewrite <- EPOL. eapply (pol_resv_range' E0 FSB0 HR0 s mo Hkern c0 cl); [exact RRC| clear -CLO; lia| clear -CHI; cbn; lia]. }
  assert (PTHR : forall a' k, ae_thread E0 <= a' -> a' + Z.of_nat k <= ae_thread E0 + 4096 -> PP s mo (Z_to_bv 64 a', k)).
  { intros a' k H1 H2. rewrite <- EPOL. eapply (pol_thread' E0 FSB0 HR0 s mo Hkern WE); assumption. }
  assert (KIP0 : KIP (aS E0 FSB0 HR0 s) (aN E0 FSB0 HR0 s) (aEB EB0 s) (PP s mo) mo) by (split; [exact (AHK_kia _ _ _ _ _ _ _ _ _ _ _ _ _ AH0)| intros x Hx; exact Hx]).
  (* [comment removed for export] *)
  eapply (rzA_seg_cfg bsegs (aS E0 FSB0 HR0 s) (aN E0 FSB0 HR0 s) (aEB EB0 s) (PP s mo)); [| exact KIP0|].
  { stepA.
    lazymatch goal with |- evtA _ _ _ (MS ?r ?f ?pc ?x1 ?x2 ?x3 ?x4) => let v := eval vm_compute in (bv_unsigned pc) in change pc with (Z_to_bv 64 v) end.
    eapply (malloc_pre (PP s mo) gp (wz 0x5e1550) s6 s7 s8 s9 s10 s11 F fc usp lo n 0x6028f8 (fp_ctx PL0) (ae_thread E0) (ae_stack_top E0) (ae_stack_bottom E0));
      [ exact LOC| clear -LO; lia| exact SPH| clear -Hn2; lia| clear; cbn; lia| exact HCTX| exact HT| exact HTC| rewrite unsigned_lit by (clear; lia); clear; cbn; lia| exact HTB
      | exact PSTK| exact PDAT| exact PCTX| exact PTHR
      | exact SK| exact Hmi| exact Gai| exact Gmcs| exact GCF| exact Gfu| exact GPSC| exact Gps
      | exact TC| exact UA ]. }
  intros ms1 mo1 POST1 Hag1 KP1.
  destruct POST1 as (t0' & t1' & t2' & a6' & a7' & s2w & s3w & s5w & t3' & t4' & t5' & t6' & m1 & ws & tr & bpw & j1800 & j8 & -> & MU1 & WM1 & MI1 & SK1 & OBJ & TR & LEN30 & LTR & FTR & TU1 & FAM & FJ1800 & FBP & FJ8 & FR5 & CL).
  (* [comment removed for export] *)
  destruct TC as (_ & _ & _ & Tunw).
  assert (MU1' : munch [(usp + -2400, usp)] m m1).
  { intros aw Hout. destruct (Z.eq_dec (bv_unsigned aw) (ae_thread E0 + 3168)) as [E|NE].
    - replace aw with (wa (ae_thread E0 + 3168)) by (rewrite <- E; apply Z_to_bv_bv_unsigned).
      apply (high_byte_eq m m1 (ae_thread E0 + 3168) (Z_to_bv 8 0)); [exact Tunw| exact TU1| clear -HT; lia| clear -HT CEILB; lia].
    - apply MU1. cbn [outside] in Hout |- *. destruct Hout as [H1 _]. repeat split; [exact H1| clear -NE; lia]. }
  assert (AH1 : AHKc s LB LF m1 mo1).
  { unfold BF_tkit.AHKc. eapply (AHK_magree SR RT E0 FSB0 HR0 L0 RES0 EB0 s LB LF m1 mo mo1); [| exact Hag1| exact (proj1 (proj1 KP1))].
    eapply (AHK_frame_cl SR RT E0 FSB0 HR0 L0 RES0 EB0 PL0 ENV0 PL0OK (rt_fpc E0 FSB0 PL0) (rt_misc5_agree E0 FSB0 PL0) (rt_fpc_where E0 FSB0 PL0) so_fpc stdio_rep_agree so_fpc_where
              s LB LF m m1 mo [(usp + -2400, usp)] AH0 MU1' WM1).
    constructor; [left; cbn [fst]; clear -LO LOC; lia| constructor]. }
  pose proof (magree_frame _ _ Hag1) as (Qfds1 & Qvm1 & Qlz1 & Qfs1 & _).
  apply (INNER _ _ _ _ _ _ _ _ _ _ _ _ m1 mo1 ws tr bpw j1800 j8). unfold mid_facts. repeat match goal with |- _ /\ _ => split end; try assumption; clear -LTR; lia.
Qed.

(* [comment removed for export] *)
Lemma mid_pre : forall s LB LF m mo usp lo n m1 mo1 ws tr bpw j1800 j8 ra s0 s1 s2 s3 s4 s5,
  AHKc s LB LF m mo -> acharge n <= aps_credit s -> nbig LB <= 8000 ->
  mid_facts s LB LF m mo usp lo n m1 mo1 ws tr bpw j1800 j8 ra s0 s1 s2 s3 s4 s5 ->
  RTOK E0 FSB0 HR0 L0 RES0 EB0 (aps_credit s) OPSLACK s mo1 /\ AINV E0 FSB0 PL0 (aps_alloc s) m1 mo1
  /\ abudget_pre (aps_alloc s) n /\ nbig_live (aps_alloc s) <= 8000.
Proof.
  intros until s5. intros AH CHG NBIG MID.
  destruct MID as (AH1 & MU1' & WM1 & _).
  pose proof AH as AH0. unfold BF_tkit.AHKc in AH. ahk_open AH.
  destruct (AHK_env _ _ _ _ _ _ _ _ _ _ _ _ _ AH0) as [EE EFS]. rewrite EE in *.
  split; [exact (RTOK_open SR RT E0 FSB0 HR0 L0 RES0 EB0 HR0_ok EB0_ok ENV_depot HS_tot s LB LF m1 mo1 AH1 NBIG)|].
  pose proof AH1 as AH1c. unfold BF_tkit.AHKc in AH1c.
  destruct AH1c as (Hrep1 & _ & Hkern1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hrt1 & _ & _ & _ & _ & Hmi1 & _). rewrite EE in *.
  split. { split; [exact Hrep1|]. split; [exact Hwf|]. split; [exact Hkern1|]. split; [exact Hres|]. split; [exact Hqb|]. split; [exact Hdi|]. split; [exact Hbinv|]. split; [exact Hmi1| split; [exact Hrt1| split; [exact Hss| exact Hcs]]]. }
  split.
  { pose proof Hbud as (BU0 & BU1 & BU2 & BU3). unfold ACC in BU3.
    pose proof (DEP_nonneg LB) as DEPnn. pose proof (AsanBudget2.zlen_nonneg (as_residue (aps_alloc s))) as ZR. unfold abudget_pre. cstat. clear -BU0 BU1 BU2 BU3 DEPnn ZR CHG. lia. }
  unfold nbig_live. unfold nbig in NBIG. unfold blocks_match in Hbm.
  assert (FM : forall (l : list ablock), List.filter (fun b : Z * Z => 64512 <? snd b) (map (fun b => (ab_addr b, ab_size b)) l)
                                      = map (fun b => (ab_addr b, ab_size b)) (List.filter (fun b => 64512 <? ab_size b) l)).
  { clear. induction l as [|b l IH]; [reflexivity|]. cbn [map List.filter snd]. destruct (64512 <? ab_size b); cbn [map]; rewrite IH; reflexivity. }
  rewrite <- (Permutation_length (Permutation_filterb _ _ _ Hbm)), FM, length_map. exact NBIG.
Qed.

(* [comment removed for export] *)
Lemma malloc_leave :
  forall (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : aps) (LB : list ablock) (LF : list fblock)
         (n lo : Z) (m1 : mem) (mo1 : Model) (ws tr : list word) (bpw : word) (j1800 j8 : list byte)
         (t0'' t1'' t2'' a0' a1'' a2'' a3'' a4'' a5'' a6'' a7'' s2w s3w s5w t3'' t4'' t5'' t6'' : word) (m2 : mem) (mo2 : Model) (a' : astate) (r : Z) (Tk : TSet),
  let usp := bv_unsigned sp in
  AHKc s LB LF m mo -> alloc_ceiling <= lo -> lo <= usp - AMALLOC_STACK -> usp < 2^47 -> 0 < n <= 2^27 -> acharge n <= aps_credit s -> frm0 fc ->
  mid_facts s LB LF m mo usp lo n m1 mo1 ws tr bpw j1800 j8 ra s0 s1 s2 s3 s4 s5 ->
  alloc_post_state E0 FSB0 HR0 L0 RES0 EB0 PL0 (aps_alloc s) a' m1 m2 mo1 mo2 s (aps_credit s) OPSLACK n lo (bv_unsigned (wz (usp + -2144))) (bst_key (Z.of_nat (length tr)) ws) r a0' ->
  (forall (u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 : word) (m3 : mem) (mo3 : Model) (s' : aps),
     fin_facts s LB LF m mo usp lo n m3 mo3 s' r a0' ->
     realizes_cfg acfg bsegs (mkCfg (MS (mkR ra sp gp (wz 0x5e1550) u0 u1 u2 s0 s1 a0' v1 v2 v3 v4 v5 v6 v7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6) F (ret_pc ra) fc None m3 (seg_rom bsegs)) mo3) Tk) ->
  realizes_cfg acfg bsegs (mkCfg (MS (mkR (wz A_ALLOC_RET) (wz (usp + -2144)) gp (wz 0x5e1550) t0'' t1'' t2'' (wz usp) (wz n) a0' a1'' a2'' a3'' a4'' a5'' a6'' a7''
                               s2w s3w (wz (usp + -2128)) s5w s6 s7 s8 s9 s10 s11 t3'' t4'' t5'' t6'')
                          F (ret_pc (wz A_ALLOC_RET)) fc None m2 (seg_rom bsegs)) mo2) Tk.
Proof.
  intros until Tk. cbv zeta. intros AH LOC LO SPH Hn2 CHG FRM MID POST2 CONT.
  destruct (shell_facts_of _ _ _ _ _ AH) as (_ & _ & _ & _ & _ & _ & _ & HCTX & HT & HTC & HTB & _).
  destruct MID as (AH1 & MU1' & WM1 & MI1 & SK1 & OBJ & TR & LEN30 & LTR & FAM & FJ1800 & FBP & FJ8 & FR5 & CL & Qfs1 & Qfds1).
  pose proof AH as AH0. unfold BF_tkit.AHKc in AH. ahk_open AH.
  destruct (AHK_env _ _ _ _ _ _ _ _ _ _ _ _ _ AH0) as [EE EFS]. pose proof Henv as ENVOK0. rewrite EE in Hwf, Hkern.
  remember (bv_unsigned sp) as usp eqn:Husp in *.
  assert (Esp : sp = wz usp) by (rewrite Husp; symmetry; apply Z_to_bv_bv_unsigned).
  assert (USPR : 0 <= usp < 2^64) by (rewrite Husp; pose proof (bv_unsigned_in_range 64 sp) as BR; unfold bv_modulus in BR; clear -BR; lia).
  rewrite Esp in CONT. clear Esp Husp. unfold AMALLOC_STACK in LO. pose proof alloc_ceiling_range as CEILB.
  pose proof (proj1 Hwf) as WE.
  destruct POST2 as (SK2 & WM2 & (W & MUA & FWA & FBA) & RUN & AINV2 & TOK2 & Ffs2 & Ffds2 & Ftid2 & ACCT & EA0 & AR & PERM & JUNK & BSH).
  rewrite unsigned_lit in SK2, FWA by (clear -LO LOC USPR CEILB; lia).
  pose proof AINV2 as (Hrep2 & WF2 & K2 & RO2 & QB2 & DI2 & BI2 & MI2 & Hrt2 & SS2 & CS2).
  (* [comment removed for export] *)
  set (sq := mkAPS (aps_env s) a' (aps_fs s) (aps_fsbase s) (aps_so s) (aps_errno s) (aps_initialized s) (aps_credit s - acharge n)).
  set (LB2 := mkABlock r n :: LB).
  destruct (RTOK_ATOK E0 FSB0 HR0 L0 RES0 EB0 _ _ _ _ TOK2) as (R2 & R2' & ATOK2 & _).
  destruct AR as (A1 & A2 & A3 & A4 & A5). cbn [c_img_hi ACONSTS] in A5.
  assert (BM2 : blocks_match LB2 a').
  { unfold blocks_match. subst LB2. cbn [map ab_addr ab_size]. etransitivity; [| apply Permutation_sym; exact PERM]. apply perm_skip. exact Hbm. }
  assert (AH2 : AHKc sq LB2 LF m2 mo2).
  { pose proof ACCT as (AC1 & AC2 & AC3 & AC4). pose proof Hbud as (BU0 & BU1 & BU2 & BU3).
    unfold BF_tkit.AHKc.
    eapply (AHK_close SR RT E0 FSB0 HR0 L0 RES0 EB0 PL0 ENV0 PL0OK rt_fpE (rt_misc5_agree E0 FSB0 PL0) (rt_fpc_where2 E0 FSB0 PL0) so_fpc stdio_rep_agree so_fpc_where2
              s sq LB LF m1 mo1 a' m2 mo2 LB2 W lo (usp + -2144) R2 R2' AH1);
      [reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| exact Hrep2| exact WF2| exact K2| exact RO2| exact QB2| exact DI2| exact BI2| exact SS2| exact CS2| exact BM2| exact ATOK2| exact MI2| exact MUA| exact FWA| exact LOC
      | cbn [aps_credit sq]; clear -CHG BU0; lia
      | clear -BU1 AC1; unset_all; lia
      | clear -BU2 AC2; unset_all; lia
      | ].
    cbn [aps_credit sq aps_alloc]. subst LB2. rewrite DEP_cons. cbn [ab_size]. cstat. clear -AC4. unset_all. lia. }
  (* [comment removed for export] *)
  pose proof AH2 as AH2c. unfold BF_tkit.AHKc in AH2c.
  destruct AH2c as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hkm2 & Hli2 & _ & _ & Henv2 & _). destruct Hkm2 as (Khalt2 & Kminv2 & Klim2).
  assert (PSTK2 : forall a'' k, lo <= a'' -> a'' + Z.of_nat k <= 2^64 -> PP sq mo2 (Z_to_bv 64 a'', k)).
  { intros a'' k H1 H2. rewrite <- EPOL. eapply (pol_stack' E0 FSB0 HR0 sq mo2 K2 WE ENV0); clear -H1 H2 LOC; lia. }
  assert (PDAT2 : forall a'' k, 0xa5000 <= a'' -> a'' + Z.of_nat k <= 0x603000 -> PP sq mo2 (Z_to_bv 64 a'', k)).
  { intros a'' k H1 H2. rewrite <- EPOL. eapply (pol_img' E0 FSB0 HR0 sq mo2 K2 WE Henv2 ENV0); clear -H1 H2; lia. }
  assert (KIP2 : KIP (aS E0 FSB0 HR0 sq) (aN E0 FSB0 HR0 sq) (aEB EB0 sq) (PP sq mo2) mo2) by (split; [exact (AHK_kia _ _ _ _ _ _ _ _ _ _ _ _ _ AH2)| intros x Hx; exact Hx]).
  destruct (errno_cell m2) as [errw ERR2].
  (* [comment removed for export] *)
  Ltac survive H MUA WM2 FWA Hwf WF2 K2 := eapply (shell_cells_pres E0 ENV0 _ _ _ _ _ _ _ _ _ _ MUA WM2 FWA Hwf WF2 K2) in H; [| lia| lia].
  pose proof (cb_of_u64arr bsegs _ _ _ TR) as TRC. rewrite LEN30 in TRC. cbn [Nat.mul] in TRC.
  survive FAM MUA WM2 FWA Hwf WF2 K2. survive OBJ MUA WM2 FWA Hwf WF2 K2. survive TRC MUA WM2 FWA Hwf WF2 K2.
  survive FJ1800 MUA WM2 FWA Hwf WF2 K2. survive FBP MUA WM2 FWA Hwf WF2 K2. survive FJ8 MUA WM2 FWA Hwf WF2 K2.
  survive FR5 MUA WM2 FWA Hwf WF2 K2. survive CL MUA WM2 FWA Hwf WF2 K2.
  destruct (u64arr_of_cb bsegs _ _ _ 30 TRC) as (ws2 & LEN2 & TR2).
  assert (RRB : 0 <= r < 2^64) by (clear -A1 A4 CEILB Hn2; lia).
  unfold A_ALLOC_RET. replace (ret_pc (Z_to_bv 64 0x329dc)) with (Z_to_bv 64 A_ALLOC_RET) by (symmetry; apply ret_pc_even; [ unfold A_ALLOC_RET; clear; lia | reflexivity ]).
  subst a0'.
  eapply (rzA_seg_cfg bsegs (aS E0 FSB0 HR0 sq) (aN E0 FSB0 HR0 sq) (aEB EB0 sq) (PP sq mo2)); [| exact KIP2|].
  { eapply (malloc_suf (PP sq mo2) gp (wz 0x5e1550) s6 s7 s8 s9 s10 s11 F fc usp lo n LOC ltac:(clear -LO; lia) SPH ltac:(clear -Hn2; lia) ltac:(rewrite unsigned_lit by (clear; lia); clear; cbn; lia) PSTK2 PDAT2
              ra s0 s1 s2 s3 s4 s5 _ _ _ _ _ _ _ _ _ _ s2w s3w s5w _ _ _ _ errw bpw m2 r ws2 (Z.of_nat (length tr)) j1800 j8);
      [ exact SK2 | exact MI2 | exact RRB | rewrite unsigned_lit by (clear; lia); exact ERR2
      | exact FAM | exact OBJ | exact TR2 | exact LEN2 | exact FJ1800 | exact FBP | exact FJ8 | exact FR5 | exact CL ]. }
  intros ms3 mo3 POST3 Hag3 KP3.
  destruct POST3 as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m3 & -> & MU3 & WM3 & MI3 & SK3 & ERR0 & ERR1).
  rewrite unsigned_lit in MU3, ERR0, ERR1 by (clear; lia).
  assert (AH3 : AHKc sq LB2 LF m3 mo3).
  { unfold BF_tkit.AHKc. eapply (AHK_magree SR RT E0 FSB0 HR0 L0 RES0 EB0 sq LB2 LF m3 mo2 mo3); [| exact Hag3| exact (proj1 (proj1 KP3))].
    eapply (AHK_frame_cl SR RT E0 FSB0 HR0 L0 RES0 EB0 PL0 ENV0 PL0OK (rt_fpc E0 FSB0 PL0) (rt_misc5_agree E0 FSB0 PL0) (rt_fpc_where E0 FSB0 PL0) so_fpc stdio_rep_agree so_fpc_where
              sq LB2 LF m2 m3 mo2 _ AH2 MU3 WM3).
    constructor; [left; cbn [fst]; clear -LO LOC; lia| constructor; [do 5 right; left; cbn; clear; lia| constructor]]. }
  (* [comment removed for export] *)
  pose proof (magree_frame _ _ Hag3) as (Qfds3 & Qvm3 & Qlz3 & Qfs3 & _).
  apply (CONT u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 m3 mo3 sq). unfold fin_facts.
  split; [exact SK3|]. split; [| split; [| split; [reflexivity| split; [| split; [| split; [| split; [cbn [aps_credit sq]; clear; lia|]]]]]]].
  - (* [comment removed for export] *)
    eapply aheap_pres_trans; [| eapply aheap_pres_trans].
    + eapply (aheap_pres_shell E0 FSB0 HR0 L0 RES0 EB0 PL0 _ _ _ _ _ _ _ _ AH0 MU1' WM1); [clear -LO LOC; lia|].
      constructor; [left; cbn; clear -LO LOC; lia| constructor].
    + eapply aheap_pres_sp_mono; [eapply (aw_client_pres_all E0 FSB0 HR0 L0 RES0 EB0 PL0 ENV0 PL0OK s LB LF m1 mo1 W m2 mo2 a' lo (usp + -2144) AH1 LOC ltac:(clear -LO; lia) MUA WM2 FWA FBA WF2 K2)| clear; lia].
    + assert (HP3 : aheap_pres bsegs ACONSTS LB2 LF usp m2 m3).
      { eapply (aheap_pres_shell E0 FSB0 HR0 L0 RES0 EB0 PL0 _ _ _ _ _ _ _ _ AH2 MU3 WM3); [clear -LO LOC; lia|].
        constructor; [left; cbn; clear -LO LOC; lia| constructor; [right; cbn; clear; lia| constructor]]. }
      intros z Hz HC. apply HP3; [exact Hz|]. subst LB2.
      destruct HC as [X|[X|X]]; [left; exact X| right; left| right; right; exact X]. destruct X as (bb & Hbb & Rb). exists bb. split; [right; exact Hbb| exact Rb].
  - eapply wmono_trans; [exact WM1| eapply wmono_trans; [exact WM2| exact WM3]].
  - (* [comment removed for export] *)
    split; [| split; [cbn [aps_credit sq]; clear; lia| repeat split; reflexivity]].
    destruct RUN as (fuel & orc & evs & orc' & RUN). exists (bst_key (Z.of_nat (length tr)) ws), fuel, orc, evs, orc'. cbn [aps_alloc sq]. unfold amalloc. exact RUN.
  - rewrite Qfs3, Ffs2, Qfs1. reflexivity.
  - rewrite Qfds3, Ffds2, Qfds1. reflexivity.
  - (* [comment removed for export] *)
    split; [reflexivity|]. split; [exact (conj A1 (conj A2 (conj A3 (conj A4 A5))))|]. split; [exact AH3|]. split.
    + destruct JUNK as [junk [LJ JC]]. exists junk. split; [exact LJ|]. eapply rw_cells_transport; [exact JC| exact MU3| exact WM3|].
      cbn [disjoint_from cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by (clear -Hn2; lia). cstat. clear -A4 A5 LO LOC Hn2 CEILB. repeat split; lia.
    + destruct BSH as (S1 & S2 & S3). split; [exact S1|]. split; [exact S2|].
      eapply u8arr_transport; [exact S3| exact MU3| exact WM3|].
      rewrite blk_shadow_length by (clear -Hn2; lia). cbn [disjoint_from]. try unfold B_base.A_SB.
      cstat. clear -A4 A5 LO LOC Hn2 CEILB. repeat split; Z.div_mod_to_equations; lia.
Qed.

(* [comment removed for export] *)
Theorem malloc_contract : amalloc_rz_stmt bsegs ACONSTS aps AHKc aps_so (amalloc_rel E0) aps_credit acharge (BF_unwind.uanchor bsegs).
Proof.
  unfold amalloc_rz_stmt. intros until K. intros KN AH SK LOC LO SPA SPH TP UA FRM A0 Hn2 CHG NBIG CONT. subst a0 tp. cbn [c_tp ACONSTS].
  eapply malloc_enter; [exact AH| exact SK| exact LOC| exact LO| exact SPA| exact SPH| exact UA| exact Hn2|].
  intros t0' t1' t2' a6' a7' s2w s3w s5w t3' t4' t5' t6' m1 mo1 ws tr bpw j1800 j8 MID.
  destruct (mid_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ AH CHG NBIG MID) as (TOK1 & AINV1 & ABUD & NBL).
  pose proof MID as (_ & _ & _ & _ & SK1 & OBJ & TR & LEN30 & LTR & _).
  pose proof (bv_unsigned_in_range 64 sp) as USPR. unfold bv_modulus in USPR. unfold AMALLOC_STACK in LO. pose proof alloc_ceiling_range as CEILB.
  eapply (ALLOC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 mo1 s n lo (bv_unsigned sp + -2128) (bv_unsigned sp + -2112) (Z.of_nat (length tr)) (aps_credit s) OPSLACK ws K);
    [ exact KN | exact TOK1 | clear -CHG; lia | unfold ASLACK, OPSLACK; clear; lia | exact AINV1 | exact ABUD | exact Hn2 | exact NBL
    | rewrite unsigned_lit by (clear -LO LOC USPR CEILB; lia); exact SK1 | exact LOC
    | rewrite unsigned_lit by (clear -LO LOC USPR CEILB; lia); unfold K_ALLOC; clear -LO; lia
    | rewrite unsigned_lit by (clear -LO LOC USPR CEILB; lia); clear -SPA; Z.div_mod_to_equations; lia
    | reflexivity
    | rewrite unsigned_lit by (clear -LO LOC USPR CEILB; lia); clear; lia
    | clear; lia
    | unfold zlen; rewrite LEN30; clear -SPH LO LOC CEILB; lia
    | exact OBJ | exact TR
    | unfold zlen; rewrite LEN30; clear -LTR; lia
    | unfold zlen; rewrite LEN30; clear; lia | ].
  cbv beta. intros t0'' t1'' t2'' a0' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' m2 mo2 a' r POST2.
  eapply malloc_leave; [exact AH| exact LOC| exact LO| exact SPH| exact Hn2| exact CHG| exact FRM| exact MID| exact POST2|].
  intros u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 m3 mo3 s' (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13).
  eapply (CONT u0 u1 u2 a0' v1 v2 v3 v4 v5 v6 v7 u3 u4 u5 u6 F fc m3 mo3 s' r); assumption.
Qed.
End MallocT2.
End RC__1.
