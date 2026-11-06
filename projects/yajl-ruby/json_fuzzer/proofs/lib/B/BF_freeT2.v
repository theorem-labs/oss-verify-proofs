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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import StdioBase Malloc STree.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanConsts AsanSizeClass AsanState AsanLayout AsanOps AsanFakeStack AsanPS AsanRep AsanKern AsanClient AsanBudget AsanBudget2 AsanRepFrame AsanDepot AsanGap AsanSlack AsanWf1 AsanRealloc.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import B_base B_alloc_iface B_iface BF_fakestack_rep BF_place BF_unwind BF_unwind_walk2 BF_kit BF_kit3 BF_free_kit BF_ia BF_free0 BF_free1d BF_realloc1 BF_realloc2 BF_reallocG BM_memcpy BX_unreg BX_Exit BF_statics B_live B_policy5 B_budget5 B_slack5 B_bundle B_benv5 B_init5 B_instD5 B_balloc5 B_bpolicy5 B_rtok5 B_bframe B_bframe2 BF_tkit BF_alloc_iface BF_free_iface BF_glue_kit BF_mallocT2 BF_caT BF_shell_rep5 BF_reallocT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
#[warnings="-notation-for-abbreviation"] Notation mem := (word -> option byte).
#[warnings="-notation-for-abbreviation"] Notation wz := (fun z : Z => Z_to_bv 64 z).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import LiaA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac lia ::= LiaA.liaA.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.

(* [comment removed for export] *)
Lemma ab_remove_id : forall A LB, (forall b, In b LB -> ab_addr b <> A) -> ab_remove A LB = LB.
Proof.
  intros A LB. induction LB as [|x LB IH]; intros H; [reflexivity|]. cbn [ab_remove].
  destruct (Z.eqb_spec (ab_addr x) A) as [E|NE]; [exfalso; exact (H x (or_introl eq_refl) E)|].
  f_equal. apply IH. intros b Hb. apply H. right. exact Hb.
Qed.
Lemma ab_find_none : forall A LB, (forall b, In b LB -> ab_addr b <> A) -> ab_find A LB = None.
Proof.
  intros A LB H. unfold ab_find. induction LB as [|x LB IH]; [reflexivity|]. cbn [List.find].
  destruct (Z.eqb_spec (ab_addr x) A) as [E|NE]; [exfalso; exact (H x (or_introl eq_refl) E)|]. apply IH. intros b Hb. apply H. right. exact Hb.
Qed.

(* [comment removed for export] *)
Section FreeT2.
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
Hypothesis DEALLOC : dealloc_srz_stmt E0 FSB0 HR0 L0 RES0 EB0 PL0.

#[local] Notation AHKc := (BF_tkit.AHKc E0 FSB0 HR0 L0 RES0 EB0 PL0).
#[local] Notation SR := stdio_rep.
#[local] Notation RT := (rt_misc5 FSB0 PL0).
#[local] Notation rt_fpE := (fun E a => rt_fpc E FSB0 PL0 a).
#[local] Notation DR := (DepotR bsegs E0).
Ltac cstat := try clear DEALLOC; try clear HS_tot; try clear ENV_depot; try clear EB0_ok; try clear HR0_ok; try clear PL0OK; try clear ENV0.

Definition PP (s : aps) (mo : Model) : acc -> Prop := fun x => acc_ok (m_vm_lazy mo) (aS E0 FSB0 HR0 s) x.
Lemma EPOL : forall s mo a k, POL E0 FSB0 HR0 s mo a k = PP s mo (Z_to_bv 64 a, k). Proof. intros; reflexivity. Qed.

(* [comment removed for export] *)
Lemma afree_run_some : forall key p a f orc a' evs orc', p <> 0 ->
  arun f (afree_core E0 key p (ia0 a)) orc = Some (a', ONorm tt, evs, orc') ->
  exists f', arun f' (afree E0 key p a) orc = Some (a', ONorm tt, evs, orc').
Proof.
  intros key p a f orc a' evs orc' Hp H. exists (0 + f)%nat. unfold afree, ia_init.
  replace (p =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hp).
  replace evs with ([] ++ evs) by reflexivity. eapply arun_abind; [apply arun_aupd| exact H].
Qed.
Lemma afree_run_null : forall key a orc, exists f', arun f' (afree E0 key 0 a) orc = Some (ia0 a, ONorm tt, [], orc).
Proof.
  intros key a orc. exists (0 + 0)%nat. unfold afree, ia_init. rewrite Z.eqb_refl.
  change (@nil aev) with (@nil aev ++ @nil aev). eapply arun_abind; [apply arun_aupd| apply arun_aret].
Qed.

(* [comment removed for export] *)
Definition fpre_post (gp tp t2 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (usp lo p : Z) (izl : list byte)
    (TSD CTX T top bot : Z) (ra s0 s1 s2 s3 s4 s5 : word) (m : mem) (ms : machine_state) : Prop :=
  exists (t0 t1 a6 a7 s3w : word) (m2 : mem) (ws tr : list word) (bpw : word) (j1800 j8 : list byte),
    ms = MS (mkR (Z_to_bv 64 0x54058) (Z_to_bv 64 (usp + -2128)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 p)
                 (Z_to_bv 64 A_INST) (Z_to_bv 64 p) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (usp + -2128)) (Z_to_bv 64 1) a6 a7
                 (Z_to_bv 64 0x53fe8) s3w (Z_to_bv 64 (usp + -2128)) (Z_to_bv 64 (usp + -81)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 A_DEALLOCATE) fc None m2 (seg_rom bsegs)
    /\ mem_inv bsegs m2 /\ stk bsegs m2 lo (usp + -2128) /\ wmono bsegs m m2
    /\ munch (preW0 usp lo T) m m2
    /\ rw_cells bsegs m2 0x13e048 [C1 (Z_to_bv 8 1); C1 zb0]
    /\ rw_cells bsegs m2 (IA + 0x40dc0) [C8 (Z_to_bv 64 4096); C8 (Z_to_bv 64 (IA + 0x40dd0))]
    /\ u8arr bsegs m2 (IA + 8) izl /\ wr_at bsegs m2 IA 0x81030
    /\ uthread_cells m2 tp TSD CTX T top bot
    /\ rw_cells bsegs m2 (usp + -2128) [C8 (Z_to_bv 64 (usp + -2112)); C4 (Z_to_bv 64 (Z.of_nat (length tr))); C4 (Z_to_bv 64 0)]
    /\ u64arr bsegs m2 (usp + -2112) ws /\ length ws = 30%nat /\ firstn (length tr) ws = tr /\ (1 <= length tr <= 30)%nat
    /\ rw_cells bsegs m2 (usp + -56) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells bsegs m2 (usp + -1872) [CB 1800 j1800] /\ rw_cells bsegs m2 (usp + -72) [C8 bpw] /\ rw_cells bsegs m2 (usp + -64) [CB 8 j8].

Section FP.
Variable P : acc -> Prop.
Variables (gp tp t2 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (usp lo p : Z) (ii : bool) (izl : list byte) (TSD CTX T top bot : Z).
Hypothesis LOC : alloc_ceiling <= lo.
Hypothesis LO : lo <= usp - 8192.
Hypothesis SPH : usp < 2^47.
Hypothesis SPA : usp mod 16 = 0.
Hypothesis HTB : 0 <= bot < top /\ top <= 2^47.
Hypothesis Hp : 0 < p < 2^47.
Hypothesis EZ : izl = repeat zb0 (Z.to_nat 0x40000).
Hypothesis HTSD : 0x5d0810 <= TSD /\ TSD + 8 <= 0x603000.
Hypothesis HCTX : 0x603000 <= CTX /\ CTX + 4096 <= alloc_ceiling.
Hypothesis HT : (0x1000 <= T /\ (T + 4096 <= 0x10000 \/ 0x603000 <= T)) /\ T + 4096 <= alloc_ceiling.
Hypothesis HTC : CTX + 160 <= T \/ T + 4096 <= CTX.
Hypothesis HTP : 0x5d0810 + 88 <= bv_unsigned tp /\ bv_unsigned tp + 60 <= 0x603000.
Hypothesis PSTK : forall a k, lo <= a -> a + Z.of_nat k <= 2^64 -> P (Z_to_bv 64 a, k).
Hypothesis PDAT : forall a k, 0xa5000 <= a -> a + Z.of_nat k <= 0x603000 -> P (Z_to_bv 64 a, k).
Hypothesis PCTX : P (Z_to_bv 64 (CTX + 152), 8%nat).
Hypothesis PT : forall a k, T <= a -> a + Z.of_nat k <= T + 4096 -> P (Z_to_bv 64 a, k).

Lemma free_pre : forall (ra s0 s1 s2 s3 s4 s5 t0 t1 a1 a2 a3 a4 a5 a6 a7 : word) (m : mem),
  stk bsegs m lo usp -> mem_inv bsegs m ->
  rw_cells bsegs m 0xaf298 [C1 (Z_to_bv 8 1)] ->
  rw_cells bsegs m 0xa5580 [C8 (Z_to_bv 64 0x13e060)] -> rw_cells bsegs m 0x13e060 [C8 (Z_to_bv 64 4096)] ->
  rw_cells bsegs m 0xaf2bc [C4 (Z_to_bv 64 30)] ->
  rw_cells bsegs m 0xa5590 [C8 (Z_to_bv 64 0x1400e8)] ->
  rw_cells bsegs m 0x14010a [C1 (Z_to_bv 8 1)] ->
  rw_cells bsegs m 0x13e048 [C1 (Z_to_bv 8 (boolz ii)); C1 zb0] ->
  wr_at bsegs m IA 0x81030 -> u8arr bsegs m (IA + 8) izl ->
  (ii = true -> rw_cells bsegs m (IA + 0x40dc0) [C8 (Z_to_bv 64 4096); C8 (Z_to_bv 64 (IA + 0x40dd0))]) ->
  uthread_cells m tp TSD CTX T top bot ->
  uanchor bsegs m usp ra s0 ->
  evtA bsegs P (fpre_post gp tp t2 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc usp lo p izl TSD CTX T top bot ra s0 s1 s2 s3 s4 s5 m)
    (MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x53eb0) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros SK MI AI G1 G2 MCS GCF FUM IAF IWR IZ IPV UT UA.
  pose proof LOC as LOCu. aceil.
  pose proof HT as [[HTa _] HTb]. pose proof HCTX as [HCa HCb]. aceil.
  eapply (free_pro P) with (lo := lo) (ii := ii) (izl := izl) (TSD := TSD) (CTX := CTX) (T := T) (top := top) (bot := bot);
    [exact SK| exact LOC| lia| exact SPH| lia| lia| exact UA| exact MI| lia| exact AI| exact G1| exact G2| exact MCS| exact GCF| exact FUM| exact IAF| exact IWR| exact IZ
    | exact EZ| exact IPV| exact UT| lia| lia| lia| exact (proj2 HCTX)| exact (proj1 HT)| exact (proj2 HT)| exact HTC| lia| exact PSTK| exact PDAT| exact PCTX| exact PT|].
  intros m1 t0' t1' a3' a4' a5' a6' a7' s3' ws tr j1800 j8 bpw MI1 SK1 WM1 MU1 IAF1 PSC1 IZ1 IWR1 UT1 OBJ ARR LEN FTR LTR FR7 FJ1800 FBP FJ8.
  do 9 zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  apply evtA_done. unfold fpre_post.
  exists t0', t1', a6', a7', s3', m1, ws, tr, bpw, j1800, j8.
  split; [reflexivity|]. split; [exact MI1|]. split; [exact SK1|]. split; [exact WM1|]. split; [unfold preW0; exact MU1|].
  split; [exact IAF1|]. split; [exact PSC1|]. split; [exact IZ1|]. split; [exact IWR1|]. split; [exact UT1|].
  split; [exact OBJ|]. split; [exact ARR|]. split; [exact LEN|]. split; [exact FTR|]. split; [exact LTR|].
  split; [exact FR7|]. split; [exact FJ1800|]. split; [exact FBP| exact FJ8].
Qed.
End FP.

Theorem free_contract : afree_rz_stmt bsegs ACONSTS aps AHKc aps_so (afree_rel E0) aps_credit arefund (BF_unwind.uanchor bsegs).
Proof.
  unfold afree_rz_stmt. intros until K. intros KN AH HA SK LOC LO SPA SPH TP UA FRM A0 CF NBIG CONT. subst a0 tp. cbn [c_tp ACONSTS].
  unfold KLink.wz. cbn [c_wrap_free ACONSTS].
  destruct (shell_facts_of E0 FSB0 HR0 L0 RES0 EB0 PL0 ENV0 PL0OK _ _ _ _ _ AH) as (Gai & Gmcs & GCF & Gfu & GPSC & Gps & TC & HCTX & HT & HTC & HTB & (c0 & cl & RRC & CLO & CHI)).
  destruct (shell_facts2_of E0 FSB0 HR0 L0 RES0 EB0 PL0 ENV0 _ _ _ _ _ AH) as (Gia & Gipv & Giz & Giwr & STATS & _ & _).
  pose proof AH as AH0. unfold BF_tkit.AHKc in AH. ahk_open AH.
  destruct (AHK_env _ _ _ _ _ _ _ _ _ _ _ _ _ AH0) as [EE EFS]. pose proof Henv as ENVOK0. rewrite EE in *.
  destruct Hkm as (Khalt & Kminv & Klim).
  pose proof (bv_unsigned_in_range 64 sp) as USPR. unfold bv_modulus in USPR. unfold AMALLOC_STACK in LO. pose proof alloc_ceiling_range as CEILB.
  remember (bv_unsigned sp) as usp eqn:Husp in *.
  assert (Esp : sp = wz usp) by (rewrite Husp; symmetry; apply Z_to_bv_bv_unsigned). rewrite Esp in CONT |- *. clear Esp Husp.
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
  assert (HTSD' : 0x5d0810 <= 0x6028f8 /\ 0x6028f8 + 8 <= 0x603000) by (clear; lia).
  assert (HTP' : 0x5d0810 + 88 <= bv_unsigned (wz 0x5e1550) /\ bv_unsigned (wz 0x5e1550) + 60 <= 0x603000) by (rewrite unsigned_lit by (clear; lia); clear; lia).
  (* [comment removed for export] *)
  set (ts := as_ts (aps_alloc s)) in *. set (ast1 := shell_st true ts (aps_alloc s)).
  pose proof (model_shell_st E0 true ts (aps_alloc s)) as (MW & MR & MQ & MD & MB & MLB & MNP & MND & MRES & MIA & MTS & MSS & MCS).
  fold ast1 in MW, MR, MQ, MD, MB, MLB, MNP, MND, MRES, MIA, MTS, MSS, MCS.
  pose proof (blocks_sep_of E0 (aps_alloc s) mo ENV0 Hwf Hkern) as BS0.
  destruct Henv as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & IMGE). rewrite EE in IMGE.
  assert (FWpre : Forall (shell_iv E0 lo) (preW0 usp lo (ae_thread E0))).
  { unfold preW0, shell_iv. repeat apply Forall_cons; cbn [fst snd]; [left; clear; lia| right; left; unfold BF_shell_rep5.IA; clear; lia| right; right; left; clear; lia
      | do 4 right; clear; lia| apply Forall_nil]. }
  pose proof Hbud as (BU0 & BU1 & BU2 & BU3).
  pose proof (RTOK_open SR RT E0 FSB0 HR0 L0 RES0 EB0 HR0_ok EB0_ok ENV_depot HS_tot s LB LF m mo AH0 NBIG) as TOK0.
  destruct HA as [A00 | (bA & HbA & EbA)].
  - (* [comment removed for export] *)
    subst A.
    eapply (rzA_seg_cfg bsegs (aS E0 FSB0 HR0 s) (aN E0 FSB0 HR0 s) (aEB EB0 s) (PP s mo)
              (fun ms => exists (m' : mem) (t0' t1' a0' a1' a2' a3' a4' a5' a6' a7' : word),
                 ms = MS (mkR ra (wz usp) gp (wz 0x5e1550) t0' t1' t2 s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom bsegs)
                 /\ mem_inv bsegs m' /\ stk bsegs m' lo usp /\ wmono bsegs m m' /\ munch (preW0 usp lo (ae_thread E0)) m m'
                 /\ rw_cells bsegs m' 0x13e048 [C1 (Z_to_bv 8 1); C1 zb0]
                 /\ rw_cells bsegs m' (IA + 0x40dc0) [C8 (wz 4096); C8 (wz (IA + 0x40dd0))]
                 /\ u8arr bsegs m' (IA + 8) (zeros (Z.to_nat 0x40000)) /\ uthread_cells m' (wz 0x5e1550) 0x6028f8 (fp_ctx PL0) (ae_thread E0) (ae_stack_top E0) (ae_stack_bottom E0)));
      [| exact KIP0|].
    { stepA.
      lazymatch goal with |- evtA _ _ _ (MS ?r ?f ?pc ?x1 ?x2 ?x3 ?x4) => let v := eval vm_compute in (bv_unsigned pc) in change pc with (Z_to_bv 64 v) end.
      eapply (free_null_walk (PP s mo)) with (lo := lo) (ii := as_ia_inited (aps_alloc s)) (izl := zeros (Z.to_nat 0x40000)) (TSD := 0x6028f8) (CTX := fp_ctx PL0) (T := ae_thread E0)
               (top := ae_stack_top E0) (bot := ae_stack_bottom E0);
        [exact SK| exact LOC| clear -LO; lia| exact SPH| clear -HTB; lia| clear -HTB; lia| exact SPA| exact UA| exact Hmi| clear; lia| exact Gai| exact GPSC| exact Gps| exact Gmcs| exact GCF| exact Gfu| exact Gia
        | exact Giwr| exact Giz| unfold zeros; reflexivity| unfold IA in Gipv; exact Gipv| exact TC| clear; lia| clear; lia| exact (proj1 HCTX)| exact (proj2 HCTX)| exact (proj1 HT)| exact (proj2 HT)| exact HTC| rewrite unsigned_lit by (clear; lia); clear; lia
        | exact PSTK| exact PDAT| exact PCTX| exact PTHR| reflexivity|].
      intros m' t0' t1' a0' a1' a2' a3' a4' a5' a6' a7' MI' SK' WM' MU' IAF' PSC' IZ' IWR' UT'.
      apply evtA_done. exists m', t0', t1', a0', a1', a2', a3', a4', a5', a6', a7'. split; [reflexivity|].
      exact (conj MI' (conj SK' (conj WM' (conj MU' (conj IAF' (conj PSC' (conj IZ' UT'))))))). }
    cbv beta. intros ms2 mo1 (m2 & t0' & t1' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & -> & MI2 & SK2 & WM1 & MU1 & IAF2 & IPV2 & IZ2 & TU2) Hag1 KP1.
    (* [comment removed for export] *)
    pose proof (magree_frame _ _ Hag1) as (Qfds1 & Qvm1 & Qlz1 & Qfs1 & Qh1 & _).
    assert (K1 : AKern E0 ast1 mo1) by (apply AKern_shell_st; eapply AKern_frame; [exact Qvm1| exact Qlz1| exact Hkern]).
    pose proof TU2 as (TC2 & T40b & T8b & TUNW2).
    assert (ST2 : rw_cells bsegs m2 (ae_thread E0 + 2856) [C8 (wz (ts_reallocs ts)); C8 (wz (ts_realloced ts))]).
    { eapply rw_cells_transport; [exact STATS| exact MU1| exact WM1| unfold preW0, BF_shell_rep5.IA; cbn; clear -HT LOC CEILB; lia]. }
    assert (REP1 : ARep bsegs E0 DR ast1 m2).
    { subst ast1. eapply (ARep_shell E0 PL0 ENV0 PL0OK IMGE (aps_alloc s) m m2 mo (preW0 usp lo (ae_thread E0)) lo true ts);
        [exact Hrep| exact Hwf| exact Hkern| exact BS0| exact WM1| exact MU1| exact LOC| exact FWpre| exact IAF2| intros _; exact IPV2| exact IZ2
        | apply ts_agree78_refl| exact ST2| exact TUNW2]. }
    pose proof (RTOK_magree E0 FSB0 HR0 L0 RES0 EB0 _ _ _ _ _ TOK0 Hag1 (proj1 KP1)) as TOK0'. rewrite <- (sA_self s) in TOK0'.
    pose proof (RTOK_same_fp E0 FSB0 HR0 L0 RES0 EB0 _ _ s (aps_alloc s) ast1 mo1 TOK0' (same_fp_shell_st true ts (aps_alloc s)) MNP MND) as TOK1.
    destruct (RTOK_ATOK E0 FSB0 HR0 L0 RES0 EB0 _ _ _ _ TOK1) as (R1 & R1' & ATOK1 & _ & _).
    assert (AH1 : AHKc (sA ast1 s) LB LF m2 mo1).
    { unfold BF_tkit.AHKc.
      eapply (AHK_close SR RT E0 FSB0 HR0 L0 RES0 EB0 PL0 ENV0 PL0OK rt_fpE (rt_misc5_agree E0 FSB0 PL0) (rt_fpc_where2 E0 FSB0 PL0) so_fpc stdio_rep_agree so_fpc_where2
                s (sA ast1 s) LB LF m mo ast1 m2 mo1 LB (preW0 usp lo (ae_thread E0)) lo usp R1 R1' AH0);
        [reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| exact REP1| exact (MW Hwf)| exact K1| exact (MR Hres)| exact (MQ Hqb)| exact (MD Hdi)| exact (MB Hbinv)| exact (MSS Hss)| exact (MCS Hcs)
        | unfold blocks_match; rewrite MLB; exact Hbm| exact ATOK1| exact MI2| exact MU1| apply aw_ok_preW0| exact LOC
        | cbn [aps_credit sA aps_set_alloc]; exact BU0| rewrite MNP; exact BU1| rewrite MND; exact BU2| ].
      cbn [aps_credit aps_alloc sA aps_set_alloc]. rewrite MNP, MND, MRES. clear. lia. }
    (* [comment removed for export] *)
    destruct (AHK_blocks _ _ _ _ _ _ _ _ s LB LF m mo AH0) as (BR & _ & NDLB).
    assert (NZ : forall b, In b LB -> ab_addr b <> 0) by (intros b Hb; destruct (BR b Hb) as (B1 & _); clear -B1; lia).
    rewrite (ab_remove_id 0 LB NZ) in CONT. unfold arefund_at in CONT. rewrite (ab_find_none 0 LB NZ) in CONT.
    apply (CONT t0' t1' t2 a0' a1' a2' a3' a4' a5' a6' a7' t3 t4 t5 t6 F fc m2 mo1 (sA ast1 s)); [exact SK2| | exact FRM| reflexivity| exact AH1| | | | cbn [aps_credit sA aps_set_alloc afree_cost Z.eqb]; clear; lia].
    + eapply (aw_client_pres E0 FSB0 HR0 L0 RES0 EB0 PL0 ENV0 PL0OK s LB LF m mo ast1 mo1 m2 (preW0 usp lo (ae_thread E0)) lo usp LB AH0 (MW Hwf) K1 MU1 WM1);
        [apply aw_ok_preW0| exact LOC| clear -LO; lia|].
      intros b Hb. split; [exact Hb|]. pose proof (blocks_match_In _ _ _ Hbm Hb) as HbL.
      pose proof (live_block_off_thread E0 (aps_alloc s) _ _ Hwf HbL) as [B1 B2].
      pose proof (live_block_placed E0 FSB0 HR0 L0 RES0 EB0 PL0 s LB LF m mo _ _ AH0 HbL) as (B3 & _).
      unfold preW0, BF_shell_rep5.IA. repeat apply Forall_cons; cbn [fst snd];
        [clear -B1 LOC; lia| clear -B3; lia| clear -B3; lia| clear -B2; lia| apply Forall_nil].
    + split; [| split; [cbn [aps_credit sA aps_set_alloc]; clear; lia| repeat split; reflexivity]].
      destruct (afree_run_null (bst_key 1 []) (aps_alloc s) []) as [f' RUN']. cbn [aps_alloc sA aps_set_alloc].
      exists (bst_key 1 []), f', [], [], []. subst ast1 ts. rewrite shell_st_ia0. exact RUN'.
    + exact Qfs1.
    + exact Qfds1.
  - (* [comment removed for export] *)
    destruct bA as [bAa sz]. cbn [ab_addr] in EbA. subst bAa. rename HbA into HLB.
    assert (HLIVE : In (A, sz) (live_blocks (aps_alloc s))) by (exact (blocks_match_In LB (aps_alloc s) (mkABlock A sz) Hbm HLB)).
    pose proof (live_block_placed E0 FSB0 HR0 L0 RES0 EB0 PL0 s LB LF m mo A sz AH0 HLIVE) as (GA1 & GA2 & GA3 & GA4 & GA5).
    pose proof (live_block_off_thread E0 (aps_alloc s) _ _ Hwf HLIVE) as [_ GAT].
    assert (HA' : 0 < A < 2^47) by (clear -GA1 GA2 GA4 CEILB; lia).
    assert (CF1 : 1 <= aps_credit s) by (unfold afree_cost in CF; replace (A =? 0) with false in CF by (symmetry; apply Z.eqb_neq; clear -GA1; lia); exact CF).
    (* [comment removed for export] *)
    eapply (rzA_seg_cfg bsegs (aS E0 FSB0 HR0 s) (aN E0 FSB0 HR0 s) (aEB EB0 s) (PP s mo)); [| exact KIP0|].
    { stepA.
      lazymatch goal with |- evtA _ _ _ (MS ?r ?f ?pc ?x1 ?x2 ?x3 ?x4) => let v := eval vm_compute in (bv_unsigned pc) in change pc with (Z_to_bv 64 v) end.
      eapply (free_pre (PP s mo) gp (wz 0x5e1550) t2 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc usp lo A (as_ia_inited (aps_alloc s)) (zeros (Z.to_nat 0x40000)) 0x6028f8 (fp_ctx PL0) (ae_thread E0) (ae_stack_top E0) (ae_stack_bottom E0)
                LOC ltac:(clear -LO; lia) SPH HTB HA' ltac:(unfold zeros; reflexivity) HTSD' HCTX HT HTC HTP' PSTK PDAT PCTX PTHR);
        [ exact SK| exact Hmi| exact Gai| exact GPSC| exact Gps| exact Gmcs| exact GCF| exact Gfu| exact Gia
        | exact Giwr| exact Giz| unfold IA in Gipv; exact Gipv| exact TC| exact UA ]. }
    intros ms2 mo1 POST1 Hag1 KP1.
    destruct POST1 as (t0' & t1' & a6' & a7' & s3w & m2 & ws & tr & bpw & j1800 & j8 & -> & MI2 & SK2 & WM1 & MU1 & IAF2 & IPV2 & IZ2 & IWR2 & TU2 & OBJ & ARR & LEN30 & FTR & LTR & FR7 & FJ1800 & FBP & FJ8).
    (* [comment removed for export] *)
    pose proof (magree_frame _ _ Hag1) as (Qfds1 & Qvm1 & Qlz1 & Qfs1 & Qh1 & _).
    assert (K1 : AKern E0 ast1 mo1) by (apply AKern_shell_st; eapply AKern_frame; [exact Qvm1| exact Qlz1| exact Hkern]).
    pose proof TU2 as (TC2 & T40b & T8b & TUNW2).
    assert (ST2 : rw_cells bsegs m2 (ae_thread E0 + 2856) [C8 (wz (ts_reallocs ts)); C8 (wz (ts_realloced ts))]).
    { eapply rw_cells_transport; [exact STATS| exact MU1| exact WM1| unfold preW0, BF_shell_rep5.IA; cbn; clear -HT LOC CEILB; lia]. }
    assert (REP1 : ARep bsegs E0 DR ast1 m2).
    { subst ast1. eapply (ARep_shell E0 PL0 ENV0 PL0OK IMGE (aps_alloc s) m m2 mo (preW0 usp lo (ae_thread E0)) lo true ts);
        [exact Hrep| exact Hwf| exact Hkern| exact BS0| exact WM1| exact MU1| exact LOC| exact FWpre| exact IAF2| intros _; exact IPV2| exact IZ2
        | apply ts_agree78_refl| exact ST2| exact TUNW2]. }
    pose proof (RTOK_magree E0 FSB0 HR0 L0 RES0 EB0 _ _ _ _ _ TOK0 Hag1 (proj1 KP1)) as TOK0'. rewrite <- (sA_self s) in TOK0'.
    pose proof (RTOK_same_fp E0 FSB0 HR0 L0 RES0 EB0 _ _ s (aps_alloc s) ast1 mo1 TOK0' (same_fp_shell_st true ts (aps_alloc s)) MNP MND) as TOK1.
    destruct (RTOK_ATOK E0 FSB0 HR0 L0 RES0 EB0 _ _ _ _ TOK1) as (R1 & R1' & ATOK1 & _ & _).
    assert (AH1 : AHKc (sA ast1 s) LB LF m2 mo1).
    { unfold BF_tkit.AHKc.
      eapply (AHK_close SR RT E0 FSB0 HR0 L0 RES0 EB0 PL0 ENV0 PL0OK rt_fpE (rt_misc5_agree E0 FSB0 PL0) (rt_fpc_where2 E0 FSB0 PL0) so_fpc stdio_rep_agree so_fpc_where2
                s (sA ast1 s) LB LF m mo ast1 m2 mo1 LB (preW0 usp lo (ae_thread E0)) lo usp R1 R1' AH0);
        [reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| exact REP1| exact (MW Hwf)| exact K1| exact (MR Hres)| exact (MQ Hqb)| exact (MD Hdi)| exact (MB Hbinv)| exact (MSS Hss)| exact (MCS Hcs)
        | unfold blocks_match; rewrite MLB; exact Hbm| exact ATOK1| exact MI2| exact MU1| apply aw_ok_preW0| exact LOC
        | cbn [aps_credit sA aps_set_alloc]; exact BU0| rewrite MNP; exact BU1| rewrite MND; exact BU2| ].
      cbn [aps_credit aps_alloc sA aps_set_alloc]. rewrite MNP, MND, MRES. clear. lia. }
    assert (HP1 : aheap_pres bsegs ACONSTS LB LF usp m m2).
    { eapply (aw_client_pres E0 FSB0 HR0 L0 RES0 EB0 PL0 ENV0 PL0OK s LB LF m mo ast1 mo1 m2 (preW0 usp lo (ae_thread E0)) lo usp LB AH0 (MW Hwf) K1 MU1 WM1);
        [apply aw_ok_preW0| exact LOC| clear -LO; lia|].
      intros b Hb. split; [exact Hb|]. pose proof (blocks_match_In _ _ _ Hbm Hb) as HbL.
      pose proof (live_block_off_thread E0 (aps_alloc s) _ _ Hwf HbL) as [B1 B2].
      pose proof (live_block_placed E0 FSB0 HR0 L0 RES0 EB0 PL0 s LB LF m mo _ _ AH0 HbL) as (B3 & _).
      unfold preW0, BF_shell_rep5.IA. repeat apply Forall_cons; cbn [fst snd];
        [clear -B1 LOC; lia| clear -B3; lia| clear -B3; lia| clear -B2; lia| apply Forall_nil]. }
    (* [comment removed for export] *)
    pose proof (RTOK_open SR RT E0 FSB0 HR0 L0 RES0 EB0 HR0_ok EB0_ok ENV_depot HS_tot (sA ast1 s) LB LF m2 mo1 AH1 NBIG) as TOKA.
    cbn [aps_credit sA aps_set_alloc] in TOKA.
    pose proof AH1 as AH1c. unfold BF_tkit.AHKc in AH1c.
    destruct AH1c as (Hrep1 & Hwf1 & Hkern1 & _ & Hres1 & Hqb1 & Hdi1 & Hbinv1 & Hbm1 & _ & _ & _ & _ & Hrt1 & _ & _ & _ & Hbud1 & Hmi1 & Henv1 & _ & Hss1 & Hcs1).
    cbn [aps_alloc aps_env aps_fsbase sA aps_set_alloc] in Hrep1, Hwf1, Hkern1, Hres1, Hqb1, Hdi1, Hbinv1, Hbm1, Hrt1, Hbud1, Henv1, Hss1, Hcs1. rewrite EE in *.
    assert (AINV1 : AINV E0 FSB0 PL0 ast1 m2 mo1).
    { split; [exact Hrep1|]. split; [exact Hwf1|]. split; [exact Hkern1|]. split; [exact Hres1|]. split; [exact Hqb1|]. split; [exact Hdi1|]. split; [exact Hbinv1|]. split; [exact MI2| split; [exact Hrt1| split; [exact Hss1| exact Hcs1]]]. }
    assert (FBUD : fbudget_pre ast1).
    { unfold fbudget_pre. rewrite MNP, MND. unfold ACC in BU3.
      pose proof (DEP_nonneg LB) as DEPnn. pose proof (AsanBudget2.zlen_nonneg (as_residue (aps_alloc s))) as ZR. cstat. clear -BU0 BU1 BU2 BU3 DEPnn ZR CF1. unset_all. lia. }
    assert (HLIVE1 : In (A, sz) (live_blocks ast1)) by (rewrite MLB; exact HLIVE).
    assert (OBJ2 : rw_cells bsegs m2 (usp + -2128) [C8 (wz (usp + -2112)); C8 (wz (Z.of_nat (length tr)))]) by (apply obj_c8; [clear -LTR; lia| exact OBJ]).
    (* [comment removed for export] *)
    eapply (DEALLOC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m2 mo1 (sA ast1 s) A sz lo (usp + -2128) (usp + -2112) (Z.of_nat (length tr)) (aps_credit s) OPSLACK ws K);
      [ exact KN | exact TOKA | exact CF1 | unfold OPSLACK, FSLACK; clear; lia | exact AINV1 | exact FBUD | exact HLIVE1
      | rewrite unsigned_lit by (clear -LO LOC USPR CEILB; lia); exact SK2 | exact LOC
      | rewrite unsigned_lit by (clear -LO LOC USPR CEILB; lia); unfold K_FREE; clear -LO; lia
      | rewrite unsigned_lit by (clear -LO LOC USPR CEILB; lia); clear -SPA; Z.div_mod_to_equations; lia
      | reflexivity
      | rewrite unsigned_lit by (clear -LO LOC USPR CEILB; lia); clear; lia
      | clear; lia
      | unfold zlen; rewrite LEN30; clear -SPH LO LOC CEILB; lia
      | exact OBJ2 | exact ARR
      | unfold zlen; rewrite LEN30; clear -LTR; lia
      | unfold zlen; rewrite LEN30; clear; lia | ].
    cbv beta. intros w0 w1 w2 b0 b1 b2 b3 b4 b5 b6 b7 w3 w4 w5 w6 m5 mo4 aa3 POST6.
    destruct POST6 as (SK5 & (W5 & MUD & FWD & FBD) & RUN2 & AINV5 & TOK5 & Ffs5 & Ffds5 & Ftid5 & FACCT & PERM2).
    rewrite unsigned_lit in SK5, FWD by (clear -LO LOC USPR CEILB; lia).
    cbn [aps_alloc sA aps_set_alloc] in FWD, FBD, RUN2, FACCT, PERM2, TOK5.
    pose proof AINV5 as (Hrep5 & WF5 & K5 & RO5 & QB5 & DI5 & BI5 & MI5 & Hrt5 & SS5 & CS5).
    (* [comment removed for export] *)
    destruct (AHK_blocks _ _ _ _ _ _ _ _ s LB LF m mo AH0) as (_ & _ & NDLB).
    destruct (ab_remove_split A sz LB NDLB HLB) as [DEPR PERMR].
    set (LB3 := ab_remove A LB).
    set (sr := mkAPS (aps_env s) aa3 (aps_fs s) (aps_fsbase s) (aps_so s) (aps_errno s) (aps_initialized s) (aps_credit s - 1 + arefund sz)).
    destruct (RTOK_ATOK E0 FSB0 HR0 L0 RES0 EB0 _ _ _ _ TOK5) as (R4 & R4' & ATOK4 & _ & _).
    assert (BM3 : blocks_match LB3 aa3).
    { unfold blocks_match. subst LB3. apply Permutation_cons_inv with (a := (A, sz)).
      etransitivity; [apply Permutation_sym; exact PERMR|]. etransitivity; [| exact PERM2]. rewrite MLB. exact Hbm. }
    pose proof Hbud1 as (BW0 & BW1 & BW2 & BW3). cbn [aps_credit aps_alloc sA aps_set_alloc] in BW0, BW1, BW2, BW3.
    pose proof FACCT as (FA1 & FA2 & FA3). pose proof (arefund_nonneg sz) as RFN.
    assert (AH4 : AHKc sr LB3 LF m5 mo4).
    { unfold BF_tkit.AHKc.
      eapply (AHK_close SR RT E0 FSB0 HR0 L0 RES0 EB0 PL0 ENV0 PL0OK rt_fpE (rt_misc5_agree E0 FSB0 PL0) (rt_fpc_where2 E0 FSB0 PL0) so_fpc stdio_rep_agree so_fpc_where2
                (sA ast1 s) sr LB LF m2 mo1 aa3 m5 mo4 LB3 W5 lo (usp + -2128) R4 R4' AH1);
        [reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| exact Hrep5| exact WF5| exact K5| exact RO5| exact QB5| exact DI5| exact BI5| exact SS5| exact CS5| exact BM3| exact ATOK4| exact MI5| exact MUD| exact FWD| exact LOC
        | cbn [aps_credit sr]; clear -CF1 RFN; lia
        | clear -BW1 FA1; unset_all; cbn [aps_alloc sA aps_set_alloc] in *; lia
        | clear -BW2 FA3; unset_all; cbn [aps_alloc sA aps_set_alloc] in *; lia
        | ].
      clear -FA1 FA2 FA3 DEPR MNP MND MRES. unset_all. cbn [aps_credit aps_alloc sA aps_set_alloc]. clear MNP MND MRES.
      rewrite FA1, FA2. lia. }
    (* [comment removed for export] *)
    pose proof AH4 as AH4c. unfold BF_tkit.AHKc in AH4c.
    destruct AH4c as (_ & WF6 & K6 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hkm4 & Hli4 & _ & _ & Henv4 & _). destruct Hkm4 as (Khalt4 & Kminv4 & Klim4).
    cbn [aps_alloc aps_env sr] in WF6, K6. rewrite EE in WF6, K6.
    assert (K6q : AKern E0 (aps_alloc sr) mo4) by exact K6. pose proof (proj1 WF6) as WE6.
    assert (PSTK4 : forall a'' k, lo <= a'' -> a'' + Z.of_nat k <= 2^64 -> PP sr mo4 (Z_to_bv 64 a'', k)).
    { intros a'' k H1 H2. rewrite <- EPOL. eapply (pol_stack' E0 FSB0 HR0 sr mo4 K6q WE6 ENV0); clear -H1 H2 LOC; lia. }
    assert (KIP4 : KIP (aS E0 FSB0 HR0 sr) (aN E0 FSB0 HR0 sr) (aEB EB0 sr) (PP sr mo4) mo4) by (split; [exact (AHK_kia _ _ _ _ _ _ _ _ _ _ _ _ _ AH4)| intros x Hx; exact Hx]).
    (* [comment removed for export] *)
    assert (AGS : forall X k, usp + -2128 <= X -> X + k <= usp -> agree_on m2 m5 X k).
    { intros X k H1 H2. eapply (above_sp_agree E0 ENV0 ast1 aa3 mo4 lo (usp + -2128) W5 m2 m5); [exact MUD| exact FWD| exact Hwf1| exact WF5| exact K5| exact H1| clear -H1 LO LOC; lia| clear -H2 USPR; lia]. }
    Ltac fxfer H AGS := eapply rw_cells_agree' in H; [| apply AGS; cbn; clear; lia].
    fxfer OBJ AGS. fxfer FR7 AGS. fxfer FJ1800 AGS. fxfer FBP AGS. fxfer FJ8 AGS.
    assert (ARR5 : u64arr bsegs m5 (usp + -2112) ws) by (apply (u64arr_agree m2 m5 (usp + -2112) ws); [apply AGS; rewrite ?LEN30; cbn; clear; lia| exact ARR]).
    eapply (rzA_seg_cfg bsegs (aS E0 FSB0 HR0 sr) (aN E0 FSB0 HR0 sr) (aEB EB0 sr) (PP sr mo4)
              (fun ms => ms = MS (mkR ra (wz usp) gp (wz 0x5e1550) w0 w1 w2 s0 s1 b0 b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 w3 w4 w5 w6) F (ret_pc ra) fc None m5 (seg_rom bsegs)
                         /\ stk bsegs m5 lo usp));
      [| exact KIP4|].
    { rewrite (ret_pc_even 0x54058) by (clear; lia).
      eapply (free_epi (PP sr mo4)) with (lo := lo); [exact LOC| clear -LO; lia| intros a'' k H1 H2; apply PSTK4; [exact H1| clear -H2 USPR; lia]
        | exact MI5| exact SK5| exact OBJ| exact ARR5| exact LEN30| exact FJ1800| exact FBP| exact FJ8| exact FR7|].
      intros SK6. apply evtA_done. split; [reflexivity| exact SK6]. }
    cbv beta. intros ms7 mo5 [-> SK6] Hag7 KP7.
    assert (AH5 : AHKc sr LB3 LF m5 mo5).
    { unfold BF_tkit.AHKc. eapply (AHK_magree SR RT E0 FSB0 HR0 L0 RES0 EB0 sr LB3 LF m5 mo4 mo5); [exact AH4| exact Hag7| exact (proj1 (proj1 KP7))]. }
    pose proof (magree_frame _ _ Hag7) as (Qfds7 & Qvm7 & Qlz7 & Qfs7 & _).
    subst LB3.
    apply (CONT w0 w1 w2 b0 b1 b2 b3 b4 b5 b6 b7 w3 w4 w5 w6 F fc m5 mo5 sr); [exact SK6| | exact FRM| reflexivity| exact AH5| | | |].
    + (* [comment removed for export] *)
      eapply aheap_pres_trans; [eapply aheap_pres_sub; [intros b Hb; exact (ab_remove_sub _ _ _ Hb)| exact HP1]|].
      eapply aheap_pres_sp_mono with (SP' := usp + -2128); [| clear; lia].
      eapply (aw_client_pres_nw E0 FSB0 HR0 L0 RES0 EB0 PL0 ENV0 PL0OK (sA ast1 s) LB LF m2 mo1 aa3 mo4 m5 W5 lo (usp + -2128) (ab_remove A LB) AH1 WF5 K5 MUD);
        [exact FWD| exact LOC| clear -LO; lia|].
      intros b Hb. pose proof (ab_remove_sub _ _ _ Hb) as HbL. split; [exact HbL|].
      apply Forall_forall. intros iv Hiv.
      pose proof (blocks_match_In _ _ _ Hbm HbL) as HbA.
      apply (proj1 (Forall_forall _ _) FBD iv Hiv (ab_addr b) (ab_size b)); [cbn [aps_alloc sA aps_set_alloc]; rewrite MLB; exact HbA|].
      intros E. injection E as E1 E2. exact (ab_remove_neq A LB b NDLB Hb E1).
    + (* [comment removed for export] *)
      split; [| split; [cbn [aps_credit sr]; clear -RFN; lia| repeat split; reflexivity]].
      destruct RUN2 as (f2 & orc2 & evs2 & orc2' & RUN2). subst ast1 ts. rewrite shell_st_ia0 in RUN2.
      destruct (afree_run_some (bst_key (Z.of_nat (length tr)) ws) A (aps_alloc s) f2 orc2 aa3 evs2 orc2' ltac:(clear -GA1; lia) RUN2) as [f RUN].
      cbn [aps_alloc sr]. exists (bst_key (Z.of_nat (length tr)) ws), f, orc2, evs2, orc2'. exact RUN.
    + rewrite Qfs7, Ffs5, Qfs1. reflexivity.
    + rewrite Qfds7, Ffds5, Qfds1. reflexivity.
    + rewrite (arefund_at_found A sz LB NDLB HLB). cbn [aps_credit sr]. unfold afree_cost. replace (A =? 0) with false by (symmetry; apply Z.eqb_neq; clear -GA1; lia). clear; lia.
Qed.
End FreeT2.
End RC__1.
