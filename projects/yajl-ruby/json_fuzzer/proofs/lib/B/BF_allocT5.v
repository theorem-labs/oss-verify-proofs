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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr Nodes NodesCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import AImages AImageFacts ExecA LazyModel NodesA ImplRzA NodesA_mm NodesA_mmW SysStepA StepA StepA2 Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import STree.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanConsts AsanSizeClass AsanState AsanLayout AsanOps AsanHoare AsanPS AsanRep AsanKern AsanClient AsanWf1 AsanWf2 AsanWf3 AsanWf4 AsanWf5 AsanBudget AsanBudget2 AsanDepot AsanRepFrame AsanRepFrame2 AsanHit AsanRepHitB AsanRepCaB AsanRepX AsanRepSecB AsanSecCount AsanSlack AsanFrame AsanWf3b AsanWf5 AsanRepX2B AsanRepTailB AsanRepX3B.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import B_iface BF_place BF_fakestack_rep BF_kit BF_kit2 BF_kit3 BF_unwind BF_casec BF_lalloc2 BF_lalloc3 B_policy5 B_slack5 B_budget5 B_live B_bundle B_benv5 B_init5 B_instD5 B_balloc5 B_bpolicy5 B_rtok5 B_bevents5 BF_alloc_iface BF_ca_iface BF_dput_iface BF_tkit BF_ainv_kit BF_glue_kit BF_caT BF_casT BX_unreg BX_Exit BF_statics BF_poison BF_poison0 BF_premap2 BF_allocA BF_allocB BF_allocC BF_allocD BF_depot3 BF_dputT BF_caframe BF_deallocT1 BF_deallocT2 BF_caT2 BF_atail.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
#[warnings="-notation-for-abbreviation"] Notation mem := (word -> option byte).
#[warnings="-notation-for-abbreviation"] Notation wz := (fun z : Z => Z_to_bv 64 z).

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import LiaA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac lia ::= LiaA.liaA.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import SecRanges.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= force_section_ranges.
Ltac aceil :=
  lazymatch goal with
  | H : _ <= alloc_ceiling <= _ |- _ => idtac
  | |- context [alloc_ceiling] => repeat match goal with H : True |- _ => clear H end; pose proof alloc_ceiling_range as CEILB
  | H : context [alloc_ceiling] |- _ => repeat match goal with H' : True |- _ => clear H' end; pose proof alloc_ceiling_range as CEILB
  | _ => first [ pose proof I as CEILB | idtac ]
  end.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma sA_self : forall s, sA (aps_alloc s) s = s.
Proof. intros s. destruct s. reflexivity. Qed.
Lemma sA_sA : forall a a' s, sA a (sA a' s) = sA a s.
Proof. intros a a' s. destruct s. reflexivity. Qed.
Lemma aps_alloc_sA : forall a s, aps_alloc (sA a s) = a.
Proof. intros a s. destruct s. reflexivity. Qed.

Section AllocT5.
Variable E0 : aenv.
Variable FSB0 : Z.
Variable HR0 : list (Z * Z).
Variables L0 RES0 : list (word * word).
Variable EB0 : Z.
Variable PL0 : fs_plumb.
Hypothesis HR0_ok : Forall (fun iv => fst iv <= snd iv) HR0 /\ A0_pages HR0 <= 8192.
Hypothesis EB0_ok : 0 <= EB0 <= 2^32.
Hypothesis ENV_depot : zlen (ae_keys0 E0) <= 1000 /\ 0 <= ae_frames0 E0 <= 4096.
Hypothesis ENV0 : env0_ok5 E0.
Hypothesis PL0OK : pl0_ok5 E0 PL0.
Hypothesis L0OK : l0_ok5 E0 L0 RES0.
(* [comment removed for export] *)
Lemma CA : ca_srz_stmt E0 FSB0 HR0 L0 RES0 EB0 PL0.
Proof. exact (BF_caT2.ca_srz E0 FSB0 HR0 L0 RES0 EB0 PL0 HR0_ok EB0_ok ENV_depot ENV0 PL0OK L0OK). Qed.
Lemma LS_L0 : In (Z_to_bv 64 0x7fff7000, Z_to_bv 64 (2^28)) L0. Proof. exact (proj1 L0OK). Qed.
Lemma GS_L0 : In (Z_to_bv 64 0x8fff7000, Z_to_bv 64 (2^41)) L0. Proof. exact (proj1 (proj2 L0OK)). Qed.
Lemma HS_L0 : In (Z_to_bv 64 0x2008fff7000, Z_to_bv 64 0xdfff0001000) L0. Proof. exact (proj1 (proj2 (proj2 L0OK))). Qed.
Lemma RES0_low : Forall (fun e => 0x10000 <= elo e /\ ehi e <= 0x603000) RES0. Proof. exact (proj1 (proj2 (proj2 (proj2 L0OK)))). Qed.

#[local] Notation RTOKc := (RTOK E0 FSB0 HR0 L0 RES0 EB0).
#[local] Notation ATOKc := (ATOK E0 FSB0 HR0 L0 RES0 EB0).
#[local] Notation aSc := (B_bundle.aS E0 FSB0 HR0).
#[local] Notation aNc := (B_bundle.aN E0 FSB0 HR0).
#[local] Notation aEBc := (B_bundle.aEB EB0).
#[local] Notation SB := (ae_space_beg E0).
#[local] Notation T := (ae_thread E0).
#[local] Notation PA := (ae_ptr_array E0).
#[local] Notation CTX := (fp_ctx PL0).
#[local] Notation PP := (BF_caT.PP E0 FSB0 HR0).
#[local] Notation DPUT := (BF_dputT.depot_put_srz E0 FSB0 HR0 L0 RES0 EB0 HR0_ok ENV0 ENV_depot EB0_ok L0OK).

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Call.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m : mem) (mo : Model) (s : aps) (n lo B A len C C' : Z) (ws : list word) (K : TSet).
#[local] Notation a := (aps_alloc s).
#[local] Notation usp := (bv_unsigned sp).
#[local] Notation hi := (A + 8 * zlen ws).
Hypothesis KN : K [].
Hypothesis TOK : RTOKc C C' s mo.
Hypothesis CHG : acharge n <= C.
Hypothesis ASL : ASLACK <= C'.
Hypothesis AIV : AINV E0 FSB0 PL0 a m mo.
Hypothesis ABUD : abudget_pre a n.
Hypothesis Hn : 0 < n <= 2^27.
Hypothesis NBIG : nbig_live a <= 8000.
Hypothesis SK : stk bsegs m lo usp.
Hypothesis LOC : alloc_ceiling <= lo.
Hypothesis LO : lo <= usp - K_ALLOC.
Hypothesis SPA : usp mod 16 = 0.
Hypothesis TP : tp = wz 0x5e1550.
Hypothesis UB : usp <= B.
Hypothesis BA : B + 16 <= A.
Hypothesis AHI : A + 8 * zlen ws < 2^47.
Hypothesis BOBJ : rw_cells bsegs m B [C8 (wz A); C8 (wz len)].
Hypothesis TR : u64arr bsegs m A ws.
Hypothesis LEN : 1 <= len <= zlen ws.
Hypothesis LWS : zlen ws <= 30.
Hypothesis CONT : forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem) (mo' : Model) (a' : astate) (r : Z),
     alloc_post_state E0 FSB0 HR0 L0 RES0 EB0 PL0 a a' m m' mo mo' s C C' n lo usp (bst_key len ws) r a0' ->
     realizes_cfg acfg bsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                               F (ret_pc ra) fc None m' (seg_rom bsegs)) mo') K.

(* [comment removed for export] *)
Lemma USPR : 0 <= usp < 2^64. Proof. pose proof (bv_unsigned_in_range 64 sp) as X. unfold bv_modulus in X. exact X. Qed.
Lemma Esp : sp = wz usp. Proof. symmetry. apply Z_to_bv_bv_unsigned. Qed.
Lemma Hn1 : 1 <= n <= 2^27. Proof. clear -Hn. lia. Qed.
Lemma HB : usp <= B /\ B + 16 <= hi. Proof. pose proof LEN. clear -UB BA LEN H. unfold zlen in *. lia. Qed.
Lemma LO512 : lo <= usp - 512. Proof. pose proof LO as X. unfold K_ALLOC in X. clear -X. lia. Qed.
Lemma Hrep : ARep bsegs E0 (DepotR bsegs E0) a m. Proof. exact (proj1 AIV). Qed.
Lemma Hwf : AWf E0 [] [] a. Proof. exact (proj1 (proj2 AIV)). Qed.
Lemma Hkern : AKern E0 a mo. Proof. exact (proj1 (proj2 (proj2 AIV))). Qed.
Lemma Hmi : mem_inv bsegs m. Proof. pose proof AIV as (_ & _ & _ & _ & _ & _ & _ & X & _). exact X. Qed.
Lemma Hrt : rt_misc5 FSB0 PL0 E0 m. Proof. pose proof AIV as (_ & _ & _ & _ & _ & _ & _ & _ & X & _). exact X. Qed.
Lemma WE : wf_env E0. Proof. exact (proj1 Hwf). Qed.
Lemma ATK0 : exists R0 R0', ATOKc R0 R0' s mo /\ 0 <= C <= R0 /\ 0 <= C' <= R0'.
Proof. destruct (RTOK_elim _ _ _ _ _ _ _ _ _ _ TOK) as (R0 & R0' & ATK & HC & HC' & _). exists R0, R0'. split; [exact ATK|]. split; [exact HC| exact HC']. Qed.
Lemma ENV : ENVOK E0 FSB0 s.
Proof. destruct ATK0 as (R0 & R0' & ATK & _). exact (ATOK_ENVOK _ _ _ _ _ _ _ _ _ _ ATK). Qed.
Lemma EE : aps_env s = E0. Proof. pose proof ENV as (_ & _ & _ & _ & _ & _ & _ & _ & _ & X & _). exact X. Qed.
Lemma IMGE : fst (ae_img E0) = 0x10000 /\ 0x5f3000 <= snd (ae_img E0).
Proof. pose proof ENV as (_ & _ & _ & _ & _ & _ & _ & _ & _ & X & _ & Y). rewrite X in Y. exact Y. Qed.
Lemma IC0 : ae_ic E0 = both_ic.
Proof. pose proof ENV0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X & _). exact X. Qed.
Lemma KIP0 : KIP (aSc s) (aNc s) (aEBc s) (PP s mo) mo.
Proof. destruct ATK0 as (R0 & R0' & ATK & _). exact (PP_KIP E0 FSB0 HR0 L0 RES0 EB0 s mo R0 R0' ATK). Qed.
(* [comment removed for export] *)
Lemma EPOL : forall s' mo' a' k, POL E0 FSB0 HR0 s' mo' a' k = PP s' mo' (wz a', k). Proof. intros; reflexivity. Qed.
Lemma PSTK0 : forall a' k, lo <= a' -> a' + Z.of_nat k <= hi -> PP s mo (wz a', k).
Proof. intros a' k H1 H2. rewrite <- EPOL. eapply (pol_stack' E0 FSB0 HR0 s mo Hkern WE ENV0); clear -H1 H2 LOC AHI; aceil; lia. Qed.
Lemma PIMG0 : forall a' k, 0xa5000 <= a' -> a' + Z.of_nat k <= 0x603000 -> PP s mo (wz a', k).
Proof. intros a' k H1 H2. rewrite <- EPOL. eapply (pol_img' E0 FSB0 HR0 s mo Hkern WE ENV ENV0); [clear -H1; lia| exact H2]. Qed.
Lemma PRO0 : forall a' k, 0x10000 <= a' -> a' + Z.of_nat k <= 0x31000 -> PP s mo (wz a', k).
Proof. intros a' k H1 H2. rewrite <- EPOL. eapply (pol_img' E0 FSB0 HR0 s mo Hkern WE ENV ENV0); [clear -H1; lia| clear -H2; lia]. Qed.
Lemma PTHR0 : forall a' k, T <= a' -> a' + Z.of_nat k <= T + 4096 -> PP s mo (wz a', k).
Proof. intros a' k H1 H2. rewrite <- EPOL. eapply (pol_thread' E0 FSB0 HR0 s mo Hkern WE); [exact H1| exact H2]. Qed.
Lemma CTXR : exists c0 cl, resv_range_ok E0 c0 cl /\ c0 <= CTX /\ CTX + 160 <= c0 + cl.
Proof. pose proof PL0OK as ((c0 & cl & RRC & CLO & CHI) & _). exists c0, cl. auto. Qed.
Lemma PCTX0 : forall a' k, CTX <= a' -> a' + Z.of_nat k <= CTX + 160 -> PP s mo (wz a', k).
Proof. intros a' k H1 H2. destruct CTXR as (c0 & cl & RRC & CLO & CHI). rewrite <- EPOL. eapply (pol_resv_range' E0 FSB0 HR0 s mo Hkern c0 cl _ _ RRC); clear -H1 H2 CLO CHI; lia. Qed.
(* [comment removed for export] *)
Lemma IMX : rw_cells bsegs m 0xabd78 [C8 (wz (2^40)); C2 (wz 16); C2 (wz 2048); C1 (Z_to_bv 8 1)].
Proof.
  pose proof Hrep as (Rins & _). pose proof Rins as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & I12).
  unfold ae_instance in I12. rewrite IC0 in I12. cbn [aic_instance both_ic kInsMaxUserDefined Z.add] in I12. unfold kMinRedzone, kMaxRedzone in I12. exact I12.
Qed.
Lemma AI1 : rw_cells bsegs m 0xaf298 [C1 (Z_to_bv 8 1)].
Proof.
  pose proof Hrep as (_ & _ & _ & _ & _ & _ & _ & _ & Rglob & _). pose proof Rglob as (_ & _ & _ & _ & _ & _ & _ & Gai & _).
  rewrite IC0 in Gai. cbn [aic_asan_inited both_ic] in Gai. exact Gai.
Qed.
Lemma RSS : rw_cells bsegs m 0x130822 [C1 (Z_to_bv 8 0)].
Proof. pose proof Hrt as (_ & _ & _ & AMS & _). pose proof AMS as (_ & _ & X & _). exact X. Qed.
Lemma FSE : FSEnv bsegs E0 FSB0 PL0 m. Proof. exact (rt_misc5_fsenv _ _ _ _ Hrt). Qed.
Lemma TC : thread_cells m tp 0x6028f8 CTX T.
Proof.
  pose proof FSE as FSE'. unfold FSEnv in FSE'. pose proof FSE' as (_ & _ & _ & _ & _ & _ & FKI & FKEY & FTSD & FTSD0 & FCTXT & _). clear FSE'.
  split; [exact FKI|]. split; [exact FKEY|]. split; [| split; [exact FTSD0| exact FCTXT]].
  rewrite TP. unfold FS_TP. rewrite unsigned_lit by (clear; lia). exact FTSD.
Qed.
Lemma T8 : T mod 8 = 0.
Proof. pose proof FSE as FSE'. unfold FSEnv in FSE'. decompose [and] FSE'; assumption. Qed.
Lemma HT : placed_s T 4096 /\ T mod 8 = 0.
Proof. pose proof PL0OK as (_ & _ & (_ & P & _) & _). split; [exact P| exact T8]. Qed.
Lemma HTP : 6096912 + 88 <= bv_unsigned tp /\ bv_unsigned tp + 60 <= 6303744.
Proof. rewrite TP. rewrite unsigned_lit by (clear; lia). clear; lia. Qed.
Lemma HTSD : 6096912 <= 0x6028f8 /\ 0x6028f8 + 8 <= 6303744. Proof. clear; lia. Qed.
Ltac wfe_open WE :=
  destruct WE as (WE1 & WE2 & WE3 & WE4 & WE5 & WE6 & WE7 & WE8 & WE9 & WE10 & WE11 & WE12 & WE13 & WE14 & WE15 & WE16 & WE17 & WE18 &
                  WE19 & WE20 & WE21 & WE22 & WE23 & WE24 & WE25 & WE26 & WE27 & WE28 & WE29 & WE30 & WE31 & WE32 & WE33 & WE34 & WE35rest).
Lemma HCTX : placed CTX 4096.
Proof.
  aceil. pose proof WE as WE'. wfe_open WE'. pose proof IMGE as [EI1 EI2].
  pose proof PL0OK as (_ & _ & _ & _ & _ & _ & [IA1 IA2]).
  pose proof WE35rest as IS. unfold img_sep in IS. rewrite EI1 in IS. unfold app_mem in WE25. rewrite ?kHighMemBeg_val, ?kLowAppEnd_val in WE25.
  unfold placed, A_IMG_END, A_LOWAPP_END, A_HIGH_BEG, kIArenaLen in *. clear -IA1 IA2 WE25 WE26 IS EI2 CEILB. lia.
Qed.
Lemma TCTX : CTX + 160 <= T \/ T + 4096 <= CTX.
Proof. pose proof PL0OK as (_ & _ & _ & X & _). exact X. Qed.
Lemma CTXhi : 0x603000 <= CTX /\ CTX + 4096 <= alloc_ceiling.
Proof. pose proof HCTX as (P1 & P2 & _). unfold A_IMG_END in P1. split; [exact P1| exact P2]. Qed.
Lemma Thi : 0x1000 <= T /\ T + 4096 <= alloc_ceiling.
Proof. pose proof HT as [(P1 & P2 & _) _]. split; [exact P1| exact P2]. Qed.
(* [comment removed for export] *)
Lemma AINV_stack : forall (m' : mem) (mo' : Model),
  wmono bsegs m m' -> (forall z, 0 <= z < 2^64 -> z < lo -> m' (wa z) = m (wa z)) -> mem_inv bsegs m' ->
  m_vmmaps mo' = m_vmmaps mo -> m_vm_lazy mo' = m_vm_lazy mo ->
  AINV E0 FSB0 PL0 a m' mo'.
Proof.
  intros m' mo' WM AG MI' Qvm Qlz. aceil.
  pose proof AIV as (REP & WF & AK & RO & QB & DI & BI & MI & RT & SST & CSM).
  pose proof IMGE as [EI1 EI2].
  pose proof ENV0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & IMGR & _).
  assert (IMG_IN : forall r, In r (arep_img_ranges E0 ++ depot_static E0) -> fst (ae_img E0) <= fst r /\ fst r + snd r <= fst (ae_img E0) + snd (ae_img E0)).
  { intros r Hr. pose proof (IMGR r Hr) as X. rewrite EI1. clear -X EI2. lia. }
  pose proof (blocks_sep_of E0 a mo ENV0 WF AK) as BS.
  assert (REP' : ARep bsegs E0 (DepotR bsegs E0) a m').
  { eapply (ARep_frame_client bsegs _ _ (DepotFP E0)); [| exact REP| exact WM|].
    - intros a0 mm mm' DD W' A'. eapply DepotR_frame; [exact DD| exact W'| exact A'].
    - intros x FPx.
      pose proof (fp_below_ceiling _ _ [] [] IMG_IN (DepotFP_where E0) _ _ WF BS FPx) as UBx.
      assert (Hx : 0 <= x < 2^64).
      { destruct (fp_locate _ _ [] [] IMG_IN (DepotFP_where E0) _ _ WF BS FPx) as [(r & Hr & R)|[[R _]|[R _]]].
        - pose proof (IMG_IN r Hr). rewrite EI1 in H. clear -H R UBx CEILB. lia.
        - unfold sh_band, kLowShadowBeg, kShadowBase in R. rewrite ?kHighShadowBeg_val in R. clear -UBx CEILB R. lia.
        - unfold app_addr in R. rewrite ?kHighMemBeg_val in R. clear -UBx CEILB R. lia. }
      apply AG; [exact Hx| clear -UBx LOC; lia]. }
  assert (AGR : forall x, rt_fpc E0 FSB0 PL0 x -> m' (wa x) = m (wa x)).
  { intros x Hx. pose proof CTXhi as [C1 C2]. pose proof Thi as [T1 T2].
    pose proof PL0OK as (_ & (d0 & dl & DR0 & DD1 & DD2) & _).
    pose proof (resv_range_num E0 d0 dl DR0 ltac:(clear -DD1 DD2; lia)) as (DQ1 & DQ2 & DQ3 & DQ4).
    destruct (rt_fpc_where E0 FSB0 PL0 x Hx) as [(X1 & _)|X]; [apply AG; clear -X1 LOC CEILB; lia|].
    unfold rt_high2 in X. apply AG; clear -X LOC CEILB C1 C2 T1 T2 DQ1 DQ2 DD1 DD2; lia. }
  split; [exact REP'|]. split; [exact WF|]. split; [exact (AKern_frame _ _ _ _ Qvm Qlz AK)|]. split; [exact RO|]. split; [exact QB|].
  split; [exact DI|]. split; [exact BI|]. split; [exact MI'|]. split; [eapply rt_misc5_agree; [exact RT| exact AGR]|]. split; [exact SST| exact CSM].
Qed.

(* [comment removed for export] *)
Lemma stageA :
  (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s8' t3' t4' t5' t6' : word) (m1 m' : mem) (mo1 mo' : Model) (a1 : astate) (ab : Z) (junk : list byte),
     munch [(usp - 144, usp)] m m1 -> wmono bsegs m m1 -> mem_inv bsegs m1 -> frameA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m1 junk ->
     magree mo mo1 ->
     ca_post E0 FSB0 HR0 L0 RES0 EB0 PL0 a a1 m1 m' mo1 mo' s C C' n lo (usp - 128) ab a0' ->
     realizes_cfg acfg bsegs (mkCfg (MS (mkR (wz 0x32cac) (wz (usp - 128)) gp tp t0' t1' t2' (wz (Z.b2z (from_primary n))) (wz n) a0' a1' a2' a3' a4' a5' a6' a7'
                                          (wz 8) (wz (needed n)) (wz (rz_size n)) (wz n) (wz A_INST) (wz B) s8' (wz 7) (wz T) (wz 1) t3' t4' t5' t6')
                                    F (wz 0x32cac) fc None m' (seg_rom bsegs)) mo') K) ->
  realizes_cfg acfg bsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz A_INST) (wz n) (wz 8) (wz B) (wz 1) (wz 1) a6 a7
                                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                            F (wz A_ALLOCATE) fc None m (seg_rom bsegs)) mo) K.
Proof.
  intros CONTA. pose proof USPR as USPR'. pose proof LOC as LOC'. aceil. pose proof LO512 as LO'.
  eapply (rzA_seg_cfg bsegs (aSc s) (aNc s) (aEBc s) (PP s mo)); [| exact KIP0|].
  { unfold A_ALLOCATE, A_INST.
    eapply (alloc5_segA (PP s mo) ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo hi n B 0x6028f8 CTX T);
      [ exact SK| exact LOC'| exact LO'| clear -UB BA LEN; unfold zlen in *; lia| exact AHI| exact Hmi| exact Hn1| exact HB| exact IMX| exact AI1| exact RSS| exact TC
      | exact HTSD| exact HCTX| exact HT| exact HTP| exact PSTK0| exact PIMG0| exact PRO0| exact PCTX0]. }
  intros ms1 mo1 POST1 AG1 KP1.
  destruct POST1 as (t0' & t1' & t2' & a4' & a5' & a6' & a7' & s8' & t3' & t4' & t5' & t6' & m1 & junk & -> & MU1 & WM1 & MI1 & SK1 & FR1).
  pose proof (magree_frame _ _ AG1) as (Qfds1 & Qvm1 & Qlz1 & Qfs1 & Qh1 & Qtid1 & _).
  assert (AG1m : forall z, 0 <= z < 2^64 -> z < lo -> m1 (wa z) = m (wa z)).
  { intros z Hz Hl. apply MU1. rewrite wa_unsigned by exact Hz. cbn. clear -Hl LO'. lia. }
  pose proof (AINV_stack m1 mo1 WM1 AG1m MI1 Qvm1 Qlz1) as AIV1.
  pose proof (RTOK_magree E0 FSB0 HR0 L0 RES0 EB0 C C' s mo mo1 TOK AG1 (proj1 KP1)) as TOK1.
  (* [comment removed for export] *)
  assert (USP128 : bv_unsigned (wz (usp - 128)) = usp - 128) by (apply unsigned_lit; clear -USPR' LO' LOC' CEILB; lia).
  pose proof CA as CA'. unfold ca_srz_stmt, ca_srz_case in CA'.
  assert (GC : ca_gcost n <= C').
  { unfold ca_gcost. destruct (from_primary n) eqn:PR; [clear -ASL; unfold ASLACK in *; lia|].
    destruct (needed_sec n Hn PR) as (N1 & N8 & N2 & N40). unfold map_size, round_up, NMAXA, kPageSize, ASLACK in *. clear -ASL N2. Z.div_mod_to_equations. lia. }
  assert (SK1' : stk bsegs m1 lo (bv_unsigned (wz (usp - 128)))) by (rewrite USP128; replace (usp - 128) with (usp + -128) by (clear; lia); exact SK1).
  eapply (CA' (wz 0x32cac) (wz (usp - 128)) gp tp t0' t1' t2' (wz (Z.b2z (from_primary n))) (wz n) a4' a5' a6' a7'
             (wz 8) (wz (needed n)) (wz (rz_size n)) (wz n) (wz A_INST) (wz B) s8' (wz 7) (wz T) (wz 1) t3' t4' t5' t6' F fc m1 mo1 s n lo C C' K
             I KN TOK1 CHG GC AIV1 ABUD Hn NBIG SK1' LOC');
    rewrite ?USP128; [clear -LO; unfold K_ALLOC, K_CA in *; lia| clear -SPA; Z.div_mod_to_equations; lia| clear -UB BA AHI LEN; unfold zlen in *; lia| exact TP|].
  intros u0 u1 u2 a0' a1' a2' a3' b4 b5 b6 b7 u3 u4 u5 u6 m' mo' a1 ab POST.
  replace (ret_pc (Z_to_bv 64 208044)) with (Z_to_bv 64 208044) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
  pose proof POST as (SK2 & WM2 & (W & MUW & FW & FWB) & _).
  eapply (CONTA u0 u1 u2 a0' a1' a2' a3' b4 b5 b6 b7 s8' u3 u4 u5 u6 m1 m' mo1 mo' a1 ab junk MU1 WM1 MI1 FR1 AG1 POST).
Qed.
(* [comment removed for export] *)
Lemma ca_dput_nums : forall (a1 : astate) (m1 : mem) (mo1 : Model) C1 C1',
  CAINV E0 FSB0 PL0 a1 m1 mo1 -> RTOKc C1 C1' (sA a1 s) mo1 ->
  0 <= as_nprim_ever a1 -> 10000 * as_nprim_ever a1 + as_ndepot_ins a1 + 1 <= kInitialCredit ->
  zlen (as_node_blocks a1) <= 1832 /\ zlen (as_store_blocks a1) <= 7400 /\ AsanState.sec_bytes a1 <= 2^39 /\ as_ndepot_ins a1 + 1 <= kInitialCredit.
Proof.
  intros a1 m1 mo1 C1 C1' (Hwf1 & Hkern1 & Hres1 & Hqb1 & Hdi1 & _) TOK1 NP BUD. pose proof ENV_depot as [K0 [_ F0]].
  pose proof Hdi1 as (D1 & D2 & D3 & D4 & D5 & D6 & D7).
  pose proof Hwf1 as (_ & _ & _ & _ & _ & _ & (_ & WD2 & WD3)).
  unfold depot_n_ids in D1, D5. unfold zlen in *. unfold kDepotNodesPerBlock, kStoreBlockFrames, kInitialCredit in *.
  split; [clear -D1 WD2 BUD K0 NP; nia|].
  split; [clear -D2 D3 BUD F0 NP; nia|].
  split; [| clear -BUD NP; lia].
  destruct (RTOK_elim E0 FSB0 HR0 L0 RES0 EB0 _ _ _ _ TOK1) as (R & R' & ATK & _).
  pose proof ATK as ((HLI & _ & _) & [O1 O2] & _ & VL & _).
  pose proof (li_budget _ _ _ _ HLI) as LB. rewrite VL in LB. cbn [aps_alloc sA aps_set_alloc] in LB.
  unfold aEB, B_policy5.aEB, aEBa, a_eager_bytes in LB. cbn [aps_alloc sA aps_set_alloc] in LB.
  pose proof (regions_bytes_nonneg E0 a1 Hwf1) as RB.
  assert (0 <= (if as_ptr_committed a1 =? 0 then 0 else kPtrArrayCommit)) by (unfold kPtrArrayCommit; destruct (as_ptr_committed a1 =? 0); clear; lia).
  unfold kDepotNodeBlockBytes, page_size, zlen in LB. clear -LB RB H EB0_ok. lia.
Qed.

(* [comment removed for export] *)
Lemma newblk_geom : forall (a1 : astate) (ab : Z),
  AWf E0 [] [] a1 ->
  (if from_primary n
      then as_cache_inited a1 = true /\ avail E0 [] a1 (malloc_class n) ab
           /\ exists x, ab = chunk_of_compact SB (malloc_class n) x /\ (16 * x) mod class_size (malloc_class n) = 0
      else exists r0, ab = r0 + kPageSize /\ as_sec a1 = as_sec a ++ [mkSec r0 (map_size n) (needed n)] /\ sec_fresh E0 a r0 (map_size n)) ->
     0x603000 <= ab /\ ab + ca_span n <= alloc_ceiling /\ ab mod 16 = 0 /\ needed n <= ca_span n /\ ca_span n mod 8 = 0
  /\ (ab + ca_span n <= 0x7fff7000 \/ kHighMemBeg <= ab)
  /\ (ab + ca_span n <= T \/ T + 4096 <= ab) /\ (ab + ca_span n <= CTX \/ CTX + 160 <= ab).
Proof.
  intros a1 ab WF1 SIDE. aceil. pose proof WE as WE'. wfe_open WE'. pose proof IMGE as [EI1 EI2].
  pose proof PL0OK as (_ & _ & _ & _ & _ & _ & [IA1 IA2]).
  rewrite ?kHighMemBeg_val, ?kLowAppEnd_val in *. unfold app_mem in WE14, WE25. rewrite ?kHighMemBeg_val, ?kLowAppEnd_val in WE14, WE25.
  unfold ca_span. destruct (from_primary n) eqn:PR.
  - destruct SIDE as (_ & AV & x & Eab & XAL). set (c := malloc_class n) in *.
    assert (Hn' : 0 <= n <= 64512) by (pose proof (proj1 (from_primary_iff n ltac:(clear -Hn; lia)) PR); clear -Hn H; lia).
    pose proof (malloc_class_ok n Hn') as [HCc NEEDc]. fold c in HCc, NEEDc.
    pose proof (class_size_mod c HCc) as [CSM CS32].
    destruct AV as (CARVED & _). pose proof WF1 as (_ & WR1 & _).
    pose proof (carved_in_space E0 a1 c ab HCc WR1 CARVED) as [I1 I2].
    destruct (fp_cases n) as [(_ & EN & _)|[X _]]; [| rewrite PR in X; discriminate].
    rewrite EN. unfold kRegionSize, kSpaceSize, kIArenaLen in *.
    assert (AB16 : ab mod 16 = 0).
    { rewrite Eab. unfold chunk_of_compact, region_beg, kRegionSize. clear -WE1. Z.div_mod_to_equations. lia. }
    clear -I1 I2 WE2 WE3 WE4 WE5 WE19 WE27 IA1 IA2 CSM CS32 NEEDc AB16 CEILB. repeat split; try lia; Z.div_mod_to_equations; lia.
  - destruct SIDE as (r0 & Eab & ESEC & FR). destruct FR as (F1 & F2 & F3 & F4 & F5 & F6).
    unfold app_mem in F2. rewrite ?kHighMemBeg_val, ?kLowAppEnd_val in F2. unfold kPageSize, kSpaceSize in *.
    pose proof (F6 _ WE13) as XT. pose proof (F6 _ WE24) as XI. pose proof (F6 _ WE29) as XIMG. cbn [fst snd] in XT, XI, XIMG. rewrite EI1 in XIMG.
    destruct (needed_sec n Hn PR) as (N1 & N8 & N2 & N40).
    pose proof (map_size_facts n) as (MS4 & MSG & MS2). unfold kPageSize in MS4, MSG, MS2.
    assert (RU : round_up (needed n) 4096 + 4096 = map_size n) by reflexivity.
    assert (RU8 : round_up (needed n) 4096 mod 8 = 0 /\ needed n <= round_up (needed n) 4096) by (unfold round_up; clear -N1; Z.div_mod_to_equations; lia).
    unfold kIArenaLen in *. rewrite Eab.
    clear -F1 F2 F3 XT XI XIMG EI2 IA1 IA2 N1 MSG MS2 RU RU8 CEILB. repeat split; try lia; Z.div_mod_to_equations; lia.
Qed.

(* [comment removed for export] *)
Lemma ca_dput_statics : forall (a1 : astate) (m1 : mem) (mo1 : Model) blo bhi,
  CAINV E0 FSB0 PL0 a1 m1 mo1 -> ARepX bsegs E0 (DepotR bsegs E0) a1 m1 blo bhi -> dput_statics m1 /\ dput_mutexes m1 /\ DepotR bsegs E0 a1 m1.
Proof.
  intros a1 m1 mo1 blo bhi (_ & _ & _ & _ & _ & _ & Hrt & _) RX.
  destruct Hrt as (_ & [t XS] & _ & AMS & _).
  assert (US : unreg_statics m1) by (unfold exit_statics in XS; decompose [and] XS; assumption).
  unreg_statics_open US.
  destruct AMS as (_ & _ & _ & GPAIR & MML & DPM & CFF & _).
  destruct RX as (_ & _ & _ & _ & _ & _ & _ & RH & Rglob & _).
  pose proof Rglob as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Gps & Gdy & _).
  rewrite IC0 in Gps, Gdy. cbn [aic_page_size_cached aic_dying_flag both_ic] in Gps, Gdy.
  split; [| split; [| exact RH]].
  - split; [| exact CFF].
    unfold XB_mmap_fixed.statics, XB_mmap_fixed.GOT_PAGESIZE, XB_mmap_fixed.GOT_CFLAGS, XB_mmap_fixed.GOT_PAIR, XB_mmap_fixed.V_PAGESIZE, XB_mmap_fixed.V_CFLAGS, XB_mmap_fixed.V_MMAP_LIMIT, XB_mmap_fixed.V_DPM, XB_mmap_fixed.V_ABORTFLAG.
    split; [exact GPSC|]. split; [exact GCF|]. split; [exact GPAIR|]. split; [exact Gps|]. split; [exact MML|]. split; [exact DPM| exact Gdy].
  - destruct RH as [_ RH']. destruct RH' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & MU & MTX).
    rewrite IC0 in MU, MTX. cbn [aic_theDepot aic_stackStore both_ic] in MU, MTX.
    unfold dput_mutexes, dTD, dSS. split; [exact MU| exact MTX].
Qed.

(* [comment removed for export] *)
Definition bpost (m1 : mem) (mo1 : Model) (a1 : astate) (ab : Z) (junk : list byte)
    (ms : machine_state) (mo3 : Model) : Prop :=
  exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m2 m3 : mem) (mo2 : Model) (a2 : astate) (id b1 : Z) (j0 : byte),
    ms = MS (mkR (wz 0x32db8) (wz (usp - 128)) gp tp t0' t1' t2' (wz (Z.b2z (from_primary n))) (wz n) (wz id) a1' a2' a3' a4' a5' a6' a7'
                 (wz ab) (wz (needed n)) (wz (BF_allocB.ub n ab)) (wz (BF_allocB.cb n ab)) (wz A_INST) (wz B) (wz 0) (wz (BF_allocB.ub n ab + n)) (wz T) (wz 1) t3' t4' t5' t6')
            F (wz 0x32db8) fc None m3 (seg_rom bsegs)
    /\ munch [(BF_allocB.cb n ab, BF_allocB.cb n ab + 8)] m1 m2 /\ wmono bsegs m1 m2 /\ mem_inv bsegs m2
    /\ 0 <= b1 < 256 /\ Z.land b1 115 = 17
    /\ (exists j4, rw_cells bsegs m2 (BF_allocB.cb n ab) [C1 j0; C1 (Z_to_bv 8 b1); C2 (wz 0); C4 (wz n); C8 j4])
    /\ frameA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m2 junk
    /\ magree mo1 mo2
    /\ dput_post_state E0 FSB0 HR0 L0 RES0 EB0 a1 a2 m2 m3 mo2 mo3 (sA a1 s) (C - ca_cost n) (C' - ca_gcost n) lo (usp - 128) (bst_key len ws) id.

Lemma newblk_vs_dblocks : forall (a1 : astate) (ab : Z) (mo1 : Model),
  AWf E0 [] [] a1 -> AKern E0 a1 mo1 ->
  (if from_primary n
      then as_cache_inited a1 = true /\ avail E0 [] a1 (malloc_class n) ab
           /\ exists x, ab = chunk_of_compact SB (malloc_class n) x /\ (16 * x) mod class_size (malloc_class n) = 0
      else exists r0, ab = r0 + kPageSize /\ as_sec a1 = as_sec a ++ [mkSec r0 (map_size n) (needed n)] /\ sec_fresh E0 a r0 (map_size n)) ->
  forall b blen, (In b (ae_depot_nodes E0 :: as_node_blocks a1) /\ blen = kDepotNodeBlockBytes) \/ (In b (ae_store_blk E0 :: as_store_blocks a1) /\ blen = kStoreBlockBytes) ->
  ab + ca_span n <= b \/ b + blen <= ab.
Proof.
  intros a1 ab mo1 WF1 AK1 SIDE b blen Hb.
  destruct (blocks_sep_of E0 a1 mo1 ENV0 WF1 AK1 b blen Hb) as (_ & _ & BR & BSC & _).
  pose proof WF1 as (WE1 & WR1 & _). pose proof WE1 as (_ & _ & W3 & W4 & _).
  unfold ca_span. destruct (from_primary n) eqn:PR.
  - destruct SIDE as (_ & AV & x & Eab & XAL). set (c := malloc_class n) in *.
    assert (Hn' : 0 <= n <= 64512) by (pose proof (proj1 (from_primary_iff n ltac:(clear -Hn; lia)) PR); clear -Hn H; lia).
    pose proof (malloc_class_ok n Hn') as [HCc NEEDc]. fold c in HCc, NEEDc.
    destruct AV as (CARVED & _). pose proof (carved_in_space E0 a1 c ab HCc WR1 CARVED) as [I1 I2].
    unfold kRegionSize, kSpaceSize in *. clear -BR W3 W4 I1 I2. lia.
  - destruct SIDE as (r0 & Eab & ESEC & FR). pose proof (map_size_facts n) as (MS4 & MSG & MS2). unfold kPageSize in MS4, MSG, MS2, Eab.
    pose proof (BSC (mkSec r0 (map_size n) (needed n)) ltac:(rewrite ESEC; apply in_app_iff; right; left; reflexivity)) as X. cbn [sc_map_beg sc_map_size] in X.
    assert (RU : round_up (needed n) 4096 + 4096 = map_size n) by reflexivity.
    unfold kPageSize. clear -X Eab RU MSG. lia.
Qed.
Lemma stageB : forall (u0 u1 u2 a0' a1' a2' a3' b4 b5 b6 b7 s8' u3 u4 u5 u6 : word) (m1 m' : mem) (mo1 mo' : Model) (a1 : astate) (ab : Z) (junk : list byte),
  munch [(usp - 144, usp)] m m1 -> wmono bsegs m m1 -> mem_inv bsegs m1 -> frameA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m1 junk ->
  magree mo mo1 ->
  ca_post E0 FSB0 HR0 L0 RES0 EB0 PL0 a a1 m1 m' mo1 mo' s C C' n lo (usp - 128) ab a0' ->
  (forall ms3 mo3, bpost m' mo' a1 ab junk ms3 mo3 -> realizes_cfg acfg bsegs (mkCfg ms3 mo3) K) ->
  realizes_cfg acfg bsegs (mkCfg (MS (mkR (wz 0x32cac) (wz (usp - 128)) gp tp u0 u1 u2 (wz (Z.b2z (from_primary n))) (wz n) a0' a1' a2' a3' b4 b5 b6 b7
                                       (wz 8) (wz (needed n)) (wz (rz_size n)) (wz n) (wz A_INST) (wz B) s8' (wz 7) (wz T) (wz 1) u3 u4 u5 u6)
                                 F (wz 0x32cac) fc None m' (seg_rom bsegs)) mo') K.
Proof.
  intros until junk. intros MU1 WM1 MI1 FR1 AG1 POST CONTB.
  pose proof USPR as USPR'. pose proof LOC as LOC'. aceil. pose proof LO512 as LO'.
  pose proof (magree_frame _ _ AG1) as (Qfds1 & Qvm1 & Qlz1 & Qfs1 & Qh1 & Qtid1 & _).
  destruct POST as (SK2 & WM2 & (W & MUW & FW & FWB) & (fA & orcA & evsA & orcA' & RUNA) & CAI2 & TOK2 & Qfs2 & Qfds2 & Qtid2 & EA0 & RX2 & (shj & BSH & BSHP) & SIDE).
  subst a0'.
  pose proof CAI2 as (WF2 & AK2 & RO2 & QB2 & DI2 & MI2 & RT2 & SS2 & CS2).
  destruct (newblk_geom a1 ab WF2 SIDE) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
  pose proof (needed_range n Hn1) as (NR1 & NR2 & NR3). pose proof (rz_size_pos n) as RZ.
  (* [comment removed for export] *)
  destruct (RTOK_elim _ _ _ _ _ _ _ _ _ _ TOK2) as (R2 & R2' & ATK2 & HCR2 & HCR2' & _).
  pose proof (ATOK_ENVOK _ _ _ _ _ _ _ _ _ _ ATK2) as EV2.
  assert (PSTK2 : forall y k, lo <= y -> y + Z.of_nat k <= hi -> PP (sA a1 s) mo' (wz y, k)).
  { intros y k Hy Hk. rewrite <- EPOL. eapply (pol_stack' E0 FSB0 HR0 (sA a1 s) mo' AK2 WE ENV0); clear -Hy Hk LOC' AHI; lia. }
  assert (PTHR2 : forall y k, T <= y -> y + Z.of_nat k <= T + 4096 -> PP (sA a1 s) mo' (wz y, k)).
  { intros y k Hy Hk. rewrite <- EPOL. eapply (pol_thread' E0 FSB0 HR0 (sA a1 s) mo' AK2 WE); [exact Hy| exact Hk]. }
  assert (PCTX2 : forall y k, CTX <= y -> y + Z.of_nat k <= CTX + 160 -> PP (sA a1 s) mo' (wz y, k)).
  { intros y k Hy Hk. destruct CTXR as (c0 & cl & RRC & CLO & CHI). rewrite <- EPOL. eapply (pol_resv_range' E0 FSB0 HR0 (sA a1 s) mo' AK2 c0 cl _ _ RRC); clear -Hy Hk CLO CHI; lia. }
  assert (PBLK2 : forall y k, ab <= y -> y + Z.of_nat k <= ab + needed n -> PP (sA a1 s) mo' (wz y, k)).
  { intros y k Hy Hk. destruct k as [|k'].
    - right. split; [unfold acc_nowrap; cbn [fst snd]; rewrite unsigned_lit by (clear -Hy Hk G1 G2 G4 CEILB; lia); clear -Hy Hk G1 G2 G4 CEILB; lia| intros kk Hkk; cbn in Hkk; clear -Hkk; lia].
    - rewrite <- EPOL. unfold ca_span in G2, G4. destruct (from_primary n) eqn:PR.
      + destruct SIDE as (_ & AV & x & Eab & XAL). set (c := malloc_class n) in *.
        assert (Hn' : 0 <= n <= 64512) by (pose proof (proj1 (from_primary_iff n ltac:(clear -Hn; lia)) PR); clear -Hn H; lia).
        pose proof (malloc_class_ok n Hn') as [HCc NEEDc]. fold c in HCc, NEEDc.
        destruct AV as ((k0 & K0 & EK & KU) & _). pose proof WF2 as (_ & [_ WR2] & _). destruct (WR2 c HCc) as ((RA1 & RA2) & _). cbv zeta in RA2. unfold region_of in KU, RA2.
        pose proof (class_size_mod c HCc) as [_ CS32].
        eapply (pol_user E0 FSB0 HR0 (sA a1 s) mo' [] [] AK2 WF2 c); [exact HCc| cbn [aps_alloc sA aps_set_alloc]; clear -Hy EK K0 CS32; nia| cbn [aps_alloc sA aps_set_alloc]; clear -Hk EK K0 KU RA2 NEEDc G4 CS32; nia| clear; lia].
      + destruct SIDE as (r0 & Eab & ESEC & FR).
        pose proof (map_size_facts n) as (MS4 & MSG & MS2). unfold kPageSize in MS4, MSG, MS2, Eab.
        eapply (pol_sec_map E0 FSB0 HR0 (sA a1 s) mo' [] [] AK2 WF2 (mkSec r0 (map_size n) (needed n)));
          [cbn [aps_alloc sA aps_set_alloc]; rewrite ESEC; apply in_app_iff; right; left; reflexivity| cbn [sc_map_beg]; clear -Hy Eab; lia| cbn [sc_map_beg sc_map_size]; clear -Hk Eab MSG; lia]. }
  (* [comment removed for export] *)
  assert (FR2 : frameA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m' junk).
  { unfold frameA in *. eapply (shell_cells_pres E0 ENV0 _ _ _ _ _ _ _ _ _ _ MUW WM2 FW Hwf WF2 AK2); [clear; lia| clear -LOC' LO'; lia| exact FR1]. }
  assert (BOBJ2 : rw_cells bsegs m' B [C8 (wz A); C8 (wz len)]).
  { eapply (shell_cells_pres E0 ENV0 _ _ _ _ _ _ _ _ _ _ MUW WM2 FW Hwf WF2 AK2); [clear -UB; lia| clear -UB LOC' LO'; lia|].
    eapply (rw_cells_agree bsegs); [| exact BOBJ]. cbn. intros x Hx. apply MU1. rewrite wa_unsigned by (clear -Hx UB BA AHI USPR' LEN; unfold zlen in *; lia). cbn. clear -Hx UB. lia. }
  pose proof RT2 as (_ & _ & _ & _ & [TCTX2 TID2]).
  (* [comment removed for export] *)
  assert (WRB : wr_at bsegs m' ab (needed n)).
  { destruct RX2 as (_ & _ & Rrm & _ & Rsec & _). unfold ca_span in G4. destruct (from_primary n) eqn:PR.
    - destruct SIDE as (_ & AV & x & Eab & XAL). set (c := malloc_class n) in *.
      assert (Hn' : 0 <= n <= 64512) by (pose proof (proj1 (from_primary_iff n ltac:(clear -Hn; lia)) PR); clear -Hn H; lia).
      pose proof (malloc_class_ok n Hn') as [HCc NEEDc]. fold c in HCc, NEEDc.
      destruct AV as ((k0 & K0 & EK & KU) & _). pose proof WF2 as (_ & [_ WR2] & _). destruct (WR2 c HCc) as ((RA1 & RA2) & _). cbv zeta in RA2. unfold region_of in KU, RA2.
      pose proof (class_size_mod c HCc) as [_ CS32].
      destruct (Rrm c ltac:(unfold kNumClasses, kLargestClassID in *; clear -HCc; lia)) as [WRU _]. cbv zeta in WRU. unfold region_of in WRU.
      eapply (BF_lkit.wr_at_sub bsegs); [exact WRU| clear -EK K0 CS32; nia| clear -EK K0 KU RA2 G4 CS32; nia].
    - destruct SIDE as (r0 & Eab & ESEC & FR). pose proof (map_size_facts n) as (MS4 & MSG & MS2). unfold kPageSize in MS4, MSG, MS2, Eab.
      destruct Rsec as [_ RS]. destruct (RS (length (as_sec a)) (mkSec r0 (map_size n) (needed n)) ltac:(rewrite ESEC; rewrite nth_error_app2 by (clear; lia); rewrite Nat.sub_diag; reflexivity)) as [_ WRS].
      cbn [sc_map_beg sc_map_size] in WRS. eapply (BF_lkit.wr_at_sub bsegs); [exact WRS| clear -Eab; lia| clear -Eab MSG; lia]. }
  destruct (BF_tkit.wr_at_hdr m' (BF_allocB.cb n ab) ltac:(eapply (BF_lkit.wr_at_sub bsegs); [exact WRB| unfold BF_allocB.cb, BF_allocB.rz; clear -RZ; lia| unfold BF_allocB.cb, BF_allocB.rz; clear -RZ NR1 NR2; unfold needed1 in *; pose proof (rounded_ge n); lia]))
    as (j0 & j1 & j2 & j3 & j4 & HDR).
  (* [comment removed for export] *)
  eapply (rzA_seg_cfg bsegs (aSc (sA a1 s)) (aNc (sA a1 s)) (aEBc (sA a1 s)) (PP (sA a1 s) mo')); [| exact (PP_KIP E0 FSB0 HR0 L0 RES0 EB0 _ _ _ _ ATK2)|].
  { eapply (alloc5_segB (PP (sA a1 s) mo') (wz 0x32cac) sp gp tp u0 u1 u2 a1' a2' a3' b4 b5 b6 b7 s8' u3 u4 u5 u6 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra F fc m' junk
              lo hi n B A len CTX T ab j0 j1 j2 j3 j4);
      [ replace (usp + -128) with (usp - 128) by (clear; lia); exact SK2| exact LOC'| exact LO'| clear -UB BA LEN; unfold zlen in *; lia| exact MI2| exact Hn1| exact HB
      | unfold frameA in FR2; exact FR2| exact HDR| exact TCTX2| exact TID2| exact BOBJ2| exact Thi| exact CTXhi
      | split; [exact G1| split; [clear -G2 G4; lia| clear -G3; Z.div_mod_to_equations; lia]]| clear -G7 G4; lia| clear -G8 G4; lia
      | exact PSTK2| exact PTHR2| exact PCTX2| exact PBLK2]. }
  intros ms2 mo2 POST2 AG2 KP2.
  destruct POST2 as (v0 & v1 & v2 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m2 & b1 & -> & MU3 & WM3 & MI3 & SK3 & HB1 & HB1' & HDR3 & FR3).
  pose proof (magree_frame _ _ AG2) as (Qfds3 & Qvm3 & Qlz3 & Qfs3 & Qh3 & Qtid3 & _).
  pose proof (AKern_frame _ _ _ _ Qvm3 Qlz3 AK2) as AK3.
  pose proof (RTOK_magree E0 FSB0 HR0 L0 RES0 EB0 _ _ _ _ _ TOK2 AG2 (proj1 KP2)) as TOK3.
  (* [comment removed for export] *)
  pose proof (hoareW_arun _ _ _ _ _ _ _ _ _ _ (BF_caframe.ca_op_dk E0 (BF_caframe.dk_of a) n) eq_refl RUNA) as DK1.
  unfold BF_caframe.DK, BF_caframe.dk_of in DK1. injection DK1 as End Eks Efr Enb Esb Estd Ech Edead Etq Egq.
  pose proof (hoareW_arun _ _ _ _ _ _ _ _ _ _ (BF_caframe.ca_op_np E0 a n) eq_refl RUNA) as ENP. cbn beta in ENP.
  pose proof ABUD as (BU1 & BU2 & BU3).
  assert (BPR : 0 <= bprim n <= 1 /\ 10000 * bprim n + 1 <= acharge n /\ ca_cost n + 1 <= acharge n /\ 0 <= ca_cost n).
  { unfold bprim, ca_cost, acharge. destruct (from_primary n) eqn:PR; [unfold kCmPrim; clear; lia|].
    pose proof (cost2_le_acharge n PR) as [C2A C20]. unfold acharge in C2A. rewrite PR in C2A.
    unfold cost2 in *. pose proof (map_size_facts n) as (_ & _ & M2). unfold kPageSize in M2.
    destruct (kBigMapSize <=? map_size n) eqn:B1; destruct (map_size n <? kBigMapSize) eqn:B2;
      first [apply Z.leb_le in B1| apply Z.leb_gt in B1]; first [apply Z.ltb_lt in B2| apply Z.ltb_ge in B2]; try (clear -B1 B2; lia);
      clear -M2 B1 B2; Z.div_mod_to_equations; lia. }
  destruct (ca_dput_nums a1 m' mo' _ _ CAI2 TOK2 ltac:(rewrite ENP; clear -BU1 BPR; lia) ltac:(rewrite ENP, End; clear -BU1 BU3 BPR; lia)) as (NBZ & SBZ & SECB & NDI).
  destruct (ca_dput_statics a1 m' mo' _ _ CAI2 RX2) as (STAT2 & MTX2 & DR2).
  (* [comment removed for export] *)
  assert (GCS : ca_gcost n + DSLACK <= ASLACK).
  { unfold ca_gcost, DSLACK, ASLACK. destruct (from_primary n) eqn:PR; [clear; lia|].
    destruct (needed_sec n Hn PR) as (N1 & N8 & N2 & N40). unfold map_size, round_up, NMAXA, kPageSize in *. clear -N2. Z.div_mod_to_equations. lia. }
  (* [comment removed for export] *)
  pose proof G4 as G4'. unfold ca_span in G4'.
  assert (AG23 : forall z, 0 <= z < 2^64 -> (z < BF_allocB.cb n ab \/ BF_allocB.cb n ab + 8 <= z) -> m2 (wa z) = m' (wa z)).
  { intros z Hz H1. apply MU3. rewrite wa_unsigned by exact Hz. cbn. clear -H1. lia. }
  assert (CBR : ab <= BF_allocB.cb n ab /\ BF_allocB.cb n ab + 16 <= ab + needed n).
  { unfold BF_allocB.cb, BF_allocB.rz. pose proof (rounded_ge n) as (RG1 & _). unfold needed, needed1 in *. clear -RZ NR1 RG1 Hn. destruct (from_primary n); lia. }
  assert (STAT3 : dput_statics m2).
  { apply (dput_statics_agree m' m2 STAT2). intros x Hx. apply AG23; clear -Hx G1 CBR; lia. }
  assert (MTX3 : dput_mutexes m2).
  { apply (dput_mutexes_agree m' m2 MTX2). intros x Hx. apply AG23; clear -Hx G1 CBR; lia. }
  assert (DR3 : DepotR bsegs E0 a1 m2).
  { eapply DepotR_frame; [exact DR2| exact WM3|]. intros x FPx.
    pose proof IMGE as [EI1 EI2]. pose proof ENV0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & IMGR & _).
    destruct (DepotFP_where E0 a1 x FPx) as [(r & Hr & R)|[(b & Hb & R)|(b & Hb & R)]].
    - pose proof (IMGR r ltac:(apply in_app_iff; right; exact Hr)) as X. apply AG23; clear -X R G1 CBR; lia.
    - pose proof (newblk_vs_dblocks a1 ab mo' WF2 AK2 SIDE b _ (or_introl (conj Hb eq_refl))) as X.
      destruct (blocks_sep_of E0 a1 mo' ENV0 WF2 AK2 b _ (or_introl (conj Hb eq_refl))) as (AM & BC & _). unfold app_mem in AM. rewrite ?kHighMemBeg_val, ?kLowAppEnd_val in AM.
      unfold kDepotNodeBlockBytes in *. apply AG23; clear -X R AM BC G1 G4 CBR CEILB; lia.
    - pose proof (newblk_vs_dblocks a1 ab mo' WF2 AK2 SIDE b _ (or_intror (conj Hb eq_refl))) as X.
      destruct (blocks_sep_of E0 a1 mo' ENV0 WF2 AK2 b _ (or_intror (conj Hb eq_refl))) as (AM & BC & _). unfold app_mem in AM. rewrite ?kHighMemBeg_val, ?kLowAppEnd_val in AM.
      unfold kStoreBlockBytes in *. apply AG23; clear -X R AM BC G1 G4 CBR CEILB; lia. }
  assert (AGhi : forall x, usp <= x < 2^47 -> m2 (wa x) = m (wa x)).
  { intros x Hx. rewrite AG23 by (clear -Hx USPR' G2 G4 CBR LOC' LO' CEILB; lia).
    transitivity (m1 (wa x)).
    - apply MUW. rewrite wa_unsigned by (clear -Hx USPR'; lia). eapply outside_of_Forall; [exact FW|]. intros iv Hiv X. cbn beta in Hiv.
      destruct (aw_ok_below E0 ENV0 a a1 mo' lo (usp - 128) iv Hiv Hwf WF2 AK2 ltac:(clear -X; lia)); clear -H X Hx LOC' LO' CEILB; lia.
    - apply MU1. rewrite wa_unsigned by (clear -Hx USPR'; lia). cbn. clear -Hx. lia. }
  assert (TR3 : u64arr bsegs m2 A ws) by (eapply u64arr_agree; [| exact TR]; intros x Hx; apply AGhi; clear -Hx UB BA AHI LEN; unfold zlen in *; lia).
  (* [comment removed for export] *)
  replace (usp + -128) with (usp - 128) by (clear; lia). rewrite <- USP128' || assert (USP128 : bv_unsigned (wz (usp - 128)) = usp - 128) by (apply unsigned_lit; clear -USPR' LO' LOC' CEILB; lia).
  replace (Z_to_bv 64 (usp - 128)) with (wz (usp - 128)) by reflexivity.
  unfold depot_put_srz_stmt in *.
  eapply (DPUT (wz 0x32db8) (wz (usp - 128)) gp tp v0 v1 v2 (wz (Z.b2z (from_primary n))) (wz n) c2 c3 c4 c5 c6 c7
               (wz ab) (wz (needed n)) (wz (BF_allocB.ub n ab)) (wz (BF_allocB.cb n ab)) (wz BF_allocB.INST) (wz B) (wz 0) (wz (BF_allocB.ub n ab + n)) (wz T) (wz 1)
               v3 v4 v5 v6 F fc m2 mo2 (sA a1 s) [] [] lo A len (C - ca_cost n) (C' - ca_gcost n) ws K KN TOK3);
    rewrite ?USP128; cbn [aps_alloc sA aps_set_alloc];
    [ clear -CHG BPR; lia| clear -ASL GCS; lia| exact AK3| exact WF2| exact NBZ| exact SBZ| exact SECB| exact NDI| exact DR3| exact MTX3| exact STAT3| exact MI3
    | exact SK3| exact LOC'| clear -LO; unfold K_ALLOC, K_DEPOT in *; lia| clear -SPA; Z.div_mod_to_equations; lia| clear -UB BA; lia| exact AHI| exact TR3| exact LEN| exact LWS|].
  intros w0 w1 w2 d1 d2 d3 d4 d5 d6 d7 w3 w4 w5 w6 m3 mo3 a2 id DPOST.
  replace (ret_pc (Z_to_bv 64 208312)) with (Z_to_bv 64 208312) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
  apply CONTB. unfold bpost.
  exists w0, w1, w2, d1, d2, d3, d4, d5, d6, d7, w3, w4, w5, w6, m2, m3, mo2, a2, id, b1, j0.
  split; [reflexivity|]. split; [exact MU3|]. split; [exact WM3|]. split; [exact MI3|]. split; [exact HB1|]. split; [exact HB1'|].
  split; [exists j4; exact HDR3|]. split; [exact FR3|]. split; [exact AG2|]. exact DPOST.
Qed.

Ltac numk H N := clear - H N; decompose [and] N; clear N;
      unfold BF_allocC.cb, BF_allocC.ub, BF_allocC.rz, BF_allocC.n8, BF_allocB.cb, BF_allocB.rz, kShadowBase in *; rewrite ?kHighMemBeg_val in *; Z.div_mod_to_equations; lia.

(* [comment removed for export] *)
Lemma stageCD : forall (m1 m' : mem) (mo1 mo' : Model) (a1 : astate) (ab : Z) (junk : list byte) (ms3 : machine_state) (mo3 : Model),
  munch [(usp - 144, usp)] m m1 -> wmono bsegs m m1 -> mem_inv bsegs m1 -> frameA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m1 junk ->
  magree mo mo1 ->
  ca_post E0 FSB0 HR0 L0 RES0 EB0 PL0 a a1 m1 m' mo1 mo' s C C' n lo (usp - 128) ab (wz ab) ->
  bpost m' mo' a1 ab junk ms3 mo3 ->
  realizes_cfg acfg bsegs (mkCfg ms3 mo3) K.
Proof.
  intros until mo3. intros MU1 WM1 MI1 FR1 AG1 POST BP.
  pose proof USPR as USPR'. pose proof LOC as LOC'. aceil. pose proof LO512 as LO'. pose proof IMGE as [EI1 EI2].
  assert (USP128 : bv_unsigned (wz (usp - 128)) = usp - 128) by (apply unsigned_lit; clear -USPR' LO' LOC' CEILB; lia).
  pose proof (magree_frame _ _ AG1) as (Qfds1 & Qvm1 & Qlz1 & Qfs1 & Qh1 & Qtid1 & _).
  destruct POST as (SK2 & WM2 & (W & MUW & FW & FWB) & (fA & orcA & evsA & orcA' & RUNA) & CAI2 & TOK2 & Qfs2 & Qfds2 & Qtid2 & _ & RX2 & (shj & BSH & BSHP) & SIDE).
  pose proof CAI2 as (WF2 & AK2 & RO2 & QB2 & DI2 & MI2 & RT2 & SS2 & CS2).
  destruct (newblk_geom a1 ab WF2 SIDE) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
  pose proof (needed_range n Hn1) as (NR1 & NR2 & NR3). pose proof (rz_size_pos n) as RZ. pose proof (rounded_ge n) as (RG1 & RG2 & RG3).
  assert (SPANPOS : 16 <= ca_span n) by (clear -G4 NR1 Hn; lia).
  assert (CBR : ab <= BF_allocB.cb n ab /\ BF_allocB.cb n ab + 16 <= ab + needed n).
  { unfold BF_allocB.cb, BF_allocB.rz. unfold needed, needed1 in *. clear -RZ NR1 RG1 Hn. destruct (from_primary n); lia. }
  destruct BP as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m2 & m3 & mo2 & a2 & id & b1 & j0 & -> & MU3 & WM3 & MI3 & HB1 & HB1' & [j4 HDR3] & FR3 & AG2 & DPOST).
  pose proof (magree_frame _ _ AG2) as (Qfds3 & Qvm3 & Qlz3 & Qfs3 & Qh3 & Qtid3 & _).
  destruct DPOST as (SK4 & WM4 & MI4 & (Wd & MUd & FWd) & (fD & orcD & evsD & orcD' & RUND) & HID & DR4 & MTX4 & STAT4 & AK4 & TOK4 & Qfs4 & Qfds4 & Qtid4).
  cbn [aps_alloc sA aps_set_alloc] in RUND, DR4, AK4. rewrite sA_sA in TOK4.
  (* [comment removed for export] *)
  pose proof (hoareW_arun _ _ _ _ _ _ _ _ _ _ (BF_caframe.ca_op_dk E0 (BF_caframe.dk_of a) n) eq_refl RUNA) as DK1.
  unfold BF_caframe.DK, BF_caframe.dk_of in DK1. injection DK1 as End Eks Efr Enb Esb Estd Ech Edead Etq Egq.
  pose proof (hoareW_arun _ _ _ _ _ _ _ _ _ _ (BF_caframe.ca_op_np E0 a n) eq_refl RUNA) as ENP. cbn beta in ENP.
  pose proof ABUD as (BU1 & BU2 & BU3).
  assert (BPR : 0 <= bprim n <= 1 /\ 10000 * bprim n + 1 <= acharge n /\ ca_cost n + 1 <= acharge n /\ 0 <= ca_cost n).
  { unfold bprim, ca_cost, acharge. destruct (from_primary n) eqn:PR; [unfold kCmPrim; clear; lia|].
    pose proof (cost2_le_acharge n PR) as [C2A C20]. unfold acharge in C2A. rewrite PR in C2A.
    unfold cost2 in *. pose proof (map_size_facts n) as (_ & _ & M2). unfold kPageSize in M2.
    destruct (kBigMapSize <=? map_size n) eqn:B1; destruct (map_size n <? kBigMapSize) eqn:B2;
      first [apply Z.leb_le in B1| apply Z.leb_gt in B1]; first [apply Z.ltb_lt in B2| apply Z.ltb_ge in B2]; try (clear -B1 B2; lia);
      clear -M2 B1 B2; Z.div_mod_to_equations; lia. }
  destruct (ca_dput_nums a1 m' mo' _ _ CAI2 TOK2 ltac:(rewrite ENP; clear -BU1 BPR; lia) ltac:(rewrite ENP, End; clear -BU1 BU3 BPR; lia)) as (NBZ & SBZ & SECB & NDI).
  pose proof DI2 as (DI21 & DI22 & DI23 & DI24 & DI25 & DI26 & DI27).
  assert (DOK : depot_ok E0 a1 (bst_key len ws)).
  { split.
    - unfold bst_key, zlen. rewrite length_map, length_firstn. clear -LEN LWS. unfold zlen in *. lia.
    - unfold depot_n_ids in *. unfold kDepotNodesPerBlock in DI25. unfold zlen in *. clear -DI25 NBZ. lia. }
  destruct (hoare_arun _ _ _ _ _ _ _ _ _ _ (depot_put_wf E0 [] [] a1 (bst_key len ws) DOK WF2) eq_refl RUND) as (WFd & SAME & _ & NID).
  pose proof SAME as (SRg & SCa & SCi & SCh & STq & SGq & SSe & SPt).
  pose proof (hoareW_arun _ _ _ _ _ _ _ _ _ _ (presW_from fsame (depot_put E0 (bst_key len ws)) a1 fsame_refl (depot_put_W E0 a1 (bst_key len ws))) eq_refl RUND) as [_ DRES].
  assert (RO4 : res_ok a2) by (eapply res_ok_frame; [| | exact RO2]; [intros sc Hsc; rewrite <- SSe; exact Hsc| rewrite DRES; apply incl_refl]).
  (* [comment removed for export] *)
  destruct (RTOK_elim _ _ _ _ _ _ _ _ _ _ TOK4) as (R4 & R4' & ATK4 & HCR4 & HCR4' & GR4 & GD4 & RLE4).
  pose proof (ATOK_ENVOK _ _ _ _ _ _ _ _ _ _ ATK4) as EV4. pose proof (ATOK_KVM _ _ _ _ _ _ _ _ _ _ ATK4) as KV4. cbn [aps_alloc sA aps_set_alloc] in KV4.
  assert (PSTK4 : forall y k, lo <= y -> y + Z.of_nat k <= hi -> PP (sA a2 s) mo3 (wz y, k)).
  { intros y k Hy Hk. rewrite <- EPOL. eapply (pol_stack' E0 FSB0 HR0 (sA a2 s) mo3 AK4 WE ENV0); clear -Hy Hk LOC' AHI; lia. }
  assert (PIMG4 : forall y k, 0xa5000 <= y -> y + Z.of_nat k <= 0x603000 -> PP (sA a2 s) mo3 (wz y, k)).
  { intros y k Hy Hk. rewrite <- EPOL. eapply (pol_img' E0 FSB0 HR0 (sA a2 s) mo3 AK4 WE EV4 ENV0); [clear -Hy; lia| exact Hk]. }
  assert (PTHR4 : forall y k, T <= y -> y + Z.of_nat k <= T + 4096 -> PP (sA a2 s) mo3 (wz y, k)).
  { intros y k Hy Hk. rewrite <- EPOL. eapply (pol_thread' E0 FSB0 HR0 (sA a2 s) mo3 AK4 WE); [exact Hy| exact Hk]. }
  assert (PCTX4 : forall y k, CTX <= y -> y + Z.of_nat k <= CTX + 160 -> PP (sA a2 s) mo3 (wz y, k)).
  { intros y k Hy Hk. destruct CTXR as (c0 & cl & RRC & CLO & CHI). rewrite <- EPOL. eapply (pol_resv_range' E0 FSB0 HR0 (sA a2 s) mo3 AK4 c0 cl _ _ RRC); clear -Hy Hk CLO CHI; lia. }
  (* [comment removed for export] *)
  assert (SIDE4 : if from_primary n
      then as_cache_inited a2 = true /\ avail E0 [] a2 (malloc_class n) ab /\ exists x, ab = chunk_of_compact SB (malloc_class n) x /\ (16 * x) mod class_size (malloc_class n) = 0
      else exists r0, ab = r0 + kPageSize /\ as_sec a2 = as_sec a ++ [mkSec r0 (map_size n) (needed n)] /\ sec_fresh E0 a r0 (map_size n)).
  { destruct (from_primary n).
    - destruct SIDE as (CI & AV & X). split; [rewrite SCi; exact CI|]. split; [| exact X]. eapply avail_frame; [exact SRg| exact SCa| exact SCh| exact STq| exact SGq| exact AV].
    - destruct SIDE as (r0 & E1 & E2 & E3). exists r0. rewrite SSe. auto. }
  assert (PBLK4 : forall y k, ab <= y -> y + Z.of_nat k <= ab + needed n -> PP (sA a2 s) mo3 (wz y, k)).
  { intros y k Hy Hk. destruct k as [|k'].
    - right. split; [unfold acc_nowrap; cbn [fst snd]; rewrite unsigned_lit by (clear -Hy Hk G1 G2 G4 CEILB; lia); clear -Hy Hk G1 G2 G4 CEILB; lia| intros kk Hkk; cbn in Hkk; clear -Hkk; lia].
    - rewrite <- EPOL. pose proof G4 as G4'. unfold ca_span in G4'. destruct (from_primary n) eqn:PR.
      + destruct SIDE4 as (_ & AV & x & Eab & XAL). set (c := malloc_class n) in *.
        assert (Hn' : 0 <= n <= 64512) by (pose proof (proj1 (from_primary_iff n ltac:(clear -Hn; lia)) PR); clear -Hn H; lia).
        pose proof (malloc_class_ok n Hn') as [HCc NEEDc]. fold c in HCc, NEEDc.
        destruct AV as ((k0 & K0 & EK & KU) & _). pose proof WFd as (_ & [_ WR2] & _). destruct (WR2 c HCc) as ((RA1 & RA2) & _). cbv zeta in RA2. unfold region_of in KU, RA2.
        pose proof (class_size_mod c HCc) as [_ CS32].
        eapply (pol_user E0 FSB0 HR0 (sA a2 s) mo3 [] [] AK4 WFd c); [exact HCc| cbn [aps_alloc sA aps_set_alloc]; clear -Hy EK K0 CS32; nia| cbn [aps_alloc sA aps_set_alloc]; clear -Hk EK K0 KU RA2 G4' CS32; nia| clear; lia].
      + destruct SIDE4 as (r0 & Eab & ESEC & FR).
        pose proof (map_size_facts n) as (MS4 & MSG & MS2). unfold kPageSize in MS4, MSG, MS2, Eab.
        eapply (pol_sec_map E0 FSB0 HR0 (sA a2 s) mo3 [] [] AK4 WFd (mkSec r0 (map_size n) (needed n)));
          [cbn [aps_alloc sA aps_set_alloc]; rewrite ESEC; apply in_app_iff; right; left; reflexivity| cbn [sc_map_beg]; clear -Hy Eab; lia| cbn [sc_map_beg sc_map_size]; clear -Hk Eab MSG; lia]. }
  assert (PBSH4 : forall y k, kShadowBase + ab / 8 <= y -> y + Z.of_nat k <= kShadowBase + (ab + ca_span n) / 8 -> PP (sA a2 s) mo3 (wz y, k)).
  { intros y k Hy Hk. rewrite <- EPOL. unfold ca_span in Hk. destruct (from_primary n) eqn:PR.
    + destruct SIDE4 as (_ & AV & x & Eab & XAL). set (c := malloc_class n) in *.
      assert (Hn' : 0 <= n <= 64512) by (pose proof (proj1 (from_primary_iff n ltac:(clear -Hn; lia)) PR); clear -Hn H; lia).
      pose proof (malloc_class_ok n Hn') as [HCc NEEDc]. fold c in HCc, NEEDc.
      destruct AV as (CARVED & _). pose proof WFd as (_ & WR2 & _). pose proof (carved_in_space E0 a2 c ab HCc WR2 CARVED) as [I1 I2].
      eapply (pol_space_shadow E0 FSB0 HR0 (sA a2 s) mo3 [] [] WFd); cbn [aps_alloc sA aps_set_alloc]; rewrite ?A_SB_val; unfold kShadowBase, kRegionSize, kSpaceSize in *;
        [clear -Hy I1; Z.div_mod_to_equations; lia| clear -Hk I2; Z.div_mod_to_equations; lia].
    + destruct SIDE4 as (r0 & Eab & ESEC & FR). pose proof (map_size_facts n) as (MS4 & MSG & MS2). unfold kPageSize in MS4, MSG, MS2, Eab.
      assert (RU : round_up (needed n) 4096 + 4096 = map_size n) by reflexivity. unfold kPageSize in Hk.
      eapply (pol_sec_shadow E0 FSB0 HR0 (sA a2 s) mo3 [] [] WFd (mkSec r0 (map_size n) (needed n))); cbn [aps_alloc sA aps_set_alloc sc_map_beg sc_map_size]; rewrite ?A_SB_val;
        [exact RO4
        | rewrite ESEC; apply in_app_iff; right; left; reflexivity
        | unfold kShadowBase in *; clear -Hy Eab; Z.div_mod_to_equations; lia
        | unfold kShadowBase in *; clear -Hk Eab RU; Z.div_mod_to_equations; lia]. }
  (* [comment removed for export] *)
  assert (AG23 : forall z, 0 <= z < 2^64 -> (z < BF_allocB.cb n ab \/ BF_allocB.cb n ab + 8 <= z) -> m2 (wa z) = m' (wa z)).
  { intros z Hz H1. apply MU3. rewrite wa_unsigned by exact Hz. cbn. clear -H1. lia. }
  assert (AG34d : forall z, 0 <= z < 2^64 -> (z + 1 <= lo \/ usp - 128 <= z) -> ~ DepotFPd E0 a2 z -> m3 (wa z) = m2 (wa z)).
  { intros z Z0 Z1 Z2. apply MUd. rewrite wa_unsigned by exact Z0. eapply outside_of_Forall; [exact FWd|]. intros iv Hiv C0. cbn beta in Hiv.
    pose proof (dput_w_ok_pt E0 _ _ _ _ Hiv) as X. destruct X as [X|X]; [clear -X Z1 C0; lia|]. apply Z2. apply X. exact C0. }
  assert (NDFPlo : forall z, z < 0x180488 \/ (0x5d04a8 <= z < 0x603000) -> ~ DepotFPd E0 a2 z).
  { intros z Hz Dz. destruct (BF_deallocT1.dfp_cases E0 PL0 ENV0 PL0OK a2 mo3 z IC0 AK4 WFd EI1 EI2 Dz) as [ST|(b & bl & R & B0 & _)]; [clear -Hz ST; lia| clear -Hz R B0; lia]. }
  assert (NDFPblk : forall z, ab <= z < ab + ca_span n -> ~ DepotFPd E0 a2 z).
  { intros z Hz Dz. destruct Dz as [ST|[(b & Hb & R)|(b & Hb & R)]].
    - destruct ST as (r & Hr & R). rewrite IC0 in Hr. cbn [aic_theDepot aic_stackStore both_ic] in Hr. unfold kDepotStaticBytes, kStoreStaticBytes in Hr.
      destruct Hr as [<-|[<-|[]]]; cbn [fst snd] in R; clear -R Hz G1; lia.
    - pose proof (newblk_vs_dblocks a2 ab mo3 WFd AK4 SIDE4 b _ (or_introl (conj Hb eq_refl))) as X. unfold kDepotNodeBlockBytes in *. clear -X R Hz. lia.
    - pose proof (newblk_vs_dblocks a2 ab mo3 WFd AK4 SIDE4 b _ (or_intror (conj Hb eq_refl))) as X. unfold kStoreBlockBytes in *. clear -X R Hz. lia. }
  assert (NDFPsh : forall z, kShadowBase + ab / 8 <= z < kShadowBase + (ab + ca_span n) / 8 -> ~ DepotFPd E0 a2 z).
  { intros z Hz Dz. unfold kShadowBase in Hz. destruct (BF_deallocT1.dfp_cases E0 PL0 ENV0 PL0OK a2 mo3 z IC0 AK4 WFd EI1 EI2 Dz) as [ST|(b & bl & R & B0 & B2 & BB & _)]; [clear -Hz ST G1; lia|].
    rewrite ?kHighMemBeg_val, ?kLowAppEnd_val in BB. clear -Hz R B0 B2 BB G1 G2 CEILB. lia. }
  assert (NDFPhi : forall z, alloc_ceiling <= z -> ~ DepotFPd E0 a2 z).
  { intros z Hz Dz. destruct (BF_deallocT1.dfp_cases E0 PL0 ENV0 PL0OK a2 mo3 z IC0 AK4 WFd EI1 EI2 Dz) as [ST|(b & bl & R & B0 & B2 & _)]; [clear -Hz ST CEILB; lia| clear -Hz R B2; lia]. }
  assert (AGimg : forall z, 0xa5000 <= z < 0x180488 -> m3 (wa z) = m' (wa z)).
  { intros z Hz. rewrite AG34d; [| clear -Hz; lia| clear -Hz LOC' CEILB; lia| apply NDFPlo; clear -Hz; lia]. apply AG23; clear -Hz G1 CBR; lia. }
  assert (AGblk : forall z, ab <= z < ab + ca_span n -> (z < BF_allocB.cb n ab \/ BF_allocB.cb n ab + 8 <= z) -> m3 (wa z) = m' (wa z)).
  { intros z Hz H1. rewrite AG34d; [| clear -Hz G1 G2 CEILB; lia| clear -Hz G2 LOC'; lia| apply NDFPblk; exact Hz]. apply AG23; [clear -Hz G1 G2 CEILB; lia| exact H1]. }
  assert (AGsh : forall z, kShadowBase + ab / 8 <= z < kShadowBase + (ab + ca_span n) / 8 -> m3 (wa z) = m' (wa z)).
  { intros z Hz. pose proof Hz as Hz'. unfold kShadowBase in Hz'. rewrite AG34d; [| clear -Hz' G1 G2 CEILB; lia| clear -Hz' G1 G2 LOC' CEILB; lia| apply NDFPsh; exact Hz].
    apply AG23; [clear -Hz' G1 G2 CEILB; lia|]. rewrite ?kHighMemBeg_val in G6. unfold BF_allocB.cb, BF_allocB.rz. clear -Hz' G1 G2 G4 G6 RZ NR1 CEILB. Z.div_mod_to_equations. lia. }
  assert (AGhi : forall z, usp - 128 <= z < 2^47 -> m3 (wa z) = m2 (wa z)).
  { intros z Hz. apply AG34d; [clear -Hz USPR' LO' LOC' CEILB; lia| clear -Hz; lia| apply NDFPhi; clear -Hz LO' LOC'; lia]. }
  (* [comment removed for export] *)
  assert (HDR4 : rw_cells bsegs m3 (BF_allocB.cb n ab) [C1 j0; C1 (Z_to_bv 8 b1); C2 (wz 0); C4 (wz n); C8 j4]).
  { eapply (rw_cells_agree bsegs); [| exact HDR3]. cbn. intros x Hx. apply AG34d; [clear -Hx G1 G2 G4 CBR CEILB; lia| clear -Hx G2 G4 CBR LOC'; lia| apply NDFPblk; clear -Hx G4 CBR; lia]. }
  assert (FR4 : frameA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m3 junk).
  { unfold frameA in *. eapply (rw_cells_agree bsegs); [| exact FR3]. cbn. intros x Hx. apply AGhi. clear -Hx UB BA AHI LEN USPR'; unfold zlen in *; lia. }
  (* [comment removed for export] *)
  pose proof RT2 as (_ & [tX XS] & _ & AMS2 & _).
  assert (US : unreg_statics m') by (unfold exit_statics in XS; decompose [and] XS; assumption). unreg_statics_open US.
  pose proof RX2 as (Rins & _ & Rrm & _ & Rsec & _ & _ & _ & Rglob & _).
  pose proof Rglob as (Gfl & Gfu & Gth & Gdd & Gsh & Ghe & Gcp & Gai & Gmcs & Gps & Gdy & Ganc & Grm & _).
  rewrite IC0 in Ghe, Grm. cbn [aic_kHighMemEnd aic_REAL_memcpy_var aic_musl_memcpy aic_musl_memset both_ic] in Ghe, Grm.
  assert (PG2 : poison_globals m').
  { unfold poison_globals. split.
    { pose proof (rwc_join_at bsegs m' _ _ _ _ GHE GRSP ltac:(reflexivity)) as X4.
      pose proof (rwc_join_at bsegs m' _ _ _ _ GME X4 ltac:(reflexivity)) as X3.
      pose proof (rwc_join_at bsegs m' _ _ _ _ GMB X3 ltac:(reflexivity)) as X2.
      pose proof (rwc_join_at bsegs m' _ _ _ _ GSBP X2 ltac:(reflexivity)) as X1. cbn [app] in X1. exact X1. }
    split; [exact GCF|]. split; [exact GSB|]. split; [exact Ghe|]. split; [exact Grm|]. split; [exact GCPM| exact GTHR]. }
  assert (PG4 : poison_globals m3) by (apply (poison_globals_agree m' m3 PG2); intros z Hz; apply AGimg; clear -Hz; lia).
  pose proof Rins as (I1 & I2 & _). unfold ae_instance in I1, I2. rewrite IC0 in I1, I2. cbn [aic_instance both_ic kInsSpaceBeg kInsSecondary Z.add] in I1, I2.
  assert (ISB4 : rw_cells bsegs m3 700280 [C8 (wz SB)]).
  { pose proof (BF_depot3.rw_cells_app_split bsegs m' _ [C8 (wz SB)] _ I1) as [X _]. eapply (rw_cells_agree bsegs); [| exact X]. cbn. intros z Hz. apply AGimg. clear -Hz. lia. }
  assert (IPS4 : rw_cells bsegs m3 700312 [C8 (wz 4096)]).
  { pose proof (BF_depot3.rw_cells_app_split bsegs m' _ [C8 (wz kPageSize)] _ I2) as [X _]. unfold kPageSize in X. eapply (rw_cells_agree bsegs); [| exact X]. cbn. intros z Hz. apply AGimg. clear -Hz. lia. }
  (* [comment removed for export] *)
  unfold BF_allocB.ub, BF_allocB.cb, BF_allocB.rz. fold (BF_allocC.rz n). fold (BF_allocC.cb n ab). fold (BF_allocC.ub n ab).
  change A_INST with BF_allocC.INST.
  set (Q4 := fun ms => exists m4, segC5_regs sp gp tp F fc n B T ab ms m4 /\ munch [(usp + -128 - 64, usp + -128); (BF_allocC.cb n ab + 8, BF_allocC.cb n ab + 16); (kShadowBase + ab / 8, kShadowBase + ab / 8 + BF_allocC.rz n / 8); (kShadowBase + (BF_allocC.ub n ab + rounded n) / 8, kShadowBase + (ab + ca_span n) / 8)] m3 m4 /\ wmono bsegs m3 m4 /\ mem_inv bsegs m4 /\ stk bsegs m4 lo (usp + -128)
                      /\ rw_cells bsegs m4 (BF_allocC.cb n ab) [C1 j0; C1 (Z_to_bv 8 b1); C2 (wz 0); C4 (wz n); C8 (wz id)] /\ poison_globals m4
                      /\ (from_primary n = false ->
                            rw_cells bsegs m4 (kShadowBase + ab / 8) [CB (Z.to_nat (BF_allocC.rz n / 8)) (repeat (Z_to_bv 8 250) (Z.to_nat (BF_allocC.rz n / 8)))]
                         /\ rw_cells bsegs m4 (kShadowBase + (BF_allocC.ub n ab + rounded n) / 8) [CB (Z.to_nat (RL n ab / 8)) (repeat (Z_to_bv 8 250) (Z.to_nat (RL n ab / 8)))])
                      /\ (from_primary n = true -> munch [(BF_allocC.cb n ab + 8, BF_allocC.cb n ab + 16)] m3 m4)).
  eapply (rzA_seg_cfg bsegs (aSc (sA a2 s)) (aNc (sA a2 s)) (aEBc (sA a2 s)) (PP (sA a2 s) mo3) Q4); [| exact (PP_KIP E0 FSB0 HR0 L0 RES0 EB0 _ _ _ _ ATK4)|].
  { pose proof G4 as G4'. unfold ca_span in G4'. destruct (Sumbool.sumbool_of_bool (from_primary n)) as [PR|PR]; rewrite PR in G4'.
    - (* [comment removed for export] *)
      pose proof (BSHP PR) as ->.
      assert (CS8 : 4 <= ca_span n / 8 /\ ca_span n = 8 * (ca_span n / 8)).
      { unfold ca_span. rewrite PR. set (c := malloc_class n).
        assert (Hn' : 0 <= n <= 64512) by (pose proof (proj1 (from_primary_iff n ltac:(clear -Hn; lia)) PR); clear -Hn H; lia).
        pose proof (malloc_class_ok n Hn') as [HCc _]. pose proof (class_size_mod c HCc) as [CSM CS32]. clear -CSM CS32. Z.div_mod_to_equations. lia. }
      assert (BSH1 : rw_cells bsegs m3 (kShadowBase + ab / 8) [C1 (Z_to_bv 8 250)]).
      { pose proof (rw_cells_split_CB bsegs m' (kShadowBase + ab / 8) [] (Z.to_nat (ca_span n / 8)) (repeat (Z_to_bv 8 kAsanHeapLeftRedzoneMagic) (Z.to_nat (ca_span n / 8))) []
                      [1%nat; (Z.to_nat (ca_span n / 8) - 1)%nat] BSH ltac:(cbn [sum_nat]; clear -CS8; lia)) as X.
        cbn [app mk_CB_cells] in X. replace (take 1 (repeat (Z_to_bv 8 kAsanHeapLeftRedzoneMagic) (Z.to_nat (ca_span n / 8)))) with [Z_to_bv 8 250] in X
          by (destruct (Z.to_nat (ca_span n / 8)) eqn:EE; [clear -EE CS8; lia| reflexivity]).
        pose proof (BF_depot3.rw_cells_app_split bsegs m' _ [CB 1 [Z_to_bv 8 250]] _ X) as [X1 _].
        eapply (rw_cells_agree bsegs); [| eapply (BF_lkit.rw_cells_reshape bsegs m' _ [CB 1 [Z_to_bv 8 250]]); [cbn; tauto| reflexivity| exact X1]]. cbn. intros z Hz. apply AGsh. clear -Hz CS8. lia. }
      eapply evtA_mono.
      { eapply (alloc5_segCp (PP (sA a2 s) mo3) (wz 0x32db8) sp gp tp v0 v1 v2 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 F fc m3 lo n B T ab id b1 (ca_span n) j0 j4);
          [ replace (usp + -128) with (usp - 128) by (clear; lia); exact SK4| exact LOC'| exact MI4| exact Hn1| exact HID| exact HB1| exact HDR4| exact PG4
          | split; [exact G1| split; [exact G2| clear -G3; Z.div_mod_to_equations; lia]]| exact G4| rewrite kHighMemBeg_val; rewrite ?kHighMemBeg_val in G6; exact G6
          | exact PIMG4| exact PBLK4| exact PBSH4| exact PR| exact BSH1]. }
      intros ms' (m4 & RG4 & MU5 & WM5 & MI5 & SK5 & HD5). exists m4. split; [exact RG4|]. split; [| split; [exact WM5| split; [exact MI5| split; [exact SK5| split; [exact HD5| split; [| split; [intros X; rewrite PR in X; discriminate| intros _; exact MU5]]]]]]].
      + eapply munch_weaken; [| exact MU5]. intros y Hy. unfold WCs in Hy. cbn in Hy |- *. clear -Hy. tauto.
      + apply (poison_globals_agree m3 m4 PG4). intros z Hz. apply MU5. rewrite wa_unsigned by (clear -Hz; lia). cbn. unfold BF_allocC.cb, BF_allocC.rz. clear -Hz G1 RZ. lia.
    - (* [comment removed for export] *)
      rewrite PR in SIDE4. destruct SIDE4 as (r0 & Eab & ESEC & FR). pose proof FR as (F1 & F2 & F3 & F4 & F5 & F6).
      pose proof (map_size_facts n) as (MS4 & MSG & MS2). unfold kPageSize in MS4, MSG, MS2, Eab, F1. unfold kSpaceSize in F4.
      destruct (needed_sec n Hn PR) as (N1 & N8 & N2 & N40).
      assert (RU : round_up (needed n) 4096 + 4096 = map_size n) by reflexivity.
      pose proof WE as WE'. wfe_open WE'. rewrite ?kHighMemBeg_val in WE2. unfold kSpaceSize in WE4.
      pose proof (F6 _ WE29) as XIMG. cbn [fst snd] in XIMG. rewrite EI1 in XIMG.
      assert (R0LO : 0x603000 <= r0) by (unfold app_mem in F2; rewrite ?kLowAppEnd_val, ?kHighMemBeg_val in F2; clear -F2 XIMG EI2 MSG N1; lia).
      destruct (fp_cases n) as [[X _]|(_ & EN & _)]; [rewrite PR in X; discriminate|].
      assert (RLnn : 0 <= RL n ab /\ RL n ab mod 8 = 0 /\ BF_allocC.rz n + rounded n + RL n ab = ALSZ n).
      { unfold RL, ALSZ, BF_allocC.ub, BF_allocC.rz. rewrite EN. unfold needed1. unfold round_up. pose proof (rz_size_mod16 n) as RZM.
        unfold BF_allocB.rz, BF_allocC.rz, BF_allocD.rz in *.
        clear -RZ RG1 RG2 RG3 RZM. Z.div_mod_to_equations. lia. }
      (* [comment removed for export] *)
      destruct Rsec as [_ RS]. destruct (RS (length (as_sec a)) (mkSec r0 (map_size n) (needed n)) ltac:(rewrite <- SSe, ESEC; rewrite nth_error_app2 by (clear; lia); rewrite Nat.sub_diag; reflexivity)) as [SH32 _].
      cbn [sc_map_beg sc_map_size sc_needed] in SH32.
      assert (AGhdr : forall z, r0 <= z < r0 + 32 -> m3 (wa z) = m' (wa z)).
      { intros z Hz. rewrite AG34d; [| clear -Hz R0LO Eab G2 SPANPOS CEILB; lia| clear -Hz R0LO Eab G2 SPANPOS LOC'; lia|].
        - apply AG23; [clear -Hz R0LO Eab G2 SPANPOS CEILB; lia| clear -Hz Eab CBR; lia].
        - intros Dz. destruct (BF_deallocT1.dfp_cases E0 PL0 ENV0 PL0OK a2 mo3 z IC0 AK4 WFd EI1 EI2 Dz) as [ST|(b & bl & R & B0 & B2 & BB & B3 & B4 & _)]; [clear -Hz ST R0LO; lia|].
          pose proof (B4 (mkSec r0 (map_size n) (needed n)) ltac:(rewrite ESEC; apply in_app_iff; right; left; reflexivity)) as X. cbn [sc_map_beg sc_map_size] in X.
          clear -Hz R X MS2. lia. }
      assert (SHDR4 : rw_cells bsegs m3 (ab - 4096 + 16) [C8 (wz (needed n))]).
      { pose proof (BF_depot3.rw_cells_app_split bsegs m' _ [C8 (zw r0); C8 (zw (map_size n))] [C8 (zw (needed n)); C8 (zw (Z.of_nat (length (as_sec a))))] SH32) as [_ X].
        pose proof (BF_depot3.rw_cells_app_split bsegs m' _ [C8 (zw (needed n))] [C8 (zw (Z.of_nat (length (as_sec a))))] X) as [X1 _]. cbn [cells_size csize Nat.add] in X1.
        replace (ab - 4096 + 16) with (r0 + Z.of_nat 16) by (clear -Eab; lia). eapply (rw_cells_agree bsegs); [| exact X1]. cbn. intros z Hz. apply AGhdr. clear -Hz. lia. }
      (* [comment removed for export] *)
      assert (SPAN8 : ca_span n = 8 * (ca_span n / 8) /\ ca_span n = ALSZ n) by (unfold ca_span, ALSZ; rewrite PR; unfold kPageSize; split; [clear -G5 PR; unfold ca_span in G5; rewrite PR in G5; unfold kPageSize in G5; Z.div_mod_to_equations; lia| reflexivity]).
      pose proof RZ as RZ'. pose proof (rz_size_mod16 n) as RZM.
      assert (RZ8 : BF_allocC.rz n = 8 * (BF_allocC.rz n / 8) /\ rounded n = 8 * (rounded n / 8)) by (unfold BF_allocC.rz; clear -RZM RG3; Z.div_mod_to_equations; lia).
      assert (SUMN : sum_nat [Z.to_nat (BF_allocC.rz n / 8); Z.to_nat (rounded n / 8); Z.to_nat (RL n ab / 8)] = Z.to_nat (ca_span n / 8)).
      { cbn [sum_nat]. destruct SPAN8 as [S8 S9]. rewrite S9 in *. unfold BF_allocC.rz in *. clear -S8 RLnn RZ8 RZ' RG1. Z.div_mod_to_equations. lia. }
      pose proof (rw_cells_split_CB bsegs m' (kShadowBase + ab / 8) [] (Z.to_nat (ca_span n / 8)) shj []
                    [Z.to_nat (BF_allocC.rz n / 8); Z.to_nat (rounded n / 8); Z.to_nat (RL n ab / 8)] BSH SUMN) as X.
      cbn [app mk_CB_cells] in X.
      pose proof (BF_depot3.rw_cells_app_split bsegs m' _ [CB (Z.to_nat (BF_allocC.rz n / 8)) (take (Z.to_nat (BF_allocC.rz n / 8)) shj)] _ X) as [XL X'].
      pose proof (BF_depot3.rw_cells_app_split bsegs m' _ [CB (Z.to_nat (rounded n / 8)) _] _ X') as [XM X'']. clear X X'.
      pose proof (BF_depot3.rw_cells_app_split bsegs m' _ [CB (Z.to_nat (RL n ab / 8)) _] _ X'') as [XR _]. clear X''.
      cbn [cells_size csize] in XM, XR. repeat rewrite Nat.add_0_r in XM. repeat rewrite Nat.add_0_r in XR.
      assert (SHL4 : rw_cells bsegs m3 (kShadowBase + ab / 8) [CB (Z.to_nat (BF_allocC.rz n / 8)) (take (Z.to_nat (BF_allocC.rz n / 8)) shj)]).
      { eapply (rw_cells_agree bsegs); [| exact XL]. cbn. intros z Hz. apply AGsh. destruct SPAN8 as [S8 S9]. rewrite S9 in *. unfold BF_allocC.rz in *. clear -Hz RZ8 RZ' RLnn RG1 S8. repeat rewrite Nat.add_0_r in Hz. rewrite Z2Nat.id in Hz by lia. lia. }
      assert (SHR4 : rw_cells bsegs m3 (kShadowBase + (BF_allocC.ub n ab + rounded n) / 8)
                       [CB (Z.to_nat (RL n ab / 8)) (take (Z.to_nat (RL n ab / 8)) (drop (Z.to_nat (rounded n / 8)) (drop (Z.to_nat (BF_allocC.rz n / 8)) shj)))]).
      { replace (kShadowBase + (BF_allocC.ub n ab + rounded n) / 8) with (kShadowBase + ab / 8 + Z.of_nat (Z.to_nat (BF_allocC.rz n / 8)) + Z.of_nat (Z.to_nat (rounded n / 8)))
          by (unfold BF_allocC.ub; unfold BF_allocC.rz in *; clear -RZ8 RZ' RG1 G3; rewrite !Z2Nat.id by lia; Z.div_mod_to_equations; lia).
        eapply (rw_cells_agree bsegs); [| exact XR]. cbn. intros z Hz. apply AGsh. destruct SPAN8 as [S8 S9]. rewrite S9 in *. unfold BF_allocC.rz, BF_allocC.ub in *; clear -Hz RZ8 RZ' RLnn RG1 S8. repeat rewrite Nat.add_0_r in Hz. rewrite !Z2Nat.id in Hz by lia. lia. }
      eapply evtA_mono.
      { eapply (alloc5_segCs (PP (sA a2 s) mo3) (wz 0x32db8) sp gp tp v0 v1 v2 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 F fc m3 lo hi n B T ab id b1 SB (ca_span n) j0 j4);
          [ replace (usp + -128) with (usp - 128) by (clear; lia); exact SK4| exact LOC'| exact LO'| clear -UB BA LEN; unfold zlen in *; lia| exact AHI| exact MI4| exact Hn1| exact HID| exact HB1
          | exact HDR4| exact PG4| split; [exact G1| split; [exact G2| clear -G3; Z.div_mod_to_equations; lia]]| exact G4| rewrite kHighMemBeg_val; rewrite ?kHighMemBeg_val in G6; exact G6
          | exact PSTK4| exact PIMG4| exact PBLK4| exact PBSH4| exact PR| exact ISB4| exact IPS4| exact SHDR4| exact SHL4| exact SHR4
          | clear -Eab F1; Z.div_mod_to_equations; lia| destruct SPAN8 as [_ S9]; rewrite <- S9; clear; lia
          | clear -WE2 WE3 WE4 WE5; lia| clear -F4 Eab RU; unfold ALSZ; lia|].
        intros y k Hy Hk. rewrite <- EPOL.
        eapply (pol_sec_map E0 FSB0 HR0 (sA a2 s) mo3 [] [] AK4 WFd (mkSec r0 (map_size n) (needed n)));
          [cbn [aps_alloc sA aps_set_alloc]; rewrite ESEC; apply in_app_iff; right; left; reflexivity| cbn [sc_map_beg]; clear -Hy Eab; lia| cbn [sc_map_beg sc_map_size]; clear -Hk Eab MS2; lia]. }
      intros ms' (m4 & RG4 & MU5 & WM5 & MI5 & SK5 & HD5 & SL5 & SR5 & PG5). exists m4. split; [exact RG4|]. split; [eapply munch_weaken; [| exact MU5]; intros y Hy; unfold WCs in Hy; cbn in Hy |- *; unfold BF_allocC.ub, BF_allocC.rz in *; clear -Hy RLnn SPAN8; Z.div_mod_to_equations; lia|]. split; [exact WM5|]. split; [exact MI5|]. split; [exact SK5|].
      split; [exact HD5|]. split; [exact PG5|]. split; [intros _; split; [exact SL5| exact SR5]| intros X; rewrite PR in X; discriminate]. }
  (* [comment removed for export] *)
  intros ms4 mo4 (m4 & RG4 & MU5 & WM5 & MI5 & SK5 & HD5 & PG5 & SHX5 & MU5p) AG4 KP4.
  pose proof (magree_frame _ _ AG4) as (Qfds5 & Qvm5 & Qlz5 & Qfs5 & Qh5 & Qtid5 & _).
  pose proof (AKern_frame _ _ _ _ Qvm5 Qlz5 AK4) as AK5.
  pose proof (RTOK_magree E0 FSB0 HR0 L0 RES0 EB0 _ _ _ _ _ TOK4 AG4 (proj1 KP4)) as TOK5.
  assert (AG45 : forall z, 0 <= z < 2^64 -> (z < usp - 128 - 64 \/ usp - 128 <= z) -> (z < BF_allocC.cb n ab + 8 \/ BF_allocC.cb n ab + 16 <= z) ->
                 (z < kShadowBase + ab / 8 \/ kShadowBase + ab / 8 + BF_allocC.rz n / 8 <= z) ->
                 (z < kShadowBase + (BF_allocC.ub n ab + rounded n) / 8 \/ kShadowBase + (ab + ca_span n) / 8 <= z) -> m4 (wa z) = m3 (wa z)).
  { intros z Hz H1 H2 H3 H4. apply MU5. rewrite wa_unsigned by exact Hz. cbn. clear -H1 H2 H3 H4. lia. }
  (* [comment removed for export] *)
  pose proof G5 as SP8. assert (SP8' : ca_span n = 8 * (ca_span n / 8)) by (clear -SP8; Z.div_mod_to_equations; lia). clear SP8.
  pose proof (rz_size_mod16 n) as RZM.
  assert (RZ8 : BF_allocC.rz n = 8 * (BF_allocC.rz n / 8) /\ rounded n = 8 * (rounded n / 8)) by (unfold BF_allocC.rz; clear -RZM RG3; Z.div_mod_to_equations; lia).
  assert (N8R : 0 <= BF_allocC.n8 n /\ 8 * BF_allocC.n8 n <= n /\ n < 8 * BF_allocC.n8 n + 8 /\ 8 * BF_allocC.n8 n <= rounded n) by (unfold BF_allocC.n8; clear -Hn RG1; Z.div_mod_to_equations; lia).
  assert (USPAN : BF_allocC.rz n + rounded n <= ca_span n).
  { pose proof G4 as X. unfold BF_allocC.rz. unfold needed, needed1 in X. clear -X RZ. destruct (from_primary n); lia. }
  assert (SUMU : sum_nat [Z.to_nat (BF_allocC.rz n / 8); Z.to_nat (BF_allocC.n8 n); (Z.to_nat (ca_span n / 8) - Z.to_nat (BF_allocC.rz n / 8) - Z.to_nat (BF_allocC.n8 n))%nat] = Z.to_nat (ca_span n / 8)).
  { cbn [sum_nat]. unfold BF_allocC.rz in *. clear -SP8' RZ8 RZ N8R USPAN. Z.div_mod_to_equations. lia. }
  pose proof (rw_cells_split_CB bsegs m' (kShadowBase + ab / 8) [] (Z.to_nat (ca_span n / 8)) shj [] _ BSH SUMU) as XU. cbn [app mk_CB_cells] in XU.
  pose proof (BF_depot3.rw_cells_app_split bsegs m' _ [CB (Z.to_nat (BF_allocC.rz n / 8)) _] _ XU) as [_ XU']. clear XU.
  pose proof (BF_depot3.rw_cells_app_split bsegs m' _ [CB (Z.to_nat (BF_allocC.n8 n)) _] _ XU') as [XUm _]. clear XU'.
  cbn [cells_size csize] in XUm. repeat rewrite Nat.add_0_r in XUm. rewrite Z2Nat.id in XUm by (unfold BF_allocC.rz; clear -RZ; lia).
  assert (EUB : kShadowBase + ab / 8 + BF_allocC.rz n / 8 = kShadowBase + BF_allocC.ub n ab / 8).
  { unfold BF_allocC.ub, BF_allocC.rz in *. clear -RZ8 G3. Z.div_mod_to_equations. lia. }
  rewrite EUB in XUm.
  assert (XU4 : rw_cells bsegs m4 (kShadowBase + BF_allocC.ub n ab / 8) [CB (Z.to_nat (BF_allocC.n8 n)) (take (Z.to_nat (BF_allocC.n8 n)) (drop (Z.to_nat (BF_allocC.rz n / 8)) shj))]).
  { eapply (rw_cells_agree bsegs); [| eapply (rw_cells_agree bsegs); [| exact XUm]].
    - cbn. intros z Hz. repeat rewrite Nat.add_0_r in Hz. rewrite Z2Nat.id in Hz by (clear -N8R; lia).
      apply AG45; unfold BF_allocC.ub, BF_allocC.cb, BF_allocC.rz, kShadowBase in *; rewrite ?kHighMemBeg_val in G6.
      + clear -Hz G1 G2 CEILB N8R RZ USPAN; Z.div_mod_to_equations; lia.
      + clear -Hz G1 G2 CEILB LOC' LO' N8R RZ USPAN; Z.div_mod_to_equations; lia.
      + clear -Hz G1 G2 G6 N8R RZ USPAN CEILB; Z.div_mod_to_equations; lia.
      + clear -Hz RZ8 RZ G3 EUB; Z.div_mod_to_equations; lia.
      + clear -Hz RZ8 RZ N8R G3; Z.div_mod_to_equations; lia.
    - cbn. intros z Hz. repeat rewrite Nat.add_0_r in Hz. rewrite Z2Nat.id in Hz by (clear -N8R; lia). apply AGsh.
      unfold BF_allocC.ub, BF_allocC.rz, kShadowBase in *. clear -Hz RZ8 RZ N8R USPAN SP8' G3. Z.div_mod_to_equations. lia. }
  (* [comment removed for export] *)
  destruct (guard_cell m') as [cnr GC2].
  pose proof AMS2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & GSSP).
  assert (P0S2 : p0_statics m' cnr).
  { split; [exact PG2|]. pose proof AMS2 as (_ & _ & _ & GPAIR & MML & DPM & CFF & LPS & CF244 & _).
    pose proof Gps as Gps'. pose proof Gdy as Gdy'. pose proof Gdd as Gdd'. rewrite IC0 in Gps', Gdy', Gdd'.
    cbn [aic_page_size_cached aic_dying_flag aic_common_flags both_ic Z.add] in Gps', Gdy', Gdd'.
    split.
    - split; [exact GPSC|]. split; [exact GCF|]. split; [exact GPAIR|]. split; [exact Gps'|]. split; [exact MML|]. split; [exact DPM| exact Gdy'].
    - split; [exact GSSP|]. split; [exact GC2|]. split; [exact LPS|]. split; [exact CF244| exact Gdd']. }
  assert (IMG4 : forall x, 0xa5000 <= x < 0x180488 \/ 0x601590 <= x < 0x601818 -> m4 (wa x) = m' (wa x)).
  { intros x Hx. rewrite AG45; unfold BF_allocC.cb, BF_allocC.ub, BF_allocC.rz, kShadowBase in *;
      [| clear -Hx; lia| clear -Hx LOC' LO' CEILB; lia| clear -Hx G1 RZ; lia| clear -Hx G1; Z.div_mod_to_equations; lia| clear -Hx G1 RZ RG1; Z.div_mod_to_equations; lia].
    destruct Hx as [Hx|Hx]; [apply AGimg; exact Hx|].
    rewrite AG34d; [| clear -Hx; lia| clear -Hx LOC' CEILB; lia| apply NDFPlo; clear -Hx; lia]. apply AG23; [clear -Hx; lia| unfold BF_allocB.cb, BF_allocB.rz; clear -Hx G1 RZ; lia]. }
  assert (P0S4 : p0_statics m4 cnr).
  { apply (p0_statics_agree m' m4 cnr P0S2). intros x Hx. apply IMG4. unfold p0_static_addr in Hx. clear -Hx. lia. }
  (* [comment removed for export] *)
  assert (PBSHX : forall moX y k, kShadowBase + ab / 8 <= y -> y + Z.of_nat k <= kShadowBase + (ab + ca_span n) / 8 -> PP (sA a2 s) moX (wz y, k)).
  { intros moX y k Hy Hk. rewrite <- EPOL. unfold ca_span in Hk. destruct (from_primary n) eqn:PR.
    + destruct SIDE4 as (_ & AV & x & Eab & XAL). set (c := malloc_class n) in *.
      assert (Hn' : 0 <= n <= 64512) by (pose proof (proj1 (from_primary_iff n ltac:(clear -Hn; lia)) PR); clear -Hn H; lia).
      pose proof (malloc_class_ok n Hn') as [HCc NEEDc]. fold c in HCc, NEEDc.
      destruct AV as (CARVED & _). pose proof WFd as (_ & WR2 & _). pose proof (carved_in_space E0 a2 c ab HCc WR2 CARVED) as [IS1 IS2].
      eapply (pol_space_shadow E0 FSB0 HR0 (sA a2 s) moX [] [] WFd); cbn [aps_alloc sA aps_set_alloc]; rewrite ?A_SB_val; unfold kShadowBase, kRegionSize, kSpaceSize in *;
        [clear -Hy IS1; Z.div_mod_to_equations; lia| clear -Hk IS2; Z.div_mod_to_equations; lia].
    + destruct SIDE4 as (r0 & Eab & ESEC & FR). pose proof (map_size_facts n) as (MS4 & MSG & MS2). unfold kPageSize in MS4, MSG, MS2, Eab.
      assert (RU : round_up (needed n) 4096 + 4096 = map_size n) by reflexivity. unfold kPageSize in Hk.
      eapply (pol_sec_shadow E0 FSB0 HR0 (sA a2 s) moX [] [] WFd (mkSec r0 (map_size n) (needed n))); cbn [aps_alloc sA aps_set_alloc sc_map_beg sc_map_size]; rewrite ?A_SB_val;
        [exact RO4
        | rewrite ESEC; apply in_app_iff; right; left; reflexivity
        | unfold kShadowBase in *; clear -Hy Eab; Z.div_mod_to_equations; lia
        | unfold kShadowBase in *; clear -Hk Eab RU; Z.div_mod_to_equations; lia]. }
  destruct (RTOK_elim _ _ _ _ _ _ _ _ _ _ TOK5) as (R5 & R5' & ATK5 & HCR5 & HCR5' & GR5 & GD5 & RLE5).
  assert (SPA4 : (usp + -128) mod 16 = 0) by (clear -SPA; Z.div_mod_to_equations; lia).
  destruct RG4 as (t0' & t1' & t2' & a3' & a4' & a5' & a6' & a7' & s0' & s9' & t3' & t4' & t5' & t6' & CASES).
  assert (JOIN : forall (m5 : mem) (mo5 : Model) (xra5 t05 t15 t25 a05 a15 a25 a35 a45 a55 a65 a75 t35 t45 t55 t65 : word),
    mem_inv bsegs m5 -> stk bsegs m5 lo (usp + -128) -> wmono bsegs m4 m5 ->
    (forall z, 0 <= z < 2^64 -> (z < usp + -128 - 592 \/ usp + -128 <= z) ->
               (z < kShadowBase + BF_allocC.ub n ab / 8 \/ kShadowBase + BF_allocC.ub n ab / 8 + BF_allocC.n8 n <= z) -> m5 (wa z) = m4 (wa z)) ->
    (8 <= n -> rw_cells bsegs m5 (kShadowBase + BF_allocC.ub n ab / 8) [CB (Z.to_nat (BF_allocC.n8 n)) (repeat (Z_to_bv 8 0) (Z.to_nat (BF_allocC.n8 n)))]) ->
    ATOK E0 FSB0 HR0 L0 RES0 EB0 R5 R5' (sA a2 s) mo5 -> AKern E0 a2 mo5 ->
    m_fs mo5 = m_fs mo4 -> m_fds mo5 = m_fds mo4 -> m_tid mo5 = m_tid mo4 ->
    realizes_cfg acfg bsegs (mkCfg (MS (mkR xra5 (wz (usp + -128)) gp tp t05 t15 t25 s0' (wz n) a05 a15 a25 a35 a45 a55 a65 a75
                                        (wz ab) (wz (needed n)) (wz (BF_allocC.ub n ab)) (wz (BF_allocC.cb n ab)) (wz (8 * BF_allocC.n8 n)) (wz B) (wz 0) s9' (wz T) (wz 1) t35 t45 t55 t65)
                                   F (wz 0x32ec4) fc None m5 (seg_rom bsegs)) mo5) K).
  { intros m5 mo5 xra5 t05 t15 t25 a05 a15 a25 a35 a45 a55 a65 a75 t35 t45 t55 t65 MI5' SK5' WM45 AG45' ZSH5 ATK5' AK5' Qfs5' Qfds5' Qtid5'.
    (* [comment removed for export] *)
    assert (AG53 : forall z, 0 <= z < 2^64 -> (z < usp + -128 - 592 \/ usp + -128 <= z) -> (z < BF_allocC.cb n ab + 8 \/ BF_allocC.cb n ab + 16 <= z) ->
                   (z < kShadowBase + ab / 8 \/ kShadowBase + (ab + ca_span n) / 8 <= z) -> m5 (wa z) = m3 (wa z)).
    { intros z Hz Z1 Z2 Z4. rewrite AG45'; [| exact Hz| clear -Z1; lia| unfold BF_allocC.ub, BF_allocC.rz in *; clear -Z4 RZ N8R USPAN G3 RZ8; Z.div_mod_to_equations; lia].
      apply AG45; [exact Hz| clear -Z1; lia| exact Z2| unfold BF_allocC.ub, BF_allocC.rz in *; clear -Z4 RZ USPAN RG1; Z.div_mod_to_equations; lia
                 | unfold BF_allocC.ub, BF_allocC.rz in *; clear -Z4 RZ RG1; Z.div_mod_to_equations; lia]. }
    assert (AGT : forall z, 0 <= z < 2^64 -> (z + 1 <= lo \/ usp + -128 <= z) -> (z < BF_allocB.cb n ab \/ BF_allocB.cb n ab + 16 <= z) ->
                  ~ DepotFPd E0 a2 z -> (z < kShadowBase + ab / 8 \/ kShadowBase + (ab + ca_span n) / 8 <= z) -> m5 (wa z) = m' (wa z)).
    { intros z Hz Z1 Z2 Z3 Z4. pose proof LO as LOK. unfold K_ALLOC in LOK.
      rewrite AG53; [| exact Hz| clear -Z1 LOK; lia| unfold BF_allocB.cb, BF_allocB.rz, BF_allocC.cb, BF_allocC.rz in *; clear -Z2; lia| exact Z4].
      rewrite AG34d; [| exact Hz| exact Z1| exact Z3].
      apply AG23; [exact Hz| clear -Z2; lia]. }
    (* [comment removed for export] *)
    pose proof PL0OK as ((c0 & cl & CR0 & CC1 & CC2) & (d0 & dl & DR0 & DD1 & DD2) & TRp & CTp & DTp & CDp & CIAp).
    pose proof TRp as (TR1 & TR2 & _). pose proof TR2 as (Tlo & Thi' & Timg & Tband). unfold A_IMG_END, A_LOWAPP_END, A_HIGH_BEG in Timg, Tband.
    pose proof (resv_range_num E0 c0 cl CR0 ltac:(clear -CC1 CC2; lia)) as (CQ1 & CQ2 & CQ3 & CQ4).
    pose proof (resv_range_num E0 d0 dl DR0 ltac:(clear -DD1 DD2; lia)) as (DQ1 & DQ2 & DQ3 & DQ4).
    assert (BD : ab + ca_span n <= d0 \/ d0 + dl <= ab).
    { pose proof DR0 as (DIn & _ & _ & DRS & _). pose proof (ak_resv_geom _ _ _ AK4) as (RG1' & RG2' & RG3').
      change kSpaceSize with 137438953472 in RG3'. change kPageSize with 4096 in RG3'. change kResvLen with 137439023104 in RG3', DRS.
      unfold ca_span. destruct (from_primary n) eqn:PR.
      - destruct SIDE4 as (_ & AV & x & Eab & XAL). set (c := malloc_class n) in *.
        assert (Hn' : 0 <= n <= 64512) by (pose proof (proj1 (from_primary_iff n ltac:(clear -Hn; lia)) PR); clear -Hn H; lia).
        pose proof (malloc_class_ok n Hn') as [HCc NEEDc]. fold c in HCc, NEEDc.
        destruct AV as (CARVED & _). pose proof WFd as (_ & WR2 & _). pose proof (carved_in_space E0 a2 c ab HCc WR2 CARVED) as [IS1 IS2].
        unfold kSpaceSize, kRegionSize in *. clear -IS1 IS2 RG1' RG2' RG3' DRS. lia.
      - destruct SIDE4 as (r0 & Eab & ESEC & FRS). pose proof (map_size_facts n) as (MS4 & MSG & MS2). unfold kPageSize in MS4, MSG, MS2, Eab.
        pose proof WFd as (_ & _ & _ & _ & _ & WS & _). destruct WS as (_ & _ & WS3 & _).
        destruct (WS3 (mkSec r0 (map_size n) (needed n)) ltac:(rewrite ESEC; apply in_app_iff; right; left; reflexivity)) as (_ & _ & _ & _ & _ & _ & RSV).
        pose proof (RSV _ DIn) as X. cbn [fst snd sc_map_beg sc_map_size] in X.
        assert (RU : round_up (needed n) 4096 + 4096 = map_size n) by reflexivity. clear -X Eab RU MSG. unfold kPageSize in *. lia. }
    assert (RT5' : rt_misc5 FSB0 PL0 E0 m5).
    { apply (rt_misc5_agree E0 FSB0 PL0 m' m5 RT2). intros z Hz.
      destruct (rt_fpc_where2 E0 FSB0 PL0 z Hz) as [[ZI NM]|RH].
      - apply AGT; [clear -ZI; lia| clear -ZI LOC' CEILB; lia| unfold BF_allocB.cb, BF_allocB.rz; clear -ZI G1 RZ; lia
                   | intros Fd; exact (BF_deallocT2.dfp_not_rt E0 FSB0 PL0 ENV0 PL0OK a2 mo5 z AK5' WFd EI1 EI2 Fd Hz)| unfold kShadowBase; clear -ZI G1; Z.div_mod_to_equations; lia].
      - unfold rt_high2 in RH.
        apply AGT; [ clear -RH Thi' CQ1 CQ2 CC1 CC2 DQ1 DQ2 DD1 DD2 CEILB Tlo; lia
                   | clear -RH Thi' CQ2 CC1 CC2 DQ2 DD1 DD2 LOC'; lia
                   | unfold BF_allocB.cb, BF_allocB.rz; unfold BF_allocC.rz in USPAN; clear -RH G7 G8 BD USPAN RZ RG1 CC1 CC2 DD1 DD2; lia
                   | intros Fd; exact (BF_deallocT2.dfp_not_rt E0 FSB0 PL0 ENV0 PL0OK a2 mo5 z AK5' WFd EI1 EI2 Fd Hz)
                   | unfold kShadowBase; clear -RH Tband CQ4 CC1 CC2 DQ4 DD1 DD2 G1 G2 CEILB Tlo CQ1 DQ1; Z.div_mod_to_equations; lia]. }
    (* [comment removed for export] *)
    pose proof USPAN as USPANu. pose proof N8R as N8Ru. unfold BF_allocC.rz, BF_allocC.n8 in USPANu, N8Ru.
    assert (FR5 : frameA ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m5 junk).
    { unfold frameA in *. eapply (rw_cells_agree bsegs); [| exact FR4]. cbn. intros x Hx.
      apply AG53; unfold BF_allocC.cb, BF_allocC.rz, kShadowBase; [clear -Hx USPR' LO' LOC' CEILB; lia| clear -Hx; lia| clear -Hx G2 RZ USPANu RG1 LOC' LO' CEILB; lia| clear -Hx G1 G2 LOC' LO' CEILB; Z.div_mod_to_equations; lia]. }
    assert (HDR5 : rw_cells bsegs m5 (BF_allocC.cb n ab) [C1 j0; C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 id)]).
    { eapply (rw_cells_agree bsegs); [| exact HD5]. cbn. intros x Hx. pose proof LO as LOK. unfold K_ALLOC in LOK.
      apply AG45'; unfold BF_allocC.cb, BF_allocC.ub, BF_allocC.rz, BF_allocC.n8, kShadowBase in *; rewrite ?kHighMemBeg_val in G6;
        [clear -Hx G1 G2 RZ CEILB USPANu RG1 Hn; lia| clear -Hx G2 RZ USPANu RG1 LOC' LOK CEILB Hn; lia| clear -Hx G1 G2 G6 RZ N8Ru USPANu RG1 CEILB Hn; Z.div_mod_to_equations; lia]. }
    (* [comment removed for export] *)
    assert (WRB : wr_at bsegs m' ab (needed n)).
    { pose proof G4 as G4'. unfold ca_span in G4'. destruct (from_primary n) eqn:PR.
      - destruct SIDE as (_ & AV & xk & Eab & XAL). set (c := malloc_class n) in *.
        assert (Hn' : 0 <= n <= 64512) by (pose proof (proj1 (from_primary_iff n ltac:(clear -Hn; lia)) PR); clear -Hn H; lia).
        pose proof (malloc_class_ok n Hn') as [HCc NEEDc]. fold c in HCc, NEEDc.
        destruct AV as ((k0 & K0 & EK & KU) & _). pose proof WF2 as (_ & [_ WR2'] & _). destruct (WR2' c HCc) as ((RA1 & RA2) & _). cbv zeta in RA2. unfold region_of in KU, RA2.
        pose proof (class_size_mod c HCc) as [_ CS32].
        destruct (Rrm c ltac:(unfold kNumClasses, kLargestClassID in *; clear -HCc; lia)) as [WRU _]. cbv zeta in WRU. unfold region_of in WRU.
        eapply (BF_lkit.wr_at_sub bsegs); [exact WRU| clear -EK K0 CS32; nia| clear -EK K0 KU RA2 G4' CS32; nia].
      - destruct SIDE as (r0 & Eab & ESEC & FRS). pose proof (map_size_facts n) as (MS4 & MSG & MS2). unfold kPageSize in MS4, MSG, MS2, Eab.
        destruct Rsec as [_ RS]. destruct (RS (length (as_sec a)) (mkSec r0 (map_size n) (needed n)) ltac:(rewrite ESEC; rewrite nth_error_app2 by (clear; lia); rewrite Nat.sub_diag; reflexivity)) as [_ WRS].
        cbn [sc_map_beg sc_map_size] in WRS. eapply (BF_lkit.wr_at_sub bsegs); [exact WRS| clear -Eab; lia| clear -Eab MSG; lia]. }
    assert (WRB5 : wr_at bsegs m5 ab (needed n)).
    { eapply wr_at_transport; [exact WRB|]. exact (wmono_trans _ _ _ _ WM3 (wmono_trans _ _ _ _ WM4 (wmono_trans _ _ _ _ WM5 WM45))). }
    destruct (BF_tkit.wr_at_CB m5 (BF_allocC.ub n ab) n ltac:(eapply (BF_lkit.wr_at_sub bsegs); [exact WRB5| unfold BF_allocC.ub, BF_allocC.rz; clear -RZ; lia| unfold BF_allocC.ub, BF_allocC.rz; pose proof G4; unfold needed, needed1 in *; clear -RZ RG1 H; destruct (from_primary n); lia]) ltac:(clear -Hn; lia)) as [uj USR5].
    destruct (BF_tkit.wr_at_CB m5 ab (BF_allocC.rz n - 16) ltac:(eapply (BF_lkit.wr_at_sub bsegs); [exact WRB5| clear; lia| unfold BF_allocC.rz; pose proof G4; unfold needed, needed1 in *; clear -RZ RG1 H; destruct (from_primary n); lia]) ltac:(unfold BF_allocC.rz; clear -RZM RZ; Z.div_mod_to_equations; lia)) as [mj MAG5].
    pose proof (conj Hn (conj G1 (conj G2 (conj G3 (conj G4 (conj G5 (conj G6 (conj G7 (conj G8 (conj CEILB (conj RZ (conj RZ8 (conj RZM (conj RG1 (conj RG2 (conj RG3 (conj N8Ru (conj USPANu (conj SP8' (conj LOC' (conj LO' (conj USPR' (conj NR1 (conj NR2 (conj NR3 (conj Tband (conj Tlo (conj Thi' (conj SPANPOS CBR))))))))))))))))))))))))))))) as NUMS.
    (* [comment removed for export] *)
    set (kS := Z.to_nat (BF_allocC.rz n / 8 + BF_allocC.n8 n)).
    set (jS := nth kS shj (Z_to_bv 8 0)).
    assert (PSHB5 : n mod 8 <> 0 -> rw_cells bsegs m5 (kShadowBase + (BF_allocC.ub n ab + 8 * BF_allocC.n8 n) / 8) [C1 jS]).
    { intros NM8. pose proof (BF_tkit.u8arr_of_cells m' _ _ BSH) as U. cbn [cells_bytes cbytes] in U. rewrite app_nil_r in U.
      pose proof BSH as [[LSH0 _] _]. cbn in LSH0. destruct LSH0 as [LSH _].
      assert (N8S : 8 * BF_allocC.n8 n < n) by (unfold BF_allocC.n8 in *; clear -NM8 N8R Hn; Z.div_mod_to_equations; lia).
      assert (KLT : (kS + 1 <= length shj)%nat).
      { rewrite LSH. subst kS. unfold BF_allocC.rz, BF_allocC.n8 in *. clear -N8S N8Ru USPANu RZ RZ8 SP8' RG1.
        apply Nat2Z.inj_le. rewrite Nat2Z.inj_add. rewrite !Z2Nat.id by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations. lia. }
      destruct (drop kS shj) as [|b rest] eqn:ESK; [exfalso; apply (f_equal length) in ESK; rewrite length_skipn in ESK; cbn in ESK; clear -ESK KLT; lia|].
      assert (EJ : jS = b) by (subst jS; rewrite <- (Nat.add_0_r kS), <- nth_skipn, ESK; reflexivity).
      replace (kShadowBase + (BF_allocC.ub n ab + 8 * BF_allocC.n8 n) / 8) with (kShadowBase + ab / 8 + Z.of_nat kS)
        by (subst kS; unfold BF_allocC.ub, BF_allocC.rz, BF_allocC.n8 in *; clear -RZ8 RZ G3 N8Ru; rewrite Z2Nat.id by (Z.div_mod_to_equations; lia); Z.div_mod_to_equations; lia).
      eapply (rw_cells_agree bsegs); [| eapply (BF_tkit.u8arr_cell m' _ shj kS (C1 jS)); [exact U| exact KLT| exact I| cbn [cbytes csize]; rewrite ESK, EJ; reflexivity]].
      cbn. intros z Hz.
      assert (KZ : Z.of_nat kS = BF_allocC.rz n / 8 + BF_allocC.n8 n) by (subst kS; unfold BF_allocC.rz, BF_allocC.n8 in *; clear -RZ N8Ru; rewrite Z2Nat.id by (Z.div_mod_to_equations; lia); reflexivity).
      rewrite KZ in Hz.
      rewrite AG45'; [| numk Hz NUMS| numk Hz NUMS| numk Hz NUMS].
      rewrite AG45; [| numk Hz NUMS| numk Hz NUMS| numk Hz NUMS| numk Hz NUMS| generalize N8S; numk Hz NUMS].
      apply AGsh. generalize N8S. numk Hz NUMS. }
    (* [comment removed for export] *)
    pose proof (rt_misc5_fsenv _ _ _ _ RT5') as FSE5.
    assert (TC5 : thread_cells m5 tp 0x6028f8 CTX T).
    { pose proof FSE5 as FSE'. unfold FSEnv in FSE'. pose proof FSE' as (_ & _ & _ & _ & _ & _ & FKI & FKEY & FTSD & FTSD0 & FCTXT & _). clear FSE'.
      split; [exact FKI|]. split; [exact FKEY|]. split; [| split; [exact FTSD0| exact FCTXT]].
      rewrite TP. unfold FS_TP. rewrite unsigned_lit by (clear; lia). exact FTSD. }
    pose proof (rt_misc5_ams _ _ _ _ RT5') as AMS5. pose proof AMS5 as (LSG5 & LSC5 & _).
    assert (LSC5' : rw_cells bsegs m5 (bv_unsigned tp + 16) [C4 (Z_to_bv 64 0)]) by (rewrite TP; rewrite unsigned_lit by (clear; lia); exact LSC5).
    destruct (rt_misc5_exit _ _ _ _ RT5') as [tX5 XS5].
    assert (US5 : unreg_statics m5) by (unfold exit_statics in XS5; decompose [and] XS5; assumption).
    pose proof US5 as US5'. unfold unreg_statics in US5'. pose proof US5' as (GFL5 & _). clear US5'.
    (* [comment removed for export] *)
    assert (AGimg5 : forall x, 0xa5000 <= x < 0x180488 -> m5 (wa x) = m' (wa x)).
    { intros x Hx. apply AGT; [clear -Hx; lia| clear -Hx LOC' CEILB; lia| unfold BF_allocB.cb, BF_allocB.rz; clear -Hx G1 RZ; lia| apply NDFPlo; clear -Hx; lia| unfold kShadowBase; clear -Hx G1; Z.div_mod_to_equations; lia]. }
    assert (AGthr5 : forall x, T + 64 <= x < T + 4096 -> m5 (wa x) = m' (wa x)).
    { intros x Hx. apply AGT; [clear -Hx Thi' Tlo CEILB; lia| clear -Hx Thi' LOC'; lia| unfold BF_allocB.cb, BF_allocB.rz; clear -Hx G7 USPANu RZ RG1; lia| | unfold kShadowBase; clear -Hx Tband Tlo G1 G2 CEILB; Z.div_mod_to_equations; lia].
      intros Fd. destruct (BF_deallocT1.dfp_cases E0 PL0 ENV0 PL0OK a2 mo5 x IC0 AK5' WFd EI1 EI2 Fd) as [ST|(bb & bln & R & B0 & B2 & BB & B3 & B4 & BT' & B5)]; [clear -ST Hx Timg; lia| clear -R BT' Hx; lia]. }
    pose proof RX2 as (_ & _ & _ & Rthr & _). pose proof Rthr as (_ & _ & _ & _ & _ & TST & TBY & _).
    set (tsa := as_ts a1) in *.
    assert (STATS5 : rw_cells bsegs m5 (T + 2800) [C8 (wz (ts_mallocs tsa)); C8 (wz (ts_malloced tsa)); C8 (wz (ts_malloced_redzones tsa))]).
    { eapply (rw_cells_agree bsegs); [| eapply BF_tkit.u64arr_prefix3; unfold tstats_words in TST; cbn [map] in TST; exact TST]. cbn. intros z Hz. apply AGthr5. unfold kThrStats in Hz. clear -Hz. lia. }
    assert (LRG5 : rw_cells bsegs m5 (T + 2904) [C8 (wz (ts_malloc_large tsa))]).
    { replace (T + 2904) with (T + kThrStats + 8 * Z.of_nat 13) by (unfold kThrStats; clear; lia).
      eapply (rw_cells_agree bsegs); [| eapply (BF_tkit.u64arr_cell m' _ _ 13%nat); [exact TST| reflexivity]]. cbn. intros z Hz. apply AGthr5. unfold kThrStats in Hz. clear -Hz. lia. }
    set (bszv := match ts_by_size tsa !! (class_id (needed n)) with Some v => v | None => 0 end).
    assert (CIDB : from_primary n = true -> 0 <= class_id (needed n) < 32).
    { intros PR. assert (Hn' : 0 <= n <= 64512) by (pose proof (proj1 (from_primary_iff n ltac:(clear -Hn; lia)) PR); clear -Hn H; lia).
      pose proof (proj1 (malloc_class_ok n Hn')) as X. unfold malloc_class in X. unfold needed. rewrite PR. clear -X. lia. }
    assert (BYSZ5 : from_primary n = true -> rw_cells bsegs m5 (T + 2912 + 8 * class_id (needed n)) [C8 (wz bszv)]).
    { intros PR. pose proof (CIDB PR) as CIDB'. replace (T + 2912 + 8 * class_id (needed n)) with (T + kThrStats + 112 + 8 * Z.of_nat (Z.to_nat (class_id (needed n)))) by (unfold kThrStats; clear -CIDB'; lia).
      eapply (rw_cells_agree bsegs); [| eapply (BF_tkit.u64arr_cell m' _ _ (Z.to_nat (class_id (needed n)))); [exact TBY|]].
      - cbn. intros z Hz. apply AGthr5. unfold kThrStats in Hz. clear -Hz CIDB'. lia.
      - rewrite nth_error_map, BF_tkit.nth_error_ziota by (clear -CIDB'; lia). cbn [option_map]. subst bszv. rewrite Z2Nat.id by (clear -CIDB'; lia). rewrite Z.add_0_l. reflexivity. }
    (* [comment removed for export] *)
    pose proof Gfl as GFLB. rewrite IC0 in GFLB. replace (aic_asan_flags both_ic) with 0xabdb8 in GFLB by reflexivity.
    pose proof Rglob as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & GHK & _). rewrite IC0 in GHK. replace (aic_malloc_hook_table both_ic) with 0x140080 in GHK by reflexivity.
    assert (LFL : length (map AsanRep.zb (asan_flags_bytes both_ic)) = 128%nat) by reflexivity.
    assert (FL44 : rw_cells bsegs m5 0xabde4 [C4 (Z_to_bv 64 4096)]).
    { assert (X : rw_cells bsegs m' (0xabdb8 + Z.of_nat 44) [CB 4 (take 4 (drop 44 (map AsanRep.zb (asan_flags_bytes both_ic))))]).
      { eapply (BF_tkit.u8arr_cell m' _ _ 44%nat (CB 4 _)); [exact GFLB| rewrite LFL; cbn; clear; lia| reflexivity| reflexivity]. }
      replace 0xabde4 with (0xabdb8 + Z.of_nat 44) by reflexivity.
      eapply (rw_cells_agree bsegs); [| eapply (BF_lkit.rw_cells_reshape bsegs m' _ [CB 4 _]); [ | | exact X]]. 2: (clear; cbn; tauto). 2: (vm_compute; reflexivity).
      clear X. cbn. intros z Hz. apply AGimg5. clear -Hz. lia. }
    assert (FL52 : rw_cells bsegs m5 0xabdec [C4 (Z_to_bv 64 0xbe)]).
    { assert (X : rw_cells bsegs m' (0xabdb8 + Z.of_nat 52) [CB 4 (take 4 (drop 52 (map AsanRep.zb (asan_flags_bytes both_ic))))]).
      { eapply (BF_tkit.u8arr_cell m' _ _ 52%nat (CB 4 _)); [exact GFLB| rewrite LFL; cbn; clear; lia| reflexivity| reflexivity]. }
      replace 0xabdec with (0xabdb8 + Z.of_nat 52) by reflexivity.
      eapply (rw_cells_agree bsegs); [| eapply (BF_lkit.rw_cells_reshape bsegs m' _ [CB 4 _]); [ | | exact X]]. 2: (clear; cbn; tauto). 2: (vm_compute; reflexivity).
      clear X. cbn. intros z Hz. apply AGimg5. clear -Hz. lia. }
    assert (FL85 : rw_cells bsegs m5 0xabe0d [C1 (Z_to_bv 8 1)]).
    { replace 0xabe0d with (0xabdb8 + Z.of_nat 85) by reflexivity.
      eapply (rw_cells_agree bsegs); [| eapply (BF_tkit.u8arr_cell m' _ _ 85%nat (C1 _)); [exact GFLB| rewrite LFL; cbn; clear; lia| exact I| cbn; reflexivity]].
      cbn. intros z Hz. apply AGimg5. clear -Hz. lia. }
    assert (HK05 : rw_cells bsegs m5 0x140080 [C8 (Z_to_bv 64 0)]).
    { eapply (rw_cells_agree bsegs); [| replace 0x140080 with (0x140080 + 8 * Z.of_nat 0) by (clear; lia); eapply (BF_tkit.u64arr_cell m' _ _ 0%nat); [exact GHK| reflexivity]]. cbn. intros z Hz. apply AGimg5. clear -Hz. lia. }
    assert (PG5' : poison_globals m5).
    { apply (poison_globals_agree m4 m5 PG5). intros z Hz. pose proof LO as LOK. unfold K_ALLOC in LOK.
      apply AG45'; unfold BF_allocC.ub, BF_allocC.rz, kShadowBase; [clear -Hz; lia| clear -Hz LOC' LOK CEILB; lia| clear -Hz G1 RZ; Z.div_mod_to_equations; lia]. }
    (* [comment removed for export] *)
    assert (PSTK5 : forall y k, lo <= y -> y + Z.of_nat k <= hi -> PP (sA a2 s) mo5 (wz y, k)).
    { intros y k Hy Hk. rewrite <- EPOL. eapply (pol_stack' E0 FSB0 HR0 (sA a2 s) mo5 AK5' WE ENV0); clear -Hy Hk LOC' AHI; lia. }
    assert (PIMG5 : forall y k, 0xa5000 <= y -> y + Z.of_nat k <= 0x603000 -> PP (sA a2 s) mo5 (wz y, k)).
    { intros y k Hy Hk. rewrite <- EPOL. eapply (pol_img' E0 FSB0 HR0 (sA a2 s) mo5 AK5' WE EV4 ENV0); [clear -Hy; lia| exact Hk]. }
    assert (PRO5 : forall y k, 0x10000 <= y -> y + Z.of_nat k <= 0x31000 -> PP (sA a2 s) mo5 (wz y, k)).
    { intros y k Hy Hk. rewrite <- EPOL. eapply (pol_img' E0 FSB0 HR0 (sA a2 s) mo5 AK5' WE EV4 ENV0); [clear -Hy; lia| clear -Hk; lia]. }
    assert (PTHR5 : forall y k, T <= y -> y + Z.of_nat k <= T + 4096 -> PP (sA a2 s) mo5 (wz y, k)).
    { intros y k Hy Hk. rewrite <- EPOL. eapply (pol_thread' E0 FSB0 HR0 (sA a2 s) mo5 AK5' WE); [exact Hy| exact Hk]. }
    assert (PCTX5 : forall y k, CTX <= y -> y + Z.of_nat k <= CTX + 160 -> PP (sA a2 s) mo5 (wz y, k)).
    { intros y k Hy Hk. rewrite <- EPOL. eapply (pol_resv_range' E0 FSB0 HR0 (sA a2 s) mo5 AK5' c0 cl _ _ CR0); clear -Hy Hk CC1 CC2; lia. }
    assert (PBLK5 : forall y k, ab <= y -> y + Z.of_nat k <= ab + needed n -> PP (sA a2 s) mo5 (wz y, k)).
    { intros y k Hy Hk. destruct k as [|k'].
      - right. split; [unfold acc_nowrap; cbn [fst snd]; rewrite unsigned_lit by (clear -Hy Hk G1 G2 G4 CEILB; lia); clear -Hy Hk G1 G2 G4 CEILB; lia| intros kk Hkk; cbn in Hkk; clear -Hkk; lia].
      - rewrite <- EPOL. pose proof G4 as G4'. unfold ca_span in G4'. destruct (from_primary n) eqn:PR.
        + destruct SIDE4 as (_ & AV & xk & Eab & XAL). set (c := malloc_class n) in *.
          assert (Hn' : 0 <= n <= 64512) by (pose proof (proj1 (from_primary_iff n ltac:(clear -Hn; lia)) PR); clear -Hn H; lia).
          pose proof (malloc_class_ok n Hn') as [HCc NEEDc]. fold c in HCc, NEEDc.
          destruct AV as ((k0 & K0 & EK & KU) & _). pose proof WFd as (_ & [_ WR2'] & _). destruct (WR2' c HCc) as ((RA1 & RA2) & _). cbv zeta in RA2. unfold region_of in KU, RA2.
          pose proof (class_size_mod c HCc) as [_ CS32].
          eapply (pol_user E0 FSB0 HR0 (sA a2 s) mo5 [] [] AK5' WFd c); [exact HCc| cbn [aps_alloc sA aps_set_alloc]; clear -Hy EK K0 CS32; nia| cbn [aps_alloc sA aps_set_alloc]; clear -Hk EK K0 KU RA2 G4' CS32; nia| clear; lia].
        + destruct SIDE4 as (r0 & Eab & ESEC & FRS).
          pose proof (map_size_facts n) as (MS4 & MSG & MS2). unfold kPageSize in MS4, MSG, MS2, Eab.
          eapply (pol_sec_map E0 FSB0 HR0 (sA a2 s) mo5 [] [] AK5' WFd (mkSec r0 (map_size n) (needed n)));
            [cbn [aps_alloc sA aps_set_alloc]; rewrite ESEC; apply in_app_iff; right; left; reflexivity| cbn [sc_map_beg]; clear -Hy Eab; lia| cbn [sc_map_beg sc_map_size]; clear -Hk Eab MSG; lia]. }
    pose proof (PBSHX mo5) as PBSH5.
    assert (HCID : from_primary n = true -> 1 <= BF_allocD.cid n <= 30).
    { intros PR. assert (Hn' : 0 <= n <= 64512) by (pose proof (proj1 (from_primary_iff n ltac:(clear -Hn; lia)) PR); clear -Hn H; lia).
      pose proof (proj1 (malloc_class_ok n Hn')) as X. unfold malloc_class in X. unfold BF_allocD.cid, needed. rewrite PR. exact X. }
    (* [comment removed for export] *)
    eapply (rzA_seg_cfg bsegs (aSc (sA a2 s)) (aNc (sA a2 s)) (aEBc (sA a2 s)) (PP (sA a2 s) mo5)); [| exact (PP_KIP E0 FSB0 HR0 L0 RES0 EB0 _ _ _ _ ATK5')|].
    { eapply (alloc5_segD (PP (sA a2 s) mo5) ra sp gp tp xra5 t05 t15 t25 s0' a05 a15 a25 a35 a45 a55 a65 a75 s9' t35 t45 t55 t65
                s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m5 lo hi n B T CTX 0x6028f8 ab id b1 (ca_span n) j0 jS junk uj mj
                (wz (ts_mallocs tsa)) (wz (ts_malloced tsa)) (wz (ts_malloced_redzones tsa)) (wz (ts_malloc_large tsa)) (wz bszv));
        [ exact SK5'| exact LOC'| exact LO'| clear -UB BA LEN; unfold zlen in *; lia| exact AHI| exact MI5'| exact Hn1| exact HID| exact HB1| exact HB1'
        | unfold frameA in FR5; exact FR5| exact HDR5| exact USR5| exact MAG5| exact PSHB5| exact TC5| exact HTSD| exact HCTX| exact HT| exact HTP
        | pose proof TCTX as XT; clear -XT; lia
        | exact STATS5| exact LRG5| exact BYSZ5| exact PG5'| exact GFL5| exact FL44| exact FL52| exact FL85| exact LSG5| exact LSC5'| exact HK05
        | split; [exact G1| split; [exact G2| clear -G3; Z.div_mod_to_equations; lia]]| exact G4| exact G5
        | rewrite kHighMemBeg_val; rewrite ?kHighMemBeg_val in G6; exact G6| exact G7| exact HCID
        | exact PSTK5| exact PIMG5| exact PRO5| exact PTHR5| exact PCTX5| exact PBLK5| exact PBSH5 ]. }
    intros ms7 mo7 POST7 AG7 KP7.
    destruct POST7 as (w0 & w1 & w2 & xa1 & xa2 & xa3 & xa4 & xa5 & xa6 & xa7 & w3 & w4 & w5 & w6 & m7 & b1' & -> & MU7 & WM7 & MI7 & SK7 & HB7 & HDR7 & USR7 & MAG7 & GRAN7 & ST7 & CNT7).
    pose proof (magree_frame _ _ AG7) as (Qfds7 & Qvm7 & Qlz7 & Qfs7 & Qh7 & Qtid7 & _).
    pose proof (AKern_frame _ _ _ _ Qvm7 Qlz7 AK5') as AK7.
    pose proof (ATOK_magree _ _ _ _ _ _ _ _ _ _ _ ATK5' AG7 (proj1 KP7)) as ATK7.
    eapply (CONT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m7 mo7 (AsanRepTailB.tail_st n ab id a2) (BF_allocC.ub n ab)).
    pose proof (hoareW_arun _ _ _ _ _ _ _ _ _ _ (BF_caframe.ca_op_residue E0 a n) eq_refl RUNA) as ERS. cbn beta in ERS.
    pose proof AIV as (_ & _ & _ & RO0 & QB0 & DI0 & BI0 & _ & _ & SS0 & CS0).
    assert (KEY32 : depot_ok E0 a1 (bst_key len ws) /\ zlen (bst_key len ws) + 1 <= 32).
    { split; [exact DOK|]. unfold bst_key, zlen. rewrite length_map, length_firstn. clear -LEN LWS. unfold zlen in *. lia. }
    pose proof (BF_atail.atail_facts E0 PL0 ENV0 PL0OK a a1 a2 mo3 n ab id (bst_key len ws) _ _ _ _ _ _ _ _
                  Hwf RO0 QB0 DI0 BI0 CS0 ABUD Hn NBIG RUNA SS2 SIDE KEY32 RUND WFd AK4 (conj EI1 EI2)
                  (conj End (conj Eks (conj Efr (conj Enb (conj Esb (conj Estd (conj Ech (conj Edead (conj Etq Egq))))))))) ENP ERS)
      as (ARUN' & (WF' & RO' & QB' & DI' & BI' & SS' & CS') & ACCT' & PERM' & ABR' & FRESH' & RENV' & BLK' & NFP' & NDS').
    (* [comment removed for export] *)
    assert (outside_app' : forall W1 W2 x, outside (W1 ++ W2) x <-> (outside W1 x /\ outside W2 x)).
    { clear. induction W1 as [|[lo' hi'] W1 IH]; intros W2 x; cbn; [tauto|]. rewrite IH. tauto. }
    assert (munch_app' : forall W1 W2 (x0 x1 x2 : mem), munch W1 x0 x1 -> munch W2 x1 x2 -> munch (W1 ++ W2) x0 x2).
    { clear -outside_app'. intros W1 W2 x0 x1 x2 H1 H2 x Hx. apply outside_app' in Hx. destruct Hx as [X1 X2]. rewrite (H2 x X2). exact (H1 x X1). }
    assert (M45 : munch [(usp + -128 - 592, usp + -128); (kShadowBase + BF_allocC.ub n ab / 8, kShadowBase + BF_allocC.ub n ab / 8 + BF_allocC.n8 n)] m4 m5).
    { intros x Hx. pose proof (bv_unsigned_in_range 64 x) as R. unfold bv_modulus in R.
      rewrite <- (Z_to_bv_bv_unsigned x). apply AG45'; [exact R| |]; cbn in Hx; clear -Hx; lia. }
    assert (WMt : wmono bsegs m m7).
    { exact (wmono_trans _ _ _ _ WM1 (wmono_trans _ _ _ _ WM2 (wmono_trans _ _ _ _ WM3 (wmono_trans _ _ _ _ WM4 (wmono_trans _ _ _ _ WM5 (wmono_trans _ _ _ _ WM45 WM7)))))). }
    assert (MUt : munch (([(usp - 144, usp)] ++ W) ++ ([(BF_allocB.cb n ab, BF_allocB.cb n ab + 8)] ++ Wd)
                         ++ (([(usp + -128 - 64, usp + -128); (BF_allocC.cb n ab + 8, BF_allocC.cb n ab + 16); (kShadowBase + ab / 8, kShadowBase + ab / 8 + BF_allocC.rz n / 8); (kShadowBase + (BF_allocC.ub n ab + rounded n) / 8, kShadowBase + (ab + ca_span n) / 8)]
                              ++ [(usp + -128 - 592, usp + -128); (kShadowBase + BF_allocC.ub n ab / 8, kShadowBase + BF_allocC.ub n ab / 8 + BF_allocC.n8 n)])
                             ++ BF_allocD.W4 sp lo n T ab)) m m7).
    { eapply munch_app'; [eapply munch_app'; [exact MU1| exact MUW]|].
      eapply munch_app'; [eapply munch_app'; [exact MU3| exact MUd]|].
      eapply munch_app'; [eapply munch_app'; [exact MU5| exact M45]| exact MU7]. }
    unfold alloc_post_state.
    refine (conj SK7 (conj WMt (conj _ (conj ARUN' (conj _ (conj _ (conj _ (conj _ (conj _ (conj ACCT' (conj eq_refl (conj ABR' (conj PERM' (conj _ _)))))))))))))).
    4: { rewrite Qfs7, Qfs5', Qfs5, Qfs4, Qfs3, Qfs2, Qfs1; reflexivity. }
    4: { rewrite Qfds7, Qfds5', Qfds5, Qfds4, Qfds3, Qfds2, Qfds1; reflexivity. }
    4: { rewrite Qtid7, Qtid5', Qtid5, Qtid4, Qtid3, Qtid2, Qtid1; reflexivity. }
    4: { exists (repeat (Z_to_bv 8 190) (Z.to_nat (n `min` 4096)) ++ drop (Z.to_nat (n `min` 4096)) uj). split; [| exact USR7].
         pose proof USR5 as [[LU _] _]. cbn in LU. destruct LU as [LU _]. rewrite length_app, repeat_length, length_skipn, LU. clear -Hn. lia. }
    3: { (* [comment removed for export] *)
         assert (SFP : same_fp a2 (AsanRepTailB.tail_st n ab id a2)) by (clear; unfold AsanRepTailB.tail_st; repeat split; reflexivity).
         assert (EGR : gapR (AsanRepTailB.tail_st n ab id a2) = gapR a2) by (apply gapR_eq; reflexivity).
         assert (EGD : gapD (AsanRepTailB.tail_st n ab id a2) = gapD a2) by (apply gapD_eq; reflexivity).
         assert (EGP : gapP (AsanRepTailB.tail_st n ab id a2) = gapP a2) by (apply gapP_eq; reflexivity).
         assert (GC : ca_gcost n + DSLACK <= ASLACK).
         { unfold ca_gcost, DSLACK, ASLACK, NMAXA. pose proof (map_size_facts n) as (_ & MSG & _). unfold map_size, round_up, kPageSize in *.
           clear -Hn NR1 NR2 NR3 MSG RZ. destruct (from_primary n); Z.div_mod_to_equations; lia. }
         cbn [aps_alloc sA aps_set_alloc] in GR5, GD5, RLE5.
         apply (RTOK_intro _ _ _ _ _ _ _ _ _ _ R5 R5'); cbn [aps_alloc sA aps_set_alloc]; rewrite ?EGR, ?EGD, ?EGP;
           [ exact (ATOK_same_fp _ _ _ _ _ _ _ _ _ _ _ _ ATK7 SFP) | clear -CHG; lia | exact GR5 | exact GD5 | clear -RLE5 BPR CHG; lia | clear -HCR5' ASL GC; lia ]. }
    3: { (* [comment removed for export] *)
         split; [unfold BF_allocC.ub, BF_allocC.rz; clear -G3 RZM; Z.div_mod_to_equations; lia|]. split; [clear -Hn; lia|].
         rewrite A_SB_val. change 2147450880 with kShadowBase.
         assert (NMOD : n mod 8 = n - 8 * BF_allocC.n8 n) by (unfold BF_allocC.n8; clear -Hn; Z.div_mod_to_equations; lia).
         assert (GRAN7' : n mod 8 <> 0 -> rw_cells bsegs m7 (kShadowBase + BF_allocC.ub n ab / 8 + Z.of_nat (cells_size [CB (Z.to_nat (BF_allocC.n8 n)) (repeat (Z_to_bv 8 0) (Z.to_nat (BF_allocC.n8 n)))])) [C1 (Z_to_bv 8 (n mod 8))]).
         { intros NM8. cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r. rewrite Z2Nat.id by (clear -N8Ru; unfold BF_allocC.n8; lia).
           replace (kShadowBase + BF_allocC.ub n ab / 8 + BF_allocC.n8 n) with (kShadowBase + (BF_allocD.ub n ab + 8 * BF_allocD.n8 n) / 8)
             by (unfold BF_allocC.ub, BF_allocC.rz, BF_allocC.n8, BF_allocD.ub, BF_allocD.rz, BF_allocD.n8; clear -G3 RZM Hn; Z.div_mod_to_equations; lia).
           exact (GRAN7 NM8). }
         destruct (Z_lt_le_dec n 8) as [N8|N8].
         - (* [comment removed for export] *)
           assert (N80 : BF_allocC.n8 n = 0) by (unfold BF_allocC.n8; clear -N8 Hn; Z.div_mod_to_equations; lia).
           assert (NM8 : n mod 8 <> 0) by (rewrite NMOD, N80; clear -Hn N8; lia).
           unfold blk_shadow. unfold BF_allocC.n8 in N80. rewrite N80. replace (n mod 8 =? 0) with false by (symmetry; apply Z.eqb_neq; exact NM8). cbn [Z.to_nat repeat app].
           pose proof (GRAN7' NM8) as X. unfold BF_allocC.n8 in X. rewrite N80 in X. cbn [cells_size csize Z.to_nat repeat Nat.add Z.of_nat] in X. rewrite Z.add_0_r in X.
           exact (BF_tkit.u8arr_of_cells m7 _ _ X).
         - (* [comment removed for export] *)
           assert (ZSH7 : rw_cells bsegs m7 (kShadowBase + BF_allocC.ub n ab / 8) [CB (Z.to_nat (BF_allocC.n8 n)) (repeat (Z_to_bv 8 0) (Z.to_nat (BF_allocC.n8 n)))]).
           { eapply (rw_cells_agree bsegs); [| exact (ZSH5 N8)]. cbn. intros z Hz. repeat rewrite Nat.add_0_r in Hz. rewrite Z2Nat.id in Hz by (clear -N8Ru; unfold BF_allocC.n8; lia).
             apply MU7. rewrite wa_unsigned by (numk Hz NUMS). unfold BF_allocD.W4. pose proof TCTX as XT. pose proof (HCID) as HC.
             destruct (n mod 8 =? 0) eqn:M8; cbn; unfold BF_allocD.cb, BF_allocD.ub, BF_allocD.rz, BF_allocD.n8, BF_allocD.ctr in *;
               (destruct (from_primary n); [specialize (HC eq_refl); generalize HC| clear HC]; numk Hz NUMS). }
           destruct (Z.eq_dec (n mod 8) 0) as [M0|M0].
           + unfold blk_shadow. rewrite (proj2 (Z.eqb_eq _ _) M0). rewrite app_nil_r. fold (BF_allocC.n8 n).
             pose proof (BF_tkit.u8arr_of_cells m7 _ _ ZSH7) as X. cbn [cells_bytes cbytes app] in X. rewrite ?app_nil_r in X. exact X.
           + unfold blk_shadow. replace (n mod 8 =? 0) with false by (symmetry; apply Z.eqb_neq; exact M0). fold (BF_allocC.n8 n).
             pose proof (rwc_join_at bsegs m7 _ _ _ _ ZSH7 (GRAN7' M0) eq_refl) as X.
             pose proof (BF_tkit.u8arr_of_cells m7 _ _ X) as U. cbn [cells_bytes cbytes app] in U. rewrite <- ?app_assoc in U. cbn [app] in U. exact U. }
    2: { (* [comment removed for export] *)
         refine (conj _ (conj WF' (conj _ (conj RO' (conj QB' (conj DI' (conj BI' (conj MI7 (conj _ (conj SS' CS')))))))))).
         2: { eapply (BF_tkit.AKern_ext E0 a2); [reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| exact AK7]. }
         2: { (* [comment removed for export] *)
              apply (rt_misc5_agree E0 FSB0 PL0 m5 m7 RT5'). intros z Hz. pose proof LO as LOK. unfold K_ALLOC in LOK.
              assert (Z64 : 0 <= z < 2^64).
              { destruct (rt_fpc_where2 E0 FSB0 PL0 z Hz) as [[ZI _]|RH]; [clear -ZI; lia| unfold rt_high2 in RH; clear -RH Tlo Thi' CQ1 CQ2 CC1 CC2 DQ1 DQ2 DD1 DD2 CEILB; lia]. }
              apply MU7. rewrite wa_unsigned by exact Z64. unfold BF_allocD.W4. pose proof TCTX as XT.
              assert (CTR : T + 2904 <= BF_allocD.ctr n T /\ BF_allocD.ctr n T + 8 <= T + 3160).
              { unfold BF_allocD.ctr. pose proof HCID as HC. destruct (from_primary n); [specialize (HC eq_refl); clear -HC| clear]; lia. }
              unfold BF_allocD.cb, BF_allocD.ub, BF_allocD.rz, BF_allocD.n8 in *.
              destruct (rt_fpc_where2 E0 FSB0 PL0 z Hz) as [[ZI NM]|RH].
              - destruct (n mod 8 =? 0); cbn [outside app]; generalize ZI Timg CTR; numk Z64 NUMS.
              - unfold rt_high2 in RH. destruct (n mod 8 =? 0); cbn [outside app].
                + split; [clear -RH LOC' Thi' CQ2 CC1 CC2 DQ2 DD1 DD2; lia|].
                  split; [generalize RH XT BD CC1 CC2 DD1 DD2; numk Z64 NUMS|].
                  split; [generalize RH XT BD CC1 CC2 DD1 DD2; numk Z64 NUMS|].
                  split; [generalize RH XT BD CC1 CC2 DD1 DD2; numk Z64 NUMS|].
                  split; [clear -RH XT CTp DTp CDp CC1 CC2 DD1 DD2 CQ1 DQ1 Tlo; lia|].
                  split; [clear -RH XT CTR CTp DTp CDp CC1 CC2 DD1 DD2 CQ1 DQ1 Tlo; lia| exact I].
                + split; [clear -RH LOC' Thi' CQ2 CC1 CC2 DQ2 DD1 DD2; lia|].
                  split; [generalize RH XT BD CC1 CC2 DD1 DD2; numk Z64 NUMS|].
                  split; [generalize RH XT BD CC1 CC2 DD1 DD2; numk Z64 NUMS|].
                  split; [generalize RH XT BD CC1 CC2 DD1 DD2; numk Z64 NUMS|].
                  split; [generalize RH CQ4 DQ4 CC1 CC2 DD1 DD2; numk Z64 NUMS|].
                  split; [clear -RH XT CTp DTp CDp CC1 CC2 DD1 DD2 CQ1 DQ1 Tlo; lia|].
                  split; [clear -RH XT CTR CTp DTp CDp CC1 CC2 DD1 DD2 CQ1 DQ1 Tlo; lia| exact I]. }
         (* [comment removed for export] *)
         (* [comment removed for export] *)
         assert (run_cell : forall (mx : mem) (Ax : Z) (N k : nat) (v : byte), rw_cells bsegs mx Ax [CB N (repeat v N)] -> (k < N)%nat -> rw_cells bsegs mx (Ax + Z.of_nat k) [C1 v]).
         { clear. intros mx Ax N k v RC HK. pose proof (BF_tkit.u8arr_of_cells mx _ _ RC) as U. cbn [cells_bytes cbytes app] in U. rewrite ?app_nil_r in U.
           eapply (BF_tkit.u8arr_cell mx _ _ k (C1 v)); [exact U| rewrite repeat_length; cbn; lia| exact I|].
           cbn [cbytes csize]. rewrite skipn_repeat'. replace (N - k)%nat with (Datatypes.S (N - k - 1))%nat by lia. reflexivity. }
         (* [comment removed for export] *)
         assert (AG45sh : forall z, kShadowBase + ab / 8 <= z < kShadowBase + (ab + ca_span n) / 8 -> (z < kShadowBase + BF_allocC.ub n ab / 8 \/ kShadowBase + BF_allocC.ub n ab / 8 + BF_allocC.n8 n <= z) -> m5 (wa z) = m4 (wa z)).
         { intros z Hz Hu. apply AG45'; [numk Hz NUMS| numk Hz NUMS| exact Hu]. }
         assert (AG57sh : forall z, kShadowBase + ab / 8 <= z < kShadowBase + (ab + ca_span n) / 8 -> (z = kShadowBase + BF_allocC.ub n ab / 8 + BF_allocC.n8 n -> n mod 8 = 0) -> m7 (wa z) = m5 (wa z)).
         { intros z Hz Hu. apply MU7. rewrite wa_unsigned by (numk Hz NUMS). unfold BF_allocD.W4. pose proof TCTX as XT. pose proof HCID as HC.
           destruct (n mod 8 =? 0) eqn:M8; [apply Z.eqb_eq in M8| apply Z.eqb_neq in M8]; cbn [outside app];
             unfold BF_allocD.cb, BF_allocD.ub, BF_allocD.rz, BF_allocD.n8, BF_allocD.ctr in *;
             (destruct (from_primary n); [specialize (HC eq_refl); generalize HC| clear HC]; generalize Hu M8; numk Hz NUMS). }
         assert (AG34sh : from_primary n = true -> forall z, kShadowBase + ab / 8 <= z < kShadowBase + (ab + ca_span n) / 8 -> m4 (wa z) = m3 (wa z)).
         { intros PR z Hz. apply (MU5p PR). rewrite wa_unsigned by (numk Hz NUMS). cbn [outside]. split; [numk Hz NUMS| exact I]. }
         (* [comment removed for export] *)
         set (NL := Z.to_nat (BF_allocC.rz n / 8)). set (NR := Z.to_nat ((ca_span n - BF_allocC.rz n - rounded n) / 8)).
         assert (RLS : from_primary n = false -> RL n ab = ca_span n - BF_allocC.rz n - rounded n).
         { intros PR. unfold RL, ALSZ, ca_span, BF_allocC.ub, kPageSize. rewrite PR. clear. lia. }
         assert (NLZ : Z.of_nat NL = BF_allocC.rz n / 8) by (subst NL; unfold BF_allocC.rz; clear -RZ; rewrite Z2Nat.id by (Z.div_mod_to_equations; lia); reflexivity).
         assert (NRZ : Z.of_nat NR = (ca_span n - BF_allocC.rz n - rounded n) / 8) by (subst NR; unfold BF_allocC.rz in *; clear -RZ USPANu; rewrite Z2Nat.id by (Z.div_mod_to_equations; lia); reflexivity).
         assert (SPZ : Z.of_nat (Z.to_nat (ca_span n / 8)) = ca_span n / 8) by (clear -SPANPOS; rewrite Z2Nat.id by (Z.div_mod_to_equations; lia); reflexivity).
         (* [comment removed for export] *)
         assert (L4 : rw_cells bsegs m4 (kShadowBase + ab / 8) [CB NL (repeat (Z_to_bv 8 250) NL)]).
         { pose proof SHX5 as SX. pose proof BSHP as BP. destruct (from_primary n) eqn:PR.
           - pose proof (rw_cells_split_CB bsegs m' (kShadowBase + ab / 8) [] (Z.to_nat (ca_span n / 8)) shj [] [NL; (Z.to_nat (ca_span n / 8) - NL)%nat] BSH
                           ltac:(cbn [sum_nat]; generalize NLZ SPZ; unfold BF_allocC.rz in *; clear -RZ USPANu RG1 Hn SP8' RZ8; Z.div_mod_to_equations; lia)) as X.
             cbn [app mk_CB_cells] in X. pose proof (BF_depot3.rw_cells_app_split bsegs m' _ [CB NL (take NL shj)] _ X) as [XL _]. clear X.
             rewrite (BP eq_refl) in XL. rewrite BF_lalloc3.firstn_repeat' in XL by (generalize NLZ SPZ; unfold BF_allocC.rz in *; clear -RZ USPANu RG1 Hn SP8' RZ8; Z.div_mod_to_equations; lia).
             eapply (rw_cells_agree bsegs); [| eapply (rw_cells_agree bsegs); [| exact XL]].
             + cbn. intros z Hz. rewrite ?repeat_length, ?Nat.add_0_r, ?NLZ in Hz. apply (AG34sh eq_refl). numk Hz NUMS.
             + cbn. intros z Hz. rewrite ?repeat_length, ?Nat.add_0_r, ?NLZ in Hz. apply AGsh. numk Hz NUMS.
           - exact (proj1 (SX eq_refl)). }
         assert (LRUN7 : rw_cells bsegs m7 (kShadowBase + ab / 8) [CB NL (repeat (Z_to_bv 8 250) NL)]).
         { eapply (rw_cells_agree bsegs); [| eapply (rw_cells_agree bsegs); [| exact L4]].
           + cbn. intros z Hz. rewrite ?repeat_length, ?Nat.add_0_r, ?NLZ in Hz. apply AG57sh; [numk Hz NUMS| intros EQ; exfalso; generalize EQ; numk Hz NUMS].
           + cbn. intros z Hz. rewrite ?repeat_length, ?Nat.add_0_r, ?NLZ in Hz. apply AG45sh; numk Hz NUMS. }
         (* [comment removed for export] *)
         pose proof NDS' as ND. unfold AsanRepX2B.nd_same in ND. destruct ND as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ETS & _).
         assert (LG : AsanRepTailB.tlarge n = negb (from_primary n)).
         { unfold AsanRepTailB.tlarge, needed. destruct (from_primary n) eqn:PR; unfold from_primary in PR; cbn [negb];
           [apply Z.leb_le in PR; apply Z.ltb_ge; clear -PR; lia| apply Z.leb_gt in PR; apply Z.ltb_lt; clear -PR RZ; lia]. }
         assert (BS1 : blocks_sep E0 a1) by exact (blocks_sep_of E0 a1 mo' ENV0 WF2 AK2).
         pose proof ENV0 as ENV0'. destruct ENV0' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & IMGR & _).
         assert (IMG_IN : forall r, In r (arep_img_ranges E0 ++ depot_static E0) -> fst (ae_img E0) <= fst r /\ fst r + snd r <= fst (ae_img E0) + snd (ae_img E0)).
         { intros r Hr. pose proof (IMGR r Hr) as X. rewrite EI1. clear -X EI2. lia. }
         assert (NFP1 : forall x, ab <= x < ab + ca_span n -> ~ arep_fp E0 (DepotFP E0) a1 x).
         { intros x Hx. unfold ca_span in Hx. exact (AsanRepNewB.newblk_fp_free E0 a a1 n ab Hwf WF2 Ech BS1 IMG_IN Hn SIDE x Hx). }
         assert (RXb : ARepX bsegs E0 (DepotR bsegs E0) a1 m2 ab (ab + ca_span n)).
         { refine (AsanRepX2B.ARepX_frame bsegs E0 [] [] a1 m' m2 ab (ab + ca_span n) WF2 BS1 IMGR _ G2 WM3 _ RX2); [clear -G1; lia|].
           intros x FPx NW. pose proof (fp_below_ceiling _ _ [] [] IMG_IN (DepotFP_where E0) _ _ WF2 BS1 FPx) as UBx.
           assert (Hx : 0 <= x < 2^64).
           { destruct (fp_locate _ _ [] [] IMG_IN (DepotFP_where E0) _ _ WF2 BS1 FPx) as [(r & Hr & R)|[[R _]|[R _]]].
             - pose proof (IMG_IN r Hr) as Y. clear -Y R EI1 EI2 UBx CEILB. lia.
             - unfold sh_band, kLowShadowBeg, kShadowBase in R. rewrite kHighShadowBeg_val in R. clear -UBx CEILB R. lia.
             - unfold app_addr in R. rewrite kHighMemBeg_val in R. clear -UBx CEILB R. lia. }
           apply AG23; [exact Hx|].
           destruct (Z_lt_le_dec x ab) as [LT|GE]; [left; unfold BF_allocB.cb, BF_allocB.rz; clear -LT RZ; lia|].
           destruct (Z_lt_le_dec x (ab + ca_span n)) as [LT2|GE2]; [exfalso; exact (NFP1 x (conj GE LT2) FPx)|].
           right. unfold BF_allocB.cb, BF_allocB.rz. clear -GE2 USPANu RG1 Hn. lia. }
         assert (RXc : ARepX bsegs E0 (DepotR bsegs E0) a2 m3 ab (ab + ca_span n)).
         { exact (AsanRepX3B.ARepX_dput_step bsegs E0 a1 a2 m2 m3 ab (ab + ca_span n) lo (usp - 128) NDS' WF2 RENV' LOC' RXb DR4 WM4 AG34d). }
         set (NM := Z.to_nat ((BF_allocC.rz n + rounded n) / 8)).
         assert (NMZ : Z.of_nat NM = (BF_allocC.rz n + rounded n) / 8) by (subst NM; unfold BF_allocC.rz; clear -RZ RG1 Hn; rewrite Z2Nat.id by (Z.div_mod_to_equations; lia); reflexivity).
         assert (EUR : kShadowBase + ab / 8 + Z.of_nat NM = kShadowBase + (BF_allocC.ub n ab + rounded n) / 8).
         { rewrite NMZ. unfold BF_allocC.ub, BF_allocC.rz in *. clear -RZ RZ8 G3 RG1 Hn. Z.div_mod_to_equations. lia. }
         (* [comment removed for export] *)
         assert (RR4 : rw_cells bsegs m4 (kShadowBase + (BF_allocC.ub n ab + rounded n) / 8) [CB NR (repeat (Z_to_bv 8 250) NR)]).
         { pose proof SHX5 as SX. pose proof BSHP as BP. pose proof RLS as RLS'. destruct (from_primary n) eqn:PR.
           - pose proof (rw_cells_split_CB bsegs m' (kShadowBase + ab / 8) [] (Z.to_nat (ca_span n / 8)) shj [] [NM; NR] BSH
                           ltac:(cbn [sum_nat]; generalize NMZ NRZ SPZ; unfold BF_allocC.rz in *; clear -RZ USPANu RG1 Hn SP8' RZ8; Z.div_mod_to_equations; lia)) as X.
             cbn [app mk_CB_cells] in X. pose proof (BF_depot3.rw_cells_app_split bsegs m' _ [CB NM (take NM shj)] _ X) as [_ XR]. clear X.
             cbn [cells_size csize] in XR. rewrite ?Nat.add_0_r in XR. rewrite EUR in XR.
             rewrite (BP eq_refl) in XR. rewrite BF_lalloc3.skipn_repeat', BF_lalloc3.firstn_repeat' in XR by (generalize NMZ NRZ SPZ; unfold BF_allocC.rz in *; clear -RZ USPANu RG1 Hn SP8' RZ8; Z.div_mod_to_equations; lia).
             eapply (rw_cells_agree bsegs); [| eapply (rw_cells_agree bsegs); [| exact XR]].
             + cbn. intros z Hz. rewrite ?repeat_length, ?Nat.add_0_r, ?NRZ in Hz. apply (AG34sh eq_refl). numk Hz NUMS.
             + cbn. intros z Hz. rewrite ?repeat_length, ?Nat.add_0_r, ?NRZ in Hz. apply AGsh. numk Hz NUMS.
           - pose proof (proj2 (SX eq_refl)) as XR. rewrite (RLS' eq_refl) in XR. fold NR in XR. exact XR. }
         assert (RRUN7 : rw_cells bsegs m7 (kShadowBase + (BF_allocC.ub n ab + rounded n) / 8) [CB NR (repeat (Z_to_bv 8 250) NR)]).
         { eapply (rw_cells_agree bsegs); [| eapply (rw_cells_agree bsegs); [| exact RR4]].
           + cbn. intros z Hz. rewrite ?repeat_length, ?Nat.add_0_r, ?NRZ in Hz. apply AG57sh; [numk Hz NUMS| intros EQ; generalize EQ; numk Hz NUMS].
           + cbn. intros z Hz. rewrite ?repeat_length, ?Nat.add_0_r, ?NRZ in Hz. apply AG45sh; numk Hz NUMS. }
         (* [comment removed for export] *)
         assert (ZRUN7 : 8 <= n -> rw_cells bsegs m7 (kShadowBase + BF_allocC.ub n ab / 8) [CB (Z.to_nat (BF_allocC.n8 n)) (repeat (Z_to_bv 8 0) (Z.to_nat (BF_allocC.n8 n)))]).
         { intros N8. eapply (rw_cells_agree bsegs); [| exact (ZSH5 N8)]. cbn. intros z Hz. rewrite ?repeat_length, ?Nat.add_0_r in Hz. rewrite Z2Nat.id in Hz by (clear -N8Ru; unfold BF_allocC.n8; lia).
           apply AG57sh; [numk Hz NUMS| intros EQ; exfalso; generalize EQ; numk Hz NUMS]. }
         eapply (AsanRepTailB.ARep_tail bsegs E0 a2 m3 m7 lo n ab id);
           [ clear -Hn; lia
           | rewrite BF_atail.tspan_ca_span; exact RXc
           | exact WFd | exact WF' | exact FRESH' | exact RENV' | exact BLK' | exact NFP'
           | exact (wmono_trans _ _ _ _ WM5 (wmono_trans _ _ _ _ WM45 WM7))
           | | exact LOC' | | | | | | ].
         - (* [comment removed for export] *)
           intros z Hz NF. unfold AsanRepTailB.FPWt in NF. rewrite BF_atail.tspan_ca_span, LG in NF. unfold AsanRepTailB.tcid, kThrStats in NF.
           pose proof LO as LOK. unfold K_ALLOC in LOK. pose proof HCID as HC.
           rewrite MU7.
           2:{ rewrite wa_unsigned by exact Hz. unfold BF_allocD.W4, BF_allocD.cb, BF_allocD.ub, BF_allocD.rz, BF_allocD.n8, BF_allocD.ctr, BF_allocD.cid.
               destruct (n mod 8 =? 0) eqn:M8; [apply Z.eqb_eq in M8| apply Z.eqb_neq in M8]; cbn [outside app negb] in NF |- *;
                 (destruct (from_primary n); cbn [negb] in NF; clear HC; repeat match goal with |- _ /\ _ => split end; try exact I; generalize NF LOK M8; numk Hz NUMS). }
           rewrite AG45'; [| exact Hz| generalize NF LOK; numk Hz NUMS| generalize NF; numk Hz NUMS].
           apply AG45; [exact Hz| generalize NF LOK; numk Hz NUMS| generalize NF; numk Hz NUMS| generalize NF; numk Hz NUMS| generalize NF; numk Hz NUMS].
         - (* [comment removed for export] *)
           exists b1'. split; [exact HB7|]. replace (req n) with n by (unfold req; clear -Hn; lia). rewrite Z.div_small by (clear -Hn; lia). exact HDR7.
         - (* [comment removed for export] *)
           intros RZ16. destruct (MAG7 RZ16) as [mrest MG]. pose proof (BF_depot3.rw_cells_app_split bsegs m7 _ [C8 (Z_to_bv 64 kAllocBegMagicVal); C8 (Z_to_bv 64 (BF_allocD.cb n ab))] [CB _ mrest] MG) as [MG1 _]. exact MG1.
         - (* [comment removed for export] *)
           intros g Hg. rewrite BF_atail.tspan_ca_span in Hg.
           pose proof (AsanRepTailB.chunk_shadow_alloc n ab id (8 * g)) as CS. cbv zeta in CS. rewrite CS. clear CS.
           replace (req n) with n by (unfold req; clear -Hn; lia). unfold AsanRepTailB.tub, AsanRepTailB.trz.
           destruct (8 * g <? ab + rz_size n) eqn:C1.
           + apply Z.ltb_lt in C1.
             replace (kShadowBase + g) with (kShadowBase + ab / 8 + Z.of_nat (Z.to_nat (g - ab / 8))) by (generalize NLZ; numk Hg NUMS).
             apply (run_cell m7 _ NL _ _ LRUN7). generalize NLZ C1; numk Hg NUMS.
           + apply Z.ltb_ge in C1. destruct (8 * g <? ab + rz_size n + n / 8 * 8) eqn:C2.
             * apply Z.ltb_lt in C2.
               assert (N8 : 8 <= n) by (generalize C1 C2; numk Hg NUMS).
               replace (kShadowBase + g) with (kShadowBase + BF_allocC.ub n ab / 8 + Z.of_nat (Z.to_nat (g - BF_allocC.ub n ab / 8))) by (generalize C1; numk Hg NUMS).
               apply (run_cell m7 _ _ _ _ (ZRUN7 N8)). generalize C1 C2; numk Hg NUMS.
             * apply Z.ltb_ge in C2. destruct (8 * g <? ab + rz_size n + n) eqn:C3.
               -- apply Z.ltb_lt in C3. assert (NM8 : n mod 8 <> 0) by (generalize C2 C3; numk Hg NUMS).
                  replace (kShadowBase + g) with (kShadowBase + (BF_allocD.ub n ab + 8 * BF_allocD.n8 n) / 8) by (unfold BF_allocD.ub, BF_allocD.rz, BF_allocD.n8; generalize C2 C3; numk Hg NUMS).
                  exact (GRAN7 NM8).
               -- apply Z.ltb_ge in C3.
                  replace (kShadowBase + g) with (kShadowBase + (BF_allocC.ub n ab + rounded n) / 8 + Z.of_nat (Z.to_nat (g - (BF_allocC.ub n ab + rounded n) / 8))) by (generalize NRZ C3; numk Hg NUMS).
                  apply (run_cell m7 _ NR _ _ RRUN7). generalize NRZ C3; numk Hg NUMS.
         - (* [comment removed for export] *)
           rewrite ETS. replace (req n) with n by (unfold req; clear -Hn; lia). rewrite !BF_tkit.zw_wrap_add in ST7. exact ST7.
         - (* [comment removed for export] *)
           intros LGT. rewrite LG in LGT. pose proof CNT7 as C7. destruct (from_primary n); [discriminate|]. rewrite ETS.
           rewrite BF_tkit.zw_wrap_add in C7. replace (T + kThrStats + 104) with (T + 2904) by (unfold kThrStats; clear; lia). exact C7.
         - (* [comment removed for export] *)
           intros LGF. rewrite LG in LGF. pose proof CNT7 as C7. destruct (from_primary n); [|discriminate]. destruct C7 as [C7 _]. rewrite ETS.
           rewrite BF_tkit.zw_wrap_add in C7. replace (T + kThrStats + 112 + 8 * AsanRepTailB.tcid n) with (T + 2912 + 8 * BF_allocD.cid n) by (unfold kThrStats, AsanRepTailB.tcid, BF_allocD.cid; clear; lia).
           exact C7.
         }
    1: { (* [comment removed for export] *)
         eexists. split; [exact MUt|].
         pose proof (BF_atail.atail_wfacts E0 PL0 ENV0 PL0OK a a1 a2 mo3 n ab id (bst_key len ws) _ _ _ _ _ _ _ _
                       Hwf RO0 QB0 DI0 BI0 CS0 ABUD Hn NBIG RUNA SS2 SIDE KEY32 RUND WFd AK4 (conj EI1 EI2)
                       (conj End (conj Eks (conj Efr (conj Enb (conj Esb (conj Estd (conj Ech (conj Edead (conj Etq Egq))))))))) ENP ERS)
           as (W1 & W2 & W3 & W4f). rewrite ?BF_atail.tspan_ca_span in W1, W2, W3, W4f.
         pose proof (hoareW_arun _ _ _ _ _ _ _ _ _ _ (AsanRepX3B.depot_put_blocks_mono E0 a1 (bst_key len ws)) eq_refl RUND) as [NBM SBM].
         pose proof NDS' as ND. unfold AsanRepX2B.nd_same in ND. destruct ND as (_ & _ & _ & _ & _ & _ & _ & SEC21 & _).
         pose proof Hwf as (_ & _ & _ & _ & _ & WSa & _). destruct WSa as (_ & _ & WS3a & _).
         pose proof WE as WE'. pose proof WE' as (_ & WEhi & WErs & WEsp & _). change kSpaceSize with 137438953472 in WEsp. rewrite kHighMemBeg_val in WEhi.
         pose proof WE' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & WE29 & _).
         assert (SECm : forall sc, In sc (as_sec a) -> In sc (as_sec a2)).
         { intros sc Hsc. rewrite SEC21. exact (hoareW_arun _ _ _ _ _ _ _ _ _ _ (BF_atail.ca_op_sec E0 a n) eq_refl RUNA sc Hsc). }
         assert (STKa : forall x y, lo <= x -> y <= usp -> aw_ok E0 a (tail_st n ab id a2) lo usp (x, y)) by (intros x y Hx Hy; left; cbn [fst snd]; clear -Hx Hy; lia).
         assert (THRa : forall x y, T + 2800 <= x -> y <= T + 3168 -> aw_ok E0 a (tail_st n ab id a2) lo usp (x, y)).
         { intros x y Hx Hy. right; right; left. exists (T + kThrStats, 112 + 8 * 32). split; [unfold arep_thr_ranges; do 5 right; left; reflexivity| cbn [fst snd]; unfold kThrStats; clear -Hx Hy; lia]. }
         assert (STKv : forall x y blo bsz, In (blo, bsz) (live_blocks a) -> lo <= x -> y <= x \/ y <= blo \/ blo + bsz <= x).
         { intros x y blo bsz LIVE Hx. destruct (live_block_where E0 a blo bsz Hwf LIVE) as (_ & B1 & _). right; right. clear -B1 Hx LOC' CEILB. lia. }
         assert (THRv : forall x y blo bsz, In (blo, bsz) (live_blocks a) -> T <= x -> y <= T + 4096 -> y <= x \/ y <= blo \/ blo + bsz <= x).
         { intros x y blo bsz LIVE Hx Hy. destruct (live_block_off_thread E0 a blo bsz Hwf LIVE) as [_ [X|X]]; [right; right| right; left]; clear -X Hx Hy; lia. }
         assert (BLKv : forall x y blo bsz, In (blo, bsz) (live_blocks a) -> ab <= x -> y <= ab + ca_span n -> y <= x \/ y <= blo \/ blo + bsz <= x).
         { intros x y blo bsz LIVE Hx Hy. destruct (W3 blo bsz LIVE) as [X|X]; [right; right| right; left]; clear -X Hx Hy; lia. }
         assert (SHv : forall x y blo bsz, In (blo, bsz) (live_blocks a) -> kShadowBase + ab / 8 <= x -> y <= kShadowBase + (ab + ca_span n + 7) / 8 -> y <= x \/ y <= blo \/ blo + bsz <= x).
         { intros x y blo bsz LIVE Hx Hy. destruct (W4f blo bsz LIVE) as [X|X]; [right; right| right; left]; clear -X Hx Hy; lia. }
         assert (TLS : as_sec (tail_st n ab id a2) = as_sec a2) by (clear; unfold AsanRepTailB.tail_st; destruct a2; reflexivity).
         assert (TLN : as_node_blocks (tail_st n ab id a2) = as_node_blocks a2) by (clear; unfold AsanRepTailB.tail_st; destruct a2; reflexivity).
         assert (TLT : as_store_blocks (tail_st n ab id a2) = as_store_blocks a2) by (clear; unfold AsanRepTailB.tail_st; destruct a2; reflexivity).
         assert (CTR : T + 2904 <= BF_allocD.ctr n T /\ BF_allocD.ctr n T + 8 <= T + 3160).
         { unfold BF_allocD.ctr. pose proof HCID as HC. destruct (from_primary n); [specialize (HC eq_refl); clear -HC| clear]; lia. }
         pose proof LO as LOK. unfold K_ALLOC in LOK.
         split.
         - (* [comment removed for export] *)
           apply Forall_app; split; [apply Forall_app; split| apply Forall_app; split; [apply Forall_app; split| apply Forall_app; split; [apply Forall_app; split|]]].
           + constructor; [apply STKa; clear -LO'; lia| constructor].
           + eapply Forall_impl; [| exact FW]. intros [x y] Hxy.
             eapply (BF_caT2.aw_ok_mono E0 a a (tail_st n ab id a2) a1 lo (usp - 128) usp (x, y)); [| | | clear; lia| exact Hxy].
             * intros sc [Hs|Hs]; [left; exact Hs| right]. rewrite TLS, SEC21. exact Hs.
             * intros b Hb. rewrite TLN. apply NBM. exact Hb.
             * intros b Hb. rewrite TLT. apply SBM. exact Hb.
           + constructor; [apply W1; unfold BF_allocB.cb, BF_allocB.rz; generalize USPANu RG1 RZ Hn; clear; lia| constructor].
           + eapply Forall_impl; [| exact FWd]. intros [x y] X. unfold dput_w_ok in X. cbn [fst snd] in X. unfold aw_ok. cbn [fst snd].
             destruct X as [X|[(r & Hr & X1 & X2)|[(b & Hb & X1 & X2)|(b & Hb & X1 & X2)]]].
             * left. clear -X; lia.
             * right; left. unfold depot_static in Hr. rewrite IC0 in Hr. cbn [aic_theDepot aic_stackStore both_ic] in Hr.
               destruct Hr as [<-|[<-|[]]]; cbn [fst snd] in X1, X2.
               -- exists (aic_theDepot both_ic, 0x440010). split; [unfold img_mut; do 3 right; left; reflexivity| cbn [fst snd aic_theDepot both_ic]; clear -X1 X2; lia].
               -- exists (aic_stackStore both_ic, 0x10010). split; [unfold img_mut; do 4 right; left; reflexivity| cbn [fst snd aic_stackStore both_ic]; clear -X1 X2; lia].
             * do 6 right; left. exists b. split; [rewrite TLN; exact Hb| clear -X1 X2; lia].
             * do 7 right; left. exists b. split; [rewrite TLT; exact Hb| clear -X1 X2; lia].
           + constructor; [apply STKa; clear -LO'; lia|].
             constructor; [apply W1; unfold BF_allocC.cb, BF_allocC.rz; generalize USPANu RG1 RZ Hn; clear; lia|].
             constructor; [apply W2; [clear; lia| unfold BF_allocC.rz; generalize USPANu RG1 RZ Hn G3 RZ8; clear; intros; Z.div_mod_to_equations; lia]|].
             constructor; [apply W2; [unfold BF_allocC.ub, BF_allocC.rz; generalize RG1 RZ Hn G3 RZ8; clear; intros; Z.div_mod_to_equations; lia| clear; Z.div_mod_to_equations; lia]| constructor].
           + constructor; [apply STKa; clear -LOK; lia|].
             constructor; [apply W2; unfold BF_allocC.ub, BF_allocC.rz, BF_allocC.n8; generalize USPANu RG1 RZ Hn G3 RZ8 N8Ru; clear; intros; Z.div_mod_to_equations; lia| constructor].
           + unfold BF_allocD.W4. apply Forall_app; split; [| apply Forall_app; split].
             * constructor; [apply STKa; clear; lia|]. constructor; [apply W1; unfold BF_allocD.cb, BF_allocD.rz; generalize USPANu RG1 RZ Hn; clear; lia|].
               constructor; [apply W1; generalize SPANPOS; clear; lia|]. constructor; [apply W1; unfold BF_allocD.ub, BF_allocD.rz; generalize USPANu RG1 RZ Hn; clear; lia| constructor].
             * destruct (n mod 8 =? 0) eqn:M8; [constructor|]. apply Z.eqb_neq in M8.
               constructor; [apply W2; unfold BF_allocD.ub, BF_allocD.rz, BF_allocD.n8; generalize USPANu RG1 RZ Hn G3 RZ8 N8Ru M8; clear; intros; Z.div_mod_to_equations; lia| constructor].
             * constructor; [apply THRa; clear; lia|]. constructor; [apply THRa; clear -CTR; lia| constructor].
         - match goal with |- ?g => idtac "J7f2-OK" end.
           apply Forall_app; split; [apply Forall_app; split| apply Forall_app; split; [apply Forall_app; split| apply Forall_app; split; [apply Forall_app; split|]]].
           + constructor; [cbn [fst snd]; intros blo bsz LIVE; apply (STKv _ _ blo bsz LIVE); clear -LO'; lia| constructor].
           + exact FWB.
           + constructor; [cbn [fst snd]; intros blo bsz LIVE; apply (BLKv _ _ blo bsz LIVE); unfold BF_allocB.cb, BF_allocB.rz; generalize USPANu RG1 RZ Hn; clear; lia| constructor].
           + (* [comment removed for export] *)
             apply Forall_forall. intros [x y] Hin blo bsz LIVE. cbn [fst snd].
             pose proof (proj1 (Forall_forall _ _) FWd _ Hin) as X. unfold dput_w_ok in X. cbn [fst snd] in X.
             destruct (live_block_where E0 a blo bsz Hwf LIVE) as (Lw0 & Lw1 & Lw2 & Lw3).
             destruct X as [X|X]; [right; right; clear -X Lw1 LOC' CEILB; lia|].
             assert (DZ : forall z, x <= z < y -> DepotFPd E0 a2 z).
             { intros z Hz. destruct X as [(r & Hr & X1 & X2)|[(b & Hb & X1 & X2)|(b & Hb & X1 & X2)]].
               - left. exists r. split; [unfold depot_static in Hr; destruct Hr as [<-|[<-|[]]]; [left| right; left]; reflexivity| clear -Hz X1 X2; lia].
               - right; left. exists b. split; [exact Hb| clear -Hz X1 X2; lia].
               - right; right. exists b. split; [exact Hb| clear -Hz X1 X2; lia]. }
             destruct (Z_lt_le_dec x y) as [O0|O0]; [| left; exact O0]. destruct (Z_lt_le_dec blo y) as [O1|O1]; [| right; left; exact O1].
             destruct (Z_lt_le_dec x (blo + bsz)) as [O2|O2]; [| right; right; exact O2]. exfalso.
             set (z := Z.max x blo).
             assert (Zin : x <= z < y /\ blo <= z < blo + bsz) by (subst z; clear -O0 O1 O2 Lw0; lia).
             destruct (BF_deallocT1.dfp_cases E0 PL0 ENV0 PL0OK a2 mo3 z IC0 AK4 WFd EI1 EI2 (DZ z (proj1 Zin))) as [STz|(b & bl & R & Bb0 & Bce & Bbd & Brs & Bsc & BTb & BAb)].
             * destruct Lw3 as [[S1 S2]|(sc & Hsc & S1 & S2)]; [clear -STz Zin S1 WEhi WErs; lia|].
               destruct (WS3a sc Hsc) as (_ & _ & _ & _ & _ & _ & SR). pose proof (SR _ WE29) as X1. rewrite EI1 in X1. cbn [fst snd] in X1. clear -STz Zin S1 S2 X1 EI2. lia.
             * change kResvLen with 137439023104 in Brs.
               destruct Lw3 as [[S1 S2]|(sc & Hsc & S1 & S2)]; [unfold kSpaceSize in S2; clear -R Zin S1 S2 Brs WErs WEsp; lia|].
               destruct (Bsc sc (SECm sc Hsc)); clear -R Zin S1 S2 H; lia.
           + constructor; [cbn [fst snd]; intros blo bsz LIVE; apply (STKv _ _ blo bsz LIVE); clear -LO'; lia|].
             constructor; [cbn [fst snd]; intros blo bsz LIVE; apply (BLKv _ _ blo bsz LIVE); unfold BF_allocC.cb, BF_allocC.rz; generalize USPANu RG1 RZ Hn; clear; lia|].
             constructor; [cbn [fst snd]; intros blo bsz LIVE; apply (SHv _ _ blo bsz LIVE); [clear; lia| unfold BF_allocC.rz; generalize USPANu RG1 RZ Hn G3 RZ8; clear; intros; Z.div_mod_to_equations; lia]|].
             constructor; [cbn [fst snd]; intros blo bsz LIVE; apply (SHv _ _ blo bsz LIVE); [unfold BF_allocC.ub, BF_allocC.rz; generalize RG1 RZ Hn G3 RZ8; clear; intros; Z.div_mod_to_equations; lia| clear; Z.div_mod_to_equations; lia]| constructor].
           + constructor; [cbn [fst snd]; intros blo bsz LIVE; apply (STKv _ _ blo bsz LIVE); clear -LOK; lia|].
             constructor; [cbn [fst snd]; intros blo bsz LIVE; apply (SHv _ _ blo bsz LIVE); unfold BF_allocC.ub, BF_allocC.rz, BF_allocC.n8; generalize USPANu RG1 RZ Hn G3 RZ8 N8Ru; clear; intros; Z.div_mod_to_equations; lia| constructor].
           + unfold BF_allocD.W4. apply Forall_app; split; [| apply Forall_app; split].
             * constructor; [cbn [fst snd]; intros blo bsz LIVE; apply (STKv _ _ blo bsz LIVE); clear; lia|].
               constructor; [cbn [fst snd]; intros blo bsz LIVE; apply (BLKv _ _ blo bsz LIVE); unfold BF_allocD.cb, BF_allocD.rz; generalize USPANu RG1 RZ Hn; clear; lia|].
               constructor; [cbn [fst snd]; intros blo bsz LIVE; apply (BLKv _ _ blo bsz LIVE); generalize SPANPOS; clear; lia|].
               constructor; [cbn [fst snd]; intros blo bsz LIVE; apply (BLKv _ _ blo bsz LIVE); unfold BF_allocD.ub, BF_allocD.rz; generalize USPANu RG1 RZ Hn; clear; lia| constructor].
             * destruct (n mod 8 =? 0) eqn:M8; [constructor|]. apply Z.eqb_neq in M8.
               constructor; [cbn [fst snd]; intros blo bsz LIVE; apply (SHv _ _ blo bsz LIVE); unfold BF_allocD.ub, BF_allocD.rz, BF_allocD.n8; generalize USPANu RG1 RZ Hn G3 RZ8 N8Ru M8; clear; intros; Z.div_mod_to_equations; lia| constructor].
             * constructor; [cbn [fst snd]; intros blo bsz LIVE; apply (THRv _ _ blo bsz LIVE); clear; lia|].
               constructor; [cbn [fst snd]; intros blo bsz LIVE; apply (THRv _ _ blo bsz LIVE); clear -CTR; lia| constructor]. }
  }
  destruct CASES as [[N8 ->]|[N8 (xra' & a0' & a1' & a2' & ->)]].
  - (* [comment removed for export] *)
    eapply (poison0_srz E0 FSB0 HR0 L0 RES0 EB0 HR0_ok ENV0 LS_L0 HS_L0 RES0_low (sA a2 s) [] [] ltac:(rewrite aps_alloc_sA; exact WFd)
              (wz 0x32ec4) gp tp t0' t1' t2' s0' (wz n) a3' a4' a5' a6' a7' (wz ab) (wz (needed n)) (wz (BF_allocC.ub n ab)) (wz (BF_allocC.cb n ab)) (wz (8 * BF_allocC.n8 n)) (wz B) (wz 0) s9' (wz T) (wz 1) t3' t4' t5' t6'
              F fc m4 mo4 (usp + -128) lo R5 R5' (BF_allocC.ub n ab) (8 * BF_allocC.n8 n) cnr (take (Z.to_nat (BF_allocC.n8 n)) (drop (Z.to_nat (BF_allocC.rz n / 8)) shj)) K KN ATK5).
    + rewrite aps_alloc_sA. exact AK5.
    + exact SPA4.
    + exact SK5.
    + exact LOC'.
    + pose proof LO as X; unfold K_ALLOC in X; clear -X; lia.
    + clear -UB BA AHI LEN; unfold zlen in *; lia.
    + exact MI5.
    + exact P0S4.
    + unfold BF_allocC.ub, BF_allocC.rz; clear -G3 RZM; Z.div_mod_to_equations; lia.
    + clear; Z.div_mod_to_equations; lia.
    + clear -N8R; lia.
    + unfold BF_allocC.ub, BF_allocC.rz; clear -G1 RZ; lia.
    + unfold BF_allocC.ub, BF_allocC.rz in *; clear -G2 N8R USPAN; lia.
    + rewrite kHighMemBeg_val; rewrite ?kHighMemBeg_val in G6; unfold BF_allocC.ub, BF_allocC.rz in *; clear -G6 N8R N8 USPAN RZ; lia.
    + intros moX _ x k Hx Hk. apply (PBSHX moX); unfold BF_allocC.ub, BF_allocC.rz in *; [clear -Hx RZ G1; Z.div_mod_to_equations; lia| clear -Hk N8R USPAN RZ G1; Z.div_mod_to_equations; lia].
    + replace (8 * BF_allocC.n8 n / 8) with (BF_allocC.n8 n) by (clear; rewrite Z.mul_comm, Z.div_mul; [reflexivity| lia]). exact XU4.
    + intros ms6 mo6 P6P.
      destruct P6P as (q0 & q1 & q2 & qa0 & qa1 & qa2 & qa3 & qa4 & qa5 & qa6 & qa7 & q3 & q4 & q5 & q6 & m6 & -> & MI6 & SK6 & WM6 & MU6 & ZSH6 & P0S6 & ATK6 & AK6 & Qfs6 & Qfds6 & Qtid6).
      rewrite unsigned_lit in SK6, MU6 by (clear -USPR' LO' LOC' CEILB; lia).
      replace (ret_pc (Z_to_bv 64 208580)) with (Z_to_bv 64 208580 : word) by (apply bv_eq; vm_compute; reflexivity).
      rewrite aps_alloc_sA in AK6.
      eapply (JOIN m6 mo6); [exact MI6| exact SK6| exact WM6| | | exact ATK6| exact AK6| exact Qfs6| exact Qfds6| exact Qtid6].
      * intros z Hz Z1 Z2. apply MU6. rewrite wa_unsigned by exact Hz. cbn. clear -Z1 Z2. split; [lia| split; [Z.div_mod_to_equations; lia| exact I]].
      * intros _. replace (Z.to_nat (BF_allocC.n8 n)) with (Z.to_nat (8 * BF_allocC.n8 n / 8)) by (f_equal; clear; Z.div_mod_to_equations; lia). exact ZSH6.
  - (* [comment removed for export] *)
    assert (N80 : 8 * BF_allocC.n8 n = 0) by (unfold BF_allocC.n8; clear -N8 Hn; Z.div_mod_to_equations; lia). rewrite N80 in JOIN.
    eapply (JOIN m4 mo4); [exact MI5| exact SK5| apply wmono_refl| intros; reflexivity| intros N8'; exfalso; clear -N8 N8'; lia| exact ATK5| exact AK5| reflexivity| reflexivity| reflexivity].

Qed.

(* [comment removed for export] *)
Lemma allocate_call :
  realizes_cfg acfg bsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz A_INST) (wz n) (wz 8) (wz B) (wz 1) (wz 1) a6 a7
                                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                            F (wz A_ALLOCATE) fc None m (seg_rom bsegs)) mo) K.
Proof.
  apply stageA. intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s8' t3' t4' t5' t6' m1 m' mo1 mo' a1 ab junk MU1 WM1 MI1 FR1 AG1 POST.
  pose proof POST as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Ea0 & _). subst a0'.
  eapply (stageB t0' t1' t2' (wz ab) a1' a2' a3' a4' a5' a6' a7' s8' t3' t4' t5' t6' m1 m' mo1 mo' a1 ab junk MU1 WM1 MI1 FR1 AG1 POST).
  intros ms3 mo3 BP. exact (stageCD m1 m' mo1 mo' a1 ab junk ms3 mo3 MU1 WM1 MI1 FR1 AG1 POST BP).
Qed.
End Call.

(* [comment removed for export] *)
Theorem allocate_srz : allocate_srz_stmt E0 FSB0 HR0 L0 RES0 EB0 PL0.
Proof.
  unfold allocate_srz_stmt, allocate_srz_case. intros. eapply allocate_call; eassumption.
Qed.
End AllocT5.
End RC__1.
