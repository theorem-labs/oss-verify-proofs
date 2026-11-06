(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.B21 Require Import ImageA.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep ITree.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.Spec Require Import Prelim PrintfModel.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.G3 Require Import Printf_sn2.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.G3pm Require Import LeptFormatsPm LeptShapesPm LeptModelPm.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.B21 Require Import Layout.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.AG Require Import Shadow IcptSpec.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.B21 Require Import R_small R_m2s I_consts I_qck I_lkit RT_iface D_defs D_kit D_clx I_read I_lift
  F_achk F_pop_arg F_printf_iface I_pck I_pchead I_vprintfw I_vsnw2 I_vprintf RT_gaps_iface
  I_leptfmt I_leptargs I_leptimg I_leptlift_kit I_vsn_lept2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section Lift.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RIP : rip_stmt.
Hypothesis AF_SHW : forall Σ m p n, ART RT Σ m -> 0 < n -> rng_class RT Σ p n -> qc_words m p n /\ region_in_mem p n.
Hypothesis AF_PF : forall Σ m, ART RT Σ m -> pf_consts m.
Hypothesis AF_VSN : forall Σ m, ART RT Σ m -> vsncells m.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, kHighShadowEnd in *; lia.

(* [comment removed for export] *)
Lemma lept_args_strs : forall sh Σ m sp lo D ws, ART RT Σ m ->
  lept_args RT Σ m sp lo D (map is_s (map (fun it => fst (fst it)) sh)) ws ->
  exists strs, lstrs_ok m (lo + 64) D 2000 sh ws strs.
Proof using AF_SHW.
  induction sh as [|[[k nx] t] r IH]; intros Σ m sp lo D ws ART0 H; [exists []; exact I|].
  cbn [map fst is_s lept_args] in H. destruct ws as [|w ws']; [destruct k; destruct H|].
  destruct k; cbn [is_s] in H.
  - destruct H as [(str & (sl & BY & NZ & PAD & S0 & SB & (CS & _) & SEP) & L96) Hr].
    destruct (IH Σ m sp lo D ws' ART0 Hr) as (strs & Hs). exists (str :: strs). cbn [lstrs_ok hd tl]. split; [| exact Hs].
    exists sl. split; [exact BY|]. split; [exact NZ|]. split; [exact PAD|]. split; [exact S0|]. split; [lia|].
    split; [destruct (CS ltac:(lia)) as (AC & RC); apply (chkr_of RT AF_SHW Σ m _ _ ART0); [lia | exact AC | exact RC]|].
    split; [exact SEP | exact L96].
  - destruct (IH Σ m sp lo D ws' ART0 H) as (strs & Hs). exists strs. exact Hs.
  - destruct (IH Σ m sp lo D ws' ART0 H) as (strs & Hs). exists strs. exact Hs.
Qed.

Lemma lstrs_ok_length : forall sh m lo D dn ws strs, lstrs_ok m lo D dn sh ws strs -> (length sh <= length ws)%nat.
Proof.
  induction sh as [|[[k nx] t] r IH]; intros m lo D dn ws strs H; [cbn; lia|].
  destruct ws as [|w ws']; [destruct H|]. cbn [lstrs_ok length] in *.
  destruct k; [destruct H as [_ H]| |]; pose proof (IH _ _ _ _ _ _ H); lia.
Qed.

(* [comment removed for export] *)
Lemma lept_img_acc_lits : forall A f ks t0 sh, In (A, (f, ks, (t0, sh))) LEPT_IMG -> In (A, zlength f) ACC_LITS.
Proof.
  intros A f ks t0 sh Hin. unfold LEPT_IMG in Hin.
  repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <- <- <- <-; vm_compute; tauto|]). destruct Hin.
Qed.

Theorem vsnprintf_lept_ok : vsnprintf_lept_icontract RT.
Proof using AF RIP AF_SHW AF_PF AF_VSN.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m D ap fmt kinds
    w1 w2 w3 w4 w5 w6 w7 junk lo FDO MST -> -> -> -> -> ROWK VA QAP APH LARGS DST CDST D0 DLO DAP (g & SG1 & SG2) ART0 MI0 CALL.
  intros T c Hc Hk.
  set (ws := [w1; w2; w3; w4; w5; w6; w7]) in *.
  destruct (lept_fmts_img fmt kinds ROWK) as (f & ks & t0f & sh & ROWI & EK). subst kinds.
  assert (ROW : In (f, ks, (t0f, sh)) LEPT_SHAPES).
  { rewrite <- LEPT_IMG_rows. apply in_map_iff. exists (fmt, (f, ks, (t0f, sh))). split; [reflexivity | exact ROWI]. }
  destruct (lept_img_cstr fmt f ks t0f sh m ROWI MI0) as (CSF & A0 & AHI).
  destruct (lept_args_strs sh Σ m sp lo D ws ART0 LARGS) as (strs & LS).
  destruct (lept_fmt_split f ks t0f sh (lsargs sh ws strs) ROW) as (EF & _ & _ & _ & EKS & _).
  assert (LF1 : (1 <= length f)%nat) by (rewrite EF, !length_app; cbn [length]; lia). clear EF.
  assert (INF : In (f, ks) LEPT_FMT_LIST).
  { rewrite <- LEPT_SHAPES_cover. apply in_map_iff. exists (f, ks, (t0f, sh)). split; [reflexivity | exact ROW]. }
  pose proof (largs_lept_arg_ok sh ws strs m (lo + 64) D 2000 LS) as LAO. rewrite <- EKS in LAO.
  destruct (lept_model_run_b 1999 f ks (largs sh ws strs) ltac:(lia) INF LAO) as (P1 & FPC & r & d & o & MODEL & ER & RB & _ & _).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  destruct CALL as (ST & LOW & LOR & SPT & SPA).
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
  destruct (AF_PF Σ m ART0) as (PFC & IC & _ & ACCP & ACCX & ACCN & _).
  pose proof (AF_VSN Σ m ART0) as VSN.
  pose proof (Printf_pieces.zlength_nonneg' (d ++ o)) as O0.
  destruct CDST as (CD & DCL & DWR).
  assert (CHD : chkr m D 2000) by (destruct (CD ltac:(lia)) as (AC & RC); apply (chkr_of RT AF_SHW Σ m _ _ ART0); [lia | exact AC | exact RC]).
  pose proof (stk_split asegs m lo (lo + 64) usp ST ltac:(ul)) as (STa & STb).
  assert (STKC : forall p n, lo + 64 <= p -> p + n <= usp -> chkr m p n).
  { intros p n' H1 H2. destruct (Z_lt_le_dec 0 n') as [NP|NN].
    - apply (chkr_of RT AF_SHW Σ m p n' ART0); [ul| | ].
      + apply (af_acc_stack RT AF Σ m p n' ART0); ul.
      + right; right; left. ul.
    - split; [intros i Hi; lia| split; [intros i Hi; lia|]]. split; [| lia]. unfold region_in_mem, kLowMemEnd, kHighMemEnd. right. ul. }
  assert (LFZ : 0 < zlength f <= 0x27ef4) by (unfold zlength; lia).
  assert (FMTC : chkr m fmt (zlength f)).
  { apply (chkr_of RT AF_SHW Σ m _ _ ART0); [lia | | right; right; right; unfold zlength in *; ul].
    pose proof (af_acc_lits RT AF Σ m ART0) as FA. rewrite Forall_forall in FA.
    exact (FA (fmt, zlength f) (lept_img_acc_lits fmt f ks t0f sh ROWI)). }
  assert (ROD : rod_chk m).
  { split; [| split]; (apply (chkr_of RT AF_SHW Σ m _ _ ART0); [lia| assumption| right; right; right; unfold PFX_A, XDIG_A, NULLS_A; ul]). }
  assert (W1 : evt asegs (fun ms' => exists (m' : mem) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32),
      ms' = MS (mkR ra (Z_to_bv 64 usp) gp (Z_to_bv 64 TP_A) t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7'
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F' (ret_pc ra) fc' None m' (seg_rom asegs)
      /\ munch [(lo + 64, usp); (D, D + Z.of_nat 2000)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' (lo + 64) usp
      /\ exists junk', rw_cells asegs m' D [CB 2000 junk'])
                 (entry_st ra sp gp (Z_to_bv 64 TP_A) t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 2000) (Z_to_bv 64 fmt) (Z_to_bv 64 ap) a4 a5 a6 a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_vsnprintf m)).
  { unfold entry_st, e_vsnprintf. rewrite ESP.
    apply (ivsn_lept_evt2 RIP usp D 2000 ap (lo + 64) fmt f t0f ks sh ws strs junk 2000%nat r 1999 d o) with (g := g);
      first [ exact ROW | exact (lstrs_ok_length _ _ _ _ _ _ _ LS) | exact STb | exact (va7_area _ _ _ _ _ _ _ _ _ VA)
            | exact (va7_slots _ _ _ _ _ _ _ _ _ VA) | exact LS | exact MODEL | exact ER | exact FPC | exact P1 | exact CSF | exact DST
            | exact CHD | exact IC | exact STKC | exact FMTC | exact ROD | exact PFC | exact VSN | split; [exact SG1 | exact SG2]
            | exact MI0 | (unfold FX_Layout.STATIC_SPLIT; unfold zlength in *; lia) | (cbn [length ws]; ul) | lia | ul ]. }
  lazymatch type of W1 with evt asegs _ ?X =>
    assert (W1' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes asegs _ _ _ c (asta_evt' RT AF Σ PMc _ _ MST W1') Hc). intros c1 Hc1. apply Hk.
  exists (Z_to_bv 64 r). unfold icpt_post. eapply ASTA_conseq; [exact Hc1|]. intros ms PO.
  destruct PO as (m' & u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F' & fc' & -> & MU & WM & MI & ST' & DC).
  destruct (icpt_after RT AF Σ m m' usp lo _ D 2000 ART0 LOW ltac:(ul) ltac:(ul) MU WM) as (ART' & PRES).
  { intros x (l & h & Hin & Hx). cbn [In] in Hin. destruct Hin as [E|[E|[]]]; injection E as <- <-; [right; ul| left; lia]. }
  { intros i Hi. apply DCL. exact Hi. }
  assert (ST2 : stk asegs m' lo usp).
  { apply (stk_merge asegs m' lo (lo + 64) usp); [| exact ST'| ul].
    apply (stk_transport_disjoint asegs _ _ _ _ _ STa MU WM). cbn [disjoint_from].
    split; [left; replace (lo + (lo + 64 - lo)) with (lo + 64) by ring; reflexivity|]. split; [| exact I]. right. lia. }
  exists m'. split; [rewrite ESP; do 16 eexists; reflexivity|].
  split; [split; [exact ART'| split; [exact MI| split; [exact WM| exact ST2]]]|].
  split; [exact PRES | exact DC].
Qed.

End Lift.
