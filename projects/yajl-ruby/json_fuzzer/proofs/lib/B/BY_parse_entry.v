(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import InitMem SysStep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.MS Require Import MallocRep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim YajlBase YajlLeaf YajlBuf YajlLex YajlParser YajlFactsBuf.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RY_lib.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA AImages LazyModel NodesA Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import B_iface BYajlRep BYajl_iface BY_rz BY_hand.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac kill K := exfalso; revert K; unfold wz; rewrite ?unsigned_lit by lia; lia.

(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac aceil := first [pose proof alloc_ceiling_range as CEILB | idtac].
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma aparse1_seg : forall (P : acc -> Prop) (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m1 : mem) (H lo : Z),
  stk bsegs m1 lo (bv_unsigned sp) -> mem_inv bsegs m1 -> alloc_ceiling <= lo -> lo + 16 <= bv_unsigned sp -> bv_unsigned sp <= 2^47 ->
  0 < H < alloc_ceiling ->
  pol P lo (bv_unsigned sp) ->
  evtA bsegs P (fun ms' => exists (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 H) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 AY_DO_PARSE) fc None m' (seg_rom bsegs)
      /\ munch [(bv_unsigned sp + -16, bv_unsigned sp)] m1 m' /\ wmono bsegs m1 m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 H) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 AY_PARSE) fc None m1 (seg_rom bsegs)).
Proof. aceil.
  intros until lo. intros ST MI CEIL' LOQ SPH HR PSTK. unfold AY_PARSE, AY_DO_PARSE, pol in *.
  pose proof (munch_refl [(bv_unsigned sp + -16, bv_unsigned sp)] m1) as MU. pose proof (wmono_refl bsegs m1) as WM.
  carve_frame 16%nat ST.
  stepA. stepA.                                       (* [comment removed for export] *)
  zstepA. if_cases K0; zify_cond K0. { kill K0. }     (* [comment removed for export] *)
  stepA. stepA.                                       (* [comment removed for export] *)
  lazymatch goal with H : stk bsegs ?mx lo _ |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename H into ST2 end.
  release_frame FR ST2 (bv_unsigned sp).
  stepA.                                              (* [comment removed for export] *)
  replace (bv_unsigned sp + -16 + 16) with (bv_unsigned sp) in * by lia. rewrite ?Z_to_bv_bv_unsigned.
  apply evtA_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption| assumption].
Qed.

(* [comment removed for export] *)
Section W.
Variable Y : ay_params.
Hypothesis KIPY : AHK_y_kip_stmt Y.
Hypothesis FRAMEY : AHK_y_frame_stmt Y.
Hypothesis BLKY : AHK_y_blocks_stmt Y.
Hypothesis LAYY : AHK_y_layout_stmt Y.
Hypothesis RRT : ayR_trans_stmt Y.
Hypothesis DOP : aydo_parse_stmt Y.
Hypothesis UFRAME : forall m m' SP ra s0, (forall a, SP <= a < 2^47 -> m' (wa a) = m (wa a)) -> y_uanchor Y m SP ra s0 -> y_uanchor Y m' SP ra s0.

Theorem ayparse_proof : ayparse_stmt Y.
Proof. aceil.
  unfold ayparse_stmt. intros LF REST h mh cx T txt OT OTn lo RR K. intros until s.
  intros BAF K0 AY HR CXR TXT T47 L26 TB TSH HINV SHH SHL SHLB SHDB SHST SHCX CXF LC1 LC0 FP EA0 EA1 EA2 CRED RR0 NBIG UA CONT.   (* [comment removed for export] *)
  subst a0.
  destruct FP as (ST & CEIL & LO & SPH & SP16 & MI & TP & FRM).
  pose proof AY as AY0. apply AYST_split in AY. destruct AY as [AHK0 YS].
  destruct (BLKY _ _ _ _ _ AHK0) as (RNG & SEP & ND).
  destruct (LAYY _ _ _ _ _ AHK0) as (LAYF & LAYFB & LAYFF).
  destruct CXF as (f & FIN & FCX & FCL).
  pose proof (LAYF f FIN) as (Ff1 & Ff2 & Ff3 & Ff4 & Ff5). rewrite FCL in Ff2. replace (ff_bytes 1) with 128 in Ff2 by reflexivity.
  assert (BEND : forall b, In b (abl (yblocks mh h)) -> ab_addr b + ab_size b <= lo).
  { intros b Hb. pose proof (RNG b ltac:(apply in_or_app; left; exact Hb)) as X. unfold ablock_range in X. lia. }
  pose proof (RNG _ (or_introl eq_refl)) as HRG. unfold ablock_range, ACONSTS in HRG. cbn [c_img_hi ab_addr ab_size MallocBlocks.blk_addr MallocBlocks.blk_size fst snd] in HRG.
  unfold AY_PARSE_STACK, AY_DO_PARSE_STACK, AY_DECODE_STACK, AY_BUF_APPEND_STACK, AY_WRAP_STACK, AMALLOC_STACK, SIZEOF_HANDLE, wz in *.
  aceil.
  (* [comment removed for export] *)
  arz_seg KIPY AHK0.
  pose proof (aypol_stack Y _ LF _ _ LINK lo (bv_unsigned sp) ltac:(aceil; lia) ltac:(lia)) as PSTK.
  eapply evtA_cut.
  { eapply aparse1_seg with (H := mh_addr mh); [ exact ST | exact MI | lia | lia | lia | lia | exact PSTK ]. }
  cbv beta. intros ms1 (m1 & -> & MU & WM & MI1 & ST1).
  apply evtA_done. intros mo1 Hag1 HLI1 Hh1.
  destruct (BACK mo1 Hag1 HLI1) as [AHKb R1].
  assert (FW : Forall (fun iv : Z * Z => lo <= fst iv) [(bv_unsigned sp + -16, bv_unsigned sp)]) by (constructor; [cbn [fst]; lia| constructor]).
  assert (AHK1 : y_AHK Y s (abl (yblocks mh h) ++ REST) LF m1 mo1).
  { eapply FRAMEY; [exact AHKb| exact MU| exact WM|]. constructor; [left; cbn [fst snd]; aceil; lia| constructor]. }
  clear AHKb.
  pose proof (aystatics_munch _ _ _ YS MU WM ltac:(constructor; [cbn [fst snd]; lia| constructor])) as YS1.
  assert (PRES1 : ay_pres REST LF (bv_unsigned sp) [(mh_ctx mh, mh_ctx mh + 8)] m m1).
  { eapply ay_pres_of_munch; [exact MU| exact WM|]. intros a Ha Hc _.
    eapply (ay_client_outside_stack Y BLKY LAYY _ _ _ _ _ REST (bv_unsigned sp)); [exact AHK0| intros b0 Hb0; apply in_or_app; right; exact Hb0| aceil; lia| lia| exact Hc]. }
  assert (AGREE1 : forall a, bv_unsigned sp <= a < 2^47 -> m1 (wa a) = m (wa a)) by (intros a Ha; apply MU; rewrite wa_unsigned by lia; cbn; lia).
  clear LINK BACK PSTK.
  (* [comment removed for export] *)
  eapply (DOP LF REST h mh cx T txt OT OTn lo RR K);
    [ exact BAF   (* [comment removed for export] *)
    | exact K0
    | apply AYST_split; split; [exact AHK1| exact YS1]
    | eapply hand_rep_below; [exact HR| exact MU| exact WM| exact FW| exact BEND]
    | eapply ctx_rep_below; [exact CXR| exact MU| exact WM| exact FW| lia]
    | eapply text_at_below; [exact TXT| exact MU| exact WM| exact FW|];
      destruct TB as [(bt & Hbt & Tlo & Thi)|T0]; [right; pose proof (RNG bt ltac:(apply in_or_app; right; exact Hbt)) as X; unfold ablock_range in X; aceil; lia| left; exact T0]
    | exact T47 | exact L26 | exact TB
    | destruct TSH as [T0|(OSH & O1 & O2 & O3 & O4 & O5)]; [left; exact T0| right];
      split; [eapply oshadow_below; [exact OSH| exact MU| exact WM| exact FW| revert O3; clear; unfold oshw_hi, A_SB, amem; cbn; lia| lia| lia]|];
      split; [exact O1|]; split; [exact O2|]; split; [exact O3|]; split; [aceil; exact O4| exact O5]
    | exact HINV
    | eapply oshadow_below; [exact SHH| exact MU| exact WM| exact FW| lia| unfold SIZEOF_HANDLE; lia| lia]
    | pose proof (BEND _ (yb_in_lexer mh h)) as X; pose proof (RNG _ ltac:(apply in_or_app; left; apply yb_in_lexer)) as X2;
      unfold ablock_range in X2; cbn [ab_addr ab_size] in X, X2; unfold SIZEOF_LEXER in *;
      eapply oshadow_below; [exact SHL| exact MU| exact WM| exact FW| lia| lia| lia]
    | pose proof (BEND _ (yb_in_lexbuf mh h)) as X; pose proof (RNG _ ltac:(apply in_or_app; left; apply yb_in_lexbuf)) as X2;
      unfold ablock_range in X2; cbn [ab_addr ab_size] in X, X2; unfold SIZEOF_BUF in *;
      eapply oshadow_below; [exact SHLB| exact MU| exact WM| exact FW| lia| lia| lia]
    | pose proof (BEND _ (yb_in_decbuf mh h)) as X; pose proof (RNG _ ltac:(apply in_or_app; left; apply yb_in_decbuf)) as X2;
      unfold ablock_range in X2; cbn [ab_addr ab_size] in X, X2; unfold SIZEOF_BUF in *;
      eapply oshadow_below; [exact SHDB| exact MU| exact WM| exact FW| lia| lia| lia]
    | intros HSB; specialize (SHST HSB);
      pose proof (BEND _ (yb_in_stack mh h HSB)) as X; pose proof (RNG _ ltac:(apply in_or_app; left; apply yb_in_stack; exact HSB)) as X2;
      unfold ablock_range in X2; cbn [ab_addr ab_size] in X, X2;
      eapply oshadow_below; [exact SHST| exact MU| exact WM| exact FW| lia| lia| lia]
    | eapply oshadow_below; [exact SHCX| exact MU| exact WM| exact FW| revert Ff1 FCX; clear; unfold oshw_hi, A_SB, amem; cbn; lia| lia| lia]
    | exists f; split; [exact FIN|]; split; [exact FCX| exact FCL]
    | exact LC1 | exact LC0
    | unfold ayframe_pre, AY_DO_PARSE_STACK, AY_DECODE_STACK, AY_BUF_APPEND_STACK, AY_WRAP_STACK, AMALLOC_STACK; aceil;
      split; [exact ST1|]; split; [lia|]; split; [lia|]; split; [lia|]; split; [exact SP16|]; split; [exact MI1|]; split; [exact TP| exact FRM]
    | reflexivity | exact EA1 | exact EA2
    | exact CRED | exact RR0 | exact NBIG
    | eapply UFRAME; [exact AGREE1| exact UA]
    | ].
  cbv beta. intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F2 fc2 m2 mo2 sa2 st h' cx' mh' LK POST.
  destruct POST as (SO2 & R2 & CRED2 & (MI2 & ST2 & FRM2 & _ & PRES2) & REST2).
  eapply CONT. unfold ayparse_rpost.
  split; [exact SO2|]. split; [eapply RRT; [exact R1| exact R2]|]. split; [exact CRED2|].
  split; [| exact REST2].
  split; [exact MI2|]. split; [exact ST2|]. split; [exact FRM2|]. split; [exact I|].
  eapply ay_pres_trans; [exact PRES1| exact PRES2].
Qed.
End W.
End RC__1.
