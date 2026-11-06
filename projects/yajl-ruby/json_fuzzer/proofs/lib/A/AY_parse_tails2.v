(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import InitMem SysStep Image SFW1_lemmas.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.MS Require Import MallocRep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim YajlBase YajlLeaf YajlBuf YajlLex YajlParser YajlFactsBuf YajlFactsLex YajlFactsParse YajlFactsLoop.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RY_lib.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA AImages LazyModel NodesA Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import A_iface AYajlRep AYajl_iface AY_rz AY_hand AY_acct_needs AY_parse_kit AY_parse_pol AY_parse_head AY_parse_tails.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac aceil := first [pose proof alloc_ceiling_range as CEILB | idtac].
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition J_POP : Z := 0x88398.

Section W.
Variable Y : ay_params.
Hypothesis KIPY : AHK_y_kip_stmt Y.
Hypothesis FRAMEY : AHK_y_frame_stmt Y.
Hypothesis BLKY : AHK_y_blocks_stmt Y.
Hypothesis BSHY : AHK_y_block_shadow_stmt Y.
Hypothesis LAYY : AHK_y_layout_stmt Y.
Hypothesis RRT : ayR_trans_stmt Y.
Hypothesis UFRAME : forall m m' SP ra s0, (forall a, SP <= a < 2^47 -> m' (wa a) = m (wa a)) -> y_uanchor Y m SP ra s0 -> y_uanchor Y m' SP ra s0.

(* [comment removed for export] *)
Lemma J_pop : forall (E : apE Y) (F : bvmap 5 word) (fc : bv 32) m mo s LK h0 cx0 h mh cx obw olw cr st rest
    (rav t0 t1 a0 a1 a2 a3 a4 a5 a6 a7 s4v s5v t3 t4 t5 t6 : word),
  penvA E -> pok E h0 cx0 -> pmem E m mo s LK h mh cx obw olw cr -> pcr E (h_set_stack h rest) cr -> frm0 fc ->
  h_stack h = st :: rest -> h_stack_size h mod 8 = 0 -> plk_ok LK (h_set_stack h rest) ->
  yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) h0 cx0) (SR_again (h_set_stack h rest) cx) ->
  pagain Y E h0 cx0 LK ->
  realizes_cfg acfg asegs (mkCfg (pstate E J_POP F fc m rav t0 t1 (wz (pH E + 48)) a0 a1 a2 a3 a4 a5 a6 a7 (wz (pH E + 64)) s4v s5v t3 t4 t5 t6) mo) (p_K E).
Proof. aceil.
  intros until t6. intros PA OK PM HCR FRM HST SZM' PLK YL AG.
  popen OK PM. yhide TB. yhide OTB. yhide FFR0.
  destruct (yparse_step_again_facts (p_txt E) (zlength (p_txt E)) h0 cx0 _ cx eq_refl ltac:(openPA PA; clear -CEILB pa_len0; lia) LP YL) as (LP1 & U1 & _).
  assert (EU : h_used (h_set_stack h rest) = h_used h - 1) by (unfold h_used; cbn [h_stack h_set_stack]; rewrite HST; unfold zlength; cbn [length]; lia).
  rewrite EU in U1.
  assert (USED : h_used h = zlength rest + 1) by (unfold h_used; rewrite HST; unfold zlength; cbn [length]; lia).
  assert (Z0 : 0 <= zlength rest) by (unfold zlength; clear; lia).
  pose proof (proj2 BC3) as US. assert (SZ : 0 < h_stack_size h) by (clear -CEILB USED Z0 US; lia).
  assert (SZM1 : h_stack_size (h_set_stack h rest) mod 8 = 0) by exact SZM'.
  pose proof (pok_again Y E h0 cx0 (h_set_stack h rest) cx OK LP1 ltac:(rewrite EU; exact U1) SB1 SZM1) as OK1. yhide LP.
  pose proof (mk_pblk BLKY LAYY BSHY E s LK h mh h0 cx0 m mo PA OK AHK SAME SB1 SZ) as PB.
  pose proof (pb_HSB _ _ _ PB) as SEPHS. pose proof (pb_SB _ _ _ PB) as RSB. pose proof (pb_SBA PB) as RSBA. pose proof (pb_SBCX _ _ _ PB) as SEPSC.
  openPA PA. clear pa_ffCX0 pa_ffH0 pa_Tsep0 pa_OT0 pa_j0. pose proof SAME as (EH & EL & ELB & EDB & ECX).
  pose proof BSR as BSR'. unfold RYajlRep.bs_rep in BSR'. destruct (h_stack_blk h) as [sbk|] eqn:HSB in BSR'; [| exfalso; exact (SB1 HSB)].
  destruct BSR' as (SBNZ & junk & SC).
  clear TXT LXR DBR FF OCX GAP PRES UA CRED HS HR. yhide SV. yhide SC.
  unfold hand_cells, hand_head_cells, alloc_cells in HC. cbn [yc_callbacks yc_malloc_w yc_realloc_w yc_free_w ayc app] in HC. unfold wz in HC. rewrite EH in HC.
  pose proof (munch_refl [(mh_addr (p_mh E) + 60, mh_addr (p_mh E) + 64)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  unfold pstate, J_POP, wz.
  arz_seg KIPY AHK.
  pose proof (mk_ppol BLKY LAYY BSHY E s LK h mh h0 cx0 m mo _ _ PA OK AHK SAME SB1 SZ LINK) as PP. openPP PP. pose proof (ppol_mark E mh) as PPM.
  unfold pol in pp_stk0, pp_H0, pp_Hs0. clear pp_img0 pp_imgsh0 pp_L0 pp_Ls0 pp_DB0 pp_DBs0 pp_SB0 pp_SBs0 pp_CX0 pp_CXs0 pp_ff0 pp_ffs0 pp_T0 pp_Ts0.
  zstepA. rewrite ?ysx32_small by (clear -CEILB BC3 BC2; lia).   (* [comment removed for export] *)
  zstepA. rewrite (swrap32_small (h_used h + -1)) by (clear -CEILB USED Z0 US BC2; lia).   (* [comment removed for export] *)
  zstepA.                                                  (* [comment removed for export] *)
  zstepA. if_cases K; zify_cond K; [| exfalso; revert K U1 USED Z0 US BC2; clear; intros; rewrite ?unsigned_lit in K by lia; lia].   (* [comment removed for export] *)
  apply evtA_done. intros mo1 Hag1 HLI1 Hh1. destruct (BACK mo1 Hag1 HLI1) as [AHK1 R01].
  lazymatch goal with |- realizes_cfg _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ => rename mx into m2 end.
  pose proof (pmem_remodel E m mo mo1 s LK h mh cx obw olw cr PM AHK1 (RRT _ _ _ _ _ _ R1 R01)) as PM1.
  unfold pagain, phead, pstate, AY_PHEAD, wz in AG.
  replace (h_used h + -1) with (h_used (h_set_stack h rest)) by (rewrite EU; clear; lia).
  eapply AG; [exact YL|].
  split; [| split; [exact OK1| split; [exact FRM| exact PLK]]].
  exists obw, olw, cr. split; [| exact HCR].
  yshow TB. yshow OTB. yshow FFR0. yshow SV. yshow SC. yshow LP.
  eapply (pmem_updA BLKY LAYY BSHY FRAMEY UFRAME E m m2 mo1 s LK h mh cx obw olw cr);
    [exact PA| exact OK| exact PM1| exact SZ| exact MU| exact WM| assumption| | reflexivity| reflexivity| reflexivity| reflexivity| exact I| |
    | eapply ctx_rep_agree; [eapply munch_agree; [exact MU| exact WM]| exact CXR| intros a Ha; cbn; clear -CEILB Ha pa_CXH0; lia]
    | exists k0, k224; assumption
    | eapply (rw_cells_transport asegs); [exact SV| exact MU| exact WM| unfold psaved; cbn; clear -CEILB pa_SQ0 pa_lo0 pa_ceil0 pa_H0; lia]
    | assumption ].
  - constructor; [| constructor]. unfold ownA. cbn [fst snd]. left. rewrite EH. clear. lia.
  - (* [comment removed for export] *)
    split; [| cbn [h_set_stack h_bytesConsumed h_stack_size h_stack_blk h_parseError]; rewrite HSB, EU;
             split; [exact BC1| split; [exact BC2| split; [clear -CEILB BC3 U1; lia| intros; split; intros; congruence]]]].
    exists pew, pad. split; [| exact PW].
    unfold hand_cells, hand_head_cells, alloc_cells. cbn [yc_callbacks yc_malloc_w yc_realloc_w yc_free_w ayc app h_set_stack h_bytesConsumed h_stack_size h_parseError].
    rewrite EU. unfold wz. rewrite EH.
    lazymatch goal with H0 : rw_cells asegs m2 (mh_addr (p_mh E)) _ |- _ => exact H0 end.
  - (* [comment removed for export] *)
    eapply (rw_cells_transport asegs) in SC; [| exact MU| exact WM| cbn; clear -CEILB SEPHS US U1 EH USED Z0; lia].
    unfold RYajlRep.bs_rep. cbn [h_stack_blk h_set_stack h_stack h_stack_size]. rewrite HSB, EU. split; [exact SBNZ|].
    exists (zbytes [state_code st] ++ junk).
    destruct (u8arr_of_CB2 _ _ _ _ _ _ _ SC) as (ARR & L1 & L2).
    apply CB2_of_u8arr; [| rewrite zbytes_length, stack_bytes_length; clear -CEILB USED; unfold zlength in USED; lia
                        | rewrite length_app; cbn [zbytes map length]; clear -CEILB L2 USED Z0 US; lia].
    rewrite HST, stack_bytes_cons, zbytes_app, <- app_assoc in ARR. exact ARR.
Qed.
End W.
End RC__1.
