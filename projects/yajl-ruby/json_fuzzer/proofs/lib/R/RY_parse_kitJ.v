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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Image ZBridge SysStep SFModel SFW1_lemmas InitMem Arr FP NodesCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Images.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import PortShim.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RMallocRep RMallocTree RMalloc_iface RYajlRep RYajl_iface RY_lib RY_rz RY_kit2 RY_parse_kit.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Agent Require Import MallocBlocks.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import RawAlloc Prelim YajlBase YajlBuf YajlLex YajlDecode YajlParser YajlLeaf YajlFactsBuf YajlFactsLex YajlFactsParse YajlFactsLoop.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section S.
Variable HK : RawAlloc.PState -> list block -> (word -> option byte) -> Model -> Prop.
Hypothesis HKS : HK_silent_stmt HK.
Hypothesis HKP : HK_perm_stmt HK.
Hypothesis HKF : HK_frame_stmt HK.
Hypothesis HKB : HK_blocks_stmt HK.
Hypothesis YLX : ylex_lex_stmt HK.
Notation buf_rep := (buf_rep rsegs).
Notation buf_struct := (buf_struct rsegs).
Notation buf_data := (buf_data rsegs).
Notation lexer_rep := (lexer_rep rsegs).
Notation hand_rep := (hand_rep rsegs ryc).
Notation hand_struct := (hand_struct rsegs ryc).
Notation bs_rep := (bs_rep rsegs).
Notation ctx_rep := (ctx_rep rsegs).
Notation text_at := (text_at rsegs).
Notation RYST := (RYST HK).
Notation yparse_head_inv := (yparse_head_inv HK).
Notation yparse_exit_cont := (yparse_exit_cont HK).
Notation pmem := (pmem HK).
Notation again_cont := (again_cont HK).
Notation exit_cont := (exit_cont HK).
Notation yhead_invX := (yhead_invX HK).

Ltac kill K := exfalso; revert K; unfold wz; rewrite ?unsigned_lit by lia;
  try (change 18446744073709551615 with (Z.ones 64); rewrite ?Z.land_ones by lia; rewrite ?Z.mod_small by lia); lia.

(* [comment removed for export] *)
Lemma at_head : forall E m mo s LK h mh cx obw olw
    (rav t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s5v s6v s8v : word),
  pok E -> pmem E m mo s LK h mh cx obw olw ->
  yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) (p_h E) (p_cx E)) (SR_again h cx) ->
  again_cont E ->
  realizes_cfg acfg rsegs (mkCfg (yparse_head_state rav (p_sp E) (p_gp E) (p_tp E) (p_s0 E) (p_s1 E) (p_s2 E) (p_s3 E) (p_s4 E) (p_s5 E)
                           (p_s6 E) (p_s7 E) (p_s8 E) (p_s9 E) (p_s10 E) (p_s11 E) (p_F E) (p_fc E) m
                           (pH E) (p_T E) (pLEN E) (h_used h) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s5v s6v s8v) mo) (p_K E).
Proof.
  intros until s8v. intros OK PM YL AG.
  destruct OK as (K0 & LP & U0 & SB0 & L26 & TB & SPC & CXB & CEIL & LO & TP & B64 & PYR).
  destruct PM as (RY & HR & SAME & CXR & TXT & (padw & FR) & AX & STK & ERR & MI & PRES & SB1 & LK0).
  destruct (yparse_step_again_facts (p_txt E) (pLEN E) (p_h E) (p_cx E) h cx eq_refl ltac:(unfold pLEN in *; lia) LP YL) as (LP1 & U1 & _).
  eapply AG; [exact YL| exact SAME| exact PRES| exact LK0|].
  pose proof SAME as (_ & _ & _ & _ & _ & _ & _ & _ & ECX). unfold pCX in *. rewrite <- ECX in *.
  split; [| exact SB1].
  split; [exact RY|]. split; [exact HR|]. split; [exact CXR|]. split; [exact TXT|]. split; [exact L26|].
  split. { destruct TB as [(bt & HIN & HB)|Z0]; [left; exists bt; split; [apply in_or_app; right; exact HIN| exact HB]| right; exact Z0]. }
  split; [exact LP1|]. split; [exact U1|]. split; [subst LK; exact PYR|]. split; [exists padw, obw, olw; exact FR|].
  split; [exact AX|]. split; [exact SPC|]. split; [exact CXB|]. split; [exact STK|]. split; [unfold alloc_ceiling; lia|]. split; [unfold RY_DO_PARSE_STACK, RY_DECODE_STACK, RY_BUF_APPEND_STACK, RY_WRAP_STACK; unfold pSP in LO; lia|].
  split; [exact ERR|]. split; [exact MI| exact TP].
Qed.

(* [comment removed for export] *)
Lemma J_back : forall E m mo s LK h mh cx obw olw
    (rav t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s5v s6v s8v : word),
  pok E -> pmem E m mo s LK h mh cx obw olw ->
  yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) (p_h E) (p_cx E)) (SR_again h cx) ->
  again_cont E ->
  realizes_cfg acfg rsegs (mkCfg (pstate E 0x15d7c m rav t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s5v s6v s8v (wz 13)) mo) (p_K E).
Proof.
  intros until s8v. intros OK PM YL AG.
  pose proof OK as OK'. destruct OK' as (K0 & LP & U0 & SB0 & L26 & TB & SPC & CXB & CEIL & LO & TP & B64 & PYR).
  pose proof PM as PM'. destruct PM' as (RY & HR & SAME & CXR & TXT & (padw & FR) & AX & STK & ERR & MI & PRES & SB1 & LK0).
  destruct (yparse_step_again_facts (p_txt E) (pLEN E) (p_h E) (p_cx E) h cx eq_refl ltac:(unfold pLEN in *; lia) LP YL) as (LP1 & U1 & _).
  apply RYST_split in RY. destruct RY as [HK0 YS].
  destruct HR as (HS & LXR & DBR & BSR). destruct HS as ((pew & pad & HC & PW) & BC1 & BC2 & BC3 & BC4).
  pose proof (rw_cells_bound _ _ _ _ HC) as HCB. rewrite hand_cells_size in HCB.
  unfold hand_cells, hand_head_cells, alloc_cells in HC. cbn [yc_callbacks yc_malloc_w yc_realloc_w yc_free_w ryc app] in HC.
  destruct SAME as (_ & EH & _). unfold pstate, pH. rewrite <- EH. unfold wz in HC |- *.
  rz_seg HKS HK0.
  zstep. rewrite ysx32_small by lia.
  zstep. if_cases K1; zify_cond K1. 2:{ kill K1. }
  apply evt_done.
  pose proof (at_head E m mo s LK h mh cx obw olw rav t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s5v s6v s8v OK PM YL AG) as X.
  unfold yparse_head_state, pH, RY_PARSE_HEAD, wz in X. rewrite <- EH in X. exact X.
Qed.

(* [comment removed for export] *)
Lemma J_exit : forall E m mo s LK h mh cx obw olw st
    (rav t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s6v s8v s10v : word),
  pok E -> pmem E m mo s LK h mh cx obw olw ->
  yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) (p_h E) (p_cx E)) (SR_done st h cx) ->
  exit_cont E ->
  realizes_cfg acfg rsegs (mkCfg (pstate E 0x16124 m rav t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (wz (status_code st)) s6v s8v s10v) mo) (p_K E).
Proof.
  intros until s10v. intros OK PM YL EX.
  pose proof OK as OK'. destruct OK' as (K0 & LP & U0 & SB0 & L26 & TB & SPC & CXB & CEIL & LO & TP & B64 & PYR).
  pose proof PM as PM'. destruct PM' as (RY & HR & SAME & CXR & TXT & (padw & FR) & AX & STK & ERR & MI & PRES & SB1 & LK0).
  apply RYST_split in RY. destruct RY as [HK0 YS].
  unfold yparse_frame in FR. unfold pstate, pSP, wz in *.
  pose proof (rw_cells_bound _ _ _ _ FR) as FRB. cbn [cells_size csize Nat.add] in FRB.
  rz_seg HKS HK0.
  zstep. do 13 zstep. zstep. zstep. zstep.
  apply evt_done.
  release_frame FR STK (bv_unsigned (p_sp E) + 144).
  pose proof SAME as (_ & _ & _ & _ & _ & _ & _ & _ & ECX). unfold pCX in *.
  assert (E144 : bv_unsigned (Z_to_bv 64 (bv_unsigned (p_sp E) + 144)) = bv_unsigned (p_sp E) + 144) by (apply unsigned_lit; lia).
  unfold exit_cont, yparse_exit_cont, wz in EX.
  eapply EX; [| exact YL| reflexivity| exact HR| exact SAME| exact CXR| exact TXT| exact LK0| apply RYST_split; split; [exact HK0| exact YS]|].
  - split; [exact MI|]. split; [rewrite E144; exact STK|]. split; [exact ERR|]. split; [exact AX|]. rewrite E144. exact PRES.
  - intros k. destruct (Z.eq_dec (bv_unsigned k) 8) as [EK|NK].
    + rewrite (freg_get_same (p_F E) 8 k) by (rewrite EK; reflexivity). replace k with (8%bv : bv 5) by (apply bv_eq; rewrite EK; reflexivity). reflexivity.
    + apply freg_get_other. unfold bv_eqb. apply Z.eqb_neq. change (bv_unsigned (8%bv : bv 5)) with 8. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma ry_pres_up : forall LB LB' SP SP' X X' m m',
  ry_pres LB SP X m m' -> SP <= SP' -> (forall b, In b LB' -> In b LB) ->
  (forall a, yin_ivs X a -> ~ rclient_addr LB' SP' a) -> ry_pres LB' SP' X' m m'.
Proof.
  intros LB LB' SP SP' X X' m m' H HS HL HX a Ha Hc _. apply H; [exact Ha| | intros Hx; exact (HX a Hx Hc)].
  destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [left; lia| right; left; exact Hc| right; right].
  exists b. split; [apply HL; exact Hb| exact Hr].
Qed.

Lemma bs_rep_agree : forall P m m' SB h,
  agree_on rsegs P m m' -> bs_rep m SB h -> (forall a, SB <= a < SB + h_stack_size h -> P a) ->
  0 <= h_used h <= h_stack_size h -> bs_rep m' SB h.
Proof.
  intros P m m' SB h HP BR HF HU. unfold RYajlRep.bs_rep in *. destruct (h_stack_blk h); [| exact BR].
  destruct BR as (NZ & junk & SC). split; [exact NZ|]. exists junk.
  eapply rw_cells_agree; [exact HP| exact SC|]. intros a Ha. apply HF. revert Ha. cbn [cells_size csize Nat.add]. lia.
Qed.

Lemma hand_struct_agree : forall P m m' h mh,
  agree_on rsegs P m m' -> hand_struct m h mh -> (forall a, mh_addr mh <= a < mh_addr mh + 104 -> P a) -> hand_struct m' h mh.
Proof.
  intros P m m' h mh HP ((pew & pad & HC & PW) & R) HF. split; [| exact R]. exists pew, pad. split; [| exact PW].
  eapply rw_cells_agree; [exact HP| exact HC|]. rewrite hand_cells_size. exact HF.
Qed.

(* [comment removed for export] *)
Lemma frame_split : forall m (sp ra0 s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e fs0 padw obw olw : word),
  yparse_frame m sp ra0 s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e fs0 padw obw olw <->
  (rw_cells rsegs m (bv_unsigned sp) [C8 (wz (2^63 + 1)); C8 (wz 0x108e6); C4 padw]
   /\ rw_cells rsegs m (bv_unsigned sp + 32) [C8 fs0; C8 s11e; C8 s10e; C8 s9e; C8 s8e; C8 s7e; C8 s6e; C8 s5e; C8 s4e; C8 s3e; C8 s2e; C8 s1e; C8 s0e; C8 ra0])
  /\ rw_cells rsegs m (bv_unsigned sp + 20) [C4 olw] /\ rw_cells rsegs m (bv_unsigned sp + 24) [C8 obw].
Proof.
  intros. unfold yparse_frame.
  change ([C8 (wz (2^63 + 1)); C8 (wz 0x108e6); C4 padw; C4 olw; C8 obw; C8 fs0; C8 s11e; C8 s10e; C8 s9e; C8 s8e; C8 s7e; C8 s6e; C8 s5e; C8 s4e; C8 s3e; C8 s2e; C8 s1e; C8 s0e; C8 ra0])
    with ([C8 (wz (2^63 + 1)); C8 (wz 0x108e6); C4 padw] ++ [C4 olw] ++ [C8 obw] ++ [C8 fs0; C8 s11e; C8 s10e; C8 s9e; C8 s8e; C8 s7e; C8 s6e; C8 s5e; C8 s4e; C8 s3e; C8 s2e; C8 s1e; C8 s0e; C8 ra0]).
  rewrite !ycells_app. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ].
  replace (bv_unsigned sp + 20 + 4) with (bv_unsigned sp + 24) by lia.
  replace (bv_unsigned sp + 24 + 8) with (bv_unsigned sp + 32) by lia. tauto.
Qed.

Definition mh_set_lexbuf (mh : mhand) (mbl : mbuf) : mhand :=
  mkMH (mh_id mh) (mh_addr mh) (mh_lid mh) (mh_lexer mh) mbl (mh_decbuf mh) (mh_sid mh) (mh_stack mh) (mh_ctx mh).

Definition lex_state (s : ystate) : bool :=
  match s with ST_parse_complete | ST_parse_error | ST_lexical_error => false | _ => true end.


(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma lex_call : forall E m mo s LK h mh cx obw olw (rav : word)
    (t0 t1 t2 a6 a7 t3 t4 t5 t6 s6v s8v : word),
  pok E -> pmem E m mo s LK h mh cx obw olw -> hinv (pLEN E) h cx ->
  (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m' mo' s' lx' tok off' ob n mbl' LK',
     yleaf (ylex_lex (h_lexer h) (p_txt E) (pLEN E) (h_bytesConsumed h)) (lx', tok, off', ob, n) ->
     lex_post (p_txt E) (pLEN E) (h_bytesConsumed h) (lx', tok, off', ob, n) ->
     pmem E m' mo' s' (LK' ++ LK) (h_set_lex_off h lx' off') (mh_set_lexbuf mh mbl') cx (wz (outref_addr (p_T E) (mb_data mbl') ob)) (wz n) ->
     realizes_cfg acfg rsegs (mkCfg (MS (mkR rav (p_sp E) (p_gp E) (p_tp E) t0' t1' t2' (wz (pH E)) (wz (pH E + 48)) (wz (tok_code tok)) a1' a2' a3' a4' a5' a6' a7'
                                     (wz (pLEN E)) (wz (p_T E)) (wz (pH E + 32)) (wz 0) s6v (wz 11) s8v (wz RY_JT_TOKVAL) (wz 13) (wz RY_JT_STATE) t3' t4' t5' t6')
                                (p_F E) (ret_pc rav) (p_fc E) None m' (seg_rom rsegs)) mo') (p_K E)) ->
  realizes_cfg acfg rsegs (mkCfg (MS (mkR rav (p_sp E) (p_gp E) (p_tp E) t0 t1 t2 (wz (pH E)) (wz (pH E + 48)) (wz (mh_lexer mh)) (wz (p_T E)) (wz (pLEN E)) (wz (pH E + 32))
                                  (wz (pSP E + 24)) (wz (pSP E + 20)) a6 a7
                                  (wz (pLEN E)) (wz (p_T E)) (wz (pH E + 32)) (wz 0) s6v (wz 11) s8v (wz RY_JT_TOKVAL) (wz 13) (wz RY_JT_STATE) t3 t4 t5 t6)
                             (p_F E) (wz RY_LEX_LEX) (p_fc E) None m (seg_rom rsegs)) mo) (p_K E).
Proof.
  intros until s8v. intros OK PM HINV CONT.
  pose proof OK as OK'. destruct OK' as (K0 & LP & U0 & SB0 & L26 & TB & SPC & CXB & CEIL & LO & TP & B64 & PYR).
  pose proof PM as PM'. destruct PM' as (RY & HR & SAME & CXR & TXT & (padw & FR) & AX & STK & ERR & MI & PRES & SB1 & LK0).
  pose proof HINV as (LXI & OFFB & DBI & DBOK & STI & DEPTH & SZB).
  apply RYST_split in RY. destruct RY as [HK0 YS].
  pose proof HR as (HS & LXR & DBR & BSR). pose proof HS as (_ & BC1 & BC2 & BC3 & BC4).
  pose proof SAME as (EID & EHA & ELID & ELX & ELBI & ELBA & EDBI & EDBA & ECX). unfold pCX, pH, pSP in *.
  rewrite <- EHA, <- ECX in *.
  pose proof (proj1 STK) as LO0.
  destruct (HK_blocks HK HKB _ _ _ _ HK0) as [RNG SEP].
  apply frame_split in FR. destruct FR as ((FRA & FRB) & OL & OB).
  destruct ERR as [errv ERR].
  (* [comment removed for export] *)
  set (REST' := (buf_blocks (mh_decbuf mh) (h_decbuf h) ++ bs_blocks (mh_sid mh) (mh_stack mh) h) ++ LK ++ p_REST E).
  assert (ELB : yblocks mh h ++ LK ++ p_REST E = (mh_id mh, mh_addr mh, SIZEOF_HANDLE) :: lexer_blocks (mh_lid mh) (mh_lexer mh) (mh_lexbuf mh) (h_lexer h) ++ REST').
  { unfold yblocks, REST'. cbn [app]. rewrite <- !app_assoc. reflexivity. }
  rewrite ELB in HK0, RNG, SEP.
  eapply (YLX REST' h mh (p_T E) (p_txt E) (h_bytesConsumed h) (bv_unsigned (p_sp E) + 24) (bv_unsigned (p_sp E) + 20) obw olw (p_lo E) (p_B E) errv (p_K E));
    [exact K0 | apply RYST_split; split; [exact HK0| exact YS] | exact HS | exact LXR | exact LXI | reflexivity | exact OFFB | exact L26 | exact TXT
    | | exact OB | exact OL | clear; lia | clear; lia | clear -SPC CXB; lia | unfold REST'; clear -PYR LK0; yroom_solve | | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | ].
  { destruct TB as [(bt & HIN & HB)|Z0]; [left; exists bt; split; [unfold REST'; apply in_or_app; right; apply in_or_app; right; exact HIN| exact HB]| right; exact Z0]. }
  { split; [exact AX|]. split; [clear -SPC CXB; lia|]. split; [exact STK|]. split; [clear -CEIL; unfold alloc_ceiling; lia|].
    split; [clear -LO; unfold RY_LEX_LEX_STACK, RY_BUF_APPEND_STACK, RY_WRAP_STACK; lia|]. split; [exact ERR|]. split; [exact MI| exact TP]. }
  cbv beta. intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 mo2 s2 lx' tok off' ob n mbl' LK' POST.
  destruct POST as ((MI2 & STK2 & ERR2 & AX2 & PR2) & YL & -> & HS2 & LXR2 & MBS & OB2 & OL2 & TXT2 & LKE & RY2).
  pose proof (ypost_yleaf _ _ _ (ylex_lex_post (h_lexer h) (p_txt E) (pLEN E) (h_bytesConsumed h) eq_refl ltac:(clear -L26; unfold pLEN in *; lia) LXI OFFB) YL) as LPOST.
  apply (CONT t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 mo2 s2 lx' tok off' ob n mbl' LK' YL LPOST).
  (* [comment removed for export] *)
  unfold RY_parse_kit.pmem, pCX, pH, pSP. rewrite <- ECX.
  apply RYST_split in RY2. destruct RY2 as [HK2 YS2].
  pose proof (ry_pres_agree _ _ _ _ _ PR2) as AG.
  destruct MBS as [MBI MBA].
  assert (RR : forall b, In b REST' -> 0 < blk_addr b /\ blk_addr b + blk_size b <= p_lo E).
  { intros b Hb. pose proof (all_range_In _ _ RNG ltac:(right; apply in_or_app; right; exact Hb)) as X.
    unfold rblock_range, alloc_ceiling in X. clear -X CEIL. lia. }
  assert (INCL : forall A k b, In b REST' -> blk_addr b <= A -> A + k <= blk_addr b + blk_size b ->
            forall a, A <= a < A + k -> rclient_addr REST' (bv_unsigned (p_sp E)) a /\ ~ yin_ivs [(bv_unsigned (p_sp E) + 20, bv_unsigned (p_sp E) + 20 + 4); (bv_unsigned (p_sp E) + 24, bv_unsigned (p_sp E) + 24 + 8)] a).
  { intros A k b Hb H1 H2 a Ha. pose proof (RR b Hb) as Rb. split.
    - right; right. exists b. split; [exact Hb| clear -H1 H2 Ha; lia].
    - intros [Hx|[Hx|Hx]]; cbn in Hx; clear -Hx H1 H2 Ha Rb LO; lia. }
  assert (HICL : forall a, bv_unsigned (p_sp E) + 32 <= a \/ (bv_unsigned (p_sp E) <= a < bv_unsigned (p_sp E) + 20) ->
            rclient_addr REST' (bv_unsigned (p_sp E)) a /\ ~ yin_ivs [(bv_unsigned (p_sp E) + 20, bv_unsigned (p_sp E) + 20 + 4); (bv_unsigned (p_sp E) + 24, bv_unsigned (p_sp E) + 24 + 8)] a).
  { intros a Ha. split; [left; clear -Ha; lia|]. intros [Hx|[Hx|Hx]]; cbn in Hx; clear -Hx Ha; lia. }
  assert (IDB : In (mb_id (mh_decbuf mh), mb_addr (mh_decbuf mh), SIZEOF_BUF) REST') by (unfold REST'; apply in_or_app; left; apply in_or_app; left; left; reflexivity).
  assert (IDD : yb_data (h_decbuf h) <> None -> In (mb_did (mh_decbuf mh), mb_data (mh_decbuf mh), yb_len (h_decbuf h)) REST').
  { intros HD. unfold REST'. apply in_or_app; left. apply in_or_app; left. unfold buf_blocks. destruct (yb_data (h_decbuf h)); [| congruence]. right; left; reflexivity. }
  assert (ISB : In (mh_sid mh, mh_stack mh, h_stack_size h) REST').
  { unfold REST'. apply in_or_app; left. apply in_or_app; right. unfold bs_blocks. unfold RYajlRep.bs_rep in BSR. destruct (h_stack_blk h); [left; reflexivity| congruence]. }
  split.
  { apply RYST_split. split; [| exact YS2]. eapply HKP; [exact HK2|].
    unfold yblocks, REST'. cbn [mh_set_lexbuf mh_id mh_addr mh_lid mh_lexer mh_lexbuf mh_decbuf mh_sid mh_stack h_set_lex_off h_lexer h_decbuf app].
    apply Permutation.perm_skip. rewrite <- !app_assoc. apply Permutation.Permutation_app_head.
    replace (bs_blocks (mh_sid mh) (mh_stack mh) (h_set_lex_off h lx' off')) with (bs_blocks (mh_sid mh) (mh_stack mh) h) by reflexivity.
    rewrite (app_assoc (buf_blocks _ _) (bs_blocks _ _ _) (LK' ++ LK ++ p_REST E)).
    rewrite (app_assoc (buf_blocks _ _) (bs_blocks _ _ _) (LK ++ p_REST E)).
    apply Permutation.Permutation_app_swap_app. }
  split.
  { split; [exact HS2|]. split; [exact LXR2|]. cbn [mh_set_lexbuf mh_decbuf mh_addr mh_stack h_set_lex_off h_decbuf]. split.
    - eapply buf_rep_agree; [exact AG| exact DBR| |].
      + eapply INCL; [exact IDB| cbn; clear; lia| cbn; unfold SIZEOF_BUF; clear; lia].
      + intros HD. eapply INCL; [exact (IDD HD)| cbn; clear; lia| cbn; clear; lia].
    - eapply bs_rep_agree; [exact AG| | | unfold h_used; cbn [h_stack h_stack_size h_set_lex_off]; unfold h_used in BC3; clear -BC3; lia].
      + unfold RYajlRep.bs_rep in BSR |- *. cbn [h_stack_blk h_set_lex_off]. destruct (h_stack_blk h); [| congruence].
        cbn [h_stack h_stack_size h_set_lex_off]. replace (h_used (h_set_lex_off h lx' off')) with (h_used h) by reflexivity. exact BSR.
      + cbn [h_stack_size h_set_lex_off]. eapply INCL; [exact ISB| cbn; clear; lia| cbn; clear; lia]. }
  split.
  { unfold mh_same. cbn [mh_set_lexbuf mh_id mh_addr mh_lid mh_lexer mh_lexbuf mh_decbuf mh_sid mh_stack mh_ctx]. rewrite MBI, MBA. exact SAME. }
  split. { eapply ctx_rep_agree; [exact AG| exact CXR|]. intros a Ha. apply HICL. clear -Ha SPC. lia. }
  split; [exact TXT2|].
  split.
  { exists padw. apply frame_split. split; [| split; [exact OL2| exact OB2]]. split.
    - eapply rw_cells_agree; [exact AG| exact FRA|]. cbn [cells_size csize Nat.add]. intros a Ha. apply HICL. clear -Ha. lia.
    - eapply rw_cells_agree; [exact AG| exact FRB|]. cbn [cells_size csize Nat.add]. intros a Ha. apply HICL. clear -Ha. lia. }
  split; [exact AX2|]. split; [exact STK2|]. split; [exact ERR2|]. split; [exact MI2|].
  split.
  { eapply ry_pres_trans; [exact PRES|]. eapply ry_pres_up; [exact PR2| clear; lia| intros b Hb; unfold REST'; apply in_or_app; right; apply in_or_app; right; exact Hb|].
    intros a Hx Hc. assert (Ha : bv_unsigned (p_sp E) + 20 <= a < bv_unsigned (p_sp E) + 32) by (destruct Hx as [Hx|[Hx|Hx]]; cbn in Hx; clear -Hx; lia).
    destruct Hc as [Hc|[Hc|(b & Hb & Hr)]].
    - clear -Ha Hc. lia.
    - clear -Ha Hc LO CEIL LO0. lia.
    - pose proof (RR b ltac:(unfold REST'; apply in_or_app; right; apply in_or_app; right; exact Hb)) as Rb. clear -Ha Hr Rb LO. lia. }
  split; [exact SB1| rewrite LKE, LK0; reflexivity].
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma pass_lex : forall E m mo s LK h mh cx obw olw st rest
    (rav t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s5v s6v s8v : word),
  pok E -> pmem E m mo s LK h mh cx obw olw -> h = p_h E -> cx = p_cx E ->
  h_stack h = st :: rest -> lex_state st = true ->
  (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m' mo' s' lx' tok off' ob n mbl' LK',
     yleaf (ylex_lex (h_lexer h) (p_txt E) (pLEN E) (h_bytesConsumed h)) (lx', tok, off', ob, n) ->
     lex_post (p_txt E) (pLEN E) (h_bytesConsumed h) (lx', tok, off', ob, n) ->
     hinv (pLEN E) h cx ->
     pmem E m' mo' s' (LK' ++ LK) (h_set_lex_off h lx' off') (mh_set_lexbuf mh mbl') cx (wz (outref_addr (p_T E) (mb_data mbl') ob)) (wz n) ->
     realizes_cfg acfg rsegs (mkCfg (pstate E (state_target st + 28) m' (wz (state_target st + 28)) t0' t1' t2' (wz (tok_code tok)) a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' (wz 0) s6v s8v (wz 13)) mo') (p_K E)) ->
  realizes_cfg acfg rsegs (mkCfg (yparse_head_state rav (p_sp E) (p_gp E) (p_tp E) (p_s0 E) (p_s1 E) (p_s2 E) (p_s3 E) (p_s4 E) (p_s5 E)
                           (p_s6 E) (p_s7 E) (p_s8 E) (p_s9 E) (p_s10 E) (p_s11 E) (p_F E) (p_fc E) m
                           (pH E) (p_T E) (pLEN E) (h_used h) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s5v s6v s8v) mo) (p_K E).
Proof.
  intros until s8v. intros OK PM EH ECX0 HST LS CONT.
  pose proof OK as OK'. destruct OK' as (K0 & LP & U0 & SB0 & L26 & TB & SPC & CXB & CEIL & LO & TP & B64 & PYR).
  pose proof PM as PM'. destruct PM' as (RY & HR & SAME & CXR & TXT & (padw & FR) & AX & STK & ERR & MI & PRES & SB1 & LK0).
  rewrite <- EH in LP, U0. rewrite <- ECX0 in LP.
  assert (HINV : hinv (pLEN E) h cx).
  { destruct LP as [HI|(_ & s0 & rest0 & HS0 & HE0)]; [exact HI|]. exfalso. rewrite HST in HS0. injection HS0 as <- <-. destruct st; discriminate. }
  apply RYST_split in RY. destruct RY as [HK0 YS].
  pose proof HR as (HS & LXR & DBR & BSR). pose proof HS as ((pew & pad & HC & PW) & BC1 & BC2 & BC3 & BC4).
  pose proof SAME as (EID & EHA & ELID & ELX & ELBI & ELBA & EDBI & EDBA & ECX). unfold pCX, pH, pSP in *.
  unfold yparse_head_state.
  pose proof (proj1 STK) as LO0.
  unfold RYajlRep.bs_rep in BSR. destruct (h_stack_blk h) as [sbk|] eqn:HSB; [| congruence]. destruct BSR as (SBNZ & junk & SC).
  unfold hand_cells, hand_head_cells, alloc_cells in HC. cbn [yc_callbacks yc_malloc_w yc_realloc_w yc_free_w ryc app] in HC. unfold wz in HC.
  rewrite EHA in HC.
  pose proof (rw_cells_bound _ _ _ _ HC) as HCB. cbn [cells_size csize Nat.add length] in HCB.
  unfold yparse_frame in FR. pose proof (rw_cells_bound _ _ _ _ FR) as FRBB. cbn [cells_size csize Nat.add length] in FRBB.
  (* [comment removed for export] *)
  rz_seg HKS HK0.
  eapply evt_cut.
  { eapply (head_dispatch _ _ _ _ (p_s0 E) (p_s1 E) (p_s2 E) (p_s3 E) (p_s4 E) (p_s5 E) (p_s6 E) (p_s7 E) (p_s8 E) (p_s9 E) (p_s10 E) (p_s11 E));
      [exact HST| exact EHA| reflexivity| | exact SC| clear -BC2; lia| clear -BC3; lia| exact MI].
    unfold hand_cells, hand_head_cells, alloc_cells. cbn [yc_callbacks yc_malloc_w yc_realloc_w yc_free_w ryc app]. unfold wz. rewrite EHA. exact HC. }
  intros ms' ->.
  assert (TGT : exists tg, state_target st = tg /\ (tg = 0x15494 \/ tg = 0x154fc \/ tg = 0x15600 \/ tg = 0x15558 \/ tg = 0x155ac)).
  { destruct st; try discriminate; cbn; eauto 8. }
  destruct TGT as (tg & ETG & TGS). rewrite ETG in CONT |- *. unfold wz.
  assert (LC : forall raw (t0 t1 t2 a6 a7 t3 t4 t5 t6 : word), raw = Z_to_bv 64 (tg + 28) ->
    realizes_cfg acfg rsegs (mkCfg (MS (mkR raw (p_sp E) (p_gp E) (p_tp E) t0 t1 t2 (wz (mh_addr (p_mh E))) (wz (mh_addr (p_mh E) + 48)) (wz (mh_lexer mh)) (wz (p_T E)) (wz (pLEN E)) (wz (mh_addr (p_mh E) + 32))
                                  (wz (bv_unsigned (p_sp E) + 24)) (wz (bv_unsigned (p_sp E) + 20)) a6 a7
                                  (wz (pLEN E)) (wz (p_T E)) (wz (mh_addr (p_mh E) + 32)) (wz 0) s6v (wz 11) s8v (wz RY_JT_TOKVAL) (wz 13) (wz RY_JT_STATE) t3 t4 t5 t6)
                             (p_F E) (wz RY_LEX_LEX) (p_fc E) None m (seg_rom rsegs)) mo) (p_K E)).
  { intros raw t0x t1x t2x a6x a7x t3x t4x t5x t6x ->. eapply lex_call; [exact OK| exact PM| exact HINV|].
    intros until LK'. intros YL LPOST PM2.
    replace (ret_pc (Z_to_bv 64 (tg + 28))) with (Z_to_bv 64 (tg + 28)) by (symmetry; apply ret_pc_even; [clear -TGS; lia| destruct TGS as [-> |[-> |[-> |[-> | ->]]]]; reflexivity]).
    unfold pstate, wz in CONT. eapply CONT; [exact YL| exact LPOST| exact HINV| exact PM2]. }
  unfold wz, RY_LEX_LEX, RY_JT_TOKVAL, RY_JT_STATE in LC.
  destruct TGS as [-> |[-> |[-> |[-> | ->]]]];
    (zstep; zstep; zstep; zstep; zstep; zstep; zstep; apply evt_done; apply LC; reflexivity).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma munch_agree : forall W m m', munch W m m' -> wmono rsegs m m' -> agree_on rsegs (outside W) m m'.
Proof.
  intros W m m' MU WM a Ha Ho. split; [| apply WM]. apply MU. rewrite wa_unsigned by exact Ha. exact Ho.
Qed.

Definition ownA (E : penv) (mh : mhand) (h : yhandle) (iv : Z * Z) : Prop :=
  (mh_addr mh <= fst iv /\ snd iv <= mh_addr mh + 72)
  \/ (mh_stack mh <= fst iv /\ snd iv <= mh_stack mh + h_stack_size h)
  \/ (pCX E <= fst iv /\ snd iv <= pCX E + 8)
  \/ (p_lo E <= fst iv /\ snd iv <= pSP E + 144).

Lemma ownA_outside : forall E mh h W a,
  Forall (ownA E mh h) W ->
  (a < mh_addr mh \/ mh_addr mh + 72 <= a) -> (a < mh_stack mh \/ mh_stack mh + h_stack_size h <= a) ->
  (a < pCX E \/ pCX E + 8 <= a) -> (a < p_lo E \/ pSP E + 144 <= a) -> outside W a.
Proof.
  intros E mh h W a HF H1 H2 H3 H4. induction HF as [| [lo hi] W HO HF IH]; [exact I|].
  cbn. split; [| exact IH]. unfold ownA in HO. cbn [fst snd] in HO. lia.
Qed.

Lemma ownA_write_ok : forall E mh h LB W,
  Forall (ownA E mh h) W ->
  In (mh_id mh, mh_addr mh, SIZEOF_HANDLE) LB -> In (mh_sid mh, mh_stack mh, h_stack_size h) LB ->
  alloc_ceiling <= p_lo E -> p_lo E <= pSP E -> pSP E + 144 <= pCX E ->
  Forall (rclient_write_ok LB) W.
Proof.
  intros E mh h LB W HF I1 I2 C1 C2 C3. induction HF as [| [lo hi] W HO HF IH]; constructor; [| exact IH].
  unfold ownA in HO. unfold rclient_write_ok. cbn [fst snd] in *.
  destruct HO as [HO|[HO|[HO|HO]]].
  - right; right. eexists. split; [exact I1|]. cbn. unfold SIZEOF_HANDLE. lia.
  - right; right. eexists. split; [exact I2|]. cbn. lia.
  - left. lia.
  - left. lia.
Qed.

(* [comment removed for export] *)
Lemma pmem_ranges : forall E m mo s LK h mh cx obw olw,
  pok E -> pmem E m mo s LK h mh cx obw olw ->
  let LB := yblocks mh h ++ LK ++ p_REST E in
  In (mh_id mh, mh_addr mh, SIZEOF_HANDLE) LB /\ In (mh_sid mh, mh_stack mh, h_stack_size h) LB
  /\ (0 < mh_addr mh /\ mh_addr mh + 104 <= (Z.max 0x7fff80000000 (Z.min 0x800000000000 rc_sp) - 8388608) /\ (mh_addr mh + 104 <= 0x10000 \/ 0x56000 <= mh_addr mh))
  /\ (0 < mh_stack mh /\ mh_stack mh + h_stack_size h <= (Z.max 0x7fff80000000 (Z.min 0x800000000000 rc_sp) - 8388608) /\ (mh_stack mh + h_stack_size h <= 0x10000 \/ 0x56000 <= mh_stack mh))
  /\ (mh_addr mh + 104 <= mh_stack mh \/ mh_stack mh + h_stack_size h <= mh_addr mh)
  /\ 0 <= h_bytesConsumed h < 2^31 /\ 0 <= h_stack_size h < 2^31 /\ 0 <= h_used h <= h_stack_size h.
Proof.
  intros until olw. intros OK PM.
  destruct OK as (K0 & LP & U0 & SB0 & L26 & TB & SPC & CXB & CEIL & LO & TP & B64 & PYR).
  destruct PM as (RY & HR & SAME & CXR & TXT & (padw & FR) & AX & STK & ERR & MI & PRES & SB1 & LK0).
  apply RYST_split in RY. destruct RY as [HK0 YS]. destruct (HK_blocks HK HKB _ _ _ _ HK0) as [RNG SEP].
  destruct HR as ((_ & B1 & B2 & B3 & B4) & _ & _ & BSR).
  assert (I1 : In (mh_id mh, mh_addr mh, SIZEOF_HANDLE) (yblocks mh h ++ LK ++ p_REST E)) by (left; reflexivity).
  assert (I2 : In (mh_sid mh, mh_stack mh, h_stack_size h) (yblocks mh h ++ LK ++ p_REST E)).
  { unfold yblocks. cbn [app]. right. apply in_or_app; left. apply in_or_app; right. apply in_or_app; right.
    unfold bs_blocks. destruct (h_stack_blk h); [left; reflexivity| congruence]. }
  pose proof (all_range_In _ _ RNG I1) as R1. pose proof (all_range_In _ _ RNG I2) as R2.
  unfold rblock_range, alloc_ceiling, SIZEOF_HANDLE in R1, R2. cbn [blk_addr blk_size fst snd] in R1, R2.
  cbn [all_sep yblocks app] in SEP. destruct SEP as [SEPH _].
  pose proof (sep_from_In _ _ _ SEPH ltac:(apply in_or_app; left; apply in_or_app; right; apply in_or_app; right;
     unfold bs_blocks; destruct (h_stack_blk h); [left; reflexivity| congruence])) as S12.
  unfold bsep, SIZEOF_HANDLE in S12. cbn [blk_addr blk_size fst snd] in S12.
  cbn zeta. split; [exact I1|]. split; [exact I2|]. split; [lia|]. split; [lia|]. split; [lia|]. lia.
Qed.

Lemma all_sep_mid : forall (l1 : list block) x l2 y, all_sep (l1 ++ x :: l2) -> In y l1 -> bsep y x.
Proof.
  induction l1 as [|z l1 IH]; intros x l2 y H Hy; [destruct Hy|].
  cbn in H. destruct H as [H1 H2]. destruct Hy as [<-|Hy].
  - apply (sep_from_In _ _ _ H1). apply in_or_app. right. left. reflexivity.
  - exact (IH _ _ _ H2 Hy).
Qed.
Lemma all_sep_tail : forall (l1 : list block) x l2 y, all_sep (l1 ++ x :: l2) -> In y l2 -> bsep x y.
Proof. intros l1 x l2 y H Hy. apply all_sep_app_r in H. cbn in H. destruct H as [H _]. exact (sep_from_In _ _ _ H Hy). Qed.

(* [comment removed for export] *)
Definition mid_blocks (mh : mhand) (h : yhandle) : list block :=
  lexer_blocks (mh_lid mh) (mh_lexer mh) (mh_lexbuf mh) (h_lexer h) ++ buf_blocks (mh_decbuf mh) (h_decbuf h).
Lemma yblocks_mid : forall mh h LK REST, h_stack_blk h <> None ->
  yblocks mh h ++ LK ++ REST = (mh_id mh, mh_addr mh, SIZEOF_HANDLE) :: (mid_blocks mh h ++ (mh_sid mh, mh_stack mh, h_stack_size h) :: (LK ++ REST)).
Proof.
  intros mh h LK REST HB. unfold yblocks, mid_blocks, bs_blocks. destruct (h_stack_blk h); [| congruence].
  cbn [app]. rewrite <- !app_assoc. reflexivity.
Qed.

Lemma pmem_updA : forall E m m' mo s LK h mh cx obw olw h' cx' obw' olw' W,
  pok E -> pmem E m mo s LK h mh cx obw olw ->
  munch W m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
  Forall (ownA E mh h) W ->
  h_lexer h' = h_lexer h -> h_decbuf h' = h_decbuf h -> h_stack_blk h' = h_stack_blk h -> h_stack_size h' = h_stack_size h ->
  hand_struct m' h' mh -> bs_rep m' (mh_stack mh) h' -> ctx_rep m' (pCX E) cx' ->
  (exists padw, yparse_frame m' (p_sp E) (p_ra E) (p_s0 E) (p_s1 E) (p_s2 E) (p_s3 E) (p_s4 E) (p_s5 E) (p_s6 E) (p_s7 E)
                              (p_s8 E) (p_s9 E) (p_s10 E) (p_s11 E) (reg_get (p_F E) 8%bv) padw obw' olw') ->
  stk rsegs m' (p_lo E) (pSP E) ->
  pmem E m' mo s LK h' mh cx' obw' olw'.
Proof.
  intros until W. intros OK PM MU WM MI' OWN EL ED EB ES HS' BS' CX' FR' STK'.
  pose proof (pmem_ranges _ _ _ _ _ _ _ _ _ _ OK PM) as (I1 & I2 & R1 & R2 & S12 & B1 & B2 & B3).
  destruct OK as (K0 & LP & U0 & SB0 & L26 & TB & SPC & CXB & CEIL & LO & TP & B64 & PYR).
  destruct PM as (RY & HR & SAME & CXR & TXT & (padw & FR) & AX & STK & ERR & MI & PRES & SB1 & LK0).
  apply RYST_split in RY. destruct RY as [HK0 YS]. destruct (HK_blocks HK HKB _ _ _ _ HK0) as [RNG SEP].
  destruct HR as (HS & LXR & DBR & BSR).
  pose proof (proj1 STK) as LO0. unfold pSP in LO0, STK.
  pose proof AX as (av & x3 & x4 & x5 & x16 & x6 & x11 & x12 & x23 & rnd & _ & _ & _ & CB0 & _). unfold alloc_ceiling in CB0.
  pose proof (munch_agree _ _ _ MU WM) as AG.
  rewrite (yblocks_mid mh h LK (p_REST E) SB1) in RNG, SEP, HK0.
  set (MID := mid_blocks mh h) in *. set (TL := LK ++ p_REST E) in *.
  (* [comment removed for export] *)
  assert (OUT : forall y a, In y MID \/ In y TL -> blk_addr y <= a < blk_addr y + blk_size y -> outside W a).
  { intros y a Hy Ha.
    assert (Ry : rblock_range (blk_addr y) (blk_size y)).
    { apply (all_range_In _ _ RNG). right. apply in_or_app. destruct Hy as [Hy|Hy]; [left; exact Hy| right; right; exact Hy]. }
    unfold rblock_range, alloc_ceiling in Ry.
    cbn [all_sep] in SEP. destruct SEP as [SEPH SEPT].
    assert (D1 : bsep (mh_id mh, mh_addr mh, SIZEOF_HANDLE) y).
    { apply (sep_from_In _ _ _ SEPH). apply in_or_app. destruct Hy as [Hy|Hy]; [left; exact Hy| right; right; exact Hy]. }
    assert (D2 : blk_addr y + blk_size y <= mh_stack mh \/ mh_stack mh + h_stack_size h <= blk_addr y).
    { destruct Hy as [Hy|Hy].
      - pose proof (all_sep_mid _ _ _ _ SEPT Hy) as X. unfold bsep in X. cbn [blk_addr blk_size fst snd] in X. clear -X. lia.
      - pose proof (all_sep_tail _ _ _ _ SEPT Hy) as X. unfold bsep in X. cbn [blk_addr blk_size fst snd] in X. clear -X. lia. }
    unfold bsep, SIZEOF_HANDLE in D1. cbn [blk_addr blk_size fst snd] in D1.
    eapply ownA_outside; [exact OWN| clear -Ha D1; lia| clear -Ha D2; lia| clear -Ha Ry CEIL LO SPC; lia| clear -Ha Ry CEIL; lia]. }
  (* [comment removed for export] *)
  assert (OUTI : forall a, 0x23000 <= a < 0x56000 -> outside W a).
  { intros a Ha. eapply ownA_outside; [exact OWN| clear -Ha R1; lia| clear -Ha R2; lia| clear -Ha CEIL LO SPC; lia| clear -Ha CEIL; lia]. }
  assert (IL : In (mh_lid mh, mh_lexer mh, SIZEOF_LEXER) MID) by (unfold MID, mid_blocks, lexer_blocks; left; reflexivity).
  assert (ILB : In (mb_id (mh_lexbuf mh), mb_addr (mh_lexbuf mh), SIZEOF_BUF) MID) by (unfold MID, mid_blocks, lexer_blocks, buf_blocks; right; left; reflexivity).
  assert (ILD : yb_data (lx_buf (h_lexer h)) <> None -> In (mb_did (mh_lexbuf mh), mb_data (mh_lexbuf mh), yb_len (lx_buf (h_lexer h))) MID).
  { intros HD. unfold MID, mid_blocks, lexer_blocks, buf_blocks. right. destruct (yb_data (lx_buf (h_lexer h))); [| congruence]. right. left. reflexivity. }
  assert (IDB : In (mb_id (mh_decbuf mh), mb_addr (mh_decbuf mh), SIZEOF_BUF) MID).
  { unfold MID, mid_blocks. apply in_or_app. right. left. reflexivity. }
  assert (IDD : yb_data (h_decbuf h) <> None -> In (mb_did (mh_decbuf mh), mb_data (mh_decbuf mh), yb_len (h_decbuf h)) MID).
  { intros HD. unfold MID, mid_blocks, buf_blocks. apply in_or_app. right. destruct (yb_data (h_decbuf h)); [| congruence]. right. left. reflexivity. }
  split.
  { apply RYST_split. rewrite (yblocks_mid mh h' LK (p_REST E)) by (rewrite EB; exact SB1).
    replace (mid_blocks mh h') with MID by (unfold MID, mid_blocks; rewrite EL, ED; reflexivity). rewrite ES. fold TL. split.
    - eapply HKF; [exact HK0| exact MU| exact WM|].
      eapply ownA_write_ok; [exact OWN| left; reflexivity| right; apply in_or_app; right; left; reflexivity| unfold alloc_ceiling; exact CEIL| clear -LO; lia| exact SPC].
    - eapply ystatics_munch; [exact YS| exact MU| exact WM|].
      eapply Forall_impl; [| exact OWN]. intros iv Hiv. unfold ownA in Hiv. unfold RY_CALLBACKS. clear -Hiv R1 R2 CEIL LO SPC. lia. }
  split.
  { split; [exact HS'|]. split; [| split; [| exact BS']].
    - rewrite EL. eapply lexer_rep_agree; [exact AG| exact LXR| | |].
      + intros a Ha. apply (OUT _ a (or_introl IL)). cbn. exact Ha.
      + intros a Ha. apply (OUT _ a (or_introl ILB)). cbn. exact Ha.
      + intros HD a Ha. apply (OUT _ a (or_introl (ILD HD))). cbn. exact Ha.
    - rewrite ED. eapply buf_rep_agree; [exact AG| exact DBR| |].
      + intros a Ha. apply (OUT _ a (or_introl IDB)). cbn. exact Ha.
      + intros HD a Ha. apply (OUT _ a (or_introl (IDD HD))). cbn. exact Ha. }
  split; [exact SAME|]. split; [exact CX'|].
  split.
  { eapply text_at_agree; [exact AG| exact TXT|]. intros a Ha.
    destruct TB as [(bt & HIN & HB)|Z0]; [| unfold pLEN in Z0; clear -Ha Z0; lia].
    apply (OUT bt a); [right; unfold TL; apply in_or_app; right; exact HIN| unfold pLEN in HB; clear -Ha HB; lia]. }
  split; [exact FR'|].
  split.
  { eapply rauxv_ok_frame; [exact AX| exact MU| exact WM|].
    eapply Forall_impl; [| exact OWN]. intros iv Hiv. unfold ownA in Hiv. unfold RAUXV_CELL. clear -Hiv R1 R2 CEIL LO SPC CXB CB0. lia. }
  split; [exact STK'|].
  split.
  { destruct ERR as [errv ERR]. exists errv. eapply rw_cells_agree; [exact AG| exact ERR|].
    rewrite (ry_errno_lit _ TP). unfold RERRNO. cbn. intros a Ha. apply OUTI. clear -Ha. lia. }
  split; [exact MI'|].
  split.
  { eapply ry_pres_trans; [exact PRES|]. eapply ryajl_pres_of_munch; [exact MU| exact WM|].
    intros a Ha Hc Hx. destruct Hc as [Hc|[[Hc _]|(b & Hb & Hr)]].
    - eapply ownA_outside; [exact OWN| clear -Hc R1 CEIL LO SPC; lia| clear -Hc R2 CEIL LO SPC; lia| | clear -Hc; lia].
      assert (~ (pCX E <= a < pCX E + 8)) by (intros X; apply Hx; left; exact X). clear -H. lia.
    - apply OUTI. exact Hc.
    - apply (OUT b a); [right; unfold TL; apply in_or_app; right; exact Hb| exact Hr]. }
  split; [rewrite EB; exact SB1| exact LK0].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma J_setb : forall E m mo s LK h mh cx obw olw st rest s'
    (rav t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s5v s6v s8v : word),
  pok E -> pmem E m mo s LK h mh cx obw olw -> h_stack h = st :: rest ->
  yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) (p_h E) (p_cx E)) (SR_again (h_set_stack h (s' :: rest)) cx) ->
  again_cont E ->
  realizes_cfg acfg rsegs (mkCfg (pstate E 0x15ab0 m rav t0 t1 t2 (wz (mh_stack mh + h_used h - 1)) (wz (state_code s')) a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s5v s6v s8v (wz 13)) mo) (p_K E).
Proof.
  intros until s8v. intros OK PM HST YL AG.
  pose proof (pmem_ranges _ _ _ _ _ _ _ _ _ _ OK PM) as (I1 & I2 & R1 & R2 & S12 & B1 & B2 & B3).
  pose proof OK as OK'. destruct OK' as (K0 & LP & U0 & SB0 & L26 & TB & SPC & CXB & CEIL & LO & TP & B64 & PYR).
  pose proof PM as PM'. destruct PM' as (RY & HR & SAME & CXR & TXT & (padw & FR) & AX & STK & ERR & MI & PRES & SB1 & LK0).
  apply RYST_split in RY. destruct RY as [HK0 YS].
  pose proof HR as (HS & LXR & DBR & BSR). pose proof HS as ((pew & pad & HC & PW) & _ & _ & _ & BC4).
  unfold RYajlRep.bs_rep in BSR. destruct (h_stack_blk h) as [sbk|] eqn:HSB; [| congruence]. destruct BSR as (SBNZ & junk & SC).
  destruct CXR as [CXC CXB2]. unfold yparse_frame in FR. unfold pSP in STK, LO. unfold pSP, pCX in CXC, SPC, CXB.
  assert (USED : h_used h = zlength rest + 1) by (unfold h_used; rewrite HST; unfold zlength; cbn [length]; lia).
  assert (Z0 : 0 <= zlength rest) by (unfold zlength; clear; lia).
  pose proof (state_code_range s') as CR.
  clear ERR TXT LXR DBR.
  unfold hand_cells, hand_head_cells, alloc_cells in HC. cbn [yc_callbacks yc_malloc_w yc_realloc_w yc_free_w ryc app] in HC. unfold wz in HC.
  pose proof (rw_cells_bound _ _ _ _ FR) as FRB. cbn [cells_size csize Nat.add length] in FRB.
  unfold pstate, wz.
  pose proof (munch_refl [(mh_stack mh + h_used h - 1, mh_stack mh + h_used h)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  destruct (u8arr_of_CB2 _ _ _ _ _ _ _ SC) as (ARR & L1 & L2). clear SC.
  pose proof L1 as L1'. rewrite zbytes_length, stack_bytes_length, HST in L1'. cbn [length] in L1'.
  assert (LEN : length (zbytes (stack_bytes (h_stack h)) ++ junk) = Z.to_nat (h_stack_size h)) by (rewrite length_app; clear -L1 L2 B3; lia).
  rz_seg HKS HK0.
  match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    pose proof (u8arr_store_ok_at rsegs mx (mh_stack mh) _ (h_used h - 1) ARR ltac:(rewrite length_app; clear -L1 L2 B3 USED Z0; lia)) as SOK end.
  step.
  match type of ARR with Arr.u8arr _ ?mx _ _ =>
    pose proof (u8arr_write rsegs mx (mh_stack mh) _ (h_used h - 1) (Z_to_bv 8 (state_code s')) ARR ltac:(rewrite length_app; clear -L1 L2 B3 USED Z0; lia)) as ARR' end.
  rewrite le1_wz by (clear -CR; lia). clear ARR.
  store_done.
  step. apply evt_done.
  eapply J_back; [exact OK| | exact YL| exact AG].
  eapply pmem_updA; [exact OK| exact PM| exact MU| exact WM| exact MI| | reflexivity| reflexivity| reflexivity| reflexivity| | | split; [exact CXC| exact CXB2]| exists padw; exact FR| exact STK].
  - constructor; [| constructor]. unfold ownA. cbn [fst snd]. clear -B3 USED Z0. lia.
  - split; [| cbn [h_set_stack h_bytesConsumed h_stack_size h_stack_blk h_parseError]; rewrite HSB; repeat split; try lia; try (intros; congruence)].
    2:{ unfold h_used. cbn [h_stack h_set_stack]. unfold zlength. cbn [length]. clear -Z0 USED B3. unfold h_used, zlength in *. lia. }
    2:{ unfold h_used. cbn [h_stack h_set_stack]. unfold zlength. cbn [length]. clear -Z0 USED B3. unfold h_used, zlength in *. lia. }
    exists pew, pad. split; [| exact PW].
    unfold hand_cells, hand_head_cells, alloc_cells. cbn [yc_callbacks yc_malloc_w yc_realloc_w yc_free_w ryc app h_set_stack h_bytesConsumed h_stack_size]. unfold wz.
    replace (h_used (h_set_stack h (s' :: rest))) with (h_used h) by (unfold h_used; cbn [h_stack h_set_stack]; rewrite HST; reflexivity). exact HC.
  - unfold RYajlRep.bs_rep. cbn [h_stack_blk h_set_stack h_stack h_stack_size]. rewrite HSB. split; [exact SBNZ|].
    exists junk.
    replace (h_used (h_set_stack h (s' :: rest))) with (h_used h) by (unfold h_used; cbn [h_stack h_set_stack]; rewrite HST; reflexivity).
    apply CB2_of_u8arr; [| rewrite zbytes_length, stack_bytes_length; cbn [length]; clear -L1' ; lia | exact L2].
    revert ARR'. rewrite HST, !stack_bytes_cons, !zbytes_app. cbn [zbytes map]. rewrite <- !app_assoc. cbn [app].
    replace (mh_stack mh + (h_used h - 1)) with (mh_stack mh + h_used h - 1) by (clear; lia).
    rewrite (upd_app_len _ _ _ _ _) by (rewrite zbytes_length, stack_bytes_length; unfold zlength in USED; clear -USED; lia).
    intros ARR'. exact ARR'.
Qed.

End S.

(* [comment removed for export] *)
(* [comment removed for export] *)
End RC__1.
Ltac open_env HKB OK PM :=
  pose proof (pmem_ranges _ HKB _ _ _ _ _ _ _ _ _ _ OK PM) as (I1 & I2 & R1 & R2 & S12 & B1 & B2 & B3);
  pose proof OK as OK'; destruct OK' as (K0 & LP & U0 & SB0 & L26 & TB & SPC & CXB & CEIL & LO & TP & B64 & PYR);
  pose proof PM as PM'; destruct PM' as (RY & HR & SAME & CXR & TXT & (padw & FR) & AX & STK & ERR & MI & PRES & SB1 & LK0);
  apply RYST_split in RY; destruct RY as [HK0 YS];
  pose proof HR as (HS & LXR & DBR & BSR); pose proof HS as ((pew & pad & HC & PW) & _ & _ & _ & BC4);
  unfold RYajlRep.bs_rep in BSR;
  let sbk := fresh "sbk" in let HSB := fresh "HSB" in
  destruct (h_stack_blk _) as [sbk|] eqn:HSB in BSR; [| exfalso; exact (SB1 HSB)];
  let junk := fresh "junk" in destruct BSR as (SBNZ & junk & SC);
  destruct CXR as [CXC CXB2]; unfold yparse_frame in FR; unfold pSP in STK, LO; unfold pSP, pCX in CXC, SPC, CXB;
  unfold hand_cells, hand_head_cells, alloc_cells in HC; cbn [yc_callbacks yc_malloc_w yc_realloc_w yc_free_w ryc app] in HC; unfold wz in HC;
  pose proof (rw_cells_bound _ _ _ _ FR) as FRB; cbn [cells_size csize Nat.add length] in FRB;
  let EHA := fresh "EHA" in let ECX := fresh "ECX" in
  pose proof SAME as (_ & EHA & _ & _ & _ & _ & _ & _ & ECX); rewrite EHA in *; unfold pH.


Section RC__2.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section S2.
Variable HK : RawAlloc.PState -> list block -> (word -> option byte) -> Model -> Prop.
Hypothesis HKS : HK_silent_stmt HK.
Hypothesis HKP : HK_perm_stmt HK.
Hypothesis HKF : HK_frame_stmt HK.
Hypothesis HKB : HK_blocks_stmt HK.
Hypothesis YLX : ylex_lex_stmt HK.
Notation buf_rep := (buf_rep rsegs).
Notation buf_struct := (buf_struct rsegs).
Notation buf_data := (buf_data rsegs).
Notation lexer_rep := (lexer_rep rsegs).
Notation hand_rep := (hand_rep rsegs ryc).
Notation hand_struct := (hand_struct rsegs ryc).
Notation bs_rep := (bs_rep rsegs).
Notation ctx_rep := (ctx_rep rsegs).
Notation text_at := (text_at rsegs).
Notation RYST := (RYST HK).
Notation yparse_head_inv := (yparse_head_inv HK).
Notation yparse_exit_cont := (yparse_exit_cont HK).
Notation pmem := (pmem HK).
Notation again_cont := (again_cont HK).
Notation exit_cont := (exit_cont HK).
Notation yhead_invX := (yhead_invX HK).

Ltac kill K := exfalso; revert K; unfold wz; rewrite ?unsigned_lit by lia;
  try (change 18446744073709551615 with (Z.ones 64); rewrite ?Z.land_ones by lia; rewrite ?Z.mod_small by lia); lia.

(* [comment removed for export] *)
Lemma J_lexerr : forall E m mo s LK h mh cx obw olw st rest
    (rav t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s5v s6v s8v : word),
  pok E -> pmem E m mo s LK h mh cx obw olw -> h_stack h = st :: rest ->
  yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) (p_h E) (p_cx E)) (SR_again (h_set_stack h (ST_lexical_error :: rest)) cx) ->
  again_cont E ->
  realizes_cfg acfg rsegs (mkCfg (pstate E 0x15a98 m rav t0 t1 t2 (wz (h_used h)) a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s5v s6v s8v (wz 13)) mo) (p_K E).
Proof.
  intros until s8v. intros OK PM HST YL AG. open_env HKB OK PM.
  assert (USED : h_used h = zlength rest + 1) by (unfold h_used; rewrite HST; unfold zlength; cbn [length]; lia).
  assert (Z0 : 0 <= zlength rest) by (unfold zlength; clear; lia).
  clear ERR TXT LXR DBR. unfold pstate, pH, wz.
  rz_seg HKS HK0.
  zstep. zstep. zstep. zstep. rewrite (land_M32_small (h_used h + -1)) by (clear -USED Z0 B3 B2; lia). zstep. zstep.
  apply evt_done.
  replace (mh_stack mh + (h_used h + -1)) with (mh_stack mh + h_used h - 1) by (clear; lia).
  change (Z_to_bv 64 3) with (wz (state_code ST_lexical_error)).
  pose proof (J_setb HK HKS HKF HKB E) as JS. unfold pstate, pH in JS. eapply JS; [exact OK| exact PM| exact HST| exact YL| exact AG].
Qed.

(* [comment removed for export] *)
Lemma J_perr : forall E m mo s LK h mh cx obw olw st rest e
    (rav t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s5v s6v s8v : word),
  pok E -> pmem E m mo s LK h mh cx obw olw -> h_stack h = st :: rest ->
  yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) (p_h E) (p_cx E)) (SR_again (h_set_perr (h_set_stack h (ST_parse_error :: rest)) e) cx) ->
  again_cont E ->
  realizes_cfg acfg rsegs (mkCfg (pstate E 0x15b4c m rav t0 t1 t2 (wz (mh_stack mh + h_used h - 1)) (wz (yc_perr ryc e)) a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s5v s6v s8v (wz 13)) mo) (p_K E).
Proof.
  intros until s8v. intros OK PM HST YL AG. open_env HKB OK PM.
  assert (USED : h_used h = zlength rest + 1) by (unfold h_used; rewrite HST; unfold zlength; cbn [length]; lia).
  assert (Z0 : 0 <= zlength rest) by (unfold zlength; clear; lia).
  clear ERR TXT LXR DBR. unfold pstate, pH, wz.
  pose proof (munch_refl [(mh_stack mh + h_used h - 1, mh_stack mh + h_used h); (mh_addr mh + 24, mh_addr mh + 32)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  destruct (u8arr_of_CB2 _ _ _ _ _ _ _ SC) as (ARR & L1 & L2). clear SC.
  pose proof L1 as L1'. rewrite zbytes_length, stack_bytes_length, HST in L1'. cbn [length] in L1'.
  assert (LEN : length (zbytes (stack_bytes (h_stack h)) ++ junk) = Z.to_nat (h_stack_size h)) by (rewrite length_app; clear -L1 L2 B3; lia).
  rz_seg HKS HK0.
  zstep.
  match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    pose proof (u8arr_store_ok_at rsegs mx (mh_stack mh) _ (h_used h - 1) ARR ltac:(rewrite length_app; clear -L1 L2 B3 USED Z0; lia)) as SOK end.
  replace (mh_stack mh + h_used h - 1) with (mh_stack mh + (h_used h - 1)) by (clear; lia).
  step.
  match type of ARR with Arr.u8arr _ ?mx _ _ =>
    pose proof (u8arr_write rsegs mx (mh_stack mh) _ (h_used h - 1) (Z_to_bv 8 2) ARR ltac:(rewrite length_app; clear -L1 L2 B3 USED Z0; lia)) as ARR' end.
  change (le1 (Z_to_bv 64 2)) with [Z_to_bv 8 2]. clear ARR. store_done.
  zstep. step. apply evt_done.
  pose proof (J_back HK HKS E) as JB. unfold pstate, pH in JB. eapply JB; [exact OK| | exact YL| exact AG].
  eapply pmem_updA; [exact HKF| exact HKB| exact OK| exact PM| exact MU| exact WM| exact MI| | reflexivity| reflexivity| reflexivity| reflexivity| | | split; [exact CXC| exact CXB2]| exists padw; exact FR| exact STK].
  - constructor; [| constructor; [| constructor]]; unfold ownA; cbn [fst snd]; clear -B3 USED Z0; lia.
  - split; [| cbn [h_set_perr h_set_stack h_bytesConsumed h_stack_size h_stack_blk h_parseError]; rewrite HSB;
             replace (h_used (h_set_perr (h_set_stack h (ST_parse_error :: rest)) e)) with (h_used h) by (unfold h_used; cbn [h_stack h_set_stack h_set_perr]; rewrite HST; reflexivity);
             repeat split; try (clear -B1 B2 B3; lia); intros; congruence].
    exists (Z_to_bv 64 (yc_perr ryc e)), pad. split; [| reflexivity].
    unfold hand_cells, hand_head_cells, alloc_cells. cbn [yc_callbacks yc_malloc_w yc_realloc_w yc_free_w ryc app h_set_perr h_set_stack h_bytesConsumed h_stack_size]. unfold wz.
    replace (h_used (h_set_perr (h_set_stack h (ST_parse_error :: rest)) e)) with (h_used h) by (unfold h_used; cbn [h_stack h_set_stack h_set_perr]; rewrite HST; reflexivity). rewrite EHA. exact HC.
  - unfold RYajlRep.bs_rep. cbn [h_stack_blk h_set_stack h_set_perr h_stack h_stack_size]. rewrite HSB. split; [exact SBNZ|].
    exists junk.
    replace (h_used (h_set_perr (h_set_stack h (ST_parse_error :: rest)) e)) with (h_used h) by (unfold h_used; cbn [h_stack h_set_stack h_set_perr]; rewrite HST; reflexivity).
    apply CB2_of_u8arr; [| rewrite zbytes_length, stack_bytes_length; cbn [length]; clear -L1' ; lia | exact L2].
    revert ARR'. rewrite HST, !stack_bytes_cons, !zbytes_app. cbn [zbytes map state_code]. rewrite <- !app_assoc. cbn [app].
    rewrite (upd_app_len _ _ _ _ _) by (rewrite zbytes_length, stack_bytes_length; unfold zlength in USED; clear -USED; lia).
    intros ARR'. exact ARR'.
Qed.

(* [comment removed for export] *)
Lemma J_fail4 : forall E m mo s LK h mh cx obw olw
    (rav t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s5v s6v s8v s10v : word),
  pok E -> pmem E m mo s LK h mh cx obw olw ->
  yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) (p_h E) (p_cx E)) (SR_done YS_alloc_failed (h_set_perr h PE_alloc_failed) cx) ->
  exit_cont E ->
  realizes_cfg acfg rsegs (mkCfg (pstate E 0x160e4 m rav t0 t1 t2 (wz (yc_perr ryc PE_alloc_failed)) a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s5v s6v s8v s10v) mo) (p_K E).
Proof.
  intros until s10v. intros OK PM YL EX. open_env HKB OK PM.
  clear ERR TXT LXR DBR. unfold pstate, pH, wz.
  pose proof (munch_refl [(mh_addr mh + 24, mh_addr mh + 32)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  rz_seg HKS HK0.
  zstep. zstep. step. apply evt_done.
  change (Z_to_bv 64 4) with (wz (status_code YS_alloc_failed)).
  pose proof (J_exit HK HKS E) as JE. unfold pstate, pH in JE. eapply JE; [exact OK| | exact YL| exact EX].
  eapply pmem_updA; [exact HKF| exact HKB| exact OK| exact PM| exact MU| exact WM| exact MI| | reflexivity| reflexivity| reflexivity| reflexivity| | | split; [exact CXC| exact CXB2]| exists padw; exact FR| exact STK].
  - constructor; [| constructor]. unfold ownA; cbn [fst snd]. clear. lia.
  - split; [| cbn [h_set_perr h_bytesConsumed h_stack_size h_stack_blk h_parseError]; rewrite HSB;
             replace (h_used (h_set_perr h PE_alloc_failed)) with (h_used h) by reflexivity; repeat split; try (clear -B1 B2 B3; lia); intros; congruence].
    exists (Z_to_bv 64 (yc_perr ryc PE_alloc_failed)), pad. split; [| reflexivity].
    unfold hand_cells, hand_head_cells, alloc_cells. cbn [yc_callbacks yc_malloc_w yc_realloc_w yc_free_w ryc app h_set_perr h_bytesConsumed h_stack_size]. unfold wz.
    replace (h_used (h_set_perr h PE_alloc_failed)) with (h_used h) by reflexivity. rewrite EHA. exact HC.
  - unfold RYajlRep.bs_rep. cbn [h_stack_blk h_set_perr h_stack h_stack_size]. rewrite HSB. split; [exact SBNZ|]. exists junk. exact SC.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma pmem_setb : forall E m m' mo s LK h mh cx obw olw st rest s' junk,
  pok E -> pmem E m mo s LK h mh cx obw olw -> h_stack h = st :: rest ->
  munch [(mh_stack mh + h_used h - 1, mh_stack mh + h_used h)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
  u8arr rsegs m' (mh_stack mh) (upd (zbytes (stack_bytes (h_stack h)) ++ junk) (Z.to_nat (h_used h - 1)) (Z_to_bv 8 (state_code s'))) ->
  length junk = Z.to_nat (h_stack_size h - h_used h) ->
  (exists pew pad, rw_cells rsegs m' (mh_addr mh) (hand_cells ryc h mh pew pad) /\ perr_word ryc (h_parseError h) pew) ->
  rw_cells rsegs m' (pCX E) (ctx_cells cx) ->
  (exists padw, yparse_frame m' (p_sp E) (p_ra E) (p_s0 E) (p_s1 E) (p_s2 E) (p_s3 E) (p_s4 E) (p_s5 E) (p_s6 E) (p_s7 E)
                              (p_s8 E) (p_s9 E) (p_s10 E) (p_s11 E) (reg_get (p_F E) 8%bv) padw obw olw) ->
  stk rsegs m' (p_lo E) (pSP E) ->
  pmem E m' mo s LK (h_set_stack h (s' :: rest)) mh cx obw olw.
Proof.
  intros until junk. intros OK PM HST MU WM MI' ARR' L2 (pew & pad & HC' & PW) CXC' FR' STK'.
  pose proof (pmem_ranges _ HKB _ _ _ _ _ _ _ _ _ _ OK PM) as (I1 & I2 & R1 & R2 & S12 & B1 & B2 & B3).
  pose proof PM as (RY & HR & SAME & CXR & _). destruct CXR as [_ CXB2].
  pose proof HR as ((_ & _ & _ & _ & BC4) & _ & _ & BSR). unfold RYajlRep.bs_rep in BSR.
  destruct (h_stack_blk h) as [sbk|] eqn:HSB; [| destruct PM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SB1 & _); congruence].
  destruct BSR as [SBNZ _].
  assert (USED : h_used h = zlength rest + 1) by (unfold h_used; rewrite HST; unfold zlength; cbn [length]; lia).
  assert (Z0 : 0 <= zlength rest) by (unfold zlength; clear; lia).
  assert (EU : h_used (h_set_stack h (s' :: rest)) = h_used h) by (unfold h_used; cbn [h_stack h_set_stack]; rewrite HST; reflexivity).
  eapply pmem_updA; [exact HKF| exact HKB| exact OK| exact PM| exact MU| exact WM| exact MI'| | reflexivity| reflexivity| reflexivity| reflexivity| | | split; [exact CXC'| exact CXB2]| exact FR'| exact STK'].
  - constructor; [| constructor]. unfold ownA. cbn [fst snd]. clear -B3 USED Z0. lia.
  - split; [| cbn [h_set_stack h_bytesConsumed h_stack_size h_stack_blk h_parseError]; rewrite HSB, EU; repeat split; try (clear -B1 B2 B3; lia); intros; congruence].
    exists pew, pad. split; [| exact PW].
    unfold hand_cells, hand_head_cells. cbn [h_set_stack h_bytesConsumed h_stack_size h_parseError]. rewrite EU. exact HC'.
  - unfold RYajlRep.bs_rep. cbn [h_stack_blk h_set_stack h_stack h_stack_size]. rewrite HSB, EU. split; [exact SBNZ|].
    exists junk.
    apply CB2_of_u8arr; [| rewrite zbytes_length, stack_bytes_length; cbn [length]; unfold zlength in USED; clear -USED; lia | exact L2].
    revert ARR'. rewrite HST, !stack_bytes_cons, !zbytes_app. cbn [zbytes map]. rewrite <- !app_assoc. cbn [app].
    rewrite (upd_app_len _ _ _ _ _) by (rewrite zbytes_length, stack_bytes_length; unfold zlength in USED; clear -USED; lia).
    intros ARR'. exact ARR'.
Qed.

(* [comment removed for export] *)
Lemma pmem_pop : forall E m m' mo s LK h mh cx obw olw st rest,
  pok E -> pmem E m mo s LK h mh cx obw olw -> h_stack h = st :: rest ->
  munch [(mh_addr mh + 60, mh_addr mh + 64)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
  (exists pew pad, rw_cells rsegs m' (mh_addr mh) (hand_cells ryc (h_set_stack h rest) mh pew pad) /\ perr_word ryc (h_parseError h) pew) ->
  (exists junk, rw_cells rsegs m' (mh_stack mh) [CB (Z.to_nat (h_used h)) (zbytes (stack_bytes (h_stack h))); CB (Z.to_nat (h_stack_size h - h_used h)) junk]) ->
  rw_cells rsegs m' (pCX E) (ctx_cells cx) ->
  (exists padw, yparse_frame m' (p_sp E) (p_ra E) (p_s0 E) (p_s1 E) (p_s2 E) (p_s3 E) (p_s4 E) (p_s5 E) (p_s6 E) (p_s7 E)
                              (p_s8 E) (p_s9 E) (p_s10 E) (p_s11 E) (reg_get (p_F E) 8%bv) padw obw olw) ->
  stk rsegs m' (p_lo E) (pSP E) ->
  pmem E m' mo s LK (h_set_stack h rest) mh cx obw olw.
Proof.
  intros until rest. intros OK PM HST MU WM MI' (pew & pad & HC' & PW) (junk & SC') CXC' FR' STK'.
  pose proof (pmem_ranges _ HKB _ _ _ _ _ _ _ _ _ _ OK PM) as (I1 & I2 & R1 & R2 & S12 & B1 & B2 & B3).
  pose proof PM as (RY & HR & SAME & CXR & _). destruct CXR as [_ CXB2].
  pose proof HR as ((_ & _ & _ & _ & BC4) & _ & _ & BSR). unfold RYajlRep.bs_rep in BSR.
  destruct (h_stack_blk h) as [sbk|] eqn:HSB; [| destruct PM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SB1 & _); congruence].
  destruct BSR as [SBNZ _].
  assert (USED : h_used h = zlength rest + 1) by (unfold h_used; rewrite HST; unfold zlength; cbn [length]; lia).
  assert (Z0 : 0 <= zlength rest) by (unfold zlength; clear; lia).
  assert (EU : h_used (h_set_stack h rest) = h_used h - 1) by (unfold h_used; cbn [h_stack h_set_stack]; rewrite HST; unfold zlength; cbn [length]; lia).
  eapply pmem_updA; [exact HKF| exact HKB| exact OK| exact PM| exact MU| exact WM| exact MI'| | reflexivity| reflexivity| reflexivity| reflexivity| | | split; [exact CXC'| exact CXB2]| exact FR'| exact STK'].
  - constructor; [| constructor]. unfold ownA. cbn [fst snd]. clear. lia.
  - split; [| cbn [h_set_stack h_bytesConsumed h_stack_size h_stack_blk h_parseError]; rewrite HSB, EU; repeat split; try (clear -B1 B2 B3 USED Z0; lia); intros; congruence].
    exists pew, pad. split; [exact HC'| exact PW].
  - unfold RYajlRep.bs_rep. cbn [h_stack_blk h_set_stack h_stack h_stack_size]. rewrite HSB, EU. split; [exact SBNZ|].
    destruct (u8arr_of_CB2 _ _ _ _ _ _ _ SC') as (ARR & L1 & L2).
    exists ([Z_to_bv 8 (state_code st)] ++ junk).
    apply (CB2_of_u8arr rsegs m' (mh_stack mh) (zbytes (stack_bytes rest)) ([Z_to_bv 8 (state_code st)] ++ junk)).
    + revert ARR. rewrite HST, stack_bytes_cons, zbytes_app. cbn [zbytes map]. rewrite <- app_assoc. intros ARR. exact ARR.
    + rewrite zbytes_length, stack_bytes_length. clear -Z0 USED. unfold zlength in *. lia.
    + rewrite length_app, L2. cbn [length]. clear -B3 USED Z0. lia.
Qed.

(* [comment removed for export] *)
Lemma J_pop24 : forall E m mo s LK h mh cx obw olw st rest
    (rav t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s5v s6v s8v : word),
  pok E -> pmem E m mo s LK h mh cx obw olw -> h_stack h = st :: rest ->
  yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) (p_h E) (p_cx E)) (SR_again (h_set_stack h rest) cx) ->
  again_cont E ->
  realizes_cfg acfg rsegs (mkCfg (pstate E 0x156b0 m rav t0 t1 t2 (wz (h_used h - 1)) a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s5v s6v s8v (wz 13)) mo) (p_K E).
Proof.
  intros until s8v. intros OK PM HST YL AG. open_env HKB OK PM.
  assert (USED : h_used h = zlength rest + 1) by (unfold h_used; rewrite HST; unfold zlength; cbn [length]; lia).
  assert (Z0 : 0 <= zlength rest) by (unfold zlength; clear; lia).
  destruct (yparse_step_again_facts (p_txt E) (pLEN E) (p_h E) (p_cx E) _ _ eq_refl ltac:(clear -L26; unfold pLEN in *; lia) LP YL) as (_ & U1 & _).
  assert (EU : h_used (h_set_stack h rest) = h_used h - 1) by (unfold h_used; cbn [h_stack h_set_stack]; rewrite HST; unfold zlength; cbn [length]; lia).
  rewrite EU in U1.
  clear ERR TXT LXR DBR. unfold pstate, pH, wz.
  pose proof (munch_refl [(mh_addr (p_mh E) + 60, mh_addr (p_mh E) + 64)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  rz_seg HKS HK0.
  zstep. zstep. if_cases K; zify_cond K. 2:{ exfalso. revert K U1 USED Z0 B2 B3. clear. intros. lia. }
  apply evt_done.
  pose proof (at_head HK E) as AH. unfold yparse_head_state, pH, RY_PARSE_HEAD in AH. rewrite <- EU. eapply AH; [exact OK| | exact YL| exact AG].
  rewrite <- EHA in MU.
  eapply pmem_pop; [exact OK| exact PM| exact HST| exact MU| exact WM| exact MI| | exists junk; exact SC| exact CXC| exists padw; exact FR| exact STK].
  exists pew, pad. split; [| exact PW]. unfold hand_cells, hand_head_cells, alloc_cells.
  cbn [yc_callbacks yc_malloc_w yc_realloc_w yc_free_w ryc app h_set_stack h_bytesConsumed h_stack_size h_parseError]. unfold wz. rewrite EU, EHA. exact HC.
Qed.

(* [comment removed for export] *)
Lemma J_pop1c : forall E m mo s LK h mh cx obw olw st rest
    (rav t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s5v s6v s8v : word),
  pok E -> pmem E m mo s LK h mh cx obw olw -> h_stack h = st :: rest ->
  yleaf (yparse_step jf_callbacks (p_txt E) (pLEN E) (p_h E) (p_cx E)) (SR_again (h_set_stack h rest) cx) ->
  again_cont E ->
  realizes_cfg acfg rsegs (mkCfg (pstate E 0x156a8 m rav t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s5v s6v s8v (wz 13)) mo) (p_K E).
Proof.
  intros until s8v. intros OK PM HST YL AG. open_env HKB OK PM.
  assert (USED : h_used h = zlength rest + 1) by (unfold h_used; rewrite HST; unfold zlength; cbn [length]; lia).
  assert (Z0 : 0 <= zlength rest) by (unfold zlength; clear; lia).
  clear ERR TXT LXR DBR. unfold pstate, pH, wz.
  rz_seg HKS HK0.
  zstep. rewrite ysx32_small by (clear -USED Z0 B2 B3; lia). zstep.
  apply evt_done.
  pose proof (J_pop24 E) as JP. unfold pstate, pH, wz in JP.
  rewrite (swrap32_small (h_used h + -1)) by (clear -USED Z0 B2 B3; lia).
  replace (h_used h + -1) with (h_used h - 1) by (clear; lia).
  eapply JP; [exact OK| exact PM| exact HST| exact YL| exact AG].
Qed.

End S2.
End RC__2.
