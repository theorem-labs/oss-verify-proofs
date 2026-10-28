(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith List Lia Bool Permutation Strings.String.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bu X1cf X1cc X1bs X1c2 X1bn X1bj X1bq X1c0.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0px X0qn X0qc X0qp X0pw X0qx X0qw X0pv X0pt.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1m2 X1m3 X1m5 X1fl X1ea X1nl X1m8 X1fr X1no X1np X1h7 X1kc X1ka X1kd X1k9 X1l0 X1l1 X1l4 X1l5.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require X1ff X1fd X1ei.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1ra X1qu X1qx X1ri X1oc X1o8 X1rm X1r3 X1r6.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Notation rsegs := X1gj.rsegs.
Ltac ua := change X1ff.rsegs with X1gj.rsegs in *; change U.X1fd.rsegs with X1gj.rsegs in *.
Ltac rpc := apply ret_pc_even; [lia| reflexivity].

Definition rdrv_ok (LB : list block) (SP : Z) (a : Z) : Prop := 0 <= a < 2^64 /\ rclient_addr LB SP a /\ ~ in_ivs rdrv_X a.
Lemma rdrv_agree : forall LB SP m m', rdrv_pres LB SP m m' -> agree_on rsegs (rdrv_ok LB SP) m m'.
Proof. intros LB SP m m' H a Ha (Hr & Hc & Hx). exact (H a Ha Hc Hx). Qed.

Lemma rdrv_ok_static : forall LB SP a,
0x3b000 <= a < 0x6e000 -> ~ ralloc_static a -> ~ (0x3d200 <= a < 0x3d2e8) -> ~ (0x6db20 <= a < 0x6df20) -> ~ (0x3d110 <= a < 0x3d1f8) -> ~ (RINITIALIZED <= a < RINITIALIZED + 1) ->
~ (RAEF_INCB <= a < RAEF_INCB + 1) -> ~ (RATEXIT <= a < RATEXIT + 40) -> ~ (RATEXIT_A0 <= a < RATEXIT_A0 + 8) ->
rdrv_ok LB SP a.
Proof.
intros LB SP a H1 H2 H4 H5 H6 H7 H8 H9 H10. split; [lia|]. split; [right; left; split; [exact H1| exact H2]|].
cbn. intros [X|[X|[X|[X|[X|[X|[X|X]]]]]]]; [apply H4; exact X| apply H5; exact X| apply H6; exact X| apply H7; exact X
| apply H8; exact X| apply H9; exact X| apply H10; exact X| exact X].
Qed.
Lemma rdrv_ok_stack : forall LB SP a, SP <= a < 2^64 -> 0x6e000 <= SP -> rdrv_ok LB SP a.
Proof.
intros LB SP a H1 H2. split; [lia|]. split; [left; lia|].
cbn. unfold RINITIALIZED, RAEF_INCB, RATEXIT, RATEXIT_A0. lia.
Qed.

Section D.
Context {RCEIL : RunCeiling}.
Variables (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (rnd : EntryDraw) (arg0 arg1 : list byte) (TID : Z) (S4 S5 S6 S7 S8 S9 S10 S11 : word).
Hypothesis VSP : valid_sp sp0.
Hypothesis HCEIL : alloc_ceiling = LO sp0.
Hypothesis VARGV : valid_argv argv.
Hypothesis VENVP : valid_envp envp.
Hypothesis EARGV : argv = [arg0; arg1].
Hypothesis HT : 0 < TID < 4194304.
Hypothesis RHF : rheap_frame_stmt.
Hypothesis RND : rheap_blocks_nodup_stmt.
Hypothesis RBD : rheap_blocks_disjoint_stmt.
Hypothesis RBR : rheap_block_range_stmt.
Hypothesis MALLOC : rmalloc_stmt.
Hypothesis FREE : rfree_stmt.
Hypothesis FKP : rfree_keeps_ptr_stmt.
Hypothesis FPR : @fprintf_diag_stmt PState.
Hypothesis FWX : fwritex_stderr_stmt.
Hypothesis SWF : stdio_write_flush_stmt.
Hypothesis FWR : @fwrite_diag_stmt PState.
Hypothesis TOW : towrite_stmt.
Hypothesis TRUN : rtarget_run_stmt.

Notation usp0 := (bv_unsigned sp0).
Notation gpv := (Z_to_bv 64 0x10800).
Notation tpv := (Z_to_bv 64 RATP).
Notation IMGB := (build_stack_bytes rph sp0 argv envp uid hw rnd).
Notation LO' := (LO sp0).
Notation BASE' := (BASE sp0 argv envp uid hw rnd TID).
Notation FRAME' mm := (exists pad, MFRAME sp0 argv mm pad S7 S6 S5 S4).
Notation RUN0' := (RUN0 sp0 argv envp uid hw rnd TID S4 S5 S6 S7 S8 S9 S10 S11).

Notation GST pc x1 t0 t1 t2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 F fc mm :=
(MS (mkR x1 (Z_to_bv 64 (usp0 + -128)) gpv tpv t0 t1 t2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 S8 S9 S10 S11 t3 t4 t5 t6)
F (Z_to_bv 64 pc) fc None mm (seg_rom rsegs)).

Definition BASE2 (mm : mem) : Prop :=
stk rsegs mm LO' (usp0 + -128) /\ mem_inv rsegs mm /\ RSTAT TID true mm /\ rauxv_ok mm usp0 /\ stderr_wfile mm.

#[using="VSP HCEIL HT RBR FREE"] Lemma free_return : forall (code : Z) (s : PState) (bufp : bptr) (A cap : Z)
x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (mm : mem) (errv : word),
RHEAP s [(bufp, A, cap)] mm -> FRAME' mm -> BASE2 mm -> stdout_file mm (ps_so s) -> rw_cells rsegs mm RERRNO [C4 errv] ->
implM rsegs (raw_free bufp ;;; mret code) s RQEXIT
(GST 0x1be7c x1 t0 t1 t2 (Z_to_bv 64 code) (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 F fc mm).
Proof.
intros until errv. intros P0 FR sfH_; first [ sf_destruct 5%nat sfH_ as ST MI RS AUX SE | sf_fb; destruct sfH_ as (ST & MI & RS & AUX & SE) ]; intros SOF ERR.
pose proof (sp_facts sp0 VSP HCEIL) as SF. unfold LO in SF. unfold LO in ST. unfold RERRNO in ERR. destruct FR as [pad FR]. unfold MFRAME in FR.
pose proof (RBR _ _ _ (bufp, A, cap) P0 ltac:(left; reflexivity)) as BR. cbn [blk_addr blk_size fst snd] in BR.
pose proof BR as sfP_; first [ sf_destruct 5%nat sfP_ as BR1 BR2 BR3 BR4 BR5 | sf_fb; destruct sfP_ as (BR1 & BR2 & BR3 & BR4 & BR5) ].
unfold implM. iprefix. zstep. zstep. apply evt_done.
lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM rsegs tm s RQEXIT msx) end.
eapply implM_bind.
{ unfold rfree_stmt in FREE.
eapply FREE with (lo := usp0 - 8388608) (B := usp0) (p := bufp) (A := A) (n := cap); try reflexivity; unfold RATP;
rewrite ?(unsigned_lit 316496) by lia; rewrite ?(unsigned_lit (usp0 + -128)) by lia;
first [ exact P0 | left; reflexivity | exact AUX | exact ST | exact MI | exact ERR | unfold RFREE_STACK; lia | lia ]. }
cbv beta. intros [] s2 ms2 PO.
first [ sf_destruct 25%nat PO as w0 w1 w2 rb0 d1 d2 d3 d4 d5 d6 d7 w3 w4 w5 w6 m3 -> MI3 ST3 ERR3 AUX3 HPR3 FAE3 SOE3 HEAP3 | sf_fb; destruct PO as (w0 & w1 & w2 & rb0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m3 & -> & MI3 & ST3 & ERR3 & AUX3 & HPR3 & FAE3 & SOE3 & HEAP3) ].
rewrite ?(unsigned_lit (usp0 + -128)) in ST3 by lia. rewrite ?(unsigned_lit (usp0 + -128)) in HPR3 by lia.
replace (ret_pc (Z_to_bv 64 0x1be84)) with (Z_to_bv 64 0x1be84) by (symmetry; rpc).
cbn [lb_remove filter bptr_eqb fst snd] in HEAP3, HPR3.
apply implM_ret. change (RQEXIT code s2) with (rat_exit code s2).
eapply (main_return sp0 argv TID VSP HCEIL HT code s2).
- unfold MFRAME. eapply rheap_pres_rw_cells; [exact HPR3| exact FR| left; cbn; lia].
- unfold LO. first [exact ST3| replace (usp0 - 8388608) with (usp0 + -8388608) by lia; exact ST3].
- eapply RSTAT_heap_pres; [exact HPR3| exact RS].
- rewrite bptr_eqb_refl in HEAP3 || idtac. exact HEAP3.
- rewrite SOE3. eapply stdout_file_heap_pres; [exact HPR3| exact SOF].
- apply stderr_wfile_file. eapply stderr_wfile_heap_pres; [exact HPR3| exact SE].
- exact MI3.
Qed.

#[using="VSP HCEIL HT RBR FREE TRUN"] Lemma phaseDE : forall bufp A cap DATA cw L cfg sc s ms,
RUN0' bufp A cap DATA cw L cfg sc s ms ->
implM rsegs (main_tail bufp cw cfg (skipn (Z.to_nat (6 + L)) (map bv_unsigned DATA))) s RQEXIT ms.
Proof.
intros bufp A cap DATA cw L cfg sc s ms R0.
first [ sf_destruct 33%nat R0 as x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 x23 F fc mm junk errv -> HD PST0 ADP SO0 BLK FR BA ERR FRM MKF | sf_fb; destruct R0 as (x1 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & x23 & F & fc & mm & junk & errv & -> & HD & PST0 & ADP & SO0 & BLK & FR & BA & ERR & FRM & MKF) ].
pose proof (sp_facts sp0 VSP HCEIL) as SF. unfold LO in SF.
pose proof BA as sfP_; first [ sf_destruct 7%nat sfP_ as ST MI RS AUX IMG SE SOF | sf_fb; destruct sfP_ as (ST & MI & RS & AUX & IMG & SE & SOF) ]. unfold LO in ST. pose proof ERR as ERR0. unfold RERRNO in ERR. destruct FR as [pad FR]. unfold MFRAME in FR.
first [ sf_destruct 13%nat HD as LEN6 LENC CAPM BR CW EL LR LCW ECW ECFG CFGR SCR TB | sf_fb; destruct HD as (LEN6 & LENC & CAPM & BR & CW & EL & LR & LCW & ECW & ECFG & CFGR & SCR & TB) ]. unfold MAX_INPUT in CAPM.
pose proof BR as sfP_; first [ sf_destruct 5%nat sfP_ as BR1 BR2 BR3 BR4 BR5 | sf_fb; destruct sfP_ as (BR1 & BR2 & BR3 & BR4 & BR5) ].
pose proof BLK as BLKB. apply (proj1 (rw_cells_app _ _ _ [CB (length DATA) DATA] _)) in BLKB. destruct BLKB as [BLKB _].
apply rw_cells_bytes_at in BLKB. cbn [cells_bytes cbytes app] in BLKB. rewrite app_nil_r in BLKB.
unfold main_tail. rewrite ECFG.
unfold implM. iprefix. zstep. zstep. zstep. zstep. zstep. apply evt_done.
lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM rsegs tm s RQEXIT msx) end.
eapply implM_bind.
{ eapply TRUN with (lo := usp0 - 8388608) (AB := usp0) (p := bufp) (cap := cap);
rewrite ?(unsigned_lit (usp0 + -128)) by lia.
- exact PST0.
- left; reflexivity.
- unfold zbytes. rewrite zbytes_map_unsigned'. exact BLKB.
- apply map_unsigned_range.
- unfold zlength. rewrite length_map. lia.
- lia.
- lia.
- unfold zlength. rewrite length_map. lia.
- exact AUX.
- lia.
- lia.
- exact ST.
- lia.
- unfold RTARGET_RUN_STACK, RFUZZ_STACK. lia.
- unfold RATP. rewrite (unsigned_lit 316496) by lia. exact ERR.
- exact MI.
- exact FRM.
- rewrite SO0. exact SOF.
- apply stderr_wfile0_wfile. exact SE.
- exact (proj1 ADP).
- exact (proj2 ADP).
- exact (RSTAT_ax TID _ RS).
- reflexivity.
- clear -SF. Z.div_mod_to_equations. lia.
- reflexivity.
- reflexivity.
- reflexivity.
- unfold zlength. rewrite length_map. reflexivity. }
cbv beta. intros r s1 ms1 PO.
first [ sf_destruct 30%nat PO as u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F1 fc1 m1 errv1 -> RR FRM1 MI1 ST1 ERR1 AUX1 DP P1 SOF1 SEW1 AXT | sf_fb; destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F1 & fc1 & m1 & errv1 & -> & RR & FRM1 & MI1 & ST1 & ERR1 & AUX1 & DP & P1 & SOF1 & SEW1 & AXT) ].
ua. rewrite ?(unsigned_lit (usp0 + -128)) in ST1 by lia. rewrite ?(unsigned_lit (usp0 + -128)) in DP by lia.
unfold RATP in ERR1. rewrite ?(unsigned_lit 316496) in ERR1 by lia.
replace (ret_pc (Z_to_bv 64 0x1bdfc)) with (Z_to_bv 64 0x1bdfc) by (symmetry; rpc).
pose proof (rdrv_agree _ _ _ _ DP) as AG.
apply (rw_cells_agree rsegs _ _ _ _ _ AG) in FR; [| intros a Ha; apply rdrv_ok_stack; cbn in Ha; unfold sp_window_hi in *; lia].
assert (RS1 : RSTAT TID true m1).
{ eapply (RSTAT_reax TID _ _ _ AG); [| exact RS| exact AXT]. intros a Ha. apply rdrv_ok_static;
unfold rstat0_addr, ralloc_static, RINITIALIZED, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP, RAEF_INCB, RATEXIT, RATEXIT_A0 in *; lia. }
assert (BA2 : BASE2 m1) by (split; [exact ST1| split; [exact MI1| split; [exact RS1| split; [exact AUX1| exact SEW1]]]]).
clear AG DP.
rewrite TB.
destruct (Z.lt_ge_cases sc 0) as [SNEG|SPOS].
-
replace (sc <? 0) with true by (symmetry; apply Z.ltb_lt; lia).
replace (Z_to_bv 64 sc) with (Z_to_bv 64 (sc + 2^64)) by (apply Z_to_bv_eqm; rewrite <- (Z.mod_add sc 1) by lia; f_equal; lia).
unfold implM. iprefix. zstep. if_cases K; zify_cond K; [| exfalso; lia].
zstep. zstep. zstep.
replace (ret_pc (Z_to_bv 64 0x1be0c)) with (Z_to_bv 64 0x1be0c) by (symmetry; rpc).
apply evt_done.
lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM rsegs tm s1 RQEXIT msx) end.
apply implM_bind_assoc. unfold target_alloc_count. apply implM_mret_bind. cbv beta. apply implM_retb.
unfold COUNT_MAX. cbn [Z.ltb].
unfold implM. iprefix. zstep. zstep. zstep. if_cases K2; zify_cond K2; [| exfalso; rewrite ?unsigned_lit in K2 by lia; lia].
apply evt_done. lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM rsegs tm s1 RQEXIT msx) end.
eapply free_return; [exact P1| exists pad; exact FR| exact BA2| exact SOF1| unfold RERRNO; exact ERR1].
-
replace (sc <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
apply implM_retb.
unfold implM. iprefix. zstep. if_cases K; zify_cond K; [exfalso; lia|].
zstep. zstep.
apply evt_done. lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM rsegs tm s1 RQEXIT msx) end.
eapply free_return; [exact P1| exists pad; exact FR| exact BA2| exact SOF1| unfold RERRNO; exact ERR1].
Qed.
End D.
