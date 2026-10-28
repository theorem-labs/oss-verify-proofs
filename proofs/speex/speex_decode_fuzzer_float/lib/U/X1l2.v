(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith List Lia Bool Permutation Strings.String.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bu X1cf X1cc X1bs X1c2 X1bn X1bj X1bq.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0px X0qn X0qc X0qp X0pw X0qx X0qw X0pv X0pt.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1m2 X1m3 X1m5 X1fl X1ea X1nl X1m8 X1fr X1no X1np X1h7 X1ka X1kd X1k9 X1l0 X1l1.
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

Ltac at_pc p := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?q) _ _ _ _) => constr_eq q p end.
Ltac zsteps_to p := repeat (tryif at_pc p then fail else zstep).

Lemma rw_cells_CB0 : forall m A, 0 <= A <= 2^64 -> rw_cells rsegs m A [CB 0%nat []].
Proof.
intros m A H. split; [split|].
- cbn. split; [reflexivity| exact I].
- cbn [cells_bytes cbytes app]. apply bytes_at_nil. exact H.
- cbn [cells_size csize Nat.add]. split; [lia|]. split; [lia|]. intros i Hi. lia.
Qed.

Section B2.
Context {RCEIL : RunCeiling}.
Variables (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (rnd : EntryDraw) (arg0 arg1 : list byte) (TID : Z) (S4 S5 S6 S7 S8 S9 S10 S11 : word).
Hypothesis VSP : valid_sp sp0.
Hypothesis HCEIL : alloc_ceiling = LO sp0.
Hypothesis VARGV : valid_argv argv.
Hypothesis VENVP : valid_envp envp.
Hypothesis EARGV : argv = [arg0; arg1].
Hypothesis HT : 0 < TID < 4194304.
Hypothesis RHF : rheap_frame_stmt.
Hypothesis MALLOC : rmalloc_stmt.
Hypothesis FREE : rfree_stmt.
Hypothesis FKP : rfree_keeps_ptr_stmt.
Hypothesis FPR : @fprintf_diag_stmt PState.
Hypothesis FWX : fwritex_stderr_stmt.
Hypothesis SWF : stdio_write_flush_stmt.
Hypothesis FWR : @fwrite_diag_stmt PState.
Hypothesis TOW : towrite_stmt.

Notation usp0 := (bv_unsigned sp0).
Notation gpv := (Z_to_bv 64 0x10800).
Notation tpv := (Z_to_bv 64 RATP).
Notation IMGB := (build_stack_bytes rph sp0 argv envp uid hw rnd).
Notation LO' := (LO sp0).
Notation BASE' := (BASE sp0 argv envp uid hw rnd TID).
Notation FRAME' mm := (exists pad, MFRAME sp0 argv mm pad S7 S6 S5 S4).
Notation RDINV' := (RDINV sp0 argv envp uid hw rnd TID S4 S5 S6 S7 S8 S9 S10 S11).
Notation RDBRK' := (RDBRK sp0 argv envp uid hw rnd TID S4 S5 S6 S7 S8 S9 S10 S11).
Notation POSTBODY' := (POSTBODY sp0 argv envp uid hw rnd TID S4 S5 S6 S7 S8 S9 S10 S11).
Ltac hyps := first [exact VSP | exact HCEIL | exact VARGV | exact VENVP | exact EARGV | exact HT | exact RHF | exact MALLOC | exact FREE | exact FKP | exact FPR | exact FWX | exact SWF | exact FWR | exact TOW].

Notation GST pc x1 t0 t1 t2 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 F fc mm :=
(MS (mkR x1 (Z_to_bv 64 (usp0 + -128)) gpv tpv t0 t1 t2 (Z_to_bv 64 2) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 S8 S9 S10 S11 t3 t4 t5 t6)
F (Z_to_bv 64 pc) fc None mm (seg_rom rsegs)).
Notation RST pc x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 P1v len fd cap x23 t3 t4 t5 t6 F fc mm :=
(GST pc x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 P1v) (Z_to_bv 64 len) (Z_to_bv 64 fd) (Z_to_bv 64 cap) (Z_to_bv 64 RSTG) x23 t3 t4 t5 t6 F fc mm).

Definition RDCNT (cap LEN : Z) : Z := if READ_CAP <? cap - LEN then READ_CAP else cap - LEN.

#[using="RCEIL"] Lemma RDCNT_range : forall cap LEN, 0 <= LEN < cap -> 1 <= RDCNT cap LEN <= cap - LEN /\ RDCNT cap LEN <= READ_CAP.
Proof. intros cap LEN H. unfold RDCNT, READ_CAP. destruct (Z.ltb_spec0 65536 (cap - LEN)); lia. Qed.

#[using="RCEIL VSP HCEIL"] Lemma rd_want : forall (Q : machine_state -> Prop) x1 t0 t1 t2 (x9 : word) a0 a1 a2 a3 a4 a5 a6 a7 (P1v LEN fd cap : Z) (x23 : word) t3 t4 t5 t6
(F : bvmap 5 word) (fc : bv 32) (mm : mem),
0 <= LEN < cap -> cap <= 67108864 -> 0 <= fd < 2^32 ->
evt rsegs Q (GST 0x3a6b4 (Z_to_bv 64 0x1bd70) t0 t1 t2 x9 (Z_to_bv 64 fd) (Z_to_bv 64 RSTG) (Z_to_bv 64 (RDCNT cap LEN)) a3 a4 a5 a6 a7
(Z_to_bv 64 P1v) (Z_to_bv 64 LEN) (Z_to_bv 64 fd) (Z_to_bv 64 cap) (Z_to_bv 64 RSTG) x23 t3 t4 t5 t6 F fc mm) ->
evt rsegs Q (GST 0x1bd54 x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 P1v) (Z_to_bv 64 LEN) (Z_to_bv 64 fd) (Z_to_bv 64 cap) (Z_to_bv 64 RSTG) x23 t3 t4 t5 t6 F fc mm).
Proof.
intros until mm. intros HL HC HFD K. pose proof (sp_facts sp0 VSP HCEIL) as SF. unfold LO in SF.
zstep. zstep. zstep. if_cases K0; zify_cond K0.
all: zsteps_to 0x3a6b4%Z.
all: first
[ replace (RDCNT cap LEN) with 65536 in K by (unfold RDCNT, READ_CAP; destruct (Z.ltb_spec0 65536 (cap - LEN)); lia);
exact K
| replace (RDCNT cap LEN) with (cap - LEN) in K by (unfold RDCNT, READ_CAP; destruct (Z.ltb_spec0 65536 (cap - LEN)); lia);
first [exact K | replace (cap + - LEN) with (cap - LEN) by lia; exact K] ].
Qed.

#[using="arg0 VSP HCEIL VARGV VENVP EARGV HT RHF FPR FWX SWF"] Lemma rd_read : forall (fd P1v : Z) (st1 : rd_st) (s : PState) x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (x23 : word) t3 t4 t5 t6
(F : bvmap 5 word) (fc : bv 32) (mm : mem) (A : Z) (DATA junk stg : list byte) (errv : word),
3 <= fd < 2^32 -> nth_error (argv_ptrs sp0 argv envp) 1 = Some (Z_to_bv 64 P1v) ->
rd_content st1 = map bv_unsigned DATA -> BUF mm s (rd_buf st1) A (rd_cap st1) DATA junk -> Z.of_nat (length DATA) < rd_cap st1 ->
FRAME' mm -> BASE' mm -> ADP0 mm -> rw_cells rsegs mm RERRNO [C4 errv] -> frm0 fc -> is_mkF F ->
rw_cells rsegs mm RSTG [CB (Z.to_nat 65536) stg] ->
implM rsegs (rd_read_part fd (map bv_unsigned arg1) st1) s (POSTBODY' fd P1v)
(GST 0x1bd54 x1 t0 t1 t2 (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 P1v) (Z_to_bv 64 (zlength (rd_content st1))) (Z_to_bv 64 fd) (Z_to_bv 64 (rd_cap st1)) (Z_to_bv 64 RSTG) x23 t3 t4 t5 t6 F fc mm).
Proof.
intros until errv. intros FD HP1 HC BU LT FR BA CJ ERR FRM MKF SG.
pose proof (sp_facts sp0 VSP HCEIL) as SF. unfold LO in SF.
first [ sf_destruct 8%nat BU as P0 FA0 SO0 HA BLK [CAPR CAPK] LENR BR | sf_fb; destruct BU as (P0 & FA0 & SO0 & HA & BLK & [CAPR CAPK] & LENR & BR) ]. pose proof BR as sfP_; first [ sf_destruct 5%nat sfP_ as BR1 BR2 BR3 BR4 BR5 | sf_fb; destruct sfP_ as (BR1 & BR2 & BR3 & BR4 & BR5) ].
pose proof BA as sfP_; first [ sf_destruct 7%nat sfP_ as ST MI RS AUX IMG SE SOF | sf_fb; destruct sfP_ as (ST & MI & RS & AUX & IMG & SE & SOF) ]. unfold LO in ST.
assert (LENZ : zlength (rd_content st1) = Z.of_nat (length DATA)) by (rewrite HC; unfold zlength; rewrite length_map; reflexivity).
rewrite LENZ. unfold MAX_INPUT in CAPR.
unfold rd_read_part. cbv beta zeta. rewrite LENZ, RSTG_eq.
change (if READ_CAP <? rd_cap st1 - Z.of_nat (length DATA) then READ_CAP else rd_cap st1 - Z.of_nat (length DATA))
with (RDCNT (rd_cap st1) (Z.of_nat (length DATA))).
destruct FR as [pad FR]. unfold MFRAME in FR. unfold RERRNO in ERR.
unfold implM. iprefix.
eapply rd_want; [lia| lia| lia|].
pose proof (RDCNT_range (rd_cap st1) (Z.of_nat (length DATA)) ltac:(lia)) as [CR1 CR2]. unfold READ_CAP in CR2.
apply evt_done.
lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM rsegs tm s (POSTBODY' fd P1v) msx) end.
set (LEN := Z.of_nat (length DATA)) in *. set (CNT := RDCNT (rd_cap st1) LEN) in *.
assert (ELEN : LEN = Z.of_nat (length DATA)) by reflexivity. assert (ECNT : CNT = RDCNT (rd_cap st1) LEN) by reflexivity. clearbody LEN CNT. assert (LEN0 : 0 <= LEN) by lia.

assert (SGL : length stg = Z.to_nat 65536) by (destruct SG as [[Hwf _] _]; cbn in Hwf; lia).
pose proof (rw_cells_CB_split _ _ _ (Z.to_nat CNT) _ SG ltac:(lia)) as SGS.
apply (proj1 (rw_cells_app _ _ _ [CB (Z.to_nat CNT) (firstn (Z.to_nat CNT) stg)] _)) in SGS. destruct SGS as [SGc SGr].
cbn [cells_size csize Nat.add] in SGr. rewrite Nat.add_0_r in SGr.
eapply implM_bind.
{ set (w1 := Z_to_bv 64 RSTG). replace RSTG with (bv_unsigned w1) at 1 2 by (subst w1; rewrite unsigned_lit; unfold RSTG; lia).
eapply implM_of_enode.
eapply read_spec with (lo := usp0 - 8388608) (junk := firstn (Z.to_nat CNT) stg) (errv := errv); subst w1; unfold RATP;
rewrite ?(unsigned_lit 316496) by lia; rewrite ?(unsigned_lit (usp0 + -128)) by lia; rewrite ?(unsigned_lit RSTG) by (unfold RSTG; lia); try reflexivity;
first [exact ST | exact SGc | exact ERR | exact MI | unfold RSTG, TASK_SIZE; lia]. }
cbv beta. intros a s' ms' [PO ->].
first [ sf_destruct 21%nat PO as u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 m2 -> MUc WMc MI2 ST2 RES | sf_fb; destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & -> & MUc & WMc & MI2 & ST2 & RES) ].
unfold RATP in MUc, RES. rewrite !unsigned_lit in MUc by (unfold RSTG; lia). rewrite ?unsigned_lit in ST2 by lia. rewrite ?unsigned_lit in RES by (unfold RSTG; lia).
change (316496 + -164) with 316332 in MUc, RES. unfold RSTG in MUc, SGr, RES, BR5.
transport_after_call rsegs mm m2 MUc WMc.
replace (ret_pc (Z_to_bv 64 0x1bd70)) with (Z_to_bv 64 0x1bd70) by (symmetry; rpc).
rename ST2 into ST2'.
assert (WOKW : Forall (WOK sp0) [(usp0 + -128 - 16, usp0 + -128); (0x3d349, 0x3d349 + Z.of_nat (Z.to_nat CNT)); (316332, 316332 + 4)]).
{ unfold WOK, LO, RERRNO, RSTG. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia. }
assert (P2 : RHEAP s [(rd_buf st1, A, rd_cap st1)] m2).
{ eapply (RHEAP_munchW sp0 VSP HCEIL RHF); [exact WOKW| exact MUc| exact WMc| | exact P0].
intros iv [<-|[<-|[<-|[]]]]; cbn [fst snd]; intros Hiv Hiv2; lia. }
assert (BA2 : BASE' m2) by (eapply (BASE_munch sp0 argv envp uid hw rnd TID VSP HCEIL VARGV VENVP); [exact BA| exact WOKW| exact MUc| exact WMc| exact MI2| unfold LO; first [exact ST2' | replace (usp0 - 8388608) with (usp0 + -8388608) by lia; exact ST2']]).
assert (CJ2 : ADP0 m2) by (eapply (ADP0_munchW sp0 VSP HCEIL); [exact WOKW| exact MUc| exact WMc| exact CJ]).
clear MUc WMc BA WOKW.
destruct a as [e|bs]; cbn [read_ret] in *.
-
destruct RES as (SGc' & ERR2 & He).
pose proof BA2 as sfP_; first [ sf_destruct 7%nat sfP_ as ST3 MI3 RS3 AUX3 IMG3 SE3 SOF3 | sf_fb; destruct sfP_ as (ST3 & MI3 & RS3 & AUX3 & IMG3 & SE3 & SOF3) ]. pose proof RS3 as sfP_; first [ sf_destruct 14%nat sfP_ as _ _ _ _ _ _ _ _ _ _ G28 GD0 _ _ | sf_fb; destruct sfP_ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G28 & GD0 & _ & _) ].
pose proof VARGV as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ ARGLEN NONUL _ | sf_fb; destruct sfP_ as (_ & _ & ARGLEN & NONUL & _) ].
first [ pose proof (argv_cstring sp0 argv envp uid hw rnd m2 IMG3 1 arg1 ltac:(rewrite EARGV; reflexivity) ltac:(clear -SF; Z.div_mod_to_equations; lia)) as sfP_; sf_destruct 7%nat sfP_ as p1 slack1 HP1' P1LO P1HI STR1 SLK1 | sf_fb; destruct (argv_cstring sp0 argv envp uid hw rnd m2 IMG3 1 arg1 ltac:(rewrite EARGV; reflexivity) ltac:(clear -SF; Z.div_mod_to_equations; lia)) as (p1 & slack1 & HP1' & P1LO & P1HI & STR1 & SLK1) ]. unfold str_base, struct_size, argc, envc in P1LO.
pose proof (IMGB_len sp0 argv envp uid hw rnd VSP VARGV VENVP) as IL.
rewrite HP1 in HP1'. assert (EP : Z_to_bv 64 P1v = Z_to_bv 64 p1) by congruence. rewrite EP. clear HP1' EP.
assert (A1NN : ~ In (Z_to_bv 8 0) arg1) by (rewrite EARGV in NONUL; inversion NONUL as [|? ? ? X]; inversion X; assumption).
assert (A1LEN : Z.of_nat (length arg1) <= 131071) by (rewrite EARGV in ARGLEN; inversion ARGLEN as [|? ? ? X]; inversion X; assumption).
unfold implM. iprefix.
replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 18446744073709551615) by (apply Z_to_bv_eqm; reflexivity).
zstep. if_cases K0; zify_cond K0; try (exfalso; revert K0; clear; intros K0; rewrite ?unsigned_lit in K0 by lia; lia). clear K0.
zstep. zstep. zstep. zstep. zstep. zstep. zstep. apply evt_done.
lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM rsegs tm s (POSTBODY' fd P1v) msx) end.
cbn [io_diag].
eapply (fprintf_exit sp0 argv envp uid hw rnd TID S8 S9 S10 S11 VSP HCEIL HT RHF FPR FWX SWF (DReadError (map bv_unsigned arg1)));
[| exact BA2| exact P2| exact SO0| exact FRM| intros ms'' AE; apply implM_ret; apply evt_done; exact AE].
cbn [diag_args]. split; [reflexivity|]. exists slack1. rewrite unsigned_lit by lia.
unfold X1ei.zb. rewrite zbytes_map_unsigned'. unfold zlength. rewrite !length_map.
split; [exact STR1|]. split; [apply map_unsigned_pos; exact A1NN|]. split; [lia|].
split; [unfold X1oc.INT_MAX; lia|]. split; [right; lia| unfold GLOBALS_TOP; lia].
- destruct RES as (SGc' & ERR2 & Hbs).
pose proof (bytes_at_bound _ _ _ _ (proj2 (proj1 SGc'))) as BB. cbn [cells_bytes cbytes app] in BB. rewrite !length_app, length_skipn, length_firstn in BB.
unfold implM. iprefix.
zstep. if_cases K0; zify_cond K0; try (exfalso; revert K0 Hbs CAPR LEN0 ECNT LENR CR1 CR2; clear; intros; rewrite ?unsigned_lit in K0 by lia; lia). clear K0.
zstep. zstep. if_cases K1; zify_cond K1.
+
set (n := length bs) in *.

pose proof BLK as BLK0. apply (proj1 (rw_cells_app _ _ _ [CB (length DATA) DATA] _)) in BLK0. destruct BLK0 as [BLK1 BLK2].
cbn [cells_size csize Nat.add] in BLK2. rewrite Nat.add_0_r, <- ELEN in BLK2.
assert (JL : length junk = Z.to_nat (rd_cap st1 - LEN)) by (destruct BLK2 as [[Hwf _] _]; cbn in Hwf; lia).
pose proof (rw_cells_CB_split _ _ _ n _ BLK2 ltac:(lia)) as BLKS.
apply (proj1 (rw_cells_app _ _ _ [CB n (firstn n junk)] _)) in BLKS. destruct BLKS as [BLKd BLKr].
cbn [cells_size csize Nat.add] in BLKr. rewrite Nat.add_0_r in BLKr. clear BLK BLK2.
pose proof SGc' as SGd. apply (proj1 (rw_cells_app _ _ _ [CB n bs] _)) in SGd. destruct SGd as [SGd SGm]. cbn [cells_size csize Nat.add] in SGm. rewrite Nat.add_0_r in SGm.
pose proof (rw_cells_bytes_at _ _ _ _ SGd) as SRCB. cbn [cells_bytes cbytes app] in SRCB. rewrite app_nil_r in SRCB.
zstep. zstep. zstep. zstep. change (Z_to_bv 64 RSTG) with (Z_to_bv 64 0x3d349).
eapply evt_cut.
{ eapply memcpy_callv with (src := bs) (junk := firstn n junk);
[exact SRCB| subst n; lia| lia| lia| lia| replace (Z.to_nat (Z.of_nat n)) with n by lia; first [exact BLKd | replace (A + LEN) with (LEN + A) by lia; exact BLKd] | lia| exact MI2]. }
cbv beta. intros ms' PO.
first [ sf_destruct 21%nat PO as v0 v1 v2 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 m3 -> MUc WMc MI3 BLKd' _ | sf_fb; destruct PO as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m3 & -> & MUc & WMc & MI3 & BLKd' & _) ].
ua. transport_after_call rsegs m2 m3 MUc WMc.
replace (ret_pc (Z_to_bv 64 0x1bd08)) with (Z_to_bv 64 0x1bd08) by (symmetry; rpc).
assert (WOKW : Forall (WOK sp0) [(A + LEN, A + LEN + Z.of_nat n)]).
{ unfold WOK. constructor; [cbn [fst snd]; lia| constructor]. }
assert (P3 : RHEAP s [(rd_buf st1, A, rd_cap st1)] m3).
{ eapply (RHEAP_munchW sp0 VSP HCEIL RHF); [exact WOKW| exact MUc| exact WMc| | exact P2].
intros iv [<-|[]]. cbn [fst snd]. intros _ _. exists (rd_buf st1, A, rd_cap st1). split; [left; reflexivity|]. cbn [fst snd blk_addr blk_size]. lia. }
assert (BA3 : BASE' m3) by (eapply (BASE_munch sp0 argv envp uid hw rnd TID VSP HCEIL VARGV VENVP); [exact BA2| exact WOKW| exact MUc| exact WMc| exact MI3| unfold LO; first [exact ST2'| replace (usp0 - 8388608) with (usp0 + -8388608) by lia; exact ST2']]).
assert (CJ3 : ADP0 m3) by (eapply (ADP0_munchW sp0 VSP HCEIL); [exact WOKW| exact MUc| exact WMc| exact CJ2]).
clear MUc WMc BA2 CJ2 P2 WOKW.

assert (LEN' : zlength (rd_content st1 ++ u8s_of_bytes bs) = LEN + Z.of_nat n).
{ unfold zlength, u8s_of_bytes. rewrite length_app, length_map. unfold zlength in LENZ. lia. }
replace (Z.to_nat (Z.of_nat n)) with n in BLKd' by lia.
pose proof (rw_cells_CB_join _ _ _ _ _ _ BLK1 ltac:(replace (A + Z.of_nat (length DATA)) with (A + LEN) by lia; exact BLKd')) as BLK1'.
assert (BLK' : rw_cells rsegs m3 A [CB (length (DATA ++ bs)) (DATA ++ bs); CB (Z.to_nat (rd_cap st1 - Z.of_nat (length (DATA ++ bs)))) (skipn n junk)]).
{ apply (proj2 (rw_cells_app _ _ _ [CB (length (DATA ++ bs)) (DATA ++ bs)] _)). rewrite length_app. split; [subst n; exact BLK1'|]. cbn [cells_size csize Nat.add].
replace (A + Z.of_nat (length DATA + n + 0)) with (A + LEN + Z.of_nat n) by lia.
replace (Z.to_nat (rd_cap st1 - Z.of_nat (length DATA + n))) with (Z.to_nat (rd_cap st1 - LEN) - n)%nat by lia. exact BLKr. }
pose proof (rw_cells_CB_join _ _ _ _ _ _ SGd SGm) as SG1.
pose proof (rw_cells_CB_join _ _ _ _ _ _ SG1 ltac:(replace (0x3d349 + Z.of_nat (n + (Z.to_nat CNT - n))) with (0x3d349 + Z.of_nat (Z.to_nat CNT)) by lia; exact SGr)) as SGX.
clear SG1 SGd SGm SGr SGc' SRCB.
zstep. zstep. zstep. if_cases K2; zify_cond K2.
*
apply evt_done.
lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM rsegs tm s (POSTBODY' fd P1v) msx) end.
replace (n =? 0)%nat with false by (symmetry; apply Nat.eqb_neq; lia).
apply implM_ret. apply evt_done. cbn [POSTBODY]. unfold RDINV. cbn [rd_content rd_cap rd_buf]. rewrite LEN'.
exists 0x1bd1c. sf_eexists 17%nat. first [ unshelve sf_eexists 7%nat; [ exact (F) | exact (fc) | exact (m3) | exact (A) | exact ((DATA ++ bs)) | exact ((skipn n junk)) | exact (errv) | ] | sf_fb; exists F, fc, m3, A, (DATA ++ bs), (skipn n junk), errv ].
split; [replace (Z.of_nat n + LEN) with (LEN + Z.of_nat n) by lia; reflexivity|].
split; [right; split; [reflexivity| lia]|].
split; [rewrite HC; unfold u8s_of_bytes; rewrite map_app; reflexivity|].
split. { split; [exact P3|]. split; [exact FA0|]. split; [exact SO0|]. split; [exact HA|]. split; [exact BLK'|].
unfold MAX_INPUT. split; [split; [lia| exact CAPK]|]. split; [rewrite length_app; lia| exact BR]. }
split; [exists pad; exact FR|]. split; [exact BA3|]. split; [exact CJ3|]. split; [exact ERR2|]. split; [exact FRM|]. split; [exact MKF|].
eexists. match type of SGX with rw_cells _ _ _ [CB ?k _] => replace (Z.to_nat 65536) with k by lia end. exact SGX.
*
apply evt_done.
lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM rsegs tm s (POSTBODY' fd P1v) msx) end.
replace (n =? 0)%nat with false by (symmetry; apply Nat.eqb_neq; lia).
apply implM_ret. apply evt_done. cbn [POSTBODY]. unfold RDINV. cbn [rd_content rd_cap rd_buf]. rewrite LEN'.
exists 0x1bd14. sf_eexists 17%nat. first [ unshelve sf_eexists 7%nat; [ exact (F) | exact (fc) | exact (m3) | exact (A) | exact ((DATA ++ bs)) | exact ((skipn n junk)) | exact (errv) | ] | sf_fb; exists F, fc, m3, A, (DATA ++ bs), (skipn n junk), errv ].
split; [replace (Z.of_nat n + LEN) with (LEN + Z.of_nat n) by lia; reflexivity|].
split; [left; split; [reflexivity| rewrite ?unsigned_lit in K2 by lia; lia]|].
split; [rewrite HC; unfold u8s_of_bytes; rewrite map_app; reflexivity|].
split. { split; [exact P3|]. split; [exact FA0|]. split; [exact SO0|]. split; [exact HA|]. split; [exact BLK'|].
unfold MAX_INPUT. split; [split; [lia| exact CAPK]|]. split; [rewrite length_app; lia| exact BR]. }
split; [exists pad; exact FR|]. split; [exact BA3|]. split; [exact CJ3|]. split; [exact ERR2|]. split; [exact FRM|]. split; [exact MKF|].
eexists. match type of SGX with rw_cells _ _ _ [CB ?k _] => replace (Z.to_nat 65536) with k by lia end. exact SGX.
+
assert (Ebs : bs = []) by (destruct bs; [reflexivity| cbn [length] in K1; exfalso; rewrite ?unsigned_lit in K1 by lia; lia]). subst bs.
cbn [length Nat.eqb]. apply evt_done.
lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM rsegs tm s (POSTBODY' fd P1v) msx) end.
apply implM_ret. apply evt_done.
cbn [POSTBODY]. unfold RDBRK.
sf_eexists 17%nat. first [ unshelve sf_eexists 8%nat; [ exact (F) | exact (fc) | exact (m2) | exact (A) | exact ((rd_cap st1)) | exact (DATA) | exact (junk) | exact (errv) | ] | sf_fb; exists F, fc, m2, A, (rd_cap st1), DATA, junk, errv ].
split; [rewrite LENZ; reflexivity|].
split; [exact HC|]. split; [| split; [exists pad; exact FR| split; [exact BA2| split; [exact CJ2| split; [exact ERR2| split; [exact FRM| exact MKF]]]]]].
split; [exact P2|]. split; [exact FA0|]. split; [exact SO0|]. split; [exact HA|]. split; [rewrite <- ELEN; exact BLK|]. unfold MAX_INPUT. split; [split; [lia| exact CAPK]|]. split; [lia| exact BR].
Qed.
End B2.
