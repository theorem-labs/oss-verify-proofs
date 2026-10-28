(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj X1bs X1c2 X1br.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0px X0qp X0pw.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ea X1fl X1m2 X1m3 X1m5 X1m6 X1fr X1h7 X1go X1hk.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk X1n7. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1n8 X1my X1ho X1hv X1nb X1mc X1na.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1ra X1qu X1qx X1ri X1r3 X1nt X1rh X1re X1r6.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Local Notation rsegs := Ubsan.M.loaded_segments.

Definition dec_entry (d : dec_state bptr) : Z := match d with DecNB _ => A_nb_decode | DecSB _ _ => A_sb_decode end.

Lemma dec_nestedR_iff : forall d : dec_state bptr, dec_nestedR d <-> dec_nested d.
Proof. induction d as [st|s low IH]; cbn; [tauto|]. rewrite IH. tauto. Qed.

Lemma top_isave_none_isave : forall d : dec_state bptr, top_isave_none d <-> dec_isave d = None.
Proof. intros [st|s low]; cbn; tauto. Qed.

Lemma isave_ok_of_none : forall d : dec_state bptr, top_isave_none d -> isave_ok d.
Proof. intros [st|s low] H; cbn in H |- *; rewrite H; exact I. Qed.

Lemma land7_mod8 : forall v, Z.land v 7 = v mod 8.
Proof. intros. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.
Ltac ntk := let K := fresh "K" in if_cases K; zify_cond K; rewrite ?land7_mod8 in K; rewrite ?signed_lit_small in K by lia; [exfalso; lia | clear K].
Ltac nt := first [ if_false_x | ntk ].

Lemma rdec_disp {RCEIL : RunCeiling} : forall A d, (A = A_speex_decode \/ A = A_speex_decode_native) ->
rdec_at (dec_entry d) d -> rdec_at A d.
Proof.
intros A d HA RD. unfold rdec_at. intros until canary.
intros REP DEP ISOK NES ND LAP BRL BR BOK OWN DRANGE DAP UOUT LOUT OUT4 XST ST4 TP SE SS LAY STK LO SPX SP16 MI FRM -> -> ->.
assert (ENB : NB_MODE_PTR = 0x3b7c8) by reflexivity.
assert (EWB : A_speex_wb_mode = 0x3bbb8) by reflexivity. assert (EUWB : A_speex_uwb_mode = 0x3bc18) by reflexivity.
eapply (implM_evt rsegs _ _ _ (fun ms1 => exists va3 va4,
ms1 = MS (mkR ra sp gp tp t0 (Z_to_bv 64 (dec_entry d)) t2 s0 s1 (Z_to_bv 64 S) (Z_to_bv 64 BITS) (Z_to_bv 64 OUT) va3 va4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (dec_entry d)) fc None m (seg_rom rsegs))).
{ destruct d as [nst|s low].
- cbn [decst_rep] in REP. destruct REP as [ELBD NREP].
assert (BS : rblock_range S NBSTATE_SIZEOF).
{ apply (BRL (nb_blk nst, S, NBSTATE_SIZEOF)). rewrite ELBD. left. reflexivity. }
first [ sf_destruct 5%nat BS as S0 S16 _ SCE _ | sf_fb; destruct BS as (S0 & S16 & _ & SCE & _) ]. unfold alloc_ceiling, NBSTATE_SIZEOF in SCE, S0.
first [ sf_destruct 7%nat NREP as AL POS INV j JOK CBS X | sf_fb; destruct NREP as (AL & POS & INV & j & JOK & CBS & X) ].
apply (nb_pieces_of_cells rsegs _ _ _ m S OUT STEREO nst j JOK) in X. destruct X as (P0 & _). unfold nb_hdr_cells in P0.
pose proof (nb_desc_of_pristine m TP) as DND. unfold nb_desc_cells in DND. unfold X1ff.rsegs in DND.
cbn [dec_entry]. destruct HA as [-> | ->]; unfold A_speex_decode, A_speex_decode_native, A_nb_decode;
zstep; nt; zstep; zstep; nt; zstep; zstep; nt; zstep; zstep; nt; zstep; zstep; apply evt_done; eexists; eexists; reflexivity.
- cbn [decst_rep] in REP.
first [ sf_destruct 12%nat REP as a j LBL ELBD AL POS INV JOK X BU OUTL RL | sf_fb; destruct REP as (a & j & LBL & ELBD & AL & POS & INV & JOK & X & BU & OUTL & RL) ].
assert (BS : rblock_range S SBSTATE_SIZEOF).
{ apply (BRL (sbd_blk s, S, SBSTATE_SIZEOF)). rewrite ELBD. left. reflexivity. }
first [ sf_destruct 5%nat BS as S0 S16 _ SCE _ | sf_fb; destruct BS as (S0 & S16 & _ & SCE & _) ]. unfold alloc_ceiling, SBSTATE_SIZEOF in SCE, S0.
pose proof INV as (Imo & _).
pose proof (desc_of_pristine m (sbd_mode s) TP) as DND. unfold X1ff.rsegs in DND.
unfold sb_cells in X. unfold X1ff.rsegs in X.
cbn [dec_entry]. destruct Imo as [E|E]; rewrite E in X, DND; cbn [sb_mode_ptr desc_cells_of] in X, DND |- *;
unfold wb_desc_cells, uwb_desc_cells in DND;
destruct HA as [-> | ->]; unfold A_speex_decode, A_speex_decode_native, A_sb_decode;
zstep; nt; zstep; zstep; nt; zstep; zstep; nt; zstep; zstep; nt; zstep; zstep; apply evt_done; eexists; eexists; reflexivity. }
cbv beta. intros ms1 [va3 [va4 ->]].
eapply RD; try eassumption; reflexivity.
Qed.

Section Bridge.
Context {RCEIL : RunCeiling}.
Hypothesis NBDEC : nb_decode_stmtW.
Hypothesis SBDEC : sb_decode_goal.
Hypothesis SBH : forall k,
(forall d, (dec_depth d <= k)%nat -> rdec_at A_speex_decode_native d) ->
(forall d, (dec_depth d <= k)%nat -> rctl_at d) ->
sb_hyps k.

#[using="NBDEC SBDEC SBH"] Lemma rdec_entry_all : forall k d, (dec_depth d <= k)%nat -> rdec_at (dec_entry d) d.
Proof.
induction k as [|k IH]; intros d Hd.
- pose proof (dec_depth_pos d). lia.
- destruct d as [st|s low]; cbn [dec_entry].
+ apply rdec_nb. exact NBDEC.
+ cbn in Hd. apply (SBDEC k); [| lia].
apply SBH; [| intros d' _; apply rctl_all].
intros d' Hd'. apply rdec_disp; [right; reflexivity|]. apply IH. exact Hd'.
Qed.

#[using="NBDEC SBDEC SBH"] Theorem rdec_native_all : forall d, rdec_at A_speex_decode_native d.
Proof. intros d. apply rdec_disp; [right; reflexivity|]. apply (rdec_entry_all (dec_depth d)). lia. Qed.

#[using="NBDEC SBDEC SBH"] Theorem rdec_decode_all : forall d, rdec_at A_speex_decode d.
Proof. intros d. apply rdec_disp; [left; reflexivity|]. apply (rdec_entry_all (dec_depth d)). lia. Qed.

#[using="Type"] Lemma rdec_depth_le : forall d : dec_state bptr, (dec_depth d <= 3)%nat -> rdec_depth d <= DECODE_STACK.
Proof.
intros d Hd. assert (G : forall d' : dec_state bptr, rdec_depth d' <= Z.of_nat (dec_depth d') * SB_LOCAL_DEPTH).
{ induction d' as [st|s low IH]; cbn [rdec_depth dec_depth]; unfold NB_DECODE_DEPTH, NB_FRAME, NB_FPRINTF_DEPTH, SB_LOCAL_DEPTH in *; lia. }
specialize (G d). unfold SB_LOCAL_DEPTH, DECODE_STACK in *. lia.
Qed.

Definition rspx_decode_stmtX : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(st : PState) (LB : list block) (STEREO S : Z) (d : dec_state bptr) (LBD : list block) (b : bits_st bptr) (BITS Dc OUT lo : Z)
(outb stb : list byte) (canary : word),
DECREP STEREO m S d LBD -> RHEAP st LB m -> (forall x, In x LBD -> In x LB) ->
bits_rep rsegs m BITS Dc b -> bits_ok b -> sb_owner b = 1 -> In (sb_chars b, Dc, sb_buf_size b) LB ->
(forall x, In x LBD -> blk_id x <> sb_chars b) ->
u8arr rsegs m OUT outb -> Z.of_nat (length outb) = HOUT_BYTES -> rw_cells rsegs m STEREO [CB 24 stb] ->
rtables_pristine m -> stderr_wfile m -> ssp_cells m canary ->
(BITS + 48 <= OUT \/ OUT + HOUT_BYTES <= BITS) -> (BITS + 48 <= STEREO \/ STEREO + 24 <= BITS) ->
(OUT + HOUT_BYTES <= STEREO \/ STEREO + 24 <= OUT) ->
(BITS + 48 <= lo \/ bv_unsigned sp <= BITS) -> (OUT + HOUT_BYTES <= lo \/ bv_unsigned sp <= OUT) ->
(STEREO + 24 <= lo \/ bv_unsigned sp <= STEREO) ->
alloc_ceiling <= BITS -> alloc_ceiling <= OUT -> alloc_ceiling <= STEREO ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - DECODE_STACK ->
(bv_unsigned sp < 2^63) ->
bv_unsigned sp mod 16 = 0 -> OUT mod 4 = 0 -> STEREO mod 4 = 0 ->
mem_inv rsegs m -> frm0 fc ->
tp = wz RATP ->
a0 = wz S -> a1 = wz BITS -> a2 = wz OUT ->
implM rsegs (speex_decode io_notify bits_unpack_unsigned_M bits_peek_M bits_advance_M bits_remaining_M d b 0) st
(rspx_decode_post DECREP ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 st STEREO S LBD b BITS Dc OUT lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz A_speex_decode) fc None m (seg_rom rsegs)).

#[using="NBDEC SBDEC SBH"] Theorem rspx_decode_proofX : rspx_decode_stmtX.
Proof.
unfold rspx_decode_stmtX. intros until canary.
intros REP HEAP INLBD BR BOK OWN INBITS NOTB UOUT LOUT XST TP SE SS ABO ABS AOS ABL AOL ASL CB_ CO CS STK CL LO SPX SP16 OUT4 ST4 MI FRM TPE -> -> ->.
first [ sf_destruct 7%nat REP as TOP DE ND LAP NE OUT0 R | sf_fb; destruct REP as (TOP & DE & ND & LAP & NE & OUT0 & R) ].
assert (R1 : DREP OUT STEREO m S d LBD) by (eapply decst_rep_reout; [exact TOP| exact R]).
pose proof (RHEAP_block_range_proof _ _ _ _ HEAP INBITS) as DRANGE. cbn [blk_addr blk_size fst snd] in DRANGE.
eapply implM_mono.
{ eapply (X1hv.implM_leaves rsegs).
- apply (speex_decode_leaves io_notify d b 0 st).
- eapply (rdec_decode_all d ra sp gp tp t0 t1 t2 s0 s1 _ _ _ a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
st OUT STEREO S LBD b BITS Dc lo outb stb canary);
try eassumption; try reflexivity.
+ apply isave_ok_of_none. exact TOP.
+ apply dec_nestedR_iff. exact NE.
+ intros x Hx. eapply RHEAP_block_range_proof; [exact HEAP| apply INLBD; exact Hx].
+ intros x Hx. unfold apart.
destruct (RHEAP_blocks_disjoint_proof _ _ _ (sb_chars b, Dc, sb_buf_size b) x HEAP INBITS (INLBD x Hx)) as [D1|D1];
[cbn; intros E; apply (NOTB x Hx); symmetry; exact E| cbn in D1; left; exact D1| cbn in D1; right; exact D1].
+ unfold rdec_layout, apart. repeat match goal with |- _ /\ _ => split end; try assumption; unfold HOUT_BYTES, BITS_SIZEOF in *; lia.
+ pose proof (rdec_depth_le d DE). lia. }
cbv beta. intros [[ret d'] b'] st' ms' [PO LEAF]. cbn in LEAF. first [ sf_destruct 5%nat LEAF as RR BSIM EIS EBLK EMO | sf_fb; destruct LEAF as (RR & BSIM & EIS & EBLK & EMO) ].
first [ sf_destruct 42%nat PO as y0 y1 y2 b1 b2 b3 b4 b5 b6 b7 y3 y4 y5 y6 F' fc' m' outb' stb' -> RET DD DM NES' FRM' MU WM MI' ST' DR' EXC' BI' BOK' EOW ECH EBS OUT' LOUT' STB' SEW' SSP' -> | sf_fb; destruct PO as (y0 & y1 & y2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & y3 & y4 & y5 & y6 & F' & fc' & m' & outb' & stb' & -> & RET & DD & DM & NES' & FRM' & MU & WM & MI' & ST' & DR' & EXC' & BI' & BOK' & EOW & ECH & EBS & OUT' & LOUT' & STB' & SEW' & SSP' & ->) ].
unfold rspx_decode_post.
first [ unshelve sf_eexists 19%nat; [ exact (y0) | exact (y1) | exact (y2) | exact (b1) | exact (b2) | exact (b3) | exact (b4) | exact (b5) | exact (b6) | exact (b7) | exact (y3) | exact (y4) | exact (y5) | exact (y6) | exact (F') | exact (fc') | exact (m') | exact (outb') | exact (stb') | ] | sf_fb; exists y0, y1, y2, b1, b2, b3, b4, b5, b6, b7, y3, y4, y5, y6, F', fc', m', outb', stb' ].
split; [reflexivity|]. split; [exact RET|]. split; [exact FRM'|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|].
split.
{ split; [apply top_isave_none_isave; rewrite EIS; apply top_isave_none_isave; exact TOP|].
split; [rewrite DD; exact DE|]. split; [exact ND|]. split; [exact LAP|].
split; [apply dec_nestedR_iff; exact NES'|]. exists OUT. exact DR'. }
split; [exact BI'|]. split; [exact BOK'|]. split; [exact EOW|]. split; [exact ECH|]. split; [exact EBS|].
split; [exact OUT'|]. split; [exact LOUT'|]. split; [exact STB'|]. split; [exact SEW'|]. reflexivity.
Qed.

#[using="NBDEC SBDEC SBH"] Theorem rspx_decode_proof : rspx_decode_stmt DECREP.
Proof. exact rspx_decode_proofX. Qed.
End Bridge.
