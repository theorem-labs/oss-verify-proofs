(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bu X1cf X1cc X1bj X1bs X1c2 X1br X1bq.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0px X0qn X0qp X0pw.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1m2 X1m3 X1m5 X1m6 X1kx X1el X1ec. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk X1n7. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1h7 X1go X1hk X1ho X1n8 X1my X1nc X1ne.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1ra X1qu X1qx X1r3 X1r4 X1nt X1rh X1re.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.

Definition lower_mode (mo : spx_mode) : spx_mode := match mo with ModeUWB => ModeWB | _ => ModeNB end.
Definition sbmode_addr (mo : spx_mode) : Z := match mo with ModeUWB => A_sb_uwb_mode | _ => A_sb_wb_mode end.

Lemma speex_decoder_init_sb : forall mo, (mo = ModeWB \/ mo = ModeUWB) ->
speex_decoder_init raw_calloc raw_free mo = sb_decoder_init raw_calloc raw_free mo (speex_decoder_init raw_calloc raw_free (lower_mode mo)).
Proof. intros mo [-> | ->]; reflexivity. Qed.

Definition z4 : list byte := repeat (Z_to_bv 8 0) 4.
Definition sbx_cells (md lowp : Z) (ffs fs sub nbs lpc first sr enh : word)
(g0 g1 exc oq iq msp pg er isave : Z) (ener seed esub : word) (subm : Z) (sid : word) : list cell :=
[C8 (Z_to_bv 64 md); C8 (Z_to_bv 64 lowp); C4 ffs; C4 fs; C4 sub; C4 nbs; C4 lpc; C4 first; C4 sr; C4 enh; C8 (Z_to_bv 64 0);
C8 (Z_to_bv 64 g0); C8 (Z_to_bv 64 g1); C8 (Z_to_bv 64 exc); C8 (Z_to_bv 64 oq); C8 (Z_to_bv 64 iq); C8 (Z_to_bv 64 msp);
C8 (Z_to_bv 64 pg); C8 (Z_to_bv 64 er); C8 (Z_to_bv 64 isave); C4 ener; C4 seed; C4 esub; CB 4 z4; C8 (Z_to_bv 64 subm); C4 sid; CB 4 z4].
Definition w0 : word := Z_to_bv 64 0.
Definition sb_zero_cells : list cell := sbx_cells 0 0 w0 w0 w0 w0 w0 w0 w0 w0 0 0 0 0 0 0 0 0 0 w0 w0 w0 0 w0.

Lemma sb_zero_recast : forall m A, rw_cells rsegs m A [CB 160 (repeat (Z_to_bv 8 0) 160)] -> rw_cells rsegs m A sb_zero_cells.
Proof.
intros m A X. apply (X0pw.rw_cells_recast rsegs m A _ _ X); [cbn; repeat split; reflexivity| vm_compute; reflexivity| reflexivity].
Qed.

Definition sbinit_frame (j4 : list byte) (tmp : word) (s3 s2 s1 s0 ra : word) : list cell :=
[CB 4 j4; C4 tmp; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition sbinit_frame0 (j8 : list byte) (s3 s2 s1 s0 ra : word) : list cell :=
[CB 8 j8; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition sb_at78 {RCEIL : RunCeiling} (mo : spx_mode) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
(s : PState) (LB : list block) (AB lo : Z) (m0 : mem)
(blk : bptr) (S : Z) (lr : Z) (low : dec_state bptr) (LBL : list block)
(st : PState) (ms : machine_state) : Prop :=
exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc : bv 32) (m : mem) (errv : word) (j4 : list byte) (tmp : word) (SL : Z),
ms = MS (mkR (Z_to_bv 64 0x2e544) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 S) (Z_to_bv 64 1073741824) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (sbmode_addr mo)) (Z_to_bv 64 1) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (Z_to_bv 64 0x2e558) fc None m (seg_rom rsegs)
/\ frm0 fc /\ mem_inv rsegs m /\ stk rsegs m lo (bv_unsigned sp + -48)
/\ rw_cells rsegs m (bv_unsigned sp + -48) (sbinit_frame j4 tmp s3 s2 s1 s0 ra)
/\ rw_cells rsegs m (errno_addr tp) [C4 errv] /\ rauxv_ok m AB
/\ rheap_pres LB (bv_unsigned sp) m0 m /\ ps_so st = ps_so s /\ rtables_pristine m
/\ RHEAP st (((blk, S, SBSTATE_SIZEOF) :: LBL) ++ LB) m
/\ rblock_range S SBSTATE_SIZEOF /\ 0 < SL < 2^63
/\ rw_cells rsegs m S (sbx_cells (mode_addr mo) SL (Z_to_bv 64 (2 * sbm_frameSize mo)) (Z_to_bv 64 (sbm_frameSize mo)) (Z_to_bv 64 (sbm_subframeSize mo))
(Z_to_bv 64 4) (Z_to_bv 64 8) (Z_to_bv 64 1) (Z_to_bv 64 (lr * 2)) w0 0 0 0 0 0 0 0 0 0 w0 w0 (Z_to_bv 64 1)
(sbmode_addr mo + 40) (Z_to_bv 64 (sbm_defaultSubmode mo)))
/\ (forall STEREO, DREP 0 STEREO m SL low LBL)
/\ dec_mode low = lower_mode mo /\ dec_depth low = mode_depth (lower_mode mo) /\ lr = init_rate (lower_mode mo) /\ dec_stereo_off low /\ dec_nestedR low.

Definition sb_init_rest (mo : spx_mode) (blk : bptr) (lr : Z) (low : dec_state bptr) : M PState (option (dec_state bptr)) :=
let frame_size := sbm_frameSize mo in
let subframeSize := sbm_subframeSize mo in
let nbSubframes := Z.quot frame_size subframeSize in
let lpcSize := sbm_lpcSize mo in
let sampling_rate := lr * 2 in
g0 <- raw_calloc (QMF_ORDER * 4) 1 ;;
g1 <- raw_calloc (QMF_ORDER * 4) 1 ;;
ex <- raw_calloc (subframeSize * 4) 1 ;;
oq <- raw_calloc (lpcSize * 4) 1 ;;
iq <- raw_calloc (lpcSize * 4) 1 ;;
pg <- raw_calloc (nbSubframes * 4) 1 ;;
er <- raw_calloc (nbSubframes * 4) 1 ;;
ms <- raw_calloc (2 * lpcSize * 4) 1 ;;
match g0, g1, ex, oq, iq, pg, er, ms with
| Some g0, Some g1, Some ex, Some oq, Some iq, Some pg, Some er, Some ms =>
mret (Some (DecSB (mkSBD blk mo (2 * frame_size) frame_size subframeSize nbSubframes lpcSize
1 sampling_rate 0 g0 g1 ex oq iq ms pg er None 1 (sbm_defaultSubmode mo)) low))
| _, _, _, _, _, _, _, _ => munr
end.

Definition sb_init_rest2 (mo : spx_mode) (blk : bptr) (low : dec_state bptr) : M PState (option (dec_state bptr)) :=
let '(low_rate, low1) := speex_decoder_ctl low CtlGetSamplingRate in
let '(_, low2) := speex_decoder_ctl low1 (CtlSetWideband 1) in
sb_init_rest mo blk low_rate low2.

Definition sb_at40 {RCEIL : RunCeiling} (mo : spx_mode) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(s : PState) (LB : list block) (AB lo : Z) (m0 : mem)
(blk : bptr) (S : Z) (low : dec_state bptr) (LBL : list block)
(st : PState) (ms : machine_state) : Prop :=
exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (errv : word) (j8 : list byte) (SL lr : Z),
ms = MS (mkR (Z_to_bv 64 0x2e514) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 S) (Z_to_bv 64 (mode_addr mo)) (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (sbmode_addr mo)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x2e514) fc None m (seg_rom rsegs)
/\ frm0 fc /\ mem_inv rsegs m /\ stk rsegs m lo (bv_unsigned sp + -48)
/\ rw_cells rsegs m (bv_unsigned sp + -48) (sbinit_frame0 j8 s3 s2 s1 s0 ra)
/\ rw_cells rsegs m (errno_addr tp) [C4 errv] /\ rauxv_ok m AB
/\ rheap_pres LB (bv_unsigned sp) m0 m /\ ps_so st = ps_so s /\ rtables_pristine m
/\ RHEAP st (LBL ++ (blk, S, SBSTATE_SIZEOF) :: LB) m
/\ rblock_range S SBSTATE_SIZEOF /\ 0 < SL < 2^63
/\ rw_cells rsegs m S [C8 (Z_to_bv 64 (mode_addr mo)); C8 (Z_to_bv 64 SL); C4 (Z_to_bv 64 (2 * sbm_frameSize mo)); C4 (Z_to_bv 64 (sbm_frameSize mo));
C4 (Z_to_bv 64 (sbm_subframeSize mo)); C4 (Z_to_bv 64 4); C4 (Z_to_bv 64 8); C4 w0]
/\ rw_cells rsegs m (S + 40) [C4 (Z_to_bv 64 lr)] /\ - 2^31 <= lr < 2^31 /\ lr = fst (speex_decoder_ctl low CtlGetSamplingRate)
/\ rw_cells rsegs m (S + 44) [C4 w0; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 w0; C4 w0; C4 (Z_to_bv 64 1); CB 4 z4; C8 (Z_to_bv 64 0); C4 w0; CB 4 z4]
/\ (forall STEREO, DREP 0 STEREO m SL (snd (speex_decoder_ctl low CtlGetSamplingRate)) LBL)
/\ dec_mode low = lower_mode mo /\ dec_depth low = mode_depth (lower_mode mo)
/\ fst (speex_decoder_ctl low CtlGetSamplingRate) = init_rate (lower_mode mo) /\ dec_stereo_off low /\ dec_nestedR low
/\ bv_unsigned sp mod 16 = 0.

Lemma mode_facts : forall mo, (mo = ModeWB \/ mo = ModeUWB) ->
(sbm_frameSize mo = 160 /\ sbm_subframeSize mo = 40 \/ sbm_frameSize mo = 320 /\ sbm_subframeSize mo = 80)
/\ sbm_lpcSize mo = 8 /\ Z.quot (sbm_frameSize mo) (sbm_subframeSize mo) = 4 /\ 0 <= sbm_defaultSubmode mo <= 7
/\ init_depth mo = 48 + init_depth (lower_mode mo) /\ init_rate mo = init_rate (lower_mode mo) * 2
/\ mode_depth mo = S (mode_depth (lower_mode mo)).
Proof. intros mo [-> | ->]; cbn; repeat split; try lia; reflexivity. Qed.

Lemma sb_desc_head : forall m mo, (mo = ModeWB \/ mo = ModeUWB) -> rtables_pristine m ->
exists rest, rw_cells rsegs m (mode_addr mo) (C8 (Z_to_bv 64 (sbmode_addr mo)) :: rest)
/\ rest = tl (desc_cells_of mo).
Proof.
intros m mo Hmo TP. pose proof (desc_of_pristine m mo TP) as D.
destruct Hmo as [-> | ->]; cbn [sb_mode_ptr desc_cells_of mode_addr] in D |- *; eexists; (split; [| reflexivity]);
unfold wb_desc_cells, uwb_desc_cells in D |- *; cbn [tl]; exact D.
Qed.
Lemma sb_mode_struct : forall m mo, (mo = ModeWB \/ mo = ModeUWB) -> rtables_pristine m ->
rw_cells rsegs m (sbmode_addr mo)
([C8 (Z_to_bv 64 (mode_addr (lower_mode mo))); C4 (Z_to_bv 64 (sbm_frameSize mo)); C4 (Z_to_bv 64 (sbm_subframeSize mo)); C4 (Z_to_bv 64 (sbm_lpcSize mo));
C4 (Z_to_bv 64 (match mo with ModeUWB => 0x3f666666 | _ => 0x3f666666 end))]
++ skipn 5 (match mo with ModeUWB => sb_uwb_mode_cells | _ => sb_wb_mode_cells end)).
Proof.
intros m mo Hmo TP. destruct Hmo as [-> | ->]; cbn -[rw_cells rsegs Z_to_bv].
- pose proof (sb_wb_mode_of_pristine m TP) as X. unfold sb_wb_mode_cells in X. exact X.
- pose proof (sb_uwb_mode_of_pristine m TP) as X. unfold sb_uwb_mode_cells in X. exact X.
Qed.

Lemma sb_decoder_init_fold : forall mo (LI : M PState (option (dec_state bptr))),
sb_decoder_init raw_calloc raw_free mo LI =
(r <- raw_calloc SIZEOF_SBDECSTATE 1 ;;
match r with
| None => mret None
| Some blk => ol <- LI ;; match ol with None => munr | Some low => sb_init_rest2 mo blk low end
end).
Proof. reflexivity. Qed.

Lemma land3_mod4 : forall v, Z.land v 3 = v mod 4.
Proof. intros. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma land7_mod8 : forall v, Z.land v 7 = v mod 8.
Proof. intros. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.
Ltac ntk := let K := fresh "K" in if_cases K; zify_cond K; rewrite ?land3_mod4, ?land7_mod8 in K; rewrite ?signed_lit_small in K by lia; [exfalso; lia | clear K].
Ltac nt := first [ if_false_x | ntk ].

Theorem rinit_sbA {RCEIL : RunCeiling} : forall (mo : spx_mode)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LB : list block) (AB lo : Z) (errv : word),
(mo = ModeWB \/ mo = ModeUWB) -> rinit_at (lower_mode mo) ->
RHEAP s LB m -> rtables_pristine m ->
rauxv_ok m AB -> bv_unsigned sp <= AB ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - init_depth mo ->
rw_cells rsegs m (errno_addr tp) [C4 errv] ->
mem_inv rsegs m -> frm0 fc -> tp = Z_to_bv 64 RATP ->
a0 = Z_to_bv 64 (mode_addr mo) -> bv_unsigned sp mod 16 = 0 ->
(forall blk S low LBL st1 ms1,
sb_at40 mo ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB AB lo m blk S low LBL st1 ms1 ->
implM rsegs (sb_init_rest2 mo blk low) st1 (rinit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB AB lo mo m) ms1) ->
implM rsegs (speex_decoder_init raw_calloc raw_free mo) s
(rinit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB AB lo mo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_speex_decoder_init) fc None m (seg_rom rsegs)).
Proof.
intros mo ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB AB lo errv
Hmo IH HEAP TP AUX SB ST CLO LO ERR MI FRM TPE -> SP16 KONT.
pose proof (mode_facts mo Hmo) as sfP_; first [ sf_destruct 7%nat sfP_ as FSS LPC NBS DSM IDP IRT MDP | sf_fb; destruct sfP_ as (FSS & LPC & NBS & DSM & IDP & IRT & MDP) ]. rewrite IDP in LO.
pose proof CLO as CLOv. unfold alloc_ceiling in CLOv.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
assert (ETP : errno_addr tp = RERRNO) by (rewrite TPE; unfold RATP, RERRNO; rewrite unsigned_lit by lia; reflexivity).
rewrite ETP in ERR. unfold RERRNO in ERR.
assert (IDL : 8272 <= init_depth (lower_mode mo)) by (destruct Hmo as [-> | ->]; cbn; lia).
pose proof (desc_of_pristine m mo TP) as DESC.
rewrite (speex_decoder_init_sb mo Hmo). rewrite sb_decoder_init_fold.

pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU0. pose proof (wmono_refl rsegs m) as WM0.
carve_frame 48%nat ST.
eapply (implM_bind rsegs _ _ _ (fun r s' ms' => exists m1 j8,
rcalloc_post (Z_to_bv 64 0x2e488) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp s0 (Z_to_bv 64 (mode_addr mo)) s2 s3
s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB (1 * 160) lo AB m1 r s' ms'
/\ rw_cells rsegs m1 (bv_unsigned sp + -48) (sbinit_frame0 j8 s3 s2 s1 s0 ra)
/\ munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m1 /\ wmono rsegs m m1)).
{ eapply (implM_evt rsegs _ _ _ (fun ms1 => exists m1 j8,
ms1 = MS (mkR (Z_to_bv 64 0x2e488) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 (Z_to_bv 64 A_sb_decoder_init) t2 s0 (Z_to_bv 64 (mode_addr mo))
(Z_to_bv 64 160) (Z_to_bv 64 1) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 RCALLOC_SYM) fc None m1 (seg_rom rsegs)
/\ rw_cells rsegs m1 (bv_unsigned sp + -48) (sbinit_frame0 j8 s3 s2 s1 s0 ra)
/\ munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1 /\ stk rsegs m1 lo (bv_unsigned sp + -48))).
{ destruct Hmo as [-> | ->]; cbn [desc_cells_of sb_mode_ptr mode_addr] in DESC; unfold wb_desc_cells, uwb_desc_cells, A_speex_wb_mode, A_speex_uwb_mode in DESC;
unfold A_speex_decoder_init; cbn [mode_addr]; unfold A_speex_wb_mode, A_speex_uwb_mode.
all: zstep; nt; zstep; zstep; nt; zstep; zstep.
all: step; lstep; lstep; lstep; lstep; lstep.
all: step; step; step; step.
all: apply evt_done; unfold sbinit_frame0; sf_eexists 2%nat; (split; [reflexivity|]); (split; [eassumption|]); (split; [exact MU0|]); (split; [exact WM0|]); split; assumption. }
clear MU0 WM0. cbv beta. intros ms1 sfH_; first [ sf_destruct 8%nat sfH_ as m1 j8 -> FRa MU1 WM1 MI1 ST1 | sf_fb; destruct sfH_ as (m1 & j8 & -> & FRa & MU1 & WM1 & MI1 & ST1) ].
assert (HEAP1 : RHEAP s LB m1).
{ eapply RHEAP_frame_proof; [exact HEAP| exact MU1| exact WM1|]. constructor; [|constructor]. left. cbn [fst]. lia. }
assert (AUX1 : rauxv_ok m1 AB).
{ eapply rauxv_ok_frame; [exact AUX| exact MU1| exact WM1|]. constructor; [|constructor]. cbn [fst snd]. unfold RAUXV_CELL. lia. }
assert (ERR1 : rw_cells rsegs m1 316332 [C4 errv]).
{ eapply rw_cells_transport; [exact ERR| exact MU1| exact WM1|]. cbn. split; [lia| exact I]. }
eapply implM_mono.
{ eapply (rcalloc_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 s LB 160 1 lo AB errv HEAP1 AUX1);
[rewrite unsigned_lit by lia; lia| rewrite unsigned_lit by lia; exact ST1| exact CLO| rewrite unsigned_lit by lia; unfold RCALLOC_STACK; lia
| rewrite ETP; unfold RERRNO; exact ERR1| exact MI1| exact TPE| reflexivity| reflexivity| lia| lia| unfold RSMALL_MAX; lia]. }
cbv beta. intros r s' ms' H. exists m1, j8. exact (conj H (conj FRa (conj MU1 WM1))). }
cbv beta. intros r s1' ms2 sfH_; first [ sf_destruct 6%nat sfH_ as m1 j8 POST FR0 MU1 WM1 | sf_fb; destruct sfH_ as (m1 & j8 & POST & FR0 & MU1 & WM1) ].
first [ sf_destruct 26%nat POST as w0' w1 w2 ra0 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 m2 errv2 -> MI2 ST2 ERR2 AUX2 HP2 PSF PSO RES | sf_fb; destruct POST as (w0' & w1 & w2 & ra0 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & m2 & errv2 & -> & MI2 & ST2 & ERR2 & AUX2 & HP2 & PSF & PSO & RES) ].
rewrite unsigned_lit in ST2 by lia. rewrite unsigned_lit in HP2 by lia. rewrite ret_pc_even by lia. rewrite ETP in ERR2. unfold RERRNO in ERR2.
change (mem_inv rsegs m2) in MI2. change (stk rsegs m2 lo (bv_unsigned sp + -48)) in ST2. change (rw_cells rsegs m2 316332 [C4 errv2]) in ERR2.
assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp + -48) (sbinit_frame0 j8 s3 s2 s1 s0 ra)) by (eapply rheap_pres_rw_cells; [exact HP2| exact FR0| left; cbn; lia]).
assert (PRES2 : rheap_pres LB (bv_unsigned sp) m m2).
{ eapply rheap_pres_trans; [| eapply rheap_pres_weaken; [exact HP2| lia| auto]].
eapply rheap_pres_of_munch; [exact MU1| exact WM1|]. intros x Hx CA. apply outside_single.
destruct CA as [CA|[[CA _]|(b & Hb & Hab)]]; [lia| lia|].
pose proof (RHEAP_block_range_proof _ _ _ b HEAP Hb) as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ _ BC _ | sf_fb; destruct sfP_ as (_ & _ & _ & BC & _) ]. unfold alloc_ceiling in BC. unfold in_block in Hab. lia. }
assert (TP2 : rtables_pristine m2) by (eapply rtables_pristine_rheap; [exact TP| exact PRES2]).
clear FR0 HEAP DESC MU1 WM1.
destruct r as [blk|].
2:{
destruct RES as [-> HEAP2]. clear HP2. cbn [sb_init_rest].
apply implM_ret. unfold sbinit_frame0 in FR2.
step. step. if_cases K0; [| exfalso; zify_cond K0; rewrite ?unsigned_lit in K0 by lia; lia].
step. step. step. step. step. step. step. step.
release_frame FR2 ST2 (bv_unsigned sp).
apply evt_done. unfold rinit_post. sf_eexists 15%nat. first [ unshelve sf_eexists 4%nat; [ exact (F) | exact (fc) | exact (m2) | exact (errv2) | ] | sf_fb; exists F, fc, m2, errv2 ].
split; [reflexivity|]. split; [exact FRM|]. split; [exact MI2|]. split; [exact ST2|].
split; [rewrite ETP; unfold RERRNO; exact ERR2|]. split; [exact AUX2|]. split; [exact PRES2|]. split; [exact PSO|].
split; [reflexivity| exact HEAP2]. }

first [ sf_destruct 7%nat RES as S -> BR HEAP2 BLK _ _ | sf_fb; destruct RES as (S & -> & BR & HEAP2 & BLK & _ & _) ]. change (Z.to_nat (1 * 160)) with 160%nat in BLK.
pose proof BR as sfP_; first [ sf_destruct 5%nat sfP_ as S0 S16 _ SCE SIMG | sf_fb; destruct sfP_ as (S0 & S16 & _ & SCE & SIMG) ]. unfold alloc_ceiling in SCE.
apply sb_zero_recast in BLK. unfold sb_zero_cells, sbx_cells in BLK. clear HP2.
pose proof (sb_mode_struct m2 mo Hmo TP2) as MSTR.
eapply (implM_evt rsegs _ _ _ (fun ms3 => exists m3,
ms3 = MS (mkR (Z_to_bv 64 0x2e4c8) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp w0' w1 w2 (Z_to_bv 64 S) (Z_to_bv 64 (mode_addr mo))
(Z_to_bv 64 (mode_addr (lower_mode mo))) w4 w5 w6 w7 w8 w9 w10 (Z_to_bv 64 (sbmode_addr mo)) s3 s4 s5 s6 s7 s8 s9 s10 s11 w11 w12 w13 w14)
F (Z_to_bv 64 A_speex_decoder_init) fc None m3 (seg_rom rsegs)
/\ rw_cells rsegs m3 S (sbx_cells (mode_addr mo) 0 w0 w0 w0 w0 w0 w0 w0 w0 0 0 0 0 0 0 0 0 0 w0 w0 (Z_to_bv 64 1) 0 w0)
/\ munch [(S, S + 160)] m2 m3 /\ wmono rsegs m2 m3 /\ mem_inv rsegs m3)).
{ pose proof (munch_refl [(S, S + 160)] m2) as MU. pose proof (wmono_refl rsegs m2) as WM.
pose proof (desc_of_pristine m2 mo TP2) as DESC2.
destruct Hmo as [-> | ->]; cbn [desc_cells_of sb_mode_ptr mode_addr lower_mode sbmode_addr app skipn] in DESC2, MSTR |- *;
unfold wb_desc_cells, uwb_desc_cells, sb_wb_mode_cells, sb_uwb_mode_cells, A_speex_wb_mode, A_speex_uwb_mode, A_sb_wb_mode, A_sb_uwb_mode in DESC2, MSTR |- *;
cbn [app skipn] in MSTR.
all: step.
all: step; if_cases K0; [exfalso; zify_cond K0; rewrite ?unsigned_lit in K0 by lia; lia|].
all: zstep; zstep; nt.
all: lstep.
all: zstep; nt.
all: zstep; zstep; nt.
all: zstep.
all: zstep; lstep.
all: zstep; nt.
all: zstep; zstep; nt.
all: zstep; zstep.
all: apply evt_done; eexists; (split; [reflexivity|]); (split; [unfold sbx_cells; eassumption|]); (split; [exact MU|]); split; [exact WM| assumption]. }
cbv beta. intros ms3 sfH_; first [ sf_destruct 6%nat sfH_ as m3 -> X3 MU3 WM3 MI3 | sf_fb; destruct sfH_ as (m3 & -> & X3 & MU3 & WM3 & MI3) ].
assert (HEAP3 : RHEAP s1' ((blk, S, SBSTATE_SIZEOF) :: LB) m3).
{ eapply RHEAP_frame_proof; [exact HEAP2| exact MU3| exact WM3|]. constructor; [|constructor]. right. right.
exists (blk, S, SBSTATE_SIZEOF). split; [left; reflexivity|]. cbn. unfold SBSTATE_SIZEOF. lia. }
assert (AUX3 : rauxv_ok m3 AB).
{ eapply rauxv_ok_frame; [exact AUX2| exact MU3| exact WM3|]. constructor; [|constructor]. cbn [fst snd]. unfold RAUXV_CELL. (clear - SIMG SCE S0 S IDL CLOv MDP LO SB lo AB sp mo RCEIL; lia). }
assert (ERR3 : rw_cells rsegs m3 316332 [C4 errv2]) by (eapply rw_cells_transport; [exact ERR2| exact MU3| exact WM3| cbn; lia]).
assert (FR3 : rw_cells rsegs m3 (bv_unsigned sp + -48) (sbinit_frame0 j8 s3 s2 s1 s0 ra)).
{ unfold sbinit_frame0. eapply rw_cells_transport; [exact FR2| exact MU3| exact WM3| cbn; lia]. }
assert (ST3 : stk rsegs m3 lo (bv_unsigned sp + -48)) by (eapply stk_transport_disjoint; [exact ST2| exact MU3| exact WM3| cbn; lia]).
assert (TP3 : rtables_pristine m3).
{ eapply rtables_pristine_munch; [exact TP2| exact MU3|]. intros x Hx. unfold RTABLES_LO, RTABLES_HI in Hx. cbn. split; [lia| exact I]. }
pose proof (RHEAP_blocks_nodup_proof _ _ _ HEAP2) as ND2.
assert (PRES3 : rheap_pres LB (bv_unsigned sp) m m3).
{ eapply rheap_pres_trans; [exact PRES2|]. eapply rheap_pres_of_munch; [exact MU3| exact WM3|]. intros x Hx CA. apply outside_single.
destruct CA as [CA|[[CA _]|(b & Hb & Hab)]]; [lia| lia|].
destruct (RHEAP_blocks_disjoint_proof _ _ _ (blk, S, SBSTATE_SIZEOF) b HEAP2 ltac:(left; reflexivity) ltac:(right; exact Hb)) as [D|D].
{ intros E. cbn [map] in ND2. apply (proj1 (List.NoDup_cons_iff _ _)) in ND2. destruct ND2 as [NI _]. apply NI. cbn [blk_id fst snd] in E |- *. rewrite E. apply in_map. exact Hb. }
all: unfold in_block in Hab; cbn [blk_addr blk_size fst snd] in D; unfold SBSTATE_SIZEOF in D; lia. }
clear MI2 ST2 ERR2 AUX2 FR2 TP2 PRES2 MU3 WM3 BLK.

eapply implM_bind.
{ eapply (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m3 s1' ((blk, S, SBSTATE_SIZEOF) :: LB) AB lo errv2);
[exact HEAP3| exact TP3| exact AUX3| rewrite unsigned_lit by lia; lia| rewrite unsigned_lit by lia; exact ST3| exact CLO
| rewrite unsigned_lit by lia; lia| rewrite ETP; unfold RERRNO; exact ERR3| exact MI3| exact FRM| exact TPE| reflexivity| rewrite unsigned_lit by lia; lia]. }
cbv beta. intros ol s2' ms4 sfH_; first [ sf_destruct 28%nat sfH_ as y0 y1 y2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 F4 fc4 m4 errv4 -> FRM4 MI4 ST4 ERR4 AUX4 HP4 PSO4 RES | sf_fb; destruct sfH_ as (y0 & y1 & y2 & ya0 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & F4 & fc4 & m4 & errv4 & -> & FRM4 & MI4 & ST4 & ERR4 & AUX4 & HP4 & PSO4 & RES) ].
rewrite unsigned_lit in ST4 by lia. rewrite unsigned_lit in HP4 by lia. rewrite ret_pc_even by lia. rewrite ETP in ERR4. unfold RERRNO in ERR4.
assert (X4 : rw_cells rsegs m4 S (sbx_cells (mode_addr mo) 0 w0 w0 w0 w0 w0 w0 w0 w0 0 0 0 0 0 0 0 0 0 w0 w0 (Z_to_bv 64 1) 0 w0)).
{ eapply rheap_pres_rw_cells; [exact HP4| exact X3|]. right; right. exists (blk, S, SBSTATE_SIZEOF). split; [left; reflexivity|]. cbn. unfold SBSTATE_SIZEOF. lia. }
assert (FR4 : rw_cells rsegs m4 (bv_unsigned sp + -48) (sbinit_frame0 j8 s3 s2 s1 s0 ra)) by (eapply rheap_pres_rw_cells; [exact HP4| exact FR3| left; cbn; lia]).
assert (TP4 : rtables_pristine m4) by (eapply rtables_pristine_rheap; [exact TP3| exact HP4]).
assert (PRES4 : rheap_pres LB (bv_unsigned sp) m m4).
{ eapply rheap_pres_trans; [exact PRES3|]. eapply rheap_pres_weaken; [exact HP4| lia| intros b Hb; right; exact Hb]. }
clear X3 FR3 TP3 PRES3 HEAP3 AUX3 ERR3 ST3 MI3.
unfold sbx_cells in X4. unfold sbinit_frame0 in FR4.
destruct ol as [low|].
2:{
apply implM_unr. }

first [ sf_destruct 13%nat RES as SL LBL -> SLB HEAP4 DREP4 ND4 DM4 TIS4 DD4 RATE4 STO4 NES4 | sf_fb; destruct RES as (SL & LBL & -> & SLB & HEAP4 & DREP4 & ND4 & DM4 & TIS4 & DD4 & RATE4 & STO4 & NES4) ].
clear MSTR. pose proof (sb_mode_struct m4 mo Hmo TP4) as MSTR.
eapply (implM_evt rsegs _ _ _ (fun ms5 => exists m5,
ms5 = MS (mkR (Z_to_bv 64 0x2e514) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp y0 y1 y2 (Z_to_bv 64 S) (Z_to_bv 64 (mode_addr mo))
(Z_to_bv 64 SL) (Z_to_bv 64 25) (Z_to_bv 64 (S + 40)) (Z_to_bv 64 8) ya4 ya5 ya6 ya7
(Z_to_bv 64 (sbmode_addr mo)) s3 s4 s5 s6 s7 s8 s9 s10 s11 y3 y4 y5 y6)
F4 (Z_to_bv 64 A_speex_decoder_ctl) fc4 None m5 (seg_rom rsegs)
/\ rw_cells rsegs m5 S (sbx_cells (mode_addr mo) SL (Z_to_bv 64 (2 * sbm_frameSize mo)) (Z_to_bv 64 (sbm_frameSize mo)) (Z_to_bv 64 (sbm_subframeSize mo))
(Z_to_bv 64 4) (Z_to_bv 64 8) w0 w0 w0 0 0 0 0 0 0 0 0 0 w0 w0 (Z_to_bv 64 1) 0 w0)
/\ munch [(S, S + 160)] m4 m5 /\ wmono rsegs m4 m5 /\ mem_inv rsegs m5)).
{ pose proof (munch_refl [(S, S + 160)] m4) as MU. pose proof (wmono_refl rsegs m4) as WM. clear HP4 PRES4.
destruct Hmo as [-> | ->]; cbn [mode_addr lower_mode sbmode_addr app skipn sbm_frameSize sbm_subframeSize sbm_lpcSize] in MSTR |- *;
unfold sb_wb_mode_cells, sb_uwb_mode_cells, A_speex_wb_mode, A_speex_uwb_mode, A_speex_nb_mode, A_sb_wb_mode, A_sb_uwb_mode in MSTR |- *;
cbn [app skipn] in MSTR.
all: step; rewrite ?sx32_lit by lia.
all: zstep; zstep.
all: lstep; lstep.
all: zstep; nt.
all: step; rewrite ?sx32_lit by lia.
all: zstep.
all: lstep; lstep; lstep.
all: zstep; nt.
all: step; rewrite ?sx32_lit by lia.
all: zstep.
all: lstep; lstep.
all: zstep; zstep; zstep.
all: apply evt_done; eexists; (split; [reflexivity|]); (split; [| split; [exact MU| split; [exact WM| assumption]]]).
all: unfold sbx_cells, w0; cbn [sbm_frameSize sbm_subframeSize Z.mul Pos.mul].
all: eassumption. }
cbv beta. intros ms5 sfH_; first [ sf_destruct 6%nat sfH_ as m5 -> X5 MU5 WM5 MI5 | sf_fb; destruct sfH_ as (m5 & -> & X5 & MU5 & WM5 & MI5) ].

pose proof (RHEAP_blocks_nodup_proof _ _ _ HEAP4) as ND4'.
assert (NDL : List.NoDup (map blk_id LBL)) by (rewrite map_app in ND4'; apply List.NoDup_app_remove_r in ND4'; exact ND4').
assert (LAPL : lbd_apart LBL).
{ intros b1 b2 H1 H2 NE. eapply (RHEAP_blocks_disjoint_proof _ _ _ b1 b2 HEAP4); [apply in_app_iff; left; exact H1| apply in_app_iff; left; exact H2| exact NE]. }
assert (BRL : forall b, In b LBL -> rblock_range (blk_addr b) (blk_size b)) by (intros b Hb; eapply RHEAP_block_range_proof; [exact HEAP4| apply in_app_iff; left; exact Hb]).
assert (SAPL : forall b, In b LBL -> S + 160 <= blk_addr b \/ blk_addr b + blk_size b <= S).
{ intros b Hb. destruct (RHEAP_blocks_disjoint_proof _ _ _ (blk, S, SBSTATE_SIZEOF) b HEAP4 ltac:(apply in_app_iff; right; left; reflexivity) ltac:(apply in_app_iff; left; exact Hb)) as [D|D].
{ intros E. rewrite map_app in ND4'. eapply (NoDup_app_in_neq _ _ _ _ ND4'); [apply in_map; exact Hb| left; reflexivity| cbn; cbn in E; rewrite E; reflexivity]. }
all: cbn [blk_addr blk_size fst snd] in D |- *; unfold SBSTATE_SIZEOF in D; lia. }
assert (LCE : forall b, In b LBL -> 0 < blk_addr b /\ blk_addr b + blk_size b <= alloc_ceiling).
{ intros b Hb. first [ pose proof (BRL _ Hb) as sfP_; sf_destruct 5%nat sfP_ as B0 _ _ BC _ | sf_fb; destruct (BRL _ Hb) as (B0 & _ & _ & BC & _) ]. unfold alloc_ceiling in BC. lia. }
assert (DDL : (dec_depth low <= 2)%nat) by (rewrite DD4; destruct Hmo as [-> | ->]; cbn; lia).
pose proof (ctl_depth_le low ltac:(lia)) as CDL.
assert (HEAP5 : RHEAP s2' (LBL ++ (blk, S, SBSTATE_SIZEOF) :: LB) m5).
{ eapply RHEAP_frame_proof; [exact HEAP4| exact MU5| exact WM5|]. constructor; [|constructor]. right. right.
exists (blk, S, SBSTATE_SIZEOF). split; [apply in_app_iff; right; left; reflexivity|]. cbn. unfold SBSTATE_SIZEOF. lia. }
assert (AUX5 : rauxv_ok m5 AB).
{ eapply rauxv_ok_frame; [exact AUX4| exact MU5| exact WM5|]. constructor; [|constructor]. cbn [fst snd]. unfold RAUXV_CELL. (clear - DDL DD4 low SIMG SCE S0 S IDL CLOv MDP LO SB lo AB sp mo RCEIL; lia). }
assert (ERR5 : rw_cells rsegs m5 316332 [C4 errv4]) by (eapply rw_cells_transport; [exact ERR4| exact MU5| exact WM5| cbn; lia]).
assert (FR5 : rw_cells rsegs m5 (bv_unsigned sp + -48) (sbinit_frame0 j8 s3 s2 s1 s0 ra)).
{ unfold sbinit_frame0. eapply rw_cells_transport; [exact FR4| exact MU5| exact WM5| cbn; lia]. }
assert (ST5 : stk rsegs m5 lo (bv_unsigned sp + -48)) by (eapply stk_transport_disjoint; [exact ST4| exact MU5| exact WM5| cbn; lia]).
assert (TP5 : rtables_pristine m5).
{ eapply rtables_pristine_munch; [exact TP4| exact MU5|]. intros x Hx. unfold RTABLES_LO, RTABLES_HI in Hx. cbn. split; [lia| exact I]. }
assert (RL5 : forall STEREO, DREP 0 STEREO m5 SL low LBL).
{ intros STEREO. eapply decst_rep_munch; [exact (DREP4 STEREO)| exact MU5| exact WM5|]. intros b x Hb Hx. cbn. split; [| exact I]. pose proof (SAPL _ Hb). lia. }
assert (PRES5 : rheap_pres LB (bv_unsigned sp) m m5).
{ eapply rheap_pres_trans; [exact PRES4|]. eapply rheap_pres_of_munch; [exact MU5| exact WM5|]. intros x Hx CA. apply outside_single.
destruct CA as [CA|[[CA _]|(b & Hb & Hab)]]; [lia| lia|].
destruct (RHEAP_blocks_disjoint_proof _ _ _ (blk, S, SBSTATE_SIZEOF) b HEAP2 ltac:(left; reflexivity) ltac:(right; exact Hb)) as [D|D].
{ intros E. cbn [map] in ND2. apply (proj1 (List.NoDup_cons_iff _ _)) in ND2. destruct ND2 as [NI _]. apply NI. cbn [blk_id fst snd] in E |- *. rewrite E. apply in_map. exact Hb. }
all: unfold in_block in Hab; cbn [blk_addr blk_size fst snd] in D; unfold SBSTATE_SIZEOF in D; lia. }
clear X4 FR4 TP4 PRES4 AUX4 ERR4 ST4 MI4 MU5 WM5 HEAP4.

unfold sbx_cells in X5.
apply (rw_cells_app rsegs m5 S [C8 (Z_to_bv 64 (mode_addr mo)); C8 (Z_to_bv 64 SL); C4 (Z_to_bv 64 (2 * sbm_frameSize mo)); C4 (Z_to_bv 64 (sbm_frameSize mo));
C4 (Z_to_bv 64 (sbm_subframeSize mo)); C4 (Z_to_bv 64 4); C4 (Z_to_bv 64 8); C4 w0]) in X5.
destruct X5 as [XA X5]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in X5.
apply (rw_cells_app rsegs m5 (S + 40) [C4 w0]) in X5. destruct X5 as [XP XB]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in XB.
replace (S + 40 + 4) with (S + 44) in XB by lia.
eapply (implM_evt rsegs).
{ eapply (rctl_all low 0 0 SL LBL CtlGetSamplingRate (S + 40) lo); try reflexivity.
all: first [ exact (RL5 0) | exact I | exact TP5 | exact BRL | exact NDL | exact LAPL | exact MI5 | exact FRM4 | exact CLO
| (cbn [creq_pre]; exists w0; exact XP)
| (rewrite unsigned_lit by lia; exact ST5)
| (cbn [creq_size]; intros b Hb; pose proof (SAPL _ Hb); lia)
| (cbn [creq_ptr_ok]; lia)
| (cbn [creq_size]; rewrite ?unsigned_lit by lia; lia) ]. }
cbv beta. intros ms6 sfH_; first [ sf_destruct 26%nat sfH_ as u0 u1 u2 ua1 ua2 ua3 ua4 ua5 ua6 ua7 u3 u4 u5 u6 F6 fc6 m6 -> MU6 WM6 MI6 FRM6 ST6 RL6 CP6 _ | sf_fb; destruct sfH_ as (u0 & u1 & u2 & ua1 & ua2 & ua3 & ua4 & ua5 & ua6 & ua7 & u3 & u4 & u5 & u6 & F6 & fc6 & m6 & -> & MU6 & WM6 & MI6 & FRM6 & ST6 & RL6 & CP6 & _) ].
rewrite unsigned_lit in MU6 by lia. rewrite unsigned_lit in ST6 by lia. rewrite ret_pc_even by lia.
cbn [creq_post] in CP6. destruct CP6 as [XP6 LRR].

assert (OUTW : forall P' r' x, (S <= x < S + 160 \/ bv_unsigned sp + -48 <= x < bv_unsigned sp \/ x = 316332 \/ (316332 <= x < 316336) \/ (RTABLES_LO <= x < RTABLES_HI)) ->
~ (P' <= x < P' + creq_size r') -> outside (ctlW lo (bv_unsigned sp + -48) P' r' LBL) x).
{ intros P' r' x Hx HP. apply outside_ctlW. split; [| split; [exact HP|]].
- unfold RTABLES_LO, RTABLES_HI in Hx. (clear - Hx CLOv SCE LO IDL SPR; lia).
- intros b Hb. pose proof (SAPL _ Hb) as D. first [ pose proof (BRL _ Hb) as sfP_; sf_destruct 5%nat sfP_ as B0 _ _ BC BW | sf_fb; destruct (BRL _ Hb) as (B0 & _ & _ & BC & BW) ]. unfold alloc_ceiling in BC. unfold RTABLES_LO, RTABLES_HI in Hx. (clear - Hx D BC BW CLOv LO IDL SPR; lia). }
assert (XA6 : rw_cells rsegs m6 S [C8 (Z_to_bv 64 (mode_addr mo)); C8 (Z_to_bv 64 SL); C4 (Z_to_bv 64 (2 * sbm_frameSize mo)); C4 (Z_to_bv 64 (sbm_frameSize mo));
C4 (Z_to_bv 64 (sbm_subframeSize mo)); C4 (Z_to_bv 64 4); C4 (Z_to_bv 64 8); C4 w0]).
{ eapply rw_cells_munch_out; [exact XA| exact MU6| exact WM6|]. cbn [cells_size csize Nat.add]. intros x Hx. apply OUTW; [lia| cbn [creq_size]; lia]. }
assert (XB6 : rw_cells rsegs m6 (S + 44) [C4 w0; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 w0; C4 w0; C4 (Z_to_bv 64 1); CB 4 z4; C8 (Z_to_bv 64 0); C4 w0; CB 4 z4]).
{ eapply rw_cells_munch_out; [exact XB| exact MU6| exact WM6|]. cbn [cells_size csize Nat.add]. intros x Hx. apply OUTW; [lia| cbn [creq_size]; lia]. }
assert (FR6 : rw_cells rsegs m6 (bv_unsigned sp + -48) (sbinit_frame0 j8 s3 s2 s1 s0 ra)).
{ unfold sbinit_frame0. eapply rw_cells_munch_out; [exact FR5| exact MU6| exact WM6|]. cbn [cells_size csize Nat.add]. intros x Hx. apply OUTW; [lia| cbn [creq_size]; lia]. }
assert (ERR6 : rw_cells rsegs m6 316332 [C4 errv4]).
{ eapply rw_cells_munch_out; [exact ERR5| exact MU6| exact WM6|]. cbn [cells_size csize Nat.add]. intros x Hx. apply OUTW; [lia| cbn [creq_size]; lia]. }
assert (TP6 : rtables_pristine m6).
{ eapply rtables_pristine_munch; [exact TP5| exact MU6|]. intros x Hx. apply OUTW; [lia| cbn [creq_size]; unfold RTABLES_LO, RTABLES_HI in Hx; lia]. }
assert (WOK : forall P' r', (S <= P' /\ P' + creq_size r' <= S + 160 \/ bv_unsigned sp + -48 <= P' /\ P' + creq_size r' <= bv_unsigned sp) ->
Forall (rclient_write_ok (LBL ++ (blk, S, SBSTATE_SIZEOF) :: LB)) (ctlW lo (bv_unsigned sp + -48) P' r' LBL)
/\ Forall (fun iv : Z * Z => snd iv <= AB /\ (snd iv <= RAUXV_CELL \/ RAUXV_CELL + 8 <= fst iv)) (ctlW lo (bv_unsigned sp + -48) P' r' LBL)
/\ (forall x, 0 <= x < 2^64 -> rclient_addr LB (bv_unsigned sp) x -> outside (ctlW lo (bv_unsigned sp + -48) P' r' LBL) x)).
{ intros P' r' HP. unfold ctlW. split; [|split].
- apply Forall_cons; [left; cbn; (clear - CLO; lia)|]. apply Forall_app. split.
+ destruct r'; cbn [creq_ivs creq_size] in HP |- *; try (apply Forall_nil); apply Forall_cons; try apply Forall_nil; cbn [fst snd].
all: destruct HP as [HP|HP]; [right; right; exists (blk, S, SBSTATE_SIZEOF); split; [apply in_app_iff; right; left; reflexivity| cbn; unfold SBSTATE_SIZEOF; (clear - HP; lia)] | left; cbn [fst snd]; unfold alloc_ceiling; (clear - HP CLOv LO IDL; lia)].
+ apply Forall_forall. intros iv Hiv. unfold blocks_ivs in Hiv. apply in_map_iff in Hiv. destruct Hiv as (b & <- & Hb). right. right. exists b. split; [apply in_app_iff; left; exact Hb| cbn [fst snd]; (clear - Hb; lia)].
- apply Forall_cons; [cbn; unfold RAUXV_CELL; (clear - SB CLOv; lia)|]. apply Forall_app. split.
+ destruct r'; cbn [creq_ivs creq_size] in HP |- *; try (apply Forall_nil); apply Forall_cons; try apply Forall_nil; cbn [fst snd]; unfold RAUXV_CELL; (clear - HP SCE SIMG SB LO IDL CLOv SPR; lia).
+ apply Forall_forall. intros iv Hiv. unfold blocks_ivs in Hiv. apply in_map_iff in Hiv. destruct Hiv as (b & <- & Hb). cbn [fst snd].
first [ pose proof (BRL _ Hb) as sfP_; sf_destruct 5%nat sfP_ as B0 _ _ BC BW | sf_fb; destruct (BRL _ Hb) as (B0 & _ & _ & BC & BW) ]. unfold alloc_ceiling in BC. unfold RAUXV_CELL. (clear - BC BW CLOv LO IDL SB SPR; lia).
- intros x Hx CA. apply outside_ctlW. unfold rclient_addr, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in CA.
split; [| split].
+ destruct CA as [CA|[CA|(b' & Hb' & Hab')]]; [(clear - CA; lia)| (clear - CA CLOv; lia)|]. first [ pose proof (RHEAP_block_range_proof _ _ _ _ HEAP2 ltac:(right; exact Hb')) as sfP_; sf_destruct 5%nat sfP_ as _ _ _ BC' _ | sf_fb; destruct (RHEAP_block_range_proof _ _ _ _ HEAP2 ltac:(right; exact Hb')) as (_ & _ & _ & BC' & _) ]. unfold alloc_ceiling in BC'. unfold in_block in Hab'. (clear - Hab' BC' CLOv; lia).
+ intros HPx. destruct CA as [CA|[CA|(b' & Hb' & Hab')]]; [(clear - CA HPx HP SCE CLOv LO IDL SPR; lia)| destruct HP as [HP|HP]; (clear - CA HPx HP SIMG SCE CLOv LO IDL SPR; lia)|]. unfold in_block in Hab'.
destruct HP as [HP|HP].
* destruct (RHEAP_blocks_disjoint_proof _ _ _ (blk, S, SBSTATE_SIZEOF) b' HEAP2 ltac:(left; reflexivity) ltac:(right; exact Hb')) as [D|D].
{ intros E. cbn [map] in ND2. apply (proj1 (List.NoDup_cons_iff _ _)) in ND2. destruct ND2 as [NI _]. apply NI. cbn [blk_id fst snd] in E |- *. rewrite E. apply in_map. exact Hb'. }
all: cbn [blk_addr blk_size fst snd] in D; unfold SBSTATE_SIZEOF in D; (clear - D Hab' HPx HP; lia).
* first [ pose proof (RHEAP_block_range_proof _ _ _ _ HEAP2 ltac:(right; exact Hb')) as sfP_; sf_destruct 5%nat sfP_ as _ _ _ BC' _ | sf_fb; destruct (RHEAP_block_range_proof _ _ _ _ HEAP2 ltac:(right; exact Hb')) as (_ & _ & _ & BC' & _) ]. unfold alloc_ceiling in BC'. (clear - HP Hab' BC' HPx CLOv LO IDL SPR; lia).
+ intros b Hb Hbx. destruct CA as [CA|[CA|(b' & Hb' & Hab')]].
* first [ pose proof (BRL _ Hb) as sfP_; sf_destruct 5%nat sfP_ as _ _ _ BC _ | sf_fb; destruct (BRL _ Hb) as (_ & _ & _ & BC & _) ]. unfold alloc_ceiling in BC. (clear - CA Hbx BC CLOv LO IDL SPR; lia).
* first [ pose proof (BRL _ Hb) as sfP_; sf_destruct 5%nat sfP_ as _ _ _ _ BW | sf_fb; destruct (BRL _ Hb) as (_ & _ & _ & _ & BW) ]. (clear - CA Hbx BW; lia).
* unfold in_block in Hab'. destruct (RHEAP_blocks_disjoint_proof _ _ _ b b' HEAP5 ltac:(apply in_app_iff; left; exact Hb) ltac:(apply in_app_iff; right; right; exact Hb')) as [D|D]; [| (clear - D Hbx Hab'; lia)| (clear - D Hbx Hab'; lia)].
intros E. pose proof (RHEAP_blocks_nodup_proof _ _ _ HEAP5) as ND5. rewrite map_app in ND5.
eapply (NoDup_app_in_neq _ _ _ _ ND5); [apply in_map; exact Hb| right; apply in_map; exact Hb'| exact E]. }
destruct (WOK (S + 40) CtlGetSamplingRate ltac:(cbn [creq_size]; left; lia)) as (W1a & W1b & W1c).
assert (HEAP6 : RHEAP s2' (LBL ++ (blk, S, SBSTATE_SIZEOF) :: LB) m6) by (eapply RHEAP_frame_proof; [exact HEAP5| exact MU6| exact WM6| exact W1a]).
assert (AUX6 : rauxv_ok m6 AB) by (eapply rauxv_ok_frame; [exact AUX5| exact MU6| exact WM6| exact W1b]).
assert (PRES6 : rheap_pres LB (bv_unsigned sp) m m6).
{ eapply rheap_pres_trans; [exact PRES5|]. eapply rheap_pres_of_munch; [exact MU6| exact WM6| exact W1c]. }
clear XA XP XB FR5 ERR5 TP5 AUX5 PRES5 MU6 WM6 HEAP5 MI5 ST5.

change (implM rsegs (sb_init_rest2 mo blk low) s2' (rinit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB AB lo mo m)
(MS (mkR (Z_to_bv 64 189716) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp u0 u1 u2 (Z_to_bv 64 S) (Z_to_bv 64 (mode_addr mo)) (Z_to_bv 64 0) ua1 ua2 ua3 ua4 ua5 ua6 ua7
(Z_to_bv 64 (sbmode_addr mo)) s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6) F6 (Z_to_bv 64 189716) fc6 None m6 (seg_rom rsegs))).
apply (KONT blk S low LBL). unfold sb_at40. sf_eexists 14%nat. first [ unshelve sf_eexists 7%nat; [ exact (F6) | exact (fc6) | exact (m6) | exact (errv4) | exact (j8) | exact (SL) | exact ((fst (speex_decoder_ctl low CtlGetSamplingRate))) | ] | sf_fb; exists F6, fc6, m6, errv4, j8, SL, (fst (speex_decoder_ctl low CtlGetSamplingRate)) ].
split; [reflexivity|]. split; [exact FRM6|]. split; [exact MI6|]. split; [exact ST6|]. split; [exact FR6|].
split; [rewrite ETP; unfold RERRNO; exact ERR6|]. split; [exact AUX6|]. split; [exact PRES6|]. split; [rewrite PSO4; exact PSO|]. split; [exact TP6|].
split; [exact HEAP6|]. split; [exact BR|]. split; [exact SLB|]. split; [exact XA6|]. split; [exact XP6|]. split; [exact LRR|]. split; [reflexivity|].
split; [exact XB6|].
split; [intros STEREO; eapply decst_rep_stereo_any; [apply (ctl_stereo_off low CtlGetSamplingRate I STO4)| exact RL6]|].
split; [exact DM4|]. split; [exact DD4|]. split; [exact RATE4|]. split; [exact STO4|]. split; [exact NES4| exact SP16].
Qed.
