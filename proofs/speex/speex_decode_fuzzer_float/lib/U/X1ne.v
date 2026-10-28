(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bu X1cf X1cc X1bj X1bs X1c2 X1br X1bq.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0px X0qn X0qp X0pw.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1m2 X1m3 X1m5 X1m6 X1ec. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk X1n7. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1h7 X1go X1hk X1ho X1n8.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require X1ff.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1ra X1qu X1qx X1r3 X1r4 X1nt X1rh X1re.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.

Lemma rtables_pristine_rheap : forall LB SP m m',
rtables_pristine m -> rheap_pres LB SP m m' -> rtables_pristine m'.
Proof.
intros LB SP m m' TP HP a Ha. pose proof (bv_unsigned_in_range 64 a) as R. change (bv_modulus 64) with (2^64) in R.
destruct (HP (bv_unsigned a) ltac:(lia)) as [E _].
{ right. left. unfold RTABLES_LO, RTABLES_HI in Ha. unfold ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP. lia. }
rewrite wa_unsigned_id in E. rewrite E. apply TP. exact Ha.
Qed.

Fixpoint dec_stereo_off (d : dec_state bptr) : Prop :=
match d with DecNB st => nb_stereo_cb st = false | DecSB _ low => dec_stereo_off low end.

Lemma cbs_cells_nostereo : forall k f d f' d' js, cbs_cells k f d false js = cbs_cells k f' d' false js.
Proof. induction k as [|k IH]; intros f d f' d' js; [reflexivity|]. destruct js as [|j js]; [reflexivity|]. cbn [cbs_cells]. rewrite andb_false_r. f_equal. apply IH. Qed.

Lemma decst_rep_stereo_any : forall d OUT ST1 ST2 m S L,
dec_stereo_off d -> DREP OUT ST1 m S d L -> DREP OUT ST2 m S d L.
Proof.
induction d as [st|sb low IH]; intros OUT ST1 ST2 m S L SO R; cbn [decst_rep] in R |- *.
- destruct R as [EL (AL & POS & INV & j & JOK & CBS & X)]. split; [exact EL|]. split; [exact AL|]. split; [exact POS|]. split; [exact INV|].
exists j. split; [exact JOK|]. cbn in SO. rewrite SO in CBS |- *. split; [| exact X].
first [ sf_destruct 4%nat CBS as js L16 FA E | sf_fb; destruct CBS as (js & L16 & FA & E) ]. exists js. split; [exact L16|]. split; [exact FA|]. rewrite E. rewrite (cbs_cells_nostereo 16 A_speex_std_stereo_request_handler ST1 A_speex_std_stereo_request_handler ST2). reflexivity.
- first [ sf_destruct 12%nat R as a j LBL EL AL POS INV JOK X BU OUTL RL | sf_fb; destruct R as (a & j & LBL & EL & AL & POS & INV & JOK & X & BU & OUTL & RL) ]. first [ unshelve sf_eexists 3%nat; [ exact (a) | exact (j) | exact (LBL) | ] | sf_fb; exists a, j, LBL ].
repeat (split; [assumption|]). exists OUTL. eapply IH; [exact SO| exact RL].
Qed.

Lemma ctl_stereo_off : forall (d : dec_state bptr) r,
match r with CtlSetHandlerStereo => False | _ => True end -> dec_stereo_off d -> dec_stereo_off (snd (speex_decoder_ctl d r)).
Proof.
induction d as [st|sb low IH]; intros r Hr SO.
- destruct r; cbn in *; try exact SO. destruct Hr.
- cbn in SO. destruct r; cbn [speex_decoder_ctl]; try (destruct Hr); try exact SO.
all: match goal with |- context [speex_decoder_ctl ?lw ?q] =>
first [ pose proof (IH q I SO) as IH2 | pose proof (IH q Hr SO) as IH2 ];
destruct (speex_decoder_ctl lw q) as [vv ll]; cbn [snd dec_stereo_off] in IH2 |- *; exact IH2 end.
Qed.

Lemma ctl_mode_same : forall (d : dec_state bptr) r, dec_mode (snd (speex_decoder_ctl d r)) = dec_mode d.
Proof.
induction d as [st|sb low IH]; intros r; [destruct r; reflexivity|].
destruct r; cbn [speex_decoder_ctl]; try reflexivity.
all: match goal with |- context [speex_decoder_ctl ?lw ?q] => destruct (speex_decoder_ctl lw q) as [vv ll]; reflexivity end.
Qed.

Definition init_depth (mo : spx_mode) : Z := match mo with ModeNB => 8272 | ModeWB => 8320 | ModeUWB => 8368 end.
Definition mode_depth (mo : spx_mode) : nat := match mo with ModeNB => 1%nat | ModeWB => 2%nat | ModeUWB => 3%nat end.

Definition init_rate (mo : spx_mode) : Z := match mo with ModeNB => 8000 | ModeWB => 16000 | ModeUWB => 32000 end.

Definition rinit_post {RCEIL : RunCeiling} (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(s : PState) (LB : list block) (AB lo : Z) (mo : spx_mode) (m : mem)
(r : option (dec_state bptr)) (s' : PState) : machine_state -> Prop :=
fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (errv' : word),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (ret_pc ra) fc' None m' (seg_rom rsegs)
/\ frm0 fc'
/\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
/\ rw_cells rsegs m' (errno_addr tp) [C4 errv']
/\ rauxv_ok m' AB
/\ rheap_pres LB (bv_unsigned sp) m m'
/\ ps_so s' = ps_so s
/\ match r with
| None => a0 = Z_to_bv 64 0 /\ RHEAP s' LB m'
| Some d => exists S LBD, a0 = Z_to_bv 64 S /\ 0 < S < 2^63 /\ RHEAP s' (LBD ++ LB) m'
/\ (forall STEREO, DREP 0 STEREO m' S d LBD)
/\ List.NoDup (map blk_id (LBD ++ LB))
/\ dec_mode d = mo /\ top_isave_none d /\ dec_depth d = mode_depth mo
/\ fst (speex_decoder_ctl d CtlGetSamplingRate) = init_rate mo /\ dec_stereo_off d /\ dec_nestedR d
end.

Definition rinit_at {RCEIL : RunCeiling} (mo : spx_mode) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(s : PState) (LB : list block) (AB lo : Z) (errv : word),
RHEAP s LB m -> rtables_pristine m ->
rauxv_ok m AB -> bv_unsigned sp <= AB ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - init_depth mo ->
rw_cells rsegs m (errno_addr tp) [C4 errv] ->
mem_inv rsegs m -> frm0 fc -> tp = Z_to_bv 64 RATP ->
a0 = Z_to_bv 64 (mode_addr mo) ->
bv_unsigned sp mod 16 = 0 ->
implM rsegs (speex_decoder_init raw_calloc raw_free mo) s
(rinit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB AB lo mo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_speex_decoder_init) fc None m (seg_rom rsegs)).

Definition z8 : list byte := repeat (Z_to_bv 8 0) 8.
Definition z16 : list byte := repeat (Z_to_bv 8 0) 16.
Definition zw (n : nat) : list word := repeat (Z_to_bv 64 0) n.
Definition zcbs : list byte := repeat (Z_to_bv 8 0) 640.
Definition zjunk : nb_junk :=
NBJ (Z_to_bv 64 0) (zw 500) 0 (zw 10) (zw 10) (zw 10) (zw 2) (zw 4) (zw 3) (Z_to_bv 64 40) (Z_to_bv 64 0) (zw 3)
(Z_to_bv 64 1000) (repeat (Z_to_bv 8 0) 4) zcbs (z8, z16) (zw 3) (repeat (Z_to_bv 8 0) 4).

Lemma zjunk_ok : nb_junk_ok zjunk.
Proof. repeat split; reflexivity. Qed.

Lemma zjunk_cbs : forall SH SD, cbs_ok SH SD false (j_cbs zjunk).
Proof.
intros SH SD. exists (repeat (z8, z16) 16).
split; [reflexivity|]. split; [repeat constructor|].
apply byte_list_eq. vm_compute. reflexivity.
Qed.

Lemma nb_init_inv : forall blk : bptr, nb_inv (nb_init_state blk).
Proof. intros blk. unfold nb_inv. cbn. unfold NB_DEFAULT_SUBMODE. repeat split; try lia. Qed.

Definition cb_zero : list cell := [CB 8 z8; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); CB 16 z16].
Fixpoint cbs_zero (n : nat) : list cell := match n with O => [] | S n' => cb_zero ++ cbs_zero n' end.
Definition nb_zero_cells : list cell :=
[C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
++ [CB 1216 (repeat (Z_to_bv 8 0) 1216)]
++ [CB 956 (repeat (Z_to_bv 8 0) 956)]
++ [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ++ [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ++ [C4 (Z_to_bv 64 0)] ++ [C4 (Z_to_bv 64 0)]
++ [C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)]
++ cbs_zero 16
++ cb_zero
++ [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ++ [C4 (Z_to_bv 64 0)] ++ [CB 4 (repeat (Z_to_bv 8 0) 4)].

Lemma nb_zero_cells_bytes : cells_bytes nb_zero_cells = repeat (Z_to_bv 8 0) 2968.
Proof. vm_compute. reflexivity. Qed.
Lemma nb_zero_cells_wf : cells_wf nb_zero_cells.
Proof. cbn. repeat split; reflexivity. Qed.
Lemma nb_zero_cells_size : cells_size nb_zero_cells = 2968%nat.
Proof. reflexivity. Qed.

Lemma zero_blob_recast : forall m A,
rw_cells rsegs m A [CB 2968 (repeat (Z_to_bv 8 0) 2968)] -> rw_cells rsegs m A nb_zero_cells.
Proof.
intros m A X. apply (X0pw.rw_cells_recast rsegs m A [CB 2968 (repeat (Z_to_bv 8 0) 2968)] nb_zero_cells X).
- exact nb_zero_cells_wf.
- cbn [cells_bytes cbytes app]. rewrite app_nil_r. exact nb_zero_cells_bytes.
- rewrite nb_zero_cells_size. reflexivity.
Qed.

Lemma rw_cells_join : forall m A B cs1 cs2,
rw_cells rsegs m A cs1 -> rw_cells rsegs m B cs2 -> B = A + Z.of_nat (cells_size cs1) -> rw_cells rsegs m A (cs1 ++ cs2).
Proof. intros m A B cs1 cs2 X Y ->. apply (proj2 (rw_cells_app _ _ _ _ _)). split; assumption. Qed.
Lemma cells_wf_f32 : forall l, cells_wf (f32 l).
Proof. induction l as [|x l IH]; [exact I|]. rewrite f32_cons. split; [exact I| exact IH]. Qed.

Definition nb_mid_cells : list cell :=
f32 (zw 500) ++ [C8 (Z_to_bv 64 0)] ++ f32 (zw 10) ++ f32 (zw 10) ++ f32 (zw 10) ++ f32 (zw 2) ++ f32 (zw 4) ++ [C8 (Z_to_bv 64 0)] ++ f32 (zw 3).
Lemma nb_mid_recast : forall m A, rw_cells rsegs m A ([CB 1216 (repeat (Z_to_bv 8 0) 1216)] ++ [CB 956 (repeat (Z_to_bv 8 0) 956)]) -> rw_cells rsegs m A nb_mid_cells.
Proof.
intros m A X. apply (X0pw.rw_cells_recast rsegs m A _ nb_mid_cells X).
- unfold nb_mid_cells. repeat (apply (proj2 (cells_wf_app _ _)); split); first [apply cells_wf_f32 | (cbn; tauto)].
- vm_compute. reflexivity.
- vm_compute. reflexivity.
Qed.
Lemma nb_tailblk_recast : forall m A,
rw_cells rsegs m A ([C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ++ [C4 (Z_to_bv 64 1)] ++ [CB 4 (repeat (Z_to_bv 8 0) 4)]) ->
rw_cells rsegs m A (f32 (zw 3) ++ [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 1); CB 4 (repeat (Z_to_bv 8 0) 4)]).
Proof.
intros m A X. apply (X0pw.rw_cells_recast rsegs m A _ _ X); [cbn; tauto| vm_compute; reflexivity| reflexivity].
Qed.
Lemma nb_b3_recast : forall m A, rw_cells rsegs m A [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] -> rw_cells rsegs m A (f32 (zw 3)).
Proof. intros m A X. exact X. Qed.
Lemma nb_b45_join : forall m A, rw_cells rsegs m A ([C4 (Z_to_bv 64 0)] ++ [C4 (Z_to_bv 64 0)]) -> rw_cells rsegs m A [C8 (Z_to_bv 64 0)].
Proof. intros m A X. apply (X0pw.rw_cells_recast rsegs m A _ _ X); [cbn; tauto| vm_compute; reflexivity| reflexivity]. Qed.
Lemma nb_b45_split : forall m A, rw_cells rsegs m A [C8 (Z_to_bv 64 4294967296000)] ->
rw_cells rsegs m A ([C4 (Z_to_bv 64 0)] ++ [C4 (Z_to_bv 64 1000)]).
Proof. intros m A X. apply (X0pw.rw_cells_recast rsegs m A _ _ X); [cbn; tauto| apply byte_list_eq; vm_compute; reflexivity| reflexivity]. Qed.

Lemma nb_hdr_recast : forall m A md,
rw_cells rsegs m A [C8 md; C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 8000); C8 (Z_to_bv 64 0)] ->
rw_cells rsegs m A [C8 md; C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 8000); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].
Proof.
intros m A md X. apply (X0pw.rw_cells_recast rsegs m A _ _ X); [cbn; tauto| | reflexivity].
cbn [cells_bytes cbytes]. f_equal; try (f_equal; f_equal; apply byte_list_eq; vm_compute; reflexivity).
Qed.
Lemma nb_cbs_recast : forall m A, rw_cells rsegs m A (cbs_zero 16) -> rw_cells rsegs m A [CB 640 zcbs].
Proof.
intros m A X. apply (X0pw.rw_cells_recast rsegs m A _ _ X); [cbn; split; [reflexivity| exact I]| vm_compute; reflexivity| reflexivity].
Qed.

Ltac fixaddr H A v := lazymatch type of H with rw_cells _ _ ?ad _ => replace ad with (A + v) in H by lia end.
Ltac fixaddr2 H A v := lazymatch type of H with rw_cells _ _ ?ad _ => replace ad with (A + v) in H
by (unfold zw; rewrite ?cells_size_app; repeat rewrite cells_size_f32; repeat rewrite repeat_length;
cbn [cells_size csize length Nat.add Nat.mul]; lia) end.

Theorem rinit_nb {RCEIL : RunCeiling} : rinit_at ModeNB.
Proof.
intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB AB lo errv
HEAP TP AUX SB ST CLO LO ERR MI FRM TPE -> SP16.
cbn [init_depth] in LO. cbn [mode_addr]. change A_speex_nb_mode with NB_MODE_PTR.
assert (ENB : NB_MODE_PTR = 0x3b7c8) by reflexivity.
pose proof CLO as CLOv. unfold alloc_ceiling in CLOv.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
assert (ETP : errno_addr tp = RERRNO) by (rewrite TPE; unfold RATP, RERRNO; rewrite unsigned_lit by lia; reflexivity).
rewrite ETP in ERR. unfold RERRNO in ERR.
pose proof (nb_desc_of_pristine m TP) as ND. unfold nb_desc_cells in ND.

cbn [speex_decoder_init nb_decoder_init_d].
eapply (implM_bind rsegs _ _ _ (fun r s' ms' => rinit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB AB lo ModeNB m (option_map DecNB r) s' ms')).
2:{ intros r s' ms' H. apply implM_ret. apply evt_done. exact H. }
cbn [nb_decoder_init].

pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU0. pose proof (wmono_refl rsegs m) as WM0.
carve_frame 48%nat ST.
eapply (implM_bind rsegs _ _ _ (fun r s' ms' => exists m1,
rcalloc_post (Z_to_bv 64 0x203c0) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp s0 (Z_to_bv 64 NB_MODE_PTR) s2 s3
(Z_to_bv 64 0x3b6f8) s5 s6 s7 s8 s9 s10 s11 F fc s LB (1 * 2968) lo AB m1 r s' ms'
/\ rw_cells rsegs m1 (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
/\ munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m1 /\ wmono rsegs m m1)).
{ eapply (implM_evt rsegs _ _ _ (fun ms1 => exists m1,
ms1 = MS (mkR (Z_to_bv 64 0x203c0) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 (Z_to_bv 64 A_nb_decoder_init) t2 s0 (Z_to_bv 64 NB_MODE_PTR)
(Z_to_bv 64 2968) (Z_to_bv 64 1) a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 0x3b6f8) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 RCALLOC_SYM) fc None m1 (seg_rom rsegs)
/\ rw_cells rsegs m1 (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
/\ munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1 /\ stk rsegs m1 lo (bv_unsigned sp + -48))).
{ unfold A_speex_decoder_init. step. if_false_z. step. step. if_false_z. step. step.
step. step. step. step. step. step. step. step. if_false_z. step. step. step. if_false_z. step. step. step. step. step.
apply evt_done. eexists. split; [reflexivity|]. split; [eassumption|]. split; [exact MU0|]. split; [exact WM0|]. split; assumption. }
clear MU0 WM0. cbv beta. intros ms1 sfH_; first [ sf_destruct 7%nat sfH_ as m1 -> FRa MU1 WM1 MI1 ST1 | sf_fb; destruct sfH_ as (m1 & -> & FRa & MU1 & WM1 & MI1 & ST1) ].
assert (HEAP1 : RHEAP s LB m1).
{ eapply RHEAP_frame_proof; [exact HEAP| exact MU1| exact WM1|]. constructor; [|constructor]. left. cbn [fst]. lia. }
assert (AUX1 : rauxv_ok m1 AB).
{ eapply rauxv_ok_frame; [exact AUX| exact MU1| exact WM1|]. constructor; [|constructor]. cbn [fst snd]. unfold RAUXV_CELL. lia. }
assert (ERR1 : rw_cells rsegs m1 316332 [C4 errv]).
{ eapply rw_cells_transport; [exact ERR| exact MU1| exact WM1|]. cbn. split; [lia| exact I]. }
eapply implM_mono.
{ eapply (rcalloc_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 s LB 2968 1 lo AB errv HEAP1 AUX1);
[rewrite unsigned_lit by lia; lia| rewrite unsigned_lit by lia; exact ST1| exact CLO| rewrite unsigned_lit by lia; unfold RCALLOC_STACK; lia
| rewrite ETP; unfold RERRNO; exact ERR1| exact MI1| exact TPE| reflexivity| reflexivity| lia| lia| unfold RSMALL_MAX; lia]. }
cbv beta. intros r s' ms' H. exists m1. exact (conj H (conj FRa (conj MU1 WM1))). }
cbv beta. intros r s' ms' sfH_; first [ sf_destruct 5%nat sfH_ as m1 POST FR0 MU1 WM1 | sf_fb; destruct sfH_ as (m1 & POST & FR0 & MU1 & WM1) ].
first [ sf_destruct 26%nat POST as w0 w1 w2 ra0 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 m2 errv2 -> MI2 ST2 ERR2 AUX2 HP2 PSF PSO RES | sf_fb; destruct POST as (w0 & w1 & w2 & ra0 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & m2 & errv2 & -> & MI2 & ST2 & ERR2 & AUX2 & HP2 & PSF & PSO & RES) ].
rewrite unsigned_lit in ST2 by lia. rewrite unsigned_lit in HP2 by lia. rewrite ret_pc_even by lia. rewrite ETP in ERR2. unfold RERRNO in ERR2.
change (mem_inv rsegs m2) in MI2. change (stk rsegs m2 lo (bv_unsigned sp + -48)) in ST2. change (rw_cells rsegs m2 316332 [C4 errv2]) in ERR2.
assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) by (eapply rheap_pres_rw_cells; [exact HP2| exact FR0| left; cbn; lia]).
assert (PRES2 : rheap_pres LB (bv_unsigned sp) m m2).
{ eapply rheap_pres_trans; [| eapply rheap_pres_weaken; [exact HP2| lia| auto]].
eapply rheap_pres_of_munch; [exact MU1| exact WM1|]. intros x Hx CA. apply outside_single.
destruct CA as [CA|[[CA _]|(b & Hb & Hab)]]; [lia| lia|].
pose proof (RHEAP_block_range_proof _ _ _ b HEAP Hb) as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ _ BC _ | sf_fb; destruct sfP_ as (_ & _ & _ & BC & _) ]. unfold alloc_ceiling in BC. unfold in_block in Hab. lia. }
assert (TP2 : rtables_pristine m2) by (eapply rtables_pristine_rheap; [exact TP| exact PRES2]).
pose proof (nb_mode_of_pristine m2 TP2) as NM. unfold nb_mode_cells, A_nb_mode in NM.
pose proof (got_user_handler_of_pristine m2 TP2) as GU. unfold GOT_default_user_handler in GU.
clear FR0 HEAP ND.
destruct r as [p|].
-
first [ sf_destruct 7%nat RES as A -> BR HEAP2 BLK _ _ | sf_fb; destruct RES as (A & -> & BR & HEAP2 & BLK & _ & _) ]. change (Z.to_nat (1 * 2968)) with 2968%nat in BLK.
pose proof BR as sfP_; first [ sf_destruct 5%nat sfP_ as A0 A16 _ ACE AIMG | sf_fb; destruct sfP_ as (A0 & A16 & _ & ACE & AIMG) ]. unfold alloc_ceiling in ACE.
apply zero_blob_recast in BLK. unfold nb_zero_cells in BLK.

apply rw_cells_app in BLK. destruct BLK as [B0 BLK]. cbn [cells_size csize Nat.add] in BLK.
apply rw_cells_app in BLK. destruct BLK as [B1 BLK]. cbn [cells_size csize Nat.add] in BLK.
apply rw_cells_app in BLK. destruct BLK as [B1b BLK]. cbn [cells_size csize Nat.add] in BLK.
apply rw_cells_app in BLK. destruct BLK as [B2 BLK]. cbn [cells_size csize Nat.add] in BLK.
apply rw_cells_app in BLK. destruct BLK as [B3 BLK]. cbn [cells_size csize Nat.add] in BLK.
apply rw_cells_app in BLK. destruct BLK as [B4 BLK]. cbn [cells_size csize Nat.add] in BLK.
apply rw_cells_app in BLK. destruct BLK as [B5 BLK]. cbn [cells_size csize Nat.add] in BLK.
apply rw_cells_app in BLK. destruct BLK as [B6 BLK]. cbn [cells_size csize Nat.add] in BLK.
apply rw_cells_app in BLK. destruct BLK as [B7 BLK]. replace (cells_size (cbs_zero 16)) with 640%nat in BLK by reflexivity.
apply rw_cells_app in BLK. destruct BLK as [B8 BLK]. replace (Z.of_nat (cells_size cb_zero)) with 40 in BLK by reflexivity.
apply rw_cells_app in BLK. destruct BLK as [B9 BLK]. cbn [cells_size csize Nat.add] in BLK.
apply rw_cells_app in BLK. destruct BLK as [B10 B11]. cbn [cells_size csize Nat.add] in B11.
change (Z.of_nat 32) with 32 in *. change (Z.of_nat 1216) with 1216 in *. change (Z.of_nat 956) with 956 in *. change (Z.of_nat 8) with 8 in *. change (Z.of_nat 12) with 12 in *.
change (Z.of_nat 4) with 4 in *. change (Z.of_nat 24) with 24 in *. change (Z.of_nat 40) with 40 in *.
fixaddr B1b A 1248. fixaddr B2 A 2204. fixaddr B3 A 2212. fixaddr B4 A 2224. fixaddr B5 A 2228. fixaddr B6 A 2232. fixaddr B7 A 2256.
fixaddr B8 A 2896. fixaddr B9 A 2936. fixaddr B10 A 2960. fixaddr B11 A 2964.
cbn [cbs_zero cb_zero app] in B7. unfold cb_zero in B8.
pose proof (rw_cells_join _ _ _ _ _ B4 B5 ltac:(cbn; lia)) as B45. clear B4 B5. apply nb_b45_join in B45.
clear MU1 WM1 HP2.
apply implM_ret.
pose proof (munch_refl [(A, A + 2968)] m2) as MU. pose proof (wmono_refl rsegs m2) as WM.

step. step. if_cases K0; [exfalso; zify_cond K0; rewrite ?unsigned_lit in K0 by lia; lia|].
step. step. if_false_z.
lstep. lstep. lstep. lstep. lstep. lstep. lstep.
step. if_false_z. step. step. if_false_z.
lstep. rewrite ?unsigned_lit by lia. lstep. lstep. lstep. lstep. lstep. lstep. lstep. lstep. lstep.

eapply evt_cut.
{ lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
eapply (X1ff.memset_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mx (repeat (Z_to_bv 8 0) 1216)) end;
[| assumption].
rewrite !unsigned_lit by lia. change (Z.to_nat 1216) with 1216%nat. change X1ff.rsegs with rsegs. exact B1. }
cbv beta. intros ms4 sfH_; first [ sf_destruct 20%nat sfH_ as u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 m3 -> MU4 WM4 MI3 B1' | sf_fb; destruct sfH_ as (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & m3 & -> & MU4 & WM4 & MI3 & B1') ].
rewrite !unsigned_lit in MU4, B1' by lia. rewrite (unsigned_lit 0) in B1' by lia. change (0 mod 256) with 0 in B1'. change (Z.to_nat 1216) with 1216%nat in B1'.
change X1ff.rsegs with rsegs in *.
rewrite ret_pc_even by lia.
clear B1.
lazymatch type of MU4 with munch _ ?mx m3 => transport_after_call rsegs mx m3 MU4 WM4; clear MU4 WM4;
try match goal with H : mem_inv rsegs mx |- _ => clear H end; try clear mx end.

lstep. lstep. lstep. lstep. lstep. lstep. if_false_z.
lstep. lstep. lstep. if_false_z.
lstep. lstep. lstep. lstep. lstep. lstep. lstep. rewrite ?unsigned_lit by lia.
lstep. lstep. lstep. lstep. lstep. lstep. lstep. lstep. lstep. lstep.
lstep. cond_prep. rewrite ?zb_lxor_ones by lia. if_false_x.

do 15 (lstep; lstep; lstep; lstep; if_cases KL; [| exfalso; zify_cond KL; rewrite ?unsigned_lit in KL by lia; lia]; clear KL;
lstep; cond_prep; rewrite ?zb_lxor_ones by lia; if_false_x).
lstep. lstep. lstep. lstep. if_cases KL; [exfalso; zify_cond KL; rewrite ?unsigned_lit in KL by lia; lia|]. clear KL.

lstep. lstep. lstep. lstep. lstep.

lstep. lstep. lstep. lstep. lstep. lstep. lstep. lstep. lstep.
match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => set (mF := mx) in *; clearbody mF end.
first [ match goal with H : stk rsegs mF lo _ |- _ => rename H into STF end
| match goal with H : stk rsegs _ lo _ |- _ => assert (STF : stk rsegs mF lo (bv_unsigned sp + -48)) by (eapply stk_transport_disjoint; [exact H| exact MU| exact WM| cbn; lia]); clear H end ].
match goal with H : mem_inv rsegs mF |- _ => rename H into MIF end.
first [ match type of FR2 with rw_cells _ mF _ _ => idtac end
| eapply rw_cells_transport in FR2; [| exact MU| exact WM| cbn; lia] ].
first [ match type of ERR2 with rw_cells _ mF _ _ => idtac end
| eapply rw_cells_transport in ERR2; [| exact MU| exact WM| cbn; lia] ].
release_frame FR2 STF (bv_unsigned sp).
pose proof (RHEAP_blocks_nodup_proof _ _ _ HEAP2) as ND2.
assert (HEAPF : RHEAP s' ((p, A, 2968) :: LB) mF).
{ eapply RHEAP_frame_proof; [exact HEAP2| exact MU| exact WM|]. constructor; [|constructor]. right. right.
exists (p, A, 2968). split; [left; reflexivity|]. cbn. lia. }
assert (AUXF : rauxv_ok mF AB).
{ eapply rauxv_ok_frame; [exact AUX2| exact MU| exact WM|]. constructor; [|constructor]. cbn [fst snd]. unfold RAUXV_CELL. lia. }
assert (PRESF : rheap_pres LB (bv_unsigned sp) m mF).
{ eapply rheap_pres_trans; [exact PRES2|]. eapply rheap_pres_of_munch; [exact MU| exact WM|]. intros x Hx CA. apply outside_single.
destruct CA as [CA|[[CA _]|(b & Hb & Hab)]]; [lia| lia|].
destruct (RHEAP_blocks_disjoint_proof _ _ _ (p, A, 2968) b HEAP2 ltac:(left; reflexivity) ltac:(right; exact Hb)) as [D|D].
{ intros E. cbn [map] in ND2. apply (proj1 (List.NoDup_cons_iff _ _) ) in ND2. destruct ND2 as [NI _]. apply NI. cbn [blk_id fst snd] in E |- *. rewrite E. apply in_map. exact Hb. }
all: unfold in_block in Hab; cbn [blk_addr blk_size fst snd] in D; lia. }
assert (TPF : rtables_pristine mF).
{ eapply rtables_pristine_munch; [exact TP2| exact MU|]. intros x Hx. unfold RTABLES_LO, RTABLES_HI in Hx. cbn. split; [lia| exact I]. }

rewrite sx32_lit in B6 by lia. change (Z_to_bv 64 243480) with (Z_to_bv 64 NB_SUBMODES_PTR) in B6.
apply nb_b45_split in B45. apply rw_cells_app in B45. destruct B45 as [B4 B5]. cbn [cells_size csize] in B5.
change (Z.of_nat 4) with 4 in B5. fixaddr B5 A 2228.
apply nb_hdr_recast in B0.
pose proof (rw_cells_join _ _ _ _ _ B1' B1b ltac:(cbn; lia)) as B1. clear B1' B1b.
apply nb_mid_recast in B1. unfold nb_mid_cells in B1.
apply rw_cells_app in B1. destruct B1 as [Q1 B1]. apply rw_cells_app in B1. destruct B1 as [Q2 B1]. apply rw_cells_app in B1. destruct B1 as [Q3 B1].
apply rw_cells_app in B1. destruct B1 as [Q4 B1]. apply rw_cells_app in B1. destruct B1 as [Q5 B1]. apply rw_cells_app in B1. destruct B1 as [Q6 B1].
apply rw_cells_app in B1. destruct B1 as [Q7 B1]. apply rw_cells_app in B1. destruct B1 as [Q8 Q9].
fixaddr2 Q2 A 2032. fixaddr2 Q3 A 2040. fixaddr2 Q4 A 2080. fixaddr2 Q5 A 2120. fixaddr2 Q6 A 2160. fixaddr2 Q7 A 2168. fixaddr2 Q8 A 2184. fixaddr2 Q9 A 2192.
apply nb_b3_recast in B3.
pose proof (rw_cells_join _ _ _ _ _ B9 (rw_cells_join _ _ _ _ _ B10 B11 ltac:(cbn; lia)) ltac:(cbn; lia)) as BT.
apply nb_tailblk_recast in BT. apply rw_cells_app in BT. destruct BT as [Q17 Q18].
fixaddr2 Q18 A 2948.
apply nb_cbs_recast in B7.
apply evt_done. unfold rinit_post. sf_eexists 15%nat. first [ unshelve sf_eexists 4%nat; [ exact (F) | exact (fc) | exact (mF) | exact (errv2) | ] | sf_fb; exists F, fc, mF, errv2 ].
split; [reflexivity|]. split; [exact FRM|]. split; [exact MIF|]. split; [exact STF|].
split; [rewrite ETP; unfold RERRNO; exact ERR2|]. split; [exact AUXF|]. split; [exact PRESF|]. split; [exact PSO|].
cbn [option_map]. exists A, [(p, A, 2968)].
split; [reflexivity|]. split; [lia|]. split; [exact HEAPF|].
split.
{ intros STEREO. cbn [decst_rep]. split; [reflexivity|].
split; [apply Z.mod_divide in A16; [| lia]; apply Z.mod_divide; [lia|]; destruct A16 as [q Hq]; exists (2 * q); lia|].
split; [exact A0|]. split; [apply nb_init_inv|].
exists zjunk. split; [exact zjunk_ok|]. split; [apply zjunk_cbs|].
apply nb_cells_of_pieces; [exact zjunk_ok|]. unfold nb_pieces.
cbn [nb_hdr_cells nb_cfg_cells nb_tail_cells nb_ucb_cells cb_cells nb_isave_ptr nb_init_state nb_first nb_count_lost nb_sampling_rate
nb_innov_save nb_pitch_gain_buf_idx nb_encode_submode nb_submodeID nb_lpc_enh_enabled nb_voc_offset nb_dtx_enabled nb_isWideband
nb_highpass_enabled zjunk j_last_ol_gain j_excbuf j_exc j_old_qlsp j_interp_qlpc j_mem_sp j_mem_hp j_pi_gain j_levels j_last_pitch
j_last_pitch_gain j_pitch_gain_buf j_seed j_pad1 j_cbs j_ucb j_voc j_pad2 fst snd].
unfold NB_DEFAULT_SUBMODE.
repeat match goal with |- _ /\ _ => split end; eassumption. }
split; [exact (RHEAP_blocks_nodup_proof _ _ _ HEAPF)|].
cbn. repeat split; reflexivity.
-
destruct RES as [-> HEAP2]. clear MU1 WM1 HP2.
apply implM_ret.
step. step. if_cases K0; [| exfalso; zify_cond K0; rewrite ?unsigned_lit in K0 by lia; lia].
step. step. step. step. step. step. step. step. step.
release_frame FR2 ST2 (bv_unsigned sp).
apply evt_done. unfold rinit_post. sf_eexists 15%nat. first [ unshelve sf_eexists 4%nat; [ exact (F) | exact (fc) | exact (m2) | exact (errv2) | ] | sf_fb; exists F, fc, m2, errv2 ].
split; [reflexivity|]. split; [exact FRM|]. split; [exact MI2|]. split; [exact ST2|].
split; [rewrite ETP; unfold RERRNO; exact ERR2|]. split; [exact AUX2|]. split; [exact PRES2|]. split; [exact PSO|].
cbn [option_map]. split; [reflexivity| exact HEAP2].
Qed.
