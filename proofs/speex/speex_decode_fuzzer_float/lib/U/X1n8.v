(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj X1bs X1c2 X1br.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0px X0qp X0pw.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1m2 X1m3 X1m5. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk X1n7. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1h7 X1go X1hk X1ho.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1ra X1qu X1r3 X1nt X1rh X1re.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
Import ListNotations.
Open Scope Z_scope.

Definition A_nb_decoder_init : Z := 0x20380.
Definition A_nb_decoder_destroy : Z := 0x204d8.
Definition A_nb_decoder_ctl : Z := 0x204dc.
Definition A_sb_decoder_init : Z := 0x2e460.
Definition A_sb_decoder_destroy : Z := 0x2e62c.
Definition A_sb_decoder_ctl : Z := 0x2e6a8.
Definition A_sb_decode : Z := 0x2edc8.
Definition A_nb_mode : Z := 0x3b6f8.
Definition A_sb_wb_mode : Z := 0x3bdf0.
Definition A_sb_uwb_mode : Z := 0x3bef8.
Definition WB_SUBMODES_PTR : Z := A_sb_wb_mode + 40.
Definition UWB_SUBMODES_PTR : Z := A_sb_uwb_mode + 40.
Definition GOT_default_user_handler : Z := 0x3c090.

Notation DREP := (decst_rep rsegs NB_MODE_PTR NB_SUBMODES_PTR A_speex_default_user_handler A_speex_std_stereo_request_handler
A_speex_wb_mode A_speex_uwb_mode WB_SUBMODES_PTR UWB_SUBMODES_PTR).
Notation EXCREADY := (dec_exc_ready rsegs).
Notation DECREP := (dec_rep rsegs NB_MODE_PTR NB_SUBMODES_PTR A_speex_default_user_handler A_speex_std_stereo_request_handler
A_speex_wb_mode A_speex_uwb_mode WB_SUBMODES_PTR UWB_SUBMODES_PTR).
Notation NBREP := (nbstate_rep rsegs NB_MODE_PTR NB_SUBMODES_PTR A_speex_default_user_handler A_speex_std_stereo_request_handler).
Notation SBCELLS := (sb_cells NB_MODE_PTR A_speex_wb_mode A_speex_uwb_mode WB_SUBMODES_PTR UWB_SUBMODES_PTR).

Definition mode_desc_cells (mode query name : Z) (id : Z) (ei ed en di dd de ec dc : Z) : list cell :=
[C8 (Z_to_bv 64 mode); C8 (Z_to_bv 64 query); C8 (Z_to_bv 64 name); C4 (Z_to_bv 64 id); C4 (Z_to_bv 64 4);
C8 (Z_to_bv 64 ei); C8 (Z_to_bv 64 ed); C8 (Z_to_bv 64 en); C8 (Z_to_bv 64 di); C8 (Z_to_bv 64 dd); C8 (Z_to_bv 64 de);
C8 (Z_to_bv 64 ec); C8 (Z_to_bv 64 dc)].

Definition nb_desc_cells : list cell := Eval cbv in
mode_desc_cells A_nb_mode 0x1d038 0x104f4 0 0x1dc0c 0x1dd70 0x1e6e0 A_nb_decoder_init A_nb_decoder_destroy A_nb_decode 0x1ddb0 A_nb_decoder_ctl.
Definition wb_desc_cells : list cell := Eval cbv in
mode_desc_cells A_sb_wb_mode 0x2b8d0 0x105f9 1 0x2b9f4 0x2bcdc 0x2c8d4 A_sb_decoder_init A_sb_decoder_destroy A_sb_decode 0x2bd68 A_sb_decoder_ctl.
Definition uwb_desc_cells : list cell := Eval cbv in
mode_desc_cells A_sb_uwb_mode 0x2b8d0 0x106bb 2 0x2b9f4 0x2bcdc 0x2c8d4 A_sb_decoder_init A_sb_decoder_destroy A_sb_decode 0x2bd68 A_sb_decoder_ctl.

Local Ltac pristine_cells TP :=
apply rw_cells_of_pristine;
[ exact TP
| cbn; repeat split
| unfold RTABLES_LO, NB_MODE_PTR, A_speex_nb_mode, A_speex_wb_mode, A_speex_uwb_mode, A_nb_mode, A_sb_wb_mode, A_sb_uwb_mode, GOT_default_user_handler; lia
| match goal with |- ?a + Z.of_nat ?n <= ?h => let v := eval cbv in (Z.of_nat n) in change (a + v <= h) end;
unfold RTABLES_HI, NB_MODE_PTR, A_speex_nb_mode, A_speex_wb_mode, A_speex_uwb_mode, A_nb_mode, A_sb_wb_mode, A_sb_uwb_mode, GOT_default_user_handler; lia
| vm_compute; reflexivity ].

Lemma nb_desc_of_pristine : forall m, rtables_pristine m -> rw_cells rsegs m NB_MODE_PTR nb_desc_cells.
Proof. intros m TP. pristine_cells TP. Qed.
Lemma wb_desc_of_pristine : forall m, rtables_pristine m -> rw_cells rsegs m A_speex_wb_mode wb_desc_cells.
Proof. intros m TP. pristine_cells TP. Qed.
Lemma uwb_desc_of_pristine : forall m, rtables_pristine m -> rw_cells rsegs m A_speex_uwb_mode uwb_desc_cells.
Proof. intros m TP. pristine_cells TP. Qed.

Definition nb_mode_cells : list cell := Eval cbv in
[C4 (Z_to_bv 64 160); C4 (Z_to_bv 64 40); C4 (Z_to_bv 64 10); C4 (Z_to_bv 64 17); C4 (Z_to_bv 64 144);
C4 (Z_to_bv 64 0x3f6b851f); C4 (Z_to_bv 64 0x3f19999a); C4 (Z_to_bv 64 0x3951b717);
C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0x3b828); C8 (Z_to_bv 64 0x3b880); C8 (Z_to_bv 64 0x3b8d8); C8 (Z_to_bv 64 0x3b930);
C8 (Z_to_bv 64 0x3b988); C8 (Z_to_bv 64 0x3b9e0); C8 (Z_to_bv 64 0x3ba38); C8 (Z_to_bv 64 0x3ba90);
C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
C4 (Z_to_bv 64 NB_DEFAULT_SUBMODE)].
Lemma nb_mode_of_pristine : forall m, rtables_pristine m -> rw_cells rsegs m A_nb_mode nb_mode_cells.
Proof. intros m TP. pristine_cells TP. Qed.

Definition sb_mode_cells (nbm : Z) (mo : spx_mode) (fold : Z) (subs : list Z) : list cell :=
[C8 (Z_to_bv 64 nbm); C4 (Z_to_bv 64 (sbm_frameSize mo)); C4 (Z_to_bv 64 (sbm_subframeSize mo)); C4 (Z_to_bv 64 (sbm_lpcSize mo));
C4 (Z_to_bv 64 0x3f666666); C4 (Z_to_bv 64 0x3f19999a); C4 (Z_to_bv 64 0x3951b717); C4 (Z_to_bv 64 fold); C4 (Z_to_bv 64 0)]
++ map (fun z => C8 (Z_to_bv 64 z)) subs ++ [C4 (Z_to_bv 64 (sbm_defaultSubmode mo))].
Definition sb_wb_mode_cells : list cell := Eval cbv in
sb_mode_cells A_speex_nb_mode ModeWB 0x3f666666 [0; 0x3bc90; 0x3bce8; 0x3bd40; 0x3bd98; 0; 0; 0].
Definition sb_uwb_mode_cells : list cell := Eval cbv in
sb_mode_cells A_speex_wb_mode ModeUWB 0x3f333333 [0; 0x3bc90; 0; 0; 0; 0; 0; 0].
Lemma sb_wb_mode_of_pristine : forall m, rtables_pristine m -> rw_cells rsegs m A_sb_wb_mode sb_wb_mode_cells.
Proof. intros m TP. pristine_cells TP. Qed.
Lemma sb_uwb_mode_of_pristine : forall m, rtables_pristine m -> rw_cells rsegs m A_sb_uwb_mode sb_uwb_mode_cells.
Proof. intros m TP. pristine_cells TP. Qed.

Lemma got_user_handler_of_pristine : forall m, rtables_pristine m -> rw_cells rsegs m GOT_default_user_handler [C8 (Z_to_bv 64 A_speex_default_user_handler)].
Proof. intros m TP. pristine_cells TP. Qed.

Definition desc_cells_of (mo : spx_mode) : list cell :=
match mo with ModeNB => nb_desc_cells | ModeWB => wb_desc_cells | ModeUWB => uwb_desc_cells end.
Lemma desc_of_pristine : forall m mo, rtables_pristine m ->
rw_cells rsegs m (sb_mode_ptr NB_MODE_PTR A_speex_wb_mode A_speex_uwb_mode mo) (desc_cells_of mo).
Proof.
intros m [| |] TP; cbn [sb_mode_ptr desc_cells_of].
- apply nb_desc_of_pristine; exact TP.
- apply wb_desc_of_pristine; exact TP.
- apply uwb_desc_of_pristine; exact TP.
Qed.

Definition creq_ok (OUT P : Z) (r : ctl_req) : Prop :=
match r with
| CtlSetEnh v | CtlSetWideband v => v = 0 \/ v = 1
| CtlGetFrameSize | CtlSetHandlerStereo | CtlSetSamplingRate _ | CtlGetSamplingRate | CtlGetLookahead => True
| CtlSetInnovationSave off => P = OUT + 4 * off /\ 160 <= off
| CtlGetDtxStatus | CtlGetPiGain | CtlGetExc => True
end.

Definition creq_size (r : ctl_req) : Z :=
match r with CtlSetHandlerStereo => 24 | CtlSetInnovationSave _ => 0 | CtlGetPiGain | CtlGetExc => 16 | _ => 4 end.

Definition creq_pre (STEREO : Z) (m : mem) (S : Z) (d : dec_state bptr) (P : Z) (r : ctl_req) : Prop :=
match r with
| CtlSetEnh v | CtlSetSamplingRate v | CtlSetWideband v =>
exists w : word, rw_cells rsegs m P [C4 w] /\ bv_unsigned w mod 2^32 = v mod 2^32 /\ - 2^31 <= v < 2^31
| CtlGetFrameSize | CtlGetSamplingRate | CtlGetLookahead | CtlGetDtxStatus => exists w : word, rw_cells rsegs m P [C4 w]
| CtlSetHandlerStereo => exists pad : word,
rw_cells rsegs m P [C4 (Z_to_bv 64 SPEEX_INBAND_STEREO); C4 pad; C8 (Z_to_bv 64 A_speex_std_stereo_request_handler); C8 (Z_to_bv 64 STEREO)]
| CtlSetInnovationSave _ => True
| CtlGetPiGain => exists ws : list word, rw_cells rsegs m P (f32 ws) /\ length ws = 4%nat
| CtlGetExc => (exists ws : list word, rw_cells rsegs m P (f32 ws) /\ length ws = 4%nat) /\ EXCREADY m S d
end.
Definition creq_ptr_ok (P : Z) (r : ctl_req) : Prop :=
match r with CtlSetInnovationSave _ => True | CtlSetHandlerStereo => 0 < P /\ P mod 8 = 0 | _ => 0 < P /\ P mod 4 = 0 end.
Definition creq_post (STEREO : Z) (m : mem) (P : Z) (r : ctl_req) (v : Z) : Prop :=
match r with
| CtlSetEnh v0 | CtlSetSamplingRate v0 | CtlSetWideband v0 =>
exists w : word, rw_cells rsegs m P [C4 w] /\ bv_unsigned w mod 2^32 = v0 mod 2^32
| CtlGetFrameSize | CtlGetSamplingRate | CtlGetLookahead => rw_cells rsegs m P [C4 (Z_to_bv 64 v)] /\ - 2^31 <= v < 2^31
| CtlGetDtxStatus => rw_cells rsegs m P [C4 (Z_to_bv 64 v)] /\ (v = 0 \/ v = 1)
| CtlSetHandlerStereo => exists pad : word,
rw_cells rsegs m P [C4 (Z_to_bv 64 SPEEX_INBAND_STEREO); C4 pad; C8 (Z_to_bv 64 A_speex_std_stereo_request_handler); C8 (Z_to_bv 64 STEREO)]
| CtlSetInnovationSave _ => True
| CtlGetPiGain | CtlGetExc => exists ws : list word, rw_cells rsegs m P (f32 ws) /\ length ws = 4%nat
end.

Fixpoint ctl_depth (d : dec_state bptr) : Z :=
match d with DecNB _ => 96 | DecSB _ low => 32 + ctl_depth low end.

Definition creq_val_ok (d : dec_state bptr) (r : ctl_req) : Prop := - 2^31 <= fst (speex_decoder_ctl d r) < 2^31.

Lemma sx32_mod32 : forall w : word, bv_unsigned (sx32 w) mod 2^32 = bv_unsigned w mod 2^32.
Proof.
intros w. unfold sx32. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64). rewrite mod64_mod32.
unfold bv_swrap. pose proof (bv_unsigned_in_range 64 w) as R.
change (bv_wrap 32 (bv_unsigned w + bv_half_modulus 32)) with ((bv_unsigned w + 2^31) mod 2^32).
change (bv_half_modulus 32) with (2^31).
set (u := bv_unsigned w) in *. clearbody u. change (bv_modulus 64) with (2^64) in R.
Z.div_mod_to_equations. nia.
Qed.

Lemma sx32_cell_eqm : forall (w : word) (v : Z), bv_unsigned w mod 2^32 = v mod 2^32 -> le4 (Z_to_bv 64 v) = le4 (sx32 w).
Proof.
intros w v E. apply le4_eqm. rewrite sx32_mod32, E, Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64). apply mod64_mod32.
Qed.

Lemma C4_samebytes : forall m A (w1 w2 : word), rw_cells rsegs m A [C4 w1] -> bv_unsigned w1 mod 2^32 = bv_unsigned w2 mod 2^32 -> rw_cells rsegs m A [C4 w2].
Proof.
intros m A w1 w2 X E. eapply rw_cells_samebytes; [exact X| cbn; tauto| cbn [cells_bytes cbytes app]; rewrite (le4_eqm w2 w1) by (symmetry; exact E); reflexivity| reflexivity].
Qed.

Lemma sx32_lit : forall v, - 2^31 <= v < 2^31 -> sx32 (Z_to_bv 64 v) = Z_to_bv 64 v.
Proof.
intros v Hv. unfold sx32. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
rewrite swrap32_mod64, swrap32_small by lia. reflexivity.
Qed.

Definition creq_grp1 (r : ctl_req) : bool :=
match r with CtlGetPiGain | CtlGetExc | CtlGetDtxStatus | CtlSetInnovationSave _ => false | _ => true end.

Definition blocks_ivs (LBD : list block) : list (Z * Z) := map (fun b => (blk_addr b, blk_addr b + blk_size b)) LBD.

Definition creq_ivs (P : Z) (r : ctl_req) : list (Z * Z) :=
match r with CtlSetInnovationSave _ => [] | _ => [(P, P + creq_size r)] end.
Definition ctlW (lo usp P : Z) (r : ctl_req) (LBD : list block) : list (Z * Z) :=
(lo, usp) :: creq_ivs P r ++ blocks_ivs LBD.
Lemma ctlW_grp1 : forall lo usp P r LBD, creq_grp1 r = true -> ctlW lo usp P r LBD = (lo, usp) :: (P, P + creq_size r) :: blocks_ivs LBD.
Proof. intros lo usp P r LBD G. destruct r; try discriminate G; reflexivity. Qed.

Definition rctl_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(OUT STEREO S : Z) (d : dec_state bptr) (LBD : list block) (r : ctl_req) (P lo : Z) (m : mem) : machine_state -> Prop :=
fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (ret_pc ra) fc' None m' (seg_rom rsegs)
/\ munch (ctlW lo (bv_unsigned sp) P r LBD) m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ frm0 fc' /\ stk rsegs m' lo (bv_unsigned sp)
/\ DREP OUT STEREO m' S (snd (speex_decoder_ctl d r)) LBD
/\ creq_post STEREO m' P r (fst (speex_decoder_ctl d r))
/\ (EXCREADY m S d -> EXCREADY m' S (snd (speex_decoder_ctl d r))).

Definition rctl_at {RCEIL : RunCeiling} (d : dec_state bptr) : Prop :=
forall (OUT STEREO S : Z) (LBD : list block) (r : ctl_req) (P lo : Z)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem),
DREP OUT STEREO m S d LBD -> (dec_depth d <= 3)%nat -> creq_ok OUT P r -> creq_pre STEREO m S d P r -> creq_ptr_ok P r -> bv_unsigned sp mod 16 = 0 -> rtables_pristine m ->
(forall b, In b LBD -> rblock_range (blk_addr b) (blk_size b)) -> List.NoDup (map blk_id LBD) -> lbd_apart LBD ->
(P + creq_size r <= lo \/ bv_unsigned sp <= P) ->
(forall b, In b LBD -> P + creq_size r <= blk_addr b \/ blk_addr b + blk_size b <= P) ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - ctl_depth d ->
mem_inv rsegs m -> frm0 fc ->
a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 (ctl_req_code r) -> a2 = Z_to_bv 64 P ->
evt rsegs (rctl_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 OUT STEREO S d LBD r P lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_speex_decoder_ctl) fc None m (seg_rom rsegs)).

Definition rctl_atP {RCEIL : RunCeiling} (Pr : ctl_req -> Prop) (d : dec_state bptr) : Prop :=
forall (OUT STEREO S : Z) (LBD : list block) (r : ctl_req) (P lo : Z)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem),
Pr r ->
DREP OUT STEREO m S d LBD -> (dec_depth d <= 3)%nat -> creq_ok OUT P r -> creq_pre STEREO m S d P r -> creq_ptr_ok P r -> bv_unsigned sp mod 16 = 0 -> rtables_pristine m ->
(forall b, In b LBD -> rblock_range (blk_addr b) (blk_size b)) -> List.NoDup (map blk_id LBD) -> lbd_apart LBD ->
(P + creq_size r <= lo \/ bv_unsigned sp <= P) ->
(forall b, In b LBD -> P + creq_size r <= blk_addr b \/ blk_addr b + blk_size b <= P) ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - ctl_depth d ->
mem_inv rsegs m -> frm0 fc ->
a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 (ctl_req_code r) -> a2 = Z_to_bv 64 P ->
evt rsegs (rctl_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 OUT STEREO S d LBD r P lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_speex_decoder_ctl) fc None m (seg_rom rsegs)).

Lemma rctl_at_join {RCEIL : RunCeiling} : forall d, rctl_atP (fun r => creq_grp1 r = true) d -> rctl_atP (fun r => creq_grp1 r = false) d -> rctl_at d.
Proof. intros d H1 H2 OUT STEREO S LBD r. intros. destruct (creq_grp1 r) eqn:G; [eapply H1| eapply H2]; eassumption. Qed.

Lemma munch_weaken_to : forall W W' m m', munch W m m' -> (forall x, outside W' x -> outside W x) -> munch W' m m'.
Proof. intros W W' m m' MU SUB. eapply munch_weaken; [| exact MU]. exact SUB. Qed.

Lemma outside_cons : forall iv W x, outside (iv :: W) x <-> ~ (fst iv <= x < snd iv) /\ outside W x.
Proof. intros [lo hi] W x. cbn. tauto. Qed.

Lemma outside_blocks_ivs : forall LBD x, outside (blocks_ivs LBD) x <-> (forall b, In b LBD -> ~ (blk_addr b <= x < blk_addr b + blk_size b)).
Proof.
induction LBD as [|b L IH]; intros x; cbn.
- split; [intros _ b []| intros; exact I].
- rewrite IH. split.
+ intros [H1 H2] b' [<-|Hb']; [exact H1| apply H2; exact Hb'].
+ intros H. split; [apply H; left; reflexivity| intros b' Hb'; apply H; right; exact Hb'].
Qed.

Lemma dec_depth_pos : forall d : dec_state bptr, (1 <= dec_depth d)%nat.
Proof. destruct d; cbn; lia. Qed.

Lemma lookahead_val : forall d : dec_state bptr, (dec_depth d <= 3)%nat ->
fst (speex_decoder_ctl d CtlGetLookahead) = 40 \/ fst (speex_decoder_ctl d CtlGetLookahead) = 80 \/ fst (speex_decoder_ctl d CtlGetLookahead) = 160.
Proof.
intros d Hd. destruct d as [st|s1 [st|s2 [st|s3 low]]].
1-3: cbn -[Z.mul]; unfold NB_SUBFRAME_SIZE; lia.
exfalso. cbn [dec_depth] in Hd. pose proof (dec_depth_pos low). lia.
Qed.

Lemma outside_ctlW : forall lo usp P r L a,
outside (ctlW lo usp P r L) a <-> ~ (lo <= a < usp) /\ ~ (P <= a < P + creq_size r) /\ (forall b, In b L -> ~ (blk_addr b <= a < blk_addr b + blk_size b)).
Proof.
intros. unfold ctlW. rewrite outside_cons. cbn [fst snd].
destruct r; cbn [creq_ivs creq_size app]; rewrite ?outside_cons, outside_blocks_ivs; cbn [fst snd]; try tauto.
split; [intros [A B]; split; [exact A| split; [lia| exact B]]| intros (A & _ & B); exact (conj A B)].
Qed.

Lemma munch_agree_at : forall W m m' A n,
munch W m m' -> wmono rsegs m m' -> (forall a, A <= a < A + n -> outside W a) -> 0 <= A -> A + n <= 2^64 ->
agree_at rsegs m m' A n.
Proof.
intros W m m' A n MU WM OUT A0 AN a Ha. split; [| apply WM]. apply MU. rewrite wa_unsigned by lia. apply OUT. exact Ha.
Qed.

Lemma rw_cells_munch_out : forall W m m' A cs,
rw_cells rsegs m A cs -> munch W m m' -> wmono rsegs m m' ->
(forall a, A <= a < A + Z.of_nat (cells_size cs) -> outside W a) -> rw_cells rsegs m' A cs.
Proof.
intros W m m' A cs X MU WM OUT. pose proof (rw_cells_bound _ _ _ _ X) as B.
eapply rw_cells_agree_at; [exact X|]. eapply munch_agree_at; [exact MU| exact WM| exact OUT| lia| lia].
Qed.

Lemma rtables_pristine_munch : forall W m m', rtables_pristine m -> munch W m m' ->
(forall a, RTABLES_LO <= a < RTABLES_HI -> outside W a) -> rtables_pristine m'.
Proof.
intros W m m' TP MU OUT a Ha. rewrite (MU a (OUT _ Ha)). apply TP. exact Ha.
Qed.

Lemma decst_rep_munch : forall d W OUT STEREO m m' SL L,
DREP OUT STEREO m SL d L -> munch W m m' -> wmono rsegs m m' ->
(forall b a, In b L -> blk_addr b <= a < blk_addr b + blk_size b -> outside W a) ->
DREP OUT STEREO m' SL d L.
Proof.
intros d W OUT STEREO m m' SL L R MU WM HO. eapply decst_rep_agree; [exact R|]. eapply agree_blocks_of_munch; [exact MU| exact WM| exact HO].
Qed.

Lemma dec_exc_ready_munch : forall d W OUT STEREO m m' SL L,
DREP OUT STEREO m SL d L -> EXCREADY m SL d -> munch W m m' -> wmono rsegs m m' ->
(forall b a, In b L -> blk_addr b <= a < blk_addr b + blk_size b -> outside W a) ->
EXCREADY m' SL d.
Proof.
intros d W OUT STEREO m m' SL L R EX MU WM HO. eapply dec_exc_ready_agree; [exact R| exact EX|]. eapply agree_blocks_of_munch; [exact MU| exact WM| exact HO].
Qed.

Lemma lbd_apart_sub : forall L L', lbd_apart L -> (forall b, In b L' -> In b L) -> lbd_apart L'.
Proof. intros L L' H SUB b1 b2 H1 H2 NE. apply H; auto. Qed.

Lemma NoDup_map_app_r {A B} (f : A -> B) (l1 l2 : list A) : List.NoDup (map f (l1 ++ l2)) -> List.NoDup (map f l2).
Proof. rewrite map_app. intros H. apply List.NoDup_app_remove_l in H. exact H. Qed.

Lemma NoDup_app_in_neq {A} (l1 l2 : list A) x y : List.NoDup (l1 ++ l2) -> In x l1 -> In y l2 -> x <> y.
Proof.
intros ND H1 H2 ->. induction l1 as [|z l1 IH]; [destruct H1|].
cbn in ND. apply List.NoDup_cons_iff in ND. destruct ND as [NI ND]. destruct H1 as [->|H1].
- apply NI. apply in_app_iff. right. exact H2.
- exact (IH ND H1).
Qed.

Lemma apart_parts : forall L1 L2 b1 b2, List.NoDup (map blk_id (L1 ++ L2)) -> lbd_apart (L1 ++ L2) -> In b1 L1 -> In b2 L2 ->
blk_addr b1 + blk_size b1 <= blk_addr b2 \/ blk_addr b2 + blk_size b2 <= blk_addr b1.
Proof.
intros L1 L2 b1 b2 ND AP H1 H2. apply AP; [apply in_app_iff; left; exact H1| apply in_app_iff; right; exact H2|].
rewrite map_app in ND. eapply NoDup_app_in_neq; [exact ND| apply in_map; exact H1| apply in_map; exact H2].
Qed.

Theorem dec_rep_frame_proof : dec_rep_frame_stmt DECREP.
Proof. intros STEREO m m' S d LBD R AG. eapply dec_rep_frame; [exact R| exact AG]. Qed.
