(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1cp X1ck X1cu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt X1rh X1re.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X07z X05o X081 X05l X05m X09f X06d.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X0yr X0ys.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yr OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ys.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition A_speex_decoder_init : Z := 0x9896c.
Definition A_speex_decoder_destroy : Z := 0x98a30.
Definition A_speex_decode_native : Z := 0x98b18.
Definition A_speex_decode : Z := 0x98c00.
Definition A_speex_decoder_ctl : Z := 0x98c74.
Definition A_nb_decoder_init : Z := 0xa03b0.
Definition A_nb_decoder_destroy : Z := 0xa08d4.
Definition A_nb_decoder_ctl : Z := 0xa08d8.
Definition A_nb_decode : Z := 0xa16a8.
Definition A_sb_decoder_init : Z := 0xbcc10.
Definition A_sb_decoder_destroy : Z := 0xbd428.
Definition A_sb_decoder_ctl : Z := 0xbd590.
Definition A_sb_decode : Z := 0xbe6c0.
Definition A_speex_default_user_handler : Z := 0xb2c68.
Definition A_speex_std_stereo_request_handler : Z := 0x991f0.
Definition A_speex_inband_handler : Z := 0xb2b1c.
Definition NB_SUBMODES_PTR : Z := A_nb_mode + 32.
Definition WB_SUBMODES_PTR : Z := A_sb_wb_mode + 40.
Definition UWB_SUBMODES_PTR : Z := A_sb_uwb_mode + 40.
Definition SPEEX_INBAND_STEREO : Z := 9.

Notation DREP := (decst_rep bsegs A_speex_nb_mode NB_SUBMODES_PTR A_speex_default_user_handler A_speex_std_stereo_request_handler
A_speex_wb_mode A_speex_uwb_mode WB_SUBMODES_PTR UWB_SUBMODES_PTR).
Notation EXCREADY := (dec_exc_ready bsegs).
Notation DECREP := (dec_rep bsegs A_speex_nb_mode NB_SUBMODES_PTR A_speex_default_user_handler A_speex_std_stereo_request_handler
A_speex_wb_mode A_speex_uwb_mode WB_SUBMODES_PTR UWB_SUBMODES_PTR).
Notation NBREP := (nbstate_rep bsegs A_speex_nb_mode NB_SUBMODES_PTR A_speex_default_user_handler A_speex_std_stereo_request_handler).
Notation SBCELLS := (sb_cells A_speex_nb_mode A_speex_wb_mode A_speex_uwb_mode WB_SUBMODES_PTR UWB_SUBMODES_PTR).

Definition ablk (m : mem) (lo : Z) (b : block) : Prop :=
aobj bsegs m (blk_addr b) (blk_size b) /\ blk_addr b mod 8 = 0 /\ (blk_addr b + blk_size b <= SH_LO \/ SH_HI <= blk_addr b)
/\ (blk_addr b + blk_size b <= 0x10000 \/ IMG_TOP_B <= blk_addr b) /\ blk_addr b + blk_size b <= lo.

Definition creq_ok (OUT P : Z) (r : ctl_req) : Prop :=
match r with
| CtlSetEnh v | CtlSetWideband v => v = 0 \/ v = 1
| CtlGetFrameSize | CtlSetHandlerStereo | CtlSetSamplingRate _ | CtlGetSamplingRate | CtlGetLookahead => True
| CtlSetInnovationSave off => P = OUT + 4 * off /\ 160 <= off
| CtlGetDtxStatus | CtlGetPiGain | CtlGetExc => True
end.

Definition creq_size (r : ctl_req) : Z :=
match r with CtlSetHandlerStereo => 24 | CtlSetInnovationSave _ => 0 | CtlGetPiGain | CtlGetExc => 16 | _ => 4 end.

Definition creq_align (r : ctl_req) : Z := match r with CtlSetHandlerStereo => 8 | _ => 4 end.

Definition creq_pre (STEREO : Z) (m : mem) (S : Z) (d : dec_state bptr) (P : Z) (r : ctl_req) : Prop :=
match r with
| CtlSetEnh v | CtlSetSamplingRate v | CtlSetWideband v =>
exists w : word, rw_cells bsegs m P [C4 w] /\ bv_unsigned w mod 2^32 = v mod 2^32 /\ - 2^31 <= v < 2^31
| CtlGetFrameSize | CtlGetSamplingRate | CtlGetLookahead | CtlGetDtxStatus => exists w : word, rw_cells bsegs m P [C4 w]
| CtlSetHandlerStereo => exists pad : word,
rw_cells bsegs m P [C4 (Z_to_bv 64 SPEEX_INBAND_STEREO); C4 pad; C8 (Z_to_bv 64 A_speex_std_stereo_request_handler); C8 (Z_to_bv 64 STEREO)]
| CtlSetInnovationSave _ => True
| CtlGetPiGain => exists ws : list word, rw_cells bsegs m P (f32 ws) /\ length ws = 4%nat
| CtlGetExc => (exists ws : list word, rw_cells bsegs m P (f32 ws) /\ length ws = 4%nat) /\ EXCREADY m S d
end.
Definition creq_post (STEREO : Z) (m : mem) (P : Z) (r : ctl_req) (v : Z) : Prop :=
match r with
| CtlSetEnh v0 | CtlSetSamplingRate v0 | CtlSetWideband v0 =>
exists w : word, rw_cells bsegs m P [C4 w] /\ bv_unsigned w mod 2^32 = v0 mod 2^32
| CtlGetFrameSize | CtlGetSamplingRate | CtlGetLookahead => rw_cells bsegs m P [C4 (Z_to_bv 64 v)] /\ - 2^31 <= v < 2^31
| CtlGetDtxStatus => rw_cells bsegs m P [C4 (Z_to_bv 64 v)] /\ (v = 0 \/ v = 1)
| CtlSetHandlerStereo => exists pad : word,
rw_cells bsegs m P [C4 (Z_to_bv 64 SPEEX_INBAND_STEREO); C4 pad; C8 (Z_to_bv 64 A_speex_std_stereo_request_handler); C8 (Z_to_bv 64 STEREO)]
| CtlSetInnovationSave _ => True
| CtlGetPiGain | CtlGetExc => exists ws : list word, rw_cells bsegs m P (f32 ws) /\ length ws = 4%nat
end.

Definition creq_grp1 (r : ctl_req) : bool :=
match r with CtlGetPiGain | CtlGetExc | CtlGetDtxStatus | CtlSetInnovationSave _ => false | _ => true end.

Definition creq_ivs (P : Z) (r : ctl_req) : list (Z * Z) :=
match r with CtlSetInnovationSave _ => [] | _ => [(P, P + creq_size r)] end.
Definition ctlW (lo usp P : Z) (r : ctl_req) (LBD : list block) : list (Z * Z) :=
(lo, usp) :: creq_ivs P r ++ blocks_ivs LBD.
Lemma ctlW_grp1 : forall lo usp P r LBD, creq_grp1 r = true -> ctlW lo usp P r LBD = (lo, usp) :: (P, P + creq_size r) :: blocks_ivs LBD.
Proof. intros lo usp P r LBD G. destruct r; try discriminate G; reflexivity. Qed.

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

Lemma C4_samebytes : forall m A (w1 w2 : word), rw_cells bsegs m A [C4 w1] -> bv_unsigned w1 mod 2^32 = bv_unsigned w2 mod 2^32 -> rw_cells bsegs m A [C4 w2].
Proof.
intros m A w1 w2 X E. eapply rw_cells_samebytes; [exact X| cbn; tauto| cbn [cells_bytes cbytes app]; rewrite (le4_eqm w2 w1) by (symmetry; exact E); reflexivity| reflexivity].
Qed.

Lemma sx32_lit : forall v, - 2^31 <= v < 2^31 -> sx32 (Z_to_bv 64 v) = Z_to_bv 64 v.
Proof.
intros v Hv. unfold sx32. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
rewrite swrap32_mod64, swrap32_small by lia. reflexivity.
Qed.

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

Lemma outside_ctlW : forall lo usp P r L a,
outside (ctlW lo usp P r L) a <-> ~ (lo <= a < usp) /\ ~ (P <= a < P + creq_size r) /\ (forall b, In b L -> ~ (blk_addr b <= a < blk_addr b + blk_size b)).
Proof.
intros. unfold ctlW. rewrite outside_cons. cbn [fst snd].
destruct r; cbn [creq_ivs creq_size app]; rewrite ?outside_cons, outside_blocks_ivs; cbn [fst snd]; try tauto.
split; [intros [A B]; split; [exact A| split; [lia| exact B]]| intros (A & _ & B); exact (conj A B)].
Qed.

Definition NBCTL_STACK : Z := 128.

Definition rctl_post (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (usp : Z)
(OUT STEREO S : Z) (d : dec_state bptr) (LBD : list block) (r : ctl_req) (P lo : Z) (m : mem) : machine_state -> Prop :=
fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem),
ms' = MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (ret_pc ra) fc' None m' (seg_rom bsegs)
/\ munch (ctlW lo usp P r LBD) m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
/\ frm0 fc' /\ stk bsegs m' lo usp
/\ DREP OUT STEREO m' S (snd (speex_decoder_ctl d r)) LBD
/\ creq_post STEREO m' P r (fst (speex_decoder_ctl d r))
/\ (EXCREADY m S d -> EXCREADY m' S (snd (speex_decoder_ctl d r))).

Definition rctl_atP (Pr : ctl_req -> Prop) (d : dec_state bptr) : Prop :=
forall (OUT STEREO S : Z) (LBD : list block) (r : ctl_req) (P lo usp : Z)
(ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem),
Pr r ->
DREP OUT STEREO m S d LBD -> creq_ok OUT P r -> creq_pre STEREO m S d P r ->
(forall b, In b LBD -> ablk m lo b) ->
aobj bsegs m P (creq_size r) -> P mod creq_align r = 0 ->
aobj bsegs m A_speex_nb_mode 96 ->
(P + creq_size r <= lo \/ usp <= P) ->
(forall b, In b LBD -> P + creq_size r <= blk_addr b \/ blk_addr b + blk_size b <= P) ->
stk bsegs m lo usp -> SH_HI <= lo -> lo <= usp - NBCTL_STACK -> usp < 2^63 ->
client_constsB m -> lib_consts m -> mem_inv bsegs m -> frm0 fc ->
evt bsegs (rctl_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp OUT STEREO S d LBD r P lo m)
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 S) (Z_to_bv 64 (ctl_req_code r)) (Z_to_bv 64 P) a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_speex_decoder_ctl) fc None m (seg_rom bsegs)).

Lemma munch_weaken_to : forall W W' m m', munch W m m' -> (forall x, outside W' x -> outside W x) -> munch W' m m'.
Proof. intros W W' m m' MU SUB. eapply munch_weaken; [| exact MU]. exact SUB. Qed.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition A_speex_decoder_init : Z := 0x983e8.
Definition A_speex_decoder_destroy : Z := 0x98480.
Definition A_speex_decode_native : Z := 0x98530.
Definition A_speex_decode : Z := 0x985e0.
Definition A_speex_decoder_ctl : Z := 0x98638.
Definition A_nb_decoder_init : Z := 0x9e800.
Definition A_nb_decoder_destroy : Z := 0x9eb78.
Definition A_nb_decoder_ctl : Z := 0x9eb7c.
Definition A_nb_decode : Z := 0x9f634.
Definition A_sb_decoder_init : Z := 0xb51a0.
Definition A_sb_decoder_destroy : Z := 0xb5960.
Definition A_sb_decoder_ctl : Z := 0xb5ab8.
Definition A_sb_decode : Z := 0xb67bc.
Definition A_speex_default_user_handler : Z := 0xaced0.
Definition A_speex_std_stereo_request_handler : Z := 0x98a7c.
Definition A_speex_inband_handler : Z := 0xacdb4.
Definition NB_SUBMODES_PTR : Z := A_nb_mode + 32.
Definition WB_SUBMODES_PTR : Z := A_sb_wb_mode + 40.
Definition UWB_SUBMODES_PTR : Z := A_sb_uwb_mode + 40.
Definition SPEEX_INBAND_STEREO : Z := 9.

Notation DREP := (decst_rep asegs A_speex_nb_mode NB_SUBMODES_PTR A_speex_default_user_handler A_speex_std_stereo_request_handler
A_speex_wb_mode A_speex_uwb_mode WB_SUBMODES_PTR UWB_SUBMODES_PTR).
Notation EXCREADY := (dec_exc_ready asegs).
Notation DECREP := (dec_rep asegs A_speex_nb_mode NB_SUBMODES_PTR A_speex_default_user_handler A_speex_std_stereo_request_handler
A_speex_wb_mode A_speex_uwb_mode WB_SUBMODES_PTR UWB_SUBMODES_PTR).
Notation NBREP := (nbstate_rep asegs A_speex_nb_mode NB_SUBMODES_PTR A_speex_default_user_handler A_speex_std_stereo_request_handler).
Notation SBCELLS := (sb_cells A_speex_nb_mode A_speex_wb_mode A_speex_uwb_mode WB_SUBMODES_PTR UWB_SUBMODES_PTR).

Definition ablk (m : mem) (lo : Z) (b : block) : Prop :=
aobj asegs m (blk_addr b) (blk_size b) /\ blk_addr b mod 8 = 0 /\ (blk_addr b + blk_size b <= SH_LO \/ SH_HI <= blk_addr b)
/\ (blk_addr b + blk_size b <= 0x10000 \/ IMG_TOP <= blk_addr b) /\ blk_addr b + blk_size b <= lo.

Definition creq_ok (OUT P : Z) (r : ctl_req) : Prop :=
match r with
| CtlSetEnh v | CtlSetWideband v => v = 0 \/ v = 1
| CtlGetFrameSize | CtlSetHandlerStereo | CtlSetSamplingRate _ | CtlGetSamplingRate | CtlGetLookahead => True
| CtlSetInnovationSave off => P = OUT + 4 * off /\ 160 <= off
| CtlGetDtxStatus | CtlGetPiGain | CtlGetExc => True
end.

Definition creq_size (r : ctl_req) : Z :=
match r with CtlSetHandlerStereo => 24 | CtlSetInnovationSave _ => 0 | CtlGetPiGain | CtlGetExc => 16 | _ => 4 end.

Definition creq_align (r : ctl_req) : Z := match r with CtlSetHandlerStereo => 8 | _ => 4 end.

Definition creq_pre (STEREO : Z) (m : mem) (S : Z) (d : dec_state bptr) (P : Z) (r : ctl_req) : Prop :=
match r with
| CtlSetEnh v | CtlSetSamplingRate v | CtlSetWideband v =>
exists w : word, rw_cells asegs m P [C4 w] /\ bv_unsigned w mod 2^32 = v mod 2^32 /\ - 2^31 <= v < 2^31
| CtlGetFrameSize | CtlGetSamplingRate | CtlGetLookahead | CtlGetDtxStatus => exists w : word, rw_cells asegs m P [C4 w]
| CtlSetHandlerStereo => exists pad : word,
rw_cells asegs m P [C4 (Z_to_bv 64 SPEEX_INBAND_STEREO); C4 pad; C8 (Z_to_bv 64 A_speex_std_stereo_request_handler); C8 (Z_to_bv 64 STEREO)]
| CtlSetInnovationSave _ => True
| CtlGetPiGain => exists ws : list word, rw_cells asegs m P (f32 ws) /\ length ws = 4%nat
| CtlGetExc => (exists ws : list word, rw_cells asegs m P (f32 ws) /\ length ws = 4%nat) /\ EXCREADY m S d
end.
Definition creq_post (STEREO : Z) (m : mem) (P : Z) (r : ctl_req) (v : Z) : Prop :=
match r with
| CtlSetEnh v0 | CtlSetSamplingRate v0 | CtlSetWideband v0 =>
exists w : word, rw_cells asegs m P [C4 w] /\ bv_unsigned w mod 2^32 = v0 mod 2^32
| CtlGetFrameSize | CtlGetSamplingRate | CtlGetLookahead => rw_cells asegs m P [C4 (Z_to_bv 64 v)] /\ - 2^31 <= v < 2^31
| CtlGetDtxStatus => rw_cells asegs m P [C4 (Z_to_bv 64 v)] /\ (v = 0 \/ v = 1)
| CtlSetHandlerStereo => exists pad : word,
rw_cells asegs m P [C4 (Z_to_bv 64 SPEEX_INBAND_STEREO); C4 pad; C8 (Z_to_bv 64 A_speex_std_stereo_request_handler); C8 (Z_to_bv 64 STEREO)]
| CtlSetInnovationSave _ => True
| CtlGetPiGain | CtlGetExc => exists ws : list word, rw_cells asegs m P (f32 ws) /\ length ws = 4%nat
end.

Definition creq_grp1 (r : ctl_req) : bool :=
match r with CtlGetPiGain | CtlGetExc | CtlGetDtxStatus | CtlSetInnovationSave _ => false | _ => true end.

Definition creq_ivs (P : Z) (r : ctl_req) : list (Z * Z) :=
match r with CtlSetInnovationSave _ => [] | _ => [(P, P + creq_size r)] end.
Definition ctlW (lo usp P : Z) (r : ctl_req) (LBD : list block) : list (Z * Z) :=
(lo, usp) :: creq_ivs P r ++ blocks_ivs LBD.
Lemma ctlW_grp1 : forall lo usp P r LBD, creq_grp1 r = true -> ctlW lo usp P r LBD = (lo, usp) :: (P, P + creq_size r) :: blocks_ivs LBD.
Proof. intros lo usp P r LBD G. destruct r; try discriminate G; reflexivity. Qed.

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

Lemma C4_samebytes : forall m A (w1 w2 : word), rw_cells asegs m A [C4 w1] -> bv_unsigned w1 mod 2^32 = bv_unsigned w2 mod 2^32 -> rw_cells asegs m A [C4 w2].
Proof.
intros m A w1 w2 X E. eapply rw_cells_samebytes; [exact X| cbn; tauto| cbn [cells_bytes cbytes app]; rewrite (le4_eqm w2 w1) by (symmetry; exact E); reflexivity| reflexivity].
Qed.

Lemma sx32_lit : forall v, - 2^31 <= v < 2^31 -> sx32 (Z_to_bv 64 v) = Z_to_bv 64 v.
Proof.
intros v Hv. unfold sx32. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
rewrite swrap32_mod64, swrap32_small by lia. reflexivity.
Qed.

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

Lemma outside_ctlW : forall lo usp P r L a,
outside (ctlW lo usp P r L) a <-> ~ (lo <= a < usp) /\ ~ (P <= a < P + creq_size r) /\ (forall b, In b L -> ~ (blk_addr b <= a < blk_addr b + blk_size b)).
Proof.
intros. unfold ctlW. rewrite outside_cons. cbn [fst snd].
destruct r; cbn [creq_ivs creq_size app]; rewrite ?outside_cons, outside_blocks_ivs; cbn [fst snd]; try tauto.
split; [intros [A B]; split; [exact A| split; [lia| exact B]]| intros (A & _ & B); exact (conj A B)].
Qed.

Definition NBCTL_STACK : Z := 96.

Definition rctl_post (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (usp : Z)
(OUT STEREO S : Z) (d : dec_state bptr) (LBD : list block) (r : ctl_req) (P lo : Z) (m : mem) : machine_state -> Prop :=
fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem),
ms' = MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (ret_pc ra) fc' None m' (seg_rom asegs)
/\ munch (ctlW lo usp P r LBD) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ frm0 fc' /\ stk asegs m' lo usp
/\ DREP OUT STEREO m' S (snd (speex_decoder_ctl d r)) LBD
/\ creq_post STEREO m' P r (fst (speex_decoder_ctl d r))
/\ (EXCREADY m S d -> EXCREADY m' S (snd (speex_decoder_ctl d r))).

Definition rctl_atP (Pr : ctl_req -> Prop) (d : dec_state bptr) : Prop :=
forall (OUT STEREO S : Z) (LBD : list block) (r : ctl_req) (P lo usp : Z)
(ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem),
Pr r ->
DREP OUT STEREO m S d LBD -> creq_ok OUT P r -> creq_pre STEREO m S d P r ->
(forall b, In b LBD -> ablk m lo b) ->
aobj asegs m P (creq_size r) -> P mod creq_align r = 0 ->
aobj asegs m A_speex_nb_mode 96 ->
(P + creq_size r <= lo \/ usp <= P) ->
(forall b, In b LBD -> P + creq_size r <= blk_addr b \/ blk_addr b + blk_size b <= P) ->
stk asegs m lo usp -> SH_HI <= lo -> lo <= usp - NBCTL_STACK -> usp < 2^63 ->
client_consts m -> lib_consts m -> mem_inv asegs m -> frm0 fc ->
evt asegs (rctl_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 usp OUT STEREO S d LBD r P lo m)
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 S) (Z_to_bv 64 (ctl_req_code r)) (Z_to_bv 64 P) a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_speex_decoder_ctl) fc None m (seg_rom asegs)).

Lemma munch_weaken_to : forall W W' m m', munch W m m' -> (forall x, outside W' x -> outside W x) -> munch W' m m'.
Proof. intros W W' m m' MU SUB. eapply munch_weaken; [| exact MU]. exact SUB. Qed.
