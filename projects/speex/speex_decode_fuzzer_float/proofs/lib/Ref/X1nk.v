(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt X1rh X1re.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Open Scope Z_scope.

Definition mem := word -> option byte.
Definition NBSTATE_SIZEOF : Z := 2968.
Definition NB_EXC_OFF : Z := 1368.

Record nb_junk := NBJ {
j_last_ol_gain : word; j_excbuf : list word; j_exc : Z;
j_old_qlsp : list word; j_interp_qlpc : list word; j_mem_sp : list word; j_mem_hp : list word; j_pi_gain : list word;
j_levels : list word  ; j_last_pitch : word; j_last_pitch_gain : word;
j_pitch_gain_buf : list word; j_seed : word; j_pad1 : list byte;
j_cbs : list byte  ;
j_ucb : list byte * list byte  ;
j_voc : list word  ; j_pad2 : list byte }.

Definition cb_cells (func data : Z) (j : list byte * list byte) : list cell :=
[CB 8 (fst j); C8 (Z_to_bv 64 func); C8 (Z_to_bv 64 data); CB 16 (snd j)].

Fixpoint cbs_cells (k : nat) (stereo_func stereo_data : Z) (stereo : bool) (js : list (list byte * list byte)) : list cell :=
match k, js with
| S k', j :: js' =>
let i := (16 - Z.of_nat k)%Z in
(if (i =? 9) && stereo then cb_cells stereo_func stereo_data j else cb_cells 0 0 j) ++ cbs_cells k' stereo_func stereo_data stereo js'
| _, _ => []
end.

Lemma cb_cells_size : forall f d jj, cells_size (cb_cells f d jj) = 40%nat.
Proof. reflexivity. Qed.
Lemma cbs_cells_size : forall k sf sd b js, (k <= length js)%nat ->
cells_size (cbs_cells k sf sd b js) = (40 * k)%nat.
Proof.
induction k as [|k IH]; intros sf sd b [|j0 js] Hk.
- reflexivity. - reflexivity. - cbn [length] in Hk. lia.
- cbn [length] in Hk. cbn [cbs_cells]. cbv zeta. rewrite cells_size_app, IH by lia.
destruct (_ && _); rewrite cb_cells_size; lia.
Qed.

Section Rep.
Context {RCEIL : RunCeiling}.
Context {ptr : Type}.
Variable segs : list Segment.

Variables (NB_MODE_PTR
NB_SUBMODES_PTR
USER_HANDLER
STEREO_HANDLER       : Z).
Implicit Types st : nb_state ptr.

Definition nb_hdr_cells st (last_ol_gain : word) : list cell :=
[C8 (Z_to_bv 64 NB_MODE_PTR); C4 (Z_to_bv 64 (nb_first st)); C4 (Z_to_bv 64 (nb_count_lost st));
C4 (Z_to_bv 64 (nb_sampling_rate st)); C4 last_ol_gain; C8 (Z_to_bv 64 0)].
Definition nb_isave_ptr (OUT : Z) st : Z := match nb_innov_save st with None => 0 | Some k => OUT + 4 * k end.
Definition nb_cfg_cells st (pad : list byte) : list cell :=
[C4 (Z_to_bv 64 (nb_encode_submode st)); CB 4 pad; C8 (Z_to_bv 64 NB_SUBMODES_PTR);
C4 (Z_to_bv 64 (nb_submodeID st)); C4 (Z_to_bv 64 (nb_lpc_enh_enabled st))].
Definition nb_tail_cells st (pad : list byte) : list cell :=
[C4 (Z_to_bv 64 (nb_voc_offset st)); C4 (Z_to_bv 64 (nb_dtx_enabled st)); C4 (Z_to_bv 64 (nb_isWideband st));
C4 (Z_to_bv 64 (nb_highpass_enabled st)); CB 4 pad].

Definition cbs_ok (STEREO : Z) (stereo_cb : bool) (bs : list byte) : Prop :=
exists js, length js = 16%nat /\ Forall (fun p => length (fst p) = 8%nat /\ length (snd p) = 16%nat) js /\
bs = cells_bytes (cbs_cells 16 STEREO_HANDLER STEREO stereo_cb js).
Definition nb_ucb_cells (ju : list byte * list byte) : list cell :=
cb_cells USER_HANDLER 0 ju.

Definition nb_cells (ST OUT STEREO : Z) st (j : nb_junk) : list cell :=
nb_hdr_cells st (j_last_ol_gain j)
++ f32 (j_excbuf j)
++ [C8 (Z_to_bv 64 (j_exc j))]
++ f32 (j_old_qlsp j) ++ f32 (j_interp_qlpc j) ++ f32 (j_mem_sp j) ++ f32 (j_mem_hp j) ++ f32 (j_pi_gain j)
++ [C8 (Z_to_bv 64 (nb_isave_ptr OUT st))]
++ f32 (j_levels j)
++ [C4 (j_last_pitch j); C4 (j_last_pitch_gain j)]
++ f32 (j_pitch_gain_buf j)
++ [C4 (Z_to_bv 64 (nb_pitch_gain_buf_idx st))] ++ [C4 (j_seed j)] ++ nb_cfg_cells st (j_pad1 j)
++ [CB 640 (j_cbs j)]
++ nb_ucb_cells (j_ucb j)
++ f32 (j_voc j)
++ nb_tail_cells st (j_pad2 j).

Definition nb_junk_ok (j : nb_junk) : Prop :=
length (j_excbuf j) = 500%nat /\ length (j_old_qlsp j) = 10%nat /\ length (j_interp_qlpc j) = 10%nat /\
length (j_mem_sp j) = 10%nat /\ length (j_mem_hp j) = 2%nat /\ length (j_pi_gain j) = 4%nat /\
length (j_levels j) = 3%nat /\ length (j_pitch_gain_buf j) = 3%nat /\ length (j_pad1 j) = 4%nat /\
length (j_cbs j) = 640%nat /\ (length (fst (j_ucb j)) = 8%nat /\ length (snd (j_ucb j)) = 16%nat) /\
length (j_voc j) = 3%nat /\ length (j_pad2 j) = 4%nat.

Definition nb_inv st : Prop :=
nb_count_lost st = 0 /\ nb_encode_submode st = 1 /\ nb_highpass_enabled st = 1 /\
(nb_first st = 0 \/ nb_first st = 1) /\
0 <= nb_voc_offset st <= 143 /\ 0 <= nb_pitch_gain_buf_idx st <= 2 /\ 0 <= nb_submodeID st <= 8 /\
(nb_dtx_enabled st = 0 \/ nb_dtx_enabled st = 1) /\ (nb_isWideband st = 0 \/ nb_isWideband st = 1) /\
(nb_lpc_enh_enabled st = 0 \/ nb_lpc_enh_enabled st = 1) /\
- 2^31 <= nb_sampling_rate st < 2^31 /\
match nb_innov_save st with None => True | Some k => 160 <= k end.

Definition nbstate_rep (m : mem) (ST OUT STEREO : Z) st : Prop :=
ST mod 8 = 0 /\ 0 < ST /\ nb_inv st /\
exists j, nb_junk_ok j /\ cbs_ok STEREO (nb_stereo_cb st) (j_cbs j) /\ rw_cells segs m ST (nb_cells ST OUT STEREO st j).

#[using="Type"] Lemma nb_cells_size : forall ST OUT STEREO st j, nb_junk_ok j -> cells_size (nb_cells ST OUT STEREO st j) = 2968%nat.
Proof.
intros ST OUT STEREO st j sfH_; first [ sf_destruct 13%nat sfH_ as E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 E12 E13 | sf_fb; destruct sfH_ as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13) ].
unfold nb_cells, nb_ucb_cells. rewrite !cells_size_app, !cells_size_f32, E1, E2, E3, E4, E5, E6, E7, E8, E12.
rewrite cb_cells_size. cbn [cells_size csize nb_hdr_cells nb_cfg_cells nb_tail_cells Nat.add Nat.mul]. reflexivity.
Qed.

Definition nb_pieces (m : mem) (ST OUT STEREO : Z) st (j : nb_junk) : Prop :=
rw_cells segs m ST (nb_hdr_cells st (j_last_ol_gain j))
/\ rw_cells segs m (ST + 32) (f32 (j_excbuf j))
/\ rw_cells segs m (ST + 2032) [C8 (Z_to_bv 64 (j_exc j))]
/\ rw_cells segs m (ST + 2040) (f32 (j_old_qlsp j))
/\ rw_cells segs m (ST + 2080) (f32 (j_interp_qlpc j))
/\ rw_cells segs m (ST + 2120) (f32 (j_mem_sp j))
/\ rw_cells segs m (ST + 2160) (f32 (j_mem_hp j))
/\ rw_cells segs m (ST + 2168) (f32 (j_pi_gain j))
/\ rw_cells segs m (ST + 2184) [C8 (Z_to_bv 64 (nb_isave_ptr OUT st))]
/\ rw_cells segs m (ST + 2192) (f32 (j_levels j))
/\ rw_cells segs m (ST + 2204) [C4 (j_last_pitch j); C4 (j_last_pitch_gain j)]
/\ rw_cells segs m (ST + 2212) (f32 (j_pitch_gain_buf j))
/\ rw_cells segs m (ST + 2224) [C4 (Z_to_bv 64 (nb_pitch_gain_buf_idx st))]
/\ rw_cells segs m (ST + 2228) [C4 (j_seed j)]
/\ rw_cells segs m (ST + 2232) (nb_cfg_cells st (j_pad1 j))
/\ rw_cells segs m (ST + 2256) [CB 640 (j_cbs j)]
/\ rw_cells segs m (ST + 2896) (nb_ucb_cells (j_ucb j))
/\ rw_cells segs m (ST + 2936) (f32 (j_voc j))
/\ rw_cells segs m (ST + 2948) (nb_tail_cells st (j_pad2 j)).

Local Ltac zlits_in H :=
repeat match type of H with context [Z.of_nat ?n] => let v := eval cbv in (Z.of_nat n) in change (Z.of_nat n) with v in H end;
repeat rewrite <- Z.add_assoc in H;
repeat match type of H with context [Z.add (Zpos ?a) (Zpos ?b)] =>
let v := eval cbv in (Z.add (Zpos a) (Zpos b)) in change (Z.add (Zpos a) (Zpos b)) with v in H end.
Local Ltac zlits_goal :=
repeat match goal with |- context [Z.of_nat ?n] => let v := eval cbv in (Z.of_nat n) in change (Z.of_nat n) with v end;
repeat rewrite <- Z.add_assoc;
repeat match goal with |- context [Z.add (Zpos ?a) (Zpos ?b)] =>
let v := eval cbv in (Z.add (Zpos a) (Zpos b)) in change (Z.add (Zpos a) (Zpos b)) with v end.

#[using="Type"] Lemma nb_pieces_of_cells : forall m ST OUT STEREO st j, nb_junk_ok j ->
rw_cells segs m ST (nb_cells ST OUT STEREO st j) -> nb_pieces m ST OUT STEREO st j.
Proof.
intros m ST OUT STEREO st j JOK H.
pose proof JOK as sfP_; first [ sf_destruct 13%nat sfP_ as E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 E12 E13 | sf_fb; destruct sfP_ as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13) ].
unfold nb_cells in H. unfold nb_pieces.
repeat lazymatch type of H with
| rw_cells _ _ _ (_ ++ _) =>
apply rw_cells_app in H;
let H0 := fresh "P" in destruct H as [H0 H];
rewrite ?cells_size_app, ?cells_size_f32, ?E1, ?E2, ?E3, ?E4, ?E5, ?E6, ?E7, ?E8, ?E12 in H;
cbn [cells_size csize Nat.add Nat.mul nb_hdr_cells nb_cfg_cells nb_ucb_cells cb_cells] in H; zlits_in H
end.
repeat match goal with |- _ /\ _ => split end; assumption.
Qed.

#[using="Type"] Lemma nb_cells_of_pieces : forall m ST OUT STEREO st j, nb_junk_ok j ->
nb_pieces m ST OUT STEREO st j -> rw_cells segs m ST (nb_cells ST OUT STEREO st j).
Proof.
intros m ST OUT STEREO st j JOK H.
pose proof JOK as sfP_; first [ sf_destruct 13%nat sfP_ as E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 E12 E13 | sf_fb; destruct sfP_ as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13) ].
first [ sf_destruct 19%nat H as P0 P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 | sf_fb; destruct H as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18) ].
unfold nb_cells.
repeat (apply rw_cells_join; [assumption|];
rewrite ?cells_size_app, ?cells_size_f32, ?E1, ?E2, ?E3, ?E4, ?E5, ?E6, ?E7, ?E8, ?E12;
cbn [cells_size csize Nat.add Nat.mul nb_hdr_cells nb_cfg_cells nb_ucb_cells cb_cells]; zlits_goal).
assumption.
Qed.

#[using="Type"] Lemma nb_pieces_iff : forall m ST OUT STEREO st j, nb_junk_ok j ->
(rw_cells segs m ST (nb_cells ST OUT STEREO st j) <-> nb_pieces m ST OUT STEREO st j).
Proof. intros; split; [apply nb_pieces_of_cells | apply nb_cells_of_pieces]; assumption. Qed.
End Rep.
