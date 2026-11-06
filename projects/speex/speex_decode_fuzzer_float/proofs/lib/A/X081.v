(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1d7 X1cx X1cy X1cj X1dd X1cs.

Module B_TWIN.

Import ListNotations.
Open Scope Z_scope.

Local Notation w := (Z_to_bv 64) (only parsing).

Definition A_nb_mode : Z := 0xf8380.
Definition LC_nb_mode : list cell :=
[C4 (w 160); C4 (w 40); C4 (w 10); C4 (w 17); C4 (w 144); C4 (w 0x3f6b851f); C4 (w 0x3f19999a); C4 (w 0x3951b717); C8 (w 0x0); C8 (w 0xf8500); C8 (w 0xf8580); C8 (w 0xf8600); C8 (w 0xf8680); C8 (w 0xf8700); C8 (w 0xf8780); C8 (w 0xf8800); C8 (w 0xf8880); C8 (w 0x0); C8 (w 0x0); C8 (w 0x0); C8 (w 0x0); C8 (w 0x0); C8 (w 0x0); C8 (w 0x0); C4 (w 5); C4 (w 1); C4 (w 8); C4 (w 2); C4 (w 3); C4 (w 3); C4 (w 4); C4 (w 4); C4 (w 5); C4 (w 5); C4 (w 6); C4 (w 7)].
Definition A_speex_nb_mode : Z := 0xf8480.
Definition LC_speex_nb_mode : list cell :=
[C8 (w 0xf8380); C8 (w 0x98ce8); C8 (w 0x238c0); C4 (w 0); C4 (w 4); C8 (w 0x9a134); C8 (w 0x9a774); C8 (w 0x9c0d8); C8 (w 0xa03b0); C8 (w 0xa08d4); C8 (w 0xa16a8); C8 (w 0x9a7b4); C8 (w 0xa08d8)].
Definition A_nb_submode1 : Z := 0xf8500.
Definition LC_nb_submode1 : list cell :=
[C4 (w 0); C4 (w 1); C4 (w 0); C4 (w 0); C8 (w 0xb4244); C8 (w 0xb4818); C8 (w 0xad104); C8 (w 0xad5dc); C8 (w 0x0); C8 (w 0xb2798); C8 (w 0xb29a8); C8 (w 0x0); C4 (w 0xbf800000); C4 (w 43)].
Definition A_nb_submode2 : Z := 0xf8580.
Definition LC_nb_submode2 : list cell :=
[C4 (w 0); C4 (w 0); C4 (w 0); C4 (w 0); C8 (w 0xb4244); C8 (w 0xb4818); C8 (w 0xaac94); C8 (w 0xac9c4); C8 (w 0xf8900); C8 (w 0xaf170); C8 (w 0xb22a8); C8 (w 0xf8920); C4 (w 0x3f19999a); C4 (w 119)].
Definition A_nb_submode3 : Z := 0xf8600.
Definition LC_nb_submode3 : list cell :=
[C4 (w (-1)); C4 (w 0); C4 (w 1); C4 (w 0); C8 (w 0xb4244); C8 (w 0xb4818); C8 (w 0xaac94); C8 (w 0xac9c4); C8 (w 0xf8960); C8 (w 0xaf170); C8 (w 0xb22a8); C8 (w 0xf8980); C4 (w 0x3f0ccccd); C4 (w 160)].
Definition A_nb_submode4 : Z := 0xf8680.
Definition LC_nb_submode4 : list cell :=
[C4 (w (-1)); C4 (w 0); C4 (w 1); C4 (w 0); C8 (w 0xb4244); C8 (w 0xb4818); C8 (w 0xaac94); C8 (w 0xac9c4); C8 (w 0xf89c0); C8 (w 0xaf170); C8 (w 0xb22a8); C8 (w 0xf89e0); C4 (w 0x3ee66666); C4 (w 220)].
Definition A_nb_submode5 : Z := 0xf8700.
Definition LC_nb_submode5 : list cell :=
[C4 (w (-1)); C4 (w 0); C4 (w 3); C4 (w 0); C8 (w 0xb2cb8); C8 (w 0xb3c2c); C8 (w 0xaac94); C8 (w 0xac9c4); C8 (w 0xf8a20); C8 (w 0xaf170); C8 (w 0xb22a8); C8 (w 0xf8a40); C4 (w 0x3e800000); C4 (w 300)].
Definition A_nb_submode6 : Z := 0xf8780.
Definition LC_nb_submode6 : list cell :=
[C4 (w (-1)); C4 (w 0); C4 (w 3); C4 (w 0); C8 (w 0xb2cb8); C8 (w 0xb3c2c); C8 (w 0xaac94); C8 (w 0xac9c4); C8 (w 0xf8a20); C8 (w 0xaf170); C8 (w 0xb22a8); C8 (w 0xf8a80); C4 (w 0x3e19999a); C4 (w 364)].
Definition A_nb_submode7 : Z := 0xf8800.
Definition LC_nb_submode7 : list cell :=
[C4 (w (-1)); C4 (w 0); C4 (w 3); C4 (w 1); C8 (w 0xb2cb8); C8 (w 0xb3c2c); C8 (w 0xaac94); C8 (w 0xac9c4); C8 (w 0xf8a20); C8 (w 0xaf170); C8 (w 0xb22a8); C8 (w 0xf8a40); C4 (w 0x3d4ccccd); C4 (w 492)].
Definition A_nb_submode8 : Z := 0xf8880.
Definition LC_nb_submode8 : list cell :=
[C4 (w 0); C4 (w 1); C4 (w 0); C4 (w 0); C8 (w 0xb4244); C8 (w 0xb4818); C8 (w 0xad104); C8 (w 0xad5dc); C8 (w 0x0); C8 (w 0xaf170); C8 (w 0xb22a8); C8 (w 0xf8ac0); C4 (w 0x3f000000); C4 (w 79)].
Definition A_ltp_params_vlbr : Z := 0xf8900.
Definition LC_ltp_params_vlbr : list cell :=
[C8 (w 0x256e0); C4 (w 5); C4 (w 0)].
Definition A_split_cb_nb_vlbr : Z := 0xf8920.
Definition LC_split_cb_nb_vlbr : list cell :=
[C4 (w 10); C4 (w 4); C8 (w 0x257a0); C4 (w 4); C4 (w 0)].
Definition A_ltp_params_lbr : Z := 0xf8960.
Definition LC_ltp_params_lbr : list cell :=
[C8 (w 0x256e0); C4 (w 5); C4 (w 7)].
Definition A_split_cb_nb_lbr : Z := 0xf8980.
Definition LC_split_cb_nb_lbr : list cell :=
[C4 (w 10); C4 (w 4); C8 (w 0x25880); C4 (w 5); C4 (w 0)].
Definition A_ltp_params_med : Z := 0xf89c0.
Definition LC_ltp_params_med : list cell :=
[C8 (w 0x256e0); C4 (w 5); C4 (w 7)].
Definition A_split_cb_nb_med : Z := 0xf89e0.
Definition LC_split_cb_nb_med : list cell :=
[C4 (w 8); C4 (w 5); C8 (w 0x25a20); C4 (w 7); C4 (w 0)].
Definition A_ltp_params_nb : Z := 0xf8a20.
Definition LC_ltp_params_nb : list cell :=
[C8 (w 0x25f40); C4 (w 7); C4 (w 7)].
Definition A_split_cb_nb : Z := 0xf8a40.
Definition LC_split_cb_nb : list cell :=
[C4 (w 5); C4 (w 8); C8 (w 0x261e0); C4 (w 6); C4 (w 0)].
Definition A_split_cb_sb : Z := 0xf8a80.
Definition LC_split_cb_sb : list cell :=
[C4 (w 5); C4 (w 8); C8 (w 0x26380); C4 (w 8); C4 (w 0)].
Definition A_split_cb_nb_ulbr : Z := 0xf8ac0.
Definition LC_split_cb_nb_ulbr : list cell :=
[C4 (w 20); C4 (w 2); C8 (w 0x269e0); C4 (w 5); C4 (w 0)].
Definition A_speex_wb_mode : Z := 0xf8b00.
Definition LC_speex_wb_mode : list cell :=
[C8 (w 0xf8e40); C8 (w 0xb54f0); C8 (w 0x26d20); C4 (w 1); C4 (w 4); C8 (w 0xb5770); C8 (w 0xb641c); C8 (w 0xb85c8); C8 (w 0xbcc10); C8 (w 0xbd428); C8 (w 0xbe6c0); C8 (w 0xb65c4); C8 (w 0xbd590)].
Definition A_speex_uwb_mode : Z := 0xf8b80.
Definition LC_speex_uwb_mode : list cell :=
[C8 (w 0xf8fc0); C8 (w 0xb54f0); C8 (w 0x26da0); C4 (w 2); C4 (w 4); C8 (w 0xb5770); C8 (w 0xb641c); C8 (w 0xb85c8); C8 (w 0xbcc10); C8 (w 0xbd428); C8 (w 0xbe6c0); C8 (w 0xb65c4); C8 (w 0xbd590)].
Definition A_speex_mode_list : Z := 0xf8c00.
Definition LC_speex_mode_list : list cell :=
[C8 (w 0xf8480); C8 (w 0xf8b00); C8 (w 0xf8b80)].
Definition A_wb_submode1 : Z := 0xf8c40.
Definition LC_wb_submode1 : list cell :=
[C4 (w 0); C4 (w 0); C4 (w 1); C4 (w 0); C8 (w 0xb4c04); C8 (w 0xb51dc); C8 (w 0x0); C8 (w 0x0); C8 (w 0x0); C8 (w 0x0); C8 (w 0x0); C8 (w 0x0); C4 (w 0xbf800000); C4 (w 36)].
Definition A_wb_submode2 : Z := 0xf8cc0.
Definition LC_wb_submode2 : list cell :=
[C4 (w 0); C4 (w 0); C4 (w 1); C4 (w 0); C8 (w 0xb4c04); C8 (w 0xb51dc); C8 (w 0x0); C8 (w 0x0); C8 (w 0x0); C8 (w 0xaf170); C8 (w 0xb22a8); C8 (w 0xf8f40); C4 (w 0xbf800000); C4 (w 112)].
Definition A_wb_submode3 : Z := 0xf8d40.
Definition LC_wb_submode3 : list cell :=
[C4 (w 0); C4 (w 0); C4 (w 1); C4 (w 0); C8 (w 0xb4c04); C8 (w 0xb51dc); C8 (w 0x0); C8 (w 0x0); C8 (w 0x0); C8 (w 0xaf170); C8 (w 0xb22a8); C8 (w 0xf8f80); C4 (w 0xbf800000); C4 (w 192)].
Definition A_wb_submode4 : Z := 0xf8dc0.
Definition LC_wb_submode4 : list cell :=
[C4 (w 0); C4 (w 0); C4 (w 1); C4 (w 1); C8 (w 0xb4c04); C8 (w 0xb51dc); C8 (w 0x0); C8 (w 0x0); C8 (w 0x0); C8 (w 0xaf170); C8 (w 0xb22a8); C8 (w 0xf8f80); C4 (w 0xbf800000); C4 (w 352)].
Definition A_sb_wb_mode : Z := 0xf8e40.
Definition LC_sb_wb_mode : list cell :=
[C8 (w 0xf8480); C4 (w 160); C4 (w 40); C4 (w 8); C4 (w 0x3f666666); C4 (w 0x3f19999a); C4 (w 0x3951b717); C4 (w 0x3f666666); CB 4 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]; C8 (w 0x0); C8 (w 0xf8c40); C8 (w 0xf8cc0); C8 (w 0xf8d40); C8 (w 0xf8dc0); C8 (w 0x0); C8 (w 0x0); C8 (w 0x0); C4 (w 3); C4 (w 1); C4 (w 8); C4 (w 2); C4 (w 3); C4 (w 4); C4 (w 5); C4 (w 5); C4 (w 6); C4 (w 6); C4 (w 7); C4 (w 7); C4 (w 1); C4 (w 1); C4 (w 1); C4 (w 1); C4 (w 1); C4 (w 1); C4 (w 2); C4 (w 2); C4 (w 3); C4 (w 3); C4 (w 4); CB 4 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]; C8 (w 0x24580); C4 (w 5); CB 4 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]].
Definition A_split_cb_high_lbr : Z := 0xf8f40.
Definition LC_split_cb_high_lbr : list cell :=
[C4 (w 10); C4 (w 4); C8 (w 0x27320); C4 (w 5); C4 (w 0)].
Definition A_split_cb_high : Z := 0xf8f80.
Definition LC_split_cb_high : list cell :=
[C4 (w 8); C4 (w 5); C8 (w 0x274c0); C4 (w 7); C4 (w 1)].
Definition A_sb_uwb_mode : Z := 0xf8fc0.
Definition LC_sb_uwb_mode : list cell :=
[C8 (w 0xf8b00); C4 (w 320); C4 (w 80); C4 (w 8); C4 (w 0x3f666666); C4 (w 0x3f19999a); C4 (w 0x3951b717); C4 (w 0x3f333333); CB 4 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]; C8 (w 0x0); C8 (w 0xf8c40); C8 (w 0x0); C8 (w 0x0); C8 (w 0x0); C8 (w 0x0); C8 (w 0x0); C8 (w 0x0); C4 (w 1); C4 (w 0); C4 (w 1); C4 (w 2); C4 (w 3); C4 (w 4); C4 (w 5); C4 (w 6); C4 (w 7); C4 (w 8); C4 (w 9); C4 (w 10); C4 (w 0); C4 (w 1); C4 (w 1); C4 (w 1); C4 (w 1); C4 (w 1); C4 (w 1); C4 (w 1); C4 (w 1); C4 (w 1); C4 (w 1); CB 4 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]; C8 (w 0x24680); C4 (w 2); CB 4 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]].

Definition GOT_f41a0 : Z := 0xfcd90.
Definition LC_GOT_f41a0 : list cell :=
[C8 (w 0xb2798)].
Definition GOT_f41a8 : Z := 0xfcd98.
Definition LC_GOT_f41a8 : list cell :=
[C8 (w 0x251c0)].
Definition GOT_f41b0 : Z := 0xfcda0.
Definition LC_GOT_f41b0 : list cell :=
[C8 (w 0x25440)].
Definition GOT_f41b8 : Z := 0xfcda8.
Definition LC_GOT_f41b8 : list cell :=
[C8 (w 0x991f0)].
Definition GOT_f41c0 : Z := 0xfcdb0.
Definition LC_GOT_f41c0 : list cell :=
[C8 (w 0x24380)].
Definition GOT_f41c8 : Z := 0xfcdb8.
Definition LC_GOT_f41c8 : list cell :=
[C8 (w 0x24880)].
Definition GOT_f41d0 : Z := 0xfcdc0.
Definition LC_GOT_f41d0 : list cell :=
[C8 (w 0x24ba0)].
Definition GOT_f41d8 : Z := 0xfcdc8.
Definition LC_GOT_f41d8 : list cell :=
[C8 (w 0x24d20)].
Definition GOT_f41e0 : Z := 0xfcdd0.
Definition LC_GOT_f41e0 : list cell :=
[C8 (w 0x24ea0)].
Definition GOT_f41e8 : Z := 0xfcdd8.
Definition LC_GOT_f41e8 : list cell :=
[C8 (w 0x25020)].
Definition GOT_f41f0 : Z := 0xfcde0.
Definition LC_GOT_f41f0 : list cell :=
[C8 (w 0xf8480)].
Definition GOT_f41f8 : Z := 0xfcde8.
Definition LC_GOT_f41f8 : list cell :=
[C8 (w 0xb2c68)].
Definition GOT_f4200 : Z := 0xfcdf0.
Definition LC_GOT_f4200 : list cell :=
[C8 (w 0x23f20)].
Definition GOT_f4208 : Z := 0xfcdf8.
Definition LC_GOT_f4208 : list cell :=
[C8 (w 0x23f80)].

Definition LIB_TABLES : list (Z * list cell) :=
[(A_nb_mode, LC_nb_mode);
(A_speex_nb_mode, LC_speex_nb_mode);
(A_nb_submode1, LC_nb_submode1);
(A_nb_submode2, LC_nb_submode2);
(A_nb_submode3, LC_nb_submode3);
(A_nb_submode4, LC_nb_submode4);
(A_nb_submode5, LC_nb_submode5);
(A_nb_submode6, LC_nb_submode6);
(A_nb_submode7, LC_nb_submode7);
(A_nb_submode8, LC_nb_submode8);
(A_ltp_params_vlbr, LC_ltp_params_vlbr);
(A_split_cb_nb_vlbr, LC_split_cb_nb_vlbr);
(A_ltp_params_lbr, LC_ltp_params_lbr);
(A_split_cb_nb_lbr, LC_split_cb_nb_lbr);
(A_ltp_params_med, LC_ltp_params_med);
(A_split_cb_nb_med, LC_split_cb_nb_med);
(A_ltp_params_nb, LC_ltp_params_nb);
(A_split_cb_nb, LC_split_cb_nb);
(A_split_cb_sb, LC_split_cb_sb);
(A_split_cb_nb_ulbr, LC_split_cb_nb_ulbr);
(A_speex_wb_mode, LC_speex_wb_mode);
(A_speex_uwb_mode, LC_speex_uwb_mode);
(A_speex_mode_list, LC_speex_mode_list);
(A_wb_submode1, LC_wb_submode1);
(A_wb_submode2, LC_wb_submode2);
(A_wb_submode3, LC_wb_submode3);
(A_wb_submode4, LC_wb_submode4);
(A_sb_wb_mode, LC_sb_wb_mode);
(A_split_cb_high_lbr, LC_split_cb_high_lbr);
(A_split_cb_high, LC_split_cb_high);
(A_sb_uwb_mode, LC_sb_uwb_mode);
(GOT_f41a0, LC_GOT_f41a0);
(GOT_f41a8, LC_GOT_f41a8);
(GOT_f41b0, LC_GOT_f41b0);
(GOT_f41b8, LC_GOT_f41b8);
(GOT_f41c0, LC_GOT_f41c0);
(GOT_f41c8, LC_GOT_f41c8);
(GOT_f41d0, LC_GOT_f41d0);
(GOT_f41d8, LC_GOT_f41d8);
(GOT_f41e0, LC_GOT_f41e0);
(GOT_f41e8, LC_GOT_f41e8);
(GOT_f41f0, LC_GOT_f41f0);
(GOT_f41f8, LC_GOT_f41f8);
(GOT_f4200, LC_GOT_f4200);
(GOT_f4208, LC_GOT_f4208)].

Definition lib_consts (m : word -> option byte) : Prop :=
Forall (fun t => ro_cells bsegs m (fst t) (snd t)) LIB_TABLES.

Lemma lib_const : forall m a cs, lib_consts m -> In (a, cs) LIB_TABLES -> ro_cells bsegs m a cs.
Proof. intros m a cs H HIn. exact (proj1 (Forall_forall _ _) H (a, cs) HIn). Qed.

Ltac lc_in := cbn [In LIB_TABLES]; repeat (first [left; reflexivity | right]).

End B_TWIN.

Import ListNotations.
Open Scope Z_scope.

Local Notation w := (Z_to_bv 64) (only parsing).

Definition A_nb_mode : Z := 0xefb00.
Definition LC_nb_mode : list cell :=
[C4 (w 160); C4 (w 40); C4 (w 10); C4 (w 17); C4 (w 144); C4 (w 0x3f6b851f); C4 (w 0x3f19999a); C4 (w 0x3951b717); C8 (w 0x0); C8 (w 0xefc80); C8 (w 0xefd00); C8 (w 0xefd80); C8 (w 0xefe00); C8 (w 0xefe80); C8 (w 0xeff00); C8 (w 0xeff80); C8 (w 0xf0000); C8 (w 0x0); C8 (w 0x0); C8 (w 0x0); C8 (w 0x0); C8 (w 0x0); C8 (w 0x0); C8 (w 0x0); C4 (w 5); C4 (w 1); C4 (w 8); C4 (w 2); C4 (w 3); C4 (w 3); C4 (w 4); C4 (w 4); C4 (w 5); C4 (w 5); C4 (w 6); C4 (w 7)].
Definition A_speex_nb_mode : Z := 0xefc00.
Definition LC_speex_nb_mode : list cell :=
[C8 (w 0xefb00); C8 (w 0x98690); C8 (w 0x23880); C4 (w 0); C4 (w 4); C8 (w 0x99640); C8 (w 0x99cb0); C8 (w 0x9b178); C8 (w 0x9e800); C8 (w 0x9eb78); C8 (w 0x9f634); C8 (w 0x99ce0); C8 (w 0x9eb7c)].
Definition A_nb_submode1 : Z := 0xefc80.
Definition LC_nb_submode1 : list cell :=
[C4 (w 0); C4 (w 1); C4 (w 0); C4 (w 0); C8 (w 0xae0a0); C8 (w 0xae630); C8 (w 0xa8564); C8 (w 0xa88d8); C8 (w 0x0); C8 (w 0xacad0); C8 (w 0xaccb4); C8 (w 0x0); C4 (w 0xbf800000); C4 (w 43)].
Definition A_nb_submode2 : Z := 0xefd00.
Definition LC_nb_submode2 : list cell :=
[C4 (w 0); C4 (w 0); C4 (w 0); C4 (w 0); C8 (w 0xae0a0); C8 (w 0xae630); C8 (w 0xa6be8); C8 (w 0xa7ff4); C8 (w 0xf0080); C8 (w 0xa9ed4); C8 (w 0xac694); C8 (w 0xf00a0); C4 (w 0x3f19999a); C4 (w 119)].
Definition A_nb_submode3 : Z := 0xefd80.
Definition LC_nb_submode3 : list cell :=
[C4 (w (-1)); C4 (w 0); C4 (w 1); C4 (w 0); C8 (w 0xae0a0); C8 (w 0xae630); C8 (w 0xa6be8); C8 (w 0xa7ff4); C8 (w 0xf00e0); C8 (w 0xa9ed4); C8 (w 0xac694); C8 (w 0xf0100); C4 (w 0x3f0ccccd); C4 (w 160)].
Definition A_nb_submode4 : Z := 0xefe00.
Definition LC_nb_submode4 : list cell :=
[C4 (w (-1)); C4 (w 0); C4 (w 1); C4 (w 0); C8 (w 0xae0a0); C8 (w 0xae630); C8 (w 0xa6be8); C8 (w 0xa7ff4); C8 (w 0xf0140); C8 (w 0xa9ed4); C8 (w 0xac694); C8 (w 0xf0160); C4 (w 0x3ee66666); C4 (w 220)].
Definition A_nb_submode5 : Z := 0xefe80.
Definition LC_nb_submode5 : list cell :=
[C4 (w (-1)); C4 (w 0); C4 (w 3); C4 (w 0); C8 (w 0xacf0c); C8 (w 0xadbec); C8 (w 0xa6be8); C8 (w 0xa7ff4); C8 (w 0xf01a0); C8 (w 0xa9ed4); C8 (w 0xac694); C8 (w 0xf01c0); C4 (w 0x3e800000); C4 (w 300)].
Definition A_nb_submode6 : Z := 0xeff00.
Definition LC_nb_submode6 : list cell :=
[C4 (w (-1)); C4 (w 0); C4 (w 3); C4 (w 0); C8 (w 0xacf0c); C8 (w 0xadbec); C8 (w 0xa6be8); C8 (w 0xa7ff4); C8 (w 0xf01a0); C8 (w 0xa9ed4); C8 (w 0xac694); C8 (w 0xf0200); C4 (w 0x3e19999a); C4 (w 364)].
Definition A_nb_submode7 : Z := 0xeff80.
Definition LC_nb_submode7 : list cell :=
[C4 (w (-1)); C4 (w 0); C4 (w 3); C4 (w 1); C8 (w 0xacf0c); C8 (w 0xadbec); C8 (w 0xa6be8); C8 (w 0xa7ff4); C8 (w 0xf01a0); C8 (w 0xa9ed4); C8 (w 0xac694); C8 (w 0xf01c0); C4 (w 0x3d4ccccd); C4 (w 492)].
Definition A_nb_submode8 : Z := 0xf0000.
Definition LC_nb_submode8 : list cell :=
[C4 (w 0); C4 (w 1); C4 (w 0); C4 (w 0); C8 (w 0xae0a0); C8 (w 0xae630); C8 (w 0xa8564); C8 (w 0xa88d8); C8 (w 0x0); C8 (w 0xa9ed4); C8 (w 0xac694); C8 (w 0xf0240); C4 (w 0x3f000000); C4 (w 79)].
Definition A_ltp_params_vlbr : Z := 0xf0080.
Definition LC_ltp_params_vlbr : list cell :=
[C8 (w 0x256e0); C4 (w 5); C4 (w 0)].
Definition A_split_cb_nb_vlbr : Z := 0xf00a0.
Definition LC_split_cb_nb_vlbr : list cell :=
[C4 (w 10); C4 (w 4); C8 (w 0x257a0); C4 (w 4); C4 (w 0)].
Definition A_ltp_params_lbr : Z := 0xf00e0.
Definition LC_ltp_params_lbr : list cell :=
[C8 (w 0x256e0); C4 (w 5); C4 (w 7)].
Definition A_split_cb_nb_lbr : Z := 0xf0100.
Definition LC_split_cb_nb_lbr : list cell :=
[C4 (w 10); C4 (w 4); C8 (w 0x25880); C4 (w 5); C4 (w 0)].
Definition A_ltp_params_med : Z := 0xf0140.
Definition LC_ltp_params_med : list cell :=
[C8 (w 0x256e0); C4 (w 5); C4 (w 7)].
Definition A_split_cb_nb_med : Z := 0xf0160.
Definition LC_split_cb_nb_med : list cell :=
[C4 (w 8); C4 (w 5); C8 (w 0x25a20); C4 (w 7); C4 (w 0)].
Definition A_ltp_params_nb : Z := 0xf01a0.
Definition LC_ltp_params_nb : list cell :=
[C8 (w 0x25f40); C4 (w 7); C4 (w 7)].
Definition A_split_cb_nb : Z := 0xf01c0.
Definition LC_split_cb_nb : list cell :=
[C4 (w 5); C4 (w 8); C8 (w 0x261e0); C4 (w 6); C4 (w 0)].
Definition A_split_cb_sb : Z := 0xf0200.
Definition LC_split_cb_sb : list cell :=
[C4 (w 5); C4 (w 8); C8 (w 0x26380); C4 (w 8); C4 (w 0)].
Definition A_split_cb_nb_ulbr : Z := 0xf0240.
Definition LC_split_cb_nb_ulbr : list cell :=
[C4 (w 20); C4 (w 2); C8 (w 0x269e0); C4 (w 5); C4 (w 0)].
Definition A_speex_wb_mode : Z := 0xf0280.
Definition LC_speex_wb_mode : list cell :=
[C8 (w 0xf05c0); C8 (w 0xaf104); C8 (w 0x26d20); C4 (w 1); C4 (w 4); C8 (w 0xaf318); C8 (w 0xaff34); C8 (w 0xb18e4); C8 (w 0xb51a0); C8 (w 0xb5960); C8 (w 0xb67bc); C8 (w 0xb00cc); C8 (w 0xb5ab8)].
Definition A_speex_uwb_mode : Z := 0xf0300.
Definition LC_speex_uwb_mode : list cell :=
[C8 (w 0xf0740); C8 (w 0xaf104); C8 (w 0x26da0); C4 (w 2); C4 (w 4); C8 (w 0xaf318); C8 (w 0xaff34); C8 (w 0xb18e4); C8 (w 0xb51a0); C8 (w 0xb5960); C8 (w 0xb67bc); C8 (w 0xb00cc); C8 (w 0xb5ab8)].
Definition A_speex_mode_list : Z := 0xf0380.
Definition LC_speex_mode_list : list cell :=
[C8 (w 0xefc00); C8 (w 0xf0280); C8 (w 0xf0300)].
Definition A_wb_submode1 : Z := 0xf03c0.
Definition LC_wb_submode1 : list cell :=
[C4 (w 0); C4 (w 0); C4 (w 1); C4 (w 0); C8 (w 0xae93c); C8 (w 0xaee84); C8 (w 0x0); C8 (w 0x0); C8 (w 0x0); C8 (w 0x0); C8 (w 0x0); C8 (w 0x0); C4 (w 0xbf800000); C4 (w 36)].
Definition A_wb_submode2 : Z := 0xf0440.
Definition LC_wb_submode2 : list cell :=
[C4 (w 0); C4 (w 0); C4 (w 1); C4 (w 0); C8 (w 0xae93c); C8 (w 0xaee84); C8 (w 0x0); C8 (w 0x0); C8 (w 0x0); C8 (w 0xa9ed4); C8 (w 0xac694); C8 (w 0xf06c0); C4 (w 0xbf800000); C4 (w 112)].
Definition A_wb_submode3 : Z := 0xf04c0.
Definition LC_wb_submode3 : list cell :=
[C4 (w 0); C4 (w 0); C4 (w 1); C4 (w 0); C8 (w 0xae93c); C8 (w 0xaee84); C8 (w 0x0); C8 (w 0x0); C8 (w 0x0); C8 (w 0xa9ed4); C8 (w 0xac694); C8 (w 0xf0700); C4 (w 0xbf800000); C4 (w 192)].
Definition A_wb_submode4 : Z := 0xf0540.
Definition LC_wb_submode4 : list cell :=
[C4 (w 0); C4 (w 0); C4 (w 1); C4 (w 1); C8 (w 0xae93c); C8 (w 0xaee84); C8 (w 0x0); C8 (w 0x0); C8 (w 0x0); C8 (w 0xa9ed4); C8 (w 0xac694); C8 (w 0xf0700); C4 (w 0xbf800000); C4 (w 352)].
Definition A_sb_wb_mode : Z := 0xf05c0.
Definition LC_sb_wb_mode : list cell :=
[C8 (w 0xefc00); C4 (w 160); C4 (w 40); C4 (w 8); C4 (w 0x3f666666); C4 (w 0x3f19999a); C4 (w 0x3951b717); C4 (w 0x3f666666); CB 4 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]; C8 (w 0x0); C8 (w 0xf03c0); C8 (w 0xf0440); C8 (w 0xf04c0); C8 (w 0xf0540); C8 (w 0x0); C8 (w 0x0); C8 (w 0x0); C4 (w 3); C4 (w 1); C4 (w 8); C4 (w 2); C4 (w 3); C4 (w 4); C4 (w 5); C4 (w 5); C4 (w 6); C4 (w 6); C4 (w 7); C4 (w 7); C4 (w 1); C4 (w 1); C4 (w 1); C4 (w 1); C4 (w 1); C4 (w 1); C4 (w 2); C4 (w 2); C4 (w 3); C4 (w 3); C4 (w 4); CB 4 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]; C8 (w 0x24580); C4 (w 5); CB 4 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]].
Definition A_split_cb_high_lbr : Z := 0xf06c0.
Definition LC_split_cb_high_lbr : list cell :=
[C4 (w 10); C4 (w 4); C8 (w 0x27320); C4 (w 5); C4 (w 0)].
Definition A_split_cb_high : Z := 0xf0700.
Definition LC_split_cb_high : list cell :=
[C4 (w 8); C4 (w 5); C8 (w 0x274c0); C4 (w 7); C4 (w 1)].
Definition A_sb_uwb_mode : Z := 0xf0740.
Definition LC_sb_uwb_mode : list cell :=
[C8 (w 0xf0280); C4 (w 320); C4 (w 80); C4 (w 8); C4 (w 0x3f666666); C4 (w 0x3f19999a); C4 (w 0x3951b717); C4 (w 0x3f333333); CB 4 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]; C8 (w 0x0); C8 (w 0xf03c0); C8 (w 0x0); C8 (w 0x0); C8 (w 0x0); C8 (w 0x0); C8 (w 0x0); C8 (w 0x0); C4 (w 1); C4 (w 0); C4 (w 1); C4 (w 2); C4 (w 3); C4 (w 4); C4 (w 5); C4 (w 6); C4 (w 7); C4 (w 8); C4 (w 9); C4 (w 10); C4 (w 0); C4 (w 1); C4 (w 1); C4 (w 1); C4 (w 1); C4 (w 1); C4 (w 1); C4 (w 1); C4 (w 1); C4 (w 1); C4 (w 1); CB 4 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]; C8 (w 0x24680); C4 (w 2); CB 4 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]].

Definition GOT_f41a0 : Z := 0xf4510.
Definition LC_GOT_f41a0 : list cell := [C8 (w 0xacad0)].
Definition GOT_f41a8 : Z := 0xf4518.
Definition LC_GOT_f41a8 : list cell := [C8 (w 0x251c0)].
Definition GOT_f41b0 : Z := 0xf4520.
Definition LC_GOT_f41b0 : list cell := [C8 (w 0x25440)].
Definition GOT_f41b8 : Z := 0xf4528.
Definition LC_GOT_f41b8 : list cell := [C8 (w 0x98a7c)].
Definition GOT_f41c0 : Z := 0xf4530.
Definition LC_GOT_f41c0 : list cell := [C8 (w 0x24380)].
Definition GOT_f41c8 : Z := 0xf4538.
Definition LC_GOT_f41c8 : list cell := [C8 (w 0x24880)].
Definition GOT_f41d0 : Z := 0xf4540.
Definition LC_GOT_f41d0 : list cell := [C8 (w 0x24ba0)].
Definition GOT_f41d8 : Z := 0xf4548.
Definition LC_GOT_f41d8 : list cell := [C8 (w 0x24d20)].
Definition GOT_f41e0 : Z := 0xf4550.
Definition LC_GOT_f41e0 : list cell := [C8 (w 0x24ea0)].
Definition GOT_f41e8 : Z := 0xf4558.
Definition LC_GOT_f41e8 : list cell := [C8 (w 0x25020)].
Definition GOT_f41f0 : Z := 0xf4560.
Definition LC_GOT_f41f0 : list cell := [C8 (w 0xefc00)].
Definition GOT_f41f8 : Z := 0xf4568.
Definition LC_GOT_f41f8 : list cell := [C8 (w 0xaced0)].
Definition GOT_f4200 : Z := 0xf4570.
Definition LC_GOT_f4200 : list cell := [C8 (w 0x23f20)].
Definition GOT_f4208 : Z := 0xf4578.
Definition LC_GOT_f4208 : list cell := [C8 (w 0x23f80)].

Definition LIB_TABLES : list (Z * list cell) :=
[(A_nb_mode, LC_nb_mode);
(A_speex_nb_mode, LC_speex_nb_mode);
(A_nb_submode1, LC_nb_submode1);
(A_nb_submode2, LC_nb_submode2);
(A_nb_submode3, LC_nb_submode3);
(A_nb_submode4, LC_nb_submode4);
(A_nb_submode5, LC_nb_submode5);
(A_nb_submode6, LC_nb_submode6);
(A_nb_submode7, LC_nb_submode7);
(A_nb_submode8, LC_nb_submode8);
(A_ltp_params_vlbr, LC_ltp_params_vlbr);
(A_split_cb_nb_vlbr, LC_split_cb_nb_vlbr);
(A_ltp_params_lbr, LC_ltp_params_lbr);
(A_split_cb_nb_lbr, LC_split_cb_nb_lbr);
(A_ltp_params_med, LC_ltp_params_med);
(A_split_cb_nb_med, LC_split_cb_nb_med);
(A_ltp_params_nb, LC_ltp_params_nb);
(A_split_cb_nb, LC_split_cb_nb);
(A_split_cb_sb, LC_split_cb_sb);
(A_split_cb_nb_ulbr, LC_split_cb_nb_ulbr);
(A_speex_wb_mode, LC_speex_wb_mode);
(A_speex_uwb_mode, LC_speex_uwb_mode);
(A_speex_mode_list, LC_speex_mode_list);
(A_wb_submode1, LC_wb_submode1);
(A_wb_submode2, LC_wb_submode2);
(A_wb_submode3, LC_wb_submode3);
(A_wb_submode4, LC_wb_submode4);
(A_sb_wb_mode, LC_sb_wb_mode);
(A_split_cb_high_lbr, LC_split_cb_high_lbr);
(A_split_cb_high, LC_split_cb_high);
(A_sb_uwb_mode, LC_sb_uwb_mode);
(GOT_f41a0, LC_GOT_f41a0);
(GOT_f41a8, LC_GOT_f41a8);
(GOT_f41b0, LC_GOT_f41b0);
(GOT_f41b8, LC_GOT_f41b8);
(GOT_f41c0, LC_GOT_f41c0);
(GOT_f41c8, LC_GOT_f41c8);
(GOT_f41d0, LC_GOT_f41d0);
(GOT_f41d8, LC_GOT_f41d8);
(GOT_f41e0, LC_GOT_f41e0);
(GOT_f41e8, LC_GOT_f41e8);
(GOT_f41f0, LC_GOT_f41f0);
(GOT_f41f8, LC_GOT_f41f8);
(GOT_f4200, LC_GOT_f4200);
(GOT_f4208, LC_GOT_f4208)].

Definition lib_consts (m : word -> option byte) : Prop :=
Forall (fun t => ro_cells asegs m (fst t) (snd t)) LIB_TABLES.

Lemma lib_const : forall m a cs, lib_consts m -> In (a, cs) LIB_TABLES -> ro_cells asegs m a cs.
Proof. intros m a cs H HIn. exact (proj1 (Forall_forall _ _) H (a, cs) HIn). Qed.

Ltac lc_in := cbn [In LIB_TABLES]; repeat (first [left; reflexivity | right]).

