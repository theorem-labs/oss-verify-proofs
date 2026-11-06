(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1d7 X1cx X1cy X1cj X1dd X1cs.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X081.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X0ys.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ys.
Import ListNotations.
Open Scope Z_scope.

#[local] Notation mem := (word -> option byte).

Definition io_rw : list (Z * list cell) :=
[ (0xfdf08, [C8 (Z_to_bv 64 0xf6df8); C8 (Z_to_bv 64 0xedcfc)])
; (0x103370, [C8 (Z_to_bv 64 0)]) ].

Definition io_ro : list (Z * list cell) :=
[ (0xf7f78, [C8 (Z_to_bv 64 0x97744); C8 (Z_to_bv 64 0x44a64)])
; (0xfc010, [C8 (Z_to_bv 64 0x1007b0)])
; (0xfc0e8, [C8 (Z_to_bv 64 0xe6cc4); C8 (Z_to_bv 64 0)])
; (0xfcd78, [C8 (Z_to_bv 64 0xfc010); C8 (Z_to_bv 64 0)])
; (0xfce00, [C8 (Z_to_bv 64 0x100ab0); C8 (Z_to_bv 64 0x1023f0)])
; (0xfce88, [C8 (Z_to_bv 64 0xf7f88); C8 (Z_to_bv 64 0xf7f78)])
; (0xfdec8, [C8 (Z_to_bv 64 0xfdec8)])
; (0xfdf28, [C8 (Z_to_bv 64 0xf1040); C8 (Z_to_bv 64 0xedf30); C8 (Z_to_bv 64 0xf105c)])
; (0x1032d0, [C4 (Z_to_bv 64 1)])
; (0x19763c, [C1 (Z_to_bv 8 1)])
; (0x197960, [C1 (Z_to_bv 8 0)])

; (0xfdee8, [C8 (Z_to_bv 64 0xf16c4); C8 (Z_to_bv 64 0xf15f4)])
; (0x1976e6, [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)])

; (A_nb_mode, LC_nb_mode)
; (A_speex_nb_mode, LC_speex_nb_mode)
; (A_nb_submode1, LC_nb_submode1)
; (A_nb_submode2, LC_nb_submode2)
; (A_nb_submode3, LC_nb_submode3)
; (A_nb_submode4, LC_nb_submode4)
; (A_nb_submode5, LC_nb_submode5)
; (A_nb_submode6, LC_nb_submode6)
; (A_nb_submode7, LC_nb_submode7)
; (A_nb_submode8, LC_nb_submode8)
; (A_ltp_params_vlbr, LC_ltp_params_vlbr)
; (A_split_cb_nb_vlbr, LC_split_cb_nb_vlbr)
; (A_ltp_params_lbr, LC_ltp_params_lbr)
; (A_split_cb_nb_lbr, LC_split_cb_nb_lbr)
; (A_ltp_params_med, LC_ltp_params_med)
; (A_split_cb_nb_med, LC_split_cb_nb_med)
; (A_ltp_params_nb, LC_ltp_params_nb)
; (A_split_cb_nb, LC_split_cb_nb)
; (A_split_cb_sb, LC_split_cb_sb)
; (A_split_cb_nb_ulbr, LC_split_cb_nb_ulbr)
; (A_speex_wb_mode, LC_speex_wb_mode)
; (A_speex_uwb_mode, LC_speex_uwb_mode)
; (A_speex_mode_list, LC_speex_mode_list)
; (A_wb_submode1, LC_wb_submode1)
; (A_wb_submode2, LC_wb_submode2)
; (A_wb_submode3, LC_wb_submode3)
; (A_wb_submode4, LC_wb_submode4)
; (A_sb_wb_mode, LC_sb_wb_mode)
; (A_split_cb_high_lbr, LC_split_cb_high_lbr)
; (A_split_cb_high, LC_split_cb_high)
; (A_sb_uwb_mode, LC_sb_uwb_mode)
; (GOT_f41a0, LC_GOT_f41a0)
; (GOT_f41a8, LC_GOT_f41a8)
; (GOT_f41b0, LC_GOT_f41b0)
; (GOT_f41b8, LC_GOT_f41b8)
; (GOT_f41c0, LC_GOT_f41c0)
; (GOT_f41c8, LC_GOT_f41c8)
; (GOT_f41d0, LC_GOT_f41d0)
; (GOT_f41d8, LC_GOT_f41d8)
; (GOT_f41e0, LC_GOT_f41e0)
; (GOT_f41e8, LC_GOT_f41e8)
; (GOT_f41f0, LC_GOT_f41f0)
; (GOT_f41f8, LC_GOT_f41f8)
; (GOT_f4200, LC_GOT_f4200)
; (GOT_f4208, LC_GOT_f4208)
].

Definition io_acc : list (Z * Z) :=
[ (0x10f54, 10)
; (0x1529e, 4)
; (0x165c0, 128)
; (0x1ac77, 33)
; (0x1f32d, 21)
; (0x1f342, 23)
; (0x219c0, 128)
; (0x22ad2, 7)
; (0x23708, 16)
; (0xfc010, 8)
; (0x628100, 16)    ].

Definition io_consts (m : mem) : Prop :=
Forall (fun p => rw_cells bsegs m (fst p) (snd p)) io_rw
/\ Forall (fun p => ro_cells bsegs m (fst p) (snd p)) io_ro
/\ Forall (fun r => acc bsegs m (fst r) (snd r)) io_acc.

Definition io_rngs : list (Z * Z) :=
[ (0xfdf08, 0xfdf18); (0x103370, 0x103378);
(0xf7f78, 0xf7f88); (0xfc010, 0xfc018); (0xfc0e8, 0xfc0f8); (0xfcd78, 0xfcd88); (0xfce00, 0xfce10); (0xfce88, 0xfce98);
(0xfdec8, 0xfded0); (0xfdf28, 0xfdf40); (0x1032d0, 0x1032d4); (0x19763c, 0x19763d); (0x197960, 0x197961);

(0xfdee8, 0xfdef8); (0x1976e6, 0x1976e8);

(0xf8380, 0xf8450); (0xf8480, 0xf84e0); (0xf8500, 0xf8558); (0xf8580, 0xf85d8); (0xf8600, 0xf8658); (0xf8680, 0xf86d8);
(0xf8700, 0xf8758); (0xf8780, 0xf87d8); (0xf8800, 0xf8858); (0xf8880, 0xf88d8); (0xf8900, 0xf8910); (0xf8920, 0xf8938);
(0xf8960, 0xf8970); (0xf8980, 0xf8998); (0xf89c0, 0xf89d0); (0xf89e0, 0xf89f8); (0xf8a20, 0xf8a30); (0xf8a40, 0xf8a58);
(0xf8a80, 0xf8a98); (0xf8ac0, 0xf8ad8); (0xf8b00, 0xf8b60); (0xf8b80, 0xf8be0); (0xf8c00, 0xf8c18); (0xf8c40, 0xf8c98);
(0xf8cc0, 0xf8d18); (0xf8d40, 0xf8d98); (0xf8dc0, 0xf8e18); (0xf8e40, 0xf8f18); (0xf8f40, 0xf8f58); (0xf8f80, 0xf8f98);
(0xf8fc0, 0xf9098); (0xfcd90, 0xfcd98); (0xfcd98, 0xfcda0); (0xfcda0, 0xfcda8); (0xfcda8, 0xfcdb0); (0xfcdb0, 0xfcdb8);
(0xfcdb8, 0xfcdc0); (0xfcdc0, 0xfcdc8); (0xfcdc8, 0xfcdd0); (0xfcdd0, 0xfcdd8); (0xfcdd8, 0xfcde0); (0xfcde0, 0xfcde8);
(0xfcde8, 0xfcdf0); (0xfcdf0, 0xfcdf8); (0xfcdf8, 0xfce00) ].

Lemma io_rngs_of : io_rngs = map (fun p => (fst p, fst p + Z.of_nat (cells_size (snd p)))) (io_rw ++ io_ro).
Proof. reflexivity. Qed.

Section Get.
Variable m : mem.
Hypothesis H : io_consts m.
Lemma io_rw_at : forall a cs, In (a, cs) io_rw -> rw_cells bsegs m a cs.
Proof. intros a cs Hin. destruct H as (X & _ & _). exact (proj1 (Forall_forall _ _) X (a, cs) Hin). Qed.
Lemma io_ro_at : forall a cs, In (a, cs) io_ro -> ro_cells bsegs m a cs.
Proof. intros a cs Hin. destruct H as (_ & X & _). exact (proj1 (Forall_forall _ _) X (a, cs) Hin). Qed.
Lemma io_acc_at : forall a n, In (a, n) io_acc -> acc bsegs m a n.
Proof. intros a n Hin. destruct H as (_ & _ & X). exact (proj1 (Forall_forall _ _) X (a, n) Hin). Qed.
End Get.

Ltac io_in := cbn [io_rw io_ro io_acc In]; repeat (first [ left; reflexivity | right ]).
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.

#[local] Notation mem := (word -> option byte).

Definition io_rw : list (Z * list cell) :=
[ (0xf5688, [C8 (Z_to_bv 64 0xee584); C8 (Z_to_bv 64 0xe5488)])
; (0xfab30, [C8 (Z_to_bv 64 0)]) ].

Definition io_ro : list (Z * list cell) :=
[ (0xef708, [C8 (Z_to_bv 64 0x97490); C8 (Z_to_bv 64 0x44978)])
; (0xf3790, [C8 (Z_to_bv 64 0xf7f30)])
; (0xf3868, [C8 (Z_to_bv 64 0xde594); C8 (Z_to_bv 64 0)])
; (0xf44f8, [C8 (Z_to_bv 64 0xf3790); C8 (Z_to_bv 64 0)])
; (0xf4580, [C8 (Z_to_bv 64 0xf8230); C8 (Z_to_bv 64 0xf9bb0)])
; (0xf4608, [C8 (Z_to_bv 64 0xef718); C8 (Z_to_bv 64 0xef708)])
; (0xf5648, [C8 (Z_to_bv 64 0xf5648)])
; (0xf56a8, [C8 (Z_to_bv 64 0xe87cc); C8 (Z_to_bv 64 0xe56bc); C8 (Z_to_bv 64 0xe87e8)])
; (0xfaa90, [C4 (Z_to_bv 64 1)])
; (0x18edfc, [C1 (Z_to_bv 8 1)])
; (0x18f120, [C1 (Z_to_bv 8 0)])

; (0xf5668, [C8 (Z_to_bv 64 0xe8e50); C8 (Z_to_bv 64 0xe8d80)])
; (0x18eea6, [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)])

; (A_nb_mode, LC_nb_mode)
; (A_speex_nb_mode, LC_speex_nb_mode)
; (A_nb_submode1, LC_nb_submode1)
; (A_nb_submode2, LC_nb_submode2)
; (A_nb_submode3, LC_nb_submode3)
; (A_nb_submode4, LC_nb_submode4)
; (A_nb_submode5, LC_nb_submode5)
; (A_nb_submode6, LC_nb_submode6)
; (A_nb_submode7, LC_nb_submode7)
; (A_nb_submode8, LC_nb_submode8)
; (A_ltp_params_vlbr, LC_ltp_params_vlbr)
; (A_split_cb_nb_vlbr, LC_split_cb_nb_vlbr)
; (A_ltp_params_lbr, LC_ltp_params_lbr)
; (A_split_cb_nb_lbr, LC_split_cb_nb_lbr)
; (A_ltp_params_med, LC_ltp_params_med)
; (A_split_cb_nb_med, LC_split_cb_nb_med)
; (A_ltp_params_nb, LC_ltp_params_nb)
; (A_split_cb_nb, LC_split_cb_nb)
; (A_split_cb_sb, LC_split_cb_sb)
; (A_split_cb_nb_ulbr, LC_split_cb_nb_ulbr)
; (A_speex_wb_mode, LC_speex_wb_mode)
; (A_speex_uwb_mode, LC_speex_uwb_mode)
; (A_speex_mode_list, LC_speex_mode_list)
; (A_wb_submode1, LC_wb_submode1)
; (A_wb_submode2, LC_wb_submode2)
; (A_wb_submode3, LC_wb_submode3)
; (A_wb_submode4, LC_wb_submode4)
; (A_sb_wb_mode, LC_sb_wb_mode)
; (A_split_cb_high_lbr, LC_split_cb_high_lbr)
; (A_split_cb_high, LC_split_cb_high)
; (A_sb_uwb_mode, LC_sb_uwb_mode)
; (GOT_f41a0, LC_GOT_f41a0)
; (GOT_f41a8, LC_GOT_f41a8)
; (GOT_f41b0, LC_GOT_f41b0)
; (GOT_f41b8, LC_GOT_f41b8)
; (GOT_f41c0, LC_GOT_f41c0)
; (GOT_f41c8, LC_GOT_f41c8)
; (GOT_f41d0, LC_GOT_f41d0)
; (GOT_f41d8, LC_GOT_f41d8)
; (GOT_f41e0, LC_GOT_f41e0)
; (GOT_f41e8, LC_GOT_f41e8)
; (GOT_f41f0, LC_GOT_f41f0)
; (GOT_f41f8, LC_GOT_f41f8)
; (GOT_f4200, LC_GOT_f4200)
; (GOT_f4208, LC_GOT_f4208)
].

Definition io_acc : list (Z * Z) :=
[ (0x10f3c, 10)
; (0x151ae, 4)
; (0x164c0, 128)
; (0x1ab8e, 33)
; (0x1f2f3, 21)
; (0x1f308, 23)
; (0x21980, 128)
; (0x22a98, 7)
; (0x236c8, 16)
; (0xf3790, 8)
; (0x61f8c0, 16)    ].

Definition io_consts (m : mem) : Prop :=
Forall (fun p => rw_cells asegs m (fst p) (snd p)) io_rw
/\ Forall (fun p => ro_cells asegs m (fst p) (snd p)) io_ro
/\ Forall (fun r => acc asegs m (fst r) (snd r)) io_acc.

Definition io_rngs : list (Z * Z) :=
[ (0xf5688, 0xf5698); (0xfab30, 0xfab38);
(0xef708, 0xef718); (0xf3790, 0xf3798); (0xf3868, 0xf3878); (0xf44f8, 0xf4508); (0xf4580, 0xf4590); (0xf4608, 0xf4618);
(0xf5648, 0xf5650); (0xf56a8, 0xf56c0); (0xfaa90, 0xfaa94); (0x18edfc, 0x18edfd); (0x18f120, 0x18f121);

(0xf5668, 0xf5678); (0x18eea6, 0x18eea8);

(0xefb00, 0xefbd0); (0xefc00, 0xefc60); (0xefc80, 0xefcd8); (0xefd00, 0xefd58); (0xefd80, 0xefdd8); (0xefe00, 0xefe58);
(0xefe80, 0xefed8); (0xeff00, 0xeff58); (0xeff80, 0xeffd8); (0xf0000, 0xf0058); (0xf0080, 0xf0090); (0xf00a0, 0xf00b8);
(0xf00e0, 0xf00f0); (0xf0100, 0xf0118); (0xf0140, 0xf0150); (0xf0160, 0xf0178); (0xf01a0, 0xf01b0); (0xf01c0, 0xf01d8);
(0xf0200, 0xf0218); (0xf0240, 0xf0258); (0xf0280, 0xf02e0); (0xf0300, 0xf0360); (0xf0380, 0xf0398); (0xf03c0, 0xf0418);
(0xf0440, 0xf0498); (0xf04c0, 0xf0518); (0xf0540, 0xf0598); (0xf05c0, 0xf0698); (0xf06c0, 0xf06d8); (0xf0700, 0xf0718);
(0xf0740, 0xf0818); (0xf4510, 0xf4518); (0xf4518, 0xf4520); (0xf4520, 0xf4528); (0xf4528, 0xf4530); (0xf4530, 0xf4538);
(0xf4538, 0xf4540); (0xf4540, 0xf4548); (0xf4548, 0xf4550); (0xf4550, 0xf4558); (0xf4558, 0xf4560); (0xf4560, 0xf4568);
(0xf4568, 0xf4570); (0xf4570, 0xf4578); (0xf4578, 0xf4580) ].

Lemma io_rngs_of : io_rngs = map (fun p => (fst p, fst p + Z.of_nat (cells_size (snd p)))) (io_rw ++ io_ro).
Proof. reflexivity. Qed.

Section Get.
Variable m : mem.
Hypothesis H : io_consts m.
Lemma io_rw_at : forall a cs, In (a, cs) io_rw -> rw_cells asegs m a cs.
Proof. intros a cs Hin. destruct H as (X & _ & _). exact (proj1 (Forall_forall _ _) X (a, cs) Hin). Qed.
Lemma io_ro_at : forall a cs, In (a, cs) io_ro -> ro_cells asegs m a cs.
Proof. intros a cs Hin. destruct H as (_ & X & _). exact (proj1 (Forall_forall _ _) X (a, cs) Hin). Qed.
Lemma io_acc_at : forall a n, In (a, n) io_acc -> acc asegs m a n.
Proof. intros a n Hin. destruct H as (_ & _ & X). exact (proj1 (Forall_forall _ _) X (a, n) Hin). Qed.
End Get.

Ltac io_in := cbn [io_rw io_ro io_acc In]; repeat (first [ left; reflexivity | right ]).
