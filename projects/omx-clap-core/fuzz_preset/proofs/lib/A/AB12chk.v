(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* This file states instruction words of the task's compiled program (third-party object code). *)
(* Modified by Theorem Labs, 2026-10: GENERATED for omx-clap-core/fuzz_preset's ASan image (ELF sha256 bff8519bbe3ea0e4) by the internal file gen_ab12chk.py. Asserted against the image: the 12 code fields and x_sealed by the word (bytes) the image holds at the FIELD's address, through a table built from the image by vm_compute; each of the 12 stops by the shortest run of words ending at it that occurs ONCE in the text, so a permuted or wrong stop fails; shadow_off by the lui at SealedReserveShadow + 48 and its decoded immediate; rw_lo / rw_len / img_lo / n_res by the image's own reserved segments; TFIB_TEXT_LO = a_entry; the three sniff fields 0. img_hi is pinned by A/AB1h.v tfib_res_top. *)
(* Generator: tools/startup/gen_ab12chk.py sha256 88e574150b21aefb6b2cad771656e4d6d1c95059d585e56579dbd8324a49744b; image sha256 bff8519bbe3ea0e4d8edf35fa48015b5846960886633a77a5e9f86cb565bd590; A/AB12.v blob 4fcba06002cf7bd1d5affd24f5443161daa69be5. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1a YK1e YP02 YK09 YK0c YK0e YK0f YA0c YA0e YA0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB12 AB1h.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations. Import APC.
Open Scope bv_scope.
Open Scope Z_scope.
Definition chk_addrs : list Z := [a_entry TFIB; x_imemset TFIB; x_imemcpy TFIB; x_memset TFIB; x_memcpy TFIB; x_memiszero TFIB; x_istrncpy TFIB; x_popfree TFIB; x_envscan TFIB; x_envscan_k TFIB; x_pnscan TFIB; x_pnscan_k TFIB; nth 0 (stops_more TFIB) 0; nth 0 (stops_more TFIB) 0 - 4; nth 1 (stops_more TFIB) 0; nth 1 (stops_more TFIB) 0 - 4; nth 1 (stops_more TFIB) 0 - 8; nth 2 (stops_more TFIB) 0; nth 2 (stops_more TFIB) 0 - 4; nth 3 (stops_more TFIB) 0; nth 3 (stops_more TFIB) 0 - 4; nth 4 (stops_more TFIB) 0; nth 4 (stops_more TFIB) 0 - 4; nth 5 (stops_more TFIB) 0; nth 5 (stops_more TFIB) 0 - 4; nth 5 (stops_more TFIB) 0 - 8; nth 5 (stops_more TFIB) 0 - 12; nth 6 (stops_more TFIB) 0; nth 6 (stops_more TFIB) 0 - 4; nth 6 (stops_more TFIB) 0 - 8; nth 7 (stops_more TFIB) 0; nth 7 (stops_more TFIB) 0 - 4; nth 8 (stops_more TFIB) 0; nth 8 (stops_more TFIB) 0 - 4; nth 9 (stops_more TFIB) 0; nth 9 (stops_more TFIB) 0 - 4; nth 10 (stops_more TFIB) 0; nth 10 (stops_more TFIB) 0 - 4; nth 10 (stops_more TFIB) 0 - 8; nth 10 (stops_more TFIB) 0 - 12; nth 11 (stops_more TFIB) 0; nth 11 (stops_more TFIB) 0 - 4; 0x5affc].
Definition chk_tbl : ctable := Eval vm_compute in (fold_right (fun p t => build_table tfibsegs p 1 t) TEmpty chk_addrs).
Lemma chk_tbl_eq : chk_tbl = fold_right (fun p t => build_table tfibsegs p 1 t) TEmpty chk_addrs.
Proof. vm_cast_no_check (eq_refl chk_tbl). Qed.
Lemma chk_tbl_ok : table_ok tfibsegs chk_tbl.
Proof.
rewrite chk_tbl_eq. unfold chk_addrs. cbn [fold_right].
repeat (apply build_table_ok; [vm_compute; discriminate|]). apply table_ok_empty.
Qed.
(* x_sealed is DATA (.rodata), which fetch_word does not read: its nine bytes "<sealed>\0", read from the image *)
Lemma chk_x_sealed : memory_read tfibsegs (Z_to_bv 64 (x_sealed TFIB)) 9 = Some (List.map (Z_to_bv 8) [60; 115; 101; 97; 108; 101; 100; 62; 0]).
Proof. vm_compute. reflexivity. Qed.
Lemma chk_a_entry : fetch_word tfibsegs (Z_to_bv 64 (a_entry TFIB)) = Some (Z_to_bv 32 0xfffdf197).
Proof. apply chk_tbl_ok. vm_compute. reflexivity. Qed.
Lemma chk_x_imemset : fetch_word tfibsegs (Z_to_bv 64 (x_imemset TFIB)) = Some (Z_to_bv 32 0x00a666b3).
Proof. apply chk_tbl_ok. vm_compute. reflexivity. Qed.
Lemma chk_x_imemcpy : fetch_word tfibsegs (Z_to_bv 64 (x_imemcpy TFIB)) = Some (Z_to_bv 32 0x02060063).
Proof. apply chk_tbl_ok. vm_compute. reflexivity. Qed.
Lemma chk_x_memset : fetch_word tfibsegs (Z_to_bv 64 (x_memset TFIB)) = Some (Z_to_bv 32 0x0e060a63).
Proof. apply chk_tbl_ok. vm_compute. reflexivity. Qed.
Lemma chk_x_memcpy : fetch_word tfibsegs (Z_to_bv 64 (x_memcpy TFIB)) = Some (Z_to_bv 32 0x0035f693).
Proof. apply chk_tbl_ok. vm_compute. reflexivity. Qed.
Lemma chk_x_memiszero : fetch_word tfibsegs (Z_to_bv 64 (x_memiszero TFIB)) = Some (Z_to_bv 32 0xff010113).
Proof. apply chk_tbl_ok. vm_compute. reflexivity. Qed.
Lemma chk_x_istrncpy : fetch_word tfibsegs (Z_to_bv 64 (x_istrncpy TFIB)) = Some (Z_to_bv 32 0x06060663).
Proof. apply chk_tbl_ok. vm_compute. reflexivity. Qed.
Lemma chk_x_popfree : fetch_word tfibsegs (Z_to_bv 64 (x_popfree TFIB)) = Some (Z_to_bv 32 0x00465713).
Proof. apply chk_tbl_ok. vm_compute. reflexivity. Qed.
Lemma chk_x_envscan : fetch_word tfibsegs (Z_to_bv 64 (x_envscan TFIB)) = Some (Z_to_bv 32 0x0004b503).
Proof. apply chk_tbl_ok. vm_compute. reflexivity. Qed.
Lemma chk_x_envscan_k : fetch_word tfibsegs (Z_to_bv 64 (x_envscan_k TFIB)) = Some (Z_to_bv 32 0x00570517).
Proof. apply chk_tbl_ok. vm_compute. reflexivity. Qed.
Lemma chk_x_pnscan : fetch_word tfibsegs (Z_to_bv 64 (x_pnscan TFIB)) = Some (Z_to_bv 32 0xfff5c683).
Proof. apply chk_tbl_ok. vm_compute. reflexivity. Qed.
Lemma chk_x_pnscan_k : fetch_word tfibsegs (Z_to_bv 64 (x_pnscan_k TFIB)) = Some (Z_to_bv 32 0x03010513).
Proof. apply chk_tbl_ok. vm_compute. reflexivity. Qed.
Lemma chk_stop_0 : fetch_word tfibsegs (Z_to_bv 64 (nth 0 (stops_more TFIB) 0)) = Some (Z_to_bv 32 0x0000006f).
Proof. apply chk_tbl_ok. vm_compute. reflexivity. Qed.
Lemma chk_stop_0_m1 : fetch_word tfibsegs (Z_to_bv 64 (nth 0 (stops_more TFIB) 0 - 4)) = Some (Z_to_bv 32 0x00051a63).
Proof. apply chk_tbl_ok. vm_compute. reflexivity. Qed.
Lemma chk_stop_1 : fetch_word tfibsegs (Z_to_bv 64 (nth 1 (stops_more TFIB) 0)) = Some (Z_to_bv 32 0x0000006f).
Proof. apply chk_tbl_ok. vm_compute. reflexivity. Qed.
Lemma chk_stop_1_m1 : fetch_word tfibsegs (Z_to_bv 64 (nth 1 (stops_more TFIB) 0 - 4)) = Some (Z_to_bv 32 0x04051a63).
Proof. apply chk_tbl_ok. vm_compute. reflexivity. Qed.
Lemma chk_stop_1_m2 : fetch_word tfibsegs (Z_to_bv 64 (nth 1 (stops_more TFIB) 0 - 8)) = Some (Z_to_bv 32 0x00052503).
Proof. apply chk_tbl_ok. vm_compute. reflexivity. Qed.
Lemma chk_stop_2 : fetch_word tfibsegs (Z_to_bv 64 (nth 2 (stops_more TFIB) 0)) = Some (Z_to_bv 32 0x0000006f).
Proof. apply chk_tbl_ok. vm_compute. reflexivity. Qed.
Lemma chk_stop_2_m1 : fetch_word tfibsegs (Z_to_bv 64 (nth 2 (stops_more TFIB) 0 - 4)) = Some (Z_to_bv 32 0x04051c63).
Proof. apply chk_tbl_ok. vm_compute. reflexivity. Qed.
Lemma chk_stop_3 : fetch_word tfibsegs (Z_to_bv 64 (nth 3 (stops_more TFIB) 0)) = Some (Z_to_bv 32 0x0000006f).
Proof. apply chk_tbl_ok. vm_compute. reflexivity. Qed.
Lemma chk_stop_3_m1 : fetch_word tfibsegs (Z_to_bv 64 (nth 3 (stops_more TFIB) 0 - 4)) = Some (Z_to_bv 32 0x02051863).
Proof. apply chk_tbl_ok. vm_compute. reflexivity. Qed.
Lemma chk_stop_4 : fetch_word tfibsegs (Z_to_bv 64 (nth 4 (stops_more TFIB) 0)) = Some (Z_to_bv 32 0x0000006f).
Proof. apply chk_tbl_ok. vm_compute. reflexivity. Qed.
Lemma chk_stop_4_m1 : fetch_word tfibsegs (Z_to_bv 64 (nth 4 (stops_more TFIB) 0 - 4)) = Some (Z_to_bv 32 0x00051e63).
Proof. apply chk_tbl_ok. vm_compute. reflexivity. Qed.
Lemma chk_stop_5 : fetch_word tfibsegs (Z_to_bv 64 (nth 5 (stops_more TFIB) 0)) = Some (Z_to_bv 32 0x0000006f).
Proof. apply chk_tbl_ok. vm_compute. reflexivity. Qed.
Lemma chk_stop_5_m1 : fetch_word tfibsegs (Z_to_bv 64 (nth 5 (stops_more TFIB) 0 - 4)) = Some (Z_to_bv 32 0x00051463).
Proof. apply chk_tbl_ok. vm_compute. reflexivity. Qed.
Lemma chk_stop_5_m2 : fetch_word tfibsegs (Z_to_bv 64 (nth 5 (stops_more TFIB) 0 - 8)) = Some (Z_to_bv 32 0x00052503).
Proof. apply chk_tbl_ok. vm_compute. reflexivity. Qed.
Lemma chk_stop_5_m3 : fetch_word tfibsegs (Z_to_bv 64 (nth 5 (stops_more TFIB) 0 - 12)) = Some (Z_to_bv 32 0xec453503).
Proof. apply chk_tbl_ok. vm_compute. reflexivity. Qed.
Lemma chk_stop_6 : fetch_word tfibsegs (Z_to_bv 64 (nth 6 (stops_more TFIB) 0)) = Some (Z_to_bv 32 0x0000006f).
Proof. apply chk_tbl_ok. vm_compute. reflexivity. Qed.
Lemma chk_stop_6_m1 : fetch_word tfibsegs (Z_to_bv 64 (nth 6 (stops_more TFIB) 0 - 4)) = Some (Z_to_bv 32 0x04051a63).
Proof. apply chk_tbl_ok. vm_compute. reflexivity. Qed.
Lemma chk_stop_6_m2 : fetch_word tfibsegs (Z_to_bv 64 (nth 6 (stops_more TFIB) 0 - 8)) = Some (Z_to_bv 32 0xeb452503).
Proof. apply chk_tbl_ok. vm_compute. reflexivity. Qed.
Lemma chk_stop_7 : fetch_word tfibsegs (Z_to_bv 64 (nth 7 (stops_more TFIB) 0)) = Some (Z_to_bv 32 0x0000006f).
Proof. apply chk_tbl_ok. vm_compute. reflexivity. Qed.
Lemma chk_stop_7_m1 : fetch_word tfibsegs (Z_to_bv 64 (nth 7 (stops_more TFIB) 0 - 4)) = Some (Z_to_bv 32 0x06051263).
Proof. apply chk_tbl_ok. vm_compute. reflexivity. Qed.
Lemma chk_stop_8 : fetch_word tfibsegs (Z_to_bv 64 (nth 8 (stops_more TFIB) 0)) = Some (Z_to_bv 32 0x0000006f).
Proof. apply chk_tbl_ok. vm_compute. reflexivity. Qed.
Lemma chk_stop_8_m1 : fetch_word tfibsegs (Z_to_bv 64 (nth 8 (stops_more TFIB) 0 - 4)) = Some (Z_to_bv 32 0x0e051a63).
Proof. apply chk_tbl_ok. vm_compute. reflexivity. Qed.
Lemma chk_stop_9 : fetch_word tfibsegs (Z_to_bv 64 (nth 9 (stops_more TFIB) 0)) = Some (Z_to_bv 32 0x0000006f).
Proof. apply chk_tbl_ok. vm_compute. reflexivity. Qed.
Lemma chk_stop_9_m1 : fetch_word tfibsegs (Z_to_bv 64 (nth 9 (stops_more TFIB) 0 - 4)) = Some (Z_to_bv 32 0x06051663).
Proof. apply chk_tbl_ok. vm_compute. reflexivity. Qed.
Lemma chk_stop_10 : fetch_word tfibsegs (Z_to_bv 64 (nth 10 (stops_more TFIB) 0)) = Some (Z_to_bv 32 0x0000006f).
Proof. apply chk_tbl_ok. vm_compute. reflexivity. Qed.
Lemma chk_stop_10_m1 : fetch_word tfibsegs (Z_to_bv 64 (nth 10 (stops_more TFIB) 0 - 4)) = Some (Z_to_bv 32 0x00051463).
Proof. apply chk_tbl_ok. vm_compute. reflexivity. Qed.
Lemma chk_stop_10_m2 : fetch_word tfibsegs (Z_to_bv 64 (nth 10 (stops_more TFIB) 0 - 8)) = Some (Z_to_bv 32 0x00052503).
Proof. apply chk_tbl_ok. vm_compute. reflexivity. Qed.
Lemma chk_stop_10_m3 : fetch_word tfibsegs (Z_to_bv 64 (nth 10 (stops_more TFIB) 0 - 12)) = Some (Z_to_bv 32 0xe9c53503).
Proof. apply chk_tbl_ok. vm_compute. reflexivity. Qed.
Lemma chk_stop_11 : fetch_word tfibsegs (Z_to_bv 64 (nth 11 (stops_more TFIB) 0)) = Some (Z_to_bv 32 0x0000006f).
Proof. apply chk_tbl_ok. vm_compute. reflexivity. Qed.
Lemma chk_stop_11_m1 : fetch_word tfibsegs (Z_to_bv 64 (nth 11 (stops_more TFIB) 0 - 4)) = Some (Z_to_bv 32 0x00008067).
Proof. apply chk_tbl_ok. vm_compute. reflexivity. Qed.
(* shadow_off: the lui at SealedReserveShadow + 48 (0x5affc) loads it; its word and decoded form *)
Lemma chk_shadow_lui : fetch_word tfibsegs (Z_to_bv 64 (0x5affc)) = Some (Z_to_bv 32 0x7fff84b7).
Proof. apply chk_tbl_ok. vm_compute. reflexivity. Qed.
Lemma chk_shadow_lui_decode : decode_any (0x7fff84b7%bv : bv 32) = Some (Lui 9 524280, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma chk_shadow_off : 524280 * 4096 = shadow_off TFIB.
Proof. reflexivity. Qed.
(* the geometry fields, pinned to the image's own reserved segments (segments_reserved, computed from its PT_LOADs) *)
Lemma chk_rw : nth 3 (segments_reserved TSEGS) (Z_to_bv 64 0, Z_to_bv 64 0) = (Z_to_bv 64 (rw_lo TFIB), Z_to_bv 64 (rw_len TFIB)).
Proof. vm_compute. reflexivity. Qed.
Lemma chk_img_lo : fst (nth 0 (segments_reserved TSEGS) (Z_to_bv 64 0, Z_to_bv 64 0)) = Z_to_bv 64 (img_lo TFIB).
Proof. vm_compute. reflexivity. Qed.
Lemma chk_n_res : length (segments_reserved TSEGS) = n_res TFIB.
Proof. vm_compute. reflexivity. Qed.
(* TFIB_TEXT_LO is the entry; TFIB_TEXT_N is the whole executable text (.text end - entry) / 4 *)
Lemma chk_text_lo : TFIB_TEXT_LO = a_entry TFIB.
Proof. reflexivity. Qed.
(* x_sniff, sniff_tab, sniff_cell are 0: image A has no sniff table, as the donor's are 0 *)
Lemma chk_sniff : x_sniff TFIB = 0 /\ sniff_tab TFIB = 0 /\ sniff_cell TFIB = 0.
Proof. repeat split; reflexivity. Qed.
