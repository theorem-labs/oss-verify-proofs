(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1dh X1ch X1cg X1dk X1cr X1cs X1dg X1ck.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nw X1qz.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X05o X05p X09u X0ae X09j X09y X09x.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X110 X106 X10k X10j.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X110 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X106 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10k OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10j.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition RA_pgi_mm1 : Z := 0xc1b1c.
Definition RA_pgi_mm2 : Z := 0xc1b4c.
Definition RA_pgi_mm3 : Z := 0xc1b68.
Definition RA_pgi_lexp : Z := 0xc1b9c.
Definition RA_pgi_bexp : Z := 0xc1cb8.
Definition RA_pgi_mcpy : Z := 0xc1cd4.

Definition pgi_frame (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (j0 : list byte) (hs : list byte) : list cell :=
[CB 8 j0; C8 (wz (ogg_page_granulepos (ubytes hs))); C8 (Z_to_bv 64 (znth (ubytes hs) 18)); C8 (Z_to_bv 64 (znth (ubytes hs) 21)); C8 (Z_to_bv 64 (znth (ubytes hs) 5));
C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition stream_cells_r (Bd bfill bret L G lfill lpack lret : Z) (hdr : list byte) (os : stream_st bptr) : list cell :=
[C8 (wz Bd); C8 (wz (os_body_storage os)); C8 (wz bfill); C8 (wz bret);
C8 (wz L); C8 (wz G); C8 (wz (os_lacing_storage os)); C8 (wz lfill);
C8 (wz lpack); C8 (wz lret);
CB 284 hdr;
C4 (wz (os_header_fill os)); C4 (wz (os_e_o_s os)); C4 (wz (os_b_o_s os));
C8 (wz (os_serialno os)); C8 (wz (os_pageno os)); C8 (wz (os_packetno os)); C8 (wz (os_granulepos os))].

Lemma stream_cells_r_eq : forall Bd L G hdr (os : stream_st bptr),
stream_cells Bd L G hdr os = stream_cells_r Bd (os_body_fill os) (os_body_returned os) L G (os_lacing_fill os) (os_lacing_packet os) (os_lacing_returned os) hdr os.
Proof. reflexivity. Qed.

Lemma serialno_pieces : forall hs : list byte, (18 <= length hs)%nat ->
Z_to_bv 64 (Z.lor
((Z.lor (Z.lor (Z.land (Z.shiftl (bv_unsigned (nth (Z.to_nat 15) hs (Z_to_bv 8 0))) 8) 18446744073709551615)
(bv_unsigned (nth (Z.to_nat 14) hs (Z_to_bv 8 0))))
(Z.land (Z.shiftl (bv_unsigned (nth (Z.to_nat 16) hs (Z_to_bv 8 0))) 16) 18446744073709551615)) mod 2^64)
((bv_swrap 32 (Z.shiftl (bv_unsigned (nth (Z.to_nat 17) hs (Z_to_bv 8 0))) 24)) mod 2^64))
= Z_to_bv 64 (ogg_page_serialno (ubytes hs)).
Proof.
intros hs LEN. unfold ogg_page_serialno, le32_at.
change (zslice 14 4 (ubytes hs)) with (zslice 14 (Z.of_nat 4) (ubytes hs)).
rewrite !zslice_S by (rewrite ?zlength_ubytes; lia). rewrite zslice_0.
norm_lit_idx. rewrite !znth_ubytes by lia. cbn [le_val].
word_bits.
Qed.

Definition pgi_regs (x1 : word) (usp : Z) (gp tp x5 x6 x7 : word) (A : Z) (x9 x10 x11 x12 x13 x14 x15 x16 x17 : word) (blen Bp H : Z) (x22 : word) (hs : list byte) (x25 x28 x29 x30 x31 : word)
: bvmap 5 word :=
mkR x1 (Z_to_bv 64 (usp + -144)) gp tp x5 x6 x7 (Z_to_bv 64 A) x9 x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 (-1)) (Z_to_bv 64 blen) (Z_to_bv 64 Bp) (Z_to_bv 64 H) x22
(Z_to_bv 64 (znth (ubytes hs) 19)) (Z_to_bv 64 (znth (ubytes hs) 4)) x25 (Z_to_bv 64 (znth (ubytes hs) 26)) (Z_to_bv 64 (znth (ubytes hs) 20)) x28 x29 x30 x31.

Lemma pgi_w0 : forall (A G Dsy Bd L Gv usp lo : Z) (og : page) (shdr hs : list byte) (os : stream_st bptr)
(ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
(27 <= length hs)%nat -> length shdr = 284%nat -> stream_fields_ok os ->
rw_cells bsegs m A (stream_cells Bd L Gv shdr os) ->
rw_cells bsegs m G (page_cells Dsy og) -> bytes_at bsegs m (Dsy + pg_hdr og) hs ->
0 < A -> 0 < Bd -> Bd < 2^63 -> 0 <= Dsy -> 0 <= pg_hdr og -> Dsy + pg_hdr og + Z.of_nat (length hs) < 2^63 ->
stk bsegs m lo usp -> lo <= usp - 144 -> A + 408 <= lo -> G + 32 <= lo -> Dsy + pg_hdr og + Z.of_nat (length hs) <= lo -> mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem) (j0 : list byte) (v25 v22 : Z) (x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
ms = MS (pgi_regs x1 usp gp tp x5 x6 x7 A (Z_to_bv 64 (os_lacing_returned os)) (Z_to_bv 64 Bd) (Z_to_bv 64 (os_body_returned os)) x12 x13 x14 x15 x16 x17
(pg_body_len og) (Dsy + pg_hdr og + pg_header_len og) (Dsy + pg_hdr og) (Z_to_bv 64 v22) hs (Z_to_bv 64 v25) x28 x29 x30 x31)
F (Z_to_bv 64 0xc1b00) fc None m1 (seg_rom bsegs)
/\ munch [(usp + -144, usp)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo (usp + -144)
/\ rw_cells bsegs m1 (usp + -144) (pgi_frame ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j0 hs)
/\ 0 <= v25 < 2^64 /\ 0 <= v22 < 2^64 /\ Z_to_bv 64 (Z.lor v25 v22) = Z_to_bv 64 (ogg_page_serialno (ubytes hs)))
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 G) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_ogg_stream_pagein) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros LENH HL FOK OS OG HS A0 Bd0 BdT D0 PG0 TOPH ST LO ALO GLO HLO MI.
unfold A_ogg_stream_pagein, pgi_regs, pgi_frame.
pose proof FOK as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12). unfold int31 in *.
unfold page_cells, wz in OG. pose proof (rw_cells_bound _ _ _ _ OG) as GGB. cbn [cells_size csize Nat.add] in GGB.
unfold stream_cells, wz in OS. pose proof (rw_cells_bound _ _ _ _ OS) as GB. cbn [cells_size csize Nat.add] in GB.
pose proof HS as (HB0 & HB1 & HB). pose proof ST as (STa & STb & _).
pose proof (munch_refl [(usp + -144, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
carve_frame 144%nat ST.
apply (rw_cells_split_CB bsegs _ _ [] 144 _ [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
ato 0xc1a88.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
pose proof (bytes_at_read1 bsegs mx (Dsy + pg_hdr og) hs 4 _ HS ltac:(lia) ltac:(lia) eq_refl) as R4;
pose proof (bytes_at_read1 bsegs mx (Dsy + pg_hdr og) hs 5 _ HS ltac:(lia) ltac:(lia) eq_refl) as R5 end.
astep. astep. clear R4 R5.
ato 0xc110c.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
call (ogg_page_granulepos_spec _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mx G Dsy og hs) end.
all: try reflexivity. all: try exact OG. all: try exact HS. all: try lia. all: try assumption.
subst.
replace (ret_pc (Z_to_bv 64 0xc1a9c)) with (Z_to_bv 64 0xc1a9c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
ato 0xc1aa0. astep. sh_if.
ato 0xc1aac. astep. sh_if.
ato 0xc1ab8.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
pose proof (bytes_at_read1 bsegs mx (Dsy + pg_hdr og) hs 14 _ HS ltac:(lia) ltac:(lia) eq_refl) as R14;
pose proof (bytes_at_read1 bsegs mx (Dsy + pg_hdr og) hs 15 _ HS ltac:(lia) ltac:(lia) eq_refl) as R15;
pose proof (bytes_at_read1 bsegs mx (Dsy + pg_hdr og) hs 16 _ HS ltac:(lia) ltac:(lia) eq_refl) as R16;
pose proof (bytes_at_read1 bsegs mx (Dsy + pg_hdr og) hs 17 _ HS ltac:(lia) ltac:(lia) eq_refl) as R17;
pose proof (bytes_at_read1 bsegs mx (Dsy + pg_hdr og) hs 18 _ HS ltac:(lia) ltac:(lia) eq_refl) as R18 end.
ato 0xc1acc. clear R14 R15 R16 R17 R18.
astep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
pose proof (bytes_at_read1 bsegs mx (Dsy + pg_hdr og) hs 19 _ HS ltac:(lia) ltac:(lia) eq_refl) as R19;
pose proof (bytes_at_read1 bsegs mx (Dsy + pg_hdr og) hs 20 _ HS ltac:(lia) ltac:(lia) eq_refl) as R20;
pose proof (bytes_at_read1 bsegs mx (Dsy + pg_hdr og) hs 21 _ HS ltac:(lia) ltac:(lia) eq_refl) as R21 end.
ato 0xc1adc. clear R19 R20 R21.
astep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
pose proof (bytes_at_read1 bsegs mx (Dsy + pg_hdr og) hs 26 _ HS ltac:(lia) ltac:(lia) eq_refl) as R26 end.
astep. clear R26.
ato 0xc1b00.
rewrite <- !(znth_ubytes hs) in FR by lia.
lazymatch goal with |- context [Z_to_bv 64 (bv_swrap 32 ?e)] => rewrite <- (Z_to_bv_mod64 (bv_swrap 32 e)) end.
lazymatch goal with |- context [Z_to_bv 64 (Z.lor (Z.lor ?a ?b) ?c)] => rewrite <- (Z_to_bv_mod64 (Z.lor (Z.lor a b) c)) end.
apply evt_done. do 18 eexists. split; [rewrite <- !(znth_ubytes hs) by lia; reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|].
split; [apply Z.mod_pos_bound; lia|]. split; [apply Z.mod_pos_bound; lia|].
rewrite !znth_ubytes by lia. rewrite <- (serialno_pieces hs ltac:(lia)).
change (2^64) with 18446744073709551616. rewrite !mod64_land. reflexivity.
Qed.

Lemma pgi_b0 : forall (A usp blen Bp H : Z) (hs : list byte) (x1 gp tp x5 x6 x7 x9 x10 x12 x13 x14 x15 x16 x17 x22 x25 x28 x29 x30 x31 : word) F fc (m : mem),
evt bsegs (fun ms => ms = MS (pgi_regs x1 usp gp tp x5 x6 x7 A x9 x10 (Z_to_bv 64 0) x12 x13 x14 x15 x16 x17 blen Bp H x22 hs x25 x28 x29 x30 x31)
F (Z_to_bv 64 0xc1b20) fc None m (seg_rom bsegs))
(MS (pgi_regs x1 usp gp tp x5 x6 x7 A x9 x10 (Z_to_bv 64 0) x12 x13 x14 x15 x16 x17 blen Bp H x22 hs x25 x28 x29 x30 x31)
F (Z_to_bv 64 0xc1b00) fc None m (seg_rom bsegs)).
Proof.
intros. unfold pgi_regs.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
astep. apply evt_done. reflexivity.
Qed.

Lemma pgi_b1 : forall (A Bd bfill br L G lfill lpack lret usp blen Bp H : Z) (shdr hs : list byte) (os : stream_st bptr)
(x1 gp tp x5 x6 x7 x9 x12 x13 x14 x15 x16 x17 x22 x25 x28 x29 x30 x31 : word) F fc (m : mem),
rw_cells bsegs m A (stream_cells_r Bd bfill br L G lfill lpack lret shdr os) -> length shdr = 284%nat ->
0 < br -> bfill = br -> bfill < 2^63 -> 0 < A -> A + 408 < 2^63 -> mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem) (x12' x13' : word),
ms = MS (pgi_regs x1 usp gp tp x5 x6 x7 A x9 (Z_to_bv 64 Bd) (Z_to_bv 64 br) x12' x13' x14 x15 x16 x17 blen Bp H x22 hs x25 x28 x29 x30 x31)
F (Z_to_bv 64 0xc1b20) fc None m1 (seg_rom bsegs)
/\ munch [(A, A + 408)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
/\ rw_cells bsegs m1 A (stream_cells_r Bd (bfill - br) 0 L G lfill lpack lret shdr os))
(MS (pgi_regs x1 usp gp tp x5 x6 x7 A x9 (Z_to_bv 64 Bd) (Z_to_bv 64 br) x12 x13 x14 x15 x16 x17 blen Bp H x22 hs x25 x28 x29 x30 x31)
F (Z_to_bv 64 0xc1b00) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros OS HL BR BF BFT A0 AT MI.
unfold pgi_regs, stream_cells_r, wz in *.
pose proof (munch_refl [(A, A + 408)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
astep. sh_if.
ato 0xc1b10. astep. sh_if.
ato 0xc1b20.
apply evt_done. do 3 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. exact OS.
Qed.

Lemma pgi_b2 : forall (A Bd bfill br L G lfill lpack lret usp blen Bp H : Z) (shdr hs : list byte) (os : stream_st bptr)
(x1 gp tp x5 x6 x7 x9 x12 x13 x14 x15 x16 x17 x22 x25 x28 x29 x30 x31 : word) F fc (m : mem),
rw_cells bsegs m A (stream_cells_r Bd bfill br L G lfill lpack lret shdr os) -> length shdr = 284%nat ->
0 < br -> br < bfill -> bfill < 2^63 -> 0 < Bd -> Bd + br < 2^63 -> 0 < A -> A + 408 < 2^63 -> mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem),
ms = MS (pgi_regs (Z_to_bv 64 RA_pgi_mm1) usp gp tp x5 x6 x7 A x9 (Z_to_bv 64 Bd) (Z_to_bv 64 (Bd + br)) (Z_to_bv 64 (bfill - br)) (Z_to_bv 64 bfill) x14 x15 x16 x17
blen Bp H x22 hs x25 x28 x29 x30 x31)
F (Z_to_bv 64 oe_memmove) fc None m1 (seg_rom bsegs)
/\ munch [(A, A + 408)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
/\ rw_cells bsegs m1 A (stream_cells_r Bd (bfill - br) br L G lfill lpack lret shdr os))
(MS (pgi_regs x1 usp gp tp x5 x6 x7 A x9 (Z_to_bv 64 Bd) (Z_to_bv 64 br) x12 x13 x14 x15 x16 x17 blen Bp H x22 hs x25 x28 x29 x30 x31)
F (Z_to_bv 64 0xc1b00) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros OS HL BR BF BFT Bd0 BdT A0 AT MI.
unfold pgi_regs, RA_pgi_mm1, oe_memmove, stream_cells_r, wz in *.
pose proof (munch_refl [(A, A + 408)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
astep. sh_if.
ato 0xc1b10. astep. sh_if.
ato 0x663f8.
apply evt_done. eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. exact OS.
Qed.

Lemma pgi_b3 : forall (A Bd bfill br L G lfill lpack lret usp blen Bp H : Z) (shdr hs : list byte) (os : stream_st bptr)
(gp tp x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x22 x25 x28 x29 x30 x31 : word) F fc (m : mem),
rw_cells bsegs m A (stream_cells_r Bd bfill br L G lfill lpack lret shdr os) -> length shdr = 284%nat ->
0 < A -> A + 408 < 2^63 -> mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem),
ms = MS (pgi_regs (Z_to_bv 64 RA_pgi_mm1) usp gp tp x5 x6 x7 A x9 x10 x11 x12 x13 x14 x15 x16 x17 blen Bp H x22 hs x25 x28 x29 x30 x31)
F (Z_to_bv 64 0xc1b20) fc None m1 (seg_rom bsegs)
/\ munch [(A, A + 408)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
/\ rw_cells bsegs m1 A (stream_cells_r Bd bfill 0 L G lfill lpack lret shdr os))
(MS (pgi_regs (Z_to_bv 64 RA_pgi_mm1) usp gp tp x5 x6 x7 A x9 x10 x11 x12 x13 x14 x15 x16 x17 blen Bp H x22 hs x25 x28 x29 x30 x31)
F (ret_pc (Z_to_bv 64 RA_pgi_mm1)) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros OS HL A0 AT MI.
unfold pgi_regs, RA_pgi_mm1, stream_cells_r, wz in *.
replace (ret_pc (Z_to_bv 64 0xc1b1c)) with (Z_to_bv 64 0xc1b1c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (munch_refl [(A, A + 408)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
astep.
apply evt_done. eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. exact OS.
Qed.

Lemma pgi_l0 : forall (A usp blen Bp H v25 v22 : Z) (hs : list byte) (x1 gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) F fc (m : mem),
0 <= v25 < 2^64 -> 0 <= v22 < 2^64 -> Z_to_bv 64 (Z.lor v25 v22) = Z_to_bv 64 (ogg_page_serialno (ubytes hs)) ->
evt bsegs (fun ms => ms = MS (pgi_regs x1 usp gp tp x5 x6 x7 A (Z_to_bv 64 0) x10 x11 x12 x13 x14 x15 x16 x17 blen Bp H (Z_to_bv 64 v22) hs
(Z_to_bv 64 (ogg_page_serialno (ubytes hs))) x28 x29 x30 x31)
F (Z_to_bv 64 0xc1b84) fc None m (seg_rom bsegs))
(MS (pgi_regs x1 usp gp tp x5 x6 x7 A (Z_to_bv 64 0) x10 x11 x12 x13 x14 x15 x16 x17 blen Bp H (Z_to_bv 64 v22) hs (Z_to_bv 64 v25) x28 x29 x30 x31)
F (Z_to_bv 64 0xc1b20) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros V25 V22 ESER. unfold pgi_regs.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
astep. rewrite ESER. astep.
apply evt_done. reflexivity.
Qed.

Lemma pgi_l1 : forall (A Bd bfill br L G lfill lpack lr usp blen Bp H v25 v22 : Z) (shdr hs : list byte) (os : stream_st bptr)
(x1 gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) F fc (m : mem),
rw_cells bsegs m A (stream_cells_r Bd bfill br L G lfill lpack lr shdr os) -> length shdr = 284%nat ->
0 <= v25 < 2^64 -> 0 <= v22 < 2^64 -> Z_to_bv 64 (Z.lor v25 v22) = Z_to_bv 64 (ogg_page_serialno (ubytes hs)) ->
0 < lr -> lfill = lr -> lfill < 2^31 -> 0 <= lpack < 2^31 -> 0 < A -> A + 408 < 2^63 -> mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem) (x10' x11' : word),
ms = MS (pgi_regs x1 usp gp tp x5 x6 x7 A (Z_to_bv 64 lr) x10' x11' x12 x13 x14 x15 x16 x17 blen Bp H (Z_to_bv 64 v22) hs
(Z_to_bv 64 (ogg_page_serialno (ubytes hs))) x28 x29 x30 x31)
F (Z_to_bv 64 0xc1b84) fc None m1 (seg_rom bsegs)
/\ munch [(A, A + 408)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
/\ rw_cells bsegs m1 A (stream_cells_r Bd bfill br L G (lfill - lr) (lpack - lr) 0 shdr os))
(MS (pgi_regs x1 usp gp tp x5 x6 x7 A (Z_to_bv 64 lr) x10 x11 x12 x13 x14 x15 x16 x17 blen Bp H (Z_to_bv 64 v22) hs (Z_to_bv 64 v25) x28 x29 x30 x31)
F (Z_to_bv 64 0xc1b20) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros OS HL V25 V22 ESER LR LF LFT LP A0 AT MI. subst lfill.
unfold pgi_regs, stream_cells_r, wz in *.
pose proof (munch_refl [(A, A + 408)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
astep. rewrite ESER. astep. sh_if.
ato 0xc1b30. astep. sh_if.
ato 0xc1b84.
apply evt_done. do 3 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. exact OS.
Qed.

Lemma pgi_l2 : forall (A Bd bfill br L G lfill lpack lr usp blen Bp H v25 v22 : Z) (shdr hs : list byte) (os : stream_st bptr)
(x1 gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) F fc (m : mem),
rw_cells bsegs m A (stream_cells_r Bd bfill br L G lfill lpack lr shdr os) -> length shdr = 284%nat ->
0 <= v25 < 2^64 -> 0 <= v22 < 2^64 -> Z_to_bv 64 (Z.lor v25 v22) = Z_to_bv 64 (ogg_page_serialno (ubytes hs)) ->
0 < lr -> lr < lfill -> lfill < 2^31 -> 0 < L -> L + 4 * lfill < 2^63 -> 0 < A -> A + 408 < 2^63 -> mem_inv bsegs m ->
evt bsegs (fun ms =>
ms = MS (pgi_regs (Z_to_bv 64 RA_pgi_mm2) usp gp tp x5 x6 x7 A (Z_to_bv 64 lr) (Z_to_bv 64 L) (Z_to_bv 64 (L + 4 * lr)) (Z_to_bv 64 (4 * (lfill - lr))) x13 x14 x15 x16 x17
blen Bp H (Z_to_bv 64 v22) hs (Z_to_bv 64 (ogg_page_serialno (ubytes hs))) x28 x29 x30 x31)
F (Z_to_bv 64 oe_memmove) fc None m (seg_rom bsegs))
(MS (pgi_regs x1 usp gp tp x5 x6 x7 A (Z_to_bv 64 lr) x10 x11 x12 x13 x14 x15 x16 x17 blen Bp H (Z_to_bv 64 v22) hs (Z_to_bv 64 v25) x28 x29 x30 x31)
F (Z_to_bv 64 0xc1b20) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros OS HL V25 V22 ESER LR LF LFT L0 LT A0 AT MI.
unfold pgi_regs, RA_pgi_mm2, oe_memmove, stream_cells_r, wz in *.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
astep. rewrite ESER. astep. sh_if.
ato 0xc1b30. astep. sh_if.
ato 0x663f8. rewrite !Z.shiftl_mul_pow2 by lia. change (2^2) with 4.
replace (L + lr * 4) with (L + 4 * lr) by lia. replace ((lfill - lr) * 4) with (4 * (lfill - lr)) by lia.
apply evt_done. reflexivity.
Qed.

Lemma pgi_l3 : forall (A Bd bfill br L G lfill lpack lr usp blen Bp H : Z) (shdr hs : list byte) (os : stream_st bptr)
(gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x25 x28 x29 x30 x31 : word) F fc (m : mem),
rw_cells bsegs m A (stream_cells_r Bd bfill br L G lfill lpack lr shdr os) -> length shdr = 284%nat ->
0 < lr -> lr < lfill -> lfill < 2^31 -> 0 < G -> G + 8 * lfill < 2^63 -> 0 < A -> A + 408 < 2^63 -> mem_inv bsegs m ->
evt bsegs (fun ms =>
ms = MS (pgi_regs (Z_to_bv 64 RA_pgi_mm3) usp gp tp x5 x6 x7 A (Z_to_bv 64 lr) (Z_to_bv 64 G) (Z_to_bv 64 (G + 8 * lr)) (Z_to_bv 64 (8 * (lfill - lr))) x13 x14 x15 x16 x17
blen Bp H x22 hs x25 x28 x29 x30 x31)
F (Z_to_bv 64 oe_memmove) fc None m (seg_rom bsegs))
(MS (pgi_regs (Z_to_bv 64 RA_pgi_mm2) usp gp tp x5 x6 x7 A (Z_to_bv 64 lr) x10 x11 x12 x13 x14 x15 x16 x17 blen Bp H x22 hs x25 x28 x29 x30 x31)
F (ret_pc (Z_to_bv 64 RA_pgi_mm2)) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros OS HL LR LF LFT G0 GT A0 AT MI.
unfold pgi_regs, RA_pgi_mm2, RA_pgi_mm3, oe_memmove, stream_cells_r, wz in *.
replace (ret_pc (Z_to_bv 64 0xc1b4c)) with (Z_to_bv 64 0xc1b4c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
ato 0x663f8. rewrite !Z.shiftl_mul_pow2 by lia. change (2^3) with 8.
replace (G + lr * 8) with (G + 8 * lr) by lia. replace ((lfill - lr) * 8) with (8 * (lfill - lr)) by lia.
apply evt_done. reflexivity.
Qed.

Lemma pgi_l4 : forall (A Bd bfill br L G lfill lpack lr usp blen Bp H : Z) (shdr hs : list byte) (os : stream_st bptr)
(gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x25 x28 x29 x30 x31 : word) F fc (m : mem),
rw_cells bsegs m A (stream_cells_r Bd bfill br L G lfill lpack lr shdr os) -> length shdr = 284%nat ->
0 < lr -> lr < lfill -> lfill < 2^31 -> 0 <= lpack < 2^31 -> 0 < A -> A + 408 < 2^63 -> mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem) (x10' x11' : word),
ms = MS (pgi_regs (Z_to_bv 64 RA_pgi_mm3) usp gp tp x5 x6 x7 A (Z_to_bv 64 lr) x10' x11' x12 x13 x14 x15 x16 x17 blen Bp H x22 hs x25 x28 x29 x30 x31)
F (Z_to_bv 64 0xc1b84) fc None m1 (seg_rom bsegs)
/\ munch [(A, A + 408)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
/\ rw_cells bsegs m1 A (stream_cells_r Bd bfill br L G (lfill - lr) (lpack - lr) 0 shdr os))
(MS (pgi_regs (Z_to_bv 64 RA_pgi_mm3) usp gp tp x5 x6 x7 A (Z_to_bv 64 lr) x10 x11 x12 x13 x14 x15 x16 x17 blen Bp H x22 hs x25 x28 x29 x30 x31)
F (ret_pc (Z_to_bv 64 RA_pgi_mm3)) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros OS HL LR LF LFT LP A0 AT MI.
unfold pgi_regs, RA_pgi_mm3, stream_cells_r, wz in *.
replace (ret_pc (Z_to_bv 64 0xc1b68)) with (Z_to_bv 64 0xc1b68) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (munch_refl [(A, A + 408)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
ato 0xc1b84.
apply evt_done. do 3 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. exact OS.
Qed.

Lemma s32_range : forall x, -2^31 <= s32 x < 2^31.
Proof. intros x. unfold s32. pose proof (Z.mod_pos_bound (x + 2^31) (2^32) ltac:(lia)). lia. Qed.

Lemma mod64_inj_signed : forall a b, -2^63 <= a < 2^63 -> -2^63 <= b < 2^63 -> a mod 2^64 = b mod 2^64 -> a = b.
Proof.
intros a b Ha Hb E.
assert (Ea : a = a mod 2^64 - (if a <? 0 then 2^64 else 0)).
{ destruct (Z.ltb_spec a 0).
- rewrite <- (Z.mod_add a 1 (2^64)) by lia. rewrite Z.mod_small by lia. lia.
- rewrite Z.mod_small by lia. lia. }
assert (Eb : b = b mod 2^64 - (if b <? 0 then 2^64 else 0)).
{ destruct (Z.ltb_spec b 0).
- rewrite <- (Z.mod_add b 1 (2^64)) by lia. rewrite Z.mod_small by lia. lia.
- rewrite Z.mod_small by lia. lia. }
pose proof (Z.mod_pos_bound a (2^64) ltac:(lia)). pose proof (Z.mod_pos_bound b (2^64) ltac:(lia)).
destruct (Z.ltb_spec a 0); destruct (Z.ltb_spec b 0); lia.
Qed.

Lemma pgi_chk : forall (A Bd bfill br L G lfill lpack lr usp lo blen Bp H : Z) (shdr hs j0 : list byte) (os : stream_st bptr)
(ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(x1 gp tp x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 : word) F fc (m : mem),
rw_cells bsegs m A (stream_cells_r Bd bfill br L G lfill lpack lr shdr os) -> length shdr = 284%nat ->
rw_cells bsegs m (usp + -144) (pgi_frame ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j0 hs) -> stk bsegs m lo (usp + -144) -> lo <= usp + -144 ->
(27 <= length hs)%nat -> -2^31 <= os_serialno os < 2^31 ->
0 < A -> A + 408 <= lo -> mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem), munch [(usp + -144, usp)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\
((exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
ms = MS (mkR ra (Z_to_bv 64 usp) gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (-1)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m1 (seg_rom bsegs)
/\ stk bsegs m1 lo usp
/\ (ogg_page_serialno (ubytes hs) <> os_serialno os \/ znth (ubytes hs) 4 <> 0))
\/ (exists (x10' : word),
ms = MS (pgi_regs (Z_to_bv 64 RA_pgi_lexp) usp gp tp x5 x6 x7 A x9 (Z_to_bv 64 A) (Z_to_bv 64 (znth (ubytes hs) 26 + 1)) x12 x13 x14 x15 x16 x17 blen Bp H x22 hs
(Z_to_bv 64 (ogg_page_serialno (ubytes hs))) x28 x29 x30 x31)
F (Z_to_bv 64 A_os_lacing_expand) fc None m1 (seg_rom bsegs)
/\ m1 = m /\ x10' = x10
/\ ogg_page_serialno (ubytes hs) = os_serialno os /\ znth (ubytes hs) 4 = 0)))
(MS (pgi_regs x1 usp gp tp x5 x6 x7 A x9 x10 x11 x12 x13 x14 x15 x16 x17 blen Bp H x22 hs (Z_to_bv 64 (ogg_page_serialno (ubytes hs))) x28 x29 x30 x31)
F (Z_to_bv 64 0xc1b84) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros OS HL FR ST LO LENH SER A0 ALO MI.
unfold pgi_regs, pgi_frame, RA_pgi_lexp, A_os_lacing_expand, stream_cells_r, wz in *.
pose proof (s32_range (le32_at (ubytes hs) 14)) as PSER. fold (ogg_page_serialno (ubytes hs)) in PSER.
pose proof (byte_range (nth (Z.to_nat 4) hs (Z_to_bv 8 0))) as H4. rewrite <- (znth_ubytes hs 4) in H4 by lia.
pose proof (byte_range (nth (Z.to_nat 26) hs (Z_to_bv 8 0))) as H26. rewrite <- (znth_ubytes hs 26) in H26 by lia.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(usp + -144, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
astep. astep. if_cases CSER; zify_cond CSER.
-
ato 0xc1e14. release_frame FR ST usp. astep. astep.
apply evt_done. eexists. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. left.
do 14 eexists. split; [reflexivity|]. split; [exact ST|]. left. intros E. apply CSER. rewrite E. reflexivity.
- assert (ESER : ogg_page_serialno (ubytes hs) = os_serialno os).
{ symmetry. apply mod64_inj_signed; [lia| lia|]. rewrite ?land_ones64 in CSER. exact CSER. }
astep. if_cases CVER; zify_cond CVER; rewrite ?unsigned_lit, ?land_ones64, ?Z.mod_small in CVER by lia.
+ ato 0xc1e14. release_frame FR ST usp. astep. astep.
apply evt_done. eexists. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. left.
do 14 eexists. split; [reflexivity|]. split; [exact ST|]. right. exact CVER.
+ ato 0xc158c.
apply evt_done. eexists. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. right.
exists x10. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact ESER| exact CVER].
Qed.

Lemma pgi_e1 : forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
ra = Z_to_bv 64 RA_pgi_lexp ->
evt bsegs (fun ms => ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xc1ba0) fc None m (seg_rom bsegs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros ->. unfold RA_pgi_lexp.
replace (ret_pc (Z_to_bv 64 0xc1b9c)) with (Z_to_bv 64 0xc1b9c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
astep. apply evt_done. reflexivity.
Qed.

Lemma pgi_x1 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
evt bsegs (fun ms => ms = MS (mkR (Z_to_bv 64 RA_pgi_bexp) sp gp tp t0 t1 t2 s0 s1 s0 s3 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_os_body_expand) fc None m (seg_rom bsegs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xc1cac) fc None m (seg_rom bsegs)).
Proof.
intros. unfold RA_pgi_bexp, A_os_body_expand.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
ato 0xc14e0. apply evt_done. reflexivity.
Qed.

Lemma pgi_x2 : forall (A Bd bfill br L G lfill lpack lr n src : Z) (shdr : list byte) (os : stream_st bptr)
(ra sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
ra = Z_to_bv 64 RA_pgi_bexp ->
rw_cells bsegs m A (stream_cells_r Bd bfill br L G lfill lpack lr shdr os) -> length shdr = 284%nat ->
0 < A -> A + 408 < 2^63 -> 0 < Bd -> 0 <= bfill -> Bd + bfill < 2^63 -> mem_inv bsegs m ->
evt bsegs (fun ms => ms = MS (mkR (Z_to_bv 64 RA_pgi_mcpy) sp gp tp t0 t1 t2 (Z_to_bv 64 A) s1 (Z_to_bv 64 (Bd + bfill)) (Z_to_bv 64 src) (Z_to_bv 64 n) a3 a4 a5 a6 a7
s2 (Z_to_bv 64 n) (Z_to_bv 64 src) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 oe_memcpy) fc None m (seg_rom bsegs))
(MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 A) s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 n) (Z_to_bv 64 src) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros -> OS HL A0 AT Bd0 BF BT MI.
unfold RA_pgi_bexp, RA_pgi_mcpy, oe_memcpy, stream_cells_r, wz in *.
replace (ret_pc (Z_to_bv 64 0xc1cb8)) with (Z_to_bv 64 0xc1cb8) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
astep.
ato 0x663fc. apply evt_done. reflexivity.
Qed.

Lemma pgi_x3 : forall (A Bd bfill br L G lfill lpack lr n : Z) (shdr : list byte) (os : stream_st bptr)
(ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
ra = Z_to_bv 64 RA_pgi_mcpy ->
rw_cells bsegs m A (stream_cells_r Bd bfill br L G lfill lpack lr shdr os) -> length shdr = 284%nat ->
0 < A -> A + 408 < 2^63 -> 0 <= bfill -> 0 <= n -> bfill + n < 2^63 -> mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem) (a0' : word),
ms = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 A) s1 a0' a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 n) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xc1ce0) fc None m1 (seg_rom bsegs)
/\ munch [(A, A + 408)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
/\ rw_cells bsegs m1 A (stream_cells_r Bd (bfill + n) br L G lfill lpack lr shdr os))
(MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 A) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 n) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros -> OS HL A0 AT BF N0 BT MI.
unfold RA_pgi_mcpy, stream_cells_r, wz in *.
replace (ret_pc (Z_to_bv 64 0xc1cd4)) with (Z_to_bv 64 0xc1cd4) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (munch_refl [(A, A + 408)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
ato 0xc1ce0.
apply evt_done. do 2 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. exact OS.
Qed.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition RA_pgi_mm1 : Z := 0xb93ec.
Definition RA_pgi_mm2 : Z := 0xb941c.
Definition RA_pgi_mm3 : Z := 0xb9438.
Definition RA_pgi_lexp : Z := 0xb946c.
Definition RA_pgi_bexp : Z := 0xb9588.
Definition RA_pgi_mcpy : Z := 0xb95a4.

Definition pgi_frame (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (j0 : list byte) (hs : list byte) : list cell :=
[CB 8 j0; C8 (wz (ogg_page_granulepos (ubytes hs))); C8 (Z_to_bv 64 (znth (ubytes hs) 18)); C8 (Z_to_bv 64 (znth (ubytes hs) 21)); C8 (Z_to_bv 64 (znth (ubytes hs) 5));
C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition stream_cells_r (Bd bfill bret L G lfill lpack lret : Z) (hdr : list byte) (os : stream_st bptr) : list cell :=
[C8 (wz Bd); C8 (wz (os_body_storage os)); C8 (wz bfill); C8 (wz bret);
C8 (wz L); C8 (wz G); C8 (wz (os_lacing_storage os)); C8 (wz lfill);
C8 (wz lpack); C8 (wz lret);
CB 284 hdr;
C4 (wz (os_header_fill os)); C4 (wz (os_e_o_s os)); C4 (wz (os_b_o_s os));
C8 (wz (os_serialno os)); C8 (wz (os_pageno os)); C8 (wz (os_packetno os)); C8 (wz (os_granulepos os))].

Lemma stream_cells_r_eq : forall Bd L G hdr (os : stream_st bptr),
stream_cells Bd L G hdr os = stream_cells_r Bd (os_body_fill os) (os_body_returned os) L G (os_lacing_fill os) (os_lacing_packet os) (os_lacing_returned os) hdr os.
Proof. reflexivity. Qed.

Lemma serialno_pieces : forall hs : list byte, (18 <= length hs)%nat ->
Z_to_bv 64 (Z.lor
((Z.lor (Z.lor (Z.land (Z.shiftl (bv_unsigned (nth (Z.to_nat 15) hs (Z_to_bv 8 0))) 8) 18446744073709551615)
(bv_unsigned (nth (Z.to_nat 14) hs (Z_to_bv 8 0))))
(Z.land (Z.shiftl (bv_unsigned (nth (Z.to_nat 16) hs (Z_to_bv 8 0))) 16) 18446744073709551615)) mod 2^64)
((bv_swrap 32 (Z.shiftl (bv_unsigned (nth (Z.to_nat 17) hs (Z_to_bv 8 0))) 24)) mod 2^64))
= Z_to_bv 64 (ogg_page_serialno (ubytes hs)).
Proof.
intros hs LEN. unfold ogg_page_serialno, le32_at.
change (zslice 14 4 (ubytes hs)) with (zslice 14 (Z.of_nat 4) (ubytes hs)).
rewrite !zslice_S by (rewrite ?zlength_ubytes; lia). rewrite zslice_0.
norm_lit_idx. rewrite !znth_ubytes by lia. cbn [le_val].
word_bits.
Qed.

Definition pgi_regs (x1 : word) (usp : Z) (gp tp x5 x6 x7 : word) (A : Z) (x9 x10 x11 x12 x13 x14 x15 x16 x17 : word) (blen Bp H : Z) (x22 : word) (hs : list byte) (x25 x28 x29 x30 x31 : word)
: bvmap 5 word :=
mkR x1 (Z_to_bv 64 (usp + -144)) gp tp x5 x6 x7 (Z_to_bv 64 A) x9 x10 x11 x12 x13 x14 x15 x16 x17
(Z_to_bv 64 (-1)) (Z_to_bv 64 blen) (Z_to_bv 64 Bp) (Z_to_bv 64 H) x22
(Z_to_bv 64 (znth (ubytes hs) 19)) (Z_to_bv 64 (znth (ubytes hs) 4)) x25 (Z_to_bv 64 (znth (ubytes hs) 26)) (Z_to_bv 64 (znth (ubytes hs) 20)) x28 x29 x30 x31.

Lemma pgi_w0 : forall (A G Dsy Bd L Gv usp lo : Z) (og : page) (shdr hs : list byte) (os : stream_st bptr)
(ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
(27 <= length hs)%nat -> length shdr = 284%nat -> stream_fields_ok os ->
rw_cells asegs m A (stream_cells Bd L Gv shdr os) ->
rw_cells asegs m G (page_cells Dsy og) -> bytes_at asegs m (Dsy + pg_hdr og) hs ->
0 < A -> 0 < Bd -> Bd < 2^63 -> 0 <= Dsy -> 0 <= pg_hdr og -> Dsy + pg_hdr og + Z.of_nat (length hs) < 2^63 ->
stk asegs m lo usp -> lo <= usp - 144 -> A + 408 <= lo -> G + 32 <= lo -> Dsy + pg_hdr og + Z.of_nat (length hs) <= lo -> mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem) (j0 : list byte) (v25 v22 : Z) (x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
ms = MS (pgi_regs x1 usp gp tp x5 x6 x7 A (Z_to_bv 64 (os_lacing_returned os)) (Z_to_bv 64 Bd) (Z_to_bv 64 (os_body_returned os)) x12 x13 x14 x15 x16 x17
(pg_body_len og) (Dsy + pg_hdr og + pg_header_len og) (Dsy + pg_hdr og) (Z_to_bv 64 v22) hs (Z_to_bv 64 v25) x28 x29 x30 x31)
F (Z_to_bv 64 0xb93d0) fc None m1 (seg_rom asegs)
/\ munch [(usp + -144, usp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (usp + -144)
/\ rw_cells asegs m1 (usp + -144) (pgi_frame ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j0 hs)
/\ 0 <= v25 < 2^64 /\ 0 <= v22 < 2^64 /\ Z_to_bv 64 (Z.lor v25 v22) = Z_to_bv 64 (ogg_page_serialno (ubytes hs)))
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 G) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_ogg_stream_pagein) fc None m (seg_rom asegs)).
Proof.
intros until m. intros LENH HL FOK OS OG HS A0 Bd0 BdT D0 PG0 TOPH ST LO ALO GLO HLO MI.
unfold A_ogg_stream_pagein, pgi_regs, pgi_frame.
pose proof FOK as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12). unfold int31 in *.
unfold page_cells, wz in OG. pose proof (rw_cells_bound _ _ _ _ OG) as GGB. cbn [cells_size csize Nat.add] in GGB.
unfold stream_cells, wz in OS. pose proof (rw_cells_bound _ _ _ _ OS) as GB. cbn [cells_size csize Nat.add] in GB.
pose proof HS as (HB0 & HB1 & HB). pose proof ST as (STa & STb & _).
pose proof (munch_refl [(usp + -144, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
carve_frame 144%nat ST.
apply (rw_cells_split_CB asegs _ _ [] 144 _ [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
ato 0xb9358.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
pose proof (bytes_at_read1 asegs mx (Dsy + pg_hdr og) hs 4 _ HS ltac:(lia) ltac:(lia) eq_refl) as R4;
pose proof (bytes_at_read1 asegs mx (Dsy + pg_hdr og) hs 5 _ HS ltac:(lia) ltac:(lia) eq_refl) as R5 end.
astep. astep. clear R4 R5.
ato 0xb89dc.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
call (ogg_page_granulepos_spec _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mx G Dsy og hs) end.
all: try reflexivity. all: try exact OG. all: try exact HS. all: try lia. all: try assumption.
subst.
replace (ret_pc (Z_to_bv 64 0xb936c)) with (Z_to_bv 64 0xb936c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
ato 0xb9370. astep. sh_if.
ato 0xb937c. astep. sh_if.
ato 0xb9388.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
pose proof (bytes_at_read1 asegs mx (Dsy + pg_hdr og) hs 14 _ HS ltac:(lia) ltac:(lia) eq_refl) as R14;
pose proof (bytes_at_read1 asegs mx (Dsy + pg_hdr og) hs 15 _ HS ltac:(lia) ltac:(lia) eq_refl) as R15;
pose proof (bytes_at_read1 asegs mx (Dsy + pg_hdr og) hs 16 _ HS ltac:(lia) ltac:(lia) eq_refl) as R16;
pose proof (bytes_at_read1 asegs mx (Dsy + pg_hdr og) hs 17 _ HS ltac:(lia) ltac:(lia) eq_refl) as R17;
pose proof (bytes_at_read1 asegs mx (Dsy + pg_hdr og) hs 18 _ HS ltac:(lia) ltac:(lia) eq_refl) as R18 end.
ato 0xb939c. clear R14 R15 R16 R17 R18.
astep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
pose proof (bytes_at_read1 asegs mx (Dsy + pg_hdr og) hs 19 _ HS ltac:(lia) ltac:(lia) eq_refl) as R19;
pose proof (bytes_at_read1 asegs mx (Dsy + pg_hdr og) hs 20 _ HS ltac:(lia) ltac:(lia) eq_refl) as R20;
pose proof (bytes_at_read1 asegs mx (Dsy + pg_hdr og) hs 21 _ HS ltac:(lia) ltac:(lia) eq_refl) as R21 end.
ato 0xb93ac. clear R19 R20 R21.
astep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
pose proof (bytes_at_read1 asegs mx (Dsy + pg_hdr og) hs 26 _ HS ltac:(lia) ltac:(lia) eq_refl) as R26 end.
astep. clear R26.
ato 0xb93d0.
rewrite <- !(znth_ubytes hs) in FR by lia.
lazymatch goal with |- context [Z_to_bv 64 (bv_swrap 32 ?e)] => rewrite <- (Z_to_bv_mod64 (bv_swrap 32 e)) end.
lazymatch goal with |- context [Z_to_bv 64 (Z.lor (Z.lor ?a ?b) ?c)] => rewrite <- (Z_to_bv_mod64 (Z.lor (Z.lor a b) c)) end.
apply evt_done. do 18 eexists. split; [rewrite <- !(znth_ubytes hs) by lia; reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FR|].
split; [apply Z.mod_pos_bound; lia|]. split; [apply Z.mod_pos_bound; lia|].
rewrite !znth_ubytes by lia. rewrite <- (serialno_pieces hs ltac:(lia)).
change (2^64) with 18446744073709551616. rewrite !mod64_land. reflexivity.
Qed.

Lemma pgi_b0 : forall (A usp blen Bp H : Z) (hs : list byte) (x1 gp tp x5 x6 x7 x9 x10 x12 x13 x14 x15 x16 x17 x22 x25 x28 x29 x30 x31 : word) F fc (m : mem),
evt asegs (fun ms => ms = MS (pgi_regs x1 usp gp tp x5 x6 x7 A x9 x10 (Z_to_bv 64 0) x12 x13 x14 x15 x16 x17 blen Bp H x22 hs x25 x28 x29 x30 x31)
F (Z_to_bv 64 0xb93f0) fc None m (seg_rom asegs))
(MS (pgi_regs x1 usp gp tp x5 x6 x7 A x9 x10 (Z_to_bv 64 0) x12 x13 x14 x15 x16 x17 blen Bp H x22 hs x25 x28 x29 x30 x31)
F (Z_to_bv 64 0xb93d0) fc None m (seg_rom asegs)).
Proof.
intros. unfold pgi_regs.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
astep. apply evt_done. reflexivity.
Qed.

Lemma pgi_b1 : forall (A Bd bfill br L G lfill lpack lret usp blen Bp H : Z) (shdr hs : list byte) (os : stream_st bptr)
(x1 gp tp x5 x6 x7 x9 x12 x13 x14 x15 x16 x17 x22 x25 x28 x29 x30 x31 : word) F fc (m : mem),
rw_cells asegs m A (stream_cells_r Bd bfill br L G lfill lpack lret shdr os) -> length shdr = 284%nat ->
0 < br -> bfill = br -> bfill < 2^63 -> 0 < A -> A + 408 < 2^63 -> mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem) (x12' x13' : word),
ms = MS (pgi_regs x1 usp gp tp x5 x6 x7 A x9 (Z_to_bv 64 Bd) (Z_to_bv 64 br) x12' x13' x14 x15 x16 x17 blen Bp H x22 hs x25 x28 x29 x30 x31)
F (Z_to_bv 64 0xb93f0) fc None m1 (seg_rom asegs)
/\ munch [(A, A + 408)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
/\ rw_cells asegs m1 A (stream_cells_r Bd (bfill - br) 0 L G lfill lpack lret shdr os))
(MS (pgi_regs x1 usp gp tp x5 x6 x7 A x9 (Z_to_bv 64 Bd) (Z_to_bv 64 br) x12 x13 x14 x15 x16 x17 blen Bp H x22 hs x25 x28 x29 x30 x31)
F (Z_to_bv 64 0xb93d0) fc None m (seg_rom asegs)).
Proof.
intros until m. intros OS HL BR BF BFT A0 AT MI.
unfold pgi_regs, stream_cells_r, wz in *.
pose proof (munch_refl [(A, A + 408)] m) as MU. pose proof (wmono_refl asegs m) as WM.
astep. sh_if.
ato 0xb93e0. astep. sh_if.
ato 0xb93f0.
apply evt_done. do 3 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. exact OS.
Qed.

Lemma pgi_b2 : forall (A Bd bfill br L G lfill lpack lret usp blen Bp H : Z) (shdr hs : list byte) (os : stream_st bptr)
(x1 gp tp x5 x6 x7 x9 x12 x13 x14 x15 x16 x17 x22 x25 x28 x29 x30 x31 : word) F fc (m : mem),
rw_cells asegs m A (stream_cells_r Bd bfill br L G lfill lpack lret shdr os) -> length shdr = 284%nat ->
0 < br -> br < bfill -> bfill < 2^63 -> 0 < Bd -> Bd + br < 2^63 -> 0 < A -> A + 408 < 2^63 -> mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem),
ms = MS (pgi_regs (Z_to_bv 64 RA_pgi_mm1) usp gp tp x5 x6 x7 A x9 (Z_to_bv 64 Bd) (Z_to_bv 64 (Bd + br)) (Z_to_bv 64 (bfill - br)) (Z_to_bv 64 bfill) x14 x15 x16 x17
blen Bp H x22 hs x25 x28 x29 x30 x31)
F (Z_to_bv 64 oe_memmove) fc None m1 (seg_rom asegs)
/\ munch [(A, A + 408)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
/\ rw_cells asegs m1 A (stream_cells_r Bd (bfill - br) br L G lfill lpack lret shdr os))
(MS (pgi_regs x1 usp gp tp x5 x6 x7 A x9 (Z_to_bv 64 Bd) (Z_to_bv 64 br) x12 x13 x14 x15 x16 x17 blen Bp H x22 hs x25 x28 x29 x30 x31)
F (Z_to_bv 64 0xb93d0) fc None m (seg_rom asegs)).
Proof.
intros until m. intros OS HL BR BF BFT Bd0 BdT A0 AT MI.
unfold pgi_regs, RA_pgi_mm1, oe_memmove, stream_cells_r, wz in *.
pose proof (munch_refl [(A, A + 408)] m) as MU. pose proof (wmono_refl asegs m) as WM.
astep. sh_if.
ato 0xb93e0. astep. sh_if.
ato 0x6630c.
apply evt_done. eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. exact OS.
Qed.

Lemma pgi_b3 : forall (A Bd bfill br L G lfill lpack lret usp blen Bp H : Z) (shdr hs : list byte) (os : stream_st bptr)
(gp tp x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x22 x25 x28 x29 x30 x31 : word) F fc (m : mem),
rw_cells asegs m A (stream_cells_r Bd bfill br L G lfill lpack lret shdr os) -> length shdr = 284%nat ->
0 < A -> A + 408 < 2^63 -> mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem),
ms = MS (pgi_regs (Z_to_bv 64 RA_pgi_mm1) usp gp tp x5 x6 x7 A x9 x10 x11 x12 x13 x14 x15 x16 x17 blen Bp H x22 hs x25 x28 x29 x30 x31)
F (Z_to_bv 64 0xb93f0) fc None m1 (seg_rom asegs)
/\ munch [(A, A + 408)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
/\ rw_cells asegs m1 A (stream_cells_r Bd bfill 0 L G lfill lpack lret shdr os))
(MS (pgi_regs (Z_to_bv 64 RA_pgi_mm1) usp gp tp x5 x6 x7 A x9 x10 x11 x12 x13 x14 x15 x16 x17 blen Bp H x22 hs x25 x28 x29 x30 x31)
F (ret_pc (Z_to_bv 64 RA_pgi_mm1)) fc None m (seg_rom asegs)).
Proof.
intros until m. intros OS HL A0 AT MI.
unfold pgi_regs, RA_pgi_mm1, stream_cells_r, wz in *.
replace (ret_pc (Z_to_bv 64 0xb93ec)) with (Z_to_bv 64 0xb93ec) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (munch_refl [(A, A + 408)] m) as MU. pose proof (wmono_refl asegs m) as WM.
astep.
apply evt_done. eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. exact OS.
Qed.

Lemma pgi_l0 : forall (A usp blen Bp H v25 v22 : Z) (hs : list byte) (x1 gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) F fc (m : mem),
0 <= v25 < 2^64 -> 0 <= v22 < 2^64 -> Z_to_bv 64 (Z.lor v25 v22) = Z_to_bv 64 (ogg_page_serialno (ubytes hs)) ->
evt asegs (fun ms => ms = MS (pgi_regs x1 usp gp tp x5 x6 x7 A (Z_to_bv 64 0) x10 x11 x12 x13 x14 x15 x16 x17 blen Bp H (Z_to_bv 64 v22) hs
(Z_to_bv 64 (ogg_page_serialno (ubytes hs))) x28 x29 x30 x31)
F (Z_to_bv 64 0xb9454) fc None m (seg_rom asegs))
(MS (pgi_regs x1 usp gp tp x5 x6 x7 A (Z_to_bv 64 0) x10 x11 x12 x13 x14 x15 x16 x17 blen Bp H (Z_to_bv 64 v22) hs (Z_to_bv 64 v25) x28 x29 x30 x31)
F (Z_to_bv 64 0xb93f0) fc None m (seg_rom asegs)).
Proof.
intros until m. intros V25 V22 ESER. unfold pgi_regs.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
astep. rewrite ESER. astep.
apply evt_done. reflexivity.
Qed.

Lemma pgi_l1 : forall (A Bd bfill br L G lfill lpack lr usp blen Bp H v25 v22 : Z) (shdr hs : list byte) (os : stream_st bptr)
(x1 gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) F fc (m : mem),
rw_cells asegs m A (stream_cells_r Bd bfill br L G lfill lpack lr shdr os) -> length shdr = 284%nat ->
0 <= v25 < 2^64 -> 0 <= v22 < 2^64 -> Z_to_bv 64 (Z.lor v25 v22) = Z_to_bv 64 (ogg_page_serialno (ubytes hs)) ->
0 < lr -> lfill = lr -> lfill < 2^31 -> 0 <= lpack < 2^31 -> 0 < A -> A + 408 < 2^63 -> mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem) (x10' x11' : word),
ms = MS (pgi_regs x1 usp gp tp x5 x6 x7 A (Z_to_bv 64 lr) x10' x11' x12 x13 x14 x15 x16 x17 blen Bp H (Z_to_bv 64 v22) hs
(Z_to_bv 64 (ogg_page_serialno (ubytes hs))) x28 x29 x30 x31)
F (Z_to_bv 64 0xb9454) fc None m1 (seg_rom asegs)
/\ munch [(A, A + 408)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
/\ rw_cells asegs m1 A (stream_cells_r Bd bfill br L G (lfill - lr) (lpack - lr) 0 shdr os))
(MS (pgi_regs x1 usp gp tp x5 x6 x7 A (Z_to_bv 64 lr) x10 x11 x12 x13 x14 x15 x16 x17 blen Bp H (Z_to_bv 64 v22) hs (Z_to_bv 64 v25) x28 x29 x30 x31)
F (Z_to_bv 64 0xb93f0) fc None m (seg_rom asegs)).
Proof.
intros until m. intros OS HL V25 V22 ESER LR LF LFT LP A0 AT MI. subst lfill.
unfold pgi_regs, stream_cells_r, wz in *.
pose proof (munch_refl [(A, A + 408)] m) as MU. pose proof (wmono_refl asegs m) as WM.
astep. rewrite ESER. astep. sh_if.
ato 0xb9400. astep. sh_if.
ato 0xb9454.
apply evt_done. do 3 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. exact OS.
Qed.

Lemma pgi_l2 : forall (A Bd bfill br L G lfill lpack lr usp blen Bp H v25 v22 : Z) (shdr hs : list byte) (os : stream_st bptr)
(x1 gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) F fc (m : mem),
rw_cells asegs m A (stream_cells_r Bd bfill br L G lfill lpack lr shdr os) -> length shdr = 284%nat ->
0 <= v25 < 2^64 -> 0 <= v22 < 2^64 -> Z_to_bv 64 (Z.lor v25 v22) = Z_to_bv 64 (ogg_page_serialno (ubytes hs)) ->
0 < lr -> lr < lfill -> lfill < 2^31 -> 0 < L -> L + 4 * lfill < 2^63 -> 0 < A -> A + 408 < 2^63 -> mem_inv asegs m ->
evt asegs (fun ms =>
ms = MS (pgi_regs (Z_to_bv 64 RA_pgi_mm2) usp gp tp x5 x6 x7 A (Z_to_bv 64 lr) (Z_to_bv 64 L) (Z_to_bv 64 (L + 4 * lr)) (Z_to_bv 64 (4 * (lfill - lr))) x13 x14 x15 x16 x17
blen Bp H (Z_to_bv 64 v22) hs (Z_to_bv 64 (ogg_page_serialno (ubytes hs))) x28 x29 x30 x31)
F (Z_to_bv 64 oe_memmove) fc None m (seg_rom asegs))
(MS (pgi_regs x1 usp gp tp x5 x6 x7 A (Z_to_bv 64 lr) x10 x11 x12 x13 x14 x15 x16 x17 blen Bp H (Z_to_bv 64 v22) hs (Z_to_bv 64 v25) x28 x29 x30 x31)
F (Z_to_bv 64 0xb93f0) fc None m (seg_rom asegs)).
Proof.
intros until m. intros OS HL V25 V22 ESER LR LF LFT L0 LT A0 AT MI.
unfold pgi_regs, RA_pgi_mm2, oe_memmove, stream_cells_r, wz in *.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
astep. rewrite ESER. astep. sh_if.
ato 0xb9400. astep. sh_if.
ato 0x6630c. rewrite !Z.shiftl_mul_pow2 by lia. change (2^2) with 4.
replace (L + lr * 4) with (L + 4 * lr) by lia. replace ((lfill - lr) * 4) with (4 * (lfill - lr)) by lia.
apply evt_done. reflexivity.
Qed.

Lemma pgi_l3 : forall (A Bd bfill br L G lfill lpack lr usp blen Bp H : Z) (shdr hs : list byte) (os : stream_st bptr)
(gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x25 x28 x29 x30 x31 : word) F fc (m : mem),
rw_cells asegs m A (stream_cells_r Bd bfill br L G lfill lpack lr shdr os) -> length shdr = 284%nat ->
0 < lr -> lr < lfill -> lfill < 2^31 -> 0 < G -> G + 8 * lfill < 2^63 -> 0 < A -> A + 408 < 2^63 -> mem_inv asegs m ->
evt asegs (fun ms =>
ms = MS (pgi_regs (Z_to_bv 64 RA_pgi_mm3) usp gp tp x5 x6 x7 A (Z_to_bv 64 lr) (Z_to_bv 64 G) (Z_to_bv 64 (G + 8 * lr)) (Z_to_bv 64 (8 * (lfill - lr))) x13 x14 x15 x16 x17
blen Bp H x22 hs x25 x28 x29 x30 x31)
F (Z_to_bv 64 oe_memmove) fc None m (seg_rom asegs))
(MS (pgi_regs (Z_to_bv 64 RA_pgi_mm2) usp gp tp x5 x6 x7 A (Z_to_bv 64 lr) x10 x11 x12 x13 x14 x15 x16 x17 blen Bp H x22 hs x25 x28 x29 x30 x31)
F (ret_pc (Z_to_bv 64 RA_pgi_mm2)) fc None m (seg_rom asegs)).
Proof.
intros until m. intros OS HL LR LF LFT G0 GT A0 AT MI.
unfold pgi_regs, RA_pgi_mm2, RA_pgi_mm3, oe_memmove, stream_cells_r, wz in *.
replace (ret_pc (Z_to_bv 64 0xb941c)) with (Z_to_bv 64 0xb941c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
ato 0x6630c. rewrite !Z.shiftl_mul_pow2 by lia. change (2^3) with 8.
replace (G + lr * 8) with (G + 8 * lr) by lia. replace ((lfill - lr) * 8) with (8 * (lfill - lr)) by lia.
apply evt_done. reflexivity.
Qed.

Lemma pgi_l4 : forall (A Bd bfill br L G lfill lpack lr usp blen Bp H : Z) (shdr hs : list byte) (os : stream_st bptr)
(gp tp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x25 x28 x29 x30 x31 : word) F fc (m : mem),
rw_cells asegs m A (stream_cells_r Bd bfill br L G lfill lpack lr shdr os) -> length shdr = 284%nat ->
0 < lr -> lr < lfill -> lfill < 2^31 -> 0 <= lpack < 2^31 -> 0 < A -> A + 408 < 2^63 -> mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem) (x10' x11' : word),
ms = MS (pgi_regs (Z_to_bv 64 RA_pgi_mm3) usp gp tp x5 x6 x7 A (Z_to_bv 64 lr) x10' x11' x12 x13 x14 x15 x16 x17 blen Bp H x22 hs x25 x28 x29 x30 x31)
F (Z_to_bv 64 0xb9454) fc None m1 (seg_rom asegs)
/\ munch [(A, A + 408)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
/\ rw_cells asegs m1 A (stream_cells_r Bd bfill br L G (lfill - lr) (lpack - lr) 0 shdr os))
(MS (pgi_regs (Z_to_bv 64 RA_pgi_mm3) usp gp tp x5 x6 x7 A (Z_to_bv 64 lr) x10 x11 x12 x13 x14 x15 x16 x17 blen Bp H x22 hs x25 x28 x29 x30 x31)
F (ret_pc (Z_to_bv 64 RA_pgi_mm3)) fc None m (seg_rom asegs)).
Proof.
intros until m. intros OS HL LR LF LFT LP A0 AT MI.
unfold pgi_regs, RA_pgi_mm3, stream_cells_r, wz in *.
replace (ret_pc (Z_to_bv 64 0xb9438)) with (Z_to_bv 64 0xb9438) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (munch_refl [(A, A + 408)] m) as MU. pose proof (wmono_refl asegs m) as WM.
ato 0xb9454.
apply evt_done. do 3 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. exact OS.
Qed.

Lemma s32_range : forall x, -2^31 <= s32 x < 2^31.
Proof. intros x. unfold s32. pose proof (Z.mod_pos_bound (x + 2^31) (2^32) ltac:(lia)). lia. Qed.

Lemma mod64_inj_signed : forall a b, -2^63 <= a < 2^63 -> -2^63 <= b < 2^63 -> a mod 2^64 = b mod 2^64 -> a = b.
Proof.
intros a b Ha Hb E.
assert (Ea : a = a mod 2^64 - (if a <? 0 then 2^64 else 0)).
{ destruct (Z.ltb_spec a 0).
- rewrite <- (Z.mod_add a 1 (2^64)) by lia. rewrite Z.mod_small by lia. lia.
- rewrite Z.mod_small by lia. lia. }
assert (Eb : b = b mod 2^64 - (if b <? 0 then 2^64 else 0)).
{ destruct (Z.ltb_spec b 0).
- rewrite <- (Z.mod_add b 1 (2^64)) by lia. rewrite Z.mod_small by lia. lia.
- rewrite Z.mod_small by lia. lia. }
pose proof (Z.mod_pos_bound a (2^64) ltac:(lia)). pose proof (Z.mod_pos_bound b (2^64) ltac:(lia)).
destruct (Z.ltb_spec a 0); destruct (Z.ltb_spec b 0); lia.
Qed.

Lemma pgi_chk : forall (A Bd bfill br L G lfill lpack lr usp lo blen Bp H : Z) (shdr hs j0 : list byte) (os : stream_st bptr)
(ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(x1 gp tp x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 : word) F fc (m : mem),
rw_cells asegs m A (stream_cells_r Bd bfill br L G lfill lpack lr shdr os) -> length shdr = 284%nat ->
rw_cells asegs m (usp + -144) (pgi_frame ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j0 hs) -> stk asegs m lo (usp + -144) -> lo <= usp + -144 ->
(27 <= length hs)%nat -> -2^31 <= os_serialno os < 2^31 ->
0 < A -> A + 408 <= lo -> mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem), munch [(usp + -144, usp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\
((exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
ms = MS (mkR ra (Z_to_bv 64 usp) gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (-1)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m1 (seg_rom asegs)
/\ stk asegs m1 lo usp
/\ (ogg_page_serialno (ubytes hs) <> os_serialno os \/ znth (ubytes hs) 4 <> 0))
\/ (exists (x10' : word),
ms = MS (pgi_regs (Z_to_bv 64 RA_pgi_lexp) usp gp tp x5 x6 x7 A x9 (Z_to_bv 64 A) (Z_to_bv 64 (znth (ubytes hs) 26 + 1)) x12 x13 x14 x15 x16 x17 blen Bp H x22 hs
(Z_to_bv 64 (ogg_page_serialno (ubytes hs))) x28 x29 x30 x31)
F (Z_to_bv 64 A_os_lacing_expand) fc None m1 (seg_rom asegs)
/\ m1 = m /\ x10' = x10
/\ ogg_page_serialno (ubytes hs) = os_serialno os /\ znth (ubytes hs) 4 = 0)))
(MS (pgi_regs x1 usp gp tp x5 x6 x7 A x9 x10 x11 x12 x13 x14 x15 x16 x17 blen Bp H x22 hs (Z_to_bv 64 (ogg_page_serialno (ubytes hs))) x28 x29 x30 x31)
F (Z_to_bv 64 0xb9454) fc None m (seg_rom asegs)).
Proof.
intros until m. intros OS HL FR ST LO LENH SER A0 ALO MI.
unfold pgi_regs, pgi_frame, RA_pgi_lexp, A_os_lacing_expand, stream_cells_r, wz in *.
pose proof (s32_range (le32_at (ubytes hs) 14)) as PSER. fold (ogg_page_serialno (ubytes hs)) in PSER.
pose proof (byte_range (nth (Z.to_nat 4) hs (Z_to_bv 8 0))) as H4. rewrite <- (znth_ubytes hs 4) in H4 by lia.
pose proof (byte_range (nth (Z.to_nat 26) hs (Z_to_bv 8 0))) as H26. rewrite <- (znth_ubytes hs 26) in H26 by lia.
pose proof ST as (STa & STb & _).
pose proof (munch_refl [(usp + -144, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
astep. astep. if_cases CSER; zify_cond CSER.
-
ato 0xb96e4. release_frame FR ST usp. astep. astep.
apply evt_done. eexists. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. left.
do 14 eexists. split; [reflexivity|]. split; [exact ST|]. left. intros E. apply CSER. rewrite E. reflexivity.
- assert (ESER : ogg_page_serialno (ubytes hs) = os_serialno os).
{ symmetry. apply mod64_inj_signed; [lia| lia|]. rewrite ?land_ones64 in CSER. exact CSER. }
astep. if_cases CVER; zify_cond CVER; rewrite ?unsigned_lit, ?land_ones64, ?Z.mod_small in CVER by lia.
+ ato 0xb96e4. release_frame FR ST usp. astep. astep.
apply evt_done. eexists. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. left.
do 14 eexists. split; [reflexivity|]. split; [exact ST|]. right. exact CVER.
+ ato 0xb8e5c.
apply evt_done. eexists. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. right.
exists x10. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact ESER| exact CVER].
Qed.

Lemma pgi_e1 : forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
ra = Z_to_bv 64 RA_pgi_lexp ->
evt asegs (fun ms => ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xb9470) fc None m (seg_rom asegs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom asegs)).
Proof.
intros until m. intros ->. unfold RA_pgi_lexp.
replace (ret_pc (Z_to_bv 64 0xb946c)) with (Z_to_bv 64 0xb946c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
astep. apply evt_done. reflexivity.
Qed.

Lemma pgi_x1 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
evt asegs (fun ms => ms = MS (mkR (Z_to_bv 64 RA_pgi_bexp) sp gp tp t0 t1 t2 s0 s1 s0 s3 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_os_body_expand) fc None m (seg_rom asegs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xb957c) fc None m (seg_rom asegs)).
Proof.
intros. unfold RA_pgi_bexp, A_os_body_expand.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
ato 0xb8db0. apply evt_done. reflexivity.
Qed.

Lemma pgi_x2 : forall (A Bd bfill br L G lfill lpack lr n src : Z) (shdr : list byte) (os : stream_st bptr)
(ra sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
ra = Z_to_bv 64 RA_pgi_bexp ->
rw_cells asegs m A (stream_cells_r Bd bfill br L G lfill lpack lr shdr os) -> length shdr = 284%nat ->
0 < A -> A + 408 < 2^63 -> 0 < Bd -> 0 <= bfill -> Bd + bfill < 2^63 -> mem_inv asegs m ->
evt asegs (fun ms => ms = MS (mkR (Z_to_bv 64 RA_pgi_mcpy) sp gp tp t0 t1 t2 (Z_to_bv 64 A) s1 (Z_to_bv 64 (Bd + bfill)) (Z_to_bv 64 src) (Z_to_bv 64 n) a3 a4 a5 a6 a7
s2 (Z_to_bv 64 n) (Z_to_bv 64 src) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 oe_memcpy) fc None m (seg_rom asegs))
(MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 A) s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 n) (Z_to_bv 64 src) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom asegs)).
Proof.
intros until m. intros -> OS HL A0 AT Bd0 BF BT MI.
unfold RA_pgi_bexp, RA_pgi_mcpy, oe_memcpy, stream_cells_r, wz in *.
replace (ret_pc (Z_to_bv 64 0xb9588)) with (Z_to_bv 64 0xb9588) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
astep.
ato 0x66310. apply evt_done. reflexivity.
Qed.

Lemma pgi_x3 : forall (A Bd bfill br L G lfill lpack lr n : Z) (shdr : list byte) (os : stream_st bptr)
(ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
ra = Z_to_bv 64 RA_pgi_mcpy ->
rw_cells asegs m A (stream_cells_r Bd bfill br L G lfill lpack lr shdr os) -> length shdr = 284%nat ->
0 < A -> A + 408 < 2^63 -> 0 <= bfill -> 0 <= n -> bfill + n < 2^63 -> mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem) (a0' : word),
ms = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 A) s1 a0' a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 n) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xb95b0) fc None m1 (seg_rom asegs)
/\ munch [(A, A + 408)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
/\ rw_cells asegs m1 A (stream_cells_r Bd (bfill + n) br L G lfill lpack lr shdr os))
(MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 A) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 n) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom asegs)).
Proof.
intros until m. intros -> OS HL A0 AT BF N0 BT MI.
unfold RA_pgi_mcpy, stream_cells_r, wz in *.
replace (ret_pc (Z_to_bv 64 0xb95a4)) with (Z_to_bv 64 0xb95a4) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (munch_refl [(A, A + 408)] m) as MU. pose proof (wmono_refl asegs m) as WM.
ato 0xb95b0.
apply evt_done. do 2 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. exact OS.
Qed.
