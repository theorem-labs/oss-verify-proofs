(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Znumtheory.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1dg X1df X1ck X1dh.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qz X1od.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X07z X05o X05p X0ae X09i X09y X09x X0ag
X071 X06v.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Notation mem := (word -> option byte).

Lemma pb_w1 : forall (F D : Z) (og : page) (hs : list byte) (sinit lastg : Z)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 s11 t3 t4 t5 t6 : word) Fr fc (m : mem),
(sinit = 0 \/ sinit = 1) ->
rw_cells asegs m (F + 8544) (page_cells D og) -> bytes_at asegs m (D + pg_hdr og) hs -> (27 <= length hs)%nat -> mem_inv asegs m ->
evt asegs (fun ms =>
(sinit = 0 /\ exists (t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
ms = MS (mkR (Z_to_bv 64 0x96c88) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (F + 8688)) (Z_to_bv 64 (ogg_page_serialno (ubytes hs))) a2' a3' a4' a5' a6' a7'
s2 s3 s4 s5 s6 (Z_to_bv 64 (F + 8688)) (Z_to_bv 64 lastg) s9 (Z_to_bv 64 (F + 8544)) s11 t3' t4' t5' t6')
Fr (Z_to_bv 64 A_ogg_stream_init) fc None m (seg_rom asegs))
\/ (sinit = 1 /\ ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 0) (Z_to_bv 64 lastg) a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 (Z_to_bv 64 (F + 8688)) (Z_to_bv 64 lastg) s9 (Z_to_bv 64 (F + 8544)) s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 0x96c88) fc None m (seg_rom asegs)))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 (if sinit =? 0 then 1 else 0)) (Z_to_bv 64 lastg) a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 (Z_to_bv 64 (F + 8688)) s8 s9 (Z_to_bv 64 (F + 8544)) s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 0x96c68) fc None m (seg_rom asegs)).
Proof.
intros until m. intros SI OG HS LH MI. unfold A_ogg_stream_init.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
destruct SI as [-> | ->]; cbn [Z.eqb].
- ato 0x96c78. astep.
call (ogg_page_serialno_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fr fc m (F + 8544) D og hs); [unfold wz; reflexivity| exact OG| exact HS| exact LH| exact MI|].
ato 0xb8aac. subst. unfold wz. apply evt_done. left. split; [reflexivity|]. do 13 eexists. reflexivity.
- ato 0x96c88. apply evt_done. right. split; [reflexivity| reflexivity].
Qed.

Lemma bv_eqb_lit_ne_s : forall r k, -2^63 <= r < 2^63 -> -2^63 <= k < 2^63 -> r <> k -> bv_eqb (Z_to_bv 64 r) (Z_to_bv 64 k) = false.
Proof.
intros r k Hr Hk NE. unfold bv_eqb. apply Z.eqb_neq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
intros E. Z.div_mod_to_equations. nia.
Qed.
Lemma bv_eqb_same : forall x : word, bv_eqb x x = true.
Proof. intros x. unfold bv_eqb. apply Z.eqb_refl. Qed.
Lemma h_s32_range : forall x, -2^31 <= s32 x < 2^31.
Proof. intros x. unfold s32. pose proof (Z.mod_pos_bound (x + 2^31) (2^32) ltac:(lia)). lia. Qed.

Lemma pb_w2 : forall (F D Bd L Gv : Z) (og : page) (hs hdr : list byte) (os : stream_st unit)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 s11 t3 t4 t5 t6 : word) Fr fc (m : mem),
0 < F -> 0 < Bd < 2^63 -> length hdr = 284%nat -> stream_fields_ok os -> os_body_data os <> None ->
rw_cells asegs m (F + 8688) (stream_cells Bd L Gv hdr os) ->
rw_cells asegs m (F + 8544) (page_cells D og) -> bytes_at asegs m (D + pg_hdr og) hs -> (27 <= length hs)%nat -> mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem) (os1 : stream_st unit) (t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
((os_serialno os = ogg_page_serialno (ubytes hs) /\ m1 = m /\ os1 = os)
\/ (os_serialno os <> ogg_page_serialno (ubytes hs) /\ os1 = snd (ogg_stream_reset_serialno os (ogg_page_serialno (ubytes hs)))
/\ munch [(F + 8688, F + 8688 + 408)] m m1 /\ wmono asegs m m1 /\ stream_fields_ok os1))
/\ mem_inv asegs m1 /\ rw_cells asegs m1 (F + 8688) (stream_cells Bd L Gv hdr os1)
/\ ms = MS (mkR (Z_to_bv 64 0x96cb8) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (F + 8688)) (Z_to_bv 64 (F + 8544)) a2' a3' a4' a5' a6' a7'
s2 s3 s4 s5 s6 (Z_to_bv 64 (F + 8688)) s8 s9 (Z_to_bv 64 (F + 8544)) s11 t3' t4' t5' t6')
Fr (Z_to_bv 64 A_ogg_stream_pagein) fc None m1 (seg_rom asegs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 (F + 8688)) s8 s9 (Z_to_bv 64 (F + 8544)) s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 0x96c88) fc None m (seg_rom asegs)).
Proof.
intros until m. intros F0 BD0 HL FOK BDN OS OG HS LH MI. unfold A_ogg_stream_pagein.
pose proof (munch_refl [(F + 8688, F + 8688 + 408)] m) as MU. pose proof (wmono_refl asegs m) as WM.
pose proof (h_s32_range (le32_at (ubytes hs) 14)) as SR. fold (ogg_page_serialno (ubytes hs)) in SR.
pose proof FOK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SNR & _).
unfold stream_cells, wz in OS. unfold bptr in *.
ato 0x96c8c. astep.
call (ogg_page_serialno_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fr fc m (F + 8544) D og hs); [unfold wz; reflexivity| exact OG| exact HS| exact LH| exact MI|].
subst. unfold wz.
ato 0x96c94.
destruct (Z.eq_dec (os_serialno os) (ogg_page_serialno (ubytes hs))) as [EQ|NE].
- astep. rewrite EQ, bv_eqb_same. cbn iota. ato 0xb9314. apply evt_done. exists m, os. do 13 eexists. split; [left; split; [reflexivity| split; reflexivity]|].
split; [exact MI|]. split; [unfold stream_cells, wz; exact OS| reflexivity].
- astep. rewrite (bv_eqb_lit_ne_s (os_serialno os) (ogg_page_serialno (ubytes hs))) by lia. cbn [negb].
ato 0x96c9c. astep.
call (ogg_page_serialno_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fr fc m (F + 8544) D og hs); [unfold wz; reflexivity| exact OG| exact HS| exact LH| exact MI|].
subst. unfold wz.
ato 0x96ca8. astep.
destruct (ogg_stream_reset_serialno os (ogg_page_serialno (ubytes hs))) as [r os1] eqn:ER.
call (ogg_stream_reset_serialno_spec (F + 8688) Bd L Gv hdr os (ogg_page_serialno (ubytes hs)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fr fc m r os1);
[exact HL| exact FOK| lia| lia| exact SR| split; [intros E; contradiction| lia]| exact MI| unfold stream_cells, wz; exact OS| exact ER| reflexivity| reflexivity|].
ato 0xb9314. apply evt_done.
lazymatch goal with MU' : munch _ m ?m1 |- _ => exists m1 end. exists os1. do 13 eexists.
split; [right; split; [exact NE|]; split; [reflexivity|]; split; [first [exact MU| replace (F + 8688 + 408) with (F + 9096) in MU by lia; exact MU]|];
split; [exact WM| assumption]|].
split; [assumption|]. split; [assumption| reflexivity].
Qed.

Definition gstep (fs gfs nfr lastg pg np eosb : Z) : option Z :=
if (0 <? pg) && negb (fs =? 0) && ((0 <? lastg) || (pg <? INT64_MAX + lastg)) then
let a := np * gfs * nfr in
let b := pg - lastg in
if (a <? b) || (Z.quot INT64_MAX 640 - a <? - b) || (Z.quot INT64_MAX 640 <? a - b) then None
else
let skip := s32 (Z.quot (fs * (a - b)) gfs) in
if skip =? INT_MIN then None
else Some (if negb (eosb =? 0) then - skip else skip)
else if pg <? -1 then None else Some 0.
Lemma granule_step_gstep : forall (h : hstate unit) hdr,
granule_step h hdr = gstep (h_frame_size h) (h_granule_frame_size h) (h_nframes h) (h_last_granule h) (ogg_page_granulepos hdr) (ogg_page_packets hdr) (ogg_page_eos hdr).
Proof. intros h hdr. reflexivity. Qed.
Lemma lts_lit : forall x y, -2^63 <= x < 2^63 -> -2^63 <= y < 2^63 -> bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof. intros x y Hx Hy. unfold bv_lts. rewrite !signed_lit_small by lia. reflexivity. Qed.
Lemma h_swrap32_eq : forall z, bv_swrap 32 z = (z + 2147483648) mod 4294967296 - 2147483648.
Proof. reflexivity. Qed.
Lemma h_sx32_lit : forall e, (-2^31 <= e < 2^31)%Z -> sx32 (Z_to_bv 64 e) = Z_to_bv 64 e.
Proof.
intros e He. unfold sx32. apply Z_to_bv_eqm. rewrite unsigned_lit_wrap, h_swrap32_eq.
change (2^64)%Z with 18446744073709551616%Z. Z.div_mod_to_equations. nia.
Qed.
Lemma swrap_mod64_plus1 : forall x, -2^31 <= x < 2^31 - 1 -> bv_swrap 32 (x mod 18446744073709551616 + 1) = x + 1.
Proof.
intros x Hx. rewrite h_swrap32_eq.
assert (D : (4294967296 | 18446744073709551616)) by (exists 4294967296; reflexivity).
rewrite (Znumtheory.Zmod_div_mod 4294967296 18446744073709551616 (x mod 18446744073709551616 + 1 + 2147483648)) by (lia || exact D).
replace (x mod 18446744073709551616 + 1 + 2147483648) with (x mod 18446744073709551616 + (1 + 2147483648)) by lia.
rewrite Zplus_mod_idemp_l. replace (x + (1 + 2147483648)) with (x + 1 + 2147483648) by lia.
rewrite <- (Znumtheory.Zmod_div_mod 4294967296 18446744073709551616 (x + 1 + 2147483648)) by (lia || exact D).
rewrite Z.mod_small by lia. lia.
Qed.

Definition C640 : Z := 14411518807585587.
Lemma c640_eq : C640 = Z.quot INT64_MAX 640.
Proof. reflexivity. Qed.
Lemma zbv_sub_mod : forall x y, Z_to_bv 64 (x - y mod 18446744073709551616) = Z_to_bv 64 (x - y).
Proof.
intros x y. apply Z_to_bv_eqm. rewrite Zminus_mod_idemp_r. reflexivity.
Qed.
Lemma swrap32_small_h : forall x, -2^31 <= x < 2^31 -> bv_swrap 32 x = x.
Proof. intros x Hx. rewrite h_swrap32_eq. rewrite Z.mod_small by lia. lia. Qed.
Lemma mod64_small_h : forall x, 0 <= x < 18446744073709551616 -> x mod 18446744073709551616 = x.
Proof. intros x Hx. apply Z.mod_small. lia. Qed.
Lemma zbv_subm_mul : forall x y z, Z_to_bv 64 (((x - y mod 18446744073709551616) mod 18446744073709551616) * z) = Z_to_bv 64 ((x - y) * z).
Proof.
intros x y z. apply Z_to_bv_eqm. rewrite Zmult_mod_idemp_l. rewrite Zmult_mod. rewrite Zminus_mod_idemp_r. rewrite <- Zmult_mod. reflexivity.
Qed.
Lemma v_div_small_h : forall x y, -2^63 <= x < 2^63 -> 0 < y < 2^63 -> v_div (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (Z.quot x y).
Proof.
intros x y Hx Hy. unfold v_div, zsig. rewrite unsigned_lit by lia.
replace (y =? 0) with false by (symmetry; apply Z.eqb_neq; lia). rewrite !signed_lit_small by lia. reflexivity.
Qed.
Lemma count_lt255_le : forall l, 0 <= count_lt255 l <= Z.of_nat (length l).
Proof. induction l as [|v l IH]; cbn [count_lt255 length]; [lia|]. destruct (v <? 255); lia. Qed.
Lemma packets_range_h : forall hs : list byte, 0 <= ogg_page_packets (ubytes hs) <= 255.
Proof.
intros hs. unfold ogg_page_packets, zslice, ztake. pose proof (znth_ubytes_range hs 26) as R.
pose proof (count_lt255_le (firstn (Z.to_nat (znth (ubytes hs) 26)) (zdrop 27 (ubytes hs)))) as C.
pose proof (firstn_le_length (Z.to_nat (znth (ubytes hs) 26)) (zdrop 27 (ubytes hs))) as L. lia.
Qed.

Definition ginner (fs nfr lastg pg np : Z) : bool :=
let a := np * fs * nfr in let b := pg - lastg in
(a <? b) || (C640 - a <? - b) || (C640 <? a - b) || (s32 (Z.quot (fs * (a - b)) fs) =? INT_MIN).
Lemma gstep_run : forall fs nfr lastg pg np eosb, 0 < pg -> fs <> 0 -> (0 < lastg \/ pg < INT64_MAX + lastg) ->
(ginner fs nfr lastg pg np = true -> gstep fs fs nfr lastg pg np eosb = None) /\ (ginner fs nfr lastg pg np = false -> gstep fs fs nfr lastg pg np eosb <> None).
Proof.
intros fs nfr lastg pg np eosb PG FS C. unfold gstep, ginner. rewrite <- c640_eq.
replace ((0 <? pg) && negb (fs =? 0) && ((0 <? lastg) || (pg <? INT64_MAX + lastg))) with true
by (symmetry; apply andb_true_iff; split; [apply andb_true_iff; split; [apply Z.ltb_lt; lia| apply negb_true_iff, Z.eqb_neq; exact FS]|];
apply orb_true_iff; destruct C; [left; apply Z.ltb_lt; lia| right; apply Z.ltb_lt; lia]).
split; intros H.
- destruct ((np * fs * nfr <? pg - lastg) || (C640 - np * fs * nfr <? - (pg - lastg)) || (C640 <? np * fs * nfr - (pg - lastg))); [reflexivity|].
cbn [orb] in H. rewrite H. reflexivity.
- apply orb_false_iff in H as (H1 & H2). rewrite H1. cbn iota. rewrite H2. discriminate.
Qed.

Lemma pb_w3t : forall (S1 extra eosv : Z) (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w120 w136 w144 w152 w160 w168 w176 w184 w192 w200 w208 Fr fc (m : mem),
0 <= S1 < 2^62 ->
rw_cells asegs m S1 (hsp w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 (Z_to_bv 64 extra) w120 (Z_to_bv 64 eosv) w136
w144 w152 w160 w168 w176 w184 w192 w200 w208) ->
-2^31 <= extra < 2^31 - 1 -> (eosv = 0 \/ eosv = 1) -> mem_inv asegs m ->
evt asegs (fun ms => exists (a0' : word),
(eosv <> 0 /\ ms = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) a0' a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 A_PN) fc None m (seg_rom asegs))
\/ (eosv = 0 /\ ms = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) a0' a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 (Z_to_bv 64 (extra + 1)) s9 s10 s11 t3 t4 t5 t6)
Fr (Z_to_bv 64 A_KH) fc None m (seg_rom asegs)))
(MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) Fr (Z_to_bv 64 0x96d50) fc None m (seg_rom asegs)).
Proof.
intros until m. intros S1R SP EXR EOR MI. unfold hsp in SP. unfold A_PN, A_KH.
ato 0x96d54. astep.
destruct EOR as [-> | ->].
- rewrite bv_eqb_same. cbn [negb]. ato 0x96d60. rewrite swrap_mod64_plus1 by lia. apply evt_done. eexists. right. split; [reflexivity| reflexivity].
- rewrite (bv_eqb_lit_ne_s 1 0) by lia. cbn [negb]. ato 0x9714c. apply evt_done. eexists. left. split; [lia| reflexivity].
Qed.

Lemma pb_w3c : forall (S1 F D fs nfr lastg pg np extra eosv : Z) (og : page) (hs : list byte)
(ra sp gp tp t0 t1 t2 s0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s9 s11 t3 t4 t5 t6 : word)
w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w120 w144 w152 w160 w168 w176 w184 w192 w200 w208 Fr fc (m : mem),
0 <= S1 < 2^62 ->
rw_cells asegs m S1 (hsp w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 (Z_to_bv 64 fs) (Z_to_bv 64 extra) w120 (Z_to_bv 64 eosv) (Z_to_bv 64 nfr)
w144 w152 w160 w168 w176 w184 w192 w200 w208) ->
rw_cells asegs m (F + 8544) (page_cells D og) -> bytes_at asegs m (D + pg_hdr og) hs -> (27 <= length hs)%nat ->
0 < fs <= 640 -> 1 <= nfr <= 10 -> 0 <= np <= 255 -> 0 < pg < 2^63 -> -1 <= lastg < 2^63 -> (0 < lastg \/ pg < INT64_MAX + lastg) ->
-2^31 <= extra < 2^31 - 1 -> (eosv = 0 \/ eosv = 1) -> mem_inv asegs m ->
evt asegs (fun ms => exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
let a := np * fs * nfr in let b := pg - lastg in
(((a <? b) || (C640 - a <? - b) || (C640 <? a - b) || (s32 (Z.quot (fs * (a - b)) fs) =? INT_MIN)) = true
/\ ms = MS (mkR ra' sp gp tp t0' t1' t2' s0 (Z_to_bv 64 S1) s9 s11 (Z_to_bv 64 1) a3' a4' a5' a6' a7'
s2 s3 s4 (Z_to_bv 64 pg) s6 s7 (Z_to_bv 64 lastg) s9 (Z_to_bv 64 (F + 8544)) s11 t3' t4' t5' t6')
Fr (Z_to_bv 64 A_CL) fc None m (seg_rom asegs))
\/ (((a <? b) || (C640 - a <? - b) || (C640 <? a - b) || (s32 (Z.quot (fs * (a - b)) fs) =? INT_MIN)) = false
/\ ms = MS (mkR ra' sp gp tp t0' t1' t2' s0 (Z_to_bv 64 S1) a0' a1' a2' a3' a4' a5' a6' a7'
s2 s3 s4 (Z_to_bv 64 pg) s6 s7 (Z_to_bv 64 lastg) s9 (Z_to_bv 64 (F + 8544)) s11 t3' t4' t5' t6')
Fr (Z_to_bv 64 0x96d50) fc None m (seg_rom asegs)))
(MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) (Z_to_bv 64 np) (Z_to_bv 64 fs) a2 a3 a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 pg) s6 s7 (Z_to_bv 64 lastg) s9
(Z_to_bv 64 (F + 8544)) s11 t3 t4 t5 t6) Fr (Z_to_bv 64 0x96cf4) fc None m (seg_rom asegs)).
Proof.
intros until m. intros S1R SP OG HS LH FSR NFR NPR PGR LGR C EXR EOR MI. unfold hsp in SP. unfold A_CL.
ato 0x96d08. astep.

rewrite (swrap32_small_h (np * fs)) by nia. rewrite (mod64_small_h (np * fs)) by nia. rewrite zbv_sub_mod.
assert (BR : -2^63 < pg - lastg < 2^63) by (unfold INT64_MAX in C; lia).
assert (P1 : 0 <= np * fs <= 163200) by nia. assert (P2 : 0 <= np * fs * nfr <= 1632000) by nia.
rewrite lts_lit by lia.
set (a := np * fs * nfr) in *. set (b := pg - lastg) in *.
destruct (Z.ltb_spec a b) as [AB|AB].
-
ato 0x971a4. apply evt_done. do 16 eexists. left. split; [cbn [orb]; reflexivity| reflexivity].
- ato 0x96d10. astep.

ato 0x96d1c. astep.

rewrite zbv_sub_mod. rewrite lts_lit by (unfold C640 in *; lia).
destruct (Z.ltb_spec (14411518807585587 - a) (0 - b)) as [CB|CB].
+ ato 0x971a4. apply evt_done. do 16 eexists. left. split; [| reflexivity].
replace (C640 - a <? - b) with true by (symmetry; apply Z.ltb_lt; unfold C640; lia). rewrite orb_true_r. reflexivity.
+ ato 0x96d38. astep.

assert (ABR : 0 <= a - b <= 14411518807585587) by lia.
rewrite zbv_subm_mul. rewrite v_div_small_h by nia. rewrite Z.quot_mul by lia.
rewrite unsigned_lit by lia. rewrite Z.add_0_r.
assert (ESK : bv_swrap 32 (a - b) = s32 (a - b)) by (rewrite h_swrap32_eq; unfold s32; reflexivity).
rewrite ESK.
assert (EQS : s32 (Z.quot (fs * (a - b)) fs) = s32 (a - b)) by (f_equal; rewrite Z.mul_comm; apply Z.quot_mul; lia).
pose proof (h_s32_range (a - b)) as SKR.
destruct (Z.eq_dec (s32 (a - b)) (-2147483648)) as [SE|SN].
* rewrite SE, bv_eqb_same. cbn iota. ato 0x971a4. apply evt_done. do 16 eexists. left. split; [| reflexivity].
rewrite EQS, SE. cbn. rewrite !orb_true_r. reflexivity.
* rewrite (bv_eqb_lit_ne_s (s32 (a - b)) (-2147483648)) by lia. cbn iota.
ato 0x96d40. astep.

call (ogg_page_eos_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fr fc m (F + 8544) D og hs); [unfold wz; reflexivity| exact OG| exact HS| exact LH| exact MI|].
ato 0x96d50. apply evt_done. do 16 eexists. right. split; [| reflexivity].
rewrite EQS. unfold C640, INT_MIN.
replace (a <? b) with false by (symmetry; apply Z.ltb_ge; lia).
replace (14411518807585587 - a <? - b) with false by (symmetry; apply Z.ltb_ge; lia).
replace (14411518807585587 <? a - b) with false by (symmetry; apply Z.ltb_ge; lia).
replace (s32 (a - b) =? -2147483648) with false by (symmetry; apply Z.eqb_neq; exact SN). reflexivity.
Unshelve. all: exact (Z_to_bv 64 0).
Qed.

Ltac pb3_post_pre := eexists; do 16 eexists; split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [unfold hsp; eassumption|].
Ltac pb3_tail GS :=
eapply evt_mono; [eapply pb_w3t; [lia| unfold hsp in *; eassumption| lia| assumption| assumption]|];
let ms' := fresh "ms" in let a0' := fresh "a0" in let NE := fresh "NE" in
intros ms' (a0' & [(NE & ->) | (NE & ->)]);
[ pb3_post_pre; right; left; split; [exact GS|]; split; [exact NE| reflexivity]
| pb3_post_pre; right; right; split; [exact GS|]; split; [exact NE| reflexivity] ].

Lemma pb_w3 : forall (S1 F D : Z) (og : page) (hs : list byte) (fs gfs nfr lastg extra eosv : Z)
(ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s11 t3 t4 t5 t6 : word)
w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w120 w144 w152 w160 w176 w184 w192 w200 w208 Fr fc (m : mem),
ra = Z_to_bv 64 0x96cb8 -> 0 <= S1 < 2^62 -> 0 <= F -> F + 16384 <= S1 -> 0 <= D -> D + pg_hdr og + Z.of_nat (length hs) <= S1 ->
rw_cells asegs m (F + 8544) (page_cells D og) -> bytes_at asegs m (D + pg_hdr og) hs ->
(27 + Z.to_nat (znth (ubytes hs) 26) <= length hs)%nat -> D + pg_hdr og + Z.of_nat (length hs) < 2^64 ->
rw_cells asegs m (F + 8384) [C4 (Z_to_bv 64 fs)] ->
rw_cells asegs m S1 (hsp w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 (Z_to_bv 64 gfs) (Z_to_bv 64 extra) w120 (Z_to_bv 64 eosv) (Z_to_bv 64 nfr)
w144 w152 w160 (Z_to_bv 64 (F + 8384)) w176 w184 w192 w200 w208) ->
0 <= fs <= 640 -> gfs = fs -> 1 <= nfr <= 10 -> -1 <= lastg < 2^63 -> -2^31 <= extra < 2^31 - 1 -> (eosv = 0 \/ eosv = 1) -> mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
munch [(S1, S1 + 216)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
/\ rw_cells asegs m1 S1 (hsp w0 w8 w16 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 (Z_to_bv 64 gfs) (Z_to_bv 64 extra) w120 (Z_to_bv 64 eosv) (Z_to_bv 64 nfr)
(Z_to_bv 64 (ogg_page_granulepos (ubytes hs))) w152 w160 (Z_to_bv 64 (F + 8384)) w176 w184 w192 w200 w208)
/\ ((gstep fs gfs nfr lastg (ogg_page_granulepos (ubytes hs)) (ogg_page_packets (ubytes hs)) (ogg_page_eos (ubytes hs)) = None
/\ ms = MS (mkR ra' sp gp tp t0' t1' t2' s0 (Z_to_bv 64 S1) s9 s11 (Z_to_bv 64 1) a3' a4' a5' a6' a7'
s2 s3 s4 (Z_to_bv 64 (ogg_page_granulepos (ubytes hs))) s6 s7 (Z_to_bv 64 lastg) s9 (Z_to_bv 64 (F + 8544)) s11 t3' t4' t5' t6')
Fr (Z_to_bv 64 A_CL) fc None m1 (seg_rom asegs))
\/ (gstep fs gfs nfr lastg (ogg_page_granulepos (ubytes hs)) (ogg_page_packets (ubytes hs)) (ogg_page_eos (ubytes hs)) <> None /\ eosv <> 0
/\ ms = MS (mkR ra' sp gp tp t0' t1' t2' s0 (Z_to_bv 64 S1) a0' a1' a2' a3' a4' a5' a6' a7'
s2 s3 s4 (Z_to_bv 64 (ogg_page_granulepos (ubytes hs))) s6 s7 (Z_to_bv 64 lastg) s9 (Z_to_bv 64 (F + 8544)) s11 t3' t4' t5' t6')
Fr (Z_to_bv 64 A_PN) fc None m1 (seg_rom asegs))
\/ (gstep fs gfs nfr lastg (ogg_page_granulepos (ubytes hs)) (ogg_page_packets (ubytes hs)) (ogg_page_eos (ubytes hs)) <> None /\ eosv = 0
/\ ms = MS (mkR ra' sp gp tp t0' t1' t2' s0 (Z_to_bv 64 S1) a0' a1' a2' a3' a4' a5' a6' a7'
s2 s3 s4 (Z_to_bv 64 (ogg_page_granulepos (ubytes hs))) s6 s7 (Z_to_bv 64 (extra + 1)) s9 (Z_to_bv 64 (F + 8544)) s11 t3' t4' t5' t6')
Fr (Z_to_bv 64 A_KH) fc None m1 (seg_rom asegs))))
(MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 (Z_to_bv 64 lastg) s9 (Z_to_bv 64 (F + 8544)) s11 t3 t4 t5 t6)
Fr (ret_pc ra) fc None m (seg_rom asegs)).
Proof.
intros until m. intros -> S1R F0 FS1 D0 DS1 OG HS LH TOP FSC SP FSR EGF NFR LGR EXR EOR MI. unfold hsp in SP. unfold A_CL, A_PN, A_KH.
unfold page_cells in OG.
replace (ret_pc (Z_to_bv 64 0x96cb8)) with (Z_to_bv 64 0x96cb8) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
pose proof (munch_refl [(S1, S1 + 216)] m) as MU. pose proof (wmono_refl asegs m) as WM.
ato 0x96cbc. astep.
call (ogg_page_granulepos_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fr fc m (F + 8544) D og hs); [unfold wz; reflexivity| exact OG| exact HS| lia| exact MI|].
subst. unfold wz.
ato 0x96cc8. astep.
call (ogg_page_packets_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fr fc m (F + 8544) D og hs); [unfold wz; reflexivity| exact OG| exact HS| exact LH| exact TOP| exact MI|].
subst. unfold wz.
ato 0x96cd0.

set (pg := ogg_page_granulepos (ubytes hs)) in *.
set (np := ogg_page_packets (ubytes hs)) in *.
assert (PGR : -2^63 <= pg < 2^63) by (unfold pg, ogg_page_granulepos, s64; pose proof (Z.mod_pos_bound (le64_at (ubytes hs) 6 + 2^63) (2^64) ltac:(lia)); lia).
astep.

pose proof (packets_range_h hs) as NPR. fold np in NPR.
rewrite lts_lit by lia.
destruct (Z.ltb_spec 0 pg) as [PGP|PGN]; cbn [negb].
-
ato 0x96cdc. astep. rewrite h_sx32_lit by lia.
destruct (Z.eq_dec fs 0) as [FS0|FSN].
+
subst fs. rewrite bv_eqb_same. cbn iota.
assert (GS : gstep 0 0 nfr lastg pg np (ogg_page_eos (ubytes hs)) <> None).
{ unfold gstep. replace (0 <? pg) with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.eqb negb andb].
replace (pg <? -1) with false by (symmetry; apply Z.ltb_ge; lia). discriminate. }
ato 0x96d50. pb3_tail GS.
+ rewrite (bv_eqb_lit_ne_s fs 0) by lia.
ato 0x96ce0. astep. rewrite lts_lit by lia.

destruct (Z.ltb_spec 0 lastg) as [LP|LN].
*
cbn iota.
eapply evt_cut; [eapply (pb_w3c S1 F D fs nfr lastg pg np extra eosv og hs);
[lia| unfold hsp in *; eassumption| eassumption| eassumption| lia| lia| lia| lia| lia| lia| lia| lia| assumption| eassumption]|].
intros ms' (ra' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & [(CI & ->) | (CI & ->)]).
-- destruct (gstep_run fs nfr lastg pg np (ogg_page_eos (ubytes hs)) PGP FSN ltac:(lia)) as (GN & _).
apply evt_done. eexists. exists ra', t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6'.
split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [unfold hsp; eassumption|].
left. split; [exact (GN CI)| reflexivity].
-- destruct (gstep_run fs nfr lastg pg np (ogg_page_eos (ubytes hs)) PGP FSN ltac:(lia)) as (_ & GSm).
pose proof (GSm CI) as GS. pb3_tail GS.
* cbn iota. ato 0x96cf0. astep.

rewrite lts_lit by (unfold INT64_MAX in *; lia).
destruct (Z.ltb_spec pg (lastg + 9223372036854775807)) as [PL|PL]; cbn [negb].
--
eapply evt_cut; [eapply (pb_w3c S1 F D fs nfr lastg pg np extra eosv og hs);
[lia| unfold hsp in *; eassumption| eassumption| eassumption| lia| lia| lia| lia| lia| lia| unfold INT64_MAX; lia| lia| assumption| eassumption]|].
intros ms' (ra' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & [(CI & ->) | (CI & ->)]).
++ destruct (gstep_run fs nfr lastg pg np (ogg_page_eos (ubytes hs)) PGP FSN ltac:(unfold INT64_MAX; lia)) as (GN & _).
apply evt_done. eexists. exists ra', t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6'.
split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [unfold hsp; eassumption|].
left. split; [exact (GN CI)| reflexivity].
++ destruct (gstep_run fs nfr lastg pg np (ogg_page_eos (ubytes hs)) PGP FSN ltac:(unfold INT64_MAX; lia)) as (_ & GSm).
pose proof (GSm CI) as GS. pb3_tail GS.
--
assert (GS : gstep fs fs nfr lastg pg np (ogg_page_eos (ubytes hs)) <> None).
{ unfold gstep. replace (0 <? pg) with true by (symmetry; apply Z.ltb_lt; lia).
replace (negb (fs =? 0)) with true by (symmetry; apply negb_true_iff, Z.eqb_neq; exact FSN).
replace (0 <? lastg) with false by (symmetry; apply Z.ltb_ge; lia).
replace (pg <? INT64_MAX + lastg) with false by (symmetry; apply Z.ltb_ge; unfold INT64_MAX; lia). cbn [andb orb].
replace (pg <? -1) with false by (symmetry; apply Z.ltb_ge; lia). discriminate. }
ato 0x96d50. pb3_tail GS.
-

ato 0x96d4c. astep. rewrite lts_lit by lia.
destruct (Z.ltb_spec (-2) pg) as [P2|P2]; cbn [negb].
+
assert (GS : gstep fs fs nfr lastg pg np (ogg_page_eos (ubytes hs)) <> None).
{ unfold gstep. replace (0 <? pg) with false by (symmetry; apply Z.ltb_ge; lia). cbn [andb].
replace (pg <? -1) with false by (symmetry; apply Z.ltb_ge; lia). discriminate. }
ato 0x96d50. pb3_tail GS.
+
assert (GS : gstep fs fs nfr lastg pg np (ogg_page_eos (ubytes hs)) = None).
{ unfold gstep. replace (0 <? pg) with false by (symmetry; apply Z.ltb_ge; lia). cbn [andb].
replace (pg <? -1) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
ato 0x971a4. apply evt_done. pb3_post_pre. left. split; [exact GS| reflexivity].
Unshelve. all: exact (Z_to_bv 64 0).
Qed.

