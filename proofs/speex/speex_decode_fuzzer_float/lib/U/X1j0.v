(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1cc X1bk X1bj X1cf X1bu.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ik X1ii X1it X1ix X1iy X1iz.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qz X1r0 X1r3.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma wpre_ztake : forall l ws n, wpre l ws -> 0 <= n -> n <= zlength l -> wpre (ztake n l) ws.
Proof.
intros l ws n [P L] Hn Hl. unfold wpre, ztake, zlength in *. rewrite firstn_length_le by lia. split; [|lia].
transitivity (firstn (Z.to_nat n) (firstn (length l) ws)).
- rewrite firstn_firstn. f_equal. lia.
- rewrite P, firstn_map. reflexivity.
Qed.

Lemma sum_low_app' : forall l1 l2, sum_low (l1 ++ l2) = sum_low l1 + sum_low l2.
Proof. induction l1 as [|x l1 IH]; intros l2; cbn [sum_low app]; [lia|]. rewrite IH. lia. Qed.

Lemma low_byte_val : forall v, 0 <= v -> bv_unsigned (Z_to_bv 8 v) = Z.land v 255.
Proof.
intros v Hv. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with (2^8).
change 255 with (Z.ones 8). rewrite Z.land_ones by lia. reflexivity.
Qed.

Section PIU.
Context {RCEIL : RunCeiling}.
Variables (A Bd L Gv H lo : Z) (shdr hs : list byte) (os1 : stream_st bptr) (lws gws : list word).
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (x1 : word) (j0 : list byte).
Local Notation hdr := (ubytes hs).
Local Notation nseg := (znth (ubytes hs) 26).
Local Notation fl := (znth (ubytes hs) 5).
Local Notation ls := (os_lacing_storage os1).
Local Notation pn := (ogg_page_pageno (ubytes hs)).
Local Notation W := [(bv_unsigned sp - 144, bv_unsigned sp); (A, A + 408); (L, L + 4 * ls); (Gv, Gv + 8 * ls)].
Hypothesis LENH : length hs = (27 + Z.to_nat nseg)%nat.
Hypothesis Hnseg : 0 <= nseg < 256.
Hypothesis HL : length shdr = 284%nat.
Hypothesis FOK : stream_fields_ok os1.
Hypothesis Hls : os_lacing_fill os1 + nseg + 1 <= ls.
Hypothesis LFILL : zlength (os_lacing os1) = os_lacing_fill os1.
Hypothesis LPK : 0 <= os_lacing_packet os1 <= os_lacing_fill os1.
Hypothesis LOK : lacing_vals_ok (os_lacing os1).
Hypothesis HA : 0 < A. Hypothesis HLv : 0 < L. Hypothesis HGv : 0 < Gv. Hypothesis HH : 0 <= H.
Hypothesis TOPL : L + 4 * ls < 2^63. Hypothesis TOPG : Gv + 8 * ls < 2^63. Hypothesis TOPH : H + Z.of_nat (length hs) < 2^63.
Hypothesis LOSP : lo + 144 <= bv_unsigned sp.
Hypothesis SPA : bv_unsigned sp <= A.
Hypothesis SEP_fL : L + 4 * ls <= lo.
Hypothesis SEP_fG : Gv + 8 * ls <= lo.
Hypothesis SEP_Hf : H + Z.of_nat (length hs) <= lo.
Hypothesis SEP_LG : L + 4 * ls <= Gv \/ Gv + 8 * ls <= L.
Hypothesis SEP_HL : H + Z.of_nat (length hs) <= L \/ L + 4 * ls <= H.
Hypothesis SEP_HG : H + Z.of_nat (length hs) <= Gv \/ Gv + 8 * ls <= H.
#[local] Set Default Proof Using "LENH Hnseg HL FOK Hls LFILL LPK LOK HA HLv HGv HH TOPL TOPG TOPH LOSP SPA SEP_fL SEP_fG SEP_Hf SEP_LG SEP_HL SEP_HG".

Local Notation FRAME m loc := (rw_cells rsegs m (bv_unsigned sp + -144)
(loc ++ [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])).
Local Notation LOC := [CB 8 j0; C8 (wz (ogg_page_granulepos hdr)); C8 (Z_to_bv 64 (znth hdr 18)); C8 (Z_to_bv 64 (znth hdr 21)); C8 (Z_to_bv 64 fl)].
Local Notation os2 := (pagein_unroll os1 pn).

Definition unroll_post (x18 x19 x20 x22 x25 x29 x30 x31 : word) (m : mem) : machine_state -> Prop :=
fun ms' => exists (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 : word) m' lws',
ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp x5 x6 x7 (Z_to_bv 64 A) (Z_to_bv 64 fl) (Z_to_bv 64 (Z.land fl 1))
x11 x12 x13 x14 x15 x16 x17
x18 x19 x20 (Z_to_bv 64 H) x22 (Z_to_bv 64 (znth hdr 19 * 256)) (Z_to_bv 64 pn) x25 (Z_to_bv 64 nseg) (Z_to_bv 64 (znth hdr 20 * 65536)) x28 x29 x30 x31)
F (Z_to_bv 64 0x30a50) fc None m' (seg_rom rsegs)
/\ munch W m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ rw_cells rsegs m' A (stream_cells Bd L Gv shdr os2)
/\ u32arr rsegs m' L lws' /\ wpre (os_lacing os2) lws' /\ Z.of_nat (length lws') = ls
/\ u64arr rsegs m' Gv gws /\ FRAME m' LOC /\ bytes_at rsegs m' H hs.

Lemma pi_loop1 : forall (k : nat) (i acc : Z) m (x5 x6 x7 x11 x17 x18 x19 x20 x22 x24 x25 x28 x29 x30 x31 : word) (lp lf bf : Z),
Z.to_nat (lf - i) = k -> 0 <= lp <= i -> i < lf -> lf <= zlength (os_lacing os1) -> lf < 2^31 ->
acc = bf - sum_low (zslice lp (i - lp) (os_lacing os1)) -> -2^62 <= bf < 2^62 ->
u32arr rsegs m L lws -> wpre (os_lacing os1) lws -> mem_inv rsegs m ->
evt rsegs (fun ms' => exists x17',
ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp x5 x6 x7 (Z_to_bv 64 A) (Z_to_bv 64 fl) (Z_to_bv 64 (Z.land fl 1))
x11 (Z_to_bv 64 lp) (Z_to_bv 64 lf) (Z_to_bv 64 lf) (Z_to_bv 64 (bf - sum_low (zslice lp (lf - lp) (os_lacing os1)))) (Z_to_bv 64 (L + 4 * lf)) x17'
x18 x19 x20 (Z_to_bv 64 H) x22 (Z_to_bv 64 (znth hdr 19 * 256)) x24 x25 (Z_to_bv 64 nseg) (Z_to_bv 64 (znth hdr 20 * 65536)) x28 x29 x30 x31)
F (Z_to_bv 64 0x30a20) fc None m (seg_rom rsegs))
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp x5 x6 x7 (Z_to_bv 64 A) (Z_to_bv 64 fl) (Z_to_bv 64 (Z.land fl 1))
x11 (Z_to_bv 64 lp) (Z_to_bv 64 lf) (Z_to_bv 64 i) (Z_to_bv 64 acc) (Z_to_bv 64 (L + 4 * i)) x17
x18 x19 x20 (Z_to_bv 64 H) x22 (Z_to_bv 64 (znth hdr 19 * 256)) x24 x25 (Z_to_bv 64 nseg) (Z_to_bv 64 (znth hdr 20 * 65536)) x28 x29 x30 x31)
F (Z_to_bv 64 0x30a0c) fc None m (seg_rom rsegs)).
Proof.
induction k as [|k IH]; intros i acc m x5 x6 x7 x11 x17 x18 x19 x20 x22 x24 x25 x28 x29 x30 x31 lp lf bf Hk Hlp Hi Hlf Hlf2 Hacc Hbf LAC LPRE MI; [lia|].
subst acc.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
pose proof (wpre_length _ _ LPRE) as LL. unfold zlength in Hlf.
pose proof (byte_range (nth (Z.to_nat 5) hs (Z_to_bv 8 0))) as Hfl. rewrite <- (znth_ubytes hs 5) in Hfl by lia.
pose proof (byte_range (nth (Z.to_nat 19) hs (Z_to_bv 8 0))) as H19. rewrite <- (znth_ubytes hs 19) in H19 by lia.
pose proof (byte_range (nth (Z.to_nat 20) hs (Z_to_bv 8 0))) as H20. rewrite <- (znth_ubytes hs 20) in H20 by lia.
pose proof (Forall_znth _ _ i LOK ltac:(cbv beta; lia)) as Rv. cbv beta in Rv.
pose proof (u32_low_byte m L (os_lacing os1) lws i (wa (L + 4 * i)) LAC LPRE ltac:(lia) ltac:(lia) ltac:(lia) eq_refl) as RB.

zstep. zstep. zstep. zstep.
zstep. if_cases CL; zify_cond CL; rewrite ?zb_signed_small, ?unsigned_lit in CL by lia.
all: rewrite (low_byte_val (znth (os_lacing os1) i)) by lia.
all: assert (SUM : bf - sum_low (zslice lp (i - lp) (os_lacing os1)) - Z.land (znth (os_lacing os1) i) 255
= bf - sum_low (zslice lp (i + 1 - lp) (os_lacing os1)))
by (replace (i + 1 - lp) with ((i - lp) + 1) by lia; rewrite zslice_app, sum_low_app' by lia;
replace (lp + (i - lp)) with i by lia; rewrite (zslice_cons i), zslice_0 by (unfold zlength; lia); cbn [sum_low]; lia).
-
replace (bf - sum_low (zslice lp (i - lp) (os_lacing os1)) + - Z.land (znth (os_lacing os1) i) 255)
with (bf - sum_low (zslice lp (i + 1 - lp) (os_lacing os1))) by lia.
replace (L + 4 * i + 4) with (L + 4 * (i + 1)) by lia.
eapply (IH (i + 1)); try eassumption; try lia.
-
apply evt_done. eexists.
replace (bf - sum_low (zslice lp (i - lp) (os_lacing os1)) + - Z.land (znth (os_lacing os1) i) 255)
with (bf - sum_low (zslice lp (lf - lp) (os_lacing os1))) by (replace lf with (i + 1) by lia; lia).
replace (L + 4 * i + 4) with (L + 4 * lf) by lia. replace (i + 1) with lf by lia. reflexivity.
Qed.

Lemma pi_hole : forall m0 m (bfill : Z) (x5 x6 x7 x13 x14 x15 x16 x17 x28 x18 x19 x20 x22 x25 x29 x30 x31 : word),
let lp := os_lacing_packet os1 in
pn <> os_pageno os1 ->
bfill = os_body_fill os1 - sum_low (zslice lp (os_lacing_fill os1 - lp) (os_lacing os1)) -> -2^62 <= os_body_fill os1 < 2^62 ->
munch W m0 m -> wmono rsegs m0 m ->
rw_cells rsegs m A (stream_cells Bd L Gv shdr (set_body os1 (ztake bfill (os_body os1)) (os_body_storage os1) bfill (os_body_returned os1))) ->
u32arr rsegs m L lws -> Z.of_nat (length lws) = ls -> wpre (os_lacing os1) lws ->
u64arr rsegs m Gv gws -> Z.of_nat (length gws) = ls -> FRAME m LOC -> bytes_at rsegs m H hs -> mem_inv rsegs m ->
evt rsegs (unroll_post x18 x19 x20 x22 x25 x29 x30 x31 m0)
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp x5 x6 x7 (Z_to_bv 64 A) (Z_to_bv 64 fl) (Z_to_bv 64 (Z.land fl 1))
(Z_to_bv 64 (os_pageno os1)) (Z_to_bv 64 lp) x13 x14 x15 x16 x17
x18 x19 x20 (Z_to_bv 64 H) x22 (Z_to_bv 64 (znth hdr 19 * 256)) (Z_to_bv 64 pn) x25 (Z_to_bv 64 nseg) (Z_to_bv 64 (znth hdr 20 * 65536)) x28 x29 x30 x31)
F (Z_to_bv 64 0x30a24) fc None m (seg_rom rsegs)).
Proof.
intros until x31. cbv zeta. intros NEP Hbf Hbfr MU WM OS LAC LLEN LPRE GRA GLEN FR HS MI.
pose proof FOK as sfP_; first [ sf_destruct 12%nat sfP_ as F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 | sf_fb; destruct sfP_ as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12) ]. unfold int31 in *.
pose proof (rw_cells_bound _ _ _ _ OS) as GB. cbn [cells_size csize Nat.add] in GB.
pose proof HS as (HB0 & HB1 & HB). pose proof (wpre_length _ _ LPRE) as LL. unfold zlength in LFILL.
pose proof (byte_range (nth (Z.to_nat 5) hs (Z_to_bv 8 0))) as Hfl. rewrite <- (znth_ubytes hs 5) in Hfl by lia.
pose proof (byte_range (nth (Z.to_nat 19) hs (Z_to_bv 8 0))) as H19. rewrite <- (znth_ubytes hs 19) in H19 by lia.
pose proof (byte_range (nth (Z.to_nat 20) hs (Z_to_bv 8 0))) as H20. rewrite <- (znth_ubytes hs 20) in H20 by lia.
pose proof (Z_land_range fl 1 ltac:(lia) ltac:(lia)) as Hc1.
assert (HPN : 0 <= pn < 2^32).
{ unfold ogg_page_pageno, le32_at. pose proof (le_val_bound (zslice 18 4 hdr) (bytes_ok_zslice 18 4 hdr (ubytes_ok hs))) as X.
rewrite zlength_zslice in X by (rewrite ?zlength_ubytes; unfold zlength; lia). change (256 ^ 4) with (2^32) in X. exact X. }
unfold stream_cells, set_body, wz in OS. cbn [os_body_storage os_body_fill os_body_returned os_lacing_storage os_lacing_fill os_lacing_packet os_lacing_returned
os_header_fill os_e_o_s os_b_o_s os_serialno os_pageno os_packetno os_granulepos] in OS.
cbn [app] in FR.
unfold unroll_post, pagein_unroll. replace (pn =? os_pageno os1) with false by (symmetry; apply Z.eqb_neq; exact NEP). cbn [negb].
rewrite <- Hbf.
unfold set_body, set_lacing. cbn [os_body_data os_body os_body_storage os_body_fill os_body_returned os_lacing_vals os_lacing os_granule_vals os_granules
os_lacing_storage os_lacing_fill os_lacing_packet os_lacing_returned os_header_fill os_e_o_s os_b_o_s os_serialno os_pageno os_packetno os_granulepos].

zstep. lstep. zstep. if_cases CH; zify_cond CH; rewrite ?unsigned_lit, ?land_ones64 in CH by lia.
-
assert (EP : os_pageno os1 = -1).
{ destruct (Z.lt_ge_cases (os_pageno os1) 0); [lia|]. rewrite Z.mod_small in CH by lia. lia. }
replace (os_pageno os1 =? -1) with true by (symmetry; apply Z.eqb_eq; exact EP). cbn [negb].
apply evt_done. sf_eexists 11%nat. lazymatch goal with |- context [MS _ _ _ _ _ ?mx _ = _] => exists mx end. exists lws.
split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
unfold stream_cells, wz.
split; [lazymatch goal with OSx : rw_cells rsegs _ A _ |- _ => exact OSx end|].
split; [exact LAC|]. split; [apply wpre_ztake; [exact LPRE| lia| unfold zlength; lia]|]. split; [exact LLEN|].
split; [exact GRA|]. split; [exact FR| exact HS].
- assert (NP : os_pageno os1 <> -1) by (intros E; rewrite E in CH; apply CH; reflexivity).
replace (negb (os_pageno os1 =? -1)) with true by (symmetry; apply (proj2 (negb_true_iff _)); apply Z.eqb_neq; exact NP). cbn iota.

zstep. zstep. zstep. zstep. rewrite !Z.shiftl_mul_pow2 by lia. change (2^2) with 4. zstep.
pose proof (u32arr_store_ok rsegs _ _ _ (os_lacing_packet os1) (wa (L + os_lacing_packet os1 * 4)) LAC ltac:(lia) ltac:(f_equal; lia)) as SOK.
zstep.
change (Z_to_le_bytes 4 1024) with (le4 (Z_to_bv 64 1024)).
replace (Z_to_bv 64 (L + os_lacing_packet os1 * 4)) with (wa (L + 4 * os_lacing_packet os1)) by (unfold wa; f_equal; lia).
pose proof (u32arr_write rsegs _ _ _ (os_lacing_packet os1) (Z_to_bv 64 1024) LAC ltac:(lia)) as LAC2. clear LAC.
store_done. rename LAC2 into LAC.
lstep. lstep.
apply evt_done. sf_eexists 11%nat. lazymatch goal with |- context [MS _ _ _ _ _ ?mx _ = _] => exists mx end.
exists (upd lws (Z.to_nat (os_lacing_packet os1)) (Z_to_bv 64 1024)).
split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
unfold stream_cells, wz.
split; [lazymatch goal with OSx : rw_cells rsegs _ A _ |- _ => exact OSx end|].
split; [exact LAC|].
split. { replace (Z.to_nat (os_lacing_packet os1)) with (length (ztake (os_lacing_packet os1) (os_lacing os1))) by (unfold ztake; rewrite firstn_length_le; lia).
apply wpre_snoc; [apply wpre_ztake; [exact LPRE| lia| unfold zlength; lia]| unfold ztake; rewrite firstn_length_le by lia; lia| reflexivity]. }
split; [rewrite upd_length; exact LLEN|].
split; [exact GRA|]. split; [exact FR| exact HS].
Qed.

Lemma pi_unroll : forall m (x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x28 x18 x19 x20 x22 x24 x25 x29 x30 x31 : word),
rw_cells rsegs m A (stream_cells Bd L Gv shdr os1) -> u32arr rsegs m L lws -> Z.of_nat (length lws) = ls -> wpre (os_lacing os1) lws ->
u64arr rsegs m Gv gws -> Z.of_nat (length gws) = ls -> FRAME m LOC -> bytes_at rsegs m H hs -> mem_inv rsegs m ->
-2^62 <= os_body_fill os1 < 2^62 ->
evt rsegs (unroll_post x18 x19 x20 x22 x25 x29 x30 x31 m)
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp x5 x6 x7 (Z_to_bv 64 A) x9 x10 x11 x12 x13 x14 x15 x16 x17
x18 x19 x20 (Z_to_bv 64 H) x22 (Z_to_bv 64 (znth hdr 19)) x24 x25 (Z_to_bv 64 nseg) (Z_to_bv 64 (znth hdr 20)) x28 x29 x30 x31)
F (Z_to_bv 64 0x309bc) fc None m (seg_rom rsegs)).
Proof.
intros until x31. intros OS LAC LLEN LPRE GRA GLEN FR HS MI Hbf.
pose proof FOK as sfP_; first [ sf_destruct 12%nat sfP_ as F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 | sf_fb; destruct sfP_ as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12) ]. unfold int31 in *.
pose proof (rw_cells_bound _ _ _ _ OS) as GB. cbn [cells_size csize Nat.add] in GB.
pose proof (munch_refl W m) as MU. pose proof (wmono_refl rsegs m) as WM.
pose proof HS as (HB0 & HB1 & HB). pose proof (wpre_length _ _ LPRE) as LL. unfold zlength in LFILL.
pose proof (byte_range (nth (Z.to_nat 5) hs (Z_to_bv 8 0))) as Hfl. rewrite <- (znth_ubytes hs 5) in Hfl by lia.
pose proof (byte_range (nth (Z.to_nat 18) hs (Z_to_bv 8 0))) as H18. rewrite <- (znth_ubytes hs 18) in H18 by lia.
pose proof (byte_range (nth (Z.to_nat 19) hs (Z_to_bv 8 0))) as H19. rewrite <- (znth_ubytes hs 19) in H19 by lia.
pose proof (byte_range (nth (Z.to_nat 20) hs (Z_to_bv 8 0))) as H20. rewrite <- (znth_ubytes hs 20) in H20 by lia.
pose proof (byte_range (nth (Z.to_nat 21) hs (Z_to_bv 8 0))) as H21. rewrite <- (znth_ubytes hs 21) in H21 by lia.
pose proof (Z_land_range fl 1 ltac:(lia) ltac:(lia)) as Hc1.
unfold stream_cells, wz in OS. cbn [app] in FR.

zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
rewrite ?Z.shiftl_mul_pow2 by lia. change (2^8) with 256. change (2^16) with 65536. change (2^24) with 16777216.
assert (EPN : Z_to_bv 64 (Z.lor (Z.lor (znth hdr 19 * 256) (znth hdr 18)) (Z.lor (znth hdr 20 * 65536) (znth hdr 21 * 16777216))) = Z_to_bv 64 pn).
{ unfold ogg_page_pageno, le32_at.
rewrite (zslice_cons 18), (zslice_cons (18 + 1)), (zslice_cons (18 + 1 + 1)), (zslice_cons (18 + 1 + 1 + 1)), zslice_0 by (rewrite ?zlength_ubytes; unfold zlength; lia).
replace (18 + 1 + 1 + 1) with 21 by lia. replace (18 + 1 + 1) with 20 by lia. replace (18 + 1) with 19 by lia.
cbn [le_val]. word_bits. }
rewrite EPN. clear EPN.
assert (HPN : 0 <= pn < 2^32).
{ unfold ogg_page_pageno, le32_at. pose proof (le_val_bound (zslice 18 4 hdr) (bytes_ok_zslice 18 4 hdr (ubytes_ok hs))) as X.
rewrite zlength_zslice in X by (rewrite ?zlength_ubytes; unfold zlength; lia). change (256 ^ 4) with (2^32) in X. exact X. }

zstep. zstep. zstep. if_cases CP; zify_cond CP; rewrite ?unsigned_lit, ?land_ones64 in CP by lia.
-
assert (EQP : pn = os_pageno os1).
{ destruct (Z.lt_ge_cases (os_pageno os1) 0); [| rewrite Z.mod_small in CP by lia; exact CP].
exfalso. replace (os_pageno os1) with (-1) in CP by lia. change ((-1) mod 2^64) with 18446744073709551615 in CP. lia. }
apply evt_done. unfold unroll_post, pagein_unroll. replace (pn =? os_pageno os1) with true by (symmetry; apply Z.eqb_eq; exact EQP). cbn [negb].
sf_eexists 11%nat. exists m, lws.
split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
split; [exact OS|]. split; [exact LAC|]. split; [exact LPRE|]. split; [exact LLEN|]. split; [exact GRA|]. split; [exact FR| exact HS].
-
assert (NEP : pn <> os_pageno os1) by (intros E; apply CP; rewrite <- E, Z.mod_small by lia; reflexivity).

zstep. zstep. zstep. rewrite Z.add_0_r, (swrap32_small (os_lacing_packet os1)) by lia.
zstep. if_cases CU; zify_cond CU; rewrite ?zb_signed_small, ?unsigned_lit in CU by lia.
+
eapply (pi_hole m m (os_body_fill os1)); try eassumption; try lia.
all: first [ replace (os_lacing_fill os1 - os_lacing_packet os1) with 0 by lia; rewrite zslice_0; cbn [sum_low]; lia | exact OS ].
+
zstep. zstep. zstep. zstep. rewrite !Z.shiftl_mul_pow2 by lia. change (2^2) with 4.
replace (L + os_lacing_packet os1 * 4) with (L + 4 * os_lacing_packet os1) by lia.
eapply evt_cut.
{ eapply (pi_loop1 (Z.to_nat (os_lacing_fill os1 - os_lacing_packet os1)) (os_lacing_packet os1) (os_body_fill os1) m
_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (os_lacing_packet os1) (os_lacing_fill os1) (os_body_fill os1)); try eassumption; try lia.
all: first [ unfold zlength; lia | replace (os_lacing_packet os1 - os_lacing_packet os1) with 0 by lia; rewrite zslice_0; cbn [sum_low]; lia ]. }
cbv beta. intros ms' [x17' ->].
lstep.
eapply (pi_hole m _ (os_body_fill os1 - sum_low (zslice (os_lacing_packet os1) (os_lacing_fill os1 - os_lacing_packet os1) (os_lacing os1))));
try eassumption; try lia; try reflexivity.
Qed.
End PIU.
