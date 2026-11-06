(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0mx X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1da X1dg X1cg X1ck.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.SpecA Require X1s9.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qz X1nt X1rg X1rh X1re X1od X1r8.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require X1qy.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X001 X00a X00b X000 X04b X00c X07z X05o X05s X05t
X0ae X09j X09u X09x X0af X09p X09l X0a4 X0a5 X09v X09w
X05l X05m X06d X069 X068 X071 X06v X06y X06u.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X0yr X12c X14x X0r0 X0r9 X0ra X0qz X0v9 X0rb X0wl X0wm X110 X106 X10j X10c X108 X10q X10r X10h X10i X0x2 X0x1 X0xn X0xq X0xm.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yr OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0qz OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0v9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0rb OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wl OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wm OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X110 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X106 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10j OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X108 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10q OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10r OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10h OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10i OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0x2 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0x1 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xn OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xq OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xm.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation mem := (word -> option byte).
Local Notation Z64 := (Z_to_bv 64).

Lemma zslice_of_prefix_a : forall (buf : list Z) (ub : list Z) a n,
firstn (length buf) ub = buf -> (length buf <= length ub)%nat -> 0 <= a -> 0 <= n -> a + n <= Z.of_nat (length buf) ->
zslice a n buf = firstn (Z.to_nat n) (skipn (Z.to_nat a) ub).
Proof.
intros buf ub a n PRE LE Ha Hn Han. unfold zslice, ztake, zdrop. rewrite <- PRE.
rewrite skipn_firstn_comm. rewrite firstn_firstn. f_equal. lia.
Qed.

Lemma page_hs_a : forall (m : mem) A D (oy : sync_st bptr) bytes og,
sync_rep m A D oy bytes -> sync_inv oy -> page_ok oy og -> sy_data oy <> None ->
let hs := firstn (Z.to_nat (pg_header_len og)) (skipn (Z.to_nat (pg_hdr og)) bytes) in
let bs := firstn (Z.to_nat (pg_body_len og)) (skipn (Z.to_nat (pg_hdr og + pg_header_len og)) bytes) in
bytes_at bsegs m (D + pg_hdr og) hs /\ bytes_at bsegs m (D + pg_hdr og + pg_header_len og) bs
/\ Z.of_nat (length hs) = pg_header_len og /\ Z.of_nat (length bs) = pg_body_len og
/\ ubytes hs = page_header oy og /\ ubytes bs = page_body oy og
/\ pg_header_len og = 27 + znth (ubytes hs) 26 /\ 0 <= znth (ubytes hs) 26 <= 255
/\ 0 <= pg_hdr og /\ pg_hdr og + pg_header_len og + pg_body_len og <= Z.of_nat (length bytes)
/\ 0 <= pg_body_len og.
Proof.
intros m A D oy bytes og (OBJ & FOK & DAT & SEP) SINV POK NN. cbv zeta.
pose proof POK as (P0 & P1 & P2 & P3 & P4 & P5 & P6).
pose proof SINV as (I1 & I2 & I3 & I4 & I5). unfold zlength in I2, P5.
unfold sync_data in DAT. destruct (sy_data oy) as [p|]; [| exfalso; exact (NN eq_refl)].
destruct DAT as (D1 & (BA & WR) & LEN & PRE & LE).
pose proof (znth_bytes_ok (sy_buf oy) (pg_hdr og + 26) I5) as NS.
assert (HH : ubytes (firstn (Z.to_nat (pg_header_len og)) (skipn (Z.to_nat (pg_hdr og)) bytes)) = page_header oy og).
{ unfold page_header. rewrite ubytes_firstn, ubytes_skipn. symmetry. apply zslice_of_prefix_a; try assumption; try lia.
unfold ubytes. rewrite length_map. exact LE. }
assert (HB : ubytes (firstn (Z.to_nat (pg_body_len og)) (skipn (Z.to_nat (pg_hdr og + pg_header_len og)) bytes)) = page_body oy og).
{ unfold page_body. rewrite ubytes_firstn, ubytes_skipn. symmetry. apply zslice_of_prefix_a; try assumption; try lia.
unfold ubytes. rewrite length_map. exact LE. }
assert (N26 : znth (page_header oy og) 26 = znth (sy_buf oy) (pg_hdr og + 26)).
{ unfold page_header. apply znth_zslice; lia. }
split. { replace (D + pg_hdr og) with (D + Z.of_nat (Z.to_nat (pg_hdr og))) by lia. apply bytes_at_sub; [exact BA| lia]. }
split. { replace (D + pg_hdr og + pg_header_len og) with (D + Z.of_nat (Z.to_nat (pg_hdr og + pg_header_len og))) by lia. apply bytes_at_sub; [exact BA| lia]. }
split. { rewrite firstn_length_le; [lia|]. rewrite length_skipn. lia. }
split. { rewrite firstn_length_le; [lia|]. rewrite length_skipn. lia. }
split; [exact HH|]. split; [exact HB|]. rewrite HH, N26. lia.
Qed.

Definition pb_h1 (h : hstate unit) (serial : Z) : hstate unit :=
if h_stream_init h =? 0 then set_stream_init h (init_os (Some tt) (Some tt) (Some tt) serial) else h.
Definition pb_h2 (h1 : hstate unit) (serial : Z) : hstate unit :=
if negb (serial =? os_serialno (h_os h1)) then set_ogg h1 (h_oy h1) (snd (ogg_stream_reset_serialno (h_os h1) serial)) else h1.

Lemma pb_pre_run : forall (h : hstate unit) og q h3 q3,
prun (pb_pre h og) q = Some (h3, q3) ->
exists ro, prun (ogg_stream_pagein (St := pst) p_realloc p_free
(h_os (pb_h2 (pb_h1 h (ogg_page_serialno (page_header (h_oy h) og))) (ogg_page_serialno (page_header (h_oy h) og))))
(page_header (h_oy h) og) (page_body (h_oy h) og)) q = Some (ro, q3)
/\ h3 = set_ogg (pb_h2 (pb_h1 h (ogg_page_serialno (page_header (h_oy h) og))) (ogg_page_serialno (page_header (h_oy h) og)))
(h_oy h) (snd ro).
Proof.
intros h og q h3 q3 H. unfold pb_pre in H. cbv zeta in H.
set (serial := ogg_page_serialno (page_header (h_oy h) og)) in *.
rewrite prun_bind in H.
assert (E1 : prun (if h_stream_init h =? 0
then X1qy.mbind (ogg_stream_init p_malloc p_free serial) (fun ro => X1qy.mret (set_stream_init h (snd ro)))
else X1qy.mret h) q = Some (pb_h1 h serial, q)).
{ unfold pb_h1. destruct (h_stream_init h =? 0); [| apply prun_ret].
rewrite prun_bind. destruct (prun (ogg_stream_init p_malloc p_free serial) q) as [[ro1 q1]|] eqn:EI.
- apply stream_init_prun in EI as (-> & ->). apply prun_ret.
- exfalso. unfold ogg_stream_init in EI.
rewrite prun_bind, (prun_malloc_ok 16384) in EI by reflexivity. cbn beta iota in EI.
rewrite prun_bind, (prun_malloc_ok 4096) in EI by reflexivity. cbn beta iota in EI.
rewrite prun_bind, (prun_malloc_ok 8192) in EI by reflexivity. cbn beta iota in EI. discriminate EI. }
rewrite E1 in H. clear E1.
assert (E2 : (if negb (serial =? os_serialno (h_os (pb_h1 h serial)))
then let '(_, os) := ogg_stream_reset_serialno (h_os (pb_h1 h serial)) serial in set_ogg (pb_h1 h serial) (h_oy (pb_h1 h serial)) os
else pb_h1 h serial) = pb_h2 (pb_h1 h serial) serial).
{ unfold pb_h2. destruct (negb _); [| reflexivity]. destruct (ogg_stream_reset_serialno _ _); reflexivity. }
cbv beta in H. rewrite E2 in H. clear E2.
rewrite prun_bind in H.
destruct (prun (ogg_stream_pagein p_realloc p_free (h_os (pb_h2 (pb_h1 h serial) serial)) (page_header (h_oy h) og) (page_body (h_oy h) og)) q)
as [[ro q2]|] eqn:EP; [| discriminate H].
rewrite prun_ret in H. injection H as <- <-.
exists ro. split; [reflexivity|].
assert (EOY : h_oy (pb_h2 (pb_h1 h serial) serial) = h_oy h).
{ unfold pb_h2, pb_h1. destruct (h_stream_init h =? 0); destruct (negb _); reflexivity. }
rewrite EOY. reflexivity.
Qed.

Lemma cells32_junk4_a : forall (m : mem) A cs, rw_cells bsegs m A cs -> cells_size cs = 32%nat ->
exists j0 j1 j2 j3, rw_cells bsegs m A [CB 8 j0; CB 8 j1; CB 8 j2; CB 8 j3].
Proof.
intros m A cs H Hs. apply rw_cells_forget in H. rewrite Hs in H. destruct H as [junk H].
apply (rw_cells_split_CB _ _ _ [] _ _ [] [8; 8; 8; 8]%nat) in H; [| reflexivity]. cbn [mk_CB_cells app] in H.
do 4 eexists. exact H.
Qed.

Section Cuts.
Variable RT : rt_sig.
Variable OUT_rep : X1s9.stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable IO_FP : list (Z * Z).
Variable X : hinv.
Variable F0 : list (word * FdEntry).
Variable fs0 : Fs.Fs.
Local Notation PMh := (PMfd F0 fs0).
Local Notation F := (x_F X).

Definition at_P2 (h : hstate unit) (og : page) (nbr brem0 : Z) : config -> Prop :=
fun c => exists (Σ1 : rts RT) (a : haux) (Fx : bvmap 5 word) (fc : bv 32) (m : mem) (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r5 r8 t3 t4 t5 t6 : word)
(v48 v56 v88 j224 j232 : word) (opc : list cell),
ASTA RT Σ1 PMh (eq (MS (h_regs X h ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z64 (h_last_granule h)) r5 (Z64 (F + HO_OS)) r8 (Z64 (F + HO_OG)) (Z64 (h_eos h))
t3 t4 t5 t6) Fx (Z64 0x96d8c) fc None m (seg_rom bsegs))) c
/\ X1cn.frm0 fc /\ hsig RT X Σ1 a h /\ h_iter X h nbr brem0 /\ h_stream_init h = 1
/\ hrep RT OUT_rep ERR_rep IO_FP X Σ1 m a h (h_spill X (Z64 (h_bytes_remaining h)) v48 v56 v88 j224 j232 a h) (page_cells (a_Dsy a) og) opc
/\ op_junk opc /\ page_ok (h_oy h) og /\ h_page_budget X h og.

Definition at_P3 (h : hstate unit) (og : page) (nbr brem0 : Z) : config -> Prop :=
fun c => exists (Σ1 : rts RT) (a : haux) (Fx : bvmap 5 word) (fc : bv 32) (m : mem) (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r5 r8 t3 t4 t5 t6 : word)
(v48 v56 v88 j224 j232 : word) (opc : list cell),
ASTA RT Σ1 PMh (eq (MS (h_regs X h (Z64 0x96dbc) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z64 (h_last_granule h)) r5 (Z64 (F + HO_OS)) r8 (Z64 (F + HO_OG))
(Z64 (h_eos h)) t3 t4 t5 t6) Fx (ret_pc (Z64 0x96dbc)) fc None m (seg_rom bsegs))) c
/\ X1cn.frm0 fc /\ hsig RT X Σ1 a h /\ h_iter X h nbr brem0 /\ h_stream_init h = 1
/\ hrep RT OUT_rep ERR_rep IO_FP X Σ1 m a h (h_spill X (Z64 (h_bytes_remaining h)) v48 v56 v88 j224 j232 a h) (page_cells (a_Dsy a) og) opc
/\ op_junk opc /\ page_ok (h_oy h) og /\ os_body_returned (h_os h) = 0.

Definition at_PC (h : hstate unit) (og : page) (nbr brem0 : Z) : config -> Prop :=
fun c => exists (Σ1 : rts RT) (a : haux) (Fx : bvmap 5 word) (fc : bv 32) (m : mem) (t0 t1 t2 a2 a3 a4 a5 a6 a7 r5 r8 t3 t4 t5 t6 : word)
(v48 v56 v88 j224 j232 : word) (opc : list cell),
ASTA RT Σ1 PMh (eq (MS (h_regs X h (Z64 0x96dbc) t0 t1 t2 (Z64 (F + HO_OS)) (Z64 (F + HO_OG)) a2 a3 a4 a5 a6 a7 (Z64 (h_last_granule h)) r5 (Z64 (F + HO_OS))
r8 (Z64 (F + HO_OG)) (Z64 (h_eos h)) t3 t4 t5 t6) Fx (Z64 A_ogg_stream_pagein) fc None m (seg_rom bsegs))) c
/\ X1cn.frm0 fc /\ hsig RT X Σ1 a h /\ h_iter X h nbr brem0 /\ h_stream_init h = 1
/\ hrep RT OUT_rep ERR_rep IO_FP X Σ1 m a h (h_spill X (Z64 (h_bytes_remaining h)) v48 v56 v88 j224 j232 a h) (page_cells (a_Dsy a) og) opc
/\ op_junk opc /\ page_ok (h_oy h) og /\ h_page_budget X h og.

Definition page_post (h3 : hstate unit) (hdr : list Z) (nbr brem0 : Z) : config -> Prop :=
fun c => match granule_step h3 hdr with
| None => at_XT RT OUT_rep ERR_rep IO_FP X F0 fs0 c
| Some skip => let h4 := set_granule h3 (ogg_page_granulepos hdr) skip in
(h_eos h4 = 0 /\ at_KH RT OUT_rep ERR_rep IO_FP X F0 fs0 h4 0 nbr brem0 c)
\/ (h_eos h4 <> 0 /\ at_PN RT OUT_rep ERR_rep IO_FP X F0 fs0 h4 nbr brem0 c)
end.
End Cuts.

Lemma hsig_set_granule : forall RT X (Σ1 : rts RT) a (h : hstate unit) lg sk, hsig RT X Σ1 a h -> hsig RT X Σ1 a (set_granule h lg sk).
Proof. intros RT X Σ1 a h lg sk H. unfold hsig, h_own, h_cost in *. cbn [set_granule h_st h_bits h_stream_init h_os h_oy h_packet_count]. exact H. Qed.

Lemma hrep_set_granule : forall RT OUT_rep ERR_rep IO_FP X (Σ1 : rts RT) (m : mem) a (h : hstate unit) spill ogc opc lg sk,
hrep RT OUT_rep ERR_rep IO_FP X Σ1 m a h spill ogc opc -> -1 <= lg < 2^63 -> -2^31 < sk < 2^31 ->
hrep RT OUT_rep ERR_rep IO_FP X Σ1 m a (set_granule h lg sk) spill ogc opc.
Proof.
intros RT OUT_rep ERR_rep IO_FP X Σ1 m a h spill ogc opc lg sk HR LG SKR.
destruct HR as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & A18 & A19 & A20 & A21 & HP).
unfold hrep. cbn [set_granule h_frame_size h_bits h_oy h_rate].
do 16 (split; [assumption|]).
split; [unfold h_os_rep in *; cbn [set_granule h_stream_init h_os]; exact A17|].
do 3 (split; [assumption|]).
split; [unfold h_dec_rep in *; cbn [set_granule h_st]; exact A21|].
unfold hpure, h_consumed, h_pend in *.
cbn [set_granule h_oy h_os h_bits h_st h_stream_init h_packet_count h_last_granule h_nframes h_eos h_channels h_rate h_extra_headers
h_speex_serialno h_frame_size h_granule_frame_size h_bytes_remaining].
destruct HP as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12 & B13 & (B14a & _) & B15 & B16 & REST).
do 13 (split; [assumption|]). split; [split; [exact B14a| exact SKR]|]. split; [assumption|]. split; [exact LG| exact REST].
Qed.

Lemma hrep_ogc : forall RT OUT_rep ERR_rep IO_FP X (Σ1 : rts RT) (m : mem) a (h : hstate unit) spill ogc ogc' opc,
hrep RT OUT_rep ERR_rep IO_FP X Σ1 m a h spill ogc opc -> rw_cells bsegs m (x_F X + HO_OG) ogc' ->
hrep RT OUT_rep ERR_rep IO_FP X Σ1 m a h spill ogc' opc.
Proof.
intros RT OUT_rep ERR_rep IO_FP X Σ1 m a h spill ogc ogc' opc HR OG'.
destruct HR as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & REST).
unfold hrep. do 14 (split; [assumption|]). split; [exact OG'| exact REST].
Qed.
Lemma hrep_og_junk : forall RT OUT_rep ERR_rep IO_FP X (Σ1 : rts RT) (m : mem) a (h : hstate unit) spill D og opc,
hrep RT OUT_rep ERR_rep IO_FP X Σ1 m a h spill (page_cells D og) opc ->
exists ogc, hrep RT OUT_rep ERR_rep IO_FP X Σ1 m a h spill ogc opc /\ og_junk ogc.
Proof.
intros RT OUT_rep ERR_rep IO_FP X Σ1 m a h spill D og opc HR.
pose proof HR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & OG & _).
destruct (cells32_junk4_a _ _ _ OG eq_refl) as (j0 & j1 & j2 & j3 & OG').
exists [CB 8 j0; CB 8 j1; CB 8 j2; CB 8 j3]. split; [exact (hrep_ogc _ _ _ _ _ _ _ _ _ _ _ _ _ HR OG')| do 4 eexists; reflexivity].
Qed.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation mem := (word -> option byte).
Local Notation Z64 := (Z_to_bv 64).

Lemma zslice_of_prefix_a : forall (buf : list Z) (ub : list Z) a n,
firstn (length buf) ub = buf -> (length buf <= length ub)%nat -> 0 <= a -> 0 <= n -> a + n <= Z.of_nat (length buf) ->
zslice a n buf = firstn (Z.to_nat n) (skipn (Z.to_nat a) ub).
Proof.
intros buf ub a n PRE LE Ha Hn Han. unfold zslice, ztake, zdrop. rewrite <- PRE.
rewrite skipn_firstn_comm. rewrite firstn_firstn. f_equal. lia.
Qed.

Lemma page_hs_a : forall (m : mem) A D (oy : sync_st bptr) bytes og,
sync_rep m A D oy bytes -> sync_inv oy -> page_ok oy og -> sy_data oy <> None ->
let hs := firstn (Z.to_nat (pg_header_len og)) (skipn (Z.to_nat (pg_hdr og)) bytes) in
let bs := firstn (Z.to_nat (pg_body_len og)) (skipn (Z.to_nat (pg_hdr og + pg_header_len og)) bytes) in
bytes_at asegs m (D + pg_hdr og) hs /\ bytes_at asegs m (D + pg_hdr og + pg_header_len og) bs
/\ Z.of_nat (length hs) = pg_header_len og /\ Z.of_nat (length bs) = pg_body_len og
/\ ubytes hs = page_header oy og /\ ubytes bs = page_body oy og
/\ pg_header_len og = 27 + znth (ubytes hs) 26 /\ 0 <= znth (ubytes hs) 26 <= 255
/\ 0 <= pg_hdr og /\ pg_hdr og + pg_header_len og + pg_body_len og <= Z.of_nat (length bytes)
/\ 0 <= pg_body_len og.
Proof.
intros m A D oy bytes og (OBJ & FOK & DAT & SEP) SINV POK NN. cbv zeta.
pose proof POK as (P0 & P1 & P2 & P3 & P4 & P5 & P6).
pose proof SINV as (I1 & I2 & I3 & I4 & I5). unfold zlength in I2, P5.
unfold sync_data in DAT. destruct (sy_data oy) as [p|]; [| exfalso; exact (NN eq_refl)].
destruct DAT as (D1 & (BA & WR) & LEN & PRE & LE).
pose proof (znth_bytes_ok (sy_buf oy) (pg_hdr og + 26) I5) as NS.
assert (HH : ubytes (firstn (Z.to_nat (pg_header_len og)) (skipn (Z.to_nat (pg_hdr og)) bytes)) = page_header oy og).
{ unfold page_header. rewrite ubytes_firstn, ubytes_skipn. symmetry. apply zslice_of_prefix_a; try assumption; try lia.
unfold ubytes. rewrite length_map. exact LE. }
assert (HB : ubytes (firstn (Z.to_nat (pg_body_len og)) (skipn (Z.to_nat (pg_hdr og + pg_header_len og)) bytes)) = page_body oy og).
{ unfold page_body. rewrite ubytes_firstn, ubytes_skipn. symmetry. apply zslice_of_prefix_a; try assumption; try lia.
unfold ubytes. rewrite length_map. exact LE. }
assert (N26 : znth (page_header oy og) 26 = znth (sy_buf oy) (pg_hdr og + 26)).
{ unfold page_header. apply znth_zslice; lia. }
split. { replace (D + pg_hdr og) with (D + Z.of_nat (Z.to_nat (pg_hdr og))) by lia. apply bytes_at_sub; [exact BA| lia]. }
split. { replace (D + pg_hdr og + pg_header_len og) with (D + Z.of_nat (Z.to_nat (pg_hdr og + pg_header_len og))) by lia. apply bytes_at_sub; [exact BA| lia]. }
split. { rewrite firstn_length_le; [lia|]. rewrite length_skipn. lia. }
split. { rewrite firstn_length_le; [lia|]. rewrite length_skipn. lia. }
split; [exact HH|]. split; [exact HB|]. rewrite HH, N26. lia.
Qed.

Definition pb_h1 (h : hstate unit) (serial : Z) : hstate unit :=
if h_stream_init h =? 0 then set_stream_init h (init_os (Some tt) (Some tt) (Some tt) serial) else h.
Definition pb_h2 (h1 : hstate unit) (serial : Z) : hstate unit :=
if negb (serial =? os_serialno (h_os h1)) then set_ogg h1 (h_oy h1) (snd (ogg_stream_reset_serialno (h_os h1) serial)) else h1.

Lemma pb_pre_run : forall (h : hstate unit) og q h3 q3,
prun (pb_pre h og) q = Some (h3, q3) ->
exists ro, prun (ogg_stream_pagein (St := pst) p_realloc p_free
(h_os (pb_h2 (pb_h1 h (ogg_page_serialno (page_header (h_oy h) og))) (ogg_page_serialno (page_header (h_oy h) og))))
(page_header (h_oy h) og) (page_body (h_oy h) og)) q = Some (ro, q3)
/\ h3 = set_ogg (pb_h2 (pb_h1 h (ogg_page_serialno (page_header (h_oy h) og))) (ogg_page_serialno (page_header (h_oy h) og)))
(h_oy h) (snd ro).
Proof.
intros h og q h3 q3 H. unfold pb_pre in H. cbv zeta in H.
set (serial := ogg_page_serialno (page_header (h_oy h) og)) in *.
rewrite prun_bind in H.
assert (E1 : prun (if h_stream_init h =? 0
then X1qy.mbind (ogg_stream_init p_malloc p_free serial) (fun ro => X1qy.mret (set_stream_init h (snd ro)))
else X1qy.mret h) q = Some (pb_h1 h serial, q)).
{ unfold pb_h1. destruct (h_stream_init h =? 0); [| apply prun_ret].
rewrite prun_bind. destruct (prun (ogg_stream_init p_malloc p_free serial) q) as [[ro1 q1]|] eqn:EI.
- apply stream_init_prun in EI as (-> & ->). apply prun_ret.
- exfalso. unfold ogg_stream_init in EI.
rewrite prun_bind, (prun_malloc_ok 16384) in EI by reflexivity. cbn beta iota in EI.
rewrite prun_bind, (prun_malloc_ok 4096) in EI by reflexivity. cbn beta iota in EI.
rewrite prun_bind, (prun_malloc_ok 8192) in EI by reflexivity. cbn beta iota in EI. discriminate EI. }
rewrite E1 in H. clear E1.
assert (E2 : (if negb (serial =? os_serialno (h_os (pb_h1 h serial)))
then let '(_, os) := ogg_stream_reset_serialno (h_os (pb_h1 h serial)) serial in set_ogg (pb_h1 h serial) (h_oy (pb_h1 h serial)) os
else pb_h1 h serial) = pb_h2 (pb_h1 h serial) serial).
{ unfold pb_h2. destruct (negb _); [| reflexivity]. destruct (ogg_stream_reset_serialno _ _); reflexivity. }
cbv beta in H. rewrite E2 in H. clear E2.
rewrite prun_bind in H.
destruct (prun (ogg_stream_pagein p_realloc p_free (h_os (pb_h2 (pb_h1 h serial) serial)) (page_header (h_oy h) og) (page_body (h_oy h) og)) q)
as [[ro q2]|] eqn:EP; [| discriminate H].
rewrite prun_ret in H. injection H as <- <-.
exists ro. split; [reflexivity|].
assert (EOY : h_oy (pb_h2 (pb_h1 h serial) serial) = h_oy h).
{ unfold pb_h2, pb_h1. destruct (h_stream_init h =? 0); destruct (negb _); reflexivity. }
rewrite EOY. reflexivity.
Qed.

Lemma cells32_junk4_a : forall (m : mem) A cs, rw_cells asegs m A cs -> cells_size cs = 32%nat ->
exists j0 j1 j2 j3, rw_cells asegs m A [CB 8 j0; CB 8 j1; CB 8 j2; CB 8 j3].
Proof.
intros m A cs H Hs. apply rw_cells_forget in H. rewrite Hs in H. destruct H as [junk H].
apply (rw_cells_split_CB _ _ _ [] _ _ [] [8; 8; 8; 8]%nat) in H; [| reflexivity]. cbn [mk_CB_cells app] in H.
do 4 eexists. exact H.
Qed.

Section Cuts.
Variable RT : rt_sig.
Variable OUT_rep : X1s9.stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable IO_FP : list (Z * Z).
Variable X : hinv.
Variable F0 : list (word * FdEntry).
Variable fs0 : Fs.Fs.
Local Notation PMh := (PMfd F0 fs0).
Local Notation F := (x_F X).

Definition at_P2 (h : hstate unit) (og : page) (nbr brem0 : Z) : config -> Prop :=
fun c => exists (Σ1 : rts RT) (a : haux) (Fx : bvmap 5 word) (fc : bv 32) (m : mem) (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r5 t3 t4 t5 t6 : word)
(j0 j192 j200 : word) (opc : list cell),
ASTA RT Σ1 PMh (eq (MS (h_regs X h a ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r5 (Z64 (F + HO_OS)) (Z64 (h_last_granule h)) t3 t4 t5 t6)
Fx (Z64 0x96c88) fc None m (seg_rom asegs))) c
/\ X1cn.frm0 fc /\ hsig RT X Σ1 a h /\ h_iter X h nbr brem0 /\ h_stream_init h = 1
/\ hrep RT OUT_rep ERR_rep IO_FP X Σ1 m a h (h_spill X (Z64 nbr) (Z64 brem0) (Z64 (h_last_granule h)) (Z64 (h_speex_serialno h)) j0 j192 j200 h)
(page_cells (a_Dsy a) og) opc
/\ op_junk opc /\ page_ok (h_oy h) og /\ h_page_budget X h og.

Definition at_P3 (h : hstate unit) (og : page) (nbr brem0 : Z) : config -> Prop :=
fun c => exists (Σ1 : rts RT) (a : haux) (Fx : bvmap 5 word) (fc : bv 32) (m : mem) (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r5 t3 t4 t5 t6 : word)
(j0 j192 j200 : word) (opc : list cell),
ASTA RT Σ1 PMh (eq (MS (h_regs X h a (Z64 0x96cb8) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 r5 (Z64 (F + HO_OS)) (Z64 (h_last_granule h)) t3 t4 t5 t6)
Fx (ret_pc (Z64 0x96cb8)) fc None m (seg_rom asegs))) c
/\ X1cn.frm0 fc /\ hsig RT X Σ1 a h /\ h_iter X h nbr brem0 /\ h_stream_init h = 1
/\ hrep RT OUT_rep ERR_rep IO_FP X Σ1 m a h (h_spill X (Z64 nbr) (Z64 brem0) (Z64 (h_last_granule h)) (Z64 (h_speex_serialno h)) j0 j192 j200 h)
(page_cells (a_Dsy a) og) opc
/\ op_junk opc /\ page_ok (h_oy h) og.

Definition at_PC (h : hstate unit) (og : page) (nbr brem0 : Z) : config -> Prop :=
fun c => exists (Σ1 : rts RT) (a : haux) (Fx : bvmap 5 word) (fc : bv 32) (m : mem) (t0 t1 t2 a2 a3 a4 a5 a6 a7 r5 t3 t4 t5 t6 : word)
(j0 j192 j200 : word) (opc : list cell),
ASTA RT Σ1 PMh (eq (MS (h_regs X h a (Z64 0x96cb8) t0 t1 t2 (Z64 (F + HO_OS)) (Z64 (F + HO_OG)) a2 a3 a4 a5 a6 a7 r5 (Z64 (F + HO_OS))
(Z64 (h_last_granule h)) t3 t4 t5 t6) Fx (Z64 A_ogg_stream_pagein) fc None m (seg_rom asegs))) c
/\ X1cn.frm0 fc /\ hsig RT X Σ1 a h /\ h_iter X h nbr brem0 /\ h_stream_init h = 1
/\ hrep RT OUT_rep ERR_rep IO_FP X Σ1 m a h (h_spill X (Z64 nbr) (Z64 brem0) (Z64 (h_last_granule h)) (Z64 (h_speex_serialno h)) j0 j192 j200 h)
(page_cells (a_Dsy a) og) opc
/\ op_junk opc /\ page_ok (h_oy h) og /\ h_page_budget X h og.

Definition page_post (h3 : hstate unit) (hdr : list Z) (nbr brem0 : Z) : config -> Prop :=
fun c => match granule_step h3 hdr with
| None => at_XT RT OUT_rep ERR_rep IO_FP X F0 fs0 c
| Some skip => let h4 := set_granule h3 (ogg_page_granulepos hdr) skip in
(h_eos h4 = 0 /\ at_KH RT OUT_rep ERR_rep IO_FP X F0 fs0 h4 0 nbr brem0 c)
\/ (h_eos h4 <> 0 /\ at_PN RT OUT_rep ERR_rep IO_FP X F0 fs0 h4 nbr brem0 c)
end.
End Cuts.

Lemma hsig_set_granule : forall RT X (Σ1 : rts RT) a (h : hstate unit) lg sk, hsig RT X Σ1 a h -> hsig RT X Σ1 a (set_granule h lg sk).
Proof. intros RT X Σ1 a h lg sk H. unfold hsig, h_own, h_cost in *. cbn [set_granule h_st h_bits h_stream_init h_os h_oy h_packet_count]. exact H. Qed.

Lemma hrep_set_granule : forall RT OUT_rep ERR_rep IO_FP X (Σ1 : rts RT) (m : mem) a (h : hstate unit) spill ogc opc lg sk,
hrep RT OUT_rep ERR_rep IO_FP X Σ1 m a h spill ogc opc -> -1 <= lg < 2^63 ->
hrep RT OUT_rep ERR_rep IO_FP X Σ1 m a (set_granule h lg sk) spill ogc opc.
Proof.
intros RT OUT_rep ERR_rep IO_FP X Σ1 m a h spill ogc opc lg sk HR LG.
destruct HR as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & A18 & A19 & A20 & A21 & HP).
unfold hrep. cbn [set_granule h_frame_size h_bits h_oy h_rate].
do 16 (split; [assumption|]).
split; [unfold h_os_rep in *; cbn [set_granule h_stream_init h_os]; exact A17|].
do 3 (split; [assumption|]).
split; [unfold h_dec_rep in *; cbn [set_granule h_st]; exact A21|].
unfold hpure, h_consumed, h_pend in *.
cbn [set_granule h_oy h_os h_bits h_st h_stream_init h_packet_count h_last_granule h_nframes h_eos h_channels h_rate h_extra_headers
h_speex_serialno h_frame_size h_granule_frame_size h_bytes_remaining].
destruct HP as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12 & B13 & B14 & B15 & B16 & REST).
do 15 (split; [assumption|]). split; [exact LG| exact REST].
Qed.

Lemma hrep_ogc : forall RT OUT_rep ERR_rep IO_FP X (Σ1 : rts RT) (m : mem) a (h : hstate unit) spill ogc ogc' opc,
hrep RT OUT_rep ERR_rep IO_FP X Σ1 m a h spill ogc opc -> rw_cells asegs m (x_F X + HO_OG) ogc' ->
hrep RT OUT_rep ERR_rep IO_FP X Σ1 m a h spill ogc' opc.
Proof.
intros RT OUT_rep ERR_rep IO_FP X Σ1 m a h spill ogc ogc' opc HR OG'.
destruct HR as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & REST).
unfold hrep. do 14 (split; [assumption|]). split; [exact OG'| exact REST].
Qed.
Lemma hrep_og_junk : forall RT OUT_rep ERR_rep IO_FP X (Σ1 : rts RT) (m : mem) a (h : hstate unit) spill D og opc,
hrep RT OUT_rep ERR_rep IO_FP X Σ1 m a h spill (page_cells D og) opc ->
exists ogc, hrep RT OUT_rep ERR_rep IO_FP X Σ1 m a h spill ogc opc /\ og_junk ogc.
Proof.
intros RT OUT_rep ERR_rep IO_FP X Σ1 m a h spill D og opc HR.
pose proof HR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & OG & _).
destruct (cells32_junk4_a _ _ _ OG eq_refl) as (j0 & j1 & j2 & j3 & OG').
exists [CB 8 j0; CB 8 j1; CB 8 j2; CB 8 j3]. split; [exact (hrep_ogc _ _ _ _ _ _ _ _ _ _ _ _ _ HR OG')| do 4 eexists; reflexivity].
Qed.
