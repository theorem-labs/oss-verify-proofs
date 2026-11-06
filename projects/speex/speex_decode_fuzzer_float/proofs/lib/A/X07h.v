(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0mx X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1da X1dg X1cg X1ck.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.SpecA Require X1s9.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qz X1nt X1rg X1rh X1re X1od X1r8.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X001 X00a X00b X000 X04b X00c X07z X05o X05s X05t
X0ae X09u X09x X0af X09p X09l X0a4 X0a5 X0ab X09v X09w
X09n X05l X05e X05c X05m X09f X06d X069 X068 X07m
X071 X06v X06y X06u X073 X07j X072 X079.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X0yr X12c X14x X0r0 X0r9 X0ra X0qz X0v9 X0rb X0wl X0wm X110 X10j X10c X108 X10q X10r X10x X10h X10i X10a X0wb X0w9 X0x2 X0x1 X0xn X0xq X0xm X0xu X0ya X0xt X0y0.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X10g.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yr OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0qz OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0v9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0rb OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wl OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wm OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X110 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10j OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X108 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10q OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10r OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10h OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10i OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10a OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wb OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0w9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0x2 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0x1 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xn OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xq OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xm OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xu OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ya OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xt OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0y0.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation mem := (word -> option byte).

Definition h_with_os (h : hstate unit) (os : stream_st unit) (si : Z) : hstate unit :=
mkH (h_oy h) os (h_bits h) (h_st h) si (h_packet_count h) (h_last_granule h) (h_skip_samples h)
(h_nframes h) (h_eos h) (h_channels h) (h_rate h) (h_extra_headers h) (h_speex_serialno h)
(h_frame_size h) (h_granule_frame_size h) (h_bytes_remaining h).
Lemma set_stream_init_with : forall h os, set_stream_init h os = h_with_os h os 1.
Proof. reflexivity. Qed.
Lemma set_ogg_with : forall h os, set_ogg h (h_oy h) os = h_with_os h os (h_stream_init h).
Proof. reflexivity. Qed.

Definition a_set_os (a : haux) (Bd L G : Z) (shdr body : list byte) (lws gws : list word) (P : list (Z * Z)) : haux :=
HA (a_Dsy a) (a_sybytes a) Bd L G shdr body lws gws (a_Dc a) (a_S a) (a_LBD a) P.

Lemma own_ne_os : forall a (h : hstate unit), List.NoDup (map fst (h_own a h)) -> h_stream_init h <> 0 ->
forall p, p = a_Bd a \/ p = a_L a \/ p = a_G a ->
a_Dc a <> p /\ (sy_data (h_oy h) <> None -> a_Dsy a <> p) /\ (h_st h <> None -> forall b, In b (a_LBD a) -> blk_addr b <> p).
Proof.
intros a h ND NE p Hp. unfold h_own in ND. replace (h_stream_init h =? 0) with false in ND by (symmetry; apply Z.eqb_neq; exact NE).
rewrite !map_app in ND. cbn [map fst app] in ND.
split; [| split].
- apply NoDup_app_remove_l in ND. apply NoDup_cons_iff in ND as (N1 & _). intros E. apply N1. rewrite E.
destruct Hp as [->|[->| ->]]; [left| right; left| right; right; left]; reflexivity.
- intros NS. destruct (sy_data (h_oy h)) as [q|]; [| congruence]. cbn [map fst] in ND.
apply NoDup_app_remove_l in ND. apply NoDup_cons_iff in ND as (_ & ND).
apply NoDup_cons_iff in ND as (B1 & ND). apply NoDup_cons_iff in ND as (B2 & ND). apply NoDup_cons_iff in ND as (B3 & _).
intros E. destruct Hp as [->|[->| ->]].
+ apply B1. rewrite <- E. right; right; left; reflexivity.
+ apply B2. rewrite <- E. right; left; reflexivity.
+ apply B3. rewrite <- E. left; reflexivity.
- intros NS b Hb E. destruct (h_st h) as [d|]; [| congruence].
apply (nodup_app_disj _ _ (blk_addr b) ND); [unfold blocks_live; rewrite map_map; apply in_map_iff; exists b; split; [reflexivity| exact Hb]|].
rewrite E. destruct Hp as [->|[->| ->]]; [right; left| right; right; left| right; right; right; left]; reflexivity.
Qed.

Lemma live_remove_mid : forall p n (A B : list (Z * Z)), List.NoDup (map fst (A ++ (p, n) :: B)) -> live_remove p (A ++ (p, n) :: B) = A ++ B.
Proof.
intros p n A B ND. rewrite map_app in ND. cbn [map fst] in ND.
rewrite live_remove_app, live_remove_cons. cbn [fst]. rewrite Z.eqb_refl.
rewrite (live_remove_none p A), (live_remove_none p B); [reflexivity| |].
- intros e He E. apply NoDup_app_remove_l in ND. apply NoDup_cons_iff in ND as (NI & _). apply NI. rewrite <- E. apply in_map. exact He.
- intros e He E. apply (nodup_app_disj _ _ p ND); [rewrite <- E; apply in_map; exact He| left; reflexivity].
Qed.
Lemma perm_live_remove_mid : forall p n (P A B : list (Z * Z)), Permutation P (A ++ (p, n) :: B) -> List.NoDup (map fst (A ++ (p, n) :: B)) ->
Permutation (live_remove p P) (A ++ B).
Proof. intros p n P A B PERM ND. rewrite <- (live_remove_mid p n A B ND). apply perm_live_remove. exact PERM. Qed.

Lemma pagein_live_app : forall l1 l2 os hdr body Bd L Gv Bd' L' Gv',
(forall e, In e l2 -> fst e <> Bd /\ fst e <> L /\ fst e <> Gv) ->
pagein_live (l1 ++ l2) os hdr body Bd L Gv Bd' L' Gv' = pagein_live l1 os hdr body Bd L Gv Bd' L' Gv' ++ l2.
Proof.
intros l1 l2 os hdr body Bd L Gv Bd' L' Gv' H2.
assert (N1 : live_remove Bd l2 = l2) by (apply live_remove_none; intros e He; exact (proj1 (H2 e He))).
assert (N2 : live_remove L l2 = l2) by (apply live_remove_none; intros e He; exact (proj1 (proj2 (H2 e He)))).
assert (N3 : live_remove Gv l2 = l2) by (apply live_remove_none; intros e He; exact (proj2 (proj2 (H2 e He)))).
unfold pagein_live. destruct (pgi_ok os hdr); [| reflexivity]. cbv zeta.
destruct (os_lacing_fill (pagein_returned os) <? os_lacing_storage (pagein_returned os) - (znth hdr 26 + 1));
destruct ((zlength body - snd (pagein_skip (pgi_os3 os hdr) hdr) =? 0)
|| (os_body_fill (pgi_os3 os hdr) <? os_body_storage (pgi_os3 os hdr) - (zlength body - snd (pagein_skip (pgi_os3 os hdr) hdr))));
try reflexivity;
rewrite ?live_remove_app, ?N1, ?N2, ?N3; rewrite ?app_comm_cons; rewrite ?live_remove_app, ?N1, ?N2, ?N3; rewrite ?app_comm_cons; reflexivity.
Qed.

Section PStep.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable OUT_rep : X1s9.stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable IO_FP : list (Z * Z).
Hypothesis ERR_loc : fp_local IO_FP ERR_rep.
Hypothesis OUT_loc : forall so, fp_local IO_FP (OUT_rep so).
Hypothesis IO_img : forall y, in_ranges IO_FP y -> client_static y.
Hypothesis AF_DRV : forall Σ m, ART RT Σ m -> drv_consts m.
Variable X : hinv.
Hypothesis HX : hinv_ok OUT_rep IO_FP X.
Local Notation S1 := (x_S1 X). Local Notation lo := (x_lo X). Local Notation F := (x_F X). Local Notation sf := (x_sf X).

Lemma hrep_os_step : forall (Σ1 Σ2 : rts RT) (m m' : mem) a a' (h h' : hstate unit) spill ogc opc (Lv : list (Z * Z)),
hsig RT X Σ1 a h -> hrep RT OUT_rep ERR_rep IO_FP X Σ1 m a h spill ogc opc ->
cells_size spill = 248%nat -> cells_size ogc = 32%nat -> cells_size opc = 48%nat ->
ART RT Σ2 m' -> mem_inv bsegs m' -> stk bsegs m' lo S1 ->
(forall e, In e (x_live X) -> In e Lv) ->
(forall p q, In (p, q) (h_own a h) -> (h_stream_init h <> 0 -> p <> a_Bd a /\ p <> a_L a /\ p <> a_G a) -> In (p, q) Lv) ->
rt_pres_fp Lv [(F, 8%nat)] S1 [(F + 8688, F + 8688 + 408)] m m' ->
h_os_rep X m' a' h' ->
h_oy h' = h_oy h -> h_bits h' = h_bits h -> h_st h' = h_st h -> h_frame_size h' = h_frame_size h -> h_rate h' = h_rate h ->
a_Dsy a' = a_Dsy a -> a_sybytes a' = a_sybytes a -> a_Dc a' = a_Dc a -> a_S a' = a_S a -> a_LBD a' = a_LBD a ->
hpure X h' ->
hrep RT OUT_rep ERR_rep IO_FP X Σ2 m' a' h' spill ogc opc.
Proof using AF HX ERR_loc OUT_loc IO_img AF_DRV.
intros Σ1 Σ2 m m' a a' h h' spill ogc opc Lv HS HR SPS OGS OPS ART' MI' ST' XL KEEP PR OSR' EOY EBI EST EFS ERA EDsy Esyb EDc ES ELBD HP'.
destruct HR as (ART & MI & ST & PF & ERR & OUTR & SSP & SP & LSH & (je & ENH) & (ows & OUTB & LOWS) & FSZ & BITS & SY & OGC & OPC & OSR & (stb & STB)
& RATE & (wl & LOOK & LKR) & DEC & HP).
pose proof (hsep_of RT AF OUT_rep IO_FP X HX Σ1 m a h ART HS) as HSP.
pose proof (hx_arith OUT_rep IO_FP X HX) as (U336 & UT & U16 & S32 & SR & LW & LR & SHLO & FP0 & F64 & FL & FI & ESF & ESF2 & SH1 & SH2 & FSA).
unfold RT_STACK, H_STACK in LR.
pose proof HS as (EL & ND & PERM & EF & ESP & EPO0 & ECR).
pose proof (own_ne_os a h (proj2 (proj2 HSP))) as ONE.
assert (INF : In (F, 8%nat) [(F, 8%nat)]) by (left; reflexivity).
unfold HO_ENH, HO_OUT, HO_FSZ, HO_BITS, HO_OY, HO_OG, HO_OP, HO_OS, HO_STEREO, HO_RATE, HO_LOOK in *.
change (fs_size 8) with 16384 in *.

assert (FRT : forall A cs, rw_cells bsegs m A cs -> F + 32 <= A -> A + Z.of_nat (cells_size cs) <= F + 9252 ->
(A + Z.of_nat (cells_size cs) <= F + 8688 \/ F + 9096 <= A) -> rw_cells bsegs m' A cs).
{ intros A cs C H1 H2 H3. apply (htr_rw _ _ _ _ m m' PR _ _ C); [apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia|].
apply rng_out_cons; [lia|]. apply rng_out_nil. }
assert (ENH' : rw_cells bsegs m' (F + 32) [CB 56 je]) by (apply (FRT _ _ ENH); cbn [cells_size csize Nat.add]; lia).
assert (OUTB' : rw_cells bsegs m' (F + 128) (f32 ows)) by (apply (FRT _ _ OUTB); rewrite ?cells_size_f32, ?LOWS; lia).
assert (FSZ' : rw_cells bsegs m' (F + 8384) [C4 (Z_to_bv 64 (h_frame_size h))]) by (apply (FRT _ _ FSZ); cbn [cells_size csize Nat.add]; lia).
assert (OGC' : rw_cells bsegs m' (F + 8544) ogc) by (apply (FRT _ _ OGC); rewrite ?OGS; lia).
assert (OPC' : rw_cells bsegs m' (F + 8608) opc) by (apply (FRT _ _ OPC); rewrite ?OPS; lia).
assert (STB' : rw_cells bsegs m' (F + 9168) [CB 24 stb]) by (apply (FRT _ _ STB); cbn [cells_size csize Nat.add]; lia).
assert (RATE' : rw_cells bsegs m' (F + 9232) [C4 (Z_to_bv 64 (h_rate h))]) by (apply (FRT _ _ RATE); cbn [cells_size csize Nat.add]; lia).
assert (LOOK' : rw_cells bsegs m' (F + 9248) [C4 (Z_to_bv 64 wl)]) by (apply (FRT _ _ LOOK); cbn [cells_size csize Nat.add]; lia).
clear FRT ENH OUTB FSZ OGC OPC STB RATE LOOK.
assert (SP' : rw_cells bsegs m' S1 spill).
{ apply (htr_rw _ _ _ _ m m' PR _ _ SP); rewrite SPS; [apply acl_stack; lia|]. apply rng_out_cons; [lia|]. apply rng_out_nil. }
assert (LSH' : rw_cells bsegs m' sf [CB 16 HSH_P1]).
{ apply (htr_rw _ _ _ _ m m' PR _ _ LSH); cbn [cells_size csize Nat.add]; [apply (acl_fshadow _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia|].
unfold SH_HI in *. apply rng_out_cons; [lia|]. apply rng_out_nil. }

assert (OWNTR : forall p q, In (p, q) (h_own a h) -> (h_stream_init h <> 0 -> p <> a_Bd a /\ p <> a_L a /\ p <> a_G a) ->
acl_rng Lv [(F, 8%nat)] S1 p q /\ rng_out [(F + 8688, F + 8688 + 408)] p q).
{ intros p q Hin NE. split; [apply (acl_live _ _ _ _ _ _ _ (KEEP _ _ Hin NE)); lia|].
apply rng_out_cons; [apply (iv_own_frame X a h HSP _ _ _ _ _ _ Hin); lia|]. apply rng_out_nil. }
assert (NEDc : h_stream_init h <> 0 -> a_Dc a <> a_Bd a /\ a_Dc a <> a_L a /\ a_Dc a <> a_G a).
{ intros NS. split; [exact (proj1 (ONE NS _ (or_introl eq_refl)))|]. split; [exact (proj1 (ONE NS _ (or_intror (or_introl eq_refl))))|].
exact (proj1 (ONE NS _ (or_intror (or_intror eq_refl)))). }
assert (BOK : bits_ok (h_bits h)) by (destruct HP as (_ & _ & _ & _ & B & _); exact B).
assert (BITS' : bits_rep bsegs m' (F + 8400) (a_Dc a) (h_bits h)).
{ destruct (OWNTR _ _ (own_in_Dc a h) NEDc) as (D1 & D2).
apply (bits_rep_tr _ _ _ _ m m' PR _ _ _ BITS BOK); [| | exact D1| exact D2].
- apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia.
- apply rng_out_cons; [lia|]. apply rng_out_nil. }
assert (SY' : sync_rep m' (F + 8480) (a_Dsy a) (h_oy h) (a_sybytes a)).
{ apply (sync_rep_tr _ _ _ _ m m' PR _ _ _ _ SY).
- apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia.
- apply rng_out_cons; [lia|]. apply rng_out_nil.
- intros NS. apply (OWNTR _ _ (own_in_Dsy a h NS)). intros NI.
split; [exact (proj1 (proj2 (ONE NI _ (or_introl eq_refl))) NS)|].
split; [exact (proj1 (proj2 (ONE NI _ (or_intror (or_introl eq_refl)))) NS)|].
exact (proj1 (proj2 (ONE NI _ (or_intror (or_intror eq_refl)))) NS). }
assert (DEC' : h_dec_rep X m' a h).
{ apply (h_dec_rep_tr _ _ _ _ m m' PR X a h DEC). intros b Hb.
assert (NS0 : h_st h <> None) by (unfold h_dec_rep in DEC; destruct (h_st h); [discriminate| destruct DEC as (_ & E); rewrite E in Hb; destruct Hb]).
apply (OWNTR _ _ (own_in_blk a h NS0 b Hb)). intros NI.
split; [exact (proj2 (proj2 (ONE NI _ (or_introl eq_refl))) NS0 b Hb)|].
split; [exact (proj2 (proj2 (ONE NI _ (or_intror (or_introl eq_refl)))) NS0 b Hb)|].
exact (proj2 (proj2 (ONE NI _ (or_intror (or_intror eq_refl)))) NS0 b Hb). }
clear OSR DEC BITS OWNTR SY.

assert (FPH : fp_h X a h [(F + 8688, F + 8688 + 408)]) by (apply fp_h_cons; [right; right; left; lia| apply fp_h_nil]).
destruct (h_io_step RT OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img X HX Σ1 m m' a h _ _ HSP PR XL FPH (AF_DRV _ _ ART') PF ERR OUTR SSP)
as (PF' & ERR' & OUTR' & SSP').
unfold hrep. unfold HO_ENH, HO_OUT, HO_FSZ, HO_BITS, HO_OY, HO_OG, HO_OP, HO_OS, HO_STEREO, HO_RATE, HO_LOOK.
rewrite EOY, EBI, EFS, ERA, EDsy, Esyb, EDc.
split; [exact ART'|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact PF'|]. split; [exact ERR'|]. split; [exact OUTR'|]. split; [exact SSP'|].
split; [exact SP'|]. split; [exact LSH'|]. split; [exists je; exact ENH'|]. split; [exists ows; split; [exact OUTB'| exact LOWS]|].
split; [exact FSZ'|]. split; [exact BITS'|]. split; [exact SY'|]. split; [exact OGC'|]. split; [exact OPC'|].
split; [unfold HO_OS in OSR'; exact OSR'|]. split; [exists stb; exact STB'|]. split; [exact RATE'|]. split; [exists wl; split; [exact LOOK'| first [exact LKR | (let HH := fresh in intros HH; apply LKR; congruence)]]|].
split; [| exact HP'].
unfold h_dec_rep in DEC' |- *. rewrite EST, ES, ELBD, EDc. exact DEC'.
Qed.

Lemma h_os_rep_intro : forall (m : mem) a (h : hstate unit), h_stream_init h <> 0 ->
rw_cells bsegs m (F + HO_OS) (stream_cells (a_Bd a) (a_L a) (a_G a) (a_shdr a) (h_os h)) -> length (a_shdr a) = 284%nat ->
stream_arrays m (h_os h) (a_Bd a) (a_L a) (a_G a) (a_body a) (a_lws a) (a_gws a) -> os_pure (h_os h) ->
a_Bd a <> a_L a -> a_Bd a <> a_G a -> a_L a <> a_G a -> a_Bd a mod 16 = 0 -> 16384 <= os_body_storage (h_os h) -> h_os_rep X m a h.
Proof.
intros m a h NE C LH ARR (FOK & SINV & BINV & LOK & GL & BD & LV & GV & LS & BS) N1 N2 N3 BA BST.
unfold h_os_rep. destruct (Z.eqb_spec (h_stream_init h) 0) as [E0|_]; [exfalso; exact (NE E0)|].
split; [exact C|]. split; [exact LH|]. split; [exact ARR|]. split; [exact FOK|]. split; [exact SINV|]. split; [exact BINV|].
split; [exact LOK|]. split; [exact GL|]. split; [exact BD|]. split; [exact LV|]. split; [exact GV|]. split; [exact LS|].
split; [exact BS|]. split; [exact N1|]. split; [exact N2|]. split; [exact N3|]. split; [exact BA| exact BST].
Qed.

Lemma hpure_with_os : forall (h : hstate unit) (os : stream_st unit) si, hpure X h -> (si = 0 \/ si = 1) ->
os_lacing_fill os <= h_consumed X h -> os_body_fill os <= h_consumed X h ->
os_lacing_storage os <= 1568 + h_consumed X h -> os_body_storage os <= 17408 + 2 * h_consumed X h ->
h_packet_count h + (os_lacing_fill os - os_lacing_returned os) <= 162 * h_consumed X h ->
hpure X (h_with_os h os si).
Proof.
intros h os si HP SI B1 B2 B3 B4 B5. unfold hpure, h_consumed, h_pend in *.
cbn [h_with_os h_oy h_os h_bits h_st h_stream_init h_packet_count h_last_granule h_nframes h_eos h_channels h_rate h_extra_headers
h_speex_serialno h_frame_size h_granule_frame_size h_bytes_remaining].
destruct HP as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & A18 & A19 & A20 & A21 & A22 & REST).
do 16 (split; [assumption|]). split; [exact SI|]. do 5 (split; [assumption|]). repeat split; lia.
Qed.
Lemma budget_with_os : forall (h : hstate unit) og (os : stream_st unit) si, h_page_budget X h og ->
os_lacing_fill os = 0 -> os_body_fill os = 0 -> os_lacing_returned os = 0 ->
os_lacing_storage os <= Z.max 1024 (os_lacing_storage (h_os h)) -> os_body_storage os <= Z.max 16384 (os_body_storage (h_os h)) ->
h_page_budget X (h_with_os h os si) og.
Proof.
intros h og os si (cold & C0 & C1 & C2 & C3 & C4 & C5 & C6 & C7) E1 E2 E3 B1 B2. exists cold.
unfold h_consumed, h_pend in *. cbn [h_with_os h_oy h_os h_bytes_remaining h_packet_count].
rewrite E1, E2, E3. repeat split; lia.
Qed.

Lemma hrep_sinit : forall (Σ1 Σ2 : rts RT) (m m' : mem) a (h : hstate unit) spill ogc opc ser Bd L G (jb : list byte) (lws gws : list word),
hsig RT X Σ1 a h -> hrep RT OUT_rep ERR_rep IO_FP X Σ1 m a h spill ogc opc ->
cells_size spill = 248%nat -> cells_size ogc = 32%nat -> cells_size opc = 48%nat ->
h_stream_init h = 0 -> -2^31 <= ser < 2^31 ->
rt_after RT Σ2 S1 lo m m' ->
rt_pres_fp (rt_live RT Σ1) (rt_frames RT Σ1) S1 [(F + 8688, F + 8688 + 408)] m m' ->
rw_cells bsegs m' (F + 8688) (stream_cells Bd L G zero_hdr (init_os (Some tt) (Some tt) (Some tt) ser)) ->
u8arr bsegs m' Bd jb -> Z.of_nat (length jb) = 16384 ->
u32arr bsegs m' L lws -> Z.of_nat (length lws) = 1024 -> u64arr bsegs m' G gws -> Z.of_nat (length gws) = 1024 ->
rt_live RT Σ2 = (G, 8192) :: (L, 4096) :: (Bd, 16384) :: rt_live RT Σ1 -> rt_frames RT Σ2 = rt_frames RT Σ1 -> rt_sp0 RT Σ2 = rt_sp0 RT Σ1 ->
rt_credit RT Σ2 = rt_credit RT Σ1 -> rt_pois RT Σ2 = rt_pois RT Σ1 ->
stream_live RT Σ2 (init_os (Some tt) (Some tt) (Some tt) ser) Bd L G -> Bd mod 16 = 0 ->
hsig RT X Σ2 (a_set_os a Bd L G zero_hdr jb lws gws ((G, 8192) :: (L, 4096) :: (Bd, 16384) :: a_P a))
(set_stream_init h (init_os (Some tt) (Some tt) (Some tt) ser))
/\ hrep RT OUT_rep ERR_rep IO_FP X Σ2 m' (a_set_os a Bd L G zero_hdr jb lws gws ((G, 8192) :: (L, 4096) :: (Bd, 16384) :: a_P a))
(set_stream_init h (init_os (Some tt) (Some tt) (Some tt) ser)) spill ogc opc.
Proof using AF HX ERR_loc OUT_loc IO_img AF_DRV.
intros Σ1 Σ2 m m' a h spill ogc opc ser Bd L G jb lws gws HS HR SPS OGS OPS SI0 SR (ART' & MI' & WM' & ST') PR OS' UB LB UL LL UG LG
EL2 EF2 ES2 EC2 EP2 SLV BDA.
pose proof (own_pos RT OUT_rep ERR_rep IO_FP X Σ1 m a h spill ogc opc HR) as OPOS.
pose proof HR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HP).
pose proof HS as (EL & ND & PERM & EF & ESP & EPO0 & ECR).
pose proof SLV as (IB & IL & IG & NBL & NBG & NLG).
set (os1 := init_os (Some tt) (Some tt) (Some tt) ser) in *.
set (P1 := (G, 8192) :: (L, 4096) :: (Bd, 16384) :: a_P a).
set (a1 := a_set_os a Bd L G zero_hdr jb lws gws P1).
rewrite set_stream_init_with.
assert (EOWN : h_own a1 (h_with_os h os1 1) = ((match h_st h with Some _ => blocks_live (a_LBD a) | None => [] end) ++ [(a_Dc a, sb_buf_size (h_bits h))])
++ [(Bd, 16384); (L, 4096); (G, 8192)] ++ (match sy_data (h_oy h) with Some _ => [(a_Dsy a, sy_storage (h_oy h))] | None => [] end)).
{ unfold h_own. cbn [a1 a_set_os a_Dsy a_Dc a_Bd a_L a_G a_LBD h_with_os h_oy h_os h_bits h_st h_stream_init os1 init_os os_body_storage os_lacing_storage Z.eqb].
rewrite <- app_assoc. reflexivity. }
assert (EOWN0 : h_own a h = ((match h_st h with Some _ => blocks_live (a_LBD a) | None => [] end) ++ [(a_Dc a, sb_buf_size (h_bits h))])
++ (match sy_data (h_oy h) with Some _ => [(a_Dsy a, sy_storage (h_oy h))] | None => [] end)).
{ unfold h_own. rewrite SI0. cbn [Z.eqb app]. rewrite <- app_assoc. reflexivity. }
split.
- unfold hsig. cbn [a1 a_set_os a_P]. rewrite EL2, EF2, ES2, EC2, EP2, EL. fold P1.
split; [reflexivity|].
split.
{ apply (h_live_nodup RT AF Σ2 m' P1 [] (x_live X) ART'); [rewrite EL2, EL; reflexivity|].
intros [p q] Hin. cbn [snd]. destruct Hin as [E|[E|[E|Hin]]]; try (injection E as <- <-; lia).
exact (OPOS p q (Permutation_in _ PERM Hin)). }
split.
{ rewrite EOWN. unfold P1. rewrite EOWN0 in PERM.
eapply perm_trans; [do 3 apply perm_skip; exact PERM|].
lazymatch goal with |- Permutation (?x :: ?y :: ?z :: ?D ++ ?S) (?D ++ _ ++ ?S) =>
change (x :: y :: z :: D ++ S) with ([x; y; z] ++ D ++ S);
eapply perm_trans; [apply Permutation_app_swap_app|]; apply Permutation_app_head;
change ([x; y; z] ++ S) with (x :: y :: z :: S); change ([(Bd, 16384); (L, 4096); (G, 8192)] ++ S) with ((Bd, 16384) :: (L, 4096) :: (G, 8192) :: S) end.
eapply perm_trans; [apply perm_swap|]. eapply perm_trans; [apply perm_skip; apply perm_swap|]. apply perm_swap. }
split; [exact EF|]. split; [exact ESP|]. split; [exact EPO0|]. unfold h_cost in *. cbn [h_with_os h_packet_count]. exact ECR.
- apply (hrep_os_step Σ1 Σ2 m m' a a1 h (h_with_os h os1 1) spill ogc opc (rt_live RT Σ1) HS HR SPS OGS OPS ART' MI' ST').
+ intros e He. rewrite EL. apply in_or_app. right. exact He.
+ intros p q Hin _. rewrite EL. apply in_or_app. left. exact (Permutation_in _ (Permutation_sym PERM) Hin).
+ rewrite EF in PR. exact PR.
+ apply h_os_rep_intro; cbn [a1 a_set_os a_Bd a_L a_G a_shdr a_body a_lws a_gws h_with_os h_os h_stream_init].
* discriminate.
* unfold HO_OS. exact OS'.
* reflexivity.
* unfold stream_arrays. cbn [os1 init_os os_body_storage os_body os_lacing os_lacing_storage].
split; [exact UB|]. split; [exact LB|]. split; [split; [reflexivity| cbn; lia]|].
split; [exact UL|]. split; [split; [reflexivity| cbn; lia]|]. split; [exact LL|]. split; [exact UG| exact LG].
* apply init_os_pure. exact SR.
* exact NBL. * exact NBG. * exact NLG. * exact BDA. * cbn [os1 init_os os_body_storage]. lia.
+ reflexivity. + reflexivity. + reflexivity. + reflexivity. + reflexivity.
+ reflexivity. + reflexivity. + reflexivity. + reflexivity. + reflexivity.
+ pose proof HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & P1' & P2' & P3' & P4' & P5' & P6' & P7' & P8').
apply hpure_with_os; [exact HP| right; reflexivity| ..]; cbn [os1 init_os os_lacing_fill os_body_fill os_lacing_storage os_body_storage os_lacing_returned]; lia.
Qed.

Lemma hrep_reset : forall (Σ1 : rts RT) (m m1 : mem) a (h : hstate unit) spill ogc opc ser,
hsig RT X Σ1 a h -> hrep RT OUT_rep ERR_rep IO_FP X Σ1 m a h spill ogc opc ->
cells_size spill = 248%nat -> cells_size ogc = 32%nat -> cells_size opc = 48%nat ->
h_stream_init h <> 0 -> -2^31 <= ser < 2^31 ->
munch [(F + 8688, F + 8688 + 408)] m m1 -> wmono bsegs m m1 -> mem_inv bsegs m1 ->
rw_cells bsegs m1 (F + 8688) (stream_cells (a_Bd a) (a_L a) (a_G a) (a_shdr a) (snd (ogg_stream_reset_serialno (h_os h) ser))) ->
hsig RT X Σ1 a (set_ogg h (h_oy h) (snd (ogg_stream_reset_serialno (h_os h) ser)))
/\ hrep RT OUT_rep ERR_rep IO_FP X Σ1 m1 a (set_ogg h (h_oy h) (snd (ogg_stream_reset_serialno (h_os h) ser))) spill ogc opc.
Proof using AF HX ERR_loc OUT_loc IO_img AF_DRV.
intros Σ1 m m1 a h spill ogc opc ser HS HR SPS OGS OPS SI SR MU WM MI1 OS1.
pose proof HR as (ART0 & _ & ST & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & OSR & _ & _ & _ & _ & HP).
pose proof (hsep_of RT AF OUT_rep IO_FP X HX Σ1 m a h ART0 HS) as HSP.
pose proof (hx_arith OUT_rep IO_FP X HX) as (U336 & UT & U16 & S32 & SR' & LW & LR & SHLO & FP0 & F64 & FL & FI & ESF & ESF2 & SH1 & SH2 & FSA).
unfold RT_STACK, H_STACK in LR.
pose proof HS as (EL & ND & PERM & EF & ESP & EPO0 & ECR).
assert (INF : In (F, 8%nat) [(F, 8%nat)]) by (left; reflexivity).
unfold h_os_rep in OSR. destruct (Z.eqb_spec (h_stream_init h) 0) as [E0|_]; [exfalso; exact (SI E0)|].
destruct OSR as (_ & LH & (UB & LB & BP & UL & WP & LL & UG & LG) & FOK & SINV & BINV & LOK & GL & BD & LV & GV & LS & BS & NBL & NBG & NLG & BDA & BST).
destruct (reset_os_pure (h_os h) ser (conj FOK (conj SINV (conj BINV (conj LOK (conj GL (conj BD (conj LV (conj GV (conj LS BS))))))))) SR)
as (POS & ELS & EBS & ELF & EBF & ELR & ESN & EBO & ELA).
unfold bptr in *.
set (os1 := snd (ogg_stream_reset_serialno (h_os h) ser)) in *.
assert (EOWN : h_own a (set_ogg h (h_oy h) os1) = h_own a h).
{ unfold h_own. cbn [set_ogg h_oy h_os h_bits h_st h_stream_init]. rewrite ELS, EBS. reflexivity. }
assert (PR : rt_pres_fp (rt_live RT Σ1) [(F, 8%nat)] S1 [(F + 8688, F + 8688 + 408)] m m1).
{ apply (pres_fp_of_munch _ _ _ _ _ m m1 MU). intros x _ Ho. exact Ho. }
assert (ART1 : ART RT Σ1 m1).
{ apply (af_frame RT AF Σ1 m m1 S1 ART0); [rewrite ESP; pose proof (hi_lo _ _ _ HX) as (LW0 & _); unfold STACK_WIN in *; lia| | exact WM].
intros b Hb. apply MU. cbn [outside]. split; [| exact I]. intros Hin. apply Hb. rewrite EF.
exact (acl_frame (rt_live RT Σ1) [(F, 8%nat)] S1 F 8 (F + 8688) 408 INF ltac:(lia) ltac:(change (fs_size 8) with 16384; lia) _ Hin). }
assert (ST1 : stk bsegs m1 lo S1).
{ apply (stk_agree bsegs m m1 lo S1 ST); [| exact WM]. apply (agree_of_munch _ m m1 _ MU). intros x Hx. cbn [outside].
change (fs_size 8) with 16384 in FL. split; [lia| exact I]. }
split.
- unfold hsig. rewrite EOWN. unfold h_cost in *. cbn [set_ogg h_packet_count]. exact HS.
- apply (hrep_os_step Σ1 Σ1 m m1 a a h (set_ogg h (h_oy h) os1) spill ogc opc (rt_live RT Σ1) HS HR SPS OGS OPS ART1 MI1 ST1).
+ intros e He. rewrite EL. apply in_or_app. right. exact He.
+ intros p q Hin _. rewrite EL. apply in_or_app. left. exact (Permutation_in _ (Permutation_sym PERM) Hin).
+ exact PR.
+ destruct (own_in_os a h SI) as (IB & IL & IG).
assert (OWNTR : forall p q, In (p, q) (h_own a h) -> acl_rng (rt_live RT Σ1) [(F, 8%nat)] S1 p q /\ rng_out [(F + 8688, F + 8688 + 408)] p q).
{ assert (INL : forall e, In e (h_own a h) -> In e (rt_live RT Σ1)).
{ intros e He. rewrite EL. apply in_or_app. left. exact (Permutation_in e (Permutation_sym PERM) He). }
intros p q Hin. split; [apply (acl_live _ _ _ _ _ _ _ (INL _ Hin)); lia|].
apply rng_out_cons; [apply (iv_own_frame X a h HSP _ _ _ _ _ _ Hin); change (fs_size 8) with 16384 in *; lia|]. apply rng_out_nil. }
destruct (OWNTR _ _ IB) as (B1 & B2). destruct (OWNTR _ _ IL) as (L1 & L2). destruct (OWNTR _ _ IG) as (G1 & G2).
apply h_os_rep_intro; cbn [set_ogg h_os h_stream_init].
* exact SI.
* unfold HO_OS. exact OS1.
* exact LH.
* unfold stream_arrays, bptr. rewrite ELS, EBS.
split; [apply (htr_u8 _ _ _ _ m m1 PR _ _ UB); rewrite LB; assumption|]. split; [exact LB|].
split; [unfold body_pre; rewrite EBO; cbn [length firstn]; split; [reflexivity| lia]|].
split; [apply (htr_u32 _ _ _ _ m m1 PR _ _ UL); rewrite LL; assumption|].
split; [unfold wpre; rewrite ELA; cbn [length firstn map]; split; [reflexivity| lia]|].
split; [exact LL|]. split; [apply (htr_u64 _ _ _ _ m m1 PR _ _ UG); rewrite LG; assumption| exact LG].
* exact POS.
* exact NBL. * exact NBG. * exact NLG. * exact BDA. * rewrite EBS. exact BST.
+ reflexivity. + reflexivity. + reflexivity. + reflexivity. + reflexivity.
+ reflexivity. + reflexivity. + reflexivity. + reflexivity. + reflexivity.
+ pose proof HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & P17 & _ & _ & _ & P1' & P2' & P3' & P4' & P5' & P6' & P7' & P8').
rewrite set_ogg_with. apply hpure_with_os; [exact HP| exact P17| ..]; rewrite ?ELF, ?EBF, ?ELR, ?ELS, ?EBS; lia.
Qed.

Lemma xlive_ne_own : forall (Σ1 : rts RT) (m : mem) a (h : hstate unit) spill ogc opc, hsig RT X Σ1 a h ->
hrep RT OUT_rep ERR_rep IO_FP X Σ1 m a h spill ogc opc ->
forall p q, In (p, q) (h_own a h) -> forall e, In e (x_live X) -> fst e <> p.
Proof using AF HX.
intros Σ1 m a h spill ogc opc HS HR p q Hin [p' q'] He E. cbn [fst] in E. subst p'.
pose proof HR as (ART0 & _).
pose proof (hsep_of RT AF OUT_rep IO_FP X HX Σ1 m a h ART0 HS) as HSP.
pose proof (own_pos RT OUT_rep ERR_rep IO_FP X Σ1 m a h spill ogc opc HR p q Hin) as P1.
pose proof (proj1 (hi_live _ _ _ HX) _ _ He) as P2.
destruct (proj1 HSP p q Hin) as (_ & _ & _ & _ & _ & SEP). destruct (SEP _ _ He); lia.
Qed.

Lemma hpure_pagein : forall (h : hstate unit) og (hs : list byte) (body : list Z),
hpure X h -> h_page_budget X h og -> os_pure (h_os h) ->
os_lacing_fill (h_os h) <= os_lacing_storage (h_os h) -> os_body_fill (h_os h) <= os_body_storage (h_os h) ->
length hs = (27 + Z.to_nat (znth (ubytes hs) 26))%nat -> Z.of_nat (length hs) = pg_header_len og -> zlength body = pg_body_len og ->
bytes_ok body -> zsum (lacing_of (ubytes hs)) = zlength body ->
os_pure (snd (pagein_res (h_os h) (ubytes hs) body)) /\ hpure X (set_ogg h (h_oy h) (snd (pagein_res (h_os h) (ubytes hs) body))).
Proof using HX.
intros h og hs body HP (cold & C0 & C1 & C2 & C3 & C4 & C5 & C6 & C7) POS LFS BFS LENH HLEN BLEN BOK ZSEQ.
pose proof (hi_pay _ _ _ HX) as (_ & SZ & _). unfold MAX_FUZZ_SIZE in SZ.
pose proof HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & P17 & _ & BR & _ & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
unfold h_consumed, h_pend in *.
assert (H26 : 0 <= znth (ubytes hs) 26 < 256) by (apply znth_ubytes_range).
pose proof (zlength_nonneg body) as ZB.
destruct (pagein_res_pure (h_os h) hs body POS LENH BOK ZSEQ LFS BFS ltac:(unfold bptr; lia) ltac:(unfold bptr; lia))
as (POS' & B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9).
unfold bptr in *.
set (os' := snd (pagein_res (h_os h) (ubytes hs) body)) in *.
split; [exact POS'|].
pose proof POS' as (_ & (R0 & _) & _).
rewrite set_ogg_with. apply hpure_with_os; [exact HP| exact P17| ..]; unfold h_consumed, h_pend, bptr in *; lia.
Qed.

Lemma nodup_fst_remove_mid : forall (A B : list (Z * Z)) x, List.NoDup (map fst (A ++ x :: B)) -> List.NoDup (map fst (A ++ B)).
Proof. intros A B x ND. rewrite map_app in ND |- *. cbn [map] in ND. exact (NoDup_remove_1 _ _ _ ND). Qed.

Lemma hrep_pagein : forall (Σ1 Σ2 : rts RT) (m m' : mem) a (h : hstate unit) spill ogc opc (hs : list byte) (body : list Z)
Bd' L' Gv' (body' : list byte) (lws' gws' : list word),
hsig RT X Σ1 a h -> hrep RT OUT_rep ERR_rep IO_FP X Σ1 m a h spill ogc opc ->
cells_size spill = 248%nat -> cells_size ogc = 32%nat -> cells_size opc = 48%nat ->
h_stream_init h <> 0 ->
rt_after_f RT Σ2 S1 lo m m' ->
rt_pres_fp (pgi_rest (a_Bd a) (a_L a) (a_G a) (rt_live RT Σ1)) (rt_frames RT Σ1) S1 [(F + 8688, F + 8688 + 408)] m m' ->
rw_cells bsegs m' (F + 8688) (stream_cells Bd' L' Gv' (a_shdr a) (snd (pagein_res (h_os h) (ubytes hs) body))) ->
stream_arrays m' (snd (pagein_res (h_os h) (ubytes hs) body)) Bd' L' Gv' body' lws' gws' ->
stream_live RT Σ2 (snd (pagein_res (h_os h) (ubytes hs) body)) Bd' L' Gv' ->
rt_live RT Σ2 = pagein_live (rt_live RT Σ1) (h_os h) (ubytes hs) body (a_Bd a) (a_L a) (a_G a) Bd' L' Gv' ->
pagein_same (h_os h) (ubytes hs) body (a_Bd a) (a_L a) (a_G a) Bd' L' Gv' ->
rt_frames RT Σ2 = rt_frames RT Σ1 -> rt_sp0 RT Σ2 = rt_sp0 RT Σ1 -> rt_credit RT Σ2 = rt_credit RT Σ1 -> rt_pois RT Σ2 = rt_pois RT Σ1 ->
os_pure (snd (pagein_res (h_os h) (ubytes hs) body)) ->
hpure X (set_ogg h (h_oy h) (snd (pagein_res (h_os h) (ubytes hs) body))) ->
(pgi_ok (h_os h) (ubytes hs) = true ->
((zlength body - snd (pagein_skip (pgi_os3 (h_os h) (ubytes hs)) (ubytes hs)) =? 0)
|| (os_body_fill (pgi_os3 (h_os h) (ubytes hs)) <? os_body_storage (pgi_os3 (h_os h) (ubytes hs)) - (zlength body - snd (pagein_skip (pgi_os3 (h_os h) (ubytes hs)) (ubytes hs))))) = true) ->
hsig RT X Σ2 (a_set_os a Bd' L' Gv' (a_shdr a) body' lws' gws' (pagein_live (a_P a) (h_os h) (ubytes hs) body (a_Bd a) (a_L a) (a_G a) Bd' L' Gv'))
(set_ogg h (h_oy h) (snd (pagein_res (h_os h) (ubytes hs) body)))
/\ hrep RT OUT_rep ERR_rep IO_FP X Σ2 m' (a_set_os a Bd' L' Gv' (a_shdr a) body' lws' gws' (pagein_live (a_P a) (h_os h) (ubytes hs) body (a_Bd a) (a_L a) (a_G a) Bd' L' Gv'))
(set_ogg h (h_oy h) (snd (pagein_res (h_os h) (ubytes hs) body))) spill ogc opc.
Proof using AF HX ERR_loc OUT_loc IO_img AF_DRV.
intros Σ1 Σ2 m m' a h spill ogc opc hs body Bd' L' Gv' body' lws' gws' HS HR SPS OGS OPS SI (ART' & MI' & ST') PR OS' ARR' SLV' EL2 SAME
EF2 ES2 EC2 EP2 POS' HP' NOREA.
pose proof (own_pos RT OUT_rep ERR_rep IO_FP X Σ1 m a h spill ogc opc HR) as OPOS.
pose proof (xlive_ne_own Σ1 m a h spill ogc opc HS HR) as XNE.
pose proof HR as (ART0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & OSR & _).
pose proof (hsep_of RT AF OUT_rep IO_FP X HX Σ1 m a h ART0 HS) as HSP.
pose proof HS as (EL & ND & PERM & EF & ESP & EPO0 & ECR).
pose proof SLV' as (IB' & IL' & IG' & NBL' & NBG' & NLG').
unfold h_os_rep in OSR. destruct (Z.eqb_spec (h_stream_init h) 0) as [E0|_]; [exfalso; exact (SI E0)|].
destruct OSR as (_ & LH & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NBL & NBG & NLG & BDA & BST).
destruct (own_in_os a h SI) as (IB & IL & IG).
pose proof (pagein_res_store (h_os h) (ubytes hs) body) as (ST1 & ST2 & ST3 & ST4 & ST5). cbv zeta in ST1, ST2, ST3, ST4, ST5.
pose proof SAME as (SA1 & SA2 & SA3).
pose proof (pgi_os3_body (h_os h) (ubytes hs)) as (_ & EB3).
pose proof (pagein_returned_fields (h_os h)) as (_ & _ & _ & EL1 & _).
unfold bptr in *.
set (os := h_os h) in *. set (os' := @snd Z (stream_st unit) (pagein_res os (ubytes hs) body)) in *.
set (P' := pagein_live (a_P a) os (ubytes hs) body (a_Bd a) (a_L a) (a_G a) Bd' L' Gv').
set (a' := a_set_os a Bd' L' Gv' (a_shdr a) body' lws' gws' P').
set (core := (match h_st h with Some _ => blocks_live (a_LBD a) | None => [] end) ++ [(a_Dc a, sb_buf_size (h_bits h))]).
set (sync := match sy_data (h_oy h) with Some _ => [(a_Dsy a, sy_storage (h_oy h))] | None => [] end).
assert (EOWN0 : h_own a h = core ++ [(a_Bd a, os_body_storage os); (a_L a, 4 * os_lacing_storage os); (a_G a, 8 * os_lacing_storage os)] ++ sync).
{ unfold h_own, core, sync. fold os. destruct (Z.eqb_spec (h_stream_init h) 0) as [E0|_]; [exfalso; exact (SI E0)|]. rewrite <- app_assoc. reflexivity. }
assert (EOWN1 : h_own a' (set_ogg h (h_oy h) os') = core ++ [(Bd', os_body_storage os'); (L', 4 * os_lacing_storage os'); (Gv', 8 * os_lacing_storage os')] ++ sync).
{ unfold h_own, core, sync. cbn [a' a_set_os a_Dsy a_Dc a_Bd a_L a_G a_LBD set_ogg h_oy h_os h_bits h_st h_stream_init].
destruct (Z.eqb_spec (h_stream_init h) 0) as [E0|_]; [exfalso; exact (SI E0)|]. rewrite <- app_assoc. reflexivity. }
pose proof (proj2 (proj2 HSP)) as NDO. rewrite EOWN0 in NDO, PERM.
assert (ELP : rt_live RT Σ2 = P' ++ x_live X).
{ rewrite EL2, EL. apply pagein_live_app. intros e He.
split; [exact (XNE _ _ IB e He)|]. split; [exact (XNE _ _ IL e He)| exact (XNE _ _ IG e He)]. }
assert (POSB' : 0 < os_body_storage os') by (destruct POS' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & X1); exact X1).
assert (POSL' : 0 < os_lacing_storage os') by (destruct POS' as (_ & _ & _ & _ & _ & _ & _ & _ & X1 & _); exact X1).

assert (PERM' : Permutation P' (core ++ [(Bd', os_body_storage os'); (L', 4 * os_lacing_storage os'); (Gv', 8 * os_lacing_storage os')] ++ sync)).
{ unfold P', pagein_live. cbv zeta. unfold bptr.
destruct (pgi_ok os (ubytes hs)) eqn:OK.
2:{ destruct (SA1 eq_refl) as (-> & -> & ->). destruct (ST1 eq_refl) as (-> & ->). exact PERM. }
lazymatch goal with |- Permutation (if _ then (if ?c then _ else _) else _) _ => destruct c eqn:C1 end;
lazymatch goal with |- Permutation (if ?c then _ else _) _ => destruct c eqn:C2 end.
-
destruct (SA2 eq_refl eq_refl) as (-> & ->). rewrite (SA3 eq_refl eq_refl), (ST2 eq_refl eq_refl), (ST4 eq_refl eq_refl). exact PERM.
-
destruct (SA2 eq_refl eq_refl) as (-> & ->). rewrite (ST2 eq_refl eq_refl), (ST5 eq_refl eq_refl), EB3.
pose proof (perm_live_remove_mid (a_Bd a) _ (a_P a) core ([(a_L a, 4 * os_lacing_storage os); (a_G a, 8 * os_lacing_storage os)] ++ sync) PERM NDO) as PR1.
eapply perm_trans; [apply perm_skip; exact PR1|]. apply Permutation_middle.
-
rewrite (SA3 eq_refl eq_refl), (ST3 eq_refl eq_refl), (ST4 eq_refl eq_refl), EL1.
assert (E1 : core ++ [(a_Bd a, os_body_storage os); (a_L a, 4 * os_lacing_storage os); (a_G a, 8 * os_lacing_storage os)] ++ sync
= (core ++ [(a_Bd a, os_body_storage os)]) ++ (a_L a, 4 * os_lacing_storage os) :: (a_G a, 8 * os_lacing_storage os) :: sync)
by (rewrite <- app_assoc; reflexivity).
rewrite E1 in PERM, NDO.
pose proof (perm_live_remove_mid (a_L a) _ (a_P a) _ _ PERM NDO) as PR1.
pose proof (nodup_fst_remove_mid _ _ _ NDO) as NDO1.
pose proof (perm_live_remove_mid (a_G a) _ _ _ _ PR1 NDO1) as PR2.
eapply perm_trans; [apply perm_skip; apply perm_skip; exact PR2|].
rewrite <- app_assoc. cbn [app].
eapply perm_trans; [apply perm_skip; apply Permutation_middle|].
eapply perm_trans; [apply Permutation_middle|]. apply Permutation_app_head.
eapply perm_trans; [apply perm_swap|]. eapply perm_trans; [apply perm_skip; apply perm_swap|]. apply perm_swap.
-
rewrite (ST3 eq_refl eq_refl), (ST5 eq_refl eq_refl), EL1, EB3.

assert (NLB : L' <> a_Bd a /\ Gv' <> a_Bd a).
{ assert (INP : forall e, In e (rt_live RT Σ2) -> fst e = a_Bd a -> e = (Bd', os_body_storage os + (zlength body - snd (pagein_skip (pgi_os3 os (ubytes hs)) (ubytes hs))) + 1024)).
{ intros e He Ee. rewrite EL2 in He. unfold pagein_live in He. unfold bptr in He. rewrite OK in He. cbv zeta in He. rewrite C1, C2, EB3 in He.
destruct He as [He|He]; [symmetry; exact He|].
apply X10r.live_remove_In in He as (_ & NE). exfalso. exact (NE Ee). }
split; intros E.
- pose proof (INP _ IL' E) as E2. injection E2 as E2 _. exact (NBL' (eq_sym E2)).
- pose proof (INP _ IG' E) as E2. injection E2 as E2 _. exact (NBG' (eq_sym E2)). }
rewrite !live_remove_cons. cbn [fst].
replace (Gv' =? a_Bd a) with false by (symmetry; apply Z.eqb_neq; exact (proj2 NLB)).
replace (L' =? a_Bd a) with false by (symmetry; apply Z.eqb_neq; exact (proj1 NLB)).
assert (E1 : core ++ [(a_Bd a, os_body_storage os); (a_L a, 4 * os_lacing_storage os); (a_G a, 8 * os_lacing_storage os)] ++ sync
= (core ++ [(a_Bd a, os_body_storage os)]) ++ (a_L a, 4 * os_lacing_storage os) :: (a_G a, 8 * os_lacing_storage os) :: sync)
by (rewrite <- app_assoc; reflexivity).
rewrite E1 in PERM, NDO.
pose proof (perm_live_remove_mid (a_L a) _ (a_P a) _ _ PERM NDO) as PR1.
pose proof (nodup_fst_remove_mid _ _ _ NDO) as NDO1.
pose proof (perm_live_remove_mid (a_G a) _ _ _ _ PR1 NDO1) as PR2.
pose proof (nodup_fst_remove_mid _ _ _ NDO1) as NDO2.
rewrite <- app_assoc in PR2, NDO2. cbn [app] in PR2, NDO2.
pose proof (perm_live_remove_mid (a_Bd a) _ _ _ _ PR2 NDO2) as PR3.
cbv iota.
eapply perm_trans; [do 3 apply perm_skip; exact PR3|]. cbn [app].
eapply perm_trans; [do 2 apply perm_skip; apply Permutation_middle|].
eapply perm_trans; [apply perm_skip; apply Permutation_middle|].
eapply perm_trans; [apply Permutation_middle|]. apply Permutation_app_head.
apply perm_skip. apply perm_swap. }
split.
- unfold hsig. cbn [a' a_set_os a_P]. rewrite EF2, ES2, EC2, EP2, EOWN1.
split; [exact ELP|].
split.
{ apply (h_live_nodup RT AF Σ2 m' P' [] (x_live X) ART'); [exact ELP|].
intros [p q] Hin. pose proof (Permutation_in _ PERM' Hin) as Hin'.
apply in_app_or in Hin' as [Hin'|Hin']; [apply (OPOS p q); rewrite EOWN0; apply in_or_app; left; exact Hin'|].
apply in_app_or in Hin' as [Hin'|Hin']; [destruct Hin' as [E|[E|[E|[]]]]; injection E as <- <-; cbn [snd]; lia|].
apply (OPOS p q). rewrite EOWN0. apply in_or_app. right. apply in_or_app. right. exact Hin'. }
split; [exact PERM'|].
split; [exact EF|]. split; [exact ESP|]. split; [exact EPO0|]. unfold h_cost in *. cbn [set_ogg h_packet_count]. exact ECR.
- apply (hrep_os_step Σ1 Σ2 m m' a a' h (set_ogg h (h_oy h) os') spill ogc opc (pgi_rest (a_Bd a) (a_L a) (a_G a) (rt_live RT Σ1)) HS HR SPS OGS OPS ART' MI' ST').
+ intros e He. apply pgi_rest_In. split; [rewrite EL; apply in_or_app; right; exact He|].
split; [exact (XNE _ _ IB e He)|]. split; [exact (XNE _ _ IL e He)| exact (XNE _ _ IG e He)].
+ intros p q Hin NE. apply pgi_rest_In. destruct (NE SI) as (N1 & N2 & N3).
split; [rewrite EL; apply in_or_app; left; rewrite EOWN0 in Hin; exact (Permutation_in _ (Permutation_sym PERM) Hin)|]. cbn [fst]. auto.
+ rewrite EF in PR. exact PR.
+ apply h_os_rep_intro; cbn [a' a_set_os a_Bd a_L a_G a_shdr a_body a_lws a_gws set_ogg h_os h_stream_init].
* exact SI. * unfold HO_OS. exact OS'. * exact LH. * exact ARR'. * exact POS'.
* exact NBL'. * exact NBG'. * exact NLG'.
*
destruct (pgi_ok os (ubytes hs)) eqn:OK; [rewrite (SA3 eq_refl (NOREA eq_refl)); exact BDA| destruct (SA1 eq_refl) as (-> & _); exact BDA].
* destruct (pgi_ok os (ubytes hs)) eqn:OK; [rewrite (ST4 eq_refl (NOREA eq_refl)); exact BST| destruct (ST1 eq_refl) as (_ & ->); exact BST].
+ reflexivity. + reflexivity. + reflexivity. + reflexivity. + reflexivity.
+ reflexivity. + reflexivity. + reflexivity. + reflexivity. + reflexivity.
+ exact HP'.
Qed.

End PStep.

Lemma sum_low_nonneg : forall l, 0 <= sum_low l.
Proof. induction l as [|v l IH]; cbn [sum_low]; [lia|]. assert (0 <= Z.land v 255) by (apply Z.land_nonneg; right; lia). lia. Qed.
Lemma fill_returned_le : forall (os : stream_st bptr), 0 <= os_body_returned os -> os_body_fill (pagein_returned os) <= os_body_fill os.
Proof.
intros os BR. unfold pagein_returned. cbv zeta.
destruct (negb (os_body_returned os =? 0)); destruct (negb (os_lacing_returned _ =? 0)); cbn [set_body set_lacing os_body_fill os_lacing_returned]; lia.
Qed.
Lemma fill_expand_eq : forall (os : stream_st bptr) n, os_body_fill (X10g.lacing_expand_res os n) = os_body_fill os.
Proof. intros os n. unfold X10g.lacing_expand_res. destruct (_ <? _); reflexivity. Qed.
Lemma fill_unroll_le : forall (os : stream_st bptr) p, os_body_fill (pagein_unroll os p) <= os_body_fill os.
Proof.
intros os p. unfold pagein_unroll. cbv zeta.
pose proof (sum_low_nonneg (zslice (os_lacing_packet os) (os_lacing_fill os - os_lacing_packet os) (os_lacing os))) as SL.
destruct (negb (p =? os_pageno os)); [| lia]. destruct (negb (_ =? -1)); cbn [set_body set_lacing os_body_fill]; lia.
Qed.
Lemma pgi_os3_fill_le : forall (os : stream_st bptr) hdr, 0 <= os_body_returned os -> os_body_fill (pgi_os3 os hdr) <= os_body_fill os.
Proof.
intros os hdr BR. unfold pgi_os3, pgi_os2.
pose proof (fill_unroll_le (X10g.lacing_expand_res (pagein_returned os) (znth hdr 26 + 1)) (ogg_page_pageno hdr)) as U.
rewrite fill_expand_eq in U. pose proof (fill_returned_le os BR). lia.
Qed.

Lemma pagein_body_stays : forall (os : stream_st bptr) (hs : list byte) (body : list Z),
os_pure os -> os_body_fill os + zlength body < os_body_storage os ->
((zlength body - snd (pagein_skip (pgi_os3 os (ubytes hs)) (ubytes hs)) =? 0)
|| (os_body_fill (pgi_os3 os (ubytes hs)) <? os_body_storage (pgi_os3 os (ubytes hs)) - (zlength body - snd (pagein_skip (pgi_os3 os (ubytes hs)) (ubytes hs))))) = true.
Proof.
intros os hs body POS LT.
destruct POS as ((_ & _ & BR & _) & _).
assert (HBOK : bytes_ok (lacing_of (ubytes hs))) by (apply bytes_ok_zslice; apply ubytes_ok).
destruct (pagein_skip (pgi_os3 os (ubytes hs)) (ubytes hs)) as [[bos segptr] skipped] eqn:SK.
pose proof (pagein_skip_le _ _ _ _ _ HBOK SK) as (SK0 & _). cbn [snd].
pose proof (pgi_os3_fill_le os (ubytes hs) BR) as FL.
pose proof (pgi_os3_body os (ubytes hs)) as (_ & EST).
apply orb_true_iff. right. apply Z.ltb_lt. rewrite EST. lia.
Qed.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation mem := (word -> option byte).

Definition h_with_os (h : hstate unit) (os : stream_st unit) (si : Z) : hstate unit :=
mkH (h_oy h) os (h_bits h) (h_st h) si (h_packet_count h) (h_last_granule h) (h_skip_samples h)
(h_nframes h) (h_eos h) (h_channels h) (h_rate h) (h_extra_headers h) (h_speex_serialno h)
(h_frame_size h) (h_granule_frame_size h) (h_bytes_remaining h).
Lemma set_stream_init_with : forall h os, set_stream_init h os = h_with_os h os 1.
Proof. reflexivity. Qed.
Lemma set_ogg_with : forall h os, set_ogg h (h_oy h) os = h_with_os h os (h_stream_init h).
Proof. reflexivity. Qed.

Definition a_set_os (a : haux) (Bd L G : Z) (shdr body : list byte) (lws gws : list word) (P : list (Z * Z)) : haux :=
HA (a_Dsy a) (a_sybytes a) Bd L G shdr body lws gws (a_Dc a) (a_S a) (a_LBD a) P.

Lemma own_ne_os : forall a (h : hstate unit), List.NoDup (map fst (h_own a h)) -> h_stream_init h <> 0 ->
forall p, p = a_Bd a \/ p = a_L a \/ p = a_G a ->
a_Dc a <> p /\ (sy_data (h_oy h) <> None -> a_Dsy a <> p) /\ (h_st h <> None -> forall b, In b (a_LBD a) -> blk_addr b <> p).
Proof.
intros a h ND NE p Hp. unfold h_own in ND. replace (h_stream_init h =? 0) with false in ND by (symmetry; apply Z.eqb_neq; exact NE).
rewrite !map_app in ND. cbn [map fst app] in ND.
split; [| split].
- apply NoDup_app_remove_l in ND. apply NoDup_cons_iff in ND as (N1 & _). intros E. apply N1. rewrite E.
destruct Hp as [->|[->| ->]]; [left| right; left| right; right; left]; reflexivity.
- intros NS. destruct (sy_data (h_oy h)) as [q|]; [| congruence]. cbn [map fst] in ND.
apply NoDup_app_remove_l in ND. apply NoDup_cons_iff in ND as (_ & ND).
apply NoDup_cons_iff in ND as (B1 & ND). apply NoDup_cons_iff in ND as (B2 & ND). apply NoDup_cons_iff in ND as (B3 & _).
intros E. destruct Hp as [->|[->| ->]].
+ apply B1. rewrite <- E. right; right; left; reflexivity.
+ apply B2. rewrite <- E. right; left; reflexivity.
+ apply B3. rewrite <- E. left; reflexivity.
- intros NS b Hb E. destruct (h_st h) as [d|]; [| congruence].
apply (nodup_app_disj _ _ (blk_addr b) ND); [unfold blocks_live; rewrite map_map; apply in_map_iff; exists b; split; [reflexivity| exact Hb]|].
rewrite E. destruct Hp as [->|[->| ->]]; [right; left| right; right; left| right; right; right; left]; reflexivity.
Qed.

Lemma live_remove_mid : forall p n (A B : list (Z * Z)), List.NoDup (map fst (A ++ (p, n) :: B)) -> live_remove p (A ++ (p, n) :: B) = A ++ B.
Proof.
intros p n A B ND. rewrite map_app in ND. cbn [map fst] in ND.
rewrite live_remove_app, live_remove_cons. cbn [fst]. rewrite Z.eqb_refl.
rewrite (live_remove_none p A), (live_remove_none p B); [reflexivity| |].
- intros e He E. apply NoDup_app_remove_l in ND. apply NoDup_cons_iff in ND as (NI & _). apply NI. rewrite <- E. apply in_map. exact He.
- intros e He E. apply (nodup_app_disj _ _ p ND); [rewrite <- E; apply in_map; exact He| left; reflexivity].
Qed.
Lemma perm_live_remove_mid : forall p n (P A B : list (Z * Z)), Permutation P (A ++ (p, n) :: B) -> List.NoDup (map fst (A ++ (p, n) :: B)) ->
Permutation (live_remove p P) (A ++ B).
Proof. intros p n P A B PERM ND. rewrite <- (live_remove_mid p n A B ND). apply perm_live_remove. exact PERM. Qed.

Lemma pagein_live_app : forall l1 l2 os hdr body Bd L Gv Bd' L' Gv',
(forall e, In e l2 -> fst e <> Bd /\ fst e <> L /\ fst e <> Gv) ->
pagein_live (l1 ++ l2) os hdr body Bd L Gv Bd' L' Gv' = pagein_live l1 os hdr body Bd L Gv Bd' L' Gv' ++ l2.
Proof.
intros l1 l2 os hdr body Bd L Gv Bd' L' Gv' H2.
assert (N1 : live_remove Bd l2 = l2) by (apply live_remove_none; intros e He; exact (proj1 (H2 e He))).
assert (N2 : live_remove L l2 = l2) by (apply live_remove_none; intros e He; exact (proj1 (proj2 (H2 e He)))).
assert (N3 : live_remove Gv l2 = l2) by (apply live_remove_none; intros e He; exact (proj2 (proj2 (H2 e He)))).
unfold pagein_live. destruct (pgi_ok os hdr); [| reflexivity]. cbv zeta.
destruct (os_lacing_fill (pagein_returned os) <? os_lacing_storage (pagein_returned os) - (znth hdr 26 + 1));
destruct ((zlength body - snd (pagein_skip (pgi_os3 os hdr) hdr) =? 0)
|| (os_body_fill (pgi_os3 os hdr) <? os_body_storage (pgi_os3 os hdr) - (zlength body - snd (pagein_skip (pgi_os3 os hdr) hdr))));
try reflexivity;
rewrite ?live_remove_app, ?N1, ?N2, ?N3; rewrite ?app_comm_cons; rewrite ?live_remove_app, ?N1, ?N2, ?N3; rewrite ?app_comm_cons; reflexivity.
Qed.

Section PStep.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable OUT_rep : X1s9.stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable IO_FP : list (Z * Z).
Hypothesis ERR_loc : fp_local IO_FP ERR_rep.
Hypothesis OUT_loc : forall so, fp_local IO_FP (OUT_rep so).
Hypothesis IO_img : forall y, in_ranges IO_FP y -> client_static y.
Hypothesis AF_DRV : forall Σ m, ART RT Σ m -> drv_consts m.
Variable X : hinv.
Hypothesis HX : hinv_ok OUT_rep IO_FP X.
Local Notation S1 := (x_S1 X). Local Notation lo := (x_lo X). Local Notation F := (x_F X). Local Notation sf := (x_sf X).

Lemma hrep_os_step : forall (Σ1 Σ2 : rts RT) (m m' : mem) a a' (h h' : hstate unit) spill ogc opc (Lv : list (Z * Z)),
hsig RT X Σ1 a h -> hrep RT OUT_rep ERR_rep IO_FP X Σ1 m a h spill ogc opc ->
cells_size spill = 216%nat -> cells_size ogc = 32%nat -> cells_size opc = 48%nat ->
ART RT Σ2 m' -> mem_inv asegs m' -> stk asegs m' lo S1 ->
(forall e, In e (x_live X) -> In e Lv) ->
(forall p q, In (p, q) (h_own a h) -> (h_stream_init h <> 0 -> p <> a_Bd a /\ p <> a_L a /\ p <> a_G a) -> In (p, q) Lv) ->
rt_pres_fp Lv [(F, 8%nat)] S1 [(F + 8688, F + 8688 + 408)] m m' ->
h_os_rep X m' a' h' ->
h_oy h' = h_oy h -> h_bits h' = h_bits h -> h_st h' = h_st h -> h_frame_size h' = h_frame_size h -> h_rate h' = h_rate h ->
a_Dsy a' = a_Dsy a -> a_sybytes a' = a_sybytes a -> a_Dc a' = a_Dc a -> a_S a' = a_S a -> a_LBD a' = a_LBD a ->
hpure X h' ->
hrep RT OUT_rep ERR_rep IO_FP X Σ2 m' a' h' spill ogc opc.
Proof using AF HX ERR_loc OUT_loc IO_img AF_DRV.
intros Σ1 Σ2 m m' a a' h h' spill ogc opc Lv HS HR SPS OGS OPS ART' MI' ST' XL KEEP PR OSR' EOY EBI EST EFS ERA EDsy Esyb EDc ES ELBD HP'.
destruct HR as (ART & MI & ST & PF & ERR & OUTR & SSP & SP & LSH & (je & ENH) & (ows & OUTB & LOWS) & FSZ & BITS & SY & OGC & OPC & OSR & (stb & STB)
& RATE & (wl & LOOK) & DEC & HP).
pose proof (hsep_of RT AF OUT_rep IO_FP X HX Σ1 m a h ART HS) as HSP.
pose proof (hx_arith OUT_rep IO_FP X HX) as (U336 & UT & U16 & S32 & SR & LW & LR & SHLO & FP0 & F64 & FL & FI & ESF & ESF2 & SH1 & SH2 & FSA).
unfold RT_STACK, H_STACK in LR.
pose proof HS as (EL & ND & PERM & EF & ESP & EPO0 & ECR).
pose proof (own_ne_os a h (proj2 (proj2 HSP))) as ONE.
assert (INF : In (F, 8%nat) [(F, 8%nat)]) by (left; reflexivity).
unfold HO_ENH, HO_OUT, HO_FSZ, HO_BITS, HO_OY, HO_OG, HO_OP, HO_OS, HO_STEREO, HO_RATE, HO_LOOK in *.
change (fs_size 8) with 16384 in *.

assert (FRT : forall A cs, rw_cells asegs m A cs -> F + 32 <= A -> A + Z.of_nat (cells_size cs) <= F + 9252 ->
(A + Z.of_nat (cells_size cs) <= F + 8688 \/ F + 9096 <= A) -> rw_cells asegs m' A cs).
{ intros A cs C H1 H2 H3. apply (htr_rw _ _ _ _ m m' PR _ _ C); [apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia|].
apply rng_out_cons; [lia|]. apply rng_out_nil. }
assert (ENH' : rw_cells asegs m' (F + 32) [CB 56 je]) by (apply (FRT _ _ ENH); cbn [cells_size csize Nat.add]; lia).
assert (OUTB' : rw_cells asegs m' (F + 128) (f32 ows)) by (apply (FRT _ _ OUTB); rewrite ?cells_size_f32, ?LOWS; lia).
assert (FSZ' : rw_cells asegs m' (F + 8384) [C4 (Z_to_bv 64 (h_frame_size h))]) by (apply (FRT _ _ FSZ); cbn [cells_size csize Nat.add]; lia).
assert (OGC' : rw_cells asegs m' (F + 8544) ogc) by (apply (FRT _ _ OGC); rewrite ?OGS; lia).
assert (OPC' : rw_cells asegs m' (F + 8608) opc) by (apply (FRT _ _ OPC); rewrite ?OPS; lia).
assert (STB' : rw_cells asegs m' (F + 9168) [CB 24 stb]) by (apply (FRT _ _ STB); cbn [cells_size csize Nat.add]; lia).
assert (RATE' : rw_cells asegs m' (F + 9232) [C4 (Z_to_bv 64 (h_rate h))]) by (apply (FRT _ _ RATE); cbn [cells_size csize Nat.add]; lia).
assert (LOOK' : rw_cells asegs m' (F + 9248) [C4 wl]) by (apply (FRT _ _ LOOK); cbn [cells_size csize Nat.add]; lia).
clear FRT ENH OUTB FSZ OGC OPC STB RATE LOOK.
assert (SP' : rw_cells asegs m' S1 spill).
{ apply (htr_rw _ _ _ _ m m' PR _ _ SP); rewrite SPS; [apply acl_stack; lia|]. apply rng_out_cons; [lia|]. apply rng_out_nil. }
assert (LSH' : rw_cells asegs m' sf [CB 16 HSH_P1]).
{ apply (htr_rw _ _ _ _ m m' PR _ _ LSH); cbn [cells_size csize Nat.add]; [apply (acl_fshadow _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia|].
unfold SH_HI in *. apply rng_out_cons; [lia|]. apply rng_out_nil. }

assert (OWNTR : forall p q, In (p, q) (h_own a h) -> (h_stream_init h <> 0 -> p <> a_Bd a /\ p <> a_L a /\ p <> a_G a) ->
acl_rng Lv [(F, 8%nat)] S1 p q /\ rng_out [(F + 8688, F + 8688 + 408)] p q).
{ intros p q Hin NE. split; [apply (acl_live _ _ _ _ _ _ _ (KEEP _ _ Hin NE)); lia|].
apply rng_out_cons; [apply (iv_own_frame X a h HSP _ _ _ _ _ _ Hin); lia|]. apply rng_out_nil. }
assert (NEDc : h_stream_init h <> 0 -> a_Dc a <> a_Bd a /\ a_Dc a <> a_L a /\ a_Dc a <> a_G a).
{ intros NS. split; [exact (proj1 (ONE NS _ (or_introl eq_refl)))|]. split; [exact (proj1 (ONE NS _ (or_intror (or_introl eq_refl))))|].
exact (proj1 (ONE NS _ (or_intror (or_intror eq_refl)))). }
assert (BOK : bits_ok (h_bits h)) by (destruct HP as (_ & _ & _ & _ & B & _); exact B).
assert (BITS' : bits_rep asegs m' (F + 8400) (a_Dc a) (h_bits h)).
{ destruct (OWNTR _ _ (own_in_Dc a h) NEDc) as (D1 & D2).
apply (bits_rep_tr _ _ _ _ m m' PR _ _ _ BITS BOK); [| | exact D1| exact D2].
- apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia.
- apply rng_out_cons; [lia|]. apply rng_out_nil. }
assert (SY' : sync_rep m' (F + 8480) (a_Dsy a) (h_oy h) (a_sybytes a)).
{ apply (sync_rep_tr _ _ _ _ m m' PR _ _ _ _ SY).
- apply (acl_frame _ _ _ F 8 _ _ INF); change (fs_size 8) with 16384; lia.
- apply rng_out_cons; [lia|]. apply rng_out_nil.
- intros NS. apply (OWNTR _ _ (own_in_Dsy a h NS)). intros NI.
split; [exact (proj1 (proj2 (ONE NI _ (or_introl eq_refl))) NS)|].
split; [exact (proj1 (proj2 (ONE NI _ (or_intror (or_introl eq_refl)))) NS)|].
exact (proj1 (proj2 (ONE NI _ (or_intror (or_intror eq_refl)))) NS). }
assert (DEC' : h_dec_rep X m' a h).
{ apply (h_dec_rep_tr _ _ _ _ m m' PR X a h DEC). intros b Hb.
assert (NS0 : h_st h <> None) by (unfold h_dec_rep in DEC; destruct (h_st h); [discriminate| destruct DEC as (_ & E); rewrite E in Hb; destruct Hb]).
apply (OWNTR _ _ (own_in_blk a h NS0 b Hb)). intros NI.
split; [exact (proj2 (proj2 (ONE NI _ (or_introl eq_refl))) NS0 b Hb)|].
split; [exact (proj2 (proj2 (ONE NI _ (or_intror (or_introl eq_refl)))) NS0 b Hb)|].
exact (proj2 (proj2 (ONE NI _ (or_intror (or_intror eq_refl)))) NS0 b Hb). }
clear OSR DEC BITS OWNTR SY.

assert (FPH : fp_h X a h [(F + 8688, F + 8688 + 408)]) by (apply fp_h_cons; [right; right; left; lia| apply fp_h_nil]).
destruct (h_io_step RT OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img X HX Σ1 m m' a h _ _ HSP PR XL FPH (AF_DRV _ _ ART') PF ERR OUTR SSP)
as (PF' & ERR' & OUTR' & SSP').
unfold hrep. unfold HO_ENH, HO_OUT, HO_FSZ, HO_BITS, HO_OY, HO_OG, HO_OP, HO_OS, HO_STEREO, HO_RATE, HO_LOOK.
rewrite EOY, EBI, EFS, ERA, EDsy, Esyb, EDc.
split; [exact ART'|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact PF'|]. split; [exact ERR'|]. split; [exact OUTR'|]. split; [exact SSP'|].
split; [exact SP'|]. split; [exact LSH'|]. split; [exists je; exact ENH'|]. split; [exists ows; split; [exact OUTB'| exact LOWS]|].
split; [exact FSZ'|]. split; [exact BITS'|]. split; [exact SY'|]. split; [exact OGC'|]. split; [exact OPC'|].
split; [unfold HO_OS in OSR'; exact OSR'|]. split; [exists stb; exact STB'|]. split; [exact RATE'|]. split; [exists wl; exact LOOK'|].
split; [| exact HP'].
unfold h_dec_rep in DEC' |- *. rewrite EST, ES, ELBD, EDc. exact DEC'.
Qed.

Lemma h_os_rep_intro : forall (m : mem) a (h : hstate unit), h_stream_init h <> 0 ->
rw_cells asegs m (F + HO_OS) (stream_cells (a_Bd a) (a_L a) (a_G a) (a_shdr a) (h_os h)) -> length (a_shdr a) = 284%nat ->
stream_arrays m (h_os h) (a_Bd a) (a_L a) (a_G a) (a_body a) (a_lws a) (a_gws a) -> os_pure (h_os h) ->
a_Bd a <> a_L a -> a_Bd a <> a_G a -> a_L a <> a_G a -> h_os_rep X m a h.
Proof.
intros m a h NE C LH ARR (FOK & SINV & BINV & LOK & GL & BD & LV & GV & LS & BS) N1 N2 N3.
unfold h_os_rep. destruct (Z.eqb_spec (h_stream_init h) 0) as [E0|_]; [exfalso; exact (NE E0)|].
split; [exact C|]. split; [exact LH|]. split; [exact ARR|]. split; [exact FOK|]. split; [exact SINV|]. split; [exact BINV|].
split; [exact LOK|]. split; [exact GL|]. split; [exact BD|]. split; [exact LV|]. split; [exact GV|]. split; [exact LS|].
split; [exact BS|]. split; [exact N1|]. split; [exact N2| exact N3].
Qed.

Lemma hpure_with_os : forall (h : hstate unit) (os : stream_st unit) si, hpure X h -> (si = 0 \/ si = 1) ->
os_lacing_fill os <= h_consumed X h -> os_body_fill os <= h_consumed X h ->
os_lacing_storage os <= 1568 + h_consumed X h -> os_body_storage os <= 17408 + 2 * h_consumed X h ->
h_packet_count h + (os_lacing_fill os - os_lacing_returned os) <= 162 * h_consumed X h ->
hpure X (h_with_os h os si).
Proof.
intros h os si HP SI B1 B2 B3 B4 B5. unfold hpure, h_consumed, h_pend in *.
cbn [h_with_os h_oy h_os h_bits h_st h_stream_init h_packet_count h_last_granule h_nframes h_eos h_channels h_rate h_extra_headers
h_speex_serialno h_frame_size h_granule_frame_size h_bytes_remaining].
destruct HP as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & A18 & A19 & A20 & A21 & A22 & REST).
do 16 (split; [assumption|]). split; [exact SI|]. do 5 (split; [assumption|]). repeat split; lia.
Qed.
Lemma budget_with_os : forall (h : hstate unit) og (os : stream_st unit) si, h_page_budget X h og ->
os_lacing_fill os = 0 -> os_body_fill os = 0 -> os_lacing_returned os = 0 ->
os_lacing_storage os <= Z.max 1024 (os_lacing_storage (h_os h)) -> os_body_storage os <= Z.max 16384 (os_body_storage (h_os h)) ->
h_page_budget X (h_with_os h os si) og.
Proof.
intros h og os si (cold & C0 & C1 & C2 & C3 & C4 & C5 & C6 & C7) E1 E2 E3 B1 B2. exists cold.
unfold h_consumed, h_pend in *. cbn [h_with_os h_oy h_os h_bytes_remaining h_packet_count].
rewrite E1, E2, E3. repeat split; lia.
Qed.

Lemma hrep_sinit : forall (Σ1 Σ2 : rts RT) (m m' : mem) a (h : hstate unit) spill ogc opc ser Bd L G (jb : list byte) (lws gws : list word),
hsig RT X Σ1 a h -> hrep RT OUT_rep ERR_rep IO_FP X Σ1 m a h spill ogc opc ->
cells_size spill = 216%nat -> cells_size ogc = 32%nat -> cells_size opc = 48%nat ->
h_stream_init h = 0 -> -2^31 <= ser < 2^31 ->
rt_after RT Σ2 S1 lo m m' ->
rt_pres_fp (rt_live RT Σ1) (rt_frames RT Σ1) S1 [(F + 8688, F + 8688 + 408)] m m' ->
rw_cells asegs m' (F + 8688) (stream_cells Bd L G zero_hdr (init_os (Some tt) (Some tt) (Some tt) ser)) ->
u8arr asegs m' Bd jb -> Z.of_nat (length jb) = 16384 ->
u32arr asegs m' L lws -> Z.of_nat (length lws) = 1024 -> u64arr asegs m' G gws -> Z.of_nat (length gws) = 1024 ->
rt_live RT Σ2 = (G, 8192) :: (L, 4096) :: (Bd, 16384) :: rt_live RT Σ1 -> rt_frames RT Σ2 = rt_frames RT Σ1 -> rt_sp0 RT Σ2 = rt_sp0 RT Σ1 ->
rt_credit RT Σ2 = rt_credit RT Σ1 -> rt_pois RT Σ2 = rt_pois RT Σ1 ->
stream_live RT Σ2 (init_os (Some tt) (Some tt) (Some tt) ser) Bd L G ->
hsig RT X Σ2 (a_set_os a Bd L G zero_hdr jb lws gws ((G, 8192) :: (L, 4096) :: (Bd, 16384) :: a_P a))
(set_stream_init h (init_os (Some tt) (Some tt) (Some tt) ser))
/\ hrep RT OUT_rep ERR_rep IO_FP X Σ2 m' (a_set_os a Bd L G zero_hdr jb lws gws ((G, 8192) :: (L, 4096) :: (Bd, 16384) :: a_P a))
(set_stream_init h (init_os (Some tt) (Some tt) (Some tt) ser)) spill ogc opc.
Proof using AF HX ERR_loc OUT_loc IO_img AF_DRV.
intros Σ1 Σ2 m m' a h spill ogc opc ser Bd L G jb lws gws HS HR SPS OGS OPS SI0 SR (ART' & MI' & WM' & ST') PR OS' UB LB UL LL UG LG
EL2 EF2 ES2 EC2 EP2 SLV.
pose proof (own_pos RT OUT_rep ERR_rep IO_FP X Σ1 m a h spill ogc opc HR) as OPOS.
pose proof HR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HP).
pose proof HS as (EL & ND & PERM & EF & ESP & EPO0 & ECR).
pose proof SLV as (IB & IL & IG & NBL & NBG & NLG).
set (os1 := init_os (Some tt) (Some tt) (Some tt) ser) in *.
set (P1 := (G, 8192) :: (L, 4096) :: (Bd, 16384) :: a_P a).
set (a1 := a_set_os a Bd L G zero_hdr jb lws gws P1).
rewrite set_stream_init_with.
assert (EOWN : h_own a1 (h_with_os h os1 1) = ((match h_st h with Some _ => blocks_live (a_LBD a) | None => [] end) ++ [(a_Dc a, sb_buf_size (h_bits h))])
++ [(Bd, 16384); (L, 4096); (G, 8192)] ++ (match sy_data (h_oy h) with Some _ => [(a_Dsy a, sy_storage (h_oy h))] | None => [] end)).
{ unfold h_own. cbn [a1 a_set_os a_Dsy a_Dc a_Bd a_L a_G a_LBD h_with_os h_oy h_os h_bits h_st h_stream_init os1 init_os os_body_storage os_lacing_storage Z.eqb].
rewrite <- app_assoc. reflexivity. }
assert (EOWN0 : h_own a h = ((match h_st h with Some _ => blocks_live (a_LBD a) | None => [] end) ++ [(a_Dc a, sb_buf_size (h_bits h))])
++ (match sy_data (h_oy h) with Some _ => [(a_Dsy a, sy_storage (h_oy h))] | None => [] end)).
{ unfold h_own. rewrite SI0. cbn [Z.eqb app]. rewrite <- app_assoc. reflexivity. }
split.
- unfold hsig. cbn [a1 a_set_os a_P]. rewrite EL2, EF2, ES2, EC2, EP2, EL. fold P1.
split; [reflexivity|].
split.
{ apply (live_nodup RT AF Σ2 m' P1 [] (x_live X) ART'); [rewrite EL2, EL; reflexivity|].
intros [p q] Hin. cbn [snd]. destruct Hin as [E|[E|[E|Hin]]]; try (injection E as <- <-; lia).
exact (OPOS p q (Permutation_in _ PERM Hin)). }
split.
{ rewrite EOWN. unfold P1. rewrite EOWN0 in PERM.
eapply perm_trans; [do 3 apply perm_skip; exact PERM|].
lazymatch goal with |- Permutation (?x :: ?y :: ?z :: ?D ++ ?S) (?D ++ _ ++ ?S) =>
change (x :: y :: z :: D ++ S) with ([x; y; z] ++ D ++ S);
eapply perm_trans; [apply Permutation_app_swap_app|]; apply Permutation_app_head;
change ([x; y; z] ++ S) with (x :: y :: z :: S); change ([(Bd, 16384); (L, 4096); (G, 8192)] ++ S) with ((Bd, 16384) :: (L, 4096) :: (G, 8192) :: S) end.
eapply perm_trans; [apply perm_swap|]. eapply perm_trans; [apply perm_skip; apply perm_swap|]. apply perm_swap. }
split; [exact EF|]. split; [exact ESP|]. split; [exact EPO0|]. unfold h_cost in *. cbn [h_with_os h_packet_count]. exact ECR.
- apply (hrep_os_step Σ1 Σ2 m m' a a1 h (h_with_os h os1 1) spill ogc opc (rt_live RT Σ1) HS HR SPS OGS OPS ART' MI' ST').
+ intros e He. rewrite EL. apply in_or_app. right. exact He.
+ intros p q Hin _. rewrite EL. apply in_or_app. left. exact (Permutation_in _ (Permutation_sym PERM) Hin).
+ rewrite EF in PR. exact PR.
+ apply h_os_rep_intro; cbn [a1 a_set_os a_Bd a_L a_G a_shdr a_body a_lws a_gws h_with_os h_os h_stream_init].
* discriminate.
* unfold HO_OS. exact OS'.
* reflexivity.
* unfold stream_arrays. cbn [os1 init_os os_body_storage os_body os_lacing os_lacing_storage].
split; [exact UB|]. split; [exact LB|]. split; [split; [reflexivity| cbn; lia]|].
split; [exact UL|]. split; [split; [reflexivity| cbn; lia]|]. split; [exact LL|]. split; [exact UG| exact LG].
* apply init_os_pure. exact SR.
* exact NBL. * exact NBG. * exact NLG.
+ reflexivity. + reflexivity. + reflexivity. + reflexivity. + reflexivity.
+ reflexivity. + reflexivity. + reflexivity. + reflexivity. + reflexivity.
+ pose proof HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & P1' & P2' & P3' & P4' & P5' & P6' & P7' & P8').
apply hpure_with_os; [exact HP| right; reflexivity| ..]; cbn [os1 init_os os_lacing_fill os_body_fill os_lacing_storage os_body_storage os_lacing_returned]; lia.
Qed.

Lemma hrep_reset : forall (Σ1 : rts RT) (m m1 : mem) a (h : hstate unit) spill ogc opc ser,
hsig RT X Σ1 a h -> hrep RT OUT_rep ERR_rep IO_FP X Σ1 m a h spill ogc opc ->
cells_size spill = 216%nat -> cells_size ogc = 32%nat -> cells_size opc = 48%nat ->
h_stream_init h <> 0 -> -2^31 <= ser < 2^31 ->
munch [(F + 8688, F + 8688 + 408)] m m1 -> wmono asegs m m1 -> mem_inv asegs m1 ->
rw_cells asegs m1 (F + 8688) (stream_cells (a_Bd a) (a_L a) (a_G a) (a_shdr a) (snd (ogg_stream_reset_serialno (h_os h) ser))) ->
hsig RT X Σ1 a (set_ogg h (h_oy h) (snd (ogg_stream_reset_serialno (h_os h) ser)))
/\ hrep RT OUT_rep ERR_rep IO_FP X Σ1 m1 a (set_ogg h (h_oy h) (snd (ogg_stream_reset_serialno (h_os h) ser))) spill ogc opc.
Proof using AF HX ERR_loc OUT_loc IO_img AF_DRV.
intros Σ1 m m1 a h spill ogc opc ser HS HR SPS OGS OPS SI SR MU WM MI1 OS1.
pose proof HR as (ART0 & _ & ST & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & OSR & _ & _ & _ & _ & HP).
pose proof (hsep_of RT AF OUT_rep IO_FP X HX Σ1 m a h ART0 HS) as HSP.
pose proof (hx_arith OUT_rep IO_FP X HX) as (U336 & UT & U16 & S32 & SR' & LW & LR & SHLO & FP0 & F64 & FL & FI & ESF & ESF2 & SH1 & SH2 & FSA).
unfold RT_STACK, H_STACK in LR.
pose proof HS as (EL & ND & PERM & EF & ESP & EPO0 & ECR).
assert (INF : In (F, 8%nat) [(F, 8%nat)]) by (left; reflexivity).
unfold h_os_rep in OSR. destruct (Z.eqb_spec (h_stream_init h) 0) as [E0|_]; [exfalso; exact (SI E0)|].
destruct OSR as (_ & LH & (UB & LB & BP & UL & WP & LL & UG & LG) & FOK & SINV & BINV & LOK & GL & BD & LV & GV & LS & BS & NBL & NBG & NLG).
destruct (reset_os_pure (h_os h) ser (conj FOK (conj SINV (conj BINV (conj LOK (conj GL (conj BD (conj LV (conj GV (conj LS BS))))))))) SR)
as (POS & ELS & EBS & ELF & EBF & ELR & ESN & EBO & ELA).
unfold bptr in *.
set (os1 := snd (ogg_stream_reset_serialno (h_os h) ser)) in *.
assert (EOWN : h_own a (set_ogg h (h_oy h) os1) = h_own a h).
{ unfold h_own. cbn [set_ogg h_oy h_os h_bits h_st h_stream_init]. rewrite ELS, EBS. reflexivity. }
assert (PR : rt_pres_fp (rt_live RT Σ1) [(F, 8%nat)] S1 [(F + 8688, F + 8688 + 408)] m m1).
{ apply (pres_fp_of_munch _ _ _ _ _ m m1 MU). intros x _ Ho. exact Ho. }
assert (ART1 : ART RT Σ1 m1).
{ apply (af_frame RT AF Σ1 m m1 S1 ART0); [rewrite ESP; pose proof (hi_lo _ _ _ HX) as (LW0 & _); unfold STACK_WIN in *; lia| | exact WM].
intros b Hb. apply MU. cbn [outside]. split; [| exact I]. intros Hin. apply Hb. rewrite EF.
exact (acl_frame (rt_live RT Σ1) [(F, 8%nat)] S1 F 8 (F + 8688) 408 INF ltac:(lia) ltac:(change (fs_size 8) with 16384; lia) _ Hin). }
assert (ST1 : stk asegs m1 lo S1).
{ apply (stk_agree asegs m m1 lo S1 ST); [| exact WM]. apply (agree_of_munch _ m m1 _ MU). intros x Hx. cbn [outside].
change (fs_size 8) with 16384 in FL. split; [lia| exact I]. }
split.
- unfold hsig. rewrite EOWN. unfold h_cost in *. cbn [set_ogg h_packet_count]. exact HS.
- apply (hrep_os_step Σ1 Σ1 m m1 a a h (set_ogg h (h_oy h) os1) spill ogc opc (rt_live RT Σ1) HS HR SPS OGS OPS ART1 MI1 ST1).
+ intros e He. rewrite EL. apply in_or_app. right. exact He.
+ intros p q Hin _. rewrite EL. apply in_or_app. left. exact (Permutation_in _ (Permutation_sym PERM) Hin).
+ exact PR.
+ destruct (own_in_os a h SI) as (IB & IL & IG).
assert (OWNTR : forall p q, In (p, q) (h_own a h) -> acl_rng (rt_live RT Σ1) [(F, 8%nat)] S1 p q /\ rng_out [(F + 8688, F + 8688 + 408)] p q).
{ assert (INL : forall e, In e (h_own a h) -> In e (rt_live RT Σ1)).
{ intros e He. rewrite EL. apply in_or_app. left. exact (Permutation_in e (Permutation_sym PERM) He). }
intros p q Hin. split; [apply (acl_live _ _ _ _ _ _ _ (INL _ Hin)); lia|].
apply rng_out_cons; [apply (iv_own_frame X a h HSP _ _ _ _ _ _ Hin); change (fs_size 8) with 16384 in *; lia|]. apply rng_out_nil. }
destruct (OWNTR _ _ IB) as (B1 & B2). destruct (OWNTR _ _ IL) as (L1 & L2). destruct (OWNTR _ _ IG) as (G1 & G2).
apply h_os_rep_intro; cbn [set_ogg h_os h_stream_init].
* exact SI.
* unfold HO_OS. exact OS1.
* exact LH.
* unfold stream_arrays, bptr. rewrite ELS, EBS.
split; [apply (htr_u8 _ _ _ _ m m1 PR _ _ UB); rewrite LB; assumption|]. split; [exact LB|].
split; [unfold body_pre; rewrite EBO; cbn [length firstn]; split; [reflexivity| lia]|].
split; [apply (htr_u32 _ _ _ _ m m1 PR _ _ UL); rewrite LL; assumption|].
split; [unfold wpre; rewrite ELA; cbn [length firstn map]; split; [reflexivity| lia]|].
split; [exact LL|]. split; [apply (htr_u64 _ _ _ _ m m1 PR _ _ UG); rewrite LG; assumption| exact LG].
* exact POS.
* exact NBL. * exact NBG. * exact NLG.
+ reflexivity. + reflexivity. + reflexivity. + reflexivity. + reflexivity.
+ reflexivity. + reflexivity. + reflexivity. + reflexivity. + reflexivity.
+ pose proof HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & P17 & _ & _ & _ & P1' & P2' & P3' & P4' & P5' & P6' & P7' & P8').
rewrite set_ogg_with. apply hpure_with_os; [exact HP| exact P17| ..]; rewrite ?ELF, ?EBF, ?ELR, ?ELS, ?EBS; lia.
Qed.

Lemma xlive_ne_own : forall (Σ1 : rts RT) (m : mem) a (h : hstate unit) spill ogc opc, hsig RT X Σ1 a h ->
hrep RT OUT_rep ERR_rep IO_FP X Σ1 m a h spill ogc opc ->
forall p q, In (p, q) (h_own a h) -> forall e, In e (x_live X) -> fst e <> p.
Proof using AF HX.
intros Σ1 m a h spill ogc opc HS HR p q Hin [p' q'] He E. cbn [fst] in E. subst p'.
pose proof HR as (ART0 & _).
pose proof (hsep_of RT AF OUT_rep IO_FP X HX Σ1 m a h ART0 HS) as HSP.
pose proof (own_pos RT OUT_rep ERR_rep IO_FP X Σ1 m a h spill ogc opc HR p q Hin) as P1.
pose proof (proj1 (hi_live _ _ _ HX) _ _ He) as P2.
destruct (proj1 HSP p q Hin) as (_ & _ & _ & _ & _ & SEP). destruct (SEP _ _ He); lia.
Qed.

Lemma hpure_pagein : forall (h : hstate unit) og (hs : list byte) (body : list Z),
hpure X h -> h_page_budget X h og -> os_pure (h_os h) ->
os_lacing_fill (h_os h) <= os_lacing_storage (h_os h) -> os_body_fill (h_os h) <= os_body_storage (h_os h) ->
length hs = (27 + Z.to_nat (znth (ubytes hs) 26))%nat -> Z.of_nat (length hs) = pg_header_len og -> zlength body = pg_body_len og ->
bytes_ok body -> zsum (lacing_of (ubytes hs)) = zlength body ->
os_pure (snd (pagein_res (h_os h) (ubytes hs) body)) /\ hpure X (set_ogg h (h_oy h) (snd (pagein_res (h_os h) (ubytes hs) body))).
Proof using HX.
intros h og hs body HP (cold & C0 & C1 & C2 & C3 & C4 & C5 & C6 & C7) POS LFS BFS LENH HLEN BLEN BOK ZSEQ.
pose proof (hi_pay _ _ _ HX) as (_ & SZ & _). unfold MAX_FUZZ_SIZE in SZ.
pose proof HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & P17 & _ & BR & _ & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
unfold h_consumed, h_pend in *.
assert (H26 : 0 <= znth (ubytes hs) 26 < 256) by (apply znth_ubytes_range).
pose proof (zlength_nonneg body) as ZB.
destruct (pagein_res_pure (h_os h) hs body POS LENH BOK ZSEQ LFS BFS ltac:(unfold bptr; lia) ltac:(unfold bptr; lia))
as (POS' & B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9).
unfold bptr in *.
set (os' := snd (pagein_res (h_os h) (ubytes hs) body)) in *.
split; [exact POS'|].
pose proof POS' as (_ & (R0 & _) & _).
rewrite set_ogg_with. apply hpure_with_os; [exact HP| exact P17| ..]; unfold h_consumed, h_pend, bptr in *; lia.
Qed.

Lemma nodup_fst_remove_mid : forall (A B : list (Z * Z)) x, List.NoDup (map fst (A ++ x :: B)) -> List.NoDup (map fst (A ++ B)).
Proof. intros A B x ND. rewrite map_app in ND |- *. cbn [map] in ND. exact (NoDup_remove_1 _ _ _ ND). Qed.

Lemma hrep_pagein : forall (Σ1 Σ2 : rts RT) (m m' : mem) a (h : hstate unit) spill ogc opc (hs : list byte) (body : list Z)
Bd' L' Gv' (body' : list byte) (lws' gws' : list word),
hsig RT X Σ1 a h -> hrep RT OUT_rep ERR_rep IO_FP X Σ1 m a h spill ogc opc ->
cells_size spill = 216%nat -> cells_size ogc = 32%nat -> cells_size opc = 48%nat ->
h_stream_init h <> 0 ->
rt_after_f RT Σ2 S1 lo m m' ->
rt_pres_fp (pgi_rest (a_Bd a) (a_L a) (a_G a) (rt_live RT Σ1)) (rt_frames RT Σ1) S1 [(F + 8688, F + 8688 + 408)] m m' ->
rw_cells asegs m' (F + 8688) (stream_cells Bd' L' Gv' (a_shdr a) (snd (pagein_res (h_os h) (ubytes hs) body))) ->
stream_arrays m' (snd (pagein_res (h_os h) (ubytes hs) body)) Bd' L' Gv' body' lws' gws' ->
stream_live RT Σ2 (snd (pagein_res (h_os h) (ubytes hs) body)) Bd' L' Gv' ->
rt_live RT Σ2 = pagein_live (rt_live RT Σ1) (h_os h) (ubytes hs) body (a_Bd a) (a_L a) (a_G a) Bd' L' Gv' ->
pagein_same (h_os h) (ubytes hs) body (a_Bd a) (a_L a) (a_G a) Bd' L' Gv' ->
rt_frames RT Σ2 = rt_frames RT Σ1 -> rt_sp0 RT Σ2 = rt_sp0 RT Σ1 -> rt_credit RT Σ2 = rt_credit RT Σ1 -> rt_pois RT Σ2 = rt_pois RT Σ1 ->
os_pure (snd (pagein_res (h_os h) (ubytes hs) body)) ->
hpure X (set_ogg h (h_oy h) (snd (pagein_res (h_os h) (ubytes hs) body))) ->
hsig RT X Σ2 (a_set_os a Bd' L' Gv' (a_shdr a) body' lws' gws' (pagein_live (a_P a) (h_os h) (ubytes hs) body (a_Bd a) (a_L a) (a_G a) Bd' L' Gv'))
(set_ogg h (h_oy h) (snd (pagein_res (h_os h) (ubytes hs) body)))
/\ hrep RT OUT_rep ERR_rep IO_FP X Σ2 m' (a_set_os a Bd' L' Gv' (a_shdr a) body' lws' gws' (pagein_live (a_P a) (h_os h) (ubytes hs) body (a_Bd a) (a_L a) (a_G a) Bd' L' Gv'))
(set_ogg h (h_oy h) (snd (pagein_res (h_os h) (ubytes hs) body))) spill ogc opc.
Proof using AF HX ERR_loc OUT_loc IO_img AF_DRV.
intros Σ1 Σ2 m m' a h spill ogc opc hs body Bd' L' Gv' body' lws' gws' HS HR SPS OGS OPS SI (ART' & MI' & ST') PR OS' ARR' SLV' EL2 SAME
EF2 ES2 EC2 EP2 POS' HP'.
pose proof (own_pos RT OUT_rep ERR_rep IO_FP X Σ1 m a h spill ogc opc HR) as OPOS.
pose proof (xlive_ne_own Σ1 m a h spill ogc opc HS HR) as XNE.
pose proof HR as (ART0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & OSR & _).
pose proof (hsep_of RT AF OUT_rep IO_FP X HX Σ1 m a h ART0 HS) as HSP.
pose proof HS as (EL & ND & PERM & EF & ESP & EPO0 & ECR).
pose proof SLV' as (IB' & IL' & IG' & NBL' & NBG' & NLG').
unfold h_os_rep in OSR. destruct (Z.eqb_spec (h_stream_init h) 0) as [E0|_]; [exfalso; exact (SI E0)|].
destruct OSR as (_ & LH & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NBL & NBG & NLG).
destruct (own_in_os a h SI) as (IB & IL & IG).
pose proof (pagein_res_store (h_os h) (ubytes hs) body) as (ST1 & ST2 & ST3 & ST4 & ST5). cbv zeta in ST1, ST2, ST3, ST4, ST5.
pose proof SAME as (SA1 & SA2 & SA3).
pose proof (pgi_os3_body (h_os h) (ubytes hs)) as (_ & EB3).
pose proof (pagein_returned_fields (h_os h)) as (_ & _ & _ & EL1 & _).
unfold bptr in *.
set (os := h_os h) in *. set (os' := @snd Z (stream_st unit) (pagein_res os (ubytes hs) body)) in *.
set (P' := pagein_live (a_P a) os (ubytes hs) body (a_Bd a) (a_L a) (a_G a) Bd' L' Gv').
set (a' := a_set_os a Bd' L' Gv' (a_shdr a) body' lws' gws' P').
set (core := (match h_st h with Some _ => blocks_live (a_LBD a) | None => [] end) ++ [(a_Dc a, sb_buf_size (h_bits h))]).
set (sync := match sy_data (h_oy h) with Some _ => [(a_Dsy a, sy_storage (h_oy h))] | None => [] end).
assert (EOWN0 : h_own a h = core ++ [(a_Bd a, os_body_storage os); (a_L a, 4 * os_lacing_storage os); (a_G a, 8 * os_lacing_storage os)] ++ sync).
{ unfold h_own, core, sync. fold os. destruct (Z.eqb_spec (h_stream_init h) 0) as [E0|_]; [exfalso; exact (SI E0)|]. rewrite <- app_assoc. reflexivity. }
assert (EOWN1 : h_own a' (set_ogg h (h_oy h) os') = core ++ [(Bd', os_body_storage os'); (L', 4 * os_lacing_storage os'); (Gv', 8 * os_lacing_storage os')] ++ sync).
{ unfold h_own, core, sync. cbn [a' a_set_os a_Dsy a_Dc a_Bd a_L a_G a_LBD set_ogg h_oy h_os h_bits h_st h_stream_init].
destruct (Z.eqb_spec (h_stream_init h) 0) as [E0|_]; [exfalso; exact (SI E0)|]. rewrite <- app_assoc. reflexivity. }
pose proof (proj2 (proj2 HSP)) as NDO. rewrite EOWN0 in NDO, PERM.
assert (ELP : rt_live RT Σ2 = P' ++ x_live X).
{ rewrite EL2, EL. apply pagein_live_app. intros e He.
split; [exact (XNE _ _ IB e He)|]. split; [exact (XNE _ _ IL e He)| exact (XNE _ _ IG e He)]. }
assert (POSB' : 0 < os_body_storage os') by (destruct POS' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & X1); exact X1).
assert (POSL' : 0 < os_lacing_storage os') by (destruct POS' as (_ & _ & _ & _ & _ & _ & _ & _ & X1 & _); exact X1).

assert (PERM' : Permutation P' (core ++ [(Bd', os_body_storage os'); (L', 4 * os_lacing_storage os'); (Gv', 8 * os_lacing_storage os')] ++ sync)).
{ unfold P', pagein_live. cbv zeta. unfold bptr.
destruct (pgi_ok os (ubytes hs)) eqn:OK.
2:{ destruct (SA1 eq_refl) as (-> & -> & ->). destruct (ST1 eq_refl) as (-> & ->). exact PERM. }
lazymatch goal with |- Permutation (if _ then (if ?c then _ else _) else _) _ => destruct c eqn:C1 end;
lazymatch goal with |- Permutation (if ?c then _ else _) _ => destruct c eqn:C2 end.
-
destruct (SA2 eq_refl eq_refl) as (-> & ->). rewrite (SA3 eq_refl eq_refl), (ST2 eq_refl eq_refl), (ST4 eq_refl eq_refl). exact PERM.
-
destruct (SA2 eq_refl eq_refl) as (-> & ->). rewrite (ST2 eq_refl eq_refl), (ST5 eq_refl eq_refl), EB3.
pose proof (perm_live_remove_mid (a_Bd a) _ (a_P a) core ([(a_L a, 4 * os_lacing_storage os); (a_G a, 8 * os_lacing_storage os)] ++ sync) PERM NDO) as PR1.
eapply perm_trans; [apply perm_skip; exact PR1|]. apply Permutation_middle.
-
rewrite (SA3 eq_refl eq_refl), (ST3 eq_refl eq_refl), (ST4 eq_refl eq_refl), EL1.
assert (E1 : core ++ [(a_Bd a, os_body_storage os); (a_L a, 4 * os_lacing_storage os); (a_G a, 8 * os_lacing_storage os)] ++ sync
= (core ++ [(a_Bd a, os_body_storage os)]) ++ (a_L a, 4 * os_lacing_storage os) :: (a_G a, 8 * os_lacing_storage os) :: sync)
by (rewrite <- app_assoc; reflexivity).
rewrite E1 in PERM, NDO.
pose proof (perm_live_remove_mid (a_L a) _ (a_P a) _ _ PERM NDO) as PR1.
pose proof (nodup_fst_remove_mid _ _ _ NDO) as NDO1.
pose proof (perm_live_remove_mid (a_G a) _ _ _ _ PR1 NDO1) as PR2.
eapply perm_trans; [apply perm_skip; apply perm_skip; exact PR2|].
rewrite <- app_assoc. cbn [app].
eapply perm_trans; [apply perm_skip; apply Permutation_middle|].
eapply perm_trans; [apply Permutation_middle|]. apply Permutation_app_head.
eapply perm_trans; [apply perm_swap|]. eapply perm_trans; [apply perm_skip; apply perm_swap|]. apply perm_swap.
-
rewrite (ST3 eq_refl eq_refl), (ST5 eq_refl eq_refl), EL1, EB3.

assert (NLB : L' <> a_Bd a /\ Gv' <> a_Bd a).
{ assert (INP : forall e, In e (rt_live RT Σ2) -> fst e = a_Bd a -> e = (Bd', os_body_storage os + (zlength body - snd (pagein_skip (pgi_os3 os (ubytes hs)) (ubytes hs))) + 1024)).
{ intros e He Ee. rewrite EL2 in He. unfold pagein_live in He. unfold bptr in He. rewrite OK in He. cbv zeta in He. rewrite C1, C2, EB3 in He.
destruct He as [He|He]; [symmetry; exact He|].
apply X0a5.live_remove_In in He as (_ & NE). exfalso. exact (NE Ee). }
split; intros E.
- pose proof (INP _ IL' E) as E2. injection E2 as E2 _. exact (NBL' (eq_sym E2)).
- pose proof (INP _ IG' E) as E2. injection E2 as E2 _. exact (NBG' (eq_sym E2)). }
rewrite !live_remove_cons. cbn [fst].
replace (Gv' =? a_Bd a) with false by (symmetry; apply Z.eqb_neq; exact (proj2 NLB)).
replace (L' =? a_Bd a) with false by (symmetry; apply Z.eqb_neq; exact (proj1 NLB)).
assert (E1 : core ++ [(a_Bd a, os_body_storage os); (a_L a, 4 * os_lacing_storage os); (a_G a, 8 * os_lacing_storage os)] ++ sync
= (core ++ [(a_Bd a, os_body_storage os)]) ++ (a_L a, 4 * os_lacing_storage os) :: (a_G a, 8 * os_lacing_storage os) :: sync)
by (rewrite <- app_assoc; reflexivity).
rewrite E1 in PERM, NDO.
pose proof (perm_live_remove_mid (a_L a) _ (a_P a) _ _ PERM NDO) as PR1.
pose proof (nodup_fst_remove_mid _ _ _ NDO) as NDO1.
pose proof (perm_live_remove_mid (a_G a) _ _ _ _ PR1 NDO1) as PR2.
pose proof (nodup_fst_remove_mid _ _ _ NDO1) as NDO2.
rewrite <- app_assoc in PR2, NDO2. cbn [app] in PR2, NDO2.
pose proof (perm_live_remove_mid (a_Bd a) _ _ _ _ PR2 NDO2) as PR3.
cbv iota.
eapply perm_trans; [do 3 apply perm_skip; exact PR3|]. cbn [app].
eapply perm_trans; [do 2 apply perm_skip; apply Permutation_middle|].
eapply perm_trans; [apply perm_skip; apply Permutation_middle|].
eapply perm_trans; [apply Permutation_middle|]. apply Permutation_app_head.
apply perm_skip. apply perm_swap. }
split.
- unfold hsig. cbn [a' a_set_os a_P]. rewrite EF2, ES2, EC2, EP2, EOWN1.
split; [exact ELP|].
split.
{ apply (live_nodup RT AF Σ2 m' P' [] (x_live X) ART'); [exact ELP|].
intros [p q] Hin. pose proof (Permutation_in _ PERM' Hin) as Hin'.
apply in_app_or in Hin' as [Hin'|Hin']; [apply (OPOS p q); rewrite EOWN0; apply in_or_app; left; exact Hin'|].
apply in_app_or in Hin' as [Hin'|Hin']; [destruct Hin' as [E|[E|[E|[]]]]; injection E as <- <-; cbn [snd]; lia|].
apply (OPOS p q). rewrite EOWN0. apply in_or_app. right. apply in_or_app. right. exact Hin'. }
split; [exact PERM'|].
split; [exact EF|]. split; [exact ESP|]. split; [exact EPO0|]. unfold h_cost in *. cbn [set_ogg h_packet_count]. exact ECR.
- apply (hrep_os_step Σ1 Σ2 m m' a a' h (set_ogg h (h_oy h) os') spill ogc opc (pgi_rest (a_Bd a) (a_L a) (a_G a) (rt_live RT Σ1)) HS HR SPS OGS OPS ART' MI' ST').
+ intros e He. apply pgi_rest_In. split; [rewrite EL; apply in_or_app; right; exact He|].
split; [exact (XNE _ _ IB e He)|]. split; [exact (XNE _ _ IL e He)| exact (XNE _ _ IG e He)].
+ intros p q Hin NE. apply pgi_rest_In. destruct (NE SI) as (N1 & N2 & N3).
split; [rewrite EL; apply in_or_app; left; rewrite EOWN0 in Hin; exact (Permutation_in _ (Permutation_sym PERM) Hin)|]. cbn [fst]. auto.
+ rewrite EF in PR. exact PR.
+ apply h_os_rep_intro; cbn [a' a_set_os a_Bd a_L a_G a_shdr a_body a_lws a_gws set_ogg h_os h_stream_init].
* exact SI. * unfold HO_OS. exact OS'. * exact LH. * exact ARR'. * exact POS'.
* exact NBL'. * exact NBG'. * exact NLG'.
+ reflexivity. + reflexivity. + reflexivity. + reflexivity. + reflexivity.
+ reflexivity. + reflexivity. + reflexivity. + reflexivity. + reflexivity.
+ exact HP'.
Qed.

End PStep.
