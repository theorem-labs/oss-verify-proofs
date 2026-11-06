(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0mx X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1da X1dg X1cg X1ck.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qz X1r8.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X001 X00b X04b X07z X05o X05p X05s
X09u X0af X0ae X09j X09m X09p X09q X09x X09l X09s X09t
X09z X0a0 X0a1 X0a2 X0a3 X0a4.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X14x X0r0 X0ra X0v9 X0wl X110 X106 X109 X10c X10d X10j X108 X10f X10g X10l X10m X10n X10o X10p X10q.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0v9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wl OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X110 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X106 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X109 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10d OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10j OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X108 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10f OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10g OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10l OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10m OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10n OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10o OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10p OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10q.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Arguments skipn {A} n l : simpl nomatch.
#[local] Arguments firstn {A} n l : simpl nomatch.

Definition stream_arrays (m : mem) (os : stream_st bptr) (Bd L Gv : Z) (bodybytes : list byte) (lws gws : list word) : Prop :=
u8arr bsegs m Bd bodybytes /\ Z.of_nat (length bodybytes) = os_body_storage os /\ body_pre (os_body os) bodybytes /\
u32arr bsegs m L lws /\ wpre (os_lacing os) lws /\ Z.of_nat (length lws) = os_lacing_storage os /\
u64arr bsegs m Gv gws /\ Z.of_nat (length gws) = os_lacing_storage os.

Definition pgi_os2 (os : stream_st bptr) (hdr : list Z) : stream_st bptr := lacing_expand_res (pagein_returned os) (znth hdr 26 + 1).
Definition pgi_os3 (os : stream_st bptr) (hdr : list Z) : stream_st bptr := pagein_unroll (pgi_os2 os hdr) (ogg_page_pageno hdr).

Definition pagein_res (os : stream_st bptr) (hdr body : list Z) : Z * stream_st bptr :=
let os1 := pagein_returned os in
if negb (ogg_page_serialno hdr =? os_serialno os1) then (-1, os1) else
if 0 <? ogg_page_version hdr then (-1, os1) else
let os3 := pgi_os3 os hdr in
let '(bos, segptr, skipped) := pagein_skip os3 hdr in
let bodysize := zlength body - skipped in
if negb (bodysize =? 0) then (0, pagein_segments (pagein_body (body_expand_res os3 bodysize) body skipped bodysize) hdr bos segptr)
else (0, pagein_segments os3 hdr bos segptr).

Lemma pagein_skip_le : forall (os : stream_st bptr) hdr bos segptr skipped, bytes_ok (lacing_of hdr) ->
pagein_skip os hdr = (bos, segptr, skipped) -> 0 <= skipped <= zsum (lacing_of hdr).
Proof.
intros os hdr bos segptr skipped Hb E. pose proof (pagein_skip_sum os hdr Hb) as S. rewrite E in S. destruct S as (Hseg & ->).
pose proof (zsum_split segptr (lacing_of hdr) ltac:(lia)) as SP.
pose proof (zsum_bytes_nonneg _ (bytes_ok_ztake segptr _ Hb)). pose proof (zsum_bytes_nonneg _ (bytes_ok_zdrop segptr _ Hb)). lia.
Qed.

Lemma pagein_returned_fields : forall os : stream_st bptr,
os_body_data (pagein_returned os) = os_body_data os /\ os_lacing_vals (pagein_returned os) = os_lacing_vals os /\
os_granule_vals (pagein_returned os) = os_granule_vals os /\ os_lacing_storage (pagein_returned os) = os_lacing_storage os /\
os_body_storage (pagein_returned os) = os_body_storage os.
Proof.
intros os. unfold pagein_returned.
destruct (negb (os_body_returned os =? 0)); destruct (negb (os_lacing_returned _ =? 0)); cbn; repeat split; reflexivity.
Qed.
Lemma pagein_unroll_body_data : forall (os : stream_st bptr) pn, os_body_data (pagein_unroll os pn) = os_body_data os.
Proof. intros os pn. unfold pagein_unroll. destruct (negb (pn =? os_pageno os)); [| reflexivity]. destruct (negb (os_pageno _ =? -1)); reflexivity. Qed.
Lemma pagein_unroll_body_storage : forall (os : stream_st bptr) pn, os_body_storage (pagein_unroll os pn) = os_body_storage os.
Proof. intros os pn. unfold pagein_unroll. destruct (negb (pn =? os_pageno os)); [| reflexivity]. destruct (negb (os_pageno _ =? -1)); reflexivity. Qed.

Lemma pgi_os3_body : forall (os : stream_st bptr) hdr,
os_body_data (pgi_os3 os hdr) = os_body_data os /\ os_body_storage (pgi_os3 os hdr) = os_body_storage os.
Proof.
intros os hdr. pose proof (pagein_returned_fields os) as (E1 & E2 & E3 & E4 & E5).
unfold pgi_os3, pgi_os2. rewrite pagein_unroll_body_data, pagein_unroll_body_storage. unfold lacing_expand_res.
destruct (os_lacing_fill (pagein_returned os) <? os_lacing_storage (pagein_returned os) - (znth hdr 26 + 1)); cbn [set_blocks os_body_data os_body_storage];
rewrite E1, E5; split; reflexivity.
Qed.

Lemma pagein_prun : forall (os : stream_st unit) hdr body q r q',
prun (ogg_stream_pagein (St := pst) p_realloc p_free os hdr body) q = Some (r, q') ->
os_body_data os <> None -> os_lacing_vals os <> None -> os_granule_vals os <> None ->
bytes_ok (lacing_of hdr) -> zsum (lacing_of hdr) <= zlength body -> 0 <= znth hdr 26 ->
0 <= os_lacing_storage os -> os_lacing_storage os + znth hdr 26 + 33 < 2^58 ->
0 <= os_body_storage os -> os_body_storage os + zlength body + 1024 < 2^62 ->
r = pagein_res os hdr body /\ q' = q.
Proof.
intros os hdr body q r q' H BD LD GD HB HS N0 LS0 LSB BS0 BSB.
unfold ogg_stream_pagein, ogg_stream_check in H. unfold pagein_res, pgi_os3, pgi_os2. cbv zeta in H |- *. unfold bptr in *.
destruct (os_body_data os) as [[]|] eqn:EBD; [| exfalso; apply BD; reflexivity].
pose proof (pagein_returned_fields os) as (E1 & E2 & E3 & E4 & E5). unfold bptr in *.
set (os1 := pagein_returned os) in *.
destruct (negb (ogg_page_serialno hdr =? os_serialno os1)); [rewrite prun_ret in H; injection H as <- <-; split; reflexivity|].
destruct (0 <? ogg_page_version hdr); [rewrite prun_ret in H; injection H as <- <-; split; reflexivity|].
rewrite prun_bind in H.
destruct (prun (os_lacing_expand p_realloc p_free os1 (znth hdr 26 + 1)) q) as [[[r2 os2] q2]|] eqn:EL; [| discriminate H].
apply lacing_expand_prun in EL; [| rewrite E2; exact LD| rewrite E3; exact GD| lia| rewrite E4; lia| rewrite E4; lia].
destruct EL as (EL & ->). injection EL as -> ->. cbn [negb Z.eqb] in H.
lazymatch type of H with context [pagein_skip ?x hdr] => set (os3 := x) in * end.
destruct (pagein_skip os3 hdr) as [[bos segptr] skipped] eqn:ESK.
pose proof (pagein_skip_le os3 hdr bos segptr skipped HB ESK) as SKL.
rewrite prun_bind in H.
destruct (negb (zlength body - skipped =? 0)) eqn:EBZ.
- rewrite prun_bind in H.
destruct (prun (os_body_expand p_realloc p_free os3 (zlength body - skipped)) q) as [[[r4 os4] q4]|] eqn:EB; [| discriminate H].
assert (X : os_body_data os3 <> None /\ os_body_storage os3 = os_body_storage os).
{ destruct (pgi_os3_body os hdr) as (Y1 & Y2). split; [| exact Y2].
intros Z. change (os_body_data (pgi_os3 os hdr) = None) in Z. rewrite Y1 in Z. unfold bptr in Z. rewrite EBD in Z. discriminate Z. }
destruct X as (X1 & X2).
apply body_expand_prun in EB; [| exact X1| lia| rewrite X2; lia| rewrite X2; lia].
destruct EB as (EB & ->). injection EB as -> ->. cbn [negb Z.eqb] in H. rewrite prun_ret in H. cbn [negb Z.eqb] in H.
rewrite prun_ret in H. injection H as <- <-. split; reflexivity.
- rewrite prun_ret in H. cbn [negb Z.eqb] in H. rewrite prun_ret in H. injection H as <- <-. split; reflexivity.
Qed.

Definition pgi_ok (os : stream_st bptr) (hdr : list Z) : bool :=
(ogg_page_serialno hdr =? os_serialno (pagein_returned os)) && negb (0 <? ogg_page_version hdr).
Definition pagein_live (live : list (Z * Z)) (os : stream_st bptr) (hdr body : list Z) (Bd L Gv Bd' L' Gv' : Z) : list (Z * Z) :=
if pgi_ok os hdr then
let os1 := pagein_returned os in
let need := znth hdr 26 + 1 in
let l1 := if os_lacing_fill os1 <? os_lacing_storage os1 - need then live
else (Gv', 8 * (os_lacing_storage os1 + need + 32)) :: (L', 4 * (os_lacing_storage os1 + need + 32)) :: live_remove Gv (live_remove L live) in
let os3 := pgi_os3 os hdr in
let bodysize := zlength body - snd (pagein_skip os3 hdr) in
if (bodysize =? 0) || (os_body_fill os3 <? os_body_storage os3 - bodysize) then l1
else (Bd', os_body_storage os3 + bodysize + 1024) :: live_remove Bd l1
else live.

Definition pagein_same (os : stream_st bptr) (hdr body : list Z) (Bd L Gv Bd' L' Gv' : Z) : Prop :=
(pgi_ok os hdr = false -> Bd' = Bd /\ L' = L /\ Gv' = Gv)
/\ (pgi_ok os hdr = true -> (os_lacing_fill (pagein_returned os) <? os_lacing_storage (pagein_returned os) - (znth hdr 26 + 1)) = true -> L' = L /\ Gv' = Gv)
/\ (pgi_ok os hdr = true ->
((zlength body - snd (pagein_skip (pgi_os3 os hdr) hdr) =? 0)
|| (os_body_fill (pgi_os3 os hdr) <? os_body_storage (pgi_os3 os hdr) - (zlength body - snd (pagein_skip (pgi_os3 os hdr) hdr)))) = true -> Bd' = Bd).

Section OggPageinCPS.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis MMOV : memmove_icontract RT e_memmove.
Hypothesis MCPY : memcpy_icontract RT e_memcpy.
Hypothesis LEXP : os_lacing_expand_cps RT.
Hypothesis BEXP : os_body_expand_cps RT.

Definition pgi_rest (Bd L Gv : Z) (live : list (Z * Z)) : list (Z * Z) := live_remove Gv (live_remove L (live_remove Bd live)).

Lemma pgi_rest_sub : forall Bd L Gv live e, In e (pgi_rest Bd L Gv live) -> In e live.
Proof. intros Bd L Gv live e H. unfold pgi_rest in H. do 3 apply live_remove_sub in H. exact H. Qed.

Definition ogg_stream_pagein_cps : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (A G Dsy nsy Bd L Gv f lo : Z) (k : nat) (og : page) (os : stream_st bptr) (shdr hs bs bodybytes : list byte) (lws gws : list word)
(q q' : pst) (r : Z * stream_st bptr),
fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 G -> tp = Z_to_bv 64 0x638c98 ->
prun (ogg_stream_pagein (St := pst) p_realloc p_free os (ubytes hs) (ubytes bs)) q = Some (r, q') ->
rw_cells bsegs m A (stream_cells Bd L Gv shdr os) -> length shdr = 284%nat -> 0 < A ->
stream_arrays m os Bd L Gv bodybytes lws gws ->
stream_fields_ok os -> stream_inv os -> body_inv os -> lacing_vals_ok (os_lacing os) ->
os_body_data os <> None -> os_lacing_vals os <> None -> os_granule_vals os <> None ->
stream_live RT Σ os Bd L Gv ->
rw_cells bsegs m G (page_cells Dsy og) -> 0 < G ->
bytes_at bsegs m (Dsy + pg_hdr og) hs -> bytes_at bsegs m (Dsy + pg_hdr og + pg_header_len og) bs ->
length hs = (27 + Z.to_nat (znth (ubytes hs) 26))%nat -> Z.of_nat (length hs) = pg_header_len og -> Z.of_nat (length bs) = pg_body_len og ->
zsum (lacing_of (ubytes hs)) <= pg_body_len og -> 0 <= pg_hdr og -> pg_hdr og + pg_header_len og + pg_body_len og <= nsy ->
In (Dsy, nsy) (rt_live RT Σ) -> Dsy <> Bd -> Dsy <> L -> Dsy <> Gv ->
8 * (os_lacing_storage os + znth (ubytes hs) 26 + 33) <= 64512 -> os_body_storage os + pg_body_len og + 1024 <= 64512 -> 0 < os_lacing_storage os -> 0 < os_body_storage os ->
In (f, k) (rt_frames RT Σ) -> f <= A -> A + 408 <= f + fs_size k - 8 -> f <= G -> G + 32 <= f + fs_size k - 8 -> (A + 408 <= G \/ G + 32 <= A) ->
Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX -> 0 <= rt_credit RT Σ ->
ART RT Σ m -> mem_inv bsegs m ->
stk bsegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK + 256 <= bv_unsigned sp ->
bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
cps bsegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc A_ogg_stream_pagein m)))
(fun c => exists (Σ' : rts RT) (Bd' L' Gv' : Z),
ASTA RT Σ' PMc (fun ms => exists m' (bodybytes' : list byte) (lws' gws' : list word),
ret_stL (fun F' fc' => F' = F /\ fc' = fc) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (wz (fst r)) m' ms
/\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
/\ rt_pres_fp (pgi_rest Bd L Gv (rt_live RT Σ)) (rt_frames RT Σ) (bv_unsigned sp) [(A, A + 408)] m m'
/\ rw_cells bsegs m' A (stream_cells Bd' L' Gv' shdr (snd r))
/\ stream_arrays m' (snd r) Bd' L' Gv' bodybytes' lws' gws') c
/\ q' = q /\ r = pagein_res os (ubytes hs) (ubytes bs)
/\ stream_live RT Σ' (snd r) Bd' L' Gv'
/\ rt_live RT Σ' = pagein_live (rt_live RT Σ) os (ubytes hs) (ubytes bs) Bd L Gv Bd' L' Gv'
/\ pagein_same os (ubytes hs) (ubytes bs) Bd L Gv Bd' L' Gv'
/\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
/\ rt_credit RT Σ' = rt_credit RT Σ /\ rt_pois RT Σ' = rt_pois RT Σ).

Definition kp (P : Prop) : Prop := P.
Ltac kp_all :=
repeat match goal with
| H : rw_cells bsegs ?m ?a ?cs |- _ => change (kp (rw_cells bsegs m a cs)) in H
| H : bytes_at bsegs ?m ?a ?bs |- _ => change (kp (bytes_at bsegs m a bs)) in H
end.
Ltac cls_live IN := right; right; left; lazymatch type of IN with In (?p, ?n) _ => exists p, n; split; [exact IN | ulq0] end.
Ltac cls_frame IN := right; right; right; left; lazymatch type of IN with In (?f, ?k) _ => exists f, k; split; [exact IN | ulq0] end.
Ltac cls_stack := left; ulq0.
Ltac tx_agree cls :=
lazymatch goal with
| |- agree_on _ ?m ?m' =>
first [ match goal with PRES : rt_pres_ex ?live ?frames ?sp ?d ?n m m' |- _ =>
apply (agree_of_pres_ex live frames sp d n m m' _ PRES); intros ?x ?Hx; cps_sizes Hx; split; [cls | ulc] end
| match goal with PRES : rt_pres_fp ?live ?frames ?sp ?W m m' |- _ =>
apply (agree_of_pres_fp live frames sp W m m' _ PRES); intros ?x ?Hx; cps_sizes Hx; split; [cls | cbn [outside]; repeat split; ulc] end
| match goal with PRES : rt_pres ?live ?frames ?sp m m' |- _ =>
apply (agree_of_pres live frames sp m m' _ PRES); intros ?x ?Hx; cps_sizes Hx; cls end ]
end.

Ltac tx H cls :=
unfold kp in H;
let m' := lazymatch goal with Hc : ASTA _ _ _ (eq (MS _ _ _ _ _ ?mm _)) _ |- _ => mm end in
lazymatch type of H with
| rw_cells bsegs ?m ?A ?cs => apply (rw_cells_agree_nw bsegs m m' A cs) in H; [ | tx_agree cls ]
| bytes_at bsegs ?m ?A ?bs => apply (bytes_at_agree bsegs m m' A bs) in H; [ | tx_agree cls ]
end.

Ltac tx_agree_ex cls sep :=
lazymatch goal with
| |- agree_on _ ?m ?m' =>
first [ match goal with PRES : rt_pres_ex ?live ?frames ?sp ?d ?n m m' |- _ =>
apply (agree_of_pres_ex live frames sp d n m m' _ PRES); let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; cps_sizes Hx; split; [cls | sep x Hx] end
| match goal with PRES : rt_pres_fp ?live ?frames ?sp ?W m m' |- _ =>
apply (agree_of_pres_fp live frames sp W m m' _ PRES); let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; cps_sizes Hx; split;
[cls | cbn [outside]; repeat split; sep x Hx] end ]
end.
Ltac txe H cls sep :=
unfold kp in H;
let m' := lazymatch goal with Hc : ASTA _ _ _ (eq (MS _ _ _ _ _ ?mm _)) _ |- _ => mm end in
lazymatch type of H with
| rw_cells bsegs ?m ?A ?cs => apply (rw_cells_agree_nw bsegs m m' A cs) in H; [ | tx_agree_ex cls sep ]
| bytes_at bsegs ?m ?A ?bs => apply (bytes_at_agree bsegs m m' A bs) in H; [ | tx_agree_ex cls sep ]
end.

Lemma stream_cells_ret_body : forall Bd L G hdr (os : stream_st bptr),
stream_cells Bd L G hdr (ret_body os)
= stream_cells_r Bd (os_body_fill (ret_body os)) (os_body_returned (ret_body os)) L G (os_lacing_fill os) (os_lacing_packet os) (os_lacing_returned os) hdr os.
Proof. intros. unfold ret_body. destruct (negb (os_body_returned os =? 0)); reflexivity. Qed.

Lemma live_apart2 : forall (Σ : rts RT) (m : mem) p n p2 n2, ART RT Σ m -> In (p, n) (rt_live RT Σ) -> In (p2, n2) (rt_live RT Σ) -> p2 <> p ->
p + n <= p2 \/ p2 + n2 <= p.
Proof using AF.
intros Σ m p n p2 n2 ART0 I1 I2 NE. apply (live_remove_apart RT AF Σ m p n p2 n2 ART0 I1). apply live_remove_keep; [exact I2| exact NE].
Qed.

Lemma pgi_phaseA : forall (Σ : rts RT) PMc (ra gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (A G Dsy nsy Bd L Gv f lo usp : Z) (k : nat) (og : page) (os : stream_st bptr) (shdr hs bs bodybytes : list byte) (lws gws : list word),
fdfs_only PMc -> mat_stable PMc ->
rw_cells bsegs m A (stream_cells Bd L Gv shdr os) -> length shdr = 284%nat -> 0 < A ->
u8arr bsegs m Bd bodybytes -> Z.of_nat (length bodybytes) = os_body_storage os -> body_pre (os_body os) bodybytes ->
rw_cells bsegs m L [CB (length (u32s lws)) (u32s lws)] -> Z.of_nat (length (u32s lws)) = 4 * os_lacing_storage os ->
rw_cells bsegs m Gv [CB (length (u64s gws)) (u64s gws)] -> Z.of_nat (length (u64s gws)) = 8 * os_lacing_storage os ->
stream_fields_ok os -> zlength (os_body os) = os_body_fill os -> 0 <= os_body_returned os <= os_body_fill os -> os_body_storage os <= 64512 ->
stream_live RT Σ os Bd L Gv ->
rw_cells bsegs m G (page_cells Dsy og) -> 0 < G ->
bytes_at bsegs m (Dsy + pg_hdr og) hs -> bytes_at bsegs m (Dsy + pg_hdr og + pg_header_len og) bs ->
(27 <= length hs)%nat -> Z.of_nat (length hs) = pg_header_len og -> Z.of_nat (length bs) = pg_body_len og ->
0 <= pg_hdr og -> pg_hdr og + pg_header_len og + pg_body_len og <= nsy -> In (Dsy, nsy) (rt_live RT Σ) -> Dsy <> Bd ->
In (f, k) (rt_frames RT Σ) -> f <= A -> A + 408 <= f + fs_size k - 8 -> f <= G -> G + 32 <= f + fs_size k - 8 -> (A + 408 <= G \/ G + 32 <= A) ->
(forall a, aclient (pgi_rest Bd L Gv (rt_live RT Σ)) (rt_frames RT Σ) usp a -> ~ (Bd <= a < Bd + os_body_storage os)) ->
ART RT Σ m -> mem_inv bsegs m ->
stk bsegs m lo usp -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK + 256 <= usp -> usp + 16 <= USTACK_TOP -> usp mod 16 = 0 ->
forall T c,
ASTA RT Σ PMc (eq (MS (mkR ra (Z_to_bv 64 usp) gp (Z_to_bv 64 0x638c98) t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 G) a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 A_ogg_stream_pagein) fc None m (seg_rom bsegs))) c ->
(forall c1 (m1 : mem) (bodybytes1 j0 : list byte) (v25 v22 : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
ASTA RT Σ PMc (eq (MS (pgi_regs x1 usp gp (Z_to_bv 64 0x638c98) x5 x6 x7 A (Z_to_bv 64 (os_lacing_returned os)) x10 x11 x12 x13 x14 x15 x16 x17
(pg_body_len og) (Dsy + pg_hdr og + pg_header_len og) (Dsy + pg_hdr og) (Z_to_bv 64 v22) hs (Z_to_bv 64 v25) x28 x29 x30 x31)
F (Z_to_bv 64 0xc1b20) fc None m1 (seg_rom bsegs))) c1 ->
ART RT Σ m1 -> mem_inv bsegs m1 -> stk bsegs m1 lo (usp + -144) ->
rw_cells bsegs m1 (usp + -144) (pgi_frame ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j0 hs) ->
rw_cells bsegs m1 A (stream_cells Bd L Gv shdr (ret_body os)) ->
u8arr bsegs m1 Bd bodybytes1 -> Z.of_nat (length bodybytes1) = os_body_storage os -> body_pre (os_body (ret_body os)) bodybytes1 ->
rw_cells bsegs m1 L [CB (length (u32s lws)) (u32s lws)] -> rw_cells bsegs m1 Gv [CB (length (u64s gws)) (u64s gws)] ->
rw_cells bsegs m1 G (page_cells Dsy og) ->
bytes_at bsegs m1 (Dsy + pg_hdr og) hs -> bytes_at bsegs m1 (Dsy + pg_hdr og + pg_header_len og) bs ->
0 <= v25 < 2^64 -> 0 <= v22 < 2^64 -> Z_to_bv 64 (Z.lor v25 v22) = Z_to_bv 64 (ogg_page_serialno (ubytes hs)) ->
rt_pres_fp (pgi_rest Bd L Gv (rt_live RT Σ)) (rt_frames RT Σ) usp [(A, A + 408)] m m1 ->
realizes bsegs c1 T) ->
realizes bsegs c T.
Proof using AF MMOV.
intros Σ PMc ra gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m A G Dsy nsy Bd L Gv f lo usp k og os shdr hs bs bodybytes lws gws
FDO MST OS HL A0 BODY BLEN BPRE LAC LBL GRA LBG FOK BFILL BRF BSM SLV OG G0 HS BS LENH HLEN BSLEN PG0 PGIN INSY NSB INF FA1 FA2 FG1 FG2 SEP_AG NAB ART0 MI0 ST0 LOW LOR SPT SPA T c Hc Hk.
destruct (frame_below_lo RT AF Σ m f k lo ART0 INF LOW) as (BF1 & BF2 & BF3).
assert (FSZ : 0 <= fs_size k) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
destruct SLV as (INB & INL & ING & NBL & NBG & NLG).
destruct (live_below_lo RT AF Σ m Bd _ lo ART0 INB LOW) as (B0 & B1 & _).
destruct (live_below_lo RT AF Σ m L _ lo ART0 INL LOW) as (L0 & L1 & _).
destruct (live_below_lo RT AF Σ m Gv _ lo ART0 ING LOW) as (G0' & G1 & _).
destruct (live_below_lo RT AF Σ m Dsy _ lo ART0 INSY LOW) as (S0 & S1 & _).
pose proof FOK as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12). unfold int31 in *.
set (LV := pgi_rest Bd L Gv (rt_live RT Σ)) in *.
pose proof (pres_fp_refl LV (rt_frames RT Σ) usp [(A, A + 408)] m) as PF.
assert (SUBLV : forall e, In e LV -> In e (rt_live RT Σ)) by (intros e He; exact (pgi_rest_sub _ _ _ _ _ He)).
assert (SPL : forall a, aclient LV (rt_frames RT Σ) usp a -> usp <= a \/ a < rt_sp0 RT Σ - STACK_WIN).
{ intros a Ha. apply (aclient_split RT AF Σ m usp a ART0). apply (aclient_mono _ _ _ _ _ _ _ Ha); [exact SUBLV| auto| apply Z.le_refl]. }
pose proof BPRE as (BP1 & BP2). unfold zlength in BFILL.
assert (TOPH : Dsy + pg_hdr og + Z.of_nat (length hs) < 2^63) by (clear - S1 PGIN HLEN BSLEN LOR SPT; unfold RT_STACK, USTACK_TOP in *; lia).
assert (AT : A + 408 < 2^63) by (clear - FA2 BF1 LOR SPT FSZ; unfold RT_STACK, USTACK_TOP in *; lia).
assert (BT : Bd + os_body_storage os < 2^63) by (clear - B1 LOR SPT; unfold RT_STACK, USTACK_TOP in *; lia).
destruct (frame_live_apart RT AF Σ m f k Bd _ ART0 INF INB) as (FLB & _).
destruct (frame_live_apart RT AF Σ m f k L _ ART0 INF INL) as (FLL & _).
destruct (frame_live_apart RT AF Σ m f k Gv _ ART0 INF ING) as (FLG & _).
destruct (frame_live_apart RT AF Σ m f k Dsy _ ART0 INF INSY) as (FLS & _).
assert (SEP_GB : Bd + os_body_storage os <= G \/ G + 32 <= Bd) by (clear - FLB FG1 FG2; lia).
pose proof (live_apart2 Σ m Bd _ L _ ART0 INB INL ltac:(congruence)) as SEP_BL.
pose proof (live_apart2 Σ m Bd _ Gv _ ART0 INB ING ltac:(congruence)) as SEP_BG.
pose proof (live_apart2 Σ m Bd _ Dsy _ ART0 INB INSY NSB) as SEP_BS.
assert (SEP_AB : Bd + os_body_storage os <= A \/ A + 408 <= Bd) by (clear - FLB FA1 FA2; lia).
assert (SEP_AL : L + 4 * os_lacing_storage os <= A \/ A + 408 <= L) by (clear - FLL FA1 FA2; lia).
assert (SEP_AGv : Gv + 8 * os_lacing_storage os <= A \/ A + 408 <= Gv) by (clear - FLG FA1 FA2; lia).
assert (SEP_AS : Dsy + nsy <= A \/ A + 408 <= Dsy) by (clear - FLS FA1 FA2; lia).
clear FLB FLL FLG FLS.
rewrite stream_cells_r_eq in OS. unfold stream_cells_r in OS. unfold page_cells in OG.
cps_norm. cps_hide.
cps_seg (pgi_w0 A G Dsy Bd L Gv usp lo og shdr hs os).
destruct POST as (m1 & j0 & v25 & v22 & x1 & x5 & x6 & x7 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & -> & MU1 & WM1 & MI1 & ST1 & FR1 & V25 & V22 & ESER).
apply u8arr_rw_CB in BODY. unfold pgi_frame in FR1.
cps_seg_post.
destruct (Z.eq_dec (os_body_returned os) 0) as [BRZ|BRNZ].
-
assert (ERB : ret_body os = os) by (unfold ret_body; rewrite BRZ; reflexivity).
rewrite BRZ in Hc0.
cps_seg (pgi_b0 A usp (pg_body_len og) (Dsy + pg_hdr og + pg_header_len og) (Dsy + pg_hdr og) hs).
lazymatch type of POST with ?x = _ => subst x end.
eapply (Hk _ m1 bodybytes j0 v25 v22); try eassumption.
+ rewrite ERB, stream_cells_r_eq. exact OS.
+ apply u8arr_rw_CB. exact BODY.
+ rewrite ERB. exact BPRE.
- assert (ERB : ret_body os = set_body os (ztake (os_body_fill os - os_body_returned os) (zdrop (os_body_returned os) (os_body os)))
(os_body_storage os) (os_body_fill os - os_body_returned os) 0).
{ unfold ret_body. replace (os_body_returned os =? 0) with false by (symmetry; apply Z.eqb_neq; exact BRNZ). reflexivity. }
destruct (Z.eq_dec (os_body_fill os) (os_body_returned os)) as [BFE|BFNE].
+
cps_seg (pgi_b1 A Bd (os_body_fill os) (os_body_returned os) L Gv (os_lacing_fill os) (os_lacing_packet os) (os_lacing_returned os) usp
(pg_body_len og) (Dsy + pg_hdr og + pg_header_len og) (Dsy + pg_hdr og) shdr hs os).
destruct POST as (m2 & x12' & x13' & -> & MU2 & WM2 & MI2 & OS2). unfold stream_cells_r in OS2.
clear OS. cps_seg_post.
eapply (Hk _ m2 bodybytes j0 v25 v22); try eassumption.
* rewrite stream_cells_ret_body, ERB. cbn [set_body os_body_fill os_body_returned]. exact OS2.
* apply u8arr_rw_CB. exact BODY.
* rewrite ERB. cbn [set_body os_body]. unfold body_pre, ztake. replace (Z.to_nat (os_body_fill os - os_body_returned os)) with 0%nat by lia.
cbn [firstn length]. split; [reflexivity| lia].
+
set (nr := Z.to_nat (os_body_returned os)). set (nf := Z.to_nat (os_body_fill os - os_body_returned os)).
destruct (compact_prefix (os_body os) bodybytes nr nf BP1 ltac:(unfold nr, nf; lia) BP2) as (CP1 & CP2).
set (b1 := firstn nf bodybytes). set (b2 := skipn nf bodybytes). set (bsrc := firstn nf (skipn nr bodybytes)).
assert (Lb1 : Z.of_nat (length b1) = os_body_fill os - os_body_returned os) by (unfold b1; rewrite firstn_length_le by (unfold nf, nr in *; lia); unfold nf; lia).
assert (LEQ : length bsrc = length b1) by (unfold bsrc, b1; rewrite !firstn_length_le by (rewrite ?length_skipn; unfold nf, nr in *; lia); reflexivity).
assert (Lbs : Z.of_nat (length bsrc) = os_body_fill os - os_body_returned os) by (rewrite LEQ; exact Lb1).
assert (EB : bodybytes = b1 ++ b2) by (symmetry; apply firstn_skipn).
assert (Lb2 : Z.of_nat (length b2) = os_body_storage os - (os_body_fill os - os_body_returned os)) by (unfold b2; rewrite length_skipn; unfold nf, nr in *; lia).
apply u8arr_rw_CB in BODY.
pose proof (bytes_at_sub m1 Bd bodybytes nr nf (proj1 BODY) ltac:(unfold nf, nr in *; lia)) as SRC. fold bsrc in SRC.
replace (Bd + Z.of_nat nr) with (Bd + os_body_returned os) in SRC by (unfold nr; lia).
rewrite EB in BODY. apply u8arr_app in BODY. destruct BODY as (P1 & P2). apply u8arr_rw_CB in P1, P2.
assert (FST : os_body_fill os <= os_body_storage os) by (clear - BFILL BP2 BLEN; lia).
cps_seg (pgi_b2 A Bd (os_body_fill os) (os_body_returned os) L Gv (os_lacing_fill os) (os_lacing_packet os) (os_lacing_returned os) usp
(pg_body_len og) (Dsy + pg_hdr og + pg_header_len og) (Dsy + pg_hdr og) shdr hs os).
destruct POST as (m2 & -> & MU2 & WM2 & MI2 & OS2). unfold stream_cells_r in OS2.
clear OS. cps_seg_post.
assert (NAB' : forall a, aclient LV (rt_frames RT Σ) usp a -> ~ (Bd <= a < Bd + Z.of_nat (length bsrc))).
{ intros a Ha. specialize (NAB a Ha). clear - NAB Lbs FST BRF. lia. }
pose proof (proj2 P1) as WR1. cbn [cells_size csize Nat.add] in WR1. rewrite Nat.add_0_r, <- LEQ in WR1.
assert (EU : bv_unsigned (Z_to_bv 64 (usp + -144)) = usp + -144) by (apply unsigned_lit; ulc).
lazymatch goal with H : ASTA _ _ _ (eq _) _ |- _ => unfold pgi_regs in H; rewrite <- Lbs in H end.
kp_all.
cps_rt (MMOV Σ PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 Bd (Bd + os_body_returned os) bsrc lo).
all: [> .. | ].
all: lazymatch goal with
| |- call_ok _ _ _ _ _ => cps_callok
| |- checked_src _ _ _ _ _ _ _ => idtac
| |- checked_dst _ _ _ _ _ _ => idtac
| |- bytes_at _ _ _ _ => exact SRC
| |- _ => try (clear - B0 B1 BRF F1 F2 LOR SPT Lbs FST BSM; lia)
end.
{ apply (live_checked_src RT AF Σ m2 _ lo Bd (os_body_storage os)); [eassumption| exact INB| lia| lia| exact B1]. }
{ apply (live_checked_dst RT AF Σ m2 _ Bd (os_body_storage os)); [eassumption| exact INB| lia| lia| exact WR1]. }
intros kc2 Hc2. unfold icpt_postF in Hc2.
cps_unpack Hc2 as (m3 & RS3 & (ART3 & MI3 & WM3 & ST3) & PRES3 & BY3).
pose proof (ogg_bytes_piece m2 m3 Bd bsrc WR1 WM3 BY3) as P1'. clear BY3 P1 SRC.
tx P2 ltac:(cls_live INB). tx OS2 ltac:(cls_frame INF). tx FR1 ltac:(cls_stack). tx LAC ltac:(cls_live INL). tx GRA ltac:(cls_live ING).
tx OG ltac:(cls_frame INF). tx HS ltac:(cls_live INSY). tx BS ltac:(cls_live INSY).
cps_seg (pgi_b3 A Bd (os_body_fill os - os_body_returned os) (os_body_returned os) L Gv (os_lacing_fill os) (os_lacing_packet os) (os_lacing_returned os) usp
(pg_body_len og) (Dsy + pg_hdr og + pg_header_len og) (Dsy + pg_hdr og) shdr hs os).
destruct POST as (m4 & -> & MU4 & WM4 & MI4 & OS4). unfold stream_cells_r in OS4.
clear OS2. cps_seg_post.
eapply (Hk _ m4 (bsrc ++ b2) j0 v25 v22); try eassumption.
* rewrite stream_cells_ret_body, ERB. cbn [set_body os_body_fill os_body_returned]. exact OS4.
* apply u8arr_app. split; [apply u8arr_rw_CB; exact P1'|]. rewrite LEQ. apply u8arr_rw_CB. exact P2.
* rewrite length_app. clear - Lbs Lb1 LEQ EB BLEN. rewrite EB, length_app in BLEN. lia.
* rewrite ERB. cbn [set_body os_body]. unfold body_pre, ztake, zdrop. fold nr nf. exact (conj CP1 CP2).
Qed.

Lemma stream_cells_ret_lacing : forall Bd L G hdr (os : stream_st bptr),
stream_cells Bd L G hdr (ret_lacing os)
= stream_cells_r Bd (os_body_fill os) (os_body_returned os) L G (os_lacing_fill (ret_lacing os)) (os_lacing_packet (ret_lacing os)) (os_lacing_returned (ret_lacing os)) hdr os.
Proof. intros. unfold ret_lacing. destruct (negb (os_lacing_returned os =? 0)); reflexivity. Qed.

Lemma pgi_phaseB : forall (Σ : rts RT) PMc (x1 gp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
F fc (m0 m : mem) (A G Dsy nsy Bd L Gv f lo usp v25 v22 : Z) (k : nat) (og : page) (os : stream_st bptr) (shdr hs bs bodybytes j0 : list byte) (lws gws : list word),
fdfs_only PMc -> mat_stable PMc ->
rw_cells bsegs m A (stream_cells Bd L Gv shdr os) -> length shdr = 284%nat -> 0 < A ->
rw_cells bsegs m Bd [CB (length bodybytes) bodybytes] -> Z.of_nat (length bodybytes) = os_body_storage os ->
u32arr bsegs m L lws -> wpre (os_lacing os) lws -> Z.of_nat (length lws) = os_lacing_storage os ->
u64arr bsegs m Gv gws -> Z.of_nat (length gws) = os_lacing_storage os ->
stream_fields_ok os -> zlength (os_lacing os) = os_lacing_fill os ->
0 <= os_lacing_returned os <= os_lacing_packet os -> os_lacing_packet os <= os_lacing_fill os -> 8 * os_lacing_storage os <= 64512 ->
stream_live RT Σ os Bd L Gv ->
rw_cells bsegs m (usp + -144) (pgi_frame ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j0 hs) ->
rw_cells bsegs m G (page_cells Dsy og) -> 0 < G ->
bytes_at bsegs m (Dsy + pg_hdr og) hs -> bytes_at bsegs m (Dsy + pg_hdr og + pg_header_len og) bs ->
(27 <= length hs)%nat -> Z.of_nat (length hs) = pg_header_len og -> Z.of_nat (length bs) = pg_body_len og ->
0 <= pg_hdr og -> pg_hdr og + pg_header_len og + pg_body_len og <= nsy -> In (Dsy, nsy) (rt_live RT Σ) -> Dsy <> L -> Dsy <> Gv ->
In (f, k) (rt_frames RT Σ) -> f <= A -> A + 408 <= f + fs_size k - 8 -> f <= G -> G + 32 <= f + fs_size k - 8 -> (A + 408 <= G \/ G + 32 <= A) ->
(forall a, aclient (pgi_rest Bd L Gv (rt_live RT Σ)) (rt_frames RT Σ) usp a -> ~ (L <= a < L + 4 * os_lacing_storage os)) ->
(forall a, aclient (pgi_rest Bd L Gv (rt_live RT Σ)) (rt_frames RT Σ) usp a -> ~ (Gv <= a < Gv + 8 * os_lacing_storage os)) ->
0 <= v25 < 2^64 -> 0 <= v22 < 2^64 -> Z_to_bv 64 (Z.lor v25 v22) = Z_to_bv 64 (ogg_page_serialno (ubytes hs)) ->
ART RT Σ m -> mem_inv bsegs m ->
stk bsegs m lo (usp + -144) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK + 256 <= usp -> usp + 16 <= USTACK_TOP -> usp mod 16 = 0 ->
rt_pres_fp (pgi_rest Bd L Gv (rt_live RT Σ)) (rt_frames RT Σ) usp [(A, A + 408)] m0 m ->
forall T c,
ASTA RT Σ PMc (eq (MS (pgi_regs x1 usp gp (Z_to_bv 64 0x638c98) x5 x6 x7 A (Z_to_bv 64 (os_lacing_returned os)) x10 x11 x12 x13 x14 x15 x16 x17
(pg_body_len og) (Dsy + pg_hdr og + pg_header_len og) (Dsy + pg_hdr og) (Z_to_bv 64 v22) hs (Z_to_bv 64 v25) x28 x29 x30 x31)
F (Z_to_bv 64 0xc1b20) fc None m (seg_rom bsegs))) c ->
(forall c1 (m1 : mem) (lws1 gws1 : list word) (y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
ASTA RT Σ PMc (eq (MS (pgi_regs y1 usp gp (Z_to_bv 64 0x638c98) y5 y6 y7 A y9 y10 y11 y12 y13 y14 y15 y16 y17
(pg_body_len og) (Dsy + pg_hdr og + pg_header_len og) (Dsy + pg_hdr og) (Z_to_bv 64 v22) hs
(Z_to_bv 64 (ogg_page_serialno (ubytes hs))) y28 y29 y30 y31)
F (Z_to_bv 64 0xc1b84) fc None m1 (seg_rom bsegs))) c1 ->
ART RT Σ m1 -> mem_inv bsegs m1 -> stk bsegs m1 lo (usp + -144) ->
rw_cells bsegs m1 (usp + -144) (pgi_frame ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j0 hs) ->
rw_cells bsegs m1 A (stream_cells Bd L Gv shdr (ret_lacing os)) ->
rw_cells bsegs m1 Bd [CB (length bodybytes) bodybytes] ->
u32arr bsegs m1 L lws1 -> wpre (os_lacing (ret_lacing os)) lws1 -> Z.of_nat (length lws1) = os_lacing_storage os ->
u64arr bsegs m1 Gv gws1 -> Z.of_nat (length gws1) = os_lacing_storage os ->
rw_cells bsegs m1 G (page_cells Dsy og) ->
bytes_at bsegs m1 (Dsy + pg_hdr og) hs -> bytes_at bsegs m1 (Dsy + pg_hdr og + pg_header_len og) bs ->
rt_pres_fp (pgi_rest Bd L Gv (rt_live RT Σ)) (rt_frames RT Σ) usp [(A, A + 408)] m0 m1 ->
realizes bsegs c1 T) ->
realizes bsegs c T.
Proof using AF MMOV.
intros Σ PMc x1 gp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 m A G Dsy nsy Bd L Gv f lo usp v25 v22 k og os
shdr hs bs bodybytes j0 lws gws FDO MST OS HL A0 BODY BLEN LAC LPRE LLEN GRA GLEN FOK LFILL LRP LPF LSM SLV FR OG G0 HS BS LENH HLEN BSLEN PG0 PGIN INSY NSL NSG
INF FA1 FA2 FG1 FG2 SEP_AG NAL NAG V25 V22 ESER ART0 MI0 ST0 LOW LOR SPT SPA PF T c Hc Hk.
destruct (frame_below_lo RT AF Σ m f k lo ART0 INF LOW) as (BF1 & BF2 & BF3).
assert (FSZ : 0 <= fs_size k) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
destruct SLV as (INB & INL & ING & NBL & NBG & NLG).
destruct (live_below_lo RT AF Σ m Bd _ lo ART0 INB LOW) as (B0 & B1 & _).
destruct (live_below_lo RT AF Σ m L _ lo ART0 INL LOW) as (L0 & L1 & _).
destruct (live_below_lo RT AF Σ m Gv _ lo ART0 ING LOW) as (G0' & G1 & _).
destruct (live_below_lo RT AF Σ m Dsy _ lo ART0 INSY LOW) as (S0 & S1 & _).
pose proof FOK as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12). unfold int31 in *.
set (LV := pgi_rest Bd L Gv (rt_live RT Σ)) in *.
assert (SUBLV : forall e, In e LV -> In e (rt_live RT Σ)) by (intros e He; exact (pgi_rest_sub _ _ _ _ _ He)).
assert (SPL : forall a, aclient LV (rt_frames RT Σ) usp a -> usp <= a \/ a < rt_sp0 RT Σ - STACK_WIN).
{ intros a Ha. apply (aclient_split RT AF Σ m usp a ART0). apply (aclient_mono _ _ _ _ _ _ _ Ha); [exact SUBLV| auto| apply Z.le_refl]. }
pose proof (wpre_length _ _ LPRE) as LL. unfold zlength in LFILL.
assert (LFS : os_lacing_fill os <= os_lacing_storage os) by (clear - LL LFILL LLEN; lia).
assert (AT : A + 408 < 2^63) by (clear - FA2 BF1 LOR SPT FSZ; unfold RT_STACK, USTACK_TOP in *; lia).
destruct (frame_live_apart RT AF Σ m f k Bd _ ART0 INF INB) as (FLB & _).
destruct (frame_live_apart RT AF Σ m f k L _ ART0 INF INL) as (FLL & _).
destruct (frame_live_apart RT AF Σ m f k Gv _ ART0 INF ING) as (FLG & _).
destruct (frame_live_apart RT AF Σ m f k Dsy _ ART0 INF INSY) as (FLS & _).
assert (SEP_GL : L + 4 * os_lacing_storage os <= G \/ G + 32 <= L) by (clear - FLL FG1 FG2; lia).
assert (SEP_GG : Gv + 8 * os_lacing_storage os <= G \/ G + 32 <= Gv) by (clear - FLG FG1 FG2; lia).
pose proof (live_apart2 Σ m L _ Bd _ ART0 INL INB ltac:(congruence)) as SEP_LB.
pose proof (live_apart2 Σ m L _ Gv _ ART0 INL ING ltac:(congruence)) as SEP_LG.
pose proof (live_apart2 Σ m L _ Dsy _ ART0 INL INSY NSL) as SEP_LS.
pose proof (live_apart2 Σ m Gv _ Bd _ ART0 ING INB ltac:(congruence)) as SEP_GvB.
pose proof (live_apart2 Σ m Gv _ Dsy _ ART0 ING INSY NSG) as SEP_GvS.
assert (SEP_AB : Bd + os_body_storage os <= A \/ A + 408 <= Bd) by (clear - FLB FA1 FA2; lia).
assert (SEP_AL : L + 4 * os_lacing_storage os <= A \/ A + 408 <= L) by (clear - FLL FA1 FA2; lia).
assert (SEP_AGv : Gv + 8 * os_lacing_storage os <= A \/ A + 408 <= Gv) by (clear - FLG FA1 FA2; lia).
assert (SEP_AS : Dsy + nsy <= A \/ A + 408 <= Dsy) by (clear - FLS FA1 FA2; lia).
clear FLB FLL FLG FLS.
rewrite stream_cells_r_eq in OS. unfold stream_cells_r in OS. unfold page_cells in OG. unfold pgi_frame in FR.
destruct (Z.eq_dec (os_lacing_returned os) 0) as [LRZ|LRNZ].
-
assert (ERL : ret_lacing os = os) by (unfold ret_lacing; rewrite LRZ; reflexivity).
rewrite LRZ in Hc.
cps_norm. cps_hide.
cps_seg (pgi_l0 A usp (pg_body_len og) (Dsy + pg_hdr og + pg_header_len og) (Dsy + pg_hdr og) v25 v22 hs).
lazymatch type of POST with ?x = _ => subst x end.
eapply (Hk _ m lws gws); try eassumption.
+ rewrite ERL, stream_cells_r_eq. exact OS.
+ rewrite ERL. exact LPRE.
- assert (ERL : ret_lacing os = set_lacing os (zdrop (os_lacing_returned os) (os_lacing os)) (zdrop (os_lacing_returned os) (os_granules os)) (os_lacing_storage os)
(os_lacing_fill os - os_lacing_returned os) (os_lacing_packet os - os_lacing_returned os) 0).
{ unfold ret_lacing. replace (os_lacing_returned os =? 0) with false by (symmetry; apply Z.eqb_neq; exact LRNZ). reflexivity. }
assert (LBL : Z.of_nat (length (u32s lws)) = 4 * os_lacing_storage os) by (rewrite u32s_length; lia).
assert (LBG : Z.of_nat (length (u64s gws)) = 8 * os_lacing_storage os) by (rewrite u64s_length; lia).
destruct (Z.eq_dec (os_lacing_fill os) (os_lacing_returned os)) as [LFE|LFNE].
+
apply u32arr_u8, u8arr_rw_CB in LAC. apply u64arr_u8, u8arr_rw_CB in GRA.
cps_norm. cps_hide.
cps_seg (pgi_l1 A Bd (os_body_fill os) (os_body_returned os) L Gv (os_lacing_fill os) (os_lacing_packet os) (os_lacing_returned os) usp
(pg_body_len og) (Dsy + pg_hdr og + pg_header_len og) (Dsy + pg_hdr og) v25 v22 shdr hs os).
destruct POST as (m2 & x10' & x11' & -> & MU2 & WM2 & MI2 & OS2). unfold stream_cells_r in OS2.
clear OS. cps_seg_post.
apply u8arr_rw_CB, u8_u32arr in LAC. apply u8arr_rw_CB, u8_u64arr in GRA.
eapply (Hk _ m2 lws gws); try eassumption.
* rewrite stream_cells_ret_lacing, ERL. cbn [set_lacing os_lacing_fill os_lacing_packet os_lacing_returned]. exact OS2.
* rewrite ERL. cbn [set_lacing os_lacing]. unfold wpre, zdrop. rewrite skipn_all2 by lia. cbn. split; [reflexivity| lia].
+
set (nr := Z.to_nat (os_lacing_returned os)). set (nf := Z.to_nat (os_lacing_fill os - os_lacing_returned os)).
assert (NRF : (nr + nf <= length lws)%nat) by (unfold nr, nf; lia).

set (lb := u32s lws) in *.
set (l1 := firstn (4 * nf) lb). set (l2 := skipn (4 * nf) lb). set (lsrc := firstn (4 * nf) (skipn (4 * nr) lb)).
assert (LBn : length lb = (4 * length lws)%nat) by (unfold lb; apply u32s_length).
assert (Ll1 : Z.of_nat (length l1) = 4 * (os_lacing_fill os - os_lacing_returned os)) by (unfold l1; rewrite firstn_length_le by lia; unfold nf; lia).
assert (LEQ : length lsrc = length l1) by (unfold lsrc, l1; rewrite !firstn_length_le by (rewrite ?length_skipn; lia); reflexivity).
assert (Lls : Z.of_nat (length lsrc) = 4 * (os_lacing_fill os - os_lacing_returned os)) by (rewrite LEQ; exact Ll1).
assert (Ll2 : Z.of_nat (length l2) = 4 * os_lacing_storage os - 4 * (os_lacing_fill os - os_lacing_returned os)) by (unfold l2; rewrite length_skipn; unfold nf in *; lia).
assert (EL : lb = l1 ++ l2) by (symmetry; apply firstn_skipn).
apply u32arr_u8 in LAC. fold lb in LAC.
pose proof (bytes_at_sub m L lb (4 * nr) (4 * nf) (proj1 LAC) ltac:(lia)) as LSRC. fold lsrc in LSRC.
replace (L + Z.of_nat (4 * nr)) with (L + 4 * os_lacing_returned os) in LSRC by (unfold nr; lia).
rewrite EL in LAC. apply u8arr_app in LAC. destruct LAC as (P1 & P2). apply u8arr_rw_CB in P1, P2.

set (gb := u64s gws) in *.
set (g1 := firstn (8 * nf) gb). set (g2 := skipn (8 * nf) gb). set (gsrc := firstn (8 * nf) (skipn (8 * nr) gb)).
assert (GBn : length gb = (8 * length gws)%nat) by (unfold gb; apply u64s_length).
assert (Lg1 : Z.of_nat (length g1) = 8 * (os_lacing_fill os - os_lacing_returned os)) by (unfold g1; rewrite firstn_length_le by lia; unfold nf; lia).
assert (GEQ : length gsrc = length g1) by (unfold gsrc, g1; rewrite !firstn_length_le by (rewrite ?length_skipn; lia); reflexivity).
assert (Lgs : Z.of_nat (length gsrc) = 8 * (os_lacing_fill os - os_lacing_returned os)) by (rewrite GEQ; exact Lg1).
assert (Lg2 : Z.of_nat (length g2) = 8 * os_lacing_storage os - 8 * (os_lacing_fill os - os_lacing_returned os)) by (unfold g2; rewrite length_skipn; unfold nf in *; lia).
assert (EG : gb = g1 ++ g2) by (symmetry; apply firstn_skipn).
apply u64arr_u8 in GRA. fold gb in GRA.
pose proof (bytes_at_sub m Gv gb (8 * nr) (8 * nf) (proj1 GRA) ltac:(lia)) as GSRC. fold gsrc in GSRC.
replace (Gv + Z.of_nat (8 * nr)) with (Gv + 8 * os_lacing_returned os) in GSRC by (unfold nr; lia).
rewrite EG in GRA. apply u8arr_app in GRA. destruct GRA as (Q1 & Q2). apply u8arr_rw_CB in Q1, Q2.
assert (EDl2 : l2 = skipn (4 * nf) lb) by reflexivity. assert (EDls : lsrc = firstn (4 * nf) (skipn (4 * nr) lb)) by reflexivity.
assert (EDg2 : g2 = skipn (8 * nf) gb) by reflexivity. assert (EDgs : gsrc = firstn (8 * nf) (skipn (8 * nr) gb)) by reflexivity.
clearbody l1 l2 lsrc g1 g2 gsrc.
assert (NAL' : forall a, aclient LV (rt_frames RT Σ) usp a -> ~ (L <= a < L + Z.of_nat (length lsrc))).
{ intros a Ha. specialize (NAL a Ha). clear - NAL Lls LL LFILL LLEN LRP. lia. }
assert (NAG' : forall a, aclient LV (rt_frames RT Σ) usp a -> ~ (Gv <= a < Gv + Z.of_nat (length gsrc))).
{ intros a Ha. specialize (NAG a Ha). clear - NAG Lgs LL LFILL LLEN LRP. lia. }
pose proof (proj2 P1) as WRL. cbn [cells_size csize Nat.add] in WRL. rewrite Nat.add_0_r, <- LEQ in WRL.
pose proof (proj2 Q1) as WRG. cbn [cells_size csize Nat.add] in WRG. rewrite Nat.add_0_r, <- GEQ in WRG.
assert (EU : bv_unsigned (Z_to_bv 64 (usp + -144)) = usp + -144) by (apply unsigned_lit; clear - LOR SPT BF3; unfold RT_STACK, USTACK_TOP, SH_HI in *; lia).
cps_norm. cps_hide.
cps_seg (pgi_l2 A Bd (os_body_fill os) (os_body_returned os) L Gv (os_lacing_fill os) (os_lacing_packet os) (os_lacing_returned os) usp
(pg_body_len og) (Dsy + pg_hdr og + pg_header_len og) (Dsy + pg_hdr og) v25 v22 shdr hs os).
1: { clear - L1 LL LFILL LLEN LOR SPT. lia. }
lazymatch type of POST with ?x = _ => subst x end.

lazymatch goal with H : ASTA _ _ _ (eq _) _ |- _ => unfold pgi_regs in H; rewrite <- Lls in H end.
kp_all.
cps_rt (MMOV Σ PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m L (L + 4 * os_lacing_returned os) lsrc lo).
all: [> .. | ].
all: lazymatch goal with
| |- call_ok _ _ _ _ _ => cps_callok
| |- checked_src _ _ _ _ _ _ _ => idtac
| |- checked_dst _ _ _ _ _ _ => idtac
| |- bytes_at _ _ _ _ => exact LSRC
| |- _ => try (clear - L0 L1 LRP LPF F4 F5 LOR SPT Lls LFS LSM; lia)
end.
{ apply (live_checked_src RT AF Σ m _ lo L (4 * os_lacing_storage os)); [eassumption| exact INL| lia| lia| exact L1]. }
{ apply (live_checked_dst RT AF Σ m _ L (4 * os_lacing_storage os)); [eassumption| exact INL| lia| lia| exact WRL]. }
intros kc2 Hc2. unfold icpt_postF in Hc2.
cps_unpack Hc2 as (m3 & RS3 & (ART3 & MI3 & WM3 & ST3) & PRES3 & BY3).
pose proof (ogg_bytes_piece m m3 L lsrc WRL WM3 BY3) as P1'. clear BY3 P1 LSRC.
tx P2 ltac:(cls_live INL). tx Q1 ltac:(cls_live ING). tx Q2 ltac:(cls_live ING). tx GSRC ltac:(cls_live ING).
tx OS ltac:(cls_frame INF). tx FR ltac:(cls_stack). tx BODY ltac:(cls_live INB).
tx OG ltac:(cls_frame INF). tx HS ltac:(cls_live INSY). tx BS ltac:(cls_live INSY).

cps_seg (pgi_l3 A Bd (os_body_fill os) (os_body_returned os) L Gv (os_lacing_fill os) (os_lacing_packet os) (os_lacing_returned os) usp
(pg_body_len og) (Dsy + pg_hdr og + pg_header_len og) (Dsy + pg_hdr og) shdr hs os).
1: { clear - G1 LFS LOR SPT. lia. }
lazymatch type of POST with ?x = _ => subst x end.
lazymatch goal with H : ASTA _ _ _ (eq _) _ |- _ => unfold pgi_regs in H; rewrite <- Lgs in H end.
pose proof (wr_at_transport bsegs m m3 Gv _ WRG WM3) as WRG3.
kp_all.
cps_rt (MMOV Σ PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 Gv (Gv + 8 * os_lacing_returned os) gsrc lo).
all: [> .. | ].
all: lazymatch goal with
| |- call_ok _ _ _ _ _ => cps_callok
| |- checked_src _ _ _ _ _ _ _ => idtac
| |- checked_dst _ _ _ _ _ _ => idtac
| |- bytes_at _ _ _ _ => exact GSRC
| |- _ => try (clear - G0' G1 LRP LPF F4 F5 LOR SPT Lgs LFS LSM; lia)
end.
{ apply (live_checked_src RT AF Σ m3 _ lo Gv (8 * os_lacing_storage os)); [eassumption| exact ING| lia| lia| exact G1]. }
{ apply (live_checked_dst RT AF Σ m3 _ Gv (8 * os_lacing_storage os)); [eassumption| exact ING| lia| lia| exact WRG3]. }
intros kc4 Hc4. unfold icpt_postF in Hc4.
cps_unpack Hc4 as (m5 & RS5 & (ART5 & MI5 & WM5 & ST5) & PRES5 & BY5).
pose proof (ogg_bytes_piece m3 m5 Gv gsrc WRG3 WM5 BY5) as Q1'. clear BY5 Q1 GSRC.
tx P1' ltac:(cls_live INL). tx P2 ltac:(cls_live INL). tx Q2 ltac:(cls_live ING).
tx OS ltac:(cls_frame INF). tx FR ltac:(cls_stack). tx BODY ltac:(cls_live INB).
tx OG ltac:(cls_frame INF). tx HS ltac:(cls_live INSY). tx BS ltac:(cls_live INSY).

cps_seg (pgi_l4 A Bd (os_body_fill os) (os_body_returned os) L Gv (os_lacing_fill os) (os_lacing_packet os) (os_lacing_returned os) usp
(pg_body_len og) (Dsy + pg_hdr og + pg_header_len og) (Dsy + pg_hdr og) shdr hs os).
destruct POST as (m6 & x10' & x11' & -> & MU6 & WM6 & MI6 & OS6). unfold stream_cells_r in OS6.
clear OS. cps_seg_post.

assert (LAC6 : u32arr bsegs m6 L (firstn nf (skipn nr lws) ++ skipn nf lws)).
{ apply u8_u32arr. rewrite <- u32_move by exact NRF. fold lb. rewrite <- EDls, <- EDl2.
apply u8arr_app. split; [apply u8arr_rw_CB; exact P1'|]. rewrite LEQ. apply u8arr_rw_CB. exact P2. }
assert (GRA6 : u64arr bsegs m6 Gv (firstn nf (skipn nr gws) ++ skipn nf gws)).
{ apply u8_u64arr. rewrite <- u64_move by lia. fold gb. rewrite <- EDgs, <- EDg2.
apply u8arr_app. split; [apply u8arr_rw_CB; exact Q1'|]. rewrite GEQ. apply u8arr_rw_CB. exact Q2. }
eapply (Hk _ m6 _ _); try eassumption.
* rewrite stream_cells_ret_lacing, ERL. cbn [set_lacing os_lacing_fill os_lacing_packet os_lacing_returned]. exact OS6.
* rewrite ERL. cbn [set_lacing os_lacing]. unfold zdrop. fold nr.
replace nf with (length (os_lacing os) - nr)%nat by (unfold nf, nr; lia). apply wpre_move; [exact LPRE| unfold nr; lia].
* rewrite length_app, firstn_length_le, length_skipn by (rewrite length_skipn; lia). lia.
* rewrite length_app, firstn_length_le, length_skipn by (rewrite length_skipn; lia). lia.
Qed.

Lemma live_remove_In : forall p (l : list (Z * Z)) e, In e (live_remove p l) <-> In e l /\ fst e <> p.
Proof.
intros p l e. unfold live_remove. rewrite <- !stdpp.base.list_elem_of_In, stdpp.list_basics.list.list_elem_of_filter.
destruct (Z.eqb_spec (fst e) p) as [E|E]; cbn [negb]; split; intros [H1 H2]; try tauto; split; auto; exact I.
Qed.

Lemma pgi_rest_In : forall Bd L Gv live e, In e (pgi_rest Bd L Gv live) <-> In e live /\ fst e <> Bd /\ fst e <> L /\ fst e <> Gv.
Proof. intros. unfold pgi_rest. rewrite !live_remove_In. tauto. Qed.

Lemma chunk_apart_aclient : forall (Σ Σ1 : rts RT) (m1 : mem) p n l1 l2 LVx usp a,
ART RT Σ1 m1 -> rt_live RT Σ1 = l1 ++ (p, n) :: l2 -> (forall e, In e LVx -> In e (l1 ++ l2)) ->
rt_frames RT Σ1 = rt_frames RT Σ -> rt_sp0 RT Σ1 = rt_sp0 RT Σ -> rt_sp0 RT Σ - STACK_WIN <= usp ->
aclient LVx (rt_frames RT Σ) usp a -> ~ (p <= a < p + n).
Proof using AF.
intros Σ Σ1 m1 p n l1 l2 LVx usp a ART1 LV SUB FRS SP0 LU Ha Hin.
assert (INL : In (p, n) (rt_live RT Σ1)) by (rewrite LV; apply in_or_app; right; left; reflexivity).
pose proof (af_live_range RT AF Σ1 m1 p n ART1 INL) as (L0 & L1 & L2). rewrite SP0 in L1.
destruct Ha as [H|[H|[H|[H|H]]]].
- lia.
- pose proof (X0qz.client_static_range a H). unfold SEGTOP_A in *. lia.
- destruct H as (p' & n' & Hin' & Hp').
destruct (af_live_disj RT AF Σ1 m1 p n p' n' l1 l2 ART1 LV (SUB _ Hin')); lia.
- destruct H as (f & k & Hinf & Hf). rewrite <- FRS in Hinf.
pose proof (af_frames_range RT AF Σ1 m1 f k ART1 Hinf) as (_ & _ & _ & R3). destruct (R3 p n INL); lia.
- destruct H as (f & k & Hinf & Hf). rewrite <- FRS in Hinf.
pose proof (af_fshadow_apart RT AF Σ1 m1 f k ART1 Hinf) as (SL & _). destruct (SL p n INL); lia.
Qed.

Lemma rest_apart : forall (Σ : rts RT) (m : mem) Bd L Gv p n usp a,
ART RT Σ m -> In (p, n) (rt_live RT Σ) -> (p = Bd \/ p = L \/ p = Gv) -> rt_sp0 RT Σ - STACK_WIN <= usp ->
aclient (pgi_rest Bd L Gv (rt_live RT Σ)) (rt_frames RT Σ) usp a -> ~ (p <= a < p + n).
Proof using AF.
intros Σ m Bd L Gv p n usp a ART0 IN PE LU Ha.
destruct (in_split _ _ IN) as (l1 & l2 & E).
apply (chunk_apart_aclient Σ Σ m p n l1 l2 (pgi_rest Bd L Gv (rt_live RT Σ)) usp a ART0 E); [| reflexivity| reflexivity| exact LU| exact Ha].
intros e He. apply pgi_rest_In in He. destruct He as (He & N1 & N2 & N3). rewrite E in He.
apply in_app_or in He. apply in_or_app. destruct He as [He|[He|He]]; [left; exact He| | right; exact He].
subst e. cbn [fst] in *. exfalso. destruct PE as [->|[->| ->]]; congruence.
Qed.

Lemma wpre_firstn_ext : forall l (ws ws' : list word), wpre l ws -> firstn (length ws) ws' = ws -> wpre l ws'.
Proof.
intros l ws ws' [P LE] E. assert (LW : (length ws <= length ws')%nat).
{ destruct (Nat.le_gt_cases (length ws) (length ws')) as [H|H]; [exact H|]. rewrite firstn_all2 in E by lia. rewrite E in H. lia. }
split; [| lia]. transitivity (firstn (length l) (firstn (length ws) ws')); [rewrite firstn_firstn; f_equal; lia| rewrite E; exact P].
Qed.
Lemma body_pre_firstn_ext : forall body (bytes bytes' : list byte), body_pre body bytes -> firstn (length bytes) bytes' = bytes -> body_pre body bytes'.
Proof.
intros body bytes bytes' [P LE] E. assert (LW : (length bytes <= length bytes')%nat).
{ destruct (Nat.le_gt_cases (length bytes) (length bytes')) as [H|H]; [exact H|]. rewrite firstn_all2 in E by lia. rewrite E in H. lia. }
split; [| lia]. transitivity (firstn (length body) (ubytes (firstn (length bytes) bytes'))); [rewrite ubytes_firstn, firstn_firstn; f_equal; lia| rewrite E; exact P].
Qed.

Lemma live_head_apart : forall (Σ1 : rts RT) (m1 : mem) p n rest p2 n2, ART RT Σ1 m1 -> rt_live RT Σ1 = (p, n) :: rest -> In (p2, n2) rest ->
p + n <= p2 \/ p2 + n2 <= p.
Proof using AF. intros Σ1 m1 p n rest p2 n2 ART1 E IN. exact (af_live_disj RT AF Σ1 m1 p n p2 n2 [] rest ART1 E IN). Qed.
Lemma live_second_apart : forall (Σ1 : rts RT) (m1 : mem) p0 n0 p n rest p2 n2, ART RT Σ1 m1 -> rt_live RT Σ1 = (p0, n0) :: (p, n) :: rest ->
In (p2, n2) rest -> p + n <= p2 \/ p2 + n2 <= p.
Proof using AF. intros. apply (af_live_disj RT AF Σ1 m1 p n p2 n2 [(p0, n0)] rest); [assumption| assumption| right; assumption]. Qed.

Lemma pgi_phaseF : forall (Σ : rts RT) PMc (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x27 x28 x29 x30 x31 : word) F fc (m0 m : mem)
(LV : list (Z * Z)) (frs : list (Z * nat)) (A G Dsy nsy Bd L Gv f lo segptr bosv : Z) (k : nat) (og : page) (os5 : stream_st bptr)
(shdr hs bs bodybytes j0 : list byte) (lws gws : list word),
fdfs_only PMc -> mat_stable PMc ->
rw_cells bsegs m A (stream_cells Bd L Gv shdr os5) -> length shdr = 284%nat -> 0 < A ->
rw_cells bsegs m Bd [CB (length bodybytes) bodybytes] -> Z.of_nat (length bodybytes) = os_body_storage os5 ->
u32arr bsegs m L lws -> wpre (os_lacing os5) lws -> Z.of_nat (length lws) = os_lacing_storage os5 ->
u64arr bsegs m Gv gws -> Z.of_nat (length gws) = os_lacing_storage os5 ->
rw_cells bsegs m (bv_unsigned sp + -144) (pgi_frame ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j0 hs) ->
rw_cells bsegs m G (page_cells Dsy og) ->
bytes_at bsegs m (Dsy + pg_hdr og) hs -> bytes_at bsegs m (Dsy + pg_hdr og + pg_header_len og) bs ->
stream_fields_ok os5 -> os_lacing_fill os5 + (znth (ubytes hs) 26 - segptr) + 1 <= os_lacing_storage os5 -> 0 <= segptr <= znth (ubytes hs) 26 ->
(bosv = 0 \/ bosv = Z.land (znth (ubytes hs) 5) 2) ->
zlength (os_lacing os5) = os_lacing_fill os5 -> 0 <= os_lacing_packet os5 <= os_lacing_fill os5 -> lacing_vals_ok (os_lacing os5) ->
length hs = (27 + Z.to_nat (znth (ubytes hs) 26))%nat -> Z.of_nat (length hs) = pg_header_len og -> Z.of_nat (length bs) = pg_body_len og ->
0 <= pg_hdr og -> pg_hdr og + pg_header_len og + pg_body_len og <= nsy ->
In (Bd, os_body_storage os5) (rt_live RT Σ) -> In (L, 4 * os_lacing_storage os5) (rt_live RT Σ) -> In (Gv, 8 * os_lacing_storage os5) (rt_live RT Σ) ->
In (Dsy, nsy) (rt_live RT Σ) -> Bd <> L -> Bd <> Gv -> L <> Gv -> Dsy <> L -> Dsy <> Gv ->
rt_frames RT Σ = frs -> In (f, k) frs -> f <= A -> A + 408 <= f + fs_size k - 8 -> f <= G -> G + 32 <= f + fs_size k - 8 ->
(forall e, In e LV -> In e (rt_live RT Σ)) ->
(forall a, aclient LV frs (bv_unsigned sp) a -> bv_unsigned sp <= a \/ a < rt_sp0 RT Σ - STACK_WIN) ->
(forall a, aclient LV frs (bv_unsigned sp) a -> ~ (L <= a < L + 4 * os_lacing_storage os5)) ->
(forall a, aclient LV frs (bv_unsigned sp) a -> ~ (Gv <= a < Gv + 8 * os_lacing_storage os5)) ->
ART RT Σ m -> mem_inv bsegs m ->
stk bsegs m lo (bv_unsigned sp + -144) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK + 256 <= bv_unsigned sp -> bv_unsigned sp + 16 <= USTACK_TOP ->
rt_pres_fp LV frs (bv_unsigned sp) [(A, A + 408)] m0 m ->
forall T c,
ASTA RT Σ PMc (eq (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp (Z_to_bv 64 0x638c98) x5 x6 x7 (Z_to_bv 64 A) (Z_to_bv 64 (znth (ubytes hs) 5)) x10
x11 x12 x13 x14 x15 x16 x17
x18 x19 x20 (Z_to_bv 64 (Dsy + pg_hdr og)) x22 (Z_to_bv 64 segptr) (Z_to_bv 64 (ogg_page_pageno (ubytes hs))) (Z_to_bv 64 bosv)
(Z_to_bv 64 (znth (ubytes hs) 26)) x27 x28 x29 x30 x31)
F (Z_to_bv 64 0xc1ce0) fc None m (seg_rom bsegs))) c ->
(forall c', ASTA RT Σ PMc (fun ms => exists m' (lws' gws' : list word),
ret_stL (fun F' fc' => F' = F /\ fc' = fc) ra sp gp (Z_to_bv 64 0x638c98) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) m' ms
/\ rt_after_f RT Σ (bv_unsigned sp) lo m0 m'
/\ rt_pres_fp LV frs (bv_unsigned sp) [(A, A + 408)] m0 m'
/\ rw_cells bsegs m' A (stream_cells Bd L Gv shdr (pagein_segments os5 (ubytes hs) bosv segptr))
/\ rw_cells bsegs m' Bd [CB (length bodybytes) bodybytes]
/\ u32arr bsegs m' L lws' /\ wpre (os_lacing (pagein_segments os5 (ubytes hs) bosv segptr)) lws' /\ Z.of_nat (length lws') = os_lacing_storage os5
/\ u64arr bsegs m' Gv gws' /\ Z.of_nat (length gws') = os_lacing_storage os5) c' ->
realizes bsegs c' T) ->
realizes bsegs c T.
Proof using AF.
intros Σ PMc ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x27 x28 x29 x30 x31 F fc m0 m
LV frs A G Dsy nsy Bd L Gv f lo segptr bosv k og os5 shdr hs bs bodybytes j0 lws gws
FDO MST OS HL A0 BODY BLEN LAC LPRE LLEN GRA GLEN FR OG HS BS FOK Hls Hseg Hbos LFILL LPK LOK LENH HLEN BSLEN PG0 PGIN
INB INL ING INSY NBL NBG NLG NSL NSG EFR INF FA1 FA2 FG1 FG2 SUBLV SPL NAL NAG ART0 MI0 ST0 LOW LOR SPT PF T c Hc Hk.
subst frs.
destruct (frame_below_lo RT AF Σ m f k lo ART0 INF LOW) as (BF1 & BF2 & BF3).
assert (FSZ : 0 <= fs_size k) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
destruct (live_below_lo RT AF Σ m Bd _ lo ART0 INB LOW) as (B0 & B1 & _).
destruct (live_below_lo RT AF Σ m L _ lo ART0 INL LOW) as (L0 & L1 & _).
destruct (live_below_lo RT AF Σ m Gv _ lo ART0 ING LOW) as (G0' & G1 & _).
destruct (live_below_lo RT AF Σ m Dsy _ lo ART0 INSY LOW) as (S0 & S1 & _).
destruct (frame_live_apart RT AF Σ m f k Bd _ ART0 INF INB) as (FLB & _).
destruct (frame_live_apart RT AF Σ m f k L _ ART0 INF INL) as (FLL & _).
destruct (frame_live_apart RT AF Σ m f k Gv _ ART0 INF ING) as (FLG & _).
destruct (frame_live_apart RT AF Σ m f k Dsy _ ART0 INF INSY) as (FLS & _).
pose proof (live_apart2 Σ m L _ Bd _ ART0 INL INB ltac:(congruence)) as SEP_LB.
pose proof (live_apart2 Σ m L _ Gv _ ART0 INL ING ltac:(congruence)) as SEP_LG.
pose proof (live_apart2 Σ m L _ Dsy _ ART0 INL INSY NSL) as SEP_LS.
pose proof (live_apart2 Σ m Gv _ Bd _ ART0 ING INB ltac:(congruence)) as SEP_GvB.
pose proof (live_apart2 Σ m Gv _ Dsy _ ART0 ING INSY NSG) as SEP_GvS.
set (ls := os_lacing_storage os5) in *. set (H := Dsy + pg_hdr og) in *.
pose proof (byte_range (nth (Z.to_nat 26) hs (Z_to_bv 8 0))) as H26. rewrite <- (znth_ubytes hs 26) in H26 by lia.
assert (HR : Dsy <= H /\ H + Z.of_nat (length hs) <= Dsy + nsy) by (unfold H; clear - PG0 PGIN HLEN BSLEN; lia).
assert (SEP_AL : L + 4 * ls <= A \/ A + 408 <= L) by (clear - FLL FA1 FA2; lia).
assert (SEP_AGv : Gv + 8 * ls <= A \/ A + 408 <= Gv) by (clear - FLG FA1 FA2; lia).
assert (SEP_AH : H + Z.of_nat (length hs) <= A \/ A + 408 <= H) by (clear - FLS FA1 FA2 HR; lia).
assert (SEP_HL : H + Z.of_nat (length hs) <= L \/ L + 4 * ls <= H) by (clear - SEP_LS HR; lia).
assert (SEP_HG : H + Z.of_nat (length hs) <= Gv \/ Gv + 8 * ls <= H) by (clear - SEP_GvS HR; lia).
assert (SEP_LG' : L + 4 * ls <= Gv \/ Gv + 8 * ls <= L) by (clear - SEP_LG; lia).
assert (SEP_GB : Bd + os_body_storage os5 <= G \/ G + 32 <= Bd) by (clear - FLB FG1 FG2; lia).
assert (SEP_GL : L + 4 * ls <= G \/ G + 32 <= L) by (clear - FLL FG1 FG2; lia).
assert (SEP_GG : Gv + 8 * ls <= G \/ G + 32 <= Gv) by (clear - FLG FG1 FG2; lia).
assert (SEP_AB : Bd + os_body_storage os5 <= A \/ A + 408 <= Bd) by (clear - FLB FA1 FA2; lia).
assert (SEP_AS : Dsy + nsy <= A \/ A + 408 <= Dsy) by (clear - FLS FA1 FA2; lia).
assert (PN : 0 <= ogg_page_pageno (ubytes hs) < 2^32) by (apply pageno_range; lia).
assert (LOSP : lo + 144 <= bv_unsigned sp) by (clear - LOR; unfold RT_STACK in LOR; lia).
assert (ALO : A + 408 <= lo) by (clear - FA2 BF1; lia).
assert (TOPL : L + 4 * ls < 2^63) by (clear - L1 LOR SPT; unfold RT_STACK, USTACK_TOP in *; lia).
assert (TOPG : Gv + 8 * ls < 2^63) by (clear - G1 LOR SPT; unfold RT_STACK, USTACK_TOP in *; lia).
assert (TOPH : H + Z.of_nat (length hs) < 2^63) by (clear - HR S1 LOR SPT; unfold RT_STACK, USTACK_TOP in *; lia).
assert (HLO : H + Z.of_nat (length hs) <= lo) by (clear - HR S1; lia).
assert (HH : 0 <= H) by (clear - HR S0; lia).
clear FLB FLL FLG FLS.
unfold page_cells in OG.
cps_norm. cps_hide.
cps_seg (X10m.pi_final A Bd L Gv H lo shdr hs os5 ra sp gp (Z_to_bv 64 0x638c98) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc x1 segptr bosv
(ogg_page_pageno (ubytes hs)) (Z_to_bv 64 (znth (ubytes hs) 18)) (Z_to_bv 64 (znth (ubytes hs) 21)) j0
LENH H26 HL FOK Hls Hseg Hbos LFILL LPK LOK A0 L0 G0' HH TOPL TOPG TOPH LOSP ALO SEP_AL SEP_AGv SEP_AH L1 G1 HLO SEP_LG' SEP_HL SEP_HG eq_refl).
unfold final_post in POST.
destruct POST as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & lws1 & gws1 & -> & MU1 & WM1 & MI1 & OS1 & LAC1 & LPRE1 & LLEN1 & GRA1 & GLEN1 & ST1 & HS1).
clear OS FR HS. cps_seg_post.
apply Hk. eapply ASTA_conseq; [eassumption|]. intros ms <-. exists m1, lws1, gws1.
split; [unfold ret_stL; do 16 eexists; split; [reflexivity| split; reflexivity]|].
split; [split; [assumption| split; [exact MI1| exact ST1]]|].
split; [exact PF|]. split; [exact OS1|]. split; [exact BODY|].
split; [exact LAC1|]. split; [exact LPRE1|]. split; [exact LLEN1|]. split; [exact GRA1| exact GLEN1].
Qed.

Lemma u8arr_split3 : forall (m : mem) A (bb : list byte) a n,
u8arr bsegs m A bb -> (a + n <= length bb)%nat ->
u8arr bsegs m A (firstn a bb) /\ u8arr bsegs m (A + Z.of_nat a) (firstn n (skipn a bb)) /\ u8arr bsegs m (A + Z.of_nat a + Z.of_nat n) (skipn (a + n) bb).
Proof.
intros m A bb a n H LE.
rewrite <- (firstn_skipn a bb) in H. apply u8arr_app in H. destruct H as (H1 & H2).
rewrite firstn_length_le in H2 by lia.
rewrite <- (firstn_skipn n (skipn a bb)) in H2. apply u8arr_app in H2. destruct H2 as (H2 & H3).
rewrite firstn_length_le in H3 by (rewrite length_skipn; lia). rewrite skipn_skipn in H3.
replace (n + a)%nat with (a + n)%nat in H3 by lia.
split; [exact H1| split; [exact H2| exact H3]].
Qed.

Lemma body_pre_copy : forall (body3 zs : list Z) (bodybytes bb2 bsrc : list byte) (fill : nat),
body_pre body3 bodybytes -> length body3 = fill -> firstn (length bodybytes) bb2 = bodybytes ->
ubytes bsrc = zs -> (fill + length bsrc <= length bb2)%nat ->
body_pre (body3 ++ zs) (firstn fill bb2 ++ bsrc ++ skipn (fill + length bsrc) bb2).
Proof.
intros body3 zs bodybytes bb2 bsrc fill (BP1 & BP2) LB FX ZS LE.
assert (LZ : length zs = length bsrc) by (rewrite <- ZS; apply ubytes_length).
assert (EF : firstn fill (ubytes bb2) = body3).
{ rewrite <- BP1, <- FX, ubytes_firstn, firstn_firstn. f_equal. lia. }
split.
- rewrite !ubytes_app, length_app, LZ, LB.
rewrite firstn_app, ubytes_length, firstn_length_le by lia.
rewrite firstn_all2 by (rewrite ubytes_length, firstn_length_le; lia).
replace (fill + length bsrc - fill)%nat with (length bsrc) by lia.
rewrite firstn_app, ubytes_length, Nat.sub_diag, firstn_O, app_nil_r.
rewrite (@firstn_all2 Z (length bsrc) (ubytes bsrc)) by (rewrite ubytes_length; lia).
rewrite ubytes_firstn, EF, ZS. reflexivity.
- rewrite !length_app, firstn_length_le, LZ, LB by lia. lia.
Qed.

Lemma stream_cells_pagein_body : forall Bd L G hdr (os : stream_st bptr) body sk n,
stream_cells Bd L G hdr (pagein_body os body sk n)
= stream_cells_r Bd (os_body_fill os + n) (os_body_returned os) L G (os_lacing_fill os) (os_lacing_packet os) (os_lacing_returned os) hdr os.
Proof. intros. reflexivity. Qed.

Lemma body_expand_res_fields : forall (os : stream_st bptr) n,
os_body (body_expand_res os n) = os_body os /\ os_body_fill (body_expand_res os n) = os_body_fill os /\
os_body_returned (body_expand_res os n) = os_body_returned os /\ os_lacing_storage (body_expand_res os n) = os_lacing_storage os /\
os_lacing_fill (body_expand_res os n) = os_lacing_fill os /\ os_lacing_packet (body_expand_res os n) = os_lacing_packet os /\
os_lacing_returned (body_expand_res os n) = os_lacing_returned os /\ os_lacing (body_expand_res os n) = os_lacing os.
Proof. intros os n. unfold body_expand_res. destruct (os_body_fill os <? os_body_storage os - n); cbn; repeat split; reflexivity. Qed.

Lemma body_expand_res_room : forall (os : stream_st bptr) n, 0 <= n -> os_body_fill os <= os_body_storage os ->
os_body_fill os + n <= os_body_storage (body_expand_res os n) /\ os_body_storage os <= os_body_storage (body_expand_res os n).
Proof. intros os n N0 FS. unfold body_expand_res. destruct (Z.ltb_spec (os_body_fill os) (os_body_storage os - n)); cbn; lia. Qed.

Lemma live_apart_LV : forall (Σ Σ1 : rts RT) (m1 : mem) p n LVx usp a,
ART RT Σ1 m1 -> In (p, n) (rt_live RT Σ1) -> (forall e, In e LVx -> In e (rt_live RT Σ1) /\ fst e <> p) ->
rt_frames RT Σ1 = rt_frames RT Σ -> rt_sp0 RT Σ1 = rt_sp0 RT Σ -> rt_sp0 RT Σ - STACK_WIN <= usp ->
aclient LVx (rt_frames RT Σ) usp a -> ~ (p <= a < p + n).
Proof using AF.
intros Σ Σ1 m1 p n LVx usp a ART1 IN SUB FRS SP0 LU Ha.
destruct (in_split _ _ IN) as (l1 & l2 & E).
apply (chunk_apart_aclient Σ Σ1 m1 p n l1 l2 LVx usp a ART1 E); [| exact FRS| exact SP0| exact LU| exact Ha].
intros e He. destruct (SUB e He) as (He1 & Hne). rewrite E in He1.
apply in_app_or in He1. apply in_or_app. destruct He1 as [He1|[He1|He1]]; [left; exact He1| | right; exact He1].
subst e. cbn [fst] in Hne. congruence.
Qed.

Lemma pgi_phaseX : forall (Σ : rts RT) PMc (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) F fc (m0 m : mem)
(LV : list (Z * Z)) (A G Dsy nsy Bd L Gv f lo n src skipped : Z) (k : nat) (og : page) (os3 : stream_st bptr)
(shdr hs bs bodybytes j0 bsrc : list byte) (body : list Z) (lws gws : list word),
fdfs_only PMc -> mat_stable PMc ->
rw_cells bsegs m A (stream_cells Bd L Gv shdr os3) -> length shdr = 284%nat -> 0 < A ->
rw_cells bsegs m Bd [CB (length bodybytes) bodybytes] -> Z.of_nat (length bodybytes) = os_body_storage os3 -> body_pre (os_body os3) bodybytes ->
zlength (os_body os3) = os_body_fill os3 -> 0 <= os_body_fill os3 <= os_body_storage os3 -> os_body_storage os3 + n + 1024 <= 64512 ->
rw_cells bsegs m L [CB (length (u32s lws)) (u32s lws)] -> rw_cells bsegs m Gv [CB (length (u64s gws)) (u64s gws)] ->
rw_cells bsegs m (bv_unsigned sp + -144) (pgi_frame ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j0 hs) ->
rw_cells bsegs m G (page_cells Dsy og) ->
bytes_at bsegs m (Dsy + pg_hdr og) hs -> bytes_at bsegs m (Dsy + pg_hdr og + pg_header_len og) bs ->
bytes_at bsegs m src bsrc -> Z.of_nat (length bsrc) = n -> 0 < n -> ubytes bsrc = zslice skipped n body ->
Dsy <= src -> src + n <= Dsy + nsy -> Dsy <= Dsy + pg_hdr og -> Dsy + pg_hdr og + pg_header_len og + pg_body_len og <= Dsy + nsy ->
Z.of_nat (length hs) = pg_header_len og -> Z.of_nat (length bs) = pg_body_len og ->
In (Bd, os_body_storage os3) (rt_live RT Σ) -> In (L, Z.of_nat (length (u32s lws))) (rt_live RT Σ) -> In (Gv, Z.of_nat (length (u64s gws))) (rt_live RT Σ) ->
In (Dsy, nsy) (rt_live RT Σ) -> Bd <> L -> Bd <> Gv -> Dsy <> Bd -> 0 < Z.of_nat (length (u32s lws)) -> 0 < Z.of_nat (length (u64s gws)) ->
In (f, k) (rt_frames RT Σ) -> f <= A -> A + 408 <= f + fs_size k - 8 -> f <= G -> G + 32 <= f + fs_size k - 8 -> (A + 408 <= G \/ G + 32 <= A) ->
(forall e, In e LV -> In e (rt_live RT Σ) /\ fst e <> Bd) ->
Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX -> 0 <= rt_credit RT Σ ->
ART RT Σ m -> mem_inv bsegs m ->
stk bsegs m lo (bv_unsigned sp + -144) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK + 256 <= bv_unsigned sp -> bv_unsigned sp + 16 <= USTACK_TOP ->
bv_unsigned sp mod 16 = 0 ->
rt_pres_fp LV (rt_frames RT Σ) (bv_unsigned sp) [(A, A + 408)] m0 m ->
forall T c,
ASTA RT Σ PMc (eq (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp (Z_to_bv 64 0x638c98) x5 x6 x7 (Z_to_bv 64 A) x9 x10 x11 x12 x13 x14 x15 x16 x17
x18 (Z_to_bv 64 n) (Z_to_bv 64 src) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
F (Z_to_bv 64 0xc1cac) fc None m (seg_rom bsegs))) c ->
(forall c' (Σ2 : rts RT) (Bd2 : Z) (m' : mem) (bb' : list byte) (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
ASTA RT Σ2 PMc (eq (MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp (Z_to_bv 64 0x638c98) y5 y6 y7 (Z_to_bv 64 A) x9 y10 y11 y12 y13 y14 y15 y16 y17
x18 (Z_to_bv 64 n) (Z_to_bv 64 src) x21 x22 x23 x24 x25 x26 x27 y28 y29 y30 y31)
F (Z_to_bv 64 0xc1ce0) fc None m' (seg_rom bsegs))) c' ->
ART RT Σ2 m' -> mem_inv bsegs m' -> stk bsegs m' lo (bv_unsigned sp + -144) ->
rw_cells bsegs m' (bv_unsigned sp + -144) (pgi_frame ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j0 hs) ->
rw_cells bsegs m' A (stream_cells Bd2 L Gv shdr (pagein_body (body_expand_res os3 n) body skipped n)) ->
rw_cells bsegs m' Bd2 [CB (length bb') bb'] -> Z.of_nat (length bb') = os_body_storage (body_expand_res os3 n) ->
body_pre (os_body os3 ++ zslice skipped n body) bb' ->
rw_cells bsegs m' L [CB (length (u32s lws)) (u32s lws)] -> rw_cells bsegs m' Gv [CB (length (u64s gws)) (u64s gws)] ->
rw_cells bsegs m' G (page_cells Dsy og) ->
bytes_at bsegs m' (Dsy + pg_hdr og) hs -> bytes_at bsegs m' (Dsy + pg_hdr og + pg_header_len og) bs ->
rt_pres_fp LV (rt_frames RT Σ) (bv_unsigned sp) [(A, A + 408)] m0 m' ->
In (Bd2, os_body_storage (body_expand_res os3 n)) (rt_live RT Σ2) ->
In (L, Z.of_nat (length (u32s lws))) (rt_live RT Σ2) -> In (Gv, Z.of_nat (length (u64s gws))) (rt_live RT Σ2) -> In (Dsy, nsy) (rt_live RT Σ2) ->
Bd2 <> L -> Bd2 <> Gv -> Dsy <> Bd2 ->
(forall e, In e LV -> In e (rt_live RT Σ2)) -> (length (rt_live RT Σ2) <= length (rt_live RT Σ))%nat ->
((os_body_fill os3 < os_body_storage os3 - n /\ Bd2 = Bd /\ rt_live RT Σ2 = rt_live RT Σ)
\/ (os_body_storage os3 - n <= os_body_fill os3 /\ rt_live RT Σ2 = (Bd2, os_body_storage os3 + n + 1024) :: live_remove Bd (rt_live RT Σ))) ->
rt_frames RT Σ2 = rt_frames RT Σ -> rt_sp0 RT Σ2 = rt_sp0 RT Σ -> rt_credit RT Σ2 = rt_credit RT Σ -> rt_pois RT Σ2 = rt_pois RT Σ ->
realizes bsegs c' T) ->
realizes bsegs c T.
Proof using AF MCPY BEXP.
intros Σ PMc ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m0 m
LV A G Dsy nsy Bd L Gv f lo n src skipped k og os3 shdr hs bs bodybytes j0 bsrc body lws gws
FDO MST OS HL A0 BODY BLEN BPRE BFILL BF0 BSB LAC GRA FR OG HS BS SRC LSRC N0 ZSRC SR1 SR2 PH1 PH2 HLEN BSLEN
INB INL ING INSY NBL NBG NSB LP0 GP0 INF FA1 FA2 FG1 FG2 SEP_AG SUBLV LVM CR0 ART0 MI0 ST0 LOW LOR SPT SPA PF T c Hc Hk.
set (usp := bv_unsigned sp) in *.
destruct (frame_below_lo RT AF Σ m f k lo ART0 INF LOW) as (BF1 & BF2 & BF3).
assert (FSZ : 0 <= fs_size k) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
destruct (live_below_lo RT AF Σ m Bd _ lo ART0 INB LOW) as (B0 & B1 & _).
destruct (live_below_lo RT AF Σ m L _ lo ART0 INL LOW) as (L0 & L1 & _).
destruct (live_below_lo RT AF Σ m Gv _ lo ART0 ING LOW) as (G0' & G1 & _).
destruct (live_below_lo RT AF Σ m Dsy _ lo ART0 INSY LOW) as (S0 & S1 & _).
assert (EU : bv_unsigned (Z_to_bv 64 (usp + -144)) = usp + -144) by (apply unsigned_lit; clear - LOR SPT BF3; unfold RT_STACK, USTACK_TOP, SH_HI in *; lia).
assert (SUBLVB : forall e, In e LV -> In e (live_remove Bd (rt_live RT Σ))) by (intros e He; destruct (SUBLV e He) as (X1 & X2); apply live_remove_keep; assumption).
assert (SUBLV0 : forall e, In e LV -> In e (rt_live RT Σ)) by (intros e He; exact (proj1 (SUBLV e He))).
assert (SPL : forall a, aclient LV (rt_frames RT Σ) usp a -> usp <= a \/ a < rt_sp0 RT Σ - STACK_WIN).
{ intros a Ha. apply (aclient_split RT AF Σ m usp a ART0). apply (aclient_mono _ _ _ _ _ _ _ Ha); [exact SUBLV0| auto| apply Z.le_refl]. }
assert (INLB : In (L, Z.of_nat (length (u32s lws))) (live_remove Bd (rt_live RT Σ))) by (apply live_remove_keep; [exact INL| cbn [fst]; congruence]).
assert (INGB : In (Gv, Z.of_nat (length (u64s gws))) (live_remove Bd (rt_live RT Σ))) by (apply live_remove_keep; [exact ING| cbn [fst]; congruence]).
assert (INSYB : In (Dsy, nsy) (live_remove Bd (rt_live RT Σ))) by (apply live_remove_keep; [exact INSY| cbn [fst]; exact NSB]).
pose proof (body_expand_res_fields os3 n) as (EX1 & EX2 & EX3 & EX4 & EX5 & EX6 & EX7 & EX8).
destruct (frame_live_apart RT AF Σ m f k L _ ART0 INF INL) as (FLL & _).
destruct (frame_live_apart RT AF Σ m f k Gv _ ART0 INF ING) as (FLG & _).
destruct (frame_live_apart RT AF Σ m f k Dsy _ ART0 INF INSY) as (FLS & _).
destruct (frame_live_apart RT AF Σ m f k Bd _ ART0 INF INB) as (FLB & _).
assert (SEP_AL : L + Z.of_nat (length (u32s lws)) <= A \/ A + 408 <= L) by (clear - FLL FA1 FA2; lia).
assert (SEP_AGv : Gv + Z.of_nat (length (u64s gws)) <= A \/ A + 408 <= Gv) by (clear - FLG FA1 FA2; lia).
assert (SEP_AS : Dsy + nsy <= A \/ A + 408 <= Dsy) by (clear - FLS FA1 FA2; lia).
assert (SEP_GL : L + Z.of_nat (length (u32s lws)) <= G \/ G + 32 <= L) by (clear - FLL FG1 FG2; lia).
assert (SEP_GGv : Gv + Z.of_nat (length (u64s gws)) <= G \/ G + 32 <= Gv) by (clear - FLG FG1 FG2; lia).
assert (SEP_GS : Dsy + nsy <= G \/ G + 32 <= Dsy) by (clear - FLS FG1 FG2; lia).
assert (SEP_GB : Bd + os_body_storage os3 <= G \/ G + 32 <= Bd) by (clear - FLB FG1 FG2; lia).
assert (SEP_AB : Bd + os_body_storage os3 <= A \/ A + 408 <= Bd) by (clear - FLB FA1 FA2; lia).
clear FLL FLG FLS FLB.
cps_norm. cps_hide.

cps_seg (pgi_x1 x1 (Z_to_bv 64 (usp + -144)) gp (Z_to_bv 64 0x638c98) x5 x6 x7 (Z_to_bv 64 A) x9 x10 x11 x12 x13 x14 x15 x16 x17
x18 (Z_to_bv 64 n) (Z_to_bv 64 src) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m).
lazymatch type of POST with ?x = _ => subst x end.
kp_all. unfold kp in OS, BODY. apply u8arr_rw_CB in BODY.
cps_norm.
cps_rt (BEXP Σ PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m A Bd L Gv n f lo k os3 shdr bodybytes).
all: [> lazymatch goal with
| |- stk _ _ _ _ => rewrite EU; exact ST0
| |- _ mod 16 = 0 => rewrite EU; clear - SPA; Z.div_mod_to_equations; lia
| |- _ => first [ rewrite EU; ulc | ulc ]
end .. | ].
clear OS BODY.
intros kc2 (Σ2 & Bd2 & Hc2 & INB2 & CASE & EF2 & ES2 & EC2 & EP2).
ogg_unpackL Hc2 as (m2 & bb2 & RS2 & (ART2 & MI2 & ST2) & PRES2 & OS2 & BODY2 & BLEN2 & BPFX2). destruct RS2 as (-> & ->).
tx LAC ltac:(cls_live INLB). tx GRA ltac:(cls_live INGB). tx FR ltac:(cls_stack). tx OG ltac:(cls_frame INF).
tx HS ltac:(cls_live INSYB). tx BS ltac:(cls_live INSYB). tx SRC ltac:(cls_live INSYB).

assert (LOU : rt_sp0 RT Σ - STACK_WIN <= usp) by (clear - LOW LOR; unfold STACK_WIN; lia).
pose proof (body_expand_res_room os3 n ltac:(lia) ltac:(lia)) as (RM1 & RM2).
assert (X2 : In (L, Z.of_nat (length (u32s lws))) (rt_live RT Σ2) /\ In (Gv, Z.of_nat (length (u64s gws))) (rt_live RT Σ2) /\ In (Dsy, nsy) (rt_live RT Σ2)
/\ Bd2 <> L /\ Bd2 <> Gv /\ Dsy <> Bd2
/\ (forall e, In e LV -> In e (rt_live RT Σ2)) /\ (length (rt_live RT Σ2) <= length (rt_live RT Σ))%nat
/\ (forall a, aclient LV (rt_frames RT Σ) usp a -> ~ (Bd2 <= a < Bd2 + os_body_storage (body_expand_res os3 n)))).
{ destruct CASE as [(FITS & -> & E)|(GROW & E)].
- split; [rewrite E; exact INL|]. split; [rewrite E; exact ING|]. split; [rewrite E; exact INSY|].
split; [exact NBL|]. split; [exact NBG|]. split; [exact NSB|].
split; [rewrite E; exact SUBLV0|]. split; [rewrite E; lia|].
intros a Ha. apply (live_apart_LV Σ Σ2 m2 Bd _ LV usp a ART2 INB2); [| exact EF2| exact ES2| exact LOU| exact Ha].
intros e He. rewrite E. exact (SUBLV e He).
- assert (ES : os_body_storage (body_expand_res os3 n) = os_body_storage os3 + n + 1024)
by (unfold body_expand_res; replace (os_body_fill os3 <? _) with false by (symmetry; apply Z.ltb_ge; exact GROW); reflexivity).
pose proof (live_head_apart Σ2 m2 _ _ _ L _ ART2 E INLB) as S1x.
pose proof (live_head_apart Σ2 m2 _ _ _ Gv _ ART2 E INGB) as S2x.
pose proof (live_head_apart Σ2 m2 _ _ _ Dsy _ ART2 E INSYB) as S3x.
split; [rewrite E; right; exact INLB|]. split; [rewrite E; right; exact INGB|]. split; [rewrite E; right; exact INSYB|].
split; [clear - S1x LP0 BF0 N0; lia|]. split; [clear - S2x GP0 BF0 N0; lia|]. split; [clear - S3x N0 SR1 SR2 BF0; lia|].
split; [intros e He; rewrite E; right; exact (SUBLVB e He)|].
split; [rewrite E; cbn [length]; pose proof (live_remove_length_lt Bd _ _ INB) as X; lia|].
intros a Ha. rewrite ES. apply (chunk_apart_aclient Σ Σ2 m2 Bd2 _ [] (live_remove Bd (rt_live RT Σ)) LV usp a ART2);
[exact E| exact SUBLVB| exact EF2| exact ES2| exact LOU| exact Ha]. }
destruct X2 as (INL2 & ING2 & INSY2 & NBL2 & NBG2 & NSB2 & SUB2 & LVM2 & NAB2).
assert (INF2 : In (f, k) (rt_frames RT Σ2)) by (rewrite EF2; exact INF).
assert (LOW2 : rt_sp0 RT Σ2 - STACK_WIN <= lo) by (rewrite ES2; exact LOW).
assert (SUBF2 : forall e, In e (rt_frames RT Σ) -> In e (rt_frames RT Σ2)) by (intros e He; rewrite EF2; exact He).
destruct (live_below_lo RT AF Σ2 m2 Bd2 _ lo ART2 INB2 LOW2) as (B20 & B21 & _).
pose proof (live_apart2 Σ2 m2 Dsy _ Bd2 _ ART2 INSY2 INB2 ltac:(congruence)) as SEP_SB2.
destruct (frame_live_apart RT AF Σ2 m2 f k Bd2 _ ART2 INF2 INB2) as (FLB2 & _).
assert (SEP_AB2 : Bd2 + os_body_storage (body_expand_res os3 n) <= A \/ A + 408 <= Bd2) by (clear - FLB2 FA1 FA2; lia).
assert (SEP_GB2 : Bd2 + os_body_storage (body_expand_res os3 n) <= G \/ G + 32 <= Bd2) by (clear - FLB2 FG1 FG2; lia).
assert (DISJ : Bd2 + os_body_fill os3 + Z.of_nat (length bsrc) <= src \/ src + Z.of_nat (length bsrc) <= Bd2 + os_body_fill os3)
by (clear - SEP_SB2 SR1 SR2 LSRC BF0 RM1 EX2; lia).
clear FLB2. cps_hide.

assert (LB2 : (Z.to_nat (os_body_fill os3) + length bsrc <= length bb2)%nat) by (clear - BLEN2 RM1 LSRC BF0 EX2; lia).
pose proof (u8arr_split3 m2 Bd2 bb2 (Z.to_nat (os_body_fill os3)) (length bsrc) BODY2 LB2) as (P1 & P2 & P3). clear BODY2.
rewrite Z2Nat.id in P2, P3 by lia.
assert (LP2 : length (firstn (length bsrc) (skipn (Z.to_nat (os_body_fill os3)) bb2)) = length bsrc) by (rewrite firstn_length_le; [reflexivity| rewrite length_skipn; lia]).
apply u8arr_rw_CB in P1, P2, P3.
pose proof (proj2 P2) as WR2. cbn [cells_size csize Nat.add] in WR2. rewrite Nat.add_0_r, LP2 in WR2.

rewrite stream_cells_r_eq, EX2 in OS2.
cps_seg (pgi_x2 A Bd2 (os_body_fill os3) (os_body_returned (body_expand_res os3 n)) L Gv (os_lacing_fill (body_expand_res os3 n))
(os_lacing_packet (body_expand_res os3 n)) (os_lacing_returned (body_expand_res os3 n)) n src shdr (body_expand_res os3 n)).
1: (clear - FA2 BF1 LOR SPT FSZ; lia).
1: (clear - B21 RM1 N0 LOR SPT; lia).
lazymatch type of POST with ?x = _ => subst x end.
kp_all.
lazymatch goal with H : ASTA _ _ _ (eq _) _ |- _ => rewrite <- LSRC in H end.
cps_rt (MCPY Σ2 PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 (Bd2 + os_body_fill os3) src bsrc lo).
all: [> lazymatch goal with
| |- call_ok _ _ _ _ _ => cps_callok
| |- bytes_at _ _ _ _ => unfold kp in SRC; exact SRC
| |- checked_src _ _ _ _ _ _ _ => apply (live_checked_src RT AF Σ2 m2 _ lo Dsy nsy); [exact ART2| exact INSY2| clear - SR1 LSRC; lia| clear - SR2 LSRC; lia| exact S1]
| |- checked_dst _ _ _ _ _ _ => apply (live_checked_dst RT AF Σ2 m2 _ Bd2 (os_body_storage (body_expand_res os3 n))); [exact ART2| exact INB2| clear - BF0; lia| clear - RM1 LSRC; lia| exact WR2]
| |- _ \/ _ => exact DISJ
| |- _ => idtac
end .. | ].
1: (clear - B20 B21 RM1 BF0 N0 LOR SPT; lia).
1: (clear - SR1 SR2 S0 S1 N0 LOR SPT; lia).
intros kc3 Hc3. unfold icpt_postF in Hc3.
cps_unpack Hc3 as (m3 & RS3 & (ART3 & MI3 & WM3 & ST3) & PRES3 & BY3).
pose proof (ogg_bytes_piece m2 m3 _ bsrc WR2 WM3 BY3) as P2'. clear BY3 P2.
assert (LP1 : Z.of_nat (length (firstn (Z.to_nat (os_body_fill os3)) bb2)) = os_body_fill os3) by (rewrite firstn_length_le by lia; lia).
assert (LP3 : Z.of_nat (length (skipn (Z.to_nat (os_body_fill os3) + length bsrc) bb2)) = Z.of_nat (length bb2) - os_body_fill os3 - Z.of_nat (length bsrc))
by (rewrite length_skipn; lia).
pose proof (live_apart2 Σ2 m3 Bd2 _ L _ ART3 INB2 INL2 ltac:(congruence)) as SEP_B2L.
pose proof (live_apart2 Σ2 m3 Bd2 _ Gv _ ART3 INB2 ING2 ltac:(congruence)) as SEP_B2G.
assert (DR : 0 <= os_body_fill os3 /\ os_body_fill os3 + Z.of_nat (length bsrc) <= os_body_storage (body_expand_res os3 n)) by (clear - BF0 RM1 LSRC; lia).
assert (HR : Dsy <= Dsy + pg_hdr og /\ Dsy + pg_hdr og + Z.of_nat (length hs) + Z.of_nat (length bs) <= Dsy + nsy) by (clear - PH1 PH2 HLEN BSLEN; lia).
cps_hide.
txe P1 ltac:(cls_live INB2) ltac:(fun x Hx => clear - Hx LP1; lia).
txe P3 ltac:(cls_live INB2) ltac:(fun x Hx => clear - Hx; lia).
txe OS2 ltac:(cls_frame INF2) ltac:(fun x Hx => clear - Hx SEP_AB2 DR; unfold hid in *; lia).
txe LAC ltac:(cls_live INL2) ltac:(fun x Hx => clear - Hx SEP_B2L DR; unfold hid in *; lia).
txe GRA ltac:(cls_live ING2) ltac:(fun x Hx => clear - Hx SEP_B2G DR; unfold hid in *; lia).
txe FR ltac:(cls_stack) ltac:(fun x Hx => clear - Hx B21 DR LOR; lia).
txe OG ltac:(cls_frame INF2) ltac:(fun x Hx => clear - Hx SEP_GB2 DR; unfold hid in *; lia).
txe HS ltac:(cls_live INSY2) ltac:(fun x Hx => clear - Hx SEP_SB2 DR HR; unfold hid in *; lia).
txe BS ltac:(cls_live INSY2) ltac:(fun x Hx => clear - Hx SEP_SB2 DR HR HLEN BSLEN; unfold hid in *; lia).
clear SRC.
lazymatch goal with H : ASTA _ _ _ (eq _) _ |- _ => rewrite LSRC in H end.

cps_seg (pgi_x3 A Bd2 (os_body_fill os3) (os_body_returned (body_expand_res os3 n)) L Gv (os_lacing_fill (body_expand_res os3 n))
(os_lacing_packet (body_expand_res os3 n)) (os_lacing_returned (body_expand_res os3 n)) n shdr (body_expand_res os3 n)).
1: (clear - FA2 BF1 LOR SPT FSZ; lia).
destruct POST as (m4 & a0' & -> & MU4 & WM4 & MI4 & OS4).
clear OS2. unfold page_cells in OG. unfold pgi_frame in FR. cps_seg_post.

assert (BODY4 : u8arr bsegs m4 Bd2 (firstn (Z.to_nat (os_body_fill os3)) bb2 ++ bsrc ++ skipn (Z.to_nat (os_body_fill os3) + length bsrc) bb2)).
{ apply u8arr_app. split; [apply u8arr_rw_CB; exact P1|]. rewrite LP1.
apply u8arr_app. split; [apply u8arr_rw_CB; exact P2'| apply u8arr_rw_CB; exact P3]. }
clear P1 P2' P3.
eapply (Hk _ Σ2 Bd2 m4 (firstn (Z.to_nat (os_body_fill os3)) bb2 ++ bsrc ++ skipn (Z.to_nat (os_body_fill os3) + length bsrc) bb2)); try eassumption.
- rewrite stream_cells_pagein_body, EX2. exact OS4.
- apply u8arr_rw_CB. exact BODY4.
- rewrite !length_app, firstn_length_le, length_skipn by lia. clear - BLEN2 LB2. lia.
- apply (body_pre_copy (os_body os3) (zslice skipped n body) bodybytes bb2 bsrc (Z.to_nat (os_body_fill os3)) BPRE); [| exact BPFX2| exact ZSRC| exact LB2].
unfold zlength in BFILL. lia.
Qed.

Lemma lacing_expand_res_fields : forall (os : stream_st bptr) n, 0 <= n -> os_lacing_fill os <= os_lacing_storage os ->
os_body (lacing_expand_res os n) = os_body os /\ os_body_fill (lacing_expand_res os n) = os_body_fill os /\
os_body_returned (lacing_expand_res os n) = os_body_returned os /\ os_body_storage (lacing_expand_res os n) = os_body_storage os /\
os_body_data (lacing_expand_res os n) = os_body_data os /\
os_lacing_fill (lacing_expand_res os n) = os_lacing_fill os /\ os_lacing_packet (lacing_expand_res os n) = os_lacing_packet os /\
os_lacing_returned (lacing_expand_res os n) = os_lacing_returned os /\ os_lacing (lacing_expand_res os n) = os_lacing os /\
os_pageno (lacing_expand_res os n) = os_pageno os /\
os_lacing_storage os <= os_lacing_storage (lacing_expand_res os n) /\ os_lacing_fill os + n <= os_lacing_storage (lacing_expand_res os n).
Proof.
intros os n N0 FS. unfold lacing_expand_res. destruct (Z.ltb_spec (os_lacing_fill os) (os_lacing_storage os - n)); cbn; repeat split; try reflexivity; try lia.
Qed.

Lemma pgi_phaseL : forall (Σ : rts RT) PMc (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(x5 x6 x7 x9 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 : word) F fc (m0 m : mem)
(LV : list (Z * Z)) (A G Dsy nsy Bd L Gv f lo : Z) (k : nat) (og : page) (os1 : stream_st bptr)
(shdr hs bs bodybytes j0 : list byte) (lws gws : list word),
fdfs_only PMc -> mat_stable PMc ->
rw_cells bsegs m A (stream_cells Bd L Gv shdr os1) -> length shdr = 284%nat -> 0 < A ->
rw_cells bsegs m Bd [CB (length bodybytes) bodybytes] -> Z.of_nat (length bodybytes) = os_body_storage os1 ->
u32arr bsegs m L lws -> wpre (os_lacing os1) lws -> Z.of_nat (length lws) = os_lacing_storage os1 ->
u64arr bsegs m Gv gws -> Z.of_nat (length gws) = os_lacing_storage os1 ->
rw_cells bsegs m (bv_unsigned sp + -144) (pgi_frame ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j0 hs) ->
rw_cells bsegs m G (page_cells Dsy og) ->
bytes_at bsegs m (Dsy + pg_hdr og) hs -> bytes_at bsegs m (Dsy + pg_hdr og + pg_header_len og) bs ->
stream_fields_ok os1 -> stream_inv os1 -> os_lacing_returned os1 = 0 -> body_inv os1 -> lacing_vals_ok (os_lacing os1) -> body_pre (os_body os1) bodybytes ->
length hs = (27 + Z.to_nat (znth (ubytes hs) 26))%nat -> Z.of_nat (length hs) = pg_header_len og -> Z.of_nat (length bs) = pg_body_len og ->
zsum (lacing_of (ubytes hs)) <= pg_body_len og -> 0 <= pg_hdr og -> pg_hdr og + pg_header_len og + pg_body_len og <= nsy ->
8 * (os_lacing_storage os1 + znth (ubytes hs) 26 + 33) <= 64512 -> 0 < os_lacing_storage os1 -> 0 < os_body_storage os1 ->
In (Bd, os_body_storage os1) (rt_live RT Σ) -> In (L, 4 * os_lacing_storage os1) (rt_live RT Σ) -> In (Gv, 8 * os_lacing_storage os1) (rt_live RT Σ) ->
In (Dsy, nsy) (rt_live RT Σ) -> Bd <> L -> Bd <> Gv -> L <> Gv -> Dsy <> Bd -> Dsy <> L -> Dsy <> Gv ->
In (f, k) (rt_frames RT Σ) -> f <= A -> A + 408 <= f + fs_size k - 8 -> f <= G -> G + 32 <= f + fs_size k - 8 -> (A + 408 <= G \/ G + 32 <= A) ->
(forall e, In e LV -> In e (rt_live RT Σ) /\ fst e <> Bd /\ fst e <> L /\ fst e <> Gv) ->
Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX -> 0 <= rt_credit RT Σ ->
ART RT Σ m -> mem_inv bsegs m ->
stk bsegs m lo (bv_unsigned sp + -144) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK + 256 <= bv_unsigned sp -> bv_unsigned sp + 16 <= USTACK_TOP ->
bv_unsigned sp mod 16 = 0 ->
rt_pres_fp LV (rt_frames RT Σ) (bv_unsigned sp) [(A, A + 408)] m0 m ->
forall T c,
ASTA RT Σ PMc (eq (MS (pgi_regs (Z_to_bv 64 RA_pgi_lexp) (bv_unsigned sp) gp (Z_to_bv 64 0x638c98) x5 x6 x7 A x9 (Z_to_bv 64 A) (Z_to_bv 64 (znth (ubytes hs) 26 + 1))
x12 x13 x14 x15 x16 x17 (pg_body_len og) (Dsy + pg_hdr og + pg_header_len og) (Dsy + pg_hdr og) x22 hs
(Z_to_bv 64 (ogg_page_serialno (ubytes hs))) x28 x29 x30 x31)
F (Z_to_bv 64 A_os_lacing_expand) fc None m (seg_rom bsegs))) c ->
(forall c' (Σ1 : rts RT) (L1 G1 : Z) (m' : mem) (lws' gws' : list word) (bos' segptr skipped : Z)
(y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
let os3 := pagein_unroll (lacing_expand_res os1 (znth (ubytes hs) 26 + 1)) (ogg_page_pageno (ubytes hs)) in
ASTA RT Σ1 PMc (eq (MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp (Z_to_bv 64 0x638c98) y5 y6 y7 (Z_to_bv 64 A) (Z_to_bv 64 (znth (ubytes hs) 5))
y10 y11 y12 y13 y14 y15 y16 y17
(Z_to_bv 64 (-1)) (Z_to_bv 64 (pg_body_len og - skipped)) (Z_to_bv 64 (Dsy + pg_hdr og + pg_header_len og + skipped))
(Z_to_bv 64 (Dsy + pg_hdr og)) x22 (Z_to_bv 64 segptr) (Z_to_bv 64 (ogg_page_pageno (ubytes hs))) (Z_to_bv 64 bos')
(Z_to_bv 64 (znth (ubytes hs) 26)) (Z_to_bv 64 (znth (ubytes hs) 20 * 65536)) y28 y29 y30 y31)
F (Z_to_bv 64 (if pg_body_len og - skipped =? 0 then 0xc1ce0 else 0xc1cac)) fc None m' (seg_rom bsegs))) c' ->
pagein_skip os3 (ubytes hs) = (bos', segptr, skipped) -> 0 <= skipped <= zsum (lacing_of (ubytes hs)) -> 0 <= segptr <= znth (ubytes hs) 26 ->
(bos' = 0 \/ bos' = Z.land (znth (ubytes hs) 5) 2) ->
ART RT Σ1 m' -> mem_inv bsegs m' -> stk bsegs m' lo (bv_unsigned sp + -144) ->
rw_cells bsegs m' (bv_unsigned sp + -144) (pgi_frame ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j0 hs) ->
rw_cells bsegs m' A (stream_cells Bd L1 G1 shdr os3) ->
rw_cells bsegs m' Bd [CB (length bodybytes) bodybytes] ->
u32arr bsegs m' L1 lws' -> wpre (os_lacing os3) lws' -> Z.of_nat (length lws') = os_lacing_storage os3 ->
u64arr bsegs m' G1 gws' -> Z.of_nat (length gws') = os_lacing_storage os3 ->
rw_cells bsegs m' G (page_cells Dsy og) ->
bytes_at bsegs m' (Dsy + pg_hdr og) hs -> bytes_at bsegs m' (Dsy + pg_hdr og + pg_header_len og) bs ->
rt_pres_fp LV (rt_frames RT Σ) (bv_unsigned sp) [(A, A + 408)] m0 m' ->
stream_fields_ok os3 -> stream_inv os3 -> os_lacing_returned os3 = 0 -> body_inv os3 -> lacing_vals_ok (os_lacing os3) ->
os_lacing_fill os3 + znth (ubytes hs) 26 + 1 <= os_lacing_storage os3 -> os_body_storage os3 = os_body_storage os1 ->
os_lacing_storage os1 <= os_lacing_storage os3 -> 8 * os_lacing_storage os3 <= 64512 -> body_pre (os_body os3) bodybytes ->
In (L1, 4 * os_lacing_storage os3) (rt_live RT Σ1) -> In (G1, 8 * os_lacing_storage os3) (rt_live RT Σ1) -> L1 <> G1 ->
In (Bd, os_body_storage os1) (rt_live RT Σ1) -> In (Dsy, nsy) (rt_live RT Σ1) -> Bd <> L1 -> Bd <> G1 -> Dsy <> L1 -> Dsy <> G1 ->
(forall e, In e LV -> In e (rt_live RT Σ1)) -> (length (rt_live RT Σ1) <= length (rt_live RT Σ))%nat ->
(forall a, aclient LV (rt_frames RT Σ) (bv_unsigned sp) a -> ~ (L1 <= a < L1 + 4 * os_lacing_storage os3)) ->
(forall a, aclient LV (rt_frames RT Σ) (bv_unsigned sp) a -> ~ (G1 <= a < G1 + 8 * os_lacing_storage os3)) ->
((os_lacing_fill os1 < os_lacing_storage os1 - (znth (ubytes hs) 26 + 1) /\ L1 = L /\ G1 = Gv /\ rt_live RT Σ1 = rt_live RT Σ)
\/ (os_lacing_storage os1 - (znth (ubytes hs) 26 + 1) <= os_lacing_fill os1
/\ rt_live RT Σ1 = (G1, 8 * (os_lacing_storage os1 + (znth (ubytes hs) 26 + 1) + 32)) :: (L1, 4 * (os_lacing_storage os1 + (znth (ubytes hs) 26 + 1) + 32))
:: live_remove Gv (live_remove L (rt_live RT Σ)))) ->
rt_frames RT Σ1 = rt_frames RT Σ -> rt_sp0 RT Σ1 = rt_sp0 RT Σ -> rt_credit RT Σ1 = rt_credit RT Σ -> rt_pois RT Σ1 = rt_pois RT Σ ->
realizes bsegs c' T) ->
realizes bsegs c T.
Proof using AF LEXP.
intros Σ PMc ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x5 x6 x7 x9 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 F fc m0 m
LV A G Dsy nsy Bd L Gv f lo k og os1 shdr hs bs bodybytes j0 lws gws
FDO MST OS HL A0 BODY BLEN LAC LPRE LLEN GRA GLEN FR OG HS BS FOK SINV LR0 BINV LOK BPRE LENH HLEN BSLEN HSUM PG0 PGIN LSB LS0 BS0
INB INL ING INSY NBL NBG NLG NSB NSL NSG INF FA1 FA2 FG1 FG2 SEP_AG SUBLV LVM CR0 ART0 MI0 ST0 LOW LOR SPT SPA PF T c Hc Hk.
set (usp := bv_unsigned sp) in *.
destruct (frame_below_lo RT AF Σ m f k lo ART0 INF LOW) as (BF1 & BF2 & BF3).
assert (FSZ : 0 <= fs_size k) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
destruct (live_below_lo RT AF Σ m Bd _ lo ART0 INB LOW) as (B0 & B1 & _).
destruct (live_below_lo RT AF Σ m L _ lo ART0 INL LOW) as (L0 & L1' & _).
destruct (live_below_lo RT AF Σ m Gv _ lo ART0 ING LOW) as (G0' & G1' & _).
destruct (live_below_lo RT AF Σ m Dsy _ lo ART0 INSY LOW) as (S0 & S1 & _).
pose proof (byte_range (nth (Z.to_nat 26) hs (Z_to_bv 8 0))) as H26. rewrite <- (znth_ubytes hs 26) in H26 by lia.
pose proof FOK as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12). unfold int31 in *.
pose proof SINV as (I1 & I2 & I3 & I4 & I5). unfold zlength in I3, I4.
pose proof (wpre_length _ _ LPRE) as LL.
assert (LFS : os_lacing_fill os1 <= os_lacing_storage os1) by lia.
assert (NSY : 0 < nsy) by lia.
assert (LOU : rt_sp0 RT Σ - STACK_WIN <= usp) by (clear - LOW LOR; unfold RT_STACK in *; lia).
assert (SPL : forall a, aclient LV (rt_frames RT Σ) usp a -> usp <= a \/ a < rt_sp0 RT Σ - STACK_WIN).
{ intros a Ha. apply (aclient_split RT AF Σ m usp a ART0). apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros e He; exact (proj1 (SUBLV e He))| auto| apply Z.le_refl]. }
assert (EU : bv_unsigned (Z_to_bv 64 (usp + -144)) = usp + -144) by (apply unsigned_lit; clear - LOR SPT BF3; unfold RT_STACK, USTACK_TOP, SH_HI in *; lia).
assert (SUBLVLG : forall e, In e LV -> In e (live_remove Gv (live_remove L (rt_live RT Σ)))).
{ intros e He. destruct (SUBLV e He) as (X1 & X2 & X3 & X4). apply live_remove_keep; [apply live_remove_keep|]; assumption. }
assert (INBLG : In (Bd, os_body_storage os1) (live_remove Gv (live_remove L (rt_live RT Σ)))) by (apply live_remove_keep; [apply live_remove_keep|]; cbn [fst]; assumption).
assert (INSYLG : In (Dsy, nsy) (live_remove Gv (live_remove L (rt_live RT Σ)))) by (apply live_remove_keep; [apply live_remove_keep|]; cbn [fst]; assumption).
assert (INGL : In (Gv, 8 * os_lacing_storage os1) (live_remove L (rt_live RT Σ))) by (apply live_remove_keep; [exact ING| cbn [fst]; congruence]).
destruct (frame_live_apart RT AF Σ m f k Bd _ ART0 INF INB) as (FLB & _).
destruct (frame_live_apart RT AF Σ m f k Dsy _ ART0 INF INSY) as (FLS & _).
assert (SEP_AB : Bd + os_body_storage os1 <= A \/ A + 408 <= Bd) by (clear - FLB FA1 FA2; lia).
assert (SEP_AS : Dsy + nsy <= A \/ A + 408 <= Dsy) by (clear - FLS FA1 FA2; lia).
assert (SEP_GB : Bd + os_body_storage os1 <= G \/ G + 32 <= Bd) by (clear - FLB FG1 FG2; lia).
assert (SEP_GS : Dsy + nsy <= G \/ G + 32 <= Dsy) by (clear - FLS FG1 FG2; lia).
assert (AT : A + 408 < 2^63) by (clear - FA2 BF1 LOR SPT FSZ; unfold RT_STACK, USTACK_TOP in *; lia).
clear FLB FLS.
cps_norm. cps_hide.
unfold pgi_regs in Hc.
kp_all. unfold kp in OS.
cps_norm.
cps_rt (LEXP Σ PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m A Bd L Gv (znth (ubytes hs) 26 + 1) f lo k os1 shdr lws gws).
all: [> lazymatch goal with
| |- stk _ _ _ _ => rewrite EU; exact ST0
| |- _ mod 16 = 0 => rewrite EU; clear - SPA; Z.div_mod_to_equations; lia
| |- _ => first [ rewrite EU; ulc | ulc ]
end .. | ].
clear OS LAC GRA.
assert (HR : Dsy <= Dsy + pg_hdr og /\ Dsy + pg_hdr og + Z.of_nat (length hs) + Z.of_nat (length bs) <= Dsy + nsy) by (clear - PG0 PGIN HLEN BSLEN; lia).
intros kc2 (Σ1 & L1 & G1 & Hc2 & INL1 & ING1 & NLG1 & CASE & EF1 & ES1 & EC1 & EP1).
ogg_unpackL Hc2 as (m2 & lws2 & gws2 & RS2 & (ART2 & MI2 & ST2) & PRES2 & OS2 & LAC2 & LLEN2 & LPFX2 & GRA2 & GLEN2 & GPFX2). destruct RS2 as (-> & ->).
txe BODY ltac:(cls_live INBLG) ltac:(fun x Hx => clear - Hx SEP_AB BLEN; unfold hid in *; lia).
txe FR ltac:(cls_stack) ltac:(fun x Hx => clear - Hx BF1 FA2 FSZ LOR; lia).
txe OG ltac:(cls_frame INF) ltac:(fun x Hx => clear - Hx SEP_AG; unfold hid in *; lia).
txe HS ltac:(cls_live INSYLG) ltac:(fun x Hx => clear - Hx SEP_AS HR; unfold hid in *; lia).
txe BS ltac:(cls_live INSYLG) ltac:(fun x Hx => clear - Hx SEP_AS HR HLEN; unfold hid in *; lia).

pose proof (lacing_expand_res_fields os1 (znth (ubytes hs) 26 + 1) ltac:(lia) LFS) as (E2b & E2bf & E2br & E2bs & E2bd & E2lf & E2lp & E2lr & E2l & E2pn & E2ls & E2ls').
assert (LS2 : 8 * os_lacing_storage (lacing_expand_res os1 (znth (ubytes hs) 26 + 1)) <= 64512).
{ unfold lacing_expand_res. destruct (_ <? _); cbn [set_blocks os_lacing_storage]; lia. }
assert (X1 : In (Bd, os_body_storage os1) (rt_live RT Σ1) /\ In (Dsy, nsy) (rt_live RT Σ1) /\ Bd <> L1 /\ Bd <> G1 /\ Dsy <> L1 /\ Dsy <> G1
/\ (forall e, In e LV -> In e (rt_live RT Σ1)) /\ (length (rt_live RT Σ1) <= length (rt_live RT Σ))%nat
/\ (forall a, aclient LV (rt_frames RT Σ) usp a -> ~ (L1 <= a < L1 + 4 * os_lacing_storage (lacing_expand_res os1 (znth (ubytes hs) 26 + 1))))
/\ (forall a, aclient LV (rt_frames RT Σ) usp a -> ~ (G1 <= a < G1 + 8 * os_lacing_storage (lacing_expand_res os1 (znth (ubytes hs) 26 + 1))))).
{ destruct CASE as [(FITS & -> & -> & E)|(GROW & E)].
- assert (ES : os_lacing_storage (lacing_expand_res os1 (znth (ubytes hs) 26 + 1)) = os_lacing_storage os1)
by (unfold lacing_expand_res; replace (os_lacing_fill os1 <? _) with true by (symmetry; apply Z.ltb_lt; exact FITS); reflexivity).
rewrite ES in INL1, ING1 |- *. rewrite E.
split; [exact INB|]. split; [exact INSY|]. split; [exact NBL|]. split; [exact NBG|]. split; [exact NSL|]. split; [exact NSG|].
split; [intros e He; exact (proj1 (SUBLV e He))|]. split; [lia|].
split.
+ intros a Ha. apply (live_apart_LV Σ Σ1 m2 L _ LV usp a ART2 INL1); [| exact EF1| exact ES1| exact LOU| exact Ha].
intros e He. rewrite E. destruct (SUBLV e He) as (X1 & X2 & X3 & X4). split; assumption.
+ intros a Ha. apply (live_apart_LV Σ Σ1 m2 Gv _ LV usp a ART2 ING1); [| exact EF1| exact ES1| exact LOU| exact Ha].
intros e He. rewrite E. destruct (SUBLV e He) as (X1 & X2 & X3 & X4). split; assumption.
- assert (ES : os_lacing_storage (lacing_expand_res os1 (znth (ubytes hs) 26 + 1)) = os_lacing_storage os1 + (znth (ubytes hs) 26 + 1) + 32)
by (unfold lacing_expand_res; replace (os_lacing_fill os1 <? _) with false by (symmetry; apply Z.ltb_ge; exact GROW); reflexivity).
rewrite ES in INL1, ING1 |- *.
pose proof (live_second_apart Σ1 m2 _ _ _ _ _ Bd _ ART2 E INBLG) as SBL.
pose proof (live_head_apart Σ1 m2 _ _ _ Bd _ ART2 E (or_intror INBLG)) as SBG.
pose proof (live_second_apart Σ1 m2 _ _ _ _ _ Dsy _ ART2 E INSYLG) as SSL.
pose proof (live_head_apart Σ1 m2 _ _ _ Dsy _ ART2 E (or_intror INSYLG)) as SSG.
rewrite E.
split; [right; right; exact INBLG|]. split; [right; right; exact INSYLG|].
split; [clear - SBL BS0 LS0 H26; lia|]. split; [clear - SBG BS0 LS0 H26; lia|].
split; [clear - SSL NSY LS0 H26; lia|]. split; [clear - SSG NSY LS0 H26; lia|].
split; [intros e He; right; right; exact (SUBLVLG e He)|].
split; [cbn [length]; pose proof (live_remove_length_lt L _ _ INL) as X1; pose proof (live_remove_length_lt Gv _ _ INGL) as X2; lia|].
split.
+ intros a Ha. apply (chunk_apart_aclient Σ Σ1 m2 L1 _ [(G1, 8 * (os_lacing_storage os1 + (znth (ubytes hs) 26 + 1) + 32))]
(live_remove Gv (live_remove L (rt_live RT Σ))) LV usp a ART2);
[exact E| intros e He; right; exact (SUBLVLG e He)| exact EF1| exact ES1| exact LOU| exact Ha].
+ intros a Ha. apply (chunk_apart_aclient Σ Σ1 m2 G1 _ [] ((L1, 4 * (os_lacing_storage os1 + (znth (ubytes hs) 26 + 1) + 32))
:: live_remove Gv (live_remove L (rt_live RT Σ))) LV usp a ART2);
[exact E| intros e He; right; exact (SUBLVLG e He)| exact EF1| exact ES1| exact LOU| exact Ha]. }
destruct X1 as (INB1 & INSY1 & NBL1 & NBG1 & NSL1 & NSG1 & SUB1 & LVM1 & NAL1 & NAG1).

assert (FOK2 : stream_fields_ok (lacing_expand_res os1 (znth (ubytes hs) 26 + 1))).
{ unfold lacing_expand_res. destruct (_ <? _); [exact FOK|]. apply fields_ok_set_blocks; [exact FOK| lia| unfold int31; lia]. }
assert (SINV2 : stream_inv (lacing_expand_res os1 (znth (ubytes hs) 26 + 1))).
{ unfold lacing_expand_res. destruct (_ <? _); [exact SINV|]. apply set_blocks_inv; exact SINV. }
assert (BINV2 : body_inv (lacing_expand_res os1 (znth (ubytes hs) 26 + 1))).
{ unfold lacing_expand_res. destruct (_ <? _); [exact BINV|]. apply set_blocks_body_inv; exact BINV. }
assert (LOK2 : lacing_vals_ok (os_lacing (lacing_expand_res os1 (znth (ubytes hs) 26 + 1)))) by (rewrite E2l; exact LOK).
assert (LFILL2 : zlength (os_lacing (lacing_expand_res os1 (znth (ubytes hs) 26 + 1))) = os_lacing_fill (lacing_expand_res os1 (znth (ubytes hs) 26 + 1)))
by (rewrite E2l, E2lf; unfold zlength; lia).
assert (LPK2 : 0 <= os_lacing_packet (lacing_expand_res os1 (znth (ubytes hs) 26 + 1)) <= os_lacing_fill (lacing_expand_res os1 (znth (ubytes hs) 26 + 1)))
by (rewrite E2lp, E2lf; lia).
assert (Hls2 : os_lacing_fill (lacing_expand_res os1 (znth (ubytes hs) 26 + 1)) + znth (ubytes hs) 26 + 1 <= os_lacing_storage (lacing_expand_res os1 (znth (ubytes hs) 26 + 1)))
by (rewrite E2lf; lia).
pose proof BPRE as (BP1 & BP2). pose proof BINV as (J1 & J2 & J3 & J4). unfold zlength in J1.
assert (Hbf2 : -2^62 <= os_body_fill (lacing_expand_res os1 (znth (ubytes hs) 26 + 1)) < 2^62) by (rewrite E2bf; lia).

cps_seg pgi_e1.
lazymatch type of POST with ?x = _ => subst x end.
clear Hc.

assert (LOW1 : rt_sp0 RT Σ1 - STACK_WIN <= lo) by (rewrite ES1; exact LOW).
assert (INF1 : In (f, k) (rt_frames RT Σ1)) by (rewrite EF1; exact INF).
destruct (live_below_lo RT AF Σ1 m2 L1 _ lo ART2 INL1 LOW1) as (L10 & L11 & _).
destruct (live_below_lo RT AF Σ1 m2 G1 _ lo ART2 ING1 LOW1) as (G10 & G11 & _).
destruct (frame_live_apart RT AF Σ1 m2 f k L1 _ ART2 INF1 INL1) as (FLL1 & _).
destruct (frame_live_apart RT AF Σ1 m2 f k G1 _ ART2 INF1 ING1) as (FLG1 & _).
set (ls2 := os_lacing_storage (lacing_expand_res os1 (znth (ubytes hs) 26 + 1))) in *.
assert (SEP_AL1 : L1 + 4 * ls2 <= A \/ A + 408 <= L1) by (clear - FLL1 FA1 FA2; lia).
assert (SEP_AGv1 : G1 + 8 * ls2 <= A \/ A + 408 <= G1) by (clear - FLG1 FA1 FA2; lia).
assert (SEP_GL1 : L1 + 4 * ls2 <= G \/ G + 32 <= L1) by (clear - FLL1 FG1 FG2; lia).
assert (SEP_GG1 : G1 + 8 * ls2 <= G \/ G + 32 <= G1) by (clear - FLG1 FG1 FG2; lia).
clear FLL1 FLG1.
pose proof (live_apart2 Σ1 m2 L1 _ G1 _ ART2 INL1 ING1 ltac:(congruence)) as SEP_LG1.
pose proof (live_apart2 Σ1 m2 Dsy _ L1 _ ART2 INSY1 INL1 ltac:(congruence)) as SEP_SL1.
pose proof (live_apart2 Σ1 m2 Dsy _ G1 _ ART2 INSY1 ING1 ltac:(congruence)) as SEP_SG1.
pose proof (live_apart2 Σ1 m2 Bd _ L1 _ ART2 INB1 INL1 ltac:(congruence)) as SEP_BL1.
pose proof (live_apart2 Σ1 m2 Bd _ G1 _ ART2 INB1 ING1 ltac:(congruence)) as SEP_BG1.
assert (SEP_LG1' : L1 + 4 * ls2 <= G1 \/ G1 + 8 * ls2 <= L1) by (clear - SEP_LG1; lia).
assert (SEP_HL1 : Dsy + pg_hdr og + Z.of_nat (length hs) <= L1 \/ L1 + 4 * ls2 <= Dsy + pg_hdr og) by (clear - SEP_SL1 HR; lia).
assert (SEP_HG1 : Dsy + pg_hdr og + Z.of_nat (length hs) <= G1 \/ G1 + 8 * ls2 <= Dsy + pg_hdr og) by (clear - SEP_SG1 HR; lia).
assert (SEP_AH : Dsy + pg_hdr og + Z.of_nat (length hs) <= A \/ A + 408 <= Dsy + pg_hdr og) by (clear - SEP_AS HR; unfold hid in *; lia).
assert (TOPL1 : L1 + 4 * ls2 < 2^63) by (clear - L11 LOR SPT; lia).
assert (TOPG1 : G1 + 8 * ls2 < 2^63) by (clear - G11 LOR SPT; lia).
assert (TOPH : Dsy + pg_hdr og + Z.of_nat (length hs) < 2^63) by (clear - HR S1 LOR SPT; lia).
assert (HH : 0 <= Dsy + pg_hdr og) by (clear - HR S0; lia).
assert (LOSP : lo + 144 <= bv_unsigned sp) by (clear - LOR; lia).
assert (ALO : A + 408 <= lo) by (clear - FA2 BF1; lia).
assert (HLO : Dsy + pg_hdr og + Z.of_nat (length hs) <= lo) by (clear - HR S1; lia).
assert (LPRE2 : wpre (os_lacing (lacing_expand_res os1 (znth (ubytes hs) 26 + 1))) lws2) by (rewrite E2l; exact (wpre_firstn_ext _ _ _ LPRE LPFX2)).
cps_hide.
unfold pgi_frame in FR.
cps_seg (X10o.pi_unroll A Bd L1 G1 (Dsy + pg_hdr og) lo shdr hs (lacing_expand_res os1 (znth (ubytes hs) 26 + 1)) lws2 gws2
ra sp gp (Z_to_bv 64 0x638c98) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 RA_pgi_lexp) j0
LENH H26 HL FOK2 Hls2 LFILL2 LPK2 LOK2 A0 L10 G10 HH TOPL1 TOPG1 TOPH LOSP ALO SEP_AL1 SEP_AGv1 SEP_AH L11 G11 HLO SEP_LG1' SEP_HL1 SEP_HG1).
unfold X10o.unroll_post in POST.
destruct POST as (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & m3 & lws3 & -> & MU3 & WM3 & MI3 & OS3 & LAC3 & LPRE3 & LLEN3 & GRA3 & FR3 & HS3).
clear OS2 LAC2 GRA2 FR HS.

assert (ART3 : ART RT Σ1 m3).
{ apply (af_frame RT AF Σ1 m2 m3 lo ART2 LOW1); [| exact WM3].
intros a Ha. apply MU3. cbn [outside]. repeat split; intros Hin; apply Ha; change (bv_unsigned sp) with usp in Hin.
- left. unfold USTACK_TOP. clear - Hin LOR SPT. lia.
- right; right; right; left. exists f, k. split; [exact INF1| clear - Hin FA1 FA2; lia].
- right; right; left. exists L1, (4 * ls2). split; [exact INL1| clear - Hin; lia].
- right; right; left. exists G1, (8 * ls2). split; [exact ING1| clear - Hin; lia]. }
assert (PF3 : rt_pres_fp LV (rt_frames RT Σ) usp [(A, A + 408)] m0 m3).
{ apply (pres_fp_trans _ _ _ _ m0 m2 m3 PF). apply (pres_fp_of_munch _ _ _ _ _ m2 m3 MU3).
intros x Hx Ho. cbn [outside] in Ho |- *. destruct Ho as (Ho & _). change (bv_unsigned sp) with usp.
pose proof (SPL x Hx) as Sx. pose proof (NAL1 x Hx) as Lx. pose proof (NAG1 x Hx) as Gx.
split; [clear - Sx LOW LOR; lia|]. split; [exact Ho|]. split; [exact Lx|]. split; [exact Gx| exact I]. }
clear PF ART2 MI2. rename PF3 into PF.
pose proof (rw_cells_transport bsegs _ m2 m3 Bd _ BODY MU3 WM3) as BODY3.
pose proof (rw_cells_transport bsegs _ m2 m3 G _ OG MU3 WM3) as OG3.
pose proof (bytes_at_transport bsegs _ m2 m3 _ bs BS MU3) as BS3.
unfold page_cells in OG3.
cbn [disjoint_from cells_size csize Nat.add] in BODY3, OG3, BS3.
specialize (BODY3 ltac:(repeat split; [clear - B1 BLEN LOR; lia| clear - SEP_AB BLEN; unfold hid in *; lia| clear - SEP_BL1 BLEN; unfold hid in *; lia| clear - SEP_BG1 BLEN; unfold hid in *; lia])).
specialize (OG3 ltac:(repeat split; [clear - FG2 BF1 LOR; lia| clear - SEP_AG; unfold hid in *; lia| clear - SEP_GL1; unfold hid in *; lia| clear - SEP_GG1; unfold hid in *; lia])).
specialize (BS3 ltac:(repeat split; [clear - HR S1 LOR HLEN; lia| clear - SEP_AS HR HLEN; unfold hid in *; lia| clear - SEP_SL1 HR HLEN; unfold hid in *; lia| clear - SEP_SG1 HR HLEN; unfold hid in *; lia])).
clear BODY OG BS.
set (os2 := lacing_expand_res os1 (znth (ubytes hs) 26 + 1)) in *.
assert (LR2 : os_lacing_returned os2 = 0) by (rewrite E2lr; exact LR0).
pose proof (pagein_unroll_inv os2 (ogg_page_pageno (ubytes hs)) SINV2 LR2) as (SINV3 & LR3 & ELV3 & EGV3 & EBD3 & ELS3 & EBS3 & HLF3).
pose proof (pagein_unroll_body_inv os2 (ogg_page_pageno (ubytes hs)) SINV2 LR2 BINV2) as (BINV3 & HBF3 & HBR3).
pose proof (body_inv_fill_nonneg _ BINV3) as HBF3'.
pose proof SINV3 as (K1 & K2 & K3 & K4 & K5). unfold zlength in K3, K4.
assert (FOK3 : stream_fields_ok (pagein_unroll os2 (ogg_page_pageno (ubytes hs)))).
apply fields_ok_unroll; [exact FOK2| exact SINV2| |].
1: (clear - HBF3 HBF3'; lia).
1: (clear - Hls2 LS2 H26; lia).
pose proof (lacing_vals_ok_unroll os2 (ogg_page_pageno (ubytes hs)) LOK2) as LOK3.
set (os3 := pagein_unroll os2 (ogg_page_pageno (ubytes hs))) in *.
assert (LFILL3 : zlength (os_lacing os3) = os_lacing_fill os3) by (clear - K3; unfold zlength; lia).
assert (HBP : 0 <= Dsy + pg_hdr og + pg_header_len og) by (clear - HR HLEN S0; lia).
assert (TOPB : Dsy + pg_hdr og + pg_header_len og + pg_body_len og < 2^63) by (clear - HR HLEN BSLEN S1 LOR SPT; lia).

cps_seg (X10n.pi_skip A Bd L1 G1 (Dsy + pg_hdr og) (Dsy + pg_hdr og + pg_header_len og) (pg_body_len og) shdr hs os3 lws3 m3 sp gp (Z_to_bv 64 0x638c98) F fc
(Z_to_bv 64 RA_pgi_lexp) (ogg_page_pageno (ubytes hs)) y5 y6 y7 y14 y15 y16 y17 (Z_to_bv 64 (-1)) x22 (Z_to_bv 64 (znth (ubytes hs) 20 * 65536)) y28 _ _ _
LENH H26 HL FOK3 LFILL3 LOK3 LPRE3 HBP HSUM TOPB OS3 LAC3 HS3).
revert POST. destruct (pagein_skip os3 (ubytes hs)) as [[bos' segptr] skipped] eqn:ESK. intros POST.
unfold X10n.skip_exit in POST.
destruct POST as (z10 & z11 & z12 & z13 & -> & Hsk & Hseg & Hbos).
unfold ls2 in *.
assert (Hls2s : os_lacing_fill os2 + (znth (ubytes hs) 26 + 1) < os_lacing_storage os2).
{ unfold os2, lacing_expand_res. destruct (Z.ltb_spec (os_lacing_fill os1) (os_lacing_storage os1 - (znth (ubytes hs) 26 + 1))); cbv iota; unfold set_blocks; cbn [os_lacing_fill os_lacing_storage]; clear - LFS H26 H; lia. }
assert (BPRE3 : body_pre (os_body os3) bodybytes).
{ destruct (unroll_body os2 (ogg_page_pageno (ubytes hs))) as [E|E]; fold os3 in E.
- rewrite E, E2b. exact BPRE.
- rewrite E, E2b. apply body_pre_ztake; [exact BPRE| lia|]. unfold zlength. rewrite <- E2b. clear - HBF3 J1 E2bf E2b. rewrite E2b. lia. }
eapply (Hk _ Σ1 L1 G1 m3 lws3 gws2 bos' segptr skipped); try eassumption; try reflexivity; rewrite ?ELS3, ?EBS3.
all: try eassumption.
- apply (stk_transport bsegs _ m2 m3 lo (usp + -144) ST2 MU3 WM3). intros x Hx. left. cbn [outside]. change (bv_unsigned sp) with usp.
repeat split; clear - Hx ALO L11 G11; lia.
- clear - HLF3 Hls2s. lia.
Qed.

Lemma ret_body_fields : forall os : stream_st bptr,
os_lacing (ret_body os) = os_lacing os /\ os_lacing_storage (ret_body os) = os_lacing_storage os /\ os_lacing_fill (ret_body os) = os_lacing_fill os /\
os_lacing_packet (ret_body os) = os_lacing_packet os /\ os_lacing_returned (ret_body os) = os_lacing_returned os /\ os_body_storage (ret_body os) = os_body_storage os.
Proof. intros os. unfold ret_body. destruct (negb (os_body_returned os =? 0)); cbn; repeat split; reflexivity. Qed.
Lemma ret_body_fields_ok : forall os : stream_st bptr, stream_fields_ok os -> 0 <= os_body_returned os <= os_body_fill os -> stream_fields_ok (ret_body os).
Proof.
intros os FOK BR. pose proof FOK as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12).
unfold ret_body. destruct (negb (os_body_returned os =? 0)); [| exact FOK].
unfold stream_fields_ok, set_body. cbn. unfold int31 in *. repeat split; try tauto; lia.
Qed.
Lemma ret_lacing_body : forall os : stream_st bptr, os_body (ret_lacing os) = os_body os /\ os_body_storage (ret_lacing os) = os_body_storage os.
Proof. intros os. unfold ret_lacing. destruct (negb (os_lacing_returned os =? 0)); cbn; split; reflexivity. Qed.

Theorem ogg_stream_pagein_ok : ogg_stream_pagein_cps.
Proof using AF MMOV MCPY LEXP BEXP.
intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m A G Dsy nsy Bd L Gv f lo k og os shdr hs bs bodybytes lws gws q q' r
FDO MST -> -> -> RUN OS HL A0 ARR FOK SINV BINV LOK BDN LVN GVN SLV OG G0 HS BS LENH HLEN BSLEN HSUM PG0 PGIN INSY NSB NSL NSG LSB BSB LS0 BS0
INF FA1 FA2 FG1 FG2 SEP_AG LVM CR0 ART0 MI0 ST0 LOW LOR SPT SPA.
intros T c Hc Hk.
set (usp := bv_unsigned sp) in *.
assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
unfold entry_st in Hc. rewrite ESP in Hc.
set (hdr := ubytes hs) in *.
pose proof (byte_range (nth (Z.to_nat 26) hs (Z_to_bv 8 0))) as H26. rewrite <- (znth_ubytes hs 26) in H26 by lia. fold hdr in H26.
pose proof (byte_range (nth (Z.to_nat 4) hs (Z_to_bv 8 0))) as H4. rewrite <- (znth_ubytes hs 4) in H4 by lia. fold hdr in H4.
assert (HBOK : bytes_ok (lacing_of hdr)) by (apply bytes_ok_zslice; apply ubytes_ok).
pose proof FOK as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12). unfold int31 in F4, F5, F6, F7.

destruct (pagein_prun os hdr (ubytes bs) q r q' RUN BDN LVN GVN HBOK ltac:(rewrite zlength_ubytes, BSLEN; exact HSUM) ltac:(lia) ltac:(unfold bptr in *; lia) ltac:(unfold bptr in *; lia) ltac:(unfold bptr in *; lia)
ltac:(rewrite zlength_ubytes, BSLEN; unfold bptr in *; lia)) as (-> & ->).
subst hdr.
destruct ARR as (BODY & BLEN & BPRE & LAC & LPRE & LLEN & GRA & GLEN).
pose proof SINV as (I1 & I2 & I3 & I4 & I5).
pose proof BINV as (J1 & J2 & J3 & J4). pose proof (body_inv_returned_le_fill os BINV) as BRF.
assert (LOU : rt_sp0 RT Σ - STACK_WIN <= usp) by (clear - LOW LOR; unfold RT_STACK in *; lia).
destruct (frame_below_lo RT AF Σ m f k lo ART0 INF LOW) as (BF1 & BF2 & BF3).
assert (FSZ : 0 <= fs_size k) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
assert (ALO : A + 408 <= lo) by (clear - FA2 BF1 FSZ; lia).
pose proof SLV as (INB & INL & ING & NBL & NBG & NLG).
set (LV := pgi_rest Bd L Gv (rt_live RT Σ)) in *.
assert (NAB : forall a, aclient LV (rt_frames RT Σ) usp a -> ~ (Bd <= a < Bd + os_body_storage os))
by (intros a Ha; exact (rest_apart Σ m Bd L Gv Bd _ usp a ART0 INB (or_introl eq_refl) LOU Ha)).
assert (NAL : forall a, aclient LV (rt_frames RT Σ) usp a -> ~ (L <= a < L + 4 * os_lacing_storage os))
by (intros a Ha; exact (rest_apart Σ m Bd L Gv L _ usp a ART0 INL (or_intror (or_introl eq_refl)) LOU Ha)).
assert (NAG : forall a, aclient LV (rt_frames RT Σ) usp a -> ~ (Gv <= a < Gv + 8 * os_lacing_storage os))
by (intros a Ha; exact (rest_apart Σ m Bd L Gv Gv _ usp a ART0 ING (or_intror (or_intror eq_refl)) LOU Ha)).
assert (SUBLV : forall e, In e LV -> In e (rt_live RT Σ)) by (intros e He; exact (pgi_rest_sub _ _ _ _ _ He)).
assert (SPL : forall a, aclient LV (rt_frames RT Σ) usp a -> usp <= a \/ a < rt_sp0 RT Σ - STACK_WIN).
{ intros a Ha. apply (aclient_split RT AF Σ m usp a ART0). apply (aclient_mono _ _ _ _ _ _ _ Ha); [exact SUBLV| auto| apply Z.le_refl]. }
assert (LBL : Z.of_nat (length (u32s lws)) = 4 * os_lacing_storage os) by (rewrite u32s_length; lia).
assert (LBG : Z.of_nat (length (u64s gws)) = 8 * os_lacing_storage os) by (rewrite u64s_length; lia).
assert (LENH27 : (27 <= length hs)%nat) by lia.

pose proof (u8arr_rw_CB m L (u32s lws)) as XL. pose proof (u8arr_rw_CB m Gv (u64s gws)) as XG.
refine (pgi_phaseA Σ PMc ra gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m A G Dsy nsy Bd L Gv f lo usp k og os shdr hs bs bodybytes lws gws
FDO MST OS HL A0 BODY BLEN BPRE (proj1 XL (u32arr_u8 _ _ _ LAC)) LBL (proj1 XG (u64arr_u8 _ _ _ GRA)) LBG FOK J1 (conj J2 BRF) ltac:(clear - BSB PG0 BSLEN; lia) SLV OG G0 HS BS LENH27 HLEN BSLEN PG0 PGIN INSY NSB
INF FA1 FA2 FG1 FG2 SEP_AG NAB ART0 MI0 ST0 LOW LOR SPT SPA T c Hc _).
clear XL XG.
intros c1 m1 bodybytes1 j0 v25 v22 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 Hc1 ART1 MI1 ST1 FR1 OS1 BODY1 BLEN1 BPRE1 LAC1 GRA1 OG1 HS1 BS1 V25 V22 ESER PF1.

destruct (ret_body_fields os) as (RB1 & RB2 & RB3 & RB4 & RB5 & RB6).
apply u8arr_rw_CB in BODY1. apply u8arr_rw_CB, u8_u32arr in LAC1. apply u8arr_rw_CB, u8_u64arr in GRA1.
rewrite <- RB5 in Hc1.
refine (pgi_phaseB Σ PMc x1 gp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m m1 A G Dsy nsy Bd L Gv f lo usp v25 v22 k og
(ret_body os) shdr hs bs bodybytes1 j0 lws gws FDO MST OS1 HL A0 BODY1 ltac:(rewrite RB6; exact BLEN1) LAC1 ltac:(rewrite RB1; exact LPRE) ltac:(rewrite RB2; exact LLEN)
GRA1 ltac:(rewrite RB2; exact GLEN) (ret_body_fields_ok os FOK (conj J2 BRF)) ltac:(rewrite RB1, RB3; exact I3) ltac:(rewrite RB5, RB4; exact I1) ltac:(rewrite RB4, RB3; exact I2)
ltac:(rewrite RB2; clear - LSB H26; lia) ltac:(unfold stream_live; rewrite RB2, RB6; exact SLV) FR1 OG1 G0 HS1 BS1 LENH27 HLEN BSLEN PG0 PGIN INSY NSL NSG
INF FA1 FA2 FG1 FG2 SEP_AG ltac:(rewrite RB2; exact NAL) ltac:(rewrite RB2; exact NAG) V25 V22 ESER ART1 MI1 ST1 LOW LOR SPT SPA PF1 T c1 Hc1 _).
clear Hc Hc1.
intros c2 m2 lws2 gws2 y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 Hc2 ART2 MI2 ST2 FR2 OS2 BODY2 LAC2 LPRE2 LLEN2 GRA2 GLEN2 OG2 HS2 BS2 PF2.
rewrite <- pagein_returned_eq in OS2, LPRE2. rewrite RB2 in LLEN2, GLEN2.

pose proof (pagein_returned_inv os SINV) as (SINV1 & LR1 & ELV1 & EGV1 & EBD1 & ELS1 & EBS1 & ESN1 & EPN1).
pose proof (pagein_returned_body_inv os SINV BINV) as (BINV1 & BR1 & BFR1 & LF1).
pose proof (fields_ok_returned os FOK SINV BRF) as FOK1.
pose proof (lacing_vals_ok_returned os LOK) as LOK1.
pose proof (ret_lacing_body (ret_body os)) as (RL1 & RL2). rewrite <- pagein_returned_eq in RL1, RL2.
set (os1 := pagein_returned os) in *.

rewrite stream_cells_r_eq in OS2.
cps_seg (pgi_chk A Bd (os_body_fill os1) (os_body_returned os1) L Gv (os_lacing_fill os1) (os_lacing_packet os1) (os_lacing_returned os1) usp lo
(pg_body_len og) (Dsy + pg_hdr og + pg_header_len og) (Dsy + pg_hdr og) shdr hs j0 os1).
destruct POST as (m3 & MU3 & WM3 & MI3 & [(t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & -> & ST3 & FAILC) | (x10' & -> & EM3 & EX10 & ESER' & CVER)]).
-
destruct (live_below_lo RT AF Σ m2 Bd _ lo ART2 INB LOW) as (B0 & B1 & _).
destruct (live_below_lo RT AF Σ m2 L _ lo ART2 INL LOW) as (L0 & L1 & _).
destruct (live_below_lo RT AF Σ m2 Gv _ lo ART2 ING LOW) as (G0' & G1 & _).
destruct (live_below_lo RT AF Σ m2 Dsy _ lo ART2 INSY LOW) as (S0 & S1 & _).
assert (ART3 : ART RT Σ m3).
{ apply (af_frame RT AF Σ m2 m3 lo ART2 LOW); [| exact WM3].
intros a Ha. apply MU3. cbn [outside]. split; [| exact I]. intros Hin. apply Ha. left. clear - Hin LOR SPT; unfold USTACK_TOP, RT_STACK in *; lia. }
assert (PF3 : rt_pres_fp LV (rt_frames RT Σ) usp [(A, A + 408)] m m3).
{ apply (pres_fp_trans _ _ _ _ m m2 m3 PF2). apply (pres_fp_of_munch _ _ _ _ _ m2 m3 MU3).
intros x Hx Ho. cbn [outside] in Ho |- *. pose proof (SPL x Hx) as Sx. split; [clear - Sx LOW LOR; unfold STACK_WIN, RT_STACK in *; lia| exact I]. }
unfold stream_cells_r in OS2.
pose proof (rw_cells_transport bsegs _ m2 m3 A _ OS2 MU3 WM3 ltac:(cbn [disjoint_from cells_size csize Nat.add]; split; [left; clear - ALO LOR; unfold RT_STACK in *; lia| exact I])) as OS3.
pose proof (rw_cells_transport bsegs _ m2 m3 Bd _ BODY2 MU3 WM3 ltac:(cbn [disjoint_from cells_size csize Nat.add]; split; [left; clear - B1 BLEN1 LOR; unfold RT_STACK in *; lia| exact I])) as BODY3.
pose proof (u32arr_transport bsegs _ m2 m3 L _ LAC2 MU3 WM3 ltac:(cbn [disjoint_from]; split; [left; clear - L1 LLEN2 LOR; unfold RT_STACK in *; lia| exact I])) as LAC3.
pose proof (u64arr_transport bsegs _ m2 m3 Gv _ GRA2 MU3 WM3 ltac:(cbn [disjoint_from]; split; [left; clear - G1 GLEN2 LOR; unfold RT_STACK in *; lia| exact I])) as GRA3.
unfold page_cells in OG2.
pose proof (rw_cells_transport bsegs _ m2 m3 G _ OG2 MU3 WM3 ltac:(cbn [disjoint_from cells_size csize Nat.add]; split; [left; clear - FG2 BF1 LOR; unfold RT_STACK in *; lia| exact I])) as OG3.
clear OS2 BODY2 LAC2 GRA2 OG2 FR2 HS2 BS2.
assert (ERES : pagein_res os (ubytes hs) (ubytes bs) = (-1, os1)).
{ unfold pagein_res. cbv zeta. fold os1. destruct FAILC as [NE|NV].
- replace (ogg_page_serialno (ubytes hs) =? os_serialno os1) with false by (symmetry; apply Z.eqb_neq; exact NE). reflexivity.
- destruct (negb (ogg_page_serialno (ubytes hs) =? os_serialno os1)); [reflexivity|].
unfold ogg_page_version. replace (0 <? znth (ubytes hs) 4) with true by (symmetry; apply Z.ltb_lt; clear - NV H4; lia). reflexivity. }
assert (POK : pgi_ok os (ubytes hs) = false).
{ unfold pgi_ok. fold os1. destruct FAILC as [NE|NV].
- replace (ogg_page_serialno (ubytes hs) =? os_serialno os1) with false by (symmetry; apply Z.eqb_neq; exact NE). reflexivity.
- unfold ogg_page_version. replace (0 <? znth (ubytes hs) 4) with true by (symmetry; apply Z.ltb_lt; clear - NV H4; lia). apply andb_false_r. }
apply Hk. exists Σ, Bd, L, Gv. rewrite ERES. cbn [fst snd].
split; [| split; [reflexivity| split; [reflexivity| split; [| split; [| split; [| repeat split; reflexivity]]]]]].
+ eapply ASTA_conseq; [eassumption|]. intros ms <-. exists m3, bodybytes1, lws2, gws2.
split; [unfold ret_stL; do 16 eexists; split; [rewrite <- ESP; reflexivity| split; reflexivity]|].
split; [split; [exact ART3| split; [exact MI3| exact ST3]]|].
split; [exact PF3|]. split; [exact OS3|].
unfold stream_arrays. split; [apply u8arr_rw_CB; exact BODY3|]. split; [rewrite EBS1; exact BLEN1|]. split; [rewrite RL1; exact BPRE1|].
split; [exact LAC3|]. split; [exact LPRE2|]. split; [rewrite ELS1; exact LLEN2|]. split; [exact GRA3| rewrite ELS1; exact GLEN2].
+ unfold stream_live. rewrite EBS1, ELS1. exact SLV.
+ unfold pagein_live. rewrite POK. reflexivity.
+ unfold pagein_same. rewrite POK. split; [intros _; repeat split; reflexivity|]. split; intros E; discriminate E.
-
subst m3.
assert (SUBLV3 : forall e, In e LV -> In e (rt_live RT Σ) /\ fst e <> Bd /\ fst e <> L /\ fst e <> Gv) by (intros e He; apply pgi_rest_In in He; exact He).
refine (pgi_phaseL Σ PMc ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y5 y6 y7 y9 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 v22) y28 y29 y30 y31 F fc m m2
LV A G Dsy nsy Bd L Gv f lo k og os1 shdr hs bs bodybytes1 j0 lws2 gws2
FDO MST OS2 HL A0 BODY2 ltac:(rewrite EBS1; exact BLEN1) LAC2 LPRE2 ltac:(rewrite ELS1; exact LLEN2) GRA2 ltac:(rewrite ELS1; exact GLEN2)
FR2 OG2 HS2 BS2 FOK1 SINV1 LR1 BINV1 LOK1 ltac:(rewrite RL1; exact BPRE1) LENH HLEN BSLEN HSUM PG0 PGIN
ltac:(rewrite ELS1; exact LSB) ltac:(rewrite ELS1; exact LS0) ltac:(rewrite EBS1; exact BS0)
ltac:(rewrite EBS1; exact INB) ltac:(rewrite ELS1; exact INL) ltac:(rewrite ELS1; exact ING) INSY NBL NBG NLG NSB NSL NSG
INF FA1 FA2 FG1 FG2 SEP_AG SUBLV3 LVM CR0 ART2 MI2 ST2 LOW LOR SPT SPA PF2 T c0 Hc _).
intros c4 Σ1 L1 G1 m4 lws4 gws4 bos' segptr skipped z1 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 os3 Hc4 ESK Hsk Hseg Hbos ART4 MI4 ST4 FR4 OS4 BODY4
LAC4 LPRE4 LLEN4 GRA4 GLEN4 OG4 HS4 BS4 PF4 FOK3 SINV3 LR3 BINV3 LOK3 Hls3 EBS3 ELS3 LS3B BPRE3 INL4 ING4 NLG4 INB4 INSY4 NBL4 NBG4 NSL4 NSG4 SUB4 LVM4 NAL4 NAG4
CASEL EF4 ES4 EC4 EP4.
assert (POK : pgi_ok os (ubytes hs) = true).
{ unfold pgi_ok. fold os1. rewrite ESER', Z.eqb_refl. unfold ogg_page_version. rewrite CVER. reflexivity. }
assert (E3 : pgi_os3 os (ubytes hs) = os3) by reflexivity.
assert (LIVE1 : forall Bd', pagein_live (rt_live RT Σ) os (ubytes hs) (ubytes bs) Bd L Gv Bd' L1 G1
= let l1 := rt_live RT Σ1 in
let bodysize := pg_body_len og - skipped in
if (bodysize =? 0) || (os_body_fill os3 <? os_body_storage os3 - bodysize) then l1 else (Bd', os_body_storage os3 + bodysize + 1024) :: live_remove Bd l1).
{ intros Bd'. unfold pagein_live. rewrite POK. cbv zeta. fold os1. rewrite E3, ESK. cbn [snd]. rewrite zlength_ubytes, BSLEN.
destruct CASEL as [(C1 & -> & -> & E)|(C1 & E)]; rewrite E.
- replace (os_lacing_fill os1 <? os_lacing_storage os1 - (znth (ubytes hs) 26 + 1)) with true by (symmetry; apply Z.ltb_lt; exact C1). reflexivity.
- replace (os_lacing_fill os1 <? os_lacing_storage os1 - (znth (ubytes hs) 26 + 1)) with false by (symmetry; apply Z.ltb_ge; exact C1). reflexivity. }
pose proof SINV3 as (K1 & K2 & K3 & K4 & K5).
assert (LOW4 : rt_sp0 RT Σ1 - STACK_WIN <= lo) by (rewrite ES4; exact LOW).
assert (SPL4 : forall a, aclient LV (rt_frames RT Σ) (bv_unsigned sp) a -> bv_unsigned sp <= a \/ a < rt_sp0 RT Σ1 - STACK_WIN) by (intros a Ha; rewrite ES4; exact (SPL a Ha)).
destruct (Z.eqb_spec (pg_body_len og - skipped) 0) as [BZ|BNZ].
+
replace (pg_body_len og - skipped =? 0) with true in Hc4 by (symmetry; apply Z.eqb_eq; exact BZ). cbv iota in Hc4.
refine (pgi_phaseF Σ1 PMc ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 z1 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 _ _ _ _ _ z28 z29 z30 z31 F fc m m4
LV (rt_frames RT Σ) A G Dsy nsy Bd L1 G1 f lo segptr bos' k og os3 shdr hs bs bodybytes1 j0 lws4 gws4
FDO MST OS4 HL A0 BODY4 ltac:(rewrite EBS3, EBS1; exact BLEN1) LAC4 LPRE4 LLEN4 GRA4 GLEN4 FR4 OG4 HS4 BS4 FOK3 ltac:(clear - Hls3 Hseg; lia) Hseg Hbos
K3 ltac:(clear - K1 K2; lia) LOK3 LENH HLEN BSLEN PG0 PGIN ltac:(rewrite EBS3; exact INB4) INL4 ING4 INSY4 NBL4 NBG4 NLG4 NSL4 NSG4 EF4
INF FA1 FA2 FG1 FG2 SUB4 SPL4 NAL4 NAG4 ART4 MI4 ST4 LOW4 LOR SPT PF4 T c4 Hc4 _).
intros c5 Hc5. apply Hk. exists Σ1, Bd, L1, G1.
assert (ERES : pagein_res os (ubytes hs) (ubytes bs) = (0, pagein_segments os3 (ubytes hs) bos' segptr)).
{ unfold pagein_res. cbv zeta. fold os1. rewrite ESER', Z.eqb_refl. cbn [negb]. unfold ogg_page_version. rewrite CVER. replace (0 <? 0) with false by reflexivity.
rewrite E3, ESK. rewrite zlength_ubytes, BSLEN, BZ. reflexivity. }
rewrite ERES. cbn [fst snd].
pose proof (segments_shape os3 (ubytes hs) bos' segptr HBOK ltac:(rewrite zlength_lacing_of by lia; lia) ltac:(clear - K2; lia)) as SH. cbv zeta in SH.
destruct SH as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13 & Q14 & Q15 & Q16 & Q17).
split; [| split; [reflexivity| split; [reflexivity| split; [| split; [| split; [| repeat split; assumption]]]]]].
* eapply ASTA_conseq; [exact Hc5|]. intros ms (m5 & lws5 & gws5 & RS5 & RA5 & PF5 & OS5 & BODY5 & LAC5 & LPRE5 & LLEN5 & GRA5 & GLEN5).
exists m5, bodybytes1, lws5, gws5.
split; [exact RS5|]. split; [exact RA5|]. split; [exact PF5|]. split; [exact OS5|].
unfold stream_arrays. rewrite Q4, Q5, Q7.
split; [apply u8arr_rw_CB; exact BODY5|]. split; [rewrite EBS3, EBS1; exact BLEN1|]. split; [exact BPRE3|].
split; [exact LAC5|]. split; [exact LPRE5|]. split; [exact LLEN5|]. split; [exact GRA5| exact GLEN5].
* unfold stream_live. rewrite Q4, Q5, EBS3. repeat split; assumption.
* rewrite (LIVE1 Bd). cbv zeta. rewrite BZ. reflexivity.
* unfold pagein_same. rewrite POK. split; [intros E; discriminate E|]. split.
-- intros _ C. fold os1 in C. destruct CASEL as [(C1 & E1 & E2 & _)|(C1 & _)]; [exact (conj E1 E2)|]. exfalso. apply Z.ltb_lt in C. lia.
-- intros _ _. reflexivity.
+
replace (pg_body_len og - skipped =? 0) with false in Hc4 by (symmetry; apply Z.eqb_neq; exact BNZ). cbv iota in Hc4.
assert (BSRC : bytes_at bsegs m4 (Dsy + pg_hdr og + pg_header_len og + skipped) (firstn (Z.to_nat (pg_body_len og - skipped)) (skipn (Z.to_nat skipped) bs))).
{ pose proof (bytes_at_sub m4 _ bs (Z.to_nat skipped) (Z.to_nat (pg_body_len og - skipped)) BS4 ltac:(clear - Hsk HSUM BSLEN BNZ; lia)) as X.
rewrite Z2Nat.id in X by lia. exact X. }
pose proof BINV3 as (J1' & J2' & J3' & J4'). pose proof BPRE3 as (BP1' & BP2'). unfold zlength in J1'.
pose proof (body_inv_fill_nonneg _ BINV3) as BF30.
assert (NPOS : 0 < pg_body_len og - skipped) by (clear - BNZ Hsk HSUM; lia).
assert (LSRC : Z.of_nat (length (firstn (Z.to_nat (pg_body_len og - skipped)) (skipn (Z.to_nat skipped) bs))) = pg_body_len og - skipped)
by (rewrite firstn_length_le by (rewrite length_skipn; clear - Hsk HSUM BSLEN NPOS; lia); lia).
assert (ZSRC : ubytes (firstn (Z.to_nat (pg_body_len og - skipped)) (skipn (Z.to_nat skipped) bs)) = zslice skipped (pg_body_len og - skipped) (ubytes bs))
by (rewrite ubytes_firstn, ubytes_skipn; reflexivity).
assert (SUBLVB : forall e, In e LV -> In e (rt_live RT Σ1) /\ fst e <> Bd) by (intros e He; split; [exact (SUB4 e He)| exact (proj1 (proj2 (SUBLV3 e He)))]).
assert (LS3P : 0 < os_lacing_storage os3) by (clear - LS0 ELS1 ELS3 LS3B; lia).
pose proof (proj1 (u8arr_rw_CB _ _ _) (u32arr_u8 _ _ _ LAC4)) as LAC4c. pose proof (proj1 (u8arr_rw_CB _ _ _) (u64arr_u8 _ _ _ GRA4)) as GRA4c.
assert (EL4 : Z.of_nat (length (u32s lws4)) = 4 * os_lacing_storage os3) by (rewrite u32s_length; lia).
assert (EG4 : Z.of_nat (length (u64s gws4)) = 8 * os_lacing_storage os3) by (rewrite u64s_length; lia).
refine (pgi_phaseX Σ1 PMc ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 z1 z5 z6 z7 _ z10 z11 z12 z13 z14 z15 z16 z17 _ _ _ _ _ _ _ _ z28 z29 z30 z31 F fc m m4
LV A G Dsy nsy Bd L1 G1 f lo (pg_body_len og - skipped) (Dsy + pg_hdr og + pg_header_len og + skipped) skipped k og os3 shdr hs bs bodybytes1 j0
(firstn (Z.to_nat (pg_body_len og - skipped)) (skipn (Z.to_nat skipped) bs)) (ubytes bs) lws4 gws4
FDO MST OS4 HL A0 BODY4 ltac:(rewrite EBS3, EBS1; exact BLEN1) BPRE3 ltac:(unfold zlength; exact J1') ltac:(clear - BF30 BP2' J1' BLEN1 EBS3 EBS1; lia)
ltac:(clear - BSB EBS3 EBS1 Hsk HSUM NPOS; lia) LAC4c GRA4c FR4 OG4 HS4 BS4 BSRC LSRC NPOS ZSRC
ltac:(clear - PG0 HLEN Hsk HSUM; lia) ltac:(clear - PGIN Hsk HSUM HLEN BSLEN; lia) ltac:(clear - PG0; lia) ltac:(clear - PGIN; lia) HLEN BSLEN
ltac:(rewrite EBS3; exact INB4) ltac:(rewrite EL4; exact INL4) ltac:(rewrite EG4; exact ING4) INSY4 NBL4 NBG4 NSB ltac:(lia) ltac:(lia)
ltac:(rewrite EF4; exact INF) FA1 FA2 FG1 FG2 SEP_AG SUBLVB ltac:(clear - LVM LVM4; lia) ltac:(rewrite EC4; exact CR0) ART4 MI4 ST4 LOW4 LOR SPT SPA ltac:(rewrite EF4; exact PF4) T c4 Hc4 _).
intros c6 Σ2 Bd2 m6 bb6 w1 w5 w6 w7 w10 w11 w12 w13 w14 w15 w16 w17 w28 w29 w30 w31 Hc6 ART6 MI6 ST6 FR6 OS6 BODY6 BLEN6 BPRE6 LAC6 GRA6 OG6 HS6 BS6 PF6
INB6 INL6 ING6 INSY6 NBL6 NBG6 NSB6 SUB6 LVM6 CASEB EF6 ES6 EC6 EP6.
set (bsz := pg_body_len og - skipped) in *.
set (os5 := pagein_body (body_expand_res os3 bsz) (ubytes bs) skipped bsz) in *.
pose proof (body_expand_res_fields os3 bsz) as (EX1 & EX2 & EX3 & EX4 & EX5 & EX6 & EX7 & EX8).
assert (FOK5 : stream_fields_ok os5).
{ unfold os5. apply fields_ok_body; [| rewrite EX2; clear - BF30 BP2' J1' BLEN1 EBS3 EBS1 BSB BS0 NPOS Hsk HSUM; unfold bsz in *; lia].
unfold body_expand_res. destruct (_ <? _); [exact FOK3|]. apply fields_ok_set_blocks; [exact FOK3| clear - BSB EBS3 EBS1 BS0 NPOS Hsk HSUM; unfold bsz in *; lia| pose proof FOK3 as (_ & _ & _ & X & _); exact X]. }
assert (ES5 : os_lacing os5 = os_lacing os3 /\ os_lacing_storage os5 = os_lacing_storage os3 /\ os_lacing_fill os5 = os_lacing_fill os3 /\ os_lacing_packet os5 = os_lacing_packet os3
/\ os_body_storage os5 = os_body_storage (body_expand_res os3 bsz) /\ os_body os5 = os_body os3 ++ zslice skipped bsz (ubytes bs)).
{ unfold os5, pagein_body, set_body. cbn [os_lacing os_lacing_storage os_lacing_fill os_lacing_packet os_body_storage os_body]. rewrite EX8, EX4, EX5, EX6, EX1.
repeat split; reflexivity. }
destruct ES5 as (E5l & E5ls & E5lf & E5lp & E5bs & E5b).
apply u8arr_rw_CB, u8_u32arr in LAC6. apply u8arr_rw_CB, u8_u64arr in GRA6.
assert (LOW6 : rt_sp0 RT Σ2 - STACK_WIN <= lo) by (rewrite ES6, ES4; exact LOW).
assert (SPL6 : forall a, aclient LV (rt_frames RT Σ) (bv_unsigned sp) a -> bv_unsigned sp <= a \/ a < rt_sp0 RT Σ2 - STACK_WIN) by (intros a Ha; rewrite ES6, ES4; exact (SPL a Ha)).
refine (pgi_phaseF Σ2 PMc ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 w1 w5 w6 w7 w10 w11 w12 w13 w14 w15 w16 w17 _ _ _ _ _ w28 w29 w30 w31 F fc m m6
LV (rt_frames RT Σ) A G Dsy nsy Bd2 L1 G1 f lo segptr bos' k og os5 shdr hs bs bb6 j0 lws4 gws4
FDO MST OS6 HL A0 BODY6 ltac:(rewrite E5bs; exact BLEN6) LAC6 ltac:(rewrite E5l; exact LPRE4) ltac:(rewrite E5ls; exact LLEN4) GRA6 ltac:(rewrite E5ls; exact GLEN4)
FR6 OG6 HS6 BS6 FOK5 ltac:(rewrite E5lf, E5ls; clear - Hls3 Hseg; lia) Hseg Hbos
ltac:(rewrite E5l, E5lf; exact K3) ltac:(rewrite E5lp, E5lf; clear - K1 K2; lia) ltac:(rewrite E5l; exact LOK3) LENH HLEN BSLEN PG0 PGIN
ltac:(rewrite E5bs; exact INB6) ltac:(rewrite E5ls, <- EL4; exact INL6) ltac:(rewrite E5ls, <- EG4; exact ING6) INSY6 NBL6 NBG6 NLG4 NSL4 NSG4
ltac:(rewrite EF6; exact EF4) INF FA1 FA2 FG1 FG2 SUB6 SPL6 ltac:(rewrite E5ls; exact NAL4) ltac:(rewrite E5ls; exact NAG4)
ART6 MI6 ST6 LOW6 LOR SPT ltac:(rewrite EF4 in PF6; exact PF6) T c6 Hc6 _).
intros c7 Hc7. apply Hk. exists Σ2, Bd2, L1, G1.
assert (ERES : pagein_res os (ubytes hs) (ubytes bs) = (0, pagein_segments os5 (ubytes hs) bos' segptr)).
{ unfold pagein_res. cbv zeta. fold os1. rewrite ESER', Z.eqb_refl. cbn [negb]. unfold ogg_page_version. rewrite CVER. replace (0 <? 0) with false by reflexivity.
rewrite E3, ESK. rewrite zlength_ubytes, BSLEN. fold bsz.
replace (bsz =? 0) with false by (symmetry; apply Z.eqb_neq; exact BNZ). reflexivity. }
rewrite ERES. cbn [fst snd].
pose proof (segments_shape os5 (ubytes hs) bos' segptr HBOK ltac:(rewrite zlength_lacing_of by lia; lia) ltac:(rewrite E5lp, E5lf; clear - K2; lia)) as SH. cbv zeta in SH.
destruct SH as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13 & Q14 & Q15 & Q16 & Q17).
split; [| split; [reflexivity| split; [reflexivity| split; [| split; [| split; [| repeat split; congruence]]]]]].
* eapply ASTA_conseq; [exact Hc7|]. intros ms (m7 & lws7 & gws7 & RS7 & RA7 & PF7 & OS7 & BODY7 & LAC7 & LPRE7 & LLEN7 & GRA7 & GLEN7).
exists m7, bb6, lws7, gws7.
split; [exact RS7|]. split; [exact RA7|]. split; [exact PF7|]. split; [exact OS7|].
unfold stream_arrays. rewrite Q4, Q5, Q7.
split; [apply u8arr_rw_CB; exact BODY7|]. split; [rewrite E5bs; exact BLEN6|]. split; [rewrite E5b; exact BPRE6|].
split; [exact LAC7|]. split; [exact LPRE7|]. split; [exact LLEN7|]. split; [exact GRA7| exact GLEN7].
* unfold stream_live. rewrite Q4, Q5, E5bs, E5ls. split; [exact INB6|]. split; [rewrite <- EL4; exact INL6|]. split; [rewrite <- EG4; exact ING6|].
split; [exact NBL6|]. split; [exact NBG6| exact NLG4].
* rewrite (LIVE1 Bd2). cbv zeta. fold bsz.
replace (bsz =? 0) with false by (symmetry; apply Z.eqb_neq; exact BNZ). cbn [orb].
destruct CASEB as [(C2 & -> & E)|(C2 & E)]; rewrite E.
-- replace (os_body_fill os3 <? os_body_storage os3 - bsz) with true by (symmetry; apply Z.ltb_lt; exact C2). reflexivity.
-- replace (os_body_fill os3 <? os_body_storage os3 - bsz) with false by (symmetry; apply Z.ltb_ge; exact C2). reflexivity.
* unfold pagein_same. rewrite POK. split; [intros E; discriminate E|]. split.
-- intros _ C. fold os1 in C. destruct CASEL as [(C1 & E1 & E2 & _)|(C1 & _)]; [exact (conj E1 E2)|]. exfalso. apply Z.ltb_lt in C. lia.
-- intros _ C. rewrite E3, ESK in C. cbn [snd] in C. rewrite zlength_ubytes, BSLEN in C. fold bsz in C.
replace (bsz =? 0) with false in C by (symmetry; apply Z.eqb_neq; exact BNZ). cbn [orb] in C. apply Z.ltb_lt in C.
destruct CASEB as [(C2 & EB2 & _)|(C2 & _)]; [exact EB2| exfalso; lia].
Qed.

End OggPageinCPS.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Arguments skipn {A} n l : simpl nomatch.
#[local] Arguments firstn {A} n l : simpl nomatch.

Definition stream_arrays (m : mem) (os : stream_st bptr) (Bd L Gv : Z) (bodybytes : list byte) (lws gws : list word) : Prop :=
u8arr asegs m Bd bodybytes /\ Z.of_nat (length bodybytes) = os_body_storage os /\ body_pre (os_body os) bodybytes /\
u32arr asegs m L lws /\ wpre (os_lacing os) lws /\ Z.of_nat (length lws) = os_lacing_storage os /\
u64arr asegs m Gv gws /\ Z.of_nat (length gws) = os_lacing_storage os.

Definition pgi_os2 (os : stream_st bptr) (hdr : list Z) : stream_st bptr := lacing_expand_res (pagein_returned os) (znth hdr 26 + 1).
Definition pgi_os3 (os : stream_st bptr) (hdr : list Z) : stream_st bptr := pagein_unroll (pgi_os2 os hdr) (ogg_page_pageno hdr).

Definition pagein_res (os : stream_st bptr) (hdr body : list Z) : Z * stream_st bptr :=
let os1 := pagein_returned os in
if negb (ogg_page_serialno hdr =? os_serialno os1) then (-1, os1) else
if 0 <? ogg_page_version hdr then (-1, os1) else
let os3 := pgi_os3 os hdr in
let '(bos, segptr, skipped) := pagein_skip os3 hdr in
let bodysize := zlength body - skipped in
if negb (bodysize =? 0) then (0, pagein_segments (pagein_body (body_expand_res os3 bodysize) body skipped bodysize) hdr bos segptr)
else (0, pagein_segments os3 hdr bos segptr).

Lemma pagein_skip_le : forall (os : stream_st bptr) hdr bos segptr skipped, bytes_ok (lacing_of hdr) ->
pagein_skip os hdr = (bos, segptr, skipped) -> 0 <= skipped <= zsum (lacing_of hdr).
Proof.
intros os hdr bos segptr skipped Hb E. pose proof (pagein_skip_sum os hdr Hb) as S. rewrite E in S. destruct S as (Hseg & ->).
pose proof (zsum_split segptr (lacing_of hdr) ltac:(lia)) as SP.
pose proof (zsum_bytes_nonneg _ (bytes_ok_ztake segptr _ Hb)). pose proof (zsum_bytes_nonneg _ (bytes_ok_zdrop segptr _ Hb)). lia.
Qed.

Lemma pagein_returned_fields : forall os : stream_st bptr,
os_body_data (pagein_returned os) = os_body_data os /\ os_lacing_vals (pagein_returned os) = os_lacing_vals os /\
os_granule_vals (pagein_returned os) = os_granule_vals os /\ os_lacing_storage (pagein_returned os) = os_lacing_storage os /\
os_body_storage (pagein_returned os) = os_body_storage os.
Proof.
intros os. unfold pagein_returned.
destruct (negb (os_body_returned os =? 0)); destruct (negb (os_lacing_returned _ =? 0)); cbn; repeat split; reflexivity.
Qed.
Lemma pagein_unroll_body_data : forall (os : stream_st bptr) pn, os_body_data (pagein_unroll os pn) = os_body_data os.
Proof. intros os pn. unfold pagein_unroll. destruct (negb (pn =? os_pageno os)); [| reflexivity]. destruct (negb (os_pageno _ =? -1)); reflexivity. Qed.
Lemma pagein_unroll_body_storage : forall (os : stream_st bptr) pn, os_body_storage (pagein_unroll os pn) = os_body_storage os.
Proof. intros os pn. unfold pagein_unroll. destruct (negb (pn =? os_pageno os)); [| reflexivity]. destruct (negb (os_pageno _ =? -1)); reflexivity. Qed.

Lemma pgi_os3_body : forall (os : stream_st bptr) hdr,
os_body_data (pgi_os3 os hdr) = os_body_data os /\ os_body_storage (pgi_os3 os hdr) = os_body_storage os.
Proof.
intros os hdr. pose proof (pagein_returned_fields os) as (E1 & E2 & E3 & E4 & E5).
unfold pgi_os3, pgi_os2. rewrite pagein_unroll_body_data, pagein_unroll_body_storage. unfold lacing_expand_res.
destruct (os_lacing_fill (pagein_returned os) <? os_lacing_storage (pagein_returned os) - (znth hdr 26 + 1)); cbn [set_blocks os_body_data os_body_storage];
rewrite E1, E5; split; reflexivity.
Qed.

Lemma pagein_prun : forall (os : stream_st unit) hdr body q r q',
prun (ogg_stream_pagein (St := pst) p_realloc p_free os hdr body) q = Some (r, q') ->
os_body_data os <> None -> os_lacing_vals os <> None -> os_granule_vals os <> None ->
bytes_ok (lacing_of hdr) -> zsum (lacing_of hdr) <= zlength body -> 0 <= znth hdr 26 ->
0 <= os_lacing_storage os -> os_lacing_storage os + znth hdr 26 + 33 < 2^58 ->
0 <= os_body_storage os -> os_body_storage os + zlength body + 1024 < 2^62 ->
r = pagein_res os hdr body /\ q' = q.
Proof.
intros os hdr body q r q' H BD LD GD HB HS N0 LS0 LSB BS0 BSB.
unfold ogg_stream_pagein, ogg_stream_check in H. unfold pagein_res, pgi_os3, pgi_os2. cbv zeta in H |- *. unfold bptr in *.
destruct (os_body_data os) as [[]|] eqn:EBD; [| exfalso; apply BD; reflexivity].
pose proof (pagein_returned_fields os) as (E1 & E2 & E3 & E4 & E5). unfold bptr in *.
set (os1 := pagein_returned os) in *.
destruct (negb (ogg_page_serialno hdr =? os_serialno os1)); [rewrite prun_ret in H; injection H as <- <-; split; reflexivity|].
destruct (0 <? ogg_page_version hdr); [rewrite prun_ret in H; injection H as <- <-; split; reflexivity|].
rewrite prun_bind in H.
destruct (prun (os_lacing_expand p_realloc p_free os1 (znth hdr 26 + 1)) q) as [[[r2 os2] q2]|] eqn:EL; [| discriminate H].
apply lacing_expand_prun in EL; [| rewrite E2; exact LD| rewrite E3; exact GD| lia| rewrite E4; lia| rewrite E4; lia].
destruct EL as (EL & ->). injection EL as -> ->. cbn [negb Z.eqb] in H.
lazymatch type of H with context [pagein_skip ?x hdr] => set (os3 := x) in * end.
destruct (pagein_skip os3 hdr) as [[bos segptr] skipped] eqn:ESK.
pose proof (pagein_skip_le os3 hdr bos segptr skipped HB ESK) as SKL.
rewrite prun_bind in H.
destruct (negb (zlength body - skipped =? 0)) eqn:EBZ.
- rewrite prun_bind in H.
destruct (prun (os_body_expand p_realloc p_free os3 (zlength body - skipped)) q) as [[[r4 os4] q4]|] eqn:EB; [| discriminate H].
assert (X : os_body_data os3 <> None /\ os_body_storage os3 = os_body_storage os).
{ destruct (pgi_os3_body os hdr) as (Y1 & Y2). split; [| exact Y2].
intros Z. change (os_body_data (pgi_os3 os hdr) = None) in Z. rewrite Y1 in Z. unfold bptr in Z. rewrite EBD in Z. discriminate Z. }
destruct X as (X1 & X2).
apply body_expand_prun in EB; [| exact X1| lia| rewrite X2; lia| rewrite X2; lia].
destruct EB as (EB & ->). injection EB as -> ->. cbn [negb Z.eqb] in H. rewrite prun_ret in H. cbn [negb Z.eqb] in H.
rewrite prun_ret in H. injection H as <- <-. split; reflexivity.
- rewrite prun_ret in H. cbn [negb Z.eqb] in H. rewrite prun_ret in H. injection H as <- <-. split; reflexivity.
Qed.

Definition pgi_ok (os : stream_st bptr) (hdr : list Z) : bool :=
(ogg_page_serialno hdr =? os_serialno (pagein_returned os)) && negb (0 <? ogg_page_version hdr).
Definition pagein_live (live : list (Z * Z)) (os : stream_st bptr) (hdr body : list Z) (Bd L Gv Bd' L' Gv' : Z) : list (Z * Z) :=
if pgi_ok os hdr then
let os1 := pagein_returned os in
let need := znth hdr 26 + 1 in
let l1 := if os_lacing_fill os1 <? os_lacing_storage os1 - need then live
else (Gv', 8 * (os_lacing_storage os1 + need + 32)) :: (L', 4 * (os_lacing_storage os1 + need + 32)) :: live_remove Gv (live_remove L live) in
let os3 := pgi_os3 os hdr in
let bodysize := zlength body - snd (pagein_skip os3 hdr) in
if (bodysize =? 0) || (os_body_fill os3 <? os_body_storage os3 - bodysize) then l1
else (Bd', os_body_storage os3 + bodysize + 1024) :: live_remove Bd l1
else live.

Definition pagein_same (os : stream_st bptr) (hdr body : list Z) (Bd L Gv Bd' L' Gv' : Z) : Prop :=
(pgi_ok os hdr = false -> Bd' = Bd /\ L' = L /\ Gv' = Gv)
/\ (pgi_ok os hdr = true -> (os_lacing_fill (pagein_returned os) <? os_lacing_storage (pagein_returned os) - (znth hdr 26 + 1)) = true -> L' = L /\ Gv' = Gv)
/\ (pgi_ok os hdr = true ->
((zlength body - snd (pagein_skip (pgi_os3 os hdr) hdr) =? 0)
|| (os_body_fill (pgi_os3 os hdr) <? os_body_storage (pgi_os3 os hdr) - (zlength body - snd (pagein_skip (pgi_os3 os hdr) hdr)))) = true -> Bd' = Bd).

Section OggPageinCPS.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis MMOV : memmove_icontract RT e_memmove.
Hypothesis MCPY : memcpy_icontract RT e_memcpy.
Hypothesis LEXP : os_lacing_expand_cps RT.
Hypothesis BEXP : os_body_expand_cps RT.

Definition pgi_rest (Bd L Gv : Z) (live : list (Z * Z)) : list (Z * Z) := live_remove Gv (live_remove L (live_remove Bd live)).

Lemma pgi_rest_sub : forall Bd L Gv live e, In e (pgi_rest Bd L Gv live) -> In e live.
Proof. intros Bd L Gv live e H. unfold pgi_rest in H. do 3 apply live_remove_sub in H. exact H. Qed.

Definition ogg_stream_pagein_cps : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (A G Dsy nsy Bd L Gv f lo : Z) (k : nat) (og : page) (os : stream_st bptr) (shdr hs bs bodybytes : list byte) (lws gws : list word)
(q q' : pst) (r : Z * stream_st bptr),
fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 G -> tp = Z_to_bv 64 0x630458 ->
prun (ogg_stream_pagein (St := pst) p_realloc p_free os (ubytes hs) (ubytes bs)) q = Some (r, q') ->
rw_cells asegs m A (stream_cells Bd L Gv shdr os) -> length shdr = 284%nat -> 0 < A ->
stream_arrays m os Bd L Gv bodybytes lws gws ->
stream_fields_ok os -> stream_inv os -> body_inv os -> lacing_vals_ok (os_lacing os) ->
os_body_data os <> None -> os_lacing_vals os <> None -> os_granule_vals os <> None ->
stream_live RT Σ os Bd L Gv ->
rw_cells asegs m G (page_cells Dsy og) -> 0 < G ->
bytes_at asegs m (Dsy + pg_hdr og) hs -> bytes_at asegs m (Dsy + pg_hdr og + pg_header_len og) bs ->
length hs = (27 + Z.to_nat (znth (ubytes hs) 26))%nat -> Z.of_nat (length hs) = pg_header_len og -> Z.of_nat (length bs) = pg_body_len og ->
zsum (lacing_of (ubytes hs)) <= pg_body_len og -> 0 <= pg_hdr og -> pg_hdr og + pg_header_len og + pg_body_len og <= nsy ->
In (Dsy, nsy) (rt_live RT Σ) -> Dsy <> Bd -> Dsy <> L -> Dsy <> Gv ->
8 * (os_lacing_storage os + znth (ubytes hs) 26 + 33) <= 64512 -> os_body_storage os + pg_body_len og + 1024 <= 64512 -> 0 < os_lacing_storage os -> 0 < os_body_storage os ->
In (f, k) (rt_frames RT Σ) -> f <= A -> A + 408 <= f + fs_size k - 8 -> f <= G -> G + 32 <= f + fs_size k - 8 -> (A + 408 <= G \/ G + 32 <= A) ->
Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX -> 0 <= rt_credit RT Σ ->
ART RT Σ m -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK + 256 <= bv_unsigned sp ->
bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc A_ogg_stream_pagein m)))
(fun c => exists (Σ' : rts RT) (Bd' L' Gv' : Z),
ASTA RT Σ' PMc (fun ms => exists m' (bodybytes' : list byte) (lws' gws' : list word),
ret_stL (fun F' fc' => F' = F /\ fc' = fc) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (wz (fst r)) m' ms
/\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
/\ rt_pres_fp (pgi_rest Bd L Gv (rt_live RT Σ)) (rt_frames RT Σ) (bv_unsigned sp) [(A, A + 408)] m m'
/\ rw_cells asegs m' A (stream_cells Bd' L' Gv' shdr (snd r))
/\ stream_arrays m' (snd r) Bd' L' Gv' bodybytes' lws' gws') c
/\ q' = q /\ r = pagein_res os (ubytes hs) (ubytes bs)
/\ stream_live RT Σ' (snd r) Bd' L' Gv'
/\ rt_live RT Σ' = pagein_live (rt_live RT Σ) os (ubytes hs) (ubytes bs) Bd L Gv Bd' L' Gv'
/\ pagein_same os (ubytes hs) (ubytes bs) Bd L Gv Bd' L' Gv'
/\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
/\ rt_credit RT Σ' = rt_credit RT Σ /\ rt_pois RT Σ' = rt_pois RT Σ).

Definition kp (P : Prop) : Prop := P.
Ltac kp_all :=
repeat match goal with
| H : rw_cells asegs ?m ?a ?cs |- _ => change (kp (rw_cells asegs m a cs)) in H
| H : bytes_at asegs ?m ?a ?bs |- _ => change (kp (bytes_at asegs m a bs)) in H
end.
Ltac cls_live IN := right; right; left; lazymatch type of IN with In (?p, ?n) _ => exists p, n; split; [exact IN | ulq0] end.
Ltac cls_frame IN := right; right; right; left; lazymatch type of IN with In (?f, ?k) _ => exists f, k; split; [exact IN | ulq0] end.
Ltac cls_stack := left; ulq0.
Ltac tx_agree cls :=
lazymatch goal with
| |- agree_on _ ?m ?m' =>
first [ match goal with PRES : rt_pres_ex ?live ?frames ?sp ?d ?n m m' |- _ =>
apply (agree_of_pres_ex live frames sp d n m m' _ PRES); intros ?x ?Hx; cps_sizes Hx; split; [cls | ulc] end
| match goal with PRES : rt_pres_fp ?live ?frames ?sp ?W m m' |- _ =>
apply (agree_of_pres_fp live frames sp W m m' _ PRES); intros ?x ?Hx; cps_sizes Hx; split; [cls | cbn [outside]; repeat split; ulc] end
| match goal with PRES : rt_pres ?live ?frames ?sp m m' |- _ =>
apply (agree_of_pres live frames sp m m' _ PRES); intros ?x ?Hx; cps_sizes Hx; cls end ]
end.

Ltac tx H cls :=
unfold kp in H;
let m' := lazymatch goal with Hc : ASTA _ _ _ (eq (MS _ _ _ _ _ ?mm _)) _ |- _ => mm end in
lazymatch type of H with
| rw_cells asegs ?m ?A ?cs => apply (rw_cells_agree_nw asegs m m' A cs) in H; [ | tx_agree cls ]
| bytes_at asegs ?m ?A ?bs => apply (bytes_at_agree asegs m m' A bs) in H; [ | tx_agree cls ]
end.

Ltac tx_agree_ex cls sep :=
lazymatch goal with
| |- agree_on _ ?m ?m' =>
first [ match goal with PRES : rt_pres_ex ?live ?frames ?sp ?d ?n m m' |- _ =>
apply (agree_of_pres_ex live frames sp d n m m' _ PRES); let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; cps_sizes Hx; split; [cls | sep x Hx] end
| match goal with PRES : rt_pres_fp ?live ?frames ?sp ?W m m' |- _ =>
apply (agree_of_pres_fp live frames sp W m m' _ PRES); let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; cps_sizes Hx; split;
[cls | cbn [outside]; repeat split; sep x Hx] end ]
end.
Ltac txe H cls sep :=
unfold kp in H;
let m' := lazymatch goal with Hc : ASTA _ _ _ (eq (MS _ _ _ _ _ ?mm _)) _ |- _ => mm end in
lazymatch type of H with
| rw_cells asegs ?m ?A ?cs => apply (rw_cells_agree_nw asegs m m' A cs) in H; [ | tx_agree_ex cls sep ]
| bytes_at asegs ?m ?A ?bs => apply (bytes_at_agree asegs m m' A bs) in H; [ | tx_agree_ex cls sep ]
end.

Lemma stream_cells_ret_body : forall Bd L G hdr (os : stream_st bptr),
stream_cells Bd L G hdr (ret_body os)
= stream_cells_r Bd (os_body_fill (ret_body os)) (os_body_returned (ret_body os)) L G (os_lacing_fill os) (os_lacing_packet os) (os_lacing_returned os) hdr os.
Proof. intros. unfold ret_body. destruct (negb (os_body_returned os =? 0)); reflexivity. Qed.

Lemma live_apart2 : forall (Σ : rts RT) (m : mem) p n p2 n2, ART RT Σ m -> In (p, n) (rt_live RT Σ) -> In (p2, n2) (rt_live RT Σ) -> p2 <> p ->
p + n <= p2 \/ p2 + n2 <= p.
Proof using AF.
intros Σ m p n p2 n2 ART0 I1 I2 NE. apply (live_remove_apart RT AF Σ m p n p2 n2 ART0 I1). apply live_remove_keep; [exact I2| exact NE].
Qed.

Lemma pgi_phaseA : forall (Σ : rts RT) PMc (ra gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (A G Dsy nsy Bd L Gv f lo usp : Z) (k : nat) (og : page) (os : stream_st bptr) (shdr hs bs bodybytes : list byte) (lws gws : list word),
fdfs_only PMc -> mat_stable PMc ->
rw_cells asegs m A (stream_cells Bd L Gv shdr os) -> length shdr = 284%nat -> 0 < A ->
u8arr asegs m Bd bodybytes -> Z.of_nat (length bodybytes) = os_body_storage os -> body_pre (os_body os) bodybytes ->
rw_cells asegs m L [CB (length (u32s lws)) (u32s lws)] -> Z.of_nat (length (u32s lws)) = 4 * os_lacing_storage os ->
rw_cells asegs m Gv [CB (length (u64s gws)) (u64s gws)] -> Z.of_nat (length (u64s gws)) = 8 * os_lacing_storage os ->
stream_fields_ok os -> zlength (os_body os) = os_body_fill os -> 0 <= os_body_returned os <= os_body_fill os -> os_body_storage os <= 64512 ->
stream_live RT Σ os Bd L Gv ->
rw_cells asegs m G (page_cells Dsy og) -> 0 < G ->
bytes_at asegs m (Dsy + pg_hdr og) hs -> bytes_at asegs m (Dsy + pg_hdr og + pg_header_len og) bs ->
(27 <= length hs)%nat -> Z.of_nat (length hs) = pg_header_len og -> Z.of_nat (length bs) = pg_body_len og ->
0 <= pg_hdr og -> pg_hdr og + pg_header_len og + pg_body_len og <= nsy -> In (Dsy, nsy) (rt_live RT Σ) -> Dsy <> Bd ->
In (f, k) (rt_frames RT Σ) -> f <= A -> A + 408 <= f + fs_size k - 8 -> f <= G -> G + 32 <= f + fs_size k - 8 -> (A + 408 <= G \/ G + 32 <= A) ->
(forall a, aclient (pgi_rest Bd L Gv (rt_live RT Σ)) (rt_frames RT Σ) usp a -> ~ (Bd <= a < Bd + os_body_storage os)) ->
ART RT Σ m -> mem_inv asegs m ->
stk asegs m lo usp -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK + 256 <= usp -> usp + 16 <= USTACK_TOP -> usp mod 16 = 0 ->
forall T c,
ASTA RT Σ PMc (eq (MS (mkR ra (Z_to_bv 64 usp) gp (Z_to_bv 64 0x630458) t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 G) a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 A_ogg_stream_pagein) fc None m (seg_rom asegs))) c ->
(forall c1 (m1 : mem) (bodybytes1 j0 : list byte) (v25 v22 : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
ASTA RT Σ PMc (eq (MS (pgi_regs x1 usp gp (Z_to_bv 64 0x630458) x5 x6 x7 A (Z_to_bv 64 (os_lacing_returned os)) x10 x11 x12 x13 x14 x15 x16 x17
(pg_body_len og) (Dsy + pg_hdr og + pg_header_len og) (Dsy + pg_hdr og) (Z_to_bv 64 v22) hs (Z_to_bv 64 v25) x28 x29 x30 x31)
F (Z_to_bv 64 0xb93f0) fc None m1 (seg_rom asegs))) c1 ->
ART RT Σ m1 -> mem_inv asegs m1 -> stk asegs m1 lo (usp + -144) ->
rw_cells asegs m1 (usp + -144) (pgi_frame ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j0 hs) ->
rw_cells asegs m1 A (stream_cells Bd L Gv shdr (ret_body os)) ->
u8arr asegs m1 Bd bodybytes1 -> Z.of_nat (length bodybytes1) = os_body_storage os -> body_pre (os_body (ret_body os)) bodybytes1 ->
rw_cells asegs m1 L [CB (length (u32s lws)) (u32s lws)] -> rw_cells asegs m1 Gv [CB (length (u64s gws)) (u64s gws)] ->
rw_cells asegs m1 G (page_cells Dsy og) ->
bytes_at asegs m1 (Dsy + pg_hdr og) hs -> bytes_at asegs m1 (Dsy + pg_hdr og + pg_header_len og) bs ->
0 <= v25 < 2^64 -> 0 <= v22 < 2^64 -> Z_to_bv 64 (Z.lor v25 v22) = Z_to_bv 64 (ogg_page_serialno (ubytes hs)) ->
rt_pres_fp (pgi_rest Bd L Gv (rt_live RT Σ)) (rt_frames RT Σ) usp [(A, A + 408)] m m1 ->
realizes asegs c1 T) ->
realizes asegs c T.
Proof using AF MMOV.
intros Σ PMc ra gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m A G Dsy nsy Bd L Gv f lo usp k og os shdr hs bs bodybytes lws gws
FDO MST OS HL A0 BODY BLEN BPRE LAC LBL GRA LBG FOK BFILL BRF BSM SLV OG G0 HS BS LENH HLEN BSLEN PG0 PGIN INSY NSB INF FA1 FA2 FG1 FG2 SEP_AG NAB ART0 MI0 ST0 LOW LOR SPT SPA T c Hc Hk.
destruct (frame_below_lo RT AF Σ m f k lo ART0 INF LOW) as (BF1 & BF2 & BF3).
assert (FSZ : 0 <= fs_size k) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
destruct SLV as (INB & INL & ING & NBL & NBG & NLG).
destruct (live_below_lo RT AF Σ m Bd _ lo ART0 INB LOW) as (B0 & B1 & _).
destruct (live_below_lo RT AF Σ m L _ lo ART0 INL LOW) as (L0 & L1 & _).
destruct (live_below_lo RT AF Σ m Gv _ lo ART0 ING LOW) as (G0' & G1 & _).
destruct (live_below_lo RT AF Σ m Dsy _ lo ART0 INSY LOW) as (S0 & S1 & _).
pose proof FOK as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12). unfold int31 in *.
set (LV := pgi_rest Bd L Gv (rt_live RT Σ)) in *.
pose proof (pres_fp_refl LV (rt_frames RT Σ) usp [(A, A + 408)] m) as PF.
assert (SUBLV : forall e, In e LV -> In e (rt_live RT Σ)) by (intros e He; exact (pgi_rest_sub _ _ _ _ _ He)).
assert (SPL : forall a, aclient LV (rt_frames RT Σ) usp a -> usp <= a \/ a < rt_sp0 RT Σ - STACK_WIN).
{ intros a Ha. apply (aclient_split RT AF Σ m usp a ART0). apply (aclient_mono _ _ _ _ _ _ _ Ha); [exact SUBLV| auto| apply Z.le_refl]. }
pose proof BPRE as (BP1 & BP2). unfold zlength in BFILL.
assert (TOPH : Dsy + pg_hdr og + Z.of_nat (length hs) < 2^63) by (clear - S1 PGIN HLEN BSLEN LOR SPT; unfold RT_STACK, USTACK_TOP in *; lia).
assert (AT : A + 408 < 2^63) by (clear - FA2 BF1 LOR SPT FSZ; unfold RT_STACK, USTACK_TOP in *; lia).
assert (BT : Bd + os_body_storage os < 2^63) by (clear - B1 LOR SPT; unfold RT_STACK, USTACK_TOP in *; lia).
destruct (frame_live_apart RT AF Σ m f k Bd _ ART0 INF INB) as (FLB & _).
destruct (frame_live_apart RT AF Σ m f k L _ ART0 INF INL) as (FLL & _).
destruct (frame_live_apart RT AF Σ m f k Gv _ ART0 INF ING) as (FLG & _).
destruct (frame_live_apart RT AF Σ m f k Dsy _ ART0 INF INSY) as (FLS & _).
assert (SEP_GB : Bd + os_body_storage os <= G \/ G + 32 <= Bd) by (clear - FLB FG1 FG2; lia).
pose proof (live_apart2 Σ m Bd _ L _ ART0 INB INL ltac:(congruence)) as SEP_BL.
pose proof (live_apart2 Σ m Bd _ Gv _ ART0 INB ING ltac:(congruence)) as SEP_BG.
pose proof (live_apart2 Σ m Bd _ Dsy _ ART0 INB INSY NSB) as SEP_BS.
assert (SEP_AB : Bd + os_body_storage os <= A \/ A + 408 <= Bd) by (clear - FLB FA1 FA2; lia).
assert (SEP_AL : L + 4 * os_lacing_storage os <= A \/ A + 408 <= L) by (clear - FLL FA1 FA2; lia).
assert (SEP_AGv : Gv + 8 * os_lacing_storage os <= A \/ A + 408 <= Gv) by (clear - FLG FA1 FA2; lia).
assert (SEP_AS : Dsy + nsy <= A \/ A + 408 <= Dsy) by (clear - FLS FA1 FA2; lia).
clear FLB FLL FLG FLS.
rewrite stream_cells_r_eq in OS. unfold stream_cells_r in OS. unfold page_cells in OG.
cps_norm. cps_hide.
cps_seg (pgi_w0 A G Dsy Bd L Gv usp lo og shdr hs os).
destruct POST as (m1 & j0 & v25 & v22 & x1 & x5 & x6 & x7 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & -> & MU1 & WM1 & MI1 & ST1 & FR1 & V25 & V22 & ESER).
apply u8arr_rw_CB in BODY. unfold pgi_frame in FR1.
cps_seg_post.
destruct (Z.eq_dec (os_body_returned os) 0) as [BRZ|BRNZ].
-
assert (ERB : ret_body os = os) by (unfold ret_body; rewrite BRZ; reflexivity).
rewrite BRZ in Hc0.
cps_seg (pgi_b0 A usp (pg_body_len og) (Dsy + pg_hdr og + pg_header_len og) (Dsy + pg_hdr og) hs).
lazymatch type of POST with ?x = _ => subst x end.
eapply (Hk _ m1 bodybytes j0 v25 v22); try eassumption.
+ rewrite ERB, stream_cells_r_eq. exact OS.
+ apply u8arr_rw_CB. exact BODY.
+ rewrite ERB. exact BPRE.
- assert (ERB : ret_body os = set_body os (ztake (os_body_fill os - os_body_returned os) (zdrop (os_body_returned os) (os_body os)))
(os_body_storage os) (os_body_fill os - os_body_returned os) 0).
{ unfold ret_body. replace (os_body_returned os =? 0) with false by (symmetry; apply Z.eqb_neq; exact BRNZ). reflexivity. }
destruct (Z.eq_dec (os_body_fill os) (os_body_returned os)) as [BFE|BFNE].
+
cps_seg (pgi_b1 A Bd (os_body_fill os) (os_body_returned os) L Gv (os_lacing_fill os) (os_lacing_packet os) (os_lacing_returned os) usp
(pg_body_len og) (Dsy + pg_hdr og + pg_header_len og) (Dsy + pg_hdr og) shdr hs os).
destruct POST as (m2 & x12' & x13' & -> & MU2 & WM2 & MI2 & OS2). unfold stream_cells_r in OS2.
clear OS. cps_seg_post.
eapply (Hk _ m2 bodybytes j0 v25 v22); try eassumption.
* rewrite stream_cells_ret_body, ERB. cbn [set_body os_body_fill os_body_returned]. exact OS2.
* apply u8arr_rw_CB. exact BODY.
* rewrite ERB. cbn [set_body os_body]. unfold body_pre, ztake. replace (Z.to_nat (os_body_fill os - os_body_returned os)) with 0%nat by lia.
cbn [firstn length]. split; [reflexivity| lia].
+
set (nr := Z.to_nat (os_body_returned os)). set (nf := Z.to_nat (os_body_fill os - os_body_returned os)).
destruct (compact_prefix (os_body os) bodybytes nr nf BP1 ltac:(unfold nr, nf; lia) BP2) as (CP1 & CP2).
set (b1 := firstn nf bodybytes). set (b2 := skipn nf bodybytes). set (bsrc := firstn nf (skipn nr bodybytes)).
assert (Lb1 : Z.of_nat (length b1) = os_body_fill os - os_body_returned os) by (unfold b1; rewrite firstn_length_le by (unfold nf, nr in *; lia); unfold nf; lia).
assert (LEQ : length bsrc = length b1) by (unfold bsrc, b1; rewrite !firstn_length_le by (rewrite ?length_skipn; unfold nf, nr in *; lia); reflexivity).
assert (Lbs : Z.of_nat (length bsrc) = os_body_fill os - os_body_returned os) by (rewrite LEQ; exact Lb1).
assert (EB : bodybytes = b1 ++ b2) by (symmetry; apply firstn_skipn).
assert (Lb2 : Z.of_nat (length b2) = os_body_storage os - (os_body_fill os - os_body_returned os)) by (unfold b2; rewrite length_skipn; unfold nf, nr in *; lia).
apply u8arr_rw_CB in BODY.
pose proof (bytes_at_sub m1 Bd bodybytes nr nf (proj1 BODY) ltac:(unfold nf, nr in *; lia)) as SRC. fold bsrc in SRC.
replace (Bd + Z.of_nat nr) with (Bd + os_body_returned os) in SRC by (unfold nr; lia).
rewrite EB in BODY. apply u8arr_app in BODY. destruct BODY as (P1 & P2). apply u8arr_rw_CB in P1, P2.
assert (FST : os_body_fill os <= os_body_storage os) by (clear - BFILL BP2 BLEN; lia).
cps_seg (pgi_b2 A Bd (os_body_fill os) (os_body_returned os) L Gv (os_lacing_fill os) (os_lacing_packet os) (os_lacing_returned os) usp
(pg_body_len og) (Dsy + pg_hdr og + pg_header_len og) (Dsy + pg_hdr og) shdr hs os).
destruct POST as (m2 & -> & MU2 & WM2 & MI2 & OS2). unfold stream_cells_r in OS2.
clear OS. cps_seg_post.
assert (NAB' : forall a, aclient LV (rt_frames RT Σ) usp a -> ~ (Bd <= a < Bd + Z.of_nat (length bsrc))).
{ intros a Ha. specialize (NAB a Ha). clear - NAB Lbs FST BRF. lia. }
pose proof (proj2 P1) as WR1. cbn [cells_size csize Nat.add] in WR1. rewrite Nat.add_0_r, <- LEQ in WR1.
assert (EU : bv_unsigned (Z_to_bv 64 (usp + -144)) = usp + -144) by (apply unsigned_lit; ulc).
lazymatch goal with H : ASTA _ _ _ (eq _) _ |- _ => unfold pgi_regs in H; rewrite <- Lbs in H end.
kp_all.
cps_rt (MMOV Σ PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 Bd (Bd + os_body_returned os) bsrc lo).
all: [> .. | ].
all: lazymatch goal with
| |- call_ok _ _ _ _ _ => cps_callok
| |- checked_src _ _ _ _ _ _ _ => idtac
| |- checked_dst _ _ _ _ _ _ => idtac
| |- bytes_at _ _ _ _ => exact SRC
| |- _ => try (clear - B0 B1 BRF F1 F2 LOR SPT Lbs FST BSM; lia)
end.
{ apply (live_checked_src RT AF Σ m2 _ lo Bd (os_body_storage os)); [eassumption| exact INB| lia| lia| exact B1]. }
{ apply (live_checked_dst RT AF Σ m2 _ Bd (os_body_storage os)); [eassumption| exact INB| lia| lia| exact WR1]. }
intros kc2 Hc2. unfold icpt_postF in Hc2.
cps_unpack Hc2 as (m3 & RS3 & (ART3 & MI3 & WM3 & ST3) & PRES3 & BY3).
pose proof (ogg_bytes_piece m2 m3 Bd bsrc WR1 WM3 BY3) as P1'. clear BY3 P1 SRC.
tx P2 ltac:(cls_live INB). tx OS2 ltac:(cls_frame INF). tx FR1 ltac:(cls_stack). tx LAC ltac:(cls_live INL). tx GRA ltac:(cls_live ING).
tx OG ltac:(cls_frame INF). tx HS ltac:(cls_live INSY). tx BS ltac:(cls_live INSY).
cps_seg (pgi_b3 A Bd (os_body_fill os - os_body_returned os) (os_body_returned os) L Gv (os_lacing_fill os) (os_lacing_packet os) (os_lacing_returned os) usp
(pg_body_len og) (Dsy + pg_hdr og + pg_header_len og) (Dsy + pg_hdr og) shdr hs os).
destruct POST as (m4 & -> & MU4 & WM4 & MI4 & OS4). unfold stream_cells_r in OS4.
clear OS2. cps_seg_post.
eapply (Hk _ m4 (bsrc ++ b2) j0 v25 v22); try eassumption.
* rewrite stream_cells_ret_body, ERB. cbn [set_body os_body_fill os_body_returned]. exact OS4.
* apply u8arr_app. split; [apply u8arr_rw_CB; exact P1'|]. rewrite LEQ. apply u8arr_rw_CB. exact P2.
* rewrite length_app. clear - Lbs Lb1 LEQ EB BLEN. rewrite EB, length_app in BLEN. lia.
* rewrite ERB. cbn [set_body os_body]. unfold body_pre, ztake, zdrop. fold nr nf. exact (conj CP1 CP2).
Qed.

Lemma stream_cells_ret_lacing : forall Bd L G hdr (os : stream_st bptr),
stream_cells Bd L G hdr (ret_lacing os)
= stream_cells_r Bd (os_body_fill os) (os_body_returned os) L G (os_lacing_fill (ret_lacing os)) (os_lacing_packet (ret_lacing os)) (os_lacing_returned (ret_lacing os)) hdr os.
Proof. intros. unfold ret_lacing. destruct (negb (os_lacing_returned os =? 0)); reflexivity. Qed.

Lemma pgi_phaseB : forall (Σ : rts RT) PMc (x1 gp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
F fc (m0 m : mem) (A G Dsy nsy Bd L Gv f lo usp v25 v22 : Z) (k : nat) (og : page) (os : stream_st bptr) (shdr hs bs bodybytes j0 : list byte) (lws gws : list word),
fdfs_only PMc -> mat_stable PMc ->
rw_cells asegs m A (stream_cells Bd L Gv shdr os) -> length shdr = 284%nat -> 0 < A ->
rw_cells asegs m Bd [CB (length bodybytes) bodybytes] -> Z.of_nat (length bodybytes) = os_body_storage os ->
u32arr asegs m L lws -> wpre (os_lacing os) lws -> Z.of_nat (length lws) = os_lacing_storage os ->
u64arr asegs m Gv gws -> Z.of_nat (length gws) = os_lacing_storage os ->
stream_fields_ok os -> zlength (os_lacing os) = os_lacing_fill os ->
0 <= os_lacing_returned os <= os_lacing_packet os -> os_lacing_packet os <= os_lacing_fill os -> 8 * os_lacing_storage os <= 64512 ->
stream_live RT Σ os Bd L Gv ->
rw_cells asegs m (usp + -144) (pgi_frame ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j0 hs) ->
rw_cells asegs m G (page_cells Dsy og) -> 0 < G ->
bytes_at asegs m (Dsy + pg_hdr og) hs -> bytes_at asegs m (Dsy + pg_hdr og + pg_header_len og) bs ->
(27 <= length hs)%nat -> Z.of_nat (length hs) = pg_header_len og -> Z.of_nat (length bs) = pg_body_len og ->
0 <= pg_hdr og -> pg_hdr og + pg_header_len og + pg_body_len og <= nsy -> In (Dsy, nsy) (rt_live RT Σ) -> Dsy <> L -> Dsy <> Gv ->
In (f, k) (rt_frames RT Σ) -> f <= A -> A + 408 <= f + fs_size k - 8 -> f <= G -> G + 32 <= f + fs_size k - 8 -> (A + 408 <= G \/ G + 32 <= A) ->
(forall a, aclient (pgi_rest Bd L Gv (rt_live RT Σ)) (rt_frames RT Σ) usp a -> ~ (L <= a < L + 4 * os_lacing_storage os)) ->
(forall a, aclient (pgi_rest Bd L Gv (rt_live RT Σ)) (rt_frames RT Σ) usp a -> ~ (Gv <= a < Gv + 8 * os_lacing_storage os)) ->
0 <= v25 < 2^64 -> 0 <= v22 < 2^64 -> Z_to_bv 64 (Z.lor v25 v22) = Z_to_bv 64 (ogg_page_serialno (ubytes hs)) ->
ART RT Σ m -> mem_inv asegs m ->
stk asegs m lo (usp + -144) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK + 256 <= usp -> usp + 16 <= USTACK_TOP -> usp mod 16 = 0 ->
rt_pres_fp (pgi_rest Bd L Gv (rt_live RT Σ)) (rt_frames RT Σ) usp [(A, A + 408)] m0 m ->
forall T c,
ASTA RT Σ PMc (eq (MS (pgi_regs x1 usp gp (Z_to_bv 64 0x630458) x5 x6 x7 A (Z_to_bv 64 (os_lacing_returned os)) x10 x11 x12 x13 x14 x15 x16 x17
(pg_body_len og) (Dsy + pg_hdr og + pg_header_len og) (Dsy + pg_hdr og) (Z_to_bv 64 v22) hs (Z_to_bv 64 v25) x28 x29 x30 x31)
F (Z_to_bv 64 0xb93f0) fc None m (seg_rom asegs))) c ->
(forall c1 (m1 : mem) (lws1 gws1 : list word) (y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
ASTA RT Σ PMc (eq (MS (pgi_regs y1 usp gp (Z_to_bv 64 0x630458) y5 y6 y7 A y9 y10 y11 y12 y13 y14 y15 y16 y17
(pg_body_len og) (Dsy + pg_hdr og + pg_header_len og) (Dsy + pg_hdr og) (Z_to_bv 64 v22) hs
(Z_to_bv 64 (ogg_page_serialno (ubytes hs))) y28 y29 y30 y31)
F (Z_to_bv 64 0xb9454) fc None m1 (seg_rom asegs))) c1 ->
ART RT Σ m1 -> mem_inv asegs m1 -> stk asegs m1 lo (usp + -144) ->
rw_cells asegs m1 (usp + -144) (pgi_frame ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j0 hs) ->
rw_cells asegs m1 A (stream_cells Bd L Gv shdr (ret_lacing os)) ->
rw_cells asegs m1 Bd [CB (length bodybytes) bodybytes] ->
u32arr asegs m1 L lws1 -> wpre (os_lacing (ret_lacing os)) lws1 -> Z.of_nat (length lws1) = os_lacing_storage os ->
u64arr asegs m1 Gv gws1 -> Z.of_nat (length gws1) = os_lacing_storage os ->
rw_cells asegs m1 G (page_cells Dsy og) ->
bytes_at asegs m1 (Dsy + pg_hdr og) hs -> bytes_at asegs m1 (Dsy + pg_hdr og + pg_header_len og) bs ->
rt_pres_fp (pgi_rest Bd L Gv (rt_live RT Σ)) (rt_frames RT Σ) usp [(A, A + 408)] m0 m1 ->
realizes asegs c1 T) ->
realizes asegs c T.
Proof using AF MMOV.
intros Σ PMc x1 gp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 m A G Dsy nsy Bd L Gv f lo usp v25 v22 k og os
shdr hs bs bodybytes j0 lws gws FDO MST OS HL A0 BODY BLEN LAC LPRE LLEN GRA GLEN FOK LFILL LRP LPF LSM SLV FR OG G0 HS BS LENH HLEN BSLEN PG0 PGIN INSY NSL NSG
INF FA1 FA2 FG1 FG2 SEP_AG NAL NAG V25 V22 ESER ART0 MI0 ST0 LOW LOR SPT SPA PF T c Hc Hk.
destruct (frame_below_lo RT AF Σ m f k lo ART0 INF LOW) as (BF1 & BF2 & BF3).
assert (FSZ : 0 <= fs_size k) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
destruct SLV as (INB & INL & ING & NBL & NBG & NLG).
destruct (live_below_lo RT AF Σ m Bd _ lo ART0 INB LOW) as (B0 & B1 & _).
destruct (live_below_lo RT AF Σ m L _ lo ART0 INL LOW) as (L0 & L1 & _).
destruct (live_below_lo RT AF Σ m Gv _ lo ART0 ING LOW) as (G0' & G1 & _).
destruct (live_below_lo RT AF Σ m Dsy _ lo ART0 INSY LOW) as (S0 & S1 & _).
pose proof FOK as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12). unfold int31 in *.
set (LV := pgi_rest Bd L Gv (rt_live RT Σ)) in *.
assert (SUBLV : forall e, In e LV -> In e (rt_live RT Σ)) by (intros e He; exact (pgi_rest_sub _ _ _ _ _ He)).
assert (SPL : forall a, aclient LV (rt_frames RT Σ) usp a -> usp <= a \/ a < rt_sp0 RT Σ - STACK_WIN).
{ intros a Ha. apply (aclient_split RT AF Σ m usp a ART0). apply (aclient_mono _ _ _ _ _ _ _ Ha); [exact SUBLV| auto| apply Z.le_refl]. }
pose proof (wpre_length _ _ LPRE) as LL. unfold zlength in LFILL.
assert (LFS : os_lacing_fill os <= os_lacing_storage os) by (clear - LL LFILL LLEN; lia).
assert (AT : A + 408 < 2^63) by (clear - FA2 BF1 LOR SPT FSZ; unfold RT_STACK, USTACK_TOP in *; lia).
destruct (frame_live_apart RT AF Σ m f k Bd _ ART0 INF INB) as (FLB & _).
destruct (frame_live_apart RT AF Σ m f k L _ ART0 INF INL) as (FLL & _).
destruct (frame_live_apart RT AF Σ m f k Gv _ ART0 INF ING) as (FLG & _).
destruct (frame_live_apart RT AF Σ m f k Dsy _ ART0 INF INSY) as (FLS & _).
assert (SEP_GL : L + 4 * os_lacing_storage os <= G \/ G + 32 <= L) by (clear - FLL FG1 FG2; lia).
assert (SEP_GG : Gv + 8 * os_lacing_storage os <= G \/ G + 32 <= Gv) by (clear - FLG FG1 FG2; lia).
pose proof (live_apart2 Σ m L _ Bd _ ART0 INL INB ltac:(congruence)) as SEP_LB.
pose proof (live_apart2 Σ m L _ Gv _ ART0 INL ING ltac:(congruence)) as SEP_LG.
pose proof (live_apart2 Σ m L _ Dsy _ ART0 INL INSY NSL) as SEP_LS.
pose proof (live_apart2 Σ m Gv _ Bd _ ART0 ING INB ltac:(congruence)) as SEP_GvB.
pose proof (live_apart2 Σ m Gv _ Dsy _ ART0 ING INSY NSG) as SEP_GvS.
assert (SEP_AB : Bd + os_body_storage os <= A \/ A + 408 <= Bd) by (clear - FLB FA1 FA2; lia).
assert (SEP_AL : L + 4 * os_lacing_storage os <= A \/ A + 408 <= L) by (clear - FLL FA1 FA2; lia).
assert (SEP_AGv : Gv + 8 * os_lacing_storage os <= A \/ A + 408 <= Gv) by (clear - FLG FA1 FA2; lia).
assert (SEP_AS : Dsy + nsy <= A \/ A + 408 <= Dsy) by (clear - FLS FA1 FA2; lia).
clear FLB FLL FLG FLS.
rewrite stream_cells_r_eq in OS. unfold stream_cells_r in OS. unfold page_cells in OG. unfold pgi_frame in FR.
destruct (Z.eq_dec (os_lacing_returned os) 0) as [LRZ|LRNZ].
-
assert (ERL : ret_lacing os = os) by (unfold ret_lacing; rewrite LRZ; reflexivity).
rewrite LRZ in Hc.
cps_norm. cps_hide.
cps_seg (pgi_l0 A usp (pg_body_len og) (Dsy + pg_hdr og + pg_header_len og) (Dsy + pg_hdr og) v25 v22 hs).
lazymatch type of POST with ?x = _ => subst x end.
eapply (Hk _ m lws gws); try eassumption.
+ rewrite ERL, stream_cells_r_eq. exact OS.
+ rewrite ERL. exact LPRE.
- assert (ERL : ret_lacing os = set_lacing os (zdrop (os_lacing_returned os) (os_lacing os)) (zdrop (os_lacing_returned os) (os_granules os)) (os_lacing_storage os)
(os_lacing_fill os - os_lacing_returned os) (os_lacing_packet os - os_lacing_returned os) 0).
{ unfold ret_lacing. replace (os_lacing_returned os =? 0) with false by (symmetry; apply Z.eqb_neq; exact LRNZ). reflexivity. }
assert (LBL : Z.of_nat (length (u32s lws)) = 4 * os_lacing_storage os) by (rewrite u32s_length; lia).
assert (LBG : Z.of_nat (length (u64s gws)) = 8 * os_lacing_storage os) by (rewrite u64s_length; lia).
destruct (Z.eq_dec (os_lacing_fill os) (os_lacing_returned os)) as [LFE|LFNE].
+
apply u32arr_u8, u8arr_rw_CB in LAC. apply u64arr_u8, u8arr_rw_CB in GRA.
cps_norm. cps_hide.
cps_seg (pgi_l1 A Bd (os_body_fill os) (os_body_returned os) L Gv (os_lacing_fill os) (os_lacing_packet os) (os_lacing_returned os) usp
(pg_body_len og) (Dsy + pg_hdr og + pg_header_len og) (Dsy + pg_hdr og) v25 v22 shdr hs os).
destruct POST as (m2 & x10' & x11' & -> & MU2 & WM2 & MI2 & OS2). unfold stream_cells_r in OS2.
clear OS. cps_seg_post.
apply u8arr_rw_CB, u8_u32arr in LAC. apply u8arr_rw_CB, u8_u64arr in GRA.
eapply (Hk _ m2 lws gws); try eassumption.
* rewrite stream_cells_ret_lacing, ERL. cbn [set_lacing os_lacing_fill os_lacing_packet os_lacing_returned]. exact OS2.
* rewrite ERL. cbn [set_lacing os_lacing]. unfold wpre, zdrop. rewrite skipn_all2 by lia. cbn. split; [reflexivity| lia].
+
set (nr := Z.to_nat (os_lacing_returned os)). set (nf := Z.to_nat (os_lacing_fill os - os_lacing_returned os)).
assert (NRF : (nr + nf <= length lws)%nat) by (unfold nr, nf; lia).

set (lb := u32s lws) in *.
set (l1 := firstn (4 * nf) lb). set (l2 := skipn (4 * nf) lb). set (lsrc := firstn (4 * nf) (skipn (4 * nr) lb)).
assert (LBn : length lb = (4 * length lws)%nat) by (unfold lb; apply u32s_length).
assert (Ll1 : Z.of_nat (length l1) = 4 * (os_lacing_fill os - os_lacing_returned os)) by (unfold l1; rewrite firstn_length_le by lia; unfold nf; lia).
assert (LEQ : length lsrc = length l1) by (unfold lsrc, l1; rewrite !firstn_length_le by (rewrite ?length_skipn; lia); reflexivity).
assert (Lls : Z.of_nat (length lsrc) = 4 * (os_lacing_fill os - os_lacing_returned os)) by (rewrite LEQ; exact Ll1).
assert (Ll2 : Z.of_nat (length l2) = 4 * os_lacing_storage os - 4 * (os_lacing_fill os - os_lacing_returned os)) by (unfold l2; rewrite length_skipn; unfold nf in *; lia).
assert (EL : lb = l1 ++ l2) by (symmetry; apply firstn_skipn).
apply u32arr_u8 in LAC. fold lb in LAC.
pose proof (bytes_at_sub m L lb (4 * nr) (4 * nf) (proj1 LAC) ltac:(lia)) as LSRC. fold lsrc in LSRC.
replace (L + Z.of_nat (4 * nr)) with (L + 4 * os_lacing_returned os) in LSRC by (unfold nr; lia).
rewrite EL in LAC. apply u8arr_app in LAC. destruct LAC as (P1 & P2). apply u8arr_rw_CB in P1, P2.

set (gb := u64s gws) in *.
set (g1 := firstn (8 * nf) gb). set (g2 := skipn (8 * nf) gb). set (gsrc := firstn (8 * nf) (skipn (8 * nr) gb)).
assert (GBn : length gb = (8 * length gws)%nat) by (unfold gb; apply u64s_length).
assert (Lg1 : Z.of_nat (length g1) = 8 * (os_lacing_fill os - os_lacing_returned os)) by (unfold g1; rewrite firstn_length_le by lia; unfold nf; lia).
assert (GEQ : length gsrc = length g1) by (unfold gsrc, g1; rewrite !firstn_length_le by (rewrite ?length_skipn; lia); reflexivity).
assert (Lgs : Z.of_nat (length gsrc) = 8 * (os_lacing_fill os - os_lacing_returned os)) by (rewrite GEQ; exact Lg1).
assert (Lg2 : Z.of_nat (length g2) = 8 * os_lacing_storage os - 8 * (os_lacing_fill os - os_lacing_returned os)) by (unfold g2; rewrite length_skipn; unfold nf in *; lia).
assert (EG : gb = g1 ++ g2) by (symmetry; apply firstn_skipn).
apply u64arr_u8 in GRA. fold gb in GRA.
pose proof (bytes_at_sub m Gv gb (8 * nr) (8 * nf) (proj1 GRA) ltac:(lia)) as GSRC. fold gsrc in GSRC.
replace (Gv + Z.of_nat (8 * nr)) with (Gv + 8 * os_lacing_returned os) in GSRC by (unfold nr; lia).
rewrite EG in GRA. apply u8arr_app in GRA. destruct GRA as (Q1 & Q2). apply u8arr_rw_CB in Q1, Q2.
assert (EDl2 : l2 = skipn (4 * nf) lb) by reflexivity. assert (EDls : lsrc = firstn (4 * nf) (skipn (4 * nr) lb)) by reflexivity.
assert (EDg2 : g2 = skipn (8 * nf) gb) by reflexivity. assert (EDgs : gsrc = firstn (8 * nf) (skipn (8 * nr) gb)) by reflexivity.
clearbody l1 l2 lsrc g1 g2 gsrc.
assert (NAL' : forall a, aclient LV (rt_frames RT Σ) usp a -> ~ (L <= a < L + Z.of_nat (length lsrc))).
{ intros a Ha. specialize (NAL a Ha). clear - NAL Lls LL LFILL LLEN LRP. lia. }
assert (NAG' : forall a, aclient LV (rt_frames RT Σ) usp a -> ~ (Gv <= a < Gv + Z.of_nat (length gsrc))).
{ intros a Ha. specialize (NAG a Ha). clear - NAG Lgs LL LFILL LLEN LRP. lia. }
pose proof (proj2 P1) as WRL. cbn [cells_size csize Nat.add] in WRL. rewrite Nat.add_0_r, <- LEQ in WRL.
pose proof (proj2 Q1) as WRG. cbn [cells_size csize Nat.add] in WRG. rewrite Nat.add_0_r, <- GEQ in WRG.
assert (EU : bv_unsigned (Z_to_bv 64 (usp + -144)) = usp + -144) by (apply unsigned_lit; clear - LOR SPT BF3; unfold RT_STACK, USTACK_TOP, SH_HI in *; lia).
cps_norm. cps_hide.
cps_seg (pgi_l2 A Bd (os_body_fill os) (os_body_returned os) L Gv (os_lacing_fill os) (os_lacing_packet os) (os_lacing_returned os) usp
(pg_body_len og) (Dsy + pg_hdr og + pg_header_len og) (Dsy + pg_hdr og) v25 v22 shdr hs os).
1: { clear - L1 LL LFILL LLEN LOR SPT. lia. }
lazymatch type of POST with ?x = _ => subst x end.

lazymatch goal with H : ASTA _ _ _ (eq _) _ |- _ => unfold pgi_regs in H; rewrite <- Lls in H end.
kp_all.
cps_rt (MMOV Σ PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m L (L + 4 * os_lacing_returned os) lsrc lo).
all: [> .. | ].
all: lazymatch goal with
| |- call_ok _ _ _ _ _ => cps_callok
| |- checked_src _ _ _ _ _ _ _ => idtac
| |- checked_dst _ _ _ _ _ _ => idtac
| |- bytes_at _ _ _ _ => exact LSRC
| |- _ => try (clear - L0 L1 LRP LPF F4 F5 LOR SPT Lls LFS LSM; lia)
end.
{ apply (live_checked_src RT AF Σ m _ lo L (4 * os_lacing_storage os)); [eassumption| exact INL| lia| lia| exact L1]. }
{ apply (live_checked_dst RT AF Σ m _ L (4 * os_lacing_storage os)); [eassumption| exact INL| lia| lia| exact WRL]. }
intros kc2 Hc2. unfold icpt_postF in Hc2.
cps_unpack Hc2 as (m3 & RS3 & (ART3 & MI3 & WM3 & ST3) & PRES3 & BY3).
pose proof (ogg_bytes_piece m m3 L lsrc WRL WM3 BY3) as P1'. clear BY3 P1 LSRC.
tx P2 ltac:(cls_live INL). tx Q1 ltac:(cls_live ING). tx Q2 ltac:(cls_live ING). tx GSRC ltac:(cls_live ING).
tx OS ltac:(cls_frame INF). tx FR ltac:(cls_stack). tx BODY ltac:(cls_live INB).
tx OG ltac:(cls_frame INF). tx HS ltac:(cls_live INSY). tx BS ltac:(cls_live INSY).

cps_seg (pgi_l3 A Bd (os_body_fill os) (os_body_returned os) L Gv (os_lacing_fill os) (os_lacing_packet os) (os_lacing_returned os) usp
(pg_body_len og) (Dsy + pg_hdr og + pg_header_len og) (Dsy + pg_hdr og) shdr hs os).
1: { clear - G1 LFS LOR SPT. lia. }
lazymatch type of POST with ?x = _ => subst x end.
lazymatch goal with H : ASTA _ _ _ (eq _) _ |- _ => unfold pgi_regs in H; rewrite <- Lgs in H end.
pose proof (wr_at_transport asegs m m3 Gv _ WRG WM3) as WRG3.
kp_all.
cps_rt (MMOV Σ PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 Gv (Gv + 8 * os_lacing_returned os) gsrc lo).
all: [> .. | ].
all: lazymatch goal with
| |- call_ok _ _ _ _ _ => cps_callok
| |- checked_src _ _ _ _ _ _ _ => idtac
| |- checked_dst _ _ _ _ _ _ => idtac
| |- bytes_at _ _ _ _ => exact GSRC
| |- _ => try (clear - G0' G1 LRP LPF F4 F5 LOR SPT Lgs LFS LSM; lia)
end.
{ apply (live_checked_src RT AF Σ m3 _ lo Gv (8 * os_lacing_storage os)); [eassumption| exact ING| lia| lia| exact G1]. }
{ apply (live_checked_dst RT AF Σ m3 _ Gv (8 * os_lacing_storage os)); [eassumption| exact ING| lia| lia| exact WRG3]. }
intros kc4 Hc4. unfold icpt_postF in Hc4.
cps_unpack Hc4 as (m5 & RS5 & (ART5 & MI5 & WM5 & ST5) & PRES5 & BY5).
pose proof (ogg_bytes_piece m3 m5 Gv gsrc WRG3 WM5 BY5) as Q1'. clear BY5 Q1 GSRC.
tx P1' ltac:(cls_live INL). tx P2 ltac:(cls_live INL). tx Q2 ltac:(cls_live ING).
tx OS ltac:(cls_frame INF). tx FR ltac:(cls_stack). tx BODY ltac:(cls_live INB).
tx OG ltac:(cls_frame INF). tx HS ltac:(cls_live INSY). tx BS ltac:(cls_live INSY).

cps_seg (pgi_l4 A Bd (os_body_fill os) (os_body_returned os) L Gv (os_lacing_fill os) (os_lacing_packet os) (os_lacing_returned os) usp
(pg_body_len og) (Dsy + pg_hdr og + pg_header_len og) (Dsy + pg_hdr og) shdr hs os).
destruct POST as (m6 & x10' & x11' & -> & MU6 & WM6 & MI6 & OS6). unfold stream_cells_r in OS6.
clear OS. cps_seg_post.

assert (LAC6 : u32arr asegs m6 L (firstn nf (skipn nr lws) ++ skipn nf lws)).
{ apply u8_u32arr. rewrite <- u32_move by exact NRF. fold lb. rewrite <- EDls, <- EDl2.
apply u8arr_app. split; [apply u8arr_rw_CB; exact P1'|]. rewrite LEQ. apply u8arr_rw_CB. exact P2. }
assert (GRA6 : u64arr asegs m6 Gv (firstn nf (skipn nr gws) ++ skipn nf gws)).
{ apply u8_u64arr. rewrite <- u64_move by lia. fold gb. rewrite <- EDgs, <- EDg2.
apply u8arr_app. split; [apply u8arr_rw_CB; exact Q1'|]. rewrite GEQ. apply u8arr_rw_CB. exact Q2. }
eapply (Hk _ m6 _ _); try eassumption.
* rewrite stream_cells_ret_lacing, ERL. cbn [set_lacing os_lacing_fill os_lacing_packet os_lacing_returned]. exact OS6.
* rewrite ERL. cbn [set_lacing os_lacing]. unfold zdrop. fold nr.
replace nf with (length (os_lacing os) - nr)%nat by (unfold nf, nr; lia). apply wpre_move; [exact LPRE| unfold nr; lia].
* rewrite length_app, firstn_length_le, length_skipn by (rewrite length_skipn; lia). lia.
* rewrite length_app, firstn_length_le, length_skipn by (rewrite length_skipn; lia). lia.
Qed.

Lemma live_remove_In : forall p (l : list (Z * Z)) e, In e (live_remove p l) <-> In e l /\ fst e <> p.
Proof.
intros p l e. unfold live_remove. rewrite <- !stdpp.base.list_elem_of_In, stdpp.list_basics.list.list_elem_of_filter.
destruct (Z.eqb_spec (fst e) p) as [E|E]; cbn [negb]; split; intros [H1 H2]; try tauto; split; auto; exact I.
Qed.

Lemma pgi_rest_In : forall Bd L Gv live e, In e (pgi_rest Bd L Gv live) <-> In e live /\ fst e <> Bd /\ fst e <> L /\ fst e <> Gv.
Proof. intros. unfold pgi_rest. rewrite !live_remove_In. tauto. Qed.

Lemma chunk_apart_aclient : forall (Σ Σ1 : rts RT) (m1 : mem) p n l1 l2 LVx usp a,
ART RT Σ1 m1 -> rt_live RT Σ1 = l1 ++ (p, n) :: l2 -> (forall e, In e LVx -> In e (l1 ++ l2)) ->
rt_frames RT Σ1 = rt_frames RT Σ -> rt_sp0 RT Σ1 = rt_sp0 RT Σ -> rt_sp0 RT Σ - STACK_WIN <= usp ->
aclient LVx (rt_frames RT Σ) usp a -> ~ (p <= a < p + n).
Proof using AF.
intros Σ Σ1 m1 p n l1 l2 LVx usp a ART1 LV SUB FRS SP0 LU Ha Hin.
assert (INL : In (p, n) (rt_live RT Σ1)) by (rewrite LV; apply in_or_app; right; left; reflexivity).
pose proof (af_live_range RT AF Σ1 m1 p n ART1 INL) as (L0 & L1 & L2). rewrite SP0 in L1.
destruct Ha as [H|[H|[H|[H|H]]]].
- lia.
- pose proof (X000.client_static_range a H). unfold SEGTOP_A in *. lia.
- destruct H as (p' & n' & Hin' & Hp').
destruct (af_live_disj RT AF Σ1 m1 p n p' n' l1 l2 ART1 LV (SUB _ Hin')); lia.
- destruct H as (f & k & Hinf & Hf). rewrite <- FRS in Hinf.
pose proof (af_frames_range RT AF Σ1 m1 f k ART1 Hinf) as (_ & _ & _ & R3). destruct (R3 p n INL); lia.
- destruct H as (f & k & Hinf & Hf). rewrite <- FRS in Hinf.
pose proof (af_fshadow_apart RT AF Σ1 m1 f k ART1 Hinf) as (SL & _). destruct (SL p n INL); lia.
Qed.

Lemma rest_apart : forall (Σ : rts RT) (m : mem) Bd L Gv p n usp a,
ART RT Σ m -> In (p, n) (rt_live RT Σ) -> (p = Bd \/ p = L \/ p = Gv) -> rt_sp0 RT Σ - STACK_WIN <= usp ->
aclient (pgi_rest Bd L Gv (rt_live RT Σ)) (rt_frames RT Σ) usp a -> ~ (p <= a < p + n).
Proof using AF.
intros Σ m Bd L Gv p n usp a ART0 IN PE LU Ha.
destruct (in_split _ _ IN) as (l1 & l2 & E).
apply (chunk_apart_aclient Σ Σ m p n l1 l2 (pgi_rest Bd L Gv (rt_live RT Σ)) usp a ART0 E); [| reflexivity| reflexivity| exact LU| exact Ha].
intros e He. apply pgi_rest_In in He. destruct He as (He & N1 & N2 & N3). rewrite E in He.
apply in_app_or in He. apply in_or_app. destruct He as [He|[He|He]]; [left; exact He| | right; exact He].
subst e. cbn [fst] in *. exfalso. destruct PE as [->|[->| ->]]; congruence.
Qed.

Lemma wpre_firstn_ext : forall l (ws ws' : list word), wpre l ws -> firstn (length ws) ws' = ws -> wpre l ws'.
Proof.
intros l ws ws' [P LE] E. assert (LW : (length ws <= length ws')%nat).
{ destruct (Nat.le_gt_cases (length ws) (length ws')) as [H|H]; [exact H|]. rewrite firstn_all2 in E by lia. rewrite E in H. lia. }
split; [| lia]. transitivity (firstn (length l) (firstn (length ws) ws')); [rewrite firstn_firstn; f_equal; lia| rewrite E; exact P].
Qed.
Lemma body_pre_firstn_ext : forall body (bytes bytes' : list byte), body_pre body bytes -> firstn (length bytes) bytes' = bytes -> body_pre body bytes'.
Proof.
intros body bytes bytes' [P LE] E. assert (LW : (length bytes <= length bytes')%nat).
{ destruct (Nat.le_gt_cases (length bytes) (length bytes')) as [H|H]; [exact H|]. rewrite firstn_all2 in E by lia. rewrite E in H. lia. }
split; [| lia]. transitivity (firstn (length body) (ubytes (firstn (length bytes) bytes'))); [rewrite ubytes_firstn, firstn_firstn; f_equal; lia| rewrite E; exact P].
Qed.

Lemma live_head_apart : forall (Σ1 : rts RT) (m1 : mem) p n rest p2 n2, ART RT Σ1 m1 -> rt_live RT Σ1 = (p, n) :: rest -> In (p2, n2) rest ->
p + n <= p2 \/ p2 + n2 <= p.
Proof using AF. intros Σ1 m1 p n rest p2 n2 ART1 E IN. exact (af_live_disj RT AF Σ1 m1 p n p2 n2 [] rest ART1 E IN). Qed.
Lemma live_second_apart : forall (Σ1 : rts RT) (m1 : mem) p0 n0 p n rest p2 n2, ART RT Σ1 m1 -> rt_live RT Σ1 = (p0, n0) :: (p, n) :: rest ->
In (p2, n2) rest -> p + n <= p2 \/ p2 + n2 <= p.
Proof using AF. intros. apply (af_live_disj RT AF Σ1 m1 p n p2 n2 [(p0, n0)] rest); [assumption| assumption| right; assumption]. Qed.

Lemma pgi_phaseF : forall (Σ : rts RT) PMc (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x27 x28 x29 x30 x31 : word) F fc (m0 m : mem)
(LV : list (Z * Z)) (frs : list (Z * nat)) (A G Dsy nsy Bd L Gv f lo segptr bosv : Z) (k : nat) (og : page) (os5 : stream_st bptr)
(shdr hs bs bodybytes j0 : list byte) (lws gws : list word),
fdfs_only PMc -> mat_stable PMc ->
rw_cells asegs m A (stream_cells Bd L Gv shdr os5) -> length shdr = 284%nat -> 0 < A ->
rw_cells asegs m Bd [CB (length bodybytes) bodybytes] -> Z.of_nat (length bodybytes) = os_body_storage os5 ->
u32arr asegs m L lws -> wpre (os_lacing os5) lws -> Z.of_nat (length lws) = os_lacing_storage os5 ->
u64arr asegs m Gv gws -> Z.of_nat (length gws) = os_lacing_storage os5 ->
rw_cells asegs m (bv_unsigned sp + -144) (pgi_frame ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j0 hs) ->
rw_cells asegs m G (page_cells Dsy og) ->
bytes_at asegs m (Dsy + pg_hdr og) hs -> bytes_at asegs m (Dsy + pg_hdr og + pg_header_len og) bs ->
stream_fields_ok os5 -> os_lacing_fill os5 + (znth (ubytes hs) 26 - segptr) + 1 <= os_lacing_storage os5 -> 0 <= segptr <= znth (ubytes hs) 26 ->
(bosv = 0 \/ bosv = Z.land (znth (ubytes hs) 5) 2) ->
zlength (os_lacing os5) = os_lacing_fill os5 -> 0 <= os_lacing_packet os5 <= os_lacing_fill os5 -> lacing_vals_ok (os_lacing os5) ->
length hs = (27 + Z.to_nat (znth (ubytes hs) 26))%nat -> Z.of_nat (length hs) = pg_header_len og -> Z.of_nat (length bs) = pg_body_len og ->
0 <= pg_hdr og -> pg_hdr og + pg_header_len og + pg_body_len og <= nsy ->
In (Bd, os_body_storage os5) (rt_live RT Σ) -> In (L, 4 * os_lacing_storage os5) (rt_live RT Σ) -> In (Gv, 8 * os_lacing_storage os5) (rt_live RT Σ) ->
In (Dsy, nsy) (rt_live RT Σ) -> Bd <> L -> Bd <> Gv -> L <> Gv -> Dsy <> L -> Dsy <> Gv ->
rt_frames RT Σ = frs -> In (f, k) frs -> f <= A -> A + 408 <= f + fs_size k - 8 -> f <= G -> G + 32 <= f + fs_size k - 8 ->
(forall e, In e LV -> In e (rt_live RT Σ)) ->
(forall a, aclient LV frs (bv_unsigned sp) a -> bv_unsigned sp <= a \/ a < rt_sp0 RT Σ - STACK_WIN) ->
(forall a, aclient LV frs (bv_unsigned sp) a -> ~ (L <= a < L + 4 * os_lacing_storage os5)) ->
(forall a, aclient LV frs (bv_unsigned sp) a -> ~ (Gv <= a < Gv + 8 * os_lacing_storage os5)) ->
ART RT Σ m -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp + -144) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK + 256 <= bv_unsigned sp -> bv_unsigned sp + 16 <= USTACK_TOP ->
rt_pres_fp LV frs (bv_unsigned sp) [(A, A + 408)] m0 m ->
forall T c,
ASTA RT Σ PMc (eq (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp (Z_to_bv 64 0x630458) x5 x6 x7 (Z_to_bv 64 A) (Z_to_bv 64 (znth (ubytes hs) 5)) x10
x11 x12 x13 x14 x15 x16 x17
x18 x19 x20 (Z_to_bv 64 (Dsy + pg_hdr og)) x22 (Z_to_bv 64 segptr) (Z_to_bv 64 (ogg_page_pageno (ubytes hs))) (Z_to_bv 64 bosv)
(Z_to_bv 64 (znth (ubytes hs) 26)) x27 x28 x29 x30 x31)
F (Z_to_bv 64 0xb95b0) fc None m (seg_rom asegs))) c ->
(forall c', ASTA RT Σ PMc (fun ms => exists m' (lws' gws' : list word),
ret_stL (fun F' fc' => F' = F /\ fc' = fc) ra sp gp (Z_to_bv 64 0x630458) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) m' ms
/\ rt_after_f RT Σ (bv_unsigned sp) lo m0 m'
/\ rt_pres_fp LV frs (bv_unsigned sp) [(A, A + 408)] m0 m'
/\ rw_cells asegs m' A (stream_cells Bd L Gv shdr (pagein_segments os5 (ubytes hs) bosv segptr))
/\ rw_cells asegs m' Bd [CB (length bodybytes) bodybytes]
/\ u32arr asegs m' L lws' /\ wpre (os_lacing (pagein_segments os5 (ubytes hs) bosv segptr)) lws' /\ Z.of_nat (length lws') = os_lacing_storage os5
/\ u64arr asegs m' Gv gws' /\ Z.of_nat (length gws') = os_lacing_storage os5) c' ->
realizes asegs c' T) ->
realizes asegs c T.
Proof using AF.
intros Σ PMc ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x27 x28 x29 x30 x31 F fc m0 m
LV frs A G Dsy nsy Bd L Gv f lo segptr bosv k og os5 shdr hs bs bodybytes j0 lws gws
FDO MST OS HL A0 BODY BLEN LAC LPRE LLEN GRA GLEN FR OG HS BS FOK Hls Hseg Hbos LFILL LPK LOK LENH HLEN BSLEN PG0 PGIN
INB INL ING INSY NBL NBG NLG NSL NSG EFR INF FA1 FA2 FG1 FG2 SUBLV SPL NAL NAG ART0 MI0 ST0 LOW LOR SPT PF T c Hc Hk.
subst frs.
destruct (frame_below_lo RT AF Σ m f k lo ART0 INF LOW) as (BF1 & BF2 & BF3).
assert (FSZ : 0 <= fs_size k) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
destruct (live_below_lo RT AF Σ m Bd _ lo ART0 INB LOW) as (B0 & B1 & _).
destruct (live_below_lo RT AF Σ m L _ lo ART0 INL LOW) as (L0 & L1 & _).
destruct (live_below_lo RT AF Σ m Gv _ lo ART0 ING LOW) as (G0' & G1 & _).
destruct (live_below_lo RT AF Σ m Dsy _ lo ART0 INSY LOW) as (S0 & S1 & _).
destruct (frame_live_apart RT AF Σ m f k Bd _ ART0 INF INB) as (FLB & _).
destruct (frame_live_apart RT AF Σ m f k L _ ART0 INF INL) as (FLL & _).
destruct (frame_live_apart RT AF Σ m f k Gv _ ART0 INF ING) as (FLG & _).
destruct (frame_live_apart RT AF Σ m f k Dsy _ ART0 INF INSY) as (FLS & _).
pose proof (live_apart2 Σ m L _ Bd _ ART0 INL INB ltac:(congruence)) as SEP_LB.
pose proof (live_apart2 Σ m L _ Gv _ ART0 INL ING ltac:(congruence)) as SEP_LG.
pose proof (live_apart2 Σ m L _ Dsy _ ART0 INL INSY NSL) as SEP_LS.
pose proof (live_apart2 Σ m Gv _ Bd _ ART0 ING INB ltac:(congruence)) as SEP_GvB.
pose proof (live_apart2 Σ m Gv _ Dsy _ ART0 ING INSY NSG) as SEP_GvS.
set (ls := os_lacing_storage os5) in *. set (H := Dsy + pg_hdr og) in *.
pose proof (byte_range (nth (Z.to_nat 26) hs (Z_to_bv 8 0))) as H26. rewrite <- (znth_ubytes hs 26) in H26 by lia.
assert (HR : Dsy <= H /\ H + Z.of_nat (length hs) <= Dsy + nsy) by (unfold H; clear - PG0 PGIN HLEN BSLEN; lia).
assert (SEP_AL : L + 4 * ls <= A \/ A + 408 <= L) by (clear - FLL FA1 FA2; lia).
assert (SEP_AGv : Gv + 8 * ls <= A \/ A + 408 <= Gv) by (clear - FLG FA1 FA2; lia).
assert (SEP_AH : H + Z.of_nat (length hs) <= A \/ A + 408 <= H) by (clear - FLS FA1 FA2 HR; lia).
assert (SEP_HL : H + Z.of_nat (length hs) <= L \/ L + 4 * ls <= H) by (clear - SEP_LS HR; lia).
assert (SEP_HG : H + Z.of_nat (length hs) <= Gv \/ Gv + 8 * ls <= H) by (clear - SEP_GvS HR; lia).
assert (SEP_LG' : L + 4 * ls <= Gv \/ Gv + 8 * ls <= L) by (clear - SEP_LG; lia).
assert (SEP_GB : Bd + os_body_storage os5 <= G \/ G + 32 <= Bd) by (clear - FLB FG1 FG2; lia).
assert (SEP_GL : L + 4 * ls <= G \/ G + 32 <= L) by (clear - FLL FG1 FG2; lia).
assert (SEP_GG : Gv + 8 * ls <= G \/ G + 32 <= Gv) by (clear - FLG FG1 FG2; lia).
assert (SEP_AB : Bd + os_body_storage os5 <= A \/ A + 408 <= Bd) by (clear - FLB FA1 FA2; lia).
assert (SEP_AS : Dsy + nsy <= A \/ A + 408 <= Dsy) by (clear - FLS FA1 FA2; lia).
assert (PN : 0 <= ogg_page_pageno (ubytes hs) < 2^32) by (apply pageno_range; lia).
assert (LOSP : lo + 144 <= bv_unsigned sp) by (clear - LOR; unfold RT_STACK in LOR; lia).
assert (ALO : A + 408 <= lo) by (clear - FA2 BF1; lia).
assert (TOPL : L + 4 * ls < 2^63) by (clear - L1 LOR SPT; unfold RT_STACK, USTACK_TOP in *; lia).
assert (TOPG : Gv + 8 * ls < 2^63) by (clear - G1 LOR SPT; unfold RT_STACK, USTACK_TOP in *; lia).
assert (TOPH : H + Z.of_nat (length hs) < 2^63) by (clear - HR S1 LOR SPT; unfold RT_STACK, USTACK_TOP in *; lia).
assert (HLO : H + Z.of_nat (length hs) <= lo) by (clear - HR S1; lia).
assert (HH : 0 <= H) by (clear - HR S0; lia).
clear FLB FLL FLG FLS.
unfold page_cells in OG.
cps_norm. cps_hide.
cps_seg (X0a0.pi_final A Bd L Gv H lo shdr hs os5 ra sp gp (Z_to_bv 64 0x630458) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc x1 segptr bosv
(ogg_page_pageno (ubytes hs)) (Z_to_bv 64 (znth (ubytes hs) 18)) (Z_to_bv 64 (znth (ubytes hs) 21)) j0
LENH H26 HL FOK Hls Hseg Hbos LFILL LPK LOK A0 L0 G0' HH TOPL TOPG TOPH LOSP ALO SEP_AL SEP_AGv SEP_AH L1 G1 HLO SEP_LG' SEP_HL SEP_HG eq_refl).
unfold final_post in POST.
destruct POST as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & lws1 & gws1 & -> & MU1 & WM1 & MI1 & OS1 & LAC1 & LPRE1 & LLEN1 & GRA1 & GLEN1 & ST1 & HS1).
clear OS FR HS. cps_seg_post.
apply Hk. eapply ASTA_conseq; [eassumption|]. intros ms <-. exists m1, lws1, gws1.
split; [unfold ret_stL; do 16 eexists; split; [reflexivity| split; reflexivity]|].
split; [split; [assumption| split; [exact MI1| exact ST1]]|].
split; [exact PF|]. split; [exact OS1|]. split; [exact BODY|].
split; [exact LAC1|]. split; [exact LPRE1|]. split; [exact LLEN1|]. split; [exact GRA1| exact GLEN1].
Qed.

Lemma u8arr_split3 : forall (m : mem) A (bb : list byte) a n,
u8arr asegs m A bb -> (a + n <= length bb)%nat ->
u8arr asegs m A (firstn a bb) /\ u8arr asegs m (A + Z.of_nat a) (firstn n (skipn a bb)) /\ u8arr asegs m (A + Z.of_nat a + Z.of_nat n) (skipn (a + n) bb).
Proof.
intros m A bb a n H LE.
rewrite <- (firstn_skipn a bb) in H. apply u8arr_app in H. destruct H as (H1 & H2).
rewrite firstn_length_le in H2 by lia.
rewrite <- (firstn_skipn n (skipn a bb)) in H2. apply u8arr_app in H2. destruct H2 as (H2 & H3).
rewrite firstn_length_le in H3 by (rewrite length_skipn; lia). rewrite skipn_skipn in H3.
replace (n + a)%nat with (a + n)%nat in H3 by lia.
split; [exact H1| split; [exact H2| exact H3]].
Qed.

Lemma body_pre_copy : forall (body3 zs : list Z) (bodybytes bb2 bsrc : list byte) (fill : nat),
body_pre body3 bodybytes -> length body3 = fill -> firstn (length bodybytes) bb2 = bodybytes ->
ubytes bsrc = zs -> (fill + length bsrc <= length bb2)%nat ->
body_pre (body3 ++ zs) (firstn fill bb2 ++ bsrc ++ skipn (fill + length bsrc) bb2).
Proof.
intros body3 zs bodybytes bb2 bsrc fill (BP1 & BP2) LB FX ZS LE.
assert (LZ : length zs = length bsrc) by (rewrite <- ZS; apply ubytes_length).
assert (EF : firstn fill (ubytes bb2) = body3).
{ rewrite <- BP1, <- FX, ubytes_firstn, firstn_firstn. f_equal. lia. }
split.
- rewrite !ubytes_app, length_app, LZ, LB.
rewrite firstn_app, ubytes_length, firstn_length_le by lia.
rewrite firstn_all2 by (rewrite ubytes_length, firstn_length_le; lia).
replace (fill + length bsrc - fill)%nat with (length bsrc) by lia.
rewrite firstn_app, ubytes_length, Nat.sub_diag, firstn_O, app_nil_r.
rewrite (@firstn_all2 Z (length bsrc) (ubytes bsrc)) by (rewrite ubytes_length; lia).
rewrite ubytes_firstn, EF, ZS. reflexivity.
- rewrite !length_app, firstn_length_le, LZ, LB by lia. lia.
Qed.

Lemma stream_cells_pagein_body : forall Bd L G hdr (os : stream_st bptr) body sk n,
stream_cells Bd L G hdr (pagein_body os body sk n)
= stream_cells_r Bd (os_body_fill os + n) (os_body_returned os) L G (os_lacing_fill os) (os_lacing_packet os) (os_lacing_returned os) hdr os.
Proof. intros. reflexivity. Qed.

Lemma body_expand_res_fields : forall (os : stream_st bptr) n,
os_body (body_expand_res os n) = os_body os /\ os_body_fill (body_expand_res os n) = os_body_fill os /\
os_body_returned (body_expand_res os n) = os_body_returned os /\ os_lacing_storage (body_expand_res os n) = os_lacing_storage os /\
os_lacing_fill (body_expand_res os n) = os_lacing_fill os /\ os_lacing_packet (body_expand_res os n) = os_lacing_packet os /\
os_lacing_returned (body_expand_res os n) = os_lacing_returned os /\ os_lacing (body_expand_res os n) = os_lacing os.
Proof. intros os n. unfold body_expand_res. destruct (os_body_fill os <? os_body_storage os - n); cbn; repeat split; reflexivity. Qed.

Lemma body_expand_res_room : forall (os : stream_st bptr) n, 0 <= n -> os_body_fill os <= os_body_storage os ->
os_body_fill os + n <= os_body_storage (body_expand_res os n) /\ os_body_storage os <= os_body_storage (body_expand_res os n).
Proof. intros os n N0 FS. unfold body_expand_res. destruct (Z.ltb_spec (os_body_fill os) (os_body_storage os - n)); cbn; lia. Qed.

Lemma live_apart_LV : forall (Σ Σ1 : rts RT) (m1 : mem) p n LVx usp a,
ART RT Σ1 m1 -> In (p, n) (rt_live RT Σ1) -> (forall e, In e LVx -> In e (rt_live RT Σ1) /\ fst e <> p) ->
rt_frames RT Σ1 = rt_frames RT Σ -> rt_sp0 RT Σ1 = rt_sp0 RT Σ -> rt_sp0 RT Σ - STACK_WIN <= usp ->
aclient LVx (rt_frames RT Σ) usp a -> ~ (p <= a < p + n).
Proof using AF.
intros Σ Σ1 m1 p n LVx usp a ART1 IN SUB FRS SP0 LU Ha.
destruct (in_split _ _ IN) as (l1 & l2 & E).
apply (chunk_apart_aclient Σ Σ1 m1 p n l1 l2 LVx usp a ART1 E); [| exact FRS| exact SP0| exact LU| exact Ha].
intros e He. destruct (SUB e He) as (He1 & Hne). rewrite E in He1.
apply in_app_or in He1. apply in_or_app. destruct He1 as [He1|[He1|He1]]; [left; exact He1| | right; exact He1].
subst e. cbn [fst] in Hne. congruence.
Qed.

Lemma pgi_phaseX : forall (Σ : rts RT) PMc (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) F fc (m0 m : mem)
(LV : list (Z * Z)) (A G Dsy nsy Bd L Gv f lo n src skipped : Z) (k : nat) (og : page) (os3 : stream_st bptr)
(shdr hs bs bodybytes j0 bsrc : list byte) (body : list Z) (lws gws : list word),
fdfs_only PMc -> mat_stable PMc ->
rw_cells asegs m A (stream_cells Bd L Gv shdr os3) -> length shdr = 284%nat -> 0 < A ->
rw_cells asegs m Bd [CB (length bodybytes) bodybytes] -> Z.of_nat (length bodybytes) = os_body_storage os3 -> body_pre (os_body os3) bodybytes ->
zlength (os_body os3) = os_body_fill os3 -> 0 <= os_body_fill os3 <= os_body_storage os3 -> os_body_storage os3 + n + 1024 <= 64512 ->
rw_cells asegs m L [CB (length (u32s lws)) (u32s lws)] -> rw_cells asegs m Gv [CB (length (u64s gws)) (u64s gws)] ->
rw_cells asegs m (bv_unsigned sp + -144) (pgi_frame ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j0 hs) ->
rw_cells asegs m G (page_cells Dsy og) ->
bytes_at asegs m (Dsy + pg_hdr og) hs -> bytes_at asegs m (Dsy + pg_hdr og + pg_header_len og) bs ->
bytes_at asegs m src bsrc -> Z.of_nat (length bsrc) = n -> 0 < n -> ubytes bsrc = zslice skipped n body ->
Dsy <= src -> src + n <= Dsy + nsy -> Dsy <= Dsy + pg_hdr og -> Dsy + pg_hdr og + pg_header_len og + pg_body_len og <= Dsy + nsy ->
Z.of_nat (length hs) = pg_header_len og -> Z.of_nat (length bs) = pg_body_len og ->
In (Bd, os_body_storage os3) (rt_live RT Σ) -> In (L, Z.of_nat (length (u32s lws))) (rt_live RT Σ) -> In (Gv, Z.of_nat (length (u64s gws))) (rt_live RT Σ) ->
In (Dsy, nsy) (rt_live RT Σ) -> Bd <> L -> Bd <> Gv -> Dsy <> Bd -> 0 < Z.of_nat (length (u32s lws)) -> 0 < Z.of_nat (length (u64s gws)) ->
In (f, k) (rt_frames RT Σ) -> f <= A -> A + 408 <= f + fs_size k - 8 -> f <= G -> G + 32 <= f + fs_size k - 8 -> (A + 408 <= G \/ G + 32 <= A) ->
(forall e, In e LV -> In e (rt_live RT Σ) /\ fst e <> Bd) ->
Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX -> 0 <= rt_credit RT Σ ->
ART RT Σ m -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp + -144) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK + 256 <= bv_unsigned sp -> bv_unsigned sp + 16 <= USTACK_TOP ->
bv_unsigned sp mod 16 = 0 ->
rt_pres_fp LV (rt_frames RT Σ) (bv_unsigned sp) [(A, A + 408)] m0 m ->
forall T c,
ASTA RT Σ PMc (eq (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp (Z_to_bv 64 0x630458) x5 x6 x7 (Z_to_bv 64 A) x9 x10 x11 x12 x13 x14 x15 x16 x17
x18 (Z_to_bv 64 n) (Z_to_bv 64 src) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
F (Z_to_bv 64 0xb957c) fc None m (seg_rom asegs))) c ->
(forall c' (Σ2 : rts RT) (Bd2 : Z) (m' : mem) (bb' : list byte) (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
ASTA RT Σ2 PMc (eq (MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp (Z_to_bv 64 0x630458) y5 y6 y7 (Z_to_bv 64 A) x9 y10 y11 y12 y13 y14 y15 y16 y17
x18 (Z_to_bv 64 n) (Z_to_bv 64 src) x21 x22 x23 x24 x25 x26 x27 y28 y29 y30 y31)
F (Z_to_bv 64 0xb95b0) fc None m' (seg_rom asegs))) c' ->
ART RT Σ2 m' -> mem_inv asegs m' -> stk asegs m' lo (bv_unsigned sp + -144) ->
rw_cells asegs m' (bv_unsigned sp + -144) (pgi_frame ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j0 hs) ->
rw_cells asegs m' A (stream_cells Bd2 L Gv shdr (pagein_body (body_expand_res os3 n) body skipped n)) ->
rw_cells asegs m' Bd2 [CB (length bb') bb'] -> Z.of_nat (length bb') = os_body_storage (body_expand_res os3 n) ->
body_pre (os_body os3 ++ zslice skipped n body) bb' ->
rw_cells asegs m' L [CB (length (u32s lws)) (u32s lws)] -> rw_cells asegs m' Gv [CB (length (u64s gws)) (u64s gws)] ->
rw_cells asegs m' G (page_cells Dsy og) ->
bytes_at asegs m' (Dsy + pg_hdr og) hs -> bytes_at asegs m' (Dsy + pg_hdr og + pg_header_len og) bs ->
rt_pres_fp LV (rt_frames RT Σ) (bv_unsigned sp) [(A, A + 408)] m0 m' ->
In (Bd2, os_body_storage (body_expand_res os3 n)) (rt_live RT Σ2) ->
In (L, Z.of_nat (length (u32s lws))) (rt_live RT Σ2) -> In (Gv, Z.of_nat (length (u64s gws))) (rt_live RT Σ2) -> In (Dsy, nsy) (rt_live RT Σ2) ->
Bd2 <> L -> Bd2 <> Gv -> Dsy <> Bd2 ->
(forall e, In e LV -> In e (rt_live RT Σ2)) -> (length (rt_live RT Σ2) <= length (rt_live RT Σ))%nat ->
((os_body_fill os3 < os_body_storage os3 - n /\ Bd2 = Bd /\ rt_live RT Σ2 = rt_live RT Σ)
\/ (os_body_storage os3 - n <= os_body_fill os3 /\ rt_live RT Σ2 = (Bd2, os_body_storage os3 + n + 1024) :: live_remove Bd (rt_live RT Σ))) ->
rt_frames RT Σ2 = rt_frames RT Σ -> rt_sp0 RT Σ2 = rt_sp0 RT Σ -> rt_credit RT Σ2 = rt_credit RT Σ -> rt_pois RT Σ2 = rt_pois RT Σ ->
realizes asegs c' T) ->
realizes asegs c T.
Proof using AF MCPY BEXP.
intros Σ PMc ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m0 m
LV A G Dsy nsy Bd L Gv f lo n src skipped k og os3 shdr hs bs bodybytes j0 bsrc body lws gws
FDO MST OS HL A0 BODY BLEN BPRE BFILL BF0 BSB LAC GRA FR OG HS BS SRC LSRC N0 ZSRC SR1 SR2 PH1 PH2 HLEN BSLEN
INB INL ING INSY NBL NBG NSB LP0 GP0 INF FA1 FA2 FG1 FG2 SEP_AG SUBLV LVM CR0 ART0 MI0 ST0 LOW LOR SPT SPA PF T c Hc Hk.
set (usp := bv_unsigned sp) in *.
destruct (frame_below_lo RT AF Σ m f k lo ART0 INF LOW) as (BF1 & BF2 & BF3).
assert (FSZ : 0 <= fs_size k) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
destruct (live_below_lo RT AF Σ m Bd _ lo ART0 INB LOW) as (B0 & B1 & _).
destruct (live_below_lo RT AF Σ m L _ lo ART0 INL LOW) as (L0 & L1 & _).
destruct (live_below_lo RT AF Σ m Gv _ lo ART0 ING LOW) as (G0' & G1 & _).
destruct (live_below_lo RT AF Σ m Dsy _ lo ART0 INSY LOW) as (S0 & S1 & _).
assert (EU : bv_unsigned (Z_to_bv 64 (usp + -144)) = usp + -144) by (apply unsigned_lit; clear - LOR SPT BF3; unfold RT_STACK, USTACK_TOP, SH_HI in *; lia).
assert (SUBLVB : forall e, In e LV -> In e (live_remove Bd (rt_live RT Σ))) by (intros e He; destruct (SUBLV e He) as (X1 & X2); apply live_remove_keep; assumption).
assert (SUBLV0 : forall e, In e LV -> In e (rt_live RT Σ)) by (intros e He; exact (proj1 (SUBLV e He))).
assert (SPL : forall a, aclient LV (rt_frames RT Σ) usp a -> usp <= a \/ a < rt_sp0 RT Σ - STACK_WIN).
{ intros a Ha. apply (aclient_split RT AF Σ m usp a ART0). apply (aclient_mono _ _ _ _ _ _ _ Ha); [exact SUBLV0| auto| apply Z.le_refl]. }
assert (INLB : In (L, Z.of_nat (length (u32s lws))) (live_remove Bd (rt_live RT Σ))) by (apply live_remove_keep; [exact INL| cbn [fst]; congruence]).
assert (INGB : In (Gv, Z.of_nat (length (u64s gws))) (live_remove Bd (rt_live RT Σ))) by (apply live_remove_keep; [exact ING| cbn [fst]; congruence]).
assert (INSYB : In (Dsy, nsy) (live_remove Bd (rt_live RT Σ))) by (apply live_remove_keep; [exact INSY| cbn [fst]; exact NSB]).
pose proof (body_expand_res_fields os3 n) as (EX1 & EX2 & EX3 & EX4 & EX5 & EX6 & EX7 & EX8).
destruct (frame_live_apart RT AF Σ m f k L _ ART0 INF INL) as (FLL & _).
destruct (frame_live_apart RT AF Σ m f k Gv _ ART0 INF ING) as (FLG & _).
destruct (frame_live_apart RT AF Σ m f k Dsy _ ART0 INF INSY) as (FLS & _).
destruct (frame_live_apart RT AF Σ m f k Bd _ ART0 INF INB) as (FLB & _).
assert (SEP_AL : L + Z.of_nat (length (u32s lws)) <= A \/ A + 408 <= L) by (clear - FLL FA1 FA2; lia).
assert (SEP_AGv : Gv + Z.of_nat (length (u64s gws)) <= A \/ A + 408 <= Gv) by (clear - FLG FA1 FA2; lia).
assert (SEP_AS : Dsy + nsy <= A \/ A + 408 <= Dsy) by (clear - FLS FA1 FA2; lia).
assert (SEP_GL : L + Z.of_nat (length (u32s lws)) <= G \/ G + 32 <= L) by (clear - FLL FG1 FG2; lia).
assert (SEP_GGv : Gv + Z.of_nat (length (u64s gws)) <= G \/ G + 32 <= Gv) by (clear - FLG FG1 FG2; lia).
assert (SEP_GS : Dsy + nsy <= G \/ G + 32 <= Dsy) by (clear - FLS FG1 FG2; lia).
assert (SEP_GB : Bd + os_body_storage os3 <= G \/ G + 32 <= Bd) by (clear - FLB FG1 FG2; lia).
assert (SEP_AB : Bd + os_body_storage os3 <= A \/ A + 408 <= Bd) by (clear - FLB FA1 FA2; lia).
clear FLL FLG FLS FLB.
cps_norm. cps_hide.

cps_seg (pgi_x1 x1 (Z_to_bv 64 (usp + -144)) gp (Z_to_bv 64 0x630458) x5 x6 x7 (Z_to_bv 64 A) x9 x10 x11 x12 x13 x14 x15 x16 x17
x18 (Z_to_bv 64 n) (Z_to_bv 64 src) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m).
lazymatch type of POST with ?x = _ => subst x end.
kp_all. unfold kp in OS, BODY. apply u8arr_rw_CB in BODY.
cps_norm.
cps_rt (BEXP Σ PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m A Bd L Gv n f lo k os3 shdr bodybytes).
all: [> lazymatch goal with
| |- stk _ _ _ _ => rewrite EU; exact ST0
| |- _ mod 16 = 0 => rewrite EU; clear - SPA; Z.div_mod_to_equations; lia
| |- _ => first [ rewrite EU; ulc | ulc ]
end .. | ].
clear OS BODY.
intros kc2 (Σ2 & Bd2 & Hc2 & INB2 & CASE & EF2 & ES2 & EC2 & EP2).
ogg_unpackL Hc2 as (m2 & bb2 & RS2 & (ART2 & MI2 & ST2) & PRES2 & OS2 & BODY2 & BLEN2 & BPFX2). destruct RS2 as (-> & ->).
tx LAC ltac:(cls_live INLB). tx GRA ltac:(cls_live INGB). tx FR ltac:(cls_stack). tx OG ltac:(cls_frame INF).
tx HS ltac:(cls_live INSYB). tx BS ltac:(cls_live INSYB). tx SRC ltac:(cls_live INSYB).

assert (LOU : rt_sp0 RT Σ - STACK_WIN <= usp) by (clear - LOW LOR; unfold STACK_WIN; lia).
pose proof (body_expand_res_room os3 n ltac:(lia) ltac:(lia)) as (RM1 & RM2).
assert (X2 : In (L, Z.of_nat (length (u32s lws))) (rt_live RT Σ2) /\ In (Gv, Z.of_nat (length (u64s gws))) (rt_live RT Σ2) /\ In (Dsy, nsy) (rt_live RT Σ2)
/\ Bd2 <> L /\ Bd2 <> Gv /\ Dsy <> Bd2
/\ (forall e, In e LV -> In e (rt_live RT Σ2)) /\ (length (rt_live RT Σ2) <= length (rt_live RT Σ))%nat
/\ (forall a, aclient LV (rt_frames RT Σ) usp a -> ~ (Bd2 <= a < Bd2 + os_body_storage (body_expand_res os3 n)))).
{ destruct CASE as [(FITS & -> & E)|(GROW & E)].
- split; [rewrite E; exact INL|]. split; [rewrite E; exact ING|]. split; [rewrite E; exact INSY|].
split; [exact NBL|]. split; [exact NBG|]. split; [exact NSB|].
split; [rewrite E; exact SUBLV0|]. split; [rewrite E; lia|].
intros a Ha. apply (live_apart_LV Σ Σ2 m2 Bd _ LV usp a ART2 INB2); [| exact EF2| exact ES2| exact LOU| exact Ha].
intros e He. rewrite E. exact (SUBLV e He).
- assert (ES : os_body_storage (body_expand_res os3 n) = os_body_storage os3 + n + 1024)
by (unfold body_expand_res; replace (os_body_fill os3 <? _) with false by (symmetry; apply Z.ltb_ge; exact GROW); reflexivity).
pose proof (live_head_apart Σ2 m2 _ _ _ L _ ART2 E INLB) as S1x.
pose proof (live_head_apart Σ2 m2 _ _ _ Gv _ ART2 E INGB) as S2x.
pose proof (live_head_apart Σ2 m2 _ _ _ Dsy _ ART2 E INSYB) as S3x.
split; [rewrite E; right; exact INLB|]. split; [rewrite E; right; exact INGB|]. split; [rewrite E; right; exact INSYB|].
split; [clear - S1x LP0 BF0 N0; lia|]. split; [clear - S2x GP0 BF0 N0; lia|]. split; [clear - S3x N0 SR1 SR2 BF0; lia|].
split; [intros e He; rewrite E; right; exact (SUBLVB e He)|].
split; [rewrite E; cbn [length]; pose proof (live_remove_length_lt Bd _ _ INB) as X; lia|].
intros a Ha. rewrite ES. apply (chunk_apart_aclient Σ Σ2 m2 Bd2 _ [] (live_remove Bd (rt_live RT Σ)) LV usp a ART2);
[exact E| exact SUBLVB| exact EF2| exact ES2| exact LOU| exact Ha]. }
destruct X2 as (INL2 & ING2 & INSY2 & NBL2 & NBG2 & NSB2 & SUB2 & LVM2 & NAB2).
assert (INF2 : In (f, k) (rt_frames RT Σ2)) by (rewrite EF2; exact INF).
assert (LOW2 : rt_sp0 RT Σ2 - STACK_WIN <= lo) by (rewrite ES2; exact LOW).
assert (SUBF2 : forall e, In e (rt_frames RT Σ) -> In e (rt_frames RT Σ2)) by (intros e He; rewrite EF2; exact He).
destruct (live_below_lo RT AF Σ2 m2 Bd2 _ lo ART2 INB2 LOW2) as (B20 & B21 & _).
pose proof (live_apart2 Σ2 m2 Dsy _ Bd2 _ ART2 INSY2 INB2 ltac:(congruence)) as SEP_SB2.
destruct (frame_live_apart RT AF Σ2 m2 f k Bd2 _ ART2 INF2 INB2) as (FLB2 & _).
assert (SEP_AB2 : Bd2 + os_body_storage (body_expand_res os3 n) <= A \/ A + 408 <= Bd2) by (clear - FLB2 FA1 FA2; lia).
assert (SEP_GB2 : Bd2 + os_body_storage (body_expand_res os3 n) <= G \/ G + 32 <= Bd2) by (clear - FLB2 FG1 FG2; lia).
assert (DISJ : Bd2 + os_body_fill os3 + Z.of_nat (length bsrc) <= src \/ src + Z.of_nat (length bsrc) <= Bd2 + os_body_fill os3)
by (clear - SEP_SB2 SR1 SR2 LSRC BF0 RM1 EX2; lia).
clear FLB2. cps_hide.

assert (LB2 : (Z.to_nat (os_body_fill os3) + length bsrc <= length bb2)%nat) by (clear - BLEN2 RM1 LSRC BF0 EX2; lia).
pose proof (u8arr_split3 m2 Bd2 bb2 (Z.to_nat (os_body_fill os3)) (length bsrc) BODY2 LB2) as (P1 & P2 & P3). clear BODY2.
rewrite Z2Nat.id in P2, P3 by lia.
assert (LP2 : length (firstn (length bsrc) (skipn (Z.to_nat (os_body_fill os3)) bb2)) = length bsrc) by (rewrite firstn_length_le; [reflexivity| rewrite length_skipn; lia]).
apply u8arr_rw_CB in P1, P2, P3.
pose proof (proj2 P2) as WR2. cbn [cells_size csize Nat.add] in WR2. rewrite Nat.add_0_r, LP2 in WR2.

rewrite stream_cells_r_eq, EX2 in OS2.
cps_seg (pgi_x2 A Bd2 (os_body_fill os3) (os_body_returned (body_expand_res os3 n)) L Gv (os_lacing_fill (body_expand_res os3 n))
(os_lacing_packet (body_expand_res os3 n)) (os_lacing_returned (body_expand_res os3 n)) n src shdr (body_expand_res os3 n)).
1: (clear - FA2 BF1 LOR SPT FSZ; lia).
1: (clear - B21 RM1 N0 LOR SPT; lia).
lazymatch type of POST with ?x = _ => subst x end.
kp_all.
lazymatch goal with H : ASTA _ _ _ (eq _) _ |- _ => rewrite <- LSRC in H end.
cps_rt (MCPY Σ2 PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2 (Bd2 + os_body_fill os3) src bsrc lo).
all: [> lazymatch goal with
| |- call_ok _ _ _ _ _ => cps_callok
| |- bytes_at _ _ _ _ => unfold kp in SRC; exact SRC
| |- checked_src _ _ _ _ _ _ _ => apply (live_checked_src RT AF Σ2 m2 _ lo Dsy nsy); [exact ART2| exact INSY2| clear - SR1 LSRC; lia| clear - SR2 LSRC; lia| exact S1]
| |- checked_dst _ _ _ _ _ _ => apply (live_checked_dst RT AF Σ2 m2 _ Bd2 (os_body_storage (body_expand_res os3 n))); [exact ART2| exact INB2| clear - BF0; lia| clear - RM1 LSRC; lia| exact WR2]
| |- _ \/ _ => exact DISJ
| |- _ => idtac
end .. | ].
1: (clear - B20 B21 RM1 BF0 N0 LOR SPT; lia).
1: (clear - SR1 SR2 S0 S1 N0 LOR SPT; lia).
intros kc3 Hc3. unfold icpt_postF in Hc3.
cps_unpack Hc3 as (m3 & RS3 & (ART3 & MI3 & WM3 & ST3) & PRES3 & BY3).
pose proof (ogg_bytes_piece m2 m3 _ bsrc WR2 WM3 BY3) as P2'. clear BY3 P2.
assert (LP1 : Z.of_nat (length (firstn (Z.to_nat (os_body_fill os3)) bb2)) = os_body_fill os3) by (rewrite firstn_length_le by lia; lia).
assert (LP3 : Z.of_nat (length (skipn (Z.to_nat (os_body_fill os3) + length bsrc) bb2)) = Z.of_nat (length bb2) - os_body_fill os3 - Z.of_nat (length bsrc))
by (rewrite length_skipn; lia).
pose proof (live_apart2 Σ2 m3 Bd2 _ L _ ART3 INB2 INL2 ltac:(congruence)) as SEP_B2L.
pose proof (live_apart2 Σ2 m3 Bd2 _ Gv _ ART3 INB2 ING2 ltac:(congruence)) as SEP_B2G.
assert (DR : 0 <= os_body_fill os3 /\ os_body_fill os3 + Z.of_nat (length bsrc) <= os_body_storage (body_expand_res os3 n)) by (clear - BF0 RM1 LSRC; lia).
assert (HR : Dsy <= Dsy + pg_hdr og /\ Dsy + pg_hdr og + Z.of_nat (length hs) + Z.of_nat (length bs) <= Dsy + nsy) by (clear - PH1 PH2 HLEN BSLEN; lia).
cps_hide.
txe P1 ltac:(cls_live INB2) ltac:(fun x Hx => clear - Hx LP1; lia).
txe P3 ltac:(cls_live INB2) ltac:(fun x Hx => clear - Hx; lia).
txe OS2 ltac:(cls_frame INF2) ltac:(fun x Hx => clear - Hx SEP_AB2 DR; unfold hid in *; lia).
txe LAC ltac:(cls_live INL2) ltac:(fun x Hx => clear - Hx SEP_B2L DR; unfold hid in *; lia).
txe GRA ltac:(cls_live ING2) ltac:(fun x Hx => clear - Hx SEP_B2G DR; unfold hid in *; lia).
txe FR ltac:(cls_stack) ltac:(fun x Hx => clear - Hx B21 DR LOR; lia).
txe OG ltac:(cls_frame INF2) ltac:(fun x Hx => clear - Hx SEP_GB2 DR; unfold hid in *; lia).
txe HS ltac:(cls_live INSY2) ltac:(fun x Hx => clear - Hx SEP_SB2 DR HR; unfold hid in *; lia).
txe BS ltac:(cls_live INSY2) ltac:(fun x Hx => clear - Hx SEP_SB2 DR HR HLEN BSLEN; unfold hid in *; lia).
clear SRC.
lazymatch goal with H : ASTA _ _ _ (eq _) _ |- _ => rewrite LSRC in H end.

cps_seg (pgi_x3 A Bd2 (os_body_fill os3) (os_body_returned (body_expand_res os3 n)) L Gv (os_lacing_fill (body_expand_res os3 n))
(os_lacing_packet (body_expand_res os3 n)) (os_lacing_returned (body_expand_res os3 n)) n shdr (body_expand_res os3 n)).
1: (clear - FA2 BF1 LOR SPT FSZ; lia).
destruct POST as (m4 & a0' & -> & MU4 & WM4 & MI4 & OS4).
clear OS2. unfold page_cells in OG. unfold pgi_frame in FR. cps_seg_post.

assert (BODY4 : u8arr asegs m4 Bd2 (firstn (Z.to_nat (os_body_fill os3)) bb2 ++ bsrc ++ skipn (Z.to_nat (os_body_fill os3) + length bsrc) bb2)).
{ apply u8arr_app. split; [apply u8arr_rw_CB; exact P1|]. rewrite LP1.
apply u8arr_app. split; [apply u8arr_rw_CB; exact P2'| apply u8arr_rw_CB; exact P3]. }
clear P1 P2' P3.
eapply (Hk _ Σ2 Bd2 m4 (firstn (Z.to_nat (os_body_fill os3)) bb2 ++ bsrc ++ skipn (Z.to_nat (os_body_fill os3) + length bsrc) bb2)); try eassumption.
- rewrite stream_cells_pagein_body, EX2. exact OS4.
- apply u8arr_rw_CB. exact BODY4.
- rewrite !length_app, firstn_length_le, length_skipn by lia. clear - BLEN2 LB2. lia.
- apply (body_pre_copy (os_body os3) (zslice skipped n body) bodybytes bb2 bsrc (Z.to_nat (os_body_fill os3)) BPRE); [| exact BPFX2| exact ZSRC| exact LB2].
unfold zlength in BFILL. lia.
Qed.

Lemma lacing_expand_res_fields : forall (os : stream_st bptr) n, 0 <= n -> os_lacing_fill os <= os_lacing_storage os ->
os_body (lacing_expand_res os n) = os_body os /\ os_body_fill (lacing_expand_res os n) = os_body_fill os /\
os_body_returned (lacing_expand_res os n) = os_body_returned os /\ os_body_storage (lacing_expand_res os n) = os_body_storage os /\
os_body_data (lacing_expand_res os n) = os_body_data os /\
os_lacing_fill (lacing_expand_res os n) = os_lacing_fill os /\ os_lacing_packet (lacing_expand_res os n) = os_lacing_packet os /\
os_lacing_returned (lacing_expand_res os n) = os_lacing_returned os /\ os_lacing (lacing_expand_res os n) = os_lacing os /\
os_pageno (lacing_expand_res os n) = os_pageno os /\
os_lacing_storage os <= os_lacing_storage (lacing_expand_res os n) /\ os_lacing_fill os + n <= os_lacing_storage (lacing_expand_res os n).
Proof.
intros os n N0 FS. unfold lacing_expand_res. destruct (Z.ltb_spec (os_lacing_fill os) (os_lacing_storage os - n)); cbn; repeat split; try reflexivity; try lia.
Qed.

Lemma pgi_phaseL : forall (Σ : rts RT) PMc (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(x5 x6 x7 x9 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 : word) F fc (m0 m : mem)
(LV : list (Z * Z)) (A G Dsy nsy Bd L Gv f lo : Z) (k : nat) (og : page) (os1 : stream_st bptr)
(shdr hs bs bodybytes j0 : list byte) (lws gws : list word),
fdfs_only PMc -> mat_stable PMc ->
rw_cells asegs m A (stream_cells Bd L Gv shdr os1) -> length shdr = 284%nat -> 0 < A ->
rw_cells asegs m Bd [CB (length bodybytes) bodybytes] -> Z.of_nat (length bodybytes) = os_body_storage os1 ->
u32arr asegs m L lws -> wpre (os_lacing os1) lws -> Z.of_nat (length lws) = os_lacing_storage os1 ->
u64arr asegs m Gv gws -> Z.of_nat (length gws) = os_lacing_storage os1 ->
rw_cells asegs m (bv_unsigned sp + -144) (pgi_frame ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j0 hs) ->
rw_cells asegs m G (page_cells Dsy og) ->
bytes_at asegs m (Dsy + pg_hdr og) hs -> bytes_at asegs m (Dsy + pg_hdr og + pg_header_len og) bs ->
stream_fields_ok os1 -> stream_inv os1 -> os_lacing_returned os1 = 0 -> body_inv os1 -> lacing_vals_ok (os_lacing os1) -> body_pre (os_body os1) bodybytes ->
length hs = (27 + Z.to_nat (znth (ubytes hs) 26))%nat -> Z.of_nat (length hs) = pg_header_len og -> Z.of_nat (length bs) = pg_body_len og ->
zsum (lacing_of (ubytes hs)) <= pg_body_len og -> 0 <= pg_hdr og -> pg_hdr og + pg_header_len og + pg_body_len og <= nsy ->
8 * (os_lacing_storage os1 + znth (ubytes hs) 26 + 33) <= 64512 -> 0 < os_lacing_storage os1 -> 0 < os_body_storage os1 ->
In (Bd, os_body_storage os1) (rt_live RT Σ) -> In (L, 4 * os_lacing_storage os1) (rt_live RT Σ) -> In (Gv, 8 * os_lacing_storage os1) (rt_live RT Σ) ->
In (Dsy, nsy) (rt_live RT Σ) -> Bd <> L -> Bd <> Gv -> L <> Gv -> Dsy <> Bd -> Dsy <> L -> Dsy <> Gv ->
In (f, k) (rt_frames RT Σ) -> f <= A -> A + 408 <= f + fs_size k - 8 -> f <= G -> G + 32 <= f + fs_size k - 8 -> (A + 408 <= G \/ G + 32 <= A) ->
(forall e, In e LV -> In e (rt_live RT Σ) /\ fst e <> Bd /\ fst e <> L /\ fst e <> Gv) ->
Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX -> 0 <= rt_credit RT Σ ->
ART RT Σ m -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp + -144) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK + 256 <= bv_unsigned sp -> bv_unsigned sp + 16 <= USTACK_TOP ->
bv_unsigned sp mod 16 = 0 ->
rt_pres_fp LV (rt_frames RT Σ) (bv_unsigned sp) [(A, A + 408)] m0 m ->
forall T c,
ASTA RT Σ PMc (eq (MS (pgi_regs (Z_to_bv 64 RA_pgi_lexp) (bv_unsigned sp) gp (Z_to_bv 64 0x630458) x5 x6 x7 A x9 (Z_to_bv 64 A) (Z_to_bv 64 (znth (ubytes hs) 26 + 1))
x12 x13 x14 x15 x16 x17 (pg_body_len og) (Dsy + pg_hdr og + pg_header_len og) (Dsy + pg_hdr og) x22 hs
(Z_to_bv 64 (ogg_page_serialno (ubytes hs))) x28 x29 x30 x31)
F (Z_to_bv 64 A_os_lacing_expand) fc None m (seg_rom asegs))) c ->
(forall c' (Σ1 : rts RT) (L1 G1 : Z) (m' : mem) (lws' gws' : list word) (bos' segptr skipped : Z)
(y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
let os3 := pagein_unroll (lacing_expand_res os1 (znth (ubytes hs) 26 + 1)) (ogg_page_pageno (ubytes hs)) in
ASTA RT Σ1 PMc (eq (MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp (Z_to_bv 64 0x630458) y5 y6 y7 (Z_to_bv 64 A) (Z_to_bv 64 (znth (ubytes hs) 5))
y10 y11 y12 y13 y14 y15 y16 y17
(Z_to_bv 64 (-1)) (Z_to_bv 64 (pg_body_len og - skipped)) (Z_to_bv 64 (Dsy + pg_hdr og + pg_header_len og + skipped))
(Z_to_bv 64 (Dsy + pg_hdr og)) x22 (Z_to_bv 64 segptr) (Z_to_bv 64 (ogg_page_pageno (ubytes hs))) (Z_to_bv 64 bos')
(Z_to_bv 64 (znth (ubytes hs) 26)) (Z_to_bv 64 (znth (ubytes hs) 20 * 65536)) y28 y29 y30 y31)
F (Z_to_bv 64 (if pg_body_len og - skipped =? 0 then 0xb95b0 else 0xb957c)) fc None m' (seg_rom asegs))) c' ->
pagein_skip os3 (ubytes hs) = (bos', segptr, skipped) -> 0 <= skipped <= zsum (lacing_of (ubytes hs)) -> 0 <= segptr <= znth (ubytes hs) 26 ->
(bos' = 0 \/ bos' = Z.land (znth (ubytes hs) 5) 2) ->
ART RT Σ1 m' -> mem_inv asegs m' -> stk asegs m' lo (bv_unsigned sp + -144) ->
rw_cells asegs m' (bv_unsigned sp + -144) (pgi_frame ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j0 hs) ->
rw_cells asegs m' A (stream_cells Bd L1 G1 shdr os3) ->
rw_cells asegs m' Bd [CB (length bodybytes) bodybytes] ->
u32arr asegs m' L1 lws' -> wpre (os_lacing os3) lws' -> Z.of_nat (length lws') = os_lacing_storage os3 ->
u64arr asegs m' G1 gws' -> Z.of_nat (length gws') = os_lacing_storage os3 ->
rw_cells asegs m' G (page_cells Dsy og) ->
bytes_at asegs m' (Dsy + pg_hdr og) hs -> bytes_at asegs m' (Dsy + pg_hdr og + pg_header_len og) bs ->
rt_pres_fp LV (rt_frames RT Σ) (bv_unsigned sp) [(A, A + 408)] m0 m' ->
stream_fields_ok os3 -> stream_inv os3 -> os_lacing_returned os3 = 0 -> body_inv os3 -> lacing_vals_ok (os_lacing os3) ->
os_lacing_fill os3 + znth (ubytes hs) 26 + 1 <= os_lacing_storage os3 -> os_body_storage os3 = os_body_storage os1 ->
os_lacing_storage os1 <= os_lacing_storage os3 -> 8 * os_lacing_storage os3 <= 64512 -> body_pre (os_body os3) bodybytes ->
In (L1, 4 * os_lacing_storage os3) (rt_live RT Σ1) -> In (G1, 8 * os_lacing_storage os3) (rt_live RT Σ1) -> L1 <> G1 ->
In (Bd, os_body_storage os1) (rt_live RT Σ1) -> In (Dsy, nsy) (rt_live RT Σ1) -> Bd <> L1 -> Bd <> G1 -> Dsy <> L1 -> Dsy <> G1 ->
(forall e, In e LV -> In e (rt_live RT Σ1)) -> (length (rt_live RT Σ1) <= length (rt_live RT Σ))%nat ->
(forall a, aclient LV (rt_frames RT Σ) (bv_unsigned sp) a -> ~ (L1 <= a < L1 + 4 * os_lacing_storage os3)) ->
(forall a, aclient LV (rt_frames RT Σ) (bv_unsigned sp) a -> ~ (G1 <= a < G1 + 8 * os_lacing_storage os3)) ->
((os_lacing_fill os1 < os_lacing_storage os1 - (znth (ubytes hs) 26 + 1) /\ L1 = L /\ G1 = Gv /\ rt_live RT Σ1 = rt_live RT Σ)
\/ (os_lacing_storage os1 - (znth (ubytes hs) 26 + 1) <= os_lacing_fill os1
/\ rt_live RT Σ1 = (G1, 8 * (os_lacing_storage os1 + (znth (ubytes hs) 26 + 1) + 32)) :: (L1, 4 * (os_lacing_storage os1 + (znth (ubytes hs) 26 + 1) + 32))
:: live_remove Gv (live_remove L (rt_live RT Σ)))) ->
rt_frames RT Σ1 = rt_frames RT Σ -> rt_sp0 RT Σ1 = rt_sp0 RT Σ -> rt_credit RT Σ1 = rt_credit RT Σ -> rt_pois RT Σ1 = rt_pois RT Σ ->
realizes asegs c' T) ->
realizes asegs c T.
Proof using AF LEXP.
intros Σ PMc ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x5 x6 x7 x9 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 F fc m0 m
LV A G Dsy nsy Bd L Gv f lo k og os1 shdr hs bs bodybytes j0 lws gws
FDO MST OS HL A0 BODY BLEN LAC LPRE LLEN GRA GLEN FR OG HS BS FOK SINV LR0 BINV LOK BPRE LENH HLEN BSLEN HSUM PG0 PGIN LSB LS0 BS0
INB INL ING INSY NBL NBG NLG NSB NSL NSG INF FA1 FA2 FG1 FG2 SEP_AG SUBLV LVM CR0 ART0 MI0 ST0 LOW LOR SPT SPA PF T c Hc Hk.
set (usp := bv_unsigned sp) in *.
destruct (frame_below_lo RT AF Σ m f k lo ART0 INF LOW) as (BF1 & BF2 & BF3).
assert (FSZ : 0 <= fs_size k) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
destruct (live_below_lo RT AF Σ m Bd _ lo ART0 INB LOW) as (B0 & B1 & _).
destruct (live_below_lo RT AF Σ m L _ lo ART0 INL LOW) as (L0 & L1' & _).
destruct (live_below_lo RT AF Σ m Gv _ lo ART0 ING LOW) as (G0' & G1' & _).
destruct (live_below_lo RT AF Σ m Dsy _ lo ART0 INSY LOW) as (S0 & S1 & _).
pose proof (byte_range (nth (Z.to_nat 26) hs (Z_to_bv 8 0))) as H26. rewrite <- (znth_ubytes hs 26) in H26 by lia.
pose proof FOK as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12). unfold int31 in *.
pose proof SINV as (I1 & I2 & I3 & I4 & I5). unfold zlength in I3, I4.
pose proof (wpre_length _ _ LPRE) as LL.
assert (LFS : os_lacing_fill os1 <= os_lacing_storage os1) by lia.
assert (NSY : 0 < nsy) by lia.
assert (LOU : rt_sp0 RT Σ - STACK_WIN <= usp) by (clear - LOW LOR; unfold RT_STACK in *; lia).
assert (SPL : forall a, aclient LV (rt_frames RT Σ) usp a -> usp <= a \/ a < rt_sp0 RT Σ - STACK_WIN).
{ intros a Ha. apply (aclient_split RT AF Σ m usp a ART0). apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros e He; exact (proj1 (SUBLV e He))| auto| apply Z.le_refl]. }
assert (EU : bv_unsigned (Z_to_bv 64 (usp + -144)) = usp + -144) by (apply unsigned_lit; clear - LOR SPT BF3; unfold RT_STACK, USTACK_TOP, SH_HI in *; lia).
assert (SUBLVLG : forall e, In e LV -> In e (live_remove Gv (live_remove L (rt_live RT Σ)))).
{ intros e He. destruct (SUBLV e He) as (X1 & X2 & X3 & X4). apply live_remove_keep; [apply live_remove_keep|]; assumption. }
assert (INBLG : In (Bd, os_body_storage os1) (live_remove Gv (live_remove L (rt_live RT Σ)))) by (apply live_remove_keep; [apply live_remove_keep|]; cbn [fst]; assumption).
assert (INSYLG : In (Dsy, nsy) (live_remove Gv (live_remove L (rt_live RT Σ)))) by (apply live_remove_keep; [apply live_remove_keep|]; cbn [fst]; assumption).
assert (INGL : In (Gv, 8 * os_lacing_storage os1) (live_remove L (rt_live RT Σ))) by (apply live_remove_keep; [exact ING| cbn [fst]; congruence]).
destruct (frame_live_apart RT AF Σ m f k Bd _ ART0 INF INB) as (FLB & _).
destruct (frame_live_apart RT AF Σ m f k Dsy _ ART0 INF INSY) as (FLS & _).
assert (SEP_AB : Bd + os_body_storage os1 <= A \/ A + 408 <= Bd) by (clear - FLB FA1 FA2; lia).
assert (SEP_AS : Dsy + nsy <= A \/ A + 408 <= Dsy) by (clear - FLS FA1 FA2; lia).
assert (SEP_GB : Bd + os_body_storage os1 <= G \/ G + 32 <= Bd) by (clear - FLB FG1 FG2; lia).
assert (SEP_GS : Dsy + nsy <= G \/ G + 32 <= Dsy) by (clear - FLS FG1 FG2; lia).
assert (AT : A + 408 < 2^63) by (clear - FA2 BF1 LOR SPT FSZ; unfold RT_STACK, USTACK_TOP in *; lia).
clear FLB FLS.
cps_norm. cps_hide.
unfold pgi_regs in Hc.
kp_all. unfold kp in OS.
cps_norm.
cps_rt (LEXP Σ PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m A Bd L Gv (znth (ubytes hs) 26 + 1) f lo k os1 shdr lws gws).
all: [> lazymatch goal with
| |- stk _ _ _ _ => rewrite EU; exact ST0
| |- _ mod 16 = 0 => rewrite EU; clear - SPA; Z.div_mod_to_equations; lia
| |- _ => first [ rewrite EU; ulc | ulc ]
end .. | ].
clear OS LAC GRA.
assert (HR : Dsy <= Dsy + pg_hdr og /\ Dsy + pg_hdr og + Z.of_nat (length hs) + Z.of_nat (length bs) <= Dsy + nsy) by (clear - PG0 PGIN HLEN BSLEN; lia).
intros kc2 (Σ1 & L1 & G1 & Hc2 & INL1 & ING1 & NLG1 & CASE & EF1 & ES1 & EC1 & EP1).
ogg_unpackL Hc2 as (m2 & lws2 & gws2 & RS2 & (ART2 & MI2 & ST2) & PRES2 & OS2 & LAC2 & LLEN2 & LPFX2 & GRA2 & GLEN2 & GPFX2). destruct RS2 as (-> & ->).
txe BODY ltac:(cls_live INBLG) ltac:(fun x Hx => clear - Hx SEP_AB BLEN; unfold hid in *; lia).
txe FR ltac:(cls_stack) ltac:(fun x Hx => clear - Hx BF1 FA2 FSZ LOR; lia).
txe OG ltac:(cls_frame INF) ltac:(fun x Hx => clear - Hx SEP_AG; unfold hid in *; lia).
txe HS ltac:(cls_live INSYLG) ltac:(fun x Hx => clear - Hx SEP_AS HR; unfold hid in *; lia).
txe BS ltac:(cls_live INSYLG) ltac:(fun x Hx => clear - Hx SEP_AS HR HLEN; unfold hid in *; lia).

pose proof (lacing_expand_res_fields os1 (znth (ubytes hs) 26 + 1) ltac:(lia) LFS) as (E2b & E2bf & E2br & E2bs & E2bd & E2lf & E2lp & E2lr & E2l & E2pn & E2ls & E2ls').
assert (LS2 : 8 * os_lacing_storage (lacing_expand_res os1 (znth (ubytes hs) 26 + 1)) <= 64512).
{ unfold lacing_expand_res. destruct (_ <? _); cbn [set_blocks os_lacing_storage]; lia. }
assert (X1 : In (Bd, os_body_storage os1) (rt_live RT Σ1) /\ In (Dsy, nsy) (rt_live RT Σ1) /\ Bd <> L1 /\ Bd <> G1 /\ Dsy <> L1 /\ Dsy <> G1
/\ (forall e, In e LV -> In e (rt_live RT Σ1)) /\ (length (rt_live RT Σ1) <= length (rt_live RT Σ))%nat
/\ (forall a, aclient LV (rt_frames RT Σ) usp a -> ~ (L1 <= a < L1 + 4 * os_lacing_storage (lacing_expand_res os1 (znth (ubytes hs) 26 + 1))))
/\ (forall a, aclient LV (rt_frames RT Σ) usp a -> ~ (G1 <= a < G1 + 8 * os_lacing_storage (lacing_expand_res os1 (znth (ubytes hs) 26 + 1))))).
{ destruct CASE as [(FITS & -> & -> & E)|(GROW & E)].
- assert (ES : os_lacing_storage (lacing_expand_res os1 (znth (ubytes hs) 26 + 1)) = os_lacing_storage os1)
by (unfold lacing_expand_res; replace (os_lacing_fill os1 <? _) with true by (symmetry; apply Z.ltb_lt; exact FITS); reflexivity).
rewrite ES in INL1, ING1 |- *. rewrite E.
split; [exact INB|]. split; [exact INSY|]. split; [exact NBL|]. split; [exact NBG|]. split; [exact NSL|]. split; [exact NSG|].
split; [intros e He; exact (proj1 (SUBLV e He))|]. split; [lia|].
split.
+ intros a Ha. apply (live_apart_LV Σ Σ1 m2 L _ LV usp a ART2 INL1); [| exact EF1| exact ES1| exact LOU| exact Ha].
intros e He. rewrite E. destruct (SUBLV e He) as (X1 & X2 & X3 & X4). split; assumption.
+ intros a Ha. apply (live_apart_LV Σ Σ1 m2 Gv _ LV usp a ART2 ING1); [| exact EF1| exact ES1| exact LOU| exact Ha].
intros e He. rewrite E. destruct (SUBLV e He) as (X1 & X2 & X3 & X4). split; assumption.
- assert (ES : os_lacing_storage (lacing_expand_res os1 (znth (ubytes hs) 26 + 1)) = os_lacing_storage os1 + (znth (ubytes hs) 26 + 1) + 32)
by (unfold lacing_expand_res; replace (os_lacing_fill os1 <? _) with false by (symmetry; apply Z.ltb_ge; exact GROW); reflexivity).
rewrite ES in INL1, ING1 |- *.
pose proof (live_second_apart Σ1 m2 _ _ _ _ _ Bd _ ART2 E INBLG) as SBL.
pose proof (live_head_apart Σ1 m2 _ _ _ Bd _ ART2 E (or_intror INBLG)) as SBG.
pose proof (live_second_apart Σ1 m2 _ _ _ _ _ Dsy _ ART2 E INSYLG) as SSL.
pose proof (live_head_apart Σ1 m2 _ _ _ Dsy _ ART2 E (or_intror INSYLG)) as SSG.
rewrite E.
split; [right; right; exact INBLG|]. split; [right; right; exact INSYLG|].
split; [clear - SBL BS0 LS0 H26; lia|]. split; [clear - SBG BS0 LS0 H26; lia|].
split; [clear - SSL NSY LS0 H26; lia|]. split; [clear - SSG NSY LS0 H26; lia|].
split; [intros e He; right; right; exact (SUBLVLG e He)|].
split; [cbn [length]; pose proof (live_remove_length_lt L _ _ INL) as X1; pose proof (live_remove_length_lt Gv _ _ INGL) as X2; lia|].
split.
+ intros a Ha. apply (chunk_apart_aclient Σ Σ1 m2 L1 _ [(G1, 8 * (os_lacing_storage os1 + (znth (ubytes hs) 26 + 1) + 32))]
(live_remove Gv (live_remove L (rt_live RT Σ))) LV usp a ART2);
[exact E| intros e He; right; exact (SUBLVLG e He)| exact EF1| exact ES1| exact LOU| exact Ha].
+ intros a Ha. apply (chunk_apart_aclient Σ Σ1 m2 G1 _ [] ((L1, 4 * (os_lacing_storage os1 + (znth (ubytes hs) 26 + 1) + 32))
:: live_remove Gv (live_remove L (rt_live RT Σ))) LV usp a ART2);
[exact E| intros e He; right; exact (SUBLVLG e He)| exact EF1| exact ES1| exact LOU| exact Ha]. }
destruct X1 as (INB1 & INSY1 & NBL1 & NBG1 & NSL1 & NSG1 & SUB1 & LVM1 & NAL1 & NAG1).

assert (FOK2 : stream_fields_ok (lacing_expand_res os1 (znth (ubytes hs) 26 + 1))).
{ unfold lacing_expand_res. destruct (_ <? _); [exact FOK|]. apply fields_ok_set_blocks; [exact FOK| lia| unfold int31; lia]. }
assert (SINV2 : stream_inv (lacing_expand_res os1 (znth (ubytes hs) 26 + 1))).
{ unfold lacing_expand_res. destruct (_ <? _); [exact SINV|]. apply set_blocks_inv; exact SINV. }
assert (BINV2 : body_inv (lacing_expand_res os1 (znth (ubytes hs) 26 + 1))).
{ unfold lacing_expand_res. destruct (_ <? _); [exact BINV|]. apply set_blocks_body_inv; exact BINV. }
assert (LOK2 : lacing_vals_ok (os_lacing (lacing_expand_res os1 (znth (ubytes hs) 26 + 1)))) by (rewrite E2l; exact LOK).
assert (LFILL2 : zlength (os_lacing (lacing_expand_res os1 (znth (ubytes hs) 26 + 1))) = os_lacing_fill (lacing_expand_res os1 (znth (ubytes hs) 26 + 1)))
by (rewrite E2l, E2lf; unfold zlength; lia).
assert (LPK2 : 0 <= os_lacing_packet (lacing_expand_res os1 (znth (ubytes hs) 26 + 1)) <= os_lacing_fill (lacing_expand_res os1 (znth (ubytes hs) 26 + 1)))
by (rewrite E2lp, E2lf; lia).
assert (Hls2 : os_lacing_fill (lacing_expand_res os1 (znth (ubytes hs) 26 + 1)) + znth (ubytes hs) 26 + 1 <= os_lacing_storage (lacing_expand_res os1 (znth (ubytes hs) 26 + 1)))
by (rewrite E2lf; lia).
pose proof BPRE as (BP1 & BP2). pose proof BINV as (J1 & J2 & J3 & J4). unfold zlength in J1.
assert (Hbf2 : -2^62 <= os_body_fill (lacing_expand_res os1 (znth (ubytes hs) 26 + 1)) < 2^62) by (rewrite E2bf; lia).

cps_seg pgi_e1.
lazymatch type of POST with ?x = _ => subst x end.
clear Hc.

assert (LOW1 : rt_sp0 RT Σ1 - STACK_WIN <= lo) by (rewrite ES1; exact LOW).
assert (INF1 : In (f, k) (rt_frames RT Σ1)) by (rewrite EF1; exact INF).
destruct (live_below_lo RT AF Σ1 m2 L1 _ lo ART2 INL1 LOW1) as (L10 & L11 & _).
destruct (live_below_lo RT AF Σ1 m2 G1 _ lo ART2 ING1 LOW1) as (G10 & G11 & _).
destruct (frame_live_apart RT AF Σ1 m2 f k L1 _ ART2 INF1 INL1) as (FLL1 & _).
destruct (frame_live_apart RT AF Σ1 m2 f k G1 _ ART2 INF1 ING1) as (FLG1 & _).
set (ls2 := os_lacing_storage (lacing_expand_res os1 (znth (ubytes hs) 26 + 1))) in *.
assert (SEP_AL1 : L1 + 4 * ls2 <= A \/ A + 408 <= L1) by (clear - FLL1 FA1 FA2; lia).
assert (SEP_AGv1 : G1 + 8 * ls2 <= A \/ A + 408 <= G1) by (clear - FLG1 FA1 FA2; lia).
assert (SEP_GL1 : L1 + 4 * ls2 <= G \/ G + 32 <= L1) by (clear - FLL1 FG1 FG2; lia).
assert (SEP_GG1 : G1 + 8 * ls2 <= G \/ G + 32 <= G1) by (clear - FLG1 FG1 FG2; lia).
clear FLL1 FLG1.
pose proof (live_apart2 Σ1 m2 L1 _ G1 _ ART2 INL1 ING1 ltac:(congruence)) as SEP_LG1.
pose proof (live_apart2 Σ1 m2 Dsy _ L1 _ ART2 INSY1 INL1 ltac:(congruence)) as SEP_SL1.
pose proof (live_apart2 Σ1 m2 Dsy _ G1 _ ART2 INSY1 ING1 ltac:(congruence)) as SEP_SG1.
pose proof (live_apart2 Σ1 m2 Bd _ L1 _ ART2 INB1 INL1 ltac:(congruence)) as SEP_BL1.
pose proof (live_apart2 Σ1 m2 Bd _ G1 _ ART2 INB1 ING1 ltac:(congruence)) as SEP_BG1.
assert (SEP_LG1' : L1 + 4 * ls2 <= G1 \/ G1 + 8 * ls2 <= L1) by (clear - SEP_LG1; lia).
assert (SEP_HL1 : Dsy + pg_hdr og + Z.of_nat (length hs) <= L1 \/ L1 + 4 * ls2 <= Dsy + pg_hdr og) by (clear - SEP_SL1 HR; lia).
assert (SEP_HG1 : Dsy + pg_hdr og + Z.of_nat (length hs) <= G1 \/ G1 + 8 * ls2 <= Dsy + pg_hdr og) by (clear - SEP_SG1 HR; lia).
assert (SEP_AH : Dsy + pg_hdr og + Z.of_nat (length hs) <= A \/ A + 408 <= Dsy + pg_hdr og) by (clear - SEP_AS HR; unfold hid in *; lia).
assert (TOPL1 : L1 + 4 * ls2 < 2^63) by (clear - L11 LOR SPT; lia).
assert (TOPG1 : G1 + 8 * ls2 < 2^63) by (clear - G11 LOR SPT; lia).
assert (TOPH : Dsy + pg_hdr og + Z.of_nat (length hs) < 2^63) by (clear - HR S1 LOR SPT; lia).
assert (HH : 0 <= Dsy + pg_hdr og) by (clear - HR S0; lia).
assert (LOSP : lo + 144 <= bv_unsigned sp) by (clear - LOR; lia).
assert (ALO : A + 408 <= lo) by (clear - FA2 BF1; lia).
assert (HLO : Dsy + pg_hdr og + Z.of_nat (length hs) <= lo) by (clear - HR S1; lia).
assert (LPRE2 : wpre (os_lacing (lacing_expand_res os1 (znth (ubytes hs) 26 + 1))) lws2) by (rewrite E2l; exact (wpre_firstn_ext _ _ _ LPRE LPFX2)).
cps_hide.
unfold pgi_frame in FR.
cps_seg (X0a2.pi_unroll A Bd L1 G1 (Dsy + pg_hdr og) lo shdr hs (lacing_expand_res os1 (znth (ubytes hs) 26 + 1)) lws2 gws2
ra sp gp (Z_to_bv 64 0x630458) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 RA_pgi_lexp) j0
LENH H26 HL FOK2 Hls2 LFILL2 LPK2 LOK2 A0 L10 G10 HH TOPL1 TOPG1 TOPH LOSP ALO SEP_AL1 SEP_AGv1 SEP_AH L11 G11 HLO SEP_LG1' SEP_HL1 SEP_HG1).
unfold X0a2.unroll_post in POST.
destruct POST as (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & m3 & lws3 & -> & MU3 & WM3 & MI3 & OS3 & LAC3 & LPRE3 & LLEN3 & GRA3 & FR3 & HS3).
clear OS2 LAC2 GRA2 FR HS.

assert (ART3 : ART RT Σ1 m3).
{ apply (af_frame RT AF Σ1 m2 m3 lo ART2 LOW1); [| exact WM3].
intros a Ha. apply MU3. cbn [outside]. repeat split; intros Hin; apply Ha; change (bv_unsigned sp) with usp in Hin.
- left. unfold USTACK_TOP. clear - Hin LOR SPT. lia.
- right; right; right; left. exists f, k. split; [exact INF1| clear - Hin FA1 FA2; lia].
- right; right; left. exists L1, (4 * ls2). split; [exact INL1| clear - Hin; lia].
- right; right; left. exists G1, (8 * ls2). split; [exact ING1| clear - Hin; lia]. }
assert (PF3 : rt_pres_fp LV (rt_frames RT Σ) usp [(A, A + 408)] m0 m3).
{ apply (pres_fp_trans _ _ _ _ m0 m2 m3 PF). apply (pres_fp_of_munch _ _ _ _ _ m2 m3 MU3).
intros x Hx Ho. cbn [outside] in Ho |- *. destruct Ho as (Ho & _). change (bv_unsigned sp) with usp.
pose proof (SPL x Hx) as Sx. pose proof (NAL1 x Hx) as Lx. pose proof (NAG1 x Hx) as Gx.
split; [clear - Sx LOW LOR; lia|]. split; [exact Ho|]. split; [exact Lx|]. split; [exact Gx| exact I]. }
clear PF ART2 MI2. rename PF3 into PF.
pose proof (rw_cells_transport asegs _ m2 m3 Bd _ BODY MU3 WM3) as BODY3.
pose proof (rw_cells_transport asegs _ m2 m3 G _ OG MU3 WM3) as OG3.
pose proof (bytes_at_transport asegs _ m2 m3 _ bs BS MU3) as BS3.
unfold page_cells in OG3.
cbn [disjoint_from cells_size csize Nat.add] in BODY3, OG3, BS3.
specialize (BODY3 ltac:(repeat split; [clear - B1 BLEN LOR; lia| clear - SEP_AB BLEN; unfold hid in *; lia| clear - SEP_BL1 BLEN; unfold hid in *; lia| clear - SEP_BG1 BLEN; unfold hid in *; lia])).
specialize (OG3 ltac:(repeat split; [clear - FG2 BF1 LOR; lia| clear - SEP_AG; unfold hid in *; lia| clear - SEP_GL1; unfold hid in *; lia| clear - SEP_GG1; unfold hid in *; lia])).
specialize (BS3 ltac:(repeat split; [clear - HR S1 LOR HLEN; lia| clear - SEP_AS HR HLEN; unfold hid in *; lia| clear - SEP_SL1 HR HLEN; unfold hid in *; lia| clear - SEP_SG1 HR HLEN; unfold hid in *; lia])).
clear BODY OG BS.
set (os2 := lacing_expand_res os1 (znth (ubytes hs) 26 + 1)) in *.
assert (LR2 : os_lacing_returned os2 = 0) by (rewrite E2lr; exact LR0).
pose proof (pagein_unroll_inv os2 (ogg_page_pageno (ubytes hs)) SINV2 LR2) as (SINV3 & LR3 & ELV3 & EGV3 & EBD3 & ELS3 & EBS3 & HLF3).
pose proof (pagein_unroll_body_inv os2 (ogg_page_pageno (ubytes hs)) SINV2 LR2 BINV2) as (BINV3 & HBF3 & HBR3).
pose proof (body_inv_fill_nonneg _ BINV3) as HBF3'.
pose proof SINV3 as (K1 & K2 & K3 & K4 & K5). unfold zlength in K3, K4.
assert (FOK3 : stream_fields_ok (pagein_unroll os2 (ogg_page_pageno (ubytes hs)))).
apply fields_ok_unroll; [exact FOK2| exact SINV2| |].
1: (clear - HBF3 HBF3'; lia).
1: (clear - Hls2 LS2 H26; lia).
pose proof (lacing_vals_ok_unroll os2 (ogg_page_pageno (ubytes hs)) LOK2) as LOK3.
set (os3 := pagein_unroll os2 (ogg_page_pageno (ubytes hs))) in *.
assert (LFILL3 : zlength (os_lacing os3) = os_lacing_fill os3) by (clear - K3; unfold zlength; lia).
assert (HBP : 0 <= Dsy + pg_hdr og + pg_header_len og) by (clear - HR HLEN S0; lia).
assert (TOPB : Dsy + pg_hdr og + pg_header_len og + pg_body_len og < 2^63) by (clear - HR HLEN BSLEN S1 LOR SPT; lia).

cps_seg (X0a1.pi_skip A Bd L1 G1 (Dsy + pg_hdr og) (Dsy + pg_hdr og + pg_header_len og) (pg_body_len og) shdr hs os3 lws3 m3 sp gp (Z_to_bv 64 0x630458) F fc
(Z_to_bv 64 RA_pgi_lexp) (ogg_page_pageno (ubytes hs)) y5 y6 y7 y14 y15 y16 y17 (Z_to_bv 64 (-1)) x22 (Z_to_bv 64 (znth (ubytes hs) 20 * 65536)) y28 _ _ _
LENH H26 HL FOK3 LFILL3 LOK3 LPRE3 HBP HSUM TOPB OS3 LAC3 HS3).
revert POST. destruct (pagein_skip os3 (ubytes hs)) as [[bos' segptr] skipped] eqn:ESK. intros POST.
unfold X0a1.skip_exit in POST.
destruct POST as (z10 & z11 & z12 & z13 & -> & Hsk & Hseg & Hbos).
unfold ls2 in *.
assert (Hls2s : os_lacing_fill os2 + (znth (ubytes hs) 26 + 1) < os_lacing_storage os2).
{ unfold os2, lacing_expand_res. destruct (Z.ltb_spec (os_lacing_fill os1) (os_lacing_storage os1 - (znth (ubytes hs) 26 + 1))); cbv iota; unfold set_blocks; cbn [os_lacing_fill os_lacing_storage]; clear - LFS H26 H; lia. }
assert (BPRE3 : body_pre (os_body os3) bodybytes).
{ destruct (unroll_body os2 (ogg_page_pageno (ubytes hs))) as [E|E]; fold os3 in E.
- rewrite E, E2b. exact BPRE.
- rewrite E, E2b. apply body_pre_ztake; [exact BPRE| lia|]. unfold zlength. rewrite <- E2b. clear - HBF3 J1 E2bf E2b. rewrite E2b. lia. }
eapply (Hk _ Σ1 L1 G1 m3 lws3 gws2 bos' segptr skipped); try eassumption; try reflexivity; rewrite ?ELS3, ?EBS3.
all: try eassumption.
- apply (stk_transport asegs _ m2 m3 lo (usp + -144) ST2 MU3 WM3). intros x Hx. left. cbn [outside]. change (bv_unsigned sp) with usp.
repeat split; clear - Hx ALO L11 G11; lia.
- clear - HLF3 Hls2s. lia.
Qed.

Lemma ret_body_fields : forall os : stream_st bptr,
os_lacing (ret_body os) = os_lacing os /\ os_lacing_storage (ret_body os) = os_lacing_storage os /\ os_lacing_fill (ret_body os) = os_lacing_fill os /\
os_lacing_packet (ret_body os) = os_lacing_packet os /\ os_lacing_returned (ret_body os) = os_lacing_returned os /\ os_body_storage (ret_body os) = os_body_storage os.
Proof. intros os. unfold ret_body. destruct (negb (os_body_returned os =? 0)); cbn; repeat split; reflexivity. Qed.
Lemma ret_body_fields_ok : forall os : stream_st bptr, stream_fields_ok os -> 0 <= os_body_returned os <= os_body_fill os -> stream_fields_ok (ret_body os).
Proof.
intros os FOK BR. pose proof FOK as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12).
unfold ret_body. destruct (negb (os_body_returned os =? 0)); [| exact FOK].
unfold stream_fields_ok, set_body. cbn. unfold int31 in *. repeat split; try tauto; lia.
Qed.
Lemma ret_lacing_body : forall os : stream_st bptr, os_body (ret_lacing os) = os_body os /\ os_body_storage (ret_lacing os) = os_body_storage os.
Proof. intros os. unfold ret_lacing. destruct (negb (os_lacing_returned os =? 0)); cbn; split; reflexivity. Qed.

Theorem ogg_stream_pagein_ok : ogg_stream_pagein_cps.
Proof using AF MMOV MCPY LEXP BEXP.
intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m A G Dsy nsy Bd L Gv f lo k og os shdr hs bs bodybytes lws gws q q' r
FDO MST -> -> -> RUN OS HL A0 ARR FOK SINV BINV LOK BDN LVN GVN SLV OG G0 HS BS LENH HLEN BSLEN HSUM PG0 PGIN INSY NSB NSL NSG LSB BSB LS0 BS0
INF FA1 FA2 FG1 FG2 SEP_AG LVM CR0 ART0 MI0 ST0 LOW LOR SPT SPA.
intros T c Hc Hk.
set (usp := bv_unsigned sp) in *.
assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
unfold entry_st in Hc. rewrite ESP in Hc.
set (hdr := ubytes hs) in *.
pose proof (byte_range (nth (Z.to_nat 26) hs (Z_to_bv 8 0))) as H26. rewrite <- (znth_ubytes hs 26) in H26 by lia. fold hdr in H26.
pose proof (byte_range (nth (Z.to_nat 4) hs (Z_to_bv 8 0))) as H4. rewrite <- (znth_ubytes hs 4) in H4 by lia. fold hdr in H4.
assert (HBOK : bytes_ok (lacing_of hdr)) by (apply bytes_ok_zslice; apply ubytes_ok).
pose proof FOK as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12). unfold int31 in F4, F5, F6, F7.

destruct (pagein_prun os hdr (ubytes bs) q r q' RUN BDN LVN GVN HBOK ltac:(rewrite zlength_ubytes, BSLEN; exact HSUM) ltac:(lia) ltac:(unfold bptr in *; lia) ltac:(unfold bptr in *; lia) ltac:(unfold bptr in *; lia)
ltac:(rewrite zlength_ubytes, BSLEN; unfold bptr in *; lia)) as (-> & ->).
subst hdr.
destruct ARR as (BODY & BLEN & BPRE & LAC & LPRE & LLEN & GRA & GLEN).
pose proof SINV as (I1 & I2 & I3 & I4 & I5).
pose proof BINV as (J1 & J2 & J3 & J4). pose proof (body_inv_returned_le_fill os BINV) as BRF.
assert (LOU : rt_sp0 RT Σ - STACK_WIN <= usp) by (clear - LOW LOR; unfold RT_STACK in *; lia).
destruct (frame_below_lo RT AF Σ m f k lo ART0 INF LOW) as (BF1 & BF2 & BF3).
assert (FSZ : 0 <= fs_size k) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
assert (ALO : A + 408 <= lo) by (clear - FA2 BF1 FSZ; lia).
pose proof SLV as (INB & INL & ING & NBL & NBG & NLG).
set (LV := pgi_rest Bd L Gv (rt_live RT Σ)) in *.
assert (NAB : forall a, aclient LV (rt_frames RT Σ) usp a -> ~ (Bd <= a < Bd + os_body_storage os))
by (intros a Ha; exact (rest_apart Σ m Bd L Gv Bd _ usp a ART0 INB (or_introl eq_refl) LOU Ha)).
assert (NAL : forall a, aclient LV (rt_frames RT Σ) usp a -> ~ (L <= a < L + 4 * os_lacing_storage os))
by (intros a Ha; exact (rest_apart Σ m Bd L Gv L _ usp a ART0 INL (or_intror (or_introl eq_refl)) LOU Ha)).
assert (NAG : forall a, aclient LV (rt_frames RT Σ) usp a -> ~ (Gv <= a < Gv + 8 * os_lacing_storage os))
by (intros a Ha; exact (rest_apart Σ m Bd L Gv Gv _ usp a ART0 ING (or_intror (or_intror eq_refl)) LOU Ha)).
assert (SUBLV : forall e, In e LV -> In e (rt_live RT Σ)) by (intros e He; exact (pgi_rest_sub _ _ _ _ _ He)).
assert (SPL : forall a, aclient LV (rt_frames RT Σ) usp a -> usp <= a \/ a < rt_sp0 RT Σ - STACK_WIN).
{ intros a Ha. apply (aclient_split RT AF Σ m usp a ART0). apply (aclient_mono _ _ _ _ _ _ _ Ha); [exact SUBLV| auto| apply Z.le_refl]. }
assert (LBL : Z.of_nat (length (u32s lws)) = 4 * os_lacing_storage os) by (rewrite u32s_length; lia).
assert (LBG : Z.of_nat (length (u64s gws)) = 8 * os_lacing_storage os) by (rewrite u64s_length; lia).
assert (LENH27 : (27 <= length hs)%nat) by lia.

pose proof (u8arr_rw_CB m L (u32s lws)) as XL. pose proof (u8arr_rw_CB m Gv (u64s gws)) as XG.
refine (pgi_phaseA Σ PMc ra gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m A G Dsy nsy Bd L Gv f lo usp k og os shdr hs bs bodybytes lws gws
FDO MST OS HL A0 BODY BLEN BPRE (proj1 XL (u32arr_u8 _ _ _ LAC)) LBL (proj1 XG (u64arr_u8 _ _ _ GRA)) LBG FOK J1 (conj J2 BRF) ltac:(clear - BSB PG0 BSLEN; lia) SLV OG G0 HS BS LENH27 HLEN BSLEN PG0 PGIN INSY NSB
INF FA1 FA2 FG1 FG2 SEP_AG NAB ART0 MI0 ST0 LOW LOR SPT SPA T c Hc _).
clear XL XG.
intros c1 m1 bodybytes1 j0 v25 v22 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 Hc1 ART1 MI1 ST1 FR1 OS1 BODY1 BLEN1 BPRE1 LAC1 GRA1 OG1 HS1 BS1 V25 V22 ESER PF1.

destruct (ret_body_fields os) as (RB1 & RB2 & RB3 & RB4 & RB5 & RB6).
apply u8arr_rw_CB in BODY1. apply u8arr_rw_CB, u8_u32arr in LAC1. apply u8arr_rw_CB, u8_u64arr in GRA1.
rewrite <- RB5 in Hc1.
refine (pgi_phaseB Σ PMc x1 gp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m m1 A G Dsy nsy Bd L Gv f lo usp v25 v22 k og
(ret_body os) shdr hs bs bodybytes1 j0 lws gws FDO MST OS1 HL A0 BODY1 ltac:(rewrite RB6; exact BLEN1) LAC1 ltac:(rewrite RB1; exact LPRE) ltac:(rewrite RB2; exact LLEN)
GRA1 ltac:(rewrite RB2; exact GLEN) (ret_body_fields_ok os FOK (conj J2 BRF)) ltac:(rewrite RB1, RB3; exact I3) ltac:(rewrite RB5, RB4; exact I1) ltac:(rewrite RB4, RB3; exact I2)
ltac:(rewrite RB2; clear - LSB H26; lia) ltac:(unfold stream_live; rewrite RB2, RB6; exact SLV) FR1 OG1 G0 HS1 BS1 LENH27 HLEN BSLEN PG0 PGIN INSY NSL NSG
INF FA1 FA2 FG1 FG2 SEP_AG ltac:(rewrite RB2; exact NAL) ltac:(rewrite RB2; exact NAG) V25 V22 ESER ART1 MI1 ST1 LOW LOR SPT SPA PF1 T c1 Hc1 _).
clear Hc Hc1.
intros c2 m2 lws2 gws2 y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 Hc2 ART2 MI2 ST2 FR2 OS2 BODY2 LAC2 LPRE2 LLEN2 GRA2 GLEN2 OG2 HS2 BS2 PF2.
rewrite <- pagein_returned_eq in OS2, LPRE2. rewrite RB2 in LLEN2, GLEN2.

pose proof (pagein_returned_inv os SINV) as (SINV1 & LR1 & ELV1 & EGV1 & EBD1 & ELS1 & EBS1 & ESN1 & EPN1).
pose proof (pagein_returned_body_inv os SINV BINV) as (BINV1 & BR1 & BFR1 & LF1).
pose proof (fields_ok_returned os FOK SINV BRF) as FOK1.
pose proof (lacing_vals_ok_returned os LOK) as LOK1.
pose proof (ret_lacing_body (ret_body os)) as (RL1 & RL2). rewrite <- pagein_returned_eq in RL1, RL2.
set (os1 := pagein_returned os) in *.

rewrite stream_cells_r_eq in OS2.
cps_seg (pgi_chk A Bd (os_body_fill os1) (os_body_returned os1) L Gv (os_lacing_fill os1) (os_lacing_packet os1) (os_lacing_returned os1) usp lo
(pg_body_len og) (Dsy + pg_hdr og + pg_header_len og) (Dsy + pg_hdr og) shdr hs j0 os1).
destruct POST as (m3 & MU3 & WM3 & MI3 & [(t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & -> & ST3 & FAILC) | (x10' & -> & EM3 & EX10 & ESER' & CVER)]).
-
destruct (live_below_lo RT AF Σ m2 Bd _ lo ART2 INB LOW) as (B0 & B1 & _).
destruct (live_below_lo RT AF Σ m2 L _ lo ART2 INL LOW) as (L0 & L1 & _).
destruct (live_below_lo RT AF Σ m2 Gv _ lo ART2 ING LOW) as (G0' & G1 & _).
destruct (live_below_lo RT AF Σ m2 Dsy _ lo ART2 INSY LOW) as (S0 & S1 & _).
assert (ART3 : ART RT Σ m3).
{ apply (af_frame RT AF Σ m2 m3 lo ART2 LOW); [| exact WM3].
intros a Ha. apply MU3. cbn [outside]. split; [| exact I]. intros Hin. apply Ha. left. clear - Hin LOR SPT; unfold USTACK_TOP, RT_STACK in *; lia. }
assert (PF3 : rt_pres_fp LV (rt_frames RT Σ) usp [(A, A + 408)] m m3).
{ apply (pres_fp_trans _ _ _ _ m m2 m3 PF2). apply (pres_fp_of_munch _ _ _ _ _ m2 m3 MU3).
intros x Hx Ho. cbn [outside] in Ho |- *. pose proof (SPL x Hx) as Sx. split; [clear - Sx LOW LOR; unfold STACK_WIN, RT_STACK in *; lia| exact I]. }
unfold stream_cells_r in OS2.
pose proof (rw_cells_transport asegs _ m2 m3 A _ OS2 MU3 WM3 ltac:(cbn [disjoint_from cells_size csize Nat.add]; split; [left; clear - ALO LOR; unfold RT_STACK in *; lia| exact I])) as OS3.
pose proof (rw_cells_transport asegs _ m2 m3 Bd _ BODY2 MU3 WM3 ltac:(cbn [disjoint_from cells_size csize Nat.add]; split; [left; clear - B1 BLEN1 LOR; unfold RT_STACK in *; lia| exact I])) as BODY3.
pose proof (u32arr_transport asegs _ m2 m3 L _ LAC2 MU3 WM3 ltac:(cbn [disjoint_from]; split; [left; clear - L1 LLEN2 LOR; unfold RT_STACK in *; lia| exact I])) as LAC3.
pose proof (u64arr_transport asegs _ m2 m3 Gv _ GRA2 MU3 WM3 ltac:(cbn [disjoint_from]; split; [left; clear - G1 GLEN2 LOR; unfold RT_STACK in *; lia| exact I])) as GRA3.
unfold page_cells in OG2.
pose proof (rw_cells_transport asegs _ m2 m3 G _ OG2 MU3 WM3 ltac:(cbn [disjoint_from cells_size csize Nat.add]; split; [left; clear - FG2 BF1 LOR; unfold RT_STACK in *; lia| exact I])) as OG3.
clear OS2 BODY2 LAC2 GRA2 OG2 FR2 HS2 BS2.
assert (ERES : pagein_res os (ubytes hs) (ubytes bs) = (-1, os1)).
{ unfold pagein_res. cbv zeta. fold os1. destruct FAILC as [NE|NV].
- replace (ogg_page_serialno (ubytes hs) =? os_serialno os1) with false by (symmetry; apply Z.eqb_neq; exact NE). reflexivity.
- destruct (negb (ogg_page_serialno (ubytes hs) =? os_serialno os1)); [reflexivity|].
unfold ogg_page_version. replace (0 <? znth (ubytes hs) 4) with true by (symmetry; apply Z.ltb_lt; clear - NV H4; lia). reflexivity. }
assert (POK : pgi_ok os (ubytes hs) = false).
{ unfold pgi_ok. fold os1. destruct FAILC as [NE|NV].
- replace (ogg_page_serialno (ubytes hs) =? os_serialno os1) with false by (symmetry; apply Z.eqb_neq; exact NE). reflexivity.
- unfold ogg_page_version. replace (0 <? znth (ubytes hs) 4) with true by (symmetry; apply Z.ltb_lt; clear - NV H4; lia). apply andb_false_r. }
apply Hk. exists Σ, Bd, L, Gv. rewrite ERES. cbn [fst snd].
split; [| split; [reflexivity| split; [reflexivity| split; [| split; [| split; [| repeat split; reflexivity]]]]]].
+ eapply ASTA_conseq; [eassumption|]. intros ms <-. exists m3, bodybytes1, lws2, gws2.
split; [unfold ret_stL; do 16 eexists; split; [rewrite <- ESP; reflexivity| split; reflexivity]|].
split; [split; [exact ART3| split; [exact MI3| exact ST3]]|].
split; [exact PF3|]. split; [exact OS3|].
unfold stream_arrays. split; [apply u8arr_rw_CB; exact BODY3|]. split; [rewrite EBS1; exact BLEN1|]. split; [rewrite RL1; exact BPRE1|].
split; [exact LAC3|]. split; [exact LPRE2|]. split; [rewrite ELS1; exact LLEN2|]. split; [exact GRA3| rewrite ELS1; exact GLEN2].
+ unfold stream_live. rewrite EBS1, ELS1. exact SLV.
+ unfold pagein_live. rewrite POK. reflexivity.
+ unfold pagein_same. rewrite POK. split; [intros _; repeat split; reflexivity|]. split; intros E; discriminate E.
-
subst m3.
assert (SUBLV3 : forall e, In e LV -> In e (rt_live RT Σ) /\ fst e <> Bd /\ fst e <> L /\ fst e <> Gv) by (intros e He; apply pgi_rest_In in He; exact He).
refine (pgi_phaseL Σ PMc ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y5 y6 y7 y9 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 v22) y28 y29 y30 y31 F fc m m2
LV A G Dsy nsy Bd L Gv f lo k og os1 shdr hs bs bodybytes1 j0 lws2 gws2
FDO MST OS2 HL A0 BODY2 ltac:(rewrite EBS1; exact BLEN1) LAC2 LPRE2 ltac:(rewrite ELS1; exact LLEN2) GRA2 ltac:(rewrite ELS1; exact GLEN2)
FR2 OG2 HS2 BS2 FOK1 SINV1 LR1 BINV1 LOK1 ltac:(rewrite RL1; exact BPRE1) LENH HLEN BSLEN HSUM PG0 PGIN
ltac:(rewrite ELS1; exact LSB) ltac:(rewrite ELS1; exact LS0) ltac:(rewrite EBS1; exact BS0)
ltac:(rewrite EBS1; exact INB) ltac:(rewrite ELS1; exact INL) ltac:(rewrite ELS1; exact ING) INSY NBL NBG NLG NSB NSL NSG
INF FA1 FA2 FG1 FG2 SEP_AG SUBLV3 LVM CR0 ART2 MI2 ST2 LOW LOR SPT SPA PF2 T c0 Hc _).
intros c4 Σ1 L1 G1 m4 lws4 gws4 bos' segptr skipped z1 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 os3 Hc4 ESK Hsk Hseg Hbos ART4 MI4 ST4 FR4 OS4 BODY4
LAC4 LPRE4 LLEN4 GRA4 GLEN4 OG4 HS4 BS4 PF4 FOK3 SINV3 LR3 BINV3 LOK3 Hls3 EBS3 ELS3 LS3B BPRE3 INL4 ING4 NLG4 INB4 INSY4 NBL4 NBG4 NSL4 NSG4 SUB4 LVM4 NAL4 NAG4
CASEL EF4 ES4 EC4 EP4.
assert (POK : pgi_ok os (ubytes hs) = true).
{ unfold pgi_ok. fold os1. rewrite ESER', Z.eqb_refl. unfold ogg_page_version. rewrite CVER. reflexivity. }
assert (E3 : pgi_os3 os (ubytes hs) = os3) by reflexivity.
assert (LIVE1 : forall Bd', pagein_live (rt_live RT Σ) os (ubytes hs) (ubytes bs) Bd L Gv Bd' L1 G1
= let l1 := rt_live RT Σ1 in
let bodysize := pg_body_len og - skipped in
if (bodysize =? 0) || (os_body_fill os3 <? os_body_storage os3 - bodysize) then l1 else (Bd', os_body_storage os3 + bodysize + 1024) :: live_remove Bd l1).
{ intros Bd'. unfold pagein_live. rewrite POK. cbv zeta. fold os1. rewrite E3, ESK. cbn [snd]. rewrite zlength_ubytes, BSLEN.
destruct CASEL as [(C1 & -> & -> & E)|(C1 & E)]; rewrite E.
- replace (os_lacing_fill os1 <? os_lacing_storage os1 - (znth (ubytes hs) 26 + 1)) with true by (symmetry; apply Z.ltb_lt; exact C1). reflexivity.
- replace (os_lacing_fill os1 <? os_lacing_storage os1 - (znth (ubytes hs) 26 + 1)) with false by (symmetry; apply Z.ltb_ge; exact C1). reflexivity. }
pose proof SINV3 as (K1 & K2 & K3 & K4 & K5).
assert (LOW4 : rt_sp0 RT Σ1 - STACK_WIN <= lo) by (rewrite ES4; exact LOW).
assert (SPL4 : forall a, aclient LV (rt_frames RT Σ) (bv_unsigned sp) a -> bv_unsigned sp <= a \/ a < rt_sp0 RT Σ1 - STACK_WIN) by (intros a Ha; rewrite ES4; exact (SPL a Ha)).
destruct (Z.eqb_spec (pg_body_len og - skipped) 0) as [BZ|BNZ].
+
replace (pg_body_len og - skipped =? 0) with true in Hc4 by (symmetry; apply Z.eqb_eq; exact BZ). cbv iota in Hc4.
refine (pgi_phaseF Σ1 PMc ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 z1 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 _ _ _ _ _ z28 z29 z30 z31 F fc m m4
LV (rt_frames RT Σ) A G Dsy nsy Bd L1 G1 f lo segptr bos' k og os3 shdr hs bs bodybytes1 j0 lws4 gws4
FDO MST OS4 HL A0 BODY4 ltac:(rewrite EBS3, EBS1; exact BLEN1) LAC4 LPRE4 LLEN4 GRA4 GLEN4 FR4 OG4 HS4 BS4 FOK3 ltac:(clear - Hls3 Hseg; lia) Hseg Hbos
K3 ltac:(clear - K1 K2; lia) LOK3 LENH HLEN BSLEN PG0 PGIN ltac:(rewrite EBS3; exact INB4) INL4 ING4 INSY4 NBL4 NBG4 NLG4 NSL4 NSG4 EF4
INF FA1 FA2 FG1 FG2 SUB4 SPL4 NAL4 NAG4 ART4 MI4 ST4 LOW4 LOR SPT PF4 T c4 Hc4 _).
intros c5 Hc5. apply Hk. exists Σ1, Bd, L1, G1.
assert (ERES : pagein_res os (ubytes hs) (ubytes bs) = (0, pagein_segments os3 (ubytes hs) bos' segptr)).
{ unfold pagein_res. cbv zeta. fold os1. rewrite ESER', Z.eqb_refl. cbn [negb]. unfold ogg_page_version. rewrite CVER. replace (0 <? 0) with false by reflexivity.
rewrite E3, ESK. rewrite zlength_ubytes, BSLEN, BZ. reflexivity. }
rewrite ERES. cbn [fst snd].
pose proof (segments_shape os3 (ubytes hs) bos' segptr HBOK ltac:(rewrite zlength_lacing_of by lia; lia) ltac:(clear - K2; lia)) as SH. cbv zeta in SH.
destruct SH as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13 & Q14 & Q15 & Q16 & Q17).
split; [| split; [reflexivity| split; [reflexivity| split; [| split; [| split; [| repeat split; assumption]]]]]].
* eapply ASTA_conseq; [exact Hc5|]. intros ms (m5 & lws5 & gws5 & RS5 & RA5 & PF5 & OS5 & BODY5 & LAC5 & LPRE5 & LLEN5 & GRA5 & GLEN5).
exists m5, bodybytes1, lws5, gws5.
split; [exact RS5|]. split; [exact RA5|]. split; [exact PF5|]. split; [exact OS5|].
unfold stream_arrays. rewrite Q4, Q5, Q7.
split; [apply u8arr_rw_CB; exact BODY5|]. split; [rewrite EBS3, EBS1; exact BLEN1|]. split; [exact BPRE3|].
split; [exact LAC5|]. split; [exact LPRE5|]. split; [exact LLEN5|]. split; [exact GRA5| exact GLEN5].
* unfold stream_live. rewrite Q4, Q5, EBS3. repeat split; assumption.
* rewrite (LIVE1 Bd). cbv zeta. rewrite BZ. reflexivity.
* unfold pagein_same. rewrite POK. split; [intros E; discriminate E|]. split.
-- intros _ C. fold os1 in C. destruct CASEL as [(C1 & E1 & E2 & _)|(C1 & _)]; [exact (conj E1 E2)|]. exfalso. apply Z.ltb_lt in C. lia.
-- intros _ _. reflexivity.
+
replace (pg_body_len og - skipped =? 0) with false in Hc4 by (symmetry; apply Z.eqb_neq; exact BNZ). cbv iota in Hc4.
assert (BSRC : bytes_at asegs m4 (Dsy + pg_hdr og + pg_header_len og + skipped) (firstn (Z.to_nat (pg_body_len og - skipped)) (skipn (Z.to_nat skipped) bs))).
{ pose proof (bytes_at_sub m4 _ bs (Z.to_nat skipped) (Z.to_nat (pg_body_len og - skipped)) BS4 ltac:(clear - Hsk HSUM BSLEN BNZ; lia)) as X.
rewrite Z2Nat.id in X by lia. exact X. }
pose proof BINV3 as (J1' & J2' & J3' & J4'). pose proof BPRE3 as (BP1' & BP2'). unfold zlength in J1'.
pose proof (body_inv_fill_nonneg _ BINV3) as BF30.
assert (NPOS : 0 < pg_body_len og - skipped) by (clear - BNZ Hsk HSUM; lia).
assert (LSRC : Z.of_nat (length (firstn (Z.to_nat (pg_body_len og - skipped)) (skipn (Z.to_nat skipped) bs))) = pg_body_len og - skipped)
by (rewrite firstn_length_le by (rewrite length_skipn; clear - Hsk HSUM BSLEN NPOS; lia); lia).
assert (ZSRC : ubytes (firstn (Z.to_nat (pg_body_len og - skipped)) (skipn (Z.to_nat skipped) bs)) = zslice skipped (pg_body_len og - skipped) (ubytes bs))
by (rewrite ubytes_firstn, ubytes_skipn; reflexivity).
assert (SUBLVB : forall e, In e LV -> In e (rt_live RT Σ1) /\ fst e <> Bd) by (intros e He; split; [exact (SUB4 e He)| exact (proj1 (proj2 (SUBLV3 e He)))]).
assert (LS3P : 0 < os_lacing_storage os3) by (clear - LS0 ELS1 ELS3 LS3B; lia).
pose proof (proj1 (u8arr_rw_CB _ _ _) (u32arr_u8 _ _ _ LAC4)) as LAC4c. pose proof (proj1 (u8arr_rw_CB _ _ _) (u64arr_u8 _ _ _ GRA4)) as GRA4c.
assert (EL4 : Z.of_nat (length (u32s lws4)) = 4 * os_lacing_storage os3) by (rewrite u32s_length; lia).
assert (EG4 : Z.of_nat (length (u64s gws4)) = 8 * os_lacing_storage os3) by (rewrite u64s_length; lia).
refine (pgi_phaseX Σ1 PMc ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 z1 z5 z6 z7 _ z10 z11 z12 z13 z14 z15 z16 z17 _ _ _ _ _ _ _ _ z28 z29 z30 z31 F fc m m4
LV A G Dsy nsy Bd L1 G1 f lo (pg_body_len og - skipped) (Dsy + pg_hdr og + pg_header_len og + skipped) skipped k og os3 shdr hs bs bodybytes1 j0
(firstn (Z.to_nat (pg_body_len og - skipped)) (skipn (Z.to_nat skipped) bs)) (ubytes bs) lws4 gws4
FDO MST OS4 HL A0 BODY4 ltac:(rewrite EBS3, EBS1; exact BLEN1) BPRE3 ltac:(unfold zlength; exact J1') ltac:(clear - BF30 BP2' J1' BLEN1 EBS3 EBS1; lia)
ltac:(clear - BSB EBS3 EBS1 Hsk HSUM NPOS; lia) LAC4c GRA4c FR4 OG4 HS4 BS4 BSRC LSRC NPOS ZSRC
ltac:(clear - PG0 HLEN Hsk HSUM; lia) ltac:(clear - PGIN Hsk HSUM HLEN BSLEN; lia) ltac:(clear - PG0; lia) ltac:(clear - PGIN; lia) HLEN BSLEN
ltac:(rewrite EBS3; exact INB4) ltac:(rewrite EL4; exact INL4) ltac:(rewrite EG4; exact ING4) INSY4 NBL4 NBG4 NSB ltac:(lia) ltac:(lia)
ltac:(rewrite EF4; exact INF) FA1 FA2 FG1 FG2 SEP_AG SUBLVB ltac:(clear - LVM LVM4; lia) ltac:(rewrite EC4; exact CR0) ART4 MI4 ST4 LOW4 LOR SPT SPA ltac:(rewrite EF4; exact PF4) T c4 Hc4 _).
intros c6 Σ2 Bd2 m6 bb6 w1 w5 w6 w7 w10 w11 w12 w13 w14 w15 w16 w17 w28 w29 w30 w31 Hc6 ART6 MI6 ST6 FR6 OS6 BODY6 BLEN6 BPRE6 LAC6 GRA6 OG6 HS6 BS6 PF6
INB6 INL6 ING6 INSY6 NBL6 NBG6 NSB6 SUB6 LVM6 CASEB EF6 ES6 EC6 EP6.
set (bsz := pg_body_len og - skipped) in *.
set (os5 := pagein_body (body_expand_res os3 bsz) (ubytes bs) skipped bsz) in *.
pose proof (body_expand_res_fields os3 bsz) as (EX1 & EX2 & EX3 & EX4 & EX5 & EX6 & EX7 & EX8).
assert (FOK5 : stream_fields_ok os5).
{ unfold os5. apply fields_ok_body; [| rewrite EX2; clear - BF30 BP2' J1' BLEN1 EBS3 EBS1 BSB BS0 NPOS Hsk HSUM; unfold bsz in *; lia].
unfold body_expand_res. destruct (_ <? _); [exact FOK3|]. apply fields_ok_set_blocks; [exact FOK3| clear - BSB EBS3 EBS1 BS0 NPOS Hsk HSUM; unfold bsz in *; lia| pose proof FOK3 as (_ & _ & _ & X & _); exact X]. }
assert (ES5 : os_lacing os5 = os_lacing os3 /\ os_lacing_storage os5 = os_lacing_storage os3 /\ os_lacing_fill os5 = os_lacing_fill os3 /\ os_lacing_packet os5 = os_lacing_packet os3
/\ os_body_storage os5 = os_body_storage (body_expand_res os3 bsz) /\ os_body os5 = os_body os3 ++ zslice skipped bsz (ubytes bs)).
{ unfold os5, pagein_body, set_body. cbn [os_lacing os_lacing_storage os_lacing_fill os_lacing_packet os_body_storage os_body]. rewrite EX8, EX4, EX5, EX6, EX1.
repeat split; reflexivity. }
destruct ES5 as (E5l & E5ls & E5lf & E5lp & E5bs & E5b).
apply u8arr_rw_CB, u8_u32arr in LAC6. apply u8arr_rw_CB, u8_u64arr in GRA6.
assert (LOW6 : rt_sp0 RT Σ2 - STACK_WIN <= lo) by (rewrite ES6, ES4; exact LOW).
assert (SPL6 : forall a, aclient LV (rt_frames RT Σ) (bv_unsigned sp) a -> bv_unsigned sp <= a \/ a < rt_sp0 RT Σ2 - STACK_WIN) by (intros a Ha; rewrite ES6, ES4; exact (SPL a Ha)).
refine (pgi_phaseF Σ2 PMc ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 w1 w5 w6 w7 w10 w11 w12 w13 w14 w15 w16 w17 _ _ _ _ _ w28 w29 w30 w31 F fc m m6
LV (rt_frames RT Σ) A G Dsy nsy Bd2 L1 G1 f lo segptr bos' k og os5 shdr hs bs bb6 j0 lws4 gws4
FDO MST OS6 HL A0 BODY6 ltac:(rewrite E5bs; exact BLEN6) LAC6 ltac:(rewrite E5l; exact LPRE4) ltac:(rewrite E5ls; exact LLEN4) GRA6 ltac:(rewrite E5ls; exact GLEN4)
FR6 OG6 HS6 BS6 FOK5 ltac:(rewrite E5lf, E5ls; clear - Hls3 Hseg; lia) Hseg Hbos
ltac:(rewrite E5l, E5lf; exact K3) ltac:(rewrite E5lp, E5lf; clear - K1 K2; lia) ltac:(rewrite E5l; exact LOK3) LENH HLEN BSLEN PG0 PGIN
ltac:(rewrite E5bs; exact INB6) ltac:(rewrite E5ls, <- EL4; exact INL6) ltac:(rewrite E5ls, <- EG4; exact ING6) INSY6 NBL6 NBG6 NLG4 NSL4 NSG4
ltac:(rewrite EF6; exact EF4) INF FA1 FA2 FG1 FG2 SUB6 SPL6 ltac:(rewrite E5ls; exact NAL4) ltac:(rewrite E5ls; exact NAG4)
ART6 MI6 ST6 LOW6 LOR SPT ltac:(rewrite EF4 in PF6; exact PF6) T c6 Hc6 _).
intros c7 Hc7. apply Hk. exists Σ2, Bd2, L1, G1.
assert (ERES : pagein_res os (ubytes hs) (ubytes bs) = (0, pagein_segments os5 (ubytes hs) bos' segptr)).
{ unfold pagein_res. cbv zeta. fold os1. rewrite ESER', Z.eqb_refl. cbn [negb]. unfold ogg_page_version. rewrite CVER. replace (0 <? 0) with false by reflexivity.
rewrite E3, ESK. rewrite zlength_ubytes, BSLEN. fold bsz.
replace (bsz =? 0) with false by (symmetry; apply Z.eqb_neq; exact BNZ). reflexivity. }
rewrite ERES. cbn [fst snd].
pose proof (segments_shape os5 (ubytes hs) bos' segptr HBOK ltac:(rewrite zlength_lacing_of by lia; lia) ltac:(rewrite E5lp, E5lf; clear - K2; lia)) as SH. cbv zeta in SH.
destruct SH as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13 & Q14 & Q15 & Q16 & Q17).
split; [| split; [reflexivity| split; [reflexivity| split; [| split; [| split; [| repeat split; congruence]]]]]].
* eapply ASTA_conseq; [exact Hc7|]. intros ms (m7 & lws7 & gws7 & RS7 & RA7 & PF7 & OS7 & BODY7 & LAC7 & LPRE7 & LLEN7 & GRA7 & GLEN7).
exists m7, bb6, lws7, gws7.
split; [exact RS7|]. split; [exact RA7|]. split; [exact PF7|]. split; [exact OS7|].
unfold stream_arrays. rewrite Q4, Q5, Q7.
split; [apply u8arr_rw_CB; exact BODY7|]. split; [rewrite E5bs; exact BLEN6|]. split; [rewrite E5b; exact BPRE6|].
split; [exact LAC7|]. split; [exact LPRE7|]. split; [exact LLEN7|]. split; [exact GRA7| exact GLEN7].
* unfold stream_live. rewrite Q4, Q5, E5bs, E5ls. split; [exact INB6|]. split; [rewrite <- EL4; exact INL6|]. split; [rewrite <- EG4; exact ING6|].
split; [exact NBL6|]. split; [exact NBG6| exact NLG4].
* rewrite (LIVE1 Bd2). cbv zeta. fold bsz.
replace (bsz =? 0) with false by (symmetry; apply Z.eqb_neq; exact BNZ). cbn [orb].
destruct CASEB as [(C2 & -> & E)|(C2 & E)]; rewrite E.
-- replace (os_body_fill os3 <? os_body_storage os3 - bsz) with true by (symmetry; apply Z.ltb_lt; exact C2). reflexivity.
-- replace (os_body_fill os3 <? os_body_storage os3 - bsz) with false by (symmetry; apply Z.ltb_ge; exact C2). reflexivity.
* unfold pagein_same. rewrite POK. split; [intros E; discriminate E|]. split.
-- intros _ C. fold os1 in C. destruct CASEL as [(C1 & E1 & E2 & _)|(C1 & _)]; [exact (conj E1 E2)|]. exfalso. apply Z.ltb_lt in C. lia.
-- intros _ C. rewrite E3, ESK in C. cbn [snd] in C. rewrite zlength_ubytes, BSLEN in C. fold bsz in C.
replace (bsz =? 0) with false in C by (symmetry; apply Z.eqb_neq; exact BNZ). cbn [orb] in C. apply Z.ltb_lt in C.
destruct CASEB as [(C2 & EB2 & _)|(C2 & _)]; [exact EB2| exfalso; lia].
Qed.

End OggPageinCPS.
