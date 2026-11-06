(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qz X1od X1r8.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require X1qy.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X05m X09u X0af X09x X0ae X09t X09z X0a0
X0a4 X0a5 X09v X09w.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X10j X110 X10g X10l X10m X10q X10r X10h X10i.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10j OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X110 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10g OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10l OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10m OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10q OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10r OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10h OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10i.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition os_pure (os : stream_st bptr) : Prop :=
stream_fields_ok os /\ stream_inv os /\ body_inv os /\ lacing_vals_ok (os_lacing os)
/\ length (os_granules os) = length (os_lacing os)
/\ os_body_data os <> None /\ os_lacing_vals os <> None /\ os_granule_vals os <> None
/\ 0 < os_lacing_storage os /\ 0 < os_body_storage os.

Lemma stream_inv_glen : forall os : stream_st bptr, stream_inv os -> length (os_granules os) = length (os_lacing os).
Proof. intros os (_ & _ & C & D & _). unfold zlength in C, D. lia. Qed.

Lemma init_os_pure : forall ser, -2^31 <= ser < 2^31 -> os_pure (init_os (Some tt) (Some tt) (Some tt) ser).
Proof.
intros ser SR. unfold os_pure, init_os.
split; [unfold stream_fields_ok, int31; cbn; lia|].
split; [unfold stream_inv; cbn; rewrite ?zlength_nil; lia|].
split; [apply ogg_stream_init_body_inv|].
split; [constructor|]. split; [reflexivity|].
cbn. split; [discriminate|]. split; [discriminate|]. split; [discriminate|]. lia.
Qed.

Lemma reset_os_pure : forall (os : stream_st bptr) ser, os_pure os -> -2^31 <= ser < 2^31 ->
os_pure (snd (ogg_stream_reset_serialno os ser))
/\ os_lacing_storage (snd (ogg_stream_reset_serialno os ser)) = os_lacing_storage os
/\ os_body_storage (snd (ogg_stream_reset_serialno os ser)) = os_body_storage os
/\ os_lacing_fill (snd (ogg_stream_reset_serialno os ser)) = 0 /\ os_body_fill (snd (ogg_stream_reset_serialno os ser)) = 0
/\ os_lacing_returned (snd (ogg_stream_reset_serialno os ser)) = 0
/\ os_serialno (snd (ogg_stream_reset_serialno os ser)) = ser
/\ os_body (snd (ogg_stream_reset_serialno os ser)) = [] /\ os_lacing (snd (ogg_stream_reset_serialno os ser)) = [].
Proof.
intros os ser (FOK & SINV & BINV & LOK & GL & BD & LV & GV & LS & BS) SR.
unfold ogg_stream_reset_serialno, ogg_stream_check.
destruct (os_body_data os) as [b|] eqn:EB; [| exfalso; exact (BD eq_refl)].
cbn [snd]. unfold ogg_stream_reset. cbn.
pose proof FOK as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12). unfold int31 in *.
split; [| repeat split; reflexivity].
unfold os_pure. cbn.
split; [unfold stream_fields_ok, int31; cbn; lia|].
split; [unfold stream_inv; cbn; rewrite ?zlength_nil; lia|].
split; [unfold body_inv; cbn; rewrite ?zlength_nil; repeat split; try lia; constructor|].
split; [constructor|]. split; [reflexivity|].
rewrite EB. split; [discriminate|]. split; [exact LV|]. split; [exact GV|]. lia.
Qed.

Lemma lor512_lt2048 : forall v, 0 <= v < 2048 -> 0 <= Z.lor v 512 < 2048.
Proof. intros v Hv. apply (lor_small v 512 11); lia. Qed.

Lemma lacing_vals_ok_segments_h : forall (os : stream_st bptr) hdr bos segptr,
bytes_ok (lacing_of hdr) -> lacing_vals_ok (os_lacing os) -> lacing_vals_ok (os_lacing (pagein_segments os hdr bos segptr)).
Proof.
intros os hdr bos segptr Hb H. unfold pagein_segments.
destruct (seg_loop (zdrop segptr (lacing_of hdr)) (negb (bos =? 0)) (os_lacing_fill os) (os_lacing_packet os) (-1))
as [[[[lac gran] f] p] sv] eqn:E.
pose proof (seg_loop_vals512 _ _ _ _ _ _ _ _ _ _ (Forall_zdrop _ segptr _ Hb) E) as L.
assert (A : lacing_vals_ok (os_lacing os ++ lac)).
{ apply Forall_app. split; [exact H|]. eapply Forall_impl; [| exact L]. cbv beta. intros; lia. }
unfold set_lacing, set_tail; cbn.
destruct (negb (ogg_page_eos hdr =? 0)); [| exact A].
destruct (0 <? f); [| exact A].
apply X0af.Forall_zupd; [exact A|]. apply lor512_lt2048. apply (Forall_znth _ _ _ A). lia.
Qed.

Lemma pagein_returned_lacing_returned : forall os : stream_st bptr, os_lacing_returned (pagein_returned os) = 0 \/ pagein_returned os = os /\ os_lacing_returned os = 0.
Proof.
intros os. unfold pagein_returned.
destruct (negb (os_body_returned os =? 0)) eqn:E1; destruct (os_lacing_returned _ =? 0) eqn:E2; cbn [negb];
first [left; reflexivity | apply Z.eqb_eq in E2; first [left; exact E2 | right; split; [reflexivity| exact E2]]].
Qed.

Lemma pagein_res_pure : forall (os : stream_st bptr) (hs : list byte) (body : list Z),
os_pure os -> length hs = (27 + Z.to_nat (znth (ubytes hs) 26))%nat ->
bytes_ok body -> zsum (lacing_of (ubytes hs)) = zlength body ->
os_lacing_fill os <= os_lacing_storage os -> os_body_fill os <= os_body_storage os ->
os_lacing_storage os + os_lacing_fill os + 600 < 2^30 -> os_body_storage os + os_body_fill os + 2 * zlength body + 1024 < 2^62 ->
let os' := snd (pagein_res os (ubytes hs) body) in
os_pure os'
/\ os_lacing_fill os' <= os_lacing_fill os + znth (ubytes hs) 26 + 1
/\ os_body_fill os' <= os_body_fill os + zlength body
/\ os_lacing_storage os' <= Z.max (os_lacing_storage os) (os_lacing_fill os + 2 * (znth (ubytes hs) 26 + 1) + 32)
/\ os_body_storage os' <= Z.max (os_body_storage os) (os_body_fill os + 2 * zlength body + 1024)
/\ os_lacing_storage os <= os_lacing_storage os' /\ os_body_storage os <= os_body_storage os'
/\ os_lacing_fill os' <= os_lacing_storage os' /\ os_body_fill os' <= os_body_storage os'
/\ os_serialno os' = os_serialno os.
Proof.
intros os hs body (FOK & SINV & BINV & LOK & GL & BD & LV & GV & LS & BS) LENH BOK ZSEQ LFS BFS LSB BSB. cbv zeta.
set (hdr := ubytes hs) in *.
assert (H26 : 0 <= znth hdr 26 < 256) by (apply znth_ubytes_range).
assert (HBOK : bytes_ok (lacing_of hdr)) by (apply bytes_ok_zslice; apply ubytes_ok).
assert (ZLL : zlength (lacing_of hdr) = znth hdr 26) by (apply zlength_lacing_of; [exact LENH| exact (proj1 H26)]).
pose proof FOK as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12). unfold int31 in F4, F5, F6, F7.
pose proof SINV as (I1 & I2 & I3 & I4 & I5).
pose proof (body_inv_returned_le_fill os BINV) as BRF.
pose proof (zlength_nonneg body) as ZB.

pose proof (pagein_returned_inv os SINV) as (SINV1 & LR1 & ELV1 & EGV1 & EBD1 & ELS1 & EBS1 & ESN1 & EPN1).
pose proof (pagein_returned_body_inv os SINV BINV) as (BINV1 & BR1 & BFR1 & LF1).
pose proof (fields_ok_returned os FOK SINV BRF) as FOK1.
pose proof (lacing_vals_ok_returned os LOK) as LOK1.
unfold pagein_res. cbv zeta.
set (os1 := pagein_returned os) in *.
pose proof (body_inv_fill_nonneg os1 BINV1) as BF1N.
pose proof SINV1 as (I1a & I2a & I3a & I4a & _).
assert (POS1 : os_pure os1).
{ unfold os_pure. split; [exact FOK1|]. split; [exact SINV1|]. split; [exact BINV1|]. split; [exact LOK1|].
split; [exact (stream_inv_glen os1 SINV1)|]. rewrite ELV1, EGV1, EBD1, ELS1, EBS1. repeat split; assumption. }
assert (FAIL : os_pure os1
/\ os_lacing_fill os1 <= os_lacing_fill os + znth hdr 26 + 1 /\ os_body_fill os1 <= os_body_fill os + zlength body
/\ os_lacing_storage os1 <= Z.max (os_lacing_storage os) (os_lacing_fill os + 2 * (znth hdr 26 + 1) + 32)
/\ os_body_storage os1 <= Z.max (os_body_storage os) (os_body_fill os + 2 * zlength body + 1024)
/\ os_lacing_storage os <= os_lacing_storage os1 /\ os_body_storage os <= os_body_storage os1
/\ os_lacing_fill os1 <= os_lacing_storage os1 /\ os_body_fill os1 <= os_body_storage os1 /\ os_serialno os1 = os_serialno os).
{ rewrite ELS1, EBS1, LF1, BFR1, ESN1. split; [exact POS1|]. repeat split; lia. }
destruct (negb (ogg_page_serialno hdr =? os_serialno os1)); [exact FAIL|].
destruct (0 <? ogg_page_version hdr); [exact FAIL|].
clear FAIL.

set (need := znth hdr 26 + 1) in *.
assert (LFS1 : os_lacing_fill os1 <= os_lacing_storage os1) by (rewrite ELS1, LF1; lia).
pose proof (lacing_expand_res_fields os1 need ltac:(lia) LFS1) as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12).
assert (XLS : os_lacing_storage (lacing_expand_res os1 need) <= Z.max (os_lacing_storage os1) (os_lacing_fill os1 + 2 * need + 32)).
{ unfold lacing_expand_res. destruct (Z.ltb_spec (os_lacing_fill os1) (os_lacing_storage os1 - need)); cbn [set_blocks os_lacing_storage]; lia. }
assert (XV : os_lacing_vals (lacing_expand_res os1 need) <> None /\ os_granule_vals (lacing_expand_res os1 need) <> None
/\ os_serialno (lacing_expand_res os1 need) = os_serialno os1 /\ os_granules (lacing_expand_res os1 need) = os_granules os1
/\ os_header_fill (lacing_expand_res os1 need) = os_header_fill os1).
{ unfold lacing_expand_res. destruct (os_lacing_fill os1 <? os_lacing_storage os1 - need); cbn [set_blocks os_lacing_vals os_granule_vals os_serialno os_granules os_header_fill].
- rewrite ELV1, EGV1. repeat split; first [assumption | reflexivity].
- repeat split; discriminate. }
destruct XV as (XLV & XGV & XSN & XGR & XHF).
assert (SINV2 : stream_inv (lacing_expand_res os1 need)).
{ unfold lacing_expand_res. destruct (_ <? _); [exact SINV1| exact (proj1 (set_blocks_inv _ _ _ _ _ _ SINV1))]. }
assert (BINV2 : body_inv (lacing_expand_res os1 need)).
{ unfold lacing_expand_res. destruct (_ <? _); [exact BINV1| apply set_blocks_body_inv; exact BINV1]. }
assert (FOK2 : stream_fields_ok (lacing_expand_res os1 need)).
{ unfold lacing_expand_res. destruct (Z.ltb_spec (os_lacing_fill os1) (os_lacing_storage os1 - need)); [exact FOK1|].
apply fields_ok_set_blocks; [exact FOK1| rewrite EBS1; lia| unfold int31; rewrite ELS1; lia]. }
assert (LOK2 : lacing_vals_ok (os_lacing (lacing_expand_res os1 need))) by (rewrite X9; exact LOK1).
set (os2 := lacing_expand_res os1 need) in *.

pose proof (pagein_unroll_inv os2 (ogg_page_pageno hdr) SINV2 ltac:(rewrite X8; exact LR1)) as (SINV3 & LR3 & ELV3 & EGV3 & EBD3 & ELS3 & EBS3 & HLF3).
pose proof (pagein_unroll_body_inv os2 (ogg_page_pageno hdr) SINV2 ltac:(rewrite X8; exact LR1) BINV2) as (BINV3 & HBF3 & HBR3).
pose proof (body_inv_fill_nonneg _ BINV3) as BF3N.
pose proof SINV2 as (I1b & I2b & I3b & I4b & _).
assert (FOK3 : stream_fields_ok (pagein_unroll os2 (ogg_page_pageno hdr))) by (apply fields_ok_unroll; [exact FOK2| exact SINV2| lia| rewrite X6, LF1; lia]).
pose proof (lacing_vals_ok_unroll os2 (ogg_page_pageno hdr) LOK2) as LOK3.
assert (ESN3 : os_serialno (pagein_unroll os2 (ogg_page_pageno hdr)) = os_serialno os2).
{ unfold pagein_unroll. destruct (negb _); [| reflexivity]. destruct (negb _); destruct os2; reflexivity. }
assert (E3 : pgi_os3 os hdr = pagein_unroll os2 (ogg_page_pageno hdr)) by reflexivity. rewrite E3. clear E3.
set (os3 := pagein_unroll os2 (ogg_page_pageno hdr)) in *.
pose proof SINV3 as (I1c & I2c & I3c & I4c & _).

pose proof (pagein_skip_sum os3 hdr HBOK) as SKS.
destruct (pagein_skip os3 hdr) as [[bos segptr] skipped] eqn:ESK.
destruct SKS as (SEG & SKE).
pose proof (zsum_split segptr (lacing_of hdr) ltac:(lia)) as ZSP.
pose proof (zsum_bytes_nonneg _ (bytes_ok_ztake segptr _ HBOK)) as ZN1.
pose proof (zsum_bytes_nonneg _ (bytes_ok_zdrop segptr _ HBOK)) as ZN2.
set (bsz := zlength body - skipped) in *.
assert (BSZ : 0 <= bsz <= zlength body) by (unfold bsz; lia).

set (osB := if negb (bsz =? 0) then body_expand_res os3 bsz else os3).
assert (BFS3 : os_body_fill os3 <= os_body_storage os3) by (rewrite EBS3, X4, EBS1; lia).
pose proof (body_expand_res_fields os3 bsz) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8).
pose proof (body_expand_res_room os3 bsz ltac:(lia) BFS3) as (YR1 & YR2).
assert (YBS : os_body_storage (body_expand_res os3 bsz) <= Z.max (os_body_storage os3) (os_body_fill os3 + 2 * bsz + 1024)).
{ unfold body_expand_res. destruct (Z.ltb_spec (os_body_fill os3) (os_body_storage os3 - bsz)); cbn [set_blocks os_body_storage]; lia. }
assert (YV : os_body_data (body_expand_res os3 bsz) <> None /\ os_lacing_vals (body_expand_res os3 bsz) = os_lacing_vals os3
/\ os_granule_vals (body_expand_res os3 bsz) = os_granule_vals os3 /\ os_serialno (body_expand_res os3 bsz) = os_serialno os3
/\ os_granules (body_expand_res os3 bsz) = os_granules os3).
{ unfold body_expand_res. destruct (os_body_fill os3 <? os_body_storage os3 - bsz); cbn [set_blocks os_body_data os_lacing_vals os_granule_vals os_serialno os_granules].
- rewrite EBD3, X5, EBD1. repeat split; [exact BD| reflexivity ..].
- repeat split; [discriminate| reflexivity ..]. }
destruct YV as (YBD & YLV & YGV & YSN & YGR).
assert (EBD3' : os_body_data os3 <> None) by (rewrite EBD3, X5, EBD1; exact BD).
assert (PB : stream_inv osB /\ os_lacing_returned osB = 0 /\ body_inv osB /\ stream_fields_ok osB /\ lacing_vals_ok (os_lacing osB)
/\ os_lacing osB = os_lacing os3 /\ os_lacing_fill osB = os_lacing_fill os3 /\ os_lacing_packet osB = os_lacing_packet os3
/\ os_lacing_storage osB = os_lacing_storage os3 /\ os_body_fill osB = os_body_fill os3
/\ os_body_data osB <> None /\ os_lacing_vals osB = os_lacing_vals os3 /\ os_granule_vals osB = os_granule_vals os3
/\ os_serialno osB = os_serialno os3
/\ os_body_storage os3 <= os_body_storage osB <= Z.max (os_body_storage os3) (os_body_fill os3 + 2 * bsz + 1024)
/\ os_body_fill osB + bsz <= os_body_storage osB).
{ unfold osB. destruct (Z.eqb_spec bsz 0) as [BZ|BNZ]; cbn [negb].
- split; [exact SINV3|]. split; [exact LR3|]. split; [exact BINV3|]. split; [exact FOK3|]. split; [exact LOK3|].
do 9 (split; [first [reflexivity | exact EBD3']|]). split; [lia|]. rewrite BZ. lia.
- assert (S4 : stream_inv (body_expand_res os3 bsz) /\ os_lacing_returned (body_expand_res os3 bsz) = os_lacing_returned os3).
{ unfold body_expand_res. destruct (_ <? _); [split; [exact SINV3| reflexivity]| exact (set_blocks_inv _ _ _ _ _ _ SINV3)]. }
split; [exact (proj1 S4)|]. split; [rewrite (proj2 S4); exact LR3|].
split; [unfold body_expand_res; destruct (_ <? _); [exact BINV3| apply set_blocks_body_inv; exact BINV3]|].
split.
{ unfold body_expand_res. destruct (Z.ltb_spec (os_body_fill os3) (os_body_storage os3 - bsz)); [exact FOK3|].
apply fields_ok_set_blocks; [exact FOK3| rewrite EBS3, X4, EBS1; lia| pose proof FOK3 as (_ & _ & _ & Z4 & _); exact Z4]. }
split; [rewrite Y8; exact LOK3|].
split; [exact Y8|]. split; [exact Y5|]. split; [exact Y6|]. split; [exact Y4|]. split; [exact Y2|].
split; [exact YBD|]. split; [exact YLV|]. split; [exact YGV|]. split; [exact YSN|]. split; [lia|]. rewrite Y2. lia. }
destruct PB as (SINVB & LRB & BINVB & FOKB & LOKB & ELB & ELFB & ELPB & ELSB & EBFB & EBDB & ELVB & EGVB & ESNB & (BSB1 & BSB2) & BROOM).
pose proof SINVB as (I1d & I2d & I3d & I4d & _).

assert (ERES : (if negb (bsz =? 0) then (0, pagein_segments (pagein_body (body_expand_res os3 bsz) body skipped bsz) hdr bos segptr)
else (0, pagein_segments os3 hdr bos segptr))
= (0, pagein_segments (if negb (bsz =? 0) then pagein_body osB body skipped bsz else osB) hdr bos segptr)).
{ unfold osB. destruct (negb (bsz =? 0)); reflexivity. }
rewrite ERES. cbn [snd]. clear ERES.
pose proof (pagein_body_segments_body_inv osB hdr body bos segptr skipped SINVB LRB BINVB HBOK ZSEQ SEG SKE) as PBS.
cbv zeta in PBS. fold bsz in PBS. destruct PBS as (BINV5 & BF5 & _ & BR5).
set (os4 := if negb (bsz =? 0) then pagein_body osB body skipped bsz else osB) in *.
assert (P4 : stream_inv os4 /\ os_lacing_returned os4 = 0 /\ stream_fields_ok os4 /\ lacing_vals_ok (os_lacing os4)
/\ os_lacing_fill os4 = os_lacing_fill os3 /\ os_lacing_packet os4 = os_lacing_packet os3 /\ os_lacing_storage os4 = os_lacing_storage os3
/\ os_body_storage os4 = os_body_storage osB /\ os_body_data os4 <> None /\ os_lacing_vals os4 = os_lacing_vals os3
/\ os_granule_vals os4 = os_granule_vals os3 /\ os_serialno os4 = os_serialno os3).
{ unfold os4. destruct (Z.eqb_spec bsz 0) as [BZ|BNZ]; cbn [negb].
- split; [exact SINVB|]. split; [exact LRB|]. split; [exact FOKB|]. split; [exact LOKB|]. repeat split; assumption.
- pose proof (pagein_body_inv osB body skipped bsz SINVB) as (S5 & R5).
split; [exact S5|]. split; [rewrite R5; exact LRB|]. split; [apply fields_ok_body; [exact FOKB| lia]|].
unfold pagein_body, set_body. cbn [os_lacing os_lacing_fill os_lacing_packet os_lacing_storage os_body_storage os_body_data os_lacing_vals os_granule_vals os_serialno].
split; [exact LOKB|]. repeat split; assumption. }
destruct P4 as (SINV4 & LR4 & FOK4 & LOK4 & ELF4 & ELP4 & ELS4 & EBS4 & EBD4 & ELV4 & EGV4 & ESN4).
pose proof SINV4 as (I1e & I2e & I3e & I4e & _).
assert (PN : 0 <= ogg_page_pageno hdr < 2^32) by (apply pageno_range; lia).
pose proof (segments_shape os4 hdr bos segptr HBOK SEG ltac:(lia)) as SH. cbv zeta in SH.
destruct SH as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13 & Q14 & Q15 & Q16 & Q17).
assert (SINV6 : stream_inv (pagein_segments os4 hdr bos segptr)) by (apply pagein_segments_inv; [exact SINV4| exact LR4| exact HBOK| lia]).
assert (FOK6 : stream_fields_ok (pagein_segments os4 hdr bos segptr)).
{ apply fields_ok_segments; [exact FOK4| exact HBOK| exact SEG| lia| rewrite ELF4, ZLL; fold os2 in HLF3; rewrite X6, LF1 in HLF3; lia| exact PN]. }
pose proof (lacing_vals_ok_segments_h os4 hdr bos segptr HBOK LOK4) as LOK6.

fold os2 in HLF3. rewrite X6, LF1 in HLF3.
assert (ELS3' : os_lacing_storage os3 = os_lacing_storage os2) by exact ELS3.
assert (EBS3' : os_body_storage os3 = os_body_storage os) by (rewrite EBS3; fold os2; rewrite X4, EBS1; reflexivity).
assert (EBF3 : os_body_fill os3 <= os_body_fill os) by (fold os2 in HBF3; rewrite X2, BFR1 in HBF3; lia).
unfold os_pure. rewrite Q1, Q2, Q3, Q4, Q5, Q6, Q12, Q16.
split.
{ split; [exact FOK6|]. split; [exact SINV6|]. split; [exact BINV5|]. split; [exact LOK6|].
split; [exact (stream_inv_glen _ SINV6)|].
split; [exact EBD4|]. split; [rewrite ELV4, ELV3; exact XLV|]. split; [rewrite EGV4, EGV3; exact XGV|].
split; [rewrite ELS4, ELS3'; lia| rewrite EBS4; lia]. }
rewrite ELF4, ELS4, ELS3', EBS4, ESN4, ESN3, XSN, ESN1. rewrite ZLL. fold os2.
rewrite Q6 in BF5. rewrite BF5, EBFB.
split; [lia|]. split; [lia|]. split; [rewrite ELS1, LF1 in XLS; lia|]. split; [rewrite EBS3' in BSB2; lia|].
split; [rewrite ELS1 in X11; lia|]. split; [rewrite EBS3' in BSB1; lia|].
split; [rewrite LF1 in X12; lia|]. split; [lia| reflexivity].
Qed.

Lemma segments_storage : forall (os : stream_st bptr) hdr bos segptr,
os_lacing_storage (pagein_segments os hdr bos segptr) = os_lacing_storage os /\ os_body_storage (pagein_segments os hdr bos segptr) = os_body_storage os.
Proof. intros. unfold pagein_segments. destruct (seg_loop _ _ _ _ _) as [[[[? ?] ?] ?] ?]. split; reflexivity. Qed.
Lemma unroll_lacing_storage : forall (os : stream_st bptr) pn, os_lacing_storage (pagein_unroll os pn) = os_lacing_storage os.
Proof. intros os pn. unfold pagein_unroll. destruct (negb (pn =? os_pageno os)); [| reflexivity]. destruct (negb (os_pageno _ =? -1)); reflexivity. Qed.

Lemma pagein_res_store : forall (os : stream_st bptr) (hdr body : list Z),
let os' := snd (pagein_res os hdr body) in
let os1 := pagein_returned os in
let need := znth hdr 26 + 1 in
let os3 := pgi_os3 os hdr in
let bsz := zlength body - snd (pagein_skip os3 hdr) in
(pgi_ok os hdr = false -> os_lacing_storage os' = os_lacing_storage os /\ os_body_storage os' = os_body_storage os)
/\ (pgi_ok os hdr = true -> (os_lacing_fill os1 <? os_lacing_storage os1 - need) = true -> os_lacing_storage os' = os_lacing_storage os)
/\ (pgi_ok os hdr = true -> (os_lacing_fill os1 <? os_lacing_storage os1 - need) = false -> os_lacing_storage os' = os_lacing_storage os + need + 32)
/\ (pgi_ok os hdr = true -> ((bsz =? 0) || (os_body_fill os3 <? os_body_storage os3 - bsz)) = true -> os_body_storage os' = os_body_storage os)
/\ (pgi_ok os hdr = true -> ((bsz =? 0) || (os_body_fill os3 <? os_body_storage os3 - bsz)) = false -> os_body_storage os' = os_body_storage os + bsz + 1024).
Proof.
intros os hdr body. cbv zeta.
pose proof (pagein_returned_fields os) as (E1 & E2 & E3 & E4 & E5).
pose proof (pgi_os3_body os hdr) as (B1 & B2).
assert (L3 : os_lacing_storage (pgi_os3 os hdr)
= if os_lacing_fill (pagein_returned os) <? os_lacing_storage (pagein_returned os) - (znth hdr 26 + 1) then os_lacing_storage os
else os_lacing_storage os + (znth hdr 26 + 1) + 32).
{ unfold pgi_os3, pgi_os2. rewrite unroll_lacing_storage. unfold lacing_expand_res.
destruct (_ <? _); cbn [set_blocks os_lacing_storage]; rewrite E4; reflexivity. }
unfold pagein_res, pgi_ok. cbv zeta.
destruct (ogg_page_serialno hdr =? os_serialno (pagein_returned os)) eqn:ES; cbn [negb andb].
2:{ split; [intros _; cbn [snd]; rewrite E4, E5; split; reflexivity| repeat split; intros E; discriminate E]. }
destruct (0 <? ogg_page_version hdr) eqn:EV; cbn [negb].
{ split; [intros _; cbn [snd]; rewrite E4, E5; split; reflexivity| repeat split; intros E; discriminate E]. }
split; [intros E; discriminate E|].
destruct (pagein_skip (pgi_os3 os hdr) hdr) as [[bos segptr] skipped] eqn:ESK. cbn [snd].
set (os3 := pgi_os3 os hdr) in *.
assert (LS : os_lacing_storage (snd (if negb (zlength body - skipped =? 0)
then (0, pagein_segments (pagein_body (body_expand_res os3 (zlength body - skipped)) body skipped (zlength body - skipped)) hdr bos segptr)
else (0, pagein_segments os3 hdr bos segptr))) = os_lacing_storage os3).
{ destruct (negb _); cbn [snd]; rewrite (proj1 (segments_storage _ _ _ _)); [| reflexivity].
unfold pagein_body, set_body, body_expand_res. cbn [os_lacing_storage].
destruct (os_body_fill os3 <? os_body_storage os3 - (zlength body - skipped)); reflexivity. }
assert (BS : os_body_storage (snd (if negb (zlength body - skipped =? 0)
then (0, pagein_segments (pagein_body (body_expand_res os3 (zlength body - skipped)) body skipped (zlength body - skipped)) hdr bos segptr)
else (0, pagein_segments os3 hdr bos segptr)))
= if (zlength body - skipped =? 0) || (os_body_fill os3 <? os_body_storage os3 - (zlength body - skipped)) then os_body_storage os3
else os_body_storage os3 + (zlength body - skipped) + 1024).
{ destruct (zlength body - skipped =? 0); cbn [negb orb snd]; rewrite (proj2 (segments_storage _ _ _ _)); [reflexivity|].
unfold pagein_body, set_body, body_expand_res. cbn [os_body_storage].
destruct (os_body_fill os3 <? os_body_storage os3 - (zlength body - skipped)); reflexivity. }
cbn [snd] in LS, BS |- *.
rewrite LS, BS, L3, B2.
split; [intros _ C; rewrite C; reflexivity|]. split; [intros _ C; rewrite C; reflexivity|].
split; [intros _ C; rewrite C; reflexivity| intros _ C; rewrite C; reflexivity].
Qed.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition os_pure (os : stream_st bptr) : Prop :=
stream_fields_ok os /\ stream_inv os /\ body_inv os /\ lacing_vals_ok (os_lacing os)
/\ length (os_granules os) = length (os_lacing os)
/\ os_body_data os <> None /\ os_lacing_vals os <> None /\ os_granule_vals os <> None
/\ 0 < os_lacing_storage os /\ 0 < os_body_storage os.

Lemma stream_inv_glen : forall os : stream_st bptr, stream_inv os -> length (os_granules os) = length (os_lacing os).
Proof. intros os (_ & _ & C & D & _). unfold zlength in C, D. lia. Qed.

Lemma init_os_pure : forall ser, -2^31 <= ser < 2^31 -> os_pure (init_os (Some tt) (Some tt) (Some tt) ser).
Proof.
intros ser SR. unfold os_pure, init_os.
split; [unfold stream_fields_ok, int31; cbn; lia|].
split; [unfold stream_inv; cbn; rewrite ?zlength_nil; lia|].
split; [apply ogg_stream_init_body_inv|].
split; [constructor|]. split; [reflexivity|].
cbn. split; [discriminate|]. split; [discriminate|]. split; [discriminate|]. lia.
Qed.

Lemma reset_os_pure : forall (os : stream_st bptr) ser, os_pure os -> -2^31 <= ser < 2^31 ->
os_pure (snd (ogg_stream_reset_serialno os ser))
/\ os_lacing_storage (snd (ogg_stream_reset_serialno os ser)) = os_lacing_storage os
/\ os_body_storage (snd (ogg_stream_reset_serialno os ser)) = os_body_storage os
/\ os_lacing_fill (snd (ogg_stream_reset_serialno os ser)) = 0 /\ os_body_fill (snd (ogg_stream_reset_serialno os ser)) = 0
/\ os_lacing_returned (snd (ogg_stream_reset_serialno os ser)) = 0
/\ os_serialno (snd (ogg_stream_reset_serialno os ser)) = ser
/\ os_body (snd (ogg_stream_reset_serialno os ser)) = [] /\ os_lacing (snd (ogg_stream_reset_serialno os ser)) = [].
Proof.
intros os ser (FOK & SINV & BINV & LOK & GL & BD & LV & GV & LS & BS) SR.
unfold ogg_stream_reset_serialno, ogg_stream_check.
destruct (os_body_data os) as [b|] eqn:EB; [| exfalso; exact (BD eq_refl)].
cbn [snd]. unfold ogg_stream_reset. cbn.
pose proof FOK as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12). unfold int31 in *.
split; [| repeat split; reflexivity].
unfold os_pure. cbn.
split; [unfold stream_fields_ok, int31; cbn; lia|].
split; [unfold stream_inv; cbn; rewrite ?zlength_nil; lia|].
split; [unfold body_inv; cbn; rewrite ?zlength_nil; repeat split; try lia; constructor|].
split; [constructor|]. split; [reflexivity|].
rewrite EB. split; [discriminate|]. split; [exact LV|]. split; [exact GV|]. lia.
Qed.

Lemma lor512_lt2048 : forall v, 0 <= v < 2048 -> 0 <= Z.lor v 512 < 2048.
Proof. intros v Hv. apply (lor_small v 512 11); lia. Qed.

Lemma lacing_vals_ok_segments_h : forall (os : stream_st bptr) hdr bos segptr,
bytes_ok (lacing_of hdr) -> lacing_vals_ok (os_lacing os) -> lacing_vals_ok (os_lacing (pagein_segments os hdr bos segptr)).
Proof.
intros os hdr bos segptr Hb H. unfold pagein_segments.
destruct (seg_loop (zdrop segptr (lacing_of hdr)) (negb (bos =? 0)) (os_lacing_fill os) (os_lacing_packet os) (-1))
as [[[[lac gran] f] p] sv] eqn:E.
pose proof (seg_loop_vals512 _ _ _ _ _ _ _ _ _ _ (Forall_zdrop _ segptr _ Hb) E) as L.
assert (A : lacing_vals_ok (os_lacing os ++ lac)).
{ apply Forall_app. split; [exact H|]. eapply Forall_impl; [| exact L]. cbv beta. intros; lia. }
unfold set_lacing, set_tail; cbn.
destruct (negb (ogg_page_eos hdr =? 0)); [| exact A].
destruct (0 <? f); [| exact A].
apply X0af.Forall_zupd; [exact A|]. apply lor512_lt2048. apply (Forall_znth _ _ _ A). lia.
Qed.

Lemma pagein_returned_lacing_returned : forall os : stream_st bptr, os_lacing_returned (pagein_returned os) = 0 \/ pagein_returned os = os /\ os_lacing_returned os = 0.
Proof.
intros os. unfold pagein_returned.
destruct (negb (os_body_returned os =? 0)) eqn:E1; destruct (os_lacing_returned _ =? 0) eqn:E2; cbn [negb];
first [left; reflexivity | apply Z.eqb_eq in E2; first [left; exact E2 | right; split; [reflexivity| exact E2]]].
Qed.

Lemma pagein_res_pure : forall (os : stream_st bptr) (hs : list byte) (body : list Z),
os_pure os -> length hs = (27 + Z.to_nat (znth (ubytes hs) 26))%nat ->
bytes_ok body -> zsum (lacing_of (ubytes hs)) = zlength body ->
os_lacing_fill os <= os_lacing_storage os -> os_body_fill os <= os_body_storage os ->
os_lacing_storage os + os_lacing_fill os + 600 < 2^30 -> os_body_storage os + os_body_fill os + 2 * zlength body + 1024 < 2^62 ->
let os' := snd (pagein_res os (ubytes hs) body) in
os_pure os'
/\ os_lacing_fill os' <= os_lacing_fill os + znth (ubytes hs) 26 + 1
/\ os_body_fill os' <= os_body_fill os + zlength body
/\ os_lacing_storage os' <= Z.max (os_lacing_storage os) (os_lacing_fill os + 2 * (znth (ubytes hs) 26 + 1) + 32)
/\ os_body_storage os' <= Z.max (os_body_storage os) (os_body_fill os + 2 * zlength body + 1024)
/\ os_lacing_storage os <= os_lacing_storage os' /\ os_body_storage os <= os_body_storage os'
/\ os_lacing_fill os' <= os_lacing_storage os' /\ os_body_fill os' <= os_body_storage os'
/\ os_serialno os' = os_serialno os.
Proof.
intros os hs body (FOK & SINV & BINV & LOK & GL & BD & LV & GV & LS & BS) LENH BOK ZSEQ LFS BFS LSB BSB. cbv zeta.
set (hdr := ubytes hs) in *.
assert (H26 : 0 <= znth hdr 26 < 256) by (apply znth_ubytes_range).
assert (HBOK : bytes_ok (lacing_of hdr)) by (apply bytes_ok_zslice; apply ubytes_ok).
assert (ZLL : zlength (lacing_of hdr) = znth hdr 26) by (apply zlength_lacing_of; [exact LENH| exact (proj1 H26)]).
pose proof FOK as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12). unfold int31 in F4, F5, F6, F7.
pose proof SINV as (I1 & I2 & I3 & I4 & I5).
pose proof (body_inv_returned_le_fill os BINV) as BRF.
pose proof (zlength_nonneg body) as ZB.

pose proof (pagein_returned_inv os SINV) as (SINV1 & LR1 & ELV1 & EGV1 & EBD1 & ELS1 & EBS1 & ESN1 & EPN1).
pose proof (pagein_returned_body_inv os SINV BINV) as (BINV1 & BR1 & BFR1 & LF1).
pose proof (fields_ok_returned os FOK SINV BRF) as FOK1.
pose proof (lacing_vals_ok_returned os LOK) as LOK1.
unfold pagein_res. cbv zeta.
set (os1 := pagein_returned os) in *.
pose proof (body_inv_fill_nonneg os1 BINV1) as BF1N.
pose proof SINV1 as (I1a & I2a & I3a & I4a & _).
assert (POS1 : os_pure os1).
{ unfold os_pure. split; [exact FOK1|]. split; [exact SINV1|]. split; [exact BINV1|]. split; [exact LOK1|].
split; [exact (stream_inv_glen os1 SINV1)|]. rewrite ELV1, EGV1, EBD1, ELS1, EBS1. repeat split; assumption. }
assert (FAIL : os_pure os1
/\ os_lacing_fill os1 <= os_lacing_fill os + znth hdr 26 + 1 /\ os_body_fill os1 <= os_body_fill os + zlength body
/\ os_lacing_storage os1 <= Z.max (os_lacing_storage os) (os_lacing_fill os + 2 * (znth hdr 26 + 1) + 32)
/\ os_body_storage os1 <= Z.max (os_body_storage os) (os_body_fill os + 2 * zlength body + 1024)
/\ os_lacing_storage os <= os_lacing_storage os1 /\ os_body_storage os <= os_body_storage os1
/\ os_lacing_fill os1 <= os_lacing_storage os1 /\ os_body_fill os1 <= os_body_storage os1 /\ os_serialno os1 = os_serialno os).
{ rewrite ELS1, EBS1, LF1, BFR1, ESN1. split; [exact POS1|]. repeat split; lia. }
destruct (negb (ogg_page_serialno hdr =? os_serialno os1)); [exact FAIL|].
destruct (0 <? ogg_page_version hdr); [exact FAIL|].
clear FAIL.

set (need := znth hdr 26 + 1) in *.
assert (LFS1 : os_lacing_fill os1 <= os_lacing_storage os1) by (rewrite ELS1, LF1; lia).
pose proof (lacing_expand_res_fields os1 need ltac:(lia) LFS1) as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12).
assert (XLS : os_lacing_storage (lacing_expand_res os1 need) <= Z.max (os_lacing_storage os1) (os_lacing_fill os1 + 2 * need + 32)).
{ unfold lacing_expand_res. destruct (Z.ltb_spec (os_lacing_fill os1) (os_lacing_storage os1 - need)); cbn [set_blocks os_lacing_storage]; lia. }
assert (XV : os_lacing_vals (lacing_expand_res os1 need) <> None /\ os_granule_vals (lacing_expand_res os1 need) <> None
/\ os_serialno (lacing_expand_res os1 need) = os_serialno os1 /\ os_granules (lacing_expand_res os1 need) = os_granules os1
/\ os_header_fill (lacing_expand_res os1 need) = os_header_fill os1).
{ unfold lacing_expand_res. destruct (os_lacing_fill os1 <? os_lacing_storage os1 - need); cbn [set_blocks os_lacing_vals os_granule_vals os_serialno os_granules os_header_fill].
- rewrite ELV1, EGV1. repeat split; first [assumption | reflexivity].
- repeat split; discriminate. }
destruct XV as (XLV & XGV & XSN & XGR & XHF).
assert (SINV2 : stream_inv (lacing_expand_res os1 need)).
{ unfold lacing_expand_res. destruct (_ <? _); [exact SINV1| exact (proj1 (set_blocks_inv _ _ _ _ _ _ SINV1))]. }
assert (BINV2 : body_inv (lacing_expand_res os1 need)).
{ unfold lacing_expand_res. destruct (_ <? _); [exact BINV1| apply set_blocks_body_inv; exact BINV1]. }
assert (FOK2 : stream_fields_ok (lacing_expand_res os1 need)).
{ unfold lacing_expand_res. destruct (Z.ltb_spec (os_lacing_fill os1) (os_lacing_storage os1 - need)); [exact FOK1|].
apply fields_ok_set_blocks; [exact FOK1| rewrite EBS1; lia| unfold int31; rewrite ELS1; lia]. }
assert (LOK2 : lacing_vals_ok (os_lacing (lacing_expand_res os1 need))) by (rewrite X9; exact LOK1).
set (os2 := lacing_expand_res os1 need) in *.

pose proof (pagein_unroll_inv os2 (ogg_page_pageno hdr) SINV2 ltac:(rewrite X8; exact LR1)) as (SINV3 & LR3 & ELV3 & EGV3 & EBD3 & ELS3 & EBS3 & HLF3).
pose proof (pagein_unroll_body_inv os2 (ogg_page_pageno hdr) SINV2 ltac:(rewrite X8; exact LR1) BINV2) as (BINV3 & HBF3 & HBR3).
pose proof (body_inv_fill_nonneg _ BINV3) as BF3N.
pose proof SINV2 as (I1b & I2b & I3b & I4b & _).
assert (FOK3 : stream_fields_ok (pagein_unroll os2 (ogg_page_pageno hdr))) by (apply fields_ok_unroll; [exact FOK2| exact SINV2| lia| rewrite X6, LF1; lia]).
pose proof (lacing_vals_ok_unroll os2 (ogg_page_pageno hdr) LOK2) as LOK3.
assert (ESN3 : os_serialno (pagein_unroll os2 (ogg_page_pageno hdr)) = os_serialno os2).
{ unfold pagein_unroll. destruct (negb _); [| reflexivity]. destruct (negb _); destruct os2; reflexivity. }
assert (E3 : pgi_os3 os hdr = pagein_unroll os2 (ogg_page_pageno hdr)) by reflexivity. rewrite E3. clear E3.
set (os3 := pagein_unroll os2 (ogg_page_pageno hdr)) in *.
pose proof SINV3 as (I1c & I2c & I3c & I4c & _).

pose proof (pagein_skip_sum os3 hdr HBOK) as SKS.
destruct (pagein_skip os3 hdr) as [[bos segptr] skipped] eqn:ESK.
destruct SKS as (SEG & SKE).
pose proof (zsum_split segptr (lacing_of hdr) ltac:(lia)) as ZSP.
pose proof (zsum_bytes_nonneg _ (bytes_ok_ztake segptr _ HBOK)) as ZN1.
pose proof (zsum_bytes_nonneg _ (bytes_ok_zdrop segptr _ HBOK)) as ZN2.
set (bsz := zlength body - skipped) in *.
assert (BSZ : 0 <= bsz <= zlength body) by (unfold bsz; lia).

set (osB := if negb (bsz =? 0) then body_expand_res os3 bsz else os3).
assert (BFS3 : os_body_fill os3 <= os_body_storage os3) by (rewrite EBS3, X4, EBS1; lia).
pose proof (body_expand_res_fields os3 bsz) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8).
pose proof (body_expand_res_room os3 bsz ltac:(lia) BFS3) as (YR1 & YR2).
assert (YBS : os_body_storage (body_expand_res os3 bsz) <= Z.max (os_body_storage os3) (os_body_fill os3 + 2 * bsz + 1024)).
{ unfold body_expand_res. destruct (Z.ltb_spec (os_body_fill os3) (os_body_storage os3 - bsz)); cbn [set_blocks os_body_storage]; lia. }
assert (YV : os_body_data (body_expand_res os3 bsz) <> None /\ os_lacing_vals (body_expand_res os3 bsz) = os_lacing_vals os3
/\ os_granule_vals (body_expand_res os3 bsz) = os_granule_vals os3 /\ os_serialno (body_expand_res os3 bsz) = os_serialno os3
/\ os_granules (body_expand_res os3 bsz) = os_granules os3).
{ unfold body_expand_res. destruct (os_body_fill os3 <? os_body_storage os3 - bsz); cbn [set_blocks os_body_data os_lacing_vals os_granule_vals os_serialno os_granules].
- rewrite EBD3, X5, EBD1. repeat split; [exact BD| reflexivity ..].
- repeat split; [discriminate| reflexivity ..]. }
destruct YV as (YBD & YLV & YGV & YSN & YGR).
assert (EBD3' : os_body_data os3 <> None) by (rewrite EBD3, X5, EBD1; exact BD).
assert (PB : stream_inv osB /\ os_lacing_returned osB = 0 /\ body_inv osB /\ stream_fields_ok osB /\ lacing_vals_ok (os_lacing osB)
/\ os_lacing osB = os_lacing os3 /\ os_lacing_fill osB = os_lacing_fill os3 /\ os_lacing_packet osB = os_lacing_packet os3
/\ os_lacing_storage osB = os_lacing_storage os3 /\ os_body_fill osB = os_body_fill os3
/\ os_body_data osB <> None /\ os_lacing_vals osB = os_lacing_vals os3 /\ os_granule_vals osB = os_granule_vals os3
/\ os_serialno osB = os_serialno os3
/\ os_body_storage os3 <= os_body_storage osB <= Z.max (os_body_storage os3) (os_body_fill os3 + 2 * bsz + 1024)
/\ os_body_fill osB + bsz <= os_body_storage osB).
{ unfold osB. destruct (Z.eqb_spec bsz 0) as [BZ|BNZ]; cbn [negb].
- split; [exact SINV3|]. split; [exact LR3|]. split; [exact BINV3|]. split; [exact FOK3|]. split; [exact LOK3|].
do 9 (split; [first [reflexivity | exact EBD3']|]). split; [lia|]. rewrite BZ. lia.
- assert (S4 : stream_inv (body_expand_res os3 bsz) /\ os_lacing_returned (body_expand_res os3 bsz) = os_lacing_returned os3).
{ unfold body_expand_res. destruct (_ <? _); [split; [exact SINV3| reflexivity]| exact (set_blocks_inv _ _ _ _ _ _ SINV3)]. }
split; [exact (proj1 S4)|]. split; [rewrite (proj2 S4); exact LR3|].
split; [unfold body_expand_res; destruct (_ <? _); [exact BINV3| apply set_blocks_body_inv; exact BINV3]|].
split.
{ unfold body_expand_res. destruct (Z.ltb_spec (os_body_fill os3) (os_body_storage os3 - bsz)); [exact FOK3|].
apply fields_ok_set_blocks; [exact FOK3| rewrite EBS3, X4, EBS1; lia| pose proof FOK3 as (_ & _ & _ & Z4 & _); exact Z4]. }
split; [rewrite Y8; exact LOK3|].
split; [exact Y8|]. split; [exact Y5|]. split; [exact Y6|]. split; [exact Y4|]. split; [exact Y2|].
split; [exact YBD|]. split; [exact YLV|]. split; [exact YGV|]. split; [exact YSN|]. split; [lia|]. rewrite Y2. lia. }
destruct PB as (SINVB & LRB & BINVB & FOKB & LOKB & ELB & ELFB & ELPB & ELSB & EBFB & EBDB & ELVB & EGVB & ESNB & (BSB1 & BSB2) & BROOM).
pose proof SINVB as (I1d & I2d & I3d & I4d & _).

assert (ERES : (if negb (bsz =? 0) then (0, pagein_segments (pagein_body (body_expand_res os3 bsz) body skipped bsz) hdr bos segptr)
else (0, pagein_segments os3 hdr bos segptr))
= (0, pagein_segments (if negb (bsz =? 0) then pagein_body osB body skipped bsz else osB) hdr bos segptr)).
{ unfold osB. destruct (negb (bsz =? 0)); reflexivity. }
rewrite ERES. cbn [snd]. clear ERES.
pose proof (pagein_body_segments_body_inv osB hdr body bos segptr skipped SINVB LRB BINVB HBOK ZSEQ SEG SKE) as PBS.
cbv zeta in PBS. fold bsz in PBS. destruct PBS as (BINV5 & BF5 & _ & BR5).
set (os4 := if negb (bsz =? 0) then pagein_body osB body skipped bsz else osB) in *.
assert (P4 : stream_inv os4 /\ os_lacing_returned os4 = 0 /\ stream_fields_ok os4 /\ lacing_vals_ok (os_lacing os4)
/\ os_lacing_fill os4 = os_lacing_fill os3 /\ os_lacing_packet os4 = os_lacing_packet os3 /\ os_lacing_storage os4 = os_lacing_storage os3
/\ os_body_storage os4 = os_body_storage osB /\ os_body_data os4 <> None /\ os_lacing_vals os4 = os_lacing_vals os3
/\ os_granule_vals os4 = os_granule_vals os3 /\ os_serialno os4 = os_serialno os3).
{ unfold os4. destruct (Z.eqb_spec bsz 0) as [BZ|BNZ]; cbn [negb].
- split; [exact SINVB|]. split; [exact LRB|]. split; [exact FOKB|]. split; [exact LOKB|]. repeat split; assumption.
- pose proof (pagein_body_inv osB body skipped bsz SINVB) as (S5 & R5).
split; [exact S5|]. split; [rewrite R5; exact LRB|]. split; [apply fields_ok_body; [exact FOKB| lia]|].
unfold pagein_body, set_body. cbn [os_lacing os_lacing_fill os_lacing_packet os_lacing_storage os_body_storage os_body_data os_lacing_vals os_granule_vals os_serialno].
split; [exact LOKB|]. repeat split; assumption. }
destruct P4 as (SINV4 & LR4 & FOK4 & LOK4 & ELF4 & ELP4 & ELS4 & EBS4 & EBD4 & ELV4 & EGV4 & ESN4).
pose proof SINV4 as (I1e & I2e & I3e & I4e & _).
assert (PN : 0 <= ogg_page_pageno hdr < 2^32) by (apply pageno_range; lia).
pose proof (segments_shape os4 hdr bos segptr HBOK SEG ltac:(lia)) as SH. cbv zeta in SH.
destruct SH as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13 & Q14 & Q15 & Q16 & Q17).
assert (SINV6 : stream_inv (pagein_segments os4 hdr bos segptr)) by (apply pagein_segments_inv; [exact SINV4| exact LR4| exact HBOK| lia]).
assert (FOK6 : stream_fields_ok (pagein_segments os4 hdr bos segptr)).
{ apply fields_ok_segments; [exact FOK4| exact HBOK| exact SEG| lia| rewrite ELF4, ZLL; fold os2 in HLF3; rewrite X6, LF1 in HLF3; lia| exact PN]. }
pose proof (lacing_vals_ok_segments_h os4 hdr bos segptr HBOK LOK4) as LOK6.

fold os2 in HLF3. rewrite X6, LF1 in HLF3.
assert (ELS3' : os_lacing_storage os3 = os_lacing_storage os2) by exact ELS3.
assert (EBS3' : os_body_storage os3 = os_body_storage os) by (rewrite EBS3; fold os2; rewrite X4, EBS1; reflexivity).
assert (EBF3 : os_body_fill os3 <= os_body_fill os) by (fold os2 in HBF3; rewrite X2, BFR1 in HBF3; lia).
unfold os_pure. rewrite Q1, Q2, Q3, Q4, Q5, Q6, Q12, Q16.
split.
{ split; [exact FOK6|]. split; [exact SINV6|]. split; [exact BINV5|]. split; [exact LOK6|].
split; [exact (stream_inv_glen _ SINV6)|].
split; [exact EBD4|]. split; [rewrite ELV4, ELV3; exact XLV|]. split; [rewrite EGV4, EGV3; exact XGV|].
split; [rewrite ELS4, ELS3'; lia| rewrite EBS4; lia]. }
rewrite ELF4, ELS4, ELS3', EBS4, ESN4, ESN3, XSN, ESN1. rewrite ZLL. fold os2.
rewrite Q6 in BF5. rewrite BF5, EBFB.
split; [lia|]. split; [lia|]. split; [rewrite ELS1, LF1 in XLS; lia|]. split; [rewrite EBS3' in BSB2; lia|].
split; [rewrite ELS1 in X11; lia|]. split; [rewrite EBS3' in BSB1; lia|].
split; [rewrite LF1 in X12; lia|]. split; [lia| reflexivity].
Qed.

Lemma segments_storage : forall (os : stream_st bptr) hdr bos segptr,
os_lacing_storage (pagein_segments os hdr bos segptr) = os_lacing_storage os /\ os_body_storage (pagein_segments os hdr bos segptr) = os_body_storage os.
Proof. intros. unfold pagein_segments. destruct (seg_loop _ _ _ _ _) as [[[[? ?] ?] ?] ?]. split; reflexivity. Qed.
Lemma unroll_lacing_storage : forall (os : stream_st bptr) pn, os_lacing_storage (pagein_unroll os pn) = os_lacing_storage os.
Proof. intros os pn. unfold pagein_unroll. destruct (negb (pn =? os_pageno os)); [| reflexivity]. destruct (negb (os_pageno _ =? -1)); reflexivity. Qed.

Lemma pagein_res_store : forall (os : stream_st bptr) (hdr body : list Z),
let os' := snd (pagein_res os hdr body) in
let os1 := pagein_returned os in
let need := znth hdr 26 + 1 in
let os3 := pgi_os3 os hdr in
let bsz := zlength body - snd (pagein_skip os3 hdr) in
(pgi_ok os hdr = false -> os_lacing_storage os' = os_lacing_storage os /\ os_body_storage os' = os_body_storage os)
/\ (pgi_ok os hdr = true -> (os_lacing_fill os1 <? os_lacing_storage os1 - need) = true -> os_lacing_storage os' = os_lacing_storage os)
/\ (pgi_ok os hdr = true -> (os_lacing_fill os1 <? os_lacing_storage os1 - need) = false -> os_lacing_storage os' = os_lacing_storage os + need + 32)
/\ (pgi_ok os hdr = true -> ((bsz =? 0) || (os_body_fill os3 <? os_body_storage os3 - bsz)) = true -> os_body_storage os' = os_body_storage os)
/\ (pgi_ok os hdr = true -> ((bsz =? 0) || (os_body_fill os3 <? os_body_storage os3 - bsz)) = false -> os_body_storage os' = os_body_storage os + bsz + 1024).
Proof.
intros os hdr body. cbv zeta.
pose proof (pagein_returned_fields os) as (E1 & E2 & E3 & E4 & E5).
pose proof (pgi_os3_body os hdr) as (B1 & B2).
assert (L3 : os_lacing_storage (pgi_os3 os hdr)
= if os_lacing_fill (pagein_returned os) <? os_lacing_storage (pagein_returned os) - (znth hdr 26 + 1) then os_lacing_storage os
else os_lacing_storage os + (znth hdr 26 + 1) + 32).
{ unfold pgi_os3, pgi_os2. rewrite unroll_lacing_storage. unfold lacing_expand_res.
destruct (_ <? _); cbn [set_blocks os_lacing_storage]; rewrite E4; reflexivity. }
unfold pagein_res, pgi_ok. cbv zeta.
destruct (ogg_page_serialno hdr =? os_serialno (pagein_returned os)) eqn:ES; cbn [negb andb].
2:{ split; [intros _; cbn [snd]; rewrite E4, E5; split; reflexivity| repeat split; intros E; discriminate E]. }
destruct (0 <? ogg_page_version hdr) eqn:EV; cbn [negb].
{ split; [intros _; cbn [snd]; rewrite E4, E5; split; reflexivity| repeat split; intros E; discriminate E]. }
split; [intros E; discriminate E|].
destruct (pagein_skip (pgi_os3 os hdr) hdr) as [[bos segptr] skipped] eqn:ESK. cbn [snd].
set (os3 := pgi_os3 os hdr) in *.
assert (LS : os_lacing_storage (snd (if negb (zlength body - skipped =? 0)
then (0, pagein_segments (pagein_body (body_expand_res os3 (zlength body - skipped)) body skipped (zlength body - skipped)) hdr bos segptr)
else (0, pagein_segments os3 hdr bos segptr))) = os_lacing_storage os3).
{ destruct (negb _); cbn [snd]; rewrite (proj1 (segments_storage _ _ _ _)); [| reflexivity].
unfold pagein_body, set_body, body_expand_res. cbn [os_lacing_storage].
destruct (os_body_fill os3 <? os_body_storage os3 - (zlength body - skipped)); reflexivity. }
assert (BS : os_body_storage (snd (if negb (zlength body - skipped =? 0)
then (0, pagein_segments (pagein_body (body_expand_res os3 (zlength body - skipped)) body skipped (zlength body - skipped)) hdr bos segptr)
else (0, pagein_segments os3 hdr bos segptr)))
= if (zlength body - skipped =? 0) || (os_body_fill os3 <? os_body_storage os3 - (zlength body - skipped)) then os_body_storage os3
else os_body_storage os3 + (zlength body - skipped) + 1024).
{ destruct (zlength body - skipped =? 0); cbn [negb orb snd]; rewrite (proj2 (segments_storage _ _ _ _)); [reflexivity|].
unfold pagein_body, set_body, body_expand_res. cbn [os_body_storage].
destruct (os_body_fill os3 <? os_body_storage os3 - (zlength body - skipped)); reflexivity. }
cbn [snd] in LS, BS |- *.
rewrite LS, BS, L3, B2.
split; [intros _ C; rewrite C; reflexivity|]. split; [intros _ C; rewrite C; reflexivity|].
split; [intros _ C; rewrite C; reflexivity| intros _ C; rewrite C; reflexivity].
Qed.
