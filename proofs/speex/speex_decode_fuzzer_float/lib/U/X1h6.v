(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bu X1cf X1cc X1bs X1c2 X1bn X1bj X1bk X1bq X1br X1c0.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0px X0qn X0qc X0qp X0qb X0pt.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1m2 X1m3 X1m5 X1fl X1ea X1fr X1h7 X1kd X1k9.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ik X1ij X1ii X1il.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1g3 X1g1 X1g6 X1g5.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1go X1hk. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1hl. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1gy X1hg X1hh X1hi X1gz X1gt.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1ra X1qu X1qx X1ri X1r3 X1r4 X1r6 X1qz X1r0 X1r1 X1nt X1rg X1rh X1re X1od.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation cleanupP := (cleanup raw_free (St:=PState)).
Notation h_decoder_initP := (h_decoder_init raw_calloc raw_free (St:=PState)).
Notation h_decoder_destroyP := (h_decoder_destroy raw_free (St:=PState)).

Definition ph_after_init (h : hstate bptr) (blk : bptr) (hd : spx_header) (st0 : dec_state bptr) : M PState (option (hstate bptr)) :=
let '(_, st) := speex_decoder_ctl st0 (CtlSetEnh 1) in
let '(frame_size, st) := speex_decoder_ctl st CtlGetFrameSize in
if (frame_size <? 0) || (2 * 320 <? frame_size) then X1qx.mbind (h_decoder_destroyP st) (fun _ => X1qx.mbind (raw_free blk) (fun _ => X1qx.mret None)) else
let rate := if h_rate h =? 0 then hd_rate hd else h_rate h in
let '(_, st) := speex_decoder_ctl st (CtlSetSamplingRate rate) in
if (hd_frames_per_packet hd <? 1) || (10 <? hd_frames_per_packet hd)
then X1qx.mbind (h_decoder_destroyP st) (fun _ => X1qx.mbind (raw_free blk) (fun _ => X1qx.mret None)) else
let nframes := hd_frames_per_packet hd in
let channels := if h_channels h =? -1 then hd_nb_channels hd else h_channels h in
let '(channels, st) := (if negb (channels =? 1)
then let '(_, st) := speex_decoder_ctl st CtlSetHandlerStereo in (2, st)
else (channels, st)) in
if INT_MAX - 1 <? hd_extra_headers hd then X1qx.mbind (h_decoder_destroyP st) (fun _ => X1qx.mbind (raw_free blk) (fun _ => X1qx.mret None)) else
let extra := hd_extra_headers hd in
X1qx.mbind (raw_free blk) (fun _ =>
let '(lookahead, st) := speex_decoder_ctl st CtlGetLookahead in
X1qx.mret (Some (set_header h st nframes channels rate extra frame_size))).

Definition ph_after_p2h (h : hstate bptr) (blk : bptr) (hd : spx_header) : M PState (option (hstate bptr)) :=
if (SPEEX_NB_MODES <=? hd_mode hd) || (hd_mode hd <? 0) then X1qx.mbind (raw_free blk) (fun _ => X1qx.mret None) else
let modeID := hd_mode hd in
match speex_lib_get_mode modeID with
| None => X1qx.munr
| Some mode =>
if 1 <? hd_speex_version_id hd then X1qx.mbind (raw_free blk) (fun _ => X1qx.mret None) else
if mode_bitstream_version mode <? hd_mode_bitstream_version hd then X1qx.mbind (raw_free blk) (fun _ => X1qx.mret None) else
if hd_mode_bitstream_version hd <? mode_bitstream_version mode then X1qx.mbind (raw_free blk) (fun _ => X1qx.mret None) else
X1qx.mbind (h_decoder_initP mode) (fun ost =>
match ost with
| None => X1qx.mbind (raw_free blk) (fun _ => X1qx.mret None)
| Some st => ph_after_init h blk hd st
end) end.

Lemma process_header_eq : forall (h : hstate bptr) pdata bytes,
process_header raw_calloc raw_free io_notify h pdata bytes
= X1qx.mbind (speex_packet_to_header raw_calloc raw_free io_notify pdata bytes)
(fun r => match r with None => X1qx.mret None | Some (blk, hd) => ph_after_p2h h blk hd end).
Proof. intros. reflexivity. Qed.

Definition hdr_tailK (fuel' : nat) (h : hstate bptr) (pn : Z) (ph : option (hstate bptr)) : M PState (outcome bptr) :=
X1qx.mbind (match ph with
| None => X1qx.mbind (cleanupP h) (fun _ => X1qx.mret None)
| Some h' => X1qx.mret (Some (h', pn))
end)
(fun ro => match ro with
| None => X1qx.mret Returned
| Some (h2, pn2) => packet_loopP fuel' (incr_packet_count h2) pn2
end).

Definition hglobX {RCEIL : RunCeiling} (c : hcx) (x : hax) (h : hstate bptr) (st : PState) (m : mem) (extra : list block) : Prop :=
RHEAP st (extra ++ a_LB x) m /\ Permutation (a_LB x) (owned x h ++ x_LB0 c)
/\ bytes_at rsegs m (x_P c) (to_bytes (x_payload c)) /\ rtables_pristine m /\ stderr_wfile m
/\ (exists errv : word, rw_cells rsegs m RERRNO [C4 errv]) /\ rauxv_ok m (x_AB c) /\ mem_inv rsegs m /\ stk rsegs m (x_lo c) (hsp c)
/\ pres_except rsegs (rclient_addr (x_LB0 c) (usp c)) rharness_X (x_m0 c) m /\ ps_so st = ps_so (x_st0 c).

Lemma hglobX_nil {RCEIL : RunCeiling} : forall c x h st m, hglobX c x h st m [] <-> hglob c x h st m.
Proof. intros. split; intros H; exact H. Qed.

Lemma hglobX_agree2 {RCEIL : RunCeiling} : rheap_block_range_stmt -> forall (c : hcx) x h st st' m m' extra extra' (P : Z -> Prop) errv',
hcx_ok c -> hglobX c x h st m extra -> agree_on rsegs P m m' ->
RHEAP st' (extra' ++ a_LB x) m' -> mem_inv rsegs m' -> stk rsegs m' (x_lo c) (hsp c) -> stderr_wfile m' ->
rw_cells rsegs m' RERRNO [C4 errv'] -> rauxv_ok m' (x_AB c) -> ps_so st' = ps_so st ->
(forall a, hclient_caller_addr c a -> P a) ->
hglobX c x h st' m' extra'.
Proof.
intros RBR c x h st st' m m' extra extra' P errv' CX HG AG HP1 MI1 ST1 SEW1 ERR1 AUX1 SO1 PC.
pose proof CX as sfP_; first [ sf_destruct 11%nat sfP_ as PF P0 P16 PL PIN SPAB ABB CEIL LO SP16 SPB | sf_fb; destruct sfP_ as (PF & P0 & P16 & PL & PIN & SPAB & ABB & CEIL & LO & SP16 & SPB) ].
pose proof HG as sfP_; first [ sf_destruct 11%nat sfP_ as HP PERM PAY TP SEW (errv & ERR) AUX MI ST PE SO | sf_fb; destruct sfP_ as (HP & PERM & PAY & TP & SEW & (errv & ERR) & AUX & MI & ST & PE & SO) ].
assert (HL0 : forall b, In b (x_LB0 c) -> In b (extra ++ a_LB x)).
{ intros b Hb. apply in_app_iff. right. eapply Permutation_in; [apply Permutation_sym; exact PERM|]. apply in_app_iff. right. exact Hb. }
split; [exact HP1|]. split; [exact PERM|].
split. { eapply (pay_keep c _ _ _ CX AG PAY). intros NE IN a Ha. apply PC. right; right. exists (x_pb c, x_P c, zlength (x_payload c)). split; [exact IN| cbn; lia]. }
split. { eapply rtables_pristine_agree; [exact AG| | exact TP]. intros a Ha. apply PC. right; left.
unfold RTABLES_LO, RTABLES_HI, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in *. lia. }
split; [exact SEW1|]. split; [exists errv'; exact ERR1|]. split; [exact AUX1|].
split; [exact MI1|]. split; [exact ST1|].
split. { eapply (pres_except_step RBR c _ _ _ _ _ _ CX HP); [exact HL0| exact PE| exact AG|].
intros a Hc Hout Hx. apply PC. destruct Hc as [Hc|[Hc|(bb & Hbb & Rbb)]].
- left. exact Hc.
- right; left. split; [lia|]. split; [tauto|]. intros Hs. apply Hx. cbn. left. cbn. exact Hs.
- right; right. exists bb. split; [exact Hbb| exact Rbb]. }
rewrite SO1. exact SO.
Qed.

Definition xfoot_ok (c : hcx) (extra : list block) (iv : Z * Z) : Prop :=
(x_lo c <= fst iv /\ snd iv <= usp c)
\/ (exists b, In b extra /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b).

Lemma xoutside_of_foot {RCEIL : RunCeiling} : forall (c : hcx) extra W a,
Forall (xfoot_ok c extra) W ->
(forall b bb, In b extra -> In bb (x_LB0 c) ->
blk_addr b + blk_size b <= blk_addr bb \/ blk_addr bb + blk_size bb <= blk_addr b) ->
(forall b, In b extra -> rblock_range (blk_addr b) (blk_size b)) ->
(forall b, In b (x_LB0 c) -> rblock_range (blk_addr b) (blk_size b)) ->
alloc_ceiling <= x_lo c <= usp c ->
hclient_caller_addr c a -> outside W a.
Proof.
intros c extra W a FW DJ RO R0 XLO Ha. unfold alloc_ceiling in XLO.
induction W as [|[lo hi] W IH]; [exact I|].
inversion FW as [|iv W' F1 F2]; subst. split; [| apply IH; exact F2].
unfold xfoot_ok in F1. cbn [fst snd] in F1. unfold rblock_range, alloc_ceiling in RO, R0.
destruct F1 as [K|(b & Hb & K1 & K2)].
- destruct Ha as [Ha|[(Ha & _ & _)|(bb & Hbb & Rbb)]]; [lia| lia|]. pose proof (R0 bb Hbb). lia.
- destruct Ha as [Ha|[(Ha & _ & _)|(bb & Hbb & Rbb)]].
+ pose proof (RO b Hb). lia.
+ pose proof (RO b Hb). lia.
+ pose proof (DJ b bb Hb Hbb). lia.
Qed.

Lemma hglobX_munch {RCEIL : RunCeiling} : rheap_frame_stmt -> rheap_block_range_stmt -> rheap_blocks_nodup_stmt -> rheap_blocks_disjoint_stmt ->
forall (c : hcx) x h st m m' extra W,
hcx_ok c -> hglobX c x h st m extra -> munch W m m' -> wmono rsegs m m' ->
mem_inv rsegs m' -> stk rsegs m' (x_lo c) (hsp c) ->
Forall (xfoot_ok c extra) W ->
hglobX c x h st m' extra /\ agree_on rsegs (fun a => outside W a) m m'.
Proof.
intros RHF RBR RND RBD c x h st m m' extra W CX HG MU WM MI1 ST1 FW.
pose proof CX as sfP_; first [ sf_destruct 11%nat sfP_ as PF P0 P16 PL PIN SPAB ABB CEIL LO SP16 SPB | sf_fb; destruct sfP_ as (PF & P0 & P16 & PL & PIN & SPAB & ABB & CEIL & LO & SP16 & SPB) ]. unfold RFUZZ_STACK in LO.
pose proof CEIL as CEIL'. unfold alloc_ceiling in CEIL'.
pose proof HG as sfP_; first [ sf_destruct 11%nat sfP_ as HP PERM PAY TP SEW (errv & ERR) AUX MI ST PE SO | sf_fb; destruct sfP_ as (HP & PERM & PAY & TP & SEW & (errv & ERR) & AUX & MI & ST & PE & SO) ].
pose proof (agree_on_of_munch _ _ _ MU WM) as AG.
assert (HL0 : forall b, In b (x_LB0 c) -> In b (extra ++ a_LB x)).
{ intros b Hb. apply in_app_iff. right. eapply Permutation_in; [apply Permutation_sym; exact PERM|]. apply in_app_iff. right. exact Hb. }
assert (HLe : forall b, In b extra -> In b (extra ++ a_LB x)) by (intros b Hb; apply in_app_iff; left; exact Hb).
pose proof (RND _ _ _ HP) as ND.
assert (HP1 : RHEAP st (extra ++ a_LB x) m').
{ eapply RHF; [exact HP| exact MU| exact WM|]. eapply Forall_impl; [| exact FW].
intros [lo hi] [K|(b & Hb & K1 & K2)]; cbn [fst snd] in *.
- left. cbn. lia.
- right; right. exists b. split; [apply HLe; exact Hb| cbn; lia]. }
assert (OUTS : forall a, hclient_caller_addr c a -> outside W a).
{ intros a Ha. apply (xoutside_of_foot c extra W a FW); [| | | lia| exact Ha].
- intros b bb Hb Hbb. eapply (RBD _ _ _ _ _ HP); [apply HLe; exact Hb| apply HL0; exact Hbb|].
intros E. rewrite map_app in ND. eapply (nodup_app_disj _ _ (blk_id b) ND); [apply in_map; exact Hb|].
rewrite E. apply in_map. eapply Permutation_in; [apply Permutation_sym; exact PERM|]. apply in_app_iff. right. exact Hbb.
- intros b Hb. apply (RBR _ _ _ _ HP). apply HLe. exact Hb.
- intros b Hb. apply (RBR _ _ _ _ HP). apply HL0. exact Hb. }

assert (OUTST : forall a, 0x10000 <= a < 0x6e000 -> outside W a).
{ intros a Ha. clear -FW Ha HP HLe RBR CEIL'. induction W as [|[lo hi] W IH]; [exact I|].
inversion FW as [|iv W' F1 F2]; subst. split; [| apply IH; exact F2].
unfold xfoot_ok in F1. cbn [fst snd] in F1. destruct F1 as [K|(b & Hb & K1 & K2)]; [lia|].
pose proof (RBR _ _ _ _ HP (HLe b Hb)) as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ _ B4 B5 | sf_fb; destruct sfP_ as (_ & _ & _ & B4 & B5) ]. unfold alloc_ceiling in B4. lia. }
split; [| exact AG].
assert (SEW1 : stderr_wfile m').
{ eapply stderr_wfile_agree; [exact AG| | exact SEW]. intros a Ha. apply OUTST. unfold stderr_addr in Ha. lia. }
eapply (hglobX_agree2 RBR c x h st st m m' extra extra _ errv CX HG AG HP1 MI1 ST1 SEW1); [| | reflexivity| exact OUTS].
- eapply rw_cells_agree; [exact AG| exact ERR|]. intros a Ha. apply OUTST. cbn in Ha. unfold RERRNO in Ha. lia.
- eapply rauxv_ok_agree; [exact AG| exact AUX| |]; intros a Ha; [apply OUTST; unfold RAUXV_CELL in Ha; lia| apply OUTS; left; lia].
Qed.

Definition hdr_pure {RCEIL : RunCeiling} (c : hcx) (x : hax) (h : hstate bptr) (nbr brem0 : Z) : Prop :=
h_stream_init h = 1 /\ h_eos h = 0 /\ h_packet_count h = 0 /\ h_st h = None
/\ a_S x = 0 /\ a_LBD x = []
/\ hpure c x h /\ low_ok h nbr brem0
/\ 1 + (os_lacing_fill (h_os h) - os_lacing_returned (h_os h)) <= 162 * hconsumed c h.

Definition hdr_blk {RCEIL : RunCeiling} (m : mem) (HB : Z) (hd : spx_header) : Prop :=
(exists junk28 w1 w2 w3 r1 r2, rw_cells rsegs m HB (spx_header_cells junk28 hd w1 w2 w3 r1 r2))
/\ rblock_range HB SIZEOF_SPEEX_HEADER_Z
/\ -2^31 <= hd_speex_version_id hd < 2^31 /\ -2^31 <= hd_rate hd < 2^31 /\ 0 <= hd_mode hd < SPEEX_NB_MODES
/\ -2^31 <= hd_mode_bitstream_version hd < 2^31 /\ -2^31 <= hd_nb_channels hd < 2^31
/\ -2^31 <= hd_frames_per_packet hd < 2^31 /\ -2^31 <= hd_extra_headers hd < 2^31.

Definition hdr_frame {RCEIL : RunCeiling} (c : hcx) (x : hax) (h : hstate bptr) (m : mem) (nbr brem0 : Z) : Prop :=
(exists j16 jsk lk, rw_cells rsegs m (aLOW c) (low_cells c h j16 (C8 (wz nbr)) (C8 (wz brem0)) jsk lk) /\ lk_ok h lk)
/\ (exists stb, rw_cells rsegs m (aSTEREO c) [CB 24 stb])
/\ stream_rep m c x h
/\ (exists opj, rw_cells rsegs m (aOP c) [CB 48 opj]) /\ (exists ogj, rw_cells rsegs m (aOG c) [CB 32 ogj])
/\ sync_rep m (aOY c) (a_D x) (h_oy h) (a_sybytes x)
/\ bits_rep rsegs m (aBITS c) (a_Dc x) (h_bits h)
/\ (exists pad, rw_cells rsegs m (aFSZ c) (fsz_cells h pad))
/\ (exists outb, u8arr rsegs m (aOUT c) outb /\ Z.of_nat (length outb) = 8000)
/\ (exists cbj, rw_cells rsegs m (aCBK c) [CB 44 cbj; C4 (wz 1)])
/\ rw_cells rsegs m (aSAV c) (sav_cells c).

Definition HM {RCEIL : RunCeiling} (c : hcx) (h : hstate bptr) (blk : bptr) (hd : spx_header) (st : PState) (ms : machine_state) : Prop :=
exists (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
(x : hax) (nbr brem0 HB pno : Z) (s0w s3w s8w : word),
ms = MS (hregs c h (a_S x) s0w (wz pno) s3w (wz 2147483647) s8w (wz (h_speex_serialno h))
x1 t0 t1 t2 (wz HB) a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6)
F (wz 0x1c580) fc None m (seg_rom rsegs)
/\ frm0 fc /\ hdr_pure c x h nbr brem0 /\ hdr_frame c x h m nbr brem0
/\ hglobX c x h st m [(blk, HB, SIZEOF_SPEEX_HEADER_Z)]
/\ hdr_blk m HB hd /\ 0 <= pno <= h_packet_count h.

Definition HS {RCEIL : RunCeiling} (dec_rep : Z -> mem -> Z -> dec_state bptr -> list block -> Prop)
(c : hcx) (h : hstate bptr) (blk : bptr) (hd : spx_header) (d : dec_state bptr) (st : PState) (ms : machine_state) : Prop :=
exists (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
(x : hax) (nbr brem0 HB S pno : Z) (LBD : list block) (s0w s3w s8w : word),
ms = MS (mkR x1 (wz (hsp c)) (x_gp c) (wz RATP) t0 t1 t2 s0w (wz pno) (wz S) a1 a2 a3 a4 a5 a6 a7
(wz (a_S x)) s3w (wz (h_extra_headers h)) (wz 2147483647) (wz HB) (wz (h_packet_count h)) s8w (wz (h_nframes h))
(wz (h_speex_serialno h)) (wz (h_channels h)) t3 t4 t5 t6)
F (wz 0x1c5d8) fc None m (seg_rom rsegs)
/\ frm0 fc /\ hdr_pure c x h nbr brem0 /\ hdr_frame c x h m nbr brem0
/\ hglobX c x h st m (LBD ++ [(blk, HB, SIZEOF_SPEEX_HEADER_Z)])
/\ hdr_blk m HB hd /\ 0 <= pno <= h_packet_count h
/\ 0 < S < 2^63 /\ (forall STEREO, dec_rep STEREO m S d LBD) /\ (forall b, In b LBD -> rblock_range (blk_addr b) (blk_size b)).

Definition hdr_junkframe {RCEIL : RunCeiling} (c : hcx) (x : hax) (h : hstate bptr) (m : mem) : Prop :=
stream_rep m c x h /\ sync_rep m (aOY c) (a_D x) (h_oy h) (a_sybytes x) /\ bits_rep rsegs m (aBITS c) (a_Dc x) (h_bits h)
/\ cl_junk c m /\ rw_cells rsegs m (aSAV c) (sav_cells c).

Definition F294 {RCEIL : RunCeiling} (c : hcx) (h : hstate bptr) (blk : bptr) (st : PState) (ms : machine_state) : Prop :=
exists (x1 t0 t1 t2 q8 q9 a0 a1 a2 a3 a4 a5 a6 a7 q18 q19 q20 q21 q23 q24 q25 q26 q27 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
(x : hax) (nbr brem0 HB : Z),
ms = MS (mkR x1 (wz (hsp c)) (x_gp c) (wz RATP) t0 t1 t2 q8 q9 a0 a1 a2 a3 a4 a5 a6 a7 q18 q19 q20 q21 (wz HB) q23 q24 q25 q26 q27 t3 t4 t5 t6)
F (wz 0x1c754) fc None m (seg_rom rsegs)
/\ frm0 fc /\ hdr_pure c x h nbr brem0 /\ hdr_junkframe c x h m
/\ hglobX c x h st m [(blk, HB, SIZEOF_SPEEX_HEADER_Z)].

Definition F28c {RCEIL : RunCeiling} (dec_rep : Z -> mem -> Z -> dec_state bptr -> list block -> Prop)
(c : hcx) (h : hstate bptr) (blk : bptr) (d : dec_state bptr) (st : PState) (ms : machine_state) : Prop :=
exists (x1 t0 t1 t2 q8 q9 a0 a1 a2 a3 a4 a5 a6 a7 q19 q20 q21 q23 q24 q25 q26 q27 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
(x : hax) (nbr brem0 HB S : Z) (LBD : list block),
ms = MS (mkR x1 (wz (hsp c)) (x_gp c) (wz RATP) t0 t1 t2 q8 q9 a0 a1 a2 a3 a4 a5 a6 a7 (wz S) q19 q20 q21 (wz HB) q23 q24 q25 q26 q27 t3 t4 t5 t6)
F (wz 0x1c74c) fc None m (seg_rom rsegs)
/\ frm0 fc /\ hdr_pure c x h nbr brem0 /\ hdr_junkframe c x h m
/\ hglobX c x h st m (LBD ++ [(blk, HB, SIZEOF_SPEEX_HEADER_Z)])
/\ 0 < S /\ dec_rep (aSTEREO c) m S d LBD /\ (forall b, In b LBD -> rblock_range (blk_addr b) (blk_size b)).

Lemma hdr_frame_junk {RCEIL : RunCeiling} : forall c x h m nbr brem0, hdr_frame c x h m nbr brem0 -> hdr_junkframe c x h m.
Proof.
intros c x h m nbr brem0 sfH_; first [ sf_destruct 11%nat sfH_ as (j16 & jsk & lk & LOW & _) (stb & STB) OSP (opj & OP) (ogj & OG) SY BI (pad & FSZ) OUT (cbj & CBK) SAV | sf_fb; destruct sfH_ as ((j16 & jsk & lk & LOW & _) & (stb & STB) & OSP & (opj & OP) & (ogj & OG) & SY & BI & (pad & FSZ) & OUT & (cbj & CBK) & SAV) ].
split; [exact OSP|]. split; [exact SY|]. split; [exact BI|]. split; [| exact SAV].
apply rw_cells_forget in LOW. change (cells_size _) with 80%nat in LOW. destruct LOW as [jl LOW].
split. { exists jl, stb. apply (proj2 (rw_cells_app rsegs m (aLOW c) [CB 80 jl] [CB 24 stb])). split; [exact LOW|].
lazymatch goal with |- rw_cells _ _ ?A _ => replace A with (aSTEREO c) by (cbn; lia) end. exact STB. }
split. { exists opj, ogj. apply (proj2 (rw_cells_app rsegs m (aOP c) [CB 48 opj] [CB 32 ogj])). split; [exact OP|].
lazymatch goal with |- rw_cells _ _ ?A _ => replace A with (aOG c) by (cbn; lia) end. exact OG. }
split. { apply rw_cells_forget in FSZ. change (cells_size _) with 8%nat in FSZ. destruct FSZ as [f8 FSZ]. exists f8. exact FSZ. }
split; [exact OUT|].
apply rw_cells_forget in CBK. change (cells_size _) with 48%nat in CBK. destruct CBK as [hij CBK]. exists hij. exact CBK.
Qed.
