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
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1go X1hk. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1hl. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1gy X1hg X1hf X1hh X1hi X1hj X1gz X1gt X1gu X1h6 X1gx X1h3 X1h1.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require X1ff X1fd.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1ra X1qu X1qx X1ri X1r3 X1r4 X1r6 X1qz X1r0 X1r1 X1nt X1rg X1rh X1re X1od.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac rpc := apply ret_pc_even; [lia| reflexivity].

Lemma le4_eqm : forall a b : word, bv_unsigned a mod 2^32 = bv_unsigned b mod 2^32 -> le4 a = le4 b.
Proof.
intros a b E. unfold le4. rewrite <- (Z_to_le_bytes_mod 4 (bv_unsigned a) 32) by (cbn; lia).
rewrite <- (Z_to_le_bytes_mod 4 (bv_unsigned b) 32) by (cbn; lia). rewrite E. reflexivity.
Qed.
Lemma mod64_mod32 : forall v, (v mod 2^64) mod 2^32 = v mod 2^32.
Proof. intros v. symmetry. apply Znumtheory.Zmod_div_mod; [lia| lia| exists (2^32); reflexivity]. Qed.
Lemma rw_cells_C4_eqm : forall m A pre w v post,
rw_cells rsegs m A (pre ++ C4 w :: post) -> bv_unsigned w mod 2^32 = v mod 2^32 -> rw_cells rsegs m A (pre ++ C4 (Z_to_bv 64 v) :: post).
Proof.
intros m A pre w v post [[WF BY] WR] E. split; [split|].
- apply cells_wf_app in WF. apply cells_wf_app. destruct WF as [W1 W2]. split; [exact W1|]. cbn in W2 |- *. exact W2.
- rewrite cells_bytes_app in BY |- *. cbn [cells_bytes cbytes app] in BY |- *.
rewrite (le4_eqm (Z_to_bv 64 v) w); [exact BY|]. rewrite Z_to_bv_unsigned. change (bv_wrap 64 v) with (v mod 2^64).
rewrite mod64_mod32. symmetry. exact E.
- rewrite cells_size_app in WR |- *. cbn [cells_size csize] in WR |- *. exact WR.
Qed.
Lemma rw_cells_C4_CB4 : forall m A pre w post,
rw_cells rsegs m A (pre ++ C4 w :: post) -> rw_cells rsegs m A (pre ++ CB 4 (le4 w) :: post).
Proof.
intros m A pre w post [[WF BY] WR]. split; [split|].
- apply cells_wf_app in WF. apply cells_wf_app. destruct WF as [W1 [_ W2]]. split; [exact W1|]. split; [cbn; first [reflexivity| apply length_le4]| exact W2].
- rewrite cells_bytes_app in BY |- *. cbn [cells_bytes cbytes app] in BY |- *. exact BY.
- rewrite cells_size_app in WR |- *. cbn [cells_size csize] in WR |- *. exact WR.
Qed.

Lemma mod64_of_int : forall v, -2^63 <= v < 2^63 -> v mod 2^64 = (if v <? 0 then v + 2^64 else v).
Proof.
intros v Hv. destruct (Z.ltb_spec v 0).
- symmetry. apply (Z.mod_unique_pos v (2^64) (-1)); lia.
- apply Z.mod_small. lia.
Qed.
Lemma ltu_lit_int : forall k v, 0 <= k < 2^63 -> -2^63 <= v < 2^63 -> (k <? v mod 2^64) = ((v <? 0) || (k <? v)).
Proof.
intros k v Hk Hv. rewrite mod64_of_int by lia. destruct (Z.ltb_spec v 0); cbn [orb].
- apply Z.ltb_lt. lia.
- reflexivity.
Qed.

Lemma mod64_eq0 : forall v, -2^63 <= v < 2^63 -> (v mod 2^64 = 0 <-> v = 0).
Proof. intros v Hv. rewrite mod64_of_int by lia. destruct (Z.ltb_spec v 0); lia. Qed.

Ltac scond_int K :=
rewrite ?Z_to_bv_unsigned in K; cbv beta delta [bv_wrap bv_modulus] in K; rewrite ?Z.mod_0_l in K by lia;
match type of K with
| ?v mod _ <> 0 => let K' := fresh in assert (K' : v <> 0) by (intros E; apply K; rewrite E; reflexivity); clear K; rename K' into K
| ?v mod _ = 0 => apply (proj1 (mod64_eq0 v ltac:(lia))) in K
| _ => idtac
end.

Definition ph_after_rate (h : hstate bptr) (blk : bptr) (hd : spx_header) (st : dec_state bptr) (frame_size rate : Z) : M PState (option (hstate bptr)) :=
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

Definition hc_frame {RCEIL : RunCeiling} (c : hcx) (x : hax) (h : hstate bptr) (m : mem) (nbr brem0 fs rate : Z) : Prop :=
(exists j16 jsk lk, rw_cells rsegs m (aLOW c) [CB 16 j16; C8 (wz brem0); C8 (wz nbr); CB 16 jsk; C8 (wz (x_P c)); C8 (wz fs); C8 (wz (h_last_granule h)); CB 4 lk; C4 (wz rate)])
/\ (exists stb, rw_cells rsegs m (aSTEREO c) [CB 24 stb])
/\ stream_rep m c x h
/\ (exists opj, rw_cells rsegs m (aOP c) [CB 48 opj]) /\ (exists ogj, rw_cells rsegs m (aOG c) [CB 32 ogj])
/\ sync_rep m (aOY c) (a_D x) (h_oy h) (a_sybytes x)
/\ bits_rep rsegs m (aBITS c) (a_Dc x) (h_bits h)
/\ (exists pad, rw_cells rsegs m (aFSZ c) [CB 4 pad; C4 (wz fs)])
/\ (exists outb, u8arr rsegs m (aOUT c) outb /\ Z.of_nat (length outb) = 8000)
/\ (exists cbj, rw_cells rsegs m (aCBK c) [CB 48 cbj])
/\ rw_cells rsegs m (aSAV c) (sav_cells c).

Definition HCG {RCEIL : RunCeiling} (dec_rep : Z -> mem -> Z -> dec_state bptr -> list block -> Prop)
(c : hcx) (pc s1v : Z) (X : Prop) (h : hstate bptr) (blk : bptr) (hd : spx_header) (d : dec_state bptr) (fs rate : Z) (st : PState) (ms : machine_state) : Prop :=
exists (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
(x : hax) (nbr brem0 HB S pno : Z) (LBD : list block) (s0w s3w s8w : word),
ms = MS (mkR x1 (wz (hsp c)) (x_gp c) (wz RATP) t0 t1 t2 s0w (wz pno) a0 a1 a2 a3 a4 a5 a6 a7
(wz S) s3w (wz (h_extra_headers h)) (wz 2147483647) (wz HB) (wz (h_packet_count h)) s8w (wz s1v)
(wz (h_speex_serialno h)) (wz (h_channels h)) t3 t4 t5 t6)
F (wz pc) fc None m (seg_rom rsegs)
/\ frm0 fc /\ hdr_pure c x h nbr brem0 /\ hc_frame c x h m nbr brem0 fs rate
/\ hglobX c x h st m (LBD ++ [(blk, HB, SIZEOF_SPEEX_HEADER_Z)])
/\ hdr_blk m HB hd /\ 0 <= pno <= h_packet_count h
/\ 0 < S < 2^63 /\ dec_rep (aSTEREO c) m S d LBD /\ (forall b, In b LBD -> rblock_range (blk_addr b) (blk_size b))
/\ 0 <= fs <= 640 /\ -2^31 <= rate < 2^31 /\ X.

Notation HR dec_rep c h blk hd d fs rate := (HCG dec_rep c 0x1c624 (h_nframes h) True h blk hd d fs rate).
Notation HC dec_rep c h blk hd d fs rate := (HCG dec_rep c 0x1c644 (hd_frames_per_packet hd) (1 <= hd_frames_per_packet hd <= 10) h blk hd d fs rate).

Lemma junkframe_of {RCEIL : RunCeiling} : forall c x h m (low fz cbk : list cell) stb opj ogj outb,
rw_cells rsegs m (aLOW c) low -> cells_size low = 80%nat -> rw_cells rsegs m (aSTEREO c) [CB 24 stb] -> stream_rep m c x h ->
rw_cells rsegs m (aOP c) [CB 48 opj] -> rw_cells rsegs m (aOG c) [CB 32 ogj] ->
sync_rep m (aOY c) (a_D x) (h_oy h) (a_sybytes x) -> bits_rep rsegs m (aBITS c) (a_Dc x) (h_bits h) ->
rw_cells rsegs m (aFSZ c) fz -> cells_size fz = 8%nat ->
u8arr rsegs m (aOUT c) outb -> Z.of_nat (length outb) = 8000 ->
rw_cells rsegs m (aCBK c) cbk -> cells_size cbk = 48%nat -> rw_cells rsegs m (aSAV c) (sav_cells c) ->
hdr_junkframe c x h m.
Proof.
intros c x h m low fz cbk stb opj ogj outb LOW SL STB OSP OP OG SY BI FSZ SF OUT LOUT CBK SC SAV.
split; [exact OSP|]. split; [exact SY|]. split; [exact BI|]. split; [| exact SAV].
apply rw_cells_forget in LOW. rewrite SL in LOW. destruct LOW as [jl LOW].
split. { exists jl, stb. apply (proj2 (rw_cells_app rsegs m (aLOW c) [CB 80 jl] [CB 24 stb])). split; [exact LOW|].
lazymatch goal with |- rw_cells _ _ ?A _ => replace A with (aSTEREO c) by (cbn; lia) end. exact STB. }
split. { exists opj, ogj. apply (proj2 (rw_cells_app rsegs m (aOP c) [CB 48 opj] [CB 32 ogj])). split; [exact OP|].
lazymatch goal with |- rw_cells _ _ ?A _ => replace A with (aOG c) by (cbn; lia) end. exact OG. }
split. { apply rw_cells_forget in FSZ. rewrite SF in FSZ. destruct FSZ as [f8 FSZ]. exists f8. exact FSZ. }
split; [exists outb; split; [exact OUT| exact LOUT]|].
apply rw_cells_forget in CBK. rewrite SC in CBK. destruct CBK as [hij CBK]. exists hij. exact CBK.
Qed.

Section HDR3.
Context {RCEIL : RunCeiling}.
Variable dec_rep : Z -> mem -> Z -> dec_state bptr -> list block -> Prop.
Hypothesis DRF : dec_rep_frame_stmt dec_rep.
Hypothesis DCTL : rspx_decoder_ctl_stmt dec_rep.
Hypothesis DDESTROY : rspx_decoder_destroy_stmt dec_rep.
Hypothesis RFREE : rfree_stmt.
Hypothesis RHF : rheap_frame_stmt.
Hypothesis RBR : rheap_block_range_stmt.
Hypothesis RND : rheap_blocks_nodup_stmt.
Hypothesis RBD : rheap_blocks_disjoint_stmt.
Variable c : hcx.
Hypothesis CX : hcx_ok c.

Notation tpv := (wz RATP).
Notation DESTROY_FREE_NONE st blk := (X1qx.mbind (h_decoder_destroyP st) (fun _ => X1qx.mbind (raw_free blk) (fun _ => X1qx.mret (@None (hstate bptr))))).

#[using="RCEIL CX"] Lemma ctl_frame_ok : forall extra (BL : list block) P sz,
(aLOW c <= P /\ P + sz <= usp c) -> (forall b, In b BL -> In b extra) ->
Forall (xfoot_ok c extra) ((x_lo c, aLOW c) :: (P, P + sz) :: map (fun b : block => (blk_addr b, blk_addr b + blk_size b)) BL).
Proof.
intros extra BL P sz HP HBL. pose proof CX as sfP_; first [ sf_destruct 11%nat sfP_ as PF P0 P16 PL PIN SPAB ABB CEIL LO SP16 SPB | sf_fb; destruct sfP_ as (PF & P0 & P16 & PL & PIN & SPAB & ABB & CEIL & LO & SP16 & SPB) ]. unfold RFUZZ_STACK in LO.
apply Forall_cons; [left; cbn; lia|]. apply Forall_cons; [left; cbn; lia|].
apply Forall_forall. intros iv Hiv. apply in_map_iff in Hiv. destruct Hiv as (b & <- & Hb). right. exists b. split; [apply HBL; exact Hb| cbn; lia].
Qed.

Definition ph_from_rate (h : hstate bptr) (blk : bptr) (hd : spx_header) (d2 : dec_state bptr) (fs rate : Z) : M PState (option (hstate bptr)) :=
let '(_, st) := speex_decoder_ctl d2 (CtlSetSamplingRate rate) in
if (hd_frames_per_packet hd <? 1) || (10 <? hd_frames_per_packet hd)
then X1qx.mbind (h_decoder_destroyP st) (fun _ => X1qx.mbind (raw_free blk) (fun _ => X1qx.mret None))
else ph_after_rate h blk hd st fs rate.

#[using="DRF DCTL DDESTROY RFREE RHF RBR RND RBD CX"] Lemma hdr_ctls1 : forall fuel' h blk hd d pn st ms (br0 : Z) (oy0 : sync_st bptr),
HS dec_rep c h blk hd d st ms ->
(forall d2 fs rate st' ms', HR dec_rep c h blk hd d2 fs rate st' ms' ->
implM rsegs (X1qx.mbind (ph_from_rate h blk hd d2 fs rate) (hdr_tailK fuel' h pn)) st' (PKPOST dec_rep c br0 oy0) ms') ->
implM rsegs (X1qx.mbind (ph_after_init h blk hd d) (hdr_tailK fuel' h pn)) st (PKPOST dec_rep c br0 oy0) ms.
Proof.
intros fuel' h blk hd d pn st ms br0 oy0 HSC KC.
first [ sf_destruct 38%nat HSC as x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m x nbr brem0 HB S pno LBD s0w s3w s8w -> FRM PU FR HG HBK PNO SB DR BRD | sf_fb; destruct HSC as (x1 & t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & F & fc & m & x & nbr & brem0 & HB & S & pno & LBD & s0w & s3w & s8w & -> & FRM & PU & FR & HG & HBK & PNO & SB & DR & BRD) ].
pose proof PU as sfP_; first [ sf_destruct 9%nat sfP_ as SI1 EOS0 PC0 EST AS0 ALBD PURE LOK BUD' | sf_fb; destruct sfP_ as (SI1 & EOS0 & PC0 & EST & AS0 & ALBD & PURE & LOK & BUD') ].
pose proof FR as sfP_; first [ sf_destruct 11%nat sfP_ as (j16 & jsk & lk & LOW & LKOK) (stb & STB) OSP (opj & OP) (ogj & OG) SY BI (pad & FSZ) (outb & OUT & LOUT) (cbj & CBK) SAV | sf_fb; destruct sfP_ as ((j16 & jsk & lk & LOW & LKOK) & (stb & STB) & OSP & (opj & OP) & (ogj & OG) & SY & BI & (pad & FSZ) & (outb & OUT & LOUT) & (cbj & CBK) & SAV) ].
pose proof HG as sfP_; first [ sf_destruct 11%nat sfP_ as HP PERM PAY TP SEW (errv & ERR) AUX MI ST PE SO | sf_fb; destruct sfP_ as (HP & PERM & PAY & TP & SEW & (errv & ERR) & AUX & MI & ST & PE & SO) ].
pose proof HBK as sfP_; first [ sf_destruct 9%nat sfP_ as (junk28 & w1 & w2 & w3 & r1 & r2 & HCELLS) HBR V1 V2 V3 V4 V5 V6 V7 | sf_fb; destruct sfP_ as ((junk28 & w1 & w2 & w3 & r1 & r2 & HCELLS) & HBR & V1 & V2 & V3 & V4 & V5 & V6 & V7) ].
pose proof PURE as sfP_; first [ sf_destruct 22%nat sfP_ as SYOK BOK OWN SYBLK SYLEN BBR BSZ FS GFS NFR CHR RTR EXR SSR PCR LGR SIR EOR BRR L4K STR BUD | sf_fb; destruct sfP_ as (SYOK & BOK & OWN & SYBLK & SYLEN & BBR & BSZ & FS & GFS & NFR & CHR & RTR & EXR & SSR & PCR & LGR & SIR & EOR & BRR & L4K & STR & BUD) ].
pose proof CX as sfP_; first [ sf_destruct 11%nat sfP_ as PF P0 P16 PL PIN SPAB ABB CEIL LO SP16 SPB | sf_fb; destruct sfP_ as (PF & P0 & P16 & PL & PIN & SPAB & ABB & CEIL & LO & SP16 & SPB) ].
unfold RFUZZ_STACK in LO. pose proof CEIL as CEIL'. unfold alloc_ceiling in CEIL'.
pose proof HBR as sfP_; first [ sf_destruct 5%nat sfP_ as HB1 _ _ HB4 HB5 | sf_fb; destruct sfP_ as (HB1 & _ & _ & HB4 & HB5) ]. unfold alloc_ceiling, SIZEOF_SPEEX_HEADER_Z in HB4, HB5. unfold SPEEX_NB_MODES in V3.
assert (EOSB : 0 <= h_eos h <= 1) by lia.

unfold ph_after_init.
destruct (speex_decoder_ctl d (CtlSetEnh 1)) as [v1 d1] eqn:E1.
destruct (speex_decoder_ctl d1 CtlGetFrameSize) as [fs d2] eqn:E2.
set (rate := if h_rate h =? 0 then hd_rate hd else h_rate h).
assert (RTR' : -2^31 <= rate < 2^31) by (subst rate; destruct (h_rate h =? 0); lia).
change (let '(_, st3) := speex_decoder_ctl d2 (CtlSetSamplingRate rate) in
if (hd_frames_per_packet hd <? 1) || (10 <? hd_frames_per_packet hd) then DESTROY_FREE_NONE st3 blk else ph_after_rate h blk hd st3 fs rate)
with (ph_from_rate h blk hd d2 fs rate).
pose proof (RND _ _ _ HP) as ND.
set (LBX := (LBD ++ [(blk, HB, SIZEOF_SPEEX_HEADER_Z)]) ++ a_LB x) in *.
assert (HLo : forall b, In b (owned x h) -> In b LBX).
{ intros b Hb. subst LBX. apply in_app_iff. right. eapply Permutation_in; [apply Permutation_sym; exact PERM|]. apply in_app_iff. left. exact Hb. }
assert (HLD : forall b, In b LBD -> In b LBX) by (intros b Hb; subst LBX; apply in_app_iff; left; apply in_app_iff; left; exact Hb).
assert (HHB : In (blk, HB, SIZEOF_SPEEX_HEADER_Z) LBX) by (subst LBX; apply in_app_iff; left; apply in_app_iff; right; left; reflexivity).

assert (APART : forall bb a, (In bb (owned x h) \/ bb = (blk, HB, SIZEOF_SPEEX_HEADER_Z)) -> blk_addr bb <= a < blk_addr bb + blk_size bb ->
outside (map (fun b : block => (blk_addr b, blk_addr b + blk_size b)) LBD) a).
{ intros bb a Hbb Ra. apply outside_blocks. intros b Hb.
assert (NE : blk_id b <> blk_id bb).
{ pose proof ND as ND'. subst LBX. rewrite <- app_assoc, map_app in ND'. intros E.
eapply (nodup_app_disj _ _ (blk_id b) ND'); [apply in_map; exact Hb|]. rewrite E, map_app. apply in_app_iff.
destruct Hbb as [Hbb| ->]; [right; apply in_map; eapply Permutation_in; [apply Permutation_sym; exact PERM|]; apply in_app_iff; left; exact Hbb| left; left; reflexivity]. }
assert (Hbb' : In bb LBX) by (destruct Hbb as [Hbb| ->]; [apply HLo; exact Hbb| exact HHB]).
pose proof (RBD _ _ _ _ _ HP (HLD _ Hb) Hbb' NE). lia. }

assert (OWF : forall P sz a, (aLOW c <= a < P \/ P + sz <= a < usp c) -> aLOW c <= P -> 0 <= sz ->
outside ((x_lo c, aLOW c) :: (P, P + sz) :: map (fun b : block => (blk_addr b, blk_addr b + blk_size b)) LBD) a).
{ intros P sz a Ha HPl Hsz. cbn [outside]. split; [lia|]. split; [lia|]. apply outside_blocks. intros b Hb.
pose proof (BRD b Hb) as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ _ B4 _ | sf_fb; destruct sfP_ as (_ & _ & _ & B4 & _) ]. unfold alloc_ceiling in B4. lia. }
assert (OWB : forall P sz bb a, (In bb (owned x h) \/ bb = (blk, HB, SIZEOF_SPEEX_HEADER_Z)) -> blk_addr bb <= a < blk_addr bb + blk_size bb -> aLOW c <= P -> 0 <= sz ->
outside ((x_lo c, aLOW c) :: (P, P + sz) :: map (fun b : block => (blk_addr b, blk_addr b + blk_size b)) LBD) a).
{ intros P sz bb a Hbb Ra HPl Hsz. assert (Hbb' : In bb LBX) by (destruct Hbb as [Hbb| ->]; [apply HLo; exact Hbb| exact HHB]).
pose proof (RBR _ _ _ _ HP Hbb') as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ _ B4 _ | sf_fb; destruct sfP_ as (_ & _ & _ & B4 & _) ]. unfold alloc_ceiling in B4.
cbn [outside]. split; [lia|]. split; [lia|]. apply (APART bb a Hbb Ra). }

pose proof (proj1 (rw_cells_app rsegs m (aCBK c) [CB 44 cbj] [C4 (wz 1)]) CBK) as [CBK1 ENH]. cbn [cells_size csize Nat.add] in ENH. clear CBK.
replace (aCBK c + Z.of_nat 44) with (usp c + -108) in ENH by lia.
unfold low_cells, wz in LOW. unfold spx_header_cells in HCELLS. unfold wz in ENH.
unfold implM. iprefix. unfold wz.

do 7 zstep.

eapply evt_cut.
{ eapply DCTL with (STEREO := aSTEREO c) (S := S) (d := d) (LBD := LBD) (code := SPEEX_SET_ENH) (P := usp c + -108) (arg := ArgIntIn 1) (req := CtlSetEnh 1) (lo := x_lo c);
rewrite ?(unsigned_lit (aLOW c)) by lia;
first [ ctl_ptr_tac CX | exact (DR (aSTEREO c)) | reflexivity | exact TP | exact BRD | exact ST | exact MI | exact FRM
| cbn [ctl_req_fits]; right; reflexivity
| exists (Z_to_bv 64 1); split; [exact ENH| split; [reflexivity| lia]]
| right; lia
| intros b Hb; pose proof (BRD b Hb) as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ _ B4 _ | sf_fb; destruct sfP_ as (_ & _ & _ & B4 & _) ]; unfold alloc_ceiling in B4; cbn [ctl_arg_size]; lia
| unfold DEC_CTL_STACK, alloc_ceiling in *; lia ]. }
cbv beta. intros ms1 PO.
first [ sf_destruct 29%nat PO as y0 y1 y2 e0 e1 e2 e3 e4 e5 e6 e7 y3 y4 y5 y6 F1 fc1 m1 req1 -> CRQ MU WM MI1 FRM1 ST1 EA0 DR1 AP1 | sf_fb; destruct PO as (y0 & y1 & y2 & e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & y3 & y4 & y5 & y6 & F1 & fc1 & m1 & req1 & -> & CRQ & MU & WM & MI1 & FRM1 & ST1 & EA0 & DR1 & AP1) ].
cbn in CRQ. injection CRQ as <-. rewrite E1 in DR1. cbn [snd] in DR1. clear EA0.
cbn [ctl_arg_size] in MU. rewrite ?(unsigned_lit (aLOW c)) in MU by lia. rewrite ?(unsigned_lit (aLOW c)) in ST1 by lia.
replace (ret_pc (Z_to_bv 64 0x1c5f4)) with (Z_to_bv 64 0x1c5f4) by (symmetry; rpc).
destruct (hglobX_munch RHF RBR RND RBD c x h st m m1 _ _ CX HG MU WM MI1 ST1) as [HG1 AG].
{ apply ctl_frame_ok; [lia| intros b Hb; apply in_app_iff; left; exact Hb]. }
destruct AP1 as (we1 & ENH1 & _).
eapply (rw_cells_agree _ _ _ _ _ _ AG) in LOW; [| intros a Ha; apply OWF; cbn in Ha; lia].
eapply (rw_cells_agree _ _ _ _ _ _ AG) in STB; [| intros a Ha; apply OWF; cbn in Ha; lia].
eapply (rw_cells_agree _ _ _ _ _ _ AG) in OP; [| intros a Ha; apply OWF; cbn in Ha; lia].
eapply (rw_cells_agree _ _ _ _ _ _ AG) in OG; [| intros a Ha; apply OWF; cbn in Ha; lia].
eapply (rw_cells_agree _ _ _ _ _ _ AG) in FSZ; [| intros a Ha; apply OWF; unfold fsz_cells in Ha; cbn in Ha; lia].
eapply (u8arr_agree _ _ _ _ _ AG) in OUT; [| intros a Ha; apply OWF; lia].
eapply (rw_cells_agree _ _ _ _ _ _ AG) in CBK1; [| intros a Ha; apply OWF; cbn in Ha; lia].
eapply (rw_cells_agree _ _ _ _ _ _ AG) in SAV; [| intros a Ha; apply OWF; cbn in Ha; lia].
eapply (rw_cells_agree _ _ _ _ _ _ AG) in HCELLS; [| intros a Ha; eapply (OWB _ _ (blk, HB, SIZEOF_SPEEX_HEADER_Z)); [right; reflexivity| cbn in Ha |- *; unfold SIZEOF_SPEEX_HEADER_Z; lia| lia| lia]].
eapply (stream_rep_agree2 _ _ _ _ _ _ AG) in OSP; [| intros a Ha; apply OWF; lia| intros a (bb & Hbb & Ra); apply (OWB _ _ bb a); [left; apply in_owned_stream; exact Hbb| exact Ra| lia| lia]].
eapply (sync_rep_agree _ _ _ _ _ _ _ AG) in SY; [| intros a Ha; apply OWF; lia|].
2:{ intros a Ha. first [ sf_destruct 4%nat SY as _ _ DAT _ | sf_fb; destruct SY as (_ & _ & DAT & _) ]. unfold sync_data in DAT.
destruct (sy_data (h_oy h)) as [q|] eqn:ESD; [| first [ sf_destruct 4%nat DAT as _ _ _ ST0 | sf_fb; destruct DAT as (_ & _ & _ & ST0) ]; rewrite SYLEN, ST0 in Ha; lia].
apply (OWB _ _ (q, a_D x, sy_storage (h_oy h)) a); [left; apply in_owned_sync; exact ESD| cbn; rewrite <- SYLEN; lia| lia| lia]. }
eapply (bits_rep_agree _ _ _ _ _ _ AG) in BI; [| exact BOK| intros a Ha; apply OWF; lia| intros a Ha; apply (OWB _ _ _ a (or_introl (in_owned_bits x h))); [cbn; lia| lia| lia]].
assert (CBK : rw_cells rsegs m1 (aCBK c) [CB 44 cbj; C4 we1]).
{ apply (proj2 (rw_cells_app rsegs m1 (aCBK c) [CB 44 cbj] [C4 we1])). split; [exact CBK1|].
lazymatch goal with |- rw_cells _ _ ?A _ => replace A with (usp c + -108) by (cbn; lia) end. exact ENH1. }
clear MU WM AG HG ST MI ENH HP ENH1 CBK1.
pose proof HG1 as sfP_; first [ sf_destruct 10%nat sfP_ as HP _ _ TP1 _ _ _ _ ST _ | sf_fb; destruct sfP_ as (HP & _ & _ & TP1 & _ & _ & _ & _ & ST & _) ]. clear TP. rename TP1 into TP. rename HG1 into HG. rename MI1 into MI.
clear FRM. rename FRM1 into FRM. clear DR. rename DR1 into DR.

assert (FAILX : forall dX mX stX (FX : bvmap 5 word) fcX (y1 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y19 y20 y21 y23 y24 y25 y26 y27 y28 y29 y30 y31 : word),
frm0 fcX -> hdr_junkframe c x h mX -> hglobX c x h stX mX (LBD ++ [(blk, HB, SIZEOF_SPEEX_HEADER_Z)]) -> dec_rep (aSTEREO c) mX S dX LBD ->
evt rsegs (fun ms1 => impl rsegs (at_node rsegs) ((X1qx.mbind (DESTROY_FREE_NONE dX blk) (hdr_tailK fuel' h pn)) stX)
(epost (fun p ms2 => PKPOST dec_rep c br0 oy0 (fst p) (snd p) ms2)) ms1)
(MS (mkR y1 (Z_to_bv 64 (aLOW c)) (x_gp c) (Z_to_bv 64 RATP) y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 S) y19 y20 y21 (Z_to_bv 64 HB)
y23 y24 y25 y26 y27 y28 y29 y30 y31) FX (Z_to_bv 64 0x1c74c) fcX None mX (seg_rom rsegs))).
{ intros. apply evt_done. apply (hdr_f28c dec_rep DDESTROY RFREE RBR RND c CX).
unfold F28c. sf_eexists 26%nat. first [ unshelve sf_eexists 9%nat; [ exact (FX) | exact (fcX) | exact (mX) | exact (x) | exact (nbr) | exact (brem0) | exact (HB) | exact (S) | exact (LBD) | ] | sf_fb; exists FX, fcX, mX, x, nbr, brem0, HB, S, LBD ].
split; [reflexivity|]. split; [assumption|]. split; [exact PU|]. split; [assumption|]. split; [assumption|].
split; [lia|]. split; [assumption| exact BRD]. }

unfold fsz_cells in FSZ.
pose proof (proj1 (rw_cells_app rsegs m1 (aFSZ c) [CB 4 pad] [C4 (Z_to_bv 64 (h_frame_size h))]) FSZ) as [FSZ1 FSC]. cbn [cells_size csize Nat.add] in FSC. clear FSZ.
replace (aFSZ c + Z.of_nat 4) with (usp c + -8156) in FSC by lia.
apply (rw_cells_C4_CB4 m1 _ [] _ []) in FSC. cbn [app] in FSC.

do 4 zstep.
eapply evt_cut.
{ eapply DCTL with (STEREO := aSTEREO c) (S := S) (d := d1) (LBD := LBD) (code := SPEEX_GET_FRAME_SIZE) (P := usp c + -8156) (arg := ArgIntOut) (req := CtlGetFrameSize) (lo := x_lo c);
rewrite ?(unsigned_lit (aLOW c)) by lia;
first [ ctl_ptr_tac CX | exact DR | reflexivity | exact TP | exact BRD | exact ST | exact MI | exact FRM
| exact I
| eexists; exact FSC
| right; lia
| intros b Hb; pose proof (BRD b Hb) as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ _ B4 _ | sf_fb; destruct sfP_ as (_ & _ & _ & B4 & _) ]; unfold alloc_ceiling in B4; cbn [ctl_arg_size]; lia
| unfold DEC_CTL_STACK, alloc_ceiling in *; lia ]. }
cbv beta. intros ms2 PO.
first [ sf_destruct 29%nat PO as z0 z1 z2 g0 g1 g2 g3 g4 g5 g6 g7 z3 z4 z5 z6 F2 fc2 m2 req2 -> CRQ MU WM MI2 FRM2 ST2 EA0 DR2 AP2 | sf_fb; destruct PO as (z0 & z1 & z2 & g0 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & z3 & z4 & z5 & z6 & F2 & fc2 & m2 & req2 & -> & CRQ & MU & WM & MI2 & FRM2 & ST2 & EA0 & DR2 & AP2) ].
cbn in CRQ. injection CRQ as <-. rewrite E2 in DR2, AP2. cbn [fst snd] in DR2, AP2. clear EA0.
cbn [ctl_arg_size] in MU. rewrite ?(unsigned_lit (aLOW c)) in MU by lia. rewrite ?(unsigned_lit (aLOW c)) in ST2 by lia.
replace (ret_pc (Z_to_bv 64 0x1c604)) with (Z_to_bv 64 0x1c604) by (symmetry; rpc).
destruct (hglobX_munch RHF RBR RND RBD c x h st m1 m2 _ _ CX HG MU WM MI2 ST2) as [HG2 AG].
{ apply ctl_frame_ok; [lia| intros b Hb; apply in_app_iff; left; exact Hb]. }
destruct AP2 as [FSC2 FSR].
eapply (rw_cells_agree _ _ _ _ _ _ AG) in LOW; [| intros a Ha; apply OWF; cbn in Ha; lia].
eapply (rw_cells_agree _ _ _ _ _ _ AG) in STB; [| intros a Ha; apply OWF; cbn in Ha; lia].
eapply (rw_cells_agree _ _ _ _ _ _ AG) in OP; [| intros a Ha; apply OWF; cbn in Ha; lia].
eapply (rw_cells_agree _ _ _ _ _ _ AG) in OG; [| intros a Ha; apply OWF; cbn in Ha; lia].
eapply (rw_cells_agree _ _ _ _ _ _ AG) in FSZ1; [| intros a Ha; apply OWF; cbn in Ha; lia].
eapply (u8arr_agree _ _ _ _ _ AG) in OUT; [| intros a Ha; apply OWF; lia].
eapply (rw_cells_agree _ _ _ _ _ _ AG) in CBK; [| intros a Ha; apply OWF; cbn in Ha; lia].
eapply (rw_cells_agree _ _ _ _ _ _ AG) in SAV; [| intros a Ha; apply OWF; cbn in Ha; lia].
eapply (rw_cells_agree _ _ _ _ _ _ AG) in HCELLS; [| intros a Ha; eapply (OWB _ _ (blk, HB, SIZEOF_SPEEX_HEADER_Z)); [right; reflexivity| cbn in Ha |- *; unfold SIZEOF_SPEEX_HEADER_Z; lia| lia| lia]].
eapply (stream_rep_agree2 _ _ _ _ _ _ AG) in OSP; [| intros a Ha; apply OWF; lia| intros a (bb & Hbb & Ra); apply (OWB _ _ bb a); [left; apply in_owned_stream; exact Hbb| exact Ra| lia| lia]].
eapply (sync_rep_agree _ _ _ _ _ _ _ AG) in SY; [| intros a Ha; apply OWF; lia|].
2:{ intros a Ha. first [ sf_destruct 4%nat SY as _ _ DAT _ | sf_fb; destruct SY as (_ & _ & DAT & _) ]. unfold sync_data in DAT.
destruct (sy_data (h_oy h)) as [q|] eqn:ESD; [| first [ sf_destruct 4%nat DAT as _ _ _ ST0 | sf_fb; destruct DAT as (_ & _ & _ & ST0) ]; rewrite SYLEN, ST0 in Ha; lia].
apply (OWB _ _ (q, a_D x, sy_storage (h_oy h)) a); [left; apply in_owned_sync; exact ESD| cbn; rewrite <- SYLEN; lia| lia| lia]. }
eapply (bits_rep_agree _ _ _ _ _ _ AG) in BI; [| exact BOK| intros a Ha; apply OWF; lia| intros a Ha; apply (OWB _ _ _ a (or_introl (in_owned_bits x h))); [cbn; lia| lia| lia]].
clear MU WM AG HG ST MI HP FSC.
pose proof HG2 as sfP_; first [ sf_destruct 10%nat sfP_ as HP _ _ TP2 _ _ _ _ ST _ | sf_fb; destruct sfP_ as (HP & _ & _ & TP2 & _ & _ & _ & _ & ST & _) ]. clear TP. rename TP2 into TP. rename HG2 into HG. rename MI2 into MI.
clear FRM. rename FRM2 into FRM. clear DR. rename DR2 into DR.

pose proof (munch_refl [(aLOW c + 56, aLOW c + 64)] m2) as MU. pose proof (wmono_refl rsegs m2) as WM.
zstep. rewrite sx32_signed_small by lia. zstep. zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => set (m3 := mx) in * end.
pose proof (agree_on_of_munch _ _ _ MU WM) as AG.
destruct (hglobX_munch RHF RBR RND RBD c x h st m2 m3 _ _ CX HG MU WM) as [HG3 _]; [assumption| assumption| apply Forall_cons; [left; cbn; lia| apply Forall_nil]|].
eapply (stream_rep_agree2 _ _ _ _ _ _ AG) in OSP; [| side1c| intros a (bb & Hbb & Ra); pose proof (RBR _ _ _ _ HP (HLo _ (in_owned_stream _ _ _ Hbb))) as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ _ B4 _ | sf_fb; destruct sfP_ as (_ & _ & _ & B4 & _) ]; unfold alloc_ceiling in B4; cbn [outside fst snd]; lia].
eapply (sync_rep_agree _ _ _ _ _ _ _ AG) in SY; [| side1c|].
2:{ intros a Ha. first [ sf_destruct 4%nat SY as _ _ DAT _ | sf_fb; destruct SY as (_ & _ & DAT & _) ]. unfold sync_data in DAT.
destruct (sy_data (h_oy h)) as [q|] eqn:ESD; [| first [ sf_destruct 4%nat DAT as _ _ _ ST0 | sf_fb; destruct DAT as (_ & _ & _ & ST0) ]; rewrite SYLEN, ST0 in Ha; lia].
pose proof (RBR _ _ _ _ HP (HLo _ (in_owned_sync _ _ _ ESD))) as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ _ B4 _ | sf_fb; destruct sfP_ as (_ & _ & _ & B4 & _) ]. cbn in B4. unfold alloc_ceiling in B4. cbn [outside fst snd]. lia. }
eapply (bits_rep_agree _ _ _ _ _ _ AG) in BI; [| exact BOK| side1c| intros a Ha; pose proof BBR as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ _ B4 _ | sf_fb; destruct sfP_ as (_ & _ & _ & B4 & _) ]; unfold alloc_ceiling in B4; cbn [outside fst snd]; lia].
assert (DR3 : dec_rep (aSTEREO c) m3 S d2 LBD).
{ eapply DRF; [exact DR|]. intros a Ha (bb & Hbb & Ra). apply AG; [exact Ha|].
pose proof (BRD bb Hbb) as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ _ B4 _ | sf_fb; destruct sfP_ as (_ & _ & _ & B4 & _) ]. unfold alloc_ceiling in B4. cbn [outside fst snd]. lia. }
clear MU WM AG HG DR HP ST MI. rename HG3 into HG. rename DR3 into DR.
pose proof HG as sfP_; first [ sf_destruct 10%nat sfP_ as HP _ _ _ _ _ _ MI ST _ | sf_fb; destruct sfP_ as (HP & _ & _ & _ & _ & _ & _ & MI & ST & _) ].
clearbody m3.

assert (FSZ : rw_cells rsegs m3 (aFSZ c) [CB 4 pad; C4 (Z_to_bv 64 fs)]).
{ apply (proj2 (rw_cells_app rsegs m3 (aFSZ c) [CB 4 pad] [C4 (Z_to_bv 64 fs)])). split; [exact FSZ1|].
lazymatch goal with |- rw_cells _ _ ?A _ => replace A with (usp c + -8156) by (cbn; lia) end. exact FSC2. }
clear FSZ1 FSC2.

assert (JF3 : hdr_junkframe c x h m3).
{ eapply (junkframe_of c x h m3); [exact LOW| reflexivity| exact STB| exact OSP| exact OP| exact OG| exact SY| exact BI| exact FSZ| reflexivity| exact OUT| exact LOUT| exact CBK| reflexivity| exact SAV]. }

zstep. if_cases BF; unfold bv_ltu in BF; rewrite !Z_to_bv_unsigned in BF; change (bv_wrap 64 640) with 640 in BF;
change (bv_wrap 64 fs) with (fs mod 2^64) in BF; rewrite ltu_lit_int in BF by lia; change (2 * 320) with 640.
-
rewrite BF. apply (FAILX d2 m3 st F2 fc2); [exact FRM| exact JF3| exact HG| exact DR].
- rewrite BF. assert (FSOK : 0 <= fs <= 640) by (destruct (Z.ltb_spec fs 0); destruct (Z.ltb_spec 640 fs); cbn in BF; try discriminate; lia). clear BF JF3.

assert (JR : forall mR (FR' : bvmap 5 word) (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
rw_cells rsegs mR (aLOW c) [CB 16 j16; C8 (Z_to_bv 64 brem0); C8 (Z_to_bv 64 nbr); CB 16 jsk; C8 (Z_to_bv 64 (x_P c)); C8 (Z_to_bv 64 fs); C8 (Z_to_bv 64 (h_last_granule h)); CB 4 lk; C4 (Z_to_bv 64 rate)] ->
rw_cells rsegs mR (aSTEREO c) [CB 24 stb] -> stream_rep mR c x h -> rw_cells rsegs mR (aOP c) [CB 48 opj] -> rw_cells rsegs mR (aOG c) [CB 32 ogj] ->
sync_rep mR (aOY c) (a_D x) (h_oy h) (a_sybytes x) -> bits_rep rsegs mR (aBITS c) (a_Dc x) (h_bits h) ->
rw_cells rsegs mR (aFSZ c) [CB 4 pad; C4 (Z_to_bv 64 fs)] -> u8arr rsegs mR (aOUT c) outb -> rw_cells rsegs mR (aCBK c) [CB 44 cbj; C4 we1] ->
rw_cells rsegs mR (aSAV c) (sav_cells c) ->
rw_cells rsegs mR HB [CB 28 junk28; C4 (wz (hd_speex_version_id hd)); C4 (wz (hd_header_size hd)); C4 (wz (hd_rate hd)); C4 (wz (hd_mode hd));
C4 (wz (hd_mode_bitstream_version hd)); C4 (wz (hd_nb_channels hd)); C4 w1; C4 w2; C4 w3;
C4 (wz (hd_frames_per_packet hd)); C4 (wz (hd_extra_headers hd)); C4 r1; C4 r2] ->
hglobX c x h st mR (LBD ++ [(blk, HB, SIZEOF_SPEEX_HEADER_Z)]) -> dec_rep (aSTEREO c) mR S d2 LBD ->
evt rsegs (fun ms1 => impl rsegs (at_node rsegs) ((X1qx.mbind (ph_from_rate h blk hd d2 fs rate) (hdr_tailK fuel' h pn)) st)
(epost (fun p ms2 => PKPOST dec_rep c br0 oy0 (fst p) (snd p) ms2)) ms1)
(MS (mkR y1 (Z_to_bv 64 (aLOW c)) (x_gp c) (Z_to_bv 64 RATP) y5 y6 y7 s0w (Z_to_bv 64 pno) y10 y11 y12 y13 y14 y15 y16 y17
(Z_to_bv 64 S) s3w (Z_to_bv 64 (h_extra_headers h)) (Z_to_bv 64 2147483647) (Z_to_bv 64 HB) (Z_to_bv 64 (h_packet_count h))
s8w (Z_to_bv 64 (h_nframes h)) (Z_to_bv 64 (h_speex_serialno h)) (Z_to_bv 64 (h_channels h)) y28 y29 y30 y31)
F2 (Z_to_bv 64 0x1c624) fc2 None mR (seg_rom rsegs))).
{ intros. apply evt_done. apply KC.
lazymatch goal with H : hglobX c x h st mR _ |- _ => pose proof H as sfP_; first [ sf_destruct 10%nat sfP_ as HPR _ _ _ _ _ _ MIR STR' _ | sf_fb; destruct sfP_ as (HPR & _ & _ & _ & _ & _ & _ & MIR & STR' & _) ] end.
unfold HCG. sf_eexists 16%nat. first [ unshelve sf_eexists 13%nat; [ exact (F2) | exact (fc2) | exact (mR) | exact (x) | exact (nbr) | exact (brem0) | exact (HB) | exact (S) | exact (pno) | exact (LBD) | exact (s0w) | exact (s3w) | exact (s8w) | ] | sf_fb; exists F2, fc2, mR, x, nbr, brem0, HB, S, pno, LBD, s0w, s3w, s8w ].
split; [reflexivity|]. split; [exact FRM|]. split; [exact PU|].
split. { split; [exists j16, jsk, lk; unfold wz; assumption|]. split; [exists stb; assumption|]. split; [assumption|].
split; [exists opj; assumption|]. split; [exists ogj; assumption|]. split; [assumption|]. split; [assumption|].
split; [exists pad; unfold wz; assumption|]. split; [exists outb; split; [assumption| exact LOUT]|].
split; [| assumption].
lazymatch goal with H : rw_cells rsegs mR (aCBK c) _ |- _ => apply rw_cells_forget in H; cbn [cells_size csize Nat.add] in H; destruct H as [hij H']; exists hij; exact H' end. }
split; [assumption|]. split. { split; [first [ unshelve sf_eexists 6%nat; [ exact (junk28) | exact (w1) | exact (w2) | exact (w3) | exact (r1) | exact (r2) | ] | sf_fb; exists junk28, w1, w2, w3, r1, r2 ]; unfold spx_header_cells; assumption|]. split; [exact HBR|]. unfold SPEEX_NB_MODES. repeat (split; [lia|]). lia. }
split; [exact PNO|]. split; [exact SB|]. split; [assumption|]. split; [exact BRD|]. split; [exact FSOK|]. split; [exact RTR'| exact I]. }

zstep. rewrite sx32_signed_small by lia. zstep. if_cases BRT; scond BRT; scond_int BRT.
+
assert (ER : rate = h_rate h) by (subst rate; replace (h_rate h =? 0) with false by (symmetry; apply Z.eqb_neq; exact BRT); reflexivity).
rewrite <- ER in LOW. apply JR; assumption.
+
assert (ER : rate = hd_rate hd) by (subst rate; rewrite BRT; reflexivity).
pose proof (munch_refl [(aLOW c + 76, aLOW c + 80)] m3) as MU. pose proof (wmono_refl rsegs m3) as WM.
zstep. rewrite sx32_signed_small by lia. zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => set (m5 := mx) in * end.
pose proof (agree_on_of_munch _ _ _ MU WM) as AG.
destruct (hglobX_munch RHF RBR RND RBD c x h st m3 m5 _ _ CX HG MU WM) as [HG4 _]; [assumption| assumption| apply Forall_cons; [left; cbn; lia| apply Forall_nil]|].
eapply (stream_rep_agree2 _ _ _ _ _ _ AG) in OSP; [| side1c| intros a (bb & Hbb & Ra); pose proof (RBR _ _ _ _ HP (HLo _ (in_owned_stream _ _ _ Hbb))) as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ _ B4 _ | sf_fb; destruct sfP_ as (_ & _ & _ & B4 & _) ]; unfold alloc_ceiling in B4; cbn [outside fst snd]; lia].
eapply (sync_rep_agree _ _ _ _ _ _ _ AG) in SY; [| side1c|].
2:{ intros a Ha. first [ sf_destruct 4%nat SY as _ _ DAT _ | sf_fb; destruct SY as (_ & _ & DAT & _) ]. unfold sync_data in DAT.
destruct (sy_data (h_oy h)) as [q|] eqn:ESD; [| first [ sf_destruct 4%nat DAT as _ _ _ ST0 | sf_fb; destruct DAT as (_ & _ & _ & ST0) ]; rewrite SYLEN, ST0 in Ha; lia].
pose proof (RBR _ _ _ _ HP (HLo _ (in_owned_sync _ _ _ ESD))) as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ _ B4 _ | sf_fb; destruct sfP_ as (_ & _ & _ & B4 & _) ]. cbn in B4. unfold alloc_ceiling in B4. cbn [outside fst snd]. lia. }
eapply (bits_rep_agree _ _ _ _ _ _ AG) in BI; [| exact BOK| side1c| intros a Ha; pose proof BBR as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ _ B4 _ | sf_fb; destruct sfP_ as (_ & _ & _ & B4 & _) ]; unfold alloc_ceiling in B4; cbn [outside fst snd]; lia].
assert (DR4 : dec_rep (aSTEREO c) m5 S d2 LBD).
{ eapply DRF; [exact DR|]. intros a Ha (bb & Hbb & Ra). apply AG; [exact Ha|].
pose proof (BRD bb Hbb) as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ _ B4 _ | sf_fb; destruct sfP_ as (_ & _ & _ & B4 & _) ]. unfold alloc_ceiling in B4. cbn [outside fst snd]. lia. }
clearbody m5. rewrite <- ER in LOW. apply JR; assumption.
Qed.
End HDR3.
