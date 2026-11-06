(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/pj_parse_seg_c1.v, with its module paths and module names changed; 605 of its 682 lines of code are new or changed and 694 lines of the source are left out. *)
(* fuzz_preset, the walk of round_trip_text on the #102 pins, image A' (asan 1be0f53d96cb9d6c, twin bff8519bbe3ea0e4):
   STRETCH O2 (lane WalkRtt102.RttO2CK). rule 24: proves no function (kind: segment lemma): the function-level gate is
   the text owner's, cleared for round_trip_text by an proof-index lookup (EXIT=0, no released asan proof; the index
   snapshot of 04:58Z, NOT a cold/* sweep - this lane ran none).
   THE STATEMENT is the cut layer's RTT_SEG_O2 (lib/A/Prog/Rtt102Cut.v) at L := A_prog_listing, PA := PI_prog_A,
   PI := prh_img_A: from rtt_at_o2 at RT_O2 (A' +0x328), given the CK stretch, the text's conclusion.
   THE CODE (A' +0x328 .. +0x33c, A' capstone listing lines 204-208):
     +0x328 lbu a0, -0x5e4(s11)    g_own_ran_out (s11 = sigma + RT_O1 + RT_S11, rtt_s11; the byte is 0: the ledger's own field)
     +0x32c addi s5, zero, 1
     +0x330 bnez a0, X             not taken: the byte is rtt_led's own field, 0 (the engine decides it)
     +0x334 jal fuzz_alloc_ran_out the kit's text (PRH_FnAlloc.v at the batch kit's cut, blob 4d8aeba047e5, the text unchanged: S' = S, the ledger with most / own kept)
     +0x338 bnez a0, X             not taken: a0 = ranr = ri_ran D = 0 (rtt_rb, the granted read-back) -> +0x33c RT_CK
   Both branches to X are refuted by the cut's own facts; the run reaches RT_CK only (cut 6e2b5d75a77: RTT_SEG_O2 has
   no X edge). THE RUNS (measured on A', probe build ed82971dd4): ss_O2a stops at PTS_call AS_fuzz_alloc_ran_out
   with the return offset 824 in pc / ra; ss_O2r with a0 pinned to 0 stops at RT_CK.
   Numerals. DERIVED: 824 (+0x338, fuzz_alloc_ran_out's return site, 4 * the slot inside the function), -1508 (the lbu
   immediate -0x5e4), 176 / 160 (RT_R's bounds: the frame 0xa0 and the realignment 0x20 - 16), 27392 / 0 (STK_round_trip_text
   / STK_fuzz_alloc_ran_out at prh_img_A, by vm_compute), 128 (fs_frame_bytes 1), 8 / 16 / 32 (LENGTH: word, granule,
   alignment). WORD: register indices. No ADDRESS literal: code addresses are pa_sigma / pa_val of PAImg_prog.v.
   RE-FIT TO THE BATCH KIT'S CUT 7cdbb61b5fa0 (lane WalkRtt102b, on the shared layer 80a1d52c32c7): DW is gone (Section and
   statement); rtt_carry's 11th conjunct, the wild traces since the entry, is kept by o2_carry_eqmem (same state) and
   o2_carry_call (Rtt102Cut.rtt_wild_keep0 across the callee's empty-budget journal); rtt_J is the depot-moved journal,
   so the call rule is applied at the entry `set_depot (st_depot S) (ri_S D)`, and its caller journal (rtt_Jc D S ..)
   is rtt_J at RT_CK as it stands, fuzz_alloc_ran_out keeping S; every journal is read by the ajx_* projections;
   rtt_rb's two appended conjuncts (back's free order at every depth bound, pj_ncapR back t) pass through, by
   PRH_PjOrder.pj_foR_frame (blob e5917626b82b) and Rtt102Cut.v rtt_ncapR_agree (PRH_Reader.v, blob 4266e709561a, has
   no frame lemma for pj_ncapR).
   R-FORM PORT (lane WalkRtt102-2.RttO2, on wave 0 448ecd157e57 of this port): the statement concludes
   YA0nH.SRr' segs YGcfRehidePost.RZ_cf and rtt_J is at RZW := YA0nH.wle' SEGS YGcfRehidePost.RZ_cf
   (CrtFit's WLE contract); the runs take the R runners paj_run_x_invR / paj_run_to_x_invR at RZW, the call the R rule
   aj_call_x_spR at RZW, the plain text tfuzz_alloc_ran_out_specX lifted into its callee premise (YA0nH.SRr_SRrG,
   YCbqG.apost_base_x_R_lift at YA0nH.wle_wle', recipe R5); every journal, the callee's included, is read by the ajxR_*
   projections (aview clauses only, no world conjunct). No Section hypothesis changed. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG YGcallx YCbqGcall.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YSRrMemnorm YGcfTreeVis YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PjRoundTrip PresetRoomPos.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes WriterValue PjWriteHyp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_prog PAImg_prog PRH_Base PRH_Img.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Reader PRH_FnAlloc PRH_FnCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_FnWriter PRH_PjOrder.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S10Env S1ImgA S1Ledger Rtt102Cut.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YA0nH YGcfRehidePost.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- image A': round_trip_text's entry as a byte offset from the listing's base (DERIVED: the generated sigma / base) ---- *)
Definition RTT_PC : Z := A_prog_sigma AS_round_trip_text - A_prog_base.
(* DERIVED: fuzz_alloc_ran_out's return site +0x338 *)
Definition RT_O2R : Z := 824.
(* DERIVED: the immediate of `lbu a0, -0x5e4(s11)` at +0x328 *)
Definition RT_OWNOFF : Z := -1508.
(* the registers the prologue fixed (rtt_cregs) *)
Definition RTT_CREGS : list (bv 5) := [2; 8; 9; 18; 19; 20; 25; 26; 3; 4]%bv.

(* the O2 entry: the one read-only region, g_own_ran_out's byte at s11 - 1508 (atom xr 27 = s11), holding 0 *)
Definition ss_O2a : sstate := mkSS (RTT_PC + RT_O2) cur_atoms
  [YP09.mkRegion (Some (xr 27)) RT_OWNOFF (RT_OWNOFF + 1) 0 0 [YP09.mkChunk RT_OWNOFF (CVal 1 (SLit 0))]] None
  (mkFacts [] [] []).
(* after fuzz_alloc_ran_out: a0 pinned to the flag it returned, no region *)
Definition ss_O2r (v : Z) : sstate := mkSS (RTT_PC + RT_O2R) (sr_set cur_atoms 10%bv (SLit v)) [] None (mkFacts [] [] []).

(* ---- pure arithmetic ---- *)
Lemma o2_R : forall sp0, sp0 mod 16 = 0 ->
  RT_R sp0 mod 32 = 0 /\ sp0 - 176 <= RT_R sp0 <= sp0 - 160 /\ (RT_R sp0 - sp0) mod 16 = 0.
Proof.
intros sp0 H. unfold RT_R, RT_FRAME.
pose proof (Z.div_mod (sp0 - 160) 32 ltac:(lia)) as E1.
pose proof (Z.mod_pos_bound (sp0 - 160) 32 ltac:(lia)) as M1.
pose proof (Z.div_mod sp0 16 ltac:(lia)) as E2. rewrite H, Z.add_0_r in E2.
set (m := (sp0 - 160) mod 32) in *. set (d := (sp0 - 160) / 32) in *. set (q := sp0 / 16) in *.
assert (Hm : m = 0 \/ m = 16) by lia.
split; [|split; [lia|]].
- replace (sp0 - 160 - m) with (d * 32) by lia. apply Z.mod_mul. lia.
- destruct Hm as [Hm | Hm]; rewrite Hm.
  + replace (sp0 - 160 - 0 - sp0) with ((-10) * 16) by lia. apply Z.mod_mul. lia.
  + replace (sp0 - 160 - 16 - sp0) with ((-11) * 16) by lia. apply Z.mod_mul. lia.
Qed.
(* the shadow of back (F + 32, 56 bytes) inside the class-1 frame's 16 shadow bytes *)
Lemma o2_sh_in : forall F x, F mod 32 = 0 -> F + 32 <= x < F + 88 ->
  shadow_addr F <= shadow_of_addr SHADOW_OFF x < shadow_addr F + 128 / 8.
Proof.
intros F x HF Hx. unfold shadow_addr, shadow_of_addr.
pose proof (Z.div_mod F 32 ltac:(lia)) as E. rewrite HF, Z.add_0_r in E.
set (q := F / 32) in *.
assert (EF : F / 8 = 4 * q).
{ rewrite E. replace (32 * q) with ((4 * q) * 8) by lia. apply Z.div_mul. lia. }
assert (EX : x / 8 = 4 * q + (x - F) / 8).
{ replace x with ((x - F) + (4 * q) * 8) at 1 by lia. rewrite Z.div_add by lia. lia. }
assert (B1 : 4 <= (x - F) / 8) by (apply Z.div_le_lower_bound; lia).
assert (B2 : (x - F) / 8 < 11) by (apply Z.div_lt_upper_bound; lia).
change (128 / 8) with 16. lia.
Qed.

(* bytes keep / writability across memories (pure, any segment list) *)
Lemma o2_wr_ov : forall segs (m m' : word -> option byte) x, m' (Z_to_bv 64 x) = m (Z_to_bv 64 x) ->
  writable_at segs m x -> writable_at segs m' x.
Proof. intros segs m m' x E. unfold writable_at, wview. rewrite E. tauto. Qed.

Ltac o2keep HS := lazymatch goal with |- getr _ ?rr = _ =>
  let H := fresh in prreg HS rr H; rewrite H; repeat rewrite ew_ewset_other by lia; te_close end.
Ltac o2in := cbv [RTT_CREGS In]; repeat (first [left; reflexivity | right]).
Ltac o2zvm := first [ apply Z.leb_le; vm_compute; reflexivity | apply Z.ltb_lt; vm_compute; reflexivity
                    | vm_compute; reflexivity ].

Section img. Context {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
#[local] Existing Instance prh_img_A.
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PI_prog_A).
#[local] Notation VAL := (@pa_val _ A_prog_listing PI_prog_A).
#[local] Notation SIGMA := (@pa_sigma _ A_prog_listing PI_prog_A).
#[local] Notation BASE := (@pa_val _ A_prog_listing PI_prog_A A_TEXT).
#[local] Notation RLO := (@pa_relro_lo _ A_prog_listing PI_prog_A).
#[local] Notation RHI := (@pa_relro_hi _ A_prog_listing PI_prog_A).
#[local] Notation PST := (@prh_pst prh_img_A).
(* the world relation of every journal of this walk (Rtt102Cut.v RZW) *)
#[local] Notation RZW := (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf).

(* ---- image A' facts (vm_compute over the generated listing, no number typed) ---- *)
Lemma o2_pc : forall off, BASE + (RTT_PC + off) = SIGMA AS_round_trip_text + off.
Proof.
intros off. assert (E : BASE + RTT_PC = SIGMA AS_round_trip_text) by (vm_compute; reflexivity). lia.
Qed.
Lemma o2_base : 0 <= BASE /\ BASE + 2 ^ 20 <= 2 ^ 31.
Proof. split; o2zvm. Qed.
Lemma o2_s11 : SIGMA AS_round_trip_text + RT_O1 + RT_S11 = @pi_g_own_ran_out prh_img_A - RT_OWNOFF /\
  4096 <= @pi_g_own_ran_out prh_img_A /\ @pi_g_own_ran_out prh_img_A + 2048 <= 2 ^ 31.
Proof. split; [vm_compute; reflexivity | split; o2zvm]. Qed.
Lemma o2_stk : @STK_round_trip_text prh_img_A = 27392 /\ @STK_fuzz_alloc_ran_out prh_img_A = 0.
Proof. split; vm_compute; reflexivity. Qed.
Lemma o2_ro_img : forall a, in_roP SEGS RLO RHI a -> in_img SEGS a.
Proof.
intros a [(sg & Hin & _ & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr] | exact (@pa_relro_img _ _ PI_prog_A a Hr)].
Qed.
Lemma o2_pst_ro : forall a, Exists (in_zr a) PST -> ~ in_roP SEGS RLO RHI a.
Proof. exact pst_not_ro_A. Qed.

(* ---- memories equal pointwise (a run that writes nothing) ---- *)
Lemma o2_av_eq : forall (H : word -> bool) (m m' : word -> option byte), (forall x, m' x = m x) ->
  forall a, aview SEGS H m' a = aview SEGS H m a.
Proof. intros H m m' Hm a. apply aview_eq_of. unfold mrestrict. rewrite Hm. reflexivity. Qed.
Lemma o2_mb_eq : forall (H : word -> bool) (m m' : word -> option byte), (forall x, m' x = m x) ->
  forall a, mbyte SEGS (mrestrict H m') a = mbyte SEGS (mrestrict H m) a.
Proof. intros H m m' Hm a. unfold mbyte, mrestrict. rewrite Hm. reflexivity. Qed.
(* two pointwise-equal memories agree (pj_agreeR) on every byte set, under one view *)
Lemma o2_agree_eq : forall (H : word -> bool) (m m' : word -> option byte) (X : Z -> Prop), (forall x, m' x = m x) ->
  pj_agreeR SEGS (mrestrict H m) (mrestrict H m') X.
Proof.
intros H m m' X Hm x _. split; [apply (o2_mb_eq H m m' Hm) |].
apply o2_wr_ov. unfold mrestrict. rewrite Hm. reflexivity.
Qed.
Lemma o2_tree_eq : forall (W : world SEGS) m m' lblk p t Dl, (forall x, m' x = m x) ->
  pj_nodeR SEGS (mrestrict (w_H W) m) lblk p t Dl -> pj_nodeR SEGS (mrestrict (w_H W) m') lblk p t Dl.
Proof.
intros W m m' lblk p t Dl Hm HT. exact (pj_nodeR_frame SEGS t _ _ lblk p Dl HT (o2_agree_eq (w_H W) m m' _ Hm)).
Qed.

(* ---- off the image: presence from writability, writability across views ---- *)
Lemma o2_apr_of_wr : forall (H : word -> bool) (m : word -> option byte) a, 0 <= a < 2 ^ 64 -> ~ in_img SEGS a ->
  writable_at SEGS (mrestrict H m) a -> apresent H m a.
Proof.
intros H m a Ha Hn Hw. unfold apresent.
destruct (mrestrict H m (Z_to_bv 64 a)) as [b|] eqn:E.
- unfold mrestrict in E. destruct (H (Z_to_bv 64 a)) eqn:Hh; [discriminate E|].
  split; [reflexivity | exists b; exact E].
- exfalso. unfold writable_at in Hw. apply (YGcallMxmn.ak_wview_absent_seg SEGS _ _ Hw E).
  rewrite unsigned_lit_small by lia. apply find_segment_none. exact Hn.
Qed.
Lemma o2_wr_keep : forall (H H' : word -> bool) (m m' : word -> option byte) x, 0 <= x < 2 ^ 64 -> ~ in_img SEGS x ->
  aview SEGS H' m' x = aview SEGS H m x -> writable_at SEGS (mrestrict H m) x -> writable_at SEGS (mrestrict H' m') x.
Proof.
intros H H' m m' x Hx Hn He Hw. apply apresent_writable.
apply (apresent_transfer SEGS H H' m m' x Hx Hn He). exact (o2_apr_of_wr H m x Hx Hn Hw).
Qed.
(* views that agree on a byte set off the image agree (pj_agreeR) on it *)
Lemma o2_agree_keep : forall (W W' : world SEGS) m m' (X : Z -> Prop),
  (forall x, X x -> 0 <= x < 2 ^ 64 /\ ~ in_img SEGS x /\ aview SEGS (w_H W') m' x = aview SEGS (w_H W) m x) ->
  pj_agreeR SEGS (mrestrict (w_H W) m) (mrestrict (w_H W') m') X.
Proof.
intros W W' m m' X HA x Hx. destruct (HA x Hx) as (Hr & Hn & He). split.
- apply mbyte_of_aview. exact He.
- exact (o2_wr_keep (w_H W) (w_H W') m m' x Hr Hn He).
Qed.
(* the tree frame lemma over views that agree on its footprint, off the image *)
Lemma o2_tree_keep : forall (W W' : world SEGS) m m' lblk p t Dl,
  pj_nodeR SEGS (mrestrict (w_H W) m) lblk p t Dl ->
  (forall x, pj_footR p Dl x -> 0 <= x < 2 ^ 64 /\ ~ in_img SEGS x /\ aview SEGS (w_H W') m' x = aview SEGS (w_H W) m x) ->
  pj_nodeR SEGS (mrestrict (w_H W') m') lblk p t Dl.
Proof.
intros W W' m m' lblk p t Dl HT HA. exact (pj_nodeR_frame SEGS t _ _ lblk p Dl HT (o2_agree_keep W W' m m' _ HA)).
Qed.
(* a covering hull's sub-range (FuzzStrdup.v sd_hull_sub, restated) *)
Lemma o2_hull_sub : forall (rd : reader) p m d n, shadow_hull_vis rd p m -> p <= d -> d + n <= p + m -> 0 < n ->
  shadow_hull_vis rd d n.
Proof.
intros rd p m d n Hh Hpd Hdn Hn s Hs. apply Hh.
pose proof (shadow_mono p d Hpd) as M1. pose proof (shadow_mono (d + n - 1) (p + m - 1) ltac:(lia)) as M2.
assert (R8 : forall u v, u <= v -> u / 8 * 8 <= v / 8 * 8)
  by (intros u v Huv; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
pose proof (R8 _ _ M1). pose proof (R8 _ _ M2). lia.
Qed.
(* a word at a: its 8 bytes (YCem.v rdword_of_val_mem, restated) *)
Lemma o2_rdword : forall H mem a v, val_mem SEGS (mrestrict H mem) a 8 v -> 0 <= v < 2 ^ 64 ->
  rdword (aview SEGS H mem) a = Some v.
Proof.
intros H mem a v Hv Hr.
assert (B : forall k, (k < 8)%nat -> aview SEGS H mem (a + Z.of_nat k) = Some (le_byte v 8 k)).
{ intros k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. unfold le_byte. apply Z.mod_mod. lia. }
unfold rdword.
rewrite <- (Z.add_0_r a) at 1. change 0 with (Z.of_nat 0) at 1. rewrite (B 0%nat) by lia.
change 1 with (Z.of_nat 1). rewrite (B 1%nat) by lia. change 2 with (Z.of_nat 2) at 1. rewrite (B 2%nat) by lia.
change 3 with (Z.of_nat 3). rewrite (B 3%nat) by lia. change 4 with (Z.of_nat 4). rewrite (B 4%nat) by lia.
change 5 with (Z.of_nat 5). rewrite (B 5%nat) by lia. change 6 with (Z.of_nat 6). rewrite (B 6%nat) by lia.
change 7 with (Z.of_nat 7). rewrite (B 7%nat) by lia.
f_equal. apply le_bytes8. exact Hr.
Qed.

(* ---- the seats (run float state fx) ---- *)
Section run. Context {fx : YK11.FPState}.
Lemma o2_seat_a : forall (W : world SEGS) regs0 rg mem,
  getr rg 27 = w64 (SIGMA AS_round_trip_text + RT_O1 + RT_S11) -> prh_own W mem 0 ->
  st_ok_pi SEGS VAL (TE regs0 rg []) ss_O2a
    (restrict (w_H W) (mkst rg (Z_to_bv 64 (BASE + (RTT_PC + RT_O2))) mem (seg_rom SEGS))).
Proof.
intros W regs0 rg mem R27 [Hown _].
destruct o2_s11 as (S1 & S2 & S3).
set (E := TE regs0 rg []).
assert (X27 : bv_unsigned (ew E (xr 27)) = SIGMA AS_round_trip_text + RT_O1 + RT_S11).
{ unfold E, xr. rewrite (te_cur regs0 rg [] 27%bv 27) by reflexivity. rewrite R27. unfold w64.
  apply unsigned_lit_small. unfold RT_OWNOFF in S1. lia. }
unfold ss_O2a. apply ts_st_ok.
- apply te_regs_ok.
- vm_compute. reflexivity.
- constructor; [|constructor].
  apply (ts_rok E _ (xr 27) (SIGMA AS_round_trip_text + RT_O1 + RT_S11));
    [exact X27 | unfold RT_OWNOFF in *; lia | unfold RT_OWNOFF in *; lia | intros o Ho; lia |].
  constructor; [|constructor].
  apply (ts_chunk E _ _ RT_OWNOFF 1 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia |].
  replace (SIGMA AS_round_trip_text + RT_O1 + RT_S11 + RT_OWNOFF) with (@pi_g_own_ran_out prh_img_A) by lia.
  exact Hown.
- split; exact I.
- split; [exact I | split; exact I].
Qed.
Lemma o2_seat_r : forall (W : world SEGS) regs0 rg mem v, getr rg 10 = w64 v ->
  st_ok_pi SEGS VAL (TE regs0 rg []) (ss_O2r v)
    (restrict (w_H W) (mkst rg (Z_to_bv 64 (BASE + (RTT_PC + RT_O2R))) mem (seg_rom SEGS))).
Proof.
intros W regs0 rg mem v R10. unfold ss_O2r. apply ts_st_ok.
- apply regs_ok_pin; [apply te_regs_ok | intros X; discriminate X | exact R10].
- reflexivity.
- constructor.
- exact I.
- split; [exact I | split; exact I].
Qed.
End run.

(* ---- the cut's facts, at image A' ---- *)
Section cut. Context {fx : YK11.FPState}.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Variables (CTX0 : list (list Z)).
(* the allocator laws at the cf instance's head (engine interface, YCbqG.v AR_laws_x; owner the instance, the cf instance owner) *)
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
(* The kit's text of fuzz_alloc_ran_out (lib/A/PRH_FnAlloc.v at the batch kit's cut, blob 4d8aeba047e5; the text is unchanged from
   walkkit-next de5e947c224b), at any float state: the call is made at the cut's fxc (owned by the kit) *)
Hypothesis TFARO : forall fx' : YK11.FPState, tfuzz_alloc_ran_out_specX (fx := fx') B ARx SK.
#[local] Notation AJ := (ajournal_xR (SK := SK) SEGS B PST ARx RZW).

(* the entry's frame chain, extended by round_trip_text's own record (s0 = the entry sp) *)
Lemma o2_chain : forall D ly S Hp W mem md k pos sp,
  rtt_pre (fx := fx) B ARx CTX0 D -> rtt_J B ARx SK D ly S Hp W mem md k pos -> rtt_saved D W mem ->
  sp + 16 <= ri_sp D ->
  exists ch1, achain ly (aview SEGS (w_H W) mem) sp (ri_sp D) ch1.
Proof.
intros D ly S Hp W mem md k pos sp HPRE HJ HSV Hsp.
pose proof HPRE as (HFP & _).
destruct HFP as ((HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0) & _).
pose proof (ajxR_ly HJ) as Hly. pose proof (ajxR_hi HJ) as HKS.
pose proof Hstk0 as (Hal & HS0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
pose proof asan_consts as (C1 & _).
destruct (Z_lt_le_dec (ri_sp D) (ly_top (ri_ly D) - 16)) as [Hlt | Hge].
- exists ((ri_sp D, raZ (ri_regs D), s0Z (ri_regs D)) :: ri_ch D).
  apply (achain_ly_top (ri_ly D) ly); [exact Etop |].
  apply (achain_push (ri_ly D) (aview SEGS (w_H (ri_W D)) (ri_mem D)) (aview SEGS (w_H W) mem)
    (ri_sp D) (s0Z (ri_regs D)) (raZ (ri_regs D)) (ri_ch D) sp Hch0).
  + lia.
  + intros a Ha. apply HKS; [unfold ri_sp in *; lia | unfold ri_sp in *; lia].
  + apply o2_rdword; [exact (HSV 0%nat ltac:(lia)) |].
    pose proof (bv_unsigned_in_range 64 (getr (ri_regs D) 1%bv)) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr. exact Hr.
  + apply o2_rdword; [exact (HSV 1%nat ltac:(lia)) |].
    pose proof (bv_unsigned_in_range 64 (getr (ri_regs D) 8%bv)) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr. exact Hr.
  + exact Hra40.
  + unfold ri_sp in *; lia.
  + unfold ri_sp in *. pose proof (Z.div_mod (spZ (ri_regs D)) 16 ltac:(lia)) as E.
    rewrite Hal, Z.add_0_r in E. rewrite E.
    replace (16 * (spZ (ri_regs D) / 16)) with ((2 * (spZ (ri_regs D) / 16)) * 8) by lia.
    apply Z.mod_mul. lia.
  + exact Hlt.
  + exact Hsp.
- exists []. left. split; [right; left; rewrite Etop; lia | reflexivity].
Qed.

(* EVERY FAKE FRAME OF A NON-NEGATIVE CLASS IS 64-ALIGNED (the retirement of S10TxString.v's FAL64 stand-in, on
   WalkRtt102's derivation): frame_addr ly cid pos = ly_F ly + kFakeFramesOff + cid * 2 ^ kStackSizeLog +
   pos * fs_frame_bytes cid (YG0f.v:39-40), ly_F ly page aligned by layout_ok's lo_F_al (YG0f.v:313), the layout ok by
   AR_laws_x's field 18 alx_layout_ok, kFakeFramesOff = 576 * 64, 2 ^ kStackSizeLog = 16384 * 64, and
   fs_frame_bytes cid = Z.shiftl 64 cid = 64 * 2 ^ cid for 0 <= cid (YG00.v:560). *)
Lemma rtt_frame_al64 : forall ly S Hp W mem md cid pos, ARx ly S Hp W mem md -> 0 <= cid ->
  frame_addr ly cid pos mod 64 = 0.
Proof.
intros ly S Hp W mem md cid pos HAR Hc.
pose proof (alx_layout_ok SEGS B ARx LAWS ly S Hp W mem md HAR) as LO.
pose proof (lo_F_al _ LO) as FAL. unfold page_aligned in FAL.
apply Z.mod_divide in FAL as [q Hq]; [|lia].
assert (EB : fs_frame_bytes cid = 64 * 2 ^ cid) by (unfold fs_frame_bytes; rewrite Z.shiftl_mul_pow2 by exact Hc; ring).
assert (EK : kFakeFramesOff = 576 * 64) by reflexivity.
assert (ES : Z.shiftl 1 kStackSizeLog = 16384 * 64) by reflexivity.
unfold frame_addr, fs_frame_off. rewrite Hq, EK, ES, EB.
apply Z.mod_divide; [lia|]. exists (q * 64 + 576 + cid * 16384 + pos * 2 ^ cid). ring.
Qed.

(* the footprint of a tree whose root is in a live frame and whose blocks stay live, across a callee's journal *)
Lemma o2_foot_call : forall STK1 sp1 FP1 lyc Sc Hpc W memc mdc ly2 S2 Hp2 W2 mem2 md2 k1 mem3 p Dl cid pos',
  ARx lyc Sc Hpc W memc mdc ->
  AJ STK1 sp1 FP1 lyc Sc Hpc W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
  In (cid, pos') (frames Sc) -> frame_addr lyc cid pos' <= p -> p + 56 <= frame_addr lyc cid pos' + fs_frame_bytes cid ->
  (forall a k, In (a, k) Dl -> In (a - cf_head, k + cf_head) (ablocks B lyc Sc) /\
     In (a - cf_head, k + cf_head) (ablocks B ly2 S2)) ->
  (forall x, pj_footR p Dl x -> ~ inFP FP1 x) ->
  (forall x, mem3 x = mem2 x) ->
  forall x, pj_footR p Dl x -> 0 <= x < 2 ^ 64 /\ ~ in_img SEGS x /\ aview SEGS (w_H W2) mem3 x = aview SEGS (w_H W) memc x.
Proof.
intros STK1 sp1 FP1 lyc Sc Hpc W memc mdc ly2 S2 Hp2 W2 mem2 md2 k1 mem3 p Dl cid pos' HAR HJc Hin Hlo Hhi HB HFP Hm3 x Hx.
pose proof (ajxR_blk HJc) as HKB. pose proof (ajxR_frm HJc) as HKF.
pose proof cf_head_nonneg as C0. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
rewrite (o2_av_eq (w_H W2) mem2 mem3 Hm3 x).
pose proof Hx as Hx'.
destruct Hx as [Hx | ((a, k) & Hb & Hx)].
- destruct (alx_frames SEGS B ARx LAWS lyc Sc Hpc W memc mdc cid pos' HAR Hin) as (_ & Happ & _ & _).
  assert (Hni : ~ in_img SEGS x).
  { refine (proj2 (alx_client_img SEGS B ARx LAWS lyc Sc Hpc W memc mdc x HAR _)).
    right. left. exists cid, pos'. split; [exact Hin | lia]. }
  split; [unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ; lia|].
  split; [exact Hni|].
  apply (HKF cid pos' x Hin); [left; unfold frame_rng, in_zr; cbn [fst snd]; lia | exact (HFP x Hx')].
- unfold pj_holdsR in Hx. cbn [fst snd] in Hx.
  destruct (HB a k Hb) as [Hb1 Hb2].
  assert (Hrs : k + cf_head <= req_size (k + cf_head)) by (unfold req_size; destruct (Z.eqb_spec (k + cf_head) 0); lia).
  destruct (alx_blocks SEGS B ARx LAWS lyc Sc Hpc W memc mdc _ _ HAR Hb1) as (_ & B4096 & BC & _).
  assert (Hni : ~ in_img SEGS x).
  { refine (proj2 (alx_client_img SEGS B ARx LAWS lyc Sc Hpc W memc mdc x HAR _)).
    left. exists (a - cf_head), (k + cf_head). split; [exact Hb1 | lia]. }
  split; [lia|]. split; [exact Hni|].
  replace x with (a - cf_head + (x - (a - cf_head))) by lia.
  apply (HKB (a - cf_head) (k + cf_head) (x - (a - cf_head)) Hb1 Hb2); [lia|].
  replace (a - cf_head + (x - (a - cf_head))) with x by lia. exact (HFP x Hx').
Qed.

(* the tree visibility of a harness tree at any allocator state, from the laws (blocks, head shadow, tail) *)
Lemma o2_tv_laws : forall ly S Hp W mem md W0 mem0 Dl,
  ARx ly S Hp W mem md -> YGcfTreeVis.tree_vis_cf SEGS W0 mem0 Dl ->
  (forall a k, In (a, k) Dl -> In (a - cf_head, k + cf_head) (ablocks B ly S) /\ In (a - cf_head) Hp) ->
  YGcfTreeVis.tree_vis_cf SEGS W mem Dl.
Proof.
intros ly S Hp W mem md W0 mem0 Dl HAR HTV HB a k Hin.
destruct (HTV a k Hin) as (T1 & T2 & T3 & T4 & _ & _ & _).
destruct (HB a k Hin) as [Hab Hhp].
pose proof cf_head_nonneg as C0.
assert (Hrs : k + cf_head <= req_size (k + cf_head)) by (unfold req_size; destruct (Z.eqb_spec (k + cf_head) 0); lia).
destruct (alx_hshadow SEGS B ARx LAWS ly S Hp W mem md (a - cf_head) (k + cf_head) HAR Hab Hhp) as [HBS HHV].
destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md (a - cf_head) (k + cf_head) HAR Hab) as (_ & _ & _ & _ & BP & _).
replace (a - cf_head + cf_head) with a in HBS, HHV by lia.
split; [exact T1|]. split; [exact T2|]. split; [exact T3|]. split; [exact T4|].
split; [eapply block_shadow_range; [exact HBS | lia | lia]|].
split.
- intros Hk.
  assert (HH : shadow_hull_vis (aview SEGS (w_H W) mem) a (req_size (k + cf_head) - cf_head)) by (apply HHV; lia).
  apply (o2_hull_sub _ _ _ a k HH); lia.
- intros x Hx. destruct (Z_lt_le_dec x (a - cf_head + req_size (k + cf_head))) as [Hl | Hg].
  + apply (aview_some_of_apresent SEGS). exact (proj1 (BP x ltac:(lia))).
  + apply (alx_blocks_tail SEGS B ARx LAWS ly S Hp W mem md (a - cf_head) (k + cf_head) x HAR Hab). split; [exact Hg|].
    apply (Z.lt_le_trans _ ((a + k + 7) / 8 * 8)); [lia|].
    apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; lia.
Qed.

(* ---- the carried state across a run that writes nothing (the state S, so the wild traces, unchanged) ---- *)
Lemma o2_carry_eqmem : forall D fxc ly S Hp W regs mem md k pos regs' mem' md',
  rtt_carry (fx := fx) B ARx SK D fxc ly S Hp W regs mem md k pos ->
  (forall x, mem' x = mem x) ->
  rtt_J B ARx SK D ly S Hp W mem' md' k pos ->
  YAkMemnorm.memnorm SEGS mem' ->
  (forall r : bv 5, In r RTT_CREGS -> getr regs' r = getr regs r) ->
  rtt_carry (fx := fx) B ARx SK D fxc ly S Hp W regs' mem' md' k pos.
Proof.
intros D fxc ly S Hp W regs mem md k pos regs' mem' md' HC Hm HJ' HMN' Hr.
destruct HC as (HFX & HJ & HFR & HSV & HCR & HMN & HROD & HROOM & HDOC & HTV & HWD).
pose proof (o2_av_eq (w_H W) mem mem' Hm) as Hav.
split; [exact HFX|]. split; [exact HJ'|].
split.
{ destruct HFR as (F1 & F2 & F3 & F4). split; [exact F1|]. split; [exact F2|]. split.
  - rewrite <- F3. apply ts_rdword_keep. intros j Hj. apply Hav.
  - intros a Ha. destruct (F4 a Ha) as [Hh [b Hb]]. split; [exact Hh|]. exists b. rewrite Hm. exact Hb. }
split.
{ intros j Hj. apply (ts_vm_av (w_H W) (w_H W) mem mem'); [intros j' _; apply Hav | exact (HSV j Hj)]. }
split.
{ pose proof HCR as (R2 & R8 & R9 & R18 & R19 & R20 & R25 & R26 & R3 & R4).
  split; [rewrite (Hr 2%bv) by o2in; exact R2|]. split; [rewrite (Hr 8%bv) by o2in; exact R8|].
  split; [rewrite (Hr 9%bv) by o2in; exact R9|]. split; [rewrite (Hr 18%bv) by o2in; exact R18|].
  split; [rewrite (Hr 19%bv) by o2in; exact R19|]. split; [rewrite (Hr 20%bv) by o2in; exact R20|].
  split; [rewrite (Hr 25%bv) by o2in; exact R25|]. split; [rewrite (Hr 26%bv) by o2in; exact R26|].
  split; [rewrite (Hr 3%bv) by o2in; exact R3|]. rewrite (Hr 4%bv) by o2in; exact R4. }
split; [intros _; exact HMN'|].
split; [intros a H1 H2 H3; rewrite Hav; exact (HROD a H1 H2 H3)|].
split; [exact HROOM|].
split; [exact (o2_tree_eq W mem mem' _ _ _ _ Hm HDOC)|].
split; [|exact HWD].
intros a0 k0 Hin. destruct (HTV a0 k0 Hin) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
split; [exact T1|]. split; [exact T2|]. split; [exact T3|]. split; [exact T4|].
split; [apply (range_addressable_agree (aview SEGS (w_H W) mem)); [intros x _; apply Hav | exact T5]|].
split; [intros Hk s Hs; rewrite Hav; exact (T6 Hk s Hs)|].
intros x Hx. rewrite Hav. exact (T7 x Hx).
Qed.

(* ---- the carried state across a kit call (callee journal at RT_R sp0, any footprint the carried bytes avoid),
   then a run that writes nothing; the callee's journal is empty-budget, so the wild traces stay rtt_wild's
   (Rtt102Cut.rtt_wild_keep0) ---- *)
Lemma o2_carry_call : forall D fxc lyc Sc Hpc W regsc memc mdc k pos STK1 FP1 ly2 S2 Hp2 W2 regs2 mem2 md2 k1 k'
  regs3 mem3 md3,
  rtt_pre (fx := fx) B ARx CTX0 D ->
  rtt_carry (fx := fx) B ARx SK D fxc lyc Sc Hpc W regsc memc mdc k pos ->
  AJ STK1 (RT_R (ri_sp D)) FP1 lyc Sc Hpc W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
  ~ YI16.sink_open_fp FP1 ->
  (forall a, frame_addr lyc RT_CID pos + RT_FLAGP <= a < frame_addr lyc RT_CID pos + RT_FLAGP + 8 -> ~ inFP FP1 a) ->
  (forall x, pj_footR (ri_doc D) (ri_D D) x -> ~ inFP FP1 x) ->
  (forall a k0, In (a, k0) (ri_D D) -> In (a - cf_head, k0 + cf_head) (ablocks B lyc Sc)) ->
  (forall a k0, In (a, k0) (ri_D D) -> In (a - cf_head, k0 + cf_head) (ablocks B ly2 S2) /\ In (a - cf_head) Hp2) ->
  aregs_preserved regsc regs2 ->
  (YAkMemnorm.memnorm SEGS (ri_mem D) -> YAkMemnorm.memnorm SEGS mem3) ->
  rtt_room D S2 ->
  (forall x, mem3 x = mem2 x) ->
  (forall r : bv 5, In r RTT_CREGS -> getr regs3 r = getr regs2 r) ->
  rtt_J B ARx SK D ly2 S2 Hp2 W2 mem3 md3 k' pos ->
  rtt_carry (fx := fx) B ARx SK D fxc ly2 S2 Hp2 W2 regs3 mem3 md3 k' pos.
Proof.
intros D fxc lyc Sc Hpc W regsc memc mdc k pos STK1 FP1 ly2 S2 Hp2 W2 regs2 mem2 md2 k1 k' regs3 mem3 md3
  HPRE HC HJc HSO HFPf HFPd HBc HB2 HP HMN3 HRM Hm3 HR3 HJ3.
destruct HC as (HFX & HJ & HFR & HSV & HCR & HMN & HROD & HROOM & HDOC & HTV & HWD).
pose proof (ajxR_ar HJ) as HARc. pose proof (ajxR_ly HJ) as Hly0c.
pose proof (ajxR_ar HJ3) as HAR3.
pose proof (ajxR_ly HJc) as Hlyc. pose proof (ajxR_frs HJc) as Hfrc. pose proof (ajxR_hi HJc) as HKS.
pose proof (ajxR_img HJc) as HKI. pose proof (ajxR_frm HJc) as HKF.
pose proof HPRE as (HFP0 & _ & _ & _ & _ & _ & _ & _ & _ & HTREE & _).
pose proof HFP0 as ((HAR0 & _ & _ & _ & _ & Hstk0 & _) & _).
pose proof Hstk0 as (Hal0 & HSTK0 & Hceil0 & Hslo0 & Hshi0 & H470 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct o2_stk as [HSTR _].
destruct (o2_R (ri_sp D) Hal0) as (_ & [HRlo HRhi] & _).
destruct (alx_layout SEGS B ARx LAWS lyc Sc Hpc W memc mdc ly2 HARc Hlyc) as (_ & EFA & _).
assert (EFL : forall cid p, flag_addr ly2 cid p = flag_addr lyc cid p).
{ intros cid p. unfold flag_addr. pose proof Hlyc as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
pose proof (o2_av_eq (w_H W2) mem2 mem3 Hm3) as Hav3.
destruct HFR as (F1 & F2 & F3 & F4).
assert (Hin1 : In (RT_CID, pos) (frames Sc)) by (rewrite F1; left; reflexivity).
assert (Hin2 : In (RT_CID, pos) (frames S2)) by (rewrite Hfrc; exact Hin1).
assert (FB1 : fs_frame_bytes RT_CID = 128) by reflexivity.
split; [exact HFX|]. split; [exact HJ3|].
split.
{ split; [rewrite Hfrc; exact F1|]. split; [exact F2|]. split.
  - rewrite EFA, EFL. rewrite <- F3. apply ts_rdword_keep. intros j Hj. rewrite Hav3.
    apply (HKF RT_CID pos); [exact Hin1 | left; unfold frame_rng, in_zr; cbn [fst snd]; rewrite FB1; unfold RT_FLAGP; lia |].
    apply HFPf. lia.
  - intros a Ha.
    destruct (alx_frames SEGS B ARx LAWS ly2 S2 Hp2 W2 mem3 md3 RT_CID pos HAR3 Hin2) as (_ & _ & Hpr & _).
    exact (proj1 (Hpr a Ha)). }
split.
{ intros j Hj. apply (ts_vm_av (w_H W) (w_H W2) memc mem3); [|exact (HSV j Hj)].
  intros i Hi. rewrite Hav3. apply HKS; unfold ri_sp in *; lia. }
split.
{ pose proof HCR as (R2 & R8 & R9 & R18 & R19 & R20 & R25 & R26 & R3 & R4).
  assert (G : forall r : bv 5, In r RTT_CREGS -> getr regs3 r = getr regsc r).
  { intros r Hr. rewrite (HR3 r Hr). apply (ts_ap regsc regs2 r HP).
    cbv [RTT_CREGS In] in Hr. repeat (destruct Hr as [<- | Hr]; [ts_cs|]). destruct Hr. }
  unfold rtt_cregs. cbv zeta. rewrite !EFA.
  split; [rewrite (G 2%bv) by o2in; exact R2|]. split; [rewrite (G 8%bv) by o2in; exact R8|].
  split; [rewrite (G 9%bv) by o2in; exact R9|]. split; [rewrite (G 18%bv) by o2in; exact R18|].
  split; [rewrite (G 19%bv) by o2in; exact R19|]. split; [rewrite (G 20%bv) by o2in; exact R20|].
  split; [rewrite (G 25%bv) by o2in; exact R25|]. split; [rewrite (G 26%bv) by o2in; exact R26|].
  split; [rewrite (G 3%bv) by o2in; exact R3|]. rewrite (G 4%bv) by o2in; exact R4. }
split; [exact HMN3|].
split.
{ intros a Hro Hno Her. rewrite Hav3.
  rewrite (HKI a (o2_ro_img a Hro) Hno Her (fun Hp => o2_pst_ro a Hp Hro) (fp_spares_closed (SK := SK) FP1 a HSO)).
  exact (HROD a Hro Hno Her). }
split; [exact HRM|].
split.
{ destruct HTREE as (_ & HDsub & _ & (_ & (cid & pos' & Hcf & Hc1 & Hc2) & _)).
  destruct (alx_layout SEGS B ARx LAWS (ri_ly D) (ri_S D) (ri_Hp D) (ri_W D) (ri_mem D) (ri_md D) lyc HAR0 Hly0c)
    as (_ & EFA0 & _).
  apply (o2_tree_keep W W2 memc mem3 _ _ _ _ HDOC).
  apply (o2_foot_call STK1 (RT_R (ri_sp D)) FP1 lyc Sc Hpc W memc mdc ly2 S2 Hp2 W2 mem2 md2 k1 mem3
    (ri_doc D) (ri_D D) cid pos' HARc HJc).
  - rewrite F1. right. exact Hcf.
  - rewrite EFA0. exact Hc1.
  - rewrite EFA0. exact Hc2.
  - intros a k0 Hin. split; [exact (HBc a k0 Hin) | exact (proj1 (HB2 a k0 Hin))].
  - exact HFPd.
  - exact Hm3. }
split; [exact (o2_tv_laws ly2 S2 Hp2 W2 mem3 md3 W memc (ri_D D) HAR3 HTV HB2)|].
(* the wild traces: the callee stored none (its journal from Sc is at the empty budget) *)
eapply (rtt_wild_keep0 B ARx SK D Sc); [| exact HWD | exact HJc]. reflexivity.
Qed.

(* back's shadow (rtt_back) across a call whose footprint misses the frame's shadow *)
Lemma o2_back_call : forall lyc Sc Hpc W memc mdc pos STK1 sp1 FP1 ly2 S2 Hp2 W2 mem2 md2 k1 mem3,
  ARx lyc Sc Hpc W memc mdc -> In (RT_CID, pos) (frames Sc) ->
  AJ STK1 sp1 FP1 lyc Sc Hpc W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
  (forall a, in_zr a (shadow_addr (frame_addr lyc RT_CID pos), fs_frame_bytes RT_CID / 8) -> ~ inFP FP1 a) ->
  (forall x, mem3 x = mem2 x) ->
  (forall cid p, frame_addr ly2 cid p = frame_addr lyc cid p) ->
  rtt_back lyc W memc pos -> rtt_back ly2 W2 mem3 pos.
Proof.
intros lyc Sc Hpc W memc mdc pos STK1 sp1 FP1 ly2 S2 Hp2 W2 mem2 md2 k1 mem3 HAR Hin HJc HFPs Hm3 EFA HBK.
unfold rtt_back in *. rewrite EFA.
destruct (alx_frames SEGS B ARx LAWS lyc Sc Hpc W memc mdc RT_CID pos HAR Hin) as (Hal32 & _).
pose proof (ajxR_frm HJc) as HKF.
assert (FB1 : fs_frame_bytes RT_CID = 128) by reflexivity.
apply (range_addressable_agree (aview SEGS (w_H W) memc)); [|exact HBK].
intros x Hx. rewrite (o2_av_eq (w_H W2) mem2 mem3 Hm3).
unfold RT_BACK in Hx.
pose proof (o2_sh_in (frame_addr lyc RT_CID pos) x Hal32 ltac:(lia)) as Hs.
apply (HKF RT_CID pos); [exact Hin | right; unfold in_zr; cbn [fst snd]; rewrite FB1; lia |].
apply HFPs. unfold in_zr; cbn [fst snd]; rewrite FB1; lia.
Qed.

(* the ledger's blocks of the document tree, at a state whose ledger list holds the entry's *)
Lemma o2_dblocks : forall D ly S Hp W mem Lamc peak cnt fail ran most own,
  rtt_pre (fx := fx) B ARx CTX0 D -> (forall bk, In bk (ri_Lam D) -> In bk Lamc) ->
  prh_ledger B ly S Hp W mem Lamc peak cnt fail ran most own ->
  forall a k0, In (a, k0) (ri_D D) -> In (a - cf_head, k0 + cf_head) (ablocks B ly S) /\ In (a - cf_head) Hp.
Proof.
intros D ly S Hp W mem Lamc peak cnt fail ran most own HPRE Hsub HL a k0 Hin.
pose proof HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HTREE & _).
destruct HTREE as (_ & HDsub & _).
destruct (prh_ledger_hblock B ly S Hp W mem Lamc peak cnt fail ran a k0 most own HL (Hsub _ (HDsub _ Hin)))
  as (_ & H1 & H2 & _).
exact (conj H1 H2).
Qed.
Lemma o2_led_eq : forall ly S Hp (W : world SEGS) m m' Lam peak cnt fail ran most own, (forall x, m' x = m x) ->
  prh_ledger B ly S Hp W m Lam peak cnt fail ran most own -> prh_ledger B ly S Hp W m' Lam peak cnt fail ran most own.
Proof.
intros ly S Hp W m m' Lam peak cnt fail ran most own Hm HL.
apply (prh_ledger_kept B ly S Hp W m ly S Hp W m' Lam peak cnt fail ran most own HL).
- intros a _. apply (o2_mb_eq (w_H W) m m' Hm).
- intros a k i _ _. apply (o2_mb_eq (w_H W) m m' Hm).
- intros a k _ H. exact H.
- apply Permutation_refl.
Qed.

(* ==== THE STRETCH ==== *)
Theorem rtt_seg_o2_A : @RTT_SEG_O2 fx rc ci cp prh_img_A RL A_prog_listing PI_prog_A B ARx SK CTX0.
Proof.
unfold RTT_SEG_O2.
intros SCK D HPRE fxc ly S Hp W regs mem md k pos HO2.
(* the goal YA0nH.SRr' SEGS RZ_cf is YA0nH.SRrG SEGS RZW, the form the R runners and the R call rule conclude *)
unfold YA0nH.SRr'.
pose proof HO2 as (HC & HBK & HS11 & HCK & R23 & rc0 & Lamr & peakr & cntr & ranr & R24 & Hrc & HLED & HRB).
pose proof HC as (HFX & HJ & HFR & HSV & HCR & HMN & HROD & HROOM & HDOC & HTV & HWD).
pose proof HCR as (R2 & R8 & R9 & R18 & R19 & R20 & R25 & R26 & R3 & R4).
pose proof HPRE as (HFP0 & HMN0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HRAN0 & _).
(* the byte the +0x328 lbu reads: the ledger's g_own_ran_out field, 0 at RT_O2 *)
pose proof (PRH_Base.prh_ledger_own B _ _ _ _ _ _ _ _ _ _ _ _ (proj1 HLED)) as HOWN.
pose proof HFP0 as ((HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0) & _).
pose proof Hstk0 as (Hal0 & HSTK0 & Hceil0 & Hslo0 & Hshi0 & H470 & _).
pose proof (HMN HMN0) as HPM.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof o2_base as HB.
destruct o2_stk as [HSTR HSTF].
destruct (o2_R (ri_sp D) Hal0) as (HR32 & [HRlo HRhi] & HR16).
(* the read-back's granted outcome (rtt_rb): ranr = ran = 0 and back over its blocks Db, with back's free order at
   every depth bound and its capacities *)
pose proof HRB as (Hr0 & Hrc0 & Hcn & HPOS & Db & HPL & HNEW & HSZ & HRDB & (F & HFO & HFOM) & HLEN & HPA & HTB & HFOA &
  HNC).
assert (Er : ranr = 0) by (rewrite Hr0; exact HRAN0).
assert (HLsub : forall bk, In bk (ri_Lam D) -> In bk Lamr).
{ intros bk Hbk. apply (Permutation_in _ (Permutation_sym HPL)). apply in_or_app. right. exact Hbk. }
assert (HSO0 : ~ YI16.sink_open_fp []) by (intros (r & Hr & _); destruct Hr).
(* ---- the run from RT_O2 to the call ---- *)
rewrite <- (o2_pc RT_O2).
pose proof (o2_seat_a (fx := fxc) W (ri_regs D) regs mem HS11 HOWN) as HS.
assert (SHOK : sh_ok SEGS (SLit 0) [] (TE (ri_regs D) regs []) (mrestrict (w_H W) mem)) by apply Forall_nil.
assert (HEI : img_env VAL A_LIM (TE (ri_regs D) regs [])) by apply te_env.
pose (RUN := @paj_run_x_invR fxc rc SK A_prog_listing PL_prog_A PI_prog_A B PST ARx _ LAWS (YAkMemnorm.memnorm SEGS)
  (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS) RZW (YA0nH.wle'_refl SEGS YGcfRehidePost.RZ_cf)
  (YA0nH.wle'_trans SEGS YGcfRehidePost.RZ_cf)).
paj_run_tok_x_invR RUN HS HJ SHOK HPM (0, 0).
{ cbv [ss_O2a ss_mem]. apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
assert (Hm1 : forall x, ms_mem ms x = mem x).
{ intros x. apply HF. intros (r & Hr & Hx). cbv [ss_O2a ss_mem In] in Hr. destruct Hr as [Hr | []]. subst r.
  cbn [YP09.r_wlo YP09.r_whi] in Hx. lia. }
assert (HRK1 : forall r : bv 5, In r RTT_CREGS -> getr (ms_regs ms) r = getr regs r).
{ intros r Hr. cbv [RTT_CREGS In] in Hr. repeat (destruct Hr as [<- | Hr]; [o2keep HS|]). destruct Hr. }
assert (Z23 : getr (ms_regs ms) 23 = getr regs 23) by o2keep HS.
assert (Z24 : getr (ms_regs ms) 24 = getr regs 24) by o2keep HS.
prreg HS (1%bv : bv 5) Q1.
lazymatch goal with |- YA0nH.SRrG _ _ _ (mkCfg _ ?mdq) _ =>
  pose proof (o2_carry_eqmem D fxc ly S Hp W regs mem md k pos (ms_regs ms) (ms_mem ms) mdq HC Hm1 HJ HPM HRK1) as HC1
end.
pose proof HC1 as (_ & HJ1 & HFR1 & HSV1 & HCR1 & _ & HROD1 & _ & _ & _ & _).
pose proof HCR1 as (Q2 & Q8 & _ & _ & _ & _ & _ & _ & Q3 & Q4).
pose proof (ajxR_ar HJ1) as HARc.
assert (Hsp1 : spZ (ms_regs ms) = RT_R (ri_sp D)).
{ unfold spZ. rewrite Q2. unfold w64. rewrite unsigned_lit_small; [reflexivity|]. unfold ri_sp in *. lia. }
assert (Hs0 : s0Z (ms_regs ms) = ri_sp D).
{ unfold s0Z. rewrite Q8. unfold w64. rewrite unsigned_lit_small; [reflexivity|]. unfold ri_sp in *. lia. }
destruct (o2_chain D ly S Hp W (ms_mem ms) _ k pos (RT_R (ri_sp D)) HPRE HJ1 HSV1 ltac:(lia)) as (ch1 & Hch1).
pose proof (o2_led_eq ly S Hp W mem (ms_mem ms) Lamr peakr cntr SIZE_MAXZ ranr (ri_most D) 0 Hm1 (proj1 HLED))
  as HLED1.
(* ---- the call of fuzz_alloc_ran_out: the R rule at RZW applies to rtt_J, the journal from the entry with its depot
   moved to the call state's ---- *)
eapply (YA0nH.SRrG_bind SEGS RZW (YA0nH.wle'_trans SEGS YGcfRehidePost.RZ_cf)).
{ lazymatch goal with |- YA0nH.SRrG _ _ _ (mkCfg ?msq ?mdq) _ =>
  eapply (aj_call_x_spR (fx := fxc) (SK := SK) SEGS B PST ARx LAWS (@pa_segs_low _ _ PI_prog_A) RZW
    (YA0nH.wle'_refl SEGS YGcfRehidePost.RZ_cf) (YA0nH.wle'_trans SEGS YGcfRehidePost.RZ_cf) W _ _ msq
    STK_round_trip_text (ri_sp D) (ri_FP D) (ri_ly D) (set_depot (st_depot S) (ri_S D)) (ri_Hp D) (ri_W D) (ri_mem D)
    (ri_md D) [(RT_CID, pos)] ly S Hp mdq k STK_fuzz_alloc_ran_out [] (RT_R (ri_sp D) - ri_sp D) _ ch1 _ HS eq_refl HJ)
  end.
  - rewrite Hsp1. lia.
  - exact HR16.
  - lia.
  - rewrite HSTF. lia.
  - rewrite HSTF, HSTR. lia.
  - rewrite (HRK1 3%bv) by o2in. exact R3.
  - rewrite (HRK1 4%bv) by o2in. exact R4.
  - exact Q1.
  - apply (ret_ok_codeptr_v (PI := PI_prog_A)); [lia | reflexivity].
  - rewrite unsigned_lit_small by lia. lia.
  - replace (ri_sp D + (RT_R (ri_sp D) - ri_sp D)) with (RT_R (ri_sp D)) by lia. rewrite Hs0. exact Hch1.
  - intros HPRE1.
    (* the plain text (its SRr, its post apost_base_x at wle), lifted to RZW (recipe R5: YA0nH.SRr_SRrG,
       YCbqG.apost_base_x_R_lift at YA0nH.wle_wle') *)
    eapply (YA0nH.SRrG_mono SEGS RZW).
    { apply (YA0nH.SRr_SRrG SEGS RZW (YA0nH.wle_wle' SEGS YGcfRehidePost.RZ_cf)).
      (* fpre: the frame, the read-only view, the stack room, the return address, and K0-FRM0-ENTRY's frm = 0 at the
         call's float state fxc, from rtt_carry's rtt_fx *)
      refine (TFARO fxc ly S Hp W _ _ _ ch1 Lamr peakr cntr SIZE_MAXZ ranr (ri_most D) 0
        (conj HPRE1 (conj HROD1 (conj _ (conj _ (proj1 HFX))))) HLED1).
      + pose proof (ajxR_ly HJ1) as Hly1. pose proof Hly1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eshi & _).
        rewrite Hsp1, Eshi. unfold ri_sp in *. lia.
      + unfold raZ. rewrite Q1. rewrite unsigned_lit_small by lia. lia. }
    intros W' c' _ HP'.
    exact (apost_base_x_R_lift (SK := SK) SEGS B PST ARx RZW (YA0nH.wle_wle' SEGS YGcfRehidePost.RZ_cf)
      _ _ _ _ _ _ _ _ _ _ _ _ HP').
  - intros a (r & Hr & _). destruct Hr. }
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ2 & HJc & HP2 & HQ2).
destruct HQ2 as ((HRL2 & H10 & EHp & ES & EAB & HLED2) & HMN2).
(* fuzz_alloc_ran_out keeps S: the caller journal rtt_Jc D S .. ly2 S2 .. is rtt_J at ly2, S *)
subst S2. subst Hp2.
replace (ri_sp D + (RT_R (ri_sp D) - ri_sp D)) with (RT_R (ri_sp D)) in HJc by lia.
pose proof (ajxR_ly HJc) as Hlyc.
destruct (alx_layout SEGS B ARx LAWS ly S Hp W (ms_mem ms) _ ly2 HARc Hlyc) as (_ & EFA & _).
pose proof (HMN2 HPM) as HPM2.
pose proof (o2_dblocks D ly S Hp W (ms_mem ms) Lamr peakr cntr SIZE_MAXZ ranr (ri_most D) 0 HPRE HLsub HLED1) as HBc0.
pose proof (o2_dblocks D ly2 S Hp W2 mem2 Lamr peakr cntr SIZE_MAXZ ranr (ri_most D) 0 HPRE HLsub HLED2) as HB2.
assert (HBc : forall a k0, In (a, k0) (ri_D D) -> In (a - cf_head, k0 + cf_head) (ablocks B ly S))
  by (intros a k0 Hin; exact (proj1 (HBc0 a k0 Hin))).
assert (HFPf0 : forall a, frame_addr ly RT_CID pos + RT_FLAGP <= a < frame_addr ly RT_CID pos + RT_FLAGP + 8 ->
  ~ inFP [] a) by (intros a _; apply inFP_nil).
assert (HFPd0 : forall x, pj_footR (ri_doc D) (ri_D D) x -> ~ inFP [] x) by (intros x _; apply inFP_nil).
rename ms into ms1. clear HS SHOK HEI HJ HPM HF HFr HG.
(* ---- the return site: a0 = ranr = 0, so `bnez a0` at +0x338 falls through to RT_CK ---- *)
lazymatch goal with |- YA0nH.SRrG _ _ _ (mkCfg (mkst _ (Z_to_bv 64 ?p) _ _) _) _ =>
  replace p with (BASE + (RTT_PC + RT_O2R)) by (vm_compute; reflexivity) end.
clear Hr0. subst ranr.
pose (RUNTO := @paj_run_to_x_invR fxc rc SK A_prog_listing PL_prog_A PI_prog_A B PST ARx _ LAWS
  (YAkMemnorm.memnorm SEGS) (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS) RZW (YA0nH.wle'_refl SEGS YGcfRehidePost.RZ_cf)
  (YA0nH.wle'_trans SEGS YGcfRehidePost.RZ_cf)).
pose proof (o2_seat_r (fx := fxc) W2 (ri_regs D) regs2 mem2 0 H10) as HS.
assert (SHOK : sh_ok SEGS (SLit 0) [] (TE (ri_regs D) regs2 []) (mrestrict (w_H W2) mem2)) by apply Forall_nil.
assert (HEI : img_env VAL A_LIM (TE (ri_regs D) regs2 [])) by apply te_env.
paj_run_to_tok_x_invR RUNTO HS HJ2 SHOK HPM2 (0, 0) (RTT_PC + RT_CK).
{ cbv [ss_O2r ss_mem]. apply awr_ok_nil. }
assert (Hm4 : forall x, ms_mem ms x = mem2 x).
{ intros x. apply HF. intros (r & Hr & _). cbv [ss_O2r ss_mem In] in Hr. destruct Hr. }
assert (HRK4 : forall r : bv 5, In r RTT_CREGS -> getr (ms_regs ms) r = getr regs2 r).
{ intros r Hr. cbv [RTT_CREGS In] in Hr. repeat (destruct Hr as [<- | Hr]; [o2keep HS|]). destruct Hr. }
assert (Y23 : getr (ms_regs ms) 23 = getr regs2 23) by o2keep HS.
assert (Y24 : getr (ms_regs ms) 24 = getr regs2 24) by o2keep HS.
pmkst HS.
lazymatch goal with |- YA0nH.SRrG _ _ _ (mkCfg (mkst _ (Z_to_bv 64 ?p) _ _) _) _ =>
  replace p with (SIGMA AS_round_trip_text + RT_CK) by (vm_compute; reflexivity) end.
eapply (SCK D HPRE fxc ly2 S Hp W2 (ms_regs ms) (ms_mem ms) _ (k + k1) pos).
split.
{ exact (o2_carry_call D fxc ly S Hp W (ms_regs ms1) (ms_mem ms1) _ k pos STK_fuzz_alloc_ran_out [] ly2 S Hp W2 regs2
    mem2 md2 k1 (k + k1) (ms_regs ms) (ms_mem ms) _ HPRE HC1 HJc HSO0 HFPf0 HFPd0 HBc HB2 HP2
    (fun _ => HPM2) HROOM Hm4 HRK4 HJ2). }
split.
{ assert (HinF : In (RT_CID, pos) (frames S)) by (rewrite (proj1 HFR1); left; reflexivity).
  assert (HBK1 : rtt_back ly W (ms_mem ms1) pos).
  { unfold rtt_back in *. apply (range_addressable_agree (aview SEGS (w_H W) mem)); [|exact HBK].
    intros x _. apply (o2_av_eq (w_H W) mem (ms_mem ms1) Hm1). }
  exact (o2_back_call ly S Hp W (ms_mem ms1) _ pos STK_fuzz_alloc_ran_out (RT_R (ri_sp D)) [] ly2 S Hp W2 mem2 md2 k1
    (ms_mem ms) HARc HinF HJc (fun a _ => inFP_nil a) Hm4 EFA HBK1). }
split.
{ rewrite Y23. rewrite (ts_ap _ _ 23%bv HP2) by ts_cs. rewrite Z23, R23, EFA. reflexivity. }
split.
{ rewrite Y24. rewrite (ts_ap _ _ 24%bv HP2) by ts_cs. rewrite Z24, R24, Hrc0. reflexivity. }
exists Lamr, peakr.
subst cntr.
split.
{ split; [|exact (proj2 HLED)]. rewrite HRAN0.
  exact (o2_led_eq ly2 S Hp W2 mem2 (ms_mem ms) Lamr peakr _ SIZE_MAXZ 0 (ri_most D) 0 Hm4 HLED2). }
(* back's footprint: in round_trip_text's live frame and in the blocks Db, which fuzz_alloc_ran_out keeps *)
assert (HFT : forall x, pj_footR (frame_addr ly RT_CID pos + RT_BACK) Db x ->
  0 <= x < 2 ^ 64 /\ ~ in_img SEGS x /\ aview SEGS (w_H W2) (ms_mem ms) x = aview SEGS (w_H W) (ms_mem ms1) x).
{ apply (o2_foot_call STK_fuzz_alloc_ran_out (RT_R (ri_sp D)) [] ly S Hp W (ms_mem ms1) _ ly2 S Hp W2 mem2 md2 k1
    (ms_mem ms) (frame_addr ly RT_CID pos + RT_BACK) Db RT_CID pos HARc HJc).
  - rewrite (proj1 HFR1). left. reflexivity.
  - unfold RT_BACK. lia.
  - unfold RT_BACK. change (fs_frame_bytes RT_CID) with 128. lia.
  - intros a k0 Hin. rewrite EAB.
    assert (Hab : In (a - cf_head, k0 + cf_head) (ablocks B ly S)).
    { apply (Permutation_in _ (Permutation_sym HPA)). apply in_or_app. right.
      unfold ck_hblks. exact (in_map (fun ak : Z * Z => (fst ak - cf_head, snd ak + cf_head)) Db (a, k0) Hin). }
    split; exact Hab.
  - intros x _. apply inFP_nil.
  - exact Hm4. }
unfold rtt_rb. cbv zeta. rewrite EFA.
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
(* the position after rt_text: fuzz_alloc_ran_out keeps S, so the read-back's position is the CK state's *)
split; [exact HPOS|].
exists Db. split; [exact HPL|]. split; [exact HNEW|]. split; [exact HSZ|]. split; [exact HRDB|].
split.
{ exists F. split; [|exact HFOM].
  pose proof (PRH_PjOrder.pj_foR_lblk SEGS _ _ _ _ _ _ HFO) as HFOL.
  pose proof (PRH_PjOrder.pj_foR_frame SEGS _ _ _ _ _ _ _ _ HFO HFOL (o2_agree_eq (w_H W) mem (ms_mem ms1) _ Hm1))
    as HFO1.
  exact (PRH_PjOrder.pj_foR_frame SEGS _ _ _ _ _ _ _ _ HFO1 HFOL (o2_agree_keep W W2 (ms_mem ms1) (ms_mem ms) _ HFT)). }
split; [exact HLEN|].
split; [rewrite EAB; exact HPA|].
pose proof (o2_tree_eq W mem (ms_mem ms1) _ _ _ _ Hm1 HTB) as HTB1.
split; [exact (o2_tree_keep W W2 (ms_mem ms1) (ms_mem ms) _ _ _ _ HTB1 HFT)|].
(* back's free order at every depth bound (the frame of the DOC_D one, at each bound) *)
split.
{ intros Hhd nn Hnn. destruct (HFOA Hhd nn Hnn) as (Fn & HFOn & HFOMn). exists Fn. split; [|exact HFOMn].
  pose proof (PRH_PjOrder.pj_foR_lblk SEGS _ _ _ _ _ _ HFOn) as HFOLn.
  pose proof (PRH_PjOrder.pj_foR_frame SEGS _ _ _ _ _ _ _ _ HFOn HFOLn (o2_agree_eq (w_H W) mem (ms_mem ms1) _ Hm1))
    as HFO1n.
  exact (PRH_PjOrder.pj_foR_frame SEGS _ _ _ _ _ _ _ _ HFO1n HFOLn
    (o2_agree_keep W W2 (ms_mem ms1) (ms_mem ms) _ HFT)). }
(* K0-CAP of back: its header and kids are in back's footprint, which neither the run nor the call writes *)
pose proof (rtt_ncapR_agree SEGS (ri_t D) (mrestrict (w_H W) mem) (mrestrict (w_H W) (ms_mem ms1)) _ _ _ HTB HNC
  (o2_agree_eq (w_H W) mem (ms_mem ms1) _ Hm1)) as HNC1.
exact (rtt_ncapR_agree SEGS (ri_t D) (mrestrict (w_H W) (ms_mem ms1)) (mrestrict (w_H W2) (ms_mem ms)) _ _ _ HTB1 HNC1
  (o2_agree_keep W W2 (ms_mem ms1) (ms_mem ms) _ HFT)).
Qed.

End cut.
End img.

Print Assumptions rtt_seg_o2_A.

(* the ELABORATED statements (the text owner's FPState rule): the top theorem and every lemma here that states a cut
   predicate of Rtt102Cut.v (rtt_pre / rtt_carry take the contract's fx) or binds a second FPState (fxc); this file
   defines no Prop of its own *)
Set Printing Implicit.
Unset Printing Notations.
Check @rtt_seg_o2_A.
Check @o2_seat_a.
Check @o2_seat_r.
Check @o2_chain.
Check @o2_carry_eqmem.
Check @o2_carry_call.
Check @o2_dblocks.
Set Printing Notations.
Unset Printing Implicit.
