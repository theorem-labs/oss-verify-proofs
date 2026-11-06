(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-30 (G-BRA): the TAIL segment of the image-B walk of fuzz_reply's relay_add over a
   generic allocator relation ARx, in the ROOM form: pb_rb_tail_x proves lib/B/W_relay_add_cut_x.v rb_tail_stmt.
   From the cut RBU (0x82c04, the entry appended, the lock held, the room rp_RM RP S1 kr) pthread_mutex_unlock
   (&g_lock) 0x82c0c (AUNLOCK, aunlock_realizes_x, through W_sites_x.v aj_gx_entry_at_x; the allocator state S1 is
   kept), wake () 0x82c10 (WAKE, W_wake_c_x.v wk_spec_x at G = [], its journal lifted to RA_G and composed with
   W_journal_x.v ajournal_gx_sub_x; its seat fact S' = set_fs f S1 carries the room by RPF_of), s1 = 0, the epilogue
   0x82c18-0x82c3c (the eight saved registers from the frame) and the return: ra_post_x's fd >= 0 arm.  No trap edge
   in this segment.
   Donor: lib/B/W_relay_add_tail.v (pb_ra_tail, the AR walk, a working branch 22c3862876d; removed
   from this tree by KF-COUNT #4; its machine-code account holds unchanged), converted by
   route (b) (CONVERSION.md sha256 1015972e02a9; internal record), as image A converted its relay_add (lib/A/W_relay_add.v, the
   room form): afn_pre / ajournal_gx / the run chain to their _x twins (Hp after S, Hp' after S'), cgif's laws al_*
   to AR_laws_x's alx_*, the unlock rule to aunlock_realizes_x, wake to wk_spec_x.  Section hypotheses: the donor's,
   by name and order, for the facts this segment reads (AR-stated ones in their _x form), and HPST (W_op_add.v
   Section x's text: the generic journal's image clause keeps only bytes off PST, and wake's journal carries
   relay_add's globals by that clause; trivial at PST = []).  A live block's bytes are off the image by the laws'
   alx_client_img (the kit's blk_off_imgP_x states image A's top). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI00 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep gestures_end_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_syms W_listing W_pl W_kit W_contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_journal W_sites W_rep W_frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_wake_c W_relay_add_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_journal_x W_contract_x W_sites_x W_kit_x W_wake_c_x W_relay_add_cut_x.
(* route R: SRrG / wle' (YA0nH) and relay_add's contract at R (W_contract_srlf_xR.v) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_contract_srlf_xR.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Open Scope bv_scope.
Local Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Abbreviation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Abbreviation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Abbreviation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Abbreviation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).
Section c.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable MT : ameter_ops.
(* the room round's record (W_journal_x.v Record roomp): rp_RM with its law rp_RPF (RPF_of) *)
Variable RP : roomp.
Variable G : list (Z * Z).
Variable RG : rep_globals.
Variable CTX : list (list Z).
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis TL : PALib B.
Hypothesis MTL : ameter_laws MT.
Hypothesis HG : gx_ok SEGS B (RA_G RG).
Hypothesis HWK : forall a, rg_wake RG + 4 <= a < rg_wake RG + 8 ->
  in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Hypothesis HNROM : forall a, inG (RA_G RG) a -> ~ in_rom SEGS a.
(* the live-state meter does not see the fake stack: a set_fs costs nothing (KF-COUNT #4's text) *)
Hypothesis MO_FR : forall s f, mo_le MT s (set_fs f s) 0.
Hypothesis HV3 : VAL (A_OBJ 3) = rg_lock RG.
Hypothesis HRGA : ra_aligned RG.
Hypothesis HRGP : ra_apart (ra_cells RG).
Hypothesis AUNLOCK : aunlock_realizes_x B ARx (SIGMA WS_pthread_mutex_unlock).
(* wake () (lib/B/W_wake_c_x.v): journal at G = [], the seat fact S' = set_fs f S *)
Hypothesis WAKE : wk_spec_x B PST ARx RG (BASE + AF_fr_wake).
(* the image is off PST (W_op_add.v Section x's HPST): wake's journal keeps relay_add's globals by its image clause *)
Hypothesis HPST : forall a, in_img SEGS a -> ~ Exists (in_zr a) PST.
Let RET := paj_ret_at (PL := PL_fr) (PI := PI).

(* ------------------------------------------------------------------ the seat at 0x82c04 *)
(* sp = atom 2 (the entry sp - 64); the frame [sp, sp + 64) read-only, its eight slots the saved registers, seated
   as the extra atoms 32 .. 39 (slot i at sp + 8 i holds RA_SAVED's register i at the entry). *)
Definition tl_extra (cx : racx_x) : list word := map (getr (bxregs cx)) RA_SAVED.
Definition tl_frame : YP09.region :=
YP09.mkRegion (Some 2%nat) 0 64 0 0
[YP09.mkChunk 0 (CVal 8 (SOff 32 0)); YP09.mkChunk 8 (CVal 8 (SOff 33 0)); YP09.mkChunk 16 (CVal 8 (SOff 34 0));
 YP09.mkChunk 24 (CVal 8 (SOff 35 0)); YP09.mkChunk 32 (CVal 8 (SOff 36 0)); YP09.mkChunk 40 (CVal 8 (SOff 37 0));
 YP09.mkChunk 48 (CVal 8 (SOff 38 0)); YP09.mkChunk 56 (CVal 8 (SOff 39 0))].
Definition tl_facts : facts := mkFacts [ (2%nat, mkAF (2^46) (2^47) 5) ] [] [].
Definition ss_tl : sstate := mkSS A_ra_unlock sr_atoms [tl_frame] None tl_facts.
Definition tl_SH : list shent := [].
Definition Bx : sv := SOff 18 0.
Definition Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).

Lemma tl_seat_x : forall cx regs1 W1 m1,
afn_pre_x SEGS B ARx RA_STK (bxly cx) (bxS cx) (bxHp cx) (bxW cx) (bxregs cx) (bxmem cx) (bxmd cx) (bxch cx) ->
bsp0 cx mod 32 = 0 -> bregs_base cx regs1 -> rb_saved cx W1 m1 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs1 (tl_extra cx))) ss_tl
(restrict (w_H W1) (mkst regs1 (Z_to_bv 64 (BASE + A_ra_unlock)) m1 (seg_rom SEGS)))
/\ sh_ok SEGS Bx tl_SH (Eimg (Ereg regs1 (tl_extra cx))) (mrestrict (w_H W1) m1).
Proof.
intros cx regs1 W1 m1 HPRE Hal32 HR HSV.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HR as (Rsp & _).
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs1 (tl_extra cx))).
assert (E2 : ew E 2 = getr regs1 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs1 _ 2 2%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = bsp0 cx - RA_FRAME) by (rewrite E2; exact Rsp).
assert (EX : forall i, (i < 8)%nat -> ew E (32 + i) = getr (bxregs cx) (nth i RA_SAVED 0%bv)).
{ intros i Hi. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite ew_Ereg_extra. unfold tl_extra.
  rewrite (nth_indep _ _ (getr (bxregs cx) 0%bv)) by (rewrite length_map; cbn; lia).
  rewrite map_nth. reflexivity. }
split.
- unfold ss_tl. apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + apply Forall_cons; [|apply Forall_nil]. unfold region_ok, tl_frame.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite Usp. unfold bsp0, RA_FRAME in *.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil;
    lazymatch goal with |- context [YP09.mkChunk ?od (CVal 8 (SOff ?n 0))] =>
      let i := eval cbv in (n - 32)%nat in
      let Xi := fresh "Xi" in pose proof (EX i ltac:(lia)) as Xi; cbn [Nat.add] in Xi;
      apply (chunk_ok_val SEGS E _ _ od 8 (SOff n 0) (bv_unsigned (getr (bxregs cx) (nth i RA_SAVED 0%bv))));
      [ cbn [sv_denot]; rewrite Xi, Z.add_0_r, !Z_to_bv_bv_unsigned; reflexivity
      | pose proof (bv_unsigned_in_range 64 (getr (bxregs cx) (nth i RA_SAVED 0%bv))) as Hrr;
        change (bv_modulus 64) with (2 ^ 64) in Hrr;
        replace (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) by reflexivity; lia
      | cbn [Z.of_N]; lia
      | let Si := fresh "Si" in pose proof (HSV i ltac:(lia)) as Si; unfold arm, bsp0, RA_FRAME in Si;
        replace (spZ (bxregs cx) - 64 + od) with (spZ (bxregs cx) - 64 + 8 * Z.of_nat i) by (cbn; lia); exact Si ]
    end.
  + cbn [pairwise_disjoint all_disjoint]. repeat split.
  + split; [|split; [exact I | exact I]].
    cbn [tl_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp. change (2 ^ 5) with 32. unfold bsp0, RA_FRAME in *.
    revert Hslo Hshi H47 Hceil Hal32 C1 C3 Hstk0. clear.
    unfold SB, zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros.
    repeat match goal with |- _ /\ _ => split end; try lia.
    rewrite Zminus_mod, Hal32. reflexivity.
- unfold sh_ok, tl_SH. constructor.
Qed.
(* ------------------------------------------------------------------ bytes kept, writability *)
(* W_gestures_end.v's gse_writable_view (W4): a byte a reader sees, off the read-only segments, is writable. *)
Lemma tl_writable_view : forall H (m : word -> option byte) a v, 0 <= a < 2 ^ 64 ->
aview SEGS H m a = Some v -> ~ in_rom SEGS a -> writable_at SEGS (mrestrict H m) a.
Proof.
intros H m a v Ha Hv Hn. unfold aview, mbyte in Hv. unfold writable_at, wview.
destruct (mrestrict H m (Z_to_bv 64 a)) as [b|] eqn:Em; [discriminate|].
unfold seg_rom, memory_read in Hv.
destruct (find_segment SEGS (bv_unsigned (Z_to_bv 64 a)) (Z.of_N 1)) as [sg|] eqn:Ef; [|discriminate].
change (Z.of_N 1) with 1 in Ef. rewrite Ef.
destruct (seg_readable sg); [|discriminate].
destruct (find_segment_hit _ _ _ _ Ef) as (Hin & Hlo & Hhi). rewrite unsigned_lit_small in Hlo, Hhi by lia.
destruct (seg_writable sg) eqn:Ew.
- destruct (segment_byte_at (seg_bytes sg) (Z.to_N (bv_unsigned (Z_to_bv 64 a) - Z.of_N (seg_base sg)))) eqn:Eb; [discriminate|].
  exfalso. change (N.to_nat 1) with 1%nat in Hv. cbn [segment_read_bytes] in Hv. rewrite Eb in Hv. cbn in Hv. discriminate Hv.
- exfalso. apply Hn. exists sg. split; [exact Hin|]. split; [exact Ew | lia].
Qed.
(* a byte of relay_add's globals whose view is kept and seen is kept (writable by HNROM) *)
Lemma tl_glob_kept : forall (W W' : world SEGS) m m' a, inG (RA_G RG) a ->
aview SEGS (w_H W') m' a = aview SEGS (w_H W) m a -> aview SEGS (w_H W) m a <> None -> abyte_kept W m W' m' a.
Proof.
intros W W' m m' a Hg He Hs. split; [exact He|]. intros _. unfold arm.
pose proof (pa_img_range a (proj1 (HG a Hg))) as Hr.
destruct (aview SEGS (w_H W) m a) as [v|] eqn:Ev; [|exfalso; exact (Hs eq_refl)].
exact (tl_writable_view (w_H W') m' a v ltac:(lia) He (HNROM a Hg)).
Qed.
(* a byte of a live block (after) whose view is kept is kept (writable: present by the laws' block clause) *)
Lemma tl_heap_kept_x : forall ly S Hp (W W' : world SEGS) m m' md' p n a,
ARx ly S Hp W' m' md' -> In (p, n) (ablocks B ly S) -> p <= a < p + req_size n ->
aview SEGS (w_H W') m' a = aview SEGS (w_H W) m a -> abyte_kept W m W' m' a.
Proof.
intros ly S Hp W W' m m' md' p n a HAR Hin Ha He. split; [exact He|]. intros _. unfold arm.
destruct (alx_blocks _ _ _ LAWS ly S Hp W' m' md' p n HAR Hin) as (_ & _ & _ & _ & HP & _).
apply (apresent_writable SEGS). exact (proj1 (HP a Ha)).
Qed.
Lemma tl_not_owned_x : forall ly S Hp W mem md a, ARx ly S Hp W mem md -> in_img SEGS a ->
~ Exists (in_zr a) (as_owned_static B) -> ~ aowned B ly S a.
Proof.
intros ly S Hp W mem md a HAR Hi Ho Hown. apply Ho.
exact (proj1 (alx_owned_image _ _ _ LAWS ly S Hp W mem md a HAR Hi) Hown).
Qed.
(* a live block's byte is not an image byte (the laws' alx_client_img, block clause) *)
Lemma tl_blk_not_img_x : forall ly S Hp W mem md p n a, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) ->
p <= a < p + req_size n -> ~ in_img SEGS a.
Proof.
intros ly S Hp W mem md p n a HAR Hin Ha.
refine (proj2 (alx_client_img _ _ _ LAWS ly S Hp W mem md a HAR _)).
left. exists p, n. split; [exact Hin | exact Ha].
Qed.
Lemma tl_vm_kept : forall H H' (m m' : word -> option byte) a n v, val_mem SEGS (mrestrict H m) a n v ->
(forall b, a <= b < a + Z.of_nat n -> aview SEGS H' m' b = aview SEGS H m b) -> val_mem SEGS (mrestrict H' m') a n v.
Proof.
intros H H' m m' a n v Hv Hk. apply (val_mem_kept SEGS H H' m m' a n v); [|exact Hv]. intros k Hk'. apply Hk. lia.
Qed.
Lemma tl_view_some : forall H (m : word -> option byte) a n v k, val_mem SEGS (mrestrict H m) a n v -> 0 <= k < Z.of_nat n ->
aview SEGS H m (a + k) <> None.
Proof.
intros H m a n v k Hv Hk. unfold aview. replace (a + k) with (a + Z.of_nat (Z.to_nat k)) by lia.
rewrite (Hv (Z.to_nat k) ltac:(lia)). discriminate.
Qed.
(* ------------------------------------------------------------------ the relay's table, kept *)
Lemma tl_key_ptrs_len : forall ks, length (key_ptrs ks) = (8 * length ks)%nat.
Proof.
induction ks as [|k ks IH]; [reflexivity|]. unfold key_ptrs in *. cbn [map concat]. rewrite length_app, IH.
rewrite OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.length_le8. cbn [length]. lia.
Qed.
Lemma tl_req_pos : forall n, 0 < n -> req_size n = n.
Proof. intros n Hn. unfold req_size. destruct (Z.eqb_spec n 0); lia. Qed.
(* every byte an entry's predicate reads lies in one of the entry's live blocks *)
Lemma tl_efp_blk : forall ly S W m e, aentry_ok B ly S W m e ->
forall r, In r (aentry_fp e) -> forall a, fst r <= a < snd r ->
exists p n, In (p, n) (ablocks B ly S) /\ p <= a < p + req_size n.
Proof.
intros ly S W m e (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15) r Hr a Ha.
unfold aentry_fp in Hr. apply in_app_or in Hr as [Hr | Hr].
- destruct (Z.eqb_spec (re_cap e) 0) as [Hc|Hc]; [destruct Hr|]. destruct Hr as [<- | []].
  destruct H10 as [(Hc0 & _) | (Hcp & Hin & Hj & _)]; [lia|].
  exists (re_buf e), (re_cap e). split; [exact Hin|].
  unfold gfp, bzs in Ha. rewrite length_map, length_app in Ha. cbn [fst snd] in Ha.
  rewrite (tl_req_pos (re_cap e) Hcp). lia.
- destruct Hr as [<- | Hr].
  + destruct H12 as [(Hz & Hk) | (Hz & Hin & Hk1 & Hk2 & _)].
    * unfold gfp, bzs in Ha. rewrite length_map, Hk in Ha. cbn in Ha. lia.
    * exists (re_hp e), (re_kh e). split; [exact Hin|].
      unfold gfp, bzs in Ha. rewrite length_map, tl_key_ptrs_len in Ha. cbn [fst snd] in Ha.
      unfold re_nheld in Hk1. rewrite (tl_req_pos (re_kh e)) by lia. lia.
  + apply in_map_iff in Hr as (k & <- & Hk). rewrite Forall_forall in H15. destruct (H15 k Hk) as (K1 & K2 & K3 & K4 & K5).
    exists (key_addr k), (Z.of_nat (length (key_text k)) + 1). split; [exact K1|].
    unfold gfp, bzs in Ha. rewrite length_map, length_app in Ha. cbn [fst snd length] in Ha.
    rewrite (tl_req_pos (Z.of_nat (length (key_text k)) + 1)) by lia. lia.
Qed.
(* the relay's table at a later state whose live blocks are the same: every global and block byte keeps its view *)
Lemma tl_relay_kept_x : forall ly S (W : world SEGS) m ly' S' Hp' (W' : world SEGS) m' md' T1 es,
arelay_at B RG ly S W m T1 es -> ARx ly' S' Hp' W' m' md' -> ablocks B ly' S' = ablocks B ly S ->
(forall p n a, In (p, n) (ablocks B ly S) -> p <= a < p + req_size n -> aview SEGS (w_H W') m' a = aview SEGS (w_H W) m a) ->
(forall a, inG (RA_G RG) a -> ~ (rg_lock RG <= a < rg_lock RG + 12) -> aview SEGS (w_H W') m' a = aview SEGS (w_H W) m a) ->
arelay_at B RG ly' S' W' m' T1 es.
Proof.
intros ly S W m ly' S' Hp' W' m' md' T1 es HR HAR' HBL KB KG.
pose proof HR as (V1 & _ & V3 & _ & V5 & _ & _ & HinT & _ & HF & _).
ra_pick HRGP 2%nat 3%nat D23. ra_pick HRGP 2%nat 4%nat D24. ra_pick HRGP 2%nat 5%nat D25.
assert (KH : forall p n a, In (p, n) (ablocks B ly S) -> p <= a < p + req_size n -> abyte_kept W m W' m' a).
{ intros p n a Hin Ha. apply (tl_heap_kept_x ly' S' Hp' W W' m m' md' p n a HAR');
  [rewrite HBL; exact Hin | exact Ha | exact (KB p n a Hin Ha)]. }
apply (arelay_at_kept B RG ly S W m ly' S' W' m' T1 es HR).
- intros r Hr a Ha. unfold arelay_fp in Hr.
  destruct Hr as [<- | [<- | [<- | [<- | Hr]]]]; cbn [fst snd] in Ha.
  + apply tl_glob_kept; [apply ra_src_in; lia | apply KG; [apply ra_src_in; lia | clear - Ha D25; lia] |].
    replace a with (rg_src RG + (a - rg_src RG)) by lia. apply (tl_view_some _ _ _ 8 _ _ V1). lia.
  + apply tl_glob_kept; [apply ra_nsrc_in; lia | apply KG; [apply ra_nsrc_in; lia | clear - Ha D23; lia] |].
    replace a with (rg_nsrc RG + (a - rg_nsrc RG)) by lia. apply (tl_view_some _ _ _ 4 _ _ V3). lia.
  + apply tl_glob_kept; [apply ra_capsrc_in; lia | apply KG; [apply ra_capsrc_in; lia | clear - Ha D24; lia] |].
    replace a with (rg_capsrc RG + (a - rg_capsrc RG)) by lia. apply (tl_view_some _ _ _ 4 _ _ V5). lia.
  + apply (KH T1 ATABLE a HinT). change (req_size ATABLE) with 896. unfold ATABLE in Ha. lia.
  + apply in_concat in Hr as (l & Hl & Hr). apply in_map_iff in Hl as (e & <- & He).
    rewrite Forall_forall in HF. destruct (tl_efp_blk ly S W m e (HF e He) r Hr a Ha) as (p & n & Hin & Hpa).
    exact (KH p n a Hin Hpa).
- intros b Hb. rewrite HBL. unfold arelay_blks in Hb. destruct Hb as [<- | Hb]; [exact HinT|].
  apply in_concat in Hb as (l & Hl & Hb). apply in_map_iff in Hl as (e & <- & He).
  rewrite Forall_forall in HF. destruct (HF e He) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & H10 & _ & H12 & _ & _ & H15).
  unfold aentry_blks in Hb. apply in_app_or in Hb as [Hb | Hb].
  + destruct (Z.eqb_spec (re_cap e) 0); [destruct Hb|]. destruct Hb as [<- | []].
    destruct H10 as [(Hc0 & _) | (_ & Hin & _)]; [lia | exact Hin].
  + apply in_app_or in Hb as [Hb | Hb].
    * destruct (Z.eqb_spec (re_hp e) 0); [destruct Hb|]. destruct Hb as [<- | []].
      destruct H12 as [(Hz & _) | (_ & Hin & _)]; [lia | exact Hin].
    * apply in_map_iff in Hb as (k & <- & Hk). rewrite Forall_forall in H15. exact (proj1 (H15 k Hk)).
Qed.
(* the lock at a later state: its twelve bytes keep their views *)
Lemma tl_lock_kept : forall (W W' : world SEGS) m m' b,
alock_at RG W m b -> (forall a, rg_lock RG <= a < rg_lock RG + 12 -> aview SEGS (w_H W') m' a = aview SEGS (w_H W) m a) ->
alock_at RG W' m' b.
Proof.
intros W W' m m' b HL KL. apply (alock_at_kept RG W m W' m' b HL).
intros r Hr x Hx. destruct Hr as [<- | []]. cbn [fst snd] in Hx.
pose proof HL as (V0 & V4 & V8 & _). unfold arm in V0, V4, V8.
apply tl_glob_kept; [apply ra_lock_in; lia | apply KL; lia |].
destruct (Z_lt_ge_dec x (rg_lock RG + 4)) as [h1|h1]; [|destruct (Z_lt_ge_dec x (rg_lock RG + 8)) as [h2|h2]].
- replace x with (rg_lock RG + (x - rg_lock RG)) by lia. apply (tl_view_some _ _ _ 4 _ _ V0). lia.
- replace x with (rg_lock RG + 4 + (x - (rg_lock RG + 4))) by lia. apply (tl_view_some _ _ _ 4 _ _ V4). lia.
- replace x with (rg_lock RG + 8 + (x - (rg_lock RG + 8))) by lia. apply (tl_view_some _ _ _ 4 _ _ V8). lia.
Qed.

(* W_gestures_end.v's gse_keep_high (W4), over ajournal_gx_x: a byte above alloc_ceiling outside the journal's window
   keeps its view *)
Lemma tl_keep_high_x : forall G0 XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
gx_ok SEGS B G0 -> ajournal_gx_x SEGS B PST ARx G0 XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp0 + XO - (STK + XO) <= a < sp0 + XO) ->
aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a.
Proof.
intros G0 XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k HGx (HS0 & HX0 & (memS & HJi & Hag) & _)
  a Ha Hno.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _). rewrite (F1 a Ha Hno).
pose proof asan_consts as (C1 & _).
apply (aview_gagree SEGS G0 _ _ _ a Hag). apply inGb_false. rewrite unsigned_lit_small by lia. intros HGa.
pose proof (inG_low SEGS B pa_segs_low G0 a HGx HGa) as HL. unfold kLowMemEnd in HL. lia.
Qed.
(* W_gestures_end.v's gse_keep_img (W4), over ajournal_gx_x: an image byte, not owned, not errno, off the journal's
   globals, keeps its view (off PST by HPST) *)
Lemma tl_keep_img_x : forall G0 XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
ajournal_gx_x SEGS B PST ARx G0 XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
fp_spares FP a -> ~ inG G0 a -> aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a.
Proof.
intros G0 XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k (HS0 & HX0 & (memS & HJi & Hag) & _)
  a Hi Ho He Hf Hg.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _). rewrite (F3 a Hi Ho He (HPST a Hi) Hf).
pose proof (pa_segs_low a Hi) as HL.
apply (aview_gagree SEGS G0 _ _ _ a Hag). apply inGb_false. rewrite unsigned_lit_small by (unfold kLowMemEnd in HL; lia). exact Hg.
Qed.
(* ... and a byte of a block live at both ends, off the footprint *)
Lemma tl_keep_blk_x : forall G0 XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k p n i,
gx_ok SEGS B G0 -> ajournal_gx_x SEGS B PST ARx G0 XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B ly' S') -> 0 <= i < req_size n -> ~ inFP FP (p + i) ->
aview SEGS (w_H W') mem' (p + i) = aview SEGS (w_H W) mem (p + i).
Proof.
intros G0 XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k p n i HGx (HS0 & HX0 & (memS & HJi & Hag) & _)
  H1 H2 Hi Hf.
pose proof HJi as (HAR0 & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _). rewrite (F2 p n i H1 H2 Hi Hf).
apply (aview_gagree SEGS G0 _ _ _ (p + i) Hag). apply inGb_false. intros HGa.
destruct (alx_blocks _ _ _ LAWS ly' S' Hp' W' mem' md' p n HAR0 H2) as (_ & H4096 & Hc & _).
pose proof asan_consts as (C1 & _).
rewrite unsigned_lit_small in HGa by lia.
destruct (HGx _ HGa) as [Hi' _].
exact (tl_blk_not_img_x ly' S' Hp' W' mem' md' p n (p + i) HAR0 H2 ltac:(lia) Hi').
Qed.

(* ------------------------------------------------------------------ wake (), over the walk's journal *)
(* WAKE (lib/B/W_wake_c_x.v: journal at G = [], wake writes no global), its journal lifted to RA_G RG and composed
   with the walk's (W_journal_x.v ajournal_gx_sub_x), in the form of W_gestures_end.v gse_callS; the call is made 64
   bytes below the entry sp.  frames are read off wake's journal (own = []), the meter by MO_FR at the seat fact
   (the end state is a set_fs of the state before the call), the seat fact from
   wk_post_x's last conjunct. *)
Lemma tl_wake_x : forall W regsc memc mdc STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc k raw,
ajournal_gx_x SEGS B PST ARx (RA_G RG) 0 [] STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc k ->
spZ regsc = sp0 + -64 -> WK_STK + 64 <= STK -> sp0 mod 16 = 0 ->
getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
getr regsc 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
s0Z regsc < alloc_ceiling ->
count_cid 0 (frames Sc) < fs_frames 0 -> awake_at RG W memc -> rom_view SEGS W memc ->
SRr SEGS W (mkCfg (mkst regsc (Z_to_bv 64 (BASE + AF_fr_wake)) memc (seg_rom SEGS)) mdc)
(fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 k1,
 c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
 ajournal_gx_x SEGS B PST ARx (RA_G RG) 0 [] STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + k1) /\
 ajournal_gx_x SEGS B PST ARx [] 0 [] WK_STK (sp0 + -64) [] lyc Sc Hpc W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 /\
 aregs_preserved regsc regs2 /\ frames S2 = frames Sc /\ mo_le MT Sc S2 0 /\ ablocks B ly2 S2 = ablocks B lyc Sc /\
 (forall a, in_img SEGS a -> apresent (w_H W) memc a -> apresent (w_H W2) mem2 a) /\
 (forall i, 0 <= i < 4 -> aview SEGS (w_H W2) mem2 (as_errno B + i) = aview SEGS (w_H W) memc (as_errno B + i)) /\
 (exists f, S2 = set_fs f Sc)).
Proof.
intros W regsc memc mdc STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc k raw HJ Hsp HSTK Hal Hgp Htp Hra Hraw Hra4 Hs0
  Hcnt Hwk Hrom.
destruct (ajournal_gx_inner_x SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (memS & HJi & _).
rewrite !Z.add_0_r in HJi.
pose proof (ajournal_gx_AR_x SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HARc.
assert (HPRE1 : afn_pre_x SEGS B ARx WK_STK lyc Sc Hpc W regsc memc mdc []).
{ eapply afn_pre_x_at with (STK1 := WK_STK) (o := -64) (ch1 := []).
  - exact HJi.
  - exact Hsp.
  - reflexivity.
  - lia.
  - unfold WK_STK, WK_FRAME, ASTACK. lia.
  - lia.
  - rewrite Hra. exact Hraw.
  - unfold raZ. rewrite Hra. exact Hra4.
  - exact Hgp.
  - exact Htp.
  - apply achain_low. exact Hs0. }
eapply SRr_mono.
{ exact (WAKE W lyc Sc Hpc regsc memc mdc [] HPRE1 Hcnt Hwk Hrom). }
cbv beta. intros W2 c2 _ (regs2 & ly2 & S2 & Hp2 & mem2 & md2 & k1 & -> & HJw & HP & HBL & HPR & _ & HERRw & HSEAT).
exists ly2, S2, Hp2, regs2, mem2, md2, k1. split; [rewrite Hra; reflexivity|].
rewrite Hsp in HJw.
destruct (ajournal_gx_inner_x SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJw) as (memS2 & HJwi & _).
pose proof HJwi as (_ & _ & _ & _ & _ & Hfrw & _). cbn [app] in Hfrw.
split.
{ change own with ([] ++ own).
  eapply (ajournal_gx_sub_x SEGS B PST ARx LAWS pa_segs_low (RA_G RG));
  [ exact HJ
  | exact (ajournal_gx_G_mono_x SEGS B PST ARx [] (RA_G RG) 0 [] WK_STK (sp0 + -64) [] lyc Sc Hpc W memc mdc []
      ly2 S2 Hp2 W2 mem2 md2 k1 (fun a Ha => False_ind _ (inG_nil a Ha)) HJw)
  | unfold WK_STK, WK_FRAME, ASTACK in *; lia | lia | lia
  | intros a (r & Hr & _); destruct Hr
  | exact HG
  | intros a Ha; exfalso; exact (inFP_nil a Ha) ]. }
split; [exact HJw|]. split; [exact HP|]. split; [exact Hfrw|].
split; [destruct HSEAT as (f & ->); exact (MO_FR Sc f)|].
split; [exact HBL|]. split; [exact HPR|]. split; [exact HERRw | exact HSEAT].
Qed.

(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): this segment at a world relation R, over the cut interface's R forms
   (W_relay_add_cut_x.v Section cR): its runs and branches at their G twins, the call steps at R, the strict callees
   and the return lifted.  At the cf instance R := wle' SEGS RZ_cf. *)
Section cR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', wle W W' -> R W W'.
Let RUNR := paj_run_x_xG B PST ARx LAWS R (RA_G RG) HG 0 [].
Let RUNTOR := paj_run_to_x_xG B PST ARx LAWS R (RA_G RG) HG 0 [].
Lemma tl_keep_high_xR : forall G0 XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
gx_ok SEGS B G0 -> ajournal_gx_xR SEGS B PST ARx R G0 XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp0 + XO - (STK + XO) <= a < sp0 + XO) ->
aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a.
Proof.
intros G0 XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k HGx (HS0 & HX0 & (memS & HJi & Hag) & _)
  a Ha Hno.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _). rewrite (F1 a Ha Hno).
pose proof asan_consts as (C1 & _).
apply (aview_gagree SEGS G0 _ _ _ a Hag). apply inGb_false. rewrite unsigned_lit_small by lia. intros HGa.
pose proof (inG_low SEGS B pa_segs_low G0 a HGx HGa) as HL. unfold kLowMemEnd in HL. lia.
Qed.
Lemma tl_keep_img_xR : forall G0 XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
ajournal_gx_xR SEGS B PST ARx R G0 XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
fp_spares FP a -> ~ inG G0 a -> aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a.
Proof.
intros G0 XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k (HS0 & HX0 & (memS & HJi & Hag) & _)
  a Hi Ho He Hf Hg.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _). rewrite (F3 a Hi Ho He (HPST a Hi) Hf).
pose proof (pa_segs_low a Hi) as HL.
apply (aview_gagree SEGS G0 _ _ _ a Hag). apply inGb_false. rewrite unsigned_lit_small by (unfold kLowMemEnd in HL; lia). exact Hg.
Qed.
Lemma tl_keep_blk_xR : forall G0 XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k p n i,
gx_ok SEGS B G0 -> ajournal_gx_xR SEGS B PST ARx R G0 XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B ly' S') -> 0 <= i < req_size n -> ~ inFP FP (p + i) ->
aview SEGS (w_H W') mem' (p + i) = aview SEGS (w_H W) mem (p + i).
Proof.
intros G0 XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k p n i HGx (HS0 & HX0 & (memS & HJi & Hag) & _)
  H1 H2 Hi Hf.
pose proof HJi as (HAR0 & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _). rewrite (F2 p n i H1 H2 Hi Hf).
apply (aview_gagree SEGS G0 _ _ _ (p + i) Hag). apply inGb_false. intros HGa.
destruct (alx_blocks _ _ _ LAWS ly' S' Hp' W' mem' md' p n HAR0 H2) as (_ & H4096 & Hc & _).
pose proof asan_consts as (C1 & _).
rewrite unsigned_lit_small in HGa by lia.
destruct (HGx _ HGa) as [Hi' _].
exact (tl_blk_not_img_x ly' S' Hp' W' mem' md' p n (p + i) HAR0 H2 ltac:(lia) Hi').
Qed.
Lemma tl_wake_xR : forall W regsc memc mdc STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc k raw,
ajournal_gx_xR SEGS B PST ARx R (RA_G RG) 0 [] STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc k ->
spZ regsc = sp0 + -64 -> WK_STK + 64 <= STK -> sp0 mod 16 = 0 ->
getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
getr regsc 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
s0Z regsc < alloc_ceiling ->
count_cid 0 (frames Sc) < fs_frames 0 -> awake_at RG W memc -> rom_view SEGS W memc ->
SRrG SEGS R W (mkCfg (mkst regsc (Z_to_bv 64 (BASE + AF_fr_wake)) memc (seg_rom SEGS)) mdc)
(fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 k1,
 c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
 ajournal_gx_xR SEGS B PST ARx R (RA_G RG) 0 [] STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + k1) /\
 ajournal_gx_xR SEGS B PST ARx R [] 0 [] WK_STK (sp0 + -64) [] lyc Sc Hpc W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 /\
 aregs_preserved regsc regs2 /\ frames S2 = frames Sc /\ mo_le MT Sc S2 0 /\ ablocks B ly2 S2 = ablocks B lyc Sc /\
 (forall a, in_img SEGS a -> apresent (w_H W) memc a -> apresent (w_H W2) mem2 a) /\
 (forall i, 0 <= i < 4 -> aview SEGS (w_H W2) mem2 (as_errno B + i) = aview SEGS (w_H W) memc (as_errno B + i)) /\
 (exists f, S2 = set_fs f Sc)).
Proof.
intros W regsc memc mdc STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc k raw HJ Hsp HSTK Hal Hgp Htp Hra Hraw Hra4 Hs0
  Hcnt Hwk Hrom.
destruct (ajournal_gx_inner_xR SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (memS & HJi & _).
rewrite !Z.add_0_r in HJi.
pose proof (ajournal_gx_AR_xR SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HARc.
assert (HPRE1 : afn_pre_x SEGS B ARx WK_STK lyc Sc Hpc W regsc memc mdc []).
{ eapply afn_pre_x_atR with (STK1 := WK_STK) (o := -64) (ch1 := []).
  - exact HJi.
  - exact Hsp.
  - reflexivity.
  - lia.
  - unfold WK_STK, WK_FRAME, ASTACK. lia.
  - lia.
  - rewrite Hra. exact Hraw.
  - unfold raZ. rewrite Hra. exact Hra4.
  - exact Hgp.
  - exact Htp.
  - apply achain_low. exact Hs0. }
eapply SRrG_mono.
{ apply (SRr_SRrG SEGS R WLE_R). exact (WAKE W lyc Sc Hpc regsc memc mdc [] HPRE1 Hcnt Hwk Hrom). }
cbv beta. intros W2 c2 _ (regs2 & ly2 & S2 & Hp2 & mem2 & md2 & k1 & -> & HJw & HP & HBL & HPR & _ & HERRw & HSEAT).
(* wake's journal is at wle; at R by WLE_R *)
rewrite ajournal_gx_x_wle in HJw.
apply (ajournal_gx_xR_mono SEGS B PST ARx (@wle SEGS) R WLE_R) in HJw.
exists ly2, S2, Hp2, regs2, mem2, md2, k1. split; [rewrite Hra; reflexivity|].
rewrite Hsp in HJw.
destruct (ajournal_gx_inner_xR SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJw) as (memS2 & HJwi & _).
pose proof HJwi as (_ & _ & _ & _ & _ & Hfrw & _). cbn [app] in Hfrw.
split.
{ change own with ([] ++ own).
  eapply (ajournal_gx_sub_xR SEGS B PST ARx LAWS pa_segs_low R_trans (RA_G RG));
  [ exact HJ
  | exact (ajournal_gx_G_mono_xR SEGS B PST ARx [] (RA_G RG) 0 [] WK_STK (sp0 + -64) [] lyc Sc Hpc W memc mdc []
      ly2 S2 Hp2 W2 mem2 md2 k1 (fun a Ha => False_ind _ (inG_nil a Ha)) HJw)
  | unfold WK_STK, WK_FRAME, ASTACK in *; lia | lia | lia
  | intros a (r & Hr & _); destruct Hr
  | exact HG
  | intros a Ha; exfalso; exact (inFP_nil a Ha) ]. }
split; [exact HJw|]. split; [exact HP|]. split; [exact Hfrw|].
split; [destruct HSEAT as (f & ->); exact (MO_FR Sc f)|].
split; [exact HBL|]. split; [exact HPR|]. split; [exact HERRw | exact HSEAT].
Qed.
Theorem pb_rb_tail_xR : rb_tail_stmtR B PST ARx MT RP G RG CTX R.
Proof.
intros cx W1 c1 HB (regs1 & ly1 & S1 & Hp1 & m1 & md1 & k1 & T1 & -> & HR & Hfd & HAL & HREL & HML & HRM & HBLK).
pose proof HAL as (HJ & HROM1 & HPK1 & HSV & HLK & HWAKE & HFR & HERR1).
pose proof HB as (HPRE & Hal32 & HCNT & H10 & Rfd & _ & _ & _ & _ & HNEW & HGin & HGerr & _).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof HR as ((Rsp & R3 & R4 & R23 & R24 & R25 & R26 & R27) & R8 & R18).
assert (WS : RA_STK = 16512) by reflexivity.
unfold bsp0 in HJ.
destruct (tl_seat_x cx regs1 W1 m1 HPRE Hal32 (proj1 HR) HSV) as [HS SHOK].
remember (Eimg (Ereg regs1 (tl_extra cx))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r)
by (intros n r Hn; subst E; pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5;
rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
assert (EX : forall i, (i < 8)%nat -> ew E (32 + i) = getr (bxregs cx) (nth i RA_SAVED 0%bv)).
{ intros i Hi. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite ew_Ereg_extra. unfold tl_extra.
  rewrite (nth_indep _ _ (getr (bxregs cx) 0%bv)) by (rewrite length_map; cbn; lia).
  rewrite map_nth. reflexivity. }
assert (HAE : env_agree 32 (Ereg regs1 (tl_extra cx)) E)
by (rewrite HE; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clear HE.
assert (Usp : bv_unsigned (ew E 2) = bsp0 cx - RA_FRAME) by (rewrite (EE 2%nat 2%bv eq_refl); exact Rsp).
unfold bsp0, RA_FRAME in Usp, Rsp.
(* the lock's address and its bounds (an image byte of RA_G) *)
pose proof (pa_img_range _ (proj1 (HG (rg_lock RG) (ra_lock_in RG (rg_lock RG) ltac:(lia))))) as BL0.
pose proof (pa_img_range _ (proj1 (HG (rg_lock RG + 11) (ra_lock_in RG (rg_lock RG + 11) ltac:(lia))))) as BL1.
assert (BG : forall a, inG (RA_G RG) a -> 0x10000 <= a < 0x5fc000) by (intros a Ha; exact (pa_img_range a (proj1 (HG a Ha)))).
pose proof HRGA as (HLA & _ & _ & _).
unfold cfg_at. change (w64 (BASE + A_ra_unlock)) with (Z_to_bv 64 (BASE + A_ra_unlock)).
(* ---- 0x82c04-0x82c0c: a0 = &g_lock, the call *)
paj_run_tok_xR RUNR HS HJ SHOK Bspan.
{ apply awr_ok_x_of0. intros a (r & Hin & Hr). cbn [ss_mem ss_tl add_cond In] in Hin. destruct Hin as [<- | []].
  cbn [tl_frame YP09.r_base YP09.r_wlo YP09.r_whi] in Hr. lia. }
(* the run wrote nothing: every byte keeps its view *)
assert (K0 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W1) (ms_mem ms) a = aview SEGS (w_H W1) m1 a).
{ intros a Ha. apply (aview_kept_out E _ (w_H W1) m1 (ms_mem ms) HFr a Ha).
  intros (r & Hin & Hr). cbn [ss_mem ss_tl add_cond In] in Hin. destruct Hin as [<- | []].
  cbn [tl_frame YP09.r_base YP09.r_wlo YP09.r_whi] in Hr. lia. }
assert (P0 : forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) (ms_mem ms) a).
{ intros a Hp. lazymatch goal with Hg : mem_grows (mrestrict (w_H W1) m1) (mrestrict (w_H W1) (ms_mem ms)) |- _ =>
    exact (apresent_grows _ _ _ a Hg Hp) end. }
pmkst HS.
prreg HS (1%bv : bv 5) QRA. prreg HS (2%bv : bv 5) QSP. prreg HS (3%bv : bv 5) QGP. prreg HS (4%bv : bv 5) QTP.
prreg HS (10%bv : bv 5) QA0.
assert (HSPc : spZ (ms_regs ms) = spZ (bxregs cx) + -64) by (unfold spZ at 1; rewrite QSP, Usp; lia).
assert (QA0' : getr (ms_regs ms) 10 = w64 (rg_lock RG)).
{ rewrite QA0. change 244%nat with (A_OBJ 3). rewrite (img_env_atomP E (A_OBJ 3) HEI ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
  rewrite HV3. reflexivity. }
assert (LKc : alock_at RG W1 (ms_mem ms) true) by (apply (tl_lock_kept W1 W1 m1 (ms_mem ms) true HLK); intros a Ha; apply K0; lia).
pose proof LKc as (LK0 & LK4 & LK8 & LKW). unfold arm in LK0, LK4, LK8, LKW.
assert (LKV : forall a, rg_lock RG <= a < rg_lock RG + 12 -> aview SEGS (w_H W1) (ms_mem ms) a <> None).
{ intros a Ha. destruct (Z_lt_ge_dec a (rg_lock RG + 4)) as [h1|h1]; [|destruct (Z_lt_ge_dec a (rg_lock RG + 8)) as [h2|h2]].
  - replace a with (rg_lock RG + (a - rg_lock RG)) by lia. apply (tl_view_some _ _ _ 4 _ _ LK0). lia.
  - replace a with (rg_lock RG + 4 + (a - (rg_lock RG + 4))) by lia. apply (tl_view_some _ _ _ 4 _ _ LK4). lia.
  - replace a with (rg_lock RG + 8 + (a - (rg_lock RG + 8))) by lia. apply (tl_view_some _ _ _ 4 _ _ LK8). lia. }
pose proof (ajournal_gx_AR_xR SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HARd.
assert (HNOWN : forall a, rg_lock RG <= a < rg_lock RG + 12 -> ~ aowned B ly1 S1 a).
{ intros a Ha. destruct (HG a (ra_lock_in RG a Ha)) as (Hi & Hno & _). exact (tl_not_owned_x _ _ _ _ _ _ a HARd Hi Hno). }
(* ---- pthread_mutex_unlock (&g_lock): the lock word becomes 0; the allocator state S1 is kept *)
eapply (SRrG_bind SEGS R R_trans).
{ eapply (aj_gx_entry_at_xR B PST ARx LAWS R_trans WLE_R (RA_G RG) 0 [] ESTACK (SIGMA WS_pthread_mutex_unlock)
    (fun a => rg_lock RG + 4 <= a < rg_lock RG + 8)
    (fun (regs' : bvmap 5 word) (mem' : word -> option byte) =>
       getr regs' 10 = w64 0 /\ val_mem SEGS (mrestrict (w_H W1) mem') (rg_lock RG + 4) 4 0)
    W1 _ _ RA_STK (spZ (bxregs cx)) (bFP cx) (bxly cx) (bxS cx) (bxHp cx) (bxW cx) (bxmem cx) (bxmd cx)
    _ _ _ _ _ _ (-64) _ HG eq_refl HJ).
  - exact HSPc.
  - reflexivity.
  - lia.
  - lia.
  - rewrite WS. unfold ESTACK. lia.
  - rewrite QGP, (EE 3%nat 3%bv eq_refl), R3. exact Hgp.
  - rewrite QTP, (EE 4%nat 4%bv eq_refl), R4. exact Htp.
  - exact QRA.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros a. destruct (Z_lt_ge_dec a (rg_lock RG + 4)); [right; lia|].
    destruct (Z_lt_ge_dec a (rg_lock RG + 8)); [left; lia | right; lia].
  - intros a Ha _. exact (LKV a ltac:(lia)).
  - intros a Ha HnG. exfalso. apply HnG. apply ra_lock_in. lia.
  - intros HPRE2 HSC. apply (AUNLOCK _ _ _ _ _ _ _ (rg_lock RG) HPRE2).
    + exact QA0'.
    + lia.
    + exact HLA.
    + lia.
    + exact LK0.
    + exact LK4.
    + exact LK8.
    + intros a Ha. split; [exact (LKV a ltac:(lia))|]. rewrite HSPc. unfold ESTACK. lia.
    + intros a Ha. split; [|split].
      * replace a with (rg_lock RG + (a - rg_lock RG)) by lia. apply LKW. lia.
      * exact (HNOWN a ltac:(lia)).
      * rewrite HSPc. unfold ESTACK. lia.
    + intros a Ha HK. refine (proj2 (proj2 (HG a _)) (proj1 (proj2 HK))). apply ra_lock_in. lia. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & (HA02 & HLK2) & HK2 & HPR2).
assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (rg_lock RG + 4 <= a < rg_lock RG + 8) ->
  ~ (spZ (bxregs cx) + -64 - ESTACK <= a < spZ (bxregs cx) + -64) ->
  aview SEGS (w_H W1) mem2 a = aview SEGS (w_H W1) m1 a)
  by (intros a Ha Hw Hs; rewrite (HK2 a Ha Hw Hs); apply K0; exact Ha).
jafter_call_keep_pi HS 40%nat regs2 (mrestrict (w_H W1) mem2) HP2 [0]%nat HS2.
match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_nil].
  apply (region_kept_aview E (w_H W1) (ms_mem ms) mem2 2 (spZ (bxregs cx) - 64)); [exact Usp | | exact HPR2].
  intros a Ha. apply HK2; [lia | cbn; lia | unfold ESTACK; lia]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 40 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall m, (m < 40)%nat -> ew Ea m = ew E m) by (intros m Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
assert (HAEa : env_agree 32 (Ereg regs1 (tl_extra cx)) Ea) by (rewrite HEa; apply env_agree_havoc_ge; [cbv; lia | exact HAE]).
clear HEa.
assert (Usp2 : bv_unsigned (ew Ea 2) = spZ (bxregs cx) - 64) by (rewrite OLDa by lia; exact Usp).
assert (SHOK2 : sh_ok SEGS Bx tl_SH Ea (mrestrict (w_H W1) mem2)) by (unfold sh_ok, tl_SH; constructor).
(* ---- 0x82c10: jal wake *)
paj_run_to_tok_xR RUNTOR HS HJ2 SHOK2 Bspan AF_fr_wake.
{ apply awr_ok_x_of0. intros a (r & Hin & Hr). cbn [ss_mem add_cond In] in Hin. destruct Hin as [<- | []].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr. lia. }
assert (K3 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W1) (ms_mem ms0) a = aview SEGS (w_H W1) mem2 a).
{ intros a Ha. lazymatch goal with H : frame_of Ea _ (mrestrict (w_H W1) mem2) (mrestrict (w_H W1) (ms_mem ms0)) |- _ =>
    apply (aview_kept_out Ea _ (w_H W1) mem2 (ms_mem ms0) H a Ha) end.
  intros (r & Hin & Hr). cbn [ss_mem add_cond In] in Hin. destruct Hin as [<- | []].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr. lia. }
assert (P2 : forall a, apresent (w_H W1) mem2 a -> apresent (w_H W1) (ms_mem ms0) a).
{ intros a Hp. lazymatch goal with Hg : mem_grows (mrestrict (w_H W1) mem2) (mrestrict (w_H W1) (ms_mem ms0)) |- _ =>
    exact (apresent_grows _ _ _ a Hg Hp) end. }
pmkst HS.
prreg HS (1%bv : bv 5) WRA. prreg HS (2%bv : bv 5) WSP. prreg HS (3%bv : bv 5) WGP. prreg HS (4%bv : bv 5) WTP.
prreg HS (8%bv : bv 5) WS0.
assert (HSPw : spZ (ms_regs ms0) = spZ (bxregs cx) + -64) by (unfold spZ at 1; rewrite WSP, Usp2; lia).
assert (FD8 : getr (ms_regs ms0) 8 = w64 (bxfd cx)) by (rewrite WS0, OLDa, (EE 8%nat 8%bv eq_refl) by lia; exact R8).
(* g_wake[1] and the .rodata at the call: no write touched them (apart from the lock word, off the stack) *)
assert (AW : awake_at RG W1 (ms_mem ms0)).
{ unfold awake_at in HWAKE |- *. apply (tl_vm_kept _ _ _ _ _ _ _ HWAKE). intros b Hb.
  pose proof (HWK b ltac:(cbn in Hb; lia)) as (HbI & _). pose proof (pa_img_range b HbI) as HbR.
  ra_pick HRGP 2%nat 6%nat D26.
  rewrite K3 by lia. apply K2; [lia | cbn in Hb; lia | unfold ESTACK; lia]. }
assert (ROMV : rom_view SEGS W1 (ms_mem ms0)).
{ intros a Ha. assert (HaI : in_img SEGS a) by (destruct Ha as (sg & Hsg & _ & Hr); exists sg; split; [exact Hsg | exact Hr]).
  pose proof (pa_img_range a HaI) as HaR.
  assert (HnL : ~ (rg_lock RG + 4 <= a < rg_lock RG + 8)) by (intros HL; apply (HNROM a (ra_lock_in RG a ltac:(lia))); exact Ha).
  rewrite K3 by lia. rewrite K2 by (unfold ESTACK; lia). exact (HROM1 a Ha). }
eapply (SRrG_bind SEGS R R_trans).
{ eapply (tl_wake_xR W1 (ms_regs ms0) (ms_mem ms0) _ RA_STK (spZ (bxregs cx)) (bFP cx) (bxly cx) (bxS cx) (bxHp cx)
    (bxW cx) (bxmem cx) (bxmd cx) [] ly1 S1 Hp1 _ (Z_to_bv 64 (BASE + 2256)) HJ2).
  - exact HSPw.
  - unfold WK_STK, WK_FRAME, ASTACK. lia.
  - exact Hal16.
  - rewrite WGP, OLDa, (EE 3%nat 3%bv eq_refl), R3 by lia. exact Hgp.
  - rewrite WTP, OLDa, (EE 4%nat 4%bv eq_refl), R4 by lia. exact Htp.
  - exact WRA.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite unsigned_lit_small by lia. lia.
  - unfold s0Z. rewrite FD8. unfold w64. rewrite unsigned_lit_small by lia. lia.
  - rewrite HFR. exact HCNT.
  - exact AW.
  - exact ROMV. }
cbv beta. intros W3 c3 _
  (ly3 & S3 & Hp3 & regs3 & mem3 & md3 & k3 & -> & HJ3 & HJw & HP3 & HFR3 & HML3 & HBL3 & HPR3 & HERR3 & HSEAT).
jafter_call_keep_pi HS 56%nat regs3 (mrestrict (w_H W3) mem3) HP3 [0]%nat HS3.
match type of HS3 with ?ty -> _ => assert (HRK : ty); [|specialize (HS3 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_nil].
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; intros a Ha; rewrite Usp2 in Ha; [|lia].
  apply (mbyte_of_aview SEGS).
  eapply (tl_keep_high_xR [] 0 [] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (gx_ok_nil SEGS B) HJw a);
  revert Ha; clear - Hslo Hshi H47 Hceil Hstk0 C1 WS; unfold WK_STK, WK_FRAME, ASTACK, RA_STK, RA_FRAME in *; intros; lia. }
clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
remember (havoc Ea 56 (map (getr regs3) CLOB)) as Eb eqn:HEb in HS.
assert (HEIb : img_env VAL A_LIM Eb) by (rewrite HEb; apply img_env_havoc; [exact HEIa | cbv; lia]).
assert (OLDb : forall m, (m < 56)%nat -> ew Eb m = ew Ea m) by (intros m Hm; rewrite HEb; apply YN3v.ew_havoc_old; exact Hm).
assert (HAEb : env_agree 32 (Ereg regs1 (tl_extra cx)) Eb) by (rewrite HEb; apply env_agree_havoc_ge; [cbv; lia | exact HAEa]).
clear HEb.
assert (Usp3 : bv_unsigned (ew Eb 2) = spZ (bxregs cx) - 64) by (rewrite OLDb by lia; exact Usp2).
assert (SHOK3 : sh_ok SEGS Bx tl_SH Eb (mrestrict (w_H W3) mem3)) by (unfold sh_ok, tl_SH; constructor).
(* ---- 0x82c14-0x82c40: s1 = 0, a0 = 0, the eight restores, sp += 64, ret *)
paj_run_tok_xR RUNR HS HJ3 SHOK3 Bspan.
{ apply awr_ok_x_of0. intros a (r & Hin & Hr). cbn [ss_mem add_cond In] in Hin. destruct Hin as [<- | []].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr. lia. }
assert (K4 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W3) (ms_mem ms1) a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha. lazymatch goal with H : frame_of Eb _ (mrestrict (w_H W3) mem3) (mrestrict (w_H W3) (ms_mem ms1)) |- _ =>
    apply (aview_kept_out Eb _ (w_H W3) mem3 (ms_mem ms1) H a Ha) end.
  intros (r & Hin & Hr). cbn [ss_mem add_cond In] in Hin. destruct Hin as [<- | []].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr. lia. }
assert (P4 : forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) (ms_mem ms1) a).
{ intros a Hp. lazymatch goal with Hg : mem_grows (mrestrict (w_H W3) mem3) (mrestrict (w_H W3) (ms_mem ms1)) |- _ =>
    exact (apresent_grows _ _ _ a Hg Hp) end. }
pose proof (ajournal_gx_AR_xR SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HAR3.
pose proof HARd as HAR1.
prreg HS (1%bv : bv 5) F1. prreg HS (2%bv : bv 5) F2. prreg HS (3%bv : bv 5) F3. prreg HS (4%bv : bv 5) F4.
prreg HS (8%bv : bv 5) F8. prreg HS (9%bv : bv 5) F9. prreg HS (10%bv : bv 5) F10.
prreg HS (18%bv : bv 5) F18. prreg HS (19%bv : bv 5) F19. prreg HS (20%bv : bv 5) F20. prreg HS (21%bv : bv 5) F21.
prreg HS (22%bv : bv 5) F22. prreg HS (23%bv : bv 5) F23. prreg HS (24%bv : bv 5) F24. prreg HS (25%bv : bv 5) F25.
prreg HS (26%bv : bv 5) F26. prreg HS (27%bv : bv 5) F27.
assert (FRS : forall (i : nat) (r : bv 5), (i < 8)%nat -> nth i RA_SAVED 0%bv = r -> ew Eb (32 + i) = getr (bxregs cx) r)
  by (intros i r Hi <-; rewrite OLDb, OLDa by lia; exact (EX i Hi)).
assert (FKP : forall (n : nat) (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew Eb n = getr regs1 r)
  by (intros n r Hn Hr; rewrite OLDb, OLDa by lia; exact (EE n r Hr)).
(* the lock released at mem2: the lock word 0 (unlock's post), the type word and the waiters kept *)
assert (LK2 : alock_at RG W1 mem2 false).
{ assert (V0 : val_mem SEGS (mrestrict (w_H W1) mem2) (rg_lock RG) 4 0).
  { apply (tl_vm_kept _ _ _ _ _ _ _ LK0). intros b Hb. cbn in Hb. apply HK2; [lia | lia | unfold ESTACK; lia]. }
  assert (V8 : val_mem SEGS (mrestrict (w_H W1) mem2) (rg_lock RG + 8) 4 0).
  { apply (tl_vm_kept _ _ _ _ _ _ _ LK8). intros b Hb. cbn in Hb. apply HK2; [lia | lia | unfold ESTACK; lia]. }
  split; [exact V0|]. split; [exact HLK2|]. split; [exact V8|].
  intros i Hi. unfold arm.
  assert (Hs : aview SEGS (w_H W1) mem2 (rg_lock RG + i) <> None).
  { destruct (Z_lt_ge_dec i 4) as [h1|h1]; [|destruct (Z_lt_ge_dec i 8) as [h2|h2]].
    - apply (tl_view_some _ _ _ 4 _ _ V0). lia.
    - replace (rg_lock RG + i) with (rg_lock RG + 4 + (i - 4)) by lia. apply (tl_view_some _ _ _ 4 _ _ HLK2). lia.
    - replace (rg_lock RG + i) with (rg_lock RG + 8 + (i - 8)) by lia. apply (tl_view_some _ _ _ 4 _ _ V8). lia. }
  destruct (aview SEGS (w_H W1) mem2 (rg_lock RG + i)) as [v|] eqn:Ev; [|exfalso; exact (Hs eq_refl)].
  exact (tl_writable_view (w_H W1) mem2 (rg_lock RG + i) v ltac:(lia) Ev
    (HNROM _ (ra_lock_in RG (rg_lock RG + i) ltac:(lia)))). }
(* an image byte of RA_G, other than the lock word, from m1 to the final memory *)
assert (KGF : forall a, inG (RA_G RG) a -> ~ (rg_lock RG + 4 <= a < rg_lock RG + 8) ->
  aview SEGS (w_H W3) (ms_mem ms1) a = aview SEGS (w_H W1) m1 a).
{ intros a Hg Hnl. pose proof (BG a Hg) as HaR. destruct (HG a Hg) as (Hi & Ho & _).
  rewrite K4 by lia.
  rewrite (tl_keep_img_xR [] 0 [] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJw a Hi Ho (HGerr a Hg)
    (fp_spares_closed [] a sink_closed_nil) (inG_nil a)).
  rewrite K3 by lia. apply K2; [lia | exact Hnl | unfold ESTACK; lia]. }
(* a byte of a block live at m1, to the final memory *)
assert (KBF : forall p n a, In (p, n) (ablocks B ly1 S1) -> p <= a < p + req_size n ->
  aview SEGS (w_H W3) (ms_mem ms1) a = aview SEGS (w_H W1) m1 a).
{ intros p n a Hin Ha.
  destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 _ _ p n HARd Hin) as (_ & H4096 & Hc & _).
  pose proof (tl_blk_not_img_x ly1 S1 Hp1 W1 _ _ p n a HARd Hin Ha) as HnI.
  assert (HnL : ~ (rg_lock RG + 4 <= a < rg_lock RG + 8))
    by (intros HL; apply HnI; exact (proj1 (HG a (ra_lock_in RG a ltac:(lia))))).
  rewrite K4 by lia.
  replace a with (p + (a - p)) by lia.
  rewrite (tl_keep_blk_xR [] 0 [] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ p n (a - p) (gx_ok_nil SEGS B) HJw Hin
    ltac:(rewrite HBL3; exact Hin) ltac:(lia) (inFP_nil _)).
  rewrite K3 by lia. apply K2; [lia | replace (p + (a - p)) with a by lia; exact HnL | unfold ESTACK; lia]. }
apply (SRr_SRrG SEGS R WLE_R).
eapply (RET W3 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold bPOSTR, ra_post_xR.
lazymatch goal with |- exists _ _ _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists ly3, S3, Hp3, r, m, d, (k1 + k3) end.
split.
{ rewrite F1, OLDb, OLDa by lia. pose proof (EX 7%nat ltac:(lia)) as X7. cbn [Nat.add nth RA_SAVED] in X7. rewrite X7.
  rewrite Hra. reflexivity. }
split.
{ eapply rb_liftR; [exact HB|].
  apply (ajournal_gx_materialize_xR SEGS B PST ARx LAWS Hsegs). exact HJ3. }
split.
{ intros rr Hrr. unfold acallee_saved in Hrr.
  assert (Hcase : rr = 2 \/ rr = 3 \/ rr = 4 \/ rr = 8 \/ rr = 9 \/ rr = 18 \/ rr = 19 \/ rr = 20 \/ rr = 21 \/
    rr = 22 \/ rr = 23 \/ rr = 24 \/ rr = 25 \/ rr = 26 \/ rr = 27) by lia.
  clear Hrr.
  destruct Hcase as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]].
  - replace (Z_to_bv 5 2) with (2%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite F2, Usp3. replace (spZ (bxregs cx) - 64 + 64) with (spZ (bxregs cx)) by lia. unfold spZ.
    apply Z_to_bv_bv_unsigned.
  - replace (Z_to_bv 5 3) with (3%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite F3, (FKP 3%nat 3%bv ltac:(lia) eq_refl). exact R3.
  - replace (Z_to_bv 5 4) with (4%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite F4, (FKP 4%nat 4%bv ltac:(lia) eq_refl). exact R4.
  - replace (Z_to_bv 5 8) with (8%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite F8. pose proof (FRS 6%nat 8%bv ltac:(lia) eq_refl) as X. cbn [Nat.add] in X. exact X.
  - replace (Z_to_bv 5 9) with (9%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite F9. pose proof (FRS 5%nat 9%bv ltac:(lia) eq_refl) as X. cbn [Nat.add] in X. exact X.
  - replace (Z_to_bv 5 18) with (18%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite F18. pose proof (FRS 4%nat 18%bv ltac:(lia) eq_refl) as X. cbn [Nat.add] in X. exact X.
  - replace (Z_to_bv 5 19) with (19%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite F19. pose proof (FRS 3%nat 19%bv ltac:(lia) eq_refl) as X. cbn [Nat.add] in X. exact X.
  - replace (Z_to_bv 5 20) with (20%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite F20. pose proof (FRS 2%nat 20%bv ltac:(lia) eq_refl) as X. cbn [Nat.add] in X. exact X.
  - replace (Z_to_bv 5 21) with (21%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite F21. pose proof (FRS 1%nat 21%bv ltac:(lia) eq_refl) as X. cbn [Nat.add] in X. exact X.
  - replace (Z_to_bv 5 22) with (22%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite F22. pose proof (FRS 0%nat 22%bv ltac:(lia) eq_refl) as X. cbn [Nat.add] in X. exact X.
  - replace (Z_to_bv 5 23) with (23%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite F23, (FKP 23%nat 23%bv ltac:(lia) eq_refl). exact R23.
  - replace (Z_to_bv 5 24) with (24%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite F24, (FKP 24%nat 24%bv ltac:(lia) eq_refl). exact R24.
  - replace (Z_to_bv 5 25) with (25%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite F25, (FKP 25%nat 25%bv ltac:(lia) eq_refl). exact R25.
  - replace (Z_to_bv 5 26) with (26%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite F26, (FKP 26%nat 26%bv ltac:(lia) eq_refl). exact R26.
  - replace (Z_to_bv 5 27) with (27%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite F27, (FKP 27%nat 27%bv ltac:(lia) eq_refl). exact R27. }
split.
{ intros a Hi Ho He Hp. apply P4, (HPR3 a Hi), P2, HPR2, P0. exact (HPK1 a Hi Ho He Hp). }
split; [rewrite HFR3; exact HFR|].
split; [pose proof (mle_station MT (bxS cx) S1 S3 _ _ MTL HML HML3) as X; rewrite Z.add_0_r in X; exact X|].
(* the room: unlock kept S1, wake's seat is a set_fs (W_wake_c_x.v wk_post_x), which keeps rp_RM (RPF_of) *)
split; [destruct HSEAT as (f & HS3); rewrite HS3; apply RPF_of; exact HRM|].
split.
{ apply (tl_lock_kept W1 W3 mem2 (ms_mem ms1) false LK2). intros a Ha.
  pose proof (BG a (ra_lock_in RG a Ha)) as HaR. destruct (HG a (ra_lock_in RG a Ha)) as (Hi & Ho & _).
  rewrite K4 by lia.
  rewrite (tl_keep_img_xR [] 0 [] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJw a Hi Ho (HGerr a (ra_lock_in RG a Ha))
    (fp_spares_closed [] a sink_closed_nil) (inG_nil a)).
  apply K3. lia. }
(* errno: the runs write no errno byte (K0 / K3 / K4), unlock keeps every byte off its lock word and stack window (K2;
   errno is below kLowMemEnd and not in RA_G), wake keeps errno (HERR3) *)
split.
2:{ intros i Hi. destruct (ra_errno_low _ TL i Hi) as (Hlo & _).
  assert (HnG : ~ inG (RA_G RG) (as_errno B + i)) by (intros Hg; apply (HGerr _ Hg); lia).
  rewrite K4 by lia. rewrite (HERR3 i Hi). rewrite K3 by lia.
  rewrite K2; [exact (HERR1 i Hi) | lia | intros Hl; apply HnG; apply ra_lock_in; lia | unfold ESTACK; lia]. }
right. split; [exact Hfd|]. split; [rewrite F10; reflexivity|]. exists T1. split.
{ apply (tl_relay_kept_x ly1 S1 W1 m1 ly3 S3 Hp3 W3 (ms_mem ms1) _ T1 _ HREL HAR3 HBL3).
  - exact KBF.
  - intros a Hg Hnl. apply KGF; [exact Hg | lia]. }
destruct HBLK as [(HT & HP) | (HT & HT1 & HE)].
- left. split; [exact HT | rewrite HBL3; exact HP].
- right. split; [exact HT|]. split; [exact HT1 | rewrite HBL3; exact HE].
Qed.
End cR.
(* the strict segment is its R twin at R := wle (route R's rule: one walk text) *)
Theorem pb_rb_tail_x : rb_tail_stmt B PST ARx MT RP G RG CTX.
Proof.
eapply (pb_rb_tail_xR (@wle SEGS));
  first [ eassumption | intros ? ? H; exact H | intros ?; apply wle_refl | intros ? ? ? H1 H2; eapply wle_trans; [exact H1 | exact H2] ].
Qed.
End c.
End b.
End a.
