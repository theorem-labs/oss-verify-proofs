(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/AE2y.v, with its module paths and module names changed; 366 of its 406 lines of code are new or changed and 664 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/Padded102B.v; 261 of its 322 lines of code are new or changed and 345 lines of the source are left out. *)
(* fuzz_preset, image B' (#102 pins: asan-ubsan sha256 d663f82d7f488d30): padded's segment S3 (row PDB-S3 of
   the internal file FREE-PIECES-102.md), B' 0x830dc -> 0x830f0: the size test and the call
   __asan_memcpy (b, data, size), from the cut PD_OK to the cut PD_SET, where S4 (pd_s4_stmt, row PDB-S4) takes
   over: pd_s3_of_s4 : pd_s4_stmt -> pd_s3_stmt.
   rule 24: proves function padded (reuse search: the internal file REWALK-102-PLAN.md section D3: none exists; proof-index
   padded / 0x830dc / 0x830f0: no released proof) - this file proves one segment lemma of it (kind: segment lemma).
   INPUTS: the frozen interface lib/B/Prog/Padded102B.v (Padded102B.v (sha256 c84199f45390; internal record); its
   Section d's Context lines, local notations and the runtime row AI_cpy (:173) are copied below; its shared seat
   pd_seat and its closed listing tables PL_pd_B are cited); the listing lib/B/Listing_prog.v (sha256 416d90f8ab75; internal record)
   :1683-1687 (slots 1668-1672 of the whole-program listing = B' 0x830dc-0x830ec: `beqz s2, +20`; `mv a0, s0`;
   `mv a1, s3`; `mv a2, s2`; PCall AS___asan_memcpy, whose return site is PD_SET).
   THE WALK: the shared seat pd_seat at PD_OK; the branch on s2 = size (atom 18). Taken (size = 0): the runner to
   PD_SET, where x = [] and every fact of the cut holds unchanged. Not taken: the runner to the call; YGcallMxmn.v :269
   aj_intrin_at_xm OCpy with the row AI_cpy, its source premises from the cut's src_rd and pd_src_apart, its
   destination from pd_okblk; at the return pd_at_set is rebuilt (pd3_keep: the copy writes [b, b + size) and the
   callee's ESTACK window only, and puts x at b), then the S4 premise is applied.
   Numerals: 48 (LENGTH: the frame, `addi sp, sp, -48`); 16 (LENGTH: FUZZ_PAD, fuzz.h; = cf_head at CfParams_preset,
   read by reflexivity); 8 (LENGTH: word, shadow granule); 4096 (DERIVED: ESTACK); 16432 (DERIVED: STK_padded at
   prh_img_B, by vm_compute); 2 ^ 32 / 2 ^ 44 / 2 ^ 47 / 2 ^ 63 / 2 ^ 64 (DERIVED: the copy rule's size bound, shadow
   and stack bounds, the machine word). No ADDRESS literal. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YI16 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG YCbqGcall.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames YGcallx YGcallcf YGcallMx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG01cf YG00cf YG0ncf YG0dcf YG0sshcf YGcfRoomPre YG0lawscf YGcfApath.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YSRrMemnorm YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YGcfRoomKeep YGcfRoomLive.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetLiveBounds PresetRoomPos PresetRun
  PresetReqAt PresetRoomPosKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnAlloc PRH_FnReader
  PRH_FnCheck CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import Padded102B Padded102B_Home.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- image-free arithmetic ---- *)
(* the shadow byte of an address below 2 ^ 47 lies in [SHADOW_OFF, kHighMemBeg) *)
Lemma pd3_sh_band : forall x, 0 <= x < 2 ^ 47 -> SHADOW_OFF <= shadow_of_addr SHADOW_OFF x < kHighMemBeg.
Proof.
intros x Hx. unfold shadow_of_addr, SHADOW_OFF, kHighMemBeg.
pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)).
assert (x / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.
(* so does every byte of the shadow hull of a range below 2 ^ 47 *)
Lemma pd3_hull_band : forall x n s, 0 <= x -> 0 < n -> x + n <= 2 ^ 47 ->
  shadow_addr x / 8 * 8 <= s < shadow_addr (x + n - 1) / 8 * 8 + 8 -> SHADOW_OFF <= s < kHighMemBeg.
Proof.
intros x n s Hx Hn Hxn Hs. unfold shadow_addr in Hs.
pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)) as P1.
assert (P2 : (x + n - 1) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
pose proof (Z.div_mod (SHADOW_OFF + x / 8) 8 ltac:(lia)) as D1.
pose proof (Z.mod_pos_bound (SHADOW_OFF + x / 8) 8 ltac:(lia)) as M1.
pose proof (Z.div_mod (SHADOW_OFF + (x + n - 1) / 8) 8 ltac:(lia)) as D2.
pose proof (Z.mod_pos_bound (SHADOW_OFF + (x + n - 1) / 8) 8 ltac:(lia)) as M2.
unfold SHADOW_OFF, kHighMemBeg in *. lia.
Qed.
(* an application range holds no shadow byte *)
Lemma pd3_app_band {rc : YM05.RunCeil} : forall p len s, in_app p len -> SHADOW_OFF <= s < kHighMemBeg ->
  ~ (p <= s < p + len).
Proof. intros p len s Happ Hs. unfold in_app, kLowShadowBeg, SHADOW_OFF, kHighMemBeg in *. lia. Qed.
(* rdword reads eight bytes *)
Lemma pd3_rdword_eq : forall (rd rd' : reader) a, (forall i, 0 <= i < 8 -> rd' (a + i) = rd (a + i)) ->
  rdword rd' a = rdword rd a.
Proof.
intros rd rd' a H. unfold rdword.
pose proof (H 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0.
rewrite H0, (H 1 ltac:(lia)), (H 2 ltac:(lia)), (H 3 ltac:(lia)), (H 4 ltac:(lia)), (H 5 ltac:(lia)),
  (H 6 ltac:(lia)), (H 7 ltac:(lia)).
reflexivity.
Qed.
(* the registers aregs_preserved keeps, read at a bv literal *)
Lemma pd3_ap : forall (regs regs' : bvmap 5 word) (r : bv 5), aregs_preserved regs regs' ->
  acallee_saved (bv_unsigned r) -> getr regs' r = getr regs r.
Proof. intros regs regs' r HP Hr. pose proof (HP _ Hr) as H. rewrite !Z_to_bv_bv_unsigned in H. exact H. Qed.
Lemma pd3_ap_trans : forall r1 r2 r3, aregs_preserved r1 r2 -> aregs_preserved r2 r3 -> aregs_preserved r1 r3.
Proof. intros r1 r2 r3 H1 H2 r Hr. rewrite (H2 r Hr). exact (H1 r Hr). Qed.
Ltac pd3_cs := unfold acallee_saved;
  lazymatch goal with |- context [bv_unsigned ?r] => let v := eval vm_compute in (bv_unsigned r) in
    change (bv_unsigned r) with v end; lia.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
Context {PA : PAImg B_prog_listing}.
#[local] Existing Instance prh_img_B.
#[local] Notation CP := CfParams_preset.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation VAL := (@pa_val _ B_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
#[local] Notation PST := (@prh_pst prh_img_B).
Variable B : asyms.
#[local] Notation ARc := (fun ly S Hp W mem md => ARcf (cp := CP) SEGS B ly S Hp W mem md /\ xs_placed_cf ly S).
#[local] Notation AJ := (ajournal_x (SK := SK) SEGS B PST ARc).
(* the interface's two runtime rows (Padded102B.v :173-174), restated in the same Section; S3 cites AI_cpy only *)
Hypothesis AI_cpy : aintrin_realizes_xm SEGS B ARc OCpy (SIGMA AS___asan_memcpy).
Hypothesis AI_set : aintrin_realizes_xm SEGS B ARc OSet (SIGMA AS___asan_memset).
(* the allocator's laws at ARcf (AR_laws_ok_cf, YG0lawscf.v) and AR_laws_x from them (YGcallcf.v), as
   Padded102B.v's Section d states them *)
Let LAWS_cf : AR_laws_cf (cp := CP) SEGS B := AR_laws_ok_cf (cp := CP) SEGS B.
Let LAWS : AR_laws_x SEGS B ARc (@cf_head CP) := AR_laws_x_xs (cp := CP) SEGS B LAWS_cf.

(* ---- the bytes a view keeps ---- *)
Lemma pd3_garr8_vis : forall (W : world SEGS) m p l a, garr8 SEGS (mrestrict (w_H W) m) p l ->
  p <= a < p + Z.of_nat (length l) -> aview SEGS (w_H W) m a <> None.
Proof.
intros W m p l a H Ha. destruct (H (Z.to_nat (a - p)) ltac:(lia)) as [V _].
specialize (V 0%nat ltac:(lia)). cbn [Z.of_nat] in V. rewrite Z.add_0_r, Z2Nat.id in V by lia.
replace (p + (a - p)) with a in V by lia. unfold aview. rewrite V. discriminate.
Qed.

(* the cut's registers survive any change that keeps the callee-saved ones *)
Lemma pd3_regsat_keep : forall D regs regs' b, pd_regsat (PA := PA) D regs b -> aregs_preserved regs regs' ->
  pd_regsat (PA := PA) D regs' b.
Proof.
intros D regs regs' b (R2 & R8 & R9 & R18 & R19 & R3 & R4 & R20) HP. unfold pd_regsat.
assert (A : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs' r = getr regs r)
  by (intros r Hr; exact (pd3_ap regs regs' r HP Hr)).
refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))).
- rewrite A; [exact R2 | pd3_cs].
- rewrite A; [exact R8 | pd3_cs].
- rewrite A; [exact R9 | pd3_cs].
- rewrite A; [exact R18 | pd3_cs].
- rewrite A; [exact R19 | pd3_cs].
- rewrite A; [exact R3 | pd3_cs].
- rewrite A; [exact R4 | pd3_cs].
- intros r Hr. rewrite (HP r ltac:(unfold acallee_saved; lia)). exact (R20 r Hr).
Qed.

(* ---- views ---- *)
Lemma pd3_aview_ext : forall (H : word -> bool) (m m' : word -> option byte) a, (forall x, m' x = m x) ->
  aview SEGS H m' a = aview SEGS H m a.
Proof. intros H m m' a E. unfold aview, mbyte, mrestrict. rewrite E. reflexivity. Qed.
(* the seat's frame region has an empty write window, so the runner's frame_of / awr_ok over it are trivial *)
Lemma pd3_frame_eq : forall E (m m' : word -> option byte), frame_of E [pd_frame] m m' -> forall x, m' x = m x.
Proof. intros E m m' HF x. apply HF. intros (r & Hr & Hw). destruct Hr as [<-|[]]. cbn in Hw. lia. Qed.
Ltac pd3_awr := let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hw := fresh "Hw" in
  intros a (r & Hr & Hw); cbn in Hr; destruct Hr as [<-|[]]; cbn in Hw; lia.

(* ---- THE KEEP: every fact of the cut survives a change of the view off [b, b + n) and off the callee's ESTACK window
   below the body sp (__asan_memcpy (b, data, n) writes only there), and x is at b afterwards: pd_at_set. At n = 0 it
   is the size = 0 arm (no byte changes, x = []). ---- *)
Lemma pd3_keep : pd_img (PA := PA) B -> forall D ly S Hp W regs mem md k b regs' mem' md',
  pd_at_ok (SK := SK) (PA := PA) B D ly S Hp W regs mem md k b ->
  pd_J (SK := SK) (PA := PA) B D ly S Hp W mem' md' k ->
  pd_mn (PA := PA) D mem' ->
  aregs_preserved regs regs' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (b <= a < b + pd_size (PA := PA) D) ->
     ~ (pd_sp0 D - 48 - ESTACK <= a < pd_sp0 D - 48) -> aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) ->
  (forall i, 0 <= i < pd_size (PA := PA) D ->
     aview SEGS (w_H W) mem' (b + i) = aview SEGS (w_H W) mem (din_data D + i)) ->
  pd_at_set (SK := SK) (PA := PA) B D ly S Hp W regs' mem' md' k b.
Proof.
intros IMG D ly S Hp W regs mem md k b regs' mem' md' HOK HJ' Hmn' HAP KV Hcopy.
pose proof (pdi_pst_ok B IMG) as Hpst.
destruct HOK as (HB & Hblk & HnHp & Hap).
pose proof HB as (Hret & HJ & Hsv & Hrs & Hgp & Htp & Hrod & Hmn & HHp & Hled & Hroom & Hsrc & Hhome & Hsz3 & Hhull).
pose proof Hblk as (Hb0 & Hown' & Hb4096 & Hbceil & Hbfresh & Hperm & HLamb & Hwr & Hbra & Hbhull & Hpos).
pose proof Hap as (Hrange & Hpt).
pose proof Hsrc as (Hby & Hd4096 & Hdceil & Hdamr & Hdra & Hdhull).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _ & _).
pose proof HJ' as (HAR' & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSTK : STK_padded = 16432) by (vm_compute; reflexivity).
rewrite HSTK in Hslo.
assert (En : pd_size D = Z.of_nat (length (din_x D))) by reflexivity.
assert (Hn0 : 0 <= pd_size D) by lia.
assert (Hh16 : @cf_head CP = 16) by reflexivity.
pose proof (Permutation_in _ (Permutation_sym Hperm) (in_eq _ _)) as Hinb.
assert (Rq : req_size (pd_size D + 16) = pd_size D + 16) by (unfold req_size; destruct (Z.eqb_spec (pd_size D + 16) 0); lia).
destruct (alx_blocks SEGS B ARc LAWS ly S Hp W mem md b (pd_size D + 16) HAR Hinb) as (_ & _ & Hbc & Happ & _ & _).
rewrite Rq in Hbc, Happ.
(* the view is kept below alloc_ceiling off the copy's destination, and on the whole shadow band *)
assert (KV' : forall a, 0 <= a < YM05.alloc_ceiling -> ~ (b <= a < b + pd_size D) ->
  aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a).
{ intros a Ha Hb. apply KV; [lia | exact Hb | unfold ESTACK; lia]. }
assert (KS : forall s, SHADOW_OFF <= s < kHighMemBeg -> aview SEGS (w_H W) mem' s = aview SEGS (w_H W) mem s).
{ intros s Hs. pose proof (pd3_app_band b (pd_size D + 16) s Happ Hs) as Ho.
  apply KV'; [unfold SHADOW_OFF, kHighMemBeg in *; lia | lia]. }
(* an image byte is no byte of the padded block *)
assert (KI : forall a, in_img SEGS a -> aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a).
{ intros a Hi. pose proof (@pa_segs_low _ _ PA a Hi) as Hlow. rewrite C5 in Hlow.
  apply KV'; [lia|]. intros Hab.
  apply (blk_img_x SEGS B ARc LAWS ly S Hp W mem md b (pd_size D + 16) a HAR Hinb); [rewrite Rq; lia | exact Hi]. }
refine (conj _ (conj _ (conj HnHp (conj Hap _)))).
- (* pd_base *)
  refine (conj Hret (conj HJ' (conj _ (conj (pd3_regsat_keep D regs regs' b Hrs HAP) (conj Hgp (conj Htp (conj _
    (conj Hmn' (conj HHp (conj _ (conj Hroom (conj _ (conj Hhome (conj Hsz3 Hhull)))))))))))))).
  + (* the five saved words: above the call's sp *)
    unfold pd_saved in *. rewrite Forall_forall in *. intros p Hp'.
    assert (Hf : 8 <= fst p <= 40).
    { cbn [In] in Hp'. destruct Hp' as [<- | [<- | [<- | [<- | [<- | []]]]]]; cbn [fst]; lia. }
    rewrite (pd3_rdword_eq (aview SEGS (w_H W) mem) (aview SEGS (w_H W) mem')); [exact (Hsv p Hp')|].
    intros i Hi. apply KV; [lia | lia | unfold ESTACK; lia].
  + (* the read-only view: image bytes *)
    intros a Hro Hno Her. rewrite KI; [exact (Hrod a Hro Hno Her)|].
    destruct Hro as [(sg & Hin & _ & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr] | exact (@pa_relro_img _ _ PA a Hr)].
  + (* the ledger: the statics are image bytes, the heads lie in other blocks *)
    apply (prh_ledger_kept_aview B ly S Hp W mem ly S Hp W mem' (din_Lam D) (din_peak D) (din_cnt D) (din_fail D)
      (din_ran D) (din_most D) (din_own D) Hled).
    * intros a Ha. exact (KI a (Hpst a Ha)).
    * intros a kk i Hin Hi. rewrite Hh16.
      destruct (prh_ledger_hblock B ly S Hp W mem _ _ _ _ _ a kk _ _ Hled Hin) as (Hk0 & Hab & _).
      rewrite Hh16 in Hab.
      assert (Hne : (a - 16, kk + 16) <> (b, pd_size D + 16)).
      { intros E. injection E as E1 _. apply (HLamb a kk Hin). rewrite Hh16. exact E1. }
      pose proof (sep_blocks_x SEGS B ARc LAWS ly S Hp W mem md _ _ _ _ HAR Hab Hinb Hne) as Hd.
      assert (Rk : req_size (kk + 16) = kk + 16) by (unfold req_size; destruct (Z.eqb_spec (kk + 16) 0); lia).
      unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Rq, Rk in Hd.
      destruct (alx_blocks SEGS B ARc LAWS ly S Hp W mem md _ _ HAR Hab) as (_ & H4096 & Hc & _).
      rewrite Rk in Hc. apply KV'; lia.
    * intros a kk _ H. exact H.
    * apply Permutation_refl.
  + (* the source window *)
    refine (conj _ (conj Hd4096 (conj Hdceil (conj Hdamr (conj _ _))))).
    * unfold bytes_at in *. apply (pdh_garr8_move W W mem mem' (din_data D) (din_data D) (din_x D) Hby).
      intros j Hj. destruct (Hpt (din_data D + Z.of_nat j) ltac:(lia)) as [H1 H2]. apply KV'; [exact H1 | lia].
    * apply (range_addressable_agree (aview SEGS (w_H W) mem)); [|exact Hdra].
      intros x Hx. apply KS. apply pd3_sh_band. lia.
    * intros Hp0 s Hs. rewrite KS; [exact (Hdhull Hp0 s Hs)|].
      exact (pd3_hull_band (din_data D) (Z.of_nat (length (din_x D))) s ltac:(lia) Hp0 ltac:(lia) Hs).
- (* the padded block *)
  unfold pd_okblk.
  refine (conj Hb0 (conj Hown' (conj Hb4096 (conj Hbceil (conj Hbfresh (conj Hperm (conj HLamb (conj _ (conj _
    (conj _ Hpos)))))))))).
  + intros a Ha. apply (apresent_writable SEGS).
    destruct (alx_blocks SEGS B ARc LAWS ly S Hp W mem' md' b (pd_size D + 16) HAR' Hinb) as (_ & _ & _ & _ & Hpr & _).
    rewrite Rq in Hpr. exact (proj1 (Hpr a ltac:(lia))).
  + apply (range_addressable_agree (aview SEGS (w_H W) mem)); [|exact Hbra].
    intros x Hx. apply KS. apply pd3_sh_band. lia.
  + intros s Hs. rewrite KS; [exact (Hbhull s Hs)|].
    exact (pd3_hull_band b (pd_size D + 16) s ltac:(lia) ltac:(lia) ltac:(lia) Hs).
- (* the copy *)
  unfold bytes_at in *. apply (pdh_garr8_move W W mem mem' (din_data D) b (din_x D) Hby).
  intros j Hj. exact (Hcopy (Z.of_nat j) ltac:(lia)).
Qed.

(* ======== THE SEGMENT ======== *)
Lemma pd_s3_of_s4 : pd_s4_stmt B -> pd_s3_stmt B.
Proof.
intros S4 IMG D ly S Hp W regs mem md k b HOK.
pose proof HOK as (HB & Hblk & HnHp & Hap).
pose proof HB as (Hret & HJ & Hsv & Hrs & Hgp & Htp & Hrod & Hmn & HHp & Hled & Hroom & Hsrc & Hhome & Hsz3 & Hhull).
pose proof Hblk as (Hb0 & _ & Hb4096 & Hbceil & Hbfresh & Hperm & _ & _ & Hbra & Hbhull & _).
pose proof Hap as (Hrange & Hpt).
pose proof Hsrc as (Hby & Hd4096 & Hdceil & Hdamr & Hdra & Hdhull).
unfold pd_J in HJ.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _ & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof Hrs as (R2 & R8 & R9 & R18 & R19 & R3 & R4 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@YM05.alloc_ceiling_val rc) as [[CL CU] _].
pose proof (@pa_segs_low _ _ PA) as Hsegs.
assert (FSTK : @STK_padded prh_img_B = 16432) by (vm_compute; reflexivity). rewrite FSTK in Hslo.
assert (Hes : ESTACK = 4096) by reflexivity.
assert (En : pd_size D = Z.of_nat (length (din_x D))) by reflexivity.
assert (Hn0 : 0 <= pd_size D) by lia.
pose proof (Permutation_in _ (Permutation_sym Hperm) (in_eq _ _)) as Hinb.
assert (Rq : req_size (pd_size D + 16) = pd_size D + 16) by (unfold req_size; destruct (Z.eqb_spec (pd_size D + 16) 0); lia).
destruct (alx_blocks SEGS B ARc LAWS ly S Hp W mem md b (pd_size D + 16) HAR Hinb) as (_ & _ & Hbc & Happ & _ & _).
rewrite Rq in Hbc, Happ.
assert (Hamr : amem_range b (pd_size D))
  by (clear - Happ C1 Hn0; unfold amem_range, in_app, kLowShadowBeg, kHighMemBeg, kLowMemEnd, kHighMemEnd, ASAN_CEIL in *; lia).
(* ---- the shared seat at PD_OK ---- *)
destruct (pd_seat B IMG D PD_OK ly S Hp W regs mem md k b (din_own D) HB ltac:(lia)) as (HS & SHOK & HEI & HAE).
lazymatch type of HS with st_ok_pi _ _ ?E0 _ _ => remember E0 as E eqn:HE end. clear HE.
assert (EW : forall (n : nat) (r : bv 5), Z.of_nat n = bv_unsigned r -> (n < 32)%nat -> ew E n = getr regs r)
  by (intros n r Hr Hn; rewrite (proj1 HAE n Hn); apply ew_Ereg_nat; exact Hr).
assert (E18' : ew E 18 = Z_to_bv 64 (pd_size D)) by (rewrite (EW 18%nat 18%bv eq_refl ltac:(lia)); exact R18).
pose (P := fun m => YAkMemnorm.memnorm SEGS (din_mem D) -> YAkMemnorm.memnorm SEGS m).
pose (PLAW := srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) (din_mem D) (srr_inv_laws_memnorm_k SEGS)).
pose (RUN := @paj_run_x_inv fx rc SK B_prog_listing PL_pd_B PA B PST ARc _ LAWS P PLAW).
pose (RUNTO := @paj_run_to_x_inv fx rc SK B_prog_listing PL_pd_B PA B PST ARc _ LAWS P PLAW).
pose (BR := @paj_branch fx rc B_prog_listing PA).
assert (HPM : P mem) by exact Hmn.
(* ---- 0x830dc `beqz s2, +20` ---- *)
psrr_branch_tok RUN BR HS SHOK PD_Bspan.
- (* size = 0: the branch to PD_SET, nothing written, x = [] *)
  rewrite branch_eq_U, (U_atom E 18 (pd_size D) E18' ltac:(lia)), U_SLit in Hc.
  rewrite (zcanon_id 0) in Hc by (unfold M64; lia). apply Z.eqb_eq in Hc.
  paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM PD_Bspan (pd_koff PD_SET); [pd3_awr|].
  pose proof (pd3_frame_eq _ _ _ HF) as K1. clear HF HFr HG.
  assert (HAP : aregs_preserved regs (ms_regs ms))
    by (eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs _ HS); [exact HAE | vm_compute; reflexivity]).
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst _ ?pc _ _) _) _ =>
    replace pc with (Z_to_bv 64 (pd_pc PD_SET)) by (unfold pd_pc, PD_OFF, PD_SLOT, PD_SET; f_equal; cbn; lia) end.
  apply (S4 IMG D ly S Hp W (ms_regs ms) (ms_mem ms) _ k b).
  apply (pd3_keep IMG D ly S Hp W regs mem md k b (ms_regs ms) (ms_mem ms) _ HOK HJ HPM HAP).
  + intros a _ _ _. exact (pd3_aview_ext _ mem (ms_mem ms) a K1).
  + intros i Hi. exfalso. lia.
- (* size <> 0: 0x830e0 .. 0x830ec, a0 = b, a1 = data, a2 = size, the call *)
  rewrite branch_eq_U, (U_atom E 18 (pd_size D) E18' ltac:(lia)), U_SLit in Hc.
  rewrite (zcanon_id 0) in Hc by (unfold M64; lia). apply Z.eqb_neq in Hc.
  assert (Hpos : 0 < pd_size D) by lia.
  paj_run_tok_x_inv RUN HS HJ SHOK HPM PD_Bspan; [pd3_awr|].
  pose proof (pd3_frame_eq _ _ _ HF) as K1. clear HF HFr HG.
  assert (HAP1 : aregs_preserved regs (ms_regs ms))
    by (eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs _ HS); [exact HAE | vm_compute; reflexivity]).
  pmkst HS.
  prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12. prreg HS (1%bv : bv 5) Q1.
  prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  assert (HspT : spZ (ms_regs ms) = pd_sp0 D + -48).
  { unfold spZ at 1. rewrite Q2, (EW 2%nat 2%bv eq_refl ltac:(lia)), R2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
  (* the call: YGcallMxmn.v :269 aj_intrin_at_xm OCpy, d = b, x = data, n = size, the row AI_cpy *)
  eapply SRr_bind.
  { eapply (aj_intrin_at_xm SEGS B PST ARc LAWS Hsegs OCpy (SIGMA AS___asan_memcpy) AI_cpy W (ms_regs ms) (ms_mem ms)
      STK_padded (pd_sp0 D) [] (din_ly D) (din_S D) (din_Hp D) (din_W D) (din_mem D) (din_md D) [] ly S Hp _ k
      b (din_data D) (pd_size D) (-48) _ HJ).
    - rewrite Q10, (EW 8%nat 8%bv eq_refl ltac:(lia)). exact R8.
    - rewrite Q11, (EW 19%nat 19%bv eq_refl ltac:(lia)). exact R19.
    - rewrite Q12, (EW 18%nat 18%bv eq_refl ltac:(lia)). exact R18.
    - lia.
    - lia.
    - lia.
    - exact HspT.
    - reflexivity.
    - lia.
    - rewrite FSTK, Hes. lia.
    - rewrite Q3, (EW 3%nat 3%bv eq_refl ltac:(lia)), R3. exact Hgp.
    - rewrite Q4, (EW 4%nat 4%bv eq_refl ltac:(lia)), R4. exact Htp.
    - exact Q1.
    - apply (ret_ok_codeptr_v (PI := PA)); [lia | reflexivity].
    - intros a Ha. split; [|rewrite Hes; lia].
      right; right; left. exists b, (pd_size D + 16). split; [exact Hinb|]. split; [|rewrite Rq; lia].
      intros X. apply Hbfresh. exact (in_map fst _ _ X).
    - exact Hamr.
    - eapply range_addressable_agree;
        [|exact (range_addressable_sub _ SHADOW_OFF b (pd_size D + 16) b (pd_size D) Hbra ltac:(lia) ltac:(lia))].
      intros x Hx. apply pd3_aview_ext. exact K1.
    - intros Hp0 s Hs. rewrite (pd3_aview_ext (w_H W) mem (ms_mem ms) s K1).
      exact (pdh_hull_sub _ b (pd_size D + 16) b (pd_size D) Hbhull ltac:(lia) ltac:(lia) Hp0 s Hs).
    - split; [lia|]. split; [lia|]. split.
      { intros a Ha. split.
        - rewrite (pd3_aview_ext (w_H W) mem (ms_mem ms) a K1).
          unfold bytes_at in Hby. exact (pd3_garr8_vis W mem _ _ a Hby ltac:(lia)).
        - rewrite HspT, Hes. lia. }
      split; [lia|]. split; [exact Hdamr|]. split.
      + eapply range_addressable_agree; [|exact Hdra]. intros x Hx. apply pd3_aview_ext. exact K1.
      + intros Hp0 s Hs. rewrite (pd3_aview_ext (w_H W) mem (ms_mem ms) s K1). exact (Hdhull Hp0 s Hs). }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha02 & Hcopy & Hfr2 & Hpres2 & Hmn2).
  cbv beta iota in Hcopy.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst _ ?pc _ _) _) _ =>
    replace pc with (Z_to_bv 64 (pd_pc PD_SET)) by (unfold pd_pc, PD_OFF, PD_SLOT, PD_SET; f_equal; cbn; lia) end.
  (* ---- PD_SET: pd_at_set, then the S4 premise ---- *)
  apply (S4 IMG D ly S Hp W regs2 mem2 md2 k b).
  apply (pd3_keep IMG D ly S Hp W regs mem md k b regs2 mem2 md2 HOK HJ2 (fun H0 => Hmn2 (HPM H0))
    (pd3_ap_trans _ _ _ HAP1 HP2)).
  + intros a Ha Hnb Hnw. rewrite (Hfr2 a Ha Hnb ltac:(lia)). exact (pd3_aview_ext _ mem (ms_mem ms) a K1).
  + intros i Hi. rewrite (Hcopy i Hi). exact (pd3_aview_ext _ mem (ms_mem ms) _ K1).
Qed.
End d.
