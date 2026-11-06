(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the ASan+UBSan walk (image B, fuzz_reply.asan-ubsan) of fuzz_reply's check_no_loss,
   a NEW walk over lib/B/W_listing.v (B's body is not A's up to relocation: VERDICT.md (sha256 810ca1df9ca9; internal record)), after
   lib/A/W_check_no_loss.v (sha256 8817affe2a55; internal record) and lib/B/W_check_bounded.v (at
   7e062bb9b9c), with the image-B facts (frame, registers, trap sites) of the old-frame walk lib/B/Prog/check_no_loss.v
   (a working branch 0fafbcda68f). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/B/W_check_no_loss.v, with its module paths and module names changed; 1008 of its 1108 lines of code are new or changed and 4874 lines of the source are left out. *)
(* fuzz_preset image B' (asan-ubsan, #102), parse_value 0x8637c, segment D (the DISPATCH): the STRING
   CALL ARM. From parse_string's entry (`jal parse_string` at B 0x8655c, a0 = q, the type word 4 stored at v by
   0x86554) to the shared exit 0x8664c: the kit's parse_string text (lib/A/PRH_FnReader.v tparse_string_specX CTX0 CW, the batch kit
   BUDGETED: post at wbudget CW 0) through YCbqGwild.v's aj_call_xWbR at wle' segs RZ_cf from the C1 journal at the empty
   budget, then one engine stretch at the return 0x86560 (`addi s3, s3, 16`, the ASan check of v + 16, `sd a0, 0(s3)`,
   `snez s5, a0; addi s5, s5, -1`, `j 8664c`) on the caller's journal REBASED at the post-call depot, then the exit cut
   pv_at_exit (pv_body_x: the journal unbased at the callee's budget WS1) with pv_Qm by PvB_D_Str.v pvD_Qm_str. The
   wild-room form's call premises: prh_cw_ok at the call view (the word at q - 8 is the entry's: pv_pre's
   prh_cw_entry) and wild_room .. CW 0 at the call depot (pv_pre's at entry across the C1 journal, ajournal_xw_room).
   KIT (PRH_FnReader.v blob c30f1da6a2d1, the
   post-implication form): the text takes the #102 ledger statics most / own (kept), fpre with frm_zero at the entry
   float state (parse_value's fx0 before strtod: rd_pre's first conjunct), and the two live-count premises over the
   all-granted events prhPs_evs .. [] at the call state (PvB_D_Str.v pvs_counts: pv_pre's over parse_value's granted
   run, which at the quote IS parse_string's, carried to the call state by pv_reader0's room keep); its m-form post
   (fpostWbm) gives each arm's live list and run position over prhPs_evs at the arm's outcome list, which pvD_Qm_str
   composes with the keep from entry into pv_Qm's room post (PvB_Room.v rp_call), and the memnorm keep applied to the
   call state's (pvd_cs) and carried across the exit stretch by the caller-frame runner twin (PvB_D_Fr.v
   paj_run_to_x_fr_invR at wle' segs RZ_cf). fpre's return-address bound at the call is the jal's return slot
   (PvB_D_Kit.v pvd_ret_lt_ceil).
   The C1 reader facts (pv_reader0, at the C1 memory memC) reach the call memory mem across the one stretch byte
   write, the type word [v, v + 4): every fact the text reads lies off the node (the cursor and the text by rd_pre's
   separation, alloc.c's statics on the image, the ledger's heads in other blocks or below the node's user bytes). The
   cursor chain the text asks at the call view (prh_s0 F_parse_string q = q): q = sp0 is parse_value's own record
   (pv_chain), q = sp0 + 8 is one record whose next frame word is parse_value's saved ra (below alloc_ceiling by
   prh_cur_entry), q >= sp0 + 16 is the entry chain from q with the cursor's p word patched (pj_in_okR).
   Numerals: 20116 / 20352 listing offsets (PvB_D_Call AF_pv_str_ret, PvB_Defs AF_pv_exit); 16 / 24 / 56 / 4 / 8 the
   node layout (LENGTH); 144 parse_string's frame (PRH_Img pi_frame); 2 ^ 44 .. 2 ^ 47, 4096 atom ranges (LENGTH).
   Rule 24: proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YK0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YK06 YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YCbqG YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YCbqGwild.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YA0nH YGcfRehidePost YGcfSecsStep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetHullBudget.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjGrammar PjTree PresetRoomPos PresetReqAt.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnReader PRH_Charge PRH_FnParse.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import PRH_ImgB Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PvB_Defs PvB_Model PvB_A_Home PvB_D_Str.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PvB_D_Kit PvB_D_Fr PvB_D_Call.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

#[local] Instance PIB : PrhImg := prh_img_B.
(* YK06 declares a concrete alloc_ceiling; the kit's statements read the run's ceiling YM05.alloc_ceiling *)
#[local] Abbreviation alloc_ceiling := YM05.alloc_ceiling.

(* ---- the stretch's symbolic state at parse_string's return (B 0x86560): every register its own atom; atom 19 = v
   (s3), 23 = the shadow base (s7); one region: v's str field [v + 16, v + 24), written; its shadow entry ---- *)
Definition PVCS_Bx : sv := SOff 23 0.
Definition PVCS_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition pvcs_vreg : YP09.region := YP09.mkRegion (Some 19%nat) 16 24 16 24 [].
Definition pvcs_facts : facts :=
  mkFacts [ (23%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (19%nat, mkAF 4096 (2 ^ 47 - 56) 3) ] [] [].
Definition pvcs_ss : sstate := mkSS AF_pv_str_ret sr_atoms [pvcs_vreg] None pvcs_facts.
Definition pvcs_SH : list shent := [mkSHE 19 16 24].

Section c. Context {fx0 : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
Context {PA : PAImg B_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation VAL := (@pa_val _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ B_prog_listing PA).
#[local] Notation PSTX := (@prh_pst prh_img_B).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* ---- engine-free byte helpers (PvB_A.v's pva_rdword_ext / pva_rdword_of_val / pva_val_keep / pva_garr8_keep /
   pva_wr_keep / pva_in_keep / pva_aview_of_frame / pva_ro_img, restated: PvB_A.v was under edit) ---- *)
Lemma pvcs_rdword_ext : forall (rd rd' : reader) a, (forall i, 0 <= i < 8 -> rd' (a + i) = rd (a + i)) ->
  rdword rd' a = rdword rd a.
Proof.
intros rd rd' a H. unfold rdword. pose proof (H 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0.
rewrite H0, (H 1), (H 2), (H 3), (H 4), (H 5), (H 6), (H 7) by lia. reflexivity.
Qed.
Lemma pvcs_rdword_of_val : forall H mem a v,
  val_mem SEGS (mrestrict H mem) a 8 v -> 0 <= v < 2 ^ 64 -> rdword (aview SEGS H mem) a = Some v.
Proof.
intros H mem a v Hv Hr.
assert (Bk : forall k, (k < 8)%nat -> aview SEGS H mem (a + Z.of_nat k) = Some (YG0f.le_byte v 8 k)).
{ intros k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
  change (YO0f.le_byte v 8 k) with (YG0f.le_byte v 8 k). unfold YG0f.le_byte. apply Z.mod_mod. lia. }
unfold rdword.
rewrite <- (Z.add_0_r a) at 1. change 0 with (Z.of_nat 0) at 1. rewrite (Bk 0%nat) by lia.
change 1 with (Z.of_nat 1). rewrite (Bk 1%nat) by lia. change 2 with (Z.of_nat 2) at 1. rewrite (Bk 2%nat) by lia.
change 3 with (Z.of_nat 3). rewrite (Bk 3%nat) by lia. change 4 with (Z.of_nat 4). rewrite (Bk 4%nat) by lia.
change 5 with (Z.of_nat 5). rewrite (Bk 5%nat) by lia. change 6 with (Z.of_nat 6). rewrite (Bk 6%nat) by lia.
change 7 with (Z.of_nat 7). rewrite (Bk 7%nat) by lia.
f_equal. apply le_bytes8. exact Hr.
Qed.
Lemma pvcs_val_keep : forall (W W' : world SEGS) m m' a (n : nat) v, val_mem SEGS (rdW W m) a n v ->
  (forall x, a <= x < a + Z.of_nat n -> aview SEGS (w_H W') m' x = aview SEGS (w_H W) m x) ->
  val_mem SEGS (rdW W' m') a n v.
Proof.
intros W W' m m' a n v Hv Hk k Hkn. rewrite (mbyte_of_aview SEGS (w_H W) (w_H W') m m' (a + Z.of_nat k)).
- exact (Hv k Hkn).
- apply Hk. lia.
Qed.
Lemma pvcs_garr8_keep : forall (W W' : world SEGS) m m' a l, garr8 SEGS (rdW W m) a l ->
  (forall x, a <= x < a + Z.of_nat (length l) -> aview SEGS (w_H W') m' x = aview SEGS (w_H W) m x) ->
  garr8 SEGS (rdW W' m') a l.
Proof.
intros W W' m m' a l Hg Hk j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
apply (pvcs_val_keep W W' m m' _ 1 _ Hv). intros x Hx. apply Hk. cbn [Z.of_nat] in Hx. lia.
Qed.
Lemma pvcs_wr_keep : forall (m m' : word -> option byte) x, writable_at SEGS m x -> mbyte SEGS m' x = mbyte SEGS m x ->
  0 <= x < 2 ^ 64 -> ~ in_img SEGS x -> writable_at SEGS m' x.
Proof.
intros m m' x Hw Hb Hx Hn. unfold writable_at, wview in *. unfold mbyte in Hb.
destruct (m' (Z_to_bv 64 x)) as [b'|]; [discriminate|].
destruct (m (Z_to_bv 64 x)) as [b|]; [|exact Hw].
rewrite (seg_rom_none SEGS x Hx Hn) in Hb. discriminate Hb.
Qed.
Lemma pvcs_in_keep : forall (W W' : world SEGS) m m' q text len p d tb,
  pj_in_okR SEGS (rdW W m) q text len p d tb ->
  (forall x, q <= x < q + 24 -> aview SEGS (w_H W') m' x = aview SEGS (w_H W) m x) ->
  (forall x, text <= x < text + len -> aview SEGS (w_H W') m' x = aview SEGS (w_H W) m x) ->
  (forall x, q <= x < q + 24 -> 0 <= x < 2 ^ 64 /\ ~ in_img SEGS x) ->
  pj_in_okR SEGS (rdW W' m') q text len p d tb.
Proof.
intros W W' m m' q text len p d tb (V1 & V2 & V3 & Hrw & Hq8 & Ht0 & Ht62 & Hp & Hlen & Gt & Hqt & Hd) Kq Kt Hoff.
split; [apply (pvcs_val_keep W W' m m' q 8 p V1); intros x Hx; apply Kq; cbn in Hx; lia|].
split; [apply (pvcs_val_keep W W' m m' (q + 8) 8 _ V2); intros x Hx; apply Kq; cbn in Hx; lia|].
split; [apply (pvcs_val_keep W W' m m' (q + 16) 4 d V3); intros x Hx; apply Kq; cbn in Hx; lia|].
split.
{ intros x Hx. destruct (Hoff x Hx) as [Hx64 Hni].
  apply (pvcs_wr_keep _ _ x (Hrw x Hx)); [apply (mbyte_of_aview SEGS); apply Kq; exact Hx | exact Hx64 | exact Hni]. }
do 5 (split; [assumption|]).
split; [apply (pvcs_garr8_keep W W' m m' text tb Gt); intros x Hx; apply Kt; lia|].
split; assumption.
Qed.
Lemma pvcs_aview_of_frame : forall (Wx : world SEGS) (E' : env) rs (m m' : word -> option byte) a,
  frame_of E' rs (mrestrict (w_H Wx) m) (mrestrict (w_H Wx) m') -> ~ in_wrange E' rs a -> 0 <= a < 2 ^ 64 ->
  aview SEGS (w_H Wx) m' a = aview SEGS (w_H Wx) m a.
Proof.
intros Wx E' rs m m' a HF Hn Ha. unfold aview. f_equal. unfold mbyte.
rewrite (HF (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by lia. exact Hn.
Qed.
Lemma pvcs_ro_img : forall a, in_roP SEGS pa_relro_lo pa_relro_hi a -> in_img SEGS a.
Proof.
intros a [(sg & Hin & _ & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr] | exact (@pa_relro_img _ _ PA a Hr)].
Qed.
(* a memory that differs from another only on [lo, lo + n) shows the same view off it *)
Lemma pvcs_av_off : forall (W : world SEGS) (m m' : word -> option byte) lo n,
  (forall x : word, ~ (lo <= bv_unsigned x < lo + n) -> mrestrict (w_H W) m' x = mrestrict (w_H W) m x) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < lo + n) -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a.
Proof.
intros W m m' lo n H a Ha Hn. unfold aview, mbyte. rewrite (H (Z_to_bv 64 a)); [reflexivity|].
rewrite unsigned_lit_small by lia. exact Hn.
Qed.

(* a kept register (aregs_preserved's `Z_to_bv 5 r` form) read at its literal index (PvB_A.v pva_getr_lit) *)
Lemma pvcs_getr_lit : forall (regs regs' : bvmap 5 word) (r : bv 5) z, bv_unsigned r = z ->
  getr regs' (Z_to_bv 5 z) = getr regs (Z_to_bv 5 z) -> getr regs' r = getr regs r.
Proof. intros regs regs' r z Hr H. subst z. rewrite !Z_to_bv_bv_unsigned in H. exact H. Qed.
(* the last range of a pairwise-apart list is apart from every other *)
Lemma pvcs_pairwise_last : forall (l : list (Z * Z)) x, pairwise zdisjoint (l ++ [x]) -> Forall (fun y => zdisjoint y x) l.
Proof.
induction l as [|y l IH]; cbn; intros x H; [constructor|].
destruct H as [Hf Hp]. constructor; [apply Forall_app in Hf as [_ Hx]; inversion Hx; assumption | exact (IH x Hp)].
Qed.
(* a register value saved by the prologue, read at its literal index (PvB_A.v pva_val_lit) *)
Lemma pvcs_val_lit : forall (segs : list Segment) m a (n : nat) regs (r : bv 5) z, bv_unsigned r = z ->
  val_mem segs m a n (bv_unsigned (getr regs (Z_to_bv 5 z))) -> val_mem segs m a n (bv_unsigned (getr regs r)).
Proof. intros segs m a n regs r z Hr H. subst z. rewrite Z_to_bv_bv_unsigned in H. exact H. Qed.
(* a present byte is visible *)
Lemma pvcs_present_view : forall H (mem : word -> option byte) a, apresent H mem a -> aview SEGS H mem a <> None.
Proof. intros H mem a [Hh [b Hb]]. unfold aview, mbyte, mrestrict. rewrite Hh, Hb. discriminate. Qed.
(* two memories holding the same value at [a, a + n) show the same view there *)
Lemma pvcs_av_of_val : forall (W W' : world SEGS) m m' a (n : nat) z, val_mem SEGS (rdW W m) a n z ->
  val_mem SEGS (rdW W' m') a n z -> forall x, a <= x < a + Z.of_nat n -> aview SEGS (w_H W') m' x = aview SEGS (w_H W) m x.
Proof.
intros W W' m m' a n z H1 H2 x Hx. unfold aview.
replace x with (a + Z.of_nat (Z.to_nat (x - a))) by lia.
rewrite (H1 (Z.to_nat (x - a)) ltac:(lia)), (H2 (Z.to_nat (x - a)) ltac:(lia)). reflexivity.
Qed.
(* pv_frame rides through a change of world and memory that keeps the frame's views and their presence (PvB_D_Kit.v
   pvd_frame_tr across a call, whose world moves) *)
Lemma pvcs_frame_tr_w : forall regs0 sp0 Y fa fl shb (W W' : world SEGS) mem mem',
  (forall a, (Y <= a < sp0 \/ fa <= a < fa + 64 \/ SHADOW_OFF + fa / 8 <= a < SHADOW_OFF + fa / 8 + 8) ->
     aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) ->
  (forall a, (Y <= a < sp0 \/ fa <= a < fa + 64) -> apresent (w_H W') mem' a) ->
  pv_frame regs0 sp0 Y fa fl shb W mem -> pv_frame regs0 sp0 Y fa fl shb W' mem'.
Proof.
intros regs0 sp0 Y fa fl shb W W' mem mem' HK HP (HYr & HY32 & HPR & Vsav & V48 & Vm & Vd & Vp & Vf & HPf & Hl & G).
assert (VT : forall a n v, (forall kk, (kk < n)%nat -> Y <= a + Z.of_nat kk < sp0 \/ fa <= a + Z.of_nat kk < fa + 64) ->
  val_mem SEGS (rdW W mem) a n v -> val_mem SEGS (rdW W' mem') a n v).
{ intros a n v Hr Hv. apply (pvcs_val_keep W W' mem mem' a n v Hv). intros x Hx. apply HK.
  destruct (Hr (Z.to_nat (x - a)) ltac:(lia)) as [H1 | H1]; [left | right; left]; lia. }
unfold pv_frame. split; [exact HYr|]. split; [exact HY32|].
split; [intros a Ha; apply HP; left; exact Ha|].
split.
{ rewrite Forall_forall in Vsav |- *. intros [o r] Hin. apply VT; [|exact (Vsav _ Hin)].
  intros kk Hk. left. cbn [fst].
  assert (Ho : -104 <= o <= -8).
  { unfold pv_saved in Hin. repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <-; lia|]). destruct Hin. }
  lia. }
split; [apply VT; [intros kk Hk; left; lia | exact V48]|].
split; [apply VT; [intros kk Hk; right; lia | exact Vm]|].
split; [apply VT; [intros kk Hk; right; lia | exact Vd]|].
split; [apply VT; [intros kk Hk; right; lia | exact Vp]|].
split; [apply VT; [intros kk Hk; right; lia | exact Vf]|].
split; [intros a Ha; apply HP; right; exact Ha|].
split; [exact Hl|].
apply (pvcs_garr8_keep W W' mem mem' _ _ G). intros x Hx. apply HK. right; right. rewrite Hl in Hx. cbn in Hx. lia.
Qed.
(* a chunk of a symbolic state (PvB_A.v pva_cv / pva_cv_ok / pva_val / pva_val8, restated) *)
Definition pvcs_cv (rs : smem) (j : nat) (off w : Z) : option YP09.chunk :=
  match find_region rs (Some j) off w with Some r => find_chunk (YP09.r_chunks r) off w | None => None end.
Lemma pvcs_cv_ok : forall E ss ms j off w c, st_ok SEGS E ss ms -> pvcs_cv (ss_mem ss) j off w = Some c ->
  YP09.chunk_ok SEGS E (ms_mem ms) (bv_unsigned (ew E j)) c.
Proof.
intros E ss ms j off w c HS H. unfold pvcs_cv in H.
destruct (find_region (ss_mem ss) (Some j) off w) as [r|] eqn:Hr; [|discriminate H].
destruct (find_region_sound _ _ _ _ _ Hr) as (Hin & Hb & _).
destruct (find_chunk_sound _ _ _ _ H) as (Hcin & _).
destruct (st_ok_mem_ok SEGS E ss ms HS) as (_ & Hrs & _).
destruct (proj1 (Forall_forall _ _) Hrs r Hin) as (_ & _ & _ & Hcs).
pose proof (proj1 (Forall_forall _ _) Hcs _ Hcin) as Hck. rewrite Hb in Hck. exact Hck.
Qed.
Lemma pvcs_val8 : forall E ss H ms j off e v b a, st_ok SEGS E ss (restrict H ms) ->
  pvcs_cv (ss_mem ss) j off 8 = Some (YP09.mkChunk off (CVal 8 e)) -> bv_unsigned (ew E j) = b -> a = b + off ->
  U E e = v -> val_mem SEGS (mrestrict H (ms_mem ms)) a 8 v.
Proof.
intros E ss H ms j off e v b a HS Hc Hb Ha Hv. subst a.
pose proof (pvcs_cv_ok E ss (restrict H ms) j off 8 _ HS Hc) as Hck. rewrite Hb in Hck.
apply (val_of_chunk_ok SEGS E _ _ off 8 e v Hck); [| rewrite <- Hv; unfold U; exact (bv_unsigned_in_range _ (sv_denot E e)) | cbn; lia].
rewrite <- Hv. unfold U. symmetry. apply Z_to_bv_bv_unsigned.
Qed.
(* ---- chains (PvB_A.v pva_fpchain_patch / pva_achain_patch, restated) ---- *)
Lemma pvcs_fpchain_patch : forall (rd rd' : reader) X L top ch bp,
  fpchain (rdword rd) bp top ch -> L + 16 <= bp -> bp + 16 <= top -> bp mod 8 = 0 -> X mod 8 = 0 ->
  (forall a, L <= a -> a + 8 <= top -> a mod 8 = 0 -> a <> X -> rdword rd' a = rdword rd a) ->
  (exists w, rdword rd' X = Some w /\ 4096 <= w < L) ->
  (exists w0, rdword rd X = Some w0 /\ 4096 <= w0) ->
  exists ch', fpchain (rdword rd') bp top ch' /\ Forall (fun r => bp <= fst (fst r)) ch'.
Proof.
intros rd rd' X L top ch. induction ch as [|[[fp ra] nfp] rest IH]; intros bp Hc HL Htop Hb8 HX8 Hag Hw' Hw0.
- destruct Hc as (r & Hr & Hr4).
  assert (Hne : bp - 8 <> X).
  { intros E. destruct Hw0 as (w0 & Hw0 & H4). rewrite <- E, Hr in Hw0. injection Hw0 as Ew. lia. }
  exists []. split; [|constructor]. exists r. split; [|exact Hr4]. rewrite (Hag (bp - 8)) by lia. exact Hr.
- destruct Hc as (Efp & Hal & Hra & Hnfp & Hra4 & Hrest). subst fp.
  assert (Hra' : exists ra', rdword rd' (bp - 8) = Some ra' /\ 4096 <= ra').
  { destruct (Z.eq_dec (bp - 8) X) as [E8 | N8].
    - destruct Hw' as (w & Hw & Hw4 & _). exists w. rewrite E8. split; [exact Hw | exact Hw4].
    - exists ra. rewrite (Hag (bp - 8)) by lia. split; [exact Hra | exact Hra4]. }
  destruct Hra' as (ra' & Hra'1 & Hra'2).
  destruct (Z.eq_dec (bp - 16) X) as [E16 | N16].
  + destruct Hw' as (w & Hw & Hwlo & Hwhi). exists [(bp, ra', w)].
    split; [|constructor; [cbn; lia | constructor]].
    cbn [fpchain]. split; [reflexivity|]. split; [exact Hal|]. split; [exact Hra'1|].
    split; [rewrite E16; exact Hw|]. split; [exact Hra'2|].
    replace (bad_next bp top w) with true; [reflexivity|]. unfold bad_next. symmetry.
    apply orb_true_intro. left. apply orb_true_intro. left. apply Z.leb_le. lia.
  + assert (Hn' : rdword rd' (bp - 16) = Some nfp) by (rewrite (Hag (bp - 16)) by lia; exact Hnfp).
    destruct (bad_next bp top nfp) eqn:Hbad.
    * exists [(bp, ra', nfp)]. split; [|constructor; [cbn; lia | constructor]].
      cbn [fpchain]. split; [reflexivity|]. split; [exact Hal|]. split; [exact Hra'1|]. split; [exact Hn'|].
      split; [exact Hra'2|]. rewrite Hbad. reflexivity.
    * pose proof Hbad as Hbad'. unfold bad_next in Hbad'.
      apply Bool.orb_false_iff in Hbad' as [Hb12 Hb3]. apply Bool.orb_false_iff in Hb12 as [Hb1 Hb2].
      apply Z.leb_gt in Hb1. apply Z.leb_gt in Hb2. apply Bool.negb_false_iff, Z.eqb_eq in Hb3.
      change (fpchain (rdword rd) nfp top rest) in Hrest.
      destruct (IH nfp Hrest ltac:(lia) ltac:(lia) Hb3 HX8 Hag Hw' Hw0) as (ch' & Hc' & Hf').
      exists ((bp, ra', nfp) :: ch'). split.
      -- cbn [fpchain]. split; [reflexivity|]. split; [exact Hal|]. split; [exact Hra'1|]. split; [exact Hn'|].
         split; [exact Hra'2|]. rewrite Hbad. exact Hc'.
      -- constructor; [cbn; lia|]. eapply Forall_impl; [|exact Hf']. intros r Hr. cbn beta in Hr |- *. lia.
Qed.
Lemma pvcs_achain_patch : forall ly (rd rd' : reader) sp v ch X,
  achain ly rd sp v ch -> X mod 8 = 0 ->
  (forall a, sp <= a -> a + 8 <= ly_top ly -> a mod 8 = 0 -> a <> X -> rdword rd' a = rdword rd a) ->
  (exists w, rdword rd' X = Some w /\ 4096 <= w < sp) -> (exists w0, rdword rd X = Some w0 /\ 4096 <= w0) ->
  exists ch', achain ly rd' sp v ch'.
Proof.
intros ly rd rd' sp v ch X [(Hb & ->) | (H1 & H2 & H3 & H4 & H5)] HX Hag Hw' Hw0.
- exists []. left. split; [exact Hb | reflexivity].
- destruct (pvcs_fpchain_patch rd rd' X sp (ly_top ly) ch v H4 ltac:(lia) ltac:(lia) H3 HX Hag Hw' Hw0)
    as (ch' & Hc' & Hf').
  exists ch'. right. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact Hc'|].
  eapply Forall_impl; [|exact Hf']. intros r Hr. cbn beta in Hr. lia.
Qed.
(* a word of 8 visible bytes is read *)
Lemma pvcs_rdword_some : forall (rd : reader) a, (forall i, 0 <= i < 8 -> rd (a + i) <> None) ->
  exists w, rdword rd a = Some w.
Proof.
intros rd a H. unfold rdword.
pose proof (H 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0.
destruct (rd a) as [b0|]; [|exfalso; exact (H0 eq_refl)].
destruct (rd (a + 1)) as [b1|] eqn:E1; [|exfalso; exact (H 1 ltac:(lia) E1)].
destruct (rd (a + 2)) as [b2|] eqn:E2; [|exfalso; exact (H 2 ltac:(lia) E2)].
destruct (rd (a + 3)) as [b3|] eqn:E3; [|exfalso; exact (H 3 ltac:(lia) E3)].
destruct (rd (a + 4)) as [b4|] eqn:E4; [|exfalso; exact (H 4 ltac:(lia) E4)].
destruct (rd (a + 5)) as [b5|] eqn:E5; [|exfalso; exact (H 5 ltac:(lia) E5)].
destruct (rd (a + 6)) as [b6|] eqn:E6; [|exfalso; exact (H 6 ltac:(lia) E6)].
destruct (rd (a + 7)) as [b7|] eqn:E7; [|exfalso; exact (H 7 ltac:(lia) E7)].
eexists. reflexivity.
Qed.
(* a word read through the view is a sum of bytes, so it is not negative *)
Lemma pvcs_rdword_nonneg : forall H mem a w, rdword (aview SEGS H mem) a = Some w -> 0 <= w.
Proof.
intros H mem a w E. unfold rdword in E.
assert (Hb : forall x b, aview SEGS H mem x = Some b -> 0 <= b).
{ intros x b Ex. unfold aview in Ex.
  destruct (mbyte SEGS (mrestrict H mem) x) as [bb|]; cbn [option_map] in Ex; [|discriminate Ex].
  injection Ex as <-. pose proof (bv_unsigned_in_range _ bb). lia. }
destruct (aview SEGS H mem a) as [b0|] eqn:E0; [|discriminate E].
destruct (aview SEGS H mem (a + 1)) as [b1|] eqn:E1; [|discriminate E].
destruct (aview SEGS H mem (a + 2)) as [b2|] eqn:E2; [|discriminate E].
destruct (aview SEGS H mem (a + 3)) as [b3|] eqn:E3; [|discriminate E].
destruct (aview SEGS H mem (a + 4)) as [b4|] eqn:E4; [|discriminate E].
destruct (aview SEGS H mem (a + 5)) as [b5|] eqn:E5; [|discriminate E].
destruct (aview SEGS H mem (a + 6)) as [b6|] eqn:E6; [|discriminate E].
destruct (aview SEGS H mem (a + 7)) as [b7|] eqn:E7; [|discriminate E].
injection E as <-.
pose proof (Hb _ _ E0). pose proof (Hb _ _ E1). pose proof (Hb _ _ E2). pose proof (Hb _ _ E3).
pose proof (Hb _ _ E4). pose proof (Hb _ _ E5). pose proof (Hb _ _ E6). pose proof (Hb _ _ E7). lia.
Qed.

Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.

(* ---- Section hypotheses ---- *)
(* the kit rule: YCbqG's 16-field record at the harness head length (the instance's AR_laws_x_xs) *)
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
(* the callee text: the kit's parse_string (lib/A/PRH_FnReader.v tparse_string_specX CTX0 CW at the batch kit's tip 240b06ed4fd4:
   the cursor set CW, prh_cw_ok at the call state, wild_room .. CW 0 at the call state; post at wbudget CW 0) *)
Hypothesis TPSTR : forall CTX0 CW, tparse_string_specX (fx := fx0) (PI := PIB) (PA := PA) B ARx SK CTX0 CW.
(* MARKED instance fact, discharged at lib/A/CfParamsPreset.v (cf_head = 16, preset source/alloc.c:31): a harness
   block's hidden head holds its 8-byte size word (PRH_Base.v prh_head_wide; PvB_X.v takes it in this spelling) *)
Hypothesis HHEAD : 8 <= cf_head.
(* MARKED image fact, discharged at PI_prog_B: alloc.c's five statics are image bytes, neither the runtime's own
   statics nor errno (FuzzFreeB.v / OwnB.v pal_pst_ok, with YC80x.v's PST_ok) *)
Hypothesis PSTOK : forall a, Exists (in_zr a) PSTX ->
  in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
(* MARKED image fact, discharged at PI_prog_B: no read-only byte is one of alloc.c's statics (S1ImgB.v pst_not_ro_B) *)
Hypothesis RONP : forall a, in_roP SEGS pa_relro_lo pa_relro_hi a -> ~ Exists (in_zr a) PSTX.
(* the two image facts of PvB_A_Home.v, in its spelling: *)
(* MARKED image fact, discharged at PI_prog_B: the image's shadow is mapped in every allocator state
   (img_shadow_vis_cf, lib/Reusable/YGcfAmx2.v, over ARx) *)
Hypothesis pvh_img_vis : forall ly S Hp W mem md a, ARx ly S Hp W mem md -> IMG_LO_B <= a < IMG_TOP_B ->
  aview SEGS (w_H W) mem (shadow_addr a) <> None.
(* MARKED image fact, discharged at PI_prog_B: the image's zero-shadow ranges are whole granules *)
Hypothesis pvh_zs_al : forall r, In r (as_zero_shadow B) -> fst r mod 8 = 0 /\ snd r mod 8 = 0.
(* MARKED instance fact, discharged at PI_prog_B (PAImg_prog.v: pa_lo := IMG_LO_B, pa_hi := IMG_TOP_B): the
   per-instance image bounds of the kit's kept_img / kept_at lie inside the B' image box the shadow-visibility fact
   covers (PvB_A_Home.v PA_BOX, same text) *)
Hypothesis PA_BOX : IMG_LO_B <= @pa_lo _ B_prog_listing PA /\ @pa_hi _ B_prog_listing PA <= IMG_TOP_B.
(* MARKED instance fact, discharged at lib/A/CfParamsPreset.v (CfParams_preset: cf_head = 16, preset source
   alloc.c:31; PresetReqAt.HEAD = 16, fuzz/alloc.c:28): the harness head the model's run events add (PresetReqAt.rd_hev)
   is the instance's, so parse_string's events at the call are parse_value's (PRH_FnReader.prhPs_evs_of_value) *)
Hypothesis HHD : cf_head = PresetReqAt.HEAD.

(* ---- where the node lies (rd_pre's prhReader_at without its window case, which rd_pre excludes) ---- *)
Definition pvcs_at (ly : alayout) (S : astate) (Lam : list (Z * Z)) (v : Z) : Prop :=
  (exists a k, In (a, k) Lam /\ a <= v /\ v + 56 <= a + k) \/
  (exists b m, In (b, m) (ablocks B ly S) /\ ~ In (b + cf_head, m - cf_head) Lam /\ b <= v /\ v + 56 <= b + m) \/
  (exists cid pos, In (cid, pos) (frames S) /\
     frame_addr ly cid pos <= v /\ v + 56 <= frame_addr ly cid pos + fs_frame_bytes cid).
Definition pvcs_loc (ly : alayout) (S : astate) (v : Z) : Prop :=
  (exists b m, In (b, m) (ablocks B ly S) /\ b <= v /\ v + 56 <= b + req_size m) \/
  (exists cid pos, In (cid, pos) (frames S) /\
     frame_addr ly cid pos <= v /\ v + 56 <= frame_addr ly cid pos + fs_frame_bytes cid).

Lemma pvcs_at_entry : forall en, pv_pre B ARx en -> pvcs_at (pe_ly en) (pe_S en) (pe_Lam en) (pe_v en).
Proof.
intros en HPRE.
assert (HRDP : rd_pre (fx := fx0) B (pe_STK en) (pe_ly en) (pe_S en) (pe_Hp en) (pe_W en) (pe_regs en)
  (pe_mem en) (pe_Lam en) (pe_peak en) (pe_cnt en) (pe_fail en) (pe_ran en) (pe_most en) (pe_own en) (pe_e en)
  (pe_q en) (pe_text en)
  (pe_len en) (pe_p en) (pe_d en) (pe_tb en) (pe_v en)) by (unfold pv_pre in HPRE; tauto).
pose proof HRDP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hnode & _ & _ & Hvwin & _).
pose proof Hnode as (_ & _ & _ & _ & Hvat & _).
destruct Hvat as [H | [H | [H | (H1 & H2)]]]; [left; exact H | right; left; exact H | right; right; exact H |].
exfalso. destruct Hvwin; lia.
Qed.
Lemma pvcs_at_tr : forall ly S ly' S' Lam v, incl (ablocks B ly S) (ablocks B ly' S') ->
  incl (frames S) (frames S') -> (forall c p, frame_addr ly' c p = frame_addr ly c p) ->
  pvcs_at ly S Lam v -> pvcs_at ly' S' Lam v.
Proof.
intros ly S ly' S' Lam v Ib If EF [H | [(b & m & Hin & H1) | (cid & p & Hin & H1)]].
- left; exact H.
- right; left. exists b, m. split; [apply Ib; exact Hin | exact H1].
- right; right. exists cid, p. split; [apply If; exact Hin | rewrite !EF; exact H1].
Qed.
Lemma pvcs_loc_of_at : forall ly S Hp W mem Lam peak cnt fail ran most own v,
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own -> pvcs_at ly S Lam v -> pvcs_loc ly S v.
Proof.
intros ly S Hp W mem Lam peak cnt fail ran most own v HL
  [(a & k & Hin & H1 & H2) | [(b & m & Hin & _ & H1 & H2) | Hf]].
- destruct HL as (_ & _ & HF & _). rewrite Forall_forall in HF.
  destruct (HF (a, k) Hin) as (Hk & Hab & _). cbn [fst snd] in Hk, Hab.
  pose proof (pvh_req_ge (k + cf_head)). left. exists (a - cf_head), (k + cf_head). split; [exact Hab | lia].
- pose proof (pvh_req_ge m). left. exists b, m. split; [exact Hin | lia].
- right. exact Hf.
Qed.
Lemma pvcs_loc_facts : forall ly S Hp W mem md v, ARx ly S Hp W mem md -> pvcs_loc ly S v ->
  4096 <= v /\ v + 56 <= alloc_ceiling /\ (forall x, v <= x < v + 56 -> ~ in_img SEGS x).
Proof.
intros ly S Hp W mem md v HAR [(b & m & Hin & H1 & H2) | (cid & p & Hin & H1 & H2)].
- destruct (alx_blocks SEGS B ARx LAWS _ _ _ _ _ _ _ _ HAR Hin) as (_ & H4096 & Hc & _).
  split; [lia|]. split; [lia|]. intros x Hx. exact (blk_img_x SEGS B ARx LAWS _ _ _ _ _ _ _ _ x HAR Hin ltac:(lia)).
- destruct (frames_bounds_x SEGS B ARx LAWS _ _ _ _ _ _ _ _ HAR Hin) as (H4096 & Hc & _).
  split; [lia|]. split; [lia|]. intros x Hx. exact (frm_img_x SEGS B ARx LAWS _ _ _ _ _ _ cid p x HAR Hin ltac:(lia)).
Qed.
(* the ledger's head words lie off the node: in another block, or below the node's own harness block's user bytes *)
Lemma pvcs_heads_apart : forall ly S Hp W mem md Hp' W' mem' Lam peak cnt fail ran most own v,
  ARx ly S Hp W mem md -> prh_ledger B ly S Hp' W' mem' Lam peak cnt fail ran most own -> pvcs_at ly S Lam v ->
  forall a k i, In (a, k) Lam -> 0 <= i < 8 -> 0 <= a - cf_head + i < 2 ^ 64 /\ ~ (v <= a - cf_head + i < v + 56).
Proof.
intros ly S Hp W mem md Hp' W' mem' Lam peak cnt fail ran most own v HAR HL Hat a k i Hin Hi.
pose proof ASAN_CEIL_range as HAC. unfold ASAN_CEIL in HAC.
destruct HL as (_ & _ & HF & _). rewrite Forall_forall in HF.
destruct (HF (a, k) Hin) as (Hk & Hab & _). cbn [fst snd] in Hk, Hab.
assert (Hkc : 0 < k + cf_head) by lia.
pose proof (pvh_req_eq (k + cf_head) Hkc) as Er.
destruct (alx_blocks SEGS B ARx LAWS _ _ _ _ _ _ _ _ HAR Hab) as (_ & H4096 & Hc & _). rewrite Er in Hc.
split; [lia|].
destruct Hat as [(a1 & k1 & Hin1 & H1 & H2) | [(b & m & Hinb & Hnl & H1 & H2) | (cid & p & Hinf & H1 & H2)]].
- destruct (HF (a1, k1) Hin1) as (Hk1 & Hab1 & _). cbn [fst snd] in Hk1, Hab1.
  destruct (Z.eq_dec a a1) as [<- | Hne]; [lia|].
  assert (Hne' : (a - cf_head, k + cf_head) <> (a1 - cf_head, k1 + cf_head)) by (intros X; injection X; lia).
  pose proof (sep_blocks_x SEGS B ARx LAWS _ _ _ _ _ _ _ _ _ _ HAR Hab Hab1 Hne') as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Er, (pvh_req_eq (k1 + cf_head)) in Hd by lia. lia.
- assert (Hne' : (a - cf_head, k + cf_head) <> (b, m)).
  { intros X. injection X as E1 E2. apply Hnl.
    replace (b + cf_head) with a by lia. replace (m - cf_head) with k by lia. exact Hin. }
  pose proof (sep_blocks_x SEGS B ARx LAWS _ _ _ _ _ _ _ _ _ _ HAR Hab Hinb Hne') as Hd.
  pose proof (pvh_req_ge m). unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Er in Hd. lia.
- pose proof (sep_block_frame_x SEGS B ARx LAWS _ _ _ _ _ _ _ _ _ _ HAR Hab Hinf) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Er in Hd. lia.
Qed.
(* alloc.c's statics lie off the node (image bytes; the node is a block's or a frame's) *)
Lemma pvcs_statics_apart : forall ly S Hp W mem md v, ARx ly S Hp W mem md -> pvcs_loc ly S v ->
  forall a, Exists (in_zr a) PSTX -> 0 <= a < 2 ^ 64 /\ ~ (v <= a < v + 56).
Proof.
intros ly S Hp W mem md v HAR Hl a Ha.
destruct (PSTOK a Ha) as (Hi & _). pose proof (@pa_segs_low _ B_prog_listing PA a Hi) as Hlo.
destruct (pvcs_loc_facts ly S Hp W mem md v HAR Hl) as (_ & _ & Hni).
split; [unfold kLowMemEnd in Hlo; lia|]. intros Hx. exact (Hni a Hx Hi).
Qed.
(* the ledger rides through a change that keeps alloc.c's statics (with #102's g_most / g_own_ran_out) and every head
   word *)
Lemma pvcs_ledger_heads : forall ly S Hp (W W' : world SEGS) m m' Lam peak cnt fail ran most own,
  prh_ledger B ly S Hp W m Lam peak cnt fail ran most own ->
  (forall a, Exists (in_zr a) PSTX -> aview SEGS (w_H W') m' a = aview SEGS (w_H W) m a) ->
  (forall a k i, In (a, k) Lam -> 0 <= i < 8 ->
     aview SEGS (w_H W') m' (a - cf_head + i) = aview SEGS (w_H W) m (a - cf_head + i)) ->
  prh_ledger B ly S Hp W' m' Lam peak cnt fail ran most own.
Proof.
intros ly S Hp W W' m m' Lam peak cnt fail ran most own (HG & HN & HF & HP) Kp Kh.
assert (KP : forall a0 (n0 : nat) v0, In (a0, Z.of_nat n0) PSTX -> val_mem SEGS (rdW W m) a0 n0 v0 ->
  val_mem SEGS (rdW W' m') a0 n0 v0).
{ intros a0 n0 v0 Hin Hv. apply (pvcs_val_keep W W' m m' a0 n0 v0 Hv). intros x Hx. apply Kp.
  apply Exists_exists. exists (a0, Z.of_nat n0). split; [exact Hin|]. unfold in_zr. cbn [fst snd]. lia. }
split; [|split; [exact HN | split; [|exact HP]]].
- destruct HG as (G1 & G2 & G3 & G4 & G5 & (Gm & Gmb) & (Go & Gob) & Hr). unfold prh_glob.
  split; [apply (KP _ _ _ ltac:(unfold prh_pst; cbn [In]; left; reflexivity) G1)|].
  split; [apply (KP _ _ _ ltac:(unfold prh_pst; cbn [In]; right; left; reflexivity) G2)|].
  split; [apply (KP _ _ _ ltac:(unfold prh_pst; cbn [In]; right; right; left; reflexivity) G3)|].
  split; [apply (KP _ _ _ ltac:(unfold prh_pst; cbn [In]; right; right; right; left; reflexivity) G4)|].
  split; [apply (KP _ _ _ ltac:(unfold prh_pst; cbn [In]; right; right; right; right; left; reflexivity) G5)|].
  split.
  { split; [|exact Gmb].
    apply (KP _ _ _ ltac:(unfold prh_pst; cbn [In]; right; right; right; right; right; left; reflexivity) Gm). }
  split; [|exact Hr].
  split; [|exact Gob].
  apply (KP _ _ _ ltac:(unfold prh_pst; cbn [In]; right; right; right; right; right; right; left; reflexivity) Go).
- rewrite Forall_forall in HF |- *. intros [a k] Hin. destruct (HF (a, k) Hin) as (Hk & Hab & Hhp & Ha16 & Hv).
  cbn [fst snd] in *. split; [exact Hk|]. split; [exact Hab|]. split; [exact Hhp|]. split; [exact Ha16|].
  apply (pvcs_val_keep W W' m m' _ 8 k Hv). intros x Hx. cbn in Hx.
  replace x with (a - cf_head + (x - (a - cf_head))) by lia. apply (Kh a k); [exact Hin | lia].
Qed.

Lemma pvcs_loc_tr : forall ly S ly' S' v, incl (ablocks B ly S) (ablocks B ly' S') ->
  incl (frames S) (frames S') -> (forall c p, frame_addr ly' c p = frame_addr ly c p) ->
  pvcs_loc ly S v -> pvcs_loc ly' S' v.
Proof.
intros ly S ly' S' v Ib If EF [(b & m & Hin & H1) | (cid & p & Hin & H1)].
- left. exists b, m. split; [apply Ib; exact Hin | exact H1].
- right. exists cid, p. split; [apply If; exact Hin | rewrite !EF; exact H1].
Qed.
(* the node's bytes are present at every allocator state where it lies in a live block or frame *)
Lemma pvcs_loc_present : forall ly S Hp W mem md v, ARx ly S Hp W mem md -> pvcs_loc ly S v ->
  forall x, v <= x < v + 56 -> apresent (w_H W) mem x.
Proof.
intros ly S Hp W mem md v HAR [(b & m & Hin & H1 & H2) | (cid & p & Hin & H1 & H2)] x Hx.
- destruct (alx_blocks SEGS B ARx LAWS _ _ _ _ _ _ _ _ HAR Hin) as (_ & _ & _ & _ & Hb & _).
  exact (proj1 (Hb x ltac:(lia))).
- destruct (alx_frames SEGS B ARx LAWS _ _ _ _ _ _ _ _ HAR Hin) as (_ & _ & Hf & _).
  exact (proj1 (Hf x ltac:(lia))).
Qed.
(* the one block a call adds is not a block of the call state, and it is apart from each of them *)
Lemma pvcs_newblock : forall ly S ly' S' Hp' W' mem' md' p n, ARx ly' S' Hp' W' mem' md' ->
  ablocks B ly' S' = ablocks B ly S ++ [(p, n)] -> 0 <= n ->
  ~ In (p, n) (ablocks B ly S) /\
  (forall b m, In (b, m) (ablocks B ly S) -> zdisjoint (b, req_size m) (p, req_size n)).
Proof.
intros ly S ly' S' Hp' W' mem' md' p n HAR E Hn.
assert (Hin : In (p, n) (ablocks B ly' S')) by (rewrite E; apply in_or_app; right; left; reflexivity).
destruct (alx_blocks SEGS B ARx LAWS _ _ _ _ _ _ _ _ HAR Hin) as (_ & _ & _ & _ & _ & Hpw).
rewrite E, map_app in Hpw.
change (map (fun b : Z * Z => (fst b, req_size (snd b))) [(p, n)]) with [(p, req_size n)] in Hpw.
apply pvcs_pairwise_last in Hpw. rewrite Forall_forall in Hpw.
assert (Hd : forall b m, In (b, m) (ablocks B ly S) -> zdisjoint (b, req_size m) (p, req_size n)).
{ intros b m Hbm. exact (Hpw (b, req_size m) (in_map (fun b0 : Z * Z => (fst b0, req_size (snd b0))) _ (b, m) Hbm)). }
split; [|exact Hd]. intros Hx. pose proof (Hd p n Hx) as H. pose proof (req_size_pos n Hn) as Hr.
unfold zdisjoint in H. cbn [fst snd] in H. lia.
Qed.
(* the added block lies off the node, which is in a block or a frame of the call state *)
Lemma pvcs_node_new : forall ly S ly' S' Hp' W' mem' md' p n v, ARx ly' S' Hp' W' mem' md' ->
  ablocks B ly' S' = ablocks B ly S ++ [(p, n)] -> 0 <= n -> incl (frames S) (frames S') ->
  (forall c q, frame_addr ly' c q = frame_addr ly c q) -> pvcs_loc ly S v ->
  forall x, p <= x < p + req_size n -> ~ (v <= x < v + 56).
Proof.
intros ly S ly' S' Hp' W' mem' md' p n v HAR E Hn If EF Hl x Hx Hv.
destruct (pvcs_newblock ly S ly' S' Hp' W' mem' md' p n HAR E Hn) as (_ & Hd).
destruct Hl as [(b & m & Hin & H1 & H2) | (cid & c & Hin & H1 & H2)].
- pose proof (Hd b m Hin) as H. unfold zdisjoint in H. cbn [fst snd] in H. lia.
- assert (Hin' : In (p, n) (ablocks B ly' S')) by (rewrite E; apply in_or_app; right; left; reflexivity).
  pose proof (sep_block_frame_x SEGS B ARx LAWS _ _ _ _ _ _ _ _ _ _ HAR Hin' (If _ Hin)) as H.
  unfold zdisjoint in H. cbn [fst snd] in H. rewrite EF in H. lia.
Qed.

(* ---- THE ARM ---- *)
Lemma pvd_call_str : pvd_str_goal B ARx.
Proof.
unfold pvd_str_goal.
intros en y Y fa fl pos lyc Sc k W' memC regs mem mdc HPRE Hsk HCS Hty R10 KX.
unfold pvd_kxR, YA0nH.SRr' in KX. unfold YA0nH.SRr'.
destruct HCS as (HKR & R9 & R19 & R20 & R24 & R1 & HBODY & HCHAIN & HRD0 & HEQ & HGRC & HMNc).
pose proof HBODY as (HFRM & HinF & Efa & Efl & HJ & HWIN).
pose proof HKR as (R2 & R8 & R18 & R26 & R27 & R23 & R3 & R4).
pose proof HFRM as (HYr & HY32 & HPR0 & Vsav & Vfa48 & Vmagic & Vdesc & Vpc & Vfl & HPRfa & Hshlen & Gsh).
(* pv_pre's parts by type *)
assert (HFPRE : fpre B ARx (pe_STK en) (pe_ly en) (pe_S en) (pe_Hp en) (pe_W en) (pe_regs en) (pe_mem en) (pe_md en)
  (pe_ch en)) by (unfold pv_pre in HPRE; tauto).
assert (HRDP : rd_pre (fx := fx0) B (pe_STK en) (pe_ly en) (pe_S en) (pe_Hp en) (pe_W en) (pe_regs en)
  (pe_mem en) (pe_Lam en) (pe_peak en) (pe_cnt en) (pe_fail en) (pe_ran en) (pe_most en) (pe_own en) (pe_e en)
  (pe_q en) (pe_text en)
  (pe_len en) (pe_p en) (pe_d en) (pe_tb en) (pe_v en)) by (unfold pv_pre in HPRE; tauto).
assert (HUNIV : prh_univ_closure B (pe_CTX0 en)) by (unfold pv_pre in HPRE; tauto).
assert (HCURE : prh_cur_entry (pe_W en) (pe_mem en) (pe_regs en) (pe_q en))
  by (unfold pv_pre in HPRE; tauto).
assert (HCWE : prh_cw_entry B (pe_CW en) (pe_W en) (pe_mem en) (pe_regs en) (pe_q en))
  by (unfold pv_pre in HPRE; tauto).
assert (HWR0 : YCbqGwild.wild_room (as_universe B) (pe_CW en) 0 (st_depot (pe_S en)))
  by (unfold pv_pre in HPRE; tauto).
assert (HHB0 : PresetHullBudget.hull_budget (pe_S en) (PresetReqAt.rd_hevs (pe_gt en)))
  by (unfold pv_pre in HPRE; tauto).
assert (HQCH : (pe_sp en <= pe_q en < pe_sp en + 16) \/
   (pe_sp en + 16 <= pe_q en /\
    exists ch', achain (pe_ly en) (aview SEGS (w_H (pe_W en)) (pe_mem en)) (spZ (pe_regs en))
      (prh_s0 F_parse_string (pe_q en)) ch')) by (unfold pv_pre in HPRE; tauto).
pose proof HFPRE as (HAFN & HRO & Hhi64 & _).
pose proof HAFN as (HAR0 & Hra_ok & Hra4 & Hgp & Htp & Hstk0 & Hpres0 & Hchain & HQT0).
pose proof Hstk0 as (Hal16 & HSTK0 & Hceil0 & Hslo0 & Hshi0 & H470 & Hbot0 & Htop20 & Htop0).
pose proof HRDP as (Hfrm0 & Hmuniv & Hruniv1 & Hruniv2 & Hcur0 & Hwin & Hqlo & Hqhi & Hqra & Hsrc & Hhome &
  Hmaxrun & Hnode & Hqv & Htv0 & Hvwin & HLED0 & Hdmax & Hcntb & Htxc).
pose proof Hwin as (He0 & He16 & Hetop & Hepres).
pose proof Hnode as (Hv4096 & Hv8 & Hvrw & Hvz & Hvat & Hvam & Hvown & Hvra).
pose proof HRD0 as (Hfrs & Habl & Hbb & HROOMc & HCUR & HSRC & HHOME & HVEQ & HVRA & HLEDc & HRPc & HSECc).
pose proof HCUR as (Vp1 & Vend & Vdep & Hqrw & Hq8 & Htx0 & Htx62 & Hp1r & Htblen & Gtb & Hqt & Hd32).
(* rd_pre's text / node apartness is guarded by 0 < len (the batch kit): the text is not empty, the C1 cursor p1 = end - |34 :: y|
   lies in [text, text + len] *)
assert (Htv : pe_text en + pe_len en <= pe_v en \/ pe_v en + 56 <= pe_text en).
{ apply Htv0. assert (Hl1 : 1 <= Z.of_nat (length (34 :: y))) by (cbn [length]; lia). clear - Hp1r Hl1. lia. }
clear Htv0.
pose proof Hcur0 as (Vp0 & _ & _ & _ & _ & _ & _ & Hp0r & Htblen0 & _).
pose proof (ajx_ar HJ) as HAR. pose proof (ajx_ly HJ) as Hly. pose proof (ajx_secs HJ) as Hsecs.
pose proof (ajx_wle HJ) as Hwle. pose proof (ajx_io HJ) as Hio. pose proof (ajx_frs HJ) as Hfrs'.
pose proof (ajx_nev HJ) as Hnev. pose proof (ajx_k HJ) as Hk0. pose proof (ajx_hi HJ) as J1.
pose proof (ajx_blk HJ) as J2. pose proof (ajx_img HJ) as J3. pose proof (ajx_frm HJ) as J4.
pose proof (ajx_gone HJ) as Jgone. pose proof (ajx_pres HJ) as Hpres. pose proof (ajx_stk HJ) as Hstk.
pose proof (ajx_extra HJ) as J5. pose proof (ajx_qt HJ) as HQT.
pose proof Hstk as (Hsp16 & HSTK1 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof Hly as (_ & _ & _ & _ & _ & EF4 & _ & _ & Etop & Eslo & Eshi & _).
assert (EF : forall c p, frame_addr lyc c p = frame_addr (pe_ly en) c p)
  by (intros; unfold frame_addr; rewrite EF4; reflexivity).
pose proof ASAN_CEIL_range as HAC. unfold ASAN_CEIL in HAC.
set (sp0 := pe_sp en) in *. set (ee := pe_e en) in *.
set (q := pe_q en) in *. set (v := pe_v en) in *. set (text := pe_text en) in *. set (len := pe_len en) in *.
change (spZ (pe_regs en)) with sp0 in *.
set (p1 := text + len - Z.of_nat (length (34 :: y))) in *.
assert (HSTKe : pe_STK en = Z.of_nat (S (PjGrammar.MAXD - pe_d en)) * 320 + 16560) by reflexivity.
assert (HSTK : 16880 <= pe_STK en) by (rewrite HSTKe; nia).
assert (HpsV : STK_parse_string = 16560) by (vm_compute; reflexivity).
(* ---- bounds ---- *)
assert (Hsp_lo : alloc_ceiling + 4272 <= sp0) by (clear - Hceil0 Hslo0 HSTK; lia).
assert (Hsp_hi : sp0 + ee <= 2 ^ 47) by (clear - Hshi H47; lia).
assert (HYb : sp0 - 176 <= Y <= sp0 - 160) by exact HYr.
assert (Hq_lo : sp0 <= q) by exact Hqlo.
pose proof Hsrc as (Hsbytes & Htx4096 & Htxceil & Htxam & Htxra & Hsrcrest).
(* where the node lies, at the entry and at the call state *)
pose proof (pvcs_at_entry en HPRE) as Hat0. change (pe_v en) with v in Hat0.
assert (Hatc : pvcs_at lyc Sc (pe_Lam en) v).
{ apply (pvcs_at_tr (pe_ly en) (pe_S en)); [rewrite Habl; apply incl_refl | rewrite Hfrs; apply incl_tl, incl_refl |
    exact EF | exact Hat0]. }
pose proof (pvcs_loc_of_at _ _ _ _ _ _ _ _ _ _ _ _ _ HLEDc Hatc) as Hlocc.
destruct (pvcs_loc_facts _ _ _ _ _ _ _ HAR Hlocc) as (Hv4k & Hvceil & Hvimg).
(* ---- the C1 reader facts at the call memory ---- *)
assert (AVC : forall a, 0 <= a < 2 ^ 64 -> ~ (v <= a < v + 4) ->
  aview SEGS (w_H W') mem a = aview SEGS (w_H W') memC a) by exact (pvcs_av_off W' memC mem v 4 HEQ).
assert (HCUR3 : pj_in_okR SEGS (rdW W' mem) q text len p1 (Z.of_nat (pe_d en)) (pe_tb en)).
{ apply (pvcs_in_keep W' W' memC mem q text len p1 _ _ HCUR).
  - intros x Hx. apply AVC; [lia|]. clear - Hqv Hx. lia.
  - intros x Hx. apply AVC; [lia|]. clear - Htv Hx. lia.
  - intros x Hx. split; [lia|]. intros Hi. pose proof (@pa_segs_low _ B_prog_listing PA x Hi).
    unfold kLowMemEnd in *. lia. }
assert (HLED3 : prh_ledger B lyc Sc (pe_Hp en) W' mem (pe_Lam en) (pe_peak en) (pe_cnt en) (pe_fail en) (pe_ran en)
  (pe_most en) (pe_own en)).
{ apply (pvcs_ledger_heads lyc Sc (pe_Hp en) W' W' memC mem _ _ _ _ _ _ _ HLEDc).
  - intros a Ha. destruct (pvcs_statics_apart _ _ _ _ _ _ _ HAR Hlocc a Ha) as [Hr Hn]. apply AVC; [exact Hr|].
    intros X. apply Hn. lia.
  - intros a k0 i Hin Hi.
    destruct (pvcs_heads_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HAR HLEDc Hatc a k0 i Hin Hi) as [Hr Hn].
    apply AVC; [exact Hr|]. intros X. apply Hn. lia. }
assert (HSRC3 : src_rd W' mem text (pe_tb en)).
{ apply (pva_src_rd_at B ARx LAWS pvh_img_vis pvh_zs_al PA_BOX lyc Sc (pe_Hp en) W' mem mdc (pe_Lam en) _ _ _ _ _ _ W'
    memC
    text (pe_tb en) HAR HLED3); [rewrite Htblen; exact HHOME | exact HSRC |].
  intros x Hx. apply AVC; [lia|]. clear - Htv Hx Htblen. lia. }
(* the cursor after the white space and after the quote *)
pose proof (pvm_skip_rest (pe_tb en) text len (pe_p en) Htblen0 Hp0r) as [Hrest1 Hp1b].
change (rest_atR (pe_tb en) text (pe_p en)) with (pe_rest en) in Hrest1, Hp1b.
rewrite Hsk in Hrest1, Hp1b. change (text + len - Z.of_nat (length (34 :: y))) with p1 in Hrest1, Hp1b.
assert (Hlen34 : Z.of_nat (length (34 :: y)) = Z.of_nat (length y) + 1) by (cbn [length]; lia).
assert (Hp1end : p1 < text + len) by (unfold p1; lia).
assert (Hnth34 : nth_error (pe_tb en) (Z.to_nat (p1 - text)) = Some 34).
{ pose proof Hrest1 as H. unfold rest_atR in H. destruct (pvd_nth_skipn _ _ _ _ H) as [Hn Hl].
  rewrite <- Hn. apply nth_error_nth'. exact Hl. }
assert (Hrest2 : rest_atR (pe_tb en) text (p1 + 1) = y).
{ pose proof Hrest1 as H. unfold rest_atR in H |- *.
  replace (Z.to_nat (p1 + 1 - text)) with (1 + Z.to_nat (p1 - text))%nat by lia.
  rewrite <- skipn_skipn, H. reflexivity. }
(* parse_string's two live-count premises at the call state (the text's, over the all-granted events prhPs_evs .. []):
   pv_pre's over parse_value's granted run, which at the quote IS parse_string's, at the call state by pv_reader0's
   room keep (PvB_D_Str.v pvs_counts) *)
destruct (pvs_counts B ARx en y Sc HHD HPRE Hsk HRPc) as (HPKS3 & HPK243).
rewrite <- Hrest2 in HPKS3, HPK243.
(* the call chain from the callee's sp Y through parse_value's own record *)
set (rdc := fun a => if (0 <=? a) && (a <? 2 ^ 64) then aview SEGS (w_H W') mem a else aview SEGS (w_H W') memC a).
destruct (HCHAIN rdc) as (ch1 & Hch1c).
{ intros a Ha. unfold rdc. destruct ((0 <=? a) && (a <? 2 ^ 64)) eqn:Er; [|reflexivity].
  apply andb_prop in Er as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. apply AVC; [lia | exact Ha]. }
assert (Hch1 : achain lyc (aview SEGS (w_H W') mem) Y sp0 ch1).
{ apply (achain_kept lyc rdc _ Y sp0 ch1 Y Hch1c ltac:(lia) ltac:(rewrite Etop; lia)).
  intros a Ha. unfold rdc. replace ((0 <=? a) && (a <? 2 ^ 64)) with true; [reflexivity|].
  symmetry. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
assert (HspY : spZ regs = Y) by (unfold spZ; rewrite R2; apply unsigned_lit_small; lia).
assert (Hs0 : s0Z regs = sp0) by (unfold s0Z; rewrite R8; apply unsigned_lit_small; lia).
assert (HQRA3 : range_addressable (aview SEGS (w_H W') mem) SHADOW_OFF q 24).
{ apply (pvd_stack_ra B ARx LAWS lyc Sc (pe_Hp en) W' mem mdc q 24 HAR); [rewrite Eslo | rewrite Eshi];
    clear - Hslo Hqlo Hqhi Hshi HSTK1 HSTK; lia. }
(* ---- the cursor chain at the call view (prh_s0 F_parse_string q = q, parse_string's frame 144) ---- *)
pose proof Hcur0 as (_ & _ & Vdep0 & _).
pose proof HCUR3 as (Vp3 & _ & Vdep3 & _).
assert (Hs0q : prh_s0 F_parse_string q = q).
{ unfold prh_s0. assert (E : pi_s0cur F_parse_string = Some 0) by reflexivity. rewrite E. lia. }
assert (E144 : pi_frame F_parse_string = 144) by reflexivity.
assert (Rs8 : rdword (aview SEGS (w_H W') mem) (sp0 - 8) = Some (raZ (pe_regs en))).
{ pose proof (proj1 (Forall_forall _ _) Vsav (-8, 1) ltac:(unfold pv_saved; cbn [In]; tauto)) as V.
  cbn [fst snd] in V. replace (sp0 - 8) with (sp0 + -8) by lia.
  apply pvcs_rdword_of_val; [exact (pvcs_val_lit _ _ _ _ _ (1%bv : bv 5) 1 eq_refl V) | apply bv_unsigned_in_range]. }
assert (Rs16 : rdword (aview SEGS (w_H W') mem) (sp0 - 16) = Some (s0Z (pe_regs en))).
{ pose proof (proj1 (Forall_forall _ _) Vsav (-16, 8) ltac:(unfold pv_saved; cbn [In]; tauto)) as V.
  cbn [fst snd] in V. replace (sp0 - 16) with (sp0 + -16) by lia.
  apply pvcs_rdword_of_val; [exact (pvcs_val_lit _ _ _ _ _ (8%bv : bv 5) 8 eq_refl V) | apply bv_unsigned_in_range]. }
(* the s0 - 16 word's bound (prh_cur_entry) and the s0 - 8 word's trace in CW (prh_cw_entry), at parse_string *)
pose proof (proj2 HCURE F_parse_string (or_introl eq_refl)) as HCE16.
pose proof (fun r w Hr => HCWE F_parse_string r w (or_introl eq_refl) Hr) as HCE8.
rewrite Hs0q in HCE8, HCE16.
assert (NFP : forall a, ~ (q <= a < q + 8) -> ~ (q + 16 <= a < q + 20) -> ~ (v <= a < v + 56) ->
  ~ inFP (pe_FP en) a).
{ intros a H1 H2 H3 (r & Hr & Hra). unfold pe_FP in Hr.
  destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hra; [exact (H1 Hra) | exact (H2 Hra) | exact (H3 Hra)]. }
(* the caller's stack above sp0, off FP: the window clause below sp0 + e, the journal's stack clause above *)
assert (KST : forall a, sp0 <= a < 2 ^ 47 -> ~ inFP (pe_FP en) a ->
  aview SEGS (w_H W') mem a = aview SEGS (w_H (pe_W en)) (pe_mem en) a).
{ intros a Ha Hn. destruct (Z_lt_le_dec a (sp0 + ee)) as [Hlt | Hge].
  - apply HWIN; [clear - Ha Hlt; lia | exact Hn].
  - apply J1; clear - Ha Hge Hsp_lo HAC; lia. }
assert (Hqc : q = sp0 \/ q = sp0 + 8 \/ sp0 + 16 <= q) by (clear - Hq_lo Hq8 Hal16; lia).
assert (HCURS : (exists ch, achain lyc (aview SEGS (w_H W') mem) (Y - 144) q ch) /\
   prh_cw_ok B (pe_CW en) W' mem F_parse_string q /\ prh_cur_low W' mem F_parse_string q).
{ clear - Hs0q Hch1 Rs8 Rs16 HCE8 HCE16 KST NFP Hepres HQCH Vdep0 Vdep3 Vp0 Vp3 Hqc Hq_lo Hq8 Hal16 HYb Hsp_lo
    Hqhi He0 Htop2 Htop H47 Etop Hp1r Hp0r Htxceil Htblen0 Htx4096 Hv4k Hvceil HAC.
  unfold prh_cw_ok, prh_cur_low. rewrite Hs0q.
  destruct Hqc as [Eq | [Eq | Hq16]].
  - (* q = sp0: parse_value's own record, then the entry's chain (pv_chain) *)
    split; [exists ch1; apply (achain_lower lyc _ Y (Y - 144) q ch1); [rewrite Eq; exact Hch1 | lia]|].
    split.
    + intros r w Hr Hw. replace (q - 8) with (sp0 - 8) in Hw by lia. rewrite Rs8 in Hw. injection Hw as <-.
      apply (HCE8 r _ Hr). unfold prh_word_entry.
      replace (q - 8 =? spZ (pe_regs en) - 8) with true; [reflexivity|].
      symmetry. apply Z.eqb_eq. change (spZ (pe_regs en)) with sp0. lia.
    + intros w Hw. replace (q - 16) with (sp0 - 16) in Hw by lia. rewrite Rs16 in Hw. injection Hw as <-.
      apply HCE16. unfold prh_word_entry.
      replace (q - 16 =? spZ (pe_regs en) - 8) with false
        by (symmetry; apply Z.eqb_neq; change (spZ (pe_regs en)) with sp0; lia).
      replace (q - 16 =? spZ (pe_regs en) - 16) with true; [reflexivity|].
      symmetry. apply Z.eqb_eq. change (spZ (pe_regs en)) with sp0. lia.
  - (* q = sp0 + 8: one record (ra = the word at sp0), whose next frame word is parse_value's saved ra *)
    assert (Hraw : raZ (pe_regs en) < alloc_ceiling).
    { apply HCE16. unfold prh_word_entry.
      replace (q - 16 =? spZ (pe_regs en) - 8) with true; [reflexivity|].
      symmetry. apply Z.eqb_eq. change (spZ (pe_regs en)) with sp0. lia. }
    assert (K0 : forall i, 0 <= i < 8 ->
      aview SEGS (w_H W') mem (sp0 + i) = aview SEGS (w_H (pe_W en)) (pe_mem en) (sp0 + i)).
    { intros i Hi. apply KST; [lia|]. apply NFP; lia. }
    split; [| split].
    + destruct (pvcs_rdword_some (aview SEGS (w_H W') mem) sp0) as (w0 & Hw0).
      { intros i Hi. rewrite K0 by exact Hi. apply pvcs_present_view. apply Hepres. lia. }
      destruct (Z_lt_le_dec q (ly_top lyc - 16)) as [Htl | Htl].
      * destruct (Z_lt_le_dec w0 4096) as [Hw4 | Hw4].
        -- exists []. right. split; [lia|]. split; [exact Htl|]. split; [lia|].
           split; [|constructor]. cbn [fpchain]. exists w0.
           split; [replace (q - 8) with sp0 by lia; exact Hw0|].
           pose proof (pvcs_rdword_nonneg _ _ _ _ Hw0). lia.
        -- exists [(q, w0, raZ (pe_regs en))]. right. split; [lia|]. split; [exact Htl|]. split; [lia|].
           split; [|constructor; [cbn [fst]; lia | constructor]].
           cbn [fpchain]. split; [reflexivity|]. split; [lia|].
           split; [replace (q - 8) with sp0 by lia; exact Hw0|].
           split; [replace (q - 16) with (sp0 - 8) by lia; exact Rs8|]. split; [exact Hw4|].
           replace (bad_next q (ly_top lyc) (raZ (pe_regs en))) with true; [reflexivity|].
           unfold bad_next. symmetry. apply orb_true_intro. left. apply orb_true_intro. left. apply Z.leb_le. lia.
      * exists []. left. split; [right; left; lia | reflexivity].
    + intros r w Hr Hw. replace (q - 8) with sp0 in Hw by lia. apply (HCE8 r w Hr). unfold prh_word_entry.
      replace (q - 8 =? spZ (pe_regs en) - 8) with false
        by (symmetry; apply Z.eqb_neq; change (spZ (pe_regs en)) with sp0; lia).
      replace (q - 8 =? spZ (pe_regs en) - 16) with false
        by (symmetry; apply Z.eqb_neq; change (spZ (pe_regs en)) with sp0; lia).
      replace (q - 8) with sp0 by lia. rewrite <- Hw. apply pvcs_rdword_ext. intros i Hi. symmetry. exact (K0 i Hi).
    + intros w Hw. replace (q - 16) with (sp0 - 8) in Hw by lia. rewrite Rs8 in Hw. injection Hw as <-. exact Hraw.
  - (* q >= sp0 + 16: the entry's chain from q, its p word patched *)
    destruct HQCH as [Hqa | (_ & che & Hche)]; [lia|].
    change (spZ (pe_regs en)) with sp0 in Hche. rewrite Hs0q in Hche.
    assert (KNQ : forall a, sp0 <= a -> a + 8 <= ly_top (pe_ly en) -> a mod 8 = 0 -> a <> q ->
      rdword (aview SEGS (w_H W') mem) a = rdword (aview SEGS (w_H (pe_W en)) (pe_mem en)) a).
    { intros a Ha Htopa Ha8 Haq. apply pvcs_rdword_ext. intros i Hi.
      destruct (Z.eq_dec a (q + 16)) as [Eaq | Naq].
      - destruct (Z_lt_le_dec i 4) as [Hi4 | Hi4].
        + apply (pvcs_av_of_val (pe_W en) W' (pe_mem en) mem (q + 16) 4 (Z.of_nat (pe_d en)));
            [exact Vdep0 | exact Vdep3 | cbn; lia].
        + apply KST; [lia|]. apply NFP; lia.
      - apply KST; [lia|]. apply NFP; lia. }
    destruct (pvcs_achain_patch (pe_ly en) (aview SEGS (w_H (pe_W en)) (pe_mem en)) (aview SEGS (w_H W') mem)
      sp0 q che q Hche Hq8 KNQ) as (chq & Hchq).
    { exists p1. split; [apply pvcs_rdword_of_val; [exact Vp3 | lia] | lia]. }
    { exists (pe_p en). split; [apply pvcs_rdword_of_val; [exact Vp0 | lia] | lia]. }
    split; [exists chq; apply (achain_lower lyc _ sp0 (Y - 144) q chq);
      [exact (achain_ly_top (pe_ly en) lyc _ sp0 q chq Etop Hchq) | lia]|].
    split.
    + intros r w Hr Hw. apply (HCE8 r w Hr). unfold prh_word_entry.
      replace (q - 8 =? spZ (pe_regs en) - 8) with false
        by (symmetry; apply Z.eqb_neq; change (spZ (pe_regs en)) with sp0; lia).
      replace (q - 8 =? spZ (pe_regs en) - 16) with false
        by (symmetry; apply Z.eqb_neq; change (spZ (pe_regs en)) with sp0; lia).
      rewrite <- Hw. symmetry. apply KNQ; lia.
    + intros w Hw. apply HCE16. unfold prh_word_entry.
      replace (q - 16 =? spZ (pe_regs en) - 8) with false
        by (symmetry; apply Z.eqb_neq; change (spZ (pe_regs en)) with sp0; lia).
      replace (q - 16 =? spZ (pe_regs en) - 16) with false
        by (symmetry; apply Z.eqb_neq; change (spZ (pe_regs en)) with sp0; lia).
      rewrite <- Hw. symmetry. apply KNQ; lia. }
(* parse_string's live premise (the batch kit's tip 03fcabb582d0, PRH_FnReader.v :566-576): the request half as before (from
   rd_room's prh_maxreq), and the per-event live room over the callee's own events, which ARE the value's
   (PvB_D_Str.v pvs_trace + PRH_FnReader.prhPs_evs_model at cf_head = HEAD), so it is rd_room Sc's third conjunct *)
assert (Egt3 : PresetReqAt.rd_hevs (pe_gt en) = prhPs_evs y []).
{ unfold pe_gt, prhPv_gtrace. rewrite (pvs_trace prh_jr_strtod (pe_d en) (pe_rest en) y [] Hsk).
  symmetry. exact (prhPs_evs_model y [] HHD). }
(* parse_string's hull budget at the call state: pv_pre's over parse_value's events, which at the quote ARE
   parse_string's (Egt3), the meters kept from entry (pv_reader0's secs_same) *)
assert (HHULLs : PresetHullBudget.hull_budget Sc (prhPs_evs (rest_atR (pe_tb en) text (p1 + 1)) [])).
{ rewrite Hrest2, <- Egt3. exact (PresetHullBudget.hull_budget_same (pe_S en) Sc _ HSECc HHB0). }
assert (HROOM3 : (forall Q, PjGrammar.scan (rest_atR (pe_tb en) text (p1 + 1)) = Some Q ->
   LIVE_parse_string Q < cf_malloc_max) /\
  prh_live_evs Sc (prhPs_evs (rest_atR (pe_tb en) text (p1 + 1)) [])).
{ pose proof HROOMc as (_ & Hmaxreq & Hlive). rewrite Egt3 in Hlive. split.
  - intros Q HQ. rewrite Hrest2 in HQ.
    unfold pe_gt, prhPv_gtrace in Hmaxreq.
    rewrite (pvs_model prh_jr_strtod (pe_d en) (pe_rest en) y [] Hsk), HQ in Hmaxreq.
    unfold LIVE_parse_string. unfold prh_maxreq in Hmaxreq.
    pose proof (@cf_head_nonneg cp) as Hch0.
    destruct (PjGrammar.decode y) as [[s r]|];
      cbn [PjGrammar.take fst snd map fold_right PjGrammar.esize] in Hmaxreq; clear - Hmaxreq Hch0; lia.
  - rewrite Hrest2. exact Hlive. }
(* fpre's return-address bound at the call: the jal's return slot BASE + 0x86070 *)
assert (Hra3 : raZ regs < YM05.alloc_ceiling).
{ destruct (plookup (@pl_tpi _ PL_prog_B) AF_pv_str_ret) as [e|] eqn:Hk; [|vm_compute in Hk; discriminate Hk].
  exact (pvd_ret_lt_ceil regs AF_pv_str_ret e R1 ltac:(unfold AF_pv_str_ret; lia) Hk). }
(* the wild room at the call state: pv_pre's at entry, across the C1 journal (the empty budget: no wild trace stored
   since entry, YCbqGwild.ajournal_xw_room at WS = []) *)
assert (HWRc : YCbqGwild.wild_room (as_universe B) (pe_CW en) 0 (st_depot Sc))
  by exact (YCbqGwild.ajournal_xw_room SEGS B PSTX ARx (pe_STK en + ee) (sp0 + ee) (pe_FP en) (pe_ly en) (pe_S en)
    (pe_Hp en) (pe_W en) (pe_mem en) (pe_md en) [(0, pos)] lyc Sc (pe_Hp en) W' mem mdc k [] (pe_CW en) 0%nat HJ HWR0
    (le_n 0)).
(* ---- the call: parse_string's BUDGETED text at the callee's entry, in its relation wle' segs RZ_cf (its text
   concludes YA0nH.SRr' segs RZ_cf: it frees), by YCbqGwild.aj_call_xWbR at that relation from the C1 journal lifted
   to it (YA0nH.wle_wle'), at the empty budget, window [Y, sp0 + e) ---- *)
assert (HJR : ajournal_xwR (SK := SK) SEGS B PSTX ARx (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf) (pe_STK en + ee)
    (sp0 + ee) (pe_FP en) (pe_ly en) (pe_S en) (pe_Hp en) (pe_W en) (pe_mem en) (pe_md en) [(0, pos)] lyc Sc
    (pe_Hp en) W' mem mdc k [])
  by (eapply (ajournal_xwR_mono (SK := SK) SEGS B PSTX ARx (@wle SEGS));
      [exact (YA0nH.wle_wle' SEGS YGcfRehidePost.RZ_cf) | exact HJ]).
eapply (YA0nH.SRrG_bind SEGS (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf) (YA0nH.wle'_trans SEGS YGcfRehidePost.RZ_cf)).
{ eapply (YCbqGwild.aj_call_xWbR SEGS B PSTX ARx LAWS (@pa_segs_low _ _ PA) (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf)
    (YA0nH.wle'_refl SEGS YGcfRehidePost.RZ_cf) (YA0nH.wle'_trans SEGS YGcfRehidePost.RZ_cf) W' regs mem
    (SIGMA AS_parse_string)
    (pe_STK en + ee) (sp0 + ee) (pe_FP en) (pe_ly en) (pe_S en) (pe_Hp en) (pe_W en) (pe_mem en) (pe_md en)
    [(0, pos)] lyc Sc (pe_Hp en) mdc k [] STK_parse_string (sp0 + ee - Y) [(q, q + 8)] (Y - (sp0 + ee))
    (Z_to_bv 64 (BASE + AF_pv_str_ret)) ch1 _ _ HJR).
  - rewrite HspY. clear - HYb. lia.
  - clear - HY32 Hal16 He16. lia.
  - clear - He0 HYb. lia.
  - rewrite HpsV. lia.
  - clear - HpsV HSTK HYb He0. lia.
  - clear - He0 HYb. lia.
  - clear - HY32 Hal16 He16. lia.
  - clear. lia.
  - rewrite R3. exact Hgp.
  - rewrite R4. exact Htp.
  - exact R1.
  - apply (ret_ok_codeptr_v (PI := PA)); [unfold AF_pv_str_ret; lia | reflexivity].
  - pose proof (@pa_B_ok _ B_prog_listing PA) as HBok. rewrite unsigned_lit_small; unfold AF_pv_str_ret; lia.
  - replace (sp0 + ee + (Y - (sp0 + ee))) with Y by lia. rewrite Hs0. exact Hch1.
  - intros HAFN3 HWIN3.
    assert (HRO3 : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W') mem)).
    { intros a Hr Ho Her. rewrite (J3 a (pvcs_ro_img a Hr) Ho Her (RONP a Hr)).
      - exact (HRO a Hr Ho Her).
      - apply fp_spares_closed. apply sink_closed_pos. unfold pe_FP.
        repeat (apply Forall_cons; [cbn [fst]; lia|]). apply Forall_nil. }
    assert (HFP3 : fpre B ARx STK_parse_string lyc Sc (pe_Hp en) W' regs mem mdc ch1).
    { split; [exact HAFN3|]. split; [exact HRO3|]. split; [rewrite HspY, Eshi; clear - Hhi64 HYb; lia|].
      split; [exact Hra3 | exact Hfrm0]. }
    assert (HCCH : exists ch, achain lyc (aview SEGS (w_H W') mem) (spZ regs - pi_frame F_parse_string)
      (prh_s0 F_parse_string q) ch) by (rewrite HspY, E144, Hs0q; exact (proj1 HCURS)).
    destruct HCURS as (_ & HCWOK & HCLOW).
    exact (TPSTR (pe_CTX0 en) (pe_CW en) (pe_most en) (pe_own en) lyc Sc (pe_Hp en) W' regs mem mdc ch1
      (sp0 + ee - Y) q text len p1
      (Z.of_nat (pe_d en)) (pe_tb en) (pe_Lam en) (pe_peak en) (pe_cnt en) (pe_fail en) (pe_ran en)
      HFP3 HUNIV HCCH HCLOW HCWOK ltac:(rewrite HspY; lia) (proj1 HROOMc) HWRc HPKS3 HPK243 HHULLs R10 HCUR3 Hp1end
      Hnth34
      HWIN3 ltac:(rewrite HspY; lia) ltac:(rewrite HspY; lia) HQRA3 HSRC3 HHOME HLED3 ltac:(clear - Hcntb; lia)
      HROOM3).
  - intros a Ha. left. destruct Ha as (r & Hr & Hwr). destruct Hr as [<- | []].
    exists (q, q + 8). split; [unfold pe_FP; left; reflexivity | exact Hwr]. }
cbv beta. intros W4 c4 _ (ly4 & S4 & Hp4 & regs4 & mem4 & md4 & k1 & WS1 & Ec4 & HPW & HJ4w & HJc & HXw & HP4 & HKP).
subst c4. cbv beta delta [fQmn] in HKP.
destruct HKP as ((res & R10' & Hroom4 & Hhull4 & Hbb4 & HM) & HMK4).
assert (HMN4 : YAkMemnorm.memnorm SEGS mem4) by exact (HMK4 HMNc).
(* the caller's journal after the call is BUDGETED, at the callee's WS1 (wbudget CW 0: the callee post's P), and at
   the re-hiding relation: the stretch to the exit runs on it REBASED at the post-call depot
   (YCbqGwild.ajournal_xw_rebaseR); the exit cut unbases it (ajournal_xw_unbase0R with ajxR_wild, the post-call
   depot's wild part within the entry's and WS1) *)
pose proof (ajxR_wild HJ4w) as HWILD.
assert (HJ4 : ajournal_xR (SK := SK) SEGS B PSTX ARx (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf) (pe_STK en + ee)
    (sp0 + ee) (pe_FP en) (pe_ly en)
    (set_depot (st_depot S4) (pe_S en)) (pe_Hp en) (pe_W en) (pe_mem en) (pe_md en) [(0, pos)] ly4 S4 Hp4 W4 mem4 md4
    (k + k1))
  by (eapply YCbqGwild.ajournal_xw_rebaseR; exact HJ4w).
clear HJ4w HJR.
(* what the rest reads; the entry, journal and cursor facts of the call are spent *)
clear HBODY HCHAIN HFPRE HRDP HUNIV HCURE HCWE HWR0 HWRc HHB0 HHULLs HQCH HAFN HRO Hhi64 HAR0 Hra_ok Hra4 Hgp Htp
  Hstk0 Hpres0
  Hchain HQT0 Hal16 HSTK0 Hceil0 Hslo0 Hshi0 H470 Hbot0 Htop20 Htop0 Hmuniv Hruniv1 Hruniv2 Hcur0 Hwin Hqra Hsrc Hhome
  Hmaxrun Hnode Hvwin Hdmax Hcntb He16 Hetop Hepres Hv4096 Hvrw Hvz Hvat Hvown Hvra HROOMc HCUR HSRC HHOME
  HVEQ Vp1 Vend Vdep Hqrw Hq8 Hp1r Hqt Hd32 Vp0 Hp0r Htblen0 Hly Hsecs Hwle Hio Hfrs' Hnev Hk0
  J1 J2 J3 J4 Jgone Hpres Hstk J5 HQT Hsp16 HSTK1 Hceil Hslo Hshi H47 Hbot Htop2 Htop Eslo Eshi Etop EF4
  HSTKe HpsV Hsbytes Htx4096 Htxceil Htxam Htxra Hsrcrest HCUR3 HLED3 HSRC3 Hrest1 Hp1b Hlen34 Hp1end
  Hnth34 Hch1c Hch1 HspY Hs0 HQRA3 Vdep0 Vp3 Vdep3 Hs0q E144 Rs8 Rs16 HCE8 HCE16 NFP KST Hqc HCURS HROOM3
  Hbb HEQ HGRC.
(* ---- after the call: the callee's journal and the registers it kept ---- *)
pose proof HJc as (HAR4 & Hly4 & _ & _ & _ & Hfrs4 & _ & _ & M1 & M2 & M3 & M4 & _ & _ & _ & _ & _).
rewrite app_nil_l in Hfrs4.
pose proof Hly4 as (_ & _ & _ & _ & _ & EF4c & _ & _ & Etop4 & Eslo4 & Eshi4 & _).
assert (EFc : forall c p, frame_addr ly4 c p = frame_addr lyc c p)
  by (intros; unfold frame_addr; rewrite EF4c; reflexivity).
assert (EFlc : forall c p, flag_addr ly4 c p = flag_addr lyc c p)
  by (intros; unfold flag_addr; rewrite EF4c; reflexivity).
assert (Q2 : getr regs4 2 = getr regs 2)
  by exact (pvcs_getr_lit _ _ (2%bv : bv 5) 2 eq_refl (HP4 2 ltac:(unfold acallee_saved; lia))).
assert (Q3 : getr regs4 3 = getr regs 3)
  by exact (pvcs_getr_lit _ _ (3%bv : bv 5) 3 eq_refl (HP4 3 ltac:(unfold acallee_saved; lia))).
assert (Q4 : getr regs4 4 = getr regs 4)
  by exact (pvcs_getr_lit _ _ (4%bv : bv 5) 4 eq_refl (HP4 4 ltac:(unfold acallee_saved; lia))).
assert (Q8 : getr regs4 8 = getr regs 8)
  by exact (pvcs_getr_lit _ _ (8%bv : bv 5) 8 eq_refl (HP4 8 ltac:(unfold acallee_saved; lia))).
assert (Q18 : getr regs4 18 = getr regs 18)
  by exact (pvcs_getr_lit _ _ (18%bv : bv 5) 18 eq_refl (HP4 18 ltac:(unfold acallee_saved; lia))).
assert (Q19 : getr regs4 19 = getr regs 19)
  by exact (pvcs_getr_lit _ _ (19%bv : bv 5) 19 eq_refl (HP4 19 ltac:(unfold acallee_saved; lia))).
assert (Q23 : getr regs4 23 = getr regs 23)
  by exact (pvcs_getr_lit _ _ (23%bv : bv 5) 23 eq_refl (HP4 23 ltac:(unfold acallee_saved; lia))).
assert (Q26 : getr regs4 26 = getr regs 26)
  by exact (pvcs_getr_lit _ _ (26%bv : bv 5) 26 eq_refl (HP4 26 ltac:(unfold acallee_saved; lia))).
assert (Q27 : getr regs4 27 = getr regs 27)
  by exact (pvcs_getr_lit _ _ (27%bv : bv 5) 27 eq_refl (HP4 27 ltac:(unfold acallee_saved; lia))).
(* the post's ledger, heads and blocks, by its arm *)
assert (HMS : exists Lam4 pk4 cn4 fl4 rn4,
  prh_ledger B ly4 S4 Hp4 W4 mem4 Lam4 pk4 cn4 fl4 rn4 (pe_most en) (pe_own en) /\
  ((Lam4 = pe_Lam en /\ Hp4 = pe_Hp en /\ ablocks B ly4 S4 = ablocks B lyc Sc) \/
   (exists Q, Lam4 = (res, Z.of_nat Q + 1) :: pe_Lam en /\ Hp4 = (res - cf_head) :: pe_Hp en /\
      ablocks B ly4 S4 = ablocks B lyc Sc ++ [(res - cf_head, Z.of_nat Q + 1 + cf_head)]))).
{ revert HM. destruct (PjGrammar.scan (rest_atR (pe_tb en) text (p1 + 1))) as [Q|]; intros HM.
  - destruct HM as [(_ & _ & EH & EA & _ & HL & _) | [(_ & _ & EH & EA & _ & _ & _ & _ & HL & _) |
      [(_ & _ & _ & EH & EA & HL & _) | (_ & _ & _ & s & r & _ & EH & EA & _ & _ & HL & _)]]].
    + do 5 eexists. split; [exact HL | left; split; [reflexivity | split; assumption]].
    + do 5 eexists. split; [exact HL | left; split; [reflexivity | split; assumption]].
    + do 5 eexists. split; [exact HL | left; split; [reflexivity | split; assumption]].
    + do 5 eexists. split; [exact HL | right; exists Q; split; [reflexivity | split; assumption]].
  - destruct HM as (_ & EH & EA & HL & _).
    do 5 eexists. split; [exact HL | left; split; [reflexivity | split; assumption]]. }
destruct HMS as (Lam4 & pk4 & cn4 & fl4 & rn4 & HLED4 & HMS).
assert (Hab4 : incl (ablocks B lyc Sc) (ablocks B ly4 S4)).
{ destruct HMS as [(_ & _ & EA) | (Q & _ & _ & EA)]; rewrite EA; [apply incl_refl | apply incl_appl, incl_refl]. }
assert (Hloc4 : pvcs_loc ly4 S4 v).
{ apply (pvcs_loc_tr lyc Sc); [exact Hab4 | rewrite Hfrs4; apply incl_refl | exact EFc | exact Hlocc]. }
(* the node's str field is addressable after the call *)
assert (HRA4 : range_addressable (aview SEGS (w_H W4) mem4) SHADOW_OFF (v + 16) 8).
{ destruct Hatc as [(a1 & kk1 & Hin1 & H1 & H2) | [(b & m & Hinb & Hnl & H1 & H2) | (cid & cp' & Hinf & H1 & H2)]].
  - refine (proj1 (pva_home_shadow B ARx LAWS pvh_img_vis pvh_zs_al PA_BOX ly4 S4 Hp4 W4 mem4 md4 Lam4 pk4 cn4 fl4
      rn4 (pe_most en) (pe_own en)
      (v + 16) 8 HAR4 HLED4 ltac:(lia) _)).
    left. left. exists a1, kk1. split; [|lia].
    destruct HMS as [(-> & _) | (Q & -> & _)]; [exact Hin1 | right; exact Hin1].
  - (* the block's base is no hidden head at the call (blocks are apart), nor the new block's base *)
    assert (Hnb : ~ In b (pe_Hp en)).
    { intros Hh. pose proof HLEDc as (_ & _ & HF & HP). rewrite Forall_forall in HF.
      apply (Permutation_in _ HP) in Hh. apply in_map_iff in Hh as ((a & k0) & Eh & Hak). cbn [fst] in Eh.
      destruct (HF (a, k0) Hak) as (Hkk0 & Hab & _). cbn [fst snd] in Hkk0, Hab.
      destruct (Z.eq_dec m (k0 + cf_head)) as [Em | Nm].
      + apply Hnl. replace (b + cf_head) with a by lia. replace (m - cf_head) with k0 by lia. exact Hak.
      + assert (Hne : (b, m) <> (a - cf_head, k0 + cf_head)) by (intros X; injection X as _ X2; exact (Nm X2)).
        pose proof (sep_blocks_x SEGS B ARx LAWS _ _ _ _ _ _ _ _ _ _ HAR Hinb Hab Hne) as Hd.
        pose proof (pvh_req_ge m). assert (Hkc : 0 < k0 + cf_head) by lia.
        pose proof (pvh_req_eq (k0 + cf_head) Hkc) as Er.
        unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Er in Hd. lia. }
    refine (proj1 (pva_home_shadow B ARx LAWS pvh_img_vis pvh_zs_al PA_BOX ly4 S4 Hp4 W4 mem4 md4 Lam4 pk4 cn4 fl4
      rn4 (pe_most en) (pe_own en)
      (v + 16) 8 HAR4 HLED4 ltac:(lia) _)).
    right. exists b, m. split; [apply Hab4; exact Hinb|]. split; [|lia].
    destruct HMS as [(_ & EH & _) | (Q & _ & EH & EA)]; rewrite EH; [exact Hnb|].
    intros [Eb | Hb]; [|exact (Hnb Hb)].
    assert (Hn0 : 0 <= Z.of_nat Q + 1 + cf_head) by lia.
    destruct (pvcs_newblock lyc Sc ly4 S4 Hp4 W4 mem4 md4 _ _ HAR4 EA Hn0) as (_ & Hd).
    pose proof (Hd b m Hinb) as H. pose proof (pvh_req_ge m). pose proof (req_size_pos _ Hn0) as Hr.
    unfold zdisjoint in H. cbn [fst snd] in H. lia.
  - (* a caller's fake frame: its shadow is kept by the call, and it was addressable at the dispatch *)
    intros x Hx. destruct (HVRA x ltac:(lia)) as (s & Hs & Hok). exists s. split; [|exact Hok].
    rewrite <- Hs.
    assert (Hsx : SHADOW_OFF <= shadow_of_addr SHADOW_OFF x < SHADOW_OFF + 2 ^ 44).
    { unfold shadow_of_addr. split; [pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)); lia|].
      apply Z.add_lt_mono_l. apply Z.div_lt_upper_bound; [lia|]. clear - Hvceil HAC H2 H1 Hx. lia. }
    transitivity (aview SEGS (w_H W') mem (shadow_of_addr SHADOW_OFF x)).
    + apply (M4 cid cp' _ Hinf).
      * right. destruct (alx_frames SEGS B ARx LAWS _ _ _ _ _ _ _ _ HAR Hinf) as (Hf32 & _).
        assert (Hc0 : 0 <= cid).
        { destruct (Z_lt_le_dec cid 0) as [Hn | Hn]; [exfalso | exact Hn].
          assert (HF32 : fs_frame_bytes cid <= 32).
          { unfold fs_frame_bytes. replace cid with (- (- cid)) by lia.
            rewrite Z.shiftl_opp_r, Z.shiftr_div_pow2 by lia.
            assert (H2p : 2 ^ 1 <= 2 ^ (- cid)) by (apply Z.pow_le_mono_r; lia).
            change (2 ^ 1) with 2 in H2p. apply Z.div_le_upper_bound; lia. }
          lia. }
        rewrite (fs_frame_bytes_eq cid Hc0) in H2 |- *.
        pose proof (Z.pow_pos_nonneg 2 cid ltac:(lia) Hc0).
        unfold in_zr, shadow_addr, shadow_of_addr. cbn [fst snd]. remember (2 ^ cid) as P eqn:EP. clear EP. lia.
      * intros (r & Hr & Hwr). destruct Hr as [<- | []]. cbn [fst snd] in Hwr.
        clear - Hwr Hsx Hsp_lo Hq_lo HAC. unfold SHADOW_OFF in *. lia.
    + apply AVC; [clear - Hsx; unfold SHADOW_OFF in *; lia|]. intros Hvx.
      clear - Hvx Hsx Hvam. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, SHADOW_OFF, shadow_of_addr in *. lia. }
(* ---- the stretch 0x86560 .. 0x8664c: s3 = v + 16, the ASan check of v + 16, `sd a0, 0(s3)`, s5 = (a0 != 0) - 1 ---- *)
set (E := Eimg (Ereg regs4 [])).
assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
assert (Eof : forall n : nat, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs4 []) n).
{ intros n Hn. unfold E, Eimg. cbn [ew]. replace ((A_TEXT <=? n)%nat) with false by (symmetry; apply Nat.leb_gt; lia).
  reflexivity. }
assert (HAE : env_agree 32 (Ereg regs4 []) E).
{ unfold E. split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. }
assert (E19 : ew E 19 = w64 v) by (rewrite (Eof 19%nat ltac:(cbv; lia)); exact (eq_trans Q19 R19)).
assert (E23 : ew E 23 = w64 SHADOW_OFF) by (rewrite (Eof 23%nat ltac:(cbv; lia)); exact (eq_trans Q23 R23)).
assert (U19 : bv_unsigned (ew E 19) = v) by (rewrite E19; apply unsigned_lit_small; lia).
assert (U23 : bv_unsigned (ew E 23) = SHADOW_OFF) by (rewrite E23; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (HS : st_ok_pi SEGS VAL E pvcs_ss
  (restrict (w_H W4) (@YK11.mkst fx0 regs4 (Z_to_bv 64 (BASE + AF_pv_str_ret)) mem4 (YK11.seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold pvcs_ss.
  replace (Z_to_bv 64 (BASE + AF_pv_str_ret)) with (Z_to_bv 64 (VAL A_TEXT + AF_pv_str_ret)) by reflexivity.
  apply pa_entry_st_ok_full.
  - unfold E; apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold pvcs_vreg, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U19. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
    intros o Ho. apply (apresent_writable SEGS). apply (pvcs_loc_present _ _ _ _ _ _ _ HAR4 Hloc4). lia.
  - cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
  - split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok pvcs_facts]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U19, U23. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r. repeat split; try lia. }
assert (HBx : U E PVCS_Bx = SHADOW_OFF) by (unfold PVCS_Bx; rewrite U_SOff, U23; reflexivity).
assert (SHOK : sh_ok SEGS PVCS_Bx pvcs_SH E (rdW W4 mem4)).
{ unfold pvcs_SH. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W4) mem4 E PVCS_Bx 19 (v + 16) 8 v 16 24);
    [exact HRA4 | exact HBx | exact (U_atom E 19 v E19 ltac:(lia)) | lia | lia |].
  intros x Hx. clear - Hx Hvam. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, SHADOW_OFF in *. lia. }
pose (RUNTO := paj_run_to_x_fr_invR (SK := SK) (PL := PL_prog_B) (PI := PA) B PSTX ARx LAWS (YAkMemnorm.memnorm SEGS)
  (srr_inv_laws_memnorm_k SEGS) (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf) (YA0nH.wle'_refl SEGS YGcfRehidePost.RZ_cf)
  (YA0nH.wle'_trans SEGS YGcfRehidePost.RZ_cf)).
paj_run_to_tok_x_inv RUNTO HS HJ4 SHOK HMN4 PVCS_Bspan AF_pv_exit.
{ (* the str word's 8 bytes lie in the node: a live block (awr_byte) or a caller's fake frame (wr_fp_frame) *)
  intros a (r & Hin & Hr). unfold pvcs_ss in Hin. cbn [ss_mem In] in Hin. destruct Hin as [<- | []].
  unfold pvcs_vreg in Hr. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite U19 in Hr.
  assert (HinFP : inFP (pe_FP en) a).
  { exists (v, v + 56). split; [unfold pe_FP; right; right; left; reflexivity | cbn [fst snd]; lia]. }
  destruct (pvcs_loc_of_at _ _ _ _ _ _ _ _ _ _ _ _ _ HLED0 Hat0) as
    [(b & m & Hinb & H1 & H2) | (cid & c & Hinf & H1 & H2)].
  - left. right. left. split; [exact HinFP|]. exists b, m. split; [apply Hab4; rewrite Habl; exact Hinb | lia].
  - right. split; [exact HinFP|]. exists cid, c. split; [exact Hinf|].
    unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFc, EF. lia. }
rewrite ?wvb_collapse in HJ4.
lazymatch goal with |- YA0nH.SRrG _ _ _ {| cfg_ms := ?m; cfg_model := _ |} _ => rename m into msf end.
(* the stretch wrote only the str word *)
assert (AVF : forall a, 0 <= a < 2 ^ 64 -> ~ (v + 16 <= a < v + 24) ->
  aview SEGS (w_H W4) (ms_mem msf) a = aview SEGS (w_H W4) mem4 a).
{ intros a Ha Hn. apply (pvcs_aview_of_frame W4 E (ss_mem pvcs_ss) mem4 (ms_mem msf) a HFr); [|exact Ha].
  intros (r & Hin & Hr). unfold pvcs_ss in Hin. cbn [ss_mem In] in Hin. destruct Hin as [<- | []].
  unfold pvcs_vreg in Hr. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite U19 in Hr. exact (Hn Hr). }
(* the call kept the node's bytes (a block or a frame of the call state, off q's p word) *)
assert (KN : forall a, v <= a < v + 56 -> aview SEGS (w_H W4) mem4 a = aview SEGS (w_H W') mem a).
{ intros a Ha.
  assert (HnF : ~ inFP [(q, q + 8)] a)
    by (intros (r & Hr & Hra); destruct Hr as [<- | []]; cbn [fst snd] in Hra; clear - Hqv Ha Hra; lia).
  destruct Hlocc as [(b & m & Hinb & H1 & H2) | (cid & c & Hinf & H1 & H2)].
  - replace a with (b + (a - b)) by lia.
    apply (M2 b m (a - b) Hinb (Hab4 _ Hinb)); [lia | replace (b + (a - b)) with a by lia; exact HnF].
  - apply (M4 cid c a Hinf); [left; unfold in_zr, frame_rng; cbn [fst snd]; lia | exact HnF]. }
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
  assert (HAEf : env_agree 32 (Ereg regs4 []) Ex) by (pvd_agree HAE) end.
assert (KRF : forall r, In r [2; 3; 4; 8; 18; 23; 26; 27]%bv -> getr (ms_regs msf) r = getr regs4 r)
  by (intros r Hr; exact (regs_kept_of_st_ok_pi _ _ _ regs4 []
        [2; 3; 4; 8; 18; 23; 26; 27]%bv HS HAEf ltac:(vm_compute; reflexivity) r Hr)).
pvd_reg HS (21%bv : bv 5) R21.
(* the result is 0 or the new block's user address, a 64-bit value *)
assert (Hres64 : 0 <= res < 2 ^ 64).
{ destruct HMS as [(_ & _ & EA) | (Q & _ & _ & EA)].
  - revert HM. destruct (PjGrammar.scan (rest_atR (pe_tb en) text (p1 + 1))) as [Q|]; intros HM;
      [destruct HM as [(_ & Er & _) | [(_ & Er & _) | [(_ & Er & _) | (_ & Hr4 & _ & s & r & _ & _ & EA' & _)]]] |
       destruct HM as (Er & _)]; try lia.
    rewrite EA in EA'. exfalso. assert (Hl : length (ablocks B lyc Sc) = length (ablocks B lyc Sc ++
      [(res - cf_head, Z.of_nat Q + 1 + cf_head)])) by (rewrite <- EA'; reflexivity).
    rewrite length_app in Hl. cbn [length] in Hl. lia.
  - assert (Hin' : In (res - cf_head, Z.of_nat Q + 1 + cf_head) (ablocks B ly4 S4))
      by (rewrite EA; apply in_or_app; right; left; reflexivity).
    destruct (alx_blocks SEGS B ARx LAWS _ _ _ _ _ _ _ _ HAR4 Hin') as (_ & H4k & Hc & _).
    assert (Hn0 : 0 <= Z.of_nat Q + 1 + cf_head) by (pose proof (@cf_head_nonneg cp); lia).
    pose proof (req_size_pos _ Hn0) as Hr. pose proof (@cf_head_nonneg cp). lia. }
pose proof HJ4 as (HARf & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpresf & _ & _ & _).
assert (Efb : fs_frame_bytes 0 = 64) by reflexivity.
destruct (frames_bounds_x SEGS B ARx LAWS _ _ _ _ _ _ _ _ HAR HinF) as (Hfa0 & Hfac & _).
rewrite <- Efa in Hfa0, Hfac. rewrite Efb in Hfac.
(* parse_value's fake frame lies off the node *)
assert (Hfa_v : forall a, fa <= a < fa + 64 -> ~ (v <= a < v + 56)).
{ intros a Ha Hv. destruct (pvcs_loc_of_at _ _ _ _ _ _ _ _ _ _ _ _ _ HLED0 Hat0) as
    [(b & m & Hinb & H1 & H2) | (cid & c & Hinf & H1 & H2)].
  - rewrite <- Habl in Hinb. pose proof (sep_block_frame_x SEGS B ARx LAWS _ _ _ _ _ _ _ _ _ _ HAR Hinb HinF) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite <- Efa, Efb in Hd. lia.
  - destruct (in_split _ _ Hinf) as (l2 & l3 & Hl).
    pose proof (sep_frames_pos_x SEGS B ARx LAWS lyc Sc (pe_Hp en) W' mem mdc (0, pos) (cid, c) [] l2 l3 HAR
      ltac:(rewrite Hfrs, Hl; reflexivity)) as Hd.
    unfold frame_rng, zdisjoint in Hd. cbn [fst snd] in Hd. rewrite <- Efa, EF, Efb in Hd. lia. }
assert (Hp1d : p1 = pe_text en + pe_len en - Z.of_nat (length (PjGrammar.skip (pe_rest en))))
  by (unfold p1; rewrite Hsk; reflexivity).
pmkst HS.
apply KX. unfold pv_at_exit.
exists fx0, (ms_regs msf), (ms_mem msf), Y, fa, fl, pos, ly4, S4, Hp4, (k + k1), (if res =? 0 then -1 else 0).
split; [repeat f_equal; try (vm_compute; reflexivity)|].
split; [exact Hfrm0|]. split; [intros r _; reflexivity|].
split.
{ unfold pv_keep_regs. rewrite !KRF by (cbn; tauto). rewrite Q2, Q8, Q18, Q26, Q27, Q23, Q3, Q4.
  split; [exact R2|]. split; [exact R8|]. split; [exact R18|]. split; [exact R26|]. split; [exact R27|].
  split; [exact R23|]. split; [exact R3 | exact R4]. }
assert (U10 : U E (SOff 10 0) = res)
  by (apply (U_atom E 10 res); [rewrite (Eof 10%nat ltac:(cbv; lia)); exact R10' | exact Hres64]).
split.
{ (* s5 = (a0 != 0) - 1, `snez s5, a0; addi s5, s5, -1` *)
  rewrite R21. apply bv_eq. unfold w64. rewrite Z_to_bv_unsigned.
  change (bv_unsigned (sv_denot E (SAlu ALU_ADD (SAlu ALU_SLTU (SLit 0) (SOff 10 0)) (SLit (-1)))))
    with (U E (SAlu ALU_ADD (SAlu ALU_SLTU (SLit 0) (SOff 10 0)) (SLit (-1)))).
  rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite U10, !U_SLit.
  change (zcanon 0) with 0. change (zcanon (-1)) with (2 ^ 64 - 1).
  destruct (Z.eqb_spec res 0) as [E0 | N0].
  - rewrite E0. vm_compute. reflexivity.
  - replace (0 <? res) with true by (symmetry; apply Z.ltb_lt; lia). vm_compute. reflexivity. }
split.
{ (* pv_body_x: the frame, parse_value's fake frame on top, the journal unbased from the post-call depot at the
     callee's budget WS1 (its wbudget CW 0 is the callee post's P), the window *)
  exists WS1. split; [|exact HPW].
  split; [|split; [rewrite Hfrs4; exact HinF | split; [rewrite EFc; exact Efa | split; [rewrite EFlc; exact Efl |
    split; [eapply YCbqGwild.ajournal_xw_unbase0R; [exact HJ4 | exact HWILD]|]]]]].
  - apply (pvcs_frame_tr_w (pe_regs en) sp0 Y fa fl pv_shadow_live W' W4 mem (ms_mem msf)); [| | exact HFRM].
    + intros a Ha.
      assert (Hsh : SHADOW_OFF + fa / 8 <= a < SHADOW_OFF + fa / 8 + 8 -> SHADOW_OFF <= a < SHADOW_OFF + 2 ^ 44).
      { intros H. split; [pose proof (Z.div_pos fa 8 ltac:(lia) ltac:(lia)); lia|].
        assert (fa / 8 < 2 ^ 44 - 8) by (apply Z.div_lt_upper_bound; lia). lia. }
      rewrite AVF.
      2:{ destruct Ha as [Ha | [Ha | Ha]]; [lia | lia | specialize (Hsh Ha); unfold SHADOW_OFF in *; lia]. }
      2:{ destruct Ha as [Ha | [Ha | Ha]]; [lia | pose proof (Hfa_v a Ha); lia |].
          specialize (Hsh Ha). unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, SHADOW_OFF in Hvam, Hsh. lia. }
      assert (HnF : ~ inFP [(q, q + 8)] a).
      { intros (r & Hr & Hra). destruct Hr as [<- | []]. cbn [fst snd] in Hra.
        destruct Ha as [Ha | [Ha | Ha]]; [lia | lia | specialize (Hsh Ha); unfold SHADOW_OFF in *; lia]. }
      destruct Ha as [Ha | [Ha | Ha]].
      * apply HXw; [lia | exact HnF].
      * apply (M4 0 pos a HinF); [left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite <- Efa, Efb; lia | exact HnF].
      * apply (M4 0 pos a HinF); [right; unfold in_zr, shadow_addr; cbn [fst snd]; rewrite <- Efa, Efb; cbn; lia | exact HnF].
    + intros a [Ha | Ha].
      * apply Hpresf. lia.
      * assert (HinF4 : In (0, pos) (frames S4)) by (rewrite Hfrs4; exact HinF).
        destruct (alx_frames SEGS B ARx LAWS _ _ _ _ _ _ _ _ HARf HinF4) as (_ & _ & Hfb & _).
        rewrite EFc, <- Efa, Efb in Hfb. exact (proj1 (Hfb a Ha)).
  - intros a Ha Hn. rewrite AVF by lia.
    rewrite HXw.
    + exact (HWIN a Ha Hn).
    + lia.
    + intros (r & Hr & Hra). apply Hn. exists r. destruct Hr as [<- | []].
      split; [unfold pe_FP; left; reflexivity | exact Hra]. }
(* pv_Qm: the packaging of parse_string's post (PvB_D_Str.v pvD_Qm_str) at the final memory *)
assert (HIT : forall p', pj_in_okR SEGS (rdW W4 mem4) q text len p' (Z.of_nat (pe_d en)) (pe_tb en) ->
   pj_in_okR SEGS (rdW W4 (ms_mem msf)) q text len p' (Z.of_nat (pe_d en)) (pe_tb en)).
{ intros p' H. apply (pvcs_in_keep W4 W4 mem4 (ms_mem msf) q text len p' _ _ H).
  - intros x Hx. apply AVF; [lia|]. clear - Hqv Hx. lia.
  - intros x Hx. apply AVF; [lia|]. clear - Htv Hx. lia.
  - intros x Hx. split; [lia|]. intros Hi. pose proof (@pa_segs_low _ B_prog_listing PA x Hi).
    unfold kLowMemEnd in *. lia. }
assert (HSTF : forall a, Exists (in_zr a) PSTX -> aview SEGS (w_H W4) (ms_mem msf) a = aview SEGS (w_H W4) mem4 a).
{ intros a Ha. destruct (pvcs_statics_apart _ _ _ _ _ _ _ HAR Hlocc a Ha) as [Hr Hn]. apply AVF; [exact Hr|].
  intros X. apply Hn. lia. }
assert (HHDw : forall a k0 i, In (a, k0) (pe_Lam en) -> 0 <= i < 8 ->
  aview SEGS (w_H W4) (ms_mem msf) (a - cf_head + i) = aview SEGS (w_H W4) mem4 (a - cf_head + i)).
{ intros a k0 i Hin Hi.
  destruct (pvcs_heads_apart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HAR HLEDc Hatc a k0 i Hin Hi) as [Hr Hn].
  apply AVF; [exact Hr|]. intros X. apply Hn. lia. }
assert (HLTa : forall pk cn fl0 rn, prh_ledger B ly4 S4 Hp4 W4 mem4 (pe_Lam en) pk cn fl0 rn (pe_most en) (pe_own en) ->
  prh_ledger B ly4 S4 Hp4 W4 (ms_mem msf) (pe_Lam en) pk cn fl0 rn (pe_most en) (pe_own en)).
{ intros pk cn fl0 rn H. exact (pvcs_ledger_heads _ _ _ W4 W4 mem4 (ms_mem msf) _ _ _ _ _ _ _ H HSTF HHDw). }
(* the exit cut's last conjunct: the memory normal form (the keep, then the stretch's runner twin) *)
split; [|exact HMN4].
apply (pvD_Qm_str B ARx en pos p1 res (if res =? 0 then -1 else 0) y lyc Sc W' memC ly4 S4 Hp4 W4 (ms_mem msf)
  HHD HPRE Hp1d Hsk HRD0 Hfrs4).
- (* the post's parts, at the final memory *)
  split; [exact Hroom4|]. split; [exact Hhull4|].
  fold text. rewrite Hrest2. revert HM. rewrite Hrest2. destruct (PjGrammar.scan y) as [Q|] eqn:Esc; intros HM.
  + destruct HM as [(Ecf & Er & EH & EA & _ & HL & HI & HPm & HPs) |
      [(Ecf & Er & EH & EA & _ & _ & _ & HX & HL & HI & HPm & HPs) |
      [(Ecf & Er & Ed & EH & EA & HL & HI & HPm & HPs) |
       (Ecf & Hres & H16 & s & r & Ed & EH & EA & _ & Hcb & HL & HI & HPm & HPs)]]].
    * left. exact (conj Ecf (conj Er (conj EH (conj EA (conj (HLTa _ _ _ _ HL) (conj (HIT _ HI) (conj HPm HPs))))))).
    * right; left.
      exact (conj Ecf (conj Er (conj EH (conj EA (conj HX (conj (HLTa _ _ _ _ HL) (conj (HIT _ HI)
        (conj HPm HPs)))))))).
    * right; right; left.
      exact (conj Ecf (conj Er (conj Ed (conj EH (conj EA (conj (HLTa _ _ _ _ HL)
        (conj (HIT _ HI) (conj HPm HPs)))))))).
    * right; right; right. split; [exact Ecf|]. split; [exact Hres|]. split; [exact H16|]. exists s, r.
      split; [exact Ed|]. split; [exact EH|]. split; [exact EA|].
      assert (Hn0 : 0 <= Z.of_nat Q + 1 + cf_head) by lia.
      pose proof (pvcs_node_new lyc Sc ly4 S4 Hp4 W4 mem4 md4 _ _ v HAR4 EA Hn0
        ltac:(rewrite Hfrs4; apply incl_refl) EFc Hlocc) as HNN.
      assert (Hin' : In (res - cf_head, Z.of_nat Q + 1 + cf_head) (ablocks B ly4 S4))
        by (rewrite EA; apply in_or_app; right; left; reflexivity).
      destruct (alx_blocks SEGS B ARx LAWS _ _ _ _ _ _ _ _ HAR4 Hin') as (_ & H4k & Hbc & _).
      assert (Hq0 : 0 < Z.of_nat Q + 1 + cf_head) by lia.
      rewrite (pvh_req_eq _ Hq0) in Hbc, HNN.
      destruct (PjGrammar.G1_4 y s r Ed) as (q' & Esc' & _ & Hls & _). rewrite Esc in Esc'. injection Esc' as <-.
      split.
      -- destruct Hcb as [Hcs Hcg]. split; [exact Hcs|].
         apply (pvcs_garr8_keep W4 W4 mem4 (ms_mem msf) res _ Hcg). intros x Hx.
         rewrite length_app in Hx. cbn [length] in Hx.
         apply AVF; [lia|]. intros X. apply (HNN x); lia.
      -- split; [|split; [exact (HIT _ HI) | exact (conj HPm HPs)]].
         apply (pvcs_ledger_heads _ _ _ W4 W4 mem4 (ms_mem msf) _ _ _ _ _ _ _ HL HSTF).
         intros a k0 i [Eak | Hin] Hi.
         ++ injection Eak as <- <-. apply AVF; [lia|]. intros X. apply (HNN (res - cf_head + i)); lia.
         ++ exact (HHDw a k0 i Hin Hi).
  + destruct HM as (Er & EH & EA & HL & HI & HPm & HPs).
    exact (conj Er (conj EH (conj EA (conj (HLTa _ _ _ _ HL) (conj (HIT _ HI) (conj HPm HPs)))))).
- (* the new block: 64-bit, fresh, off the node *)
  intros Q HQ Hr0. fold text in HQ. rewrite Hrest2 in HQ. revert HM. rewrite Hrest2, HQ. intros HM.
  destruct HM as [(_ & Er & _) | [(_ & Er & _) | [(_ & Er & _) | (_ & Hres & _ & s & r & _ & _ & EA & _)]]];
    [lia | lia | lia |].
  assert (Hn0 : 0 <= Z.of_nat Q + 1 + cf_head) by lia.
  pose proof (pvcs_node_new lyc Sc ly4 S4 Hp4 W4 mem4 md4 _ _ v HAR4 EA Hn0
    ltac:(rewrite Hfrs4; apply incl_refl) EFc Hlocc) as HNN.
  destruct (pvcs_newblock lyc Sc ly4 S4 Hp4 W4 mem4 md4 _ _ HAR4 EA Hn0) as (Hfresh & _).
  assert (Hq0 : 0 < Z.of_nat Q + 1 + cf_head) by lia.
  rewrite (pvh_req_eq _ Hq0) in HNN.
  split; [lia|]. split; [exact Hfresh|]. intros x Hx. apply (HNN x). lia.
- reflexivity.
- (* the type word, stored before the call, kept by the call and the stretch *)
  apply (pvcs_val_keep W' W4 mem (ms_mem msf) v 4 4 Hty). intros x Hx. cbn in Hx.
  rewrite AVF by lia. apply KN. lia.
- (* the str word, the stretch's store *)
  refine (pvcs_val8 E _ (w_H W4) msf 19 16 (SOff 10 0) res v (v + 16) HS _ U19 eq_refl U10).
  vm_compute. reflexivity.
- intros a Ha. rewrite AVF by lia. rewrite KN by lia. apply AVC; lia.
- intros a Ha. rewrite AVF by lia. rewrite KN by lia. apply AVC; lia.
- split; [exact Hv8|]. intros x Hx. apply (apresent_writable SEGS).
  apply (pvcs_loc_present _ _ _ _ _ _ _ HARf Hloc4). exact Hx.
Qed.

End c.
