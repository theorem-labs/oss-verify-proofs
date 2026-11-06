(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/ExvB_Loop_kitQ.v, with its module paths and module names changed; 583 of its 621 lines of code are new or changed and 158 lines of the source are left out. *)
(* fuzz_preset, image B' (#102 pins: asan-ubsan sha256 d663f82d7f488d30, unstripped twin c90d4fa54d43160b): SEGMENT
   CB1 Poison of the re-walk of check_no_overread (cno, entry B' 0x819f0 = slot 201 of the whole-program listing),
   0x81a94 (offset 164, the cut CNB_FRAME) -> 0x81b80 (offset 400, the cut CNB_COPY). Row R7-4 of
   the internal file FREE-PIECES-102.md (a Theorem Labs lane, the internal file PLAN-cno-caw-102.md sections 5.0 / 5.2 row "CB1 Poison").
   rule 24: no function proved. rule 24: proves no function (kind: segment lemma).
   INPUTS (by path, blobs at this file's commit; the branch's base 0e85941c7687, the
   the kit CUT a working branch 7cdbb61b5fa0, the post-implication position form):
     THE CONTRACT lib/B/Prog/Cno102B_Base.v 06098b64f859: cnb_pre (no DW at the cut), the cuts cnb_at_frame /
     cnb_at_copy (both at the spent wild budget 0, cnb_base .. k 0; both state own = 0 through cnb_pre_mid's ledger and
     the progress fact cnb_prog D [] S: CB1 makes no run event and leaves the allocator state S as it is, so the fact
     passes through unchanged), the exit cnb_ex_copy, cnb_S1_bounds, the listing tables PL_cno_B. Nothing here
     re-states the contract.
     Listing (the cut's): lib/B/Listing_prog.v c97cc46b3e13, lib/Reusable/YPsym.v b6f5a85d234d. lib/B/PAImg_prog.v
     (15fab93fe702) is NOT Required: this file is PARAMETRIC over {PA : PAImg B_prog_listing} (owner 12:48Z).
     The kit (the cut's): lib/A/PRH_Base.v ef7c8ca98529 (prh_ledger `.. ran most own` with prh_most / prh_own as fields of
     prh_glob, its named projections, src_rd, kept_at), lib/A/PRH_FnReader.v f1ae32e3b2cd (prhReader_home),
     lib/A/PRH_FnCheck.v c40cf3fdcd2a (STK_check_no_overread), lib/B/PRH_ImgB.v 3216eca68342 (the B' cells).
     Engine (the cut's P'' set): YC80x.v 14f84f225e8f (srr_inv_laws), YC1fPx.v 7814b594066f (paj_run_to_x_inv over
     ajournal_x), YC1fP.v 96e2e49ece5f, YCbqG.v 219748197d6b (ajournal_xw read through its ajx_* projections, AR_laws_x),
     YCbqGwild.v 0c63874858e4 (wbudget, ajournal_xw_rebase / ajournal_xw_unbase0), YCbq.v dedbf56c64d5, YGcallcf.v
     8645fa6a514f (AR_laws_x_xs), YG0lawscf.v 17c91dd453e4 (AR_laws_ok_cf); lib/Reusable/YImgTop.v d2a97d3111ce
     (IMG_TOP_B = 0x601000); lib/A/CfParamsPreset.v b60d0f63c926 (the one CfParams instance, cf_head = 16, as
     CnoB102f's Cno102B_F.v).
   AT THE CUT: THE WILD BUDGET. CB1 is call-free and stores no allocator trace, so the cut's budgeted journal
   (cnb_J D wk) is REBASED to the empty budget (YCbqGwild.ajournal_xw_rebase: the entry with its depot moved to the
   cut's), the two stretches run on it as before, and the exit's journal is UNBASED at the same WS
   (YCbqGwild.ajournal_xw_unbase0 with the cut's ajx_wild): the spent budget wk and its wbudget [] wk WS pass through,
   0 at both cuts (the pattern of CB9's Cno102B_E9.v 3e20ff19944e). The journal is read through YCbqG's ajx_*
   projections, the cut cnb_at_frame and its cnb_base by the TYPE of each conjunct (cnb1_pick), never by position.
   THE CODE (Listing_prog.v slots 242-300, offset = 4 * (slot - 201); checked by cnb1_slots below):
     164 sd s3, 48(s1) (F at s1 + 48) ; 168 / 172 / 176 s6 / s5 / s4 = s3 + 32 / 128 / 224 (d1 / d2 / d3) ;
     180 lui a0, 0x41b59 ; 184 / 188 auipc a1 / a2 (PHi 7 / 8) ; 192 srli a3, s3, 3 ; 196 add s2, a3, s2 (s2 = F's
     shadow) ; 200 li s10, -8 ; 204 addiw a0, a0, -1357 (a0 = 0x41b58ab3, the frame magic) ; 208 a1 = the frame
     description string (A_OBJ 2 + 0x886b, .rodata 0x1886b) ; 212 a2 = cno's own pc (A_TEXT + 0x324) ;
     216 / 220 / 224 sd a0 / a1 / a2, 0 / 8 / 16(s3) (F's header) ; 228-396 forty `sb` of 0xf1 / 0xf2 / 0xf3 / s10 = 0xf8
     at s2 + 0 .. s2 + 39 (the frame's shadow poison) ; 400 = CNB_COPY (`li a2, 0x31`).
   THE PROOF: two symbolic stretches through the engine's memory-invariant runner paj_run_to_x_inv at ARx := ARcf /\
   xs_placed_cf (CnoB102f's ARcfx), P generic (srr_inv_laws only: the segment is call-free). Stretch 1 (164 -> 216)
   writes [s1 + 48, s1 + 56) (the real stack, the journal's first write case); stretch 2 (216 -> 400) writes
   [F, F + 24) and [shadow F, shadow F + 40) (the function's own class-3 frame and its shadow, the journal's own-frame
   case). Every fact of cnb_at_copy is either a register the run computes, the journal the runner keeps, or a fact of
   cnb_at_frame carried across the two write windows: the PST statics, the harness blocks' heads, the input bytes and
   their shadow, the saved words, the flag word, the read-only bytes are all off the windows (cnb1_safe_off,
   cnb1_pst_off below).
   THE B' RANGE FACT: ONE step needs it - the frame-header stores at [F, F + 24) do not touch the program statics
   (prh_pst). It is isolated in cnb1_pst_below_frame, whose statement names the fact it needs, cnb1_img_top: some
   segment of the image reaches IMG_TOP_B. Given it, the lemma is proved at IMG_TOP_B's value of record 0x601000
   (YImgTop.v d2a97d3111ce; every prh_pst cell of B' is below 0x5dde08). The segment lemma takes cnb1_img_top as its
   one named argument; it closes by computation at the B' instance with the witness PAImg_prog.v 15fab93fe702's
   B_prog_cover uses (AsanUbsan_segment_003). Owner: the B' instantiation (the top).
   Abort edges / UBSan traps / ASan report sites: none in 0x81a94 - 0x81b80 (no branch, no call, no check).
   Numerals: offsets above (DERIVED); 48 / 56 / 24 / 40 / 104 / 504 / 512 / 160 / 192 / 32 / 128 / 224 (LENGTH: slot,
   window, frame and struct offsets); 3 (the frame class); register numbers (WORD); 4096 and 2 ^ 47 (LENGTH: the
   runner's atom-range facts); 0x5dde08 (the end of B''s prh_pst cells, computed from PRH_ImgB.v); 0 (COUNT: the spent
   wild budget at both cuts). No ADDRESS. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
(* YK06 is NOT imported: its plain alloc_ceiling would shadow the RunCeil field YM05.alloc_ceiling (Cno102B_Base.v) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG YGcfNames.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC80x YC1fPx YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcallcf YG0lawscf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YImgTop YAkMemnorm YI08 YO0c YCbqGwild.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PresetRoomPos PresetRodata.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnAlloc
  PRH_FnReader PRH_FnPj PRH_FnEx PRH_FnCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import Cno102B_Base.
(* the PLAIN build's sink instance is loaded transitively; it must never fill an ASan sink argument *)
#[global] Remove Hints OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YI5b.src0_sink_head : typeclass_instances.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.
(* this file's address arithmetic reads `F / 8` (F's shadow) and `x mod 32`; lia failed on those goals at this Require
   closure until zify's euclidean-division flag was on, so the file turns it on for itself only *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* a conjunct of a conjunction chain BY ITS TYPE (CB9's cnb9_pick, Cno102B_E9.v 3e20ff19944e): the cut cnb_at_frame and
   its cnb_base are read by the statement of each conjunct, never by position *)
Local Ltac cnb1_pick H :=
  lazymatch type of H with
  | _ /\ _ => first [ exact (proj1 H) | let H' := fresh "Hpk" in pose proof (proj2 H) as H'; cnb1_pick H' ]
  | _ => exact H
  end.

(* ---- the inner cut of this segment: DERIVED byte offset inside check_no_overread ---- *)
Definition CNB_HDR : Z := 216.

(* THE SLOT CHECK on the listing of record: the segment's first word (`sd s3, 0x30(s1)`), the own-pc PAddHi, the
   first header store (`sd a0, 0(s3)`), the last poison store (`sb a0, 0x23(s2)`) and CB2's first word
   (`li a2, 0x31`). This pins CNB_FRAME, CNB_HDR and CNB_COPY. *)
Lemma cnb1_slots :
  map (fun k => nth_error B_prog_listing (CNB_SLOT + k)) [41; 53; 54; 99; 100]%nat =
  [Some (PW 0x334b823); Some (PAddHi (12%bv : bv 5) (12%bv : bv 5) 8 A_TEXT 0x324); Some (PW 0xa9b023);
   Some (PW 0x2a901a3); Some (PW 0x3100613)].
Proof. vm_compute. reflexivity. Qed.

Lemma cnb1_fsb : fs_frame_bytes CNB_CID = 512.
Proof. vm_compute. reflexivity. Qed.

(* ---- a memory change that keeps every byte off a write set Wr ---- *)
Definition cnb1_kept (H : word -> bool) (m m' : word -> option byte) (Wr : Z -> Prop) : Prop :=
  forall x : word, ~ Wr (bv_unsigned x) -> mrestrict H m' x = mrestrict H m x.

Lemma cnb1_kept_mbyte : forall segs H m m' Wr a, cnb1_kept H m m' Wr -> 0 <= a < 2 ^ 64 -> ~ Wr a ->
  mbyte segs (mrestrict H m') a = mbyte segs (mrestrict H m) a.
Proof.
intros segs H m m' Wr a HK Ha Hw. unfold mbyte. rewrite HK; [reflexivity|].
rewrite unsigned_lit_small by exact Ha. exact Hw.
Qed.
Lemma cnb1_kept_aview : forall segs H m m' Wr a, cnb1_kept H m m' Wr -> 0 <= a < 2 ^ 64 -> ~ Wr a ->
  aview segs H m' a = aview segs H m a.
Proof.
intros segs H m m' Wr a HK Ha Hw. unfold aview. rewrite (cnb1_kept_mbyte segs H m m' Wr a HK Ha Hw). reflexivity.
Qed.
Lemma cnb1_kept_val_mem : forall segs H m m' Wr a n v, cnb1_kept H m m' Wr ->
  (forall k, (k < n)%nat -> 0 <= a + Z.of_nat k < 2 ^ 64 /\ ~ Wr (a + Z.of_nat k)) ->
  val_mem segs (mrestrict H m) a n v -> val_mem segs (mrestrict H m') a n v.
Proof.
intros segs H m m' Wr a n v HK Hr Hv k Hk. destruct (Hr k Hk) as [Ha Hw].
rewrite (cnb1_kept_mbyte segs H m m' Wr _ HK Ha Hw). exact (Hv k Hk).
Qed.
Lemma cnb1_kept_rdword : forall segs H m m' Wr a v, cnb1_kept H m m' Wr ->
  (forall x, a <= x < a + 8 -> 0 <= x < 2 ^ 64 /\ ~ Wr x) ->
  rdword (aview segs H m) a = Some v -> rdword (aview segs H m') a = Some v.
Proof.
intros segs H m m' Wr a v HK Hr Hw.
assert (E : forall x, a <= x < a + 8 -> aview segs H m' x = aview segs H m x).
{ intros x Hx. destruct (Hr x Hx) as [Ha Hn]. exact (cnb1_kept_aview segs H m m' Wr x HK Ha Hn). }
unfold rdword in *.
rewrite (E a), (E (a + 1)), (E (a + 2)), (E (a + 3)), (E (a + 4)), (E (a + 5)), (E (a + 6)), (E (a + 7)) by lia.
exact Hw.
Qed.
(* the runner's memory only grows *)
Lemma cnb1_grows_apresent : forall H (m m' : word -> option byte) a,
  mem_grows (mrestrict H m) (mrestrict H m') -> apresent H m a -> apresent H m' a.
Proof.
intros H m m' a G [Hh [b Hb]]. split; [exact Hh|].
specialize (G (Z_to_bv 64 a)). unfold mrestrict in G. rewrite Hh, Hb in G. cbv iota in G.
destruct (m' (Z_to_bv 64 a)) as [b'|]; [exists b'; reflexivity|].
exfalso. apply G; [discriminate | reflexivity].
Qed.
Lemma cnb1_grows_aview : forall segs H (m m' : word -> option byte) a,
  mem_grows (mrestrict H m) (mrestrict H m') -> aview segs H m a <> None -> aview segs H m' a <> None.
Proof.
intros segs H m m' a G Hn. unfold aview, mbyte in *.
destruct (mrestrict H m (Z_to_bv 64 a)) as [b|] eqn:E1.
- pose proof (G (Z_to_bv 64 a) ltac:(rewrite E1; discriminate)) as G1.
  destruct (mrestrict H m' (Z_to_bv 64 a)) as [b'|]; [cbn [option_map]; discriminate | contradiction].
- destruct (mrestrict H m' (Z_to_bv 64 a)) as [b'|]; [cbn [option_map]; discriminate | exact Hn].
Qed.
Lemma cnb1_grows_trans : forall (m1 m2 m3 : word -> option byte), mem_grows m1 m2 -> mem_grows m2 m3 -> mem_grows m1 m3.
Proof. intros m1 m2 m3 G1 G2 x Hx. exact (G2 x (G1 x Hx)). Qed.
(* an 8-byte value read as a little-endian word read (YCem.v:101 rdword_of_val_mem, body for body; YCem is not
   Required: it imports image A's tfib facts) *)
Lemma cnb1_rdword_of_val_mem : forall segs H mem a v,
  val_mem segs (mrestrict H mem) a 8 v -> 0 <= v < 2 ^ 64 -> rdword (aview segs H mem) a = Some v.
Proof.
intros segs H mem a v Hv Hr.
assert (B : forall k, (k < 8)%nat -> aview segs H mem (a + Z.of_nat k) = Some (le_byte v 8 k)).
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
(* `srli a3, s3, 3` on a 64-bit value *)
Lemma cnb1_srl3 : forall a, 0 <= a < 2 ^ 64 -> alu64 ALU_SRL (Z_to_bv 64 a) (Z_to_bv 64 3) = Z_to_bv 64 (a / 8).
Proof.
intros a Ha. apply bv_eq. rewrite YO0c.alu64_srl, !Z_to_bv_unsigned.
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite (Z.mod_small a) by lia. change ((3 mod 2 ^ 64) mod 64) with 3.
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
rewrite Z.mod_small; [reflexivity|]. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.

Section run.
Context {fz : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg}.
#[local] Existing Instance CfParams_preset.
#[local] Existing Instance prh_img_B.
Context {PA : PAImg B_prog_listing}.
#[local] Existing Instance PL_cno_B.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation VAL := (@pa_val _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
Variable B : asyms.
Variable SK : YI16.sink_head.
(* the walk's allocator relation, the cf instance (CnoB102f's ARcfx, Cno102B_F.v) and its laws *)
#[local] Abbreviation ARcfx := (fun ly S Hp W mem md => ARcf SEGS B ly S Hp W mem md /\ xs_placed_cf ly S).
#[local] Notation LAWS := (AR_laws_x_xs SEGS B (AR_laws_ok_cf SEGS B)).

(* the two stretches' symbolic memories: the real-stack slot s1 + 48, F's 24 header bytes, F's 40 shadow bytes; the
   atom-range facts the runner's static check reads (every window lies above page 0) *)
Definition cnb1_R1 : YP09.region := YP09.mkRegion (Some 9%nat) 48 56 48 56 [].
Definition cnb1_RF : YP09.region := YP09.mkRegion (Some 19%nat) 0 24 0 24 [].
Definition cnb1_RS : YP09.region := YP09.mkRegion (Some 18%nat) 0 40 0 40 [].
Definition cnb1_G1 : facts := mkFacts [(9%nat, mkAF 4096 (2 ^ 47) 5)] [] [].
Definition cnb1_G2 : facts := mkFacts [(19%nat, mkAF 4096 (2 ^ 47) 5); (18%nat, mkAF 4096 (2 ^ 47) 2)] [] [].

Lemma cnb1_entry : forall pc rgs G (W : world SEGS) regs mem,
  regions_wf rgs = true ->
  Forall (region_ok SEGS (Eimg (Ereg regs [])) (mrestrict (w_H W) mem)) rgs ->
  pairwise_disjoint (Eimg (Ereg regs [])) rgs ->
  facts_ok (Eimg (Ereg regs [])) G ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs [])) (mkSS pc sr_atoms rgs None G)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (YK11.seg_rom SEGS))).
Proof.
intros pc rgs G W regs mem Hwf Hok Hdisj HG.
rewrite restrict_mkst_fx. apply pa_entry_st_ok_full; [apply regs_ok_Eimg_Ereg | exact Hwf | exact Hok | exact Hdisj | exact HG].
Qed.
Lemma cnb1_ew : forall regs n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> (n < 32)%nat ->
  ew (Eimg (Ereg regs [])) n = getr regs rr.
Proof. intros regs n rr Hn H32. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat regs [] n rr Hn). Qed.
Lemma cnb1_reg_val : forall (H : word -> bool) E ss ms (rd : bv 5) e v,
  st_ok_pi SEGS VAL E ss (restrict H ms) -> sr_get (ss_regs ss) rd = e -> sv_denot E e = v ->
  getr (ms_regs ms) rd = v.
Proof. intros H E ss ms rd e v HS He Hv. rewrite (st_ok_pi_restrict_reg H E ss ms rd HS), He. exact Hv. Qed.
Lemma cnb1_agree : forall regs, env_agree 32 (Ereg regs []) (Eimg (Ereg regs [])).
Proof. intros regs. split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. Qed.

(* ---- the numbers the segment reads off the journal at the cut (by name: ajx_ar, ajx_ly, ajx_stk): F (frame law,
   layout law), s1 (the contract's cnb_S1_bounds), the entry sp's stack window (astk_ok), the stack budget STK ---- *)
Lemma cnb1_nums : forall D wk ly S Hp W mem md k,
  cnb_J (SK := SK) B ARcfx D wk ly S Hp W mem md k -> In (CNB_CID, bi_fpos D) (frames S) ->
  frame_addr ly CNB_CID (bi_fpos D) = cnb_F D /\ cnb_F D mod 32 = 0 /\
  4096 <= cnb_F D /\ cnb_F D + 512 <= YM05.alloc_ceiling /\
  (cnb_F D + 512 <= kLowShadowBeg \/ kHighMemBeg <= cnb_F D) /\
  cnb_S1 D mod 32 = 0 /\ cnb_sp0 D - 192 < cnb_S1 D <= cnb_sp0 D - 160 /\
  YM05.alloc_ceiling + STK_check_no_overread <= cnb_sp0 D <= 2 ^ 47 /\
  192 <= STK_check_no_overread /\ 0x7fff7f800000 <= YM05.alloc_ceiling <= 0x7fffff800000.
Proof.
intros D wk ly S Hp W mem md k (WS & HJ & _) Hin.
pose proof (ajx_ar HJ) as HAR. pose proof (ajx_ly HJ) as Hlyle. pose proof (ajx_stk HJ) as HSTK.
assert (EF : frame_addr ly CNB_CID (bi_fpos D) = cnb_F D).
{ unfold cnb_F, frame_addr. destruct Hlyle as (_ & _ & _ & _ & _ & EFl & _). rewrite EFl. reflexivity. }
pose proof (alx_frames SEGS B ARcfx LAWS ly S Hp W mem md CNB_CID (bi_fpos D) HAR Hin) as (Hal32 & Happ & _ & _).
pose proof (frames_bounds_x SEGS B ARcfx LAWS ly S Hp W mem md CNB_CID (bi_fpos D) HAR Hin) as (H4096 & Hceil & _).
rewrite EF in Hal32, Happ, H4096, Hceil. rewrite cnb1_fsb in Happ, Hceil.
pose proof HSTK as (Hsp16 & HSTK0 & Hceil0 & Hlo & Hhi & H47 & _).
pose proof (cnb_S1_bounds D Hsp16) as (S1a & S1b & S1c).
pose proof YCbq.asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSTKv : 192 <= STK_check_no_overread) by (vm_compute; discriminate).
destruct Happ as (_ & Hband). unfold ASAN_CEIL in Hband.
split; [exact EF|]. split; [exact Hal32|]. split; [lia|]. split; [lia|].
split; [destruct Hband as [Hb | (Hb & _)]; [left | right]; lia|].
split; [exact S1c|]. split; [lia|]. split; [lia|]. split; [exact HSTKv|]. lia.
Qed.

(* ---- THE B' RANGE FACT, isolated (the internal file brief-r74.md "Blocker you may hit: IMG_TOP_B"): the image reaches IMG_TOP_B ---- *)
Definition cnb1_img_top : Prop :=
  exists sg, In sg SEGS /\ YImgTop.IMG_TOP_B <= Z.of_N (seg_base sg) + Z.of_N (seg_size sg).
(* B''s program statics (PRH_ImgB.v 3216eca68342: g_live 0x5ddda0, g_peak 0x5dddc0, g_count 0x5ddde0, g_fail_at
   0xa6e00, g_ran_out 0x5dde00, g_most 0xa6e20, g_own_ran_out 0x5ddd80) *)
Lemma cnb1_pst_range : forall a, Exists (in_zr a) prh_pst -> 4096 <= a < 0x5dde08.
Proof.
intros a Ha. apply Exists_exists in Ha as ((p & w) & Hin & Hr).
assert (Hpw : In (p, w) [(0x5ddda0, 8); (0x5dddc0, 8); (0x5ddde0, 8); (0xa6e00, 8); (0x5dde00, 1); (0xa6e20, 8);
  (0x5ddd80, 1)]) by exact Hin.
unfold in_zr in Hr. cbn [fst snd] in Hr.
cbn [In] in Hpw. repeat (destruct Hpw as [E|Hpw]; [injection E; intros; subst; lia|]). destruct Hpw.
Qed.
(* THE ONE STEP THAT NEEDS IT: a static lies below every live fake frame. ly_img covers the image's segments and a
   live fake frame lies at or above ly_img's end (AR_laws_x field 17, alx_img); the fact puts that end at or above
   IMG_TOP_B, and every static is below IMG_TOP_B at its value of record 0x601000 (YImgTop.v d2a97d3111ce) *)
Lemma cnb1_pst_below_frame : cnb1_img_top ->
  forall ly S Hp W mem md cid pos a, ARcfx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  Exists (in_zr a) prh_pst -> a < frame_addr ly cid pos.
Proof.
intros (sg & Hsg & Htop) ly S Hp W mem md cid pos a HAR Hin Hpst.
destruct (alx_img SEGS B ARcfx LAWS ly S Hp W mem md HAR) as [Hseg Hfr].
destruct (Hseg sg Hsg) as [_ Hend]. pose proof (Hfr cid pos Hin) as Hf.
pose proof (cnb1_pst_range a Hpst) as Ha. rewrite YImgTop.IMG_TOP_B_val in Htop. lia.
Qed.

(* ---- the write set of the segment and the registers it leaves ---- *)
Definition cnb1_wr (D : cnb_in) (a : Z) : Prop :=
  (cnb_S1 D + 48 <= a < cnb_S1 D + 56) \/ (cnb_F D <= a < cnb_F D + 24) \/
  (shadow_addr (cnb_F D) <= a < shadow_addr (cnb_F D) + 40).
Definition cnb1_regs (D : cnb_in) (regs regs' : bvmap 5 word) : Prop :=
  (forall r : bv 5, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 19%bv; 23%bv; 24%bv; 27%bv] -> getr regs' r = getr regs r) /\
  getr regs' 18%bv = w64 (shadow_addr (cnb_F D)) /\ getr regs' 20%bv = w64 (cnb_d3 D) /\
  getr regs' 21%bv = w64 (cnb_d2 D) /\ getr regs' 22%bv = w64 (cnb_d1 D) /\ getr regs' 26%bv = w64 (-8).

(* ---- THE RUN: 164 -> 216 -> 400, at any spent wild budget wk (the cuts pass 0): the budgeted journal is rebased to
   the empty budget for the two call-free stretches and unbased at the same WS after them ---- *)
Lemma cnb1_run : forall P, srr_inv_laws SEGS P ->
  forall D wk ly S Hp W regs mem md k,
  cnb_J (SK := SK) B ARcfx D wk ly S Hp W mem md k ->
  In (CNB_CID, bi_fpos D) (frames S) ->
  getr regs 9%bv = w64 (cnb_S1 D) -> getr regs 18%bv = w64 SHADOW_OFF -> getr regs 19%bv = w64 (cnb_F D) ->
  P mem ->
  SRr SEGS W (mkCfg (mkst regs (w64 (cnb_pc CNB_FRAME)) mem (YK11.seg_rom SEGS)) md)
    (fun W' c' => W' = W /\ exists regs' mem' md',
       c' = mkCfg (mkst regs' (w64 (cnb_pc CNB_COPY)) mem' (YK11.seg_rom SEGS)) md' /\
       cnb_J (SK := SK) B ARcfx D wk ly S Hp W mem' md' k /\
       cnb1_kept (w_H W) mem mem' (cnb1_wr D) /\ mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') /\
       rdword (aview SEGS (w_H W) mem') (cnb_S1 D + 48) = Some (cnb_F D) /\
       cnb1_regs D regs regs' /\ P mem').
Proof.
intros P PLAW D wk ly S Hp W regs mem md k HJw Hin R9 R18 R19 HPM.
destruct (cnb1_nums D wk ly S Hp W mem md k HJw Hin) as (EF & F32 & F4k & Fc & Fapp & S32 & S1b & Sp & STKv & Ceil).
(* the budgeted journal (cnb_J D wk) by name: its stack window present (ajx_pres), its wild part kept for the unbase at
   the exit (ajx_wild), and the journal at the empty budget from the entry with its depot moved to the cut's (the
   runner's journal, YCbqGwild.ajournal_xw_rebase) *)
destruct HJw as (WS & HJW & HBUD).
pose proof (ajx_pres HJW) as HPRES. pose proof (ajx_wild HJW) as HWILD.
pose proof (YCbqGwild.ajournal_xw_rebase SEGS B prh_pst ARcfx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJW) as HJ.
clear HJW.
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs []))) by apply Eimg_env.
assert (U9 : bv_unsigned (ew (Eimg (Ereg regs [])) 9) = cnb_S1 D).
{ rewrite (cnb1_ew regs 9 9%bv eq_refl ltac:(lia)), R9. unfold w64. apply unsigned_lit_small. lia. }
assert (D19 : sv_denot (Eimg (Ereg regs [])) (SOff 19 0) = Z_to_bv 64 (cnb_F D)).
{ cbn [sv_denot]. rewrite (cnb1_ew regs 19 19%bv eq_refl ltac:(lia)), R19. unfold w64.
  rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity. }
(* ---- STRETCH 1: 164 -> 216 (`sd s3, 48(s1)`, the struct pointers, s2 = F's shadow, a0 / a1 / a2, s10) ---- *)
assert (HS : st_ok_pi SEGS VAL (Eimg (Ereg regs [])) (mkSS (CNB_OFF + CNB_FRAME) sr_atoms [cnb1_R1] None cnb1_G1)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + (CNB_OFF + CNB_FRAME))) mem (YK11.seg_rom SEGS)))).
{ apply cnb1_entry.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold region_ok, cnb1_R1.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
    split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
    intros o Ho. apply (apresent_writable SEGS). apply HPRES. lia.
  - cbn. tauto.
  - unfold facts_ok, cnb1_G1. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U9. change (2 ^ 5) with 32.
    repeat split; try exact I; try apply Forall_nil; lia. }
assert (SHOK : sh_ok SEGS (SLit SHADOW_OFF) [] (Eimg (Ereg regs [])) (mrestrict (w_H W) mem)) by apply Forall_nil.
assert (Epc1 : w64 (cnb_pc CNB_FRAME) = Z_to_bv 64 (BASE + (CNB_OFF + CNB_FRAME))) by (unfold cnb_pc, w64; f_equal; lia).
rewrite Epc1.
pose (RUNTO := @paj_run_to_x_inv fz rc SK B_prog_listing PL_cno_B PA B prh_pst ARcfx cf_head LAWS P PLAW).
paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM (0, 0) (CNB_OFF + CNB_HDR).
{ intros a (r & Hr & Ha). cbn [ss_mem In] in Hr. destruct Hr as [<-|[]].
  cbn [cnb1_R1 YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U9 in Ha.
  left. lia. }
rename ms into ms1. rename HS into HS1. rename HJ into HJ1. rename HPM into HPM1.
rename HF into HF1. rename HFr into HFr1. rename HG into HG1.
pmkst HS1.
pose proof (regs_kept_of_st_ok_pi _ _ _ regs [] [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 19%bv; 23%bv; 24%bv; 27%bv] HS1
  (cnb1_agree regs) ltac:(vm_compute; reflexivity)) as K1.
cbn [ms_regs restrict] in K1.
assert (Q18 : getr (ms_regs ms1) 18%bv = w64 (shadow_addr (cnb_F D))).
{ apply (cnb1_reg_val _ _ _ _ 18%bv (SAlu ALU_ADD (SAlu ALU_SRL (SOff 19 0) (SLit 3)) (SOff 18 0)) _ HS1);
    [vm_compute; reflexivity|].
  cbn [sv_denot]. rewrite (cnb1_ew regs 19 19%bv eq_refl ltac:(lia)), (cnb1_ew regs 18 18%bv eq_refl ltac:(lia)), R19, R18.
  unfold w64. rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia). rewrite !Z.add_0_r.
  rewrite cnb1_srl3 by lia. rewrite YI08.alu64_add_lit. unfold shadow_addr. f_equal. lia. }
assert (Q20 : getr (ms_regs ms1) 20%bv = w64 (cnb_d3 D)).
{ apply (cnb1_reg_val _ _ _ _ 20%bv (SOff 19 224) _ HS1); [vm_compute; reflexivity|].
  cbn [sv_denot]. rewrite (cnb1_ew regs 19 19%bv eq_refl ltac:(lia)), R19. unfold w64, cnb_d3.
  rewrite unsigned_lit_small by lia. reflexivity. }
assert (Q21 : getr (ms_regs ms1) 21%bv = w64 (cnb_d2 D)).
{ apply (cnb1_reg_val _ _ _ _ 21%bv (SOff 19 128) _ HS1); [vm_compute; reflexivity|].
  cbn [sv_denot]. rewrite (cnb1_ew regs 19 19%bv eq_refl ltac:(lia)), R19. unfold w64, cnb_d2.
  rewrite unsigned_lit_small by lia. reflexivity. }
assert (Q22 : getr (ms_regs ms1) 22%bv = w64 (cnb_d1 D)).
{ apply (cnb1_reg_val _ _ _ _ 22%bv (SOff 19 32) _ HS1); [vm_compute; reflexivity|].
  cbn [sv_denot]. rewrite (cnb1_ew regs 19 19%bv eq_refl ltac:(lia)), R19. unfold w64, cnb_d1.
  rewrite unsigned_lit_small by lia. reflexivity. }
assert (Q26 : getr (ms_regs ms1) 26%bv = w64 (-8)).
{ apply (cnb1_reg_val _ _ _ _ 26%bv (SLit 18446744073709551608) _ HS1); [vm_compute; reflexivity|].
  cbn [sv_denot]. unfold w64. apply bv_eq. rewrite !Z_to_bv_unsigned. vm_compute. reflexivity. }
(* F at s1 + 48: the stretch's own chunk *)
assert (W48 : rdword (aview SEGS (w_H W) (ms_mem ms1)) (cnb_S1 D + 48) = Some (cnb_F D)).
{ pose proof (st_ok_mem_ok SEGS _ _ _ HS1) as (_ & HMO & _).
  cbn [ss_mem abs_ss setpc ms_mem restrict] in HMO.
  apply Forall_inv in HMO. destruct HMO as (_ & _ & _ & HCH).
  cbn [YP09.r_chunks YP09.r_base base_val] in HCH. apply Forall_inv in HCH. rewrite U9 in HCH.
  pose proof (val_of_chunk_ok SEGS _ _ _ 48 8 (SOff 19 0) (cnb_F D) HCH D19
    ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(change (Z.of_N 8) with 8; lia)) as HV.
  change (N.to_nat 8) with 8%nat in HV.
  exact (cnb1_rdword_of_val_mem SEGS (w_H W) (ms_mem ms1) _ _ HV ltac:(lia)). }
(* ---- STRETCH 2: 216 -> 400 (F's header, the 40 shadow poison bytes) ---- *)
pose proof (ajx_ar HJ1) as HAR1.
pose proof (alx_frames SEGS B ARcfx LAWS ly S Hp W (ms_mem ms1) _ CNB_CID (bi_fpos D) HAR1 Hin) as (_ & _ & PF & PSH).
rewrite EF, cnb1_fsb in PF, PSH.
assert (U19 : bv_unsigned (ew (Eimg (Ereg (ms_regs ms1) [])) 19) = cnb_F D).
{ rewrite (cnb1_ew (ms_regs ms1) 19 19%bv eq_refl ltac:(lia)), (K1 19%bv ltac:(cbn; tauto)), R19.
  unfold w64. apply unsigned_lit_small. lia. }
assert (U18 : bv_unsigned (ew (Eimg (Ereg (ms_regs ms1) [])) 18) = shadow_addr (cnb_F D)).
{ rewrite (cnb1_ew (ms_regs ms1) 18 18%bv eq_refl ltac:(lia)), Q18.
  unfold w64. apply unsigned_lit_small. unfold shadow_addr, SHADOW_OFF. lia. }
assert (HS2 : st_ok_pi SEGS VAL (Eimg (Ereg (ms_regs ms1) [])) (mkSS (CNB_OFF + CNB_HDR) sr_atoms [cnb1_RF; cnb1_RS] None cnb1_G2)
  (restrict (w_H W) (mkst (ms_regs ms1) (Z_to_bv 64 (BASE + (CNB_OFF + CNB_HDR))) (ms_mem ms1) (YK11.seg_rom SEGS)))).
{ apply cnb1_entry.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold region_ok, cnb1_RF, cnb1_RS;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]; rewrite ?U19, ?U18.
    + split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. apply (apresent_writable SEGS). exact (proj1 (PF (cnb_F D + o) ltac:(lia))).
    + split; [unfold shadow_addr, SHADOW_OFF; lia|]. split; [unfold shadow_addr, SHADOW_OFF; lia|].
      split; [|apply Forall_nil].
      intros o Ho. apply (apresent_writable SEGS). exact (proj1 (PSH o ltac:(lia))).
  - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
    cbn [cnb1_RF cnb1_RS YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U19, U18.
    unfold shadow_addr, SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *.
    split; [split; [lia | exact I] | split; exact I].
  - unfold facts_ok, cnb1_G2. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U19, U18. change (2 ^ 5) with 32. change (2 ^ 2) with 4.
    unfold shadow_addr, SHADOW_OFF. repeat split; try exact I; try apply Forall_nil; lia. }
assert (SHOK2 : sh_ok SEGS (SLit SHADOW_OFF) [] (Eimg (Ereg (ms_regs ms1) [])) (mrestrict (w_H W) (ms_mem ms1)))
  by apply Forall_nil.
assert (HEI2 : img_env VAL A_LIM (Eimg (Ereg (ms_regs ms1) []))) by apply Eimg_env.
replace (BASE + 1020) with (BASE + (CNB_OFF + CNB_HDR))
  by (unfold CNB_OFF, CNB_SLOT, CNB_HDR; change (Z.of_nat 201) with 201; lia).
paj_run_to_tok_x_inv RUNTO HS2 HJ1 SHOK2 HPM1 (0, 0) (CNB_OFF + CNB_COPY).
{ intros a (r & Hr & Ha). cbn [ss_mem In] in Hr.
  destruct Hr as [<-|[<-|[]]]; cbn [cnb1_RF cnb1_RS YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
    [rewrite U19 in Ha | rewrite U18 in Ha];
    right; right; right; exists CNB_CID, (bi_fpos D); (split; [left; reflexivity|]); rewrite EF, cnb1_fsb;
    [left | right]; unfold in_zr; cbn [fst snd]; lia. }
rename ms into ms2. rename HS2 into HS3. rename HJ1 into HJ2. rename HPM1 into HPM2.
rename HF into HF2. rename HFr into HFr2. rename HG into HG2.
pmkst HS3.
pose proof (regs_kept_of_st_ok_pi _ _ _ (ms_regs ms1) []
  [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 21%bv; 22%bv; 23%bv; 24%bv; 26%bv; 27%bv] HS3
  (cnb1_agree (ms_regs ms1)) ltac:(vm_compute; reflexivity)) as K2.
cbn [ms_regs restrict] in K2.
replace (BASE + 1204) with (cnb_pc CNB_COPY)
  by (unfold cnb_pc, CNB_OFF, CNB_SLOT, CNB_COPY; change (Z.of_nat 201) with 201; lia).
(* ---- THE EXIT ---- *)
apply SRr_ret. split; [reflexivity|].
do 3 eexists. split; [reflexivity|].
(* the journal at the cut's budget WS: unbased from the rebased entry with the cut's wild part *)
split.
{ unfold cnb_J. exists WS. split; [|exact HBUD].
  eapply YCbqGwild.ajournal_xw_unbase0; [exact HJ2 | exact HWILD]. }
split.
{ intros x Hx.
  assert (N2 : ~ in_wrange (Eimg (Ereg (ms_regs ms1) [])) [cnb1_RF; cnb1_RS] (bv_unsigned x)).
  { intros (r & Hr & Hb). cbn [In] in Hr.
    destruct Hr as [<-|[<-|[]]]; cbn [cnb1_RF cnb1_RS YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb;
      [rewrite U19 in Hb | rewrite U18 in Hb]; apply Hx; unfold cnb1_wr; lia. }
  assert (N1 : ~ in_wrange (Eimg (Ereg regs [])) [cnb1_R1] (bv_unsigned x)).
  { intros (r & Hr & Hb). cbn [In] in Hr. destruct Hr as [<-|[]].
    cbn [cnb1_R1 YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb. rewrite U9 in Hb. apply Hx. unfold cnb1_wr. lia. }
  rewrite (HFr2 x N2), (HFr1 x N1). reflexivity. }
split; [exact (cnb1_grows_trans _ _ _ HG1 HG2)|].
split.
{ apply (cnb1_kept_rdword SEGS (w_H W) (ms_mem ms1) (ms_mem ms2)
    (in_wrange (Eimg (Ereg (ms_regs ms1) [])) [cnb1_RF; cnb1_RS]) _ _ HFr2); [|exact W48].
  intros x Hx. split; [lia|]. intros (r & Hr & Hb). cbn [In] in Hr.
  destruct Hr as [<-|[<-|[]]]; cbn [cnb1_RF cnb1_RS YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb;
    [rewrite U19 in Hb | rewrite U18 in Hb]; unfold shadow_addr, SHADOW_OFF in Hb; lia. }
split; [|exact HPM2].
split.
{ intros r Hr. rewrite (K2 r ltac:(cbn [In] in Hr |- *; tauto)). exact (K1 r Hr). }
split; [rewrite (K2 18%bv ltac:(cbn; tauto)); exact Q18|].
split; [rewrite (K2 20%bv ltac:(cbn; tauto)); exact Q20|].
split; [rewrite (K2 21%bv ltac:(cbn; tauto)); exact Q21|].
split; [rewrite (K2 22%bv ltac:(cbn; tauto)); exact Q22|].
rewrite (K2 26%bv ltac:(cbn; tauto)); exact Q26.
Qed.

(* ---- WHAT THE WRITE SET MISSES ---- *)
(* a byte of a live block or of the image, and the shadow byte of its granule, are off the write set: the frame and
   the blocks are disjoint (alx_sep), the image is not the frame (alx_client_img), every block and image byte is below
   the shadow or above it, and below the stack; F is 8-aligned, so a shadow byte of F's 320 bytes is F's alone *)
Lemma cnb1_safe_off : forall D wk ly S Hp W mem md k a,
  cnb_J (SK := SK) B ARcfx D wk ly S Hp W mem md k -> In (CNB_CID, bi_fpos D) (frames S) ->
  ((exists b n, In (b, n) (ablocks B ly S) /\ b <= a < b + req_size n) \/ in_img SEGS a) ->
  (0 <= a < 2 ^ 64 /\ ~ cnb1_wr D a) /\ (0 <= SHADOW_OFF + a / 8 < 2 ^ 64 /\ ~ cnb1_wr D (SHADOW_OFF + a / 8)).
Proof.
intros D wk ly S Hp W mem md k a HJ Hin Ha.
destruct (cnb1_nums D wk ly S Hp W mem md k HJ Hin) as (EF & F32 & F4k & Fc & Fapp & S32 & S1b & Sp & STKv & Ceil).
pose proof HJ as (WS & HJW & _). pose proof (ajx_ar HJW) as HAR.
assert (HNF : ~ (cnb_F D <= a < cnb_F D + 512)).
{ destruct Ha as [(b & n & Hb & Hr) | Him].
  - pose proof (sep_block_frame_x SEGS B ARcfx LAWS ly S Hp W mem md b n CNB_CID (bi_fpos D) HAR Hb Hin) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite EF, cnb1_fsb in Hd. lia.
  - intros Hr. apply (frm_img_x SEGS B ARcfx LAWS ly S Hp W mem md CNB_CID (bi_fpos D) a HAR Hin);
      [rewrite EF, cnb1_fsb; lia | exact Him]. }
assert (HAB : 0 <= a < YM05.alloc_ceiling /\ (a < SHADOW_OFF \/ kHighMemBeg <= a)).
{ destruct Ha as [(b & n & Hb & Hr) | Him].
  - destruct (alx_blocks SEGS B ARcfx LAWS ly S Hp W mem md b n HAR Hb) as (_ & H4096 & Hc & Happ & _).
    unfold in_app, ASAN_CEIL, kLowShadowBeg, SHADOW_OFF in *. lia.
  - pose proof (pa_segs_low a Him) as Hl. unfold kLowMemEnd, SHADOW_OFF in *. lia. }
unfold cnb1_wr, shadow_addr. unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *.
split; split; [lia | intros [Hw|[Hw|Hw]]; lia | lia | intros [Hw|[Hw|Hw]]; lia].
Qed.
(* a static: the B' range fact's one consumer *)
Lemma cnb1_pst_off : cnb1_img_top -> forall D wk ly S Hp W mem md k a,
  cnb_J (SK := SK) B ARcfx D wk ly S Hp W mem md k -> In (CNB_CID, bi_fpos D) (frames S) ->
  Exists (in_zr a) prh_pst -> 0 <= a < 2 ^ 64 /\ ~ cnb1_wr D a.
Proof.
intros HTOP D wk ly S Hp W mem md k a HJ Hin Hpst.
destruct (cnb1_nums D wk ly S Hp W mem md k HJ Hin) as (EF & F32 & F4k & Fc & Fapp & S32 & S1b & Sp & STKv & Ceil).
pose proof HJ as (WS & HJW & _). pose proof (ajx_ar HJW) as HAR.
pose proof (cnb1_pst_below_frame HTOP ly S Hp W mem md CNB_CID (bi_fpos D) a HAR Hin Hpst) as Hb. rewrite EF in Hb.
pose proof (cnb1_pst_range a Hpst) as Hr.
unfold cnb1_wr, shadow_addr, SHADOW_OFF. split; [lia | intros [Hw|[Hw|Hw]]; lia].
Qed.
(* the input: a live block or an image read-only range (the contract's prhReader_home, kept_at) *)
Lemma cnb1_home_safe : forall ly S Hp (W : world SEGS) mem Lam peak cnt fail ran most own p n x,
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  PRH_FnReader.prhReader_home B ly S Hp Lam p n -> p <= x < p + n ->
  (exists b m, In (b, m) (ablocks B ly S) /\ b <= x < b + req_size m) \/ in_img SEGS x.
Proof.
intros ly S Hp W mem Lam peak cnt fail ran most own p n x HL [Hk | (b & m & Hb & _ & Hb1 & Hb2)] Hx.
- assert (HF : Forall (fun ak => prh_hblock B ly S Hp W mem (fst ak) (snd ak)) Lam)
    by (eapply prh_ledger_blocks; exact HL).
  destruct Hk as [(b & m & Hin & Hb1 & Hb2) | [(_ & _ & _ & Hro) | Hki]].
  + left. pose proof (proj1 (Forall_forall _ _) HF (b, m) Hin) as (Hm0 & Hab & _). cbn [fst snd] in *.
    exists (b - cf_head), (m + cf_head). split; [exact Hab|]. unfold req_size.
    change cf_head with 16. destruct (Z.eqb_spec (m + 16) 0); cbv beta iota; lia.
  + right. destruct (Hro x Hx) as (Hr & _).
    destruct Hr as [(sg & Hsg & _ & Hlo) | Hrel];
      [exists sg; split; [exact Hsg | exact Hlo] | exact (pa_relro_img x Hrel)].
  + right. destruct Hki as (_ & _ & Hro). destruct (Hro x Hx) as (Hr & _).
    destruct Hr as [(sg & Hsg & _ & Hlo) | Hrel];
      [exists sg; split; [exact Hsg | exact Hlo] | exact (pa_relro_img x Hrel)].
- left. exists b, m. split; [exact Hb|]. unfold req_size. destruct (Z.eqb_spec m 0); cbv beta iota; lia.
Qed.

(* ---- THE STATE FACTS CARRIED ACROSS A KEPT MEMORY ---- *)
Lemma cnb1_pst_val : forall (W : world SEGS) m m' Wr p (w : nat) v,
  cnb1_kept (w_H W) m m' Wr -> (forall a, Exists (in_zr a) prh_pst -> 0 <= a < 2 ^ 64 /\ ~ Wr a) ->
  In (p, Z.of_nat w) prh_pst -> val_mem SEGS (mrestrict (w_H W) m) p w v -> val_mem SEGS (mrestrict (w_H W) m') p w v.
Proof.
intros W m m' Wr p w v HK HP Hin Hv.
apply (cnb1_kept_val_mem SEGS (w_H W) m m' Wr p w v HK); [|exact Hv].
intros k0 Hk0. apply HP. apply Exists_exists. exists (p, Z.of_nat w). split; [exact Hin|].
unfold in_zr; cbn [fst snd]. lia.
Qed.
(* prh_glob read by shape (every val_mem conjunct, with the Batch-2 fields prh_most / prh_own unfolded, is one prh_pst
   cell), so a cell the kit owner adds is carried too *)
Lemma cnb1_glob_keep : forall (W : world SEGS) m m' Wr live peak cnt fail ran most own,
  cnb1_kept (w_H W) m m' Wr -> (forall a, Exists (in_zr a) prh_pst -> 0 <= a < 2 ^ 64 /\ ~ Wr a) ->
  prh_glob W m live peak cnt fail ran most own -> prh_glob W m' live peak cnt fail ran most own.
Proof.
intros W m m' Wr live peak cnt fail ran most own HK HP HG.
assert (CELL : forall p (w : nat) v, In (p, Z.of_nat w) prh_pst ->
  val_mem SEGS (mrestrict (w_H W) m) p w v -> val_mem SEGS (mrestrict (w_H W) m') p w v)
  by (intros p w v; exact (cnb1_pst_val W m m' Wr p w v HK HP)).
unfold prh_glob, prh_most, prh_own in *.
repeat match goal with H : _ /\ _ |- _ => destruct H end.
repeat split; try assumption;
match goal with H : val_mem SEGS (mrestrict _ m) ?p ?w ?v |- val_mem SEGS (mrestrict _ m') ?p ?w ?v =>
  exact (CELL p w v ltac:(unfold prh_pst; cbn [In]; repeat (first [left; reflexivity | right])) H) end.
Qed.
(* the ledger through its named projections (PRH_Base.v 3004a98fe2d9), rebuilt at the new memory *)
Lemma cnb1_ledger_keep : forall ly S Hp (W : world SEGS) m m' Wr Lam peak cnt fail ran most own,
  cnb1_kept (w_H W) m m' Wr -> (forall a, Exists (in_zr a) prh_pst -> 0 <= a < 2 ^ 64 /\ ~ Wr a) ->
  (forall b n a, In (b, n) (ablocks B ly S) -> b <= a < b + req_size n -> 0 <= a < 2 ^ 64 /\ ~ Wr a) ->
  prh_ledger B ly S Hp W m Lam peak cnt fail ran most own -> prh_ledger B ly S Hp W m' Lam peak cnt fail ran most own.
Proof.
intros ly S Hp W m m' Wr Lam peak cnt fail ran most own HK HP HB HL.
assert (HG : prh_glob W m (Ledger.lsum Lam) peak cnt fail ran most own) by (eapply prh_ledger_glob; exact HL).
assert (HND : NoDup (map fst Lam)) by (eapply prh_ledger_nodup; exact HL).
assert (HF : Forall (fun ak => prh_hblock B ly S Hp W m (fst ak) (snd ak)) Lam) by (eapply prh_ledger_blocks; exact HL).
assert (HPm : Permutation Hp (map (fun ak => fst ak - cf_head) Lam)) by (eapply prh_ledger_heads; exact HL).
unfold prh_ledger.
split; [exact (cnb1_glob_keep W m m' Wr _ _ _ _ _ _ _ HK HP HG)|].
split; [exact HND|]. split; [|exact HPm].
eapply Forall_impl; [|exact HF]. intros [a kk] (Hk0 & Hin & Hhp & H16 & Hv). cbn [fst snd] in *.
split; [exact Hk0|]. split; [exact Hin|]. split; [exact Hhp|]. split; [exact H16|].
apply (cnb1_kept_val_mem SEGS (w_H W) m m' Wr _ 8 kk HK); [|exact Hv].
intros j Hj. apply (HB (a - cf_head) (kk + cf_head)); [exact Hin|].
unfold req_size. change cf_head with 16. destruct (Z.eqb_spec (kk + 16) 0); cbv beta iota; lia.
Qed.
(* the input bytes, their shadow, and its hull (visibility only, which the runner never takes away) *)
Lemma cnb1_src_keep : forall (W : world SEGS) m m' Wr p l,
  cnb1_kept (w_H W) m m' Wr -> mem_grows (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
  (forall x, p <= x < p + Z.of_nat (length l) ->
     (0 <= x < 2 ^ 64 /\ ~ Wr x) /\ (0 <= SHADOW_OFF + x / 8 < 2 ^ 64 /\ ~ Wr (SHADOW_OFF + x / 8))) ->
  src_rd W m p l -> src_rd W m' p l.
Proof.
intros W m m' Wr p l HK HG HX (HB & H4 & Hc & Hr & HA & HH).
split.
{ intros j Hj. destruct (HB j Hj) as [Hv Hb]. split; [|exact Hb].
  apply (cnb1_kept_val_mem SEGS (w_H W) m m' Wr _ 1 _ HK); [|exact Hv].
  intros k0 Hk0. assert (Hx : p <= p + Z.of_nat j + Z.of_nat k0 < p + Z.of_nat (length l)) by lia.
  exact (proj1 (HX _ Hx)). }
split; [exact H4|]. split; [exact Hc|]. split; [exact Hr|]. split.
{ intros x Hx. destruct (HA x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
  unfold shadow_of_addr in *. destruct (HX x Hx) as (_ & Hsa & Hsw).
  rewrite (cnb1_kept_aview SEGS (w_H W) m m' Wr _ HK Hsa Hsw). exact Hs. }
{ intros Hpos s Hs. apply (cnb1_grows_aview SEGS (w_H W) m m' s HG). exact (HH Hpos s Hs). }
Qed.
(* the thirteen saved words, in [entry sp - 104, entry sp) *)
Lemma cnb1_saved_keep : forall D (W : world SEGS) m m' Wr,
  cnb1_kept (w_H W) m m' Wr ->
  (forall x, cnb_sp0 D - 104 <= x < cnb_sp0 D -> 0 <= x < 2 ^ 64 /\ ~ Wr x) ->
  cnb_saved D W m -> cnb_saved D W m'.
Proof.
intros D W m m' Wr HK HX HS. unfold cnb_saved in *. rewrite Forall_forall in HS |- *.
intros [off r] Hin. pose proof (HS _ Hin) as Hw. cbn [fst snd] in *.
assert (Hoff : 56 <= off <= 152).
{ cbn [In] in Hin. repeat (destruct Hin as [E|Hin]; [injection E; intros; subst; lia|]). destruct Hin. }
apply (cnb1_kept_rdword SEGS (w_H W) m m' Wr _ _ HK); [|exact Hw].
intros x Hx. apply HX. lia.
Qed.
(* the frame: its flag word at F + 504, its bytes and its shadow present *)
Lemma cnb1_frame_keep : forall D ly S (W : world SEGS) m m' Wr,
  cnb1_kept (w_H W) m m' Wr -> mem_grows (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
  (forall x, cnb_F D + 504 <= x < cnb_F D + 512 -> 0 <= x < 2 ^ 64 /\ ~ Wr x) ->
  cnb_frame D ly S W m -> cnb_frame D ly S W m'.
Proof.
intros D ly S W m m' Wr HK HG HX (Hfrs & Hnin & Hflag & HFP & HSP).
split; [exact Hfrs|]. split; [exact Hnin|]. split.
{ apply (cnb1_kept_rdword SEGS (w_H W) m m' Wr _ _ HK); [|exact Hflag].
  intros x Hx. apply HX. rewrite cnb1_fsb in Hx. lia. }
split; intros a Ha; [exact (cnb1_grows_apresent _ m m' a HG (HFP a Ha)) | exact (cnb1_grows_apresent _ m m' a HG (HSP a Ha))].
Qed.
End run.

(* ==== THE SEGMENT ==== *)
Section cb1. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {RL : PrhRoomLive}.
#[local] Existing Instance CfParams_preset.
#[local] Existing Instance prh_img_B.
Context {PA : PAImg B_prog_listing}.
#[local] Existing Instance PL_cno_B.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
Variable B : asyms.
Variable SK : YI16.sink_head.
#[local] Abbreviation ARcfx := (fun ly S Hp W mem md => ARcf SEGS B ly S Hp W mem md /\ xs_placed_cf ly S).
(* the entry's call context; the cut's cnb_pre takes no DW (prh_univ_closure B CTX0, DW-SPLIT) *)
Variable CTX0 : list (list Z).
(* THE ONE NAMED ARGUMENT (the B' range fact, see the header): owner the B' instantiation file, once IMG_TOP_B lands *)
Hypothesis HTOP : cnb1_img_top (PA := PA).

(* THE SEGMENT STATEMENT (the contract's FORWARD form, Cno102B_Base.v 06098b64f859 :639-643): generic P with its
   runner laws only - CB1 is call-free *)
Definition cnb_seg_poisonP : Prop :=
  forall P : (word -> option byte) -> Prop, srr_inv_laws SEGS P ->
  forall D fxk ly S Hp W regs mem md k,
  cnb_pre (fx := fx) B ARcfx CTX0 D ->
  cnb_at_frame (fx := fx) (SK := SK) B ARcfx D fxk ly S Hp W regs mem md k -> P mem ->
  SRr SEGS W (@cnb_cfg SEGS fxk (cnb_pc CNB_FRAME) regs mem md)
    (fun W' c' => cnb_ex_copy (fx := fx) (SK := SK) B ARcfx D W' c' /\ P (ms_mem (cfg_ms c'))).

Lemma cnb_seg_poison : cnb_seg_poisonP.
Proof.
intros P PLAW D fxk ly S Hp W regs mem md k _ HAT HPM.
(* the cut and its cnb_base, each conjunct by its type *)
pose proof HAT as HAT'. unfold cnb_at_frame in HAT'.
assert (HB : cnb_base (fx := fx) (SK := SK) B ARcfx D fxk ly S Hp W regs mem md k 0) by cnb1_pick HAT'.
assert (HR : cnb_regsat regs [(2%bv, cnb_S1 D); (8%bv, cnb_sp0 D); (9%bv, cnb_S1 D); (18%bv, SHADOW_OFF);
  (19%bv, cnb_F D); (23%bv, cnb_size D); (24%bv, bi_data D); (27%bv, cnb_F D)]) by cnb1_pick HAT'.
assert (HPMID : cnb_pre_mid B D ly S Hp W mem 0) by cnb1_pick HAT'.
assert (HPROG : cnb_prog D [] S) by cnb1_pick HAT'.
assert (HAB : ablocks B ly S = ablocks B (bi_ly D) (bi_S D)) by cnb1_pick HAT'.
assert (HBB : blocks_bytes S = blocks_bytes (bi_S D)) by cnb1_pick HAT'.
assert (HHULL : PresetHullBudget.hull_budget S (cnb_hev_all (bi_x D))) by cnb1_pick HAT'.
clear HAT HAT'.
pose proof HB as HB'. unfold cnb_base in HB'.
assert (Hfrz : frm_zero (@YK11.fp_csr fxk)) by cnb1_pick HB'.
assert (Hfk : fregs_kept_x fx fxk) by cnb1_pick HB'.
assert (HJ : cnb_J (SK := SK) B ARcfx D 0 ly S Hp W mem md k) by cnb1_pick HB'.
assert (HFR : cnb_frame D ly S W mem) by cnb1_pick HB'.
assert (HSAV : cnb_saved D W mem) by cnb1_pick HB'.
assert (HG3 : getr regs 3%bv = getr (bi_regs D) 3%bv) by cnb1_pick HB'.
assert (HG4 : getr regs 4%bv = getr (bi_regs D) 4%bv) by cnb1_pick HB'.
assert (HROD : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem)) by cnb1_pick HB'.
clear HB HB'.
assert (Hin : In (CNB_CID, bi_fpos D) (frames S)) by (destruct HFR as (Hfrs & _); rewrite Hfrs; left; reflexivity).
unfold cnb_regsat in HR. pose proof (proj1 (Forall_forall _ _) HR) as HRf.
assert (R2 : getr regs 2%bv = w64 (cnb_S1 D)) by exact (HRf (2%bv, cnb_S1 D) ltac:(cbn; tauto)).
assert (R8 : getr regs 8%bv = w64 (cnb_sp0 D)) by exact (HRf (8%bv, cnb_sp0 D) ltac:(cbn; tauto)).
assert (R9 : getr regs 9%bv = w64 (cnb_S1 D)) by exact (HRf (9%bv, cnb_S1 D) ltac:(cbn; tauto)).
assert (R18 : getr regs 18%bv = w64 SHADOW_OFF) by exact (HRf (18%bv, SHADOW_OFF) ltac:(cbn; tauto)).
assert (R19 : getr regs 19%bv = w64 (cnb_F D)) by exact (HRf (19%bv, cnb_F D) ltac:(cbn; tauto)).
assert (R23 : getr regs 23%bv = w64 (cnb_size D)) by exact (HRf (23%bv, cnb_size D) ltac:(cbn; tauto)).
assert (R24 : getr regs 24%bv = w64 (bi_data D)) by exact (HRf (24%bv, bi_data D) ltac:(cbn; tauto)).
assert (R27 : getr regs 27%bv = w64 (cnb_F D)) by exact (HRf (27%bv, cnb_F D) ltac:(cbn; tauto)).
destruct (cnb1_nums B SK D 0 ly S Hp W mem md k HJ Hin)
  as (EF & F32 & F4k & Fc & Fapp & S32 & S1b & Sp & STKv & Ceil).
pose proof HPMID as HPMID'. unfold cnb_pre_mid in HPMID'.
assert (HHp : Hp = bi_Hp D) by cnb1_pick HPMID'.
assert (HLED : prh_ledger B ly S Hp W mem (bi_Lam D) (bi_peak D) (bi_cnt D) SIZE_MAXZ (bi_ran D) (bi_most D) 0)
  by cnb1_pick HPMID'.
assert (HRL : room_live_cf S) by cnb1_pick HPMID'.
assert (HSRC : src_rd W mem (bi_data D) (bi_x D)) by cnb1_pick HPMID'.
assert (HHOME : 0 < cnb_size D -> PRH_FnReader.prhReader_home B ly S Hp (bi_Lam D) (bi_data D) (cnb_size D))
  by cnb1_pick HPMID'.
clear HPMID HPMID'.
(* what the write set misses *)
assert (PSTc : forall a, Exists (in_zr a) prh_pst -> 0 <= a < 2 ^ 64 /\ ~ cnb1_wr D a)
  by (intros a Ha; exact (cnb1_pst_off B SK HTOP D 0 ly S Hp W mem md k a HJ Hin Ha)).
assert (BLKc : forall b n a, In (b, n) (ablocks B ly S) -> b <= a < b + req_size n -> 0 <= a < 2 ^ 64 /\ ~ cnb1_wr D a).
{ intros b n a Hb Ha.
  exact (proj1 (cnb1_safe_off B SK D 0 ly S Hp W mem md k a HJ Hin (or_introl (ex_intro _ b (ex_intro _ n (conj Hb Ha)))))). }
assert (DATc : forall x, bi_data D <= x < bi_data D + Z.of_nat (length (bi_x D)) ->
  (0 <= x < 2 ^ 64 /\ ~ cnb1_wr D x) /\ (0 <= SHADOW_OFF + x / 8 < 2 ^ 64 /\ ~ cnb1_wr D (SHADOW_OFF + x / 8))).
{ intros x Hx. apply (cnb1_safe_off B SK D 0 ly S Hp W mem md k x HJ Hin).
  apply (cnb1_home_safe B ly S Hp W mem (bi_Lam D) (bi_peak D) (bi_cnt D) SIZE_MAXZ (bi_ran D) (bi_most D) 0
    (bi_data D) (cnb_size D) x HLED); [apply HHOME; unfold cnb_size; lia | exact Hx]. }
unfold cnb_cfg.
eapply SRr_mono; [exact (cnb1_run (fz := fxk) B SK P PLAW D 0 ly S Hp W regs mem md k HJ Hin R9 R18 R19 HPM)|].
cbv beta. intros W' c' _ (-> & regs' & mem' & md' & -> & HJ' & HK & HGR & HW48 & HRG & HPM').
destruct HRG as (RK & Q18 & Q20 & Q21 & Q22 & Q26).
split; [|exact HPM'].
exists fxk, ly, S, Hp, regs', mem', md', k.
split; [reflexivity|].
split.
{ (* cnb_base *)
  split; [exact Hfrz|]. split; [exact Hfk|]. split; [exact HJ'|].
  split.
  { apply (cnb1_frame_keep D ly S W mem mem' (cnb1_wr D) HK HGR); [|exact HFR].
    intros x Hx. split; [lia|]. unfold cnb1_wr, shadow_addr, SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *.
    intros [Hw|[Hw|Hw]]; lia. }
  split.
  { apply (cnb1_saved_keep D W mem mem' (cnb1_wr D) HK); [|exact HSAV].
    intros x Hx. split; [lia|]. unfold cnb1_wr, shadow_addr, SHADOW_OFF in *. intros [Hw|[Hw|Hw]]; lia. }
  split; [rewrite (RK 3%bv ltac:(cbn; tauto)); exact HG3|].
  split; [rewrite (RK 4%bv ltac:(cbn; tauto)); exact HG4|].
  (* the read-only view: a read-only byte is an image byte, off the write set *)
  intros a Hro Hown Herr.
  assert (Him : in_img SEGS a).
  { destruct Hro as [(sg & Hsg & _ & Hr) | Hrel]; [exists sg; split; [exact Hsg | exact Hr] | exact (pa_relro_img a Hrel)]. }
  destruct (cnb1_safe_off B SK D 0 ly S Hp W mem md k a HJ Hin (or_intror Him)) as ((Ha & Hw) & _).
  rewrite (cnb1_kept_aview SEGS (w_H W) mem mem' (cnb1_wr D) a HK Ha Hw). exact (HROD a Hro Hown Herr). }
split.
{ (* the registers *)
  unfold cnb_regsat, cnb_core. cbn [app].
  repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd].
  all: first [ rewrite RK by (cbn; tauto); assumption | assumption ]. }
split; [exact HW48|].
split.
{ (* cnb_pre_mid at own = 0: the ledger, whose g_most / g_own_ran_out fields are prh_pst cells off the write set *)
  split; [exact HHp|].
  split; [exact (cnb1_ledger_keep B ly S Hp W mem mem' (cnb1_wr D) _ _ _ _ _ _ _ HK PSTc BLKc HLED)|].
  split; [exact HRL|].
  split; [exact (cnb1_src_keep W mem mem' (cnb1_wr D) _ _ HK HGR DATc HSRC)|].
  exact HHOME. }
(* cnb_prog D [] S: no run event, the same allocator state *)
split; [exact HPROG|].
split; [exact HAB|]. split; [exact HBB|].
(* the hull budget: CB1 makes no allocator call and leaves S as it is *)
exact HHULL.
Qed.
End cb1.
