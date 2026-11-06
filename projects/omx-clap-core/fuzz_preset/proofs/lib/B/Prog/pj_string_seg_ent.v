(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the ENTRY segment of pj_string's image-B walk (fuzz_preset asan-ubsan; the cuts of
   lib/B/Prog/pj_string_defs.v): from the kit's premises (pjs_pre, the kit's tip d607d12e4b0f) and
   fuzz_strdup's live-set bounds (pjs_cnt, derived in the top) at the entry to the cut pjs_C1 at the
   `jal fuzz_strdup` (+0x68), then the C1 segment (pjs_seg_C1, a premise) to the walk's post pjs_FIN.
   proves no function (kind: segment lemma): pjs_seg_entry_holds is pjs_seg_entry from pjs_texts, pjs_g_lit and
   pjs_seg_C1. The body walked (engine YC80x / YC1fPx over YCbqG's ajournal_x at the caller-window widened window
   (STK_pj_string + d) (sp0 + d), YCbqGcallW.v ajournal_x_init_W), three seats:
     seat 0, +0x00 .. +0x30  frame 32, ra / s0 / s1 / s2 saved at sp+24 / +16 / +8 / +0, s1 := s, s2 := the shadow
                             offset (the GOT slot and the cell: FuzzFreeB.v's got_regionP / bcell_regionP, PALib), s0 :=
                             v, the memset arguments; the run stops at `jal __asan_memset`;
     +0x30                   memset (v, 0, 56) by YGcallMxmn.v aj_intrin_at_xm_fr into v's harness block, other block
                             or fake frame, from pjs_texts' __asan_memset text (its m-form: the memnorm keep);
     seat 1, +0x34 .. +0x54  the UBSan NULL / alignment checks and the ASan check of the 4-byte store (the engine decides
                             all three: v >= 4096, v mod 8 = 0, v's shadow entry), v->type := 4; the run stops at
                             `bnez s1` (+0x58);
     seat 2, +0x58 .. +0x64  the branch on s (paj_branch): s <> 0 -> a0 := s1; s = 0 -> s1 := the "" literal PJS_LIT,
                             a0 := s1; both runs stop at PJS_C1, with no memory region (the memory is the seat's).
   The memory at C1 is the entry's but for the frame [sp0 - 32, sp0), the callee window below it and v's 56 bytes
   (pjs_bytes 0). The ledger's head words miss v's bytes by prh_head_wide (the kit's name, PRH_Base.v: 8 <= cf_head; a
   premise of the text). The memnorm keep from the entry memory is the runners' memory invariant
   (YC1fPx.v paj_run_*_inv, pj_string_runf.v paj_run_xf_inv; YSRrMemnorm.v's instance) and memset's keep.
   Section hypotheses: AR_laws_x SEGS B ARx cf_head; PALib B (the unit's image binding of B, a STAND-IN as in
   FuzzFreeB.v / FuzzMallocB.v / OwnB.v, owner a Theorem Labs lane).
   Numerals: 32 / 24 / 16 / 8 / 56 / 4 (LENGTH: frame, slots, node, type); 4096 / 4128 (LENGTH: page, ESTACK + frame);
   2 ^ 44 / 2 ^ 46 / 2 ^ 47 / 2 ^ 64 (LENGTH: shadow span, stack band, words); 88 (DERIVED: the slot of `bnez s1`
   times 4); atom 32 (DERIVED: the first extra atom). No ADDRESS literal: PJS_LIT's numbers are computed. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG FCiface YGcallMx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YGcfRoomKeep YG0dcf YGcfRoomPre.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC1fP YC80x YC1fPx YC80xf YCbqGcall YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoomLive YGcfStr.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YSRrMemnorm YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PjRoundTrip PresetLiveBounds.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_Charge PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_FnAlloc PRH_FnPj.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1Ledger PjStringCommon.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import S1ImgB pj_string_defs pj_string_glue
  pj_string_runf.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance prh_img_B.

(* ---- the three seats ---- *)
Definition PJS0_BR : Z := PJS_PC + 88.   (* the `bnez s1` *)
Definition PJS0_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
(* seat 0, at the entry: pj_string's frame (atom 2, written over [sp0 - 32, sp0)), the GOT slot and the shadow-offset
   cell, the shadow offset as the extra atom 32 *)
Definition PJS0_Bx0 : sv := SOff 32 0.
Definition pjs0_frame : YP09.region := YP09.mkRegion (Some 2%nat) (-32) 0 (-32) 0 [].
Definition pjs0_facts0 : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] B_alias_hints.
Definition ss_pjs0 : sstate := mkSS PJS_PC sr_atoms [pjs0_frame; got_regionP; bcell_regionP 32] None pjs0_facts0.
(* seat 1, at memset's return site: v's node (s0, atom 8) written over [v, v + 4), its shadow entry, s2 (atom 18) the
   shadow offset *)
Definition PJS0_Bx1 : sv := SOff 18 0.
Definition PJS0_SH1 : list shent := [mkSHE 8 0 56].
Definition pjs0_vreg : YP09.region := YP09.mkRegion (Some 8%nat) 0 56 0 4 [].
Definition pjs0_facts1 : facts :=
  mkFacts [(8%nat, mkAF 4096 (2 ^ 47 - 64) 3); (18%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition ss_pjs1 : sstate := mkSS PJS_M1 sr_atoms [pjs0_vreg] None pjs0_facts1.
(* seat 2, at the `bnez s1`: no memory region, no fact (the branch decides s) *)
Definition PJS0_Bx2 : sv := SLit SHADOW_OFF.
Definition PJS0_Bspan2 : Z * Z := (0, 0).
Definition ss_pjs2 : sstate := mkSS PJS0_BR sr_atoms [] None (mkFacts [] [] []).
(* the registers seat 1 and seat 2 keep from the one before (the callee-saved ones memset keeps, s1 before the branch) *)
Definition PJS0_KR : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

(* ---- pure helpers ---- *)
Lemma pjs0_hull_bounds : forall x n s, 0 <= x -> 0 < n -> x + n <= kHighMemEnd ->
  shadow_addr x / 8 * 8 <= s < shadow_addr (x + n - 1) / 8 * 8 + 8 -> kLowMemEnd <= s < kHighShadowEnd.
Proof.
intros x n s H0 Hn Hx Hs. unfold shadow_addr, kLowMemEnd, kHighShadowEnd, kHighMemEnd, SHADOW_OFF in *.
pose proof (Z.div_pos x 8 H0 ltac:(lia)) as P1.
assert (P3 : (x + n - 1) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
pose proof (Z.div_mod (SHADOW_OFF + x / 8) 8 ltac:(lia)) as D1.
pose proof (Z.mod_pos_bound (SHADOW_OFF + x / 8) 8 ltac:(lia)) as M1.
pose proof (Z.div_mod (SHADOW_OFF + (x + n - 1) / 8) 8 ltac:(lia)) as D2.
pose proof (Z.mod_pos_bound (SHADOW_OFF + (x + n - 1) / 8) 8 ltac:(lia)) as M2.
unfold SHADOW_OFF in *.
lia.
Qed.
Lemma pjs0_in_roP_rng : forall segs rlo rhi lo hi,
  existsb (fun s => negb (seg_writable s) && (Z.of_N (seg_base s) <=? lo) &&
    (hi <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) segs = true ->
  forall a, lo <= a < hi -> in_roP segs rlo rhi a.
Proof.
intros segs rlo rhi lo hi H a Ha. left. apply existsb_exists in H as (s & Hin & Hb).
apply andb_prop in Hb as [Hb H3]. apply andb_prop in Hb as [H1 H2].
exists s. split; [exact Hin|]. split; [destruct (seg_writable s); [discriminate H1 | reflexivity]|].
apply Z.leb_le in H2. apply Z.leb_le in H3. lia.
Qed.
Lemma pjs0_cs_of_list : forall (r : bv 5), In r PJS_KEPT -> In r PJS0_KR.
Proof. intros r Hr. unfold PJS_KEPT in Hr. unfold PJS0_KR. cbn [In] in Hr |- *. tauto. Qed.
Ltac pjs0_cs :=
  lazymatch goal with |- acallee_saved (bv_unsigned ?x) =>
    let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v end;
  unfold acallee_saved; lia.
Lemma pjs0_pres : forall regs regs' (r : bv 5), aregs_preserved regs regs' -> acallee_saved (bv_unsigned r) ->
  getr regs' r = getr regs r.
Proof. intros regs regs' r HP Hr. rewrite <- (Z_to_bv_bv_unsigned 5 r). exact (HP _ Hr). Qed.

Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Notation PA := PI_prog_B.
#[local] Notation PL := PL_prog_B.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation VAL := (@pa_val _ B_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
#[local] Notation RLO := (@pa_relro_lo _ B_prog_listing PA).
#[local] Notation RHI := (@pa_relro_hi _ B_prog_listing PA).
#[local] Notation PST := (prh_pst (PI := prh_img_B)).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
#[local] Notation AJ := (ajournal_x (SK := SK) SEGS B PST ARx).
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
(* STAND-IN for the unit's image binding of B (TfibSyms analogue; owner a Theorem Labs lane), proved once by the final instance *)
Hypothesis PAL : PALib (L := B_prog_listing) (PI := PI_prog_B) B.


(* ---- memory helpers (pj_parse_seg_ent.v's, at this file's names) ---- *)
Definition pjs0_cv (rs : smem) (j : nat) (off w : Z) : option YP09.chunk :=
  match find_region rs (Some j) off w with Some r => find_chunk (YP09.r_chunks r) off w | None => None end.
Lemma pjs0_cv_ok : forall E ss ms j off w c, st_ok SEGS E ss ms -> pjs0_cv (ss_mem ss) j off w = Some c ->
  YP09.chunk_ok SEGS E (ms_mem ms) (bv_unsigned (ew E j)) c.
Proof.
intros E ss ms j off w c HS H. unfold pjs0_cv in H.
destruct (find_region (ss_mem ss) (Some j) off w) as [r|] eqn:Hr; [|discriminate H].
destruct (find_region_sound _ _ _ _ _ Hr) as (Hin & Hb & _).
destruct (find_chunk_sound _ _ _ _ H) as (Hcin & _).
destruct (st_ok_mem_ok SEGS E ss ms HS) as (_ & Hrs & _).
destruct (proj1 (Forall_forall _ _) Hrs r Hin) as (_ & _ & _ & Hcs).
pose proof (proj1 (Forall_forall _ _) Hcs _ Hcin) as Hck. rewrite Hb in Hck. exact Hck.
Qed.
Lemma pjs0_val : forall E ss ms j off (w : N) e v b a, st_ok_pi SEGS VAL E ss ms ->
  pjs0_cv (ss_mem ss) j off (Z.of_N w) = Some (YP09.mkChunk off (CVal w e)) ->
  bv_unsigned (ew E j) = b -> a = b + off -> U E e = v -> Z.of_N w <= 8 -> 0 <= v < 2 ^ (8 * Z.of_N w) ->
  val_mem SEGS (ms_mem ms) a (N.to_nat w) v.
Proof.
intros E ss ms j off w e v b a HS H Hb Ha HU Hw Hv. subst a.
pose proof (pjs0_cv_ok E (abs_ss VAL ss) ms j off (Z.of_N w) _ HS H) as Hck. rewrite Hb in Hck.
apply (val_of_chunk_ok SEGS E _ _ off w e v Hck); [|exact Hv | exact Hw].
rewrite <- HU. unfold U. symmetry. apply Z_to_bv_bv_unsigned.
Qed.
Lemma pjs0_val_st : forall E ss ms j off (w : N) e v b a, st_ok SEGS E ss ms ->
  pjs0_cv (ss_mem ss) j off (Z.of_N w) = Some (YP09.mkChunk off (CVal w e)) ->
  bv_unsigned (ew E j) = b -> a = b + off -> U E e = v -> Z.of_N w <= 8 -> 0 <= v < 2 ^ (8 * Z.of_N w) ->
  val_mem SEGS (ms_mem ms) a (N.to_nat w) v.
Proof.
intros E ss ms j off w e v b a HS H Hb Ha HU Hw Hv. subst a.
pose proof (pjs0_cv_ok E ss ms j off (Z.of_N w) _ HS H) as Hck. rewrite Hb in Hck.
apply (val_of_chunk_ok SEGS E _ _ off w e v Hck); [|exact Hv | exact Hw].
rewrite <- HU. unfold U. symmetry. apply Z_to_bv_bv_unsigned.
Qed.
Lemma pjs0_val1_of_aview : forall H m a v, aview SEGS H m a = Some v -> val_mem SEGS (mrestrict H m) a 1 v.
Proof.
intros H m a v Hv k Hk. assert (Ek : k = 0%nat) by lia. subst k.
replace (a + Z.of_nat 0) with a by lia.
unfold aview in Hv. destruct (mbyte SEGS (mrestrict H m) a) as [b|]; cbn [option_map] in Hv; [|discriminate Hv].
injection Hv as <-. pose proof (bv_unsigned_in_range 8 b) as Rb. unfold bv_modulus in Rb.
rewrite YI04.le_byte_small by (cbn in Rb |- *; lia). cbn [Z.of_nat]. rewrite Z.mul_0_r, Z.shiftr_0_r, Z_to_bv_bv_unsigned.
reflexivity.
Qed.
Lemma pjs0_garr8_of_aview : forall H m p l, Forall (fun x => 0 <= x < 256) l ->
  (forall j, (j < length l)%nat -> aview SEGS H m (p + Z.of_nat j) = Some (nth j l 0)) ->
  garr8 SEGS (mrestrict H m) p l.
Proof.
intros H m p l Hl Hv j Hj. split.
- apply pjs0_val1_of_aview. exact (Hv j Hj).
- apply (proj1 (Forall_forall _ _) Hl). apply nth_In. exact Hj.
Qed.
Lemma pjs0_aview_of_val : forall H m a (n : nat) x k, val_mem SEGS (mrestrict H m) a n x -> (k < n)%nat ->
  aview SEGS H m (a + Z.of_nat k) = Some (le_byte x n k).
Proof.
intros H m a n x k Hv Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
apply Z.mod_small. unfold YO0f.le_byte. apply Z.mod_pos_bound. lia.
Qed.
Lemma pjs0_aview_some : forall H m p l a, garr8 SEGS (mrestrict H m) p l -> p <= a < p + Z.of_nat (length l) ->
  aview SEGS H m a <> None.
Proof.
intros H m p l a Hg Ha. destruct (Hg (Z.to_nat (a - p)) ltac:(lia)) as [Hv _].
pose proof (pjs0_aview_of_val H m _ 1 _ 0 Hv ltac:(lia)) as E. rewrite Z2Nat.id in E by lia.
replace (p + (a - p) + Z.of_nat 0) with a in E by lia. rewrite E. discriminate.
Qed.
Lemma pjs0_grows_of_apresent : forall (H : word -> bool) m m',
  (forall a, apresent H m a -> apresent H m' a) -> mem_grows (mrestrict H m) (mrestrict H m').
Proof.
intros H m m' Hp x Hx. unfold mrestrict in *. destruct (H x) eqn:Ehx; [exact Hx|].
destruct (m x) as [b|] eqn:Em; [|exfalso; exact (Hx eq_refl)].
assert (Ha : apresent H m (bv_unsigned x)) by (unfold apresent; rewrite Z_to_bv_bv_unsigned; split; [exact Ehx | exists b; exact Em]).
destruct (Hp _ Ha) as [_ [b' Hb']]. rewrite Z_to_bv_bv_unsigned in Hb'. rewrite Hb'. discriminate.
Qed.

(* ---- what each seat's run keeps ---- *)
Lemma pjs0_awr0 : forall E STK sp0 d FP bl0 blc ly own, bv_unsigned (ew E 2) = sp0 -> 32 <= STK -> 0 <= d ->
  awr_ok E (ss_mem ss_pjs0) (STK + d) (sp0 + d) FP bl0 blc ly own.
Proof.
intros E STK sp0 d FP bl0 blc ly own Hsp HS Hd a (r & Hin & Hr). cbn [ss_pjs0 ss_mem In] in Hin.
destruct Hin as [<- | [<- | [<- | []]]];
  cbn [pjs0_frame got_regionP bcell_regionP YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; [|lia | lia].
left. rewrite Hsp in Hr. lia.
Qed.
Lemma pjs0_keep0 : forall (Wx : world SEGS) E (m m' : word -> option byte) sp0, bv_unsigned (ew E 2) = sp0 ->
  frame_of E (ss_mem ss_pjs0) (mrestrict (w_H Wx) m) (mrestrict (w_H Wx) m') ->
  forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 32 <= a < sp0) -> aview SEGS (w_H Wx) m' a = aview SEGS (w_H Wx) m a.
Proof.
intros Wx E m m' sp0 Hsp HF a Ha Hn. unfold aview. f_equal. unfold mbyte.
rewrite (HF (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by lia.
intros (r & Hin & Hr). cbn [ss_pjs0 ss_mem In] in Hin.
destruct Hin as [<- | [<- | [<- | []]]];
  cbn [pjs0_frame got_regionP bcell_regionP YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; [|lia | lia].
rewrite Hsp in Hr. lia.
Qed.
Lemma pjs0_keep1 : forall (Wx : world SEGS) E (m m' : word -> option byte) v, bv_unsigned (ew E 8) = v ->
  frame_of E (ss_mem ss_pjs1) (mrestrict (w_H Wx) m) (mrestrict (w_H Wx) m') ->
  forall a, 0 <= a < 2 ^ 64 -> ~ (v <= a < v + 4) -> aview SEGS (w_H Wx) m' a = aview SEGS (w_H Wx) m a.
Proof.
intros Wx E m m' v Hv HF a Ha Hn. unfold aview. f_equal. unfold mbyte.
rewrite (HF (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by lia.
intros (r & Hin & Hr). cbn [ss_pjs1 ss_mem In] in Hin. destruct Hin as [<- | []].
cbn [pjs0_vreg YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite Hv in Hr. lia.
Qed.

(* ---- the "" literal at C1: an image string under route (a) (pjs_g_lit, restated 2026-10-29: the ONE byte read -
   not owned-static, not errno, its const shadow cell - and pjs_g_lit_sh, the state fact; the rest of the granule is
   only asked visible, which the image ROM gives through mbyte's ROM fallback, checked here by computation) ---- *)
Lemma pjs0_lit_ok : forall ly S Hp W m md Lam, pjs_g_lit B -> pjs_g_lit_sh ARx -> ARx ly S Hp W m md ->
  arodata_okP SEGS RLO RHI B (aview SEGS (w_H W) m) ->
  cstr_ok (PA := PA) W m PJS_LIT [] /\ kept_at (PA := PA) B Lam PJS_LIT 1.
Proof.
intros ly S Hp W m md Lam (Hno & Her & GL2) GL3 HAR HROD.
assert (LV : PJS_LIT = 136224) by (vm_compute; reflexivity).
assert (LRO : forall a, PJS_LIT <= a < PJS_LIT + 8 -> in_roP SEGS RLO RHI a)
  by (apply pjs0_in_roP_rng; vm_compute; reflexivity).
(* the byte read: arodata_okP (the fpre) gives its ROM value *)
assert (L0 : aview SEGS (w_H W) m PJS_LIT = Some 0).
{ rewrite (HROD PJS_LIT (LRO PJS_LIT ltac:(lia)) Hno Her). vm_compute. reflexivity. }
(* the rest of the granule: image bytes, visible through mbyte's ROM fallback, whoever owns them *)
assert (LTL : forall a, PJS_LIT < a < PJS_LIT + 8 -> aview SEGS (w_H W) m a <> None).
{ assert (Hb : forallb (fun i => match seg_rom SEGS (Z_to_bv 64 (PJS_LIT + i)) with Some _ => true | None => false end)
    [1; 2; 3; 4; 5; 6; 7] = true) by (vm_compute; reflexivity).
  intros a Ha. unfold aview, mbyte. destruct (mrestrict (w_H W) m (Z_to_bv 64 a)); [discriminate|].
  destruct (seg_rom SEGS (Z_to_bv 64 a)) eqn:Er; [discriminate|]. exfalso.
  rewrite forallb_forall in Hb. specialize (Hb (a - PJS_LIT) ltac:(cbn [In]; lia)).
  replace (PJS_LIT + (a - PJS_LIT)) with a in Hb by lia. rewrite Er in Hb. discriminate Hb. }
assert (LSH : aview SEGS (w_H W) m (shadow_addr PJS_LIT) = Some 1).
{ pose proof (alx_const_cells SEGS B ARx LAWS ly S Hp W m md HAR) as HC.
  rewrite Forall_forall in HC. pose proof (HC _ (GL2 ly)) as Hz.
  unfold cell_holds in Hz. cbn [z1 c1 c_at c_val c_w aeval] in Hz.
  specialize (Hz 0%nat ltac:(lia)). change (Z.of_nat 0) with 0 in Hz. rewrite Z.add_0_r in Hz. rewrite Hz.
  reflexivity. }
assert (CA : shadow_addr PJS_LIT / 8 * 8 = 2147467904) by (vm_compute; reflexivity).
assert (CB : shadow_addr PJS_LIT = 2147467908) by (vm_compute; reflexivity).
assert (CI : IMG_LO_B = 65536) by (vm_compute; reflexivity).
assert (CT : IMG_TOP_B = 6295552) by (vm_compute; reflexivity).
split.
- unfold cstr_ok, cstr. cbn [length app Z.of_nat].
  split; [split; [|constructor]|].
  { apply pjs0_garr8_of_aview; [repeat constructor; lia|]. intros j Hj. cbn [length] in Hj.
    assert (j = 0%nat) by lia. subst j. cbn [nth Z.of_nat]. rewrite Z.add_0_r. exact L0. }
  split; [rewrite LV; lia|].
  split; [pose proof (@YM05.alloc_ceiling_value rc) as [[ACm _] _]; rewrite LV; lia|].
  split; [lia|].
  split; [unfold YGcfStr.amem_range8; left; apply Z.leb_le; vm_compute; reflexivity|].
  split.
  { intros x Hx. assert (Ex : x = PJS_LIT) by lia. subst x. exists 1. split.
    - unfold shadow_of_addr. exact LSH.
    - right. rewrite LV. lia. }
  split.
  { intros s Hs. unfold shadow_addr in Hs. rewrite LV in Hs. unfold SHADOW_OFF in Hs.
    assert (Es : shadow_addr ((s - SHADOW_OFF) * 8) = s).
    { unfold shadow_addr. rewrite Z.div_mul by lia. lia. }
    rewrite <- Es. apply (GL3 ly S Hp W m md _ HAR). rewrite CI, CT. unfold SHADOW_OFF in *. lia. }
  intros a Ha. apply LTL. rewrite LV in Ha |- *. lia.
- right; right. unfold kept_img. change (@pa_lo _ _ PA) with IMG_LO_B. change (@pa_hi _ _ PA) with IMG_TOP_B.
  rewrite CI, CT, LV. split; [lia|]. split; [lia|].
  intros a Ha. rewrite <- LV in Ha. assert (Ea : a = PJS_LIT) by lia. subst a.
  split; [apply LRO; lia|]. split; [exact Hno|]. split; [exact Her|].
  right. exists 1. split; [exact GL2 | right; rewrite LV; lia].
Qed.

Theorem pjs_seg_entry_holds : forall CTX0,
  pjs_texts (SK := SK) B ARx -> pjs_g_lit B -> pjs_g_lit_sh ARx -> pjs_seg_C1 (SK := SK) B ARx CTX0 ->
  pjs_seg_entry (SK := SK) B ARx CTX0.
Proof.
intros CTX0 HTX HLIT HSH HC1 en HPRE HCNT. pose proof HPRE as HPRE0.
destruct HTX as (AMSET & _).
pose proof (pjs_pre_v B ARx LAWS CTX0 en HPRE) as (HPL & Hv4096 & Hv56 & Hv8 & Hvamr & Hvimg & Hvpst & _).
destruct en as [ly S Hp W regs mem md ch d v s cs Lam peak cnt fail ran most own rpsm rpx rpos rpi rpH0 rphist].
unfold pjs_place in HPL. unfold js_len, js_sp1, js_sp0 in *.
cbn [js_ly js_S js_Hp js_W js_regs js_mem js_md js_ch js_d js_v js_s js_cs js_Lam js_peak js_cnt js_fail js_ran js_most js_own] in *.
set (en := MkPjsEnt ly S Hp W regs mem md ch d v s cs Lam peak cnt fail ran most own rpsm rpx rpos rpi rpH0 rphist) in *.
unfold pjs_pre in HPRE. cbv zeta in HPRE.
cbn [js_ly js_S js_Hp js_W js_regs js_mem js_md js_ch js_d js_v js_s js_cs js_Lam js_peak js_cnt js_fail js_ran js_most js_own en]
  in HPRE.
destruct HPRE as (HFPRE & HUNIV & HROOM & HRP & _ & H10 & H11 & HFWIN & HSLOT & HCEIL & HWIDE & HSCASE & HMAX & HLED &
  HLIVE).
pose proof HFPRE as (HAFN & HROD & HSTKHI).
pose proof HAFN as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof HFWIN as (Hd0 & Hd16 & Hdtop & Hdpres).
pose proof HSLOT as (_ & _ & Hrw & _ & _ & Hvra & Hvhull).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof (@alloc_ceiling_lt rc) as ACL.
assert (Hs64 : 0 <= s < 2 ^ 64)
  by (destruct HSCASE as [(-> & _) | (_ & (_ & Hs4 & Hs5 & _) & _)]; lia).
pose proof cf_head_nonneg as Hh0. pose proof HWIDE as Hh8. unfold prh_head_wide in Hh8.
assert (HSTK : 4128 <= STK_pj_string) by (apply Z.leb_le; vm_compute; reflexivity).
assert (Hes : ESTACK = 4096) by reflexivity.
pose proof (@pa_segs_low _ B_prog_listing PA) as Hsegs.
set (sp0 := spZ regs) in *.
(* the harness heads miss v's 56 bytes (v's place; 8 <= cf_head for v in a harness block's own user bytes) *)
assert (HHD : forall a k i, In (a, k) Lam -> 0 <= i < 8 -> ~ (v <= a - cf_head + i < v + 56)).
{ intros a k i Hin Hi Hx.
  destruct (prh_ledger_hblock B ly S Hp W mem Lam peak cnt fail ran a k most own HLED Hin) as (Hk & Hab & _).
  assert (R : 1 <= req_size (k + cf_head) /\ k + cf_head <= req_size (k + cf_head)) by (apply req_size_pos; lia).
  destruct HPL as [(a0 & k0 & Hin0 & Ha0 & Hk0') | [(b & m & Hin1 & Hnl & Hb & Hm) | (cid & pos & Hin2 & Hf & Hfm)]].
  - destruct (Z.eq_dec a a0) as [-> | Hne]; [lia|].
    destruct (prh_ledger_hblock B ly S Hp W mem Lam peak cnt fail ran a0 k0 most own HLED Hin0) as (Hkk0 & Hab0 & _).
    assert (R0 : 1 <= req_size (k0 + cf_head) /\ k0 + cf_head <= req_size (k0 + cf_head)) by (apply req_size_pos; lia).
    assert (Hne' : (a - cf_head, k + cf_head) <> (a0 - cf_head, k0 + cf_head)) by (intros E; injection E as E1 _; lia).
    pose proof (sep_blocks_x SEGS B ARx LAWS ly S Hp W mem md _ _ _ _ HAR Hab Hab0 Hne') as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
  - assert (Hne' : (a - cf_head, k + cf_head) <> (b, m)).
    { intros E. injection E as E1 E2. apply Hnl. rewrite <- E1, <- E2.
      replace (a - cf_head + cf_head) with a by lia. replace (k + cf_head - cf_head) with k by lia. exact Hin. }
    pose proof (sep_blocks_x SEGS B ARx LAWS ly S Hp W mem md _ _ _ _ HAR Hab Hin1 Hne') as Hd.
    assert (Rm : 1 <= req_size m /\ m <= req_size m) by (apply req_size_pos; lia).
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
  - pose proof (sep_block_frame_x SEGS B ARx LAWS ly S Hp W mem md _ _ cid pos HAR Hab Hin2) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
pose proof (ajournal_x_init_W (SK := SK) SEGS B PST ARx STK_pj_string d [(v, v + 56)] ly S Hp W regs mem md ch
  HAFN HFWIN) as HJ.
(* ======== seat 0 ======== *)
remember (@Eimg _ B_prog_listing PA (Ereg regs [Z_to_bv 64 SHADOW_OFF])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs [Z_to_bv 64 SHADOW_OFF]) n)
  by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (Er : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs r).
{ intros n r Hn Hr. rewrite EL by (unfold A_TEXT; lia). exact (ew_Ereg_nat regs _ n r Hr). }
assert (E2 : ew E 2 = getr regs 2) by (apply Er; [lia | reflexivity]).
assert (E10 : ew E 10 = Z_to_bv 64 v) by (rewrite (Er 10%nat 10%bv) by (first [lia | reflexivity]); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 s) by (rewrite (Er 11%nat 11%bv) by (first [lia | reflexivity]); exact H11).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (Usp : bv_unsigned (ew E 2) = sp0) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 SHADOW_OFF]) E)
  by (subst E; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (Uimg : forall j, (A_TEXT <= j < A_LIM)%nat -> bv_unsigned (ew E j) = VAL j).
{ intros j Hj. subst E. rewrite Eimg_img by exact Hj. apply unsigned_lit_small. apply pa_val_range. }
assert (Di : forall j, (A_TEXT <= j < A_LIM)%nat -> sv_denot E (SOff j 0) = Z_to_bv 64 (VAL j)).
{ intros j Hj. cbn [sv_denot]. rewrite Uimg by exact Hj. rewrite Z.add_0_r. reflexivity. }
assert (Ur : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> U E (SOff n 0) = bv_unsigned (getr regs r)).
{ intros n r Hn Hr. rewrite U_SOff, (Er n r Hn Hr), Z.add_0_r. apply zcanon_id.
  pose proof (bv_unsigned_in_range 64 (getr regs r)) as Rr. unfold bv_modulus in Rr. unfold M64. exact Rr. }
destruct (alx_const SEGS B ARx LAWS ly S Hp W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B PAL), (pal_cell B PAL) in Kgot. rewrite (pal_cell B PAL) in Kcell.
assert (HS : st_ok_pi SEGS VAL E ss_pjs0
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + PJS_PC)) mem (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_pjs0. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold pjs0_frame, got_regionP, bcell_regionP.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
    rewrite ?Uimg by (unfold A_OBJ, A_TEXT, A_LIM; lia).
    + rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros q Hq. apply (apresent_writable SEGS). apply Hpres. lia.
    + pose proof (@pa_val_range _ B_prog_listing PA (A_OBJ 0)). pose proof (@pa_val_range _ B_prog_listing PA (A_OBJ 12)).
      split; [lia|]. split; [apply Z.leb_le; vm_compute; reflexivity|]. split; [intros q Hq; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ _ 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
        [apply Di; unfold A_OBJ, A_TEXT, A_LIM; lia | lia | lia |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
    + pose proof (@pa_val_range _ B_prog_listing PA (A_OBJ 12)).
      split; [lia|]. split; [apply Z.leb_le; vm_compute; reflexivity|]. split; [intros q Hq; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ _ 0 8 (SOff 32 0) SHADOW_OFF);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, unsigned_lit_small by (unfold SHADOW_OFF; lia); reflexivity
        | unfold SHADOW_OFF; lia | lia |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
  - apply pairwise_disjoint_of_extents.
    unfold pjs0_frame, got_regionP, bcell_regionP, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp.
    rewrite !Uimg by (unfold A_OBJ, A_TEXT, A_LIM; lia).
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    assert (VG : VAL (A_OBJ 0) < 2 ^ 40) by (apply Z.ltb_lt; vm_compute; reflexivity).
    assert (VC : VAL (A_OBJ 12) < 2 ^ 40) by (apply Z.ltb_lt; vm_compute; reflexivity).
    pose proof (@pa_val_range _ B_prog_listing PA (A_OBJ 0)). pose proof (@pa_val_range _ B_prog_listing PA (A_OBJ 12)).
    pose proof (pal_got_cell B PAL) as HgcD.
    repeat split; lia.
  - split; [|split; [exact I | apply B_alias_hints_ok; exact HEI]].
    unfold pjs0_facts0. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E32, unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; try lia. }
assert (SHOK : sh_ok SEGS PJS0_Bx0 [] E (mrestrict (w_H W) mem)) by constructor.
clear HE EL.
unfold cfg_at. change (w64 (SIGMA AS_pj_string)) with (Z_to_bv 64 (BASE + PJS_PC)).
(* the memnorm keep from the entry memory, the runners' memory invariant (YSRrMemnorm.v's instance) *)
pose (PMN := fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m).
pose proof (YSRrMemnorm.srr_inv_laws_imp SEGS _ mem (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS)) as PLAW.
fold PMN in PLAW.
assert (HPM : PMN (ms_mem (mkst regs (Z_to_bv 64 (BASE + PJS_PC)) mem (seg_rom SEGS)))) by (intros h; exact h).
pose (RUN := @paj_run_x_inv fx rc SK B_prog_listing PL PA B PST ARx cf_head LAWS PMN PLAW).
(* ---- seat 0's run: +0x00 .. the `jal __asan_memset` ---- *)
paj_run_tok_x_inv RUN HS HJ SHOK HPM PJS0_Bspan;
  [apply (pjs0_awr0 E STK_pj_string sp0 d); [exact Usp | lia | exact Hd0] |].
clear HF. rename HG into G1.
pose proof (pjs0_keep0 W E mem _ sp0 Usp HFr) as K1. clear HFr.
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
prreg HS (12%bv : bv 5) Q12. prreg HS (18%bv : bv 5) Q18.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?r _ ?m _) _) _ => set (m1 := m) in *; set (r1 := r) in * end.
(* the four saved words *)
assert (VRA : val_mem SEGS (mrestrict (w_H W) m1) (sp0 - 32 + 24) 8 (raZ regs)).
{ refine (pjs0_val_st E _ _ 2 (-8) 8 (SOff 1 0) _ sp0 _ HS _ Usp _ _ _ _).
  - vm_compute. reflexivity.
  - lia.
  - exact (Ur 1%nat 1%bv ltac:(lia) eq_refl).
  - lia.
  - pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Rr. unfold bv_modulus in Rr. unfold raZ. cbn in Rr |- *. lia. }
assert (VS0 : val_mem SEGS (mrestrict (w_H W) m1) (sp0 - 32 + 16) 8 (s0Z regs)).
{ refine (pjs0_val_st E _ _ 2 (-16) 8 (SOff 8 0) _ sp0 _ HS _ Usp _ _ _ _).
  - vm_compute. reflexivity.
  - lia.
  - exact (Ur 8%nat 8%bv ltac:(lia) eq_refl).
  - lia.
  - pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Rr. unfold bv_modulus in Rr. unfold s0Z. cbn in Rr |- *. lia. }
assert (VS1 : val_mem SEGS (mrestrict (w_H W) m1) (sp0 - 32 + 8) 8 (bv_unsigned (getr regs 9))).
{ refine (pjs0_val_st E _ _ 2 (-24) 8 (SOff 9 0) _ sp0 _ HS _ Usp _ _ _ _).
  - vm_compute. reflexivity.
  - lia.
  - exact (Ur 9%nat 9%bv ltac:(lia) eq_refl).
  - lia.
  - pose proof (bv_unsigned_in_range 64 (getr regs 9)) as Rr. unfold bv_modulus in Rr. cbn in Rr |- *. lia. }
assert (VS2 : val_mem SEGS (mrestrict (w_H W) m1) (sp0 - 32) 8 (bv_unsigned (getr regs 18))).
{ refine (pjs0_val_st E _ _ 2 (-32) 8 (SOff 18 0) _ sp0 _ HS _ Usp _ _ _ _).
  - vm_compute. reflexivity.
  - lia.
  - exact (Ur 18%nat 18%bv ltac:(lia) eq_refl).
  - lia.
  - pose proof (bv_unsigned_in_range 64 (getr regs 18)) as Rr. unfold bv_modulus in Rr. cbn in Rr |- *. lia. }
assert (HK1 : forall r, In r PJS_KEPT -> getr r1 r = getr regs r).
{ exact (regs_kept_of_st_ok SEGS E _ _ regs [Z_to_bv 64 SHADOW_OFF] PJS_KEPT HS HAE
    ltac:(vm_compute; reflexivity)). }
assert (Hsp1 : spZ r1 = sp0 + d + (-32 - d)).
{ unfold YG0d.spZ at 1. rewrite Q2, Usp. rewrite unsigned_lit_small by lia. lia. }
(* v's shadow at the call: the entry's (the run wrote the frame only) *)
assert (KSH1 : forall t, kLowMemEnd <= t < kHighShadowEnd -> aview SEGS (w_H W) m1 t = aview SEGS (w_H W) mem t).
{ intros t Ht. apply K1; lia. }
(* ======== +0x30: memset (v, 0, 56) ======== *)
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rT _ ?mT _) _) _ =>
  eapply (YGcallMxmn.aj_intrin_at_xm_fr (SK := SK) SEGS B PST ARx LAWS Hsegs OSet (SIGMA AS___asan_memset) AMSET
    W rT mT (STK_pj_string + d) (sp0 + d) [(v, v + 56)] ly S Hp W mem md [] ly S Hp _ 0 v 0 56 (-32 - d) _ HJ)
  end.
  - rewrite Q10, E10. reflexivity.
  - rewrite Q11. reflexivity.
  - rewrite Q12. reflexivity.
  - lia.
  - lia.
  - lia.
  - exact Hsp1.
  - lia.
  - lia.
  - rewrite Hes. lia.
  - rewrite Q3, (Er 3%nat 3%bv) by (first [lia | reflexivity]). exact Hgp.
  - rewrite Q4, (Er 4%nat 4%bv) by (first [lia | reflexivity]). exact Htp.
  - exact Q1.
  - apply (ret_ok_codeptr_v (PI := PA)); [lia | reflexivity].
  - intros a Ha. split.
    + destruct HPL as [(a0 & k0 & Hin0 & Ha0 & Hk0) | [(b & m & Hin1 & _ & Hb & Hm) | (cid & pos & Hin2 & Hf & Hfm)]].
      * destruct (prh_ledger_hblock B ly S Hp W mem Lam peak cnt fail ran a0 k0 most own HLED Hin0) as (Hk0' & Hab & _).
        assert (Rq : 1 <= req_size (k0 + cf_head) /\ k0 + cf_head <= req_size (k0 + cf_head))
          by (apply req_size_pos; lia).
        left. right. left. split; [exists (v, v + 56); split; [left; reflexivity | cbn [fst snd]; lia]|].
        exists (a0 - cf_head), (k0 + cf_head). split; [exact Hab | lia].
      * assert (Rm : 1 <= req_size m /\ m <= req_size m) by (apply req_size_pos; lia).
        left. right. left. split; [exists (v, v + 56); split; [left; reflexivity | cbn [fst snd]; lia]|].
        exists b, m. split; [exact Hin1 | lia].
      * right. split; [exists (v, v + 56); split; [left; reflexivity | cbn [fst snd]; lia]|].
        exists cid, pos. split; [exact Hin2|]. unfold in_zr, frame_rng; cbn [fst snd]. lia.
    + rewrite Hes. lia.
  - exact Hvamr.
  - eapply range_addressable_agree; [|exact Hvra]. intros x Hx.
    pose proof (shadow_addr_bounds x ltac:(lia)) as Hsx. unfold shadow_addr in Hsx. unfold shadow_of_addr.
    apply KSH1. exact Hsx.
  - intros _ t Ht. pose proof (pjs0_hull_bounds v 56 t ltac:(lia) ltac:(lia) ltac:(lia) Ht) as Htb.
    rewrite KSH1 by exact Htb. exact (Hvhull t Ht).
  - exact I. }
cbv beta. intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & HP4 & Ha04 & Heff & Hfr4 & Hpres4 & HMN4).
assert (HPM4 : PMN mem4) by (intros h; exact (HMN4 (HPM h))).
cbv beta iota in Heff.
lazymatch goal with |- SRr _ _ (mkCfg (mkst _ ?p _ _) _) _ =>
  replace p with (Z_to_bv 64 (BASE + PJS_M1)) by (apply bv_eq; vm_compute; reflexivity) end.
(* the registers memset keeps *)
assert (R4 : forall r, In r PJS0_KR -> getr regs4 r = getr r1 r).
{ intros r Hr. cbv [PJS0_KR In] in Hr.
  repeat match type of Hr with _ \/ _ => destruct Hr as [Hr | Hr] | False => destruct Hr | _ = _ => subst r end;
  (apply pjs0_pres; [exact HP4 | pjs0_cs]). }
assert (G4 : mem_grows (mrestrict (w_H W) m1) (mrestrict (w_H W) mem4)) by exact (pjs0_grows_of_apresent _ _ _ Hpres4).
(* ======== seat 1 ======== *)
set (E1 := @Eimg _ B_prog_listing PA (Ereg regs4 [])).
assert (HEI1 : img_env VAL A_LIM E1) by (unfold E1; apply Eimg_env).
assert (HAE1 : env_agree 32 (Ereg regs4 []) E1)
  by (unfold E1; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (Er1 : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E1 n = getr regs4 r).
{ intros n r Hn Hr. unfold E1. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat regs4 _ n r Hr). }
assert (V48 : getr regs4 8 = Z_to_bv 64 v) by (rewrite (R4 8%bv) by (cbn; tauto); rewrite Q8; exact E10).
assert (V49 : getr regs4 9 = Z_to_bv 64 s) by (rewrite (R4 9%bv) by (cbn; tauto); rewrite Q9; exact E11).
assert (V418 : getr regs4 18 = Z_to_bv 64 SHADOW_OFF) by (rewrite (R4 18%bv) by (cbn; tauto); rewrite Q18; exact E32).
assert (V42 : spZ regs4 = sp0 - 32).
{ unfold YG0d.spZ at 1. rewrite (R4 2%bv) by (cbn; tauto). unfold YG0d.spZ in Hsp1. lia. }
assert (HK4 : forall r, In r PJS_KEPT -> getr regs4 r = getr regs r).
{ intros r Hr. rewrite (R4 r (pjs0_cs_of_list r Hr)). exact (HK1 r Hr). }
assert (Uv1 : bv_unsigned (ew E1 8) = v) by (rewrite (Er1 8%nat 8%bv) by (first [lia | reflexivity]); rewrite V48; apply unsigned_lit_small; lia).
assert (Ush1 : bv_unsigned (ew E1 18) = SHADOW_OFF)
  by (rewrite (Er1 18%nat 18%bv) by (first [lia | reflexivity]); rewrite V418; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
(* the memory after memset against the entry's *)
assert (KALL4 : forall a, 0 <= a < 2 ^ 64 -> ~ (v <= a < v + 56) -> ~ (sp0 - 32 - 4096 <= a < sp0) ->
  aview SEGS (w_H W) mem4 a = aview SEGS (w_H W) mem a).
{ intros a Ha H1 H2. rewrite Hfr4, K1 by (rewrite ?Hes; lia). reflexivity. }
assert (MG4 : mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem4)) by (intros x Hx; apply G4, G1, Hx).
assert (HVRA4 : range_addressable (aview SEGS (w_H W) mem4) SHADOW_OFF v 56).
{ eapply range_addressable_agree; [|exact Hvra]. intros x Hx.
  pose proof (shadow_addr_bounds x ltac:(lia)) as Hsx. unfold shadow_addr in Hsx. unfold shadow_of_addr.
  apply KALL4; [lia | intros Ho; unfold amem_range in Hvamr; lia | lia]. }
assert (HS1 : st_ok_pi SEGS VAL E1 ss_pjs1
  (restrict (w_H W) (mkst regs4 (Z_to_bv 64 (BASE + PJS_M1)) mem4 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_pjs1. apply pa_entry_st_ok_full.
  - unfold E1. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold region_ok, pjs0_vreg.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Uv1.
    split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (writable_at_grows SEGS _ _ _ MG4). apply (proj2 Hrw). lia.
  - cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
  - split; [|split; [exact I | exact I]].
    cbn [pjs0_facts1 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Uv1, Ush1. change (2 ^ 3) with 8. rewrite Z.pow_0_r, Z.mod_1_r.
    unfold SHADOW_OFF. repeat split; lia. }
assert (SHOK1 : sh_ok SEGS PJS0_Bx1 PJS0_SH1 E1 (mrestrict (w_H W) mem4)).
{ unfold sh_ok, PJS0_SH1. constructor; [|constructor]. unfold shent_ok, app_apart. cbn [she_m she_lo she_hi].
  assert (UB : U E1 PJS0_Bx1 = SHADOW_OFF).
  { unfold PJS0_Bx1. apply (U_atom E1 18 SHADOW_OFF); [rewrite (Er1 18%nat 18%bv) by (first [lia | reflexivity]); exact V418 | unfold SHADOW_OFF; lia]. }
  assert (UV : U E1 (SOff 8 0) = v) by (apply (U_atom E1 8 v); [rewrite (Er1 8%nat 8%bv) by (first [lia | reflexivity]); exact V48 | lia]).
  rewrite UB, UV. split.
  - replace (v + 0) with v by lia. replace (56 - 0) with 56 by lia. exact HVRA4.
  - intros a Ha. unfold amem_range in Hvamr. unfold SHADOW_OFF, kLowMemEnd, kHighMemBeg, kHighMemEnd in *. lia. }
clear HS HJ SHOK HPM. rename HS1 into HS. rename HJ4 into HJ. rename SHOK1 into SHOK. rename HPM4 into HPM.
pose (RUNF := @paj_run_xf_inv fx rc SK B_prog_listing PL PA B PST ARx cf_head LAWS PMN PLAW).
(* ---- seat 1's run: the checks, the type store; stop at the `bnez s1` ---- *)
paj_run_tok_x_inv RUNF HS HJ SHOK HPM PJS0_Bspan.
{ intros a (r & Hin & Hr). cbn [ss_pjs1 ss_mem In] in Hin. destruct Hin as [<- | []].
  cbn [pjs0_vreg YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite Uv1 in Hr.
  assert (HFP : inFP [(v, v + 56)] a) by (exists (v, v + 56); split; [left; reflexivity | cbn [fst snd]; lia]).
  destruct HPL as [(a0 & k0 & Hin0 & Ha0 & Hk0) | [(b & m & Hin1 & _ & Hb & Hm) | (cid & pos & Hin2 & Hf & Hfm)]].
  - destruct (prh_ledger_hblock B ly S Hp W mem Lam peak cnt fail ran a0 k0 most own HLED Hin0) as (Hk0' & Hab & _).
    assert (Rq : 1 <= req_size (k0 + cf_head) /\ k0 + cf_head <= req_size (k0 + cf_head)) by (apply req_size_pos; lia).
    left. right; left. split; [exact HFP|]. exists (a0 - cf_head), (k0 + cf_head). split; [exact Hab | lia].
  - assert (Rm : 1 <= req_size m /\ m <= req_size m) by (apply req_size_pos; lia).
    left. right; left. split; [exact HFP|]. exists b, m. split; [exact Hin1 | lia].
  - right. split; [exact HFP|]. exists cid, pos. split; [exact Hin2|].
    unfold in_zr, frame_rng. cbn [fst snd]. lia. }
clear HF. rename HG into G2.
pose proof (pjs0_keep1 W E1 mem4 _ v Uv1 HFr) as K2. clear HFr.
pmkst HS.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?r _ ?m _) _) _ => set (m58 := m) in *; set (regs58 := r) in * end.
assert (VTY : val_mem SEGS (mrestrict (w_H W) m58) v 4 4).
{ refine (pjs0_val E1 _ _ 8 0 4 (SLit 4) 4 v v HS _ Uv1 _ _ _ _).
  - vm_compute. reflexivity.
  - lia.
  - rewrite U_SLit. reflexivity.
  - lia.
  - cbn. lia. }
assert (R58 : forall r, In r PJS0_KR -> getr regs58 r = getr regs4 r)
  by exact (regs_kept_of_st_ok_pi (PI := PA) E1 _ _ regs4 [] PJS0_KR HS HAE1 ltac:(vm_compute; reflexivity)).
(* ---- the memory at the branch against the entry's ---- *)
assert (KALL : forall a, 0 <= a < 2 ^ 64 -> ~ (v <= a < v + 56) -> ~ (sp0 - 32 - 4096 <= a < sp0) ->
  aview SEGS (w_H W) m58 a = aview SEGS (w_H W) mem a).
{ intros a Ha H1 H2. rewrite K2 by lia. exact (KALL4 a Ha H1 H2). }
assert (MG58 : mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) m58)) by (intros x Hx; apply G2, MG4, Hx).
assert (KFR : forall x, sp0 - 32 <= x < sp0 -> aview SEGS (w_H W) m58 x = aview SEGS (w_H W) m1 x).
{ intros x Hx. rewrite K2 by lia. rewrite Hfr4 by (rewrite ?Hes; lia). reflexivity. }
assert (VRA5 : val_mem SEGS (mrestrict (w_H W) m58) (sp0 - 32 + 24) 8 (raZ regs))
  by (apply (pjs1_val_keep W W m1 m58 _ 8 _ VRA); intros x Hx; apply KFR; change (Z.of_nat 8) with 8 in Hx; lia).
assert (VS05 : val_mem SEGS (mrestrict (w_H W) m58) (sp0 - 32 + 16) 8 (s0Z regs))
  by (apply (pjs1_val_keep W W m1 m58 _ 8 _ VS0); intros x Hx; apply KFR; change (Z.of_nat 8) with 8 in Hx; lia).
assert (VS15 : val_mem SEGS (mrestrict (w_H W) m58) (sp0 - 32 + 8) 8 (bv_unsigned (getr regs 9)))
  by (apply (pjs1_val_keep W W m1 m58 _ 8 _ VS1); intros x Hx; apply KFR; change (Z.of_nat 8) with 8 in Hx; lia).
assert (VS25 : val_mem SEGS (mrestrict (w_H W) m58) (sp0 - 32) 8 (bv_unsigned (getr regs 18)))
  by (apply (pjs1_val_keep W W m1 m58 _ 8 _ VS2); intros x Hx; apply KFR; change (Z.of_nat 8) with 8 in Hx; lia).
assert (V58 : garr8 SEGS (mrestrict (w_H W) m58) v (pjs_bytes 0)).
{ apply pjs0_garr8_of_aview; [exact (pjs_bytes_range 0)|]. intros j Hj. rewrite pjs_bytes_len in Hj.
  rewrite pjs_bytes_nth by exact Hj.
  destruct (Nat.ltb_spec j 4) as [Hj4 | Hj4].
  - rewrite (pjs0_aview_of_val _ _ _ 4 4 j VTY Hj4).
    do 4 (destruct j as [|j]; [vm_compute; reflexivity|]). lia.
  - rewrite K2 by lia. rewrite (Heff (Z.of_nat j)) by lia.
    replace ((j =? 0)%nat) with false by (symmetry; apply Nat.eqb_neq; lia).
    destruct ((16 <=? j)%nat && (j <? 24)%nat); [rewrite pjs_le_byte_0|]; reflexivity. }
(* ---- C1 from any state the branch arms reach: the memory of the branch, the registers given ---- *)
assert (Q58 : forall regsF memF mdF kF,
  AJ (STK_pj_string + d) (sp0 + d) [(v, v + 56)] ly S Hp W mem md [] ly S Hp W memF mdF kF ->
  (forall x, mrestrict (w_H W) memF x = mrestrict (w_H W) m58 x) -> PMN memF ->
  spZ regsF = sp0 - 32 -> getr regsF 8 = w64 v -> getr regsF 18 = w64 SHADOW_OFF ->
  (forall r, In r PJS_KEPT -> getr regsF r = getr regs r) -> getr regsF 10 = w64 (pjs_sarg s) ->
  pjs_C1 (SK := SK) B ARx en regsF memF mdF kF).
{ intros regsF memF mdF kF HJF EQ HPMF HspF H8F H18F HKF H10F.
  assert (AV : forall a, aview SEGS (w_H W) memF a = aview SEGS (w_H W) m58 a)
    by (intros a; unfold aview, mbyte; rewrite EQ; reflexivity).
  assert (KF : forall a, 0 <= a < 2 ^ 64 -> ~ (v <= a < v + 56) -> ~ (sp0 - 32 - 4096 <= a < sp0) ->
    aview SEGS (w_H W) memF a = aview SEGS (w_H W) mem a) by (intros a H1 H2 H3; rewrite AV; exact (KALL a H1 H2 H3)).
  assert (MGF : mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) memF))
    by (intros x Hx; rewrite EQ; exact (MG58 x Hx)).
  assert (KM : forall a l, garr8 SEGS (mrestrict (w_H W) m58) a l -> garr8 SEGS (mrestrict (w_H W) memF) a l)
    by (intros a l Hg; apply (pjs1_garr8_keep W W m58 memF a l Hg); intros x _; exact (AV x)).
  assert (KV : forall a n x, val_mem SEGS (mrestrict (w_H W) m58) a n x -> val_mem SEGS (mrestrict (w_H W) memF) a n x)
    by (intros a n x Hv; apply (pjs1_val_keep W W m58 memF a n x Hv); intros y _; exact (AV y)).
  assert (VBF : garr8 SEGS (mrestrict (w_H W) memF) v (pjs_bytes 0)) by exact (KM _ _ V58).
  pose proof (ajx_ar HJF) as HARF. pose proof (ajx_pres HJF) as HpresF.
  assert (RODF : arodata_okP SEGS RLO RHI B (aview SEGS (w_H W) memF)).
  { intros a Hro Hno Herr.
    assert (Hi : in_img SEGS a).
    { destruct Hro as [(sg & Hin & _ & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr] | exact (@pa_relro_img _ _ PA a Hr)]. }
    pose proof (Hsegs a Hi) as Hlo.
    rewrite KF; [exact (HROD a Hro Hno Herr) | lia | intros Ho; exact (Hvimg a Ho Hi) | lia]. }
  assert (KSHF : forall t, kLowMemEnd <= t < kHighShadowEnd -> aview SEGS (w_H W) memF t = aview SEGS (w_H W) mem t).
  { intros t Ht. apply KF; [lia | intros Ho; unfold amem_range in Hvamr; lia | lia]. }
  assert (HSTR : cstr_ok (PA := PA) W memF (pjs_sarg s) cs /\
    kept_at (PA := PA) B Lam (pjs_sarg s) (Z.of_nat (length cs) + 1)).
  { destruct HSCASE as [(Hs0 & Hcs) | (Hsn & HCS & HKA & HAP)].
    - subst s cs. unfold pjs_sarg. rewrite Z.eqb_refl.
      exact (pjs0_lit_ok ly S Hp W memF mdF Lam HLIT HSH HARF RODF).
    - unfold pjs_sarg. destruct (Z.eqb_spec s 0) as [Es | _]; [contradiction|].
      split; [|exact HKA].
      pose proof HCS as HCS0.
      destruct HCS as ((Hg & Hnz) & Hs4096 & Hsceil & Hslen & Hsam8 & Hsra & Hshull & Hstail).
      assert (KS : forall x, s <= x < s + Z.of_nat (length cs) + 1 -> aview SEGS (w_H W) memF x = aview SEGS (w_H W) mem x)
        by (intros x Hx; apply KF; lia).
      split; [split; [|exact Hnz]|].
      { apply (pjs1_garr8_keep W W mem memF s _ Hg). rewrite length_app. cbn [length].
        intros x Hx. apply KS. lia. }
      split; [exact Hs4096|]. split; [exact Hsceil|]. split; [exact Hslen|]. split; [exact Hsam8|].
      split.
      { eapply range_addressable_agree; [|exact Hsra]. intros x Hx.
        pose proof (shadow_addr_bounds x ltac:(lia)) as Hsx. unfold shadow_addr in Hsx. unfold shadow_of_addr.
        apply KSHF. exact Hsx. }
      split.
      { intros t Ht. rewrite KSHF; [exact (Hshull t Ht)|].
        exact (pjs0_hull_bounds s (Z.of_nat (length cs) + 1) t ltac:(lia) ltac:(lia) ltac:(lia) Ht). }
      (* the NUL's aligned word tail lies below alloc_ceiling: the kit's cstr_ok_tail_lt (the ceiling is p + len + 1) *)
      intros a Ha. pose proof (cstr_ok_tail_lt W mem s cs a HCS0 Ha) as Hta.
      destruct (Z_le_dec v a) as [Hva | Hva]; [destruct (Z_lt_dec a (v + 56)) as [Hva' | Hva']|].
      + apply (pjs0_aview_some _ _ v (pjs_bytes 0) a VBF). rewrite pjs_bytes_len. lia.
      + rewrite KF; [exact (Hstail a Ha) | lia | lia | lia].
      + rewrite KF; [exact (Hstail a Ha) | lia | lia | lia]. }
  destruct HSTR as (HSTR & HKAT).
  subst en. unfold pjs_C1, pjs_inv. unfold js_len, js_sp1, js_sp0.
  cbn [js_ly js_S js_Hp js_W js_regs js_mem js_md js_ch js_d js_v js_s js_cs js_Lam js_peak js_cnt js_fail js_ran js_most js_own].
  fold sp0. unfold PJS_FR.
  split.
  { split; [exact HJF|].
    split; [intros a Ha; apply KF; lia|].
    split; [exact HspF|].
    split; [exact (KV _ _ _ VRA5)|]. split; [exact (KV _ _ _ VS05)|].
    split; [exact (KV _ _ _ VS15)|]. split; [exact (KV _ _ _ VS25)|].
    split; [exact H8F|]. split; [exact H18F|]. split; [exact HKF|].
    split; [intros a Ha; apply HpresF; lia|].
    split; [exact RODF|]. split; [exact VBF|].
    split; [intros a Ha; exact (writable_at_grows SEGS _ _ a MGF (proj2 Hrw a Ha))|].
    split.
    { eapply range_addressable_agree; [|exact Hvra]. intros x Hx.
      pose proof (shadow_addr_bounds x ltac:(lia)) as Hsx. unfold shadow_addr in Hsx. unfold shadow_of_addr.
      apply KSHF. exact Hsx. }
    exact HPMF. }
  split; [exact H10F|]. split; [exact HSTR|]. split; [exact HKAT|].
  apply (prh_ledger_kept_aview B ly S Hp W mem ly S Hp W memF Lam peak cnt fail ran most own HLED).
  - intros a Ha. pose proof (pst_in_img_B a Ha) as Hi. pose proof (Hsegs a Hi) as Hlo.
    apply KF; [lia | intros Ho; exact (Hvimg a Ho Hi) | lia].
  - intros a k i Hin Hi.
    destruct (prh_ledger_hblock B ly S Hp W mem Lam peak cnt fail ran a k most own HLED Hin) as (Hk0 & Hab & _).
    destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HAR Hab) as (Hal & H4096 & Hcl & _).
    assert (Rq : 1 <= req_size (k + cf_head) /\ k + cf_head <= req_size (k + cf_head)) by (apply req_size_pos; lia).
    apply KF; [lia | exact (HHD a k i Hin Hi) | lia].
  - intros a k _ H. exact H.
  - apply Permutation_refl. }
(* ======== seat 2: the branch on s ======== *)
lazymatch goal with |- SRr _ _ (mkCfg (mkst _ ?p _ _) _) _ =>
  replace p with (Z_to_bv 64 (BASE + PJS0_BR)) by (apply bv_eq; vm_compute; reflexivity) end.
set (Ev2 := @Eimg _ B_prog_listing PA (Ereg regs58 [])).
assert (HEIv2 : img_env VAL A_LIM Ev2) by (unfold Ev2; apply Eimg_env).
assert (HAEv2 : env_agree 32 (Ereg regs58 []) Ev2)
  by (unfold Ev2; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (Erv2 : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew Ev2 n = getr regs58 r).
{ intros n r Hn Hr. unfold Ev2. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat regs58 _ n r Hr). }
assert (V59 : ew Ev2 9 = Z_to_bv 64 s)
  by (rewrite (Erv2 9%nat 9%bv) by (first [lia | reflexivity]); rewrite (R58 9%bv) by (cbn; tauto); exact V49).
assert (HSv2 : st_ok_pi SEGS VAL Ev2 ss_pjs2
  (restrict (w_H W) (mkst regs58 (Z_to_bv 64 (BASE + PJS0_BR)) m58 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_pjs2. apply pa_entry_st_ok_full.
  - unfold Ev2. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - exact I.
  - split; [exact I | split; exact I]. }
assert (SHOKv2 : sh_ok SEGS PJS0_Bx2 [] Ev2 (mrestrict (w_H W) m58)) by constructor.
clear HS SHOK. rename HSv2 into HS. rename SHOKv2 into SHOK.
pose (RUNTO := @paj_run_to_x_inv fx rc SK B_prog_listing PL PA B PST ARx cf_head LAWS PMN PLAW).
pose (BR := @paj_branch fx rc B_prog_listing PA).
(* the registers both arms keep, against the entry's *)
assert (RK : forall regsF, (forall r, In r ((2%bv : bv 5) :: (8%bv : bv 5) :: (18%bv : bv 5) :: PJS_KEPT) ->
    getr regsF r = getr regs58 r) ->
  spZ regsF = sp0 - 32 /\ getr regsF 8 = w64 v /\ getr regsF 18 = w64 SHADOW_OFF /\
  (forall r, In r PJS_KEPT -> getr regsF r = getr regs r)).
{ intros regsF HF. split; [|split; [|split]].
  - unfold YG0d.spZ at 1. rewrite (HF 2%bv) by (cbn; tauto). rewrite (R58 2%bv) by (cbn; tauto). exact V42.
  - rewrite (HF 8%bv) by (cbn; tauto). rewrite (R58 8%bv) by (cbn; tauto). exact V48.
  - rewrite (HF 18%bv) by (cbn; tauto). rewrite (R58 18%bv) by (cbn; tauto). exact V418.
  - intros r Hr. rewrite (HF r) by (right; right; right; exact Hr). rewrite (R58 r (pjs0_cs_of_list r Hr)).
    exact (HK4 r Hr). }
psrr_branch_tok RUN BR HS SHOK PJS0_Bspan2.
- (* `bnez s1` taken: s <> 0, a0 := s1 *)
  rewrite branch_ne_U, (U_atom Ev2 9 s V59 ltac:(lia)), U_SLit in Hc.
  assert (Hsn : s <> 0) by (intros E0; rewrite E0 in Hc; vm_compute in Hc; discriminate Hc).
  paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM PJS0_Bspan2 PJS_C1;
    [intros a (r & Hin & _); vm_compute in Hin; destruct Hin |].
  pose proof HFr as EQ. clear HFr HF.
  pmkst HS.
  prreg HS (10%bv : bv 5) T10.
  pose proof (regs_kept_of_st_ok_pi (PI := PA) Ev2 _ _ regs58 [] ((2%bv : bv 5) :: (8%bv : bv 5) :: (18%bv : bv 5) :: PJS_KEPT)
    HS HAEv2 ltac:(vm_compute; reflexivity)) as TK.
  destruct (RK _ TK) as (TSP & T8 & T18 & TKEPT).
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rF ?p ?mF _) ?mdF) _ =>
    replace p with (Z_to_bv 64 (BASE + PJS_C1)) by (apply bv_eq; vm_compute; reflexivity);
    refine (HC1 en rF mF mdF _ HPRE0 HCNT (Q58 rF mF mdF _ HJ _ HPM TSP T8 T18 TKEPT _)) end.
  + intros x. apply EQ. intros (r & Hin & _). vm_compute in Hin. destruct Hin.
  + rewrite T10, V59. unfold pjs_sarg. destruct (Z.eqb_spec s 0); [contradiction | reflexivity].
- (* `bnez s1` not taken: s = 0, s1 := the "" literal, a0 := s1 *)
  rewrite branch_ne_U, (U_atom Ev2 9 s V59 ltac:(lia)), U_SLit in Hc.
  assert (Hs0 : s = 0).
  { revert Hc. destruct (Z.eqb_spec s (zcanon 0)) as [E0 | E0]; intros Hc; [rewrite E0; reflexivity | discriminate Hc]. }
  paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM PJS0_Bspan2 PJS_C1;
    [intros a (r & Hin & _); vm_compute in Hin; destruct Hin |].
  pose proof HFr as EQ. clear HFr HF.
  pmkst HS.
  prreg HS (10%bv : bv 5) T10.
  pose proof (regs_kept_of_st_ok_pi (PI := PA) Ev2 _ _ regs58 [] ((2%bv : bv 5) :: (8%bv : bv 5) :: (18%bv : bv 5) :: PJS_KEPT)
    HS HAEv2 ltac:(vm_compute; reflexivity)) as TK.
  destruct (RK _ TK) as (TSP & T8 & T18 & TKEPT).
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rF ?p ?mF _) ?mdF) _ =>
    replace p with (Z_to_bv 64 (BASE + PJS_C1)) by (apply bv_eq; vm_compute; reflexivity);
    refine (HC1 en rF mF mdF _ HPRE0 HCNT (Q58 rF mF mdF _ HJ _ HPM TSP T8 T18 TKEPT _)) end.
  + intros x. apply EQ. intros (r & Hin & _). vm_compute in Hin. destruct Hin.
  + rewrite T10. subst s. unfold pjs_sarg. rewrite Z.eqb_refl. apply bv_eq. vm_compute. reflexivity.
Qed.
End e.
