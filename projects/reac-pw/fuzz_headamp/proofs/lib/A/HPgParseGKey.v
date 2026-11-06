(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the contract of the ASan strcmp interceptor (and of the one-`j` trampoline
   __interceptor_trampoline_strcmp = __wrap_strcmp that enters it), in the form of abcmp_realizes
   (projects/cgif/cgif_file_fuzzer/proofs/lib/YG0d.v) over the asan-state definitions of that proof as libreac/fuzz_grant holds
   them. The interceptor compares byte by byte up to the first index k where the bytes differ or s1's byte is 0, checks
   [s1, s1 + k + 1) and [s2, s2 + k + 1) with the READ_RANGE checks (QuickCheck below 64 bytes, else
   __asan_region_is_poisoned), calls the empty weak hook, and returns CharCmpX (-1, 0 or 1). Target-independent: every
   address comes from the layout or the registers. R1: the strings are disjoint from the callee's stack window
   [sp - 2 ESTACK, sp). R2: not stated, because this interceptor does not touch the AddrHashMap metadata (no FILE
   object). It subsumes the literal instance of libreac/fuzz_pcap lib/A/Rt/StrcmpDef.v (x = y, k = the literal's
   length, c1 = c2 = 0, result 0). *)
(* Modified by Theorem Labs, 2026-10-29: taken by path from libreac/fuzz_grant lib/Reusable/AStrcmpDef.v
   (a working branch 97c611eec86, owner a Theorem Labs lane, the text of record for the strcmp trampoline contract in
   a Theorem Labs lane's registry). Only the module paths change (fuzz_grant -> fuzz_identity); the statement is identical. The
   walk is a Theorem Labs lane's lib/A/Rt/Strcmp.v, relocated to identity's addresses separately. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_identity/lib/AStrcmpDef.v (donor image sha256 c954b804786c), with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/Reusable/AStrcmpDef.v, with its module paths changed; 324 of its 357 lines of code are new or changed and 20 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: the call-site form of lib/Reusable/YCbq.v's aj_bcmp_at (lines 2262-2310), restated
   for the strcmp wrapper's contract astrcmp_realizes of lib/Reusable/AStrcmpDef.v (fuzz_identity's text, module paths
   changed): the same journal threading through ecall_pre_at and ajournal_after_write, with the strcmp contract's
   str_meet premise and its strcmp_res result in place of bcmp's n-byte compare. The string lemmas below are new. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgStrcmp.v at afaa3cb55c1 for reac-pw/fuzz_headamp
   image A; module paths changed; the contract astrcmp_realizes is taken as the Section hypothesis STRCMP at 0x41ba0,
   for every float state, with str_meet and strcmp_res unfolded (hks_meet / hks_res name the same two texts inside
   this file); aj_strcmp_at -> hks_strcmp_at, cstr_at -> hks_cstr_at, strcmp_res_0 -> hks_res_0, cstr_at_cons /
   cstr_at_nil / str_meet_of_cstr -> hks_cstr_cons / hks_cstr_nil / hks_meet_of_cstr; the range lemmas kept as
   hks_hull_sub / hks_src_sub (range_addressable_sub and amem_range_sub are YG0v.v's and HPgBase.hd_amem_range_le);
   rl_cstr_args -> hks_cstr_args (from HPgBase.hd_cstr, with the wrapper's 2 ESTACK window); hks_blk_args,
   hks_cstr_of_garr8, hks_zbytes_inj and the call-site lemma hks_strcmp_call are new. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/A/HPgKcStr.v, with its module names changed; 433 of its 486 lines of code are new or changed and 304 lines of the source are left out. *)
(* reac-pw/fuzz_headamp: the IMAGE-INDEPENDENT lemmas of the key segment of reac_headamp_prop_parse_result's walks
   (image A lib/A/HPgParseKey.v; image B takes them as they stand): where the parse's frame, the hole, out, res and
   the errno cell lie (from the call's premises, HPgParseBase.hp_call_ok), hp_core again after a run or a wrapper
   call whose writes lie in the parse's stack window below the saved words, the hole and the errno cell, the pod's
   bytes and shadow at a cut, the two strings strcmp compares (where they first differ), and the key segment's model
   steps (Pod/Headamp.v parse_key read by the code's tests). Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI04.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YM05 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI08 YN3v YI00 YI0m YI09 YC5d YG05 YO09 YG0p.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Cursor Model Accessors Spa Headamp Strtol.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require CType.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec HPgHole HPgParseBase HPgParseGWalk.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A.Rt Require Import FMupoison.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Open Scope Z_scope.

Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {segs : list Segment}.
Variable B : asyms.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Hypothesis errno_low : api_env segs B.
Context {akey aph apad asens gotw guard : Z} {dcs : list (Z * Z)}.
Local Abbreviation pctx := (@hp_ctx segs).
Local Abbreviation call_ok := (@hp_call_ok fx rc SK segs B akey aph apad asens gotw guard dcs).
Implicit Types x : pctx.

(* ======================================= the frame ======================================= *)
Lemma hgk_layout : forall x, call_ok x -> layout_ok (hx_lyc x).
Proof.
intros x ((HJ & _) & _). pose proof HJ as (HAR & _). exact (am_layout B (hx_lyc x) (hx_Sc x) _ (proj1 HAR)).
Qed.

Lemma hgk_frame : forall x, call_ok x ->
hx_spa x mod 32 = 0 /\ hx_sp x - 0x120 < hx_spa x <= hx_sp x - 0x100 /\
hx_sp0 x - hx_STK x <= hx_sp x - T_parse_STK /\ hx_sp x <= hx_sp0 x /\ hx_sp x mod 16 = 0 /\
alloc_ceiling <= ly_stk_lo (hx_lyc x) /\ ly_stk_lo (hx_lyc x) <= hx_sp0 x - hx_STK x /\
hx_sp0 x <= ly_stk_hi (hx_lyc x) /\ ly_stk_hi (hx_lyc x) <= 2 ^ 47 /\
ly_stk_lo (hx_lyc x) + 64 <= hx_fr x /\ hx_fr x + 128 <= ly_stk_hi (hx_lyc x) /\
ly_stk_lo (hx_lyc x) mod 4096 = 0 /\ hx_sp0 x mod 16 = 0.
Proof.
intros x Hc. pose proof (hgk_layout x Hc) as LO.
destruct Hc as (HP & _).
pose proof (hd_parse_frame segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HP) as (F32 & F1 & F2 & F2' & F3 & F4 & F16 & S16).
destruct HP as (HJ & _ & _ & _ & _ & Hal & Hw1 & Hw2 & _).
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
pose proof (lo_top _ LO) as LT. unfold page_aligned in LT.
unfold hx_fr, hx_spa, hx_sp in *. rewrite Eslo, Eshi in *.
repeat split; lia.
Qed.

Lemma hgk_hstack : forall x pat, call_ok x -> length pat = 8%nat -> Forall (fun v => 0 <= v < 256) pat ->
hstack_ok (hx_lyc x) (hx_fr x) pat.
Proof.
intros x pat Hc Hl Hb. pose proof (hgk_frame x Hc) as (F32 & _ & _ & _ & _ & _ & _ & _ & _ & F5 & F6 & _).
unfold hstack_ok. rewrite Hl. change (8 * Z.of_nat 8) with 64.
split; [unfold hx_fr, hd_fr; apply Z.mod_divide in F32 as [m Hm]; [|lia]; rewrite Hm;
        replace (m * 32 + 64) with ((4 * m + 8) * 8) by lia; apply Z.mod_mul; lia|].
split; [lia|]. split; [lia|]. split; [lia | exact Hb].
Qed.

Lemma hgk_PAT_KEY_ok : length PAT_KEY = 8%nat /\ Forall (fun v => 0 <= v < 256) PAT_KEY.
Proof. split; [reflexivity|]. unfold PAT_KEY. repeat apply Forall_cons; try apply Forall_nil; lia. Qed.
Lemma hgk_PAT_DOT_ok : length PAT_DOT = 8%nat /\ Forall (fun v => 0 <= v < 256) PAT_DOT.
Proof. split; [reflexivity|]. unfold PAT_DOT. repeat apply Forall_cons; try apply Forall_nil; lia. Qed.

Lemma hgk_hole_band : forall x a, call_ok x -> hp_hole x a ->
kHighShadowBeg <= a < kHighShadowEnd /\ a < ly_stk_lo (hx_lyc x) /\ kLowMemEnd <= a /\ 0 <= a < 2 ^ 64.
Proof.
intros x a Hc Ha. pose proof (hgk_layout x Hc) as LO.
pose proof (hgk_hstack x PAT_KEY Hc (proj1 hgk_PAT_KEY_ok) (proj2 hgk_PAT_KEY_ok)) as OK.
unfold hp_hole, hx_shf in Ha.
destruct (hole_band (hx_lyc x) (hx_fr x) PAT_KEY LO OK a ltac:(change (Z.of_nat (length PAT_KEY)) with 8; lia))
  as (H1 & H2 & H3 & _ & H4).
repeat split; lia.
Qed.

(* the hole's first byte: the shadow address of hd_fr spa, 8-aligned frame object *)
Lemma hgk_shf : forall x, call_ok x -> hx_shf x = SHADOW_OFF + hx_spa x / 8 + 8 /\ hx_fr x = hx_spa x + 64.
Proof.
intros x Hc. pose proof (hgk_frame x Hc) as (F32 & _).
unfold hx_shf, hx_fr, hd_fr, shadow_addr. split; [|reflexivity].
apply Z.mod_divide in F32 as [m Hm]; [|lia]. rewrite Hm.
replace (m * 32 + 64) with ((4 * m + 8) * 8) by lia. replace (m * 32) with ((4 * m) * 8) by lia.
rewrite !Z.div_mul by lia. lia.
Qed.

(* ======================================= the call's ranges, apart ======================================= *)
Lemma hgk_out_apart : forall x j, call_ok x -> 0 <= j < 3 * (hx_cap x + 1) ->
~ (hx_sp x - T_parse_STK <= hx_O x + j < hx_sp x) /\ ~ hp_hole x (hx_O x + j) /\ ~ in_img segs (hx_O x + j) /\
(hx_R x <> 0 -> ~ (hx_R x <= hx_O x + j < hx_R x + 12)) /\ app_addr (hx_O x + j).
Proof.
intros x j Hc Hj. pose proof (hgk_frame x Hc) as (_ & _ & Fw & Fsp & _ & Fceil & Flo & _).
pose proof Hc as (HP & _ & _ & _ & _ & _ & HA).
pose proof HP as (HJ & _). pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
destruct HA as (_ & Hcap & (HO0 & HOin & _) & _ & Hoff & HR & _).
pose proof (AR_laws_ok segs B) as LAWS.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR HOin) as (_ & H4096 & Hceilb & Happ & _).
assert (Hrq : req_size (3 * (hx_cap x + 1)) = 3 * (hx_cap x + 1)) by (unfold req_size; destruct (_ =? 0) eqn:E; lia).
rewrite Hrq in Hceilb, Happ.
split; [apply Hoff; lia|].
split.
{ intros Hh. pose proof (hgk_hole_band x _ Hc Hh) as (B1 & _).
  destruct Happ as (_ & [HL | [HH1 HH2]]); unfold kLowShadowBeg, kHighShadowBeg, kHighShadowEnd, kHighMemBeg in *; lia. }
split.
{ refine (proj2 (al_client_img _ _ LAWS _ _ _ _ _ _ HAR _)). left. exists (hx_O x), (3 * (hx_cap x + 1)).
  rewrite Hrq. split; [exact HOin | lia]. }
split; [|apply (in_app_addr _ _ _ Happ); lia].
intros HR0 Hin. destruct HR as [HR|((Hwin & _) & _ & _)]; [exact (HR0 HR)|].
destruct Hwin as [Hw | (cid & pos & Hown & _ & Hf1 & Hf2)].
- lia.
- assert (Hf : In (cid, pos) (frames (hx_Sc x))) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
  pose proof (sep_block_frame segs B LAWS _ _ _ _ _ _ _ _ _ HAR HOin Hf) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Hrq in Hd. lia.
Qed.

Lemma hgk_res_apart : forall x j, call_ok x -> hx_R x <> 0 -> 0 <= j < 12 ->
~ (hx_sp x - T_parse_STK <= hx_R x + j < hx_sp x) /\ ~ hp_hole x (hx_R x + j) /\ ~ in_img segs (hx_R x + j) /\
(kHighShadowEnd <= hx_R x + j \/ app_addr (hx_R x + j)) /\ 0 <= hx_R x + j < 2 ^ 47.
Proof.
intros x j Hc HR0 Hj. pose proof (hgk_frame x Hc) as (_ & _ & Fw & Fsp & _ & Fceil & Flo & Fhi & F47 & _).
pose proof Hc as (HP & _ & _ & _ & _ & _ & HA).
pose proof HP as (HJ & _). pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
destruct HA as (_ & _ & _ & _ & _ & HR & _).
pose proof (AR_laws_ok segs B) as LAWS.
destruct HR as [HR|((Hwin & Hoff) & _ & _)]; [contradiction |].
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
split; [unfold hx_sp; lia|].
destruct Hwin as [Hw | (cid & pos & Hown & _ & Hf1 & Hf2)].
- split.
  + intros Hh. pose proof (hgk_hole_band x _ Hc Hh) as (B1 & B2 & _). lia.
  + split; [intros Hi; pose proof (segs_low _ Hi); lia|]. split; [left; lia | lia].
- assert (Hf : In (cid, pos) (frames (hx_Sc x))) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
  destruct (frames_bounds segs B LAWS _ _ _ _ _ _ _ HAR Hf) as (G1 & G2 & Gapp).
  split.
  + intros Hh. pose proof (hgk_hole_band x _ Hc Hh) as (B1 & _).
    destruct Gapp as (_ & [HL | [HH1 HH2]]); unfold kLowShadowBeg, kHighShadowBeg, kHighShadowEnd, kHighMemBeg in *; lia.
  + split; [apply (frm_img segs B LAWS _ _ _ _ _ _ _ _ HAR Hf); lia|].
    split; [right; apply (in_app_addr _ _ _ Gapp); lia | lia].
Qed.

Lemma hgk_errno_apart : forall x j, call_ok x -> 0 <= j < 4 ->
~ (hx_sp x - T_parse_STK <= as_errno B + j < hx_sp x) /\ ~ hp_hole x (as_errno B + j) /\ in_img segs (as_errno B + j) /\
0 <= as_errno B + j < kLowMemEnd.
Proof.
intros x j Hc Hj. pose proof (hgk_frame x Hc) as (_ & _ & Fw & Fsp & _ & Fceil & Flo & _).
destruct errno_low as ((E0 & E4) & Eimg & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
split; [lia|]. split; [|split; [apply Eimg; lia | lia]].
intros Hh. pose proof (hgk_hole_band x _ Hc Hh) as (_ & _ & B3 & _). lia.
Qed.

(* the saved words lie at sp - 112 .. sp - 1 *)
Lemma hgk_saved_offs : forall o r, In (o, r) HP_SAVED -> -104 <= o <= -8.
Proof.
intros o r Hin. unfold HP_SAVED in Hin.
repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; lia|]). destruct Hin.
Qed.

(* ======================================= hp_core again ======================================= *)
(* After a run or a wrapper call whose writes Wr lie in the parse's stack window below the saved words
   [sp - T_parse_STK, sp - 112), the hole and the errno cell: hp_core with the end memory's journal and pattern. *)
Lemma hgk_core_keep : forall x pat pat' cl rb regs mem md regs' mem' md' (Wr : Z -> Prop),
call_ok x -> Z.of_nat (length cl) <= hx_cap x -> Z.of_nat (length rb) <= 12 ->
hp_core B x pat cl rb regs mem md ->
hjournal segs B (hx_STK x) (hx_sp0 x) (hx_FP x) (hx_ly x) (hx_S x) (hx_W0 x) (hx_mem0 x) (hx_md0 x) (hx_own x)
  (hx_lyc x) (hx_Sc x) (hx_W x) mem' md' (hx_k x) (hx_fr x) pat' ->
same_io md md' ->
(forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> hx_view x mem' a = hx_view x mem a) ->
(forall a, Wr a -> (hx_sp x - T_parse_STK <= a < hx_sp x - 112) \/ hp_hole x a \/
  (as_errno B <= a < as_errno B + 4)) ->
(exists ev, rd32 (hx_view x mem') (as_errno B) ev) ->
getr regs' 2 = getr regs 2 -> getr regs' 8 = getr regs 8 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
getr regs' 9 = getr regs 9 -> getr regs' 18 = getr regs 18 -> getr regs' 19 = getr regs 19 ->
getr regs' 26 = getr regs 26 -> getr regs' 27 = getr regs 27 ->
hp_core B x pat' cl rb regs' mem' md'.
Proof.
intros x pat pat' cl rb regs mem md regs' mem' md' Wr Hc Hcl Hrb HC HJ' Hio' HK HW HE' E2 E8 E3 E4 E9 E18 E19 E26 E27.
destruct HC as (HJ & Hio & Hkeep & (HSV & Hf) & HO & HR & _ & R2 & R8 & R3 & R4 & R9 & R18 & R19 & R26 & R27).
pose proof (hgk_frame x Hc) as (_ & _ & Fw & Fsp & _ & Fceil & Flo & Fhi & F47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct errno_low as ((Er0 & Er4) & _ & _).
assert (HT : T_parse_STK = 12576) by reflexivity.
assert (NW : forall a, ~ (hx_sp x - T_parse_STK <= a < hx_sp x - 112) -> ~ hp_hole x a ->
  ~ (as_errno B <= a < as_errno B + 4) -> ~ Wr a).
{ intros a H1 H2 H3 Hw. destruct (HW a Hw) as [X|[X|X]]; auto. }
split; [exact HJ'|].
split; [eapply same_io_trans; [exact Hio | exact Hio']|].
split.
{ intros a Ha Hs Hh Hp. rewrite (HK a Ha); [exact (Hkeep a Ha Hs Hh Hp)|].
  apply NW; [lia | exact Hh |]. intros X. apply Hp. unfold hp_pw. right. right. exact X. }
split.
{ split.
  - rewrite Forall_forall in HSV |- *. intros [o r] Hin. pose proof (hgk_saved_offs o r Hin) as Ho.
    specialize (HSV _ Hin) as Hv. cbn [fst snd] in *.
    eapply val_mem_kept; [|exact Hv]. intros k Hk.
    apply HK; [unfold T_parse_STK, T_PARSE_FRAME, ESTACK in *; lia|]. apply NW.
    + lia.
    + intros Hh. pose proof (hgk_hole_band x _ Hc Hh) as (_ & B2 & _). lia.
    + lia.
  - eapply val_mem_kept; [|exact Hf]. intros k Hk. unfold HP_FS0 in *.
    apply HK; [unfold T_parse_STK, T_PARSE_FRAME, ESTACK in *; lia|]. apply NW.
    + lia.
    + intros Hh. pose proof (hgk_hole_band x _ Hc Hh) as (_ & B2 & _). lia.
    + lia. }
split.
{ apply (garr8_frame segs _ _ _ _ HO). intros a Ha.
  unfold hd_zbytes in Ha. rewrite length_map, length_ha_cells_bytes in Ha.
  pose proof (hgk_out_apart x (a - hx_O x) Hc ltac:(lia)) as (A1 & A2 & A3 & _ & A5).
  replace (hx_O x + (a - hx_O x)) with a in * by lia.
  pose proof (app_addr_below_ceil a A5) as Ab. unfold ASAN_CEIL in Ab.
  apply (mbyte_of_aview segs). apply HK; [lia|]. apply NW; [lia | exact A2 |].
  intros X. apply A3. apply (proj1 (proj2 errno_low)). exact X. }
split.
{ intros HR0. specialize (HR HR0). apply (garr8_frame segs _ _ _ _ HR). intros a Ha.
  unfold hd_zbytes in Ha. rewrite length_map in Ha.
  pose proof (hgk_res_apart x (a - hx_R x) Hc HR0 ltac:(lia)) as (A1 & A2 & A3 & _ & A5).
  replace (hx_R x + (a - hx_R x)) with a in * by lia.
  apply (mbyte_of_aview segs). apply HK; [lia|].
  apply NW; [lia | exact A2 |]. intros X. apply A3. apply (proj1 (proj2 errno_low)). exact X. }
split; [exact HE'|].
rewrite E2, E8, E3, E4, E9, E18, E19, E26, E27. repeat split; assumption.
Qed.

(* ======================================= the pod at a cut ======================================= *)
(* Every byte of a cut's memory outside the stack window, the hole and the parse's writes reads as at the call. *)
Lemma hgk_kept : forall x pat cl rb regs mem md a, hp_core B x pat cl rb regs mem md -> 0 <= a < 2 ^ 64 ->
~ (hx_sp x - T_parse_STK <= a < hx_sp x) -> ~ hp_hole x a -> ~ hp_pw B x (Z.of_nat (length cl)) a ->
hx_view x mem a = hx_view x (hx_memc x) a.
Proof. intros x pat cl rb regs mem md a (_ & _ & HK & _) Ha H1 H2 H3. exact (HK a Ha H1 H2 H3). Qed.

(* The shadow bytes of application memory below the allocator's ceiling lie below the hole and the stack, apart
   from out, res and the errno cell. *)
Lemma hgk_shadow_kept : forall x pat cl rb regs mem md s, call_ok x -> Z.of_nat (length cl) <= hx_cap x ->
hp_core B x pat cl rb regs mem md -> SHADOW_OFF <= s < SHADOW_OFF + ly_stk_lo (hx_lyc x) / 8 ->
hx_view x mem s = hx_view x (hx_memc x) s.
Proof.
intros x pat cl rb regs mem md s Hc Hcl HC Hs.
pose proof (hgk_frame x Hc) as (_ & _ & Fw & Fsp & _ & Fceil & Flo & Fhi & F47 & Ffr1 & Ffr2 & Fpg & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HL : ly_stk_lo (hx_lyc x) / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia).
unfold SHADOW_OFF in Hs.
apply (hgk_kept x pat cl rb regs mem md s HC); [lia | unfold T_parse_STK, T_PARSE_FRAME, ESTACK in *; lia | |].
- intros Hh. unfold hp_hole, hx_shf, shadow_addr, SHADOW_OFF in Hh.
  assert (ly_stk_lo (hx_lyc x) / 8 <= hx_fr x / 8) by (apply Z.div_le_mono; lia). lia.
- intros [HO | [(HR0 & HR) | HE]].
  + pose proof (hgk_out_apart x (s - hx_O x) Hc ltac:(lia)) as (_ & _ & _ & _ & A5).
    replace (hx_O x + (s - hx_O x)) with s in A5 by lia.
    destruct A5 as (_ & [A5 | (A5 & _)]); unfold kLowShadowBeg, kHighMemBeg in A5; lia.
  + pose proof (hgk_res_apart x (s - hx_R x) Hc HR0 ltac:(lia)) as (_ & _ & _ & A4 & _).
    replace (hx_R x + (s - hx_R x)) with s in A4 by lia.
    destruct A4 as [A4 | (_ & [A4 | (A4 & _)])]; unfold kHighShadowEnd, kLowShadowBeg, kHighMemBeg in A4; lia.
  + pose proof (hgk_errno_apart x (s - as_errno B) Hc ltac:(lia)) as (_ & _ & _ & A4).
    unfold kLowMemEnd in A4. lia.
Qed.

(* The pod's bytes, their shadow and the shadow hull at a cut (a non-NULL call). *)
Lemma hgk_pod_at : forall x pat cl rb regs mem md, call_ok x -> hx_null x = 0 -> Z.of_nat (length cl) <= hx_cap x ->
hp_core B x pat cl rb regs mem md ->
garr8 segs (hx_rd x mem) (hx_P x) (hd_zbytes (hx_bs x)) /\
range_addressable (hx_view x mem) SHADOW_OFF (hx_P x) (hx_len x) /\
shadow_hull_vis (hx_view x mem) (hx_P x) (hx_len x).
Proof.
intros x pat cl rb regs mem md Hc Hn Hcl HC.
pose proof (hgk_frame x Hc) as (_ & _ & Fw & Fsp & _ & Fceil & Flo & Fhi & F47 & Ffr1 & Ffr2 & Fpg & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof Hc as (HP & _ & _ & _ & _ & _ & HA).
pose proof HP as (HJ & _). pose proof HJ as (HAR & _).
destruct HA as (Hpod & Hcap & _).
destruct (Hpod Hn) as (HP0 & HP16 & Hlen & Hlen8 & HSZ & HP63 & HG & HPin & HPO & HPR & HPE & HRA & HHV & HAM & HPoff).
pose proof (AR_laws_ok segs B) as LAWS.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR HPin) as (_ & H4096 & Hceilb & Happ & _).
assert (Hrq : req_size (Z.of_nat (length (hx_bs x))) = Z.of_nat (length (hx_bs x)))
  by (unfold req_size; destruct (_ =? 0) eqn:E; lia).
rewrite Hrq in Hceilb, Happ.
unfold hx_len.
(* the pod's own bytes *)
assert (KP : forall a, hx_P x <= a < hx_P x + Z.of_nat (length (hx_bs x)) -> hx_view x mem a = hx_view x (hx_memc x) a).
{ intros a Ha. apply (hgk_kept x pat cl rb regs mem md a HC); [lia | apply HPoff; lia | |].
  - intros Hh. pose proof (hgk_hole_band x _ Hc Hh) as (B1 & _).
    destruct Happ as (_ & [HL | [HH1 HH2]]); unfold kLowShadowBeg, kHighShadowBeg, kHighShadowEnd, kHighMemBeg in *; lia.
  - intros [HO | [(HR0 & HR) | HE]].
    + lia.
    + destruct HPR as [HPR|HPR]; [contradiction | lia].
    + lia. }
assert (KS : forall s, SHADOW_OFF <= s < SHADOW_OFF + ly_stk_lo (hx_lyc x) / 8 ->
  hx_view x mem s = hx_view x (hx_memc x) s) by (intros s Hs; exact (hgk_shadow_kept x pat cl rb regs mem md s Hc Hcl HC Hs)).
assert (HLq : (hx_P x + Z.of_nat (length (hx_bs x))) / 8 <= ly_stk_lo (hx_lyc x) / 8) by (apply Z.div_le_mono; lia).
split; [|split].
- apply (garr8_frame segs _ _ _ _ HG). intros a Ha. unfold hd_zbytes in Ha. rewrite length_map in Ha.
  apply (mbyte_of_aview segs). apply KP. exact Ha.
- intros a Ha. destruct (HRA a Ha) as (s & Hs & Hok). exists s. split; [|exact Hok].
  rewrite KS; [exact Hs|]. unfold shadow_of_addr. lia.
- intros s Hs Hn0. apply (HHV s Hs). unfold hx_view in KS. rewrite <- (KS s); [exact Hn0|].
  unfold shadow_addr, SHADOW_OFF in Hs |- *. lia.
Qed.

(* ======================================= present bytes ======================================= *)
Lemma hgk_aview_present : forall H (mem : word -> option byte) s v, 0 <= s < 2 ^ 64 -> ~ in_img segs s ->
aview segs H mem s = Some v -> apresent H mem s.
Proof.
intros H mem s v Hs Hn E. unfold aview, mbyte, mrestrict in E.
destruct (H (Z_to_bv 64 s)) eqn:EH.
- rewrite (seg_rom_none segs s Hs Hn) in E. discriminate E.
- destruct (mem (Z_to_bv 64 s)) as [b|] eqn:EM.
  + split; [exact EH | exists b; exact EM].
  + rewrite (seg_rom_none segs s Hs Hn) in E. discriminate E.
Qed.

(* the caller's stack window is present at a cut (the hole lies below it) *)
Lemma hgk_present : forall x pat cl rb regs mem md, hp_core B x pat cl rb regs mem md ->
forall a, hx_sp0 x - hx_STK x <= a < hx_sp0 x -> apresent (w_H (hx_W x)) mem a.
Proof.
intros x pat cl rb regs mem md ((HJ & OK & HP) & _) a Ha.
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstatic & _).
pose proof (am_layout B (hx_lyc x) (hx_Sc x) _ (proj1 HAR)) as LO.
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Eslo & _).
apply (proj1 (hp_apresent_unp _ (hU (hx_fr x) pat) mem a
  (hole_free_stack (hx_lyc x) (hx_fr x) pat a LO OK ltac:(rewrite Eslo; lia)))).
apply Hpres. exact Ha.
Qed.

(* the hole's bytes are present at a cut *)
Lemma hgk_hole_present : forall x pat cl rb regs mem md, call_ok x -> hp_core B x pat cl rb regs mem md ->
length pat = 8%nat -> forall o, 0 <= o < 8 -> apresent (w_H (hx_W x)) mem (hx_shf x + o).
Proof.
intros x pat cl rb regs mem md Hc ((HJ & OK & HP) & _) Hl o Ho.
pose proof (hgk_hole_band x (hx_shf x + o) Hc ltac:(unfold hp_hole; lia)) as (_ & _ & L & R).
apply (hgk_aview_present _ _ _ (nth (Z.to_nat o) pat 0) R).
- intros Hi. pose proof (segs_low _ Hi). lia.
- exact (HP o ltac:(rewrite Hl; cbn; lia)).
Qed.

(* ======================================= two strings meet ======================================= *)
(* A NUL-terminated string in the view: the bytes s at a (each nonzero), then the NUL. *)
Definition hgk_cstr_at (H : word -> bool) (mem : word -> option byte) (a : Z) (s : list Z) : Prop :=
(forall i, 0 <= i < Z.of_nat (length s) -> aview segs H mem (a + i) = Some (nth (Z.to_nat i) s 0)) /\
aview segs H mem (a + Z.of_nat (length s)) = Some 0 /\
Forall (fun b => 0 < b < 256) s.
(* where the strcmp wrapper's contract (HPgHole.hd_astrcmp_hole) has the two strings meet, and its result *)
Definition hgk_meet (H : word -> bool) (mem : word -> option byte) (x y k c1 c2 : Z) : Prop :=
0 <= k /\
(forall i, 0 <= i < k -> exists b, aview segs H mem (x + i) = Some b /\ aview segs H mem (y + i) = Some b /\ b <> 0) /\
aview segs H mem (x + k) = Some c1 /\ aview segs H mem (y + k) = Some c2 /\ (c1 <> c2 \/ c1 = 0).
Definition hgk_res (c1 c2 : Z) : Z := if c1 =? c2 then 0 else if c1 <? c2 then -1 else 1.

Lemma hgk_res_0 : forall c1 c2, hgk_res c1 c2 = 0 <-> c1 = c2.
Proof.
intros c1 c2. unfold hgk_res.
destruct (Z.eqb_spec c1 c2) as [E|E]; [tauto|].
destruct (c1 <? c2); split; intros H; first [discriminate H | exfalso; exact (E H)].
Qed.

Lemma hgk_res_range : forall c1 c2, -1 <= hgk_res c1 c2 <= 1.
Proof. intros c1 c2. unfold hgk_res. destruct (c1 =? c2); [lia|]. destruct (c1 <? c2); lia. Qed.

Lemma hgk_cstr_cons : forall H mem a b s, hgk_cstr_at H mem a (b :: s) ->
aview segs H mem a = Some b /\ 0 < b < 256 /\ hgk_cstr_at H mem (a + 1) s.
Proof.
intros H mem a b s (Hc & Hn & Hf). inversion Hf as [|b' s' Hb Hs]; subst.
cbn [length] in Hc, Hn. rewrite Nat2Z.inj_succ in Hc, Hn.
split; [specialize (Hc 0 ltac:(lia)); rewrite Z.add_0_r in Hc; exact Hc|].
split; [exact Hb|].
split; [|split; [replace (a + 1 + Z.of_nat (length s)) with (a + Z.succ (Z.of_nat (length s))) by lia; exact Hn | exact Hs]].
intros i Hi. specialize (Hc (i + 1) ltac:(lia)). replace (a + (i + 1)) with (a + 1 + i) in Hc by lia.
rewrite Hc. f_equal. replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia. reflexivity.
Qed.

Lemma hgk_cstr_nil : forall H mem a, hgk_cstr_at H mem a [] -> aview segs H mem a = Some 0.
Proof. intros H mem a (_ & Hn & _). cbn [length Z.of_nat] in Hn. rewrite Z.add_0_r in Hn. exact Hn. Qed.

Lemma hgk_str_meet : forall (s : list Z) H mem (x : Z) (t : list Z) (y : Z),
hgk_cstr_at H mem x s -> hgk_cstr_at H mem y t ->
exists kk c1 c2, hgk_meet H mem x y kk c1 c2 /\ 0 <= kk <= Z.of_nat (length s) /\ kk <= Z.of_nat (length t) /\
(hgk_res c1 c2 = 0 <-> s = t).
Proof.
induction s as [|b s IH]; intros H mem x t y Hx Hy.
- pose proof (hgk_cstr_nil H mem x Hx) as X0.
  destruct t as [|b' t].
  + pose proof (hgk_cstr_nil H mem y Hy) as Y0.
    exists 0, 0, 0. split; [|cbn [length Z.of_nat]; split; [lia|]; split; [lia|]; rewrite hgk_res_0; tauto].
    split; [lia|]. split; [intros i Hi; lia|]. rewrite !Z.add_0_r. split; [exact X0|]. split; [exact Y0|]. right; reflexivity.
  + destruct (hgk_cstr_cons H mem y b' t Hy) as (Y0 & Hb' & _).
    exists 0, 0, b'. split; [|cbn [length]; split; [lia|]; split; [lia|]; rewrite hgk_res_0; split; [lia | discriminate]].
    split; [lia|]. split; [intros i Hi; lia|]. rewrite !Z.add_0_r. split; [exact X0|]. split; [exact Y0|]. right; reflexivity.
- destruct (hgk_cstr_cons H mem x b s Hx) as (X0 & Hb & Hx').
  destruct t as [|b' t].
  + pose proof (hgk_cstr_nil H mem y Hy) as Y0.
    exists 0, b, 0. split; [|cbn [length]; split; [lia|]; split; [lia|]; rewrite hgk_res_0; split; [lia | discriminate]].
    split; [lia|]. split; [intros i Hi; lia|]. rewrite !Z.add_0_r. split; [exact X0|]. split; [exact Y0|]. left; lia.
  + destruct (hgk_cstr_cons H mem y b' t Hy) as (Y0 & Hb' & Hy').
    destruct (Z.eq_dec b b') as [<-|Hne].
    * destruct (IH H mem (x + 1) t (y + 1) Hx' Hy') as (kk & c1 & c2 & (Hk0 & Heq & Hc1 & Hc2 & Hend) & Hks & Hkt & Hres).
      exists (kk + 1), c1, c2.
      split; [|cbn [length]; split; [lia|]; split; [lia|]; rewrite Hres;
               split; [intros ->; reflexivity | intros Hst; injection Hst; tauto]].
      split; [lia|].
      split; [|split; [replace (x + (kk + 1)) with (x + 1 + kk) by lia; exact Hc1|];
              split; [replace (y + (kk + 1)) with (y + 1 + kk) by lia; exact Hc2 | exact Hend]].
      intros i Hi. destruct (Z.eq_dec i 0) as [->|Hi0].
      { exists b. rewrite !Z.add_0_r. split; [exact X0|]. split; [exact Y0|]. lia. }
      destruct (Heq (i - 1) ltac:(lia)) as (bb & B1 & B2 & B3).
      exists bb. replace (x + i) with (x + 1 + (i - 1)) by lia. replace (y + i) with (y + 1 + (i - 1)) by lia. tauto.
    * exists 0, b, b'.
      split; [|cbn [length]; split; [lia|]; split; [lia|]; rewrite hgk_res_0;
               split; [intros E; exfalso; exact (Hne E) | intros E; injection E; intros _ E'; exfalso; exact (Hne E')]].
      split; [lia|]. split; [intros i Hi; lia|]. rewrite !Z.add_0_r. split; [exact X0|]. split; [exact Y0|]. left; exact Hne.
Qed.

(* a string read through hd_cstr (a literal of the image) is a C string in the view *)
Lemma hgk_cstr_of_hd : forall H mem a s, hd_cstr segs H mem a s -> hgk_cstr_at H mem a s.
Proof. intros H mem a s (Hb & Hn & Hf & _). split; [exact Hb|]. split; [exact Hn | exact Hf]. Qed.

End g.

(* ======================================= the key's model, by the code's tests ======================================= *)
(* strtol's end offset and value (lib/Prog/__intscan_c.v, the model the strtol wrapper's contract states) *)
Lemma hgk_ndig_le : forall l, (PIS.ndig l <= length l)%nat.
Proof. induction l as [|b l IH]; cbn [PIS.ndig length]; [lia|]. destruct (CType.c_digit b); lia. Qed.

Lemma hgk_rest_le : forall s, (length (PIS.s10_rest s) <= length s)%nat.
Proof.
intros s. unfold PIS.s10_rest. pose proof (Strtol.length_sign_split (CType.skip_space s)).
pose proof (Strtol.length_skip_space s). lia.
Qed.

Lemma hgk_end_le : forall s, 0 <= PIS.s10_end s <= Z.of_nat (length s).
Proof.
intros s. pose proof (hgk_rest_le s) as R. pose proof (hgk_ndig_le (PIS.s10_rest s)) as N.
unfold PIS.s10_end, PIS.s10_nd. destruct (Nat.eqb (PIS.ndig (PIS.s10_rest s)) 0); lia.
Qed.

Lemma hgk_val_range : forall s, - 2 ^ 63 <= PIS.s10_val s < 2 ^ 63.
Proof. intros s. unfold PIS.s10_val, PIS.LMIN. lia. Qed.

Lemma hgk_key_e0 : forall s, PIS.s10_end s = 0 -> Headamp.parse_key s = Headamp.KBad.
Proof. intros s H. unfold Headamp.parse_key. rewrite H. reflexivity. Qed.

Lemma hgk_key_nodot : forall s, PIS.s10_end s <> 0 ->
bv_unsigned (nth (Z.to_nat (PIS.s10_end s)) s Cursor.NUL) <> 46 -> Headamp.parse_key s = Headamp.KBad.
Proof.
intros s H1 H2. unfold Headamp.parse_key. rewrite (proj2 (Z.eqb_neq _ _) H1), (proj2 (Z.eqb_neq _ _) H2). reflexivity.
Qed.

Lemma hgk_key_name : forall s, PIS.s10_end s <> 0 -> bv_unsigned (nth (Z.to_nat (PIS.s10_end s)) s Cursor.NUL) = 46 ->
Headamp.parse_key s =
match Headamp.param_of_name (Cursor.cstr (skipn (S (Z.to_nat (PIS.s10_end s))) s)) with
| None => Headamp.KBad
| Some p => if (PIS.s10_val s <? 0) || (Headamp.REAC_HEADAMP_MAX_CH <=? PIS.s10_val s) then Headamp.KRange
            else Headamp.KCell (PIS.s10_val s) p
end.
Proof.
intros s H1 H2. unfold Headamp.parse_key. rewrite (proj2 (Z.eqb_neq _ _) H1), (proj2 (Z.eqb_eq _ _) H2). reflexivity.
Qed.

Lemma hgk_nth_len : forall (l : list byte) i, bv_unsigned (nth i l Cursor.NUL) = 46 -> (i < length l)%nat.
Proof.
intros l i H. destruct (Nat.lt_ge_cases i (length l)) as [L|L]; [exact L|].
rewrite nth_overflow in H by exact L. vm_compute in H. discriminate H.
Qed.

Lemma hgk_nonul_skipn : forall (l : list byte) n, ~ In Cursor.NUL l -> ~ In Cursor.NUL (skipn n l).
Proof. intros l n H X. apply H. rewrite <- (firstn_skipn n l). apply in_or_app. right. exact X. Qed.

Lemma hgk_cstr_nonul : forall l, ~ In Cursor.NUL l -> Cursor.cstr l = l.
Proof.
induction l as [|x l IH]; intros H; [reflexivity|]. unfold Cursor.cstr in *. cbn [Cursor.nul_idx].
destruct (Z.eqb_spec (bv_unsigned x) 0) as [E|E].
- exfalso. apply H. left. apply bv_eq. rewrite E. reflexivity.
- cbn [firstn]. f_equal. apply IH. intros X. apply H. right. exact X.
Qed.

Lemma hgk_prefix_len : forall k, Headamp.ha_prefix k = true -> (13 <= length k)%nat.
Proof.
intros k H. unfold Headamp.ha_prefix in H. apply Cursor.bytes_eqb_eq in H.
assert (L : length (firstn (length Headamp.HA_PREFIX) k) = length Headamp.HA_PREFIX) by (rewrite H; reflexivity).
rewrite length_firstn in L. change (length Headamp.HA_PREFIX) with 13%nat in L. lia.
Qed.

Lemma hgk_zbytes_inj : forall l1 l2, hd_zbytes l1 = hd_zbytes l2 -> l1 = l2.
Proof.
unfold hd_zbytes. induction l1 as [|b1 l1 IH]; intros [|b2 l2] H; cbn [map] in H; try discriminate H; [reflexivity|].
injection H as Hb Hl. f_equal; [apply bv_eq; exact Hb | apply IH; exact Hl].
Qed.

Lemma hgk_zbytes_pos : forall l, ~ In Cursor.NUL l -> Forall (fun b => 0 < b < 256) (hd_zbytes l).
Proof.
intros l H. unfold hd_zbytes. apply Forall_forall. intros z Hz. apply in_map_iff in Hz as (b & <- & Hb).
pose proof (Cursor.byte_range b) as R. split; [|lia].
destruct (Z.eq_dec (bv_unsigned b) 0) as [E|E]; [|lia].
exfalso. apply H. replace b with Cursor.NUL in Hb; [exact Hb|]. apply bv_eq. rewrite E. reflexivity.
Qed.

(* param_of_name by the three strcmp results (each 0 exactly when the name is that literal) *)
Lemma hgk_param_phantom : forall nm, nm = Headamp.NAME_PHANTOM -> Headamp.param_of_name nm = Some Headamp.HA_PHANTOM.
Proof. intros nm ->. reflexivity. Qed.
Lemma hgk_param_pad : forall nm, nm <> Headamp.NAME_PHANTOM -> nm = Headamp.NAME_PAD ->
Headamp.param_of_name nm = Some Headamp.HA_PAD.
Proof. intros nm _ ->. reflexivity. Qed.
Lemma hgk_param_sens : forall nm, nm <> Headamp.NAME_PHANTOM -> nm <> Headamp.NAME_PAD -> nm = Headamp.NAME_SENS ->
Headamp.param_of_name nm = Some Headamp.HA_SENS.
Proof. intros nm _ _ ->. reflexivity. Qed.
Lemma hgk_param_none : forall nm, nm <> Headamp.NAME_PHANTOM -> nm <> Headamp.NAME_PAD -> nm <> Headamp.NAME_SENS ->
Headamp.param_of_name nm = None.
Proof.
intros nm H1 H2 H3. unfold Headamp.param_of_name.
destruct (Cursor.bytes_eqb nm Headamp.NAME_PHANTOM) eqn:E1; [apply Cursor.bytes_eqb_eq in E1; contradiction|].
destruct (Cursor.bytes_eqb nm Headamp.NAME_PAD) eqn:E2; [apply Cursor.bytes_eqb_eq in E2; contradiction|].
destruct (Cursor.bytes_eqb nm Headamp.NAME_SENS) eqn:E3; [apply Cursor.bytes_eqb_eq in E3; contradiction|].
reflexivity.
Qed.

Section m. Context {segs : list Segment}.
Local Abbreviation pctx := (@hp_ctx segs).
Implicit Types x : pctx.

(* a refusal of the key: the advance with the key slot empty, keys + 1 and the first refusal kept *)
Lemma hgk_key_refuse : forall x r cc n ck cl keys rf bad, hp_m_key x r cc n ck cl keys rf -> 0 <= bad <= 5 ->
Headamp.parse_cell (hp_kstr x ck) (Spa.child_at (hx_bs x) cc) = inl bad ->
hp_m_adv x r cc n None cl (keys + 1) (if rf =? Headamp.REFUSE_NONE then bad else rf).
Proof.
intros x r cc n ck cl keys rf bad (Hnull & Hst & Hc1 & Hc8 & Hin & Hn & HK & (Hcl & Hk & Hrf) & HP & HW) Hb Hpc.
split; [exact Hnull|]. split; [exact Hst|]. split; [exact Hc1|]. split; [exact Hc8|]. split; [exact Hin|].
split; [exact Hn|]. split; [intros ck' Hck'; discriminate Hck'|].
split; [split; [exact Hcl|]; split; [lia|]; destruct (rf =? Headamp.REFUSE_NONE); lia|].
rewrite HW, Hpc. reflexivity.
Qed.

(* the key read as the cell address (ch, p): the value cut *)
Lemma hgk_key_val : forall x r cc n ck cl keys rf ch p, hp_m_key x r cc n ck cl keys rf ->
Headamp.parse_key (skipn 13 (hp_kstr x ck)) = Headamp.KCell ch p -> hp_m_val x r cc n ch p cl keys rf.
Proof.
intros x r cc n ck cl keys rf ch p (Hnull & Hst & Hc1 & Hc8 & Hin & Hn & HK & Hs & HP & HW) Hk.
pose proof (Headamp.parse_key_cell _ _ _ Hk) as (Hch & Hp).
split; [exact Hnull|]. split; [exact Hst|]. split; [exact Hc1|]. split; [exact Hc8|]. split; [exact Hin|].
split; [exact Hn|]. split; [exact Hs|]. split; [exact Hch|].
split; [unfold Headamp.HA_PHANTOM, Headamp.HA_PAD, Headamp.HA_SENS in *; lia|].
rewrite HW, (hp_parse_cell_vcell (hp_kstr x ck) (Spa.child_at (hx_bs x) cc) ch p Hk). reflexivity.
Qed.
End m.
