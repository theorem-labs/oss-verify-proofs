(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the TAIL segment of sup_chain's walk on plugin-hostd/fuzz_command's ASan+UBSan
   build (fuzz_command.asan-ubsan), from the loop exit BASE + SCB_LEXIT = 0x8c444 to the return 0x8c558, against the
   interface lib/B/Prog/sup_chain_d.v (scb_lctx, scb_inv) and the helpers lib/B/Prog/sup_chain_aux.v. Statement from
   a Theorem Labs lane 707acd856cb (lib/B/Prog/sup_chain_c.v, tsup_chain_spec). The block bookkeeping of the post is the pure lemma
   scb4_final_blocks; the release segment 0x8c47c .. 0x8c558 is scb4_rel; scb_tail composes the four calls with both.

   The code: ld s2,8(s1) (the slot); arg_s(slot, list) 0x8c450; free(list) 0x8c458; rec_shape_of("chain", 5)
   0x8c468; answer(slot, shape, 1) 0x8c478 with this call's class-1 frame still live; then the inline release
   0x8c47c .. 0x8c4e4 (the magic 0x45e0360e at F, f5 at the frame's 16 shadow bytes, the flag byte through the word
   at F + 120), the epilogue (the saved registers back, sp := s0 - 192 + 192) and `ret`. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/sup_chain_s4.v, with its module paths and module names changed; 1163 of its 1234 lines of code are new or changed and 1980 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgParseBase.v at afaa3cb55c1 (lines 312-641:
   pre_pod, pre_stack, kept_view, pod_at_cut, shent_pod, cut_env, frame_region_ok, saved_of_frame_region, leaf_regs,
   ppost_intro) and proofs/reac-pw/fuzz_headamp/lib/A/HPgCallsStr.v at a9577ae74c2 (hc_garr8_some, hc_garr8_of_aview,
   hc_bytes_pos, hc_notin0, hc_awrap_of, hc_awrap_cstr, hc_hull_sub, hc_off_stack_sub, hc_awrap_sub), renamed with the
   prefix hk_ and restated for headamp's parse: the call record, premises, cut core and post of lib/A/HPgParseBase.v
   and the frame hole of lib/A/HPgHole.v. *)
(* reac-pw/fuzz_headamp: the IMAGE-INDEPENDENT kit of reac_headamp_prop_parse_result's walks, image A
   (fuzz_headamp.asan 0x845b4) and image B (fuzz_headamp.asan-ubsan 0x849ac). No image numeral: every lemma is over
   segs (Section variable) with the one Section hypothesis segs_low. Proves no function (kind: segment lemma).

   What both images do the same way (measured on the pinned images, neutral listings of both): the prologue
   `addi sp,sp,-0x100`, the thirteen saves ra, s0 .. s11 at sp0 - 8 .. sp0 - 104 and `fsd fs0,0x90(sp)` at
   sp0 - 112 (HPgParseBase.HP_SAVED, HP_FS0), `addi s0,sp,0x100` (s0 = sp0), `andi sp,sp,-0x20` (sp = spa,
   HPgParseBase.hx_spa), s1 = res, s2 = cap, s3 = out, s11 = SHADOW_OFF, s10 = the hole's first shadow byte; the
   temporaries at spa + 0x10 .. spa + 0x38 and the frame object [spa + 0x40, spa + 0x80) (the strtol end pointer at
   spa + 0x60); the epilogue `addi sp,s0,-0x100`, the thirteen `ld`, `fld fs0,0x90(sp)`, `addi sp,sp,0x100`, `ret`.

   The groups:
   1. hk_call_*: the call's facts, from hp_call_ok (hd_pre, hd_parse_args unfolded, the stack and frame bounds).
   2. hk_kept* / hk_*_at_cut / hk_shent_*: what every cut's hp_core gives (bytes kept, the pod, out, res, strings and
      constant cells at the cut's memory, the shadow entries the instrumented checks take).
   3. hk_env, hk_saves, hk_temps, hk_hole_rg, hk_atoms: the engine's entry at a cut (env slots 32 = SHADOW_OFF,
      33 .. 45 the thirteen saved words in HP_SAVED order, 46 fs0's entry bits, 47 .. the segment's own values).
   4. hk_core_*: hp_core again after a run or a wrapper call.
   5. the return: the reloads, `fld fs0`, hj_leave and hp_post's intro.
   The prologue's own steps (fsd fs0, the realign, the hole's opening) are lib/A/HPgParseGPro.v's. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK0j YP00 YG0q YG05 YO09 YI0m YE00 YE01.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Cursor Model Accessors Spa Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A.Rt Require Import FMupoison.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec HPgHole HPgParseBase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================================= arithmetic ======================================= *)
(* The shadow hull of a range below kHighMemEnd lies in the shadow band [SHADOW_OFF, kHighShadowEnd). *)
Lemma hk_hull_band : forall P n s, 0 <= P -> 0 < n -> P + n < kHighMemEnd ->
shadow_addr P / 8 * 8 <= s < shadow_addr (P + n - 1) / 8 * 8 + 8 -> SHADOW_OFF <= s < kHighShadowEnd.
Proof. intros P n s HP Hn Hhi Hs. unfold shadow_addr, kHighMemEnd, kHighShadowEnd, SHADOW_OFF in *. lia. Qed.

(* A range outside [sp - T_parse_STK, sp) keeps its shadow hull away from the shadow bytes of [fr, fr + 64), fr the
   parse's frame object. *)
Lemma hk_hull_hole : forall P n sp fr s,
0 <= P -> 0 < n -> (P + n <= sp - T_parse_STK \/ sp <= P) -> sp - 224 < fr <= sp - 192 -> fr mod 8 = 0 ->
shadow_addr P / 8 * 8 <= s < shadow_addr (P + n - 1) / 8 * 8 + 8 ->
~ (shadow_addr fr <= s < shadow_addr fr + 8).
Proof. intros P n sp fr s HP Hn Hside Hfr H8 Hs. unfold shadow_addr, T_parse_STK, T_PARSE_FRAME, ESTACK in *. lia. Qed.

(* A byte's shadow byte is a shadow byte of [fr, fr + 64) only if the byte is in it. *)
Lemma hk_sh_in : forall fr a, fr mod 8 = 0 -> shadow_addr fr <= shadow_addr a < shadow_addr fr + 8 ->
fr <= a < fr + 64.
Proof. intros fr a H8 Hs. unfold shadow_addr in Hs. lia. Qed.

(* ======================================= the engine's entry: regions and slots ======================================= *)
(* the saves at s0 = sp0 (atom 8): the thirteen saved words at sp0 - 8 .. sp0 - 104 (env slots 33 .. 45, HP_SAVED's
   order) and fs0's entry bits at sp0 - 112 (slot 46); read-only *)
Definition hk_saved_chunks : list YP09.chunk :=
[YP09.mkChunk (-8) (CVal 8 (SOff 33 0)); YP09.mkChunk (-16) (CVal 8 (SOff 34 0));
 YP09.mkChunk (-24) (CVal 8 (SOff 35 0)); YP09.mkChunk (-32) (CVal 8 (SOff 36 0));
 YP09.mkChunk (-40) (CVal 8 (SOff 37 0)); YP09.mkChunk (-48) (CVal 8 (SOff 38 0));
 YP09.mkChunk (-56) (CVal 8 (SOff 39 0)); YP09.mkChunk (-64) (CVal 8 (SOff 40 0));
 YP09.mkChunk (-72) (CVal 8 (SOff 41 0)); YP09.mkChunk (-80) (CVal 8 (SOff 42 0));
 YP09.mkChunk (-88) (CVal 8 (SOff 43 0)); YP09.mkChunk (-96) (CVal 8 (SOff 44 0));
 YP09.mkChunk (-104) (CVal 8 (SOff 45 0)); YP09.mkChunk (-112) (CVal 8 (SOff 46 0))].
Definition hk_saves : YP09.region := YP09.mkRegion (Some 8%nat) (-0x70) 0 0 0 hk_saved_chunks.
(* the temporaries and the frame object [spa, spa + 0x80) at sp = spa (atom 2), writable, the segment's chunks *)
Definition hk_temps (cs : list YP09.chunk) : YP09.region := YP09.mkRegion (Some 2%nat) 0 0x80 0 0x80 cs.
(* the hole's eight shadow bytes at s10 (atom 26), writable, one literal byte chunk each (for non-token runs only:
   a writable region inside the shadow span fails the token engine's static check) *)
Definition hk_hole_chunks (pat : list Z) : list YP09.chunk :=
map (fun i => YP09.mkChunk (Z.of_nat i) (CVal 1 (SLit (nth i pat 0)))) (seq 0 8).
Definition hk_hole_rg (pat : list Z) : YP09.region := YP09.mkRegion (Some 26%nat) 0 8 0 8 (hk_hole_chunks pat).
(* the atoms every cut knows: spa (32-aligned), sp0 (16-aligned), the hole's first byte (4-aligned), SHADOW_OFF *)
Definition hk_atoms : list (nat * afact) :=
[(2%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (8%nat, mkAF (2 ^ 46) (2 ^ 47) 4);
 (26%nat, mkAF (SHADOW_OFF + 2 ^ 43) (SHADOW_OFF + 2 ^ 44) 2); (27%nat, mkAF SHADOW_OFF SHADOW_OFF 0)].
(* the shadow base the token runs take: s11 *)
Definition hk_Bx : sv := SOff 27 0.
Definition hk_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).

Lemma hk_sv_SOff0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.

Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {segs : list Segment}.
Variable B : asyms.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Context {akey aph apad asens gotw guard : Z} {dcs : list (Z * Z)}.
Local Notation call_ok := (hp_call_ok B akey aph apad asens gotw guard dcs).
Implicit Types (x : @hp_ctx segs).

(* ======================================= 1. the call ======================================= *)
Lemma hk_call_pre : forall x, call_ok x ->
hd_pre segs B (hx_STK x) (hx_sp0 x) (hx_FP x) (hx_ly x) (hx_S x) (hx_W0 x) (hx_mem0 x) (hx_md0 x) (hx_own x)
  (hx_k x) T_parse_STK (hx_regs x) (hx_lyc x) (hx_Sc x) (hx_W x) (hx_memc x) (hx_mdc x).
Proof. intros x H. exact (proj1 H). Qed.

Lemma hk_call_journal : forall x, call_ok x ->
ajournal segs B (hx_STK x) (hx_sp0 x) (hx_FP x) (hx_ly x) (hx_S x) (hx_W0 x) (hx_mem0 x) (hx_md0 x) (hx_own x)
  (hx_lyc x) (hx_Sc x) (hx_W x) (hx_memc x) (hx_mdc x) (hx_k x).
Proof. intros x H. exact (proj1 (proj1 H)). Qed.

Lemma hk_call_AR : forall x, call_ok x -> AR segs B (hx_lyc x) (hx_Sc x) (hx_W x) (hx_memc x) (hx_mdc x).
Proof. intros x H. exact (proj1 (hk_call_journal x H)). Qed.

Lemma hk_call_regs : forall x, call_ok x ->
0 <= hx_null x <= 1 /\ getr (hx_regs x) 10 = w64 (if hx_null x =? 0 then hx_P x else 0) /\
getr (hx_regs x) 11 = w64 (hx_O x) /\ getr (hx_regs x) 12 = w64 (hx_cap x) /\
getr (hx_regs x) 13 = w64 (hx_R x) /\ YK0s.ret_ok (getr (hx_regs x) 1) /\ 4096 <= raZ (hx_regs x) /\
getr (hx_regs x) 3 = w64 (as_gp B) /\ getr (hx_regs x) 4 = w64 (as_tp B).
Proof.
intros x ((_ & Hra & Hra4 & Hgp & Htp & _) & Hn & H10 & H11 & H12 & H13 & _).
exact (conj Hn (conj H10 (conj H11 (conj H12 (conj H13 (conj Hra (conj Hra4 (conj Hgp Htp)))))))).
Qed.

Lemma hk_call_args : forall x, call_ok x ->
hd_parse_args segs B (hx_STK x) (hx_sp0 x) (hx_ly x) (hx_S x) (hx_lyc x) (hx_Sc x) (hx_W x) (hx_memc x) (hx_own x)
  (hx_regs x) (hx_RLO x) (hx_RHI x) akey aph apad asens gotw guard dcs
  (hx_null x) (hx_P x) (hx_O x) (hx_R x) (hx_cap x) (hx_ev x) (hx_bs x).
Proof. intros x (_ & _ & _ & _ & _ & _ & H). exact H. Qed.

(* the pod of a non-NULL call (role's pre_pod) *)
Lemma hk_pod : forall x, call_ok x -> hx_null x = 0 ->
0 < hx_P x /\ hx_P x mod 16 = 0 /\ 8 <= hx_len x <= 16384 /\ hx_len x mod 8 = 0 /\ hx_SZ x = hx_len x - 8 /\
hx_P x + hx_len x <= 2 ^ 63 /\
garr8 segs (hx_rd x (hx_memc x)) (hx_P x) (hd_zbytes (hx_bs x)) /\
In (hx_P x, hx_len x) (ablocks B (hx_lyc x) (hx_Sc x)) /\
(hx_P x + hx_len x <= hx_O x \/ hx_O x + 3 * (hx_cap x + 1) <= hx_P x) /\
(hx_R x = 0 \/ hx_P x + hx_len x <= hx_R x \/ hx_R x + 12 <= hx_P x) /\
(hx_P x + hx_len x <= as_errno B \/ as_errno B + 4 <= hx_P x) /\
range_addressable (hx_view x (hx_memc x)) SHADOW_OFF (hx_P x) (hx_len x) /\
shadow_hull_vis (hx_view x (hx_memc x)) (hx_P x) (hx_len x) /\
amem_range (hx_P x) (hx_len x + 8) /\
hd_off_stack (hx_regs x) T_parse_STK (hx_P x) (hx_len x).
Proof. intros x H Hn. destruct (hk_call_args x H) as (Hp & _). exact (Hp Hn). Qed.

(* the stack: the caller's window, the parse's own frame (role's pre_stack; HPgHole.hd_parse_frame) *)
Lemma hk_stack : forall x, call_ok x ->
alloc_ceiling <= ly_stk_lo (hx_lyc x) /\ ly_stk_lo (hx_lyc x) + hx_STK x <= hx_sp0 x /\
hx_sp0 x - hx_STK x <= hx_sp x - T_parse_STK /\ hx_sp x <= hx_sp0 x /\ hx_sp0 x <= ly_stk_hi (hx_lyc x) /\
ly_stk_hi (hx_lyc x) <= 2 ^ 47 /\ hx_sp x mod 16 = 0 /\ hx_sp0 x mod 16 = 0 /\
hx_spa x mod 32 = 0 /\ hx_sp x - 0x120 < hx_spa x <= hx_sp x - 0x100 /\ hx_fr x = hx_spa x + 0x40 /\
ly_stk_lo (hx_lyc x) + 64 <= hx_fr x /\ hx_fr x + 128 <= ly_stk_hi (hx_lyc x).
Proof.
intros x Hc. pose proof (hk_call_pre x Hc) as HP.
epose proof (hd_parse_frame segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HP) as (F32 & F1 & F2 & F2' & F3 & F4 & F16 & S16).
destruct HP as (HJ & _ & _ & _ & _ & Hal & Hw1 & Hw2 & _).
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Eslo & Eshi & _).
unfold hx_fr, hx_spa, hx_sp. unfold hd_fr in *.
clear - F32 F1 F2 F2' F3 F4 F16 S16 Hal Hw1 Hw2 Hal16 Hstk0 Hceil Hslo Hshi H47 Eslo Eshi.
repeat split; lia.
Qed.

(* the frame object and the temporaries [spa, spa + 0x80) lie in the parse's window, below the saves *)
Lemma hk_frame_win : forall x, call_ok x ->
hx_sp x - T_parse_STK <= hx_spa x /\ hx_spa x + 0x80 <= hx_sp x - 0x80 /\ hx_fr x mod 8 = 0 /\
hx_sp x - 224 < hx_fr x <= hx_sp x - 192 /\ 0 <= hx_spa x.
Proof.
intros x Hc. pose proof (hk_stack x Hc) as HS.
pose proof alloc_ceiling_value as [[C1 C2] _].
clear - HS C1. unfold T_parse_STK, T_PARSE_FRAME, ESTACK in *. repeat split; lia.
Qed.

(* every byte of the parse's window is above the allocator's ceiling and below 2^47 *)
Lemma hk_window_band : forall x a, call_ok x -> hx_sp x - T_parse_STK <= a < hx_sp x ->
alloc_ceiling <= a < 2 ^ 47.
Proof.
intros x a Hc Ha. pose proof (hk_stack x Hc) as (H1 & H2 & H3 & H4 & H5 & H6 & _).
clear - Ha H1 H2 H3 H4 H5 H6. lia.
Qed.

(* the hole's eight shadow bytes: in the shadow band, above the shadow of everything below 2^46, below the ceiling *)
Lemma hk_hole_band : forall x a, call_ok x -> hp_hole x a ->
SHADOW_OFF + 2 ^ 43 <= a < kHighShadowEnd /\ a < alloc_ceiling.
Proof.
intros x a Hc Hh. pose proof (hk_stack x Hc) as HS.
pose proof alloc_ceiling_value as [[C1 C2] _].
unfold hp_hole, hx_shf, shadow_addr in Hh.
clear - Hh HS C1. unfold kHighShadowEnd, SHADOW_OFF in *. lia.
Qed.

(* the shadow byte of a byte outside the frame object is not a hole byte *)
Lemma hk_sh_not_hole : forall x a, call_ok x -> ~ (hx_fr x <= a < hx_fr x + 64) -> ~ hp_hole x (shadow_addr a).
Proof.
intros x a Hc Hn Hh. apply Hn. pose proof (hk_frame_win x Hc) as (_ & _ & H8 & _).
unfold hp_hole, hx_shf in Hh. exact (hk_sh_in (hx_fr x) a H8 Hh).
Qed.

(* the pod lies on one side of the parse's window *)
Lemma hk_pod_side : forall x, call_ok x -> hx_null x = 0 ->
hx_P x + hx_len x <= hx_sp x - T_parse_STK \/ hx_sp x <= hx_P x.
Proof.
intros x Hc Hn. pose proof (hk_pod x Hc Hn) as (HP0 & _ & Hl & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hoff).
destruct (Z_le_gt_dec (hx_sp x) (hx_P x)) as [Hge|Hlt]; [right; exact Hge|left].
destruct (Z_le_gt_dec (hx_P x + hx_len x) (hx_sp x - T_parse_STK)) as [Hle|Hgt]; [exact Hle|].
exfalso. apply (Hoff (Z.max (hx_P x) (hx_sp x - T_parse_STK))); unfold hx_sp, T_parse_STK, T_PARSE_FRAME, ESTACK in *; lia.
Qed.

(* out: the block of 3 (cap + 1) bytes the harness made for this call *)
Lemma hk_out : forall x, call_ok x ->
0 <= hx_cap x <= 9 /\ hx_O x <> 0 /\ In (hx_O x, 3 * (hx_cap x + 1)) (ablocks B (hx_lyc x) (hx_Sc x)) /\
~ In (hx_O x, 3 * (hx_cap x + 1)) (ablocks B (hx_ly x) (hx_S x)) /\
hx_O x mod 16 = 0 /\ 4096 <= hx_O x /\ hx_O x + 3 * (hx_cap x + 1) <= alloc_ceiling /\
in_app (hx_O x) (3 * (hx_cap x + 1)) /\
range_addressable (hx_view x (hx_memc x)) SHADOW_OFF (hx_O x) (3 * (hx_cap x + 1)) /\
hd_off_stack (hx_regs x) T_parse_STK (hx_O x) (3 * (hx_cap x + 1)) /\
(forall a, hx_O x <= a < hx_O x + 3 * (hx_cap x + 1) ->
  awr_byte (hx_STK x) (hx_sp0 x) (hx_FP x) (ablocks B (hx_ly x) (hx_S x)) (ablocks B (hx_lyc x) (hx_Sc x))
    (hx_lyc x) (hx_own x) a /\
  apresent (w_H (hx_W x)) (hx_memc x) a /\ ~ aowned B (hx_lyc x) (hx_Sc x) a /\ ~ in_img segs a).
Proof.
intros x Hc. pose proof (hk_call_args x Hc) as (_ & Hcap & (HO0 & HOin & HOout) & HOra & HOoff & _).
pose proof (hk_call_AR x Hc) as HAR.
destruct (al_blocks _ _ (AR_laws_ok segs B) _ _ _ _ _ _ _ HAR HOin) as (H16 & H4096 & Hceil & Happ & Hbytes & _).
assert (Hrs : req_size (3 * (hx_cap x + 1)) = 3 * (hx_cap x + 1))
by (unfold req_size; destruct (Z.eqb_spec (3 * (hx_cap x + 1)) 0); lia).
rewrite Hrs in Hceil, Happ, Hbytes.
split; [exact Hcap|]. split; [exact HO0|]. split; [exact HOin|]. split; [exact HOout|].
split; [exact H16|]. split; [exact H4096|]. split; [exact Hceil|]. split; [exact Happ|].
split; [exact HOra|]. split; [exact HOoff|].
intros a Ha. destruct (Hbytes a Ha) as [Hpr Hown].
split; [|split; [exact Hpr|split; [exact Hown|]]].
- replace a with (hx_O x + (a - hx_O x)) by lia.
  apply (hd_fresh_awr _ _ _ _ _ _ _ (hx_O x) (3 * (hx_cap x + 1))); [exact HOin | exact HOout | rewrite Hrs; lia].
- refine (proj2 (al_client_img _ _ (AR_laws_ok segs B) _ _ _ _ _ a HAR _)).
  left. exists (hx_O x), (3 * (hx_cap x + 1)). split; [exact HOin | rewrite Hrs; lia].
Qed.

(* res, when res <> 0: in the caller's stack window or in a side-stack frame the caller holds *)
Lemma hk_res : forall x, call_ok x -> hx_R x <> 0 ->
hx_R x mod 4 = 0 /\ range_addressable (hx_view x (hx_memc x)) SHADOW_OFF (hx_R x) 12 /\
(hx_sp x <= hx_R x \/ hx_R x + 12 <= hx_sp x - T_parse_STK) /\
(forall a, hx_R x <= a < hx_R x + 12 ->
  awr_byte (hx_STK x) (hx_sp0 x) (hx_FP x) (ablocks B (hx_ly x) (hx_S x)) (ablocks B (hx_lyc x) (hx_Sc x))
    (hx_lyc x) (hx_own x) a /\
  ~ in_img segs a /\ ((alloc_ceiling <= a < 2 ^ 47) \/ app_addr a)).
Proof.
intros x Hc HR0. pose proof (hk_call_args x Hc) as (_ & _ & _ & _ & _ & HR & _).
destruct HR as [HR|(Hwc & Hal & Hra)]; [contradiction|].
destruct Hwc as [Hloc Hside].
pose proof (hk_stack x Hc) as HS. pose proof (hk_call_AR x Hc) as HAR. pose proof (hk_call_journal x Hc) as HJ.
split; [exact Hal|]. split; [exact Hra|]. split; [exact Hside|].
intros a Ha.
destruct Hloc as [Hst | (cid & pos & Hin & Hcid & Hf1 & Hf2)].
- split; [left; lia|]. split.
  + intros Hi. pose proof (segs_low a Hi) as Hlow. pose proof alloc_ceiling_value as [[C1 C2] _].
    unfold kLowMemEnd in Hlow. lia.
  + left. lia.
- assert (HinF : In (cid, pos) (frames (hx_Sc x))).
  { pose proof HJ as (_ & _ & _ & _ & _ & Hfr & _). rewrite Hfr. apply in_or_app. left. exact Hin. }
  split.
  { right; right; right. exists cid, pos. split; [exact Hin|]. left. unfold in_zr. cbn [fst snd]. lia. }
  split.
  + refine (proj2 (al_client_img _ _ (AR_laws_ok segs B) _ _ _ _ _ a HAR _)).
    right. left. exists cid, pos. split; [exact HinF | lia].
  + right. destruct (al_frames _ _ (AR_laws_ok segs B) _ _ _ _ _ cid pos HAR HinF) as (_ & Happ & _).
    exact (in_app_addr _ _ a Happ ltac:(lia)).
Qed.

(* ======================================= 2. a cut ======================================= *)
(* the registers every cut keeps (hp_core's last nine conjuncts, in its order) *)
Definition hk_cregs (x : @hp_ctx segs) (regs : bvmap 5 word) : Prop :=
getr regs 2 = w64 (hx_spa x) /\ getr regs 8 = w64 (hx_sp x) /\
getr regs 3 = getr (hx_regs x) 3 /\ getr regs 4 = getr (hx_regs x) 4 /\
getr regs 9 = w64 (hx_R x) /\ getr regs 18 = w64 (hx_cap x) /\ getr regs 19 = w64 (hx_O x) /\
getr regs 26 = w64 (hx_shf x) /\ getr regs 27 = w64 SHADOW_OFF.

Lemma hk_core_cregs : forall x pat cl rb regs mem md, hp_core B x pat cl rb regs mem md -> hk_cregs x regs.
Proof. intros x pat cl rb regs mem md (_ & _ & _ & _ & _ & _ & _ & H). exact H. Qed.

Lemma hk_cregs_same : forall x (regs regs2 : bvmap 5 word), hk_cregs x regs ->
getr regs2 2 = getr regs 2 -> getr regs2 3 = getr regs 3 -> getr regs2 4 = getr regs 4 ->
getr regs2 8 = getr regs 8 -> getr regs2 9 = getr regs 9 -> getr regs2 18 = getr regs 18 ->
getr regs2 19 = getr regs 19 -> getr regs2 26 = getr regs 26 -> getr regs2 27 = getr regs 27 ->
hk_cregs x regs2.
Proof.
intros x regs regs2 (H2 & H8 & H3 & H4 & H9 & H18 & H19 & H26 & H27) E2 E3 E4 E8 E9 E18 E19 E26 E27.
unfold hk_cregs. repeat split; congruence.
Qed.

(* the core with other registers that keep the nine *)
Lemma hk_core_regs : forall x pat cl rb regs mem md regs2, hp_core B x pat cl rb regs mem md -> hk_cregs x regs2 ->
hp_core B x pat cl rb regs2 mem md.
Proof.
intros x pat cl rb regs mem md regs2 (H1 & H2 & H3 & H4 & H5 & H6 & H7 & _) Hr.
exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 Hr))))))).
Qed.

(* the core after the model's lazy backing was materialized (SRr_msteps) *)
Lemma hk_core_wvb : forall x pat cl rb regs mem md X, hp_core B x pat cl rb regs mem md ->
hp_core B x pat cl rb regs mem (with_vm_backing (m_vm_lazy md) X md).
Proof.
intros x pat cl rb regs mem md X ((HJ & OK & HP) & Hio & REST).
split; [unfold hjournal; split; [|split; [exact OK | exact HP]]|].
- eapply ajournal_materialize; first [exact (AR_laws_ok segs B) | exact segs_low | exact HJ].
- split; [|exact REST]. eapply same_io_trans; [exact Hio|].
  apply same_io_materialized. apply same_but_materialized_wvb_any.
Qed.

Lemma hk_core_journal : forall x pat cl rb regs mem md, hp_core B x pat cl rb regs mem md ->
ajournal segs B (hx_STK x) (hx_sp0 x) (hx_FP x) (hx_ly x) (hx_S x) (hx_W0 x) (hx_mem0 x) (hx_md0 x) (hx_own x)
  (hx_lyc x) (hx_Sc x) (hx_W x) (unpoison (hU (hx_fr x) pat) mem) md (hx_k x) /\
hstack_ok (hx_lyc x) (hx_fr x) pat /\ hpat segs (hx_W x) mem (hx_fr x) pat.
Proof. intros x pat cl rb regs mem md (HJ & _). exact HJ. Qed.

Lemma hk_core_io : forall x pat cl rb regs mem md, hp_core B x pat cl rb regs mem md -> same_io (hx_mdc x) md.
Proof. intros x pat cl rb regs mem md (_ & H & _). exact H. Qed.

Lemma hk_core_saved : forall x pat cl rb regs mem md, hp_core B x pat cl rb regs mem md -> hp_saved_ok x mem.
Proof. intros x pat cl rb regs mem md (_ & _ & _ & H & _). exact H. Qed.

Lemma hk_core_cells : forall x pat cl rb regs mem md, hp_core B x pat cl rb regs mem md ->
garr8 segs (hx_rd x mem) (hx_O x) (hd_zbytes (ha_cells_bytes cl)) /\
(hx_R x <> 0 -> garr8 segs (hx_rd x mem) (hx_R x) (hd_zbytes rb)) /\
(exists ev', rd32 (hx_view x mem) (as_errno B) ev').
Proof. intros x pat cl rb regs mem md (_ & _ & _ & _ & H1 & H2 & H3 & _). exact (conj H1 (conj H2 H3)). Qed.

(* a byte the parse does not hold (role's kept_view) *)
Lemma hk_kept : forall x pat cl rb regs mem md, hp_core B x pat cl rb regs mem md ->
forall a, 0 <= a < 2 ^ 64 -> ~ (hx_sp x - T_parse_STK <= a < hx_sp x) -> ~ hp_hole x a ->
~ hp_pw B x (Z.of_nat (length cl)) a -> hx_view x mem a = hx_view x (hx_memc x) a.
Proof. intros x pat cl rb regs mem md (_ & _ & HK & _). exact HK. Qed.

(* a shadow byte below kHighShadowEnd that is not a hole byte is kept *)
Lemma hk_kept_sh : forall x pat cl rb regs mem md s, api_env segs B -> call_ok x ->
hp_core B x pat cl rb regs mem md -> Z.of_nat (length cl) <= hx_cap x + 1 ->
SHADOW_OFF <= s < kHighShadowEnd -> ~ hp_hole x s ->
hx_view x mem s = hx_view x (hx_memc x) s.
Proof.
intros x pat cl rb regs mem md s Henv Hc HC Hcl Hs Hh.
pose proof (hk_stack x Hc) as (S1 & S2 & S3 & _).
pose proof (hk_out x Hc) as (_ & _ & _ & _ & _ & _ & HOc & HOapp & _).
pose proof alloc_ceiling_value as [[C1 C2] _]. destruct Henv as [[He0 He1] _].
apply (hk_kept x pat cl rb regs mem md HC s); [unfold kHighShadowEnd, SHADOW_OFF in *; lia | | exact Hh |].
- intros Hw. unfold kHighShadowEnd in *. lia.
- intros [Ho | [(HR0 & HR) | He]].
  + unfold in_app, ASAN_CEIL, kLowShadowBeg, kHighMemBeg, kHighShadowEnd, SHADOW_OFF in *. lia.
  + destruct (hk_res x Hc HR0) as (_ & _ & _ & Hr). destruct (Hr s HR) as (_ & _ & [Hst | Happ]).
    * unfold kHighShadowEnd in *. lia.
    * unfold app_addr, ASAN_CEIL, kLowShadowBeg, kHighMemBeg, kHighShadowEnd, SHADOW_OFF in *. lia.
  + unfold kLowMemEnd, SHADOW_OFF in *. lia.
Qed.

(* an image byte outside the errno cell is kept *)
Lemma hk_kept_img : forall x pat cl rb regs mem md a, call_ok x ->
hp_core B x pat cl rb regs mem md -> Z.of_nat (length cl) <= hx_cap x + 1 ->
in_img segs a -> ~ (as_errno B <= a < as_errno B + 4) -> hx_view x mem a = hx_view x (hx_memc x) a.
Proof.
intros x pat cl rb regs mem md a Hc HC Hcl Hi He.
pose proof (segs_low a Hi) as Hlow.
pose proof (hk_out x Hc) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hob).
pose proof alloc_ceiling_value as [[C1 C2] _].
apply (hk_kept x pat cl rb regs mem md HC a); [unfold kLowMemEnd in Hlow; lia | | |].
- intros Hw. pose proof (hk_window_band x a Hc Hw). unfold kLowMemEnd in Hlow. lia.
- intros Hh. pose proof (hk_hole_band x a Hc Hh). unfold kLowMemEnd, SHADOW_OFF in *. lia.
- intros [Ho | [(HR0 & HR) | He']].
  + destruct (Hob a ltac:(lia)) as (_ & _ & _ & Hni). exact (Hni Hi).
  + destruct (hk_res x Hc HR0) as (_ & _ & _ & Hr). destruct (Hr a HR) as (_ & Hni & _). exact (Hni Hi).
  + exact (He He').
Qed.

(* a byte readable at the call stays readable at a cut outside the window and the hole: out, res and the errno
   cell are readable through the cut's own facts *)
Lemma hk_some_at_cut : forall x pat cl rb regs mem md a, hp_core B x pat cl rb regs mem md -> length rb = 12%nat ->
0 <= a < 2 ^ 64 -> ~ (hx_sp x - T_parse_STK <= a < hx_sp x) -> ~ hp_hole x a ->
hx_view x (hx_memc x) a <> None -> hx_view x mem a <> None.
Proof.
intros x pat cl rb regs mem md a HC Hrb Ha Hw Hh Hn.
pose proof (hk_kept x pat cl rb regs mem md HC a Ha Hw Hh) as HK.
destruct HC as (_ & _ & _ & _ & HO & HR & (ev' & HE) & _).
assert (Hd : forall lo hi, {lo <= a < hi} + {~ (lo <= a < hi)}).
{ intros lo hi. destruct (Z_le_gt_dec lo a); destruct (Z_lt_ge_dec a hi); [left; lia | right; lia | right; lia | right; lia]. }
assert (Hsome : forall b (l : list Z), garr8 segs (hx_rd x mem) b l -> b <= a < b + Z.of_nat (length l) ->
  hx_view x mem a <> None).
{ intros b l Hg Hb. pose proof (garr8_mbyte segs (hx_rd x mem) b l (Z.to_nat (a - b)) Hg ltac:(lia)) as M.
  rewrite Z2Nat.id in M by lia. replace (b + (a - b)) with a in M by lia.
  unfold hx_view, aview. change (mrestrict (w_H (hx_W x)) mem) with (hx_rd x mem). rewrite M. discriminate. }
destruct (Hd (hx_O x) (hx_O x + 3 * Z.of_nat (length cl))) as [Io|Io].
{ apply (Hsome _ _ HO). unfold hd_zbytes. rewrite length_map, length_ha_cells_bytes. lia. }
assert (Hr : ~ (hx_R x <> 0 /\ hx_R x <= a < hx_R x + 12) \/ (hx_R x <> 0 /\ hx_R x <= a < hx_R x + 12)).
{ destruct (Z.eq_dec (hx_R x) 0); [left; tauto|]. destruct (Hd (hx_R x) (hx_R x + 12)); [right | left]; tauto. }
destruct Hr as [Hr|(R0 & Ir)].
2:{ apply (Hsome _ _ (HR R0)). unfold hd_zbytes. rewrite length_map, Hrb. lia. }
destruct (Hd (as_errno B) (as_errno B + 4)) as [Ie|Ie].
{ replace a with (as_errno B + Z.of_nat (Z.to_nat (a - as_errno B))) by lia.
  rewrite (HE (Z.to_nat (a - as_errno B)) ltac:(lia)). discriminate. }
rewrite HK; [exact Hn|]. intros [H1|[H2|H3]]; [exact (Io H1) | exact (Hr H2) | exact (Ie H3)].
Qed.

(* the pod, its shadow and its hull are as at the call at every cut (role's pod_at_cut) *)
Lemma hk_pod_at_cut : forall x pat cl rb regs mem md, api_env segs B -> call_ok x -> hx_null x = 0 ->
hp_core B x pat cl rb regs mem md -> Z.of_nat (length cl) <= hx_cap x + 1 ->
garr8 segs (hx_rd x mem) (hx_P x) (hd_zbytes (hx_bs x)) /\
range_addressable (hx_view x mem) SHADOW_OFF (hx_P x) (hx_len x) /\
shadow_hull_vis (hx_view x mem) (hx_P x) (hx_len x).
Proof.
intros x pat cl rb regs mem md Henv Hc Hn HC Hcl.
pose proof (hk_pod x Hc Hn) as (HP0 & HP16 & Hl8 & Hl8m & HSZ & HP63 & HG & Hin & HdO & HdR & HdE & HRA & HHV & HAM & HOFF).
pose proof (hk_pod_side x Hc Hn) as Hside.
pose proof (hk_frame_win x Hc) as (W1 & W2 & W3 & W4 & W5).
assert (Ll : length (hd_zbytes (hx_bs x)) = length (hx_bs x)) by (unfold hd_zbytes; apply length_map).
assert (KP : forall a, hx_P x <= a < hx_P x + hx_len x ->
  aview segs (w_H (hx_W x)) mem a = aview segs (w_H (hx_W x)) (hx_memc x) a).
{ intros a Ha. apply (hk_kept x pat cl rb regs mem md HC a).
  - destruct HAM as [HL|[HH1 HH2]]; unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia.
  - intros Hw. exact (HOFF a Ha Hw).
  - intros Hh. pose proof (hk_hole_band x a Hc Hh) as HB.
    destruct HAM as [HL|[HH1 HH2]]; unfold kLowMemEnd, kHighMemBeg, kHighShadowEnd, SHADOW_OFF in *; lia.
  - intros [Ho|[(HR0 & Hr)|He]]; lia. }
assert (Hbig : hx_P x + hx_len x < kHighMemEnd)
by (destruct HAM as [HL|[HH1 HH2]]; unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia).
split; [|split].
- intros j Hj. rewrite Ll in Hj. destruct (HG j ltac:(rewrite Ll; exact Hj)) as [Hv Hr]. split; [|exact Hr].
  apply (val_mem_kept segs (w_H (hx_W x)) (w_H (hx_W x)) (hx_memc x) mem); [|exact Hv].
  intros k Hk. apply KP. unfold hx_len. lia.
- intros a Ha. destruct (HRA a Ha) as (s & Hs & Hok). exists s. split; [|exact Hok].
  rewrite <- Hs. unfold shadow_of_addr.
  apply (hk_kept_sh x pat cl rb regs mem md (SHADOW_OFF + a / 8) Henv Hc HC Hcl).
  + unfold kHighMemEnd, kHighShadowEnd, SHADOW_OFF in *. lia.
  + change (SHADOW_OFF + a / 8) with (shadow_addr a). apply hk_sh_not_hole; [exact Hc|].
    intros Hfa. apply (HOFF a Ha). unfold hx_sp in *. lia.
- intros s Hs Hnone. apply (HHV s Hs).
  rewrite <- (hk_kept_sh x pat cl rb regs mem md s Henv Hc HC Hcl); [exact Hnone | |].
  + exact (hk_hull_band (hx_P x) (hx_len x) s ltac:(lia) ltac:(lia) Hbig Hs).
  + unfold hp_hole, hx_shf.
    exact (hk_hull_hole (hx_P x) (hx_len x) (hx_sp x) (hx_fr x) s ltac:(lia) ltac:(lia) Hside ltac:(lia) W3 Hs).
Qed.

(* the out block's shadow and presence at a cut *)
Lemma hk_out_at_cut : forall x pat cl rb regs mem md, api_env segs B -> call_ok x ->
hp_core B x pat cl rb regs mem md -> Z.of_nat (length cl) <= hx_cap x + 1 ->
range_addressable (hx_view x mem) SHADOW_OFF (hx_O x) (3 * (hx_cap x + 1)) /\
(forall a, hx_O x <= a < hx_O x + 3 * (hx_cap x + 1) -> apresent (w_H (hx_W x)) mem a).
Proof.
intros x pat cl rb regs mem md Henv Hc HC Hcl.
pose proof (hk_out x Hc) as (Hcap & HO0 & HOin & _ & _ & H4096 & HOc & HOapp & HOra & HOoff & _).
pose proof (hk_frame_win x Hc) as (W1 & W2 & W3 & W4 & W5).
pose proof alloc_ceiling_value as [[C1 C2] _].
split.
- intros a Ha. destruct (HOra a Ha) as (s & Hs & Hok). exists s. split; [|exact Hok].
  rewrite <- Hs. unfold shadow_of_addr.
  apply (hk_kept_sh x pat cl rb regs mem md (SHADOW_OFF + a / 8) Henv Hc HC Hcl).
  + unfold kHighShadowEnd, SHADOW_OFF in *. lia.
  + change (SHADOW_OFF + a / 8) with (shadow_addr a). apply hk_sh_not_hole; [exact Hc|].
    intros Hfa. apply (HOoff a Ha). unfold hx_sp in *. lia.
- intros a Ha. pose proof (hk_core_journal x pat cl rb regs mem md HC) as (HJ & OK & _).
  destruct (al_blocks _ _ (AR_laws_ok segs B) _ _ _ _ _ _ _ (proj1 HJ) HOin) as (_ & _ & _ & _ & Hbytes & _).
  assert (Hrs : req_size (3 * (hx_cap x + 1)) = 3 * (hx_cap x + 1))
  by (unfold req_size; destruct (Z.eqb_spec (3 * (hx_cap x + 1)) 0); lia).
  destruct (Hbytes a ltac:(rewrite Hrs; lia)) as [Hpr _].
  assert (HIN : in_ush (hU (hx_fr x) pat) (bv_unsigned (Z_to_bv 64 a)) = false).
  { apply in_hU_false. rewrite unsigned_lit_small by (unfold in_app, ASAN_CEIL in *; lia).
    destruct OK as (_ & _ & _ & Hhi & _). pose proof (hk_stack x Hc) as HS.
    unfold in_app, ASAN_CEIL, kLowShadowBeg, kHighMemBeg, shadow_addr, SHADOW_OFF in *. lia. }
  exact (proj1 (hp_apresent_unp (w_H (hx_W x)) (hU (hx_fr x) pat) mem a HIN) Hpr).
Qed.

(* a NUL-terminated literal of the image (HPgBase.hd_cstr) whose bytes are apart from the errno cell, at a cut *)
Lemma hk_cstr_at_cut : forall x pat cl rb regs mem md a s, api_env segs B -> call_ok x ->
hp_core B x pat cl rb regs mem md -> Z.of_nat (length cl) <= hx_cap x + 1 -> length rb = 12%nat ->
hd_cstr segs (w_H (hx_W x)) (hx_memc x) a s ->
(forall i, 0 <= i <= Z.of_nat (length s) -> ~ (as_errno B <= a + i < as_errno B + 4)) ->
hd_cstr segs (w_H (hx_W x)) mem a s.
Proof.
intros x pat cl rb regs mem md a s Henv Hc HC Hcl Hrb Hcs Herr.
destruct Hcs as (Hb & Hn & Hf & Ha0 & Hhi & Himg & Hm8 & Hra & Hhv & Htl).
assert (Hlow : a + Z.of_nat (length s) < kLowMemEnd) by exact (proj2 (segs_low _ (Himg (Z.of_nat (length s)) ltac:(lia)))).
assert (KI : forall i, 0 <= i <= Z.of_nat (length s) ->
  aview segs (w_H (hx_W x)) mem (a + i) = aview segs (w_H (hx_W x)) (hx_memc x) (a + i)).
{ intros i Hi. exact (hk_kept_img x pat cl rb regs mem md (a + i) Hc HC Hcl (Himg i Hi) (Herr i Hi)). }
assert (KS : forall b, 0 <= b < kLowMemEnd ->
  aview segs (w_H (hx_W x)) mem (shadow_addr b) = aview segs (w_H (hx_W x)) (hx_memc x) (shadow_addr b)).
{ intros b Hb'. apply (hk_kept_sh x pat cl rb regs mem md (shadow_addr b) Henv Hc HC Hcl).
  - unfold shadow_addr, kLowMemEnd, kHighShadowEnd, SHADOW_OFF in *. lia.
  - intros Hh. pose proof (hk_hole_band x _ Hc Hh) as HB. unfold shadow_addr, kLowMemEnd, SHADOW_OFF in *. lia. }
split; [intros i Hi; rewrite (KI i ltac:(lia)); exact (Hb i Hi)|].
split; [rewrite (KI (Z.of_nat (length s)) ltac:(lia)); exact Hn|].
split; [exact Hf|]. split; [exact Ha0|]. split; [exact Hhi|]. split; [exact Himg|]. split; [exact Hm8|].
split; [|split].
- intros b Hb'. destruct (Hra b Hb') as (v & Hv & Hok). exists v. split; [|exact Hok].
  rewrite <- Hv. unfold shadow_of_addr. change (SHADOW_OFF + b / 8) with (shadow_addr b). apply KS. lia.
- intros t Ht Hnone. apply (Hhv t Ht).
  change (aview segs (w_H (hx_W x)) (hx_memc x) t) with (hx_view x (hx_memc x) t).
  rewrite <- (hk_kept_sh x pat cl rb regs mem md t Henv Hc HC Hcl); [exact Hnone | |].
  + unfold shadow_addr, kLowMemEnd, kHighShadowEnd, SHADOW_OFF in *. lia.
  + intros Hh. pose proof (hk_hole_band x _ Hc Hh) as HB. unfold shadow_addr, kLowMemEnd, SHADOW_OFF in *. lia.
- intros t Ht. apply (hk_some_at_cut x pat cl rb regs mem md t HC Hrb).
  + destruct Hm8 as [HL|[HH1 HH2]]; unfold amem_range, kLowMemEnd, kHighMemBeg in *; lia.
  + intros Hw. pose proof (hk_window_band x t Hc Hw). pose proof alloc_ceiling_value as [[C1 C2] _].
    destruct Hm8 as [HL|[HH1 HH2]]; unfold kLowMemEnd, kHighMemBeg in *; lia.
  + intros Hh. pose proof (hk_hole_band x _ Hc Hh) as HB.
    destruct Hm8 as [HL|[HH1 HH2]]; unfold kLowMemEnd, kHighMemBeg, SHADOW_OFF in *; lia.
  + exact (Htl t Ht).
Qed.

(* the 8-byte constant cells (HPgBase.hd_ro_cells), each in the image and apart from the errno cell, at a cut *)
Lemma hk_ro_cells_at_cut : forall x pat cl rb regs mem md cs, call_ok x ->
hp_core B x pat cl rb regs mem md -> Z.of_nat (length cl) <= hx_cap x + 1 ->
hd_ro_cells segs (w_H (hx_W x)) (hx_memc x) cs ->
Forall (fun c => forall k, 0 <= k < 8 -> in_img segs (fst c + k) /\ ~ (as_errno B <= fst c + k < as_errno B + 4)) cs ->
hd_ro_cells segs (w_H (hx_W x)) mem cs.
Proof.
intros x pat cl rb regs mem md cs Hc HC Hcl Hro Hloc. unfold hd_ro_cells in *.
rewrite Forall_forall in *. intros c Hin.
apply (val_mem_kept segs (w_H (hx_W x)) (w_H (hx_W x)) (hx_memc x) mem); [|exact (Hro c Hin)].
intros k Hk. destruct (Hloc c Hin k ltac:(lia)) as [Hi He].
exact (hk_kept_img x pat cl rb regs mem md (fst c + k) Hc HC Hcl Hi He).
Qed.

(* an 8-byte word whose bytes are kept *)
Lemma hk_rdword_kept : forall (rd rd' : reader) a v, (forall k, 0 <= k < 8 -> rd' (a + k) = rd (a + k)) ->
rdword rd a = Some v -> rdword rd' a = Some v.
Proof.
intros rd rd' a v HK Hw.
assert (H0 : rd' a = rd a) by (pose proof (HK 0 ltac:(lia)) as H; rewrite Z.add_0_r in H; exact H).
unfold rdword in *.
rewrite H0, (HK 1 ltac:(lia)), (HK 2 ltac:(lia)), (HK 3 ltac:(lia)), (HK 4 ltac:(lia)), (HK 5 ltac:(lia)),
  (HK 6 ltac:(lia)), (HK 7 ltac:(lia)).
exact Hw.
Qed.

(* ---------------------------------- the shadow entries (role's shent_pod) ---------------------------------- *)
(* the instrumented check of [p + lo, p + hi) inside a range [a, a + n) marked usable, s11 (atom 27) the shadow
   offset and atom m holding p *)
Lemma hk_shent_of_ra : forall H mem E (m : nat) a n p lo hi,
range_addressable (aview segs H mem) SHADOW_OFF a n ->
ew E 27 = w64 SHADOW_OFF -> ew E m = w64 p -> 0 <= p < 2 ^ 64 -> a <= p + lo -> lo <= hi -> p + hi <= a + n ->
(forall b, p + lo <= b < p + hi -> b < SHADOW_OFF \/ SHADOW_OFF + 17592186044416 <= b) ->
shent_ok segs (SOff 27 0) E (mrestrict H mem) (mkSHE m lo hi).
Proof.
intros H mem E m a n p lo hi Hra E27 Em Hp Hlo Hlh Hhi Hap.
apply (shent_ok_of_range segs H mem E (SOff 27 0) m a n p lo hi Hra).
- apply U_atom; [exact E27 | unfold SHADOW_OFF; lia].
- apply U_atom; [exact Em | exact Hp].
- exact Hlo.
- exact Hhi.
- intros b Hb. rewrite Z.min_l, Z.max_r in Hb by lia. specialize (Hap b Hb). lia.
Qed.

(* res's check (instrumented `sw` at res + 0, 4, 8) *)
Lemma hk_shent_res : forall x H mem E (m : nat) lo hi, call_ok x -> hx_R x <> 0 ->
ew E 27 = w64 SHADOW_OFF -> ew E m = w64 (hx_R x) ->
range_addressable (aview segs H mem) SHADOW_OFF (hx_R x) 12 -> 0 <= lo -> lo <= hi <= 12 ->
shent_ok segs (SOff 27 0) E (mrestrict H mem) (mkSHE m lo hi).
Proof.
intros x H mem E m lo hi Hc HR0 E27 Em Hra Hlo Hhi.
destruct (hk_res x Hc HR0) as (_ & _ & _ & Hr).
pose proof alloc_ceiling_value as [[C1 C2] _].
assert (HR1 : 0 <= hx_R x /\ hx_R x + 12 <= 2 ^ 47).
{ destruct (Hr (hx_R x) ltac:(lia)) as (_ & _ & [Hs|Ha]); destruct (Hr (hx_R x + 11) ltac:(lia)) as (_ & _ & [Hs'|Ha']);
  unfold app_addr, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; lia. }
apply (hk_shent_of_ra H mem E m (hx_R x) 12 (hx_R x) lo hi Hra E27 Em); [lia | lia | lia | lia |].
intros b Hb. destruct (Hr b ltac:(lia)) as (_ & _ & [Hs|Hap]);
unfold app_addr, ASAN_CEIL, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *; lia.
Qed.

(* the pod's checks at the atom m holding P + o *)
Lemma hk_shent_pod : forall x H mem E (m : nat) o lo hi, call_ok x -> hx_null x = 0 ->
ew E 27 = w64 SHADOW_OFF -> ew E m = w64 (hx_P x + o) ->
range_addressable (aview segs H mem) SHADOW_OFF (hx_P x) (hx_len x) ->
0 <= o <= hx_len x -> 0 <= o + lo -> lo <= hi -> o + hi <= hx_len x ->
shent_ok segs (SOff 27 0) E (mrestrict H mem) (mkSHE m lo hi).
Proof.
intros x H mem E m o lo hi Hc Hn E27 Em Hra Ho0 Hlo Hlh Hhi.
pose proof (hk_pod x Hc Hn) as (HP0 & _ & Hl8 & _ & _ & HP63 & _ & _ & _ & _ & _ & _ & _ & HAM & _).
assert (Ho : 0 <= hx_P x + o < 2 ^ 64).
{ destruct HAM as [HL|[HH1 HH2]]; unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia. }
apply (hk_shent_of_ra H mem E m (hx_P x) (hx_len x) (hx_P x + o) lo hi Hra E27 Em Ho); [lia | exact Hlh | lia |].
intros b Hb. destruct HAM as [HL|[HH1 HH2]]; unfold kLowMemEnd, kHighMemBeg, kHighMemEnd, SHADOW_OFF in *; lia.
Qed.

(* ---------------------------------- the string premises (HPgCallsStr.v) ---------------------------------- *)
(* The bytes of a garr8 list are readable. *)
Lemma hk_garr8_some : forall H mem a (s : list Z), garr8 segs (mrestrict H mem) a s ->
forall b, a <= b < a + Z.of_nat (length s) -> aview segs H mem b <> None.
Proof.
intros H mem a s Hg b Hb.
pose proof (garr8_mbyte segs (mrestrict H mem) a s (Z.to_nat (b - a)) Hg ltac:(lia)) as M.
rewrite Z2Nat.id in M by lia. replace (a + (b - a)) with b in M by lia.
unfold aview. rewrite M. discriminate.
Qed.

(* Bytes known through the reader make a garr8 list. *)
Lemma hk_garr8_of_aview : forall H mem a (s : list Z), Forall (fun v => 0 <= v < 256) s ->
(forall i, 0 <= i < Z.of_nat (length s) -> aview segs H mem (a + i) = Some (nth (Z.to_nat i) s 0)) ->
garr8 segs (mrestrict H mem) a s.
Proof.
intros H mem a s Hf Hv j Hj.
pose proof (proj1 (Forall_forall _ _) Hf (nth j s 0) ltac:(apply nth_In; exact Hj)) as Hr. cbv beta in Hr.
split; [|exact Hr].
intros kk Hk. assert (kk = 0%nat) as -> by lia. cbn [Z.of_nat]. rewrite Z.add_0_r.
pose proof (Hv (Z.of_nat j) ltac:(lia)) as V. rewrite Nat2Z.id in V.
apply aview_byte in V as (b & Hb & Hvb & _). rewrite Hb. f_equal.
unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
change (2 ^ 8) with 256. rewrite !Z.mod_small by lia. rewrite Hvb. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

Lemma hk_bytes_pos : forall s : list Z, Forall (fun v => 0 < v < 256) s -> Forall (fun v => 0 <= v < 256) s.
Proof. intros s H. rewrite Forall_forall in *. intros v Hv. specialize (H v Hv). lia. Qed.

(* A list of bytes whose values are all nonzero holds no NUL. *)
Lemma hk_notin0 : forall l : list byte, Forall (fun v => 0 < v < 256) (hd_zbytes l) -> ~ In (Z_to_bv 8 0) l.
Proof.
intros l H Hin. unfold hd_zbytes in H. rewrite Forall_forall in H.
specialize (H _ (in_map (fun b : byte => bv_unsigned b) _ _ Hin)). cbv beta in H.
assert (E : bv_unsigned (Z_to_bv 8 0) = 0) by reflexivity. rewrite E in H. lia.
Qed.

(* The facts of a C string l at a give the wrappers' string premises at regs, mem and its len + 8 range. *)
Lemma hk_awrap_of : forall (W : world segs) (regs : bvmap 5 word) mem a (l : list byte),
0 < a -> ~ In (Z_to_bv 8 0) l -> Z.of_nat (length l) + 1 < 2 ^ 32 ->
garr8 segs (mrestrict (w_H W) mem) a (hd_zbytes l ++ [0]) ->
hd_off_stack regs (2 * ESTACK) a (Z.of_nat (length l) + 1) ->
amem_range a (Z.of_nat (length l) + 8) ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF a (Z.of_nat (length l) + 1) ->
shadow_hull_vis (aview segs (w_H W) mem) a (Z.of_nat (length l) + 1) ->
hd_str_tail (aview segs (w_H W) mem) (a + Z.of_nat (length l)) ->
(0 < a /\ ~ In (Z_to_bv 8 0) l /\
 Z.of_nat (length l) + 1 < 2 ^ 32 /\ a + Z.of_nat (length l) + 1 <= 2 ^ 63 /\
 garr8 segs (mrestrict (w_H W) mem) a (map (fun b : byte => bv_unsigned b) l ++ [0]) /\
 src_ok segs W regs mem a (Z.of_nat (length l) + 1) /\
 (forall b, a <= b <= a + Z.of_nat (length l) -> ~ (spZ regs - 2 * ESTACK <= b < spZ regs)) /\
 amem_range a (Z.of_nat (length l) + 1) /\
 range_addressable (aview segs (w_H W) mem) SHADOW_OFF a (Z.of_nat (length l) + 1) /\
 shadow_hull_vis (aview segs (w_H W) mem) a (Z.of_nat (length l) + 1) /\
 (forall b, a + Z.of_nat (length l) < b < a + Z.of_nat (length l) - (a + Z.of_nat (length l)) mod 8 + 8 ->
  aview segs (w_H W) mem b <> None)) /\
amem_range a (Z.of_nat (length l) + 8).
Proof.
intros W regs mem a l Ha0 Hnz Hlen Hg Hoff Hm8 Hra Hhv Htl.
unfold hd_off_stack in Hoff.
assert (Lz : length (hd_zbytes l ++ [0]) = S (length l))
by (unfold hd_zbytes; rewrite length_app, length_map; cbn [length]; lia).
assert (ESTACK = 4096) as Hes by reflexivity.
split; [|exact Hm8].
split; [exact Ha0|]. split; [exact Hnz|]. split; [exact Hlen|].
split; [clear - Hm8; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia|].
split; [exact Hg|].
split.
{ intros b Hb. split.
  - apply (hk_garr8_some (w_H W) mem a _ Hg). rewrite Lz. lia.
  - intros Hw. apply (Hoff b ltac:(lia)). clear - Hw Hes. lia. }
split; [intros b Hb; apply Hoff; lia|].
split; [eapply hd_amem_range_le; [|exact Hm8]; lia|].
split; [exact Hra|]. split; [exact Hhv|].
exact Htl.
Qed.

(* A literal of the image as HPgBase.hd_cstr states it, outside the wrapper's window. *)
Lemma hk_awrap_cstr : forall (W : world segs) (regs : bvmap 5 word) mem a (l : list byte),
hd_cstr segs (w_H W) mem a (hd_zbytes l) ->
hd_off_stack regs (2 * ESTACK) a (Z.of_nat (length l) + 1) ->
(0 < a /\ ~ In (Z_to_bv 8 0) l /\
 Z.of_nat (length l) + 1 < 2 ^ 32 /\ a + Z.of_nat (length l) + 1 <= 2 ^ 63 /\
 garr8 segs (mrestrict (w_H W) mem) a (map (fun b : byte => bv_unsigned b) l ++ [0]) /\
 src_ok segs W regs mem a (Z.of_nat (length l) + 1) /\
 (forall b, a <= b <= a + Z.of_nat (length l) -> ~ (spZ regs - 2 * ESTACK <= b < spZ regs)) /\
 amem_range a (Z.of_nat (length l) + 1) /\
 range_addressable (aview segs (w_H W) mem) SHADOW_OFF a (Z.of_nat (length l) + 1) /\
 shadow_hull_vis (aview segs (w_H W) mem) a (Z.of_nat (length l) + 1) /\
 (forall b, a + Z.of_nat (length l) < b < a + Z.of_nat (length l) - (a + Z.of_nat (length l)) mod 8 + 8 ->
  aview segs (w_H W) mem b <> None)) /\
amem_range a (Z.of_nat (length l) + 8).
Proof.
intros W regs mem a l Hc Hoff.
assert (Ll : length (hd_zbytes l) = length l) by (unfold hd_zbytes; apply length_map).
destruct Hc as (Hb & Hn & Hf & Ha0 & _ & Himg & Hm8 & Hra & Hhv & Htl).
rewrite Ll in Hn, Himg, Hm8, Hra, Hhv, Htl.
assert (Hlow : a + Z.of_nat (length l) < kLowMemEnd)
by (exact (proj2 (segs_low _ (Himg (Z.of_nat (length l)) ltac:(lia))))).
apply hk_awrap_of.
- exact Ha0.
- exact (hk_notin0 l Hf).
- clear - Hlow Ha0. unfold kLowMemEnd in Hlow. lia.
- apply (proj2 (garr8_app segs _ a (hd_zbytes l) [0])). split.
  + exact (hk_garr8_of_aview (w_H W) mem a (hd_zbytes l) (hk_bytes_pos _ Hf) Hb).
  + rewrite Ll. apply hk_garr8_of_aview; [constructor; [cbv beta; lia | constructor]|].
    intros i Hi. cbn [length Z.of_nat] in Hi. assert (i = 0) as -> by lia. rewrite Z.add_0_r. exact Hn.
- exact Hoff.
- exact Hm8.
- exact Hra.
- exact Hhv.
- exact Htl.
Qed.

(* A shadow hull shrinks to a sub-range. *)
Lemma hk_hull_sub : forall (rd : reader) p n y k, shadow_hull_vis rd p n -> p <= y -> y + k <= p + n -> 0 < k ->
shadow_hull_vis rd y k.
Proof.
intros rd p n y k H Hxy Hyk Hk s Hs. apply H.
pose proof (shadow_mono p y Hxy) as M1. pose proof (shadow_mono (y + k - 1) (p + n - 1) ltac:(lia)) as M2.
assert (R8 : forall u v, u <= v -> u / 8 * 8 <= v / 8 * 8)
by (intros u v Huv; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
pose proof (R8 _ _ M1) as N1. pose proof (R8 _ _ M2) as N2. clear - Hs N1 N2. lia.
Qed.

(* A range kept out of one stack window is kept out of a smaller one inside it, for a sub-range. *)
Lemma hk_off_stack_sub : forall (regs regs' : bvmap 5 word) T T' p n p' n',
hd_off_stack regs T p n -> spZ regs - T <= spZ regs' - T' -> spZ regs' <= spZ regs -> p <= p' -> p' + n' <= p + n ->
hd_off_stack regs' T' p' n'.
Proof. intros regs regs' T T' p n p' n' H H1 H2 H3 H4 x Hx Hw. apply (H x ltac:(lia)). lia. Qed.

(* A C string inside a range [P, P + n) held in the form hd_parse_args states the pod: the key the strncmp call reads. *)
Lemma hk_awrap_sub : forall (W : world segs) (regs : bvmap 5 word) mem (P n a : Z) (l : list byte),
0 < P -> n < 2 ^ 32 -> P <= a -> a + Z.of_nat (length l) + 1 <= P + n ->
amem_range P (n + 8) ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF P n ->
shadow_hull_vis (aview segs (w_H W) mem) P n ->
hd_off_stack regs (2 * ESTACK) P n ->
garr8 segs (mrestrict (w_H W) mem) a (hd_zbytes l ++ [0]) ->
~ In (Z_to_bv 8 0) l ->
hd_str_tail (aview segs (w_H W) mem) (a + Z.of_nat (length l)) ->
(0 < a /\ ~ In (Z_to_bv 8 0) l /\
 Z.of_nat (length l) + 1 < 2 ^ 32 /\ a + Z.of_nat (length l) + 1 <= 2 ^ 63 /\
 garr8 segs (mrestrict (w_H W) mem) a (map (fun b : byte => bv_unsigned b) l ++ [0]) /\
 src_ok segs W regs mem a (Z.of_nat (length l) + 1) /\
 (forall b, a <= b <= a + Z.of_nat (length l) -> ~ (spZ regs - 2 * ESTACK <= b < spZ regs)) /\
 amem_range a (Z.of_nat (length l) + 1) /\
 range_addressable (aview segs (w_H W) mem) SHADOW_OFF a (Z.of_nat (length l) + 1) /\
 shadow_hull_vis (aview segs (w_H W) mem) a (Z.of_nat (length l) + 1) /\
 (forall b, a + Z.of_nat (length l) < b < a + Z.of_nat (length l) - (a + Z.of_nat (length l)) mod 8 + 8 ->
  aview segs (w_H W) mem b <> None)) /\
amem_range a (Z.of_nat (length l) + 8).
Proof.
intros W regs mem P n a l HP0 Hn Hpa Hae Hm Hra Hhv Hoff Hg Hnz Htl.
unfold hd_off_stack in Hoff.
apply hk_awrap_of.
- lia.
- exact Hnz.
- lia.
- exact Hg.
- intros y Hy. apply Hoff. lia.
- clear - Hm Hpa Hae. destruct Hm as [Hl | (Hh1 & Hh2)]; unfold amem_range; [left | right; split]; lia.
- eapply range_addressable_sub; [exact Hra | lia | lia].
- exact (hk_hull_sub _ P n a (Z.of_nat (length l) + 1) Hhv Hpa ltac:(lia) ltac:(lia)).
- exact Htl.
Qed.

(* ---------------------------------- the first cut: hp_core after the entry's run ---------------------------------- *)
(* From the entry segment's run (the prologue, the hole opened with PAT_KEY, res zeroed when res <> 0): the core of
   every cut, no cell written yet. *)
Lemma hk_core_intro : forall x regs mem md, api_env segs B -> call_ok x ->
ajournal segs B (hx_STK x) (hx_sp0 x) (hx_FP x) (hx_ly x) (hx_S x) (hx_W0 x) (hx_mem0 x) (hx_md0 x) (hx_own x)
  (hx_lyc x) (hx_Sc x) (hx_W x) (unpoison (hU (hx_fr x) PAT_KEY) mem) md (hx_k x) ->
hstack_ok (hx_lyc x) (hx_fr x) PAT_KEY ->
hpat segs (hx_W x) mem (hx_fr x) PAT_KEY ->
same_io (hx_mdc x) md ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (hx_sp x - T_parse_STK <= a < hx_sp x) -> ~ hp_hole x a ->
  ~ (hx_R x <> 0 /\ hx_R x <= a < hx_R x + 12) -> hx_view x mem a = hx_view x (hx_memc x) a) ->
hp_saved_ok x mem ->
(hx_R x <> 0 -> garr8 segs (hx_rd x mem) (hx_R x) (hd_zbytes (ha_res_bytes 0 0 0))) ->
hk_cregs x regs ->
hp_core B x PAT_KEY [] (ha_res_bytes 0 0 0) regs mem md.
Proof.
intros x regs mem md Henv Hc HJ OK HP Hio HK HSV HR Hregs.
pose proof (hk_call_args x Hc) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Herr & _).
pose proof (hk_stack x Hc) as (S1 & S2 & S3 & _).
pose proof alloc_ceiling_value as [[C1 C2] _].
destruct Henv as [[He0 He1] [Heimg _]].
unfold hp_core.
split; [unfold hjournal; split; [exact HJ | split; [exact OK | exact HP]]|].
split; [exact Hio|].
split.
{ intros a Ha Hw Hh Hpw. apply (HK a Ha Hw Hh). intros Hr. apply Hpw. unfold hp_pw. right. left. exact Hr. }
split; [exact HSV|].
split; [replace (hd_zbytes (ha_cells_bytes [])) with (@nil Z) by reflexivity; intros j Hj; cbn in Hj; lia|].
split; [exact HR|].
split.
{ exists (hx_ev x). intros kk Hkk.
  rewrite (HK (as_errno B + Z.of_nat kk)); [exact (Herr kk Hkk) | unfold kLowMemEnd in *; lia | | |].
  - intros Hw. pose proof (hk_window_band x _ Hc Hw). unfold kLowMemEnd in *. lia.
  - intros Hh. pose proof (hk_hole_band x _ Hc Hh) as HB. unfold kLowMemEnd, SHADOW_OFF in *. lia.
  - intros (HR0 & Hr). destruct (hk_res x Hc HR0) as (_ & _ & _ & HRr).
    destruct (HRr _ Hr) as (_ & Hni & _). exact (Hni (Heimg (as_errno B + Z.of_nat kk) ltac:(lia))). }
exact Hregs.
Qed.

(* the read-only data the wrappers read (aro_unowned's in-segment half), at a cut *)
Lemma hk_aro_at_cut : forall x pat cl rb regs mem md, call_ok x -> hp_core B x pat cl rb regs mem md ->
Z.of_nat (length cl) <= hx_cap x + 1 ->
forall a, in_rom segs a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
aview segs (w_H (hx_W x)) mem a = option_map (fun b : byte => bv_unsigned b) (seg_rom segs (Z_to_bv 64 a)).
Proof.
intros x pat cl rb regs mem md Hc HC Hcl a Hr Ho He.
pose proof (hk_call_args x Hc) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hro & _).
assert (Hi : in_img segs a) by (destruct Hr as (sg & Hin & _ & Hb); exists sg; split; [exact Hin | exact Hb]).
change (aview segs (w_H (hx_W x)) mem a) with (hx_view x mem a).
rewrite (hk_kept_img x pat cl rb regs mem md a Hc HC Hcl Hi He).
exact (Hro a (or_introl Hr) Ho He).
Qed.

(* ======================================= 3. the engine's entry at a cut ======================================= *)
(* env slots: 0 .. 31 the registers at the cut, 32 SHADOW_OFF, 33 .. 45 the thirteen saved words (HP_SAVED's
   order: ra, s0, s1, s2 .. s11), 46 fs0's entry bits, 47 .. the segment's own values L *)
Definition hk_saved_vals x : list word := map (fun c => getr (hx_regs x) (Z_to_bv 5 (snd c))) HP_SAVED.
Definition hk_fs0 : word := Sem.reg_get (@fp_regs fx) (Z_to_bv 5 8).
Definition hk_env x (regs : bvmap 5 word) (L : list word) : env :=
Ereg regs (w64 SHADOW_OFF :: hk_saved_vals x ++ hk_fs0 :: L).

Lemma hk_env_reg : forall x regs L (n : nat) (r : bv 5), Z.of_nat n = bv_unsigned r ->
ew (hk_env x regs L) n = getr regs r.
Proof. intros x regs L n r H. unfold hk_env. apply ew_Ereg_nat. exact H. Qed.

Lemma hk_env_sb : forall x regs L, ew (hk_env x regs L) 32 = w64 SHADOW_OFF.
Proof. intros x regs L. unfold hk_env. change 32%nat with (32 + 0)%nat. rewrite ew_Ereg_extra. reflexivity. Qed.

Lemma hk_saved_nth : forall x j, (j < 13)%nat ->
nth j (hk_saved_vals x) (Z_to_bv 64 0) = getr (hx_regs x) (Z_to_bv 5 (snd (nth j HP_SAVED (0, 0)))).
Proof. intros x j Hj. unfold hk_saved_vals. do 13 (destruct j as [|j]; [reflexivity|]). lia. Qed.

Lemma hk_env_saved : forall x regs L j, (j < 13)%nat ->
ew (hk_env x regs L) (33 + j) = getr (hx_regs x) (Z_to_bv 5 (snd (nth j HP_SAVED (0, 0)))).
Proof.
intros x regs L j Hj. unfold hk_env.
replace (33 + j)%nat with (32 + S j)%nat by lia. rewrite ew_Ereg_extra. cbn [nth].
rewrite app_nth1 by (unfold hk_saved_vals; rewrite length_map; cbn [length HP_SAVED]; lia).
apply hk_saved_nth. exact Hj.
Qed.

Lemma hk_env_fs0 : forall x regs L, ew (hk_env x regs L) 46 = hk_fs0.
Proof. intros x regs L. unfold hk_env. change 46%nat with (32 + 14)%nat. rewrite ew_Ereg_extra. reflexivity. Qed.

Lemma hk_env_seg : forall x regs L j, ew (hk_env x regs L) (47 + j) = nth j L (Z_to_bv 64 0).
Proof.
intros x regs L j. unfold hk_env.
replace (47 + j)%nat with (32 + S (14 + j))%nat by lia. rewrite ew_Ereg_extra. cbn [nth].
rewrite app_nth2 by (unfold hk_saved_vals; rewrite length_map; cbn [length HP_SAVED]; lia).
unfold hk_saved_vals. rewrite length_map. cbn [length HP_SAVED].
replace (14 + j - 13)%nat with (S j) by lia. reflexivity.
Qed.

Lemma hk_U_Bx : forall x regs L, hk_cregs x regs -> U (hk_env x regs L) hk_Bx = SHADOW_OFF.
Proof.
intros x regs L (_ & _ & _ & _ & _ & _ & _ & _ & H27). unfold hk_Bx.
apply U_atom; [rewrite (hk_env_reg x regs L 27 27%bv eq_refl), H27; reflexivity | unfold SHADOW_OFF; lia].
Qed.

Lemma hk_atoms_ok : forall x regs L l, call_ok x -> hk_cregs x regs -> atoms_ok (hk_env x regs L) l ->
atoms_ok (hk_env x regs L) (hk_atoms ++ l).
Proof.
intros x regs L l Hc (H2 & H8 & _ & _ & _ & _ & _ & H26 & H27) Hl.
pose proof (hk_stack x Hc) as HS. pose proof (hk_frame_win x Hc) as HW. pose proof alloc_ceiling_value as [[C1 C2] _].
unfold hk_atoms. cbn [app atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite (hk_env_reg x regs L 2 2%bv eq_refl), (hk_env_reg x regs L 8 8%bv eq_refl),
  (hk_env_reg x regs L 26 26%bv eq_refl), (hk_env_reg x regs L 27 27%bv eq_refl), H2, H8, H26, H27.
unfold w64, hx_shf, shadow_addr.
rewrite !unsigned_lit_small by (unfold T_parse_STK, T_PARSE_FRAME, ESTACK, SHADOW_OFF in *; lia).
change (2 ^ 5) with 32. change (2 ^ 4) with 16. change (2 ^ 2) with 4. change (2 ^ 0) with 1.
split; [unfold T_parse_STK, T_PARSE_FRAME, ESTACK in *; repeat split; lia|].
split; [unfold T_parse_STK, T_PARSE_FRAME, ESTACK in *; repeat split; lia|].
split; [unfold T_parse_STK, T_PARSE_FRAME, ESTACK, SHADOW_OFF in *; repeat split; lia|].
split; [unfold SHADOW_OFF; repeat split; lia|].
exact Hl.
Qed.

(* the caller's stack window is present at a cut's memory *)
Lemma hk_present_stack : forall x pat cl rb regs mem md, call_ok x -> hp_core B x pat cl rb regs mem md ->
forall a, hx_sp0 x - hx_STK x <= a < hx_sp0 x -> apresent (w_H (hx_W x)) mem a.
Proof.
intros x pat cl rb regs mem md Hc HC a Ha.
pose proof (hk_core_journal x pat cl rb regs mem md HC) as (HJ & OK & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
pose proof (hk_stack x Hc) as HS. pose proof alloc_ceiling_value as [[C1 C2] _].
assert (HIN : in_ush (hU (hx_fr x) pat) (bv_unsigned (Z_to_bv 64 a)) = false).
{ apply in_hU_false. rewrite unsigned_lit_small by lia.
  destruct OK as (_ & _ & _ & Hhi & _). unfold shadow_addr, SHADOW_OFF in *. lia. }
exact (proj1 (hp_apresent_unp (w_H (hx_W x)) (hU (hx_fr x) pat) mem a HIN) (Hpres a Ha)).
Qed.

Lemma hk_chunk_saved : forall x regs L mem off r (j : nat), nth j HP_SAVED (0, 0) = (off, r) -> (j < 13)%nat ->
hp_saved_ok x mem ->
YP09.chunk_ok segs (hk_env x regs L) (hx_rd x mem) (hx_sp x) (YP09.mkChunk off (CVal 8 (SOff (33 + j) 0))).
Proof.
intros x regs L mem off r j Hn Hj HSV.
apply (chunk_ok_val segs (hk_env x regs L) (hx_rd x mem) (hx_sp x) off 8 (SOff (33 + j) 0)
  (bv_unsigned (getr (hx_regs x) (Z_to_bv 5 r)))).
- rewrite hk_sv_SOff0, (hk_env_saved x regs L j Hj), Hn. cbn [snd]. symmetry. apply Z_to_bv_bv_unsigned.
- apply bv_unsigned_in_range.
- lia.
- destruct HSV as [HS _]. rewrite Forall_forall in HS.
  assert (Hin : In (off, r) HP_SAVED) by (rewrite <- Hn; apply nth_In; cbn [length HP_SAVED]; lia).
  exact (HS (off, r) Hin).
Qed.

Lemma hk_chunk_fs0 : forall x regs L mem, hp_saved_ok x mem ->
YP09.chunk_ok segs (hk_env x regs L) (hx_rd x mem) (hx_sp x) (YP09.mkChunk (-112) (CVal 8 (SOff 46 0))).
Proof.
intros x regs L mem (_ & HF).
apply (chunk_ok_val segs (hk_env x regs L) (hx_rd x mem) (hx_sp x) (-112) 8 (SOff 46 0) (bv_unsigned hk_fs0)).
- rewrite hk_sv_SOff0, hk_env_fs0. symmetry. apply Z_to_bv_bv_unsigned.
- apply bv_unsigned_in_range.
- lia.
- exact HF.
Qed.

(* the saves region at s0 (role's frame_region_ok) *)
Lemma hk_saves_ok : forall x pat cl rb regs mem md L, call_ok x -> hp_core B x pat cl rb regs mem md ->
region_ok segs (hk_env x regs L) (hx_rd x mem) hk_saves.
Proof.
intros x pat cl rb regs mem md L Hc HC.
pose proof (hk_core_cregs x pat cl rb regs mem md HC) as (_ & H8 & _).
pose proof (hk_core_saved x pat cl rb regs mem md HC) as HSV.
pose proof (hk_stack x Hc) as HS. pose proof alloc_ceiling_value as [[C1 C2] _].
assert (Hb : base_val (hk_env x regs L) (Some 8%nat) = hx_sp x).
{ cbn [base_val]. rewrite (hk_env_reg x regs L 8 8%bv eq_refl), H8. unfold w64. apply unsigned_lit_small.
  unfold T_parse_STK, T_PARSE_FRAME, ESTACK in *. lia. }
unfold region_ok, hk_saves. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite Hb.
split; [unfold T_parse_STK, T_PARSE_FRAME, ESTACK in *; lia|]. split; [lia|]. split; [intros o Ho; lia|].
unfold hk_saved_chunks.
apply Forall_cons; [exact (hk_chunk_saved x regs L mem (-8) 1 0 eq_refl ltac:(lia) HSV)|].
apply Forall_cons; [exact (hk_chunk_saved x regs L mem (-16) 8 1 eq_refl ltac:(lia) HSV)|].
apply Forall_cons; [exact (hk_chunk_saved x regs L mem (-24) 9 2 eq_refl ltac:(lia) HSV)|].
apply Forall_cons; [exact (hk_chunk_saved x regs L mem (-32) 18 3 eq_refl ltac:(lia) HSV)|].
apply Forall_cons; [exact (hk_chunk_saved x regs L mem (-40) 19 4 eq_refl ltac:(lia) HSV)|].
apply Forall_cons; [exact (hk_chunk_saved x regs L mem (-48) 20 5 eq_refl ltac:(lia) HSV)|].
apply Forall_cons; [exact (hk_chunk_saved x regs L mem (-56) 21 6 eq_refl ltac:(lia) HSV)|].
apply Forall_cons; [exact (hk_chunk_saved x regs L mem (-64) 22 7 eq_refl ltac:(lia) HSV)|].
apply Forall_cons; [exact (hk_chunk_saved x regs L mem (-72) 23 8 eq_refl ltac:(lia) HSV)|].
apply Forall_cons; [exact (hk_chunk_saved x regs L mem (-80) 24 9 eq_refl ltac:(lia) HSV)|].
apply Forall_cons; [exact (hk_chunk_saved x regs L mem (-88) 25 10 eq_refl ltac:(lia) HSV)|].
apply Forall_cons; [exact (hk_chunk_saved x regs L mem (-96) 26 11 eq_refl ltac:(lia) HSV)|].
apply Forall_cons; [exact (hk_chunk_saved x regs L mem (-104) 27 12 eq_refl ltac:(lia) HSV)|].
apply Forall_cons; [exact (hk_chunk_fs0 x regs L mem HSV)|].
apply Forall_nil.
Qed.

(* the saved words read back from a run's final state (role's saved_of_frame_region) *)
Lemma hk_saved_of_region : forall x E (m : word -> option byte),
region_ok segs E m hk_saves -> base_val E (Some 8%nat) = hx_sp x ->
(forall j, (j < 13)%nat -> ew E (33 + j) = getr (hx_regs x) (Z_to_bv 5 (snd (nth j HP_SAVED (0, 0))))) ->
ew E 46 = hk_fs0 ->
Forall (fun c => val_mem segs m (hx_sp x + fst c) 8 (bv_unsigned (getr (hx_regs x) (Z_to_bv 5 (snd c))))) HP_SAVED /\
val_mem segs m (hx_sp x + HP_FS0) 8 (bv_unsigned hk_fs0).
Proof.
intros x E m HR Hb HE HF.
unfold region_ok, hk_saves in HR. cbn [YP09.r_base YP09.r_chunks] in HR. rewrite Hb in HR.
destruct HR as (_ & _ & _ & HC).
assert (G : forall off j r, nth j HP_SAVED (0, 0) = (off, r) -> (j < 13)%nat ->
  In (YP09.mkChunk off (CVal 8 (SOff (33 + j) 0))) hk_saved_chunks ->
  val_mem segs m (hx_sp x + off) 8 (bv_unsigned (getr (hx_regs x) (Z_to_bv 5 r)))).
{ intros off j r Hn Hj Hin.
  apply (val_of_chunk_ok segs E m (hx_sp x) off 8 (SOff (33 + j) 0) _ (proj1 (Forall_forall _ _) HC _ Hin)).
  - rewrite hk_sv_SOff0, (HE j Hj), Hn. cbn [snd]. symmetry. apply Z_to_bv_bv_unsigned.
  - apply bv_unsigned_in_range.
  - lia. }
split.
- unfold HP_SAVED. cbn [fst snd].
  apply Forall_cons; [exact (G (-8) 0%nat 1 eq_refl ltac:(lia) ltac:(cbn; tauto))|].
  apply Forall_cons; [exact (G (-16) 1%nat 8 eq_refl ltac:(lia) ltac:(cbn; tauto))|].
  apply Forall_cons; [exact (G (-24) 2%nat 9 eq_refl ltac:(lia) ltac:(cbn; tauto))|].
  apply Forall_cons; [exact (G (-32) 3%nat 18 eq_refl ltac:(lia) ltac:(cbn; tauto))|].
  apply Forall_cons; [exact (G (-40) 4%nat 19 eq_refl ltac:(lia) ltac:(cbn; tauto))|].
  apply Forall_cons; [exact (G (-48) 5%nat 20 eq_refl ltac:(lia) ltac:(cbn; tauto))|].
  apply Forall_cons; [exact (G (-56) 6%nat 21 eq_refl ltac:(lia) ltac:(cbn; tauto))|].
  apply Forall_cons; [exact (G (-64) 7%nat 22 eq_refl ltac:(lia) ltac:(cbn; tauto))|].
  apply Forall_cons; [exact (G (-72) 8%nat 23 eq_refl ltac:(lia) ltac:(cbn; tauto))|].
  apply Forall_cons; [exact (G (-80) 9%nat 24 eq_refl ltac:(lia) ltac:(cbn; tauto))|].
  apply Forall_cons; [exact (G (-88) 10%nat 25 eq_refl ltac:(lia) ltac:(cbn; tauto))|].
  apply Forall_cons; [exact (G (-96) 11%nat 26 eq_refl ltac:(lia) ltac:(cbn; tauto))|].
  apply Forall_cons; [exact (G (-104) 12%nat 27 eq_refl ltac:(lia) ltac:(cbn; tauto))|].
  apply Forall_nil.
- unfold HP_FS0.
  apply (val_of_chunk_ok segs E m (hx_sp x) (-112) 8 (SOff 46 0) _
    (proj1 (Forall_forall _ _) HC (YP09.mkChunk (-112) (CVal 8 (SOff 46 0)))
      ltac:(unfold hk_saved_chunks; cbn; tauto))).
  + rewrite hk_sv_SOff0, HF. symmetry. apply Z_to_bv_bv_unsigned.
  + apply bv_unsigned_in_range.
  + lia.
Qed.

(* the temporaries region at sp = spa *)
Lemma hk_temps_ok : forall x pat cl rb regs mem md L cs, call_ok x -> hp_core B x pat cl rb regs mem md ->
Forall (YP09.chunk_ok segs (hk_env x regs L) (hx_rd x mem) (hx_spa x)) cs ->
region_ok segs (hk_env x regs L) (hx_rd x mem) (hk_temps cs).
Proof.
intros x pat cl rb regs mem md L cs Hc HC Hcs.
pose proof (hk_core_cregs x pat cl rb regs mem md HC) as (H2 & _).
pose proof (hk_stack x Hc) as HS. pose proof (hk_frame_win x Hc) as HW. pose proof alloc_ceiling_value as [[C1 C2] _].
assert (Hb : base_val (hk_env x regs L) (Some 2%nat) = hx_spa x).
{ cbn [base_val]. rewrite (hk_env_reg x regs L 2 2%bv eq_refl), H2. unfold w64. apply unsigned_lit_small.
  unfold T_parse_STK, T_PARSE_FRAME, ESTACK in *. lia. }
unfold region_ok, hk_temps. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite Hb.
split; [lia|]. split; [unfold T_parse_STK, T_PARSE_FRAME, ESTACK in *; lia|]. split; [|exact Hcs].
intros o Ho. apply (apresent_writable segs). apply (hk_present_stack x pat cl rb regs mem md Hc HC).
unfold T_parse_STK, T_PARSE_FRAME, ESTACK in *. lia.
Qed.

(* a byte read through the view, outside the image, is present *)
Lemma hk_present_of_view : forall H mem a v, 0 <= a < 2 ^ 64 -> ~ in_img segs a -> aview segs H mem a = Some v ->
apresent H mem a.
Proof.
intros H mem a v Ha Hn Hv.
assert (Hr : seg_rom segs (Z_to_bv 64 a) = None) by (apply seg_rom_none; assumption).
unfold aview, mbyte, mrestrict in Hv. cbv beta in Hv. unfold apresent.
destruct (H (Z_to_bv 64 a)); [rewrite Hr in Hv; discriminate Hv|].
split; [reflexivity|].
destruct (mem (Z_to_bv 64 a)) as [b|]; [exists b; reflexivity | rewrite Hr in Hv; discriminate Hv].
Qed.

Lemma hk_view_val1 : forall H mem a v, aview segs H mem a = Some v -> val_mem segs (mrestrict H mem) a 1 v /\ 0 <= v < 256.
Proof.
intros H mem a v Hv. apply aview_byte in Hv as (b & Hb & Hvb & Hr). split; [|exact Hr].
intros kk Hk. assert (kk = 0%nat) as -> by lia. cbn [Z.of_nat]. rewrite Z.add_0_r. rewrite Hb. f_equal.
unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
change (2 ^ 8) with 256. rewrite !Z.mod_small by lia. rewrite Hvb. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

(* the hole region at s10 (for the runs that write the hole) *)
Lemma hk_hole_ok : forall x pat cl rb regs mem md L, call_ok x -> hp_core B x pat cl rb regs mem md ->
length pat = 8%nat ->
region_ok segs (hk_env x regs L) (hx_rd x mem) (hk_hole_rg pat).
Proof.
intros x pat cl rb regs mem md L Hc HC Hl.
pose proof (hk_core_cregs x pat cl rb regs mem md HC) as (_ & _ & _ & _ & _ & _ & _ & H26 & _).
pose proof (hk_core_journal x pat cl rb regs mem md HC) as (HJ & OK & HP).
pose proof (hk_stack x Hc) as HS. pose proof alloc_ceiling_value as [[C1 C2] _].
assert (Hsh : SHADOW_OFF <= hx_shf x /\ hx_shf x + 8 <= SHADOW_OFF + 2 ^ 44)
by (unfold hx_shf, shadow_addr, SHADOW_OFF in *; lia).
assert (Hb : base_val (hk_env x regs L) (Some 26%nat) = hx_shf x).
{ cbn [base_val]. rewrite (hk_env_reg x regs L 26 26%bv eq_refl), H26. unfold w64. apply unsigned_lit_small.
  unfold SHADOW_OFF in *. lia. }
assert (HV : forall i, 0 <= i < 8 -> aview segs (w_H (hx_W x)) mem (hx_shf x + i) = Some (nth (Z.to_nat i) pat 0)).
{ intros i Hi. apply HP. rewrite Hl. lia. }
assert (Hni : forall i, 0 <= i < 8 -> ~ in_img segs (hx_shf x + i)).
{ intros i Hi Himg. pose proof (segs_low _ Himg). unfold kLowMemEnd, SHADOW_OFF in *. lia. }
unfold region_ok, hk_hole_rg. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite Hb.
split; [unfold SHADOW_OFF in *; lia|]. split; [unfold SHADOW_OFF in *; lia|]. split.
- intros o Ho. apply (apresent_writable segs).
  apply (hk_present_of_view (w_H (hx_W x)) mem (hx_shf x + o) (nth (Z.to_nat o) pat 0));
  [unfold SHADOW_OFF in *; lia | exact (Hni o Ho) | exact (HV o Ho)].
- unfold hk_hole_chunks. apply Forall_forall. intros c Hin. apply in_map_iff in Hin as (i & <- & Hi). apply in_seq in Hi.
  assert (Hbyte : 0 <= nth i pat 0 < 256).
  { destruct OK as (_ & _ & _ & _ & HB). rewrite Forall_forall in HB. apply HB. apply nth_In. lia. }
  apply (chunk_ok_val segs (hk_env x regs L) (hx_rd x mem) (hx_shf x) (Z.of_nat i) 1 (SLit (nth i pat 0)) (nth i pat 0)).
  + cbn [sv_denot]. reflexivity.
  + change (2 ^ (8 * Z.of_N 1)) with 256. exact Hbyte.
  + lia.
  + pose proof (HV (Z.of_nat i) ltac:(lia)) as V. rewrite Nat2Z.id in V. exact (proj1 (hk_view_val1 _ _ _ _ V)).
Qed.

(* ======================================= 4. hp_core again: after a run or a wrapper call ======================================= *)
Lemma hk_saved_kept : forall x mem mem2,
(forall a, hx_sp x - 112 <= a < hx_sp x -> hx_view x mem2 a = hx_view x mem a) ->
hp_saved_ok x mem -> hp_saved_ok x mem2.
Proof.
intros x mem mem2 HK (HS & HF). split.
- rewrite Forall_forall in *. intros c Hin. specialize (HS c Hin).
  assert (Hc : -104 <= fst c <= -8)
  by (unfold HP_SAVED in Hin; repeat (destruct Hin as [<-|Hin]; [cbn; lia|]); destruct Hin).
  apply (val_mem_kept segs (w_H (hx_W x)) (w_H (hx_W x)) mem mem2); [|exact HS].
  intros k Hk. apply HK. lia.
- apply (val_mem_kept segs (w_H (hx_W x)) (w_H (hx_W x)) mem mem2); [|exact HF].
  intros k Hk. apply HK. unfold HP_FS0. lia.
Qed.

Lemma hk_garr8_kept : forall x mem mem2 b (l : list Z),
(forall a, b <= a < b + Z.of_nat (length l) -> hx_view x mem2 a = hx_view x mem a) ->
garr8 segs (hx_rd x mem) b l -> garr8 segs (hx_rd x mem2) b l.
Proof.
intros x mem mem2 b l HK HG j Hj. destruct (HG j Hj) as [Hv Hr]. split; [|exact Hr].
apply (val_mem_kept segs (w_H (hx_W x)) (w_H (hx_W x)) mem mem2); [|exact Hv].
intros k Hk. apply HK. lia.
Qed.

Lemma hk_rd32_kept : forall (rd rd' : reader) a v, (forall k, 0 <= k < 4 -> rd' (a + k) = rd (a + k)) ->
rd32 rd a v -> rd32 rd' a v.
Proof. intros rd rd' a v HK H k Hk. rewrite (HK (Z.of_nat k) ltac:(lia)). exact (H k Hk). Qed.

Lemma hk_hpat_kept : forall x mem mem2 pat,
(forall i, 0 <= i < Z.of_nat (length pat) -> hx_view x mem2 (hx_shf x + i) = hx_view x mem (hx_shf x + i)) ->
hpat segs (hx_W x) mem (hx_fr x) pat -> hpat segs (hx_W x) mem2 (hx_fr x) pat.
Proof. intros x mem mem2 pat HK HP i Hi. pose proof (HK i Hi) as E. unfold hx_view, hx_shf in E. rewrite E. exact (HP i Hi). Qed.

(* the nine registers of the cut from aregs_preserved (a call returns them) *)
Lemma hk_cregs_pres : forall x (regs regs2 : bvmap 5 word), hk_cregs x regs -> aregs_preserved regs regs2 -> hk_cregs x regs2.
Proof.
intros x regs regs2 Hr Hp. apply (hk_cregs_same x regs regs2 Hr);
match goal with |- getr _ ?r = getr _ ?r =>
  let z := eval vm_compute in (bv_unsigned r) in
  replace r with (Z_to_bv 5 z) by (apply bv_eq; reflexivity); apply Hp; unfold acallee_saved; lia end.
Qed.

(* THE step: the core at the new memory from the core at the old one, the bytes outside Wr kept, every byte of Wr in
   the window below the saves, in the hole or in the parse's writes for its caller; the new journal, pattern, cells,
   res bytes and errno cell given *)
Lemma hk_core_step : forall x pat pat' cl cl' rb rb' regs mem md regs2 mem2 md2 (Wr : Z -> Prop),
api_env segs B -> call_ok x -> hp_core B x pat cl rb regs mem md ->
(length cl <= length cl')%nat -> Z.of_nat (length cl') <= hx_cap x + 1 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> hx_view x mem2 a = hx_view x mem a) ->
(forall a, Wr a -> (hx_sp x - T_parse_STK <= a < hx_sp x - 112) \/ hp_hole x a \/
  hp_pw B x (Z.of_nat (length cl')) a) ->
ajournal segs B (hx_STK x) (hx_sp0 x) (hx_FP x) (hx_ly x) (hx_S x) (hx_W0 x) (hx_mem0 x) (hx_md0 x) (hx_own x)
  (hx_lyc x) (hx_Sc x) (hx_W x) (unpoison (hU (hx_fr x) pat) mem2) md2 (hx_k x) ->
length pat' = length pat -> Forall (fun v => 0 <= v < 256) pat' -> hpat segs (hx_W x) mem2 (hx_fr x) pat' ->
same_io md md2 ->
garr8 segs (hx_rd x mem2) (hx_O x) (hd_zbytes (ha_cells_bytes cl')) ->
(hx_R x <> 0 -> garr8 segs (hx_rd x mem2) (hx_R x) (hd_zbytes rb')) ->
(exists ev', rd32 (hx_view x mem2) (as_errno B) ev') ->
hk_cregs x regs2 ->
hp_core B x pat' cl' rb' regs2 mem2 md2.
Proof.
intros x pat pat' cl cl' rb rb' regs mem md regs2 mem2 md2 Wr Henv Hc HC Hle Hcap HK HW HJ2 HL HB HP2 Hio2 HO2 HR2 HE2 Hr2.
pose proof HC as ((_ & OK & _) & Hio & HKo & HSV & _).
pose proof (hk_stack x Hc) as HS.
pose proof alloc_ceiling_value as [[C1 C2] _].
pose proof (hk_out x Hc) as (Hcap0 & _ & _ & _ & _ & _ & HOc & HOapp & _ & HOoff & Hob).
pose proof Henv as [[He0 He1] _].
unfold hp_core.
split; [eapply hj_repat_raw; [exact HJ2 | exact OK | exact HL | exact HB | exact HP2]|].
split; [eapply same_io_trans; [exact Hio | exact Hio2]|].
split.
{ intros a Ha Hw Hh Hpw. rewrite (HK a Ha).
  - apply (HKo a Ha Hw Hh). intros Hp. apply Hpw. unfold hp_pw in *.
    destruct Hp as [Hp|[Hp|Hp]]; [left; lia | right; left; exact Hp | right; right; exact Hp].
  - intros HWa. destruct (HW a HWa) as [Hw'|[Hh'|Hp']]; [apply Hw; lia | exact (Hh Hh') | exact (Hpw Hp')]. }
split.
{ apply (hk_saved_kept x mem mem2); [|exact HSV].
  intros a Ha. apply HK; [unfold T_parse_STK, T_PARSE_FRAME, ESTACK in *; lia|].
  intros HWa. destruct (HW a HWa) as [Hw'|[Hh'|Hp']].
  - lia.
  - pose proof (hk_hole_band x a Hc Hh'). unfold T_parse_STK, T_PARSE_FRAME, ESTACK in *. lia.
  - unfold hp_pw in Hp'. destruct Hp' as [Ho|[(HR0 & Hr)|He]].
    + apply (HOoff a ltac:(lia)). unfold hx_sp in *. lia.
    + destruct (hk_res x Hc HR0) as (_ & _ & Hside & _). unfold T_parse_STK, T_PARSE_FRAME, ESTACK in *. lia.
    + unfold kLowMemEnd, T_parse_STK, T_PARSE_FRAME, ESTACK in *. lia. }
exact (conj HO2 (conj HR2 (conj HE2 Hr2))).
Qed.

(* after an engine run: frame_of over the run's write windows, each in [spa, spa + 0x80), the hole, the new cells
   out[3 |cl| ..) or res *)
Lemma hk_core_of_run : forall x pat pat' cl cl' rb rb' regs mem md regs2 mem2 md2 E rs,
api_env segs B -> call_ok x -> hp_core B x pat cl rb regs mem md ->
(length cl <= length cl')%nat -> Z.of_nat (length cl') <= hx_cap x + 1 ->
frame_of E rs (hx_rd x mem) (hx_rd x mem2) ->
(forall a, in_wrange E rs a -> (hx_spa x <= a < hx_spa x + 0x80) \/ hp_hole x a \/
  (hx_O x <= a < hx_O x + 3 * Z.of_nat (length cl')) \/ (hx_R x <> 0 /\ hx_R x <= a < hx_R x + 12)) ->
ajournal segs B (hx_STK x) (hx_sp0 x) (hx_FP x) (hx_ly x) (hx_S x) (hx_W0 x) (hx_mem0 x) (hx_md0 x) (hx_own x)
  (hx_lyc x) (hx_Sc x) (hx_W x) (unpoison (hU (hx_fr x) pat) mem2) md2 (hx_k x) ->
length pat' = length pat -> Forall (fun v => 0 <= v < 256) pat' -> hpat segs (hx_W x) mem2 (hx_fr x) pat' ->
same_io md md2 ->
garr8 segs (hx_rd x mem2) (hx_O x) (hd_zbytes (ha_cells_bytes cl')) ->
(hx_R x <> 0 -> garr8 segs (hx_rd x mem2) (hx_R x) (hd_zbytes rb')) ->
hk_cregs x regs2 ->
hp_core B x pat' cl' rb' regs2 mem2 md2.
Proof.
intros x pat pat' cl cl' rb rb' regs mem md regs2 mem2 md2 E rs Henv Hc HC Hle Hcap Hfr HW HJ2 HL HB HP2 Hio2 HO2 HR2 Hr2.
assert (HK : forall a, 0 <= a < 2 ^ 64 -> ~ in_wrange E rs a -> hx_view x mem2 a = hx_view x mem a).
{ intros a Ha Hn. pose proof (Hfr (Z_to_bv 64 a)) as E1. unfold hx_rd in E1.
  rewrite unsigned_lit_small in E1 by exact Ha.
  unfold hx_view, aview, mbyte. rewrite (E1 Hn). reflexivity. }
pose proof (hk_frame_win x Hc) as HFW. pose proof (hk_stack x Hc) as HS.
pose proof alloc_ceiling_value as [[C1 C2] _].
pose proof (hk_out x Hc) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hob).
pose proof Henv as [[He0 He1] [Heimg _]].
destruct (hk_core_cells x pat cl rb regs mem md HC) as (_ & _ & (ev & HEv)).
apply (hk_core_step x pat pat' cl cl' rb rb' regs mem md regs2 mem2 md2 (in_wrange E rs) Henv Hc HC Hle Hcap HK);
  [ | exact HJ2 | exact HL | exact HB | exact HP2 | exact Hio2 | exact HO2 | exact HR2 | | exact Hr2].
- intros a Ha. destruct (HW a Ha) as [H1|[H2|[H3|H4]]].
  + left. unfold T_parse_STK, T_PARSE_FRAME, ESTACK in *. lia.
  + right; left; exact H2.
  + right; right; unfold hp_pw; left; exact H3.
  + right; right; unfold hp_pw; right; left; exact H4.
- exists ev. apply (hk_rd32_kept (hx_view x mem) (hx_view x mem2) (as_errno B) ev); [|exact HEv].
  intros k Hk. apply HK; [unfold kLowMemEnd in *; lia|].
  intros Hin. destruct (HW _ Hin) as [H1|[H2|[H3|H4]]].
  + unfold T_parse_STK, T_PARSE_FRAME, ESTACK, kLowMemEnd in *. lia.
  + pose proof (hk_hole_band x _ Hc H2). unfold kLowMemEnd, SHADOW_OFF in *. lia.
  + destruct (Hob (as_errno B + k) ltac:(lia)) as (_ & _ & _ & Hni). exact (Hni (Heimg (as_errno B + k) ltac:(lia))).
  + destruct H4 as (HR0 & Hr). destruct (hk_res x Hc HR0) as (_ & _ & _ & HRr).
    destruct (HRr _ Hr) as (_ & Hni & _). exact (Hni (Heimg (as_errno B + k) ltac:(lia))).
Qed.

(* after a run that wrote only [spa + lo, spa + hi) (a frame temporary): the same pattern, cells and res *)
Lemma hk_core_frame : forall x pat cl rb regs mem md regs2 mem2 md2 lo hi,
api_env segs B -> call_ok x -> hp_core B x pat cl rb regs mem md ->
Z.of_nat (length cl) <= hx_cap x + 1 -> length rb = 12%nat -> 0 <= lo -> hi <= 0x80 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (hx_spa x + lo <= a < hx_spa x + hi) ->
  hx_rd x mem2 (Z_to_bv 64 a) = hx_rd x mem (Z_to_bv 64 a)) ->
ajournal segs B (hx_STK x) (hx_sp0 x) (hx_FP x) (hx_ly x) (hx_S x) (hx_W0 x) (hx_mem0 x) (hx_md0 x) (hx_own x)
  (hx_lyc x) (hx_Sc x) (hx_W x) (unpoison (hU (hx_fr x) pat) mem2) md2 (hx_k x) ->
same_io md md2 -> hk_cregs x regs2 ->
hp_core B x pat cl rb regs2 mem2 md2.
Proof.
intros x pat cl rb regs mem md regs2 mem2 md2 lo hi Henv Hc HC Hcl Hrb Hlo Hhi Hrd HJ2 Hio2 Hr2.
assert (HK : forall a, 0 <= a < 2 ^ 64 -> ~ (hx_spa x + lo <= a < hx_spa x + hi) -> hx_view x mem2 a = hx_view x mem a).
{ intros a Ha Hn. pose proof (Hrd a Ha Hn) as E1. unfold hx_rd in E1. unfold hx_view, aview, mbyte. rewrite E1. reflexivity. }
pose proof HC as ((_ & OK & HP) & _ & _ & _ & HO & HR & (ev & HEv) & _).
pose proof (hk_stack x Hc) as HS. pose proof (hk_frame_win x Hc) as HFW. pose proof alloc_ceiling_value as [[C1 C2] _].
pose proof (hk_out x Hc) as (Hcap0 & _ & _ & _ & _ & _ & HOc & HOapp & _ & HOoff & Hob).
pose proof Henv as [[He0 He1] [Heimg _]].
assert (NW : forall a, hx_spa x + lo <= a < hx_spa x + hi -> hx_sp x - T_parse_STK <= a < hx_sp x - 112).
{ intros a Ha. unfold T_parse_STK, T_PARSE_FRAME, ESTACK in *. lia. }
apply (hk_core_step x pat pat cl cl rb rb regs mem md regs2 mem2 md2 (fun a => hx_spa x + lo <= a < hx_spa x + hi)
  Henv Hc HC (le_n _) Hcl HK);
  [ | exact HJ2 | reflexivity | exact (proj2 (proj2 (proj2 (proj2 OK)))) | | exact Hio2 | | | | exact Hr2].
- intros a Ha. left. exact (NW a Ha).
- apply (hk_hpat_kept x mem mem2 pat); [|exact HP]. intros i Hi.
  destruct OK as (_ & _ & _ & Hfh & _).
  apply HK; [unfold hx_shf, shadow_addr, SHADOW_OFF in *; lia|].
  intros Hin. pose proof (NW _ Hin). unfold hx_shf, shadow_addr, SHADOW_OFF, T_parse_STK, T_PARSE_FRAME, ESTACK in *. lia.
- apply (hk_garr8_kept x mem mem2); [|exact HO]. intros a Ha.
  unfold hd_zbytes in Ha. rewrite length_map, length_ha_cells_bytes in Ha.
  apply HK; [unfold in_app, ASAN_CEIL in *; lia|].
  intros Hin. pose proof (NW _ Hin). apply (HOoff a ltac:(lia)). unfold hx_sp in *. lia.
- intros HR0. apply (hk_garr8_kept x mem mem2); [|exact (HR HR0)]. intros a Ha.
  unfold hd_zbytes in Ha. rewrite length_map, Hrb in Ha.
  destruct (hk_res x Hc HR0) as (_ & _ & Hside & Hr).
  destruct (Hr a ltac:(lia)) as (_ & _ & [Hst|Happ]).
  + apply HK; [lia|]. intros Hin. pose proof (NW _ Hin). unfold T_parse_STK, T_PARSE_FRAME, ESTACK in *. lia.
  + apply HK; [unfold app_addr, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; lia|]. intros Hin. pose proof (NW _ Hin).
    unfold app_addr, ASAN_CEIL, kLowShadowBeg, kHighMemBeg, T_parse_STK, T_PARSE_FRAME, ESTACK in *. lia.
- exists ev. apply (hk_rd32_kept (hx_view x mem) (hx_view x mem2) (as_errno B) ev); [|exact HEv].
  intros k Hk. apply HK; [unfold kLowMemEnd in *; lia|].
  intros Hin. pose proof (NW _ Hin). unfold T_parse_STK, T_PARSE_FRAME, ESTACK, kLowMemEnd in *. lia.
Qed.

(* after a wrapper call made at sp = spa (hj_strncmp_at / hj_strcmp_at / hj_strtol_at post): the callee wrote below
   spa (at most 3 ESTACK), the end pointer cell [spa + 0x60, spa + 0x68) and the errno cell *)
Lemma hk_core_of_call : forall x pat cl rb regsT memT mdT regs2 mem2 md2, api_env segs B -> call_ok x ->
hp_core B x pat cl rb regsT memT mdT -> Z.of_nat (length cl) <= hx_cap x + 1 -> length rb = 12%nat ->
hjournal segs B (hx_STK x) (hx_sp0 x) (hx_FP x) (hx_ly x) (hx_S x) (hx_W0 x) (hx_mem0 x) (hx_md0 x) (hx_own x)
  (hx_lyc x) (hx_Sc x) (hx_W x) mem2 md2 (hx_k x) (hx_fr x) pat ->
aregs_preserved regsT regs2 -> same_io mdT md2 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (hx_spa x - 3 * ESTACK <= a < hx_spa x) -> ~ (hx_spa x + 0x60 <= a < hx_spa x + 0x68) ->
  ~ (as_errno B <= a < as_errno B + 4) -> hx_view x mem2 a = hx_view x memT a) ->
(exists ev', rd32 (hx_view x mem2) (as_errno B) ev') ->
hp_core B x pat cl rb regs2 mem2 md2.
Proof.
intros x pat cl rb regsT memT mdT regs2 mem2 md2 Henv Hc HC Hcl Hrb HJ2 Hpr Hio2 HKc HE2.
set (Wr := fun a => (hx_spa x - 3 * ESTACK <= a < hx_spa x) \/ (hx_spa x + 0x60 <= a < hx_spa x + 0x68) \/
  (as_errno B <= a < as_errno B + 4)).
assert (HK : forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> hx_view x mem2 a = hx_view x memT a).
{ intros a Ha Hn. apply HKc; [exact Ha | intros H; apply Hn; left; exact H | intros H; apply Hn; right; left; exact H |
  intros H; apply Hn; right; right; exact H]. }
pose proof HC as ((_ & OK & _) & _ & _ & _ & HO & HR & _ & HCR).
destruct HJ2 as (HJ2 & _ & HP2).
pose proof (hk_stack x Hc) as HS. pose proof (hk_frame_win x Hc) as HFW. pose proof alloc_ceiling_value as [[C1 C2] _].
pose proof (hk_out x Hc) as (Hcap0 & _ & _ & _ & _ & _ & HOc & HOapp & _ & HOoff & Hob).
pose proof Henv as [[He0 He1] [Heimg _]].
assert (ESTACK = 4096) as Hes by reflexivity.
apply (hk_core_step x pat pat cl cl rb rb regsT memT mdT regs2 mem2 md2 Wr Henv Hc HC (le_n _) Hcl HK);
  [ | exact HJ2 | reflexivity | exact (proj2 (proj2 (proj2 (proj2 OK)))) | exact HP2 | exact Hio2 | | | exact HE2 |
    exact (hk_cregs_pres x regsT regs2 HCR Hpr)].
- intros a [Hw|[Hd|He]].
  + left. unfold T_parse_STK, T_PARSE_FRAME in *. lia.
  + left. unfold T_parse_STK, T_PARSE_FRAME in *. lia.
  + right; right. unfold hp_pw. right; right. exact He.
- apply (hk_garr8_kept x memT mem2); [|exact HO]. intros a Ha.
  unfold hd_zbytes in Ha. rewrite length_map, length_ha_cells_bytes in Ha.
  destruct (Hob a ltac:(lia)) as (_ & _ & _ & Hni).
  apply HK; [unfold in_app, ASAN_CEIL in *; lia|].
  intros [Hw|[Hd|He]].
  + apply (HOoff a ltac:(lia)). unfold hx_sp, T_parse_STK, T_PARSE_FRAME in *. lia.
  + apply (HOoff a ltac:(lia)). unfold hx_sp, T_parse_STK, T_PARSE_FRAME in *. lia.
  + exact (Hni (Heimg a He)).
- intros HR0. apply (hk_garr8_kept x memT mem2); [|exact (HR HR0)]. intros a Ha.
  unfold hd_zbytes in Ha. rewrite length_map, Hrb in Ha.
  destruct (hk_res x Hc HR0) as (_ & _ & Hside & Hr).
  destruct (Hr a ltac:(lia)) as (_ & Hni & Hloc).
  apply HK; [destruct Hloc as [Hst|Happ]; unfold app_addr, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; lia|].
  intros [Hw|[Hd|He]].
  + unfold T_parse_STK, T_PARSE_FRAME in *. lia.
  + unfold T_parse_STK, T_PARSE_FRAME in *. lia.
  + exact (Hni (Heimg a He)).
Qed.

(* the frame temporaries a wrapper call at sp = spa keeps: below the end pointer cell or above it *)
Lemma hk_temps_kept_call : forall x memT mem2 o v, api_env segs B -> call_ok x ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (hx_spa x - 3 * ESTACK <= a < hx_spa x) -> ~ (hx_spa x + 0x60 <= a < hx_spa x + 0x68) ->
  ~ (as_errno B <= a < as_errno B + 4) -> hx_view x mem2 a = hx_view x memT a) ->
(0 <= o /\ o + 8 <= 0x60) \/ (0x68 <= o /\ o + 8 <= 0x80) ->
val_mem segs (hx_rd x memT) (hx_spa x + o) 8 v -> val_mem segs (hx_rd x mem2) (hx_spa x + o) 8 v.
Proof.
intros x memT mem2 o v Henv Hc HKc Ho Hv.
pose proof (hk_stack x Hc) as HS. pose proof (hk_frame_win x Hc) as HFW. pose proof alloc_ceiling_value as [[C1 C2] _].
pose proof Henv as [[He0 He1] _].
apply (val_mem_kept segs (w_H (hx_W x)) (w_H (hx_W x)) memT mem2); [|exact Hv].
intros k Hk. apply HKc.
- unfold T_parse_STK, T_PARSE_FRAME, ESTACK in *. lia.
- lia.
- lia.
- unfold kLowMemEnd, T_parse_STK, T_PARSE_FRAME, ESTACK in *. lia.
Qed.

(* ---------------------------------- res and out at a cut; the write-set obligations ---------------------------------- *)
(* res's shadow and presence at a cut (its three words are written at EXIT by instrumented `sw`) *)
Lemma hk_res_at_cut : forall x pat cl rb regs mem md, api_env segs B -> call_ok x -> hx_R x <> 0 ->
hp_core B x pat cl rb regs mem md -> Z.of_nat (length cl) <= hx_cap x + 1 ->
range_addressable (hx_view x mem) SHADOW_OFF (hx_R x) 12 /\
(forall a, hx_R x <= a < hx_R x + 12 -> apresent (w_H (hx_W x)) mem a).
Proof.
intros x pat cl rb regs mem md Henv Hc HR0 HC Hcl.
pose proof (hk_res x Hc HR0) as (_ & HRra & Hside & Hr).
pose proof (hk_frame_win x Hc) as HFW. pose proof (hk_stack x Hc) as HS. pose proof alloc_ceiling_value as [[C1 C2] _].
split.
- intros a Ha. destruct (HRra a Ha) as (s & Hs & Hok). exists s. split; [|exact Hok].
  rewrite <- Hs. unfold shadow_of_addr.
  destruct (Hr a Ha) as (_ & _ & Hloc).
  apply (hk_kept_sh x pat cl rb regs mem md (SHADOW_OFF + a / 8) Henv Hc HC Hcl).
  + destruct Hloc as [Hst|Happ]; unfold app_addr, ASAN_CEIL, kLowShadowBeg, kHighMemBeg, kHighShadowEnd, SHADOW_OFF in *; lia.
  + change (SHADOW_OFF + a / 8) with (shadow_addr a). apply hk_sh_not_hole; [exact Hc|].
    intros Hfa. unfold T_parse_STK, T_PARSE_FRAME, ESTACK in *. lia.
- intros a Ha.
  pose proof (hk_core_journal x pat cl rb regs mem md HC) as (HJ & OK & _).
  pose proof (hk_call_args x Hc) as (_ & _ & _ & _ & _ & HR & _).
  destruct HR as [HR|((Hloc & _) & _ & _)]; [contradiction|].
  destruct Hloc as [Hst | (cid & pos & Hin & _ & Hf1 & Hf2)].
  + apply (hk_present_stack x pat cl rb regs mem md Hc HC). lia.
  + assert (HinF : In (cid, pos) (frames (hx_Sc x))).
    { pose proof (hk_call_journal x Hc) as (_ & _ & _ & _ & _ & Hfr & _). rewrite Hfr. apply in_or_app. left. exact Hin. }
    destruct (al_frames _ _ (AR_laws_ok segs B) _ _ _ _ _ cid pos (proj1 HJ) HinF) as (_ & Happ & Hb & _).
    destruct (Hb a ltac:(lia)) as [Hpr _].
    assert (HIN : in_ush (hU (hx_fr x) pat) (bv_unsigned (Z_to_bv 64 a)) = false).
    { apply in_hU_false.
      rewrite unsigned_lit_small by (unfold in_app, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *; lia).
      destruct OK as (_ & _ & _ & Hhi & _).
      unfold in_app, ASAN_CEIL, kLowShadowBeg, kHighMemBeg, shadow_addr, SHADOW_OFF in *. lia. }
    exact (proj1 (hp_apresent_unp (w_H (hx_W x)) (hU (hx_fr x) pat) mem a HIN) Hpr).
Qed.

(* the out cells' check at the atom m holding O + o *)
Lemma hk_shent_out : forall x H mem E (m : nat) o lo hi, call_ok x ->
ew E 27 = w64 SHADOW_OFF -> ew E m = w64 (hx_O x + o) ->
range_addressable (aview segs H mem) SHADOW_OFF (hx_O x) (3 * (hx_cap x + 1)) ->
0 <= o <= 3 * (hx_cap x + 1) -> 0 <= o + lo -> lo <= hi -> o + hi <= 3 * (hx_cap x + 1) ->
shent_ok segs (SOff 27 0) E (mrestrict H mem) (mkSHE m lo hi).
Proof.
intros x H mem E m o lo hi Hc E27 Em Hra Ho0 Hlo Hlh Hhi.
pose proof (hk_out x Hc) as (_ & _ & _ & _ & _ & H4096 & HOc & HOapp & _).
pose proof alloc_ceiling_value as [[C1 C2] _].
apply (hk_shent_of_ra H mem E m (hx_O x) (3 * (hx_cap x + 1)) (hx_O x + o) lo hi Hra E27 Em); [lia | lia | exact Hlh | lia |].
intros b Hb. unfold in_app, ASAN_CEIL, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
Qed.

(* the write-set obligation of the hole runners (HPgHole.awr_okH), one region at a time (role's pe_awr) *)
Lemma hk_awr_temps : forall x E rs cs U, call_ok x -> bv_unsigned (ew E 2) = hx_spa x ->
awr_okH E rs (hx_STK x) (hx_sp0 x) (hx_FP x) (ablocks B (hx_ly x) (hx_S x)) (ablocks B (hx_lyc x) (hx_Sc x))
  (hx_lyc x) (hx_own x) U ->
awr_okH E (hk_temps cs :: rs) (hx_STK x) (hx_sp0 x) (hx_FP x) (ablocks B (hx_ly x) (hx_S x))
  (ablocks B (hx_lyc x) (hx_Sc x)) (hx_lyc x) (hx_own x) U.
Proof.
intros x E rs cs U Hc H2 H.
pose proof (hk_stack x Hc) as HS. pose proof (hk_frame_win x Hc) as HW.
apply (awr_okH_cons_gen E (hk_temps cs) rs _ _ _ _ _ _ _ U 2%nat (hx_spa x) eq_refl H2); [|exact H].
intros a Ha. unfold hk_temps in Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha.
left. left. unfold T_parse_STK, T_PARSE_FRAME, ESTACK in *. lia.
Qed.

Lemma hk_awr_saves : forall x E rs U,
awr_okH E rs (hx_STK x) (hx_sp0 x) (hx_FP x) (ablocks B (hx_ly x) (hx_S x)) (ablocks B (hx_lyc x) (hx_Sc x))
  (hx_lyc x) (hx_own x) U ->
awr_okH E (hk_saves :: rs) (hx_STK x) (hx_sp0 x) (hx_FP x) (ablocks B (hx_ly x) (hx_S x))
  (ablocks B (hx_lyc x) (hx_Sc x)) (hx_lyc x) (hx_own x) U.
Proof. intros x E rs U H. apply awr_okH_cons_ro; [cbn; lia | exact H]. Qed.

Lemma hk_awr_hole : forall x E rs pat, bv_unsigned (ew E 26) = hx_shf x -> length pat = 8%nat ->
awr_okH E rs (hx_STK x) (hx_sp0 x) (hx_FP x) (ablocks B (hx_ly x) (hx_S x)) (ablocks B (hx_lyc x) (hx_Sc x))
  (hx_lyc x) (hx_own x) (hU (hx_fr x) pat) ->
awr_okH E (hk_hole_rg pat :: rs) (hx_STK x) (hx_sp0 x) (hx_FP x) (ablocks B (hx_ly x) (hx_S x))
  (ablocks B (hx_lyc x) (hx_Sc x)) (hx_lyc x) (hx_own x) (hU (hx_fr x) pat).
Proof.
intros x E rs pat H26 Hl H.
apply (awr_okH_cons_hole E (hk_hole_rg pat) rs _ _ _ _ _ _ _ (hx_fr x) pat 26%nat eq_refl H26); [cbn; lia | | exact H].
cbn [hk_hole_rg YP09.r_whi]. rewrite Hl. lia.
Qed.

(* a region the segment adds whose writable bytes lie in out's block, or in res *)
Lemma hk_awr_out : forall x E r rs U (k : nat) b, call_ok x -> YP09.r_base r = Some k -> bv_unsigned (ew E k) = b ->
(forall a, b + YP09.r_wlo r <= a < b + YP09.r_whi r -> hx_O x <= a < hx_O x + 3 * (hx_cap x + 1)) ->
awr_okH E rs (hx_STK x) (hx_sp0 x) (hx_FP x) (ablocks B (hx_ly x) (hx_S x)) (ablocks B (hx_lyc x) (hx_Sc x))
  (hx_lyc x) (hx_own x) U ->
awr_okH E (r :: rs) (hx_STK x) (hx_sp0 x) (hx_FP x) (ablocks B (hx_ly x) (hx_S x))
  (ablocks B (hx_lyc x) (hx_Sc x)) (hx_lyc x) (hx_own x) U.
Proof.
intros x E r rs U k b Hc Hk Hb Hw H.
apply (awr_okH_cons_gen E r rs _ _ _ _ _ _ _ U k b Hk Hb); [|exact H].
intros a Ha. left. pose proof (hk_out x Hc) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hob).
exact (proj1 (Hob a (Hw a Ha))).
Qed.

Lemma hk_awr_res : forall x E r rs U (k : nat) b, call_ok x -> hx_R x <> 0 -> YP09.r_base r = Some k ->
bv_unsigned (ew E k) = b -> (forall a, b + YP09.r_wlo r <= a < b + YP09.r_whi r -> hx_R x <= a < hx_R x + 12) ->
awr_okH E rs (hx_STK x) (hx_sp0 x) (hx_FP x) (ablocks B (hx_ly x) (hx_S x)) (ablocks B (hx_lyc x) (hx_Sc x))
  (hx_lyc x) (hx_own x) U ->
awr_okH E (r :: rs) (hx_STK x) (hx_sp0 x) (hx_FP x) (ablocks B (hx_ly x) (hx_S x))
  (ablocks B (hx_lyc x) (hx_Sc x)) (hx_lyc x) (hx_own x) U.
Proof.
intros x E r rs U k b Hc HR0 Hk Hb Hw H.
apply (awr_okH_cons_gen E r rs _ _ _ _ _ _ _ U k b Hk Hb); [|exact H].
intros a Ha. left. destruct (hk_res x Hc HR0) as (_ & _ & _ & Hr). exact (proj1 (Hr a (Hw a Ha))).
Qed.

End k.

Print Assumptions hk_pod_at_cut.
Print Assumptions hk_core_intro.
Print Assumptions hk_cstr_at_cut.
Print Assumptions hk_saves_ok.
Print Assumptions hk_hole_ok.
Print Assumptions hk_atoms_ok.
Print Assumptions hk_core_of_run.
Print Assumptions hk_core_frame.
Print Assumptions hk_core_of_call.
Print Assumptions hk_aro_at_cut.
