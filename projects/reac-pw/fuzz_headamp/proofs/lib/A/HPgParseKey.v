(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the run plumbing of proofs/reac-pw/fuzz_role/lib/A/RPgCfgChanges.v at 964efd2f474 (cfg_keep, cfg_kwr_ro and the same_io chain of cfg_leaf, as l_keep, l_kwr and l_post) and of proofs/reac-pw/fuzz_qdisc/lib/A/QPgCheck.v at b0f706c04a1 (awr_stk, as l_awr: the writable window is the frame [F, F + 0x60) at atom 2), for a segment of reac_role_prop_parse's walk that starts and ends at the cuts of lib/A/RPgParseBase.v; the entry states, exits, string lemmas and the walk below are new. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgParseL.v at afaa3cb55c1d; for reac-pw/fuzz_rate's reac_rate_prop_parse at image A: module paths and the rl_ / Role names changed to rate's (rt_cstr, rt_fxk, Rate.harness_parse, Rate.RATE_KEY, RtPgStrcmp's rt_cstr_args and cstr_at_of_rt_cstr; kept_run and same_io_wvb from RtPgParseBase), the pcs and image constants are fuzz_rate.asan's (key 0x21720, strcmp wrapper 0x4219c), and on the three next-child paths the foreach back edge 0x84728 beqz is the taken side to L2 (its fall-through 0x8472c j 0x84554 is the impossible one). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgParseL.v; 499 of its 567 lines of code are new or changed and 845 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgParseF.v at afaa3cb55c1d for reac-pw/fuzz_rate's
   reac_rate_prop_parse: module paths and the rl_ / Role names changed to rate's; the pcs are image A's of
   fuzz_rate.asan; the find loop's back edge is 0x845cc beqz -> L1 (taken: the next pass) with 0x845d0 j 0x84554
   (not taken: impossible, r' = 0 mod 4). *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgParseF.v at f7246d55e8c3 for image B
   (fuzz_rate.asan-ubsan); the image is lib/AU/Img0.v's and the cut vocabulary lib/AU/RtPgParseBaseB.v's; the pcs are
   image B's; P + 8 is in a1 (atom 11) at L1, image A's a0; the ret 0 leaves go through 0x84804 li a0,0; the trap
   branch 0x848ac is new and image A's alignment branch 0x84638 is gone. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/AU/RtPgParseFB.v, with its module paths and module names changed; 1569 of its 1626 lines of code are new or changed and 510 lines of the source are left out. *)
(* reac_headamp_prop_parse_result 0x845b4 of reac-pw/fuzz_headamp's ASan image A (fuzz_headamp.asan, pinned sha256
   f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47; unstripped twin
   b5f352154c54a97c66fd92dfa228e8a854498f6cd313dba0107900546b043f9a, the same loaded bytes except .note.gnu.build-id), segment KEY: from the cut
   KEY 0x849e4 (strncmp said the key has the prefix) to ADV 0x84b00 (a refusal) or VAL 0x84b30 (the key read as the
   cell address (ch, p)). It proves lib/A/HPgParseCut.v's segKEY_stmt. Proves function reac_headamp_prop_parse_result
   in part (kind: segment lemma).

   The code (neutral listing of the pinned image):
     0x849e4 sd s9,24(sp) (rf); 0x849e8 .. 0x849f0 [sp + 40] = keys + 1; 0x849f4 s9 = s8 + 13 (rest, the key text
       after the prefix); 0x849f8 sb zero,4(s10) (the end pointer's shadow byte, a hole byte: PAT_KEY -> PAT_DOT);
       0x849fc sd zero,96(sp) (the end pointer e = sp + 0x60); 0x84a00 .. 0x84a0c strtol(rest, e, 10) through the
       strtol wrapper (jal 0x41c28);
     0x84a10 s8 = the value, a0 = *e, a7 = 4; 0x84a1c beq a0,s9 (no digit) -> 0x84aac;
       0x84a20 .. 0x84a30 the instrumented check of *e (a pod byte); 0x84a34 lbu; 0x84a3c bne '.' -> 0x84adc;
       0x84a40 s9 = name = e + 1; 0x84a44 .. 0x84a50 strcmp(name, "phantom" 0x21480); 0x84a54 [sp + 8] = 2;
       0x84a5c beqz -> 0x84ac0 (p = 0); 0x84a60 .. 0x84a6c strcmp(name, "pad" 0x214a0); 0x84a70 beqz -> 0x84ac8
       (p = 1); 0x84a74 .. 0x84a80 strcmp(name, "sens" 0x214c0); 0x84a84 .. 0x84a94 a1 = rf, a4 = [sp + 32], a5 = 8,
       a6 = [sp + 48], a7 = 4; 0x84a98 bnez -> 0x84ae8; p = 2, [sp + 8] = 0x38;
     0x84acc / 0x84ad0 a6 = [sp + 48]; 0x84ad4 bltu s8,48 -> 0x84b28 (sb 0xf8 back to PAT_KEY, VAL 0x84b30);
       else a7 = 5 (OUT_OF_RANGE);
     0x84adc .. 0x84ae4 a1 = rf, a4 = [sp + 32], a5 = 8; 0x84ae8 .. 0x84aec sb 0xf8,4(s10) (back to PAT_KEY);
       0x84af0 .. 0x84afc s9 = (rf = 0 ? a7 : rf), s8 = 0; ADV 0x84b00.
   The model is Pod/Headamp.v parse_key on rest (lib/A/HPgParseGKey.v hgk_key_refuse, hgk_key_val).

   The proof: the engine (lib/Reusable YCbq / YCbn, the hole runners of lib/A/HPgHole.v) runs from a cut of its own
   at each place below, on the temporaries [spa, spa + 0x80) and the hole at s10 (and, after strtol, the byte at the
   end pointer with its shadow entry); every run stops at a wrapper's trampoline or at one of the two stores of 0xf8:
     pky_seg_a   KEY -> strtol (HPgHole.hj_strtol_at, pky_strtol_call) -> KT_at at 0x84a10;
     pky_seg_1   0x84a10 -> RF_at at 0x84ae8 (no digit, or *dot <> '.') | strcmp "phantom" -> KC_at 0 at 0x84a54;
     pky_seg_c0  0x84a54 -> VL_at at 0x84b28 | RF_at (out of range) | strcmp "pad" -> KC_at 1 at 0x84a70;
     pky_seg_c1  0x84a70 -> VL_at | RF_at | strcmp "sens" -> KC_at 2 at 0x84a84;
     pky_seg_c2  0x84a84 -> RF_at (no name) | VL_at | RF_at (out of range);
     pky_rf      0x84ae8 -> ADV 0x84b00 (rf' = rf, or the code when rf = 0); pky_vl 0x84b28 -> VAL 0x84b30.
   Every strcmp call is HPgHole.hj_strcmp_at with the name's meet from HPgParseGKey.hgk_str_meet (pky_strcmp_call).
   Section hypotheses: errno_low : api_env rsegs B; HBerrno : as_errno B = 0x5d7cac;
   STRTOL : forall F fc, hd_astrtol_hole (fx := mkFP F fc) rsegs B A_TRAMP_STRTOL (hi_gotw headamp_himg_A)
     (hi_guard headamp_himg_A);
   STRCMP : forall F fc, hd_astrcmp_hole (fx := mkFP F fc) rsegs B A_TRAMP_STRCMP. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import Img0 HPgBase HPgCSpec HPgImgA HPgHole.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgParseBase HPgParseCut HPgParseGWalk HPgParseGKit HPgParseGKey.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A.Rt Require Import FMupoison.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

Local Abbreviation pctx := (@hp_ctx rsegs).

(* ======================================= the segment's numbers ======================================= *)
Definition PK_RA_STRTOL : Z := 0x84a10.          (* strtol's return *)
Definition PK_RA_CMP1 : Z := 0x84a54.            (* the three strcmp returns *)
Definition PK_RA_CMP2 : Z := 0x84a70.
Definition PK_RA_CMP3 : Z := 0x84a84.
(* the shadow span of a run that checks no shadow byte: empty, apart from every window (the hole's too) *)
Definition pky_Bspan0 : Z * Z := (0, 0).

(* the key text after the prefix and its address *)
Definition pky_rest (x : pctx) (ck : Z) : list byte := skipn 13 (hp_kstr x ck).
Definition pky_xr (x : pctx) (ck : Z) : Z := hx_P x + ck + 8 + 13.

(* ======================================= the run from KEY to the strtol call ======================================= *)
(* the temporaries [spa, spa + 0x80) with the cells the segment reads later ([sp + 16] slot 48, [sp + 32] slot 49,
   [sp + 40] = keys slot 47, [sp + 48] slot 50), and the hole at PAT_KEY *)
Definition pky_cs_a : list YP09.chunk :=
[YP09.mkChunk 16 (CVal 8 (SOff 48 0)); YP09.mkChunk 32 (CVal 8 (SOff 49 0)); YP09.mkChunk 40 (CVal 8 (SOff 47 0));
 YP09.mkChunk 48 (CVal 8 (SOff 50 0))].

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis errno_low : api_env rsegs B.
Hypothesis HBerrno : as_errno B = 0x5d7cac.
Hypothesis STRTOL : forall F fc, hd_astrtol_hole (fx := mkFP F fc) rsegs B A_TRAMP_STRTOL (hi_gotw headamp_himg_A)
  (hi_guard headamp_himg_A).
Hypothesis STRCMP : forall F fc, hd_astrcmp_hole (fx := mkFP F fc) rsegs B A_TRAMP_STRCMP.

Local Abbreviation call_ok := (@call_ok fx rc SK B).
Implicit Types x : pctx.

Lemma pky_w64 : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (w64 z) = z.
Proof. intros z Hz. unfold w64. apply unsigned_lit_small. exact Hz. Qed.

Lemma pky_vm_eqmod : forall (m : word -> option byte) a v w, val_mem rsegs m a 8 v -> v mod 2 ^ 64 = w mod 2 ^ 64 ->
val_mem rsegs m a 8 w.
Proof.
intros m a v w H E k Hk. rewrite (H k Hk). unfold YO0f.le_byte.
change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64). rewrite E. reflexivity.
Qed.

(* the segment's own env slots *)
Definition pky_La (x : pctx) (r cc : Z) (keys : Z) : list word :=
[w64 keys; w64 ((hx_P x + r + 8) mod 8 + 3); w64 (hx_P x + r + 16); w64 (shadow_addr (hx_P x + cc))].

(* an 8-byte chunk of the segment's slots, from the cell's value at the cut *)
Lemma pky_chunk8 : forall E (m : word -> option byte) base off (n : nat) v,
ew E n = w64 v -> val_mem rsegs m (base + off) 8 v ->
YP09.chunk_ok rsegs E m base (YP09.mkChunk off (CVal 8 (SOff n 0))).
Proof.
intros E m base off n v Hn Hv.
apply (chunk_ok_val rsegs E m base off 8 (SOff n 0) (v mod 2 ^ 64)).
- rewrite hk_sv_SOff0, Hn. unfold w64. apply Z_to_bv64_eq_mod. rewrite Z.mod_mod by lia. reflexivity.
- change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). apply Z.mod_pos_bound. lia.
- lia.
- apply (pky_vm_eqmod _ _ v); [exact Hv | rewrite Z.mod_mod by lia; reflexivity].
Qed.

(* the entry state at a cut inside the segment: the temporaries [spa, spa + 0x80) with the chunks cs and the hole
   with the pattern pat *)
Definition pky_ss (pc : Z) (cs : list YP09.chunk) (pat : list Z) : sstate :=
mkSS pc sr_atoms [hk_temps cs; hk_hole_rg pat] None (mkFacts hk_atoms [] []).

Lemma pky_spa64 : forall x, call_ok x -> 0 <= hx_spa x < 2 ^ 64 /\ 0 <= hx_shf x < 2 ^ 64.
Proof.
intros x Hc. pose proof (hk_frame_win B x Hc) as (W1 & W2 & W3 & W4 & W5).
pose proof (hk_stack B x Hc) as (S1 & S2 & S3 & S4 & S5 & S6 & _).
pose proof (hk_hole_band B x (hx_shf x) Hc ltac:(unfold hp_hole; lia)) as (H1 & H2).
unfold kHighShadowEnd, SHADOW_OFF in H1. assert (HT : T_parse_STK = 12576) by reflexivity. lia.
Qed.

Lemma pky_entry : forall x pat cl rb regs mem md L cs pc F fc, call_ok x ->
hp_core B x pat cl rb regs mem md -> length pat = 8%nat ->
regions_wf [hk_temps cs; hk_hole_rg pat] = true ->
Forall (YP09.chunk_ok rsegs (hk_env x regs L) (hx_rd x mem) (hx_spa x)) cs ->
st_ok (fx := mkFP F fc) rsegs (hk_env x regs L) (pky_ss pc cs pat)
  (restrict (w_H (hx_W x)) (mkst (fx := mkFP F fc) regs (Z_to_bv 64 pc) mem (seg_rom rsegs))).
Proof.
intros x pat cl rb regs mem md L cs pc F fc Hc HC Hl Hwf Hcs.
pose proof (hk_core_cregs B x _ _ _ _ _ _ HC) as HCR.
pose proof HCR as (R2 & R8 & R3 & R4 & R9 & R18 & R19 & R26 & R27).
pose proof (pky_spa64 x Hc) as (P1 & P2).
set (E := hk_env x regs L).
assert (U2 : bv_unsigned (ew E 2) = hx_spa x).
{ subst E. rewrite (hk_env_reg x regs _ 2 2%bv eq_refl), R2. apply pky_w64. lia. }
assert (U26 : bv_unsigned (ew E 26) = hx_shf x).
{ subst E. rewrite (hk_env_reg x regs _ 26 26%bv eq_refl), R26. apply pky_w64. lia. }
pose proof (hk_frame_win B x Hc) as (W1 & W2 & W3 & W4 & W5).
pose proof (hk_stack B x Hc) as HSt.
pose proof (hk_hole_band B x (hx_shf x) Hc ltac:(unfold hp_hole; lia)) as (H1 & H2).
rewrite restrict_mkst_fx. unfold pky_ss. apply (entry_st_ok_full rsegs).
- apply regs_ok_Ereg.
- exact Hwf.
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  + exact (hk_temps_ok B x pat cl _ regs mem md _ _ Hc HC Hcs).
  + exact (hk_hole_ok B pa_segs_low x pat cl _ regs mem md _ Hc HC Hl).
- apply pairwise_disjoint_of_extents. unfold extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val hk_temps hk_hole_rg].
  unfold E, hk_env in U2, U26. rewrite U2, U26.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat split; try exact I. unfold SHADOW_OFF, kHighShadowEnd in H1. pose proof asan_consts as (C1 & _). lia.
- split; [|split; [exact I | exact I]]. cbn [f_atoms]. rewrite <- (app_nil_r hk_atoms).
  apply (hk_atoms_ok B x regs _ [] Hc HCR). exact I.
Qed.

(* ---- the window the segment's runs write: the temporaries and the hole ---- *)
Definition pky_win (x : pctx) (a : Z) : Prop := (hx_spa x <= a < hx_spa x + 0x80) \/ hp_hole x a.
Definition pky_KW (x : pctx) (m0 m : word -> option byte) : Prop :=
forall a, 0 <= a < 2 ^ 64 -> ~ pky_win x a -> hx_rd x m (Z_to_bv 64 a) = hx_rd x m0 (Z_to_bv 64 a).

Lemma pky_KW_refl : forall x m, pky_KW x m m.
Proof. intros x m a _ _. reflexivity. Qed.

Lemma pky_KW_step : forall x E rs (m0 m1 m2 : word -> option byte), pky_KW x m0 m1 ->
frame_of E rs (hx_rd x m1) (hx_rd x m2) -> (forall a, in_wrange E rs a -> pky_win x a) -> pky_KW x m0 m2.
Proof.
intros x E rs m0 m1 m2 HK HF HW a Ha Hn. rewrite <- (HK a Ha Hn). apply HF.
rewrite unsigned_lit_small by exact Ha. intros X. exact (Hn (HW a X)).
Qed.

(* every byte of the temporaries and of the hole is the journal's or a hole byte *)
Lemma pky_awr_temps : forall x E rs cs U, call_ok x -> bv_unsigned (ew E 2) = hx_spa x ->
awr_okH E rs (hx_STK x) (hx_sp0 x) (hx_FP x) (ablocks B (hx_ly x) (hx_S x)) (ablocks B (hx_lyc x) (hx_Sc x))
  (hx_lyc x) (hx_own x) U ->
awr_okH E (YP09.mkRegion (Some 2%nat) 0 0x80 0 0x80 cs :: rs) (hx_STK x) (hx_sp0 x) (hx_FP x)
  (ablocks B (hx_ly x) (hx_S x)) (ablocks B (hx_lyc x) (hx_Sc x)) (hx_lyc x) (hx_own x) U.
Proof.
intros x E rs cs U Hc H2 H.
pose proof (hk_stack B x Hc) as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & S13).
pose proof (hk_frame_win B x Hc) as (W1 & W2 & W3 & W4 & W5).
assert (HT : T_parse_STK = 12576) by reflexivity.
apply (awr_okH_cons_gen _ _ _ _ _ _ _ _ _ _ _ 2 (hx_spa x)); [reflexivity | exact H2 | | exact H].
intros a Ha. left. left. cbn [YP09.r_wlo YP09.r_whi] in Ha. lia.
Qed.

Lemma pky_awr_hole : forall x E rs hs pat, bv_unsigned (ew E 26) = hx_shf x -> length pat = 8%nat ->
awr_okH E rs (hx_STK x) (hx_sp0 x) (hx_FP x) (ablocks B (hx_ly x) (hx_S x)) (ablocks B (hx_lyc x) (hx_Sc x))
  (hx_lyc x) (hx_own x) (hU (hx_fr x) pat) ->
awr_okH E (YP09.mkRegion (Some 26%nat) 0 8 0 8 hs :: rs) (hx_STK x) (hx_sp0 x) (hx_FP x)
  (ablocks B (hx_ly x) (hx_S x)) (ablocks B (hx_lyc x) (hx_Sc x)) (hx_lyc x) (hx_own x) (hU (hx_fr x) pat).
Proof.
intros x E rs hs pat H26 Hl H.
apply (awr_okH_cons_hole _ _ _ _ _ _ _ _ _ _ (hx_fr x) pat 26); [reflexivity | exact H26 | cbn; lia | | exact H].
rewrite Hl. cbn. lia.
Qed.

(* hp_core at the new pattern at a stop whose memory differs from the cut's only in the window *)
Lemma pky_core_stop : forall x pat pat' cl rb regs mem md (regs' : bvmap 5 word) mem' md',
call_ok x -> Z.of_nat (length cl) <= hx_cap x -> Z.of_nat (length rb) <= 12 ->
hp_core B x pat cl rb regs mem md ->
ajournal rsegs B (hx_STK x) (hx_sp0 x) (hx_FP x) (hx_ly x) (hx_S x) (hx_W0 x) (hx_mem0 x) (hx_md0 x) (hx_own x)
  (hx_lyc x) (hx_Sc x) (hx_W x) (unpoison (hU (hx_fr x) pat) mem') md' (hx_k x) ->
length pat' = length pat -> Forall (fun v => 0 <= v < 256) pat' -> hpat rsegs (hx_W x) mem' (hx_fr x) pat' ->
same_io md md' -> pky_KW x mem mem' -> hk_cregs x regs' ->
hp_core B x pat' cl rb regs' mem' md'.
Proof.
intros x pat pat' cl rb regs mem md regs' mem' md' Hc Hcl Hrb HC HJ' Hl Hb HP' Hio HKW HR'.
pose proof (hk_core_journal B x _ _ _ _ _ _ HC) as (_ & OK & _).
pose proof (hk_core_cregs B x _ _ _ _ _ _ HC) as HR.
pose proof (hk_frame_win B x Hc) as (W1 & W2 & W3 & W4 & W5).
pose proof errno_low as ((Er0 & Er4) & _ & _). unfold kLowMemEnd in Er4.
pose proof (hk_stack B x Hc) as HSt. pose proof asan_consts as (C1 & _).
assert (HT : T_parse_STK = 12576) by reflexivity.
assert (KV : forall a, 0 <= a < 2 ^ 64 -> ~ pky_win x a -> hx_view x mem' a = hx_view x mem a).
{ intros a Ha Hn. unfold hx_view. apply aview_eq_of. exact (HKW a Ha Hn). }
pose proof HC as (_ & _ & _ & _ & _ & _ & (ev & Hev) & _).
destruct HR' as (A2 & A8 & A3 & A4 & A9 & A18 & A19 & A26 & A27).
destruct HR as (B2 & B8 & B3 & B4 & B9 & B18 & B19 & B26 & B27).
apply (hgk_core_keep B pa_segs_low errno_low x pat pat' cl rb regs mem md regs' mem' md' (pky_win x) Hc Hcl Hrb HC);
  try congruence.
- exact (hj_repat_raw rsegs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ pat pat' HJ' OK Hl Hb HP').
- exact KV.
- intros a Ha. destruct Ha as [Hs|Hh]; [left | right; left; exact Hh]. lia.
- exists ev. intros k Hk. rewrite <- (Hev k Hk). apply KV; [lia|].
  intros Hw. destruct Hw as [Hs|Hh]; [lia|].
  pose proof (hk_hole_band B x _ Hc Hh) as (A1 & _). unfold SHADOW_OFF in A1. lia.
Qed.

(* ======================================= a stopped run's facts ======================================= *)

(* an 8-byte chunk of a stopped run's region at sp *)
Lemma pky_cell : forall {fy : YK11.FPState} E ss ms (H : word -> bool) (rg : YP09.region) base off (v : sv) z,
st_ok (fx := fy) rsegs E ss (restrict H ms) -> In rg (ss_mem ss) -> base_val E (YP09.r_base rg) = base ->
In (YP09.mkChunk off (CVal 8 v)) (YP09.r_chunks rg) -> U E v = z ->
val_mem rsegs (mrestrict H (ms_mem ms)) (base + off) 8 z.
Proof.
intros fy E ss ms H rg base off v z HS Hin Hb Hc Hz.
pose proof (st_ok_mem_ok rsegs E ss _ HS) as (_ & HR & _).
pose proof (proj1 (Forall_forall _ _) HR rg Hin) as (_ & _ & _ & HC).
pose proof (proj1 (Forall_forall _ _) HC _ Hc) as HCk. rewrite Hb in HCk.
apply (val_of_chunk_ok rsegs E _ base off 8 v z HCk); [rewrite denot_lit_U, Hz; reflexivity | | lia].
rewrite <- Hz. pose proof (U_range E v) as R. unfold M64 in R. change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
Qed.

(* a 1-byte literal chunk of a stopped run's region: the byte through the view *)
Lemma pky_byte : forall {fy : YK11.FPState} E ss ms (W : world rsegs) (rg : YP09.region) base off v,
st_ok (fx := fy) rsegs E ss (restrict (w_H W) ms) -> In rg (ss_mem ss) -> base_val E (YP09.r_base rg) = base ->
In (YP09.mkChunk off (CVal 1 (SLit v))) (YP09.r_chunks rg) ->
aview rsegs (w_H W) (ms_mem ms) (base + off) = Some ((v mod 2 ^ 64) mod 256).
Proof.
intros fy E ss ms W rg base off v HS Hin Hb Hc.
pose proof (st_ok_mem_ok rsegs E ss _ HS) as (_ & HR & _).
pose proof (proj1 (Forall_forall _ _) HR rg Hin) as (_ & _ & _ & HC).
pose proof (proj1 (Forall_forall _ _) HC _ Hc) as HCk. rewrite Hb in HCk.
destruct (HCk 0 ltac:(cbn; lia)) as (b & Hb1 & Hb2). cbn [cbyte YP09.c_val YP09.c_off] in Hb1.
injection Hb1 as <-. rewrite Z.add_0_r in Hb2. unfold aview.
change (ms_mem (restrict (w_H W) ms)) with (mrestrict (w_H W) (ms_mem ms)) in Hb2.
change (base + YP09.c_off (YP09.mkChunk off (CVal 1 (SLit v)))) with (base + off) in Hb2. rewrite Hb2.
cbn [option_map]. f_equal.
Qed.

(* a byte of one of the image's loaded segments, by computation *)
Lemma pky_in_img_b : forall a,
existsb (fun s => (Z.of_N (seg_base s) <=? a) && (a <? Z.of_N (seg_base s) + Z.of_N (seg_size s))) rsegs = true ->
in_img rsegs a.
Proof.
intros a H. apply existsb_exists in H as (s & Hin & Hs). apply andb_prop in Hs as [H1 H2].
apply Z.leb_le in H1. apply Z.ltb_lt in H2. exists s. split; [exact Hin | lia].
Qed.

(* the stack-guard words: the GOT word 0x9cff8 and the guard 0x5f7d90 *)
Lemma pky_in_img_w : forall a k, (a = 0x9cff8 \/ a = 0x5f7d90) -> 0 <= k < 8 -> in_img rsegs (a + k).
Proof.
intros a k Ha Hk. apply pky_in_img_b.
assert (k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7) as Hk' by lia.
destruct Ha as [-> | ->]; destruct Hk' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]];
  vm_compute; reflexivity.
Qed.

(* ======================================= the key's text in the pod ======================================= *)
Lemma pky_pod_view : forall x (mem : word -> option byte) j,
garr8 rsegs (hx_rd x mem) (hx_P x) (hd_zbytes (hx_bs x)) -> (j < length (hx_bs x))%nat ->
hx_view x mem (hx_P x + Z.of_nat j) = Some (bv_unsigned (nth j (hx_bs x) Cursor.NUL)).
Proof.
intros x mem j HG Hj. unfold hx_view, aview. change (mrestrict (w_H (hx_W x)) mem) with (hx_rd x mem).
rewrite (garr8_mbyte rsegs _ _ _ j HG) by (unfold hd_zbytes; rewrite length_map; exact Hj).
cbn [option_map]. rewrite hgw_nth_zbytes, Z_to_bv_bv_unsigned. reflexivity.
Qed.

(* rest = the key text after its 13 prefix bytes: a C string at P + ck + 8 + 13 inside the pod *)
Lemma pky_rest_view : forall x ck (mem : word -> option byte), hp_key_ok x ck ->
Headamp.ha_prefix (hp_kstr x ck) = true ->
garr8 rsegs (hx_rd x mem) (hx_P x) (hd_zbytes (hx_bs x)) ->
(forall i, (i <= length (pky_rest x ck))%nat ->
  hx_view x mem (pky_xr x ck + Z.of_nat i) =
  Some (bv_unsigned (nth i (pky_rest x ck ++ [Z_to_bv 8 0]) (Z_to_bv 8 0)))) /\
~ In (Z_to_bv 8 0) (pky_rest x ck) /\ (13 <= length (hp_kstr x ck))%nat /\
length (pky_rest x ck) = (length (hp_kstr x ck) - 13)%nat /\
ck + 8 + Z.of_nat (length (hp_kstr x ck)) + 1 <= hx_len x.
Proof.
intros x ck mem HK HP HG.
pose proof HK as (Hck & _ & _).
destruct (hgw_key_bytes x ck HK) as (Hnz & L1 & L2 & Hb & Hz).
pose proof (hgk_prefix_len _ HP) as L13.
assert (Lr : length (pky_rest x ck) = (length (hp_kstr x ck) - 13)%nat) by (unfold pky_rest; apply length_skipn).
unfold hx_len in *.
split; [|split; [exact (hgk_nonul_skipn _ 13 Hnz) | split; [exact L13 | split; [exact Lr | lia]]]].
intros i Hi.
replace (pky_xr x ck + Z.of_nat i) with (hx_P x + Z.of_nat (Z.to_nat (ck + 8) + (13 + i))) by (unfold pky_xr; lia).
rewrite (pky_pod_view x mem _ HG) by lia. f_equal.
destruct (Nat.lt_ge_cases i (length (pky_rest x ck))) as [Hl|Hl].
- rewrite (Hb (13 + i)%nat) by lia. rewrite app_nth1 by exact Hl. unfold pky_rest. rewrite hgw_nth_skipn. reflexivity.
- assert (i = length (pky_rest x ck)) as -> by lia. rewrite nth_middle.
  replace (Z.to_nat (ck + 8) + (13 + length (pky_rest x ck)))%nat with (Z.to_nat (ck + 8) + length (hp_kstr x ck))%nat
    by lia.
  rewrite Hz. reflexivity.
Qed.

(* ======================================= the strtol call ======================================= *)
Lemma pky_strtol_call : forall x r cc n ck cl keys rf F fc (regsT : bvmap 5 word) memT mdT
  (Q : world rsegs -> config -> Prop),
call_ok x -> hp_m_key x r cc n ck cl keys rf ->
hp_core B x PAT_DOT cl (ha_res_bytes 0 0 0) regsT memT mdT ->
getr regsT 10 = w64 (pky_xr x ck) -> getr regsT 11 = w64 (hx_spa x + 96) -> getr regsT 12 = w64 10 ->
getr regsT 1 = w64 PK_RA_STRTOL ->
(forall regs2 mem2 md2, hp_core B x PAT_DOT cl (ha_res_bytes 0 0 0) regs2 mem2 md2 -> aregs_preserved regsT regs2 ->
   getr regs2 10 = w64 (PIS.s10_val (pky_rest x ck)) ->
   rdword (hx_view x mem2) (hx_spa x + 96) = Some (pky_xr x ck + PIS.s10_end (pky_rest x ck)) ->
   (forall a, 0 <= a < 2 ^ 64 -> ~ (hx_spa x - 3 * ESTACK <= a < hx_spa x) -> ~ (hx_spa x + 0x60 <= a < hx_spa x + 0x68) ->
      ~ (as_errno B <= a < as_errno B + 4) -> hx_view x mem2 a = hx_view x memT a) ->
   SRr rsegs (hx_W x) (cfg_at (fx := mkFP F fc) rsegs PK_RA_STRTOL regs2 mem2 md2) Q) ->
SRr rsegs (hx_W x) (cfg_at (fx := mkFP F fc) rsegs A_TRAMP_STRTOL regsT memT mdT) Q.
Proof.
intros x r cc n ck cl keys rf F fc regsT memT mdT Q Hc HM HC R10 R11 R12 R1 HK.
pose proof HM as (Hnull & Hst & Hc1 & Hc8 & Hin & Hn & HKok & (Hcl & Hk0 & Hrf) & HP & HW).
pose proof (hk_core_cregs B x _ _ _ _ _ _ HC) as (R2 & R8 & R3 & R4 & R9 & R18 & R19 & R26 & R27).
pose proof HC as (HJ & _ & _ & _ & _ & _ & (ev & Hev) & _).
pose proof HJ as (HJ0 & OK & HPt).
pose proof (hk_stack B x Hc) as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & S13).
pose proof (hk_frame_win B x Hc) as (W1 & W2 & W3 & W4 & W5).
pose proof (hk_pod B x Hc Hnull) as (HP0 & HP16 & Hlen & Hlen8 & HSZ & HP63 & _ & HPin & HPO & HPR & HPE & _ & _ & HAM & HPoff).
pose proof (hk_pod_at_cut B pa_segs_low x PAT_DOT cl _ regsT memT mdT errno_low Hc Hnull HC ltac:(lia)) as (HG & HRA & HHV).
pose proof (hk_pod_side B x Hc Hnull) as Hside.
pose proof (hk_call_regs B x Hc) as (_ & _ & _ & _ & _ & _ & _ & Hgp & Htp).
pose proof (hk_call_args B x Hc) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Gw & Gg) & _).
destruct (pky_rest_view x ck memT HKok HP HG) as (HV & Hnz & L13 & Lr & Lk).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HKok as (Hck0 & Hck1 & _).
pose proof (lo_img _ (hgk_layout B x Hc)) as (I1 & I2 & I3 & _).
assert (HT : T_parse_STK = 12576) by reflexivity. assert (HE : ESTACK = 4096) by reflexivity.
unfold hx_len in *.
set (rest := pky_rest x ck) in *. set (xr := pky_xr x ck) in *.
assert (Exr : xr = hx_P x + ck + 21) by (unfold xr, pky_xr; lia).
clearbody rest xr.
(* the guard words are kept since the call *)
assert (KI : forall a k, (a = 0x9cff8 \/ a = 0x5f7d90) -> 0 <= k < 8 ->
  aview rsegs (w_H (hx_W x)) memT (a + k) = aview rsegs (w_H (hx_W x)) (hx_memc x) (a + k)).
{ intros a k Ha Hk. apply (hk_kept_img B pa_segs_low x PAT_DOT cl _ regsT memT mdT (a + k) Hc HC ltac:(lia)).
  - exact (pky_in_img_w a k Ha Hk).
  - rewrite HBerrno. lia. }
unfold cfg_at. eapply SRr_bind.
{ apply (hj_strtol_at rsegs B pa_segs_low errno_low A_TRAMP_STRTOL (hi_gotw headamp_himg_A) (hi_guard headamp_himg_A)
    (STRTOL F fc) (hx_W x) regsT memT (hx_STK x) (hx_sp0 x) (hx_FP x) (hx_ly x) (hx_S x) (hx_W0 x) (hx_mem0 x) (hx_md0 x)
    (hx_own x) (hx_lyc x) (hx_Sc x) mdT (hx_k x) xr (hx_spa x + 96) rest ev (hx_spa x - hx_sp0 x) (w64 PK_RA_STRTOL)
    (hx_fr x) PAT_DOT HJ).
  - exact R10.
  - exact R11.
  - exact R12.
  - lia. (* 0 < x *)
  - lia.
  - unfold spZ. rewrite R2, pky_w64 by lia. lia.
  - lia.
  - lia.
  - lia.
  - rewrite R3. exact Hgp.
  - rewrite R4. exact Htp.
  - exact R1.
  - apply ret_ok_even. vm_compute. reflexivity.
  - cbn [hi_gotw hi_guard headamp_himg_A] in Gw, Gg |- *. split.
    + apply (hk_rdword_kept _ _ _ _ (fun k Hk => KI 0x9cff8 k (or_introl eq_refl) Hk) Gw).
    + destruct Gg as (can & Gg). exists can.
      apply (hk_rdword_kept _ _ _ _ (fun k Hk => KI 0x5f7d90 k (or_intror eq_refl) Hk) Gg).
  - split; [|exact Hnz]. intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. apply HV. lia.
  - lia.
  - split; [lia|]. split; [lia|]. split; [lia|].
    split; [|split; [|split]].
    + intros a Ha. split.
      * apply (hk_garr8_some _ _ _ _ HG). unfold hd_zbytes. rewrite length_map. lia.
      * unfold spZ. rewrite R2, pky_w64 by lia. lia.
    + unfold amem_range in *. lia.
    + apply (range_addressable_sub _ _ (hx_P x) (Z.of_nat (length (hx_bs x)))); [exact HRA | lia | lia].
    + intros _. apply (hk_hull_sub _ (hx_P x) (Z.of_nat (length (hx_bs x)))); [exact HHV | lia | lia | lia].
  - unfold amem_range in *. lia.
  - apply (hgw_str_tail (w_H (hx_W x)) memT (hx_P x) (hd_zbytes (hx_bs x))); [exact HG | lia | |].
    + unfold hd_zbytes. rewrite length_map. exact Hlen8.
    + unfold hd_zbytes. rewrite length_map. lia.
  - lia.
  - lia.
  - lia.
  - unfold amem_range. right. unfold kHighMemBeg, kHighMemEnd in *. lia.
  - replace (hx_spa x + 96) with (hx_fr x + 32) by lia.
    exact (proj1 (hd_dot_ok rsegs B (hx_lyc x) (hx_Sc x) (hx_fr x) (hx_W x) memT mdT (conj (proj1 HJ0) (conj OK HPt))
      S12 S13)).
  - replace (hx_spa x + 96) with (hx_fr x + 32) by lia.
    exact (proj2 (hd_dot_ok rsegs B (hx_lyc x) (hx_Sc x) (hx_fr x) (hx_W x) memT mdT (conj (proj1 HJ0) (conj OK HPt))
      S12 S13)).
  - lia.
  - rewrite HBerrno. lia.
  - lia.
  - intros a Ha Hz. unfold in_zr in Hz. unfold kImgLo, kImgEnd in *. lia.
  - lia.
  - exact Hev.
  - intros a Ha Ho He. exact (hk_aro_at_cut B pa_segs_low x PAT_DOT cl _ regsT memT mdT Hc HC ltac:(lia) a Ha Ho He). }
cbv beta. intros W' c' _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HPr & Hio2 & R10' & Hend & Herr & HK2 & Hpres2).
replace (hx_sp0 x + (hx_spa x - hx_sp0 x)) with (hx_spa x) in HK2 by lia.
assert (HK3 : forall a, 0 <= a < 2 ^ 64 -> ~ (hx_spa x - 3 * ESTACK <= a < hx_spa x) ->
  ~ (hx_spa x + 0x60 <= a < hx_spa x + 0x68) -> ~ (as_errno B <= a < as_errno B + 4) ->
  hx_view x mem2 a = hx_view x memT a).
{ intros a Ha H1 H2 H3. apply HK2; [exact Ha | lia | exact H3 | exact H1]. }
apply HK.
- apply (hk_core_of_call B pa_segs_low x PAT_DOT cl _ regsT memT mdT regs2 mem2 md2 errno_low Hc HC ltac:(lia) eq_refl
    HJ2 HPr Hio2 HK3).
  eexists. exact Herr.
- exact HPr.
- exact R10'.
- exact Hend.
- exact HK3.
Qed.

(* ======================================= the name after the dot ======================================= *)
Definition pky_en (x : pctx) (ck : Z) : Z := PIS.s10_end (pky_rest x ck).
Definition pky_nm (x : pctx) (ck : Z) : list byte :=
Cursor.cstr (skipn (S (Z.to_nat (pky_en x ck))) (pky_rest x ck)).
Definition pky_dot (x : pctx) (ck : Z) : Prop :=
pky_en x ck <> 0 /\ bv_unsigned (nth (Z.to_nat (pky_en x ck)) (pky_rest x ck) Cursor.NUL) = 46.

Lemma pky_name_view : forall x ck (mem : word -> option byte), hp_key_ok x ck ->
Headamp.ha_prefix (hp_kstr x ck) = true -> garr8 rsegs (hx_rd x mem) (hx_P x) (hd_zbytes (hx_bs x)) -> pky_dot x ck ->
hgk_cstr_at (segs := rsegs) (w_H (hx_W x)) mem (pky_xr x ck + pky_en x ck + 1) (hd_zbytes (pky_nm x ck)) /\
pky_en x ck + 1 + Z.of_nat (length (pky_nm x ck)) = Z.of_nat (length (pky_rest x ck)) /\
0 < pky_en x ck.
Proof.
intros x ck mem HK HP HG (Hen & Hdot).
destruct (pky_rest_view x ck mem HK HP HG) as (HV & Hnz & L13 & Lr & Lk).
pose proof (hgk_end_le (pky_rest x ck)) as Hel. fold (pky_en x ck) in Hel.
pose proof (hgk_nth_len _ _ Hdot) as Hlt.
set (rest := pky_rest x ck) in *. set (en := pky_en x ck) in *.
assert (Hnm : pky_nm x ck = skipn (S (Z.to_nat en)) rest).
{ unfold pky_nm. fold rest en. apply hgk_cstr_nonul. apply hgk_nonul_skipn. exact Hnz. }
assert (Lnm : length (pky_nm x ck) = (length rest - S (Z.to_nat en))%nat) by (rewrite Hnm; apply length_skipn).
assert (Hnz' : ~ In Cursor.NUL (pky_nm x ck)) by (rewrite Hnm; apply hgk_nonul_skipn; exact Hnz).
split; [|split; lia].
split; [|split].
- intros i Hi. unfold hd_zbytes in Hi. rewrite length_map in Hi.
  pose proof (HV (S (Z.to_nat en) + Z.to_nat i)%nat ltac:(lia)) as E.
  replace (pky_xr x ck + Z.of_nat (S (Z.to_nat en) + Z.to_nat i)) with (pky_xr x ck + en + 1 + i) in E by lia.
  unfold hx_view in E. rewrite E. f_equal. rewrite hgw_nth_zbytes, Hnm, hgw_nth_skipn. rewrite app_nth1 by lia. reflexivity.
- unfold hd_zbytes. rewrite length_map.
  pose proof (HV (length rest) ltac:(lia)) as E.
  replace (pky_xr x ck + en + 1 + Z.of_nat (length (pky_nm x ck))) with (pky_xr x ck + Z.of_nat (length rest)) by lia.
  unfold hx_view in E. rewrite E. rewrite app_nth2, Nat.sub_diag by lia. reflexivity.
- exact (hgk_zbytes_pos _ Hnz').
Qed.

(* ======================================= a strcmp call ======================================= *)
Lemma pky_strcmp_call : forall x r cc n ck cl keys rf F fc (regsT : bvmap 5 word) memT mdT ra y nmL
  (Q : world rsegs -> config -> Prop),
call_ok x -> hp_m_key x r cc n ck cl keys rf -> pky_dot x ck ->
hp_core B x PAT_DOT cl (ha_res_bytes 0 0 0) regsT memT mdT ->
hd_cstr rsegs (w_H (hx_W x)) (hx_memc x) y (hd_zbytes nmL) -> y + Z.of_nat (length nmL) + 1 <= as_errno B ->
getr regsT 10 = w64 (pky_xr x ck + pky_en x ck + 1) -> getr regsT 11 = w64 y ->
getr regsT 1 = w64 ra -> YK0s.ret_ok (w64 ra) ->
(forall regs2 mem2 md2 res, hp_core B x PAT_DOT cl (ha_res_bytes 0 0 0) regs2 mem2 md2 ->
   aregs_preserved regsT regs2 -> getr regs2 10 = w64 res -> -1 <= res <= 1 -> (res = 0 <-> pky_nm x ck = nmL) ->
   (forall a, 0 <= a < 2 ^ 64 -> ~ (hx_spa x - 2 * ESTACK <= a < hx_spa x) -> hx_view x mem2 a = hx_view x memT a) ->
   SRr rsegs (hx_W x) (cfg_at (fx := mkFP F fc) rsegs ra regs2 mem2 md2) Q) ->
SRr rsegs (hx_W x) (cfg_at (fx := mkFP F fc) rsegs A_TRAMP_STRCMP regsT memT mdT) Q.
Proof.
intros x r cc n ck cl keys rf F fc regsT memT mdT ra y nmL Q Hc HM Hd HC Hcs Hyer R10 R11 R1 Hra HK.
pose proof HM as (Hnull & Hst & Hc1 & Hc8 & Hin & Hn & HKok & (Hcl & Hk0 & Hrf) & HP & HW).
pose proof (hk_core_cregs B x _ _ _ _ _ _ HC) as (R2 & R8 & R3 & R4 & R9 & R18 & R19 & R26 & R27).
pose proof HC as (HJ & _ & _ & _ & _ & _ & (ev & Hev) & _).
pose proof (hk_stack B x Hc) as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & S13).
pose proof (hk_frame_win B x Hc) as (W1 & W2 & W3 & W4 & W5).
pose proof (hk_pod B x Hc Hnull) as (HP0 & HP16 & Hlen & Hlen8 & HSZ & HP63 & _ & HPin & HPO & HPR & HPE & _ & _ & HAM & HPoff).
pose proof (hk_pod_at_cut B pa_segs_low x PAT_DOT cl _ regsT memT mdT errno_low Hc Hnull HC ltac:(lia)) as (HG & HRA & HHV).
pose proof (hk_call_regs B x Hc) as (_ & _ & _ & _ & _ & _ & _ & Hgp & Htp).
destruct (pky_rest_view x ck memT HKok HP HG) as (HV & Hnz & L13 & Lr & Lk).
destruct (pky_name_view x ck memT HKok HP HG Hd) as (HN & Lnm & Hen0).
pose proof (hk_cstr_at_cut B pa_segs_low x PAT_DOT cl _ regsT memT mdT y (hd_zbytes nmL) errno_low Hc HC ltac:(lia)
  eq_refl Hcs ltac:(intros i Hi; unfold hd_zbytes in Hi; rewrite length_map in Hi; lia)) as Hcs2.
pose proof Hcs2 as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10).
destruct (hgk_str_meet (segs := rsegs) (hd_zbytes (pky_nm x ck)) (w_H (hx_W x)) memT _ (hd_zbytes nmL) y HN
  (hgk_cstr_of_hd _ _ _ _ Hcs2)) as (kk & c1 & c2 & Hmeet & Hk1 & Hk2 & Hres).
pose proof Hmeet as (Hkk0 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof errno_low as ((Er0 & Er4) & _ & _).
assert (HT : T_parse_STK = 12576) by reflexivity. assert (HE : ESTACK = 4096) by reflexivity.
unfold hd_zbytes in Hk1, Hk2, Y5, Y6, Y7, Y8, Y9, Y10. rewrite length_map in Hk1, Hk2, Y5, Y6, Y7, Y8, Y9, Y10.
unfold hx_len in *.
pose proof HKok as (Hck0 & Hck1 & _).
set (xn := pky_xr x ck + pky_en x ck + 1) in *.
assert (Exn : xn + kk + 1 <= hx_P x + Z.of_nat (length (hx_bs x))).
{ unfold xn, pky_xr. pose proof (length_skipn 13 (hp_kstr x ck)) as Ls. unfold pky_rest in Lnm, Lr. lia. }
assert (Hxn : hx_P x <= xn) by (unfold xn, pky_xr; lia).
assert (OS : forall a, xn <= a < xn + kk + 1 -> ~ (hx_sp x - T_parse_STK <= a < hx_sp x)).
{ intros a Ha. apply HPoff. lia. }
assert (YL : forall i, 0 <= i <= Z.of_nat (length nmL) -> 0 <= y + i < kLowMemEnd).
{ intros i Hi. apply pa_segs_low. apply Y6. lia. }
unfold cfg_at. eapply SRr_bind.
{ apply (hj_strcmp_at rsegs B pa_segs_low A_TRAMP_STRCMP (STRCMP F fc) (hx_W x) regsT memT (hx_STK x) (hx_sp0 x)
    (hx_FP x) (hx_ly x) (hx_S x) (hx_W0 x) (hx_mem0 x) (hx_md0 x) (hx_own x) (hx_lyc x) (hx_Sc x) mdT (hx_k x)
    xn y kk c1 c2 (hx_spa x - hx_sp0 x) (w64 ra) (hx_fr x) PAT_DOT HJ).
  - exact R10.
  - exact R11.
  - unfold xn, pky_xr. lia.
  - lia.
  - unfold spZ. rewrite R2, pky_w64 by lia. lia.
  - lia.
  - lia.
  - lia.
  - rewrite R3. exact Hgp.
  - rewrite R4. exact Htp.
  - exact R1.
  - exact Hra.
  - lia.
  - lia.
  - lia.
  - exact Hmeet.
  - intros a Ha. split.
    + apply (hk_garr8_some _ _ _ _ HG). unfold hd_zbytes. rewrite length_map. lia.
    + unfold spZ. rewrite R2, pky_w64 by lia. pose proof (OS a ltac:(lia)). lia.
  - intros a Ha. split.
    + destruct (Z_lt_le_dec (a - y) (Z.of_nat (length nmL))) as [Hl|Hl].
      * replace a with (y + (a - y)) by lia.
        rewrite (Y1 (a - y)) by (unfold hd_zbytes; rewrite length_map; lia). discriminate.
      * assert (a = y + Z.of_nat (length (hd_zbytes nmL))) as -> by (unfold hd_zbytes; rewrite length_map; lia).
        rewrite Y2. discriminate.
    + unfold spZ. rewrite R2, pky_w64 by lia. pose proof (YL (a - y) ltac:(lia)). lia.
  - intros a Ha. unfold spZ. rewrite R2, pky_w64 by lia. pose proof (OS a ltac:(lia)). lia.
  - intros a Ha. unfold spZ. rewrite R2, pky_w64 by lia. pose proof (YL (a - y) ltac:(lia)). lia.
  - unfold amem_range in *. lia.
  - unfold amem_range in *. lia.
  - apply (range_addressable_sub _ _ (hx_P x) (Z.of_nat (length (hx_bs x)))); [exact HRA | lia | lia].
  - apply (hk_hull_sub _ (hx_P x) (Z.of_nat (length (hx_bs x)))); [exact HHV | lia | lia | lia].
  - apply (range_addressable_sub _ _ y (Z.of_nat (length nmL) + 1)); [exact Y8 | lia | lia].
  - apply (hk_hull_sub _ y (Z.of_nat (length nmL) + 1)); [exact Y9 | lia | lia | lia]. }
cbv beta. intros W' c' _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HPr & Hio2 & R10' & HK2 & Hpres2).
replace (hx_sp0 x + (hx_spa x - hx_sp0 x)) with (hx_spa x) in HK2 by lia.
assert (HK3 : forall a, 0 <= a < 2 ^ 64 -> ~ (hx_spa x - 3 * ESTACK <= a < hx_spa x) ->
  ~ (hx_spa x + 0x60 <= a < hx_spa x + 0x68) -> ~ (as_errno B <= a < as_errno B + 4) ->
  hx_view x mem2 a = hx_view x memT a).
{ intros a Ha H1 H2 H3. apply HK2; [exact Ha | lia]. }
apply (HK regs2 mem2 md2 (hgk_res c1 c2)).
- apply (hk_core_of_call B pa_segs_low x PAT_DOT cl _ regsT memT mdT regs2 mem2 md2 errno_low Hc HC ltac:(lia) eq_refl
    HJ2 HPr Hio2 HK3).
  exists ev. apply (hk_rd32_kept _ _ _ _ (fun k Hk => HK2 (as_errno B + k) ltac:(unfold kLowMemEnd in Er4; lia)
    ltac:(unfold kLowMemEnd in Er4; lia)) Hev).
- exact HPr.
- exact R10'.
- exact (hgk_res_range c1 c2).
- rewrite Hres. split; [intros E; apply hgk_zbytes_inj in E; exact E | intros ->; reflexivity].
- intros a Ha H1. apply HK2; [exact Ha | exact H1].
Qed.

(* ======================================= the state after strtol ======================================= *)
Definition KT_at (x : pctx) (r cc : Z) (n : nat) (ck : Z) (cl : list Headamp.cell) (keys rf : Z)
  (F : bvmap 5 word) (fc : bv 32) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
hp_core B x PAT_DOT cl (ha_res_bytes 0 0 0) regs mem md /\ hp_fxw F fc /\ hp_m_key x r cc n ck cl keys rf /\
pa_loop x r cl (keys + 1) regs mem /\
getr regs 23 = w64 (hx_P x + cc) /\ getr regs 25 = w64 (pky_xr x ck) /\
getr regs 10 = w64 (PIS.s10_val (pky_rest x ck)) /\
val_mem rsegs (hx_rd x mem) (hx_spa x + 24) 8 rf /\
val_mem rsegs (hx_rd x mem) (hx_spa x + 48) 8 (shadow_addr (hx_P x + cc)) /\
val_mem rsegs (hx_rd x mem) (hx_spa x + 96) 8 (pky_xr x ck + PIS.s10_end (pky_rest x ck)).

(* ======================================= the runs' tactics ======================================= *)
(* the hole's chunks hold the pattern: a 1-byte literal at each offset whose low byte is the pattern's *)
Fixpoint pky_lit1 (hs : list YP09.chunk) (o : Z) : option Z :=
match hs with
| [] => None
| c :: hs' => if YP09.c_off c =? o then
                match YP09.c_val c with CVal w (SLit v) => if N.eqb w 1 then Some v else None | _ => None end
              else pky_lit1 hs' o
end.
Lemma pky_lit1_in : forall hs o v, pky_lit1 hs o = Some v -> In (YP09.mkChunk o (CVal 1 (SLit v))) hs.
Proof.
induction hs as [|c hs IH]; intros o v H; [discriminate H|]. cbn [pky_lit1] in H.
destruct (Z.eqb_spec (YP09.c_off c) o) as [E|E].
- destruct c as [oc cv]. cbn in E, H. subst oc. destruct cv as [w e| | |]; try discriminate H.
  destruct e; try discriminate H. destruct (N.eqb_spec w 1) as [->|]; [|discriminate H].
  injection H as ->. left. reflexivity.
- right. exact (IH o v H).
Qed.
Definition pky_hole_chk (hs : list YP09.chunk) (pat : list Z) : bool :=
forallb (fun i => match pky_lit1 hs (Z.of_nat i) with
                  | Some v => (v mod 2 ^ 64) mod 256 =? nth i pat 0 | None => false end) (seq 0 8).

Lemma pky_hpat_rg' : forall {fy : YK11.FPState} E ss ms (W : world rsegs) wl wh hs fr pat,
st_ok (fx := fy) rsegs E ss (restrict (w_H W) ms) -> In (YP09.mkRegion (Some 26%nat) 0 8 wl wh hs) (ss_mem ss) ->
bv_unsigned (ew E 26) = shadow_addr fr -> length pat = 8%nat -> pky_hole_chk hs pat = true ->
hpat rsegs W (ms_mem ms) fr pat.
Proof.
intros fy E ss ms W wl wh hs fr pat HS Hin H26 Hl Hchk i Hi. rewrite Hl in Hi. cbn in Hi.
unfold pky_hole_chk in Hchk. rewrite forallb_forall in Hchk.
specialize (Hchk (Z.to_nat i) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in Hchk by lia.
destruct (pky_lit1 hs i) as [v|] eqn:Ev; [|discriminate Hchk]. apply Z.eqb_eq in Hchk.
rewrite <- Hchk.
exact (pky_byte E ss ms W _ (shadow_addr fr) i v HS Hin ltac:(cbn [base_val YP09.r_base]; exact H26) (pky_lit1_in hs i v Ev)).
Qed.

Lemma pky_U_reg : forall x regs L (n : nat) (q : bv 5) v c, Z.of_nat n = bv_unsigned q -> getr regs q = w64 v ->
0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 -> U (hk_env x regs L) (SOff n c) = v + c.
Proof. intros x regs L n q v c Hn Hq Hv Hc. apply U_atom_off; [rewrite (hk_env_reg x regs L n q Hn), Hq; reflexivity | lia | lia]. Qed.

Lemma pky_U_seg : forall x regs L (n j : nat) v c, n = (47 + j)%nat -> nth j L (Z_to_bv 64 0) = w64 v ->
0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 -> U (hk_env x regs L) (SOff n c) = v + c.
Proof. intros x regs L n j v c -> Hj Hv Hc. apply U_atom_off; [rewrite hk_env_seg, Hj; reflexivity | lia | lia]. Qed.

Lemma pky_U_mod : forall E (n : nat) c v, ew E n = w64 v -> U E (SOff n c) = (v + c) mod 2 ^ 64.
Proof.
intros E n c v H. rewrite U_SOff, H. unfold w64. rewrite Z_to_bv_unsigned. unfold zcanon, M64, bv_wrap.
change (bv_modulus 64) with (2 ^ 64). rewrite Z.add_mod_idemp_l by lia. reflexivity.
Qed.

(* a register goal at a stop, as the U value of its symbolic value in the entry env E0 *)
Ltac pky_rg HAE :=
lazymatch goal with |- getr (ms_regs ?ms) ?q = _ =>
lazymatch goal with HS : st_ok ?segs ?E ?ss (restrict ?H ms) |- _ =>
  let e := eval vm_compute in (sr_get (ss_regs ss) q) in
  rewrite (st_ok_restrict_reg segs H E ss ms q HS);
  change (sr_get (ss_regs ss) q) with e;
  unfold w64; rewrite denot_lit_U; f_equal;
  lazymatch type of HAE with env_agree ?k ?E0 _ =>
    tryif constr_eq E0 E then idtac else rewrite (U_agree k E0 E e HAE ltac:(vm_compute; reflexivity)) end
end end.
(* a register the runs kept: as in the entry's registers *)
Ltac pky_rkeep HAE n :=
lazymatch goal with |- getr (ms_regs ?ms) ?q = _ =>
lazymatch goal with HS : st_ok ?segs ?E ?ss (restrict ?H ms) |- _ =>
  rewrite (st_ok_restrict_reg segs H E ss ms q HS);
  change (sr_get (ss_regs ss) q) with (SOff n 0);
  rewrite hk_sv_SOff0;
  lazymatch type of HAE with env_agree ?k ?E0 _ =>
    tryif constr_eq E0 E then idtac else rewrite (proj1 HAE n ltac:(lia)) end;
  rewrite (hk_env_reg _ _ _ n q eq_refl)
end end.
(* the run's write set: the temporaries and the hole; read-only regions *)
Ltac pky_awr x HAE B20 B260 :=
lazymatch goal with |- awr_okH ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own ?U =>
let rs' := eval vm_compute in rs in change (awr_okH E rs' stk sp0 fp b0 bc ly own U);
let B2 := fresh "B2" in let B26 := fresh "B26" in
assert (B2 : bv_unsigned (ew E 2) = hx_spa x) by (first [exact B20 | rewrite (proj1 HAE 2%nat ltac:(lia)); exact B20]);
assert (B26 : bv_unsigned (ew E 26) = hx_shf x) by (first [exact B260 | rewrite (proj1 HAE 26%nat ltac:(lia)); exact B260]);
repeat first
[ apply awr_okH_nil
| apply awr_okH_cons_ro; [cbn; lia|]
| apply (pky_awr_temps x E); [assumption | exact B2 |]
| apply (pky_awr_hole x E); [exact B26 | reflexivity |] ]
end.
(* after a run: the window holds every byte it wrote *)
Ltac pky_keep x HAE B20 B260 :=
lazymatch goal with HFr : frame_of ?E ?rs (mrestrict _ ?m1) (mrestrict _ ?m2), KW : pky_KW x ?m0 _ |- _ =>
let B2 := fresh "B2" in let B26 := fresh "B26" in
assert (B2 : bv_unsigned (ew E 2) = hx_spa x) by (first [exact B20 | rewrite (proj1 HAE 2%nat ltac:(lia)); exact B20]);
assert (B26 : bv_unsigned (ew E 26) = hx_shf x) by (first [exact B260 | rewrite (proj1 HAE 26%nat ltac:(lia)); exact B260]);
let KW' := fresh "KW" in
assert (KW' : pky_KW x m0 m2);
[ apply (pky_KW_step x E rs m0 m1 m2 KW HFr);
  let a := fresh "a" in let rg := fresh "rg" in let Hrg := fresh "Hrg" in let Hb := fresh "Hb" in
  intros a (rg & Hrg & Hb);
  let rs' := eval vm_compute in rs in change (In rg rs') in Hrg;
  repeat (destruct Hrg as [<- | Hrg];
    [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; rewrite ?B2, ?B26 in Hb; unfold pky_win, hp_hole; lia | ]);
  destruct Hrg
| clear KW HFr B2 B26; rename KW' into KW ]
end;
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
Ltac pky_upd HAE :=
lazymatch goal with HS : st_ok _ ?E' _ _ |- _ =>
lazymatch type of HAE with env_agree ?k ?E0 ?E =>
let H := fresh in assert (H : env_agree k E0 E') by env_agree_chain HAE; clear HAE; rename H into HAE end end.
(* BS: the shadow span of the run's checks; pky_Bspan0 for runs without checks (they may write the hole) *)
Ltac pky_run x HAE B20 B260 BS :=
lazymatch goal with HS : st_ok _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
aj_run_tokH pa_tbl_ok HS HJ SHOK BS; [ idtac .. | pky_awr x HAE B20 B260 | pky_keep x HAE B20 B260; pky_upd HAE] end.
Ltac pky_run_to x HAE B20 B260 BS stop :=
lazymatch goal with HS : st_ok _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
aj_run_to_tokH pa_tbl_ok HS HJ SHOK BS stop; [ idtac .. | pky_awr x HAE B20 B260 | pky_keep x HAE B20 B260; pky_upd HAE] end.
Ltac pky_br BS Hc :=
lazymatch goal with HS : st_ok _ _ _ _, SH : sh_ok _ _ _ _ _ |- _ => srr_branch_tok pa_tbl_ok HS SH BS end;
lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into Hc end.
Ltac pky_hc HAE H :=
rewrite ?branch_eq_U, ?branch_ne_U, ?branch_ltu_U, ?branch_geu_U in H;
lazymatch type of HAE with env_agree ?k ?E0 ?E =>
tryif constr_eq E0 E then idtac else (repeat (rewrite (U_agree k E0 E _ HAE) in H by (vm_compute; reflexivity))) end.
Lemma pky_same_io_wvb : forall md l X, same_io md (with_vm_backing l X md).
Proof. intros md l X. unfold same_io. repeat split; reflexivity. Qed.
Ltac pky_kio := let rec go := first [ apply same_io_refl | (eapply same_io_trans; [| apply pky_same_io_wvb]); go ] in go.
Ltac pky_at_cut x :=
lazymatch goal with HS : st_ok _ _ _ (restrict _ _) |- _ =>
  rewrite (st_ok_restrict_mkst rsegs (w_H (hx_W x)) _ _ _ HS ltac:(vm_compute; reflexivity)) end.
Ltac pky_in := vm_compute; repeat (first [left; reflexivity | right]).

(* ---- registers and cells at a stop ---- *)
Definition pky_kregs : list (bv 5 * nat) :=
[((2%bv : bv 5), 2%nat); ((3%bv : bv 5), 3%nat); ((4%bv : bv 5), 4%nat); ((8%bv : bv 5), 8%nat);
 ((9%bv : bv 5), 9%nat); ((18%bv : bv 5), 18%nat); ((19%bv : bv 5), 19%nat); ((26%bv : bv 5), 26%nat);
 ((27%bv : bv 5), 27%nat)].
Definition pky_keep_ok (sr : list sv) (l : list (bv 5 * nat)) : bool :=
forallb (fun p => sv_eqb (sr_get sr (fst p)) (SOff (snd p) 0) && Nat.eqb (Z.to_nat (bv_unsigned (fst p))) (snd p)) l.

Lemma pky_reg_kept : forall {fy : YK11.FPState} x regs L k E ss ms (H : word -> bool) (q : bv 5) (n : nat),
st_ok (fx := fy) rsegs E ss (restrict H ms) -> env_agree k (hk_env (fx := fx) x regs L) E -> (n < k)%nat ->
sv_eqb (sr_get (ss_regs ss) q) (SOff n 0) = true -> Z.of_nat n = bv_unsigned q -> getr (ms_regs ms) q = getr regs q.
Proof.
intros fy x regs L k E ss ms H q n HS HAE Hn Hs Hq.
rewrite (st_ok_restrict_reg rsegs H E ss ms q HS), (sv_eqb_denot E _ _ Hs), hk_sv_SOff0, (proj1 HAE n Hn).
apply hk_env_reg. exact Hq.
Qed.

Lemma pky_keep_regs : forall {fy : YK11.FPState} x regs L k E ss ms (H : word -> bool) l,
st_ok (fx := fy) rsegs E ss (restrict H ms) -> env_agree k (hk_env (fx := fx) x regs L) E ->
pky_keep_ok (ss_regs ss) l = true -> (forall p, In p l -> (snd p < k)%nat) ->
forall q n, In (q, n) l -> getr (ms_regs ms) q = getr regs q.
Proof.
intros fy x regs L k E ss ms H l HS HAE Hok Hk q n Hin.
unfold pky_keep_ok in Hok. rewrite forallb_forall in Hok. pose proof (Hok _ Hin) as Hp.
apply andb_prop in Hp as [H1 H2]. apply Nat.eqb_eq in H2. cbn [fst snd] in H1, H2.
apply (pky_reg_kept x regs L k E ss ms H q n HS HAE (Hk _ Hin) H1).
pose proof (bv_unsigned_in_range 5 q) as Rq. rewrite <- H2. rewrite Z2Nat.id; lia.
Qed.

Lemma pky_cregs_of : forall {fy : YK11.FPState} x regs L k E ss ms (H : word -> bool),
st_ok (fx := fy) rsegs E ss (restrict H ms) -> env_agree k (hk_env (fx := fx) x regs L) E -> (27 < k)%nat ->
pky_keep_ok (ss_regs ss) pky_kregs = true -> hk_cregs x regs -> hk_cregs x (ms_regs ms).
Proof.
intros fy x regs L k E ss ms H HS HAE Hk Hok HCR.
assert (Hl : forall p, In p pky_kregs -> (snd p < k)%nat).
{ intros p Hp. unfold pky_kregs in Hp. repeat (destruct Hp as [<- | Hp]; [cbn; lia|]). destruct Hp. }
pose proof (pky_keep_regs x regs L k E ss ms H pky_kregs HS HAE Hok Hl) as K.
apply (hk_cregs_same x regs _ HCR);
[ apply (K _ 2%nat) | apply (K _ 3%nat) | apply (K _ 4%nat) | apply (K _ 8%nat) | apply (K _ 9%nat)
| apply (K _ 18%nat) | apply (K _ 19%nat) | apply (K _ 26%nat) | apply (K _ 27%nat) ];
unfold pky_kregs; cbn [In]; repeat (first [left; reflexivity | right]).
Qed.

Fixpoint pky_fc (cs : list YP09.chunk) (off : Z) : option sv :=
match cs with
| [] => None
| c :: cs' => if YP09.c_off c =? off then
                match YP09.c_val c with CVal w v => if N.eqb w 8 then Some v else None | _ => None end
              else pky_fc cs' off
end.
Lemma pky_fc_in : forall cs off v, pky_fc cs off = Some v -> In (YP09.mkChunk off (CVal 8 v)) cs.
Proof.
induction cs as [|c cs IH]; intros off v H; [discriminate H|]. cbn [pky_fc] in H.
destruct (Z.eqb_spec (YP09.c_off c) off) as [E|E].
- destruct c as [o cv]. cbn in E, H. subst o. destruct cv as [w e| | |]; try discriminate H.
  destruct (N.eqb_spec w 8) as [->|]; [|discriminate H]. injection H as ->. left. reflexivity.
- right. exact (IH off v H).
Qed.

(* an 8-byte cell of the temporaries at a stop *)
Lemma pky_tval : forall {fy : YK11.FPState} E ss ms (H : word -> bool) cs rest off v z,
st_ok (fx := fy) rsegs E ss (restrict H ms) -> ss_mem ss = YP09.mkRegion (Some 2%nat) 0 0x80 0 0x80 cs :: rest ->
pky_fc cs off = Some v -> U E v = z -> val_mem rsegs (mrestrict H (ms_mem ms)) (bv_unsigned (ew E 2) + off) 8 z.
Proof.
intros fy E ss ms H cs rest off v z HS Hm Hc Hz.
apply (pky_cell E ss ms H (YP09.mkRegion (Some 2%nat) 0 0x80 0 0x80 cs) _ off v z HS);
  [rewrite Hm; left; reflexivity | reflexivity | exact (pky_fc_in cs off v Hc) | exact Hz].
Qed.
Ltac pky_tv off TV :=
lazymatch goal with HS : st_ok _ ?E ?ss (restrict ?H ?ms) |- _ =>
 let m := eval vm_compute in (ss_mem ss) in
 lazymatch m with YP09.mkRegion _ _ _ _ _ ?cs :: ?rest =>
  let e := eval vm_compute in (pky_fc cs off) in
  lazymatch e with Some ?v =>
   pose proof (fun z => pky_tval E ss ms H cs rest off v z HS ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
     as TV
  end end end.
(* the hole's pattern at a stop, from the hole region's chunks *)
Ltac pky_hpat HAE B260 pat :=
lazymatch goal with HS : st_ok _ ?E ?ss (restrict (w_H ?W) ?ms) |- hpat _ _ _ ?fr _ =>
 let m := eval vm_compute in (ss_mem ss) in
 lazymatch m with context [YP09.mkRegion (Some 26%nat) 0 8 ?wl ?wh ?hs] =>
  apply (pky_hpat_rg' E ss ms W wl wh hs fr pat HS);
  [ pky_in
  | first [exact B260 | rewrite (proj1 HAE 26%nat ltac:(lia)); exact B260]
  | reflexivity
  | vm_compute; reflexivity ]
 end end.

Lemma pky_tv0 : forall k E0 E (m : word -> option byte) off v spa, env_agree k E0 E -> (2 < k)%nat ->
bv_unsigned (ew E0 2) = spa ->
(forall z, U E v = z -> val_mem rsegs m (bv_unsigned (ew E 2) + off) 8 z) -> sv_atoms_lt k v = true ->
forall z, U E0 v = z -> val_mem rsegs m (spa + off) 8 z.
Proof.
intros k E0 E m off v spa HAE Hk H2 TV Hv z Hz. rewrite <- H2, <- (proj1 HAE 2%nat Hk). apply TV.
rewrite (U_agree k E0 E v HAE Hv). exact Hz.
Qed.

Lemma pky_pres : forall (regsT regs2 : bvmap 5 word) (q : bv 5) z, aregs_preserved regsT regs2 -> bv_unsigned q = z ->
acallee_saved z -> getr regs2 q = getr regsT q.
Proof.
intros regsT regs2 q z HP Hq Hz. subst z. pose proof (HP (bv_unsigned q) Hz) as E.
rewrite Z_to_bv_bv_unsigned in E. exact E.
Qed.
Ltac pky_pres_tac HPr q z := rewrite (pky_pres _ _ q z HPr eq_refl ltac:(unfold acallee_saved; lia)).

(* ======================================= KEY to the strtol call ======================================= *)
Lemma pky_seg_a : forall x r cc n ck cl keys rf F fc regs mem md, call_ok x ->
KEY_at B x r cc n ck cl keys rf F fc regs mem md ->
(forall regs2 mem2 md2, KT_at x r cc n ck cl keys rf F fc regs2 mem2 md2 ->
  SRr rsegs (hx_W x) (cfg_at (fx := mkFP F fc) rsegs PK_RA_STRTOL regs2 mem2 md2) (PPOST B MT x)) ->
SRr rsegs (hx_W x) (cfg_at (fx := mkFP F fc) rsegs PC_KEY regs mem md) (PPOST B MT x).
Proof.
intros x r cc n ck cl keys rf F fc regs mem md Hc HK HT.
pose proof HK as (HC & HFX & HM & (R20 & R21 & R22 & V16 & V32 & V40) & R23 & R24 & R25 & V48).
pose proof HM as (Hnull & Hst & Hc1 & Hc8 & Hin & Hn & HKok & (Hcl & Hk0 & Hrf) & HP & HW).
pose proof (hk_core_cregs B x _ _ _ _ _ _ HC) as HCR.
pose proof HCR as (R2 & R8 & R3 & R4 & R9 & R18 & R19 & R26 & R27).
pose proof (pky_spa64 x Hc) as (P1 & P2).
set (L := pky_La x r cc keys).
assert (CS : Forall (YP09.chunk_ok rsegs (hk_env x regs L) (hx_rd x mem) (hx_spa x)) pky_cs_a).
{ unfold pky_cs_a. repeat apply Forall_cons; try apply Forall_nil.
  - apply (pky_chunk8 _ _ _ 16 48 ((hx_P x + r + 8) mod 8 + 3)); [exact (hk_env_seg x regs _ 1) | exact V16].
  - apply (pky_chunk8 _ _ _ 32 49 (hx_P x + r + 16)); [exact (hk_env_seg x regs _ 2) | exact V32].
  - apply (pky_chunk8 _ _ _ 40 47 keys); [exact (hk_env_seg x regs _ 0) | exact V40].
  - apply (pky_chunk8 _ _ _ 48 50 (shadow_addr (hx_P x + cc))); [exact (hk_env_seg x regs _ 3) | exact V48]. }
pose proof (pky_entry x PAT_KEY cl _ regs mem md L pky_cs_a PC_KEY F fc Hc HC eq_refl
  ltac:(vm_compute; reflexivity) CS) as HS.
pose proof (hk_core_journal B x _ _ _ _ _ _ HC) as (HJ & OK & HPt).
assert (SHOK : sh_ok rsegs hk_Bx [] (hk_env x regs L) (mrestrict (w_H (hx_W x)) mem)) by apply Forall_nil.
assert (KW : pky_KW x mem mem) by apply pky_KW_refl.
assert (HAE : env_agree 51 (hk_env x regs L) (hk_env x regs L)) by apply env_agree_refl.
assert (B20 : bv_unsigned (ew (hk_env x regs L) 2) = hx_spa x) by (rewrite (hk_env_reg x regs _ 2 2%bv eq_refl), R2; apply pky_w64; lia).
assert (B260 : bv_unsigned (ew (hk_env x regs L) 26) = hx_shf x) by (rewrite (hk_env_reg x regs _ 26 26%bv eq_refl), R26; apply pky_w64; lia).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
unfold cfg_at. change (w64 PC_KEY) with (Z_to_bv 64 PC_KEY).
pose proof (hk_pod B x Hc Hnull) as (HP0 & HP16 & Hlen & Hlen8 & HSZ & HP63 & _).
pose proof HKok as (Hck0 & Hck1 & _).
pose proof Hst as (Hr16 & Hr8 & Hvs & Hrvs).
pose proof (hgw_inside_bounds _ _ _ _ Hin) as (Hcc1 & Hvs8 & Hcc2).
pose proof (hgw_u32_range (hx_bs x) cc) as Ucc. pose proof (hgw_u32_range (hx_bs x) ck) as Uck.
unfold hx_len, hp_vs in *.
pky_run x HAE B20 B260 pky_Bspan0.
pky_at_cut x.
lazymatch goal with HS : st_ok _ ?E ?ss (restrict _ ?ms) |- SRr _ _ (mkCfg _ ?md1) _ =>
  assert (HC1 : hp_core B x PAT_DOT cl (ha_res_bytes 0 0 0) (ms_regs ms) (ms_mem ms) md1);
  [ apply (pky_core_stop x PAT_KEY PAT_DOT cl _ regs mem md (ms_regs ms) (ms_mem ms) md1 Hc Hcl
      ltac:(rewrite length_ha_res_bytes; lia) HC HJ
      eq_refl (proj2 hgk_PAT_DOT_ok));
    [ pky_hpat HAE B260 PAT_DOT | pky_kio | exact KW
    | exact (pky_cregs_of x regs L 51 E ss ms (w_H (hx_W x)) HS HAE ltac:(lia) ltac:(vm_compute; reflexivity) HCR) ]
  | ];
  change (SRr rsegs (hx_W x) (cfg_at (fx := mkFP F fc) rsegs A_TRAMP_STRTOL (ms_regs ms) (ms_mem ms) md1) (PPOST B MT x));
  pky_tv 16 T16; pky_tv 24 T24; pky_tv 32 T32; pky_tv 40 T40; pky_tv 48 T48;
  pose proof (pky_tv0 51 (hk_env x regs L) E _ 16 _ (hx_spa x) HAE ltac:(lia) B20 T16 eq_refl) as M16;
  pose proof (pky_tv0 51 (hk_env x regs L) E _ 24 _ (hx_spa x) HAE ltac:(lia) B20 T24 eq_refl) as M24;
  pose proof (pky_tv0 51 (hk_env x regs L) E _ 32 _ (hx_spa x) HAE ltac:(lia) B20 T32 eq_refl) as M32;
  pose proof (pky_tv0 51 (hk_env x regs L) E _ 40 _ (hx_spa x) HAE ltac:(lia) B20 T40 eq_refl) as M40;
  pose proof (pky_tv0 51 (hk_env x regs L) E _ 48 _ (hx_spa x) HAE ltac:(lia) B20 T48 eq_refl) as M48;
  clear T16 T24 T32 T40 T48;
  apply (pky_strtol_call x r cc n ck cl keys rf F fc (ms_regs ms) (ms_mem ms) md1 (PPOST B MT x) Hc HM HC1)
end.
- pky_rg HAE. unfold pky_xr. rewrite (pky_U_reg x regs L 24 24%bv (hx_P x + ck + 8) 13 eq_refl R24) by lia. lia.
- pky_rg HAE. pose proof (hk_frame_win B x Hc) as (W1 & W2 & _). pose proof (hk_stack B x Hc) as (S1 & S2 & S3 & S4 & S5 & S6 & _).
  rewrite (pky_U_reg x regs L 2 2%bv (hx_spa x) 96 eq_refl R2) by lia. reflexivity.
- pky_rg HAE; apply U_lit; lia.
- pky_rg HAE; apply U_lit; unfold PK_RA_STRTOL; lia.
- intros regs2 mem2 md2 HC2 HPr R10' Hend HK3. apply HT. unfold KT_at.
  pose proof (hk_frame_win B x Hc) as (W1 & W2 & _). pose proof (hk_stack B x Hc) as (S1 & S2 & S3 & S4 & S5 & S6 & _).
  split; [exact HC2|]. split; [exact HFX|]. split; [exact HM|].
  split.
  { unfold pa_loop.
    split; [pky_pres_tac HPr (20%bv : bv 5) 20; pky_rkeep HAE 20%nat; exact R20|].
    split; [pky_pres_tac HPr (21%bv : bv 5) 21; pky_rkeep HAE 21%nat; exact R21|].
    split; [pky_pres_tac HPr (22%bv : bv 5) 22; pky_rkeep HAE 22%nat; exact R22|].
    split; [eapply (hk_temps_kept_call B x _ mem2 16 _ errno_low Hc HK3); [left; lia|];
            apply M16; rewrite (pky_U_seg x regs L 48 1 ((hx_P x + r + 8) mod 8 + 3) 0 eq_refl eq_refl) by lia; lia|].
    split; [eapply (hk_temps_kept_call B x _ mem2 32 _ errno_low Hc HK3); [left; lia|];
            apply M32; rewrite (pky_U_seg x regs L 49 2 (hx_P x + r + 16) 0 eq_refl eq_refl) by lia; lia|].
    eapply (hk_temps_kept_call B x _ mem2 40 _ errno_low Hc HK3); [left; lia|].
    apply (pky_vm_eqmod _ _ _ _ (M40 _ eq_refl)).
    rewrite (pky_U_mod _ 47 1 keys (hk_env_seg x regs L 0)), Z.mod_mod by lia. reflexivity. }
  split; [pky_pres_tac HPr (23%bv : bv 5) 23; pky_rkeep HAE 23%nat; exact R23|].
  split; [pky_pres_tac HPr (25%bv : bv 5) 25; pky_rg HAE; unfold pky_xr;
          rewrite (pky_U_reg x regs L 24 24%bv (hx_P x + ck + 8) 13 eq_refl R24) by lia; lia|].
  split; [exact R10'|].
  split; [eapply (hk_temps_kept_call B x _ mem2 24 _ errno_low Hc HK3); [left; lia|];
          apply M24; rewrite (pky_U_reg x regs L 25 25%bv rf 0 eq_refl R25) by lia; lia|].
  split; [eapply (hk_temps_kept_call B x _ mem2 48 _ errno_low Hc HK3); [left; lia|];
          apply M48; rewrite (pky_U_seg x regs L 50 3 (shadow_addr (hx_P x + cc)) 0 eq_refl eq_refl)
            by (unfold shadow_addr, SHADOW_OFF; lia); lia|].
  apply val_mem_of_rdword. exact Hend.
Qed.

(* ======================================= the refusal: 0x84ae8 to ADV ======================================= *)
Definition PK_RF : Z := 0x84ae8.
Definition PK_VL : Z := 0x84b28.

(* 0x84ae8 with a1 = rf, a4 = P + r + 16, a5 = 8, a6 = the shadow address of the value, a7 = the refusal code *)
Definition RF_at (x : pctx) (r cc : Z) (n : nat) (ck : Z) (cl : list Headamp.cell) (keys rf bad : Z)
  (F : bvmap 5 word) (fc : bv 32) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
hp_core B x PAT_DOT cl (ha_res_bytes 0 0 0) regs mem md /\ hp_fxw F fc /\ hp_m_key x r cc n ck cl keys rf /\
Headamp.parse_cell (hp_kstr x ck) (Spa.child_at (hx_bs x) cc) = inl bad /\ 0 <= bad <= 5 /\
pa_loop x r cl (keys + 1) regs mem /\
getr regs 23 = w64 (hx_P x + cc) /\ getr regs 11 = w64 rf /\ getr regs 14 = w64 (hx_P x + r + 16) /\
getr regs 15 = w64 8 /\ getr regs 16 = w64 (shadow_addr (hx_P x + cc)) /\ getr regs 17 = w64 bad.

Lemma pky_adv_exit : forall x r cc n ck cl keys rf bad F fc regs mem md (regs' : bvmap 5 word) mem' md',
call_ok x -> RF_at x r cc n ck cl keys rf bad F fc regs mem md ->
ajournal rsegs B (hx_STK x) (hx_sp0 x) (hx_FP x) (hx_ly x) (hx_S x) (hx_W0 x) (hx_mem0 x) (hx_md0 x) (hx_own x)
  (hx_lyc x) (hx_Sc x) (hx_W x) (unpoison (hU (hx_fr x) PAT_DOT) mem') md' (hx_k x) ->
hpat rsegs (hx_W x) mem' (hx_fr x) PAT_KEY -> same_io md md' -> pky_KW x mem mem' -> hk_cregs x regs' ->
getr regs' 20 = getr regs 20 -> getr regs' 21 = getr regs 21 -> getr regs' 22 = getr regs 22 ->
getr regs' 23 = getr regs 23 -> getr regs' 14 = getr regs 14 -> getr regs' 15 = getr regs 15 ->
getr regs' 16 = getr regs 16 -> getr regs' 24 = w64 0 ->
getr regs' 25 = w64 (if rf =? Headamp.REFUSE_NONE then bad else rf) ->
val_mem rsegs (hx_rd x mem') (hx_spa x + 16) 8 ((hx_P x + r + 8) mod 8 + 3) ->
val_mem rsegs (hx_rd x mem') (hx_spa x + 32) 8 (hx_P x + r + 16) ->
val_mem rsegs (hx_rd x mem') (hx_spa x + 40) 8 (keys + 1) ->
ADV_at B x r cc n None cl (keys + 1) (if rf =? Headamp.REFUSE_NONE then bad else rf) F fc regs' mem' md'.
Proof.
intros x r cc n ck cl keys rf bad F fc regs mem md regs' mem' md' Hc HR HJ' HP' Hio HKW HCR'
  E20 E21 E22 E23 E14 E15 E16 E24 E25 V16 V32 V40.
pose proof HR as (HC & HFX & HM & Hpc & Hbad & (R20 & R21 & R22 & _ & _ & _) & R23 & R11 & R14 & R15 & R16 & R17).
pose proof HM as (Hnull & Hst & Hc1 & Hc8 & Hin & Hn & HKok & (Hcl & Hk0 & Hrf) & HP & HW).
unfold ADV_at.
split; [exact (pky_core_stop x PAT_DOT PAT_KEY cl _ regs mem md regs' mem' md' Hc Hcl
  ltac:(rewrite length_ha_res_bytes; lia) HC HJ' eq_refl (proj2 hgk_PAT_KEY_ok) HP' Hio HKW HCR')|].
split; [exact HFX|].
split; [exact (hgk_key_refuse x r cc n ck cl keys rf bad HM Hbad Hpc)|].
split; [unfold pa_loop; rewrite E20, E21, E22; repeat split; assumption|].
split; [unfold pa_a45; rewrite E14, E15; split; assumption|].
rewrite E23, E16. cbn [hp_keyv]. repeat split; assumption.
Qed.

Lemma pky_U_segm : forall E (n : nat) v, ew E n = w64 v -> U E (SOff n 0) mod 2 ^ 64 = v mod 2 ^ 64.
Proof. intros E n v H. rewrite (pky_U_mod E n 0 v H), Z.add_0_r, Z.mod_mod by lia. reflexivity. Qed.

(* an 8-byte cell of the temporaries at a stop, as a value of the entry env (hk_env x regs L) (equal mod 2^64) *)
Ltac pky_cellg HAE B20 off :=
let TV := fresh "TV" in pky_tv off TV;
let M := fresh "M" in pose proof (pky_tv0 _ _ _ _ off _ _ HAE ltac:(lia) B20 TV eq_refl) as M; clear TV;
apply (pky_vm_eqmod _ _ _ _ (M _ eq_refl)).

Definition pky_Lr (x : pctx) (r keys : Z) : list word :=
[w64 ((hx_P x + r + 8) mod 8 + 3); w64 (hx_P x + r + 16); w64 (keys + 1)].
Definition pky_cs_r : list YP09.chunk :=
[YP09.mkChunk 16 (CVal 8 (SOff 47 0)); YP09.mkChunk 32 (CVal 8 (SOff 48 0)); YP09.mkChunk 40 (CVal 8 (SOff 49 0))].

Lemma pky_rf : forall x r cc n ck cl keys rf bad F fc regs mem md, call_ok x ->
RF_at x r cc n ck cl keys rf bad F fc regs mem md ->
(forall rf', ADV_ok B MT x r cc n None cl (keys + 1) rf') ->
SRr rsegs (hx_W x) (cfg_at (fx := mkFP F fc) rsegs PK_RF regs mem md) (PPOST B MT x).
Proof.
intros x r cc n ck cl keys rf bad F fc regs mem md Hc HR HADV.
pose proof HR as (HC & HFX & HM & Hpc & Hbad & (R20 & R21 & R22 & V16 & V32 & V40) & R23 & R11 & R14 & R15 & R16 & R17).
pose proof HM as (Hnull & Hst & Hc1 & Hc8 & Hin & Hn & HKok & (Hcl & Hk0 & Hrf) & HP & HW).
pose proof (hk_core_cregs B x _ _ _ _ _ _ HC) as HCR.
pose proof HCR as (R2 & R8 & R3 & R4 & R9 & R18 & R19 & R26 & R27).
pose proof (pky_spa64 x Hc) as (P1 & P2).
set (L := pky_Lr x r keys).
assert (CS : Forall (YP09.chunk_ok rsegs (hk_env x regs L) (hx_rd x mem) (hx_spa x)) pky_cs_r).
{ unfold pky_cs_r. repeat apply Forall_cons; try apply Forall_nil.
  - apply (pky_chunk8 _ _ _ 16 47 ((hx_P x + r + 8) mod 8 + 3)); [exact (hk_env_seg x regs _ 0) | exact V16].
  - apply (pky_chunk8 _ _ _ 32 48 (hx_P x + r + 16)); [exact (hk_env_seg x regs _ 1) | exact V32].
  - apply (pky_chunk8 _ _ _ 40 49 (keys + 1)); [exact (hk_env_seg x regs _ 2) | exact V40]. }
pose proof (pky_entry x PAT_DOT cl _ regs mem md L pky_cs_r PK_RF F fc Hc HC eq_refl
  ltac:(vm_compute; reflexivity) CS) as HS.
pose proof (hk_core_journal B x _ _ _ _ _ _ HC) as (HJ & OK & HPt).
assert (SHOK : sh_ok rsegs hk_Bx [] (hk_env x regs L) (mrestrict (w_H (hx_W x)) mem)) by apply Forall_nil.
assert (KW : pky_KW x mem mem) by apply pky_KW_refl.
assert (HAE : env_agree 50 (hk_env x regs L) (hk_env x regs L)) by apply env_agree_refl.
assert (B20 : bv_unsigned (ew (hk_env x regs L) 2) = hx_spa x) by (rewrite (hk_env_reg x regs _ 2 2%bv eq_refl), R2; apply pky_w64; lia).
assert (B260 : bv_unsigned (ew (hk_env x regs L) 26) = hx_shf x) by (rewrite (hk_env_reg x regs _ 26 26%bv eq_refl), R26; apply pky_w64; lia).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
assert (U11 : U (hk_env x regs L) (SOff 11 0) = rf) by (rewrite (pky_U_reg x regs L 11 11%bv rf 0 eq_refl R11) by lia; lia).
assert (U17 : U (hk_env x regs L) (SOff 17 0) = bad) by (rewrite (pky_U_reg x regs L 17 17%bv bad 0 eq_refl R17) by lia; lia).
unfold ADV_ok, cfg_at in *. change (w64 PK_RF) with (Z_to_bv 64 PK_RF).
(* 0x84ae8 li a0,-8; sb a0,4(s10) (back to PAT_KEY); 0x84af0 beqz a1 *)
pky_run x HAE B20 B260 pky_Bspan0.
pky_br pky_Bspan0 Hb1; pky_hc HAE Hb1; rewrite U11, U_lit in Hb1 by lia.
all: pky_run_to x HAE B20 B260 pky_Bspan0 PC_ADV; pky_at_cut x.
all: lazymatch goal with HS : st_ok _ ?E ?ss (restrict _ ?ms) |- SRr _ _ (mkCfg _ ?md1) _ =>
  eapply HADV; apply (pky_adv_exit x r cc n ck cl keys rf bad F fc regs mem md (ms_regs ms) (ms_mem ms) md1 Hc HR);
  [ exact HJ | pky_hpat HAE B260 PAT_KEY | pky_kio | exact KW
  | exact (pky_cregs_of x regs L 50 E ss ms (w_H (hx_W x)) HS HAE ltac:(lia) ltac:(vm_compute; reflexivity) HCR)
  | pky_rkeep HAE 20%nat; reflexivity | pky_rkeep HAE 21%nat; reflexivity | pky_rkeep HAE 22%nat; reflexivity
  | pky_rkeep HAE 23%nat; reflexivity | pky_rkeep HAE 14%nat; reflexivity | pky_rkeep HAE 15%nat; reflexivity
  | pky_rkeep HAE 16%nat; reflexivity | pky_rg HAE; apply U_lit; lia | pky_rg HAE
  | pky_cellg HAE B20 16; rewrite (pky_U_segm _ 47 _ (hk_env_seg x regs L 0)); reflexivity
  | pky_cellg HAE B20 32; rewrite (pky_U_segm _ 48 _ (hk_env_seg x regs L 1)); reflexivity
  | pky_cellg HAE B20 40; rewrite (pky_U_segm _ 49 _ (hk_env_seg x regs L 2)); reflexivity ] end.
- apply Z.eqb_eq in Hb1. rewrite Hb1. cbn. exact U17.
- apply Z.eqb_neq in Hb1. unfold Headamp.REFUSE_NONE. rewrite (proj2 (Z.eqb_neq rf 0) Hb1). exact U11.
Qed.

(* ======================================= the cell address: 0x84b28 to VAL ======================================= *)
Definition VL_at (x : pctx) (r cc : Z) (n : nat) (ck : Z) (cl : list Headamp.cell) (keys rf ch p : Z)
  (F : bvmap 5 word) (fc : bv 32) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
hp_core B x PAT_DOT cl (ha_res_bytes 0 0 0) regs mem md /\ hp_fxw F fc /\ hp_m_key x r cc n ck cl keys rf /\
Headamp.parse_key (pky_rest x ck) = Headamp.KCell ch p /\
pa_loop x r cl (keys + 1) regs mem /\
getr regs 23 = w64 (hx_P x + cc) /\ getr regs 24 = w64 ch /\ getr regs 13 = w64 p /\
getr regs 16 = w64 (shadow_addr (hx_P x + cc)) /\
val_mem rsegs (hx_rd x mem) (hx_spa x + 8) 8 (if p =? Headamp.HA_SENS then 0x38 else 2) /\
val_mem rsegs (hx_rd x mem) (hx_spa x + 24) 8 rf /\
val_mem rsegs (hx_rd x mem) (hx_spa x + 48) 8 (shadow_addr (hx_P x + cc)).

Lemma pky_val_exit : forall x r cc n ck cl keys rf ch p F fc regs mem md (regs' : bvmap 5 word) mem' md',
call_ok x -> VL_at x r cc n ck cl keys rf ch p F fc regs mem md ->
ajournal rsegs B (hx_STK x) (hx_sp0 x) (hx_FP x) (hx_ly x) (hx_S x) (hx_W0 x) (hx_mem0 x) (hx_md0 x) (hx_own x)
  (hx_lyc x) (hx_Sc x) (hx_W x) (unpoison (hU (hx_fr x) PAT_DOT) mem') md' (hx_k x) ->
hpat rsegs (hx_W x) mem' (hx_fr x) PAT_KEY -> same_io md md' -> pky_KW x mem mem' -> hk_cregs x regs' ->
getr regs' 20 = getr regs 20 -> getr regs' 21 = getr regs 21 -> getr regs' 22 = getr regs 22 ->
getr regs' 23 = getr regs 23 -> getr regs' 24 = getr regs 24 -> getr regs' 13 = getr regs 13 ->
getr regs' 16 = getr regs 16 ->
val_mem rsegs (hx_rd x mem') (hx_spa x + 16) 8 ((hx_P x + r + 8) mod 8 + 3) ->
val_mem rsegs (hx_rd x mem') (hx_spa x + 32) 8 (hx_P x + r + 16) ->
val_mem rsegs (hx_rd x mem') (hx_spa x + 40) 8 (keys + 1) ->
val_mem rsegs (hx_rd x mem') (hx_spa x + 8) 8 (if p =? Headamp.HA_SENS then 0x38 else 2) ->
val_mem rsegs (hx_rd x mem') (hx_spa x + 24) 8 rf ->
val_mem rsegs (hx_rd x mem') (hx_spa x + 48) 8 (shadow_addr (hx_P x + cc)) ->
VAL_at B x r cc n ch p cl keys rf F fc regs' mem' md'.
Proof.
intros x r cc n ck cl keys rf ch p F fc regs mem md regs' mem' md' Hc HV HJ' HP' Hio HKW HCR'
  E20 E21 E22 E23 E24 E13 E16 V16 V32 V40 V8 V24 V48.
pose proof HV as (HC & HFX & HM & Hk & (R20 & R21 & R22 & _ & _ & _) & R23 & R24 & R13 & R16 & _).
pose proof HM as (Hnull & Hst & Hc1 & Hc8 & Hin & Hn & HKok & (Hcl & Hk0 & Hrf) & HP & HW).
unfold VAL_at.
split; [exact (pky_core_stop x PAT_DOT PAT_KEY cl _ regs mem md regs' mem' md' Hc Hcl
  ltac:(rewrite length_ha_res_bytes; lia) HC HJ' eq_refl (proj2 hgk_PAT_KEY_ok) HP' Hio HKW HCR')|].
split; [exact HFX|].
split; [exact (hgk_key_val x r cc n ck cl keys rf ch p HM Hk)|].
split; [unfold pa_loop; rewrite E20, E21, E22; repeat split; assumption|].
rewrite E23, E24, E13, E16. repeat split; assumption.
Qed.

Definition pky_Lv (x : pctx) (r cc keys rf p : Z) : list word :=
[w64 ((hx_P x + r + 8) mod 8 + 3); w64 (hx_P x + r + 16); w64 (keys + 1);
 w64 (if p =? Headamp.HA_SENS then 0x38 else 2); w64 rf; w64 (shadow_addr (hx_P x + cc))].
Definition pky_cs_v : list YP09.chunk :=
[YP09.mkChunk 16 (CVal 8 (SOff 47 0)); YP09.mkChunk 32 (CVal 8 (SOff 48 0)); YP09.mkChunk 40 (CVal 8 (SOff 49 0));
 YP09.mkChunk 8 (CVal 8 (SOff 50 0)); YP09.mkChunk 24 (CVal 8 (SOff 51 0)); YP09.mkChunk 48 (CVal 8 (SOff 52 0))].

Lemma pky_vl : forall x r cc n ck cl keys rf ch p F fc regs mem md, call_ok x ->
VL_at x r cc n ck cl keys rf ch p F fc regs mem md ->
VAL_ok B MT x r cc n ch p cl keys rf ->
SRr rsegs (hx_W x) (cfg_at (fx := mkFP F fc) rsegs PK_VL regs mem md) (PPOST B MT x).
Proof.
intros x r cc n ck cl keys rf ch p F fc regs mem md Hc HV HVAL.
pose proof HV as (HC & HFX & HM & Hk & (R20 & R21 & R22 & V16 & V32 & V40) & R23 & R24 & R13 & R16 & V8 & V24 & V48).
pose proof (hk_core_cregs B x _ _ _ _ _ _ HC) as HCR.
pose proof HCR as (R2 & R8 & R3 & R4 & R9 & R18 & R19 & R26 & R27).
pose proof (pky_spa64 x Hc) as (P1 & P2).
set (L := pky_Lv x r cc keys rf p).
assert (CS : Forall (YP09.chunk_ok rsegs (hk_env x regs L) (hx_rd x mem) (hx_spa x)) pky_cs_v).
{ unfold pky_cs_v. repeat apply Forall_cons; try apply Forall_nil.
  - apply (pky_chunk8 _ _ _ 16 47 ((hx_P x + r + 8) mod 8 + 3)); [exact (hk_env_seg x regs _ 0) | exact V16].
  - apply (pky_chunk8 _ _ _ 32 48 (hx_P x + r + 16)); [exact (hk_env_seg x regs _ 1) | exact V32].
  - apply (pky_chunk8 _ _ _ 40 49 (keys + 1)); [exact (hk_env_seg x regs _ 2) | exact V40].
  - apply (pky_chunk8 _ _ _ 8 50 (if p =? Headamp.HA_SENS then 0x38 else 2)); [exact (hk_env_seg x regs _ 3) | exact V8].
  - apply (pky_chunk8 _ _ _ 24 51 rf); [exact (hk_env_seg x regs _ 4) | exact V24].
  - apply (pky_chunk8 _ _ _ 48 52 (shadow_addr (hx_P x + cc))); [exact (hk_env_seg x regs _ 5) | exact V48]. }
pose proof (pky_entry x PAT_DOT cl _ regs mem md L pky_cs_v PK_VL F fc Hc HC eq_refl
  ltac:(vm_compute; reflexivity) CS) as HS.
pose proof (hk_core_journal B x _ _ _ _ _ _ HC) as (HJ & OK & HPt).
assert (SHOK : sh_ok rsegs hk_Bx [] (hk_env x regs L) (mrestrict (w_H (hx_W x)) mem)) by apply Forall_nil.
assert (KW : pky_KW x mem mem) by apply pky_KW_refl.
assert (HAE : env_agree 53 (hk_env x regs L) (hk_env x regs L)) by apply env_agree_refl.
assert (B20 : bv_unsigned (ew (hk_env x regs L) 2) = hx_spa x) by (rewrite (hk_env_reg x regs _ 2 2%bv eq_refl), R2; apply pky_w64; lia).
assert (B260 : bv_unsigned (ew (hk_env x regs L) 26) = hx_shf x) by (rewrite (hk_env_reg x regs _ 26 26%bv eq_refl), R26; apply pky_w64; lia).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
unfold VAL_ok, cfg_at in *. change (w64 PK_VL) with (Z_to_bv 64 PK_VL).
(* 0x84b28 li a0,-8; sb a0,4(s10) (back to PAT_KEY); VAL 0x84b30 *)
pky_run_to x HAE B20 B260 pky_Bspan0 PC_VAL. pky_at_cut x.
lazymatch goal with HS : st_ok _ ?E ?ss (restrict _ ?ms) |- SRr _ _ (mkCfg _ ?md1) _ =>
  eapply HVAL; apply (pky_val_exit x r cc n ck cl keys rf ch p F fc regs mem md (ms_regs ms) (ms_mem ms) md1 Hc HV);
  [ exact HJ | pky_hpat HAE B260 PAT_KEY | pky_kio | exact KW
  | exact (pky_cregs_of x regs L 53 E ss ms (w_H (hx_W x)) HS HAE ltac:(lia) ltac:(vm_compute; reflexivity) HCR)
  | pky_rkeep HAE 20%nat; reflexivity | pky_rkeep HAE 21%nat; reflexivity | pky_rkeep HAE 22%nat; reflexivity
  | pky_rkeep HAE 23%nat; reflexivity | pky_rkeep HAE 24%nat; reflexivity | pky_rkeep HAE 13%nat; reflexivity
  | pky_rkeep HAE 16%nat; reflexivity
  | pky_cellg HAE B20 16; rewrite (pky_U_segm _ 47 _ (hk_env_seg x regs L 0)); reflexivity
  | pky_cellg HAE B20 32; rewrite (pky_U_segm _ 48 _ (hk_env_seg x regs L 1)); reflexivity
  | pky_cellg HAE B20 40; rewrite (pky_U_segm _ 49 _ (hk_env_seg x regs L 2)); reflexivity
  | pky_cellg HAE B20 8; rewrite (pky_U_segm _ 50 _ (hk_env_seg x regs L 3)); reflexivity
  | pky_cellg HAE B20 24; rewrite (pky_U_segm _ 51 _ (hk_env_seg x regs L 4)); reflexivity
  | pky_cellg HAE B20 48; rewrite (pky_U_segm _ 52 _ (hk_env_seg x regs L 5)); reflexivity ] end.
Qed.

(* ======================================= the model's refusals ======================================= *)
Lemma pky_cell_bad : forall x ck cc, Headamp.parse_key (pky_rest x ck) = Headamp.KBad ->
Headamp.parse_cell (hp_kstr x ck) (Spa.child_at (hx_bs x) cc) = inl Headamp.REFUSE_BAD_KEY.
Proof. intros x ck cc H. unfold Headamp.parse_cell. rewrite hgw_prefix_len. unfold pky_rest in H. rewrite H. reflexivity. Qed.
Lemma pky_cell_range : forall x ck cc, Headamp.parse_key (pky_rest x ck) = Headamp.KRange ->
Headamp.parse_cell (hp_kstr x ck) (Spa.child_at (hx_bs x) cc) = inl Headamp.REFUSE_OUT_OF_RANGE.
Proof. intros x ck cc H. unfold Headamp.parse_cell. rewrite hgw_prefix_len. unfold pky_rest in H. rewrite H. reflexivity. Qed.

(* parse_key once the dot is found: the name's param, then the channel's range *)
Lemma pky_key_named : forall x ck, pky_dot x ck ->
Headamp.parse_key (pky_rest x ck) =
match Headamp.param_of_name (pky_nm x ck) with
| None => Headamp.KBad
| Some p => if (PIS.s10_val (pky_rest x ck) <? 0) || (Headamp.REAC_HEADAMP_MAX_CH <=? PIS.s10_val (pky_rest x ck))
            then Headamp.KRange else Headamp.KCell (PIS.s10_val (pky_rest x ck)) p
end.
Proof. intros x ck (H1 & H2). exact (hgk_key_name _ H1 H2). Qed.

(* the code's unsigned test `bltu s8, 48` on the signed value *)
Lemma pky_ltu48 : forall v, - 2 ^ 63 <= v < 2 ^ 63 -> ((v mod 2 ^ 64) <? 48) = ((0 <=? v) && (v <? 48)).
Proof.
intros v Hv. destruct (Z_le_dec 0 v) as [H|H].
- rewrite Z.mod_small by lia. rewrite (proj2 (Z.leb_le 0 v) H). reflexivity.
- rewrite <- (Z.mod_unique v (2 ^ 64) (-1) (v + 2 ^ 64)) by lia. rewrite (proj2 (Z.leb_gt 0 v) ltac:(lia)).
  cbn [andb]. apply Z.ltb_ge. lia.
Qed.

Lemma pky_key_val : forall x ck p, pky_dot x ck -> Headamp.param_of_name (pky_nm x ck) = Some p ->
(PIS.s10_val (pky_rest x ck) mod 2 ^ 64 <? 48) = true ->
Headamp.parse_key (pky_rest x ck) = Headamp.KCell (PIS.s10_val (pky_rest x ck)) p.
Proof.
intros x ck p Hd Hp Hb. rewrite (pky_key_named x ck Hd), Hp. rewrite pky_ltu48 in Hb by apply hgk_val_range.
apply andb_prop in Hb as [A1 A2]. apply Z.leb_le in A1. apply Z.ltb_lt in A2. unfold Headamp.REAC_HEADAMP_MAX_CH.
rewrite (proj2 (Z.ltb_ge _ 0) A1), (proj2 (Z.leb_gt 48 _) A2). reflexivity.
Qed.

Lemma pky_key_rng : forall x ck p, pky_dot x ck -> Headamp.param_of_name (pky_nm x ck) = Some p ->
(PIS.s10_val (pky_rest x ck) mod 2 ^ 64 <? 48) = false -> Headamp.parse_key (pky_rest x ck) = Headamp.KRange.
Proof.
intros x ck p Hd Hp Hb. rewrite (pky_key_named x ck Hd), Hp. rewrite pky_ltu48 in Hb by apply hgk_val_range.
unfold Headamp.REAC_HEADAMP_MAX_CH. apply andb_false_iff in Hb as [A|A].
- apply Z.leb_gt in A. rewrite (proj2 (Z.ltb_lt _ 0) A). reflexivity.
- apply Z.ltb_ge in A. rewrite (proj2 (Z.leb_le 48 _) A), orb_true_r. reflexivity.
Qed.

Lemma pky_key_none : forall x ck, pky_dot x ck -> Headamp.param_of_name (pky_nm x ck) = None ->
Headamp.parse_key (pky_rest x ck) = Headamp.KBad.
Proof. intros x ck Hd Hp. rewrite (pky_key_named x ck Hd), Hp. reflexivity. Qed.

(* a strcmp result in -1 .. 1, as the word the code tests against 0 *)
Lemma pky_res0 : forall res, -1 <= res <= 1 -> ((res + 0) mod 2 ^ 64 =? 0) = (res =? 0).
Proof.
intros res H. rewrite Z.add_0_r. assert (res = -1 \/ res = 0 \/ res = 1) as [-> | [-> | ->]] by lia; reflexivity.
Qed.

(* ======================================= after strtol: the end pointer ======================================= *)
(* the byte at the end pointer: the byte s10_end of rest, or its NUL *)
Definition pky_db (x : pctx) (ck : Z) : Z :=
bv_unsigned (nth (Z.to_nat (pky_en x ck)) (pky_rest x ck ++ [Z_to_bv 8 0]) (Z_to_bv 8 0)).
Lemma pky_db_eq : forall x ck, pky_en x ck <= Z.of_nat (length (pky_rest x ck)) ->
pky_db x ck = bv_unsigned (nth (Z.to_nat (pky_en x ck)) (pky_rest x ck) Cursor.NUL).
Proof.
intros x ck H. unfold pky_db. pose proof (hgk_end_le (pky_rest x ck)) as Hel. fold (pky_en x ck) in Hel.
destruct (Nat.lt_ge_cases (Z.to_nat (pky_en x ck)) (length (pky_rest x ck))) as [Hl|Hl].
- rewrite app_nth1 by exact Hl. reflexivity.
- rewrite app_nth2 by exact Hl. rewrite (nth_overflow (pky_rest x ck)) by exact Hl.
  replace (Z.to_nat (pky_en x ck) - length (pky_rest x ck))%nat with 0%nat by lia. reflexivity.
Qed.

Definition pky_L1 (x : pctx) (r cc ck keys rf : Z) : list word :=
[w64 rf; w64 ((hx_P x + r + 8) mod 8 + 3); w64 (hx_P x + r + 16); w64 (keys + 1); w64 (shadow_addr (hx_P x + cc));
 w64 (pky_xr x ck + pky_en x ck); w64 (pky_db x ck)].
Definition pky_cs1 : list YP09.chunk :=
[YP09.mkChunk 24 (CVal 8 (SOff 47 0)); YP09.mkChunk 16 (CVal 8 (SOff 48 0)); YP09.mkChunk 32 (CVal 8 (SOff 49 0));
 YP09.mkChunk 40 (CVal 8 (SOff 50 0)); YP09.mkChunk 48 (CVal 8 (SOff 51 0)); YP09.mkChunk 96 (CVal 8 (SOff 52 0))].
Definition pky_hole_ro (pat : list Z) : YP09.region := YP09.mkRegion (Some 26%nat) 0 8 0 0 (hk_hole_chunks pat).
Definition pky_podb : YP09.region := YP09.mkRegion (Some 52%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 53 0))].
Definition pky_ss1 : sstate := mkSS PK_RA_STRTOL sr_atoms [hk_temps pky_cs1; pky_hole_ro PAT_DOT; pky_podb] None
  (mkFacts (hk_atoms ++ [(52%nat, mkAF 1 (2 ^ 47 - 2) 0); (53%nat, mkAF 0 255 0)]) [] []).
Definition pky_sh1 : list shent := [mkSHE 52 0 1].

Lemma pky_region_ro : forall E m b lo hi wl wh cs, region_ok rsegs E m (YP09.mkRegion b lo hi wl wh cs) ->
region_ok rsegs E m (YP09.mkRegion b lo hi 0 0 cs).
Proof.
intros E m b lo hi wl wh cs H. unfold region_ok in *. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks] in *.
destruct H as (H1 & H2 & _ & H4). split; [exact H1|]. split; [exact H2|]. split; [intros o Ho; lia | exact H4].
Qed.

Lemma pky_entry1 : forall x r cc n ck cl keys rf F fc regs mem md, call_ok x ->
KT_at x r cc n ck cl keys rf F fc regs mem md ->
st_ok (fx := mkFP F fc) rsegs (hk_env x regs (pky_L1 x r cc ck keys rf)) pky_ss1
  (restrict (w_H (hx_W x)) (mkst (fx := mkFP F fc) regs (Z_to_bv 64 PK_RA_STRTOL) mem (seg_rom rsegs))) /\
sh_ok rsegs hk_Bx pky_sh1 (hk_env x regs (pky_L1 x r cc ck keys rf)) (mrestrict (w_H (hx_W x)) mem).
Proof.
intros x r cc n ck cl keys rf F fc regs mem md Hc HT.
pose proof HT as (HC & HFX & HM & (R20 & R21 & R22 & V16 & V32 & V40) & R23 & R25 & R10 & V24 & V48 & V96).
pose proof HM as (Hnull & Hst & Hc1 & Hc8 & Hin & Hn & HKok & (Hcl & Hk0 & Hrf) & HP & HW).
pose proof (hk_core_cregs B x _ _ _ _ _ _ HC) as HCR.
pose proof HCR as (R2 & R8 & R3 & R4 & R9 & R18 & R19 & R26 & R27).
pose proof (pky_spa64 x Hc) as (P1 & P2).
pose proof (hk_pod B x Hc Hnull) as (HP0 & HP16 & Hlen & Hlen8 & HSZ & HP63 & _ & HPin & HPO & HPR & HPE & _ & _ & HAM & HPoff).
pose proof (hk_pod_at_cut B pa_segs_low x PAT_DOT cl _ regs mem md errno_low Hc Hnull HC ltac:(lia)) as (HG & HRA & HHV).
destruct (pky_rest_view x ck mem HKok HP HG) as (HV & Hnz & L13 & Lr & Lk).
pose proof HKok as (Hck0 & Hck1 & _).
pose proof (hgk_end_le (pky_rest x ck)) as Hel. fold (pky_en x ck) in Hel.
pose proof (hk_frame_win B x Hc) as (W1 & W2 & W3 & W4 & W5).
pose proof (hk_stack B x Hc) as HSt.
pose proof (hk_hole_band B x (hx_shf x) Hc ltac:(unfold hp_hole; lia)) as (H1 & H2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HT0 : T_parse_STK = 12576) by reflexivity.
unfold hx_len in *.
set (L := pky_L1 x r cc ck keys rf).
assert (He : hx_P x <= pky_xr x ck + pky_en x ck /\ pky_xr x ck + pky_en x ck + 1 <= hx_P x + Z.of_nat (length (hx_bs x)))
  by (unfold pky_xr; lia).
assert (E52 : ew (hk_env x regs L) 52 = w64 (pky_xr x ck + pky_en x ck)) by exact (hk_env_seg x regs L 5).
assert (E53 : ew (hk_env x regs L) 53 = w64 (pky_db x ck)) by exact (hk_env_seg x regs L 6).
assert (Hdb : hx_view x mem (pky_xr x ck + pky_en x ck) = Some (pky_db x ck)).
{ pose proof (HV (Z.to_nat (pky_en x ck)) ltac:(lia)) as Ev. rewrite Z2Nat.id in Ev by lia. exact Ev. }
pose proof (hk_view_val1 _ _ _ _ Hdb) as (Vdb & Rdb).
assert (B2 : bv_unsigned (ew (hk_env x regs L) 2) = hx_spa x)
  by (rewrite (hk_env_reg x regs _ 2 2%bv eq_refl), R2; apply pky_w64; lia).
assert (B26 : bv_unsigned (ew (hk_env x regs L) 26) = hx_shf x)
  by (rewrite (hk_env_reg x regs _ 26 26%bv eq_refl), R26; apply pky_w64; lia).
assert (B52 : bv_unsigned (ew (hk_env x regs L) 52) = pky_xr x ck + pky_en x ck) by (rewrite E52; apply pky_w64; lia).
assert (B53 : bv_unsigned (ew (hk_env x regs L) 53) = pky_db x ck) by (rewrite E53; apply pky_w64; lia).
pose proof (HPoff (pky_xr x ck + pky_en x ck) ltac:(lia)) as Hoff. change (spZ (hx_regs x)) with (hx_sp x) in Hoff.
split.
- rewrite restrict_mkst_fx. unfold pky_ss1. apply (entry_st_ok_full rsegs); fold (hk_env x regs L).
  + apply regs_ok_Ereg.
  + vm_compute. reflexivity.
  + constructor; [|constructor; [|constructor; [|constructor]]].
    * apply (hk_temps_ok B x PAT_DOT cl _ regs mem md _ _ Hc HC). unfold pky_cs1.
      repeat apply Forall_cons; try apply Forall_nil.
      -- apply (pky_chunk8 _ _ _ 24 47 rf); [exact (hk_env_seg x regs _ 0) | exact V24].
      -- apply (pky_chunk8 _ _ _ 16 48 ((hx_P x + r + 8) mod 8 + 3)); [exact (hk_env_seg x regs _ 1) | exact V16].
      -- apply (pky_chunk8 _ _ _ 32 49 (hx_P x + r + 16)); [exact (hk_env_seg x regs _ 2) | exact V32].
      -- apply (pky_chunk8 _ _ _ 40 50 (keys + 1)); [exact (hk_env_seg x regs _ 3) | exact V40].
      -- apply (pky_chunk8 _ _ _ 48 51 (shadow_addr (hx_P x + cc))); [exact (hk_env_seg x regs _ 4) | exact V48].
      -- apply (pky_chunk8 _ _ _ 96 52 (pky_xr x ck + pky_en x ck)); [exact (hk_env_seg x regs _ 5) | exact V96].
    * unfold pky_hole_ro. apply (pky_region_ro _ _ _ _ _ 0 8).
      exact (hk_hole_ok B pa_segs_low x PAT_DOT cl _ regs mem md _ Hc HC eq_refl).
    * unfold region_ok, pky_podb. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite B52. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val rsegs _ _ _ 0 1 (SOff 53 0) (pky_db x ck));
        [rewrite hk_sv_SOff0, E53; reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_r; exact Vdb].
  + pose proof (hk_stack B x Hc) as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & S13).
    pose proof alloc_ceiling_value as [[AC1 AC2] AC3].
    assert (Hshf : hx_shf x + 8 <= kHighShadowEnd).
    { unfold hx_shf, shadow_addr. rewrite S11. unfold kHighShadowEnd, SHADOW_OFF. lia. }
    assert (D1 : hx_shf x + 8 <= hx_spa x) by (unfold kHighShadowEnd in *; lia).
    assert (D2 : pky_xr x ck + pky_en x ck + 1 <= hx_spa x \/ hx_spa x + 128 <= pky_xr x ck + pky_en x ck).
    { unfold T_parse_STK, T_PARSE_FRAME, ESTACK in *. lia. }
    assert (D3 : pky_xr x ck + pky_en x ck + 1 <= hx_shf x \/ hx_shf x + 8 <= pky_xr x ck + pky_en x ck).
    { unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, kHighShadowEnd, SHADOW_OFF in *. lia. }
    apply pairwise_disjoint_of_extents. unfold extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val hk_temps pky_hole_ro pky_podb].
    rewrite B2, B26, B52.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; try exact I; lia.
  + split; [|split; [exact I | exact I]]. cbn [f_atoms].
    apply (hk_atoms_ok B x regs _ _ Hc HCR). cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite B52, B53. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
    unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *. repeat split; try exact I; lia.
- unfold sh_ok, pky_sh1. constructor; [|constructor].
  apply (hk_shent_pod B x (w_H (hx_W x)) mem _ 52 (ck + 21 + pky_en x ck) 0 1 Hc Hnull).
  + rewrite (hk_env_reg x regs L 27 27%bv eq_refl), R27. reflexivity.
  + rewrite E52. unfold pky_xr. f_equal. lia.
  + exact HRA.
  + unfold hx_len. unfold pky_xr in He. lia.
  + lia.
  + lia.
  + unfold hx_len. unfold pky_xr in He. lia.
Qed.

(* ======================================= after a strcmp call ======================================= *)
Definition pky_names : list (list byte) := [Headamp.NAME_PHANTOM; Headamp.NAME_PAD; Headamp.NAME_SENS].
(* the return of strcmp number i (0, 1, 2) with the result res; [spa + 8] = 2 after the first *)
Definition KC_at (x : pctx) (r cc : Z) (n : nat) (ck : Z) (cl : list Headamp.cell) (keys rf : Z) (i : nat) (res : Z)
  (F : bvmap 5 word) (fc : bv 32) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
hp_core B x PAT_DOT cl (ha_res_bytes 0 0 0) regs mem md /\ hp_fxw F fc /\ hp_m_key x r cc n ck cl keys rf /\
pa_loop x r cl (keys + 1) regs mem /\
getr regs 23 = w64 (hx_P x + cc) /\ getr regs 24 = w64 (PIS.s10_val (pky_rest x ck)) /\
getr regs 25 = w64 (pky_xr x ck + pky_en x ck + 1) /\
val_mem rsegs (hx_rd x mem) (hx_spa x + 24) 8 rf /\
val_mem rsegs (hx_rd x mem) (hx_spa x + 48) 8 (shadow_addr (hx_P x + cc)) /\
((0 < i)%nat -> val_mem rsegs (hx_rd x mem) (hx_spa x + 8) 8 2) /\
pky_dot x ck /\ getr regs 10 = w64 res /\ -1 <= res <= 1 /\ (res = 0 <-> pky_nm x ck = nth i pky_names []) /\
(forall j, (j < i)%nat -> pky_nm x ck <> nth j pky_names []).

(* a temporaries cell a strcmp call keeps *)
Lemma pky_kept2 : forall x (memT mem2 : word -> option byte) o v, call_ok x ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (hx_spa x - 2 * ESTACK <= a < hx_spa x) -> hx_view x mem2 a = hx_view x memT a) ->
0 <= o -> o + 8 <= 0x80 -> val_mem rsegs (hx_rd x memT) (hx_spa x + o) 8 v ->
val_mem rsegs (hx_rd x mem2) (hx_spa x + o) 8 v.
Proof.
intros x memT mem2 o v Hc HK Ho Ho8 Hv k Hk. rewrite <- (Hv k Hk).
pose proof (hk_frame_win B x Hc) as (W1 & W2 & W3 & W4 & W5).
pose proof (hk_stack B x Hc) as (S1 & S2 & S3 & S4 & S5 & S6 & _).
assert (HE : ESTACK = 4096) by reflexivity. assert (HT : T_parse_STK = 12576) by reflexivity.
unfold hx_rd. apply (mbyte_of_aview rsegs). apply HK; [lia | lia].
Qed.

(* the register at a stop holding the entry's register m *)
Ltac pky_rsv HAE m qm :=
lazymatch goal with |- getr (ms_regs ?ms) ?q = _ =>
lazymatch goal with HS : st_ok ?segs ?E ?ss (restrict ?H ms) |- _ =>
  rewrite (st_ok_restrict_reg segs H E ss ms q HS);
  change (sr_get (ss_regs ss) q) with (SOff m 0);
  rewrite hk_sv_SOff0;
  lazymatch type of HAE with env_agree ?k ?E0 _ =>
    tryif constr_eq E0 E then idtac else rewrite (proj1 HAE m ltac:(lia)) end;
  rewrite (hk_env_reg _ _ _ m qm eq_refl)
end end.

(* the refusal stop 0x84ae8 of the run from strtol's return: RF_at at the code bad *)
Ltac pky_rf1 x regs mem md cl L Hc Hcl HC HJ KW HAE HCR B20 B260 HRF HFX HM R20 R21 R22 R23 U47 U49 U51 bad Hpc :=
  pky_run_to x HAE B20 B260 hk_Bspan PK_RF; pky_at_cut x;
  lazymatch goal with HS : st_ok _ ?E ?ss (restrict _ ?ms) |- SRr _ _ (mkCfg _ ?md1) _ =>
    apply (HRF bad (ms_regs ms) (ms_mem ms) md1); unfold RF_at;
    split; [apply (pky_core_stop x PAT_DOT PAT_DOT cl _ regs mem md (ms_regs ms) (ms_mem ms) md1 Hc Hcl
      ltac:(rewrite length_ha_res_bytes; lia) HC HJ eq_refl (proj2 hgk_PAT_DOT_ok));
      [ pky_hpat HAE B260 PAT_DOT | pky_kio | exact KW
      | exact (pky_cregs_of x regs L 54 E ss ms (w_H (hx_W x)) HS HAE ltac:(lia) ltac:(vm_compute; reflexivity) HCR) ]|]
  end;
  split; [exact HFX|]; split; [exact HM|]; split; [exact Hpc|];
  split; [unfold Headamp.REFUSE_BAD_KEY, Headamp.REFUSE_OUT_OF_RANGE; lia|];
  split;
  [ unfold pa_loop;
    split; [pky_rkeep HAE 20%nat; exact R20|]; split; [pky_rkeep HAE 21%nat; exact R21|];
    split; [pky_rkeep HAE 22%nat; exact R22|];
    split; [pky_cellg HAE B20 16; rewrite (pky_U_segm _ 48 _ (hk_env_seg x regs L 1)); reflexivity|];
    split; [pky_cellg HAE B20 32; rewrite (pky_U_segm _ 49 _ (hk_env_seg x regs L 2)); reflexivity|];
    pky_cellg HAE B20 40; rewrite (pky_U_segm _ 50 _ (hk_env_seg x regs L 3)); reflexivity
  | ];
  split; [pky_rkeep HAE 23%nat; exact R23|];
  split; [pky_rg HAE; exact U47|]; split; [pky_rg HAE; exact U49|]; split; [pky_rg HAE; apply U_lit; lia|];
  split; [pky_rg HAE; exact U51|]; pky_rg HAE; apply U_lit; lia.

(* ======================================= from strtol's return ======================================= *)
Lemma pky_seg_1 : forall x r cc n ck cl keys rf F fc regs mem md, call_ok x ->
KT_at x r cc n ck cl keys rf F fc regs mem md ->
(forall bad regs' mem' md', RF_at x r cc n ck cl keys rf bad F fc regs' mem' md' ->
  SRr rsegs (hx_W x) (cfg_at (fx := mkFP F fc) rsegs PK_RF regs' mem' md') (PPOST B MT x)) ->
(forall res regs' mem' md', KC_at x r cc n ck cl keys rf 0 res F fc regs' mem' md' ->
  SRr rsegs (hx_W x) (cfg_at (fx := mkFP F fc) rsegs PK_RA_CMP1 regs' mem' md') (PPOST B MT x)) ->
SRr rsegs (hx_W x) (cfg_at (fx := mkFP F fc) rsegs PK_RA_STRTOL regs mem md) (PPOST B MT x).
Proof.
intros x r cc n ck cl keys rf F fc regs mem md Hc HT HRF HKC.
destruct (pky_entry1 x r cc n ck cl keys rf F fc regs mem md Hc HT) as [HS SHOK].
pose proof HT as (HC & HFX & HM & (R20 & R21 & R22 & V16 & V32 & V40) & R23 & R25 & R10 & V24 & V48 & V96).
pose proof HM as (Hnull & Hst & Hc1 & Hc8 & Hin & Hn & HKok & (Hcl & Hk0 & Hrf) & HP & HW).
pose proof (hk_core_cregs B x _ _ _ _ _ _ HC) as HCR.
pose proof HCR as (R2 & R8 & R3 & R4 & R9 & R18 & R19 & R26 & R27).
pose proof (pky_spa64 x Hc) as (P1 & P2).
pose proof (hk_frame_win B x Hc) as (W1 & W2 & _). pose proof (hk_stack B x Hc) as (S1 & S2 & S3 & S4 & S5 & S6 & _).
pose proof (hk_pod B x Hc Hnull) as (HP0 & HP16 & Hlen & Hlen8 & HSZ & HP63 & _ & HPin & HPO & HPR & HPE & _ & _ & HAM & HPoff).
pose proof (hk_pod_at_cut B pa_segs_low x PAT_DOT cl _ regs mem md errno_low Hc Hnull HC ltac:(lia)) as (HG & HRA & HHV).
destruct (pky_rest_view x ck mem HKok HP HG) as (HV & Hnz & L13 & Lr & Lk).
pose proof HKok as (Hck0 & Hck1 & _).
pose proof (hgk_end_le (pky_rest x ck)) as Hel. fold (pky_en x ck) in Hel.
pose proof (hgw_inside_bounds _ _ _ _ Hin) as (Hcc1 & Hvs8 & Hcc2).
pose proof Hst as (Hr16 & Hr8 & Hvs & Hrvs).
pose proof (hgw_u32_range (hx_bs x) cc) as Ucc.
unfold hx_len, hp_vs in *.
set (L := pky_L1 x r cc ck keys rf).
pose proof (hk_core_journal B x _ _ _ _ _ _ HC) as (HJ & OK & HPt).
assert (KW : pky_KW x mem mem) by apply pky_KW_refl.
assert (HAE : env_agree 54 (hk_env x regs L) (hk_env x regs L)) by apply env_agree_refl.
assert (B20 : bv_unsigned (ew (hk_env x regs L) 2) = hx_spa x) by (rewrite (hk_env_reg x regs _ 2 2%bv eq_refl), R2; apply pky_w64; lia).
assert (B260 : bv_unsigned (ew (hk_env x regs L) 26) = hx_shf x) by (rewrite (hk_env_reg x regs _ 26 26%bv eq_refl), R26; apply pky_w64; lia).
assert (He : hx_P x <= pky_xr x ck + pky_en x ck /\ pky_xr x ck + pky_en x ck + 1 <= hx_P x + Z.of_nat (length (hx_bs x)))
  by (unfold pky_xr; lia).
assert (U25 : U (hk_env x regs L) (SOff 25 0) = pky_xr x ck)
  by (rewrite (pky_U_reg x regs L 25 25%bv (pky_xr x ck) 0 eq_refl R25) by (unfold pky_xr in *; lia); lia).
assert (U52 : U (hk_env x regs L) (SOff 52 0) = pky_xr x ck + pky_en x ck)
  by (rewrite (pky_U_seg x regs L 52 5 (pky_xr x ck + pky_en x ck) 0 eq_refl eq_refl) by lia; lia).
assert (U53 : U (hk_env x regs L) (SOff 53 0) = pky_db x ck).
{ assert (0 <= pky_db x ck < 256) by (unfold pky_db; pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat (pky_en x ck))
    (pky_rest x ck ++ [Z_to_bv 8 0]) (Z_to_bv 8 0))) as R; change (bv_modulus 8) with 256 in R; lia).
  rewrite (pky_U_seg x regs L 53 6 (pky_db x ck) 0 eq_refl eq_refl) by lia; lia. }
assert (U47 : U (hk_env x regs L) (SOff 47 0) = rf) by (rewrite (pky_U_seg x regs L 47 0 rf 0 eq_refl eq_refl) by lia; lia).
assert (U49 : U (hk_env x regs L) (SOff 49 0) = hx_P x + r + 16)
  by (rewrite (pky_U_seg x regs L 49 2 (hx_P x + r + 16) 0 eq_refl eq_refl) by lia; lia).
assert (U51 : U (hk_env x regs L) (SOff 51 0) = shadow_addr (hx_P x + cc))
  by (rewrite (pky_U_seg x regs L 51 4 (shadow_addr (hx_P x + cc)) 0 eq_refl eq_refl) by (unfold shadow_addr, SHADOW_OFF; lia); lia).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
unfold cfg_at in *. change (w64 PK_RA_STRTOL) with (Z_to_bv 64 PK_RA_STRTOL).
(* 0x84a10 mv s8,a0; ld a0,96(sp); li a7,4; 0x84a1c beq a0,s9 (no digit: dot = rest) *)
pky_run x HAE B20 B260 hk_Bspan.
pky_br hk_Bspan Hb1; pky_hc HAE Hb1; change (pky_L1 x r cc ck keys rf) with L in Hb1; rewrite U52, U25 in Hb1.
- (* taken: no digit, dot = rest: BAD_KEY *)
  apply Z.eqb_eq in Hb1. assert (Hen : pky_en x ck = 0) by lia.
  pose proof (pky_cell_bad x ck cc (hgk_key_e0 _ Hen)) as Hpc.
  pky_rf1 x regs mem md cl L Hc Hcl HC HJ KW HAE HCR B20 B260 HRF HFX HM R20 R21 R22 R23 U47 U49 U51 4 Hpc.
- (* not taken: the end pointer is past the digits *)
  apply Z.eqb_neq in Hb1. assert (Hen : pky_en x ck <> 0) by lia.
  (* 0x84a20 .. 0x84a30 the instrumented check of *dot; 0x84a34 lbu; 0x84a3c bne '.' *)
  pky_run x HAE B20 B260 hk_Bspan.
  pky_br hk_Bspan Hb2; pky_hc HAE Hb2; change (pky_L1 x r cc ck keys rf) with L in Hb2;
    rewrite U53, U_lit in Hb2 by lia.
  + (* *dot <> '.': BAD_KEY *)
    apply negb_true_iff, Z.eqb_neq in Hb2. rewrite (pky_db_eq x ck ltac:(lia)) in Hb2.
    pose proof (pky_cell_bad x ck cc (hgk_key_nodot _ Hen Hb2)) as Hpc.
    pky_rf1 x regs mem md cl L Hc Hcl HC HJ KW HAE HCR B20 B260 HRF HFX HM R20 R21 R22 R23 U47 U49 U51 4 Hpc.
  + (* *dot = '.': the name at dot + 1; 0x84a40 .. 0x84a50 strcmp(name, "phantom") *)
    apply negb_false_iff, Z.eqb_eq in Hb2. rewrite (pky_db_eq x ck ltac:(lia)) in Hb2.
    assert (Hd : pky_dot x ck) by (split; [exact Hen | exact Hb2]).
    pky_run x HAE B20 B260 hk_Bspan. pky_at_cut x.
    lazymatch goal with HS : st_ok _ ?E ?ss (restrict _ ?ms) |- SRr _ _ (mkCfg _ ?md1) _ =>
      assert (HC1 : hp_core B x PAT_DOT cl (ha_res_bytes 0 0 0) (ms_regs ms) (ms_mem ms) md1);
      [ apply (pky_core_stop x PAT_DOT PAT_DOT cl _ regs mem md (ms_regs ms) (ms_mem ms) md1 Hc Hcl
          ltac:(rewrite length_ha_res_bytes; lia) HC HJ eq_refl (proj2 hgk_PAT_DOT_ok));
        [ pky_hpat HAE B260 PAT_DOT | pky_kio | exact KW
        | exact (pky_cregs_of x regs L 54 E ss ms (w_H (hx_W x)) HS HAE ltac:(lia) ltac:(vm_compute; reflexivity) HCR) ]
      | ];
      change (SRr rsegs (hx_W x) (cfg_at (fx := mkFP F fc) rsegs A_TRAMP_STRCMP (ms_regs ms) (ms_mem ms) md1) (PPOST B MT x));
      pky_tv 16 T16; pky_tv 24 T24; pky_tv 32 T32; pky_tv 40 T40; pky_tv 48 T48;
      pose proof (pky_tv0 54 _ E _ 16 _ (hx_spa x) HAE ltac:(lia) B20 T16 eq_refl) as M16;
      pose proof (pky_tv0 54 _ E _ 24 _ (hx_spa x) HAE ltac:(lia) B20 T24 eq_refl) as M24;
      pose proof (pky_tv0 54 _ E _ 32 _ (hx_spa x) HAE ltac:(lia) B20 T32 eq_refl) as M32;
      pose proof (pky_tv0 54 _ E _ 40 _ (hx_spa x) HAE ltac:(lia) B20 T40 eq_refl) as M40;
      pose proof (pky_tv0 54 _ E _ 48 _ (hx_spa x) HAE ltac:(lia) B20 T48 eq_refl) as M48;
      clear T16 T24 T32 T40 T48;
      pose proof (hk_call_args B x Hc) as (_ & _ & _ & _ & _ & _ & Ck & Cph & Cpad & Csens & _);
      apply (pky_strcmp_call x r cc n ck cl keys rf F fc (ms_regs ms) (ms_mem ms) md1 PK_RA_CMP1 (hi_aph headamp_himg_A)
        Headamp.NAME_PHANTOM (PPOST B MT x) Hc HM Hd HC1 Cph)
    end.
    * rewrite HBerrno. vm_compute. intro Hx. discriminate Hx.
    * pky_rg HAE. rewrite (pky_U_seg x regs L 52 5 (pky_xr x ck + pky_en x ck) 1 eq_refl eq_refl) by lia. lia.
    * pky_rg HAE; apply U_lit; lia.
    * pky_rg HAE; apply U_lit; unfold PK_RA_CMP1; lia.
    * apply ret_ok_even. vm_compute. reflexivity.
    * intros regs2 mem2 md2 res HC2 HPr R10' Hr Hiff HK2. apply (HKC res regs2 mem2 md2). unfold KC_at.
      split; [exact HC2|]. split; [exact HFX|]. split; [exact HM|].
      split.
      { unfold pa_loop.
        split; [pky_pres_tac HPr (20%bv : bv 5) 20; pky_rkeep HAE 20%nat; exact R20|].
        split; [pky_pres_tac HPr (21%bv : bv 5) 21; pky_rkeep HAE 21%nat; exact R21|].
        split; [pky_pres_tac HPr (22%bv : bv 5) 22; pky_rkeep HAE 22%nat; exact R22|].
        split; [apply (pky_kept2 x _ mem2 16 _ Hc HK2); [lia | lia |];
                apply (pky_vm_eqmod _ _ _ _ (M16 _ eq_refl)); rewrite (pky_U_segm _ 48 _ (hk_env_seg x regs L 1)); reflexivity|].
        split; [apply (pky_kept2 x _ mem2 32 _ Hc HK2); [lia | lia |];
                apply (pky_vm_eqmod _ _ _ _ (M32 _ eq_refl)); rewrite (pky_U_segm _ 49 _ (hk_env_seg x regs L 2)); reflexivity|].
        apply (pky_kept2 x _ mem2 40 _ Hc HK2); [lia | lia |].
        apply (pky_vm_eqmod _ _ _ _ (M40 _ eq_refl)); rewrite (pky_U_segm _ 50 _ (hk_env_seg x regs L 3)); reflexivity. }
      split; [pky_pres_tac HPr (23%bv : bv 5) 23; pky_rkeep HAE 23%nat; exact R23|].
      split; [pky_pres_tac HPr (24%bv : bv 5) 24; pky_rsv HAE 10%nat (10%bv : bv 5); exact R10|].
      split; [pky_pres_tac HPr (25%bv : bv 5) 25; pky_rg HAE;
              rewrite (pky_U_seg x regs L 52 5 (pky_xr x ck + pky_en x ck) 1 eq_refl eq_refl) by lia; lia|].
      split; [apply (pky_kept2 x _ mem2 24 _ Hc HK2); [lia | lia |];
              apply (pky_vm_eqmod _ _ _ _ (M24 _ eq_refl)); rewrite (pky_U_segm _ 47 _ (hk_env_seg x regs L 0)); reflexivity|].
      split; [apply (pky_kept2 x _ mem2 48 _ Hc HK2); [lia | lia |];
              apply (pky_vm_eqmod _ _ _ _ (M48 _ eq_refl)); rewrite (pky_U_segm _ 51 _ (hk_env_seg x regs L 4)); reflexivity|].
      split; [intros Hx; lia|]. split; [exact Hd|]. split; [exact R10'|]. split; [exact Hr|].
      split; [exact Hiff | intros j Hj; lia].
Qed.

(* ======================================= the strcmp returns ======================================= *)
Definition pky_Lc (x : pctx) (r cc keys rf : Z) : list word :=
[w64 ((hx_P x + r + 8) mod 8 + 3); w64 (hx_P x + r + 16); w64 (keys + 1); w64 rf; w64 (shadow_addr (hx_P x + cc));
 w64 2].
Definition pky_cs_c0 : list YP09.chunk :=
[YP09.mkChunk 16 (CVal 8 (SOff 47 0)); YP09.mkChunk 32 (CVal 8 (SOff 48 0)); YP09.mkChunk 40 (CVal 8 (SOff 49 0));
 YP09.mkChunk 24 (CVal 8 (SOff 50 0)); YP09.mkChunk 48 (CVal 8 (SOff 51 0))].
Definition pky_cs_c1 : list YP09.chunk := pky_cs_c0 ++ [YP09.mkChunk 8 (CVal 8 (SOff 52 0))].

Lemma pky_kc_cs : forall x r cc n ck cl keys rf i res F fc regs mem md,
KC_at x r cc n ck cl keys rf i res F fc regs mem md ->
Forall (YP09.chunk_ok rsegs (hk_env x regs (pky_Lc x r cc keys rf)) (hx_rd x mem) (hx_spa x)) pky_cs_c0 /\
((0 < i)%nat -> Forall (YP09.chunk_ok rsegs (hk_env x regs (pky_Lc x r cc keys rf)) (hx_rd x mem) (hx_spa x)) pky_cs_c1).
Proof.
intros x r cc n ck cl keys rf i res F fc regs mem md HK.
pose proof HK as (HC & HFX & HM & (R20 & R21 & R22 & V16 & V32 & V40) & R23 & R24 & R25 & V24 & V48 & V8 & _).
assert (C0 : Forall (YP09.chunk_ok rsegs (hk_env x regs (pky_Lc x r cc keys rf)) (hx_rd x mem) (hx_spa x)) pky_cs_c0).
{ unfold pky_cs_c0. repeat apply Forall_cons; try apply Forall_nil.
  - apply (pky_chunk8 _ _ _ 16 47 ((hx_P x + r + 8) mod 8 + 3)); [exact (hk_env_seg x regs _ 0) | exact V16].
  - apply (pky_chunk8 _ _ _ 32 48 (hx_P x + r + 16)); [exact (hk_env_seg x regs _ 1) | exact V32].
  - apply (pky_chunk8 _ _ _ 40 49 (keys + 1)); [exact (hk_env_seg x regs _ 2) | exact V40].
  - apply (pky_chunk8 _ _ _ 24 50 rf); [exact (hk_env_seg x regs _ 3) | exact V24].
  - apply (pky_chunk8 _ _ _ 48 51 (shadow_addr (hx_P x + cc))); [exact (hk_env_seg x regs _ 4) | exact V48]. }
split; [exact C0|]. intros Hi. unfold pky_cs_c1. apply Forall_app. split; [exact C0|].
apply Forall_cons; [|apply Forall_nil]. apply (pky_chunk8 _ _ _ 8 52 2); [exact (hk_env_seg x regs _ 5) | exact (V8 Hi)].
Qed.

(* the facts of a KC entry *)
Ltac pky_kc_intro x r cc n ck cl keys rf i res F fc regs mem md Hc HK :=
  pose proof HK as (HC & HFX & HM & (R20 & R21 & R22 & V16 & V32 & V40) & R23 & R24 & R25 & V24 & V48 & V8 & Hd & R10 &
    Hr & Hiff & Hprev);
  pose proof HM as (Hnull & Hst & Hc1 & Hc8 & Hin & Hn & HKok & (Hcl & Hk0 & Hrf) & HP & HW);
  pose proof (hk_core_cregs B x _ _ _ _ _ _ HC) as HCR;
  pose proof HCR as (R2 & R8 & R3 & R4 & R9 & R18 & R19 & R26 & R27);
  pose proof (pky_spa64 x Hc) as (P1 & P2);
  pose proof (hk_frame_win B x Hc) as (W1 & W2 & W3 & W4 & W5);
  pose proof (hk_stack B x Hc) as (S1 & S2 & S3 & S4 & S5 & S6 & _);
  pose proof (hk_pod B x Hc Hnull) as (HP0 & HP16 & Hlen & Hlen8 & HSZ & HP63 & _);
  pose proof HKok as (Hck0 & Hck1 & _);
  pose proof (hgw_inside_bounds _ _ _ _ Hin) as (Hcc1 & Hvs8 & Hcc2);
  pose proof Hst as (Hr16 & Hr8 & Hvs & Hrvs);
  pose proof (hgw_u32_range (hx_bs x) cc) as Ucc;
  pose proof (hgk_end_le (pky_rest x ck)) as Hel; fold (pky_en x ck) in Hel;
  pose proof (hk_pod_at_cut B pa_segs_low x PAT_DOT cl _ regs mem md errno_low Hc Hnull HC ltac:(lia)) as (HG & HRA & HHV);
  destruct (pky_rest_view x ck mem HKok HP HG) as (HV & Hnz & L13 & Lr & Lk);
  destruct (pky_name_view x ck mem HKok HP HG Hd) as (HN & Lnm & Hen0);
  unfold hx_len, hp_vs in *.

(* the refusal stop 0x84ae8 of a run from a strcmp return *)
Ltac pky_rfc x regs mem md cl L Hc Hcl HC HJ KW HAE HCR B20 B260 HRF HFX HM R20 R21 R22 R23 U50 U48 U51 bad Hpc :=
  pky_at_cut x;
  lazymatch goal with HS : st_ok _ ?E ?ss (restrict _ ?ms) |- SRr _ _ (mkCfg _ ?md1) _ =>
    apply (HRF bad (ms_regs ms) (ms_mem ms) md1); unfold RF_at;
    split; [apply (pky_core_stop x PAT_DOT PAT_DOT cl _ regs mem md (ms_regs ms) (ms_mem ms) md1 Hc Hcl
      ltac:(rewrite length_ha_res_bytes; lia) HC HJ eq_refl (proj2 hgk_PAT_DOT_ok));
      [ pky_hpat HAE B260 PAT_DOT | pky_kio | exact KW
      | exact (pky_cregs_of x regs L 53 E ss ms (w_H (hx_W x)) HS HAE ltac:(lia) ltac:(vm_compute; reflexivity) HCR) ]|]
  end;
  split; [exact HFX|]; split; [exact HM|]; split; [exact Hpc|];
  split; [unfold Headamp.REFUSE_BAD_KEY, Headamp.REFUSE_OUT_OF_RANGE; lia|];
  split;
  [ unfold pa_loop;
    split; [pky_rkeep HAE 20%nat; exact R20|]; split; [pky_rkeep HAE 21%nat; exact R21|];
    split; [pky_rkeep HAE 22%nat; exact R22|];
    split; [pky_cellg HAE B20 16; rewrite (pky_U_segm _ 47 _ (hk_env_seg x regs L 0)); reflexivity|];
    split; [pky_cellg HAE B20 32; rewrite (pky_U_segm _ 48 _ (hk_env_seg x regs L 1)); reflexivity|];
    pky_cellg HAE B20 40; rewrite (pky_U_segm _ 49 _ (hk_env_seg x regs L 2)); reflexivity
  | ];
  split; [pky_rkeep HAE 23%nat; exact R23|];
  split; [pky_rg HAE; exact U50|]; split; [pky_rg HAE; exact U48|]; split; [pky_rg HAE; apply U_lit; lia|];
  split; [pky_rg HAE; exact U51|]; pky_rg HAE; apply U_lit; lia.

(* the value stop 0x84b28 of a run from a strcmp return *)
Ltac pky_vlc x regs mem md cl L Hc Hcl HC HJ KW HAE HCR B20 B260 HVL HFX HM R20 R21 R22 R23 R24 U51 ch p Hk :=
  pky_at_cut x;
  lazymatch goal with HS : st_ok _ ?E ?ss (restrict _ ?ms) |- SRr _ _ (mkCfg _ ?md1) _ =>
    apply (HVL ch p (ms_regs ms) (ms_mem ms) md1); unfold VL_at;
    split; [apply (pky_core_stop x PAT_DOT PAT_DOT cl _ regs mem md (ms_regs ms) (ms_mem ms) md1 Hc Hcl
      ltac:(rewrite length_ha_res_bytes; lia) HC HJ eq_refl (proj2 hgk_PAT_DOT_ok));
      [ pky_hpat HAE B260 PAT_DOT | pky_kio | exact KW
      | exact (pky_cregs_of x regs L 53 E ss ms (w_H (hx_W x)) HS HAE ltac:(lia) ltac:(vm_compute; reflexivity) HCR) ]|]
  end;
  split; [exact HFX|]; split; [exact HM|]; split; [exact Hk|];
  split;
  [ unfold pa_loop;
    split; [pky_rkeep HAE 20%nat; exact R20|]; split; [pky_rkeep HAE 21%nat; exact R21|];
    split; [pky_rkeep HAE 22%nat; exact R22|];
    split; [pky_cellg HAE B20 16; rewrite (pky_U_segm _ 47 _ (hk_env_seg x regs L 0)); reflexivity|];
    split; [pky_cellg HAE B20 32; rewrite (pky_U_segm _ 48 _ (hk_env_seg x regs L 1)); reflexivity|];
    pky_cellg HAE B20 40; rewrite (pky_U_segm _ 49 _ (hk_env_seg x regs L 2)); reflexivity
  | ];
  split; [pky_rkeep HAE 23%nat; exact R23|]; split; [pky_rkeep HAE 24%nat; exact R24|];
  split; [pky_rg HAE; apply U_lit; unfold Headamp.HA_PHANTOM, Headamp.HA_PAD, Headamp.HA_SENS; lia|];
  split; [pky_rg HAE; exact U51|];
  split; [pky_cellg HAE B20 8;
          first [ rewrite U_lit by lia; reflexivity | rewrite (pky_U_segm _ 52 _ (hk_env_seg x regs L 5)); reflexivity ]|];
  split; [pky_cellg HAE B20 24; rewrite (pky_U_segm _ 50 _ (hk_env_seg x regs L 3)); reflexivity|];
  pky_cellg HAE B20 48; rewrite (pky_U_segm _ 51 _ (hk_env_seg x regs L 4)); reflexivity.

(* a strcmp stop of a run from a strcmp return, the call and the next return's facts *)
Ltac pky_cmpc x r cc n ck cl keys rf F fc regs mem md L Hc Hcl HC HJ KW HAE HCR B20 B260 HKC HFX HM Hd
  R20 R21 R22 R23 R24 R25 U25 ra y nmL Cn i' :=
  pky_at_cut x;
  lazymatch goal with HS : st_ok _ ?E ?ss (restrict _ ?ms) |- SRr _ _ (mkCfg _ ?md1) _ =>
    let HC1 := fresh "HC1" in
    assert (HC1 : hp_core B x PAT_DOT cl (ha_res_bytes 0 0 0) (ms_regs ms) (ms_mem ms) md1);
    [ apply (pky_core_stop x PAT_DOT PAT_DOT cl _ regs mem md (ms_regs ms) (ms_mem ms) md1 Hc Hcl
        ltac:(rewrite length_ha_res_bytes; lia) HC HJ eq_refl (proj2 hgk_PAT_DOT_ok));
      [ pky_hpat HAE B260 PAT_DOT | pky_kio | exact KW
      | exact (pky_cregs_of x regs L 53 E ss ms (w_H (hx_W x)) HS HAE ltac:(lia) ltac:(vm_compute; reflexivity) HCR) ]
    | ];
    change (SRr rsegs (hx_W x) (cfg_at (fx := mkFP F fc) rsegs A_TRAMP_STRCMP (ms_regs ms) (ms_mem ms) md1) (PPOST B MT x));
    let T8 := fresh "T" in let T16 := fresh "T" in let T24 := fresh "T" in let T32 := fresh "T" in
    let T40 := fresh "T" in let T48 := fresh "T" in
    pky_tv 8 T8; pky_tv 16 T16; pky_tv 24 T24; pky_tv 32 T32; pky_tv 40 T40; pky_tv 48 T48;
    let M8 := fresh "M" in let M16 := fresh "M" in let M24 := fresh "M" in let M32 := fresh "M" in
    let M40 := fresh "M" in let M48 := fresh "M" in
    pose proof (pky_tv0 53 _ E _ 8 _ (hx_spa x) HAE ltac:(lia) B20 T8 eq_refl) as M8;
    pose proof (pky_tv0 53 _ E _ 16 _ (hx_spa x) HAE ltac:(lia) B20 T16 eq_refl) as M16;
    pose proof (pky_tv0 53 _ E _ 24 _ (hx_spa x) HAE ltac:(lia) B20 T24 eq_refl) as M24;
    pose proof (pky_tv0 53 _ E _ 32 _ (hx_spa x) HAE ltac:(lia) B20 T32 eq_refl) as M32;
    pose proof (pky_tv0 53 _ E _ 40 _ (hx_spa x) HAE ltac:(lia) B20 T40 eq_refl) as M40;
    pose proof (pky_tv0 53 _ E _ 48 _ (hx_spa x) HAE ltac:(lia) B20 T48 eq_refl) as M48;
    clear T8 T16 T24 T32 T40 T48;
    apply (pky_strcmp_call x r cc n ck cl keys rf F fc (ms_regs ms) (ms_mem ms) md1 ra y nmL (PPOST B MT x)
      Hc HM Hd HC1 Cn);
    [ rewrite HBerrno; vm_compute; congruence
    | pky_rg HAE; exact U25
    | pky_rg HAE; apply U_lit; lia
    | pky_rg HAE; apply U_lit; lia
    | apply ret_ok_even; vm_compute; reflexivity
    | let regs2 := fresh "regs" in let mem2 := fresh "mem" in let md2 := fresh "md" in let res2 := fresh "res" in
      let HC2 := fresh "HC" in let HPr := fresh "HPr" in let R10' := fresh "R10" in let Hr' := fresh "Hr" in
      let Hiff' := fresh "Hiff" in let HK2 := fresh "HK" in
      intros regs2 mem2 md2 res2 HC2 HPr R10' Hr' Hiff' HK2; apply (HKC res2 regs2 mem2 md2); unfold KC_at;
      split; [exact HC2|]; split; [exact HFX|]; split; [exact HM|];
      split;
      [ unfold pa_loop;
        split; [pky_pres_tac HPr (20%bv : bv 5) 20; pky_rkeep HAE 20%nat; exact R20|];
        split; [pky_pres_tac HPr (21%bv : bv 5) 21; pky_rkeep HAE 21%nat; exact R21|];
        split; [pky_pres_tac HPr (22%bv : bv 5) 22; pky_rkeep HAE 22%nat; exact R22|];
        split; [apply (pky_kept2 x _ mem2 16 _ Hc HK2); [lia | lia |];
                apply (pky_vm_eqmod _ _ _ _ (M16 _ eq_refl)); rewrite (pky_U_segm _ 47 _ (hk_env_seg x regs L 0)); reflexivity|];
        split; [apply (pky_kept2 x _ mem2 32 _ Hc HK2); [lia | lia |];
                apply (pky_vm_eqmod _ _ _ _ (M32 _ eq_refl)); rewrite (pky_U_segm _ 48 _ (hk_env_seg x regs L 1)); reflexivity|];
        apply (pky_kept2 x _ mem2 40 _ Hc HK2); [lia | lia |];
        apply (pky_vm_eqmod _ _ _ _ (M40 _ eq_refl)); rewrite (pky_U_segm _ 49 _ (hk_env_seg x regs L 2)); reflexivity
      | ];
      split; [pky_pres_tac HPr (23%bv : bv 5) 23; pky_rkeep HAE 23%nat; exact R23|];
      split; [pky_pres_tac HPr (24%bv : bv 5) 24; pky_rkeep HAE 24%nat; exact R24|];
      split; [pky_pres_tac HPr (25%bv : bv 5) 25; pky_rkeep HAE 25%nat; exact R25|];
      split; [apply (pky_kept2 x _ mem2 24 _ Hc HK2); [lia | lia |];
              apply (pky_vm_eqmod _ _ _ _ (M24 _ eq_refl)); rewrite (pky_U_segm _ 50 _ (hk_env_seg x regs L 3)); reflexivity|];
      split; [apply (pky_kept2 x _ mem2 48 _ Hc HK2); [lia | lia |];
              apply (pky_vm_eqmod _ _ _ _ (M48 _ eq_refl)); rewrite (pky_U_segm _ 51 _ (hk_env_seg x regs L 4)); reflexivity|];
      split; [intros _; apply (pky_kept2 x _ mem2 8 _ Hc HK2); [lia | lia |];
              apply (pky_vm_eqmod _ _ _ _ (M8 _ eq_refl));
              first [ rewrite U_lit by lia; reflexivity | rewrite (pky_U_segm _ 52 _ (hk_env_seg x regs L 5)); reflexivity ]|];
      split; [exact Hd|]; split; [exact R10'|]; split; [exact Hr'|];
      split; [exact Hiff'|] ]
  end.

(* the U values of a KC entry env *)
Ltac pky_kc_U x r cc ck rf regs L R10 R24 R25 :=
  assert (U10 : U (hk_env x regs L) (SOff 10 0) = (_ + 0) mod 2 ^ 64)
    by (apply pky_U_mod; rewrite (hk_env_reg x regs L 10 10%bv eq_refl); exact R10);
  assert (U24 : U (hk_env x regs L) (SOff 24 0) = (_ + 0) mod 2 ^ 64)
    by (apply pky_U_mod; rewrite (hk_env_reg x regs L 24 24%bv eq_refl); exact R24);
  assert (U25 : U (hk_env x regs L) (SOff 25 0) = pky_xr x ck + pky_en x ck + 1)
    by (rewrite (pky_U_reg x regs L 25 25%bv _ 0 eq_refl R25) by (unfold pky_xr; lia); lia);
  assert (U48 : U (hk_env x regs L) (SOff 48 0) = hx_P x + r + 16)
    by (rewrite (pky_U_seg x regs L 48 1 (hx_P x + r + 16) 0 eq_refl eq_refl) by lia; lia);
  assert (U50 : U (hk_env x regs L) (SOff 50 0) = rf)
    by (rewrite (pky_U_seg x regs L 50 3 rf 0 eq_refl eq_refl) by lia; lia);
  assert (U51 : U (hk_env x regs L) (SOff 51 0) = shadow_addr (hx_P x + cc))
    by (rewrite (pky_U_seg x regs L 51 4 (shadow_addr (hx_P x + cc)) 0 eq_refl eq_refl)
          by (unfold shadow_addr, SHADOW_OFF; lia); lia).

Lemma pky_seg_c0 : forall x r cc n ck cl keys rf res F fc regs mem md, call_ok x ->
KC_at x r cc n ck cl keys rf 0 res F fc regs mem md ->
(forall bad regs' mem' md', RF_at x r cc n ck cl keys rf bad F fc regs' mem' md' ->
  SRr rsegs (hx_W x) (cfg_at (fx := mkFP F fc) rsegs PK_RF regs' mem' md') (PPOST B MT x)) ->
(forall ch p regs' mem' md', VL_at x r cc n ck cl keys rf ch p F fc regs' mem' md' ->
  SRr rsegs (hx_W x) (cfg_at (fx := mkFP F fc) rsegs PK_VL regs' mem' md') (PPOST B MT x)) ->
(forall res' regs' mem' md', KC_at x r cc n ck cl keys rf 1 res' F fc regs' mem' md' ->
  SRr rsegs (hx_W x) (cfg_at (fx := mkFP F fc) rsegs PK_RA_CMP2 regs' mem' md') (PPOST B MT x)) ->
SRr rsegs (hx_W x) (cfg_at (fx := mkFP F fc) rsegs PK_RA_CMP1 regs mem md) (PPOST B MT x).
Proof.
intros x r cc n ck cl keys rf res F fc regs mem md Hc HK HRF HVL HKC.
pky_kc_intro x r cc n ck cl keys rf 0%nat res F fc regs mem md Hc HK.
set (L := pky_Lc x r cc keys rf).
destruct (pky_kc_cs x r cc n ck cl keys rf 0 res F fc regs mem md HK) as [CS0 _].
pose proof (pky_entry x PAT_DOT cl _ regs mem md L pky_cs_c0 PK_RA_CMP1 F fc Hc HC eq_refl
  ltac:(vm_compute; reflexivity) CS0) as HS.
pose proof (hk_core_journal B x _ _ _ _ _ _ HC) as (HJ & OK & HPt).
assert (SHOK : sh_ok rsegs hk_Bx [] (hk_env x regs L) (mrestrict (w_H (hx_W x)) mem)) by apply Forall_nil.
assert (KW : pky_KW x mem mem) by apply pky_KW_refl.
assert (HAE : env_agree 53 (hk_env x regs L) (hk_env x regs L)) by apply env_agree_refl.
assert (B20 : bv_unsigned (ew (hk_env x regs L) 2) = hx_spa x) by (rewrite (hk_env_reg x regs _ 2 2%bv eq_refl), R2; apply pky_w64; lia).
assert (B260 : bv_unsigned (ew (hk_env x regs L) 26) = hx_shf x) by (rewrite (hk_env_reg x regs _ 26 26%bv eq_refl), R26; apply pky_w64; lia).
pky_kc_U x r cc ck rf regs L R10 R24 R25.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof (hk_call_args B x Hc) as (_ & _ & _ & _ & _ & _ & Ck & Cph & Cpad & Csens & _).
unfold cfg_at in *. change (w64 PK_RA_CMP1) with (Z_to_bv 64 PK_RA_CMP1).
(* 0x84a54 li a1,2; sd a1,8(sp); 0x84a5c beqz a0 *)
pky_run x HAE B20 B260 pky_Bspan0.
pky_br pky_Bspan0 Hb1; pky_hc HAE Hb1; rewrite U10, U_lit, pky_res0 in Hb1 by lia.
- (* res = 0: the name is "phantom" *)
  apply Z.eqb_eq in Hb1. apply Hiff in Hb1. cbn [nth pky_names] in Hb1.
  assert (Hp : Headamp.param_of_name (pky_nm x ck) = Some Headamp.HA_PHANTOM) by (apply hgk_param_phantom; exact Hb1).
  (* 0x84ac0 li a3,0; 0x84acc ld a6,48(sp); li a0,48; 0x84ad4 bltu s8,a0 *)
  pky_run x HAE B20 B260 pky_Bspan0.
  pky_br pky_Bspan0 Hb2; pky_hc HAE Hb2; rewrite U24, U_lit, Z.add_0_r in Hb2 by lia.
  + pose proof (pky_key_val x ck _ Hd Hp Hb2) as Hk.
    pky_run_to x HAE B20 B260 pky_Bspan0 PK_VL.
    pky_vlc x regs mem md cl L Hc Hcl HC HJ KW HAE HCR B20 B260 HVL HFX HM R20 R21 R22 R23 R24 U51
      (PIS.s10_val (pky_rest x ck)) Headamp.HA_PHANTOM Hk.
  + pose proof (pky_cell_range x ck cc (pky_key_rng x ck _ Hd Hp Hb2)) as Hpc.
    pky_run_to x HAE B20 B260 pky_Bspan0 PK_RF.
    pky_rfc x regs mem md cl L Hc Hcl HC HJ KW HAE HCR B20 B260 HRF HFX HM R20 R21 R22 R23 U50 U48 U51 5 Hpc.
- (* res <> 0: 0x84a60 .. 0x84a6c strcmp(name, "pad") *)
  apply Z.eqb_neq in Hb1. assert (Hn0 : pky_nm x ck <> Headamp.NAME_PHANTOM) by (intros E; apply Hb1; apply Hiff; exact E).
  pky_run x HAE B20 B260 pky_Bspan0.
  pky_cmpc x r cc n ck cl keys rf F fc regs mem md L Hc Hcl HC HJ KW HAE HCR B20 B260 HKC HFX HM Hd
    R20 R21 R22 R23 R24 R25 U25 PK_RA_CMP2 (hi_apad headamp_himg_A) Headamp.NAME_PAD Cpad 1%nat.
  intros j Hj. assert (j = 0%nat) as -> by lia. exact Hn0.
Qed.

Lemma pky_seg_c1 : forall x r cc n ck cl keys rf res F fc regs mem md, call_ok x ->
KC_at x r cc n ck cl keys rf 1 res F fc regs mem md ->
(forall bad regs' mem' md', RF_at x r cc n ck cl keys rf bad F fc regs' mem' md' ->
  SRr rsegs (hx_W x) (cfg_at (fx := mkFP F fc) rsegs PK_RF regs' mem' md') (PPOST B MT x)) ->
(forall ch p regs' mem' md', VL_at x r cc n ck cl keys rf ch p F fc regs' mem' md' ->
  SRr rsegs (hx_W x) (cfg_at (fx := mkFP F fc) rsegs PK_VL regs' mem' md') (PPOST B MT x)) ->
(forall res' regs' mem' md', KC_at x r cc n ck cl keys rf 2 res' F fc regs' mem' md' ->
  SRr rsegs (hx_W x) (cfg_at (fx := mkFP F fc) rsegs PK_RA_CMP3 regs' mem' md') (PPOST B MT x)) ->
SRr rsegs (hx_W x) (cfg_at (fx := mkFP F fc) rsegs PK_RA_CMP2 regs mem md) (PPOST B MT x).
Proof.
intros x r cc n ck cl keys rf res F fc regs mem md Hc HK HRF HVL HKC.
pky_kc_intro x r cc n ck cl keys rf 1%nat res F fc regs mem md Hc HK.
set (L := pky_Lc x r cc keys rf).
destruct (pky_kc_cs x r cc n ck cl keys rf 1 res F fc regs mem md HK) as [_ CS1].
pose proof (pky_entry x PAT_DOT cl _ regs mem md L pky_cs_c1 PK_RA_CMP2 F fc Hc HC eq_refl
  ltac:(vm_compute; reflexivity) (CS1 ltac:(lia))) as HS.
pose proof (hk_core_journal B x _ _ _ _ _ _ HC) as (HJ & OK & HPt).
assert (SHOK : sh_ok rsegs hk_Bx [] (hk_env x regs L) (mrestrict (w_H (hx_W x)) mem)) by apply Forall_nil.
assert (KW : pky_KW x mem mem) by apply pky_KW_refl.
assert (HAE : env_agree 53 (hk_env x regs L) (hk_env x regs L)) by apply env_agree_refl.
assert (B20 : bv_unsigned (ew (hk_env x regs L) 2) = hx_spa x) by (rewrite (hk_env_reg x regs _ 2 2%bv eq_refl), R2; apply pky_w64; lia).
assert (B260 : bv_unsigned (ew (hk_env x regs L) 26) = hx_shf x) by (rewrite (hk_env_reg x regs _ 26 26%bv eq_refl), R26; apply pky_w64; lia).
pky_kc_U x r cc ck rf regs L R10 R24 R25.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof (hk_call_args B x Hc) as (_ & _ & _ & _ & _ & _ & Ck & Cph & Cpad & Csens & _).
assert (Hn0 : pky_nm x ck <> Headamp.NAME_PHANTOM) by exact (Hprev 0%nat ltac:(lia)).
unfold cfg_at in *. change (w64 PK_RA_CMP2) with (Z_to_bv 64 PK_RA_CMP2).
(* 0x84a70 beqz a0 *)
pky_run x HAE B20 B260 pky_Bspan0.
pky_br pky_Bspan0 Hb1; pky_hc HAE Hb1; rewrite U10, U_lit, pky_res0 in Hb1 by lia.
- (* res = 0: the name is "pad" *)
  apply Z.eqb_eq in Hb1. apply Hiff in Hb1. cbn [nth pky_names] in Hb1.
  assert (Hp : Headamp.param_of_name (pky_nm x ck) = Some Headamp.HA_PAD) by (apply hgk_param_pad; assumption).
  (* 0x84ac8 li a3,1; 0x84acc ld a6,48(sp); li a0,48; 0x84ad4 bltu s8,a0 *)
  pky_run x HAE B20 B260 pky_Bspan0.
  pky_br pky_Bspan0 Hb2; pky_hc HAE Hb2; rewrite U24, U_lit, Z.add_0_r in Hb2 by lia.
  + pose proof (pky_key_val x ck _ Hd Hp Hb2) as Hk.
    pky_run_to x HAE B20 B260 pky_Bspan0 PK_VL.
    pky_vlc x regs mem md cl L Hc Hcl HC HJ KW HAE HCR B20 B260 HVL HFX HM R20 R21 R22 R23 R24 U51
      (PIS.s10_val (pky_rest x ck)) Headamp.HA_PAD Hk.
  + pose proof (pky_cell_range x ck cc (pky_key_rng x ck _ Hd Hp Hb2)) as Hpc.
    pky_run_to x HAE B20 B260 pky_Bspan0 PK_RF.
    pky_rfc x regs mem md cl L Hc Hcl HC HJ KW HAE HCR B20 B260 HRF HFX HM R20 R21 R22 R23 U50 U48 U51 5 Hpc.
- (* res <> 0: 0x84a74 .. 0x84a80 strcmp(name, "sens") *)
  apply Z.eqb_neq in Hb1. assert (Hn1 : pky_nm x ck <> Headamp.NAME_PAD) by (intros E; apply Hb1; apply Hiff; exact E).
  pky_run x HAE B20 B260 pky_Bspan0.
  pky_cmpc x r cc n ck cl keys rf F fc regs mem md L Hc Hcl HC HJ KW HAE HCR B20 B260 HKC HFX HM Hd
    R20 R21 R22 R23 R24 R25 U25 PK_RA_CMP3 (hi_asens headamp_himg_A) Headamp.NAME_SENS Csens 2%nat.
  intros j Hj. assert (j = 0%nat \/ j = 1%nat) as [-> | ->] by lia; [exact Hn0 | exact Hn1].
Qed.

Lemma pky_seg_c2 : forall x r cc n ck cl keys rf res F fc regs mem md, call_ok x ->
KC_at x r cc n ck cl keys rf 2 res F fc regs mem md ->
(forall bad regs' mem' md', RF_at x r cc n ck cl keys rf bad F fc regs' mem' md' ->
  SRr rsegs (hx_W x) (cfg_at (fx := mkFP F fc) rsegs PK_RF regs' mem' md') (PPOST B MT x)) ->
(forall ch p regs' mem' md', VL_at x r cc n ck cl keys rf ch p F fc regs' mem' md' ->
  SRr rsegs (hx_W x) (cfg_at (fx := mkFP F fc) rsegs PK_VL regs' mem' md') (PPOST B MT x)) ->
SRr rsegs (hx_W x) (cfg_at (fx := mkFP F fc) rsegs PK_RA_CMP3 regs mem md) (PPOST B MT x).
Proof.
intros x r cc n ck cl keys rf res F fc regs mem md Hc HK HRF HVL.
pky_kc_intro x r cc n ck cl keys rf 2%nat res F fc regs mem md Hc HK.
set (L := pky_Lc x r cc keys rf).
destruct (pky_kc_cs x r cc n ck cl keys rf 2 res F fc regs mem md HK) as [_ CS1].
pose proof (pky_entry x PAT_DOT cl _ regs mem md L pky_cs_c1 PK_RA_CMP3 F fc Hc HC eq_refl
  ltac:(vm_compute; reflexivity) (CS1 ltac:(lia))) as HS.
pose proof (hk_core_journal B x _ _ _ _ _ _ HC) as (HJ & OK & HPt).
assert (SHOK : sh_ok rsegs hk_Bx [] (hk_env x regs L) (mrestrict (w_H (hx_W x)) mem)) by apply Forall_nil.
assert (KW : pky_KW x mem mem) by apply pky_KW_refl.
assert (HAE : env_agree 53 (hk_env x regs L) (hk_env x regs L)) by apply env_agree_refl.
assert (B20 : bv_unsigned (ew (hk_env x regs L) 2) = hx_spa x) by (rewrite (hk_env_reg x regs _ 2 2%bv eq_refl), R2; apply pky_w64; lia).
assert (B260 : bv_unsigned (ew (hk_env x regs L) 26) = hx_shf x) by (rewrite (hk_env_reg x regs _ 26 26%bv eq_refl), R26; apply pky_w64; lia).
pky_kc_U x r cc ck rf regs L R10 R24 R25.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
assert (Hn0 : pky_nm x ck <> Headamp.NAME_PHANTOM) by exact (Hprev 0%nat ltac:(lia)).
assert (Hn1 : pky_nm x ck <> Headamp.NAME_PAD) by exact (Hprev 1%nat ltac:(lia)).
unfold cfg_at in *. change (w64 PK_RA_CMP3) with (Z_to_bv 64 PK_RA_CMP3).
(* 0x84a84 .. 0x84a94 a1 = rf, a4 = [spa + 32], a5 = 8, a6 = [spa + 48], a7 = 4; 0x84a98 bnez a0 *)
pky_run x HAE B20 B260 pky_Bspan0.
pky_br pky_Bspan0 Hb1; pky_hc HAE Hb1; rewrite U10, U_lit, pky_res0 in Hb1 by lia.
- (* res <> 0: no name matched: BAD_KEY *)
  apply negb_true_iff, Z.eqb_neq in Hb1. assert (Hn2 : pky_nm x ck <> Headamp.NAME_SENS) by (intros E; apply Hb1; apply Hiff; exact E).
  pose proof (pky_cell_bad x ck cc (pky_key_none x ck Hd (hgk_param_none _ Hn0 Hn1 Hn2))) as Hpc.
  pky_run_to x HAE B20 B260 pky_Bspan0 PK_RF.
  pky_rfc x regs mem md cl L Hc Hcl HC HJ KW HAE HCR B20 B260 HRF HFX HM R20 R21 R22 R23 U50 U48 U51 4 Hpc.
- (* res = 0: the name is "sens"; 0x84a9c li a3,2; [spa + 8] = 0x38; 0x84ad0 li a0,48; bltu s8,a0 *)
  apply negb_false_iff, Z.eqb_eq in Hb1. apply Hiff in Hb1. cbn [nth pky_names] in Hb1.
  assert (Hp : Headamp.param_of_name (pky_nm x ck) = Some Headamp.HA_SENS) by (apply hgk_param_sens; assumption).
  pky_run x HAE B20 B260 pky_Bspan0.
  pky_br pky_Bspan0 Hb2; pky_hc HAE Hb2; rewrite U24, U_lit, Z.add_0_r in Hb2 by lia.
  + pose proof (pky_key_val x ck _ Hd Hp Hb2) as Hk.
    pky_run_to x HAE B20 B260 pky_Bspan0 PK_VL.
    pky_vlc x regs mem md cl L Hc Hcl HC HJ KW HAE HCR B20 B260 HVL HFX HM R20 R21 R22 R23 R24 U51
      (PIS.s10_val (pky_rest x ck)) Headamp.HA_SENS Hk.
  + pose proof (pky_cell_range x ck cc (pky_key_rng x ck _ Hd Hp Hb2)) as Hpc.
    pky_run_to x HAE B20 B260 pky_Bspan0 PK_RF.
    pky_rfc x regs mem md cl L Hc Hcl HC HJ KW HAE HCR B20 B260 HRF HFX HM R20 R21 R22 R23 U50 U48 U51 5 Hpc.
Qed.

(* ======================================= the segment ======================================= *)
Theorem hp_segKEY_A : segKEY_stmt B MT.
Proof.
unfold segKEY_stmt, KEY_ok. intros x r cc n ck cl keys rf Hc HADV HVAL F fc regs mem md HK.
assert (HRF : forall bad regs' mem' md', RF_at x r cc n ck cl keys rf bad F fc regs' mem' md' ->
  SRr rsegs (hx_W x) (cfg_at (fx := mkFP F fc) rsegs PK_RF regs' mem' md') (PPOST B MT x))
  by (intros bad regs' mem' md' HR; exact (pky_rf x r cc n ck cl keys rf bad F fc regs' mem' md' Hc HR HADV)).
assert (HVL : forall ch p regs' mem' md', VL_at x r cc n ck cl keys rf ch p F fc regs' mem' md' ->
  SRr rsegs (hx_W x) (cfg_at (fx := mkFP F fc) rsegs PK_VL regs' mem' md') (PPOST B MT x))
  by (intros ch p regs' mem' md' HV; exact (pky_vl x r cc n ck cl keys rf ch p F fc regs' mem' md' Hc HV (HVAL ch p))).
apply (pky_seg_a x r cc n ck cl keys rf F fc regs mem md Hc HK).
intros regs1 mem1 md1 HT. apply (pky_seg_1 x r cc n ck cl keys rf F fc regs1 mem1 md1 Hc HT HRF).
intros res1 regs2 mem2 md2 HK1. apply (pky_seg_c0 x r cc n ck cl keys rf res1 F fc regs2 mem2 md2 Hc HK1 HRF HVL).
intros res2 regs3 mem3 md3 HK2. apply (pky_seg_c1 x r cc n ck cl keys rf res2 F fc regs3 mem3 md3 Hc HK2 HRF HVL).
intros res3 regs4 mem4 md4 HK3. exact (pky_seg_c2 x r cc n ck cl keys rf res3 F fc regs4 mem4 md4 Hc HK3 HRF HVL).
Qed.

End b.

Print Assumptions hp_segKEY_A.
