(* Modified by Theorem Labs, 2026-10: the call-site form of lib/Reusable/YCbq.v's aj_bcmp_at (lines 2262-2310), restated
   for the strcmp wrapper's contract astrcmp_realizes of lib/Reusable/AStrcmpDef.v (fuzz_identity's text, module paths
   changed): the same journal threading through ecall_pre_at and ajournal_after_write, with the strcmp contract's
   str_meet premise and its strcmp_res result in place of bcmp's n-byte compare. The string lemmas below are new. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgStrcmp.v at ef44c49740f for reac-pw/fuzz_headamp
   image A; module paths changed; restated for the strncmp wrapper's contract (reac-pw/fuzz_pin lib/A/PPgWrap.v
   astrncmp_realizes), which is taken as the Section hypothesis STRNCMP: aj_strcmp_at becomes
   hc_strncmp_at, with the contract's string premises (awrap_str, the len + 8 range) and its result (a0 = 0 exactly
   when d = 0) in place of str_meet and strcmp_res; role's string lemmas (cstr_at, str_meet_of_cstr, the range
   lemmas, rl_cstr_args) are replaced by hc_awrap_of, hc_awrap_cstr and hc_awrap_blk, which give the wrapper's
   premises from headamp's string facts; hc_aro_of_arodata and the call-site lemma hc_strncmp_key_call are new. *)
(* reac-pw/fuzz_headamp image A (fuzz_headamp.asan, pinned sha256
   f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47; every address below is measured on the
   unstripped twin b5f352154c54a97c66fd92dfa228e8a854498f6cd313dba0107900546b043f9a, whose loaded sections are
   byte-equal to the pin's except .note.gnu.build-id): the CALL ADAPTER of the strncmp wrapper. Proves no function (kind: segment lemma).

   THE CALLEE. __interceptor_trampoline_strncmp 0x41ba4 is the 4-byte jump to the wrapper ___interceptor_strncmp
   0x4268c. The wrapper compares the two strings byte by byte by musl strncmp 0x95c00, up to the first index where
   the bytes differ or one of them is 0, or until n bytes are compared; then it checks that the bytes it read are
   marked usable in the shadow map, and returns musl's result. It uses at most 2 ESTACK bytes of stack below sp and
   writes no byte outside them. Its contract is reac-pw/fuzz_pin's text, lib/A/PPgWrap.v lines 82-133 (awrap_str,
   awrap_post, astrncmp_realizes), with aro_unowned of libreac/fuzz_identity lib/A/Rt/WrapRo.v
   line 24 (origin/ossv/recipes 2d2ff01bb6f2). No file this one Requires, directly or through another, defines
   those four names (lib/A/HPgWrap.v and lib/A/Rt/WrapRo.v do), so the Section below takes the contract at 0x41ba4
   as the hypothesis STRNCMP, with the four definitions unfolded and
   beta-reduced word for word: the port of the wrapper's walk (fuzz_pin lib/A/PPgWrapNcmp.v pin_astrncmp, which
   proves exactly that text at pin's 0x41914) gives `astrncmp_realizes segs B 0x41ba4` here,
   which is convertible to STRNCMP's type and discharges it by `exact`. strncmp_model is lib/Spec/StrFun.v:157.

   THE TWO CALL SITES (capstone over the unstripped twin):
     0x83190 in LLVMFuzzerTestOneInput (fuzz_headamp.c:120, the key test of expect_of): `jal` 0x41ba4, ra 0x83194,
             a0 = s2 = the key (0x83184; s2 = pp + 0x401c + 0x68 j, the body of entry j of the pod_ent table inside
             the pp block, whose address the code loads from R+0xf0 at 0x83058), a1 = 0x20f00 (auipc 0x83178 + addi
             0x8317c: the harness's "reac.headamp.", HPgImgA.headamp_himg_A's hi_hkey), a2 = 13 (0x83180);
     0x849c8 in reac_headamp_prop_parse_result (reac_headamp_prop.c:148): `jal` 0x41ba4, ra 0x849cc, a0 = s8 = the
             key (0x849c4; a C string inside the pod's bytes [P, P + len), which the parse's contract
             HPgCSpec.hd_parse_args gives as a live block of the caller's state with its bytes, shadow facts and
             ranges: hc_awrap_sub reads the key from those facts), a1 = 0x21460
             (auipc 0x849b8 + addi 0x849bc: the parse's own "reac.headamp.", hi_akey), a2 = 13 (0x849c0).

   WHAT EACH LEMMA GIVES:
   - hc_aro_of_arodata: the contract's read-only premise (aro_unowned) from a walk's arodata_okP, as PPgWrap.v:77.
   - hc_strncmp_at: the call inside a caller's journal, at any sp = sp0 + o of that journal (the parse's walk uses it
     at 0x849c8 inside its own journal). The journal after the call is the caller's, at the same allocator state;
     every byte outside [sp0 + o - 2 ESTACK, sp0 + o) is kept; a0 = 0 exactly when strncmp_model's d = 0.
   - hc_awrap_of: the contract's string premises from the facts of a C string (its bytes and NUL, the tail of the
     NUL's 8-byte word readable, its len + 1 bytes marked usable with their shadow hull readable, len + 8 bytes of
     application memory range, no byte in the wrapper's window).
   - hc_awrap_cstr: the same from HPgBase.hd_cstr, the string facts the walks hold for the image's read-only strings
     (the literals 0x20f00 and 0x21460), and the window condition.
   - hc_awrap_blk: the same for a C string inside a live block whose bytes and NUL the walk knows, with the tail of
     the NUL's word readable (the key in pp at 0x83190): the block gives the rest. It lies in application memory
     below the allocator's ceiling (YG0d.v AR_blocks_law), so below every stack window of the journal and inside the
     len + 8 range; it is smaller than MALLOC_MAX; its shadow facts are AR's (YCbq.v range_addressable_of_block,
     shadow_hull_vis_of_block).
   - hc_awrap_sub: the same for a C string inside a range [P, P + n) whose facts the walk holds in the form the
     parse's contract states them for the pod (the bytes, the shadow facts over [P, P + n), amem_range P (n + 8), no
     byte in the wrapper's window): the key at 0x849c8. hc_off_stack_sub moves the parse contract's window
     (hd_off_stack at the parse's entry sp, T_parse_STK) to the wrapper's (the call's sp, 2 ESTACK); hc_hull_sub
     shrinks a shadow hull to a sub-range.
   - hc_strncmp_key_call: the call at 0x83190 in the continuation form of lib/A/HPgCalls.v (hc_call): from hc_core at
     the call, the walk continues at 0x83194 with hc_core again (the wrapper keeps the allocator state, so the
     journal's end state is the call's), the callee-saved registers, the I/O state, every byte outside
     [R - 2 ESTACK, R) as at the call, and a0 = 0 exactly when d = 0. The walk gets d and its meaning
     (d = 0 exactly when Pod/Headamp.v ha_prefix of the key is true) from lib/Prog/HeadCheck/PairFacts.v
     strncmp_prefix; this file does not restate it.
   The float state: the wrapper's post returns in a configuration of the Section's float state fx (awrap_post's
   cfg_at), so the continuation runs at the caller's own float state: fs1 and fs2 (-1.0f and 256.0f), which
   LLVMFuzzerTestOneInput sets before the call (0x83030, 0x83044) and reads after it, are kept. The lemmas hold for
   every float state, so a walk uses them at the float state it has reached (after the parse's return that is the
   parse's fx', HPgCSpec.hd_parse_post); STRNCMP must then hold at that float state too, as the port's theorem
   (stated for every float state) gives.

   Section hypotheses: segs_low (the image lies below the shadow map: lib/Reusable/YCbq.v's Section a0 asks it for
   ajournal_after_write) and STRNCMP (the wrapper's contract at 0x41ba4). *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK14 YK0s YK15 YK18 YP09 YI04 YI08 YN3v YI00 YI0m YI09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q YG05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require StrFun.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec HPgImgA HPgCalls.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ======================================== image A: the callee, the return address, the literal ======================================== *)
Definition A_STRNCMP : Z := 0x41ba4.          (* __interceptor_trampoline_strncmp: `j` ___interceptor_strncmp 0x4268c *)
Definition RA_STRNCMP : Z := 0x83194.         (* LLVMFuzzerTestOneInput's `jal` 0x83190 plus 4 *)
Definition A_HKEY : Z := 0x20f00.             (* the harness's "reac.headamp." *)

Lemma hc_hkey_A : A_HKEY = hi_hkey headamp_himg_A.
Proof. reflexivity. Qed.

Lemma hc_prefix_len : Z.of_nat (length Headamp.HA_PREFIX) = 13.
Proof. vm_compute. reflexivity. Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section c.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.

(* The strncmp wrapper's contract at image A's trampoline: reac-pw/fuzz_pin lib/A/PPgWrap.v:121-133
   `astrncmp_realizes segs B A_STRNCMP`, with awrap_str (PPgWrap.v:82-93), awrap_post (PPgWrap.v:98-106)
   and aro_unowned (libreac/fuzz_identity lib/A/Rt/WrapRo.v:24-26 at origin/ossv/recipes 2d2ff01bb6f2) unfolded and
   beta-reduced. The port of the wrapper's walk (fuzz_pin lib/A/PPgWrapNcmp.v pin_astrncmp) proves
   that text; at 0x41ba4 it discharges this hypothesis by `exact`. *)
Hypothesis STRNCMP :
forall ly S W regs mem md x y n (ls rs : list byte) (d : Z),
ecall_pre segs B ly S W regs mem md ->
ly_stk_lo ly + 2 * ESTACK <= spZ regs ->
(forall a, spZ regs - 2 * ESTACK <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 10 = w64 x -> getr regs 11 = w64 y -> getr regs 12 = w64 n ->
0 <= n < 2 ^ 32 ->
(0 < x /\ ~ In (Z_to_bv 8 0) ls /\
 Z.of_nat (length ls) + 1 < 2 ^ 32 /\ x + Z.of_nat (length ls) + 1 <= 2 ^ 63 /\
 garr8 segs (mrestrict (w_H W) mem) x (map (fun b : byte => bv_unsigned b) ls ++ [0]) /\
 src_ok segs W regs mem x (Z.of_nat (length ls) + 1) /\
 (forall a, x <= a <= x + Z.of_nat (length ls) -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) /\
 amem_range x (Z.of_nat (length ls) + 1) /\
 range_addressable (aview segs (w_H W) mem) SHADOW_OFF x (Z.of_nat (length ls) + 1) /\
 shadow_hull_vis (aview segs (w_H W) mem) x (Z.of_nat (length ls) + 1) /\
 (forall a, x + Z.of_nat (length ls) < a < x + Z.of_nat (length ls) - (x + Z.of_nat (length ls)) mod 8 + 8 ->
  aview segs (w_H W) mem a <> None)) ->
(0 < y /\ ~ In (Z_to_bv 8 0) rs /\
 Z.of_nat (length rs) + 1 < 2 ^ 32 /\ y + Z.of_nat (length rs) + 1 <= 2 ^ 63 /\
 garr8 segs (mrestrict (w_H W) mem) y (map (fun b : byte => bv_unsigned b) rs ++ [0]) /\
 src_ok segs W regs mem y (Z.of_nat (length rs) + 1) /\
 (forall a, y <= a <= y + Z.of_nat (length rs) -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) /\
 amem_range y (Z.of_nat (length rs) + 1) /\
 range_addressable (aview segs (w_H W) mem) SHADOW_OFF y (Z.of_nat (length rs) + 1) /\
 shadow_hull_vis (aview segs (w_H W) mem) y (Z.of_nat (length rs) + 1) /\
 (forall a, y + Z.of_nat (length rs) < a < y + Z.of_nat (length rs) - (y + Z.of_nat (length rs)) mod 8 + 8 ->
  aview segs (w_H W) mem a <> None)) ->
amem_range x (Z.of_nat (length ls) + 8) -> amem_range y (Z.of_nat (length rs) + 8) ->
StrFun.strncmp_model (ls ++ [Z_to_bv 8 0]) (rs ++ [Z_to_bv 8 0]) n = Some d ->
(forall a, in_rom segs a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
 aview segs (w_H W) mem a = option_map (fun b : byte => bv_unsigned b) (seg_rom segs (Z_to_bv 64 a))) ->
SRr segs W (cfg_at segs A_STRNCMP regs mem md)
(fun (W' : world segs) (c' : config) => W' = W /\ exists regs' mem' md',
 c' = cfg_at segs (raZ regs) regs' mem' md' /\
 AR segs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
 (exists v : word, getr regs' 10 = v /\ (v = w64 0 <-> d = 0)) /\
 (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs) ->
  aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
 (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).

(* ======================================== the read-only premise ======================================== *)
(* The contract's read-only premise (aro_unowned, unfolded) from the walks' arodata_okP: the in-segment half of it. *)
Lemma hc_aro_of_arodata : forall RLO RHI (rd : reader), arodata_okP segs RLO RHI B rd ->
forall a, in_rom segs a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
rd a = option_map (fun b : byte => bv_unsigned b) (seg_rom segs (Z_to_bv 64 a)).
Proof. intros RLO RHI rd HR a Ha Ho He. apply HR; [left; exact Ha | exact Ho | exact He]. Qed.

(* ======================================== the call inside a caller's journal ======================================== *)
(* At sp = sp0 + o of the caller's journal, with the stack of 2 ESTACK below sp inside the journal's window, the
   contract's string premises for a0 = x / ls and a1 = y / rs, a2 = n and strncmp_model's d: the call returns to ra
   with the journal extended to the call's allocator state, the bytes outside the wrapper's window kept, and
   a0 = 0 exactly when d = 0. *)
Lemma hc_strncmp_at :
forall W (regsT : bvmap 5 word) memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x y n (ls rs : list byte) (d o : Z) raw,
ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
getr regsT 10 = w64 x -> getr regsT 11 = w64 y -> getr regsT 12 = w64 n -> 0 <= n < 2 ^ 32 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 2 * ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
(0 < x /\ ~ In (Z_to_bv 8 0) ls /\
 Z.of_nat (length ls) + 1 < 2 ^ 32 /\ x + Z.of_nat (length ls) + 1 <= 2 ^ 63 /\
 garr8 segs (mrestrict (w_H W) memT) x (map (fun b : byte => bv_unsigned b) ls ++ [0]) /\
 src_ok segs W regsT memT x (Z.of_nat (length ls) + 1) /\
 (forall a, x <= a <= x + Z.of_nat (length ls) -> ~ (spZ regsT - 2 * ESTACK <= a < spZ regsT)) /\
 amem_range x (Z.of_nat (length ls) + 1) /\
 range_addressable (aview segs (w_H W) memT) SHADOW_OFF x (Z.of_nat (length ls) + 1) /\
 shadow_hull_vis (aview segs (w_H W) memT) x (Z.of_nat (length ls) + 1) /\
 (forall a, x + Z.of_nat (length ls) < a < x + Z.of_nat (length ls) - (x + Z.of_nat (length ls)) mod 8 + 8 ->
  aview segs (w_H W) memT a <> None)) ->
(0 < y /\ ~ In (Z_to_bv 8 0) rs /\
 Z.of_nat (length rs) + 1 < 2 ^ 32 /\ y + Z.of_nat (length rs) + 1 <= 2 ^ 63 /\
 garr8 segs (mrestrict (w_H W) memT) y (map (fun b : byte => bv_unsigned b) rs ++ [0]) /\
 src_ok segs W regsT memT y (Z.of_nat (length rs) + 1) /\
 (forall a, y <= a <= y + Z.of_nat (length rs) -> ~ (spZ regsT - 2 * ESTACK <= a < spZ regsT)) /\
 amem_range y (Z.of_nat (length rs) + 1) /\
 range_addressable (aview segs (w_H W) memT) SHADOW_OFF y (Z.of_nat (length rs) + 1) /\
 shadow_hull_vis (aview segs (w_H W) memT) y (Z.of_nat (length rs) + 1) /\
 (forall a, y + Z.of_nat (length rs) < a < y + Z.of_nat (length rs) - (y + Z.of_nat (length rs)) mod 8 + 8 ->
  aview segs (w_H W) memT a <> None)) ->
amem_range x (Z.of_nat (length ls) + 8) -> amem_range y (Z.of_nat (length rs) + 8) ->
StrFun.strncmp_model (ls ++ [Z_to_bv 8 0]) (rs ++ [Z_to_bv 8 0]) n = Some d ->
(forall a, in_rom segs a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
 aview segs (w_H W) memT a = option_map (fun b : byte => bv_unsigned b) (seg_rom segs (Z_to_bv 64 a))) ->
SRr segs W (cfg_at segs A_STRNCMP regsT memT mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
 c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
 ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
 aregs_preserved regsT regs2 /\ same_io mdc md2 /\
 (exists v : word, getr regs2 10 = v /\ (v = w64 0 <-> d = 0)) /\
 (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o) ->
  aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
 (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
intros W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x y n ls rs d o raw
HJ Ha0 Ha1 Ha2 Hn Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hx Hy Hmx Hmy Hmd Hro.
pose proof (AR_laws_ok segs B) as LAWS.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
assert (ESTACK = 4096) as Hes by reflexivity.
assert (HPRE : ecall_pre segs B lyc Sc W regsT memT mdc).
{ apply (ecall_pre_at segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT o HJ Hsp' Hal Hneg);
  [clear - Hbud Hes; lia | rewrite Hra; exact Hraw | exact Hgp | exact Htp]. }
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (Hlo2 : ly_stk_lo lyc + 2 * ESTACK <= spZ regsT)
by (rewrite Eslo, Hsp'; clear - Hslo Hbud; lia).
assert (Hpres2E : forall a, spZ regsT - 2 * ESTACK <= a < spZ regsT -> apresent (w_H W) memT a).
{ intros a Ha. apply Hpres. rewrite Hsp' in Ha. clear - Ha Hneg Hbud. lia. }
eapply SRr_mono.
{ exact (STRNCMP lyc Sc W regsT memT mdc x y n ls rs d HPRE Hlo2 Hpres2E Ha0 Ha1 Ha2 Hn Hx Hy Hmx Hmy Hmd Hro). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hres & Hfr & Hpres2).
rewrite Hsp' in Hfr.
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (ajournal_after_write segs B LAWS segs_low STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k mem2 md2
    (fun a => sp0 + o - 2 * ESTACK <= a < sp0 + o) Sc own HJ).
  - intros a Ha Hna. apply (Hfr a Ha). exact Hna.
  - exact Hpres2.
  - exact Hsame.
  - intros a Ha; left; left; clear - Ha Hneg Hbud Hes Hceil Hslo; zlia.
  - exact HAR2.
  - reflexivity.
  - reflexivity.
  - lia.
  - exact Hfrs.
  - exact HQT. }
split; [exact HP|]. split; [apply same_io_materialized; exact Hsame|].
split; [exact Hres|]. split; [exact Hfr | exact Hpres2].
Qed.

(* ======================================== the string premises ======================================== *)
(* The bytes of a garr8 list are readable. *)
Lemma hc_garr8_some : forall H mem a (s : list Z), garr8 segs (mrestrict H mem) a s ->
forall b, a <= b < a + Z.of_nat (length s) -> aview segs H mem b <> None.
Proof.
intros H mem a s Hg b Hb.
pose proof (garr8_mbyte segs (mrestrict H mem) a s (Z.to_nat (b - a)) Hg ltac:(lia)) as M.
rewrite Z2Nat.id in M by lia. replace (a + (b - a)) with b in M by lia.
unfold aview. rewrite M. discriminate.
Qed.

(* Bytes known through the reader make a garr8 list. *)
Lemma hc_garr8_of_aview : forall H mem a (s : list Z), Forall (fun v => 0 <= v < 256) s ->
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

Lemma hc_bytes_pos : forall s : list Z, Forall (fun v => 0 < v < 256) s -> Forall (fun v => 0 <= v < 256) s.
Proof. intros s H. rewrite Forall_forall in *. intros v Hv. specialize (H v Hv). lia. Qed.

(* A list of bytes whose values are all nonzero holds no NUL. *)
Lemma hc_notin0 : forall l : list byte, Forall (fun v => 0 < v < 256) (hd_zbytes l) -> ~ In (Z_to_bv 8 0) l.
Proof.
intros l H Hin. unfold hd_zbytes in H. rewrite Forall_forall in H.
specialize (H _ (in_map (fun b : byte => bv_unsigned b) _ _ Hin)). cbv beta in H.
assert (E : bv_unsigned (Z_to_bv 8 0) = 0) by reflexivity. rewrite E in H. lia.
Qed.

(* The facts of a C string l at a give the contract's string premises (awrap_str at regs, mem) and its
   len + 8 range. *)
Lemma hc_awrap_of : forall (W : world segs) (regs : bvmap 5 word) mem a (l : list byte),
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
split; [clear - Hm8; zlia|].
split; [exact Hg|].
split.
{ intros b Hb. split.
  - apply (hc_garr8_some (w_H W) mem a _ Hg). rewrite Lz. lia.
  - intros Hw. apply (Hoff b ltac:(lia)). clear - Hw Hes. lia. }
split; [intros b Hb; apply Hoff; lia|].
split; [eapply hd_amem_range_le; [|exact Hm8]; lia|].
split; [exact Hra|]. split; [exact Hhv|].
exact Htl.
Qed.

(* A read-only string as the walks hold it (HPgBase.hd_cstr) with no byte in the wrapper's window: the literals
   0x20f00 (the harness's) and 0x21460 (the parse's). *)
Lemma hc_awrap_cstr : forall (W : world segs) (regs : bvmap 5 word) mem a (l : list byte),
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
apply hc_awrap_of.
- exact Ha0.
- exact (hc_notin0 l Hf).
- clear - Hlow Ha0. unfold kLowMemEnd in Hlow. lia.
- apply (proj2 (garr8_app segs _ a (hd_zbytes l) [0])). split.
  + exact (hc_garr8_of_aview (w_H W) mem a (hd_zbytes l) (hc_bytes_pos _ Hf) Hb).
  + rewrite Ll. apply hc_garr8_of_aview; [constructor; [cbv beta; lia | constructor]|].
    intros i Hi. cbn [length Z.of_nat] in Hi. assert (i = 0) as -> by lia. rewrite Z.add_0_r. exact Hn.
- exact Hoff.
- exact Hm8.
- exact Hra.
- exact Hhv.
- exact Htl.
Qed.

(* A C string inside a live block [p, p + req_size m) of the journal's end state whose bytes and NUL the walk
   knows (garr8), with the tail of the NUL's word readable: the key in pp at 0x83190. The block gives the rest: it
   lies in application memory below the allocator's ceiling, so below every stack window of the journal and inside
   the len + 8 range; it is smaller than MALLOC_MAX; its bytes are marked usable and their shadow hull is readable
   (AR's shadow law). *)
Lemma hc_awrap_blk : forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word)
(o p m a : Z) (l : list byte),
ajournal segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
spZ regs = sp0 + o -> o <= 0 -> 2 * ESTACK - o <= STK ->
In (p, m) (ablocks B lyc Sc) -> p <= a -> a + Z.of_nat (length l) + 1 <= p + req_size m ->
garr8 segs (mrestrict (w_H W) memc) a (hd_zbytes l ++ [0]) ->
~ In (Z_to_bv 8 0) l ->
hd_str_tail (aview segs (w_H W) memc) (a + Z.of_nat (length l)) ->
(0 < a /\ ~ In (Z_to_bv 8 0) l /\
 Z.of_nat (length l) + 1 < 2 ^ 32 /\ a + Z.of_nat (length l) + 1 <= 2 ^ 63 /\
 garr8 segs (mrestrict (w_H W) memc) a (map (fun b : byte => bv_unsigned b) l ++ [0]) /\
 src_ok segs W regs memc a (Z.of_nat (length l) + 1) /\
 (forall b, a <= b <= a + Z.of_nat (length l) -> ~ (spZ regs - 2 * ESTACK <= b < spZ regs)) /\
 amem_range a (Z.of_nat (length l) + 1) /\
 range_addressable (aview segs (w_H W) memc) SHADOW_OFF a (Z.of_nat (length l) + 1) /\
 shadow_hull_vis (aview segs (w_H W) memc) a (Z.of_nat (length l) + 1) /\
 (forall b, a + Z.of_nat (length l) < b < a + Z.of_nat (length l) - (a + Z.of_nat (length l)) mod 8 + 8 ->
  aview segs (w_H W) memc b <> None)) /\
amem_range a (Z.of_nat (length l) + 8).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs o p m a l
HJ Hsp Hneg Hbud Hin Hpa Hae Hg Hnz Htl.
pose proof (AR_laws_ok segs B) as LAWS.
pose proof HJ as (HAR & _).
destruct (al_blocks _ _ (AR_laws_ok segs B) _ _ _ _ _ _ _ HAR Hin) as (_ & H4096 & Hceil & Happ & _ & _ & Hmax).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (_ & _ & Hlo & Hslo & _).
pose proof asan_consts as (C1 & _).
assert (ESTACK = 4096) as Hes by reflexivity.
assert (Hrs : 1 <= req_size m <= Z.max m 1) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
assert (Hra : range_addressable (aview segs (w_H W) memc) SHADOW_OFF a (Z.of_nat (length l) + 1))
by (exact (range_addressable_of_block segs B LAWS lyc Sc W memc mdc p m a (Z.of_nat (length l) + 1) HAR Hin Hpa
  ltac:(lia))).
assert (Hhv : shadow_hull_vis (aview segs (w_H W) memc) a (Z.of_nat (length l) + 1))
by (exact (shadow_hull_vis_of_block segs B LAWS lyc Sc W memc mdc p m a (Z.of_nat (length l) + 1) HAR Hin Hpa
  ltac:(lia) ltac:(lia))).
clear HJ HAR.
apply hc_awrap_of.
- lia.
- exact Hnz.
- unfold MALLOC_MAX in Hmax. clear - Hmax Hrs Hpa Hae. lia.
- exact Hg.
- intros x Hx. rewrite Hsp. clear - Hx Hpa Hae Hceil Hlo Hslo Hbud Hes. lia.
- clear - Happ C1 Hpa Hae. unfold in_app in Happ. destruct Happ as (_ & [Hl | (Hh1 & Hh2)]); unfold amem_range;
  [left | right]; unfold ASAN_CEIL, kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia.
- exact Hra.
- exact Hhv.
- exact Htl.
Qed.

(* A shadow hull shrinks to a sub-range. *)
Lemma hc_hull_sub : forall (rd : reader) x n y k, shadow_hull_vis rd x n -> x <= y -> y + k <= x + n -> 0 < k ->
shadow_hull_vis rd y k.
Proof.
intros rd x n y k H Hxy Hyk Hk s Hs. apply H.
pose proof (shadow_mono x y Hxy) as M1. pose proof (shadow_mono (y + k - 1) (x + n - 1) ltac:(lia)) as M2.
assert (R8 : forall u v, u <= v -> u / 8 * 8 <= v / 8 * 8)
by (intros u v Huv; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
pose proof (R8 _ _ M1) as N1. pose proof (R8 _ _ M2) as N2. clear - Hs N1 N2. lia.
Qed.

(* A range kept out of one stack window is kept out of a smaller one inside it, for a sub-range: the parse's
   hd_off_stack at its entry sp and T_parse_STK, moved to the wrapper's 2 ESTACK below the call's sp. *)
Lemma hc_off_stack_sub : forall (regs regs' : bvmap 5 word) T T' p n p' n',
hd_off_stack regs T p n -> spZ regs - T <= spZ regs' - T' -> spZ regs' <= spZ regs -> p <= p' -> p' + n' <= p + n ->
hd_off_stack regs' T' p' n'.
Proof. intros regs regs' T T' p n p' n' H H1 H2 H3 H4 x Hx Hw. apply (H x ltac:(lia)). lia. Qed.

(* A C string inside a range [P, P + n) whose facts the walk holds in the form HPgCSpec.hd_parse_args states them
   for the pod (its bytes marked usable, their shadow hull readable, amem_range P (n + 8), no byte in the wrapper's
   window), with the string's bytes and NUL (garr8) and the tail of the NUL's word readable: the key at 0x849c8. *)
Lemma hc_awrap_sub : forall (W : world segs) (regs : bvmap 5 word) mem (P n a : Z) (l : list byte),
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
apply hc_awrap_of.
- lia.
- exact Hnz.
- lia.
- exact Hg.
- intros x Hx. apply Hoff. lia.
- clear - Hm Hpa Hae. destruct Hm as [Hl | (Hh1 & Hh2)]; unfold amem_range; [left | right; split]; lia.
- eapply range_addressable_sub; [exact Hra | lia | lia].
- exact (hc_hull_sub _ P n a (Z.of_nat (length l) + 1) Hhv Hpa ltac:(lia) ltac:(lia)).
- exact Htl.
Qed.

(* ======================================== the harness's call at 0x83190 ======================================== *)
(* strncmp(key, "reac.headamp.", 13) in LLVMFuzzerTestOneInput (fuzz_headamp.c:120), in hc_call's continuation form:
   the key a C string inside a live block, the literal the image's string at 0x20f00. The continuation runs at
   0x83194 at the caller's own float state, with hc_core at the call's allocator state again. *)
Lemma hc_strncmp_key_call : forall RLO RHI (Q : world segs -> config -> Prop)
STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) (R key p m d : Z) (kb : list byte),
hc_core segs B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R ->
getr regs 1 = w64 RA_STRNCMP ->
getr regs 10 = w64 key -> getr regs 11 = w64 A_HKEY -> getr regs 12 = w64 13 ->
In (p, m) (ablocks B lyc Sc) -> p <= key -> key + Z.of_nat (length kb) + 1 <= p + req_size m ->
garr8 segs (mrestrict (w_H W) memc) key (hd_zbytes kb ++ [0]) ->
~ In (Z_to_bv 8 0) kb ->
hd_str_tail (aview segs (w_H W) memc) (key + Z.of_nat (length kb)) ->
hd_cstr segs (w_H W) memc A_HKEY (hd_zbytes Headamp.HA_PREFIX) ->
arodata_okP segs RLO RHI B (aview segs (w_H W) memc) ->
StrFun.strncmp_model (kb ++ [Z_to_bv 8 0]) (Headamp.HA_PREFIX ++ [Z_to_bv 8 0]) 13 = Some d ->
(forall (regs2 : bvmap 5 word) mem2 md2,
 hc_core segs B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W mem2 md2 regs2 R ->
 aregs_preserved regs regs2 -> same_io mdc md2 ->
 (forall x, 0 <= x < 2 ^ 64 -> ~ (R - 2 * ESTACK <= x < R) ->
  aview segs (w_H W) mem2 x = aview segs (w_H W) memc x) ->
 (exists v : word, getr regs2 10 = v /\ (v = w64 0 <-> d = 0)) ->
 SRr segs W (cfg_at segs RA_STRNCMP regs2 mem2 md2) Q) ->
SRr segs W (cfg_at segs A_STRNCMP regs memc mdc) Q.
Proof.
intros RLO RHI Q STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R key p m d kb
HC Hra Ha0 Ha1 Ha2 Hin Hpk Hke Hg Hnz Htl Hlit Hro Hmd K.
pose proof (hc_core_R segs B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R HC) as (HRc & _ & Hsp).
pose proof HC as (HJ & Hev & H2 & H3 & H4 & HRal & Hwin & HRs).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hst & _).
destruct Hst as (Hsp0al & _).
assert (ESTACK = 4096) as Hes by reflexivity.
assert (Hts : T_SEG_STK = 16384) by reflexivity.
pose proof asan_consts as (C1 & _).
assert (Hsp' : spZ regs = sp0 + (R - sp0)) by (rewrite Hsp; ring).
assert (Hal' : (R - sp0) mod 16 = 0) by (clear - HRal Hsp0al; Z.div_mod_to_equations; lia).
assert (Hneg : R - sp0 <= 0) by (clear - HRs; lia).
assert (Hbud : 2 * ESTACK - (R - sp0) <= STK) by (clear - Hwin Hes Hts; lia).
destruct (hc_awrap_blk STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs (R - sp0) p m key kb
  HJ Hsp' Hneg Hbud Hin Hpk Hke Hg Hnz Htl) as (Hkey & Hk8).
assert (Hoff : hd_off_stack regs (2 * ESTACK) A_HKEY (Z.of_nat (length Headamp.HA_PREFIX) + 1)).
{ intros x Hx. rewrite Hsp. rewrite hc_prefix_len in Hx. unfold A_HKEY in Hx. clear - Hx HRc C1 Hes Hts. lia. }
destruct (hc_awrap_cstr W regs memc A_HKEY Headamp.HA_PREFIX Hlit Hoff) as (Hpre & Hp8).
eapply SRr_bind.
{ exact (hc_strncmp_at W regs memc STK sp0 FP ly S W0 mem0 md0 own lyc Sc mdc k key A_HKEY 13 kb Headamp.HA_PREFIX
    d (R - sp0) (w64 RA_STRNCMP) HJ Ha0 Ha1 Ha2 ltac:(lia) Hsp' Hal' Hneg Hbud H3 H4 Hra
    ltac:(apply hc_ret_ok; unfold RA_STRNCMP; lia) Hkey Hpre Hk8 Hp8 Hmd (hc_aro_of_arodata RLO RHI _ Hro)). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP & Hio & Hv & Hkeep & _).
apply (K regs2 mem2 md2).
- split; [exact HJ2|]. split; [exact Hev|].
  split; [rewrite <- H2; exact (HP 2 ltac:(unfold acallee_saved; lia))|].
  split; [rewrite <- H3; exact (HP 3 ltac:(unfold acallee_saved; lia))|].
  split; [rewrite <- H4; exact (HP 4 ltac:(unfold acallee_saved; lia))|].
  split; [exact HRal|]. split; [exact Hwin | exact HRs].
- exact HP.
- exact Hio.
- intros x Hx Hs. apply Hkeep; [exact Hx|]. replace (sp0 + (R - sp0)) with R by ring. exact Hs.
- exact Hv.
Qed.

End c.
End b.

Print Assumptions hc_hkey_A.
Print Assumptions hc_prefix_len.
Print Assumptions hc_aro_of_arodata.
Print Assumptions hc_strncmp_at.
Print Assumptions hc_awrap_of.
Print Assumptions hc_awrap_cstr.
Print Assumptions hc_awrap_blk.
Print Assumptions hc_hull_sub.
Print Assumptions hc_off_stack_sub.
Print Assumptions hc_awrap_sub.
Print Assumptions hc_strncmp_key_call.
