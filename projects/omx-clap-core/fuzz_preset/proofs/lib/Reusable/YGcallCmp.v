(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-31 (the world relation R): aj_memcmp_at_xR / aj_memcmp_at_xmR are the two
   call-site rules over a journal at a reflexive and transitive world relation R (binders first; the call keeps the
   world, so no law of R is read); aj_memcmp_at_x / aj_memcmp_at_xm keep their statements and are the instances at
   wle. *)
(* Theorem Labs, 2026-10-29: fuzz_preset, the memcmp CALL TEXT and CALL-SITE RULES over the allocator invariant ARx of
   YCbqG.v (Section Variables segs B PST ARx), in the plain form (_x) and with the YAkMemnorm keep (_xm). The text of
   record for c-libc-stdio's po_memcmp_cf row, and the nested call of its bcmp row (musl bcmp is one `j` to
   __wrap_memcmp, so the bcmp interceptor runs the whole memcmp interceptor inside it; lib/A/AE2s.v:213).
   rule 24: no function proved. rule 24: proves no function (kind: engine text).
   No allocator instance, no image class, no address and no ledger is named in a definition or a lemma.

   THE RESULT, MEASURED (capstone, RISC-V64C, on the four ASan images: rebuilt A asan f0d2e8d4.., rebuilt B asan-ubsan
   3b5e1a09.., #102 A bff8519b.., #102 B c90d4fa5.. (unstripped sha256); addresses given as rebuilt A / #102 A, the B
   images are the same instructions at other addresses):
   - __wrap_memcmp 0x42c94 / 0x42d28 is `j __interceptor_memcmp` (0x442e8 / 0x4437c).
   - __interceptor_memcmp: `jal AsanInited`, `beqz a0` -> tail `j internal_memcmp` (the not-initialised path; the model
     pins asan_inited to 1, A/AE2y.v:70 icpt_rodata 0xab598); `jal TryAsanInitFromRtl`, `beqz a0` -> `jr t1`, a tail
     call of REAL(memcmp); else `jal MemcmpInterceptorCommon` and return: only ra / s0-s2 reloads, `addi sp`, `ret`
     (0x44358 / 0x443ec), so a0 is MemcmpInterceptorCommon's a0 unchanged.
   - MemcmpInterceptorCommon 0x43a54 / 0x43ae8: s8 = &common_flags_dont_use (.got 0xa1ac0 / 0xa2000 -> .bss 0x13c3e8 /
     0x13c9e8); `lbu a1, 0xfe(s8)` (intercept_memcmp), `beqz` -> a direct REAL(memcmp) call; `lbu a1, 0xff(s8)`
     (strict_memcmp), `beqz` -> the CharCmpX loop (`sltu; sltu; sub s5, a1, a0`: -1 / 0 / 1); otherwise (strict) the two
     shadow range checks, then `jalr s5` = REAL(memcmp) (0x43b70 / 0x43c04), `mv s5, a0`, the weak hook (a bare `ret`,
     0x43a50 / 0x43ae4), `mv a0, s5` (0x43c74 / 0x43d08), `ret`. So on the strict path a0 is REAL(memcmp)'s a0 unchanged.
   - The model's flags: Tfib_const_abs pins the 8 bytes common_flags+0xf8..+0xff to 0x0101010101010101 (A/AF0m.v:61
     at 0x13c4e0, Reusable/YF0m.v:62 at 0x13cda0 for rebuilt B), so intercept_memcmp = strict_memcmp = 1 and the code
     takes the strict path; cgif's walk of this code reads exactly those bytes (A/AE2z.v:67 mcA_rodata). No #102
     constant table is on this branch; the #102 code reads the same two struct offsets.
   - REAL(memcmp) is musl memcmp (the interceptor's t1 is __interception::real_memcmp, .data 0xa3800 / 0xa3d40, which
     holds 0x9ad48 / 0x9b284 in the file; A/AE2z.v:67 pins it): `beqz a2` -> `mv a0, zero; ret`; a loop of
     `lbu a3, 0(a0); lbu a4, 0(a1); bne a3, a4`; at the first differing byte `sub a0, a3, a4; ret` (0x9ad70 / 0x9b2ac).
     That is `n ? *l - *r : 0` over unsigned chars, computed by a full 64-bit `sub` of two zero-extended bytes: a0 is
     w64 (c1 - c2) with -255 <= c1 - c2 <= 255, which is already the sign extension of the 32-bit int result.
   amemcmp_res states exactly that: either the n bytes are equal and a0 is the zero word, or k < n is the first index
   where they differ (equal before k) and a0 = w64 (c1 - c2) of the two bytes at k, c1 at x + k and c2 at y + k.

   WHY cgif's MEMCMP SHAPE AND NOT abcmp_realizes_x's (c-omx-alloc 2026-10-29, "SWITCH"): the bcmp walk calls
   __wrap_memcmp at sp0 - 2240 (A/AE2s.v:170 G2, :213) and fits the memcmp frame [sp0 - 2240 - ESTACK, sp0 - 2240)
   inside bcmp's [sp0 - 2 * ESTACK, sp0) (A/AE2s.v:241). The memcmp chain needs 2312 bytes (A/AE2z.v:37 MC_SCR), so
   ESTACK covers it. With abcmp_realizes_x's 2 * ESTACK premises and frame at the nested sp the frame would leave
   bcmp's window, and ly_stk_lo + 2 * ESTACK <= sp0 - 2240 does not follow from bcmp's premises. So the text is
   cgif's YG0d.v:337-352 amemcmp_realizes (= the amemcmp_realizes_cf field, YG0d2cf.v:60-75): an ESTACK frame and
   only ecall_pre_x's stack facts.

   1. THE TEXTS (Section mx):
      amemcmp_res          = the result clause above.
      amemcmp_realizes_x   = YG0d.v:337-352 amemcmp_realizes with ecall_pre -> ecall_pre_x segs B ARx, AR -> ARx, the
                             ghost set Hp threaded unchanged (as YGcallMx.v's texts), and the result clause
                             (v = w64 0 <-> ...) -> amemcmp_res W mem x y n v. No other change.
      amemcmp_realizes_xm  = amemcmp_realizes_x plus the keep (MN.memnorm segs mem -> MN.memnorm segs mem') as the
                             last post conjunct (as YGcallMxmn.v's abcmp_realizes_xm); _xm_forget gives _x back.
      amemcmp_res_zero_iff = the result clause gives the zero-iff-equal fact of the AR / bcmp texts.
      abcmp_of_memcmp_x    = amemcmp_realizes_x pc -> abcmp_realizes_x segs B ARx pc (YGcallMx.v:125): the bcmp-form
                             text at the same pc, by the window widening ESTACK -> 2 * ESTACK and amemcmp_res_zero_iff.
                             A walk that needs only zero-iff-equal at a memcmp call takes amemcmp_res_zero_iff.
   2. THE RULES (Section l), over ajournal_x (YCbqG.v):
      aj_memcmp_at_x       = cgif's YCbq.v:2019 aj_memcmp_at over ajournal_x, derived from it as YGcallMx.v:448
                             aj_bcmp_at_x is from YCbq.v:2062 aj_bcmp_at (the ecall_pre_x proved inline), with the
                             result clause amemcmp_res W memT x y n v;
      aj_memcmp_at_xm      = aj_memcmp_at_x plus the keep (MN.memnorm segs memT -> MN.memnorm segs mem2) as the last
                             conclusion conjunct: an IMPLICATION, no memnorm premise (as YGcallMxmn.v's aj_bcmp_at_xm).
   3. THE LIFTS (Section cj): amemcmp_realizes_x_conj / amemcmp_realizes_xm_conj take a text at ARx to ARx /\ P for
      any P on (ly, S), as YGcallMx.v's abcmp_realizes_x_conj / YGcallMxmn.v's abcmp_realizes_xm_conj.
   | call   | rule            | text                | keep | frame                |
   | memcmp | aj_memcmp_at_x  | amemcmp_realizes_x  | no   | ESTACK below the sp  |
   | memcmp | aj_memcmp_at_xm | amemcmp_realizes_xm | yes  | ESTACK below the sp  |
   A script checked that amemcmp_realizes_x differs from YG0d.v:337 amemcmp_realizes (and from YG0d2cf.v:60
   amemcmp_realizes_cf) only in AR -> ARx, the ghost Hp and the result clause; that aj_memcmp_at_x's statement differs
   from aj_bcmp_at_x's exactly as cgif's aj_memcmp_at's from aj_bcmp_at's (the two stack-window premises go, the
   window is ESTACK, the result clause is the text's); and that each _xm differs from its _x only in the keep, as the
   bcmp pair in YGcallMxmn.v does. The commit message that added this file has its output.

   WHY YAkMemnorm: as YGcallMxmn.v (its header): this file Requires neither YAjMemnorm, nor MemNorm.v, nor
   lib/Lib/Mem.v, so lib/Lib/LiaTwx2.v is not in its Require closure. It does not Require YGcallMxmn.v either.

   Numerals: 1, 3, 4, 10, 11, 12 are RISC-V register numbers (WORD); 0 is the zero word (WORD); 16 (stack alignment),
   8 (bits of a byte), 256 (byte modulus), 2 ^ 32, 2 ^ 63, 2 ^ 64 are LENGTH / DERIVED constants of cgif's texts; -1
   (the quotient of a negative difference by 2 ^ 64) is DERIVED; 4096 (= ESTACK, YG0d.v:19) is DERIVED. The addresses
   above are in this comment only. No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbq YCbqG FCiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcallMx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Module MN := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YAkMemnorm.

Section mx. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Local Abbreviation AJ := (ajournal_x (SK := SK) segs B PST ARx).

(* ---------------------------------------------------------------------------- *)
(* 1. The texts.                                                                  *)
(* What memcmp returns (header, MEASURED): the n bytes are equal and v is the zero word, or k < n is the first index
   where they differ and v is the difference of the two unsigned bytes at k, as a word (`sub a0, a3, a4`). *)
Definition amemcmp_res (W : world segs) (mem : word -> option byte) (x y n : Z) (v : word) : Prop :=
(v = w64 0 /\ forall i, 0 <= i < n -> aview segs (w_H W) mem (x + i) = aview segs (w_H W) mem (y + i)) \/
(exists k c1 c2, 0 <= k < n /\
(forall i, 0 <= i < k -> aview segs (w_H W) mem (x + i) = aview segs (w_H W) mem (y + i)) /\
aview segs (w_H W) mem (x + k) = Some c1 /\ aview segs (w_H W) mem (y + k) = Some c2 /\ c1 <> c2 /\
v = w64 (c1 - c2)).

(* the result gives the zero-iff-equal fact of cgif's memcmp / bcmp texts *)
Lemma amemcmp_res_zero_iff : forall W mem x y n v, amemcmp_res W mem x y n v ->
(v = w64 0 <-> forall i, 0 <= i < n -> aview segs (w_H W) mem (x + i) = aview segs (w_H W) mem (y + i)).
Proof.
intros W mem x y n v [[-> Heq] | (k & c1 & c2 & Hk & _ & E1 & E2 & Hne & ->)].
- split; [intros _; exact Heq | intros _; reflexivity].
- assert (Hb : forall a c, aview segs (w_H W) mem a = Some c -> 0 <= c < 256).
  { intros a c Hc. unfold aview in Hc. destruct (mbyte segs (mrestrict (w_H W) mem) a) as [b|]; [|discriminate].
    cbn in Hc. injection Hc as <-. pose proof (bv_unsigned_in_range 8 b) as Hr. unfold bv_modulus in Hr. cbn in Hr. zlia. }
  pose proof (Hb _ _ E1) as B1. pose proof (Hb _ _ E2) as B2.
  split.
  + intros H0. exfalso. apply (f_equal bv_unsigned) in H0. unfold w64 in H0. rewrite !Z_to_bv_unsigned in H0.
    unfold bv_wrap in H0. change (bv_modulus 64) with (2 ^ 64) in H0. rewrite Z.mod_0_l in H0 by zlia.
    destruct (Z_lt_le_dec (c1 - c2) 0) as [Hneg|Hpos].
    * rewrite <- (Z.mod_unique (c1 - c2) (2 ^ 64) (-1) (c1 - c2 + 2 ^ 64)) in H0 by zlia. zlia.
    * rewrite Z.mod_small in H0 by zlia. zlia.
  + intros Hall. exfalso. specialize (Hall k Hk). rewrite E1, E2 in Hall. injection Hall as Hc. exact (Hne Hc).
Qed.

(* cgif YG0d.v:337-352 amemcmp_realizes over ecall_pre_x; Hp unchanged through the call; the result clause is
   amemcmp_res (header). *)
Definition amemcmp_realizes_x (pc : Z) : Prop :=
forall ly S Hp W regs mem md x y n,
ecall_pre_x segs B ARx ly S Hp W regs mem md ->
getr regs 10 = w64 x -> getr regs 11 = w64 y -> getr regs 12 = w64 n -> 0 <= n < 2 ^ 32 ->
0 <= x -> x + n <= 2 ^ 63 -> 0 <= y -> y + n <= 2 ^ 63 ->
src_ok segs W regs mem x n -> src_ok segs W regs mem y n -> amem_range x n -> amem_range y n ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF x n -> (0 < n -> shadow_hull_vis (aview segs (w_H W) mem) x n) ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF y n -> (0 < n -> shadow_hull_vis (aview segs (w_H W) mem) y n) ->
SRr segs W (cfg_at segs pc regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md' (v : word),
c' = cfg_at segs (raZ regs) regs' mem' md' /\
ARx ly S Hp W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = v /\
amemcmp_res W mem x y n v /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - ESTACK <= a < spZ regs) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).

(* amemcmp_realizes_x, plus the keep *)
Definition amemcmp_realizes_xm (pc : Z) : Prop :=
forall ly S Hp W regs mem md x y n,
ecall_pre_x segs B ARx ly S Hp W regs mem md ->
getr regs 10 = w64 x -> getr regs 11 = w64 y -> getr regs 12 = w64 n -> 0 <= n < 2 ^ 32 ->
0 <= x -> x + n <= 2 ^ 63 -> 0 <= y -> y + n <= 2 ^ 63 ->
src_ok segs W regs mem x n -> src_ok segs W regs mem y n -> amem_range x n -> amem_range y n ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF x n -> (0 < n -> shadow_hull_vis (aview segs (w_H W) mem) x n) ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF y n -> (0 < n -> shadow_hull_vis (aview segs (w_H W) mem) y n) ->
SRr segs W (cfg_at segs pc regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md' (v : word),
c' = cfg_at segs (raZ regs) regs' mem' md' /\
ARx ly S Hp W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = v /\
amemcmp_res W mem x y n v /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - ESTACK <= a < spZ regs) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) /\
(MN.memnorm segs mem -> MN.memnorm segs mem')).

(* forgetting the keep gives the plain text *)
Lemma amemcmp_realizes_xm_forget : forall pc, amemcmp_realizes_xm pc -> amemcmp_realizes_x pc.
Proof.
intros pc AM ly S Hp W regs mem md x y n HPRE. intros.
eapply SRr_mono; [apply (AM ly S Hp W regs mem md x y n HPRE); assumption |].
cbv beta. intros W' c' _ (-> & regs' & mem' & md' & v & Hc & K1 & K2 & K3 & K4 & K5 & K6 & K7 & _).
split; [reflexivity|]. exists regs', mem', md', v.
exact (conj Hc (conj K1 (conj K2 (conj K3 (conj K4 (conj K5 (conj K6 K7))))))).
Qed.

(* the bcmp-form text at the same pc (YGcallMx.v:125): its window [sp - 2 * ESTACK, sp) contains the memcmp text's
   [sp - ESTACK, sp), its premises contain the memcmp text's, and the result gives zero-iff-equal. *)
Lemma abcmp_of_memcmp_x : forall pc, amemcmp_realizes_x pc -> abcmp_realizes_x segs B ARx pc.
Proof.
intros pc AM ly S Hp W regs mem md x y n HPRE Hlo2 Hpres2 Ha0 Ha1 Ha2 Hn Hx0 Hxn Hy0 Hyn Hsx Hsy Hbx Hby Hmx Hmy
Hrx Hhx Hry Hhy.
assert (ESTACK = 4096) as Hes by reflexivity.
eapply SRr_mono;
[exact (AM ly S Hp W regs mem md x y n HPRE Ha0 Ha1 Ha2 Hn Hx0 Hxn Hy0 Hyn Hsx Hsy Hmx Hmy Hrx Hhx Hry Hhy) |].
cbv beta. intros W' c' _ (-> & regs' & mem' & md' & v & Hc & HAR' & HP & Hsame & Hres & Hcmp & Hfr & Hpres').
split; [reflexivity|]. exists regs', mem', md', v.
split; [exact Hc|]. split; [exact HAR'|]. split; [exact HP|]. split; [exact Hsame|]. split; [exact Hres|].
split; [exact (amemcmp_res_zero_iff W mem x y n v Hcmp)|].
split; [|exact Hpres'].
intros a Ha Hna. apply (Hfr a Ha). intros H'. apply Hna. zlia.
Qed.

(* ---------------------------------------------------------------------------- *)
(* 2. The call-site rules.                                                        *)
Section l.
Context {HL : Z}.  (* AR_laws_x's head length (YCbqG.v), implicit: inferred from LAWS *)
Hypothesis LAWS : AR_laws_x segs B ARx HL.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.

(* aj_memcmp_at_x over a journal at a reflexive and transitive world relation R (the binders of every R rule; the
   call keeps the world, so the journal's world conjunct passes through unchanged and no law of R is read);
   aj_memcmp_at_x is its case R := wle *)
Lemma aj_memcmp_at_xR : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
(forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
forall pc, amemcmp_realizes_x pc ->
forall W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k x y n (o : Z) raw,
ajournal_xR (SK := SK) segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k ->
getr regsT 10 = w64 x -> getr regsT 11 = w64 y -> getr regsT 12 = w64 n -> 0 <= n < 2 ^ 32 ->
0 <= x -> x + n <= 2 ^ 63 -> 0 <= y -> y + n <= 2 ^ 63 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
src_ok segs W regsT memT x n -> src_ok segs W regsT memT y n -> amem_range x n -> amem_range y n ->
range_addressable (aview segs (w_H W) memT) SHADOW_OFF x n -> (0 < n -> shadow_hull_vis (aview segs (w_H W) memT) x n) ->
range_addressable (aview segs (w_H W) memT) SHADOW_OFF y n -> (0 < n -> shadow_hull_vis (aview segs (w_H W) memT) y n) ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2 (v : word),
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_xR (SK := SK) segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W mem2 md2 k /\
aregs_preserved regsT regs2 /\ getr regs2 10 = v /\
amemcmp_res W memT x y n v /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - ESTACK <= a < sp0 + o) -> aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
(forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
intros R R_refl R_trans pc AM W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k x y n o raw
HJ Ha0 Ha1 Ha2 Hn Hx0 Hxn Hy0 Hyn Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hsx Hsy Hmx Hmy Hrx Hhx Hry Hhy.
pose proof (ajxR_ar HJ) as HAR. pose proof (ajxR_ly HJ) as Hly. pose proof (ajxR_secs HJ) as Hsecs. pose proof (ajxR_rel HJ) as Hwle. pose proof (ajxR_io HJ) as Hio. pose proof (ajxR_frs HJ) as Hfrs. pose proof (ajxR_nev HJ) as Hnev. pose proof (ajxR_k HJ) as Hk. pose proof (ajxR_pres HJ) as Hpres. pose proof (ajxR_stk HJ) as Hstatic. pose proof (ajxR_extra HJ) as F5. pose proof (ajxR_qt HJ) as HQT.
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (ESTACK = 4096) as Hes by reflexivity.
(* the call's ecall_pre_x, as cgif's ecall_pre_at (YCbq.v:1913) *)
assert (HPRE : ecall_pre_x segs B ARx lyc Sc Hpc W regsT memT mdc).
{ split; [exact HAR|]. split; [rewrite Hra; exact Hraw|].
split; [rewrite Hsp', Z.add_mod, Hal16, Hal by zlia; reflexivity|].
split; [rewrite Eslo, Hsp'; zlia|]. split; [rewrite Eshi, Hsp'; zlia|].
split; [intros a Ha; apply Hpres; rewrite Hsp' in Ha; zlia|]. split; [exact Hgp | exact Htp]. }
eapply SRr_mono.
{ exact (AM lyc Sc Hpc W regsT memT mdc x y n HPRE Ha0 Ha1 Ha2 Hn Hx0 Hxn Hy0 Hyn Hsx Hsy Hmx Hmy Hrx Hhx Hry Hhy). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HAR2 & HP & Hsame & Hres & Hcmp & Hfr & Hpres2).
rewrite Hsp' in Hfr.
split; [reflexivity|]. exists regs2, mem2, md2, v.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (ajournal_x_after_writeR (SK := SK) segs B PST ARx LAWS segs_low R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k mem2 md2
(fun a => sp0 + o - ESTACK <= a < sp0 + o) Sc Hpc own HJ).
- intros a Ha Hna. apply (Hfr a Ha). exact Hna.
- exact Hpres2.
- exact Hsame.
- intros a Ha; left; left; zlia.
- exact HAR2.
- reflexivity. - reflexivity. - zlia. - exact Hfrs. - exact HQT. - reflexivity. }
split; [exact HP|]. split; [exact Hres|]. split; [exact Hcmp|]. split; [exact Hfr | exact Hpres2].
Qed.

(* cgif YCbq.v:2019 aj_memcmp_at over ajournal_x: a call of memcmp through its text. *)
Lemma aj_memcmp_at_x : forall pc, amemcmp_realizes_x pc ->
forall W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k x y n (o : Z) raw,
AJ STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k ->
getr regsT 10 = w64 x -> getr regsT 11 = w64 y -> getr regsT 12 = w64 n -> 0 <= n < 2 ^ 32 ->
0 <= x -> x + n <= 2 ^ 63 -> 0 <= y -> y + n <= 2 ^ 63 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
src_ok segs W regsT memT x n -> src_ok segs W regsT memT y n -> amem_range x n -> amem_range y n ->
range_addressable (aview segs (w_H W) memT) SHADOW_OFF x n -> (0 < n -> shadow_hull_vis (aview segs (w_H W) memT) x n) ->
range_addressable (aview segs (w_H W) memT) SHADOW_OFF y n -> (0 < n -> shadow_hull_vis (aview segs (w_H W) memT) y n) ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2 (v : word),
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
AJ STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W mem2 md2 k /\
aregs_preserved regsT regs2 /\ getr regs2 10 = v /\
amemcmp_res W memT x y n v /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - ESTACK <= a < sp0 + o) -> aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
(forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof. exact (aj_memcmp_at_xR (@wle segs) (wle_refl segs) (wle_trans segs)). Qed.

(* aj_memcmp_at_xm over a journal at a reflexive and transitive world relation R (the binders of every R rule; the
   call keeps the world, so the journal's world conjunct passes through unchanged and no law of R is read);
   aj_memcmp_at_xm is its case R := wle *)
Lemma aj_memcmp_at_xmR : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
(forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
forall pc, amemcmp_realizes_xm pc ->
forall W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k x y n (o : Z) raw,
ajournal_xR (SK := SK) segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k ->
getr regsT 10 = w64 x -> getr regsT 11 = w64 y -> getr regsT 12 = w64 n -> 0 <= n < 2 ^ 32 ->
0 <= x -> x + n <= 2 ^ 63 -> 0 <= y -> y + n <= 2 ^ 63 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
src_ok segs W regsT memT x n -> src_ok segs W regsT memT y n -> amem_range x n -> amem_range y n ->
range_addressable (aview segs (w_H W) memT) SHADOW_OFF x n -> (0 < n -> shadow_hull_vis (aview segs (w_H W) memT) x n) ->
range_addressable (aview segs (w_H W) memT) SHADOW_OFF y n -> (0 < n -> shadow_hull_vis (aview segs (w_H W) memT) y n) ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2 (v : word),
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_xR (SK := SK) segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W mem2 md2 k /\
aregs_preserved regsT regs2 /\ getr regs2 10 = v /\
amemcmp_res W memT x y n v /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - ESTACK <= a < sp0 + o) -> aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
(forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a) /\
(MN.memnorm segs memT -> MN.memnorm segs mem2)).
Proof.
intros R R_refl R_trans pc AM W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k x y n o raw
HJ Ha0 Ha1 Ha2 Hn Hx0 Hxn Hy0 Hyn Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hsx Hsy Hmx Hmy Hrx Hhx Hry Hhy.
pose proof (ajxR_ar HJ) as HAR. pose proof (ajxR_ly HJ) as Hly. pose proof (ajxR_secs HJ) as Hsecs. pose proof (ajxR_rel HJ) as Hwle. pose proof (ajxR_io HJ) as Hio. pose proof (ajxR_frs HJ) as Hfrs. pose proof (ajxR_nev HJ) as Hnev. pose proof (ajxR_k HJ) as Hk. pose proof (ajxR_pres HJ) as Hpres. pose proof (ajxR_stk HJ) as Hstatic. pose proof (ajxR_extra HJ) as F5. pose proof (ajxR_qt HJ) as HQT.
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (ESTACK = 4096) as Hes by reflexivity.
(* the call's ecall_pre_x, as cgif's ecall_pre_at (YCbq.v:1913) *)
assert (HPRE : ecall_pre_x segs B ARx lyc Sc Hpc W regsT memT mdc).
{ split; [exact HAR|]. split; [rewrite Hra; exact Hraw|].
split; [rewrite Hsp', Z.add_mod, Hal16, Hal by zlia; reflexivity|].
split; [rewrite Eslo, Hsp'; zlia|]. split; [rewrite Eshi, Hsp'; zlia|].
split; [intros a Ha; apply Hpres; rewrite Hsp' in Ha; zlia|]. split; [exact Hgp | exact Htp]. }
eapply SRr_mono.
{ exact (AM lyc Sc Hpc W regsT memT mdc x y n HPRE Ha0 Ha1 Ha2 Hn Hx0 Hxn Hy0 Hyn Hsx Hsy Hmx Hmy Hrx Hhx Hry Hhy). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HAR2 & HP & Hsame & Hres & Hcmp & Hfr & Hpres2 & Hmn).
rewrite Hsp' in Hfr.
split; [reflexivity|]. exists regs2, mem2, md2, v.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (ajournal_x_after_writeR (SK := SK) segs B PST ARx LAWS segs_low R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k mem2 md2
(fun a => sp0 + o - ESTACK <= a < sp0 + o) Sc Hpc own HJ).
- intros a Ha Hna. apply (Hfr a Ha). exact Hna.
- exact Hpres2.
- exact Hsame.
- intros a Ha; left; left; zlia.
- exact HAR2.
- reflexivity. - reflexivity. - zlia. - exact Hfrs. - exact HQT. - reflexivity. }
split; [exact HP|]. split; [exact Hres|]. split; [exact Hcmp|]. split; [exact Hfr|].
split; [exact Hpres2 | exact Hmn].
Qed.

(* aj_memcmp_at_x, plus the keep (an implication in the conclusion) *)
Lemma aj_memcmp_at_xm : forall pc, amemcmp_realizes_xm pc ->
forall W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k x y n (o : Z) raw,
AJ STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k ->
getr regsT 10 = w64 x -> getr regsT 11 = w64 y -> getr regsT 12 = w64 n -> 0 <= n < 2 ^ 32 ->
0 <= x -> x + n <= 2 ^ 63 -> 0 <= y -> y + n <= 2 ^ 63 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
src_ok segs W regsT memT x n -> src_ok segs W regsT memT y n -> amem_range x n -> amem_range y n ->
range_addressable (aview segs (w_H W) memT) SHADOW_OFF x n -> (0 < n -> shadow_hull_vis (aview segs (w_H W) memT) x n) ->
range_addressable (aview segs (w_H W) memT) SHADOW_OFF y n -> (0 < n -> shadow_hull_vis (aview segs (w_H W) memT) y n) ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2 (v : word),
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
AJ STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W mem2 md2 k /\
aregs_preserved regsT regs2 /\ getr regs2 10 = v /\
amemcmp_res W memT x y n v /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - ESTACK <= a < sp0 + o) -> aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
(forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a) /\
(MN.memnorm segs memT -> MN.memnorm segs mem2)).
Proof. exact (aj_memcmp_at_xmR (@wle segs) (wle_refl segs) (wle_trans segs)). Qed.
End l.
End mx.

(* ---------------------------------------------------------------------------- *)
(* 3. A text at ARx holds at ARx /\ P for any P on (ly, S) (YGcallMx.v Section cj, YGcallMxmn.v Section cj).     *)
Section cj. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable P : alayout -> astate -> Prop.
Local Abbreviation ARP := (fun ly S Hp W mem md => ARx ly S Hp W mem md /\ P ly S).

Lemma amemcmp_realizes_x_conj : forall pc, amemcmp_realizes_x segs B ARx pc -> amemcmp_realizes_x segs B ARP pc.
Proof.
intros pc AM ly S Hp W regs mem md x y n [[HAR HPl] Hrest]. intros.
eapply SRr_mono; [apply (AM ly S Hp W regs mem md x y n (conj HAR Hrest)); assumption |].
cbv beta. intros W' c' _ (-> & regs' & mem' & md' & v & Hc & HAR' & Hrest').
split; [reflexivity|]. exists regs', mem', md', v. split; [exact Hc|]. split; [split; [exact HAR' | exact HPl] | exact Hrest'].
Qed.

Lemma amemcmp_realizes_xm_conj : forall pc, amemcmp_realizes_xm segs B ARx pc -> amemcmp_realizes_xm segs B ARP pc.
Proof.
intros pc AM ly S Hp W regs mem md x y n [[HAR HPl] Hrest]. intros.
eapply SRr_mono; [apply (AM ly S Hp W regs mem md x y n (conj HAR Hrest)); assumption |].
cbv beta. intros W' c' _ (-> & regs' & mem' & md' & v & Hc & HAR' & Hrest').
split; [reflexivity|]. exists regs', mem', md', v. split; [exact Hc|]. split; [split; [exact HAR' | exact HPl] | exact Hrest'].
Qed.
End cj.
