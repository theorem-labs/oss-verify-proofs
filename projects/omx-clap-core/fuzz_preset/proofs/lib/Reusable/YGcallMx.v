(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-30 (the world relation R): awr_byte_present_xR is awr_byte_present_x over a
   journal at any world relation R (YCbqG.ajournal_xR; the world conjunct is not read); awr_byte_present_x keeps its
   statement and is the instance at wle. aj_intrin_at_xR, aj_intrin_at_x_frR, aj_strlen_at_xR, aj_bcmp_at_xR and
   aj_strcmp_at_xR are the call rules over a journal at a reflexive and transitive R (binders first; each call keeps
   the world, so no law of R is read); the old names keep their statements and are the instances at wle. *)
(* Theorem Labs, 2026-10: the memcpy / memset, strlen, bcmp and strcmp CALL-SITE RULES, GENERIC over the allocator
   invariant ARx of YCbqG.v (Section Variables segs B PST ARx). No allocator instance, no image class, no address and
   no ledger is named here.

   1. THE TEXTS (over FCiface.v's ecall_pre_x, the one definition (frame-class lane, frozen): YG0d.v:278-284 ecall_pre
      with AR segs B -> ARx, = YG0dcf.v:64 ecall_pre_cf at ARx := ARcf):
      aintrin_realizes_x  = cgif's YG0d.v:318-336 aintrin_realizes with AR segs B -> ARx and the ghost set Hp threaded
                            unchanged (Hp right after the state, as in YG0dcf.v). dest_ok, src_ok, amem_range,
                            shadow_hull_vis, first_byte, rom_view, cfg_at are reused as they stand (they name no AR).
      astrlen_realizes_x  = a marked STAND-IN for c-libc-stdio's strlen row: YG0dcf.v:140-159 astrnlen_realizes_cf
                            without the bound n (no a1 premise, no `k + 8 <= n`), the string NUL-terminated at x + k
                            (first_byte at n := k + 1), the 2 * ESTACK window, a0 = k at the return.
      abcmp_realizes_x    = cgif's YG0d.v:353-372 abcmp_realizes, the same substitution.
      astrcmp_realizes_x  = a marked STAND-IN for c-libc-stdio's strcmp row: astrlen_realizes_x's premises once per
                            string (a0, a1), the 2 * ESTACK window, a0 = 0 at the return exactly when the strings are
                            equal.
   2. THE RULES (Section l): over ajournal_x (YCbqG.v), ported from cgif's released lib/YCbq.v
      (proofs/cgif/cgif_file_fuzzer/lib/YCbq.v):
      awr_byte_present_x  = YCbq.v:1927 awr_byte_present,
      aj_intrin_at_x      = YCbq.v:1955 aj_intrin_at,
      aj_strlen_at_x      = YCbq.v:2062 aj_bcmp_at's shape (2 * ESTACK window, one string) at astrlen_realizes_x,
      aj_bcmp_at_x        = YCbq.v:2062 aj_bcmp_at,
      aj_strcmp_at_x      = aj_bcmp_at's shape at astrcmp_realizes_x (two strings).
      The ecall_pre_x of a call is proved inline from the journal as YCbq.v:1913 ecall_pre_at proves cgif's.
      Each rule keeps the caller's journal at the call's state (ly, S, Hp, W unchanged; the runtime writes only the
      destination and its own stack window) and returns the register and memory facts of the text.

   Numerals: 1, 3, 4, 10, 11, 12 are RISC-V register numbers (WORD); 0 is the NUL byte (WORD); 16 (stack alignment),
   8 (shadow granule), 2 (the factor of the 2 * ESTACK window), 256 (byte modulus), 2 ^ 32, 2 ^ 63, 2 ^ 64 are
   LENGTH / DERIVED constants of cgif's texts; 4096 (= ESTACK, YG0d.v:19) is DERIVED. No ADDRESS. *)
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
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* membership in a footprint, and the caller-frame write set of YCbqG.v, are decidable *)
Lemma inFP_dec_fr : forall (FP : list (Z * Z)) (a : Z), {inFP FP a} + {~ inFP FP a}.
Proof.
intros FP a. destruct (Exists_dec (fun r : Z * Z => fst r <= a < snd r) FP) as [H|H].
- intros r. destruct (Z_le_dec (fst r) a); [destruct (Z_lt_dec a (snd r))|]; [left; lia | right; lia | right; lia].
- left. apply Exists_exists in H. exact H.
- right. intros Hf. apply H. apply Exists_exists. exact Hf.
Qed.

Section mx. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Local Abbreviation AJ := (ajournal_x (SK := SK) segs B PST ARx).

(* ---------------------------------------------------------------------------- *)
(* 1. The texts.                                                                  *)
(* STAND-IN DEFINITION for c-libc-stdio's amem_range8 (lib/Reusable/YGcfStr.v, origin/cold/c-libc-stdio-presetstr
   3e37c5476fed), copied from it verbatim; swap by citation when that file lands in the worktree. It is the walks'
   own region_in_mem: 8 bytes of application memory past the bytes read, and in high memory a start at or above
   kHighMemBeg + 15. Both string kits' shadow check needs it, and no ARx field excludes a string that ends in the
   last 8 bytes of a range. Numerals: 8 and 15 are LENGTH slack of that check; 1 is DERIVED. *)
Definition amem_range8 (p n : Z) : Prop :=
p + n + 8 <= kLowMemEnd - 1 \/ (kHighMemBeg + 15 <= p /\ p + n + 8 <= kHighMemEnd - 1).

(* cgif YG0d.v:318-336 over ecall_pre_x; Hp unchanged through the call. *)
Definition aintrin_realizes_x (op : memop) (pc : Z) : Prop :=
forall ly S Hp W regs mem md d x n,
ecall_pre_x segs B ARx ly S Hp W regs mem md ->
getr regs 10 = w64 d -> getr regs 11 = w64 x -> getr regs 12 = w64 n -> 0 <= n < 2 ^ 32 -> 0 <= d -> d + n <= 2 ^ 63 ->
dest_ok segs B ly S W regs mem d n -> amem_range d n ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF d n -> (0 < n -> shadow_hull_vis (aview segs (w_H W) mem) d n) ->
(match op with
| OCpy => 0 <= x /\ x + n <= 2 ^ 63 /\ src_ok segs W regs mem x n /\ (d + n <= x \/ x + n <= d) /\ amem_range x n /\
range_addressable (aview segs (w_H W) mem) SHADOW_OFF x n /\ (0 < n -> shadow_hull_vis (aview segs (w_H W) mem) x n)
| OSet => True end) ->
SRr segs W (cfg_at segs pc regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
ARx ly S Hp W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 d /\
(forall i, 0 <= i < n -> aview segs (w_H W) mem' (d + i) =
match op with OCpy => aview segs (w_H W) mem (x + i) | OSet => Some (x mod 256) end) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (spZ regs - ESTACK <= a < spZ regs) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).

(* STAND-IN for c-libc-stdio's strlen row (the strlen text over ecall_pre_x): swap by citation.
   YG0dcf.v:140-159 astrnlen_realizes_cf without the bound n; the string is NUL-terminated at x + k. *)
Definition astrlen_realizes_x (pc : Z) : Prop :=
forall ly S Hp W regs mem md x k,
ecall_pre_x segs B ARx ly S Hp W regs mem md ->
ly_stk_lo ly + 2 * ESTACK <= spZ regs -> (forall a, spZ regs - 2 * ESTACK <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 10 = w64 x -> 0 < x ->
0 <= k -> k + 1 < 2 ^ 32 -> x + k + 1 <= 2 ^ 63 ->
first_byte segs W mem x (k + 1) 0 k ->
src_ok segs W regs mem x (k + 1) -> (forall a, x <= a <= x + k -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) ->
amem_range8 x (k + 1) ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF x (k + 1) ->
shadow_hull_vis (aview segs (w_H W) mem) x (k + 1) ->
(forall a, x + k < a < x + k - (x + k) mod 8 + 8 -> aview segs (w_H W) mem a <> None) ->
rom_view segs W mem ->
SRr segs W (cfg_at segs pc regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at segs (raZ regs) regs' mem' md' /\
ARx ly S Hp W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 k /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).

(* cgif YG0d.v:353-372 abcmp_realizes over ecall_pre_x; Hp unchanged through the call. *)
Definition abcmp_realizes_x (pc : Z) : Prop :=
forall ly S Hp W regs mem md x y n,
ecall_pre_x segs B ARx ly S Hp W regs mem md ->
ly_stk_lo ly + 2 * ESTACK <= spZ regs -> (forall a, spZ regs - 2 * ESTACK <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 10 = w64 x -> getr regs 11 = w64 y -> getr regs 12 = w64 n -> 0 <= n < 2 ^ 32 ->
0 <= x -> x + n <= 2 ^ 63 -> 0 <= y -> y + n <= 2 ^ 63 ->
src_ok segs W regs mem x n -> src_ok segs W regs mem y n ->
(forall a, x <= a < x + n -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) ->
(forall a, y <= a < y + n -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) ->
amem_range x n -> amem_range y n ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF x n -> (0 < n -> shadow_hull_vis (aview segs (w_H W) mem) x n) ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF y n -> (0 < n -> shadow_hull_vis (aview segs (w_H W) mem) y n) ->
SRr segs W (cfg_at segs pc regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md' (v : word),
c' = cfg_at segs (raZ regs) regs' mem' md' /\
ARx ly S Hp W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = v /\
(v = w64 0 <-> forall i, 0 <= i < n -> aview segs (w_H W) mem (x + i) = aview segs (w_H W) mem (y + i)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).

(* STAND-IN for c-libc-stdio's strcmp row (the strcmp text over ecall_pre_x): swap by citation.
   astrlen_realizes_x's premises once per string (a0 = x NUL-terminated at x + kx, a1 = y NUL-terminated at
   y + ky), the 2 * ESTACK window; at the return a0 = 0 exactly when the two strings are equal. *)
Definition astrcmp_realizes_x (pc : Z) : Prop :=
forall ly S Hp W regs mem md x y kx ky,
ecall_pre_x segs B ARx ly S Hp W regs mem md ->
ly_stk_lo ly + 2 * ESTACK <= spZ regs -> (forall a, spZ regs - 2 * ESTACK <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 10 = w64 x -> getr regs 11 = w64 y -> 0 < x -> 0 < y ->
0 <= kx -> kx + 1 < 2 ^ 32 -> x + kx + 1 <= 2 ^ 63 ->
0 <= ky -> ky + 1 < 2 ^ 32 -> y + ky + 1 <= 2 ^ 63 ->
first_byte segs W mem x (kx + 1) 0 kx -> first_byte segs W mem y (ky + 1) 0 ky ->
src_ok segs W regs mem x (kx + 1) -> src_ok segs W regs mem y (ky + 1) ->
(forall a, x <= a <= x + kx -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) ->
(forall a, y <= a <= y + ky -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) ->
amem_range8 x (kx + 1) -> amem_range8 y (ky + 1) ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF x (kx + 1) -> shadow_hull_vis (aview segs (w_H W) mem) x (kx + 1) ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF y (ky + 1) -> shadow_hull_vis (aview segs (w_H W) mem) y (ky + 1) ->
(forall a, x + kx < a < x + kx - (x + kx) mod 8 + 8 -> aview segs (w_H W) mem a <> None) ->
(forall a, y + ky < a < y + ky - (y + ky) mod 8 + 8 -> aview segs (w_H W) mem a <> None) ->
rom_view segs W mem ->
SRr segs W (cfg_at segs pc regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md' (v : word),
c' = cfg_at segs (raZ regs) regs' mem' md' /\
ARx ly S Hp W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = v /\
(v = w64 0 <-> kx = ky /\ forall i, 0 <= i < kx -> aview segs (w_H W) mem (x + i) = aview segs (w_H W) mem (y + i)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).

(* ---------------------------------------------------------------------------- *)
(* 2. The call-site rules.                                                        *)
Lemma wr_fp_frame_dec : forall FP S lyc a, {wr_fp_frame FP S lyc a} + {~ wr_fp_frame FP S lyc a}.
Proof.
intros FP S lyc a. destruct (inFP_dec_fr FP a) as [Hf|Hf]; [|right; intros (H & _); exact (Hf H)].
destruct (Exists_dec (fun f : Z * Z => in_zr a (frame_rng lyc f)) (frames S)) as [H|H].
- intros f. unfold in_zr. destruct (Z_le_dec (fst (frame_rng lyc f)) a);
  [destruct (Z_lt_dec a (fst (frame_rng lyc f) + snd (frame_rng lyc f)))|]; [left; lia | right; lia | right; lia].
- left. split; [exact Hf|]. apply Exists_exists in H. destruct H as ([cid pos] & Hin & Hr). exists cid, pos. auto.
- right. intros (_ & cid & pos & Hin & Hr). apply H. apply Exists_exists. exists (cid, pos). auto.
Qed.

Section l.
Context {HL : Z}.  (* AR_laws_x's head length (YCbqG.v), implicit: inferred from LAWS *)
Hypothesis LAWS : AR_laws_x segs B ARx HL.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.

(* YCbqG.v field 21 (alx_blocks_hi) with field 1: every sub-range of a live block is amem_range8, the strcmp rule's
   premise (low arm: the block ends at or below kLowShadowBeg; high arm: it starts at least 16 above kHighMemBeg and
   ends at or below alloc_ceiling) *)
Lemma blocks_range8_x : forall ly S Hp W mem md p n x m,
ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> p <= x -> 0 <= m -> x + m <= p + req_size n ->
amem_range8 x m.
Proof.
intros ly S Hp W mem md p n x m HAR Hin H1 H2 H3.
destruct (alx_blocks segs B ARx LAWS ly S Hp W mem md p n HAR Hin) as (_ & _ & Hc & Ha & _).
pose proof (alx_blocks_hi segs B ARx LAWS ly S Hp W mem md p n HAR Hin) as Hhi.
pose proof (@YM05.alloc_ceiling_value rc) as [CR _].
unfold amem_range8.
destruct Ha as [_ [Lo | [Hi _]]].
- left. unfold kLowShadowBeg, kLowMemEnd in *. lia.
- right. specialize (Hhi Hi). unfold kHighMemBeg, kHighMemEnd in *. lia.
Qed.

(* cgif YCbq.v:1927 awr_byte_present, over a journal at any world relation R (the world conjunct is not read) *)
Lemma awr_byte_present_xR : forall (R : world segs -> world segs -> Prop)
STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc Wc memc mdc k a,
ajournal_xR (SK := SK) segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc Wc memc mdc k ->
awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a ->
apresent (w_H Wc) memc a /\ ~ aowned B lyc Sc a.
Proof.
intros R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc Wc memc mdc k a HJ Hw.
pose proof (ajxR_ar HJ) as HAR. pose proof (ajxR_frs HJ) as Hfrs. pose proof (ajxR_pres HJ) as Hpres.
split; [|exact (proj1 (awr_byte_cases_xR (SK := SK) segs B PST ARx LAWS R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc Wc
  memc mdc k a HJ Hw))].
destruct Hw as [Hs | [(_ & b & n & Hin & Hr) | [(b & n & Hin & _ & Hr) | (cid & pos & Hin & Hr)]]].
- apply Hpres. exact Hs.
- exact (proj1 (proj1 (proj2 (proj2 (proj2 (proj2 (alx_blocks segs B ARx LAWS lyc Sc Hpc Wc memc mdc b n HAR Hin))))) a Hr)).
- exact (proj1 (proj1 (proj2 (proj2 (proj2 (proj2 (alx_blocks segs B ARx LAWS lyc Sc Hpc Wc memc mdc b n HAR Hin))))) a Hr)).
- assert (Hin' : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hin).
destruct (alx_frames segs B ARx LAWS lyc Sc Hpc Wc memc mdc cid pos HAR Hin') as (_ & _ & Hb & Hsh).
destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [exact (proj1 (Hb a Hr))|].
specialize (Hsh (a - shadow_addr (frame_addr lyc cid pos)) ltac:(zlia)).
replace (shadow_addr (frame_addr lyc cid pos) + (a - shadow_addr (frame_addr lyc cid pos))) with a in Hsh by zlia. exact (proj1 Hsh).
Qed.

(* cgif YCbq.v:1927 awr_byte_present *)
Lemma awr_byte_present_x : forall STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc Wc memc mdc k a,
AJ STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc Wc memc mdc k ->
awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a ->
apresent (w_H Wc) memc a /\ ~ aowned B lyc Sc a.
Proof. exact (awr_byte_present_xR (@wle segs)). Qed.

(* aj_intrin_at_x over a journal at a reflexive and transitive world relation R (the binders of every R rule; the
   call keeps the world, so the journal's world conjunct passes through unchanged and no law of R is read);
   aj_intrin_at_x is its case R := wle *)
Lemma aj_intrin_at_xR : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
(forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
forall op pc, aintrin_realizes_x op pc ->
forall W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k d x n (o : Z) raw,
ajournal_xR (SK := SK) segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k ->
getr regsT 10 = w64 d -> getr regsT 11 = w64 x -> getr regsT 12 = w64 n -> 0 <= n < 2 ^ 32 -> 0 <= d -> d + n <= 2 ^ 63 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
(forall a, d <= a < d + n -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ ~ (sp0 + o - ESTACK <= a < sp0 + o)) ->
amem_range d n ->
range_addressable (aview segs (w_H W) memT) SHADOW_OFF d n ->
(0 < n -> shadow_hull_vis (aview segs (w_H W) memT) d n) ->
(match op with
| OCpy => 0 <= x /\ x + n <= 2 ^ 63 /\ src_ok segs W regsT memT x n /\ (d + n <= x \/ x + n <= d) /\ amem_range x n /\
range_addressable (aview segs (w_H W) memT) SHADOW_OFF x n /\ (0 < n -> shadow_hull_vis (aview segs (w_H W) memT) x n)
| OSet => True end) ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_xR (SK := SK) segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W mem2 md2 k /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 d /\
(forall i, 0 <= i < n -> aview segs (w_H W) mem2 (d + i) =
match op with OCpy => aview segs (w_H W) memT (x + i) | OSet => Some (x mod 256) end) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (sp0 + o - ESTACK <= a < sp0 + o) -> aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
(forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
intros R R_refl R_trans op pc AI W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k d x n o raw
HJ Ha0 Ha1 Ha2 Hn Hd0 Hdn Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hdest Hamr Hra_d Hhull Hsrc.
pose proof (ajxR_ar HJ) as HAR. pose proof (ajxR_ly HJ) as Hly. pose proof (ajxR_secs HJ) as Hsecs. pose proof (ajxR_rel HJ) as Hwle. pose proof (ajxR_io HJ) as Hio. pose proof (ajxR_frs HJ) as Hfrs. pose proof (ajxR_nev HJ) as Hnev. pose proof (ajxR_k HJ) as Hk. pose proof (ajxR_pres HJ) as Hpres. pose proof (ajxR_stk HJ) as Hstatic. pose proof (ajxR_extra HJ) as F5. pose proof (ajxR_qt HJ) as HQT.
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
(* the call's ecall_pre_x, as cgif's ecall_pre_at (YCbq.v:1913) *)
assert (HPRE : ecall_pre_x segs B ARx lyc Sc Hpc W regsT memT mdc).
{ split; [exact HAR|]. split; [rewrite Hra; exact Hraw|].
split; [rewrite Hsp', Z.add_mod, Hal16, Hal by zlia; reflexivity|].
split; [rewrite Eslo, Hsp'; zlia|]. split; [rewrite Eshi, Hsp'; zlia|].
split; [intros a Ha; apply Hpres; rewrite Hsp' in Ha; zlia|]. split; [exact Hgp | exact Htp]. }
assert (HDEST : dest_ok segs B lyc Sc W regsT memT d n).
{ intros a Ha. destruct (Hdest a Ha) as [Hw Hns].
destruct (awr_byte_present_xR R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k a HJ Hw) as [Hpa Hno]. rewrite Hsp'.
split; [apply apresent_writable; exact Hpa | auto]. }
eapply SRr_mono.
{ exact (AI lyc Sc Hpc W regsT memT mdc d x n HPRE Ha0 Ha1 Ha2 Hn Hd0 Hdn HDEST Hamr Hra_d Hhull Hsrc). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hres & Heff & Hfr & Hpres2).
rewrite Hsp' in Hfr.
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (ajournal_x_after_writeR (SK := SK) segs B PST ARx LAWS segs_low R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k mem2 md2
(fun a => (d <= a < d + n) \/ (sp0 + o - ESTACK <= a < sp0 + o)) Sc Hpc own HJ).
- intros a Ha Hna. apply (Hfr a Ha); intros H'; apply Hna; [left | right]; exact H'.
- exact Hpres2.
- exact Hsame.
- intros a [Ha | Ha]; left; [exact (proj1 (Hdest a Ha)) | left; zlia].
- exact HAR2.
- reflexivity. - reflexivity. - zlia. - exact Hfrs. - exact HQT. - reflexivity. }
split; [exact HP|]. split; [exact Hres|]. split; [exact Heff|]. split; [exact Hfr | exact Hpres2].
Qed.

(* cgif YCbq.v:1955 aj_intrin_at: a call of __asan_memcpy (OCpy) / __asan_memset (OSet) through its text. *)
Lemma aj_intrin_at_x : forall op pc, aintrin_realizes_x op pc ->
forall W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k d x n (o : Z) raw,
AJ STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k ->
getr regsT 10 = w64 d -> getr regsT 11 = w64 x -> getr regsT 12 = w64 n -> 0 <= n < 2 ^ 32 -> 0 <= d -> d + n <= 2 ^ 63 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
(forall a, d <= a < d + n -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ ~ (sp0 + o - ESTACK <= a < sp0 + o)) ->
amem_range d n ->
range_addressable (aview segs (w_H W) memT) SHADOW_OFF d n ->
(0 < n -> shadow_hull_vis (aview segs (w_H W) memT) d n) ->
(match op with
| OCpy => 0 <= x /\ x + n <= 2 ^ 63 /\ src_ok segs W regsT memT x n /\ (d + n <= x \/ x + n <= d) /\ amem_range x n /\
range_addressable (aview segs (w_H W) memT) SHADOW_OFF x n /\ (0 < n -> shadow_hull_vis (aview segs (w_H W) memT) x n)
| OSet => True end) ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
AJ STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W mem2 md2 k /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 d /\
(forall i, 0 <= i < n -> aview segs (w_H W) mem2 (d + i) =
match op with OCpy => aview segs (w_H W) memT (x + i) | OSet => Some (x mod 256) end) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (sp0 + o - ESTACK <= a < sp0 + o) -> aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
(forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof. exact (aj_intrin_at_xR (@wle segs) (wle_refl segs) (wle_trans segs)). Qed.

(* aj_intrin_at_x_fr over a journal at a reflexive and transitive world relation R (the binders of every R rule; the
   call keeps the world, so the journal's world conjunct passes through unchanged and no law of R is read);
   aj_intrin_at_x_fr is its case R := wle *)
Lemma aj_intrin_at_x_frR : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
(forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
forall op pc, aintrin_realizes_x op pc ->
forall W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k d x n (o : Z) raw,
ajournal_xR (SK := SK) segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k ->
getr regsT 10 = w64 d -> getr regsT 11 = w64 x -> getr regsT 12 = w64 n -> 0 <= n < 2 ^ 32 -> 0 <= d -> d + n <= 2 ^ 63 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
(forall a, d <= a < d + n ->
   (awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a \/ wr_fp_frame FP S lyc a) /\
   ~ (sp0 + o - ESTACK <= a < sp0 + o)) ->
amem_range d n ->
range_addressable (aview segs (w_H W) memT) SHADOW_OFF d n ->
(0 < n -> shadow_hull_vis (aview segs (w_H W) memT) d n) ->
(match op with
| OCpy => 0 <= x /\ x + n <= 2 ^ 63 /\ src_ok segs W regsT memT x n /\ (d + n <= x \/ x + n <= d) /\ amem_range x n /\
range_addressable (aview segs (w_H W) memT) SHADOW_OFF x n /\ (0 < n -> shadow_hull_vis (aview segs (w_H W) memT) x n)
| OSet => True end) ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_xR (SK := SK) segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W mem2 md2 k /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 d /\
(forall i, 0 <= i < n -> aview segs (w_H W) mem2 (d + i) =
match op with OCpy => aview segs (w_H W) memT (x + i) | OSet => Some (x mod 256) end) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (sp0 + o - ESTACK <= a < sp0 + o) -> aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
(forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
intros R R_refl R_trans op pc AI W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k d x n o raw
HJ Ha0 Ha1 Ha2 Hn Hd0 Hdn Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hdest Hamr Hra_d Hhull Hsrc.
pose proof (ajxR_ar HJ) as HAR. pose proof (ajxR_ly HJ) as Hly. pose proof (ajxR_secs HJ) as Hsecs. pose proof (ajxR_rel HJ) as Hwle. pose proof (ajxR_io HJ) as Hio. pose proof (ajxR_frs HJ) as Hfrs. pose proof (ajxR_nev HJ) as Hnev. pose proof (ajxR_k HJ) as Hk. pose proof (ajxR_pres HJ) as Hpres. pose proof (ajxR_stk HJ) as Hstatic. pose proof (ajxR_extra HJ) as F5. pose proof (ajxR_qt HJ) as HQT.
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
(* a caller-frame byte the footprint names is present and not owned at the call (the frames law at the call's state) *)
assert (HFR : forall a, wr_fp_frame FP S lyc a -> apresent (w_H W) memT a /\ ~ aowned B lyc Sc a).
{ intros a (_ & cid & pos & Hin & Hr).
  assert (Hin' : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; right; exact Hin).
  destruct (alx_frames segs B ARx LAWS lyc Sc Hpc W memT mdc cid pos HAR Hin') as (_ & _ & Hb & _).
  unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr. exact (Hb a Hr). }
(* the call's ecall_pre_x, as cgif's ecall_pre_at (YCbq.v:1913) *)
assert (HPRE : ecall_pre_x segs B ARx lyc Sc Hpc W regsT memT mdc).
{ split; [exact HAR|]. split; [rewrite Hra; exact Hraw|].
split; [rewrite Hsp', Z.add_mod, Hal16, Hal by zlia; reflexivity|].
split; [rewrite Eslo, Hsp'; zlia|]. split; [rewrite Eshi, Hsp'; zlia|].
split; [intros a Ha; apply Hpres; rewrite Hsp' in Ha; zlia|]. split; [exact Hgp | exact Htp]. }
assert (HDEST : dest_ok segs B lyc Sc W regsT memT d n).
{ intros a Ha. destruct (Hdest a Ha) as [Hw Hns]. rewrite Hsp'.
destruct Hw as [Hw | Hw].
- destruct (awr_byte_present_xR R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k a HJ Hw)
    as [Hpa Hno].
  split; [apply apresent_writable; exact Hpa | auto].
- destruct (HFR a Hw) as [Hpa Hno]. split; [apply apresent_writable; exact Hpa | auto]. }
eapply SRr_mono.
{ exact (AI lyc Sc Hpc W regsT memT mdc d x n HPRE Ha0 Ha1 Ha2 Hn Hd0 Hdn HDEST Hamr Hra_d Hhull Hsrc). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hres & Heff & Hfr & Hpres2).
rewrite Hsp' in Hfr.
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split; [| split; [exact HP|]; split; [exact Hres|]; split; [exact Heff|]; split; [exact Hfr | exact Hpres2]].
(* the intermediate memory: the call's memory off the caller-frame bytes, the entry memory on them *)
set (memi := fun xw : word => if wr_fp_frame_dec FP S lyc (bv_unsigned xw) then memT xw else mem2 xw).
assert (Hnh : forall xw : word, wr_fp_frame FP S lyc (bv_unsigned xw) -> w_H W xw = false).
{ intros xw Hw. destruct (HFR _ Hw) as [[Hh _] _]. rewrite Z_to_bv_bv_unsigned in Hh. exact Hh. }
assert (Ewd : forall a, 0 <= a < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 a) = a).
{ intros a Ha. apply unsigned_lit_small. exact Ha. }
assert (Ei_fr : forall a, 0 <= a < 2 ^ 64 -> wr_fp_frame FP S lyc a -> aview segs (w_H W) memi a = aview segs (w_H W) memT a).
{ intros a Ha Hw. apply aview_eq_of. unfold mrestrict, memi.
  destruct (wr_fp_frame_dec FP S lyc (bv_unsigned (Z_to_bv 64 a))) as [_|Hn']; [reflexivity|].
  rewrite (Ewd a Ha) in Hn'. contradiction. }
assert (Ei_nf : forall a, 0 <= a < 2 ^ 64 -> ~ wr_fp_frame FP S lyc a -> aview segs (w_H W) memi a = aview segs (w_H W) mem2 a).
{ intros a Ha Hw. apply aview_eq_of. unfold mrestrict, memi.
  destruct (wr_fp_frame_dec FP S lyc (bv_unsigned (Z_to_bv 64 a))) as [Hy|_]; [|reflexivity].
  rewrite (Ewd a Ha) in Hy. contradiction. }
(* the allocator invariant at memi: memi differs from mem2 only on caller-frame bytes, none of them owned or hidden *)
assert (HARi : ARx lyc Sc Hpc W memi md2).
{ apply (alx_frame segs B ARx LAWS lyc Sc Hpc W mem2 md2 memi md2 HAR2).
  - intros a Ha Ho. apply Ei_nf; [exact Ha|]. intros Hw. exact (proj2 (HFR a Hw) Ho).
  - intros a Hv. destruct (wr_fp_frame_dec FP S lyc (bv_unsigned (Z_to_bv 64 a))) as [Hw|Hw].
    + assert (E1 : aview segs (w_H W) memi a = aview segs (w_H W) memT a).
      { apply aview_eq_of. unfold mrestrict, memi.
        destruct (wr_fp_frame_dec FP S lyc (bv_unsigned (Z_to_bv 64 a))) as [_|Hn']; [reflexivity | contradiction]. }
      rewrite E1. pose proof (aview_some_of_apresent segs (w_H W) memT _ (proj1 (HFR _ Hw))) as Hs.
      unfold aview, mbyte in Hs |- *. rewrite Z_to_bv_bv_unsigned in Hs. exact Hs.
    + assert (E1 : aview segs (w_H W) memi a = aview segs (w_H W) mem2 a).
      { apply aview_eq_of. unfold mrestrict, memi.
        destruct (wr_fp_frame_dec FP S lyc (bv_unsigned (Z_to_bv 64 a))) as [Hy|_]; [contradiction | reflexivity]. }
      rewrite E1. exact Hv.
  - reflexivity. - reflexivity. - reflexivity.
  - intros a _ Hh. unfold memi. destruct (wr_fp_frame_dec FP S lyc (bv_unsigned (w64 a))) as [Hw|Hw]; [|reflexivity].
    rewrite (Hnh _ Hw) in Hh. discriminate. }
(* memT -> memi: the destination bytes off the caller frames and the call's stack window, by ajournal_x_after_write *)
assert (HJi : ajournal_xR (SK := SK) segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memi md2 k).
{ apply (ajournal_x_after_writeR (SK := SK) segs B PST ARx LAWS segs_low R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k
    memi md2 (fun a => (d <= a < d + n /\ ~ wr_fp_frame FP S lyc a) \/ (sp0 + o - ESTACK <= a < sp0 + o)) Sc Hpc own HJ).
  - intros a Ha Hna. destruct (wr_fp_frame_dec FP S lyc a) as [Hw|Hw].
    + exact (Ei_fr a Ha Hw).
    + rewrite (Ei_nf a Ha Hw). apply (Hfr a Ha); intros H'; apply Hna; [left; split; [exact H' | exact Hw] | right; exact H'].
  - intros a Hpa. pose proof (Hpres2 a Hpa) as (Hh2 & Hb2). destruct Hpa as (Hh & Hb). split; [exact Hh|].
    unfold memi. destruct (wr_fp_frame_dec FP S lyc (bv_unsigned (Z_to_bv 64 a))); [exact Hb | exact Hb2].
  - exact Hsame.
  - intros a [[Ha Hw] | Ha]; left.
    + destruct (proj1 (Hdest a Ha)) as [H'|H']; [exact H' | contradiction].
    + left. zlia.
  - exact HARi.
  - reflexivity. - reflexivity. - zlia. - exact Hfrs. - exact HQT. - reflexivity. }
(* memi -> mem2: the caller-frame bytes the footprint names, by ajournal_x_frame_write *)
apply (ajournal_x_frame_writeR (SK := SK) segs B PST ARx LAWS segs_low R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memi md2 k
  mem2 md2 HJi).
- intros xw Hxw. unfold mrestrict, memi. destruct (wr_fp_frame_dec FP S lyc (bv_unsigned xw)) as [Hy|_]; [contradiction | reflexivity].
- intros xw. unfold mrestrict, memi. destruct (wr_fp_frame_dec FP S lyc (bv_unsigned xw)) as [Hy|_]; [|exact (fun H => H)].
  rewrite (Hnh xw Hy). intros Hm. destruct (memT xw) as [b|] eqn:Eb; [|exfalso; apply Hm; first [exact Eb | reflexivity]].
  assert (Hpa : apresent (w_H W) memT (bv_unsigned xw)).
  { rewrite <- (Z_to_bv_bv_unsigned 64 xw) in Eb. split; [rewrite Z_to_bv_bv_unsigned; exact (Hnh xw Hy) | exists b; exact Eb]. }
  destruct (Hpres2 _ Hpa) as [_ (b' & Hb')]. rewrite Z_to_bv_bv_unsigned in Hb'. rewrite Hb'. discriminate.
- intros xw Hh. unfold memi. destruct (wr_fp_frame_dec FP S lyc (bv_unsigned xw)) as [Hy|_]; [|reflexivity].
  rewrite (Hnh xw Hy) in Hh. discriminate.
- apply same_but_materialized_refl.
Qed.

(* YGcallMx.v:186 aj_intrin_at_x with the destination widened: each byte is a byte awr_byte admits OR a byte of a
   frame of the caller's entry frames S that the footprint names (wr_fp_frame, YCbqG.v). Same conclusion. *)
Lemma aj_intrin_at_x_fr : forall op pc, aintrin_realizes_x op pc ->
forall W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k d x n (o : Z) raw,
AJ STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k ->
getr regsT 10 = w64 d -> getr regsT 11 = w64 x -> getr regsT 12 = w64 n -> 0 <= n < 2 ^ 32 -> 0 <= d -> d + n <= 2 ^ 63 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
(forall a, d <= a < d + n ->
   (awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a \/ wr_fp_frame FP S lyc a) /\
   ~ (sp0 + o - ESTACK <= a < sp0 + o)) ->
amem_range d n ->
range_addressable (aview segs (w_H W) memT) SHADOW_OFF d n ->
(0 < n -> shadow_hull_vis (aview segs (w_H W) memT) d n) ->
(match op with
| OCpy => 0 <= x /\ x + n <= 2 ^ 63 /\ src_ok segs W regsT memT x n /\ (d + n <= x \/ x + n <= d) /\ amem_range x n /\
range_addressable (aview segs (w_H W) memT) SHADOW_OFF x n /\ (0 < n -> shadow_hull_vis (aview segs (w_H W) memT) x n)
| OSet => True end) ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
AJ STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W mem2 md2 k /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 d /\
(forall i, 0 <= i < n -> aview segs (w_H W) mem2 (d + i) =
match op with OCpy => aview segs (w_H W) memT (x + i) | OSet => Some (x mod 256) end) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (sp0 + o - ESTACK <= a < sp0 + o) -> aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
(forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof. exact (aj_intrin_at_x_frR (@wle segs) (wle_refl segs) (wle_trans segs)). Qed.

(* aj_strlen_at_x over a journal at a reflexive and transitive world relation R (the binders of every R rule; the
   call keeps the world, so the journal's world conjunct passes through unchanged and no law of R is read);
   aj_strlen_at_x is its case R := wle *)
Lemma aj_strlen_at_xR : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
(forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
forall pc, astrlen_realizes_x pc ->
forall W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k x len (o : Z) raw,
ajournal_xR (SK := SK) segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k ->
getr regsT 10 = w64 x -> 0 < x -> 0 <= len -> len + 1 < 2 ^ 32 -> x + len + 1 <= 2 ^ 63 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 2 * ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
first_byte segs W memT x (len + 1) 0 len ->
src_ok segs W regsT memT x (len + 1) ->
(forall a, x <= a <= x + len -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o)) ->
amem_range8 x (len + 1) ->
range_addressable (aview segs (w_H W) memT) SHADOW_OFF x (len + 1) ->
shadow_hull_vis (aview segs (w_H W) memT) x (len + 1) ->
(forall a, x + len < a < x + len - (x + len) mod 8 + 8 -> aview segs (w_H W) memT a <> None) ->
rom_view segs W memT ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_xR (SK := SK) segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W mem2 md2 k /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 len /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o) -> aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
(forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
intros R R_refl R_trans pc AS W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k x len o raw
HJ Ha0 Hx0 Hl0 Hl32 Hxl Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hfb Hsx Hbx Hmx Hrx Hhx Htl Hrom.
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
assert (Hlo2 : ly_stk_lo lyc + 2 * ESTACK <= spZ regsT) by (rewrite Eslo, Hsp'; zlia).
assert (Hpres2E : forall a, spZ regsT - 2 * ESTACK <= a < spZ regsT -> apresent (w_H W) memT a)
by (intros a Ha; apply Hpres; rewrite Hsp' in Ha; zlia).
eapply SRr_mono.
{ exact (AS lyc Sc Hpc W regsT memT mdc x len HPRE Hlo2 Hpres2E Ha0 Hx0 Hl0 Hl32 Hxl Hfb Hsx
ltac:(rewrite Hsp'; exact Hbx) Hmx Hrx Hhx Htl Hrom). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hres & Hfr & Hpres2).
rewrite Hsp' in Hfr.
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (ajournal_x_after_writeR (SK := SK) segs B PST ARx LAWS segs_low R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k mem2 md2
(fun a => sp0 + o - 2 * ESTACK <= a < sp0 + o) Sc Hpc own HJ).
- intros a Ha Hna. apply (Hfr a Ha). exact Hna.
- exact Hpres2.
- exact Hsame.
- intros a Ha; left; left; zlia.
- exact HAR2.
- reflexivity. - reflexivity. - zlia. - exact Hfrs. - exact HQT. - reflexivity. }
split; [exact HP|]. split; [exact Hres|]. split; [exact Hfr | exact Hpres2].
Qed.

(* cgif YCbq.v:2062 aj_bcmp_at's shape at the strlen text: a0 = x points to a string NUL-terminated at x + len;
   the call returns a0 = len, keeps the journal at the call's state, and writes only its 2 * ESTACK window. *)
Lemma aj_strlen_at_x : forall pc, astrlen_realizes_x pc ->
forall W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k x len (o : Z) raw,
AJ STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k ->
getr regsT 10 = w64 x -> 0 < x -> 0 <= len -> len + 1 < 2 ^ 32 -> x + len + 1 <= 2 ^ 63 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 2 * ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
first_byte segs W memT x (len + 1) 0 len ->
src_ok segs W regsT memT x (len + 1) ->
(forall a, x <= a <= x + len -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o)) ->
amem_range8 x (len + 1) ->
range_addressable (aview segs (w_H W) memT) SHADOW_OFF x (len + 1) ->
shadow_hull_vis (aview segs (w_H W) memT) x (len + 1) ->
(forall a, x + len < a < x + len - (x + len) mod 8 + 8 -> aview segs (w_H W) memT a <> None) ->
rom_view segs W memT ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
AJ STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W mem2 md2 k /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 len /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o) -> aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
(forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof. exact (aj_strlen_at_xR (@wle segs) (wle_refl segs) (wle_trans segs)). Qed.

(* aj_bcmp_at_x over a journal at a reflexive and transitive world relation R (the binders of every R rule; the
   call keeps the world, so the journal's world conjunct passes through unchanged and no law of R is read);
   aj_bcmp_at_x is its case R := wle *)
Lemma aj_bcmp_at_xR : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
(forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
forall pc, abcmp_realizes_x pc ->
forall W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k x y n (o : Z) raw,
ajournal_xR (SK := SK) segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k ->
getr regsT 10 = w64 x -> getr regsT 11 = w64 y -> getr regsT 12 = w64 n -> 0 <= n < 2 ^ 32 ->
0 <= x -> x + n <= 2 ^ 63 -> 0 <= y -> y + n <= 2 ^ 63 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 2 * ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
src_ok segs W regsT memT x n -> src_ok segs W regsT memT y n ->
(forall a, x <= a < x + n -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o)) -> (forall a, y <= a < y + n -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o)) ->
amem_range x n -> amem_range y n ->
range_addressable (aview segs (w_H W) memT) SHADOW_OFF x n -> (0 < n -> shadow_hull_vis (aview segs (w_H W) memT) x n) ->
range_addressable (aview segs (w_H W) memT) SHADOW_OFF y n -> (0 < n -> shadow_hull_vis (aview segs (w_H W) memT) y n) ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2 (v : word),
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_xR (SK := SK) segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W mem2 md2 k /\
aregs_preserved regsT regs2 /\ getr regs2 10 = v /\
(v = w64 0 <-> forall i, 0 <= i < n -> aview segs (w_H W) memT (x + i) = aview segs (w_H W) memT (y + i)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o) -> aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
(forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
intros R R_refl R_trans pc AM W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k x y n o raw
HJ Ha0 Ha1 Ha2 Hn Hx0 Hxn Hy0 Hyn Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hsx Hsy Hbx Hby Hmx Hmy Hrx Hhx Hry Hhy.
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
assert (Hlo2 : ly_stk_lo lyc + 2 * ESTACK <= spZ regsT) by (rewrite Eslo, Hsp'; zlia).
assert (Hpres2E : forall a, spZ regsT - 2 * ESTACK <= a < spZ regsT -> apresent (w_H W) memT a)
by (intros a Ha; apply Hpres; rewrite Hsp' in Ha; zlia).
eapply SRr_mono.
{ exact (AM lyc Sc Hpc W regsT memT mdc x y n HPRE Hlo2 Hpres2E Ha0 Ha1 Ha2 Hn Hx0 Hxn Hy0 Hyn Hsx Hsy
ltac:(rewrite Hsp'; exact Hbx) ltac:(rewrite Hsp'; exact Hby) Hmx Hmy Hrx Hhx Hry Hhy). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HAR2 & HP & Hsame & Hres & Hcmp & Hfr & Hpres2).
rewrite Hsp' in Hfr.
split; [reflexivity|]. exists regs2, mem2, md2, v.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (ajournal_x_after_writeR (SK := SK) segs B PST ARx LAWS segs_low R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k mem2 md2
(fun a => sp0 + o - 2 * ESTACK <= a < sp0 + o) Sc Hpc own HJ).
- intros a Ha Hna. apply (Hfr a Ha). exact Hna.
- exact Hpres2.
- exact Hsame.
- intros a Ha; left; left; zlia.
- exact HAR2.
- reflexivity. - reflexivity. - zlia. - exact Hfrs. - exact HQT. - reflexivity. }
split; [exact HP|]. split; [exact Hres|]. split; [exact Hcmp|]. split; [exact Hfr | exact Hpres2].
Qed.

(* cgif YCbq.v:2062 aj_bcmp_at over ajournal_x: a call of bcmp through its text. *)
Lemma aj_bcmp_at_x : forall pc, abcmp_realizes_x pc ->
forall W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k x y n (o : Z) raw,
AJ STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k ->
getr regsT 10 = w64 x -> getr regsT 11 = w64 y -> getr regsT 12 = w64 n -> 0 <= n < 2 ^ 32 ->
0 <= x -> x + n <= 2 ^ 63 -> 0 <= y -> y + n <= 2 ^ 63 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 2 * ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
src_ok segs W regsT memT x n -> src_ok segs W regsT memT y n ->
(forall a, x <= a < x + n -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o)) -> (forall a, y <= a < y + n -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o)) ->
amem_range x n -> amem_range y n ->
range_addressable (aview segs (w_H W) memT) SHADOW_OFF x n -> (0 < n -> shadow_hull_vis (aview segs (w_H W) memT) x n) ->
range_addressable (aview segs (w_H W) memT) SHADOW_OFF y n -> (0 < n -> shadow_hull_vis (aview segs (w_H W) memT) y n) ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2 (v : word),
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
AJ STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W mem2 md2 k /\
aregs_preserved regsT regs2 /\ getr regs2 10 = v /\
(v = w64 0 <-> forall i, 0 <= i < n -> aview segs (w_H W) memT (x + i) = aview segs (w_H W) memT (y + i)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o) -> aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
(forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof. exact (aj_bcmp_at_xR (@wle segs) (wle_refl segs) (wle_trans segs)). Qed.

(* aj_strcmp_at_x over a journal at a reflexive and transitive world relation R (the binders of every R rule; the
   call keeps the world, so the journal's world conjunct passes through unchanged and no law of R is read);
   aj_strcmp_at_x is its case R := wle *)
Lemma aj_strcmp_at_xR : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
(forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
forall pc, astrcmp_realizes_x pc ->
forall W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k x y kx ky (o : Z) raw,
ajournal_xR (SK := SK) segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k ->
getr regsT 10 = w64 x -> getr regsT 11 = w64 y -> 0 < x -> 0 < y ->
0 <= kx -> kx + 1 < 2 ^ 32 -> x + kx + 1 <= 2 ^ 63 ->
0 <= ky -> ky + 1 < 2 ^ 32 -> y + ky + 1 <= 2 ^ 63 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 2 * ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
first_byte segs W memT x (kx + 1) 0 kx -> first_byte segs W memT y (ky + 1) 0 ky ->
src_ok segs W regsT memT x (kx + 1) -> src_ok segs W regsT memT y (ky + 1) ->
(forall a, x <= a <= x + kx -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o)) ->
(forall a, y <= a <= y + ky -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o)) ->
amem_range8 x (kx + 1) -> amem_range8 y (ky + 1) ->
range_addressable (aview segs (w_H W) memT) SHADOW_OFF x (kx + 1) -> shadow_hull_vis (aview segs (w_H W) memT) x (kx + 1) ->
range_addressable (aview segs (w_H W) memT) SHADOW_OFF y (ky + 1) -> shadow_hull_vis (aview segs (w_H W) memT) y (ky + 1) ->
(forall a, x + kx < a < x + kx - (x + kx) mod 8 + 8 -> aview segs (w_H W) memT a <> None) ->
(forall a, y + ky < a < y + ky - (y + ky) mod 8 + 8 -> aview segs (w_H W) memT a <> None) ->
rom_view segs W memT ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2 (v : word),
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal_xR (SK := SK) segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W mem2 md2 k /\
aregs_preserved regsT regs2 /\ getr regs2 10 = v /\
(v = w64 0 <-> kx = ky /\ forall i, 0 <= i < kx -> aview segs (w_H W) memT (x + i) = aview segs (w_H W) memT (y + i)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o) -> aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
(forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
intros R R_refl R_trans pc AC W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k x y kx ky o raw
HJ Ha0 Ha1 Hx0 Hy0 Hkx0 Hkx32 Hxk Hky0 Hky32 Hyk Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw
Hfx Hfy Hsx Hsy Hbx Hby Hmx Hmy Hrx Hhx Hry Hhy Htx Hty Hrom.
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
assert (Hlo2 : ly_stk_lo lyc + 2 * ESTACK <= spZ regsT) by (rewrite Eslo, Hsp'; zlia).
assert (Hpres2E : forall a, spZ regsT - 2 * ESTACK <= a < spZ regsT -> apresent (w_H W) memT a)
by (intros a Ha; apply Hpres; rewrite Hsp' in Ha; zlia).
eapply SRr_mono.
{ exact (AC lyc Sc Hpc W regsT memT mdc x y kx ky HPRE Hlo2 Hpres2E Ha0 Ha1 Hx0 Hy0 Hkx0 Hkx32 Hxk Hky0 Hky32 Hyk
Hfx Hfy Hsx Hsy ltac:(rewrite Hsp'; exact Hbx) ltac:(rewrite Hsp'; exact Hby) Hmx Hmy Hrx Hhx Hry Hhy Htx Hty Hrom). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HAR2 & HP & Hsame & Hres & Hcmp & Hfr & Hpres2).
rewrite Hsp' in Hfr.
split; [reflexivity|]. exists regs2, mem2, md2, v.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (ajournal_x_after_writeR (SK := SK) segs B PST ARx LAWS segs_low R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k mem2 md2
(fun a => sp0 + o - 2 * ESTACK <= a < sp0 + o) Sc Hpc own HJ).
- intros a Ha Hna. apply (Hfr a Ha). exact Hna.
- exact Hpres2.
- exact Hsame.
- intros a Ha; left; left; zlia.
- exact HAR2.
- reflexivity. - reflexivity. - zlia. - exact Hfrs. - exact HQT. - reflexivity. }
split; [exact HP|]. split; [exact Hres|]. split; [exact Hcmp|]. split; [exact Hfr | exact Hpres2].
Qed.

(* aj_strlen_at_x's shape at the strcmp text, once per string: a0 = x (NUL at x + kx), a1 = y (NUL at y + ky);
   the call returns a0 = 0 exactly when the strings are equal, keeps the journal at the call's state, and writes
   only its 2 * ESTACK window. *)
Lemma aj_strcmp_at_x : forall pc, astrcmp_realizes_x pc ->
forall W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k x y kx ky (o : Z) raw,
AJ STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k ->
getr regsT 10 = w64 x -> getr regsT 11 = w64 y -> 0 < x -> 0 < y ->
0 <= kx -> kx + 1 < 2 ^ 32 -> x + kx + 1 <= 2 ^ 63 ->
0 <= ky -> ky + 1 < 2 ^ 32 -> y + ky + 1 <= 2 ^ 63 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 2 * ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
first_byte segs W memT x (kx + 1) 0 kx -> first_byte segs W memT y (ky + 1) 0 ky ->
src_ok segs W regsT memT x (kx + 1) -> src_ok segs W regsT memT y (ky + 1) ->
(forall a, x <= a <= x + kx -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o)) ->
(forall a, y <= a <= y + ky -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o)) ->
amem_range8 x (kx + 1) -> amem_range8 y (ky + 1) ->
range_addressable (aview segs (w_H W) memT) SHADOW_OFF x (kx + 1) -> shadow_hull_vis (aview segs (w_H W) memT) x (kx + 1) ->
range_addressable (aview segs (w_H W) memT) SHADOW_OFF y (ky + 1) -> shadow_hull_vis (aview segs (w_H W) memT) y (ky + 1) ->
(forall a, x + kx < a < x + kx - (x + kx) mod 8 + 8 -> aview segs (w_H W) memT a <> None) ->
(forall a, y + ky < a < y + ky - (y + ky) mod 8 + 8 -> aview segs (w_H W) memT a <> None) ->
rom_view segs W memT ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2 (v : word),
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
AJ STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W mem2 md2 k /\
aregs_preserved regsT regs2 /\ getr regs2 10 = v /\
(v = w64 0 <-> kx = ky /\ forall i, 0 <= i < kx -> aview segs (w_H W) memT (x + i) = aview segs (w_H W) memT (y + i)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o) -> aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
(forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof. exact (aj_strcmp_at_xR (@wle segs) (wle_refl segs) (wle_trans segs)). Qed.
End l.
End mx.

(* ---------------------------------------------------------------------------- *)
(* 3. A text at ARx holds at ARx /\ P for any P on (ly, S): each call keeps ly and S, so P rides through.        *)
(*    For ARcfx := ARcf /\ xs_placed_cf (h-mani-a8): take a text at plain ARcf, get it at ARcfx (P := xs_placed_cf). *)
(*    The same shape as S1KitPoison's apoison_realizes_x_conj (YGcallPx.v).                                      *)
Section cj. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable P : alayout -> astate -> Prop.
Local Abbreviation ARP := (fun ly S Hp W mem md => ARx ly S Hp W mem md /\ P ly S).

Lemma aintrin_realizes_x_conj : forall op pc, aintrin_realizes_x segs B ARx op pc -> aintrin_realizes_x segs B ARP op pc.
Proof.
intros op pc AI ly S Hp W regs mem md d x n [[HAR HPl] Hrest]. intros.
eapply SRr_mono; [apply (AI ly S Hp W regs mem md d x n (conj HAR Hrest)); assumption |].
cbv beta. intros W' c' _ (-> & regs' & mem' & md' & Hc & HAR' & Hrest').
split; [reflexivity|]. exists regs', mem', md'. split; [exact Hc|]. split; [split; [exact HAR' | exact HPl] | exact Hrest'].
Qed.

Lemma astrlen_realizes_x_conj : forall pc, astrlen_realizes_x segs B ARx pc -> astrlen_realizes_x segs B ARP pc.
Proof.
intros pc AS ly S Hp W regs mem md x k [[HAR HPl] Hrest]. intros.
eapply SRr_mono; [apply (AS ly S Hp W regs mem md x k (conj HAR Hrest)); assumption |].
cbv beta. intros W' c' _ (-> & regs' & mem' & md' & Hc & HAR' & Hrest').
split; [reflexivity|]. exists regs', mem', md'. split; [exact Hc|]. split; [split; [exact HAR' | exact HPl] | exact Hrest'].
Qed.

Lemma abcmp_realizes_x_conj : forall pc, abcmp_realizes_x segs B ARx pc -> abcmp_realizes_x segs B ARP pc.
Proof.
intros pc AM ly S Hp W regs mem md x y n [[HAR HPl] Hrest]. intros.
eapply SRr_mono; [apply (AM ly S Hp W regs mem md x y n (conj HAR Hrest)); assumption |].
cbv beta. intros W' c' _ (-> & regs' & mem' & md' & v & Hc & HAR' & Hrest').
split; [reflexivity|]. exists regs', mem', md', v. split; [exact Hc|]. split; [split; [exact HAR' | exact HPl] | exact Hrest'].
Qed.

Lemma astrcmp_realizes_x_conj : forall pc, astrcmp_realizes_x segs B ARx pc -> astrcmp_realizes_x segs B ARP pc.
Proof.
intros pc AC ly S Hp W regs mem md x y kx ky [[HAR HPl] Hrest]. intros.
eapply SRr_mono; [apply (AC ly S Hp W regs mem md x y kx ky (conj HAR Hrest)); assumption |].
cbv beta. intros W' c' _ (-> & regs' & mem' & md' & v & Hc & HAR' & Hrest').
split; [reflexivity|]. exists regs', mem', md', v. split; [exact Hc|]. split; [split; [exact HAR' | exact HPl] | exact Hrest'].
Qed.
End cj.
