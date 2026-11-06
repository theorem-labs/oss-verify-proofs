(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: IMAGE B (fs.asan-ubsan) walk of parse_value 0x82fcc, stage lemmas. HEADER: see
   FSW_parse_value_holds.v (the composition into parse_value_spec k, the rule-24 line, the reuse search, the port
   sources, every pc walked and every report site). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/B/Prog/FSW_parse_value.v, with its module names and numbers changed; 1163 of its 1272 lines of code are new or changed and 1247 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: lib/B (fs.asan-ubsan, image B) twin of lib/A/FSW_put_string.v at
   a working branch ca67007c8c2 (a Theorem Labs lane), and another Theorem Labs lane: same lemma names and statement shapes;
   imports point at lib/B's image files and walk kit (YB1v, YB1w, FSH_Base, FSH_Rt, FSPstat, FSH_Fn_writer,
   FSW_K, FSW_K3, FSW_ret, FSW_frame, FSW_frame3, FSW_rd, FSW_strkit and lib/B's put_string files); the
   image-agnostic FSupoison, FSupoisonU, FSupoisonStack, FSH_YC20, FSH_Gen and FSW_writer_model stay lib/A's.
   Every address, cut, branch, offset and register of put_string's own code is RE-MEASURED on image B
   (A_put_string 0x85fc8, 928 bytes; the neutral excerpt put_string.fuzz_state.asan-ubsan.s), never copied.
   rule 24: proves no function (kind: segment lemma). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/B/FSW_put_string.v; 280 of its 343 lines of code are new or changed and 1209 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: lib/B (fs.asan-ubsan, image B) twin of lib/A/ZZpskeep.v at
   a working branch ca67007c8c2 (a Theorem Labs lane), and another Theorem Labs lane: same lemma names and statement shapes;
   imports point at lib/B's image files and walk kit (YB1v, YB1w, FSH_Base, FSH_Rt, FSPstat, FSH_Fn_writer,
   FSW_K, FSW_K3, FSW_ret, FSW_frame, FSW_frame3, FSW_rd, FSW_strkit and lib/B's put_string files); the
   image-agnostic FSupoison, FSupoisonU, FSupoisonStack, FSH_YC20, FSH_Gen and FSW_writer_model stay lib/A's.
   Every address, cut, branch, offset and register of put_string's own code is RE-MEASURED on image B
   (A_put_string 0x85fc8, 928 bytes; the neutral excerpt put_string.fuzz_state.asan-ubsan.s), never copied.
   rule 24: proves no function (kind: segment lemma). *)
(* SCRATCH (a Theorem Labs lane): put_string's TRANSPORT facts, image B (fs.asan-ubsan). Folded into FSW_put_string.v.
   Each put_string_spec premise about the out-object, the globals, the string and the buffer survives a memory change
   that agrees, off a write set Wr, with the memory before it (pske_agree). a Theorem Labs lane feeds Wr twice: the prologue's
   write set (its stack window, the fake frame, the frame's shadow and flag byte) and the complement of put's wkeep.
   Two premises are forced by the definitions (accepted by a Theorem Labs lane 2026-10-29):
   - pske_cstr_ok: cstr_ok's shadow_hull_vis conjunct (FSH_Gen.v:289; definition YG0d.v:317-318) reads the 8-aligned
     HULL of the string's shadow bytes, so Wr must miss the hull, not only the shadow bytes themselves.
   - pske_writable: the backward direction needs `apresent (w_H W) mem a \/ seg_rom tfibsegs (Z_to_bv 64 a) = None`:
     wview (LinuxProcessSem RiscvSemantics.v:528-540) falls back to WRITABLE segments only, mbyte (YP09.v:18-21) to
     any segment, so a byte that appears in mem' at a read-only image address agrees on mbyte but is writable only at
     W'. The forward direction (pske_writable_fwd) needs nothing beyond the agreement.
   Templates: FSW_strkit.v:152-219 (cstr_ok_unpoison / cstr_ok_poison, the conjunct-by-conjunct transport). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
FSupoison FSupoisonU FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
YB1v FSH_Base FSH_Rt FSPstat FSW_put_string.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require
FSH_Fn_writer.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ================= closed arithmetic (lia only here) ================= *)
Lemma pske_ar_nat : forall a n k, 0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> (k < n)%nat ->
  0 <= a + Z.of_nat k < 2 ^ 64 /\ a <= a + Z.of_nat k < a + Z.of_nat n.
Proof. intros a n k H0 H1 Hk. lia. Qed.

Lemma pske_ar_one : forall p n j, 0 <= p -> p + Z.of_nat n <= 2 ^ 64 -> (j < n)%nat ->
  0 <= p + Z.of_nat j /\ p + Z.of_nat j + Z.of_nat 1 <= 2 ^ 64 /\
  (forall x, p + Z.of_nat j <= x < p + Z.of_nat j + Z.of_nat 1 -> p <= x < p + Z.of_nat n).
Proof. intros p n j H0 H1 Hj. split; [lia | split; [lia | intros x Hx; lia]]. Qed.

Lemma pske_ar_off : forall a i n, 0 <= a -> a + n <= 2 ^ 64 -> 0 <= i < n ->
  0 <= a + i < 2 ^ 64 /\ a <= a + i < a + n.
Proof. intros a i n H0 H1 Hi. lia. Qed.

(* a sub-window [a, a + n) of [lo, hi) inside the address space *)
Lemma pske_ar_sub : forall lo hi a n, 0 <= lo -> hi <= 2 ^ 64 -> lo <= a -> a + Z.of_nat n <= hi ->
  0 <= a /\ a + Z.of_nat n <= 2 ^ 64 /\ (forall x, a <= x < a + Z.of_nat n -> lo <= x < hi).
Proof. intros lo hi a n H0 H1 H2 H3. split; [lia | split; [lia | intros x Hx; lia]]. Qed.

(* every shadow byte of [s, s + n] lies in the 8-aligned hull shadow_hull_vis reads *)
Lemma pske_hull_in : forall s n x, s <= x <= s + n ->
  shadow_addr s / 8 * 8 <= shadow_addr x < shadow_addr (s + n) / 8 * 8 + 8.
Proof. intros s n x Hx. unfold shadow_addr, SHADOW_OFF. Z.div_mod_to_equations. lia. Qed.

Lemma pske_hull_rng : forall s n t, 0 <= s -> s + n < 2 ^ 47 ->
  shadow_addr s / 8 * 8 <= t < shadow_addr (s + n) / 8 * 8 + 8 -> 0 <= t < 2 ^ 64.
Proof. intros s n t H0 H1 Ht. unfold shadow_addr, SHADOW_OFF in Ht. Z.div_mod_to_equations. lia. Qed.

Lemma pske_tail : forall y a, y < a < y - y mod 8 + 8 -> y < a < y + 8.
Proof. intros y a H. pose proof (Z.mod_pos_bound y 8 ltac:(lia)). lia. Qed.

(* cstr_ok's ceiling conjunct is `p + len + 1 <= alloc_ceiling` (a Theorem Labs lane 2d9cdf6a160; was `+ 8`): the bytes this
   file transports reach p + len + 7 (the word holding the NUL), still inside the address space *)
Lemma pske_ar_cstr : forall c s n x, c < 2 ^ 47 -> 4096 <= s -> s + n + 1 <= c -> s <= x < s + n + 8 ->
  0 <= x < 2 ^ 64.
Proof. intros c s n x H0 H1 H2 H3. lia. Qed.

Lemma pske_pstat_in :
  In (G_LIVE, G_LIVE + 8) FS_PSTAT_FP /\ In (G_PEAK, G_PEAK + 8) FS_PSTAT_FP /\
  In (G_COUNT, G_COUNT + 8) FS_PSTAT_FP /\ In (G_FAIL, G_FAIL + 8) FS_PSTAT_FP.
Proof.
unfold FS_PSTAT_FP, G_LIVE, G_PEAK, G_COUNT, G_FAIL. cbn [In].
split; [right; left; reflexivity|]. split; [right; right; left; reflexivity|].
split; [right; right; right; left; reflexivity | left; reflexivity].
Qed.

Section pske. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.

(* ================= the one agreement shape ================= *)
Definition pske_agree (W W' : world tfibsegs) (mem mem' : word -> option byte) (Wr : Z -> Prop) : Prop :=
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wr a ->
     mbyte tfibsegs (mrestrict (w_H W') mem') a = mbyte tfibsegs (mrestrict (w_H W) mem) a) /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> apresent (w_H W) mem a -> apresent (w_H W') mem' a).

(* non-vacuity: the agreement holds of an unchanged memory, for any Wr *)
Lemma pske_agree_refl : forall W mem Wr, pske_agree W W mem mem Wr.
Proof. intros W mem Wr. split; intros a _ _; [reflexivity | exact (fun P => P)]. Qed.

Lemma pske_mbyte : forall W W' mem mem' Wr a, pske_agree W W' mem mem' Wr -> 0 <= a < 2 ^ 64 -> ~ Wr a ->
  mbyte tfibsegs (mrestrict (w_H W') mem') a = mbyte tfibsegs (mrestrict (w_H W) mem) a.
Proof. intros W W' mem mem' Wr a H Ha Hw. exact (proj1 H a Ha Hw). Qed.

Lemma pske_aview : forall W W' mem mem' Wr a, pske_agree W W' mem mem' Wr -> 0 <= a < 2 ^ 64 -> ~ Wr a ->
  aview tfibsegs (w_H W') mem' a = aview tfibsegs (w_H W) mem a.
Proof.
intros W W' mem mem' Wr a H Ha Hw. unfold aview. rewrite (pske_mbyte W W' mem mem' Wr a H Ha Hw). reflexivity.
Qed.

Lemma pske_apresent_mr : forall (H : word -> bool) m a,
  apresent H m a <-> exists b, mrestrict H m (Z_to_bv 64 a) = Some b.
Proof.
intros H m a. unfold apresent, mrestrict. split.
- intros (Hh & b & Hb). exists b. rewrite Hh. exact Hb.
- intros (b & Hb). revert Hb. destruct (H (Z_to_bv 64 a)) eqn:Hh; intros Hb; [discriminate|].
  split; [reflexivity | exists b; exact Hb].
Qed.

(* ================= 1. val_mem ================= *)
Lemma pske_val_mem : forall W W' mem mem' Wr a n v,
  pske_agree W W' mem mem' Wr -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (forall x, a <= x < a + Z.of_nat n -> ~ Wr x) ->
  val_mem tfibsegs (mrestrict (w_H W) mem) a n v -> val_mem tfibsegs (mrestrict (w_H W') mem') a n v.
Proof.
intros W W' mem mem' Wr a n v H H0 H1 Hw Hv k Hk.
destruct (pske_ar_nat a n k H0 H1 Hk) as (Hr & Hin).
rewrite (pske_mbyte W W' mem mem' Wr (a + Z.of_nat k) H Hr (Hw _ Hin)). exact (Hv k Hk).
Qed.

(* ================= 2. writable_at ================= *)
Lemma pske_writable_fwd : forall W W' mem mem' Wr a,
  pske_agree W W' mem mem' Wr -> 0 <= a < 2 ^ 64 -> ~ Wr a ->
  writable_at tfibsegs (mrestrict (w_H W) mem) a -> writable_at tfibsegs (mrestrict (w_H W') mem') a.
Proof.
intros W W' mem mem' Wr a H Ha Hw Hwr. unfold writable_at in *.
destruct (mrestrict (w_H W') mem' (Z_to_bv 64 a)) as [b'|] eqn:E'.
- unfold wview. rewrite E'. discriminate.
- destruct (mrestrict (w_H W) mem (Z_to_bv 64 a)) as [b|] eqn:E.
  + exfalso.
    pose proof (proj2 (pske_apresent_mr (w_H W) mem a) (ex_intro _ b E)) as P.
    destruct (proj1 (pske_apresent_mr (w_H W') mem' a) (proj2 H a Ha Hw P)) as (b'' & E'').
    rewrite E' in E''. discriminate.
  + unfold wview in *. rewrite E in Hwr. rewrite E'. exact Hwr.
Qed.

Lemma pske_writable : forall W W' mem mem' Wr a,
  pske_agree W W' mem mem' Wr -> 0 <= a < 2 ^ 64 -> ~ Wr a ->
  (apresent (w_H W) mem a \/ seg_rom tfibsegs (Z_to_bv 64 a) = None) ->
  (writable_at tfibsegs (mrestrict (w_H W) mem) a <-> writable_at tfibsegs (mrestrict (w_H W') mem') a).
Proof.
intros W W' mem mem' Wr a H Ha Hw Hc. split; [exact (pske_writable_fwd W W' mem mem' Wr a H Ha Hw)|].
intros Hwr. unfold writable_at in *.
destruct (mrestrict (w_H W) mem (Z_to_bv 64 a)) as [b|] eqn:E.
- unfold wview. rewrite E. discriminate.
- destruct (mrestrict (w_H W') mem' (Z_to_bv 64 a)) as [b'|] eqn:E'.
  + exfalso. destruct Hc as [Hp | Hr].
    * destruct (proj1 (pske_apresent_mr (w_H W) mem a) Hp) as (b0 & E0). rewrite E in E0. discriminate.
    * pose proof (pske_mbyte W W' mem mem' Wr a H Ha Hw) as M. unfold mbyte in M.
      rewrite E, E', Hr in M. discriminate.
  + unfold wview in *. rewrite E' in Hwr. rewrite E. exact Hwr.
Qed.

(* ================= 6. zbytes_at (garr8 first; cstr_ok and wout_ok use it) ================= *)
Lemma pske_garr8 : forall W W' mem mem' Wr p l,
  pske_agree W W' mem mem' Wr -> 0 <= p -> p + Z.of_nat (length l) <= 2 ^ 64 ->
  (forall a, p <= a < p + Z.of_nat (length l) -> ~ Wr a) ->
  garr8 tfibsegs (mrestrict (w_H W) mem) p l -> garr8 tfibsegs (mrestrict (w_H W') mem') p l.
Proof.
intros W W' mem mem' Wr p l H H0 H1 Hw Hg j Hj. destruct (Hg j Hj) as (Hv & Hb). split; [|exact Hb].
destruct (pske_ar_one p (length l) j H0 H1 Hj) as (A0 & A1 & A2).
exact (pske_val_mem W W' mem mem' Wr (p + Z.of_nat j) 1 (nth j l 0) H A0 A1 (fun x Hx => Hw x (A2 x Hx)) Hv).
Qed.

Lemma pske_zbytes : forall W W' mem mem' Wr p l,
  pske_agree W W' mem mem' Wr -> 0 <= p -> p + Z.of_nat (length l) <= 2 ^ 64 ->
  (forall a, p <= a < p + Z.of_nat (length l) -> ~ Wr a) ->
  zbytes_at tfibsegs W mem p l -> zbytes_at tfibsegs W' mem' p l.
Proof.
intros W W' mem mem' Wr p l H H0 H1 Hw Hz. unfold zbytes_at in *.
exact (pske_garr8 W W' mem mem' Wr p l H H0 H1 Hw Hz).
Qed.

(* ================= 3. wout_ok ================= *)
Lemma pske_wout_ok : forall ly S ly' S' W W' mem mem' Wr o buf cap failed text,
  pske_agree W W' mem mem' Wr ->
  ly_top ly <= ly_top ly' -> o + 32 <= 2 ^ 64 ->
  (forall a, o <= a < o + 32 -> ~ Wr a) ->
  (cap <> 0 -> HEAD <= buf /\ buf + cap <= 2 ^ 64 /\ (forall a, buf - HEAD <= a < buf + cap -> ~ Wr a)) ->
  (In (buf - HEAD, cap + HEAD) (ablocks B ly S) -> In (buf - HEAD, cap + HEAD) (ablocks B ly' S')) ->
  FSH_Fn_writer.wout_ok B tfibsegs ly S W mem o buf cap failed text ->
  FSH_Fn_writer.wout_ok B tfibsegs ly' S' W' mem' o buf cap failed text.
Proof.
intros ly S ly' S' W W' mem mem' Wr o buf cap failed text H Htop Ho Hwo Hbuf Hin
  (Hal & Ho0 & Hotop & Hwp & Hb & Hc & V0 & V8 & V16 & V24 & Hf & Hbo & Hdisj).
unfold FSH_Fn_writer.wout_ok.
split; [exact Hal|]. split; [exact Ho0|]. split; [exact (Z.le_trans _ _ _ Hotop Htop)|].
split.
{ intros i Hi. destruct (Hwp i Hi) as (Hw1 & Hp1).
  destruct (pske_ar_off o i 32 Ho0 Ho Hi) as (R1 & R2).
  split; [exact (pske_writable_fwd W W' mem mem' Wr (o + i) H R1 (Hwo _ R2) Hw1)|].
  exact (proj2 H (o + i) R1 (Hwo _ R2) Hp1). }
split; [exact Hb|]. split; [exact Hc|].
assert (Hhi : o + 32 <= 2 ^ 64) by exact Ho.
split.
{ destruct (pske_ar_sub o (o + 32) o 8 Ho0 Hhi ltac:(clear - Ho0; lia) ltac:(clear - Ho0; lia)) as (A0 & A1 & A2).
  exact (pske_val_mem W W' mem mem' Wr o 8 buf H A0 A1 (fun x Hx => Hwo x (A2 x Hx)) V0). }
split.
{ destruct (pske_ar_sub o (o + 32) (o + 8) 8 Ho0 Hhi ltac:(clear - Ho0; lia) ltac:(clear - Ho0; lia))
    as (A0 & A1 & A2).
  exact (pske_val_mem W W' mem mem' Wr (o + 8) 8 _ H A0 A1 (fun x Hx => Hwo x (A2 x Hx)) V8). }
split.
{ destruct (pske_ar_sub o (o + 32) (o + 16) 8 Ho0 Hhi ltac:(clear - Ho0; lia) ltac:(clear - Ho0; lia))
    as (A0 & A1 & A2).
  exact (pske_val_mem W W' mem mem' Wr (o + 16) 8 cap H A0 A1 (fun x Hx => Hwo x (A2 x Hx)) V16). }
split.
{ destruct (pske_ar_sub o (o + 32) (o + 24) 4 Ho0 Hhi ltac:(clear - Ho0; lia) ltac:(clear - Ho0; lia))
    as (A0 & A1 & A2).
  exact (pske_val_mem W W' mem mem' Wr (o + 24) 4 failed H A0 A1 (fun x Hx => Hwo x (A2 x Hx)) V24). }
split; [exact Hf|]. split; [exact Hbo|].
destruct Hdisj as [Hz | (Hj & (Hbl & Hm & Hcap & Hhd) & Hlen & Hz)]; [left; exact Hz|].
right. assert (Hc0 : cap <> 0) by (clear - Hcap; lia).
destruct (Hbuf Hc0) as (Hb16 & Hbc & Hwb).
split; [exact Hj|]. split.
- split; [exact (Hin Hbl)|]. split; [exact Hm|]. split; [exact Hcap|].
  destruct (pske_ar_sub (buf - HEAD) (buf + cap) (buf - HEAD) 8
    ltac:(clear - Hb16; lia) Hbc (Z.le_refl _) ltac:(clear - Hcap; unfold HEAD; lia)) as (A0 & A1 & A2).
  exact (pske_val_mem W W' mem mem' Wr (buf - HEAD) 8 cap H A0 A1 (fun x Hx => Hwb x (A2 x Hx)) Hhd).
- split; [exact Hlen|].
  assert (Lz : Z.of_nat (length (text ++ [0])) = Z.of_nat (length text) + 1)
    by (rewrite length_app; cbn [length]; lia).
  destruct Hb as (Hb0 & _).
  apply (pske_zbytes W W' mem mem' Wr buf (text ++ [0]) H Hb0); [ | | exact Hz]; rewrite Lz.
  + clear - Hlen Hbc. lia.
  + intros a Ha. apply Hwb. clear - Ha Hlen. unfold HEAD. lia.
Qed.

(* ================= 4. fs_glob ================= *)
Lemma pske_glob : forall W W' mem mem' Wr live peak cnt fail,
  pske_agree W W' mem mem' Wr -> (forall a, inFP FS_PSTAT_FP a -> ~ Wr a) ->
  fs_glob tfibsegs W mem live peak cnt fail -> fs_glob tfibsegs W' mem' live peak cnt fail.
Proof.
intros W W' mem mem' Wr live peak cnt fail H Hw (V1 & V2 & V3 & V4 & R).
destruct pske_pstat_in as (I1 & I2 & I3 & I4).
unfold fs_glob, fs_glob_at.
split; [|split; [|split; [|split; [|exact R]]]].
- apply (pske_val_mem W W' mem mem' Wr G_LIVE 8 live H); [unfold G_LIVE; lia | unfold G_LIVE; lia | | exact V1].
  intros x Hx. apply Hw. exact (inFP_FS_PSTAT_FP G_LIVE I1 x Hx).
- apply (pske_val_mem W W' mem mem' Wr G_PEAK 8 peak H); [unfold G_PEAK; lia | unfold G_PEAK; lia | | exact V2].
  intros x Hx. apply Hw. exact (inFP_FS_PSTAT_FP G_PEAK I2 x Hx).
- apply (pske_val_mem W W' mem mem' Wr G_COUNT 8 cnt H); [unfold G_COUNT; lia | unfold G_COUNT; lia | | exact V3].
  intros x Hx. apply Hw. exact (inFP_FS_PSTAT_FP G_COUNT I3 x Hx).
- apply (pske_val_mem W W' mem mem' Wr G_FAIL 8 fail H); [unfold G_FAIL; lia | unfold G_FAIL; lia | | exact V4].
  intros x Hx. apply Hw. exact (inFP_FS_PSTAT_FP G_FAIL I4 x Hx).
Qed.

(* ================= 5. cstr_ok (all eight conjuncts) ================= *)
Lemma pske_cstr_ok : forall W W' mem mem' Wr s bs,
  pske_agree W W' mem mem' Wr ->
  (forall a, s <= a < s + Z.of_nat (length bs) + 8 -> ~ Wr a) ->
  (forall t, shadow_addr s / 8 * 8 <= t < shadow_addr (s + Z.of_nat (length bs)) / 8 * 8 + 8 -> ~ Wr t) ->
  cstr_ok tfibsegs W mem s bs -> cstr_ok tfibsegs W' mem' s bs.
Proof.
intros W W' mem mem' Wr s bs H Hw Hsh ((Hg & Hnz) & H4096 & Hcl & H32 & Ham & Hra & Hhv & Htl).
pose proof (@alloc_ceiling_lt rc) as Hceil.
assert (Rb : forall x, s <= x < s + Z.of_nat (length bs) + 8 -> 0 <= x < 2 ^ 64)
  by (intros x Hx; exact (pske_ar_cstr alloc_ceiling s (Z.of_nat (length bs)) x Hceil H4096
        ltac:(clear - Hcl; lia) Hx)).
assert (Rh : forall t, shadow_addr s / 8 * 8 <= t < shadow_addr (s + Z.of_nat (length bs)) / 8 * 8 + 8 ->
               0 <= t < 2 ^ 64)
  by (intros t Ht; exact (pske_hull_rng s (Z.of_nat (length bs)) t ltac:(clear - H4096; lia)
        ltac:(clear - Hcl Hceil; lia) Ht)).
split; [split; [|exact Hnz]|].
{ assert (Lz : Z.of_nat (length (bs ++ [0])) = Z.of_nat (length bs) + 1)
    by (rewrite length_app; cbn [length]; lia).
  apply (pske_garr8 W W' mem mem' Wr s (bs ++ [0]) H ltac:(clear - H4096; lia)); [ | | exact Hg]; rewrite Lz.
  - clear - Hcl Hceil. lia.
  - intros a Ha. apply Hw. clear - Ha. lia. }
split; [exact H4096|]. split; [exact Hcl|]. split; [exact H32|]. split; [exact Ham|].
split.
{ intros x Hx. destruct (Hra x Hx) as (v & Hv & Hok). exists v. split; [|exact Hok].
  change (shadow_of_addr SHADOW_OFF x) with (shadow_addr x) in Hv |- *.
  pose proof (pske_hull_in s (Z.of_nat (length bs)) x ltac:(clear - Hx; lia)) as Hxh.
  rewrite (pske_aview W W' mem mem' Wr (shadow_addr x) H (Rh _ Hxh) (Hsh _ Hxh)). exact Hv. }
split.
{ intros t Ht.
  assert (Ht' : shadow_addr s / 8 * 8 <= t < shadow_addr (s + Z.of_nat (length bs)) / 8 * 8 + 8)
    by (replace (s + Z.of_nat (length bs)) with (s + (Z.of_nat (length bs) + 1) - 1) by ring; exact Ht).
  rewrite (pske_aview W W' mem mem' Wr t H (Rh _ Ht') (Hsh _ Ht')). exact (Hhv t Ht). }
intros a Ha. pose proof (pske_tail _ _ Ha) as Ha'.
assert (Hin : s <= a < s + Z.of_nat (length bs) + 8) by (clear - Ha'; lia).
rewrite (pske_aview W W' mem mem' Wr a H (Rb a Hin) (Hw a Hin)). exact (Htl a Ha).
Qed.

(* ================= 7. wsrc_kept ================= *)
(* STATE: blocks may only be added (incl, which ablocks B ly' S' = ablocks B ly S gives) and user-poisoned ranges
   only removed (incl U' U, which U' = U gives). MEMORY: the fs_rblock disjunct reads the 8-byte size word at
   p - HEAD of the block holding the range, so Wr must miss that word for every such block. *)
Lemma pske_wsrc_kept : forall ly S U ly' S' U' W W' mem mem' Wr buf s bs,
  pske_agree W W' mem mem' Wr ->
  incl (ablocks B ly S) (ablocks B ly' S') -> incl U' U ->
  (forall p k, p <> buf -> In (p - HEAD, k + HEAD) (ablocks B ly S) ->
     p <= s -> s + Z.of_nat (length bs) <= p + k ->
     HEAD <= p /\ p - HEAD + 8 <= 2 ^ 64 /\ (forall a, p - HEAD <= a < p - HEAD + 8 -> ~ Wr a)) ->
  FSH_Fn_writer.wsrc_kept B tfibsegs ly S U W mem buf s bs ->
  FSH_Fn_writer.wsrc_kept B tfibsegs ly' S' U' W' mem' buf s bs.
Proof.
intros ly S U ly' S' U' W W' mem mem' Wr buf s bs H Hbl HU Hhd
  [Hn | [(p & k & Hp & (Hb & Hm & Hk & Hv) & Hs1 & Hs2) | [(p & k & Hp & Hb & Hs1 & Hs2 & Hr) | Hro]]].
- left. exact Hn.
- right. left. destruct (Hhd p k Hp Hb Hs1 Hs2) as (R1 & R2 & Hw).
  exists p, k. split; [exact Hp|]. split; [|split; [exact Hs1 | exact Hs2]].
  split; [exact (Hbl _ Hb)|]. split; [exact Hm|]. split; [exact Hk|].
  apply (pske_val_mem W W' mem mem' Wr (p - HEAD) 8 k H); [clear - R1; lia | exact R2 | | exact Hv].
  intros x Hx. apply Hw. exact Hx.
- right. right. left. exists p, k. split; [exact Hp|]. split; [exact (Hbl _ Hb)|].
  split; [exact Hs1|]. split; [exact Hs2|].
  intros r Hr'. exact (Hr r (HU r Hr')).
- right. right. right. exact Hro.
Qed.

(* ================= 8. the one-node frame-chain clause at o ================= *)
(* the unpoison bridge: a byte outside both poison sets reads the same through unpoison at both ends *)
Lemma pske_unpoison_aview : forall (W W' : world tfibsegs) mem mem' Wr U U' a,
  pske_agree W W' mem mem' Wr -> 0 <= a < 2 ^ 64 -> ~ Wr a -> in_ush U a = false -> in_ush U' a = false ->
  aview tfibsegs (w_H W') (unpoison U' mem') a = aview tfibsegs (w_H W) (unpoison U mem) a.
Proof.
intros W W' mem mem' Wr U U' a H Ha Hw E E'.
rewrite (aview_unpoison_out tfibsegs (w_H W') U' mem' a) by (rewrite (wz a Ha); exact E').
rewrite (aview_unpoison_out tfibsegs (w_H W) U mem a) by (rewrite (wz a Ha); exact E).
exact (pske_aview W W' mem mem' Wr a H Ha Hw).
Qed.

Lemma pske_chain_at_o : forall (W W' : world tfibsegs) mem mem' Wr U U' (regs : bvmap 5 word) o,
  pske_agree W W' mem mem' Wr -> o <= 2 ^ 64 ->
  (forall a, o - 16 <= a < o -> ~ Wr a) ->
  (forall a, o - 16 <= a < o -> in_ush U a = false) ->
  (forall a, o - 16 <= a < o -> in_ush U' a = false) ->
  (o = spZ regs + 8 /\ raZ regs < alloc_ceiling \/
   spZ regs + 16 <= o /\ exists ra nfp, rdword (aview tfibsegs (w_H W) (unpoison U mem)) (o - 8) = Some ra /\
     rdword (aview tfibsegs (w_H W) (unpoison U mem)) (o - 16) = Some nfp /\ (ra < 4096 \/ nfp < alloc_ceiling)) ->
  (o = spZ regs + 8 /\ raZ regs < alloc_ceiling \/
   spZ regs + 16 <= o /\ exists ra nfp, rdword (aview tfibsegs (w_H W') (unpoison U' mem')) (o - 8) = Some ra /\
     rdword (aview tfibsegs (w_H W') (unpoison U' mem')) (o - 16) = Some nfp /\ (ra < 4096 \/ nfp < alloc_ceiling)).
Proof.
intros W W' mem mem' Wr U U' regs o H Ho Hw HU HU' [Hl | (Hsp & ra & nfp & R8 & R16 & Hor)]; [left; exact Hl|].
right. split; [exact Hsp|]. exists ra, nfp.
assert (Hs0 : 0 <= spZ regs) by (unfold spZ; exact (proj1 (bv_unsigned_in_range _ _))).
assert (E : forall a, o - 16 <= a < o ->
          aview tfibsegs (w_H W') (unpoison U' mem') a = aview tfibsegs (w_H W) (unpoison U mem) a).
{ intros a Ha. apply (pske_unpoison_aview W W' mem mem' Wr U U' a H); [ | exact (Hw a Ha) | exact (HU a Ha) | exact (HU' a Ha)].
  clear - Ha Hs0 Hsp Ho. lia. }
split; [|split; [|exact Hor]].
- rewrite (rdword_ext (aview tfibsegs (w_H W) (unpoison U mem)) (aview tfibsegs (w_H W') (unpoison U' mem')) (o - 8));
    [exact R8|].
  intros k Hk. apply E. clear - Hk. lia.
- rewrite (rdword_ext (aview tfibsegs (w_H W) (unpoison U mem)) (aview tfibsegs (w_H W') (unpoison U' mem')) (o - 16));
    [exact R16|].
  intros k Hk. apply E. clear - Hk. lia.
Qed.

(* the same with the poison-set premises discharged from ARU at both ends: an application byte (below the shadow,
   or in high memory) is no user-poisoned shadow byte (FSupoison.ush_facts; FSW_strkit.unpoison_app's argument) *)
Lemma pske_ush_aru : forall ly S U (W : world tfibsegs) mem md a,
  ARU tfibsegs B ly S U W mem md -> (a < SHADOW_OFF \/ kHighMemBeg <= a) -> in_ush U a = false.
Proof.
intros ly S U W mem md a H Ha. destruct (in_ush U a) eqn:E; [|reflexivity]. exfalso.
destruct (ush_facts tfibsegs B ly S U W mem md a H E) as (_ & L1 & L2).
clear - Ha L1 L2. lia.
Qed.

Lemma pske_chain_at_o_aru : forall ly S ly' S' U U' (W W' : world tfibsegs) mem mem' md md' Wr
    (regs : bvmap 5 word) o,
  pske_agree W W' mem mem' Wr ->
  ARU tfibsegs B ly S U W mem md -> ARU tfibsegs B ly' S' U' W' mem' md' ->
  o <= 2 ^ 64 ->
  (forall a, o - 16 <= a < o -> ~ Wr a) ->
  (forall a, o - 16 <= a < o -> a < SHADOW_OFF \/ kHighMemBeg <= a) ->
  (o = spZ regs + 8 /\ raZ regs < alloc_ceiling \/
   spZ regs + 16 <= o /\ exists ra nfp, rdword (aview tfibsegs (w_H W) (unpoison U mem)) (o - 8) = Some ra /\
     rdword (aview tfibsegs (w_H W) (unpoison U mem)) (o - 16) = Some nfp /\ (ra < 4096 \/ nfp < alloc_ceiling)) ->
  (o = spZ regs + 8 /\ raZ regs < alloc_ceiling \/
   spZ regs + 16 <= o /\ exists ra nfp, rdword (aview tfibsegs (w_H W') (unpoison U' mem')) (o - 8) = Some ra /\
     rdword (aview tfibsegs (w_H W') (unpoison U' mem')) (o - 16) = Some nfp /\ (ra < 4096 \/ nfp < alloc_ceiling)).
Proof.
intros ly S ly' S' U U' W W' mem mem' md md' Wr regs o H HA HA' Ho Hw Happ.
apply (pske_chain_at_o W W' mem mem' Wr U U' regs o H Ho Hw).
- intros a Ha. exact (pske_ush_aru ly S U W mem md a HA (Happ a Ha)).
- intros a Ha. exact (pske_ush_aru ly' S' U' W' mem' md' a HA' (Happ a Ha)).
Qed.

(* ================= 9. the present window ================= *)
Lemma pske_present_window : forall (W W' : world tfibsegs) mem mem' Wr (regs : bvmap 5 word) ot,
  pske_agree W W' mem mem' Wr -> ot <= 2 ^ 64 ->
  (forall a, spZ regs <= a < ot -> ~ Wr a) ->
  (forall a, spZ regs <= a < ot -> apresent (w_H W) mem a) ->
  (forall a, spZ regs <= a < ot -> apresent (w_H W') mem' a).
Proof.
intros W W' mem mem' Wr regs ot H Hot Hw Hp a Ha.
assert (Hs0 : 0 <= spZ regs) by (unfold spZ; exact (proj1 (bv_unsigned_in_range _ _))).
exact (proj2 H a ltac:(clear - Hs0 Ha Hot; lia) (Hw a Ha) (Hp a Ha)).
Qed.

End pske.
