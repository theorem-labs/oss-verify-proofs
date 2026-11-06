(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/Reusable/YCbq.v aj_intrin_at (lines 2155-2206) restated as w7_memcpy_at for image A's __asan_memcpy 0x510d4, with the wrapper's same_but_materialized kept in the post as same_io; the rest of the file is new. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW7bKit.v at 25d4b718638e for reac-pw/fuzz_rate's image A: module paths changed; the image is fuzz_rate.asan (images.Asan) in place of lib/A/Img0; RPgBase.rl_cstr and RPgMem.rm_nth_map are lib/A/RtPgBase.v rt_cstr and lib/A/RtPgMem.v rtm_nth_map; __asan_memcpy is rate's 0x51860 (lib/A/RtPgW7bBase.v W7_MEMCPY). *)
(* reac-pw/fuzz_rate image A (fuzz_rate.asan, pinned sha256
   22bc8613d780c9a99353dc86368f9401311ef5c8358882651217836298529b6a; addresses measured on the unstripped twin
   0d508f2c65c249840b6c8fe3c1960824f2548b175c23583632f06bb7956458c3): the memory kit of the walk of
   LLVMFuzzerTestOneInput from 0x8150c to 0x81e00. Proves no function (kind: segment lemma).
   w7_strok: what the strlen and memcpy calls of the four parts ask of a NUL-terminated string at x, as one fact
   that moves with the memory (w7_strok_kept) and comes from RtPgBase.rt_cstr (an image string) or from a byte list
   in the frame for locals (ch). w7_memcpy_at: the journal form of __asan_memcpy (0x51860) that keeps the I/O
   state. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec RtPgMem RtPgW7bBase.
Require OSSVerify.reac_pw.fuzz_rate.images.Asan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* image A's loaded segments; an abbreviation, so every statement names the image module's own term *)
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.Asan.M.loaded_segments.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

(* ---- a memory step keeps every byte outside Z ---- *)
Definition w7_kept (W : world rsegs) (m m' : word -> option byte) (Zn : Z -> Prop) : Prop :=
forall a, 0 <= a < 2 ^ 64 -> ~ Zn a -> aview rsegs (w_H W) m' a = aview rsegs (w_H W) m a.
Lemma w7_kept_trans : forall W m1 m2 m3 (Z1 Z2 Z3 : Z -> Prop),
w7_kept W m1 m2 Z1 -> w7_kept W m2 m3 Z2 -> (forall a, Z1 a \/ Z2 a -> Z3 a) -> w7_kept W m1 m3 Z3.
Proof.
intros W m1 m2 m3 Z1 Z2 Z3 H12 H23 Hz a Ha Hn.
rewrite (H23 a Ha (fun h => Hn (Hz a (or_intror h)))). exact (H12 a Ha (fun h => Hn (Hz a (or_introl h)))).
Qed.
Lemma w7_kept_mono : forall W m m' (Z1 Z2 : Z -> Prop), w7_kept W m m' Z1 -> (forall a, Z1 a -> Z2 a) -> w7_kept W m m' Z2.
Proof. intros W m m' Z1 Z2 H Hz a Ha Hn. exact (H a Ha (fun h => Hn (Hz a h))). Qed.
Lemma w7_kept_refl : forall W m Zn, w7_kept W m m Zn.
Proof. intros W m Zn a _ _. reflexivity. Qed.

(* ---- the shadow hull of [x, x + n) ---- *)
Definition w7_hull (x n a : Z) : Prop := shadow_addr x / 8 * 8 <= a < shadow_addr (x + n - 1) / 8 * 8 + 8.

Lemma w7_ra_kept : forall (W : world rsegs) m m' x n,
range_addressable (aview rsegs (w_H W) m) SHADOW_OFF x n -> 0 <= x ->
(forall a, w7_hull x n a -> aview rsegs (w_H W) m' a = aview rsegs (w_H W) m a) ->
range_addressable (aview rsegs (w_H W) m') SHADOW_OFF x n.
Proof.
intros W m m' x n HR Hx HK y Hy. destruct (HR y Hy) as (s & Hs & Hok). exists s. split; [|exact Hok].
rewrite HK; [exact Hs|]. unfold w7_hull, shadow_of_addr. change SHADOW_OFF with 0x7fff8000.
unfold shadow_addr, SHADOW_OFF.
pose proof (Z.div_le_mono x y 8 ltac:(lia) ltac:(lia)) as M1.
pose proof (Z.div_le_mono y (x + n - 1) 8 ltac:(lia) ltac:(lia)) as M2.
pose proof (Z.mul_div_le (0x7fff8000 + x / 8) 8 ltac:(lia)) as D1.
pose proof (Z.mod_pos_bound (0x7fff8000 + (x + n - 1) / 8) 8 ltac:(lia)) as D2.
pose proof (Z.div_mod (0x7fff8000 + (x + n - 1) / 8) 8 ltac:(lia)) as D3.
assert (0x7fff8000 + x / 8 <= 0x7fff8000 + y / 8) by lia.
split; [|lia].
pose proof (Z.div_le_mono (0x7fff8000 + x / 8) (0x7fff8000 + y / 8) 8 ltac:(lia) H) as M3.
pose proof (Z.mul_div_le (0x7fff8000 + y / 8) 8 ltac:(lia)). nia.
Qed.
Lemma w7_hull_kept : forall (W : world rsegs) m m' x n,
shadow_hull_vis (aview rsegs (w_H W) m) x n ->
(forall a, w7_hull x n a -> aview rsegs (w_H W) m' a = aview rsegs (w_H W) m a) ->
shadow_hull_vis (aview rsegs (w_H W) m') x n.
Proof. intros W m m' x n HV HK s Hs. rewrite HK by exact Hs. exact (HV s Hs). Qed.

(* ---- the string facts of one call ---- *)
Definition w7_strok (W : world rsegs) (mem : word -> option byte) (R x : Z) (s : list byte) : Prop :=
0 < x /\ Z.of_nat (length s) + 1 < 2 ^ 32 /\ x + Z.of_nat (length s) + 1 <= 2 ^ 63 /\
(forall j, (j < length s)%nat ->
 aview rsegs (w_H W) mem (x + Z.of_nat j) = Some (bv_unsigned (nth j s (Z_to_bv 8 0))) /\
 bv_unsigned (nth j s (Z_to_bv 8 0)) <> 0) /\
aview rsegs (w_H W) mem (x + Z.of_nat (length s)) = Some 0 /\
(forall a, x + Z.of_nat (length s) < a < x + Z.of_nat (length s) - (x + Z.of_nat (length s)) mod 8 + 8 ->
 aview rsegs (w_H W) mem a <> None) /\
(forall a, x <= a <= x + Z.of_nat (length s) -> ~ (R - 2 * ESTACK <= a < R)) /\
amem_range x (Z.of_nat (length s) + 1) /\
range_addressable (aview rsegs (w_H W) mem) SHADOW_OFF x (Z.of_nat (length s) + 1) /\
shadow_hull_vis (aview rsegs (w_H W) mem) x (Z.of_nat (length s) + 1).

(* the bytes a w7_strok fact reads *)
Definition w7_strz (x : Z) (s : list byte) (a : Z) : Prop :=
(x <= a <= x + Z.of_nat (length s) + 8) \/ w7_hull x (Z.of_nat (length s) + 1) a.

Lemma w7_strok_kept : forall W m m' R x s,
w7_strok W m R x s -> (forall a, w7_strz x s a -> aview rsegs (w_H W) m' a = aview rsegs (w_H W) m a) ->
w7_strok W m' R x s.
Proof.
intros W m m' R x s (H0 & H1 & H2 & Hb & Hn & Ht & Hs & Ha & Hr & Hh) HK.
split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
split; [intros j Hj; rewrite HK by (left; lia); exact (Hb j Hj)|].
split; [rewrite HK by (left; lia); exact Hn|].
split; [intros a Hx; rewrite HK; [exact (Ht a Hx)|]; left; pose proof (Z.mod_pos_bound (x + Z.of_nat (length s)) 8); lia|].
split; [exact Hs|]. split; [exact Ha|].
split; [apply (w7_ra_kept W m m'); [exact Hr | lia | intros a Hx; apply HK; right; exact Hx]|].
apply (w7_hull_kept W m m'); [exact Hh | intros a Hx; apply HK; right; exact Hx].
Qed.

Lemma w7_strok_first_byte : forall W m R x s, w7_strok W m R x s ->
first_byte rsegs W m x (Z.of_nat (length s) + 1) 0 (Z.of_nat (length s)).
Proof.
intros W m R x s (_ & _ & _ & Hb & Hn & _).
split; [lia|]. split.
- intros i Hi. destruct (Hb (Z.to_nat i) ltac:(lia)) as [Ha Hz].
  rewrite Z2Nat.id in Ha by lia. eexists. split; [exact Ha | exact Hz].
- intros _. exact Hn.
Qed.

(* an image string: RtPgBase.rt_cstr plus its NUL word's tail in the image and the stack above it *)
Lemma w7_strok_cstr : forall W m R x (l : list byte),
rt_cstr rsegs (w_H W) m x (map (fun b : byte => bv_unsigned b) l) ->
(forall a, x + Z.of_nat (length l) < a < x + Z.of_nat (length l) - (x + Z.of_nat (length l)) mod 8 + 8 ->
 aview rsegs (w_H W) m a <> None) ->
x + Z.of_nat (length l) < R - 2 * ESTACK -> (length l <= 64)%nat ->
w7_strok W m R x l.
Proof.
intros W m R x l (Hb & Hn & Hz & H0 & Hhi & _ & Ham & Hra & Hhv) Ht Hst Hl.
rewrite length_map in Hb, Hn, Hhi, Ham, Hra, Hhv.
split; [exact H0|]. split; [lia|]. split; [lia|].
split.
{ intros j Hj. specialize (Hb (Z.of_nat j) ltac:(lia)). rewrite Nat2Z.id in Hb.
  rewrite rtm_nth_map in Hb.
  split; [exact Hb|].
  rewrite Forall_forall in Hz. specialize (Hz (bv_unsigned (nth j l (Z_to_bv 8 0)))).
  assert (0 < bv_unsigned (nth j l (Z_to_bv 8 0)) < 256); [|lia].
  apply Hz. rewrite <- rtm_nth_map. apply nth_In. rewrite length_map. exact Hj. }
split; [exact Hn|]. split; [exact Ht|].
split; [intros a Ha; lia|].
split; [exact Ham|]. split; [exact Hra | exact Hhv].
Qed.

(* ---- __asan_memcpy in the journal, keeping the I/O state [YCbq.v aj_intrin_at] ---- *)
Section d.
Variable B : asyms.
Hypothesis LAWS : AR_laws rsegs B.
Lemma w7_memcpy_at : aintrin_realizes rsegs B OCpy W7_MEMCPY ->
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k d x n (o : Z) raw,
ajournal rsegs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
getr regsT 10 = w64 d -> getr regsT 11 = w64 x -> getr regsT 12 = w64 n -> 0 <= n < 2 ^ 32 -> 0 <= d -> d + n <= 2 ^ 63 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
(forall a, d <= a < d + n -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ ~ (sp0 + o - ESTACK <= a < sp0 + o)) ->
amem_range d n ->
range_addressable (aview rsegs (w_H W) memT) SHADOW_OFF d n ->
(0 < n -> shadow_hull_vis (aview rsegs (w_H W) memT) d n) ->
0 <= x -> x + n <= 2 ^ 63 -> src_ok rsegs W regsT memT x n -> (d + n <= x \/ x + n <= d) -> amem_range x n ->
range_addressable (aview rsegs (w_H W) memT) SHADOW_OFF x n -> (0 < n -> shadow_hull_vis (aview rsegs (w_H W) memT) x n) ->
SRr rsegs W (mkCfg (mkst regsT (Z_to_bv 64 W7_MEMCPY) memT (seg_rom rsegs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom rsegs)) md2 /\
ajournal rsegs B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\ same_io mdc md2 /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 d /\
(forall i, 0 <= i < n -> aview rsegs (w_H W) mem2 (d + i) = aview rsegs (w_H W) memT (x + i)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (sp0 + o - ESTACK <= a < sp0 + o) -> aview rsegs (w_H W) mem2 a = aview rsegs (w_H W) memT a) /\
(forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
intros AI W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k d x n o raw
HJ Ha0 Ha1 Ha2 Hn Hd0 Hdn Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hdest Hamr Hra_d Hhull Hx0 Hxn Hsx Hdis Hamx Hrax Hhx.
pose proof w7_segs_low as Hsegs.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
assert (ESTACK = 4096) as Hes by reflexivity. assert (ASTACK = 16384) as Has by reflexivity.
assert (HPRE : ecall_pre rsegs B lyc Sc W regsT memT mdc).
{ eapply (ecall_pre_at rsegs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT o); try eassumption. rewrite Hra. exact Hraw. }
assert (HDEST : dest_ok rsegs B lyc Sc W regsT memT d n).
{ intros a Ha. destruct (Hdest a Ha) as [Hw Hns].
  destruct (awr_byte_present rsegs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ Hw) as [Hp Hno]. rewrite Hsp'.
  split; [apply apresent_writable; exact Hp | auto]. }
eapply SRr_mono.
{ exact (AI lyc Sc W regsT memT mdc d x n HPRE Ha0 Ha1 Ha2 Hn Hd0 Hdn HDEST Hamr Hra_d Hhull
    (conj Hx0 (conj Hxn (conj Hsx (conj Hdis (conj Hamx (conj Hrax Hhx))))))). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hres & Heff & Hfr & Hpres2).
rewrite Hsp' in Hfr.
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (ajournal_after_write rsegs B LAWS Hsegs STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k mem2 md2
    (fun a => (d <= a < d + n) \/ (sp0 + o - ESTACK <= a < sp0 + o)) Sc own HJ).
  - intros a Ha Hna. apply (Hfr a Ha); intros H'; apply Hna; [left | right]; exact H'.
  - exact Hpres2.
  - exact Hsame.
  - intros a [Ha | Ha]; left; [exact (proj1 (Hdest a Ha)) | left; lia].
  - exact HAR2.
  - reflexivity. - reflexivity. - lia. - exact Hfrs. - exact HQT. }
split; [exact (same_io_materialized mdc md2 Hsame)|].
split; [exact HP|]. split; [exact Hres|]. split; [exact Heff|]. split; [exact Hfr | exact Hpres2].
Qed.
End d.
End b.

Print Assumptions w7_strok_kept.
Print Assumptions w7_strok_first_byte.
Print Assumptions w7_strok_cstr.
Print Assumptions w7_memcpy_at.
