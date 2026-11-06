(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: restates text of proofs/cgif/cgif_file_fuzzer/lib/A/AC8j.v:43-78 [Apache-2.0];
   proofs/cgif/cgif_file_fuzzer/lib/A/ACes.v:275-278 [Apache-2.0]; proofs/cgif/cgif_file_fuzzer/lib/A/ACfk.v:194-195
   [Apache-2.0]; proofs/cgif/cgif_file_fuzzer/lib/A/ACh9.v:115-118 [Apache-2.0];
   proofs/cgif/cgif_file_fuzzer/lib/YCbo.v:1570-1572, 1593-1598, 1605-1613 [Apache-2.0 OR MIT]; the
   [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-10: made from proofs/reac-pw/fuzz_role/lib/A/RPgW7bBase.v (w7_field, w7_awr_cons,
   w7_post, w7_post_of_run), RPgCfgChanges.v (kept_run), RPgW7bKit.v (w7_kept, w7_hull, w7_ra_kept, w7_hull_kept,
   w7_strok and its lemmas, w7_memcpy_at) and RPgW7bCall.v (w7_strlen_at, w7_first_byte_cstr, w7_first_byte_bytes,
   w7_no_nul_Forall, w7_dec64_nz, w7_odd_nz, w7_chs_nonzero), all at 97ea9c9eafa, for reac-pw/fuzz_headamp's image B
   (lib/AU/Img0U.v rsegs): the w7_ prefix renamed to e0_, image A's own code tables and pcs dropped, __asan_memcpy at
   image B's 0x51d8c, RPgBase.rl_cstr replaced by HPgBase.hd_cstr (whose last clause gives the NUL word's tail),
   RPgSeg.rs_g_of by HPgSeg.hsu_g_of, and the register-kept and region lemmas taken from lib/AU/HPgSteps.v; its
   e0_post, e0_post_of_run, e0_kept_run, e0_kept, e0_hull, e0_ra_kept, e0_hull_kept, e0_strok, e0_strz, e0_strok_kept
   and e0_strok_first_byte are lib/AU/HPgCaseB.v's cb_* since the dedup. *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; addresses measured on the unstripped twin
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff, same loaded bytes except .note.gnu.build-id): the block-post shape and the
   memory and call kit of the walk of ent_build's case 0 in LLVMFuzzerTestOneInput 0x80c40 (lib/AU/HPgE0Def.v).
   Proves no function (kind: segment lemma).

   THE BLOCK POST. Every block of the walk is a lemma from the block's first pc to a fixed pc in the shape cb_post:
   the world kept, the journal at the block's start layout and state (no event), the I/O state kept (same_io from
   the block's model), every register outside clob kept, every byte outside the block's write set Wr kept, every
   present byte present, and a relation R of the registers and the memory. The layout and the state do not move,
   so blocks chain by SRr_bind without a meter law. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Tables.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A.Rt Require Import StrlenDef WrapRo.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgSteps HPgMem HPgSeg HPgCaseB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the image's two callees of case 0 ---- *)
Definition E0_STRLEN : Z := STRLEN_ENTRY_B.  (* __interceptor_trampoline_strlen 0x41c18 *)
Definition E0_MEMCPY : Z := 0x51d8c.         (* __asan_memcpy *)
(* the shadow base for the engine's shadow tokens: s11 holds K (the runtime's shadow offset), atom 27 *)
Definition E0SB : Z := 0x7fff8000.
Definition E0Bx : sv := SOff 27 0.
Definition E0Bspan : Z * Z := (E0SB, E0SB + 2 ^ 44 - 1).

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

(* ---- engine helpers [cgif lib/A/AC8j.v:43-78] ---- *)
Lemma e0_field : forall E m n b cs lo hi wlo whi od (w : N) e v,
region_ok rsegs E m (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal w e)) cs -> sv_denot E e = Z_to_bv 64 v ->
0 <= v < 2 ^ (8 * Z.of_N w) -> (Z.of_N w <= 8) ->
val_mem rsegs m (b + od) (N.to_nat w) v.
Proof.
intros E m n b cs lo hi wlo whi od w e v (_ & _ & _ & Hcs) Hn Hc He Hv Hw.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. cbn [YP09.r_base base_val] in Hck. rewrite Hn in Hck.
exact (val_of_chunk_ok rsegs E m b od w e v Hck He Hv Hw).
Qed.

Section d.
Variable B : asyms.
Lemma e0_awr_cons : forall E r rs STK sp0 FP bl0 blc ly own n b,
YP09.r_base r = Some n -> bv_unsigned (ew E n) = b ->
(forall a, b + YP09.r_wlo r <= a < b + YP09.r_whi r -> awr_byte STK sp0 FP bl0 blc ly own a) ->
awr_ok E rs STK sp0 FP bl0 blc ly own -> awr_ok E (r :: rs) STK sp0 FP bl0 blc ly own.
Proof.
intros E r rs STK sp0 FP bl0 blc ly own n b Hb Hn Hw H a (r' & [<-|Hin] & Ha).
- rewrite Hb in Ha. cbn [base_val] in Ha. rewrite Hn in Ha. apply Hw. exact Ha.
- apply H. exists r'. auto.
Qed.

End d.

Lemma e0_kept_trans : forall W m1 m2 m3 (Z1 Z2 Z3 : Z -> Prop),
cb_kept W m1 m2 Z1 -> cb_kept W m2 m3 Z2 -> (forall a, Z1 a \/ Z2 a -> Z3 a) -> cb_kept W m1 m3 Z3.
Proof.
intros W m1 m2 m3 Z1 Z2 Z3 H12 H23 Hz a Ha Hn.
rewrite (H23 a Ha (fun h => Hn (Hz a (or_intror h)))). exact (H12 a Ha (fun h => Hn (Hz a (or_introl h)))).
Qed.
Lemma e0_kept_mono : forall W m m' (Z1 Z2 : Z -> Prop), cb_kept W m m' Z1 -> (forall a, Z1 a -> Z2 a) -> cb_kept W m m' Z2.
Proof. intros W m m' Z1 Z2 H Hz a Ha Hn. exact (H a Ha (fun h => Hn (Hz a h))). Qed.
Lemma e0_kept_refl : forall W m Zn, cb_kept W m m Zn.
Proof. intros W m Zn a _ _. reflexivity. Qed.

(* an image string: HPgBase.hd_cstr (its last clause is the NUL word's tail) and the stack above it *)
Lemma e0_strok_cstr : forall W m R x (l : list byte),
hd_cstr rsegs (w_H W) m x (map (fun b : byte => bv_unsigned b) l) ->
x + Z.of_nat (length l) < R - 2 * ESTACK -> (length l <= 64)%nat ->
cb_strok W m R x l.
Proof.
intros W m R x l (Hb & Hn & Hz & H0 & Hhi & _ & Ham & Hra & Hhv & Ht) Hst Hl.
rewrite length_map in Hb, Hn, Hhi, Ham, Hra, Hhv, Ht.
split; [exact H0|]. split; [lia|]. split; [lia|].
split.
{ intros j Hj. specialize (Hb (Z.of_nat j) ltac:(lia)). rewrite Nat2Z.id in Hb.
  rewrite hm_nth_map in Hb.
  split; [exact Hb|].
  rewrite Forall_forall in Hz. specialize (Hz (bv_unsigned (nth j l (Z_to_bv 8 0)))).
  assert (0 < bv_unsigned (nth j l (Z_to_bv 8 0)) < 256); [|lia].
  apply Hz. rewrite <- hm_nth_map. apply nth_In. rewrite length_map. exact Hj. }
split; [exact Hn|]. split; [exact Ht|].
split; [intros a Ha; lia|].
split; [exact (hd_amem_range_le x (Z.of_nat (length l) + 1) (Z.of_nat (length l) + 8) ltac:(lia) Ham)|].
split; [exact Hra | exact Hhv].
Qed.

(* ---- first_byte of a NUL-terminated string ---- *)
Lemma e0_first_byte_cstr : forall (W : world rsegs) mem x s, hd_cstr rsegs (w_H W) mem x s ->
first_byte rsegs W mem x (Z.of_nat (length s) + 1) 0 (Z.of_nat (length s)).
Proof.
intros W mem x s (Hb & Hnul & Hrng & _).
split; [lia|]. split.
- intros i Hi. exists (nth (Z.to_nat i) s 0). split; [exact (Hb i Hi)|].
  assert (Hin : In (nth (Z.to_nat i) s 0) s) by (apply nth_In; lia).
  pose proof (proj1 (Forall_forall _ _) Hrng _ Hin) as Hr. cbn beta in Hr. lia.
- intros _. exact Hnul.
Qed.

Lemma e0_first_byte_bytes : forall (W : world rsegs) mem x (s : list byte),
garr8 rsegs (mrestrict (w_H W) mem) x (map (fun b : byte => bv_unsigned b) (s ++ [Cursor.NUL])) ->
Forall (fun b : byte => bv_unsigned b <> 0) s ->
first_byte rsegs W mem x (Z.of_nat (length s) + 1) 0 (Z.of_nat (length s)).
Proof.
intros W mem x s Hg Hnz.
assert (Hlen : length (map (fun b : byte => bv_unsigned b) (s ++ [Cursor.NUL])) = S (length s))
  by (rewrite length_map, length_app; cbn [length]; lia).
assert (Hnth : forall j, (j <= length s)%nat ->
  nth j (map (fun b : byte => bv_unsigned b) (s ++ [Cursor.NUL])) 0 = bv_unsigned (nth j (s ++ [Cursor.NUL]) Cursor.NUL)).
{ intros j Hj.
  rewrite (nth_indep _ 0 (bv_unsigned Cursor.NUL)) by (rewrite Hlen; lia).
  rewrite map_nth. reflexivity. }
assert (Hv : forall j, (j <= length s)%nat ->
  aview rsegs (w_H W) mem (x + Z.of_nat j) = Some (bv_unsigned (nth j (s ++ [Cursor.NUL]) Cursor.NUL))).
{ intros j Hj. destruct (Hg j ltac:(rewrite Hlen; lia)) as [Hm Hr].
  rewrite (Hnth j Hj) in Hm, Hr.
  exact (hm_val1_aview rsegs (w_H W) mem _ _ Hm Hr). }
split; [lia|]. split.
- intros i Hi. exists (bv_unsigned (nth (Z.to_nat i) (s ++ [Cursor.NUL]) Cursor.NUL)).
  split.
  + replace (x + i) with (x + Z.of_nat (Z.to_nat i)) by lia. apply Hv. lia.
  + rewrite app_nth1 by lia. apply (proj1 (Forall_forall _ _) Hnz). apply nth_In. lia.
- intros _. rewrite (Hv (length s) ltac:(lia)). rewrite nth_middle. reflexivity.
Qed.
End b.

(* ---- the key's first part has no zero byte ---- *)
Lemma e0_dec64_chk : forallb (fun n => no_nul (dec64 (Z.of_nat n))) (seq 0 64) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma e0_no_nul_Forall : forall l, no_nul l = true -> Forall (fun b : byte => bv_unsigned b <> 0) l.
Proof.
intros l H. apply Forall_forall. intros b Hb. unfold no_nul in H.
pose proof (proj1 (forallb_forall _ _) H b Hb) as Hq. cbn beta in Hq.
apply negb_true_iff, Z.eqb_neq in Hq. exact Hq.
Qed.
Lemma e0_dec64_nz : forall v, 0 <= v < 64 -> Forall (fun b : byte => bv_unsigned b <> 0) (dec64 v).
Proof.
intros v Hv. apply e0_no_nul_Forall.
pose proof (proj1 (forallb_forall _ _) e0_dec64_chk (Z.to_nat v) ltac:(apply in_seq; lia)) as Hq.
cbn beta in Hq. rewrite Z2Nat.id in Hq by lia. exact Hq.
Qed.
Lemma e0_odd_nz : forall n, no_nul (nth n odd_ch []) = true.
Proof.
intros n. pose proof tables_no_nul as Ht. apply andb_true_iff in Ht as [Ht _].
apply andb_true_iff in Ht as [Ht _]. apply andb_true_iff in Ht as [Ht _]. apply andb_true_iff in Ht as [Ht _].
apply andb_true_iff in Ht as [_ Ho].
destruct (nth_in_or_default n odd_ch []) as [Hin | ->].
- exact (proj1 (forallb_forall _ _) Ho _ Hin).
- reflexivity.
Qed.
Lemma e0_chs_nonzero : forall rr chs pb r, (chs, pb, r) = hsu_g_of rr ->
Forall (fun b : byte => bv_unsigned b <> 0) chs.
Proof.
intros rr chs pb r H.
assert (Hc : chs = fst (fst (hsu_g_of rr))) by (rewrite <- H; reflexivity).
clear H. subst chs. unfold hsu_g_of.
destruct (Cursor.fuzz_u8 rr) as [k0 r1]. destruct (Cursor.fuzz_u8 r1) as [c r2]. destruct (Cursor.fuzz_u8 r2) as [pb' r3].
cbn [fst]. destruct (c <? 200).
- apply e0_dec64_nz. apply Z.mod_pos_bound. lia.
- apply e0_no_nul_Forall. exact (e0_odd_nz (Z.to_nat (c mod 14))).
Qed.

(* ---- the two callees in the journal, keeping the I/O state ---- *)
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d2.
Variable B : asyms.
Hypothesis LAWS : AR_laws rsegs B.

(* __asan_memcpy [YCbq.v aj_intrin_at] *)
Lemma e0_memcpy_at : aintrin_realizes rsegs B OCpy E0_MEMCPY ->
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
SRr rsegs W (mkCfg (mkst regsT (Z_to_bv 64 E0_MEMCPY) memT (seg_rom rsegs)) mdc)
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
pose proof img_segs_low as Hsegs.
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

(* The strlen wrapper in the journal form (lib/A/Rt/StrlenDef.v astrlen_realizes at the call's pc). *)
Lemma e0_strlen_at : forall pc, astrlen_realizes rsegs B pc ->
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc kj x k (o : Z) raw,
ajournal rsegs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc kj ->
getr regsT 10 = w64 x -> 0 < x -> 0 <= k -> k + 1 < 2 ^ 32 -> x + k + 1 <= 2 ^ 63 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 2 * ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
first_byte rsegs W memT x (k + 1) 0 k ->
src_ok rsegs W regsT memT x (k + 1) ->
(forall a, x <= a <= x + k -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o)) ->
amem_range x (k + 1) ->
range_addressable (aview rsegs (w_H W) memT) SHADOW_OFF x (k + 1) ->
shadow_hull_vis (aview rsegs (w_H W) memT) x (k + 1) ->
(forall a, x + k < a < x + k - (x + k) mod 8 + 8 -> aview rsegs (w_H W) memT a <> None) ->
aro_unowned rsegs B (aview rsegs (w_H W) memT) ->
SRr rsegs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom rsegs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom rsegs)) md2 /\
ajournal rsegs B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 kj /\ same_io mdc md2 /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 k /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o) -> aview rsegs (w_H W) mem2 a = aview rsegs (w_H W) memT a) /\
(forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof using LAWS.
intros pc AM W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc kj x k o raw
HJ Ha0 Hx0 Hk0 Hk1 Hxk Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hfb Hsx Hbx Hmx Hrx Hhx Htl Hro.
pose proof img_segs_low as Hsegs.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
assert (ESTACK = 4096) as Hes by reflexivity. assert (ASTACK = 16384) as Has by reflexivity.
assert (HPRE : ecall_pre rsegs B lyc Sc W regsT memT mdc).
{ eapply ecall_pre_at with (o := o); try eassumption; try zlia. rewrite Hra. exact Hraw. }
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (Hlo2 : ly_stk_lo lyc + 2 * ESTACK <= spZ regsT) by (rewrite Eslo, Hsp'; zlia).
assert (Hpres2E : forall a, spZ regsT - 2 * ESTACK <= a < spZ regsT -> apresent (w_H W) memT a)
  by (intros a Ha; apply Hpres; rewrite Hsp' in Ha; zlia).
eapply SRr_mono.
{ exact (AM lyc Sc W regsT memT mdc x k HPRE Hlo2 Hpres2E Ha0 Hx0 Hk0 Hk1 Hxk Hfb Hsx
    ltac:(rewrite Hsp'; exact Hbx) Hmx Hrx Hhx Htl Hro). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hres & Hfr & Hpres2).
rewrite Hsp' in Hfr.
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (ajournal_after_write rsegs B LAWS img_segs_low STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc kj mem2 md2
    (fun a => sp0 + o - 2 * ESTACK <= a < sp0 + o) Sc own HJ).
  - intros a Ha Hna. apply (Hfr a Ha). exact Hna.
  - exact Hpres2.
  - exact Hsame.
  - intros a Ha; left; left; zlia.
  - exact HAR2.
  - reflexivity. - reflexivity. - zlia. - exact Hfrs. - exact HQT. }
split; [exact (same_io_materialized _ _ Hsame)|].
split; [exact HP|]. split; [exact Hres|]. split; [exact Hfr | exact Hpres2].
Qed.
End d2.
End c.

Print Assumptions e0_field.
Print Assumptions e0_strok_cstr.
Print Assumptions e0_first_byte_bytes.
Print Assumptions e0_chs_nonzero.
Print Assumptions e0_memcpy_at.
Print Assumptions e0_strlen_at.
