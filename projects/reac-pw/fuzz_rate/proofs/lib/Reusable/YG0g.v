(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YG0g.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_knock/lib/Reusable/YG0g.v at origin/ossv/recipes 6ebe35ba632 (fuzz_knock's released ASan tree); module paths changed to reac-pw/fuzz_rate. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YP09 YK04 YA0i YA0n YK08 YK0v YK13 YA05 YA06 YG0b.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YP0n.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YK0g.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG0f YG0v YG0n YG0s YG0q YG08 YG0h YG0j.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Open Scope Z_scope.
Lemma needs_remap_false : forall n', n' < 2 ^ 66 -> needs_remap n' = false.
Proof.
intros n' H. unfold needs_remap, kClearShadowMmapThreshold. apply Z.leb_gt.
assert (n' / 8 < 2 ^ 63) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.
Definition shna (md : Model) : Prop :=
region_free (vm_noaccess (m_vmmaps md)) (w64 kLowShadowBeg) (w64 (kLowShadowEnd - kLowShadowBeg)) = true /\
region_free (vm_noaccess (m_vmmaps md)) (w64 kHighShadowBeg) (w64 (kHighShadowEnd - kHighShadowBeg)) = true.
Lemma shna_same : forall md md', vm_noaccess (m_vmmaps md') = vm_noaccess (m_vmmaps md) -> shna md -> shna md'.
Proof. intros md md' E H. unfold shna. rewrite E. exact H. Qed.
Lemma shna_subtract : forall md md' lo hi,
(forall q, In q (vm_noaccess (m_vmmaps md)) -> bv_unsigned (fst q) + bv_unsigned (snd q) <= 2 ^ 64) ->
vm_noaccess (m_vmmaps md') = maps_subtract (vm_noaccess (m_vmmaps md)) lo hi -> shna md -> shna md'.
Proof.
intros md md' lo hi Hwf E [H1 H2]. unfold shna. rewrite E. split; apply region_free_subtract; assumption.
Qed.
Lemma shna_of_uncovered : forall md,
(forall q, In q (vm_noaccess (m_vmmaps md)) -> 0 < bv_unsigned (snd q)) ->
(forall x, kLowShadowBeg <= x < kLowShadowEnd \/ kHighShadowBeg <= x < kHighShadowEnd -> YK0g.covered (vm_noaccess (m_vmmaps md)) x = false) ->
shna md.
Proof.
intros md Hpos Hcov. split; apply region_free_of_uncovered; try exact Hpos.
- unfold w64. rewrite Z_to_bv_unsigned. vm_compute. reflexivity.
- intros x Hx. apply Hcov. left. unfold w64, kLowShadowBeg, kLowShadowEnd in *. rewrite !Z_to_bv_unsigned in Hx.
rewrite !bv_wrap_small in Hx by (change (bv_modulus 64) with (2 ^ 64); lia). lia.
- unfold w64. rewrite Z_to_bv_unsigned. vm_compute. reflexivity.
- intros x Hx. apply Hcov. right. unfold w64, kHighShadowBeg, kHighShadowEnd in *. rewrite !Z_to_bv_unsigned in Hx.
rewrite !bv_wrap_small in Hx by (change (bv_modulus 64) with (2 ^ 64); lia). lia.
Qed.
Lemma shna_madvise : forall md a n, shna md -> shna (madvise_dontneed_next md a n).
Proof. intros md a n H. apply (shna_same md); [reflexivity | exact H]. Qed.
Lemma na_wf_of_amwf : forall md, amwf md -> forall q, In q (vm_noaccess (m_vmmaps md)) -> bv_unsigned (fst q) + bv_unsigned (snd q) <= 2 ^ 64.
Proof. intros md [(_ & W2 & _) _]. exact W2. Qed.
Lemma shna_munmap : forall md (a n : word), amwf md -> shna md -> shna (munmap_model a n md).
Proof.
intros md a n MW H. apply (shna_subtract md _ (bv_unsigned a) (bv_unsigned a + bv_unsigned n) (na_wf_of_amwf md MW)); [|exact H].
destruct md as [fd [maps lz mt] io fs proc lim tm]. reflexivity.
Qed.
Lemma shna_mmap_model : forall flags md (a n : word), shna md -> shna (with_mmap_backing flags a n (mmap_model a n md)).
Proof.
intros flags md a n H. apply (shna_same md); [|exact H].
unfold with_mmap_backing. destruct (mmap_noreserve_b flags); destruct md as [fd [maps lz mt] io fs proc lim tm]; reflexivity.
Qed.
Lemma shna_grant_md : forall (hole : bool) flags md (a n : word), amwf md -> shna md -> shna (grant_md hole flags a n md).
Proof.
intros hole flags md a n MW H. unfold grant_md. destruct hole.
- apply shna_mmap_model. exact H.
- apply (shna_subtract md _ (bv_unsigned a) (bv_unsigned a + bv_unsigned n) (na_wf_of_amwf md MW)); [|exact H].
unfold fixedin_ok_model, fixedin_ok_vmmaps, with_mmap_replacement, with_mmap_backing. change (Z.eqb 3 0) with false. cbv iota.
destruct (mmap_noreserve_b flags); destruct md as [fd [maps lz mt] io fs proc lim tm]; reflexivity.
Qed.
Lemma naf_same : forall md md', vm_noaccess (m_vmmaps md') = vm_noaccess (m_vmmaps md) ->
forall lo n, region_free (vm_noaccess (m_vmmaps md)) lo n = true -> region_free (vm_noaccess (m_vmmaps md')) lo n = true.
Proof. intros md md' E lo n H. rewrite E. exact H. Qed.
Lemma naf_grant_md : forall (hole : bool) flags md (a n : word), amwf md ->
forall lo k, region_free (vm_noaccess (m_vmmaps md)) lo k = true -> region_free (vm_noaccess (m_vmmaps (grant_md hole flags a n md))) lo k = true.
Proof.
intros hole flags md a n MW lo k H. unfold grant_md. destruct hole.
- apply (naf_same md); [|exact H]. unfold with_mmap_backing. destruct (mmap_noreserve_b flags); destruct md as [fd [maps lz mt] io fs proc lim tm]; reflexivity.
- assert (E : vm_noaccess (m_vmmaps (fixedin_ok_model 3 flags a n md)) = maps_subtract (vm_noaccess (m_vmmaps md)) (bv_unsigned a) (bv_unsigned a + bv_unsigned n)).
{ unfold fixedin_ok_model, fixedin_ok_vmmaps, with_mmap_replacement, with_mmap_backing. change (Z.eqb 3 0) with false. cbv iota.
destruct (mmap_noreserve_b flags); destruct md as [fd [maps lz mt] io fs proc lim tm]; reflexivity. }
rewrite E. apply region_free_subtract; [exact (na_wf_of_amwf md MW) | exact H].
Qed.
Lemma mrestrict_zfill_out : forall (Hh : word -> bool) (a nw : word) (m : word -> option byte) z,
0 <= z < 2 ^ 64 -> (z < bv_unsigned a \/ bv_unsigned a + bv_unsigned nw <= z) ->
mrestrict Hh (zfill a nw m) (Z_to_bv 64 z) = mrestrict Hh m (Z_to_bv 64 z).
Proof.
intros Hh a nw m z Hz Ho. unfold mrestrict. destruct (Hh (Z_to_bv 64 z)); [reflexivity|]. apply zfill_out.
unfold w64. rewrite Z_to_bv_unsigned, bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); lia). exact Ho.
Qed.
Lemma SRr_madvise_pg : forall (segs : list Segment) (W : world segs) regs (pc : word) mem rom md (PB n : Z) (Q : world segs -> config -> Prop),
getr regs 17 = Z_to_bv 64 233 -> getr regs 10 = Z_to_bv 64 PB -> getr regs 11 = Z_to_bv 64 n -> getr regs 12 = Z_to_bv 64 4 ->
0 <= PB -> PB mod 4096 = 0 -> 0 < n -> n mod 4096 = 0 -> PB + n < 2 ^ 64 ->
madvise_dontneed_ok (m_vmmaps md) (Z_to_bv 64 PB) (Z_to_bv 64 n) = true ->
SRr segs W (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) (zfill (Z_to_bv 64 PB) (Z_to_bv 64 n) mem) rom)
(madvise_dontneed_next md (Z_to_bv 64 PB) (Z_to_bv 64 n))) Q ->
SRr segs W (mkCfg (YP0n.pend_at regs pc mem rom) md) Q.
Proof.
intros segs W regs pc mem rom md PB n Q H17 H10 H11 H12 HP0 HPal Hn Hnal Hnw Hgate HK.
assert (Hru : page_round_up_Z n = n).
{ unfold page_round_up_Z, page_size. pose proof (Z.div_mod n 4096 ltac:(lia)) as D. rewrite Hnal, Z.add_0_r in D.
replace (n + 4096 - 1) with (4095 + n / 4096 * 4096) by lia. rewrite Z.div_add by lia. change (4095 / 4096) with 0. lia. }
assert (UP : bv_unsigned (Z_to_bv 64 PB) = PB) by (rewrite Z_to_bv_unsigned, bv_wrap_small; [reflexivity | change (bv_modulus 64) with (2 ^ 64); lia]).
apply (SRr_madvise segs W regs pc mem rom md (Z_to_bv 64 PB) n Q H17 H10); try assumption.
- rewrite UP. exact HPal.
- rewrite UP, Hru. exact Hnw.
- cbv zeta. rewrite Hru. exact Hgate.
- cbv zeta. rewrite Hru. exact HK.
Qed.
Section d.
Variable segs : list Segment.
Theorem madvise_gate : forall ly S md (b n : Z),
layout_ok ly -> ALedger segs ly S md -> shna md ->
0 < n ->
(kLowShadowBeg <= b /\ b + n <= kLowShadowEnd \/ kHighShadowBeg <= b /\ b + n <= kHighShadowEnd) ->
madvise_dontneed_ok (m_vmmaps md) (w64 b) (w64 n) = true.
Proof.
intros ly S md b n LO L [N1 N2] Hn Hin.
assert (Rb : 0 <= b /\ b + n < 2 ^ 63) by (unfold kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Hin; lia).
assert (Ub : bv_unsigned (w64 b) = b) by (apply w64_unsigned; lia).
assert (Un : bv_unsigned (w64 n) = n) by (apply w64_unsigned; lia).
assert (HR : region_free (vm_reserved (m_vmmaps md)) (w64 b) (w64 n) = true).
{ rewrite (al_reserved _ _ _ _ L). apply (region_free_reserved segs); [exact (al_img_env segs ly S md LO L) | | lia | lia].
unfold kImgEnd, kLowShadowBeg, kHighShadowBeg in *. lia. }
destruct Hin as [[I1 I2]|[I1 I2]].
- apply (madvise_gate_intro _ (wiv (kLowShadowBeg, kLowShadowEnd - kLowShadowBeg))).
+ apply (al_band _ _ _ _ L). left. reflexivity.
+ unfold wiv. cbn [fst snd]. rewrite Ub, w64_unsigned by (unfold kLowShadowBeg; lia). exact I1.
+ unfold wiv. cbn [fst snd]. rewrite Ub, Un, !w64_unsigned by (unfold kLowShadowBeg, kLowShadowEnd; lia). lia.
+ exact HR.
+ apply (region_free_sub _ _ _ _ _ N1); rewrite ?Ub, ?Un, !w64_unsigned by (unfold kLowShadowBeg, kLowShadowEnd; lia); lia.
- apply (madvise_gate_intro _ (wiv (kHighShadowBeg, kHighShadowEnd - kHighShadowBeg))).
+ apply (al_band _ _ _ _ L). right. right. left. reflexivity.
+ unfold wiv. cbn [fst snd]. rewrite Ub, w64_unsigned by (unfold kHighShadowBeg; lia). exact I1.
+ unfold wiv. cbn [fst snd]. rewrite Ub, Un, !w64_unsigned by (unfold kHighShadowBeg, kHighShadowEnd; lia). lia.
+ exact HR.
+ apply (region_free_sub _ _ _ _ _ N2); rewrite ?Ub, ?Un, !w64_unsigned by (unfold kHighShadowBeg, kHighShadowEnd; lia); lia.
Qed.
Lemma al_shna_shna : forall ly S md, ALedger segs ly S md -> shna md.
Proof. intros ly S md L. exact (al_shna _ _ _ _ L). Qed.
Corollary madvise_gate_L : forall ly S md (b n : Z),
layout_ok ly -> ALedger segs ly S md -> 0 < n ->
(kLowShadowBeg <= b /\ b + n <= kLowShadowEnd \/ kHighShadowBeg <= b /\ b + n <= kHighShadowEnd) ->
madvise_dontneed_ok (m_vmmaps md) (w64 b) (w64 n) = true.
Proof. intros ly S md b n LO L. exact (madvise_gate ly S md b n LO L (al_shna_shna ly S md L)). Qed.
Lemma same_io_madvise : forall a n md, same_io md (madvise_dontneed_next md a n).
Proof. intros a n md. unfold madvise_dontneed_next. apply same_io_with_vm_backing. Qed.
Lemma amwf_madvise : forall md a n, amwf md -> amwf (madvise_dontneed_next md a n).
Proof. intros md a n H. apply (amwf_same md); [reflexivity | reflexivity | exact H]. Qed.
Lemma ALedger_madvise : forall ly S md a n, ALedger segs ly S md -> ALedger segs ly S (madvise_dontneed_next md a n).
Proof. intros ly S md a n L. apply (ALedger_same segs ly S md); [exact L | reflexivity | reflexivity | reflexivity]. Qed.
End d.
End c.
