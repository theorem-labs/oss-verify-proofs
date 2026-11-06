(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: relocated from libreac/fuzz_disco (a working branch 91c9538449b, proofs/libreac/fuzz_disco/lib/A/Rt/Memchr.v) to fuzz_identity.asan by an address map recorded by the porting lane; module paths, the record class TfibSyms (unchanged). *)
(* Modified by Theorem Labs, 2026-10: bridged to identity's contract: Section h takes aro_unowned over the view of memory in place of consts_view and gets the walk's mconsts_view from WrapRoM.mconsts_of_aro; disco's memchr_icpt_realizesM and memchr_icpt_realizes are replaced by memchr_icpt_contract for amemchr_realizes (lib/A/Rt/MemchrDef.v). *)
(* Modified by Theorem Labs, 2026-10: cgif_file_fuzzer lib/A/AE6x.v's walk of the memchr wrapper, generalised to any byte c in a1 and to a window that may hold no c: the musl call is MemchrMusl's walk, and after it the found case keeps AE6x's check (AE6y, count a0 - s2 + 1) while the not-found case takes the twin check of MemchrChk (count s1). *)
(* Modified by Theorem Labs, 2026-10-29: for a Theorem Labs lane's acceptance (a working branch), the record class is TfibSyms, not IdentTfibSyms, and the core modules are Required by full path at the applied A core's names (lib/A/A*.v, lib/Reusable/YA0m, YE08, YE21). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Rt/Memchr.v, with its module paths, module names and numbers changed; 230 of its 297 lines of code are new or changed and 507 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_identity/lib/A/FMstrlen.v at 6ebe35ba632; the tail of sl_tail (the range check by its interface, the epilogue by a symbolic run, the register and frame bookkeeping) is redone for the strcspn wrapper of reac-pw/fuzz_pin.asan: the range check of the set and the range check of the string by the interfaces of lib/A/FMcs0.v, then the epilogue at 0x42de0, which restores ten saved words. *)
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
Require Import
  OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A.AB1v
  OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A.AE34
  OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A.AF0l
  OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A.AF0m
  OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A.AF0x
  OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A.AB1w
  OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A.AE20
  OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A.AE2y
  OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A.AE3a.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YN01.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A Require PPgWrap.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A Require Import FMcs0.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* ---- small facts the composition uses ---- *)
(* the result of musl strcspn is at most the length of the string *)
Lemma cspn_le : forall set s, (PPgWrap.cspn_len set s <= length s)%nat.
Proof.
intros set s. induction s as [|b s IH]; cbn [PPgWrap.cspn_len length]; [lia|].
lazymatch goal with |- context [if ?t then _ else _] => destruct t end; lia.
Qed.
Lemma acs_of : forall z, existsb (Z.eqb z) [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] = true -> acallee_saved z.
Proof.
intros z Hz. apply existsb_exists in Hz as (q & Hq & Hzq). apply Z.eqb_eq in Hzq. subst q.
unfold acallee_saved. cbn [In] in Hq. lia.
Qed.
(* gp, tp, s4, s8 .. s11 are not written between the entry and 0x42de0 (CS_KEPT and the keep clauses of the two
   range checks); s4 and s8 also come back from the saved words, so only 3, 4, 25, 26, 27 are taken from here *)
Lemma chain_kept : forall (regs regs1 regs2 regs3 : bvmap 5 word) z,
(forall q, In q CS_KEPT -> getr regs1 (Z_to_bv 5 q) = getr regs (Z_to_bv 5 q)) ->
(forall r, acallee_saved r -> r <> 18 -> getr regs2 (Z_to_bv 5 r) = getr regs1 (Z_to_bv 5 r)) ->
(forall r, acallee_saved r -> r <> 9 -> r <> 18 -> r <> 19 -> getr regs3 (Z_to_bv 5 r) = getr regs2 (Z_to_bv 5 r)) ->
existsb (Z.eqb z) [3; 4; 25; 26; 27] = true -> getr regs3 (Z_to_bv 5 z) = getr regs (Z_to_bv 5 z).
Proof.
intros regs regs1 regs2 regs3 z MK K2 K3 Hz.
apply existsb_exists in Hz as (q & Hq & Hzq). apply Z.eqb_eq in Hzq. subst q.
assert (Hc : z = 3 \/ z = 4 \/ z = 25 \/ z = 26 \/ z = 27) by (cbn [In] in Hq; lia).
rewrite K3 by (unfold acallee_saved; lia).
rewrite K2 by (unfold acallee_saved; lia).
apply MK. unfold CS_KEPT. cbn [In]. lia.
Qed.
Lemma saved_off : forall j rz off, nth_error CS_SAVED j = Some (rz, off) -> -80 <= off <= -8.
Proof.
intros j rz off Hj.
do 10 (destruct j as [|j]; [cbn in Hj; injection Hj as <- <-; lia|]).
destruct j; discriminate.
Qed.
Lemma amem_range_sub : forall p n m, 0 <= n <= m -> amem_range p m -> amem_range p n.
Proof. unfold amem_range. intros p n m Hn Hm. lia. Qed.
(* the shadow bytes of a prefix [p, p + n) of an addressable range [p, p + m), read through a reader that agrees on
   the shadow band *)
Lemma ra_transfer : forall (rd rd' : Z -> option Z) p n m,
0 < p -> 1 <= n <= m -> p + m <= kHighMemEnd ->
(forall s, SHADOW_OFF - 8 <= s < kHighShadowEnd + 8 -> rd' s = rd s) ->
range_addressable rd SHADOW_OFF p m -> range_addressable rd' SHADOW_OFF p n.
Proof.
intros rd rd' p n m Hp Hn Hm Hag Hra.
apply (range_addressable_agree rd rd').
- intros z Hz. apply Hag. change (shadow_of_addr SHADOW_OFF z) with (shadow_addr z).
  pose proof (AE2y.shadow_addr_bounds z ltac:(unfold kHighMemEnd in *; lia)) as [B1 B2].
  unfold kLowMemEnd, kHighShadowEnd, SHADOW_OFF in *. lia.
- apply (range_addressable_sub rd SHADOW_OFF p m p n Hra); lia.
Qed.
Lemma hull_transfer : forall (rd rd' : Z -> option Z) p n m,
0 < p -> 1 <= n <= m -> p + m <= kHighMemEnd ->
(forall s, SHADOW_OFF - 8 <= s < kHighShadowEnd + 8 -> rd' s = rd s) ->
shadow_hull_vis rd p m -> shadow_hull_vis rd' p n.
Proof.
intros rd rd' p n m Hp Hn Hm Hag Hh s Hs.
pose proof (AE2y.shadow_addr_bounds p ltac:(unfold kHighMemEnd in *; lia)) as [B1 B2].
pose proof (AE2y.shadow_addr_bounds (p + n - 1) ltac:(unfold kHighMemEnd in *; lia)) as [T1 T2].
assert (Mono : shadow_addr (p + n - 1) / 8 <= shadow_addr (p + m - 1) / 8).
{ apply Z.div_le_mono; [lia|]. unfold shadow_addr. apply Z.add_le_mono_l. apply Z.div_le_mono; lia. }
pose proof (Z.div_mod (shadow_addr p) 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound (shadow_addr p) 8 ltac:(lia)) as D2.
pose proof (Z.div_mod (shadow_addr (p + n - 1)) 8 ltac:(lia)) as D3.
pose proof (Z.mod_pos_bound (shadow_addr (p + n - 1)) 8 ltac:(lia)) as D4.
rewrite Hag.
- apply Hh. lia.
- unfold kLowMemEnd, kHighShadowEnd, SHADOW_OFF in *. lia.
Qed.

(* ---- the epilogue 0x42de0 .. 0x42e10: sp += 0x80; ra, s0 .. s8 come back from sp0 - 8 .. sp0 - 80; sp += 0x7f0;
   ret.  The sp at 0x42de0 is sp0 - 2160 (CS_FRAME), so the ten words are at offsets 2152 .. 2080 from it. ---- *)
Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition cs_epi_run (s : sstate) := sym_runN tfibsegs tbl_cs FUEL s.
Definition cs_epi_chunks : list YP09.chunk :=
[YP09.mkChunk 2152 (CVal 8 (SOff 32 0)); YP09.mkChunk 2144 (CVal 8 (SOff 33 0));
YP09.mkChunk 2136 (CVal 8 (SOff 34 0)); YP09.mkChunk 2128 (CVal 8 (SOff 35 0));
YP09.mkChunk 2120 (CVal 8 (SOff 36 0)); YP09.mkChunk 2112 (CVal 8 (SOff 37 0));
YP09.mkChunk 2104 (CVal 8 (SOff 38 0)); YP09.mkChunk 2096 (CVal 8 (SOff 39 0));
YP09.mkChunk 2088 (CVal 8 (SOff 40 0)); YP09.mkChunk 2080 (CVal 8 (SOff 41 0))].
Definition cs_ss_epi : sstate :=
mkSS CS2_END sr_atoms [YP09.mkRegion (Some 2%nat) 0 CS_FRAME 0 0 cs_epi_chunks] None (mkFacts [(2%nat, mkAF (2^43) (2^47) 4)] [] []).
Definition cs_epi_e : sstate := Eval vm_compute in fst (cs_epi_run cs_ss_epi).
Lemma cs_r_epi : cs_epi_run cs_ss_epi = (cs_epi_e, RS_stopped (SR_jalr (SOff 32 0))). Proof. vm_compute. reflexivity. Qed.
End e.

(* ---- 0x42d38 to the return: the range check of the set, the range check of the string, the epilogue ---- *)
Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : TfibSyms B.
Hypothesis CHK1 : CS_CHK1 B.
Hypothesis CHK2 : CS_CHK2 B.
Theorem cs_back : forall ly S (W : world tfibsegs) regs mem md x y (str : list byte) (c : byte) regs1 mem1 md1,
ecall_pre tfibsegs B ly S W regs mem md ->
ly_stk_lo ly + 2 * ESTACK <= spZ regs ->
(forall a, spZ regs - 2 * ESTACK <= a < spZ regs -> apresent (w_H W) mem a) ->
PPgWrap.awrap_str tfibsegs W mem regs x str -> PPgWrap.awrap_str tfibsegs W mem regs y [c] ->
cs_mid B ly S W regs mem md x y (Z.of_nat (PPgWrap.cspn_len [c] str)) regs1 mem1 md1 ->
SRr tfibsegs W (cfg_at tfibsegs CS1_ENTRY regs1 mem1 md1)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
AR tfibsegs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 (Z.of_nat (PPgWrap.cspn_len [c] str)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs) -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
Proof using LAWS TB CHK1 CHK2.
intros ly S W regs mem md x y str c regs1 mem1 md1 HPRE Hslo2 Hpres2 HX HY HMID.
pose proof HPRE as (HAR0 & Hra' & Hal16 & Hslo & Htop & HpresE & Hgp & Htp).
pose proof AF0x.Hwx_tfa as Hwx. unfold ESTACK in *.
pose proof (am_layout B ly S _ (proj1 HAR0)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg).
unfold kHighMemBeg, kHighMemEnd in Lbeg, Lhi.
set (sp0 := spZ regs) in *.
assert (Hsp : 0x10007fff8000 + 8192 <= sp0 <= 2 ^ 47) by lia.
set (H := w_H W) in *.
destruct HMID as (HAR1 & Hsbm1 & M2 & M8 & M9 & M19 & M10 & M21 & M23 & MK & MFR & MPR & MSV).
unfold CS_FRAME in M2. unfold CS_WIN in MFR.
destruct HX as (Hx0 & Hxnul & Hxl32 & Hxl63 & Hxarr & Hxsrc & Hxband & Hxam & Hxra & Hxhull & Hxtail).
destruct HY as (Hy0 & Hynul & Hyl32 & Hyl63 & Hyarr & Hysrc & Hyband & Hyam & Hyra & Hyhull & Hytail).
change (Z.of_nat (length [c])) with 1 in Hyl63, Hyam, Hyra, Hyhull.
set (L := Z.of_nat (length str)) in *.
pose proof (cspn_le [c] str) as HRL.
set (r := Z.of_nat (PPgWrap.cspn_len [c] str)) in *.
assert (Hr : 0 <= r <= L) by (unfold r, L; lia).
assert (Hxhi : x + (L + 1) <= kHighMemEnd) by (clear - Hxam; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia).
assert (Hyhi : y + 2 <= kHighMemEnd) by (clear - Hyam; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia).
(* the shadow band is below the stack window, so the walk's stack writes leave it as it was *)
assert (BAND1 : forall s, SHADOW_OFF - 8 <= s < kHighShadowEnd + 8 -> aview tfibsegs H mem1 s = aview tfibsegs H mem s).
{ intros s Hs. unfold SHADOW_OFF, kHighShadowEnd in Hs. apply MFR; lia. }
assert (S1 : spZ regs1 = sp0 - 2160) by (unfold spZ; rewrite M2; unfold w64; apply unsigned_lit_small; lia).
(* the range check of the set [y, y + 2) *)
eapply SRr_bind.
{ apply (CHK1 ly S W regs1 mem1 md1 y 2).
  - exact HAR1.
  - rewrite S1. replace (sp0 - 2160) with (sp0 + (-135) * 16) by lia. rewrite Z_mod_plus_full. exact Hal16.
  - rewrite S1. unfold CHK_SCR. lia.
  - rewrite S1. lia.
  - intros a Ha. rewrite S1 in Ha. unfold CHK_SCR in Ha. apply MPR. apply Hpres2. lia.
  - rewrite M10. reflexivity.
  - exact M19.
  - lia.
  - lia.
  - lia.
  - exact Hyam.
  - exact (ra_transfer _ _ y 2 2 Hy0 ltac:(lia) Hyhi BAND1 Hyra).
  - exact (hull_transfer _ _ y 2 2 Hy0 ltac:(lia) Hyhi BAND1 Hyhull). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & K2 & Hsbm2 & A2 & Hfr2 & Hpr2).
change (w_H W) with H in Hfr2, Hpr2.
rewrite S1 in Hfr2. unfold CHK_SCR in Hfr2.
assert (S2 : spZ regs2 = sp0 - 2160).
{ rewrite <- S1. unfold spZ. f_equal. exact (K2 2 (acs_of 2 eq_refl) ltac:(discriminate)). }
assert (BAND2 : forall s, SHADOW_OFF - 8 <= s < kHighShadowEnd + 8 -> aview tfibsegs H mem2 s = aview tfibsegs H mem s).
{ intros s Hs. pose proof Hs as Hs'. unfold SHADOW_OFF, kHighShadowEnd in Hs'. rewrite Hfr2 by lia. exact (BAND1 s Hs). }
(* the range check of the string [x, x + r + 1) *)
eapply SRr_bind.
{ change CS1_END with CS2_ENTRY.
  apply (CHK2 ly S W regs2 mem2 md2 x (r + 1)).
  - exact HAR2.
  - rewrite S2. replace (sp0 - 2160) with (sp0 + (-135) * 16) by lia. rewrite Z_mod_plus_full. exact Hal16.
  - rewrite S2. unfold CHK_SCR. lia.
  - rewrite S2. lia.
  - intros a Ha. rewrite S2 in Ha. unfold CHK_SCR in Ha. apply Hpr2. apply MPR. apply Hpres2. lia.
  - rewrite A2, M21. unfold w64. f_equal. lia.
  - transitivity (getr regs1 21); [exact (K2 21 (acs_of 21 eq_refl) ltac:(discriminate)) |].
    rewrite M21. unfold w64. f_equal. lia.
  - transitivity (getr regs1 9); [exact (K2 9 (acs_of 9 eq_refl) ltac:(discriminate)) | exact M9].
  - transitivity (getr regs1 23); [exact (K2 23 (acs_of 23 eq_refl) ltac:(discriminate)) | exact M23].
  - lia.
  - lia.
  - lia.
  - apply (amem_range_sub x (r + 1) (L + 1)); [lia | exact Hxam].
  - exact (ra_transfer _ _ x (r + 1) (L + 1) Hx0 ltac:(lia) Hxhi BAND2 Hxra).
  - exact (hull_transfer _ _ x (r + 1) (L + 1) Hx0 ltac:(lia) Hxhi BAND2 Hxhull). }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HAR3 & K3 & Hsbm3 & A3 & Hfr3 & Hpr3).
change (w_H W) with H in Hfr3, Hpr3.
rewrite S2 in Hfr3. unfold CHK_SCR in Hfr3.
(* the epilogue (as FMstrlen.v's): the saved words are where the prologue left them, the checks wrote below *)
set (SVL := map (fun p => getr regs (Z_to_bv 5 (fst p))) CS_SAVED).
set (E4 := Ereg regs3 SVL).
assert (R3sp : getr regs3 2 = w64 (sp0 - 2160)).
{ transitivity (getr regs1 2); [| exact M2]. transitivity (getr regs2 2).
  - exact (K3 2 (acs_of 2 eq_refl) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)).
  - exact (K2 2 (acs_of 2 eq_refl) ltac:(discriminate)). }
assert (E4_2 : bv_unsigned (ew E4 2) = sp0 - 2160).
{ subst E4. rewrite (ew_Ereg_nat regs3 _ 2 2%bv eq_refl), R3sp. unfold w64. apply unsigned_lit_small. lia. }
assert (MB3 : forall a, 0 <= a < 2 ^ 64 -> sp0 - 80 <= a < sp0 -> mbyte tfibsegs (mrestrict H mem3) a = mbyte tfibsegs (mrestrict H mem1) a).
{ intros a Hra Ha. apply mbyte_of_aview. rewrite Hfr3 by lia. apply Hfr2; lia. }
assert (VM : forall a v, val_mem tfibsegs (mrestrict H mem1) a 8 v -> sp0 - 80 <= a -> a + 8 <= sp0 -> val_mem tfibsegs (mrestrict H mem3) a 8 v).
{ intros a v Hv Hlo Hhi. apply (AF0x.val_mem_ext (mrestrict H mem1)); [|exact Hv]. intros j Hj. apply MB3; lia. }
assert (XX : forall j rz off, nth_error CS_SAVED j = Some (rz, off) -> ew E4 (32 + j) = getr regs (Z_to_bv 5 rz)).
{ intros j rz off Hj. subst E4. rewrite ew_Ereg_extra. apply nth_error_nth. subst SVL. rewrite nth_error_map, Hj. reflexivity. }
assert (CK : forall j rz off, nth_error CS_SAVED j = Some (rz, off) ->
YP09.chunk_ok tfibsegs E4 (mrestrict H mem3) (sp0 - 2160) (YP09.mkChunk (2160 + off) (CVal 8 (SOff (32 + j) 0)))).
{ intros j rz off Hj. pose proof (saved_off j rz off Hj) as Ho.
  eapply (chunk_ok_val tfibsegs E4 _ (sp0 - 2160) (2160 + off) 8 _ (bv_unsigned (getr regs (Z_to_bv 5 rz)))).
  - cbn [sv_denot]. rewrite (XX j rz off Hj), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  - pose proof (u64_range (getr regs (Z_to_bv 5 rz))). zside.
  - zside.
  - replace (sp0 - 2160 + (2160 + off)) with (sp0 + off) by lia.
    apply VM; [exact (MSV rz off (nth_error_In _ _ Hj)) | lia | lia]. }
assert (HSe : st_ok tfibsegs E4 cs_ss_epi (restrict H (mkst regs3 (w64 CS2_END) mem3 (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold cs_ss_epi. apply (entry_st_ok_full tfibsegs); change (Ereg regs3 SVL) with E4.
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil].
    unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. unfold CS_FRAME.
    replace (base_val E4 (Some 2%nat)) with (sp0 - 2160) by (symmetry; exact E4_2).
    split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
    unfold cs_epi_chunks.
    repeat apply Forall_cons; try apply Forall_nil.
    + exact (CK 0%nat 1 (-8) eq_refl).
    + exact (CK 1%nat 8 (-16) eq_refl).
    + exact (CK 2%nat 9 (-24) eq_refl).
    + exact (CK 3%nat 18 (-32) eq_refl).
    + exact (CK 4%nat 19 (-40) eq_refl).
    + exact (CK 5%nat 20 (-48) eq_refl).
    + exact (CK 6%nat 21 (-56) eq_refl).
    + exact (CK 7%nat 22 (-64) eq_refl).
    + exact (CK 8%nat 23 (-72) eq_refl).
    + exact (CK 9%nat 24 (-80) eq_refl).
  - apply pairwise_disjoint_of_extents. cbn. repeat split.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E4_2.
    change (2 ^ 4) with 16. repeat split; try lia.
    all: replace (sp0 - 2160) with (sp0 + (-135) * 16) by lia; rewrite Z_mod_plus_full; exact Hal16. }
eapply SRr_bind; [apply (cs_phase W E4 cs_ss_epi cs_epi_e _ _ _ HSe cs_r_epi)|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HF4 & HFr4). rewrite ?wvb_wvb in *.
change (st_ok tfibsegs E4 cs_epi_e (restrict H ms4)) in HS4.
eapply (SRr_ret_at tfibsegs tbl_cs tbl_cs_ok Hwx W E4); [exact HS4 | reflexivity | vm_compute; reflexivity |].
intros mat'. cbv beta. rewrite wvb_wvb.
assert (MEQ4 : forall z, ms_mem ms4 z = mem3 z) by (intros z; apply HF4; intros Hin; destruct (in_wrange_windows E4 _ _ Hin) as (b & lo & hi & Ht & Hw); cbn in Ht; destruct Ht as [Hq|[]]; injection Hq as <- <- <-; cbn [base_val] in Hw; lia).
rreg HS4 (1%bv : bv 5) Q1. rreg HS4 (2%bv : bv 5) Q2. rreg HS4 (10%bv : bv 5) Q10.
rreg HS4 (Z_to_bv 5 3) Q3. rreg HS4 (Z_to_bv 5 4) Q4. rreg HS4 (Z_to_bv 5 8) Q8. rreg HS4 (Z_to_bv 5 9) Q9.
rreg HS4 (Z_to_bv 5 18) Q18. rreg HS4 (Z_to_bv 5 19) Q19. rreg HS4 (Z_to_bv 5 20) Q20. rreg HS4 (Z_to_bv 5 21) Q21.
rreg HS4 (Z_to_bv 5 22) Q22. rreg HS4 (Z_to_bv 5 23) Q23. rreg HS4 (Z_to_bv 5 24) Q24.
rreg HS4 (Z_to_bv 5 25) Q25. rreg HS4 (Z_to_bv 5 26) Q26. rreg HS4 (Z_to_bv 5 27) Q27.
assert (X32 : ew E4 32 = getr regs 1) by exact (XX 0%nat 1 (-8) eq_refl).
rewrite X32 in Q1.
assert (Y : forall i (rr : bv 5), Z.of_nat i = bv_unsigned rr -> ew E4 i = getr regs3 rr) by (intros ii rr Hn; subst E4; exact (ew_Ereg_nat regs3 _ ii rr Hn)).
replace (v_jalr (getr (ms_regs ms4) 1) 0) with (w64 (raZ regs)) by (rewrite Q1; unfold raZ, w64; rewrite Z_to_bv_bv_unsigned; symmetry; exact Hra').
split; [reflexivity|]. exists (ms_regs ms4), (ms_mem ms4), (with_vm_backing (m_vm_lazy md3) mat' md3).
pose proof (same_but_materialized_frame md3 _ (with_vm_backing_same md3 mat')) as MF.
assert (AV4 : forall a, aview tfibsegs H (ms_mem ms4) a = aview tfibsegs H mem3 a) by (intros a; apply aview_same; apply MEQ4).
split; [reflexivity|].
split; [|split; [|split; [|split; [|split]]]].
- apply (al_frame _ _ LAWS ly S W mem3 md3 (ms_mem ms4) _ HAR3).
  + intros a Hr' Hown. apply AV4.
  + intros a Hv. rewrite AV4. exact Hv.
  + apply MF.
  + apply MF.
  + apply MF.
  + exact (AE2y.hs_kept_eq _ _ _ MEQ4).
- intros rz Hrz. unfold acallee_saved in Hrz.
  destruct Hrz as [-> | [-> | [-> | [-> | [-> | Hrz]]]]].
  + replace (Z_to_bv 5 2) with (2%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q2. apply bv_eq.
    rewrite Z_to_bv_unsigned, E4_2. unfold sp0, spZ, bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    pose proof (u64_range (getr regs 2)). rewrite Z.mod_small by lia. lia.
  + rewrite Q3, (Y 3%nat (Z_to_bv 5 3) eq_refl). exact (chain_kept regs regs1 regs2 regs3 3 MK K2 K3 eq_refl).
  + rewrite Q4, (Y 4%nat (Z_to_bv 5 4) eq_refl). exact (chain_kept regs regs1 regs2 regs3 4 MK K2 K3 eq_refl).
  + rewrite Q8. exact (XX 1%nat 8 (-16) eq_refl).
  + rewrite Q9. exact (XX 2%nat 9 (-24) eq_refl).
  + assert (Hc : rz = 18 \/ rz = 19 \/ rz = 20 \/ rz = 21 \/ rz = 22 \/ rz = 23 \/ rz = 24 \/ rz = 25 \/ rz = 26 \/ rz = 27)
      by (clear - Hrz; lia).
    destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]].
    * rewrite Q18. exact (XX 3%nat 18 (-32) eq_refl).
    * rewrite Q19. exact (XX 4%nat 19 (-40) eq_refl).
    * rewrite Q20. exact (XX 5%nat 20 (-48) eq_refl).
    * rewrite Q21. exact (XX 6%nat 21 (-56) eq_refl).
    * rewrite Q22. exact (XX 7%nat 22 (-64) eq_refl).
    * rewrite Q23. exact (XX 8%nat 23 (-72) eq_refl).
    * rewrite Q24. exact (XX 9%nat 24 (-80) eq_refl).
    * rewrite Q25, (Y 25%nat (Z_to_bv 5 25) eq_refl). exact (chain_kept regs regs1 regs2 regs3 25 MK K2 K3 eq_refl).
    * rewrite Q26, (Y 26%nat (Z_to_bv 5 26) eq_refl). exact (chain_kept regs regs1 regs2 regs3 26 MK K2 K3 eq_refl).
    * rewrite Q27, (Y 27%nat (Z_to_bv 5 27) eq_refl). exact (chain_kept regs regs1 regs2 regs3 27 MK K2 K3 eq_refl).
- eapply same_but_materialized_trans; [exact Hsbm1 |].
  eapply same_but_materialized_trans; [exact Hsbm2 |].
  eapply same_but_materialized_trans; [exact Hsbm3 | apply with_vm_backing_same].
- rewrite Q10, (Y 10%nat 10%bv eq_refl), A3. unfold w64. f_equal. lia.
- intros a Ha Hs. rewrite AV4. rewrite Hfr3 by lia. rewrite Hfr2 by lia. apply MFR; lia.
- intros a Hp. apply (apresent_same H mem3 (ms_mem ms4) a (MEQ4 _)). apply Hpr3. apply Hpr2. apply MPR. exact Hp.
Qed.
End g.
