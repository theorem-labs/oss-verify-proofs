(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s YP0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YQ0g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YA0n YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG07.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF8t.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0a YG01 YG04 YG03 YG0h YG10 YG0u YG0d YG0y YG0w.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF8r YF8s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP09.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF64 YF3v.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF4q YF40 YF4w YF4y YF4v YF50.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac img_facts ::= lazymatch goal with k : img |- _ => let F := fresh "IMGF" in pose proof (P_facts k) as F end.
Ltac img_lia ::=
first [ (img_goal_has_k; img_facts; lia)
| lia
| (img_inst; lia)
| (try img_inst;
first [ (img_local; img_local_unfold; img_unfold_all; lia)
| (img_arith_rel; first [ (img_facts; lia)
| (img_has_moddiv; img_case; img_unfold_all; lia)
| (first [ img_has_moddiv | img_has_match ]; img_concrete; img_unfold_all; lia) ]) ]) ].
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Set Printing Depth 50. Set Printing Width 180.
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section b. Context {imgk : img}.
Variable B : asyms.
Hypothesis TS : TfxSyms B.
Hypothesis U1 : tfx_unwind_spec.
Hypothesis D1 : tfx_depot_spec B.
Variables (ly : alayout) (S : astate) (W : world tfxsegs) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (n : Z) (ch : list (Z * Z * Z)).
Let tr : list Z := call_trace ly (0x533a4 + D_2c4) regs0 ch.
Hypothesis PRE : acall_pre tfxsegs B ly S W regs0 mem0 md0 ch.
Hypothesis Hn : getr regs0 10 = w64 n.
Hypothesis Nrange0 : 49 <= n <= 64512.
Hypothesis Htr : In tr (as_universe B).
Hypothesis Hlive : blocks_bytes S + n <= LIVE_MAX.
Variables (l : list Z) (off : Z).
Hypothesis Hinited : st_cache_inited S = true.
Hypothesis Hcache : pc_chunks (cache S (chunk_class n)) = l ++ [off].
Theorem malloc_hitg :
amreal tfxsegs (malloc n tr S) W (cfg_at tfxsegs (0x53104 + D_2c4) regs0 mem0 md0) (malloc_leaf tfxsegs B ly S W regs0 mem0 md0 n).
Proof.
destruct PRE as (HAR & Hev & Hra & Hal & Hlo & Hbot & Hhi & Hpres0 & Hgp & Htp & CH & HQT).
pose proof (proj1 HAR) as HARm0. unfold spZ in *.
set (S1 := set_nev (st_nev S + 1) S).
pose proof (ARm_tick B ly S _ HARm0 Hev) as HARm. fold S1 in HARm.
pose proof (AR_tick B ly S W mem0 md0 HAR Hev) as HAR1. fold S1 in HAR1.
assert (Hinited1 : st_cache_inited S1 = true) by img_exact Hinited.
assert (Hcache1 : pc_chunks (cache S1 (chunk_class n)) = l ++ [off]) by img_exact Hcache.
assert (HQT1 : qtight S1) by img_exact HQT.
assert (LY : layout_ok ly) by img_exact (am_layout _ _ _ _ HARm).
assert (IMG : img_cover ly) by img_exact (img_cover_of_ledger ly S1 md0 (proj1 (proj2 HAR1))).
assert (HTSD : ly_tsd ly = TFX_TSD) by (img_try (rewrite (am_tsd _ _ _ _ HARm); img_exact (ts_tsd B TS))).
rewrite (ts_tp B TS) in Htp.
destruct CH as [Hra4096 Hch]. unfold raZ in Hra4096. unfold frame0_ok, spZ, s0Z in Hch.
set (sp0 := bv_unsigned (getr regs0 2)) in *.
assert (Hsp : ly_stk_lo ly + ASTACK <= sp0 /\ ly_bot ly < sp0 /\ sp0 <= ly_stk_hi ly /\ sp0 mod 16 = 0) by (img_try (repeat split; assumption)).
set (kz := rz_log n).
assert (Hkz : 1 <= kz <= 6 /\ rz_lo kz <= n <= rz_hi kz).
{ (subst kz; cbv beta). unfold rz_log. clear - Nrange0.
destruct (Z.leb_spec n 48); [img_lia|]. destruct (Z.leb_spec n 96); [img_try (cbn; img_lia)|]. destruct (Z.leb_spec n 448); [img_try (cbn; img_lia)|].
destruct (Z.leb_spec n 3968); [img_try (cbn; img_lia)|]. destruct (Z.leb_spec n 16128); [img_try (cbn; img_lia)|]. destruct (Z.leb_spec n 32256); [img_try (cbn; img_lia)|].
destruct (Z.leb_spec n 64512); [img_try (cbn; img_lia)|]. img_lia. }
destruct Hkz as [Hkz Nrange]. clearbody kz.
set (cl := chunk_class n) in *. set (cnt := Z.of_nat (length (l ++ [off]))). set (v := off / 16). set (csz := class_size cl).
set (DPOST := fun z m => YF4v.DPOST3 W ly regs0 ch B S1 z m). set (mat0 := m_vm_materialized md0).
assert (Hcl_class : cl = chunk_class n) by img_refl.
assert (Hcnt_def : cnt = Z.of_nat (length (l ++ [off]))) by img_refl.
assert (Hcsz_def : csz = class_size cl) by img_refl.
assert (Hcl : 1 <= cl <= 31) by img_exact (@YF4w.Hcl' ly regs0 mem0 n cl v kz DPOST Hkz Nrange l off Hcl_class).
assert (Hoffv : off = 16 * v /\ v mod 2 = 0).
{ pose proof (wf_classes _ _ _ _ _ (am_wf _ _ _ _ HARm) cl Hcl) as CL. pose proof (wr_elems _ _ _ _ _ _ CL) as EL. rewrite Hcache1 in EL.
pose proof (proj1 (Forall_forall _ _) EL off ltac:(img_try (rewrite !in_app_iff; cbn; tauto))) as [_ O2].
pose proof (class_ok cl Hcl) as (K1 & K2 & _). apply Z.mod_divide in O2 as [q Hq]; [|img_lia]. apply Z.mod_divide in K2 as [r Hr]; [|img_lia].
(subst v; cbv beta). rewrite Hq, Hr. replace (q * (r * 32)) with ((2 * q * r) * 16) by img_lia. rewrite Z.div_mul by img_lia. split; [img_lia|].
rewrite <- Z.mul_assoc, Z.mul_comm. img_apply Z_mod_mult. }
destruct Hoffv as [Hoff_def Hv2].
assert (Hv : 0 <= v /\ 16 * v + 2 ^ 16 <= 2 ^ 32)
by img_exact (@YF4w.Hv' _ imgk W ly regs0 mem0 n cl cnt v kz Hv2 DPOST Hkz Nrange B S1 l off HARm Hinited1 Hcache1 Hcl_class Hcnt_def Hoff_def).
assert (Hcnt : 1 <= cnt <= 16)
by img_exact (@YF4w.Hcnt' _ imgk W ly regs0 mem0 n cl cnt v kz Hv2 Hsp DPOST Hkz Nrange B S1 l off HARm Hinited1 Hcache1 Hcl_class Hcnt_def Hoff_def).
destruct (@YF4w.junk_values _ imgk W ly regs0 mem0 n cl cnt v csz kz Hv2 LY IMG Hsp DPOST Hkz Nrange B S1 l off HARm Hinited1 Hcache1 Hcl_class Hcnt_def Hoff_def Hcsz_def)
as (j0 & j1 & j2 & j3 & j4 & jb & Hj0 & Hj1 & Hj2 & Hj3 & Hj4 & Hjb & Hjb_def).
pose proof (@YF4w.KPRES _ imgk W ly regs0 mem0 n cl cnt v csz kz Hv2 LY Hsp DPOST Hkz Nrange B S1 l off HARm Hinited1 Hcache1 Hcl_class Hcnt_def Hoff_def Hcsz_def) as HKpres.
pose proof (@YF4w.SKPRES _ imgk W ly regs0 mem0 n cl cnt v csz kz Hv2 LY IMG Hsp DPOST Hkz Nrange B S1 l off HARm Hinited1 Hcache1 Hcl_class Hcnt_def Hoff_def Hcsz_def) as HSKpres.
pose proof (@YF4w.PB250 _ imgk W ly regs0 mem0 n cl cnt v csz kz Hv2 LY IMG Hsp DPOST Hkz Nrange B S1 l off HARm Hinited1 Hcache1 Hcl_class Hcnt_def Hoff_def Hcsz_def) as HPB250.
pose proof (@YF4q.casek_sizes n kz Hkz Nrange) as (L & RS & R8 & NP & FP & NS & RQ).
assert (Hcl_def : cl = class_id (R8v n + YF4q.RZ kz)) by (img_try ((subst cl; cbv beta); unfold chunk_class; rewrite NS, <- RS; img_refl)).
pose proof (@YF4y.SEED_ok _ _ imgk W ly regs0 mem0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz Hcl Hv Hcnt Hjb Hv2 LY IMG Hn Htp Hsp DPOST Hkz Nrange B S1 l off TS HTSD HARm Hpres0 Hinited1 Hcache1 Hcl_class Hcnt_def Hoff_def Hcsz_def Hj0 Hj1 Hj2 Hj3 Hj4 Hjb_def) as SEED.
eapply (amreal_atok _ true (malloc_post (as_universe B) S n)).
{ img_apply (malloc_ok (as_universe B) S n tr (ts_universe B TS) (am_wf _ _ _ _ HARm0) Hev); [img_try (unfold MALLOC_MAX; img_lia) | img_try (img_exact Hlive) | img_try (img_exact Htr)]. }
rewrite (malloc_primary_eq n tr S FP). eapply amreal_pure; [img_refl|].
eapply amreal_pure; [img_try (unfold mcheck; replace (n <? kMaxAllowedMalloc - kPage) with true by (symmetry; img_apply Z.ltb_lt; unfold kMaxAllowedMalloc, kPage; img_lia); img_refl)|].
fold S1. rewrite <- Hcl_class.
eapply amreal_pure; [img_try (img_apply refill_tree_ready; [img_exact Hinited1 | rewrite Hcache1; destruct l; discriminate])|].
eapply amreal_mono; [| img_try (img_exact (@YF50.hitg_inner _ _ imgk W ly regs0 mem0 md0 n ch cl cnt v csz j0 jb j1 j2 j3 j4 kz Hcl Hv Hcnt Hjb Hv2 LY IMG Hn Htp Hra Hra4096 Hsp Hch DPOST HKpres HSKpres HPB250 Hkz Nrange Hcl_def mat0 U1 SEED B S1 l off TS HTSD HARm Hgp Hinited1 Hcache1 Hcl_class Hcnt_def Hoff_def Hcsz_def Hj4 Hjb_def Htr HAR1 D1 (fun z m H => H) (fun z m H => H) eq_refl))].
intros [p s'] W' c' H [ns MP]. cbn [fst snd] in H, MP. destruct MP as (WF' & _ & _ & _ & _ & QT). img_exact (H (conj WF' (QT HQT))).
Qed.
End b.
End a.
