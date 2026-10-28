(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec ImageA RzCPS.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import R_unwind_chain RT_iface D_defs. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import SegRw.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Common Require Import FastWord FastWordSem.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Common.Ax Require Import ExTrie.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.HX Require Import HxRegs HxVal HxBytes HxMem HxMemSound HxStep HxStepSound HxRunSound HxHook HxHookSound HxToolkit HxGlue HxImg HxQuery HxLearn.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.HXS Require Import HxsStep HxsStepSound HxsHook HxsHookSound HxsKit.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.HXB Require Import HxaInit HxaEceInit HxaImage HxaInv HxaHooks HxaIface HxaHandoffImg HxaHandoff.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

Local Ltac closed_side := first [ vm_compute; reflexivity | apply Z.leb_le; vm_compute; reflexivity | vm_compute; discriminate ].

Lemma seg_rw_libdata : seg_rw_ok bsegs 6186592 2784 = true. Proof. vm_compute. reflexivity. Qed.
Lemma seg_rw_libbss : seg_rw_ok bsegs 12411008 2528 = true. Proof. vm_compute. reflexivity. Qed.
Lemma seg_rw_tsdmain : seg_rw_ok bsegs 12567040 64 = true. Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma fact_lit (rho : valuation) (m : word -> option byte) (B off : Z) (n : nat) (v : Z) :
  0 <= v -> bytes_at bsegs m (B + off) (Z_to_le_bytes n v) -> fact_holds bsegs rho m B (off, kbs_Z n v).
Proof. intros Hv Hb. exists (Z_to_le_bytes n v). split; [apply kbs_Z_intro; exact Hv | exact Hb]. Qed.

Lemma fact_ptr (rho : valuation) (m : word -> option byte) (B off : Z) (tag : int) (A : Z) :
  rho tag = A -> 0 <= A < 2 ^ 64 -> bytes_at bsegs m (B + off) (le8 (Z_to_bv 64 A)) -> fact_holds bsegs rho m B (off, kbs_ptr tag).
Proof. intros Er HA Hb. exists (le8 (Z_to_bv 64 A)). split; [exact (kbs_ptr_intro rho tag A Er HA) | exact Hb]. Qed.

(* [comment removed for export] *)
Lemma c8_bytes (m : word -> option byte) (a : Z) (w : word) : ro_cells bsegs m a [C8 w] -> bytes_at bsegs m a (le8 w).
Proof. intros [_ B1]. cbn [cells_bytes cbytes] in B1. rewrite app_nil_r in B1. exact B1. Qed.
Lemma c4_bytes (m : word -> option byte) (a : Z) (w : word) : ro_cells bsegs m a [C4 w] -> bytes_at bsegs m a (le4 w).
Proof. intros [_ B1]. cbn [cells_bytes cbytes] in B1. rewrite app_nil_r in B1. exact B1. Qed.
Lemma c1_bytes (m : word -> option byte) (a : Z) (b : byte) : ro_cells bsegs m a [C1 b] -> bytes_at bsegs m a [b].
Proof. intros [_ B1]. cbn [cells_bytes cbytes] in B1. exact B1. Qed.

(* [comment removed for export] *)
Lemma seg_rw_mapped (m : word -> option byte) (a n : Z) : seg_rw_ok bsegs a n = true ->
  forall i, 0 <= i < n -> (exists b, mrd bsegs m (wa (a + i)) = Some b) /\ wview bsegs m (wa (a + i)) <> None.
Proof. intros H i Hi. destruct (proj2 (seg_rw_ok_sound bsegs a n H m)) as (_ & _ & Hs). destruct (Hs (a + i) ltac:(lia)) as [Hw Hb]. split; assumption. Qed.

(* [comment removed for export] *)
Definition chunk_rng (lo A n : Z) : Prop :=
  0 < A /\ A mod 16 = 0 /\ A + n <= lo /\ (A + n <= 65536 \/ 12570624 <= A) /\ (A + n <= 0x7fff7000 \/ 0x10007fff8000 <= A).
Definition apart (a n b k : Z) : Prop := a + n <= b \/ b + k <= a.

Lemma shad_chunk (A n : Z) : 0 < A -> 0 <= n -> A + 8 * n < 2 ^ 47 -> 0x7fff8000 <= shad A /\ shad A + n < 0x10007fff8000.
Proof.
  intros H0 Hn H1. pose proof (shad_range A ltac:(lia)) as X1. pose proof (shad_range (A + 8 * n) ltac:(lia)) as X2.
  rewrite shad_add8 in X2. unfold SH_LO, SH_HI in *. split; [|lia]. unfold shad, SHB. pose proof (Z.div_pos A 8 ltac:(lia) ltac:(lia)). lia.
Qed.

Section Handoff.
Variables (rho : valuation) (m : word -> option byte) (ri : int).
Hypothesis H_ri : ri = 0%uint63 \/ ri = 16%uint63.
Hypothesis MI : mem_inv bsegs m.
Hypothesis V_relro : forall a, 5681152 <= a < 6172672 -> mrd bsegs m (wa a) = seg_rom bsegs (wa a).
Hypothesis C_shb : ro_cells bsegs m 6961656 [C8 (Z_to_bv 64 SHB)].
Hypothesis C_uar : ro_cells bsegs m 6961664 [C4 (Z_to_bv 64 1)].
Hypothesis C_tsd : rw_cells bsegs m 12430840 [C8 (Z_to_bv 64 0xbfc1f8)].
(* [comment removed for export] *)
Hypothesis C_memset : ro_cells bsegs m 0x5e6660 [C8 (Z_to_bv 64 0x1bcc34)].
Hypothesis C_malloc : ro_cells bsegs m 0x5e6680 [C8 (Z_to_bv 64 0x1f261c)].
Hypothesis C_free : ro_cells bsegs m 0x5e66c0 [C8 (Z_to_bv 64 0x1f2b40)].
(* [comment removed for export] *)
Hypothesis C_stopped : ro_cells bsegs m 0xbd6620 [C1 (Z_to_bv 8 0)].
Hypothesis C_optsdone : ro_cells bsegs m 0xbd66c0 [C8 (Z_to_bv 64 2)].
Hypothesis C_base_once : ro_cells bsegs m 0xbd66e0 [C4 (Z_to_bv 64 2)].
Hypothesis C_base_ret : ro_cells bsegs m 0xbd6700 [C4 (Z_to_bv 64 1)].
Hypothesis C_master_once : ro_cells bsegs m 0xbd61e0 [C4 (Z_to_bv 64 2)].
Hypothesis C_master_key : ro_cells bsegs m 0xbd6200 [C4 (Z_to_bv 64 3)].
Hypothesis H_imgsh : region_ok bsegs rho TE_IMGSH RG_IMGSH_E m.

Lemma eg4_ok : region_ok bsegs rho 4%uint63 eg_4 m.
Proof. exact (HxaHandoffImg.rg4_ok rho m MI). Qed.
Lemma eg5_ok : region_ok bsegs rho 5%uint63 eg_5 m.
Proof. exact (HxaHandoffImg.rg5_ok rho m V_relro). Qed.

Lemma Hri01 : to_Z ri = 0 \/ to_Z ri = 16.
Proof. destruct H_ri as [-> | ->]; [left | right]; reflexivity. Qed.
Lemma sz2 : to_Z (ESTK + ri)%uint63 = 81920 + to_Z ri.
Proof. destruct H_ri as [-> | ->]; reflexivity. Qed.
Lemma sz3 : to_Z ((ESTK + ri) >> 3)%uint63 = (81920 + to_Z ri) / 8.
Proof. destruct H_ri as [-> | ->]; reflexivity. Qed.

(* [comment removed for export] *)
Local Ltac lit_learn a n Hseg fs :=
  apply (region_ok_learn bsegs rho _ _ m fs);
  [ closed_side | closed_side | closed_side | closed_side | closed_side | closed_side | closed_side
  | intros i Hi; exact (proj1 (seg_rw_mapped m a n Hseg i Hi)) | discriminate | | closed_side ].

Lemma eg6_ok : region_ok bsegs rho 6%uint63 eg_6 m.
Proof.
  lit_learn 6186592 2784 seg_rw_libdata [(0, kbs_Z 8 0x1bcc34); (32, kbs_Z 8 0x1f261c); (96, kbs_Z 8 0x1f2b40)].
  repeat (constructor; [|]); [ | | | ].
  - exact (fact_lit rho m 6186592 0 8 0x1bcc34 ltac:(lia) (c8_bytes m _ _ C_memset)).
  - exact (fact_lit rho m 6186592 32 8 0x1f261c ltac:(lia) (c8_bytes m _ _ C_malloc)).
  - exact (fact_lit rho m 6186592 96 8 0x1f2b40 ltac:(lia) (c8_bytes m _ _ C_free)).
  - constructor.
Qed.

Lemma eg7_ok : region_ok bsegs rho 7%uint63 eg_7 m.
Proof. exact (HxaHandoff.rg7_ok rho m C_shb C_uar 0). Qed.

Lemma eg8_ok : region_ok bsegs rho 8%uint63 eg_8 m.
Proof.
  lit_learn 12411008 2528 seg_rw_libbss [(352, kbs_Z 4 2); (384, kbs_Z 4 3); (1440, kbs_Z 1 0); (1600, kbs_Z 8 2); (1632, kbs_Z 4 2); (1664, kbs_Z 4 1)].
  repeat (constructor; [|]); [ | | | | | | ].
  - exact (fact_lit rho m 12411008 352 4 2 ltac:(lia) (c4_bytes m _ _ C_master_once)).
  - exact (fact_lit rho m 12411008 384 4 3 ltac:(lia) (c4_bytes m _ _ C_master_key)).
  - exact (fact_lit rho m 12411008 1440 1 0 ltac:(lia) (c1_bytes m _ _ C_stopped)).
  - exact (fact_lit rho m 12411008 1600 8 2 ltac:(lia) (c8_bytes m _ _ C_optsdone)).
  - exact (fact_lit rho m 12411008 1632 4 2 ltac:(lia) (c4_bytes m _ _ C_base_once)).
  - exact (fact_lit rho m 12411008 1664 4 1 ltac:(lia) (c4_bytes m _ _ C_base_ret)).
  - constructor.
Qed.

Lemma eg9_ok : region_ok bsegs rho 9%uint63 eg_9 m.
Proof. exact (HxaHandoff.rg12_ok rho m C_tsd 0). Qed.

Lemma eg11_ok : region_ok bsegs rho 11%uint63 eg_11 m.
Proof. exact H_imgsh. Qed.

(* [comment removed for export] *)
Variables (lo sp0 : Z).
Hypothesis STKH : stk bsegs m lo sp0.
Hypothesis Hrho2 : rho 2%uint63 = sp0 - to_Z ri - 81920.
Hypothesis Hrho3 : rho 3%uint63 = shad (sp0 - to_Z ri - 81920).
Hypothesis Hlo : lo <= sp0 - to_Z ri - 81920.
Hypothesis Hlo0 : 0x7fff00000000 <= lo.
Hypothesis Hsp47 : sp0 + 16 <= USTACK_TOP.
Hypothesis Hsp32 : sp0 mod 32 = to_Z ri.
Hypothesis Z_stk : forall i, 0 <= i < (81920 + to_Z ri) / 8 -> mrd bsegs m (wa (shad (sp0 - to_Z ri - 81920) + i)) = Some z8.

Lemma lo_hi : lo < 2 ^ 47.
Proof. pose proof Hri01. unfold USTACK_TOP in Hsp47. lia. Qed.

Lemma B0_facts : 0x7fff00000000 <= sp0 - to_Z ri - 81920 /\ (sp0 - to_Z ri - 81920) mod 32 = 0
  /\ 0x80177a00 <= shad (sp0 - to_Z ri - 81920) /\ shad (sp0 - to_Z ri - 81920) + (81920 + to_Z ri) / 8 <= 0x7fff00000000.
Proof.
  pose proof Hri01 as Hr. unfold USTACK_TOP in Hsp47.
  split; [lia|]. split.
  { pose proof (Z.div_mod sp0 32 ltac:(lia)) as D. rewrite Hsp32 in D.
    replace (sp0 - to_Z ri - 81920) with (0 + (sp0 / 32 - 2560) * 32) by lia. rewrite Z.mod_add by lia. reflexivity. }
  unfold shad, SHB. split; Z.div_mod_to_equations; lia.
Qed.

Lemma eg3_ok : region_ok bsegs rho 3%uint63 (eg_3 ri) m.
Proof.
  destruct B0_facts as (F1 & F2 & F3 & F4). pose proof Hri01 as Hr. unfold eg_3.
  apply (zero_region_ok_d rho 3%uint63 _ 11 m (shad (sp0 - to_Z ri - 81920)) Hrho3); rewrite ?sz3.
  - lia.
  - unfold two63. lia.
  - Z.div_mod_to_equations; lia.
  - change (8 * 2 ^ Z.of_nat 11) with 16384. Z.div_mod_to_equations; lia.
  - cbn; lia.
  - exact Z_stk.
Qed.

Lemma eg2_ok : region_ok bsegs rho 2%uint63 (eg_2 ri) m.
Proof.
  destruct B0_facts as (F1 & F2 & F3 & F4). pose proof Hri01 as Hr. unfold eg_2, USTACK_TOP in *.
  apply region_ok_fresh; unfold rbase; cbn [rg_abs]; rewrite ?Hrho2, ?sz2.
  - lia.
  - unfold two63. lia.
  - lia.
  - change (8 * 2 ^ Z.of_nat 14) with 131072. lia.
  - cbn; lia.
  - closed_side.
  - change (to_Z 5%uint63) with 5. change (2 ^ 5) with 32. exact F2.
  - intros i Hi. destruct STKH as (_ & _ & Hs). destruct (Hs (sp0 - to_Z ri - 81920 + i) ltac:(lia)) as [Hw Hb]. split; [exact Hb | intros _; exact Hw].
Qed.

(* [comment removed for export] *)
Lemma chunk_learn (t : int) (rg : region) (A n : Z) (fs : list fact) :
  rg_abs rg = None -> rho t = A -> to_Z (rg_size rg) = n -> to_Z (rg_al rg) = 4 -> chunk_rng lo A n -> 0 < n < 2 ^ 20 ->
  n <= 8 * 2 ^ Z.of_nat (rg_d rg) -> Z.of_nat (rg_d rg) <= 59 ->
  wr_at bsegs m A n -> Forall (fact_holds bsegs rho m A) fs -> learn_check bsegs rg fs 0 (Z.to_nat n) = true ->
  region_ok bsegs rho t rg m.
Proof.
  intros Ea Er Es Eal (H0 & H16 & Hlo' & _) Hn Hd1 Hd2 (_ & _ & Hw) Hfs Hck. pose proof lo_hi as Hlh.
  assert (Eb : rbase rho t rg = A) by (unfold rbase; rewrite Ea; exact Er).
  apply (region_ok_learn bsegs rho t rg m fs); rewrite ?Eb, ?Es, ?Eal; try assumption; try lia.
  - unfold two63. lia.
  - intros i Hi. exact (wview_mrd bsegs m _ asegs_wr_rd (Hw i Hi)).
  - intros _ i Hi. exact (Hw i Hi).
Qed.

(* [comment removed for export] *)
Lemma chunk_shadow (t n : int) (d : nat) (A : Z) :
  rho t = shad A -> 0 < A -> A + 8 * to_Z n <= lo -> to_Z n <= 8 * 2 ^ Z.of_nat d -> Z.of_nat d <= 59 ->
  (forall i, 0 <= i < to_Z n -> mrd bsegs m (wa (shad A + i)) = Some z8) ->
  region_ok bsegs rho t (RG None n 0 false DZero d IEmpty) m.
Proof.
  intros Er H0 Hlo' Hd1 Hd2 HZ. pose proof lo_hi as Hlh. pose proof (to_Z_bounded n) as Bn.
  destruct (shad_chunk A (to_Z n) H0 ltac:(lia) ltac:(lia)) as [S1 S2].
  apply (zero_region_ok_d rho t n d m (shad A) Er); try assumption; try lia. unfold two63. lia.
Qed.

(* [comment removed for export] *)
Variables (MK SA ND ES : Z) (pad : list byte).
Hypothesis C_slot : ro_cells bsegs m 0xbfc210 [C8 (Z_to_bv 64 MK)].
Hypothesis C_mk : ro_cells bsegs m (MK + 24) [C8 (Z_to_bv 64 SA)].
Hypothesis C_sa : ro_cells bsegs m SA [C4 (Z_to_bv 64 1); CB 4 pad; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 ND)].
Hypothesis C_nd : ro_cells bsegs m ND [C8 (Z_to_bv 64 ES)].
Hypothesis C_es : rw_cells bsegs m ES [CB 904 (repeat (Z_to_bv 8 0) 704 ++ repeat (Z_to_bv 8 255) 64 ++ repeat (Z_to_bv 8 0) 136)].
Hypothesis W_mk : wr_at bsegs m MK 72.
Hypothesis W_sa : wr_at bsegs m SA 32.
Hypothesis W_nd : wr_at bsegs m ND 128.
Hypothesis Z_mk : forall i, 0 <= i < 9 -> mrd bsegs m (wa (shad MK + i)) = Some z8.
Hypothesis Z_sa : forall i, 0 <= i < 4 -> mrd bsegs m (wa (shad SA + i)) = Some z8.
Hypothesis Z_nd : forall i, 0 <= i < 16 -> mrd bsegs m (wa (shad ND + i)) = Some z8.
Hypothesis Z_es : forall i, 0 <= i < 113 -> mrd bsegs m (wa (shad ES + i)) = Some z8.
Hypothesis Hrho32 : rho 32%uint63 = MK.  Hypothesis Hrho33 : rho 33%uint63 = shad MK.
Hypothesis Hrho34 : rho 34%uint63 = SA.  Hypothesis Hrho35 : rho 35%uint63 = shad SA.
Hypothesis Hrho36 : rho 36%uint63 = ND.  Hypothesis Hrho37 : rho 37%uint63 = shad ND.
Hypothesis Hrho38 : rho 38%uint63 = ES.  Hypothesis Hrho39 : rho 39%uint63 = shad ES.
Hypothesis R_mk : chunk_rng lo MK 72.
Hypothesis R_sa : chunk_rng lo SA 32.
Hypothesis R_nd : chunk_rng lo ND 128.
Hypothesis R_es : chunk_rng lo ES 904.
Hypothesis D_mk : apart ES 904 MK 72.
Hypothesis D_sa : apart ES 904 SA 32.
Hypothesis D_nd : apart ES 904 ND 128.

Lemma chunk_word (A n : Z) : chunk_rng lo A n -> 0 <= n -> 0 <= A < 2 ^ 64.
Proof. intros (H0 & _ & H1 & _) Hn. pose proof lo_hi. lia. Qed.

Lemma eg10_ok : region_ok bsegs rho 10%uint63 eg_10 m.
Proof.
  lit_learn 12567040 64 seg_rw_tsdmain [(16, kbs_ptr 32)].
  constructor; [|constructor].
  exact (fact_ptr rho m 12567040 16 32%uint63 MK Hrho32 (chunk_word MK 72 R_mk ltac:(lia)) (c8_bytes m _ _ C_slot)).
Qed.

Lemma eg32_ok : region_ok bsegs rho 32%uint63 eg_32 m.
Proof.
  apply (chunk_learn 32%uint63 eg_32 MK 72 [(24, kbs_ptr 34)]);
    [reflexivity | exact Hrho32 | reflexivity | reflexivity | exact R_mk | lia | closed_side | closed_side | exact W_mk | | closed_side].
  constructor; [|constructor]. exact (fact_ptr rho m MK 24 34%uint63 SA Hrho34 (chunk_word SA 32 R_sa ltac:(lia)) (c8_bytes m _ _ C_mk)).
Qed.

Lemma eg34_ok : region_ok bsegs rho 34%uint63 eg_34 m.
Proof.
  apply (chunk_learn 34%uint63 eg_34 SA 32 [(0, kbs_Z 4 1 ++ kbs_any 4 ++ kbs_Z 8 0 ++ kbs_Z 8 1 ++ kbs_ptr 36)]);
    [reflexivity | exact Hrho34 | reflexivity | reflexivity | exact R_sa | lia | closed_side | closed_side | exact W_sa | | closed_side].
  constructor; [|constructor].
  destruct C_sa as [Hwf Hb]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb.
  assert (Hpad : length pad = 4%nat) by (cbn [cells_wf cell_wf] in Hwf; tauto).
  exists (le4 (Z_to_bv 64 1) ++ pad ++ le8 (Z_to_bv 64 0) ++ le8 (Z_to_bv 64 1) ++ le8 (Z_to_bv 64 ND)). split; [|cbn [fst]; rewrite Z.add_0_r; exact Hb].
  cbn [snd]. apply Forall2_app; [apply (kbs_Z_intro rho 4 1); lia|]. apply Forall2_app; [rewrite <- Hpad; apply kbs_any_intro|].
  apply Forall2_app; [apply (kbs_Z_intro rho 8 0); lia|]. apply Forall2_app; [apply (kbs_Z_intro rho 8 1); lia|].
  exact (kbs_ptr_intro rho 36%uint63 ND Hrho36 (chunk_word ND 128 R_nd ltac:(lia))).
Qed.

Lemma eg36_ok : region_ok bsegs rho 36%uint63 eg_36 m.
Proof.
  apply (chunk_learn 36%uint63 eg_36 ND 128 [(0, kbs_ptr 38)]);
    [reflexivity | exact Hrho36 | reflexivity | reflexivity | exact R_nd | lia | closed_side | closed_side | exact W_nd | | closed_side].
  constructor; [|constructor].
  apply (fact_ptr rho m ND 0 38%uint63 ES Hrho38 (chunk_word ES 904 R_es ltac:(lia))). rewrite Z.add_0_r. exact (c8_bytes m _ _ C_nd).
Qed.

Definition ES_ZS : list Z := repeat 0 704 ++ repeat 255 64 ++ repeat 0 136.

Lemma eg38_ok : region_ok bsegs rho 38%uint63 eg_38 m.
Proof.
  destruct C_es as [[Hwf Hb] Hw]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. cbn [cells_size csize Nat.add] in Hw.
  apply (chunk_learn 38%uint63 eg_38 ES 904 [(0, kbs_bytes ES_ZS)]);
    [reflexivity | exact Hrho38 | reflexivity | reflexivity | exact R_es | lia | closed_side | closed_side | exact Hw | | closed_side].
  constructor; [|constructor]. exists (map (Z_to_bv 8) ES_ZS). split.
  - cbn [snd]. apply kbs_bytes_intro. unfold ES_ZS. apply Forall_app. split; [|apply Forall_app; split];
      apply Forall_forall; intros z Hz; apply repeat_spec in Hz; subst z; lia.
  - cbn [fst]. rewrite Z.add_0_r. unfold ES_ZS. rewrite !map_app, !map_repeat. exact Hb.
Qed.

Lemma eg33_ok : region_ok bsegs rho 33%uint63 eg_33 m.
Proof. destruct R_mk as (K1 & _ & K3 & _). apply (chunk_shadow 33%uint63 9 1 MK Hrho33 K1); [change (to_Z 9%uint63) with 9; lia | closed_side | closed_side | exact Z_mk]. Qed.
Lemma eg35_ok : region_ok bsegs rho 35%uint63 eg_35 m.
Proof. destruct R_sa as (K1 & _ & K3 & _). apply (chunk_shadow 35%uint63 4 0 SA Hrho35 K1); [change (to_Z 4%uint63) with 4; lia | closed_side | closed_side | exact Z_sa]. Qed.
Lemma eg37_ok : region_ok bsegs rho 37%uint63 eg_37 m.
Proof. destruct R_nd as (K1 & _ & K3 & _). apply (chunk_shadow 37%uint63 16 1 ND Hrho37 K1); [change (to_Z 16%uint63) with 16; lia | closed_side | closed_side | exact Z_nd]. Qed.
Lemma eg39_ok : region_ok bsegs rho 39%uint63 eg_39 m.
Proof. destruct R_es as (K1 & _ & K3 & _). apply (chunk_shadow 39%uint63 113 4 ES Hrho39 K1); [change (to_Z 113%uint63) with 113; lia | closed_side | closed_side | exact Z_es]. Qed.

Definition ivw (t : int) (rg : region) : Z * Z * bool := (rbase rho t rg, rbase rho t rg + to_Z (rg_size rg), rg_wr rg).

Local Ltac sepw1 :=
  cbn [fst snd]; first [ intros [X|X]; discriminate X | intros _; lia ].
Local Ltac sepw :=
  unfold ivw, rbase; cbn [rg_abs rg_size rg_wr eg_2 eg_3 eg_4 eg_5 eg_6 eg_7 eg_8 eg_9 eg_10 eg_11 eg_32 eg_33 eg_34 eg_35 eg_36 eg_37 eg_38 eg_39];
  rewrite ?Hrho2, ?Hrho3, ?Hrho32, ?Hrho33, ?Hrho34, ?Hrho35, ?Hrho36, ?Hrho37, ?Hrho38, ?Hrho39, ?sz2, ?sz3;
  repeat match goal with |- context [to_Z ?x] => lazymatch x with ri => fail | _ => idtac end; is_ground x; let v := eval vm_compute in (to_Z x) in change (to_Z x) with v end;
  repeat (constructor; [sepw1|]); constructor.

(* [comment removed for export] *)
Lemma rmemE : Rmem bsegs rho (ME ri) m.
Proof.
  destruct B0_facts as (F1 & F2 & F3 & F4). pose proof Hri01 as Hr. pose proof lo_hi as Hlh. unfold USTACK_TOP in *.
  pose proof R_mk as (KM1 & _ & KM3 & _). pose proof R_sa as (KS1 & _ & KS3 & _). pose proof R_nd as (KN1 & _ & KN3 & _). pose proof R_es as (KE1 & _ & KE3 & KE4 & KE5).
  destruct (shad_chunk MK 9 KM1 ltac:(lia) ltac:(lia)) as [SM1 SM2]. destruct (shad_chunk SA 4 KS1 ltac:(lia) ltac:(lia)) as [SS1 SS2].
  destruct (shad_chunk ND 16 KN1 ltac:(lia) ltac:(lia)) as [SN1 SN2]. destruct (shad_chunk ES 113 KE1 ltac:(lia) ltac:(lia)) as [SE1 SE2].
  assert (F5 : shad (sp0 - to_Z ri - 81920) + (81920 + to_Z ri) / 8 <= 0x10007fff8000) by (unfold shad, SHB; Z.div_mod_to_equations; lia).
  pose proof D_mk as DM. pose proof D_sa as DS. pose proof D_nd as DN. unfold apart in DM, DS, DN.
  pose proof (Rmem_empty bsegs rho m) as R3x. pose proof (dir_inw_empty rho) as I3x.
  assert (RI4 : Rmem bsegs rho ME_4 m /\ dir_inw rho ME_4 ([ivw 4%uint63 eg_4])).
  { unfold ME_4. apply (Rmem_add_sepw bsegs rho IEmpty 4%uint63 eg_4 m ([]) R3x I3x); [vm_compute; reflexivity | vm_compute; reflexivity | exact eg4_ok | sepw]. }
  destruct RI4 as [R4x I4x]. clear R3x I3x.
  assert (RI5 : Rmem bsegs rho ME_5 m /\ dir_inw rho ME_5 ([ivw 5%uint63 eg_5; ivw 4%uint63 eg_4])).
  { unfold ME_5. apply (Rmem_add_sepw bsegs rho ME_4 5%uint63 eg_5 m ([ivw 4%uint63 eg_4]) R4x I4x); [vm_compute; reflexivity | vm_compute; reflexivity | exact eg5_ok | sepw]. }
  destruct RI5 as [R5x I5x]. clear R4x I4x.
  assert (RI6 : Rmem bsegs rho ME_6 m /\ dir_inw rho ME_6 ([ivw 6%uint63 eg_6; ivw 5%uint63 eg_5; ivw 4%uint63 eg_4])).
  { unfold ME_6. apply (Rmem_add_sepw bsegs rho ME_5 6%uint63 eg_6 m ([ivw 5%uint63 eg_5; ivw 4%uint63 eg_4]) R5x I5x); [vm_compute; reflexivity | vm_compute; reflexivity | exact eg6_ok | sepw]. }
  destruct RI6 as [R6x I6x]. clear R5x I5x.
  assert (RI7 : Rmem bsegs rho ME_7 m /\ dir_inw rho ME_7 ([ivw 7%uint63 eg_7; ivw 6%uint63 eg_6; ivw 5%uint63 eg_5; ivw 4%uint63 eg_4])).
  { unfold ME_7. apply (Rmem_add_sepw bsegs rho ME_6 7%uint63 eg_7 m ([ivw 6%uint63 eg_6; ivw 5%uint63 eg_5; ivw 4%uint63 eg_4]) R6x I6x); [vm_compute; reflexivity | vm_compute; reflexivity | exact eg7_ok | sepw]. }
  destruct RI7 as [R7x I7x]. clear R6x I6x.
  assert (RI8 : Rmem bsegs rho ME_8 m /\ dir_inw rho ME_8 ([ivw 8%uint63 eg_8; ivw 7%uint63 eg_7; ivw 6%uint63 eg_6; ivw 5%uint63 eg_5; ivw 4%uint63 eg_4])).
  { unfold ME_8. apply (Rmem_add_sepw bsegs rho ME_7 8%uint63 eg_8 m ([ivw 7%uint63 eg_7; ivw 6%uint63 eg_6; ivw 5%uint63 eg_5; ivw 4%uint63 eg_4]) R7x I7x); [vm_compute; reflexivity | vm_compute; reflexivity | exact eg8_ok | sepw]. }
  destruct RI8 as [R8x I8x]. clear R7x I7x.
  assert (RI9 : Rmem bsegs rho ME_9 m /\ dir_inw rho ME_9 ([ivw 9%uint63 eg_9; ivw 8%uint63 eg_8; ivw 7%uint63 eg_7; ivw 6%uint63 eg_6; ivw 5%uint63 eg_5; ivw 4%uint63 eg_4])).
  { unfold ME_9. apply (Rmem_add_sepw bsegs rho ME_8 9%uint63 eg_9 m ([ivw 8%uint63 eg_8; ivw 7%uint63 eg_7; ivw 6%uint63 eg_6; ivw 5%uint63 eg_5; ivw 4%uint63 eg_4]) R8x I8x); [vm_compute; reflexivity | vm_compute; reflexivity | exact eg9_ok | sepw]. }
  destruct RI9 as [R9x I9x]. clear R8x I8x.
  assert (RI10 : Rmem bsegs rho ME_10 m /\ dir_inw rho ME_10 ([ivw 10%uint63 eg_10; ivw 9%uint63 eg_9; ivw 8%uint63 eg_8; ivw 7%uint63 eg_7; ivw 6%uint63 eg_6; ivw 5%uint63 eg_5; ivw 4%uint63 eg_4])).
  { unfold ME_10. apply (Rmem_add_sepw bsegs rho ME_9 10%uint63 eg_10 m ([ivw 9%uint63 eg_9; ivw 8%uint63 eg_8; ivw 7%uint63 eg_7; ivw 6%uint63 eg_6; ivw 5%uint63 eg_5; ivw 4%uint63 eg_4]) R9x I9x); [vm_compute; reflexivity | vm_compute; reflexivity | exact eg10_ok | sepw]. }
  destruct RI10 as [R10x I10x]. clear R9x I9x.
  assert (RI11 : Rmem bsegs rho ME_11 m /\ dir_inw rho ME_11 ([ivw 11%uint63 eg_11; ivw 10%uint63 eg_10; ivw 9%uint63 eg_9; ivw 8%uint63 eg_8; ivw 7%uint63 eg_7; ivw 6%uint63 eg_6; ivw 5%uint63 eg_5; ivw 4%uint63 eg_4])).
  { unfold ME_11. apply (Rmem_add_sepw bsegs rho ME_10 11%uint63 eg_11 m ([ivw 10%uint63 eg_10; ivw 9%uint63 eg_9; ivw 8%uint63 eg_8; ivw 7%uint63 eg_7; ivw 6%uint63 eg_6; ivw 5%uint63 eg_5; ivw 4%uint63 eg_4]) R10x I10x); [vm_compute; reflexivity | vm_compute; reflexivity | exact eg11_ok | sepw]. }
  destruct RI11 as [R11x I11x]. clear R10x I10x.
  assert (RI32 : Rmem bsegs rho ME_32 m /\ dir_inw rho ME_32 ([ivw 32%uint63 eg_32; ivw 11%uint63 eg_11; ivw 10%uint63 eg_10; ivw 9%uint63 eg_9; ivw 8%uint63 eg_8; ivw 7%uint63 eg_7; ivw 6%uint63 eg_6; ivw 5%uint63 eg_5; ivw 4%uint63 eg_4])).
  { unfold ME_32. apply (Rmem_add_sepw bsegs rho ME_11 32%uint63 eg_32 m ([ivw 11%uint63 eg_11; ivw 10%uint63 eg_10; ivw 9%uint63 eg_9; ivw 8%uint63 eg_8; ivw 7%uint63 eg_7; ivw 6%uint63 eg_6; ivw 5%uint63 eg_5; ivw 4%uint63 eg_4]) R11x I11x); [vm_compute; reflexivity | vm_compute; reflexivity | exact eg32_ok | sepw]. }
  destruct RI32 as [R32x I32x]. clear R11x I11x.
  assert (RI33 : Rmem bsegs rho ME_33 m /\ dir_inw rho ME_33 ([ivw 33%uint63 eg_33; ivw 32%uint63 eg_32; ivw 11%uint63 eg_11; ivw 10%uint63 eg_10; ivw 9%uint63 eg_9; ivw 8%uint63 eg_8; ivw 7%uint63 eg_7; ivw 6%uint63 eg_6; ivw 5%uint63 eg_5; ivw 4%uint63 eg_4])).
  { unfold ME_33. apply (Rmem_add_sepw bsegs rho ME_32 33%uint63 eg_33 m ([ivw 32%uint63 eg_32; ivw 11%uint63 eg_11; ivw 10%uint63 eg_10; ivw 9%uint63 eg_9; ivw 8%uint63 eg_8; ivw 7%uint63 eg_7; ivw 6%uint63 eg_6; ivw 5%uint63 eg_5; ivw 4%uint63 eg_4]) R32x I32x); [vm_compute; reflexivity | vm_compute; reflexivity | exact eg33_ok | sepw]. }
  destruct RI33 as [R33x I33x]. clear R32x I32x.
  assert (RI34 : Rmem bsegs rho ME_34 m /\ dir_inw rho ME_34 ([ivw 34%uint63 eg_34; ivw 33%uint63 eg_33; ivw 32%uint63 eg_32; ivw 11%uint63 eg_11; ivw 10%uint63 eg_10; ivw 9%uint63 eg_9; ivw 8%uint63 eg_8; ivw 7%uint63 eg_7; ivw 6%uint63 eg_6; ivw 5%uint63 eg_5; ivw 4%uint63 eg_4])).
  { unfold ME_34. apply (Rmem_add_sepw bsegs rho ME_33 34%uint63 eg_34 m ([ivw 33%uint63 eg_33; ivw 32%uint63 eg_32; ivw 11%uint63 eg_11; ivw 10%uint63 eg_10; ivw 9%uint63 eg_9; ivw 8%uint63 eg_8; ivw 7%uint63 eg_7; ivw 6%uint63 eg_6; ivw 5%uint63 eg_5; ivw 4%uint63 eg_4]) R33x I33x); [vm_compute; reflexivity | vm_compute; reflexivity | exact eg34_ok | sepw]. }
  destruct RI34 as [R34x I34x]. clear R33x I33x.
  assert (RI35 : Rmem bsegs rho ME_35 m /\ dir_inw rho ME_35 ([ivw 35%uint63 eg_35; ivw 34%uint63 eg_34; ivw 33%uint63 eg_33; ivw 32%uint63 eg_32; ivw 11%uint63 eg_11; ivw 10%uint63 eg_10; ivw 9%uint63 eg_9; ivw 8%uint63 eg_8; ivw 7%uint63 eg_7; ivw 6%uint63 eg_6; ivw 5%uint63 eg_5; ivw 4%uint63 eg_4])).
  { unfold ME_35. apply (Rmem_add_sepw bsegs rho ME_34 35%uint63 eg_35 m ([ivw 34%uint63 eg_34; ivw 33%uint63 eg_33; ivw 32%uint63 eg_32; ivw 11%uint63 eg_11; ivw 10%uint63 eg_10; ivw 9%uint63 eg_9; ivw 8%uint63 eg_8; ivw 7%uint63 eg_7; ivw 6%uint63 eg_6; ivw 5%uint63 eg_5; ivw 4%uint63 eg_4]) R34x I34x); [vm_compute; reflexivity | vm_compute; reflexivity | exact eg35_ok | sepw]. }
  destruct RI35 as [R35x I35x]. clear R34x I34x.
  assert (RI36 : Rmem bsegs rho ME_36 m /\ dir_inw rho ME_36 ([ivw 36%uint63 eg_36; ivw 35%uint63 eg_35; ivw 34%uint63 eg_34; ivw 33%uint63 eg_33; ivw 32%uint63 eg_32; ivw 11%uint63 eg_11; ivw 10%uint63 eg_10; ivw 9%uint63 eg_9; ivw 8%uint63 eg_8; ivw 7%uint63 eg_7; ivw 6%uint63 eg_6; ivw 5%uint63 eg_5; ivw 4%uint63 eg_4])).
  { unfold ME_36. apply (Rmem_add_sepw bsegs rho ME_35 36%uint63 eg_36 m ([ivw 35%uint63 eg_35; ivw 34%uint63 eg_34; ivw 33%uint63 eg_33; ivw 32%uint63 eg_32; ivw 11%uint63 eg_11; ivw 10%uint63 eg_10; ivw 9%uint63 eg_9; ivw 8%uint63 eg_8; ivw 7%uint63 eg_7; ivw 6%uint63 eg_6; ivw 5%uint63 eg_5; ivw 4%uint63 eg_4]) R35x I35x); [vm_compute; reflexivity | vm_compute; reflexivity | exact eg36_ok | sepw]. }
  destruct RI36 as [R36x I36x]. clear R35x I35x.
  assert (RI37 : Rmem bsegs rho ME_37 m /\ dir_inw rho ME_37 ([ivw 37%uint63 eg_37; ivw 36%uint63 eg_36; ivw 35%uint63 eg_35; ivw 34%uint63 eg_34; ivw 33%uint63 eg_33; ivw 32%uint63 eg_32; ivw 11%uint63 eg_11; ivw 10%uint63 eg_10; ivw 9%uint63 eg_9; ivw 8%uint63 eg_8; ivw 7%uint63 eg_7; ivw 6%uint63 eg_6; ivw 5%uint63 eg_5; ivw 4%uint63 eg_4])).
  { unfold ME_37. apply (Rmem_add_sepw bsegs rho ME_36 37%uint63 eg_37 m ([ivw 36%uint63 eg_36; ivw 35%uint63 eg_35; ivw 34%uint63 eg_34; ivw 33%uint63 eg_33; ivw 32%uint63 eg_32; ivw 11%uint63 eg_11; ivw 10%uint63 eg_10; ivw 9%uint63 eg_9; ivw 8%uint63 eg_8; ivw 7%uint63 eg_7; ivw 6%uint63 eg_6; ivw 5%uint63 eg_5; ivw 4%uint63 eg_4]) R36x I36x); [vm_compute; reflexivity | vm_compute; reflexivity | exact eg37_ok | sepw]. }
  destruct RI37 as [R37x I37x]. clear R36x I36x.
  assert (RI38 : Rmem bsegs rho ME_38 m /\ dir_inw rho ME_38 ([ivw 38%uint63 eg_38; ivw 37%uint63 eg_37; ivw 36%uint63 eg_36; ivw 35%uint63 eg_35; ivw 34%uint63 eg_34; ivw 33%uint63 eg_33; ivw 32%uint63 eg_32; ivw 11%uint63 eg_11; ivw 10%uint63 eg_10; ivw 9%uint63 eg_9; ivw 8%uint63 eg_8; ivw 7%uint63 eg_7; ivw 6%uint63 eg_6; ivw 5%uint63 eg_5; ivw 4%uint63 eg_4])).
  { unfold ME_38. apply (Rmem_add_sepw bsegs rho ME_37 38%uint63 eg_38 m ([ivw 37%uint63 eg_37; ivw 36%uint63 eg_36; ivw 35%uint63 eg_35; ivw 34%uint63 eg_34; ivw 33%uint63 eg_33; ivw 32%uint63 eg_32; ivw 11%uint63 eg_11; ivw 10%uint63 eg_10; ivw 9%uint63 eg_9; ivw 8%uint63 eg_8; ivw 7%uint63 eg_7; ivw 6%uint63 eg_6; ivw 5%uint63 eg_5; ivw 4%uint63 eg_4]) R37x I37x); [vm_compute; reflexivity | vm_compute; reflexivity | exact eg38_ok | sepw]. }
  destruct RI38 as [R38x I38x]. clear R37x I37x.
  assert (RI39 : Rmem bsegs rho ME_39 m /\ dir_inw rho ME_39 ([ivw 39%uint63 eg_39; ivw 38%uint63 eg_38; ivw 37%uint63 eg_37; ivw 36%uint63 eg_36; ivw 35%uint63 eg_35; ivw 34%uint63 eg_34; ivw 33%uint63 eg_33; ivw 32%uint63 eg_32; ivw 11%uint63 eg_11; ivw 10%uint63 eg_10; ivw 9%uint63 eg_9; ivw 8%uint63 eg_8; ivw 7%uint63 eg_7; ivw 6%uint63 eg_6; ivw 5%uint63 eg_5; ivw 4%uint63 eg_4])).
  { unfold ME_39. apply (Rmem_add_sepw bsegs rho ME_38 39%uint63 eg_39 m ([ivw 38%uint63 eg_38; ivw 37%uint63 eg_37; ivw 36%uint63 eg_36; ivw 35%uint63 eg_35; ivw 34%uint63 eg_34; ivw 33%uint63 eg_33; ivw 32%uint63 eg_32; ivw 11%uint63 eg_11; ivw 10%uint63 eg_10; ivw 9%uint63 eg_9; ivw 8%uint63 eg_8; ivw 7%uint63 eg_7; ivw 6%uint63 eg_6; ivw 5%uint63 eg_5; ivw 4%uint63 eg_4]) R38x I38x); [vm_compute; reflexivity | vm_compute; reflexivity | exact eg39_ok | sepw]. }
  destruct RI39 as [R39x I39x]. clear R38x I38x.
  assert (RIs : Rmem bsegs rho (ME_3 ri) m /\ dir_inw rho (ME_3 ri) ([ivw 3%uint63 (eg_3 ri); ivw 39%uint63 eg_39; ivw 38%uint63 eg_38; ivw 37%uint63 eg_37; ivw 36%uint63 eg_36; ivw 35%uint63 eg_35; ivw 34%uint63 eg_34; ivw 33%uint63 eg_33; ivw 32%uint63 eg_32; ivw 11%uint63 eg_11; ivw 10%uint63 eg_10; ivw 9%uint63 eg_9; ivw 8%uint63 eg_8; ivw 7%uint63 eg_7; ivw 6%uint63 eg_6; ivw 5%uint63 eg_5; ivw 4%uint63 eg_4])).
  { unfold ME_3, ME_abs. apply (Rmem_add_sepw bsegs rho ME_39 3%uint63 (eg_3 ri) m ([ivw 39%uint63 eg_39; ivw 38%uint63 eg_38; ivw 37%uint63 eg_37; ivw 36%uint63 eg_36; ivw 35%uint63 eg_35; ivw 34%uint63 eg_34; ivw 33%uint63 eg_33; ivw 32%uint63 eg_32; ivw 11%uint63 eg_11; ivw 10%uint63 eg_10; ivw 9%uint63 eg_9; ivw 8%uint63 eg_8; ivw 7%uint63 eg_7; ivw 6%uint63 eg_6; ivw 5%uint63 eg_5; ivw 4%uint63 eg_4]) R39x I39x); [vm_compute; reflexivity | vm_compute; reflexivity | exact eg3_ok | sepw]. }
  destruct RIs as [Rsx Isx].
  unfold ME. apply (Rmem_add_sepw bsegs rho (ME_3 ri) 2%uint63 (eg_2 ri) m ([ivw 3%uint63 (eg_3 ri); ivw 39%uint63 eg_39; ivw 38%uint63 eg_38; ivw 37%uint63 eg_37; ivw 36%uint63 eg_36; ivw 35%uint63 eg_35; ivw 34%uint63 eg_34; ivw 33%uint63 eg_33; ivw 32%uint63 eg_32; ivw 11%uint63 eg_11; ivw 10%uint63 eg_10; ivw 9%uint63 eg_9; ivw 8%uint63 eg_8; ivw 7%uint63 eg_7; ivw 6%uint63 eg_6; ivw 5%uint63 eg_5; ivw 4%uint63 eg_4]) Rsx Isx); [destruct H_ri as [-> | ->]; vm_compute; reflexivity | vm_compute; reflexivity | exact eg2_ok | sepw].
Qed.

End Handoff.
