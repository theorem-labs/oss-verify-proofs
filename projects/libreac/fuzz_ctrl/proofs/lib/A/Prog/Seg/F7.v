(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3817 of its 3853 lines of code are new or changed and 212 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/ctrl_lay_block.v, with its module paths and module names changed; 371 of its 396 lines of code are new or changed and 3828 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/P2.v; 688 of its 728 lines of code are new or changed and 356 lines of the source are left out. *)
(* Segment F7 (0x81f64-0x81f78, plan-asan 2 row F7, call KN@0x81f78): the frame-loop check of the parse result
   and the first reac_ctrl_kind_name call.
     0x81f64 bne a0,s8,fail     a0 = s8 = v (carried): not taken
     0x81f68 ld  a0,248(s1)     a0 = [A+248] = fr+176 (the parse record)
     0x81f6c lw  a0,0(a0)       a0 = sext32 [fr+176] = v (0 <= v < 2^31)
     0x81f70 bne s8,a0,fail     s8 = a0 = v: not taken
     0x81f74 mv  a0,s8          a0 = v
     0x81f78 jal reac_ctrl_kind_name
   The range holds no load of a shadow byte. The segment runs through the call (the lib/A contract
   reac_ctrl_kind_name_contract, a Section Hypothesis) and ends at its return point 0x81f7c with
   a0 = kind_name_addr v. The callee writes only its stack window W = [sp-16, sp); FRA moves across that write
   and the lazy-page model step by Tac_b5.sl_callee_keep, ENT by Tac_slot.ent_store and ent_mat (W lies in the
   entry-anchored slot window). No cut pins sp = s1: on the real-stack arm sp = fr < s1, so the spill base s1 is
   FRA's A (sp <= A). Entry cut SlotInv.Inv_A81f64_at, exit cut SlotInv.Inv_A81f7c_at (F8's entry). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcKind RcKindLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import reac_ctrl_kind_name_c
  reac_ctrl_identity_fragment_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_b5.
Import ListNotations.
Import YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.FrameAPI.
Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.

(* The lw at 0x81f6c sign-extends the low 32 bits; a value below 2^31 is kept. *)
Lemma sx32_small : forall v, 0 <= v < 2 ^ 31 -> sx32 (Z_to_bv 64 v) = Z_to_bv 64 v.
Proof.
  intros v Hv. unfold sx32. rewrite (unsigned_lit v) by lia. f_equal.
  unfold bv_swrap. change (bv_half_modulus 32) with (2 ^ 31). unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32).
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma kn_len : length kind_name_bytes = 112%nat.
Proof. reflexivity. Qed.

(* The kind-name strings are read-only image bytes (the same check as reac_ctrl_kind_name_strings_in_image). *)
Lemma kn_strings : forall m, mem_inv rsegs m -> kind_name_strings m.
Proof.
  intros m Hm x Hx. destruct (Z.leb_spec x 13) as [Hle|Hgt].
  - destruct (rc_Z_le13 x ltac:(lia)) as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| -> ]]]]]]]]]]]]];
      (apply rc_ro_in_image; [exact Hm | vm_compute; reflexivity]).
  - assert (E : kind_name_addr x = QMARK)
      by (unfold kind_name_addr; rewrite (proj2 (Z.leb_gt x 13) Hgt); reflexivity).
    rewrite E, (kind_name_big x Hgt).
    apply rc_ro_in_image; [exact Hm | vm_compute; reflexivity].
Qed.

(* kind_name_strings from ro_agree alone (the name table is read-only image). The b5 cut carries ro_agree,
   not mem_inv: the strings hold on the normalized memory (where mem_inv is free) and transport back by
   mem_rel. *)
Lemma f7_kn_strings_ro : forall m, ro_agree rsegs m -> kind_name_strings m.
Proof.
  intros m Hro x Hx.
  apply (proj2 (MemNorm.bytes_at_rel rsegs m (MemNorm.normalize rsegs m)
                 (kind_name_addr x) (cstr_bytes (kind_name x))
                 (MemNorm.mem_rel_normalize rsegs m Hro))).
  exact (kn_strings (MemNorm.normalize rsegs m) (MemNorm.mem_inv_normalize rsegs m) x Hx).
Qed.

(* The base of a carried `spill` is the cut's own A: reg 9 pins it only mod 2 ^ 64, and q64's own range bounds
   (0 <= a, a + 8 <= 2 ^ 64) put it back in [0, 2 ^ 64), so the two agree. *)
Lemma f7_spill_base : forall (regs : bvmap 5 word) (mem : word -> option byte) (A off v : Z),
  rg regs 9 A -> 0 <= A -> A + 416 < 2 ^ 64 -> 0 <= off <= 416 ->
  spill regs mem off v -> q64 mem (A + off) v.
Proof.
  intros regs mem A off v H9 HA0 HA64 Hoff (A' & HA' & Hq').
  pose proof Hq' as Hq2. unfold q64, bytes_at in Hq2. destruct Hq2 as (Hb0 & Hb1 & _).
  rewrite length_le8 in Hb1.
  pose proof (rg_eq64 regs 9 A' A HA' H9) as Hm.
  rewrite (Z.mod_small A (2 ^ 64)) in Hm by lia.
  pose proof (Z.div_mod A' (2 ^ 64) ltac:(lia)) as Hdm.
  rewrite Hm in Hdm.
  assert (Hq0 : A' / 2 ^ 64 = 0) by lia.
  rewrite Hq0 in Hdm.
  assert (EA : A' = A) by lia.
  subst A'. exact Hq'.
Qed.

(* The identity record of every turn is ID_SIZE = 38 bytes: ID0 is, and each ingest keeps the length
   (RcIdentModel.ING_length). F7 carries IDj's bytes at fr + 2688 inside the frame body. *)
Lemma f7_tID_len : forall inp j, length (t_ID inp j) = 38%nat.
Proof.
  assert (Hturn : forall s len g, length (fs_id s) = 38%nat -> length (fs_id (turn s len g)) = 38%nat).
  { intros s len g Hs.
    assert (Hr : length (rp_id (fs_id s) len g) = 38%nat).
    { unfold rp_id. destruct (RcReply.ir len g); [exact (RcIdentModel.ING_length _ _ _ Hs) | exact Hs]. }
    unfold turn. cbv zeta. unfold fg_id.
    destruct (f_opens len g); cbn [fs_id];
      (destruct (fg_rf len (fs_fg s) g =? 1); [exact (RcIdentModel.ING_length _ _ _ Hr) | exact Hr]). }
  intros inp j. unfold t_ID. induction j as [|j IH]; [reflexivity|].
  cbn [fst_at]. exact (Hturn _ _ _ IH).
Qed.

(* The first fragment's body of every turn is at most 23 bytes: fs0's is empty and an opening turn keeps at most
   the 23 bytes block[9 ..] of the 50-byte frame (SlotModel.turn), so FSb's body at fr + 2880 lies inside the
   frame body. *)
Lemma f7_fsb_len : forall inp j, (length (fs_body (fst_at inp j)) <= 23)%nat.
Proof.
  intros inp j. induction j as [|j IH].
  - cbn [fst_at]. unfold fs0. cbn [fs_body length]. lia.
  - rewrite fst_at_S. unfold turn. cbv zeta.
    destruct (f_opens (t_len inp j) (t_g inp j)); cbn [fs_body]; [|exact IH].
    rewrite length_firstn, length_skipn. unfold t_g. rewrite fr50_length. lia.
Qed.

(* Register 9 pins its value only mod 2 ^ 64, so two in-range readings agree. *)
Lemma f7_rg9 : forall (regs : bvmap 5 word) (A A' : Z), rg regs 9 A -> rg regs 9 A' ->
  0 <= A < 2 ^ 64 -> 0 <= A' < 2 ^ 64 -> A' = A.
Proof.
  intros regs A A' H H' HA HA'. pose proof (rg_eq64 regs 9 A' A H' H) as Hm.
  rewrite (Z.mod_small A' (2 ^ 64)) in Hm by lia. rewrite (Z.mod_small A (2 ^ 64)) in Hm by lia. exact Hm.
Qed.

(* A prefix of a carried byte list is carried. *)
Lemma f7_bytes_firstn : forall m a bs n, bytes_at rsegs m a bs -> bytes_at rsegs m a (firstn n bs).
Proof.
  intros m a bs n (H0 & H1 & H). pose proof (length_firstn n bs) as HL.
  split; [exact H0|]. split; [lia|].
  intros i Hi. rewrite (H i ltac:(lia)).
  rewrite <- (firstn_skipn n bs) at 1. apply nth_error_app1. lia.
Qed.

(* The memcmp model reads only the first n bytes of each side. *)
Lemma f7_memcmp_firstn : forall n l r, SFA.memcmp_model (firstn n l) (firstn n r) n = SFA.memcmp_model l r n.
Proof.
  induction n as [|n IH]; intros [|a l] [|b r]; cbn; try reflexivity.
  destruct (bv_unsigned a =? bv_unsigned b); [apply IH | reflexivity].
Qed.

(* A slice is at most as long as its count, and a turn's record bytes at most its length. *)
Lemma f7_bsl_len : forall bs k n, (length (RcFrag.bsl bs k n) <= Z.to_nat n)%nat.
Proof. intros bs k n. unfold RcFrag.bsl. rewrite length_firstn. lia. Qed.
Lemma f7_tphi_len : forall g j, (length (t_phi (g_in g) j) <= Z.to_nat (flen g j))%nat.
Proof. intros g j. unfold flen, t_phi, t_len, f_phi. rewrite length_firstn. lia. Qed.

(* The 0x88 0x19 record test implies the long arm. *)
Lemma f7_8819_big : forall g j, t_8819 (g_in g) j = true -> 50 <= flen g j.
Proof.
  intros g j H. unfold flen, t_8819 in *.
  apply andb_prop in H. destruct H as (H & _). apply andb_prop in H. destruct H as (H & _).
  unfold t_big in H. apply Z.leb_le in H. exact H.
Qed.

(* addressable survives a run whose writes miss the shadow bytes of the range. *)
Lemma f7_addr_keep : forall W m m' p n,
  addressable m p n -> munch W m m' ->
  (forall i, 0 <= i < n -> outside W (shadow_addr (p + i))) -> addressable m' p n.
Proof.
  intros W m m' p n (H0 & Hn & He & HA) Hm HW. split; [exact H0|]. split; [exact Hn|]. split; [exact He|].
  intros i Hi. destruct (HA i Hi) as (Hap & b & Hb & Hok). split; [exact Hap|]. exists b. split; [|exact Hok].
  pose proof (shadow_of_app (p + i) Hap) as Hs. pose proof (in_shadow_range _ Hs) as Hbd.
  unfold mrd in *. rewrite Hm; [exact Hb|]. rewrite wa_unsigned by lia. exact (HW i Hi).
Qed.

(* The shadow of an app-range address is below HIGHMEM_BEG, and Z.shiftr a 3 + ASAN_K is that address. *)
Lemma f7_sh_hi : forall a, a <= APPMEM_END -> shadow_addr a <= HIGHMEM_BEG.
Proof.
  intros a Ha. unfold shadow_addr, ASAN_K, HIGHMEM_BEG.
  assert (D : a / 8 <= 17592186044416) by (apply Z.div_le_upper_bound; unfold APPMEM_END in *; lia).
  lia.
Qed.
Lemma f7_shiftr_shadow : forall a, Z.shiftr a 3 + ASAN_K = shadow_addr a.
Proof. intros a. unfold shadow_addr. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.

(* b5_PF (push 14 groups C / E) across a write that misses the save area below [A + 280), the frame body and
   the record block, with the shadow bytes of the last two: every conjunct is a spill word, a frame cell, a
   record byte or a metadata byte of the record. The byte lists whose length the text leaves open (the 38-byte
   record prefix and the two 6-byte compare operands) are re-witnessed by their `firstn`, which the memcmp
   model does not see. *)
Lemma f7_pf_keep : forall g j phi fr A regs regs' mem mem' W,
  b5_PF g j phi fr regs mem -> rg regs 9 A -> 0 <= A < 2 ^ 64 -> A + 416 < 2 ^ 64 ->
  getr regs' 9 = getr regs 9 -> munch W mem mem' ->
  0 <= phi -> phi + AC.a_size (flen g j) <= APPMEM_END ->
  (forall x, A <= x < A + 280 -> outside W x) ->
  (forall x, fr <= x < fr + FRAME_BYTES -> outside W x /\ outside W (shadow_addr x)) ->
  (forall x, phi <= x < phi + AC.a_size (flen g j) -> outside W x /\ outside W (shadow_addr x)) ->
  b5_PF g j phi fr regs' mem'.
Proof.
  intros g j phi fr A regs regs' mem mem' W (A1 & H9a & HA1 & Hrec & H88) H9 HA HA4 E9 MU Hphi0 HphiE
    OA Ofr Oph.
  pose proof FRAME_BYTES_val as HFBv.
  rewrite (f7_rg9 regs A A1 H9 H9a HA HA1) in *.
  assert (H9' : rg regs' 9 A) by (unfold rg in *; rewrite E9; exact H9).
  assert (Hq : forall off v, 0 <= off <= 272 -> q64 mem (A + off) v -> q64 mem' (A + off) v).
  { intros off v Hoff Hqv. unfold q64 in *. apply (fl_bytes W mem mem' (A + off) _ Hqv MU).
    rewrite length_le8. intros x Hx. apply OA. lia. }
  assert (Hblk : forall a bs, phi <= a -> a + Z.of_nat (length bs) <= phi + AC.a_size (flen g j) ->
      bytes_at rsegs mem a bs -> bytes_at rsegs mem' a bs).
  { intros a bs Ha Hb Hbs. apply (fl_bytes W mem mem' a bs Hbs MU).
    intros x Hx. exact (proj1 (Oph x ltac:(lia))). }
  assert (Hfrm : forall a bs, fr <= a -> a + Z.of_nat (length bs) <= fr + FRAME_BYTES ->
      bytes_at rsegs mem a bs -> bytes_at rsegs mem' a bs).
  { intros a bs Ha Hb Hbs. apply (fl_bytes W mem mem' a bs Hbs MU).
    intros x Hx. exact (proj1 (Ofr x ltac:(lia))). }
  assert (Hsh : forall a, phi <= a < phi + AC.a_size (flen g j) ->
      b8 mem (Z.shiftr a 3 + ASAN_K) 0 -> b8 mem' (Z.shiftr a 3 + ASAN_K) 0).
  { intros a Ha Hb. unfold b8 in *. apply (fl_bytes W mem mem' _ _ Hb MU).
    cbn [length]. intros x Hx. replace x with (Z.shiftr a 3 + ASAN_K) by lia.
    rewrite f7_shiftr_shadow. exact (proj2 (Oph a Ha)). }
  exists A. split; [exact H9'|]. split; [exact HA|].
  split.
  { intros Hlen.
    assert (Esz : AC.a_size (flen g j) = flen g j) by (unfold AC.a_size; lia).
    destruct (Hrec Hlen) as ((rb & Hrb & Hrbl) & Htphi).
    split.
    { exists (firstn 38 rb). split.
      - exact (Hblk phi (firstn 38 rb) ltac:(lia) ltac:(rewrite length_firstn; lia)
                 (f7_bytes_firstn mem phi rb 38 Hrb)).
      - rewrite length_firstn. lia. }
    pose proof (f7_tphi_len g j) as HL.
    exact (Hblk phi (t_phi (g_in g) j) ltac:(lia) ltac:(lia) Htphi). }
  intros H8819. pose proof (f7_8819_big g j H8819) as Hbig.
  assert (Esz : AC.a_size (flen g j) = flen g j) by (unfold AC.a_size; lia).
  destruct (H88 H8819) as
    ((field16 & v14 & v15 & v16 & v17 & Hu16 & Hb14 & Hb15 & Hb16 & Hb17 &
      Hr14 & Hr15 & Hr16 & Hr17 & Hs14 & Hs15 & Hs16 & Hs17 & Hf16 & Hzz) &
     (ls & rs & Hq72 & Hls & Hlsl & Hrs & Hrsl & Hcmp & Had186) &
     (ls2 & rs2 & Hq64 & Hls2 & Hls2l & Hrs2 & Hrs2l & Hcmp2 & Had180)).
  split.
  { exists field16, v14, v15, v16, v17.
    split.
    { exact (Hfrm (fr + 176 + 20) (le2 (Z_to_bv 64 field16)) ltac:(lia)
               ltac:(rewrite length_le2; lia) Hu16). }
    split; [exact (Hblk (phi + 14) [Z_to_bv 8 v14] ltac:(lia) ltac:(cbn [length]; lia) Hb14)|].
    split; [exact (Hblk (phi + 15) [Z_to_bv 8 v15] ltac:(lia) ltac:(cbn [length]; lia) Hb15)|].
    split; [exact (Hblk (phi + 16) [Z_to_bv 8 v16] ltac:(lia) ltac:(cbn [length]; lia) Hb16)|].
    split; [exact (Hblk (phi + 17) [Z_to_bv 8 v17] ltac:(lia) ltac:(cbn [length]; lia) Hb17)|].
    split; [exact Hr14|]. split; [exact Hr15|]. split; [exact Hr16|]. split; [exact Hr17|].
    split; [exact (Hsh (phi + 14) ltac:(lia) Hs14)|].
    split; [exact (Hsh (phi + 15) ltac:(lia) Hs15)|].
    split; [exact (Hsh (phi + 16) ltac:(lia) Hs16)|].
    split; [exact (Hsh (phi + 17) ltac:(lia) Hs17)|].
    split; [exact Hf16 | exact Hzz]. }
  split.
  { exists (firstn 6 ls), (firstn 6 rs).
    split; [exact (Hq 72 (fr + 186) ltac:(lia) Hq72)|].
    split.
    { exact (Hfrm (fr + 186) (firstn 6 ls) ltac:(lia) ltac:(rewrite length_firstn; lia)
               (f7_bytes_firstn mem (fr + 186) ls 6 Hls)). }
    split; [rewrite length_firstn; lia|].
    split.
    { exact (Hblk phi (firstn 6 rs) ltac:(lia) ltac:(rewrite length_firstn; lia)
               (f7_bytes_firstn mem phi rs 6 Hrs)). }
    split; [rewrite length_firstn; lia|].
    split; [rewrite f7_memcmp_firstn; exact Hcmp|].
    apply (f7_addr_keep W mem mem' (fr + 186) 6 Had186 MU).
    intros i Hi. exact (proj2 (Ofr (fr + 186 + i) ltac:(lia))). }
  exists (firstn 6 ls2), (firstn 6 rs2).
  split; [exact (Hq 64 (fr + 180) ltac:(lia) Hq64)|].
  split.
  { exact (Hfrm (fr + 180) (firstn 6 ls2) ltac:(lia) ltac:(rewrite length_firstn; lia)
             (f7_bytes_firstn mem (fr + 180) ls2 6 Hls2)). }
  split; [rewrite length_firstn; lia|].
  split.
  { exact (Hblk (phi + 6) (firstn 6 rs2) ltac:(lia) ltac:(rewrite length_firstn; lia)
             (f7_bytes_firstn mem (phi + 6) rs2 6 Hrs2)). }
  split; [rewrite length_firstn; lia|].
  split; [rewrite f7_memcmp_firstn; exact Hcmp2|].
  apply (f7_addr_keep W mem mem' (fr + 180) 6 Had180 MU).
  intros i Hi. exact (proj2 (Ofr (fr + 180 + i) ltac:(lia))).
Qed.

Section S.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

(* The callee contract (plan-asan section 4 KN), a Section Hypothesis as the brief prescribes. *)
Hypothesis HKN : reac_ctrl_kind_name_contract.

(* a_laws_store, taken apart once in this file (a Theorem Labs lane's rule for generated laws until N+1): the law is split by
   decompose and each fact is found by its type, not by its position, so a conjunct appended to the law is one
   more unused hypothesis here. It returns the three facts seg_F7 uses (owned bytes, stklo, stkhi). *)
Lemma f7_store_law : forall H mem mem' md,
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ AC.a_store_ok H (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) a ->
     mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a) ->
  (forall a, AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem' md a <->
     AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem md a) /\
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
  AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem md.
Proof.
  intros H mem mem' md HAH Hmc Hw.
  pose proof (AC.a_laws_store _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) H mem mem' md HAH Hmc Hw)
    as L.
  decompose [and] L.
  split; [assumption|]. split; assumption.
Qed.

(* FRA across the KN callee window write, WITHOUT a mem_inv premise: it is Tac_b5.sl_callee_keep with the dead
   mem_inv slot dropped (the b5 cut carries ro_agree, not mem_inv, and the repaired helpers transport FSREC
   instead). The body is sl_callee_keep's, verbatim. *)
Lemma f7_callee_keep : forall g fr hb regs regs' mem mem' md md' K,
  FRA B APIf ra g fr hb regs mem md ->
  Frame.munch [(AC.aspZ regs - K, AC.aspZ regs)] mem mem' -> Frame.wmono rsegs mem mem' ->
  stk rsegs mem' (AC.aspZ regs - K) (AC.aspZ regs) ->
  0 <= K <= FN_STACK ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
  getr regs' 26 = getr regs 26 ->
  AsanLift.mat_le md md' ->
  FRA B APIf ra g fr hb regs' mem' md'.
Proof.
  intros g fr hb regs regs' mem mem' md md' K HFRA MU WM Hstk HK E2 E3 E4 E8 E9 E19 E26 Hmat.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  pose proof (fra_win B APIf ra g fr hb regs mem md HFRA) as (Hwlo & _).
  pose proof (fra_frame B APIf ra g fr hb regs mem md HFRA) as (Hapart & _ & _ & _).
  pose proof (fra_app B APIf ra g fr hb regs mem md HFRA) as (Hgt & _).
  destruct (sl_ah_stk B APIf ra g fr hb regs mem mem' md K HFRA HK MU WM) as (HAH' & Hstkeq).
  pose proof (sl_win_stk B APIf ra g fr hb regs mem md mem' K HFRA HK MU WM Hstk) as Hwin'.
  pose proof HFRA as HF.
  destruct HF as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    _ & _ & _ & _ & _ & _ & _ & Hwin & _).
  pose proof (AC.a_laws_stack_high _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) _ _ _ HAH) as Hhi.
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  unfold AC.GT in Hgt.
  assert (Hlo : HIGHMEM_BEG <= AC.aspZ regs - K) by lia.
  assert (Hout : forall x, x < AC.aspZ regs - K \/ AC.aspZ regs <= x ->
                   Frame.outside [(AC.aspZ regs - K, AC.aspZ regs)] x).
  { intros x Hx. cbn [Frame.outside]. split; [lia | exact I]. }
  assert (HA9 : forall A', getr regs 9 = Z_to_bv 64 A' -> 0 <= A' < 2 ^ 64 -> A' = A).
  { intros A' HA' HA'r. pose proof (rg_eq64 regs 9 A' A HA' Hr9) as Hm.
    assert (HA64 : 0 <= A < 2 ^ 64).
    { unfold stk in Hwin. destruct Hwin as (Hw0 & Hw1 & _). lia. }
    rewrite !Z.mod_small in Hm by lia. exact Hm. }
  apply (sl_fra_move B APIf ra g fr hb regs' regs' mem' md md');
    [| reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | exact Hmat].
  apply (sl_stk_run B APIf ra empty FF g fr hb regs regs' mem mem' md [(AC.aspZ regs - K, AC.aspZ regs)] HFRA MU WM).
  - apply (sl_ro_keep _ mem mem' Hro MU). intros x Hx. apply Hout. left.
    unfold LOWMEM_END, HIGHMEM_BEG in *. lia.
  - cbn [all_app]. split; [|exact I]. intros a Ha. unfold app_mem. right.
    unfold HIGHMEM_BEG, APPMEM_END in *. lia.
  - unfold rt_disjoint. cbn [disjoint_from].
    unfold RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF, RT_TSDI, RT_TSDK, RT_PGSZ,
      RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG, RT_AGLOB, RT_AGLOB_LEN.
    unfold HIGHMEM_BEG in Hlo.
    repeat split; left; lia.
  - exact HAH'.
  - exact Hstkeq.
  - intros x Hx. apply Hout. destruct (Hapart K HK) as [Hd|Hd]; lia.
  - intros x Hx. apply Hout. left. lia.
  - intros A' HA' HA'r x Hx. apply Hout. right. rewrite (HA9 A' HA' HA'r) in Hx. lia.
  - intros x Hx. apply Hout. right. lia.
  - intros x Hx. apply Hout. left. unfold Sfr, shadow_addr, ASAN_K in Hx.
    pose proof (Z.div_mod fr 8 ltac:(lia)). pose proof (Z.mod_pos_bound fr 8 ltac:(lia)).
    unfold APPMEM_END, HIGHMEM_BEG in *. lia.
  - intros A' HA' HA'r x Hx. apply Hout. right. rewrite (HA9 A' HA' HA'r) in Hx. lia.
  - exact Hwin'.
  - intros Hrec. eapply fsrec_stklo; [exact Hrec | exact HAH | exact MU |].
    intros x Hx _. apply Hout. left. lia.
  - exact E2.
  - exact E3.
  - exact E4.
  - exact E8.
  - exact E9.
  - exact E19.
  - exact E26.
Qed.


(* The run 0x81f64 -> 0x81f7c over explicit registers: the two compares not taken, the record loads, and the KN
   call composed with its contract (window [sp-16, sp)). *)
Lemma f7_evt :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8v s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A kp v lo : Z),
    s1v = Z_to_bv 64 A -> a0 = Z_to_bv 64 v -> s8v = Z_to_bv 64 v -> 0 <= v < 2 ^ 31 ->
    bytes_at rsegs m (A + 248) (le8 (Z_to_bv 64 kp)) ->
    bytes_at rsegs m kp (le4 (Z_to_bv 64 v)) ->
    bytes_at rsegs m KIND_NAME kind_name_bytes -> kind_name_strings m ->
    stk rsegs m lo (bv_unsigned sp) -> lo + REAC_CTRL_KIND_NAME_FRAME <= bv_unsigned sp ->
    KIND_NAME + 112 <= bv_unsigned sp - REAC_CTRL_KIND_NAME_FRAME ->
    asan_cells m -> shadow_rw m -> addressable m KIND_NAME 112 ->
    (forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
       outside [(bv_unsigned sp - REAC_CTRL_KIND_NAME_FRAME, bv_unsigned sp)] x) ->
    LE.evt rsegs
      (fun ms' => exists (a1' a2' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x81f7c) sp gp tp t0 t1 t2 s0 s1v (Z_to_bv 64 (kind_name_addr v))
                       a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8v s9 s10 s11 t3 t4 t5 t6)
                  Fr (Z_to_bv 64 0x81f7c) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - REAC_CTRL_KIND_NAME_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\ (mem_inv rsegs m -> mem_inv rsegs m') /\ stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8v s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x81f64) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8v s9 s10 s11 t3 t4 t5 t6
    Fr fc m A kp v lo -> -> -> Hv H248 Hkp HKB HKS HST Hlo Hkn HAC HSW HAD Hout.
  assert (HL248 : ov_read_bytes rsegs m (wa (A + 248)) 8 = Some (le8 (Z_to_bv 64 kp))).
  { pose proof (bytes_at_ov_read rsegs m (A + 248) (le8 (Z_to_bv 64 kp)) 0 8 H248 ltac:(rewrite length_le8; lia)) as HH.
    cbn [Z.of_nat] in HH. rewrite Z.add_0_r, skipn_O in HH.
    rewrite firstn_all2 in HH by (rewrite length_le8; lia). exact HH. }
  assert (HLkp : ov_read_bytes rsegs m (wa kp) 4 = Some (le4 (Z_to_bv 64 v))).
  { pose proof (bytes_at_ov_read rsegs m kp (le4 (Z_to_bv 64 v)) 0 4 Hkp ltac:(rewrite length_le4; lia)) as HH.
    cbn [Z.of_nat] in HH. rewrite Z.add_0_r, skipn_O in HH.
    rewrite firstn_all2 in HH by (rewrite length_le4; lia). exact HH. }
  (* 0x81f64 bne a0,s8 : a0 = s8, not taken *)
  step. rewrite bv_eqb_refl. cbn [negb]. cbv iota.
  (* 0x81f68 ld a0,248(s1) ; 0x81f6c lw a0,0(a0) *)
  step. step. rewrite (sx32_small v Hv).
  (* 0x81f70 bne s8,a0 : equal, not taken *)
  step. rewrite bv_eqb_refl. cbn [negb]. cbv iota.
  (* 0x81f74 mv a0,s8 ; 0x81f78 jal reac_ctrl_kind_name *)
  step. step.
  pose proof HKN as HK. unfold reac_ctrl_kind_name_contract, REAC_CTRL_KIND_NAME in HK.
  eapply evt_cut.
  { eapply HK with (lo := lo).
    - exact HKB.
    - exact HKS.
    - exact HST.
    - exact Hlo.
    - exact Hkn.
    - exact HAC.
    - exact HSW.
    - exact HAD.
    - exact Hout. }
  intros ms' (a1' & a2' & m' & E & MU & WM & MI & ST' & _).
  subst ms'.
  replace (ret_pc (Z_to_bv 64 0x81f7c)) with (Z_to_bv 64 0x81f7c)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  rewrite (unsigned_lit v) by lia.
  apply evt_done.
  exists a1', a2', m'.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI | exact ST'].
Qed.

Lemma seg_F7 : forall j, Hat B APIf ra (Inv_A81f7c_at B APIf ra) j ->
  Hat B APIf ra (Inv_A81f64_at B APIf ra) j.
Proof.
  intros j Hexit g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT &
    Hgn & Hj & HHB & HFLSI & HLK & HbC & HbK & Ha0 & HIDj & HF17 & HW240 & HPF).
  destruct HbC as (Hs7 & Hs2 & (A & H9 & HAb & HSP & Hq232) & HPH & HFR & HFS & HbKN & HFGj & HFSj).
  destruct HSP as (Hq248 & Hq256 & Hq144 & Hq184 & Hq192 & Hqs80 & Hqs88 & Hqs96 & Hq272 & Hq264).
  destruct HbKN as (HKNB & HKNA).
  destruct HbK as (Hr20 & Hr22 & Hs8 & Hr25 & Hsp280 & Hu32 & Hrargs).
  subst c. rewrite SEGS.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  pose proof (fra_app B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs mem md HFRA) as (HGT & Happfr).
  pose proof (fra_win B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs mem md HFRA) as (Hwlo & Hwstk).
  pose proof (fra_frame B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs mem md HFRA)
    as (Hapart & _ & _ & _).
  pose proof HFRA as HFRA2.
  destruct HFRA2 as (A2 & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hshf & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem md HAH)
    as Hstkhi.
  assert (HKs : AF.SLOT_STACK = 1048576) by (vm_compute; reflexivity).
  assert (HKa : APPMEM_END = 140737488355328) by (vm_compute; reflexivity).
  assert (HKf : REAC_CTRL_KIND_NAME_FRAME = 16) by reflexivity.
  assert (HKn : FN_STACK = 1044480) by reflexivity.
  assert (Hwb : 0 <= g_S g - AF.SLOT_STACK /\ g_S g - AF.SLOT_STACK <= g_S g)
    by (unfold stk in Hwin; destruct Hwin as (Hw0 & Hw1 & _); lia).
  assert (Hsphi : HIGHMEM_BEG + AF.SLOT_STACK - 4096 < sp) by lia.
  assert (Hspb : 0 <= sp < 2 ^ 64) by (unfold HIGHMEM_BEG in *; lia).
  assert (HA2b : 0 <= A2 < 2 ^ 64) by lia.
  assert (HaspB : AC.aspZ regs <= APPMEM_END) by (rewrite Haspz; lia).
  (* the b5 carry's spill base is FRA's A (sp <= A on both frame arms) *)
  assert (EA : A = A2).
  { assert (E : Z_to_bv 64 A = Z_to_bv 64 A2) by (unfold rg in H9, Hr9; rewrite <- H9; exact Hr9).
    apply (f_equal (bv_unsigned (n:=64))) in E. rewrite !MState.unsigned_lit in E by lia. exact E. }
  subst A2.
  assert (HA416' : A + 416 < 2 ^ 64) by lia.
  (* the kind is the parse kind, in [0, 13] (RcParse.ctrlparse_kind_range) *)
  assert (Hv : 0 <= t_k (g_in g) j < 2 ^ 31).
  { pose proof (RcParse.ctrlparse_kind_range (t_len (g_in g) j) (t_g (g_in g) j)) as Hk.
    unfold t_k. lia. }
  (* the KN premises over the entry memory: the callee window [sp-16, sp) of fra_win's window *)
  assert (HST0 : stk rsegs mem (AC.aspZ regs - REAC_CTRL_KIND_NAME_FRAME) (AC.aspZ regs)).
  { destruct (stk_split rsegs mem (AC.aspZ regs - FN_STACK) (AC.aspZ regs - REAC_CTRL_KIND_NAME_FRAME)
                (AC.aspZ regs) Hwstk ltac:(lia)) as (_ & H). exact H. }
  assert (Hlo0 : AC.aspZ regs - REAC_CTRL_KIND_NAME_FRAME + REAC_CTRL_KIND_NAME_FRAME <= AC.aspZ regs)
    by lia.
  assert (Hkn0 : KIND_NAME + 112 <= AC.aspZ regs - REAC_CTRL_KIND_NAME_FRAME)
    by (rewrite Haspz; unfold KIND_NAME, HIGHMEM_BEG in *; lia).
  assert (Hout0 : forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x ->
            Frame.outside [(AC.aspZ regs - REAC_CTRL_KIND_NAME_FRAME, AC.aspZ regs)] x).
  { intros x Hx. cbn [Frame.outside]. split; [|exact I]. intros [HH1 HH2]. rewrite Haspz in *.
    unfold GOT_CELL_K, CELL_K, in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in *. lia. }
  set (W := [(AC.aspZ regs - REAC_CTRL_KIND_NAME_FRAME, AC.aspZ regs)]).
  apply (sl_run_lib regs (Z_to_bv 64 0x81f64) mem md
    (fun R0 pc' mem' =>
       pc' = Z_to_bv 64 0x81f7c /\
       getr R0 2 = getr regs 2 /\ getr R0 3 = getr regs 3 /\ getr R0 4 = getr regs 4 /\
       getr R0 8 = getr regs 8 /\ getr R0 9 = getr regs 9 /\ getr R0 18 = getr regs 18 /\
       getr R0 19 = getr regs 19 /\ getr R0 20 = getr regs 20 /\ getr R0 21 = getr regs 21 /\
       getr R0 22 = getr regs 22 /\ getr R0 23 = getr regs 23 /\ getr R0 24 = getr regs 24 /\
       getr R0 25 = getr regs 25 /\ getr R0 26 = getr regs 26 /\
       getr R0 10 = Z_to_bv 64 (kind_name_addr (t_k (g_in g) j)) /\
       munch W mem mem' /\ wmono rsegs mem mem' /\
       stk rsegs mem' (AC.aspZ regs - REAC_CTRL_KIND_NAME_FRAME) (AC.aspZ regs))
    (Post B APIf ra g)).
  - exact Hhalt.
  - eapply LE.evt_mono.
    { unfold Regs6ss.mkR_of.
      eapply f7_evt with (A := A) (kp := fr + 176) (v := t_k (g_in g) j)
        (lo := AC.aspZ regs - REAC_CTRL_KIND_NAME_FRAME).
      - unfold rg in H9; exact H9.
      - unfold rg in Ha0; exact Ha0.
      - unfold rg in Hs8; exact Hs8.
      - exact Hv.
      - unfold q64 in Hq248; exact Hq248.
      - unfold u32 in Hu32; exact Hu32.
      - exact HKNB.
      - exact (f7_kn_strings_ro mem Hro).
      - exact HST0.
      - exact Hlo0.
      - exact Hkn0.
      - exact (AsanRTInv.RT_cells sp mem md HRT).
      - exact (AsanRTInv.RT_shadow_rw sp mem md HRT).
      - exact HKNA.
      - exact Hout0. }
    { intros ms' (a1' & a2' & m' & E & MU & WM & MIimp & ST').
      eexists _, (Z_to_bv 64 0x81f7c), m'. split; [exact E|].
      split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. exact ST'. }
  - intros R0 pc' mem' regs' md' (Hpc & Er2 & Er3 & Er4 & Er8 & Er9 & Er18 & Er19 & Er20 & Er21 & Er22 &
      Er23 & Er24 & Er25 & Er26 & Er10 & MU & WM & ST') Hreg Hmat.
    subst pc'.
    assert (Fr2 : getr regs' 2 = getr regs 2) by (rewrite Hreg; exact Er2).
    assert (Fr3 : getr regs' 3 = getr regs 3) by (rewrite Hreg; exact Er3).
    assert (Fr4 : getr regs' 4 = getr regs 4) by (rewrite Hreg; exact Er4).
    assert (Fr8 : getr regs' 8 = getr regs 8) by (rewrite Hreg; exact Er8).
    assert (Fr9 : getr regs' 9 = getr regs 9) by (rewrite Hreg; exact Er9).
    assert (Fr18 : getr regs' 18 = getr regs 18) by (rewrite Hreg; exact Er18).
    assert (Fr19 : getr regs' 19 = getr regs 19) by (rewrite Hreg; exact Er19).
    assert (Fr20 : getr regs' 20 = getr regs 20) by (rewrite Hreg; exact Er20).
    assert (Fr21 : getr regs' 21 = getr regs 21) by (rewrite Hreg; exact Er21).
    assert (Fr22 : getr regs' 22 = getr regs 22) by (rewrite Hreg; exact Er22).
    assert (Fr23 : getr regs' 23 = getr regs 23) by (rewrite Hreg; exact Er23).
    assert (Fr24 : getr regs' 24 = getr regs 24) by (rewrite Hreg; exact Er24).
    assert (Fr25 : getr regs' 25 = getr regs 25) by (rewrite Hreg; exact Er25).
    assert (Fr26 : getr regs' 26 = getr regs 26) by (rewrite Hreg; exact Er26).
    assert (Fr10 : getr regs' 10 = Z_to_bv 64 (kind_name_addr (t_k (g_in g) j)))
      by (rewrite Hreg; exact Er10).
    assert (HaspEq : AC.aspZ regs' = AC.aspZ regs) by (unfold AC.aspZ; rewrite Fr2; reflexivity).
    (* the window W = [sp-16, sp): below sp, above the image, apart from the frame and the spill area *)
    assert (HWout : forall x, x < sp - REAC_CTRL_KIND_NAME_FRAME \/ sp <= x -> Frame.outside W x).
    { intros x Hx. subst W. cbn [Frame.outside]. split; [|exact I]. intros [HH1 HH2].
      rewrite Haspz in *. lia. }
    assert (HWfr : forall x, fr <= x < fr + FRAME_BYTES -> Frame.outside W x).
    { intros x Hx. apply HWout.
      destruct (Hapart REAC_CTRL_KIND_NAME_FRAME ltac:(lia)) as [Hd|Hd]; rewrite Haspz in Hd; lia. }
    assert (HWhiA : forall x, A <= x -> Frame.outside W x) by (intros x Hx; apply HWout; right; lia).
    assert (Hallapp : all_app W).
    { subst W. cbn [all_app]. split; [|exact I]. intros a Ha. unfold app_mem. right.
      rewrite Haspz in *. unfold HIGHMEM_BEG, APPMEM_END in *. lia. }
    assert (Htpb : 0 <= AC.as_tp AC.ASYMS /\ AC.as_tp AC.ASYMS + 16 <= 6283264)
      by (unfold AC.as_tp, AC.ASYMS; cbn; lia).
    assert (Htp : forall k, 0 <= k < 8 ->
              mbyte rsegs mem' (AC.as_tp AC.ASYMS + k) = mbyte rsegs mem (AC.as_tp AC.ASYMS + k)).
    { intros k Hk.
      assert (Hm : mem' (Z_to_bv 64 (AC.as_tp AC.ASYMS + k)) = mem (Z_to_bv 64 (AC.as_tp AC.ASYMS + k))).
      { apply MU. rewrite MState.unsigned_lit by lia. apply HWout. left. unfold HIGHMEM_BEG in *. lia. }
      unfold mbyte. rewrite Hm. reflexivity. }
    assert (Htp8 : forall k, 0 <= k < 8 ->
              mbyte rsegs mem' (AC.as_tp AC.ASYMS + 8 + k) = mbyte rsegs mem (AC.as_tp AC.ASYMS + 8 + k)).
    { intros k Hk.
      assert (Hm : mem' (Z_to_bv 64 (AC.as_tp AC.ASYMS + 8 + k)) = mem (Z_to_bv 64 (AC.as_tp AC.ASYMS + 8 + k))).
      { apply MU. rewrite MState.unsigned_lit by lia. apply HWout. left. unfold HIGHMEM_BEG in *. lia. }
      unfold mbyte. rewrite Hm. reflexivity. }
    assert (HstoreC : forall a, 0 <= a < 2 ^ 64 ->
      ~ AC.a_store_ok (hb1 phi (AC.a_size (flen g j)) ++ g_H g)
          (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) a ->
      mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
    { intros a Ha Hns. apply MU. rewrite MState.unsigned_lit by lia. subst W.
      cbn [Frame.outside]. split; [|exact I]. intros [HH1 HH2]. apply Hns.
      unfold AC.a_store_ok. right; left. rewrite Haspz in *. lia. }
    assert (HwmL : forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a)
      by (intros a Ha Hw; exact (WM (Z_to_bv 64 a) Hw)).
    destruct (f7_store_law (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem mem' md HAH HstoreC HwmL)
      as (Hown & HSTKeq & HSTKhi).
    (* FRA across the callee's window write and the lazy-page materialization: no mem_inv needed *)
    assert (HFRA'' : FRA B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs' mem' md').
    { apply (f7_callee_keep g fr (hb1 phi (AC.a_size (flen g j))) regs regs' mem mem' md md'
               REAC_CTRL_KIND_NAME_FRAME HFRA MU WM ST');
        [ lia | exact Fr2 | exact Fr3 | exact Fr4 | exact Fr8 | exact Fr9 | exact Fr19
        | exact Fr26 | exact Hmat ]. }
    (* ENT: the window [sp-16, sp) lies in the entry-anchored slot window [S - SLOT_STACK, S) *)
    assert (HENT'' : ENT APIf g (hb1 phi (AC.a_size (flen g j))) mem' md').
    { eapply ent_mat; [| exact Hmat].
      eapply ent_store with (W := W); [exact HENT | exact HFRA | exact MU | | exact HSTKeq | exact HSTKhi |].
      - intros x Hx.
        destruct (Z_lt_le_dec x (AC.aspZ regs - REAC_CTRL_KIND_NAME_FRAME)) as [H1|H1];
          [| destruct (Z_lt_le_dec x (AC.aspZ regs)) as [H2|H2]].
        + left. subst W. cbn [Frame.outside]. split; [|exact I]. intros [HH1 HH2]. lia.
        + right. left. rewrite Haspz in *. lia.
        + left. apply HWout. right. rewrite Haspz in H2. lia.
      - intros a _ Ho. exact (proj2 (Hown a) Ho). }
    (* the transports of the carried body across W *)
    assert (Hq : forall off val, 0 <= off -> q64 mem (A + off) val -> q64 mem' (A + off) val).
    { intros off val Hoff Hqv. unfold q64 in *. eapply fl_bytes; [exact Hqv | exact MU |].
      rewrite length_le8. intros x Hx. apply HWhiA. lia. }
    assert (Hsk : forall off val, 0 <= off <= 416 -> spill regs mem off val -> spill regs' mem' off val).
    { intros off val Hoff Hs. exists A. split; [unfold rg in *; rewrite Fr9; exact H9|].
      apply Hq; [lia|]. exact (f7_spill_base regs mem A off val H9 ltac:(lia) HA416' Hoff Hs). }
    assert (Hglen : length (t_g (g_in g) j) = 50%nat) by (unfold t_g; apply fr50_length).
    (* the harness block and the record block are live blocks, below stklo <= sp - FN_STACK; their shadow
       bytes, and the frame's, are below HIGHMEM_BEG < sp - 16 *)
    pose proof HFLSI as HFLSI0.
    destruct HFLSI0 as (((Hf40 & Hf120 & Hf136 & Hf160 & Hf168 & Hf176 & Hf208 & Hf248p & HfAd &
                          Hinb & Hinblk & Hp184 & Hp256 & Hp264 & Hp272 & Hp32) &
                         Hf128 & HfStk & Hf144 & HfAd17) &
                        Hf216 & Hf224 & Hf248 & (HIN1 & HINa & HINb) &
                        (Hc256 & Hc184 & Hc192 & Hc80 & Hc88 & Hc96 & Hc272 & Hc264 & HcAd72 & HcAd38 &
                         Hc72 & Hc64 & Hc56 & Hc48)).
    assert (HKl : LOWMEM_END = 2147450880) by (vm_compute; reflexivity).
    assert (HphiB : 0 <= phi /\ phi + AC.a_size (flen g j) <= APPMEM_END)
      by (destruct HHB as (_ & (Hp0 & _ & Hpn & _)); lia).
    assert (Hinout : forall x, g_p g <= x < g_p g + g_n g -> outside W x).
    { intros x Hx.
      destruct (AC.a_laws_blocks _ _ _ _ _ LAWS (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem md
                  (g_p g) (g_n g) HAH (in_or_app _ _ _ (or_intror (HIN1 ltac:(lia))))) as (_ & _ & Hpst & _).
      apply HWout. left. lia. }
    destruct (AC.a_laws_blocks _ _ _ _ _ LAWS (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem md
                phi (AC.a_size (flen g j)) HAH ltac:(apply in_or_app; left; left; reflexivity))
      as (_ & _ & Hphistk & _ & _).
    assert (Hblkout : forall x, phi <= x < phi + AC.a_size (flen g j) ->
              outside W x /\ outside W (shadow_addr x)).
    { intros x Hx. split; [apply HWout; left; lia|].
      pose proof (f7_sh_hi x ltac:(lia)) as Hs. apply HWout. left. lia. }
    assert (Hfrout : forall x, fr <= x < fr + FRAME_BYTES -> outside W x /\ outside W (shadow_addr x)).
    { intros x Hx. split; [apply HWfr; lia|].
      pose proof (Happfr x Hx) as Hap. unfold app_mem in Hap.
      pose proof (f7_sh_hi x ltac:(lia)) as Hs. apply HWout. left. lia. }
    assert (HIexit : Inv_A81f7c_at B APIf ra g j
               (mkCfg (mkst regs' (Z_to_bv 64 0x81f7c) mem' (seg_rom rsegs)) md')).
    { exists phi, regs', mem', md', fr. rewrite SEGS. split; [reflexivity|].
      split; [exact HFRA''|].
      split; [exact HENT''|].
      split; [exact Hgn|].
      split; [exact Hj|].
      split.
      { destruct HHB as (Hphinz & Hphiad). split; [exact Hphinz|].
        exact (sl_addr_keep mem mem' W phi (AC.a_size (flen g j)) Hphiad MU Hallapp). }
      split.
      { split.
        { split.
          { split; [apply Hsk; [lia | exact Hf40]|].
            split; [apply Hsk; [lia | exact Hf120]|].
            split; [apply Hsk; [lia | exact Hf136]|].
            split; [apply Hsk; [lia | exact Hf160]|].
            split; [apply Hsk; [lia | exact Hf168]|].
            split; [apply Hsk; [lia | exact Hf176]|].
            split; [apply Hsk; [lia | exact Hf208]|].
            split; [apply Hsk; [lia | exact Hf248p]|].
            split; [exact (sl_addr_keep mem mem' W (fr + 2624) 6 HfAd MU Hallapp)|].
            split.
            { apply (fl_bytes W mem mem' (g_p g) (g_in g) Hinb MU).
              intros x Hx. rewrite <- g_n_len in Hx. exact (Hinout x Hx). }
            split.
            { intros Hn. destruct (Hinblk Hn) as (Hin & Had). split; [exact Hin|].
              exact (sl_addr_keep mem mem' W (g_p g) (g_n g) Had MU Hallapp). }
            (* push 14 group D: A4's four frame pointers that PRO appends; v1.9: [A + 32] = fr + 2880 *)
            split; [apply Hsk; [lia | exact Hp184]|].
            split; [apply Hsk; [lia | exact Hp256]|].
            split; [apply Hsk; [lia | exact Hp264]|].
            split; [apply Hsk; [lia | exact Hp272] | apply Hsk; [lia | exact Hp32]]. }
          split; [apply Hsk; [lia | exact Hf128]|].
          split.
          { eapply fl_stk; [exact HfStk | exact MU | exact WM |].
            intros x Hx. left. apply HWfr. lia. }
          split; [apply Hsk; [lia | exact Hf144]|].
          exact (sl_addr_keep mem mem' W (fr + 2691) 17 HfAd17 MU Hallapp). }
        split; [apply Hsk; [lia | exact Hf216]|].
        split; [apply Hsk; [lia | exact Hf224]|].
        split; [apply Hsk; [lia | exact Hf248]|].
        (* f1_IN: the harness block *)
        split.
        { split; [exact HIN1|].
          split; [exact (sl_addr_keep mem mem' W (g_p g) (g_n g) HINa MU Hallapp)|].
          apply (fl_bytes W mem mem' (g_p g) (g_in g) HINb MU).
          intros x Hx. rewrite <- g_n_len in Hx. exact (Hinout x Hx). }
        (* FLC (push 14 group E, v1.9 slots): the eight A4 / P12 frame pointers, the two buffers, the two compare
           spills and the two first.sroa.7 byte pointers *)
        split; [apply Hsk; [lia | exact Hc256]|].
        split; [apply Hsk; [lia | exact Hc184]|].
        split; [apply Hsk; [lia | exact Hc192]|].
        split; [apply Hsk; [lia | exact Hc80]|].
        split; [apply Hsk; [lia | exact Hc88]|].
        split; [apply Hsk; [lia | exact Hc96]|].
        split; [apply Hsk; [lia | exact Hc272]|].
        split; [apply Hsk; [lia | exact Hc264]|].
        split; [exact (sl_addr_keep mem mem' W (fragb fr) 72 HcAd72 MU Hallapp)|].
        split; [exact (sl_addr_keep mem mem' W (fr + 2688) 38 HcAd38 MU Hallapp)|].
        split; [apply Hsk; [lia | exact Hc72]|].
        split; [apply Hsk; [lia | exact Hc64]|].
        split; [apply Hsk; [lia | exact Hc56] | apply Hsk; [lia | exact Hc48]]. }
      split.
      { destruct HLK as (Hj' & Hs5j & HOURb). split; [exact Hj'|]. split.
        - unfold rg in *. rewrite Fr21. exact Hs5j.
        - unfold OURb in *. apply (fl_bytes W mem mem' (fr + 2624) (OUR (g_in g)) HOURb MU).
          rewrite OUR_length. intros x Hx. apply HWfr. lia. }
      split.
      { split; [unfold rg in *; rewrite Fr23; exact Hs7|].
        split; [unfold rg in *; rewrite Fr18; exact Hs2|].
        split.
        { exists A. split; [unfold rg in *; rewrite Fr9; exact H9|]. split; [exact HAb|].
          split.
          { split; [apply Hq; [lia | exact Hq248]|].
            split; [apply Hq; [lia | exact Hq256]|].
            split; [apply Hq; [lia | exact Hq144]|].
            split; [apply Hq; [lia | exact Hq184]|].
            split; [apply Hq; [lia | exact Hq192]|].
            split; [apply Hq; [lia | exact Hqs80]|].
            split; [apply Hq; [lia | exact Hqs88]|].
            split; [apply Hq; [lia | exact Hqs96]|].
            split; [apply Hq; [lia | exact Hq272] | apply Hq; [lia | exact Hq264]]. }
          (* push 13 group C: [A + 232] = the length flag *)
          apply Hq; [lia | exact Hq232]. }
        split.
        { destruct HPH as (HPHb & HPHp & HPHf).
          split.
          { intros Hlen. apply (fl_bytes W mem mem' phi (t_g (g_in g) j) (HPHb Hlen) MU).
            rewrite Hglen. intros x Hx. destruct (HPHp Hlen) as (_ & [Hp|Hp]).
            - apply HWout. left. unfold REAC_CTRL_IDENTITY_FRAGMENT_K in Hp. rewrite Haspz in Hp. lia.
            - apply HWout. right. rewrite Haspz in Hp. lia. }
          split; [intros Hlen; rewrite HaspEq; exact (HPHp Hlen)|].
          intros Hlen0 (FSb & HFSb & HFSw & HFSr). apply (HPHf Hlen0).
          exists FSb. split; [exact HFSb|]. split; [|exact HFSr].
          apply (word_mem_frame rsegs mem' mem _ _ HFSw). intros k Hk. symmetry. apply Htp. lia. }
        split.
        { destruct HFR as (HFRa1 & HFRa2 & HFRb & HFRl).
          split; [exact (sl_addr_keep mem mem' W (fragb fr) 72 HFRa1 MU Hallapp)|].
          split; [exact (sl_addr_keep mem mem' W (fr + 2688) 38 HFRa2 MU Hallapp)|].
          split; [|exact HFRl].
          apply (fl_bytes W mem mem' (fragb fr) (t_FG (g_in g) j) HFRb MU).
          rewrite HFRl. intros x Hx. apply HWfr. unfold fragb in *. lia. }
        split.
        { destruct HFS as (HFS1 & (DB & HDB & HDB0 & HDB1)).
          split.
          { intros FS HFSw HFSb HFSin. apply (HFS1 FS); [| exact HFSb | exact HFSin].
            apply (word_mem_frame rsegs mem' mem _ _ HFSw). intros k Hk. symmetry. apply Htp. lia. }
          exists DB. split; [|split; [exact HDB0 | exact HDB1]].
          apply (word_mem_frame rsegs mem mem' _ _ HDB). intros k Hk. apply Htp8. lia. }
        split.
        { split.
          { apply (fl_bytes W mem mem' KIND_NAME kind_name_bytes HKNB MU).
            rewrite kn_len. intros x Hx. apply HWout. left.
            unfold KIND_NAME, HIGHMEM_BEG in *. lia. }
          exact (sl_addr_keep mem mem' W KIND_NAME 112 HKNA MU Hallapp). }
        (* FGj: the 72 fragment bytes at fragb fr = fr + 2768, in the frame body *)
        split.
        { destruct HFR as (_ & _ & _ & HFRl). destruct HFGj as (HFGb & HFGok). split; [|exact HFGok].
          unfold FGBe in *. apply (fl_bytes W mem mem' (fr + 2768) (t_FG (g_in g) j) HFGb MU).
          rewrite HFRl. intros x Hx. apply HWfr. lia. }
        (* FSj (v1.9): the two first-fragment spills [A+104] / [A+112], the body at fr + 2880 (frame body, at
           most 23 bytes) and its 35 addressable bytes *)
        destruct HFSj as (Hs104 & Hs112 & Hfsb & Hfsa & HFI).
        split; [apply Hsk; [lia | exact Hs104]|].
        split; [apply Hsk; [lia | exact Hs112]|].
        split.
        { apply (fl_bytes W mem mem' (fr + 2880) _ Hfsb MU).
          pose proof (f7_fsb_len (g_in g) j) as Hbl. intros x Hx. apply HWfr. lia. }
        split; [exact (sl_addr_keep mem mem' W (fr + 2880) 35 Hfsa MU Hallapp)|].
        exact HFI. }
      split.
      { split; [unfold rg in *; rewrite Fr20; exact Hr20|].
        split; [unfold rg in *; rewrite Fr22; exact Hr22|].
        split; [unfold rg in *; rewrite Fr24; exact Hs8|].
        split; [unfold rg in *; rewrite Fr25; exact Hr25|].
        split.
        { destruct Hsp280 as (A' & HA' & HA'b & Hq280).
          assert (EA' : A' = A).
          { assert (E : Z_to_bv 64 A' = Z_to_bv 64 A) by (unfold rg in HA', H9; rewrite <- HA'; exact H9).
            apply (f_equal (bv_unsigned (n:=64))) in E. rewrite !MState.unsigned_lit in E by lia. exact E. }
          subst A'.
          exists A. split; [unfold rg in *; rewrite Fr9; exact H9|]. split; [exact HAb|].
          apply Hq; [lia | exact Hq280]. }
        split; [|exact Hrargs].
        unfold u32 in *. apply (fl_bytes W mem mem' _ _ Hu32 MU).
        rewrite length_le4. intros x Hx. apply HWfr. lia. }
      split; [unfold rg; exact Fr10|].
      (* IDj: the 38 identity bytes at fr + 2688, in the frame body *)
      split.
      { destruct HIDj as (HIDb & HIDok). split; [|exact HIDok].
        unfold IDBe in *. apply (fl_bytes W mem mem' (fr + 2688) (t_ID (g_in g) j) HIDb MU).
        rewrite f7_tID_len. intros x Hx. apply HWfr. lia. }
      (* push 13 group C: [A + 200], the guarded [A + 240] and the record group *)
      split.
      { destruct HF17 as (A' & H9f & HAf & Hq200).
        rewrite (f7_rg9 regs A A' H9 H9f HAb HAf) in Hq200.
        exists A. split; [unfold rg in *; rewrite Fr9; exact H9|]. split; [exact HAb|].
        apply Hq; [lia | exact Hq200]. }
      split.
      { destruct HW240 as (A' & H9w & HAw & (w240 & Hqw & Hwr & Hw1 & Hw0)).
        rewrite (f7_rg9 regs A A' H9 H9w HAb HAw) in Hqw.
        exists A. split; [unfold rg in *; rewrite Fr9; exact H9|]. split; [exact HAb|].
        exists w240. split; [apply Hq; [lia | exact Hqw]|].
        split; [exact Hwr|]. split; [exact Hw1 | exact Hw0]. }
      exact (f7_pf_keep g j phi fr A regs regs' mem mem' W HPF H9 HAb HA416' Fr9 MU
               (proj1 HphiB) (proj2 HphiB) ltac:(intros x Hx; apply HWhiA; lia) Hfrout Hblkout). }
    pose proof (Hexit g _ HIexit) as HSR. rewrite SEGS in HSR. exact HSR.
Qed.

End S.
