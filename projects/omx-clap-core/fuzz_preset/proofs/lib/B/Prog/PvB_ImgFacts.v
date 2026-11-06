(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset, image B' (asan-ubsan #102 pin d663f82d7f48, unstripped twin c90d4fa54d43),
   parse_value walk: the DISCHARGE of segment D's one marked closed image fact LITCS (PvB_D.v LITCS =
   PvB_D_CLit.v LITCS) at the instance. Proves nothing about the program (no function walked).
   rule 24: no function proved. rule 24: proves no function (kind: instance discharge).
   RELOCATED from the old-pin donor (image B f8f98a95bc52): every image value below is re-derived from this tree's B'
   record files (YF0m.v f82202ebccdf, YD2l.v 95803a8b9493, Listing_prog.v c97cc46b3e13, PAImg_prog.v 15fab93fe702).
   The instance: B := TfibB of lib/Reusable/YD2l.v, ARx := ARcfx = (ARcf rsegs TfibB /\ xs_placed_cf) at
   CfParams_preset (lib/Reusable/YG0ncf.v, lib/A/CfParamsPreset.v), PA := PI_prog_B (lib/B/PAImg_prog.v), ci :=
   CfImg_B (lib/AU/CfImgB.v), RL := prh_room_live_a8. The run ceiling rc stays a parameter. pvi_litcs states the fact
   at ARcf (its proof reads ARcf only); pvi_litcs_x states EXACTLY LITCS's type at the instance (ARcfx),
   checked by the Check at the end of file; PvB_Inst.v pvInst_D passes it as segment D's LITCS argument.
   How each part of cstr_ok (lib/A/PRH_Base.v:993-1004, blob fdb45545469b) is met, for the three .rodata words
   parse_value passes to literal ("true" .str.6, "false" .str.7, "null" .str.8; PvB_D_Call.v pvd_word_off / pvd_lit_word):
   - the bytes and the NUL: arodata_okP (the hypothesis) at each byte of [w, w + len + 1), with in_roP from a
     non-writable segment of rsegs (pvi_ro_b, vm_compute over the closed band [0x21460, 0x214a8)), the byte range
     disjoint from as_owned_static (pvi_disj_b, vm_compute) and below errno, and the rom bytes themselves by
     vm_compute of the closed boolean pvi_romb (no goal with an evar is computed);
   - the slack (the bytes after the NUL up to the granule end): they ARE owned statics (the asan redzones
     (0x21465, 0x1b), (0x21486, 0x1a), (0x214a5, 0x1b) of B' Tfib_owned_static, YF0m.v:1786), so arodata_okP says
     nothing of them; they are visible because the reader falls back to the rom (YP09.v mbyte: a byte the memory does
     not hold reads as seg_rom), and the rom holds every byte of the band (pvi_vis_b, vm_compute);
   - range_addressable / shadow_hull_vis: alx_const_cells (YCbqG.v) of the ARcf laws (as PALibB.exvi_eh_laws) on the
     B' const shadow cells Tfib_const_shadow 129-144 (YF0m.v:1205-1220);
   - 4096 <= w, the alloc_ceiling bound (YM05.alloc_ceiling_value), the 2 ^ 32 bound, YGcfStr.amem_range8 (low arm):
     arithmetic on the closed addresses.
   Numerals: 0x10000 (ADDRESS: B_prog_val (A_OBJ 2), PAImg_prog.v, re-derived by vm_compute); 70752 / 70784 / 70816
   (DERIVED: pvd_word_off, PvB_D_Call.v:39; 0x10000 + them = 0x21460 / 0x21480 / 0x214a0, the words' addresses);
   0x21460 / 0x214a8 = 0x21460 + 0x48 (ADDRESS: the band from the first word to the last word's granule end);
   0x21465 / 0x21486 / 0x214a5 (ADDRESS: the redzones' starts, YF0m.v:1786, comment only); 0x428c / 0x4290 / 0x4294
   (DERIVED: the words' granule numbers, 0x21460 / 8 etc.); 0x7fffc288-0x7fffc297 and 2 / 5 / 6 / 5 / 0xf9 (ADDRESS
   and WORD: the B' shadow of the three words, the generated cells of Tfib_const_shadow, YF0m.v:1205-1220); 129-144
   (indices of those cells in Tfib_const_shadow, which opens at YF0m.v:1075: line 1076 + index, checked by eq_refl);
   0x5de68c (ADDRESS: TFIB_ERRNO, YF0m.v:20, by reflexivity); 116 / 102 / 110 (WORD: the dispatch bytes); 8 (LENGTH:
   granule), 4096 (page), 256 (byte range). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG YP0b YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfStr YC88.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import PRH_ImgB Img0 Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PvB_Defs PvB_D_Call.
(* the instance: Required, not Imported, and cited by qualified name *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YD2l YF0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG0ncf YG0lawscf YGcallcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require CfImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require PALibB.
(* stdpp, through the LPS modules, shadows several list lemma names; the lemmas used here are Stdlib's *)
From Stdlib Require Import List.
Import ListNotations.
Local Open Scope Z_scope.

(* ---- generic helpers (no address) ---- *)
Definition pvi_disj_b (l1 l2 : list (Z * Z)) : bool :=
  forallb (fun r => forallb (fun r' => (fst r + snd r <=? fst r') || (fst r' + snd r' <=? fst r))%bool l2) l1.

Lemma pvi_disj_b_sound : forall l1 l2, pvi_disj_b l1 l2 = true ->
  forall a, Exists (in_zr a) l1 -> ~ Exists (in_zr a) l2.
Proof.
intros l1 l2 H a H1 H2. apply Exists_exists in H1 as (r & Hr & Ar). apply Exists_exists in H2 as (r' & Hr' & Ar').
unfold pvi_disj_b in H. rewrite forallb_forall in H. specialize (H r Hr). rewrite forallb_forall in H.
specialize (H r' Hr'). apply Bool.orb_true_iff in H. unfold in_zr in Ar, Ar'.
destruct H as [H|H]; apply Z.leb_le in H; clear - H Ar Ar'; lia.
Qed.

Lemma pvi_div8 : forall y q, 8 * q <= y < 8 * q + 8 -> y / 8 = q.
Proof. intros y q H. symmetry. apply Z.div_unique with (r := y - 8 * q); clear - H; lia. Qed.

Lemma pvi_mod8 : forall y q, 8 * q <= y < 8 * q + 8 -> y mod 8 = y - 8 * q.
Proof. intros y q H. symmetry. apply Z.mod_unique with (q := q); clear - H; lia. Qed.

(* a one-byte constant cell's byte, before arithmetic *)
Lemma pvi_z1 : forall (B : asyms) ly (rd : reader) a v, cell_holds B ly rd (z1 (ANum a) v) ->
  rd (a + Z.of_nat 0) = Some (le_byte v 1 0).
Proof. intros B ly rd a v H. exact (H 0%nat (Nat.lt_0_succ 0)). Qed.

(* one granule [8 g, 8 g + 8) holds [w, w + len), and its shadow byte v admits the whole range *)
Lemma pvi_ra_of : forall (rd : reader) w len g v, 8 * g <= w -> w + len <= 8 * g + 8 ->
  rd (SHADOW_OFF + g) = Some v -> v = 0 \/ (w + len - 8 * g <= v /\ v < 8) ->
  range_addressable rd SHADOW_OFF w len.
Proof.
intros rd w len g v H1 H2 Hr Hv x Hx. exists v. split.
- unfold shadow_of_addr. rewrite (pvi_div8 x g) by (clear - H1 H2 Hx; lia). exact Hr.
- unfold saddr_ok. destruct Hv as [->|[Hv1 Hv2]]; [left; reflexivity|].
  right. rewrite (pvi_mod8 x g) by (clear - H1 H2 Hx; lia). clear - H1 H2 Hx Hv1 Hv2; lia.
Qed.

Lemma pvi_hull_of : forall (rd : reader) x n lo hi, shadow_addr x / 8 * 8 = lo ->
  shadow_addr (x + n - 1) / 8 * 8 + 8 = hi -> (forall s, lo <= s < hi -> rd s <> None) -> shadow_hull_vis rd x n.
Proof. intros rd x n lo hi E1 E2 H s Hs. apply H. clear - E1 E2 Hs; lia. Qed.

(* the rom bytes at [p, p + length l) are l (a closed boolean, computed by vm_compute) *)
Fixpoint pvi_romb (segs : list Segment) (p : Z) (l : list Z) : bool :=
  match l with
  | [] => true
  | b :: t => match YK11.seg_rom segs (Z_to_bv 64 p) with
              | Some x => (bv_unsigned x =? b) && pvi_romb segs (p + 1) t
              | None => false
              end
  end.

Lemma pvi_romb_sound : forall segs l p, pvi_romb segs p l = true -> forall j, (j < length l)%nat ->
  option_map (fun b : byte => bv_unsigned b) (YK11.seg_rom segs (Z_to_bv 64 (p + Z.of_nat j))) = Some (nth j l 0).
Proof.
intros segs l. induction l as [|b t IH]; intros p H j Hj; cbn [length] in Hj; [clear - Hj; lia|].
cbn [pvi_romb] in H. destruct (YK11.seg_rom segs (Z_to_bv 64 p)) as [x|] eqn:E; [|discriminate].
apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1.
destruct j as [|j].
- cbn [nth Z.of_nat]. rewrite Z.add_0_r, E. cbn [option_map]. rewrite H1. reflexivity.
- cbn [nth]. replace (p + Z.of_nat (S j)) with (p + 1 + Z.of_nat j) by (clear - p j; lia).
  apply IH; [exact H2 | clear - Hj; lia].
Qed.

(* a byte of a non-writable segment (in_roP's first arm), as a boolean *)
Definition pvi_ro_b (segs : list Segment) (a : Z) : bool :=
  existsb (fun s => negb (seg_writable s) && (Z.of_N (seg_base s) <=? a) &&
    (a <? Z.of_N (seg_base s) + Z.of_N (seg_size s)))%bool segs.

Lemma pvi_ro_b_sound : forall segs a, pvi_ro_b segs a = true ->
  exists s, In s segs /\ seg_writable s = false /\
    Z.of_N (seg_base s) <= a < Z.of_N (seg_base s) + Z.of_N (seg_size s).
Proof.
intros segs a H. apply existsb_exists in H as (s & Hs & Hb).
apply andb_prop in Hb as [Hb H3]. apply andb_prop in Hb as [H1 H2].
apply negb_true_iff in H1. apply Z.leb_le in H2. apply Z.ltb_lt in H3.
exists s. split; [exact Hs|]. split; [exact H1|]. clear - H2 H3; lia.
Qed.

(* the rom holds the byte, as a boolean *)
Definition pvi_vis_b (segs : list Segment) (a : Z) : bool :=
  match YK11.seg_rom segs (Z_to_bv 64 a) with Some _ => true | None => false end.

(* a boolean property of every address of [lo, lo + n) *)
Definition pvi_range_b (f : Z -> bool) (lo n : Z) : bool := forallb (fun i => f (lo + Z.of_nat i)) (seq 0 (Z.to_nat n)).

Lemma pvi_range_b_sound : forall f lo n, pvi_range_b f lo n = true -> forall a, lo <= a < lo + n -> f a = true.
Proof.
intros f lo n H a Ha. unfold pvi_range_b in H. rewrite forallb_forall in H.
specialize (H (Z.to_nat (a - lo))). rewrite Z2Nat.id in H by (clear - Ha; lia). replace (lo + (a - lo)) with a in H by ring.
apply H. apply in_seq. clear - Ha; lia.
Qed.

Section i. Context {rc : YM05.RunCeil} {ci : CfImg}.
#[local] Abbreviation CP := CfParamsPreset.CfParams_preset.
#[local] Existing Instance CfImgB.CfImg_B.
#[local] Abbreviation TB := YD2l.TfibB.
#[local] Abbreviation ARI := (YG0ncf.ARcf (cp := CP) rsegs TB).
#[local] Abbreviation SEGS := (@pa_segs _ B_prog_listing PI_prog_B).
#[local] Abbreviation VAL := (@pa_val _ B_prog_listing PI_prog_B).
(* the allocator relation: ARcf with the error-buffer extents placed (YGcallcf.v ARxs) *)
#[local] Abbreviation ARIX := (fun ly S Hp (W : world SEGS) mem md =>
  YG0ncf.ARcf (cp := CP) rsegs TB ly S Hp W mem md /\ YG0ncf.xs_placed_cf ly S).

(* a rom byte is visible whatever the memory holds: the reader falls back to the rom (YP09.v mbyte) *)
Lemma pvi_vis_rom : forall H mem a, YK11.seg_rom rsegs (Z_to_bv 64 a) <> None -> aview rsegs H mem a <> None.
Proof.
intros H mem a Hr. unfold aview, mbyte.
destruct (mrestrict H mem (Z_to_bv 64 a)); [discriminate|].
destruct (YK11.seg_rom rsegs (Z_to_bv 64 a)) eqn:E; [discriminate | congruence].
Qed.

(* a C string's bytes and its nonzero characters from the rom *)
Lemma pvi_bytes : forall (W : world rsegs) mem p l,
  (forall a, p <= a < p + Z.of_nat (length l) + 1 ->
     aview rsegs (w_H W) mem a = option_map (fun b : byte => bv_unsigned b) (YK11.seg_rom rsegs (Z_to_bv 64 a))) ->
  pvi_romb rsegs p (l ++ [0]) = true -> forallb (fun x => negb (x =? 0)) l = true ->
  garr8 rsegs (mrestrict (w_H W) mem) p (l ++ [0]) /\ Forall (fun x => x <> 0) l.
Proof.
intros W mem p l HR Hb Hnz. split.
- intros j Hj. pose proof (pvi_romb_sound rsegs (l ++ [0]) p Hb j Hj) as E.
  rewrite length_app in Hj. cbn [length] in Hj.
  apply YC88.val_mem1_of_aview. rewrite HR by lia. exact E.
- apply Forall_forall. intros x Hx. rewrite forallb_forall in Hnz. specialize (Hnz x Hx).
  apply negb_true_iff, Z.eqb_neq in Hnz. exact Hnz.
Qed.

(* ---- LITCS at the instance ---- *)
Lemma pvi_litcs : forall ly S Hp W mem md c, ARI ly S Hp W mem md ->
  arodata_okP SEGS (@pa_relro_lo _ B_prog_listing PI_prog_B) (@pa_relro_hi _ B_prog_listing PI_prog_B) TB
    (aview SEGS (w_H W) mem) -> (c = 116 \/ c = 102 \/ c = 110) ->
  cstr_ok (PA := PI_prog_B) W mem (VAL (A_OBJ 2) + pvd_word_off c) (pvd_lit_word c).
Proof.
intros ly S Hp W mem md c HA HR Hc.
unfold arodata_okP in HR.
(* the band [0x21460, 0x214a8): read-only segment bytes, all held by the rom *)
assert (ROB : pvi_range_b (pvi_ro_b rsegs) 0x21460 0x48 = true) by (vm_compute; reflexivity).
assert (VIB : pvi_range_b (pvi_vis_b rsegs) 0x21460 0x48 = true) by (vm_compute; reflexivity).
assert (VR : forall a, 0x21460 <= a < 0x214a8 -> aview rsegs (w_H W) mem a <> None).
{ intros a Ha. apply pvi_vis_rom. pose proof (pvi_range_b_sound _ _ _ VIB a ltac:(clear - Ha; lia)) as V.
  revert V. unfold pvi_vis_b. destruct (YK11.seg_rom rsegs (Z_to_bv 64 a)); intros V; [discriminate | discriminate V]. }
(* a byte range of the band outside the owned statics reads as the rom (arodata_okP) *)
assert (ROMW : forall p n, pvi_disj_b [(p, n)] (as_owned_static TB) = true -> 0x21460 <= p -> p + n <= 0x214a8 ->
  forall a, p <= a < p + n ->
  aview rsegs (w_H W) mem a = option_map (fun b : byte => bv_unsigned b) (YK11.seg_rom rsegs (Z_to_bv 64 a))).
{ intros p n D H1 H2 a Ha. apply HR.
  - unfold in_roP. left. apply pvi_ro_b_sound. exact (pvi_range_b_sound _ _ _ ROB a ltac:(clear - H1 H2 Ha; lia)).
  - apply (pvi_disj_b_sound _ _ D). apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. clear - Ha; lia.
  - assert (E : as_errno TB = 0x5de68c) by reflexivity. rewrite E. clear - H2 Ha; lia. }
(* the shadow of the three words (B' YF0m.v f82202ebccdf): const cells 129..144 of Tfib_const_shadow, the shadow bytes
   0x7fffc288 .. 0x7fffc297 of the 8-byte hulls of "true" 0x21460, "false" 0x21480 and "null" 0x214a0 *)
pose proof (alx_const_cells _ _ _ PALibB.exvi_eh_laws ly S Hp W mem md HA) as HC.
assert (CELL : forall k a v, nth_error YF0m.Tfib_const_shadow k = Some (z1 (ANum a) v) ->
  aview rsegs (w_H W) mem (a + Z.of_nat 0) = Some (le_byte v 1 0)).
{ intros k a v Hk. apply (pvi_z1 TB ly). apply (proj1 (Forall_forall _ _) HC).
  change (as_const TB ly) with (YF0m.Tfib_const ly). unfold YF0m.Tfib_const.
  apply in_or_app. right. apply in_or_app. right. exact (nth_error_In _ k Hk). }
assert (R0 : aview rsegs (w_H W) mem 0x7fffc288 = Some 2) by exact (CELL 129%nat 0x7fffc288 2 eq_refl).
assert (R1 : aview rsegs (w_H W) mem 0x7fffc289 = Some 0xf9) by exact (CELL 130%nat 0x7fffc289 0xf9 eq_refl).
assert (R2 : aview rsegs (w_H W) mem 0x7fffc28a = Some 0xf9) by exact (CELL 131%nat 0x7fffc28a 0xf9 eq_refl).
assert (R3 : aview rsegs (w_H W) mem 0x7fffc28b = Some 0xf9) by exact (CELL 132%nat 0x7fffc28b 0xf9 eq_refl).
assert (R4 : aview rsegs (w_H W) mem 0x7fffc28c = Some 5) by exact (CELL 133%nat 0x7fffc28c 5 eq_refl).
assert (R5 : aview rsegs (w_H W) mem 0x7fffc28d = Some 0xf9) by exact (CELL 134%nat 0x7fffc28d 0xf9 eq_refl).
assert (R6 : aview rsegs (w_H W) mem 0x7fffc28e = Some 0xf9) by exact (CELL 135%nat 0x7fffc28e 0xf9 eq_refl).
assert (R7 : aview rsegs (w_H W) mem 0x7fffc28f = Some 0xf9) by exact (CELL 136%nat 0x7fffc28f 0xf9 eq_refl).
assert (R8 : aview rsegs (w_H W) mem 0x7fffc290 = Some 6) by exact (CELL 137%nat 0x7fffc290 6 eq_refl).
assert (R9 : aview rsegs (w_H W) mem 0x7fffc291 = Some 0xf9) by exact (CELL 138%nat 0x7fffc291 0xf9 eq_refl).
assert (R10 : aview rsegs (w_H W) mem 0x7fffc292 = Some 0xf9) by exact (CELL 139%nat 0x7fffc292 0xf9 eq_refl).
assert (R11 : aview rsegs (w_H W) mem 0x7fffc293 = Some 0xf9) by exact (CELL 140%nat 0x7fffc293 0xf9 eq_refl).
assert (R12 : aview rsegs (w_H W) mem 0x7fffc294 = Some 5) by exact (CELL 141%nat 0x7fffc294 5 eq_refl).
assert (R13 : aview rsegs (w_H W) mem 0x7fffc295 = Some 0xf9) by exact (CELL 142%nat 0x7fffc295 0xf9 eq_refl).
assert (R14 : aview rsegs (w_H W) mem 0x7fffc296 = Some 0xf9) by exact (CELL 143%nat 0x7fffc296 0xf9 eq_refl).
assert (R15 : aview rsegs (w_H W) mem 0x7fffc297 = Some 0xf9) by exact (CELL 144%nat 0x7fffc297 0xf9 eq_refl).
assert (ALL : forall s, 0x7fffc288 <= s < 0x7fffc298 -> aview rsegs (w_H W) mem s <> None).
{ intros s Hs.
  assert (E : s = 0x7fffc288 \/ s = 0x7fffc289 \/ s = 0x7fffc28a \/ s = 0x7fffc28b \/ s = 0x7fffc28c \/
    s = 0x7fffc28d \/ s = 0x7fffc28e \/ s = 0x7fffc28f \/ s = 0x7fffc290 \/ s = 0x7fffc291 \/ s = 0x7fffc292 \/
    s = 0x7fffc293 \/ s = 0x7fffc294 \/ s = 0x7fffc295 \/ s = 0x7fffc296 \/ s = 0x7fffc297) by (clear - Hs; lia).
  repeat (destruct E as [E|E]; [subst s; congruence|]). subst s. congruence. }
pose proof (YM05.alloc_ceiling_value (rc := rc)) as AC.
assert (V2 : VAL (A_OBJ 2) = 0x10000) by (vm_compute; reflexivity).
rewrite V2. unfold cstr_ok, cstr.
destruct Hc as [-> | [-> | ->]].
- change (pvd_word_off 116) with 70752. change (pvd_lit_word 116) with PjGrammar.w_true.
  assert (L : Z.of_nat (length PjGrammar.w_true) = 4) by reflexivity.
  assert (BY : garr8 rsegs (mrestrict (w_H W) mem) (0x10000 + 70752) (PjGrammar.w_true ++ [0]) /\
    Forall (fun x => x <> 0) PjGrammar.w_true).
  { apply pvi_bytes; [| vm_compute; reflexivity | vm_compute; reflexivity].
    intros a Ha. rewrite L in Ha. apply (ROMW (0x10000 + 70752) 5);
      [vm_compute; reflexivity | clear - Ha; lia | clear - Ha; lia | clear - Ha; lia]. }
  rewrite L.
  split; [exact BY|]. split; [clear - AC; lia|]. split; [clear - AC; lia|]. split; [clear - AC; lia|].
  split; [unfold YGcfStr.amem_range8, kLowMemEnd; left; clear - AC; lia|].
  split; [apply (pvi_ra_of _ _ _ 0x428c 5); [clear - AC; lia | clear - AC; lia | exact R4 | right; clear - AC; lia]|].
  split; [apply (pvi_hull_of _ _ _ 0x7fffc288 0x7fffc290);
          [vm_compute; reflexivity | vm_compute; reflexivity | intros s Hs; apply ALL; clear - Hs; lia]|].
  intros a Ha. pose proof (Z.mod_pos_bound (0x10000 + 70752 + 4) 8 ltac:(clear - AC; lia)) as HM. apply VR.
  clear - Ha HM; lia.
- change (pvd_word_off 102) with 70784. change (pvd_lit_word 102) with PjGrammar.w_false.
  assert (L : Z.of_nat (length PjGrammar.w_false) = 5) by reflexivity.
  assert (BY : garr8 rsegs (mrestrict (w_H W) mem) (0x10000 + 70784) (PjGrammar.w_false ++ [0]) /\
    Forall (fun x => x <> 0) PjGrammar.w_false).
  { apply pvi_bytes; [| vm_compute; reflexivity | vm_compute; reflexivity].
    intros a Ha. rewrite L in Ha. apply (ROMW (0x10000 + 70784) 6);
      [vm_compute; reflexivity | clear - Ha; lia | clear - Ha; lia | clear - Ha; lia]. }
  rewrite L.
  split; [exact BY|]. split; [clear - AC; lia|]. split; [clear - AC; lia|]. split; [clear - AC; lia|].
  split; [unfold YGcfStr.amem_range8, kLowMemEnd; left; clear - AC; lia|].
  split; [apply (pvi_ra_of _ _ _ 0x4290 6); [clear - AC; lia | clear - AC; lia | exact R8 | right; clear - AC; lia]|].
  split; [apply (pvi_hull_of _ _ _ 0x7fffc290 0x7fffc298);
          [vm_compute; reflexivity | vm_compute; reflexivity | intros s Hs; apply ALL; clear - Hs; lia]|].
  intros a Ha. pose proof (Z.mod_pos_bound (0x10000 + 70784 + 5) 8 ltac:(clear - AC; lia)) as HM. apply VR.
  clear - Ha HM; lia.
- change (pvd_word_off 110) with 70816. change (pvd_lit_word 110) with PjGrammar.w_null.
  assert (L : Z.of_nat (length PjGrammar.w_null) = 4) by reflexivity.
  assert (BY : garr8 rsegs (mrestrict (w_H W) mem) (0x10000 + 70816) (PjGrammar.w_null ++ [0]) /\
    Forall (fun x => x <> 0) PjGrammar.w_null).
  { apply pvi_bytes; [| vm_compute; reflexivity | vm_compute; reflexivity].
    intros a Ha. rewrite L in Ha. apply (ROMW (0x10000 + 70816) 5);
      [vm_compute; reflexivity | clear - Ha; lia | clear - Ha; lia | clear - Ha; lia]. }
  rewrite L.
  split; [exact BY|]. split; [clear - AC; lia|]. split; [clear - AC; lia|]. split; [clear - AC; lia|].
  split; [unfold YGcfStr.amem_range8, kLowMemEnd; left; clear - AC; lia|].
  split; [apply (pvi_ra_of _ _ _ 0x4294 5); [clear - AC; lia | clear - AC; lia | exact R12 | right; clear - AC; lia]|].
  split; [apply (pvi_hull_of _ _ _ 0x7fffc290 0x7fffc298);
          [vm_compute; reflexivity | vm_compute; reflexivity | intros s Hs; apply ALL; clear - Hs; lia]|].
  (* the NUL at 0x214a4 sits at offset 4 of its aligned word, whose tail ends at the band's end 0x214a8 *)
  intros a Ha. assert (HM : (0x10000 + 70816 + 4) mod 8 = 4) by reflexivity. apply VR.
  clear - Ha HM; lia.
Qed.

(* LITCS's type at the instance (ARx := ARcfx): the fact reads ARcf only *)
Lemma pvi_litcs_x : forall ly S Hp W mem md c, ARIX ly S Hp W mem md ->
  arodata_okP SEGS (@pa_relro_lo _ B_prog_listing PI_prog_B) (@pa_relro_hi _ B_prog_listing PI_prog_B) TB
    (aview SEGS (w_H W) mem) -> (c = 116 \/ c = 102 \/ c = 110) ->
  cstr_ok (PA := PI_prog_B) W mem (VAL (A_OBJ 2) + pvd_word_off c) (pvd_lit_word c).
Proof. intros ly S Hp W mem md c [HA _]. exact (pvi_litcs ly S Hp W mem md c HA). Qed.

End i.

(* ---- pvi_litcs_x's statement is LITCS's type at the instance ---- *)
Section chk. Context {fx0 : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg}.
Context {SK : YI16.sink_head}.
#[local] Existing Instance CfImgB.CfImg_B.
#[local] Existing Instance CfParamsPreset.CfParams_preset.
#[local] Abbreviation SEGS := (@pa_segs _ B_prog_listing PI_prog_B).
#[local] Abbreviation VAL := (@pa_val _ B_prog_listing PI_prog_B).
#[local] Abbreviation ARIX := (fun ly S Hp (W : world SEGS) mem md =>
  YG0ncf.ARcf (cp := CfParamsPreset.CfParams_preset) rsegs YD2l.TfibB ly S Hp W mem md /\
  YG0ncf.xs_placed_cf ly S).
(* LITCS (PvB_D.v / PvB_D_CLit.v) with B, ARx, PA replaced by the instance; that pvi_litcs_x fills the
   LITCS argument of segment D at the instance is checked where it is passed (PvB_Inst.v pvInst_D) *)
Check (pvi_litcs_x : forall ly S Hp W mem md c, ARIX ly S Hp W mem md ->
  arodata_okP SEGS (@pa_relro_lo _ B_prog_listing PI_prog_B) (@pa_relro_hi _ B_prog_listing PI_prog_B) YD2l.TfibB
    (aview SEGS (w_H W) mem) -> (c = 116 \/ c = 102 \/ c = 110) ->
  cstr_ok (PA := PI_prog_B) W mem (VAL (A_OBJ 2) + pvd_word_off c) (pvd_lit_word c)).
End chk.

Print Assumptions pvi_litcs.
Print Assumptions pvi_litcs_x.
