(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the OBJECT-TREE facts of the DUP segment (+0xa8 .. +0x1a4) of pj_set's image-B walk
   (fuzz_preset asan-ubsan, B 0x86e8c; the cuts of lib/B/Prog/pj_set_defs.v): pure lemmas over the reader's tree
   predicates (lib/A/PRH_Reader.v: pj_nodeR, pj_memsR, pj_hdrR, pj_cstrR, pj_agreeR), cited by the segment proof.
   proves no function (kind: glue lemma). No machine step, no image constant, no allocator state.
   - pjsdt_u64_uniq: an 8-byte little-endian read determines its value (the digit decomposition is transcribed from
     lib/KindBGlue.v kb_le8_digits / lib/Prog/PvGlue.v word_mem_uniq, restated over PRH_Reader.v rd_u64; no plain
     lemma is cited). It identifies the header fields the object's tree reads at m0 with the ones the segment holds.
   - pjsd_obj_app: the object gains one member (the tail's keys[n] := dup, n := n + 1 and the 56-byte copy of the
     value struct into kids[n]); pj_set_trans.v pjst_mems_app / pjst_mems_one / pjst_mems_frame / pjst_node_move.
   - pjsd_obj_keep: the object keeps its n members when only bytes outside its header, its used slots and its
     subtrees change (the refusal path's keys[n] := 0 store); pj_hdrR_frame and pjst_mems_frame. A zero capacity is
     ruled out by the block list the premise fixes, so no 0 < cap premise is needed.
   Numerals: 56 / 8 (LENGTH: the struct pj_value and a key pointer, in the slot strides); 16 / 24 / 32 / 48 (LENGTH:
   the header's field offsets); 256, 2 ^ 64 (DERIVED: the byte radix and the word range). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG YCbqGcall YCbqGcallW FCiface YGcallMx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YGcfRoomKeep YG0dcf YGcfRoomPre.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o YK06 YGcfFsVis.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YO0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_Charge PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_FnPj PRH_FnAlloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import
S1ImgB pj_set_defs pj_set_glue pj_set_trans pj_set_vis.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Open Scope Z_scope.
#[local] Existing Instance prh_img_B.

(* ---- an 8-byte little-endian read determines its value ---- *)
Lemma pjsdt_le8 : forall v, 0 <= v < 2 ^ 64 ->
  v = YO0f.le_byte v 8 0 + 256 * (YO0f.le_byte v 8 1 + 256 * (YO0f.le_byte v 8 2 + 256 * (YO0f.le_byte v 8 3 +
      256 * (YO0f.le_byte v 8 4 + 256 * (YO0f.le_byte v 8 5 + 256 * (YO0f.le_byte v 8 6 +
      256 * YO0f.le_byte v 8 7)))))).
Proof.
intros v Hv. unfold YO0f.le_byte. change (8 * Z.of_nat 8) with 64. rewrite (Z.mod_small v) by lia.
assert (HS : forall x k, Z.shiftr x (8 * Z.of_nat (S k)) = Z.shiftr (Z.shiftr x (8 * Z.of_nat k)) 8).
{ intros x k. rewrite Z.shiftr_shiftr by lia. f_equal. lia. }
rewrite !HS. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
Z.div_mod_to_equations. lia.
Qed.

Lemma pjsdt_u64_uniq : forall segs m a v v', rd_u64 segs m a v -> rd_u64 segs m a v' -> v = v'.
Proof.
intros segs m a v v' (Hr & Hv) (Hr' & Hv').
assert (E : forall k, (k < 8)%nat -> YO0f.le_byte v 8 k = YO0f.le_byte v' 8 k).
{ intros k Hk. pose proof (Hv k Hk) as B1. pose proof (Hv' k Hk) as B2.
  assert (B3 : Z_to_bv 8 (YO0f.le_byte v 8 k) = Z_to_bv 8 (YO0f.le_byte v' 8 k)) by congruence.
  apply (f_equal (@bv_unsigned 8)) in B3. rewrite !Z_to_bv_unsigned in B3.
  unfold bv_wrap, bv_modulus in B3. change (2 ^ Z.of_N 8) with 256 in B3.
  unfold YO0f.le_byte in B3 |- *. rewrite !Z.mod_mod in B3 by lia. exact B3. }
rewrite (pjsdt_le8 v Hr), (pjsdt_le8 v' Hr'). rewrite !E by lia. reflexivity.
Qed.

Section t. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Notation PA := PI_prog_B.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).

(* (1) the object gains one member: pj_set's tail writes keys[n] := dup, n := n + 1 and copies the value
       struct into kids[n]; `mbs` is the member list before, `tv` the value, `kname` the key's characters. *)
Lemma pjsd_obj_app : forall (m0 m1 : word -> option byte) (lblk lblk' : Z -> Z -> Prop)
    (o num str kids keys n cap : Z) (mbs : list (list Z * PjTree.jv)) (Di : list (Z * Z))
    (dup kdup : Z) (kname : list Z) (tv : PjTree.jv) (Dv : list (Z * Z)) (wv : Z),
  pj_nodeR SEGS m0 lblk o (PjTree.JObj mbs) ((kids, 56 * cap) :: (keys, 8 * cap) :: Di) ->
  pj_hdrR SEGS m0 o 6 num str kids keys n cap ->
  n = Z.of_nat (length mbs) -> 0 <= n -> n < cap -> cap <= 2 ^ 54 ->
  pj_nodeR SEGS m0 lblk wv tv Dv ->
  pj_cstrR SEGS m0 lblk dup kdup kname ->
  pj_hdrR SEGS m1 o 6 num str kids keys (n + 1) cap ->
  rd_u64 SEGS m1 (keys + 8 * n) dup ->
  (forall i, 0 <= i < 56 -> mbyte SEGS m1 (kids + 56 * n + i) = mbyte SEGS m0 (wv + i)) ->
  pj_rwR SEGS m1 (kids + 56 * n) ->
  pj_agreeR SEGS m0 m1 (fun x => (kids <= x < kids + 56 * n) \/ (keys <= x < keys + 8 * n) \/
                                 (exists b, In b Di /\ pj_holdsR b x) \/
                                 (exists b, In b Dv /\ pj_holdsR b x) \/ (dup <= x < dup + kdup)) ->
  pj_apartR Dv (kids + 56 * n) ->
  NoDup ((kids, 56 * cap) :: (keys, 8 * cap) :: Di ++ (dup, kdup) :: Dv) ->
  pj_apartR ((kids, 56 * cap) :: (keys, 8 * cap) :: Di ++ (dup, kdup) :: Dv) o ->
  (forall a k, In (a, k) ((kids, 56 * cap) :: (keys, 8 * cap) :: Di ++ (dup, kdup) :: Dv) -> lblk' a k) ->
  pj_nodeR SEGS m1 lblk' o (PjTree.JObj (mbs ++ [(kname, tv)]))
    ((kids, 56 * cap) :: (keys, 8 * cap) :: Di ++ (dup, kdup) :: Dv).
Proof.
intros m0 m1 lblk lblk' o num str kids keys n cap mbs Di dup kdup kname tv Dv wv
  HN Hh0 En Hn0 Hncap _ HV HC Hh1 HK HCP HRW HM HAPv HND HAPo HL.
cbn [pj_nodeR] in HN |- *.
destruct HN as (_ & _ & num' & str' & kids' & keys' & n' & cap' & Hh' & Es & En' & Hnc & Hcap' & Di' & ED & Hi).
pose proof Hh0 as (_ & _ & _ & Hs0 & Hk0 & Hy0 & _ & Hc0).
pose proof Hh' as (_ & _ & _ & Hs1 & Hk1 & Hy1 & _ & Hc1).
pose proof (pjsdt_u64_uniq SEGS m0 (o + 24) kids' kids Hk1 Hk0) as Ek. subst kids'.
pose proof (pjsdt_u64_uniq SEGS m0 (o + 32) keys' keys Hy1 Hy0) as Ey. subst keys'.
pose proof (pjsdt_u64_uniq SEGS m0 (o + 48) cap' cap Hc1 Hc0) as Ec. subst cap'.
pose proof (pjsdt_u64_uniq SEGS m0 (o + 16) str str' Hs0 Hs1) as Ex. rewrite Es in Ex. subst str.
assert (Hp : 0 < cap) by lia.
rewrite (proj2 (Z.eqb_neq cap 0)) in ED by lia. cbn [app] in ED.
apply (f_equal (@tl _)) in ED. apply (f_equal (@tl _)) in ED. cbn [tl] in ED. subst Di'.
split; [exact HND|]. split; [exact HAPo|].
exists num, 0, kids, keys, (n + 1), cap.
split; [exact Hh1|].
split; [reflexivity|].
split; [rewrite length_app; cbn [length]; lia|].
split; [lia|].
split.
{ right. split; [exact Hp|]. split.
  - apply HL. left. reflexivity.
  - apply HL. right. left. reflexivity. }
exists (Di ++ (dup, kdup) :: Dv).
split; [rewrite (proj2 (Z.eqb_neq cap 0)) by lia; reflexivity|].
apply (proj2 (pjst_mems_app SEGS m1 lblk' (pj_nodeR SEGS m1 lblk') mbs [(kname, tv)] kids keys
  (Di ++ (dup, kdup) :: Dv))).
exists Di, ((dup, kdup) :: Dv). split; [reflexivity|]. split.
- apply (pjst_mems_frame SEGS mbs m0 m1 lblk lblk' kids keys Di Hi).
  + intros x Hx. apply HM. cbv beta in Hx |- *. rewrite <- En in Hx.
    destruct Hx as [Hx|[Hx|Hx]]; [left|right; left|right; right; left]; exact Hx.
  + intros a k Hin. apply HL. right. right. apply in_or_app. left. exact Hin.
- rewrite <- En.
  apply (proj2 (pjst_mems_one SEGS m1 lblk' (pj_nodeR SEGS m1 lblk') (kids + 56 * n) (keys + 8 * n) kname tv
    ((dup, kdup) :: Dv))).
  exists dup, kdup, Dv. split; [reflexivity|]. split; [exact HK|]. split.
  + apply (pjst_cstr_fsw SEGS m0 m1 lblk lblk' dup kdup kname HC).
    * intros x Hx. apply (pjst_agree_b SEGS m0 m1 _ x HM). cbv beta. right. right. right. right. exact Hx.
    * apply HL. right. right. apply in_or_app. right. left. reflexivity.
  + apply (pjst_node_move SEGS tv m0 m1 lblk lblk' wv (kids + 56 * n) Dv HV HCP HRW HAPv).
    * intros x Hx. apply HM. cbv beta in Hx |- *. right. right. right. left. exact Hx.
    * intros a k Hin. apply HL. right. right. apply in_or_app. right. right. exact Hin.
Qed.

(* (2) the object KEEPS its n members when a byte past the last used key slot is overwritten: pj_set's
       refusal path has already stored keys[n] := 0 before it branches to the pj_free tail. *)
Lemma pjsd_obj_keep : forall (m0 m1 : word -> option byte) (lblk lblk' : Z -> Z -> Prop)
    (o num str kids keys n cap : Z) (mbs : list (list Z * PjTree.jv)) (Di : list (Z * Z)),
  pj_nodeR SEGS m0 lblk o (PjTree.JObj mbs) ((kids, 56 * cap) :: (keys, 8 * cap) :: Di) ->
  pj_hdrR SEGS m0 o 6 num str kids keys n cap ->
  n = Z.of_nat (length mbs) -> 0 <= n -> n <= cap ->
  pj_agreeR SEGS m0 m1 (fun x => (o <= x < o + 56) \/ (kids <= x < kids + 56 * n) \/
                                 (keys <= x < keys + 8 * n) \/ (exists b, In b Di /\ pj_holdsR b x)) ->
  (forall a k, In (a, k) ((kids, 56 * cap) :: (keys, 8 * cap) :: Di) -> lblk' a k) ->
  pj_nodeR SEGS m1 lblk' o (PjTree.JObj mbs) ((kids, 56 * cap) :: (keys, 8 * cap) :: Di).
Proof.
intros m0 m1 lblk lblk' o num str kids keys n cap mbs Di HN Hh0 En Hn0 Hncap HM HL.
cbn [pj_nodeR] in HN |- *.
destruct HN as (HND & HAP & num' & str' & kids' & keys' & n' & cap' & Hh' & Es & En' & Hnc & Hcap' & Di' & ED & Hi).
pose proof Hh0 as (_ & _ & _ & _ & Hk0 & Hy0 & _ & Hc0).
pose proof Hh' as (_ & _ & _ & _ & Hk1 & Hy1 & _ & Hc1).
pose proof (pjsdt_u64_uniq SEGS m0 (o + 24) kids' kids Hk1 Hk0) as Ek. subst kids'.
pose proof (pjsdt_u64_uniq SEGS m0 (o + 32) keys' keys Hy1 Hy0) as Ey. subst keys'.
pose proof (pjsdt_u64_uniq SEGS m0 (o + 48) cap' cap Hc1 Hc0) as Ec. subst cap'.
(* a zero capacity lists no slot blocks, so the premise's block list rules it out *)
assert (Hp : 0 < cap).
{ destruct (Z.eq_dec cap 0) as [E0|E0]; [|lia]. exfalso.
  destruct mbs as [|mb mbs']; [|cbn [length] in En'; lia].
  cbn [pj_memsR] in Hi. subst Di'. rewrite E0 in ED. cbn in ED. discriminate ED. }
rewrite (proj2 (Z.eqb_neq cap 0)) in ED by lia. cbn [app] in ED.
apply (f_equal (@tl _)) in ED. apply (f_equal (@tl _)) in ED. cbn [tl] in ED. subst Di'.
split; [exact HND|]. split; [exact HAP|].
exists num', str', kids, keys, n', cap.
split.
{ apply (pj_hdrR_frame SEGS m0 m1 o _ num' str' kids keys n' cap Hh').
  intros x Hx. apply HM. cbv beta in Hx |- *. left. exact Hx. }
split; [exact Es|]. split; [exact En'|]. split; [exact Hnc|].
split.
{ right. split; [exact Hp|]. split.
  - apply HL. left. reflexivity.
  - apply HL. right. left. reflexivity. }
exists Di. split; [rewrite (proj2 (Z.eqb_neq cap 0)) by lia; reflexivity|].
apply (pjst_mems_frame SEGS mbs m0 m1 lblk lblk' kids keys Di Hi).
- intros x Hx. apply HM. cbv beta in Hx |- *. rewrite <- En in Hx.
  destruct Hx as [Hx|[Hx|Hx]]; [right; left|right; right; left|right; right; right]; exact Hx.
- intros a k Hin. apply HL. right. right. exact Hin.
Qed.

End t.
