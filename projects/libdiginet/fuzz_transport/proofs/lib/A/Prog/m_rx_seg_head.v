(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8v.v:120-122
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:518-584, 622-634 [Apache-2.0 OR MIT];
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:110-141, 221-225, 227-235, 264-270 [Apache-2.0 OR MIT], for
   libreac/fuzz_identity's ASan build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_L.v, with its module paths and module names changed; 987 of its 1030 lines of code are new or changed and 1037 lines of the source are left out. *)
(* m_rx_seg_head: the head segment of the image-A walk of m_rx (statement lib/A/Prog/m_rx_cg.v, kit
   lib/A/Prog/m_rx_seg_kit.v): from the entry 0x8488c to the cut MAC (0x84abc) or to the cut EPI (0x8496c).
     0x8488c - 0x848c0  sp = sp - 144 and the 13 saves (ra, s0 .. s11 at sp + 136 .. sp + 40);
     0x848c4 - 0x848c8  n < 30 goes to 0x84968: a0 = 0 and the epilogue (the model: mrx_m_short);
     0x848cc - 0x848d8  s0 = fa; s2 = the shadow base (the GOT word A_OBJ 1, then the cell A_OBJ 93);
     0x848dc - 0x84964  the four checked 1-byte loads at fa + 12 .. fa + 15: the ethertype <> 0x885f, numbytes < 16
                        or n - 14 < numbytes goes to 0x84968 (the model: mrx_m_et / mrx_m_len);
     0x849a8 - 0x84ab8  the eleven checked 1-byte loads at fa + 18 .. fa + 28 and the three spills. *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YN3v YI04 YI00 YI08 YG0s.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YI00.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YP0m YP09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c YO0f.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportSyms DgnTransportList DgnTransportAddr DgnTransportPa DgnTransportImg DgnTransportPaLib YC4b YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportCg TransportGCg TransportGRwA TransportGRunA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
  m_lost_cg m_wake_cg m_maybe_online_cg m_tick_cg desk_named_cg check_state_data_cg m_rx_cg m_rx_seg_kit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require m_rx_epi.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module EPI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T.m_rx_epi.
Module ACells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.AsanCells.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ---- the two symbolic states of the segment ---- *)

(* Phase 1 (the entry, 0x8488c): the 144-byte frame below sp, the shadow base's GOT word (object 1) and its cell
   (object 93). Atom 32 is the shadow base; no shadow entry (no instrumented access before 0x848dc). *)
Definition hd_regions : smem := [stack_region MRX_FRAME; got_regionP; bcell_regionP 32].
Definition hd_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition ss_hd : sstate := mkSS AF_m_rx sr_atoms hd_regions None hd_facts.
Definition HD_SH : list shent := [].
Definition HD_Bx : sv := SOff 32 0.

(* Phase 2 (0x848dc, n >= 30): s0 = fa, s2 = the shadow base. The frame's fifteen loaded bytes as atoms 32 .. 46,
   and the three spill slots at sp + 16 .. sp + 40. The shadow entry is the frame's first 30 bytes. *)
Definition hd2_chunks : list YP09.chunk :=
  [YP09.mkChunk 12 (CVal 1 (SOff 32 0)); YP09.mkChunk 13 (CVal 1 (SOff 33 0));
   YP09.mkChunk 14 (CVal 1 (SOff 34 0)); YP09.mkChunk 15 (CVal 1 (SOff 35 0));
   YP09.mkChunk 18 (CVal 1 (SOff 36 0)); YP09.mkChunk 19 (CVal 1 (SOff 37 0));
   YP09.mkChunk 20 (CVal 1 (SOff 38 0)); YP09.mkChunk 21 (CVal 1 (SOff 39 0));
   YP09.mkChunk 22 (CVal 1 (SOff 40 0)); YP09.mkChunk 23 (CVal 1 (SOff 41 0));
   YP09.mkChunk 24 (CVal 1 (SOff 42 0)); YP09.mkChunk 25 (CVal 1 (SOff 43 0));
   YP09.mkChunk 26 (CVal 1 (SOff 44 0)); YP09.mkChunk 27 (CVal 1 (SOff 45 0));
   YP09.mkChunk 28 (CVal 1 (SOff 46 0))].
Definition hd2_frame : YP09.region := YP09.mkRegion (Some 8%nat) 12 29 0 0 hd2_chunks.
Definition hd2_stack : YP09.region := YP09.mkRegion (Some 2%nat) 16 40 16 40 [].
Definition hd2_regions : smem := [hd2_stack; hd2_frame].
Definition hd2_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46 - MRX_FRAME) (2 ^ 47) 4); (8%nat, mkAF 0 (2 ^ 47 - 31) 0);
           (18%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (32%nat, mkAF 0 255 0); (33%nat, mkAF 0 255 0); (34%nat, mkAF 0 255 0); (35%nat, mkAF 0 255 0);
           (36%nat, mkAF 0 255 0); (37%nat, mkAF 0 255 0); (38%nat, mkAF 0 255 0); (39%nat, mkAF 0 255 0);
           (40%nat, mkAF 0 255 0); (41%nat, mkAF 0 255 0); (42%nat, mkAF 0 255 0); (43%nat, mkAF 0 255 0);
           (44%nat, mkAF 0 255 0); (45%nat, mkAF 0 255 0); (46%nat, mkAF 0 255 0)] [] [].
Definition ss_hd2 : sstate := mkSS (AF_m_rx + 0x50) sr_atoms hd2_regions None hd2_facts.
Definition HD2_SH : list shent := [mkSHE 8 0 30].
Definition HD2_Bx : sv := SOff 18 0.

(* The frame bytes the phase-2 atoms hold, in atom order. *)
Definition hd_offs : list Z := [12; 13; 14; 15; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28].

(* ---- small helpers ---- *)

(* The model's option, destructed without an inversion on a world-carrying value. *)
Lemma hd_some_inv : forall (x y : list byte) (a b : Z), Some (x, a) = Some (y, b) -> y = x /\ b = a.
Proof. intros x y a b H. injection H as H1 H2. split; [symmetry; exact H1 | symmetry; exact H2]. Qed.

(* An 8-byte chunk of value v, read back as a word through the view. *)
Lemma hd_rdword_chunk : forall (E : env) (Hh : word -> bool) (mm : word -> option byte) (base off : Z) (e : sv) (v : Z),
  YP09.chunk_ok tfibsegs E (mrestrict Hh mm) base (YP09.mkChunk off (CVal 8 e)) ->
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  rdword (aview tfibsegs Hh mm) (base + off) = Some v.
Proof.
intros E Hh mm base off e v HC He Hv.
assert (Hb : forall j, (j < 8)%nat -> aview tfibsegs Hh mm (base + off + Z.of_nat j) = Some (YO0f.le_byte v 8 j))
  by (intros j Hj; exact (mrx_chunk_rd E Hh mm base off 8%N e v HC He ltac:(cbn; lia) j ltac:(cbn; lia))).
pose proof (Hb 0%nat ltac:(lia)) as B0. pose proof (Hb 1%nat ltac:(lia)) as B1.
pose proof (Hb 2%nat ltac:(lia)) as B2. pose proof (Hb 3%nat ltac:(lia)) as B3.
pose proof (Hb 4%nat ltac:(lia)) as B4. pose proof (Hb 5%nat ltac:(lia)) as B5.
pose proof (Hb 6%nat ltac:(lia)) as B6. pose proof (Hb 7%nat ltac:(lia)) as B7.
change (Z.of_nat 0) with 0 in B0. rewrite Z.add_0_r in B0.
change (Z.of_nat 1) with 1 in B1. change (Z.of_nat 2) with 2 in B2.
change (Z.of_nat 3) with 3 in B3. change (Z.of_nat 4) with 4 in B4.
change (Z.of_nat 5) with 5 in B5. change (Z.of_nat 6) with 6 in B6.
change (Z.of_nat 7) with 7 in B7.
unfold rdword. rewrite B0, B1, B2, B3, B4, B5, B6, B7. f_equal. exact (le_bytes8 v Hv).
Qed.

(* A byte of the view determines the byte of the memory. *)
Lemma hd_mbyte_of_aview : forall (Hh : word -> bool) (m m' : word -> option byte) a,
  aview tfibsegs Hh m' a = aview tfibsegs Hh m a ->
  YP09.mbyte tfibsegs (mrestrict Hh m') a = YP09.mbyte tfibsegs (mrestrict Hh m) a.
Proof.
intros Hh m m' a H.
change (aview tfibsegs Hh m' a)
  with (option_map (fun b : byte => bv_unsigned b) (YP09.mbyte tfibsegs (mrestrict Hh m') a)) in H.
change (aview tfibsegs Hh m a)
  with (option_map (fun b : byte => bv_unsigned b) (YP09.mbyte tfibsegs (mrestrict Hh m) a)) in H.
destruct (YP09.mbyte tfibsegs (mrestrict Hh m') a) as [b1|];
destruct (YP09.mbyte tfibsegs (mrestrict Hh m) a) as [b2|]; cbn [option_map] in H;
  try discriminate H; [|reflexivity].
injection H as H. f_equal. apply bv_eq. exact H.
Qed.

(* One byte of the frame, as the model reads it. *)
Lemma hd_fb : forall (mm : word -> option byte) (frx : TI.tframe) (c : Z),
  garr8 tfibsegs mm (TI.tf_addr frx) (map DSpec.bz (TI.tf_bytes frx)) ->
  0 <= c -> c < mlen frx ->
  val_mem tfibsegs mm (TI.tf_addr frx + c) 1 (mfb frx c) /\ 0 <= mfb frx c < 256.
Proof.
intros mm frx c Hg Hc Hl.
assert (Hlt : (Z.to_nat c < length (map DSpec.bz (TI.tf_bytes frx)))%nat)
  by (rewrite length_map; unfold mlen in Hl; lia).
exact (garr8_nthZ tfibsegs mm (TI.tf_addr frx) (map DSpec.bz (TI.tf_bytes frx)) c Hg Hc Hlt).
Qed.

(* One 1-byte chunk of the frame region. *)
Lemma hd_frame_chunk : forall (E : env) (mm : word -> option byte) (frx : TI.tframe) (c : Z) (j : nat),
  garr8 tfibsegs mm (TI.tf_addr frx) (map DSpec.bz (TI.tf_bytes frx)) ->
  0 <= c -> c < mlen frx -> ew E j = w64 (mfb frx c) ->
  YP09.chunk_ok tfibsegs E mm (TI.tf_addr frx) (YP09.mkChunk c (CVal 1 (SOff j 0))).
Proof.
intros E mm frx c j Hg Hc Hl He.
destruct (hd_fb mm frx c Hg Hc Hl) as [Hv Hr].
apply (chunk_ok_val tfibsegs E mm (TI.tf_addr frx) c 1 (SOff j 0) (mfb frx c)).
- cbn [sv_denot]. rewrite He. unfold w64. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
- change (2 ^ (8 * Z.of_N 1)) with 256. lia.
- cbn. lia.
- cbn [N.to_nat]. exact Hv.
Qed.

(* The fifteen frame bytes the phase-2 atoms hold. *)
Definition hd_vals2 (frx : TI.tframe) : list word :=
  [w64 (mfb frx 12); w64 (mfb frx 13); w64 (mfb frx 14); w64 (mfb frx 15); w64 (mfb frx 18);
   w64 (mfb frx 19); w64 (mfb frx 20); w64 (mfb frx 21); w64 (mfb frx 22); w64 (mfb frx 23);
   w64 (mfb frx 24); w64 (mfb frx 25); w64 (mfb frx 26); w64 (mfb frx 27); w64 (mfb frx 28)].

(* A frame byte is a byte: the bound of whichever mfb the goal holds. *)
Ltac hd_bb Hg :=
  match goal with
  | |- context [mfb ?f ?c] =>
      let Hb := fresh "Hbb" in
      assert (Hb : 0 <= mfb f c < 256) by (exact (proj2 (hd_fb _ f c Hg ltac:(lia) ltac:(lia))));
      lia
  end.

(* The two bytes of a big-endian 16-bit field do not overlap. *)
Lemma hd_lor8 : forall x y, 0 <= x < 256 -> 0 <= y < 256 -> Z.lor (x * 2 ^ 8) y = x * 2 ^ 8 + y.
Proof.
intros x y Hx Hy. symmetry. apply Z.add_nocarry_lor.
apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
destruct (Z_lt_le_dec i 8) as [Hl|Hl].
- replace (x * 2 ^ 8) with (Z.shiftl x 8) by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity).
  rewrite Z.shiftl_spec by lia. rewrite (Z.testbit_neg_r x (i - 8)) by lia. reflexivity.
- rewrite <- (Z.mod_small y (2 ^ 8)) by lia. rewrite Z.mod_pow2_bits_high by lia.
  apply andb_false_r.
Qed.

(* `slli x, 8; or y`: the big-endian 16-bit field the code assembles. *)
Lemma hd_den_or8 : forall (E : env) (j k : nat) (x y : Z),
  ew E j = w64 x -> ew E k = w64 y -> 0 <= x < 256 -> 0 <= y < 256 ->
  sv_denot E (SAlu ALU_OR (SAlu ALU_SLL (SOff j 0) (SLit 8)) (SOff k 0)) = Z_to_bv 64 (x * 2 ^ 8 + y).
Proof.
intros E j k x y Hj Hk Hx Hy.
cbn [sv_denot alu64 alu].
rewrite Hj, Hk. unfold w64. rewrite !unsigned_lit_small by lia. rewrite !Z.add_0_r.
apply bv_eq.
rewrite bv_or_unsigned, bv_shiftl_unsigned, bv_and_unsigned, !Z_to_bv_unsigned.
unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
rewrite (Z.mod_small x (2 ^ 64)) by lia.
rewrite (Z.mod_small y (2 ^ 64)) by lia.
rewrite (Z.mod_small 8 (2 ^ 64)) by lia.
rewrite (Z.mod_small 63 (2 ^ 64)) by lia.
change (Z.land 8 63) with 8.
rewrite Z.shiftl_mul_pow2 by lia.
rewrite (Z.mod_small (x * 2 ^ 8) (2 ^ 64)) by lia.
rewrite (Z.mod_small (x * 2 ^ 8 + y) (2 ^ 64)) by lia.
apply hd_lor8; lia.
Qed.

(* A big-endian 16-bit field of the frame, in the model's bytes. *)
Lemma hd_be16 : forall (frx : TI.tframe) (p : Z), 0 <= p -> p + 1 < mlen frx ->
  DSpec.spec_be16 (TW.zs (TI.tf_bytes frx)) p = mfb frx p * 2 ^ 8 + mfb frx (p + 1).
Proof.
intros frx p Hp Hl. unfold mfb, mlen in *.
rewrite (EPI.mrx_be16 (TI.tf_bytes frx) p Hp ltac:(lia)).
rewrite <- (EPI.mrx_byte_at (TI.tf_bytes frx) p Hp ltac:(lia)).
rewrite <- (EPI.mrx_byte_at (TI.tf_bytes frx) (p + 1) ltac:(lia) ltac:(lia)).
reflexivity.
Qed.

(* The thirteen saved slots, from the stack region's chunks at the end of the prologue. *)
Definition hd_save_chunks : list YP09.chunk :=
  [YP09.mkChunk (-104) (CVal 8 (SOff 27 0)); YP09.mkChunk (-96) (CVal 8 (SOff 26 0));
   YP09.mkChunk (-88) (CVal 8 (SOff 25 0)); YP09.mkChunk (-80) (CVal 8 (SOff 24 0));
   YP09.mkChunk (-72) (CVal 8 (SOff 23 0)); YP09.mkChunk (-64) (CVal 8 (SOff 22 0));
   YP09.mkChunk (-56) (CVal 8 (SOff 21 0)); YP09.mkChunk (-48) (CVal 8 (SOff 20 0));
   YP09.mkChunk (-40) (CVal 8 (SOff 19 0)); YP09.mkChunk (-32) (CVal 8 (SOff 18 0));
   YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0));
   YP09.mkChunk (-8) (CVal 8 (SOff 1 0))].

Ltac hd_in := cbn [In]; repeat (first [left; reflexivity | right]).

Lemma hd_saved_of : forall (E : env) (Wx : world tfibsegs) (mm : word -> option byte) (base : Z) (regsx : bvmap 5 word),
  (forall j : Z, 0 <= j < 32 -> ew E (Z.to_nat j) = YK11.getr regsx (Z_to_bv 5 j)) ->
  Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H Wx) mm) base) hd_save_chunks ->
  mrx_saved Wx mm base regsx.
Proof.
intros E Wx mm base regsx HE HF.
assert (HD : forall (jz coff : Z), 0 <= jz < 32 ->
  In (YP09.mkChunk coff (CVal 8 (SOff (Z.to_nat jz) 0))) hd_save_chunks ->
  rdword (aview tfibsegs (w_H Wx) mm) (base + coff) = Some (bv_unsigned (YK11.getr regsx (Z_to_bv 5 jz)))).
{ intros jz coff Hj Hin.
  apply (hd_rdword_chunk E (w_H Wx) mm base coff (SOff (Z.to_nat jz) 0));
  [ exact (proj1 (Forall_forall _ _) HF _ Hin)
  | cbn [sv_denot]; rewrite (HE jz Hj), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
  | apply YK11.u64_range ]. }
unfold mrx_saved, MRX_SAVES.
repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
- replace (base - MRX_FRAME + 136) with (base + (-8)) by (unfold MRX_FRAME; lia).
  exact (HD 1 (-8) ltac:(lia) ltac:(hd_in)).
- replace (base - MRX_FRAME + 128) with (base + (-16)) by (unfold MRX_FRAME; lia).
  exact (HD 8 (-16) ltac:(lia) ltac:(hd_in)).
- replace (base - MRX_FRAME + 120) with (base + (-24)) by (unfold MRX_FRAME; lia).
  exact (HD 9 (-24) ltac:(lia) ltac:(hd_in)).
- replace (base - MRX_FRAME + 112) with (base + (-32)) by (unfold MRX_FRAME; lia).
  exact (HD 18 (-32) ltac:(lia) ltac:(hd_in)).
- replace (base - MRX_FRAME + 104) with (base + (-40)) by (unfold MRX_FRAME; lia).
  exact (HD 19 (-40) ltac:(lia) ltac:(hd_in)).
- replace (base - MRX_FRAME + 96) with (base + (-48)) by (unfold MRX_FRAME; lia).
  exact (HD 20 (-48) ltac:(lia) ltac:(hd_in)).
- replace (base - MRX_FRAME + 88) with (base + (-56)) by (unfold MRX_FRAME; lia).
  exact (HD 21 (-56) ltac:(lia) ltac:(hd_in)).
- replace (base - MRX_FRAME + 80) with (base + (-64)) by (unfold MRX_FRAME; lia).
  exact (HD 22 (-64) ltac:(lia) ltac:(hd_in)).
- replace (base - MRX_FRAME + 72) with (base + (-72)) by (unfold MRX_FRAME; lia).
  exact (HD 23 (-72) ltac:(lia) ltac:(hd_in)).
- replace (base - MRX_FRAME + 64) with (base + (-80)) by (unfold MRX_FRAME; lia).
  exact (HD 24 (-80) ltac:(lia) ltac:(hd_in)).
- replace (base - MRX_FRAME + 56) with (base + (-88)) by (unfold MRX_FRAME; lia).
  exact (HD 25 (-88) ltac:(lia) ltac:(hd_in)).
- replace (base - MRX_FRAME + 48) with (base + (-96)) by (unfold MRX_FRAME; lia).
  exact (HD 26 (-96) ltac:(lia) ltac:(hd_in)).
- replace (base - MRX_FRAME + 40) with (base + (-104)) by (unfold MRX_FRAME; lia).
  exact (HD 27 (-104) ltac:(lia) ltac:(hd_in)).
Qed.

(* The value of register r in the machine state of a symbolic state HS. *)
Ltac hd_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | ?T => idtac "hd_reg: no match for" T; fail
  end.

(* The windows a run wrote, each inside the bytes Zs. *)
Ltac hd_win Hin Hx tac :=
  lazymatch type of Hin with In ?x ?l => let l' := eval vm_compute in l in change (In x l') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; tac |]);
  destruct Hin.

(* The write rights of a phase-1 run: the 144-byte frame below sp, inside the call's own window. *)
Ltac hd_awr1 UspE :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  apply awr_ok_x_cons;
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite UspE in Ha;
    left; split; [unfold awr_byte; left; lia | lia] |];
  apply awr_ok_x_cons;
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |];
  apply awr_ok_x_cons;
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |];
  apply awr_ok_x_nil.

(* The write rights of a phase-2 run: the three spill slots at sp + 16 .. sp + 40. *)
Ltac hd_awr2 UspE :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  apply awr_ok_x_cons;
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite UspE in Ha;
    left; split; [unfold awr_byte; left; lia | lia] |];
  apply awr_ok_x_cons;
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |];
  apply awr_ok_x_nil.

Section hd. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis HCELLS : transport_cells B.
Hypothesis HMRX : trans_mrx_cells B.
Hypothesis HRO : trans_ro_rd_unowned B.
Hypothesis HNE : trans_rom_no_errno B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis MTL : ameter_laws MT.
Hypothesis HGX : gx_ok tfibsegs B TG.G_HARNESS.
Hypothesis HGNE : gx_noerrno B TG.G_HARNESS.
Hypothesis HBCMP : forall fx' : YK11.FPState, @abcmp_realizes fx' rc tfibsegs B (transport_sigma TS___interceptor_trampoline_bcmp).
Hypothesis HMCPY : forall fx' : YK11.FPState, @aintrin_realizes fx' rc tfibsegs B OCpy (transport_sigma TS___asan_memcpy).
Hypothesis HML : forall fx' : YK11.FPState, @transport_m_lost_cg fx' rc B MT (transport_sigma TS_m_lost).
Hypothesis HDN : forall fx' : YK11.FPState, @transport_desk_named_cg fx' rc B MT (transport_sigma TS_desk_named).
Hypothesis HMW : forall fx' : YK11.FPState, @transport_m_wake_cg fx' rc B MT (transport_sigma TS_m_wake).
Hypothesis HMO : forall fx' : YK11.FPState, @transport_m_maybe_online_cg fx' rc B MT (transport_sigma TS_m_maybe_online).
Hypothesis HMT : forall fx' : YK11.FPState, @transport_m_tick_cg fx' rc B MT (transport_sigma TS_m_tick).
Variable sp1 : Z.
Variable regs0 : bvmap 5 word.
Variable lyc : alayout.
Variable Sc : astate.
Variable W : world tfibsegs.
Variable memc : word -> option byte.
Variable mdc : Model.
Variable fr : TI.tframe.
Variable n : Z.
Variable Bw' : list byte.
Variable r : Z.
Hypothesis HST : mrx_static B sp1 regs0 lyc Sc W memc mdc fr n.
Local Notation K := (@mrx_K fx rc B MT sp1 regs0 lyc Sc W memc mdc Bw' r).

Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

Lemma hd_vals : VAL (A_OBJ 1) = ACells.GOT_CELL_K /\ VAL (A_OBJ 93) = ACells.CELL_K /\
  BASE + AF_m_rx = transport_sigma TS_m_rx.
Proof. vm_compute. repeat split. Qed.

(* The walk's phase-1 valuation: the 32 entry registers and the shadow base. *)
Definition hd_E (regs : bvmap 5 word) : env := Eimg (PI := PI_transport) (Ereg regs [w64 SHADOW_OFF]).

(* The two image regions hold the shadow base, at any AR state (diginet_session_config_default.v scfg_img_ok). *)
Lemma hd_img_ok : forall ly S (Wx : world segs) mem md (E : env),
  @AR rc segs B ly S Wx mem md ->
  ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1)) -> ew E (A_OBJ 93) = Z_to_bv 64 (VAL (A_OBJ 93)) ->
  ew E 32 = Z_to_bv 64 SHADOW_OFF ->
  region_ok segs E (mrestrict (w_H Wx) mem) got_regionP /\
  region_ok segs E (mrestrict (w_H Wx) mem) (bcell_regionP 32).
Proof.
  intros ly S Wx mem md E HAR E1 E93 E32.
  destruct (HCELLS ly) as (I1 & I2 & _).
  destruct hd_vals as (V1 & V93 & _).
  assert (CH : forall c, In c (as_const B ly) -> cell_holds B ly (aview segs (w_H Wx) mem) c).
  { intros c Hc. destruct HAR as (Mx & _). exact (proj1 (Forall_forall _ _) (am_const _ _ _ _ Mx) c Hc). }
  assert (Kcell : rdword (aview segs (w_H Wx) mem) ACells.CELL_K = Some ACells.ASAN_K)
    by (apply (rdword_cell B ly); [unfold ACells.ASAN_K; lia | exact (CH _ I1)]).
  assert (Kgot : rdword (aview segs (w_H Wx) mem) ACells.GOT_CELL_K = Some ACells.CELL_K)
    by (apply (rdword_cell B ly); [unfold ACells.CELL_K; lia | exact (CH _ I2)]).
  assert (VB : forall nn v0, ew E nn = Z_to_bv 64 v0 -> 0 <= v0 < 2 ^ 64 -> base_val E (Some nn) = v0)
    by (intros nn v0 Hn Hv0; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hv0).
  assert (P64 : 2 ^ (8 * Z.of_N 8) = 2 ^ 64) by reflexivity.
  assert (R1 : 0 <= VAL (A_OBJ 1) < 2 ^ 47) by (rewrite V1; unfold ACells.GOT_CELL_K; lia).
  assert (R93 : 0 <= VAL (A_OBJ 93) < 2 ^ 47) by (rewrite V93; unfold ACells.CELL_K; lia).
  unfold got_regionP, bcell_regionP, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  split.
  - rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E1) by lia.
    split; [lia|]. split; [lia|].
    split; [intros o Ho; lia|]. constructor; [|constructor].
    apply (chunk_ok_val segs E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 93) 0) (VAL (A_OBJ 93)));
    [cbn [sv_denot]; rewrite E93, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | rewrite P64; lia | cbn; lia |].
    rewrite Z.add_0_r, V1, V93. exact (val_mem_of_rdword segs (w_H Wx) mem _ _ Kgot).
  - rewrite (VB (A_OBJ 93) (VAL (A_OBJ 93)) E93) by lia.
    split; [lia|]. split; [lia|].
    split; [intros o Ho; lia|]. constructor; [|constructor].
    apply (chunk_ok_val segs E _ (VAL (A_OBJ 93)) 0 8 (SOff 32 0) SHADOW_OFF);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | rewrite P64; unfold SHADOW_OFF; lia | cbn; lia |].
    rewrite Z.add_0_r, V93. exact (val_mem_of_rdword segs (w_H Wx) mem _ _ Kcell).
Qed.

(* The entry state of phase 1. *)
Lemma hd_entry : forall ly S (Wx : world segs) regs mem md,
  @AR rc segs B ly S Wx mem md ->
  (forall a, spZ regs - MRX_FRAME <= a < spZ regs -> apresent (w_H Wx) mem a) ->
  2 ^ 46 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
  st_ok_pi segs VAL (hd_E regs) ss_hd
    (restrict (w_H Wx) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + AF_m_rx)) mem (YK11.seg_rom segs))).
Proof.
  intros ly S Wx regs mem md HAR Hpres Hsp Hsp16.
  assert (E2' : ew (hd_E regs) 2 = YK11.getr regs 2) by (unfold hd_E; apply ew_Eimg_Ereg_nat; reflexivity).
  assert (Usp : bv_unsigned (ew (hd_E regs) 2) = spZ regs) by (rewrite E2'; reflexivity).
  assert (E32 : ew (hd_E regs) 32 = Z_to_bv 64 SHADOW_OFF)
    by (unfold hd_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (EOB : forall j, (j < 95)%nat -> ew (hd_E regs) (A_OBJ j) = Z_to_bv 64 (VAL (A_OBJ j)))
    by (intros j Hj; unfold hd_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  destruct (hd_img_ok ly S Wx mem md (hd_E regs) HAR (EOB 1%nat ltac:(lia)) (EOB 93%nat ltac:(lia)) E32) as [RG RC].
  destruct hd_vals as (V1 & V93 & _).
  assert (VB : forall nn v0, ew (hd_E regs) nn = Z_to_bv 64 v0 -> 0 <= v0 < 2 ^ 64 ->
    base_val (hd_E regs) (Some nn) = v0)
    by (intros nn v0 Hn Hv0; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hv0).
  rewrite restrict_mkst_fx. unfold ss_hd, hd_regions.
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [exact RG | apply Forall_cons; [exact RC | apply Forall_nil]]].
    unfold stack_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite Usp. unfold MRX_FRAME in *.
    split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply Hpres. lia.
  - apply pairwise_disjoint_of_extents.
    unfold stack_region, got_regionP, bcell_regionP, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) (EOB 1%nat ltac:(lia))) by (rewrite V1; unfold ACells.GOT_CELL_K; lia).
    rewrite (VB (A_OBJ 93) (VAL (A_OBJ 93)) (EOB 93%nat ltac:(lia))) by (rewrite V93; unfold ACells.CELL_K; lia).
    cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    rewrite V1, V93. unfold ACells.GOT_CELL_K, ACells.CELL_K, MRX_FRAME in *.
    repeat split; first [exact I | lia].
  - unfold hd_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E32, unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; first [lia | unfold SHADOW_OFF; lia].
Qed.

(* The walk's phase-2 valuation: the registers at 0x848dc and the fifteen frame bytes. *)
Definition hd_E2 (regs : bvmap 5 word) (frx : TI.tframe) : env :=
  Eimg (PI := PI_transport) (Ereg regs (hd_vals2 frx)).

(* The entry state of phase 2 (0x848dc, n >= 30), with the shadow entry of the frame's first 30 bytes. *)
Lemma hd_entry2 : forall (Wx : world segs) regs mem (frx : TI.tframe),
  (forall a, spZ regs + 16 <= a < spZ regs + 40 -> apresent (w_H Wx) mem a) ->
  2 ^ 46 - MRX_FRAME <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
  YK11.getr regs 8 = w64 (TI.tf_addr frx) -> YK11.getr regs 18 = w64 SHADOW_OFF ->
  30 <= mlen frx ->
  garr8 segs (mrestrict (w_H Wx) mem) (TI.tf_addr frx) (map DSpec.bz (TI.tf_bytes frx)) ->
  decode_rd_ok Wx mem (TI.tf_addr frx) (mlen frx) ->
  (TI.tf_addr frx + 29 <= spZ regs + 16 \/ spZ regs + 40 <= TI.tf_addr frx) ->
  st_ok_pi segs VAL (hd_E2 regs frx) ss_hd2
    (restrict (w_H Wx) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + 13944)) mem (YK11.seg_rom segs)))
  /\ sh_ok segs HD2_Bx HD2_SH (hd_E2 regs frx) (mrestrict (w_H Wx) mem).
Proof.
  intros Wx regs mem frx Hpres Hsp Hsp16 H8 H18 Hml Hg HRD Hdis.
  pose proof HRD as (_ & HRA & _ & Hmr & Hq0 & _).
  assert (FF : MRX_FRAME = 144) by reflexivity.
  assert (Hfa : 0 <= TI.tf_addr frx <= 2 ^ 47 - 31)
    by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hmr; lia).
  set (E := hd_E2 regs frx).
  assert (E2' : ew E 2 = YK11.getr regs 2) by (unfold E, hd_E2; apply ew_Eimg_Ereg_nat; reflexivity).
  assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2'; reflexivity).
  assert (E8 : ew E 8 = w64 (TI.tf_addr frx))
    by (unfold E, hd_E2; rewrite (ew_Eimg_Ereg_nat regs _ 8 (Z_to_bv 5 8) eq_refl); exact H8).
  assert (U8 : bv_unsigned (ew E 8) = TI.tf_addr frx)
    by (rewrite E8; unfold w64; apply unsigned_lit_small; lia).
  assert (E18 : ew E 18 = w64 SHADOW_OFF)
    by (unfold E, hd_E2; rewrite (ew_Eimg_Ereg_nat regs _ 18 (Z_to_bv 5 18) eq_refl); exact H18).
  assert (U18 : bv_unsigned (ew E 18) = SHADOW_OFF)
    by (rewrite E18; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (EXB : forall j, (j < 15)%nat -> ew E (32 + j) = nth j (hd_vals2 frx) (Z_to_bv 64 0))
    by (intros j Hj; unfold E, hd_E2; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
  pose proof (EXB 0%nat ltac:(lia)) as A32. pose proof (EXB 1%nat ltac:(lia)) as A33.
  pose proof (EXB 2%nat ltac:(lia)) as A34. pose proof (EXB 3%nat ltac:(lia)) as A35.
  pose proof (EXB 4%nat ltac:(lia)) as A36. pose proof (EXB 5%nat ltac:(lia)) as A37.
  pose proof (EXB 6%nat ltac:(lia)) as A38. pose proof (EXB 7%nat ltac:(lia)) as A39.
  pose proof (EXB 8%nat ltac:(lia)) as A40. pose proof (EXB 9%nat ltac:(lia)) as A41.
  pose proof (EXB 10%nat ltac:(lia)) as A42. pose proof (EXB 11%nat ltac:(lia)) as A43.
  pose proof (EXB 12%nat ltac:(lia)) as A44. pose proof (EXB 13%nat ltac:(lia)) as A45.
  pose proof (EXB 14%nat ltac:(lia)) as A46.
  cbn [Nat.add nth hd_vals2] in A32, A33, A34, A35, A36, A37, A38, A39, A40, A41, A42, A43, A44, A45, A46.
  split.
  - rewrite restrict_mkst_fx. unfold ss_hd2, hd2_regions.
    apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
    + apply regs_ok_Eimg_Ereg.
    + vm_compute. reflexivity.
    + apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      * unfold hd2_stack, region_ok.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
        intros o Ho. apply (apresent_writable segs). apply Hpres. lia.
      * unfold hd2_frame, hd2_chunks, region_ok.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite U8. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        repeat apply Forall_cons; try apply Forall_nil;
          first [ exact (hd_frame_chunk E _ frx 12 32 Hg ltac:(lia) ltac:(lia) A32)
                | exact (hd_frame_chunk E _ frx 13 33 Hg ltac:(lia) ltac:(lia) A33)
                | exact (hd_frame_chunk E _ frx 14 34 Hg ltac:(lia) ltac:(lia) A34)
                | exact (hd_frame_chunk E _ frx 15 35 Hg ltac:(lia) ltac:(lia) A35)
                | exact (hd_frame_chunk E _ frx 18 36 Hg ltac:(lia) ltac:(lia) A36)
                | exact (hd_frame_chunk E _ frx 19 37 Hg ltac:(lia) ltac:(lia) A37)
                | exact (hd_frame_chunk E _ frx 20 38 Hg ltac:(lia) ltac:(lia) A38)
                | exact (hd_frame_chunk E _ frx 21 39 Hg ltac:(lia) ltac:(lia) A39)
                | exact (hd_frame_chunk E _ frx 22 40 Hg ltac:(lia) ltac:(lia) A40)
                | exact (hd_frame_chunk E _ frx 23 41 Hg ltac:(lia) ltac:(lia) A41)
                | exact (hd_frame_chunk E _ frx 24 42 Hg ltac:(lia) ltac:(lia) A42)
                | exact (hd_frame_chunk E _ frx 25 43 Hg ltac:(lia) ltac:(lia) A43)
                | exact (hd_frame_chunk E _ frx 26 44 Hg ltac:(lia) ltac:(lia) A44)
                | exact (hd_frame_chunk E _ frx 27 45 Hg ltac:(lia) ltac:(lia) A45)
                | exact (hd_frame_chunk E _ frx 28 46 Hg ltac:(lia) ltac:(lia) A46) ].
    + apply pairwise_disjoint_of_extents.
      unfold hd2_stack, hd2_frame, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, U8.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      repeat split; first [exact I | lia].
    + unfold hd2_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
      unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite Usp, U8, U18.
      rewrite A32, A33, A34, A35, A36, A37, A38, A39, A40, A41, A42, A43, A44, A45, A46.
      unfold w64. rewrite !unsigned_lit_small by hd_bb Hg.
      change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
      repeat match goal with |- _ /\ _ => split end; try exact I;
        first [ lia | unfold SHADOW_OFF; lia | hd_bb Hg ].
  - unfold sh_ok, HD2_SH. constructor; [|constructor].
    apply (shent_ok_of_range segs (w_H Wx) mem E HD2_Bx 8 (TI.tf_addr frx) 30 (TI.tf_addr frx) 0 30).
    + apply (range_addressable_sub _ _ (TI.tf_addr frx) (mlen frx)); [exact HRA | lia | lia].
    + unfold U, HD2_Bx. cbn [sv_denot]. rewrite E18, Z.add_0_r, Z_to_bv_bv_unsigned.
      unfold w64. apply unsigned_lit_small. unfold SHADOW_OFF; lia.
    + unfold U. cbn [sv_denot]. rewrite E8, Z.add_0_r, Z_to_bv_bv_unsigned.
      unfold w64. apply unsigned_lit_small. lia.
    + lia.
    + lia.
    + intros x Hx. cbn [Z.min Z.max] in Hx.
      unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hmr. unfold SHADOW_OFF. lia.
Qed.

(* ---- the segment ---- *)

Lemma mrx_seg_head : forall Bw : list byte,
  K (MRX_PC OFF_EPI) (R_EPI Bw' r) ->
  K (MRX_PC OFF_MAC) (R_MAC fr n sp1 lyc Sc Bw' r) ->
  @mrx_K_entry fx rc B MT sp1 regs0 lyc Sc W memc mdc fr n Bw Bw' r.
Proof using All.
intros Bw HKE HKM.
unfold mrx_K_entry. intros HJ Hgarr Hrom Htw Hm.
pose proof HST as (Hsp1 & Hsp16 & Hceil & Hslo & Hshi & Hra & Hra4 & Hgp & Htp & Ha0 & Ha1 &
  Hfa0 & Hfan & Hsrc & Hoff & Hapart & Hev & HAR).
pose proof HJ as (HSTK & _ & (memS & HJi & _) & _).
rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & Hstk & _).
clear HJi memS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FS : MRX_STK = 8352) by reflexivity.
assert (FF : MRX_FRAME = 144) by reflexivity.
assert (EST : ESTACK = 4096) by reflexivity.
assert (Hsp : 2 ^ 46 <= spZ regs0 <= 2 ^ 47) by (rewrite Hsp1; lia).
pose proof (mrx_m_n timg_A fr Bw n Bw' r Hm) as Hnr.
assert (Hn64 : 0 <= n < 2 ^ 64) by (unfold mlen in Hnr; lia).
set (E0 := hd_E regs0).
assert (HEI : img_env VAL A_LIM E0) by (unfold E0, hd_E; apply Eimg_env).
assert (EE : forall nn (rg : bv 5), Z.of_nat nn = bv_unsigned rg -> ew E0 nn = YK11.getr regs0 rg)
  by (intros nn rg Hn; unfold E0, hd_E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (EZ : forall j : Z, 0 <= j < 32 -> ew E0 (Z.to_nat j) = YK11.getr regs0 (Z_to_bv 5 j)).
{ intros j Hj. apply EE. rewrite Z2Nat.id by lia. symmetry.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 5) with 32. apply Z.mod_small. lia. }
assert (E32 : ew E0 32 = Z_to_bv 64 SHADOW_OFF)
  by (unfold E0, hd_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs0 _ 0)).
assert (Usp : bv_unsigned (ew E0 2) = spZ regs0) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
pose proof (hd_entry lyc Sc W regs0 memc mdc HAR ltac:(intros a Ha; apply Hpres0; lia) Hsp
  ltac:(rewrite Hsp1; exact Hsp16)) as HS.
fold E0 in HS.
assert (SHOK : sh_ok segs HD_Bx HD_SH E0 (mrestrict (w_H W) memc)) by (unfold sh_ok, HD_SH; apply Forall_nil).
pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUNTO.
pose proof (paj_branch (fx := fx) (PI := PI_transport)) as BR.
unfold cfg_at.
destruct hd_vals as (_ & _ & VB0).
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx regs0 (Z_to_bv 64 (BASE + AF_m_rx)) memc
    (YK11.seg_rom segs)) mdc) Q) end.
(* run 1, +0x00 .. +0x3c: the frame, the 13 saves, `bltu a1, 30`. *)
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ hd_awr1 Usp. }
set (md1 := with_vm_backing (m_vm_lazy mdc) mat mdc) in *. clearbody md1. clear mat.
assert (KA1 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 - MRX_FRAME <= a < sp1) ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) memc a).
{ intros a Ha H1.
  apply (kept_of_frame _ _ (w_H W) memc (ms_mem ms) (fun x => sp1 - MRX_FRAME <= x < sp1) HFr);
    [| exact Ha | exact H1].
  intros b wlo whi x Hin Hx. cbv beta.
  hd_win Hin Hx ltac:(rewrite ?Usp in Hx; lia). }
assert (GA1 : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
clear HF HFr HG.
assert (HBR : branch_taken BC_LTU (sv_denot E0 (SOff 11 0)) (sv_denot E0 (SLit 30)) = (n <? 30)).
{ cbn [branch_taken sv_denot]. rewrite (EE 11%nat 11%bv eq_refl), Ha1. unfold w64.
  rewrite unsigned_lit_small by lia. rewrite Z.add_0_r.
  apply EPI.mrxk_ltu; lia. }
psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
1: { (* n < 30: a0 = 0 and the epilogue (SPEC_E_SHORT) *)
  rewrite HBR in Hc. apply Z.ltb_lt in Hc.
  rewrite (mrx_m_short timg_A fr Bw n ltac:(lia) ltac:(unfold mlen in *; lia)) in Hm.
  destruct (hd_some_inv _ _ _ _ Hm) as [HBwe HRe].
  (* run 2, +0xdc: `mv a0, zero`, to the epilogue *)
  paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan (AF_m_rx + 224).
  { hd_awr1 Usp. }
  set (md2 := with_vm_backing (m_vm_lazy md1) mat md1) in *. clearbody md2. clear mat.
  assert (KA2 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 - MRX_FRAME <= a < sp1) ->
    aview segs (w_H W) (ms_mem ms0) a = aview segs (w_H W) memc a).
  { intros a Ha H1. rewrite <- (KA1 a Ha H1).
    apply (kept_of_frame _ _ (w_H W) (ms_mem ms) (ms_mem ms0) (fun x => sp1 - MRX_FRAME <= x < sp1) HFr);
      [| exact Ha | exact H1].
    intros b wlo whi x Hin Hx. cbv beta.
    hd_win Hin Hx ltac:(rewrite ?Usp in Hx; lia). }
  clear HF HFr HG.
  pmkst HS.
  hd_reg HS (Z_to_bv 5 10) (Z_to_bv 64 0) R10 ltac:(reflexivity).
  hd_reg HS (Z_to_bv 5 2) (Z_to_bv 64 (sp1 - MRX_FRAME)) R2
    ltac:(cbn [sv_denot]; rewrite Usp; f_equal; lia).
  hd_reg HS (3%bv : bv 5) (YK11.getr regs0 3) R3
    ltac:(cbn [sv_denot]; rewrite (EE 3%nat 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  hd_reg HS (4%bv : bv 5) (YK11.getr regs0 4) R4
    ltac:(cbn [sv_denot]; rewrite (EE 4%nat 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  pose proof (st_ok_pi_region_nth E0 _ _ 0 _ HS eq_refl) as RG0.
  cbn [ms_mem restrict] in RG0.
  destruct RG0 as (_ & _ & _ & HCH0).
  cbn [YP09.r_base YP09.r_chunks base_val] in HCH0. rewrite Usp in HCH0.
  assert (HSV : mrx_saved W (ms_mem ms0) sp1 regs0).
  { rewrite <- Hsp1. exact (hd_saved_of E0 W (ms_mem ms0) (spZ regs0) regs0 EZ HCH0). }
  assert (TWF : tw_at TMAP_A (aview segs (w_H W) (ms_mem ms0)) Bw).
  { apply (tw_kept TMAP_A (aview segs (w_H W) memc)); [exact Htw|].
    intros x Hx. pose proof (TMAP_A_hull x Hx) as Hh.
    unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh. apply KA2; lia. }
  replace (BASE + 14088) with (MRX_PC OFF_EPI)
    by (unfold MRX_PC, OFF_EPI; rewrite <- VB0; unfold AF_m_rx; lia).
  apply (HKE W Bw).
  eapply mrx_at_intro.
  + exact HJ.
  + reflexivity.
  + apply Permutation_refl.
  + exact (mo_le_refl MT MTL Sc).
  + exact R2.
  + exact R3.
  + exact R4.
  + exact HSV.
  + exact TWF.
  + split; [symmetry; exact HBwe | rewrite HRe; exact R10]. }
(* n >= 30: the frame's header. *)
rewrite HBR in Hc. apply Z.ltb_ge in Hc. rename Hc into Hn30.
assert (Hml30 : 30 <= mlen fr) by lia.
pose proof (trans_src_ok_rd B LAWS lyc Sc W memc mdc (TI.tf_addr fr) (mlen fr) HAR Hsrc ltac:(lia)) as HRD.
pose proof HRD as (_ & _ & _ & Hmr & Hq0 & Hq63).
(* run 2, +0x40 .. +0x4c: s0 = fa, s2 = the shadow base. *)
paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan (AF_m_rx + 80).
{ hd_awr1 Usp. }
set (md2 := with_vm_backing (m_vm_lazy md1) mat md1) in *. clearbody md2. clear mat.
assert (KA2 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 - MRX_FRAME <= a < sp1) ->
  aview segs (w_H W) (ms_mem ms0) a = aview segs (w_H W) memc a).
{ intros a Ha H1. rewrite <- (KA1 a Ha H1).
  apply (kept_of_frame _ _ (w_H W) (ms_mem ms) (ms_mem ms0) (fun x => sp1 - MRX_FRAME <= x < sp1) HFr);
    [| exact Ha | exact H1].
  intros b wlo whi x Hin Hx. cbv beta.
  hd_win Hin Hx ltac:(rewrite ?Usp in Hx; lia). }
assert (GA2 : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem ms0) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG (GA1 a Ha))).
clear HF HFr HG.
(* the frame's bytes, its shadow facts and the read-only view at the run's memory *)
assert (Hfrkept : forall a, TI.tf_addr fr <= a < TI.tf_addr fr + mlen fr ->
  aview segs (w_H W) (ms_mem ms0) a = aview segs (w_H W) memc a).
{ intros a Ha. apply KA2;
  [ unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hmr; lia
  | unfold mlen in *; lia ]. }
assert (Hgarr2 : garr8 segs (mrestrict (w_H W) (ms_mem ms0)) (TI.tf_addr fr)
  (map DSpec.bz (TI.tf_bytes fr))).
{ apply (garr8_frame segs (mrestrict (w_H W) memc) _ _ _ Hgarr).
  intros a Ha. apply hd_mbyte_of_aview. apply Hfrkept. rewrite length_map in Ha. unfold mlen. lia. }
assert (HRD2 : decode_rd_ok W (ms_mem ms0) (TI.tf_addr fr) (mlen fr)).
{ apply (trans_rd_ok_view W W memc (ms_mem ms0) (TI.tf_addr fr) (mlen fr) HRD).
  - exact Hfrkept.
  - intros s Hs. apply KA2; unfold kLowMemEnd, kHighShadowEnd in Hs; lia. }
assert (Hrom2 : trans_rom_view_rd W (ms_mem ms0)).
{ intros a Ha. rewrite <- (Hrom a Ha). apply KA2; [|unfold TRANS_RLO, TRANS_RHI in *];
  revert Ha; unfold trans_in_ro_rd, TRANS_RO_RD, TRANS_RO_GLOBALS, TRANS_JT_LLVMF, TRANS_JT_NOTICE,
    TRANS_K_LLVMF, TRANS_K_POLL, TRANS_SCALE, TRANS_HOST, TRANS_DESK, TRANS_SPEC_BCAST, TRANS_SPEC_OUI,
    TRANS_STR_C24, TRANS_STR_PC, TRANS_CMD, TRANS_DESK2, TRANS_NOTDD, TRANS_OTHER, TRANS_STR4,
    TRANS_BROADCAST, TRANS_PNAME0, TRANS_PNAME1, TRANS_IO, TRANS_SPEC_C24, TRANS_SPEC_PC, TRANS_SRC,
    TRANS_DST, TRANS_NAME, TRANS_PERS;
  intros HE; repeat (apply Exists_cons in HE as [HE | HE]; [unfold in_zr in HE; cbn [fst snd] in HE; lia|]);
  apply Exists_nil in HE; destruct HE. }
(* the registers at 0x848dc *)
pmkst HS.
hd_reg HS (Z_to_bv 5 8) (w64 (TI.tf_addr fr)) R8
  ltac:(cbn [sv_denot]; rewrite (EE 10%nat (10%bv : bv 5) eq_refl), Ha0, Z.add_0_r, Z_to_bv_bv_unsigned;
        reflexivity).
hd_reg HS (Z_to_bv 5 18) (w64 SHADOW_OFF) R18
  ltac:(cbn [sv_denot]; rewrite E32, unsigned_lit_small by (unfold SHADOW_OFF; lia);
        rewrite Z.add_0_r; reflexivity).
hd_reg HS (Z_to_bv 5 2) (Z_to_bv 64 (sp1 - MRX_FRAME)) R2
  ltac:(cbn [sv_denot]; rewrite Usp; f_equal; lia).
hd_reg HS (1%bv : bv 5) (YK11.getr regs0 1) R1
  ltac:(cbn [sv_denot]; rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
hd_reg HS (3%bv : bv 5) (YK11.getr regs0 3) R3
  ltac:(cbn [sv_denot]; rewrite (EE 3%nat 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
hd_reg HS (4%bv : bv 5) (YK11.getr regs0 4) R4
  ltac:(cbn [sv_denot]; rewrite (EE 4%nat 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
assert (HspB : spZ (ms_regs ms0) = sp1 - MRX_FRAME)
  by (refine (eq_trans (f_equal bv_unsigned R2) _); apply unsigned_lit_small; lia).
(* the saved slots at the restart, kept to the end of the segment *)
pose proof (st_ok_pi_region_nth E0 _ _ 0 _ HS eq_refl) as RG0.
cbn [ms_mem restrict] in RG0.
destruct RG0 as (_ & _ & _ & HCH0).
cbn [YP09.r_base YP09.r_chunks base_val] in HCH0. rewrite Usp in HCH0.
assert (HSV0 : mrx_saved W (ms_mem ms0) sp1 regs0)
  by (rewrite <- Hsp1; exact (hd_saved_of E0 W (ms_mem ms0) (spZ regs0) regs0 EZ HCH0)).
hd_reg HS (Z_to_bv 5 11) (w64 n) R11
  ltac:(cbn [sv_denot]; rewrite (EE 11%nat (11%bv : bv 5) eq_refl), Ha1, Z.add_0_r, Z_to_bv_bv_unsigned;
        reflexivity).
clear HCH0 HS SHOK.
(* phase 2: the frame's bytes as atoms, the shadow entry of its first 30 bytes *)
destruct (hd_entry2 W (ms_regs ms0) (ms_mem ms0) fr
  ltac:(intros a Ha; apply GA2; apply Hpres0; rewrite HspB in Ha; lia)
  ltac:(rewrite HspB; lia)
  ltac:(rewrite HspB; replace (sp1 - MRX_FRAME) with (sp1 + (-9) * 16) by lia;
        rewrite Z_mod_plus_full; exact Hsp16)
  R8 R18 Hml30 Hgarr2 HRD2
  ltac:(rewrite HspB; unfold mlen in *; lia)) as [HS2 SHOK2].
set (E1 := hd_E2 (ms_regs ms0) fr) in HS2, SHOK2.
assert (HEIB : img_env VAL A_LIM E1) by (unfold E1, hd_E2; apply Eimg_env).
assert (Usp2 : bv_unsigned (ew E1 2) = sp1 - MRX_FRAME).
{ unfold E1, hd_E2. rewrite (ew_Eimg_Ereg_nat (ms_regs ms0) _ 2 (2%bv : bv 5) eq_refl). exact HspB. }
(* the frame bytes as atoms, and the world at the restart *)
assert (EE1 : forall nn (rg : bv 5), Z.of_nat nn = bv_unsigned rg -> ew E1 nn = YK11.getr (ms_regs ms0) rg)
  by (intros nn rg Hn; unfold E1, hd_E2; apply ew_Eimg_Ereg_nat; exact Hn).
assert (EXB : forall j, (j < 15)%nat -> ew E1 (32 + j) = nth j (hd_vals2 fr) (Z_to_bv 64 0))
  by (intros j Hj; unfold E1, hd_E2; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EXB 0%nat ltac:(lia)) as A32. pose proof (EXB 1%nat ltac:(lia)) as A33.
pose proof (EXB 2%nat ltac:(lia)) as A34. pose proof (EXB 3%nat ltac:(lia)) as A35.
pose proof (EXB 4%nat ltac:(lia)) as A36. pose proof (EXB 5%nat ltac:(lia)) as A37.
pose proof (EXB 6%nat ltac:(lia)) as A38. pose proof (EXB 7%nat ltac:(lia)) as A39.
pose proof (EXB 8%nat ltac:(lia)) as A40. pose proof (EXB 9%nat ltac:(lia)) as A41.
pose proof (EXB 10%nat ltac:(lia)) as A42. pose proof (EXB 11%nat ltac:(lia)) as A43.
pose proof (EXB 12%nat ltac:(lia)) as A44. pose proof (EXB 13%nat ltac:(lia)) as A45.
pose proof (EXB 14%nat ltac:(lia)) as A46.
cbn [Nat.add nth hd_vals2] in A32, A33, A34, A35, A36, A37, A38, A39, A40, A41, A42, A43, A44, A45, A46.
pose proof (proj2 (hd_fb _ fr 12 Hgarr ltac:(lia) ltac:(lia))) as Hb12.
pose proof (proj2 (hd_fb _ fr 13 Hgarr ltac:(lia) ltac:(lia))) as Hb13.
pose proof (proj2 (hd_fb _ fr 14 Hgarr ltac:(lia) ltac:(lia))) as Hb14.
pose proof (proj2 (hd_fb _ fr 15 Hgarr ltac:(lia) ltac:(lia))) as Hb15.
assert (TW0 : tw_at TMAP_A (aview segs (w_H W) (ms_mem ms0)) Bw).
{ apply (tw_kept TMAP_A (aview segs (w_H W) memc)); [exact Htw|].
  intros x Hx. pose proof (TMAP_A_hull x Hx) as Hh.
  unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh. apply KA2; lia. }
assert (HSE : DSpec.SPEC_ETHERTYPE = 34911) by reflexivity.
(* run 3: the four checked loads of the ethertype and the length *)
paj_run_to_tok RUNTO HS2 HJ SHOK2 YC4b.Bspan (AF_m_rx + 560).
{ hd_awr2 Usp2. }
assert (KC : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 - MRX_FRAME + 16 <= a < sp1 - MRX_FRAME + 40) ->
  aview segs (w_H W) (ms_mem ms1) a = aview segs (w_H W) (ms_mem ms0) a).
{ intros a Ha H1.
  apply (kept_of_frame _ _ (w_H W) (ms_mem ms0) (ms_mem ms1)
    (fun x => sp1 - MRX_FRAME + 16 <= x < sp1 - MRX_FRAME + 40) HFr); [| exact Ha | exact H1].
  intros b wlo whi x Hin Hx. cbv beta.
  hd_win Hin Hx ltac:(rewrite ?Usp2 in Hx; lia). }
clear HF HFr HG.
lazymatch type of HS2 with st_ok_pi _ _ ?EF _ _ => set (EX3 := EF) in * end.
assert (HEF3 : forall nn, (nn < 1024)%nat -> ew EX3 nn = ew E1 nn)
  by (intros nn Hn; unfold EX3; repeat rewrite ew_ewset_other by lia; reflexivity).
assert (B32 : ew EX3 32 = w64 (mfb fr 12)) by (rewrite (HEF3 32%nat ltac:(lia)); exact A32).
assert (B33 : ew EX3 33 = w64 (mfb fr 13)) by (rewrite (HEF3 33%nat ltac:(lia)); exact A33).
assert (Usp3 : bv_unsigned (ew EX3 2) = sp1 - MRX_FRAME)
  by (rewrite (HEF3 2%nat ltac:(lia)); exact Usp2).
assert (HET : branch_taken BC_NE
    (sv_denot EX3 (SAlu ALU_OR (SAlu ALU_SLL (SOff 32 0) (SLit 8)) (SOff 33 0))) (sv_denot EX3 (SLit 34911))
  = negb (DSpec.spec_be16 (TW.zs (TI.tf_bytes fr)) 12 =? 34911)).
{ rewrite (hd_den_or8 EX3 32 33 (mfb fr 12) (mfb fr 13) B32 B33 Hb12 Hb13).
  rewrite (hd_be16 fr 12 ltac:(lia) ltac:(lia)).
  cbn [branch_taken sv_denot]. rewrite EPI.mrxk_eqb by lia. reflexivity. }
psrr_branch_tok RUN BR HS2 SHOK2 YC4b.Bspan.
1: { (* the ethertype is not 0x885f: return 0 *)
  rewrite HET in Hc. apply negb_true_iff, Z.eqb_neq in Hc.
  rewrite (EPI.mrx_m_et timg_A fr Bw n ltac:(unfold mlen in *; lia) ltac:(rewrite HSE; exact Hc)) in Hm.
  destruct (hd_some_inv _ _ _ _ Hm) as [HBwe HRe].
  paj_run_to_tok RUNTO HS2 HJ SHOK2 YC4b.Bspan (AF_m_rx + 224).
  { hd_awr2 Usp3. }
  assert (KB : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 - MRX_FRAME + 16 <= a < sp1 - MRX_FRAME + 40) ->
    aview segs (w_H W) (ms_mem ms2) a = aview segs (w_H W) (ms_mem ms0) a).
  { intros a Ha H1. rewrite <- (KC a Ha H1).
    apply (kept_of_frame _ _ (w_H W) (ms_mem ms1) (ms_mem ms2)
      (fun x => sp1 - MRX_FRAME + 16 <= x < sp1 - MRX_FRAME + 40) HFr); [| exact Ha | exact H1].
    intros b wlo whi x Hin Hx. cbv beta.
    hd_win Hin Hx ltac:(rewrite ?Usp3 in Hx; lia). }
  pmkst HS2.
  hd_reg HS2 (Z_to_bv 5 10) (Z_to_bv 64 0) Q10 ltac:(reflexivity).
  hd_reg HS2 (Z_to_bv 5 2) (Z_to_bv 64 (sp1 - MRX_FRAME)) Q2
    ltac:(cbn [sv_denot]; rewrite Usp2; f_equal; lia).
  hd_reg HS2 (3%bv : bv 5) (YK11.getr regs0 3) Q3
    ltac:(cbn [sv_denot]; rewrite (EE1 3%nat (3%bv : bv 5) eq_refl), R3, Z.add_0_r, Z_to_bv_bv_unsigned;
          reflexivity).
  hd_reg HS2 (4%bv : bv 5) (YK11.getr regs0 4) Q4
    ltac:(cbn [sv_denot]; rewrite (EE1 4%nat (4%bv : bv 5) eq_refl), R4, Z.add_0_r, Z_to_bv_bv_unsigned;
          reflexivity).
  assert (HSVF : mrx_saved W (ms_mem ms2) sp1 regs0).
  { apply (mrx_saved_kept W W (ms_mem ms0) (ms_mem ms2) sp1 regs0 HSV0).
    intros a Ha. apply KB; lia. }
  assert (TWF : tw_at TMAP_A (aview segs (w_H W) (ms_mem ms2)) Bw).
  { apply (tw_kept TMAP_A (aview segs (w_H W) (ms_mem ms0))); [exact TW0|].
    intros x Hx. pose proof (TMAP_A_hull x Hx) as Hh.
    unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh. apply KB; lia. }
  replace (BASE + 14088) with (MRX_PC OFF_EPI)
    by (unfold MRX_PC, OFF_EPI; rewrite <- VB0; unfold AF_m_rx; lia).
  apply (HKE W Bw).
  eapply mrx_at_intro.
  + exact HJ.
  + reflexivity.
  + apply Permutation_refl.
  + exact (mo_le_refl MT MTL Sc).
  + exact Q2.
  + exact Q3.
  + exact Q4.
  + exact HSVF.
  + exact TWF.
  + split; [symmetry; exact HBwe | rewrite HRe; exact Q10]. }
(* the ethertype is 0x885f *)
rewrite HET in Hc. apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into HetOK.
assert (B34 : ew EX3 34 = w64 (mfb fr 14)) by (rewrite (HEF3 34%nat ltac:(lia)); exact A34).
assert (B35 : ew EX3 35 = w64 (mfb fr 15)) by (rewrite (HEF3 35%nat ltac:(lia)); exact A35).
assert (B11 : ew EX3 11 = w64 n)
  by (rewrite (EE1 11%nat (11%bv : bv 5) eq_refl); exact R11).
pose proof (EPI.mrx_be16_range (TW.zs (TI.tf_bytes fr)) 14) as RNB.
assert (DNB : sv_denot EX3 (SAlu ALU_OR (SAlu ALU_SLL (SOff 34 0) (SLit 8)) (SOff 35 0))
  = Z_to_bv 64 (DSpec.spec_be16 (TW.zs (TI.tf_bytes fr)) 14)).
{ rewrite (hd_den_or8 EX3 34 35 (mfb fr 14) (mfb fr 15) B34 B35 Hb14 Hb15).
  rewrite (hd_be16 fr 14 ltac:(lia) ltac:(lia)). reflexivity. }
assert (HSE16 : DSpec.spec_be16 (TW.zs (TI.tf_bytes fr)) 12 = DSpec.SPEC_ETHERTYPE) by (rewrite HSE; exact HetOK).
(* run 4: numbytes, `bltu s4, 16` *)
paj_run_to_tok RUNTO HS2 HJ SHOK2 YC4b.Bspan (AF_m_rx + 560).
{ hd_awr2 Usp3. }
assert (KD : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 - MRX_FRAME + 16 <= a < sp1 - MRX_FRAME + 40) ->
  aview segs (w_H W) (ms_mem ms2) a = aview segs (w_H W) (ms_mem ms0) a).
{ intros a Ha H1. rewrite <- (KC a Ha H1).
  apply (kept_of_frame _ _ (w_H W) (ms_mem ms1) (ms_mem ms2)
    (fun x => sp1 - MRX_FRAME + 16 <= x < sp1 - MRX_FRAME + 40) HFr); [| exact Ha | exact H1].
  intros b wlo whi x Hin Hx. cbv beta.
  hd_win Hin Hx ltac:(rewrite ?Usp3 in Hx; lia). }
clear HF HFr HG.
assert (HNS : branch_taken BC_LTU
    (sv_denot EX3 (SAlu ALU_OR (SAlu ALU_SLL (SOff 34 0) (SLit 8)) (SOff 35 0))) (sv_denot EX3 (SLit 16))
  = (DSpec.spec_be16 (TW.zs (TI.tf_bytes fr)) 14 <? 16)).
{ rewrite DNB. cbn [branch_taken sv_denot]. apply EPI.mrxk_ltu; lia. }
psrr_branch_tok RUN BR HS2 SHOK2 YC4b.Bspan.
1: { (* numbytes < 16: return 0 *)
  rewrite HNS in Hc. apply Z.ltb_lt in Hc.
  rewrite (EPI.mrx_m_len timg_A fr Bw n ltac:(unfold mlen in *; lia) HSE16 (or_introl Hc)) in Hm.
  destruct (hd_some_inv _ _ _ _ Hm) as [HBwe HRe].
  paj_run_to_tok RUNTO HS2 HJ SHOK2 YC4b.Bspan (AF_m_rx + 224).
  { hd_awr2 Usp3. }
  assert (KB : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 - MRX_FRAME + 16 <= a < sp1 - MRX_FRAME + 40) ->
    aview segs (w_H W) (ms_mem ms3) a = aview segs (w_H W) (ms_mem ms0) a).
  { intros a Ha H1. rewrite <- (KD a Ha H1).
    apply (kept_of_frame _ _ (w_H W) (ms_mem ms2) (ms_mem ms3)
      (fun x => sp1 - MRX_FRAME + 16 <= x < sp1 - MRX_FRAME + 40) HFr); [| exact Ha | exact H1].
    intros b wlo whi x Hin Hx. cbv beta.
    hd_win Hin Hx ltac:(rewrite ?Usp3 in Hx; lia). }
  pmkst HS2.
  hd_reg HS2 (Z_to_bv 5 10) (Z_to_bv 64 0) Q10 ltac:(reflexivity).
  hd_reg HS2 (Z_to_bv 5 2) (Z_to_bv 64 (sp1 - MRX_FRAME)) Q2
    ltac:(cbn [sv_denot]; rewrite Usp3; f_equal; lia).
  hd_reg HS2 (3%bv : bv 5) (YK11.getr regs0 3) Q3
    ltac:(cbn [sv_denot]; rewrite (EE1 3%nat (3%bv : bv 5) eq_refl), R3, Z.add_0_r, Z_to_bv_bv_unsigned;
          reflexivity).
  hd_reg HS2 (4%bv : bv 5) (YK11.getr regs0 4) Q4
    ltac:(cbn [sv_denot]; rewrite (EE1 4%nat (4%bv : bv 5) eq_refl), R4, Z.add_0_r, Z_to_bv_bv_unsigned;
          reflexivity).
  assert (HSVF : mrx_saved W (ms_mem ms3) sp1 regs0).
  { apply (mrx_saved_kept W W (ms_mem ms0) (ms_mem ms3) sp1 regs0 HSV0).
    intros a Ha. apply KB; lia. }
  assert (TWF : tw_at TMAP_A (aview segs (w_H W) (ms_mem ms3)) Bw).
  { apply (tw_kept TMAP_A (aview segs (w_H W) (ms_mem ms0))); [exact TW0|].
    intros x Hx. pose proof (TMAP_A_hull x Hx) as Hh.
    unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh. apply KB; lia. }
  replace (BASE + 14088) with (MRX_PC OFF_EPI)
    by (unfold MRX_PC, OFF_EPI; rewrite <- VB0; unfold AF_m_rx; lia).
  apply (HKE W Bw).
  eapply mrx_at_intro.
  + exact HJ.
  + reflexivity.
  + apply Permutation_refl.
  + exact (mo_le_refl MT MTL Sc).
  + exact Q2.
  + exact Q3.
  + exact Q4.
  + exact HSVF.
  + exact TWF.
  + split; [symmetry; exact HBwe | rewrite HRe; exact Q10]. }
(* numbytes >= 16 *)
rewrite HNS in Hc. apply Z.ltb_ge in Hc. rename Hc into HnbLo.
(* run 5: `addi a1, a1, -14`, `bgeu a1, s4` *)
paj_run_to_tok RUNTO HS2 HJ SHOK2 YC4b.Bspan (AF_m_rx + 560).
{ hd_awr2 Usp3. }
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 - MRX_FRAME + 16 <= a < sp1 - MRX_FRAME + 40) ->
  aview segs (w_H W) (ms_mem ms3) a = aview segs (w_H W) (ms_mem ms0) a).
{ intros a Ha H1. rewrite <- (KD a Ha H1).
  apply (kept_of_frame _ _ (w_H W) (ms_mem ms2) (ms_mem ms3)
    (fun x => sp1 - MRX_FRAME + 16 <= x < sp1 - MRX_FRAME + 40) HFr); [| exact Ha | exact H1].
  intros b wlo whi x Hin Hx. cbv beta.
  hd_win Hin Hx ltac:(rewrite ?Usp3 in Hx; lia). }
clear HF HFr HG.
assert (HNL : branch_taken BC_GEU (sv_denot EX3 (SOff 11 (-14)))
    (sv_denot EX3 (SAlu ALU_OR (SAlu ALU_SLL (SOff 34 0) (SLit 8)) (SOff 35 0)))
  = negb (n - 14 <? DSpec.spec_be16 (TW.zs (TI.tf_bytes fr)) 14)).
{ rewrite DNB. cbn [branch_taken sv_denot]. rewrite B11. unfold w64.
  rewrite unsigned_lit_small by lia. replace (n + -14) with (n - 14) by lia.
  rewrite EPI.mrxk_ltu by lia. reflexivity. }
psrr_branch_tok RUN BR HS2 SHOK2 YC4b.Bspan.
2: { (* n - 14 < numbytes: return 0 *)
  rewrite HNL in Hc. apply negb_false_iff, Z.ltb_lt in Hc.
  rewrite (EPI.mrx_m_len timg_A fr Bw n ltac:(unfold mlen in *; lia) HSE16 (or_intror Hc)) in Hm.
  destruct (hd_some_inv _ _ _ _ Hm) as [HBwe HRe].
  paj_run_to_tok RUNTO HS2 HJ SHOK2 YC4b.Bspan (AF_m_rx + 224).
  { hd_awr2 Usp3. }
  assert (KB : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 - MRX_FRAME + 16 <= a < sp1 - MRX_FRAME + 40) ->
    aview segs (w_H W) (ms_mem ms4) a = aview segs (w_H W) (ms_mem ms0) a).
  { intros a Ha H1. rewrite <- (KE a Ha H1).
    apply (kept_of_frame _ _ (w_H W) (ms_mem ms3) (ms_mem ms4)
      (fun x => sp1 - MRX_FRAME + 16 <= x < sp1 - MRX_FRAME + 40) HFr); [| exact Ha | exact H1].
    intros b wlo whi x Hin Hx. cbv beta.
    hd_win Hin Hx ltac:(rewrite ?Usp3 in Hx; lia). }
  pmkst HS2.
  hd_reg HS2 (Z_to_bv 5 10) (Z_to_bv 64 0) Q10 ltac:(reflexivity).
  hd_reg HS2 (Z_to_bv 5 2) (Z_to_bv 64 (sp1 - MRX_FRAME)) Q2
    ltac:(cbn [sv_denot]; rewrite Usp3; f_equal; lia).
  hd_reg HS2 (3%bv : bv 5) (YK11.getr regs0 3) Q3
    ltac:(cbn [sv_denot]; rewrite (EE1 3%nat (3%bv : bv 5) eq_refl), R3, Z.add_0_r, Z_to_bv_bv_unsigned;
          reflexivity).
  hd_reg HS2 (4%bv : bv 5) (YK11.getr regs0 4) Q4
    ltac:(cbn [sv_denot]; rewrite (EE1 4%nat (4%bv : bv 5) eq_refl), R4, Z.add_0_r, Z_to_bv_bv_unsigned;
          reflexivity).
  assert (HSVF : mrx_saved W (ms_mem ms4) sp1 regs0).
  { apply (mrx_saved_kept W W (ms_mem ms0) (ms_mem ms4) sp1 regs0 HSV0).
    intros a Ha. apply KB; lia. }
  assert (TWF : tw_at TMAP_A (aview segs (w_H W) (ms_mem ms4)) Bw).
  { apply (tw_kept TMAP_A (aview segs (w_H W) (ms_mem ms0))); [exact TW0|].
    intros x Hx. pose proof (TMAP_A_hull x Hx) as Hh.
    unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh. apply KB; lia. }
  replace (BASE + 14088) with (MRX_PC OFF_EPI)
    by (unfold MRX_PC, OFF_EPI; rewrite <- VB0; unfold AF_m_rx; lia).
  apply (HKE W Bw).
  eapply mrx_at_intro.
  + exact HJ.
  + reflexivity.
  + apply Permutation_refl.
  + exact (mo_le_refl MT MTL Sc).
  + exact Q2.
  + exact Q3.
  + exact Q4.
  + exact HSVF.
  + exact TWF.
  + split; [symmetry; exact HBwe | rewrite HRe; exact Q10]. }
(* numbytes <= n - 14: the header is the model's (SPEC_OK) *)
rewrite HNL in Hc. apply negb_true_iff, Z.ltb_ge in Hc. rename Hc into HnbHi.
rewrite (EPI.mrx_m_ok timg_A fr Bw n ltac:(unfold mlen in *; lia) HSE16 ltac:(lia)) in Hm.
(* run 6, +0x11c .. +0x22c: the eleven checked loads at fa + 18 .. fa + 28 and the three spills, to MAC *)
paj_run_to_tok RUNTO HS2 HJ SHOK2 YC4b.Bspan (AF_m_rx + 560).
{ hd_awr2 Usp3. }
assert (KF : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 - MRX_FRAME + 16 <= a < sp1 - MRX_FRAME + 40) ->
  aview segs (w_H W) (ms_mem ms4) a = aview segs (w_H W) (ms_mem ms0) a).
{ intros a Ha H1. rewrite <- (KE a Ha H1).
  apply (kept_of_frame _ _ (w_H W) (ms_mem ms3) (ms_mem ms4)
    (fun x => sp1 - MRX_FRAME + 16 <= x < sp1 - MRX_FRAME + 40) HFr); [| exact Ha | exact H1].
  intros b wlo whi x Hin Hx. cbv beta.
  hd_win Hin Hx ltac:(rewrite ?Usp3 in Hx; lia). }
clear HF HFr HG.
(* the frame lies outside the spill window, so its bytes and the read-only view are the restart's *)
assert (Hfrk4 : forall a, TI.tf_addr fr <= a < TI.tf_addr fr + mlen fr ->
  aview segs (w_H W) (ms_mem ms4) a = aview segs (w_H W) (ms_mem ms0) a).
{ intros a Ha. apply KF;
  [ unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hmr; lia
  | unfold mlen in *; lia ]. }
assert (Hgarr4 : garr8 segs (mrestrict (w_H W) (ms_mem ms4)) (TI.tf_addr fr)
  (map DSpec.bz (TI.tf_bytes fr))).
{ apply (garr8_frame segs (mrestrict (w_H W) (ms_mem ms0)) _ _ _ Hgarr2).
  intros a Ha. apply hd_mbyte_of_aview. apply Hfrk4. rewrite length_map in Ha. unfold mlen. lia. }
assert (HRD4 : decode_rd_ok W (ms_mem ms4) (TI.tf_addr fr) (mlen fr)).
{ apply (trans_rd_ok_view W W (ms_mem ms0) (ms_mem ms4) (TI.tf_addr fr) (mlen fr) HRD2).
  - exact Hfrk4.
  - intros s Hs. apply KF; unfold kLowMemEnd, kHighShadowEnd in Hs; lia. }
assert (Hrom4 : trans_rom_view_rd W (ms_mem ms4)).
{ intros a Ha. rewrite <- (Hrom2 a Ha). apply KF; revert Ha;
  unfold trans_in_ro_rd, TRANS_RO_RD, TRANS_RO_GLOBALS, TRANS_JT_LLVMF, TRANS_JT_NOTICE,
    TRANS_K_LLVMF, TRANS_K_POLL, TRANS_SCALE, TRANS_HOST, TRANS_DESK, TRANS_SPEC_BCAST, TRANS_SPEC_OUI,
    TRANS_STR_C24, TRANS_STR_PC, TRANS_CMD, TRANS_DESK2, TRANS_NOTDD, TRANS_OTHER, TRANS_STR4,
    TRANS_BROADCAST, TRANS_PNAME0, TRANS_PNAME1, TRANS_IO, TRANS_SPEC_C24, TRANS_SPEC_PC, TRANS_SRC,
    TRANS_DST, TRANS_NAME, TRANS_PERS;
  intros HE; repeat (apply Exists_cons in HE as [HE | HE]; [unfold in_zr in HE; cbn [fst snd] in HE; lia|]);
  apply Exists_nil in HE; destruct HE. }
assert (HSV4 : mrx_saved W (ms_mem ms4) sp1 regs0).
{ apply (mrx_saved_kept W W (ms_mem ms0) (ms_mem ms4) sp1 regs0 HSV0).
  intros a Ha. apply KF; lia. }
assert (TW4 : tw_at TMAP_A (aview segs (w_H W) (ms_mem ms4)) Bw).
{ apply (tw_kept TMAP_A (aview segs (w_H W) (ms_mem ms0))); [exact TW0|].
  intros x Hx. pose proof (TMAP_A_hull x Hx) as Hh.
  unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh. apply KF; lia. }
(* the valuation at MAC: the atoms below 1024 are the restart's *)
lazymatch type of HS2 with st_ok_pi _ _ ?EF _ _ => set (EX6 := EF) in * end.
assert (HEF6 : forall nn, (nn < 1024)%nat -> ew EX6 nn = ew EX3 nn)
  by (intros nn Hn; unfold EX6; repeat rewrite ew_ewset_other by lia; reflexivity).
assert (Usp6 : bv_unsigned (ew EX6 2) = sp1 - MRX_FRAME)
  by (rewrite (HEF6 2%nat ltac:(lia)); exact Usp3).
assert (DEN : forall (j : nat) (v : Z), ew EX6 j = w64 v -> 0 <= v < 2 ^ 64 ->
  sv_denot EX6 (SOff j 0) = Z_to_bv 64 v)
  by (intros j v Hv Hr; cbn [sv_denot]; rewrite Hv; unfold w64;
      rewrite unsigned_lit_small by lia; rewrite Z.add_0_r; reflexivity).
assert (C8 : ew EX6 8 = w64 (TI.tf_addr fr))
  by (rewrite (HEF6 8%nat ltac:(lia)), (EE1 8%nat (8%bv : bv 5) eq_refl); exact R8).
assert (C18 : ew EX6 18 = w64 SHADOW_OFF)
  by (rewrite (HEF6 18%nat ltac:(lia)), (EE1 18%nat (18%bv : bv 5) eq_refl); exact R18).
assert (C34 : ew EX6 34 = w64 (mfb fr 14)) by (rewrite (HEF6 34%nat ltac:(lia)); exact B34).
assert (C35 : ew EX6 35 = w64 (mfb fr 15)) by (rewrite (HEF6 35%nat ltac:(lia)); exact B35).
assert (C36 : ew EX6 36 = w64 (mfb fr 18)) by (rewrite (HEF6 36%nat ltac:(lia)); exact A36).
assert (C37 : ew EX6 37 = w64 (mfb fr 19)) by (rewrite (HEF6 37%nat ltac:(lia)); exact A37).
assert (C38 : ew EX6 38 = w64 (mfb fr 20)) by (rewrite (HEF6 38%nat ltac:(lia)); exact A38).
assert (C39 : ew EX6 39 = w64 (mfb fr 21)) by (rewrite (HEF6 39%nat ltac:(lia)); exact A39).
assert (C40 : ew EX6 40 = w64 (mfb fr 22)) by (rewrite (HEF6 40%nat ltac:(lia)); exact A40).
assert (C41 : ew EX6 41 = w64 (mfb fr 23)) by (rewrite (HEF6 41%nat ltac:(lia)); exact A41).
assert (C42 : ew EX6 42 = w64 (mfb fr 24)) by (rewrite (HEF6 42%nat ltac:(lia)); exact A42).
assert (C43 : ew EX6 43 = w64 (mfb fr 25)) by (rewrite (HEF6 43%nat ltac:(lia)); exact A43).
assert (C44 : ew EX6 44 = w64 (mfb fr 26)) by (rewrite (HEF6 44%nat ltac:(lia)); exact A44).
assert (C45 : ew EX6 45 = w64 (mfb fr 27)) by (rewrite (HEF6 45%nat ltac:(lia)); exact A45).
assert (C46 : ew EX6 46 = w64 (mfb fr 28)) by (rewrite (HEF6 46%nat ltac:(lia)); exact A46).
(* the three spill slots *)
pose proof (st_ok_pi_region_nth EX6 _ _ 0 _ HS2 eq_refl) as RGS.
cbn [ms_mem restrict] in RGS. destruct RGS as (_ & _ & _ & HCHS).
cbn [YP09.r_base YP09.r_chunks base_val] in HCHS. rewrite Usp6 in HCHS.
assert (SP16 : mrx_spill W (ms_mem ms4) sp1 16 fr 25).
{ unfold mrx_spill. replace (sp1 - MRX_FRAME + 16) with (sp1 - MRX_FRAME + 16) by lia.
  apply (hd_rdword_chunk EX6 (w_H W) (ms_mem ms4) (sp1 - MRX_FRAME) 16 (SOff 43 0));
  [ apply (proj1 (Forall_forall _ _) HCHS); hd_in
  | apply DEN; [exact C43 | hd_bb Hgarr] | hd_bb Hgarr ]. }
assert (SP24 : mrx_spill W (ms_mem ms4) sp1 24 fr 24).
{ unfold mrx_spill.
  apply (hd_rdword_chunk EX6 (w_H W) (ms_mem ms4) (sp1 - MRX_FRAME) 24 (SOff 42 0));
  [ apply (proj1 (Forall_forall _ _) HCHS); hd_in
  | apply DEN; [exact C42 | hd_bb Hgarr] | hd_bb Hgarr ]. }
assert (SP32 : mrx_spill W (ms_mem ms4) sp1 32 fr 21).
{ unfold mrx_spill.
  apply (hd_rdword_chunk EX6 (w_H W) (ms_mem ms4) (sp1 - MRX_FRAME) 32 (SOff 39 0));
  [ apply (proj1 (Forall_forall _ _) HCHS); hd_in
  | apply DEN; [exact C39 | hd_bb Hgarr] | hd_bb Hgarr ]. }
(* the registers at MAC *)
pmkst HS2.
hd_reg HS2 (Z_to_bv 5 2) (Z_to_bv 64 (sp1 - MRX_FRAME)) Q2
  ltac:(cbn [sv_denot]; rewrite Usp6; f_equal; lia).
hd_reg HS2 (3%bv : bv 5) (YK11.getr regs0 3) Q3
  ltac:(cbn [sv_denot]; rewrite (HEF6 3%nat ltac:(lia)),
        (EE1 3%nat (3%bv : bv 5) eq_refl), R3, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
hd_reg HS2 (4%bv : bv 5) (YK11.getr regs0 4) Q4
  ltac:(cbn [sv_denot]; rewrite (HEF6 4%nat ltac:(lia)),
        (EE1 4%nat (4%bv : bv 5) eq_refl), R4, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
hd_reg HS2 (Z_to_bv 5 8) (w64 (TI.tf_addr fr)) Q8 ltac:(apply DEN; [exact C8 | lia]).
hd_reg HS2 (Z_to_bv 5 18) (w64 SHADOW_OFF) Q18
  ltac:(apply DEN; [exact C18 | unfold SHADOW_OFF; lia]).
hd_reg HS2 (Z_to_bv 5 19) (w64 (mfb fr 18)) Q19 ltac:(apply DEN; [exact C36 | hd_bb Hgarr]).
hd_reg HS2 (Z_to_bv 5 20) (w64 (DSpec.spec_be16 (TW.zs (TI.tf_bytes fr)) 14)) Q20
  ltac:(rewrite (hd_den_or8 EX6 34 35 (mfb fr 14) (mfb fr 15) C34 C35 Hb14 Hb15);
        rewrite (hd_be16 fr 14 ltac:(lia) ltac:(lia)); reflexivity).
hd_reg HS2 (Z_to_bv 5 21) (w64 (mfb fr 20)) Q21 ltac:(apply DEN; [exact C38 | hd_bb Hgarr]).
hd_reg HS2 (Z_to_bv 5 22) (w64 (mfb fr 22)) Q22 ltac:(apply DEN; [exact C40 | hd_bb Hgarr]).
hd_reg HS2 (Z_to_bv 5 23) (w64 (mfb fr 26)) Q23 ltac:(apply DEN; [exact C44 | hd_bb Hgarr]).
hd_reg HS2 (Z_to_bv 5 24) (w64 (mfb fr 27)) Q24 ltac:(apply DEN; [exact C45 | hd_bb Hgarr]).
hd_reg HS2 (Z_to_bv 5 25) (w64 (mfb fr 28)) Q25 ltac:(apply DEN; [exact C46 | hd_bb Hgarr]).
hd_reg HS2 (Z_to_bv 5 26) (w64 (mfb fr 23)) Q26 ltac:(apply DEN; [exact C41 | hd_bb Hgarr]).
hd_reg HS2 (Z_to_bv 5 27) (w64 (mfb fr 19)) Q27 ltac:(apply DEN; [exact C37 | hd_bb Hgarr]).
(* the cut *)
replace (BASE + 14424) with (MRX_PC OFF_MAC)
  by (unfold MRX_PC, OFF_MAC; rewrite <- VB0; unfold AF_m_rx; lia).
apply (HKM W Bw).
eapply mrx_at_intro.
- exact HJ.
- reflexivity.
- apply Permutation_refl.
- exact (mo_le_refl MT MTL Sc).
- exact Q2.
- exact Q3.
- exact Q4.
- exact HSV4.
- exact TW4.
- unfold R_MAC. split; [reflexivity|]. split; [reflexivity|].
  split; [exact (conj Hgarr4 (conj HRD4 Hrom4))|].
  split; [unfold mrx_hdr; split; [unfold mlen in *; lia|]; split; [exact HSE16 | lia]|].
  split; [exact Q8|]. split; [exact Q19|]. split; [exact Q20|].
  split; [| exact Hm].
  unfold mrx_hregs.
  split; [exact Q18|]. split; [exact Q21|]. split; [exact Q22|]. split; [exact Q23|].
  split; [exact Q24|]. split; [exact Q25|]. split; [exact Q26|]. split; [exact Q27|].
  split; [exact SP16|]. split; [exact SP24 | exact SP32].
Qed.

End hd.
