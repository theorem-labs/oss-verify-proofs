(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, origin/cold/pg-prog), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-10: the walk is reac-repacer/fuzz_uci's check_clamp in image A, in the shape of the released image-A walks proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_entry.v, .../LLVMFuzzerTestOneInput_seg_copy.v and .../LLVMFuzzerTestOneInput_seg_exit_tail.v at origin/ossv/recipes 88154566652a: module paths, listing symbol type, the symbolic states, the cut points and every address and offset are this function's; the fake-frame class is 1, the single intrinsic is __asan_memcpy of 20 bytes, and the result is the caller-journal contract of lib/A/Prog/check_clamp_cg.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths changed; 663 of its 1139 lines of code are new or changed and 8 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths, module names and numbers changed; 770 of its 936 lines of code are new or changed and 973 lines of the source are left out. *)
(* on_data_seg_head: Theorem od_head : forall fx rc B MT, @od_head_stmt fx rc B MT (lib/B/Prog/on_data_seg_cut.v),
   the head piece of the walk of on_data on fuzz_transport.asan-ubsan (0x88a48 = transportb_sigma TB_on_data,
   AF_on_data = 0x77a8 of lib/B/Prog/DgnTransportBList.v), from the entry to the cut od_sc_at at send_control's entry
   (+0x170). Image B's form of lib/A/Prog/on_data_seg_head.v: the same cut and carried facts; the offsets, the order
   of the frame word's store and the UBSan alignment check of f are image B's. The walk holds the caller's G journal
   (lib/A/W_journalG.v ajournal_gx TG.G_HARNESS_B 0 []); the runs are the position-abstract runs of
   lib/B/Prog/TransportGRunB.v paj_run_x / paj_run_to_x:
     run 1   +0x000 .. +0x070  the frame (`addi sp, sp, -160`, `sd zero, 0(sp)`, the 13 saves), s0, the realign into
                               s1, s7 = now, s4 = fp, the flag word through its GOT word (1, so `beqz a2` is not
                               taken), s11 = the shadow base, s3 = s, a0 = 160, up to `jal __asan_stack_malloc_2`;
     +0x074                    the class-2 stack malloc: the statement's astack_malloc_realizes premise through
                               lib/A/Prog/TransportGFrame.v gx_stack_malloc_at (the frame F in a0, 4096 <= F);
     run 2a  +0x078 .. +0x0e0  `bnez s6` taken (the real-stack arm is not reached), the frame word at s1 + 48 (image B
                               stores it here, at +0x0a8), the frame's 24-byte header, s9 = the frame's shadow address
                               (it stops at the first shadow store);
     run 2b  +0x0e4 .. +0x144  the frame's shadow bytes 0 .. 19, the UBSan alignment check of f (`andi a1, s4, 7` at
                               +0x0f4 and `bnez a1` at +0x138: trans_dframe_at's fp mod 8 = 0, so the trap word at
                               +0x540 is not reached), s5 = fp + 20 and s2 = its shadow address (a run to +0x148);
     run 2c  +0x148 .. +0x16c  `lb a0, 0(s2)` (the shadow byte of fp + 20, which is 0), `bnez a0` not taken,
                               `lw a2, 0(s5)` (fr_send b), s8 = s + 18160, a1 = 0xa0, a0 = s, a3 = a4 = 0, up to
                               `jal send_control`: the cut od_sc_at.
   The shadow byte of fp + 20 and the four bytes at fp + 20 at +0x148 are those at entry: f lies in a frame of the
   call's frames (trans_dframe_at's decode_in_fake), whose bytes and shadow bytes what the call keeps so far keeps
   (TransportGCg.v dk_kept_frame_byte_g, dk_kept_ra_g); at entry decode_rd_ok makes f's 64 bytes addressable, and the
   shadow byte of fp + 23 is then 0 (fp mod 8 = 0). What the call keeps (acall_kept_g) runs from the entry to the stack
   malloc's return (TransportGCg.v dk_kept_step_g, then dk_kept_trans_g with the call's acall_kept) and from there over
   the three written ranges (dk_kept_own_g: the frame's header and shadow bytes, the slot s1 + 48 in the call's
   window). No byte of G is written, so the world relation at Bw holds at the cut. *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YN3v YI04 YI00 YI08 YI09 YG0s.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0p YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c YO0f.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB YF0x.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG TransportGFrame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TransportGRwB TransportGRunB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB CanKit CanLeafb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_set_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import io_send_cg send_control_cg on_ack_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import on_data_cg on_data_seg_cut.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TSess0 TSess.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Mem Cells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog Require diginet_frame_parse_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module FCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.AsanCells.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module LMem := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Mem.
Module LC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Cells.
Module PParse := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.diginet_frame_parse_c.
Module YF0x := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.YF0x.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

Definition ODH_B0 : Z * Z := (0, 0).

(* run 1, +0x000 .. +0x074: the stack region below the entry sp and the four image regions (the GOT word of the shadow
   base's cell, that cell, the GOT word of the flag word, the flag word). *)
Definition odh_got_uar : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 0)) 0 8 0 0 [YP09.mkChunk 0 (YP09.CVal 8 (SOff (A_OBJ 96) 0))].
Definition odh_uar_cell : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 96)) 0 4 0 0 [YP09.mkChunk 0 (YP09.CVal 4 (SLit 1))].
Definition odh_img_regions : smem := [got_regionP; bcell_regionP 32; odh_got_uar; odh_uar_cell].
Definition odh_regions1 : smem := stack_region ONDATA_FRAME :: odh_img_regions.
Definition odh_facts1 : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition ss_odh1 : sstate := mkSS AF_on_data sr_atoms odh_regions1 None odh_facts1.

(* run 2a, +0x078 .. +0x0e0: after the stack malloc, the frame F in a0 (atom 10); the run writes the frame word at
   s1 + 48 (atom 9) and the frame's 24-byte header, and stops at the first shadow store. *)
Definition ODH_C1 : Z := AF_on_data + 0x78.
Definition odh_rg_slot : YP09.region := YP09.mkRegion (Some 9%nat) 48 56 48 56 [].
Definition odh_rg_hdr : YP09.region := YP09.mkRegion (Some 10%nat) 0 24 0 24 [].
Definition odh_regions2 : smem := [odh_rg_slot; odh_rg_hdr].
Definition odh_facts2 : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5);
           (10%nat, mkAF 4096 (2 ^ 47) 6); (27%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition ss_odh2 : sstate := mkSS ODH_C1 sr_atoms odh_regions2 None odh_facts2.

(* run 2b, +0x0e4 .. +0x144: s9 (atom 25) holds the frame's shadow address; the run writes the frame's shadow bytes
   0 .. 19, decides the alignment check of s4 (atom 20 = fp, 8-aligned) and computes s5 and s2, up to +0x148. *)
Definition ODH_C2 : Z := AF_on_data + 0xe4.
Definition ODH_C3 : Z := AF_on_data + 0x148.
Definition odh_rg_sh : YP09.region := YP09.mkRegion (Some 25%nat) 0 20 0 20 [].
Definition odh_facts3 : facts :=
  mkFacts [(20%nat, mkAF 4096 (2 ^ 47) 3); (25%nat, mkAF SHADOW_OFF (2 ^ 46) 0)] [] [].
Definition ss_odh3 : sstate := mkSS ODH_C2 sr_atoms [odh_rg_sh] None odh_facts3.

(* run 2c, +0x148 .. +0x170: the shadow byte of fp + 20 at s2 (atom 18, the byte 0), the four bytes at fp + 20 at s5
   (atom 21, the value atom 33). *)
Definition odh_rg_sb : YP09.region := YP09.mkRegion (Some 18%nat) 0 1 0 0 [YP09.mkChunk 0 (YP09.CVal 1 (SLit 0))].
Definition odh_rg_f : YP09.region := YP09.mkRegion (Some 21%nat) 0 4 0 0 [YP09.mkChunk 0 (YP09.CVal 4 (SOff 33 0))].
Definition odh_regions4 : smem := [odh_rg_sb; odh_rg_f].
Definition odh_facts4 : facts := mkFacts [(33%nat, mkAF 0 (2 ^ 32 - 1) 0)] [] [].
Definition ss_odh4 : sstate := mkSS ODH_C3 sr_atoms odh_regions4 None odh_facts4.

(* ------------------------------------------------------------------ *)
(* The four bytes at f + 20 and the shadow byte of f + 20              *)
(* ------------------------------------------------------------------ *)

(* frame_f_bytes at code 0: 20 bytes, then the four bytes of fr_send b. *)
Lemma odh_ffb_split : forall buf b fj, DSpec.fr_code b = 0 -> length fj = 64%nat ->
  exists pre post, frame_f_bytes buf b fj =
    map (fun x : byte => bv_unsigned x) (pre ++ LMem.le4 (Z_to_bv 64 (DSpec.fr_send b)) ++ post) /\
    length pre = 20%nat.
Proof.
intros buf b fj Hc Hfj.
assert (Lb : (30 <= length b)%nat).
{ unfold DSpec.fr_code in Hc. destruct (Nat.ltb_spec (length b) 30) as [Hl|Hl]; [discriminate Hc | exact Hl]. }
exists (DSpec.fr_dst b ++ DSpec.fr_src b ++ LMem.le2 (Z_to_bv 64 (DSpec.fr_ethertype b)) ++
        firstn 2 (skipn 14 fj) ++ LMem.le2 (Z_to_bv 64 (DSpec.fr_numbytes b)) ++
        LMem.le2 (Z_to_bv 64 (DSpec.fr_sum b))).
eexists. split.
- unfold frame_f_bytes, frame_f_cells. rewrite Hc. cbn [Z.eqb]. unfold PParse.parse_cells.
  cbn [LC.cells_bytes LC.cbytes]. rewrite <- !app_assoc. reflexivity.
- rewrite !length_app, !LMem.length_le2. unfold DSpec.fr_dst, DSpec.fr_src.
  rewrite !length_firstn, !length_skipn, Hfj. lia.
Qed.

Lemma odh_ffb_byte : forall buf b fj (k : nat), DSpec.fr_code b = 0 -> length fj = 64%nat -> (k < 4)%nat ->
  nth (20 + k) (frame_f_bytes buf b fj) 0 = YG0f.le_byte (DSpec.fr_send b) 4 k.
Proof.
intros buf b fj k Hc Hfj Hk. destruct (odh_ffb_split buf b fj Hc Hfj) as (pre & post & -> & Hpre).
rewrite map_app, app_nth2 by (rewrite length_map; lia). rewrite length_map, Hpre.
replace (20 + k - 20)%nat with k by lia.
rewrite map_app, app_nth1 by (rewrite length_map, LMem.length_le4; lia).
pose proof (can_leafb_le4_byte (DSpec.fr_send b) k Hk) as H. unfold LMem.wa in H.
rewrite (nth_error_nth' _ (Z_to_bv 8 0)) in H by (rewrite LMem.length_le4; lia).
cbn [option_map] in H.
rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map, LMem.length_le4; lia).
rewrite map_nth.
exact (f_equal (fun o => match o with Some z => z | None => 0 end) H).
Qed.

Lemma odh_ffb_len : forall buf b fj, DSpec.fr_code b = 0 -> length fj = 64%nat ->
  (24 <= length (frame_f_bytes buf b fj))%nat.
Proof.
intros buf b fj Hc Hfj. destruct (odh_ffb_split buf b fj Hc Hfj) as (pre & post & -> & Hpre).
rewrite length_map, !length_app, Hpre, LMem.length_le4. lia.
Qed.

(* A byte of a garr8 array, read through the view. *)
Lemma odh_garr8_view : forall (H : word -> bool) (mem : word -> option byte) a (l : list Z) (j : nat),
  garr8 tfibsegs (mrestrict H mem) a l -> (j < length l)%nat ->
  aview tfibsegs H mem (a + Z.of_nat j) = Some (nth j l 0).
Proof.
intros H mem a l j Hg Hj. pose proof (garr8_mbyte tfibsegs (mrestrict H mem) a l j Hg Hj) as Hb.
destruct (Hg j Hj) as [_ Hr].
unfold aview. rewrite Hb. cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. exact Hr.
Qed.

(* n bytes of the view that are the little-endian bytes of v. *)
Lemma odh_val_of_view : forall (H : word -> bool) (mem : word -> option byte) a (n : nat) v,
  (forall k, (k < n)%nat -> aview tfibsegs H mem (a + Z.of_nat k) = Some (YG0f.le_byte v n k)) ->
  val_mem tfibsegs (mrestrict H mem) a n v.
Proof.
intros H mem a n v Hv k Hk. pose proof (Hv k Hk) as E. unfold aview in E.
destruct (mbyte tfibsegs (mrestrict H mem) (a + Z.of_nat k)) as [x|] eqn:Ex; [|discriminate E].
cbn [option_map] in E. f_equal.
pose proof (f_equal (fun o => match o with Some z => z | None => 0 end) E) as E'. cbn beta iota in E'.
change (YO0f.le_byte v n k) with (YG0f.le_byte v n k). rewrite <- E'. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

(* The shadow byte of f + 20 is 0: f's 64 bytes are addressable and fp mod 8 = 0, so the byte of fp + 23 is 0. *)
Lemma odh_sh0 : forall (rd : Z -> option Z) fp, fp mod 8 = 0 -> range_addressable rd SHADOW_OFF fp 64 ->
  rd (SHADOW_OFF + (fp + 20) / 8) = Some 0.
Proof.
intros rd fp H8 HR. destruct (HR (fp + 23) ltac:(lia)) as (s & Hs & Hok).
pose proof (Z.div_mod fp 8 ltac:(lia)) as D. rewrite H8, Z.add_0_r in D.
assert (E1 : (fp + 23) / 8 = fp / 8 + 2).
{ rewrite D at 1. replace (8 * (fp / 8) + 23) with ((fp / 8 + 2) * 8 + 7) by ring.
  rewrite Z.div_add_l by lia. change (7 / 8) with 0. ring. }
assert (E2 : (fp + 20) / 8 = fp / 8 + 2).
{ rewrite D at 1. replace (8 * (fp / 8) + 20) with ((fp / 8 + 2) * 8 + 4) by ring.
  rewrite Z.div_add_l by lia. change (4 / 8) with 0. ring. }
assert (E3 : (fp + 23) mod 8 = 7).
{ rewrite D at 1. replace (8 * (fp / 8) + 23) with (7 + (fp / 8 + 2) * 8) by ring.
  rewrite Z_mod_plus_full. reflexivity. }
unfold shadow_of_addr in Hs. rewrite E1 in Hs. rewrite E2.
destruct Hok as [-> | [H1 H2]]; [exact Hs|]. rewrite E3 in H1. lia.
Qed.

(* The sign-extended 4-byte load of atom 33. *)
Lemma odh_sext : forall E v, 0 <= v < 2 ^ 32 -> ew E 33 = Z_to_bv 64 v ->
  sv_denot E (SExt true 32 (SOff 33 0)) = Z_to_bv 64 (bv_swrap 32 v).
Proof.
intros E v R H. cbn [sv_denot]. rewrite H.
rewrite unsigned_lit_small by lia. rewrite Z.add_0_r.
rewrite LMem.sext_small, LMem.signed_of_extract by lia.
rewrite unsigned_lit_small by lia. reflexivity.
Qed.

(* `addi s5, s4, 20`, `srli s2, s5, 3`, `add s2, s2, s11` in one run: the shadow address of an atom plus an offset
   (CanKit.v can_denot_shadow at a nonzero offset). *)
Lemma odh_denot_shadow_off : forall E n m v c SHB,
  ew E n = Z_to_bv 64 v -> ew E m = Z_to_bv 64 SHB ->
  0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 -> 0 <= SHB -> SHB + (v + c) / 8 < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff n c) (SLit 3)) (SOff m 0)) = Z_to_bv 64 (SHB + (v + c) / 8).
Proof.
intros E n m v c SHB Hn Hm Hv Hc HS1 HS2.
assert (HD : 0 <= (v + c) / 8) by (apply Z.div_pos; lia).
pose proof (U_atom_off E n v c Hn Hv Hc) as Un.
pose proof (U_atom_off E m SHB 0 Hm ltac:(lia) ltac:(lia)) as Um. rewrite Z.add_0_r in Um.
rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
rewrite Un, Um, U_SLit, (zcanon_id 3) by (unfold M64; lia).
change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
rewrite (zcanon_id ((v + c) / 8)) by (unfold M64; lia).
rewrite (Z.add_comm ((v + c) / 8) SHB). apply zcanon_id. unfold M64. lia.
Qed.

Section sh. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

Lemma odh_vals : VAL (A_OBJ 1) = FCells.GOT_CELL_K /\ VAL (A_OBJ 95) = FCells.CELL_K /\
  VAL (A_OBJ 0) = FCells.GOT_UAR /\ VAL (A_OBJ 96) = FCells.UAR /\
  BASE + AF_on_data = transportb_sigma TB_on_data.
Proof. vm_compute. repeat split. Qed.

(* The four image regions hold what transport_cells says they hold, at any AR state. *)
Lemma odh_img_ok : forall ly S (W : world segs) mem md (E : env),
  transport_cells B -> @AR rc segs B ly S W mem md ->
  ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1)) -> ew E (A_OBJ 95) = Z_to_bv 64 (VAL (A_OBJ 95)) ->
  ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0)) -> ew E (A_OBJ 96) = Z_to_bv 64 (VAL (A_OBJ 96)) ->
  ew E 32 = Z_to_bv 64 SHADOW_OFF ->
  Forall (region_ok segs E (mrestrict (w_H W) mem)) odh_img_regions /\
  pairwise_disjoint E odh_img_regions.
Proof.
  intros ly S W mem md E HCELLS HAR E1 E95 E0 E96 E32.
  destruct (HCELLS ly) as (I1 & I2 & _ & _ & _ & I6 & I7 & _).
  destruct odh_vals as (V1 & V95 & V0 & V96 & _).
  assert (CH : forall c, In c (as_const B ly) -> cell_holds B ly (aview segs (w_H W) mem) c).
  { intros c Hc. destruct HAR as (Mx & _). exact (proj1 (Forall_forall _ _) (am_const _ _ _ _ Mx) c Hc). }
  assert (Kcell : rdword (aview segs (w_H W) mem) FCells.CELL_K = Some FCells.ASAN_K)
    by (apply (rdword_cell B ly); [unfold FCells.ASAN_K; lia | exact (CH _ I1)]).
  assert (Kgot : rdword (aview segs (w_H W) mem) FCells.GOT_CELL_K = Some FCells.CELL_K)
    by (apply (rdword_cell B ly); [unfold FCells.CELL_K; lia | exact (CH _ I2)]).
  assert (Kguar : rdword (aview segs (w_H W) mem) FCells.GOT_UAR = Some FCells.UAR)
    by (apply (rdword_cell B ly); [unfold FCells.UAR; lia | exact (CH _ I7)]).
  assert (Kuar : rd32 (aview segs (w_H W) mem) FCells.UAR 1).
  { pose proof (CH _ I6) as H6. unfold cell_holds in H6. cbn [c_at c_val c_w z4 c4 aeval] in H6.
    intros k Hk. exact (H6 k Hk). }
  assert (VB : forall n v0, ew E n = Z_to_bv 64 v0 -> 0 <= v0 < 2 ^ 64 -> base_val E (Some n) = v0)
    by (intros n v0 Hn Hv0; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hv0).
  split.
  - unfold odh_img_regions, got_regionP, bcell_regionP, odh_got_uar, odh_uar_cell.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    + rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E1) by (rewrite V1; unfold FCells.GOT_CELL_K; lia).
      split; [rewrite V1; unfold FCells.GOT_CELL_K; lia|].
      split; [rewrite V1; unfold FCells.GOT_CELL_K; lia|].
      split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val segs E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 95) 0) (VAL (A_OBJ 95)));
      [cbn [sv_denot]; rewrite E95, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | rewrite V95; unfold FCells.CELL_K; lia | lia |].
      rewrite Z.add_0_r, V1, V95. exact (val_mem_of_rdword segs (w_H W) mem _ _ Kgot).
    + rewrite (VB (A_OBJ 95) (VAL (A_OBJ 95)) E95) by (rewrite V95; unfold FCells.CELL_K; lia).
      split; [rewrite V95; unfold FCells.CELL_K; lia|].
      split; [rewrite V95; unfold FCells.CELL_K; lia|].
      split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val segs E _ (VAL (A_OBJ 95)) 0 8 (SOff 32 0) SHADOW_OFF);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | unfold SHADOW_OFF; lia | lia |].
      rewrite Z.add_0_r, V95. exact (val_mem_of_rdword segs (w_H W) mem _ _ Kcell).
    + rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E0) by (rewrite V0; unfold FCells.GOT_UAR; lia).
      split; [rewrite V0; unfold FCells.GOT_UAR; lia|].
      split; [rewrite V0; unfold FCells.GOT_UAR; lia|].
      split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val segs E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 96) 0) (VAL (A_OBJ 96)));
      [cbn [sv_denot]; rewrite E96, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | rewrite V96; unfold FCells.UAR; lia | lia |].
      rewrite Z.add_0_r, V0, V96. exact (val_mem_of_rdword segs (w_H W) mem _ _ Kguar).
    + rewrite (VB (A_OBJ 96) (VAL (A_OBJ 96)) E96) by (rewrite V96; unfold FCells.UAR; lia).
      split; [rewrite V96; unfold FCells.UAR; lia|].
      split; [rewrite V96; unfold FCells.UAR; lia|].
      split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val segs E _ (VAL (A_OBJ 96)) 0 4 (SLit 1) 1); [reflexivity | lia | lia |].
      rewrite Z.add_0_r, V96. exact (can_val_mem_of_rd32 segs (w_H W) mem _ _ Kuar).
  - apply pairwise_disjoint_of_extents.
    unfold odh_img_regions, got_regionP, bcell_regionP, odh_got_uar, odh_uar_cell, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E1) by (rewrite V1; unfold FCells.GOT_CELL_K; lia).
    rewrite (VB (A_OBJ 95) (VAL (A_OBJ 95)) E95) by (rewrite V95; unfold FCells.CELL_K; lia).
    rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E0) by (rewrite V0; unfold FCells.GOT_UAR; lia).
    rewrite (VB (A_OBJ 96) (VAL (A_OBJ 96)) E96) by (rewrite V96; unfold FCells.UAR; lia).
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    rewrite V1, V95, V0, V96. unfold FCells.GOT_CELL_K, FCells.CELL_K, FCells.GOT_UAR, FCells.UAR.
    repeat split; first [exact I | lia].
Qed.

(* The walk's valuation at the entry: the 32 registers and the shadow base (atom 32). *)
Definition odh_E (regs : bvmap 5 word) : env := Eimg (PI := PI_transportb) (Ereg regs [w64 SHADOW_OFF]).

Lemma odh_ew_reg : forall regs n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (odh_E regs) n = YK11.getr regs r.
Proof. intros regs n r Hn. unfold odh_E. apply can_ew_Eimg_Ereg_nat. exact Hn. Qed.
Lemma odh_ew_32 : forall regs, ew (odh_E regs) 32 = Z_to_bv 64 SHADOW_OFF.
Proof. intros regs. unfold odh_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0). Qed.
Lemma odh_ew_obj : forall regs i, (i < 97)%nat -> ew (odh_E regs) (A_OBJ i) = Z_to_bv 64 (VAL (A_OBJ i)).
Proof. intros regs i Hi. unfold odh_E. apply Eimg_img. unfold A_OBJ, A_TEXT, A_LIM. lia. Qed.
Lemma odh_env_img : forall regs, img_env VAL A_LIM (odh_E regs).
Proof. intros regs. unfold odh_E. apply Eimg_env. Qed.

(* The entry state of run 1 (the saves go into the stack region). *)
Lemma odh_entry1 : forall ly S (W : world segs) regs mem md,
  transport_cells B -> @AR rc segs B ly S W mem md ->
  (forall a, spZ regs - ONDATA_FRAME <= a < spZ regs -> apresent (w_H W) mem a) ->
  2 ^ 46 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
  st_ok_pi segs VAL (odh_E regs) ss_odh1
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + AF_on_data)) mem (YK11.seg_rom segs))).
Proof.
  intros ly S W regs mem md HCELLS HAR Hpres Hsp Hsp16.
  rewrite restrict_mkst_fx. unfold ss_odh1, odh_regions1.
  assert (Usp : bv_unsigned (ew (odh_E regs) 2) = spZ regs)
    by (rewrite (odh_ew_reg regs 2 2%bv eq_refl); reflexivity).
  assert (E32 : ew (odh_E regs) 32 = Z_to_bv 64 SHADOW_OFF) by apply odh_ew_32.
  destruct (odh_img_ok ly S W mem md (odh_E regs) HCELLS HAR
    (odh_ew_obj regs 1 ltac:(lia)) (odh_ew_obj regs 95 ltac:(lia))
    (odh_ew_obj regs 0 ltac:(lia)) (odh_ew_obj regs 96 ltac:(lia)) E32) as [HRs HPd].
  destruct odh_vals as (V1 & V95 & V0 & V96 & _).
  assert (VB : forall n v0, ew (odh_E regs) n = Z_to_bv 64 v0 -> 0 <= v0 < 2 ^ 64 ->
    base_val (odh_E regs) (Some n) = v0)
    by (intros n v0 Hn Hv0; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hv0).
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [| exact HRs].
    unfold stack_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite Usp. unfold ONDATA_FRAME in *.
    split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply Hpres. lia.
  - unfold odh_img_regions in *. apply pairwise_disjoint_of_extents.
    unfold stack_region, got_regionP, bcell_regionP, odh_got_uar, odh_uar_cell, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) (odh_ew_obj regs 1 ltac:(lia)))
      by (rewrite V1; unfold FCells.GOT_CELL_K; lia).
    rewrite (VB (A_OBJ 95) (VAL (A_OBJ 95)) (odh_ew_obj regs 95 ltac:(lia)))
      by (rewrite V95; unfold FCells.CELL_K; lia).
    rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) (odh_ew_obj regs 0 ltac:(lia)))
      by (rewrite V0; unfold FCells.GOT_UAR; lia).
    rewrite (VB (A_OBJ 96) (VAL (A_OBJ 96)) (odh_ew_obj regs 96 ltac:(lia)))
      by (rewrite V96; unfold FCells.UAR; lia).
    cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    rewrite V1, V95, V0, V96. unfold FCells.GOT_CELL_K, FCells.CELL_K, FCells.GOT_UAR, FCells.UAR, ONDATA_FRAME.
    repeat split; first [exact I | lia].
  - unfold odh_facts1, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E32, unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; unfold SHADOW_OFF; lia.
Qed.

(* The entry state of run 2a: the frame F in a0 (atom 10), the slot s1 + 48 and the frame's header writable. *)
Lemma odh_entry2 : forall (W : world segs) regs mem (F spv : Z),
  YK11.getr regs 2 = w64 spv -> YK11.getr regs 9 = w64 spv ->
  YK11.getr regs 10 = w64 F -> YK11.getr regs 27 = w64 SHADOW_OFF ->
  2 ^ 46 <= spv <= 2 ^ 47 -> spv mod 32 = 0 ->
  4096 <= F -> F + 256 <= 2 ^ 47 -> F mod 64 = 0 -> F + 24 <= spv + 48 ->
  (forall a, spv + 48 <= a < spv + 56 -> apresent (w_H W) mem a) ->
  (forall a, F <= a < F + 24 -> apresent (w_H W) mem a) ->
  st_ok_pi segs VAL (odh_E regs) ss_odh2
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + ODH_C1)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem F spv R2 R9 R10 R27 Hsp Hsp32 HF0 HFs HF64 Hdj Hpslot Hpframe.
  rewrite restrict_mkst_fx. unfold ss_odh2, odh_regions2.
  assert (U2 : bv_unsigned (ew (odh_E regs) 2) = spv)
    by (rewrite (odh_ew_reg regs 2 2%bv eq_refl), R2; apply unsigned_lit_small; lia).
  assert (U9 : bv_unsigned (ew (odh_E regs) 9) = spv)
    by (rewrite (odh_ew_reg regs 9 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
  assert (U10 : bv_unsigned (ew (odh_E regs) 10) = F)
    by (rewrite (odh_ew_reg regs 10 10%bv eq_refl), R10; apply unsigned_lit_small; lia).
  assert (U27 : bv_unsigned (ew (odh_E regs) 27) = SHADOW_OFF)
    by (rewrite (odh_ew_reg regs 27 27%bv eq_refl), R27; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (U32 : bv_unsigned (ew (odh_E regs) 32) = SHADOW_OFF)
    by (rewrite (odh_ew_32 regs); apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [odh_rg_slot odh_rg_hdr
         YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite U9. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Hpslot. lia.
    + rewrite U10. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Hpframe. lia.
  - apply pairwise_disjoint_of_extents.
    unfold odh_rg_slot, odh_rg_hdr, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite U9, U10. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; first [exact I | lia].
  - unfold odh_facts2, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U2, U9, U10, U27, U32.
    change (2 ^ 5) with 32. change (2 ^ 6) with 64. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; unfold SHADOW_OFF; lia.
Qed.

(* The entry state of run 2b: the frame's 20 shadow bytes at s9 (atom 25), s4 = fp (atom 20, 8-aligned). *)
Lemma odh_entry3 : forall (W : world segs) regs mem (SH fp : Z),
  YK11.getr regs 20 = w64 fp -> YK11.getr regs 25 = w64 SH -> SHADOW_OFF <= SH -> SH + 20 <= 2 ^ 46 ->
  4096 <= fp <= 2 ^ 47 -> fp mod 8 = 0 ->
  (forall a, SH <= a < SH + 20 -> apresent (w_H W) mem a) ->
  st_ok_pi segs VAL (odh_E regs) ss_odh3
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + ODH_C2)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem SH fp R20 R25 Hlo Hhi Hfp Hfp8 Hpres.
  rewrite restrict_mkst_fx. unfold ss_odh3.
  assert (U20 : bv_unsigned (ew (odh_E regs) 20) = fp)
    by (rewrite (odh_ew_reg regs 20 20%bv eq_refl), R20; apply unsigned_lit_small; lia).
  assert (U25 : bv_unsigned (ew (odh_E regs) 25) = SH)
    by (rewrite (odh_ew_reg regs 25 25%bv eq_refl), R25; apply unsigned_lit_small; unfold SHADOW_OFF in *; lia).
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold odh_rg_sh, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U25. split; [unfold SHADOW_OFF in *; lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply Hpres. lia.
  - apply pairwise_disjoint_of_extents.
    unfold odh_rg_sh, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    cbn [zpairwise_disjoint zall_disjoint]. repeat split.
  - unfold odh_facts3, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U20, U25.
    change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; try exact Hfp8; unfold SHADOW_OFF in *; lia.
Qed.

(* The valuation of run 2c: the 32 registers at +0x148, the shadow base (atom 32) and the value of the four bytes at
   fp + 20 (atom 33). *)
Definition odh_E4 (regs : bvmap 5 word) (v : Z) : env :=
  Eimg (PI := PI_transportb) (Ereg regs [w64 SHADOW_OFF; Z_to_bv 64 v]).

Lemma odh_entry4 : forall (W : world segs) regs mem (fp v : Z),
  YK11.getr regs 18 = w64 (SHADOW_OFF + (fp + 20) / 8) -> YK11.getr regs 21 = w64 (fp + 20) ->
  in_app fp 64 -> 0 <= v < 2 ^ 32 ->
  aview segs (w_H W) mem (SHADOW_OFF + (fp + 20) / 8) = Some 0 ->
  val_mem segs (mrestrict (w_H W) mem) (fp + 20) 4 v ->
  st_ok_pi segs VAL (odh_E4 regs v) ss_odh4
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + ODH_C3)) mem (YK11.seg_rom segs))).
Proof.
intros W regs mem fp v R18 R21 Happ Hv Hsb Hval.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (odh_E4 regs v) n = YK11.getr regs r)
  by (intros n r Hn; unfold odh_E4; apply can_ew_Eimg_Ereg_nat; exact Hn).
assert (E33 : ew (odh_E4 regs v) 33 = Z_to_bv 64 v)
  by (unfold odh_E4; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (SO : SHADOW_OFF = 2147450880) by reflexivity.
destruct Happ as (Hf4096 & Happ).
pose proof (@ASAN_CEIL_range rc) as [HC _].
assert (Hfhi : fp + 64 <= 2 ^ 47) by (destruct Happ as [X | [_ X]]; unfold kLowShadowBeg in X; lia).
assert (HSB : SHADOW_OFF <= SHADOW_OFF + (fp + 20) / 8 < 2 ^ 46).
{ split; [pose proof (Z.div_pos (fp + 20) 8 ltac:(lia) ltac:(lia)); lia|].
  assert ((fp + 20) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia). unfold SHADOW_OFF. change (2 ^ 47 / 8) with (2 ^ 44) in H. lia. }
assert (U18 : bv_unsigned (ew (odh_E4 regs v) 18) = SHADOW_OFF + (fp + 20) / 8)
  by (rewrite (EE 18%nat 18%bv eq_refl), R18; apply unsigned_lit_small; unfold SHADOW_OFF in *; lia).
assert (U21 : bv_unsigned (ew (odh_E4 regs v) 21) = fp + 20)
  by (rewrite (EE 21%nat 21%bv eq_refl), R21; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew (odh_E4 regs v) 33) = v)
  by (rewrite E33; apply unsigned_lit_small; lia).
(* the shadow byte is apart from f's bytes: f lies in application memory *)
assert (Hdj : SHADOW_OFF + (fp + 20) / 8 + 1 <= fp + 20 \/ fp + 24 <= SHADOW_OFF + (fp + 20) / 8).
{ unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *.
  destruct Happ as [X | [X1 X2]]; [right; lia | left].
  assert ((fp + 20) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia). change (2 ^ 47 / 8) with (2 ^ 44) in H. lia. }
rewrite restrict_mkst_fx. unfold ss_odh4, odh_regions4.
apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [odh_rg_sb odh_rg_f
       YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite U18. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val segs _ _ (SHADOW_OFF + (fp + 20) / 8) 0 1 (SLit 0) 0); [reflexivity | lia | lia |].
    rewrite Z.add_0_r. apply odh_val_of_view. intros k Hk. replace k with 0%nat by lia.
    cbn [Z.of_nat]. rewrite Z.add_0_r, Hsb. reflexivity.
  + rewrite U21. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val segs _ _ (fp + 20) 0 4 (SOff 33 0) v);
      [cbn [sv_denot]; rewrite U33, Z.add_0_r; reflexivity | exact Hv | lia |].
    rewrite Z.add_0_r. exact Hval.
- apply pairwise_disjoint_of_extents.
  unfold odh_rg_sb, odh_rg_f, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite U18, U21. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  destruct Hdj as [Hdj | Hdj]; repeat split; first [exact I | lia].
- unfold odh_facts4, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U33. rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac. *)
Ltac odh_reg HS r v H tac :=
  lazymatch type of HS with
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  end.
(* Region i of the symbolic state HS, at the machine state's memory. *)
Ltac odh_region HS i HR :=
  lazymatch type of HS with
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?sg ?Ex ?ssx (restrict ?Hh ?msx) =>
      let r0 := eval vm_compute in (nth i (ss_mem ssx) got_regionP) in
      assert (HR : region_ok sg Ex (ms_mem (restrict Hh msx)) r0)
        by (apply (can_region_nth Ex ssx (restrict Hh msx) i r0 HS); vm_compute; reflexivity)
  | st_ok_pi ?sg ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let r0 := eval vm_compute in (nth i (ss_mem ssx) got_regionP) in
      assert (HR : region_ok sg Ex (ms_mem (restrict Hh msx)) r0)
        by (let HS' := fresh in pose proof HS as HS'; unfold st_ok_pi in HS';
            eapply (can_region_nth Ex _ (restrict Hh msx) i r0 HS'); vm_compute; reflexivity)
  end; cbn [ms_mem restrict] in HR.
Ltac odh_u64 x := pose proof (bv_unsigned_in_range 64 x) as Hrg; unfold bv_modulus in Hrg;
  change (2 ^ Z.of_N 64) with (2 ^ 64) in Hrg; lia.
(* The awr obligation's regions, computed. *)
Ltac odh_awr_rs :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
(* A callee-saved register at the machine state of HS, from the equation Q of its value at the run's start. *)
Ltac odh_kreg HS rg r n Q H :=
  lazymatch type of Q with _ = ?v =>
    odh_reg HS r v H
      ltac:(cbn [sv_denot]; rewrite (odh_ew_reg rg n r eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Q) end.
(* The same at the state of run 2c's end, whose valuation is odh_E4 (the run makes no fresh atom). *)
Ltac odh_kreg4 HS EE4 r n Q H :=
  lazymatch type of Q with _ = ?v =>
    odh_reg HS r v H
      ltac:(cbn [sv_denot]; rewrite (EE4 n r eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Q) end.
(* The machine state a run left, named. *)
Ltac odh_msname HS nm :=
  lazymatch type of HS with
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok _ _ _ (restrict _ ?mf) =>
      rename mf into nm
  | st_ok_pi _ _ _ _ (restrict _ ?mf) => rename mf into nm
  end.
(* The windows a run's regions may write, computed; each case is closed by lia. *)
Ltac odh_windows Hin Hx :=
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx | ]).

(* The thirteen words the prologue saves, as (offset from the entry stack pointer, register). *)
Definition odh_saved : list (Z * bv 5) :=
  [(-8, 1%bv); (-16, 8%bv); (-24, 9%bv); (-32, 18%bv); (-40, 19%bv); (-48, 20%bv); (-56, 21%bv);
   (-64, 22%bv); (-72, 23%bv); (-80, 24%bv); (-88, 25%bv); (-96, 26%bv); (-104, 27%bv)].

(* Every byte of the caller's stack window is present at any memory of the G journal. *)
Lemma odh_jpres : forall STK sp0 FP ly S W0 mem0 md0 own ly' S' (W' : world segs) mem' md' k,
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem'
    md' k ->
  forall a, sp0 - STK <= a < sp0 -> apresent (w_H W') mem' a.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k HJ.
pose proof HJ as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hp & _). exact Hp.
Qed.

Lemma odh_holds : @od_head_stmt fx rc B MT.
Proof.
unfold od_head_stmt, od_top_at. intros SC LAWS0 CALLEES.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' HPRE HTFG.
pose proof LAWS0 as (HPCS & HCELLS & HODC & HGU & HGNE0 & HROU & HRNE & LAWS & MTL & MTF & SMP & ASF & FFL
  & HGX & HGNE).
pose proof CALLEES as (ASM0 & _ & _ & _ & _).
pose proof HPRE as (HJe & Hra & Hra4 & Hgp & Htp & H10 & H11 & H12 & Hsp16 & Hlo & Hhi & Hnow & HDF & Htw & Hfn
  & Hm & HTF & HROM & HAP & Hinv1 & Hinv4 & Hinv3 & Hcnt & Hev).
pose proof HDF as (Hcode & Hbuf0 & Hgb & Hsrcb & Howb & HnGb & Hfp0 & Hfp8 & Hfj & Hgf & Hfake & Hrdf & Howf).
pose proof (ASM0 fx) as ASM. clear ASM0.
pose proof HJe as (HSTK & _ & (memS & HJi & _) & _).
rewrite !Z.add_0_r in HJi.
pose proof HJi as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & Hstk & _).
pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
clear HJi memS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FS : ONDATA_STK = ltac:(let v := eval vm_compute in ONDATA_STK in exact v)) by reflexivity.
assert (FF : ONDATA_FRAME = 160) by reflexivity.
assert (CS : ONDATA_S = 6157888) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
assert (Hsp : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
(* f: its frame of the call's frames *)
destruct Hfake as (cf & pf & Hinf & Hfl & Hfh).
destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cf pf HAR Hinf) as (Hf4096 & Hfce & Hfapp).
change FRAME_F_SIZE with 64 in Hfh, Hrdf.
assert (Hfapp64 : in_app fp 64)
  by (apply (in_app_sub _ _ fp 64 Hfapp); [exact Hfl | lia | exact Hfh]).
assert (HfR : 0 <= DSpec.fr_send b < 2 ^ 32) by apply DSpec.be32_range.
assert (Hpres1 : forall a, spZ regs - ONDATA_FRAME <= a < spZ regs -> apresent (w_H W) memc a)
  by (intros a Ha; apply Hpres0; lia).
pose proof (odh_entry1 lyc Sc W regs memc mdc HCELLS HAR Hpres1 Hsp Hsp16) as HS.
assert (HEI : img_env VAL A_LIM (odh_E regs)) by apply odh_env_img.
assert (SHOK : sh_ok segs (SOff 32 0) (@nil shent) (odh_E regs) (mrestrict (w_H W) memc)) by constructor.
assert (Usp : bv_unsigned (ew (odh_E regs) 2) = spZ regs)
  by (rewrite (odh_ew_reg regs 2 2%bv eq_refl); reflexivity).
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B
  HGX 0 []) as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
  TG.G_HARNESS_B HGX 0 []) as RUNTO.
pose proof HJe as HJ.
unfold cfg_at.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + AF_on_data)) memc
    (YK11.seg_rom segs)) mdc) Q) end.
(* ---- run 1, +0x000 .. +0x074 ---- *)
paj_run_tok RUN HS HJ SHOK ODH_B0.
{ odh_awr_rs.
  apply awr_ok_x_cons;
  [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite Usp in Ha;
    left; split; [unfold awr_byte; left; lia | lia] |].
  repeat (apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |]).
  apply awr_ok_x_nil. }
rename HF into HF1, HFr into HFr1, HG into HG1. odh_msname HS ms1.
set (sp1 := 32 * ((spZ regs + -160) / 32)).
destruct (can_sp1_facts (spZ regs + -160) ltac:(lia) ltac:(rewrite <- Zplus_mod_idemp_l, Hsp16; reflexivity))
  as (Hsp1r & Hsp1al & Hsp1al16).
fold sp1 in Hsp1r, Hsp1al, Hsp1al16.
assert (Gsp1 : spZ regs - 176 <= sp1 <= spZ regs - 160) by (clear - Hsp1r; lia).
assert (E2' : ew (odh_E regs) 2 = Z_to_bv 64 (spZ regs))
  by (rewrite (odh_ew_reg regs 2 2%bv eq_refl); unfold spZ; symmetry; apply Z_to_bv_bv_unsigned).
odh_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 30752)) R1 ltac:(apply codeptr_val; exact HEI).
odh_reg HS (2%bv : bv 5) (Z_to_bv 64 sp1) R2
  ltac:(exact (can_denot_and_m32 (odh_E regs) 2 (spZ regs) (-160) E2' ltac:(lia) ltac:(lia) ltac:(lia))).
odh_reg HS (3%bv : bv 5) (w64 (as_gp B)) R3
  ltac:(cbn [sv_denot]; rewrite (odh_ew_reg regs 3 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Hgp).
odh_reg HS (4%bv : bv 5) (w64 (as_tp B)) R4
  ltac:(cbn [sv_denot]; rewrite (odh_ew_reg regs 4 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Htp).
odh_reg HS (8%bv : bv 5) (w64 (spZ regs)) R8 ltac:(cbn [sv_denot]; rewrite Usp, Z.add_0_r; reflexivity).
odh_reg HS (9%bv : bv 5) (Z_to_bv 64 sp1) R9
  ltac:(exact (can_denot_and_m32_add0 (odh_E regs) 2 (spZ regs) (-160) E2' ltac:(lia) ltac:(lia) ltac:(lia))).
odh_reg HS (19%bv : bv 5) (w64 ONDATA_S) R19
  ltac:(cbn [sv_denot]; rewrite (odh_ew_reg regs 10 10%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact H10).
odh_reg HS (20%bv : bv 5) (w64 fp) R20
  ltac:(cbn [sv_denot]; rewrite (odh_ew_reg regs 11 11%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact H11).
odh_reg HS (23%bv : bv 5) (w64 now) R23
  ltac:(cbn [sv_denot]; rewrite (odh_ew_reg regs 12 12%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact H12).
odh_reg HS (27%bv : bv 5) (w64 SHADOW_OFF) R27
  ltac:(cbn [sv_denot]; rewrite (odh_ew_32 regs), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
(* The thirteen words the prologue saved, read back from the stack region the run wrote. *)
odh_region HS 0%nat HRsk.
assert (HSVo : forall (o : Z) (r : bv 5), In (o, r) odh_saved -> -104 <= o <= -8).
{ intros o r Hin. unfold odh_saved in Hin. cbn [In] in Hin.
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <-; lia |]). destruct Hin. }
assert (HSV : forall (o : Z) (r : bv 5), In (o, r) odh_saved ->
  rdword (aview segs (w_H W) (ms_mem ms1)) (spZ regs + o) = Some (bv_unsigned (YK11.getr regs r))).
{ intros o r Hin. unfold odh_saved in Hin.
  apply (YF0x.val_mem_rdword (w_H W) (ms_mem ms1) (spZ regs + o) (bv_unsigned (YK11.getr regs r))
    ltac:(odh_u64 (YK11.getr regs r))).
  apply (can_field_of_region (odh_E regs) _ 2 (spZ regs) _ (-160) 0 (-160) 0 o 8%N
    (SOff (Z.to_nat (bv_unsigned r)) 0) (bv_unsigned (YK11.getr regs r)) HRsk Usp);
  [ cbn [In] in Hin |- *; repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <-;
      repeat (first [left; reflexivity | right]) |]); destruct Hin
  | cbn [sv_denot]; rewrite (odh_ew_reg regs (Z.to_nat (bv_unsigned r)) r ltac:(rewrite Z2Nat.id;
      [reflexivity | apply bv_unsigned_in_range])), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
  | cbn; odh_u64 (YK11.getr regs r)
  | cbn; lia ]. }
clear HRsk.
(* ---- +0x074: the class-2 stack malloc, at the pc the statement's premise names ---- *)
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transportb_sigma TB___asan_stack_malloc_2)) mm rom)
    mdx) Q) end.
rewrite <- HPCS.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (@YK11.mkst _ ?rg _ ?mm _) ?mdx) _ =>
  eapply (gx_stack_malloc_at (SK := tfib_sink_head) segs B LAWS transportb_segs_low SMP ONDATA_CID ASM
    ltac:(unfold ONDATA_CID; lia) TG.G_HARNESS_B W rg mm STK sp0 FP ly S W0 mem0 md0 own lyc Sc mdx k (sp1 - sp0)
    (Z_to_bv 64 (BASE + 30752)) HJ) end.
  - unfold spZ at 1. rewrite R2, unsigned_lit_small by lia. lia.
  - rewrite Zminus_mod, Hsp1al16, Hsp0a. reflexivity.
  - lia.
  - lia.
  - exact R3.
  - exact R4.
  - exact R1.
  - apply (ret_ok_codeptr_v (PI := PI_transportb)); [lia | reflexivity].
  - lia. }
cbv beta.
intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & pos & -> & HJ2 & HP2 & Ha0 & Eab2 & Hfrs2 & Hnev2
  & Hset2 & Hz & Hflag & Hfpres & HK1).
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HAR2.
assert (Hin2 : In (ONDATA_CID, pos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ ONDATA_CID pos HAR2 Hin2) as (HFal & HFapp & HFb & HFsh).
destruct (frames_bounds segs B LAWS _ _ _ _ _ ONDATA_CID pos HAR2 Hin2) as (HF0 & HFc & _).
destruct (dkg_frame_al64 segs B _ _ _ _ _ ONDATA_CID pos HAR2 Hin2) as (HF64 & _ & _).
change (fs_frame_bytes ONDATA_CID / 8) with 32 in HFsh.
change (fs_frame_bytes ONDATA_CID) with 256 in HFb, HFc, HFapp, Hz, Hflag, Hfpres, HFsh.
set (F := frame_addr lyc ONDATA_CID pos) in *.
(* the thirteen saved words, kept by the class-2 call *)
assert (HSV2 : forall (o : Z) (r : bv 5), In (o, r) odh_saved ->
  rdword (aview segs (w_H W) mem2) (spZ regs + o) = Some (bv_unsigned (YK11.getr regs r))).
{ intros o r Hin. pose proof (HSVo o r Hin) as Ho.
  rewrite <- (HSV o r Hin). unfold rdword.
  rewrite !(proj1 HK1) by lia. reflexivity. }
assert (Q2 : YK11.getr regs2 2 = Z_to_bv 64 sp1)
  by (transitivity (YK11.getr (ms_regs ms1) 2); [exact (HP2 2 ltac:(unfold acallee_saved; lia)) | exact R2]).
assert (Q3 : YK11.getr regs2 3 = w64 (as_gp B))
  by (transitivity (YK11.getr (ms_regs ms1) 3); [exact (HP2 3 ltac:(unfold acallee_saved; lia)) | exact R3]).
assert (Q4 : YK11.getr regs2 4 = w64 (as_tp B))
  by (transitivity (YK11.getr (ms_regs ms1) 4); [exact (HP2 4 ltac:(unfold acallee_saved; lia)) | exact R4]).
assert (Q8 : YK11.getr regs2 8 = w64 (spZ regs))
  by (transitivity (YK11.getr (ms_regs ms1) 8); [exact (HP2 8 ltac:(unfold acallee_saved; lia)) | exact R8]).
assert (Q9 : YK11.getr regs2 9 = Z_to_bv 64 sp1)
  by (transitivity (YK11.getr (ms_regs ms1) 9); [exact (HP2 9 ltac:(unfold acallee_saved; lia)) | exact R9]).
assert (Q19 : YK11.getr regs2 19 = w64 ONDATA_S)
  by (transitivity (YK11.getr (ms_regs ms1) 19); [exact (HP2 19 ltac:(unfold acallee_saved; lia)) | exact R19]).
assert (Q20 : YK11.getr regs2 20 = w64 fp)
  by (transitivity (YK11.getr (ms_regs ms1) 20); [exact (HP2 20 ltac:(unfold acallee_saved; lia)) | exact R20]).
assert (Q23 : YK11.getr regs2 23 = w64 now)
  by (transitivity (YK11.getr (ms_regs ms1) 23); [exact (HP2 23 ltac:(unfold acallee_saved; lia)) | exact R23]).
assert (Q27 : YK11.getr regs2 27 = w64 SHADOW_OFF)
  by (transitivity (YK11.getr (ms_regs ms1) 27); [exact (HP2 27 ltac:(unfold acallee_saved; lia)) | exact R27]).
clear HS.
set (memT := ms_mem ms1) in *. set (regsT := ms_regs ms1) in *. clearbody memT regsT. clear ms1.
(* ---- run 2a, +0x078 .. +0x0e0: the frame taken, the frame word at s1 + 48, the frame's 24-byte header, s9 ---- *)
pose proof (odh_entry2 W regs2 mem2 F sp1 Q2 Q9 Ha0 Q27 ltac:(lia) Hsp1al ltac:(lia) ltac:(lia) HF64 ltac:(lia)
  ltac:(intros a Ha; apply (odh_jpres _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2); lia)
  ltac:(intros a Ha; apply Hfpres; lia)) as HS.
repeat match goal with H : img_env _ _ _ |- _ => clear H end.
assert (HEI : img_env VAL A_LIM (odh_E regs2)) by apply odh_env_img.
clear SHOK.
assert (SHOK : sh_ok segs (SOff 32 0) (@nil shent) (odh_E regs2) (mrestrict (w_H W) mem2)) by constructor.
assert (U9a : bv_unsigned (ew (odh_E regs2) 9) = sp1)
  by (rewrite (odh_ew_reg regs2 9 9%bv eq_refl), Q9; apply unsigned_lit_small; lia).
assert (U10' : bv_unsigned (ew (odh_E regs2) 10) = F)
  by (rewrite (odh_ew_reg regs2 10 10%bv eq_refl), Ha0; apply unsigned_lit_small; lia).
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + ODH_C1)) mem2
    (YK11.seg_rom segs)) md2) Q) end.
clear HJ. rename HJ2 into HJ.
paj_run_tok RUN HS HJ SHOK ODH_B0.
{ odh_awr_rs.
  apply awr_ok_x_cons;
  [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U9a in Ha;
    left; split; [unfold awr_byte; left; lia | lia] |].
  eapply (awr_ok_x_cons_own _ _ _ _ _ _ _ _ _ _ _ _ ONDATA_CID pos); [left; reflexivity | | apply awr_ok_x_nil].
  intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U10' in Ha.
  left. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes ONDATA_CID) with 256.
  change (frame_addr lyc ONDATA_CID pos) with F. lia. }
rename HF into HF2a, HFr into HFr2a, HG into HG2a. odh_msname HS ms3.
(* What the call keeps from memc to mem2 (the memory the stack malloc returned). *)
assert (Hwin : forall a, spZ regs - ONDATA_STK <= a < spZ regs -> apresent (w_H W) memc a)
  by (intros a Ha; apply Hpres0; lia).
assert (KT : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 160 <= a < spZ regs) ->
  aview segs (w_H W) memT a = aview segs (w_H W) memc a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ (fun x => spZ regs - 160 <= x < spZ regs) HFr1); [| exact Ha | exact Hn].
  intros b0 wlo whi x Hin Hx. odh_windows Hin Hx; first [rewrite ?Usp in Hx; lia | destruct Hin]. }
assert (Kg1 : acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W memT (spZ regs - ONDATA_STK) (spZ regs)
  (fun _ => False)).
{ apply (dk_kept_step_g segs B LAWS transportb_segs_low TG.G_HARNESS_B lyc Sc W memc mdc memc memT
    (spZ regs - ONDATA_STK) (spZ regs) (fun _ => False) (fun x => spZ regs - 160 <= x < spZ regs) HAR).
  - apply dk_kept_refl_g. exact Hwin.
  - intros a Ha Hn. exact (KT a Ha Hn).
  - intros a Ha. exact (apresent_grows _ _ _ a HG1 Ha).
  - intros a Ha _. lia.
  - intros bb m i Hb Hi Hzs. exfalso.
    destruct (al_blocks _ _ LAWS lyc Sc W memc mdc bb m HAR Hb) as (_ & H4096 & Hbc & _). lia.
  - intros a Ha Hi _ _ _. pose proof (transportb_segs_low a Hi) as Hl. unfold kLowMemEnd in *. lia.
  - intros cid pos0 a Hin Hr Ha. exfalso.
    destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos0 HAR Hin) as (F4096 & Fce & _).
    pose proof (fs_frame_bytes_nonneg cid) as Hfs.
    destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [lia|].
    pose proof (shadow_range_end (frame_addr lyc cid pos0) (fs_frame_bytes cid) Hfs) as Hse.
    assert (Hd : (frame_addr lyc cid pos0 + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
    unfold shadow_addr, SHADOW_OFF in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia. }
rewrite Zplus_minus in HK1.
assert (Kg2 : acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W mem2 (spZ regs - ONDATA_STK) (spZ regs)
  (fun _ => False)).
{ apply (dk_kept_trans_g segs B TG.G_HARNESS_B lyc Sc W memc W memT W mem2 (spZ regs - ONDATA_STK) (spZ regs)
    (sp1 - ESTACK) sp1 (fun _ => False) (fun _ => False)); [lia | lia | exact Kg1 | | lia | lia | tauto].
  apply acall_kept_g_of. exact HK1. }
assert (GK2 : gx_kept segs TG.G_HARNESS_B W memc W mem2).
{ apply (gx_kept_trans segs TG.G_HARNESS_B W memc W memT W mem2).
  - intros a Ha. pose proof (inG_low segs B transportb_segs_low TG.G_HARNESS_B a HGX Ha) as Hl.
    unfold kLowMemEnd in Hl. apply KT; lia.
  - exact (gx_kept_of_acall_kept segs B TG.G_HARNESS_B lyc Sc W memT W mem2 _ _ _ HGX HGNE HK1). }
clear KT Kg1 HF1 HFr1 HG1.
(* the registers at +0x0e4 *)
assert (EF10 : ew (odh_E regs2) 10 = Z_to_bv 64 F) by (rewrite (odh_ew_reg regs2 10 10%bv eq_refl); exact Ha0).
assert (EF27 : ew (odh_E regs2) 27 = Z_to_bv 64 SHADOW_OFF) by (rewrite (odh_ew_reg regs2 27 27%bv eq_refl); exact Q27).
assert (HFbv : 0 <= F < 2 ^ 64) by lia.
assert (Hfpbv : 0 <= fp /\ fp + 64 <= 2 ^ 47) by lia.
assert (HFd : 0 <= F / 8 /\ F / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
assert (HfD : 0 <= (fp + 20) / 8 /\ (fp + 20) / 8 < 2 ^ 44)
  by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
odh_reg HS (25%bv : bv 5) (Z_to_bv 64 (SHADOW_OFF + F / 8)) T25
  ltac:(exact (can_denot_shadow (odh_E regs2) 10 27 F SHADOW_OFF EF10 EF27 HFbv
               ltac:(unfold SHADOW_OFF; lia) ltac:(unfold SHADOW_OFF; lia))).
odh_kreg HS regs2 (2%bv : bv 5) 2%nat Q2 T2. odh_kreg HS regs2 (3%bv : bv 5) 3%nat Q3 T3.
odh_kreg HS regs2 (4%bv : bv 5) 4%nat Q4 T4. odh_kreg HS regs2 (8%bv : bv 5) 8%nat Q8 T8.
odh_kreg HS regs2 (9%bv : bv 5) 9%nat Q9 T9. odh_kreg HS regs2 (19%bv : bv 5) 19%nat Q19 T19.
odh_kreg HS regs2 (20%bv : bv 5) 20%nat Q20 T20. odh_kreg HS regs2 (23%bv : bv 5) 23%nat Q23 T23.
odh_kreg HS regs2 (27%bv : bv 5) 27%nat Q27 T27.
odh_reg HS (22%bv : bv 5) (w64 F) T22
  ltac:(cbn [sv_denot]; rewrite (odh_ew_reg regs2 10 10%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Ha0).
odh_reg HS (26%bv : bv 5) (w64 F) T26
  ltac:(cbn [sv_denot]; rewrite (odh_ew_reg regs2 10 10%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Ha0).
(* run 2a wrote the slot s1 + 48 and the frame's header only *)
assert (K2a : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 + 48 <= a < sp1 + 56 \/ F <= a < F + 24) ->
  aview segs (w_H W) (ms_mem ms3) a = aview segs (w_H W) mem2 a).
{ intros a Ha Hn.
  apply (kept_of_frame _ _ _ _ _ (fun x => sp1 + 48 <= x < sp1 + 56 \/ F <= x < F + 24) HFr2a);
    [| exact Ha | exact Hn].
  intros b0 wlo whi x Hin Hx. odh_windows Hin Hx; first [rewrite ?U9a, ?U10' in Hx; lia | destruct Hin]. }
pose proof HG2a as G2a. clear HF2a HFr2a HG2a.
(* ---- run 2b, +0x0e4 .. +0x144: the frame's shadow bytes 0 .. 19, the alignment check of f, s5, s2 ---- *)
pmkst HS. clear HS.
pose proof (odh_entry3 W (ms_regs ms3) (ms_mem ms3) (SHADOW_OFF + F / 8) fp T20 T25
  ltac:(unfold SHADOW_OFF; lia) ltac:(unfold SHADOW_OFF; lia) ltac:(lia) Hfp8
  ltac:(intros a Ha; apply (apresent_grows _ _ _ a G2a);
        replace a with (shadow_addr F + (a - shadow_addr F)) by (unfold shadow_addr; lia);
        exact (proj1 (HFsh (a - shadow_addr F) ltac:(unfold shadow_addr; lia))))) as HS.
repeat match goal with H : img_env _ _ _ |- _ => clear H end.
assert (HEI : img_env VAL A_LIM (odh_E (ms_regs ms3))) by apply odh_env_img.
clear SHOK.
assert (SHOK : sh_ok segs (SOff 32 0) (@nil shent) (odh_E (ms_regs ms3)) (mrestrict (w_H W) (ms_mem ms3)))
  by constructor.
assert (U25 : bv_unsigned (ew (odh_E (ms_regs ms3)) 25) = SHADOW_OFF + F / 8)
  by (rewrite (odh_ew_reg (ms_regs ms3) 25 25%bv eq_refl), T25; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
lazymatch goal with |- SRr _ ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + ODH_C2)) mm rom) mdx) Q) end.
paj_run_to_tok RUNTO HS HJ SHOK ODH_B0 ODH_C3.
{ odh_awr_rs.
  eapply (awr_ok_x_cons_own _ _ _ _ _ _ _ _ _ _ _ _ ONDATA_CID pos); [left; reflexivity | | apply awr_ok_x_nil].
  intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U25 in Ha.
  right. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes ONDATA_CID / 8) with 32.
  change (frame_addr lyc ONDATA_CID pos) with F. unfold shadow_addr. lia. }
rename HF into HF2b, HFr into HFr2b, HG into HG2b. odh_msname HS ms4.
(* run 2b wrote the frame's shadow bytes 0 .. 19 only *)
assert (K2b : forall a, 0 <= a < 2 ^ 64 -> ~ (SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 20) ->
  aview segs (w_H W) (ms_mem ms4) a = aview segs (w_H W) (ms_mem ms3) a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ (fun x => SHADOW_OFF + F / 8 <= x < SHADOW_OFF + F / 8 + 20) HFr2b);
    [| exact Ha | exact Hn].
  intros b0 wlo whi x Hin Hx. odh_windows Hin Hx; first [rewrite ?U25 in Hx; lia | destruct Hin]. }
pose proof HG2b as G2b. clear HF2b HFr2b HG2b.
(* the registers at +0x148 *)
odh_kreg HS (ms_regs ms3) (2%bv : bv 5) 2%nat T2 V2. odh_kreg HS (ms_regs ms3) (3%bv : bv 5) 3%nat T3 V3.
odh_kreg HS (ms_regs ms3) (4%bv : bv 5) 4%nat T4 V4. odh_kreg HS (ms_regs ms3) (8%bv : bv 5) 8%nat T8 V8.
odh_kreg HS (ms_regs ms3) (9%bv : bv 5) 9%nat T9 V9. odh_kreg HS (ms_regs ms3) (19%bv : bv 5) 19%nat T19 V19.
odh_kreg HS (ms_regs ms3) (20%bv : bv 5) 20%nat T20 V20.
odh_kreg HS (ms_regs ms3) (22%bv : bv 5) 22%nat T22 V22. odh_kreg HS (ms_regs ms3) (23%bv : bv 5) 23%nat T23 V23.
odh_kreg HS (ms_regs ms3) (25%bv : bv 5) 25%nat T25 V25. odh_kreg HS (ms_regs ms3) (26%bv : bv 5) 26%nat T26 V26.
odh_kreg HS (ms_regs ms3) (27%bv : bv 5) 27%nat T27 V27.
assert (EV20 : ew (odh_E (ms_regs ms3)) 20 = Z_to_bv 64 fp)
  by (rewrite (odh_ew_reg (ms_regs ms3) 20 20%bv eq_refl); exact T20).
assert (EV27 : ew (odh_E (ms_regs ms3)) 27 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite (odh_ew_reg (ms_regs ms3) 27 27%bv eq_refl); exact T27).
odh_reg HS (21%bv : bv 5) (w64 (fp + 20)) V21
  ltac:(cbn [sv_denot]; rewrite (odh_ew_reg (ms_regs ms3) 20 20%bv eq_refl), T20; unfold w64;
        rewrite (unsigned_lit_small fp) by lia; reflexivity).
odh_reg HS (18%bv : bv 5) (Z_to_bv 64 (SHADOW_OFF + (fp + 20) / 8)) V18
  ltac:(exact (odh_denot_shadow_off (odh_E (ms_regs ms3)) 20 27 fp 20 SHADOW_OFF EV20 EV27 ltac:(lia) ltac:(lia)
               ltac:(unfold SHADOW_OFF; lia) ltac:(unfold SHADOW_OFF; lia))).
(* what the call keeps from memc to the memory at +0x148, over the header, the frame's shadow bytes and the slot *)
assert (KF3 : forall a, 0 <= a < 2 ^ 64 ->
  ~ (F <= a < F + 24 \/ SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 20 \/ sp1 + 48 <= a < sp1 + 56) ->
  aview segs (w_H W) (ms_mem ms4) a = aview segs (w_H W) mem2 a).
{ intros a Ha Hn.
  rewrite (K2b a Ha ltac:(intros X; apply Hn; tauto)).
  exact (K2a a Ha ltac:(intros X; apply Hn; tauto)). }
assert (GF3 : forall a, apresent (w_H W) mem2 a -> apresent (w_H W) (ms_mem ms4) a).
{ intros a Ha. apply (apresent_grows _ _ _ a G2b). exact (apresent_grows _ _ _ a G2a Ha). }
assert (KG3 : acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W (ms_mem ms4) (spZ regs - ONDATA_STK) (spZ regs)
  (fun _ => False)).
{ apply (dk_kept_own_g segs B LAWS transportb_segs_low TG.G_HARNESS_B lyc Sc S2 W memc mdc mem2 md2 mem2
    (ms_mem ms4) (spZ regs - ONDATA_STK) (spZ regs) ONDATA_CID pos F (flag_addr lyc ONDATA_CID pos) (fun _ => False)
    (fun a => F <= a < F + 24 \/ SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 20 \/ sp1 + 48 <= a < sp1 + 56)
    HGX HAR HAR2 Hfrs2 Eab2 eq_refl eq_refl FFL); [lia | lia | intros a [] | | exact Kg2 | | exact GF3].
  - intros a [X | [X | X]].
    + right; right; left. unfold dkg_nf. left. change (fs_frame_bytes ONDATA_CID) with 256. lia.
    + right; right; left. unfold dkg_nf. right; left. change (fs_frame_bytes ONDATA_CID / 8) with 32.
      try unfold shadow_addr. lia.
    + left. lia.
  - intros a Ha Hn. exact (KF3 a Ha Hn). }
(* the shadow byte of fp + 20 and the four bytes at fp + 20, at +0x148 *)
assert (HRA3 : range_addressable (aview segs (w_H W) (ms_mem ms4)) SHADOW_OFF fp 64)
  by exact (dk_kept_ra_g segs B LAWS TG.G_HARNESS_B lyc Sc W memc mdc (ms_mem ms4) _ _ _ cf pf fp 64 HAR KG3 Hinf
    Hfl Hfh (fun x _ H => H) (proj1 (proj2 Hrdf))).
pose proof (odh_sh0 _ fp Hfp8 HRA3) as Hsb.
assert (Hval : val_mem segs (mrestrict (w_H W) (ms_mem ms4)) (fp + 20) 4 (DSpec.fr_send b)).
{ apply odh_val_of_view. intros kk Hkk.
  rewrite (dk_kept_frame_byte_g segs B TG.G_HARNESS_B lyc Sc W memc (ms_mem ms4) _ _ _ cf pf (fp + 20 + Z.of_nat kk)
    KG3 Hinf ltac:(lia) (fun H => H)).
  replace (fp + 20 + Z.of_nat kk) with (fp + Z.of_nat (20 + kk)) by lia.
  rewrite (odh_garr8_view (w_H W) memc fp _ (20 + kk) Hgf
    ltac:(pose proof (odh_ffb_len buf b fj Hcode Hfj); lia)).
  f_equal. exact (odh_ffb_byte buf b fj kk Hcode Hfj Hkk). }
(* ---- run 2c, +0x148 .. +0x16c: `lb a0, 0(s2)`, `bnez a0`, `lw a2, 0(s5)`, s8, a1, a0, a3, a4, up to
   `jal send_control` ---- *)
pmkst HS. clear HS SHOK.
pose proof (odh_entry4 W (ms_regs ms4) (ms_mem ms4) fp (DSpec.fr_send b) V18 V21 Hfapp64 HfR Hsb Hval) as HS.
repeat match goal with H : img_env _ _ _ |- _ => clear H end.
assert (HEI : img_env VAL A_LIM (odh_E4 (ms_regs ms4) (DSpec.fr_send b))) by (unfold odh_E4; apply Eimg_env).
assert (SHOK : sh_ok segs (SOff 32 0) (@nil shent) (odh_E4 (ms_regs ms4) (DSpec.fr_send b))
  (mrestrict (w_H W) (ms_mem ms4))) by constructor.
assert (EE4 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r ->
  ew (odh_E4 (ms_regs ms4) (DSpec.fr_send b)) n = YK11.getr (ms_regs ms4) r)
  by (intros n r Hn; unfold odh_E4; apply can_ew_Eimg_Ereg_nat; exact Hn).
lazymatch goal with |- SRr _ ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + ODH_C3)) mm rom) mdx) Q) end.
paj_run_tok RUN HS HJ SHOK ODH_B0.
{ odh_awr_rs.
  apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |].
  apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |].
  apply awr_ok_x_nil. }
rename HF into HF2c, HFr into HFr2c, HG into HG2c. odh_msname HS ms5.
(* run 2c wrote no byte *)
assert (K2c : forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W) (ms_mem ms5) a = aview segs (w_H W) (ms_mem ms4) a).
{ intros a Ha. apply (kept_of_frame _ _ _ _ _ (fun _ => False) HFr2c); [| exact Ha | exact (fun X => X)].
  intros b0 wlo whi x Hin Hx. cbv beta. odh_windows Hin Hx; first [lia | destruct Hin]. }
(* the registers at send_control's entry *)
odh_kreg4 HS EE4 (2%bv : bv 5) 2%nat V2 X2. odh_kreg4 HS EE4 (3%bv : bv 5) 3%nat V3 X3.
odh_kreg4 HS EE4 (4%bv : bv 5) 4%nat V4 X4. odh_kreg4 HS EE4 (8%bv : bv 5) 8%nat V8 X8.
odh_kreg4 HS EE4 (9%bv : bv 5) 9%nat V9 X9. odh_kreg4 HS EE4 (18%bv : bv 5) 18%nat V18 X18.
odh_kreg4 HS EE4 (19%bv : bv 5) 19%nat V19 X19. odh_kreg4 HS EE4 (20%bv : bv 5) 20%nat V20 X20.
odh_kreg4 HS EE4 (21%bv : bv 5) 21%nat V21 X21. odh_kreg4 HS EE4 (22%bv : bv 5) 22%nat V22 X22.
odh_kreg4 HS EE4 (23%bv : bv 5) 23%nat V23 X23. odh_kreg4 HS EE4 (25%bv : bv 5) 25%nat V25 X25.
odh_kreg4 HS EE4 (26%bv : bv 5) 26%nat V26 X26. odh_kreg4 HS EE4 (27%bv : bv 5) 27%nat V27 X27.
odh_reg HS (10%bv : bv 5) (w64 ONDATA_S) X10
  ltac:(cbn [sv_denot]; rewrite (EE4 19%nat 19%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact V19).
odh_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 31004)) X1 ltac:(apply codeptr_val; exact HEI).
odh_reg HS (11%bv : bv 5) (w64 0xa0) X11 ltac:(reflexivity).
odh_reg HS (13%bv : bv 5) (w64 0) X13 ltac:(reflexivity).
odh_reg HS (14%bv : bv 5) (w64 0) X14 ltac:(reflexivity).
assert (E33 : ew (odh_E4 (ms_regs ms4) (DSpec.fr_send b)) 33 = Z_to_bv 64 (DSpec.fr_send b))
  by (unfold odh_E4; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 1)).
odh_reg HS (12%bv : bv 5) (w64 (bv_swrap 32 (DSpec.fr_send b))) X12
  ltac:(exact (odh_sext _ (DSpec.fr_send b) HfR E33)).
odh_reg HS (24%bv : bv 5) (w64 (ONDATA_S + 18160)) X24
  ltac:(cbn [sv_denot]; rewrite (EE4 19%nat 19%bv eq_refl), V19; unfold w64;
        rewrite (unsigned_lit_small ONDATA_S) by (rewrite CS; lia); reflexivity).
(* ---- the facts the cut carries, at the memory of send_control's entry ---- *)
set (m5 := ms_mem ms5) in *.
(* every byte outside the three written ranges is the one the stack malloc left *)
assert (KF5 : forall a, 0 <= a < 2 ^ 64 ->
  ~ (F <= a < F + 24 \/ SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 20 \/ sp1 + 48 <= a < sp1 + 56) ->
  aview segs (w_H W) m5 a = aview segs (w_H W) mem2 a).
{ intros a Ha Hn. rewrite (K2c a Ha). exact (KF3 a Ha Hn). }
assert (GF5 : forall a, apresent (w_H W) mem2 a -> apresent (w_H W) m5 a).
{ intros a Ha. apply (apresent_grows _ _ _ a HG2c). exact (GF3 a Ha). }
assert (NGF : forall a, F <= a < F + 256 -> ~ inG TG.G_HARNESS_B a).
{ intros a Ha Hg. destruct (HGX a Hg) as [Hi _].
  exact (frm_img segs B LAWS _ _ _ _ _ ONDATA_CID pos a HAR2 Hin2
    ltac:(change (fs_frame_bytes ONDATA_CID) with 256; lia) Hi). }
(* the world relation at Bw: no byte of G is written *)
assert (Htw5 : tw_at TMAP_B (aview segs (w_H W) m5) Bw).
{ apply (tw_kept_GB (aview segs (w_H W) memc)); [exact Htw|]. intros b0 n i Hin Hi.
  assert (Hg : inG TG.G_HARNESS_B (b0 + i)).
  { unfold inG. apply Exists_exists. exists (b0, n). split; [exact Hin | unfold in_zr; cbn [fst snd]; lia]. }
  pose proof (inG_low segs B transportb_segs_low TG.G_HARNESS_B _ HGX Hg) as Hl. unfold kLowMemEnd in Hl.
  rewrite (KF5 (b0 + i) ltac:(lia)
    ltac:(intros [X | [X | X]]; [exact (NGF (b0 + i) ltac:(lia) Hg) | unfold SHADOW_OFF in X; lia | lia])).
  exact (GK2 (b0 + i) Hg). }
(* what the call keeps, at m5 *)
assert (KG5 : acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W m5 (spZ regs - ONDATA_STK) (spZ regs)
  (ondata_wr Bw b)).
{ apply (acall_kept_g_weaken segs B TG.G_HARNESS_B lyc Sc W memc W m5 (spZ regs - ONDATA_STK) (spZ regs)
    (fun _ => False) (ondata_wr Bw b)); [tauto|].
  apply (dk_kept_own_g segs B LAWS transportb_segs_low TG.G_HARNESS_B lyc Sc S2 W memc mdc mem2 md2 mem2 m5
    (spZ regs - ONDATA_STK) (spZ regs) ONDATA_CID pos F (flag_addr lyc ONDATA_CID pos) (fun _ => False)
    (fun a => F <= a < F + 24 \/ SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 20 \/ sp1 + 48 <= a < sp1 + 56)
    HGX HAR HAR2 Hfrs2 Eab2 eq_refl eq_refl FFL); [lia | lia | intros a [] | | exact Kg2 | | exact GF5].
  - intros a [X | [X | X]].
    + right; right; left. unfold dkg_nf. left. change (fs_frame_bytes ONDATA_CID) with 256. lia.
    + right; right; left. unfold dkg_nf. right; left. change (fs_frame_bytes ONDATA_CID / 8) with 32.
      try unfold shadow_addr. lia.
    + left. lia.
  - intros a Ha Hn. exact (KF5 a Ha Hn). }
(* the thirteen saved words, at m5 *)
assert (HSV5 : forall (o : Z) (r : bv 5), In (o, r) odh_saved ->
  rdword (aview segs (w_H W) m5) (spZ regs + o) = Some (bv_unsigned (YK11.getr regs r))).
{ intros o r Hin. pose proof (HSVo o r Hin) as Ho. rewrite <- (HSV2 o r Hin).
  apply YCbq.rdword_ext. intros i Hi. apply KF5; [lia|].
  intros [X | [X | X]]; [lia | unfold SHADOW_OFF in X; lia | lia]. }
assert (HFW5 : Forall (fun o : Z * Z => rdword (aview segs (w_H W) m5) (spZ regs - fst o) =
    Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) OD_SAVED).
{ unfold OD_SAVED. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
  match goal with |- rdword _ (spZ regs - ?o) = Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 ?r))) =>
    replace (spZ regs - o) with (spZ regs + - o) by ring;
    apply (HSV5 (- o) (Z_to_bv 5 r)); unfold odh_saved; cbn [In];
    repeat (first [left; apply (f_equal2 pair); [reflexivity | apply bv_eq; reflexivity] | right]) end. }
(* the frame's last word, at m5 *)
assert (HFL5 : rdword (aview segs (w_H W) m5) (F + OD_FBYTES - 8) = Some (flag_addr lyc ONDATA_CID pos)).
{ rewrite <- Hflag. unfold OD_FBYTES. apply YCbq.rdword_ext. intros i Hi. apply KF5; [lia|].
  intros [X | [X | X]]; [lia | | lia].
  destruct HFapp as (_ & [HL | [HH _]]); unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *; lia. }
(* the class-2 frame changed the allocator state's st_fs only *)
assert (HMO : mo_le MT Sc S2 0).
{ destruct Hset2 as (f2 & Ef2). rewrite Ef2. apply (mo_le_set_fs_r MT MTF). exact (mo_le_refl MT MTL Sc). }
assert (EVv : ONDATA_EV = ltac:(let v := eval vm_compute in ONDATA_EV in exact v)) by reflexivity.
lazymatch type of HJ with context [@W_journalG.ajournal_gx ?r ?sk ?sg ?bq ?g ?xo ?o ?stk ?sp ?fpq ?l ?s ?w0 ?m0 ?d0
    ?ow ?l' ?s' ?w' ?m' ?md' ?kk] => set (md5 := md') in * end.
assert (CUR5 : od_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b Bw pos F lyc S2 W m5 md5 0).
{ refine (conj _ (conj _ (conj Hfrs2 (conj _ (conj eq_refl (conj HMO (conj KG5 (conj HFW5 HFL5)))))))).
  - rewrite Z.add_0_r. exact HJ.
  - rewrite EVv. lia.
  - rewrite Eab2. apply Permutation_refl. }
(* what the head fixed *)
assert (HFIX : od_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F).
{ refine (conj HPRE (conj HTFG (conj _ (conj eq_refl (conj HF0 (conj HF64 (conj HFc HFapp))))))).
  unfold sp1, ONDATA_FRAME. replace (spZ regs - 160) with (spZ regs + -160) by lia. reflexivity. }
(* send_control's entry: the cut od_sc_at *)
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transportb_sigma TB_send_control)) mm rom) mdx) Q) end.
apply (SC LAWS0 CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F
  S2 m5 md5 (ms_regs ms5) HFIX).
- exact (conj CUR5 (conj Eab2 Htw5)).
- unfold od_regs_sc, od_regs_s, od_regs_rel.
  refine (conj (conj (conj X2 (conj _ (conj _ (conj X8 (conj X9 (conj X25 X26))))))
    (conj X18 (conj X19 (conj X20 (conj X21 X27))))) (conj _ (conj X22 (conj X23 (conj X24
    (conj X10 (conj X11 (conj X12 (conj X13 X14))))))))).
  + rewrite X3. symmetry. exact Hgp.
  + rewrite X4. symmetry. exact Htp.
  + rewrite X1. reflexivity.
Qed.
End sh.

(* The head piece of the walk of on_data (on_data_seg_cut.v od_head_stmt), at every machine, run ceiling, record and
   meter. *)
Theorem od_head : forall fx rc B MT, @od_head_stmt fx rc B MT.
Proof. intros fx rc B MT. exact (@odh_holds fx rc B MT). Qed.

Print Assumptions od_head.
