(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/AF0x.v, with its module paths and module names changed; 708 of its 766 lines of code are new or changed and 514 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/B/Prog/io_send_seg_entry.v, with its module paths and module names changed; 1303 of its 1414 lines of code are new or changed and 655 lines of the source are left out. *)
(* io_send_seg_e2a: the E2 arm of the image-B walk of io_send (fuzz_transport.asan-ubsan 41113a03c82f, entry
   0x82ffc = TImgB.v ti_io_send timg_B; the statement of record is lib/B/Prog/io_send_cg.v
   transport_io_send_cg_holds_stmt), 0x83110 .. 0x83144 = transportb_text + IOS_E2ARM .. + IOS_AT 0x148. It proves
   io_send_seg_cut.v ios_e2_arm_stmt (ios_e2_arm, end of file).

   The code (io_send_cg.v header lines 107-111; listing iosend-B-listing.txt), with sp = the walk's sp (the entry sp
   less IOSEND_FRAME = 160):
     0x83110            `PCall` check_state_wake (0x84628), return address 0x83114; the call takes no argument;
     0x83114 - 0x83118  a0 = sp + 8 (the struct spec_frame f); `PCall` check_latest_control (0x84490), return
                        address 0x8311c;
     0x8311c - 0x83128  a0 = the %hi of object 55, a2 = GOT.e2 (PLdHi of object 29 = GOT + 196, 4 bytes signed),
                        a1 = a2 + 1 (addiw), `blt a1, a2` to the trap word 0x83358 (UBSan's signed-overflow check);
     0x8312c - 0x8313c  a2 = f.send (the 4-byte signed load at sp + 40), a1 stored back at GOT.e2 (`sw a1, -248(a0)`),
                        a0 = the %hi of object 56, a1 = s3 & 1, a2 stored at g_last_counter (`sw a2, -884(a0)`);
     0x83140 - 0x83144  a1 = 0 goes to 0x832c0 (= transportb_text + IOS_FLY), else `j` 0x83310 (= + IOS_EPI).

   How (the image-A twin lib/A/Prog/io_send_seg_e2a.v, with the helpers it took from image A's io_send_seg_e2.v /
   ack.v / csf.v / tail.v copied here with the prefix ie2a_ at image B's names):
   - the two LEAF calls (ie2a_calls): the leaf form of TransportGCg.v gx_call_leaf and DgnTransportBLeafb.v
     decode_leafb_journal (ie2a_leaf_call with ie2a_csw_leaf for check_state_wake, whose one footprint row beyond its
     frame is M.foreign; ie2a_call_clc for check_latest_control from the struct at sp + 8). Each leaf keeps the world
     and every byte outside its own ESTACK window, so the cut survives it (ie2a_keep over [sp - ESTACK, sp)).
   - the counter, its overflow branch and the two stores (ie2a_tail): one symbolic state (ie2a_state: f.send at
     sp + 40, GOT.e2 at object 29 with the %hi alias of the store, g_last_counter at -884 from the %hi of object 56);
     a run to the `blt`, whose branch to the trap word is refuted as in lib/B/Prog/m_set_cgW.v run 3a: the model's
     int_inc (GOT_e2 (ios_B0 Bw)) = Some e2 (io_send_segs.v ios_arm_e2) says GOT.e2 is not INT_MAX, so the addiw does
     not wrap and a1 = GOT.e2 + 1 > a2; a run to the `beq` that stores both words; the world after them is two
     io_send_seg_world.v ios_tw_step (GOT + 196 and g_last_counter, 4 bytes each), both bytes of iosend_wr
     (ios_wr_got_e2 / ios_wr_lastc), and the running kept fact is ie2a_kept_step.
   - the split on `s3 & 1` (ie2a_br_and1): s3 is the unsigned byte of g_fail_next the entry read, 0 or 1 by ios_fix,
     so the machine's test is the model's `truth (g_fail_next Bw)`; bit clear is the frame in flight
     (io_send_segs.v ios_arm_e2's second case), bit set the epilogue (its first case). *)
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
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c YO0f.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg CanKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TransportGRwB TransportGRunB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB m_set_cg io_send_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import check_sent_frame_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require
  DgnTransportBLeafb LeafCgKit AsanKA check_state_wake_c check_latest_control_c
  check_state_wake_cg check_latest_control_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import io_send_segs io_send_seg_frm.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import io_send_seg_cut io_send_seg_world.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec StrFun.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Mem Frame ExecF.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module BCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.AsanCells.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module SFun := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.StrFun.
Module LMem := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Mem.
Module LExecF := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.ExecF.
Module LCK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.LeafCgKit.
Module AKA := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.AsanKA.
Module LB := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.DgnTransportBLeafb.
Module CSW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_state_wake_c.
Module LLCc := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_latest_control_c.
Module LSW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_state_wake_cg.
Module LLC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_latest_control_cg.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* Values, bytes and registers                                         *)
(* ------------------------------------------------------------------ *)

(* A 32-bit value through the sign extension the stores write back: the byte a store writes is the byte of the
   value itself, since le_byte reads only the low 32 bits. *)
Lemma ie2a_swrap_mod : forall z, bv_swrap 32 z mod 2 ^ 32 = z mod 2 ^ 32.
Proof.
intros z. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
change (2 ^ Z.of_N 32) with 4294967296. change (4294967296 `div` 2) with 2147483648.
change (2 ^ 32) with 4294967296. rewrite Zminus_mod_idemp_l. f_equal. lia.
Qed.

Lemma ie2a_le_byte_swrap : forall v j, YO0f.le_byte (bv_swrap 32 v) 4 j = YO0f.le_byte v 4 j.
Proof.
intros v j. unfold YO0f.le_byte. change (8 * Z.of_nat 4) with 32. rewrite ie2a_swrap_mod. reflexivity.
Qed.

Lemma ie2a_bow : forall v j, (j < 4)%nat ->
  bv_unsigned (byte_of_word (Z_to_bv 64 v) (Z.of_nat j)) = YO0f.le_byte v 4 j.
Proof.
intros v j Hj. unfold byte_of_word, YO0f.le_byte. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 8) with (2 ^ 8). change (2 ^ Z.of_N 64) with (2 ^ 64). change (8 * Z.of_nat 4) with 32.
change 256 with (2 ^ 8).
apply Z.bits_inj'. intros m Hm.
destruct (Z_lt_le_dec m 8) as [Hl|Hl].
- rewrite !Z.mod_pow2_bits_low by lia. rewrite !Z.shiftr_spec by lia.
  rewrite !Z.mod_pow2_bits_low by lia. reflexivity.
- rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

(* The 4 bytes of the one chunk of a region, read through the view (image A's io_send_seg_ack.v iak_chunk_rd /
   iak_region_rd4). *)
Lemma ie2a_chunk_rd : forall (E : env) (H : word -> bool) (mm : word -> option byte) (base off : Z) (e : sv) (v : Z),
  YP09.chunk_ok tfibsegs E (mrestrict H mm) base (YP09.mkChunk off (CVal 4 e)) -> sv_denot E e = Z_to_bv 64 v ->
  forall j, (j < 4)%nat -> aview tfibsegs H mm (base + off + Z.of_nat j) = Some (YO0f.le_byte v 4 j).
Proof.
intros E H mm base off e v HC He j Hj. unfold YP09.chunk_ok in HC.
cbn [YP09.c_off YP09.c_val YP09.c_len YP09.cv_len] in HC.
destruct (HC (Z.of_nat j) ltac:(cbn; lia)) as (bt & Hb1 & Hb2). cbn [YP09.cbyte] in Hb1. rewrite He in Hb1.
injection Hb1 as <-.
change (aview tfibsegs H mm (base + off + Z.of_nat j))
  with (option_map (fun b : byte => bv_unsigned b) (YP09.mbyte tfibsegs (mrestrict H mm) (base + off + Z.of_nat j))).
rewrite Hb2. cbn [option_map]. f_equal. apply ie2a_bow. exact Hj.
Qed.

Lemma ie2a_region_rd4 : forall E (H : word -> bool) (mm : word -> option byte) n lo hi wlo whi off e v b,
  region_ok tfibsegs E (mrestrict H mm) (YP09.mkRegion (Some n) lo hi wlo whi [YP09.mkChunk off (CVal 4 e)]) ->
  bv_unsigned (ew E n) = b -> sv_denot E e = Z_to_bv 64 v ->
  forall j, (j < 4)%nat -> aview tfibsegs H mm (b + off + Z.of_nat j) = Some (YO0f.le_byte v 4 j).
Proof.
  intros E H mm n lo hi wlo whi off e v b (_ & _ & _ & HC) Hb Hv.
  cbn [YP09.r_base YP09.r_chunks base_val] in HC. rewrite Hb in HC. apply Forall_inv in HC.
  exact (ie2a_chunk_rd E H mm b off e v HC Hv).
Qed.

(* The 4-byte signed load of an atom holding the unsigned int u. *)
Lemma ie2a_sext_den : forall E n u, ew E n = Z_to_bv 64 u -> 0 <= u < 2 ^ 32 ->
  sv_denot E (SExt true 32 (SOff n 0)) = Z_to_bv 64 (bv_swrap 32 u).
Proof.
intros E n u Hn Hu. cbn [sv_denot]. rewrite Hn, Z.add_0_r, Z_to_bv_bv_unsigned.
change (sext 64 (bv_extract 0 32 (Z_to_bv 64 u))) with (Z_to_bv 64 (bv_signed (bv_extract 0 32 (Z_to_bv 64 u)))).
f_equal. rewrite (LMem.signed_of_extract 32 (Z_to_bv 64 u)) by lia.
rewrite unsigned_lit_small by lia. reflexivity.
Qed.

(* `addiw a1, a2, 1` on a 32-bit signed value x that is not INT_MAX: no wrap (lib/B/Prog/m_set_cgW.v run 3a). *)
Lemma ie2a_addw_den : forall E n u, ew E n = Z_to_bv 64 u -> 0 <= u < 2 ^ 32 ->
  - 2 ^ 31 <= bv_swrap 32 u -> bv_swrap 32 u + 1 < 2 ^ 31 ->
  sv_denot E (SAluw ALU_ADD (SExt true 32 (SOff n 0)) (SLit 1)) = Z_to_bv 64 (bv_swrap 32 u + 1).
Proof.
intros E n u Hn Hu Hge Hlt.
set (x := bv_swrap 32 u) in *.
change (sv_denot E (SAluw ALU_ADD (SExt true 32 (SOff n 0)) (SLit 1)))
  with (sext 64 (alu32 ALU_ADD (low32 (sv_denot E (SExt true 32 (SOff n 0)))) (low32 (Z_to_bv 64 1)))).
rewrite (ie2a_sext_den E n u Hn Hu). fold x.
rewrite zalu32_sound. unfold zalu32, zu32, M32. rewrite Z_to_bv64_canon. apply f_equal.
cbn [zalu_raw]. change (1 mod 2 ^ 32) with 1.
rewrite <- (swrap32_id (x + 1)) by lia.
replace (x mod 2 ^ 32 + 1) with ((x + 1) + (- (x / 2 ^ 32)) * bv_modulus 32)
  by (change (bv_modulus 32) with (2 ^ 32); pose proof (Z.div_mod x (2 ^ 32) ltac:(lia)); lia).
apply swrap_add_mod.
Qed.

Lemma ie2a_lts : forall a b, -2^63 <= a < 2^63 -> -2^63 <= b < 2^63 ->
  bv_lts (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof.
  intros a b Ha Hb. unfold bv_lts. rewrite !Z_to_bv_signed.
  rewrite !bv_swrap_small by (change (bv_half_modulus 64) with (2^63); lia). reflexivity.
Qed.

(* The model's increment: e2 = GOT.e2 + 1, and GOT.e2 is not INT_MAX. *)
Lemma ie2a_int_inc : forall x y, TC.int_inc x = Some y -> y = x + 1 /\ x <> TC.INT_MAX.
Proof.
intros x y H. unfold TC.int_inc in H. destruct (Z.eqb_spec x TC.INT_MAX) as [E|E]; [discriminate H|].
injection H as <-. split; [reflexivity | exact E].
Qed.

(* GOT.e2 and the two stores of this stretch, as the world holds them. *)
Lemma ie2a_set_e2 : forall Bx v, TW.set_GOT_e2 Bx v = TW.upd Bx TW.A_GOT_e2 (TW.put 4 v).
Proof. reflexivity. Qed.
Lemma ie2a_set_lastc : forall Bx v,
  TW.set_g_last_counter Bx v = TW.upd Bx TW.OFF_g_last_counter (TW.put 4 v).
Proof. reflexivity. Qed.

(* The branch of 0x83140 on bit 0 of s3: s3 is the byte of g_fail_next the entry read, 0 or 1. *)
Lemma ie2a_br_and1 : forall (E : env) n u, ew E n = Z_to_bv 64 u -> 0 <= u <= 1 ->
  branch_taken BC_EQ (sv_denot E (SAlu ALU_AND (SOff n 0) (SLit 1))) (sv_denot E (SLit 0)) = (u =? 0).
Proof.
intros E n u Hn Hu. cbn [sv_denot]. rewrite Hn, Z.add_0_r, Z_to_bv_bv_unsigned.
assert (E01 : u = 0 \/ u = 1) by lia.
destruct E01 as [E1 | E1]; subst u; vm_compute; reflexivity.
Qed.

(* The register indices the calls' lemmas name as Z_to_bv 5 n. *)
Lemma ie2a_i1 : Z_to_bv 5 1 = 1%bv. Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma ie2a_i2 : Z_to_bv 5 2 = 2%bv. Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma ie2a_i3 : Z_to_bv 5 3 = 3%bv. Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma ie2a_i4 : Z_to_bv 5 4 = 4%bv. Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma ie2a_i10 : Z_to_bv 5 10 = 10%bv. Proof. apply bv_eq; vm_compute; reflexivity. Qed.

(* The registers this stretch keeps: sp, gp, tp, s0 = len, s1 = p, s3 = the g_fail_next byte, s4 = the shadow base,
   and s8 .. s11, which io_send never writes. All are callee-saved, so a call keeps them. *)
Definition ie2a_kept : list (bv 5) := [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 19%bv; 20%bv; 24%bv; 25%bv; 26%bv; 27%bv].

Lemma ie2a_ap : forall (R1 R2 : bvmap 5 word) (r : bv 5), aregs_preserved R1 R2 -> acallee_saved (bv_unsigned r) ->
  YK11.getr R2 r = YK11.getr R1 r.
Proof. intros R1 R2 r HP Hc. pose proof (HP _ Hc) as H. rewrite !Z_to_bv_bv_unsigned in H. exact H. Qed.

Lemma ie2a_kept_of_pres : forall rg rg2 : bvmap 5 word, aregs_preserved rg rg2 ->
  forall r, In r ie2a_kept -> YK11.getr rg2 r = YK11.getr rg r.
Proof.
intros rg rg2 HP r Hr. apply (ie2a_ap rg rg2 r HP). unfold ie2a_kept in Hr. cbn [In] in Hr.
repeat (destruct Hr as [<- | Hr];
        [unfold acallee_saved;
         lazymatch goal with |- context [bv_unsigned ?x] =>
           let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v end;
         lia |]).
destruct Hr.
Qed.

Lemma ie2a_regs_step : forall regs (r3 r4 : bvmap 5 word) p frame fail,
  ios_regs regs r3 p frame fail ->
  (forall r, 24 <= r <= 27 -> YK11.getr r3 (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)) ->
  (forall r : bv 5, In r ie2a_kept -> YK11.getr r4 r = YK11.getr r3 r) ->
  ios_regs regs r4 p frame fail /\
  (forall r, 24 <= r <= 27 -> YK11.getr r4 (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)).
Proof.
  intros regs r3 r4 p frame fail HR G24 M.
  destruct HR as (G2 & G3 & G4 & G8 & G9 & G19 & G20).
  split.
  - unfold ios_regs.
    rewrite (M 2%bv ltac:(unfold ie2a_kept; cbn [In]; tauto)),
            (M 3%bv ltac:(unfold ie2a_kept; cbn [In]; tauto)),
            (M 4%bv ltac:(unfold ie2a_kept; cbn [In]; tauto)),
            (M 8%bv ltac:(unfold ie2a_kept; cbn [In]; tauto)),
            (M 9%bv ltac:(unfold ie2a_kept; cbn [In]; tauto)),
            (M 19%bv ltac:(unfold ie2a_kept; cbn [In]; tauto)),
            (M 20%bv ltac:(unfold ie2a_kept; cbn [In]; tauto)).
    exact (conj G2 (conj G3 (conj G4 (conj G8 (conj G9 (conj G19 G20)))))).
  - assert (E24 : Z_to_bv 5 24 = 24%bv) by (apply bv_eq; vm_compute; reflexivity).
    assert (E25 : Z_to_bv 5 25 = 25%bv) by (apply bv_eq; vm_compute; reflexivity).
    assert (E26 : Z_to_bv 5 26 = 26%bv) by (apply bv_eq; vm_compute; reflexivity).
    assert (E27 : Z_to_bv 5 27 = 27%bv) by (apply bv_eq; vm_compute; reflexivity).
    intros r Hr.
    assert (HR4 : r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    destruct HR4 as [E|[E|[E|E]]]; subst r.
    + rewrite E24, (M 24%bv ltac:(unfold ie2a_kept; cbn [In]; tauto)), <- E24.
      exact (G24 24 ltac:(lia)).
    + rewrite E25, (M 25%bv ltac:(unfold ie2a_kept; cbn [In]; tauto)), <- E25.
      exact (G24 25 ltac:(lia)).
    + rewrite E26, (M 26%bv ltac:(unfold ie2a_kept; cbn [In]; tauto)), <- E26.
      exact (G24 26 ltac:(lia)).
    + rewrite E27, (M 27%bv ltac:(unfold ie2a_kept; cbn [In]; tauto)), <- E27.
      exact (G24 27 ltac:(lia)).
Qed.

(* The bytes of G this stretch stores: GOT.e2 and g_last_counter. *)
Definition ie2a_wr (a : Z) : Prop :=
  (TB_GOT + 196 <= a < TB_GOT + 196 + 4) \/ (TB_g_last_counter <= a < TB_g_last_counter + 4).

Lemma ie2a_wr_inG : forall a, ie2a_wr a -> inG TG.G_HARNESS_B a.
Proof.
intros a [Ha | Ha].
- apply (ios_inG_row _ _ _ a TMAP_B_GOT). unfold TW.SZ_GOT. lia.
- apply (ios_inG_row _ _ _ a TMAP_B_g_last_counter). unfold TW.SZ_g_last_counter. lia.
Qed.

Lemma ie2a_wr_iosend : forall n a, ie2a_wr a -> iosend_wr n a.
Proof.
intros n a [Ha | Ha]; [apply ios_wr_got_e2 | apply ios_wr_lastc]; lia.
Qed.

(* The frame never holds a byte of ie2a_wr: it is outside G, or inside g_s, which holds neither word. *)
Lemma ie2a_frame_off : forall p n a, iosend_frame_at p n -> p <= a < p + n -> ~ ie2a_wr a.
Proof.
intros p n a HFAT Ha HW.
assert (EG : TB_GOT = 0x5e4f60) by reflexivity.
assert (EL : TB_g_last_counter = 0x5dedc0) by reflexivity.
assert (ES : TB_g_s = 0x5df640) by reflexivity.
assert (SS : TW.SZ_g_s = 18264) by reflexivity.
destruct HFAT as [HnG | (Hlo & Hhi)].
- exact (HnG a Ha (ie2a_wr_inG a HW)).
- destruct HW as [HW | HW]; lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The struct spec_frame's fields                                       *)
(* ------------------------------------------------------------------ *)

(* Byte k of the little-endian value of a byte list is the list's byte k (image A's io_send_seg_e2.v). *)
Lemma ie2a_ble_shiftr : forall (l : list byte) (k : nat),
  Z.shiftr (bytes_le_to_Z l) (8 * Z.of_nat k) mod 256 = bv_unsigned (nth k l (Z_to_bv 8 0)).
Proof.
  induction l as [|b r IH]; intros k.
  - cbn [bytes_le_to_Z nth]. destruct k; rewrite Z.shiftr_0_l, Z_to_bv_unsigned; reflexivity.
  - assert (Hb : 0 <= bv_unsigned b < 256)
      by (pose proof (bv_unsigned_in_range 8 b) as Hr; change (bv_modulus 8) with 256 in Hr; lia).
    assert (HL : Z.log2 (bv_unsigned b) < 8).
    { destruct (Z.eq_dec (bv_unsigned b) 0) as [E|Hne];
        [rewrite E, Z.log2_nonpos by lia; lia | apply Z.log2_lt_pow2; lia]. }
    cbn [bytes_le_to_Z].
    destruct k as [|k'].
    + cbn [nth]. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
      change 256 with (2 ^ 8).
      apply Z.bits_inj'. intros i Hi.
      destruct (Z_lt_le_dec i 8) as [Hl|Hl].
      * rewrite Z.mod_pow2_bits_low by lia. rewrite Z.lor_spec, Z.shiftl_spec by lia.
        rewrite (Z.testbit_neg_r (bytes_le_to_Z r) (i - 8)) by lia. apply orb_false_r.
      * rewrite Z.mod_pow2_bits_high by lia. symmetry. apply Z.bits_above_log2; lia.
    + cbn [nth]. rewrite <- (IH k').
      f_equal.
      apply Z.bits_inj'. intros i Hi.
      rewrite !Z.shiftr_spec by lia.
      rewrite Z.lor_spec, Z.shiftl_spec by lia.
      rewrite (Z.bits_above_log2 (bv_unsigned b) (i + 8 * Z.of_nat (S k'))) by lia.
      cbn [orb]. f_equal. lia.
Qed.

Lemma ie2a_nth_sub : forall (l : list byte) (off : Z) (n k : nat), 0 <= off -> (k < n)%nat ->
  (Z.to_nat off + n <= length l)%nat ->
  nth k (TW.sub l off n) (Z_to_bv 8 0) = nth (Z.to_nat off + k) l (Z_to_bv 8 0).
Proof.
  intros l off n k H0 Hk Hn.
  assert (HS : (k < length (TW.sub l off n))%nat)
    by (unfold TW.sub; rewrite length_firstn, length_skipn; lia).
  assert (HL : (Z.to_nat off + k < length l)%nat) by lia.
  pose proof (TWL.ne_sub l off n k H0) as E.
  replace (k <? n)%nat with true in E by (symmetry; apply Nat.ltb_lt; lia).
  rewrite (nth_error_nth' (TW.sub l off n) (Z_to_bv 8 0) HS),
          (nth_error_nth' l (Z_to_bv 8 0) HL) in E.
  injection E as E. exact E.
Qed.

Lemma ie2a_le_byte1 : forall b : byte, YO0f.le_byte (bv_unsigned b) 1 0 = bv_unsigned b.
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as Hr. change (bv_modulus 8) with 256 in Hr.
  unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
  rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite Z.mod_mod by lia. apply Z.mod_small. lia.
Qed.

(* A field of a garr8 byte array, as YI04.val_mem of its little-endian value. *)
Lemma ie2a_val_of_garr8 : forall (m : word -> option byte) (fp off : Z) (SB : list byte) (n : nat),
  garr8 tfibsegs m fp (map (fun b : byte => bv_unsigned b) SB) -> 0 <= off ->
  (Z.to_nat off + n <= length SB)%nat ->
  YI04.val_mem tfibsegs m (fp + off) n (TW.u_at SB off n).
Proof.
  intros m fp off SB n HG H0 Hn k Hk.
  assert (Hj : ((Z.to_nat off + k) < length (map (fun b : byte => bv_unsigned b) SB))%nat)
    by (rewrite length_map; lia).
  destruct (HG (Z.to_nat off + k)%nat Hj) as [Hv _].
  specialize (Hv 0%nat ltac:(lia)). rewrite Nat2Z.inj_0, Z.add_0_r in Hv.
  rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) in Hv by exact Hj.
  rewrite map_nth in Hv.
  replace (fp + off + Z.of_nat k) with (fp + Z.of_nat (Z.to_nat off + k)) by lia.
  rewrite Hv. f_equal. f_equal.
  rewrite ie2a_le_byte1.
  unfold YO0f.le_byte, TW.u_at.
  rewrite (Z.mod_small (bytes_le_to_Z (TW.sub SB off n)) (2 ^ (8 * Z.of_nat n)))
    by (apply TWL.ble_small, TWL.length_sub_le).
  rewrite ie2a_ble_shiftr, (ie2a_nth_sub SB off n k H0 Hk Hn). reflexivity.
Qed.

(* put n of the value of n bytes of a list is those n bytes (image A's io_send_seg_ack.v). *)
Lemma ie2a_put_sub : forall (SB : list byte) k n, 0 <= k -> k + Z.of_nat n <= Z.of_nat (length SB) ->
  TW.put n (TW.u_at SB k n) = TW.sub SB k n.
Proof.
  intros SB k n Hk Hl. pose proof (TWL.length_sub SB k n Hk Hl) as L. unfold TW.put, TW.u_at.
  remember (TW.sub SB k n) as s eqn:Es. rewrite <- L. apply SFun.Z_to_le_bytes_to_Z.
Qed.

Lemma ie2a_nth_sub_bz : forall (SB : list byte) k n j, 0 <= k -> (j < n)%nat ->
  k + Z.of_nat n <= Z.of_nat (length SB) ->
  nth j (map DSpec.bz (TW.sub SB k n)) 0 = nth (Z.to_nat k + j) (map DSpec.bz SB) 0.
Proof.
  intros SB k n j Hk Hj Hl.
  destruct (nth_error SB (Z.to_nat k + j)) as [x|] eqn:Ex.
  2: { exfalso. apply nth_error_None in Ex. lia. }
  assert (E1 : nth_error (map DSpec.bz (TW.sub SB k n)) j = Some (DSpec.bz x)).
  { rewrite nth_error_map, (TWL.ne_sub SB k n j Hk).
    replace (j <? n)%nat with true by (symmetry; apply Nat.ltb_lt; exact Hj). rewrite Ex. reflexivity. }
  assert (E2 : nth_error (map DSpec.bz SB) (Z.to_nat k + j) = Some (DSpec.bz x))
    by (rewrite nth_error_map, Ex; reflexivity).
  erewrite (nth_error_nth _ _ _ E1). erewrite (nth_error_nth _ _ _ E2). reflexivity.
Qed.

Lemma ie2a_garr8_sub : forall (m : word -> option byte) p (SB : list byte) k n,
  garr8 tfibsegs m p (map DSpec.bz SB) -> 0 <= k -> k + Z.of_nat n <= Z.of_nat (length SB) ->
  garr8 tfibsegs m (p + k) (map DSpec.bz (TW.sub SB k n)).
Proof.
  intros m p SB k n HG Hk Hl j Hj.
  rewrite length_map, (TWL.length_sub SB k n Hk Hl) in Hj.
  rewrite (ie2a_nth_sub_bz SB k n j Hk Hj Hl).
  assert (Hj' : (Z.to_nat k + j < length (map DSpec.bz SB))%nat) by (rewrite length_map; lia).
  replace (p + k + Z.of_nat j) with (p + Z.of_nat (Z.to_nat k + j)) by lia.
  exact (HG _ Hj').
Qed.

(* A field of n bytes at offset k of the struct's byte list, of value v. *)
Lemma ie2a_field : forall (m : word -> option byte) p (SB : list byte) k n v,
  garr8 tfibsegs m p (map DSpec.bz SB) -> 0 <= k -> k + Z.of_nat n <= Z.of_nat (length SB) ->
  TW.u_at SB k n = v -> garr8 tfibsegs m (p + k) (map DSpec.bz (TW.put n v)).
Proof.
  intros m p SB k n v HG Hk Hl Hv. subst v. rewrite (ie2a_put_sub SB k n Hk Hl).
  exact (ie2a_garr8_sub m p SB k n HG Hk Hl).
Qed.

(* A range of n bytes at x + k, x 8-aligned, inside one granule has one shadow byte. *)
Lemma ie2a_shadow_one : forall x k n, 0 <= x -> x mod 8 = 0 -> 0 <= k -> 0 < n -> k mod 8 + n <= 8 ->
  BCells.shadow_addr (x + k + n - 1) - BCells.shadow_addr (x + k) + 1 = 1.
Proof.
  intros x k n H0 Hx Hk Hn Hm. unfold BCells.shadow_addr.
  pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. pose proof (Z.div_mod k 8 ltac:(lia)) as Dk.
  pose proof (Z.mod_pos_bound k 8 ltac:(lia)) as Mk.
  assert (E1 : x / 8 + k / 8 = (x + k) / 8).
  { apply Z.div_unique with (k mod 8); [left; lia | lia]. }
  assert (E2 : x / 8 + k / 8 = (x + k + n - 1) / 8).
  { apply Z.div_unique with (k mod 8 + n - 1); [left; lia | lia]. }
  rewrite <- E1, <- E2. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* Memory facts carried across a stretch                               *)
(* ------------------------------------------------------------------ *)

Lemma ie2a_rdword_ext : forall (rd rd' : Z -> option Z) a, (forall i, 0 <= i < 8 -> rd' (a + i) = rd (a + i)) ->
  rdword rd' a = rdword rd a.
Proof.
intros rd rd' a H. unfold rdword.
assert (H0 : rd' a = rd a) by (rewrite <- (Z.add_0_r a); apply H; lia).
rewrite H0, (H 1), (H 2), (H 3), (H 4), (H 5), (H 6), (H 7) by lia. reflexivity.
Qed.

(* garr8 at a later memory whose view keeps the bytes. *)
Lemma ie2a_garr8_kept : forall (H H' : word -> bool) (m m' : word -> option byte) p l,
  garr8 tfibsegs (mrestrict H m) p l ->
  (forall a, p <= a < p + Z.of_nat (length l) -> aview tfibsegs H' m' a = aview tfibsegs H m a) ->
  garr8 tfibsegs (mrestrict H' m') p l.
Proof.
intros H H' m m' p l HG HK j Hj. destruct (HG j Hj) as [HV HR]. split; [|exact HR].
intros kk Hk. assert (kk = 0)%nat by lia. subst kk.
specialize (HV 0%nat Hk).
assert (Hk' : p <= p + Z.of_nat j + Z.of_nat 0 < p + Z.of_nat (length l)) by lia.
pose proof (HK _ Hk') as E. unfold aview in E. cbv beta in E. rewrite HV in E. cbn [option_map] in E.
destruct (mbyte tfibsegs (mrestrict H' m') (p + Z.of_nat j + Z.of_nat 0)) as [b'|] eqn:Eb; [|discriminate E].
cbn [option_map] in E. injection E as E. f_equal. apply bv_eq. exact E.
Qed.

(* The nine saved words, at a memory that keeps [sp - 72, sp). *)
Lemma ie2a_saved_kept : forall (W2 W3 : world tfibsegs) mem2 mem3 regs,
  ios_saved W2 mem2 regs ->
  (forall a, spZ regs - 72 <= a < spZ regs ->
     aview tfibsegs (w_H W3) mem3 a = aview tfibsegs (w_H W2) mem2 a) ->
  ios_saved W3 mem3 regs.
Proof.
intros W2 W3 mem2 mem3 regs HS HK. unfold ios_saved in *.
assert (HB : forall o, In o IOS_SAVED -> 8 <= fst o <= 72).
{ intros o Ho. unfold IOS_SAVED in Ho.
  repeat (destruct Ho as [Ho | Ho]; [subst o; cbn [fst]; lia |]). destruct Ho. }
rewrite Forall_forall in *. intros o Ho. rewrite <- (HS o Ho). apply ie2a_rdword_ext.
intros i Hi. pose proof (HB o Ho). apply HK. lia.
Qed.

(* The struct spec_frame at a memory that keeps its 80 bytes. *)
Lemma ie2a_sframe_kept : forall (W2 W3 : world tfibsegs) mem2 mem3 q fa f,
  trans_sframe_at W2 mem2 q fa f ->
  (forall a, q <= a < q + 80 -> aview tfibsegs (w_H W3) mem3 a = aview tfibsegs (w_H W2) mem2 a) ->
  trans_sframe_at W3 mem3 q fa f.
Proof.
intros W2 W3 mem2 mem3 q fa f (H0 & H8 & SB & HG & HL & HR) HK.
split; [exact H0|]. split; [exact H8|]. exists SB. split; [|split; [exact HL | exact HR]].
apply (ie2a_garr8_kept _ _ _ _ _ _ HG). rewrite length_map, HL. exact HK.
Qed.

(* ------------------------------------------------------------------ *)
(* Tactics of the runs                                                 *)
(* ------------------------------------------------------------------ *)

(* The write right of a run whose state has no writable window. *)
Ltac ie2a_awr_nil :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  apply awr_ok_x_nil.

(* The write right of the run over ie2a_state: the read-only stack cells (an empty window) and the two words of G,
   GOT.e2 (based at atom 270 = A_OBJ 29) and g_last_counter (atom 456 = A_HI 56, window -884 .. -880). *)
Ltac ie2a_awr U1 U2 :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  repeat (apply awr_ok_x_cons_g;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
      first [ lia
            | rewrite U1 in Ha; apply ie2a_wr_inG; left; lia
            | rewrite U2 in Ha; apply ie2a_wr_inG; right; lia ] |]);
  apply awr_ok_x_nil.

(* The model term after a run, named and opaque. *)
Ltac ie2a_md mdv := lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ =>
  set (mdv := mdx) in *; clearbody mdv end.

(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac. *)
Ltac ie2a_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | ?T => idtac "ie2a_reg: no match for" T; fail
  end.

(* The windows a run wrote, each closed by tac. *)
Ltac ie2a_win Hin Hx tac :=
  lazymatch type of Hin with In ?x ?l => let l' := eval vm_compute in l in change (In x l') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; tac |]);
  destruct Hin.

(* The symbolic state of HS, computed. *)
Ltac ie2a_rw HS := lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ss ?m =>
  let ss' := eval vm_compute in ss in change (st_ok_pi sg vl Ex ss' m) in HS end.

(* The two regions this stretch writes, read back from a state of the run: GOT.e2 (index 1 of ie2a_regions) and
   g_last_counter (index 2). *)
Ltac ie2a_stored HS Re Rl :=
  lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ss (restrict ?Hh ?m) =>
    let r1 := eval vm_compute in (nth 1 (ss_mem ss) (YP09.mkRegion None 0 0 0 0 [])) in
    pose proof (st_ok_pi_region_nth Ex ss (restrict Hh m) 1 r1 HS ltac:(vm_compute; reflexivity)) as Re;
    let r2 := eval vm_compute in (nth 2 (ss_mem ss) (YP09.mkRegion None 0 0 0 0 [])) in
    pose proof (st_ok_pi_region_nth Ex ss (restrict Hh m) 2 r2 HS ltac:(vm_compute; reflexivity)) as Rl
  end;
  cbn [ms_mem restrict] in Re, Rl.

(* ------------------------------------------------------------------ *)
(* The symbolic states                                                 *)
(* ------------------------------------------------------------------ *)

(* A state with no region and no fact: the registers only (the call of a leaf right at a cut). *)
Definition ie2a_ss0 (pc : Z) : sstate := mkSS pc sr_atoms [] None (mkFacts [] [] []).
(* No instrumented check on the stretch: the empty shadow entry, at the shadow base s4. *)
Definition ie2a_Bx : sv := SOff 20 0.

(* After check_latest_control (0x8311c): atom 32 GOT.e2 (4 bytes, unsigned), atom 33 f.send (4 bytes, unsigned).
   Regions: f.send at sp + 40 (io_send's own frame, read only), GOT.e2 at object 29 (GOT + 196, written), and
   g_last_counter, which the code reaches as -884 from the %hi of object 56 (written). The store of GOT.e2 is
   `sw a1, -248(a0)` with a0 the %hi of object 55; the alias of the facts names it object 29. *)
Definition ie2a_rstk : YP09.region :=
  YP09.mkRegion (Some 2%nat) 40 44 40 40 [YP09.mkChunk 40 (CVal 4 (SOff 33 0))].
Definition ie2a_re2 : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 29)) 0 4 0 4 [YP09.mkChunk 0 (CVal 4 (SOff 32 0))].
Definition ie2a_rlc : YP09.region :=
  YP09.mkRegion (Some (A_HI 56)) (-884) (-880) (-884) (-880) [].
Definition ie2a_regions : smem := [ie2a_rstk; ie2a_re2; ie2a_rlc].
Definition ie2a_facts : facts := mkFacts [] [] [(SOff (A_HI 55) (-248), SOff (A_OBJ 29) 0)].
Definition ie2a_ss (pc : Z) : sstate := mkSS pc sr_atoms ie2a_regions None ie2a_facts.

(* The two values the stretch reads. *)
Definition ie2a_snd (frame : list byte) : Z := DSpec.sf_send (TC.rf frame).
Definition ie2a_e2v (Bx : list byte) : Z := TW.u_at Bx TW.A_GOT_e2 4.

Section e2a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).
Definition ie2a_E0 (regs : bvmap 5 word) : env := Eimg (PI := PI_transportb) (Ereg regs []).

(* ------------------------------------------------------------------ *)
(* The leaf form                                                       *)
(* ------------------------------------------------------------------ *)

(* A byte of G is never hidden (it is a byte of a loaded segment). *)
Lemma ie2a_G_vis : forall (W : world segs) a, inG TG.G_HARNESS_B a -> w_H W (Z_to_bv 64 a) = false.
Proof.
intros W a Ha. destruct (aview segs (w_H W) (fun _ => None) a) as [v|] eqn:E.
- exact (LB.decode_leafb_aview_vis W (fun _ => None) a v E).
- exfalso. exact (gx_rw_vis segs TG.G_HARNESS_B a G_HARNESS_B_rw Ha (w_H W) (fun _ => None) E).
Qed.

(* A range of G bytes is a range a leaf's footprint may read. *)
Lemma ie2a_rng_G : forall (W : world segs) lo len, 0 <= lo -> lo + len <= 2 ^ 64 ->
  (forall a, lo <= a < lo + len -> inG TG.G_HARNESS_B a) ->
  LExecF.rng (LCK.RNG_W (world segs) (@w_H segs) W) lo len.
Proof.
intros W lo len H0 H1 HG. apply (LB.decode_leafb_rng W lo len H0 H1). intros a Ha. exact (ie2a_G_vis W a (HG a Ha)).
Qed.

(* The world relation at the leaf form's view: on the payload bytes the two views agree. *)
Lemma ie2a_csw : forall (W : world segs) mem Bw,
  tw_at TMAP_B (aview segs (w_H W) mem) Bw -> tw_at TMAP_B (CSW.csw_view mem) Bw.
Proof.
intros W mem Bw H. apply (tw_kept TMAP_B _ _ Bw H). intros x Hx.
unfold CSW.csw_view, aview. cbv beta. f_equal.
exact (LB.decode_leafb_mrd W mem x (ie2a_G_vis W x (ios_tw_in_G x Hx))).
Qed.

Lemma ie2a_inG_M : forall a, TB_M <= a < TB_M + TW.SZ_M -> inG TG.G_HARNESS_B a.
Proof. intros a Ha. exact (ios_inG_row _ _ _ a TMAP_B_M Ha). Qed.

(* A leaf call (the leaf bridge's post, written range WR = []) from io_send's G journal, in continuation form: the
   return state keeps the journal, the callee-saved registers, every byte outside the leaf's window [sp - ESTACK, sp)
   and presence, and the leaf's X (image A's io_send_seg_tail.v ios_leaf_call). *)
Lemma ie2a_leaf_call : forall (W : world segs) (regsT : bvmap 5 word) memT STK sp0 FP ly S W0 mem md own lyc Sc mdc
    k (o PC : Z) (X : (word -> option byte) -> Prop) (Q : world segs -> config -> Prop),
  AR_laws segs B ->
  ajournal_gx TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
  YK0s.ret_ok (YK11.getr regsT 1) -> YK11.getr regsT 3 = w64 (as_gp B) -> YK11.getr regsT 4 = w64 (as_tp B) ->
  (LB.decode_leafb_ecall_pre B lyc Sc W regsT memT mdc ->
     SRr segs W (@LCK.cfg_at fx PC regsT memT mdc) (LB.decode_leafb_post B lyc Sc W regsT memT mdc None [] X)) ->
  (forall regs2 mem2 md2,
     ajournal_gx TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k ->
     aregs_preserved regsT regs2 ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regsT - ESTACK <= a < spZ regsT) ->
        aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) ->
     (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a) ->
     X mem2 ->
     SRr segs W (mkCfg (YK11.mkst regs2 (YK11.getr regsT 1) mem2 (YK11.seg_rom segs)) md2) Q) ->
  SRr segs W (mkCfg (YK11.mkst regsT (Z_to_bv 64 PC) memT (YK11.seg_rom segs)) mdc) Q.
Proof.
intros W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o PC X Q LAWS HJ Hsp Hal Hneg Hbud Hra Hgp Htp
  HLEAF HK.
eapply SRr_bind.
{ apply (@gx_call_leaf fx rc tfib_sink_head segs B TG.G_HARNESS_B STK sp0 FP ly S W0 mem md own
    lyc Sc W memT mdc k _ (YK11.getr regsT 1)
    (fun regs2 mem2 md2 => aregs_preserved regsT regs2 /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regsT - ESTACK <= a < spZ regsT) ->
          aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
       (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a) /\ X mem2) HJ).
  intros memS HJS.
  eapply SRr_mono.
  { exact (@LB.decode_leafb_journal fx rc tfib_sink_head B LAWS W regsT memT STK sp0 FP ly S W0 memS md own lyc Sc
      mdc k o PC None [] X HJS Hsp Hal Hneg Hbud Hra Hgp Htp
      ltac:(intros a Ha; unfold LCK.in_wr in Ha; inversion Ha) HLEAF). }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP & _ & HK2 & HG2 & HX).
  split; [reflexivity|]. exists regs2, mem2, md2. split; [reflexivity|]. split; [exact HJ2|].
  split; [exact HP|]. split; [|split; [exact HG2 | exact HX]].
  intros a Ha Hn. apply HK2; [exact Ha | exact Hn | intros Hw; unfold LCK.in_wr in Hw; inversion Hw]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP & HK2 & HG2 & HX).
exact (HK regs2 mem2 md2 HJ2 HP HK2 HG2 HX).
Qed.

(* check_state_wake through the leaf form: its footprint premises at a call state whose sp is above G, its own
   16-byte frame and the 4 bytes of M.foreign it loads (check_state_wake_c.v CHECK_STATE_WAKE_FOREIGN). *)
Lemma ie2a_csw_leaf : forall (W : world segs) regsT memT mdc ly2 S2 B5,
  (forall fx' : YK11.FPState, @transport_leaf_at rc B (@LSW.transport_check_state_wake_cg) fx') ->
  tw_at TMAP_B (aview segs (w_H W) memT) B5 -> TC.check_state_wake_m B5 = Some (B5, tt) ->
  TG.G_HARNESS_B_HI + ESTACK <= spZ regsT -> spZ regsT <= 2 ^ 47 ->
  LB.decode_leafb_ecall_pre B ly2 S2 W regsT memT mdc ->
  SRr segs W (@LCK.cfg_at fx (transportb_sigma TB_check_state_wake) regsT memT mdc)
    (LB.decode_leafb_post B ly2 S2 W regsT memT mdc None [] (fun _ => B5 = B5)).
Proof.
intros W regsT memT mdc ly2 S2 B5 HL Htw Hm Hlo Hhi HPRE.
pose proof (HL fx ly2 S2 W regsT memT mdc (spZ regsT - CSW.CHECK_STATE_WAKE_FRAME) B5 B5 HPRE) as HC.
cbv zeta in HC.
change (bv_unsigned (YK11.getr regsT (Z_to_bv 5 2))) with (spZ regsT) in HC.
change CSW.CHECK_STATE_WAKE with (transportb_sigma TB_check_state_wake) in HC.
unfold LB.decode_leafb_ecall_pre, LCK.ecall_pre in HPRE.
destruct HPRE as (_ & _ & _ & _ & _ & Hpres & _).
change (LCK.spZ regsT) with (spZ regsT) in Hpres.
assert (EST : LCK.ESTACK = 4096) by reflexivity. rewrite EST in Hpres.
assert (FR : CSW.CHECK_STATE_WAKE_FRAME = 16) by reflexivity.
assert (GHI : TG.G_HARNESS_B_HI = 0x5f2e10) by reflexivity.
assert (EE : ESTACK = 4096) by reflexivity.
assert (EM : TB_M = 0x5dede0) by reflexivity.
unfold CSW.CHECK_STATE_WAKE_FOREIGN, TW.A_M_foreign, TW.OFF_M in HC.
assert (GLO : TG.G_HARNESS_B_LO = 0x5ded00) by reflexivity.
assert (SM : TW.SZ_M = 1648) by reflexivity.
apply HC.
- exact (ie2a_csw W memT B5 Htw).
- exact Hm.
- apply (LB.decode_leafb_stk W memT); [lia | lia |]. intros a Ha. apply Hpres. lia.
- lia.
- unfold AKA.off_stk. left. change (bv_unsigned (YK11.getr regsT (Z_to_bv 5 2))) with (spZ regsT). lia.
- apply (LB.decode_leafb_rng_vis W memT); [lia | lia |]. intros a Ha. apply Hpres. lia.
- apply ie2a_rng_G; [lia | lia |]. intros a Ha. apply ie2a_inG_M. lia.
Qed.

(* What a leaf call returns (DgnTransportBLeafb.v decode_leafb_journal's facts with RES = None, WR = [] and the
   leaf's X Bx = Bx). *)
Definition ie2a_lr (regsT : bvmap 5 word) (W2 : world segs) (memT : word -> option byte) (Bx : list byte)
    (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model) : Prop :=
  aregs_preserved regsT regs2 /\ (forall r, None = Some r -> YK11.getr regs2 10 = w64 r) /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regsT - ESTACK <= a < spZ regsT) -> ~ LCK.in_wr [] a ->
     aview segs (w_H W2) mem2 a = aview segs (w_H W2) memT a) /\
  (forall a, apresent (w_H W2) memT a -> apresent (w_H W2) mem2 a) /\ Bx = Bx.

(* The stack window of a call from io_send's frame: the struct at sp + 8 lies in the caller's journal window, above
   the callee's ESTACK window. *)
Definition ie2a_call_win (STK sp0 sp : Z) : Prop :=
  sp mod 16 = 0 /\ sp0 - STK <= sp - ESTACK /\ sp + 88 <= sp0.

(* check_latest_control at 0x84490 (the call at 0x83118), a0 = sp + 8 (image A's io_send_seg_ack.v
   iak_call_clc). *)
Lemma ie2a_call_clc : forall STK sp0 FP ly S W0 mem0 md0 own ly2 S2 (W2 : world segs) memT mdT k
    (regsT : bvmap 5 word) (sp p : Z) (fr Bx : list byte),
  transport_cells B -> AR_laws segs B ->
  (forall fx' : YK11.FPState, @transport_leaf_at rc B (@LLC.transport_check_latest_control_cg) fx') ->
  ajournal_gx TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 memT mdT k ->
  YK11.getr regsT (Z_to_bv 5 2) = Z_to_bv 64 sp -> YK11.getr regsT (Z_to_bv 5 10) = Z_to_bv 64 (sp + 8) ->
  YK0s.ret_ok (YK11.getr regsT (Z_to_bv 5 1)) ->
  YK11.getr regsT (Z_to_bv 5 3) = w64 (as_gp B) -> YK11.getr regsT (Z_to_bv 5 4) = w64 (as_tp B) ->
  ie2a_call_win STK sp0 sp ->
  trans_sframe_at W2 memT (sp + 8) p (TC.rf fr) ->
  tw_at TMAP_B (aview segs (w_H W2) memT) Bx -> TC.check_latest_control_m Bx fr = Some (Bx, tt) ->
  SRr segs W2 (mkCfg (@YK11.mkst fx regsT (Z_to_bv 64 LLCc.CHECK_LATEST_CONTROL) memT (YK11.seg_rom segs)) mdT)
    (fun W3 c3 => W3 = W2 /\ exists regs3 mem3 md3,
       c3 = mkCfg (@YK11.mkst fx regs3 (YK11.getr regsT (Z_to_bv 5 1)) mem3 (YK11.seg_rom segs)) md3 /\
       ajournal_gx TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem3 md3 k /\
       ie2a_lr regsT W2 memT Bx regs3 mem3 md3).
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 memT mdT k regsT sp p fr Bx HCELLS LAWS LEAF HJ
    R2 R10 Rra R3 R4 (Hal & Hlo & Hhi) HSF HTW HM.
  pose proof HJ as (HSTK & _ & (memS0 & HJ0 & _) & _). rewrite !Z.add_0_r in HJ0.
  pose proof HJ0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (Hsp0al & HSTK0 & Hceil & Hslo & Hshi & H47 & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (EST : ESTACK = 4096) by reflexivity.
  assert (EM : TB_M = 0x5dede0) by reflexivity.
  assert (SM : TW.SZ_M = 1648) by reflexivity.
  assert (SPu : bv_unsigned (YK11.getr regsT (Z_to_bv 5 2)) = sp) by (rewrite R2; apply unsigned_lit_small; lia).
  destruct HSF as (Hfp0 & Hfp8 & SB & HG & HLSB & _ & _ & _ & _ & _ & _ & _ & Fsend & _).
  apply (gx_call_leaf segs B TG.G_HARNESS_B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 memT mdT k _
    (YK11.getr regsT (Z_to_bv 5 1)) (ie2a_lr regsT W2 memT Bx) HJ).
  intros memS HJS.
  pose proof HJS as (HAR & Hly & _).
  pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Eslo & Eshi & _).
  unfold ie2a_lr.
  apply (LB.decode_leafb_journal B LAWS W2 regsT memT STK sp0 FP ly S W0 memS md0 own ly2 S2 mdT k (sp - sp0)
    LLCc.CHECK_LATEST_CONTROL None [] (fun _ => Bx = Bx) HJS).
  - change (spZ regsT) with (bv_unsigned (YK11.getr regsT (Z_to_bv 5 2))). rewrite SPu. lia.
  - rewrite Zminus_mod, Hal, Hsp0al. reflexivity.
  - lia.
  - lia.
  - exact Rra.
  - exact R3.
  - exact R4.
  - intros a Ha. inversion Ha.
  - intros HPRE.
    pose proof (LEAF fx) as LF.
    unfold transport_leaf_at, LLC.transport_check_latest_control_cg in LF.
    specialize (LF ly2 S2 W2 regsT memT mdT (sp - ESTACK) Bx Bx (sp + 8) fr HPRE).
    cbv zeta in LF.
    assert (HRA : range_addressable (aview segs (w_H W2) memT) SHADOW_OFF (sp + 8 + 32) 4)
      by (apply (can_stack_addressable segs B ly2 S2 W2 memT mdT (sp + 8 + 32) 4 HAR); lia).
    apply LF; clear LF.
    + exact R10.
    + lia.
    + exact Hfp8.
    + apply (LB.decode_leafb_bytes_garr8 W2 memT (sp + 8 + 32) (TW.put 4 (DSpec.sf_send (TC.rf fr))));
        [| lia | rewrite TWL.length_put; lia].
      exact (ie2a_field _ (sp + 8) SB 32 4 _ HG ltac:(lia) ltac:(rewrite HLSB; cbn; lia) Fsend).
    + exact (ie2a_csw W2 memT Bx HTW).
    + exact HM.
    + rewrite SPu. apply (LB.decode_leafb_stk_journal B STK sp0 FP ly S W0 memS md0 own ly2 S2 W2 memT mdT k
        (sp - ESTACK) sp HJS); lia.
    + rewrite SPu. unfold LLCc.CHECK_LATEST_CONTROL_FRAME. lia.
    + unfold AKA.off_stk. rewrite SPu.
      unfold LLCc.CHECK_LATEST_CONTROL_FRAME, TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI. lia.
    + exact (LB.decode_leafb_asan_cells B HCELLS ly2 S2 W2 memT mdT HAR).
    + rewrite SPu. apply (@LB.decode_leafb_app_stack rc). unfold LLCc.CHECK_LATEST_CONTROL_FRAME. lia.
    + rewrite SPu. apply (@LB.decode_leafb_app_stack rc). lia.
    + unfold AKA.off_stk. rewrite SPu. unfold LLCc.CHECK_LATEST_CONTROL_FRAME, BCells.GOT_CELL_K. lia.
    + unfold AKA.off_stk. rewrite SPu. unfold LLCc.CHECK_LATEST_CONTROL_FRAME, BCells.CELL_K. lia.
    + unfold AKA.off_stk. rewrite SPu. right. lia.
    + apply (LB.decode_leafb_addressable W2 memT (sp + 8 + 32) 4 HRA);
        [lia | lia | unfold BCells.APPMEM_END; lia |].
      intros i Hi. apply (@LB.decode_leafb_app_stack rc). lia.
    + rewrite SPu. apply (LB.decode_leafb_rng_journal B STK sp0 FP ly S W0 memS md0 own ly2 S2 W2 memT mdT k
        (sp - LLCc.CHECK_LATEST_CONTROL_FRAME) LLCc.CHECK_LATEST_CONTROL_FRAME HJS);
        unfold LLCc.CHECK_LATEST_CONTROL_FRAME; lia.
    + exact (proj1 (LB.decode_leafb_rng_cells W2)).
    + exact (proj2 (LB.decode_leafb_rng_cells W2)).
    + pose proof (LB.decode_leafb_rng_shadow W2 memT (sp + 8 + 32) 4 HRA ltac:(lia) ltac:(lia) ltac:(lia)) as Hr.
      rewrite (ie2a_shadow_one (sp + 8) 32 4) in Hr
        by first [exact Hfp8 | lia | (vm_compute; let H := fresh in intro H; discriminate H)].
      exact Hr.
    + apply (LB.decode_leafb_rng_journal B STK sp0 FP ly S W0 memS md0 own ly2 S2 W2 memT mdT k (sp + 8 + 32) 4 HJS);
        lia.
    + unfold LLCc.CHECK_LATEST_CONTROL_HOST, TW.A_M_host_counter, TW.OFF_M.
      apply ie2a_rng_G; [lia | lia |]. intros a Ha. apply ie2a_inG_M. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* Carrying the cut                                                    *)
(* ------------------------------------------------------------------ *)

(* What ios_fix gives about the stack. *)
Lemma ie2a_geo : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world segs) memc mdc k regs p frame Bw,
  ios_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw ->
  @AR rc segs B lyc Sc W memc mdc /\ YM05.alloc_ceiling <= sp0 - STK /\ sp0 - STK <= spZ regs - IOSEND_STK /\
  spZ regs <= sp0 /\ sp0 <= 2 ^ 47 /\ sp0 mod 16 = 0 /\ spZ regs mod 16 = 0.
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw HFX.
  destruct HFX as (HJ & _ & _ & _ & _ & _ & _ & Hal & Hlo & Hhi & _).
  pose proof HJ as (HSTK & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
  pose proof HJi as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (H16 & HSTK0 & Hceil & Hslo & Hshi & H47 & _).
  split; [exact HAR|]. repeat split; lia.
Qed.

(* The part of ios_fix that names neither the memory nor the world: the frame's placement against io_send's stack
   window, and the window itself. *)
Definition ie2a_fix (STK sp0 : Z) (regs : bvmap 5 word) (p : Z) (frame : list byte) : Prop :=
  0 < p /\ 0 < Z.of_nat (length frame) /\
  decode_off_win regs IOSEND_STK p (Z.of_nat (length frame)) /\
  spZ regs mod 16 = 0 /\ sp0 - STK <= spZ regs - IOSEND_STK /\ spZ regs <= sp0 /\
  YM05.alloc_ceiling <= spZ regs - IOSEND_STK /\ spZ regs <= 2 ^ 47 /\
  YK0s.ret_ok (YK11.getr regs 1) /\ 4096 <= raZ regs /\
  YK11.getr regs 3 = w64 (as_gp B) /\ YK11.getr regs 4 = w64 (as_tp B).

(* A step of the walk that changes only bytes of io_send's stack window or bytes of G in its written range keeps the
   running kept fact (image A's io_send_seg_csf.v ics_kept_step). *)
Lemma ie2a_kept_step : forall G lyc Sc (W : world segs) memc mdc (W2 : world segs) mem2 mem3 slo shi (E Zs : Z -> Prop),
  AR_laws segs B -> gx_ok segs B G ->
  @AR rc segs B lyc Sc W memc mdc ->
  acall_kept_g segs B G lyc Sc W memc W2 mem2 slo shi E ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview segs (w_H W2) mem3 a = aview segs (w_H W2) mem2 a) ->
  (forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) mem3 a) ->
  (forall a, Zs a -> (slo <= a < shi) \/ (inG G a /\ E a)) ->
  YM05.alloc_ceiling <= slo -> shi <= 2 ^ 47 ->
  acall_kept_g segs B G lyc Sc W memc W2 mem3 slo shi E.
Proof.
  intros G lyc Sc W memc mdc W2 mem2 mem3 slo shi E Zs LAWS HGX HAR (K1 & K2 & K3 & K4 & K5 & K6) Hkp Hgr HZ Hce Hhi.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (GLOW : forall a, inG G a -> 0 <= a < kLowMemEnd)
    by (intros a Ha; exact (transportb_segs_low a (proj1 (HGX a Ha)))).
  split; [|split; [|split; [|split; [|split]]]].
  - intros a Ha Hw. rewrite Hkp; [apply K1; [exact Ha | exact Hw] | lia |].
    intros HZa. destruct (HZ a HZa) as [Hs | [Hg _]]; [exact (Hw Hs) | pose proof (GLOW a Hg); lia].
  - intros b m i Hb Hi Hn. destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hb) as (_ & H4096 & Hbc & _).
    rewrite Hkp; [apply (K2 b m i Hb Hi Hn) | lia |].
    intros HZa. destruct (HZ _ HZa) as [Hs | [_ He]]; [lia | exact (Hn He)].
  - intros a Hi HnG Hno He. pose proof (transportb_segs_low a Hi) as Hlow.
    rewrite Hkp; [apply K3; [exact Hi | exact HnG | exact Hno | exact He] | lia |].
    intros HZa. destruct (HZ _ HZa) as [Hs | [Hg _]]; [lia | exact (HnG Hg)].
  - intros cid pos a Hin Hr Hn.
    destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (F4096 & Fce & _).
    pose proof (fs_frame_bytes_nonneg cid) as Hfs.
    assert (Ha : 0 <= a < YM05.alloc_ceiling).
    { destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [lia|].
      pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hfs) as Hse.
      assert (Hd : (frame_addr lyc cid pos + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
      pose proof (Z.div_pos (frame_addr lyc cid pos) 8 ltac:(lia) ltac:(lia)).
      unfold shadow_addr, SHADOW_OFF in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia. }
    rewrite Hkp; [apply (K4 cid pos a Hin Hr Hn) | lia |].
    intros HZa. destruct (HZ _ HZa) as [Hs | [_ He]]; [lia | exact (Hn He)].
  - intros a Ha Hw Hp. apply Hgr. apply K5; [exact Ha | exact Hw | exact Hp].
  - intros a Ha. apply Hgr. apply K6. exact Ha.
Qed.

(* A stretch that writes only inside [lo, hi), a leaf's own frame, keeps every memory fact of the cut: the harness
   globals and the shadow band lie below 2 ^ 45, the struct and the saved words above sp - IOSEND_FRAME, and the frame
   outside io_send's whole stack window (ios_fix's decode_off_win). The journal, the registers and the world the
   stretch moves to come from the stretch itself (image A's io_send_seg_e2.v ios_e2_keep). *)
Lemma ie2a_keep : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world segs) memc k
    (regs : bvmap 5 word) (p : Z) (frame : list byte) (fail : Z)
    ly3 S3 (W3 : world segs) mem3 md3 (regs3 : bvmap 5 word) mem4 md4 (regs4 : bvmap 5 word) Bx (lo hi : Z),
  AR_laws segs B ->
  0 < p -> 0 < Z.of_nat (length frame) ->
  decode_off_win regs IOSEND_STK p (Z.of_nat (length frame)) ->
  2 ^ 46 <= spZ regs <= 2 ^ 47 ->
  spZ regs - IOSEND_STK <= lo -> hi <= spZ regs - IOSEND_FRAME -> 2 ^ 45 <= lo ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) ->
     aview segs (w_H W3) mem4 a = aview segs (w_H W3) mem3 a) ->
  ios_e2_at B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame fail
    ly3 S3 W3 mem3 md3 regs3 Bx ->
  ios_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs frame ly3 S3 W3 mem4 md4 ->
  ios_regs regs regs4 p frame fail ->
  (forall r, 24 <= r <= 27 -> YK11.getr regs4 (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)) ->
  ios_e2_at B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame fail
    ly3 S3 W3 mem4 md4 regs4 Bx.
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame fail
    ly3 S3 W3 mem3 md3 regs3 mem4 md4 regs4 Bx lo hi
    LAWS Hp0 Hn0 HOFF HSP Hlo Hhi H45 KV AT CUR RG R24.
  destruct AT as (CUR3 & SAVED & RG3 & R243 & SFR & SRCS & GARR & SRCF & HTW).
  assert (EF : IOSEND_FRAME = 160) by reflexivity.
  assert (EO : IOS_F_OFF = 8) by reflexivity.
  assert (ES : SF_SIZE = 80) by reflexivity.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof CUR3 as (HJ3 & _).
  pose proof HJ3 as (_ & _ & (memS3 & HJi3 & _) & _). rewrite !Z.add_0_r in HJi3.
  pose proof (proj1 HJi3) as HAR3.
  (* where the frame lies: a heap block or a fake frame below alloc_ceiling, or the machine stack *)
  pose proof (trans_src_ok_place B LAWS ly3 S3 W3 mem3 md3 p (Z.of_nat (length frame)) HAR3 SRCF
                ltac:(lia)) as HPL.
  assert (KFR : forall a, p <= a < p + Z.of_nat (length frame) -> ~ (lo <= a < hi))
    by (intros a Ha; unfold decode_off_win in HOFF; lia).
  assert (KSF : forall a, spZ regs - IOSEND_FRAME + IOS_F_OFF <= a <
                          spZ regs - IOSEND_FRAME + IOS_F_OFF + SF_SIZE -> ~ (lo <= a < hi))
    by (intros a Ha; lia).
  assert (KSH : forall s, kLowMemEnd <= s < kHighShadowEnd ->
                  aview segs (w_H W3) mem4 s = aview segs (w_H W3) mem3 s)
    by (intros s Hs; apply KV; lia).
  split; [exact CUR|].
  split.
  { (* the saved words *)
    apply (ie2a_saved_kept W3 W3 mem3 mem4 regs SAVED).
    intros a Ha. apply KV; lia. }
  split; [exact RG|]. split; [exact R24|].
  split.
  { (* the struct *)
    apply (ie2a_sframe_kept W3 W3 mem3 mem4 _ p (TC.rf frame) SFR).
    intros a Ha. apply KV; [lia | apply KSF; lia]. }
  split.
  { exact (trans_src_ok_view B ly3 S3 W3 W3 mem3 mem4
            (spZ regs - IOSEND_FRAME + IOS_F_OFF) SF_SIZE SRCS
            (fun a Ha => KV a ltac:(lia) (KSF a Ha)) KSH). }
  split.
  { (* the frame *)
    apply (ie2a_garr8_kept (w_H W3) (w_H W3) mem3 mem4 p (map DSpec.bz frame) GARR).
    intros a Ha. rewrite length_map in Ha.
    apply KV; [destruct HPL as [Pl|Pl]; lia | apply KFR; lia]. }
  split.
  { exact (trans_src_ok_view B ly3 S3 W3 W3 mem3 mem4 p (Z.of_nat (length frame)) SRCF
            (fun a Ha => KV a ltac:(destruct HPL as [Pl|Pl]; lia) (KFR a Ha)) KSH). }
  (* the world *)
  apply (tw_kept TMAP_B (aview segs (w_H W3) mem3) _ Bx HTW).
  intros x Hx. pose proof (TMAP_B_hull x Hx) as Hh.
  unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh. apply KV; lia.
Qed.

(* ie2a_keep for the stretch that writes the two words of G instead of bytes below sp: no other fact of the cut reads
   them (the saved words and the struct lie above sp - IOSEND_FRAME, the shadow band above kLowMemEnd, the frame
   outside G or inside g_s), so every fact but the world relation survives; the world after the stores comes in as a
   premise. *)
Lemma ie2a_keep_g : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world segs) memc k
    (regs : bvmap 5 word) (p : Z) (frame : list byte) (fail : Z)
    ly3 S3 (W3 : world segs) mem3 md3 (regs3 : bvmap 5 word) mem4 md4 (regs4 : bvmap 5 word) Bx By,
  AR_laws segs B ->
  ie2a_fix STK sp0 regs p frame -> 60 <= Z.of_nat (length frame) ->
  iosend_frame_at p (Z.of_nat (length frame)) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ ie2a_wr a ->
     aview segs (w_H W3) mem4 a = aview segs (w_H W3) mem3 a) ->
  ios_e2_at B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame fail
    ly3 S3 W3 mem3 md3 regs3 Bx ->
  ios_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs frame ly3 S3 W3 mem4 md4 ->
  ios_regs regs regs4 p frame fail ->
  (forall r, 24 <= r <= 27 -> YK11.getr regs4 (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)) ->
  tw_at TMAP_B (aview segs (w_H W3) mem4) By ->
  ios_e2_at B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame fail
    ly3 S3 W3 mem4 md4 regs4 By.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame fail
  ly3 S3 W3 mem3 md3 regs3 mem4 md4 regs4 Bx By LAWS FIX H60 HFAT KV AT CUR RG R24 HTW4.
destruct AT as (CUR3 & SAVED & RG3 & R243 & SFR & SRCS & GARR & SRCF & HTW).
destruct FIX as (Hp0 & Hn0 & Hoff & Hsp16 & Hslo & Hshi & Hce & H47 & Hra & Hra4 & Hgp & Htp).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (EF : IOSEND_FRAME = 160) by reflexivity.
assert (EO : IOS_F_OFF = 8) by reflexivity.
assert (ES : SF_SIZE = 80) by reflexivity.
assert (EIS : IOSEND_STK = 8512) by reflexivity.
assert (EG : TB_GOT = 0x5e4f60) by reflexivity.
assert (EL : TB_g_last_counter = 0x5dedc0) by reflexivity.
assert (HSP : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
pose proof CUR3 as (HJ3 & _).
pose proof HJ3 as (_ & _ & (memS3 & HJi3 & _) & _). rewrite !Z.add_0_r in HJi3.
pose proof (proj1 HJi3) as HAR3.
(* where the frame lies: a heap block or a fake frame below alloc_ceiling, G, or the machine stack *)
pose proof (trans_src_ok_place B LAWS ly3 S3 W3 mem3 md3 p (Z.of_nat (length frame)) HAR3 SRCF
              ltac:(lia)) as HPL.
assert (KSH : forall s, kLowMemEnd <= s < kHighShadowEnd ->
                aview segs (w_H W3) mem4 s = aview segs (w_H W3) mem3 s).
{ intros s Hs. apply KV; [lia|]. intros [HW | HW]; lia. }
split; [exact CUR|].
split.
{ (* the nine saved words, far above G *)
  apply (ie2a_saved_kept W3 W3 mem3 mem4 regs SAVED).
  intros a Ha. apply KV; [lia|]. intros [HW | HW]; lia. }
split; [exact RG|]. split; [exact R24|].
split.
{ (* the struct spec_frame at sp + 8 *)
  apply (ie2a_sframe_kept W3 W3 mem3 mem4 _ p (TC.rf frame)); [exact SFR|].
  intros a Ha. apply KV; [lia|]. intros [HW | HW]; lia. }
split.
{ exact (trans_src_ok_view B ly3 S3 W3 W3 mem3 mem4
          (spZ regs - IOSEND_FRAME + IOS_F_OFF) SF_SIZE SRCS
          (fun a Ha => KV a ltac:(lia) ltac:(intros [HW | HW]; lia)) KSH). }
split.
{ (* the frame's bytes *)
  apply (ie2a_garr8_kept (w_H W3) (w_H W3) mem3 mem4 p (map DSpec.bz frame) GARR).
  intros a Ha. rewrite length_map in Ha.
  apply KV; [destruct HPL as [Pl|Pl]; lia | exact (ie2a_frame_off p (Z.of_nat (length frame)) a HFAT Ha)]. }
split.
{ exact (trans_src_ok_view B ly3 S3 W3 W3 mem3 mem4 p (Z.of_nat (length frame)) SRCF
          (fun a Ha => KV a ltac:(destruct HPL as [Pl|Pl]; lia)
                         (ie2a_frame_off p (Z.of_nat (length frame)) a HFAT Ha)) KSH). }
exact HTW4.
Qed.

(* ------------------------------------------------------------------ *)
(* The symbolic states                                                 *)
(* ------------------------------------------------------------------ *)

Lemma ie2a_e0_entry : forall (W : world segs) (regs : bvmap 5 word) mem pc,
  st_ok_pi segs VAL (ie2a_E0 regs) (ie2a_ss0 pc)
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + pc)) mem (YK11.seg_rom segs))).
Proof.
intros W regs mem pc. rewrite restrict_mkst_fx. unfold ie2a_ss0.
apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
- apply regs_ok_Eimg_Ereg.
- reflexivity.
- constructor.
- apply pairwise_disjoint_of_extents. cbn. tauto.
- unfold facts_ok. cbn. repeat constructor.
Qed.

Lemma ie2a_e0_agree : forall regs, env_agree 32 (Ereg regs []) (ie2a_E0 regs).
Proof.
intros regs. split; [|reflexivity]. intros n Hn. unfold ie2a_E0. rewrite Eimg_low by (unfold A_TEXT; lia). reflexivity.
Qed.

(* The listing's values of object 29 (GOT.e2) and of the two %hi slots the stores use. *)
Lemma ie2a_vals : VAL (A_OBJ 29) = TB_GOT + 196 /\ VAL (A_HI 55) = TB_GOT + 196 + 248 /\
  VAL (A_HI 56) = TB_g_last_counter + 884.
Proof. repeat split; vm_compute; reflexivity. Qed.

(* The walk's valuation: the 32 registers of the cut, then GOT.e2 and f.send. *)
Definition ie2a_E (regs : bvmap 5 word) (e2 snd4 : Z) : env :=
  Eimg (PI := PI_transportb) (Ereg regs [Z_to_bv 64 e2; Z_to_bv 64 snd4]).

Lemma ie2a_agree : forall regs e2 snd4,
  env_agree 32 (Ereg regs [Z_to_bv 64 e2; Z_to_bv 64 snd4]) (ie2a_E regs e2 snd4).
Proof.
  intros. split; [intros n Hn; unfold ie2a_E; apply Eimg_low; unfold A_TEXT; lia | reflexivity].
Qed.

(* The state the token engine runs from at 0x8311c: the three regions at their bases, the %hi alias of GOT.e2, and
   the registers as atoms. The two written words are bytes of G (writable at any memory, TransportGCg.v
   gx_rw_writable with TransportGRwB.v G_HARNESS_B_rw). *)
Lemma ie2a_state : forall (pc sp e2 snd4 : Z) (W : world segs) (regs : bvmap 5 word) mem,
  YK11.getr regs 2 = w64 sp -> 2 ^ 46 <= sp -> sp + 160 <= 2 ^ 47 ->
  0 <= e2 < 2 ^ 32 -> 0 <= snd4 < 2 ^ 32 ->
  YI04.val_mem segs (mrestrict (w_H W) mem) (sp + 40) 4 snd4 ->
  YI04.val_mem segs (mrestrict (w_H W) mem) (TB_GOT + 196 + 0) 4 e2 ->
  st_ok_pi segs VAL (ie2a_E regs e2 snd4) (ie2a_ss pc)
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + pc)) mem (YK11.seg_rom segs))).
Proof.
  intros pc sp e2 snd4 W regs mem Hsp2 Hlo Hhi He2 Hsnd V40 Ve2.
  assert (EG : TB_GOT = 0x5e4f60) by reflexivity.
  assert (EL : TB_g_last_counter = 0x5dedc0) by reflexivity.
  destruct ie2a_vals as (V29 & V55 & V56).
  set (E := ie2a_E regs e2 snd4).
  assert (EOB : forall j, (A_TEXT <= j < A_LIM)%nat -> ew E j = Z_to_bv 64 (VAL j))
    by (intros j Hj; unfold E, ie2a_E; apply Eimg_img; exact Hj).
  assert (E2 : ew E 2 = YK11.getr regs 2)
    by (unfold E, ie2a_E; apply ew_Eimg_Ereg_nat; reflexivity).
  assert (Usp : bv_unsigned (ew E 2) = sp)
    by (rewrite E2, Hsp2; apply unsigned_lit_small; lia).
  assert (X32 : ew E 32 = Z_to_bv 64 e2)
    by (unfold E, ie2a_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (X33 : ew E 33 = Z_to_bv 64 snd4)
    by (unfold E, ie2a_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
  assert (U29 : base_val E (Some (A_OBJ 29)) = TB_GOT + 196).
  { cbn [base_val]. rewrite (EOB (A_OBJ 29) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)), V29.
    apply unsigned_lit_small. lia. }
  assert (U56 : base_val E (Some (A_HI 56)) = TB_g_last_counter + 884).
  { cbn [base_val]. rewrite (EOB (A_HI 56) ltac:(unfold A_HI, A_TEXT, A_LIM; lia)), V56.
    apply unsigned_lit_small. lia. }
  assert (U55 : bv_unsigned (ew E (A_HI 55)) = TB_GOT + 196 + 248).
  { rewrite (EOB (A_HI 55) ltac:(unfold A_HI, A_TEXT, A_LIM; lia)), V55. apply unsigned_lit_small. lia. }
  assert (WG : forall a, inG TG.G_HARNESS_B a -> writable_at segs (mrestrict (w_H W) mem) a)
    by (intros a Ha; exact (gx_rw_writable segs TG.G_HARNESS_B a G_HARNESS_B_rw Ha _)).
  rewrite restrict_mkst_fx. unfold ie2a_ss, ie2a_regions.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute; reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
    + unfold ie2a_rstk, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite Usp. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val segs E _ sp 40 4 (SOff 33 0) snd4);
        [cbn [sv_denot]; rewrite X33, Z.add_0_r; apply Z_to_bv_bv_unsigned | cbn; lia | cbn; lia | exact V40].
    + unfold ie2a_re2, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      rewrite U29. split; [lia|]. split; [lia|]. split.
      * intros o Ho. apply WG. apply (ios_inG_row _ _ _ _ TMAP_B_GOT). unfold TW.SZ_GOT. lia.
      * apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val segs E _ (TB_GOT + 196) 0 4 (SOff 32 0) e2);
          [cbn [sv_denot]; rewrite X32, Z.add_0_r; apply Z_to_bv_bv_unsigned | cbn; lia | cbn; lia | exact Ve2].
    + unfold ie2a_rlc, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      rewrite U56. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. apply WG. apply (ios_inG_row _ _ _ _ TMAP_B_g_last_counter).
      unfold TW.SZ_g_last_counter. lia.
  - apply pairwise_disjoint_of_extents.
    unfold ie2a_rstk, ie2a_re2, ie2a_rlc, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite U29, U56. cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; first [exact I | lia].
  - unfold ie2a_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    split; [exact I|]. split; [exact I|]. split; [|exact I].
    cbn [sv_denot]. rewrite U55, (EOB (A_OBJ 29) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)), V29.
    rewrite unsigned_lit_small by lia. f_equal; lia.
Qed.

(* The values the stretch reads, where the engine reads them: f.send through check_sent_frame_cg.v trans_sframe_at
   and ie2a_val_of_garr8, GOT.e2 through TWorldG.v tw_read_val at the GOT row of TMAP_B. *)
Lemma ie2a_cut_vals : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world segs) memc k
    (regs : bvmap 5 word) (p : Z) (frame : list byte) (fail : Z)
    ly3 S3 (W3 : world segs) mem3 md3 (regs3 : bvmap 5 word) Bx,
  ios_e2_at B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame fail
    ly3 S3 W3 mem3 md3 regs3 Bx ->
  YI04.val_mem segs (mrestrict (w_H W3) mem3) (spZ regs - IOSEND_FRAME + 40) 4 (ie2a_snd frame) /\
  YI04.val_mem segs (mrestrict (w_H W3) mem3) (TB_GOT + 196 + 0) 4 (ie2a_e2v Bx) /\
  0 <= ie2a_snd frame < 2 ^ 32 /\ 0 <= ie2a_e2v Bx < 2 ^ 32.
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame fail ly3 S3 W3 mem3 md3 regs3 Bx AT.
  destruct AT as (_ & _ & _ & _ & SFR & _ & _ & _ & HTW).
  destruct SFR as (_ & _ & SB & HG & HL & _ & _ & _ & _ & _ & _ & _ & HSND & _).
  assert (EO : IOS_F_OFF = 8) by reflexivity.
  assert (ESND : ie2a_snd frame = TW.u_at SB 32 4) by (unfold ie2a_snd; rewrite HSND; reflexivity).
  pose proof (ie2a_val_of_garr8 (mrestrict (w_H W3) mem3) (spZ regs - IOSEND_FRAME + IOS_F_OFF) 32 SB 4 HG
                ltac:(lia) ltac:(rewrite HL; cbn; lia)) as R32.
  split. { rewrite ESND. replace (spZ regs - IOSEND_FRAME + 40)
             with (spZ regs - IOSEND_FRAME + IOS_F_OFF + 32) by lia. exact R32. }
  split.
  { exact (tw_read_val segs (mrestrict (w_H W3) mem3) TMAP_B Bx TW.OFF_GOT TB_GOT TW.SZ_GOT 196 4
             TMAP_B_ok HTW TMAP_B_GOT ltac:(lia) ltac:(unfold TW.SZ_GOT; lia)). }
  pose proof (TWL.u_at_range SB 32 4) as Q2.
  pose proof (TWL.u_at_range Bx TW.A_GOT_e2 4) as Q5.
  change (8 * Z.of_nat 4) with 32 in Q2, Q5.
  unfold ie2a_e2v. rewrite ESND. split; lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The two leaf calls (0x83110 .. 0x83118)                             *)
(* ------------------------------------------------------------------ *)

(* From the E2 arm's head to the return of check_latest_control: `PCall` check_state_wake, a0 = sp + 8, `PCall`
   check_latest_control. Neither callee writes a byte of G or of io_send's frame, so the cut and its world reach
   0x8311c unchanged. *)
Lemma ie2a_calls : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world segs) memc mdc k
    (regs : bvmap 5 word) (p : Z) (frame : list byte) (fail : Z)
    ly3 S3 (W3 : world segs) mem3 md3 (regs3 : bvmap 5 word) Bx (Q : world segs -> config -> Prop),
  transport_cells B -> AR_laws segs B -> gx_ok segs B TG.G_HARNESS_B ->
  (forall fx' : YK11.FPState, @transport_leaf_at rc B (@LSW.transport_check_state_wake_cg) fx') ->
  (forall fx' : YK11.FPState, @transport_leaf_at rc B (@LLC.transport_check_latest_control_cg) fx') ->
  @AR rc segs B lyc Sc W memc mdc ->
  ie2a_fix STK sp0 regs p frame -> 60 <= Z.of_nat (length frame) ->
  ios_e2_at B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame fail
    ly3 S3 W3 mem3 md3 regs3 Bx ->
  TC.check_state_wake_m Bx = Some (Bx, tt) ->
  TC.check_latest_control_m Bx frame = Some (Bx, tt) ->
  (forall mem5 md5 regs5,
     ios_e2_at B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame fail
       ly3 S3 W3 mem5 md5 regs5 Bx ->
     SRr segs W3 (@cfg_at fx segs (transportb_text + IOS_AT 0x120) regs5 mem5 md5) Q) ->
  SRr segs W3 (@cfg_at fx segs (transportb_text + IOS_E2ARM) regs3 mem3 md3) Q.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame fail
  ly3 S3 W3 mem3 md3 regs3 Bx Q HCELLS LAWS HGX LCSW LCLC HARc FIX H60 AT HMW HMC HK.
pose proof AT as AT0.
destruct FIX as (Hp0 & Hn0 & Hoff & Hsp16 & Hslo & Hshi & Hce & H47r & Hra & Hra4 & Hgp & Htp).
destruct AT as (CUR & SAVED & RG & R24 & SFR & SRCS & GARR & SRCF & HTW).
pose proof CUR as (HJ & HFR & HPM & HMO & HKEPT).
pose proof RG as (R2 & R3 & R4 & R8 & R9 & R19 & R20).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FS : IOSEND_STK = 8512) by reflexivity.
assert (FF : IOSEND_FRAME = 160) by reflexivity.
assert (EST : ESTACK = 4096) by reflexivity.
assert (GHI : TG.G_HARNESS_B_HI = 0x5f2e10) by reflexivity.
assert (EO : IOS_F_OFF = 8) by reflexivity.
assert (HSP : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
(* the entry sp of the walk, from the journal inside ios_cur *)
pose proof HJ as (HSTKj & _ & (memS0 & HJ0 & _) & _). rewrite !Z.add_0_r in HJ0.
pose proof HJ0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hsp0a & HSTK0 & Hceil0 & Hslo1 & Hshi1 & H47 & _).
clear HJ0 memS0.
set (sp := spZ regs - IOSEND_FRAME) in *.
assert (Esp : sp = spZ regs - IOSEND_FRAME) by reflexivity.
assert (Hsp16' : sp mod 16 = 0).
{ rewrite Esp, FF. replace (spZ regs - 160) with (spZ regs + (-10) * 16) by lia.
  rewrite Z_mod_plus_full. exact Hsp16. }
assert (Hsp3 : spZ regs3 = sp)
  by (unfold spZ at 1; rewrite R2; apply unsigned_lit_small; lia).
change IOS_F_OFF with 8 in SFR, SRCS.
(* ---- run 1 (0x83110): `PCall` check_state_wake ---- *)
set (E0 := ie2a_E0 regs3).
assert (HEI : img_env VAL A_LIM E0) by (unfold E0, ie2a_E0; apply Eimg_env).
pose proof (ie2a_e0_entry W3 regs3 mem3 (IOS_AT 0x114)) as HS. fold E0 in HS.
assert (SHOK : sh_ok segs ie2a_Bx [] E0 (mrestrict (w_H W3) mem3)) by constructor.
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
              TG.G_HARNESS_B HGX 0 []) as RUN.
unfold cfg_at.
lazymatch goal with |- SRr _ ?Wx _ ?Qx =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx regs3 (Z_to_bv 64 (BASE + IOS_AT 0x114)) mem3
    (YK11.seg_rom segs)) md3) Qx) end.
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ ie2a_awr_nil. }
ie2a_md md1. rename ms into ms1.
assert (KC1 : forall a, 0 <= a < 2 ^ 64 ->
  aview segs (w_H W3) (ms_mem ms1) a = aview segs (w_H W3) mem3 a).
{ intros a Ha. apply (kept_of_frame _ _ _ _ _ (fun _ : Z => False) HFr); [| exact Ha | intros []].
  intros b wlo whi x Hin Hx. exfalso. vm_compute in Hin. exact Hin. }
assert (GC1 : forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) (ms_mem ms1) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
clear HF HFr HG.
assert (HPC1 : aregs_preserved regs3 (ms_regs ms1)).
{ apply (aregs_preserved_of_st_ok segs (w_H W3) E0 _ ms1 regs3 [] HS).
  - exact (ie2a_e0_agree regs3).
  - vm_compute. reflexivity. }
pose proof (ie2a_kept_of_pres regs3 (ms_regs ms1) HPC1) as KR1.
pmkst HS.
ie2a_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + IOS_AT 0x118)) Q1 ltac:(apply codeptr_val; exact HEI).
assert (Q2 : YK11.getr (ms_regs ms1) 2 = w64 sp)
  by (rewrite (KR1 2%bv ltac:(unfold ie2a_kept; cbn [In]; tauto)); exact R2).
assert (Q3 : YK11.getr (ms_regs ms1) 3 = w64 (as_gp B))
  by (rewrite (KR1 3%bv ltac:(unfold ie2a_kept; cbn [In]; tauto)), R3; exact Hgp).
assert (Q4 : YK11.getr (ms_regs ms1) 4 = w64 (as_tp B))
  by (rewrite (KR1 4%bv ltac:(unfold ie2a_kept; cbn [In]; tauto)), R4; exact Htp).
assert (Hspc1 : spZ (ms_regs ms1) = sp)
  by (unfold spZ at 1; rewrite Q2; apply unsigned_lit_small; lia).
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Qx =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transportb_sigma TB_check_state_wake)) mm rom) mdx) Qx)
  end.
apply (ie2a_leaf_call W3 (ms_regs ms1) (ms_mem ms1) STK sp0 FP ly S W0 mem0 md0 own ly3 S3 md1 (k + 0)
  (sp - sp0) (transportb_sigma TB_check_state_wake) (fun _ => Bx = Bx) Q LAWS HJ).
- rewrite Hspc1. lia.
- rewrite Esp, FF. replace (spZ regs - 160 - sp0) with (spZ regs - sp0 + (-10) * 16) by lia.
  rewrite Z_mod_plus_full, Zminus_mod, Hsp16, Hsp0a. reflexivity.
- lia.
- lia.
- rewrite Q1. apply (ret_ok_codeptr_v (PI := PI_transportb));
    [unfold IOS_AT, DgnTransportBList.AF_io_send; lia | reflexivity].
- exact Q3.
- exact Q4.
- intros HPRE.
  apply (ie2a_csw_leaf W3 (ms_regs ms1) (ms_mem ms1) md1 ly3 S3 Bx LCSW); [| exact HMW | lia | lia | exact HPRE].
  apply (tw_kept TMAP_B _ _ Bx HTW). intros x Hx. pose proof (TMAP_B_hull x Hx) as Hh.
  unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh. apply KC1. lia.
- intros regs4 mem4 md4 HJ4 HP4 HK4 HG4 _.
  rewrite Q1.
  assert (KR2 : forall r, In r ie2a_kept -> YK11.getr regs4 r = YK11.getr regs3 r)
    by (intros r Hr; rewrite (ie2a_kept_of_pres _ _ HP4 r Hr); exact (KR1 r Hr)).
  assert (KV2 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp - ESTACK <= a < sp) ->
    aview segs (w_H W3) mem4 a = aview segs (w_H W3) mem3 a).
  { intros a Ha Hn. rewrite (HK4 a Ha ltac:(rewrite Hspc1; exact Hn)). exact (KC1 a Ha). }
  assert (GV2 : forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) mem4 a)
    by (intros a Ha; exact (HG4 a (GC1 a Ha))).
  (* ---- run 2 (0x83114): a0 = sp + 8; `PCall` check_latest_control ---- *)
  set (E1 := ie2a_E0 regs4).
  assert (HEI1 : img_env VAL A_LIM E1) by (unfold E1, ie2a_E0; apply Eimg_env).
  pose proof (ie2a_e0_entry W3 regs4 mem4 (IOS_AT 0x118)) as HS1. fold E1 in HS1.
  assert (SHOK1 : sh_ok segs ie2a_Bx [] E1 (mrestrict (w_H W3) mem4)) by constructor.
  clear HS SHOK.
  rename HJ4 into HJ1.
  paj_run_tok RUN HS1 HJ1 SHOK1 YC4b.Bspan.
  { ie2a_awr_nil. }
  ie2a_md md2. rename ms into ms2.
  assert (KC3 : forall a, 0 <= a < 2 ^ 64 ->
    aview segs (w_H W3) (ms_mem ms2) a = aview segs (w_H W3) mem4 a).
  { intros a Ha. apply (kept_of_frame _ _ _ _ _ (fun _ : Z => False) HFr); [| exact Ha | intros []].
    intros b wlo whi x Hin Hx. exfalso. vm_compute in Hin. exact Hin. }
  assert (GC3 : forall a, apresent (w_H W3) mem4 a -> apresent (w_H W3) (ms_mem ms2) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
  clear HF HFr HG.
  assert (HPC2 : aregs_preserved regs4 (ms_regs ms2)).
  { apply (aregs_preserved_of_st_ok segs (w_H W3) E1 _ ms2 regs4 [] HS1).
    - exact (ie2a_e0_agree regs4).
    - vm_compute. reflexivity. }
  pose proof (ie2a_kept_of_pres regs4 (ms_regs ms2) HPC2) as KR3.
  pmkst HS1.
  ie2a_reg HS1 (1%bv : bv 5) (Z_to_bv 64 (BASE + IOS_AT 0x120)) P1 ltac:(apply codeptr_val; exact HEI1).
  ie2a_reg HS1 (10%bv : bv 5) (Z_to_bv 64 (sp + 8)) P10
    ltac:(cbn [sv_denot];
          rewrite (ew_Eimg_Ereg_nat regs4 (@nil word) 2%nat 2%bv eq_refl),
                  (KR2 2%bv ltac:(unfold ie2a_kept; cbn [In]; tauto)), R2;
          rewrite unsigned_lit_small by lia; reflexivity).
  assert (P2 : YK11.getr (ms_regs ms2) 2 = w64 sp).
  { rewrite (KR3 2%bv ltac:(unfold ie2a_kept; cbn [In]; tauto)),
            (KR2 2%bv ltac:(unfold ie2a_kept; cbn [In]; tauto)). exact R2. }
  assert (P3 : YK11.getr (ms_regs ms2) 3 = w64 (as_gp B)).
  { rewrite (KR3 3%bv ltac:(unfold ie2a_kept; cbn [In]; tauto)),
            (KR2 3%bv ltac:(unfold ie2a_kept; cbn [In]; tauto)), R3. exact Hgp. }
  assert (P4 : YK11.getr (ms_regs ms2) 4 = w64 (as_tp B)).
  { rewrite (KR3 4%bv ltac:(unfold ie2a_kept; cbn [In]; tauto)),
            (KR2 4%bv ltac:(unfold ie2a_kept; cbn [In]; tauto)), R4. exact Htp. }
  assert (Hspc2 : spZ (ms_regs ms2) = sp)
    by (unfold spZ at 1; rewrite P2; apply unsigned_lit_small; lia).
  (* the struct and the world at the call state *)
  assert (HSF2 : trans_sframe_at W3 (ms_mem ms2) (sp + 8) p (TC.rf frame)).
  { apply (ie2a_sframe_kept W3 W3 mem3 (ms_mem ms2) (sp + 8) p (TC.rf frame)); [exact SFR|].
    intros a Ha. rewrite (KC3 a ltac:(lia)). apply KV2; lia. }
  assert (HTW2 : tw_at TMAP_B (aview segs (w_H W3) (ms_mem ms2)) Bx).
  { apply (tw_kept TMAP_B _ _ Bx HTW). intros x Hx. pose proof (TMAP_B_hull x Hx) as Hh.
    unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh.
    rewrite (KC3 x ltac:(lia)). apply KV2; lia. }
  assert (HWIN : ie2a_call_win STK sp0 sp) by (split; [exact Hsp16' | split; lia]).
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Qx =>
    change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 LLCc.CHECK_LATEST_CONTROL) mm rom) mdx) Qx) end.
  eapply SRr_bind.
  { refine (ie2a_call_clc STK sp0 FP ly S W0 mem0 md0 own ly3 S3 W3 (ms_mem ms2) _ (k + 0)
      (ms_regs ms2) sp p frame Bx HCELLS LAWS LCLC HJ1 _ _ _ _ _ HWIN HSF2 HTW2 HMC).
    - rewrite ie2a_i2. exact P2.
    - rewrite ie2a_i10. exact P10.
    - rewrite ie2a_i1, P1. apply (ret_ok_codeptr_v (PI := PI_transportb));
        [unfold IOS_AT, DgnTransportBList.AF_io_send; lia | reflexivity].
    - rewrite ie2a_i3. exact P3.
    - rewrite ie2a_i4. exact P4. }
  intros W4 c4 _ (-> & regs5 & mem5 & md5 & -> & HJ5 & HP5 & _ & HK5 & HG5 & _).
  rewrite ie2a_i1, P1.
  (* ---- the cut at 0x8311c ---- *)
  assert (KR4 : forall r, In r ie2a_kept -> YK11.getr regs5 r = YK11.getr regs3 r).
  { intros r Hr. rewrite (ie2a_kept_of_pres _ _ HP5 r Hr), (KR3 r Hr). exact (KR2 r Hr). }
  assert (KV4 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp - ESTACK <= a < sp) ->
    aview segs (w_H W3) mem5 a = aview segs (w_H W3) mem3 a).
  { intros a Ha Hn.
    rewrite (HK5 a Ha ltac:(rewrite Hspc2; exact Hn) ltac:(intros X; unfold LCK.in_wr in X; inversion X)).
    rewrite (KC3 a Ha). apply KV2; [exact Ha | exact Hn]. }
  assert (GV4 : forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) mem5 a)
    by (intros a Ha; exact (HG5 a (GC3 a (GV2 a Ha)))).
  assert (CUR5 : ios_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs frame
                   ly3 S3 W3 mem5 md5).
  { unfold ios_cur. split; [exact HJ5|]. split; [exact HFR|]. split; [exact HPM|]. split; [exact HMO|].
    apply (ie2a_kept_step TG.G_HARNESS_B lyc Sc W memc mdc W3 mem3 mem5
      (spZ regs - IOSEND_STK) (spZ regs) (iosend_wr (Z.of_nat (length frame)))
      (fun a => sp - ESTACK <= a < sp)
      LAWS HGX HARc HKEPT ltac:(intros a Ha Hn; exact (KV4 a Ha Hn)) GV4
      ltac:(intros a Ha; cbv beta in Ha; left; lia) ltac:(lia) ltac:(lia)). }
  destruct (ie2a_regs_step regs regs3 regs5 p frame fail RG R24 KR4) as (RG5 & R245).
  apply (HK mem5 md5 regs5).
  apply (ie2a_keep STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame fail
           ly3 S3 W3 mem3 md3 regs3 mem5 md5 regs5 Bx (sp - ESTACK) sp
           LAWS Hp0 Hn0 Hoff HSP ltac:(lia) ltac:(lia) ltac:(lia)
           ltac:(intros a Ha Hn; exact (KV4 a Ha Hn)) AT0 CUR5 RG5 R245).
Qed.

(* ------------------------------------------------------------------ *)
(* The counter, its overflow branch, the two stores and the branch      *)
(* (0x8311c .. 0x83144)                                                *)
(* ------------------------------------------------------------------ *)

(* From the return of check_latest_control: GOT.e2 + 1 (addiw) and its branch to the trap word, refuted by the
   model's int_inc; the stores of GOT.e2 + 1 and of f.send at g_last_counter; then the test of bit 0 of s3. Both stores
   are bytes of G in iosend_wr, so the running kept fact survives (ie2a_kept_step) and the world moves by two
   ios_tw_step. *)
Lemma ie2a_tail : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world segs) memc mdc k
    (regs : bvmap 5 word) (p : Z) (frame : list byte) (fail e2 : Z)
    ly3 S3 (W3 : world segs) mem3 md3 (regs3 : bvmap 5 word) Bx (Q : world segs -> config -> Prop),
  AR_laws segs B -> gx_ok segs B TG.G_HARNESS_B -> @AR rc segs B lyc Sc W memc mdc ->
  ie2a_fix STK sp0 regs p frame -> 60 <= Z.of_nat (length frame) ->
  iosend_frame_at p (Z.of_nat (length frame)) ->
  0 <= fail <= 1 ->
  TC.int_inc (TW.GOT_e2 Bx) = Some e2 ->
  ios_e2_at B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame fail
    ly3 S3 W3 mem3 md3 regs3 Bx ->
  (forall mem5 md5 regs5,
     ios_e2_at B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame fail
       ly3 S3 W3 mem5 md5 regs5
       (TW.set_g_last_counter (TW.set_GOT_e2 Bx e2) (DSpec.sf_send (TC.rf frame))) ->
     fail = 0 ->
     SRr segs W3 (@cfg_at fx segs (transportb_text + IOS_FLY) regs5 mem5 md5) Q) ->
  (forall mem5 md5 regs5,
     ios_e2_at B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame fail
       ly3 S3 W3 mem5 md5 regs5
       (TW.set_g_last_counter (TW.set_GOT_e2 Bx e2) (DSpec.sf_send (TC.rf frame))) ->
     fail <> 0 ->
     SRr segs W3 (@cfg_at fx segs (transportb_text + IOS_EPI) regs5 mem5 md5) Q) ->
  SRr segs W3 (@cfg_at fx segs (transportb_text + IOS_AT 0x120) regs3 mem3 md3) Q.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame fail e2
  ly3 S3 W3 mem3 md3 regs3 Bx Q LAWS HGX HARc FIX H60 HFAT Hfail Hinc AT HFLY HEPI.
pose proof AT as AT0.
pose proof FIX as FIX0.
destruct FIX as (Hp0 & Hn0 & Hoff & Hsp16 & Hslo & Hshi & Hce & H47r & Hra & Hra4 & Hgp & Htp).
destruct AT as (CUR & SAVED & RG & R24 & SFR & SRCS & GARR & SRCF & HTW).
pose proof CUR as (HJ & HFR & HPM & HMO & HKEPT).
pose proof RG as (R2 & R3 & R4 & R8 & R9 & R19 & R20).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (ie2a_cut_vals STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame fail
            ly3 S3 W3 mem3 md3 regs3 Bx AT0) as (V40 & Ve2 & Z2 & Z5).
assert (FS : IOSEND_STK = 8512) by reflexivity.
assert (FF : IOSEND_FRAME = 160) by reflexivity.
assert (EG : TB_GOT = 0x5e4f60) by reflexivity.
assert (EL : TB_g_last_counter = 0x5dedc0) by reflexivity.
assert (HSP : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
(* the model's counter: GOT.e2 is not INT_MAX, so GOT.e2 + 1 is a 32-bit signed value *)
destruct (ie2a_int_inc _ _ Hinc) as (Ee2 & NI).
pose proof (TWL.s32_range Bx TW.A_GOT_e2) as Se.
change (TW.s32_at Bx TW.A_GOT_e2) with (TW.GOT_e2 Bx) in Se.
assert (Hn3 : TW.GOT_e2 Bx + 1 < 2 ^ 31) by (unfold TC.INT_MAX in NI; lia).
assert (EGv : TW.GOT_e2 Bx = bv_swrap 32 (ie2a_e2v Bx)) by reflexivity.
(* the run's state: the three regions, with the GOT.e2 and g_last_counter write windows *)
pose proof (ie2a_state (IOS_AT 0x120) (spZ regs - IOSEND_FRAME) (ie2a_e2v Bx) (ie2a_snd frame)
              W3 regs3 mem3 R2 ltac:(lia) ltac:(lia) Z5 Z2 V40 Ve2) as HS0.
set (E0 := ie2a_E regs3 (ie2a_e2v Bx) (ie2a_snd frame)) in HS0.
assert (HEI : img_env VAL A_LIM E0) by (unfold E0, ie2a_E; apply Eimg_env).
assert (SHOK : sh_ok segs ie2a_Bx [] E0 (mrestrict (w_H W3) mem3)) by apply Forall_nil.
assert (X32 : ew E0 32 = Z_to_bv 64 (ie2a_e2v Bx))
  by (unfold E0, ie2a_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 0)).
assert (X33 : ew E0 33 = Z_to_bv 64 (ie2a_snd frame))
  by (unfold E0, ie2a_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 1)).
assert (X19 : ew E0 19 = Z_to_bv 64 fail)
  by (unfold E0, ie2a_E; rewrite (ew_Eimg_Ereg_nat regs3 _ 19%nat 19%bv eq_refl); exact R19).
assert (U270 : bv_unsigned (ew E0 270%nat) = TB_GOT + 196)
  by (unfold E0, ie2a_E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); vm_compute; reflexivity).
assert (U456 : bv_unsigned (ew E0 456%nat) = TB_g_last_counter + 884)
  by (unfold E0, ie2a_E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); vm_compute; reflexivity).
(* the values the code loads and stores *)
assert (De2 : sv_denot E0 (SExt true 32 (SOff 32 0)) = Z_to_bv 64 (TW.GOT_e2 Bx))
  by (rewrite EGv; exact (ie2a_sext_den E0 32 (ie2a_e2v Bx) X32 Z5)).
assert (DA1 : sv_denot E0 (SAluw ALU_ADD (SExt true 32 (SOff 32 0)) (SLit 1)) = Z_to_bv 64 (TW.GOT_e2 Bx + 1))
  by (rewrite EGv; apply (ie2a_addw_den E0 32 (ie2a_e2v Bx) X32 Z5); rewrite <- EGv; lia).
(* the two bases the stores address, as facts of the state: without them the static check of the run
   (YP0j.v cells_safe_b) cannot place a write window against the runtime cells' span *)
assert (FA270 : afact_ok E0 270%nat (mkAF (TB_GOT + 196) (TB_GOT + 196) 2)).
{ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U270.
  split; [lia|]. split; [vm_compute; reflexivity | lia]. }
assert (FA456 : afact_ok E0 456%nat (mkAF (TB_g_last_counter + 884) (TB_g_last_counter + 884) 2)).
{ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U456.
  split; [lia|]. split; [vm_compute; reflexivity | lia]. }
pose proof (st_ok_pi_add_fact E0 _ _ 270%nat _ HS0 FA270) as HS1.
pose proof (st_ok_pi_add_fact E0 _ _ 456%nat _ HS1 FA456) as HS.
clear HS0 HS1.
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
              TG.G_HARNESS_B HGX 0 []) as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
              TG.G_HARNESS_B HGX 0 []) as RUNTO.
pose proof (paj_branch (fx := fx) (PI := PI_transportb)) as BR.
unfold cfg_at.
lazymatch goal with |- SRr _ ?Wx _ ?Qx =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx regs3 (Z_to_bv 64 (BASE + IOS_AT 0x120)) mem3
    (YK11.seg_rom segs)) md3) Qx) end.
(* ---- run 1 (0x8311c .. 0x83128): a0 = %hi 55, a2 = GOT.e2, a1 = a2 + 1; it stops at `blt a1, a2` ---- *)
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ ie2a_awr U270 U456. }
ie2a_md mt1. rename ms into ms1.
assert (KW : forall a, 0 <= a < 2 ^ 64 -> ~ ie2a_wr a ->
  aview segs (w_H W3) (ms_mem ms1) a = aview segs (w_H W3) mem3 a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ ie2a_wr HFr); [| exact Ha | exact Hn].
  intros b wlo whi x Hin Hx. ie2a_win Hin Hx ltac:(rewrite ?U270, ?U456 in Hx; first [left; lia | right; lia]). }
assert (GW : forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) (ms_mem ms1) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
clear HF HFr HG.
(* the branch of 0x83128 to the trap word: GOT.e2 + 1 < GOT.e2 never holds *)
psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
{ exfalso. rewrite DA1, De2 in Hc. cbn [branch_taken] in Hc.
  rewrite (ie2a_lts (TW.GOT_e2 Bx + 1) (TW.GOT_e2 Bx) ltac:(lia) ltac:(lia)) in Hc.
  apply Z.ltb_lt in Hc. lia. }
clear Hc.
(* ---- run 2 (0x8312c .. 0x83140): a2 = f.send, the two stores, a1 = s3 & 1; it stops at `beq a1, zero` ---- *)
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ ie2a_awr U270 U456. }
ie2a_md mt2. rename ms into ms2.
assert (KW2 : forall a, 0 <= a < 2 ^ 64 -> ~ ie2a_wr a ->
  aview segs (w_H W3) (ms_mem ms2) a = aview segs (w_H W3) mem3 a).
{ intros a Ha Hn. rewrite <- (KW a Ha Hn). apply (kept_of_frame _ _ _ _ _ ie2a_wr HFr); [| exact Ha | exact Hn].
  intros b wlo whi x Hin Hx. ie2a_win Hin Hx ltac:(rewrite ?U270, ?U456 in Hx; first [left; lia | right; lia]). }
assert (GW2 : forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) (ms_mem ms2) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG (GW a Ha))).
clear HF HFr HG KW GW.
clear dependent ms1.
(* the branch of 0x83140 on bit 0 of s3 *)
psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
- (* s3 & 1 = 0: the frame in flight at 0x832c0 *)
  rewrite (ie2a_br_and1 E0 19 fail X19 ltac:(lia)) in Hc. apply Z.eqb_eq in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan IOS_FLY.
  { ie2a_awr U270 U456. }
  ie2a_md mt3. rename ms into ms3.
  assert (KWF : forall a, 0 <= a < 2 ^ 64 -> ~ ie2a_wr a ->
    aview segs (w_H W3) (ms_mem ms3) a = aview segs (w_H W3) mem3 a).
  { intros a Ha Hn. rewrite <- (KW2 a Ha Hn). apply (kept_of_frame _ _ _ _ _ ie2a_wr HFr); [| exact Ha | exact Hn].
    intros b wlo whi x Hin Hx.
    ie2a_win Hin Hx ltac:(rewrite ?U270, ?U456 in Hx; first [left; lia | right; lia]). }
  assert (GF : forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) (ms_mem ms3) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG (GW2 a Ha))).
  clear HF HFr HG.
  ie2a_stored HS RGe RGl.
  pose proof (ie2a_region_rd4 E0 _ _ 270%nat _ _ _ _ _ _ e2 _ RGe U270
                ltac:(rewrite Ee2; exact DA1)) as VE.
  pose proof (ie2a_region_rd4 E0 _ _ 456%nat _ _ _ _ _ _ (bv_swrap 32 (ie2a_snd frame)) _ RGl U456
                (ie2a_sext_den E0 33 (ie2a_snd frame) X33 Z2)) as VL.
  assert (VEb : forall j, (j < 4)%nat ->
    aview segs (w_H W3) (ms_mem ms3) (TB_GOT + 196 + Z.of_nat j) = Some (YO0f.le_byte e2 4 j))
    by (intros j Hj; rewrite <- (VE j Hj); f_equal; lia).
  assert (VLb : forall j, (j < 4)%nat ->
    aview segs (w_H W3) (ms_mem ms3) (TB_g_last_counter + 0 + Z.of_nat j) =
    Some (YO0f.le_byte (ie2a_snd frame) 4 j))
    by (intros j Hj; rewrite <- (ie2a_le_byte_swrap (ie2a_snd frame) j), <- (VL j Hj); f_equal; lia).
  assert (HTW2 : tw_at TMAP_B (aview segs (w_H W3) (ms_mem ms3))
                   (TW.set_g_last_counter (TW.set_GOT_e2 Bx e2) (ie2a_snd frame))).
  { rewrite ie2a_set_lastc, ie2a_set_e2.
    eapply (ios_tw_end (aview segs (w_H W3) (ms_mem ms3)) (aview segs (w_H W3) mem3)).
    - eapply (ios_tw_step _ _ _ _ TW.OFF_g_last_counter TB_g_last_counter TW.SZ_g_last_counter 0
                TW.OFF_g_last_counter 4%nat (ie2a_snd frame));
        [| exact TMAP_B_g_last_counter | reflexivity | lia | unfold TW.SZ_g_last_counter; lia | exact VLb].
      eapply (ios_tw_step _ _ _ _ TW.OFF_GOT TB_GOT TW.SZ_GOT 196 TW.A_GOT_e2 4%nat e2);
        [| exact TMAP_B_GOT | reflexivity | lia | unfold TW.SZ_GOT; lia | exact VEb].
      apply ios_tw_start. exact HTW.
    - intros x Hx HP. ios_unP HP. pose proof (TMAP_B_hull x Hx) as Hh.
      unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh.
      apply KWF; [lia | intros [HWx | HWx]; lia]. }
  pose proof (regs_kept_of_st_ok_pi E0 _ _ regs3 _ ie2a_kept HS (ie2a_agree regs3 _ _)
                ltac:(vm_compute; reflexivity)) as KR2.
  cbn [ms_regs restrict] in KR2.
  assert (CUR2 : ios_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs frame
                   ly3 S3 W3 (ms_mem ms3) mt3).
  { unfold ios_cur. split; [exact HJ|]. split; [exact HFR|]. split; [exact HPM|]. split; [exact HMO|].
    apply (ie2a_kept_step TG.G_HARNESS_B lyc Sc W memc mdc W3 mem3 (ms_mem ms3)
      (spZ regs - IOSEND_STK) (spZ regs) (iosend_wr (Z.of_nat (length frame))) ie2a_wr
      LAWS HGX HARc HKEPT ltac:(intros a Ha Hn; exact (KWF a Ha Hn)) GF
      ltac:(intros a Ha; right; split;
            [exact (ie2a_wr_inG a Ha) | exact (ie2a_wr_iosend (Z.of_nat (length frame)) a Ha)])
      ltac:(lia) ltac:(lia)). }
  destruct (ie2a_regs_step regs regs3 (ms_regs ms3) p frame fail RG R24 KR2) as (RGb & R24b).
  assert (AT2 : ios_e2_at B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame fail
                  ly3 S3 W3 (ms_mem ms3) mt3 (ms_regs ms3)
                  (TW.set_g_last_counter (TW.set_GOT_e2 Bx e2) (ie2a_snd frame))).
  { apply (ie2a_keep_g STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame fail
             ly3 S3 W3 mem3 md3 regs3 (ms_mem ms3) mt3 (ms_regs ms3) Bx _
             LAWS FIX0 H60 HFAT ltac:(intros a Ha Hn; exact (KWF a Ha Hn)) AT0 CUR2 RGb R24b HTW2). }
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (@YK11.mkst _ ?rg _ ?mm _) ?mdx) _ =>
    change (SRr segs W3 (@cfg_at fx segs (transportb_text + IOS_FLY) rg mm mdx) Q) end.
  exact (HFLY (ms_mem ms3) mt3 (ms_regs ms3) AT2 Hc).
- (* s3 & 1 <> 0: the epilogue at 0x83310 *)
  rewrite (ie2a_br_and1 E0 19 fail X19 ltac:(lia)) in Hc. apply Z.eqb_neq in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan IOS_EPI.
  { ie2a_awr U270 U456. }
  ie2a_md mt3. rename ms into ms3.
  assert (KWF : forall a, 0 <= a < 2 ^ 64 -> ~ ie2a_wr a ->
    aview segs (w_H W3) (ms_mem ms3) a = aview segs (w_H W3) mem3 a).
  { intros a Ha Hn. rewrite <- (KW2 a Ha Hn). apply (kept_of_frame _ _ _ _ _ ie2a_wr HFr); [| exact Ha | exact Hn].
    intros b wlo whi x Hin Hx.
    ie2a_win Hin Hx ltac:(rewrite ?U270, ?U456 in Hx; first [left; lia | right; lia]). }
  assert (GF : forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) (ms_mem ms3) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG (GW2 a Ha))).
  clear HF HFr HG.
  ie2a_stored HS RGe RGl.
  pose proof (ie2a_region_rd4 E0 _ _ 270%nat _ _ _ _ _ _ e2 _ RGe U270
                ltac:(rewrite Ee2; exact DA1)) as VE.
  pose proof (ie2a_region_rd4 E0 _ _ 456%nat _ _ _ _ _ _ (bv_swrap 32 (ie2a_snd frame)) _ RGl U456
                (ie2a_sext_den E0 33 (ie2a_snd frame) X33 Z2)) as VL.
  assert (VEb : forall j, (j < 4)%nat ->
    aview segs (w_H W3) (ms_mem ms3) (TB_GOT + 196 + Z.of_nat j) = Some (YO0f.le_byte e2 4 j))
    by (intros j Hj; rewrite <- (VE j Hj); f_equal; lia).
  assert (VLb : forall j, (j < 4)%nat ->
    aview segs (w_H W3) (ms_mem ms3) (TB_g_last_counter + 0 + Z.of_nat j) =
    Some (YO0f.le_byte (ie2a_snd frame) 4 j))
    by (intros j Hj; rewrite <- (ie2a_le_byte_swrap (ie2a_snd frame) j), <- (VL j Hj); f_equal; lia).
  assert (HTW2 : tw_at TMAP_B (aview segs (w_H W3) (ms_mem ms3))
                   (TW.set_g_last_counter (TW.set_GOT_e2 Bx e2) (ie2a_snd frame))).
  { rewrite ie2a_set_lastc, ie2a_set_e2.
    eapply (ios_tw_end (aview segs (w_H W3) (ms_mem ms3)) (aview segs (w_H W3) mem3)).
    - eapply (ios_tw_step _ _ _ _ TW.OFF_g_last_counter TB_g_last_counter TW.SZ_g_last_counter 0
                TW.OFF_g_last_counter 4%nat (ie2a_snd frame));
        [| exact TMAP_B_g_last_counter | reflexivity | lia | unfold TW.SZ_g_last_counter; lia | exact VLb].
      eapply (ios_tw_step _ _ _ _ TW.OFF_GOT TB_GOT TW.SZ_GOT 196 TW.A_GOT_e2 4%nat e2);
        [| exact TMAP_B_GOT | reflexivity | lia | unfold TW.SZ_GOT; lia | exact VEb].
      apply ios_tw_start. exact HTW.
    - intros x Hx HP. ios_unP HP. pose proof (TMAP_B_hull x Hx) as Hh.
      unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh.
      apply KWF; [lia | intros [HWx | HWx]; lia]. }
  pose proof (regs_kept_of_st_ok_pi E0 _ _ regs3 _ ie2a_kept HS (ie2a_agree regs3 _ _)
                ltac:(vm_compute; reflexivity)) as KR2.
  cbn [ms_regs restrict] in KR2.
  assert (CUR2 : ios_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs frame
                   ly3 S3 W3 (ms_mem ms3) mt3).
  { unfold ios_cur. split; [exact HJ|]. split; [exact HFR|]. split; [exact HPM|]. split; [exact HMO|].
    apply (ie2a_kept_step TG.G_HARNESS_B lyc Sc W memc mdc W3 mem3 (ms_mem ms3)
      (spZ regs - IOSEND_STK) (spZ regs) (iosend_wr (Z.of_nat (length frame))) ie2a_wr
      LAWS HGX HARc HKEPT ltac:(intros a Ha Hn; exact (KWF a Ha Hn)) GF
      ltac:(intros a Ha; right; split;
            [exact (ie2a_wr_inG a Ha) | exact (ie2a_wr_iosend (Z.of_nat (length frame)) a Ha)])
      ltac:(lia) ltac:(lia)). }
  destruct (ie2a_regs_step regs regs3 (ms_regs ms3) p frame fail RG R24 KR2) as (RGb & R24b).
  assert (AT2 : ios_e2_at B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame fail
                  ly3 S3 W3 (ms_mem ms3) mt3 (ms_regs ms3)
                  (TW.set_g_last_counter (TW.set_GOT_e2 Bx e2) (ie2a_snd frame))).
  { apply (ie2a_keep_g STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p frame fail
             ly3 S3 W3 mem3 md3 regs3 (ms_mem ms3) mt3 (ms_regs ms3) Bx _
             LAWS FIX0 H60 HFAT ltac:(intros a Ha Hn; exact (KWF a Ha Hn)) AT0 CUR2 RGb R24b HTW2). }
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (@YK11.mkst _ ?rg _ ?mm _) ?mdx) _ =>
    change (SRr segs W3 (@cfg_at fx segs (transportb_text + IOS_EPI) rg mm mdx) Q) end.
  exact (HEPI (ms_mem ms3) mt3 (ms_regs ms3) AT2 Hc).
Qed.

(* ------------------------------------------------------------------ *)
(* The segment                                                         *)
(* ------------------------------------------------------------------ *)

(* The E2 arm, 0x83110 .. 0x83144: from the dispatch's E2 exit (io_send_seg_cut.v ios_at_csf, f.cmd = 0xe2 and
   f.retry = 0) to the frame in flight (IOS_FLY) when bit 0 of the entry g_fail_next is clear, and to the epilogue
   (IOS_EPI) when it is set. *)
Lemma ios_e2_arm : @ios_e2_arm_stmt fx rc B MT.
Proof.
unfold ios_e2_arm_stmt.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw Bw' ly3 S3 W2 mem4 md4 regs4 Q
  HLAWS HFIX AT EE2 Erty HCSF HARM HFLY HEPI.
destruct HLAWS as (HCELLS & _ & _ & _ & LAWS & MTL & HGX & HGE & _ & _ & _ & LCLC & _ & LCSW & _).
destruct (ie2a_geo STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame Bw HFIX)
  as (HARc & Hce & Hlo & Hhi & H47 & Hsp0al & Hal).
pose proof (ios_len60 _ _ _ HCSF) as H60.
destruct HFIX as (HJc & Hra & Hra4 & Hgp & Htp & H11 & H12 & Hsp16 & Hslo & Hshi & Hp0 & HG8c & HSRCc & HOFFc
  & HFATc & Hfailb & HROM & Htwc & Hfly & Hcmd & Hev).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FS : IOSEND_STK = 8512) by reflexivity.
(* the model: the two leaf calls, the counter and the world each arm leaves *)
assert (Hretry : TC.truth (DSpec.sf_retry (TC.rf frame)) = false).
{ unfold TC.truth. unfold ios_e2_rty in Erty. rewrite Erty. reflexivity. }
destruct (ios_arm_e2 Bw frame Bw' HARM EE2 Hretry) as (HMW & HMC & e2 & Hinc & Hcase).
cbv zeta in Hcase.
(* the fixed facts this stretch reads *)
assert (FIX : ie2a_fix STK sp0 regs p frame).
{ unfold ie2a_fix.
  split; [exact Hp0|]. split; [lia|]. split; [exact HOFFc|]. split; [exact Hsp16|].
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [exact Hra|]. split; [exact Hra4|]. split; [exact Hgp | exact Htp]. }
assert (Hfail0 : 0 <= TW.g_fail_next Bw <= 1).
{ pose proof (TWL.u_at_range Bw TW.OFF_g_fail_next 1) as Hr.
  change (TW.u_at Bw TW.OFF_g_fail_next 1) with (TW.g_fail_next Bw) in Hr. lia. }
(* 0x83110 .. 0x83118: the two leaf calls *)
apply (ie2a_calls STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame
         (TW.g_fail_next Bw) ly3 S3 W2 mem4 md4 regs4 (ios_B0 Bw) Q
         HCELLS LAWS HGX LCSW LCLC HARc FIX H60 AT HMW HMC).
intros mem5 md5 regs5 AT5.
(* 0x8311c .. 0x83144: the counter, the two stores and the branch *)
apply (ie2a_tail STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p frame
         (TW.g_fail_next Bw) e2 ly3 S3 W2 mem5 md5 regs5 (ios_B0 Bw) Q
         LAWS HGX HARc FIX H60 HFATc Hfail0 Hinc AT5).
- (* bit 0 clear: the frame in flight, at the world ios_arm_e2's second case gives *)
  intros mem6 md6 regs6 AT6 Hz.
  assert (Htruth : TC.truth (TW.g_fail_next Bw) = false)
    by (unfold TC.truth; rewrite Hz; reflexivity).
  destruct Hcase as [(Ht & _) | (_ & EBw')]; [rewrite Htruth in Ht; discriminate Ht|].
  exact (HFLY ly3 S3 mem6 md6 regs6
           (TW.set_g_last_counter (TW.set_GOT_e2 (ios_B0 Bw) e2) (DSpec.sf_send (TC.rf frame)))
           Htruth EBw' AT6).
- (* bit 0 set: the epilogue, at the world ios_arm_e2's first case gives *)
  intros mem6 md6 regs6 AT6 Hz.
  assert (Htruth : TC.truth (TW.g_fail_next Bw) = true)
    by (unfold TC.truth; apply negb_true_iff, Z.eqb_neq; exact Hz).
  destruct Hcase as [(_ & EBw') | (Hf & _)]; [|rewrite Htruth in Hf; discriminate Hf].
  rewrite <- EBw' in AT6.
  exact (HEPI ly3 S3 W2 mem6 md6 regs6 AT6).
Qed.

End e2a.
