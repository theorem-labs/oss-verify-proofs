(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 274 of its 316 lines of code are new or changed and 1882 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/DgnBcRel.v; 509 of its 547 lines of code are new or changed and 278 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/DgnBcLoopTest.v, with its module paths and module names changed; 17 of its 549 lines of code are new or changed and 15 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: libdiginet/fuzz_frame image B's copy of this unit's lib/A/Prog/DgnBcLoopTest.v: module paths lib/B (the image-B core's YB1v / YE2k / YCbq / YC5d, lib/B/Prog/PaJournal.v, the listing files lib/B/Prog/FrameBSyms.v .. FrameBCJ.v, lib/B/Prog/CanLeafb.v, DgnFrameCg.v, diginet_body_check_cg.v, diginet_msg_next_cg.v, DgnBcCut.v, DgnBcLoopCut.v), the listing names of image B (frameb_listing, PI_frameb), the engine-run kit of image B's lib/B/Prog/DgnBcScan.v for lib/A/Prog/DgnBcScan.v's, and image B's code after +0x198: the segment bt_t2 also passes the two UBSan guards +0x198 `beqz a0` and +0x1b8 `bgeu a0,a1` (a1 = -2) to the `unimp` word at +0x444, which the engine decides not taken from the fact 4096 <= p <= 0x7fffff800000 on a0 = p, and the release is reached through +0x43c. *)
(* DgnBcLoopTest (image B): Lemma bl_test : bl_test_stmt (lib/B/Prog/DgnBcLoopCut.v), the second half of one turn
   of the msg_next loop of diginet_body_check (fuzz_decode.asan-ubsan 0x82970 = dgndecb_sigma DDB_diginet_body_check),
   offsets +0x178 .. +0x1dc and +0x43c of the listing lib/B/Prog/DgnDecodeBList.v. No function is proved here.
   The code writes a0, a1, a2 only, writes no memory and calls nothing:
     +0x178 .. +0x180  `beq a0,s10` (s10 = 1) to +0x184; `bnez a0` to +0x16c (BC_LOOP); `j +0x1f8` (BC_SCAN);
     +0x184 .. +0x190  a0 = m.status (the byte at s6 = m), `bne a0,s11` (s11 = 0xf0) to +0x16c; a0 = m.sysex_len
                       (the word at m + 16), `bltu a0,s2` (s2 = 3) to +0x16c;
     +0x194            a0 = m.sysex (the word at m + 8);
     +0x198            `beqz a0` to the `unimp` word at +0x444 (UBSan guard 1: m.sysex is not null);
     +0x19c .. +0x1b0  the instrumented check of the byte at a0, a1 = that byte, `bne a1,s4` (s4 = 0x13) to +0x16c;
     +0x1b4 .. +0x1b8  a1 = -2, `bgeu a0,a1` to +0x444 (UBSan guard 2: m.sysex + 2 does not wrap);
     +0x1bc .. +0x1d8  a0 + 2, its instrumented check, a0 = that byte, `bne a0,112` to +0x16c; +0x1dc `j +0x43c`;
     +0x43c            `li a0,-10`, `j +0x2d0` (BC_REL).
   How it is proved. Three engine segments over read-only regions (lib/B/Prog/DgnBcScan.v bcs_run: the memory
   after a run is the memory before, the model changes only in its materialized part):
     bt_t1x  +0x178, a0 <> 1: no region; split on `beq` (refuted) and `bnez`;
     bt_t1o  +0x178, a0 = 1: the status byte and the words at m + 8 and m + 16 as a region at s6 (atoms 32, 33,
             34); split on `beq` (refuted), `bne a0,s11` and `bltu a0,s2`, up to +0x198 with a0 = m.sysex;
     bt_t2   +0x198: the body bytes at a0 and a0 + 2 as a region at a0 (atoms 32, 33), the shadow entry of the three
             bytes at a0 (lib/Reusable/YCbq.v range_addressable_of_block of the body's heap block), so the token engine
             passes both checks; the fact 4096 <= a0 <= 0x7fffff800000 (a0 = body + cp + 1 in the body's heap block,
             diginet_msg_next's post), so the engine decides both UBSan guards not taken (YP0e.v decide_cond2: the
             interval of a0 is disjoint from 0 and below 2^64 - 2); split on the two byte compares.
   The values come from bl_after: a0 = mr_code r, the 40 message bytes msg_cells body mj r at m (for a result of 1
   the status cell is b8 (mr_status r), the sysex word body + mr_sysex r for a sysex, the sysex_len word
   mr_sysex_len r), and the body bytes from bc_cur. The registers the cuts read are callee-saved, so they are the
   entry's (aregs_preserved). *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YN3v YI04 YI00 YI09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YG0p YG0s.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c YO0f.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib DgnTransportBCJ.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Cells Mem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog Require diginet_msg_next_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg diginet_body_check_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require diginet_msg_next_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import CanLeafb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnBcCut DgnBcLoopCut DgnBcScan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module BMN := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.diginet_msg_next_cg.
Module LC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Cells.
Module BTMem := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Mem.
Module PMsg := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.diginet_msg_next_c.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* The symbolic states                                                 *)
(* ------------------------------------------------------------------ *)

(* Offsets of the test from the listing's base. *)
Definition BT_AT (k : Z) : Z := AF_diginet_body_check + k.
(* +0x178 with a0 <> 1: no memory is read. *)
Definition bt1x_ss : sstate := mkSS BL_RET sr_atoms [] None (mkFacts [] [] []).
(* +0x178 with a0 = 1: the status byte, the sysex word and the sysex_len word of m (s6), as atoms 32, 33, 34. *)
Definition bt1_rg : YP09.region := YP09.mkRegion (Some 22%nat) 0 24 0 0
  [YP09.mkChunk 0 (CVal 1 (SOff 32 0)); YP09.mkChunk 8 (CVal 8 (SOff 33 0)); YP09.mkChunk 16 (CVal 8 (SOff 34 0))].
Definition bt1_ss : sstate := mkSS BL_RET sr_atoms [bt1_rg] None (mkFacts [] [] []).
(* +0x198: the body bytes at a0 and a0 + 2 as atoms 32, 33; the shadow entry of the three bytes at a0. *)
Definition bt2_SH : list shent := [mkSHE 10 0 3].
Definition bt2_G : facts := mkFacts [(25%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (10%nat, bcs_PTR);
  (32%nat, mkAF 0 255 0); (33%nat, mkAF 0 255 0)] [] [].
Definition bt2_rg : YP09.region := YP09.mkRegion (Some 10%nat) 0 3 0 0
  [YP09.mkChunk 0 (CVal 1 (SOff 32 0)); YP09.mkChunk 2 (CVal 1 (SOff 33 0))].
Definition bt2_ss : sstate := mkSS (BT_AT 0x198) sr_atoms [bt2_rg] None bt2_G.

(* ------------------------------------------------------------------ *)
(* The model: the result codes, the message bytes of a result of 1    *)
(* ------------------------------------------------------------------ *)

Lemma bt_code_range : forall r, -8 <= mr_code r <= 1.
Proof. intros r. unfold mr_code. destruct (mr_kind r); lia. Qed.

Lemma bt_is_end_code : forall r, is_end r = true <-> mr_code r = 0.
Proof. intros r. unfold is_end, mr_code. destruct (mr_kind r); split; intros H; try reflexivity; discriminate. Qed.

Lemma bt_refused_kind : forall b r, refused b r = true -> mr_kind r = MkSysex.
Proof. intros b r. unfold refused. destruct (mr_kind r); intros H; try discriminate H; reflexivity. Qed.

Lemma bt_code1_kinds : forall r, mr_code r = 1 -> mr_kind r = MkSysex \/ mr_kind r = MkChan.
Proof. intros r. unfold mr_code. destruct (mr_kind r); intros H; try discriminate H; auto. Qed.

(* A channel message's status is a channel status 0x80 .. 0xef. *)
Lemma bt_chan_status : forall b pos st, st_ok st -> mr_kind (msg_step b pos st) = MkChan ->
  0x80 <= mr_status (msg_step b pos st) < 0xf0.
Proof.
  intros b pos st Hs. unfold msg_step.
  destruct (length b <=? pos)%nat; [cbn; discriminate|].
  destruct (at8 b pos =? 0xf0); [destruct (find_f7 _); cbn; discriminate|].
  destruct (Z.leb_spec 0xf0 (at8 b pos)) as [A|A]; [cbn; discriminate|].
  destruct (Z.leb_spec 0x80 (at8 b pos)) as [C|C].
  - intros Hk. rewrite (chan_step_status _ _ _ _ _ _ Hk). lia.
  - destruct (Z.eqb_spec st 0) as [E|E]; [cbn; discriminate|].
    intros Hk. rewrite (chan_step_status _ _ _ _ _ _ Hk). destruct Hs; lia.
Qed.

(* A result of 1 whose status byte reads 0xf0 is a sysex. *)
Lemma bt_kind_sysex : forall b pos st, st_ok st -> mr_code (msg_step b pos st) = 1 ->
  bz (b8 (mr_status (msg_step b pos st))) = 240 -> mr_kind (msg_step b pos st) = MkSysex.
Proof.
  intros b pos st Hs H1 H240.
  destruct (bt_code1_kinds _ H1) as [Hk | Hk]; [exact Hk|].
  pose proof (bt_chan_status b pos st Hs Hk) as Hr.
  rewrite bz_b8 in H240 by lia. lia.
Qed.

(* The 40 message bytes of a result of 1: the status byte, 7 bytes, the sysex word, the sysex_len word, 16 bytes. *)
Lemma bt_msg_code1 : forall body (mj : list byte) r, length mj = 40%nat -> mr_code r = 1 ->
  exists pre post, LC.cells_bytes (PMsg.msg_cells body mj r) =
    b8 (mr_status r) :: pre ++
      BTMem.le8 (Z_to_bv 64 (if writes_sysex (mr_kind r) then body + Z.of_nat (mr_sysex r) else 0)) ++
      BTMem.le8 (Z_to_bv 64 (Z.of_nat (mr_sysex_len r))) ++ post /\
    length pre = 7%nat.
Proof.
  intros body mj r Hmj H1.
  exists ([b8 (mr_running r); b8 (mr_d1 r); b8 (mr_d2 r)] ++ firstn 4 (skipn 4 mj)). eexists. split.
  - destruct (bt_code1_kinds r H1) as [Hk | Hk]; unfold PMsg.msg_cells, is_end; rewrite Hk;
      cbn [writes_status writes_running writes_sysex writes_len LC.cells_bytes LC.cbytes app]; reflexivity.
  - rewrite length_app, length_firstn, length_skipn, Hmj. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Bytes and words of a garr8 array                                    *)
(* ------------------------------------------------------------------ *)

Lemma bt_garr8_c1 : forall (m : word -> option byte) base (b : byte) (l : list byte),
  garr8 tfibsegs m base (map bz (b :: l)) -> val_mem tfibsegs m base 1 (bz b) /\ 0 <= bz b < 256.
Proof.
  intros m base b l H. assert (H0 : (0 < length (map bz (b :: l)))%nat) by (cbn; lia).
  destruct (H 0%nat H0) as [Hv Hr]. cbn [nth map Z.of_nat] in Hv, Hr. rewrite Z.add_0_r in Hv.
  exact (conj Hv Hr).
Qed.

(* An eight-byte cell C8 (Z_to_bv 64 v) of the array, at index o. *)
Lemma bt_garr8_c8 : forall (m : word -> option byte) base (pre : list byte) (v : Z) (post : list byte) (o : nat),
  garr8 tfibsegs m base (map bz (pre ++ BTMem.le8 (Z_to_bv 64 v) ++ post)) -> length pre = o ->
  val_mem tfibsegs m (base + Z.of_nat o) 8 (v mod 2 ^ 64).
Proof.
  intros m base pre v post o H Ho k Hk. subst o.
  assert (Hl : (length pre + k < length (map bz (pre ++ BTMem.le8 (Z_to_bv 64 v) ++ post)))%nat)
    by (rewrite length_map, !length_app, BTMem.length_le8; lia).
  pose proof (garr8_mbyte tfibsegs m base _ (length pre + k) H Hl) as Hb.
  rewrite bcs_nth_bz in Hb. unfold at8 in Hb.
  rewrite app_nth2 in Hb by lia. replace (length pre + k - length pre)%nat with k in Hb by lia.
  rewrite app_nth1 in Hb by (rewrite BTMem.length_le8; lia).
  replace (base + Z.of_nat (length pre) + Z.of_nat k) with (base + Z.of_nat (length pre + k)) by lia.
  rewrite Hb. f_equal. f_equal.
  assert (Hc : bv_unsigned (nth k (BTMem.le8 (Z_to_bv 64 v)) (b8 0)) = YG0f.le_byte v 8 k).
  { pose proof (can_leafb_le8_byte v k Hk) as Hc0. unfold BTMem.wa in Hc0.
    rewrite (nth_error_nth' _ (b8 0)) in Hc0 by (rewrite BTMem.length_le8; lia).
    exact (f_equal (fun o => match o with Some z => z | None => 0 end) Hc0). }
  unfold bz. rewrite Hc.
  unfold YG0f.le_byte, YO0f.le_byte. change (8 * Z.of_nat 8) with 64. rewrite Z.mod_mod by lia. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Branch values and kept registers                                    *)
(* ------------------------------------------------------------------ *)

Lemma bt_modeq : forall x y, - 2 ^ 63 <= x < 2 ^ 63 -> - 2 ^ 63 <= y < 2 ^ 63 ->
  (x mod 2 ^ 64 =? y mod 2 ^ 64) = (x =? y).
Proof.
  intros x y Hx Hy. destruct (Z.eqb_spec x y) as [->|Hne]; [rewrite Z.eqb_refl; reflexivity|].
  apply Z.eqb_neq. intros H.
  assert (Hd : (x - y) mod 2 ^ 64 = 0)
    by (rewrite Zminus_mod, H, Z.sub_diag; reflexivity).
  apply Z.mod_divide in Hd; [|lia]. destruct Hd as [k Hk]. nia.
Qed.

Lemma bt_u_den : forall (E : env) a x, sv_denot E a = w64 x -> U E a = zcanon x.
Proof.
  intros E a x H. unfold U. rewrite H. unfold w64. rewrite Z_to_bv_unsigned.
  unfold bv_wrap, bv_modulus, zcanon, M64. change (2 ^ Z.of_N 64) with (2 ^ 64). reflexivity.
Qed.

Lemma bt_bt_eq : forall (E : env) a b x y, sv_denot E a = w64 x -> sv_denot E b = w64 y ->
  - 2 ^ 63 <= x < 2 ^ 63 -> - 2 ^ 63 <= y < 2 ^ 63 ->
  branch_taken BC_EQ (sv_denot E a) (sv_denot E b) = (x =? y).
Proof.
  intros E a b x y Ha Hb Hx Hy. rewrite branch_eq_U.
  rewrite (bt_u_den E a x Ha), (bt_u_den E b y Hb). unfold zcanon, M64.
  apply bt_modeq; lia.
Qed.

Lemma bt_bt_ne : forall (E : env) a b x y, sv_denot E a = w64 x -> sv_denot E b = w64 y ->
  - 2 ^ 63 <= x < 2 ^ 63 -> - 2 ^ 63 <= y < 2 ^ 63 ->
  branch_taken BC_NE (sv_denot E a) (sv_denot E b) = negb (x =? y).
Proof.
  intros E a b x y Ha Hb Hx Hy. rewrite branch_ne_U.
  rewrite (bt_u_den E a x Ha), (bt_u_den E b y Hb). unfold zcanon, M64.
  rewrite bt_modeq by lia. reflexivity.
Qed.

(* An atom of the entry environment, any value. *)
Lemma bt_den0 : forall E0 E n v, env_agree 512 E0 E -> (n < 512)%nat -> ew E0 n = w64 v ->
  sv_denot E (SOff n 0) = w64 v.
Proof.
  intros E0 E n v HA Hn H. cbn [sv_denot]. rewrite (bcs_agree_ew E0 E n HA Hn), H, Z.add_0_r.
  unfold w64. apply Z_to_bv_bv_unsigned.
Qed.

Ltac bt_kp HP H n := etransitivity; [exact (HP n ltac:(unfold acallee_saved; lia)) | exact H].

(* The loop's registers are callee-saved. *)
Lemma bt_loop_kept : forall regs r1 r2 body sp1 F,
  bc_regs_loop regs r1 body sp1 F -> aregs_preserved r1 r2 -> bc_regs_loop regs r2 body sp1 F.
Proof.
  intros regs r1 r2 body sp1 F
    (((H2 & H3 & H4 & H8 & H9 & H23 & H24) & H19 & H25) & H18 & H20 & H21 & H22 & H26 & H27) HP.
  unfold bc_regs_loop, bc_regs_scan, bc_regs_rel.
  refine (conj (conj (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))) (conj _ _))
            (conj _ (conj _ (conj _ (conj _ (conj _ _)))))).
  - bt_kp HP H2 2.
  - bt_kp HP H3 3.
  - bt_kp HP H4 4.
  - bt_kp HP H8 8.
  - bt_kp HP H9 9.
  - bt_kp HP H23 23.
  - bt_kp HP H24 24.
  - bt_kp HP H19 19.
  - bt_kp HP H25 25.
  - bt_kp HP H18 18.
  - bt_kp HP H20 20.
  - bt_kp HP H21 21.
  - bt_kp HP H22 22.
  - bt_kp HP H26 26.
  - bt_kp HP H27 27.
Qed.

(* The callee-saved registers the run kept, from the entry registers r0 (env Eimg (Ereg r0 ex)). *)
Ltac bt_kept r0 ex HPR :=
  lazymatch goal with
  | HS : st_ok_pi _ ?vl ?Ex ?ssx (restrict (w_H ?Wx) ?msx), HAG : env_agree 512 _ ?Ex |- _ =>
    assert (HPR : aregs_preserved r0 (ms_regs msx))
      by (apply (aregs_preserved_of_st_ok tfibsegs (w_H Wx) Ex (abs_ss vl ssx) msx r0 ex HS
                   (bcs_agree32 r0 ex Ex HAG));
          vm_compute; reflexivity)
  end.

(* ------------------------------------------------------------------ *)
(* The three segments                                                  *)
(* ------------------------------------------------------------------ *)

Section bt. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).
Local Abbreviation bt_at pc r mem md :=
  (mkCfg (@YK11.mkst fx r (Z_to_bv 64 (BASE + pc)) mem (YK11.seg_rom segs)) md).

Definition bt1_E (r : bvmap 5 word) (a b c : Z) : env :=
  Eimg (PI := PI_transportb) (Ereg r [w64 a; w64 b; w64 c]).
Definition bt2_E (r : bvmap 5 word) (a b : Z) : env :=
  Eimg (PI := PI_transportb) (Ereg r [w64 a; w64 b]).

(* +0x178 with a0 = code <> 1: `beq a0,s10` is not taken; `bnez a0` to the loop head, else the prefix scan. *)
Lemma bt_t1x : forall (W : world segs) (r : bvmap 5 word) (mem : word -> option byte) (md : Model) (code : Z)
    (Q : world segs -> config -> Prop),
  YK11.getr r 10 = w64 code -> YK11.getr r 26 = w64 1 -> code <> 1 -> - 2 ^ 63 <= code < 2 ^ 63 ->
  (code <> 0 -> forall (r' : bvmap 5 word) mat, aregs_preserved r r' ->
     SRr segs W (bt_at BC_LOOP r' mem (with_vm_backing (m_vm_lazy md) mat md)) Q) ->
  (code = 0 -> forall (r' : bvmap 5 word) mat, aregs_preserved r r' ->
     SRr segs W (bt_at BC_SCAN r' mem (with_vm_backing (m_vm_lazy md) mat md)) Q) ->
  SRr segs W (bt_at BL_RET r mem md) Q.
Proof.
  intros W r mem md code Q R10 R26 Hc1 Hcr KL KS.
  assert (HS : st_ok_pi segs VAL (Eimg (PI := PI_transportb) (Ereg r [])) bt1x_ss
    (restrict (w_H W) (@YK11.mkst fx r (Z_to_bv 64 (BASE + BL_RET)) mem (YK11.seg_rom segs)))).
  { rewrite restrict_mkst_fx. unfold bt1x_ss. apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
    - apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - apply Forall_nil.
    - exact I.
    - exact (conj I (conj I I)). }
  assert (HSH : sh_ok segs bcs_Bx [] (Eimg (PI := PI_transportb) (Ereg r [])) (mrestrict (w_H W) mem))
    by apply Forall_nil.
  assert (HEI : img_env VAL A_LIM (Eimg (PI := PI_transportb) (Ereg r []))) by apply Eimg_env.
  pose proof (env_agree_refl 512 (Eimg (PI := PI_transportb) (Ereg r []))) as HAG.
  assert (X10 : ew (Eimg (PI := PI_transportb) (Ereg r [])) 10 = w64 code)
    by (rewrite (bcs_ew_reg r _ 10 10%bv ltac:(lia) eq_refl); exact R10).
  assert (X26 : ew (Eimg (PI := PI_transportb) (Ereg r [])) 26 = w64 1)
    by (rewrite (bcs_ew_reg r _ 26 26%bv ltac:(lia) eq_refl); exact R26).
  bcs_step ([] : list shent) BC_LOOP.
  bcs_branch ([] : list shent).
  - (* a0 = s10: impossible *)
    exfalso.
    rewrite (bt_bt_eq _ _ _ code 1 (bt_den0 _ _ 10 code HAG ltac:(lia) X10) (bt_den0 _ _ 26 1 HAG ltac:(lia) X26)
               Hcr ltac:(lia)) in Hc.
    apply Z.eqb_eq in Hc. exact (Hc1 Hc).
  - bcs_step ([] : list shent) BC_LOOP.
    bcs_branch ([] : list shent).
    + (* a0 <> 0: the loop head *)
      rewrite (bt_bt_ne _ (SOff 10 0) (SLit 0) code 0 (bt_den0 _ _ 10 code HAG ltac:(lia) X10) eq_refl Hcr
                 ltac:(lia)) in Hc0.
      apply negb_true_iff, Z.eqb_neq in Hc0.
      bcs_step ([] : list shent) BC_LOOP.
      bt_kept r ([] : list word) HPR. bcs_shape. exact (KL Hc0 _ _ HPR).
    + (* a0 = 0: the prefix scan *)
      rewrite (bt_bt_ne _ (SOff 10 0) (SLit 0) code 0 (bt_den0 _ _ 10 code HAG ltac:(lia) X10) eq_refl Hcr
                 ltac:(lia)) in Hc0.
      apply negb_false_iff, Z.eqb_eq in Hc0.
      bcs_step ([] : list shent) BC_SCAN.
      bt_kept r ([] : list word) HPR. bcs_shape. exact (KS Hc0 _ _ HPR).
Qed.

Lemma bt1_E_ex : forall r a b c,
  ew (bt1_E r a b c) 32 = w64 a /\ ew (bt1_E r a b c) 33 = w64 b /\ ew (bt1_E r a b c) 34 = w64 c.
Proof.
  intros r a b c. unfold bt1_E. rewrite !Eimg_low by (unfold A_TEXT; lia).
  split; [exact (ew_Ereg_extra r _ 0) | split; [exact (ew_Ereg_extra r _ 1) | exact (ew_Ereg_extra r _ 2)]].
Qed.

(* +0x178 with a0 = 1: the status byte (m + 0) against s11 = 0xf0, the sysex_len word (m + 16) against s2 = 3, then
   the sysex word (m + 8) into a0, up to +0x198. *)
Lemma bt_t1o : forall (W : world segs) (r : bvmap 5 word) (mem : word -> option byte) (md : Model)
    (m vst vsx vsl : Z) (Q : world segs -> config -> Prop),
  YK11.getr r 10 = w64 1 -> YK11.getr r 18 = w64 3 -> YK11.getr r 22 = w64 m ->
  YK11.getr r 26 = w64 1 -> YK11.getr r 27 = w64 240 ->
  0 <= m -> m + 24 <= 2 ^ 64 ->
  0 <= vst < 256 -> 0 <= vsx < 2 ^ 64 -> 0 <= vsl < 2 ^ 64 ->
  val_mem segs (mrestrict (w_H W) mem) m 1 vst ->
  val_mem segs (mrestrict (w_H W) mem) (m + 8) 8 vsx ->
  val_mem segs (mrestrict (w_H W) mem) (m + 16) 8 vsl ->
  (vst <> 240 -> forall (r' : bvmap 5 word) mat, aregs_preserved r r' ->
     SRr segs W (bt_at BC_LOOP r' mem (with_vm_backing (m_vm_lazy md) mat md)) Q) ->
  (vst = 240 -> vsl < 3 -> forall (r' : bvmap 5 word) mat, aregs_preserved r r' ->
     SRr segs W (bt_at BC_LOOP r' mem (with_vm_backing (m_vm_lazy md) mat md)) Q) ->
  (vst = 240 -> 3 <= vsl -> forall (r' : bvmap 5 word) mat, aregs_preserved r r' -> YK11.getr r' 10 = w64 vsx ->
     SRr segs W (bt_at (BT_AT 0x198) r' mem (with_vm_backing (m_vm_lazy md) mat md)) Q) ->
  SRr segs W (bt_at BL_RET r mem md) Q.
Proof.
  intros W r mem md m vst vsx vsl Q R10 R18 R22 R26 R27 Hm0 Hm1 Hvst Hvsx Hvsl V0 V8 V16 KL1 KL2 KT2.
  destruct (bt1_E_ex r vst vsx vsl) as (X32 & X33 & X34).
  assert (U22 : bv_unsigned (ew (bt1_E r vst vsx vsl) 22) = m)
    by (unfold bt1_E; rewrite (bcs_ew_reg r _ 22 22%bv ltac:(lia) eq_refl), R22; unfold w64;
        apply unsigned_lit_small; lia).
  assert (HS : st_ok_pi segs VAL (bt1_E r vst vsx vsl) bt1_ss
    (restrict (w_H W) (@YK11.mkst fx r (Z_to_bv 64 (BASE + BL_RET)) mem (YK11.seg_rom segs)))).
  { rewrite restrict_mkst_fx. unfold bt1_ss. apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
    - apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - apply Forall_cons; [|apply Forall_nil]. unfold bt1_rg, YP09.region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U22.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
      + apply (bcs_chunk1 _ _ 32 m 0 m vst X32 Hvst ltac:(lia) V0).
      + apply (chunk_ok_val segs _ _ m 8 8 (SOff 33 0) vsx).
        * cbn [sv_denot]. rewrite X33, Z.add_0_r. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
        * cbn. lia.
        * cbn. lia.
        * exact V8.
      + apply (chunk_ok_val segs _ _ m 16 8 (SOff 34 0) vsl).
        * cbn [sv_denot]. rewrite X34, Z.add_0_r. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
        * cbn. lia.
        * cbn. lia.
        * exact V16.
    - exact (conj I I).
    - exact (conj I (conj I I)). }
  assert (HSH : sh_ok segs bcs_Bx [] (bt1_E r vst vsx vsl) (mrestrict (w_H W) mem)) by apply Forall_nil.
  assert (HEI : img_env VAL A_LIM (bt1_E r vst vsx vsl)) by apply Eimg_env.
  pose proof (env_agree_refl 512 (bt1_E r vst vsx vsl)) as HAG.
  assert (X10 : ew (bt1_E r vst vsx vsl) 10 = w64 1)
    by (unfold bt1_E; rewrite (bcs_ew_reg r _ 10 10%bv ltac:(lia) eq_refl); exact R10).
  assert (X18 : ew (bt1_E r vst vsx vsl) 18 = w64 3)
    by (unfold bt1_E; rewrite (bcs_ew_reg r _ 18 18%bv ltac:(lia) eq_refl); exact R18).
  assert (X26 : ew (bt1_E r vst vsx vsl) 26 = w64 1)
    by (unfold bt1_E; rewrite (bcs_ew_reg r _ 26 26%bv ltac:(lia) eq_refl); exact R26).
  assert (X27 : ew (bt1_E r vst vsx vsl) 27 = w64 240)
    by (unfold bt1_E; rewrite (bcs_ew_reg r _ 27 27%bv ltac:(lia) eq_refl); exact R27).
  bcs_step ([] : list shent) (BT_AT 0x198).
  bcs_branch ([] : list shent).
  - (* a0 = s10 = 1 *)
    bcs_step ([] : list shent) (BT_AT 0x198).
    bcs_branch ([] : list shent).
    + (* the status is not 0xf0: the loop head *)
      rewrite branch_ne_U, U_zext in Hc0.
      rewrite (bcs_U _ _ 32 vst HAG ltac:(lia) X32 ltac:(lia)), (bcs_U _ _ 27 240 HAG ltac:(lia) X27 ltac:(lia))
        in Hc0.
      change (2 ^ Z.of_N 8) with 256 in Hc0. rewrite (Z.mod_small vst 256) in Hc0 by lia.
      apply negb_true_iff, Z.eqb_neq in Hc0.
      bcs_step ([] : list shent) BC_LOOP.
      bt_kept r [w64 vst; w64 vsx; w64 vsl] HPR. bcs_shape. exact (KL1 Hc0 _ _ HPR).
    + (* the status is 0xf0 *)
      rewrite branch_ne_U, U_zext in Hc0.
      rewrite (bcs_U _ _ 32 vst HAG ltac:(lia) X32 ltac:(lia)), (bcs_U _ _ 27 240 HAG ltac:(lia) X27 ltac:(lia))
        in Hc0.
      change (2 ^ Z.of_N 8) with 256 in Hc0. rewrite (Z.mod_small vst 256) in Hc0 by lia.
      apply negb_false_iff, Z.eqb_eq in Hc0.
      bcs_step ([] : list shent) (BT_AT 0x198).
      bcs_branch ([] : list shent).
      * (* sysex_len < 3: the loop head *)
        rewrite branch_ltu_U in Hc1.
        rewrite (bcs_U _ _ 34 vsl HAG ltac:(lia) X34 ltac:(lia)), (bcs_U _ _ 18 3 HAG ltac:(lia) X18 ltac:(lia))
          in Hc1.
        apply Z.ltb_lt in Hc1.
        bcs_step ([] : list shent) BC_LOOP.
        bt_kept r [w64 vst; w64 vsx; w64 vsl] HPR. bcs_shape. exact (KL2 Hc0 Hc1 _ _ HPR).
      * (* sysex_len >= 3: a0 = the sysex word *)
        rewrite branch_ltu_U in Hc1.
        rewrite (bcs_U _ _ 34 vsl HAG ltac:(lia) X34 ltac:(lia)), (bcs_U _ _ 18 3 HAG ltac:(lia) X18 ltac:(lia))
          in Hc1.
        apply Z.ltb_ge in Hc1.
        bcs_step ([] : list shent) (BT_AT 0x198).
        bt_kept r [w64 vst; w64 vsx; w64 vsl] HPR.
        bcs_reg HS (10%bv : bv 5) (w64 vsx) R10'
          ltac:(rewrite (bcs_den _ _ 33 vsx 0 HAG ltac:(lia) X33 ltac:(lia)); f_equal; lia).
        bcs_shape. exact (KT2 Hc0 Hc1 _ _ HPR R10').
  - (* a0 <> s10: impossible, both are 1 *)
    exfalso. rewrite branch_eq_U in Hc.
    rewrite (bcs_U _ _ 10 1 HAG ltac:(lia) X10 ltac:(lia)), (bcs_U _ _ 26 1 HAG ltac:(lia) X26 ltac:(lia)) in Hc.
    cbn in Hc. discriminate Hc.
Qed.

(* +0x198: the UBSan guard `beqz a0` (decided not taken: p >= 4096), the checked byte at a0 = p against s4 = 0x13,
   the UBSan guard `bgeu a0,-2` (decided not taken: p <= 2 ^ 47 - 4), the checked byte at p + 2 against 0x70,
   then -10 (+0x43c) and the release. *)
Lemma bt_t2 : forall (W : world segs) (r : bvmap 5 word) (mem : word -> option byte) (md : Model)
    (p b0 b2 : Z) (Q : world segs -> config -> Prop),
  YK11.getr r 10 = w64 p -> YK11.getr r 20 = w64 19 -> YK11.getr r 25 = w64 SHADOW_OFF ->
  4096 <= p -> p <= bcs_PTRHI -> 0 <= b0 < 256 -> 0 <= b2 < 256 ->
  val_mem segs (mrestrict (w_H W) mem) p 1 b0 ->
  val_mem segs (mrestrict (w_H W) mem) (p + 2) 1 b2 ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF p 3 ->
  (forall x, p <= x < p + 3 -> ~ (SHADOW_OFF <= x < SHADOW_OFF + 17592186044416)) ->
  (b0 <> 19 \/ b2 <> 112 -> forall (r' : bvmap 5 word) mat, aregs_preserved r r' ->
     SRr segs W (bt_at BC_LOOP r' mem (with_vm_backing (m_vm_lazy md) mat md)) Q) ->
  (b0 = 19 -> b2 = 112 -> forall (r' : bvmap 5 word) mat, aregs_preserved r r' -> YK11.getr r' 10 = w64 (-10) ->
     SRr segs W (bt_at BC_REL r' mem (with_vm_backing (m_vm_lazy md) mat md)) Q) ->
  SRr segs W (bt_at (BT_AT 0x198) r mem md) Q.
Proof.
  intros W r mem md p b0 b2 Q R10 R20 R25 Hp1 Hp2 HB0 HB2 V0 V2 HRA HAPP KL KR.
  unfold bcs_PTRHI in Hp2.
  assert (X32 : ew (bt2_E r b0 b2) 32 = w64 b0)
    by (unfold bt2_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra r _ 0)).
  assert (X33 : ew (bt2_E r b0 b2) 33 = w64 b2)
    by (unfold bt2_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra r _ 1)).
  assert (X10 : ew (bt2_E r b0 b2) 10 = w64 p)
    by (unfold bt2_E; rewrite (bcs_ew_reg r _ 10 10%bv ltac:(lia) eq_refl); exact R10).
  assert (X20 : ew (bt2_E r b0 b2) 20 = w64 19)
    by (unfold bt2_E; rewrite (bcs_ew_reg r _ 20 20%bv ltac:(lia) eq_refl); exact R20).
  assert (X25 : ew (bt2_E r b0 b2) 25 = w64 SHADOW_OFF)
    by (unfold bt2_E; rewrite (bcs_ew_reg r _ 25 25%bv ltac:(lia) eq_refl); exact R25).
  assert (U10 : bv_unsigned (ew (bt2_E r b0 b2) 10) = p)
    by (rewrite X10; unfold w64; apply unsigned_lit_small; lia).
  assert (U25 : bv_unsigned (ew (bt2_E r b0 b2) 25) = SHADOW_OFF)
    by (rewrite X25; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (U32 : bv_unsigned (ew (bt2_E r b0 b2) 32) = b0)
    by (rewrite X32; unfold w64; apply unsigned_lit_small; lia).
  assert (U33 : bv_unsigned (ew (bt2_E r b0 b2) 33) = b2)
    by (rewrite X33; unfold w64; apply unsigned_lit_small; lia).
  assert (HS : st_ok_pi segs VAL (bt2_E r b0 b2) bt2_ss
    (restrict (w_H W) (@YK11.mkst fx r (Z_to_bv 64 (BASE + BT_AT 0x198)) mem (YK11.seg_rom segs)))).
  { rewrite restrict_mkst_fx. unfold bt2_ss. apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
    - apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - apply Forall_cons; [|apply Forall_nil]. unfold bt2_rg, YP09.region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U10.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      + apply (bcs_chunk1 _ _ 32 p 0 p b0 X32 HB0 ltac:(lia) V0).
      + apply (bcs_chunk1 _ _ 33 p 2 (p + 2) b2 X33 HB2 ltac:(lia) V2).
    - exact (conj I I).
    - unfold facts_ok, bt2_G. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
      unfold afact_ok, bcs_PTR, bcs_PTRHI. cbn [af_lo af_hi af_al2].
      rewrite U25, U10, U32, U33. rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SHADOW_OFF.
      repeat split; try exact I; lia. }
  assert (HSH : sh_ok segs bcs_Bx bt2_SH (bt2_E r b0 b2) (mrestrict (w_H W) mem)).
  { apply Forall_cons; [|apply Forall_nil].
    apply (shent_ok_of_range segs (w_H W) mem (bt2_E r b0 b2) bcs_Bx 10%nat p 3 p 0 3).
    - exact HRA.
    - unfold bcs_Bx. apply U_atom; [exact X25 | unfold SHADOW_OFF; lia].
    - apply U_atom; [exact X10 | lia].
    - lia.
    - lia.
    - intros x Hx. cbn [Z.min Z.max] in Hx. apply HAPP. lia. }
  assert (HEI : img_env VAL A_LIM (bt2_E r b0 b2)) by apply Eimg_env.
  pose proof (env_agree_refl 512 (bt2_E r b0 b2)) as HAG.
  bcs_step bt2_SH BC_LOOP.
  bcs_branch bt2_SH.
  - (* the byte at p is not 0x13: the loop head *)
    rewrite branch_ne_U in Hc.
    rewrite (bcs_U _ _ 32 b0 HAG ltac:(lia) X32 ltac:(lia)), (bcs_U _ _ 20 19 HAG ltac:(lia) X20 ltac:(lia)) in Hc.
    apply negb_true_iff, Z.eqb_neq in Hc.
    bcs_step bt2_SH BC_LOOP.
    bt_kept r [w64 b0; w64 b2] HPR. bcs_shape. exact (KL (or_introl Hc) _ _ HPR).
  - (* the byte at p is 0x13 *)
    rewrite branch_ne_U in Hc.
    rewrite (bcs_U _ _ 32 b0 HAG ltac:(lia) X32 ltac:(lia)), (bcs_U _ _ 20 19 HAG ltac:(lia) X20 ltac:(lia)) in Hc.
    apply negb_false_iff, Z.eqb_eq in Hc.
    bcs_step bt2_SH BC_LOOP.
    bcs_branch bt2_SH.
    + (* the byte at p + 2 is not 0x70: the loop head *)
      rewrite branch_ne_U in Hc0.
      rewrite (bcs_U _ _ 33 b2 HAG ltac:(lia) X33 ltac:(lia)), U_lit in Hc0 by lia.
      apply negb_true_iff, Z.eqb_neq in Hc0.
      bcs_step bt2_SH BC_LOOP.
      bt_kept r [w64 b0; w64 b2] HPR. bcs_shape. exact (KL (or_intror Hc0) _ _ HPR).
    + (* the byte at p + 2 is 0x70: a0 = -10 and the release *)
      rewrite branch_ne_U in Hc0.
      rewrite (bcs_U _ _ 33 b2 HAG ltac:(lia) X33 ltac:(lia)), U_lit in Hc0 by lia.
      apply negb_false_iff, Z.eqb_eq in Hc0.
      bcs_step bt2_SH BC_REL.
      bt_kept r [w64 b0; w64 b2] HPR.
      bcs_reg HS (10%bv : bv 5) (w64 (-10)) R10'
        ltac:(cbn [sv_denot]; unfold w64; apply bv_eq; rewrite !Z_to_bv_unsigned; reflexivity).
      bcs_shape. exact (KR Hc Hc0 _ _ HPR R10').
Qed.

(* ------------------------------------------------------------------ *)
(* The cut                                                             *)
(* ------------------------------------------------------------------ *)

Variable B : asyms.
Variable MT : ameter_ops.

Lemma bl_test : @bl_test_stmt fx rc B MT.
Proof.
  unfold bl_test_stmt.
  intros HLAWS STK sp0 FP lyx Sx W0 mem0 md0 own lyc Sc W memc mdc k regs body bb pos sp1 F cp st mj
    W3 regs3 mem3 md3 ly3 S3 Q HFIX Hcp Hst Hmj HAF KLOOP KSCAN KREL.
  pose proof HLAWS as (_ & LAWS & _).
  destruct HAF as (HC3 & HR3 & H10 & _ & Hm3 & _).
  pose proof HFIX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HF4096 & _ & HFceil & _).
  unfold BC_FBYTES in HFceil.
  pose proof HC3 as (HJ3 & Hperm & _ & _ & _ & _ & _ & HG3 & HSRC3).
  pose proof HJ3 as (HAR3 & _).
  pose proof asan_consts as (C1 & _).
  (* the length of the body: below 2 ^ 47 (trans_src_ok_place when there are bytes) *)
  assert (Hlen47 : Z.of_nat (length bb) <= 2 ^ 47).
  { destruct (Nat.eq_dec (length bb) 0) as [E0|E0]; [rewrite E0; lia|].
    pose proof (trans_src_ok_place B LAWS ly3 S3 W3 mem3 md3 body _ HAR3 (HSRC3 ltac:(lia)) ltac:(lia)) as Hp.
    destruct Hp as [Hp|Hp]; lia. }
  pose proof HR3 as (((R2 & R3 & R4 & R8 & R9 & R23 & R24) & R19 & R25) & R18 & R20 & R21 & R22 & R26 & R27).
  destruct (Z.eq_dec (mr_code (msg_step bb cp st)) 1) as [Hc1 | Hc1].
  - (* a result of 1: the status and sysex test *)
    destruct (bt_msg_code1 body mj (msg_step bb cp st) Hmj Hc1) as (pre & post & Ecb & Hpre).
    unfold BMN.trans_mn_msg_bytes in Hm3. rewrite Ecb in Hm3.
    set (sx := if writes_sysex (mr_kind (msg_step bb cp st))
               then body + Z.of_nat (mr_sysex (msg_step bb cp st)) else 0) in Hm3.
    set (sl := Z.of_nat (mr_sysex_len (msg_step bb cp st))) in Hm3.
    destruct (bt_garr8_c1 _ _ _ _ Hm3) as [V0 B0].
    pose proof (bt_garr8_c8 _ (F + 96) (b8 (mr_status (msg_step bb cp st)) :: pre) sx
      (BTMem.le8 (Z_to_bv 64 sl) ++ post) 8 Hm3 ltac:(cbn [length]; lia)) as V8.
    assert (Hm3b : garr8 segs (mrestrict (w_H W3) mem3) (F + 96)
      (map bz (((b8 (mr_status (msg_step bb cp st)) :: pre) ++ BTMem.le8 (Z_to_bv 64 sx)) ++
               BTMem.le8 (Z_to_bv 64 sl) ++ post)))
      by (rewrite <- app_assoc; exact Hm3).
    pose proof (bt_garr8_c8 _ (F + 96) _ sl post 16 Hm3b
      ltac:(rewrite length_app, BTMem.length_le8; cbn [length]; lia)) as V16.
    assert (Hne : is_end (msg_step bb cp st) = false).
    { destruct (is_end _) eqn:Ee; [|reflexivity]. exfalso. apply bt_is_end_code in Ee. lia. }
    apply (bt_t1o W3 regs3 mem3 md3 (F + 96) (bz (b8 (mr_status (msg_step bb cp st)))) (sx mod 2 ^ 64)
             (sl mod 2 ^ 64) Q ltac:(rewrite H10, Hc1; reflexivity) R18 R22 R26 R27 ltac:(lia) ltac:(lia) B0
             ltac:(apply Z.mod_pos_bound; lia) ltac:(apply Z.mod_pos_bound; lia) V0 V8 V16).
    + (* the status is not 0xf0: not a sysex *)
      intros Hs0 regs4 mat HPR. apply KLOOP; [exact Hne | | exact (bt_loop_kept _ _ _ _ _ _ HR3 HPR)].
      destruct (refused bb _) eqn:Er; [|reflexivity]. exfalso. apply Hs0.
      apply bt_refused_kind in Er.
      rewrite (proj2 (msg_step_code1_f0 bb cp st Hst Hc1) Er). apply bz_b8. lia.
    + (* a sysex shorter than 3 *)
      intros Hs0 Hlt regs4 mat HPR. apply KLOOP; [exact Hne | | exact (bt_loop_kept _ _ _ _ _ _ HR3 HPR)].
      pose proof (bt_kind_sysex bb cp st Hst Hc1 Hs0) as Hk.
      destruct (msg_step_sysex bb cp st Hk) as (_ & _ & Hsl & _).
      assert (Hs3 : (mr_sysex_len (msg_step bb cp st) < 3)%nat).
      { rewrite Z.mod_small in Hlt by (unfold sl; lia). unfold sl in Hlt. lia. }
      unfold refused. rewrite Hk, (proj2 (Nat.leb_gt 3 _) Hs3). reflexivity.
    + (* a sysex of 3 or more: the two body bytes *)
      intros Hs0 Hge regs1 mat1 HPR1 R10'.
      pose proof (bt_kind_sysex bb cp st Hst Hc1 Hs0) as Hk.
      destruct (msg_step_sysex bb cp st Hk) as (_ & Hsx & Hsl & _).
      assert (Esx : sx = body + Z.of_nat (S cp)) by (unfold sx; rewrite Hk, Hsx; reflexivity).
      assert (Hs3 : (3 <= mr_sysex_len (msg_step bb cp st))%nat).
      { rewrite Z.mod_small in Hge by (unfold sl; lia). unfold sl in Hge. lia. }
      (* the body has bytes here: decode_rd_ok and its place at the state after the call (bc_cur) *)
      assert (HL : (0 < length bb)%nat) by lia.
      pose proof (trans_src_ok_rd B LAWS ly3 S3 W3 mem3 md3 body _ HAR3 (HSRC3 HL) ltac:(lia)) as HRD.
      pose proof (trans_src_ok_place B LAWS ly3 S3 W3 mem3 md3 body _ HAR3 (HSRC3 HL) ltac:(lia)) as HPL.
      pose proof HRD as (_ & HRAb & _ & Ham & _).
      unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Ham.
      assert (Hb4096 : 4096 <= body) by (destruct HPL as [Hp|Hp]; lia).
      assert (Hl47 : body + Z.of_nat (length bb) <= 140737488355327) by lia.
      rewrite Esx, Z.mod_small in R10' by lia.
      assert (Hj1 : (S cp < length (map bz bb))%nat) by (rewrite length_map; lia).
      assert (Hj2 : (S cp + 2 < length (map bz bb))%nat) by (rewrite length_map; lia).
      destruct (HG3 _ Hj1) as [VB0 RB0]. destruct (HG3 _ Hj2) as [VB2 RB2].
      rewrite bcs_nth_bz in VB0, RB0, VB2, RB2.
      replace (body + Z.of_nat (S cp + 2)) with (body + Z.of_nat (S cp) + 2) in VB2 by lia.
      pose proof (range_addressable_sub _ _ body (Z.of_nat (length bb)) (body + Z.of_nat (S cp)) 3 HRAb
        ltac:(lia) ltac:(lia)) as HRA.
      assert (HAPP : forall x, body + Z.of_nat (S cp) <= x < body + Z.of_nat (S cp) + 3 ->
                       ~ (SHADOW_OFF <= x < SHADOW_OFF + 17592186044416)).
      { intros x Hx. unfold SHADOW_OFF. lia. }
      apply (bt_t2 W3 regs1 mem3 _ (body + Z.of_nat (S cp)) (at8 bb (S cp)) (at8 bb (S cp + 2)) Q R10'
               ltac:(bt_kp HPR1 R20 20) ltac:(bt_kp HPR1 R25 25)
               ltac:(lia) ltac:(unfold bcs_PTRHI; lia) RB0 RB2 VB0 VB2 HRA HAPP).
      * (* one of the two bytes differs: the loop head *)
        intros Hor regs2 mat2 HPR2. rewrite wvb_collapse.
        apply KLOOP; [exact Hne | |
                      exact (bt_loop_kept _ _ _ _ _ _ HR3 (aregs_preserved_trans _ _ _ HPR1 HPR2))].
        unfold refused. rewrite Hk, Hsx.
        destruct Hor as [Hb | Hb].
        -- rewrite (proj2 (Z.eqb_neq _ _) Hb), andb_false_r. reflexivity.
        -- rewrite (proj2 (Z.eqb_neq _ _) Hb), andb_false_r. reflexivity.
      * (* F0 13 xx 70: the release with -10 *)
        intros Hb0 Hb2 regs2 mat2 HPR2 R10''. rewrite wvb_collapse.
        apply KREL.
        -- unfold refused. rewrite Hk, Hsx, Hb0, Hb2, (proj2 (Nat.leb_le 3 _) Hs3). reflexivity.
        -- exact (proj1 (proj1 (bt_loop_kept _ _ _ _ _ _ HR3 (aregs_preserved_trans _ _ _ HPR1 HPR2)))).
        -- exact R10''.
  - (* another result: the end, or an error code *)
    apply (bt_t1x W3 regs3 mem3 md3 (mr_code (msg_step bb cp st)) Q H10 R26 Hc1
             ltac:(pose proof (bt_code_range (msg_step bb cp st)); lia)).
    + intros Hc0 regs4 mat HPR. apply KLOOP; [| | exact (bt_loop_kept _ _ _ _ _ _ HR3 HPR)].
      * destruct (is_end _) eqn:Ee; [|reflexivity]. exfalso. apply Hc0. apply bt_is_end_code. exact Ee.
      * destruct (refused bb _) eqn:Er; [|reflexivity]. exfalso. apply Hc1.
        apply bt_refused_kind in Er. unfold mr_code. rewrite Er. reflexivity.
    + intros Hc0 regs4 mat HPR. apply KSCAN.
      * apply bt_is_end_code. exact Hc0.
      * exact (proj1 (bt_loop_kept _ _ _ _ _ _ HR3 HPR)).
Qed.

End bt.
