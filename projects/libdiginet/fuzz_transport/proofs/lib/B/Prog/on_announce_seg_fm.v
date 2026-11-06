(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, origin/cold/pg-prog), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/CanKit.v, with its module paths and module names changed; 496 of its 563 lines of code are new or changed and 457 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/B/Prog/SrxBDeskKit.v, with its module paths and module names changed; 1390 of its 1495 lines of code are new or changed and 458 lines of the source are left out. *)
(* on_announce_seg_fm: Lemma onann_fm_piece : onann_fm_stmt (lib/B/Prog/OnannCutB.v), the find_mac piece of
   on_announce's image-B walk, offsets +0x250 .. +0x2fc of the listing lib/B/Prog/DgnTransportBList.v
   (fuzz_transport.asan-ubsan 0x87f18 .. 0x87fc4), ending at the desk-notice cut onann_dn_at (+0x300).

   What the code does (transport/src/diginet_session.c:168-174, find_mac inlined). +0x250 `bne a0, zero`: a0 = s & 7
   = 0 (onann_regs_fm), so UBSan's trap word at +0x774 is not reached. +0x254, +0x258: a6 = p and s6 = fp spilled at
   s1 + 32 and s1 + 40. +0x25c `ld s11, 32(s10)`: unknown_len = 15 (onann_a_ok). +0x260 `li s6, 6`; +0x264
   `bgeu s11, s6` is taken (15 >= 6), so the +0x268 arm is not reached. +0x278, +0x27c: s8 and s9 spilled at s1 + 0
   and s1 + 8. +0x280 `li s9, 0` (i = 0); +0x284 `ld s8, 24(s10)`: unknown = buf + 30 (onann_a_ok); +0x288
   `snez s7, s8` = 1 (buf + 30 > 0); +0x28c, +0x290: s5 = s10 = unknown.
   The loop at +0x294, for i = 0 .. 9: `bltu s10, s8` (s10 = unknown + i >= unknown) and `beq a0, zero` with
   a0 = s7 xor (s10 = 0) = 1 (the two UBSan pointer checks of unknown + i) are both refuted; a0 = unknown + i,
   a1 = s, a2 = 6 and `jal` the bcmp wrapper (+0x2b0, abcmp_realizes through TransportGCg.v gx_call_leaf and
   YCbq.v aj_bcmp_at); a result 0 goes to +0x2e4 (a5 = s9 = i), else s9, s10, s6, s5 are bumped by one and
   `bgeu s11, s6` (15 >= 6 + i + 1) runs the turn again, and after the ten turns a5 = -1. Both exits reload
   s9 = F, s8 = SHADOW_OFF, s6 = fp, s10 = a from s1 + 8, s1 + 0, s1 + 40, s1 + 16, then a6 = p from s1 + 32 and
   a1 = 1, and fall into the desk-notice cut at +0x300.

   The walk: one run from +0x250 to the loop head +0x294 (ONANN_FMLP), then the turn lemma fm_turn, used by an
   induction on the turns left (fm_loop). The loop invariant fm_inv holds onann_cur at e = 0, the world
   onann_w1 timg_B Bw b, a's fields (onann_a_ok), the spill slots the exits read, the registers at the loop head
   (s5 = s10 = buf + 30 + i, s6 = 6 + i, s7 = 1, s8 = buf + 30, s9 = i, s11 = 15), 0 <= i <= 9, and the model
   equation onann_off (onann_w1 ..) b = TSess.v find_mac_loop (ann_unknown (fr_body b)) (S_cfg_host_mac ..) i
   (10 - i). The bcmp result is 0 exactly when the six bytes at buf + 30 + i agree with g_s.cfg.host_mac's
   (fm_memeq_iff: the frame bytes at buf through onann_f30's garr8, g_s's through the world relation), which is
   TSess0.v memeq 6 (skipn i (ann_unknown (fr_body b))) (S_cfg_host_mac ..), the test of find_mac_loop.
   What the call keeps (acall_kept_g) is carried over each run and over the bcmp call by fm_keep
   (TransportGFrame.v dk_kept_step_gw): every byte the piece changes lies in the call's stack window
   [sp - ONANN_STK, sp). No byte of G is written, so the world relation is the cut's throughout. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TransportRtCg TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGFrame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TransportGRwB TransportGRunB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB CanKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_set_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import send_control_cg set_state_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_wake_cg maybe_online_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_tick_cg on_ack_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_personality_from_name_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_announce_parse_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import on_announce_cg OnannCutB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import on_announce_seg_kit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TSess0 TSess TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec DgnLib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 1. Arithmetic and list helpers                                      *)
(* ------------------------------------------------------------------ *)

Lemma fm_ltu : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
  bv_ltu (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof. intros a b Ha Hb. unfold bv_ltu. rewrite !unsigned_lit_small by lia. reflexivity. Qed.

Lemma fm_eqb : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
  bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 b) = (a =? b).
Proof.
  intros a b Ha Hb. unfold bv_eqb. rewrite !unsigned_lit_small by lia. reflexivity.
Qed.

Lemma fm_swrap32_id : forall x, -2 ^ 31 <= x < 2 ^ 31 -> bv_swrap 32 x = x.
Proof.
  intros x Hx. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma fm_m1 : Z_to_bv 64 18446744073709551615 = w64 (-1).
Proof. apply bv_eq. unfold w64. rewrite !Z_to_bv_unsigned. reflexivity. Qed.

Lemma fm_addiw : forall (E : env) (n : nat) (v : Z), ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 30 ->
  sv_denot E (SAluw ALU_ADD (SOff n 0) (SLit 1)) = Z_to_bv 64 (v + 1).
Proof.
  intros E n v Hn Hv. cbn [sv_denot].
  rewrite Hn, unsigned_lit_small by lia. rewrite Z.add_0_r.
  rewrite (zalu32_sound ALU_ADD v 1).
  f_equal. unfold zalu32, zu32, M32. cbn [zalu_raw].
  rewrite (Z.mod_small v (2 ^ 32)) by lia. change (1 mod 2 ^ 32) with 1.
  rewrite fm_swrap32_id by lia. unfold zcanon, M64. apply Z.mod_small. lia.
Qed.

Lemma fm_nth_skipn : forall (A : Type) (l : list A) (d : A) (m n : nat),
  nth n (skipn m l) d = nth (m + n) l d.
Proof.
  intros A l d m. revert l. induction m as [|m IH]; intros l n; [reflexivity|].
  destruct l as [|x l]; [destruct n; reflexivity|]. cbn [skipn]. rewrite IH. reflexivity.
Qed.

Lemma fm_nth_firstn : forall (A : Type) (l : list A) (d : A) (n k : nat), (k < n)%nat ->
  nth k (firstn n l) d = nth k l d.
Proof.
  intros A l d n. revert l. induction n as [|n IH]; intros l k Hk; [lia|].
  destruct l as [|x l]; [destruct k; reflexivity|]. cbn [firstn].
  destruct k as [|k]; [reflexivity|]. cbn [nth]. apply IH. lia.
Qed.

(* The byte at index j of the frame bytes b, as the model's at8. *)
Lemma fm_at8_body : forall (b : list byte) (j : nat),
  (j < Z.to_nat (DSpec.fr_body_len b))%nat -> (j < 15)%nat ->
  DSpec.at8 (DSpec.ann_unknown (DSpec.fr_body b)) j = DSpec.at8 b (30 + j).
Proof.
  intros b j Hj H15. unfold DSpec.at8, DSpec.ann_unknown, DSpec.fr_body.
  rewrite fm_nth_firstn by lia. rewrite fm_nth_firstn by lia. rewrite fm_nth_skipn. reflexivity.
Qed.

(* The byte at index n of a tail of l. *)
Lemma fm_at8_skipn : forall (l : list byte) (m n : nat), DSpec.at8 (skipn m l) n = DSpec.at8 l (m + n).
Proof. intros l m n. unfold DSpec.at8. rewrite fm_nth_skipn. reflexivity. Qed.

(* The byte at index j of a world's g_s.cfg.host_mac. *)
Lemma fm_at8_mac : forall (X : list byte) (j : nat), (j < 6)%nat ->
  DSpec.at8 (TW.S_cfg_host_mac X) j = DSpec.at8 X (Z.to_nat TW.OFF_g_s + j).
Proof.
  intros X j Hj. unfold DSpec.at8, TW.S_cfg_host_mac, TW.sub, TW.A_S_cfg_host_mac.
  rewrite fm_nth_firstn by lia. rewrite fm_nth_skipn.
  replace (Z.to_nat (TW.OFF_g_s + 0)) with (Z.to_nat TW.OFF_g_s) by (unfold TW.OFF_g_s; lia).
  reflexivity.
Qed.

(* A shadow byte of an address below 2 ^ 63 is an address. *)
Lemma fm_sh_range : forall x, 0 <= x < 2 ^ 63 -> 0 <= shadow_of_addr SHADOW_OFF x < 2 ^ 64.
Proof.
  intros x Hx. pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)) as D0.
  assert (D1 : x / 8 <= x) by (apply Z.div_le_upper_bound; lia).
  unfold shadow_of_addr, SHADOW_OFF. lia.
Qed.

(* ... and so is every byte of the shadow hull of a range below 2 ^ 63. *)
Lemma fm_hull_range : forall q n s, 0 <= q -> q + n <= 2 ^ 63 -> 0 <= n ->
  shadow_addr q / 8 * 8 <= s < shadow_addr (q + n - 1) / 8 * 8 + 8 -> 0 <= s < 2 ^ 64.
Proof.
  intros q n s Hq Hqn Hn Hs. unfold shadow_addr, SHADOW_OFF in Hs.
  pose proof (Z.div_pos q 8 ltac:(lia) ltac:(lia)) as D0.
  pose proof (Z.div_pos (q + n - 1) 8 ltac:(lia) ltac:(lia)) as D1.
  assert (D2 : (q + n - 1) / 8 <= q + n - 1) by (apply Z.div_le_upper_bound; lia).
  assert (D3 : 0 <= (2147483648 + q / 8) / 8) by (apply Z.div_pos; lia).
  assert (D4 : (2147483648 + (q + n - 1) / 8) / 8 <= 2147483648 + (q + n - 1) / 8)
    by (apply Z.div_le_upper_bound; lia).
  lia.
Qed.

(* memeq of the six bytes, as six byte equations. *)
Lemma fm_memeq_iff : forall (x y : list byte),
  TS0.memeq 6 x y = true <-> (forall j, (j < 6)%nat -> DSpec.at8 x j = DSpec.at8 y j).
Proof.
  intros x y. unfold TS0.memeq. cbn [seq forallb].
  rewrite !Bool.andb_true_iff. split.
  - intros (H0 & H1 & H2 & H3 & H4 & H5 & _) j Hj.
    do 6 (destruct j as [|j]; [first [apply Z.eqb_eq; exact H0 | apply Z.eqb_eq; exact H1 |
      apply Z.eqb_eq; exact H2 | apply Z.eqb_eq; exact H3 | apply Z.eqb_eq; exact H4 |
      apply Z.eqb_eq; exact H5]|]). lia.
  - intros H. repeat split; try exact I; apply Z.eqb_eq; apply H; lia.
Qed.

(* One turn of the model's loop. *)
Lemma fm_find_mac_S : forall (u mac : list byte) (i : Z) (f : nat),
  TSS.find_mac_loop u mac i (S f) =
  (if TS0.memeq 6 (skipn (Z.to_nat i) u) mac then i else TSS.find_mac_loop u mac (i + 1) f).
Proof. intros u mac i f. reflexivity. Qed.

Lemma fm_find_mac_m_eq : forall (u mac : list byte),
  TSS.find_mac_m u 15 mac = TSS.find_mac_loop u mac 0 (Z.to_nat (10 - 0)).
Proof. intros u mac. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* 2. The symbolic states                                              *)
(* ------------------------------------------------------------------ *)

(* The loop head (+0x294, the first UBSan pointer check of unknown + i). *)
Definition ONANN_FMLP : Z := AF_on_announce + 0x294.

(* +0x250 .. +0x294: the two spill pairs the piece writes ([s1, s1 + 16) and [s1 + 32, s1 + 48); the words at
   s1 + 16 and s1 + 24, a and now, are not touched), and a's unknown and unknown_len at a + 24 and a + 32
   (s10 = a, atom 26; atom 32 = unknown = buf + 30). *)
Definition fm_rg_sl : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0 48 0 48
    [YP09.mkChunk 16 (YP09.CVal 8 (SOff 33 0)); YP09.mkChunk 24 (YP09.CVal 8 (SOff 34 0))].
Definition fm_rg_a : YP09.region :=
  YP09.mkRegion (Some 26%nat) 24 40 0 0
    [YP09.mkChunk 24 (YP09.CVal 8 (SOff 32 0)); YP09.mkChunk 32 (YP09.CVal 8 (SLit 15))].
Definition fm_facts_a : facts :=
  mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 0); (32%nat, mkAF 30 (2 ^ 63) 0)] [] [].
Definition ss_fm_a : sstate := mkSS ONANN_FM sr_atoms [fm_rg_sl; fm_rg_a] None fm_facts_a.

(* A turn from +0x294: the spill slots, read-only (SHADOW_OFF, F, a, p, fp at s1 + 0, 8, 16, 32, 40); the atoms
   24 (s8 = unknown) and 26 (s10 = unknown + i) are positive. *)
Definition fm_rg_slt : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0 48 0 0
    [YP09.mkChunk 0 (YP09.CVal 8 (SLit SHADOW_OFF)); YP09.mkChunk 8 (YP09.CVal 8 (SOff 19 0));
     YP09.mkChunk 16 (YP09.CVal 8 (SOff 19 32)); YP09.mkChunk 32 (YP09.CVal 8 (SOff 32 0));
     YP09.mkChunk 40 (YP09.CVal 8 (SOff 33 0))].
Definition fm_facts_t : facts :=
  mkFacts [(24%nat, mkAF 30 (2 ^ 63) 0); (26%nat, mkAF 30 (2 ^ 63) 0)] [] [].
Definition ss_fm_t : sstate := mkSS ONANN_FMLP sr_atoms [fm_rg_slt] None fm_facts_t.

(* The register and region readers of a symbolic state (on_ack_seg_ign.v's). *)
Ltac fm_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  end.
Ltac fm_region HS i HR :=
  lazymatch type of HS with
  | st_ok_pi ?sg ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let r0 := eval vm_compute in (nth i (ss_mem ssx) got_regionP) in
      assert (HR : region_ok sg Ex (ms_mem (restrict Hh msx)) r0)
        by (let HS' := fresh in pose proof HS as HS'; unfold st_ok_pi in HS';
            eapply (can_region_nth Ex _ (restrict Hh msx) i r0 HS'); vm_compute; reflexivity)
  end; cbn [ms_mem restrict] in HR.
Ltac fm_in := cbn [In]; repeat (first [left; reflexivity | right]).
Ltac fm_awr_rs :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.

Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

(* An 8-byte word of memory, read off rdword at the walk's view. *)
Lemma fm_val_rdword : forall (H : word -> bool) mem a v, 0 <= v < 2 ^ 64 ->
  rdword (aview segs H mem) a = Some v -> YI04.val_mem segs (mrestrict H mem) a 8 v.
Proof. intros H mem a v _ Hw. exact (val_mem_of_rdword segs H mem a v Hw). Qed.

Definition fm_EA (regs2 : bvmap 5 word) (buf aa now : Z) : env :=
  Eimg (PI := PI_transportb) (Ereg regs2 [w64 (buf + 30); w64 aa; w64 now]).
Definition fm_ET (regsT : bvmap 5 word) (pv fp : Z) : env :=
  Eimg (PI := PI_transportb) (Ereg regsT [w64 pv; w64 fp]).

Lemma fm_EA_reg : forall regs2 buf aa now n (r : bv 5), Z.of_nat n = bv_unsigned r ->
  ew (fm_EA regs2 buf aa now) n = YK11.getr regs2 r.
Proof. intros regs2 buf aa now n r Hn. unfold fm_EA. apply can_ew_Eimg_Ereg_nat. exact Hn. Qed.
Lemma fm_EA_x : forall regs2 buf aa now, ew (fm_EA regs2 buf aa now) 32 = w64 (buf + 30).
Proof.
  intros regs2 buf aa now. unfold fm_EA. rewrite Eimg_low by (unfold A_TEXT; lia).
  exact (ew_Ereg_extra regs2 _ 0).
Qed.
Lemma fm_EA_x1 : forall regs2 buf aa now, ew (fm_EA regs2 buf aa now) 33 = w64 aa.
Proof.
  intros regs2 buf aa now. unfold fm_EA. rewrite Eimg_low by (unfold A_TEXT; lia).
  exact (ew_Ereg_extra regs2 _ 1).
Qed.
Lemma fm_EA_x2 : forall regs2 buf aa now, ew (fm_EA regs2 buf aa now) 34 = w64 now.
Proof.
  intros regs2 buf aa now. unfold fm_EA. rewrite Eimg_low by (unfold A_TEXT; lia).
  exact (ew_Ereg_extra regs2 _ 2).
Qed.
Lemma fm_ET_reg : forall regsT pv fp n (r : bv 5), Z.of_nat n = bv_unsigned r ->
  ew (fm_ET regsT pv fp) n = YK11.getr regsT r.
Proof. intros regsT pv fp n r Hn. unfold fm_ET. apply can_ew_Eimg_Ereg_nat. exact Hn. Qed.
Lemma fm_ET_x0 : forall regsT pv fp, ew (fm_ET regsT pv fp) 32 = w64 pv.
Proof.
  intros regsT pv fp. unfold fm_ET. rewrite Eimg_low by (unfold A_TEXT; lia).
  exact (ew_Ereg_extra regsT _ 0).
Qed.
Lemma fm_ET_x1 : forall regsT pv fp, ew (fm_ET regsT pv fp) 33 = w64 fp.
Proof.
  intros regsT pv fp. unfold fm_ET. rewrite Eimg_low by (unfold A_TEXT; lia).
  exact (ew_Ereg_extra regsT _ 1).
Qed.

(* The symbolic state at +0x250 holds of the machine state there. *)
Lemma fm_entry_a : forall (W2 : world segs) (regs2 : bvmap 5 word) mem2 (sp1 F buf now : Z),
  YK11.getr regs2 9 = w64 sp1 -> YK11.getr regs2 26 = w64 (F + ONANN_A) ->
  4096 <= F -> F + 512 <= sp1 -> sp1 + 48 <= 2 ^ 47 ->
  0 < buf -> buf + 30 <= 2 ^ 63 -> 0 <= now < 2 ^ 64 -> 2 ^ 46 <= sp1 ->
  (forall a, sp1 <= a < sp1 + 48 -> apresent (w_H W2) mem2 a) ->
  rdword (aview segs (w_H W2) mem2) (F + ONANN_A + 24) = Some (buf + 30) ->
  rdword (aview segs (w_H W2) mem2) (F + ONANN_A + 32) = Some 15 ->
  YI04.val_mem segs (mrestrict (w_H W2) mem2) (sp1 + 16) 8 (F + ONANN_A) ->
  YI04.val_mem segs (mrestrict (w_H W2) mem2) (sp1 + 24) 8 now ->
  st_ok_pi segs VAL (fm_EA regs2 buf (F + ONANN_A) now) ss_fm_a
    (restrict (w_H W2) (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + ONANN_FM)) mem2 (YK11.seg_rom segs))).
Proof.
  intros W2 regs2 mem2 sp1 F buf now R9 R26 HF0 HFsp Hsp47 Hbuf0 Hbuf63 Hnow Hsplo Hpres Hrd24 Hrd32
    Hv16 Hv24.
  set (E := fm_EA regs2 buf (F + ONANN_A) now).
  assert (U9 : bv_unsigned (ew E 9) = sp1)
    by (unfold E; rewrite (fm_EA_reg regs2 buf _ now 9 9%bv eq_refl), R9; unfold w64;
        apply unsigned_lit_small; lia).
  assert (U26 : bv_unsigned (ew E 26) = F + ONANN_A)
    by (unfold E; rewrite (fm_EA_reg regs2 buf _ now 26 26%bv eq_refl), R26; unfold w64;
        apply unsigned_lit_small; unfold ONANN_A; lia).
  assert (E32 : ew E 32 = w64 (buf + 30)) by (unfold E; apply fm_EA_x).
  assert (E33 : ew E 33 = w64 (F + ONANN_A)) by (unfold E; apply fm_EA_x1).
  assert (E34 : ew E 34 = w64 now) by (unfold E; apply fm_EA_x2).
  assert (U32 : bv_unsigned (ew E 32) = buf + 30)
    by (rewrite E32; unfold w64; apply unsigned_lit_small; lia).
  unfold ONANN_A in U26, Hrd24, Hrd32, E33, Hv16.
  rewrite restrict_mkst_fx. unfold ss_fm_a.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok, fm_rg_sl, fm_rg_a;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
      rewrite ?U9, ?U26.
    + split; [lia|]. split; [lia|]. split.
      * intros o Ho. apply (apresent_writable segs (w_H W2)). apply Hpres. lia.
      * repeat apply Forall_cons; try apply Forall_nil.
        -- apply (chunk_ok_val segs E _ sp1 16 8 (SOff 33 0) (F + 32));
             [cbn [sv_denot]; rewrite E33, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity
             | lia | lia | exact Hv16].
        -- apply (chunk_ok_val segs E _ sp1 24 8 (SOff 34 0) now);
             [cbn [sv_denot]; rewrite E34, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity
             | lia | lia | exact Hv24].
    + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val segs E _ (F + 32) 24 8 (SOff 32 0) (buf + 30));
          [cbn [sv_denot]; rewrite E32, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity
          | lia | lia |].
        exact (fm_val_rdword (w_H W2) mem2 (F + 32 + 24) (buf + 30) ltac:(lia) Hrd24).
      * apply (chunk_ok_val segs E _ (F + 32) 32 8 (SLit 15) 15);
          [cbn [sv_denot]; reflexivity | lia | lia |].
        exact (fm_val_rdword (w_H W2) mem2 (F + 32 + 32) 15 ltac:(lia) Hrd32).
  - apply pairwise_disjoint_of_extents.
    unfold extent_of_region, fm_rg_sl, fm_rg_a.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U26.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; first [exact I | lia].
  - unfold fm_facts_a, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U32, U9.
    rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

(* The symbolic state at the loop head holds of the machine state there. *)
Lemma fm_entry_t : forall (W2 : world segs) (regsT : bvmap 5 word) memT (sp1 F buf pv fp i : Z),
  YK11.getr regsT 9 = w64 sp1 -> YK11.getr regsT 19 = w64 F ->
  YK11.getr regsT 24 = w64 (buf + 30) -> YK11.getr regsT 26 = w64 (buf + 30 + i) ->
  4096 <= F -> F + 512 <= sp1 -> sp1 + 48 <= 2 ^ 47 ->
  0 <= pv < 2 ^ 64 -> 0 <= fp < 2 ^ 64 -> 0 <= i <= 9 ->
  0 < buf -> buf + 30 + i <= 2 ^ 63 ->
  YI04.val_mem segs (mrestrict (w_H W2) memT) sp1 8 SHADOW_OFF ->
  YI04.val_mem segs (mrestrict (w_H W2) memT) (sp1 + 8) 8 F ->
  YI04.val_mem segs (mrestrict (w_H W2) memT) (sp1 + 16) 8 (F + ONANN_A) ->
  YI04.val_mem segs (mrestrict (w_H W2) memT) (sp1 + 32) 8 pv ->
  YI04.val_mem segs (mrestrict (w_H W2) memT) (sp1 + 40) 8 fp ->
  st_ok_pi segs VAL (fm_ET regsT pv fp) ss_fm_t
    (restrict (w_H W2) (@YK11.mkst fx regsT (Z_to_bv 64 (BASE + ONANN_FMLP)) memT (YK11.seg_rom segs))).
Proof.
  intros W2 regsT memT sp1 F buf pv fp i R9 R19 R24 R26 HF0 HFsp Hsp47 Hpv Hfp Hi Hbuf0 Hbuf63
    Hrd0 Hrd8 Hrd16 Hrd32 Hrd40.
  set (E := fm_ET regsT pv fp).
  assert (U9 : bv_unsigned (ew E 9) = sp1)
    by (unfold E; rewrite (fm_ET_reg regsT pv fp 9 9%bv eq_refl), R9; unfold w64;
        apply unsigned_lit_small; lia).
  assert (E19 : ew E 19 = w64 F) by (unfold E; rewrite (fm_ET_reg regsT pv fp 19 19%bv eq_refl); exact R19).
  assert (U19 : bv_unsigned (ew E 19) = F)
    by (rewrite E19; unfold w64; apply unsigned_lit_small; lia).
  assert (U24 : bv_unsigned (ew E 24) = buf + 30)
    by (unfold E; rewrite (fm_ET_reg regsT pv fp 24 24%bv eq_refl), R24; unfold w64;
        apply unsigned_lit_small; lia).
  assert (U26 : bv_unsigned (ew E 26) = buf + 30 + i)
    by (unfold E; rewrite (fm_ET_reg regsT pv fp 26 26%bv eq_refl), R26; unfold w64;
        apply unsigned_lit_small; lia).
  assert (E32 : ew E 32 = w64 pv) by (unfold E; apply fm_ET_x0).
  assert (E33 : ew E 33 = w64 fp) by (unfold E; apply fm_ET_x1).
  unfold ONANN_A in Hrd16.
  rewrite restrict_mkst_fx. unfold ss_fm_t.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok, fm_rg_slt;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
      rewrite ?U9.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    + apply (chunk_ok_val segs E _ sp1 0 8 (SLit SHADOW_OFF) SHADOW_OFF);
        [cbn [sv_denot]; reflexivity | unfold SHADOW_OFF; lia | lia |].
      rewrite Z.add_0_r. exact Hrd0.
    + apply (chunk_ok_val segs E _ sp1 8 8 (SOff 19 0) F);
        [cbn [sv_denot]; rewrite E19, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity
        | lia | lia |].
      exact Hrd8.
    + apply (chunk_ok_val segs E _ sp1 16 8 (SOff 19 32) (F + 32));
        [cbn [sv_denot]; rewrite U19; reflexivity | lia | lia |].
      exact Hrd16.
    + apply (chunk_ok_val segs E _ sp1 32 8 (SOff 32 0) pv);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity
        | lia | lia |].
      exact Hrd32.
    + apply (chunk_ok_val segs E _ sp1 40 8 (SOff 33 0) fp);
        [cbn [sv_denot]; rewrite E33, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity
        | lia | lia |].
      exact Hrd40.
  - apply pairwise_disjoint_of_extents.
    cbn [map zpairwise_disjoint zall_disjoint]. repeat split; exact I.
  - unfold fm_facts_t, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U24, U26.
    rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

End e.

(* ------------------------------------------------------------------ *)
(* 3. The bcmp wrapper at the walk's own G journal                     *)
(* ------------------------------------------------------------------ *)

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Local Abbreviation segs := tfibsegs.
Hypothesis LAWS : AR_laws segs B.
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).

(* check_latest_sent_seg_cj.v cls_bcmp at this walk's journal: the journal and every byte outside the wrapper's
   own stack window are kept, and a0 is 0 exactly when the two ranges hold the same bytes. *)
Lemma fm_bcmp :
  forall (STK sp0 : Z) FP ly S (W0 : world segs) mem0 md0 own lyc Sc (W : world segs)
         (memT : word -> option byte) mdc k (regsT : bvmap 5 word) (x y n o : Z) (raw : word),
  @abcmp_realizes fx rc segs B (transportb_sigma TB___interceptor_trampoline_bcmp) ->
  ajournal_gx TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memT mdc k ->
  YK11.getr regsT 10 = w64 x -> YK11.getr regsT 11 = w64 y -> YK11.getr regsT 12 = w64 n ->
  0 <= n < 2 ^ 32 -> 0 <= x -> x + n <= 2 ^ 63 -> 0 <= y -> y + n <= 2 ^ 63 ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 2 * ESTACK - o <= STK ->
  YK11.getr regsT 3 = w64 (as_gp B) -> YK11.getr regsT 4 = w64 (as_tp B) ->
  YK11.getr regsT 1 = raw -> YK0s.ret_ok raw ->
  src_ok segs W regsT memT x n -> src_ok segs W regsT memT y n ->
  (forall a, x <= a < x + n -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o)) ->
  (forall a, y <= a < y + n -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o)) ->
  amem_range x n -> amem_range y n ->
  range_addressable (aview segs (w_H W) memT) SHADOW_OFF x n ->
  (0 < n -> shadow_hull_vis (aview segs (w_H W) memT) x n) ->
  range_addressable (aview segs (w_H W) memT) SHADOW_OFF y n ->
  (0 < n -> shadow_hull_vis (aview segs (w_H W) memT) y n) ->
  SRr segs W
    (mkCfg (@YK11.mkst fx regsT (Z_to_bv 64 (transportb_sigma TB___interceptor_trampoline_bcmp)) memT
              (YK11.seg_rom segs)) mdc)
    (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
       c2 = mkCfg (@YK11.mkst fx regs2 raw mem2 (YK11.seg_rom segs)) md2 /\
       ajournal_gx TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k /\
       (exists v : word, aregs_preserved regsT regs2 /\ YK11.getr regs2 10 = v /\
          (v = w64 0 <-> forall j, 0 <= j < n ->
             aview segs (w_H W) memT (x + j) = aview segs (w_H W) memT (y + j)) /\
          (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o) ->
             aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
          (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a))).
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memT mdc k regsT x y n o raw
    AM HJ H10 H11 H12 Hn Hx0 Hxn Hy0 Hyn Hsp Hal Hneg Hbud Hgp Htp Hra Hraw
    Hsx Hsy Hbx Hby Hmx Hmy Hrx Hhx Hry Hhy.
  apply (@gx_call_leaf fx rc tfib_sink_head segs B TG.G_HARNESS_B STK sp0 FP ly S W0 mem0 md0 own
           lyc Sc W memT mdc k _ raw _ HJ).
  intros memS HJi.
  eapply SRr_mono.
  { exact (@aj_bcmp_at fx rc tfib_sink_head segs B LAWS transportb_segs_low
             (transportb_sigma TB___interceptor_trampoline_bcmp) AM W regsT memT STK sp0 FP ly S W0 memS md0 own
             lyc Sc mdc k x y n o raw HJi H10 H11 H12 Hn Hx0 Hxn Hy0 Hyn Hsp Hal Hneg Hbud Hgp Htp Hra Hraw
             Hsx Hsy Hbx Hby Hmx Hmy Hrx Hhx Hry Hhy). }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & Hc & HJ2 & HP & Hres & Hcmp & Hfr2 & Hpres2).
  split; [reflexivity|]. exists regs2, mem2, md2. split; [exact Hc|]. split; [exact HJ2|].
  exists v. split; [exact HP|]. split; [exact Hres|]. split; [exact Hcmp|]. split; [exact Hfr2 | exact Hpres2].
Qed.

End c.

(* ------------------------------------------------------------------ *)
(* 4. The piece                                                        *)
(* ------------------------------------------------------------------ *)

Section m. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

(* A byte of the frame bytes b at buf, read through the walk's view. *)
Lemma fm_aview_b : forall (W2 : world segs) mem2 (buf : Z) (b : list byte) (j : nat),
  garr8 segs (mrestrict (w_H W2) mem2) buf (TW.zs b) -> (j < length b)%nat ->
  aview segs (w_H W2) mem2 (buf + Z.of_nat j) = Some (DSpec.at8 b j).
Proof.
  intros W2 mem2 buf b j HG Hj.
  assert (Hj' : (j < length (TW.zs b))%nat) by (unfold TW.zs; rewrite length_map; lia).
  pose proof (garr8_mbyte segs (mrestrict (w_H W2) mem2) buf (TW.zs b) j HG Hj') as Hm.
  destruct (HG j Hj') as [_ Hr].
  unfold aview. rewrite Hm. cbn [option_map]. f_equal.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
  rewrite Z.mod_small by lia.
  unfold TW.zs, DSpec.at8, DSpec.bz.
  rewrite (nth_indep (map bv_unsigned b) 0 (bv_unsigned (DSpec.b8 0))) by (rewrite length_map; lia).
  rewrite map_nth. reflexivity.
Qed.

(* A byte of g_s's payload, read through the world relation. *)
Lemma fm_aview_w : forall (W2 : world segs) memT (X : list byte) (j : Z), 0 <= j < TW.SZ_g_s ->
  tw_at TMAP_B (aview segs (w_H W2) memT) X ->
  aview segs (w_H W2) memT (ONANN_S + j) = Some (DSpec.at8 X (Z.to_nat (TW.OFF_g_s + j))).
Proof.
  intros W2 memT X j Hj [_ HR].
  pose proof (HR TW.OFF_g_s TB_g_s TW.SZ_g_s j TMAP_B_g_s Hj) as H.
  change ONANN_S with TB_g_s. rewrite H. reflexivity.
Qed.

(* What the walk keeps, carried over one step that changes only bytes of the call's stack window. *)
Lemma fm_keep : forall lyc Sc (W : world segs) memc mdc (W2 : world segs) memX memY (Zs : Z -> Prop)
    (regs : bvmap 5 word) (Bw b : list byte),
  AR_laws segs B -> @AR rc segs B lyc Sc W memc mdc ->
  alloc_ceiling <= spZ regs - ONANN_STK ->
  acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W2 memX (spZ regs - ONANN_STK) (spZ regs) (onann_wr Bw b) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview segs (w_H W2) memY a = aview segs (w_H W2) memX a) ->
  (forall a, apresent (w_H W2) memX a -> apresent (w_H W2) memY a) ->
  (forall a, Zs a -> spZ regs - ONANN_STK <= a < spZ regs) ->
  acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W2 memY (spZ regs - ONANN_STK) (spZ regs) (onann_wr Bw b).
Proof.
  intros lyc Sc W memc mdc W2 memX memY Zs regs Bw b LAWS HAR Hce HK Hkp Hgr HZ.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  apply (dk_kept_step_gw segs B LAWS transportb_segs_low TG.G_HARNESS_B lyc Sc W memc mdc W2 memX memY
    (spZ regs - ONANN_STK) (spZ regs) (onann_wr Bw b) Zs HAR HK Hkp Hgr).
  - intros a Ha _. exact (HZ a Ha).
  - intros b0 m i Hb Hi Hz. exfalso.
    destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b0 m HAR Hb) as (_ & H4096 & Hbc & _).
    pose proof (HZ _ Hz) as Hw. lia.
  - intros a Hz Hi _ _ _. exfalso.
    pose proof (transportb_segs_low a Hi) as Hl. unfold kLowMemEnd in Hl.
    pose proof (HZ a Hz) as Hw. lia.
  - intros cid pos a Hin Hr Hz. exfalso.
    destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (F4096 & Fce & _).
    pose proof (fs_frame_bytes_nonneg cid) as Hfs.
    pose proof (HZ a Hz) as Hw.
    destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng, shadow_addr in Hr; cbn [fst snd] in Hr; [lia|].
    assert (D1 : frame_addr lyc cid pos / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia).
    assert (D2 : fs_frame_bytes cid / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia).
    unfold SHADOW_OFF in Hr. lia.
Qed.

(* The bytes diginet_announce_parse leaves in a's version and name fields: at most ten. *)
Lemma fm_ann_field_len : forall src, (length (map DSpec.bz (TSS.ann_field src)) <= 10)%nat.
Proof.
  intros src. rewrite length_map. unfold TSS.ann_field.
  rewrite length_app, length_firstn. cbn [length].
  unfold DSpec.copy_len. pose proof (DSpec.nz_run_le (firstn (Nat.min 9 (10 - 1)) src)) as Hn.
  rewrite length_firstn in Hn. lia.
Qed.

(* Two memories the walk's view cannot tell apart hold the same byte. *)
Lemma fm_mbyte_of_aview : forall (W3 : world segs) m m' a,
  aview segs (w_H W3) m' a = aview segs (w_H W3) m a ->
  YP09.mbyte segs (mrestrict (w_H W3) m') a = YP09.mbyte segs (mrestrict (w_H W3) m) a.
Proof.
  intros W3 m m' a H. unfold aview in H.
  destruct (YP09.mbyte segs (mrestrict (w_H W3) m') a) as [x|] eqn:E1;
  destruct (YP09.mbyte segs (mrestrict (w_H W3) m) a) as [y|] eqn:E2;
    cbn [option_map] in H; try discriminate.
  - injection H as H. f_equal. apply bv_eq. exact H.
  - reflexivity.
Qed.

Lemma fm_aview_of_val : forall (W3 : world segs) m a (n : nat) v (j : nat), (j < n)%nat ->
  YI04.val_mem segs (mrestrict (w_H W3) m) a n v ->
  aview segs (w_H W3) m (a + Z.of_nat j) = Some (YO0f.le_byte v n j).
Proof.
  intros W3 m a n v j Hj HV. unfold aview. rewrite (HV j Hj). cbn [option_map]. f_equal.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
  unfold YO0f.le_byte. apply Z.mod_mod. lia.
Qed.

Lemma fm_val_mem_ext : forall (W3 : world segs) m m' a (n : nat) v,
  (forall j, (j < n)%nat ->
     aview segs (w_H W3) m' (a + Z.of_nat j) = aview segs (w_H W3) m (a + Z.of_nat j)) ->
  YI04.val_mem segs (mrestrict (w_H W3) m) a n v ->
  YI04.val_mem segs (mrestrict (w_H W3) m') a n v.
Proof.
  intros W3 m m' a n v HK HV j Hj.
  rewrite (fm_mbyte_of_aview W3 m m' _ (HK j Hj)). exact (HV j Hj).
Qed.

Lemma fm_garr8_ext : forall (W3 : world segs) m m' p l,
  (forall j, (j < length l)%nat ->
     aview segs (w_H W3) m' (p + Z.of_nat j) = aview segs (w_H W3) m (p + Z.of_nat j)) ->
  garr8 segs (mrestrict (w_H W3) m) p l -> garr8 segs (mrestrict (w_H W3) m') p l.
Proof.
  intros W3 m m' p l HK HG j Hj. destruct (HG j Hj) as [HV Hr]. split; [|exact Hr].
  intros kk Hk. destruct kk as [|kk]; [|lia].
  rewrite Z.add_0_r. rewrite (fm_mbyte_of_aview W3 m m' _ (HK j Hj)).
  pose proof (HV 0%nat ltac:(lia)) as Hq. rewrite Z.add_0_r in Hq. exact Hq.
Qed.

(* A byte the walk's view shows is a byte. *)
Lemma fm_aview_byte_range : forall (W3 : world segs) memD a v,
  aview segs (w_H W3) memD a = Some v -> 0 <= v < 256.
Proof.
  intros W3 memD a v H. unfold aview in H.
  destruct (YP09.mbyte segs (mrestrict (w_H W3) memD) a) as [bb|] eqn:E; [|discriminate].
  cbn [option_map] in H. injection H as <-.
  pose proof (bv_unsigned_in_range 8 bb) as R. change (bv_modulus 8) with 256 in R. lia.
Qed.

(* ... so an 8-byte word the view shows is a 64-bit value. *)
Lemma fm_rdword_range : forall (W3 : world segs) memD a v,
  rdword (aview segs (w_H W3) memD) a = Some v -> 0 <= v < 2 ^ 64.
Proof.
  intros W3 memD a v H. unfold rdword in H.
  destruct (aview segs (w_H W3) memD a) as [v0|] eqn:E0; [|discriminate].
  destruct (aview segs (w_H W3) memD (a + 1)) as [v1|] eqn:E1; [|discriminate].
  destruct (aview segs (w_H W3) memD (a + 2)) as [v2|] eqn:E2; [|discriminate].
  destruct (aview segs (w_H W3) memD (a + 3)) as [v3|] eqn:E3; [|discriminate].
  destruct (aview segs (w_H W3) memD (a + 4)) as [v4|] eqn:E4; [|discriminate].
  destruct (aview segs (w_H W3) memD (a + 5)) as [v5|] eqn:E5; [|discriminate].
  destruct (aview segs (w_H W3) memD (a + 6)) as [v6|] eqn:E6; [|discriminate].
  destruct (aview segs (w_H W3) memD (a + 7)) as [v7|] eqn:E7; [|discriminate].
  injection H as <-.
  pose proof (fm_aview_byte_range W3 memD _ _ E0).
  pose proof (fm_aview_byte_range W3 memD _ _ E1).
  pose proof (fm_aview_byte_range W3 memD _ _ E2).
  pose proof (fm_aview_byte_range W3 memD _ _ E3).
  pose proof (fm_aview_byte_range W3 memD _ _ E4).
  pose proof (fm_aview_byte_range W3 memD _ _ E5).
  pose proof (fm_aview_byte_range W3 memD _ _ E6).
  pose proof (fm_aview_byte_range W3 memD _ _ E7).
  lia.
Qed.

(* The loop invariant at the head +0x294 of find_mac's loop, at the turn i. *)
Definition fm_inv (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
    (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate)
    (W : world segs) (memc : word -> option byte) (k : Z) (regs : bvmap 5 word)
    (fp buf now pos sp1 F pvv fpv : Z) (Bw b : list byte) (ly2 : alayout) (S2 : astate) (W2 : world segs)
    (i : Z) (regsT : bvmap 5 word) (memT : word -> option byte) (mdT : Model) : Prop :=
  onann_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw b pos F ly2 S2 W2 memT mdT 0 /\
  tw_at TMAP_B (aview segs (w_H W2) memT) (onann_w1 timg_B Bw b) /\
  onann_a_ok W2 memT F buf b /\
  onann_slots_dn W2 memT fp now sp1 F /\
  garr8 segs (mrestrict (w_H W2) memT) buf (TW.zs b) /\
  decode_rd_ok W2 memT buf (Z.of_nat (length b)) /\
  YI04.val_mem segs (mrestrict (w_H W2) memT) sp1 8 SHADOW_OFF /\
  YI04.val_mem segs (mrestrict (w_H W2) memT) (sp1 + 8) 8 F /\
  YI04.val_mem segs (mrestrict (w_H W2) memT) (sp1 + 16) 8 (F + ONANN_A) /\
  YI04.val_mem segs (mrestrict (w_H W2) memT) (sp1 + 32) 8 pvv /\
  YI04.val_mem segs (mrestrict (w_H W2) memT) (sp1 + 40) 8 fpv /\
  0 <= i <= 9 /\
  onann_off (onann_w1 timg_B Bw b) b =
    TSS.find_mac_loop (DSpec.ann_unknown (DSpec.fr_body b))
      (TW.S_cfg_host_mac (onann_w1 timg_B Bw b)) i (Z.to_nat (10 - i)) /\
  YK11.getr regsT 2 = w64 sp1 /\ YK11.getr regsT 3 = w64 (as_gp B) /\
  YK11.getr regsT 4 = w64 (as_tp B) /\ YK11.getr regsT 8 = w64 (spZ regs) /\
  YK11.getr regsT 9 = w64 sp1 /\ YK11.getr regsT 18 = w64 (SHADOW_OFF + F / 8) /\
  YK11.getr regsT 19 = w64 F /\ YK11.getr regsT 20 = w64 ONANN_S /\
  YK11.getr regsT 21 = w64 (buf + 30 + i) /\ YK11.getr regsT 22 = w64 (6 + i) /\
  YK11.getr regsT 23 = w64 1 /\ YK11.getr regsT 24 = w64 (buf + 30) /\
  YK11.getr regsT 25 = w64 i /\ YK11.getr regsT 26 = w64 (buf + 30 + i) /\
  YK11.getr regsT 27 = w64 15.

Lemma fm_holds : @onann_fm_stmt fx rc B MT.
Proof.
unfold onann_fm_stmt, onann_fm_at.
intros DN HLAWS HCALL STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw'
  pos sp1 F ly2 S2 W2 mem2 md2 regs2 HFIX HCUR HREGS.
pose proof HLAWS as (_ & HCELLS & HZS & HGU & HGE & HROU & HRNE & LAWS & MTL & MTF & _ & _ & _ & HGX & HGNE).
pose proof HCALL as (_ & _ & _ & HBCMP & _).
pose proof HFIX as (HJe & Hra & Hra4 & Hgp & Htp & _ & Hfpr & _ & Hsp16 & Hlo & Hhi & Hnow & HDF & Htwc & _ & _ &
  _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsp1e & HFa & HF0 & HF64 & HFc & HFapp).
pose proof HCUR as (HCURc & Htw2 & Hig & Hcmd & HAOK & HSLD).
pose proof HCURc as (HJ & He & Hfrs & Hperm & HlyF & HMO & HK & HSV & HFL).
pose proof HREGS as (((Q2 & Q3 & Q4 & Q8 & Q9 & Q18 & Q19 & Q25) & Q20 & Q24) & Q22 & Q26 & Q16 & Q10).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSTK : ONANN_STK = 9008) by reflexivity.
destruct (onann_cur_ar B MT LAWS HFIX HCURc) as (HARc & HAR2 & ELO & EHI & EFA & EFL & Hin2 & EF2 & HFb & HFsh &
  HFG & HF0' & HF64' & HFc' & HFapp' & Hceil & Hslo & Hshi & H47 & HFLp & HFLo & HFLr & HFLF & HFLS &
  Hsp1b & Hsp1m & Hsp1lo).
assert (Hce : alloc_ceiling <= spZ regs - ONANN_STK) by lia.
assert (HFsp : F + 512 <= sp1) by lia.
assert (Hsp47 : sp1 + 48 <= 2 ^ 47) by lia.
assert (HSP2 : spZ regs2 = sp1) by (unfold spZ; rewrite Q2; unfold w64; apply unsigned_lit_small; lia).
(* the journal's static facts: sp0 is 16-aligned *)
pose proof HJe as (_ & _ & (memSx & HJix & _) & _). rewrite !Z.add_0_r in HJix.
pose proof HJix as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (Hsp016 & _ & _ & _ & _ & _ & _).
clear HJix memSx Hstk0.
(* f, the frame bytes at buf, and a's fields at the cut state, with the bcmp wrapper's window *)
destruct (onann_f30 B MT HLAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF
  Bw Bw' pos sp1 F ly2 S2 W2 mem2 md2 0 regs2 (2 * ESTACK) HFIX HCURc
  ltac:(rewrite HSP2; unfold ESTACK; lia) ltac:(rewrite HSP2; lia)) as
  (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hbuf0 & Hgarr & Hsrcbuf & Hoffbuf & HbufG).
destruct (onann_f30 B MT HLAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF
  Bw Bw' pos sp1 F ly2 S2 W2 mem2 md2 0 regs ONANN_STK HFIX HCURc ltac:(lia) ltac:(lia)) as
  (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hoffbuf2 & _).
unfold decode_off_win in Hoffbuf2.
pose proof (onann_ign_false b Hig) as (_ & HBL).
pose proof (trans_src_ok_rd B LAWS ly2 S2 W2 mem2 md2 buf (Z.of_nat (length b)) HAR2 Hsrcbuf) as HRDbuf.
(* the length of the frame bytes *)
pose proof HDF as (HFC & _).
assert (HLB : 30 + DSpec.fr_body_len b <= Z.of_nat (length b)).
{ unfold DSpec.fr_body_len. pose proof (DSpec.fr_code_ok b HFC) as (_ & _ & _ & NL). lia. }
assert (HLB45 : (45 <= length b)%nat) by lia.
specialize (HRDbuf ltac:(lia)).
pose proof HRDbuf as (Hvisbuf & HRAbuf & HHUbuf & HAMbuf & Hbufge & Hbufle).
(* the six bytes of g_s.cfg.host_mac *)
assert (HSmac : forall (W3 : world segs) (S3 : astate) (ly3 : alayout) mem3 md3,
  @AR rc segs B ly3 S3 W3 mem3 md3 ->
  range_addressable (aview segs (w_H W3) mem3) SHADOW_OFF ONANN_S 6 /\
  shadow_hull_vis (aview segs (w_H W3) mem3) ONANN_S 6).
{ intros W3 S3 ly3 mem3 md3 HAR3.
  apply (decode_zshadow_ra B ly3 S3 W3 mem3 md3 ONANN_S (ONANN_S + TW.SZ_g_s) ONANN_S 6 HAR3 HZS ltac:(lia));
    [ assert (E64 : ONANN_S / 64 * 64 = ONANN_S) by reflexivity; lia
    | assert (E64 : (ONANN_S + 6 - 1) / 64 * 64 = ONANN_S) by reflexivity; unfold TW.SZ_g_s; lia ]. }
assert (HAMmac : amem_range ONANN_S 6)
  by (unfold amem_range, kLowMemEnd, ONANN_S, TB_g_s; left; lia).
assert (HLB45Z : 45 <= Z.of_nat (length b)) by lia.
pose proof (bv_unsigned_in_range 64 (YK11.getr regs2 16)) as Hpvv.
pose proof (bv_unsigned_in_range 64 (YK11.getr regs2 22)) as Hfpv.
change (bv_modulus 64) with (2 ^ 64) in Hpvv, Hfpv.
set (pvv := bv_unsigned (YK11.getr regs2 16)) in Hpvv |- *.
set (fpv := bv_unsigned (YK11.getr regs2 22)) in Hfpv |- *.
assert (Hpveq : Z_to_bv 64 pvv = w64 (onann_pv timg_B b))
  by (unfold pvv; rewrite Z_to_bv_bv_unsigned; exact Q16).
assert (Hfpeq : Z_to_bv 64 fpv = w64 fp)
  by (unfold fpv; rewrite Z_to_bv_bv_unsigned; exact Q22).
pose proof HK as (K1 & K2 & K3 & K4 & K5 & K6).
pose proof HAOK as (_ & _ & HA24 & HA32 & _).
(* the bcmp wrapper's result and the model's memeq *)
assert (HMEQ : forall (memD : word -> option byte) (ii : Z), 0 <= ii <= 9 ->
  tw_at TMAP_B (aview segs (w_H W2) memD) (onann_w1 timg_B Bw b) ->
  garr8 segs (mrestrict (w_H W2) memD) buf (TW.zs b) ->
  ((forall j, 0 <= j < 6 ->
      aview segs (w_H W2) memD (buf + 30 + ii + j) = aview segs (w_H W2) memD (ONANN_S + j)) <->
   TS0.memeq 6 (skipn (Z.to_nat ii) (DSpec.ann_unknown (DSpec.fr_body b)))
     (TW.S_cfg_host_mac (onann_w1 timg_B Bw b)) = true)).
{ intros memD ii Hii Htw3 Hg3.
  assert (HL : forall j, 0 <= j < 6 ->
    aview segs (w_H W2) memD (buf + 30 + ii + j) = Some (DSpec.at8 b (Z.to_nat (30 + ii + j)))).
  { intros j Hj. replace (buf + 30 + ii + j) with (buf + Z.of_nat (Z.to_nat (30 + ii + j))) by lia.
    apply (fm_aview_b W2 memD buf b); [exact Hg3 | lia]. }
  assert (HRw : forall j, 0 <= j < 6 ->
    aview segs (w_H W2) memD (ONANN_S + j) =
      Some (DSpec.at8 (onann_w1 timg_B Bw b) (Z.to_nat (TW.OFF_g_s + j)))).
  { intros j Hj. apply (fm_aview_w W2 memD _ j ltac:(unfold TW.SZ_g_s; lia) Htw3). }
  rewrite fm_memeq_iff. split.
  - intros H j Hj.
    pose proof (H (Z.of_nat j) ltac:(lia)) as Hq.
    rewrite (HL (Z.of_nat j) ltac:(lia)), (HRw (Z.of_nat j) ltac:(lia)) in Hq.
    injection Hq as Hq.
    rewrite fm_at8_skipn, (fm_at8_body b (Z.to_nat ii + j) ltac:(lia) ltac:(lia)), fm_at8_mac by lia.
    replace (30 + (Z.to_nat ii + j))%nat with (Z.to_nat (30 + ii + Z.of_nat j)) by lia.
    replace (Z.to_nat TW.OFF_g_s + j)%nat with (Z.to_nat (TW.OFF_g_s + Z.of_nat j))
      by (unfold TW.OFF_g_s; lia).
    exact Hq.
  - intros H j Hj.
    rewrite (HL j Hj), (HRw j Hj). f_equal.
    pose proof (H (Z.to_nat j) ltac:(lia)) as Hq.
    rewrite fm_at8_skipn, (fm_at8_body b (Z.to_nat ii + Z.to_nat j) ltac:(lia) ltac:(lia)),
      fm_at8_mac in Hq by lia.
    replace (Z.to_nat (30 + ii + j)) with (30 + (Z.to_nat ii + Z.to_nat j))%nat by lia.
    replace (Z.to_nat (TW.OFF_g_s + j)) with (Z.to_nat TW.OFF_g_s + Z.to_nat j)%nat
      by (unfold TW.OFF_g_s; lia).
    exact Hq. }
(* one turn of the loop *)
assert (TURN : forall (i : Z) (regsT : bvmap 5 word) (memT : word -> option byte) (mdT : Model),
  fm_inv STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs fp buf now pos sp1 F pvv fpv Bw b
    ly2 S2 W2 i regsT memT mdT ->
  (forall (regsU : bvmap 5 word) (memU : word -> option byte) (mdU : Model), i <= 8 ->
     fm_inv STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs fp buf now pos sp1 F pvv fpv Bw b
       ly2 S2 W2 (i + 1) regsU memU mdU ->
     SRr segs W2 (mkCfg (@YK11.mkst fx regsU (Z_to_bv 64 (BASE + ONANN_FMLP)) memU (YK11.seg_rom segs)) mdU)
       (@transport_onann_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' b)) ->
  SRr segs W2 (mkCfg (@YK11.mkst fx regsT (Z_to_bv 64 (BASE + ONANN_FMLP)) memT (YK11.seg_rom segs)) mdT)
    (@transport_onann_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' b)).
{ intros i regsT memT mdT HINV HNEXT.
  unfold fm_inv in HINV.
  destruct HINV as (HCURt & Htwt & HAOKt & HSLDt & Hgarrt & HRDt & HV0 & HV8 & HV16 & HV32 & HV40 & Hi & HOFF &
    T2 & T3 & T4 & T8 & T9 & T18 & T19 & T20 & T21 & T22 & T23 & T24 & T25 & T26 & T27).
  pose proof HCURt as (HJt & Het & Hfrst & Hpermt & HlyFt & HMOt & HKt & HSVt & HFLt).
  assert (HSPT : spZ regsT = sp1) by (unfold spZ; rewrite T2; unfold w64; apply unsigned_lit_small; lia).
  pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
    TG.G_HARNESS_B HGX 0 []) as RUN.
  pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
    TG.G_HARNESS_B HGX 0 []) as RUNTO.
  pose proof (paj_branch (PI := PI_transportb)) as BR.
  pose proof (fm_entry_t W2 regsT memT sp1 F buf pvv fpv i T9 T19 T24 T26 HF0 HFsp Hsp47
    ltac:(lia) ltac:(lia) Hi Hbuf0 ltac:(lia) HV0 HV8 HV16 HV32 HV40) as HS.
  assert (HEI : img_env VAL A_LIM (fm_ET regsT pvv fpv)) by (unfold fm_ET; apply Eimg_env).
  assert (SHOK : sh_ok segs (SLit 0) [] (fm_ET regsT pvv fpv) (mrestrict (w_H W2) memT))
    by (unfold sh_ok; constructor).
  (* +0x294 `bltu s10, s8`: unknown + i is at or above unknown, so the trap word is not reached *)
  psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
  { exfalso. cbn [sv_denot branch_taken] in Hc.
    rewrite (fm_ET_reg regsT pvv fpv 26 26%bv eq_refl), T26 in Hc.
    rewrite (fm_ET_reg regsT pvv fpv 24 24%bv eq_refl), T24 in Hc.
    unfold w64 in Hc. rewrite !unsigned_lit_small in Hc by lia. rewrite !Z.add_0_r in Hc.
    rewrite fm_ltu in Hc by lia. apply Z.ltb_lt in Hc. lia. }
  clear Hc.
  (* +0x298 .. +0x2a0: a0 = (unknown <> 0) xor (unknown + i = 0) *)
  paj_run_tok RUN HS HJt SHOK YC4b.Bspan.
  { fm_awr_rs. apply awr_ok_x_cons;
      [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia | apply awr_ok_x_nil]. }
  set (mdA := with_vm_backing (m_vm_lazy mdT) mat mdT) in *. clearbody mdA. clear mat.
  lazymatch type of HS with st_ok_pi _ _ ?EF _ (restrict _ ?mf) => set (EA := EF) in *; rename mf into msA end.
  assert (EAlo : forall n, (n < 1024)%nat -> ew EA n = ew (fm_ET regsT pvv fpv) n)
    by (intros n Hn; unfold EA; rewrite ?ew_ewset_other by lia; reflexivity).
  clearbody EA.
  rename HF into HFu1. rename HFr into HFru1. rename HG into HGu1.
  (* +0x2a0 `beq a0, zero`: a0 = 1, so the trap word is not reached *)
  psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
  { exfalso. cbn [sv_denot branch_taken] in Hc.
    rewrite (EAlo 23%nat ltac:(lia)), (fm_ET_reg regsT pvv fpv 23 23%bv eq_refl), T23 in Hc.
    unfold w64 in Hc. rewrite unsigned_lit_small in Hc by lia. rewrite Z.add_0_r in Hc.
    rewrite zalu64_sound in Hc. vm_compute in Hc. discriminate. }
  clear Hc.
  (* +0x2a4 .. +0x2b4: a0 = unknown + i, a1 = s, a2 = 6, `jal` the bcmp wrapper *)
  paj_run_tok RUN HS HJt SHOK YC4b.Bspan.
  { fm_awr_rs. apply awr_ok_x_cons;
      [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia | apply awr_ok_x_nil]. }
  set (mdB := with_vm_backing (m_vm_lazy mdA) mat mdA) in *. clearbody mdB. clear mat.
  rename HF into HFu2. rename HFr into HFru2. rename HG into HGu2.
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?mf) => rename mf into msB end.
  assert (HEIb : img_env VAL A_LIM EA)
    by (lazymatch goal with HX : img_env _ _ EA |- _ => exact HX end).
  (* the two runs wrote nothing *)
  assert (KFT : forall a, 0 <= a < 2 ^ 64 ->
    aview segs (w_H W2) (ms_mem msB) a = aview segs (w_H W2) memT a).
  { intros a Ha.
    assert (K2a : aview segs (w_H W2) (ms_mem msB) a = aview segs (w_H W2) (ms_mem msA) a).
    { apply (kept_of_frame _ _ _ _ _ (fun _ : Z => False) HFru2); [| exact Ha | intros []].
      intros b0 wlo whi x Hin Hx.
      lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
      cbn [In] in Hin.
      repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; lia |]).
      destruct Hin. }
    assert (K1a : aview segs (w_H W2) (ms_mem msA) a = aview segs (w_H W2) memT a).
    { apply (kept_of_frame _ _ _ _ _ (fun _ : Z => False) HFru1); [| exact Ha | intros []].
      intros b0 wlo whi x Hin Hx.
      lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
      cbn [In] in Hin.
      repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; lia |]).
      destruct Hin. }
    rewrite K2a, K1a. reflexivity. }
  (* the registers the bcmp wrapper reads *)
  fm_reg HS (2%bv : bv 5) (w64 sp1) Rg2
    ltac:(cbn [sv_denot]; rewrite (EAlo 2%nat ltac:(lia)),
      (fm_ET_reg regsT pvv fpv 2 2%bv eq_refl), T2, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  fm_reg HS (3%bv : bv 5) (w64 (as_gp B)) Rg3
    ltac:(cbn [sv_denot]; rewrite (EAlo 3%nat ltac:(lia)),
      (fm_ET_reg regsT pvv fpv 3 3%bv eq_refl), T3, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  fm_reg HS (4%bv : bv 5) (w64 (as_tp B)) Rg4
    ltac:(cbn [sv_denot]; rewrite (EAlo 4%nat ltac:(lia)),
      (fm_ET_reg regsT pvv fpv 4 4%bv eq_refl), T4, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  fm_reg HS (10%bv : bv 5) (w64 (buf + 30 + i)) Rg10
    ltac:(cbn [sv_denot]; rewrite (EAlo 21%nat ltac:(lia)),
      (fm_ET_reg regsT pvv fpv 21 21%bv eq_refl), T21, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  fm_reg HS (11%bv : bv 5) (w64 ONANN_S) Rg11
    ltac:(cbn [sv_denot]; rewrite (EAlo 20%nat ltac:(lia)),
      (fm_ET_reg regsT pvv fpv 20 20%bv eq_refl), T20, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  fm_reg HS (12%bv : bv 5) (w64 6) Rg12 ltac:(reflexivity).
  fm_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + (AF_on_announce + 0x2b4))) Rg1
    ltac:(apply codeptr_val; exact HEIb).
  assert (HSPB : spZ (ms_regs msB) = sp1)
    by (unfold spZ; rewrite Rg2; unfold w64; apply unsigned_lit_small; lia).
  pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJt) as HARB.
  unfold decode_off_win in Hoffbuf. rewrite HSP2 in Hoffbuf.
  pose proof HRDt as (HvisT & HRAT & HHUT & HAMT & HbufgeT & HbufleT).
  (* every fact of the turn's memory survives a step that changes only the wrapper's window *)
  assert (MOVE : forall memY : word -> option byte,
    (forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 - 2 * ESTACK <= a < sp1) ->
       aview segs (w_H W2) memY a = aview segs (w_H W2) memT a) ->
    (forall a, apresent (w_H W2) memT a -> apresent (w_H W2) memY a) ->
    tw_at TMAP_B (aview segs (w_H W2) memY) (onann_w1 timg_B Bw b) /\
    onann_a_ok W2 memY F buf b /\
    onann_slots_dn W2 memY fp now sp1 F /\
    garr8 segs (mrestrict (w_H W2) memY) buf (TW.zs b) /\
    decode_rd_ok W2 memY buf (Z.of_nat (length b)) /\
    YI04.val_mem segs (mrestrict (w_H W2) memY) sp1 8 SHADOW_OFF /\
    YI04.val_mem segs (mrestrict (w_H W2) memY) (sp1 + 8) 8 F /\
    YI04.val_mem segs (mrestrict (w_H W2) memY) (sp1 + 16) 8 (F + ONANN_A) /\
    YI04.val_mem segs (mrestrict (w_H W2) memY) (sp1 + 32) 8 pvv /\
    YI04.val_mem segs (mrestrict (w_H W2) memY) (sp1 + 40) 8 fpv /\
    acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W2 memY
      (spZ regs - ONANN_STK) (spZ regs) (onann_wr Bw b) /\
    Forall (fun o : Z * Z => rdword (aview segs (w_H W2) memY) (spZ regs - fst o) =
      Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) ONANN_SAVED /\
    rdword (aview segs (w_H W2) memY) (F + ONANN_FBYTES - 8) = Some (flag_addr lyc ONANN_CID pos)).
  { intros memY HKY HPY.
    assert (HSH : forall x, 0 <= x -> x <= 2 ^ 47 -> 0 <= SHADOW_OFF + x / 8 <= 2 ^ 45).
    { intros x Hx0 Hx1. assert (Hd : x / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia).
      assert (Hd0 : 0 <= x / 8) by (apply Z.div_pos; lia).
      unfold SHADOW_OFF. lia. }
    assert (HBUF47 : buf + Z.of_nat (length b) <= 2 ^ 47).
    { destruct HAMT as [Hm | Hm];
        unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hm; lia. }
    pose proof HAOKt as (Ga1 & Ga2 & Ra1 & Ra2 & Sh1).
    pose proof HSLDt as (SL48 & SL56 & SL24 & SL16).
    pose proof HCURt as (_ & _ & _ & _ & _ & _ & HKt' & HSVt' & HFLt').
    assert (TW' : tw_at TMAP_B (aview segs (w_H W2) memY) (onann_w1 timg_B Bw b)).
    { apply (tw_kept_rows TMAP_B _ _ _ Htwt). intros o bb n ii Hin Hii.
      pose proof (tw_row TMAP_B o bb n TMAP_B_ok Hin) as (_ & _ & _ & Hb0 & Hbn).
      pose proof (TMAP_B_hull (bb + ii)
        ltac:(exists o; exists bb; exists n; split; [exact Hin | lia])) as Hh.
      unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh.
      apply HKY; [lia | unfold ESTACK; lia]. }
    assert (AOK' : onann_a_ok W2 memY F buf b).
    { split; [|split; [|split; [|split]]].
      - apply (fm_garr8_ext W2 memT memY); [|exact Ga1].
        intros j Hj. pose proof (fm_ann_field_len (skipn 15 (DSpec.fr_body b))) as Hl.
        apply HKY; [unfold ONANN_A; lia | unfold ONANN_A, ESTACK; lia].
      - apply (fm_garr8_ext W2 memT memY); [|exact Ga2].
        intros j Hj. pose proof (fm_ann_field_len (skipn 24 (DSpec.fr_body b))) as Hl.
        apply HKY; [unfold ONANN_A; lia | unfold ONANN_A, ESTACK; lia].
      - rewrite <- Ra1. apply YCbq.rdword_ext. intros kk Hk.
        apply HKY; [unfold ONANN_A; lia | unfold ONANN_A, ESTACK; lia].
      - rewrite <- Ra2. apply YCbq.rdword_ext. intros kk Hk.
        apply HKY; [unfold ONANN_A; lia | unfold ONANN_A, ESTACK; lia].
      - intros ii Hii. rewrite (HKY (SHADOW_OFF + F / 8 + ii)).
        + exact (Sh1 ii Hii).
        + destruct (HSH F ltac:(lia) ltac:(lia)) as [Hs0 Hs1]. unfold ESTACK in *. lia.
        + destruct (HSH F ltac:(lia) ltac:(lia)) as [Hs0 Hs1]. unfold ESTACK in *. lia. }
    assert (SLD' : onann_slots_dn W2 memY fp now sp1 F).
    { split; [|split; [|split]]; unfold onann_slot.
      - rewrite <- SL48. apply YCbq.rdword_ext. intros kk Hk. apply HKY; [lia | unfold ESTACK; lia].
      - rewrite <- SL56. apply YCbq.rdword_ext. intros kk Hk. apply HKY; [lia | unfold ESTACK; lia].
      - rewrite <- SL24. apply YCbq.rdword_ext. intros kk Hk. apply HKY; [lia | unfold ESTACK; lia].
      - rewrite <- SL16. apply YCbq.rdword_ext. intros kk Hk. apply HKY; [lia | unfold ESTACK; lia]. }
    assert (GB' : garr8 segs (mrestrict (w_H W2) memY) buf (TW.zs b)).
    { apply (fm_garr8_ext W2 memT memY); [|exact Hgarrt].
      intros j Hj. unfold TW.zs in Hj. rewrite length_map in Hj.
      apply HKY; [lia|]. destruct Hoffbuf as [Ho | Ho]; unfold ESTACK in *; lia. }
    assert (RD' : decode_rd_ok W2 memY buf (Z.of_nat (length b))).
    { apply (trans_rd_ok_view W2 W2 memT memY buf (Z.of_nat (length b)) HRDt).
      - intros a Ha. apply HKY; [lia|]. destruct Hoffbuf as [Ho | Ho]; unfold ESTACK in *; lia.
      - intros s Hs. apply HKY;
          [unfold kLowMemEnd, kHighShadowEnd in Hs; lia
          | unfold kLowMemEnd, kHighShadowEnd in Hs; unfold ESTACK; lia]. }
    assert (VM : forall a v, sp1 <= a -> a + 8 <= sp1 + 48 ->
      YI04.val_mem segs (mrestrict (w_H W2) memT) a 8 v ->
      YI04.val_mem segs (mrestrict (w_H W2) memY) a 8 v).
    { intros a v Ho1 Ho2 HV. apply (fm_val_mem_ext W2 memT memY); [|exact HV].
      intros j Hj. apply HKY; [lia | unfold ESTACK; lia]. }
    assert (KG' : acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W2 memY
      (spZ regs - ONANN_STK) (spZ regs) (onann_wr Bw b)).
    { apply (fm_keep lyc Sc W memc mdc W2 memT memY
        (fun a => sp1 - 2 * ESTACK <= a < sp1) regs Bw b LAWS HARc Hce HKt').
      - intros a Ha Hn. apply HKY; [exact Ha | exact Hn].
      - exact HPY.
      - intros a Ha. unfold ESTACK in *. lia. }
    assert (SV' : Forall (fun o : Z * Z => rdword (aview segs (w_H W2) memY) (spZ regs - fst o) =
      Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) ONANN_SAVED).
    { apply Forall_forall. intros o Hin. cbv beta.
      pose proof (proj1 (Forall_forall _ _) HSVt' o Hin) as Hv. cbv beta in Hv.
      assert (Ho : 8 <= fst o <= 104).
      { unfold ONANN_SAVED in Hin. cbn [In] in Hin.
        repeat (destruct Hin as [Hin | Hin]; [subst o; cbn [fst]; lia |]). destruct Hin. }
      rewrite <- Hv. apply YCbq.rdword_ext. intros kk Hk. apply HKY; [lia | unfold ESTACK; lia]. }
    assert (FL' : rdword (aview segs (w_H W2) memY) (F + ONANN_FBYTES - 8) =
      Some (flag_addr lyc ONANN_CID pos)).
    { rewrite <- HFLt'. apply YCbq.rdword_ext. intros kk Hk.
      apply HKY; [unfold ONANN_FBYTES; lia | unfold ONANN_FBYTES, ESTACK; lia]. }
    split; [exact TW'|]. split; [exact AOK'|]. split; [exact SLD'|]. split; [exact GB'|].
    split; [exact RD'|].
    split; [exact (VM sp1 SHADOW_OFF ltac:(lia) ltac:(lia) HV0)|].
    split; [exact (VM (sp1 + 8) F ltac:(lia) ltac:(lia) HV8)|].
    split; [exact (VM (sp1 + 16) (F + ONANN_A) ltac:(lia) ltac:(lia) HV16)|].
    split; [exact (VM (sp1 + 32) pvv ltac:(lia) ltac:(lia) HV32)|].
    split; [exact (VM (sp1 + 40) fpv ltac:(lia) ltac:(lia) HV40)|].
    split; [exact KG'|]. split; [exact SV' | exact FL']. }
  (* the bytes the wrapper reads: [unknown + i, + 6) of the frame bytes, [s, s + 6) of g_s *)
  assert (HVX : forall a, buf + 30 + i <= a < buf + 30 + i + 6 ->
    aview segs (w_H W2) (ms_mem msB) a <> None).
  { intros a Ha. rewrite (KFT a ltac:(lia)).
    replace a with (buf + Z.of_nat (Z.to_nat (a - buf))) by lia.
    rewrite (fm_aview_b W2 memT buf b (Z.to_nat (a - buf)) Hgarrt ltac:(lia)). discriminate. }
  assert (HVY : forall a, ONANN_S <= a < ONANN_S + 6 -> aview segs (w_H W2) (ms_mem msB) a <> None).
  { intros a Ha. rewrite (KFT a ltac:(unfold ONANN_S, TB_g_s in *; lia)).
    replace a with (ONANN_S + (a - ONANN_S)) by lia.
    rewrite (fm_aview_w W2 memT (onann_w1 timg_B Bw b) (a - ONANN_S)
      ltac:(unfold TW.SZ_g_s; lia) Htwt). discriminate. }
  pmkst HS.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (mkCfg (@YK11.mkst fx rg
      (Z_to_bv 64 (transportb_sigma TB___interceptor_trampoline_bcmp)) mm rom) mdx) Q) end.
  eapply SRr_bind.
  { apply (fm_bcmp B LAWS STK sp0 FP ly S W0 mem0 md0 ((ONANN_CID, pos) :: own) ly2 S2 W2
      (ms_mem msB) mdB (k + 0) (ms_regs msB) (buf + 30 + i) ONANN_S 6 (sp1 - sp0)
      (Z_to_bv 64 (BASE + (AF_on_announce + 0x2b4)))).
    - exact (HBCMP fx).
    - exact HJt.
    - exact Rg10.
    - exact Rg11.
    - exact Rg12.
    - lia.
    - lia.
    - lia.
    - unfold ONANN_S, TB_g_s. lia.
    - unfold ONANN_S, TB_g_s. lia.
    - rewrite HSPB. lia.
    - pose proof (Z.div_mod sp1 32 ltac:(lia)) as D32.
      pose proof (Z.div_mod sp0 16 ltac:(lia)) as D16.
      rewrite Hsp1m in D32. rewrite Hsp016 in D16.
      replace (sp1 - sp0) with ((2 * (sp1 / 32) - sp0 / 16) * 16) by lia.
      apply Z_mod_mult.
    - lia.
    - unfold ESTACK. lia.
    - exact Rg3.
    - exact Rg4.
    - exact Rg1.
    - apply (ret_ok_codeptr_v (PI := PI_transportb));
        [unfold AF_on_announce; lia | unfold AF_on_announce; reflexivity].
    - intros a Ha. split; [exact (HVX a Ha)|]. rewrite HSPB. unfold ESTACK.
      destruct Hoffbuf as [Ho | Ho]; unfold ESTACK in Ho; lia.
    - intros a Ha. split; [exact (HVY a Ha)|]. rewrite HSPB.
      unfold ESTACK, ONANN_S, TB_g_s in *. lia.
    - intros a Ha. destruct Hoffbuf as [Ho | Ho]; unfold ESTACK in Ho |- *; lia.
    - intros a Ha. unfold ESTACK, ONANN_S, TB_g_s in *. lia.
    - destruct HAMT as [Hm | Hm]; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *;
        [left; lia | right; lia].
    - exact HAMmac.
    - intros xx Hxx. destruct (HRAT xx ltac:(lia)) as (s & Hs & Hok). exists s. split; [|exact Hok].
      rewrite (KFT _ (fm_sh_range xx ltac:(lia))). exact Hs.
    - intros _ s Hs. rewrite (KFT s (fm_hull_range (buf + 30 + i) 6 s
        ltac:(lia) ltac:(lia) ltac:(lia) Hs)).
      apply (trans_hull_sub (aview segs (w_H W2) memT) buf (Z.of_nat (length b)) (buf + 30 + i) 6
        HHUT ltac:(lia) ltac:(lia)). exact Hs.
    - destruct (HSmac W2 S2 ly2 (ms_mem msB) mdB HARB) as [HRa _]. exact HRa.
    - intros _. destruct (HSmac W2 S2 ly2 (ms_mem msB) mdB HARB) as [_ HHu]. exact HHu. }
  cbv beta.
  intros Wx cx _ (-> & regs3 & mem3 & md3 & -> & HJ3 & (vres & HPres & Hv10 & Hiff & Hkept & Hgrow)).
  assert (U9b : bv_unsigned (ew EA 9) = sp1)
    by (rewrite (EAlo 9%nat ltac:(lia)), (fm_ET_reg regsT pvv fpv 9 9%bv eq_refl), T9;
        unfold w64; apply unsigned_lit_small; lia).
  (* the symbolic state at the return: the spill slots kept *)
  jafter_call_keep_pi HS 40%nat regs3 (mrestrict (w_H W2) mem3) HPres [0%nat] HS2.
  match type of HS2 with ?tq -> _ => assert (HRK : tq) end.
  { cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
    apply (region_kept_aview _ _ _ _ 9%nat sp1); [exact U9b | | exact Hgrow].
    intros a Ha. apply Hkept; lia. }
  specialize (HS2 HRK). clear HRK HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
  set (EC := havoc EA 40 (map (YK11.getr regs3) CLOB)) in HS.
  assert (HEIc : img_env VAL A_LIM EC)
    by (unfold EC; apply img_env_havoc; [exact HEIb | rewrite length_map; vm_compute; lia]).
  assert (EClo : forall j, (j < 40)%nat -> ew EC j = ew EA j)
    by (intros j Hj; unfold EC; apply ew_havoc_old; exact Hj).
  clearbody EC.
  assert (SHOKc : sh_ok segs (SLit 0) [] EC (mrestrict (w_H W2) mem3)) by (unfold sh_ok; constructor).
  clear HEI HEIb SHOK.
  fm_reg HS (10%bv : bv 5) (sv_denot EC (SOff 44 0)) Dv10 ltac:(reflexivity).
  cbn [ms_regs mkst restrict] in Dv10.
  assert (PB : forall a, apresent (w_H W2) memT a -> apresent (w_H W2) (ms_mem msB) a).
  { intros a Ha. apply (apresent_grows _ _ _ a HGu2). apply (apresent_grows _ _ _ a HGu1). exact Ha. }
  assert (KC : forall memZ : word -> option byte,
    (forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W2) memZ a = aview segs (w_H W2) mem3 a) ->
    forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 - 2 * ESTACK <= a < sp1) ->
      aview segs (w_H W2) memZ a = aview segs (w_H W2) memT a).
  { intros memZ HZ a Ha Hn. rewrite (HZ a Ha), (Hkept a Ha ltac:(lia)). exact (KFT a Ha). }
  assert (PC : forall memZ : word -> option byte,
    (forall a, apresent (w_H W2) mem3 a -> apresent (w_H W2) memZ a) ->
    forall a, apresent (w_H W2) memT a -> apresent (w_H W2) memZ a).
  { intros memZ HZ a Ha. apply HZ. apply Hgrow. exact (PB a Ha). }
  (* the model's loop test at this turn *)
  assert (HMQ : TS0.memeq 6 (skipn (Z.to_nat i) (DSpec.ann_unknown (DSpec.fr_body b)))
      (TW.S_cfg_host_mac (onann_w1 timg_B Bw b)) = true <-> vres = w64 0).
  { rewrite <- (HMEQ memT i Hi Htwt Hgarrt). split.
    - intros Hag. apply Hiff. intros j Hj.
      rewrite (KFT (buf + 30 + i + j) ltac:(lia)),
        (KFT (ONANN_S + j) ltac:(unfold ONANN_S, TB_g_s; lia)). exact (Hag j Hj).
    - intros Hz j Hj.
      rewrite <- (KFT (buf + 30 + i + j) ltac:(lia)),
        <- (KFT (ONANN_S + j) ltac:(unfold ONANN_S, TB_g_s; lia)).
      exact (proj1 Hiff Hz j Hj). }
  (* +0x2b4 `beq a0, zero`: the six bytes agree exactly when the wrapper answered 0 *)
  psrr_branch_tok RUN BR HS SHOKc YC4b.Bspan.
  { (* the six bytes agree: the model's find_mac answers i *)
    assert (Hv0 : vres = w64 0).
    { rewrite <- Dv10, Hv10 in Hc. cbn [branch_taken sv_denot] in Hc.
      unfold bv_eqb in Hc. apply Z.eqb_eq in Hc.
      apply bv_eq. unfold w64. exact Hc. }
    assert (Hmq : TS0.memeq 6 (skipn (Z.to_nat i) (DSpec.ann_unknown (DSpec.fr_body b)))
      (TW.S_cfg_host_mac (onann_w1 timg_B Bw b)) = true) by (apply HMQ; exact Hv0).
    replace (Z.to_nat (10 - i)) with (Datatypes.S (Z.to_nat (10 - i - 1))) in HOFF by lia.
    rewrite fm_find_mac_S, Hmq in HOFF.
    (* +0x2e4 .. +0x2fc: a5 = i, the reloads, a1 = 1 *)
    paj_run_to_tok RUNTO HS HJ3 SHOKc YC4b.Bspan ONANN_DN.
    { fm_awr_rs. apply awr_ok_x_cons;
        [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia | apply awr_ok_x_nil]. }
    set (mdE := with_vm_backing (m_vm_lazy md3) mat md3) in *. clearbody mdE. clear mat.
    rename HF into HFe. rename HFr into HFre. rename HG into HGe.
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mf) => rename mf into msE end.
    assert (KE : forall a, 0 <= a < 2 ^ 64 ->
      aview segs (w_H W2) (ms_mem msE) a = aview segs (w_H W2) mem3 a).
    { intros a Ha. apply (kept_of_frame _ _ _ _ _ (fun _ : Z => False) HFre); [| exact Ha | intros []].
      intros b0 wlo whi x Hin Hx.
      lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
      cbn [In] in Hin.
      repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; lia |]).
      destruct Hin. }
    assert (PE : forall a, apresent (w_H W2) mem3 a -> apresent (w_H W2) (ms_mem msE) a)
      by (intros a Ha; exact (apresent_grows _ _ _ a HGe Ha)).
    destruct (MOVE (ms_mem msE) (KC _ KE) (PC _ PE)) as
      (TWe & AOKe & SLDe & GBe & RDe & VMe0 & VMe8 & VMe16 & VMe32 & VMe40 & KGe & SVe & FLe).
    fm_reg HS (2%bv : bv 5) (w64 sp1) R2e
      ltac:(cbn [sv_denot]; rewrite (EClo 2%nat ltac:(lia)),
        (EAlo 2%nat ltac:(lia)), (fm_ET_reg regsT pvv fpv 2 2%bv eq_refl), T2, Z.add_0_r,
        Z_to_bv_bv_unsigned; reflexivity).
    fm_reg HS (3%bv : bv 5) (w64 (as_gp B)) R3e
      ltac:(cbn [sv_denot]; rewrite (EClo 3%nat ltac:(lia)),
        (EAlo 3%nat ltac:(lia)), (fm_ET_reg regsT pvv fpv 3 3%bv eq_refl), T3, Z.add_0_r,
        Z_to_bv_bv_unsigned; reflexivity).
    fm_reg HS (4%bv : bv 5) (w64 (as_tp B)) R4e
      ltac:(cbn [sv_denot]; rewrite (EClo 4%nat ltac:(lia)),
        (EAlo 4%nat ltac:(lia)), (fm_ET_reg regsT pvv fpv 4 4%bv eq_refl), T4, Z.add_0_r,
        Z_to_bv_bv_unsigned; reflexivity).
    fm_reg HS (8%bv : bv 5) (w64 (spZ regs)) R8e
      ltac:(cbn [sv_denot]; rewrite (EClo 8%nat ltac:(lia)),
        (EAlo 8%nat ltac:(lia)), (fm_ET_reg regsT pvv fpv 8 8%bv eq_refl), T8, Z.add_0_r,
        Z_to_bv_bv_unsigned; reflexivity).
    fm_reg HS (9%bv : bv 5) (w64 sp1) R9e
      ltac:(cbn [sv_denot]; rewrite (EClo 9%nat ltac:(lia)),
        (EAlo 9%nat ltac:(lia)), (fm_ET_reg regsT pvv fpv 9 9%bv eq_refl), T9, Z.add_0_r,
        Z_to_bv_bv_unsigned; reflexivity).
    fm_reg HS (18%bv : bv 5) (w64 (SHADOW_OFF + F / 8)) R18e
      ltac:(cbn [sv_denot]; rewrite (EClo 18%nat ltac:(lia)),
        (EAlo 18%nat ltac:(lia)), (fm_ET_reg regsT pvv fpv 18 18%bv eq_refl), T18, Z.add_0_r,
        Z_to_bv_bv_unsigned; reflexivity).
    fm_reg HS (19%bv : bv 5) (w64 F) R19e
      ltac:(cbn [sv_denot]; rewrite (EClo 19%nat ltac:(lia)),
        (EAlo 19%nat ltac:(lia)), (fm_ET_reg regsT pvv fpv 19 19%bv eq_refl), T19, Z.add_0_r,
        Z_to_bv_bv_unsigned; reflexivity).
    fm_reg HS (20%bv : bv 5) (w64 ONANN_S) R20e
      ltac:(cbn [sv_denot]; rewrite (EClo 20%nat ltac:(lia)),
        (EAlo 20%nat ltac:(lia)), (fm_ET_reg regsT pvv fpv 20 20%bv eq_refl), T20, Z.add_0_r,
        Z_to_bv_bv_unsigned; reflexivity).
    fm_reg HS (24%bv : bv 5) (w64 SHADOW_OFF) R24e ltac:(reflexivity).
    fm_reg HS (25%bv : bv 5) (w64 F) R25e
      ltac:(cbn [sv_denot]; rewrite (EClo 19%nat ltac:(lia)),
        (EAlo 19%nat ltac:(lia)), (fm_ET_reg regsT pvv fpv 19 19%bv eq_refl), T19, Z.add_0_r,
        Z_to_bv_bv_unsigned; reflexivity).
    fm_reg HS (26%bv : bv 5) (w64 (F + ONANN_A)) R26e
      ltac:(cbn [sv_denot]; rewrite (EClo 19%nat ltac:(lia)),
        (EAlo 19%nat ltac:(lia)), (fm_ET_reg regsT pvv fpv 19 19%bv eq_refl), T19;
        unfold w64, ONANN_A; rewrite unsigned_lit_small by lia; reflexivity).
    fm_reg HS (22%bv : bv 5) (w64 fp) R22e
      ltac:(cbn [sv_denot]; rewrite (EClo 33%nat ltac:(lia)),
        (EAlo 33%nat ltac:(lia)), (fm_ET_x1 regsT pvv fpv); unfold w64;
        rewrite unsigned_lit_small by lia; rewrite Z.add_0_r; exact Hfpeq).
    fm_reg HS (16%bv : bv 5) (w64 (onann_pv timg_B b)) R16e
      ltac:(cbn [sv_denot]; rewrite (EClo 32%nat ltac:(lia)),
        (EAlo 32%nat ltac:(lia)), (fm_ET_x0 regsT pvv fpv); unfold w64;
        rewrite unsigned_lit_small by lia; rewrite Z.add_0_r; exact Hpveq).
    fm_reg HS (15%bv : bv 5) (w64 (onann_off (onann_w1 timg_B Bw b) b)) R15e
      ltac:(cbn [sv_denot]; rewrite (EClo 25%nat ltac:(lia)),
        (EAlo 25%nat ltac:(lia)), (fm_ET_reg regsT pvv fpv 25 25%bv eq_refl), T25, Z.add_0_r,
        Z_to_bv_bv_unsigned, HOFF; reflexivity).
    fm_reg HS (11%bv : bv 5) (w64 1) R11e ltac:(reflexivity).
    pmkst HS.
    lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
      change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + ONANN_DN)) mm rom) mdx) Q) end.
    apply (DN HLAWS HCALL STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF
      Bw Bw' pos sp1 F ly2 S2 W2 (ms_mem msE) mdE (ms_regs msE) HFIX).
    - unfold onann_dn_cur.
      split; [|split; [exact TWe | split; [exact Hig | split; [exact AOKe | exact SLDe]]]].
      unfold onann_cur.
      refine (conj HJ3 (conj Het (conj Hfrst (conj Hpermt (conj HlyFt
        (conj HMOt (conj KGe (conj SVe FLe)))))))).
    - unfold onann_regs_dn, onann_regs_ign, onann_regs_rel.
      refine (conj (conj (conj R2e (conj (eq_trans R3e (eq_sym Hgp)) (conj (eq_trans R4e (eq_sym Htp))
        (conj R8e (conj R9e (conj R18e (conj R19e R25e))))))) (conj R20e R24e))
        (conj R22e (conj R26e (conj R16e (conj R15e R11e))))). }
  rename Hc into Hne0.
  (* +0x2b8 .. +0x2c8: i + 1, and `bgeu s11, s6` *)
  paj_run_tok RUN HS HJ3 SHOKc YC4b.Bspan.
  { fm_awr_rs. apply awr_ok_x_cons;
      [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia | apply awr_ok_x_nil]. }
  set (mdD := with_vm_backing (m_vm_lazy md3) mat md3) in *. clearbody mdD. clear mat.
  rename HF into HFu3. rename HFr into HFru3. rename HG into HGu3.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mf) => rename mf into msD end.
  (* the six bytes differ, so the model's loop goes on *)
  assert (Hvne : vres <> w64 0).
  { rewrite <- Dv10, Hv10 in Hne0. cbn [branch_taken sv_denot] in Hne0.
    unfold bv_eqb in Hne0. intros Heq. rewrite Heq in Hne0. unfold w64 in Hne0.
    rewrite Z.eqb_refl in Hne0. discriminate. }
  assert (Hmqf : TS0.memeq 6 (skipn (Z.to_nat i) (DSpec.ann_unknown (DSpec.fr_body b)))
    (TW.S_cfg_host_mac (onann_w1 timg_B Bw b)) = false).
  { destruct (TS0.memeq 6 (skipn (Z.to_nat i) (DSpec.ann_unknown (DSpec.fr_body b)))
      (TW.S_cfg_host_mac (onann_w1 timg_B Bw b))) eqn:Em; [|reflexivity].
    exfalso. apply Hvne. apply HMQ. reflexivity. }
  assert (E22c : ew EC 22 = w64 (6 + i))
    by (rewrite (EClo 22%nat ltac:(lia)), (EAlo 22%nat ltac:(lia)),
        (fm_ET_reg regsT pvv fpv 22 22%bv eq_refl); exact T22).
  assert (E27c : ew EC 27 = w64 15)
    by (rewrite (EClo 27%nat ltac:(lia)), (EAlo 27%nat ltac:(lia)),
        (fm_ET_reg regsT pvv fpv 27 27%bv eq_refl); exact T27).
  assert (E25c : ew EC 25 = Z_to_bv 64 i)
    by (rewrite (EClo 25%nat ltac:(lia)), (EAlo 25%nat ltac:(lia)),
        (fm_ET_reg regsT pvv fpv 25 25%bv eq_refl); exact T25).
  assert (E21c : ew EC 21 = w64 (buf + 30 + i))
    by (rewrite (EClo 21%nat ltac:(lia)), (EAlo 21%nat ltac:(lia)),
        (fm_ET_reg regsT pvv fpv 21 21%bv eq_refl); exact T21).
  assert (E26c : ew EC 26 = w64 (buf + 30 + i))
    by (rewrite (EClo 26%nat ltac:(lia)), (EAlo 26%nat ltac:(lia)),
        (fm_ET_reg regsT pvv fpv 26 26%bv eq_refl); exact T26).
  assert (KD : forall a, 0 <= a < 2 ^ 64 ->
    aview segs (w_H W2) (ms_mem msD) a = aview segs (w_H W2) mem3 a).
  { intros a Ha. apply (kept_of_frame _ _ _ _ _ (fun _ : Z => False) HFru3); [| exact Ha | intros []].
    intros b0 wlo whi x Hin Hx.
    lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
    cbn [In] in Hin.
    repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; lia |]).
    destruct Hin. }
  assert (PD : forall a, apresent (w_H W2) mem3 a -> apresent (w_H W2) (ms_mem msD) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HGu3 Ha)).
  psrr_branch_tok RUN BR HS SHOKc YC4b.Bspan.
  { (* 15 >= 6 + i + 1: the turn runs again at i + 1 *)
    assert (Hile : i <= 8).
    { cbn [branch_taken sv_denot] in Hc. rewrite E22c, E27c in Hc.
      unfold w64 in Hc. rewrite !unsigned_lit_small in Hc by lia.
      rewrite fm_ltu in Hc by lia. apply Bool.negb_true_iff, Z.ltb_ge in Hc. lia. }
    replace (Z.to_nat (10 - i)) with (Datatypes.S (Z.to_nat (10 - (i + 1)))) in HOFF by lia.
    rewrite fm_find_mac_S, Hmqf in HOFF.
    paj_run_to_tok RUNTO HS HJ3 SHOKc YC4b.Bspan ONANN_FMLP.
    { fm_awr_rs. apply awr_ok_x_cons;
        [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia | apply awr_ok_x_nil]. }
    set (mdF := with_vm_backing (m_vm_lazy mdD) mat mdD) in *. clearbody mdF. clear mat.
    rename HF into HFf. rename HFr into HFrf. rename HG into HGf.
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mf) => rename mf into msF end.
    assert (KF2 : forall a, 0 <= a < 2 ^ 64 ->
      aview segs (w_H W2) (ms_mem msF) a = aview segs (w_H W2) mem3 a).
    { intros a Ha. rewrite <- (KD a Ha).
      apply (kept_of_frame _ _ _ _ _ (fun _ : Z => False) HFrf); [| exact Ha | intros []].
      intros b0 wlo whi x Hin Hx.
      lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
      cbn [In] in Hin.
      repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; lia |]).
      destruct Hin. }
    assert (PF2 : forall a, apresent (w_H W2) mem3 a -> apresent (w_H W2) (ms_mem msF) a)
      by (intros a Ha; exact (apresent_grows _ _ _ a HGf (PD a Ha))).
    destruct (MOVE (ms_mem msF) (KC _ KF2) (PC _ PF2)) as
      (TWf & AOKf & SLDf & GBf & RDf & VMf0 & VMf8 & VMf16 & VMf32 & VMf40 & KGf & SVf & FLf).
    fm_reg HS (2%bv : bv 5) (w64 sp1) R2f
      ltac:(cbn [sv_denot]; rewrite (EClo 2%nat ltac:(lia)), (EAlo 2%nat ltac:(lia)),
        (fm_ET_reg regsT pvv fpv 2 2%bv eq_refl), T2, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    fm_reg HS (3%bv : bv 5) (w64 (as_gp B)) R3f
      ltac:(cbn [sv_denot]; rewrite (EClo 3%nat ltac:(lia)), (EAlo 3%nat ltac:(lia)),
        (fm_ET_reg regsT pvv fpv 3 3%bv eq_refl), T3, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    fm_reg HS (4%bv : bv 5) (w64 (as_tp B)) R4f
      ltac:(cbn [sv_denot]; rewrite (EClo 4%nat ltac:(lia)), (EAlo 4%nat ltac:(lia)),
        (fm_ET_reg regsT pvv fpv 4 4%bv eq_refl), T4, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    fm_reg HS (8%bv : bv 5) (w64 (spZ regs)) R8f
      ltac:(cbn [sv_denot]; rewrite (EClo 8%nat ltac:(lia)), (EAlo 8%nat ltac:(lia)),
        (fm_ET_reg regsT pvv fpv 8 8%bv eq_refl), T8, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    fm_reg HS (9%bv : bv 5) (w64 sp1) R9f
      ltac:(cbn [sv_denot]; rewrite (EClo 9%nat ltac:(lia)), (EAlo 9%nat ltac:(lia)),
        (fm_ET_reg regsT pvv fpv 9 9%bv eq_refl), T9, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    fm_reg HS (18%bv : bv 5) (w64 (SHADOW_OFF + F / 8)) R18f
      ltac:(cbn [sv_denot]; rewrite (EClo 18%nat ltac:(lia)), (EAlo 18%nat ltac:(lia)),
        (fm_ET_reg regsT pvv fpv 18 18%bv eq_refl), T18, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    fm_reg HS (19%bv : bv 5) (w64 F) R19f
      ltac:(cbn [sv_denot]; rewrite (EClo 19%nat ltac:(lia)), (EAlo 19%nat ltac:(lia)),
        (fm_ET_reg regsT pvv fpv 19 19%bv eq_refl), T19, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    fm_reg HS (20%bv : bv 5) (w64 ONANN_S) R20f
      ltac:(cbn [sv_denot]; rewrite (EClo 20%nat ltac:(lia)), (EAlo 20%nat ltac:(lia)),
        (fm_ET_reg regsT pvv fpv 20 20%bv eq_refl), T20, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    fm_reg HS (21%bv : bv 5) (w64 (buf + 30 + (i + 1))) R21f
      ltac:(cbn [sv_denot]; rewrite E21c; unfold w64;
        rewrite unsigned_lit_small by lia; f_equal; lia).
    fm_reg HS (22%bv : bv 5) (w64 (6 + (i + 1))) R22f
      ltac:(cbn [sv_denot]; rewrite E22c; unfold w64;
        rewrite unsigned_lit_small by lia; f_equal; lia).
    fm_reg HS (23%bv : bv 5) (w64 1) R23f
      ltac:(cbn [sv_denot]; rewrite (EClo 23%nat ltac:(lia)), (EAlo 23%nat ltac:(lia)),
        (fm_ET_reg regsT pvv fpv 23 23%bv eq_refl), T23, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    fm_reg HS (24%bv : bv 5) (w64 (buf + 30)) R24f
      ltac:(cbn [sv_denot]; rewrite (EClo 24%nat ltac:(lia)), (EAlo 24%nat ltac:(lia)),
        (fm_ET_reg regsT pvv fpv 24 24%bv eq_refl), T24, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    fm_reg HS (25%bv : bv 5) (w64 (i + 1)) R25f
      ltac:(unfold w64; exact (fm_addiw EC 25 i E25c ltac:(lia))).
    fm_reg HS (26%bv : bv 5) (w64 (buf + 30 + (i + 1))) R26f
      ltac:(cbn [sv_denot]; rewrite E26c; unfold w64;
        rewrite unsigned_lit_small by lia; f_equal; lia).
    fm_reg HS (27%bv : bv 5) (w64 15) R27f
      ltac:(cbn [sv_denot]; rewrite E27c; unfold w64;
        rewrite unsigned_lit_small by lia; rewrite Z.add_0_r; reflexivity).
    pmkst HS.
    lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
      change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + ONANN_FMLP)) mm rom) mdx) Q) end.
    apply (HNEXT (ms_regs msF) (ms_mem msF) mdF ltac:(lia)).
    unfold fm_inv.
    split; [unfold onann_cur;
      refine (conj HJ3 (conj Het (conj Hfrst (conj Hpermt (conj HlyFt
        (conj HMOt (conj KGf (conj SVf FLf))))))))|].
    split; [exact TWf|]. split; [exact AOKf|]. split; [exact SLDf|]. split; [exact GBf|].
    split; [exact RDf|]. split; [exact VMf0|]. split; [exact VMf8|]. split; [exact VMf16|].
    split; [exact VMf32|]. split; [exact VMf40|]. split; [lia|]. split; [exact HOFF|].
    split; [exact R2f|]. split; [exact R3f|]. split; [exact R4f|]. split; [exact R8f|].
    split; [exact R9f|]. split; [exact R18f|]. split; [exact R19f|]. split; [exact R20f|].
    split; [exact R21f|]. split; [exact R22f|]. split; [exact R23f|]. split; [exact R24f|].
    split; [exact R25f|]. split; [exact R26f | exact R27f]. }
  { (* 15 < 6 + i + 1: the ten turns are done, a5 = -1 *)
    assert (Hi9 : i = 9).
    { cbn [branch_taken sv_denot] in Hc. rewrite E22c, E27c in Hc.
      unfold w64 in Hc. rewrite !unsigned_lit_small in Hc by lia.
      rewrite fm_ltu in Hc by lia. apply Bool.negb_false_iff, Z.ltb_lt in Hc. lia. }
    replace (Z.to_nat (10 - i)) with (Datatypes.S 0%nat) in HOFF by lia.
    rewrite fm_find_mac_S, Hmqf in HOFF. cbn [TSS.find_mac_loop] in HOFF.
    paj_run_to_tok RUNTO HS HJ3 SHOKc YC4b.Bspan ONANN_DN.
    { fm_awr_rs. apply awr_ok_x_cons;
        [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia | apply awr_ok_x_nil]. }
    set (mdG := with_vm_backing (m_vm_lazy mdD) mat mdD) in *. clearbody mdG. clear mat.
    rename HF into HFg. rename HFr into HFrg. rename HG into HGg.
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mf) => rename mf into msG end.
    assert (KG2 : forall a, 0 <= a < 2 ^ 64 ->
      aview segs (w_H W2) (ms_mem msG) a = aview segs (w_H W2) mem3 a).
    { intros a Ha. rewrite <- (KD a Ha).
      apply (kept_of_frame _ _ _ _ _ (fun _ : Z => False) HFrg); [| exact Ha | intros []].
      intros b0 wlo whi x Hin Hx.
      lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
      cbn [In] in Hin.
      repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; lia |]).
      destruct Hin. }
    assert (PG2 : forall a, apresent (w_H W2) mem3 a -> apresent (w_H W2) (ms_mem msG) a)
      by (intros a Ha; exact (apresent_grows _ _ _ a HGg (PD a Ha))).
    destruct (MOVE (ms_mem msG) (KC _ KG2) (PC _ PG2)) as
      (TWg & AOKg & SLDg & GBg & RDg & VMg0 & VMg8 & VMg16 & VMg32 & VMg40 & KGg & SVg & FLg).
    fm_reg HS (2%bv : bv 5) (w64 sp1) R2g
      ltac:(cbn [sv_denot]; rewrite (EClo 2%nat ltac:(lia)), (EAlo 2%nat ltac:(lia)),
        (fm_ET_reg regsT pvv fpv 2 2%bv eq_refl), T2, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    fm_reg HS (3%bv : bv 5) (w64 (as_gp B)) R3g
      ltac:(cbn [sv_denot]; rewrite (EClo 3%nat ltac:(lia)), (EAlo 3%nat ltac:(lia)),
        (fm_ET_reg regsT pvv fpv 3 3%bv eq_refl), T3, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    fm_reg HS (4%bv : bv 5) (w64 (as_tp B)) R4g
      ltac:(cbn [sv_denot]; rewrite (EClo 4%nat ltac:(lia)), (EAlo 4%nat ltac:(lia)),
        (fm_ET_reg regsT pvv fpv 4 4%bv eq_refl), T4, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    fm_reg HS (8%bv : bv 5) (w64 (spZ regs)) R8g
      ltac:(cbn [sv_denot]; rewrite (EClo 8%nat ltac:(lia)), (EAlo 8%nat ltac:(lia)),
        (fm_ET_reg regsT pvv fpv 8 8%bv eq_refl), T8, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    fm_reg HS (9%bv : bv 5) (w64 sp1) R9g
      ltac:(cbn [sv_denot]; rewrite (EClo 9%nat ltac:(lia)), (EAlo 9%nat ltac:(lia)),
        (fm_ET_reg regsT pvv fpv 9 9%bv eq_refl), T9, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    fm_reg HS (18%bv : bv 5) (w64 (SHADOW_OFF + F / 8)) R18g
      ltac:(cbn [sv_denot]; rewrite (EClo 18%nat ltac:(lia)), (EAlo 18%nat ltac:(lia)),
        (fm_ET_reg regsT pvv fpv 18 18%bv eq_refl), T18, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    fm_reg HS (19%bv : bv 5) (w64 F) R19g
      ltac:(cbn [sv_denot]; rewrite (EClo 19%nat ltac:(lia)), (EAlo 19%nat ltac:(lia)),
        (fm_ET_reg regsT pvv fpv 19 19%bv eq_refl), T19, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    fm_reg HS (20%bv : bv 5) (w64 ONANN_S) R20g
      ltac:(cbn [sv_denot]; rewrite (EClo 20%nat ltac:(lia)), (EAlo 20%nat ltac:(lia)),
        (fm_ET_reg regsT pvv fpv 20 20%bv eq_refl), T20, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    fm_reg HS (24%bv : bv 5) (w64 SHADOW_OFF) R24g ltac:(reflexivity).
    fm_reg HS (25%bv : bv 5) (w64 F) R25g
      ltac:(cbn [sv_denot]; rewrite (EClo 19%nat ltac:(lia)), (EAlo 19%nat ltac:(lia)),
        (fm_ET_reg regsT pvv fpv 19 19%bv eq_refl), T19, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    fm_reg HS (26%bv : bv 5) (w64 (F + ONANN_A)) R26g
      ltac:(cbn [sv_denot]; rewrite (EClo 19%nat ltac:(lia)), (EAlo 19%nat ltac:(lia)),
        (fm_ET_reg regsT pvv fpv 19 19%bv eq_refl), T19;
        unfold w64, ONANN_A; rewrite unsigned_lit_small by lia; reflexivity).
    fm_reg HS (22%bv : bv 5) (w64 fp) R22g
      ltac:(cbn [sv_denot]; rewrite (EClo 33%nat ltac:(lia)), (EAlo 33%nat ltac:(lia)),
        (fm_ET_x1 regsT pvv fpv); unfold w64;
        rewrite unsigned_lit_small by lia; rewrite Z.add_0_r; exact Hfpeq).
    fm_reg HS (16%bv : bv 5) (w64 (onann_pv timg_B b)) R16g
      ltac:(cbn [sv_denot]; rewrite (EClo 32%nat ltac:(lia)), (EAlo 32%nat ltac:(lia)),
        (fm_ET_x0 regsT pvv fpv); unfold w64;
        rewrite unsigned_lit_small by lia; rewrite Z.add_0_r; exact Hpveq).
    fm_reg HS (15%bv : bv 5) (w64 (onann_off (onann_w1 timg_B Bw b) b)) R15g
      ltac:(rewrite HOFF; cbn [sv_denot]; exact fm_m1).
    fm_reg HS (11%bv : bv 5) (w64 1) R11g ltac:(reflexivity).
    pmkst HS.
    lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
      change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + ONANN_DN)) mm rom) mdx) Q) end.
    apply (DN HLAWS HCALL STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF
      Bw Bw' pos sp1 F ly2 S2 W2 (ms_mem msG) mdG (ms_regs msG) HFIX).
    - unfold onann_dn_cur.
      split; [|split; [exact TWg | split; [exact Hig | split; [exact AOKg | exact SLDg]]]].
      unfold onann_cur.
      refine (conj HJ3 (conj Het (conj Hfrst (conj Hpermt (conj HlyFt
        (conj HMOt (conj KGg (conj SVg FLg)))))))).
    - unfold onann_regs_dn, onann_regs_ign, onann_regs_rel.
      refine (conj (conj (conj R2g (conj (eq_trans R3g (eq_sym Hgp)) (conj (eq_trans R4g (eq_sym Htp))
        (conj R8g (conj R9g (conj R18g (conj R19g R25g))))))) (conj R20g R24g))
        (conj R22g (conj R26g (conj R16g (conj R15g R11g))))). } }
(* the ten turns *)
assert (LOOP : forall (n : nat) (i : Z) (regsT : bvmap 5 word) (memT : word -> option byte) (mdT : Model),
  Z.of_nat n = 9 - i ->
  fm_inv STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs fp buf now pos sp1 F pvv fpv Bw b
    ly2 S2 W2 i regsT memT mdT ->
  SRr segs W2 (mkCfg (@YK11.mkst fx regsT (Z_to_bv 64 (BASE + ONANN_FMLP)) memT (YK11.seg_rom segs)) mdT)
    (@transport_onann_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' b)).
{ induction n as [|n IH]; intros i regsT memT mdT Hn HINV.
  - apply (TURN i regsT memT mdT HINV). intros regsU memU mdU Hle _. exfalso. lia.
  - apply (TURN i regsT memT mdT HINV). intros regsU memU mdU Hle HINV'.
    exact (IH (i + 1) regsU memU mdU ltac:(lia) HINV'). }
(* +0x250 .. +0x294: the spills, unknown_len, unknown, i = 0 *)
pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
  TG.G_HARNESS_B HGX 0 []) as RUNTO.
pose proof (paj_branch (PI := PI_transportb)) as BR.
assert (HVm16 : YI04.val_mem segs (mrestrict (w_H W2) mem2) (sp1 + 16) 8 (F + ONANN_A))
  by (apply (fm_val_rdword (w_H W2) mem2 (sp1 + 16) (F + ONANN_A) ltac:(unfold ONANN_A; lia));
      exact (proj2 (proj2 (proj2 HSLD)))).
assert (HVm24 : YI04.val_mem segs (mrestrict (w_H W2) mem2) (sp1 + 24) 8 now)
  by (apply (fm_val_rdword (w_H W2) mem2 (sp1 + 24) now ltac:(lia));
      exact (proj1 (proj2 (proj2 HSLD)))).
pose proof (fm_entry_a W2 regs2 mem2 sp1 F buf now Q9 Q26 HF0 HFsp Hsp47 Hbuf0 ltac:(lia) Hnow Hsp1lo
  ltac:(intros a Ha; apply K6; lia) HA24 HA32 HVm16 HVm24) as HS.
assert (HEI : img_env VAL A_LIM (fm_EA regs2 buf (F + ONANN_A) now))
  by (unfold fm_EA; apply Eimg_env).
assert (SHOK : sh_ok segs (SLit 0) [] (fm_EA regs2 buf (F + ONANN_A) now) (mrestrict (w_H W2) mem2))
  by (unfold sh_ok; constructor).
assert (U9a : bv_unsigned (ew (fm_EA regs2 buf (F + ONANN_A) now) 9) = sp1)
  by (rewrite (fm_EA_reg regs2 buf _ now 9 9%bv eq_refl), Q9; unfold w64;
      apply unsigned_lit_small; lia).
psrr_branch_tok RUNTO BR HS SHOK YC4b.Bspan.
- exfalso. cbn [sv_denot branch_taken] in Hc.
  rewrite (fm_EA_reg regs2 buf _ now 10 10%bv eq_refl), Q10 in Hc.
  unfold w64 in Hc. rewrite unsigned_lit_small in Hc by lia. rewrite Z.add_0_r in Hc.
  rewrite fm_eqb in Hc by lia. cbn in Hc. discriminate.
- (* +0x254 .. +0x290: the four spills, unknown_len = 15, i = 0, unknown = buf + 30 *)
  clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan ONANN_FMLP.
  { fm_awr_rs.
    apply awr_ok_x_cons.
    { intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U9a in Ha.
      left. split; [unfold awr_byte; left; lia | lia]. }
    apply awr_ok_x_cons;
      [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia | apply awr_ok_x_nil]. }
  set (mdR := with_vm_backing (m_vm_lazy md2) mat md2) in *. clearbody mdR. clear mat.
  rename HF into HFr0. rename HFr into HFrr0. rename HG into HGr0.
  lazymatch type of HS with st_ok_pi _ _ ?EF _ (restrict _ ?mf) => set (ER := EF) in *; rename mf into msR end.
  assert (ERlo : forall n, (n < 1024)%nat -> ew ER n = ew (fm_EA regs2 buf (F + ONANN_A) now) n)
    by (intros n Hn; unfold ER; rewrite ?ew_ewset_other by lia; reflexivity).
  clearbody ER.
  (* the run changed only the two spill pairs *)
  assert (KR : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 <= a < sp1 + 48) ->
    aview segs (w_H W2) (ms_mem msR) a = aview segs (w_H W2) mem2 a).
  { intros a Ha Hn.
    apply (kept_of_frame _ _ _ _ _ (fun x => sp1 <= x < sp1 + 48) HFrr0); [| exact Ha | exact Hn].
    intros b0 wlo whi x Hin Hx.
    lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
    cbn [In] in Hin.
    repeat (destruct Hin as [Hin | Hin];
      [injection Hin as <- <- <-; cbn [base_val] in Hx; rewrite ?U9a, ?U26a in Hx; lia |]).
    destruct Hin. }
  assert (PR : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem msR) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HGr0 Ha)).
  (* the spill slots the run wrote *)
  pose proof U9a as U9f.
  assert (D24 : sv_denot ER (SOff 24 0) = Z_to_bv 64 SHADOW_OFF).
  { cbn [sv_denot]. rewrite (ERlo 24%nat ltac:(lia)), (fm_EA_reg regs2 buf _ now 24 24%bv eq_refl), Q24.
    unfold w64. rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia). rewrite Z.add_0_r. reflexivity. }
  assert (D25 : sv_denot ER (SOff 25 0) = Z_to_bv 64 F).
  { cbn [sv_denot]. rewrite (ERlo 25%nat ltac:(lia)), (fm_EA_reg regs2 buf _ now 25 25%bv eq_refl), Q25.
    unfold w64. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity. }
  assert (D16 : sv_denot ER (SOff 16 0) = Z_to_bv 64 pvv).
  { cbn [sv_denot]. rewrite (ERlo 16%nat ltac:(lia)), (fm_EA_reg regs2 buf _ now 16 16%bv eq_refl).
    unfold pvv. rewrite Z.add_0_r. reflexivity. }
  assert (D22 : sv_denot ER (SOff 22 0) = Z_to_bv 64 fpv).
  { cbn [sv_denot]. rewrite (ERlo 22%nat ltac:(lia)), (fm_EA_reg regs2 buf _ now 22 22%bv eq_refl).
    unfold fpv. rewrite Z.add_0_r. reflexivity. }
  fm_region HS 0%nat HR0.
  pose proof (can_field_of_region ER _ 9%nat sp1 _ _ _ _ _ 0 8%N (SOff 24 0) SHADOW_OFF
    HR0 U9f ltac:(fm_in) D24 ltac:(unfold SHADOW_OFF; cbn; lia) ltac:(cbn; lia)) as VB0.
  pose proof (can_field_of_region ER _ 9%nat sp1 _ _ _ _ _ 8 8%N (SOff 25 0) F
    HR0 U9f ltac:(fm_in) D25 ltac:(cbn; lia) ltac:(cbn; lia)) as VB8.
  pose proof (can_field_of_region ER _ 9%nat sp1 _ _ _ _ _ 32 8%N (SOff 16 0) pvv
    HR0 U9f ltac:(fm_in) D16 ltac:(cbn; lia) ltac:(cbn; lia)) as VB32.
  pose proof (can_field_of_region ER _ 9%nat sp1 _ _ _ _ _ 40 8%N (SOff 22 0) fpv
    HR0 U9f ltac:(fm_in) D22 ltac:(cbn; lia) ltac:(cbn; lia)) as VB40.
  change (N.to_nat 8) with 8%nat in VB0, VB8, VB32, VB40.
  rewrite Z.add_0_r in VB0.
  (* the slots the run did not touch, and the rest of the memory *)
  assert (D33 : sv_denot ER (SOff 33 0) = Z_to_bv 64 (F + ONANN_A)).
  { cbn [sv_denot]. rewrite (ERlo 33%nat ltac:(lia)), (fm_EA_x1 regs2 buf (F + ONANN_A) now).
    unfold w64. rewrite unsigned_lit_small by (unfold ONANN_A; lia). rewrite Z.add_0_r. reflexivity. }
  assert (D34 : sv_denot ER (SOff 34 0) = Z_to_bv 64 now).
  { cbn [sv_denot]. rewrite (ERlo 34%nat ltac:(lia)), (fm_EA_x2 regs2 buf (F + ONANN_A) now).
    unfold w64. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity. }
  pose proof (can_field_of_region ER _ 9%nat sp1 _ _ _ _ _ 16 8%N (SOff 33 0) (F + ONANN_A)
    HR0 U9f ltac:(fm_in) D33 ltac:(unfold ONANN_A; cbn; lia) ltac:(cbn; lia)) as VB16.
  change (N.to_nat 8) with 8%nat in VB16.
  assert (TW0 : tw_at TMAP_B (aview segs (w_H W2) (ms_mem msR)) (onann_w1 timg_B Bw b)).
  { apply (tw_kept_rows TMAP_B _ _ _ Htw2). intros o bb n ii Hin Hii.
    pose proof (tw_row TMAP_B o bb n TMAP_B_ok Hin) as (_ & _ & _ & Hb0 & Hbn).
    pose proof (TMAP_B_hull (bb + ii)
      ltac:(exists o; exists bb; exists n; split; [exact Hin | lia])) as Hh.
    unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh.
    apply KR; lia. }
  assert (AOK0 : onann_a_ok W2 (ms_mem msR) F buf b).
  { pose proof HAOK as (Ga1 & Ga2 & Ra1 & Ra2 & Sh1).
    assert (HFd : 0 <= F / 8 <= 2 ^ 44)
      by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
    split; [|split; [|split; [|split]]].
    - apply (fm_garr8_ext W2 mem2 (ms_mem msR)); [|exact Ga1].
      intros j Hj. pose proof (fm_ann_field_len (skipn 15 (DSpec.fr_body b))) as Hl.
      apply KR; unfold ONANN_A; lia.
    - apply (fm_garr8_ext W2 mem2 (ms_mem msR)); [|exact Ga2].
      intros j Hj. pose proof (fm_ann_field_len (skipn 24 (DSpec.fr_body b))) as Hl.
      apply KR; unfold ONANN_A; lia.
    - rewrite <- Ra1. apply YCbq.rdword_ext. intros kk Hk. apply KR; unfold ONANN_A; lia.
    - rewrite <- Ra2. apply YCbq.rdword_ext. intros kk Hk. apply KR; unfold ONANN_A; lia.
    - intros ii Hii. rewrite (KR (SHADOW_OFF + F / 8 + ii)); [exact (Sh1 ii Hii) | | ];
        unfold SHADOW_OFF in *; lia. }
  pose proof (can_field_of_region ER _ 9%nat sp1 _ _ _ _ _ 24 8%N (SOff 34 0) now
    HR0 U9f ltac:(fm_in) D34 ltac:(cbn; lia) ltac:(cbn; lia)) as VB24.
  change (N.to_nat 8) with 8%nat in VB24.
  assert (SLD0 : onann_slots_dn W2 (ms_mem msR) fp now sp1 F).
  { pose proof HSLD as (SL48 & SL56 & SL24 & SL16).
    split; [|split; [|split]]; unfold onann_slot.
    - rewrite <- SL48. apply YCbq.rdword_ext. intros kk Hk. apply KR; lia.
    - rewrite <- SL56. apply YCbq.rdword_ext. intros kk Hk. apply KR; lia.
    - rewrite <- SL24. apply YCbq.rdword_ext. intros kk Hk.
      replace (sp1 + 24 + kk) with (sp1 + 24 + Z.of_nat (Z.to_nat kk)) by lia.
      rewrite (fm_aview_of_val W2 (ms_mem msR) (sp1 + 24) 8 now (Z.to_nat kk) ltac:(lia) VB24).
      rewrite (fm_aview_of_val W2 mem2 (sp1 + 24) 8 now (Z.to_nat kk) ltac:(lia) HVm24). reflexivity.
    - rewrite <- SL16. apply YCbq.rdword_ext. intros kk Hk.
      replace (sp1 + 16 + kk) with (sp1 + 16 + Z.of_nat (Z.to_nat kk)) by lia.
      rewrite (fm_aview_of_val W2 (ms_mem msR) (sp1 + 16) 8 (F + ONANN_A) (Z.to_nat kk) ltac:(lia) VB16).
      rewrite (fm_aview_of_val W2 mem2 (sp1 + 16) 8 (F + ONANN_A) (Z.to_nat kk) ltac:(lia) HVm16).
      reflexivity. }
  assert (GB0 : garr8 segs (mrestrict (w_H W2) (ms_mem msR)) buf (TW.zs b)).
  { apply (fm_garr8_ext W2 mem2 (ms_mem msR)); [|exact Hgarr].
    intros j Hj. unfold TW.zs in Hj. rewrite length_map in Hj.
    apply KR; [lia|]. destruct Hoffbuf2 as [Ho | Ho]; lia. }
  assert (RD0 : decode_rd_ok W2 (ms_mem msR) buf (Z.of_nat (length b))).
  { apply (trans_rd_ok_view W2 W2 mem2 (ms_mem msR) buf (Z.of_nat (length b)) HRDbuf).
    - intros a Ha. apply KR; [lia|]. destruct Hoffbuf2 as [Ho | Ho]; lia.
    - intros s Hs. apply KR; unfold kLowMemEnd, kHighShadowEnd in Hs; lia. }
  assert (KG0 : acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W2 (ms_mem msR)
    (spZ regs - ONANN_STK) (spZ regs) (onann_wr Bw b)).
  { apply (fm_keep lyc Sc W memc mdc W2 mem2 (ms_mem msR)
      (fun a => sp1 <= a < sp1 + 48) regs Bw b LAWS HARc Hce HK).
    - intros a Ha Hn. apply KR; [exact Ha | exact Hn].
    - exact PR.
    - intros a Ha. lia. }
  assert (SV0 : Forall (fun o : Z * Z => rdword (aview segs (w_H W2) (ms_mem msR)) (spZ regs - fst o) =
    Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) ONANN_SAVED).
  { apply Forall_forall. intros o Hin. cbv beta.
    pose proof (proj1 (Forall_forall _ _) HSV o Hin) as Hv. cbv beta in Hv.
    assert (Ho : 8 <= fst o <= 104).
    { unfold ONANN_SAVED in Hin. cbn [In] in Hin.
      repeat (destruct Hin as [Hin | Hin]; [subst o; cbn [fst]; lia |]). destruct Hin. }
    rewrite <- Hv. apply YCbq.rdword_ext. intros kk Hk. apply KR; lia. }
  assert (FL0 : rdword (aview segs (w_H W2) (ms_mem msR)) (F + ONANN_FBYTES - 8) =
    Some (flag_addr lyc ONANN_CID pos)).
  { rewrite <- HFL. apply YCbq.rdword_ext. intros kk Hk.
    apply KR; unfold ONANN_FBYTES; lia. }
  (* the model at the first turn *)
  assert (HOFF0 : onann_off (onann_w1 timg_B Bw b) b =
    TSS.find_mac_loop (DSpec.ann_unknown (DSpec.fr_body b))
      (TW.S_cfg_host_mac (onann_w1 timg_B Bw b)) 0 (Z.to_nat (10 - 0))).
  { unfold onann_off. rewrite Hcmd, Z.eqb_refl. cbv iota. apply fm_find_mac_m_eq. }
  (* the registers at the loop head *)
  fm_reg HS (2%bv : bv 5) (w64 sp1) P2
    ltac:(cbn [sv_denot]; rewrite (ERlo 2%nat ltac:(lia)), (fm_EA_reg regs2 buf _ now 2 2%bv eq_refl), Q2,
      Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  fm_reg HS (3%bv : bv 5) (w64 (as_gp B)) P3
    ltac:(cbn [sv_denot]; rewrite (ERlo 3%nat ltac:(lia)), (fm_EA_reg regs2 buf _ now 3 3%bv eq_refl), Q3, Hgp,
      Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  fm_reg HS (4%bv : bv 5) (w64 (as_tp B)) P4
    ltac:(cbn [sv_denot]; rewrite (ERlo 4%nat ltac:(lia)), (fm_EA_reg regs2 buf _ now 4 4%bv eq_refl), Q4, Htp,
      Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  fm_reg HS (8%bv : bv 5) (w64 (spZ regs)) P8
    ltac:(cbn [sv_denot]; rewrite (ERlo 8%nat ltac:(lia)), (fm_EA_reg regs2 buf _ now 8 8%bv eq_refl), Q8,
      Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  fm_reg HS (9%bv : bv 5) (w64 sp1) P9
    ltac:(cbn [sv_denot]; rewrite (ERlo 9%nat ltac:(lia)), (fm_EA_reg regs2 buf _ now 9 9%bv eq_refl), Q9,
      Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  fm_reg HS (18%bv : bv 5) (w64 (SHADOW_OFF + F / 8)) P18
    ltac:(cbn [sv_denot]; rewrite (ERlo 18%nat ltac:(lia)), (fm_EA_reg regs2 buf _ now 18 18%bv eq_refl), Q18,
      Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  fm_reg HS (19%bv : bv 5) (w64 F) P19
    ltac:(cbn [sv_denot]; rewrite (ERlo 19%nat ltac:(lia)), (fm_EA_reg regs2 buf _ now 19 19%bv eq_refl), Q19,
      Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  fm_reg HS (20%bv : bv 5) (w64 ONANN_S) P20
    ltac:(cbn [sv_denot]; rewrite (ERlo 20%nat ltac:(lia)), (fm_EA_reg regs2 buf _ now 20 20%bv eq_refl), Q20,
      Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  fm_reg HS (21%bv : bv 5) (w64 (buf + 30 + 0)) P21
    ltac:(cbn [sv_denot]; rewrite (ERlo 32%nat ltac:(lia)), (fm_EA_x regs2 buf (F + ONANN_A) now); unfold w64;
      rewrite unsigned_lit_small by lia; f_equal; lia).
  fm_reg HS (22%bv : bv 5) (w64 (6 + 0)) P22 ltac:(unfold w64; f_equal; lia).
  fm_reg HS (23%bv : bv 5) (w64 1) P23 ltac:(reflexivity).
  fm_reg HS (24%bv : bv 5) (w64 (buf + 30)) P24
    ltac:(cbn [sv_denot]; rewrite (ERlo 32%nat ltac:(lia)), (fm_EA_x regs2 buf (F + ONANN_A) now); unfold w64;
      rewrite unsigned_lit_small by lia; rewrite Z.add_0_r; reflexivity).
  fm_reg HS (25%bv : bv 5) (w64 0) P25 ltac:(reflexivity).
  fm_reg HS (26%bv : bv 5) (w64 (buf + 30 + 0)) P26
    ltac:(cbn [sv_denot]; rewrite (ERlo 32%nat ltac:(lia)), (fm_EA_x regs2 buf (F + ONANN_A) now); unfold w64;
      rewrite unsigned_lit_small by lia; f_equal; lia).
  fm_reg HS (27%bv : bv 5) (w64 15) P27 ltac:(reflexivity).
  pmkst HS.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + ONANN_FMLP)) mm rom) mdx) Q) end.
  apply (LOOP 9%nat 0 (ms_regs msR) (ms_mem msR) mdR ltac:(lia)).
  unfold fm_inv.
  split; [unfold onann_cur;
    refine (conj HJ (conj He (conj Hfrs (conj Hperm (conj HlyF
      (conj HMO (conj KG0 (conj SV0 FL0))))))))|].
  split; [exact TW0|]. split; [exact AOK0|]. split; [exact SLD0|]. split; [exact GB0|].
  split; [exact RD0|]. split; [exact VB0|]. split; [exact VB8|]. split; [exact VB16|].
  split; [exact VB32|]. split; [exact VB40|]. split; [lia|]. split; [exact HOFF0|].
  split; [exact P2|]. split; [exact P3|]. split; [exact P4|]. split; [exact P8|].
  split; [exact P9|]. split; [exact P18|]. split; [exact P19|]. split; [exact P20|].
  split; [exact P21|]. split; [exact P22|]. split; [exact P23|]. split; [exact P24|].
  split; [exact P25|]. split; [exact P26 | exact P27].
Qed.

End m.

(* The find_mac piece of the walk of on_announce (OnannCutB.v onann_fm_stmt), at every machine, run ceiling,
   record and meter. *)
Lemma onann_fm_piece : forall (fx : YK11.FPState) (rc : YM05.RunCeil) B MT, @onann_fm_stmt fx rc B MT.
Proof. intros fx rc B MT. exact (@fm_holds fx rc B MT). Qed.
