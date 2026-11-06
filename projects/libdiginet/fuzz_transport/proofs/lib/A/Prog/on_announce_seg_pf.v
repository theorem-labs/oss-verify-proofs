(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 706 of its 765 lines of code are new or changed and 1865 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/on_announce_seg_tail.v; 1000 of its 1076 lines of code are new or changed and 689 lines of the source are left out. *)
(* on_announce_seg_pf: the personality piece of the image-A walk of on_announce, onann_piece_pf : onann_pf_stmt
   (lib/A/Prog/OnannCut.v), code +0x248 .. +0x2a4 (0x87cbc .. 0x87d18), from the personality cut onann_pf_at to the
   find_mac cut onann_fm_at (cmd = 0xe1, +0x2a8) or the desk notice cut onann_dn_at (any other cmd, +0x308). The runs
   are lib/A/Prog/TransportGRunA.v paj_run_x / paj_run_to_x over the caller's G journal:
     run A  +0x248 .. +0x24c  a0 = a + 10 (a.name), `jal diginet_personality_from_name` (+0x24c): the donor-form callee
                              lifted by TransportGCg.v gx_call_cg; its premise: x = a + 10 <> 0, tb = TSess.v ann_field of
                              the body from 24 (the name the leaf stored and its 0), placed in the own class-4 frame
                              (decode_in_fake) and marked usable by a's shadow bytes 32 .. 36 (TransportGNotice.v
                              frame_ra_zero, frame_hull_vis), outside the callee's window (the frame lies below
                              alloc_ceiling), the read-only view (kit onann_rom_call); its X: a0 = trans_pfrom_res tb =
                              onann_pv timg_A b (kit onann_pv_res);
     run C  +0x250 .. +0x254  s9 = p and `beqz a0` from a state with no region: p = 0 runs to the join +0x270, any other p
                              to +0x258;
     run N  +0x258 .. +0x26c  the checked 8-byte store of p at s + 128 (g_s.personality; the shadow entry of
                              [s + 128, s + 136), g_s's zero shadow: trans_onann_cells), to the join: the world is
                              onann_w1 timg_A Bw b = set_S_personality Bw p (row 2 of onann_wr);
     run D  +0x270 .. +0x2a4  a at s1 + 56, s11 = fp + 30, the checked 1-byte load of f + 30 (the shadow entry of
                              [f + 30, f + 31): the token engine's slow-path stub at +0x818), a0 = cmd = fr_cmd b,
                              s5 = n = F + 336, a1 = 0xe1, a3 = -1, the spills of the frame, now and the shadow byte's
                              address at s1 + 40, s1 + 0 and s1 + 32, up to `bne a0, a1`;
     run E  +0x2a4            `bne a0, a1` from a state with no region: cmd <> 0xe1 to onann_dn_at (a3 = -1 =
                              onann_off), cmd = 0xe1 to onann_fm_at.
   What the cut carries (onann_cur) moves across the callee by pf_cur_call (TransportGCg.v dk_kept_trans_nf_g with the
   own frame's separation, TransportGFrame.v dkg_nf_sep_gw) and across runs N and D by pf_cur_step (TransportGFrame.v
   dk_kept_nfz_gw); a's bytes move by pf_aok_move; the runs with no region keep the memory (functional
   extensionality over the run's frame). *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From Stdlib Require Import FunctionalExtensionality.
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c YO0f.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportSyms DgnTransportList DgnTransportAddr DgnTransportPa DgnTransportImg DgnTransportPaLib YC4b YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG AF0x.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportCg TransportGCg TransportGRwA TransportGRunA CanKit TransportGFrame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import m_lost_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import io_send_cg send_control_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_wake_cg maybe_online_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import session_lost_cg on_ack_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_personality_from_name_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportRtCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require diginet_announce_parse_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import on_announce_cg OnannCut.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require TransportGNotice.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import on_announce_seg_kit on_announce_seg_kitf.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TSess0 TSess TCb TWorldLemmas TNeed.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec DgnLib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module FCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.AsanCells.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TN := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TNeed.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module DLib := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnLib.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 1. The pcs and the symbolic states                                  *)
(* ------------------------------------------------------------------ *)

(* The pcs inside the piece, as offsets from the listing's base. *)
Definition ONANN_PFC : Z := AF_on_announce + 0x250.   (* 0x87cc4 `mv s9, a0`, the call's return *)
Definition ONANN_PFN : Z := AF_on_announce + 0x258.   (* 0x87ccc `addi a0, s4, 128` (p <> 0) *)
Definition ONANN_PFJ : Z := AF_on_announce + 0x270.   (* 0x87ce4 `sd s5, 56(s1)`, the join *)
Definition ONANN_PFB : Z := AF_on_announce + 0x2a4.   (* 0x87d18 `bne a0, a1` *)

(* A state with no region and no fact (runs A, C and E). *)
Definition pf_ss0 (pc : Z) : sstate := mkSS pc sr_atoms [] None (mkFacts [] [] []).
(* The shadow base of the token engine (s8, atom 24) and the span of shadow bytes its entries read. *)
Definition PF_Bx : sv := SOff 24 0.
Definition PF_B0 : Z * Z := (0, 0).
(* Run N: g_s.personality's 8 bytes (s4 = s, atom 20), writable; its shadow entry. *)
Definition pf_rg_gs : YP09.region := YP09.mkRegion (Some 20%nat) 128 136 128 136 [].
Definition pf_facts_n : facts :=
  mkFacts [(20%nat, mkAF ONANN_S ONANN_S 6); (24%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition pf_ss_n : sstate := mkSS ONANN_PFN sr_atoms [pf_rg_gs] None pf_facts_n.
Definition PF_SH_N : list shent := [mkSHE 20 128 136].
(* Run D: the spill slots s1 + 0 .. s1 + 64 (s1 = sp1, atom 9), writable; f + 30 (s6 = fp, atom 22) holding cmd
   (atom 32), read only; the shadow entry of [f + 30, f + 31). *)
Definition pf_rg_stk : YP09.region := YP09.mkRegion (Some 9%nat) 0 64 0 64 [].
Definition pf_rg_f : YP09.region :=
  YP09.mkRegion (Some 22%nat) 30 31 0 0 [YP09.mkChunk 30 (YP09.CVal 1 (SOff 32 0))].
Definition pf_facts_j : facts :=
  mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (22%nat, mkAF 4096 (2 ^ 47 - 2 ^ 23) 3);
           (24%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (32%nat, mkAF 0 255 0)] [] [].
Definition pf_ss_j : sstate := mkSS ONANN_PFJ sr_atoms [pf_rg_stk; pf_rg_f] None pf_facts_j.
Definition PF_SH_J : list shent := [mkSHE 22 30 31].

(* ------------------------------------------------------------------ *)
(* 2. The model                                                        *)
(* ------------------------------------------------------------------ *)

(* An announce field (copy_strz's bytes and its 0) has at most 10 bytes, and its last byte is the 0. *)
Lemma pf_ann_len : forall s, (length (TSS.ann_field s) <= 10)%nat.
Proof.
  intros s. unfold TSS.ann_field. rewrite length_app, length_firstn. cbn [length].
  pose proof (DSpec.strz_len_le s) as L. rewrite <- DSpec.copy_len_strz in L. lia.
Qed.

Lemma pf_tb_nul : forall s, In (DSpec.b8 0) (TSS.ann_field s).
Proof. intros s. unfold TSS.ann_field. apply in_or_app. right. left. reflexivity. Qed.

Lemma pf_find_01 : forall z i, TN.personality_name_find DLib.personalities 0 z = Some i -> i = 0 \/ i = 1.
Proof.
  intros z i H. unfold DLib.personalities in H. cbn [TN.personality_name_find DLib.dp_announce_name] in H.
  destruct (TN.z_list_eqb z _); [injection H as <-; lia|].
  destruct (TN.z_list_eqb z _); [injection H as <-; lia | discriminate H].
Qed.

(* The personality pointer: 0 exactly when the name is no personality's, then the world is unchanged; else the
   store of :192-193. *)
Lemma pf_pv_facts : forall Bw b,
  0 <= onann_pv timg_A b < 2 ^ 64 /\
  (onann_pv timg_A b = 0 -> onann_w1 timg_A Bw b = Bw) /\
  (onann_pv timg_A b <> 0 -> onann_w1 timg_A Bw b = TW.set_S_personality Bw (onann_pv timg_A b)).
Proof.
  intros Bw b. unfold onann_w1, onann_pv.
  destruct (TN.diginet_personality_from_name (onann_name b)) as [i|] eqn:Ei.
  - unfold TN.diginet_personality_from_name in Ei. destruct (pf_find_01 _ _ Ei) as [-> | ->];
      change (TI.ti_personalities timg_A) with TRANS_PERS; unfold TRANS_PERS;
      (split; [lia | split; [intros H; lia | intros _; reflexivity]]).
  - split; [lia | split; [intros _; reflexivity | intros H; exfalso; exact (H eq_refl)]].
Qed.

(* set_S_personality at its numeral offset (g_s + 128). *)
Lemma pf_w1_eq : forall Bw v, TW.set_S_personality Bw v = TW.upd Bw (TW.OFF_g_s + 128) (TW.put 8 v).
Proof. intros Bw v. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* 3. Arithmetic, bytes and the run's values                           *)
(* ------------------------------------------------------------------ *)

(* sp1 = the realigned sp (`addi sp, sp, -192`, `andi sp, sp, -32`). *)
Lemma pf_sp1 : forall x sp1, 0 <= x -> x mod 16 = 0 -> sp1 = 32 * ((x - ONANN_FRAME) / 32) ->
  x - 208 <= sp1 <= x - 192 /\ sp1 mod 32 = 0.
Proof.
  intros x sp1 Hx Hx16 Esp1. rewrite Esp1. unfold ONANN_FRAME.
  pose proof (Z.div_mod (x - 192) 32 ltac:(lia)) as D.
  pose proof (Z.mod_pos_bound (x - 192) 32 ltac:(lia)) as M.
  pose proof (Z.div_mod x 16 ltac:(lia)) as D16. rewrite Hx16, Z.add_0_r in D16.
  set (q := (x - 192) / 32) in *. set (r := (x - 192) mod 32) in *. set (t := x / 16) in *.
  split; [lia|]. rewrite Z.mul_comm, Z.mod_mul by lia. reflexivity.
Qed.

(* A byte read through the view is a byte value. *)
Lemma pf_aview_byte : forall (H : word -> bool) (m : word -> option byte) a v,
  aview tfibsegs H m a = Some v -> 0 <= v < 256.
Proof.
  intros H m a v Hv. unfold aview in Hv.
  destruct (YP09.mbyte tfibsegs (mrestrict H m) a) as [b|]; [|discriminate Hv].
  cbn in Hv. injection Hv as <-. pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R.
  exact R.
Qed.

(* A byte read through the view is a one-byte value of the restricted memory. *)
Lemma pf_vm1 : forall (H : word -> bool) (m : word -> option byte) a v,
  aview tfibsegs H m a = Some v -> val_mem tfibsegs (mrestrict H m) a 1 v.
Proof.
  intros H m a v Hv k Hk. assert (k = 0%nat) by lia. subst k. cbn [Z.of_nat]. rewrite Z.add_0_r.
  unfold aview in Hv. destruct (YP09.mbyte tfibsegs (mrestrict H m) a) as [b|] eqn:Eb; [|discriminate Hv].
  cbn in Hv. injection Hv as <-. f_equal. apply bv_eq.
  pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
  unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
  rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite !(Z.mod_small (bv_unsigned b)) by lia. reflexivity.
Qed.

(* `srli a0, s11, 3` then `add a2, a0, s8` with s11 = fp + 30: the shadow byte's address of f + 30. *)
Lemma pf_denot_shadow : forall E n m v c SHB,
  ew E n = Z_to_bv 64 v -> ew E m = Z_to_bv 64 SHB ->
  0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 -> 0 <= SHB < 2 ^ 64 -> SHB + (v + c) / 8 < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff n c) (SLit 3)) (SOff m 0)) = Z_to_bv 64 (SHB + (v + c) / 8).
Proof.
  intros E n m v c SHB Hn Hm Hv Hvc HS1 HS2.
  assert (HD : 0 <= (v + c) / 8) by (apply Z.div_pos; lia).
  assert (Un : U E (SOff n c) = v + c) by exact (U_atom_off E n v c Hn Hv Hvc).
  assert (Um : U E (SOff m 0) = SHB) by exact (U_atom E m SHB Hm HS1).
  rewrite denot_lit_U. f_equal.
  rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
  rewrite Un, Um, U_SLit, (zcanon_id 3) by (unfold M64; lia).
  change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  rewrite (zcanon_id ((v + c) / 8)) by (unfold M64; lia).
  rewrite (Z.add_comm ((v + c) / 8) SHB). apply zcanon_id. unfold M64. lia.
Qed.

(* g_s's payload bytes are bytes of G. *)
Lemma pf_inG : forall a, ONANN_S <= a < ONANN_S + TW.SZ_g_s -> inG TG.G_HARNESS a.
Proof.
  intros a Ha. unfold inG. apply Exists_exists. exists (TA_g_s, TW.SZ_g_s).
  split; [exact (TMAP_A_in_G _ _ _ TMAP_A_g_s) | unfold in_zr, ONANN_S in *; cbn [fst snd]; lia].
Qed.

(* The value of an atom, and of an atom plus c. *)
Lemma pf_denot_atom : forall E n v, ew E n = v -> sv_denot E (SOff n 0) = v.
Proof. intros E n v H. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact H. Qed.

Lemma pf_denot_off : forall E n x c, ew E n = w64 x -> 0 <= x < 2 ^ 64 -> sv_denot E (SOff n c) = w64 (x + c).
Proof.
  intros E n x c H Hx. cbn [sv_denot]. rewrite H. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
Qed.

(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac. *)
Ltac pf_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | ?T => idtac "pf_reg: no match for" T; fail
  end.
(* A register holding the atom n of the run's valuation, which agrees below atom 1024 with a start valuation (EL)
   whose atom n is the start value of register rs (EE); Q : that start value is v. *)
Ltac pf_kreg HS EL EE r n rs Q H :=
  lazymatch type of Q with _ = ?v =>
    pf_reg HS r v H
      ltac:(exact (pf_denot_atom _ n v (eq_trans (EL n ltac:(lia)) (eq_trans (EE n rs eq_refl) Q)))) end.
(* A register holding atom n plus c (Q : the start value of rs is w64 x). *)
Ltac pf_kreg_off HS EL EE r n rs Q H x c :=
  pf_reg HS r (w64 (x + c)) H
    ltac:(exact (pf_denot_off _ n x c (eq_trans (EL n ltac:(lia)) (eq_trans (EE n rs eq_refl) Q)) ltac:(lia))).
(* A register holding a literal. *)
Ltac pf_klit HS r v H :=
  pf_reg HS r v H ltac:(cbn [sv_denot]; unfold w64; apply bv_eq; rewrite !Z_to_bv_unsigned; reflexivity).
(* Region i of the symbolic state HS, at the machine state's memory. *)
Ltac pf_region HS i HR :=
  lazymatch type of HS with
  | st_ok_pi ?sg ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let r0 := eval vm_compute in (nth i (ss_mem ssx) got_regionP) in
      assert (HR : region_ok sg Ex (ms_mem (restrict Hh msx)) r0)
        by (let HS' := fresh in pose proof HS as HS'; unfold st_ok_pi in HS';
            eapply (can_region_nth Ex _ (restrict Hh msx) i r0 HS'); vm_compute; reflexivity)
  end; cbn [ms_mem restrict] in HR.
Ltac pf_in := cbn [In]; repeat (first [left; reflexivity | right]).
(* The awr obligation's regions, computed. *)
Ltac pf_awr_rs :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
(* A run from a state with no region keeps the memory: functional extensionality over the run's frame. *)
Ltac pf_mem_eq HF EM :=
  lazymatch type of HF with frame_of _ _ ?m ?m' =>
    assert (EM : m' = m)
      by (apply functional_extensionality; intros x; apply HF;
          let r := fresh "r" in let Hr := fresh "Hr" in intros (r & Hr & _); cbn in Hr; destruct Hr) end.

Section pf. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).

Definition pf_E (regs : bvmap 5 word) : env := Eimg (PI := PI_transport) (Ereg regs []).
Definition pf_Ej (regs : bvmap 5 word) (cmd : Z) : env := Eimg (PI := PI_transport) (Ereg regs [w64 cmd]).

(* ------------------------------------------------------------------ *)
(* 4. The entry states                                                 *)
(* ------------------------------------------------------------------ *)

Lemma pf_entry0 : forall (W : world segs) regs mem pc,
  st_ok_pi segs VAL (pf_E regs) (pf_ss0 pc)
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + pc)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem pc. rewrite restrict_mkst_fx. unfold pf_ss0.
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. exact I.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. repeat split; exact I.
Qed.

(* g_s's bytes [s + 128, s + 136) are addressable at every AR state: whole granules of the record's zero shadow. *)
Lemma pf_ra_gs : forall ly S (W : world segs) mem md,
  trans_onann_cells B -> @AR rc segs B ly S W mem md ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF (ONANN_S + 128) 8.
Proof.
  intros ly S W mem md HZ HAR x Hx.
  exists 0. split; [|left; reflexivity].
  pose proof (Z.div_mod x 8 ltac:(lia)) as D8. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as M8.
  assert (Hx8 : ONANN_S <= 8 * (x / 8) /\ 8 * (x / 8) + 8 <= ONANN_S + TW.SZ_g_s)
    by (unfold ONANN_S, TA_g_s, TW.SZ_g_s in *; lia).
  assert (Hz := decode_zshadow_rd B ly S W mem md ONANN_S (ONANN_S + TW.SZ_g_s) (8 * (x / 8)) HAR
    ltac:(rewrite Z.mul_comm; apply Z_mod_mult) (proj1 Hx8) (proj2 Hx8) HZ).
  unfold shadow_of_addr.
  replace (SHADOW_OFF + x / 8) with (FCells.shadow_addr (8 * (x / 8))); [exact Hz|].
  unfold FCells.shadow_addr, FCells.ASAN_K, SHADOW_OFF. rewrite Z.mul_comm, Z.div_mul by lia. lia.
Qed.

(* Run N's state at +0x258: g_s.personality's region, s = ONANN_S, the shadow base; its shadow entry. *)
Lemma pf_entry_n : forall ly S (W : world segs) regs mem md,
  trans_onann_cells B -> @AR rc segs B ly S W mem md ->
  YK11.getr regs 20 = w64 ONANN_S -> YK11.getr regs 24 = w64 SHADOW_OFF ->
  st_ok_pi segs VAL (pf_E regs) pf_ss_n
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + ONANN_PFN)) mem (YK11.seg_rom segs))) /\
  sh_ok segs PF_Bx PF_SH_N (pf_E regs) (mrestrict (w_H W) mem).
Proof.
  intros ly S W regs mem md HZ HAR R20 R24.
  assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (pf_E regs) n = YK11.getr regs r)
    by (intros n r Hn; unfold pf_E; apply can_ew_Eimg_Ereg_nat; exact Hn).
  assert (U20 : bv_unsigned (ew (pf_E regs) 20) = ONANN_S)
    by (rewrite (EE 20%nat 20%bv eq_refl), R20; apply unsigned_lit_small; unfold ONANN_S, TA_g_s; lia).
  assert (U24 : bv_unsigned (ew (pf_E regs) 24) = SHADOW_OFF)
    by (rewrite (EE 24%nat 24%bv eq_refl), R24; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  split.
  - rewrite restrict_mkst_fx. unfold pf_ss_n.
    apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
    + apply regs_ok_Eimg_Ereg.
    + vm_compute. reflexivity.
    + apply Forall_cons; [|apply Forall_nil]. unfold pf_rg_gs, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U20.
      split; [unfold ONANN_S, TA_g_s; lia|]. split; [unfold ONANN_S, TA_g_s; lia|]. split; [|constructor].
      intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (ONANN_S + o) G_HARNESS_rw).
      apply pf_inG. unfold TW.SZ_g_s. lia.
    + apply pairwise_disjoint_of_extents. unfold pf_rg_gs, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. cbn [zpairwise_disjoint zall_disjoint]. repeat split.
    + unfold pf_facts_n, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
      unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U20, U24.
      change (2 ^ 6) with 64. rewrite !Z.pow_0_r, !Z.mod_1_r.
      repeat match goal with |- _ /\ _ => split end; try exact I; unfold ONANN_S, TA_g_s, SHADOW_OFF;
      first [lia | reflexivity].
  - pose proof (pf_ra_gs ly S W mem md HZ HAR) as HRA.
    assert (UB : U (pf_E regs) PF_Bx = SHADOW_OFF).
    { unfold U, PF_Bx. cbn [sv_denot]. rewrite U24, Z.add_0_r. apply unsigned_lit_small. unfold SHADOW_OFF; lia. }
    unfold sh_ok, PF_SH_N. constructor; [|constructor].
    apply (shent_ok_of_range segs (w_H W) mem _ PF_Bx 20 (ONANN_S + 128) 8 ONANN_S 128 136 HRA UB).
    + unfold U. cbn [sv_denot]. rewrite U20, Z.add_0_r. apply unsigned_lit_small. unfold ONANN_S, TA_g_s; lia.
    + lia.
    + lia.
    + intros x Hx. cbn [Z.min Z.max] in Hx. unfold ONANN_S, TA_g_s, SHADOW_OFF in *. lia.
Qed.

(* Run D's state at +0x270: the spill slots, the byte at f + 30 (cmd, atom 32), the shadow entry of f + 30. *)
Lemma pf_entry_j : forall (W : world segs) regs mem (sp1 fp cmd : Z),
  YK11.getr regs 9 = w64 sp1 -> YK11.getr regs 22 = w64 fp -> YK11.getr regs 24 = w64 SHADOW_OFF ->
  2 ^ 46 <= sp1 -> sp1 + 64 <= 2 ^ 47 -> sp1 mod 32 = 0 ->
  4096 <= fp -> fp + 64 <= 2 ^ 47 - 2 ^ 23 -> fp mod 8 = 0 -> in_app fp 64 -> fp + 64 <= sp1 ->
  (forall a, sp1 <= a < sp1 + 64 -> apresent (w_H W) mem a) ->
  aview segs (w_H W) mem (fp + 30) = Some cmd ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF (fp + 30) 1 ->
  st_ok_pi segs VAL (pf_Ej regs cmd) pf_ss_j
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + ONANN_PFJ)) mem (YK11.seg_rom segs))) /\
  sh_ok segs PF_Bx PF_SH_J (pf_Ej regs cmd) (mrestrict (w_H W) mem).
Proof.
  intros W regs mem sp1 fp cmd R9 R22 R24 Hs1 Hs2 Hs32 Hf1 Hf2 Hf8 Hfapp Hfsp Hpres Hcmd HRA.
  pose proof (pf_aview_byte _ _ _ _ Hcmd) as Rc.
  assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (pf_Ej regs cmd) n = YK11.getr regs r)
    by (intros n r Hn; unfold pf_Ej; apply can_ew_Eimg_Ereg_nat; exact Hn).
  assert (E32 : ew (pf_Ej regs cmd) 32 = w64 cmd)
    by (unfold pf_Ej; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (U9 : bv_unsigned (ew (pf_Ej regs cmd) 9) = sp1)
    by (rewrite (EE 9%nat 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
  assert (U22 : bv_unsigned (ew (pf_Ej regs cmd) 22) = fp)
    by (rewrite (EE 22%nat 22%bv eq_refl), R22; apply unsigned_lit_small; lia).
  assert (U24 : bv_unsigned (ew (pf_Ej regs cmd) 24) = SHADOW_OFF)
    by (rewrite (EE 24%nat 24%bv eq_refl), R24; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (U32 : bv_unsigned (ew (pf_Ej regs cmd) 32) = cmd)
    by (rewrite E32; unfold w64; apply unsigned_lit_small; lia).
  split.
  - rewrite restrict_mkst_fx. unfold pf_ss_j.
    apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
    + apply regs_ok_Eimg_Ereg.
    + vm_compute. reflexivity.
    + apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold region_ok.
      * unfold pf_rg_stk. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite U9. split; [lia|]. split; [lia|]. split; [|constructor].
        intros o Ho. apply (apresent_writable segs). apply Hpres. lia.
      * unfold pf_rg_f. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite U22. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val segs _ _ fp 30 1 (SOff 32 0) cmd);
          [cbn [sv_denot]; rewrite E32, Z.add_0_r; unfold w64; rewrite unsigned_lit_small by lia; reflexivity
          | cbn; lia | cbn; lia |].
        exact (pf_vm1 _ _ _ _ Hcmd).
    + apply pairwise_disjoint_of_extents. unfold pf_rg_stk, pf_rg_f, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U22.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hfapp.
      repeat split; first [exact I | lia].
    + unfold pf_facts_j, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
      unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U9, U22, U24, U32.
      change (2 ^ 5) with 32. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
      repeat match goal with |- _ /\ _ => split end; try exact I; unfold SHADOW_OFF; first [lia | reflexivity].
  - assert (UB : U (pf_Ej regs cmd) PF_Bx = SHADOW_OFF).
    { unfold U, PF_Bx. cbn [sv_denot]. rewrite U24, Z.add_0_r. apply unsigned_lit_small. unfold SHADOW_OFF; lia. }
    unfold sh_ok, PF_SH_J. constructor; [|constructor].
    apply (shent_ok_of_range segs (w_H W) mem _ PF_Bx 22 (fp + 30) 1 fp 30 31 HRA UB).
    + unfold U. cbn [sv_denot]. rewrite U22, Z.add_0_r. apply unsigned_lit_small. lia.
    + lia.
    + lia.
    + intros x Hx. cbn [Z.min Z.max] in Hx. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hfapp.
      unfold SHADOW_OFF. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 5. What the cut carries, moved                                      *)
(* ------------------------------------------------------------------ *)

(* onann_cur at a later model of the same memory. *)
Lemma pf_cur_md : forall {STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k} {regs : bvmap 5 word} {Bw b : list byte}
    {pos F ly2 S2} {W2 : world segs} {mem2 md2 md3},
  onann_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw b pos F ly2 S2 W2 mem2 md2 0 ->
  ajournal_gx TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 ((ONANN_CID, pos) :: own) ly2 S2 W2 mem2 md3 (k + 0) ->
  onann_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw b pos F ly2 S2 W2 mem2 md3 0.
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw b pos F ly2 S2 W2 mem2 md2 md3
    (_ & He & Hfr & Hperm & HlyF & Hmo & HK & Hsv & Hfl) HJ.
  exact (conj HJ (conj He (conj Hfr (conj Hperm (conj HlyF (conj Hmo (conj HK (conj Hsv Hfl)))))))).
Qed.

(* The arithmetic of the caller's facts. *)
Lemma pf_basics : forall {STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k} {regs : bvmap 5 word} {fp buf now : Z}
    {b fj : list byte} {TF : option TI.tframe} {Bw Bw' : list byte} {pos sp1 F : Z},
  onann_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F ->
  alloc_ceiling <= sp0 - STK /\ sp0 - STK <= spZ regs - ONANN_STK /\ spZ regs <= sp0 /\ sp0 <= 2 ^ 47 /\
  spZ regs - 208 <= sp1 <= spZ regs - 192 /\ sp1 mod 32 = 0 /\
  208 + PFROM_STK <= ONANN_STK /\ 0 <= PFROM_STK /\ 2 ^ 46 <= alloc_ceiling /\
  (forall a, sp0 - STK <= a < sp0 -> apresent (w_H W) memc a).
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F HFIX.
  pose proof HFIX as (HJ0 & Hret & Hra & Hgp & Htp & H10 & H11 & H12 & Hsp16 & Hlo & Hhi & Hnow & HDF & Htw0 & Hgf &
    Hm & HTF & Htfg & Hrom & Hap & Hri & Hcnt & Hcnt2 & Hev & Esp1 & EF & HF0 & HF64 & HFc & HFapp).
  pose proof HJ0 as (HSTK & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
  pose proof HJi as (_ & Hlyle & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & Hstk & _).
  pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (HSK : 208 + PFROM_STK <= ONANN_STK) by (vm_compute; congruence).
  assert (HPF : 0 <= PFROM_STK) by (vm_compute; congruence).
  assert (Hsp0 : 0 <= spZ regs) by (unfold spZ; pose proof (bv_unsigned_in_range 64 (YK11.getr regs 2)); lia).
  destruct (pf_sp1 (spZ regs) sp1 Hsp0 Hsp16 Esp1) as [Hs1 Hs2].
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ Hpres0))))))))); lia.
Qed.

(* onann_cur moved over a run that changes only the spill slots [sp1, sp1 + 64) and g_s.personality. *)
Lemma pf_cur_step : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
    (fp buf now : Z) (b fj : list byte) (TF : option TI.tframe) (Bw Bw' : list byte) (pos sp1 F : Z)
    ly2 S2 (W2 : world segs) mem2 md2 mem3 md3 (Zs : Z -> Prop),
  onann_laws B MT ->
  onann_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F ->
  onann_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw b pos F ly2 S2 W2 mem2 md2 0 ->
  ajournal_gx TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 ((ONANN_CID, pos) :: own) ly2 S2 W2 mem3 md3 (k + 0) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview segs (w_H W2) mem3 a = aview segs (w_H W2) mem2 a) ->
  (forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) mem3 a) ->
  (forall a, Zs a -> (sp1 <= a < sp1 + 64) \/ (ONANN_S + 128 <= a < ONANN_S + 136)) ->
  onann_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw b pos F ly2 S2 W2 mem3 md3 0 /\
  (forall a, F <= a < F + 1024 \/ SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 128 ->
     aview segs (w_H W2) mem3 a = aview segs (w_H W2) mem2 a).
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F ly2 S2 W2 mem2
    md2 mem3 md3 Zs LAWS0 HFIX HCUR HJ3 Hkp Hgr HZ.
  pose proof LAWS0 as (HSM & HCELLS & HOC & HGU & HGE0 & HRU & HRE & LAWS & MTL & MTF & SMP & ASF & FFL & HGX & HGE).
  pose proof HFIX as (HJ0 & Hret & Hra & Hgp & Htp & H10 & H11 & H12 & Hsp16 & Hlo & Hhi & Hnow & HDF & Htw0 & Hgf &
    Hm & HTF & Htfg & Hrom & Hap & Hri & Hcnt & Hcnt2 & Hev & Esp1 & EF & HF0 & HF64 & HFc & HFapp).
  pose proof HCUR as (HJ2 & He0 & Hfrs & Hperm & HlyF & Hmo & HK & Hsaved & HFLw).
  destruct (pf_basics HFIX) as (Bc & Bl & Bh & B47 & Bs1 & Bs32 & BSK & BPF & B46 & Bpres).
  pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0) as HARc.
  pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HAR2.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  unfold ONANN_FBYTES in HFc, HFapp, HFLw.
  assert (Hbl : forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly2 S2))
    by (intros bm Hbm; exact (Permutation_in _ (Permutation_sym Hperm) Hbm)).
  assert (EF2 : frame_addr ly2 ONANN_CID pos = F) by (rewrite EF; unfold frame_addr; rewrite HlyF; reflexivity).
  assert (Hin2 : In (ONANN_CID, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
  (* a frame byte is no byte of g_s *)
  assert (NGF : forall a, F <= a < F + 1024 -> ~ (ONANN_S + 128 <= a < ONANN_S + 136)).
  { intros a Ha Hg. apply (frm_img segs B LAWS ly2 S2 W2 mem2 md2 ONANN_CID pos a HAR2 Hin2);
      [rewrite EF2; change (fs_frame_bytes ONANN_CID) with 1024; lia|].
    apply trans_g_img. apply pf_inG. unfold TW.SZ_g_s. lia. }
  assert (NZF : forall a, F <= a < F + 1024 \/ SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 128 -> ~ Zs a).
  { intros a Ha Hz. pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)) as HF8.
    assert (HF8u : F / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia).
    destruct (HZ a Hz) as [X | X]; destruct Ha as [Ha | Ha].
    - lia.
    - unfold SHADOW_OFF in *. lia.
    - exact (NGF a Ha X).
    - unfold SHADOW_OFF, ONANN_S, TA_g_s in *. lia. }
  split.
  2: { intros a Ha. apply Hkp; [|exact (NZF a Ha)].
       pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)) as HF8.
       assert (HF8u : F / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia).
       destruct Ha as [Ha | Ha]; unfold SHADOW_OFF in *; lia. }
  assert (KP3 : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W2 mem3 (spZ regs - ONANN_STK) (spZ regs)
    (onann_wr Bw b)).
  { apply (dk_kept_nfz_gw segs B LAWS transport_segs_low TG.G_HARNESS lyc Sc ly2 S2 W memc mdc W2 mem2 md2 mem2 mem3
      (spZ regs - ONANN_STK) (spZ regs) ONANN_CID pos F (flag_addr lyc ONANN_CID pos) (onann_wr Bw b) Zs
      HGX HARc HAR2 Hfrs Hbl HlyF EF eq_refl FFL); [lia | lia | | exact HK | exact Hkp | exact Hgr].
    intros a Ha. destruct (HZ a Ha) as [X | X]; [left; lia | right; right; apply pf_inG; unfold TW.SZ_g_s; lia]. }
  assert (HSo : forall o, In o ONANN_SAVED -> 8 <= fst o <= 104).
  { intros o Ho. unfold ONANN_SAVED in Ho. cbn [In] in Ho.
    repeat (destruct Ho as [<- | Ho]; [cbn [fst]; lia|]). destruct Ho. }
  refine (conj HJ3 (conj He0 (conj Hfrs (conj Hperm (conj HlyF (conj Hmo (conj KP3 (conj _ _)))))))).
  - rewrite Forall_forall in Hsaved |- *. intros o Ho. rewrite <- (Hsaved o Ho).
    pose proof (HSo o Ho) as Hob. apply rdword_ext. intros i Hi. apply Hkp; [lia|].
    intros Hz. destruct (HZ _ Hz) as [X | X]; unfold ONANN_S, TA_g_s in X; lia.
  - unfold ONANN_FBYTES. rewrite <- HFLw. apply rdword_ext. intros i Hi. apply Hkp; [lia|]. apply NZF. left. lia.
Qed.

(* onann_cur moved across personality_from_name: its acall_kept at the call state (ly2, S2), whose frames are the
   own frame on top of the entry's (TransportGCg.v dk_kept_trans_nf_g with the own frame's separation). *)
Lemma pf_cur_call : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
    (fp buf now : Z) (b fj : list byte) (TF : option TI.tframe) (Bw Bw' : list byte) (pos sp1 F : Z)
    ly2 S2 (W2 : world segs) mem2 md2 ly3 S3 (W3 : world segs) mem3 md3,
  onann_laws B MT ->
  onann_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F ->
  onann_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw b pos F ly2 S2 W2 mem2 md2 0 ->
  ajournal_gx TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 ((ONANN_CID, pos) :: own) ly3 S3 W3 mem3 md3 (k + 0) ->
  frames S3 = frames S2 -> Permutation (ablocks B ly3 S3) (ablocks B ly2 S2) -> mo_le MT S2 S3 0 ->
  acall_kept_g segs B TG.G_HARNESS ly2 S2 W2 mem2 W3 mem3 (sp1 - PFROM_STK) sp1 (fun _ => False) ->
  onann_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw b pos F ly3 S3 W3 mem3 md3 0 /\
  (forall a, F <= a < F + 1024 \/ SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 128 ->
     aview segs (w_H W3) mem3 a = aview segs (w_H W2) mem2 a).
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F ly2 S2 W2 mem2
    md2 ly3 S3 W3 mem3 md3 LAWS0 HFIX HCUR HJ3 Hfr3 Hperm3 Hmo3 KC.
  pose proof LAWS0 as (HSM & HCELLS & HOC & HGU & HGE0 & HRU & HRE & LAWS & MTL & MTF & SMP & ASF & FFL & HGX & HGE).
  pose proof HFIX as (HJ0 & Hret & Hra & Hgp & Htp & H10 & H11 & H12 & Hsp16 & Hlo & Hhi & Hnow & HDF & Htw0 & Hgf &
    Hm & HTF & Htfg & Hrom & Hap & Hri & Hcnt & Hcnt2 & Hev & Esp1 & EF & HF0 & HF64 & HFc & HFapp).
  pose proof HCUR as (HJ2 & He0 & Hfrs & Hperm & HlyF & Hmo & HK & Hsaved & HFLw).
  destruct (pf_basics HFIX) as (Bc & Bl & Bh & B47 & Bs1 & Bs32 & BSK & BPF & B46 & Bpres).
  pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HAR2.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  unfold ONANN_FBYTES in HFc, HFapp, HFLw.
  pose proof HJ0 as (_ & _ & (memS0 & HJi0 & _) & _). rewrite !Z.add_0_r in HJi0.
  pose proof HJi0 as (_ & Hlyle0 & _). pose proof Hlyle0 as (_ & _ & _ & _ & _ & ELF0 & _).
  pose proof HJ3 as (_ & _ & (memS3 & HJi3 & _) & _). rewrite !Z.add_0_r in HJi3.
  pose proof HJi3 as (_ & Hlyle3 & _). pose proof Hlyle3 as (_ & _ & _ & _ & _ & ELF3 & _).
  clear HJi0 HJi3 memS0 memS3.
  assert (ELF3c : ly_F ly3 = ly_F lyc) by (rewrite ELF3, ELF0; reflexivity).
  assert (Hbl : forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly2 S2))
    by (intros bm Hbm; exact (Permutation_in _ (Permutation_sym Hperm) Hbm)).
  assert (EF2 : frame_addr ly2 ONANN_CID pos = F) by (rewrite EF; unfold frame_addr; rewrite HlyF; reflexivity).
  assert (Hin2 : In (ONANN_CID, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
  destruct (dkg_nf_sep_gw segs B LAWS transport_segs_low lyc Sc ly2 S2 W2 mem2 md2 ONANN_CID pos F
    (flag_addr lyc ONANN_CID pos) HAR2 Hfrs Hbl HlyF EF eq_refl FFL) as (N1 & N2 & N3 & N4).
  pose proof KC as (L1 & _ & _ & L4 & _).
  (* the own frame's bytes and shadow bytes are the callee's frame clause's *)
  assert (KF : forall a, F <= a < F + 1024 \/ SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 128 ->
     aview segs (w_H W3) mem3 a = aview segs (w_H W2) mem2 a).
  { intros a Ha. apply (L4 ONANN_CID pos a Hin2); [|intros X; exact X].
    unfold frame_rng, in_zr. cbn [fst snd]. rewrite EF2. unfold shadow_addr.
    change (fs_frame_bytes ONANN_CID) with 1024. change (1024 / 8) with 128.
    destruct Ha as [Ha | Ha]; [left | right]; lia. }
  split; [|exact KF].
  assert (KP3 : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W3 mem3 (spZ regs - ONANN_STK) (spZ regs)
    (onann_wr Bw b)).
  { apply (dk_kept_trans_nf_g segs B TG.G_HARNESS lyc Sc ly2 S2 W memc W2 mem2 W3 mem3
      (spZ regs - ONANN_STK) (spZ regs) (sp1 - PFROM_STK) sp1 (onann_wr Bw b) (fun _ => False)
      (dkg_nf ONANN_CID F (flag_addr lyc ONANN_CID pos))).
    - lia.
    - lia.
    - intros c p. unfold frame_addr. rewrite HlyF. reflexivity.
    - intros f Hf. rewrite Hfrs. right. exact Hf.
    - exact Hbl.
    - exact N1.
    - exact N3.
    - exact HK.
    - exact KC.
    - lia.
    - lia.
    - intros a []. }
  assert (HSo : forall o, In o ONANN_SAVED -> 8 <= fst o <= 104).
  { intros o Ho. unfold ONANN_SAVED in Ho. cbn [In] in Ho.
    repeat (destruct Ho as [<- | Ho]; [cbn [fst]; lia|]). destruct Ho. }
  refine (conj HJ3 (conj He0 (conj _ (conj _ (conj ELF3c (conj _ (conj KP3 (conj _ _)))))))).
  - rewrite Hfr3. exact Hfrs.
  - exact (Permutation_trans Hperm3 Hperm).
  - exact (mo_le_trans MT MTL _ _ _ _ _ Hmo Hmo3).
  - rewrite Forall_forall in Hsaved |- *. intros o Ho. rewrite <- (Hsaved o Ho).
    pose proof (HSo o Ho) as Hob. apply rdword_ext. intros i Hi. apply L1; lia.
  - unfold ONANN_FBYTES. rewrite <- HFLw. apply rdword_ext. intros i Hi. apply KF. left. lia.
Qed.

(* a's 40 bytes and its shadow bytes moved to a later memory that keeps them. *)
Lemma pf_aok_move : forall (W2 W3 : world segs) mem2 mem3 F buf b,
  onann_a_ok W2 mem2 F buf b ->
  (forall a, F + ONANN_A <= a < F + ONANN_A + 40 -> aview segs (w_H W3) mem3 a = aview segs (w_H W2) mem2 a) ->
  (forall i, 32 <= i < 37 ->
     aview segs (w_H W3) mem3 (SHADOW_OFF + F / 8 + i) = aview segs (w_H W2) mem2 (SHADOW_OFF + F / 8 + i)) ->
  onann_a_ok W3 mem3 F buf b.
Proof.
  intros W2 W3 mem2 mem3 F buf b (A1 & A2 & A3 & A4 & A5) K Ks.
  pose proof (pf_ann_len (skipn 15 (DSpec.fr_body b))) as L1.
  pose proof (pf_ann_len (skipn 24 (DSpec.fr_body b))) as L2.
  split; [|split; [|split; [|split]]].
  - eapply garr8_frame; [exact A1|]. intros a Ha. rewrite length_map in Ha.
    apply (mbyte_of_aview segs). apply K. lia.
  - eapply garr8_frame; [exact A2|]. intros a Ha. rewrite length_map in Ha.
    apply (mbyte_of_aview segs). apply K. lia.
  - rewrite <- A3. apply rdword_ext. intros i Hi. apply K. lia.
  - rewrite <- A4. apply rdword_ext. intros i Hi. apply K. lia.
  - intros i Hi. rewrite Ks by exact Hi. exact (A5 i Hi).
Qed.

(* ------------------------------------------------------------------ *)
(* 6. The byte at f + 30 at a cut state                                *)
(* ------------------------------------------------------------------ *)

(* At a state onann_cur carries: the byte at f + 30 is cmd and addressable (on_announce_seg_kitf.v onann_f30, the
   call's written range onann_wr in G: onann_wr_G), f lies in a frame of the entry. *)
Lemma pf_f30 : forall {STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k} {regs : bvmap 5 word}
    {fp buf now : Z} {b fj : list byte} {TF : option TI.tframe} {Bw Bw' : list byte} {pos sp1 F : Z}
    {ly2 S2} {W2 : world segs} {mem2 md2},
  onann_laws B MT ->
  onann_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F ->
  onann_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw b pos F ly2 S2 W2 mem2 md2 0 ->
  aview segs (w_H W2) mem2 (fp + 30) = Some (DSpec.fr_cmd b) /\
  range_addressable (aview segs (w_H W2) mem2) SHADOW_OFF (fp + 30) 1 /\
  4096 <= fp /\ fp + 64 <= alloc_ceiling /\ fp mod 8 = 0 /\ in_app fp 64.
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F ly2 S2 W2 mem2
    md2 LAWS0 HFIX HCUR.
  pose proof LAWS0 as (HSM & HCELLS & HOC & HGU & HGE0 & HRU & HRE & LAWS & MTL & MTF & SMP & ASF & FFL & HGX & HGE).
  pose proof HFIX as (HJ0 & Hret & Hra & Hgp & Htp & H10 & H11 & H12 & Hsp16 & Hlo & Hhi & Hnow & HDF & _).
  pose proof HCUR as (HJ2 & He0 & Hfrs & Hperm & HlyF & Hmo & HK & _).
  pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0) as HARc.
  destruct (onann_f30 B LAWS lyc Sc W memc mdc W2 mem2 _ _ _ regs ONANN_STK fp buf b fj HARc HK (onann_wr_G Bw b) HDF)
    as (_ & Hrd2 & HC & _).
  pose proof HDF as (_ & _ & _ & _ & _ & _ & Hfp0 & Hfp8 & _ & _ & HF & _ & _).
  destruct HF as (cid & p & Hin & Fa1 & Fa2). unfold FRAME_F_SIZE in Fa2.
  destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid p HARc Hin) as (Fb1 & Fb2 & Fb3).
  pose proof Hrd2 as (_ & HRA & _).
  split; [exact HC|]. split; [intros x Hx; apply HRA; lia|].
  split; [lia|]. split; [lia|]. split; [exact Hfp8|].
  exact (in_app_sub _ _ fp 64 Fb3 Fa1 ltac:(lia) Fa2).
Qed.

(* ------------------------------------------------------------------ *)
(* 7. From the join (+0x270) to the two cuts                           *)
(* ------------------------------------------------------------------ *)

Lemma pf_tail : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
    (fp buf now : Z) (b fj : list byte) (TF : option TI.tframe) (Bw Bw' : list byte) (pos sp1 F : Z)
    ly3 S3 (W3 : world segs) memJ mdJ (regsJ : bvmap 5 word),
  onann_laws B MT -> onann_callees B MT -> onann_fm_at B MT -> onann_dn_at B MT ->
  onann_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F ->
  onann_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw b pos F ly3 S3 W3 memJ mdJ 0 ->
  tw_at TMAP_A (aview segs (w_H W3) memJ) (onann_w1 timg_A Bw b) ->
  onann_ign b = false ->
  onann_a_ok W3 memJ F buf b ->
  onann_regs_base regs regsJ sp1 F ->
  YK11.getr regsJ 20 = w64 ONANN_S -> YK11.getr regsJ 21 = w64 (F + ONANN_A) -> YK11.getr regsJ 22 = w64 fp ->
  YK11.getr regsJ 23 = w64 F -> YK11.getr regsJ 24 = w64 SHADOW_OFF ->
  YK11.getr regsJ 25 = w64 (onann_pv timg_A b) -> YK11.getr regsJ 26 = w64 now ->
  SRr segs W3 (mkCfg (@YK11.mkst fx regsJ (Z_to_bv 64 (BASE + ONANN_PFJ)) memJ (YK11.seg_rom segs)) mdJ)
    (@transport_onann_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' b).
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F ly3 S3 W3 memJ
    mdJ regsJ LAWS0 CALLEES FM DN HFIX HCUR HTW HIGN HAOK HRB R20 R21 R22 R23 R24 R25 R26.
  pose proof LAWS0 as (HSM & HCELLS & HOC & HGU & HGE0 & HRU & HRE & LAWS & MTL & MTF & SMP & ASF & FFL & HGX & HGE).
  pose proof HFIX as (HJ0 & Hret & Hra & Hgp & Htp & H10 & H11 & H12 & Hsp16 & Hlo & Hhi & Hnow & HDF & Htw0 & Hgf &
    Hm & HTF & Htfg & Hrom & Hap & Hri & Hcnt & Hcnt2 & Hev & Esp1 & EF & HF0 & HF64 & HFc & HFapp).
  pose proof HRB as (R2 & R3 & R4 & R8 & R9 & R18 & R19).
  destruct (pf_basics HFIX) as (Bc & Bl & Bh & B47 & Bs1 & Bs32 & BSK & BPF & B46 & Bpres).
  destruct (pf_f30 LAWS0 HFIX HCUR) as (HFC & HFR & Hf0 & Hfc & Hf8 & Hfapp).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  unfold ONANN_FBYTES in HFc, HFapp.
  pose proof (pf_aview_byte _ _ _ _ HFC) as Hcmd.
  pose proof HCUR as (HJ & _).
  pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR3.
  assert (Hpres : forall a, sp1 <= a < sp1 + 64 -> apresent (w_H W3) memJ a).
  { intros a Ha. pose proof HJ as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
    pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hp & _). apply Hp. lia. }
  (* ---- run D, +0x270 .. +0x2a4 ---- *)
  destruct (pf_entry_j W3 regsJ memJ sp1 fp (DSpec.fr_cmd b) R9 R22 R24 ltac:(lia) ltac:(lia) Bs32 Hf0 ltac:(lia)
    Hf8 Hfapp ltac:(lia) Hpres HFC HFR) as [HS SHOK].
  set (E0 := pf_Ej regsJ (DSpec.fr_cmd b)) in HS, SHOK.
  assert (HEI : img_env VAL A_LIM E0) by (unfold E0, pf_Ej; apply Eimg_env).
  assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E0 n = YK11.getr regsJ r)
    by (intros n r Hn; unfold E0, pf_Ej; apply can_ew_Eimg_Ereg_nat; exact Hn).
  assert (E32 : ew E0 32 = w64 (DSpec.fr_cmd b))
    by (unfold E0, pf_Ej; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsJ _ 0)).
  assert (U9 : bv_unsigned (ew E0 9) = sp1)
    by (rewrite (EE 9%nat 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
  pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
    as RUN.
  pose proof (@paj_run_to_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX
    0 []) as RUNTO.
  pose proof (paj_branch (fx := fx) (PI := PI_transport)) as BR.
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { pf_awr_rs.
    apply awr_ok_x_cons.
    - intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U9 in Ha.
      left. split; [unfold awr_byte; left; lia | lia].
    - apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia|].
      apply awr_ok_x_nil. }
  set (mdB := with_vm_backing (m_vm_lazy mdJ) mat mdJ) in *. clearbody mdB. clear mat.
  rename ms into msB.
  lazymatch type of HS with st_ok_pi _ _ ?EF _ _ => set (EB := EF) in * end.
  assert (EBlo : forall n, (n < 1024)%nat -> ew EB n = ew E0 n)
    by (intros n Hn; unfold EB; rewrite ?ew_ewset_other by lia; reflexivity).
  (* run D wrote the spill slots only *)
  assert (KD : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 <= a < sp1 + 64) ->
    aview segs (w_H W3) (ms_mem msB) a = aview segs (w_H W3) memJ a).
  { intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ (fun x => sp1 <= x < sp1 + 64) HFr); [| exact Ha | exact Hn].
    intros b0 wlo whi x Hin Hx.
    lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
    cbn [In] in Hin.
    repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; rewrite ?U9 in Hx; lia |]).
    destruct Hin. }
  assert (GD : forall a, apresent (w_H W3) memJ a -> apresent (w_H W3) (ms_mem msB) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
  clear HF HFr HG.
  (* the slots' values, from the stack region's chunks *)
  pf_region HS 0%nat HR.
  assert (U9B : bv_unsigned (ew EB 9) = sp1) by (rewrite EBlo by lia; exact U9).
  assert (D21 : sv_denot EB (SOff 21 0) = Z_to_bv 64 (F + ONANN_A)).
  { cbn [sv_denot]. rewrite (EBlo 21%nat ltac:(lia)), (EE 21%nat 21%bv eq_refl), R21. unfold w64.
    rewrite unsigned_lit_small by (unfold ONANN_A; lia). rewrite Z.add_0_r. reflexivity. }
  assert (D23 : sv_denot EB (SOff 23 0) = Z_to_bv 64 F).
  { cbn [sv_denot]. rewrite (EBlo 23%nat ltac:(lia)), (EE 23%nat 23%bv eq_refl), R23. unfold w64.
    rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity. }
  assert (D26 : sv_denot EB (SOff 26 0) = Z_to_bv 64 now).
  { cbn [sv_denot]. rewrite (EBlo 26%nat ltac:(lia)), (EE 26%nat 26%bv eq_refl), R26. unfold w64.
    rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity. }
  assert (V56 : val_mem segs (mrestrict (w_H W3) (ms_mem msB)) (sp1 + 56) 8 (F + ONANN_A)).
  { exact (can_field_of_region EB _ 9 sp1 _ 0 64 0 64 56 8%N (SOff 21 0) (F + ONANN_A) HR U9B ltac:(pf_in) D21
      ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold ONANN_A; lia) ltac:(cbn; lia)). }
  assert (V40 : val_mem segs (mrestrict (w_H W3) (ms_mem msB)) (sp1 + 40) 8 F).
  { exact (can_field_of_region EB _ 9 sp1 _ 0 64 0 64 40 8%N (SOff 23 0) F HR U9B ltac:(pf_in) D23
      ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(cbn; lia)). }
  assert (V0 : val_mem segs (mrestrict (w_H W3) (ms_mem msB)) (sp1 + 0) 8 now).
  { exact (can_field_of_region EB _ 9 sp1 _ 0 64 0 64 0 8%N (SOff 26 0) now HR U9B ltac:(pf_in) D26
      ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(cbn; lia)). }
  assert (V32 : val_mem segs (mrestrict (w_H W3) (ms_mem msB)) (sp1 + 32) 8 (SHADOW_OFF + (fp + 30) / 8)).
  { eapply (can_field_of_region EB _ 9 sp1 _ 0 64 0 64 32 8%N _ (SHADOW_OFF + (fp + 30) / 8) HR U9B).
    - pf_in.
    - apply (pf_denot_shadow EB 22 24 fp 30 SHADOW_OFF).
      + rewrite (EBlo 22%nat ltac:(lia)), (EE 22%nat 22%bv eq_refl), R22. reflexivity.
      + rewrite (EBlo 24%nat ltac:(lia)), (EE 24%nat 24%bv eq_refl), R24. reflexivity.
      + lia.
      + lia.
      + unfold SHADOW_OFF; lia.
      + assert ((fp + 30) / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia). unfold SHADOW_OFF in *. lia.
    - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). pose proof (Z.div_pos (fp + 30) 8 ltac:(lia) ltac:(lia)).
      assert ((fp + 30) / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia). unfold SHADOW_OFF in *. lia.
    - cbn; lia. }
  clear HR.
  (* the registers at +0x2a4 *)
  pf_kreg HS EBlo EE (Z_to_bv 5 2) 2%nat (Z_to_bv 5 2) R2 Q2. pf_kreg HS EBlo EE (Z_to_bv 5 3) 3%nat (Z_to_bv 5 3) R3 Q3.
  pf_kreg HS EBlo EE (Z_to_bv 5 4) 4%nat (Z_to_bv 5 4) R4 Q4. pf_kreg HS EBlo EE (Z_to_bv 5 8) 8%nat (Z_to_bv 5 8) R8 Q8.
  pf_kreg HS EBlo EE (Z_to_bv 5 9) 9%nat (Z_to_bv 5 9) R9 Q9.
  pf_kreg HS EBlo EE (Z_to_bv 5 18) 18%nat (Z_to_bv 5 18) R18 Q18.
  pf_kreg HS EBlo EE (Z_to_bv 5 19) 19%nat (Z_to_bv 5 19) R19 Q19.
  pf_kreg HS EBlo EE (Z_to_bv 5 20) 20%nat (Z_to_bv 5 20) R20 Q20.
  pf_kreg HS EBlo EE (Z_to_bv 5 22) 22%nat (Z_to_bv 5 22) R22 Q22.
  pf_kreg HS EBlo EE (Z_to_bv 5 24) 24%nat (Z_to_bv 5 24) R24 Q24.
  pf_kreg HS EBlo EE (Z_to_bv 5 25) 25%nat (Z_to_bv 5 25) R25 Q25.
  pf_kreg_off HS EBlo EE (Z_to_bv 5 21) 18%nat (Z_to_bv 5 18) R18 Q21 F 336.
  pf_kreg_off HS EBlo EE (Z_to_bv 5 27) 22%nat (Z_to_bv 5 22) R22 Q27 fp 30.
  pf_klit HS (Z_to_bv 5 13) (w64 (-1)) Q13.
  pf_klit HS (Z_to_bv 5 11) (w64 225) Q11.
  pf_reg HS (Z_to_bv 5 10) (w64 (DSpec.fr_cmd b)) Q10
    ltac:(cbn [sv_denot]; rewrite (EBlo 32%nat ltac:(lia)), E32;
          unfold w64; rewrite unsigned_lit_small by lia; rewrite Z.add_0_r; reflexivity).
  (* what the cut carries, at the memory of +0x2a4 *)
  destruct (pf_cur_step STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F
    ly3 S3 W3 memJ mdJ (ms_mem msB) mdB (fun a => sp1 <= a < sp1 + 64) LAWS0 HFIX HCUR HJ KD GD
    ltac:(intros a Ha; left; exact Ha)) as [CURB KFB].
  assert (AOKB : onann_a_ok W3 (ms_mem msB) F buf b).
  { apply (pf_aok_move W3 W3 memJ (ms_mem msB) F buf b HAOK).
    - intros a Ha. apply KFB. left. unfold ONANN_A in Ha. lia.
    - intros i Hi. apply KFB. right. lia. }
  assert (TWB : tw_at TMAP_A (aview segs (w_H W3) (ms_mem msB)) (onann_w1 timg_A Bw b)).
  { apply (tw_kept TMAP_A (aview segs (w_H W3) memJ)); [exact HTW|].
    intros x Hx. pose proof (TMAP_A_hull x Hx) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
    apply KD; lia. }
  assert (SLB : onann_slots_dn W3 (ms_mem msB) fp now sp1 F).
  { unfold onann_slots_dn, onann_slot.
    split; [apply (AF0x.val_mem_rdword _ _ _ _); [unfold ONANN_A; lia | exact V56]|].
    split; [apply (AF0x.val_mem_rdword _ _ _ _); [lia | exact V0]|].
    split; [|apply (AF0x.val_mem_rdword _ _ _ _); [lia | exact V40]].
    apply (AF0x.val_mem_rdword _ _ _ _); [|exact V32].
    pose proof (Z.div_pos (fp + 30) 8 ltac:(lia) ltac:(lia)).
    assert ((fp + 30) / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia). unfold SHADOW_OFF in *. lia. }
  clear V56 V40 V0 V32 D21 D23 D26 KD GD KFB.
  (* ---- run E, +0x2a4: `bne a0, a1`, from a state with no region ---- *)
  pmkst HS.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + ONANN_PFB)) mm rom) mdx) Q) end.
  clear HS SHOK.
  pose proof (pf_entry0 W3 (ms_regs msB) (ms_mem msB) ONANN_PFB) as HS.
  set (E1 := pf_E (ms_regs msB)) in HS.
  assert (HEI1 : img_env VAL A_LIM E1) by (unfold E1, pf_E; apply Eimg_env).
  assert (SHOK : sh_ok segs PF_Bx (@nil shent) E1 (mrestrict (w_H W3) (ms_mem msB))) by constructor.
  assert (E1lo : forall n, (n < 1024)%nat -> ew E1 n = ew E1 n) by (intros n Hn; reflexivity).
  assert (EE1 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E1 n = YK11.getr (ms_regs msB) r)
    by (intros n r Hn; unfold E1, pf_E; apply can_ew_Eimg_Ereg_nat; exact Hn).
  assert (U10 : U E1 (SOff 10 0) = DSpec.fr_cmd b).
  { apply U_atom; [|lia]. rewrite (EE1 10%nat (Z_to_bv 5 10) eq_refl). exact Q10. }
  assert (U11 : U E1 (SOff 11 0) = 225).
  { apply U_atom; [|lia]. rewrite (EE1 11%nat (Z_to_bv 5 11) eq_refl). exact Q11. }
  clear HEI.
  psrr_branch_tok RUN BR HS SHOK PF_B0.
  - (* cmd <> 0xe1: to the desk notice cut +0x308 *)
    rewrite branch_ne_U, U10, U11 in Hc. apply negb_true_iff, Z.eqb_neq in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK PF_B0 ONANN_DN.
    { pf_awr_rs. apply awr_ok_x_nil. }
    set (mdF := with_vm_backing (m_vm_lazy mdB) mat mdB) in *. clearbody mdF. clear mat.
    rename ms into msF.
    pf_mem_eq HF EMF. clear HF HFr HG.
    pf_kreg HS E1lo EE1 (Z_to_bv 5 2) 2%nat (Z_to_bv 5 2) Q2 F2.
    pf_kreg HS E1lo EE1 (Z_to_bv 5 3) 3%nat (Z_to_bv 5 3) Q3 F3.
    pf_kreg HS E1lo EE1 (Z_to_bv 5 4) 4%nat (Z_to_bv 5 4) Q4 F4.
    pf_kreg HS E1lo EE1 (Z_to_bv 5 8) 8%nat (Z_to_bv 5 8) Q8 F8.
    pf_kreg HS E1lo EE1 (Z_to_bv 5 9) 9%nat (Z_to_bv 5 9) Q9 F9.
    pf_kreg HS E1lo EE1 (Z_to_bv 5 18) 18%nat (Z_to_bv 5 18) Q18 F18.
    pf_kreg HS E1lo EE1 (Z_to_bv 5 19) 19%nat (Z_to_bv 5 19) Q19 F19.
    pf_kreg HS E1lo EE1 (Z_to_bv 5 20) 20%nat (Z_to_bv 5 20) Q20 F20.
    pf_kreg HS E1lo EE1 (Z_to_bv 5 21) 21%nat (Z_to_bv 5 21) Q21 F21.
    pf_kreg HS E1lo EE1 (Z_to_bv 5 22) 22%nat (Z_to_bv 5 22) Q22 F22.
    pf_kreg HS E1lo EE1 (Z_to_bv 5 24) 24%nat (Z_to_bv 5 24) Q24 F24.
    pf_kreg HS E1lo EE1 (Z_to_bv 5 25) 25%nat (Z_to_bv 5 25) Q25 F25.
    pf_kreg HS E1lo EE1 (Z_to_bv 5 27) 27%nat (Z_to_bv 5 27) Q27 F27.
    pf_kreg HS E1lo EE1 (Z_to_bv 5 13) 13%nat (Z_to_bv 5 13) Q13 F13.
    pmkst HS.
    lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
      change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + ONANN_DN)) mm rom) mdx) Q) end.
    rewrite EMF in HJ |- *.
    apply (DN LAWS0 CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw'
      pos sp1 F ly3 S3 W3 (ms_mem msB) mdF (ms_regs msF) HFIX).
    + refine (conj (pf_cur_md CURB HJ) (conj TWB (conj HIGN (conj AOKB SLB)))).
    + unfold onann_regs_dn, onann_regs_fm, onann_regs_base.
      assert (Hoff : onann_off (onann_w1 timg_A Bw b) b = -1).
      { unfold onann_off. replace (DSpec.fr_cmd b =? TS0.DIGINET_CMD_ANNOUNCE_SESSION) with false; [reflexivity|].
        symmetry. apply Z.eqb_neq. unfold TS0.DIGINET_CMD_ANNOUNCE_SESSION. exact Hc. }
      rewrite Hoff.
      refine (conj (conj (conj F2 (conj F3 (conj F4 (conj F8 (conj F9 (conj F18 F19))))))
        (conj F20 (conj F21 (conj F22 (conj F24 (conj F25 F27)))))) F13).
  - (* cmd = 0xe1: to the find_mac cut +0x2a8 *)
    rewrite branch_ne_U, U10, U11 in Hc. apply negb_false_iff, Z.eqb_eq in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK PF_B0 ONANN_FM.
    { pf_awr_rs. apply awr_ok_x_nil. }
    set (mdF := with_vm_backing (m_vm_lazy mdB) mat mdB) in *. clearbody mdF. clear mat.
    rename ms into msF.
    pf_mem_eq HF EMF. clear HF HFr HG.
    pf_kreg HS E1lo EE1 (Z_to_bv 5 2) 2%nat (Z_to_bv 5 2) Q2 F2.
    pf_kreg HS E1lo EE1 (Z_to_bv 5 3) 3%nat (Z_to_bv 5 3) Q3 F3.
    pf_kreg HS E1lo EE1 (Z_to_bv 5 4) 4%nat (Z_to_bv 5 4) Q4 F4.
    pf_kreg HS E1lo EE1 (Z_to_bv 5 8) 8%nat (Z_to_bv 5 8) Q8 F8.
    pf_kreg HS E1lo EE1 (Z_to_bv 5 9) 9%nat (Z_to_bv 5 9) Q9 F9.
    pf_kreg HS E1lo EE1 (Z_to_bv 5 18) 18%nat (Z_to_bv 5 18) Q18 F18.
    pf_kreg HS E1lo EE1 (Z_to_bv 5 19) 19%nat (Z_to_bv 5 19) Q19 F19.
    pf_kreg HS E1lo EE1 (Z_to_bv 5 20) 20%nat (Z_to_bv 5 20) Q20 F20.
    pf_kreg HS E1lo EE1 (Z_to_bv 5 21) 21%nat (Z_to_bv 5 21) Q21 F21.
    pf_kreg HS E1lo EE1 (Z_to_bv 5 22) 22%nat (Z_to_bv 5 22) Q22 F22.
    pf_kreg HS E1lo EE1 (Z_to_bv 5 24) 24%nat (Z_to_bv 5 24) Q24 F24.
    pf_kreg HS E1lo EE1 (Z_to_bv 5 25) 25%nat (Z_to_bv 5 25) Q25 F25.
    pf_kreg HS E1lo EE1 (Z_to_bv 5 27) 27%nat (Z_to_bv 5 27) Q27 F27.
    pmkst HS.
    lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
      change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + ONANN_FM)) mm rom) mdx) Q) end.
    rewrite EMF in HJ |- *.
    apply (FM LAWS0 CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw'
      pos sp1 F ly3 S3 W3 (ms_mem msB) mdF (ms_regs msF) HFIX).
    + refine (conj (pf_cur_md CURB HJ) (conj TWB (conj HIGN (conj _ (conj AOKB SLB))))).
      unfold TS0.DIGINET_CMD_ANNOUNCE_SESSION. exact Hc.
    + unfold onann_regs_fm, onann_regs_base.
      exact (conj (conj F2 (conj F3 (conj F4 (conj F8 (conj F9 (conj F18 F19))))))
        (conj F20 (conj F21 (conj F22 (conj F24 (conj F25 F27)))))).
Qed.

(* ------------------------------------------------------------------ *)
(* 8. From the personality cut (+0x248) to the join                    *)
(* ------------------------------------------------------------------ *)

Lemma pf_holds : @onann_pf_stmt fx rc B MT.
Proof.
  unfold onann_pf_stmt. intros FM DN. unfold onann_pf_at.
  intros LAWS0 CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F
    ly2 S2 W2 mem2 md2 regs2 HFIX HCUR HREGS.
  pose proof LAWS0 as (HSM & HCELLS & HOC & HGU & HGE0 & HRU & HRE & LAWS & MTL & MTF & SMP & ASF & FFL & HGX & HGE).
  pose proof CALLEES as (CSM & CLEAF & CPF & CBCMP & CMS & CNT & CWK & CMO & CF5).
  pose proof HFIX as (HJ0 & Hret & Hra & Hgp & Htp & H10 & H11 & H12 & Hsp16 & Hlo & Hhi & Hnow & HDF & Htw0 & Hgf &
    Hm & HTF & Htfg & Hrom & Hap & Hri & Hcnt & Hcnt2 & Hev & Esp1 & EF & HF0 & HF64 & HFc & HFapp).
  pose proof HCUR as ((HJ2 & He0 & Hfrs & Hperm & HlyF & Hmo & HK & Hsaved & HFLw) & Htw2 & Hign & HAOK).
  pose proof HREGS as ((((R2 & R3 & R4 & R8 & R9 & R18 & R19) & R23) & R20 & R24) & R21 & R22 & R26).
  destruct (pf_basics HFIX) as (Bc & Bl & Bh & B47 & Bs1 & Bs32 & BSK & BPF & B46 & Bpres).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  unfold ONANN_FBYTES in HFc, HFapp, HFLw.
  pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HAR2.
  assert (EF2 : frame_addr ly2 ONANN_CID pos = F) by (rewrite EF; unfold frame_addr; rewrite HlyF; reflexivity).
  assert (Hin2 : In (ONANN_CID, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
  destruct (al_frames _ _ LAWS ly2 S2 W2 mem2 md2 ONANN_CID pos HAR2 Hin2) as (_ & _ & HFb & HFsh).
  rewrite EF2 in HFb, HFsh. change (fs_frame_bytes ONANN_CID) with 1024 in HFb.
  change (fs_frame_bytes ONANN_CID / 8) with 128 in HFsh.
  assert (DFm8 : F mod 8 = 0).
  { pose proof (Z.div_mod F 64 ltac:(lia)) as D. rewrite HF64, Z.add_0_r in D. rewrite D.
    replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by ring. apply Z.mod_mul. lia. }
  pose proof (pf_ann_len (skipn 24 (DSpec.fr_body b))) as Ltb.
  pose proof (pf_pv_facts Bw b) as (Hpv & Hpv0 & Hpv1).
  (* ---- run A, +0x248 .. +0x24c: a0 = a + 10, `jal diginet_personality_from_name` ---- *)
  pose proof (pf_entry0 W2 regs2 mem2 ONANN_PF) as HS.
  set (E0 := pf_E regs2) in HS.
  assert (HEI : img_env VAL A_LIM E0) by (unfold E0, pf_E; apply Eimg_env).
  assert (SHOK : sh_ok segs PF_Bx (@nil shent) E0 (mrestrict (w_H W2) mem2)) by constructor.
  assert (E0lo : forall n, (n < 1024)%nat -> ew E0 n = ew E0 n) by (intros n Hn; reflexivity).
  assert (EE0 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E0 n = YK11.getr regs2 r)
    by (intros n r Hn; unfold E0, pf_E; apply can_ew_Eimg_Ereg_nat; exact Hn).
  pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
    as RUN.
  pose proof (@paj_run_to_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX
    0 []) as RUNTO.
  pose proof (paj_branch (fx := fx) (PI := PI_transport)) as BR.
  paj_run_tok RUN HS HJ2 SHOK PF_B0.
  { pf_awr_rs. apply awr_ok_x_nil. }
  set (md1 := with_vm_backing (m_vm_lazy md2) mat md2) in *. clearbody md1. clear mat.
  rename ms into msA.
  pf_mem_eq HF EMA. clear HF HFr HG.
  match goal with H : img_env _ _ _ |- _ => lazymatch H with HEI => fail | _ => clear H end end.
  assert (HBASE : BASE = 0x81264) by (vm_compute; reflexivity).
  pf_reg HS (Z_to_bv 5 10) (w64 (F + ONANN_A + 10)) A10
    ltac:(cbn [sv_denot]; rewrite (EE0 21%nat (21%bv : bv 5) eq_refl), R21;
          unfold w64; rewrite unsigned_lit_small by (unfold ONANN_A; lia); reflexivity).
  pf_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 27232)) A1 ltac:(apply codeptr_val; exact HEI).
  pf_kreg HS E0lo EE0 (Z_to_bv 5 2) 2%nat (Z_to_bv 5 2) R2 A2.
  pf_kreg HS E0lo EE0 (Z_to_bv 5 3) 3%nat (Z_to_bv 5 3) R3 A3.
  pf_kreg HS E0lo EE0 (Z_to_bv 5 4) 4%nat (Z_to_bv 5 4) R4 A4.
  assert (ASP : spZ (ms_regs msA) = sp1)
    by (change (bv_unsigned (YK11.getr (ms_regs msA) (Z_to_bv 5 2)) = sp1); rewrite A2; unfold w64;
        apply unsigned_lit_small; lia).
  assert (HAP : aregs_preserved regs2 (ms_regs msA)).
  { apply (aregs_preserved_of_st_ok segs (w_H W2) E0 _ msA regs2 [] HS).
    - split; [intros n Hn; unfold E0, pf_E; apply Eimg_low; unfold A_TEXT; lia | reflexivity].
    - vm_compute. reflexivity. }
  (* ---- the call of diginet_personality_from_name ---- *)
  pmkst HS. rewrite EMA in HJ2 |- *.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (@cfg_at fx segs (transport_sigma TS_diginet_personality_from_name) rg mm mdx) Q) end.
  assert (HSRC : trans_src_ok B ly2 S2 W2 mem2 (F + ONANN_A + 10)
    (Z.of_nat (length (TSS.ann_field (skipn 24 (DSpec.fr_body b)))))).
  { right. split.
    - left. exists ONANN_CID, pos. split; [exact Hin2|]. rewrite EF2. change (fs_frame_bytes ONANN_CID) with 1024.
      unfold ONANN_A. lia.
    - unfold decode_rd_ok. split; [|split; [|split; [|split; [|split]]]].
      + intros a Ha. apply can_aview_vis. apply (proj1 (HFb a ltac:(unfold ONANN_A in Ha; lia))).
      + apply (TransportGNotice.frame_ra_zero _ F (F + ONANN_A + 10) _ 32 37);
          [lia | exact DFm8 | unfold ONANN_A; lia | unfold ONANN_A; lia |].
        exact (proj2 (proj2 (proj2 (proj2 HAOK)))).
      + apply (TransportGNotice.frame_hull_vis _ F 1024 (F + ONANN_A + 10) _);
          [lia | exact HF64 | reflexivity | unfold ONANN_A; lia
          | unfold TSS.ann_field; rewrite length_app; cbn [length]; lia | unfold ONANN_A; lia |].
        intros i Hi. apply can_aview_vis. exact (proj1 (HFsh i Hi)).
      + apply (amem_range_sub_app F 1024); [exact HFapp | lia | unfold ONANN_A; lia | unfold ONANN_A; lia | lia].
      + unfold ONANN_A; lia.
      + unfold ONANN_A; lia. }
  pose proof (onann_rom_call B HRU HRE lyc Sc W memc W2 mem2 _ _ _ Hrom HK) as HROM2.
  eapply SRr_bind.
  { apply (@gx_call_cg fx rc tfib_sink_head segs B MT TG.G_HARNESS STK sp0 FP ly S W0 mem0 md0
      ((ONANN_CID, pos) :: own) ly2 S2 W2 mem2 md1 (k + 0) _ (ms_regs msA) PFROM_STK PFROM_EV 0 (fun _ => False)
      (fun regs3 _ _ => YK11.getr regs3 10 = w64 (trans_pfrom_res (TSS.ann_field (skipn 24 (DSpec.fr_body b)))))
      HGX HGE HJ2).
    intros memS HJS. eapply SRr_mono.
    { apply (CPF fx STK sp0 FP ly S W0 memS md0 ((ONANN_CID, pos) :: own) ly2 S2 W2 mem2 md1 (k + 0) (ms_regs msA)
        (F + ONANN_A + 10) (TSS.ann_field (skipn 24 (DSpec.fr_body b))) HJS).
      - rewrite A1. apply (ret_ok_codeptr_v (PI := PI_transport)); [lia | reflexivity].
      - unfold raZ. rewrite A1, HBASE. rewrite unsigned_lit_small by lia. lia.
      - exact (eq_trans A3 Hgp).
      - exact (eq_trans A4 Htp).
      - exact A10.
      - rewrite ASP. pose proof (Z.div_mod sp1 32 ltac:(lia)) as D1. rewrite Bs32, Z.add_0_r in D1. rewrite D1.
        replace (32 * (sp1 / 32)) with ((2 * (sp1 / 32)) * 16) by ring. apply Z.mod_mul. lia.
      - rewrite ASP. lia.
      - rewrite ASP. lia.
      - unfold ONANN_A. lia.
      - exact (proj1 (proj2 HAOK)).
      - exact (pf_tb_nul _).
      - exact HSRC.
      - unfold decode_off_win. left. rewrite ASP. unfold ONANN_A. lia.
      - exact HROM2.
      - assert (0 <= ONANN_EV) by (vm_compute; congruence). unfold PFROM_EV. lia. }
    intros W' c' _ Hp.
    exact (decode_cg_post_dcg B MT STK sp0 FP ly S W0 memS md0 ((ONANN_CID, pos) :: own) ly2 S2 W2 mem2 (k + 0)
      (ms_regs msA) _ _ _ _ _ W' c' Hp). }
  cbv beta. intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & e & -> & He & HJ3 & HP3 & Hfr3 & Hperm3 & HK3 & Hmo3 &
    (HX3 & HGK3)).
  assert (Ee : e = 0) by (unfold PFROM_EV in He; lia). subst e. rewrite Z.add_0_r in HJ3.
  rewrite ASP in HK3.
  rewrite (onann_pv_res b) in HX3.
  destruct (pf_cur_call STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F
    ly2 S2 W2 mem2 md1 ly3 S3 W3 mem3 md3 LAWS0 HFIX (pf_cur_md (proj1 HCUR) HJ2) HJ3 Hfr3 Hperm3 Hmo3 HK3)
    as [CUR3 KF3].
  assert (AOK3 : onann_a_ok W3 mem3 F buf b).
  { apply (pf_aok_move W2 W3 mem2 mem3 F buf b HAOK).
    - intros a Ha. apply KF3. left. unfold ONANN_A in Ha. lia.
    - intros i Hi. apply KF3. right. lia. }
  assert (TW3 : tw_at TMAP_A (aview segs (w_H W3) mem3) Bw).
  { apply (tw_kept_GA _ _ Bw Htw2). intros b0 m0 i Hin Hi. exact (gx_kept_rows _ _ _ _ _ _ HGK3 b0 m0 i Hin Hi). }
  pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HAR3.
  (* the registers after the call *)
  assert (CS : forall n, acallee_saved n -> YK11.getr regs3 (Z_to_bv 5 n) = YK11.getr regs2 (Z_to_bv 5 n))
    by (intros n Hn; exact (eq_trans (HP3 n Hn) (HAP n Hn))).
  assert (P2 : YK11.getr regs3 2 = w64 sp1) by exact (eq_trans (CS 2 ltac:(hnf; lia)) R2).
  assert (P3 : YK11.getr regs3 3 = YK11.getr regs 3) by exact (eq_trans (CS 3 ltac:(hnf; lia)) R3).
  assert (P4 : YK11.getr regs3 4 = YK11.getr regs 4) by exact (eq_trans (CS 4 ltac:(hnf; lia)) R4).
  assert (P8 : YK11.getr regs3 8 = w64 (spZ regs)) by exact (eq_trans (CS 8 ltac:(hnf; lia)) R8).
  assert (P9 : YK11.getr regs3 9 = w64 sp1) by exact (eq_trans (CS 9 ltac:(hnf; lia)) R9).
  assert (P18 : YK11.getr regs3 18 = w64 F) by exact (eq_trans (CS 18 ltac:(hnf; lia)) R18).
  assert (P19 : YK11.getr regs3 19 = w64 (SHADOW_OFF + F / 8)) by exact (eq_trans (CS 19 ltac:(hnf; lia)) R19).
  assert (P20 : YK11.getr regs3 20 = w64 ONANN_S) by exact (eq_trans (CS 20 ltac:(hnf; lia)) R20).
  assert (P21 : YK11.getr regs3 21 = w64 (F + ONANN_A)) by exact (eq_trans (CS 21 ltac:(hnf; lia)) R21).
  assert (P22 : YK11.getr regs3 22 = w64 fp) by exact (eq_trans (CS 22 ltac:(hnf; lia)) R22).
  assert (P23 : YK11.getr regs3 23 = w64 F) by exact (eq_trans (CS 23 ltac:(hnf; lia)) R23).
  assert (P24 : YK11.getr regs3 24 = w64 SHADOW_OFF) by exact (eq_trans (CS 24 ltac:(hnf; lia)) R24).
  assert (P26 : YK11.getr regs3 26 = w64 now) by exact (eq_trans (CS 26 ltac:(hnf; lia)) R26).
  clear CS HP3 HAP.
  (* ---- run C, +0x250 .. +0x254: s9 = p, `beqz a0`, from a state with no region ---- *)
  rewrite A1. change (Z_to_bv 64 (BASE + 27232)) with (Z_to_bv 64 (BASE + ONANN_PFC)).
  clear HS SHOK HEI E0lo EE0.
  clear dependent msA.
  pose proof (pf_entry0 W3 regs3 mem3 ONANN_PFC) as HS.
  set (E2 := pf_E regs3) in HS.
  assert (HEI : img_env VAL A_LIM E2) by (unfold E2, pf_E; apply Eimg_env).
  assert (SHOK : sh_ok segs PF_Bx (@nil shent) E2 (mrestrict (w_H W3) mem3)) by constructor.
  assert (E2lo : forall n, (n < 1024)%nat -> ew E2 n = ew E2 n) by (intros n Hn; reflexivity).
  assert (EE2 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E2 n = YK11.getr regs3 r)
    by (intros n r Hn; unfold E2, pf_E; apply can_ew_Eimg_Ereg_nat; exact Hn).
  paj_run_tok RUN HS HJ3 SHOK PF_B0.
  { pf_awr_rs. apply awr_ok_x_nil. }
  set (md4 := with_vm_backing (m_vm_lazy md3) mat md3) in *. clearbody md4. clear mat.
  rename ms into msC.
  pf_mem_eq HF EMC. clear HF HFr HG.
  match goal with H : img_env _ _ _ |- _ => lazymatch H with HEI => fail | _ => clear H end end.
  assert (U10 : U E2 (SOff 10 0) = onann_pv timg_A b).
  { apply U_atom; [|exact Hpv]. rewrite (EE2 10%nat (Z_to_bv 5 10) eq_refl). exact HX3. }
  psrr_branch_tok RUN BR HS SHOK PF_B0.
  - (* p = 0: to the join +0x270 *)
    rewrite branch_eq_U, U10, U_lit in Hc by lia. apply Z.eqb_eq in Hc.
    paj_run_to_tok RUNTO HS HJ3 SHOK PF_B0 ONANN_PFJ.
    { pf_awr_rs. apply awr_ok_x_nil. }
    set (md5 := with_vm_backing (m_vm_lazy md4) mat md4) in *. clearbody md5. clear mat.
    rename ms into msJ.
    pf_mem_eq HF EMJ. clear HF HFr HG.
    pf_kreg HS E2lo EE2 (Z_to_bv 5 2) 2%nat (Z_to_bv 5 2) P2 J2.
    pf_kreg HS E2lo EE2 (Z_to_bv 5 3) 3%nat (Z_to_bv 5 3) P3 J3.
    pf_kreg HS E2lo EE2 (Z_to_bv 5 4) 4%nat (Z_to_bv 5 4) P4 J4.
    pf_kreg HS E2lo EE2 (Z_to_bv 5 8) 8%nat (Z_to_bv 5 8) P8 J8.
    pf_kreg HS E2lo EE2 (Z_to_bv 5 9) 9%nat (Z_to_bv 5 9) P9 J9.
    pf_kreg HS E2lo EE2 (Z_to_bv 5 18) 18%nat (Z_to_bv 5 18) P18 J18.
    pf_kreg HS E2lo EE2 (Z_to_bv 5 19) 19%nat (Z_to_bv 5 19) P19 J19.
    pf_kreg HS E2lo EE2 (Z_to_bv 5 20) 20%nat (Z_to_bv 5 20) P20 J20.
    pf_kreg HS E2lo EE2 (Z_to_bv 5 21) 21%nat (Z_to_bv 5 21) P21 J21.
    pf_kreg HS E2lo EE2 (Z_to_bv 5 22) 22%nat (Z_to_bv 5 22) P22 J22.
    pf_kreg HS E2lo EE2 (Z_to_bv 5 23) 23%nat (Z_to_bv 5 23) P23 J23.
    pf_kreg HS E2lo EE2 (Z_to_bv 5 24) 24%nat (Z_to_bv 5 24) P24 J24.
    pf_kreg HS E2lo EE2 (Z_to_bv 5 26) 26%nat (Z_to_bv 5 26) P26 J26.
    pf_kreg HS E2lo EE2 (Z_to_bv 5 25) 10%nat (Z_to_bv 5 10) HX3 J25.
    pmkst HS.
    lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
      change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + ONANN_PFJ)) mm rom) mdx) Q) end.
    rewrite EMJ in HJ3 |- *. rewrite EMC in HJ3 |- *.
    apply (pf_tail STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F
      ly3 S3 W3 mem3 md5 (ms_regs msJ) LAWS0 CALLEES FM DN HFIX (pf_cur_md CUR3 HJ3)
      ltac:(rewrite (Hpv0 Hc); exact TW3) Hign AOK3).
    + exact (conj J2 (conj J3 (conj J4 (conj J8 (conj J9 (conj J18 J19)))))).
    + exact J20.
    + exact J21.
    + exact J22.
    + exact J23.
    + exact J24.
    + exact J25.
    + exact J26.
  - (* p <> 0: to +0x258, then the store of p at s + 128 *)
    rewrite branch_eq_U, U10, U_lit in Hc by lia. apply Z.eqb_neq in Hc.
    paj_run_to_tok RUNTO HS HJ3 SHOK PF_B0 ONANN_PFN.
    { pf_awr_rs. apply awr_ok_x_nil. }
    set (md5 := with_vm_backing (m_vm_lazy md4) mat md4) in *. clearbody md5. clear mat.
    rename ms into msN0.
    pf_mem_eq HF EMN. clear HF HFr HG.
    pf_kreg HS E2lo EE2 (Z_to_bv 5 2) 2%nat (Z_to_bv 5 2) P2 N2.
    pf_kreg HS E2lo EE2 (Z_to_bv 5 3) 3%nat (Z_to_bv 5 3) P3 N3.
    pf_kreg HS E2lo EE2 (Z_to_bv 5 4) 4%nat (Z_to_bv 5 4) P4 N4.
    pf_kreg HS E2lo EE2 (Z_to_bv 5 8) 8%nat (Z_to_bv 5 8) P8 N8.
    pf_kreg HS E2lo EE2 (Z_to_bv 5 9) 9%nat (Z_to_bv 5 9) P9 N9.
    pf_kreg HS E2lo EE2 (Z_to_bv 5 18) 18%nat (Z_to_bv 5 18) P18 N18.
    pf_kreg HS E2lo EE2 (Z_to_bv 5 19) 19%nat (Z_to_bv 5 19) P19 N19.
    pf_kreg HS E2lo EE2 (Z_to_bv 5 20) 20%nat (Z_to_bv 5 20) P20 N20.
    pf_kreg HS E2lo EE2 (Z_to_bv 5 21) 21%nat (Z_to_bv 5 21) P21 N21.
    pf_kreg HS E2lo EE2 (Z_to_bv 5 22) 22%nat (Z_to_bv 5 22) P22 N22.
    pf_kreg HS E2lo EE2 (Z_to_bv 5 23) 23%nat (Z_to_bv 5 23) P23 N23.
    pf_kreg HS E2lo EE2 (Z_to_bv 5 24) 24%nat (Z_to_bv 5 24) P24 N24.
    pf_kreg HS E2lo EE2 (Z_to_bv 5 26) 26%nat (Z_to_bv 5 26) P26 N26.
    pf_kreg HS E2lo EE2 (Z_to_bv 5 25) 10%nat (Z_to_bv 5 10) HX3 N25.
    pmkst HS.
    lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
      change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + ONANN_PFN)) mm rom) mdx) Q) end.
    rewrite EMN in HJ3 |- *. rewrite EMC in HJ3 |- *.
    clear HS SHOK HEI E2lo EE2 U10 EMN EMC.
    set (regsN := ms_regs msN0) in *. clearbody regsN. clear dependent msN0. clear dependent msC.
    (* ---- run N, +0x258 .. +0x26c: the checked store of p at s + 128 ---- *)
    destruct (pf_entry_n ly3 S3 W3 regsN mem3 md3 HOC HAR3 N20 N24) as [HS SHOK].
    set (E3 := pf_E regsN) in HS, SHOK.
    assert (HEI : img_env VAL A_LIM E3) by (unfold E3, pf_E; apply Eimg_env).
    assert (EE3 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E3 n = YK11.getr regsN r)
      by (intros n r Hn; unfold E3, pf_E; apply can_ew_Eimg_Ereg_nat; exact Hn).
    assert (U20 : bv_unsigned (ew E3 20) = ONANN_S)
      by (rewrite (EE3 20%nat (Z_to_bv 5 20) eq_refl); unfold w64 in N20; rewrite N20;
          apply unsigned_lit_small; unfold ONANN_S, TA_g_s; lia).
    paj_run_to_tok RUNTO HS HJ3 SHOK YC4b.Bspan ONANN_PFJ.
    { pf_awr_rs.
      apply awr_ok_x_cons_g;
        [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U20 in Ha;
         apply pf_inG; unfold TW.SZ_g_s; lia |].
      apply awr_ok_x_nil. }
    set (md6 := with_vm_backing (m_vm_lazy md5) mat md5) in *. clearbody md6. clear mat.
    rename ms into msJ.
    lazymatch type of HS with st_ok_pi _ _ ?EF _ _ => set (EN := EF) in * end.
    assert (ENlo : forall n, (n < 1024)%nat -> ew EN n = ew E3 n)
      by (intros n Hn; unfold EN; rewrite ?ew_ewset_other by lia; reflexivity).
    assert (KN : forall a, 0 <= a < 2 ^ 64 -> ~ (ONANN_S + 128 <= a < ONANN_S + 136) ->
      aview segs (w_H W3) (ms_mem msJ) a = aview segs (w_H W3) mem3 a).
    { intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ (fun x => ONANN_S + 128 <= x < ONANN_S + 136) HFr);
        [| exact Ha | exact Hn].
      intros b0 wlo whi x Hin Hx.
      lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
      cbn [In] in Hin.
      repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; rewrite ?U20 in Hx;
        lia |]).
      destruct Hin. }
    assert (GN : forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) (ms_mem msJ) a)
      by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
    clear HF HFr HG.
    (* the stored value, read back from g_s.personality's region *)
    pf_region HS 0%nat HR.
    assert (U20N : bv_unsigned (ew EN 20) = ONANN_S) by (rewrite ENlo by lia; exact U20).
    assert (D25 : sv_denot EN (SOff 25 0) = Z_to_bv 64 (onann_pv timg_A b)).
    { exact (pf_denot_atom EN 25%nat _
        (eq_trans (ENlo 25%nat ltac:(lia)) (eq_trans (EE3 25%nat (Z_to_bv 5 25) eq_refl) N25))). }
    assert (HVAL : val_mem segs (mrestrict (w_H W3) (ms_mem msJ)) (ONANN_S + 128) 8 (onann_pv timg_A b)).
    { exact (can_field_of_region EN _ 20 ONANN_S _ 128 136 128 136 128 8%N (SOff 25 0) (onann_pv timg_A b) HR U20N
        ltac:(pf_in) D25 ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact Hpv) ltac:(cbn; lia)). }
    clear HR.
    (* the world after the store: set_S_personality Bw p *)
    assert (TWN : tw_at TMAP_A (aview segs (w_H W3) (ms_mem msJ)) (onann_w1 timg_A Bw b)).
    { rewrite (Hpv1 Hc), pf_w1_eq.
      apply (tw_write TMAP_A (aview segs (w_H W3) mem3) _ Bw TW.OFF_g_s TA_g_s TW.SZ_g_s 128 8 (onann_pv timg_A b)
        TMAP_A_ok TW3 TMAP_A_g_s ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
      - intros j Hj. unfold aview.
        replace (TA_g_s + 128 + Z.of_nat j) with (ONANN_S + 128 + Z.of_nat j) by (unfold ONANN_S; lia).
        rewrite (HVAL j Hj). cbn [option_map]. f_equal.
        rewrite AF0x.unsigned_lit_small8; [reflexivity|].
        unfold YO0f.le_byte. apply Z.mod_pos_bound. lia.
      - intros x Hx Hout. pose proof (TMAP_A_hull x Hx) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
        apply KN; [lia | unfold ONANN_S; lia]. }
    destruct (pf_cur_step STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F
      ly3 S3 W3 mem3 md3 (ms_mem msJ) md6 (fun a => ONANN_S + 128 <= a < ONANN_S + 136) LAWS0 HFIX CUR3 HJ3 KN GN
      ltac:(intros a Ha; right; exact Ha)) as [CURJ KFJ].
    assert (AOKJ : onann_a_ok W3 (ms_mem msJ) F buf b).
    { apply (pf_aok_move W3 W3 mem3 (ms_mem msJ) F buf b AOK3).
      - intros a Ha. apply KFJ. left. unfold ONANN_A in Ha. lia.
      - intros i Hi. apply KFJ. right. lia. }
    (* the registers at the join *)
    pf_kreg HS ENlo EE3 (Z_to_bv 5 2) 2%nat (Z_to_bv 5 2) N2 J2.
    pf_kreg HS ENlo EE3 (Z_to_bv 5 3) 3%nat (Z_to_bv 5 3) N3 J3.
    pf_kreg HS ENlo EE3 (Z_to_bv 5 4) 4%nat (Z_to_bv 5 4) N4 J4.
    pf_kreg HS ENlo EE3 (Z_to_bv 5 8) 8%nat (Z_to_bv 5 8) N8 J8.
    pf_kreg HS ENlo EE3 (Z_to_bv 5 9) 9%nat (Z_to_bv 5 9) N9 J9.
    pf_kreg HS ENlo EE3 (Z_to_bv 5 18) 18%nat (Z_to_bv 5 18) N18 J18.
    pf_kreg HS ENlo EE3 (Z_to_bv 5 19) 19%nat (Z_to_bv 5 19) N19 J19.
    pf_kreg HS ENlo EE3 (Z_to_bv 5 20) 20%nat (Z_to_bv 5 20) N20 J20.
    pf_kreg HS ENlo EE3 (Z_to_bv 5 21) 21%nat (Z_to_bv 5 21) N21 J21.
    pf_kreg HS ENlo EE3 (Z_to_bv 5 22) 22%nat (Z_to_bv 5 22) N22 J22.
    pf_kreg HS ENlo EE3 (Z_to_bv 5 23) 23%nat (Z_to_bv 5 23) N23 J23.
    pf_kreg HS ENlo EE3 (Z_to_bv 5 24) 24%nat (Z_to_bv 5 24) N24 J24.
    pf_kreg HS ENlo EE3 (Z_to_bv 5 25) 25%nat (Z_to_bv 5 25) N25 J25.
    pf_kreg HS ENlo EE3 (Z_to_bv 5 26) 26%nat (Z_to_bv 5 26) N26 J26.
    pmkst HS.
    lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
      change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + ONANN_PFJ)) mm rom) mdx) Q) end.
    apply (pf_tail STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F
      ly3 S3 W3 (ms_mem msJ) md6 (ms_regs msJ) LAWS0 CALLEES FM DN HFIX CURJ TWN Hign AOKJ).
    + exact (conj J2 (conj J3 (conj J4 (conj J8 (conj J9 (conj J18 J19)))))).
    + exact J20.
    + exact J21.
    + exact J22.
    + exact J23.
    + exact J24.
    + exact J25.
    + exact J26.
Qed.
End pf.

(* The personality piece of the walk of on_announce (OnannCut.v onann_pf_stmt), at every machine, run ceiling,
   record and meter. *)
Theorem onann_piece_pf : forall fx rc B MT, @onann_pf_stmt fx rc B MT.
Proof. intros fx rc B MT. exact (@pf_holds fx rc B MT). Qed.
