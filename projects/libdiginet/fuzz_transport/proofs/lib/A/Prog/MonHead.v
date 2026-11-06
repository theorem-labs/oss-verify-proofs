(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, origin/cold/pg-prog), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-10: the walk is reac-repacer/fuzz_uci's check_clamp in image A, in the shape of the released image-A walks proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_entry.v, .../LLVMFuzzerTestOneInput_seg_copy.v and .../LLVMFuzzerTestOneInput_seg_exit_tail.v at origin/ossv/recipes 88154566652a: module paths, listing symbol type, the symbolic states, the cut points and every address and offset are this function's; the fake-frame class is 1, the single intrinsic is __asan_memcpy of 20 bytes, and the result is the caller-journal contract of lib/A/Prog/check_clamp_cg.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths changed; 663 of its 1139 lines of code are new or changed and 8 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths, module names and numbers changed; 1054 of its 1168 lines of code are new or changed and 1025 lines of the source are left out. *)
(* MonHead: Lemma mon_head : the head piece of the walk of maybe_online (fuzz_transport.asan 0x8b170,
   AF_maybe_online = 0x9f0c of lib/A/Prog/DgnTransportList.v), the Prop mon_head_stmt of lib/A/Prog/MonCut.v:
   from the entry to one of the two cuts, in two runs of the position-abstract engine over the caller's G journal
   (lib/A/W_journalG.v ajournal_gx TG.G_HARNESS 0 [], run by lib/A/Prog/TransportGRunA.v paj_run_x) and one call.
     +0x000 .. +0x064  the frame (`addi sp, sp, -96`), the zero word at sp, the 11 saves, s0, the realign into s1,
                       the two runtime cells read through their GOT words (the flag word is 1, so `beqz a2` at
                       +0x05c is not taken; transport_cells rows 1, 2, 6, 7), s8 = the shadow base, s3 = s, a0 = 160
                       and `jal __asan_stack_malloc_2` (lib/A/Prog/TransportGFrame.v gx_stack_malloc_at);
     +0x068 .. +0x1d0  the frame F in a0 (F >= 4096, so `bnez s2` at +0x078 skips the real-stack arm), s7 = s2 = F,
                       the frame's 24-byte header, s6 = its shadow address and its 20 shadow bytes, s4 = s + 112,
                       s9 = its shadow address, the frame word at s1 + 0, the three checked loads and the three
                       tests of :178, the checks of s + 176, s + 24 and s + 184, s5 = F + 32 and the 8-byte store
                       at s + 184 (:179).
   The instrumented checks need no token: the shadow byte of each access is a chunk of the run's region at g_s's
   shadow address (mh_rg_gsh, value 0 from trans_maybeon_cells), reached by the engine's shadow alias
   (lib/Reusable/YP0i.v shadow_norm: the alias (s3 >> 3) + s8 = atom 34).  The frame's own shadow bytes are the
   region mh_rg_fsh at the alias (a0 >> 3) + s8 = atom 33.  So no error path is reached.
   The three tests leave the run at +0x140, +0x15c and +0x178; each taken side runs to +0x290 and closes with
   mon_rel_at (maybeon_go Bw = false, so W2 = W, e = 0 and Bw' = Bw by the model premise), the last not-taken side
   runs to +0x1d4 and closes with mon_ntc_at. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportSyms DgnTransportList DgnTransportAddr DgnTransportPa DgnTransportImg DgnTransportPaLib YC4b YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG AF0x AE2y.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportCg TransportGCg TransportGRwA TransportGRunA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import CanKit TransportGFrame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import m_lost_cg notice_cg maybe_online_cg MonCut.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TSess0 TSess TWorldLemmas.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module FCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.AsanCells.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.

(* ------------------------------------------------------------------ *)
(* 1. The two symbolic states                                          *)
(* ------------------------------------------------------------------ *)

(* The world offsets of the six fields the head reads or writes, as numerals: the walk never leaves the kernel a
   conversion between a world accessor and its definition. *)
Definition MON_O_KA : Z := 1672.   (* s + 24,  S_cfg_keepalive_ms,  4 bytes, unsigned *)
Definition MON_O_ST : Z := 1760.   (* s + 112, S_state,             4 bytes, signed *)
Definition MON_O_E1 : Z := 1788.   (* s + 140, S_e1_named_us,       4 bytes, signed *)
Definition MON_O_WA : Z := 1792.   (* s + 144, S_wake_acked,        4 bytes, signed *)
Definition MON_O_RX : Z := 1824.   (* s + 176, S_last_rx_us,        8 bytes *)
Definition MON_O_NK : Z := 1832.   (* s + 184, S_next_keepalive_us, 8 bytes *)
Lemma mon_offs : TW.A_S_cfg_keepalive_ms = MON_O_KA /\ TW.A_S_state = MON_O_ST /\ TW.A_S_e1_named_us = MON_O_E1 /\
  TW.A_S_wake_acked = MON_O_WA /\ TW.A_S_last_rx_us = MON_O_RX /\ TW.A_S_next_keepalive_us = MON_O_NK /\
  TW.OFF_g_s = 1648.
Proof. repeat split; reflexivity. Qed.

(* g_s's shadow address, a numeral. *)
Definition MON_GSH : Z := SHADOW_OFF + MAYBEON_S / 8.

(* run 1: the entry.  Regions: the 96-byte frame below sp (the zero word and the 11 saves), and the two runtime
   cells through their GOT words (objects 1 / 93: the shadow base; objects 0 / 94: the use-after-return flag). *)
Definition mh_got_uar : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 0)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff (A_OBJ 94) 0))].
Definition mh_uar_cell : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 94)) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SLit 1))].
Definition mh_img_regions : smem := [got_regionP; bcell_regionP 32; mh_got_uar; mh_uar_cell].
Definition mh_regions1 : smem := stack_region MAYBEON_FRAME :: mh_img_regions.
Definition mh_facts1 : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (10%nat, mkAF MAYBEON_S MAYBEON_S 0)] [] [].
Definition ss_mh1 : sstate := mkSS AF_maybe_online sr_atoms mh_regions1 None mh_facts1.
(* The token engine is not used: every instrumented check reads a shadow region of the state. *)
Definition MH_SH : list shent := [].
Definition MH_B0 : Z * Z := (0, 0).

(* run 2: +0x68, the frame in a0.  Atom 33 is the frame's shadow address, atom 34 g_s's; the two aliases let the
   engine normalise `(x >> 3) + s8` to those atoms (YP0i.v shadow_norm).  Atoms 35 .. 40 are the six world fields. *)
Definition mh_alias : list (sv * sv) :=
  [(SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 0) (SLit 3)) (SOff 24 0), SOff 33 0);
   (SAlu ALU_ADD (SAlu ALU_SRL (SOff 19 0) (SLit 3)) (SOff 24 0), SOff 34 0)].
Definition mh_rg_hdr : YP09.region := YP09.mkRegion (Some 10%nat) 0 24 0 24 [].
Definition mh_rg_fsh : YP09.region := YP09.mkRegion (Some 33%nat) 0 20 0 20 [].
Definition mh_rg_slot : YP09.region := YP09.mkRegion (Some 9%nat) 0 8 0 8 [].
Definition mh_rg_gsh : YP09.region := YP09.mkRegion (Some 34%nat) 3 24 0 0
  [YP09.mkChunk 3 (CVal 1 (SLit 0)); YP09.mkChunk 14 (CVal 1 (SLit 0));
   YP09.mkChunk 17 (CVal 1 (SLit 0)); YP09.mkChunk 18 (CVal 1 (SLit 0));
   YP09.mkChunk 22 (CVal 1 (SLit 0)); YP09.mkChunk 23 (CVal 1 (SLit 0))].
Definition mh_rg_gs : YP09.region := YP09.mkRegion (Some 19%nat) 24 192 184 192
  [YP09.mkChunk 24 (CVal 4 (SOff 35 0)); YP09.mkChunk 112 (CVal 4 (SOff 36 0));
   YP09.mkChunk 140 (CVal 4 (SOff 37 0)); YP09.mkChunk 144 (CVal 4 (SOff 38 0));
   YP09.mkChunk 176 (CVal 8 (SOff 39 0)); YP09.mkChunk 184 (CVal 8 (SOff 40 0))].
Definition mh_regions2 : smem := [mh_rg_hdr; mh_rg_fsh; mh_rg_slot; mh_rg_gsh; mh_rg_gs].
Definition mh_facts2 : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5);
           (10%nat, mkAF 4096 (2 ^ 47) 6); (19%nat, mkAF MAYBEON_S MAYBEON_S 6);
           (24%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (33%nat, mkAF SHADOW_OFF (2 ^ 46) 0); (34%nat, mkAF MON_GSH MON_GSH 0);
           (35%nat, mkAF 0 (2 ^ 32 - 1) 0); (36%nat, mkAF 0 (2 ^ 32 - 1) 0);
           (37%nat, mkAF 0 (2 ^ 32 - 1) 0); (38%nat, mkAF 0 (2 ^ 32 - 1) 0)]
    [] mh_alias.
Definition MON_C1 : Z := AF_maybe_online + 0x68.
Definition ss_mh2 : sstate := mkSS MON_C1 sr_atoms mh_regions2 None mh_facts2.

(* The values of atoms 32 .. 40 of run 2's valuation. *)
Definition mh_vals (F : Z) (Bw : list byte) : list word :=
  [Z_to_bv 64 SHADOW_OFF; Z_to_bv 64 (SHADOW_OFF + F / 8); Z_to_bv 64 MON_GSH;
   Z_to_bv 64 (TW.u_at Bw MON_O_KA 4); Z_to_bv 64 (TW.u_at Bw MON_O_ST 4);
   Z_to_bv 64 (TW.u_at Bw MON_O_E1 4); Z_to_bv 64 (TW.u_at Bw MON_O_WA 4);
   Z_to_bv 64 (TW.u_at Bw MON_O_RX 8); Z_to_bv 64 (TW.u_at Bw MON_O_NK 8)].

(* The value of register r in the machine state of a symbolic state HS. *)
Ltac mh_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | ?T => idtac "mh_reg: no match for" T; fail
  end.

(* ------------------------------------------------------------------ *)
(* 2. The model on this path                                           *)
(* ------------------------------------------------------------------ *)

Lemma mh_rng4 : forall Bw k, 0 <= TW.u_at Bw k 4 < 2 ^ 32.
Proof. intros Bw k. exact (TWL.u_at_range Bw k 4). Qed.
Lemma mh_rng8 : forall Bw k, 0 <= TW.u_at Bw k 8 < 2 ^ 64.
Proof. intros Bw k. exact (TWL.u_at_range Bw k 8). Qed.

(* A 4-byte field, sign-extended by `lw`, against a small literal: the model's signed accessor. *)
Lemma mh_eqb_s32 : forall E Bw n o c, ew E n = Z_to_bv 64 (TW.u_at Bw o 4) -> 0 <= c < 2 ^ 31 ->
  bv_eqb (sv_denot E (SExt true 32 (SOff n 0))) (sv_denot E (SLit c)) = (TW.s32_at Bw o =? c).
Proof.
intros E Bw n o c H Hc. unfold TW.s32_at. cbn [sv_denot]. rewrite H.
pose proof (mh_rng4 Bw o) as R.
rewrite unsigned_lit_small by lia. rewrite Z.add_0_r.
rewrite Mem.sext_small, Mem.signed_of_extract by lia.
rewrite unsigned_lit_small by lia.
unfold bv_eqb. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
pose proof (bv_swrap_in_range 32 (TW.u_at Bw o 4) ltac:(discriminate)) as Rs.
change (bv_half_modulus 32) with (2 ^ 31) in Rs.
rewrite (Z.mod_small c (2 ^ 64)) by lia.
destruct (Z.eqb_spec (bv_swrap 32 (TW.u_at Bw o 4)) c) as [Heq | Hne].
- rewrite Heq, (Z.mod_small c (2 ^ 64)) by lia. apply Z.eqb_refl.
- apply Z.eqb_neq. intros HH. apply Hne.
  destruct (Z_lt_le_dec (bv_swrap 32 (TW.u_at Bw o 4)) 0) as [Hneg | Hpos].
  + rewrite <- (Z.mod_unique (bv_swrap 32 (TW.u_at Bw o 4)) (2 ^ 64) (-1)
      (bv_swrap 32 (TW.u_at Bw o 4) + 2 ^ 64)) in HH by lia. lia.
  + rewrite (Z.mod_small (bv_swrap 32 (TW.u_at Bw o 4)) (2 ^ 64)) in HH by lia. exact HH.
Qed.

Lemma mh_br_ne : forall E Bw n o c, ew E n = Z_to_bv 64 (TW.u_at Bw o 4) -> 0 <= c < 2 ^ 31 ->
  branch_taken BC_NE (sv_denot E (SExt true 32 (SOff n 0))) (sv_denot E (SLit c)) = negb (TW.s32_at Bw o =? c).
Proof. intros. cbn [branch_taken]. rewrite (mh_eqb_s32 E Bw n o c); [reflexivity | assumption | assumption]. Qed.
Lemma mh_br_eq : forall E Bw n o c, ew E n = Z_to_bv 64 (TW.u_at Bw o 4) -> 0 <= c < 2 ^ 31 ->
  branch_taken BC_EQ (sv_denot E (SExt true 32 (SOff n 0))) (sv_denot E (SLit c)) = (TW.s32_at Bw o =? c).
Proof. intros. cbn [branch_taken]. exact (mh_eqb_s32 E Bw n o c ltac:(assumption) ltac:(assumption)). Qed.

(* The stored word: the model's u64 (S_last_rx_us Bw + ms_m (S_cfg_keepalive_ms Bw)). *)
Definition MON_NKV (Bw : list byte) : Z := (TW.u_at Bw MON_O_KA 4 * 1000 + TW.u_at Bw MON_O_RX 8) mod 2 ^ 64.
Lemma mh_nkv : forall Bw,
  TS0.u64 (TW.u_at Bw MON_O_RX 8 + TS0.ms_m (TW.u_at Bw MON_O_KA 4)) = MON_NKV Bw.
Proof.
intros Bw. unfold MON_NKV, TS0.ms_m, TS0.u64.
rewrite Zplus_mod_idemp_r, (Z.add_comm (TW.u_at Bw MON_O_RX 8)). reflexivity.
Qed.
Lemma mh_store_val : forall E Bw, ew E 35 = Z_to_bv 64 (TW.u_at Bw MON_O_KA 4) ->
  ew E 39 = Z_to_bv 64 (TW.u_at Bw MON_O_RX 8) ->
  bv_unsigned (sv_denot E (SAlu ALU_ADD (SMd M_MUL (SOff 35 0) (SLit 1000)) (SOff 39 0))) = MON_NKV Bw.
Proof.
intros E Bw H35 H39. pose proof (mh_rng4 Bw MON_O_KA) as R35. pose proof (mh_rng8 Bw MON_O_RX) as R39.
cbn [sv_denot alu64 alu mul_div]. rewrite H35, H39, !unsigned_lit_small by lia. rewrite !Z.add_0_r.
rewrite bv_add_unsigned, bv_mul_unsigned, !Z_to_bv_unsigned.
unfold bv_wrap, MON_NKV. change (bv_modulus 64) with (2 ^ 64).
rewrite (Z.mod_small (TW.u_at Bw MON_O_KA 4) (2 ^ 64)) by lia.
rewrite (Z.mod_small (TW.u_at Bw MON_O_RX 8) (2 ^ 64)) by lia.
rewrite (Z.mod_small 1000 (2 ^ 64)) by lia.
rewrite Zplus_mod_idemp_l. reflexivity.
Qed.

(* maybeon_w1 Bw in closed form, and its state (the store misses s + 112). *)
Lemma mh_wlen : forall Bw : list byte, length Bw = Z.to_nat TW.W_LEN -> Z.of_nat (length Bw) = 65616.
Proof. intros Bw HL. rewrite HL. reflexivity. Qed.
Lemma mh_w1 : forall Bw,
  maybeon_w1 Bw = TW.upd Bw MON_O_NK (TW.put 8 (TS0.u64 (TW.u_at Bw MON_O_RX 8 + TS0.ms_m (TW.u_at Bw MON_O_KA 4)))).
Proof. intros Bw. reflexivity. Qed.
Lemma mh_w1_state : forall Bw, length Bw = Z.to_nat TW.W_LEN -> TW.S_state (maybeon_w1 Bw) = TW.S_state Bw.
Proof.
intros Bw HL. pose proof (mh_wlen Bw HL) as HLz.
unfold maybeon_w1, TW.set_S_next_keepalive_us, TW.S_state.
rewrite TWL.s32_at_upd_out; [reflexivity | | | |];
  rewrite ?TWL.length_put, ?HLz; unfold TW.A_S_next_keepalive_us, TW.A_S_state, TW.OFF_g_s; lia.
Qed.
Lemma mh_w1_len : forall Bw, length Bw = Z.to_nat TW.W_LEN -> length (maybeon_w1 Bw) = Z.to_nat TW.W_LEN.
Proof.
intros Bw HL. pose proof (mh_wlen Bw HL) as HLz.
unfold maybeon_w1, TW.set_S_next_keepalive_us.
rewrite TWL.length_upd_put; [exact HL | unfold TW.A_S_next_keepalive_us, TW.OFF_g_s; lia |].
rewrite HLz. unfold TW.A_S_next_keepalive_us, TW.OFF_g_s. lia.
Qed.
Lemma mh_go : forall Bw, maybeon_go Bw =
  ((TW.s32_at Bw MON_O_ST =? 1) && negb (TW.s32_at Bw MON_O_WA =? 0) &&
   negb (TW.s32_at Bw MON_O_E1 =? 0))%bool.
Proof. intros Bw. reflexivity. Qed.
Lemma mh_go_false : forall Bw, maybeon_go Bw = false ->
  forall I F, TSS.maybe_online_m I F Bw = Some (Bw, tt).
Proof. intros Bw H I F. rewrite (maybeon_model I F Bw), H. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* 3. The walk                                                         *)
(* ------------------------------------------------------------------ *)

Section mh. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

Lemma mh_vals_img : VAL (A_OBJ 1) = FCells.GOT_CELL_K /\ VAL (A_OBJ 93) = FCells.CELL_K /\
  VAL (A_OBJ 0) = FCells.GOT_UAR /\ VAL (A_OBJ 94) = FCells.UAR /\
  BASE + AF_maybe_online = transport_sigma TS_maybe_online.
Proof. vm_compute. repeat split. Qed.

(* The four image regions hold what transport_cells says they hold, at any AR state. *)
Lemma mh_img_ok : forall ly S (W : world segs) mem md (E : env),
  transport_cells B -> @AR rc segs B ly S W mem md ->
  ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1)) -> ew E (A_OBJ 93) = Z_to_bv 64 (VAL (A_OBJ 93)) ->
  ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0)) -> ew E (A_OBJ 94) = Z_to_bv 64 (VAL (A_OBJ 94)) ->
  ew E 32 = Z_to_bv 64 SHADOW_OFF ->
  Forall (region_ok segs E (mrestrict (w_H W) mem)) mh_img_regions /\
  pairwise_disjoint E mh_img_regions.
Proof.
  intros ly S W mem md E HCELLS HAR E1 E93 E0 E94 E32.
  destruct (HCELLS ly) as (I1 & I2 & _ & _ & _ & I6 & I7 & _).
  destruct mh_vals_img as (V1 & V93 & V0 & V94 & _).
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
    intros j Hj. exact (H6 j Hj). }
  assert (VB : forall n v0, ew E n = Z_to_bv 64 v0 -> 0 <= v0 < 2 ^ 64 -> base_val E (Some n) = v0)
    by (intros n v0 Hn Hv0; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hv0).
  split.
  - unfold mh_img_regions, got_regionP, bcell_regionP, mh_got_uar, mh_uar_cell.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    + rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E1) by (rewrite V1; unfold FCells.GOT_CELL_K; lia).
      split; [rewrite V1; unfold FCells.GOT_CELL_K; lia|].
      split; [rewrite V1; unfold FCells.GOT_CELL_K; lia|].
      split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val segs E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 93) 0) (VAL (A_OBJ 93)));
      [cbn [sv_denot]; rewrite E93, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | rewrite V93; unfold FCells.CELL_K; cbn; lia | cbn; lia |].
      rewrite Z.add_0_r, V1, V93. exact (val_mem_of_rdword segs (w_H W) mem _ _ Kgot).
    + rewrite (VB (A_OBJ 93) (VAL (A_OBJ 93)) E93) by (rewrite V93; unfold FCells.CELL_K; lia).
      split; [rewrite V93; unfold FCells.CELL_K; lia|].
      split; [rewrite V93; unfold FCells.CELL_K; lia|].
      split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val segs E _ (VAL (A_OBJ 93)) 0 8 (SOff 32 0) SHADOW_OFF);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | unfold SHADOW_OFF; cbn; lia | cbn; lia |].
      rewrite Z.add_0_r, V93. exact (val_mem_of_rdword segs (w_H W) mem _ _ Kcell).
    + rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E0) by (rewrite V0; unfold FCells.GOT_UAR; lia).
      split; [rewrite V0; unfold FCells.GOT_UAR; lia|].
      split; [rewrite V0; unfold FCells.GOT_UAR; lia|].
      split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val segs E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 94) 0) (VAL (A_OBJ 94)));
      [cbn [sv_denot]; rewrite E94, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | rewrite V94; unfold FCells.UAR; cbn; lia | cbn; lia |].
      rewrite Z.add_0_r, V0, V94. exact (val_mem_of_rdword segs (w_H W) mem _ _ Kguar).
    + rewrite (VB (A_OBJ 94) (VAL (A_OBJ 94)) E94) by (rewrite V94; unfold FCells.UAR; lia).
      split; [rewrite V94; unfold FCells.UAR; lia|].
      split; [rewrite V94; unfold FCells.UAR; lia|].
      split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val segs E _ (VAL (A_OBJ 94)) 0 4 (SLit 1) 1); [reflexivity | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r, V94. exact (can_val_mem_of_rd32 segs (w_H W) mem _ _ Kuar).
  - apply pairwise_disjoint_of_extents.
    unfold mh_img_regions, got_regionP, bcell_regionP, mh_got_uar, mh_uar_cell, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E1) by (rewrite V1; unfold FCells.GOT_CELL_K; lia).
    rewrite (VB (A_OBJ 93) (VAL (A_OBJ 93)) E93) by (rewrite V93; unfold FCells.CELL_K; lia).
    rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E0) by (rewrite V0; unfold FCells.GOT_UAR; lia).
    rewrite (VB (A_OBJ 94) (VAL (A_OBJ 94)) E94) by (rewrite V94; unfold FCells.UAR; lia).
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    rewrite V1, V93, V0, V94. unfold FCells.GOT_CELL_K, FCells.CELL_K, FCells.GOT_UAR, FCells.UAR.
    repeat split; first [exact I | lia].
Qed.

Definition mh_E (regs : bvmap 5 word) (extra : list word) : env := Eimg (PI := PI_transport) (Ereg regs extra).

Lemma mh_env_img : forall regs extra, img_env VAL A_LIM (mh_E regs extra).
Proof. intros regs extra. unfold mh_E. apply Eimg_env. Qed.
Lemma mh_ew_reg : forall regs extra n (r : bv 5), Z.of_nat n = bv_unsigned r ->
  ew (mh_E regs extra) n = YK11.getr regs r.
Proof. intros. unfold mh_E. apply can_ew_Eimg_Ereg_nat. assumption. Qed.
Lemma mh_ew_extra : forall regs extra j, (j < length extra)%nat -> (j < 200)%nat ->
  ew (mh_E regs extra) (32 + j) = nth j extra (Z_to_bv 64 0).
Proof.
  intros regs extra j Hj Hj2. unfold mh_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra.
Qed.
Lemma mh_ew_obj : forall regs extra i, (i < 95)%nat -> ew (mh_E regs extra) (A_OBJ i) = Z_to_bv 64 (VAL (A_OBJ i)).
Proof. intros. unfold mh_E. apply Eimg_img. unfold A_OBJ, A_TEXT, A_LIM. lia. Qed.

(* The entry state of run 1. *)
Lemma mh_entry1 : forall ly S (W : world segs) regs mem md,
  transport_cells B -> @AR rc segs B ly S W mem md ->
  (forall a, spZ regs - MAYBEON_FRAME <= a < spZ regs -> apresent (w_H W) mem a) ->
  2 ^ 46 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 -> YK11.getr regs 10 = w64 MAYBEON_S ->
  st_ok_pi segs VAL (mh_E regs [w64 SHADOW_OFF]) ss_mh1
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + AF_maybe_online)) mem (YK11.seg_rom segs))).
Proof.
  intros ly S W regs mem md HCELLS HAR Hpres Hsp Hsp16 H10.
  set (E := mh_E regs [w64 SHADOW_OFF]).
  assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF)
    by (exact (mh_ew_extra regs [w64 SHADOW_OFF] 0 ltac:(cbn; lia) ltac:(lia))).
  assert (Usp : bv_unsigned (ew E 2) = spZ regs)
    by (unfold E; rewrite (mh_ew_reg regs [w64 SHADOW_OFF] 2 2%bv eq_refl); reflexivity).
  assert (E10 : ew E 10 = Z_to_bv 64 MAYBEON_S)
    by (unfold E; rewrite (mh_ew_reg regs [w64 SHADOW_OFF] 10 10%bv eq_refl); exact H10).
  assert (U10 : bv_unsigned (ew E 10) = MAYBEON_S)
    by (rewrite E10; apply unsigned_lit_small; unfold MAYBEON_S, TA_g_s; lia).
  destruct (mh_img_ok ly S W mem md E HCELLS HAR
    (mh_ew_obj regs [w64 SHADOW_OFF] 1 ltac:(lia)) (mh_ew_obj regs [w64 SHADOW_OFF] 93 ltac:(lia))
    (mh_ew_obj regs [w64 SHADOW_OFF] 0 ltac:(lia)) (mh_ew_obj regs [w64 SHADOW_OFF] 94 ltac:(lia)) E32)
    as [HRs HPd].
  destruct mh_vals_img as (V1 & V93 & V0 & V94 & _).
  assert (VB : forall n v0, ew E n = Z_to_bv 64 v0 -> 0 <= v0 < 2 ^ 64 -> base_val E (Some n) = v0)
    by (intros n v0 Hn Hv0; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hv0).
  rewrite restrict_mkst_fx. unfold ss_mh1, mh_regions1.
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [| exact HRs].
    unfold stack_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite Usp. unfold MAYBEON_FRAME.
    split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply Hpres. unfold MAYBEON_FRAME. lia.
  - unfold mh_img_regions in *. apply pairwise_disjoint_of_extents.
    unfold stack_region, got_regionP, bcell_regionP, mh_got_uar, mh_uar_cell, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) (mh_ew_obj regs [w64 SHADOW_OFF] 1 ltac:(lia)))
      by (rewrite V1; unfold FCells.GOT_CELL_K; lia).
    rewrite (VB (A_OBJ 93) (VAL (A_OBJ 93)) (mh_ew_obj regs [w64 SHADOW_OFF] 93 ltac:(lia)))
      by (rewrite V93; unfold FCells.CELL_K; lia).
    rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) (mh_ew_obj regs [w64 SHADOW_OFF] 0 ltac:(lia)))
      by (rewrite V0; unfold FCells.GOT_UAR; lia).
    rewrite (VB (A_OBJ 94) (VAL (A_OBJ 94)) (mh_ew_obj regs [w64 SHADOW_OFF] 94 ltac:(lia)))
      by (rewrite V94; unfold FCells.UAR; lia).
    cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    rewrite V1, V93, V0, V94.
    unfold FCells.GOT_CELL_K, FCells.CELL_K, FCells.GOT_UAR, FCells.UAR, MAYBEON_FRAME.
    repeat split; first [exact I | lia].
  - unfold mh_facts1, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E32, E10, !unsigned_lit_small by (unfold SHADOW_OFF, MAYBEON_S, TA_g_s; lia).
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I;
      first [unfold SHADOW_OFF; lia | unfold MAYBEON_S, TA_g_s; lia | lia].
Qed.

(* g_s's 24 shadow bytes at and below granule 23 are 0 (trans_maybeon_cells). *)
Lemma mh_gsh_zero : forall ly S (W : world segs) mem md j,
  trans_maybeon_cells B -> @AR rc segs B ly S W mem md -> 0 <= j < 24 ->
  aview segs (w_H W) mem (MON_GSH + j) = Some 0.
Proof.
  intros ly S W mem md j HZ HAR Hj.
  assert (Hz := decode_zshadow_rd B ly S W mem md MAYBEON_S (MAYBEON_S + TW.SZ_g_s) (MAYBEON_S + 8 * j) HAR
    ltac:(replace (MAYBEON_S + 8 * j) with ((769848 + j) * 8) by (unfold MAYBEON_S, TA_g_s; lia);
          apply Z_mod_mult)
    ltac:(lia) ltac:(unfold TW.SZ_g_s; lia) HZ).
  replace (MON_GSH + j) with (FCells.shadow_addr (MAYBEON_S + 8 * j)); [exact Hz|].
  unfold FCells.shadow_addr, FCells.ASAN_K, MON_GSH, SHADOW_OFF, MAYBEON_S, TA_g_s.
  replace (6158784 + 8 * j) with ((769848 + j) * 8) by lia.
  rewrite Z.div_mul by lia. replace (6158784 / 8) with 769848 by reflexivity. lia.
Qed.

(* The numerals the geometry of the two states needs; lia never divides a closed numeral itself. *)
Lemma mh_nums : MON_GSH = 2148220728 /\ MAYBEON_S = 6158784 /\ SHADOW_OFF = 2147450880 /\
  TW.SZ_g_s = 18264 /\ kLowShadowBeg = 2147446784 /\ kHighMemBeg = 17594333495296 /\
  kLowMemEnd = 2147450880 /\ MAYBEON_S / 8 = 769848 /\ MAYBEON_FRAME = 96 /\
  MAYBEON_ALIGN = 16 /\ ESTACK = 4096 /\ MAYBEON_CID = 2 /\ MON_FBYTES = 256 /\
  TG.G_HARNESS_LO = 6156416 /\ TG.G_HARNESS_HI = 6238608 /\ TA_g_s = 6158784.
Proof. repeat split; reflexivity. Qed.
Ltac mh_lia :=
  let HN := fresh "HN" in pose proof mh_nums as HN;
  destruct HN as (?EG & ?ESg & ?ESH & ?ESZ & ?ELS & ?EHM & ?ELM & ?EQS & ?EFR & ?EAL & ?EES & ?ECID & ?EFB
    & ?EGLO & ?EGHI & ?ETAG);
  lia.

(* g_s's payload is a range of G. *)
Lemma mh_inG : forall a, MAYBEON_S <= a < MAYBEON_S + TW.SZ_g_s -> inG TG.G_HARNESS a.
Proof.
intros a Ha. unfold inG. apply Exists_exists. exists (TA_g_s, TW.SZ_g_s).
split; [exact (TMAP_A_in_G TW.OFF_g_s TA_g_s TW.SZ_g_s TMAP_A_g_s)|].
unfold in_zr. cbn [fst snd]. unfold MAYBEON_S in Ha. lia.
Qed.

(* The entry state of run 2, at +0x68. *)
Lemma mh_entry2 : forall lyc Sc (W : world segs) regs2 mem2 md2 Bw F sp1,
  trans_maybeon_cells B -> @AR rc segs B lyc Sc W mem2 md2 ->
  tw_at TMAP_A (aview segs (w_H W) mem2) Bw ->
  YK11.getr regs2 2 = Z_to_bv 64 sp1 -> YK11.getr regs2 9 = Z_to_bv 64 sp1 ->
  YK11.getr regs2 10 = w64 F -> YK11.getr regs2 19 = w64 MAYBEON_S -> YK11.getr regs2 24 = w64 SHADOW_OFF ->
  2 ^ 46 <= sp1 <= 2 ^ 47 -> sp1 mod 32 = 0 ->
  4096 <= F -> F mod 64 = 0 -> F + 256 <= alloc_ceiling ->
  (F + 256 <= kLowShadowBeg \/ kHighMemBeg <= F) ->
  (F + 256 <= MAYBEON_S \/ MAYBEON_S + TW.SZ_g_s <= F) ->
  alloc_ceiling <= sp1 - 4096 ->
  (forall a, sp1 <= a < sp1 + 8 -> apresent (w_H W) mem2 a) ->
  (forall a, F <= a < F + 24 -> apresent (w_H W) mem2 a) ->
  (forall j, 0 <= j < 20 -> apresent (w_H W) mem2 (SHADOW_OFF + F / 8 + j)) ->
  st_ok_pi segs VAL (mh_E regs2 (mh_vals F Bw)) ss_mh2
    (restrict (w_H W) (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + MON_C1)) mem2 (YK11.seg_rom segs))).
Proof.
  intros lyc Sc W regs2 mem2 md2 Bw F sp1 HMC HAR Htw R2 R9 R10 R19 R24 Hsp Hsp32 HF0 HF64 HFc Happ HFg Hce
    Hpsl Hphd Hpsh.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  set (E := mh_E regs2 (mh_vals F Bw)).
  assert (HQ : F = 8 * (F / 8)).
  { pose proof (Z.div_mod F 64 ltac:(lia)) as D. rewrite HF64, Z.add_0_r in D.
    assert (E8 : F / 8 = 8 * (F / 64)).
    { rewrite D at 1. replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by lia. apply Z.div_mul. lia. }
    rewrite E8. lia. }
  assert (HQ0 : 0 <= F / 8) by (apply Z.div_pos; lia).
  assert (HQc : F / 8 <= alloc_ceiling) by lia.
  assert (EX : forall j, (j < 9)%nat -> ew E (32 + j) = nth j (mh_vals F Bw) (Z_to_bv 64 0))
    by (intros j Hj; unfold E; apply mh_ew_extra; [cbn; lia | lia]).
  pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
  pose proof (EX 2%nat ltac:(lia)) as E34. pose proof (EX 3%nat ltac:(lia)) as E35.
  pose proof (EX 4%nat ltac:(lia)) as E36. pose proof (EX 5%nat ltac:(lia)) as E37.
  pose proof (EX 6%nat ltac:(lia)) as E38. pose proof (EX 7%nat ltac:(lia)) as E39.
  pose proof (EX 8%nat ltac:(lia)) as E40.
  cbn [Nat.add nth mh_vals] in E32, E33, E34, E35, E36, E37, E38, E39, E40.
  assert (E2' : ew E 2 = Z_to_bv 64 sp1) by (unfold E; rewrite (mh_ew_reg regs2 _ 2 2%bv eq_refl); exact R2).
  assert (E9 : ew E 9 = Z_to_bv 64 sp1) by (unfold E; rewrite (mh_ew_reg regs2 _ 9 9%bv eq_refl); exact R9).
  assert (E10 : ew E 10 = Z_to_bv 64 F) by (unfold E; rewrite (mh_ew_reg regs2 _ 10 10%bv eq_refl); exact R10).
  assert (E19 : ew E 19 = Z_to_bv 64 MAYBEON_S)
    by (unfold E; rewrite (mh_ew_reg regs2 _ 19 19%bv eq_refl); exact R19).
  assert (E24 : ew E 24 = Z_to_bv 64 SHADOW_OFF)
    by (unfold E; rewrite (mh_ew_reg regs2 _ 24 24%bv eq_refl); exact R24).
  assert (U2 : bv_unsigned (ew E 2) = sp1) by (rewrite E2'; apply unsigned_lit_small; lia).
  assert (U9 : bv_unsigned (ew E 9) = sp1) by (rewrite E9; apply unsigned_lit_small; lia).
  assert (U10 : bv_unsigned (ew E 10) = F) by (rewrite E10; apply unsigned_lit_small; lia).
  assert (U19 : bv_unsigned (ew E 19) = MAYBEON_S)
    by (rewrite E19; apply unsigned_lit_small; mh_lia).
  assert (U33 : bv_unsigned (ew E 33) = SHADOW_OFF + F / 8)
    by (rewrite E33; apply unsigned_lit_small; mh_lia).
  assert (U34 : bv_unsigned (ew E 34) = MON_GSH)
    by (rewrite E34; apply unsigned_lit_small; mh_lia).
  assert (DEN : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n 0) = Z_to_bv 64 v)
    by (intros n v Hn Hv; cbn [sv_denot]; rewrite Hn, unsigned_lit_small, Z.add_0_r by exact Hv; reflexivity).
  assert (VB : forall n v0, ew E n = Z_to_bv 64 v0 -> 0 <= v0 < 2 ^ 64 -> base_val E (Some n) = v0)
    by (intros n v0 Hn Hv0; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hv0).
  pose proof (mh_rng4 Bw MON_O_KA) as RKA. pose proof (mh_rng4 Bw MON_O_ST) as RST.
  pose proof (mh_rng4 Bw MON_O_E1) as RE1. pose proof (mh_rng4 Bw MON_O_WA) as RWA.
  pose proof (mh_rng8 Bw MON_O_RX) as RRX. pose proof (mh_rng8 Bw MON_O_NK) as RNK.
  rewrite restrict_mkst_fx. unfold ss_mh2, mh_regions2.
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil;
    unfold mh_rg_hdr, mh_rg_fsh, mh_rg_slot, mh_rg_gsh, mh_rg_gs, region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    + rewrite (VB 10%nat F E10 ltac:(lia)). split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Hphd. lia.
    + rewrite (VB 33%nat (SHADOW_OFF + F / 8) E33 ltac:(mh_lia)).
      split; [mh_lia|]. split; [mh_lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Hpsh. lia.
    + rewrite (VB 9%nat sp1 E9 ltac:(lia)). split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Hpsl. lia.
    + rewrite (VB 34%nat MON_GSH E34 ltac:(mh_lia)).
      split; [mh_lia|].
      split; [mh_lia|].
      split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil;
      match goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?o _) =>
        apply (chunk_ok_val segs E _ MON_GSH o 1 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia |];
        apply AE2y.val_mem1_of_aview; apply (mh_gsh_zero lyc Sc W mem2 md2 o HMC HAR ltac:(lia)) end.
    + rewrite (VB 19%nat MAYBEON_S E19 ltac:(mh_lia)).
      split; [mh_lia|]. split; [mh_lia|].
      split.
      { intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (MAYBEON_S + o) G_HARNESS_rw).
        apply mh_inG. mh_lia. }
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val segs E _ MAYBEON_S 24 4 (SOff 35 0) (TW.u_at Bw MON_O_KA 4));
          [apply DEN; [exact E35 | lia] | cbn; lia | cbn; lia |].
        exact (tw_read_val segs _ TMAP_A Bw TW.OFF_g_s TA_g_s TW.SZ_g_s 24 4 TMAP_A_ok Htw TMAP_A_g_s
          ltac:(lia) ltac:(mh_lia)).
      * apply (chunk_ok_val segs E _ MAYBEON_S 112 4 (SOff 36 0) (TW.u_at Bw MON_O_ST 4));
          [apply DEN; [exact E36 | lia] | cbn; lia | cbn; lia |].
        exact (tw_read_val segs _ TMAP_A Bw TW.OFF_g_s TA_g_s TW.SZ_g_s 112 4 TMAP_A_ok Htw TMAP_A_g_s
          ltac:(lia) ltac:(mh_lia)).
      * apply (chunk_ok_val segs E _ MAYBEON_S 140 4 (SOff 37 0) (TW.u_at Bw MON_O_E1 4));
          [apply DEN; [exact E37 | lia] | cbn; lia | cbn; lia |].
        exact (tw_read_val segs _ TMAP_A Bw TW.OFF_g_s TA_g_s TW.SZ_g_s 140 4 TMAP_A_ok Htw TMAP_A_g_s
          ltac:(lia) ltac:(mh_lia)).
      * apply (chunk_ok_val segs E _ MAYBEON_S 144 4 (SOff 38 0) (TW.u_at Bw MON_O_WA 4));
          [apply DEN; [exact E38 | lia] | cbn; lia | cbn; lia |].
        exact (tw_read_val segs _ TMAP_A Bw TW.OFF_g_s TA_g_s TW.SZ_g_s 144 4 TMAP_A_ok Htw TMAP_A_g_s
          ltac:(lia) ltac:(mh_lia)).
      * apply (chunk_ok_val segs E _ MAYBEON_S 176 8 (SOff 39 0) (TW.u_at Bw MON_O_RX 8));
          [apply DEN; [exact E39 | lia] | cbn; lia | cbn; lia |].
        exact (tw_read_val segs _ TMAP_A Bw TW.OFF_g_s TA_g_s TW.SZ_g_s 176 8 TMAP_A_ok Htw TMAP_A_g_s
          ltac:(lia) ltac:(mh_lia)).
      * apply (chunk_ok_val segs E _ MAYBEON_S 184 8 (SOff 40 0) (TW.u_at Bw MON_O_NK 8));
          [apply DEN; [exact E40 | lia] | cbn; lia | cbn; lia |].
        exact (tw_read_val segs _ TMAP_A Bw TW.OFF_g_s TA_g_s TW.SZ_g_s 184 8 TMAP_A_ok Htw TMAP_A_g_s
          ltac:(lia) ltac:(mh_lia)).
  - apply pairwise_disjoint_of_extents.
    unfold mh_rg_hdr, mh_rg_fsh, mh_rg_slot, mh_rg_gsh, mh_rg_gs, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB 10%nat F E10 ltac:(lia)), (VB 9%nat sp1 E9 ltac:(lia)),
      (VB 33%nat (SHADOW_OFF + F / 8) E33 ltac:(mh_lia)),
      (VB 34%nat MON_GSH E34 ltac:(mh_lia)),
      (VB 19%nat MAYBEON_S E19 ltac:(mh_lia)).
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold MON_GSH, SHADOW_OFF, MAYBEON_S, TA_g_s, TW.SZ_g_s, kLowShadowBeg, kHighMemBeg in *.
    replace (6158784 / 8) with 769848 in * by reflexivity.
    repeat split; first [exact I | lia].
  - unfold mh_facts2, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    assert (U24 : bv_unsigned (ew E 24) = SHADOW_OFF) by (rewrite E24; apply unsigned_lit_small; mh_lia).
    assert (U35 : bv_unsigned (ew E 35) = TW.u_at Bw MON_O_KA 4)
      by (rewrite E35; apply unsigned_lit_small; lia).
    assert (U36 : bv_unsigned (ew E 36) = TW.u_at Bw MON_O_ST 4)
      by (rewrite E36; apply unsigned_lit_small; lia).
    assert (U37 : bv_unsigned (ew E 37) = TW.u_at Bw MON_O_E1 4)
      by (rewrite E37; apply unsigned_lit_small; lia).
    assert (U38 : bv_unsigned (ew E 38) = TW.u_at Bw MON_O_WA 4)
      by (rewrite E38; apply unsigned_lit_small; lia).
    rewrite U2, U9, U10, U19, U24, U33, U34, U35, U36, U37, U38.
    change (2 ^ 5) with 32. change (2 ^ 6) with 64. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end;
      try exact I; try reflexivity; try assumption; try mh_lia.
    unfold mh_alias. cbn [alias_ok]. split; [|split; [|exact I]].
    + etransitivity;
      [ apply (denot_shx E 10 24 0 F SHADOW_OFF E10 E24 ltac:(lia) ltac:(lia) ltac:(mh_lia) ltac:(mh_lia))
      | rewrite Z.add_0_r; symmetry; apply (DEN 33%nat (SHADOW_OFF + F / 8) E33 ltac:(mh_lia)) ].
    + etransitivity;
      [ apply (denot_shx E 19 24 0 MAYBEON_S SHADOW_OFF E19 E24 ltac:(mh_lia) ltac:(lia) ltac:(mh_lia)
          ltac:(mh_lia))
      | rewrite Z.add_0_r; symmetry; apply (DEN 34%nat MON_GSH E34 ltac:(mh_lia)) ].
Qed.

(* The write right of run 1: the 96-byte frame below the entry sp (a byte of the call's own stack window), and the
   four read-only image regions. *)
Ltac mh_awr1 Usp :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  apply awr_ok_x_cons;
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite Usp in Ha;
    left; split; [unfold awr_byte; left; mh_lia | mh_lia] |];
  repeat (apply awr_ok_x_cons;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; mh_lia |]);
  apply awr_ok_x_nil.

(* The write right of run 2: the frame's header and its shadow bytes (bytes of the own frame), the machine frame's
   slot (the call's stack window), g_s's shadow (no writable byte) and g_s's next_keepalive_us (a byte of G). *)
Ltac mh_awr2 U10 U33 U9 U19 pos Fv :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  apply (awr_ok_x_cons_own _ _ _ _ _ _ _ _ _ _ _ _ MAYBEON_CID pos);
  [ left; reflexivity
  | let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U10 in Ha;
    left; unfold in_zr; cbn [fst snd]; change (fs_frame_bytes MAYBEON_CID) with 256; fold Fv; mh_lia |];
  apply (awr_ok_x_cons_own _ _ _ _ _ _ _ _ _ _ _ _ MAYBEON_CID pos);
  [ left; reflexivity
  | let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U33 in Ha;
    right; unfold in_zr; cbn [fst snd]; change (fs_frame_bytes MAYBEON_CID / 8) with 32;
    unfold shadow_addr; fold Fv; mh_lia |];
  apply awr_ok_x_cons;
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U9 in Ha;
    left; split; [unfold awr_byte; left; mh_lia | mh_lia] |];
  apply awr_ok_x_cons;
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; mh_lia |];
  apply awr_ok_x_cons_g;
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U19 in Ha; apply mh_inG; mh_lia |];
  apply awr_ok_x_nil.

(* The bytes run 2 may change: the frame's header, the frame's 20 shadow bytes, the machine frame's slot and
   g_s's next_keepalive_us (the windows of mh_regions2). *)
Definition MH_ZS (F sp1 a : Z) : Prop :=
  (F <= a < F + 24) \/ (SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 20) \/
  (sp1 <= a < sp1 + 8) \/ (MAYBEON_S + 184 <= a < MAYBEON_S + 192).

(* The kept bytes of one run over the regions of ss_mh2 (their windows are MH_ZS). *)
Ltac mh_kept_tac KAn Fv Sv U10 U33 U9 U19 U34 :=
  lazymatch goal with
  | HFrx : frame_of ?E ?rs (mrestrict (w_H ?Wx) ?mo) (mrestrict (w_H ?Wx) ?mn) |- _ =>
    assert (KAn : forall a, 0 <= a < 2 ^ 64 -> ~ MH_ZS Fv Sv a ->
      aview segs (w_H Wx) mn a = aview segs (w_H Wx) mo a);
    [ intros aa Haa Hnn;
      apply (kept_of_frame E rs (w_H Wx) mo mn (MH_ZS Fv Sv) HFrx); [| exact Haa | exact Hnn];
      let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in
      let x := fresh "x" in let Hin := fresh "Hin" in let Hx := fresh "Hx" in
      intros b wlo whi x Hin Hx; cbv beta;
      lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end;
      cbn [In] in Hin;
      repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx;
        rewrite ?U10, ?U33, ?U9, ?U19, ?U34 in Hx; unfold MH_ZS;
        first [left; lia | right; left; lia | right; right; left; lia | right; right; right; lia] |]);
      destruct Hin
    | ]
  end.


(* Carry the kept facts of one more run of mh_regions2. *)
Ltac mh_chain KA GA U10 U33 U9 U19 U34 Fv Sv Mem0 :=
  lazymatch goal with
  | HFrx : frame_of ?E _ (mrestrict (w_H ?Wx) ?mo) (mrestrict (w_H ?Wx) ?mn) |- _ =>
    lazymatch goal with
    | HGx : mem_grows (mrestrict (w_H Wx) mo) (mrestrict (w_H Wx) mn) |- _ =>
      let K2 := fresh "K2" in let G2 := fresh "G2" in let K3 := fresh "K3" in
      mh_kept_tac K2 Fv Sv U10 U33 U9 U19 U34;
      assert (G2 : forall a, apresent (w_H Wx) Mem0 a -> apresent (w_H Wx) mn a)
        by (intros aa Haa; exact (apresent_grows (w_H Wx) mo mn aa HGx (GA aa Haa)));
      assert (K3 : forall a, 0 <= a < 2 ^ 64 -> ~ MH_ZS Fv Sv a ->
          aview segs (w_H Wx) mn a = aview segs (w_H Wx) Mem0 a)
        by (intros aa Haa Hnn; exact (eq_trans (K2 aa Haa Hnn) (KA aa Haa Hnn)));
      clear KA GA K2; rename K3 into KA; rename G2 into GA
    end
  end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H end;
  repeat match goal with H : mem_grows _ _ |- _ => clear H end.

(* The registers the release reads, at a state of run 2. *)
Ltac mh_regs_r HS HR Fv Sv Rg Hgpx Htpx E2x E3x E4x E8x E9x E10x E26x E27x E33x :=
  let V2 := fresh "V2" in let V3 := fresh "V3" in let V4 := fresh "V4" in let V8 := fresh "V8" in
  let V9 := fresh "V9" in let V18 := fresh "V18" in let V22 := fresh "V22" in let V23 := fresh "V23" in
  let V26 := fresh "V26" in let V27 := fresh "V27" in
  mh_reg HS (2%bv : bv 5) (w64 Sv) V2
    ltac:(cbn [sv_denot]; rewrite E2x, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity);
  mh_reg HS (3%bv : bv 5) (w64 (as_gp B)) V3
    ltac:(cbn [sv_denot]; rewrite E3x, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity);
  mh_reg HS (4%bv : bv 5) (w64 (as_tp B)) V4
    ltac:(cbn [sv_denot]; rewrite E4x, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity);
  mh_reg HS (8%bv : bv 5) (w64 (spZ Rg)) V8
    ltac:(cbn [sv_denot]; rewrite E8x, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity);
  mh_reg HS (9%bv : bv 5) (w64 Sv) V9
    ltac:(cbn [sv_denot]; rewrite E9x, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity);
  mh_reg HS (18%bv : bv 5) (w64 Fv) V18
    ltac:(cbn [sv_denot]; rewrite E10x, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity);
  mh_reg HS (22%bv : bv 5) (w64 (SHADOW_OFF + Fv / 8)) V22
    ltac:(cbn [sv_denot]; rewrite E33x, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity);
  mh_reg HS (23%bv : bv 5) (w64 Fv) V23
    ltac:(cbn [sv_denot]; rewrite E10x, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity);
  mh_reg HS (26%bv : bv 5) (YK11.getr Rg 26) V26
    ltac:(cbn [sv_denot]; rewrite E26x, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity);
  mh_reg HS (27%bv : bv 5) (YK11.getr Rg 27) V27
    ltac:(cbn [sv_denot]; rewrite E27x, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity);
  lazymatch type of V2 with YK11.getr (ms_regs ?Msx) _ = _ =>
  assert (HR : mon_regs_rel Rg (ms_regs Msx) Sv Fv) end;
  [ unfold mon_regs_rel;
    split; [exact V2|]; split; [rewrite V3; symmetry; exact Hgpx|];
    split; [rewrite V4; symmetry; exact Htpx|]; split; [exact V8|]; split; [exact V9|];
    split; [exact V18|]; split; [exact V22|]; split; [exact V23|];
    split; [exact V26 | exact V27]
  | clear V2 V3 V4 V8 V9 V18 V22 V23 V26 V27 ].

(* The registers the notice path also reads. *)
Ltac mh_regs_n HS HR Fv Sv Rg Hgpx Htpx E2x E3x E4x E8x E9x E10x E19x E24x E26x E27x E33x :=
  let HRr := fresh "HRr" in
  mh_regs_r HS HRr Fv Sv Rg Hgpx Htpx E2x E3x E4x E8x E9x E10x E26x E27x E33x;
  let V19 := fresh "V19" in let V20 := fresh "V20" in let V21 := fresh "V21" in
  let V24 := fresh "V24" in let V25 := fresh "V25" in
  mh_reg HS (19%bv : bv 5) (w64 MAYBEON_S) V19
    ltac:(cbn [sv_denot]; rewrite E19x, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity);
  mh_reg HS (20%bv : bv 5) (w64 (MAYBEON_S + 112)) V20
    ltac:(cbn [sv_denot]; rewrite E19x, unsigned_lit_small by mh_lia; reflexivity);
  mh_reg HS (21%bv : bv 5) (w64 (Fv + 32)) V21
    ltac:(cbn [sv_denot]; rewrite E10x, unsigned_lit_small by mh_lia; reflexivity);
  mh_reg HS (24%bv : bv 5) (w64 SHADOW_OFF) V24
    ltac:(cbn [sv_denot]; rewrite E24x, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity);
  mh_reg HS (25%bv : bv 5) (w64 (SHADOW_OFF + (MAYBEON_S + 112) / 8)) V25
    ltac:(exact (denot_shx _ 19 24 112 MAYBEON_S SHADOW_OFF E19x E24x ltac:(mh_lia) ltac:(lia)
      ltac:(mh_lia) ltac:(mh_lia)));
  lazymatch type of V19 with YK11.getr (ms_regs ?Msx) _ = _ =>
  assert (HR : mon_regs_ntc Rg (ms_regs Msx) Sv Fv) end;
  [ unfold mon_regs_ntc;
    split; [exact HRr|]; split; [exact V19|]; split; [exact V20|]; split; [exact V21|];
    split; [exact V24 | exact V25]
  | clear HRr V19 V20 V21 V24 V25 ].

Lemma mh_den : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n 0) = Z_to_bv 64 v.
Proof.
intros E n v Hn Hv. cbn [sv_denot]. rewrite Hn, unsigned_lit_small, Z.add_0_r by exact Hv. reflexivity.
Qed.

(* At a release exit the store at s + 184 has not run: g_s's eight bytes there are still the world's, read off the
   run's own region. *)
Lemma mh_tw_rel : forall (W : world segs) E (mo mn : word -> option byte) Bw F sp1,
  gx_ok segs B TG.G_HARNESS ->
  bv_unsigned (ew E 19) = MAYBEON_S -> ew E 40 = Z_to_bv 64 (TW.u_at Bw MON_O_NK 8) ->
  4096 <= F -> F + 256 <= alloc_ceiling -> (forall a, F <= a < F + 256 -> ~ in_img segs a) ->
  alloc_ceiling <= sp1 ->
  tw_at TMAP_A (aview segs (w_H W) mo) Bw ->
  region_ok segs E (mrestrict (w_H W) mn) mh_rg_gs ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ MH_ZS F sp1 a -> aview segs (w_H W) mn a = aview segs (w_H W) mo a) ->
  tw_at TMAP_A (aview segs (w_H W) mn) Bw.
Proof.
intros W E mo mn Bw F sp1 HGX U19 E40 HF0 HFc HFimg Hsp Htw RG KA.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Himg : forall y, tw_in TMAP_A y -> in_img segs y).
{ intros y (o & b & n & Hin & Hy). refine (proj1 (HGX y _)).
  unfold inG. apply Exists_exists. exists (b, n).
  split; [exact (TMAP_A_in_G o b n Hin) | unfold in_zr; cbn [fst snd]; lia]. }
pose proof (mh_rng8 Bw MON_O_NK) as RNK.
assert (HV : val_mem segs (mrestrict (w_H W) mn) (MAYBEON_S + 184) 8 (TW.u_at Bw MON_O_NK 8)).
{ apply (can_field_of_region E _ 19 MAYBEON_S _ 24 192 184 192 184 8%N (SOff 40 0)
    (TW.u_at Bw MON_O_NK 8) RG U19);
  [ repeat (first [left; reflexivity | right])
  | apply (mh_den E 40 (TW.u_at Bw MON_O_NK 8) E40 ltac:(lia))
  | cbn; lia | cbn; lia ]. }
apply (tw_kept TMAP_A (aview segs (w_H W) mo)); [exact Htw|].
intros x Hx. pose proof (TMAP_A_hull x Hx) as Hh.
unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
destruct (Z_le_gt_dec (MAYBEON_S + 184) x) as [Hx1|Hx1];
  [destruct (Z_lt_ge_dec x (MAYBEON_S + 192)) as [Hx2|Hx2]|].
- remember (Z.to_nat (x - (MAYBEON_S + 184))) as j eqn:Ejd.
  assert (Ej : (j < 8)%nat) by (rewrite Ejd; mh_lia).
  pose proof (HV _ Ej) as Hb.
  replace (MAYBEON_S + 184 + Z.of_nat j) with x in Hb by (rewrite Ejd; mh_lia).
  assert (Hr : aview segs (w_H W) mo x =
    Some (YO0f.le_byte (TW.u_at Bw (TW.OFF_g_s + 184) 8) 8 j)).
  { replace x with (TA_g_s + 184 + Z.of_nat j) by (rewrite Ejd; unfold MAYBEON_S in *; mh_lia).
    exact (tw_read TMAP_A (aview segs (w_H W) mo) Bw TW.OFF_g_s TA_g_s TW.SZ_g_s 184 8
      j TMAP_A_ok Htw TMAP_A_g_s ltac:(lia) ltac:(mh_lia) Ej). }
  rewrite Hr. unfold aview. rewrite Hb. cbn [option_map]. f_equal.
  replace (TW.OFF_g_s + 184) with MON_O_NK by reflexivity.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
  unfold YO0f.le_byte. apply Z.mod_mod. lia.
- apply KA; [mh_lia|]. unfold MH_ZS. intros [Hy | [Hy | [Hy | Hy]]];
  [ apply (HFimg x); [mh_lia | exact (Himg x Hx)] | mh_lia | mh_lia | mh_lia ].
- apply KA; [mh_lia|]. unfold MH_ZS. intros [Hy | [Hy | [Hy | Hy]]];
  [ apply (HFimg x); [mh_lia | exact (Himg x Hx)] | mh_lia | mh_lia | mh_lia ].
Qed.

Lemma mon_head : mon_head_stmt B MT.
Proof.
intros NTC REL.
unfold transport_maybe_online_cg_holds_stmt.
intros HPCS HCELLS HMCELLS HROU HRNE LAWS MTL MTF SMP ASF FFL HGX HGN ASM0 HAI0 HNOT0.
assert (HLAWS : mon_laws B MT).
{ unfold mon_laws.
  split; [exact HPCS|]. split; [exact HCELLS|]. split; [exact HMCELLS|]. split; [exact HROU|].
  split; [exact HRNE|]. split; [exact LAWS|]. split; [exact MTL|]. split; [exact MTF|].
  split; [exact SMP|]. split; [exact ASF|]. split; [exact FFL|]. split; [exact HGX | exact HGN]. }
unfold transport_maybe_online_cg.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs TF Bw Bw'
  HJ Hra Hra4 Hgp Htp H10 Hsp16 Hlo Hhi Htw Hgf Hm HTF HRO Hap Hcnt Hev.
pose proof (ASM0 fx) as ASM.
pose proof HJ as HJ00.
pose proof HJ as (HSTK & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & Hstk & _).
pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
clear HJi memS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HMS : MAYBEON_STK = MAYBEON_FRAME + MAYBEON_ALIGN + Z.max ESTACK NOTICE_STK) by reflexivity.
pose proof (Z.le_max_l ESTACK NOTICE_STK) as HMX.
assert (Hspr : 2 ^ 46 <= spZ regs <= 2 ^ 47) by mh_lia.
assert (Hwin0 : forall a, spZ regs - MAYBEON_STK <= a < spZ regs -> apresent (w_H W) memc a)
  by (intros a Ha; apply Hpres0; mh_lia).
(* the realigned stack pointer *)
destruct (can_sp1_facts (spZ regs + -96) ltac:(mh_lia)
  ltac:(rewrite <- Zplus_mod_idemp_l, Hsp16; reflexivity)) as (Hsp1r & Hsp1al & Hsp1al16).
set (sp1 := 32 * ((spZ regs + -96) / 32)) in *.
assert (Esp1 : sp1 = 32 * ((spZ regs - MAYBEON_FRAME) / 32))
  by (unfold sp1; do 3 f_equal; mh_lia).
assert (Gsp1 : spZ regs - 112 <= sp1 <= spZ regs - 96) by (clear - Hsp1r; lia).
(* run 1: the entry to the stack-malloc call *)
set (E0 := mh_E regs [w64 SHADOW_OFF]).
assert (HEI : img_env VAL A_LIM E0) by apply mh_env_img.
assert (Usp : bv_unsigned (ew E0 2) = spZ regs)
  by (unfold E0; rewrite (mh_ew_reg regs [w64 SHADOW_OFF] 2 2%bv eq_refl); reflexivity).
assert (E32 : ew E0 32 = Z_to_bv 64 SHADOW_OFF)
  by (exact (mh_ew_extra regs [w64 SHADOW_OFF] 0 ltac:(cbn; lia) ltac:(lia))).
pose proof (mh_entry1 lyc Sc W regs memc mdc HCELLS HAR ltac:(intros a Ha; apply Hpres0; mh_lia)
  Hspr Hsp16 H10) as HS. fold E0 in HS.
assert (SHOK : sh_ok segs (SOff 32 0) MH_SH E0 (mrestrict (w_H W) memc))
  by (unfold MH_SH, sh_ok; apply Forall_nil).
pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUNTO.
pose proof (paj_branch (fx := fx) (PI := PI_transport)) as BR.
unfold cfg_at.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + AF_maybe_online)) memc
    (YK11.seg_rom segs)) mdc) Q) end.
paj_run_tok RUN HS HJ SHOK MH_B0.
{ mh_awr1 Usp. }
set (md1 := with_vm_backing (m_vm_lazy mdc) mat mdc) in *. clearbody md1. clear mat.
(* the eleven saved words, read back from the stack region the run wrote *)
pose proof (st_ok_region_nth E0 _ _ 0 _ HS eq_refl) as HRsk. cbn [ms_mem restrict] in HRsk.
assert (HSV : forall o r, In (o, r) MON_SAVED ->
  rdword (aview segs (w_H W) (ms_mem ms)) (spZ regs - o) =
  Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 r)))).
{ intros o r Hin.
  assert (Ho : 8 <= o <= 88 /\ 0 <= r <= 25).
  { unfold MON_SAVED in Hin. cbn [In] in Hin.
    repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <-; lia |]). destruct Hin. }
  assert (Er : Z.of_nat (Z.to_nat r) = bv_unsigned (Z_to_bv 5 r)).
  { rewrite Z2Nat.id by lia. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
    change (2 ^ Z.of_N 5) with 32. rewrite Z.mod_small by lia. reflexivity. }
  apply (AF0x.val_mem_rdword (w_H W) (ms_mem ms) (spZ regs - o)
    (bv_unsigned (YK11.getr regs (Z_to_bv 5 r)))
    ltac:(pose proof (bv_unsigned_in_range 64 (YK11.getr regs (Z_to_bv 5 r))) as Hrg;
          unfold bv_modulus in Hrg; change (2 ^ Z.of_N 64) with (2 ^ 64) in Hrg; lia)).
  replace (spZ regs - o) with (spZ regs + - o) by ring.
  apply (can_field_of_region E0 _ 2 (spZ regs) _ (-96) 0 (-96) 0 (- o) 8%N
    (SOff (Z.to_nat r) 0) (bv_unsigned (YK11.getr regs (Z_to_bv 5 r))) HRsk Usp);
  [ unfold MON_SAVED in Hin; cbn [In] in Hin;
    repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <-; cbn [Z.to_nat Pos.to_nat Pos.iter_op Nat.add];
      repeat (first [left; reflexivity | right]) |]); destruct Hin
  | cbn [sv_denot]; unfold E0;
    rewrite (mh_ew_reg regs [w64 SHADOW_OFF] (Z.to_nat r) (Z_to_bv 5 r) Er), Z.add_0_r, Z_to_bv_bv_unsigned;
    reflexivity
  | cbn; pose proof (bv_unsigned_in_range 64 (YK11.getr regs (Z_to_bv 5 r))) as Hrg;
    unfold bv_modulus in Hrg; change (2 ^ Z.of_N 64) with (2 ^ 64) in Hrg; lia
  | cbn; lia ]. }
(* the registers at the call *)
pmkst HS.
mh_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 40820)) R1 ltac:(apply codeptr_val; exact HEI).
mh_reg HS (2%bv : bv 5) (Z_to_bv 64 sp1) R2
  ltac:(exact (can_denot_and_m32 E0 2 (spZ regs) (-96)
    ltac:(unfold E0; rewrite (mh_ew_reg regs [w64 SHADOW_OFF] 2 2%bv eq_refl); unfold spZ;
          symmetry; apply Z_to_bv_bv_unsigned) ltac:(mh_lia) ltac:(mh_lia) ltac:(mh_lia))).
mh_reg HS (3%bv : bv 5) (w64 (as_gp B)) R3
  ltac:(cbn [sv_denot]; unfold E0; rewrite (mh_ew_reg regs [w64 SHADOW_OFF] 3 3%bv eq_refl), Z.add_0_r,
        Z_to_bv_bv_unsigned; exact Hgp).
mh_reg HS (4%bv : bv 5) (w64 (as_tp B)) R4
  ltac:(cbn [sv_denot]; unfold E0; rewrite (mh_ew_reg regs [w64 SHADOW_OFF] 4 4%bv eq_refl), Z.add_0_r,
        Z_to_bv_bv_unsigned; exact Htp).
mh_reg HS (8%bv : bv 5) (w64 (spZ regs)) R8 ltac:(cbn [sv_denot]; rewrite Usp, Z.add_0_r; reflexivity).
mh_reg HS (9%bv : bv 5) (Z_to_bv 64 sp1) R9
  ltac:(exact (can_denot_and_m32_add0 E0 2 (spZ regs) (-96)
    ltac:(unfold E0; rewrite (mh_ew_reg regs [w64 SHADOW_OFF] 2 2%bv eq_refl); unfold spZ;
          symmetry; apply Z_to_bv_bv_unsigned) ltac:(mh_lia) ltac:(mh_lia) ltac:(mh_lia))).
mh_reg HS (19%bv : bv 5) (w64 MAYBEON_S) R19
  ltac:(cbn [sv_denot]; unfold E0; rewrite (mh_ew_reg regs [w64 SHADOW_OFF] 10 10%bv eq_refl), Z.add_0_r,
        Z_to_bv_bv_unsigned; exact H10).
mh_reg HS (24%bv : bv 5) (w64 SHADOW_OFF) R24
  ltac:(cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
mh_reg HS (26%bv : bv 5) (YK11.getr regs 26) R26
  ltac:(cbn [sv_denot]; unfold E0; rewrite (mh_ew_reg regs [w64 SHADOW_OFF] 26 26%bv eq_refl), Z.add_0_r,
        Z_to_bv_bv_unsigned; reflexivity).
mh_reg HS (27%bv : bv 5) (YK11.getr regs 27) R27
  ltac:(cbn [sv_denot]; unfold E0; rewrite (mh_ew_reg regs [w64 SHADOW_OFF] 27 27%bv eq_refl), Z.add_0_r,
        Z_to_bv_bv_unsigned; reflexivity).
(* +0x064: the class-2 stack malloc, at the pc the record names *)
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transport_sigma TS___asan_stack_malloc_2)) mm rom) mdx) Q)
  end.
rewrite <- HPCS.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (@YK11.mkst _ ?rg _ ?mm _) ?mdx) _ =>
  exact (@gx_stack_malloc_at fx rc tfib_sink_head segs B LAWS transport_segs_low SMP MAYBEON_CID ASM
    ltac:(mh_lia) TG.G_HARNESS W rg mm STK sp0 FP ly S W0 mem0 md0 own lyc Sc mdx k (sp1 - sp0)
    (Z_to_bv 64 (BASE + 40820)) HJ
    ltac:(unfold spZ at 1; rewrite R2, unsigned_lit_small by mh_lia; lia)
    ltac:(rewrite Zminus_mod, Hsp1al16, Hsp0a; reflexivity)
    ltac:(mh_lia) ltac:(mh_lia) R3 R4 R1
    ltac:(apply (ret_ok_codeptr_v (PI := PI_transport)); [mh_lia | reflexivity]) Hcnt) end. }
cbv beta.
intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & pos & -> & HJ2 & HP2 & Ha0 & Eab2 & Hfrs2 & Hnev2
  & Hset2 & Hz & Hflag & Hfpres & HK1).
set (F := frame_addr lyc MAYBEON_CID pos) in *.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HAR2.
assert (Hin2 : In (MAYBEON_CID, pos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ MAYBEON_CID pos HAR2 Hin2) as (HFal & HFapp & HFb & HFsh).
destruct (frames_bounds segs B LAWS _ _ _ _ _ MAYBEON_CID pos HAR2 Hin2) as (HF0 & HFc & _).
destruct (dkg_frame_al64 segs B _ _ _ _ _ MAYBEON_CID pos HAR2 Hin2) as (HF64 & HFs64 & HFs).
change (fs_frame_bytes MAYBEON_CID / 8) with 32 in HFsh.
change (fs_frame_bytes MAYBEON_CID) with 256 in HFb, HFc, HFapp, Hz, Hflag, Hfpres, HFsh.
fold F in HFal, HFapp, HFb, HFsh, HF0, HFc, HF64, HFs, Hz, Hflag, Hfpres.
assert (HFq8 : 0 <= F / 8 <= 2 ^ 44)
  by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; [lia | mh_lia]]).
assert (Hce1 : alloc_ceiling <= sp1 - ESTACK) by mh_lia.
assert (HappD : F + 256 <= kLowShadowBeg \/ kHighMemBeg <= F)
  by (destruct HFapp as (_ & [Hx | [Hx _]]); [left; mh_lia | right; mh_lia]).
destruct HK1 as (K1a & K1b & K1c & K1d & K1e & K1f).
assert (Hpsl : forall a, sp1 <= a < sp1 + 8 -> apresent (w_H W) mem2 a).
{ intros a Ha. apply K1e.
  - mh_lia.
  - intros [Hx Hy]. mh_lia.
  - apply (apresent_grows (w_H W) memc (ms_mem ms) a HG). apply Hpres0. mh_lia. }
assert (HimgP : forall y, tw_in TMAP_A y -> in_img segs y).
{ intros y (o & b & n & Hinr & Hy). refine (proj1 (HGX y _)).
  unfold inG. apply Exists_exists. exists (b, n).
  split; [exact (TMAP_A_in_G o b n Hinr) | unfold in_zr; cbn [fst snd]; lia]. }
assert (HFimg : forall a, F <= a < F + 256 -> ~ in_img segs a).
{ intros a Ha. apply (frm_img segs B LAWS _ _ _ _ _ MAYBEON_CID pos a HAR2 Hin2).
  change (fs_frame_bytes MAYBEON_CID) with 256. fold F. exact Ha. }
(* g_s's payload and the frame are apart: a frame byte is not an image byte *)
assert (HFg : F + 256 <= MAYBEON_S \/ MAYBEON_S + TW.SZ_g_s <= F).
{ destruct (Z_le_gt_dec (F + 256) MAYBEON_S) as [Hx|Hx]; [left; exact Hx|].
  destruct (Z_le_gt_dec (MAYBEON_S + TW.SZ_g_s) F) as [Hy|Hy]; [right; exact Hy|].
  exfalso. apply (HFimg (Z.max F MAYBEON_S)); [mh_lia|].
  exact (proj1 (HGX (Z.max F MAYBEON_S) (mh_inG (Z.max F MAYBEON_S) ltac:(mh_lia)))). }
(* the saved words and the frame's flag word, kept by the call *)
assert (HSV2 : forall o r, In (o, r) MON_SAVED ->
  rdword (aview segs (w_H W) mem2) (spZ regs - o) = Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 r)))).
{ intros o r Hin.
  assert (Ho : 8 <= o <= 88 /\ 0 <= r <= 25).
  { unfold MON_SAVED in Hin. cbn [In] in Hin.
    repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <-; lia |]). destruct Hin. }
  apply (AF0x.rdword_ext (aview segs (w_H W) (ms_mem ms))); [|exact (HSV o r Hin)].
  intros i Hi. apply K1a; mh_lia. }
assert (Q2 : YK11.getr regs2 2 = Z_to_bv 64 sp1)
  by (transitivity (YK11.getr (ms_regs ms) 2); [exact (HP2 2 ltac:(unfold acallee_saved; lia)) | exact R2]).
assert (Q3 : YK11.getr regs2 3 = w64 (as_gp B))
  by (transitivity (YK11.getr (ms_regs ms) 3); [exact (HP2 3 ltac:(unfold acallee_saved; lia)) | exact R3]).
assert (Q4 : YK11.getr regs2 4 = w64 (as_tp B))
  by (transitivity (YK11.getr (ms_regs ms) 4); [exact (HP2 4 ltac:(unfold acallee_saved; lia)) | exact R4]).
assert (Q8 : YK11.getr regs2 8 = w64 (spZ regs))
  by (transitivity (YK11.getr (ms_regs ms) 8); [exact (HP2 8 ltac:(unfold acallee_saved; lia)) | exact R8]).
assert (Q9 : YK11.getr regs2 9 = Z_to_bv 64 sp1)
  by (transitivity (YK11.getr (ms_regs ms) 9); [exact (HP2 9 ltac:(unfold acallee_saved; lia)) | exact R9]).
assert (Q19 : YK11.getr regs2 19 = w64 MAYBEON_S)
  by (transitivity (YK11.getr (ms_regs ms) 19); [exact (HP2 19 ltac:(unfold acallee_saved; lia)) | exact R19]).
assert (Q24 : YK11.getr regs2 24 = w64 SHADOW_OFF)
  by (transitivity (YK11.getr (ms_regs ms) 24); [exact (HP2 24 ltac:(unfold acallee_saved; lia)) | exact R24]).
assert (Q26 : YK11.getr regs2 26 = YK11.getr regs 26)
  by (transitivity (YK11.getr (ms_regs ms) 26); [exact (HP2 26 ltac:(unfold acallee_saved; lia)) | exact R26]).
assert (Q27 : YK11.getr regs2 27 = YK11.getr regs 27)
  by (transitivity (YK11.getr (ms_regs ms) 27); [exact (HP2 27 ltac:(unfold acallee_saved; lia)) | exact R27]).
(* run 1 wrote only the 96 bytes below the entry sp *)
assert (HG1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 96 <= a < spZ regs) ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) memc a).
{ intros a Ha Hn.
  apply (kept_of_frame E0 mh_regions1 (w_H W) memc (ms_mem ms)
    (fun x => spZ regs - 96 <= x < spZ regs) HFr); [| exact Ha | exact Hn].
  intros b wlo whi x Hin Hx. cbv beta.
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx;
    rewrite ?Usp in Hx; mh_lia |]). destruct Hin. }
(* the world and the record's shadow, carried through run 1 and the call *)
assert (HGK : gx_kept segs TG.G_HARNESS W memc W mem2).
{ apply (gx_kept_trans segs TG.G_HARNESS W memc W (ms_mem ms) W mem2).
  - intros a HaG. pose proof (inG_low segs B transport_segs_low TG.G_HARNESS a HGX HaG) as Hlow.
    apply HG1; mh_lia.
  - apply (gx_kept_of_acall_kept segs B TG.G_HARNESS lyc Sc W (ms_mem ms) W mem2
      (sp0 + (sp1 - sp0) - ESTACK) (sp0 + (sp1 - sp0)) (fun _ => False) HGX HGN).
    exact (conj K1a (conj K1b (conj K1c (conj K1d (conj K1e K1f))))). }
assert (Htw2 : tw_at TMAP_A (aview segs (w_H W) mem2) Bw)
  by (apply (tw_kept_GA (aview segs (w_H W) memc)); [exact Htw|];
      intros b n i Hbn Hi; apply HGK; unfold inG; apply Exists_exists; exists (b, n);
      split; [exact Hbn | unfold in_zr; cbn [fst snd]; lia]).
clear HS HEI SHOK.
assert (HEI : img_env VAL A_LIM (mh_E regs2 (mh_vals F Bw))) by apply mh_env_img.
assert (SHOK : sh_ok segs (SOff 24 0) MH_SH (mh_E regs2 (mh_vals F Bw)) (mrestrict (w_H W) mem2))
  by (unfold MH_SH, sh_ok; apply Forall_nil).
pose proof (mh_entry2 lyc S2 W regs2 mem2 md2 Bw F sp1 HMCELLS HAR2 Htw2 Q2 Q9 Ha0 Q19 Q24
  ltac:(mh_lia) Hsp1al ltac:(mh_lia) HF64 ltac:(mh_lia)
  ltac:(destruct HFapp as (_ & [Hx | [Hx _]]); [left; mh_lia | right; mh_lia]) HFg ltac:(mh_lia)
  ltac:(intros a Ha; apply Hpsl; mh_lia)
  ltac:(intros a Ha; exact (proj1 (HFb a ltac:(lia))))
  ltac:(intros j Hj; replace (SHADOW_OFF + F / 8 + j) with (shadow_addr F + j) by reflexivity;
        exact (proj1 (HFsh j ltac:(lia))))) as HS.
set (E1 := mh_E regs2 (mh_vals F Bw)) in HS, HEI, SHOK.
assert (U10' : bv_unsigned (ew E1 10) = F)
  by (unfold E1; rewrite (mh_ew_reg regs2 (mh_vals F Bw) 10 10%bv eq_refl), Ha0; apply unsigned_lit_small; mh_lia).
assert (U9' : bv_unsigned (ew E1 9) = sp1)
  by (unfold E1; rewrite (mh_ew_reg regs2 (mh_vals F Bw) 9 9%bv eq_refl), Q9; apply unsigned_lit_small; mh_lia).
assert (U19' : bv_unsigned (ew E1 19) = MAYBEON_S)
  by (unfold E1; rewrite (mh_ew_reg regs2 (mh_vals F Bw) 19 19%bv eq_refl), Q19; apply unsigned_lit_small; mh_lia).
assert (U33' : bv_unsigned (ew E1 33) = SHADOW_OFF + F / 8).
{ pose proof (mh_ew_extra regs2 (mh_vals F Bw) 1 ltac:(cbn; lia) ltac:(lia)) as X.
  cbn [Nat.add nth mh_vals] in X. unfold E1. rewrite X. apply unsigned_lit_small.
  assert (HFq : 0 <= F / 8 <= F) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  mh_lia. }
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + MON_C1)) mem2
    (YK11.seg_rom segs)) md2) Q) end.
(* What the entry and the call keep of the caller's memory. *)
assert (KPT0 : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W mem2 (spZ regs - MAYBEON_STK) (spZ regs)
  (maybeon_wr Bw)).
{ apply (dk_kept_trans_g segs B TG.G_HARNESS lyc Sc W memc W (ms_mem ms) W mem2
    (spZ regs - MAYBEON_STK) (spZ regs) (sp0 + (sp1 - sp0) - ESTACK) (sp0 + (sp1 - sp0))
    (maybeon_wr Bw) (fun _ => False)); [mh_lia | mh_lia | | | mh_lia | mh_lia | intros a [] ].
  - apply (dk_kept_step_g segs B LAWS transport_segs_low TG.G_HARNESS lyc Sc W memc mdc memc (ms_mem ms)
      (spZ regs - MAYBEON_STK) (spZ regs) (maybeon_wr Bw) (fun a => spZ regs - 96 <= a < spZ regs) HAR).
    + apply dk_kept_refl_g. exact Hwin0.
    + intros a Ha Hn. apply HG1; [exact Ha | exact Hn].
    + intros a Hp. exact (apresent_grows (w_H W) memc (ms_mem ms) a HG Hp).
    + intros a Hz1 Hc1. mh_lia.
    + intros b m i Hb Hi Hz2. exfalso.
      destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hb) as (_ & Hb4096 & Hbce & _). mh_lia.
    + intros a Hz3 Hi3 _ _. exfalso. pose proof (transport_segs_low a Hi3). mh_lia.
    + intros c0 p0 a Hin Hr Hz4. exfalso.
      destruct (frames_bounds segs B LAWS lyc Sc W memc mdc c0 p0 HAR Hin) as (G4096 & Gce & _).
      pose proof (fs_frame_bytes_nonneg c0) as Hfs.
      destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [mh_lia|].
      pose proof (shadow_range_end (frame_addr lyc c0 p0) (fs_frame_bytes c0) Hfs) as Hse.
      assert (Hd : (frame_addr lyc c0 p0 + fs_frame_bytes c0) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
      pose proof (Z.div_pos (frame_addr lyc c0 p0) 8 ltac:(lia) ltac:(lia)).
      unfold shadow_addr in Hr, Hse. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. mh_lia.
  - apply acall_kept_g_of. exact (conj K1a (conj K1b (conj K1c (conj K1d (conj K1e K1f))))). }
(* the frame's last word, which holds the address of its flag byte *)
assert (HFL2 : rdword (aview segs (w_H W) mem2) (F + MON_FBYTES - 8) = Some (flag_addr lyc MAYBEON_CID pos))
  by (replace (F + MON_FBYTES - 8) with (F + 256 - 8) by mh_lia; exact Hflag).
assert (HMO : mo_le MT Sc S2 0).
{ destruct Hset2 as (f2 & Ef2). rewrite Ef2. apply (mo_le_set_fs_r MT MTF). exact (mo_le_refl MT MTL Sc). }
assert (HEV0 : 0 <= MAYBEON_EV) by (unfold MAYBEON_EV, NOTICE_EV; lia).
clear HG1 HSV HF HFr HG K1a K1b K1c K1d K1e K1f Hflag Hz Hfpres HP2 Hnev2 Hset2.
clear R1 R2 R3 R4 R8 R9 R19 R24 R26 R27 HRsk.
clear dependent ms.
(* run 2: +0x68 .. the first test of :178 *)
paj_run_tok RUN HS HJ2 SHOK MH_B0.
{ mh_awr2 U10' U33' U9' U19' pos F. }
(* the caller's facts both cuts take *)
assert (U34' : bv_unsigned (ew E1 34) = MON_GSH).
{ pose proof (mh_ew_extra regs2 (mh_vals F Bw) 2 ltac:(cbn; lia) ltac:(lia)) as X.
  cbn [Nat.add nth mh_vals] in X. unfold E1. rewrite X. apply unsigned_lit_small. mh_lia. }
assert (HFIX : mon_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs TF Bw Bw' pos sp1 F).
{ unfold mon_fix.
  split; [exact HJ00|]. split; [exact Hra|]. split; [exact Hra4|]. split; [exact Hgp|]. split; [exact Htp|].
  split; [exact H10|]. split; [exact Hsp16|]. split; [exact Hlo|]. split; [exact Hhi|].
  split; [exact Htw|]. split; [exact Hgf|]. split; [exact Hm|]. split; [exact HTF|]. split; [exact HRO|].
  split; [exact Hap|]. split; [exact Hcnt|]. split; [exact Hev|].
  split; [exact Esp1|]. split; [reflexivity|]. split; [exact HF0|]. split; [exact HF64|].
  split; [exact HFc | exact HFapp]. }
(* what both cuts carry, at any later memory of run 2 *)
assert (HCUR : forall (mF : word -> option byte) (mdF : Model),
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0
    ((MAYBEON_CID, pos) :: own) lyc S2 W mF mdF k ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ MH_ZS F sp1 a -> aview segs (w_H W) mF a = aview segs (w_H W) mem2 a) ->
  (forall a, apresent (w_H W) mem2 a -> apresent (w_H W) mF a) ->
  mon_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw pos F lyc S2 W mF mdF 0).
{ intros mF mdF HJF KA GA. unfold mon_cur.
  split; [rewrite Z.add_0_r; exact HJF|].
  split; [split; [lia | exact HEV0]|].
  split; [exact Hfrs2|].
  split; [rewrite Eab2; apply Permutation_refl|].
  split; [reflexivity|].
  split; [exact HMO|].
  split.
  { apply (dk_kept_nfz_gw segs B LAWS transport_segs_low TG.G_HARNESS lyc Sc lyc S2 W memc mdc W mem2 md2
      mem2 mF (spZ regs - MAYBEON_STK) (spZ regs) MAYBEON_CID pos F (flag_addr lyc MAYBEON_CID pos)
      (maybeon_wr Bw) (MH_ZS F sp1) HGX HAR HAR2 Hfrs2 ltac:(intros bm Hbm; rewrite Eab2; exact Hbm)
      eq_refl eq_refl eq_refl FFL ltac:(mh_lia) ltac:(mh_lia)); [| exact KPT0 | exact KA | exact GA].
    intros a Hz. unfold MH_ZS in Hz. unfold dkg_nf.
    destruct Hz as [Hz | [Hz | [Hz | Hz]]].
    - right; left; left. change (fs_frame_bytes MAYBEON_CID) with 256. mh_lia.
    - right; left; right; left. change (fs_frame_bytes MAYBEON_CID / 8) with 32. mh_lia.
    - left. mh_lia.
    - right; right. apply mh_inG. mh_lia. }
  split.
  { unfold MON_SAVED. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
    match goal with |- rdword _ (spZ regs - ?o) = Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 ?r))) =>
      apply (AF0x.rdword_ext (aview segs (w_H W) mem2));
      [ intros i Hi; apply KA; [mh_lia | unfold MH_ZS; intros [Hx | [Hx | [Hx | Hx]]]; mh_lia]
      | apply (HSV2 o r); unfold MON_SAVED; cbn [In];
        repeat (first [left; reflexivity | right]) ] end. }
  apply (AF0x.rdword_ext (aview segs (w_H W) mem2)); [|exact HFL2].
  intros i Hi. apply KA; [mh_lia | unfold MH_ZS; intros [Hx | [Hx | [Hx | Hx]]]; mh_lia]. }
(* the three tests of :178 *)
mh_kept_tac KA1 F sp1 U10' U33' U9' U19' U34'.
assert (GA1 : forall a, apresent (w_H W) mem2 a -> apresent (w_H W) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows (w_H W) mem2 (ms_mem ms) a HG Ha)).
clear HF HFr HG.
assert (E36' : ew E1 36 = Z_to_bv 64 (TW.u_at Bw MON_O_ST 4)).
{ pose proof (mh_ew_extra regs2 (mh_vals F Bw) 4 ltac:(cbn; lia) ltac:(lia)) as X.
  cbn [Nat.add nth mh_vals] in X. unfold E1. exact X. }
assert (E37' : ew E1 37 = Z_to_bv 64 (TW.u_at Bw MON_O_E1 4)).
{ pose proof (mh_ew_extra regs2 (mh_vals F Bw) 5 ltac:(cbn; lia) ltac:(lia)) as X.
  cbn [Nat.add nth mh_vals] in X. unfold E1. exact X. }
assert (E38' : ew E1 38 = Z_to_bv 64 (TW.u_at Bw MON_O_WA 4)).
{ pose proof (mh_ew_extra regs2 (mh_vals F Bw) 6 ltac:(cbn; lia) ltac:(lia)) as X.
  cbn [Nat.add nth mh_vals] in X. unfold E1. exact X. }
assert (E35' : ew E1 35 = Z_to_bv 64 (TW.u_at Bw MON_O_KA 4)).
{ pose proof (mh_ew_extra regs2 (mh_vals F Bw) 3 ltac:(cbn; lia) ltac:(lia)) as X.
  cbn [Nat.add nth mh_vals] in X. unfold E1. exact X. }
assert (E39' : ew E1 39 = Z_to_bv 64 (TW.u_at Bw MON_O_RX 8)).
{ pose proof (mh_ew_extra regs2 (mh_vals F Bw) 7 ltac:(cbn; lia) ltac:(lia)) as X.
  cbn [Nat.add nth mh_vals] in X. unfold E1. exact X. }
assert (E40' : ew E1 40 = Z_to_bv 64 (TW.u_at Bw MON_O_NK 8)).
{ pose proof (mh_ew_extra regs2 (mh_vals F Bw) 8 ltac:(cbn; lia) ltac:(lia)) as X.
  cbn [Nat.add nth mh_vals] in X. unfold E1. exact X. }
assert (EE2 : ew E1 2 = Z_to_bv 64 sp1)
  by (unfold E1; rewrite (mh_ew_reg regs2 (mh_vals F Bw) 2 2%bv eq_refl); exact Q2).
assert (EE3 : ew E1 3 = w64 (as_gp B))
  by (unfold E1; rewrite (mh_ew_reg regs2 (mh_vals F Bw) 3 3%bv eq_refl); exact Q3).
assert (EE4 : ew E1 4 = w64 (as_tp B))
  by (unfold E1; rewrite (mh_ew_reg regs2 (mh_vals F Bw) 4 4%bv eq_refl); exact Q4).
assert (EE8 : ew E1 8 = w64 (spZ regs))
  by (unfold E1; rewrite (mh_ew_reg regs2 (mh_vals F Bw) 8 8%bv eq_refl); exact Q8).
assert (EE9 : ew E1 9 = Z_to_bv 64 sp1)
  by (unfold E1; rewrite (mh_ew_reg regs2 (mh_vals F Bw) 9 9%bv eq_refl); exact Q9).
assert (EE10 : ew E1 10 = w64 F)
  by (unfold E1; rewrite (mh_ew_reg regs2 (mh_vals F Bw) 10 10%bv eq_refl); exact Ha0).
assert (EE19 : ew E1 19 = w64 MAYBEON_S)
  by (unfold E1; rewrite (mh_ew_reg regs2 (mh_vals F Bw) 19 19%bv eq_refl); exact Q19).
assert (EE24 : ew E1 24 = w64 SHADOW_OFF)
  by (unfold E1; rewrite (mh_ew_reg regs2 (mh_vals F Bw) 24 24%bv eq_refl); exact Q24).
assert (EE26 : ew E1 26 = YK11.getr regs 26)
  by (unfold E1; rewrite (mh_ew_reg regs2 (mh_vals F Bw) 26 26%bv eq_refl); exact Q26).
assert (EE27 : ew E1 27 = YK11.getr regs 27)
  by (unfold E1; rewrite (mh_ew_reg regs2 (mh_vals F Bw) 27 27%bv eq_refl); exact Q27).
assert (EE33 : ew E1 33 = Z_to_bv 64 (SHADOW_OFF + F / 8)).
{ pose proof (mh_ew_extra regs2 (mh_vals F Bw) 1 ltac:(cbn; lia) ltac:(lia)) as X.
  cbn [Nat.add nth mh_vals] in X. unfold E1. exact X. }
(* a release exit: the model gives Bw' = Bw, and g_s is the world the call started from *)
assert (RELCLOSE : forall (mF : word -> option byte) (mdF : Model) (regsF : bvmap 5 word),
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0
    ((MAYBEON_CID, pos) :: own) lyc S2 W mF mdF k ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ MH_ZS F sp1 a -> aview segs (w_H W) mF a = aview segs (w_H W) mem2 a) ->
  (forall a, apresent (w_H W) mem2 a -> apresent (w_H W) mF a) ->
  region_ok segs E1 (mrestrict (w_H W) mF) mh_rg_gs ->
  maybeon_go Bw = false ->
  mon_regs_rel regs regsF sp1 F ->
  SRr segs W (mkCfg (@YK11.mkst fx regsF (Z_to_bv 64 (BASE + MON_REL)) mF (YK11.seg_rom segs)) mdF)
    (@transport_maybeon_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw')).
{ intros mF mdF regsF HJF KA GA RG HGO HREG.
  assert (EBw : Bw' = Bw)
    by (apply mon_some_inv; exact (eq_trans (eq_sym Hm) (mh_go_false Bw HGO timg_A TF))).
  apply (REL HLAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs TF Bw Bw' pos sp1 F
    lyc S2 W mF mdF 0 regsF HFIX); [| exact HREG].
  unfold mon_rel_cur. split; [exact (HCUR mF mdF HJF KA GA)|].
  rewrite EBw. split; [| exact Hgf].
  exact (mh_tw_rel W E1 mem2 mF Bw F sp1 HGX U19' E40' HF0 HFc HFimg ltac:(mh_lia) Htw2 RG KA). }
psrr_branch_tok RUN BR HS SHOK MH_B0.
- (* S_state <> S_WAKING: the release cut *)
  rewrite (mh_br_ne E1 Bw 36 MON_O_ST 1 E36' ltac:(lia)) in Hc.
  apply negb_true_iff, Z.eqb_neq in Hc.
  assert (HGOF : maybeon_go Bw = false)
    by (rewrite mh_go, (proj2 (Z.eqb_neq _ _) Hc); reflexivity).
  paj_run_to_tok RUNTO HS HJ2 SHOK MH_B0 MON_REL.
  { mh_awr2 U10' U33' U9' U19' pos F. }
  mh_chain KA1 GA1 U10' U33' U9' U19' U34' F sp1 mem2.
  pose proof (st_ok_pi_region_nth E1 _ _ 4 _ HS eq_refl) as RGs. cbn [ms_mem restrict] in RGs.
  mh_regs_r HS HREG F sp1 regs Hgp Htp EE2 EE3 EE4 EE8 EE9 EE10 EE26 EE27 EE33.
  pmkst HS.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + MON_REL)) mm rom) mdx) Q) end.
  lazymatch goal with |- SRr _ _ (mkCfg (@YK11.mkst _ ?rg _ ?mm _) ?mdx) _ =>
    exact (RELCLOSE mm mdx rg HJ2 KA1 GA1 RGs HGOF HREG) end.

- rewrite (mh_br_ne E1 Bw 36 MON_O_ST 1 E36' ltac:(lia)) in Hc.
  apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into Hst.
  paj_run_tok RUN HS HJ2 SHOK MH_B0.
  { mh_awr2 U10' U33' U9' U19' pos F. }
  mh_chain KA1 GA1 U10' U33' U9' U19' U34' F sp1 mem2.
  psrr_branch_tok RUN BR HS SHOK MH_B0.
  + (* S_wake_acked = 0 *)
  rewrite (mh_br_eq E1 Bw 38 MON_O_WA 0 E38' ltac:(lia)) in Hc. apply Z.eqb_eq in Hc.
    assert (HGOF : maybeon_go Bw = false).
    { rewrite mh_go, (proj2 (Z.eqb_eq _ _) Hc). cbn [negb]. rewrite andb_false_r. reflexivity. }
  paj_run_to_tok RUNTO HS HJ2 SHOK MH_B0 MON_REL.
  { mh_awr2 U10' U33' U9' U19' pos F. }
  mh_chain KA1 GA1 U10' U33' U9' U19' U34' F sp1 mem2.
  pose proof (st_ok_pi_region_nth E1 _ _ 4 _ HS eq_refl) as RGs. cbn [ms_mem restrict] in RGs.
  mh_regs_r HS HREG F sp1 regs Hgp Htp EE2 EE3 EE4 EE8 EE9 EE10 EE26 EE27 EE33.
  pmkst HS.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + MON_REL)) mm rom) mdx) Q) end.
  lazymatch goal with |- SRr _ _ (mkCfg (@YK11.mkst _ ?rg _ ?mm _) ?mdx) _ =>
    exact (RELCLOSE mm mdx rg HJ2 KA1 GA1 RGs HGOF HREG) end.

  + rewrite (mh_br_eq E1 Bw 38 MON_O_WA 0 E38' ltac:(lia)) in Hc. apply Z.eqb_neq in Hc. rename Hc into Hwa.
    paj_run_tok RUN HS HJ2 SHOK MH_B0.
    { mh_awr2 U10' U33' U9' U19' pos F. }
    mh_chain KA1 GA1 U10' U33' U9' U19' U34' F sp1 mem2.
    psrr_branch_tok RUN BR HS SHOK MH_B0.
    * (* S_e1_named_us = 0 *)
      rewrite (mh_br_eq E1 Bw 37 MON_O_E1 0 E37' ltac:(lia)) in Hc. apply Z.eqb_eq in Hc.
      assert (HGOF : maybeon_go Bw = false).
      { rewrite mh_go, (proj2 (Z.eqb_eq _ _) Hc). cbn [negb]. rewrite andb_false_r. reflexivity. }
  paj_run_to_tok RUNTO HS HJ2 SHOK MH_B0 MON_REL.
  { mh_awr2 U10' U33' U9' U19' pos F. }
  mh_chain KA1 GA1 U10' U33' U9' U19' U34' F sp1 mem2.
  pose proof (st_ok_pi_region_nth E1 _ _ 4 _ HS eq_refl) as RGs. cbn [ms_mem restrict] in RGs.
  mh_regs_r HS HREG F sp1 regs Hgp Htp EE2 EE3 EE4 EE8 EE9 EE10 EE26 EE27 EE33.
  pmkst HS.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + MON_REL)) mm rom) mdx) Q) end.
  lazymatch goal with |- SRr _ _ (mkCfg (@YK11.mkst _ ?rg _ ?mm _) ?mdx) _ =>
    exact (RELCLOSE mm mdx rg HJ2 KA1 GA1 RGs HGOF HREG) end.

    * rewrite (mh_br_eq E1 Bw 37 MON_O_E1 0 E37' ltac:(lia)) in Hc. apply Z.eqb_neq in Hc. rename Hc into He1.
      (* the test of :178 holds *)
      assert (HGO : maybeon_go Bw = true).
      { rewrite mh_go, (proj2 (Z.eqb_eq _ _) Hst), (proj2 (Z.eqb_neq _ _) Hwa),
          (proj2 (Z.eqb_neq _ _) He1). reflexivity. }
      paj_run_to_tok RUNTO HS HJ2 SHOK MH_B0 MON_NTC.
      { mh_awr2 U10' U33' U9' U19' pos F. }
      mh_chain KA1 GA1 U10' U33' U9' U19' U34' F sp1 mem2.
      (* the world after the store at s + 184 *)
      pose proof (st_ok_pi_region_nth E1 _ _ 4 _ HS eq_refl) as RGs. cbn [ms_mem restrict] in RGs.
      assert (HNK : forall j, (j < 8)%nat ->
        aview segs (w_H W) (ms_mem ms) (MAYBEON_S + 184 + Z.of_nat j) = Some (YO0f.le_byte (MON_NKV Bw) 8 j)).
      { intros j Hj.
        assert (HV : val_mem segs (mrestrict (w_H W) (ms_mem ms)) (MAYBEON_S + 184) 8 (MON_NKV Bw)).
        { apply (can_field_of_region E1 _ 19 MAYBEON_S _ 24 192 184 192 184 8%N
            (SAlu ALU_ADD (SMd M_MUL (SOff 35 0) (SLit 1000)) (SOff 39 0)) (MON_NKV Bw) RGs U19');
          [ repeat (first [left; reflexivity | right])
          | rewrite <- (mh_store_val E1 Bw E35' E39'); symmetry; apply Z_to_bv_bv_unsigned
          | cbn; unfold MON_NKV; pose proof (Z.mod_pos_bound
              (TW.u_at Bw MON_O_KA 4 * 1000 + TW.u_at Bw MON_O_RX 8) (2 ^ 64) ltac:(lia)); lia
          | cbn; lia ]. }
        pose proof (HV j Hj) as Hb. unfold aview. rewrite Hb. cbn [option_map]. f_equal.
        rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
        unfold YO0f.le_byte. apply Z.mod_mod. lia. }
      assert (HTW1 : tw_at TMAP_A (aview segs (w_H W) (ms_mem ms)) (maybeon_w1 Bw)).
      { rewrite mh_w1.
        replace MON_O_NK with (TW.OFF_g_s + 184) by reflexivity.
        apply (tw_write TMAP_A (aview segs (w_H W) mem2) (aview segs (w_H W) (ms_mem ms)) Bw
          TW.OFF_g_s TA_g_s TW.SZ_g_s 184 8 (TS0.u64 (TW.u_at Bw MON_O_RX 8 + TS0.ms_m (TW.u_at Bw MON_O_KA 4))))
          ; [exact TMAP_A_ok | exact Htw2 | exact TMAP_A_g_s | lia | mh_lia | | ].
        - intros j Hj. rewrite (mh_nkv Bw). exact (HNK j Hj).
        - intros x Hx Hnx. pose proof (TMAP_A_hull x Hx) as Hh.
          apply KA1; [mh_lia|].
          unfold MH_ZS. intros [Hy | [Hy | [Hy | Hy]]];
            [ apply (HFimg x); [mh_lia | exact (HimgP x Hx)] | mh_lia | mh_lia | mh_lia ]. }
      (* the state of maybeon_w1 Bw is S_WAKING *)
      assert (HSTW : TW.S_state (maybeon_w1 Bw) = TS0.DIGINET_S_WAKING).
      { rewrite (mh_w1_state Bw (tw_len _ _ _ Htw)). exact Hst. }
      (* G outside the written range, kept *)
      assert (HGEX : gx_kept_ex segs TG.G_HARNESS (maybeon_wr Bw) W memc W (ms_mem ms)).
      { apply (gx_kept_ex_step segs B transport_segs_low TG.G_HARNESS (maybeon_wr Bw) W memc mem2 (ms_mem ms)
            (MH_ZS F sp1) HGX).
        - intros a Hz HaG. unfold MH_ZS in Hz. destruct Hz as [Hz | [Hz | [Hz | Hz]]].
          + exfalso. apply (HFimg a); [mh_lia | exact (proj1 (HGX a HaG))].
          + exfalso. pose proof (inG_low segs B transport_segs_low TG.G_HARNESS a HGX HaG). mh_lia.
          + exfalso. pose proof (inG_low segs B transport_segs_low TG.G_HARNESS a HGX HaG). mh_lia.
          + unfold maybeon_wr. split; [exact HGO|]. left. unfold twa_fld.
            unfold TW.A_S_next_keepalive_us, TW.OFF_g_s. mh_lia.
        - intros a Ha Hn. apply KA1; [exact Ha | exact Hn].
        - apply gx_kept_ex_of_kept. exact HGK. }
      (* the registers at the notice cut *)
      mh_regs_n HS HREGN F sp1 regs Hgp Htp EE2 EE3 EE4 EE8 EE9 EE10 EE19 EE24 EE26 EE27 EE33.
      pmkst HS.
      lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
        change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + MON_NTC)) mm rom) mdx) Q) end.
      lazymatch goal with |- SRr _ _ (mkCfg (@YK11.mkst _ ?rg _ ?mm _) ?mdx) _ =>
      apply (NTC HLAWS HAI0 HNOT0 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs TF Bw Bw'
        pos sp1 F S2 mm mdx rg HFIX) end.
      -- unfold mon_ntc_cur.
         split; [exact (HCUR _ _ HJ2 KA1 GA1)|].
         split; [exact Eab2|].
         split; [exact HGEX|].
         split; [exact HTW1|].
         split; [exact HGO | exact HSTW].
      -- exact HREGN.
Qed.

End mh.
