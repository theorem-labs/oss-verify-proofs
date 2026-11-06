(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, origin/cold/pg-prog), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-10: the walk is reac-repacer/fuzz_uci's check_clamp in image A, in the shape of the released image-A walks proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_entry.v, .../LLVMFuzzerTestOneInput_seg_copy.v and .../LLVMFuzzerTestOneInput_seg_exit_tail.v at origin/ossv/recipes 88154566652a: module paths, listing symbol type, the symbolic states, the cut points and every address and offset are this function's; the fake-frame class is 1, the single intrinsic is __asan_memcpy of 20 bytes, and the result is the caller-journal contract of lib/A/Prog/check_clamp_cg.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths changed; 663 of its 1139 lines of code are new or changed and 8 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths, module names and numbers changed; 1969 of its 2149 lines of code are new or changed and 959 lines of the source are left out. *)
(* diginet_session_wake_seg_head: Lemma wake_head : wake_head_stmt (lib/A/Prog/diginet_session_wake_seg_cut.v), the
   head piece of the image-A ASan walk of diginet_session_wake (fuzz_transport.asan 0x866fc =
   transport_sigma TS_diginet_session_wake, AF_diginet_session_wake = 0x5498 of lib/A/Prog/DgnTransportList.v), from
   the entry to the three cuts it reaches: the release cut wake_rel_at (+0x434), the e2 cut wake_e2_at (+0x410) and
   the mid cut wake_mid_at (+0x264). The walk holds the caller's G journal (lib/A/W_journalG.v ajournal_gx G_HARNESS
   0 []); the runs are lib/A/Prog/TransportGRunA.v paj_run_x / paj_run_to_x, the splits paj_branch:
     run 1   +0x000 .. +0x070  the frame, `sd zero, 0(sp)`, the 13 saves (wh_saved, read back for wake_cur's saved
                               words), s0 = the entry sp, the realign into s1 (sp1, CanKit.v can_sp1_facts /
                               can_denot_and_m32), s4 = now, the flag word and the shadow base through their GOT words
                               (transport_cells: wh_img_ok), s3 = s, `beqz a2` not taken, a0 = 256, up to the jal;
     +0x070                    `jal __asan_stack_malloc_2`: lib/A/Prog/TransportGFrame.v gx_stack_malloc_at at
                               pc_stack_malloc (as_code B) WAKE_CID with the count premise; its acall_kept and
                               TransportGCg.v dk_kept_step_g / dk_kept_trans_g / gx_kept_of_acall_kept give what the call
                               kept so far and G kept;
     run 2a  +0x074 .. +0x0dc  `bnez s2` taken (F >= 4096), the frame word at s1 + 8, the 24-byte header, s8 = F's
                               shadow address (can_denot_shadow), up to the first shadow store;
     run 2b  +0x0e0 .. +0x160  the frame's 32 shadow bytes;
     run 2c  +0x164 .. +0x180  a0 = -1, `beqz s3` not taken, the checked 4-byte load of s + 116 (S_desk_known, the
                               record's zero shadow of g_s: wh_ra, decode_zshadow_rd), up to `beqz a1`;
     +0x184                    the split on S_desk_known Bw (DgnTransportPaLib.v paj_branch, wk_eqb): 0 goes to the
                               release cut with a0 = -1 and the model's world Bw (wake_model's first branch);
     run 3   +0x188 .. +0x1a8  the checked 4-byte load of s + 136 (S_foreign), s5 = s + 18224, up to `beqz a0`;
     +0x1ac                    the split on S_foreign Bw: not 0 runs the refused path +0x1b0 .. +0x1d4 (the checked
                               8-byte load at s + 18256, + 1, the store back: wh_tw_rf with wk_refused_eq; a0 = -10)
                               to the release cut;
     run 4a  +0x1d8 .. +0x220  the checked stores of 0 at s + 140, s + 144 and of now at s + 152 (wh_tw_w1 with
                               wk_w1_eq: the world wake_w1 Bw now), s6 = F + 144;
     run 4b  +0x224 .. +0x258  e2's shadow bytes 18 .. 25 := 0, .., 0, 4, the arguments, up to the jal;
     +0x25c                    `jal send_control`: send_control_cg.v transport_send_control_cg at
                               transport_sigma TS_send_control in the same G journal, with cmd = DIGINET_CMD_WAKE,
                               ack = 0, kp = F + 144 (e2 in the own frame: decode_in_fake, transport_twr_ok_g_intro,
                               wh_e2_rd), klp = sp1 + 16 (e2_len in the machine frame: the stack's zero shadow,
                               stack_zshadow_ra), the model equation from wake_model, the run invariants and
                               g_fail_next at wake_w1 Bw now (wk_w1_keep), trans_rom_view_rd (wh_rom); its post
                               transport_cg_post_out with the out cell [(klp, 8)] folds with TransportGCg.v
                               dk_kept_trans_nf_g (NF: the own frame's bytes, shadow and flag byte, and klp) and
                               wh_ungover (the out cell put back lies in the walk's own window);
     +0x260                    the split on `bltz a0` (wk_lts0, wk_sc_ret): a negative result goes to the e2 cut with
                               a0 = r and the world B1; otherwise the mid cut, with e2's 60 bytes, e2_len = 60, the
                               read facts of e2's range and the keeps of send_control_m (wk_sc_keep, wk_w1_keep).
   Every cut state's wake_cur is built once after the stack malloc and moved: wh_cur_step over a step that writes
   only the stack window, the own frame or G (wh_kept: TransportGCg.v dk_kept_step_g with dkg_nf_sep), wh_cur_move
   over a step that keeps every byte's view. *)
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
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0p YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c YO0f.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportSyms DgnTransportList DgnTransportAddr DgnTransportPa DgnTransportImg DgnTransportPaLib YC4b YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG AF0x.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportCg TransportGCg TransportGRwA TransportGRunA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA TImgA CanKit TransportGFrame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import m_lost_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import io_send_cg send_control_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
diginet_session_wake_cg diginet_session_wake_seg_cut diginet_session_wake_seg_keep.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TSess0 TSess TCb TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Mem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module FCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.AsanCells.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module DLib := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnLib.
Module LMem := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Mem.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

Definition WH_B0 : Z * Z := (0, 0).

(* run 1, +0x000 .. +0x070 *)
Definition wh_got_uar : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 0)) 0 8 0 0 [YP09.mkChunk 0 (YP09.CVal 8 (SOff (A_OBJ 94) 0))].
Definition wh_uar_cell : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 94)) 0 4 0 0 [YP09.mkChunk 0 (YP09.CVal 4 (SLit 1))].
Definition wh_img_regions : smem := [got_regionP; bcell_regionP 32; wh_got_uar; wh_uar_cell].
Definition wh_regions1 : smem := stack_region WAKE_FRAME :: wh_img_regions.
Definition wh_facts1 : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition ss_wh1 : sstate := mkSS AF_diginet_session_wake sr_atoms wh_regions1 None wh_facts1.

(* run 2a, +0x074 .. +0x0dc: after the stack malloc, the frame F in a0 (atom 10); the run stores the frame word at
   s1 + 8, writes the frame's 24-byte header and stops at the first shadow store (+0x0e0). *)
Definition WH_C1 : Z := AF_diginet_session_wake + 0x74.
Definition wh_rg_slot : YP09.region := YP09.mkRegion (Some 9%nat) 8 16 8 16 [].
Definition wh_rg_hdr : YP09.region := YP09.mkRegion (Some 10%nat) 0 24 0 24 [].
Definition wh_facts2 : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5);
           (10%nat, mkAF 4096 (2 ^ 47) 6); (26%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition ss_wh2 : sstate := mkSS WH_C1 sr_atoms [wh_rg_slot; wh_rg_hdr] None wh_facts2.

(* run 2b, +0x0e0 .. +0x160: s8 (atom 24) holds the frame's shadow address; the run writes the frame's 32 shadow
   bytes, up to +0x164. *)
Definition WH_C2 : Z := AF_diginet_session_wake + 0xe0.
Definition WH_C3 : Z := AF_diginet_session_wake + 0x164.
Definition wh_rg_sh : YP09.region := YP09.mkRegion (Some 24%nat) 0 32 0 32 [].
Definition wh_facts3 : facts := mkFacts [(24%nat, mkAF SHADOW_OFF (2 ^ 46) 0)] [] [].
Definition ss_wh3 : sstate := mkSS WH_C2 sr_atoms [wh_rg_sh] None wh_facts3.

(* run 2c, +0x164 .. +0x180: a0 = -1, `beqz s3` (not taken: s3 = s, atom 19), the checked 4-byte load of s + 116
   (atom 33, the 4 bytes of S_desk_known), up to `beqz a1` at +0x184. s10 (atom 26) is the shadow base. *)
Definition wh_rg_dk : YP09.region :=
  YP09.mkRegion (Some 19%nat) 116 120 0 0 [YP09.mkChunk 116 (YP09.CVal 4 (SOff 33 0))].
Definition wh_facts4 : facts :=
  mkFacts [(19%nat, mkAF WAKE_S WAKE_S 6); (26%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (33%nat, mkAF 0 (2 ^ 32 - 1) 0)] [] [].
Definition ss_wh4 : sstate := mkSS WH_C3 sr_atoms [wh_rg_dk] None wh_facts4.
Definition WH_SH4 : list shent := [mkSHE 19 116 120].
Definition WH_Bx : sv := SOff 26 0.

(* The branch points +0x184 (`beqz a1`), +0x1ac (`beqz a0`) and +0x260 (`bltz a0`), each taken up from a state with
   no region. *)
Definition WH_C4 : Z := AF_diginet_session_wake + 0x184.
Definition ss_wh0 (pc : Z) : sstate := mkSS pc sr_atoms [] None (mkFacts [] [] []).

(* run 3, +0x188 .. +0x1a8: the checked 4-byte load of s + 136 (atom 33, the 4 bytes of S_foreign), s5 = s + 18224,
   up to `beqz a0` at +0x1ac. *)
Definition WH_C5 : Z := AF_diginet_session_wake + 0x188.
Definition WH_C6 : Z := AF_diginet_session_wake + 0x1ac.
Definition wh_rg_fo : YP09.region :=
  YP09.mkRegion (Some 19%nat) 136 140 0 0 [YP09.mkChunk 136 (YP09.CVal 4 (SOff 33 0))].
Definition ss_wh6 : sstate := mkSS WH_C5 sr_atoms [wh_rg_fo] None wh_facts4.
Definition WH_SH6 : list shent := [mkSHE 19 136 140].

(* the refused path, +0x1b0 .. +0x1d4: the checked 8-byte load of s5 + 32 = s + 18256 (atom 33), + 1, the store
   back, a0 = -10, `j` to the release cut. s5 is atom 21. *)
Definition WH_C7 : Z := AF_diginet_session_wake + 0x1b0.
Definition wh_rg_rf : YP09.region :=
  YP09.mkRegion (Some 21%nat) 32 40 32 40 [YP09.mkChunk 32 (YP09.CVal 8 (SOff 33 0))].
Definition wh_facts7 : facts :=
  mkFacts [(21%nat, mkAF (WAKE_S + 18224) (WAKE_S + 18224) 4); (26%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition ss_wh7 : sstate := mkSS WH_C7 sr_atoms [wh_rg_rf] None wh_facts7.
Definition WH_SH7 : list shent := [mkSHE 21 32 40].

(* run 4a, +0x1d8 .. +0x220: the checked stores of 0 at s + 140 and s + 144 and of now at s + 152, s6 = F + 144, up
   to +0x224; run 4b, +0x224 .. +0x25c: the frame's shadow bytes 18 .. 25, the arguments and `jal send_control`. *)
Definition WH_C8 : Z := AF_diginet_session_wake + 0x1d8.
Definition WH_C8b : Z := AF_diginet_session_wake + 0x224.
Definition wh_rg_w1a : YP09.region := YP09.mkRegion (Some 19%nat) 140 148 140 148 [].
Definition wh_rg_w1b : YP09.region := YP09.mkRegion (Some 19%nat) 152 160 152 160 [].
Definition wh_facts8 : facts :=
  mkFacts [(19%nat, mkAF WAKE_S WAKE_S 6); (26%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition ss_wh8 : sstate := mkSS WH_C8 sr_atoms [wh_rg_w1a; wh_rg_w1b] None wh_facts8.
Definition WH_SH8 : list shent := [mkSHE 19 140 160].
Definition wh_rg_e2sh : YP09.region := YP09.mkRegion (Some 24%nat) 18 26 18 26 [].
Definition wh_facts8b : facts := mkFacts [(24%nat, mkAF SHADOW_OFF (2 ^ 46) 0)] [] [].
Definition ss_wh8b : sstate := mkSS WH_C8b sr_atoms [wh_rg_e2sh] None wh_facts8b.

(* After send_control returns, +0x260 (`bltz a0`). *)
Definition WH_C9 : Z := AF_diginet_session_wake + 0x260.

(* The two fields the branches read, at their numeral offsets in the world. *)
Lemma wh_dk_num : forall Bw, TW.S_desk_known Bw = bv_swrap 32 (TW.u_at Bw (TW.OFF_g_s + 116) 4).
Proof. intros Bw. reflexivity. Qed.
Lemma wh_fo_num : forall Bw, TW.S_foreign Bw = bv_swrap 32 (TW.u_at Bw (TW.OFF_g_s + 136) 4).
Proof. intros Bw. reflexivity. Qed.

(* send_control's X names e2's bytes and the length cell by a match on e2; with e2 <> [] they are e2 and 60. *)
Lemma wh_nonempty : forall (l d : list byte), l <> [] -> match l with [] => d | _ => l end = l.
Proof. intros l d H. destruct l; [contradiction H; reflexivity | reflexivity]. Qed.
Lemma wh_nonempty_put : forall (l d : list byte), l <> [] ->
  match l with [] => d | _ => TW.put 8 (Z.of_nat (length l)) end = TW.put 8 (Z.of_nat (length l)).
Proof. intros l d H. destruct l; [contradiction H; reflexivity | reflexivity]. Qed.

(* The refused path's store at s + 18256 keeps g_fail_next. *)
Lemma wh_refused_gfn : forall Bw v, length Bw = Z.to_nat TW.W_LEN ->
  TW.g_fail_next (TW.upd Bw (TW.OFF_g_s + 18256) (TW.put 8 v)) = TW.g_fail_next Bw.
Proof. intros Bw v HB. unfold TW.g_fail_next. wk_out. reflexivity. Qed.

(* A field of a row of TMAP_A is a range of G. *)
Lemma wh_twa_G : forall o b n k w a, In (o, b, n) TMAP_A -> o <= k -> k + w <= o + n ->
  twa_fld o b k w a -> inG TG.G_HARNESS a.
Proof.
intros o b n k w a Hin H1 H2 Ha. unfold twa_fld in Ha. unfold inG. apply Exists_exists. exists (b, n).
split; [exact (TMAP_A_in_G o b n Hin) | unfold in_zr; cbn [fst snd]; lia].
Qed.

Ltac wh_ioff := unfold io_send_cg.TW.A_GOT_e2, io_send_cg.TW.A_GOT_e3, io_send_cg.TW.A_GOT_acks,
  io_send_cg.TW.A_M_host_counter, io_send_cg.TW.A_M_next_ka, io_send_cg.TW.A_M_last_display,
  io_send_cg.TW.A_M_display_sent, io_send_cg.TW.A_M_fly_on, io_send_cg.TW.A_M_fly_cmd,
  io_send_cg.TW.A_M_fly_counter, io_send_cg.TW.A_M_fly_retries, io_send_cg.TW.A_M_fly_sent,
  io_send_cg.TW.A_M_fly_len, io_send_cg.TW.A_M_fly_frame, io_send_cg.TW.A_Cmd_st in *;
  unfold TW.OFF_g_fail_next, TW.OFF_GOT, TW.SZ_GOT, TW.OFF_g_last_counter, TW.SZ_g_last_counter, TW.OFF_M, TW.SZ_M,
  TC.SPEC_MAX_FRAME, TW.OFF_g_cmd, TW.SZ_g_cmd, TC.CMDS_MAX, TW.OFF_g_q, TW.SZ_g_q, TW.OFF_g_nq, TW.SZ_g_nq in *;
  unfold io_send_cg.TC.SPEC_MAX_FRAME, io_send_cg.TC.CMDS_MAX in *; lia.

(* io_send's stores (io_send_cg.v iosend_wr) are bytes of G. *)
Lemma wh_iosend_G : forall n a, iosend_wr n a -> inG TG.G_HARNESS a.
Proof.
intros n a H. unfold iosend_wr in H.
repeat match type of H with _ \/ _ => destruct H as [H | H] end;
  [ refine (wh_twa_G _ _ _ _ _ _ TMAP_A_g_fail_next _ _ H)
  | refine (wh_twa_G _ _ _ _ _ _ TMAP_A_GOT _ _ H)
  | refine (wh_twa_G _ _ _ _ _ _ TMAP_A_GOT _ _ H)
  | refine (wh_twa_G _ _ _ _ _ _ TMAP_A_GOT _ _ H)
  | refine (wh_twa_G _ _ _ _ _ _ TMAP_A_g_last_counter _ _ H)
  | refine (wh_twa_G _ _ _ _ _ _ TMAP_A_M _ _ H)
  | refine (wh_twa_G _ _ _ _ _ _ TMAP_A_M _ _ H)
  | refine (wh_twa_G _ _ _ _ _ _ TMAP_A_M _ _ H)
  | refine (wh_twa_G _ _ _ _ _ _ TMAP_A_M _ _ H)
  | refine (wh_twa_G _ _ _ _ _ _ TMAP_A_M _ _ H)
  | refine (wh_twa_G _ _ _ _ _ _ TMAP_A_M _ _ H)
  | refine (wh_twa_G _ _ _ _ _ _ TMAP_A_M _ _ H)
  | refine (wh_twa_G _ _ _ _ _ _ TMAP_A_M _ _ H)
  | refine (wh_twa_G _ _ _ _ _ _ TMAP_A_M _ _ H)
  | refine (wh_twa_G _ _ _ _ _ _ TMAP_A_M _ _ H)
  | refine (wh_twa_G _ _ _ _ _ _ TMAP_A_M _ _ H)
  | destruct H as (s & Hs & H); refine (wh_twa_G _ _ _ _ _ _ TMAP_A_g_cmd _ _ H)
  | refine (wh_twa_G _ _ _ _ _ _ TMAP_A_g_q _ _ H)
  | refine (wh_twa_G _ _ _ _ _ _ TMAP_A_g_nq _ _ H) ]; wh_ioff.
Qed.

Section sh. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

Lemma wh_vals : VAL (A_OBJ 1) = FCells.GOT_CELL_K /\ VAL (A_OBJ 93) = FCells.CELL_K /\
  VAL (A_OBJ 0) = FCells.GOT_UAR /\ VAL (A_OBJ 94) = FCells.UAR /\
  BASE + AF_diginet_session_wake = transport_sigma TS_diginet_session_wake.
Proof. vm_compute. repeat split. Qed.

(* The four image regions hold what transport_cells says they hold, at any AR state. *)
Lemma wh_img_ok : forall ly S (W : world segs) mem md (E : env),
  transport_cells B -> @AR rc segs B ly S W mem md ->
  ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1)) -> ew E (A_OBJ 93) = Z_to_bv 64 (VAL (A_OBJ 93)) ->
  ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0)) -> ew E (A_OBJ 94) = Z_to_bv 64 (VAL (A_OBJ 94)) ->
  ew E 32 = Z_to_bv 64 SHADOW_OFF ->
  Forall (region_ok segs E (mrestrict (w_H W) mem)) wh_img_regions /\
  pairwise_disjoint E wh_img_regions.
Proof.
  intros ly S W mem md E HCELLS HAR E1 E93 E0 E94 E32.
  destruct (HCELLS ly) as (I1 & I2 & _ & _ & _ & I6 & I7 & _).
  destruct wh_vals as (V1 & V93 & V0 & V94 & _).
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
  assert (R1 : 0 <= VAL (A_OBJ 1) < 2 ^ 47) by (rewrite V1; unfold FCells.GOT_CELL_K; lia).
  assert (R93 : 0 <= VAL (A_OBJ 93) < 2 ^ 47) by (rewrite V93; unfold FCells.CELL_K; lia).
  assert (R0 : 0 <= VAL (A_OBJ 0) < 2 ^ 47) by (rewrite V0; unfold FCells.GOT_UAR; lia).
  assert (R94 : 0 <= VAL (A_OBJ 94) < 2 ^ 47) by (rewrite V94; unfold FCells.UAR; lia).
  split.
  - unfold wh_img_regions, got_regionP, bcell_regionP, wh_got_uar, wh_uar_cell.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    + rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E1) by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val segs E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 93) 0) (VAL (A_OBJ 93)));
      [cbn [sv_denot]; rewrite E93, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      rewrite Z.add_0_r, V1, V93. exact (val_mem_of_rdword segs (w_H W) mem _ _ Kgot).
    + rewrite (VB (A_OBJ 93) (VAL (A_OBJ 93)) E93) by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val segs E _ (VAL (A_OBJ 93)) 0 8 (SOff 32 0) SHADOW_OFF);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | unfold SHADOW_OFF; zside | zside |].
      rewrite Z.add_0_r, V93. exact (val_mem_of_rdword segs (w_H W) mem _ _ Kcell).
    + rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E0) by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val segs E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 94) 0) (VAL (A_OBJ 94)));
      [cbn [sv_denot]; rewrite E94, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      rewrite Z.add_0_r, V0, V94. exact (val_mem_of_rdword segs (w_H W) mem _ _ Kguar).
    + rewrite (VB (A_OBJ 94) (VAL (A_OBJ 94)) E94) by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val segs E _ (VAL (A_OBJ 94)) 0 4 (SLit 1) 1); [reflexivity | zside | zside |].
      rewrite Z.add_0_r, V94. exact (can_val_mem_of_rd32 segs (w_H W) mem _ _ Kuar).
  - apply pairwise_disjoint_of_extents.
    unfold wh_img_regions, got_regionP, bcell_regionP, wh_got_uar, wh_uar_cell, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E1), (VB (A_OBJ 93) (VAL (A_OBJ 93)) E93),
      (VB (A_OBJ 0) (VAL (A_OBJ 0)) E0), (VB (A_OBJ 94) (VAL (A_OBJ 94)) E94) by lia.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    rewrite V1, V93, V0, V94. unfold FCells.GOT_CELL_K, FCells.CELL_K, FCells.GOT_UAR, FCells.UAR.
    repeat split; first [exact I | lia].
Qed.

(* The walk's valuation: the 32 registers and the shadow base (atom 32). *)
Definition wh_E (regs : bvmap 5 word) : env := Eimg (PI := PI_transport) (Ereg regs [w64 SHADOW_OFF]).

Lemma wh_ew_reg : forall regs n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (wh_E regs) n = YK11.getr regs r.
Proof. intros regs n r Hn. unfold wh_E. apply can_ew_Eimg_Ereg_nat. exact Hn. Qed.
Lemma wh_ew_32 : forall regs, ew (wh_E regs) 32 = Z_to_bv 64 SHADOW_OFF.
Proof. intros regs. unfold wh_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0). Qed.
Lemma wh_ew_obj : forall regs i, (i < 95)%nat -> ew (wh_E regs) (A_OBJ i) = Z_to_bv 64 (VAL (A_OBJ i)).
Proof. intros regs i Hi. unfold wh_E. apply Eimg_img. unfold A_OBJ, A_TEXT, A_LIM. lia. Qed.
Lemma wh_env_img : forall regs, img_env VAL A_LIM (wh_E regs).
Proof. intros regs. unfold wh_E. apply Eimg_env. Qed.

(* The entry state of run 1 (the saves go into the stack region). *)
Lemma wh_entry1 : forall ly S (W : world segs) regs mem md,
  transport_cells B -> @AR rc segs B ly S W mem md ->
  (forall a, spZ regs - WAKE_FRAME <= a < spZ regs -> apresent (w_H W) mem a) ->
  2 ^ 46 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
  st_ok_pi segs VAL (wh_E regs) ss_wh1
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + AF_diginet_session_wake)) mem (YK11.seg_rom segs))).
Proof.
  intros ly S W regs mem md HCELLS HAR Hpres Hsp Hsp16.
  rewrite restrict_mkst_fx. unfold ss_wh1, wh_regions1.
  assert (Usp : bv_unsigned (ew (wh_E regs) 2) = spZ regs)
    by (rewrite (wh_ew_reg regs 2 2%bv eq_refl); reflexivity).
  assert (E32 : ew (wh_E regs) 32 = Z_to_bv 64 SHADOW_OFF) by apply wh_ew_32.
  destruct (wh_img_ok ly S W mem md (wh_E regs) HCELLS HAR
    (wh_ew_obj regs 1 ltac:(lia)) (wh_ew_obj regs 93 ltac:(lia))
    (wh_ew_obj regs 0 ltac:(lia)) (wh_ew_obj regs 94 ltac:(lia)) E32) as [HRs HPd].
  destruct wh_vals as (V1 & V93 & V0 & V94 & _).
  assert (VB : forall n v0, ew (wh_E regs) n = Z_to_bv 64 v0 -> 0 <= v0 < 2 ^ 64 ->
    base_val (wh_E regs) (Some n) = v0)
    by (intros n v0 Hn Hv0; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hv0).
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [| exact HRs].
    unfold stack_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite Usp. unfold WAKE_FRAME in *.
    split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply Hpres. lia.
  - unfold wh_img_regions in *. apply pairwise_disjoint_of_extents.
    unfold stack_region, got_regionP, bcell_regionP, wh_got_uar, wh_uar_cell, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) (wh_ew_obj regs 1 ltac:(lia)))
      by (rewrite V1; unfold FCells.GOT_CELL_K; lia).
    rewrite (VB (A_OBJ 93) (VAL (A_OBJ 93)) (wh_ew_obj regs 93 ltac:(lia)))
      by (rewrite V93; unfold FCells.CELL_K; lia).
    rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) (wh_ew_obj regs 0 ltac:(lia)))
      by (rewrite V0; unfold FCells.GOT_UAR; lia).
    rewrite (VB (A_OBJ 94) (VAL (A_OBJ 94)) (wh_ew_obj regs 94 ltac:(lia)))
      by (rewrite V94; unfold FCells.UAR; lia).
    cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    rewrite V1, V93, V0, V94. unfold FCells.GOT_CELL_K, FCells.CELL_K, FCells.GOT_UAR, FCells.UAR, WAKE_FRAME.
    repeat split; first [exact I | lia].
  - unfold wh_facts1, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E32, unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; unfold SHADOW_OFF; lia.
Qed.

(* The entry state of run 2a: s1 (atom 9) = sp1, a0 (atom 10) = F, s10 (atom 26) = the shadow base; the frame word
   slot [sp1 + 8, sp1 + 16) and the header [F, F + 24). *)
Lemma wh_entry2 : forall (W : world segs) regs mem (F spv : Z),
  YK11.getr regs 2 = w64 spv -> YK11.getr regs 9 = w64 spv ->
  YK11.getr regs 10 = w64 F -> YK11.getr regs 26 = w64 SHADOW_OFF ->
  2 ^ 46 <= spv <= 2 ^ 47 - 16 -> spv mod 32 = 0 ->
  4096 <= F -> F + 256 <= 2 ^ 47 -> F mod 64 = 0 -> F + 256 <= spv ->
  (forall a, spv + 8 <= a < spv + 16 -> apresent (w_H W) mem a) ->
  (forall a, F <= a < F + 24 -> apresent (w_H W) mem a) ->
  st_ok_pi segs VAL (wh_E regs) ss_wh2
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + WH_C1)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem F spv R2 R9 R10 R26 Hsp Hsp32 HF0 HFs HF64 HFsp Hpslot Hpframe.
  rewrite restrict_mkst_fx. unfold ss_wh2.
  assert (U2 : bv_unsigned (ew (wh_E regs) 2) = spv)
    by (rewrite (wh_ew_reg regs 2 2%bv eq_refl), R2; apply unsigned_lit_small; lia).
  assert (U9 : bv_unsigned (ew (wh_E regs) 9) = spv)
    by (rewrite (wh_ew_reg regs 9 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
  assert (U10 : bv_unsigned (ew (wh_E regs) 10) = F)
    by (rewrite (wh_ew_reg regs 10 10%bv eq_refl), R10; apply unsigned_lit_small; lia).
  assert (U26 : bv_unsigned (ew (wh_E regs) 26) = SHADOW_OFF)
    by (rewrite (wh_ew_reg regs 26 26%bv eq_refl), R26; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (U32 : bv_unsigned (ew (wh_E regs) 32) = SHADOW_OFF)
    by (rewrite (wh_ew_32 regs); apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [wh_rg_slot wh_rg_hdr YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite U9. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Hpslot. lia.
    + rewrite U10. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Hpframe. lia.
  - apply pairwise_disjoint_of_extents.
    unfold wh_rg_slot, wh_rg_hdr, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite U9, U10. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; first [exact I | lia].
  - unfold wh_facts2, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U2, U9, U10, U26, U32.
    change (2 ^ 5) with 32. change (2 ^ 6) with 64. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; unfold SHADOW_OFF; lia.
Qed.

Lemma wh_entry3 : forall (W : world segs) regs mem (SH : Z),
  YK11.getr regs 24 = w64 SH -> SHADOW_OFF <= SH -> SH + 32 <= 2 ^ 46 ->
  (forall a, SH <= a < SH + 32 -> apresent (w_H W) mem a) ->
  st_ok_pi segs VAL (wh_E regs) ss_wh3
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + WH_C2)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem SH R24 Hlo Hhi Hpres.
  rewrite restrict_mkst_fx. unfold ss_wh3.
  assert (U24 : bv_unsigned (ew (wh_E regs) 24) = SH)
    by (rewrite (wh_ew_reg regs 24 24%bv eq_refl), R24; apply unsigned_lit_small; unfold SHADOW_OFF in *; lia).
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold wh_rg_sh, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U24. split; [unfold SHADOW_OFF in *; lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply Hpres. lia.
  - apply pairwise_disjoint_of_extents.
    unfold wh_rg_sh, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    cbn [zpairwise_disjoint zall_disjoint]. repeat split.
  - unfold wh_facts3, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U24. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; unfold SHADOW_OFF in *; lia.
Qed.

(* g_s's payload bytes are bytes of G. *)
Lemma wh_inG : forall a, WAKE_S <= a < WAKE_S + TW.SZ_g_s -> inG TG.G_HARNESS a.
Proof.
intros a Ha. unfold inG. apply Exists_exists. exists (0x5df9c0, 18264). split.
- unfold TG.G_HARNESS. cbn [In]. tauto.
- unfold in_zr, WAKE_S, TA_g_s, TW.SZ_g_s in *. cbn [fst snd]. lia.
Qed.

(* Every byte of g_s's payload is addressable at every AR state: whole granules of the record's zero shadow. *)
Lemma wh_ra : forall ly S (W : world segs) mem md lo n,
  trans_wake_cells B -> @AR rc segs B ly S W mem md ->
  0 <= lo -> lo + n <= TW.SZ_g_s ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF (WAKE_S + lo) n.
Proof.
intros ly S W mem md lo n HZ HAR Hlo Hn x Hx.
exists 0. split; [|left; reflexivity].
pose proof (Z.div_mod x 8 ltac:(lia)) as D8. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as M8.
assert (Hx8 : WAKE_S <= 8 * (x / 8) /\ 8 * (x / 8) + 8 <= WAKE_S + TW.SZ_g_s)
  by (unfold WAKE_S, TA_g_s, TW.SZ_g_s in *; lia).
assert (Hz := decode_zshadow_rd B ly S W mem md WAKE_S (WAKE_S + TW.SZ_g_s) (8 * (x / 8)) HAR
  ltac:(rewrite Z.mul_comm; apply Z_mod_mult) (proj1 Hx8) (proj2 Hx8) HZ).
unfold shadow_of_addr.
replace (SHADOW_OFF + x / 8) with (FCells.shadow_addr (8 * (x / 8))); [exact Hz|].
unfold FCells.shadow_addr, FCells.ASAN_K, SHADOW_OFF. rewrite Z.mul_comm, Z.div_mul by lia. lia.
Qed.

(* The valuation of a run that reads one field of g_s: the 32 registers, the shadow base (atom 32) and the field's
   bytes (atom 33). *)
Definition wh_Ev (regs : bvmap 5 word) (v : Z) : env :=
  Eimg (PI := PI_transport) (Ereg regs [w64 SHADOW_OFF; Z_to_bv 64 v]).

Lemma wh_ev_reg : forall regs v n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (wh_Ev regs v) n = YK11.getr regs r.
Proof. intros regs v n r Hn. unfold wh_Ev. apply can_ew_Eimg_Ereg_nat. exact Hn. Qed.
Lemma wh_ev_32 : forall regs v, ew (wh_Ev regs v) 32 = Z_to_bv 64 SHADOW_OFF.
Proof. intros regs v. unfold wh_Ev. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0). Qed.
Lemma wh_ev_33 : forall regs v, ew (wh_Ev regs v) 33 = Z_to_bv 64 v.
Proof. intros regs v. unfold wh_Ev. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 1). Qed.

Lemma wh_entry4 : forall ly S (W : world segs) regs mem md Bw,
  trans_wake_cells B -> @AR rc segs B ly S W mem md ->
  tw_at TMAP_A (aview segs (w_H W) mem) Bw ->
  YK11.getr regs 19 = w64 WAKE_S -> YK11.getr regs 26 = w64 SHADOW_OFF ->
  st_ok_pi segs VAL (wh_Ev regs (TW.u_at Bw (TW.OFF_g_s + 116) 4)) ss_wh4
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + WH_C3)) mem (YK11.seg_rom segs))) /\
  sh_ok segs WH_Bx WH_SH4 (wh_Ev regs (TW.u_at Bw (TW.OFF_g_s + 116) 4)) (mrestrict (w_H W) mem).
Proof.
intros ly S W regs mem md Bw HSC HAR Htw R19 R26.
set (v := TW.u_at Bw (TW.OFF_g_s + 116) 4).
assert (CS : WAKE_S = 6158784) by reflexivity.
assert (U19 : bv_unsigned (ew (wh_Ev regs v) 19) = WAKE_S)
  by (rewrite (wh_ev_reg regs v 19 19%bv eq_refl), R19; apply unsigned_lit_small; rewrite CS; lia).
assert (U26 : bv_unsigned (ew (wh_Ev regs v) 26) = SHADOW_OFF)
  by (rewrite (wh_ev_reg regs v 26 26%bv eq_refl), R26; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (R33 : 0 <= v < 2 ^ 32) by exact (TWL.u_at_range Bw _ 4).
assert (U33 : bv_unsigned (ew (wh_Ev regs v) 33) = v)
  by (rewrite wh_ev_33; apply unsigned_lit_small; lia).
split.
- rewrite restrict_mkst_fx. unfold ss_wh4.
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
    cbn [wh_rg_dk YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U19. split; [rewrite CS; lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val segs _ _ WAKE_S 116 4 (SOff 33 0) v);
      [cbn [sv_denot]; rewrite U33, Z.add_0_r; reflexivity | exact R33 | lia |].
    exact (tw_read_val segs _ TMAP_A Bw TW.OFF_g_s TA_g_s TW.SZ_g_s 116 4 TMAP_A_ok Htw TMAP_A_g_s
      ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
  + apply pairwise_disjoint_of_extents.
    unfold wh_rg_dk, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    cbn [zpairwise_disjoint zall_disjoint]. repeat split.
  + unfold wh_facts4, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U19, U26, U33.
    change (2 ^ 6) with 64. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; rewrite ?CS; unfold SHADOW_OFF;
    first [lia | reflexivity].
- pose proof (wh_ra ly S W mem md 116 4 HSC HAR ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)) as HRA.
  assert (UB : U (wh_Ev regs v) WH_Bx = SHADOW_OFF).
  { unfold U, WH_Bx. cbn [sv_denot]. rewrite U26, Z.add_0_r. apply unsigned_lit_small. unfold SHADOW_OFF; lia. }
  unfold sh_ok, WH_SH4. constructor; [|constructor].
  apply (shent_ok_of_range segs (w_H W) mem _ WH_Bx 19 (WAKE_S + 116) 4 WAKE_S 116 120 HRA UB).
  + unfold U. cbn [sv_denot]. rewrite U19, Z.add_0_r. apply unsigned_lit_small. rewrite CS; lia.
  + lia.
  + lia.
  + intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF. lia.
Qed.

Lemma wh_entry6 : forall ly S (W : world segs) regs mem md Bw,
  trans_wake_cells B -> @AR rc segs B ly S W mem md ->
  tw_at TMAP_A (aview segs (w_H W) mem) Bw ->
  YK11.getr regs 19 = w64 WAKE_S -> YK11.getr regs 26 = w64 SHADOW_OFF ->
  st_ok_pi segs VAL (wh_Ev regs (TW.u_at Bw (TW.OFF_g_s + 136) 4)) ss_wh6
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + WH_C5)) mem (YK11.seg_rom segs))) /\
  sh_ok segs WH_Bx WH_SH6 (wh_Ev regs (TW.u_at Bw (TW.OFF_g_s + 136) 4)) (mrestrict (w_H W) mem).
Proof.
intros ly S W regs mem md Bw HSC HAR Htw R19 R26.
set (v := TW.u_at Bw (TW.OFF_g_s + 136) 4).
assert (CS : WAKE_S = 6158784) by reflexivity.
assert (U19 : bv_unsigned (ew (wh_Ev regs v) 19) = WAKE_S)
  by (rewrite (wh_ev_reg regs v 19 19%bv eq_refl), R19; apply unsigned_lit_small; rewrite CS; lia).
assert (U26 : bv_unsigned (ew (wh_Ev regs v) 26) = SHADOW_OFF)
  by (rewrite (wh_ev_reg regs v 26 26%bv eq_refl), R26; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (R33 : 0 <= v < 2 ^ 32) by exact (TWL.u_at_range Bw _ 4).
assert (U33 : bv_unsigned (ew (wh_Ev regs v) 33) = v)
  by (rewrite wh_ev_33; apply unsigned_lit_small; lia).
split.
- rewrite restrict_mkst_fx. unfold ss_wh6.
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
    cbn [wh_rg_fo YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U19. split; [rewrite CS; lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val segs _ _ WAKE_S 136 4 (SOff 33 0) v);
      [cbn [sv_denot]; rewrite U33, Z.add_0_r; reflexivity | exact R33 | lia |].
    exact (tw_read_val segs _ TMAP_A Bw TW.OFF_g_s TA_g_s TW.SZ_g_s 136 4 TMAP_A_ok Htw TMAP_A_g_s
      ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
  + apply pairwise_disjoint_of_extents.
    unfold wh_rg_fo, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    cbn [zpairwise_disjoint zall_disjoint]. repeat split.
  + unfold wh_facts4, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U19, U26, U33.
    change (2 ^ 6) with 64. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; rewrite ?CS; unfold SHADOW_OFF;
    first [lia | reflexivity].
- pose proof (wh_ra ly S W mem md 136 4 HSC HAR ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)) as HRA.
  assert (UB : U (wh_Ev regs v) WH_Bx = SHADOW_OFF).
  { unfold U, WH_Bx. cbn [sv_denot]. rewrite U26, Z.add_0_r. apply unsigned_lit_small. unfold SHADOW_OFF; lia. }
  unfold sh_ok, WH_SH6. constructor; [|constructor].
  apply (shent_ok_of_range segs (w_H W) mem _ WH_Bx 19 (WAKE_S + 136) 4 WAKE_S 136 140 HRA UB).
  + unfold U. cbn [sv_denot]. rewrite U19, Z.add_0_r. apply unsigned_lit_small. rewrite CS; lia.
  + lia.
  + lia.
  + intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF. lia.
Qed.

Lemma wh_entry7 : forall ly S (W : world segs) regs mem md Bw,
  trans_wake_cells B -> @AR rc segs B ly S W mem md ->
  tw_at TMAP_A (aview segs (w_H W) mem) Bw ->
  YK11.getr regs 21 = w64 (WAKE_S + 18224) -> YK11.getr regs 26 = w64 SHADOW_OFF ->
  st_ok_pi segs VAL (wh_Ev regs (TW.u_at Bw (TW.OFF_g_s + 18256) 8)) ss_wh7
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + WH_C7)) mem (YK11.seg_rom segs))) /\
  sh_ok segs WH_Bx WH_SH7 (wh_Ev regs (TW.u_at Bw (TW.OFF_g_s + 18256) 8)) (mrestrict (w_H W) mem).
Proof.
intros ly S W regs mem md Bw HSC HAR Htw R21 R26.
set (v := TW.u_at Bw (TW.OFF_g_s + 18256) 8).
assert (CS : WAKE_S = 6158784) by reflexivity.
assert (U21 : bv_unsigned (ew (wh_Ev regs v) 21) = WAKE_S + 18224)
  by (rewrite (wh_ev_reg regs v 21 21%bv eq_refl), R21; apply unsigned_lit_small; rewrite CS; lia).
assert (U26 : bv_unsigned (ew (wh_Ev regs v) 26) = SHADOW_OFF)
  by (rewrite (wh_ev_reg regs v 26 26%bv eq_refl), R26; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (R33 : 0 <= v < 2 ^ 64) by exact (TWL.u_at_range Bw _ 8).
assert (U33 : bv_unsigned (ew (wh_Ev regs v) 33) = v)
  by (rewrite wh_ev_33; apply unsigned_lit_small; lia).
split.
- rewrite restrict_mkst_fx. unfold ss_wh7.
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
    cbn [wh_rg_rf YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U21. split; [rewrite CS; lia|]. split; [lia|]. split.
    * intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (WAKE_S + 18224 + o) G_HARNESS_rw).
      apply wh_inG. unfold TW.SZ_g_s. lia.
    * constructor; [|constructor].
      apply (chunk_ok_val segs _ _ (WAKE_S + 18224) 32 8 (SOff 33 0) v);
        [cbn [sv_denot]; rewrite U33, Z.add_0_r; reflexivity | exact R33 | lia |].
      replace (WAKE_S + 18224 + 32) with (TA_g_s + 18256) by (unfold WAKE_S; lia).
      exact (tw_read_val segs _ TMAP_A Bw TW.OFF_g_s TA_g_s TW.SZ_g_s 18256 8 TMAP_A_ok Htw TMAP_A_g_s
        ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
  + apply pairwise_disjoint_of_extents.
    unfold wh_rg_rf, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    cbn [zpairwise_disjoint zall_disjoint]. repeat split.
  + unfold wh_facts7, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U21, U26.
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; rewrite ?CS; unfold SHADOW_OFF;
    first [lia | reflexivity].
- pose proof (wh_ra ly S W mem md 18256 8 HSC HAR ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)) as HRA.
  assert (UB : U (wh_Ev regs v) WH_Bx = SHADOW_OFF).
  { unfold U, WH_Bx. cbn [sv_denot]. rewrite U26, Z.add_0_r. apply unsigned_lit_small. unfold SHADOW_OFF; lia. }
  unfold sh_ok, WH_SH7. constructor; [|constructor].
  apply (shent_ok_of_range segs (w_H W) mem _ WH_Bx 21 (WAKE_S + 18256) 8 (WAKE_S + 18224) 32 40 HRA UB).
  + unfold U. cbn [sv_denot]. rewrite U21, Z.add_0_r. apply unsigned_lit_small. rewrite CS; lia.
  + lia.
  + lia.
  + intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF. lia.
Qed.

Lemma wh_entry8 : forall ly S (W : world segs) regs mem md,
  trans_wake_cells B -> @AR rc segs B ly S W mem md ->
  YK11.getr regs 19 = w64 WAKE_S -> YK11.getr regs 26 = w64 SHADOW_OFF ->
  st_ok_pi segs VAL (wh_E regs) ss_wh8
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + WH_C8)) mem (YK11.seg_rom segs))) /\
  sh_ok segs WH_Bx WH_SH8 (wh_E regs) (mrestrict (w_H W) mem).
Proof.
intros ly S W regs mem md HSC HAR R19 R26.
assert (CS : WAKE_S = 6158784) by reflexivity.
assert (U19 : bv_unsigned (ew (wh_E regs) 19) = WAKE_S)
  by (rewrite (wh_ew_reg regs 19 19%bv eq_refl), R19; apply unsigned_lit_small; rewrite CS; lia).
assert (U26 : bv_unsigned (ew (wh_E regs) 26) = SHADOW_OFF)
  by (rewrite (wh_ew_reg regs 26 26%bv eq_refl), R26; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
split.
- rewrite restrict_mkst_fx. unfold ss_wh8.
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [wh_rg_w1a wh_rg_w1b YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    * rewrite U19. split; [rewrite CS; lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (WAKE_S + o) G_HARNESS_rw).
      apply wh_inG. unfold TW.SZ_g_s. lia.
    * rewrite U19. split; [rewrite CS; lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (WAKE_S + o) G_HARNESS_rw).
      apply wh_inG. unfold TW.SZ_g_s. lia.
  + apply pairwise_disjoint_of_extents.
    unfold wh_rg_w1a, wh_rg_w1b, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite U19. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; first [exact I | rewrite ?CS; lia].
  + unfold wh_facts8, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U19, U26.
    change (2 ^ 6) with 64. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; rewrite ?CS; unfold SHADOW_OFF in *;
    first [lia | reflexivity].
- pose proof (wh_ra ly S W mem md 140 20 HSC HAR ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)) as HRA.
  assert (UB : U (wh_E regs) WH_Bx = SHADOW_OFF).
  { unfold U, WH_Bx. cbn [sv_denot]. rewrite U26, Z.add_0_r. apply unsigned_lit_small. unfold SHADOW_OFF; lia. }
  unfold sh_ok, WH_SH8. constructor; [|constructor].
  apply (shent_ok_of_range segs (w_H W) mem _ WH_Bx 19 (WAKE_S + 140) 20 WAKE_S 140 160 HRA UB).
  + unfold U. cbn [sv_denot]. rewrite U19, Z.add_0_r. apply unsigned_lit_small. rewrite CS; lia.
  + lia.
  + lia.
  + intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF. lia.
Qed.

Lemma wh_entry8b : forall (W : world segs) regs mem (SH : Z),
  YK11.getr regs 24 = w64 SH -> SHADOW_OFF <= SH -> SH + 32 <= 2 ^ 46 ->
  (forall a, SH + 18 <= a < SH + 26 -> apresent (w_H W) mem a) ->
  st_ok_pi segs VAL (wh_E regs) ss_wh8b
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + WH_C8b)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem SH R24 Hlo Hhi Hpres.
  rewrite restrict_mkst_fx. unfold ss_wh8b.
  assert (U24 : bv_unsigned (ew (wh_E regs) 24) = SH)
    by (rewrite (wh_ew_reg regs 24 24%bv eq_refl), R24; apply unsigned_lit_small; unfold SHADOW_OFF in *; lia).
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold wh_rg_e2sh, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U24. split; [unfold SHADOW_OFF in *; lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply Hpres. lia.
  - apply pairwise_disjoint_of_extents.
    unfold wh_rg_e2sh, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    cbn [zpairwise_disjoint zall_disjoint]. repeat split.
  - unfold wh_facts8b, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U24. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; unfold SHADOW_OFF in *; lia.
Qed.

(* A region cell of n bytes holding v, read byte by byte through the view. *)
Lemma wh_aview_of_val : forall H (m : word -> option byte) a (n : nat) v j,
  val_mem segs (mrestrict H m) a n v -> (j < n)%nat ->
  aview segs H m (a + Z.of_nat j) = Some (YO0f.le_byte v n j).
Proof.
intros H m a n v j HV Hj. unfold aview. rewrite (HV j Hj). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
apply Z.mod_small. unfold YO0f.le_byte. apply Z.mod_pos_bound. lia.
Qed.

(* A store of w bytes of a register holding v leaves v's low w bytes. *)
Lemma wh_vm_w : forall (m : word -> option byte) a (w : N) v, Z.of_N w <= 8 ->
  val_mem segs m a (N.to_nat w) (bv_unsigned (Z_to_bv 64 v) mod 2 ^ (8 * Z.of_N w)) -> val_mem segs m a (N.to_nat w) v.
Proof.
  intros m a w v Hw H.
  assert (Hd : (2 ^ (8 * Z.of_N w) | 2 ^ 64)).
  { exists (2 ^ (64 - 8 * Z.of_N w)). rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  assert (E : (bv_unsigned (Z_to_bv 64 v) mod 2 ^ (8 * Z.of_N w)) mod 2 ^ (8 * Z.of_N w) = v mod 2 ^ (8 * Z.of_N w)).
  { rewrite Zmod_mod, Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    apply Z.mod_mod_divide; try exact Hd; try (apply Z.pow_nonzero; lia); try (apply Z.pow_pos_nonneg; lia). }
  intros k Hk. rewrite (H k Hk). unfold YO0f.le_byte. rewrite N_nat_Z, E. reflexivity.
Qed.

(* A chunk of w bytes of the value e reads, byte k, the k-th little-endian byte of e. *)
Lemma wh_chunk_val : forall E (H : word -> bool) (m : word -> option byte) bopt lo hi wlo whi cs off (w : N) e,
  region_ok segs E (mrestrict H m) (YP09.mkRegion bopt lo hi wlo whi cs) ->
  In (YP09.mkChunk off (YP09.CVal w e)) cs -> (Z.of_N w <= 8) ->
  val_mem segs (mrestrict H m) (base_val E bopt + off) (N.to_nat w)
    (bv_unsigned (sv_denot E e) mod 2 ^ (8 * Z.of_N w)).
Proof.
  intros E H m bopt lo hi wlo whi cs off w e (_ & _ & _ & Hcs) Hin Hw.
  pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hc. cbn [YP09.r_base] in Hc.
  exact (val_of_chunk_any segs E _ _ off w e Hc Hw).
Qed.

(* The bytes a chunk of w bytes holding the register value v leaves, read through the view. *)
Lemma wh_chunk_bytes : forall E (H : word -> bool) (m : word -> option byte) bopt lo hi wlo whi cs off (w : N) e v,
  region_ok segs E (mrestrict H m) (YP09.mkRegion bopt lo hi wlo whi cs) ->
  In (YP09.mkChunk off (YP09.CVal w e)) cs -> (Z.of_N w <= 8) -> sv_denot E e = Z_to_bv 64 v ->
  forall j, (j < N.to_nat w)%nat ->
  aview segs H m (base_val E bopt + off + Z.of_nat j) = Some (YO0f.le_byte v (N.to_nat w) j).
Proof.
  intros E H m bopt lo hi wlo whi cs off w e v HR Hin Hw He j Hj.
  pose proof (wh_chunk_val E H m bopt lo hi wlo whi cs off w e HR Hin Hw) as HV. rewrite He in HV.
  exact (wh_aview_of_val H m _ _ v j (wh_vm_w _ _ w v Hw HV) Hj).
Qed.

(* The shadow hull of a range of a 64-aligned frame of fs bytes (a multiple of 64) lies in the frame's fs / 8
   shadow bytes. *)
Lemma wh_hull_in : forall (rd : Z -> option Z) Fc fs q n,
  0 <= Fc -> Fc mod 64 = 0 -> fs mod 64 = 0 -> 64 <= fs -> Fc <= q -> 0 <= n -> q + n <= Fc + fs ->
  (forall i, 0 <= i < fs / 8 -> rd (SHADOW_OFF + Fc / 8 + i) <> None) ->
  shadow_hull_vis rd q n.
Proof.
  intros rd Fc fs q n HF0 HF64 Hfs64 Hfs Hq Hn Hqn HV s Hs.
  unfold shadow_addr, SHADOW_OFF in Hs.
  pose proof (Z.div_mod Fc 64 ltac:(lia)) as DF. rewrite HF64, Z.add_0_r in DF.
  pose proof (Z.div_mod fs 64 ltac:(lia)) as DS. rewrite Hfs64, Z.add_0_r in DS.
  set (g := Fc / 64) in *. set (h := fs / 64) in *.
  assert (EF8 : Fc / 8 = 8 * g) by (rewrite DF; replace (64 * g) with ((8 * g) * 8) by ring; apply Z.div_mul; lia).
  assert (ES8 : fs / 8 = 8 * h) by (rewrite DS; replace (64 * h) with ((8 * h) * 8) by ring; apply Z.div_mul; lia).
  assert (Hg : 0 <= g) by lia. assert (Hh : 1 <= h) by lia.
  assert (L1 : 8 * g <= q / 8) by (apply Z.div_le_lower_bound; lia).
  assert (L2 : (q + n - 1) / 8 < 8 * g + 8 * h) by (apply Z.div_lt_upper_bound; lia).
  assert (A1 : 268431360 + g <= (2147450880 + q / 8) / 8) by (apply Z.div_le_lower_bound; lia).
  assert (A2 : (2147450880 + (q + n - 1) / 8) / 8 < 268431360 + g + h) by (apply Z.div_lt_upper_bound; lia).
  replace s with (SHADOW_OFF + Fc / 8 + (s - (SHADOW_OFF + Fc / 8))) by ring.
  apply HV. rewrite ES8. unfold SHADOW_OFF. rewrite EF8. lia.
Qed.

(* e2's 60 bytes at F + 144, with the frame's shadow bytes 18 .. 25 = 0, .., 0, 4: what __asan_memcpy's source check
   and send_control's keep disjunction read. *)
Lemma wh_e2_rd : forall (W2 : world segs) mem2 F,
  4096 <= F -> F mod 64 = 0 -> in_app F 256 ->
  (forall a, F + 144 <= a < F + 204 -> aview segs (w_H W2) mem2 a <> None) ->
  (forall i, 0 <= i < 32 -> aview segs (w_H W2) mem2 (SHADOW_OFF + F / 8 + i) <> None) ->
  (forall i, 0 <= i < 8 ->
     aview segs (w_H W2) mem2 (SHADOW_OFF + F / 8 + 18 + i) = Some (if i <? 7 then 0 else 4)) ->
  decode_rd_ok W2 mem2 (F + 144) SENDCTL_F.
Proof.
  intros W2 mem2 F HF0 HF64 HFapp Hv Hsv Hsh. unfold SENDCTL_F.
  pose proof (Z.div_mod F 64 ltac:(lia)) as DF. rewrite HF64, Z.add_0_r in DF.
  assert (HF8 : F mod 8 = 0) by (rewrite DF; replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by ring;
    apply Z.mod_mul; lia).
  pose proof (Z.div_mod F 8 ltac:(lia)) as DF8. rewrite HF8, Z.add_0_r in DF8.
  assert (ES : (F + 144) / 8 = F / 8 + 18).
  { rewrite DF8 at 1. replace (8 * (F / 8) + 144) with ((F / 8 + 18) * 8) by ring. apply Z.div_mul. lia. }
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp. pose proof asan_consts as (C1 & _).
  split; [intros a Ha; apply Hv; lia|]. split; [|split; [|split]].
  - apply (block_shadow_range _ SHADOW_OFF (F + 144) 60 (F + 144) 60); [| lia | lia].
    split; [rewrite Z.add_mod, HF8 by lia; reflexivity|]. split; [lia|].
    intros i Hi. change ((60 + 7) / 8) with 8 in Hi. change (60 / 8) with 7. change (60 mod 8) with 4.
    unfold shadow_of_addr. rewrite ES. rewrite Z.add_assoc. exact (Hsh i Hi).
  - apply (wh_hull_in _ F 256 (F + 144) 60); [lia | exact HF64 | reflexivity | lia | lia | lia | lia |].
    change (256 / 8) with 32. exact Hsv.
  - unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd. lia.
  - lia.
Qed.

(* The bytes of a garr8 array are visible. *)
Lemma wh_garr8_vis : forall H (m : word -> option byte) a (l : list Z),
  garr8 segs (mrestrict H m) a l -> forall x, a <= x < a + Z.of_nat (length l) -> aview segs H m x <> None.
Proof.
intros H m a l HG x Hx.
pose proof (garr8_mbyte segs (mrestrict H m) a l (Z.to_nat (x - a)) HG ltac:(lia)) as Hb.
rewrite Z2Nat.id in Hb by lia. replace (a + (x - a)) with x in Hb by lia.
unfold aview. rewrite Hb. cbn [option_map]. discriminate.
Qed.

(* garr8 at a later memory whose view agrees on the array's bytes. *)
Lemma wh_garr8_move : forall H (m m' : word -> option byte) a (l : list Z),
  garr8 segs (mrestrict H m) a l ->
  (forall x, a <= x < a + Z.of_nat (length l) -> aview segs H m' x = aview segs H m x) ->
  garr8 segs (mrestrict H m') a l.
Proof.
intros H m m' a l HG HV. apply (garr8_frame segs (mrestrict H m)); [exact HG|].
intros x Hx. apply can_mbyte_of_aview. exact (HV x Hx).
Qed.

(* A kept fact read at the memory with the out cells put back holds at the returned memory when the out cells lie
   in the window and are present there. *)
Lemma wh_ungover : forall outs lyc Sc (W : world segs) memc mdc (W2 : world segs) mem2 memX slo shi (Eo : Z -> Prop),
  AR_laws segs B -> @AR rc segs B lyc Sc W memc mdc ->
  alloc_ceiling <= slo -> shi <= 2 ^ 64 ->
  (forall a, inG outs a -> slo <= a < shi) ->
  (forall a, inG outs a -> apresent (w_H W2) mem2 a) ->
  acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W2 (gover outs mem2 memX) slo shi Eo ->
  acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W2 mem2 slo shi Eo.
Proof.
intros outs lyc Sc W memc mdc W2 mem2 memX slo shi Eo LAWS HAR Hce Hshi Hout Hpres (K1 & K2 & K3 & K4 & K5 & K6).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HnG : forall a, a < alloc_ceiling -> ~ inG outs a) by (intros a Ha Hin; pose proof (Hout a Hin); lia).
assert (Hgv : forall a, 0 <= a < 2 ^ 64 -> ~ inG outs a ->
  aview segs (w_H W2) (gover outs mem2 memX) a = aview segs (w_H W2) mem2 a)
  by (intros a Ha Hn; exact (gover_out_aview segs outs (w_H W2) mem2 memX a Ha Hn)).
assert (Hgp : forall a, 0 <= a < 2 ^ 64 -> ~ inG outs a ->
  apresent (w_H W2) (gover outs mem2 memX) a -> apresent (w_H W2) mem2 a)
  by (intros a Ha Hn Hp; exact (gover_out_apresent outs (w_H W2) mem2 memX a Ha Hn Hp)).
split; [|split; [|split; [|split; [|split]]]].
- intros a Ha Hw. assert (Hn : ~ inG outs a) by (intros Hin; pose proof (Hout a Hin); lia).
  rewrite <- (Hgv a ltac:(lia) Hn). apply K1; assumption.
- intros b n i Hb Hi Hn.
  destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b n HAR Hb) as (_ & H4096 & Hbce & _).
  assert (Hno : ~ inG outs (b + i)) by (apply HnG; lia).
  rewrite <- (Hgv (b + i) ltac:(lia) Hno). apply (K2 b n i Hb Hi Hn).
- intros a Hi HnGg Hno He. pose proof (transport_segs_low a Hi) as Hlow. unfold kLowMemEnd in Hlow.
  assert (Hn : ~ inG outs a) by (apply HnG; lia).
  rewrite <- (Hgv a ltac:(lia) Hn). apply K3; assumption.
- intros cid pos a Hin Hr Hn.
  destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (F4096 & Fce & _).
  pose proof (fs_frame_bytes_nonneg cid) as Hfs.
  assert (Ha : 0 <= a < alloc_ceiling).
  { destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [lia|].
    pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hfs) as Hse.
    assert (Hd : (frame_addr lyc cid pos + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
    pose proof (Z.div_pos (frame_addr lyc cid pos) 8 ltac:(lia) ltac:(lia)).
    unfold shadow_addr, SHADOW_OFF in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia. }
  assert (Hn2 : ~ inG outs a) by (apply HnG; lia).
  rewrite <- (Hgv a ltac:(lia) Hn2). apply (K4 cid pos a Hin Hr Hn).
- intros a Ha Hw Hp. assert (Hn : ~ inG outs a) by (intros Hin; pose proof (Hout a Hin); lia).
  apply (Hgp a ltac:(lia) Hn). apply K5; assumption.
- intros a Ha. destruct (inGb outs a) eqn:Eb.
  + exact (Hpres a (proj1 (inGb_spec outs a) Eb)).
  + assert (Hn : ~ inG outs a) by (apply inGb_false; exact Eb).
    apply (Hgp a ltac:(lia) Hn). apply K6. exact Ha.
Qed.

(* The world relation after the three stores of :129-131 (s + 140, s + 144, s + 152). *)
Lemma wh_tw_w1 : forall (rd rd' : Z -> option Z) Bw now,
  tw_at TMAP_A rd Bw ->
  (forall j, (j < 4)%nat -> rd' (TA_g_s + 140 + Z.of_nat j) = Some (YO0f.le_byte 0 4 j)) ->
  (forall j, (j < 4)%nat -> rd' (TA_g_s + 144 + Z.of_nat j) = Some (YO0f.le_byte 0 4 j)) ->
  (forall j, (j < 8)%nat -> rd' (TA_g_s + 152 + Z.of_nat j) = Some (YO0f.le_byte now 8 j)) ->
  (forall x, tw_in TMAP_A x -> ~ (TA_g_s + 140 <= x < TA_g_s + 148) -> ~ (TA_g_s + 152 <= x < TA_g_s + 160) ->
     rd' x = rd x) ->
  tw_at TMAP_A rd' (wake_w1 Bw now).
Proof.
intros rd rd' Bw now Hat H1 H2 H3 HO.
set (rdA := fun x => if ((TA_g_s + 144 <=? x) && (x <? TA_g_s + 160))%bool then rd x else rd' x).
set (rdB := fun x => if ((TA_g_s + 152 <=? x) && (x <? TA_g_s + 160))%bool then rd x else rd' x).
assert (HA : tw_at TMAP_A rdA (TW.upd Bw (TW.OFF_g_s + 140) (TW.put 4 0))).
{ apply (tw_write TMAP_A rd rdA Bw TW.OFF_g_s TA_g_s TW.SZ_g_s 140 4 0 TMAP_A_ok Hat TMAP_A_g_s);
    [lia | unfold TW.SZ_g_s; lia | |].
  - intros j Hj. unfold rdA.
    assert (Hb : ((TA_g_s + 144 <=? TA_g_s + 140 + Z.of_nat j) && (TA_g_s + 140 + Z.of_nat j <? TA_g_s + 160))%bool
      = false) by (apply andb_false_iff; left; apply Z.leb_gt; lia).
    rewrite Hb. exact (H1 j Hj).
  - intros x Hx Hn. unfold rdA.
    destruct ((TA_g_s + 144 <=? x) && (x <? TA_g_s + 160))%bool eqn:Eb; [reflexivity|].
    apply andb_false_iff in Eb.
    assert (Hx2 : x < TA_g_s + 144 \/ TA_g_s + 160 <= x)
      by (destruct Eb as [Eb | Eb]; [apply Z.leb_gt in Eb | apply Z.ltb_ge in Eb]; lia).
    apply HO; [exact Hx | lia | lia]. }
assert (HB : tw_at TMAP_A rdB (TW.upd (TW.upd Bw (TW.OFF_g_s + 140) (TW.put 4 0)) (TW.OFF_g_s + 144) (TW.put 4 0))).
{ apply (tw_write TMAP_A rdA rdB _ TW.OFF_g_s TA_g_s TW.SZ_g_s 144 4 0 TMAP_A_ok HA TMAP_A_g_s);
    [lia | unfold TW.SZ_g_s; lia | |].
  - intros j Hj. unfold rdB.
    assert (Hb : ((TA_g_s + 152 <=? TA_g_s + 144 + Z.of_nat j) && (TA_g_s + 144 + Z.of_nat j <? TA_g_s + 160))%bool
      = false) by (apply andb_false_iff; left; apply Z.leb_gt; lia).
    rewrite Hb. exact (H2 j Hj).
  - intros x Hx Hn. unfold rdA, rdB.
    destruct ((TA_g_s + 152 <=? x) && (x <? TA_g_s + 160))%bool eqn:Eb.
    + apply andb_true_iff in Eb. destruct Eb as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
      assert (Hb : ((TA_g_s + 144 <=? x) && (x <? TA_g_s + 160))%bool = true)
        by (apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
      rewrite Hb. reflexivity.
    + apply andb_false_iff in Eb.
      destruct ((TA_g_s + 144 <=? x) && (x <? TA_g_s + 160))%bool eqn:Eb2; [|reflexivity].
      apply andb_true_iff in Eb2. destruct Eb2 as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
      apply HO; [exact Hx | lia |].
      destruct Eb as [Eb | Eb]; [apply Z.leb_gt in Eb | apply Z.ltb_ge in Eb]; lia. }
rewrite wk_w1_eq.
change TW.A_S_e1_named_us with (TW.OFF_g_s + 140). change TW.A_S_wake_acked with (TW.OFF_g_s + 144).
change TW.A_S_wake_sent_us with (TW.OFF_g_s + 152).
apply (tw_write TMAP_A rdB rd' _ TW.OFF_g_s TA_g_s TW.SZ_g_s 152 8 now TMAP_A_ok HB TMAP_A_g_s);
  [lia | unfold TW.SZ_g_s; lia | |].
- intros j Hj. exact (H3 j Hj).
- intros x Hx Hn. unfold rdB.
  destruct ((TA_g_s + 152 <=? x) && (x <? TA_g_s + 160))%bool eqn:Eb; [|reflexivity].
  apply andb_true_iff in Eb. destruct Eb as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
  exfalso. apply Hn. lia.
Qed.

(* The bytes of a present range, as a list. *)
Lemma wh_garr8_ex : forall H (m : word -> option byte) base (n : nat),
  (forall a, base <= a < base + Z.of_nat n -> apresent H m a) ->
  exists K : list byte, length K = n /\ garr8 segs (mrestrict H m) base (TW.zs K).
Proof.
intros H m base n Hp.
destruct (garr8_of_present segs (mrestrict H m) base n) as (l & Hl & Hg).
{ intros a Ha. destruct (Hp a Ha) as (Hh & b & Hb). exists b. unfold mrestrict. rewrite Hh. exact Hb. }
exists (TW.bs l). split; [unfold TW.bs; rewrite length_map; exact Hl|].
replace (TW.zs (TW.bs l)) with l; [exact Hg|].
pose proof (garr8_bytes_ok segs _ _ _ Hg) as Hok. unfold TW.zs, TW.bs. rewrite map_map.
symmetry. rewrite <- (map_id l) at 2. apply map_ext_in. intros x Hx.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. apply Z.mod_small.
unfold bytes_ok in Hok. rewrite Forall_forall in Hok. exact (Hok x Hx).
Qed.

(* The read-only bytes the callees read stay the image's: acall_kept_g keeps every TRANS_RO_RD byte (an image byte
   below G, outside the owned statics and errno). *)
Lemma wh_rom : forall lyc Sc (W : world segs) memc (W2 : world segs) mem2 slo shi (E : Z -> Prop),
  trans_ro_rd_unowned B -> trans_rom_no_errno B ->
  acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W2 mem2 slo shi E ->
  trans_rom_view_rd W memc -> trans_rom_view_rd W2 mem2.
Proof.
intros lyc Sc W memc W2 mem2 slo shi E HRU HRE (_ & _ & K3 & _) Hrom a Ha.
rewrite <- (Hrom a Ha).
destruct (trans_ro_rd_scoped B HRU HRE a Ha) as [Ho He].
apply (K3 a (trans_ro_img a Ha)); [|exact Ho | exact He].
intro Ga. pose proof (inG_G_HARNESS_hull a Ga) as Gh. pose proof (trans_ro_rd_bounds a Ha) as Rb.
unfold TG.G_HARNESS_LO in Gh. lia.
Qed.

(* The world relation after the refused path's store at s + 18256. *)
Lemma wh_tw_rf : forall (rd rd' : Z -> option Z) Bw v,
  tw_at TMAP_A rd Bw ->
  (forall j, (j < 8)%nat -> rd' (TA_g_s + 18256 + Z.of_nat j) = Some (YO0f.le_byte v 8 j)) ->
  (forall x, tw_in TMAP_A x -> ~ (TA_g_s + 18256 <= x < TA_g_s + 18264) -> rd' x = rd x) ->
  tw_at TMAP_A rd' (TW.upd Bw (TW.OFF_g_s + 18256) (TW.put 8 v)).
Proof.
intros rd rd' Bw v Hat H1 HO.
apply (tw_write TMAP_A rd rd' Bw TW.OFF_g_s TA_g_s TW.SZ_g_s 18256 8 v TMAP_A_ok Hat TMAP_A_g_s);
  [lia | unfold TW.SZ_g_s; lia | exact H1 |].
intros x Hx Hn. apply HO; [exact Hx | lia].
Qed.

(* A state with no region at a branch point. *)
Lemma wh_entry0 : forall (W : world segs) regs mem pc,
  st_ok_pi segs VAL (wh_E regs) (ss_wh0 pc)
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + pc)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem pc. rewrite restrict_mkst_fx. unfold ss_wh0.
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. exact I.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. repeat split; exact I.
Qed.

(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac. *)
Ltac wh_reg HS r v H tac :=
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
Ltac wh_region HS i HR :=
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
Ltac wh_u64 x := pose proof (bv_unsigned_in_range 64 x) as Hrg; unfold bv_modulus in Hrg;
  change (2 ^ Z.of_N 64) with (2 ^ 64) in Hrg; lia.
Ltac wh_in := cbn [In]; repeat (first [left; reflexivity | right]).
(* The awr obligation's regions, computed. *)
Ltac wh_awr_rs :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
(* A register at the machine state of HS, from the equation Q of its value at the run's start (valuation wh_E rg). *)
Ltac wh_kreg HS rg r n Q H :=
  lazymatch type of Q with _ = ?v =>
    wh_reg HS r v H
      ltac:(cbn [sv_denot]; rewrite (wh_ew_reg rg n r eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Q) end.
(* The same, at a state whose valuation agrees with E0 below atom 1024 (Elo), E0's registers by EE. *)
Ltac wh_kreg5 HS Elo EE r n Q H :=
  lazymatch type of Q with _ = ?v =>
    wh_reg HS r v H
      ltac:(cbn [sv_denot]; rewrite (Elo n ltac:(lia)), (EE n r eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Q) end.
(* After a run to a cut from a state with no region: every byte of the view as at its start (KD), presence grown
   (GR). *)
Ltac wh_after_cut HS W KD GR m5 msF :=
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?mf) => rename mf into msF end;
  assert (KD : forall a, aview tfibsegs (w_H W) (ms_mem msF) a = aview tfibsegs (w_H W) m5 a);
  [ let a := fresh "a" in let Ha := fresh "Ha" in
    intros a; rewrite (aview_wrap64 tfibsegs _ (ms_mem msF) a), (aview_wrap64 tfibsegs _ m5 a);
    pose proof (Z.mod_pos_bound a (2 ^ 64) ltac:(lia)) as Ha;
    match goal with HFx : frame_of ?E ?rs (mrestrict (w_H W) m5) (mrestrict (w_H W) (ms_mem msF)) |- _ =>
      exact (can_aview_kept_frame E rs (w_H W) m5 (ms_mem msF) 0 HFx ltac:(lia)
               ltac:(let x := fresh "x" in let Hx := fresh "Hx" in let r := fresh "r" in let Hr := fresh "Hr" in
                     intros x Hx; unfold in_wrange; intros (r & Hr & _); vm_compute in Hr; destruct Hr) _ Ha) end
  | ];
  assert (GR : forall a, apresent (w_H W) m5 a -> apresent (w_H W) (ms_mem msF) a);
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    match goal with HGx : mem_grows (mrestrict (w_H W) m5) (mrestrict (w_H W) (ms_mem msF)) |- _ =>
      exact (apresent_grows _ _ _ a HGx Ha) end
  | ].

(* The sign-extended 4-byte load of a field whose bytes are atom 33. *)
Lemma wh_sext : forall E u, 0 <= u < 2 ^ 32 -> ew E 33 = Z_to_bv 64 u ->
  sv_denot E (SExt true 32 (SOff 33 0)) = Z_to_bv 64 (bv_swrap 32 u).
Proof.
intros E u R H. cbn [sv_denot]. rewrite H.
rewrite unsigned_lit_small by lia. rewrite Z.add_0_r.
rewrite LMem.sext_small, LMem.signed_of_extract by lia.
rewrite unsigned_lit_small by lia. reflexivity.
Qed.

(* The thirteen words the prologue saves, as (offset from the entry stack pointer, register). *)
Definition wh_saved : list (Z * bv 5) :=
  [(-8, 1%bv); (-16, 8%bv); (-24, 9%bv); (-32, 18%bv); (-40, 19%bv); (-48, 20%bv); (-56, 21%bv);
   (-64, 22%bv); (-72, 23%bv); (-80, 24%bv); (-88, 25%bv); (-96, 26%bv); (-104, 27%bv)].

(* Every byte of the caller's stack window is present at any memory of the G journal. *)
Lemma wh_jpres : forall STK sp0 FP ly S W0 mem0 md0 own ly' S' (W' : world segs) mem' md' k,
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k ->
  forall a, sp0 - STK <= a < sp0 -> apresent (w_H W') mem' a.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k HJ.
pose proof HJ as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hp & _). exact Hp.
Qed.

(* One step of the walk keeps the caller's memory when each byte it may change is in the call's stack window, in the
   own frame of class WAKE_CID (its bytes, its shadow, its flag byte) or in G: TransportGCg.v dk_kept_step_g with
   the own frame's separation facts (dkg_nf_sep), the written range Eo left as it is. *)
Lemma wh_kept : forall lyc Sc S2 (W : world segs) memc mdc mem2 md2 memX memY slo shi pos F FL (Eo Zs : Z -> Prop),
  AR_laws segs B -> gx_ok segs B TG.G_HARNESS -> frame_flag_lawP segs B ->
  @AR rc segs B lyc Sc W memc mdc -> @AR rc segs B lyc S2 W mem2 md2 ->
  frames S2 = (WAKE_CID, pos) :: frames Sc -> ablocks B lyc S2 = ablocks B lyc Sc ->
  F = frame_addr lyc WAKE_CID pos -> FL = flag_addr lyc WAKE_CID pos ->
  alloc_ceiling <= slo -> shi <= 2 ^ 64 ->
  (forall a, Zs a -> (slo <= a < shi) \/ dkg_nf WAKE_CID F FL a \/ inG TG.G_HARNESS a) ->
  acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W memX slo shi Eo ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview segs (w_H W) memY a = aview segs (w_H W) memX a) ->
  (forall a, apresent (w_H W) memX a -> apresent (w_H W) memY a) ->
  acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W memY slo shi Eo.
Proof.
  intros lyc Sc S2 W memc mdc mem2 md2 memX memY slo shi pos F FL Eo Zs LAWS HG FFL HARc HAR2 Hfrs Hbl EF EFL
    Hce Hshi HZ KP Hkp Hgr.
  destruct (dkg_nf_sep segs B LAWS transport_segs_low lyc Sc S2 W mem2 md2 WAKE_CID pos F FL HAR2 Hfrs Hbl EF EFL FFL)
    as (N1 & N2 & N3 & N4).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  apply (dk_kept_step_g segs B LAWS transport_segs_low TG.G_HARNESS lyc Sc W memc mdc memX memY slo shi Eo Zs HARc KP
    Hkp Hgr).
  - intros a Ha Hc. destruct (HZ a Ha) as [Hw | [Hn | Hg]]; [exact Hw | pose proof (N4 a Hn); lia |].
    pose proof (inG_low segs B transport_segs_low TG.G_HARNESS a HG Hg). unfold kLowMemEnd in *. lia.
  - intros b m i Hb Hi Ha. exfalso. destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HARc Hb) as (_ & H4096 & Hbc & _).
    destruct (HZ _ Ha) as [Hw | [Hn | Hg]]; [lia | exact (N1 b m i Hb Hi Hn) |].
    destruct (HG _ Hg) as [Hi' _]. exact (blk_img segs B LAWS lyc Sc W memc mdc b m (b + i) HARc Hb ltac:(lia) Hi').
  - intros a Ha Hi HnG _ _. exfalso. pose proof (transport_segs_low a Hi) as Hlow. unfold kLowMemEnd in Hlow.
    destruct (HZ a Ha) as [Hw | [Hn | Hg]]; [lia | exact (N2 a Hn Hi) | exact (HnG Hg)].
  - intros cid pos' a Hin Hr Ha. exfalso.
    destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos' HARc Hin) as (G4096 & Gce & _).
    pose proof (fs_frame_bytes_nonneg cid) as Hfs.
    destruct (HZ a Ha) as [Hw | [Hn | Hg]].
    + destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [lia|].
      pose proof (shadow_range_end (frame_addr lyc cid pos') (fs_frame_bytes cid) Hfs) as Hse.
      assert (Hd : (frame_addr lyc cid pos' + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
      unfold shadow_addr, SHADOW_OFF in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia.
    + exact (N3 cid pos' a Hin Hr Hn).
    + destruct (HG _ Hg) as [Hi _]. pose proof (inG_low segs B transport_segs_low TG.G_HARNESS a HG Hg) as Hl.
      destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr.
      * exact (frm_img segs B LAWS lyc Sc W memc mdc cid pos' a HARc Hin Hr Hi).
      * pose proof (Z.div_pos (frame_addr lyc cid pos') 8 ltac:(lia) ltac:(lia)).
        unfold shadow_addr, SHADOW_OFF, kLowMemEnd in *. lia.
Qed.

(* What every cut carries, moved by a step of the head (before send_control) that changes only the bytes Zs: each
   in the call's stack window, in the own frame or in G, none a saved word or a byte of the frame's last word. *)
Lemma wh_cur_step : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world segs) memc mdc k regs Bw pos F S2
    memX mdX memY mdY e (Zs : Z -> Prop),
  AR_laws segs B -> gx_ok segs B TG.G_HARNESS -> frame_flag_lawP segs B ->
  @AR rc segs B lyc Sc W memc mdc -> ablocks B lyc S2 = ablocks B lyc Sc -> F = frame_addr lyc WAKE_CID pos ->
  alloc_ceiling <= spZ regs - WAKE_STK -> spZ regs <= 2 ^ 47 ->
  wake_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw pos F lyc S2 W memX mdX e ->
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0
    ((WAKE_CID, pos) :: own) lyc S2 W memY mdY (k + e) ->
  (forall a, Zs a -> (spZ regs - WAKE_STK <= a < spZ regs) \/ dkg_nf WAKE_CID F (flag_addr lyc WAKE_CID pos) a \/
     inG TG.G_HARNESS a) ->
  (forall a, Zs a -> ~ (spZ regs - 104 <= a < spZ regs)) ->
  (forall a, Zs a -> ~ (F + 248 <= a < F + 256)) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview segs (w_H W) memY a = aview segs (w_H W) memX a) ->
  (forall a, apresent (w_H W) memX a -> apresent (w_H W) memY a) ->
  wake_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw pos F lyc S2 W memY mdY e.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bw pos F S2 memX mdX memY mdY e Zs
  LAWS HG FFL HARc Hbl EF Hce H47 (HJ & He & Hfr & Hperm & HlyF & HMO & HK & HSV & HFL) HJY HZ HZs HZf KP GR.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJY) as HARY.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct wake_stk_bounds as (_ & _ & _ & WS4 & _). assert (Hes : ESTACK = 4096) by reflexivity.
assert (Hin : In (WAKE_CID, pos) (frames S2)) by (rewrite Hfr; left; reflexivity).
destruct (frames_bounds segs B LAWS _ _ _ _ _ WAKE_CID pos HARY Hin) as (HF0 & HFc & _).
rewrite <- EF in HF0, HFc. change (fs_frame_bytes WAKE_CID) with 256 in HFc.
refine (conj HJY (conj He (conj Hfr (conj Hperm (conj HlyF (conj HMO (conj _ (conj _ _)))))))).
- exact (wh_kept lyc Sc S2 W memc mdc memY mdY memX memY (spZ regs - WAKE_STK) (spZ regs) pos F
    (flag_addr lyc WAKE_CID pos) (wake_wr Bw) Zs LAWS HG FFL HARc HARY Hfr Hbl EF eq_refl Hce ltac:(lia) HZ HK KP GR).
- rewrite Forall_forall in HSV |- *. intros o Ho. rewrite <- (HSV o Ho).
  assert (Hob : 8 <= fst o <= 104).
  { unfold WAKE_SAVED in Ho. cbn [In] in Ho. repeat (destruct Ho as [<- | Ho]; [cbn [fst]; lia|]). destruct Ho. }
  apply rdword_ext. intros i Hi. apply KP; [lia|]. intros Hz. apply (HZs _ Hz). lia.
- rewrite <- HFL. apply rdword_ext. intros i Hi. apply KP.
  + unfold WAKE_FBYTES. lia.
  + intros Hz. apply (HZf _ Hz). unfold WAKE_FBYTES. lia.
Qed.

(* What every cut carries, moved to a later memory whose view is the same at every address. *)
Lemma wh_cur_move : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw pos F ly2 S2
    (W2 : world segs) mem2 md2 mem3 md3 e,
  wake_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw pos F ly2 S2 W2 mem2 md2 e ->
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0
    ((WAKE_CID, pos) :: own) ly2 S2 W2 mem3 md3 (k + e) ->
  (forall a, aview segs (w_H W2) mem3 a = aview segs (w_H W2) mem2 a) ->
  (forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) mem3 a) ->
  wake_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw pos F ly2 S2 W2 mem3 md3 e.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw pos F ly2 S2 W2 mem2 md2 mem3 md3 e
  (HJ & He & Hfr & Hperm & HlyF & HMO & HK & HSV & HFL) HJ3 KD GR.
refine (conj HJ3 (conj He (conj Hfr (conj Hperm (conj HlyF (conj HMO (conj _ (conj _ _)))))))).
- destruct HK as (K1 & K2 & K3 & K4 & K5 & K6).
  split; [|split; [|split; [|split; [|split]]]].
  + intros a Ha Hw. rewrite KD. exact (K1 a Ha Hw).
  + intros b m i Hb Hi Hn. rewrite KD. exact (K2 b m i Hb Hi Hn).
  + intros a Hi HnG Hno Hne. rewrite KD. exact (K3 a Hi HnG Hno Hne).
  + intros cid pos0 a Hin Hr Hn. rewrite KD. exact (K4 cid pos0 a Hin Hr Hn).
  + intros a Ha Hw Hp. apply GR. exact (K5 a Ha Hw Hp).
  + intros a Ha. apply GR. exact (K6 a Ha).
- refine (Forall_impl _ _ HSV). intros o Ho. rewrite (rdword_ext _ _ _ (fun k0 _ => KD _)). exact Ho.
- rewrite (rdword_ext _ _ _ (fun k0 _ => KD _)). exact HFL.
Qed.

Lemma wake_head : @wake_head_stmt fx rc B MT.
Proof.
unfold wake_head_stmt. intros MID E2 REL.
unfold transport_diginet_session_wake_cg_holds_stmt.
intros HPCS HCELLS HSC HGU HGE HROU HRNE LAWS MTL MTF SMP ASF FFL ASM0 SND0 CPY0 SET0 NT0.
unfold transport_diginet_session_wake_cg.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now res TF Bw Bw'
  HJe Hra Hra4 Hgp Htp H10 H11 Hsp16 Hlo Hhi Hnow Htw Hfn Hm HTF HTFG HROM HAP Hinv1 Hinv4 Hcnt Hev.
pose proof (G_HARNESS_gx_ok B HGU) as HGX. pose proof (G_HARNESS_gx_noerrno B HGE) as HGNE.
pose proof (ASM0 fx) as ASM. clear ASM0.
pose proof HJe as (HSTK & _ & (memS & HJi & _) & _).
rewrite !Z.add_0_r in HJi.
pose proof HJi as (HAR & Hlyle & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & Hstk & _).
pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
clear HJi memS.
pose proof asan_consts as (AC1 & AC2 & AC3 & AC4 & AC5).
destruct wake_stk_bounds as (WS1 & WS2 & WS3 & WS4 & WS5 & WS6).
assert (FF : WAKE_FRAME = 128) by reflexivity.
assert (CS : WAKE_S = 6158784) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
assert (Hsp : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
assert (Hpres1 : forall a, spZ regs - WAKE_FRAME <= a < spZ regs -> apresent (w_H W) memc a)
  by (intros a Ha; apply Hpres0; lia).
pose proof (wh_entry1 lyc Sc W regs memc mdc HCELLS HAR Hpres1 Hsp Hsp16) as HS.
assert (HEI : img_env VAL A_LIM (wh_E regs)) by apply wh_env_img.
assert (SHOK : sh_ok segs (SOff 32 0) (@nil shent) (wh_E regs) (mrestrict (w_H W) memc)) by constructor.
assert (Usp : bv_unsigned (ew (wh_E regs) 2) = spZ regs)
  by (rewrite (wh_ew_reg regs 2 2%bv eq_refl); reflexivity).
pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUNTO.
pose proof (paj_branch (fx := fx) (PI := PI_transport)) as BR.
pose proof HJe as HJ.
unfold cfg_at.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (BASE + AF_diginet_session_wake)) memc
    (YK11.seg_rom segs)) mdc) Q) end.
(* run 1, +0x000 .. +0x070 *)
paj_run_tok RUN HS HJ SHOK WH_B0.
{ wh_awr_rs.
  apply awr_ok_x_cons;
  [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite Usp in Ha;
    left; split; [unfold awr_byte; left; lia | lia] |].
  repeat (apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |]).
  apply awr_ok_x_nil. }
rename HF into HF1, HFr into HFr1, HG into HG1.
set (sp1 := 32 * ((spZ regs + -128) / 32)).
destruct (can_sp1_facts (spZ regs + -128) ltac:(lia) ltac:(rewrite <- Zplus_mod_idemp_l, Hsp16; reflexivity))
  as (Hsp1r & Hsp1al & Hsp1al16).
fold sp1 in Hsp1r, Hsp1al, Hsp1al16.
assert (Gsp1 : spZ regs - 144 <= sp1 <= spZ regs - 128) by (clear - Hsp1r; lia).
assert (E2' : ew (wh_E regs) 2 = Z_to_bv 64 (spZ regs))
  by (rewrite (wh_ew_reg regs 2 2%bv eq_refl); unfold spZ; symmetry; apply Z_to_bv_bv_unsigned).
wh_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 21772)) R1 ltac:(apply codeptr_val; exact HEI).
wh_reg HS (2%bv : bv 5) (Z_to_bv 64 sp1) R2
  ltac:(exact (can_denot_and_m32 (wh_E regs) 2 (spZ regs) (-128) E2' ltac:(lia) ltac:(lia) ltac:(lia))).
wh_reg HS (3%bv : bv 5) (w64 (as_gp B)) R3
  ltac:(cbn [sv_denot]; rewrite (wh_ew_reg regs 3 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Hgp).
wh_reg HS (4%bv : bv 5) (w64 (as_tp B)) R4
  ltac:(cbn [sv_denot]; rewrite (wh_ew_reg regs 4 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Htp).
wh_reg HS (8%bv : bv 5) (w64 (spZ regs)) R8 ltac:(cbn [sv_denot]; rewrite Usp, Z.add_0_r; reflexivity).
wh_reg HS (9%bv : bv 5) (Z_to_bv 64 sp1) R9
  ltac:(exact (can_denot_and_m32_add0 (wh_E regs) 2 (spZ regs) (-128) E2' ltac:(lia) ltac:(lia) ltac:(lia))).
wh_reg HS (19%bv : bv 5) (w64 WAKE_S) R19
  ltac:(cbn [sv_denot]; rewrite (wh_ew_reg regs 10 10%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact H10).
wh_reg HS (20%bv : bv 5) (w64 now) R20
  ltac:(cbn [sv_denot]; rewrite (wh_ew_reg regs 11 11%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact H11).
wh_reg HS (26%bv : bv 5) (w64 SHADOW_OFF) R26
  ltac:(cbn [sv_denot]; rewrite (wh_ew_32 regs), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
(* The thirteen words the prologue saved, read back from the stack region the run wrote. *)
wh_region HS 0%nat HRsk.
assert (HSVo : forall (o : Z) (r : bv 5), In (o, r) wh_saved -> -104 <= o <= -8).
{ intros o r Hin. unfold wh_saved in Hin. cbn [In] in Hin.
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <-; lia |]). destruct Hin. }
assert (HSV : forall (o : Z) (r : bv 5), In (o, r) wh_saved ->
  rdword (aview segs (w_H W) (ms_mem ms)) (spZ regs + o) = Some (bv_unsigned (YK11.getr regs r))).
{ intros o r Hin. unfold wh_saved in Hin.
  apply (AF0x.val_mem_rdword (w_H W) (ms_mem ms) (spZ regs + o) (bv_unsigned (YK11.getr regs r))
    ltac:(wh_u64 (YK11.getr regs r))).
  apply (can_field_of_region (wh_E regs) _ 2 (spZ regs) _ (-128) 0 (-128) 0 o 8%N
    (SOff (Z.to_nat (bv_unsigned r)) 0) (bv_unsigned (YK11.getr regs r)) HRsk Usp);
  [ cbn [In] in Hin |- *; repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <-;
      repeat (first [left; reflexivity | right]) |]); destruct Hin
  | cbn [sv_denot]; rewrite (wh_ew_reg regs (Z.to_nat (bv_unsigned r)) r ltac:(rewrite Z2Nat.id;
      [reflexivity | apply bv_unsigned_in_range])), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
  | cbn; wh_u64 (YK11.getr regs r)
  | cbn; lia ]. }
clear HRsk.
(* +0x070: the class-2 stack malloc, at the pc the statement's premise names. *)
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transport_sigma TS___asan_stack_malloc_2)) mm rom) mdx) Q) end.
rewrite <- HPCS.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (@YK11.mkst _ ?rg _ ?mm _) ?mdx) _ =>
  eapply (gx_stack_malloc_at (SK := tfib_sink_head) segs B LAWS transport_segs_low SMP WAKE_CID ASM
    ltac:(unfold WAKE_CID; lia) TG.G_HARNESS W rg mm STK sp0 FP ly S W0 mem0 md0 own lyc Sc mdx k (sp1 - sp0)
    (Z_to_bv 64 (BASE + 21772)) HJ) end.
  - unfold spZ at 1. rewrite R2, unsigned_lit_small by lia. lia.
  - rewrite Zminus_mod, Hsp1al16, Hsp0a. reflexivity.
  - lia.
  - lia.
  - exact R3.
  - exact R4.
  - exact R1.
  - apply (ret_ok_codeptr_v (PI := PI_transport)); [lia | reflexivity].
  - lia. }
cbv beta.
intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & pos & -> & HJ2 & HP2 & Ha0 & Eab2 & Hfrs2 & Hnev2
  & Hset2 & Hz & Hflag & Hfpres & HK1).
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HAR2.
assert (Hin2 : In (WAKE_CID, pos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ WAKE_CID pos HAR2 Hin2) as (HFal & HFapp & HFb & HFsh).
destruct (frames_bounds segs B LAWS _ _ _ _ _ WAKE_CID pos HAR2 Hin2) as (HF0 & HFc & _).
destruct (dkg_frame_al64 segs B _ _ _ _ _ WAKE_CID pos HAR2 Hin2) as (HF64 & _ & _).
change (fs_frame_bytes WAKE_CID / 8) with 32 in HFsh.
change (fs_frame_bytes WAKE_CID) with 256 in HFb, HFc, HFapp, Hz, Hflag, Hfpres, HFsh.
set (F := frame_addr lyc WAKE_CID pos) in *.
(* the thirteen saved words, kept by the class-2 call *)
assert (HSV2 : forall (o : Z) (r : bv 5), In (o, r) wh_saved ->
  rdword (aview segs (w_H W) mem2) (spZ regs + o) = Some (bv_unsigned (YK11.getr regs r))).
{ intros o r Hin. pose proof (HSVo o r Hin) as Ho.
  rewrite <- (HSV o r Hin). unfold rdword.
  rewrite !(proj1 HK1) by lia. reflexivity. }
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
assert (Q19 : YK11.getr regs2 19 = w64 WAKE_S)
  by (transitivity (YK11.getr (ms_regs ms) 19); [exact (HP2 19 ltac:(unfold acallee_saved; lia)) | exact R19]).
assert (Q20 : YK11.getr regs2 20 = w64 now)
  by (transitivity (YK11.getr (ms_regs ms) 20); [exact (HP2 20 ltac:(unfold acallee_saved; lia)) | exact R20]).
assert (Q26 : YK11.getr regs2 26 = w64 SHADOW_OFF)
  by (transitivity (YK11.getr (ms_regs ms) 26); [exact (HP2 26 ltac:(unfold acallee_saved; lia)) | exact R26]).
clear HS.
set (memT := ms_mem ms) in *. set (regsT := ms_regs ms) in *. clearbody memT regsT. clear ms.
(* +0x074 .. +0x0dc: the frame taken, the frame word at s1 + 8, the 24-byte header, s8 = the frame's shadow
   address. *)
assert (Hpslot : forall a, sp1 + 8 <= a < sp1 + 16 -> apresent (w_H W) mem2 a)
  by (intros a Ha; apply (wh_jpres _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2); lia).
pose proof (wh_entry2 W regs2 mem2 F sp1 Q2 Q9 Ha0 Q26 ltac:(lia) Hsp1al ltac:(lia) ltac:(lia) HF64 ltac:(lia)
  Hpslot ltac:(intros a Ha; apply Hfpres; lia)) as HS.
assert (HEI2 : img_env VAL A_LIM (wh_E regs2)) by apply wh_env_img.
clear HEI. rename HEI2 into HEI.
assert (SHOK2 : sh_ok segs (SOff 32 0) (@nil shent) (wh_E regs2) (mrestrict (w_H W) mem2)) by constructor.
clear SHOK. rename SHOK2 into SHOK.
assert (U9' : bv_unsigned (ew (wh_E regs2) 9) = sp1)
  by (rewrite (wh_ew_reg regs2 9 9%bv eq_refl), Q9; apply unsigned_lit_small; lia).
assert (U10' : bv_unsigned (ew (wh_E regs2) 10) = F)
  by (rewrite (wh_ew_reg regs2 10 10%bv eq_refl), Ha0; apply unsigned_lit_small; lia).
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + WH_C1)) mem2
    (YK11.seg_rom segs)) md2) Q) end.
pose proof HJ2 as HJm2. clear HJ. rename HJ2 into HJ.
paj_run_tok RUN HS HJ SHOK WH_B0.
{ wh_awr_rs.
  apply awr_ok_x_cons;
  [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U9' in Ha;
    left; split; [unfold awr_byte; left; lia | lia] |].
  eapply (awr_ok_x_cons_own _ _ _ _ _ _ _ _ _ _ _ _ WAKE_CID pos); [left; reflexivity | | apply awr_ok_x_nil].
  intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U10' in Ha.
  left. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes WAKE_CID) with 256.
  change (frame_addr lyc WAKE_CID pos) with F. lia. }
rename HF into HF2a, HFr into HFr2a, HG into HG2a.
clear HEI1.
(* What the call keeps from memc to mem2 (the memory the stack malloc returned). *)
assert (Hwin : forall a, spZ regs - WAKE_STK <= a < spZ regs -> apresent (w_H W) memc a)
  by (intros a Ha; apply Hpres0; lia).
assert (KT : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 128 <= a < spZ regs) ->
  aview segs (w_H W) memT a = aview segs (w_H W) memc a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ (fun x => spZ regs - 128 <= x < spZ regs) HFr1); [| exact Ha | exact Hn].
  intros b wlo whi x Hin Hx.
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; rewrite ?Usp in Hx; lia |]).
  destruct Hin. }
assert (Kg1 : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W memT (spZ regs - WAKE_STK) (spZ regs) (fun _ => False)).
{ apply (dk_kept_step_g segs B LAWS transport_segs_low TG.G_HARNESS lyc Sc W memc mdc memc memT
    (spZ regs - WAKE_STK) (spZ regs) (fun _ => False) (fun x => spZ regs - 128 <= x < spZ regs) HAR).
  - apply dk_kept_refl_g. exact Hwin.
  - intros a Ha Hn. exact (KT a Ha Hn).
  - intros a Ha. exact (apresent_grows _ _ _ a HG1 Ha).
  - intros a Ha _. lia.
  - intros b m i Hb Hi Hzs. exfalso.
    destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hb) as (_ & H4096 & Hbc & _). lia.
  - intros a Ha Hi _ _ _. pose proof (transport_segs_low a Hi) as Hl. unfold kLowMemEnd in *. lia.
  - intros cid pos0 a Hin Hr Ha. exfalso.
    destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos0 HAR Hin) as (F4096 & Fce & _).
    pose proof (fs_frame_bytes_nonneg cid) as Hfs.
    destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [lia|].
    pose proof (shadow_range_end (frame_addr lyc cid pos0) (fs_frame_bytes cid) Hfs) as Hse.
    assert (Hd : (frame_addr lyc cid pos0 + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
    unfold shadow_addr, SHADOW_OFF in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia. }
rewrite Zplus_minus in HK1.
assert (Kg2 : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W mem2 (spZ regs - WAKE_STK) (spZ regs) (fun _ => False)).
{ apply (dk_kept_trans_g segs B TG.G_HARNESS lyc Sc W memc W memT W mem2 (spZ regs - WAKE_STK) (spZ regs)
    (sp1 - ESTACK) sp1 (fun _ => False) (fun _ => False)); [lia | lia | exact Kg1 | | lia | lia | tauto].
  apply acall_kept_g_of. exact HK1. }
assert (GK2 : gx_kept segs TG.G_HARNESS W memc W mem2).
{ apply (gx_kept_trans segs TG.G_HARNESS W memc W memT W mem2).
  - intros a Ha. pose proof (inG_low segs B transport_segs_low TG.G_HARNESS a HGX Ha) as Hl.
    unfold kLowMemEnd in Hl. apply KT; lia.
  - exact (gx_kept_of_acall_kept segs B TG.G_HARNESS lyc Sc W memT W mem2 _ _ _ HGX HGNE HK1). }
clear KT Kg1 HF1 HFr1 HG1.
(* the registers at +0x0e0 *)
assert (EF10 : ew (wh_E regs2) 10 = Z_to_bv 64 F) by (rewrite (wh_ew_reg regs2 10 10%bv eq_refl); exact Ha0).
assert (EF26 : ew (wh_E regs2) 26 = Z_to_bv 64 SHADOW_OFF) by (rewrite (wh_ew_reg regs2 26 26%bv eq_refl); exact Q26).
assert (HFbv : 0 <= F < 2 ^ 64) by lia.
assert (HFd : 0 <= F / 8 /\ F / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
wh_reg HS (24%bv : bv 5) (Z_to_bv 64 (SHADOW_OFF + F / 8)) T24
  ltac:(exact (can_denot_shadow (wh_E regs2) 10 26 F SHADOW_OFF EF10 EF26 HFbv
               ltac:(unfold SHADOW_OFF; lia) ltac:(unfold SHADOW_OFF; lia))).
wh_kreg HS regs2 (2%bv : bv 5) 2%nat Q2 T2. wh_kreg HS regs2 (3%bv : bv 5) 3%nat Q3 T3.
wh_kreg HS regs2 (4%bv : bv 5) 4%nat Q4 T4. wh_kreg HS regs2 (8%bv : bv 5) 8%nat Q8 T8.
wh_kreg HS regs2 (9%bv : bv 5) 9%nat Q9 T9. wh_kreg HS regs2 (19%bv : bv 5) 19%nat Q19 T19.
wh_kreg HS regs2 (20%bv : bv 5) 20%nat Q20 T20. wh_kreg HS regs2 (26%bv : bv 5) 26%nat Q26 T26.
wh_reg HS (25%bv : bv 5) (w64 F) T25
  ltac:(cbn [sv_denot]; rewrite (wh_ew_reg regs2 10 10%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Ha0).
wh_reg HS (18%bv : bv 5) (w64 F) T18
  ltac:(cbn [sv_denot]; rewrite (wh_ew_reg regs2 10 10%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Ha0).
(* run 2a wrote the frame word slot and the frame's header only *)
assert (K2a : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 + 8 <= a < sp1 + 16 \/ F <= a < F + 24) ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem2 a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ (fun x => sp1 + 8 <= x < sp1 + 16 \/ F <= x < F + 24) HFr2a);
    [| exact Ha | exact Hn].
  intros b wlo whi x Hin Hx.
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; rewrite ?U9', ?U10' in Hx;
    first [left; lia | right; lia] |]).
  destruct Hin. }
pose proof HG2a as G2a. clear HF2a HFr2a HG2a.
(* +0x0e0 .. +0x160: the frame's 32 shadow bytes. *)
pmkst HS.
set (ms3 := ms) in *. clearbody ms3. clear HS.
pose proof (wh_entry3 W (ms_regs ms3) (ms_mem ms3) (SHADOW_OFF + F / 8) T24
  ltac:(unfold SHADOW_OFF; lia) ltac:(unfold SHADOW_OFF; lia)
  ltac:(intros a Ha; apply (apresent_grows _ _ _ a G2a);
        replace a with (shadow_addr F + (a - shadow_addr F)) by (unfold shadow_addr; lia);
        exact (proj1 (HFsh (a - shadow_addr F) ltac:(unfold shadow_addr; lia))))) as HS.
assert (HEI3 : img_env VAL A_LIM (wh_E (ms_regs ms3))) by apply wh_env_img.
clear HEI. rename HEI3 into HEI.
assert (SHOK3 : sh_ok segs (SOff 32 0) (@nil shent) (wh_E (ms_regs ms3)) (mrestrict (w_H W) (ms_mem ms3)))
  by constructor.
clear SHOK. rename SHOK3 into SHOK.
assert (U24 : bv_unsigned (ew (wh_E (ms_regs ms3)) 24) = SHADOW_OFF + F / 8)
  by (rewrite (wh_ew_reg (ms_regs ms3) 24 24%bv eq_refl), T24; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
lazymatch goal with |- SRr _ ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + WH_C2)) mm rom) mdx) Q) end.
paj_run_to_tok RUNTO HS HJ SHOK WH_B0 WH_C3.
{ wh_awr_rs.
  eapply (awr_ok_x_cons_own _ _ _ _ _ _ _ _ _ _ _ _ WAKE_CID pos); [left; reflexivity | | apply awr_ok_x_nil].
  intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U24 in Ha.
  right. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes WAKE_CID / 8) with 32.
  change (frame_addr lyc WAKE_CID pos) with F. unfold shadow_addr. lia. }
match goal with H : img_env _ _ _ |- _ => lazymatch H with HEI => fail | _ => clear H end end.
rename HF into HF2b, HFr into HFr2b, HG into HG2b.
(* run 2b wrote the frame's 32 shadow bytes only *)
assert (K2b : forall a, 0 <= a < 2 ^ 64 -> ~ (SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 32) ->
  aview segs (w_H W) (ms_mem ms0) a = aview segs (w_H W) (ms_mem ms3) a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ (fun x => SHADOW_OFF + F / 8 <= x < SHADOW_OFF + F / 8 + 32) HFr2b);
    [| exact Ha | exact Hn].
  intros b wlo whi x Hin Hx.
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; rewrite ?U24 in Hx; lia |]).
  destruct Hin. }
pose proof HG2b as G2b. clear HF2b HFr2b HG2b.
(* the registers at +0x164 *)
wh_kreg HS (ms_regs ms3) (2%bv : bv 5) 2%nat T2 V2. wh_kreg HS (ms_regs ms3) (3%bv : bv 5) 3%nat T3 V3.
wh_kreg HS (ms_regs ms3) (4%bv : bv 5) 4%nat T4 V4. wh_kreg HS (ms_regs ms3) (8%bv : bv 5) 8%nat T8 V8.
wh_kreg HS (ms_regs ms3) (9%bv : bv 5) 9%nat T9 V9. wh_kreg HS (ms_regs ms3) (18%bv : bv 5) 18%nat T18 V18.
wh_kreg HS (ms_regs ms3) (19%bv : bv 5) 19%nat T19 V19. wh_kreg HS (ms_regs ms3) (20%bv : bv 5) 20%nat T20 V20.
wh_kreg HS (ms_regs ms3) (24%bv : bv 5) 24%nat T24 V24. wh_kreg HS (ms_regs ms3) (25%bv : bv 5) 25%nat T25 V25.
wh_kreg HS (ms_regs ms3) (26%bv : bv 5) 26%nat T26 V26.
(* the bytes of G at +0x164 are the entry's *)
assert (NGF : forall a, F <= a < F + 256 -> ~ inG TG.G_HARNESS a).
{ intros a Ha Hg. destruct (HGX a Hg) as [Hi _].
  exact (frm_img segs B LAWS _ _ _ _ _ WAKE_CID pos a HAR2 Hin2 ltac:(change (fs_frame_bytes WAKE_CID) with 256; lia) Hi). }
assert (NGH : forall a, SHADOW_OFF <= a -> ~ inG TG.G_HARNESS a).
{ intros a Ha Hg. pose proof (inG_low segs B transport_segs_low TG.G_HARNESS a HGX Hg) as Hl.
  unfold kLowMemEnd, SHADOW_OFF in *. lia. }
assert (Htw4 : tw_at TMAP_A (aview segs (w_H W) (ms_mem ms0)) Bw).
{ apply (tw_kept_GA (aview segs (w_H W) memc)); [exact Htw|]. intros b n i Hin Hi.
  assert (Hg : inG TG.G_HARNESS (b + i)).
  { unfold inG. apply Exists_exists. exists (b, n). split; [exact Hin | unfold in_zr; cbn [fst snd]; lia]. }
  pose proof (inG_low segs B transport_segs_low TG.G_HARNESS _ HGX Hg) as Hl. unfold kLowMemEnd in Hl.
  rewrite (K2b (b + i) ltac:(lia) ltac:(unfold SHADOW_OFF; lia)).
  rewrite (K2a (b + i) ltac:(lia) ltac:(intros [Hx | Hx]; [lia | exact (NGF (b + i) ltac:(lia) Hg)])).
  exact (GK2 (b + i) Hg). }
(* +0x164 .. +0x180: a0 = -1, `beqz s3`, the checked load of s + 116, up to `beqz a1`. *)
pmkst HS.
set (ms4 := ms0) in *. clearbody ms4. clear HS SHOK.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR4.
destruct (wh_entry4 lyc S2 W (ms_regs ms4) (ms_mem ms4) _ Bw HSC HAR4 Htw4 V19 V26) as [HS SHOK].
clear HEI.
set (vdk := TW.u_at Bw (TW.OFF_g_s + 116) 4) in *.
assert (HEI : img_env VAL A_LIM (wh_Ev (ms_regs ms4) vdk)) by (unfold wh_Ev; apply Eimg_env).
lazymatch goal with |- SRr _ ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + WH_C3)) mm rom) mdx) Q) end.
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ wh_awr_rs.
  apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |].
  apply awr_ok_x_nil. }
rename HF into HF2c, HFr into HFr2c, HG into HG2c.
lazymatch type of HS with st_ok_pi _ _ ?EF _ _ => set (E5 := EF) in * end.
assert (EE4 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r ->
  ew (wh_Ev (ms_regs ms4) vdk) n = YK11.getr (ms_regs ms4) r)
  by (intros n r Hn; apply wh_ev_reg; exact Hn).
assert (E5lo : forall n, (n < 1024)%nat -> ew E5 n = ew (wh_Ev (ms_regs ms4) vdk) n)
  by (intros n Hn; unfold E5; rewrite !ew_ewset_other by lia; reflexivity).
set (m5 := ms_mem ms) in *.
(* run 2c wrote no byte *)
assert (K2c : forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W) m5 a = aview segs (w_H W) (ms_mem ms4) a).
{ intros a Ha. apply (kept_of_frame _ _ _ _ _ (fun _ => False) HFr2c); [| exact Ha | intros []].
  intros b wlo whi x Hin Hx.
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
  cbn [In] in Hin. destruct Hin as [Hin | []]. injection Hin as <- <- <-. lia. }
(* the registers at +0x184 *)
wh_kreg5 HS E5lo EE4 (2%bv : bv 5) 2%nat V2 X2. wh_kreg5 HS E5lo EE4 (3%bv : bv 5) 3%nat V3 X3.
wh_kreg5 HS E5lo EE4 (4%bv : bv 5) 4%nat V4 X4. wh_kreg5 HS E5lo EE4 (8%bv : bv 5) 8%nat V8 X8.
wh_kreg5 HS E5lo EE4 (9%bv : bv 5) 9%nat V9 X9. wh_kreg5 HS E5lo EE4 (18%bv : bv 5) 18%nat V18 X18.
wh_kreg5 HS E5lo EE4 (19%bv : bv 5) 19%nat V19 X19. wh_kreg5 HS E5lo EE4 (20%bv : bv 5) 20%nat V20 X20.
wh_kreg5 HS E5lo EE4 (24%bv : bv 5) 24%nat V24 X24. wh_kreg5 HS E5lo EE4 (25%bv : bv 5) 25%nat V25 X25.
wh_kreg5 HS E5lo EE4 (26%bv : bv 5) 26%nat V26 X26.
assert (E33 : ew E5 33 = Z_to_bv 64 vdk) by (rewrite E5lo by lia; apply wh_ev_33).
assert (R33 : 0 <= vdk < 2 ^ 32) by exact (TWL.u_at_range Bw _ 4).
wh_reg HS (11%bv : bv 5) (Z_to_bv 64 (TW.S_desk_known Bw)) X11
  ltac:(rewrite wh_dk_num; exact (wh_sext E5 vdk R33 E33)).
wh_reg HS (10%bv : bv 5) (Z_to_bv 64 (-1)) X10
  ltac:(apply bv_eq; cbn [sv_denot]; rewrite !Z_to_bv_unsigned; reflexivity).
(* ---- the facts every cut carries, at the memory of +0x184 ---- *)
assert (KF5 : forall a, 0 <= a < 2 ^ 64 ->
  ~ (sp1 + 8 <= a < sp1 + 16 \/ F <= a < F + 24 \/ SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 32) ->
  aview segs (w_H W) m5 a = aview segs (w_H W) mem2 a).
{ intros a Ha Hn. rewrite (K2c a Ha). rewrite (K2b a Ha ltac:(intros X; apply Hn; tauto)).
  exact (K2a a Ha ltac:(intros [X | X]; apply Hn; tauto)). }
assert (GF5 : forall a, apresent (w_H W) mem2 a -> apresent (w_H W) m5 a).
{ intros a Ha. apply (apresent_grows _ _ _ a HG2c). apply (apresent_grows _ _ _ a G2b).
  exact (apresent_grows _ _ _ a G2a Ha). }
assert (HMO : mo_le MT Sc S2 0).
{ destruct Hset2 as (f2 & Ef2). rewrite Ef2. apply (mo_le_set_fs_r MT MTF). exact (mo_le_refl MT MTL Sc). }
assert (HEV0 : 0 <= WAKE_EV) by (unfold WAKE_EV; vm_compute; intro Hx; discriminate Hx).
assert (CUR2 : wake_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw pos F lyc S2 W mem2 md2 0).
{ refine (conj _ (conj _ (conj Hfrs2 (conj _ (conj eq_refl (conj HMO (conj _ (conj _ _)))))))).
  - rewrite Z.add_0_r. exact HJm2.
  - lia.
  - rewrite Eab2. apply Permutation_refl.
  - apply (acall_kept_g_weaken segs B TG.G_HARNESS lyc Sc W memc W mem2 _ _ (fun _ => False) (wake_wr Bw));
      [tauto | exact Kg2].
  - unfold WAKE_SAVED. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
    match goal with |- rdword _ (spZ regs - ?o) = Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 ?r))) =>
      replace (spZ regs - o) with (spZ regs + - o) by ring;
      apply (HSV2 (- o) (Z_to_bv 5 r)); unfold wh_saved; cbn [In];
      repeat (first [left; apply (f_equal2 pair); [reflexivity | apply bv_eq; reflexivity] | right]) end.
  - unfold WAKE_FBYTES. exact Hflag. }
assert (HSHF : SHADOW_OFF + F / 8 + 32 <= F \/ F + 256 <= SHADOW_OFF + F / 8).
{ pose proof (Z.div_mod F 8 ltac:(lia)) as DF8. pose proof (Z.mod_pos_bound F 8 ltac:(lia)) as MF8.
  clear - HFapp HF0 DF8 MF8. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
  destruct HFapp as (_ & [HL | (HH1 & HH2)]); [right | left]; unfold SHADOW_OFF; lia. }
lazymatch type of HJ with context [@W_journalG.ajournal_gx ?r ?sk ?sg ?b ?g ?xo ?o ?stk ?sp ?fp ?l ?s ?w0 ?m0 ?d0
    ?ow ?l' ?s' ?w' ?m' ?md' ?kk] => set (md5 := md') in * end.
assert (CUR5 : wake_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw pos F lyc S2 W m5 md5 0).
{ apply (wh_cur_step STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bw pos F S2 mem2 md2 m5 md5 0
    (fun a => sp1 + 8 <= a < sp1 + 16 \/ F <= a < F + 24 \/ SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 32)
    LAWS HGX FFL HAR Eab2 eq_refl ltac:(lia) ltac:(lia) CUR2 ltac:(rewrite Z.add_0_r; exact HJ)).
  - intros a [X | [X | X]].
    + left. lia.
    + right; left. unfold dkg_nf. left. change (fs_frame_bytes WAKE_CID) with 256. lia.
    + right; left. unfold dkg_nf. right; left. change (fs_frame_bytes WAKE_CID / 8) with 32. lia.
  - intros a [X | [X | X]] Hs; unfold SHADOW_OFF in *; lia.
  - intros a [X | [X | X]] Hf; [lia | lia | destruct HSHF; lia].
  - exact KF5.
  - exact GF5. }
assert (Htw5 : tw_at TMAP_A (aview segs (w_H W) m5) Bw).
{ apply (tw_kept TMAP_A (aview segs (w_H W) (ms_mem ms4))); [exact Htw4|]. intros x Hx.
  pose proof (TMAP_A_hull x Hx) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh. apply K2c. lia. }
(* the record facts and the caller's facts, as the cuts state them *)
assert (HLAWS : wake_laws B MT)
  by exact (conj HPCS (conj HCELLS (conj HSC (conj HGU (conj HGE (conj HROU (conj HRNE (conj LAWS (conj MTL
    (conj MTF (conj SMP (conj ASF (conj FFL (conj HGX HGNE)))))))))))))).
assert (HFIX : wake_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now res TF Bw Bw' pos sp1 F).
{ unfold wake_fix.
  refine (conj HJe (conj Hra (conj Hra4 (conj Hgp (conj Htp (conj H10 (conj H11 (conj Hsp16 (conj Hlo (conj Hhi
    (conj Hnow (conj Htw (conj Hfn (conj Hm (conj HTF (conj HTFG (conj HROM (conj HAP (conj Hinv1 (conj Hinv4
    (conj Hcnt (conj Hev (conj _ (conj eq_refl (conj HF0 (conj HF64 (conj HFc HFapp))))))))))))))))))))))))))).
  unfold sp1, WAKE_FRAME. replace (spZ regs - 128) with (spZ regs + -128) by lia. reflexivity. }
(* +0x184: `beqz a1` on S_desk_known, from a state with no region *)
pmkst HS.
clear HS SHOK HEI.
pose proof (wh_entry0 W (ms_regs ms) m5 WH_C4) as HS.
assert (SHOK : sh_ok segs (SOff 32 0) (@nil shent) (wh_E (ms_regs ms)) (mrestrict (w_H W) m5)) by constructor.
assert (HEI : img_env VAL A_LIM (wh_E (ms_regs ms))) by apply wh_env_img.
lazymatch goal with |- SRr _ ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + WH_C4)) mm rom) mdx) Q) end.
assert (D11 : sv_denot (wh_E (ms_regs ms)) (SOff 11 0) = Z_to_bv 64 (TW.S_desk_known Bw))
  by (cbn [sv_denot]; rewrite (wh_ew_reg (ms_regs ms) 11 11%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact X11).
assert (Rdk : - 2 ^ 63 <= TW.S_desk_known Bw < 2 ^ 63).
{ pose proof (wk_s32_range Bw TW.A_S_desk_known) as R.
  change (TW.s32_at Bw TW.A_S_desk_known) with (TW.S_desk_known Bw) in R. lia. }
psrr_branch_tok RUN BR HS SHOK WH_B0.
- (* S_desk_known Bw = 0: to the release cut with a0 = -1 *)
  cbn [branch_taken] in Hc. rewrite D11 in Hc.
  change (sv_denot (wh_E (ms_regs ms)) (SLit 0)) with (Z_to_bv 64 0) in Hc.
  rewrite (wk_eqb _ 0 Rdk ltac:(lia)) in Hc. apply Z.eqb_eq in Hc.
  rewrite wake_model in Hm. rewrite (proj2 (Z.eqb_eq _ _) Hc) in Hm.
  destruct (wake_some_inv _ _ _ _ Hm) as [EB ER].
  paj_run_to_tok RUNTO HS HJ SHOK WH_B0 WAKE_REL.
  { wh_awr_rs. apply awr_ok_x_nil. }
  wh_after_cut HS W KD GR m5 msF.
  wh_kreg HS (ms_regs ms) (2%bv : bv 5) 2%nat X2 Y2. wh_kreg HS (ms_regs ms) (3%bv : bv 5) 3%nat X3 Y3.
  wh_kreg HS (ms_regs ms) (4%bv : bv 5) 4%nat X4 Y4. wh_kreg HS (ms_regs ms) (8%bv : bv 5) 8%nat X8 Y8.
  wh_kreg HS (ms_regs ms) (9%bv : bv 5) 9%nat X9 Y9. wh_kreg HS (ms_regs ms) (18%bv : bv 5) 18%nat X18 Y18.
  wh_kreg HS (ms_regs ms) (24%bv : bv 5) 24%nat X24 Y24. wh_kreg HS (ms_regs ms) (25%bv : bv 5) 25%nat X25 Y25.
  wh_kreg HS (ms_regs ms) (10%bv : bv 5) 10%nat X10 Y10.
  pmkst HS.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + WAKE_REL)) mm rom) mdx) Q) end.
  apply (REL HLAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now res TF Bw Bw' pos sp1 F lyc S2 W
    (ms_mem msF) _ 0 (ms_regs msF) HFIX).
  + refine (conj (wh_cur_move STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw pos F lyc S2 W m5 md5
      (ms_mem msF) _ 0 CUR5 ltac:(rewrite Z.add_0_r; exact HJ) KD GR) (conj _ _)).
    * rewrite <- EB. apply (tw_kept TMAP_A (aview segs (w_H W) m5)); [exact Htw5 | intros x _; exact (KD x)].
    * rewrite <- EB. exact Hfn.
  + unfold wake_regs_rel, wake_regs_core.
    refine (conj (conj Y2 (conj _ (conj _ (conj Y8 (conj Y9 (conj Y18 (conj Y24 Y25))))))) _).
    * rewrite Y3. symmetry. exact Hgp.
    * rewrite Y4. symmetry. exact Htp.
    * rewrite Y10, <- ER. apply bv_eq. vm_compute. reflexivity.
- (* S_desk_known Bw <> 0: on to +0x188 *)
  cbn [branch_taken] in Hc. rewrite D11 in Hc.
  change (sv_denot (wh_E (ms_regs ms)) (SLit 0)) with (Z_to_bv 64 0) in Hc.
  rewrite (wk_eqb _ 0 Rdk ltac:(lia)) in Hc. apply Z.eqb_neq in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK WH_B0 WH_C5.
  { wh_awr_rs. apply awr_ok_x_nil. }
  wh_after_cut HS W KD GR m5 msF.
  rename Hc into Hdk. clear HF HFr HG.
  wh_kreg HS (ms_regs ms) (2%bv : bv 5) 2%nat X2 Z2. wh_kreg HS (ms_regs ms) (3%bv : bv 5) 3%nat X3 Z3.
  wh_kreg HS (ms_regs ms) (4%bv : bv 5) 4%nat X4 Z4. wh_kreg HS (ms_regs ms) (8%bv : bv 5) 8%nat X8 Z8.
  wh_kreg HS (ms_regs ms) (9%bv : bv 5) 9%nat X9 Z9. wh_kreg HS (ms_regs ms) (18%bv : bv 5) 18%nat X18 Z18.
  wh_kreg HS (ms_regs ms) (19%bv : bv 5) 19%nat X19 Z19. wh_kreg HS (ms_regs ms) (20%bv : bv 5) 20%nat X20 Z20.
  wh_kreg HS (ms_regs ms) (24%bv : bv 5) 24%nat X24 Z24. wh_kreg HS (ms_regs ms) (25%bv : bv 5) 25%nat X25 Z25.
  wh_kreg HS (ms_regs ms) (26%bv : bv 5) 26%nat X26 Z26.
  set (m6 := ms_mem msF) in *.
  assert (Htw6 : tw_at TMAP_A (aview segs (w_H W) m6) Bw)
    by (apply (tw_kept TMAP_A (aview segs (w_H W) m5)); [exact Htw5 | intros x _; exact (KD x)]).
  lazymatch type of HJ with context [@W_journalG.ajournal_gx ?r ?sk ?sg ?b ?g ?xo ?o ?stk ?sp ?fp ?l ?s ?w0 ?m0 ?d0
      ?ow ?l' ?s' ?w' ?m' ?md' ?kk] => set (md6 := md') in * end.
  assert (CUR6 : wake_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw pos F lyc S2 W m6 md6 0)
    by exact (wh_cur_move STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw pos F lyc S2 W m5 md5 m6 md6 0
      CUR5 ltac:(rewrite Z.add_0_r; exact HJ) KD GR).
  (* run 3, +0x188 .. +0x1a8: the checked load of s + 136, s5 = s + 18224, up to `beqz a0` *)
  pmkst HS.
  set (ms6 := msF) in *. clearbody ms6. clear HS SHOK HEI KD GR.
  pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR6.
  destruct (wh_entry6 lyc S2 W (ms_regs ms6) m6 _ Bw HSC HAR6 Htw6 Z19 Z26) as [HS SHOK].
  set (vfo := TW.u_at Bw (TW.OFF_g_s + 136) 4) in *.
  assert (HEI : img_env VAL A_LIM (wh_Ev (ms_regs ms6) vfo)) by (unfold wh_Ev; apply Eimg_env).
  lazymatch goal with |- SRr _ ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr segs Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + WH_C5)) mm rom) mdx) Q) end.
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { wh_awr_rs.
    apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |].
    apply awr_ok_x_nil. }
  rename HF into HF3, HFr into HFr3, HG into HG3.
  lazymatch type of HS with st_ok_pi _ _ ?EF _ (restrict _ ?mf) => set (E7 := EF) in *; rename mf into ms7 end.
  assert (EE6 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r ->
    ew (wh_Ev (ms_regs ms6) vfo) n = YK11.getr (ms_regs ms6) r)
    by (intros n r Hn; apply wh_ev_reg; exact Hn).
  assert (E7lo : forall n, (n < 1024)%nat -> ew E7 n = ew (wh_Ev (ms_regs ms6) vfo) n)
    by (intros n Hn; unfold E7; rewrite ?ew_ewset_other by lia; reflexivity).
  set (m7 := ms_mem ms7) in *.
  (* run 3 wrote no byte *)
  assert (K3 : forall a, aview segs (w_H W) m7 a = aview segs (w_H W) m6 a).
  { intros a. rewrite (aview_wrap64 segs _ m7 a), (aview_wrap64 segs _ m6 a).
    pose proof (Z.mod_pos_bound a (2 ^ 64) ltac:(lia)) as Ha.
    apply (kept_of_frame _ _ _ _ _ (fun _ => False) HFr3); [| exact Ha | intros []].
    intros b wlo whi x Hin Hx.
    lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
    cbn [In] in Hin. destruct Hin as [Hin | []]. injection Hin as <- <- <-. lia. }
  assert (G3 : forall a, apresent (w_H W) m6 a -> apresent (w_H W) m7 a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG3 Ha)).
  clear HF3 HFr3 HG3.
  wh_kreg5 HS E7lo EE6 (2%bv : bv 5) 2%nat Z2 W2r. wh_kreg5 HS E7lo EE6 (3%bv : bv 5) 3%nat Z3 W3r.
  wh_kreg5 HS E7lo EE6 (4%bv : bv 5) 4%nat Z4 W4r. wh_kreg5 HS E7lo EE6 (8%bv : bv 5) 8%nat Z8 W8r.
  wh_kreg5 HS E7lo EE6 (9%bv : bv 5) 9%nat Z9 W9r. wh_kreg5 HS E7lo EE6 (18%bv : bv 5) 18%nat Z18 W18r.
  wh_kreg5 HS E7lo EE6 (19%bv : bv 5) 19%nat Z19 W19r. wh_kreg5 HS E7lo EE6 (20%bv : bv 5) 20%nat Z20 W20r.
  wh_kreg5 HS E7lo EE6 (24%bv : bv 5) 24%nat Z24 W24r. wh_kreg5 HS E7lo EE6 (25%bv : bv 5) 25%nat Z25 W25r.
  wh_kreg5 HS E7lo EE6 (26%bv : bv 5) 26%nat Z26 W26r.
  assert (E33f : ew E7 33 = Z_to_bv 64 vfo) by (rewrite E7lo by lia; apply wh_ev_33).
  assert (R33f : 0 <= vfo < 2 ^ 32) by exact (TWL.u_at_range Bw _ 4).
  wh_reg HS (10%bv : bv 5) (Z_to_bv 64 (TW.S_foreign Bw)) W10r
    ltac:(rewrite wh_fo_num; exact (wh_sext E7 vfo R33f E33f)).
  wh_reg HS (21%bv : bv 5) (w64 (WAKE_S + 18224)) W21r
    ltac:(cbn [sv_denot]; rewrite (E7lo 19%nat ltac:(lia)), (EE6 19%nat 19%bv eq_refl), Z19; unfold w64;
          rewrite (unsigned_lit_small WAKE_S) by (rewrite CS; lia); reflexivity).
  assert (Htw7 : tw_at TMAP_A (aview segs (w_H W) m7) Bw)
    by (apply (tw_kept TMAP_A (aview segs (w_H W) m6)); [exact Htw6 | intros x _; exact (K3 x)]).
  lazymatch type of HJ with context [@W_journalG.ajournal_gx ?r ?sk ?sg ?b ?g ?xo ?o ?stk ?sp ?fp ?l ?s ?w0 ?m0 ?d0
      ?ow ?l' ?s' ?w' ?m' ?md' ?kk] => set (md7 := md') in * end.
  assert (CUR7 : wake_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw pos F lyc S2 W m7 md7 0)
    by exact (wh_cur_move STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw pos F lyc S2 W m6 md6 m7 md7 0
      CUR6 ltac:(rewrite Z.add_0_r; exact HJ) K3 G3).
  (* +0x1ac: `beqz a0` on S_foreign, from a state with no region *)
  pmkst HS.
  clear HS SHOK HEI.
  pose proof (wh_entry0 W (ms_regs ms7) m7 WH_C6) as HS.
  assert (SHOK : sh_ok segs (SOff 32 0) (@nil shent) (wh_E (ms_regs ms7)) (mrestrict (w_H W) m7)) by constructor.
  assert (HEI : img_env VAL A_LIM (wh_E (ms_regs ms7))) by apply wh_env_img.
  lazymatch goal with |- SRr _ ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr segs Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + WH_C6)) mm rom) mdx) Q) end.
  assert (D10 : sv_denot (wh_E (ms_regs ms7)) (SOff 10 0) = Z_to_bv 64 (TW.S_foreign Bw))
    by (cbn [sv_denot]; rewrite (wh_ew_reg (ms_regs ms7) 10 10%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        exact W10r).
  assert (Rfo : - 2 ^ 63 <= TW.S_foreign Bw < 2 ^ 63).
  { pose proof (wk_s32_range Bw TW.A_S_foreign) as R.
    change (TW.s32_at Bw TW.A_S_foreign) with (TW.S_foreign Bw) in R. lia. }
  psrr_branch_tok RUN BR HS SHOK WH_B0.
  2: {
  (* S_foreign Bw <> 0: the refused path, +0x1b0 .. +0x1d4, then the release cut with a0 = -10 *)
  cbn [branch_taken] in Hc. rewrite D10 in Hc.
  change (sv_denot (wh_E (ms_regs ms7)) (SLit 0)) with (Z_to_bv 64 0) in Hc.
  rewrite (wk_eqb _ 0 Rfo ltac:(lia)) in Hc. apply Z.eqb_neq in Hc. rename Hc into Hfo.
  rewrite wake_model in Hm. rewrite (proj2 (Z.eqb_neq _ _) Hdk), (proj2 (Z.eqb_neq _ _) Hfo) in Hm.
  destruct (wake_some_inv _ _ _ _ Hm) as [EB ER].
  paj_run_to_tok RUNTO HS HJ SHOK WH_B0 WH_C7.
  { wh_awr_rs. apply awr_ok_x_nil. }
  wh_after_cut HS W KD GR m7 ms8. clear HF HFr HG.
  wh_kreg HS (ms_regs ms7) (2%bv : bv 5) 2%nat W2r P2. wh_kreg HS (ms_regs ms7) (3%bv : bv 5) 3%nat W3r P3.
  wh_kreg HS (ms_regs ms7) (4%bv : bv 5) 4%nat W4r P4. wh_kreg HS (ms_regs ms7) (8%bv : bv 5) 8%nat W8r P8.
  wh_kreg HS (ms_regs ms7) (9%bv : bv 5) 9%nat W9r P9. wh_kreg HS (ms_regs ms7) (18%bv : bv 5) 18%nat W18r P18.
  wh_kreg HS (ms_regs ms7) (21%bv : bv 5) 21%nat W21r P21. wh_kreg HS (ms_regs ms7) (24%bv : bv 5) 24%nat W24r P24.
  wh_kreg HS (ms_regs ms7) (25%bv : bv 5) 25%nat W25r P25. wh_kreg HS (ms_regs ms7) (26%bv : bv 5) 26%nat W26r P26.
  set (m8 := ms_mem ms8) in *.
  assert (Htw8 : tw_at TMAP_A (aview segs (w_H W) m8) Bw)
    by (apply (tw_kept TMAP_A (aview segs (w_H W) m7)); [exact Htw7 | intros x _; exact (KD x)]).
  lazymatch type of HJ with context [@W_journalG.ajournal_gx ?r ?sk ?sg ?b ?g ?xo ?o ?stk ?sp ?fp ?l ?s ?w0 ?m0 ?d0
      ?ow ?l' ?s' ?w' ?m' ?md' ?kk] => set (md8 := md') in * end.
  assert (CUR8 : wake_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw pos F lyc S2 W m8 md8 0)
    by exact (wh_cur_move STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw pos F lyc S2 W m7 md7 m8 md8 0
      CUR7 ltac:(rewrite Z.add_0_r; exact HJ) KD GR).
  pmkst HS.
  clear HS SHOK HEI KD GR.
  pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR8.
  destruct (wh_entry7 lyc S2 W (ms_regs ms8) m8 _ Bw HSC HAR8 Htw8 P21 P26) as [HS SHOK].
  set (vrf := TW.u_at Bw (TW.OFF_g_s + 18256) 8) in *.
  assert (HEI : img_env VAL A_LIM (wh_Ev (ms_regs ms8) vrf)) by (unfold wh_Ev; apply Eimg_env).
  assert (EE8 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r ->
    ew (wh_Ev (ms_regs ms8) vrf) n = YK11.getr (ms_regs ms8) r)
    by (intros n r Hn; apply wh_ev_reg; exact Hn).
  assert (U21R : bv_unsigned (ew (wh_Ev (ms_regs ms8) vrf) 21) = WAKE_S + 18224)
    by (rewrite (EE8 21%nat 21%bv eq_refl), P21; apply unsigned_lit_small; rewrite CS; lia).
  lazymatch goal with |- SRr _ ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr segs Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + WH_C7)) mm rom) mdx) Q) end.
  paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan WAKE_REL.
  { wh_awr_rs.
    apply awr_ok_x_cons_g;
    [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U21R in Ha;
      apply wh_inG; unfold TW.SZ_g_s; lia |].
    apply awr_ok_x_nil. }
  lazymatch type of HS with st_ok_pi _ _ ?EF _ (restrict _ ?mf) => set (E9 := EF) in HS; rename mf into ms9 end.
  rename HF into HFR, HFr into HFrR, HG into HGR.
  assert (E9lo : forall n, (n < 1024)%nat -> ew E9 n = ew (wh_Ev (ms_regs ms8) vrf) n)
    by (intros n Hn; unfold E9; rewrite ?ew_ewset_other by lia; reflexivity).
  assert (U21S : bv_unsigned (ew E9 21) = WAKE_S + 18224) by (rewrite E9lo by lia; exact U21R).
  (* the refused path wrote g_s.stats.refused only *)
  assert (KR : forall a, 0 <= a < 2 ^ 64 -> ~ (WAKE_S + 18256 <= a < WAKE_S + 18264) ->
    aview segs (w_H W) (ms_mem ms9) a = aview segs (w_H W) m8 a).
  { intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ (fun x => WAKE_S + 18256 <= x < WAKE_S + 18264) HFrR);
      [| exact Ha | exact Hn].
    intros b wlo whi x Hin Hx.
    lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
    cbn [In] in Hin. destruct Hin as [Hin | []]. injection Hin as <- <- <-.
    cbn [base_val] in Hx. rewrite U21R in Hx. lia. }
  wh_region HS 0%nat HRR.
  assert (E33r : ew E9 33 = Z_to_bv 64 vrf) by (rewrite E9lo by lia; apply wh_ev_33).
  assert (R33r : 0 <= vrf < 2 ^ 64) by exact (TWL.u_at_range Bw _ 8).
  assert (HVR : forall j, (j < 8)%nat ->
    aview segs (w_H W) (ms_mem ms9) (TA_g_s + 18256 + Z.of_nat j) = Some (YO0f.le_byte (vrf + 1) 8 j)).
  { intros j Hj.
    replace (TA_g_s + 18256 + Z.of_nat j) with (base_val E9 (Some 21%nat) + 32 + Z.of_nat j)
      by (cbn [base_val]; rewrite U21S; unfold WAKE_S; lia).
    exact (wh_chunk_bytes E9 (w_H W) (ms_mem ms9) (Some 21%nat) 32 40 32 40 _ 32 8 (SOff 33 1) (vrf + 1) HRR
      ltac:(wh_in) ltac:(lia)
      ltac:(cbn [sv_denot]; rewrite E33r; rewrite unsigned_lit_small by lia; reflexivity) j Hj). }
  assert (TWR : tw_at TMAP_A (aview segs (w_H W) (ms_mem ms9))
    (TW.upd Bw (TW.OFF_g_s + 18256) (TW.put 8 (vrf + 1)))).
  { apply (wh_tw_rf (aview segs (w_H W) m8) _ Bw (vrf + 1) Htw8 HVR).
    intros x Hx Hn. pose proof (TMAP_A_hull x Hx) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
    apply KR; [lia | unfold WAKE_S; lia]. }
  assert (EBw' : Bw' = TW.upd Bw (TW.OFF_g_s + 18256) (TW.put 8 (vrf + 1))).
  { rewrite <- EB, wk_refused_eq. change TW.A_S_stats_refused with (TW.OFF_g_s + 18256). reflexivity. }
  wh_kreg5 HS E9lo EE8 (2%bv : bv 5) 2%nat P2 Q2r. wh_kreg5 HS E9lo EE8 (3%bv : bv 5) 3%nat P3 Q3r.
  wh_kreg5 HS E9lo EE8 (4%bv : bv 5) 4%nat P4 Q4r. wh_kreg5 HS E9lo EE8 (8%bv : bv 5) 8%nat P8 Q8r.
  wh_kreg5 HS E9lo EE8 (9%bv : bv 5) 9%nat P9 Q9r. wh_kreg5 HS E9lo EE8 (18%bv : bv 5) 18%nat P18 Q18r.
  wh_kreg5 HS E9lo EE8 (24%bv : bv 5) 24%nat P24 Q24r. wh_kreg5 HS E9lo EE8 (25%bv : bv 5) 25%nat P25 Q25r.
  wh_reg HS (10%bv : bv 5) (Z_to_bv 64 (-10)) Q10r
    ltac:(apply bv_eq; cbn [sv_denot]; rewrite !Z_to_bv_unsigned; reflexivity).
  lazymatch type of HJ with context [@W_journalG.ajournal_gx ?r ?sk ?sg ?b ?g ?xo ?o ?stk ?sp ?fp ?l ?s ?w0 ?m0 ?d0
      ?ow ?l' ?s' ?w' ?m' ?md' ?kk] => set (md9 := md') in * end.
  assert (CUR9 : wake_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw pos F lyc S2 W
    (ms_mem ms9) md9 0).
  { apply (wh_cur_step STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bw pos F S2 m8 md8 (ms_mem ms9) md9 0
      (fun a => WAKE_S + 18256 <= a < WAKE_S + 18264)
      LAWS HGX FFL HAR Eab2 eq_refl ltac:(lia) ltac:(lia) CUR8 ltac:(rewrite Z.add_0_r; exact HJ)).
    - intros a Ha. right; right. apply wh_inG. unfold TW.SZ_g_s. lia.
    - intros a Ha Hs. rewrite CS in Ha. lia.
    - intros a Ha Hf. exact (NGF a ltac:(lia) (wh_inG a ltac:(unfold TW.SZ_g_s; lia))).
    - exact KR.
    - intros a Ha. exact (apresent_grows _ _ _ a HGR Ha). }
  pmkst HS.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + WAKE_REL)) mm rom) mdx) Q) end.
  apply (REL HLAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now res TF Bw Bw' pos sp1 F lyc S2 W
    (ms_mem ms9) md9 0 (ms_regs ms9) HFIX).
  - refine (conj CUR9 (conj _ _)).
    + rewrite EBw'. exact TWR.
    + rewrite EBw', wh_refused_gfn by exact (tw_len _ _ _ Htw). exact Hfn.
  - unfold wake_regs_rel, wake_regs_core.
    refine (conj (conj Q2r (conj _ (conj _ (conj Q8r (conj Q9r (conj Q18r (conj Q24r Q25r))))))) _).
    + rewrite Q3r. symmetry. exact Hgp.
    + rewrite Q4r. symmetry. exact Htp.
    + rewrite Q10r, <- ER. apply bv_eq. vm_compute. reflexivity. }
  (* S_foreign Bw = 0: on to +0x1d8 *)
  cbn [branch_taken] in Hc. rewrite D10 in Hc.
  change (sv_denot (wh_E (ms_regs ms7)) (SLit 0)) with (Z_to_bv 64 0) in Hc.
  rewrite (wk_eqb _ 0 Rfo ltac:(lia)) in Hc. apply Z.eqb_eq in Hc. rename Hc into Hfo.
  paj_run_to_tok RUNTO HS HJ SHOK WH_B0 WH_C8.
  { wh_awr_rs. apply awr_ok_x_nil. }
  wh_after_cut HS W KD GR m7 ms8. clear HF HFr HG.
  wh_kreg HS (ms_regs ms7) (2%bv : bv 5) 2%nat W2r P2. wh_kreg HS (ms_regs ms7) (3%bv : bv 5) 3%nat W3r P3.
  wh_kreg HS (ms_regs ms7) (4%bv : bv 5) 4%nat W4r P4. wh_kreg HS (ms_regs ms7) (8%bv : bv 5) 8%nat W8r P8.
  wh_kreg HS (ms_regs ms7) (9%bv : bv 5) 9%nat W9r P9. wh_kreg HS (ms_regs ms7) (18%bv : bv 5) 18%nat W18r P18.
  wh_kreg HS (ms_regs ms7) (19%bv : bv 5) 19%nat W19r P19. wh_kreg HS (ms_regs ms7) (20%bv : bv 5) 20%nat W20r P20.
  wh_kreg HS (ms_regs ms7) (21%bv : bv 5) 21%nat W21r P21. wh_kreg HS (ms_regs ms7) (24%bv : bv 5) 24%nat W24r P24.
  wh_kreg HS (ms_regs ms7) (25%bv : bv 5) 25%nat W25r P25. wh_kreg HS (ms_regs ms7) (26%bv : bv 5) 26%nat W26r P26.
  set (m8 := ms_mem ms8) in *.
  assert (Htw8 : tw_at TMAP_A (aview segs (w_H W) m8) Bw)
    by (apply (tw_kept TMAP_A (aview segs (w_H W) m7)); [exact Htw7 | intros x _; exact (KD x)]).
  lazymatch type of HJ with context [@W_journalG.ajournal_gx ?r ?sk ?sg ?b ?g ?xo ?o ?stk ?sp ?fp ?l ?s ?w0 ?m0 ?d0
      ?ow ?l' ?s' ?w' ?m' ?md' ?kk] => set (md8 := md') in * end.
  assert (CUR8 : wake_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw pos F lyc S2 W m8 md8 0)
    by exact (wh_cur_move STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw pos F lyc S2 W m7 md7 m8 md8 0
      CUR7 ltac:(rewrite Z.add_0_r; exact HJ) KD GR).
  (* run 4a, +0x1d8 .. +0x220: the three checked stores, s6 = e2 *)
  pmkst HS.
  clear HS SHOK HEI KD GR.
  pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR8.
  destruct (wh_entry8 lyc S2 W (ms_regs ms8) m8 _ HSC HAR8 P19 P26) as [HS SHOK].
  assert (HEI : img_env VAL A_LIM (wh_E (ms_regs ms8))) by apply wh_env_img.
  assert (EE8 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (wh_E (ms_regs ms8)) n = YK11.getr (ms_regs ms8) r)
    by (intros n r Hn; apply wh_ew_reg; exact Hn).
  assert (U19d : bv_unsigned (ew (wh_E (ms_regs ms8)) 19) = WAKE_S)
    by (rewrite (EE8 19%nat 19%bv eq_refl), P19; apply unsigned_lit_small; rewrite CS; lia).
  lazymatch goal with |- SRr _ ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr segs Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + WH_C8)) mm rom) mdx) Q) end.
  paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan WH_C8b.
  { wh_awr_rs.
    apply awr_ok_x_cons_g;
    [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U19d in Ha;
      apply wh_inG; unfold TW.SZ_g_s; lia |].
    apply awr_ok_x_cons_g;
    [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U19d in Ha;
      apply wh_inG; unfold TW.SZ_g_s; lia |].
    apply awr_ok_x_nil. }
  rename HF into HF4, HFr into HFr4, HG into HG4.
  lazymatch type of HS with st_ok_pi _ _ ?EF _ (restrict _ ?mf) => set (EA := EF) in HS; rename mf into msA end.
  assert (EAl : forall n, (n < 1024)%nat -> ew EA n = ew (wh_E (ms_regs ms8)) n)
    by (intros n Hn; unfold EA; rewrite ?ew_ewset_other by lia; reflexivity).
  assert (U19A : bv_unsigned (ew EA 19) = WAKE_S) by (rewrite EAl by lia; exact U19d).
  set (mA := ms_mem msA) in *.
  (* run 4a wrote g_s's three fields only *)
  assert (KR4a : forall a, 0 <= a < 2 ^ 64 -> ~ (WAKE_S + 140 <= a < WAKE_S + 148 \/ WAKE_S + 152 <= a < WAKE_S + 160) ->
    aview segs (w_H W) mA a = aview segs (w_H W) m8 a).
  { intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ (fun x => WAKE_S + 140 <= x < WAKE_S + 148 \/
      WAKE_S + 152 <= x < WAKE_S + 160) HFr4); [| exact Ha | exact Hn].
    intros b wlo whi x Hin Hx.
    lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
    cbn [In] in Hin.
    repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; rewrite ?U19d in Hx;
      first [left; lia | right; lia] |]).
    destruct Hin. }
  assert (GR4a : forall a, apresent (w_H W) m8 a -> apresent (w_H W) mA a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG4 Ha)).
  clear HF4 HFr4 HG4.
  wh_region HS 0%nat HRa. wh_region HS 1%nat HRb.
  assert (V140A : forall j, (j < 4)%nat ->
    aview segs (w_H W) mA (TA_g_s + 140 + Z.of_nat j) = Some (YO0f.le_byte 0 4 j)).
  { intros j Hj. replace (TA_g_s + 140 + Z.of_nat j) with (base_val EA (Some 19%nat) + 140 + Z.of_nat j)
      by (cbn [base_val]; rewrite U19A; unfold WAKE_S; lia).
    exact (wh_chunk_bytes EA (w_H W) mA (Some 19%nat) 140 148 140 148 _ 140 4 (SLit 0) 0 HRa ltac:(wh_in)
      ltac:(lia) eq_refl j Hj). }
  assert (V144A : forall j, (j < 4)%nat ->
    aview segs (w_H W) mA (TA_g_s + 144 + Z.of_nat j) = Some (YO0f.le_byte 0 4 j)).
  { intros j Hj. replace (TA_g_s + 144 + Z.of_nat j) with (base_val EA (Some 19%nat) + 144 + Z.of_nat j)
      by (cbn [base_val]; rewrite U19A; unfold WAKE_S; lia).
    exact (wh_chunk_bytes EA (w_H W) mA (Some 19%nat) 140 148 140 148 _ 144 4 (SLit 0) 0 HRa ltac:(wh_in)
      ltac:(lia) eq_refl j Hj). }
  assert (V152A : forall j, (j < 8)%nat ->
    aview segs (w_H W) mA (TA_g_s + 152 + Z.of_nat j) = Some (YO0f.le_byte now 8 j)).
  { intros j Hj. replace (TA_g_s + 152 + Z.of_nat j) with (base_val EA (Some 19%nat) + 152 + Z.of_nat j)
      by (cbn [base_val]; rewrite U19A; unfold WAKE_S; lia).
    exact (wh_chunk_bytes EA (w_H W) mA (Some 19%nat) 152 160 152 160 _ 152 8 (SOff 20 0) now HRb ltac:(wh_in)
      ltac:(lia) ltac:(cbn [sv_denot]; rewrite (EAl 20%nat ltac:(lia)), (EE8 20%nat 20%bv eq_refl), P20,
                        Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) j Hj). }
  clear HRa HRb.
  (* the registers at +0x224 *)
  wh_kreg5 HS EAl EE8 (2%bv : bv 5) 2%nat P2 A2. wh_kreg5 HS EAl EE8 (3%bv : bv 5) 3%nat P3 A3.
  wh_kreg5 HS EAl EE8 (4%bv : bv 5) 4%nat P4 A4. wh_kreg5 HS EAl EE8 (8%bv : bv 5) 8%nat P8 A8.
  wh_kreg5 HS EAl EE8 (9%bv : bv 5) 9%nat P9 A9. wh_kreg5 HS EAl EE8 (18%bv : bv 5) 18%nat P18 A18.
  wh_kreg5 HS EAl EE8 (19%bv : bv 5) 19%nat P19 A19. wh_kreg5 HS EAl EE8 (20%bv : bv 5) 20%nat P20 A20.
  wh_kreg5 HS EAl EE8 (21%bv : bv 5) 21%nat P21 A21. wh_kreg5 HS EAl EE8 (24%bv : bv 5) 24%nat P24 A24.
  wh_kreg5 HS EAl EE8 (25%bv : bv 5) 25%nat P25 A25. wh_kreg5 HS EAl EE8 (26%bv : bv 5) 26%nat P26 A26.
  wh_reg HS (22%bv : bv 5) (w64 (F + 144)) A22
    ltac:(cbn [sv_denot]; rewrite (EAl 25%nat ltac:(lia)), (EE8 25%nat 25%bv eq_refl), P25; unfold w64;
          rewrite (unsigned_lit_small F) by lia; reflexivity).
  (* run 4b, +0x224 .. +0x25c: e2's shadow bytes, the arguments, `jal send_control` *)
  pmkst HS.
  clear HS SHOK HEI.
  pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HARA.
  destruct (al_frames _ _ LAWS _ _ _ _ _ WAKE_CID pos HARA Hin2) as (_ & _ & _ & HFshA).
  change (fs_frame_bytes WAKE_CID / 8) with 32 in HFshA.
  pose proof (wh_entry8b W (ms_regs msA) mA (SHADOW_OFF + F / 8) A24
    ltac:(unfold SHADOW_OFF; lia) ltac:(unfold SHADOW_OFF; lia)
    ltac:(intros a Ha; replace a with (shadow_addr F + (a - shadow_addr F)) by (unfold shadow_addr; lia);
          exact (proj1 (HFshA (a - shadow_addr F) ltac:(unfold shadow_addr; lia))))) as HS.
  assert (SHOK : sh_ok segs (SOff 32 0) (@nil shent) (wh_E (ms_regs msA)) (mrestrict (w_H W) mA)) by constructor.
  assert (HEI : img_env VAL A_LIM (wh_E (ms_regs msA))) by apply wh_env_img.
  assert (EEA : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (wh_E (ms_regs msA)) n = YK11.getr (ms_regs msA) r)
    by (intros n r Hn; apply wh_ew_reg; exact Hn).
  assert (U24d : bv_unsigned (ew (wh_E (ms_regs msA)) 24) = SHADOW_OFF + F / 8)
    by (rewrite (EEA 24%nat 24%bv eq_refl), A24; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  lazymatch goal with |- SRr _ ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr segs Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + WH_C8b)) mm rom) mdx) Q) end.
  paj_run_tok RUN HS HJ SHOK WH_B0.
  { wh_awr_rs.
    eapply (awr_ok_x_cons_own _ _ _ _ _ _ _ _ _ _ _ _ WAKE_CID pos); [left; reflexivity | | apply awr_ok_x_nil].
    intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U24d in Ha.
    right. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes WAKE_CID / 8) with 32.
    change (frame_addr lyc WAKE_CID pos) with F. unfold shadow_addr. lia. }
  rename HF into HF4b, HFr into HFr4b, HG into HG4b.
  lazymatch type of HS with
  | st_ok_pi _ _ ?EF _ (restrict _ ?mf) => set (EC := EF) in HS; rename mf into msC
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok _ ?EF _ (restrict _ ?mf) =>
      set (EC := EF) in HS; rename mf into msC
  end.
  assert (ECl : forall n, (n < 1024)%nat -> ew EC n = ew (wh_E (ms_regs msA)) n)
    by (intros n Hn; unfold EC; rewrite ?ew_ewset_other by lia; reflexivity).
  assert (U24C : bv_unsigned (ew EC 24) = SHADOW_OFF + F / 8) by (rewrite ECl by lia; exact U24d).
  set (mC := ms_mem msC) in *.
  (* run 4b wrote e2's shadow bytes only *)
  assert (KR4b : forall a, 0 <= a < 2 ^ 64 -> ~ (SHADOW_OFF + F / 8 + 18 <= a < SHADOW_OFF + F / 8 + 26) ->
    aview segs (w_H W) mC a = aview segs (w_H W) mA a).
  { intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ (fun x => SHADOW_OFF + F / 8 + 18 <= x < SHADOW_OFF + F / 8 + 26)
      HFr4b); [| exact Ha | exact Hn].
    intros b wlo whi x Hin Hx.
    lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
    cbn [In] in Hin.
    repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; rewrite ?U24d in Hx; lia |]).
    destruct Hin. }
  wh_region HS 0%nat HRc.
  assert (VSH : forall i, 0 <= i < 8 ->
    aview segs (w_H W) mC (SHADOW_OFF + F / 8 + 18 + i) = Some (if i <? 7 then 0 else 4)).
  { intros i Hi.
    assert (Hi' : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by lia.
    replace (SHADOW_OFF + F / 8 + 18 + i) with (base_val EC (Some 24%nat) + (18 + i) + Z.of_nat 0)
      by (cbn [base_val]; rewrite U24C; lia).
    destruct Hi' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]];
    lazymatch goal with |- aview _ _ _ (_ + ?o + _) = _ =>
      first [ rewrite (wh_chunk_bytes EC (w_H W) mC (Some 24%nat) 18 26 18 26 _ o 1 (SLit 0) 0 HRc ltac:(wh_in)
                ltac:(lia) eq_refl 0 ltac:(lia)); reflexivity
            | rewrite (wh_chunk_bytes EC (w_H W) mC (Some 24%nat) 18 26 18 26 _ o 1 (SLit 4) 4 HRc ltac:(wh_in)
                ltac:(lia) eq_refl 0 ltac:(lia)); reflexivity ] end. }
  clear HRc.
  assert (KR4 : forall a, 0 <= a < 2 ^ 64 ->
    ~ (WAKE_S + 140 <= a < WAKE_S + 148 \/ WAKE_S + 152 <= a < WAKE_S + 160 \/
       SHADOW_OFF + F / 8 + 18 <= a < SHADOW_OFF + F / 8 + 26) ->
    aview segs (w_H W) mC a = aview segs (w_H W) m8 a).
  { intros a Ha Hn. rewrite (KR4b a Ha ltac:(intros X; apply Hn; tauto)).
    exact (KR4a a Ha ltac:(intros [X | X]; apply Hn; tauto)). }
  assert (GR4 : forall a, apresent (w_H W) m8 a -> apresent (w_H W) mC a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG4b (GR4a a Ha))).
  assert (KGS : forall a, WAKE_S <= a < WAKE_S + TW.SZ_g_s -> aview segs (w_H W) mC a = aview segs (w_H W) mA a).
  { intros a Ha. apply KR4b; [unfold WAKE_S, TA_g_s, TW.SZ_g_s in *; lia | unfold SHADOW_OFF, WAKE_S, TA_g_s, TW.SZ_g_s in *; lia]. }
  assert (V140 : forall j, (j < 4)%nat ->
    aview segs (w_H W) mC (TA_g_s + 140 + Z.of_nat j) = Some (YO0f.le_byte 0 4 j))
    by (intros j Hj; rewrite KGS by (unfold WAKE_S, TW.SZ_g_s; lia); exact (V140A j Hj)).
  assert (V144 : forall j, (j < 4)%nat ->
    aview segs (w_H W) mC (TA_g_s + 144 + Z.of_nat j) = Some (YO0f.le_byte 0 4 j))
    by (intros j Hj; rewrite KGS by (unfold WAKE_S, TW.SZ_g_s; lia); exact (V144A j Hj)).
  assert (V152 : forall j, (j < 8)%nat ->
    aview segs (w_H W) mC (TA_g_s + 152 + Z.of_nat j) = Some (YO0f.le_byte now 8 j))
    by (intros j Hj; rewrite KGS by (unfold WAKE_S, TW.SZ_g_s; lia); exact (V152A j Hj)).
  (* the world relation at wake_w1 Bw now *)
  assert (TWC : tw_at TMAP_A (aview segs (w_H W) mC) (wake_w1 Bw now)).
  { apply (wh_tw_w1 (aview segs (w_H W) m8) _ Bw now Htw8 V140 V144 V152).
    intros x Hx H1 H2. pose proof (TMAP_A_hull x Hx) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
    apply KR4; [lia|]. intros [X | [X | X]]; [unfold WAKE_S in X; lia | unfold WAKE_S in X; lia |
      unfold SHADOW_OFF in X; lia]. }
  lazymatch type of HJ with context [@W_journalG.ajournal_gx ?r ?sk ?sg ?b ?g ?xo ?o ?stk ?sp ?fp ?l ?s ?w0 ?m0 ?d0
      ?ow ?l' ?s' ?w' ?m' ?md' ?kk] => set (mdC := md') in * end.
  assert (CURC : wake_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw pos F lyc S2 W mC mdC 0).
  { apply (wh_cur_step STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bw pos F S2 m8 md8 mC mdC 0
      (fun a => WAKE_S + 140 <= a < WAKE_S + 148 \/ WAKE_S + 152 <= a < WAKE_S + 160 \/
                SHADOW_OFF + F / 8 + 18 <= a < SHADOW_OFF + F / 8 + 26)
      LAWS HGX FFL HAR Eab2 eq_refl ltac:(lia) ltac:(lia) CUR8 ltac:(rewrite Z.add_0_r; exact HJ)).
    - intros a [X | [X | X]].
      + right; right. apply wh_inG. unfold TW.SZ_g_s. lia.
      + right; right. apply wh_inG. unfold TW.SZ_g_s. lia.
      + right; left. unfold dkg_nf. right; left. change (fs_frame_bytes WAKE_CID / 8) with 32. lia.
    - intros a [X | [X | X]] Hs; rewrite ?CS in X; unfold SHADOW_OFF in *; lia.
    - intros a [X | [X | X]] Hf.
      + exact (NGF a ltac:(lia) (wh_inG a ltac:(unfold TW.SZ_g_s; lia))).
      + exact (NGF a ltac:(lia) (wh_inG a ltac:(unfold TW.SZ_g_s; lia))).
      + destruct HSHF; lia.
    - exact KR4.
    - exact GR4. }
  (* the registers at the call *)
  wh_kreg5 HS ECl EEA (2%bv : bv 5) 2%nat A2 C2. wh_kreg5 HS ECl EEA (3%bv : bv 5) 3%nat A3 C3.
  wh_kreg5 HS ECl EEA (4%bv : bv 5) 4%nat A4 C4. wh_kreg5 HS ECl EEA (8%bv : bv 5) 8%nat A8 C8.
  wh_kreg5 HS ECl EEA (9%bv : bv 5) 9%nat A9 C9. wh_kreg5 HS ECl EEA (18%bv : bv 5) 18%nat A18 C18.
  wh_kreg5 HS ECl EEA (19%bv : bv 5) 19%nat A19 C19. wh_kreg5 HS ECl EEA (20%bv : bv 5) 20%nat A20 C20.
  wh_kreg5 HS ECl EEA (21%bv : bv 5) 21%nat A21 C21. wh_kreg5 HS ECl EEA (24%bv : bv 5) 24%nat A24 C24.
  wh_kreg5 HS ECl EEA (25%bv : bv 5) 25%nat A25 C25. wh_kreg5 HS ECl EEA (26%bv : bv 5) 26%nat A26 C26.
  wh_kreg5 HS ECl EEA (22%bv : bv 5) 22%nat A22 C22.
  assert (HEIC : img_env VAL A_LIM EC)
    by (unfold EC; match goal with H : img_env _ _ ?E |- img_env _ _ ?E => exact H end).
  wh_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 22264)) C1 ltac:(apply codeptr_val; exact HEIC).
  wh_reg HS (10%bv : bv 5) (w64 WAKE_S) C10
    ltac:(cbn [sv_denot]; rewrite (ECl 19%nat ltac:(lia)), (EEA 19%nat 19%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
          exact A19).
  wh_reg HS (11%bv : bv 5) (w64 TS0.DIGINET_CMD_WAKE) C11 ltac:(cbn [sv_denot]; reflexivity).
  wh_reg HS (12%bv : bv 5) (w64 (bv_swrap 32 0)) C12 ltac:(cbn [sv_denot]; reflexivity).
  wh_reg HS (13%bv : bv 5) (w64 (F + 144)) C13
    ltac:(cbn [sv_denot]; rewrite (ECl 22%nat ltac:(lia)), (EEA 22%nat 22%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
          exact A22).
  wh_reg HS (14%bv : bv 5) (w64 (sp1 + 16)) C14
    ltac:(cbn [sv_denot]; rewrite (ECl 9%nat ltac:(lia)), (EEA 9%nat 9%bv eq_refl), A9;
          rewrite (unsigned_lit_small sp1) by lia; reflexivity).
  pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HARC.
  destruct (al_frames _ _ LAWS _ _ _ _ _ WAKE_CID pos HARC Hin2) as (_ & _ & HFbC & HFshC).
  change (fs_frame_bytes WAKE_CID / 8) with 32 in HFshC. change (fs_frame_bytes WAKE_CID) with 256 in HFbC.
  assert (ESH : shadow_addr F = SHADOW_OFF + F / 8) by reflexivity.
  assert (HFshv : forall i, 0 <= i < 32 -> aview segs (w_H W) mC (SHADOW_OFF + F / 8 + i) <> None).
  { intros i Hi. apply can_aview_vis. rewrite <- ESH. exact (proj1 (HFshC i Hi)). }
  (* +0x25c: `jal send_control`, a G-form callee in the same G journal *)
  pmkst HS.
  set (regsC := ms_regs msC) in *.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (@cfg_at fx segs (transport_sigma TS_send_control) rg mm mdx) Q) end.
  assert (USPC : spZ regsC = sp1) by (unfold spZ; rewrite C2; apply unsigned_lit_small; lia).
  pose proof (SND0 fx) as SND.
  assert (HmS := Hm). rewrite wake_model in HmS.
  rewrite (proj2 (Z.eqb_neq _ _) Hdk), (proj2 (Z.eqb_eq _ _) Hfo) in HmS.
  revert HmS.
  destruct (TSS.send_control_m timg_A TF (wake_w1 Bw now) TS0.DIGINET_CMD_WAKE 0) as [[B1 [rs e2]]|] eqn:ESC;
    intros HmS; cbv beta iota delta [negb] in HmS; [| exfalso; discriminate HmS].
  pose proof (tw_len _ _ _ Htw) as HLB.
  destruct (wk_w1_keep Bw now HLB) as (L1 & KS1 & KG1 & KF1 & KM1 & KM2 & KN1 & KC1 & KC2).
  assert (Hkp0 : F + 144 <> 0) by lia.
  destruct (wh_garr8_ex (w_H W) mC (F + 144) 60 ltac:(intros a Ha; exact (proj1 (HFbC a ltac:(lia)))))
    as (K & HKl & HKg).
  destruct (wh_garr8_ex (w_H W) mC (sp1 + 16) 8
    ltac:(intros a Ha; apply (wh_jpres _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ); lia)) as (KL & HKLl & HKLg).
  pose proof Hlyle as (_ & _ & _ & _ & _ & ELF & _ & _ & _ & ESLO & ESHI & _).
  assert (EBC : BASE + 22264 = 0x8695c) by (vm_compute; reflexivity).
  pose proof (Z.div_mod sp1 32 ltac:(lia)) as D32. rewrite Hsp1al, Z.add_0_r in D32.
  assert (HNEV : 0 <= NOTICE_EV) by (vm_compute; intro Hx; discriminate Hx).
  eapply SRr_bind.
  { apply (SND STK sp0 FP ly S W0 mem0 md0 ((WAKE_CID, pos) :: own) lyc S2 W mC mdC k regsC
      TS0.DIGINET_CMD_WAKE 0 (F + 144) (sp1 + 16) rs K KL e2 TF (wake_w1 Bw now) B1 HJ).
    - rewrite C1. apply (ret_ok_codeptr_v (PI := PI_transport)); [lia | reflexivity].
    - unfold raZ. rewrite C1, EBC. rewrite unsigned_lit_small by lia. lia.
    - exact C3.
    - exact C4.
    - exact C10.
    - exact C11.
    - exact C12.
    - exact C13.
    - exact C14.
    - rewrite USPC. rewrite D32. replace (32 * (sp1 / 32)) with ((2 * (sp1 / 32)) * 16) by ring.
      apply Z.mod_mul. lia.
    - rewrite USPC. lia.
    - rewrite USPC. lia.
    - vm_compute. split; [intro Hx; discriminate Hx | reflexivity].
    - lia.
    - right. split; [lia|]. split.
      { exists WAKE_CID, pos. split; [rewrite Hfrs2; left; reflexivity|].
        change (frame_addr lyc WAKE_CID pos) with F. change (fs_frame_bytes WAKE_CID) with 256.
        unfold SENDCTL_F. lia. }
      split.
      { eapply (transport_twr_ok_g_intro segs B LAWS); [exact HJ|]. intros a Ha. left. rewrite USPC. split.
        - unfold awr_byte. right; right; right. unfold in_frames. exists WAKE_CID, pos. split; [left; reflexivity|].
          left. unfold in_zr. cbn [fst snd]. change (frame_addr lyc WAKE_CID pos) with F.
          change (fs_frame_bytes WAKE_CID) with 256. unfold SENDCTL_F in Ha. lia.
        - unfold SENDCTL_F in Ha. lia. }
      split.
      { apply (wh_e2_rd W mC F HF0 HF64 HFapp); [| exact HFshv | exact VSH].
        intros a Ha. apply can_aview_vis. exact (proj1 (HFbC a ltac:(lia))). }
      split.
      { unfold decode_off_win. rewrite USPC. left. unfold SENDCTL_F. lia. }
      split.
      { intros x Hx. apply NGF. unfold SENDCTL_F in Hx. lia. }
      split; [rewrite HKl; reflexivity|].
      split; [exact HKg|].
      split.
      { rewrite D32. replace (32 * (sp1 / 32) + 16) with ((4 * (sp1 / 32) + 2) * 8) by ring. apply Z.mod_mul. lia. }
      split.
      { eapply (transport_twr_ok_g_intro segs B LAWS); [exact HJ|]. intros a Ha. left. rewrite USPC. split.
        - unfold awr_byte. left. lia.
        - lia. }
      split.
      { destruct (stack_zshadow_ra B lyc S2 W mC mdC (sp1 + 16) 8 HARC ltac:(lia) ltac:(lia) ltac:(lia)) as [HRA HHV].
        split; [intros a Ha; apply can_aview_vis; apply (wh_jpres _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ); lia|].
        split; [exact HRA|]. split; [exact HHV|].
        split; [unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd; lia|]. lia. }
      split.
      { unfold decode_off_win. rewrite USPC. right. lia. }
      split.
      { intros x Hx Hg. pose proof (inG_low segs B transport_segs_low TG.G_HARNESS x HGX Hg) as Hl.
        unfold kLowMemEnd in Hl. lia. }
      split; [exact HKLl|].
      split; [exact HKLg|].
      left. unfold SENDCTL_F. lia.
    - exact TWC.
    - rewrite KF1. exact Hfn.
    - exact ESC.
    - pose proof CURC as (_ & _ & _ & _ & _ & _ & KCC & _ & _).
      exact (wh_rom lyc Sc W memc W mC _ _ (wake_wr Bw) HROU HRNE KCC HROM).
    - rewrite KM1, KM2. exact Hinv1.
    - intros s Hs Hst. rewrite KN1 in Hs. rewrite KC1 in Hst by lia. rewrite KC2 by lia. exact (Hinv4 s Hs Hst).
    - rewrite Hfrs2, <- wake_cid_sendctl. cbn [count_cid]. rewrite Z.eqb_refl.
      change (if true then 1 else 0) with 1. lia.
    - unfold WAKE_EV in Hev. lia. }
  (* +0x260, after send_control returns *)
  intros W3 c3 _ HPOST.
  unfold transport_sendctl_post, transport_cg_post_out in HPOST. cbv beta in HPOST.
  destruct HPOST as (ly3 & S3 & regs3 & mem3 & md3 & e3 & -> & He3 & HJ3 & HP3 & Hfr3 & Hperm3 & HK3 & Hmo3 &
    (HX10 & HXtw & HXgf & HXkeep)).
  destruct HXkeep as [HXk | (HXe2 & HXkl)]; [exfalso; exact (Hkp0 HXk)|].
  pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HAR3.
  pose proof HJ3 as (_ & _ & (memS3 & HJi3 & _) & _). rewrite !Z.add_0_r in HJi3.
  pose proof HJi3 as (_ & Hlyle3 & _). clear HJi3 memS3.
  pose proof Hlyle3 as (_ & _ & _ & _ & _ & ELF3 & _).
  assert (ELF3c : ly_F ly3 = ly_F lyc) by (rewrite ELF3, ELF; reflexivity).
  assert (EF3 : frame_addr ly3 WAKE_CID pos = F)
    by (change F with (frame_addr lyc WAKE_CID pos); unfold frame_addr; rewrite ELF3c; reflexivity).
  assert (Hfrs3 : frames S3 = (WAKE_CID, pos) :: frames Sc) by (rewrite Hfr3; exact Hfrs2).
  assert (Hin3 : In (WAKE_CID, pos) (frames S3)) by (rewrite Hfrs3; left; reflexivity).
  unfold sendctl_outs in HK3. rewrite (proj2 (Z.eqb_neq _ _) Hkp0) in HK3.
  pose proof HK3 as (L31 & _ & _ & L34 & _).
  (* the 8 bytes at klp, present at the returned memory *)
  assert (HKLlen : length (TW.zs (match e2 with [] => KL | _ => TW.put 8 (Z.of_nat (length e2)) end)) = 8%nat)
    by (destruct e2; unfold TW.zs; rewrite length_map; [exact HKLl | apply TWL.length_put]).
  assert (HPKL : forall a, inG [(sp1 + 16, 8)] a -> apresent (w_H W3) mem3 a).
  { intros a Ha. unfold inG in Ha. apply Exists_exists in Ha as (rr & Hrr & Har). cbn [In] in Hrr.
    destruct Hrr as [<- | []]. unfold in_zr in Har. cbn [fst snd] in Har.
    apply (apresent_of_aview segs (w_H W3) mem3 a ltac:(lia)).
    - intros Him. pose proof (transport_segs_low a Him). unfold kLowMemEnd in *. lia.
    - apply (wh_garr8_vis (w_H W3) mem3 (sp1 + 16) _ HXkl). rewrite HKLlen. lia. }
  (* what the call kept, from its entry to send_control's return *)
  destruct (dkg_nf_sep segs B LAWS transport_segs_low lyc Sc S2 W mC mdC WAKE_CID pos F (flag_addr lyc WAKE_CID pos)
    HARC Hfrs2 Eab2 eq_refl eq_refl FFL) as (N1 & N2 & N3 & N4).
  pose proof CURC as (_ & _ & _ & _ & _ & _ & KCC & HSVC & HFLC).
  assert (KCg : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W3 (gover [(sp1 + 16, 8)] mem3 mC)
    (spZ regs - WAKE_STK) (spZ regs) (wake_wr Bw)).
  { apply (dk_kept_trans_nf_g segs B TG.G_HARNESS lyc Sc lyc S2 W memc W mC W3 (gover [(sp1 + 16, 8)] mem3 mC)
      (spZ regs - WAKE_STK) (spZ regs) (spZ regsC - SENDCTL_STK) (spZ regsC) (wake_wr Bw)
      (sendctl_wr (F + 144) (sp1 + 16))
      (fun a => dkg_nf WAKE_CID F (flag_addr lyc WAKE_CID pos) a \/ sp1 + 16 <= a < sp1 + 24)).
    - lia.
    - lia.
    - intros c p. reflexivity.
    - intros f Hf. rewrite Hfrs2. right. exact Hf.
    - intros bm Hbm. rewrite Eab2. exact Hbm.
    - intros b m i Hb Hi [Hn | Hn]; [exact (N1 b m i Hb Hi Hn)|].
      destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hb) as (_ & H4096 & Hbc & _). lia.
    - intros cid p a Hin Hr [Hn | Hn]; [exact (N3 cid p a Hin Hr Hn)|].
      destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid p HAR Hin) as (G4096 & Gce & _).
      pose proof (fs_frame_bytes_nonneg cid) as Hfs.
      destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [lia|].
      pose proof (shadow_range_end (frame_addr lyc cid p) (fs_frame_bytes cid) Hfs) as Hse.
      assert (Hd : (frame_addr lyc cid p + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
      unfold shadow_addr, SHADOW_OFF in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia.
    - exact KCC.
    - exact HK3.
    - rewrite USPC. lia.
    - rewrite USPC. lia.
    - intros a Ha. unfold sendctl_wr in Ha. destruct Ha as [Ha | [Ha | (_ & [Ha | Ha])]].
      + left. unfold wake_wr. do 11 right. left. exact Ha.
      + left. unfold wake_wr. do 12 right. left. exact Ha.
      + right. left. unfold dkg_nf. left. change (fs_frame_bytes WAKE_CID) with 256. unfold SENDCTL_F in Ha. lia.
      + right. right. lia. }
  assert (KC3 : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W3 mem3 (spZ regs - WAKE_STK) (spZ regs) (wake_wr Bw)).
  { apply (wh_ungover [(sp1 + 16, 8)] lyc Sc W memc mdc W3 mem3 mC (spZ regs - WAKE_STK) (spZ regs) (wake_wr Bw)
      LAWS HAR ltac:(lia) ltac:(lia)); [| exact HPKL | exact KCg].
    intros a Ha. unfold inG in Ha. apply Exists_exists in Ha as (rr & Hrr & Har). cbn [In] in Hrr.
    destruct Hrr as [<- | []]. unfold in_zr in Har. cbn [fst snd] in Har. lia. }
  (* a byte of the own frame, its shadow or the saved words that send_control did not write is the call's *)
  assert (HGO : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 + 16 <= a < sp1 + 24) ->
    aview segs (w_H W3) mem3 a = aview segs (w_H W3) (gover [(sp1 + 16, 8)] mem3 mC) a).
  { intros a Ha Hn. symmetry. apply (gover_out_aview segs); [exact Ha|].
    intros Hg. apply Hn. unfold inG in Hg. apply Exists_exists in Hg as (rr & Hrr & Har). cbn [In] in Hrr.
    destruct Hrr as [<- | []]. unfold in_zr in Har. cbn [fst snd] in Har. lia. }
  assert (KSV3 : forall a, spZ regs - 104 <= a < spZ regs -> aview segs (w_H W3) mem3 a = aview segs (w_H W) mC a).
  { intros a Ha. rewrite HGO by lia. apply L31; [lia|]. rewrite USPC. lia. }
  assert (KFR3 : forall a, F <= a < F + 256 -> ~ (F + 144 <= a < F + 204) ->
    aview segs (w_H W3) mem3 a = aview segs (w_H W) mC a).
  { intros a Ha Hn. rewrite HGO by lia. apply (L34 WAKE_CID pos a Hin2).
    - left. unfold in_zr, frame_rng. cbn [fst snd]. change (frame_addr lyc WAKE_CID pos) with F.
      change (fs_frame_bytes WAKE_CID) with 256. lia.
    - intros Hw. unfold sendctl_wr in Hw. destruct Hw as [Hw | [Hw | (_ & [Hw | Hw])]].
      + apply (NGF a ltac:(lia)). apply wh_inG. unfold twa_fld, TW.A_S_stats_tx_frames, TW.OFF_g_s, TA_g_s in Hw.
        unfold WAKE_S, TA_g_s, TW.SZ_g_s. lia.
      + apply (NGF a ltac:(lia)). exact (wh_iosend_G SENDCTL_F a Hw).
      + unfold SENDCTL_F in Hw. lia.
      + lia. }
  assert (KSH3 : forall i, 0 <= i < 32 ->
    aview segs (w_H W3) mem3 (SHADOW_OFF + F / 8 + i) = aview segs (w_H W) mC (SHADOW_OFF + F / 8 + i)).
  { intros i Hi. rewrite HGO by (unfold SHADOW_OFF in *; lia). apply (L34 WAKE_CID pos _ Hin2).
    - right. unfold in_zr. cbn [fst snd]. change (frame_addr lyc WAKE_CID pos) with F.
      change (fs_frame_bytes WAKE_CID / 8) with 32. unfold shadow_addr. lia.
    - intros Hw. unfold sendctl_wr in Hw. destruct Hw as [Hw | [Hw | (_ & [Hw | Hw])]].
      + unfold twa_fld, TW.A_S_stats_tx_frames, TW.OFF_g_s, TA_g_s in Hw. unfold SHADOW_OFF in *. lia.
      + pose proof (wh_iosend_G SENDCTL_F _ Hw) as Hg. pose proof (inG_low segs B transport_segs_low _ _ HGX Hg) as Hl.
        unfold kLowMemEnd, SHADOW_OFF in *. lia.
      + unfold SENDCTL_F in Hw. destruct HSHF; lia.
      + unfold SHADOW_OFF in *. lia. }
  assert (CUR3 : wake_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw pos F ly3 S3 W3 mem3 md3 e3).
  { refine (conj HJ3 (conj _ (conj Hfrs3 (conj _ (conj ELF3c (conj _ (conj KC3 (conj _ _)))))))).
    - unfold WAKE_EV. lia.
    - rewrite <- Eab2. exact Hperm3.
    - exact (mo_le_trans MT MTL _ _ _ _ _ HMO Hmo3).
    - rewrite Forall_forall in HSVC |- *. intros o Ho. rewrite <- (HSVC o Ho).
      assert (Hob : 8 <= fst o <= 104).
      { unfold WAKE_SAVED in Ho. cbn [In] in Ho. repeat (destruct Ho as [<- | Ho]; [cbn [fst]; lia|]). destruct Ho. }
      apply rdword_ext. intros i Hi. apply KSV3. lia.
    - rewrite <- HFLC. unfold WAKE_FBYTES. apply rdword_ext. intros i Hi. apply KFR3; lia. }
  (* the registers send_control kept *)
  assert (RR2 : YK11.getr regs3 2 = Z_to_bv 64 sp1)
    by (transitivity (YK11.getr regsC 2); [exact (HP3 2 ltac:(hnf; lia)) | exact C2]).
  assert (RR3 : YK11.getr regs3 3 = w64 (as_gp B))
    by (transitivity (YK11.getr regsC 3); [exact (HP3 3 ltac:(hnf; lia)) | exact C3]).
  assert (RR4 : YK11.getr regs3 4 = w64 (as_tp B))
    by (transitivity (YK11.getr regsC 4); [exact (HP3 4 ltac:(hnf; lia)) | exact C4]).
  assert (RR8 : YK11.getr regs3 8 = w64 (spZ regs))
    by (transitivity (YK11.getr regsC 8); [exact (HP3 8 ltac:(hnf; lia)) | exact C8]).
  assert (RR9 : YK11.getr regs3 9 = Z_to_bv 64 sp1)
    by (transitivity (YK11.getr regsC 9); [exact (HP3 9 ltac:(hnf; lia)) | exact C9]).
  assert (RR18 : YK11.getr regs3 18 = w64 F)
    by (transitivity (YK11.getr regsC 18); [exact (HP3 18 ltac:(hnf; lia)) | exact C18]).
  assert (RR19 : YK11.getr regs3 19 = w64 WAKE_S)
    by (transitivity (YK11.getr regsC 19); [exact (HP3 19 ltac:(hnf; lia)) | exact C19]).
  assert (RR20 : YK11.getr regs3 20 = w64 now)
    by (transitivity (YK11.getr regsC 20); [exact (HP3 20 ltac:(hnf; lia)) | exact C20]).
  assert (RR21 : YK11.getr regs3 21 = w64 (WAKE_S + 18224))
    by (transitivity (YK11.getr regsC 21); [exact (HP3 21 ltac:(hnf; lia)) | exact C21]).
  assert (RR22 : YK11.getr regs3 22 = w64 (F + 144))
    by (transitivity (YK11.getr regsC 22); [exact (HP3 22 ltac:(hnf; lia)) | exact C22]).
  assert (RR24 : YK11.getr regs3 24 = Z_to_bv 64 (SHADOW_OFF + F / 8))
    by (transitivity (YK11.getr regsC 24); [exact (HP3 24 ltac:(hnf; lia)) | exact C24]).
  assert (RR25 : YK11.getr regs3 25 = w64 F)
    by (transitivity (YK11.getr regsC 25); [exact (HP3 25 ltac:(hnf; lia)) | exact C25]).
  assert (RR26 : YK11.getr regs3 26 = w64 SHADOW_OFF)
    by (transitivity (YK11.getr regsC 26); [exact (HP3 26 ltac:(hnf; lia)) | exact C26]).
  destruct (wk_sc_ret _ _ _ _ _ _ _ _ ESC) as [Rrs Hret].
  (* +0x260: `bltz a0`, from a state with no region *)
  rewrite C1.
  change (Z_to_bv 64 (BASE + 22264)) with (Z_to_bv 64 (BASE + WH_C9)).
  clear HS SHOK HEI.
  pose proof (wh_entry0 W3 regs3 mem3 WH_C9) as HS.
  assert (SHOK3 : sh_ok segs (SOff 32 0) (@nil shent) (wh_E regs3) (mrestrict (w_H W3) mem3)) by constructor.
  assert (HEI9 : img_env VAL A_LIM (wh_E regs3)) by apply wh_env_img.
  assert (D10r : sv_denot (wh_E regs3) (SOff 10 0) = Z_to_bv 64 rs)
    by (cbn [sv_denot]; rewrite (wh_ew_reg regs3 10 10%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact HX10).
  psrr_branch_tok RUN BR HS SHOK3 WH_B0.
  + (* rs < 0: the e2 cut with a0 = rs *)
    cbn [branch_taken] in Hc. rewrite D10r in Hc.
    change (sv_denot (wh_E regs3) (SLit 0)) with (Z_to_bv 64 0) in Hc.
    rewrite (wk_lts0 rs Rrs) in Hc. apply Z.ltb_lt in Hc.
    rewrite (proj2 (Z.ltb_lt _ _) Hc) in HmS.
    destruct (wake_some_inv _ _ _ _ HmS) as [EB ER].
    paj_run_to_tok RUNTO HS HJ3 SHOK3 WH_B0 WAKE_E2.
    { wh_awr_rs. apply awr_ok_x_nil. }
    wh_after_cut HS W3 KD GR mem3 msF.
    wh_kreg HS regs3 (2%bv : bv 5) 2%nat RR2 Y2. wh_kreg HS regs3 (3%bv : bv 5) 3%nat RR3 Y3.
    wh_kreg HS regs3 (4%bv : bv 5) 4%nat RR4 Y4. wh_kreg HS regs3 (8%bv : bv 5) 8%nat RR8 Y8.
    wh_kreg HS regs3 (9%bv : bv 5) 9%nat RR9 Y9. wh_kreg HS regs3 (18%bv : bv 5) 18%nat RR18 Y18.
    wh_kreg HS regs3 (24%bv : bv 5) 24%nat RR24 Y24. wh_kreg HS regs3 (25%bv : bv 5) 25%nat RR25 Y25.
    wh_kreg HS regs3 (10%bv : bv 5) 10%nat HX10 Y10.
    pmkst HS.
    lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
      change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + WAKE_E2)) mm rom) mdx) Q) end.
    apply (E2 HLAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now res TF Bw Bw' pos sp1 F ly3 S3 W3
      (ms_mem msF) _ e3 (ms_regs msF) HFIX).
    * refine (conj (wh_cur_move STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw pos F ly3 S3 W3 mem3 md3
        (ms_mem msF) _ e3 CUR3 HJ3 KD GR) (conj _ _)).
      -- rewrite <- EB. apply (tw_kept TMAP_A (aview segs (w_H W3) mem3)); [exact HXtw | intros x _; exact (KD x)].
      -- rewrite <- EB. exact HXgf.
    * unfold wake_regs_rel, wake_regs_core.
      refine (conj (conj Y2 (conj _ (conj _ (conj Y8 (conj Y9 (conj Y18 (conj Y24 Y25))))))) _).
      -- rewrite Y3. symmetry. exact Hgp.
      -- rewrite Y4. symmetry. exact Htp.
      -- rewrite Y10, ER. reflexivity.
  + (* 0 <= rs: the mid cut *)
    cbn [branch_taken] in Hc. rewrite D10r in Hc.
    change (sv_denot (wh_E regs3) (SLit 0)) with (Z_to_bv 64 0) in Hc.
    rewrite (wk_lts0 rs Rrs) in Hc. apply Z.ltb_ge in Hc.
    destruct (Hret Hc) as [Hrs0 Hle2].
    assert (Hne : e2 <> []) by (intros Ex; rewrite Ex in Hle2; discriminate Hle2).
    rewrite (wh_nonempty e2 K Hne) in HXe2. rewrite (wh_nonempty_put e2 KL Hne), Hle2 in HXkl.
    destruct (wk_sc_keep _ _ _ _ _ _ _ _ L1 ESC) as (_ & KSt & KGn).
    paj_run_to_tok RUNTO HS HJ3 SHOK3 WH_B0 WAKE_MID.
    { wh_awr_rs. apply awr_ok_x_nil. }
    wh_after_cut HS W3 KD GR mem3 msF.
    wh_kreg HS regs3 (2%bv : bv 5) 2%nat RR2 Y2. wh_kreg HS regs3 (3%bv : bv 5) 3%nat RR3 Y3.
    wh_kreg HS regs3 (4%bv : bv 5) 4%nat RR4 Y4. wh_kreg HS regs3 (8%bv : bv 5) 8%nat RR8 Y8.
    wh_kreg HS regs3 (9%bv : bv 5) 9%nat RR9 Y9. wh_kreg HS regs3 (18%bv : bv 5) 18%nat RR18 Y18.
    wh_kreg HS regs3 (19%bv : bv 5) 19%nat RR19 Y19. wh_kreg HS regs3 (20%bv : bv 5) 20%nat RR20 Y20.
    wh_kreg HS regs3 (21%bv : bv 5) 21%nat RR21 Y21. wh_kreg HS regs3 (22%bv : bv 5) 22%nat RR22 Y22.
    wh_kreg HS regs3 (24%bv : bv 5) 24%nat RR24 Y24. wh_kreg HS regs3 (25%bv : bv 5) 25%nat RR25 Y25.
    wh_kreg HS regs3 (26%bv : bv 5) 26%nat RR26 Y26.
    pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HARF.
    destruct (al_frames _ _ LAWS _ _ _ _ _ WAKE_CID pos HARF Hin3) as (_ & _ & _ & HFshF).
    rewrite EF3 in HFshF. change (fs_frame_bytes WAKE_CID / 8) with 32 in HFshF.
    pmkst HS.
    lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
      change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + WAKE_MID)) mm rom) mdx) Q) end.
    apply (MID HLAWS CPY0 SET0 NT0 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs now res TF Bw Bw' B1 e2
      rs pos sp1 F ly3 S3 W3 (ms_mem msF) _ e3 (ms_regs msF) HFIX).
    * assert (HXe2F : garr8 segs (mrestrict (w_H W3) (ms_mem msF)) (F + 144) (TW.zs e2))
        by (apply (wh_garr8_move (w_H W3) mem3); [exact HXe2 | intros x _; exact (KD x)]).
      refine (conj (wh_cur_move STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw pos F ly3 S3 W3 mem3 md3
        (ms_mem msF) _ e3 CUR3 HJ3 KD GR) _).
      refine (conj Hdk (conj Hfo (conj ESC (conj Hc (conj Hle2 (conj _ (conj _ (conj _ (conj HXgf
        (conj HXe2F (conj _ _))))))))))).
      -- rewrite KSt. exact KS1.
      -- rewrite KGn. exact KG1.
      -- apply (tw_kept TMAP_A (aview segs (w_H W3) mem3)); [exact HXtw | intros x _; exact (KD x)].
      -- unfold WAKE_E2OFF. apply (wh_e2_rd W3 (ms_mem msF) F HF0 HF64 HFapp).
         ++ intros a Ha. apply (wh_garr8_vis (w_H W3) (ms_mem msF) (F + 144) _ HXe2F).
            unfold TW.zs. rewrite length_map, Hle2. lia.
         ++ intros i Hi. apply can_aview_vis. rewrite <- ESH. exact (proj1 (HFshF i Hi)).
         ++ intros i Hi. rewrite KD.
            replace (SHADOW_OFF + F / 8 + 18 + i) with (SHADOW_OFF + F / 8 + (18 + i)) by ring.
            rewrite (KSH3 (18 + i) ltac:(lia)). rewrite <- (VSH i Hi). f_equal. lia.
      -- unfold WAKE_KLPOFF. apply (wh_garr8_move (w_H W3) mem3); [exact HXkl | intros x _; exact (KD x)].
    * unfold wake_regs_mid, wake_regs_core.
      refine (conj (conj Y2 (conj _ (conj _ (conj Y8 (conj Y9 (conj Y18 (conj Y24 Y25))))))) _).
      -- rewrite Y3. symmetry. exact Hgp.
      -- rewrite Y4. symmetry. exact Htp.
      -- refine (conj Y19 (conj Y20 (conj Y21 (conj _ Y26)))). unfold WAKE_E2OFF. exact Y22.
Qed.
End sh.
