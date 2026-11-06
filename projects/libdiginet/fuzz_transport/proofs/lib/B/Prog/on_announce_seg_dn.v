(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Mem.v, with its module paths and module names changed; 1136 of its 1210 lines of code are new or changed and 413 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/TickRetx.v, with its module paths, module names and numbers changed; 1683 of its 1806 lines of code are new or changed and 1087 lines of the source are left out. *)
(* on_announce_seg_dn: Lemma onann_dn_piece : onann_dn_stmt (lib/B/Prog/OnannCutB.v), the desk-notice piece of
   on_announce's image-B walk, offsets +0x300 .. +0x3e8 of the listing lib/B/Prog/DgnTransportBList.v
   (fuzz_transport.asan-ubsan 0x87fc8 .. 0x880b0), ending at the two cuts onann_e0_at (+0x3ec, cmd 0xe0) and
   onann_e1_at (+0x4a0, cmd 0xe1), which it is given.

   What the code does. s5 = n = F + 112 (the desk notice in the function's own class-3 frame); n's nine shadow bytes
   14 .. 22 := 0 (n usable); the 4-byte store of 1 (N_DESK) at n (:196); `beq a1, zero` (a1 = 1, the UBSan test of
   s & 7 the find_mac / personality pieces left) is not taken, so the trap word +0x774 is not reached; a3 = s + 112,
   the checked 4-byte load of g_s.state (the shadow byte of g_s's payload is 0: trans_onann_cells, read by
   DgnTransportBCg.v decode_zshadow_rd); the stores at n + 4 (the state), n + 8 (8 zero bytes) and n + 16 (fp); the
   check of the 8-byte store at n + 24 (the frame's shadow byte 17, 0 since +0x314); the spills of the shadow address
   of s + 112 at s1 + 32 and of s + 112 at s1 + 40 (onann_slots_arm); the stores of a at n + 24, p at n + 32 and
   off at n + 40 (s7 = off); `jal __asan_memset` (+0x390: n + 44, 0, 28) through TransportGCg.v gx_intrin_at; the
   checks of the 8-byte loads at s + 96 and s + 104 with their spills at s1 + 8 and s1 + 0 (onann_slots_ntf);
   a2 = g_s.notify (= TI.ti_notice timg_B by the model's call_notify), a0 = the notify context, a1 = n, and the
   indirect call `jalr a2` (+0x3cc) of notice (notice_cg.v transport_notice_cg at TI.ti_notice timg_B, a G-form
   callee in the same journal). After it: the checked reload of the command byte at f + 30 through the spills at
   s1 + 48 and s1 + 56 (on_announce_seg_kit.v onann_f30 at the post-notice memory) and `bne a0, a1` (+0x3e8, a1 =
   224): 0xe0 falls through to onann_e0_at (+0x3ec), 0xe1 goes to onann_e1_at (+0x4a0).

   Four runs of the token engine over the caller's G journal (lib/B/Prog/TransportGRunB.v paj_run_x / paj_run_to_x),
   each from a symbolic state whose constant registers (s4 = s, s8 = the shadow base, a1 = 1) are pinned as literals,
   so every check of a g_s access reads a literal shadow address:
     run 1  +0x300 .. +0x360  n's shadow bytes and n's first three fields; it stops at +0x364, the load of the
                              frame's shadow byte 17, whose address is not a literal (the frame is symbolic);
     run 2  +0x364 .. +0x390  that byte read as the region of a2 (its value 0 is run 1's store), the spills and the
                              stores of a, p and off; it stops at the call of __asan_memset;
     run 3  +0x394 .. +0x3cc  the two g_s checks, the spills, the loads of notify and of the context, and the
                              indirect call, which paj_run_to_x follows to notice's entry;
     run 4  +0x3d0 .. +0x3e8  the reload of f + 30; the `bne` is split (DgnTransportBPaLib.v psrr_branch_tok) from a
                              state with no region, and each arm runs to its cut.
   The bytes of the notice are collected as val_mem facts at each run's end and carried to the call of notice by the
   runs' frame_of facts; the 72 bytes are then trans_ntc_at's NB (check_state_data_cg.v trans_ntc_at) for
   onann_dntc timg_B (onann_w1 timg_B Bw b) b, with the announce a the parse filled (onann_a_ok). What the call kept
   is folded step by step (TransportGFrame.v dk_kept_nfz_gw, TransportGCg.v dk_kept_trans_nf_g for notice). *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGFrame TransportGNotice.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TransportGRwB TransportGRunB CanKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TransportGFrameB TransportGNoticeB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_set_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import send_control_cg set_state_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_wake_cg maybe_online_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_tick_cg on_ack_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_personality_from_name_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_announce_parse_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import on_announce_cg OnannCutB on_announce_seg_kit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TSess0 TSess TCb TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require WalkNotify.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Mem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec DgnLib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module FCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.AsanCells.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module WN := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T.WalkNotify.
Module LMem := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Mem.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 1. The pcs, the shadow addresses and the symbolic states            *)
(* ------------------------------------------------------------------ *)

(* The shadow bytes of g_s the checks of this piece read, as literals. *)
Definition ONDN_SH96 : Z := 2148220628.
Definition ONDN_SH104 : Z := 2148220629.
Definition ONDN_SH112 : Z := 2148220630.
Lemma ondn_sh_eq : ONDN_SH96 = SHADOW_OFF + (ONANN_S + 96) / 8 /\ ONDN_SH104 = SHADOW_OFF + (ONANN_S + 104) / 8 /\
  ONDN_SH112 = SHADOW_OFF + (ONANN_S + 112) / 8 /\ ONANN_S = 6157888.
Proof. repeat split; reflexivity. Qed.

(* The ends of the four runs. *)
Definition ONDN_C1 : Z := AF_on_announce + 0x364.   (* the load of the frame's shadow byte 17 *)
Definition ONDN_C2 : Z := AF_on_announce + 0x394.   (* __asan_memset's return address *)
Definition ONDN_C3 : Z := AF_on_announce + 0x3d0.   (* notice's return address *)
Definition ONDN_C4 : Z := AF_on_announce + 0x3e8.   (* `bne a0, a1` *)

(* run 1 (+0x300): the frame's shadow bytes 14 .. 22 at s2 (atom 18, written), the notice's first 24 bytes at s3
   (atom 19, written), the shadow byte of s + 112 and the 4 bytes of g_s.state at their literal addresses (read;
   the state is atom 32). s4, s8 and a1 are pinned as literals. *)
Definition ondn_R_sh : YP09.region := YP09.mkRegion (Some 18%nat) 14 23 14 23 [].
Definition ondn_R_n1 : YP09.region := YP09.mkRegion (Some 19%nat) 112 136 112 136 [].
Definition ondn_R_gsh1 : YP09.region :=
  YP09.mkRegion None ONDN_SH112 (ONDN_SH112 + 1) 0 0 [YP09.mkChunk ONDN_SH112 (YP09.CVal 1 (SLit 0))].
Definition ondn_R_gst1 : YP09.region :=
  YP09.mkRegion None (ONANN_S + 112) (ONANN_S + 116) 0 0 [YP09.mkChunk (ONANN_S + 112) (YP09.CVal 4 (SOff 32 0))].
Definition ondn_facts1 : facts :=
  mkFacts [(18%nat, mkAF SHADOW_OFF (2 ^ 47) 0); (19%nat, mkAF 4096 (2 ^ 47) 6)] [] [].
Definition ondn_regs1 : list sv :=
  sr_set (sr_set (sr_set sr_atoms (Z_to_bv 5 20) (SLit ONANN_S)) (Z_to_bv 5 24) (SLit SHADOW_OFF))
    (Z_to_bv 5 11) (SLit 1).
Definition ss_dn1 : sstate := mkSS ONANN_DN ondn_regs1 [ondn_R_sh; ondn_R_n1; ondn_R_gsh1; ondn_R_gst1] None
  ondn_facts1.

(* run 2 (+0x364): the frame's shadow byte 17 at a2 (atom 12, read, 0), the notice's bytes 24 .. 48 at s5 (atom 21,
   written), the spill slots s1 + 32 and s1 + 40 (atom 9, written). s4, a3 and a4 are pinned as literals. *)
Definition ondn_R_shb : YP09.region := YP09.mkRegion (Some 12%nat) 0 1 0 0 [YP09.mkChunk 0 (YP09.CVal 1 (SLit 0))].
Definition ondn_R_n2 : YP09.region := YP09.mkRegion (Some 21%nat) 24 48 24 48 [].
Definition ondn_R_sl2 : YP09.region := YP09.mkRegion (Some 9%nat) 32 48 32 48 [].
Definition ondn_facts2 : facts :=
  mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (21%nat, mkAF 4096 (2 ^ 47) 4)] [] [].
Definition ondn_regs2 : list sv :=
  sr_set (sr_set (sr_set sr_atoms (Z_to_bv 5 20) (SLit ONANN_S)) (Z_to_bv 5 13) (SLit (ONANN_S + 112)))
    (Z_to_bv 5 14) (SLit ONDN_SH112).
Definition ss_dn2 : sstate := mkSS ONDN_C1 ondn_regs2 [ondn_R_shb; ondn_R_n2; ondn_R_sl2] None ondn_facts2.

(* run 3 (+0x394): the shadow bytes of s + 96 and s + 104 and the two 8-byte words there (read; the notify pointer
   is the code pointer of notice, the context is atom 32), the spill slots s1 + 0 and s1 + 8 (atom 9, written).
   s4, s8 and s10 are pinned as literals. *)
Definition ondn_R_gsh3 : YP09.region :=
  YP09.mkRegion None ONDN_SH96 (ONDN_SH96 + 2) 0 0
    [YP09.mkChunk ONDN_SH96 (YP09.CVal 1 (SLit 0)); YP09.mkChunk ONDN_SH104 (YP09.CVal 1 (SLit 0))].
Definition ondn_R_gs3 : YP09.region :=
  YP09.mkRegion None (ONANN_S + 96) (ONANN_S + 112) 0 0
    [YP09.mkChunk (ONANN_S + 96) (YP09.CVal 8 (SOff A_TEXT AF_notice));
     YP09.mkChunk (ONANN_S + 104) (YP09.CVal 8 (SOff 32 0))].
Definition ondn_R_sl3 : YP09.region := YP09.mkRegion (Some 9%nat) 0 16 0 16 [].
Definition ondn_facts3 : facts := mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5)] [] [].
Definition ondn_regs3 : list sv :=
  sr_set (sr_set (sr_set sr_atoms (Z_to_bv 5 20) (SLit ONANN_S)) (Z_to_bv 5 24) (SLit SHADOW_OFF))
    (Z_to_bv 5 26) (SLit (ONANN_S + 96)).
Definition ss_dn3 : sstate := mkSS ONDN_C2 ondn_regs3 [ondn_R_gsh3; ondn_R_gs3; ondn_R_sl3] None ondn_facts3.

(* run 4 (+0x3d0): the spill slots s1 + 48 and s1 + 56 (read: the shadow address of f + 30, atom 32, and f + 30,
   atom 33), that shadow byte (0) and the command byte at f + 30 (atom 34). *)
Definition ondn_R_sl4 : YP09.region :=
  YP09.mkRegion (Some 9%nat) 48 64 0 0
    [YP09.mkChunk 48 (YP09.CVal 8 (SOff 32 0)); YP09.mkChunk 56 (YP09.CVal 8 (SOff 33 0))].
Definition ondn_R_fsh : YP09.region := YP09.mkRegion (Some 32%nat) 0 1 0 0 [YP09.mkChunk 0 (YP09.CVal 1 (SLit 0))].
Definition ondn_R_fcmd : YP09.region :=
  YP09.mkRegion (Some 33%nat) 0 1 0 0 [YP09.mkChunk 0 (YP09.CVal 1 (SOff 34 0))].
Definition ondn_facts4 : facts := mkFacts [(34%nat, mkAF 0 255 0)] [] [].
Definition ss_dn4 : sstate := mkSS ONDN_C3 sr_atoms [ondn_R_sl4; ondn_R_fsh; ondn_R_fcmd] None ondn_facts4.

(* A state with no region, at any pc of the listing (the `bne` at +0x3e8 is split from it). *)
Definition ss_dn_nil (pc : Z) : sstate := mkSS pc sr_atoms [] None (mkFacts [] [] []).

(* No run of this piece carries a shadow token: the span is empty. *)
Definition ONDN_B0 : Z * Z := (0, 0).
Definition ONDN_BX : sv := SLit 0.

(* The bytes each run may change: run 1 the notice's shadow bytes and its first 24 bytes; run 2 its bytes 24 .. 48
   and the spills at s1 + 32, s1 + 40; the memset the notice's bytes 44 .. 72 and the ESTACK bytes below s1; run 3
   the spills at s1 + 0, s1 + 8. *)
Definition ondn_Z1 (F : Z) (x : Z) : Prop :=
  (SHADOW_OFF + F / 8 + 14 <= x < SHADOW_OFF + F / 8 + 23) \/ (F + 112 <= x < F + 136).
Definition ondn_Z2 (F sp1 : Z) (x : Z) : Prop := (F + 136 <= x < F + 160) \/ (sp1 + 32 <= x < sp1 + 48).
Definition ondn_Z3 (F sp1 : Z) (x : Z) : Prop := (F + 156 <= x < F + 184) \/ (sp1 - ESTACK <= x < sp1).
Definition ondn_Z4 (sp1 : Z) (x : Z) : Prop := sp1 <= x < sp1 + 16.
(* All of them: what this piece changes before the call of notice. *)
Definition ondn_ZA (F sp1 : Z) (x : Z) : Prop :=
  ondn_Z1 F x \/ ondn_Z2 F sp1 x \/ ondn_Z3 F sp1 x \/ ondn_Z4 sp1 x.

(* ------------------------------------------------------------------ *)
(* 2. Bytes, values and the model                                      *)
(* ------------------------------------------------------------------ *)

(* Two views equal at a byte read the same byte. *)
Lemma ondn_mbyte_of_aview : forall H (m m' : word -> option byte) a,
  aview tfibsegs H m' a = aview tfibsegs H m a ->
  YP09.mbyte tfibsegs (mrestrict H m') a = YP09.mbyte tfibsegs (mrestrict H m) a.
Proof.
intros H m m' a E. unfold aview in E.
destruct (YP09.mbyte tfibsegs (mrestrict H m') a) as [x|], (YP09.mbyte tfibsegs (mrestrict H m) a) as [y|];
  cbn [option_map] in E; [| discriminate E | discriminate E | reflexivity].
injection E as E. f_equal. apply bv_eq. exact E.
Qed.

(* A value in memory, carried to a memory whose view agrees on its bytes. *)
Lemma ondn_vm_keep : forall H (m m' : word -> option byte) a (n : nat) v,
  val_mem tfibsegs (mrestrict H m) a n v ->
  (forall x, a <= x < a + Z.of_nat n -> aview tfibsegs H m' x = aview tfibsegs H m x) ->
  val_mem tfibsegs (mrestrict H m') a n v.
Proof.
intros H m m' a n v HV HK j Hj. rewrite <- (HV j Hj). apply ondn_mbyte_of_aview. apply HK. lia.
Qed.

(* A chunk of w bytes of the value e reads the w low little-endian bytes of e. *)
Lemma ondn_chunk_val : forall E (H : word -> bool) (m : word -> option byte) bopt lo hi wlo whi cs off (w : N) e,
  region_ok tfibsegs E (mrestrict H m) (YP09.mkRegion bopt lo hi wlo whi cs) ->
  In (YP09.mkChunk off (YP09.CVal w e)) cs -> (Z.of_N w <= 8) ->
  val_mem tfibsegs (mrestrict H m) (base_val E bopt + off) (N.to_nat w)
    (bv_unsigned (sv_denot E e) mod 2 ^ (8 * Z.of_N w)).
Proof.
intros E H m bopt lo hi wlo whi cs off w e (_ & _ & _ & Hcs) Hin Hw.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hc. cbn [YP09.r_base] in Hc.
exact (val_of_chunk_any tfibsegs E _ _ off w e Hc Hw).
Qed.

(* A store of w bytes of a register holding v leaves v's low w bytes. *)
Lemma ondn_vm_w : forall (m : word -> option byte) a (w : N) v, Z.of_N w <= 8 ->
  val_mem tfibsegs m a (N.to_nat w) (bv_unsigned (Z_to_bv 64 v) mod 2 ^ (8 * Z.of_N w)) ->
  val_mem tfibsegs m a (N.to_nat w) v.
Proof.
intros m a w v Hw H.
assert (Hd : (2 ^ (8 * Z.of_N w) | 2 ^ 64)).
{ exists (2 ^ (64 - 8 * Z.of_N w)). rewrite <- Z.pow_add_r by lia. f_equal. lia. }
assert (E : (bv_unsigned (Z_to_bv 64 v) mod 2 ^ (8 * Z.of_N w)) mod 2 ^ (8 * Z.of_N w) = v mod 2 ^ (8 * Z.of_N w)).
{ rewrite Zmod_mod, Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  apply Z.mod_mod_divide; try exact Hd; try (apply Z.pow_nonzero; lia); try (apply Z.pow_pos_nonneg; lia). }
intros k Hk. rewrite (H k Hk). unfold YO0f.le_byte. rewrite N_nat_Z, E. reflexivity.
Qed.

(* The sign-extended 4-byte load of g_s's state is the model's S_state. *)
Lemma ondn_sext32 : forall E X, ew E 32 = Z_to_bv 64 (TW.u_at X (TW.OFF_g_s + 112) 4) ->
  sv_denot E (SExt true 32 (SOff 32 0)) = Z_to_bv 64 (TW.S_state X).
Proof.
intros E X H. pose proof (TWL.u_at_range X (TW.OFF_g_s + 112) 4) as R.
change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in R.
cbn [sv_denot]. rewrite H. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r.
rewrite LMem.sext_small, LMem.signed_of_extract by lia.
rewrite unsigned_lit_small by lia. reflexivity.
Qed.

Lemma ondn_state_at : forall X, TW.S_state X = bv_swrap 32 (TW.u_at X (TW.OFF_g_s + 112) 4).
Proof. intros X. reflexivity. Qed.

Lemma ondn_state_range : forall X, - 2 ^ 31 <= TW.S_state X < 2 ^ 31.
Proof.
intros X. rewrite ondn_state_at.
pose proof (bv_swrap_in_range 32 (TW.u_at X (TW.OFF_g_s + 112) 4) ltac:(discriminate)) as R.
change (bv_half_modulus 32) with (2 ^ 31) in R. lia.
Qed.

(* The 72 bytes of the desk notice at n = F + 112, as trans_ntc_at reads them: the stores of 1 (N_DESK), the state,
   8 zero bytes, fp, the announce pointer, the personality pointer, the mac offset and the memset's 28 zeros. *)
Definition ondn_bytes (st fpz ap pv off : Z) : list byte :=
  TW.put 4 1 ++ TW.put 4 st ++ TW.put 8 0 ++ TW.put 8 fpz ++ TW.put 8 ap ++ TW.put 8 pv ++ TW.put 4 off ++
  repeat (DSpec.b8 0) 28.

Lemma ondn_bytes_len : forall st fpz ap pv off, length (ondn_bytes st fpz ap pv off) = 72%nat.
Proof.
intros st fpz ap pv off. unfold ondn_bytes.
rewrite ?length_app, ?TWL.length_put, ?repeat_length. reflexivity.
Qed.

Lemma ondn_nb : forall (H : word -> bool) (m : word -> option byte) F st fpz ap pv off,
  val_mem tfibsegs (mrestrict H m) (F + 112) 4 1 ->
  val_mem tfibsegs (mrestrict H m) (F + 116) 4 st ->
  val_mem tfibsegs (mrestrict H m) (F + 120) 8 0 ->
  val_mem tfibsegs (mrestrict H m) (F + 128) 8 fpz ->
  val_mem tfibsegs (mrestrict H m) (F + 136) 8 ap ->
  val_mem tfibsegs (mrestrict H m) (F + 144) 8 pv ->
  val_mem tfibsegs (mrestrict H m) (F + 152) 4 off ->
  (forall a, F + 156 <= a < F + 184 -> aview tfibsegs H m a = Some 0) ->
  garr8 tfibsegs (mrestrict H m) (F + 112) (map DSpec.bz (ondn_bytes st fpz ap pv off)).
Proof.
intros H m F st fpz ap pv off V0 V4 V8 V16 V24 V32 V40 Z0.
unfold ondn_bytes. rewrite !map_app.
apply garr8_app. split; [exact (garr8_of_put _ _ _ 4 1 V0)|].
rewrite length_map, TWL.length_put. replace (F + 112 + Z.of_nat 4) with (F + 116) by lia.
apply garr8_app. split; [exact (garr8_of_put _ _ _ 4 st V4)|].
rewrite length_map, TWL.length_put. replace (F + 116 + Z.of_nat 4) with (F + 120) by lia.
apply garr8_app. split; [exact (garr8_of_put _ _ _ 8 0 V8)|].
rewrite length_map, TWL.length_put. replace (F + 120 + Z.of_nat 8) with (F + 128) by lia.
apply garr8_app. split; [exact (garr8_of_put _ _ _ 8 fpz V16)|].
rewrite length_map, TWL.length_put. replace (F + 128 + Z.of_nat 8) with (F + 136) by lia.
apply garr8_app. split; [exact (garr8_of_put _ _ _ 8 ap V24)|].
rewrite length_map, TWL.length_put. replace (F + 136 + Z.of_nat 8) with (F + 144) by lia.
apply garr8_app. split; [exact (garr8_of_put _ _ _ 8 pv V32)|].
rewrite length_map, TWL.length_put. replace (F + 144 + Z.of_nat 8) with (F + 152) by lia.
apply garr8_app. split; [exact (garr8_of_put _ _ _ 4 off V40)|].
rewrite length_map, TWL.length_put. replace (F + 152 + Z.of_nat 4) with (F + 156) by lia.
rewrite map_repeat. change (DSpec.bz (DSpec.b8 0)) with 0.
apply garr8_zeros. intros a Ha.
pose proof (Z0 a ltac:(lia)) as Za. unfold aview in Za.
destruct (YP09.mbyte tfibsegs (mrestrict H m) a) as [c|] eqn:Ec; [|discriminate Za].
cbn in Za. injection Za as Hb. f_equal. apply bv_eq. rewrite Hb. reflexivity.
Qed.

(* find_mac's answer is -1 or an index it scanned: it fits in 32 bits. *)
Lemma ondn_off_range : forall X b, - 2 ^ 31 <= onann_off X b < 2 ^ 31.
Proof.
assert (H : forall (u mc : list byte) k (i : Z), 0 <= i -> i + Z.of_nat k < 2 ^ 31 ->
  - 2 ^ 31 <= TSS.find_mac_loop u mc i k < 2 ^ 31).
{ intros u mc k. induction k as [|k IH]; intros i Hi Hk; cbn [TSS.find_mac_loop]; [lia|].
  match goal with |- context [if ?c then _ else _] => destruct c end; [lia|]. apply IH; lia. }
intros X b. unfold onann_off.
destruct (DSpec.fr_cmd b =? TS0.DIGINET_CMD_ANNOUNCE_SESSION); [|lia].
unfold TSS.find_mac_m. apply H; [lia | vm_compute; reflexivity].
Qed.

(* On the notice path the model's call_notify tests the notify pointer and notice answers. *)
Lemma ondn_model : forall (TF : option TI.tframe) (Bw b Bw' : list byte) (now : Z),
  onann_ign b = false ->
  TSS.on_announce_m timg_B TF Bw b now = Some (Bw', tt) ->
  exists B2,
    TW.S_notify (onann_w1 timg_B Bw b) = TI.ti_notice timg_B /\
    TC.notice_m timg_B TF (onann_w1 timg_B Bw b) (onann_dntc timg_B (onann_w1 timg_B Bw b) b) = Some (B2, tt) /\
    TSS.call_notify timg_B TF (onann_w1 timg_B Bw b) (onann_dntc timg_B (onann_w1 timg_B Bw b) b) = Some (B2, tt) /\
    (DSpec.fr_cmd b = TS0.DIGINET_CMD_ANNOUNCE -> onann_k_e0 timg_B TF B2 now = Some (Bw', tt)) /\
    (DSpec.fr_cmd b = TS0.DIGINET_CMD_ANNOUNCE_SESSION ->
       onann_k_e1 timg_B TF B2 (onann_off (onann_w1 timg_B Bw b) b) b = Some (Bw', tt)).
Proof.
intros TF Bw b Bw' now Hig Hm.
rewrite (onann_model_split timg_B TF Bw b now Hig) in Hm.
destruct (TSS.call_notify timg_B TF (onann_w1 timg_B Bw b) (onann_dntc timg_B (onann_w1 timg_B Bw b) b))
  as [[B2 u]|] eqn:HCN; [|discriminate Hm].
destruct u. exists B2.
assert (HNT : TW.S_notify (onann_w1 timg_B Bw b) = TI.ti_notice timg_B).
{ unfold TSS.call_notify in HCN.
  destruct (Z.eqb_spec (TW.S_notify (onann_w1 timg_B Bw b)) (TI.ti_notice timg_B)) as [E|E]; [exact E|discriminate HCN]. }
assert (HNM : TC.notice_m timg_B TF (onann_w1 timg_B Bw b) (onann_dntc timg_B (onann_w1 timg_B Bw b) b)
  = Some (B2, tt)).
{ rewrite <- HCN. unfold TSS.call_notify. rewrite HNT. rewrite Z.eqb_refl. reflexivity. }
split; [exact HNT|]. split; [exact HNM|]. split; [reflexivity|].
split.
- intros Hc. rewrite Hc, Z.eqb_refl in Hm. exact Hm.
- intros Hc. rewrite Hc in Hm.
  replace (TS0.DIGINET_CMD_ANNOUNCE_SESSION =? TS0.DIGINET_CMD_ANNOUNCE) with false in Hm by reflexivity.
  exact Hm.
Qed.

(* The desk notice's kind, and the fields the code stores. *)
Lemma ondn_kind : forall X b, TI.n_kind (onann_dntc timg_B X b) = TC.N_DESK.
Proof. intros X b. reflexivity. Qed.


(* A byte of the view, in val_mem's form. *)
Lemma ondn_vm1 : forall (H : word -> bool) (m : word -> option byte) a v,
  aview tfibsegs H m a = Some v -> val_mem tfibsegs (mrestrict H m) a 1 v.
Proof.
intros H m a v Hv k Hk. assert (k = 0%nat) by lia. subst k. cbn [Z.of_nat]. rewrite Z.add_0_r.
unfold aview in Hv. destruct (YP09.mbyte tfibsegs (mrestrict H m) a) as [c|] eqn:Ec; [|discriminate Hv].
cbn in Hv. injection Hv as Hb.
pose proof (bv_unsigned_in_range 8 c) as R. change (bv_modulus 8) with 256 in R.
f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. unfold YO0f.le_byte, bv_wrap. change (bv_modulus 8) with 256.
change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. change (2 ^ 8) with 256.
rewrite <- Hb. rewrite !(Z.mod_small (bv_unsigned c) 256 R). reflexivity.
Qed.

(* An 8-byte value in memory, read as a word. *)
Lemma ondn_rdword_of_val : forall (H : word -> bool) (m : word -> option byte) a v, 0 <= v < 2 ^ 64 ->
  val_mem tfibsegs (mrestrict H m) a 8 v -> rdword (aview tfibsegs H m) a = Some v.
Proof.
intros H m a v Hv HV.
assert (A : forall k : nat, (k < 8)%nat -> aview tfibsegs H m (a + Z.of_nat k) = Some (YO0f.le_byte v 8 k)).
{ intros k Hk. unfold aview. rewrite (HV k Hk). cbn [option_map]. f_equal.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
  unfold YO0f.le_byte. apply Z.mod_mod. lia. }
pose proof (A 0%nat ltac:(lia)) as H0. pose proof (A 1%nat ltac:(lia)) as H1.
pose proof (A 2%nat ltac:(lia)) as H2. pose proof (A 3%nat ltac:(lia)) as H3.
pose proof (A 4%nat ltac:(lia)) as H4. pose proof (A 5%nat ltac:(lia)) as H5.
pose proof (A 6%nat ltac:(lia)) as H6. pose proof (A 7%nat ltac:(lia)) as H7.
cbv [Z.of_nat Pos.of_succ_nat Pos.succ] in H0, H1, H2, H3, H4, H5, H6, H7. rewrite Z.add_0_r in H0.
unfold rdword. rewrite H0, H1, H2, H3, H4, H5, H6, H7. f_equal. apply le_bytes8. exact Hv.
Qed.

(* ------------------------------------------------------------------ *)
(* 3. The symbolic states hold of the machine states                   *)
(* ------------------------------------------------------------------ *)

Section ent. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

(* The valuations of the four runs: the 32 registers and the extra atoms each run reads. *)
Definition ondn_E1 (regs : bvmap 5 word) (X : list byte) : env :=
  Eimg (PI := PI_transportb) (Ereg regs [Z_to_bv 64 (TW.u_at X (TW.OFF_g_s + 112) 4)]).
Definition ondn_E2 (regs : bvmap 5 word) : env := Eimg (PI := PI_transportb) (Ereg regs []).
Definition ondn_E3 (regs : bvmap 5 word) (X : list byte) : env :=
  Eimg (PI := PI_transportb) (Ereg regs [Z_to_bv 64 (TW.u_at X (TW.OFF_g_s + 104) 8)]).
Definition ondn_E4 (regs : bvmap 5 word) (fp cmd : Z) : env :=
  Eimg (PI := PI_transportb)
    (Ereg regs [Z_to_bv 64 (SHADOW_OFF + (fp + 30) / 8); Z_to_bv 64 (fp + 30); Z_to_bv 64 cmd]).

Lemma ondn_ew1 : forall regs X n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (ondn_E1 regs X) n = YK11.getr regs r.
Proof. intros regs X n r Hn. unfold ondn_E1. apply can_ew_Eimg_Ereg_nat. exact Hn. Qed.
Lemma ondn_ew2 : forall regs n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (ondn_E2 regs) n = YK11.getr regs r.
Proof. intros regs n r Hn. unfold ondn_E2. apply can_ew_Eimg_Ereg_nat. exact Hn. Qed.
Lemma ondn_ew3 : forall regs X n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (ondn_E3 regs X) n = YK11.getr regs r.
Proof. intros regs X n r Hn. unfold ondn_E3. apply can_ew_Eimg_Ereg_nat. exact Hn. Qed.
Lemma ondn_ew4 : forall regs fp cmd n (r : bv 5), Z.of_nat n = bv_unsigned r ->
  ew (ondn_E4 regs fp cmd) n = YK11.getr regs r.
Proof. intros regs fp cmd n r Hn. unfold ondn_E4. apply can_ew_Eimg_Ereg_nat. exact Hn. Qed.

Lemma ondn_ew1_32 : forall regs X, ew (ondn_E1 regs X) 32 = Z_to_bv 64 (TW.u_at X (TW.OFF_g_s + 112) 4).
Proof.
intros regs X. unfold ondn_E1. rewrite Eimg_low by (unfold A_TEXT; lia).
exact (ew_Ereg_extra regs [Z_to_bv 64 (TW.u_at X (TW.OFF_g_s + 112) 4)] 0).
Qed.
Lemma ondn_ew3_32 : forall regs X, ew (ondn_E3 regs X) 32 = Z_to_bv 64 (TW.u_at X (TW.OFF_g_s + 104) 8).
Proof.
intros regs X. unfold ondn_E3. rewrite Eimg_low by (unfold A_TEXT; lia).
exact (ew_Ereg_extra regs [Z_to_bv 64 (TW.u_at X (TW.OFF_g_s + 104) 8)] 0).
Qed.
Lemma ondn_ew4_x : forall regs fp cmd j, (j < 3)%nat ->
  ew (ondn_E4 regs fp cmd) (32 + j) =
  nth j [Z_to_bv 64 (SHADOW_OFF + (fp + 30) / 8); Z_to_bv 64 (fp + 30); Z_to_bv 64 cmd] (Z_to_bv 64 0).
Proof.
intros regs fp cmd j Hj. unfold ondn_E4. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra.
Qed.

(* The denotation of an atom whose value is known. *)
Lemma ondn_den : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n 0) = Z_to_bv 64 v.
Proof.
intros E n v Hn Hv. cbn [sv_denot]. rewrite Hn, unsigned_lit_small, Z.add_0_r by exact Hv. reflexivity.
Qed.

(* g_s's shadow bytes are 0 at every AR state. *)
Lemma ondn_gshadow : forall ly S (W : world segs) mem md T,
  trans_onann_cells B -> @AR rc segs B ly S W mem md ->
  T mod 8 = 0 -> ONANN_S <= T -> T + 8 <= ONANN_S + TW.SZ_g_s ->
  aview segs (w_H W) mem (SHADOW_OFF + T / 8) = Some 0.
Proof.
intros ly S W mem md T HSC HAR HT Hlo Hhi.
pose proof (decode_zshadow_rd B ly S W mem md ONANN_S (ONANN_S + TW.SZ_g_s) T HAR HT Hlo Hhi HSC) as H.
replace (SHADOW_OFF + T / 8) with (FCells.shadow_addr T); [exact H|].
unfold FCells.shadow_addr, FCells.ASAN_K, SHADOW_OFF. lia.
Qed.

(* run 1 at +0x300: the frame's shadow band, the notice's first 24 bytes, the checked load of g_s.state. *)
Lemma ondn_entry1 : forall ly S (W : world segs) regs mem md X F,
  trans_onann_cells B -> @AR rc segs B ly S W mem md ->
  tw_at TMAP_B (aview segs (w_H W) mem) X ->
  YK11.getr regs 18 = w64 (SHADOW_OFF + F / 8) -> YK11.getr regs 19 = w64 F ->
  YK11.getr regs 20 = w64 ONANN_S -> YK11.getr regs 24 = w64 SHADOW_OFF -> YK11.getr regs 11 = w64 1 ->
  4096 <= F -> F mod 64 = 0 -> F + 512 <= 2 ^ 47 ->
  (F + 512 <= SHADOW_OFF \/ SHADOW_OFF + 2 ^ 44 <= F) ->
  (F + 512 <= ONANN_S \/ ONANN_S + TW.SZ_g_s <= F) ->
  (forall a, F + 112 <= a < F + 136 -> apresent (w_H W) mem a) ->
  (forall i, 14 <= i < 23 -> apresent (w_H W) mem (SHADOW_OFF + F / 8 + i)) ->
  st_ok_pi segs VAL (ondn_E1 regs X) ss_dn1
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + ONANN_DN)) mem (YK11.seg_rom segs))).
Proof.
intros ly S W regs mem md X F HSC HAR Htw R18 R19 R20 R24 R11 HF0 HF64 HFc HSHF HFG Hpf Hpsh.
assert (CS : ONANN_S = 6157888) by reflexivity.
pose proof (Z.div_mod F 64 ltac:(lia)) as DF. rewrite HF64, Z.add_0_r in DF.
assert (HF8 : F / 8 = 8 * (F / 64))
  by (rewrite DF at 1; replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by ring; apply Z.div_mul; lia).
assert (HQ : 64 <= F / 64 /\ F / 64 <= 2 ^ 41) by (split; lia).
set (E := ondn_E1 regs X) in *.
assert (U18 : bv_unsigned (ew E 18) = SHADOW_OFF + F / 8)
  by (unfold E; rewrite (ondn_ew1 regs X 18 18%bv eq_refl), R18; unfold w64; apply unsigned_lit_small;
      unfold SHADOW_OFF; lia).
assert (U19 : bv_unsigned (ew E 19) = F)
  by (unfold E; rewrite (ondn_ew1 regs X 19 19%bv eq_refl), R19; unfold w64; apply unsigned_lit_small; lia).
pose proof (TWL.u_at_range X (TW.OFF_g_s + 112) 4) as R32.
change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in R32.
assert (U32 : bv_unsigned (ew E 32) = TW.u_at X (TW.OFF_g_s + 112) 4)
  by (unfold E; rewrite ondn_ew1_32; apply unsigned_lit_small; lia).
assert (Hs : aview segs (w_H W) mem ONDN_SH112 = Some 0).
{ replace ONDN_SH112 with (SHADOW_OFF + (ONANN_S + 112) / 8) by reflexivity.
  exact (ondn_gshadow ly S W mem md (ONANN_S + 112) HSC HAR ltac:(rewrite CS; reflexivity) ltac:(lia)
    ltac:(unfold TW.SZ_g_s; lia)). }
rewrite restrict_mkst_fx.
assert (H0 : st_ok_pi segs VAL E
  (mkSS ONANN_DN sr_atoms [ondn_R_sh; ondn_R_n1; ondn_R_gsh1; ondn_R_gst1] None ondn_facts1)
  (@YK11.mkst fx regs (Z_to_bv 64 (BASE + ONANN_DN)) (mrestrict (w_H W) mem) (YK11.seg_rom segs))).
{ apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks ondn_R_sh ondn_R_n1 ondn_R_gsh1
        ondn_R_gst1 base_val]; rewrite ?U18, ?U19.
    + split; [unfold SHADOW_OFF; lia|]. split; [unfold SHADOW_OFF; lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Hpsh. lia.
    + split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Hpf. lia.
    + split; [unfold ONDN_SH112; lia|]. split; [unfold ONDN_SH112; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val segs E _ 0 ONDN_SH112 1 (SLit 0) 0); [reflexivity | lia | lia |].
      rewrite Z.add_0_l. exact (ondn_vm1 _ _ _ _ Hs).
    + split; [rewrite CS; lia|]. split; [rewrite CS; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val segs E _ 0 (ONANN_S + 112) 4 (SOff 32 0) (TW.u_at X (TW.OFF_g_s + 112) 4));
        [apply ondn_den; [unfold E; apply ondn_ew1_32 | lia] | exact R32 | lia |].
      replace (0 + (ONANN_S + 112)) with (TB_g_s + 112) by (rewrite CS; reflexivity).
      exact (tw_read_val segs _ TMAP_B X TW.OFF_g_s TB_g_s TW.SZ_g_s 112 4 TMAP_B_ok Htw TMAP_B_g_s
        ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
  - apply pairwise_disjoint_of_extents.
    unfold extent_of_region, ondn_R_sh, ondn_R_n1, ondn_R_gsh1, ondn_R_gst1.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U18, U19.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold ONDN_SH112, SHADOW_OFF, TW.SZ_g_s in *. rewrite CS in HFG.
    repeat split; first [exact I | destruct HSHF; destruct HFG; lia].
  - unfold ondn_facts1, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U18, U19.
    change (2 ^ 6) with 64. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; unfold SHADOW_OFF; lia. }
assert (R20' : YK11.getr regs (Z_to_bv 5 20) = Z_to_bv 64 ONANN_S) by exact R20.
assert (R24' : YK11.getr regs (Z_to_bv 5 24) = Z_to_bv 64 SHADOW_OFF) by exact R24.
assert (R11' : YK11.getr regs (Z_to_bv 5 11) = Z_to_bv 64 1) by exact R11.
pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 20) ONANN_S H0 R20' eq_refl) as H1.
pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 24) SHADOW_OFF H1 R24' eq_refl) as H2.
pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 11) 1 H2 R11' eq_refl) as H3.
exact H3.
Qed.

(* run 2 at +0x364: the frame's shadow byte 17 (0), the notice's bytes 24 .. 48, the two spills. *)
Lemma ondn_entry2 : forall (W : world segs) regs mem F sp1,
  YK11.getr regs 12 = w64 (SHADOW_OFF + F / 8 + 17) -> YK11.getr regs 21 = w64 (F + 112) ->
  YK11.getr regs 9 = w64 sp1 ->
  YK11.getr regs 20 = w64 ONANN_S -> YK11.getr regs 13 = w64 (ONANN_S + 112) ->
  YK11.getr regs 14 = w64 ONDN_SH112 ->
  aview segs (w_H W) mem (SHADOW_OFF + F / 8 + 17) = Some 0 ->
  4096 <= F -> F mod 64 = 0 -> F + 512 <= 2 ^ 47 ->
  (F + 512 <= SHADOW_OFF \/ SHADOW_OFF + 2 ^ 44 <= F) ->
  F + 512 <= sp1 -> 2 ^ 46 <= sp1 -> sp1 + 64 <= 2 ^ 47 -> sp1 mod 32 = 0 ->
  (forall a, F + 136 <= a < F + 160 -> apresent (w_H W) mem a) ->
  (forall a, sp1 + 32 <= a < sp1 + 48 -> apresent (w_H W) mem a) ->
  st_ok_pi segs VAL (ondn_E2 regs) ss_dn2
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + ONDN_C1)) mem (YK11.seg_rom segs))).
Proof.
intros W regs mem F sp1 R12 R21 R9 R20 R13 R14 Hs HF0 HF64 HFc HSHF HFsp Hsp Hsp2 Hsp32 Hpf Hpsl.
pose proof (Z.div_mod F 64 ltac:(lia)) as DF. rewrite HF64, Z.add_0_r in DF.
assert (HF8 : F / 8 = 8 * (F / 64))
  by (rewrite DF at 1; replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by ring; apply Z.div_mul; lia).
set (E := ondn_E2 regs) in *.
assert (U12 : bv_unsigned (ew E 12) = SHADOW_OFF + F / 8 + 17)
  by (unfold E; rewrite (ondn_ew2 regs 12 12%bv eq_refl), R12; unfold w64; apply unsigned_lit_small;
      unfold SHADOW_OFF; lia).
assert (U21 : bv_unsigned (ew E 21) = F + 112)
  by (unfold E; rewrite (ondn_ew2 regs 21 21%bv eq_refl), R21; unfold w64; apply unsigned_lit_small; lia).
assert (U9 : bv_unsigned (ew E 9) = sp1)
  by (unfold E; rewrite (ondn_ew2 regs 9 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx.
assert (H0 : st_ok_pi segs VAL E (mkSS ONDN_C1 sr_atoms [ondn_R_shb; ondn_R_n2; ondn_R_sl2] None ondn_facts2)
  (@YK11.mkst fx regs (Z_to_bv 64 (BASE + ONDN_C1)) (mrestrict (w_H W) mem) (YK11.seg_rom segs))).
{ apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks ondn_R_shb ondn_R_n2 ondn_R_sl2
        base_val]; rewrite ?U12, ?U21, ?U9.
    + split; [unfold SHADOW_OFF; lia|]. split; [unfold SHADOW_OFF; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val segs E _ (SHADOW_OFF + F / 8 + 17) 0 1 (SLit 0) 0); [reflexivity | lia | lia |].
      rewrite Z.add_0_r. exact (ondn_vm1 _ _ _ _ Hs).
    + split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Hpf. lia.
    + split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Hpsl. lia.
  - apply pairwise_disjoint_of_extents.
    unfold extent_of_region, ondn_R_shb, ondn_R_n2, ondn_R_sl2.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U12, U21, U9.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold SHADOW_OFF in *.
    repeat split; first [exact I | destruct HSHF; lia].
  - unfold ondn_facts2, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U9, U21.
    change (2 ^ 5) with 32. change (2 ^ 4) with 16.
    assert (M21 : (F + 112) mod 16 = 0)
      by (rewrite DF; replace (64 * (F / 64) + 112) with ((4 * (F / 64) + 7) * 16) by ring; apply Z.mod_mul; lia).
    repeat match goal with |- _ /\ _ => split end; try exact I; try lia. }
assert (R20' : YK11.getr regs (Z_to_bv 5 20) = Z_to_bv 64 ONANN_S) by exact R20.
assert (R13' : YK11.getr regs (Z_to_bv 5 13) = Z_to_bv 64 (ONANN_S + 112)) by exact R13.
assert (R14' : YK11.getr regs (Z_to_bv 5 14) = Z_to_bv 64 ONDN_SH112) by exact R14.
pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 20) ONANN_S H0 R20' eq_refl) as H1.
pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 13) (ONANN_S + 112) H1 R13' eq_refl) as H2.
pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 14) ONDN_SH112 H2 R14' eq_refl) as H3.
exact H3.
Qed.

(* run 3 at +0x394: the checks and the loads of g_s.notify and g_s.notify_ctx, and the two spills. *)
Lemma ondn_entry3 : forall ly S (W : world segs) regs mem md X sp1,
  trans_onann_cells B -> @AR rc segs B ly S W mem md ->
  tw_at TMAP_B (aview segs (w_H W) mem) X -> TW.S_notify X = TI.ti_notice timg_B ->
  YK11.getr regs 9 = w64 sp1 -> YK11.getr regs 20 = w64 ONANN_S -> YK11.getr regs 24 = w64 SHADOW_OFF ->
  YK11.getr regs 26 = w64 (ONANN_S + 96) ->
  2 ^ 46 <= sp1 -> sp1 + 64 <= 2 ^ 47 -> sp1 mod 32 = 0 ->
  (forall a, sp1 <= a < sp1 + 16 -> apresent (w_H W) mem a) ->
  st_ok_pi segs VAL (ondn_E3 regs X) ss_dn3
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + ONDN_C2)) mem (YK11.seg_rom segs))).
Proof.
intros ly S W regs mem md X sp1 HSC HAR Htw HNT R9 R20 R24 R26 Hsp Hsp2 Hsp32 Hpsl.
assert (CS : ONANN_S = 6157888) by reflexivity.
set (E := ondn_E3 regs X) in *.
assert (HEI : img_env VAL A_LIM E) by (unfold E, ondn_E3; apply Eimg_env).
assert (U9 : bv_unsigned (ew E 9) = sp1)
  by (unfold E; rewrite (ondn_ew3 regs X 9 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
pose proof (TWL.u_at_range X (TW.OFF_g_s + 104) 8) as R34.
change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in R34.
assert (EUN : TW.u_at X (TW.OFF_g_s + 96) 8 = BASE + AF_notice).
{ change (TW.S_notify X = BASE + AF_notice). rewrite HNT. reflexivity. }
assert (EBN : BASE + AF_notice = 0x8341c) by reflexivity.
assert (Hs96 : aview segs (w_H W) mem ONDN_SH96 = Some 0).
{ replace ONDN_SH96 with (SHADOW_OFF + (ONANN_S + 96) / 8) by reflexivity.
  exact (ondn_gshadow ly S W mem md (ONANN_S + 96) HSC HAR ltac:(rewrite CS; reflexivity) ltac:(lia)
    ltac:(unfold TW.SZ_g_s; lia)). }
assert (Hs104 : aview segs (w_H W) mem ONDN_SH104 = Some 0).
{ replace ONDN_SH104 with (SHADOW_OFF + (ONANN_S + 104) / 8) by reflexivity.
  exact (ondn_gshadow ly S W mem md (ONANN_S + 104) HSC HAR ltac:(rewrite CS; reflexivity) ltac:(lia)
    ltac:(unfold TW.SZ_g_s; lia)). }
rewrite restrict_mkst_fx.
assert (H0 : st_ok_pi segs VAL E (mkSS ONDN_C2 sr_atoms [ondn_R_gsh3; ondn_R_gs3; ondn_R_sl3] None ondn_facts3)
  (@YK11.mkst fx regs (Z_to_bv 64 (BASE + ONDN_C2)) (mrestrict (w_H W) mem) (YK11.seg_rom segs))).
{ apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks ondn_R_gsh3 ondn_R_gs3 ondn_R_sl3
        base_val]; rewrite ?U9.
    + split; [unfold ONDN_SH96; lia|]. split; [unfold ONDN_SH96, ONDN_SH104; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      * apply (chunk_ok_val segs E _ 0 ONDN_SH96 1 (SLit 0) 0); [reflexivity | lia | lia |].
        rewrite Z.add_0_l. exact (ondn_vm1 _ _ _ _ Hs96).
      * apply (chunk_ok_val segs E _ 0 ONDN_SH104 1 (SLit 0) 0); [reflexivity | lia | lia |].
        rewrite Z.add_0_l. exact (ondn_vm1 _ _ _ _ Hs104).
    + split; [rewrite CS; lia|]. split; [rewrite CS; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      * apply (chunk_ok_val segs E _ 0 (ONANN_S + 96) 8 (SOff A_TEXT AF_notice) (BASE + AF_notice));
          [apply codeptr_val; exact HEI | rewrite EBN; lia | lia |].
        replace (0 + (ONANN_S + 96)) with (TB_g_s + 96) by (rewrite CS; reflexivity). rewrite <- EUN.
        exact (tw_read_val segs _ TMAP_B X TW.OFF_g_s TB_g_s TW.SZ_g_s 96 8 TMAP_B_ok Htw TMAP_B_g_s
          ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
      * apply (chunk_ok_val segs E _ 0 (ONANN_S + 104) 8 (SOff 32 0) (TW.u_at X (TW.OFF_g_s + 104) 8));
          [apply ondn_den; [unfold E; apply ondn_ew3_32 | exact R34] | exact R34 | lia |].
        replace (0 + (ONANN_S + 104)) with (TB_g_s + 104) by (rewrite CS; reflexivity).
        exact (tw_read_val segs _ TMAP_B X TW.OFF_g_s TB_g_s TW.SZ_g_s 104 8 TMAP_B_ok Htw TMAP_B_g_s
          ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
    + split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Hpsl. lia.
  - apply pairwise_disjoint_of_extents.
    unfold extent_of_region, ondn_R_gsh3, ondn_R_gs3, ondn_R_sl3.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold ONDN_SH96, ONDN_SH104 in *. rewrite CS.
    repeat split; first [exact I | lia].
  - unfold ondn_facts3, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U9. change (2 ^ 5) with 32.
    repeat match goal with |- _ /\ _ => split end; try exact I; lia. }
assert (R20' : YK11.getr regs (Z_to_bv 5 20) = Z_to_bv 64 ONANN_S) by exact R20.
assert (R24' : YK11.getr regs (Z_to_bv 5 24) = Z_to_bv 64 SHADOW_OFF) by exact R24.
assert (R26' : YK11.getr regs (Z_to_bv 5 26) = Z_to_bv 64 (ONANN_S + 96)) by exact R26.
pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 20) ONANN_S H0 R20' eq_refl) as H1.
pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 24) SHADOW_OFF H1 R24' eq_refl) as H2.
pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 26) (ONANN_S + 96) H2 R26' eq_refl) as H3.
exact H3.
Qed.

(* run 4 at +0x3d0: the two spills of f + 30, that shadow byte and the command byte. *)
Lemma ondn_entry4 : forall (W : world segs) regs mem sp1 fp cmd,
  YK11.getr regs 9 = w64 sp1 ->
  val_mem segs (mrestrict (w_H W) mem) (sp1 + 48) 8 (SHADOW_OFF + (fp + 30) / 8) ->
  val_mem segs (mrestrict (w_H W) mem) (sp1 + 56) 8 (fp + 30) ->
  aview segs (w_H W) mem (SHADOW_OFF + (fp + 30) / 8) = Some 0 ->
  aview segs (w_H W) mem (fp + 30) = Some cmd -> 0 <= cmd < 256 ->
  4096 <= fp -> fp + 64 <= 2 ^ 47 ->
  (fp + 64 <= SHADOW_OFF \/ SHADOW_OFF + 2 ^ 44 <= fp) ->
  fp + 64 <= sp1 -> 2 ^ 46 <= sp1 -> sp1 + 64 <= 2 ^ 47 ->
  st_ok_pi segs VAL (ondn_E4 regs fp cmd) ss_dn4
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + ONDN_C3)) mem (YK11.seg_rom segs))).
Proof.
intros W regs mem sp1 fp cmd R9 V48 V56 Hsh Hcm Hcr Hfp0 Hfpc HSHF Hfpsp Hsp Hsp2.
assert (HD : 0 <= (fp + 30) / 8 /\ (fp + 30) / 8 <= 2 ^ 44)
  by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
set (E := ondn_E4 regs fp cmd) in *.
assert (U9 : bv_unsigned (ew E 9) = sp1)
  by (unfold E; rewrite (ondn_ew4 regs fp cmd 9 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = SHADOW_OFF + (fp + 30) / 8).
{ unfold E. change (32%nat) with (32 + 0)%nat. rewrite (ondn_ew4_x regs fp cmd 0 ltac:(lia)). cbn [nth].
  apply unsigned_lit_small. unfold SHADOW_OFF. lia. }
assert (U33 : bv_unsigned (ew E 33) = fp + 30).
{ unfold E. change (33%nat) with (32 + 1)%nat. rewrite (ondn_ew4_x regs fp cmd 1 ltac:(lia)). cbn [nth].
  apply unsigned_lit_small. lia. }
assert (U34 : bv_unsigned (ew E 34) = cmd).
{ unfold E. change (34%nat) with (32 + 2)%nat. rewrite (ondn_ew4_x regs fp cmd 2 ltac:(lia)). cbn [nth].
  apply unsigned_lit_small. lia. }
assert (W32 : ew E 32 = Z_to_bv 64 (SHADOW_OFF + (fp + 30) / 8)).
{ unfold E. change (32%nat) with (32 + 0)%nat. rewrite (ondn_ew4_x regs fp cmd 0 ltac:(lia)). reflexivity. }
assert (W33 : ew E 33 = Z_to_bv 64 (fp + 30)).
{ unfold E. change (33%nat) with (32 + 1)%nat. rewrite (ondn_ew4_x regs fp cmd 1 ltac:(lia)). reflexivity. }
assert (W34 : ew E 34 = Z_to_bv 64 cmd).
{ unfold E. change (34%nat) with (32 + 2)%nat. rewrite (ondn_ew4_x regs fp cmd 2 ltac:(lia)). reflexivity. }
rewrite restrict_mkst_fx.
apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks ondn_R_sl4 ondn_R_fsh ondn_R_fcmd
      base_val]; rewrite ?U9, ?U32, ?U33.
  + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    * apply (chunk_ok_val segs E _ sp1 48 8 (SOff 32 0) (SHADOW_OFF + (fp + 30) / 8));
        [apply ondn_den; [exact W32 | unfold SHADOW_OFF; lia] | unfold SHADOW_OFF; lia | lia |].
      exact V48.
    * apply (chunk_ok_val segs E _ sp1 56 8 (SOff 33 0) (fp + 30));
        [apply ondn_den; [exact W33 | lia] | lia | lia |].
      exact V56.
  + split; [unfold SHADOW_OFF; lia|]. split; [unfold SHADOW_OFF; lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val segs E _ (SHADOW_OFF + (fp + 30) / 8) 0 1 (SLit 0) 0); [reflexivity | lia | lia |].
    rewrite Z.add_0_r. exact (ondn_vm1 _ _ _ _ Hsh).
  + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val segs E _ (fp + 30) 0 1 (SOff 34 0) cmd);
      [apply ondn_den; [exact W34 | lia] | lia | lia |].
    rewrite Z.add_0_r. exact (ondn_vm1 _ _ _ _ Hcm).
- apply pairwise_disjoint_of_extents.
  unfold extent_of_region, ondn_R_sl4, ondn_R_fsh, ondn_R_fcmd.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U32, U33.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold SHADOW_OFF in *.
  repeat split; first [exact I | destruct HSHF; lia].
- unfold ondn_facts4, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U34. rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 4. The notice at n = F + 112, as notice's statement reads it        *)
(* ------------------------------------------------------------------ *)

Lemma ondn_ntc_at : forall ly2 S2 (W : world segs) memN mdN (regsC : bvmap 5 word) (X b : list byte) F pos
    fpz st off,
  AR_laws segs B -> @AR rc segs B ly2 S2 W memN mdN -> In (ONANN_CID, pos) (frames S2) ->
  F = frame_addr ly2 ONANN_CID pos -> 4096 <= F -> F mod 64 = 0 -> F + 512 <= alloc_ceiling -> in_app F 512 ->
  F + 512 <= spZ regsC - NOTICE_STK -> 0 <= spZ regsC - NOTICE_STK ->
  (forall a, F <= a < F + 512 -> apresent (w_H W) memN a) ->
  (forall i, 0 <= i < 64 -> apresent (w_H W) memN (SHADOW_OFF + F / 8 + i)) ->
  (forall i, 14 <= i < 23 -> aview segs (w_H W) memN (SHADOW_OFF + F / 8 + i) = Some 0) ->
  (forall i, 4 <= i < 9 -> aview segs (w_H W) memN (SHADOW_OFF + F / 8 + i) = Some 0) ->
  st = TW.S_state X -> off = onann_off X b ->
  0 <= fpz < 2 ^ 64 ->
  garr8 segs (mrestrict (w_H W) memN) (F + 112) (map DSpec.bz (ondn_bytes st fpz (F + ONANN_A) (onann_pv timg_B b) off)) ->
  garr8 segs (mrestrict (w_H W) memN) (F + ONANN_A) (map DSpec.bz (TSS.ann_field (skipn 15 (DSpec.fr_body b)))) ->
  garr8 segs (mrestrict (w_H W) memN) (F + ONANN_A + 10)
    (map DSpec.bz (TSS.ann_field (skipn 24 (DSpec.fr_body b)))) ->
  0 <= onann_pv timg_B b < 2 ^ 64 ->
  trans_ntc_at B ly2 S2 W memN regsC NOTICE_STK (F + 112) (onann_dntc timg_B X b).
Proof.
intros ly2 S2 W memN mdN regsC X b F pos fpz st off LAWS HAR Hin EF HF0 HF64 HFc HFapp Hwin Hwin0 HFb HFsh
  ZS ZA Est Eoff Hfpz HNB HV HN Hpv.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (DFm8 : F mod 8 = 0).
{ pose proof (Z.div_mod F 64 ltac:(lia)) as D. rewrite HF64, Z.add_0_r in D. rewrite D.
  replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by ring. apply Z.mod_mul. lia. }
pose proof (ondn_state_range X) as Hstr.
pose proof (ondn_off_range X b) as Hoffr.
unfold trans_ntc_at.
split; [lia|]. split; [rewrite Z.add_mod, DFm8 by lia; reflexivity|].
split.
{ right. split.
  - left. exists ONANN_CID, pos. split; [exact Hin|]. rewrite <- EF.
    change (fs_frame_bytes ONANN_CID) with 512. unfold NTC_SIZE. lia.
  - unfold decode_rd_ok, NTC_SIZE. split; [|split; [|split; [|split; [|split]]]].
    + intros a Ha. apply can_aview_vis. apply HFb. lia.
    + apply (frame_ra_zero _ F (F + 112) 72 14 23); [lia | exact DFm8 | lia | lia |].
      intros i Hi. apply ZS. lia.
    + apply (frame_hull_vis _ F 512 (F + 112) 72); [lia | exact HF64 | reflexivity | lia | lia | lia |].
      intros i Hi. change (shadow_addr F + i) with (SHADOW_OFF + F / 8 + i).
      apply can_aview_vis. apply HFsh. change (512 / 8) with 64 in Hi. lia.
    + apply (amem_range_sub_app F 512); [exact HFapp | lia | lia | lia | lia].
    + lia.
    + lia. }
split; [left; unfold NTC_SIZE; lia|].
exists (ondn_bytes st fpz (F + ONANN_A) (onann_pv timg_B b) off).
split; [exact HNB|].
split; [exact (ondn_bytes_len _ _ _ _ _)|].
unfold onann_dntc, ondn_bytes, TW.s32_at, ONANN_A in *.
cbn [TI.n_kind TI.n_state TI.n_old TI.n_reason TI.n_pers TI.n_mac_offset TI.n_body_len TI.n_counter TI.n_retry
  TI.n_body TI.n_ann length].
assert (E24 : TW.u_at (TW.put 4 1 ++ TW.put 4 st ++ TW.put 8 0 ++ TW.put 8 fpz ++ TW.put 8 (F + 32) ++
  TW.put 8 (onann_pv timg_B b) ++ TW.put 4 off ++ repeat (DSpec.b8 0) 28) 24 8 = F + 32)
  by (WN.ntc_field; apply Z.mod_small; lia).
assert (E48 : TW.u_at (TW.put 4 1 ++ TW.put 4 st ++ TW.put 8 0 ++ TW.put 8 fpz ++ TW.put 8 (F + 32) ++
  TW.put 8 (onann_pv timg_B b) ++ TW.put 4 off ++ repeat (DSpec.b8 0) 28) 48 8 = 0) by WN.ntc_field.
rewrite E24, E48.
split; [WN.ntc_field; change (TS0.DIGINET_N_DESK) with 1; reflexivity|].
split; [WN.ntc_field; rewrite Est; apply WN.swrap32_mod; exact Hstr|].
split; [WN.ntc_field|].
split; [WN.ntc_field|].
split; [WN.ntc_field; apply Z.mod_small; exact Hpv|].
split; [WN.ntc_field; rewrite Eoff; apply WN.swrap32_mod; exact Hoffr|].
split; [WN.ntc_field|].
split; [WN.ntc_field|].
split; [WN.ntc_field|].
split; [apply garr8_nil|].
split; [exact (trans_src_ok_null B ly2 S2 W memN)|].
split; [left; lia|].
split; [lia|]. split; [rewrite Z.add_mod, DFm8 by lia; reflexivity|].
split; [exact HV|].
split; [exact HN|].
split.
- right. split.
  + left. exists ONANN_CID, pos. split; [exact Hin|]. rewrite <- EF.
    change (fs_frame_bytes ONANN_CID) with 512. unfold ANN_SIZE. lia.
  + unfold decode_rd_ok, ANN_SIZE. split; [|split; [|split; [|split; [|split]]]].
    * intros a Ha. apply can_aview_vis. apply HFb. lia.
    * apply (frame_ra_zero _ F (F + 32) 20 4 9); [lia | exact DFm8 | lia | lia |].
      intros i Hi. apply ZA. lia.
    * apply (frame_hull_vis _ F 512 (F + 32) 20); [lia | exact HF64 | reflexivity | lia | lia | lia |].
      intros i Hi. change (shadow_addr F + i) with (SHADOW_OFF + F / 8 + i).
      apply can_aview_vis. apply HFsh. change (512 / 8) with 64 in Hi. lia.
    * apply (amem_range_sub_app F 512); [exact HFapp | lia | lia | lia | lia].
    * lia.
    * lia.
- unfold ANN_SIZE. left. lia.
Qed.

(* A state with no region, at any pc of the listing (the `bne` at +0x3e8 is split from it). *)
Lemma ondn_entry0 : forall (W : world segs) regs mem pc,
  st_ok_pi segs VAL (ondn_E2 regs) (ss_dn_nil pc)
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + pc)) mem (YK11.seg_rom segs))).
Proof.
intros W regs mem pc. rewrite restrict_mkst_fx. unfold ss_dn_nil.
apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. exact I.
- unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. repeat split; exact I.
Qed.
End ent.

(* ------------------------------------------------------------------ *)
(* 5. G, and the readers of a symbolic state                           *)
(* ------------------------------------------------------------------ *)

Lemma ondn_inG : forall b0 n0 a, In (b0, n0) TG.G_HARNESS_B -> b0 <= a < b0 + n0 -> inG TG.G_HARNESS_B a.
Proof.
intros b0 n0 a Hin Ha. unfold inG. apply Exists_exists. exists (b0, n0).
split; [exact Hin | unfold in_zr; cbn [fst snd]; lia].
Qed.
Lemma ondn_inG_gs : forall a, ONANN_S <= a < ONANN_S + TW.SZ_g_s -> inG TG.G_HARNESS_B a.
Proof. intros a Ha. apply (ondn_inG _ _ a (TMAP_B_in_G _ _ _ TMAP_B_g_s)). unfold ONANN_S in Ha. lia. Qed.

(* The value of register r in the machine state of a symbolic state HS. *)
Ltac ondn_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | ?T => idtac "ondn_reg: no match for" T; fail
  end.
(* Register r of HS, whose symbolic value is the atom n, the start value of register rn (Q its value). *)
Ltac ondn_kreg_of HS Elo EE r n rn Q H :=
  lazymatch type of Q with _ = ?v =>
    ondn_reg HS r v H
      ltac:(cbn [sv_denot]; try rewrite (Elo n ltac:(lia)); rewrite (EE n rn eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
            exact Q) end.
Ltac ondn_kreg HS Elo EE r n Q H := ondn_kreg_of HS Elo EE r n r Q H.
(* Region i of a symbolic state. *)
Ltac ondn_region HS i HR :=
  lazymatch type of HS with
  | st_ok_pi ?sg ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let r0 := eval vm_compute in (nth i (ss_mem ssx) got_regionP) in
      assert (HR : region_ok sg Ex (ms_mem (restrict Hh msx)) r0)
        by (let HS' := fresh in pose proof HS as HS'; unfold st_ok_pi in HS';
            eapply (can_region_nth Ex _ (restrict Hh msx) i r0 HS'); vm_compute; reflexivity)
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?sg ?Ex ?ssx (restrict ?Hh ?msx) =>
      let r0 := eval vm_compute in (nth i (ss_mem ssx) got_regionP) in
      assert (HR : region_ok sg Ex (ms_mem (restrict Hh msx)) r0)
        by (apply (can_region_nth Ex ssx (restrict Hh msx) i r0 HS); vm_compute; reflexivity)
  end; cbn [ms_mem restrict] in HR.
Ltac ondn_in := cbn [In]; repeat (first [left; reflexivity | right]).
Ltac ondn_awr_rs :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp0 ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp0 b0 bc lyq ownq) end.
(* The windows of a run's start state, computed, against the bytes Zs the run may change. *)
Ltac ondn_win Hin Hx tac :=
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; tac |]);
  destruct Hin.
Ltac ondn_name_md md :=
  lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => set (md := m) in *; clearbody md end.
Ltac ondn_lo HS E0 Hlo m :=
  lazymatch type of HS with
  | st_ok_pi _ _ ?EF _ (restrict _ ?mf) =>
      assert (Hlo : forall n, (n < 1024)%nat -> ew EF n = ew E0 n)
        by (intros n Hn; rewrite ?ew_ewset_other by lia; reflexivity); rename mf into m
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok _ ?EF _ (restrict _ ?mf) =>
      assert (Hlo : forall n, (n < 1024)%nat -> ew EF n = ew E0 n)
        by (intros n Hn; rewrite ?ew_ewset_other by lia; reflexivity); rename mf into m
  end.

(* `addi a0, p, c`, `srli a2, a0, 3`, `add a2, a2, s8` with s8 a literal: the shadow address of p + c. *)
Lemma ondn_den_shadow_lit : forall E n v c,
  ew E n = Z_to_bv 64 v -> 0 <= v -> 0 <= c -> v + c < 2 ^ 47 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff n c) (SLit 3)) (SLit SHADOW_OFF))
    = Z_to_bv 64 (SHADOW_OFF + (v + c) / 8).
Proof.
intros E n v c Hn H0 Hc H47.
assert (HD : 0 <= (v + c) / 8 <= 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
assert (Un : U E (SOff n c) = v + c)
  by (rewrite U_SOff, Hn, (unsigned_lit_small v ltac:(lia)); apply zcanon_id; unfold M64; lia).
rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
rewrite Un, !U_SLit, (zcanon_id 3) by (unfold M64; lia).
change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
rewrite (zcanon_id ((v + c) / 8)) by (unfold M64; lia).
rewrite (zcanon_id SHADOW_OFF) by (unfold M64, SHADOW_OFF; lia).
rewrite (Z.add_comm ((v + c) / 8) SHADOW_OFF). apply zcanon_id. unfold M64, SHADOW_OFF. lia.
Qed.

(* (F + 136) / 8 = F / 8 + 17 and (F + 112) / 8 = F / 8 + 14 for a 64-aligned frame. *)
Lemma ondn_div8 : forall Fv c, Fv mod 64 = 0 -> 0 <= Fv -> 0 <= c -> c mod 8 = 0 ->
  (Fv + c) / 8 = Fv / 8 + c / 8.
Proof.
intros Fv c H64 H0 Hc Hc8.
pose proof (Z.div_mod Fv 64 ltac:(lia)) as D. rewrite H64, Z.add_0_r in D.
pose proof (Z.div_mod c 8 ltac:(lia)) as Dc. rewrite Hc8, Z.add_0_r in Dc.
assert (E1 : Fv / 8 = 8 * (Fv / 64))
  by (rewrite D at 1; replace (64 * (Fv / 64)) with ((8 * (Fv / 64)) * 8) by ring; apply Z.div_mul; lia).
assert (E2 : (Fv + c) / 8 = 8 * (Fv / 64) + c / 8).
{ rewrite D at 1. rewrite Dc at 1.
  replace (64 * (Fv / 64) + 8 * (c / 8)) with ((8 * (Fv / 64) + c / 8) * 8) by ring.
  apply Z.div_mul. lia. }
lia.
Qed.

(* Two byte lists of the same length that read as the bytes at one address are equal. *)
Lemma ondn_garr8_det : forall (H : word -> bool) (m : word -> option byte) p (l1 l2 : list byte),
  garr8 tfibsegs (mrestrict H m) p (map DSpec.bz l1) ->
  garr8 tfibsegs (mrestrict H m) p (map DSpec.bz l2) -> length l1 = length l2 -> l1 = l2.
Proof.
intros H m p l1 l2 G1 G2 HL.
apply (nth_ext l1 l2 (DSpec.b8 0) (DSpec.b8 0)); [exact HL|].
intros n Hn.
assert (E1 : nth n (map DSpec.bz l1) 0 = DSpec.bz (nth n l1 (DSpec.b8 0))).
{ rewrite (nth_indep (map DSpec.bz l1) 0 (DSpec.bz (DSpec.b8 0))) by (rewrite length_map; lia).
  apply map_nth. }
assert (E2 : nth n (map DSpec.bz l2) 0 = DSpec.bz (nth n l2 (DSpec.b8 0))).
{ rewrite (nth_indep (map DSpec.bz l2) 0 (DSpec.bz (DSpec.b8 0))) by (rewrite length_map; lia).
  apply map_nth. }
destruct (G1 n ltac:(rewrite length_map; lia)) as (V1 & R1).
destruct (G2 n ltac:(rewrite length_map; lia)) as (V2 & R2).
rewrite E1 in V1, R1. rewrite E2 in V2, R2.
pose proof (V1 0%nat ltac:(lia)) as M1. pose proof (V2 0%nat ltac:(lia)) as M2.
cbn [Z.of_nat] in M1, M2. rewrite Z.add_0_r in M1, M2.
assert (EQ : Z_to_bv 8 (YO0f.le_byte (DSpec.bz (nth n l1 (DSpec.b8 0))) 1 0)
           = Z_to_bv 8 (YO0f.le_byte (DSpec.bz (nth n l2 (DSpec.b8 0))) 1 0)).
{ rewrite M1 in M2. exact (f_equal (fun o => match o with Some x => x | None => Z_to_bv 8 0 end) M2). }
apply bv_eq.
apply (f_equal (@bv_unsigned 8)) in EQ. rewrite !Z_to_bv_unsigned in EQ.
unfold bv_wrap in EQ. change (bv_modulus 8) with 256 in EQ.
unfold YO0f.le_byte in EQ.
change (8 * Z.of_nat 1) with 8 in EQ. change (8 * Z.of_nat 0) with 0 in EQ.
rewrite !Z.shiftr_0_r, !Zmod_mod in EQ. change (2 ^ 8) with 256 in EQ.
rewrite !(Z.mod_small _ 256) in EQ by (unfold DSpec.bz in R1, R2 |- *; lia).
exact EQ.
Qed.

(* The announce pointer and the body pointer of the 72 bytes. *)
Lemma ondn_bytes_ann : forall st fpz ap pv off, 0 <= ap < 2 ^ 64 ->
  TW.u_at (ondn_bytes st fpz ap pv off) 24 8 = ap.
Proof. intros st fpz ap pv off Hap. unfold ondn_bytes. WN.ntc_field. apply Z.mod_small. exact Hap. Qed.
Lemma ondn_bytes_body : forall st fpz ap pv off, TW.u_at (ondn_bytes st fpz ap pv off) 48 8 = 0.
Proof. intros st fpz ap pv off. unfold ondn_bytes. WN.ntc_field. Qed.
(* An atom whose 64-bit value is known. *)
Lemma ondn_den_reg : forall E n v, ew E n = Z_to_bv 64 v -> sv_denot E (SOff n 0) = Z_to_bv 64 v.
Proof.
intros E n v H. cbn [sv_denot]. rewrite H, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.
Lemma ondn_den_off : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v -> 0 <= c -> v + c < 2 ^ 64 ->
  sv_denot E (SOff n c) = Z_to_bv 64 (v + c).
Proof.
intros E n v c Hn H0 Hc Hvc. rewrite denot_lit_U. f_equal.
rewrite U_SOff, Hn, (unsigned_lit_small v ltac:(lia)). apply zcanon_id. unfold M64. lia.
Qed.

(* a.version and a.name are at most 10 bytes each (spec_strz_len reads at most 9). *)
Lemma ondn_annf_len : forall src, (length (TSS.ann_field src) <= 10)%nat.
Proof.
intros src. unfold TSS.ann_field. rewrite length_app, length_firstn. cbn [length].
rewrite DSpec.copy_len_strz. pose proof (DSpec.strz_len_le src). lia.
Qed.

(* The same, between two views. *)
Lemma ondn_mbyte_of_aview2 : forall H H' (m m' : word -> option byte) a,
  aview tfibsegs H' m' a = aview tfibsegs H m a ->
  YP09.mbyte tfibsegs (mrestrict H' m') a = YP09.mbyte tfibsegs (mrestrict H m) a.
Proof.
intros H H' m m' a E. unfold aview in E.
destruct (YP09.mbyte tfibsegs (mrestrict H' m') a) as [x|], (YP09.mbyte tfibsegs (mrestrict H m) a) as [y|];
  cbn [option_map] in E; [| discriminate E | discriminate E | reflexivity].
injection E as E. f_equal. apply bv_eq. exact E.
Qed.
Lemma ondn_vm_keepw : forall H H' (m m' : word -> option byte) a (n : nat) v,
  val_mem tfibsegs (mrestrict H m) a n v ->
  (forall x, a <= x < a + Z.of_nat n -> aview tfibsegs H' m' x = aview tfibsegs H m x) ->
  val_mem tfibsegs (mrestrict H' m') a n v.
Proof.
intros H H' m m' a n v HV HK j Hj. rewrite <- (HV j Hj). apply ondn_mbyte_of_aview2. apply HK. lia.
Qed.

(* Two 64-bit words are equal exactly when their values are. *)
Lemma ondn_eqb : forall v w, 0 <= v < 2 ^ 64 -> 0 <= w < 2 ^ 64 ->
  bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 w) = (v =? w).
Proof.
intros v w Hv Hw. unfold bv_eqb. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 64) with (2 ^ 64). rewrite !(Z.mod_small _ (2 ^ 64)) by lia. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* 6. The piece                                                        *)
(* ------------------------------------------------------------------ *)

(* A byte of a range this piece does not change: the kit's lia takes no disjunction, so split them by hand. *)
Ltac ondn_no :=
  unfold ondn_Z1, ondn_Z2, ondn_Z3, ondn_Z4, ONANN_A, ONANN_FBYTES in *;
  first [ intros [HH|HH] | intros HH ];
  unfold SHADOW_OFF in *;
  first [ lia | match goal with H : _ \/ _ |- _ => destruct H as [HSH|HSH]; lia end ].
Section dn. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

Lemma onann_dn_piece : @onann_dn_stmt fx rc B MT.
Proof.
unfold onann_dn_stmt. intros E0A E1A. unfold onann_dn_at.
intros LAWS0 CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F
  ly2 S2 W2 mem2 md2 regs2 HFIX HCUR HREGS.
pose proof LAWS0 as (HSMpc & HCELLS & HOC & HGU & HGE0 & HRU & HRE & LAWS & MTL & MTF & SMP & ASF & FFL & HGX & HGE).
pose proof CALLEES as (HSMR & HANP & HPF & HBC & HMS & HNC & HSS & HWK & HMO & HSHF5).
pose proof HFIX as (HJ0 & Hret & Hra & Hgp & Htp & Ea0 & Ea1 & Ea2 & Hsp16 & Hwin1 & Hwin2 & Hnow & HDF & Htw0 & Hgf &
  Hm & HTFat & HTFG & Hrom & Hapart & Hri & Hcnt3 & Hcnt1 & Hcnt2 & Hev & Esp1 & EFdef & QF0 & QF64 & QFc & QFapp).
pose proof HCUR as (HCUR0 & Htw2 & Hig & HAOK & HSLOT).
pose proof HCUR0 as (HJ1 & He0 & Hfrs & Hperm & HlyF & Hmo & HK & Hsaved & HFLw).
pose proof HREGS as (((R2 & R3 & R4 & R8 & R9 & R18 & R19 & R25) & R20 & R24) & R22 & R26 & R16 & R15 & R11).
pose proof HAOK as (HAv & HAn & HAu & HAl & HAsh).
pose proof HSLOT as (HS48 & HS56 & HS24 & HS16).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (onann_cur_ar B MT LAWS HFIX HCUR0) as (HARc & HAR2 & ESLO & ESHI & EFA & EFLa & Hin2 & EFA2 & HFpres &
  HFshpres & HFnG & HF0 & HF64 & HFc & HFapp & Hce & Hslo & Hshi & Hsthi & HFLpres & HFLown & (HFLlo & HFLhi) &
  HFLd1 & HFLd2 & (Hsp1a & Hsp1b) & Hsp132 & Hsp146).
assert (CS : ONANN_S = 6157888) by reflexivity.
assert (EST : ESTACK = 4096) by reflexivity.
assert (ESTK : ONANN_STK = 208 + WAKE_STK) by exact onann_stk_eq.
assert (HWE : 2 * ESTACK <= WAKE_STK) by (vm_compute; discriminate).
assert (HWN : NOTICE_STK <= WAKE_STK) by (vm_compute; discriminate).
assert (HNEV : NOTICE_EV = 0) by reflexivity.
assert (HEV0 : 0 <= ONANN_EV) by (vm_compute; discriminate).
(* the entry stack pointer's alignment, from the journal *)
pose proof HJ0 as (HSTKj & _ & (memSj & HJi & _) & _).
rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & Hlyle & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & Hstk0 & _).
pose proof Hstk0 as (Hsp0a & Hstkz & Hceil0 & Hslo0 & Hshi0 & H47j & _).
clear HJi memSj.
assert (DF8m : F mod 8 = 0).
{ pose proof (Z.div_mod F 64 ltac:(lia)) as D. rewrite HF64, Z.add_0_r in D. rewrite D.
  replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by ring. apply Z.mod_mul. lia. }
assert (Hpvr : 0 <= onann_pv timg_B b < 2 ^ 64).
{ rewrite <- (onann_pv_res b). unfold trans_pfrom_res.
  destruct (list_eq_dec Z.eq_dec _ _); [unfold TRANS_PERS; lia|].
  destruct (list_eq_dec Z.eq_dec _ _); unfold TRANS_PERS; lia. }
(* the frame, the shadow band and the stack are apart *)
assert (HSHF : F + 512 <= SHADOW_OFF \/ SHADOW_OFF + 2 ^ 44 <= F).
{ unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
  destruct HFapp as (_ & [HL | (HH1 & HH2)]); [left | right]; unfold SHADOW_OFF; lia. }
assert (HFG : F + 512 <= ONANN_S \/ ONANN_S + TW.SZ_g_s <= F).
{ destruct (Z_le_gt_dec (F + 512) ONANN_S) as [h|h]; [left; exact h|].
  destruct (Z_le_gt_dec (ONANN_S + TW.SZ_g_s) F) as [h2|h2]; [right; exact h2|].
  exfalso.
  assert (Hx : exists x, F <= x < F + 512 /\ ONANN_S <= x < ONANN_S + TW.SZ_g_s).
  { destruct (Z_le_gt_dec F ONANN_S) as [h3|h3]; [exists ONANN_S | exists F]; unfold TW.SZ_g_s in *; lia. }
  destruct Hx as (x & Hx1 & Hx2). exact (HFnG x Hx1 (ondn_inG_gs x Hx2)). }
assert (HFsp : F + 512 <= sp1) by lia.
assert (Hsp47 : sp1 + 64 <= 2 ^ 47) by lia.
assert (HF47 : F + 512 <= 2 ^ 47) by lia.
assert (HFd : 0 <= F / 8 <= 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
assert (E17 : (F + 136) / 8 = F / 8 + 17)
  by (rewrite (ondn_div8 F 136 HF64 ltac:(lia) ltac:(lia) ltac:(reflexivity)); reflexivity).
assert (E17b : SHADOW_OFF + (F + 136) / 8 = SHADOW_OFF + F / 8 + 17) by (rewrite E17; lia).
(* the model on this path *)
pose proof (tw_len _ _ _ Htw0) as HLw.
destruct (ondn_model TF Bw b Bw' now Hig Hm) as (B2 & HNT & HNM & HCN & HKE0 & HKE1).
pose proof (onann_w1_len timg_B Bw b HLw) as HLw1.
destruct (onann_dn_world TF (onann_w1 timg_B Bw b) b B2 HCN) as (dv & EB2).
assert (HsameB2 : onann_same Bw B2).
{ rewrite EB2. apply (onann_same_trans Bw (onann_w1 timg_B Bw b));
    [exact (onann_same_w1 timg_B Bw b HLw) | exact (onann_same_desk _ dv HLw1)]. }
pose proof HsameB2 as (HL2 & HSt2 & HNt2 & HNc2 & HAw2 & HHm2 & HGn2 & HGf2 & HRi2).
assert (Hgf2 : TW.g_fail_next B2 <= 1) by lia.
assert (Hri2 : onann_ri B2) by (apply HRi2; exact Hri).
(* f, the caller's struct diginet_frame, at the cut state *)
assert (USP2 : spZ regs2 = sp1)
  by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; lia).
destruct (onann_f30 B MT LAWS0 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw'
  pos sp1 F ly2 S2 W2 mem2 md2 0 regs2 NOTICE_STK HFIX HCUR0 ltac:(lia) ltac:(lia))
  as (Hfp0 & Hfpc & Hfp8 & HfpF & Hg8f & Hfake & Hrdok & Hoffw & Hcmdr & Hcmdv & Hcmdg & Hcmdsh & Hf32 & Hbuf0 &
      Hbufg & Hbufs & Hbufw & HbufG).
assert (Hfp64 : 0 <= fp < 2 ^ 64) by (unfold FRAME_F_SIZE in Hfpc; lia).
(* the run kit *)
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B
  HGX 0 []) as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B
  HGX 0 []) as RUNTO.
pose proof (paj_branch (fx := fx) (PI := PI_transportb)) as BR.
(* ---- run 1, +0x300 .. +0x360 ---- *)
pose proof (ondn_entry1 (fx := fx) B ly2 S2 W2 regs2 mem2 md2 (onann_w1 timg_B Bw b) F HOC HAR2 Htw2 R18 R19 R20 R24 R11
  HF0 HF64 HF47 HSHF HFG
  ltac:(intros a Ha; exact (proj1 (HFpres a ltac:(lia))))
  ltac:(intros i Hi; exact (proj1 (HFshpres i ltac:(lia))))) as HS.
set (EA := ondn_E1 regs2 (onann_w1 timg_B Bw b)) in HS.
assert (HEIA : img_env VAL A_LIM EA) by (unfold EA, ondn_E1; apply Eimg_env).
assert (EEA : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew EA n = YK11.getr regs2 r)
  by (intros n r Hn; exact (ondn_ew1 regs2 _ n r Hn)).
assert (U18A : bv_unsigned (ew EA 18) = SHADOW_OFF + F / 8)
  by (rewrite (EEA 18%nat 18%bv eq_refl), R18; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U19A : bv_unsigned (ew EA 19) = F)
  by (rewrite (EEA 19%nat 19%bv eq_refl), R19; unfold w64; apply unsigned_lit_small; lia).
assert (SHOK : sh_ok segs ONDN_BX (@nil shent) EA (mrestrict (w_H W2) mem2)) by constructor.
pose proof HJ1 as HJ.
paj_run_to_tok RUNTO HS HJ SHOK ONDN_B0 ONDN_C1.
{ ondn_awr_rs.
  apply (awr_ok_x_cons_own _ _ _ _ _ _ _ _ _ _ _ _ ONANN_CID pos); [left; reflexivity | |].
  { intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U18A in Ha.
    right. unfold in_zr, shadow_addr. cbn [fst snd]. rewrite EFA2.
    change (fs_frame_bytes ONANN_CID / 8) with 64. lia. }
  apply (awr_ok_x_cons_own _ _ _ _ _ _ _ _ _ _ _ _ ONANN_CID pos); [left; reflexivity | |].
  { intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U19A in Ha.
    left. unfold in_zr. cbn [fst snd]. rewrite EFA2.
    change (fs_frame_bytes ONANN_CID) with 512. lia. }
  repeat (apply awr_ok_x_cons;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |]).
  apply awr_ok_x_nil. }
ondn_name_md mdA.
ondn_lo HS EA EAlo msA.
(* what run 1 wrote *)
assert (KA : forall a, 0 <= a < 2 ^ 64 -> ~ ondn_Z1 F a ->
  aview segs (w_H W2) (ms_mem msA) a = aview segs (w_H W2) mem2 a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ (ondn_Z1 F) HFr); [| exact Ha | exact Hn].
  intros b0 wlo whi x Hiw Hx. cbv beta.
  ondn_win Hiw Hx ltac:(rewrite ?U18A, ?U19A in Hx; unfold ondn_Z1; first [left; lia | right; lia]). }
assert (GA : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem msA) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
clear HF HFr HG.
ondn_region HS 0%nat RGsh.
ondn_region HS 1%nat RGn.
assert (ZS1 : forall i, 14 <= i < 23 -> aview segs (w_H W2) (ms_mem msA) (SHADOW_OFF + F / 8 + i) = Some 0).
{ intros i Hi.
  pose proof RGsh as (_ & _ & _ & Hcs). cbn [base_val YP09.r_base] in Hcs.
  try rewrite (EAlo 18%nat ltac:(lia)) in Hcs. rewrite U18A in Hcs.
  assert (Hi' : i = 14 \/ i = 15 \/ i = 16 \/ i = 17 \/ i = 18 \/ i = 19 \/ i = 20 \/ i = 21 \/ i = 22) by lia.
  destruct Hi' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]];
  apply (chunks_zero_aview _ _ _ (SHADOW_OFF + F / 8) _ _ Hcs); ondn_in. }
pose proof (ondn_chunk_val _ _ _ _ _ _ _ _ _ 112 4 (SLit 1) RGn ltac:(ondn_in) ltac:(lia)) as V112.
pose proof (ondn_chunk_val _ _ _ _ _ _ _ _ _ 116 4 (SExt true 32 (SOff 32 0)) RGn ltac:(ondn_in) ltac:(lia)) as V116.
pose proof (ondn_chunk_val _ _ _ _ _ _ _ _ _ 120 8 (SLit 0) RGn ltac:(ondn_in) ltac:(lia)) as V120.
pose proof (ondn_chunk_val _ _ _ _ _ _ _ _ _ 128 8 (SOff 22 0) RGn ltac:(ondn_in) ltac:(lia)) as V128.
cbn [base_val] in V112, V116, V120, V128.
try rewrite (EAlo 19%nat ltac:(lia)) in V112. try rewrite (EAlo 19%nat ltac:(lia)) in V116.
try rewrite (EAlo 19%nat ltac:(lia)) in V120. try rewrite (EAlo 19%nat ltac:(lia)) in V128.
rewrite U19A in V112, V116, V120, V128.
change (N.to_nat 4) with 4%nat in V112, V116. change (N.to_nat 8) with 8%nat in V120, V128.
cbn [sv_denot] in V112, V120.
change (bv_unsigned (Z_to_bv 64 1) mod 2 ^ (8 * Z.of_N 4)) with 1 in V112.
change (bv_unsigned (Z_to_bv 64 0) mod 2 ^ (8 * Z.of_N 8)) with 0 in V120.
rewrite (ondn_sext32 _ (onann_w1 timg_B Bw b)) in V116;
  [| try rewrite (EAlo 32%nat ltac:(lia)); unfold EA; apply ondn_ew1_32].
apply (ondn_vm_w _ _ 4 (TW.S_state (onann_w1 timg_B Bw b)) ltac:(lia)) in V116.
change (N.to_nat 4) with 4%nat in V116.
rewrite (ondn_den_reg _ 22 fp) in V128;
  [| try rewrite (EAlo 22%nat ltac:(lia)); rewrite (EEA 22%nat 22%bv eq_refl); exact R22].
apply (ondn_vm_w _ _ 8 fp ltac:(lia)) in V128. change (N.to_nat 8) with 8%nat in V128.
(* the registers at the end of run 1 *)
ondn_reg HS (Z_to_bv 5 12) (w64 (SHADOW_OFF + F / 8 + 17)) Q12
  ltac:(rewrite <- E17b; apply (ondn_den_shadow_lit _ 19 F 136);
        [try rewrite (EAlo 19%nat ltac:(lia)); rewrite (EEA 19%nat 19%bv eq_refl); exact R19 |
         lia | lia | lia]).
ondn_reg HS (Z_to_bv 5 21) (w64 (F + 112)) Q21
  ltac:(apply (ondn_den_off _ 19 F 112);
        [try rewrite (EAlo 19%nat ltac:(lia)); rewrite (EEA 19%nat 19%bv eq_refl); exact R19 |
         lia | lia | lia]).
ondn_reg HS (Z_to_bv 5 13) (w64 (ONANN_S + 112)) Q13 ltac:(unfold w64; vm_compute; reflexivity).
ondn_reg HS (Z_to_bv 5 14) (w64 ONDN_SH112) Q14 ltac:(unfold w64; vm_compute; reflexivity).
ondn_kreg HS EAlo EEA (Z_to_bv 5 2) 2%nat R2 Q2.
ondn_kreg HS EAlo EEA (Z_to_bv 5 3) 3%nat R3 Q3.
ondn_kreg HS EAlo EEA (Z_to_bv 5 4) 4%nat R4 Q4.
ondn_kreg HS EAlo EEA (Z_to_bv 5 8) 8%nat R8 Q8.
ondn_kreg HS EAlo EEA (Z_to_bv 5 9) 9%nat R9 Q9.
ondn_kreg HS EAlo EEA (Z_to_bv 5 15) 15%nat R15 Q15.
ondn_kreg HS EAlo EEA (Z_to_bv 5 16) 16%nat R16 Q16.
ondn_kreg HS EAlo EEA (Z_to_bv 5 18) 18%nat R18 Q18.
ondn_kreg HS EAlo EEA (Z_to_bv 5 19) 19%nat R19 Q19.
ondn_reg HS (Z_to_bv 5 20) (w64 ONANN_S) Q20 ltac:(unfold w64; vm_compute; reflexivity).
ondn_kreg HS EAlo EEA (Z_to_bv 5 22) 22%nat R22 Q22.
ondn_reg HS (Z_to_bv 5 24) (w64 SHADOW_OFF) Q24 ltac:(unfold w64; vm_compute; reflexivity).
ondn_kreg HS EAlo EEA (Z_to_bv 5 25) 25%nat R25 Q25.
ondn_kreg HS EAlo EEA (Z_to_bv 5 26) 26%nat R26 Q26.
pose proof HK as (K1 & K2 & K3 & K4 & K5 & K6).
(* ---- run 2, +0x364 .. the call of __asan_memset ---- *)
pmkst HS.
clear HS SHOK.
set (rA := ms_regs msA) in *. set (mA := ms_mem msA) in *. clearbody rA mA.
lazymatch goal with |- SRr _ ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Qx =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + ONDN_C1)) mm rom) mdx) Qx) end.
pose proof (ondn_entry2 (fx := fx) W2 rA mA F sp1 Q12 Q21 Q9 Q20 Q13 Q14 ltac:(apply ZS1; lia)
  HF0 HF64 HF47 HSHF HFsp Hsp146 Hsp47 Hsp132
  ltac:(intros a Ha; apply GA; exact (proj1 (HFpres a ltac:(lia))))
  ltac:(intros a Ha; apply GA; apply K6; lia)) as HS.
set (EB := ondn_E2 rA) in HS.
assert (HEIB : img_env VAL A_LIM EB) by (unfold EB, ondn_E2; apply Eimg_env).
assert (EEB : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew EB n = YK11.getr rA r)
  by (intros n r Hn; exact (ondn_ew2 rA n r Hn)).
assert (U21B : bv_unsigned (ew EB 21) = F + 112)
  by (rewrite (EEB 21%nat (Z_to_bv 5 21) eq_refl), Q21; unfold w64; apply unsigned_lit_small; lia).
assert (U9B : bv_unsigned (ew EB 9) = sp1)
  by (rewrite (EEB 9%nat (Z_to_bv 5 9) eq_refl), Q9; unfold w64; apply unsigned_lit_small; lia).
assert (U12B : bv_unsigned (ew EB 12) = SHADOW_OFF + F / 8 + 17)
  by (rewrite (EEB 12%nat (Z_to_bv 5 12) eq_refl), Q12; unfold w64; apply unsigned_lit_small;
      unfold SHADOW_OFF; lia).
assert (SHOK : sh_ok segs ONDN_BX (@nil shent) EB (mrestrict (w_H W2) mA)) by constructor.
paj_run_tok RUN HS HJ SHOK ONDN_B0.
{ ondn_awr_rs.
  apply awr_ok_x_cons;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |].
  apply (awr_ok_x_cons_own _ _ _ _ _ _ _ _ _ _ _ _ ONANN_CID pos); [left; reflexivity | |].
  { intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U21B in Ha.
    left. unfold in_zr. cbn [fst snd]. rewrite EFA2.
    change (fs_frame_bytes ONANN_CID) with 512. lia. }
  apply awr_ok_x_cons;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U9B in Ha;
     left; split; [unfold awr_byte; left; lia | lia] |].
  apply awr_ok_x_nil. }
ondn_name_md mdB.
ondn_lo HS EB EBlo msB.
assert (KB : forall a, 0 <= a < 2 ^ 64 -> ~ ondn_Z2 F sp1 a ->
  aview segs (w_H W2) (ms_mem msB) a = aview segs (w_H W2) mA a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ (ondn_Z2 F sp1) HFr); [| exact Ha | exact Hn].
  intros b0 wlo whi x Hiw Hx. cbv beta.
  ondn_win Hiw Hx ltac:(rewrite ?U12B, ?U21B, ?U9B in Hx; unfold ondn_Z2;
                        first [left; lia | right; lia]). }
assert (GB : forall a, apresent (w_H W2) mA a -> apresent (w_H W2) (ms_mem msB) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
clear HF HFr HG.
ondn_region HS 1%nat RGn2.
ondn_region HS 2%nat RGsl2.
pose proof (ondn_chunk_val _ _ _ _ _ _ _ _ _ 24 8 (SOff 26 0) RGn2 ltac:(ondn_in) ltac:(lia)) as V136.
pose proof (ondn_chunk_val _ _ _ _ _ _ _ _ _ 32 8 (SOff 16 0) RGn2 ltac:(ondn_in) ltac:(lia)) as V144.
pose proof (ondn_chunk_val _ _ _ _ _ _ _ _ _ 40 4 (SOff 15 0) RGn2 ltac:(ondn_in) ltac:(lia)) as V152.
pose proof (ondn_chunk_val _ _ _ _ _ _ _ _ _ 32 8 (SLit ONDN_SH112) RGsl2 ltac:(ondn_in) ltac:(lia)) as VS32.
pose proof (ondn_chunk_val _ _ _ _ _ _ _ _ _ 40 8 (SLit (ONANN_S + 112)) RGsl2 ltac:(ondn_in) ltac:(lia)) as VS40.
cbn [base_val] in V136, V144, V152, VS32, VS40.
try rewrite (EBlo 21%nat ltac:(lia)) in V136. try rewrite (EBlo 21%nat ltac:(lia)) in V144.
try rewrite (EBlo 21%nat ltac:(lia)) in V152.
try rewrite (EBlo 9%nat ltac:(lia)) in VS32. try rewrite (EBlo 9%nat ltac:(lia)) in VS40.
rewrite U21B in V136, V144, V152. rewrite U9B in VS32, VS40.
replace (F + 112 + 24) with (F + 136) in V136 by lia.
replace (F + 112 + 32) with (F + 144) in V144 by lia.
replace (F + 112 + 40) with (F + 152) in V152 by lia.
change (N.to_nat 8) with 8%nat in V136, V144, VS32, VS40. change (N.to_nat 4) with 4%nat in V152.
rewrite (ondn_den_reg _ 26 (F + ONANN_A)) in V136;
  [| try rewrite (EBlo 26%nat ltac:(lia)); rewrite (EEB 26%nat (Z_to_bv 5 26) eq_refl); exact Q26].
rewrite (ondn_den_reg _ 16 (onann_pv timg_B b)) in V144;
  [| try rewrite (EBlo 16%nat ltac:(lia)); rewrite (EEB 16%nat (Z_to_bv 5 16) eq_refl); exact Q16].
rewrite (ondn_den_reg _ 15 (onann_off (onann_w1 timg_B Bw b) b)) in V152;
  [| try rewrite (EBlo 15%nat ltac:(lia)); rewrite (EEB 15%nat (Z_to_bv 5 15) eq_refl); exact Q15].
apply (ondn_vm_w _ _ 8 (F + ONANN_A) ltac:(lia)) in V136. change (N.to_nat 8) with 8%nat in V136.
apply (ondn_vm_w _ _ 8 (onann_pv timg_B b) ltac:(lia)) in V144. change (N.to_nat 8) with 8%nat in V144.
apply (ondn_vm_w _ _ 4 (onann_off (onann_w1 timg_B Bw b) b) ltac:(lia)) in V152.
change (N.to_nat 4) with 4%nat in V152.
cbn [sv_denot] in VS32, VS40.
change (bv_unsigned (Z_to_bv 64 ONDN_SH112) mod 2 ^ (8 * Z.of_N 8)) with ONDN_SH112 in VS32.
change (bv_unsigned (Z_to_bv 64 (ONANN_S + 112)) mod 2 ^ (8 * Z.of_N 8)) with (ONANN_S + 112) in VS40.
(* the registers at the call of __asan_memset *)
ondn_reg HS (Z_to_bv 5 10) (w64 (F + 156)) M10
  ltac:(replace (F + 156) with (F + 112 + 44) by lia; apply (ondn_den_off _ 21 (F + 112) 44);
        [try rewrite (EBlo 21%nat ltac:(lia)); rewrite (EEB 21%nat (Z_to_bv 5 21) eq_refl); exact Q21 |
         lia | lia | lia]).
ondn_reg HS (Z_to_bv 5 11) (w64 0) M11 ltac:(unfold w64; vm_compute; reflexivity).
ondn_reg HS (Z_to_bv 5 12) (w64 28) M12 ltac:(unfold w64; vm_compute; reflexivity).
ondn_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + ONDN_C2)) M1 ltac:(apply codeptr_val; assumption).
ondn_kreg HS EBlo EEB (Z_to_bv 5 2) 2%nat Q2 M2.
ondn_kreg HS EBlo EEB (Z_to_bv 5 3) 3%nat Q3 M3.
ondn_kreg HS EBlo EEB (Z_to_bv 5 4) 4%nat Q4 M4.
ondn_kreg HS EBlo EEB (Z_to_bv 5 8) 8%nat Q8 M8.
ondn_kreg HS EBlo EEB (Z_to_bv 5 9) 9%nat Q9 M9.
ondn_kreg HS EBlo EEB (Z_to_bv 5 18) 18%nat Q18 M18.
ondn_kreg HS EBlo EEB (Z_to_bv 5 19) 19%nat Q19 M19.
ondn_reg HS (Z_to_bv 5 20) (w64 ONANN_S) M20 ltac:(unfold w64; vm_compute; reflexivity).
ondn_kreg HS EBlo EEB (Z_to_bv 5 21) 21%nat Q21 M21.
ondn_kreg HS EBlo EEB (Z_to_bv 5 22) 22%nat Q22 M22.
ondn_kreg HS EBlo EEB (Z_to_bv 5 24) 24%nat Q24 M24.
ondn_kreg HS EBlo EEB (Z_to_bv 5 25) 25%nat Q25 M25.
ondn_reg HS (Z_to_bv 5 23) (w64 (onann_off (onann_w1 timg_B Bw b) b)) M23
  ltac:(cbn [sv_denot]; try rewrite (EBlo 15%nat ltac:(lia));
        rewrite (EEB 15%nat (Z_to_bv 5 15) eq_refl), Q15, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
ondn_reg HS (Z_to_bv 5 26) (w64 (ONANN_S + 96)) M26 ltac:(unfold w64; vm_compute; reflexivity).
assert (USPB : spZ (ms_regs msB) = sp1)
  by (change (bv_unsigned (YK11.getr (ms_regs msB) (Z_to_bv 5 2)) = sp1); rewrite M2; unfold w64;
      apply unsigned_lit_small; lia).
pmkst HS.
(* +0x390: __asan_memset (n + 44, 0, 28), through the G call kit *)
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Qx =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transportb_sigma TB___asan_memset)) mm rom) mdx) Qx) end.
eapply SRr_bind.
{ apply (@gx_intrin_at fx rc tfib_sink_head segs B LAWS transportb_segs_low OSet
    (transportb_sigma TB___asan_memset) (HMS fx) TG.G_HARNESS_B W2 (ms_regs msB) (ms_mem msB) STK sp0 FP ly S W0
    mem0 md0 ((ONANN_CID, pos) :: own) ly2 S2 mdB (k + 0) (F + 156) 0 28 (sp1 - sp0)
    (Z_to_bv 64 (BASE + ONDN_C2)) HGX G_HARNESS_B_rw HJ M10 M11 M12).
  - lia.
  - lia.
  - lia.
  - rewrite USPB. lia.
  - pose proof (Z.div_mod sp1 32 ltac:(lia)) as D1. pose proof (Z.div_mod sp0 16 ltac:(lia)) as D2.
    rewrite Hsp132, Z.add_0_r in D1. rewrite Hsp0a, Z.add_0_r in D2.
    rewrite D1, D2. replace (32 * (sp1 / 32) - 16 * (sp0 / 16)) with ((2 * (sp1 / 32) - sp0 / 16) * 16) by ring.
    apply Z.mod_mul. lia.
  - lia.
  - lia.
  - exact (eq_trans M3 Hgp).
  - exact (eq_trans M4 Htp).
  - exact M1.
  - apply (ret_ok_codeptr_v (PI := PI_transportb));
      [unfold ONDN_C2, AF_on_announce; lia | unfold ONDN_C2, AF_on_announce; reflexivity].
  - eapply (transport_twr_ok_g_intro segs B LAWS); [exact HJ|]. intros a Ha. left. rewrite USPB. split.
    + unfold awr_byte. right; right; right. unfold in_frames. exists ONANN_CID, pos. split; [left; reflexivity|].
      left. unfold in_zr. cbn [fst snd]. rewrite EFA2. change (fs_frame_bytes ONANN_CID) with 512. lia.
    + lia.
  - apply (amem_range_sub_app F 512); [exact HFapp | lia | lia | lia | lia].
  - apply (frame_ra_zero _ F (F + 156) 28 19 23); [lia | exact DF8m | lia | lia |].
    intros i Hi. rewrite (KB (SHADOW_OFF + F / 8 + i) ltac:(unfold SHADOW_OFF; lia) ltac:(ondn_no)).
    apply ZS1. lia.
  - intros _. apply (frame_hull_vis _ F 512 (F + 156) 28); [lia | exact HF64 | reflexivity | lia | lia | lia |].
    intros i Hi. change (shadow_addr F + i) with (SHADOW_OFF + F / 8 + i).
    apply can_aview_vis. apply GB. apply GA. exact (proj1 (HFshpres i ltac:(change (512 / 8) with 64 in Hi; lia))).
  - exact I. }
cbv beta. intros W3x c2 _ (-> & regsM & memM & mdM & -> & HJ2 & HPM & HA0M & HsetM & HeffM & HgrM).
(* the memset's zeros and what it kept *)
assert (ZMM : forall a, F + 156 <= a < F + 184 -> aview segs (w_H W2) memM a = Some 0).
{ intros a Ha. replace a with ((F + 156) + (a - (F + 156))) by lia.
  rewrite (HsetM (a - (F + 156)) ltac:(lia)). reflexivity. }
assert (KM : forall a, 0 <= a < 2 ^ 64 -> ~ ondn_Z3 F sp1 a ->
  aview segs (w_H W2) memM a = aview segs (w_H W2) (ms_mem msB) a).
{ intros a Ha Hn. apply HeffM; [exact Ha | intros Hd; apply Hn; left; lia | intros Hd; apply Hn; right; lia]. }
assert (CHM : forall n, acallee_saved n ->
  YK11.getr regsM (Z_to_bv 5 n) = YK11.getr (ms_regs msB) (Z_to_bv 5 n))
  by (intros n Hn; exact (HPM n Hn)).
assert (N2 : YK11.getr regsM 2 = w64 sp1) by exact (eq_trans (CHM 2 ltac:(hnf; lia)) M2).
assert (N3 : YK11.getr regsM 3 = YK11.getr regs 3) by exact (eq_trans (CHM 3 ltac:(hnf; lia)) M3).
assert (N4 : YK11.getr regsM 4 = YK11.getr regs 4) by exact (eq_trans (CHM 4 ltac:(hnf; lia)) M4).
assert (N8 : YK11.getr regsM 8 = w64 (spZ regs)) by exact (eq_trans (CHM 8 ltac:(hnf; lia)) M8).
assert (N9 : YK11.getr regsM 9 = w64 sp1) by exact (eq_trans (CHM 9 ltac:(hnf; lia)) M9).
assert (N18 : YK11.getr regsM 18 = w64 (SHADOW_OFF + F / 8)) by exact (eq_trans (CHM 18 ltac:(hnf; lia)) M18).
assert (N19 : YK11.getr regsM 19 = w64 F) by exact (eq_trans (CHM 19 ltac:(hnf; lia)) M19).
assert (N20 : YK11.getr regsM 20 = w64 ONANN_S) by exact (eq_trans (CHM 20 ltac:(hnf; lia)) M20).
assert (N21 : YK11.getr regsM 21 = w64 (F + 112)) by exact (eq_trans (CHM 21 ltac:(hnf; lia)) M21).
assert (N22 : YK11.getr regsM 22 = w64 fp) by exact (eq_trans (CHM 22 ltac:(hnf; lia)) M22).
assert (N23 : YK11.getr regsM 23 = w64 (onann_off (onann_w1 timg_B Bw b) b))
  by exact (eq_trans (CHM 23 ltac:(hnf; lia)) M23).
assert (N24 : YK11.getr regsM 24 = w64 SHADOW_OFF) by exact (eq_trans (CHM 24 ltac:(hnf; lia)) M24).
assert (N25 : YK11.getr regsM 25 = w64 F) by exact (eq_trans (CHM 25 ltac:(hnf; lia)) M25).
assert (N26 : YK11.getr regsM 26 = w64 (ONANN_S + 96)) by exact (eq_trans (CHM 26 ltac:(hnf; lia)) M26).
(* no byte of G is one of the bytes this piece changes *)
assert (NZG : forall a, inG TG.G_HARNESS_B a ->
  ~ ondn_Z1 F a /\ ~ ondn_Z2 F sp1 a /\ ~ ondn_Z3 F sp1 a /\ ~ ondn_Z4 sp1 a).
{ intros a Hg. pose proof (inG_low segs B transportb_segs_low TG.G_HARNESS_B a HGX Hg) as Hl.
  unfold kLowMemEnd in Hl.
  assert (HnF : ~ (F <= a < F + 512)) by (intros HF; exact (HFnG a HF Hg)).
  unfold ondn_Z1, ondn_Z2, ondn_Z3, ondn_Z4, SHADOW_OFF in *.
  split; [intros [HH|HH]; lia|]. split; [intros [HH|HH]; lia|]. split; [intros [HH|HH]; lia|]. intros HH; lia. }
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HARM.
assert (TWM : tw_at TMAP_B (aview segs (w_H W2) memM) (onann_w1 timg_B Bw b)).
{ apply (tw_kept_GB (aview segs (w_H W2) mem2)); [exact Htw2|].
  intros b0 n0 i Hbn Hi.
  assert (Hg : inG TG.G_HARNESS_B (b0 + i)) by (apply (ondn_inG b0 n0); [exact Hbn | lia]).
  pose proof (inG_low segs B transportb_segs_low TG.G_HARNESS_B _ HGX Hg) as Hl. unfold kLowMemEnd in Hl.
  destruct (NZG _ Hg) as (NG1 & NG2 & NG3 & NG4).
  rewrite (KM (b0 + i) ltac:(lia) NG3), (KB (b0 + i) ltac:(lia) NG2), (KA (b0 + i) ltac:(lia) NG1). reflexivity. }
(* ---- run 3, +0x394 .. the indirect call of notice ---- *)
clear HS SHOK.
pose proof (ondn_entry3 (fx := fx) B ly2 S2 W2 regsM memM mdM (onann_w1 timg_B Bw b) sp1 HOC HARM TWM HNT N9 N20 N24 N26
  Hsp146 Hsp47 Hsp132
  ltac:(intros a Ha; apply HgrM; apply GB; apply GA; apply K6; lia)) as HS.
set (EC := ondn_E3 regsM (onann_w1 timg_B Bw b)) in HS.
assert (HEIC : img_env VAL A_LIM EC) by (unfold EC, ondn_E3; apply Eimg_env).
assert (EEC : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew EC n = YK11.getr regsM r)
  by (intros n r Hn; exact (ondn_ew3 regsM _ n r Hn)).
assert (U9C : bv_unsigned (ew EC 9) = sp1)
  by (rewrite (EEC 9%nat (Z_to_bv 5 9) eq_refl), (N9 : YK11.getr regsM (Z_to_bv 5 9) = w64 sp1);
      unfold w64; apply unsigned_lit_small; lia).
assert (SHOK : sh_ok segs ONDN_BX (@nil shent) EC (mrestrict (w_H W2) memM)) by constructor.
paj_run_to_tok RUNTO HS HJ2 SHOK ONDN_B0 AF_notice.
{ ondn_awr_rs.
  apply awr_ok_x_cons;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |].
  apply awr_ok_x_cons;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |].
  apply awr_ok_x_cons;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U9C in Ha;
     left; split; [unfold awr_byte; left; lia | lia] |].
  apply awr_ok_x_nil. }
ondn_name_md mdC.
ondn_lo HS EC EClo msC.
assert (KC : forall a, 0 <= a < 2 ^ 64 -> ~ ondn_Z4 sp1 a ->
  aview segs (w_H W2) (ms_mem msC) a = aview segs (w_H W2) memM a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ (ondn_Z4 sp1) HFr); [| exact Ha | exact Hn].
  intros b0 wlo whi x Hiw Hx. cbv beta.
  ondn_win Hiw Hx ltac:(rewrite ?U9C in Hx; unfold ondn_Z4; lia). }
assert (GC : forall a, apresent (w_H W2) memM a -> apresent (w_H W2) (ms_mem msC) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
clear HF HFr HG.
set (memN := ms_mem msC) in *.
(* what the bytes of the notice read at the call *)
assert (KBN : forall a, 0 <= a < 2 ^ 64 -> ~ ondn_Z3 F sp1 a -> ~ ondn_Z4 sp1 a ->
  aview segs (w_H W2) memN a = aview segs (w_H W2) (ms_mem msB) a)
  by (intros a Ha H3 H4; rewrite (KC a Ha H4); exact (KM a Ha H3)).
assert (KAN : forall a, 0 <= a < 2 ^ 64 -> ~ ondn_Z2 F sp1 a -> ~ ondn_Z3 F sp1 a -> ~ ondn_Z4 sp1 a ->
  aview segs (w_H W2) memN a = aview segs (w_H W2) mA a)
  by (intros a Ha H2 H3 H4; rewrite (KBN a Ha H3 H4); exact (KB a Ha H2)).
assert (K2N : forall a, 0 <= a < 2 ^ 64 -> ~ ondn_Z1 F a -> ~ ondn_Z2 F sp1 a -> ~ ondn_Z3 F sp1 a ->
  ~ ondn_Z4 sp1 a -> aview segs (w_H W2) memN a = aview segs (w_H W2) mem2 a)
  by (intros a Ha H1 H2 H3 H4; rewrite (KAN a Ha H2 H3 H4); exact (KA a Ha H1)).
assert (V112N : val_mem segs (mrestrict (w_H W2) memN) (F + 112) 4 1)
  by (apply (ondn_vm_keep _ mA); [exact V112 |
      intros x Hx; apply KAN; [lia | ondn_no | ondn_no | ondn_no]]).
assert (V116N : val_mem segs (mrestrict (w_H W2) memN) (F + 116) 4 (TW.S_state (onann_w1 timg_B Bw b)))
  by (apply (ondn_vm_keep _ mA); [exact V116 |
      intros x Hx; apply KAN; [lia | ondn_no | ondn_no | ondn_no]]).
assert (V120N : val_mem segs (mrestrict (w_H W2) memN) (F + 120) 8 0)
  by (apply (ondn_vm_keep _ mA); [exact V120 |
      intros x Hx; apply KAN; [lia | ondn_no | ondn_no | ondn_no]]).
assert (V128N : val_mem segs (mrestrict (w_H W2) memN) (F + 128) 8 fp)
  by (apply (ondn_vm_keep _ mA); [exact V128 |
      intros x Hx; apply KAN; [lia | ondn_no | ondn_no | ondn_no]]).
assert (V136N : val_mem segs (mrestrict (w_H W2) memN) (F + 136) 8 (F + ONANN_A))
  by (apply (ondn_vm_keep _ (ms_mem msB)); [exact V136 |
      intros x Hx; apply KBN; [lia | ondn_no | ondn_no]]).
assert (V144N : val_mem segs (mrestrict (w_H W2) memN) (F + 144) 8 (onann_pv timg_B b))
  by (apply (ondn_vm_keep _ (ms_mem msB)); [exact V144 |
      intros x Hx; apply KBN; [lia | ondn_no | ondn_no]]).
assert (V152N : val_mem segs (mrestrict (w_H W2) memN) (F + 152) 4 (onann_off (onann_w1 timg_B Bw b) b))
  by (apply (ondn_vm_keep _ (ms_mem msB)); [exact V152 |
      intros x Hx; apply KBN; [lia | ondn_no | ondn_no]]).
assert (ZMN : forall a, F + 156 <= a < F + 184 -> aview segs (w_H W2) memN a = Some 0).
{ intros a Ha. rewrite (KC a ltac:(lia) ltac:(ondn_no)). exact (ZMM a Ha). }
assert (HNBN : garr8 segs (mrestrict (w_H W2) memN) (F + 112)
  (map DSpec.bz (ondn_bytes (TW.S_state (onann_w1 timg_B Bw b)) fp (F + ONANN_A) (onann_pv timg_B b)
     (onann_off (onann_w1 timg_B Bw b) b))))
  by exact (ondn_nb (w_H W2) memN F _ _ _ _ _ V112N V116N V120N V128N V136N V144N V152N ZMN).
(* a, the announce the parse filled, at the call *)
assert (KAnn : forall x, F + ONANN_A <= x < F + ONANN_A + 20 ->
  aview segs (w_H W2) memN x = aview segs (w_H W2) mem2 x).
{ intros x Hx. unfold ONANN_A in Hx. apply K2N; [lia | ondn_no | ondn_no | ondn_no | ondn_no]. }
assert (HAvN : garr8 segs (mrestrict (w_H W2) memN) (F + ONANN_A)
  (map DSpec.bz (TSS.ann_field (skipn 15 (DSpec.fr_body b))))).
{ eapply garr8_frame; [exact HAv|]. intros a Ha. rewrite length_map in Ha.
  pose proof (ondn_annf_len (skipn 15 (DSpec.fr_body b))) as HL.
  apply ondn_mbyte_of_aview. apply KAnn. unfold ONANN_A in *. lia. }
assert (HAnN : garr8 segs (mrestrict (w_H W2) memN) (F + ONANN_A + 10)
  (map DSpec.bz (TSS.ann_field (skipn 24 (DSpec.fr_body b))))).
{ eapply garr8_frame; [exact HAn|]. intros a Ha. rewrite length_map in Ha.
  pose proof (ondn_annf_len (skipn 24 (DSpec.fr_body b))) as HL.
  apply ondn_mbyte_of_aview. apply KAnn. unfold ONANN_A in *. lia. }
assert (HAshN : forall i, 4 <= i < 9 -> aview segs (w_H W2) memN (SHADOW_OFF + F / 8 + i) = Some 0).
{ intros i Hi. rewrite (K2N (SHADOW_OFF + F / 8 + i) ltac:(unfold SHADOW_OFF; lia)
    ltac:(ondn_no) ltac:(ondn_no) ltac:(ondn_no) ltac:(ondn_no)).
  exact (HAsh i Hi). }
assert (ZSN : forall i, 14 <= i < 23 -> aview segs (w_H W2) memN (SHADOW_OFF + F / 8 + i) = Some 0).
{ intros i Hi. rewrite (KBN (SHADOW_OFF + F / 8 + i) ltac:(unfold SHADOW_OFF; lia)
    ltac:(ondn_no) ltac:(ondn_no)).
  rewrite (KB (SHADOW_OFF + F / 8 + i) ltac:(unfold SHADOW_OFF; lia) ltac:(ondn_no)).
  exact (ZS1 i Hi). }
(* the registers at notice's entry *)
ondn_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + ONDN_C3)) P1 ltac:(apply codeptr_val; assumption).
ondn_reg HS (Z_to_bv 5 11) (w64 (F + 112)) P11
  ltac:(cbn [sv_denot]; try rewrite (EClo 21%nat ltac:(lia));
        rewrite (EEC 21%nat 21%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact N21).
ondn_kreg HS EClo EEC (Z_to_bv 5 2) 2%nat N2 P2.
ondn_kreg HS EClo EEC (Z_to_bv 5 3) 3%nat N3 P3.
ondn_kreg HS EClo EEC (Z_to_bv 5 4) 4%nat N4 P4.
ondn_kreg HS EClo EEC (Z_to_bv 5 8) 8%nat N8 P8.
ondn_kreg HS EClo EEC (Z_to_bv 5 9) 9%nat N9 P9.
ondn_kreg HS EClo EEC (Z_to_bv 5 18) 18%nat N18 P18.
ondn_kreg HS EClo EEC (Z_to_bv 5 19) 19%nat N19 P19.
ondn_reg HS (Z_to_bv 5 20) (w64 ONANN_S) P20 ltac:(unfold w64; vm_compute; reflexivity).
ondn_kreg HS EClo EEC (Z_to_bv 5 21) 21%nat N21 P21.
ondn_kreg HS EClo EEC (Z_to_bv 5 22) 22%nat N22 P22.
ondn_kreg HS EClo EEC (Z_to_bv 5 23) 23%nat N23 P23.
ondn_reg HS (Z_to_bv 5 24) (w64 SHADOW_OFF) P24 ltac:(unfold w64; vm_compute; reflexivity).
ondn_kreg HS EClo EEC (Z_to_bv 5 25) 25%nat N25 P25.
ondn_reg HS (Z_to_bv 5 26) (w64 (ONANN_S + 96)) P26 ltac:(unfold w64; vm_compute; reflexivity).
ondn_reg HS (Z_to_bv 5 27) (w64 (ONANN_S + 104)) P27 ltac:(unfold w64; vm_compute; reflexivity).
(* the spills of the two shadow addresses, read back after the notice *)
ondn_region HS 2%nat RGsl3.
pose proof (ondn_chunk_val _ _ _ _ _ _ _ _ _ 8 8 (SLit ONDN_SH96) RGsl3 ltac:(ondn_in) ltac:(lia)) as VS8.
pose proof (ondn_chunk_val _ _ _ _ _ _ _ _ _ 0 8 (SLit ONDN_SH104) RGsl3 ltac:(ondn_in) ltac:(lia)) as VS0.
cbn [base_val] in VS8, VS0.
try rewrite (EClo 9%nat ltac:(lia)) in VS8. try rewrite (EClo 9%nat ltac:(lia)) in VS0.
rewrite U9C in VS8, VS0.
change (N.to_nat 8) with 8%nat in VS8, VS0.
cbn [sv_denot] in VS8, VS0.
change (bv_unsigned (Z_to_bv 64 ONDN_SH96) mod 2 ^ (8 * Z.of_N 8)) with ONDN_SH96 in VS8.
change (bv_unsigned (Z_to_bv 64 ONDN_SH104) mod 2 ^ (8 * Z.of_N 8)) with ONDN_SH104 in VS0.
assert (USPC : spZ (ms_regs msC) = sp1)
  by (change (bv_unsigned (YK11.getr (ms_regs msC) (Z_to_bv 5 2)) = sp1); rewrite P2; unfold w64;
      apply unsigned_lit_small; lia).
pmkst HS.
(* what the call kept from its entry to notice's call *)
set (FL := flag_addr lyc ONANN_CID pos) in *.
assert (Hblin : forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly2 S2))
  by (intros bm Hb; exact (Permutation_in _ (Permutation_sym Hperm) Hb)).
assert (HSZ : forall a, ondn_ZA F sp1 a ->
  (spZ regs - ONANN_STK <= a < spZ regs) \/ dkg_nf ONANN_CID F FL a \/ inG TG.G_HARNESS_B a).
{ intros a [[Hz|Hz] | [[Hz|Hz] | [[Hz|Hz] | Hz]]].
  - right; left; right; left. change (fs_frame_bytes ONANN_CID / 8) with 64. lia.
  - right; left; left. change (fs_frame_bytes ONANN_CID) with 512. lia.
  - right; left; left. change (fs_frame_bytes ONANN_CID) with 512. lia.
  - left; lia.
  - right; left; left. change (fs_frame_bytes ONANN_CID) with 512. lia.
  - left; lia.
  - left; unfold ondn_Z4 in Hz; lia. }
assert (KN : acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W2 memN (spZ regs - ONANN_STK) (spZ regs)
  (onann_wr Bw b)).
{ apply (dk_kept_nfz_gw segs B LAWS transportb_segs_low TG.G_HARNESS_B lyc Sc ly2 S2 W memc mdc W2 mem2 md2 mem2
    memN (spZ regs - ONANN_STK) (spZ regs) ONANN_CID pos F FL (onann_wr Bw b) (ondn_ZA F sp1)
    HGX HARc HAR2 Hfrs Hblin HlyF EFdef eq_refl FFL ltac:(lia) ltac:(lia) HSZ HK).
  - intros a Ha Hn. apply K2N; [exact Ha | intros HH; apply Hn; left; exact HH |
      intros HH; apply Hn; right; left; exact HH | intros HH; apply Hn; right; right; left; exact HH |
      intros HH; apply Hn; right; right; right; exact HH].
  - intros a Ha. apply GC. apply HgrM. apply GB. apply GA. exact Ha. }
(* +0x3cc: notice, at TI.ti_notice timg_B, with ra = +0x3d0 *)
assert (EBR : BASE + ONDN_C3 = BASE + AF_on_announce + 0x3d0) by (unfold ONDN_C3; f_equal; lia).
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Qx =>
  change (SRr segs Wx (@cfg_at fx segs (TI.ti_notice timg_B) (ms_regs msC) memN mdC) Qx) end.
(* notice's stores are bytes of GOT: apart from n's 72 bytes, from its empty body, from the announce and from TF *)
assert (HAPN : notice_apart W2 memN (F + 112) (onann_dntc timg_B (onann_w1 timg_B Bw b) b) TF
  (onann_w1 timg_B Bw b)).
{ intros x Hx.
  assert (HwG : inG TG.G_HARNESS_B x)
    by exact (onann_wr_G Bw b x (onann_wr_dntc _ _ Bw b x Hx)).
  split; [intros Hr; unfold NTC_SIZE in Hr; exact (HFnG x ltac:(lia) HwG)|].
  split.
  - intros NB HgNB HlNB.
    assert (ENB : NB = ondn_bytes (TW.S_state (onann_w1 timg_B Bw b)) fp (F + ONANN_A) (onann_pv timg_B b)
      (onann_off (onann_w1 timg_B Bw b) b)).
    { apply (ondn_garr8_det (w_H W2) memN (F + 112)); [exact HgNB | exact HNBN |].
      rewrite HlNB. symmetry. exact (ondn_bytes_len _ _ _ _ _). }
    subst NB. rewrite ondn_bytes_body.
    rewrite (ondn_bytes_ann (TW.S_state (onann_w1 timg_B Bw b)) fp (F + ONANN_A) (onann_pv timg_B b)
      (onann_off (onann_w1 timg_B Bw b) b) ltac:(unfold ONANN_A; lia)).
    split; [unfold onann_dntc; cbn [TI.n_body length Z.of_nat]; intros Hr; lia|].
    intros _ Hr. unfold ANN_SIZE, ONANN_A in Hr. exact (HFnG x ltac:(lia) HwG).
  - exact (onann_apart_ntc TF Bw b (notice_wr (onann_w1 timg_B Bw b)
      (onann_dntc timg_B (onann_w1 timg_B Bw b) b)) Hapart
      (fun y Hy => onann_wr_dntc _ _ Bw b y Hy) x Hx). }
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HARN.
assert (TWN : tw_at TMAP_B (aview segs (w_H W2) memN) (onann_w1 timg_B Bw b)).
{ apply (tw_kept_GB (aview segs (w_H W2) memM)); [exact TWM|].
  intros b0 n0 i Hbn Hi.
  assert (Hg : inG TG.G_HARNESS_B (b0 + i)) by (apply (ondn_inG b0 n0); [exact Hbn | lia]).
  pose proof (inG_low segs B transportb_segs_low TG.G_HARNESS_B _ HGX Hg) as Hl. unfold kLowMemEnd in Hl.
  destruct (NZG _ Hg) as (NG1 & NG2 & NG3 & NG4).
  exact (KC (b0 + i) ltac:(lia) NG4). }
assert (EC3 : BASE + ONDN_C3 = 557208) by reflexivity.
eapply SRr_bind.
{ exact (HNC fx STK sp0 FP ly S W0 mem0 md0 ((ONANN_CID, pos) :: own) ly2 S2 W2 memN mdC (k + 0) (ms_regs msC)
    (F + 112) (onann_dntc timg_B (onann_w1 timg_B Bw b) b) TF (onann_w1 timg_B Bw b) B2
    HJ2
    ltac:(rewrite P1; apply (ret_ok_codeptr_v (PI := PI_transportb));
          [unfold ONDN_C3, AF_on_announce; lia | unfold ONDN_C3, AF_on_announce; reflexivity])
    ltac:(unfold raZ; rewrite P1, EC3; rewrite unsigned_lit_small; lia)
    (eq_trans P3 Hgp) (eq_trans P4 Htp) P11
    ltac:(rewrite USPC; pose proof (Z.div_mod sp1 32 ltac:(lia)) as D1; rewrite Hsp132, Z.add_0_r in D1;
          rewrite D1; replace (32 * (sp1 / 32)) with ((2 * (sp1 / 32)) * 16) by ring; apply Z.mod_mul; lia)
    ltac:(rewrite USPC; lia) ltac:(rewrite USPC; lia)
    (ondn_ntc_at B ly2 S2 W2 memN mdC (ms_regs msC) (onann_w1 timg_B Bw b) b F pos fp
       (TW.S_state (onann_w1 timg_B Bw b)) (onann_off (onann_w1 timg_B Bw b) b)
       LAWS HARN Hin2 ltac:(rewrite EFA2; reflexivity) HF0 HF64 HFc HFapp
       ltac:(rewrite USPC; lia) ltac:(rewrite USPC; lia)
       ltac:(intros a Ha; apply GC; apply HgrM; apply GB; apply GA; exact (proj1 (HFpres a Ha)))
       ltac:(intros i Hi; apply GC; apply HgrM; apply GB; apply GA; exact (proj1 (HFshpres i Hi)))
       ZSN HAshN eq_refl eq_refl ltac:(lia) HNBN HAvN HAnN Hpvr)
    (onann_tf_call B LAWS HRU HRE lyc Sc W memc mdc ly2 S2 W2 memN mdC pos regs (ms_regs msC) NOTICE_STK TF Bw b
       HARc HARN Hfrs Hperm EFA ESLO ESHI KN HTFG ltac:(rewrite USPC; lia) ltac:(rewrite USPC; lia) HTFat)
    (onann_rom_call B HRU HRE lyc Sc W memc W2 memN _ _ _ Hrom KN)
    TWN HNM
    HAPN
    ltac:(intros HD; exfalso; unfold onann_dntc in HD; cbn [TI.n_kind] in HD;
          unfold TS0.DIGINET_N_DESK, TC.N_DATA in HD; discriminate HD)
    ltac:(lia)). }
intros W3 c3 _ HPOST.
unfold transport_notice_post, transport_cg_post in HPOST. cbv beta in HPOST.
destruct HPOST as (ly3 & S3 & regs3 & mem3 & md4 & e3 & -> & He3 & HJ3 & HP3 & Hfr3 & Hperm3 & HK3 & Hmo3 & Htw3).
assert (He30 : e3 = 0) by (unfold NOTICE_EV in He3; lia). subst e3.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HAR3.
pose proof HJ3 as (_ & _ & (memS3 & HJi3 & _) & _). rewrite !Z.add_0_r in HJi3.
pose proof HJi3 as (_ & Hlyle3 & _). pose proof Hlyle3 as (_ & _ & _ & _ & _ & ELF3 & _ & _ & _ & ESLO3 & ESHI3 & _).
clear HJi3 memS3.
pose proof HJ1 as (_ & _ & (memS2j & HJi2j & _) & _).
pose proof HJi2j as (_ & Hlyle2j & _). pose proof Hlyle2j as (_ & _ & _ & _ & _ & ELF2j & _).
clear HJi2j memS2j.
assert (ELF3c : ly_F ly3 = ly_F lyc) by (rewrite <- HlyF, ELF3, ELF2j; reflexivity).
assert (EFA3 : forall c p, frame_addr ly3 c p = frame_addr lyc c p)
  by (intros c p; unfold frame_addr; rewrite ELF3c; reflexivity).
assert (Hfrs3 : frames S3 = (ONANN_CID, pos) :: frames Sc) by (rewrite Hfr3; exact Hfrs).
assert (Hperm3c : Permutation (ablocks B ly3 S3) (ablocks B lyc Sc))
  by (apply (Permutation_trans Hperm3); exact Hperm).
assert (Hbl3 : forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly3 S3))
  by (intros bm Hb; exact (Permutation_in _ (Permutation_sym Hperm3c) Hb)).
assert (Hin3 : In (ONANN_CID, pos) (frames S3)) by (rewrite Hfrs3; left; reflexivity).
(* what the call kept, from its entry to notice's return *)
assert (KC3 : acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W3 mem3 (spZ regs - ONANN_STK) (spZ regs)
  (onann_wr Bw b)).
{ apply (dk_kept_trans_nf_g segs B TG.G_HARNESS_B lyc Sc ly2 S2 W memc W2 memN W3 mem3
    (spZ regs - ONANN_STK) (spZ regs) (spZ (ms_regs msC) - NOTICE_STK) (spZ (ms_regs msC)) (onann_wr Bw b)
    (notice_wr (onann_w1 timg_B Bw b) (onann_dntc timg_B (onann_w1 timg_B Bw b) b)) (dkg_nf ONANN_CID F FL)).
  - lia.
  - lia.
  - intros c p. rewrite EFA. reflexivity.
  - intros f Hf. rewrite Hfrs. right. exact Hf.
  - exact Hblin.
  - intros b0 m0 i Hb Hi Hn.
    destruct (dkg_nf_sep_gw segs B LAWS transportb_segs_low lyc Sc ly2 S2 W2 mem2 md2 ONANN_CID pos F FL
      HAR2 Hfrs Hblin HlyF EFdef eq_refl FFL) as (N1' & N2' & N3' & N4').
    exact (N1' b0 m0 i Hb Hi Hn).
  - intros cid p a Hin Hr Hn.
    destruct (dkg_nf_sep_gw segs B LAWS transportb_segs_low lyc Sc ly2 S2 W2 mem2 md2 ONANN_CID pos F FL
      HAR2 Hfrs Hblin HlyF EFdef eq_refl FFL) as (N1' & N2' & N3' & N4').
    exact (N3' cid p a Hin Hr Hn).
  - exact KN.
  - exact HK3.
  - rewrite USPC. lia.
  - rewrite USPC. lia.
  - intros a Ha. left. exact (onann_wr_dntc _ _ Bw b a Ha). }
pose proof HK3 as (L1 & L2 & L3 & L4 & L5 & L6).
(* the bytes the after-notice code reads: the spills, the saved words and the frame's last word *)
assert (KSTK : forall a, sp1 <= a < spZ regs -> aview segs (w_H W3) mem3 a = aview segs (w_H W2) memN a).
{ intros a Ha. rewrite USPC in L1. rewrite L1 by lia. reflexivity. }
assert (KFRM : forall a, F <= a < F + 512 -> ~ onann_wr Bw b a ->
  aview segs (w_H W3) mem3 a = aview segs (w_H W2) memN a).
{ intros a Ha Hn. apply (L4 ONANN_CID pos a Hin2).
  - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFA2. change (fs_frame_bytes ONANN_CID) with 512. lia.
  - intros Hw. apply Hn. exact (onann_wr_dntc _ _ Bw b a Hw). }
assert (KFSH : forall i, 0 <= i < 64 -> aview segs (w_H W3) mem3 (SHADOW_OFF + F / 8 + i)
  = aview segs (w_H W2) memN (SHADOW_OFF + F / 8 + i)).
{ intros i Hi. apply (L4 ONANN_CID pos _ Hin2).
  - right. unfold in_zr, shadow_addr. cbn [fst snd]. rewrite EFA2.
    change (fs_frame_bytes ONANN_CID / 8) with 64. lia.
  - intros Hw. pose proof (onann_wr_G Bw b _ (onann_wr_dntc _ _ Bw b _ Hw)) as Hg.
    pose proof (inG_low segs B transportb_segs_low TG.G_HARNESS_B _ HGX Hg) as Hl.
    unfold kLowMemEnd, SHADOW_OFF in *. lia. }
assert (KSAV : forall a, sp1 + 64 <= a < spZ regs -> aview segs (w_H W3) mem3 a = aview segs (w_H W2) mem2 a).
{ intros a Ha. rewrite (KSTK a ltac:(lia)). apply K2N; [lia | ondn_no | ondn_no | ondn_no | ondn_no]. }
assert (KLAST : forall a, F + 504 <= a < F + 512 -> aview segs (w_H W3) mem3 a = aview segs (w_H W2) mem2 a).
{ intros a Ha.
  rewrite (KFRM a ltac:(lia)
    ltac:(intros Hw; exact (HFnG a ltac:(lia) (onann_wr_G Bw b a Hw)))).
  apply K2N; [lia | ondn_no | ondn_no | ondn_no | ondn_no]. }
assert (HSo : forall o, In o ONANN_SAVED -> 8 <= fst o <= 104).
{ intros o Ho. unfold ONANN_SAVED in Ho. cbn [In] in Ho.
  repeat (destruct Ho as [<- | Ho]; [cbn [fst]; lia|]). destruct Ho. }
(* the cut after notice *)
assert (CUR3 : onann_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw b pos F ly3 S3 W3 mem3 md4 0).
{ split; [replace (k + 0) with (k + 0 + 0) by lia; exact HJ3|].
  split; [lia|].
  split; [exact Hfrs3|].
  split; [exact Hperm3c|].
  split; [exact ELF3c|].
  split; [exact (mo_le_trans MT MTL _ _ _ _ _ Hmo Hmo3)|].
  split; [exact KC3|].
  split.
  - rewrite Forall_forall in Hsaved |- *. intros o Ho. rewrite <- (Hsaved o Ho).
    pose proof (HSo o Ho) as Hob. apply YCbq.rdword_ext. intros i Hi. apply KSAV. lia.
  - unfold ONANN_FBYTES in HFLw |- *. unfold FL in HFLw. rewrite <- HFLw.
    apply YCbq.rdword_ext. intros i Hi. apply KLAST. lia. }
(* the spill slots and the announce at the cut *)
assert (SLOT32 : onann_slot W3 mem3 sp1 32 (SHADOW_OFF + (ONANN_S + 112) / 8)).
{ unfold onann_slot. replace (SHADOW_OFF + (ONANN_S + 112) / 8) with ONDN_SH112 by reflexivity.
  apply ondn_rdword_of_val; [unfold ONDN_SH112; lia|].
  apply (ondn_vm_keepw (w_H W2) (w_H W3) (ms_mem msB) mem3); [exact VS32|].
  intros x Hx. rewrite (KSTK x ltac:(lia)). apply KBN; [lia | ondn_no | ondn_no]. }
assert (SLOT40 : onann_slot W3 mem3 sp1 40 (ONANN_S + 112)).
{ unfold onann_slot. apply ondn_rdword_of_val; [rewrite CS; lia|].
  apply (ondn_vm_keepw (w_H W2) (w_H W3) (ms_mem msB) mem3); [exact VS40|].
  intros x Hx. rewrite (KSTK x ltac:(lia)). apply KBN; [lia | ondn_no | ondn_no]. }
assert (SLOT8 : onann_slot W3 mem3 sp1 8 (SHADOW_OFF + (ONANN_S + 96) / 8)).
{ unfold onann_slot. replace (SHADOW_OFF + (ONANN_S + 96) / 8) with ONDN_SH96 by reflexivity.
  apply ondn_rdword_of_val; [unfold ONDN_SH96; lia|].
  apply (ondn_vm_keepw (w_H W2) (w_H W3) memN mem3); [exact VS8|].
  intros x Hx. apply (KSTK x ltac:(lia)). }
assert (SLOT0 : onann_slot W3 mem3 sp1 0 (SHADOW_OFF + (ONANN_S + 104) / 8)).
{ unfold onann_slot. replace (SHADOW_OFF + (ONANN_S + 104) / 8) with ONDN_SH104 by reflexivity.
  apply ondn_rdword_of_val; [unfold ONDN_SH104; lia|].
  apply (ondn_vm_keepw (w_H W2) (w_H W3) memN mem3); [exact VS0|].
  intros x Hx. apply (KSTK x ltac:(lia)). }
assert (SLOT24 : onann_slot W3 mem3 sp1 24 now).
{ unfold onann_slot in HS24 |- *. rewrite <- HS24. apply YCbq.rdword_ext. intros i Hi.
  rewrite (KSTK (sp1 + 24 + i) ltac:(lia)). apply K2N; [lia | ondn_no | ondn_no | ondn_no | ondn_no]. }
assert (SLOT16 : onann_slot W3 mem3 sp1 16 (F + ONANN_A)).
{ unfold onann_slot in HS16 |- *. rewrite <- HS16. apply YCbq.rdword_ext. intros i Hi.
  rewrite (KSTK (sp1 + 16 + i) ltac:(lia)). apply K2N; [lia | ondn_no | ondn_no | ondn_no | ondn_no]. }
assert (SLOT48 : onann_slot W3 mem3 sp1 48 (SHADOW_OFF + (fp + 30) / 8)).
{ unfold onann_slot in HS48 |- *. rewrite <- HS48. apply YCbq.rdword_ext. intros i Hi.
  rewrite (KSTK (sp1 + 48 + i) ltac:(lia)). apply K2N; [lia | ondn_no | ondn_no | ondn_no | ondn_no]. }
assert (SLOT56 : onann_slot W3 mem3 sp1 56 (fp + 30)).
{ unfold onann_slot in HS56 |- *. rewrite <- HS56. apply YCbq.rdword_ext. intros i Hi.
  rewrite (KSTK (sp1 + 56 + i) ltac:(lia)). apply K2N; [lia | ondn_no | ondn_no | ondn_no | ondn_no]. }
assert (HAOK3 : onann_a_ok W3 mem3 F buf b).
{ split; [|split; [|split; [|split]]].
  - eapply garr8_frame; [exact HAvN|]. intros a Ha. rewrite length_map in Ha.
    pose proof (ondn_annf_len (skipn 15 (DSpec.fr_body b))) as HL.
    apply ondn_mbyte_of_aview2. apply KFRM; [unfold ONANN_A in *; lia|].
    intros Hw. exact (HFnG a ltac:(unfold ONANN_A in *; lia) (onann_wr_G Bw b a Hw)).
  - eapply garr8_frame; [exact HAnN|]. intros a Ha. rewrite length_map in Ha.
    pose proof (ondn_annf_len (skipn 24 (DSpec.fr_body b))) as HL.
    apply ondn_mbyte_of_aview2. apply KFRM; [unfold ONANN_A in *; lia|].
    intros Hw. exact (HFnG a ltac:(unfold ONANN_A in *; lia) (onann_wr_G Bw b a Hw)).
  - rewrite <- HAu. apply YCbq.rdword_ext. intros i Hi.
    rewrite (KFRM (F + ONANN_A + 24 + i) ltac:(unfold ONANN_A; lia)
      ltac:(intros Hw; exact (HFnG (F + ONANN_A + 24 + i) ltac:(unfold ONANN_A; lia) (onann_wr_G Bw b _ Hw)))).
    apply K2N; [unfold ONANN_A; lia | ondn_no | ondn_no | ondn_no | ondn_no].
  - rewrite <- HAl. apply YCbq.rdword_ext. intros i Hi.
    rewrite (KFRM (F + ONANN_A + 32 + i) ltac:(unfold ONANN_A; lia)
      ltac:(intros Hw; exact (HFnG (F + ONANN_A + 32 + i) ltac:(unfold ONANN_A; lia) (onann_wr_G Bw b _ Hw)))).
    apply K2N; [unfold ONANN_A; lia | ondn_no | ondn_no | ondn_no | ondn_no].
  - intros i Hi. rewrite (KFSH i ltac:(lia)). exact (HAshN i Hi). }
(* f at the cut after notice *)
assert (USP3 : spZ regs3 = sp1)
  by (change (bv_unsigned (YK11.getr regs3 (Z_to_bv 5 2)) = sp1); rewrite (HP3 2 ltac:(hnf; lia)), P2;
      unfold w64; apply unsigned_lit_small; lia).
destruct (onann_f30 B MT LAWS0 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw'
  pos sp1 F ly3 S3 W3 mem3 md4 0 regs3 NOTICE_STK HFIX CUR3 ltac:(rewrite USP3; lia) ltac:(rewrite USP3; lia))
  as (Zfp0 & Zfpc & Zfp8 & ZfpF & Zg8f & Zfake & Zrdok & Zoffw & Zcmdr & Zcmdv & Zcmdg & Zcmdsh & Zf32 & Zbuf0 &
      Zbufg & Zbufs & Zbufw & ZbufG).
assert (HSHFfp : fp + 64 <= SHADOW_OFF \/ SHADOW_OFF + 2 ^ 44 <= fp).
{ pose proof Zrdok as (_ & _ & _ & Zamr & _). unfold FRAME_F_SIZE in Zamr.
  unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Zamr.
  destruct Zamr as [HL | (HH1 & HH2)]; [left | right]; unfold SHADOW_OFF; lia. }
(* ---- run 4, +0x3d0 .. +0x3e8 ---- *)
assert (P9' : YK11.getr regs3 9 = w64 sp1) by exact (eq_trans (HP3 9 ltac:(hnf; lia)) P9).
assert (V48N : val_mem segs (mrestrict (w_H W3) mem3) (sp1 + 48) 8 (SHADOW_OFF + (fp + 30) / 8))
  by (apply val_mem_of_rdword; exact SLOT48).
assert (V56N : val_mem segs (mrestrict (w_H W3) mem3) (sp1 + 56) 8 (fp + 30))
  by (apply val_mem_of_rdword; exact SLOT56).
try clear HS. try clear SHOK.
pose proof (ondn_entry4 (fx := fx) W3 regs3 mem3 sp1 fp (DSpec.fr_cmd b) P9' V48N V56N Zcmdsh Zcmdv ltac:(lia)
  Zfp0 ltac:(unfold FRAME_F_SIZE in Zfpc; lia) HSHFfp ltac:(unfold FRAME_F_SIZE in Zfpc; lia) Hsp146 Hsp47) as HS.
set (ED := ondn_E4 regs3 fp (DSpec.fr_cmd b)) in HS.
assert (HEID : img_env VAL A_LIM ED) by (unfold ED, ondn_E4; apply Eimg_env).
assert (EED : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew ED n = YK11.getr regs3 r)
  by (intros n r Hn; exact (ondn_ew4 regs3 fp (DSpec.fr_cmd b) n r Hn)).
assert (SHOKD : sh_ok segs ONDN_BX (@nil shent) ED (mrestrict (w_H W3) mem3)) by constructor.
rewrite P1.
lazymatch goal with |- SRr _ ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Qx =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + ONDN_C3)) mm rom) mdx) Qx) end.
pose proof HJ3 as HJD.
paj_run_to_tok RUNTO HS HJD SHOKD ONDN_B0 ONDN_C4.
{ ondn_awr_rs.
  repeat (apply awr_ok_x_cons;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |]).
  apply awr_ok_x_nil. }
ondn_name_md mdD.
ondn_lo HS ED EDlo msD.
assert (KD : forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W3) (ms_mem msD) a = aview segs (w_H W3) mem3 a).
{ intros a Ha. apply (kept_of_frame _ _ _ _ _ (fun _ => False) HFr); [| exact Ha | tauto].
  intros b0 wlo whi x Hiw Hx. cbv beta. ondn_win Hiw Hx ltac:(lia). }
assert (GD : forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) (ms_mem msD) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
clear HF HFr HG.
assert (W34D : ew ED 34 = Z_to_bv 64 (DSpec.fr_cmd b)).
{ unfold ED. change (34%nat) with (32 + 2)%nat. exact (ondn_ew4_x regs3 fp (DSpec.fr_cmd b) 2 ltac:(lia)). }
ondn_reg HS (Z_to_bv 5 10) (w64 (DSpec.fr_cmd b)) X10
  ltac:(cbn [sv_denot]; try rewrite (EDlo 34%nat ltac:(lia));
        rewrite W34D, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
ondn_reg HS (Z_to_bv 5 11) (w64 224) X11 ltac:(unfold w64; vm_compute; reflexivity).
(* the registers run 4 starts from, and the ones it leaves *)
assert (Y2 : YK11.getr regs3 2 = w64 sp1) by exact (eq_trans (HP3 2 ltac:(hnf; lia)) P2).
assert (Y3 : YK11.getr regs3 3 = YK11.getr regs 3) by exact (eq_trans (HP3 3 ltac:(hnf; lia)) P3).
assert (Y4 : YK11.getr regs3 4 = YK11.getr regs 4) by exact (eq_trans (HP3 4 ltac:(hnf; lia)) P4).
assert (Y8 : YK11.getr regs3 8 = w64 (spZ regs)) by exact (eq_trans (HP3 8 ltac:(hnf; lia)) P8).
assert (Y18 : YK11.getr regs3 18 = w64 (SHADOW_OFF + F / 8)) by exact (eq_trans (HP3 18 ltac:(hnf; lia)) P18).
assert (Y19 : YK11.getr regs3 19 = w64 F) by exact (eq_trans (HP3 19 ltac:(hnf; lia)) P19).
assert (Y20 : YK11.getr regs3 20 = w64 ONANN_S) by exact (eq_trans (HP3 20 ltac:(hnf; lia)) P20).
assert (Y22 : YK11.getr regs3 22 = w64 fp) by exact (eq_trans (HP3 22 ltac:(hnf; lia)) P22).
assert (Y23 : YK11.getr regs3 23 = w64 (onann_off (onann_w1 timg_B Bw b) b))
  by exact (eq_trans (HP3 23 ltac:(hnf; lia)) P23).
assert (Y24 : YK11.getr regs3 24 = w64 SHADOW_OFF) by exact (eq_trans (HP3 24 ltac:(hnf; lia)) P24).
assert (Y25 : YK11.getr regs3 25 = w64 F) by exact (eq_trans (HP3 25 ltac:(hnf; lia)) P25).
assert (Y26 : YK11.getr regs3 26 = w64 (ONANN_S + 96)) by exact (eq_trans (HP3 26 ltac:(hnf; lia)) P26).
assert (Y27 : YK11.getr regs3 27 = w64 (ONANN_S + 104)) by exact (eq_trans (HP3 27 ltac:(hnf; lia)) P27).
ondn_kreg HS EDlo EED (Z_to_bv 5 2) 2%nat Y2 X2.
ondn_kreg HS EDlo EED (Z_to_bv 5 3) 3%nat Y3 X3.
ondn_kreg HS EDlo EED (Z_to_bv 5 4) 4%nat Y4 X4.
ondn_kreg HS EDlo EED (Z_to_bv 5 8) 8%nat Y8 X8.
ondn_kreg HS EDlo EED (Z_to_bv 5 9) 9%nat P9' X9.
ondn_kreg HS EDlo EED (Z_to_bv 5 18) 18%nat Y18 X18.
ondn_kreg HS EDlo EED (Z_to_bv 5 19) 19%nat Y19 X19.
ondn_kreg HS EDlo EED (Z_to_bv 5 20) 20%nat Y20 X20.
ondn_kreg HS EDlo EED (Z_to_bv 5 22) 22%nat Y22 X22.
ondn_kreg HS EDlo EED (Z_to_bv 5 23) 23%nat Y23 X23.
ondn_kreg HS EDlo EED (Z_to_bv 5 24) 24%nat Y24 X24.
ondn_kreg HS EDlo EED (Z_to_bv 5 25) 25%nat Y25 X25.
ondn_kreg HS EDlo EED (Z_to_bv 5 26) 26%nat Y26 X26.
ondn_kreg HS EDlo EED (Z_to_bv 5 27) 27%nat Y27 X27.
(* everything the two cuts carry, at any memory this piece's last runs leave *)
assert (MOVE : forall mX, (forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W3) mX a = aview segs (w_H W3) mem3 a) ->
  (forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) mX a) ->
  acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W3 mX (spZ regs - ONANN_STK) (spZ regs) (onann_wr Bw b) /\
  tw_at TMAP_B (aview segs (w_H W3) mX) B2 /\
  onann_a_ok W3 mX F buf b /\
  onann_slots_arm W3 mX sp1 /\ onann_slots_ntf W3 mX sp1 /\
  onann_slot W3 mX sp1 16 (F + ONANN_A) /\ onann_slot W3 mX sp1 24 now /\
  Forall (fun o : Z * Z => rdword (aview segs (w_H W3) mX) (spZ regs - fst o) =
     Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) ONANN_SAVED /\
  rdword (aview segs (w_H W3) mX) (F + ONANN_FBYTES - 8) = Some (flag_addr lyc ONANN_CID pos)).
{ intros mX HKx HGx.
  assert (HKept : acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W3 mX (spZ regs - ONANN_STK) (spZ regs)
    (onann_wr Bw b)).
  { apply (dk_kept_step_gw segs B LAWS transportb_segs_low TG.G_HARNESS_B lyc Sc W memc mdc W3 mem3 mX
      (spZ regs - ONANN_STK) (spZ regs) (onann_wr Bw b) (fun _ => False) HARc KC3
      ltac:(intros a Ha _; exact (HKx a Ha)) HGx);
    [intros a HFx _; destruct HFx | intros b0 m0 i _ _ HFx; destruct HFx |
     intros a HFx _ _ _ _; destruct HFx | intros c p a _ _ HFx; destruct HFx]. }
  pose proof CUR3 as (_ & _ & _ & _ & _ & _ & _ & HsavX & HflX).
  split; [exact HKept|].
  split.
  { apply (tw_kept_GB (aview segs (w_H W3) mem3)); [exact Htw3|].
    intros b0 n0 i Hbn Hi.
    assert (Hg : inG TG.G_HARNESS_B (b0 + i)) by (apply (ondn_inG b0 n0); [exact Hbn | lia]).
    pose proof (inG_low segs B transportb_segs_low TG.G_HARNESS_B _ HGX Hg) as Hl. unfold kLowMemEnd in Hl.
    apply HKx. lia. }
  split.
  { pose proof HAOK3 as (A1 & A2 & A3 & A4 & A5). split; [|split; [|split; [|split]]].
    - eapply garr8_frame; [exact A1|]. intros a Ha. rewrite length_map in Ha.
      pose proof (ondn_annf_len (skipn 15 (DSpec.fr_body b))) as HL.
      apply ondn_mbyte_of_aview2. apply HKx. unfold ONANN_A in *. lia.
    - eapply garr8_frame; [exact A2|]. intros a Ha. rewrite length_map in Ha.
      pose proof (ondn_annf_len (skipn 24 (DSpec.fr_body b))) as HL.
      apply ondn_mbyte_of_aview2. apply HKx. unfold ONANN_A in *. lia.
    - rewrite <- A3. apply YCbq.rdword_ext. intros i Hi. apply HKx. unfold ONANN_A in *. lia.
    - rewrite <- A4. apply YCbq.rdword_ext. intros i Hi. apply HKx. unfold ONANN_A in *. lia.
    - intros i Hi. rewrite (HKx (SHADOW_OFF + F / 8 + i) ltac:(unfold SHADOW_OFF; lia)). exact (A5 i Hi). }
  split.
  { split; unfold onann_slot in SLOT32, SLOT40 |- *.
    - rewrite <- SLOT32. apply YCbq.rdword_ext. intros i Hi. apply HKx. lia.
    - rewrite <- SLOT40. apply YCbq.rdword_ext. intros i Hi. apply HKx. lia. }
  split.
  { split; unfold onann_slot in SLOT8, SLOT0 |- *.
    - rewrite <- SLOT8. apply YCbq.rdword_ext. intros i Hi. apply HKx. lia.
    - rewrite <- SLOT0. apply YCbq.rdword_ext. intros i Hi. apply HKx. lia. }
  split.
  { unfold onann_slot in SLOT16 |- *. rewrite <- SLOT16. apply YCbq.rdword_ext. intros i Hi. apply HKx. lia. }
  split.
  { unfold onann_slot in SLOT24 |- *. rewrite <- SLOT24. apply YCbq.rdword_ext. intros i Hi. apply HKx. lia. }
  split.
  { rewrite Forall_forall in HsavX |- *. intros o Ho. rewrite <- (HsavX o Ho).
    pose proof (HSo o Ho) as Hob. apply YCbq.rdword_ext. intros i Hi. apply HKx. lia. }
  rewrite <- HflX. apply YCbq.rdword_ext. intros i Hi. apply HKx. unfold ONANN_FBYTES in *. lia. }
(* +0x3e8: `bne a0, a1`, taken up again from a state with no region *)
pmkst HS.
clear HS SHOKD.
set (rD := ms_regs msD) in *. set (mD := ms_mem msD) in *. clearbody rD mD.
pose proof (ondn_entry0 (fx := fx) W3 rD mD ONDN_C4) as HS.
assert (HEIE : img_env VAL A_LIM (ondn_E2 rD)) by (unfold ondn_E2; apply Eimg_env).
assert (EEE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (ondn_E2 rD) n = YK11.getr rD r)
  by (intros n r Hn; exact (ondn_ew2 rD n r Hn)).
assert (SHOKE : sh_ok segs ONDN_BX (@nil shent) (ondn_E2 rD) (mrestrict (w_H W3) mD)) by constructor.
lazymatch goal with |- SRr _ ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Qx =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + ONDN_C4)) mm rom) mdx) Qx) end.
assert (D10 : sv_denot (ondn_E2 rD) (SOff 10 0) = Z_to_bv 64 (DSpec.fr_cmd b))
  by (cbn [sv_denot]; rewrite (EEE 10%nat (Z_to_bv 5 10) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact X10).
assert (D11b : sv_denot (ondn_E2 rD) (SOff 11 0) = Z_to_bv 64 224)
  by (cbn [sv_denot]; rewrite (EEE 11%nat (Z_to_bv 5 11) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact X11).
pose proof HJD as HJE.
psrr_branch_tok RUN BR HS SHOKE ONDN_B0.
- (* taken: the command byte is not 0xe0, so it is 0xe1: the cut onann_e1_at *)
  cbn [branch_taken] in Hc. rewrite D10, D11b, (ondn_eqb (DSpec.fr_cmd b) 224 ltac:(lia) ltac:(lia)) in Hc.
  apply negb_true_iff, Z.eqb_neq in Hc.
  destruct (onann_ign_false b Hig) as ([Hcmd | Hcmd] & Hbl);
    [exfalso; apply Hc; rewrite Hcmd; reflexivity|].
  paj_run_to_tok RUNTO HS HJE SHOKE ONDN_B0 ONANN_E1.
  { ondn_awr_rs. apply awr_ok_x_nil. }
  ondn_name_md mdE.
  ondn_lo HS (ondn_E2 rD) EElo msE.
  assert (KE : forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W3) (ms_mem msE) a = aview segs (w_H W3) mem3 a).
  { intros a Ha. rewrite <- (KD a Ha).
    apply (kept_of_frame _ _ _ _ _ (fun _ => False) HFr); [| exact Ha | tauto].
    intros b0 wlo whi x Hiw Hx. cbv beta. ondn_win Hiw Hx ltac:(lia). }
  assert (GE : forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) (ms_mem msE) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG (GD a Ha))).
  destruct (MOVE (ms_mem msE) KE GE) as (MK & MTW & MA & MARM & MNTF & MS16 & MS24 & MSAV & MFL).
  ondn_kreg HS EElo EEE (Z_to_bv 5 2) 2%nat X2 Z2.
  ondn_kreg HS EElo EEE (Z_to_bv 5 3) 3%nat X3 Z3.
  ondn_kreg HS EElo EEE (Z_to_bv 5 4) 4%nat X4 Z4.
  ondn_kreg HS EElo EEE (Z_to_bv 5 8) 8%nat X8 Z8.
  ondn_kreg HS EElo EEE (Z_to_bv 5 9) 9%nat X9 Z9.
  ondn_kreg HS EElo EEE (Z_to_bv 5 18) 18%nat X18 Z18.
  ondn_kreg HS EElo EEE (Z_to_bv 5 19) 19%nat X19 Z19.
  ondn_kreg HS EElo EEE (Z_to_bv 5 20) 20%nat X20 Z20.
  ondn_kreg HS EElo EEE (Z_to_bv 5 22) 22%nat X22 Z22.
  ondn_kreg HS EElo EEE (Z_to_bv 5 23) 23%nat X23 Z23.
  ondn_kreg HS EElo EEE (Z_to_bv 5 24) 24%nat X24 Z24.
  ondn_kreg HS EElo EEE (Z_to_bv 5 25) 25%nat X25 Z25.
  ondn_kreg HS EElo EEE (Z_to_bv 5 26) 26%nat X26 Z26.
  ondn_kreg HS EElo EEE (Z_to_bv 5 27) 27%nat X27 Z27.
  pmkst HS.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Qx =>
    change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + ONANN_E1)) mm rom) mdx) Qx) end.
  apply (E1A LAWS0 CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos
    sp1 F B2 ly3 S3 W3 (ms_mem msE) mdE (ms_regs msE) HFIX).
  + split.
    { split; [replace (k + 0) with (k + 0 + 0) by lia; exact HJE|].
      split; [lia|]. split; [exact Hfrs3|]. split; [exact Hperm3c|]. split; [exact ELF3c|].
      split; [exact (mo_le_trans MT MTL _ _ _ _ _ Hmo Hmo3)|].
      split; [exact MK|]. split; [exact MSAV|]. exact MFL. }
    split; [exact MTW|].
    split; [split; [exact HCN|]; exists dv; exact EB2|].
    split; [exact Hcmd|].
    split; [exact (HKE1 Hcmd)|].
    split; [exact Hgf2|].
    split; [exact MA|].
    split; [exact MARM|]. split; [exact MNTF|]. exact MS16.
  + split; [split; [split; [exact Z2 | split; [exact Z3 | split; [exact Z4 | split; [exact Z8 |
      split; [exact Z9 | split; [exact Z18 | split; [exact Z19 | exact Z25]]]]]]] |
      split; [exact Z20 | exact Z24]] |].
    split; [exact Z23|]. split; [exact Z22|]. split; [exact Z26 | exact Z27].
- (* not taken: the command byte is 0xe0: the cut onann_e0_at *)
  cbn [branch_taken] in Hc. rewrite D10, D11b, (ondn_eqb (DSpec.fr_cmd b) 224 ltac:(lia) ltac:(lia)) in Hc.
  apply negb_false_iff, Z.eqb_eq in Hc.
  paj_run_to_tok RUNTO HS HJE SHOKE ONDN_B0 ONANN_E0.
  { ondn_awr_rs. apply awr_ok_x_nil. }
  ondn_name_md mdE.
  ondn_lo HS (ondn_E2 rD) EElo msE.
  assert (KE : forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W3) (ms_mem msE) a = aview segs (w_H W3) mem3 a).
  { intros a Ha. rewrite <- (KD a Ha).
    apply (kept_of_frame _ _ _ _ _ (fun _ => False) HFr); [| exact Ha | tauto].
    intros b0 wlo whi x Hiw Hx. cbv beta. ondn_win Hiw Hx ltac:(lia). }
  assert (GE : forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) (ms_mem msE) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG (GD a Ha))).
  destruct (MOVE (ms_mem msE) KE GE) as (MK & MTW & MA & MARM & MNTF & MS16 & MS24 & MSAV & MFL).
  ondn_kreg HS EElo EEE (Z_to_bv 5 2) 2%nat X2 Z2.
  ondn_kreg HS EElo EEE (Z_to_bv 5 3) 3%nat X3 Z3.
  ondn_kreg HS EElo EEE (Z_to_bv 5 4) 4%nat X4 Z4.
  ondn_kreg HS EElo EEE (Z_to_bv 5 8) 8%nat X8 Z8.
  ondn_kreg HS EElo EEE (Z_to_bv 5 9) 9%nat X9 Z9.
  ondn_kreg HS EElo EEE (Z_to_bv 5 18) 18%nat X18 Z18.
  ondn_kreg HS EElo EEE (Z_to_bv 5 19) 19%nat X19 Z19.
  ondn_kreg HS EElo EEE (Z_to_bv 5 20) 20%nat X20 Z20.
  ondn_kreg HS EElo EEE (Z_to_bv 5 24) 24%nat X24 Z24.
  ondn_kreg HS EElo EEE (Z_to_bv 5 25) 25%nat X25 Z25.
  pmkst HS.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Qx =>
    change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + ONANN_E0)) mm rom) mdx) Qx) end.
  apply (E0A LAWS0 CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos
    sp1 F B2 ly3 S3 W3 (ms_mem msE) mdE (ms_regs msE) HFIX).
  + split.
    { split; [replace (k + 0) with (k + 0 + 0) by lia; exact HJE|].
      split; [lia|]. split; [exact Hfrs3|]. split; [exact Hperm3c|]. split; [exact ELF3c|].
      split; [exact (mo_le_trans MT MTL _ _ _ _ _ Hmo Hmo3)|].
      split; [exact MK|]. split; [exact MSAV|]. exact MFL. }
    split; [exact MTW|].
    split; [split; [exact HCN|]; exists dv; exact EB2|].
    split; [exact Hc|].
    split; [exact (HKE0 Hc)|].
    split; [exact Hgf2|].
    split; [exact Hri2|].
    split; [exact MARM|]. exact MS24.
  + split; [split; [exact Z2 | split; [exact Z3 | split; [exact Z4 | split; [exact Z8 |
      split; [exact Z9 | split; [exact Z18 | split; [exact Z19 | exact Z25]]]]]]] |
      split; [exact Z20 | exact Z24]].
Qed.
End dn.
