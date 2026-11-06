(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Mem.v, with its module paths and module names changed; 1136 of its 1210 lines of code are new or changed and 413 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/TickRetx.v, with its module names, addresses and numbers changed; 1410 of its 1570 lines of code are new or changed and 1050 lines of the source are left out. *)
(* on_announce_seg_fn: Theorem onann_piece_fn : onann_fn_stmt (lib/A/Prog/OnannCut.v), the foreign-notice piece of
   the walk of on_announce on fuzz_transport.asan (0x87a74 = transport_sigma TS_on_announce), code +0x58c .. +0x658
   (0x88000 .. 0x880cc), from the cut onann_fn_at to the cuts onann_sl2_at (+0x65c) and onann_fnrel_at (+0x73c).
   What the code does (a0 = s + 136, a1 = its shadow byte, s1 = sp1, s2 = the frame F, s3 = its first shadow byte,
   s6 = fp, s8 = the shadow base, s9 = s + 104, s10 = the shadow byte of s + 112):
     run 1  +0x58c .. +0x608  the check of the 4-byte store at s + 136 (g_s's zero shadow, trans_onann_cells);
                              s5 = fn = F + 448; the store of 1 at s + 136 (g_s.foreign = 1, :216, Bf =
                              TW.set_S_foreign B2 1, row 4 of onann_wr); fn's shadow bytes 56 .. 64 := 0 (fn usable);
                              the 4-byte store of 6 (N_FOREIGN) at fn; the check of the 4-byte load at s + 112 and
                              a1 = S_state Bf (the store of :216 keeps it); the stores at fn + 4 (state), fn + 8
                              (8 zero bytes: old, reason) and fn + 16 (fp); the check of the 8-byte store at fn + 24,
                              whose shadow byte 59 the run itself set to 0 (resolved through the alias of
                              `srli a0, 3; add a0, s8` with s8 pinned to the shadow base); a = F + 256 (from
                              sp1 + 56) stored at fn + 24; a0 = fn + 32, a1 = 0, a2 = 40;
     +0x60c                   __asan_memset (TransportGCg.v gx_intrin_at): fn's bytes 32 .. 71 := 0;
     run 2  +0x610 .. +0x638  the checks of the 8-byte loads at s + 96 and s + 104 (their shadow bytes from
                              sp1 + 8 and sp1 + 16), s7 = F (from sp1 + 40), a2 = notify, a0 = notify_ctx, a1 = fn;
     +0x63c                   `jalr a2`: notice at TI.ti_notice timg_A, through the premise transport_notice_cg in
                              the same G journal (the 72 bytes at fn read as trans_ntc_at with onann_fntc Bf b;
                              the call's kept facts fold with dk_kept_trans_nf_g);
     run 3  +0x640 .. +0x654  the check of the 4-byte load at s + 112 (s10) and s5 = S_state B3, a0 = s5 - 1 (32-bit),
                              a1 = 1;
     +0x658                   `bltu a1, a0`, taken up again from a state with no region: a state outside
                              {S_WAKING, S_ONLINE} goes to onann_fnrel_at (+0x73c) with Bw' = B3, any other to
                              onann_sl2_at (+0x65c).
   Lemmas of note: ofn_ltu1 (the `addiw a0, s5, -1; bltu a1, a0` test is the model's state test), ofn_nb (fn's 72
   bytes), ofn_ntc_at (trans_ntc_at at fn), ofn_apart (notice_apart; ofn_garr8_det reads the announce pointer off
   any byte list the clause quantifies over), ofn_bf_state / ofn_bf_gfn (the store of :216 keeps g_s.state and
   g_fail_next), ofn_b3_state / ofn_b3_gfn (the foreign notice's GOT.foreign store keeps them). *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c YO0f.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportSyms DgnTransportList DgnTransportAddr DgnTransportPa DgnTransportImg DgnTransportPaLib YC4b YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG.
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import on_announce_cg OnannCut on_announce_seg_kit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import SlostNtcKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require TransportGNotice.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TSess0 TSess TCb TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TNotifyFacts.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require WalkNotify.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Mem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module LMem := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Mem.
Module FCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.AsanCells.
Module WN := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T.WalkNotify.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 1. The symbolic states                                              *)
(* ------------------------------------------------------------------ *)

(* The shadow byte of g_s.notify (s + 96); s + 104, s + 112 and s + 136 have the next, the second and the fifth. *)
Definition OFN_SH : Z := 2148220740.
Lemma ofn_sh_eq : OFN_SH = SHADOW_OFF + (ONANN_S + 96) / 8 /\ OFN_SH + 1 = SHADOW_OFF + (ONANN_S + 104) / 8 /\
  OFN_SH + 2 = SHADOW_OFF + (ONANN_S + 112) / 8 /\ OFN_SH + 5 = SHADOW_OFF + (ONANN_S + 136) / 8.
Proof. repeat split; reflexivity. Qed.
(* fn, the foreign notice, at F + 448; its 72 bytes end at F + 520. *)
Definition OFN_FN : Z := 448.
Lemma ofn_fn_fits : OFN_FN + NTC_SIZE = 520 /\ ONANN_A + ANN_SIZE = 276.
Proof. split; reflexivity. Qed.
(* The return address of the call of notice (`jalr a2` at +0x63c) and the pc of `bltu a1, a0` (+0x658). *)
Definition OFN_RET : Z := ONANN_FN + 0xb4.
Definition OFN_BR : Z := ONANN_FN + 0xcc.

(* run 1: fn's nine shadow bytes 56 .. 64 (base s3, atom 19), fn's first 32 bytes (base s2, atom 18), g_s's
   notify / notify_ctx / state and the written foreign, the four shadow bytes of g_s read by the checks, and the
   spill slots sp1 + 8 .. sp1 + 56 (base s1, atom 9). *)
Definition OFN_R_sh : YP09.region := YP09.mkRegion (Some 19%nat) 56 65 56 65 [].
Definition OFN_R_fn : YP09.region := YP09.mkRegion (Some 18%nat) 448 480 448 480 [].
Definition OFN_R_gs : YP09.region :=
  YP09.mkRegion None (ONANN_S + 96) (ONANN_S + 140) (ONANN_S + 136) (ONANN_S + 140)
    [YP09.mkChunk (ONANN_S + 96) (YP09.CVal 8 (SOff 32 0)); YP09.mkChunk (ONANN_S + 104) (YP09.CVal 8 (SOff 33 0));
     YP09.mkChunk (ONANN_S + 112) (YP09.CVal 4 (SOff 34 0))].
Definition OFN_R_shg : YP09.region :=
  YP09.mkRegion None OFN_SH (OFN_SH + 6) 0 0
    [YP09.mkChunk OFN_SH (YP09.CVal 1 (SLit 0)); YP09.mkChunk (OFN_SH + 1) (YP09.CVal 1 (SLit 0));
     YP09.mkChunk (OFN_SH + 2) (YP09.CVal 1 (SLit 0)); YP09.mkChunk (OFN_SH + 5) (YP09.CVal 1 (SLit 0))].
Definition OFN_R_slot : YP09.region :=
  YP09.mkRegion (Some 9%nat) 8 64 0 0
    [YP09.mkChunk 8 (YP09.CVal 8 (SLit OFN_SH)); YP09.mkChunk 16 (YP09.CVal 8 (SLit (OFN_SH + 1)));
     YP09.mkChunk 24 (YP09.CVal 8 (SLit (ONANN_S + 96))); YP09.mkChunk 40 (YP09.CVal 8 (SOff 18 0));
     YP09.mkChunk 48 (YP09.CVal 8 (SLit (ONANN_S + 112))); YP09.mkChunk 56 (YP09.CVal 8 (SOff 18 256))].
(* The shadow address of fn + 24 is `(s2 >> 3) + s8` with s8 the shadow base: the alias names it s3 (atom 19), so
   the instrumented check of the 8-byte store reads the frame's shadow byte 59, which the run set to 0. *)
Definition OFN_FACTS : facts :=
  mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (18%nat, mkAF 4096 (2 ^ 47) 6);
           (19%nat, mkAF (SHADOW_OFF + 512) (SHADOW_OFF + 2 ^ 44) 3); (34%nat, mkAF 0 (2 ^ 32 - 1) 0)] []
    [(SAlu ALU_ADD (SAlu ALU_SRL (SOff 18 0) (SLit 3)) (SLit SHADOW_OFF), SOff 19 0)].
Definition OFN_REGS : list sv :=
  sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms (Z_to_bv 5 10) (SLit (ONANN_S + 136)))
    (Z_to_bv 5 11) (SLit (OFN_SH + 5))) (Z_to_bv 5 24) (SLit SHADOW_OFF)) (Z_to_bv 5 25) (SLit (ONANN_S + 104)))
    (Z_to_bv 5 26) (SLit (OFN_SH + 2)).
Definition ss_ofn : sstate :=
  mkSS ONANN_FN OFN_REGS [OFN_R_sh; OFN_R_fn; OFN_R_gs; OFN_R_shg; OFN_R_slot] None OFN_FACTS.
Definition OFN_Bx : sv := SLit 0.
Definition OFN_B0 : Z * Z := (0, 0).

(* run 3, from +0x640: g_s's state at the notice's world (atom 32), its shadow byte, the slot sp1 + 48. *)
Definition OFN_R_st : YP09.region :=
  YP09.mkRegion None (ONANN_S + 112) (ONANN_S + 116) 0 0 [YP09.mkChunk (ONANN_S + 112) (YP09.CVal 4 (SOff 32 0))].
Definition OFN_R_sh2 : YP09.region :=
  YP09.mkRegion None (OFN_SH + 2) (OFN_SH + 3) 0 0 [YP09.mkChunk (OFN_SH + 2) (YP09.CVal 1 (SLit 0))].
Definition OFN_R_slot2 : YP09.region :=
  YP09.mkRegion (Some 9%nat) 48 56 0 0 [YP09.mkChunk 48 (YP09.CVal 8 (SLit (ONANN_S + 112)))].
Definition OFN_FACTS3 : facts := mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (32%nat, mkAF 0 (2 ^ 32 - 1) 0)] [] [].
Definition OFN_REGS3 : list sv := sr_set sr_atoms (Z_to_bv 5 26) (SLit (OFN_SH + 2)).
Definition ss_ofn3 : sstate := mkSS OFN_RET OFN_REGS3 [OFN_R_st; OFN_R_sh2; OFN_R_slot2] None OFN_FACTS3.
(* +0x658, `bltu a1, a0`, taken up again with no region. *)
Definition ss_ofnb : sstate := mkSS OFN_BR sr_atoms [] None (mkFacts [] [] []).

(* The bytes the piece may change between the cut and the cuts it ends at: fn's nine shadow bytes, fn's 72 bytes,
   g_s.foreign, and the stack window of __asan_memset below sp1. *)
Definition OFN_Z (F sp1 : Z) (x : Z) : Prop :=
  (SHADOW_OFF + F / 8 + 56 <= x < SHADOW_OFF + F / 8 + 65) \/ (F + 448 <= x < F + 520) \/
  (ONANN_S + 136 <= x < ONANN_S + 140) \/ (sp1 - ESTACK <= x < sp1).

(* ------------------------------------------------------------------ *)
(* 2. Region and byte lemmas                                           *)
(* ------------------------------------------------------------------ *)

(* A byte of the shadow read as 0 is a stored 0. *)
Lemma ofn_vm0 : forall (H : word -> bool) (m : word -> option byte) a,
  aview tfibsegs H m a = Some 0 -> val_mem tfibsegs (mrestrict H m) a 1 0.
Proof.
  intros H m a Hv kx Hk. assert (kx = 0%nat) by lia. subst kx. cbn [Z.of_nat]. rewrite Z.add_0_r.
  unfold aview in Hv. destruct (YP09.mbyte tfibsegs (mrestrict H m) a) as [bb|] eqn:Eb; [|discriminate Hv].
  cbn in Hv. injection Hv as Hb. change (YO0f.le_byte 0 1 0) with 0.
  f_equal. apply bv_eq. rewrite Hb. reflexivity.
Qed.

(* A one-byte chunk of the literal 0 reads 0. *)
Lemma ofn_chunk0 : forall E (H : word -> bool) (m : word -> option byte) bopt lo hi wlo whi cs off,
  region_ok tfibsegs E (mrestrict H m) (YP09.mkRegion bopt lo hi wlo whi cs) ->
  In (YP09.mkChunk off (YP09.CVal 1 (SLit 0))) cs ->
  aview tfibsegs H m (base_val E bopt + off) = Some 0.
Proof.
  intros E H m bopt lo hi wlo whi cs off (_ & _ & _ & Hcs) Hin.
  pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hc. cbn [YP09.r_base] in Hc.
  destruct (Hc 0 ltac:(cbn; lia)) as (bb & Hb1 & Hb2). rewrite Z.add_0_r in Hb2. cbn [YP09.c_off] in Hb2.
  cbn [YP09.cbyte YP09.c_val YP09.c_off] in Hb1. injection Hb1 as <-.
  unfold aview. rewrite Hb2. reflexivity.
Qed.

(* A chunk of w bytes of the value e reads, byte k, the k-th little-endian byte of e. *)
Lemma ofn_chunk_val : forall E (H : word -> bool) (m : word -> option byte) bopt lo hi wlo whi cs off (w : N) e,
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
Lemma ofn_vm_w : forall (m : word -> option byte) a (w : N) v, Z.of_N w <= 8 ->
  val_mem tfibsegs m a (N.to_nat w) (bv_unsigned (Z_to_bv 64 v) mod 2 ^ (8 * Z.of_N w)) ->
  val_mem tfibsegs m a (N.to_nat w) v.
Proof.
  intros m a w v Hw H.
  assert (Hd : (2 ^ (8 * Z.of_N w) | 2 ^ 64)).
  { exists (2 ^ (64 - 8 * Z.of_N w)). rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  assert (E : (bv_unsigned (Z_to_bv 64 v) mod 2 ^ (8 * Z.of_N w)) mod 2 ^ (8 * Z.of_N w) = v mod 2 ^ (8 * Z.of_N w)).
  { rewrite Zmod_mod, Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    apply Z.mod_mod_divide; try exact Hd; try (apply Z.pow_nonzero; lia); try (apply Z.pow_pos_nonneg; lia). }
  intros kx Hk. rewrite (H kx Hk). unfold YO0f.le_byte. rewrite N_nat_Z, E. reflexivity.
Qed.

(* A region kept by a step that keeps its bytes' views and their presence. *)
Lemma ofn_rk : forall E (H : word -> bool) (m m2 : word -> option byte) bopt lo hi wlo whi cs,
  (forall a, base_val E bopt + lo <= a < base_val E bopt + hi -> aview tfibsegs H m2 a = aview tfibsegs H m a) ->
  (forall a, apresent H m a -> apresent H m2 a) ->
  region_kept tfibsegs E (mrestrict H m) (mrestrict H m2) (YP09.mkRegion bopt lo hi wlo whi cs).
Proof.
  intros E H m m2 bopt lo hi wlo whi cs Hav Hp.
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi]; intros a Ha.
  - apply (mbyte_of_aview tfibsegs). apply Hav. lia.
  - apply writable_kept. apply Hp.
Qed.

(* A byte is determined by its unsigned value. *)
Lemma ofn_bz_inj : forall x y : byte, DSpec.bz x = DSpec.bz y -> x = y.
Proof.
  intros x y Hx. unfold DSpec.bz in Hx.
  rewrite <- (Z_to_bv_bv_unsigned 8 x), <- (Z_to_bv_bv_unsigned 8 y), Hx. reflexivity.
Qed.

Lemma ofn_map_bz_inj : forall (l1 l2 : list byte), map DSpec.bz l1 = map DSpec.bz l2 -> l1 = l2.
Proof.
  induction l1 as [|x l1 IH]; intros [|y l2] Hm; cbn [map] in Hm; try discriminate; [reflexivity|].
  injection Hm as Hx Hl. rewrite (IH l2 Hl), (ofn_bz_inj x y Hx). reflexivity.
Qed.

(* Two byte lists of the same length read from the same memory at the same address are equal. *)
Lemma ofn_garr8_det : forall (H : word -> bool) (m : word -> option byte) p (l1 l2 : list byte),
  length l1 = length l2 ->
  garr8 tfibsegs (mrestrict H m) p (map DSpec.bz l1) -> garr8 tfibsegs (mrestrict H m) p (map DSpec.bz l2) ->
  l1 = l2.
Proof.
  intros H m p l1 l2 HL H1 H2. apply ofn_map_bz_inj.
  apply (nth_ext _ _ 0 0); [rewrite !length_map; exact HL|].
  intros n Hn.
  assert (Hn3 : (n < length (map DSpec.bz l2))%nat) by (rewrite !length_map in *; lia).
  destruct (H1 n Hn) as (V1 & R1). destruct (H2 n Hn3) as (V2 & R2).
  pose proof (V1 0%nat ltac:(cbn; lia)) as W1. pose proof (V2 0%nat ltac:(cbn; lia)) as W2.
  cbn [Z.of_nat] in W1, W2. rewrite Z.add_0_r in W1, W2.
  rewrite (tw_le_byte1 _ R1) in W1. rewrite (tw_le_byte1 _ R2) in W2.
  rewrite W1 in W2.
  assert (SI : forall x y : bv 8, Some x = Some y -> bv_unsigned x = bv_unsigned y)
    by (intros x y Hxy; injection Hxy as Hxy'; rewrite Hxy'; reflexivity).
  apply SI in W2. rewrite !Z_to_bv_unsigned in W2. unfold bv_wrap, bv_modulus in W2.
  change (2 ^ Z.of_N 8) with 256 in W2.
  rewrite (Z.mod_small _ 256) in W2 by exact R1. rewrite (Z.mod_small _ 256) in W2 by exact R2. exact W2.
Qed.

(* The windows a run wrote, each inside the bytes Zs: the windows of the state's regions, computed, each case
   closed by tac. *)
Ltac ofn_win Hin Hx tac :=
  lazymatch type of Hin with In ?x ?l => let l' := eval vm_compute in l in change (In x l') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; tac |]);
  destruct Hin.

(* g_s's payload bytes are bytes of G. *)
Lemma ofn_inG : forall a, ONANN_S <= a < ONANN_S + TW.SZ_g_s -> inG TG.G_HARNESS a.
Proof.
intros a Ha. unfold inG. apply Exists_exists. exists (TA_g_s, TW.SZ_g_s).
split; [exact (TMAP_A_in_G _ _ _ TMAP_A_g_s) | unfold in_zr, ONANN_S, TA_g_s, TW.SZ_g_s in *; cbn [fst snd]; lia].
Qed.

(* ------------------------------------------------------------------ *)
(* 3. The model's facts                                                *)
(* ------------------------------------------------------------------ *)

Lemma ofn_bf_eq : forall Bx, TW.set_S_foreign Bx 1 = TW.upd Bx (TW.OFF_g_s + 136) (TW.put 4 1).
Proof. intros Bx. reflexivity. Qed.

Lemma ofn_len_bf : forall Bx, length Bx = Z.to_nat TW.W_LEN ->
  length (TW.set_S_foreign Bx 1) = Z.to_nat TW.W_LEN.
Proof. intros Bx L. unfold TW.set_S_foreign. wlen. Qed.

(* The store of :216 keeps g_s.state, g_s.notify and g_fail_next. *)
Lemma ofn_bf_state : forall Bx, length Bx = Z.to_nat TW.W_LEN ->
  TW.S_state (TW.set_S_foreign Bx 1) = TW.S_state Bx.
Proof.
intros Bx HL. assert (LZ : Z.of_nat (length Bx) = TW.W_LEN) by (rewrite HL; unfold TW.W_LEN; lia).
unfold TW.set_S_foreign, TW.S_state.
rewrite TWL.s32_at_upd_out;
  [reflexivity | unfold TW.A_S_foreign, TW.OFF_g_s; lia | unfold TW.A_S_state, TW.OFF_g_s; lia
  | rewrite TWL.length_put; unfold TW.A_S_foreign, TW.A_S_state, TW.OFF_g_s; lia
  | rewrite TWL.length_put, LZ; unfold TW.A_S_foreign, TW.OFF_g_s, TW.W_LEN; lia].
Qed.

Lemma ofn_bf_notify : forall Bx, length Bx = Z.to_nat TW.W_LEN ->
  TW.S_notify (TW.set_S_foreign Bx 1) = TW.u_at Bx (TW.OFF_g_s + 96) 8.
Proof.
intros Bx HL. assert (LZ : Z.of_nat (length Bx) = TW.W_LEN) by (rewrite HL; unfold TW.W_LEN; lia).
unfold TW.set_S_foreign, TW.S_notify, TW.A_S_notify.
rewrite TWL.u_at_upd_out;
  [reflexivity | unfold TW.A_S_foreign, TW.OFF_g_s; lia | unfold TW.OFF_g_s; lia
  | rewrite TWL.length_put; unfold TW.A_S_foreign, TW.OFF_g_s; lia
  | rewrite TWL.length_put, LZ; unfold TW.A_S_foreign, TW.OFF_g_s, TW.W_LEN; lia].
Qed.

Lemma ofn_bf_gfn : forall Bx, length Bx = Z.to_nat TW.W_LEN ->
  TW.g_fail_next (TW.set_S_foreign Bx 1) = TW.g_fail_next Bx.
Proof.
intros Bx HL. assert (LZ : Z.of_nat (length Bx) = TW.W_LEN) by (rewrite HL; unfold TW.W_LEN; lia).
unfold TW.set_S_foreign, TW.g_fail_next.
rewrite TWL.u_at_upd_out;
  [reflexivity | unfold TW.A_S_foreign, TW.OFF_g_s; lia | unfold TW.OFF_g_fail_next; lia
  | rewrite TWL.length_put; unfold TW.A_S_foreign, TW.OFF_g_s, TW.OFF_g_fail_next; lia
  | rewrite TWL.length_put, LZ; unfold TW.A_S_foreign, TW.OFF_g_s, TW.W_LEN; lia].
Qed.

(* The foreign notice's store of GOT.foreign keeps g_s.state and g_fail_next. *)
Lemma ofn_b3_state : forall Bx d, length Bx = Z.to_nat TW.W_LEN ->
  TW.S_state (TW.set_GOT_foreign Bx d) = TW.S_state Bx.
Proof.
intros Bx d HL. assert (LZ : Z.of_nat (length Bx) = TW.W_LEN) by (rewrite HL; unfold TW.W_LEN; lia).
unfold TW.set_GOT_foreign, TW.S_state.
rewrite TWL.s32_at_upd_out;
  [reflexivity | unfold TW.A_GOT_foreign, TW.OFF_GOT; lia | unfold TW.A_S_state, TW.OFF_g_s; lia
  | rewrite TWL.length_put; unfold TW.A_GOT_foreign, TW.A_S_state, TW.OFF_GOT, TW.OFF_g_s; lia
  | rewrite TWL.length_put, LZ; unfold TW.A_GOT_foreign, TW.OFF_GOT, TW.W_LEN; lia].
Qed.

Lemma ofn_b3_gfn : forall Bx d, length Bx = Z.to_nat TW.W_LEN ->
  TW.g_fail_next (TW.set_GOT_foreign Bx d) = TW.g_fail_next Bx.
Proof.
intros Bx d HL. assert (LZ : Z.of_nat (length Bx) = TW.W_LEN) by (rewrite HL; unfold TW.W_LEN; lia).
unfold TW.set_GOT_foreign, TW.g_fail_next.
rewrite TWL.u_at_upd_out;
  [reflexivity | unfold TW.A_GOT_foreign, TW.OFF_GOT; lia | unfold TW.OFF_g_fail_next; lia
  | rewrite TWL.length_put; unfold TW.A_GOT_foreign, TW.OFF_GOT, TW.OFF_g_fail_next; lia
  | rewrite TWL.length_put, LZ; unfold TW.A_GOT_foreign, TW.OFF_GOT, TW.W_LEN; lia].
Qed.

(* On this path call_notify's test holds and notice gives B3. *)
Lemma ofn_model : forall (TF : option TI.tframe) (Bf b B3 : list byte),
  TSS.call_notify timg_A TF Bf (onann_fntc Bf b) = Some (B3, tt) ->
  TW.S_notify Bf = TI.ti_notice timg_A /\ TC.notice_m timg_A TF Bf (onann_fntc Bf b) = Some (B3, tt).
Proof.
  intros TF Bf b B3 H. unfold TSS.call_notify in H.
  destruct (Z.eqb_spec (TW.S_notify Bf) (TI.ti_notice timg_A)) as [E|E]; [|discriminate H].
  split; [exact E | exact H].
Qed.

Lemma ofn_state_range : forall Bx, - 2 ^ 31 <= TW.S_state Bx < 2 ^ 31.
Proof. intros Bx. unfold TW.S_state. apply TWL.s32_range. Qed.

(* The sign-extended 4-byte load of g_s's state is the model's S_state. *)
Lemma ofn_sext : forall E n Bx, ew E n = Z_to_bv 64 (TW.u_at Bx (TW.OFF_g_s + 112) 4) ->
  sv_denot E (SExt true 32 (SOff n 0)) = Z_to_bv 64 (TW.S_state Bx).
Proof.
intros E n Bx H. pose proof (TWL.u_at_range Bx (TW.OFF_g_s + 112) 4) as R. cbn [sv_denot]. rewrite H.
rewrite unsigned_lit_small by lia. rewrite Z.add_0_r.
rewrite LMem.sext_small, LMem.signed_of_extract by lia.
rewrite unsigned_lit_small by lia. reflexivity.
Qed.

(* `addiw a0, s5, -1; li a1, 1; bltu a1, a0`: the branch is taken exactly when the state is neither S_WAKING (1)
   nor S_ONLINE (2). *)
Lemma ofn_ltu1 : forall st, - 2 ^ 31 <= st < 2 ^ 31 ->
  bv_ltu (Z_to_bv 64 1) (sext 64 (alu32 ALU_ADD (low32 (Z_to_bv 64 st)) (low32 (Z_to_bv 64 (-1))))) =
  negb ((st =? 1) || (st =? 2)).
Proof.
intros st Hst. rewrite zalu32_sound.
unfold bv_ltu. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite (Z.mod_small 1 (2 ^ 64)) by lia.
assert (RZ : 0 <= zalu32 ALU_ADD st (-1) < 2 ^ 64)
  by (unfold zalu32, zcanon, M64; apply Z.mod_pos_bound; lia).
rewrite (Z.mod_small _ (2 ^ 64)) by exact RZ.
unfold zalu32, zcanon, zu32, M64, M32. cbn [zalu_raw].
unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
change (2 ^ Z.of_N 32) with (2 ^ 32).
destruct (Z.eqb_spec st 1) as [-> | H1]; [vm_compute; reflexivity |].
destruct (Z.eqb_spec st 2) as [-> | H2]; [vm_compute; reflexivity |].
cbn [orb negb]. apply Z.ltb_lt.
Z.div_mod_to_equations. lia.
Qed.

(* fn's 72 bytes: the stores of 6 (4), the state (4), 8 zeros, fp (8), a (8), and the memset's 40 zeros. *)
Definition ofn_bytes (st fpv F : Z) : list byte :=
  TW.put 4 6 ++ TW.put 4 st ++ TW.put 8 0 ++ TW.put 8 fpv ++ TW.put 8 (F + 256) ++ repeat (DSpec.b8 0) 40.

Lemma ofn_bytes_len : forall st fpv F, length (ofn_bytes st fpv F) = 72%nat.
Proof. intros. unfold ofn_bytes. rewrite !length_app, !TWL.length_put, repeat_length. reflexivity. Qed.

Lemma ofn_nb : forall (H : word -> bool) (m : word -> option byte) F st fpv,
  val_mem tfibsegs (mrestrict H m) (F + 448) 4 6 ->
  val_mem tfibsegs (mrestrict H m) (F + 452) 4 st ->
  val_mem tfibsegs (mrestrict H m) (F + 456) 8 0 ->
  val_mem tfibsegs (mrestrict H m) (F + 464) 8 fpv ->
  val_mem tfibsegs (mrestrict H m) (F + 472) 8 (F + 256) ->
  (forall a, F + 480 <= a < F + 520 -> aview tfibsegs H m a = Some 0) ->
  garr8 tfibsegs (mrestrict H m) (F + 448) (map DSpec.bz (ofn_bytes st fpv F)).
Proof.
  intros H m F st fpv V0 V4 V8 V16 V24 Z0.
  unfold ofn_bytes. rewrite !map_app. apply garr8_app.
  split; [exact (TransportGNotice.garr8_of_put tfibsegs _ _ 4 6 V0) |].
  rewrite length_map, TWL.length_put. replace (F + 448 + Z.of_nat 4) with (F + 452) by lia.
  apply garr8_app. split; [exact (TransportGNotice.garr8_of_put tfibsegs _ _ 4 st V4) |].
  rewrite length_map, TWL.length_put. replace (F + 452 + Z.of_nat 4) with (F + 456) by lia.
  apply garr8_app. split; [exact (TransportGNotice.garr8_of_put tfibsegs _ _ 8 0 V8) |].
  rewrite length_map, TWL.length_put. replace (F + 456 + Z.of_nat 8) with (F + 464) by lia.
  apply garr8_app. split; [exact (TransportGNotice.garr8_of_put tfibsegs _ _ 8 fpv V16) |].
  rewrite length_map, TWL.length_put. replace (F + 464 + Z.of_nat 8) with (F + 472) by lia.
  apply garr8_app. split; [exact (TransportGNotice.garr8_of_put tfibsegs _ _ 8 (F + 256) V24) |].
  rewrite length_map, TWL.length_put. replace (F + 472 + Z.of_nat 8) with (F + 480) by lia.
  rewrite map_repeat. change (DSpec.bz (DSpec.b8 0)) with 0.
  apply garr8_zeros. intros a Ha.
  pose proof (Z0 a ltac:(rewrite ?repeat_length in Ha; cbn [Z.of_nat Pos.of_succ_nat] in Ha; lia)) as Za.
  unfold aview in Za.
  destruct (YP09.mbyte tfibsegs (mrestrict H m) a) as [bb|] eqn:Eb; [|discriminate Za].
  cbn in Za. injection Za as Hb. f_equal. apply bv_eq. rewrite Hb. reflexivity.
Qed.
(* An announce field is the string up to its NUL, at most 9 bytes, and the NUL. *)
Lemma ofn_ann_len : forall src : list byte, (length (TSS.ann_field src) <= 10)%nat.
Proof.
  intros src. unfold TSS.ann_field. rewrite length_app, length_firstn. cbn [length].
  rewrite DSpec.copy_len_strz. pose proof (DSpec.strz_len_le src) as H. lia.
Qed.

(* `srli a1, a0, 3; add a1, a1, s8` with s8 pinned to the shadow base: the shadow address of the frame. *)
Lemma ofn_denot_shadow : forall E n F,
  ew E n = Z_to_bv 64 F -> 0 <= F < 2 ^ 47 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff n 0) (SLit 3)) (SLit SHADOW_OFF))
  = Z_to_bv 64 (SHADOW_OFF + F / 8).
Proof.
intros E n F Hn HF.
assert (HD : 0 <= F / 8) by (apply Z.div_pos; lia).
assert (HD2 : F / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia).
assert (Un : U E (SOff n 0) = F)
  by (rewrite U_SOff, Hn, (unsigned_lit_small F ltac:(lia)), Z.add_0_r; apply zcanon_id; unfold M64; lia).
rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
rewrite Un, !U_SLit, (zcanon_id 3) by (unfold M64; lia).
change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
rewrite (zcanon_id (F / 8)) by (unfold M64; lia).
rewrite (zcanon_id SHADOW_OFF) by (unfold M64, SHADOW_OFF; lia).
rewrite (Z.add_comm (F / 8) SHADOW_OFF). apply zcanon_id. unfold M64, SHADOW_OFF. lia.
Qed.


Section fn. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

(* The valuation of runs 1 and 2: the registers at the cut, then g_s's notify, notify_ctx and state in B2. *)
Definition ofn_vals (Bx : list byte) : list word :=
  [Z_to_bv 64 (TW.u_at Bx (TW.OFF_g_s + 96) 8); Z_to_bv 64 (TW.u_at Bx (TW.OFF_g_s + 104) 8);
   Z_to_bv 64 (TW.u_at Bx (TW.OFF_g_s + 112) 4)].
Definition ofn_E (regs : bvmap 5 word) (Bx : list byte) : env := Eimg (PI := PI_transport) (Ereg regs (ofn_vals Bx)).

Lemma ofn_entry0 : forall ly S (W : world segs) regs mem md Bx sp1 F,
  trans_onann_cells B -> @AR rc segs B ly S W mem md ->
  tw_at TMAP_A (aview segs (w_H W) mem) Bx ->
  YK11.getr regs 9 = w64 sp1 -> YK11.getr regs 18 = w64 F -> YK11.getr regs 19 = w64 (SHADOW_OFF + F / 8) ->
  2 ^ 46 <= sp1 <= 2 ^ 47 -> sp1 mod 32 = 0 -> 4096 <= F -> F mod 64 = 0 -> F + 1024 <= sp1 ->
  in_app F 1024 -> (F + 1024 <= ONANN_S \/ ONANN_S + TW.SZ_g_s <= F) ->
  (forall a, F + 448 <= a < F + 480 -> apresent (w_H W) mem a) ->
  (forall i, 56 <= i < 65 -> apresent (w_H W) mem (SHADOW_OFF + F / 8 + i)) ->
  rdword (aview segs (w_H W) mem) (sp1 + 8) = Some OFN_SH ->
  rdword (aview segs (w_H W) mem) (sp1 + 16) = Some (OFN_SH + 1) ->
  rdword (aview segs (w_H W) mem) (sp1 + 24) = Some (ONANN_S + 96) ->
  rdword (aview segs (w_H W) mem) (sp1 + 40) = Some F ->
  rdword (aview segs (w_H W) mem) (sp1 + 48) = Some (ONANN_S + 112) ->
  rdword (aview segs (w_H W) mem) (sp1 + 56) = Some (F + 256) ->
  st_ok_pi segs VAL (ofn_E regs Bx)
    (mkSS ONANN_FN sr_atoms [OFN_R_sh; OFN_R_fn; OFN_R_gs; OFN_R_shg; OFN_R_slot] None OFN_FACTS)
    (@YK11.mkst fx regs (Z_to_bv 64 (BASE + ONANN_FN)) (mrestrict (w_H W) mem) (YK11.seg_rom segs)).
Proof.
  intros ly S W regs mem md Bx sp1 F HZC HAR Htw R9 R18 R19 Hsp Hsp32 HF0 HF64 HFc HFapp HFG Hpf Hpsh
    S8 S16 S24 S40 S48 S56.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (Z.div_mod F 64 ltac:(lia)) as DF. rewrite HF64, Z.add_0_r in DF.
  assert (HF8 : F / 8 = 8 * (F / 64))
    by (rewrite DF at 1; replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by ring; apply Z.div_mul; lia).
  assert (HF8b : 512 <= F / 8 <= 2 ^ 44)
    by (split; [apply Z.div_le_lower_bound; lia | apply Z.div_le_upper_bound; lia]).
  assert (HSHF : SHADOW_OFF + F / 8 + 128 <= F \/ F + 1024 <= SHADOW_OFF + F / 8).
  { unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp. destruct HFapp as (_ & [HL | (HH1 & HH2)]);
    [right | left]; unfold SHADOW_OFF; lia. }
  assert (HAPP : F + 1024 <= kLowShadowBeg \/ kHighMemBeg <= F).
  { unfold in_app in HFapp. destruct HFapp as (_ & [HL | (HH1 & HH2)]); [left | right]; lia. }
  unfold kLowShadowBeg, kHighMemBeg in HAPP.
  assert (HF8G : F / 8 + 128 <= 769860 \/ 769883 <= F / 8).
  { destruct HFG as [HL | HR].
    - left. assert (HM : F / 8 <= 6157760 / 8) by (apply Z.div_le_mono; [lia | unfold ONANN_S, TA_g_s in HL; lia]).
      change (6157760 / 8) with 769720 in HM. lia.
    - right. assert (HM : 6177048 / 8 <= F / 8)
        by (apply Z.div_le_mono; [lia | unfold ONANN_S, TA_g_s, TW.SZ_g_s in HR; lia]).
      change (6177048 / 8) with 772131 in HM. lia. }
  set (E := ofn_E regs Bx).
  assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs r)
    by (intros n r Hn; unfold E, ofn_E; apply ew_Eimg_Ereg_nat; exact Hn).
  assert (U9 : bv_unsigned (ew E 9) = sp1)
    by (rewrite (EE 9%nat 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
  assert (U18 : bv_unsigned (ew E 18) = F)
    by (rewrite (EE 18%nat 18%bv eq_refl), R18; unfold w64; apply unsigned_lit_small; lia).
  assert (U19 : bv_unsigned (ew E 19) = SHADOW_OFF + F / 8)
    by (rewrite (EE 19%nat 19%bv eq_refl), R19; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (EX : forall j, (j < 3)%nat -> ew E (32 + j) = nth j (ofn_vals Bx) (Z_to_bv 64 0))
    by (intros j Hj; unfold E, ofn_E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
  pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
  pose proof (EX 2%nat ltac:(lia)) as E34.
  cbn [Nat.add nth ofn_vals] in E32, E33, E34.
  pose proof (TWL.u_at_range Bx (TW.OFF_g_s + 96) 8) as R32.
  pose proof (TWL.u_at_range Bx (TW.OFF_g_s + 104) 8) as R33.
  pose proof (TWL.u_at_range Bx (TW.OFF_g_s + 112) 4) as R34.
  change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in R32, R33.
  change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in R34.
  assert (U34 : bv_unsigned (ew E 34) = TW.u_at Bx (TW.OFF_g_s + 112) 4)
    by (rewrite E34; apply unsigned_lit_small; lia).
  assert (DEN : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n 0) = Z_to_bv 64 v)
    by (intros n v Hn Hv; cbn [sv_denot]; rewrite Hn, unsigned_lit_small, Z.add_0_r by exact Hv; reflexivity).
  assert (ZSH : forall j, j = 0 \/ j = 1 \/ j = 2 \/ j = 5 -> val_mem segs (mrestrict (w_H W) mem) (OFN_SH + j) 1 0).
  { intros j Hj. apply ofn_vm0.
    replace (OFN_SH + j) with (FCells.shadow_addr (ONANN_S + 96 + 8 * j)).
    - apply (decode_zshadow_rd B ly S W mem md ONANN_S (ONANN_S + TW.SZ_g_s) _ HAR); [| | | exact HZC].
      + unfold ONANN_S, TA_g_s. destruct Hj as [-> | [-> | [-> | ->]]]; reflexivity.
      + destruct Hj as [-> | [-> | [-> | ->]]]; lia.
      + unfold TW.SZ_g_s. destruct Hj as [-> | [-> | [-> | ->]]]; unfold ONANN_S, TA_g_s; lia.
    - unfold FCells.shadow_addr, FCells.ASAN_K, OFN_SH, ONANN_S, TA_g_s.
      destruct Hj as [-> | [-> | [-> | ->]]]; reflexivity. }
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks OFN_R_sh OFN_R_fn OFN_R_gs OFN_R_shg
        OFN_R_slot base_val]; rewrite ?U9, ?U18, ?U19.
    + split; [unfold SHADOW_OFF; lia|]. split; [unfold SHADOW_OFF; lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Hpsh. lia.
    + split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Hpf. lia.
    + split; [unfold ONANN_S, TA_g_s; lia|]. split; [unfold ONANN_S, TA_g_s; lia|]. split.
      * intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS (0 + o) G_HARNESS_rw).
        apply ofn_inG. unfold TW.SZ_g_s, ONANN_S, TA_g_s in *. lia.
      * repeat apply Forall_cons; try apply Forall_nil.
        -- apply (chunk_ok_val segs E _ 0 (ONANN_S + 96) 8 (SOff 32 0) (TW.u_at Bx (TW.OFF_g_s + 96) 8));
             [apply DEN; [exact E32 | exact R32] | exact R32 | unfold ONANN_S, TA_g_s; lia |].
           replace (0 + (ONANN_S + 96)) with (TA_g_s + 96) by (unfold ONANN_S; lia).
           exact (tw_read_val segs _ TMAP_A Bx TW.OFF_g_s TA_g_s TW.SZ_g_s 96 8 TMAP_A_ok Htw TMAP_A_g_s
             ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
        -- apply (chunk_ok_val segs E _ 0 (ONANN_S + 104) 8 (SOff 33 0) (TW.u_at Bx (TW.OFF_g_s + 104) 8));
             [apply DEN; [exact E33 | exact R33] | exact R33 | unfold ONANN_S, TA_g_s; lia |].
           replace (0 + (ONANN_S + 104)) with (TA_g_s + 104) by (unfold ONANN_S; lia).
           exact (tw_read_val segs _ TMAP_A Bx TW.OFF_g_s TA_g_s TW.SZ_g_s 104 8 TMAP_A_ok Htw TMAP_A_g_s
             ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
        -- apply (chunk_ok_val segs E _ 0 (ONANN_S + 112) 4 (SOff 34 0) (TW.u_at Bx (TW.OFF_g_s + 112) 4));
             [cbn [sv_denot]; rewrite U34, Z.add_0_r; reflexivity | exact R34 | unfold ONANN_S, TA_g_s; lia |].
           replace (0 + (ONANN_S + 112)) with (TA_g_s + 112) by (unfold ONANN_S; lia).
           exact (tw_read_val segs _ TMAP_A Bx TW.OFF_g_s TA_g_s TW.SZ_g_s 112 4 TMAP_A_ok Htw TMAP_A_g_s
             ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
    + split; [unfold OFN_SH; lia|]. split; [unfold OFN_SH; lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val segs E _ 0 OFN_SH 1 (SLit 0) 0); [reflexivity | lia | unfold OFN_SH; lia |].
        rewrite Z.add_0_l. pose proof (ZSH 0 ltac:(lia)) as Z0. rewrite Z.add_0_r in Z0. exact Z0.
      * apply (chunk_ok_val segs E _ 0 (OFN_SH + 1) 1 (SLit 0) 0); [reflexivity | lia | unfold OFN_SH; lia |].
        rewrite Z.add_0_l. exact (ZSH 1 ltac:(lia)).
      * apply (chunk_ok_val segs E _ 0 (OFN_SH + 2) 1 (SLit 0) 0); [reflexivity | lia | unfold OFN_SH; lia |].
        rewrite Z.add_0_l. exact (ZSH 2 ltac:(lia)).
      * apply (chunk_ok_val segs E _ 0 (OFN_SH + 5) 1 (SLit 0) 0); [reflexivity | lia | unfold OFN_SH; lia |].
        rewrite Z.add_0_l. exact (ZSH 5 ltac:(lia)).
    + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val segs E _ sp1 8 8 (SLit OFN_SH) OFN_SH);
          [reflexivity | unfold OFN_SH; lia | lia |].
        exact (val_mem_of_rdword segs (w_H W) mem _ _ S8).
      * apply (chunk_ok_val segs E _ sp1 16 8 (SLit (OFN_SH + 1)) (OFN_SH + 1));
          [reflexivity | unfold OFN_SH; lia | lia |].
        exact (val_mem_of_rdword segs (w_H W) mem _ _ S16).
      * apply (chunk_ok_val segs E _ sp1 24 8 (SLit (ONANN_S + 96)) (ONANN_S + 96));
          [reflexivity | unfold ONANN_S, TA_g_s; lia | lia |].
        exact (val_mem_of_rdword segs (w_H W) mem _ _ S24).
      * apply (chunk_ok_val segs E _ sp1 40 8 (SOff 18 0) F);
          [apply DEN; [rewrite (EE 18%nat 18%bv eq_refl), R18; reflexivity | lia]
          | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | lia |].
        exact (val_mem_of_rdword segs (w_H W) mem _ _ S40).
      * apply (chunk_ok_val segs E _ sp1 48 8 (SLit (ONANN_S + 112)) (ONANN_S + 112));
          [reflexivity | unfold ONANN_S, TA_g_s; lia | lia |].
        exact (val_mem_of_rdword segs (w_H W) mem _ _ S48).
      * apply (chunk_ok_val segs E _ sp1 56 8 (SOff 18 256) (F + 256));
          [cbn [sv_denot]; rewrite (EE 18%nat 18%bv eq_refl), R18; unfold w64;
           rewrite unsigned_lit_small by lia; reflexivity
          | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | lia |].
        exact (val_mem_of_rdword segs (w_H W) mem _ _ S56).
  - apply pairwise_disjoint_of_extents.
    unfold extent_of_region, OFN_R_sh, OFN_R_fn, OFN_R_gs, OFN_R_shg, OFN_R_slot.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U18, U19.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold OFN_SH, ONANN_S, TA_g_s, TW.SZ_g_s, SHADOW_OFF in *.
    destruct HSHF as [SH1 | SH1]; destruct HF8G as [G81 | G81]; destruct HAPP as [AP1 | AP1];
      repeat split; first [exact I | lia].
  - unfold OFN_FACTS, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U9, U18, U19, U34.
    change (2 ^ 5) with 32. change (2 ^ 6) with 64. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    assert (M8 : (SHADOW_OFF + F / 8) mod 8 = 0).
    { rewrite HF8. unfold SHADOW_OFF. replace (2147450880 + 8 * (F / 64)) with ((268431360 + F / 64) * 8) by ring.
      apply Z.mod_mul. lia. }
    repeat match goal with |- _ /\ _ => split end; try exact I; try (unfold SHADOW_OFF in *; lia).
    (* the alias: the shadow address of the frame is s3 *)
    rewrite (ofn_denot_shadow E 18 F ltac:(rewrite (EE 18%nat 18%bv eq_refl), R18; unfold w64; reflexivity)
      ltac:(lia)).
    cbn [sv_denot]. rewrite U19, Z.add_0_r. reflexivity.
Qed.

Lemma ofn_entry : forall ly S (W : world segs) regs mem md Bx sp1 F,
  trans_onann_cells B -> @AR rc segs B ly S W mem md ->
  tw_at TMAP_A (aview segs (w_H W) mem) Bx ->
  YK11.getr regs 9 = w64 sp1 -> YK11.getr regs 18 = w64 F -> YK11.getr regs 19 = w64 (SHADOW_OFF + F / 8) ->
  YK11.getr regs 10 = w64 (ONANN_S + 136) -> YK11.getr regs 11 = w64 (OFN_SH + 5) ->
  YK11.getr regs 24 = w64 SHADOW_OFF -> YK11.getr regs 25 = w64 (ONANN_S + 104) ->
  YK11.getr regs 26 = w64 (OFN_SH + 2) ->
  2 ^ 46 <= sp1 <= 2 ^ 47 -> sp1 mod 32 = 0 -> 4096 <= F -> F mod 64 = 0 -> F + 1024 <= sp1 ->
  in_app F 1024 -> (F + 1024 <= ONANN_S \/ ONANN_S + TW.SZ_g_s <= F) ->
  (forall a, F + 448 <= a < F + 480 -> apresent (w_H W) mem a) ->
  (forall i, 56 <= i < 65 -> apresent (w_H W) mem (SHADOW_OFF + F / 8 + i)) ->
  rdword (aview segs (w_H W) mem) (sp1 + 8) = Some OFN_SH ->
  rdword (aview segs (w_H W) mem) (sp1 + 16) = Some (OFN_SH + 1) ->
  rdword (aview segs (w_H W) mem) (sp1 + 24) = Some (ONANN_S + 96) ->
  rdword (aview segs (w_H W) mem) (sp1 + 40) = Some F ->
  rdword (aview segs (w_H W) mem) (sp1 + 48) = Some (ONANN_S + 112) ->
  rdword (aview segs (w_H W) mem) (sp1 + 56) = Some (F + 256) ->
  st_ok_pi segs VAL (ofn_E regs Bx) ss_ofn
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + ONANN_FN)) mem (YK11.seg_rom segs))).
Proof.
  intros ly S W regs mem md Bx sp1 F HZC HAR Htw R9 R18 R19 R10 R11 R24 R25 R26 Hsp Hsp32 HF0 HF64 HFc HFapp HFG
    Hpf Hpsh S8 S16 S24 S40 S48 S56.
  rewrite restrict_mkst_fx.
  pose proof (ofn_entry0 ly S W regs mem md Bx sp1 F HZC HAR Htw R9 R18 R19 Hsp Hsp32 HF0 HF64 HFc HFapp HFG
    Hpf Hpsh S8 S16 S24 S40 S48 S56) as H0.
  pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 10) (ONANN_S + 136) H0 R10 eq_refl) as H1.
  pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 11) (OFN_SH + 5) H1 R11 eq_refl) as H2.
  pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 24) SHADOW_OFF H2 R24 eq_refl) as H3.
  pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 25) (ONANN_S + 104) H3 R25 eq_refl) as H4.
  pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 26) (OFN_SH + 2) H4 R26 eq_refl) as H5.
  exact H5.
Qed.

(* The state at +0x640, after notice returns. *)
Lemma ofn_entry3 : forall ly S (W : world segs) regs mem md Bx sp1,
  trans_onann_cells B -> @AR rc segs B ly S W mem md ->
  tw_at TMAP_A (aview segs (w_H W) mem) Bx ->
  YK11.getr regs 9 = w64 sp1 -> YK11.getr regs 26 = w64 (OFN_SH + 2) ->
  2 ^ 46 <= sp1 <= 2 ^ 47 -> sp1 mod 32 = 0 ->
  rdword (aview segs (w_H W) mem) (sp1 + 48) = Some (ONANN_S + 112) ->
  st_ok_pi segs VAL (Eimg (PI := PI_transport) (Ereg regs [Z_to_bv 64 (TW.u_at Bx (TW.OFF_g_s + 112) 4)])) ss_ofn3
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + OFN_RET)) mem (YK11.seg_rom segs))).
Proof.
  intros ly S W regs mem md Bx sp1 HZC HAR Htw R9 R26 Hsp Hsp32 S48.
  rewrite restrict_mkst_fx.
  set (E := Eimg (PI := PI_transport) (Ereg regs [Z_to_bv 64 (TW.u_at Bx (TW.OFF_g_s + 112) 4)])).
  assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs r)
    by (intros n r Hn; unfold E; apply ew_Eimg_Ereg_nat; exact Hn).
  assert (U9 : bv_unsigned (ew E 9) = sp1)
    by (rewrite (EE 9%nat 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
  assert (E32 : ew E 32 = Z_to_bv 64 (TW.u_at Bx (TW.OFF_g_s + 112) 4))
    by (unfold E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  pose proof (TWL.u_at_range Bx (TW.OFF_g_s + 112) 4) as R32.
  change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in R32.
  assert (U32 : bv_unsigned (ew E 32) = TW.u_at Bx (TW.OFF_g_s + 112) 4)
    by (rewrite E32; apply unsigned_lit_small; lia).
  assert (ZSH : val_mem segs (mrestrict (w_H W) mem) (OFN_SH + 2) 1 0).
  { apply ofn_vm0. replace (OFN_SH + 2) with (FCells.shadow_addr (ONANN_S + 112)).
    - apply (decode_zshadow_rd B ly S W mem md ONANN_S (ONANN_S + TW.SZ_g_s) _ HAR); [| | | exact HZC].
      + unfold ONANN_S, TA_g_s. reflexivity.
      + lia.
      + unfold TW.SZ_g_s, ONANN_S, TA_g_s. lia.
    - unfold FCells.shadow_addr, FCells.ASAN_K, OFN_SH, ONANN_S, TA_g_s. reflexivity. }
  assert (H0 : st_ok_pi segs VAL E
    (mkSS OFN_RET sr_atoms [OFN_R_st; OFN_R_sh2; OFN_R_slot2] None OFN_FACTS3)
    (@YK11.mkst fx regs (Z_to_bv 64 (BASE + OFN_RET)) (mrestrict (w_H W) mem) (YK11.seg_rom segs))).
  { apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks OFN_R_st OFN_R_sh2 OFN_R_slot2
        base_val]; rewrite ?U9.
    + split; [unfold ONANN_S, TA_g_s; lia|]. split; [unfold ONANN_S, TA_g_s; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val segs E _ 0 (ONANN_S + 112) 4 (SOff 32 0) (TW.u_at Bx (TW.OFF_g_s + 112) 4));
        [cbn [sv_denot]; rewrite U32, Z.add_0_r; reflexivity | exact R32 | unfold ONANN_S, TA_g_s; lia |].
      replace (0 + (ONANN_S + 112)) with (TA_g_s + 112) by (unfold ONANN_S; lia).
      exact (tw_read_val segs _ TMAP_A Bx TW.OFF_g_s TA_g_s TW.SZ_g_s 112 4 TMAP_A_ok Htw TMAP_A_g_s
        ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
    + split; [unfold OFN_SH; lia|]. split; [unfold OFN_SH; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val segs E _ 0 (OFN_SH + 2) 1 (SLit 0) 0); [reflexivity | lia | unfold OFN_SH; lia |].
      rewrite Z.add_0_l. exact ZSH.
    + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val segs E _ sp1 48 8 (SLit (ONANN_S + 112)) (ONANN_S + 112));
        [reflexivity | unfold ONANN_S, TA_g_s; lia | lia |].
      exact (val_mem_of_rdword segs (w_H W) mem _ _ S48).
  - apply pairwise_disjoint_of_extents.
    unfold extent_of_region, OFN_R_st, OFN_R_sh2, OFN_R_slot2.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold OFN_SH, ONANN_S, TA_g_s. repeat split; first [exact I | lia].
  - unfold OFN_FACTS3, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U9, U32.
    change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; lia. }
  exact (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 26) (OFN_SH + 2) H0 R26 eq_refl).
Qed.

(* The state at +0x658 with no region. *)
Lemma ofn_entryb : forall (W : world segs) regs mem,
  st_ok_pi segs VAL (Eimg (PI := PI_transport) (Ereg regs [])) ss_ofnb
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + OFN_BR)) mem (YK11.seg_rom segs))).
Proof.
  intros W regs mem. rewrite restrict_mkst_fx. unfold ss_ofnb.
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. exact I.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. repeat split; exact I.
Qed.

(* The value of register r in the machine state of a symbolic state HS. *)
Ltac ofn_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | ?T => idtac "ofn_reg: no match for" T; fail
  end.

(* Region i of a symbolic state, before or after a run. *)
Ltac ofn_region HS i H :=
  lazymatch type of HS with
  | st_ok_pi _ _ _ _ _ => pose proof (st_ok_pi_region_nth _ _ _ i _ HS eq_refl) as H
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok _ _ _ _ =>
      pose proof (st_ok_region_nth _ _ _ i _ HS eq_refl) as H
  | ?T => idtac "ofn_region: no match for" T; fail
  end; cbn [ms_mem restrict] in H.

(* The valuation of a symbolic state, before or after a run. *)
Ltac ofn_env HS N :=
  lazymatch type of HS with
  | st_ok_pi _ _ ?EF _ _ => set (N := EF) in HS
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok _ ?EF _ _ => set (N := EF) in HS
  | ?T => idtac "ofn_env: no match for" T; fail
  end.

Ltac ofn_kreg HS E1lo EE r n Q H :=
  lazymatch type of Q with _ = ?v =>
    ofn_reg HS r v H
      ltac:(cbn [sv_denot]; rewrite (E1lo n ltac:(lia)), (EE n r eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Q) end.
Ltac ofn_kregb HS EEb r n Q H :=
  lazymatch type of Q with _ = ?v =>
    ofn_reg HS r v H
      ltac:(cbn [sv_denot]; rewrite (EEb n r eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Q) end.

(* The facts every cut carries move to a later memory whose view is the same at every address. *)
Lemma ofn_cur_move : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw b pos F ly2 S2
    (W2 : world segs) mem2 md2 mem3 md3 e,
  onann_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw b pos F ly2 S2 W2 mem2 md2 e ->
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0
    ((ONANN_CID, pos) :: own) ly2 S2 W2 mem3 md3 (k + e) ->
  (forall a, aview segs (w_H W2) mem3 a = aview segs (w_H W2) mem2 a) ->
  (forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) mem3 a) ->
  onann_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw b pos F ly2 S2 W2 mem3 md3 e.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw b pos F ly2 S2 W2 mem2 md2 mem3 md3 e
  (HJ & He & Hfr & Hperm & HlyF & HMO & HK & HSV & HFL) HJ3 KD GR.
refine (conj HJ3 (conj He (conj Hfr (conj Hperm (conj HlyF (conj HMO (conj _ (conj _ _)))))))).
- destruct HK as (K1 & K2 & K3 & K4 & K5 & K6).
  split; [|split; [|split; [|split; [|split]]]].
  + intros a Ha Hw. rewrite KD. exact (K1 a Ha Hw).
  + intros b0 m i Hb Hi Hn. rewrite KD. exact (K2 b0 m i Hb Hi Hn).
  + intros a Hi HnG Hno Hne. rewrite KD. exact (K3 a Hi HnG Hno Hne).
  + intros cid pos0 a Hin Hr Hn. rewrite KD. exact (K4 cid pos0 a Hin Hr Hn).
  + intros a Ha Hw Hp. apply GR. exact (K5 a Ha Hw Hp).
  + intros a Ha. apply GR. exact (K6 a Ha).
- refine (Forall_impl _ _ HSV). intros o Ho. rewrite (rdword_ext _ _ _ (fun k0 _ => KD _)). exact Ho.
- rewrite (rdword_ext _ _ _ (fun k0 _ => KD _)). exact HFL.
Qed.

Lemma ofn_slot_move : forall (W2 : world segs) mem2 mem3 sp1 o v,
  (forall a, aview segs (w_H W2) mem3 a = aview segs (w_H W2) mem2 a) ->
  onann_slot W2 mem2 sp1 o v -> onann_slot W2 mem3 sp1 o v.
Proof.
intros W2 mem2 mem3 sp1 o v KD H. unfold onann_slot in *.
rewrite (rdword_ext _ _ _ (fun k0 _ => KD _)). exact H.
Qed.

(* fn's 72 bytes, as notice's statement reads them (check_state_data_cg.v trans_ntc_at). *)
Lemma ofn_ntc_at : forall lyc ly2 S2 (W2 : world segs) memN mdN (regsC : bvmap 5 word) (Bf b : list byte)
    F pos fp,
  AR_laws segs B -> @AR rc segs B ly2 S2 W2 memN mdN -> In (ONANN_CID, pos) (frames S2) ->
  frame_addr ly2 ONANN_CID pos = F -> 4096 <= F -> F mod 64 = 0 -> F + 1024 <= alloc_ceiling -> in_app F 1024 ->
  F + 1024 <= spZ regsC - NOTICE_STK -> ly_stk_lo ly2 = ly_stk_lo lyc ->
  (forall i, 32 <= i < 37 -> aview segs (w_H W2) memN (SHADOW_OFF + F / 8 + i) = Some 0) ->
  (forall i, 56 <= i < 65 -> aview segs (w_H W2) memN (SHADOW_OFF + F / 8 + i) = Some 0) ->
  garr8 segs (mrestrict (w_H W2) memN) (F + 448) (map DSpec.bz (ofn_bytes (TW.S_state Bf) fp F)) ->
  garr8 segs (mrestrict (w_H W2) memN) (F + ONANN_A)
    (map DSpec.bz (TSS.ann_field (skipn 15 (DSpec.fr_body b)))) ->
  garr8 segs (mrestrict (w_H W2) memN) (F + ONANN_A + 10)
    (map DSpec.bz (TSS.ann_field (skipn 24 (DSpec.fr_body b)))) ->
  trans_ntc_at B ly2 S2 W2 memN regsC NOTICE_STK (F + 448) (onann_fntc Bf b).
Proof.
intros lyc ly2 S2 W2 memN mdN regsC Bf b F pos fp LAWS HAR Hin EF HF0 HF64 HFc HFapp Hwin ELO ZA ZF HNB HV HNm.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (al_frames _ _ LAWS ly2 S2 W2 memN mdN ONANN_CID pos HAR Hin) as (_ & _ & HFb & HFsh).
rewrite EF in HFb, HFsh. change (fs_frame_bytes ONANN_CID) with 1024 in HFb.
change (fs_frame_bytes ONANN_CID / 8) with 128 in HFsh.
change (shadow_addr F) with (SHADOW_OFF + F / 8) in HFsh.
assert (DFm8 : F mod 8 = 0).
{ pose proof (Z.div_mod F 64 ltac:(lia)) as D. rewrite HF64, Z.add_0_r in D. rewrite D.
  replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by ring. apply Z.mod_mul. lia. }
assert (Hst : - 2 ^ 31 <= TW.S_state Bf < 2 ^ 31) by apply ofn_state_range.
set (NB := ofn_bytes (TW.S_state Bf) fp F) in *.
assert (ELEN : length NB = 72%nat) by apply ofn_bytes_len.
assert (E0 : TW.u_at NB 0 4 = 6) by (unfold NB, ofn_bytes; WN.ntc_field; try (apply Z.mod_small; lia)).
assert (E4 : TW.u_at NB 4 4 = TW.S_state Bf mod 2 ^ 32)
  by (unfold NB, ofn_bytes; WN.ntc_field).
assert (E8 : TW.u_at NB 8 4 = 0) by (unfold NB, ofn_bytes; WN.ntc_field).
assert (E12 : TW.u_at NB 12 4 = 0) by (unfold NB, ofn_bytes; WN.ntc_field).
assert (E24 : TW.u_at NB 24 8 = F + 256)
  by (unfold NB, ofn_bytes; WN.ntc_field; try (apply Z.mod_small; lia)).
assert (E32 : TW.u_at NB 32 8 = 0) by (unfold NB, ofn_bytes; WN.ntc_field).
assert (E40 : TW.u_at NB 40 4 = 0) by (unfold NB, ofn_bytes; WN.ntc_field).
assert (E48 : TW.u_at NB 48 8 = 0) by (unfold NB, ofn_bytes; WN.ntc_field).
assert (E56 : TW.u_at NB 56 8 = 0) by (unfold NB, ofn_bytes; WN.ntc_field).
assert (E64 : TW.u_at NB 64 4 = 0) by (unfold NB, ofn_bytes; WN.ntc_field).
assert (E68 : TW.u_at NB 68 2 = 0) by (unfold NB, ofn_bytes; WN.ntc_field).
assert (HFK : trans_src_ok B ly2 S2 W2 memN (F + 448) NTC_SIZE).
{ right. split.
  - left. exists ONANN_CID, pos. rewrite EF. split; [exact Hin|]. unfold NTC_SIZE.
    change (fs_frame_bytes ONANN_CID) with 1024. lia.
  - unfold decode_rd_ok, NTC_SIZE. split; [|split; [|split; [|split; [|split]]]].
    + intros a Ha. apply can_aview_vis. exact (proj1 (HFb a ltac:(lia))).
    + apply (TransportGNotice.frame_ra_zero _ F (F + 448) 72 56 65); [lia | exact DFm8 | lia | lia | exact ZF].
    + apply (TransportGNotice.frame_hull_vis _ F 1024 (F + 448) 72); [lia | exact HF64 | reflexivity | lia | lia | lia |].
      intros i Hi. apply can_aview_vis. exact (proj1 (HFsh i Hi)).
    + apply (amem_range_sub_app F 1024); [exact HFapp | lia | lia | lia | lia].
    + lia.
    + lia. }
assert (HAK : trans_src_ok B ly2 S2 W2 memN (F + 256) ANN_SIZE).
{ right. split.
  - left. exists ONANN_CID, pos. rewrite EF. split; [exact Hin|]. unfold ANN_SIZE.
    change (fs_frame_bytes ONANN_CID) with 1024. lia.
  - unfold decode_rd_ok, ANN_SIZE. split; [|split; [|split; [|split; [|split]]]].
    + intros a Ha. apply can_aview_vis. exact (proj1 (HFb a ltac:(lia))).
    + apply (TransportGNotice.frame_ra_zero _ F (F + 256) 20 32 37); [lia | exact DFm8 | lia | lia | exact ZA].
    + apply (TransportGNotice.frame_hull_vis _ F 1024 (F + 256) 20); [lia | exact HF64 | reflexivity | lia | lia | lia |].
      intros i Hi. apply can_aview_vis. exact (proj1 (HFsh i Hi)).
    + apply (amem_range_sub_app F 1024); [exact HFapp | lia | lia | lia | lia].
    + lia.
    + lia. }
unfold trans_ntc_at.
split; [lia|]. split; [rewrite Z.add_mod, DFm8 by lia; reflexivity|].
split; [exact HFK|].
split; [left; unfold NTC_SIZE; lia|].
exists NB.
split; [exact HNB|]. split; [exact ELEN|].
unfold onann_fntc, onann_ann.
cbn [TI.n_kind TI.n_state TI.n_old TI.n_reason TI.n_pers TI.n_mac_offset TI.n_body_len TI.n_counter TI.n_retry
  TI.n_body TI.n_ann TI.ta_version TI.ta_name length].
unfold TW.s32_at.
split; [rewrite E0; reflexivity|].
split; [rewrite E4; apply WN.swrap32_mod; exact Hst|].
split; [rewrite E8; reflexivity|].
split; [rewrite E12; reflexivity|].
split; [exact E32|].
split; [rewrite E40; reflexivity|].
split; [exact E56|].
split; [exact E64|].
split; [exact E68|].
rewrite E48.
split; [apply garr8_nil|].
split; [exact (trans_src_ok_null B ly2 S2 W2 memN)|].
split; [left; cbn [Z.of_nat]; lia|].
rewrite E24.
split; [lia|]. split; [rewrite Z.add_mod, DFm8 by lia; reflexivity|].
split; [exact HV|].
split; [exact HNm|].
split; [unfold ONANN_A in HAK; exact HAK|].
left. unfold ANN_SIZE. lia.
Qed.

(* An N_FOREIGN notice stores GOT.foreign only: apart from fn's bytes, from its empty body, from the announce (a
   frame byte is not a byte of G) and from TF (onann_apart through onann_wr_fntc). *)
Lemma ofn_apart : forall ly2 S2 (W2 : world segs) memN mdN (TF : option TI.tframe) (Bw b Bf : list byte) F pos fp,
  AR_laws segs B -> @AR rc segs B ly2 S2 W2 memN mdN -> In (ONANN_CID, pos) (frames S2) ->
  frame_addr ly2 ONANN_CID pos = F ->
  (forall a, F <= a < F + 1024 -> ~ inG TG.G_HARNESS a) ->
  garr8 segs (mrestrict (w_H W2) memN) (F + 448) (map DSpec.bz (ofn_bytes (TW.S_state Bf) fp F)) ->
  onann_apart TF Bw b ->
  notice_apart W2 memN (F + 448) (onann_fntc Bf b) TF Bf.
Proof.
intros ly2 S2 W2 memN mdN TF Bw b Bf F pos fp LAWS HAR Hin EF HFoffG HNB Hap x Hx.
assert (HG : inG TG.G_HARNESS x) by exact (onann_ntc_wr_G Bf (onann_fntc Bf b) x Hx).
assert (HNF : forall y, F <= y < F + 1024 -> x <> y)
  by (intros y Hy Hxy; apply (HFoffG y Hy); rewrite <- Hxy; exact HG).
split; [|split].
- intros Hr. unfold NTC_SIZE in Hr. exact (HNF x ltac:(lia) eq_refl).
- intros NB HNB2 HL2.
  assert (ENB : NB = ofn_bytes (TW.S_state Bf) fp F).
  { apply (ofn_garr8_det (w_H W2) memN (F + 448));
      [rewrite HL2, ofn_bytes_len; reflexivity | exact HNB2 | exact HNB]. }
  rewrite ENB. split.
  + unfold onann_fntc. cbn [TI.n_body length Z.of_nat]. lia.
  + intros _.
    assert (E24 : TW.u_at (ofn_bytes (TW.S_state Bf) fp F) 24 8 = F + 256).
    { unfold ofn_bytes. WN.ntc_field. apply Z.mod_small.
      destruct (al_frames _ _ LAWS ly2 S2 W2 memN mdN ONANN_CID pos HAR Hin) as (_ & Happ & _ & _).
      rewrite EF in Happ. change (fs_frame_bytes ONANN_CID) with 1024 in Happ.
      unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
      pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
      destruct (frames_bounds segs B LAWS ly2 S2 W2 memN mdN ONANN_CID pos HAR Hin) as (G1 & G2 & _).
      rewrite EF in G1, G2. change (fs_frame_bytes ONANN_CID) with 1024 in G2. lia. }
    rewrite E24. unfold ANN_SIZE. intros Hr. exact (HNF x ltac:(lia) eq_refl).
- exact (onann_apart_ntc TF Bw b (notice_wr Bf (onann_fntc Bf b)) Hap
    (fun y Hy => onann_wr_fntc Bf Bf Bw b y Hy) x Hx).
Qed.

Lemma onann_piece_fn_holds : @onann_fn_stmt fx rc B MT.
Proof.
unfold onann_fn_stmt. intros SL2 FNREL. unfold onann_fn_at.
intros LAWS0 CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F B2
  ly2 S2 W2 mem2 md2 regs2 HFIX HCUR HREGS.
pose proof LAWS0 as (HSM & HCELLS & HZC & HGU & HGNE & HROU & HRNE & LAWS & MTL & MTF & SMP & ASF & FFL & HGX & HGE).
pose proof CALLEES as (ASM0 & LEAF0 & PFROM0 & BCMP0 & HMS & HN & WAKE0 & MO0 & SETSH0).
pose proof HFIX as (HJ0 & Hret & Hra & Hgp & Htp & H10 & H11 & H12 & Hsp16 & Hlo & Hhi & Hnow & Hdf & Htw0 & Hgf0 &
  Hm & HTFa & Htfg & Hrom & Hap & Hri0 & Hcnt & Hcnt2 & Hev & Esp1 & EF & HF0 & HF64 & HFc & HFapp).
pose proof HCUR as ((HJ2 & He0 & Hfrs & Hperm & HlyF & Hmo & HK & Hsaved & HFLw) & Htw2 & Hb2 & Hkfn & Hgf2 & Haok &
  HSA & S40 & S56).
pose proof HSA as (S8 & S16 & S24 & S48).
pose proof HREGS as ((((R2 & R3 & R4 & R8 & R9 & R18 & R19) & R20 & R24 & R25 & R26) & R10) & R11 & R22).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (onann_cur_ar B MT LAWS HFIX (proj1 HCUR)) as (HARc & HAR2 & ELO2 & EHI2 & EFA & EFL & Hin & EFA2 & HFpres & HSHpres
  & HFoffG & HF0b & HF64b & HFcb & HFappb & Hce & Hslo & Hshi & H47 & HFLpres & HFLown & HFLb & HFLs1 & HFLs2).
pose proof (proj1 Haok) as HAV. pose proof (proj1 (proj2 Haok)) as HAN.
pose proof (proj2 (proj2 (proj2 (proj2 Haok)))) as HAsh.
assert (HFR : ONANN_FRAME = 192) by reflexivity.
assert (Hsp1 : spZ regs - 224 <= sp1 <= spZ regs - 192 /\ sp1 mod 32 = 0).
{ rewrite Esp1. rewrite HFR.
  pose proof (Z.div_mod (spZ regs - 192) 32 ltac:(lia)) as D.
  pose proof (Z.mod_pos_bound (spZ regs - 192) 32 ltac:(lia)) as M.
  set (q := (spZ regs - 192) / 32) in *. set (r := (spZ regs - 192) mod 32) in *.
  split; [lia|]. rewrite Z.mul_comm, Z.mod_mul by lia. reflexivity. }
destruct Hsp1 as (Hsp1r & Hsp1a).
assert (HSTKn : ONANN_STK = 8992) by reflexivity.
assert (HNSTK : NOTICE_STK = 8240) by reflexivity.
assert (HES : ESTACK = 4096) by reflexivity.
assert (Hspb : 2 ^ 46 <= sp1 <= 2 ^ 47) by lia.
assert (HFG : F + 1024 <= ONANN_S \/ ONANN_S + TW.SZ_g_s <= F).
{ destruct (Z_le_gt_dec (F + 1024) ONANN_S) as [h|h]; [left; exact h|].
  destruct (Z_le_gt_dec (ONANN_S + TW.SZ_g_s) F) as [h2|h2]; [right; exact h2|].
  exfalso.
  assert (Hx : exists x, F <= x < F + 1024 /\ ONANN_S <= x < ONANN_S + TW.SZ_g_s).
  { destruct (Z_le_gt_dec F ONANN_S) as [h3|h3]; [exists ONANN_S | exists F];
    unfold TW.SZ_g_s, ONANN_S, TA_g_s in *; lia. }
  destruct Hx as (x & Hx1 & Hx2). exact (HFoffG x Hx1 (ofn_inG x Hx2)). }
assert (HLB2 : length B2 = Z.to_nat TW.W_LEN) by exact (tw_len _ _ _ Htw2).
set (Bf := TW.set_S_foreign B2 1) in *.
assert (HLBf : length Bf = Z.to_nat TW.W_LEN) by (unfold Bf; exact (ofn_len_bf B2 HLB2)).
assert (ESTf : TW.S_state Bf = TW.S_state B2) by (unfold Bf; exact (ofn_bf_state B2 HLB2)).
assert (EGFf : TW.g_fail_next Bf = TW.g_fail_next B2) by (unfold Bf; exact (ofn_bf_gfn B2 HLB2)).
unfold onann_k_fn in Hkfn.
destruct (TSS.call_notify timg_A TF Bf (onann_fntc Bf b)) as [[B3 u3]|] eqn:ECN; [|discriminate Hkfn].
destruct u3.
destruct (ofn_model TF Bf b B3 ECN) as (HNT & HNM).
destruct (onann_fg_world TF Bf b B3 ECN) as (d3 & EB3).
assert (HLB3 : length B3 = Z.to_nat TW.W_LEN)
  by (rewrite EB3; unfold TW.set_GOT_foreign; pose proof HLBf as L; wlen).
assert (EST3 : TW.S_state B3 = TW.S_state B2) by (rewrite EB3, (ofn_b3_state Bf d3 HLBf); exact ESTf).
assert (EGF3 : TW.g_fail_next B3 <= 1) by (rewrite EB3, (ofn_b3_gfn Bf d3 HLBf), EGFf; exact Hgf2).
assert (Hst3 : - 2 ^ 31 <= TW.S_state B3 < 2 ^ 31) by apply ofn_state_range.
assert (Hbl : forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly2 S2))
  by (intros bm Hbm; exact (Permutation_in _ (Permutation_sym Hperm) Hbm)).
destruct (dkg_nf_sep_gw segs B LAWS transport_segs_low lyc Sc ly2 S2 W2 mem2 md2 ONANN_CID pos F
  (flag_addr lyc ONANN_CID pos) HAR2 Hfrs Hbl HlyF EF eq_refl FFL) as (N1 & N2 & N3 & N4).
pose proof (Z.div_mod F 64 ltac:(lia)) as DF. rewrite HF64b, Z.add_0_r in DF.
assert (HF8 : F / 8 = 8 * (F / 64))
  by (rewrite DF at 1; replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by ring; apply Z.div_mul; lia).
assert (HFlt : F + 1024 <= 2 ^ 47) by lia.
assert (HF8b : 512 <= F / 8 <= 2 ^ 44).
{ split; [apply Z.div_le_lower_bound; lia |].
  apply Z.div_le_upper_bound; [lia | change (8 * 2 ^ 44) with 140737488355328; lia]. }
assert (HSHF : SHADOW_OFF + F / 8 + 128 <= F \/ F + 1024 <= SHADOW_OFF + F / 8).
{ unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFappb.
  destruct HFappb as (_ & [HL | (HH1 & HH2)]); [right | left]; unfold SHADOW_OFF; lia. }
assert (HZin : forall x, OFN_Z F sp1 x ->
  (spZ regs - ONANN_STK <= x < spZ regs) \/ dkg_nf ONANN_CID F (flag_addr lyc ONANN_CID pos) x \/
  inG TG.G_HARNESS x).
{ intros x [Hz | [Hz | [Hz | Hz]]].
  - right; left. right; left. change (fs_frame_bytes ONANN_CID / 8) with 128. lia.
  - right; left. left. change (fs_frame_bytes ONANN_CID) with 1024. lia.
  - right; right. apply ofn_inG. unfold TW.SZ_g_s, ONANN_S, TA_g_s in *. lia.
  - left. lia. }
assert (HGnZ : forall x, inG TG.G_HARNESS x -> ~ (ONANN_S + 136 <= x < ONANN_S + 140) -> ~ OFN_Z F sp1 x).
{ intros x Hxg Hn Hz. pose proof (inG_low segs B transport_segs_low _ x HGX Hxg) as Hl.
  unfold kLowMemEnd in Hl.
  destruct Hz as [Hz | [Hz | [Hz | Hz]]].
  - unfold SHADOW_OFF in Hz. lia.
  - destruct (HGX x Hxg) as [Hi _]. apply (N2 x); [|exact Hi].
    unfold dkg_nf. left. change (fs_frame_bytes ONANN_CID) with 1024. lia.
  - exact (Hn Hz).
  - lia. }
(* ---------------- run 1: +0x58c .. +0x608 ---------------- *)
pose proof (ofn_entry ly2 S2 W2 regs2 mem2 md2 B2 sp1 F HZC HAR2 Htw2 R9 R18 R19 R10 R11 R24 R25 R26
  Hspb Hsp1a HF0b HF64b ltac:(lia) HFappb HFG
  ltac:(intros a Ha; exact (proj1 (HFpres a ltac:(lia))))
  ltac:(intros i Hi; exact (proj1 (HSHpres i ltac:(lia))))
  S8 S16 S24 S40 S48 S56) as HS.
set (E0 := ofn_E regs2 B2) in HS.
assert (HEI : img_env VAL A_LIM E0) by (unfold E0, ofn_E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E0 n = YK11.getr regs2 r)
  by (intros n r Hn; unfold E0, ofn_E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (U18 : bv_unsigned (ew E0 18) = F)
  by (rewrite (EE 18%nat 18%bv eq_refl), R18; unfold w64; apply unsigned_lit_small; lia).
assert (U19 : bv_unsigned (ew E0 19) = SHADOW_OFF + F / 8)
  by (rewrite (EE 19%nat 19%bv eq_refl), R19; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (E34 : ew E0 34 = Z_to_bv 64 (TW.u_at B2 (TW.OFF_g_s + 112) 4)).
{ unfold E0, ofn_E. rewrite Eimg_low by (unfold A_TEXT; lia).
  pose proof (ew_Ereg_extra regs2 (ofn_vals B2) 2) as X. cbn [Nat.add nth ofn_vals] in X. exact X. }
assert (E32v : ew E0 32 = Z_to_bv 64 (TW.u_at B2 (TW.OFF_g_s + 96) 8)).
{ unfold E0, ofn_E. rewrite Eimg_low by (unfold A_TEXT; lia).
  pose proof (ew_Ereg_extra regs2 (ofn_vals B2) 0) as X. cbn [Nat.add nth ofn_vals] in X. exact X. }
assert (SHOK : sh_ok segs OFN_Bx (@nil shent) E0 (mrestrict (w_H W2) mem2)) by constructor.
pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX
  0 []) as RUNTO.
pose proof (paj_branch (fx := fx) (PI := PI_transport)) as BR.
paj_run_tok RUN HS HJ2 SHOK OFN_B0.
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fpx ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fpx b0 bc lyq ownq) end;
  eapply awr_ok_x_cons_own with (cid := ONANN_CID) (pos := pos); [left; reflexivity | |];
  [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U19 in Ha;
    right; unfold in_zr, shadow_addr; cbn [fst snd]; rewrite EFA2;
    change (fs_frame_bytes ONANN_CID / 8) with 128; lia |];
  eapply awr_ok_x_cons_own with (cid := ONANN_CID) (pos := pos); [left; reflexivity | |];
  [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U18 in Ha;
    left; unfold in_zr; cbn [fst snd]; rewrite EFA2; change (fs_frame_bytes ONANN_CID) with 1024; lia |];
  apply awr_ok_x_cons_g;
  [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
    apply ofn_inG; unfold ONANN_S, TA_g_s, TW.SZ_g_s in *; lia |];
  apply awr_ok_x_cons; [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |];
  apply awr_ok_x_cons; [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |];
  apply awr_ok_x_nil. }
set (md1 := with_vm_backing (m_vm_lazy md2) mat md2) in *. clearbody md1. clear mat.
assert (KR1 : forall a, 0 <= a < 2 ^ 64 -> ~ OFN_Z F sp1 a ->
  aview segs (w_H W2) (ms_mem ms) a = aview segs (w_H W2) mem2 a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ (OFN_Z F sp1) HFr); [| exact Ha | exact Hn].
  intros b0 wlo whi x Hiw Hx. cbv beta.
  ofn_win Hiw Hx ltac:(rewrite ?U18, ?U19 in Hx; unfold OFN_Z, ONANN_S, TA_g_s;
    first [lia | left; lia | right; left; lia | right; right; left; lia]). }
assert (GA1 : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
ofn_region HS 0%nat RG0.
ofn_env HS E1.
assert (HEI1 : img_env VAL A_LIM E1) by (unfold E1; exact HEI).
assert (E1lo : forall n, (n < 1024)%nat -> ew E1 n = ew E0 n)
  by (intros n Hn; unfold E1; rewrite ?ew_ewset_other by lia; reflexivity).
assert (U18b : bv_unsigned (ew E1 18) = F) by (rewrite E1lo by lia; exact U18).
assert (U19b : bv_unsigned (ew E1 19) = SHADOW_OFF + F / 8) by (rewrite E1lo by lia; exact U19).
assert (ZS1 : forall i, 56 <= i < 65 -> aview segs (w_H W2) (ms_mem ms) (SHADOW_OFF + F / 8 + i) = Some 0).
{ intros i Hi. rewrite <- U19b.
  assert (Hi' : i = 56 \/ i = 57 \/ i = 58 \/ i = 59 \/ i = 60 \/ i = 61 \/ i = 62 \/ i = 63 \/ i = 64) by lia.
  destruct Hi' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]];
  apply (ofn_chunk0 E1 (w_H W2) (ms_mem ms) (Some 19%nat) _ _ _ _ _ _ RG0);
  cbn [In]; repeat (first [left; reflexivity | right]). }
clear RG0 HF HFr HG.
pmkst HS.
ofn_reg HS (Z_to_bv 5 10) (Z_to_bv 64 (F + 480)) Q10 ltac:(cbn [sv_denot]; rewrite U18b; reflexivity).
ofn_reg HS (Z_to_bv 5 11) (Z_to_bv 64 0) Q11 ltac:(reflexivity).
ofn_reg HS (Z_to_bv 5 12) (Z_to_bv 64 40) Q12 ltac:(reflexivity).
ofn_reg HS (Z_to_bv 5 2) (w64 sp1) Q2
  ltac:(cbn [sv_denot]; rewrite E1lo by lia; rewrite (EE 2%nat 2%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        exact R2).
ofn_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 28192)) Q1 ltac:(apply codeptr_val; exact HEI).
ofn_reg HS (3%bv : bv 5) (w64 (as_gp B)) Q3
  ltac:(cbn [sv_denot]; rewrite E1lo by lia; rewrite (EE 3%nat 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        exact (eq_trans R3 Hgp)).
ofn_reg HS (4%bv : bv 5) (w64 (as_tp B)) Q4
  ltac:(cbn [sv_denot]; rewrite E1lo by lia; rewrite (EE 4%nat 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        exact (eq_trans R4 Htp)).
assert (QSP : spZ (ms_regs ms) = sp1)
  by (change (bv_unsigned (YK11.getr (ms_regs ms) (Z_to_bv 5 2)) = sp1); rewrite Q2; unfold w64;
      apply unsigned_lit_small; lia).
(* ---------------- +0x60c: __asan_memset (fn + 32, 0, 40) ---------------- *)
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transport_sigma TS___asan_memset)) mm rom) mdx) Q) end.
eapply SRr_bind.
{ apply (@gx_intrin_at fx rc tfib_sink_head segs B LAWS transport_segs_low OSet (transport_sigma TS___asan_memset)
    (HMS fx) TG.G_HARNESS W2 (ms_regs ms) (ms_mem ms) STK sp0 FP ly S W0 mem0 md0 ((ONANN_CID, pos) :: own) ly2 S2
    md1 (k + 0) (F + 480) 0 40 (sp1 - sp0) (Z_to_bv 64 (BASE + 28192)) HGX G_HARNESS_rw HJ2 Q10 Q11 Q12).
  - lia.
  - lia.
  - lia.
  - rewrite QSP. lia.
  - pose proof (Z.div_mod sp1 32 ltac:(lia)) as D1. pose proof (Z.div_mod sp0 16 ltac:(lia)) as D2.
    rewrite Hsp1a, Z.add_0_r in D1.
    pose proof HJ0 as (_ & _ & (memS0 & HJi0 & _) & _). rewrite !Z.add_0_r in HJi0.
    pose proof HJi0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk0 & _).
    destruct Hstk0 as (Hsp0a & _). rewrite Hsp0a, Z.add_0_r in D2.
    rewrite D1, D2. replace (32 * (sp1 / 32) - 16 * (sp0 / 16)) with ((2 * (sp1 / 32) - sp0 / 16) * 16) by ring.
    apply Z.mod_mul. lia.
  - lia.
  - lia.
  - exact Q3.
  - exact Q4.
  - exact Q1.
  - apply (ret_ok_codeptr_v (PI := PI_transport)); [lia | reflexivity].
  - eapply (transport_twr_ok_g_intro segs B LAWS); [exact HJ2|]. intros a Ha. left. rewrite QSP. split.
    + unfold awr_byte. right; right; right. unfold in_frames. exists ONANN_CID, pos. split; [left; reflexivity|].
      left. unfold in_zr. cbn [fst snd]. rewrite EFA2. change (fs_frame_bytes ONANN_CID) with 1024. lia.
    + lia.
  - apply (amem_range_sub_app F 1024); [exact HFappb | lia | lia | lia | lia].
  - apply (TransportGNotice.frame_ra_zero _ F (F + 480) 40 60 65); [lia | | lia | lia |].
    + pose proof (Z.div_mod F 64 ltac:(lia)) as D. rewrite HF64b, Z.add_0_r in D. rewrite D.
      replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by ring. apply Z.mod_mul. lia.
    + intros i Hi. exact (ZS1 i ltac:(lia)).
  - intros _. apply (TransportGNotice.frame_hull_vis _ F 1024 (F + 480) 40);
      [lia | exact HF64b | reflexivity | lia | lia | lia |].
    intros i Hi. apply can_aview_vis.
    destruct (al_frames _ _ LAWS ly2 S2 W2 (ms_mem ms) md1 ONANN_CID pos
      (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) Hin) as (_ & _ & _ & HFsh1).
    rewrite EFA2 in HFsh1. change (fs_frame_bytes ONANN_CID / 8) with 128 in HFsh1.
    change (shadow_addr F) with (SHADOW_OFF + F / 8) in HFsh1. exact (proj1 (HFsh1 i Hi)).
  - exact I. }
cbv beta. intros Wm cm _ (-> & regsM & memM & mdM & -> & HJ3 & HPM & HA0M & HsetM & HeffM & HgrM).
assert (KAM : forall a, 0 <= a < 2 ^ 64 -> ~ OFN_Z F sp1 a ->
  aview segs (w_H W2) memM a = aview segs (w_H W2) mem2 a).
{ intros a Ha Hn. rewrite HeffM; [exact (KR1 a Ha Hn) | exact Ha | |].
  - intros Hd. apply Hn. right; left. lia.
  - intros Hd. apply Hn. right; right; right. lia. }
assert (GAM : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) memM a)
  by (intros a Ha; exact (HgrM a (GA1 a Ha))).
assert (ZMM : forall a, F + 480 <= a < F + 520 -> aview segs (w_H W2) memM a = Some 0).
{ intros a Ha. replace a with ((F + 480) + (a - (F + 480))) by lia.
  rewrite (HsetM (a - (F + 480)) ltac:(lia)). reflexivity. }
jafter_call_keep_hi HS 1024%nat regsM (mrestrict (w_H W2) memM) HPM [0%nat; 1%nat; 2%nat; 3%nat; 4%nat] HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq) end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
  - apply ofn_rk; [| exact HgrM]. intros a Ha. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in Ha.
    rewrite U19b in Ha. apply HeffM; unfold SHADOW_OFF in *; lia.
  - apply ofn_rk; [| exact HgrM]. intros a Ha. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in Ha.
    rewrite U18b in Ha. apply HeffM; lia.
  - apply ofn_rk; [| exact HgrM]. intros a Ha. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in Ha.
    apply HeffM; [unfold ONANN_S, TA_g_s in *; lia | |];
      [destruct HFG; unfold ONANN_S, TA_g_s, TW.SZ_g_s in *; lia | unfold ONANN_S, TA_g_s in *; lia].
  - apply ofn_rk; [| exact HgrM]. intros a Ha. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in Ha.
    unfold OFN_SH in *. apply HeffM; [lia | |];
      [unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFappb;
       destruct HFappb as (_ & [HL | (HH1 & HH2)]); lia | lia].
  - apply ofn_rk; [| exact HgrM]. intros a Ha. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in Ha.
    assert (U9b : bv_unsigned (ew E1 9) = sp1)
      by (rewrite E1lo by lia; rewrite (EE 9%nat 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
    rewrite U9b in Ha. apply HeffM; lia. }
specialize (HS2 HRK). clear HRK HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
set (E2 := havoc E1 1024 (map (YK11.getr regsM) CLOB)) in HS.
assert (HEI2 : img_env VAL A_LIM E2) by (apply img_env_havoc_hi; [exact HEI | cbv; lia]).
assert (E2lo : forall n, (n < 1024)%nat -> ew E2 n = ew E1 n) by (intros n Hn; apply ew_havoc_old; exact Hn).
assert (U18c : bv_unsigned (ew E2 18) = F) by (rewrite E2lo by lia; exact U18b).
assert (U19c : bv_unsigned (ew E2 19) = SHADOW_OFF + F / 8) by (rewrite E2lo by lia; exact U19b).
assert (SHOK2 : sh_ok segs OFN_Bx (@nil shent) E2 (mrestrict (w_H W2) memM)) by constructor.
clear dependent ms.
(* ---------------- run 2: +0x610 .. +0x638 ---------------- *)
paj_run_tok RUN HS HJ3 SHOK2 OFN_B0.
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fpx ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fpx b0 bc lyq ownq) end;
  eapply awr_ok_x_cons_own with (cid := ONANN_CID) (pos := pos); [left; reflexivity | |];
  [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U19c in Ha;
    right; unfold in_zr, shadow_addr; cbn [fst snd]; rewrite EFA2;
    change (fs_frame_bytes ONANN_CID / 8) with 128; lia |];
  eapply awr_ok_x_cons_own with (cid := ONANN_CID) (pos := pos); [left; reflexivity | |];
  [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U18c in Ha;
    left; unfold in_zr; cbn [fst snd]; rewrite EFA2; change (fs_frame_bytes ONANN_CID) with 1024; lia |];
  apply awr_ok_x_cons_g;
  [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
    apply ofn_inG; unfold ONANN_S, TA_g_s, TW.SZ_g_s in *; lia |];
  apply awr_ok_x_cons; [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |];
  apply awr_ok_x_cons; [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |];
  apply awr_ok_x_nil. }
set (md3 := with_vm_backing (m_vm_lazy mdM) mat mdM) in *. clearbody md3. clear mat.
assert (KRN : forall a, 0 <= a < 2 ^ 64 -> ~ OFN_Z F sp1 a ->
  aview segs (w_H W2) (ms_mem ms) a = aview segs (w_H W2) memM a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ (OFN_Z F sp1) HFr); [| exact Ha | exact Hn].
  intros b0 wlo whi x Hiw Hx. cbv beta.
  ofn_win Hiw Hx ltac:(rewrite ?U18c, ?U19c in Hx; unfold OFN_Z, ONANN_S, TA_g_s;
    first [lia | left; lia | right; left; lia | right; right; left; lia]). }
assert (KAN : forall a, 0 <= a < 2 ^ 64 -> ~ OFN_Z F sp1 a ->
  aview segs (w_H W2) (ms_mem ms) a = aview segs (w_H W2) mem2 a)
  by (intros a Ha Hn; rewrite (KRN a Ha Hn); exact (KAM a Ha Hn)).
assert (GAN : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG (GAM a Ha))).
assert (ZMN : forall a, F + 480 <= a < F + 520 -> aview segs (w_H W2) (ms_mem ms) a = Some 0).
{ intros a Ha. rewrite <- (ZMM a Ha).
  apply (kept_of_frame _ _ _ _ _ (fun x => (SHADOW_OFF + F / 8 + 56 <= x < SHADOW_OFF + F / 8 + 65) \/
    (F + 448 <= x < F + 480) \/ (ONANN_S + 136 <= x < ONANN_S + 140)) HFr); [| lia |].
  - intros b0 wlo whi x Hiw Hx. cbv beta.
    ofn_win Hiw Hx ltac:(rewrite ?U18c, ?U19c in Hx; unfold ONANN_S, TA_g_s;
      first [lia | left; lia | right; left; lia | right; right; lia]).
  - cbv beta. unfold ONANN_S, TA_g_s, TW.SZ_g_s in *.
    intros [Hx | [Hx | Hx]]; [destruct HSHF as [Hg | Hg]; unfold SHADOW_OFF in *; lia | lia |
      destruct HFG as [Hg | Hg]; lia]. }
clear HF HFr HG.
ofn_region HS 0%nat RS0.
ofn_region HS 1%nat RS1.
ofn_region HS 2%nat RS2.
ofn_env HS E3.
assert (E3lo : forall n, (n < 1024)%nat -> ew E3 n = ew E2 n)
  by (intros n Hn; unfold E3; rewrite ?ew_ewset_other by lia; reflexivity).
assert (U18d : bv_unsigned (ew E3 18) = F) by (rewrite E3lo by lia; exact U18c).
assert (U19d : bv_unsigned (ew E3 19) = SHADOW_OFF + F / 8) by (rewrite E3lo by lia; exact U19c).
assert (ZSN : forall i, 56 <= i < 65 -> aview segs (w_H W2) (ms_mem ms) (SHADOW_OFF + F / 8 + i) = Some 0).
{ intros i Hi. rewrite <- U19d.
  assert (Hi' : i = 56 \/ i = 57 \/ i = 58 \/ i = 59 \/ i = 60 \/ i = 61 \/ i = 62 \/ i = 63 \/ i = 64) by lia.
  destruct Hi' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]];
  apply (ofn_chunk0 E3 (w_H W2) (ms_mem ms) (Some 19%nat) _ _ _ _ _ _ RS0);
  cbn [In]; repeat (first [left; reflexivity | right]). }
assert (D34 : sv_denot E3 (SExt true 32 (SOff 34 0)) = Z_to_bv 64 (TW.S_state B2)).
{ apply (ofn_sext E3 34 B2). rewrite E3lo by lia. rewrite E2lo by lia. rewrite E1lo by lia. exact E34. }
pose proof (ofn_chunk_val E3 (w_H W2) (ms_mem ms) _ _ _ _ _ _ 448 4 (SLit 6) RS1
  ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)) as VP0.
pose proof (ofn_chunk_val E3 (w_H W2) (ms_mem ms) _ _ _ _ _ _ 452 4 (SExt true 32 (SOff 34 0)) RS1
  ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)) as VP4.
pose proof (ofn_chunk_val E3 (w_H W2) (ms_mem ms) _ _ _ _ _ _ 456 8 (SLit 0) RS1
  ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)) as VP8.
pose proof (ofn_chunk_val E3 (w_H W2) (ms_mem ms) _ _ _ _ _ _ 464 8 (SOff 22 0) RS1
  ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)) as VP16.
pose proof (ofn_chunk_val E3 (w_H W2) (ms_mem ms) _ _ _ _ _ _ 472 8 (SOff 18 256) RS1
  ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)) as VP24.
pose proof (ofn_chunk_val E3 (w_H W2) (ms_mem ms) _ _ _ _ _ _ (ONANN_S + 136) 4 (SLit 1) RS2
  ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)) as VG.
cbn [base_val] in VP0, VP4, VP8, VP16, VP24, VG. rewrite U18d in VP0, VP4, VP8, VP16, VP24.
change (N.to_nat 4) with 4%nat in VP0, VP4, VG. change (N.to_nat 8) with 8%nat in VP8, VP16, VP24.
change (bv_unsigned (sv_denot E3 (SLit 6)) mod 2 ^ (8 * Z.of_N 4)) with 6 in VP0.
change (bv_unsigned (sv_denot E3 (SLit 0)) mod 2 ^ (8 * Z.of_N 8)) with 0 in VP8.
change (bv_unsigned (sv_denot E3 (SLit 1)) mod 2 ^ (8 * Z.of_N 4)) with 1 in VG.
rewrite D34 in VP4. apply (ofn_vm_w _ _ 4 (TW.S_state B2) ltac:(lia)) in VP4.
assert (D22 : sv_denot E3 (SOff 22 0) = Z_to_bv 64 fp).
{ cbn [sv_denot]. rewrite E3lo by lia. rewrite E2lo by lia. rewrite E1lo by lia.
  rewrite (EE 22%nat 22%bv eq_refl), R22. unfold w64. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
  reflexivity. }
rewrite D22 in VP16. apply (ofn_vm_w _ _ 8 fp ltac:(lia)) in VP16.
assert (D18 : sv_denot E3 (SOff 18 256) = Z_to_bv 64 (F + 256)) by (cbn [sv_denot]; rewrite U18d; reflexivity).
rewrite D18 in VP24. apply (ofn_vm_w _ _ 8 (F + 256) ltac:(lia)) in VP24.
change (N.to_nat 4) with 4%nat in VP4. change (N.to_nat 8) with 8%nat in VP16, VP24.
pose proof (ofn_nb (w_H W2) (ms_mem ms) F (TW.S_state B2) fp VP0 VP4 VP8 VP16 VP24 ZMN) as HNB.
rewrite <- ESTf in HNB.
assert (E32b : ew E3 32 = Z_to_bv 64 (TI.ti_notice timg_A)).
{ rewrite E3lo by lia. rewrite E2lo by lia. rewrite E1lo by lia. rewrite E32v.
  rewrite <- (ofn_bf_notify B2 HLB2). fold Bf. rewrite HNT. reflexivity. }
ofn_reg HS (Z_to_bv 5 12) (Z_to_bv 64 (TI.ti_notice timg_A)) T12
  ltac:(cbn [sv_denot]; rewrite E32b, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
ofn_reg HS (Z_to_bv 5 11) (w64 (F + 448)) T11 ltac:(cbn [sv_denot]; rewrite U18d; reflexivity).
ofn_reg HS (Z_to_bv 5 2) (w64 sp1) T2
  ltac:(cbn [sv_denot]; rewrite E3lo by lia; rewrite E2lo by lia; rewrite E1lo by lia;
        rewrite (EE 2%nat 2%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R2).
ofn_reg HS (Z_to_bv 5 3) (w64 (as_gp B)) T3
  ltac:(cbn [sv_denot]; rewrite E3lo by lia; rewrite E2lo by lia; rewrite E1lo by lia;
        rewrite (EE 3%nat 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact (eq_trans R3 Hgp)).
ofn_reg HS (Z_to_bv 5 4) (w64 (as_tp B)) T4
  ltac:(cbn [sv_denot]; rewrite E3lo by lia; rewrite E2lo by lia; rewrite E1lo by lia;
        rewrite (EE 4%nat 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact (eq_trans R4 Htp)).
ofn_reg HS (Z_to_bv 5 8) (YK11.getr regs2 (Z_to_bv 5 8)) T8
  ltac:(cbn [sv_denot]; rewrite E3lo by lia; rewrite E2lo by lia; rewrite E1lo by lia;
        rewrite (EE 8%nat (Z_to_bv 5 8) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
ofn_reg HS (Z_to_bv 5 9) (YK11.getr regs2 (Z_to_bv 5 9)) T9
  ltac:(cbn [sv_denot]; rewrite E3lo by lia; rewrite E2lo by lia; rewrite E1lo by lia;
        rewrite (EE 9%nat (Z_to_bv 5 9) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
ofn_reg HS (Z_to_bv 5 18) (YK11.getr regs2 (Z_to_bv 5 18)) T18
  ltac:(cbn [sv_denot]; rewrite E3lo by lia; rewrite E2lo by lia; rewrite E1lo by lia;
        rewrite (EE 18%nat (Z_to_bv 5 18) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
ofn_reg HS (Z_to_bv 5 19) (YK11.getr regs2 (Z_to_bv 5 19)) T19
  ltac:(cbn [sv_denot]; rewrite E3lo by lia; rewrite E2lo by lia; rewrite E1lo by lia;
        rewrite (EE 19%nat (Z_to_bv 5 19) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
ofn_reg HS (Z_to_bv 5 20) (YK11.getr regs2 (Z_to_bv 5 20)) T20
  ltac:(cbn [sv_denot]; rewrite E3lo by lia; rewrite E2lo by lia; rewrite E1lo by lia;
        rewrite (EE 20%nat (Z_to_bv 5 20) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
ofn_reg HS (Z_to_bv 5 23) (w64 F) T23
  ltac:(cbn [sv_denot]; rewrite U18d, Z.add_0_r; reflexivity).
ofn_reg HS (Z_to_bv 5 24) (w64 SHADOW_OFF) T24 ltac:(reflexivity).
ofn_reg HS (Z_to_bv 5 25) (w64 (ONANN_S + 104)) T25 ltac:(reflexivity).
ofn_reg HS (Z_to_bv 5 26) (w64 (OFN_SH + 2)) T26 ltac:(reflexivity).
assert (KCN : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W2 (ms_mem ms) (spZ regs - ONANN_STK) (spZ regs)
  (onann_wr Bw b)).
{ apply (dk_kept_nfz_gw segs B LAWS transport_segs_low TG.G_HARNESS lyc Sc ly2 S2 W memc mdc W2 mem2 md2 mem2
    (ms_mem ms) (spZ regs - ONANN_STK) (spZ regs) ONANN_CID pos F (flag_addr lyc ONANN_CID pos) (onann_wr Bw b)
    (OFN_Z F sp1) HGX HARc HAR2 Hfrs Hbl HlyF EF eq_refl FFL); [lia | lia | exact HZin | exact HK | | exact GAN].
  intros a Ha Hn. exact (KAN a Ha Hn). }
assert (PTW : tw_at TMAP_A (aview segs (w_H W2) (ms_mem ms)) Bf).
{ unfold Bf. rewrite ofn_bf_eq.
  apply (tw_write TMAP_A (aview segs (w_H W2) mem2) _ B2 TW.OFF_g_s TA_g_s TW.SZ_g_s 136 4 1 TMAP_A_ok Htw2
    TMAP_A_g_s); [lia | unfold TW.SZ_g_s; lia | |].
  - intros j Hj. unfold aview. replace (TA_g_s + 136 + Z.of_nat j) with (0 + (ONANN_S + 136) + Z.of_nat j)
      by (unfold ONANN_S; lia).
    rewrite (VG j Hj). cbn [option_map]. f_equal.
    rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
    apply Z.mod_small. unfold YO0f.le_byte. apply Z.mod_pos_bound. lia.
  - intros x Hx Hn. destruct Hx as (o & bb & n & Hin3 & Hx).
    assert (HxG : inG TG.G_HARNESS x).
    { unfold inG. apply Exists_exists. exists (bb, n).
      split; [exact (TMAP_A_in_G o bb n Hin3) | unfold in_zr; cbn [fst snd]; lia]. }
    apply KAN; [pose proof (inG_low segs B transport_segs_low _ x HGX HxG); unfold kLowMemEnd in *; lia|].
    apply HGnZ; [exact HxG | unfold ONANN_S; cbn [Z.of_nat Pos.of_succ_nat] in Hn; lia]. }
assert (P4 : 0 <= TI.ti_notice timg_A < 2 ^ 64) by (rewrite (proj1 notice_at); lia).
assert (P5 : TI.ti_notice timg_A mod 2 = 0) by (rewrite (proj1 notice_at); reflexivity).
eapply (SRr_jalr_call_pi (PL := PL_transport) (PI := PI_transport) W2 E3 _ _ _ _ 0x600e7 (1%bv : bv 5)
  (12%bv : bv 5) (TI.ti_notice timg_A) HEI2 HS eq_refl);
  [ vm_compute; reflexivity | vm_refl_bv | reflexivity | cbn [ss_pc]; lia | exact T12 | exact P4 | exact P5 |].
intros matC ms1 Ems1 _. subst ms1.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Qx =>
  set (regsC := rg); set (mdC := mdx);
  change (SRr segs Wx (@cfg_at fx segs (TI.ti_notice timg_A) regsC (ms_mem ms) mdC) Qx) end.
assert (EBN : BASE + (28236 + 4) = 0x880b4) by (vm_compute; reflexivity).
assert (RC1 : YK11.getr regsC 1%bv = Z_to_bv 64 (BASE + (28236 + 4)))
  by (unfold regsC; rewrite YK11.getr_same by (intros Hc; apply (f_equal bv_unsigned) in Hc; vm_compute in Hc;
      discriminate Hc); reflexivity).
assert (RCK : forall r : bv 5, bv_unsigned r <> 1 -> YK11.getr regsC r = YK11.getr (ms_regs ms) r)
  by (intros r Hr; unfold regsC; apply YK11.getr_other; intros Eq; apply Hr; rewrite Eq; reflexivity).
assert (RC2 : YK11.getr regsC 2%bv = w64 sp1) by (rewrite RCK by (vm_compute; discriminate); exact T2).
assert (RC3 : YK11.getr regsC 3%bv = w64 (as_gp B)) by (rewrite RCK by (vm_compute; discriminate); exact T3).
assert (RC4 : YK11.getr regsC 4%bv = w64 (as_tp B)) by (rewrite RCK by (vm_compute; discriminate); exact T4).
assert (RC11 : YK11.getr regsC 11%bv = w64 (F + 448)) by (rewrite RCK by (vm_compute; discriminate); exact T11).
assert (USPC : spZ regsC = sp1) by (unfold spZ; rewrite RC2; unfold w64; apply unsigned_lit_small; lia).
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HARN.
assert (KAA : forall a, F + 256 <= a < F + 276 ->
  aview segs (w_H W2) (ms_mem ms) a = aview segs (w_H W2) mem2 a).
{ intros a Ha. apply KAN; [lia|]. unfold OFN_Z, ONANN_S, TA_g_s, TW.SZ_g_s in *.
  intros [Hz | [Hz | [Hz | Hz]]]; [destruct HSHF; unfold SHADOW_OFF in *; lia | lia |
    destruct HFG; lia | lia]. }
assert (ZAN : forall i, 32 <= i < 37 -> aview segs (w_H W2) (ms_mem ms) (SHADOW_OFF + F / 8 + i) = Some 0).
{ intros i Hi. rewrite KAN; [exact (HAsh i Hi) | unfold SHADOW_OFF in *; lia |].
  unfold OFN_Z, ONANN_S, TA_g_s in *.
  intros [Hz | [Hz | [Hz | Hz]]]; [lia | destruct HSHF; unfold SHADOW_OFF in *; lia |
    unfold SHADOW_OFF in *; lia | unfold SHADOW_OFF in *; lia]. }
assert (HVN : garr8 segs (mrestrict (w_H W2) (ms_mem ms)) (F + ONANN_A)
  (map DSpec.bz (TSS.ann_field (skipn 15 (DSpec.fr_body b))))).
{ eapply garr8_frame; [exact HAV|]. intros a Ha. rewrite length_map in Ha.
  apply (mbyte_of_aview segs). apply KAA. unfold ONANN_A in *.
  pose proof (ofn_ann_len (skipn 15 (DSpec.fr_body b))) as HL. lia. }
assert (HNmN : garr8 segs (mrestrict (w_H W2) (ms_mem ms)) (F + ONANN_A + 10)
  (map DSpec.bz (TSS.ann_field (skipn 24 (DSpec.fr_body b))))).
{ eapply garr8_frame; [exact HAN|]. intros a Ha. rewrite length_map in Ha.
  apply (mbyte_of_aview segs). apply KAA. unfold ONANN_A in *.
  pose proof (ofn_ann_len (skipn 24 (DSpec.fr_body b))) as HL. lia. }
(* +0x63c: the call of notice *)
eapply SRr_bind.
{ exact (HN fx STK sp0 FP ly S W0 mem0 md0 ((ONANN_CID, pos) :: own) ly2 S2 W2 (ms_mem ms) mdC (k + 0) regsC
    (F + 448) (onann_fntc Bf b) TF Bf B3
    ltac:(apply (ajournal_gx_materialize segs B LAWS transport_segs_low); exact HJ3)
    ltac:(rewrite RC1; apply (ret_ok_codeptr_v (PI := PI_transport)); [lia | reflexivity])
    ltac:(unfold raZ; rewrite RC1, EBN; rewrite unsigned_lit_small by lia; lia)
    RC3 RC4 RC11
    ltac:(rewrite USPC; pose proof (Z.div_mod sp1 32 ltac:(lia)) as D1;
          rewrite Hsp1a, Z.add_0_r in D1; rewrite D1;
          replace (32 * (sp1 / 32)) with ((2 * (sp1 / 32)) * 16) by ring; apply Z.mod_mul; lia)
    ltac:(rewrite USPC; lia) ltac:(rewrite USPC; lia)
    (ofn_ntc_at lyc ly2 S2 W2 (ms_mem ms) md3 regsC Bf b F pos fp LAWS HARN Hin EFA2 HF0b HF64b HFcb HFappb
       ltac:(rewrite USPC; lia) ELO2 ZAN ZSN HNB HVN HNmN)
    (onann_tf_call B LAWS HROU HRNE lyc Sc W memc mdc ly2 S2 W2 (ms_mem ms) md3 pos regs regsC NOTICE_STK TF Bw b
       HARc HARN Hfrs Hperm EFA ELO2 EHI2 KCN Htfg ltac:(rewrite USPC; lia) ltac:(rewrite USPC; lia) HTFa)
    (onann_rom_call B HROU HRNE lyc Sc W memc W2 (ms_mem ms) (spZ regs - ONANN_STK) (spZ regs) (onann_wr Bw b)
       Hrom KCN)
    PTW HNM
    (ofn_apart ly2 S2 W2 (ms_mem ms) md3 TF Bw b Bf F pos fp LAWS HARN Hin EFA2 HFoffG HNB Hap)
    ltac:(intros HD; exfalso; unfold onann_fntc in HD; cbn [TI.n_kind] in HD;
          unfold TS0.DIGINET_N_FOREIGN, TC.N_DATA in HD; discriminate HD)
    ltac:(unfold NOTICE_EV; unfold ONANN_EV in Hev; rewrite !Z.add_0_r;
          rewrite !Z.add_0_r in Hev; exact Hev)). }
intros W3 c3 _ HPOST.
unfold transport_notice_post, transport_cg_post in HPOST. cbv beta in HPOST.
destruct HPOST as (ly3 & S3 & regs3 & mem3 & md4 & e3 & -> & He3 & HJ4 & HP4 & Hfr4 & Hperm4 & HK4 & Hmo4 & Htw4).
assert (He30 : e3 = 0) by (unfold NOTICE_EV in He3; lia). subst e3.
rewrite ?Z.add_0_r in HJ4. rewrite ?Z.add_0_r in HJ4.
pose proof HJ4 as (_ & _ & (memS4 & HJi4 & _) & _). rewrite !Z.add_0_r in HJi4.
pose proof HJi4 as (HAR4 & Hlyle4 & _).
pose proof Hlyle4 as (_ & _ & _ & _ & _ & ELF4 & _ & _ & _ & ELO4 & EHI4 & _).
clear HJi4 memS4.
assert (ELF4c : ly_F ly3 = ly_F lyc).
{ pose proof HJ3 as (_ & _ & (memS3 & HJi3 & _) & _).
  pose proof HJi3 as (_ & Hlyle3 & _).
  pose proof Hlyle3 as (_ & _ & _ & _ & _ & ELF3 & _).
  rewrite ELF4, <- ELF3. exact HlyF. }
assert (EFA3 : forall c p, frame_addr ly3 c p = frame_addr lyc c p)
  by (intros c p; unfold frame_addr; rewrite ELF4c; reflexivity).
assert (Hin4 : In (ONANN_CID, pos) (frames S3)) by (rewrite Hfr4; exact Hin).
assert (Hfrs4 : frames S3 = (ONANN_CID, pos) :: frames Sc) by (rewrite Hfr4; exact Hfrs).
assert (Hperm4c : Permutation (ablocks B ly3 S3) (ablocks B lyc Sc))
  by exact (Permutation_trans Hperm4 Hperm).
assert (R3_9 : YK11.getr regs3 (Z_to_bv 5 9) = w64 sp1).
{ rewrite (HP4 9 ltac:(hnf; lia)). rewrite RCK by (vm_compute; discriminate). rewrite T9. exact R9. }
assert (R3_26 : YK11.getr regs3 (Z_to_bv 5 26) = w64 (OFN_SH + 2)).
{ rewrite (HP4 26 ltac:(hnf; lia)). rewrite RCK by (vm_compute; discriminate). exact T26. }
assert (R3_2 : YK11.getr regs3 (Z_to_bv 5 2) = w64 sp1).
{ rewrite (HP4 2 ltac:(hnf; lia)). rewrite RCK by (vm_compute; discriminate). exact T2. }
assert (R3_3 : YK11.getr regs3 (Z_to_bv 5 3) = YK11.getr regs (Z_to_bv 5 3)).
{ rewrite (HP4 3 ltac:(hnf; lia)). rewrite RCK by (vm_compute; discriminate).
  rewrite T3. symmetry. exact Hgp. }
assert (R3_4 : YK11.getr regs3 (Z_to_bv 5 4) = YK11.getr regs (Z_to_bv 5 4)).
{ rewrite (HP4 4 ltac:(hnf; lia)). rewrite RCK by (vm_compute; discriminate).
  rewrite T4. symmetry. exact Htp. }
assert (R3_8 : YK11.getr regs3 (Z_to_bv 5 8) = w64 (spZ regs)).
{ rewrite (HP4 8 ltac:(hnf; lia)). rewrite RCK by (vm_compute; discriminate). rewrite T8. exact R8. }
assert (R3_18 : YK11.getr regs3 (Z_to_bv 5 18) = w64 F).
{ rewrite (HP4 18 ltac:(hnf; lia)). rewrite RCK by (vm_compute; discriminate). rewrite T18. exact R18. }
assert (R3_19 : YK11.getr regs3 (Z_to_bv 5 19) = w64 (SHADOW_OFF + F / 8)).
{ rewrite (HP4 19 ltac:(hnf; lia)). rewrite RCK by (vm_compute; discriminate). rewrite T19. exact R19. }
assert (R3_20 : YK11.getr regs3 (Z_to_bv 5 20) = w64 ONANN_S).
{ rewrite (HP4 20 ltac:(hnf; lia)). rewrite RCK by (vm_compute; discriminate). rewrite T20. exact R20. }
assert (R3_23 : YK11.getr regs3 (Z_to_bv 5 23) = w64 F).
{ rewrite (HP4 23 ltac:(hnf; lia)). rewrite RCK by (vm_compute; discriminate). exact T23. }
assert (R3_24 : YK11.getr regs3 (Z_to_bv 5 24) = w64 SHADOW_OFF).
{ rewrite (HP4 24 ltac:(hnf; lia)). rewrite RCK by (vm_compute; discriminate). exact T24. }
assert (R3_25 : YK11.getr regs3 (Z_to_bv 5 25) = w64 (ONANN_S + 104)).
{ rewrite (HP4 25 ltac:(hnf; lia)). rewrite RCK by (vm_compute; discriminate). exact T25. }
assert (KC4 : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W3 mem3 (spZ regs - ONANN_STK) (spZ regs)
  (onann_wr Bw b)).
{ apply (dk_kept_trans_nf_g segs B TG.G_HARNESS lyc Sc ly2 S2 W memc W2 (ms_mem ms) W3 mem3
    (spZ regs - ONANN_STK) (spZ regs) (spZ regsC - NOTICE_STK) (spZ regsC) (onann_wr Bw b)
    (notice_wr Bf (onann_fntc Bf b)) (dkg_nf ONANN_CID F (flag_addr lyc ONANN_CID pos))).
  - lia.
  - lia.
  - exact EFA.
  - intros f Hf. rewrite Hfrs. right. exact Hf.
  - exact Hbl.
  - exact N1.
  - exact N3.
  - exact KCN.
  - exact HK4.
  - rewrite USPC. lia.
  - rewrite USPC. lia.
  - intros a Ha. left. exact (onann_wr_fntc Bf Bf Bw b a Ha). }
assert (KST4 : forall a, sp1 <= a < spZ regs -> aview segs (w_H W3) mem3 a = aview segs (w_H W2) mem2 a).
{ intros a Ha. pose proof HK4 as (L1 & _). rewrite USPC in L1. rewrite L1 by lia.
  apply KAN; [lia|]. unfold OFN_Z, ONANN_S, TA_g_s, SHADOW_OFF in *.
  intros [Hz | [Hz | [Hz | Hz]]]; lia. }
assert (SL4 : forall o v, 0 <= o <= 56 -> onann_slot W2 mem2 sp1 o v -> onann_slot W3 mem3 sp1 o v).
{ intros o v Ho Hs. unfold onann_slot in *. rewrite <- Hs. apply rdword_ext. intros i Hi. apply KST4. lia. }
assert (HSV4 : Forall (fun o : Z * Z => rdword (aview segs (w_H W3) mem3) (spZ regs - fst o) =
    Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) ONANN_SAVED).
{ assert (HSo : forall o, In o ONANN_SAVED -> 8 <= fst o <= 104).
  { intros o Ho. unfold ONANN_SAVED in Ho. cbn [In] in Ho.
    repeat (destruct Ho as [<- | Ho]; [cbn [fst]; lia|]). destruct Ho. }
  rewrite Forall_forall in Hsaved |- *. intros o Ho. pose proof (HSo o Ho) as Hob.
  rewrite <- (Hsaved o Ho). apply rdword_ext. intros i Hi. apply KST4. lia. }
assert (HFL4 : rdword (aview segs (w_H W3) mem3) (F + 1024 - 8) = Some (flag_addr lyc ONANN_CID pos)).
{ unfold ONANN_FBYTES in HFLw. rewrite <- HFLw. apply rdword_ext. intros i Hi.
  pose proof HK4 as (_ & _ & _ & L4 & _).
  rewrite (L4 ONANN_CID pos (F + 1024 - 8 + i) ltac:(rewrite Hfrs; left; reflexivity)).
  - apply KAN; [lia|]. unfold OFN_Z, ONANN_S, TA_g_s, TW.SZ_g_s in *.
    intros [Hz | [Hz | [Hz | Hz]]]; [destruct HSHF; unfold SHADOW_OFF in *; lia | lia |
      destruct HFG; lia | lia].
  - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFA. rewrite <- EFA2.
    rewrite (EFA ONANN_CID pos). change (fs_frame_bytes ONANN_CID) with 1024. lia.
  - intros Hw. pose proof (onann_ntc_fg_wr Bf (onann_fntc Bf b) (F + 1024 - 8 + i) eq_refl Hw) as Hg.
    apply (HFoffG (F + 1024 - 8 + i) ltac:(lia)).
    apply onann_got_G with (A := TW.A_GOT_foreign) (n := 4);
      [unfold TW.A_GOT_foreign, TW.OFF_GOT; lia | unfold TW.A_GOT_foreign, TW.OFF_GOT, TW.SZ_GOT; lia
       | exact Hg]. }
assert (CUR4 : onann_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw b pos F ly3 S3 W3 mem3 md4 0).
{ refine (conj _ (conj _ (conj Hfrs4 (conj Hperm4c (conj ELF4c (conj _ (conj KC4 (conj HSV4 _)))))))).
  - rewrite ?Z.add_0_r. exact HJ4.
  - assert (HEV0 : ONANN_EV = 0) by reflexivity. rewrite HEV0. lia.
  - exact (mo_le_trans MT MTL _ _ _ _ _ Hmo Hmo4).
  - unfold ONANN_FBYTES. exact HFL4. }
(* ---------------- run 3: +0x640 .. +0x654 ---------------- *)
rewrite RC1. change (Z_to_bv 64 (BASE + (28236 + 4))) with (Z_to_bv 64 (BASE + OFN_RET)).
clear HS SHOK2.
pose proof (ofn_entry3 ly3 S3 W3 regs3 mem3 md4 B3 sp1 HZC HAR4 Htw4 R3_9 R3_26 Hspb Hsp1a
  ltac:(exact (SL4 48 (ONANN_S + 112) ltac:(lia) S48))) as HS.
set (E4 := Eimg (PI := PI_transport) (Ereg regs3 [Z_to_bv 64 (TW.u_at B3 (TW.OFF_g_s + 112) 4)])) in HS.
assert (HEI4 : img_env VAL A_LIM E4) by (unfold E4; apply Eimg_env).
assert (EE4 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E4 n = YK11.getr regs3 r)
  by (intros n r Hn; unfold E4; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E4x : ew E4 32 = Z_to_bv 64 (TW.u_at B3 (TW.OFF_g_s + 112) 4))
  by (unfold E4; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 0)).
assert (SHOK4 : sh_ok segs OFN_Bx (@nil shent) E4 (mrestrict (w_H W3) mem3)) by constructor.
paj_run_tok RUN HS HJ4 SHOK4 OFN_B0.
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fpx ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fpx b0 bc lyq ownq) end;
  apply awr_ok_x_cons; [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |];
  apply awr_ok_x_cons; [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |];
  apply awr_ok_x_cons; [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |];
  apply awr_ok_x_nil. }
set (md6 := with_vm_backing (m_vm_lazy md4) mat md4) in *. clearbody md6. clear mat.
lazymatch type of HS with
| st_ok_pi _ _ _ _ (restrict _ ?mf) => rename mf into ms3
| OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok _ _ _ (restrict _ ?mf) =>
    rename mf into ms3
end.
ofn_env HS E5.
assert (E5lo : forall n, (n < 1024)%nat -> ew E5 n = ew E4 n)
  by (intros n Hn; unfold E5; rewrite ?ew_ewset_other by lia; reflexivity).
assert (KD5 : forall a, aview segs (w_H W3) (ms_mem ms3) a = aview segs (w_H W3) mem3 a).
{ intros a. rewrite (aview_wrap64 segs _ (ms_mem ms3) a), (aview_wrap64 segs _ mem3 a).
  pose proof (Z.mod_pos_bound a (2 ^ 64) ltac:(lia)) as Ha.
  apply (kept_of_frame _ _ _ _ _ (fun _ => False) HFr); [| lia | intros []].
  intros b0 wlo whi x Hiw Hx. cbv beta. ofn_win Hiw Hx ltac:(lia). }
assert (GR5 : forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) (ms_mem ms3) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
clear HF HFr HG.
ofn_reg HS (Z_to_bv 5 21) (Z_to_bv 64 (TW.S_state B3)) X21
  ltac:(apply (ofn_sext _ 32 B3); rewrite E5lo by lia; exact E4x).
ofn_reg HS (Z_to_bv 5 11) (Z_to_bv 64 1) X11 ltac:(reflexivity).
ofn_reg HS (Z_to_bv 5 10)
  (sext 64 (alu32 ALU_ADD (low32 (Z_to_bv 64 (TW.S_state B3))) (low32 (Z_to_bv 64 (-1))))) X10
  ltac:(change (sv_denot E5 (SAluw ALU_ADD (SExt true 32 (SOff 32 0)) (SLit (-1))))
          with (sext 64 (alu32 ALU_ADD (low32 (sv_denot E5 (SExt true 32 (SOff 32 0))))
                                       (low32 (sv_denot E5 (SLit (-1))))));
        rewrite (ofn_sext E5 32 B3 ltac:(rewrite E5lo by lia; exact E4x)); reflexivity).
ofn_reg HS (Z_to_bv 5 2) (YK11.getr regs3 (Z_to_bv 5 2)) X2
  ltac:(cbn [sv_denot]; rewrite E5lo by lia; rewrite (EE4 2%nat (Z_to_bv 5 2) eq_refl), Z.add_0_r,
        Z_to_bv_bv_unsigned; reflexivity).
ofn_reg HS (Z_to_bv 5 3) (YK11.getr regs3 (Z_to_bv 5 3)) X3
  ltac:(cbn [sv_denot]; rewrite E5lo by lia; rewrite (EE4 3%nat (Z_to_bv 5 3) eq_refl), Z.add_0_r,
        Z_to_bv_bv_unsigned; reflexivity).
ofn_reg HS (Z_to_bv 5 4) (YK11.getr regs3 (Z_to_bv 5 4)) X4
  ltac:(cbn [sv_denot]; rewrite E5lo by lia; rewrite (EE4 4%nat (Z_to_bv 5 4) eq_refl), Z.add_0_r,
        Z_to_bv_bv_unsigned; reflexivity).
ofn_reg HS (Z_to_bv 5 8) (YK11.getr regs3 (Z_to_bv 5 8)) X8
  ltac:(cbn [sv_denot]; rewrite E5lo by lia; rewrite (EE4 8%nat (Z_to_bv 5 8) eq_refl), Z.add_0_r,
        Z_to_bv_bv_unsigned; reflexivity).
ofn_reg HS (Z_to_bv 5 9) (YK11.getr regs3 (Z_to_bv 5 9)) X9
  ltac:(cbn [sv_denot]; rewrite E5lo by lia; rewrite (EE4 9%nat (Z_to_bv 5 9) eq_refl), Z.add_0_r,
        Z_to_bv_bv_unsigned; reflexivity).
ofn_reg HS (Z_to_bv 5 18) (YK11.getr regs3 (Z_to_bv 5 18)) X18
  ltac:(cbn [sv_denot]; rewrite E5lo by lia; rewrite (EE4 18%nat (Z_to_bv 5 18) eq_refl), Z.add_0_r,
        Z_to_bv_bv_unsigned; reflexivity).
ofn_reg HS (Z_to_bv 5 19) (YK11.getr regs3 (Z_to_bv 5 19)) X19
  ltac:(cbn [sv_denot]; rewrite E5lo by lia; rewrite (EE4 19%nat (Z_to_bv 5 19) eq_refl), Z.add_0_r,
        Z_to_bv_bv_unsigned; reflexivity).
ofn_reg HS (Z_to_bv 5 20) (YK11.getr regs3 (Z_to_bv 5 20)) X20
  ltac:(cbn [sv_denot]; rewrite E5lo by lia; rewrite (EE4 20%nat (Z_to_bv 5 20) eq_refl), Z.add_0_r,
        Z_to_bv_bv_unsigned; reflexivity).
ofn_reg HS (Z_to_bv 5 23) (YK11.getr regs3 (Z_to_bv 5 23)) X23
  ltac:(cbn [sv_denot]; rewrite E5lo by lia; rewrite (EE4 23%nat (Z_to_bv 5 23) eq_refl), Z.add_0_r,
        Z_to_bv_bv_unsigned; reflexivity).
ofn_reg HS (Z_to_bv 5 24) (YK11.getr regs3 (Z_to_bv 5 24)) X24
  ltac:(cbn [sv_denot]; rewrite E5lo by lia; rewrite (EE4 24%nat (Z_to_bv 5 24) eq_refl), Z.add_0_r,
        Z_to_bv_bv_unsigned; reflexivity).
ofn_reg HS (Z_to_bv 5 25) (YK11.getr regs3 (Z_to_bv 5 25)) X25
  ltac:(cbn [sv_denot]; rewrite E5lo by lia; rewrite (EE4 25%nat (Z_to_bv 5 25) eq_refl), Z.add_0_r,
        Z_to_bv_bv_unsigned; reflexivity).
ofn_reg HS (Z_to_bv 5 26) (w64 (OFN_SH + 2)) X26 ltac:(reflexivity).
assert (CUR5 : onann_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw b pos F ly3 S3 W3
  (ms_mem ms3) md6 0).
{ apply (ofn_cur_move STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw b pos F ly3 S3 W3 mem3 md4
    (ms_mem ms3) md6 0 CUR4); [rewrite ?Z.add_0_r; exact HJ4 | exact KD5 | exact GR5]. }
assert (TW5 : tw_at TMAP_A (aview segs (w_H W3) (ms_mem ms3)) B3)
  by (apply (tw_kept TMAP_A (aview segs (w_H W3) mem3)); [exact Htw4 | intros x _; exact (KD5 x)]).
assert (SLA5 : onann_slots_arm W3 (ms_mem ms3) sp1).
{ unfold onann_slots_arm.
  refine (conj _ (conj _ (conj _ _))); apply (ofn_slot_move W3 mem3 (ms_mem ms3) sp1 _ _ KD5).
  - exact (SL4 8 _ ltac:(lia) S8).
  - exact (SL4 16 _ ltac:(lia) S16).
  - exact (SL4 24 _ ltac:(lia) S24).
  - exact (SL4 48 _ ltac:(lia) S48). }
(* ---------------- +0x658: `bltu a1, a0` ---------------- *)
pmkst HS.
set (m4 := ms_mem ms3) in *.
clear HS SHOK4.
pose proof (ofn_entryb W3 (ms_regs ms3) m4) as HS.
set (Eb := Eimg (PI := PI_transport) (Ereg (ms_regs ms3) [])) in HS.
assert (SHOKb : sh_ok segs OFN_Bx (@nil shent) Eb (mrestrict (w_H W3) m4)) by constructor.
assert (HEIb : img_env VAL A_LIM Eb) by (unfold Eb; apply Eimg_env).
assert (EEb : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew Eb n = YK11.getr (ms_regs ms3) r)
  by (intros n r Hn; unfold Eb; apply ew_Eimg_Ereg_nat; exact Hn).
assert (D10 : sv_denot Eb (SOff 10 0) =
  sext 64 (alu32 ALU_ADD (low32 (Z_to_bv 64 (TW.S_state B3))) (low32 (Z_to_bv 64 (-1)))))
  by (cbn [sv_denot]; rewrite (EEb 10%nat (Z_to_bv 5 10) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact X10).
assert (D11 : sv_denot Eb (SOff 11 0) = Z_to_bv 64 1)
  by (cbn [sv_denot]; rewrite (EEb 11%nat (Z_to_bv 5 11) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact X11).
lazymatch goal with |- SRr _ ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + OFN_BR)) mm rom) mdx) Q) end.
psrr_branch_tok RUN BR HS SHOKb OFN_B0.
- (* taken: neither S_WAKING nor S_ONLINE, to the release cut +0x73c *)
  cbn [branch_taken] in Hc. rewrite D10, D11 in Hc.
  rewrite (ofn_ltu1 _ Hst3) in Hc. apply negb_true_iff, orb_false_iff in Hc.
  destruct Hc as (Hc1 & Hc2). apply Z.eqb_neq in Hc1. apply Z.eqb_neq in Hc2.
  assert (EBW : Bw' = B3).
  { assert (Hne1 : TW.S_state B3 <> TS0.DIGINET_S_WAKING) by (unfold TS0.DIGINET_S_WAKING; exact Hc1).
    assert (Hne2 : TW.S_state B3 <> TS0.DIGINET_S_ONLINE) by (unfold TS0.DIGINET_S_ONLINE; exact Hc2).
    unfold onann_k_fs in Hkfn.
    rewrite (proj2 (Z.eqb_neq _ _) Hne2), (proj2 (Z.eqb_neq _ _) Hne1) in Hkfn.
    cbn [orb] in Hkfn. exact (onann_some_inv _ _ (eq_sym Hkfn)). }
  paj_run_to_tok RUNTO HS HJ4 SHOKb OFN_B0 ONANN_FNREL.
  { lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fpx ?b0 ?bc ?lyq ?ownq =>
      let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fpx b0 bc lyq ownq) end.
    apply awr_ok_x_nil. }
  lazymatch type of HS with
  | st_ok_pi _ _ _ _ (restrict _ ?mf) => rename mf into msF
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok _ _ _ (restrict _ ?mf) =>
      rename mf into msF
  end.
  assert (KD : forall a, aview segs (w_H W3) (ms_mem msF) a = aview segs (w_H W3) m4 a).
  { unfold m4. intros a. rewrite (aview_wrap64 segs _ (ms_mem msF) a), (aview_wrap64 segs _ (ms_mem ms3) a).
    pose proof (Z.mod_pos_bound a (2 ^ 64) ltac:(lia)) as Ha.
    apply (kept_of_frame _ _ _ _ _ (fun _ => False) HFr); [| lia | intros []].
    intros b0 wlo whi x Hiw Hx. cbv beta. ofn_win Hiw Hx ltac:(lia). }
  assert (GR : forall a, apresent (w_H W3) m4 a -> apresent (w_H W3) (ms_mem msF) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
  ofn_kregb HS EEb (Z_to_bv 5 2) 2%nat X2 Y2. ofn_kregb HS EEb (Z_to_bv 5 3) 3%nat X3 Y3.
  ofn_kregb HS EEb (Z_to_bv 5 4) 4%nat X4 Y4. ofn_kregb HS EEb (Z_to_bv 5 8) 8%nat X8 Y8.
  ofn_kregb HS EEb (Z_to_bv 5 9) 9%nat X9 Y9. ofn_kregb HS EEb (Z_to_bv 5 18) 18%nat X18 Y18.
  ofn_kregb HS EEb (Z_to_bv 5 19) 19%nat X19 Y19. ofn_kregb HS EEb (Z_to_bv 5 23) 23%nat X23 Y23.
  pmkst HS.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + ONANN_FNREL)) mm rom) mdx) Q) end.
  apply (FNREL LAWS0 CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw'
    pos sp1 F ly3 S3 W3 (ms_mem msF) _ 0 (ms_regs msF) HFIX).
  + unfold onann_rel_cur. split.
    * apply (ofn_cur_move STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw b pos F ly3 S3 W3 m4 md6
        (ms_mem msF) _ 0 CUR5); [rewrite ?Z.add_0_r; exact HJ4 | exact KD | exact GR].
    * split.
      -- rewrite EBW. apply (tw_kept TMAP_A (aview segs (w_H W3) m4)); [exact TW5 | intros x _; exact (KD x)].
      -- rewrite EBW. exact EGF3.
  + unfold onann_regs_rel, onann_regs_base. repeat split.
    * exact (eq_trans Y2 R3_2).
    * exact (eq_trans Y3 R3_3).
    * exact (eq_trans Y4 R3_4).
    * exact (eq_trans Y8 R3_8).
    * exact (eq_trans Y9 R3_9).
    * exact (eq_trans Y18 R3_18).
    * exact (eq_trans Y19 R3_19).
    * exact (eq_trans Y23 R3_23).
- (* not taken: S_WAKING or S_ONLINE, to the second inlined session_lost +0x65c *)
  cbn [branch_taken] in Hc. rewrite D10, D11 in Hc.
  rewrite (ofn_ltu1 _ Hst3) in Hc. apply negb_false_iff, orb_true_iff in Hc.
  assert (HOR : TW.S_state B3 = TS0.DIGINET_S_ONLINE \/ TW.S_state B3 = TS0.DIGINET_S_WAKING).
  { destruct Hc as [Hc | Hc]; apply Z.eqb_eq in Hc; [right | left]; exact Hc. }
  assert (HSL : TSS.session_lost_m timg_A TF B3 TS0.DIGINET_R_FOREIGN = Some (Bw', tt)).
  { unfold onann_k_fs in Hkfn.
    destruct HOR as [Hon | Hwk].
    - rewrite (proj2 (Z.eqb_eq _ _) Hon) in Hkfn. cbn [orb] in Hkfn. exact Hkfn.
    - rewrite (proj2 (Z.eqb_eq _ _) Hwk) in Hkfn. rewrite orb_comm in Hkfn. cbn [orb] in Hkfn. exact Hkfn. }
  paj_run_to_tok RUNTO HS HJ4 SHOKb OFN_B0 ONANN_SL2.
  { lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fpx ?b0 ?bc ?lyq ?ownq =>
      let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fpx b0 bc lyq ownq) end.
    apply awr_ok_x_nil. }
  lazymatch type of HS with
  | st_ok_pi _ _ _ _ (restrict _ ?mf) => rename mf into msF
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok _ _ _ (restrict _ ?mf) =>
      rename mf into msF
  end.
  assert (KD : forall a, aview segs (w_H W3) (ms_mem msF) a = aview segs (w_H W3) m4 a).
  { unfold m4. intros a. rewrite (aview_wrap64 segs _ (ms_mem msF) a), (aview_wrap64 segs _ (ms_mem ms3) a).
    pose proof (Z.mod_pos_bound a (2 ^ 64) ltac:(lia)) as Ha.
    apply (kept_of_frame _ _ _ _ _ (fun _ => False) HFr); [| lia | intros []].
    intros b0 wlo whi x Hiw Hx. cbv beta. ofn_win Hiw Hx ltac:(lia). }
  assert (GR : forall a, apresent (w_H W3) m4 a -> apresent (w_H W3) (ms_mem msF) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
  ofn_kregb HS EEb (Z_to_bv 5 2) 2%nat X2 Y2. ofn_kregb HS EEb (Z_to_bv 5 3) 3%nat X3 Y3.
  ofn_kregb HS EEb (Z_to_bv 5 4) 4%nat X4 Y4. ofn_kregb HS EEb (Z_to_bv 5 8) 8%nat X8 Y8.
  ofn_kregb HS EEb (Z_to_bv 5 9) 9%nat X9 Y9. ofn_kregb HS EEb (Z_to_bv 5 18) 18%nat X18 Y18.
  ofn_kregb HS EEb (Z_to_bv 5 19) 19%nat X19 Y19. ofn_kregb HS EEb (Z_to_bv 5 20) 20%nat X20 Y20.
  ofn_kregb HS EEb (Z_to_bv 5 23) 23%nat X23 Y23. ofn_kregb HS EEb (Z_to_bv 5 24) 24%nat X24 Y24.
  ofn_kregb HS EEb (Z_to_bv 5 25) 25%nat X25 Y25. ofn_kregb HS EEb (Z_to_bv 5 26) 26%nat X26 Y26.
  ofn_kregb HS EEb (Z_to_bv 5 21) 21%nat X21 Y21.
  pmkst HS.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + ONANN_SL2)) mm rom) mdx) Q) end.
  apply (SL2 LAWS0 CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw'
    pos sp1 F B2 B3 ly3 S3 W3 (ms_mem msF) _ (ms_regs msF) HFIX).
  + unfold onann_sl2_cur.
    refine (conj _ (conj _ (conj Hb2 (conj ECN (conj _ (conj HOR (conj HSL (conj EGF3 _))))))))%type.
    * apply (ofn_cur_move STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw b pos F ly3 S3 W3 m4 md6
        (ms_mem msF) _ 0 CUR5); [rewrite ?Z.add_0_r; exact HJ4 | exact KD | exact GR].
    * apply (tw_kept TMAP_A (aview segs (w_H W3) m4)); [exact TW5 | intros x _; exact (KD x)].
    * exists d3. exact EB3.
    * unfold onann_slots_arm in SLA5 |- *.
      destruct SLA5 as (A8 & A16 & A24 & A48).
      refine (conj _ (conj _ (conj _ _))); apply (ofn_slot_move W3 m4 (ms_mem msF) sp1 _ _ KD);
        [exact A8 | exact A16 | exact A24 | exact A48].
  + unfold onann_regs_sl2, onann_regs_sl1, onann_regs_arm, onann_regs_base. repeat split.
    * exact (eq_trans Y2 R3_2).
    * exact (eq_trans Y3 R3_3).
    * exact (eq_trans Y4 R3_4).
    * exact (eq_trans Y8 R3_8).
    * exact (eq_trans Y9 R3_9).
    * exact (eq_trans Y18 R3_18).
    * exact (eq_trans Y19 R3_19).
    * exact (eq_trans Y20 R3_20).
    * exact (eq_trans Y24 R3_24).
    * exact (eq_trans Y25 R3_25).
    * exact Y26.
    * exact (eq_trans Y23 R3_23).
    * exact Y21.
Qed.

End fn.

(* The foreign-notice piece of the walk of on_announce (OnannCut.v onann_fn_stmt), at every machine, run ceiling,
   record and meter. *)
Theorem onann_piece_fn : forall fx rc B MT, @onann_fn_stmt fx rc B MT.
Proof. intros fx rc B MT. exact (@onann_piece_fn_holds fx rc B MT). Qed.
