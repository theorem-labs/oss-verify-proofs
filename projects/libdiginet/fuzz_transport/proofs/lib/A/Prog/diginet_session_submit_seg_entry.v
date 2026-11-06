(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8v.v:120-122
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:518-584, 622-634 [Apache-2.0 OR MIT];
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:110-141, 221-225, 227-235, 264-270 [Apache-2.0 OR MIT], for
   libreac/fuzz_identity's ASan build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_L.v, with its module paths and module names changed; 987 of its 1030 lines of code are new or changed and 1037 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/m_rx_seg_head.v, with its module names changed; 659 of its 732 lines of code are new or changed and 957 lines of the source are left out. *)
(* diginet_session_submit_seg_entry: Lemma ssw_seg_entry, diginet_session_submit (fuzz_transport.asan 0x89ef0) from
   its entry to the return, given the cuts APP and LOOP of lib/A/Prog/diginet_session_submit_segs.v
   (lib/A/Prog/diginet_session_submit_seg_app.v, lib/A/Prog/diginet_session_submit_seg_loop.v).

   What the code does (offsets from the entry; lib/A/Prog/diginet_session_submit_cg.v lists it word by word):
     +0x0 .. +0x54    the frame and the five saves, s1 = s, a0 = -1, the two null tests (decided: s = g_s, c <> 0),
                      s0 = c, s3 = the shadow base (through its GOT word), the check of the 1-byte load at c + 24,
                      a1 = len, `bltu len - 25, -24`;
     len outside [1, 24]: to the epilogue with a0 = -1 and the return (the model's E_ARG);
     +0x5c .. +0x6c   s2 = s + 18144, a0 = c, the call of diginet_body_check (return address +0x70);
     +0x70            `beqz a0`: a result not 0 bumps g_s.stats.refused and returns -10 (E_REFUSED);
     +0x9c .. +0xc8   the check of the 4-byte load at c + 28, a4 = key, the kind byte 0 or 8: to the append (APP);
     +0x134 .. +0x140 the kind 9: to the append;
     +0x144 .. +0x154 the check of the 4-byte load at s2, a3 = queued, 0: to the append;
     +0x158 .. +0x160 a0 = &s->queue[0], a1 = a0 + 28, a4 = key sign-extended: the search's head (LOOP) at j = 0.

   The symbolic state at the entry: the registers as atoms 0 .. 31, atom 32 the shadow base, atom 33 len, atom 34 the
   key, atom 35 queued, atom 36 coalesced, atom 37 refused (the world's values). Regions: the 48-byte frame below sp
   (written by the saves), the shadow base's GOT word and its cell, the command's bytes [c + 24, c + 32) (read-only)
   and queued (read-only); on the refused path, after the call, g_s.stats.refused (writable). Shadow entries: the
   command's 32 bytes and g_s's 18264.

   The call of diginet_body_check is lifted by TransportGCg.v gx_call_cg (a donor-form callee): after it the world
   is W2, the frame's bytes are kept by its acall_kept (above alloc_ceiling, outside its window), the command's by
   ssw_src_acall, g_s's by its gx_kept; the state after it re-enters the engine by YC1h.v jafter_call_keep_hi. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportSyms DgnTransportList DgnTransportAddr DgnTransportPa DgnTransportImg DgnTransportPaLib YC4b YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportCg TransportGCg TransportGRwA TransportGRunA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import m_lost_cg diginet_session_submit_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require diginet_body_check_cg diginet_session_submit_seg_kit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
diginet_session_submit_segs diginet_session_submit_seg_app.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TSess0 TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnLib.
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
Module PBC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.diginet_body_check_cg.
Module SSK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.diginet_session_submit_seg_kit.
Module DL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnLib.

(* ------------------------------------------------------------------ *)
(* The symbolic state at the entry                                     *)
(* ------------------------------------------------------------------ *)

Definition ent_c : YP09.region :=
  YP09.mkRegion (Some 11%nat) 24 32 0 0 [YP09.mkChunk 24 (CVal 1 (SOff 33 0)); YP09.mkChunk 28 (CVal 4 (SOff 34 0))].
Definition ent_gq : YP09.region := YP09.mkRegion (Some 10%nat) 18144 18148 0 0 [YP09.mkChunk 18144 (CVal 4 (SOff 35 0))].
(* g_s.stats.refused (s + 18256), writable, added on the refused path after the call. *)
Definition ent_gref : YP09.region :=
  YP09.mkRegion (Some 10%nat) 18256 18264 18256 18264 [YP09.mkChunk 18256 (CVal 8 (SOff 37 0))].
Definition ent_regions : smem := [stack_region SSUBMIT_FRAME; got_regionP; bcell_regionP 32; ent_c; ent_gq].
Definition ent_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF TA_g_s TA_g_s 6); (11%nat, mkAF 4096 (2 ^ 47 - 32) 2);
           (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (33%nat, mkAF 0 255 0); (34%nat, mkAF 0 (2 ^ 32 - 1) 0);
           (35%nat, mkAF 0 (2 ^ 32 - 1) 0)] [] [].
Definition ent_ss : sstate := mkSS AF_diginet_session_submit sr_atoms ent_regions None ent_facts.
Definition ENT_SH : list shent := [mkSHE 11 0 32; mkSHE 10 0 18264].

(* diginet_body_check answers 0 or -10 (DgnLib.v body_check). *)
Lemma ssw_bc_cases : forall b, DL.body_check b = 0 \/ DL.body_check b = -10.
Proof. intros b. unfold DL.body_check. destruct (DL.bc_loop _ _ _ _); [right; reflexivity|]. destruct (DgnSpec.system_at b); [right | left]; reflexivity. Qed.

Section ent. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation G := TG.G_HARNESS.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

Definition ent_extra (c : ssw_ctx) : list word :=
  [w64 SHADOW_OFF; w64 (ssw_len c); w64 (ssw_key c); w64 (ssw_q c); w64 (TW.S_stats_coalesced (cx_Bw c));
   w64 (TW.S_stats_refused (cx_Bw c))].
Definition ent_E (c : ssw_ctx) : env := Eimg (PI := PI_transport) (Ereg (cx_regs c) (ent_extra c)).

Lemma ent_vals : VAL (A_OBJ 1) = FCells.GOT_CELL_K /\ VAL (A_OBJ 93) = FCells.CELL_K /\
  BASE + AF_diginet_session_submit = transport_sigma TS_diginet_session_submit /\ BASE = 0x81264.
Proof. vm_compute. repeat split. Qed.

(* The two image regions hold what transport_cells says they hold, at any AR state
   (diginet_session_config_default.v scfg_img_ok). *)
Lemma ssw_img_ok : forall ly S (W : world segs) mem md (E : env),
  transport_cells B -> @AR rc segs B ly S W mem md ->
  ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1)) -> ew E (A_OBJ 93) = Z_to_bv 64 (VAL (A_OBJ 93)) ->
  ew E 32 = Z_to_bv 64 SHADOW_OFF ->
  region_ok segs E (mrestrict (w_H W) mem) got_regionP /\ region_ok segs E (mrestrict (w_H W) mem) (bcell_regionP 32).
Proof.
  intros ly S W mem md E HCELLS HAR E1 E93 E32.
  destruct (HCELLS ly) as (I1 & I2 & _).
  destruct ent_vals as (V1 & V93 & _).
  assert (CH : forall c, In c (as_const B ly) -> cell_holds B ly (aview segs (w_H W) mem) c).
  { intros c Hc. destruct HAR as (Mx & _). exact (proj1 (Forall_forall _ _) (am_const _ _ _ _ Mx) c Hc). }
  assert (Kcell : rdword (aview segs (w_H W) mem) FCells.CELL_K = Some FCells.ASAN_K)
    by (apply (rdword_cell B ly); [unfold FCells.ASAN_K; lia | exact (CH _ I1)]).
  assert (Kgot : rdword (aview segs (w_H W) mem) FCells.GOT_CELL_K = Some FCells.CELL_K)
    by (apply (rdword_cell B ly); [unfold FCells.CELL_K; lia | exact (CH _ I2)]).
  assert (VB : forall n v0, ew E n = Z_to_bv 64 v0 -> 0 <= v0 < 2 ^ 64 -> base_val E (Some n) = v0)
    by (intros n v0 Hn Hv0; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hv0).
  assert (R1 : 0 <= VAL (A_OBJ 1) < 2 ^ 47) by (rewrite V1; unfold FCells.GOT_CELL_K; lia).
  assert (R93 : 0 <= VAL (A_OBJ 93) < 2 ^ 47) by (rewrite V93; unfold FCells.CELL_K; lia).
  unfold got_regionP, bcell_regionP, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  split.
  - rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E1) by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
    apply (chunk_ok_val segs E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 93) 0) (VAL (A_OBJ 93)));
    [cbn [sv_denot]; rewrite E93, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    rewrite Z.add_0_r, V1, V93. exact (val_mem_of_rdword segs (w_H W) mem _ _ Kgot).
  - rewrite (VB (A_OBJ 93) (VAL (A_OBJ 93)) E93) by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
    apply (chunk_ok_val segs E _ (VAL (A_OBJ 93)) 0 8 (SOff 32 0) SHADOW_OFF);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SHADOW_OFF; zside | zside |].
    rewrite Z.add_0_r, V93. exact (val_mem_of_rdword segs (w_H W) mem _ _ Kcell).
Qed.

(* The command's 32 bytes lie outside the image (a heap block, a side-stack frame, the machine stack). *)
Lemma ssw_cp_off_img : forall c, ssw_rt B MT -> ssw_ok B c -> off_img (cx_cp c) 32.
Proof.
  intros c HRT HOK.
  pose proof HRT as (_ & _ & LAWS & _).
  pose proof (ssw_ok_stack B c HOK) as (HAR & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct HOK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSRC & _ & _ & HNG & _).
  unfold SSUBMIT_CMD_LEN in *. unfold off_img.
  destruct HSRC as [(bA & nA & Hin & B1 & B2) | (HL & _)].
  - pose proof (blk_off_imgP (PI := PI_transport) B _ _ _ _ _ bA nA HAR Hin) as Ho. unfold off_img in Ho.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ bA nA HAR Hin) as (_ & _ & _ & _ & _ & _ & Hn0).
    pose proof (req_size_pos nA (proj1 Hn0)) as [_ Hreq]. lia.
  - destruct HL as [(cid & pos & Hin & F1 & F2) | [(HG & _) | [(S1 & S3) | (HR & _)]]].
    + pose proof (frm_off_imgP (PI := PI_transport) B _ _ _ _ _ cid pos HAR Hin) as Ho.
      rewrite IMG_LO_val, IMG_TOP_val in Ho. lia.
    + exfalso. exact (proj1 (HNG (cx_cp c) ltac:(lia)) (HG (cx_cp c) ltac:(lia))).
    + destruct (trans_stk_bounds B _ _ _ _ _ HAR) as [T1 T2]. right. lia.
    + exfalso. exact (proj2 (HNG (cx_cp c) ltac:(lia)) (HR (cx_cp c) ltac:(lia))).
Qed.

(* The entry's shadow entries: the command's 32 bytes and g_s's 18264, at any AR state where the command is
   readable. *)
Lemma ent_shok : forall c ly S (W : world segs) mem md (E : env),
  trans_ssubmit_cells B -> @AR rc segs B ly S W mem md -> decode_rd_ok W mem (cx_cp c) 32 ->
  4096 <= cx_cp c -> cx_cp c + 32 <= 2 ^ 47 ->
  ew E 10 = w64 TA_g_s -> ew E 11 = w64 (cx_cp c) -> ew E 32 = w64 SHADOW_OFF ->
  sh_ok segs SSW_Bx ENT_SH E (mrestrict (w_H W) mem).
Proof.
  intros c ly S W mem md E HSC HAR HRD Hc0 Hc47 E10 E11 E32.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (EC : TA_g_s = 6158784) by reflexivity.
  assert (U10 : bv_unsigned (ew E 10) = TA_g_s) by (rewrite E10; apply unsigned_lit_small; rewrite EC; lia).
  assert (U11 : bv_unsigned (ew E 11) = cx_cp c) by (rewrite E11; apply unsigned_lit_small; lia).
  pose proof HRD as (_ & Hra_c & _ & Hamr_c & _).
  unfold sh_ok, ENT_SH. constructor; [|constructor; [|constructor]].
  - apply (shent_ok_of_range segs (w_H W) mem E SSW_Bx 11 (cx_cp c) 32 (cx_cp c) 0 32 Hra_c).
    + unfold U, SSW_Bx. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned.
      rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia). reflexivity.
    + unfold U. cbn [sv_denot]. rewrite U11, Z.add_0_r. apply unsigned_lit_small. lia.
    + lia.
    + lia.
    + intros x Hx. cbn [Z.min Z.max] in Hx. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *.
      unfold SHADOW_OFF. lia.
  - apply (shent_ok_of_range segs (w_H W) mem E SSW_Bx 10 TA_g_s 18264 TA_g_s 0 18264
      (ssw_gs_ra B _ _ _ _ _ HSC HAR)).
    + unfold U, SSW_Bx. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned.
      rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia). reflexivity.
    + unfold U. cbn [sv_denot]. rewrite U10, Z.add_0_r. apply unsigned_lit_small. rewrite EC; lia.
    + lia.
    + lia.
    + intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF. rewrite EC in *. lia.
Qed.

(* The five words the prologue saved, read from the frame region of a state (atom 2 the entry sp). *)
Lemma ssw_saved_of_frame : forall c (E : env) (WX : world segs) m wlo whi,
  region_ok segs E (mrestrict (w_H WX) m) (YP09.mkRegion (Some 2%nat) (-48) 0 wlo whi
    [YP09.mkChunk (-40) (CVal 8 (SOff 19 0)); YP09.mkChunk (-32) (CVal 8 (SOff 18 0));
     YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0));
     YP09.mkChunk (-8) (CVal 8 (SOff 1 0))]) ->
  bv_unsigned (ew E 2) = ssw_SP c ->
  (forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr (cx_regs c) r) ->
  ssw_saved c WX m.
Proof.
  intros c E WX m wlo whi HR HU HE.
  assert (F : forall (a : nat) (r : bv 5) off, (a < 32)%nat -> Z.of_nat a = bv_unsigned r ->
    In (YP09.mkChunk off (CVal 8 (SOff a 0)))
      [YP09.mkChunk (-40) (CVal 8 (SOff 19 0)); YP09.mkChunk (-32) (CVal 8 (SOff 18 0));
       YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0));
       YP09.mkChunk (-8) (CVal 8 (SOff 1 0))] ->
    val_mem segs (mrestrict (w_H WX) m) (ssw_SP c + off) 8 (bv_unsigned (YK11.getr (cx_regs c) r))).
  { intros a r off Ha Hr Hin.
    pose proof (field_of_region_any E _ 2%nat (ssw_SP c) _ _ _ _ _ off 8 (SOff a 0) HR HU Hin ltac:(lia)) as V.
    rewrite (ssw_soff0 E a (YK11.getr (cx_regs c) r) (HE a r Ha Hr)) in V.
    rewrite Z.mod_small in V; [exact V|]. pose proof (bv_unsigned_in_range _ (YK11.getr (cx_regs c) r)) as R.
    unfold bv_modulus in R. change (2 ^ (8 * Z.of_N 8)) with (2 ^ Z.of_N 64). exact R. }
  unfold ssw_saved.
  replace (ssw_SP c - 40) with (ssw_SP c + -40) by lia. replace (ssw_SP c - 32) with (ssw_SP c + -32) by lia.
  replace (ssw_SP c - 24) with (ssw_SP c + -24) by lia. replace (ssw_SP c - 16) with (ssw_SP c + -16) by lia.
  replace (ssw_SP c - 8) with (ssw_SP c + -8) by lia.
  split; [apply (F 19%nat 19%bv); [lia | reflexivity | cbn; tauto]|].
  split; [apply (F 18%nat 18%bv); [lia | reflexivity | cbn; tauto]|].
  split; [apply (F 9%nat 9%bv); [lia | reflexivity | cbn; tauto]|].
  split; [apply (F 8%nat 8%bv); [lia | reflexivity | cbn; tauto]|].
  apply (F 1%nat 1%bv); [lia | reflexivity | cbn; tauto].
Qed.

(* The entry state, and its shadow entries. *)
Lemma ent_entry : forall c, ssw_rt B MT -> ssw_ok B c ->
  st_ok_pi segs VAL (ent_E c) ent_ss
    (restrict (w_H (cx_W c)) (@YK11.mkst fx (cx_regs c) (Z_to_bv 64 (BASE + AF_diginet_session_submit)) (cx_memc c)
      (YK11.seg_rom segs))) /\
  sh_ok segs SSW_Bx ENT_SH (ent_E c) (mrestrict (w_H (cx_W c)) (cx_memc c)).
Proof.
  intros c HRT HOK.
  pose proof HRT as (HCELLS & HSC & LAWS & _).
  pose proof (ssw_ok_stack B c HOK) as (HAR & Hsp & Hce & Hwin).
  pose proof (ssw_ok_cp B MT c HRT HOK) as (Hc0 & Hc47 & Hcoff & HRD).
  pose proof (ssw_cp_off_img c HRT HOK) as Hoff. unfold off_img in Hoff.
  pose proof (ssw_ok_sp B c HOK) as (Hsp16 & _ & _ & _ & _ & ESS).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (Hcp4 : cx_cp c mod 4 = 0)
    by (destruct HOK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H4 & _); exact H4).
  assert (H10 : YK11.getr (cx_regs c) 10 = w64 SSUBMIT_S)
    by (destruct HOK as (_ & _ & _ & _ & _ & H10 & _); exact H10).
  assert (H11 : YK11.getr (cx_regs c) 11 = w64 (cx_cp c))
    by (destruct HOK as (_ & _ & _ & _ & _ & _ & H11 & _); exact H11).
  assert (Htw : tw_at TMAP_A (aview segs (w_H (cx_W c)) (cx_memc c)) (cx_Bw c))
    by (destruct HOK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Htw & _); exact Htw).
  assert (HC8 : garr8 segs (mrestrict (w_H (cx_W c)) (cx_memc c)) (cx_cp c) (TW.zs (cx_C c)))
    by (destruct HOK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HC8 & _); exact HC8).
  assert (HL0 : length (cx_C c) = 32%nat)
    by (destruct HOK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HL0 & _); exact HL0).
  assert (HNG : forall x, cx_cp c <= x < cx_cp c + 32 -> ~ inG G x)
    by (intros x Hx; destruct HOK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HNG & _);
        exact (proj1 (HNG x ltac:(unfold SSUBMIT_CMD_LEN; lia)))).
  set (E := ent_E c).
  assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr (cx_regs c) r)
    by (intros n r Hn; unfold E, ent_E; apply ew_Eimg_Ereg_nat; exact Hn).
  assert (EX : forall i, (i < 6)%nat -> ew E (32 + i) = nth i (ent_extra c) (Z_to_bv 64 0))
    by (intros i Hi; unfold E, ent_E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
  pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
  pose proof (EX 2%nat ltac:(lia)) as E34. pose proof (EX 3%nat ltac:(lia)) as E35.
  cbn [Nat.add nth ent_extra] in E32, E33, E34, E35.
  assert (EOB : forall j, (j < 95)%nat -> ew E (A_OBJ j) = Z_to_bv 64 (VAL (A_OBJ j)))
    by (intros j Hj; unfold E, ent_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  destruct (ssw_img_ok _ _ _ _ _ E HCELLS HAR (EOB 1%nat ltac:(lia)) (EOB 93%nat ltac:(lia)) E32) as [RG RC].
  destruct ent_vals as (V1 & V93 & _).
  assert (EC : TA_g_s = 6158784) by reflexivity.
  assert (Usp : bv_unsigned (ew E 2) = ssw_SP c) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
  assert (U10 : bv_unsigned (ew E 10) = TA_g_s)
    by (rewrite (EE 10%nat 10%bv eq_refl), H10; apply unsigned_lit_small; unfold SSUBMIT_S; lia).
  assert (U11 : bv_unsigned (ew E 11) = cx_cp c)
    by (rewrite (EE 11%nat 11%bv eq_refl), H11; apply unsigned_lit_small; lia).
  assert (Rlen : 0 <= ssw_len c < 256) by (unfold ssw_len, TS0.cmd_len_of; exact (SSK.ssk_u1 _ _)).
  assert (Rkey : 0 <= ssw_key c < 2 ^ 32) by (unfold ssw_key, TS0.cmd_key_of; exact (TWL.u_at_range _ _ 4)).
  assert (Rq : 0 <= ssw_q c < 2 ^ 32) by (unfold ssw_q; exact (TWL.u_at_range _ _ 4)).
  assert (VB : forall n v0, ew E n = Z_to_bv 64 v0 -> 0 <= v0 < 2 ^ 64 -> base_val E (Some n) = v0)
    by (intros n v0 Hn Hv0; cbn [base_val]; rewrite Hn; apply unsigned_lit_small; exact Hv0).
  split.
  - rewrite restrict_mkst_fx. unfold ent_ss, ent_regions.
    apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
    + apply regs_ok_Eimg_Ereg.
    + vm_compute. reflexivity.
    + apply Forall_cons; [|apply Forall_cons; [exact RG | apply Forall_cons; [exact RC |]]].
      * unfold stack_region, region_ok.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite Usp. unfold SSUBMIT_FRAME in *.
        split; [lia|]. split; [lia|]. split; [|constructor].
        intros o Ho. apply (apresent_writable segs). apply Hwin. lia.
      * apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
        -- unfold ent_c, region_ok.
           cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
           rewrite U11. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
           apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
           ++ apply (chunk_ok_val segs E _ (cx_cp c) 24 1 (SOff 33 0) (ssw_len c));
                [apply ssw_soff0; exact E33 | change (2 ^ (8 * Z.of_N 1)) with 256; exact Rlen | lia |].
              exact (ssw_garr8_u _ _ (cx_C c) 24 1 HC8 ltac:(lia) ltac:(rewrite HL0; lia)).
           ++ apply (chunk_ok_val segs E _ (cx_cp c) 28 4 (SOff 34 0) (ssw_key c));
                [apply ssw_soff0; exact E34 | exact Rkey | lia |].
              exact (ssw_garr8_u _ _ (cx_C c) 28 4 HC8 ltac:(lia) ltac:(rewrite HL0; lia)).
        -- unfold ent_gq, region_ok.
           cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
           rewrite U10. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. apply Forall_cons; [|apply Forall_nil].
           apply (chunk_ok_val segs E _ TA_g_s 18144 4 (SOff 35 0) (ssw_q c)); [apply ssw_soff0; exact E35 | exact Rq | lia |].
           exact (tw_read_val segs _ TMAP_A (cx_Bw c) TW.OFF_g_s TA_g_s TW.SZ_g_s 18144 4 TMAP_A_ok Htw TMAP_A_g_s
             ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
    + apply pairwise_disjoint_of_extents.
      unfold stack_region, got_regionP, bcell_regionP, ent_c, ent_gq, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
      rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) (EOB 1%nat ltac:(lia))) by (rewrite V1; unfold FCells.GOT_CELL_K; lia).
      rewrite (VB (A_OBJ 93) (VAL (A_OBJ 93)) (EOB 93%nat ltac:(lia))) by (rewrite V93; unfold FCells.CELL_K; lia).
      cbn [base_val]. rewrite Usp, U10, U11.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      rewrite V1, V93. unfold FCells.GOT_CELL_K, FCells.CELL_K, SSUBMIT_FRAME in *.
      assert (HCG : cx_cp c + 32 <= TA_g_s + 18144 \/ TA_g_s + 18148 <= cx_cp c + 24).
      { destruct (Z_le_gt_dec (cx_cp c + 32) (TA_g_s + 18144)) as [H1|H1]; [left; exact H1|].
        destruct (Z_le_gt_dec (TA_g_s + 18148) (cx_cp c + 24)) as [H2|H2]; [right; exact H2|].
        exfalso. apply (HNG (Z.max (cx_cp c + 24) (TA_g_s + 18144))); [lia|].
        apply ssw_gs_inG. unfold TW.SZ_g_s. lia. }
      repeat split; first [exact I | lia].
    + unfold ent_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
      unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite Usp, U10, U11, (ssw_U E 32 SHADOW_OFF E32 ltac:(unfold SHADOW_OFF; lia)),
        (ssw_U E 33 (ssw_len c) E33 ltac:(lia)), (ssw_U E 34 (ssw_key c) E34 ltac:(lia)),
        (ssw_U E 35 (ssw_q c) E35 ltac:(lia)).
      change (2 ^ 4) with 16. change (2 ^ 2) with 4. change (2 ^ 6) with 64. rewrite !Z.pow_0_r, !Z.mod_1_r.
      repeat match goal with |- _ /\ _ => split end; try exact I; first [lia | rewrite EC; reflexivity].
  - pose proof HRD as (_ & Hra_c & _ & Hamr_c & _).
    apply (ent_shok c _ _ _ _ _ E HSC HAR HRD Hc0 Hc47); [rewrite (EE 10%nat 10%bv eq_refl), H10; reflexivity
      | rewrite (EE 11%nat 11%bv eq_refl), H11; reflexivity | exact E32].
Qed.

End ent.

(* After a run whose only writable region is the frame below the entry sp (atom 2 = sp): the model named, ssw_lite
   carried to the run's memory. *)
Ltac ssw_after_stk Bv MTv cv HRT HOK HL HEX U2 :=
  lazymatch goal with |- SRr _ _ (mkCfg _ (with_vm_backing (m_vm_lazy ?m0) ?mt ?m0)) _ =>
    let md := fresh "mdw" in set (md := with_vm_backing (m_vm_lazy m0) mt m0) in *; clearbody md; clear mt end;
  lazymatch goal with HFr : frame_of ?Ex ?rs (mrestrict (w_H ?Wx) ?m1) (mrestrict (w_H ?Wx) ?m2),
                      HG : mem_grows _ _, HF : frame_of _ _ _ _ |- _ =>
    let KR := fresh "KR" in
    assert (KR : forall a, 0 <= a < 2 ^ 64 -> ~ (ssw_SP cv - 48 <= a < ssw_SP cv) ->
      aview tfibsegs (w_H Wx) m2 a = aview tfibsegs (w_H Wx) m1 a)
      by (let a := fresh "a" in let Ha := fresh "Ha" in let Hn := fresh "Hn" in intros a Ha Hn;
          apply (kept_of_frame _ _ _ _ _ (fun x => ssw_SP cv - 48 <= x < ssw_SP cv) HFr);
          [ let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let x := fresh "x" in
            let Hin := fresh "Hin" in let Hx := fresh "Hx" in
            intros b wlo whi x Hin Hx;
            ssw_win Hin Hx ltac:(first [lia | rewrite ?HEX in Hx by lia; rewrite U2 in Hx; cbv beta; lia])
          | exact Ha | exact Hn ]);
    let HL' := fresh "HL" in
    pose proof (ssw_lite_step Bv MTv cv Wx m1 m2 _ HRT HOK HL KR (fun a Ha => apresent_grows _ _ _ a HG Ha)) as HL';
    clear HL HF HFr HG KR; rename HL' into HL
  end.

(* The write rights of a run from an entry-derived state: the frame below the entry sp (inside the caller's
   stack window), the other regions read-only. *)
Ltac ssw_awr_stk HEX U2 :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  apply awr_ok_x_cons;
  [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite ?HEX in Ha by lia; rewrite U2 in Ha;
    left; split; [unfold awr_byte; left; lia | lia] |];
  ssw_awr_ro.

(* The saved words of a state after the prologue, from its frame region (index 0); HEXA relates its valuation to
   the entry's E0, EE reads E0's registers, U2 is E0's sp. *)
Ltac ent_saved HS cv HEXA EE U2 HSV :=
  let RG0 := fresh "RG0" in
  first [pose proof (st_ok_pi_region_nth (PI := PI_transport) _ _ _ 0 _ HS eq_refl) as RG0
        | pose proof (YC4b.st_ok_region_nth _ _ _ 0 _ HS eq_refl) as RG0];
  cbn [ms_mem restrict] in RG0;
  pose proof (ssw_saved_of_frame cv _ _ _ _ _ RG0 ltac:(rewrite HEXA by lia; exact U2)
    (fun n r (Hn : (n < 32)%nat) Hr => eq_trans (HEXA n ltac:(lia)) (EE n r Hr))) as HSV;
  clear RG0.

(* ssw_rg of the machine state of HS on a path from the entry (sp = the entry sp - 48, s0 = c, s1 = s,
   s2 = s + 18144, a2 = s2 >> 3, s3 = the shadow base). *)
Ltac ent_rg HS cv HEXA EE E10 E11 E32 Hgp Htp :=
  split;
  [ ssw_rv_open HS; rewrite (ssw_soffk _ 2 (-48) (ssw_SP cv));
    [ unfold w64; f_equal; lia
    | rewrite ?HEXA by lia; rewrite (EE 2%nat 2%bv eq_refl); unfold ssw_SP, spZ; rewrite Z_to_bv_bv_unsigned; reflexivity
    | lia ] |];
  split; [ssw_rv_open HS; apply ssw_soff0; rewrite ?HEXA by lia; rewrite (EE 3%nat 3%bv eq_refl); exact Hgp |];
  split; [ssw_rv_open HS; apply ssw_soff0; rewrite ?HEXA by lia; rewrite (EE 4%nat 4%bv eq_refl); exact Htp |];
  split; [ssw_rv_open HS; apply ssw_soff0; rewrite ?HEXA by lia; exact E11 |];
  split; [ssw_rv_open HS; apply ssw_soff0; rewrite ?HEXA by lia; rewrite E10; reflexivity |];
  split; [ssw_rv_open HS; cbn [sv_denot]; rewrite ?HEXA by lia; rewrite E10; apply bv_eq; vm_compute; reflexivity |];
  split; [ssw_rv_open HS; cbn [sv_denot]; rewrite ?HEXA by lia; rewrite E10; apply bv_eq; vm_compute; reflexivity |];
  split; [ssw_rv_open HS; apply ssw_soff0; rewrite ?HEXA by lia; exact E32 |];
  let r := fresh "r" in let Hr := fresh "Hr" in let Er := fresh "Er" in
  intros r Hr;
  assert (Er : r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia;
  repeat (destruct Er as [-> | Er];
    [ssw_rv_open HS; apply ssw_soff0; rewrite ?HEXA by lia; apply EE; reflexivity |]);
  subst r; ssw_rv_open HS; apply ssw_soff0; rewrite ?HEXA by lia; apply EE; reflexivity.

Section entw. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation G := TG.G_HARNESS.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

Lemma ssw_seg_entry : (forall c, @ssw_app_cut fx rc B MT c) -> (forall c, @ssw_loop_cut fx rc B MT c) ->
  forall c, ssw_rt B MT -> ssw_ok B c ->
  SRr segs (cx_W c) (@cfg_at fx segs (transport_sigma TS_diginet_session_submit) (cx_regs c) (cx_memc c) (cx_mdc c))
    (ssw_post B MT c).
Proof.
intros HAPP HLOOP c HRT HOK.
pose proof HRT as (HCELLS & HSC & LAWS & MTL & HGX & HGE & HBC & HAI0).
pose proof (ssw_ok_stack B c HOK) as (HAR0 & Hsp & Hce & Hwin).
pose proof (ssw_ok_sp B c HOK) as (Hsp16 & Hsp0 & Hlo & Hhi & Ho16 & ESS).
pose proof (ssw_ok_cp B MT c HRT HOK) as (Hc0 & Hc47 & Hcoff & HRD0).
pose proof HOK as (HJ & Hra & Hra4 & Hgp & Htp & H10 & H11 & _ & _ & _ & Htw & Hm & HL0 & Hcp0 & Hcp4 & HSRC & HC8
  & HOFF & HNGR & Hcnt & Hev).
assert (HNG : forall x, cx_cp c <= x < cx_cp c + 32 -> ~ inG G x)
  by (intros x Hx; exact (proj1 (HNGR x ltac:(unfold SSUBMIT_CMD_LEN; lia)))).
assert (HLB : length (cx_Bw c) = Z.to_nat TW.W_LEN) by exact (tw_len _ _ _ Htw).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (EST : ESTACK = 4096) by reflexivity.
assert (EBC : PBC.TRANS_BC_STK = 4400) by reflexivity.
assert (EC : TA_g_s = 6158784) by reflexivity.
assert (Rlen : 0 <= ssw_len c < 256) by (unfold ssw_len, TS0.cmd_len_of; exact (SSK.ssk_u1 _ _)).
assert (Rkey : 0 <= ssw_key c < 2 ^ 32) by (unfold ssw_key, TS0.cmd_key_of; exact (TWL.u_at_range _ _ 4)).
assert (Rq : 0 <= ssw_q c < 2 ^ 32) by (unfold ssw_q; exact (TWL.u_at_range _ _ 4)).
assert (Rref : 0 <= TW.S_stats_refused (cx_Bw c) < 2 ^ 64) by (unfold TW.S_stats_refused; exact (TWL.u_at_range _ _ 8)).
assert (HL : ssw_lite B c (cx_W c) (cx_memc c) (cx_Bw c))
  by (split; [apply dk_kept_refl_g; exact Hwin | split; [exact HC8 | split; [exact HRD0 | exact Htw]]]).
destruct (ent_entry B MT c HRT HOK) as [HS SHOK].
set (E0 := ent_E c) in HS, SHOK.
assert (HEI : img_env VAL A_LIM E0) by (unfold E0, ent_E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E0 n = YK11.getr (cx_regs c) r)
  by (intros n r Hn; unfold E0, ent_E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (EXT : forall i, (i < 6)%nat -> ew E0 (32 + i) = nth i (ent_extra c) (Z_to_bv 64 0))
  by (intros i Hi; unfold E0, ent_E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EXT 0%nat ltac:(lia)) as E32. pose proof (EXT 1%nat ltac:(lia)) as E33.
pose proof (EXT 2%nat ltac:(lia)) as E34. pose proof (EXT 3%nat ltac:(lia)) as E35.
pose proof (EXT 4%nat ltac:(lia)) as E36. pose proof (EXT 5%nat ltac:(lia)) as E37.
cbn [Nat.add nth ent_extra] in E32, E33, E34, E35, E36, E37. clear EXT.
pose proof (EE 10%nat 10%bv eq_refl) as E10. rewrite H10 in E10.
pose proof (EE 11%nat 11%bv eq_refl) as E11. rewrite H11 in E11.
assert (U2 : bv_unsigned (ew E0 2) = ssw_SP c) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS G HGX 0 []) as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS G HGX 0 []) as RUNTO.
pose proof (paj_ret_at (fx := fx) (PL := PL_transport) (PI := PI_transport)) as RET.
pose proof (paj_branch (fx := fx) (PI := PI_transport)) as BR.
unfold cfg_at.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst fx (cx_regs c) (Z_to_bv 64 (BASE + AF_diginet_session_submit)) (cx_memc c)
    (YK11.seg_rom segs)) (cx_mdc c)) Q) end.
(* +0x0 .. +0x58: the frame, the saves, the null tests, s0, s3, the check of len, `bltu` *)
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ ssw_awr_stk E0 U2. }
ssw_after_stk B MT c HRT HOK HL E0 U2.
psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
- (* len outside [1, 24]: a0 = -1, the return *)
  ssw_low HS E0 HEX.
  lazymatch type of Hc with context [sv_denot ?Ex (SOff 33 (-25))] =>
    replace (sv_denot Ex (SLit 18446744073709551592)) with (sv_denot Ex (SLit (-24))) in Hc
      by (cbn [sv_denot]; apply bv_eq; reflexivity);
    rewrite (SSK.ssk_br_len Ex 33 (ssw_len c) ltac:(first [exact E33 | rewrite HEX by lia; exact E33]) Rlen) in Hc
  end.
  destruct (SSK.ssk_arg _ _ _ _ Hc Hm) as [HBw' Hr].
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { ssw_awr_stk HEX U2. }
  ssw_after_stk B MT c HRT HOK HL HEX U2.
  ssw_low HS E0 HEXF.
  eapply (RET (cx_W c) _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'.
  apply (ssw_close B MT c (cx_lyc c) (cx_Sc c) (cx_W c) _ _ _ HRT HOK HJ eq_refl (Permutation_refl _)
    (mo_le_refl MT MTL _) (proj1 HL)).
  + lazymatch type of HS with st_ok_pi _ _ ?EF _ (restrict _ ?msF) =>
      apply (aregs_preserved_of_st_ok segs (w_H (cx_W c)) EF _ msF (cx_regs c) (ent_extra c) HS);
      [ split; [intros n Hn; rewrite ?HEXF by lia; unfold E0, ent_E; apply Eimg_low; unfold A_TEXT; lia | reflexivity]
      | vm_compute; reflexivity ]
    end.
  + ssw_rv_open HS. apply ssw_soff0. rewrite ?HEXF by lia. apply EE. reflexivity.
  + ssw_rv_open HS. rewrite Hr. apply bv_eq. reflexivity.
  + rewrite HBw'. exact (proj2 (proj2 (proj2 HL))).
- (* len in [1, 24]: the call of diginet_body_check *)
  ssw_low HS E0 HEX.
  lazymatch type of Hc with context [sv_denot ?Ex (SOff 33 (-25))] =>
    replace (sv_denot Ex (SLit 18446744073709551592)) with (sv_denot Ex (SLit (-24))) in Hc
      by (cbn [sv_denot]; apply bv_eq; reflexivity);
    rewrite (SSK.ssk_br_len Ex 33 (ssw_len c) ltac:(first [exact E33 | rewrite HEX by lia; exact E33]) Rlen) in Hc
  end.
  rename Hc into Hlen.
  assert (Hlen' : 1 <= ssw_len c <= 24)
    by (apply orb_false_iff in Hlen as [H1 H2]; apply Z.eqb_neq in H1; apply Z.ltb_ge in H2;
        unfold TS0.DIGINET_CMD_MAX_LEN in H2; lia).
  (* +0x5c .. +0x6c: s2 = s + 18144, a0 = c, `jal diginet_body_check` *)
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { ssw_awr_stk HEX U2. }
  ssw_after_stk B MT c HRT HOK HL HEX U2.
  ssw_low HS E0 HEX1.
  pmkst HS.
  ssw_reg HS (Z_to_bv 5 10) (w64 (cx_cp c)) Q10
    ltac:(apply ssw_soff0; first [exact E11 | rewrite HEX1 by lia; exact E11]).
  ssw_reg HS (Z_to_bv 5 11) (w64 (ssw_len c)) Q11
    ltac:(apply ssw_soff0; first [exact E33 | rewrite HEX1 by lia; exact E33]).
  ssw_reg HS (Z_to_bv 5 2) (w64 (ssw_SP c - 48)) Q2
    ltac:(rewrite (ssw_soffk _ 2 (-48) (ssw_SP c)); [reflexivity | | lia];
          rewrite ?HEX1 by lia; rewrite (EE 2%nat 2%bv eq_refl); unfold ssw_SP, spZ; rewrite Z_to_bv_bv_unsigned; reflexivity).
  ssw_reg HS (Z_to_bv 5 1) (Z_to_bv 64 (BASE + SSW_RET_BC)) R1
    ltac:(apply codeptr_val; lazymatch goal with H : img_env _ _ ?Ex |- img_env _ _ ?Ex => exact H end).
  ssw_reg HS (Z_to_bv 5 3) (w64 (as_gp B)) R3
    ltac:(apply ssw_soff0; rewrite ?HEX1 by lia; rewrite (EE 3%nat 3%bv eq_refl); exact Hgp).
  ssw_reg HS (Z_to_bv 5 4) (w64 (as_tp B)) R4
    ltac:(apply ssw_soff0; rewrite ?HEX1 by lia; rewrite (EE 4%nat 4%bv eq_refl); exact Htp).
  lazymatch type of Q2 with YK11.getr ?rg _ = _ =>
    assert (Hsp1 : spZ rg = ssw_SP c - 48)
      by (change (bv_unsigned (YK11.getr rg (Z_to_bv 5 2)) = ssw_SP c - 48); rewrite Q2; apply unsigned_lit_small; lia)
  end.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transport_sigma TS_diginet_body_check)) mm rom) mdx) Q) end.
  set (bb := firstn (Z.to_nat (ssw_len c)) (cx_C c)).
  assert (Hbb : length bb = Z.to_nat (ssw_len c)) by (unfold bb; rewrite length_firstn, HL0; lia).
  pose proof HL as (KA1 & HC1 & HRD1 & HTW1).
  lazymatch goal with |- SRr _ _ (mkCfg (@YK11.mkst _ ?rg _ ?mm _) ?mdx) _ =>
    eapply SRr_bind;
    [ apply (@gx_call_cg fx rc tfib_sink_head segs B MT G (cx_STK c) (cx_sp0 c) (cx_FP c)
        (cx_ly c) (cx_S c) (cx_W0 c) (cx_mem0 c) (cx_md0 c) (cx_own c) (cx_lyc c) (cx_Sc c) (cx_W c) mm mdx (cx_k c) _ rg
        PBC.TRANS_BC_STK PBC.TRANS_BC_EV 0 (fun _ => False)
        (fun regs2 _ _ => YK11.getr regs2 10 = w64 (DL.body_check bb)) HGX HGE HJ) | ]
  end.
  { intros memS HJi.
    assert (R1b : YK11.getr _ 1%bv = Z_to_bv 64 (BASE + SSW_RET_BC)) by exact R1.
    eapply SRr_mono.
    { apply (HBC fx (cx_STK c) (cx_sp0 c) (cx_FP c) (cx_ly c) (cx_S c) (cx_W0 c) memS (cx_md0 c) (cx_own c)
        (cx_lyc c) (cx_Sc c) (cx_W c) _ _ (cx_k c) _ (cx_cp c) bb HJi).
      - rewrite R1b. apply (ret_ok_codeptr_v (PI := PI_transport)); [unfold SSW_RET_BC, AF_diginet_session_submit; lia | reflexivity].
      - unfold raZ. rewrite R1b. destruct ent_vals as (_ & _ & _ & EB). rewrite EB.
        rewrite unsigned_lit_small by (unfold SSW_RET_BC, AF_diginet_session_submit; lia).
        unfold SSW_RET_BC, AF_diginet_session_submit. lia.
      - exact R3.
      - exact R4.
      - exact Q10.
      - rewrite Hbb, Z2Nat.id by lia. exact Q11.
      - rewrite Hsp1. replace (ssw_SP c - 48) with (ssw_SP c + (-3) * 16) by lia. rewrite Z_mod_plus_full. exact Hsp16.
      - rewrite Hsp1. lia.
      - rewrite Hsp1. lia.
      - left. exact Hcp0.
      - intros _. rewrite Hbb, Z2Nat.id by lia.
        apply (trans_src_ok_sub B _ _ _ _ (cx_cp c) 32); [| lia | lia | lia].
        exact (ssw_src_rd B _ _ _ _ _ _ _ HSRC HRD1).
      - intros _. rewrite Hbb, Z2Nat.id by lia. unfold decode_off_win. rewrite Hsp1. lia.
      - unfold bb. rewrite <- firstn_map. exact (ssw_garr8_firstn _ _ _ _ HC1).
      - exact Hcnt.
      - unfold PBC.TRANS_BC_EV. unfold SSUBMIT_EV in Hev. lia. }
    intros W2 c2 _ H. exact (decode_cg_post_dcg B MT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H). }
  cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & e & -> & He & HJ2 & HP2 & Hfr2 & Hperm2 & HK2 & HMO2 & HA0 & HGK).
  unfold PBC.TRANS_BC_EV in He. replace e with 0 in HJ2 by lia. rewrite Z.add_0_r in HJ2.
  pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR1.
  pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HAR2.
  rewrite Hsp1, EBC in HK2.
  pose proof HK2 as (K21 & K22 & K23 & K24 & K25 & K26).
  pose proof KA1 as (_ & _ & _ & _ & _ & KA16).
  (* what the call keeps: the caller's bytes from the entry, the command, g_s *)
  assert (KA2 : acall_kept_g segs B G (cx_lyc c) (cx_Sc c) (cx_W c) (cx_memc c) W2 mem2
                  (ssw_SP c - SSUBMIT_STK) (ssw_SP c) ssubmit_wr).
  { eapply dk_kept_trans_g; [lia | lia | exact KA1 | exact HK2 | lia | lia | intros a []]. }
  destruct (ssw_ly_same B c ly2 S2 W2 mem2 md2 (cx_k c) HOK HJ2) as (FA & FLO & FHI).
  destruct (ssw_src_acall B LAWS (cx_lyc c) (cx_Sc c) (cx_W c) (ms_mem ms0) mdw0 ly2 S2 W2 mem2 md2
     (ssw_SP c - 48 - 4400) (ssw_SP c - 48) (fun _ => False) (cx_cp c) 32 HAR1 HAR2 Hperm2 Hfr2 FA FLO FHI HK2
     (fun _ _ x => x) (fun _ _ x => x) ltac:(lia) (fun a Ha => HNGR a ltac:(unfold SSUBMIT_CMD_LEN; lia))
     (ssw_src_rd B _ _ _ _ _ _ _ HSRC HRD1) ltac:(lia)) as [HSRC2 KC2].
  assert (HL2 : ssw_lite B c W2 mem2 (cx_Bw c)).
  { split; [exact KA2|]. split.
    - apply (ssw_garr8_xfer (w_H (cx_W c)) (w_H W2) (ms_mem ms0) mem2); [|exact HC1].
      intros i Hi. unfold TW.zs in Hi. rewrite List.length_map, HL0 in Hi. apply KC2. lia.
    - split; [exact (trans_src_ok_rd B LAWS _ _ _ _ _ _ _ HAR2 HSRC2 ltac:(lia)) |].
      apply (tw_kept TMAP_A (aview segs (w_H (cx_W c)) (ms_mem ms0))); [exact HTW1|].
      intros x Hx. apply HGK. exact (ssw_tw_in_G x Hx). }
  clear HL KA1 HC1 HRD1 HTW1.
  (* the state after the call keeps the frame, the command's bytes and queued *)
  jafter_call_keep_hi HS 1024%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0%nat; 3%nat; 4%nat] HS2.
  match type of HS2 with ?tq -> _ => assert (HRK : tq) end.
  { cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
    - apply (ssw_region_kept2 E0 _ _ _ _ 2%nat (ssw_SP c)); [exact U2 | |].
      + intros a Ha. apply K21; lia.
      + intros a Ha. apply (apresent_writable segs). apply K25; [lia | lia |]. apply KA16. lia.
    - apply (ssw_region_kept2 E0 _ _ _ _ 11%nat (cx_cp c)); [rewrite E11; apply unsigned_lit_small; lia | | intros a Ha; lia].
      intros a Ha. apply KC2. lia.
    - apply (ssw_region_kept2 E0 _ _ _ _ 10%nat TA_g_s);
        [rewrite E10; apply unsigned_lit_small; unfold SSUBMIT_S; lia | | intros a Ha; lia].
      intros a Ha. apply HGK. apply ssw_gs_inG. unfold TW.SZ_g_s. lia. }
  specialize (HS2 HRK). clear HRK HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
  lazymatch type of HS with st_ok_pi _ _ (havoc ?Ex ?kk ?ws) _ _ =>
    lazymatch goal with H : img_env _ _ Ex |- _ =>
      assert (HEIc : img_env VAL A_LIM (havoc Ex kk ws)) by (apply img_env_havoc_hi; [exact H | cbv; lia]) end end.
  ssw_low HS E0 HEX3.
  lazymatch type of HS with st_ok_pi _ _ ?E1 _ _ =>
    assert (SHOK1 : sh_ok segs SSW_Bx ENT_SH E1 (mrestrict (w_H W2) mem2))
      by (apply (ent_shok B c _ _ _ _ _ E1 HSC HAR2 (proj1 (proj2 (proj2 HL2))) Hc0 Hc47);
          [rewrite HEX3 by lia; rewrite E10; reflexivity | rewrite HEX3 by lia; exact E11
          | rewrite HEX3 by lia; exact E32]) end.
  clear SHOK.
  (* a0 after the call is diginet_body_check's answer *)
  ssw_rv HS (Z_to_bv 5 10) R10.
  lazymatch type of R10 with _ = sv_denot ?E1 ?e =>
    assert (A0 : sv_denot E1 e = w64 (DL.body_check bb)) by (rewrite <- R10; exact HA0) end.
  clear R10.
  (* +0x70: `beqz a0` *)
  assert (R1c : YK11.getr (ms_regs ms0) 1%bv = Z_to_bv 64 (BASE + 36092)) by exact R1.
  rewrite R1c.
  psrr_branch_tok RUN BR HS SHOK1 YC4b.Bspan.
  + (* diginet_body_check answered 0: the queue *)
    rewrite A0 in Hc. cbn [sv_denot] in Hc.
    assert (Hbc0 : DL.body_check bb = 0).
    { destruct (ssw_bc_cases bb) as [Z|Z]; [exact Z|]. rewrite Z in Hc. vm_compute in Hc. discriminate. }
    clear Hc.
    pose proof (SSK.ssk_ok_tail (cx_Bw c) (cx_C c) (cx_Bw' c) (cx_r c) Hlen Hbc0 Hm) as HMk.
    rewrite SSK.ssk_coal_kinds in HMk. fold (ssw_key c) in HMk. fold (ssw_q c) in HMk.
    (* +0x9c .. +0xc8: the key's check, a4 = key, the kind test `bne (kind | 8) & 255, 8` *)
    paj_run_tok RUN HS HJ2 SHOK1 YC4b.Bspan.
    { ssw_awr_stk HEX3 U2. }
    ssw_after_stk B MT c HRT HOK HL2 HEX3 U2.
    psrr_branch_tok RUN BR HS SHOK1 YC4b.Bspan.
    * (* the kind is neither 0 nor 8 *)
      ssw_low HS E0 HEX4.
      rewrite ssw_br_ne, (SSK.ssk_br_kind08 _ 34 (ssw_key c) ltac:(rewrite HEX4 by lia; exact E34) Rkey) in Hc.
      apply negb_true_iff in Hc. rewrite Hc in HMk. cbn [orb] in HMk. clear Hc.
      (* +0x134 .. +0x140: the kind-9 test *)
      paj_run_tok RUN HS HJ2 SHOK1 YC4b.Bspan.
      { ssw_awr_stk HEX4 U2. }
      ssw_after_stk B MT c HRT HOK HL2 HEX4 U2.
      psrr_branch_tok RUN BR HS SHOK1 YC4b.Bspan.
      -- (* kind 9: the append *)
         ssw_low HS E0 HEX5.
         rewrite (SSK.ssk_br_kind9 _ 34 (ssw_key c) ltac:(rewrite HEX5 by lia; exact E34) Rkey) in Hc.
         rewrite Hc in HMk. cbn [orb] in HMk. clear Hc.
         paj_run_to_tok RUNTO HS HJ2 SHOK1 YC4b.Bspan SSW_APP.
         { ssw_awr_stk HEX5 U2. }
         ssw_after_stk B MT c HRT HOK HL2 HEX5 U2.
         ssw_low HS E0 HEXA.
         ent_saved HS c HEXA EE U2 HSV.
         pmkst HS.
         apply (HAPP c ly2 S2 W2 _ _ _ HRT HOK);
           [exact (conj HJ2 (conj Hfr2 (conj Hperm2 (conj HMO2 (conj HL2 HSV)))))
           | ent_rg HS c HEXA EE E10 E11 E32 Hgp Htp | exact HMk].
      -- (* not kind 9: the queue's length *)
         ssw_low HS E0 HEX5.
         rewrite (SSK.ssk_br_kind9 _ 34 (ssw_key c) ltac:(rewrite HEX5 by lia; exact E34) Rkey) in Hc.
         rewrite Hc in HMk. cbn [orb] in HMk. clear Hc.
         (* +0x144 .. +0x154: queued's check, a3 = queued, `beqz a3` *)
         paj_run_tok RUN HS HJ2 SHOK1 YC4b.Bspan.
         { ssw_awr_stk HEX5 U2. }
         ssw_after_stk B MT c HRT HOK HL2 HEX5 U2.
         psrr_branch_tok RUN BR HS SHOK1 YC4b.Bspan.
         ++ (* no command queued: the append *)
            ssw_low HS E0 HEX6.
            rewrite (SSK.ssk_br_qzero _ 35 (ssw_q c) ltac:(rewrite HEX6 by lia; exact E35) Rq) in Hc.
            apply Z.eqb_eq in Hc. rewrite Hc in HMk. cbn [Z.to_nat TS0.submit_find_m] in HMk.
            paj_run_to_tok RUNTO HS HJ2 SHOK1 YC4b.Bspan SSW_APP.
            { ssw_awr_stk HEX6 U2. }
            ssw_after_stk B MT c HRT HOK HL2 HEX6 U2.
            ssw_low HS E0 HEXA.
            ent_saved HS c HEXA EE U2 HSV.
            pmkst HS.
            apply (HAPP c ly2 S2 W2 _ _ _ HRT HOK);
              [exact (conj HJ2 (conj Hfr2 (conj Hperm2 (conj HMO2 (conj HL2 HSV)))))
              | ent_rg HS c HEXA EE E10 E11 E32 Hgp Htp | exact HMk].
         ++ (* the search from entry 0 *)
            ssw_low HS E0 HEX6.
            rewrite (SSK.ssk_br_qzero _ 35 (ssw_q c) ltac:(rewrite HEX6 by lia; exact E35) Rq) in Hc.
            apply Z.eqb_neq in Hc.
            (* +0x158 .. +0x160: a0 = &s->queue[0], a1 = a0 + 28, a4 = key sign-extended *)
            paj_run_to_tok RUNTO HS HJ2 SHOK1 YC4b.Bspan SSW_LOOP.
            { ssw_awr_stk HEX6 U2. }
            ssw_after_stk B MT c HRT HOK HL2 HEX6 U2.
            ssw_low HS E0 HEXA.
            ent_saved HS c HEXA EE U2 HSV.
            pmkst HS.
            apply (HLOOP c HRT HOK 0 W2).
            do 5 eexists. split; [reflexivity|].
            split; [exact (conj HJ2 (conj Hfr2 (conj Hperm2 (conj HMO2 (conj HL2 HSV))))) |].
            split; [ent_rg HS c HEXA EE E10 E11 E32 Hgp Htp |].
            split.
            { ssw_rv_open HS.
              rewrite (ssw_soffk _ 10 1760 TA_g_s) by (first [rewrite HEXA by lia; rewrite E10; reflexivity | rewrite EC; lia]).
              unfold w64. f_equal; lia. }
            split.
            { ssw_rv_open HS.
              rewrite (ssw_soffk _ 10 1788 TA_g_s) by (first [rewrite HEXA by lia; rewrite E10; reflexivity | rewrite EC; lia]).
              unfold w64. f_equal; lia. }
            split.
            { ssw_rv_open HS. apply ssw_soff0. rewrite HEXA by lia. rewrite E35. unfold w64. f_equal; lia. }
            split.
            { ssw_rv_open HS. apply (SSK.ssk_sextw _ 34 (ssw_key c)); [rewrite HEXA by lia; exact E34 | exact Rkey]. }
            split; [lia|].
            replace (ssw_q c - 0) with (ssw_q c) by lia. exact HMk.
    * (* the kind is 0 or 8: the append *)
      ssw_low HS E0 HEX4.
      rewrite ssw_br_ne, (SSK.ssk_br_kind08 _ 34 (ssw_key c) ltac:(rewrite HEX4 by lia; exact E34) Rkey) in Hc.
      apply negb_false_iff in Hc. rewrite Hc in HMk. cbn [orb] in HMk. clear Hc.
      paj_run_to_tok RUNTO HS HJ2 SHOK1 YC4b.Bspan SSW_APP.
      { ssw_awr_stk HEX4 U2. }
      ssw_after_stk B MT c HRT HOK HL2 HEX4 U2.
      ssw_low HS E0 HEXA.
      ent_saved HS c HEXA EE U2 HSV.
      pmkst HS.
      apply (HAPP c ly2 S2 W2 _ _ _ HRT HOK);
        [exact (conj HJ2 (conj Hfr2 (conj Hperm2 (conj HMO2 (conj HL2 HSV)))))
        | ent_rg HS c HEXA EE E10 E11 E32 Hgp Htp | exact HMk].
  + (* diginet_body_check answered -10: refused + 1, -10 *)
    rewrite A0 in Hc. cbn [sv_denot] in Hc.
    assert (Hbc : DL.body_check bb = -10).
    { destruct (ssw_bc_cases bb) as [Z|Z]; [|exact Z]. rewrite Z in Hc. vm_compute in Hc. discriminate. }
    clear Hc.
    destruct (SSK.ssk_refused (cx_Bw c) (cx_C c) (cx_Bw' c) (cx_r c) Hlen
      ltac:(change (DL.body_check bb <> 0); rewrite Hbc; discriminate) Hm) as [HBw' Hr].
    assert (HCG : cx_cp c + 32 <= TA_g_s + 18256 \/ TA_g_s + 18264 <= cx_cp c + 24).
    { destruct (Z_le_gt_dec (cx_cp c + 32) (TA_g_s + 18256)) as [H1|H1]; [left; exact H1|].
      destruct (Z_le_gt_dec (TA_g_s + 18264) (cx_cp c + 24)) as [H2|H2]; [right; exact H2|].
      exfalso. apply (HNG (Z.max (cx_cp c + 24) (TA_g_s + 18256))); [lia|].
      apply ssw_gs_inG. unfold TW.SZ_g_s. lia. }
    (* g_s.stats.refused added, writable *)
    lazymatch type of HS with st_ok_pi _ _ _ ?s _ => let s' := eval vm_compute in s in change s with s' in HS end.
    lazymatch type of HS with st_ok_pi _ _ ?E1 ?s ?msx =>
      assert (HSg : st_ok_pi segs VAL E1 (mkSS (ss_pc s) (ss_regs s) (ent_gref :: ss_mem s) (ss_resv s) (ss_facts s)) msx)
    end.
    { apply (st_ok_pi_add_region (PI := PI_transport) _ _ _ ent_gref HS); [vm_compute; reflexivity | |].
      - cbn [ms_mem restrict]. unfold ent_gref, region_ok.
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
        rewrite (ssw_base _ 10 TA_g_s) by (first [rewrite HEX3 by lia; rewrite E10; reflexivity | rewrite EC; lia]).
        split; [lia|]. split; [lia|]. split.
        { intros o Ho. apply (gx_rw_writable segs G _ G_HARNESS_rw). apply ssw_gs_inG. unfold TW.SZ_g_s. lia. }
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val segs _ _ TA_g_s 18256 8 (SOff 37 0) (TW.S_stats_refused (cx_Bw c)));
          [apply ssw_soff0; rewrite HEX3 by lia; exact E37 | exact Rref | lia |].
        destruct HL2 as (_ & _ & _ & Htw2).
        exact (tw_read_val segs _ TMAP_A _ TW.OFF_g_s TA_g_s TW.SZ_g_s 18256 8 TMAP_A_ok Htw2 TMAP_A_g_s
          ltac:(lia) ltac:(unfold TW.SZ_g_s; lia)).
      - cbn [ss_mem all_disjoint]. unfold extent_disjoint, ent_gref. cbn [YP09.r_base YP09.r_lo YP09.r_hi].
        rewrite (ssw_base _ 10 TA_g_s) by (first [rewrite HEX3 by lia; rewrite E10; reflexivity | rewrite EC; lia]).
        rewrite (ssw_base _ 2 (ssw_SP c)) by (first [rewrite HEX3 by lia; rewrite (EE 2%nat 2%bv eq_refl);
          unfold ssw_SP, spZ; rewrite Z_to_bv_bv_unsigned; reflexivity | lia]).
        rewrite (ssw_base _ 11 (cx_cp c)) by (first [rewrite HEX3 by lia; exact E11 | lia]).
        repeat split; first [exact I | lia]. }
    clear HS. rename HSg into HS.
    lazymatch type of HS with st_ok_pi _ _ _ ?s _ => let s' := eval vm_compute in s in change s with s' in HS end.
    (* +0x74 .. and the epilogue: refused's check, + 1, the store, a0 = -10, `ret` *)
    paj_run_tok RUN HS HJ2 SHOK1 YC4b.Bspan.
    { lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
        let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
      apply awr_ok_x_cons_g.
      - intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha.
        rewrite (ssw_base _ 10 TA_g_s) in Ha by (first [rewrite HEX3 by lia; rewrite E10; reflexivity | rewrite EC; lia]).
        apply ssw_gs_inG. unfold TW.SZ_g_s. lia.
      - ssw_awr_stk HEX3 U2. }
    lazymatch goal with |- SRr _ _ (mkCfg _ (with_vm_backing (m_vm_lazy ?m0) ?mt ?m0)) _ =>
      set (mdF := with_vm_backing (m_vm_lazy m0) mt m0) in *; clearbody mdF; clear mt end.
    ssw_low HS E0 HEXF.
    assert (HWR : forall a, TA_g_s + 18256 <= a < TA_g_s + 18256 + Z.of_nat 8 -> ssubmit_wr a)
      by (intros a Ha; right; right; left; unfold twa_fld, TW.A_S_stats_refused; lia).
    lazymatch goal with HFr : frame_of _ _ (mrestrict (w_H W2) ?m1) (mrestrict (w_H W2) ?m2), HG : mem_grows _ _ |- _ =>
      assert (KW : forall a, 0 <= a < 2 ^ 64 -> ~ (ssw_SP c - 48 <= a < ssw_SP c) ->
        ~ (TA_g_s + 18256 <= a < TA_g_s + 18256 + Z.of_nat 8) -> aview segs (w_H W2) m2 a = aview segs (w_H W2) m1 a)
        by (intros a Ha Hn1 Hn2;
            apply (kept_of_frame _ _ _ _ _
              (fun x => (ssw_SP c - 48 <= x < ssw_SP c) \/ (TA_g_s + 18256 <= x < TA_g_s + 18256 + Z.of_nat 8)) HFr);
            [ intros b wlo whi x Hin Hx; ssw_win Hin Hx ltac:(first [lia |
                rewrite ?HEXF in Hx by lia; rewrite U2 in Hx; cbv beta; lia |
                rewrite ?HEXF in Hx by lia; rewrite E10 in Hx; unfold w64 in Hx;
                rewrite unsigned_lit_small in Hx by (unfold SSUBMIT_S; lia); unfold SSUBMIT_S in Hx; cbv beta; lia])
            | exact Ha | intros [H1 | H1]; [exact (Hn1 H1) | exact (Hn2 H1)] ]);
      first [pose proof (st_ok_pi_region_nth (PI := PI_transport) _ _ _ 0 _ HS eq_refl) as RGC
            | pose proof (YC4b.st_ok_region_nth _ _ _ 0 _ HS eq_refl) as RGC];
      cbn [ms_mem restrict] in RGC;
      pose proof (field_of_region_any _ _ 10%nat TA_g_s _ _ _ _ _ 18256 8 (SOff 37 1) RGC
        ltac:(apply ssw_U; [rewrite HEXF by lia; rewrite E10; reflexivity | rewrite EC; lia])
        ltac:(cbn; tauto) ltac:(lia)) as VQ;
      rewrite (ssw_soffk _ 37 1 (TW.S_stats_refused (cx_Bw c))) in VQ by (first [rewrite HEXF by lia; exact E37 | lia]);
      change (N.to_nat 8) with 8%nat in VQ;
      pose proof (ssw_lite_store B MT c W2 m1 m2 _ 18256 8 (TW.S_stats_refused (cx_Bw c) + 1) HRT HOK HL2 ltac:(lia)
        ltac:(unfold TW.SZ_g_s; lia) HWR KW (fun a Ha => apresent_grows _ _ _ a HG Ha)
        (fun i Hi => eq_trans (ssw_vm_aview (w_H W2) m2 _ 8 _ i VQ Hi) (f_equal Some (ssw_le8' _ i)))) as HL3;
      clear RGC VQ
    end.
    lazymatch goal with HF : frame_of _ _ _ _, HFr : frame_of _ _ _ _, HG : mem_grows _ _ |- _ => clear HF HFr HG end.
    eapply (RET W2 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
    intros mat'.
    apply (ssw_close B MT c ly2 S2 W2 _ _ _ HRT HOK HJ2 Hfr2 Hperm2 HMO2 (proj1 HL3)).
    * lazymatch type of HS with st_ok_pi _ _ ?EF _ (restrict _ ?msF) =>
        apply (aregs_preserved_of_st_ok segs _ EF _ msF (cx_regs c) (ent_extra c) HS);
        [ split; [intros n Hn; rewrite ?HEXF by lia; unfold E0, ent_E; apply Eimg_low; unfold A_TEXT; lia | reflexivity]
        | vm_compute; reflexivity ]
      end.
    * ssw_rv_open HS. apply ssw_soff0. rewrite ?HEXF by lia. apply EE. reflexivity.
    * ssw_rv_open HS. rewrite Hr. apply bv_eq. reflexivity.
    * destruct HL3 as (_ & _ & _ & Htw3). rewrite HBw'. rewrite <- SSK.ssk_put_refused.
      replace TW.A_S_stats_refused with (TW.OFF_g_s + 18256) by (unfold TW.A_S_stats_refused; lia).
      exact Htw3.
Qed.

End entw.
