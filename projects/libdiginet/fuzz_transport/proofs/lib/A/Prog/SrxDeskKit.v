(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, origin/cold/pg-prog), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/CanKit.v, with its module names changed; 492 of its 559 lines of code are new or changed and 457 lines of the source are left out. *)
(* SrxDeskKit: the lemmas the desk piece (lib/A/Prog/SrxDesk.v) and the learn piece (lib/A/Prog/SrxLearn.v) of the
   walk of diginet_session_rx (lib/A/Prog/SrxCut.v) share. Between the desk cut (+0x2d8) and the cuts the two pieces
   end in, the code changes memory only in the stack window of a runtime callee (the bcmp wrapper, the leaf
   diginet_mac_is_digidesign, __asan_memcpy: below the realigned sp), in the slot s1 + 24 of its own machine frame,
   and in g_s's desk_mac and desk_known (bytes of G and rows of srx_wr b). srxk_move carries every fact a cut holds
   (srx_cur, srx_rd, f's decode_rd_ok and srx_fbytes) to a memory that differs from the cut's only there: a byte of G
   keeps its visibility (TransportGCg.v gx_rw_vis) and no shadow byte changes, so the placements (trans_src_ok) of
   every range survive, and the bytes the facts name by value (buf, TF, f, the saved words, the flag word) lie outside
   these bytes. The rest: the frame's bytes the code reads (fr_src b at f + 6, h.cmd at f + 30, cells of
   frame_f_bytes), the memeq test of :279 against the bcmp wrapper's result, the wrapper's contract at the walk's G
   journal, g_s's addressability (trans_srx_cells), the shadow byte's address of a field, and the tactics that read a
   register or a region off a run's symbolic state. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportSyms DgnTransportList DgnTransportAddr DgnTransportPa DgnTransportImg DgnTransportPaLib YC4b YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG AF0x.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportCg TransportGCg TransportGRwA TransportGRunA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA TImgA CanKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import check_state_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Mem Cells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog Require diginet_frame_parse_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TSess0 TSess TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_rx_cg SrxCut.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module LMem := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Mem.
Module LC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Cells.
Module ACells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.AsanCells.
Module PParse := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.diginet_frame_parse_c.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* g_s's payload bytes are bytes of G. *)
Lemma srxk_inG : forall a, SRX_S <= a < SRX_S + TW.SZ_g_s -> inG TG.G_HARNESS a.
Proof.
intros a Ha. unfold inG. apply Exists_exists. exists (0x5df9c0, 18264). split.
- unfold TG.G_HARNESS. cbn [In]. tauto.
- unfold in_zr, SRX_S, TA_g_s, TW.SZ_g_s in *. cbn [fst snd]. lia.
Qed.

(* A byte of G lies below G_HARNESS_HI, far below the shadow band and the allocation ceiling. *)
Lemma srxk_G_low : forall a, inG TG.G_HARNESS a -> TG.G_HARNESS_LO <= a < TG.G_HARNESS_HI.
Proof. intros a Ha. exact (inG_G_HARNESS_hull a Ha). Qed.

(* The realigned sp (`addi sp, sp, -160`, `andi sp, sp, -32`) from a 16-aligned entry sp. *)
Lemma srxk_sp1 : forall sp, sp mod 16 = 0 ->
  sp - 176 <= 32 * ((sp - SRX_FRAME) / 32) <= sp - 160 /\ (32 * ((sp - SRX_FRAME) / 32)) mod 32 = 0.
Proof.
intros sp H16. unfold SRX_FRAME.
pose proof (Z.div_mod (sp - 160) 32 ltac:(lia)) as D. pose proof (Z.mod_pos_bound (sp - 160) 32 ltac:(lia)) as M.
pose proof (Z.div_mod sp 16 ltac:(lia)) as D16. rewrite H16, Z.add_0_r in D16.
split; [lia|]. rewrite Z.mul_comm. apply Z_mod_mult.
Qed.

(* A run of the walk's own code that writes no byte: the view is the one before it, presence has only grown. *)
Lemma srxk_kept_run : forall (W : world tfibsegs) E (rs : smem) (m m' : word -> option byte),
  frame_of E rs (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
  (forall x, ~ in_wrange E rs x) ->
  mem_grows (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
  (forall a, aview tfibsegs (w_H W) m' a = aview tfibsegs (w_H W) m a) /\
  (forall a, apresent (w_H W) m a -> apresent (w_H W) m' a).
Proof.
intros W E rs m m' HFr Hw HG. split.
- intros a. rewrite (aview_wrap64 tfibsegs _ m' a), (aview_wrap64 tfibsegs _ m a).
  pose proof (Z.mod_pos_bound a (2 ^ 64) ltac:(lia)) as Ha.
  exact (can_aview_kept_frame E rs (w_H W) m m' 0 HFr ltac:(lia) ltac:(intros x Hx; exact (Hw x))
           (a mod 2 ^ 64) ltac:(lia)).
- intros a Ha. exact (apresent_grows _ _ _ a HG Ha).
Qed.

(* `addi r, base, c`, `srli q, r, 3`, `add q, q, shb`: the shadow byte's address of a field. *)
Lemma srxk_denot_shadow : forall E n m v c SHB,
  ew E n = Z_to_bv 64 v -> ew E m = Z_to_bv 64 SHB ->
  0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 -> 0 <= SHB -> SHB + (v + c) / 8 < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff n c) (SLit 3)) (SOff m 0)) = Z_to_bv 64 (SHB + (v + c) / 8).
Proof.
intros E n m v c SHB Hn Hm Hv Hvc HS1 HS2.
assert (HD : 0 <= (v + c) / 8) by (apply Z.div_pos; lia).
assert (Un : U E (SOff n c) = v + c)
  by (rewrite (U_atom_off E n v c Hn) by lia; reflexivity).
assert (Um : U E (SOff m 0) = SHB)
  by (rewrite U_SOff, Hm, (unsigned_lit_small SHB ltac:(lia)), Z.add_0_r; apply zcanon_id; unfold M64; lia).
rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
rewrite Un, Um, U_SLit, (zcanon_id 3) by (unfold M64; lia).
change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
rewrite (zcanon_id ((v + c) / 8)) by (unfold M64; lia).
rewrite (Z.add_comm ((v + c) / 8) SHB). apply zcanon_id. unfold M64. lia.
Qed.

Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).

(* What srx_fix gives the pieces: AR at the call state, the call's stack window (above the allocation ceiling), the
   realigned sp and the class-1 frame. *)
Lemma srxk_fix : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b TF Bw Bw' pos sp1 F,
  srx_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b TF Bw Bw' pos sp1 F ->
  AR segs B lyc Sc W memc mdc /\ YM05.alloc_ceiling <= sp0 - STK /\ sp0 - STK <= spZ regs - SRX_STK /\
  spZ regs <= sp0 /\ sp0 mod 16 = 0 /\ sp0 <= 2 ^ 47 /\ spZ regs mod 16 = 0 /\
  spZ regs - 176 <= sp1 <= spZ regs - 160 /\ sp1 mod 32 = 0 /\
  4096 <= F /\ F mod 64 = 0 /\ F + SRX_FBYTES <= YM05.alloc_ceiling /\ F = frame_addr lyc SRX_CID pos.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b TF Bw Bw' pos sp1 F HF.
destruct HF as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & Hsp16 & Hlo & Hhi & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
  & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsp1 & HFe & HF4 & HF64 & HFc & _).
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
pose proof HJ as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
destruct (srxk_sp1 (spZ regs) Hsp16) as [S1 S2]. rewrite <- Hsp1 in S1, S2.
split; [exact HAR|]. repeat (split; [lia|]). exact HFe.
Qed.

(* One step that changes only bytes of the call's window or written bytes of G keeps acall_kept_g. *)
Lemma srxk_kept_step : forall lyc Sc (W : world segs) memc mdc (W2 : world segs) mem2 mem3 slo shi (E Zs : Z -> Prop),
  AR_laws segs B -> gx_ok segs B TG.G_HARNESS -> AR segs B lyc Sc W memc mdc ->
  YM05.alloc_ceiling <= slo -> shi <= 2 ^ 64 ->
  (forall a, Zs a -> (slo <= a < shi) \/ (E a /\ inG TG.G_HARNESS a)) ->
  acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W2 mem2 slo shi E ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview segs (w_H W2) mem3 a = aview segs (w_H W2) mem2 a) ->
  (forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) mem3 a) ->
  acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W2 mem3 slo shi E.
Proof.
intros lyc Sc W memc mdc W2 mem2 mem3 slo shi E Zs LAWS HGX HAR Hce Hshi HZ (K1 & K2 & K3 & K4 & K5 & K6) Hkp Hgr.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (GL : forall a, inG TG.G_HARNESS a -> 0 <= a < kLowMemEnd)
  by (intros a Ha; exact (inG_low segs B transport_segs_low TG.G_HARNESS a HGX Ha)).
split; [|split; [|split; [|split; [|split]]]].
- intros a Ha Hw. rewrite Hkp; [exact (K1 a Ha Hw) | lia |].
  intros HZa. destruct (HZ a HZa) as [X | (_ & X)]; [exact (Hw X)|]. pose proof (GL a X). unfold kLowMemEnd in *. lia.
- intros b m i Hb Hi Hn. destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hb) as (_ & H4096 & Hbc & _).
  rewrite Hkp; [exact (K2 b m i Hb Hi Hn) | lia |].
  intros HZa. destruct (HZ _ HZa) as [X | (X & _)]; [lia | exact (Hn X)].
- intros a Hi HnG Hno He. pose proof (transport_segs_low a Hi) as Hl. unfold kLowMemEnd in Hl.
  rewrite Hkp; [exact (K3 a Hi HnG Hno He) | lia |].
  intros HZa. destruct (HZ a HZa) as [X | (_ & X)]; [lia | exact (HnG X)].
- intros cid pos a Hin Hr Hn. destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (F4096 & Fce & _).
  pose proof (fs_frame_bytes_nonneg cid) as Hfs.
  assert (Ha : 0 <= a < YM05.alloc_ceiling).
  { destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [lia|].
    pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hfs) as Hse.
    assert (Hd : (frame_addr lyc cid pos + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
    pose proof (Z.div_pos (frame_addr lyc cid pos) 8 ltac:(lia) ltac:(lia)).
    unfold shadow_addr, SHADOW_OFF in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia. }
  rewrite Hkp; [exact (K4 cid pos a Hin Hr Hn) | lia |].
  intros HZa. destruct (HZ a HZa) as [X | (X & _)]; [lia | exact (Hn X)].
- intros a Ha Hw Hp. apply Hgr. exact (K5 a Ha Hw Hp).
- intros a Ha. apply Hgr. exact (K6 a Ha).
Qed.

(* decode_rd_ok at a memory where the range stays visible and the shadow band is unchanged. *)
Lemma srxk_rd_ok_vis : forall (W2 : world segs) mem2 mem3 q n,
  decode_rd_ok W2 mem2 q n ->
  (forall a, q <= a < q + n -> aview segs (w_H W2) mem3 a <> None) ->
  (forall s, kLowMemEnd <= s < kHighShadowEnd -> aview segs (w_H W2) mem3 s = aview segs (w_H W2) mem2 s) ->
  decode_rd_ok W2 mem3 q n.
Proof.
intros W2 mem2 mem3 q n (R1 & R2 & R3 & R4 & R5 & R6) K1 K2.
assert (Hq : q + n <= kHighMemEnd - 1) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia).
unfold kHighMemEnd in Hq.
split; [exact K1|]. split; [|split; [|exact (conj R4 (conj R5 R6))]].
- intros x Hx. destruct (R2 x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
  rewrite K2; [exact Hs|]. unfold shadow_of_addr, kLowMemEnd, kHighShadowEnd, SHADOW_OFF.
  pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.mod_pos_bound x 8 ltac:(lia)). lia.
- intros s Hs. rewrite K2; [exact (R3 s Hs)|]. unfold shadow_addr, SHADOW_OFF in Hs.
  unfold kLowMemEnd, kHighShadowEnd.
  pose proof (Z.div_mod q 8 ltac:(lia)). pose proof (Z.mod_pos_bound q 8 ltac:(lia)).
  pose proof (Z.div_mod (q + n - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (q + n - 1) 8 ltac:(lia)).
  pose proof (Z.div_mod (2147450880 + q / 8) 8 ltac:(lia)).
  pose proof (Z.mod_pos_bound (2147450880 + q / 8) 8 ltac:(lia)).
  pose proof (Z.div_mod (2147450880 + (q + n - 1) / 8) 8 ltac:(lia)).
  pose proof (Z.mod_pos_bound (2147450880 + (q + n - 1) / 8) 8 ltac:(lia)). lia.
Qed.

(* trans_src_ok at such a memory: the placements read no memory. *)
Lemma srxk_src_ok_vis : forall ly2 S2 (W2 : world segs) mem2 mem3 q n,
  trans_src_ok B ly2 S2 W2 mem2 q n ->
  (forall a, q <= a < q + n -> aview segs (w_H W2) mem2 a <> None -> aview segs (w_H W2) mem3 a <> None) ->
  (forall s, kLowMemEnd <= s < kHighShadowEnd -> aview segs (w_H W2) mem3 s = aview segs (w_H W2) mem2 s) ->
  trans_src_ok B ly2 S2 W2 mem3 q n.
Proof.
intros ly2 S2 W2 mem2 mem3 q n [Hb | (HL & Hrd)] K1 K2; [left; exact Hb|].
right. split; [exact HL|]. apply (srxk_rd_ok_vis W2 mem2 mem3 q n Hrd); [|exact K2].
intros a Ha. apply K1; [exact Ha|]. exact (proj1 Hrd a Ha).
Qed.

(* A garr8 array of the view, at a memory with the same view on its range. *)
Lemma srxk_garr8 : forall (W : world segs) memc m q l,
  garr8 segs (mrestrict (w_H W) memc) q l ->
  (forall a, q <= a < q + Z.of_nat (length l) -> aview segs (w_H W) m a = aview segs (w_H W) memc a) ->
  garr8 segs (mrestrict (w_H W) m) q l.
Proof.
intros W memc m q l HG HV. apply (garr8_frame segs (mrestrict (w_H W) memc) (mrestrict (w_H W) m) q l HG).
intros a Ha. apply (mbyte_of_aview segs). exact (HV a Ha).
Qed.

(* The frame's 64 bytes, once diginet_frame_parse answered 0: the cells of lib/Prog/diginet_frame_parse_c.v
   parse_cells, whose widths add to 64 when the frame bytes are at least a header (fr_code b = 0) and fj are 64. *)
Lemma srxk_code0_len : forall b, DSpec.fr_code b = 0 -> (30 <= length b)%nat.
Proof.
intros b H. unfold DSpec.fr_code in H.
destruct ((length b <? 30)%nat) eqn:E; [discriminate H | apply Nat.ltb_ge in E; exact E].
Qed.

Lemma srxk_fbytes_len : forall buf b fj, DSpec.fr_code b = 0 -> length fj = 64%nat ->
  length (frame_f_bytes buf b fj) = 64%nat.
Proof.
intros buf b fj H0 Hfj. pose proof (srxk_code0_len b H0) as Hb.
assert (HW : LC.cells_wf (PParse.parse_cells buf b fj)).
{ cbn [PParse.parse_cells LC.cells_wf LC.cell_wf].
  unfold DSpec.fr_dst, DSpec.fr_src.
  repeat split; rewrite ?length_firstn, ?length_skipn; lia. }
unfold frame_f_bytes, frame_f_cells.
rewrite (proj2 (Z.eqb_eq (DSpec.fr_code b) 0) H0), length_map.
rewrite (LC.cells_bytes_length _ HW). reflexivity.
Qed.

(* Every fact a cut of this part of the walk carries, at a memory that differs from the cut's only in the bytes Zs:
   the callees' stack windows below the realigned sp and the slot sp1 + 24 (the own machine frame), and bytes of G
   the call writes. The ranges the facts name by value (the bytes b at buf, the heap frame TF, the own frame's 128
   bytes) lie outside both sets; the OW.dn body range of srx_ndata may be a range of G, so its placement is carried
   by visibility alone (a byte of G is visible at every memory: TransportGCg.v gx_rw_vis). *)
Lemma srxk_move : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b fj TF Bw Bw'
    pos sp1 F ly2 S2 (W2 : world segs) mem2 md2 e mem3 md3 (Zs : Z -> Prop),
  srx_laws B MT ->
  srx_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b TF Bw Bw' pos sp1 F ->
  srx_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b pos F ly2 S2 W2 mem2 md2 e ->
  srx_rd B ly2 S2 W2 mem2 regs buf b TF Bw ->
  decode_rd_ok W2 mem2 (F + SRX_F) FRAME_F_SIZE ->
  srx_fbytes W2 mem2 F buf b fj ->
  DSpec.fr_code b = 0 ->
  ajournal_gx TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 ((SRX_CID, pos) :: own) ly2 S2 W2 mem3 md3 (k + e) ->
  (forall a, Zs a -> (sp1 - 2 * ESTACK <= a < sp1 + 32) \/ (srx_wr b a /\ inG TG.G_HARNESS a)) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview segs (w_H W2) mem3 a = aview segs (w_H W2) mem2 a) ->
  (forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) mem3 a) ->
  srx_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b pos F ly2 S2 W2 mem3 md3 e /\
  srx_rd B ly2 S2 W2 mem3 regs buf b TF Bw /\
  decode_rd_ok W2 mem3 (F + SRX_F) FRAME_F_SIZE /\
  srx_fbytes W2 mem3 F buf b fj.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b fj TF Bw Bw' pos sp1 F
  ly2 S2 W2 mem2 md2 e mem3 md3 Zs HLAWS HFIX HCUR HRD HRDF HFB H0 HJ3 HZ KV GR.
destruct HLAWS as (HPCS & HCELLS & HSC & HROU & HRNE & HROR & HRON & LAWS & MTL & MTF & SMP & ASF & FFL & HGX & HGNE).
destruct (srxk_fix STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs buf now r b TF Bw Bw' pos sp1 F HFIX)
  as (HAR & Hce0 & Hlo & Hhi & Hsp0a & H47 & Hsp16 & (Hs1a & Hs1b) & Hs1m & HF4 & HF64 & HFc & HFe).
pose proof (@YM05.alloc_ceiling_val rc) as [CEIL1 CEIL2].
assert (Hes : ESTACK = 4096) by reflexivity.
assert (Hstk : SRX_STK = 9168) by reflexivity.
assert (Hfbs : SRX_FBYTES = 128) by reflexivity.
assert (Hsf : SRX_F = 32) by reflexivity.
assert (Hffs : FRAME_F_SIZE = 64) by reflexivity.
pose proof HCUR as (HJ2 & He & Hfrs & Hperm & HlyF & HMO & HK & HSV & HFL).
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HAR2.
assert (Hin2 : In (SRX_CID, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
assert (HFa2 : frame_addr ly2 SRX_CID pos = F) by (rewrite HFe; unfold frame_addr; rewrite HlyF; reflexivity).
assert (Hfs1 : fs_frame_bytes SRX_CID = SRX_FBYTES) by exact srx_fbytes_eq.
(* the bytes of G and the window, in the memory map *)
assert (GL : forall a, inG TG.G_HARNESS a -> 0 <= a < kLowMemEnd)
  by (intros a Ha; exact (inG_low segs B transport_segs_low TG.G_HARNESS a HGX Ha)).
assert (OUT : forall a, ~ (sp1 - 2 * ESTACK <= a < sp1 + 32) -> ~ inG TG.G_HARNESS a -> ~ Zs a).
{ intros a H1 H2 HZa. destruct (HZ a HZa) as [X | (_ & X)]; [exact (H1 X) | exact (H2 X)]. }
assert (NGF : forall a, F <= a < F + SRX_FBYTES -> ~ inG TG.G_HARNESS a).
{ intros a Ha Hg. destruct (HGX a Hg) as [Hi _].
  refine (frm_img segs B LAWS ly2 S2 W2 mem2 md2 SRX_CID pos a HAR2 Hin2 _ Hi).
  rewrite HFa2, Hfs1. exact Ha. }
(* the shadow band and the frame are outside the bytes Zs *)
assert (KSH : forall s, kLowMemEnd <= s < kHighShadowEnd -> aview segs (w_H W2) mem3 s = aview segs (w_H W2) mem2 s).
{ intros s Hs. unfold kLowMemEnd, kHighShadowEnd in Hs. apply KV; [lia|].
  apply OUT; [lia | intros Hg; pose proof (GL s Hg); unfold kLowMemEnd in *; lia]. }
assert (KFR : forall a, F <= a < F + SRX_FBYTES -> aview segs (w_H W2) mem3 a = aview segs (w_H W2) mem2 a).
{ intros a Ha. apply KV; [lia|]. apply OUT; [lia | exact (NGF a Ha)]. }
(* a range outside the call's window and outside G is kept *)
assert (KOFF : forall q n a, (q + n <= spZ regs - SRX_STK \/ spZ regs <= q) ->
  (forall x, q <= x < q + n -> ~ inG TG.G_HARNESS x) -> 0 <= q -> q + n <= 2 ^ 47 ->
  q <= a < q + n -> aview segs (w_H W2) mem3 a = aview segs (w_H W2) mem2 a).
{ intros q n a Hoff Hng Hq0 Hqn Ha. apply KV; [lia|].
  apply OUT; [destruct Hoff as [Ho | Ho]; lia | exact (Hng a Ha)]. }
pose proof HRD as (HG & HS & HT & HRO & HND).
pose proof HFIX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hbuf0 & _ & _ & Hoffb & Hoffg & _ & _ & _ & _
  & Htfg & _).
(* the bytes b at buf: outside G (srx_buf_off_g) and outside the call's window (decode_off_win) *)
assert (BUFB : forall a, buf <= a < buf + Z.of_nat (length b) -> aview segs (w_H W2) mem3 a = aview segs (w_H W2) mem2 a).
{ intros a Ha.
  destruct (Z.eq_dec (Z.of_nat (length b)) 0) as [Hz | Hz]; [exfalso; lia|].
  destruct (trans_src_ok_place B LAWS ly2 S2 W2 mem2 md2 buf (Z.of_nat (length b)) HAR2 HS ltac:(lia))
    as [(P1 & P2) | (P1 & P2 & P3 & P4)];
  (apply (KOFF buf (Z.of_nat (length b)) a); [exact Hoffb | intros x Hx; exact (Hoffg x Hx) | lia | lia | exact Ha]). }
assert (RDSRC : trans_src_ok B ly2 S2 W2 mem3 buf (Z.of_nat (length b)))
  by exact (trans_src_ok_view B ly2 S2 W2 W2 mem2 mem3 buf (Z.of_nat (length b)) HS BUFB KSH).
assert (RDG : garr8 segs (mrestrict (w_H W2) mem3) buf (TW.zs b)).
{ apply (srxk_garr8 W2 mem2 mem3 buf (TW.zs b) HG).
  intros a Ha. apply BUFB. unfold TW.zs in Ha. rewrite length_map in Ha. exact Ha. }
(* the heap frame TF: outside G (trans_tf_off_g) and outside the window (its decode_off_win) *)
assert (RDTF : trans_tframe_at B ly2 S2 W2 mem3 regs SRX_STK TF).
{ destruct TF as [fr|]; [|exact I].
  destruct HT as (T0 & TG8 & TS8 & TW8).
  assert (TB : forall a, TI.tf_addr fr <= a < TI.tf_addr fr + Z.of_nat (length (TI.tf_bytes fr)) ->
    aview segs (w_H W2) mem3 a = aview segs (w_H W2) mem2 a).
  { intros a Ha.
    destruct (Z.eq_dec (Z.of_nat (length (TI.tf_bytes fr))) 0) as [Hz | Hz]; [exfalso; lia|].
    destruct (trans_src_ok_place B LAWS ly2 S2 W2 mem2 md2 (TI.tf_addr fr) (Z.of_nat (length (TI.tf_bytes fr)))
      HAR2 TS8 ltac:(lia)) as [(P1 & P2) | (P1 & P2 & P3 & P4)];
    (apply (KOFF (TI.tf_addr fr) (Z.of_nat (length (TI.tf_bytes fr))) a);
      [exact TW8 | intros x Hx; exact (Htfg fr eq_refl x Hx) | lia | lia | exact Ha]). }
  split; [exact T0|]. split.
  - apply (srxk_garr8 W2 mem2 mem3 _ _ TG8). intros a Ha. apply TB. rewrite length_map in Ha. exact Ha.
  - split; [exact (trans_src_ok_view B ly2 S2 W2 W2 mem2 mem3 _ _ TS8 TB KSH) | exact TW8]. }
(* the read-only bytes lie below G and far below the call's window *)
assert (RDRO : trans_rom_view_rd W2 mem3).
{ intros a Ha. pose proof (trans_ro_rd_bounds a Ha) as Hb.
  rewrite KV; [exact (HRO a Ha) | lia|].
  apply OUT; [lia|]. intros Hg. pose proof (srxk_G_low a Hg) as Hgb.
  unfold TG.G_HARNESS_LO in Hgb. lia. }
(* the OW.dn body range: outside the call's window by its own decode_off_win, so a byte of it that Zs changes is a
   byte of G, which is visible at every memory *)
assert (RDND : srx_ndata B ly2 S2 W2 mem3 regs Bw b).
{ intros Hc Hcmd Hmac Hk Hq Hst Hdup Hka.
  destruct (HND Hc Hcmd Hmac Hk Hq Hst Hdup Hka) as [HO1 HO2]. split; [|exact HO2].
  pose proof HO2 as HO2'. unfold decode_off_win in HO2'.
  apply (srxk_src_ok_vis ly2 S2 W2 mem2 mem3 _ _ HO1); [|exact KSH].
  intros a Ha Hv. destruct (inGb TG.G_HARNESS a) eqn:Eg.
  - exact (gx_rw_vis segs TG.G_HARNESS a G_HARNESS_rw (proj1 (inGb_spec _ _) Eg) (w_H W2) mem3).
  - destruct (trans_src_ok_place B LAWS ly2 S2 W2 mem2 md2 _ _ HAR2 HO1 ltac:(lia))
      as [(P1 & P2) | (P1 & P2 & P3 & P4)];
    (rewrite (KV a ltac:(lia)
       (OUT a ltac:(destruct HO2' as [HO | HO]; lia) (proj1 (inGb_false _ _) Eg))); exact Hv). }
(* f's 64 bytes and their values *)
assert (RDF : decode_rd_ok W2 mem3 (F + SRX_F) FRAME_F_SIZE)
  by (apply (trans_rd_ok_view W2 W2 mem2 mem3 _ _ HRDF); [intros a Ha; apply KFR; lia | exact KSH]).
assert (RFB : srx_fbytes W2 mem3 F buf b fj).
{ destruct HFB as (Hfj & HFG). split; [exact Hfj|].
  apply (srxk_garr8 W2 mem2 mem3 _ _ HFG). intros a Ha.
  rewrite (srxk_fbytes_len buf b fj H0 Hfj) in Ha. apply KFR. lia. }
(* what the call keeps, and the words the cut reads back *)
assert (KG : acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W2 mem3 (spZ regs - SRX_STK) (spZ regs) (srx_wr b)).
{ assert (HZ' : forall a, Zs a -> (spZ regs - SRX_STK <= a < spZ regs) \/ (srx_wr b a /\ inG TG.G_HARNESS a)).
  { intros a HZa. destruct (HZ a HZa) as [X | X]; [left; lia | right; exact X]. }
  exact (srxk_kept_step lyc Sc W memc mdc W2 mem2 mem3 (spZ regs - SRX_STK) (spZ regs) (srx_wr b) Zs
    LAWS HGX HAR ltac:(lia) ltac:(lia) HZ' HK KV GR). }
assert (SV3 : Forall (fun o : Z * Z => rdword (aview segs (w_H W2) mem3) (spZ regs - fst o) =
    Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) SRX_SAVED).
{ apply Forall_forall. intros o Hin.
  assert (Ho : 8 <= fst o <= 104).
  { unfold SRX_SAVED in Hin. cbn [In] in Hin.
    repeat (destruct Hin as [Hin | Hin]; [subst o; cbn [fst]; lia |]). destruct Hin. }
  rewrite (rdword_ext _ _ _ (fun kk Hk => KV (spZ regs - fst o + kk) ltac:(lia)
    ltac:(apply OUT; [lia | intros Hg; pose proof (GL _ Hg); unfold kLowMemEnd in *; lia]))).
  exact (proj1 (Forall_forall _ _) HSV o Hin). }
assert (FL3 : rdword (aview segs (w_H W2) mem3) (F + SRX_FBYTES - 8) = Some (flag_addr lyc SRX_CID pos)).
{ rewrite (rdword_ext _ _ _ (fun kk Hk => KFR (F + SRX_FBYTES - 8 + kk) ltac:(lia))). exact HFL. }
split; [|split; [|split; [exact RDF | exact RFB]]].
- refine (conj HJ3 (conj He (conj Hfrs (conj Hperm (conj HlyF (conj HMO (conj KG (conj SV3 FL3)))))))).
- exact (conj RDG (conj RDSRC (conj RDTF (conj RDRO RDND)))).
Qed.

(* g_s's payload is addressable at every AR state: whole granules of the record's zero shadow (trans_srx_cells). *)
Lemma srxk_gs_ra : forall ly S (W : world segs) mem md q n,
  trans_srx_cells B -> AR segs B ly S W mem md -> SRX_S <= q -> q + n <= SRX_S + TW.SZ_g_s ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF q n.
Proof.
intros ly S W mem md q n HZ HAR Hq1 Hq2 x Hx.
exists 0. split; [|left; reflexivity].
pose proof (Z.div_mod x 8 ltac:(lia)) as D8. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as M8.
assert (HL : SRX_S / 8 <= x / 8) by (apply Z.div_le_mono; lia).
assert (HU : x / 8 <= (SRX_S + TW.SZ_g_s - 1) / 8) by (apply Z.div_le_mono; lia).
assert (HE1 : 8 * (SRX_S / 8) = SRX_S) by (vm_compute; reflexivity).
assert (HE2 : 8 * ((SRX_S + TW.SZ_g_s - 1) / 8) = SRX_S + TW.SZ_g_s - 8) by (vm_compute; reflexivity).
assert (Hz := decode_zshadow_rd B ly S W mem md SRX_S (SRX_S + TW.SZ_g_s) (8 * (x / 8)) HAR
  ltac:(rewrite Z.mul_comm; apply Z_mod_mult) ltac:(lia) ltac:(lia) (proj1 HZ)).
unfold shadow_of_addr.
replace (SHADOW_OFF + x / 8) with (ACells.shadow_addr (8 * (x / 8))); [exact Hz|].
unfold ACells.shadow_addr, ACells.ASAN_K, SHADOW_OFF. rewrite Z.mul_comm, Z.div_mul by lia. lia.
Qed.

(* The bytes of the frame the code reads: the source MAC at f + 6 (cell 6 of parse_cells) and h.cmd at f + 30. *)
Lemma srxk_fsrc : forall buf b fj i, DSpec.fr_code b = 0 -> (i < 6)%nat ->
  nth (6 + i) (frame_f_bytes buf b fj) 0 = DSpec.at8 (DSpec.fr_src b) i.
Proof.
intros buf b fj i H0 Hi. pose proof (srxk_code0_len b H0) as Hb.
assert (Hd : length (DSpec.fr_dst b) = 6%nat)
  by (unfold DSpec.fr_dst; rewrite length_firstn; lia).
unfold frame_f_bytes, frame_f_cells. rewrite (proj2 (Z.eqb_eq (DSpec.fr_code b) 0) H0).
cbn [PParse.parse_cells LC.cells_bytes LC.cbytes].
rewrite map_app, app_nth2; rewrite length_map, Hd; [|lia].
replace (6 + i - 6)%nat with i by lia.
rewrite map_app, app_nth1;
  [|rewrite length_map; unfold DSpec.fr_src; rewrite length_firstn, length_skipn; lia].
unfold DSpec.at8, DSpec.bz.
change 0 with (bv_unsigned (DSpec.b8 0)) at 1.
apply (map_nth (fun x : byte => bv_unsigned x) (DSpec.fr_src b) (DSpec.b8 0) i).
Qed.

Lemma srxk_fcmd : forall buf b fj, DSpec.fr_code b = 0 -> length fj = 64%nat ->
  nth 30 (frame_f_bytes buf b fj) 0 = DSpec.fr_cmd b.
Proof.
intros buf b fj H0 Hfj. pose proof (srxk_code0_len b H0) as Hb.
assert (Hd : length (DSpec.fr_dst b) = 6%nat) by (unfold DSpec.fr_dst; rewrite length_firstn; lia).
assert (Hs : length (DSpec.fr_src b) = 6%nat)
  by (unfold DSpec.fr_src; rewrite length_firstn, length_skipn; lia).
assert (Hj : length (firstn 2 (skipn 14 fj)) = 2%nat) by (rewrite length_firstn, length_skipn; lia).
unfold frame_f_bytes, frame_f_cells. rewrite (proj2 (Z.eqb_eq (DSpec.fr_code b) 0) H0).
cbn [PParse.parse_cells LC.cells_bytes LC.cbytes].
rewrite !map_app.
rewrite app_nth2; rewrite !length_map, ?Hd; [|lia]. replace (30 - 6)%nat with 24%nat by lia.
rewrite app_nth2; rewrite !length_map, ?Hs; [|lia]. replace (24 - 6)%nat with 18%nat by lia.
rewrite app_nth2; rewrite !length_map, ?LMem.length_le2; [|lia]. replace (18 - 2)%nat with 16%nat by lia.
rewrite app_nth2; rewrite !length_map, ?Hj; [|lia]. replace (16 - 2)%nat with 14%nat by lia.
rewrite app_nth2; rewrite !length_map, ?LMem.length_le2; [|lia]. replace (14 - 2)%nat with 12%nat by lia.
rewrite app_nth2; rewrite !length_map, ?LMem.length_le2; [|lia]. replace (12 - 2)%nat with 10%nat by lia.
rewrite app_nth2; rewrite !length_map, ?LMem.length_le4; [|lia]. replace (10 - 4)%nat with 6%nat by lia.
rewrite app_nth2; rewrite !length_map, ?LMem.length_le4; [|lia]. replace (6 - 4)%nat with 2%nat by lia.
rewrite app_nth2; rewrite !length_map, ?LMem.length_le2; [|lia]. replace (2 - 2)%nat with 0%nat by lia.
cbn [map app nth]. unfold DSpec.b8, DSpec.bz.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
pose proof (DSpec.at8_range b 28) as Hr. unfold DSpec.fr_cmd. apply Z.mod_small. exact Hr.
Qed.

(* The six bytes of g_s.desk_mac, as the world holds them. *)
Lemma srxk_desk_mac_byte : forall Bw i, length Bw = Z.to_nat TW.W_LEN -> (i < 6)%nat ->
  DSpec.at8 (TW.S_desk_mac Bw) i = bv_unsigned (nth (Z.to_nat (TW.OFF_g_s + 120 + Z.of_nat i)) Bw (Z_to_bv 8 0)).
Proof.
intros Bw i HL Hi. unfold DSpec.at8, DSpec.bz, TW.S_desk_mac, TW.A_S_desk_mac.
rewrite (tw_nth_sub Bw (TW.OFF_g_s + 120) 6 i (DSpec.b8 0));
  [| unfold TW.OFF_g_s; lia | exact Hi | rewrite HL; unfold TW.OFF_g_s, TW.W_LEN; lia].
rewrite (nth_indep Bw (DSpec.b8 0) (Z_to_bv 8 0));
  [| rewrite HL; unfold TW.OFF_g_s, TW.W_LEN; lia].
f_equal. f_equal. unfold TW.OFF_g_s. lia.
Qed.

(* A byte of g_s, read through the world relation. *)
Lemma srxk_gs_byte : forall (rd : Z -> option Z) Bw i, tw_at TMAP_A rd Bw -> 0 <= i < TW.SZ_g_s ->
  rd (SRX_S + i) = Some (bv_unsigned (nth (Z.to_nat (TW.OFF_g_s + i)) Bw (Z_to_bv 8 0))).
Proof.
intros rd Bw i Htw Hi. destruct Htw as [_ Hrd].
exact (Hrd TW.OFF_g_s TA_g_s TW.SZ_g_s i TMAP_A_g_s Hi).
Qed.

(* A byte of a garr8 array, read through the view. *)
Lemma srxk_view_garr8 : forall (W : world segs) mem q (l : list Z) j,
  garr8 segs (mrestrict (w_H W) mem) q l -> (j < length l)%nat ->
  aview segs (w_H W) mem (q + Z.of_nat j) = Some (nth j l 0).
Proof.
intros W mem q l j HG Hj.
pose proof (garr8_mbyte segs (mrestrict (w_H W) mem) q l j HG Hj) as Hm.
destruct (HG j Hj) as [_ Hr].
unfold aview. rewrite Hm. cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. exact Hr.
Qed.

Lemma srxk_memeq6 : forall x y, TS0.memeq 6 x y = true <-> (forall i, (i < 6)%nat -> DSpec.at8 x i = DSpec.at8 y i).
Proof.
intros x y. unfold TS0.memeq. rewrite forallb_forall. split.
- intros H i Hi. apply Z.eqb_eq. apply H. apply in_seq. lia.
- intros H i Hin. apply in_seq in Hin. apply Z.eqb_eq. apply H. lia.
Qed.

(* The bcmp call of :279 against g_s.desk_mac: its ranges agree exactly when the model's memeq holds. *)
Lemma srxk_bcmp_memeq : forall (W2 : world segs) mem2 F buf b fj Bw,
  DSpec.fr_code b = 0 -> srx_fbytes W2 mem2 F buf b fj ->
  tw_at TMAP_A (aview segs (w_H W2) mem2) Bw ->
  ((forall i, 0 <= i < 6 ->
      aview segs (w_H W2) mem2 (F + SRX_F + 6 + i) = aview segs (w_H W2) mem2 (SRX_S + 120 + i))
   <-> TS0.memeq 6 (DSpec.fr_src b) (TW.S_desk_mac Bw) = true).
Proof.
intros W2 mem2 F buf b fj Bw H0 HFB Htw. destruct HFB as (Hfj & HFG).
assert (HLen : length (frame_f_bytes buf b fj) = 64%nat) by exact (srxk_fbytes_len buf b fj H0 Hfj).
assert (HW : length Bw = Z.to_nat TW.W_LEN) by exact (tw_len _ _ _ Htw).
assert (EF : forall i, (i < 6)%nat ->
  aview segs (w_H W2) mem2 (F + SRX_F + 6 + Z.of_nat i) = Some (DSpec.at8 (DSpec.fr_src b) i)).
{ intros i Hi. rewrite <- (srxk_fsrc buf b fj i H0 Hi).
  replace (F + SRX_F + 6 + Z.of_nat i) with (F + SRX_F + Z.of_nat (6 + i)) by lia.
  apply (srxk_view_garr8 W2 mem2 (F + SRX_F) _ (6 + i) HFG). lia. }
assert (EW : forall i, (i < 6)%nat ->
  aview segs (w_H W2) mem2 (SRX_S + 120 + Z.of_nat i) = Some (DSpec.at8 (TW.S_desk_mac Bw) i)).
{ intros i Hi. rewrite (srxk_desk_mac_byte Bw i HW Hi).
  replace (SRX_S + 120 + Z.of_nat i) with (SRX_S + (120 + Z.of_nat i)) by lia.
  rewrite (srxk_gs_byte _ Bw (120 + Z.of_nat i) Htw ltac:(unfold TW.SZ_g_s; lia)).
  do 3 f_equal. unfold TW.OFF_g_s. lia. }
rewrite srxk_memeq6. split.
- intros H i Hi. pose proof (H (Z.of_nat i) ltac:(lia)) as Hi2.
  rewrite (EF i Hi), (EW i Hi) in Hi2.
  exact (f_equal (fun o : option Z => match o with Some z => z | None => 0 end) Hi2).
- intros H i Hi.
  replace i with (Z.of_nat (Z.to_nat i)) by lia.
  rewrite (EF (Z.to_nat i) ltac:(lia)), (EW (Z.to_nat i) ltac:(lia)).
  f_equal. apply H. lia.
Qed.

(* The bcmp wrapper's contract (YG0d.v abcmp_realizes), read at the walk's own G journal through TransportGCg.v
   gx_call_leaf over YCbq.v aj_bcmp_at: the journal and every byte outside the wrapper's own stack window are kept,
   and its result is 0 exactly when the two ranges hold the same bytes. *)
Lemma srxk_bcmp :
  forall (STK sp0 : Z) FP ly S (W0 : world segs) mem0 md0 own lyc Sc (W : world segs)
         (memT : word -> option byte) mdc k (regsT : bvmap 5 word) (x y n o : Z) (raw : word),
  AR_laws segs B ->
  @abcmp_realizes fx rc segs B (transport_sigma TS___interceptor_trampoline_bcmp) ->
  ajournal_gx TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memT mdc k ->
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
    (mkCfg (@YK11.mkst fx regsT (Z_to_bv 64 (transport_sigma TS___interceptor_trampoline_bcmp)) memT
              (YK11.seg_rom segs)) mdc)
    (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
       c2 = mkCfg (@YK11.mkst fx regs2 raw mem2 (YK11.seg_rom segs)) md2 /\
       ajournal_gx TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k /\
       (exists v : word, aregs_preserved regsT regs2 /\ YK11.getr regs2 10 = v /\
          (v = w64 0 <-> forall i, 0 <= i < n ->
             aview segs (w_H W) memT (x + i) = aview segs (w_H W) memT (y + i)) /\
          (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o) ->
             aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
          (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a))).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memT mdc k regsT x y n o raw
  LAWS AM HJ H10 H11 H12 Hn Hx0 Hxn Hy0 Hyn Hsp Hal Hneg Hbud Hgp Htp Hra Hraw
  Hsx Hsy Hbx Hby Hmx Hmy Hrx Hhx Hry Hhy.
apply (@gx_call_leaf fx rc tfib_sink_head segs B TG.G_HARNESS STK sp0 FP ly S W0 mem0 md0 own
         lyc Sc W memT mdc k _ raw _ HJ).
intros memS HJi.
eapply SRr_mono.
{ exact (@aj_bcmp_at fx rc tfib_sink_head segs B LAWS transport_segs_low
           (transport_sigma TS___interceptor_trampoline_bcmp) AM W regsT memT STK sp0 FP ly S W0 memS md0 own
           lyc Sc mdc k x y n o raw HJi H10 H11 H12 Hn Hx0 Hxn Hy0 Hyn Hsp Hal Hneg Hbud Hgp Htp Hra Hraw
           Hsx Hsy Hbx Hby Hmx Hmy Hrx Hhx Hry Hhy). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & Hc & HJ2 & HP & Hres & Hcmp & Hfr2 & Hpres2).
split; [reflexivity|]. exists regs2, mem2, md2. split; [exact Hc|]. split; [exact HJ2|].
exists v. split; [exact HP|]. split; [exact Hres|]. split; [exact Hcmp|]. split; [exact Hfr2 | exact Hpres2].
Qed.

(* The six bytes of the source MAC at f + 6, as a byte array of the view. *)
Lemma srxk_fsrc_garr8 : forall (W2 : world segs) mem2 F buf b fj,
  DSpec.fr_code b = 0 -> srx_fbytes W2 mem2 F buf b fj ->
  garr8 segs (mrestrict (w_H W2) mem2) (F + SRX_F + 6) (map (fun x : byte => bv_unsigned x) (DSpec.fr_src b)).
Proof.
intros W2 mem2 F buf b fj H0 (Hfj & HFG).
assert (Hs6 : length (DSpec.fr_src b) = 6%nat).
{ unfold DSpec.fr_src. rewrite length_firstn, length_skipn. pose proof (srxk_code0_len b H0) as Hb. lia. }
assert (HLen : length (frame_f_bytes buf b fj) = 64%nat) by exact (srxk_fbytes_len buf b fj H0 Hfj).
intros j Hj. rewrite length_map, Hs6 in Hj.
pose proof (HFG (6 + j)%nat ltac:(lia)) as [HV HR].
assert (EN : nth (6 + j) (frame_f_bytes buf b fj) 0 =
  nth j (map (fun x : byte => bv_unsigned x) (DSpec.fr_src b)) 0).
{ rewrite (srxk_fsrc buf b fj j H0 ltac:(lia)). unfold DSpec.at8, DSpec.bz.
  change 0 with (bv_unsigned (DSpec.b8 0)) at 2.
  symmetry. apply (map_nth (fun x : byte => bv_unsigned x) (DSpec.fr_src b) (DSpec.b8 0) j). }
rewrite EN in HV, HR. split; [|exact HR].
replace (F + SRX_F + 6 + Z.of_nat j) with (F + SRX_F + Z.of_nat (6 + j)) by lia. exact HV.
Qed.

(* A read-back value at a memory that keeps its bytes. *)
Lemma srxk_val_mem_move : forall (W : world segs) m m' a (n : nat) v,
  val_mem segs (mrestrict (w_H W) m) a n v ->
  (forall x, a <= x < a + Z.of_nat n -> aview segs (w_H W) m' x = aview segs (w_H W) m x) ->
  val_mem segs (mrestrict (w_H W) m') a n v.
Proof.
intros W m m' a n v HV HK j Hj.
assert (E : mbyte segs (mrestrict (w_H W) m') (a + Z.of_nat j) =
            mbyte segs (mrestrict (w_H W) m) (a + Z.of_nat j))
  by (apply (mbyte_of_aview segs); exact (HK (a + Z.of_nat j) ltac:(lia))).
rewrite E. exact (HV j Hj).
Qed.

End k.

(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac. *)
Ltac srxk_reg HS r v H tac :=
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
Ltac srxk_region HS i HR :=
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
Ltac srxk_in := cbn [In]; repeat (first [left; reflexivity | right]).
(* The awr obligation's regions, computed. *)
Ltac srxk_awr_rs :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
(* A callee-saved register at the machine state of HS, from the equation Q of its value at the run's start. *)
Ltac srxk_kreg HS EE rg r n Q H :=
  lazymatch type of Q with _ = ?v =>
    srxk_reg HS r v H
      ltac:(cbn [sv_denot]; rewrite (EE n r eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Q) end.
