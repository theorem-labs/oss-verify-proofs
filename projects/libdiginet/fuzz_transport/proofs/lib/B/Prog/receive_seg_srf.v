(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, origin/cold/pg-prog), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-10: the walk is reac-repacer/fuzz_uci's check_clamp in image A, in the shape of the released image-A walks proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_entry.v, .../LLVMFuzzerTestOneInput_seg_copy.v and .../LLVMFuzzerTestOneInput_seg_exit_tail.v at origin/ossv/recipes 88154566652a: module paths, listing symbol type, the symbolic states, the cut points and every address and offset are this function's; the fake-frame class is 1, the single intrinsic is __asan_memcpy of 20 bytes, and the result is the caller-journal contract of lib/A/Prog/check_clamp_cg.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths changed; 663 of its 1139 lines of code are new or changed and 8 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths, module names and numbers changed; 1969 of its 2149 lines of code are new or changed and 959 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/diginet_session_wake_seg_head.v, with its module paths and module names changed; 546 of its 625 lines of code are new or changed and 2070 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/receive_seg_mrx.v, with its module paths, module names and numbers changed; 169 of its 243 lines of code are new or changed and 551 lines of the source are left out. *)
(* receive_seg_srf: Lemma recv_srf : recv_srf_stmt (lib/B/Prog/receive_seg_cut.v), the call of spec_read_frame from
   receive's frame in the image-B ASan walk of receive (fuzz_transport.asan-ubsan 0x836a8 = transportb_sigma
   TB_receive). receive makes it twice: the `jal` at +0x0a4 (0x8374c, a1 = n, return address 0x83750) in the rf piece
   and the `jal` at +0x0d0 (0x83778, a1 = got, return address 0x8377c) in the poll piece; each piece runs to the
   `jal` and applies this lemma. No instruction of receive runs here: the state is at the callee's entry
   (transportb_sigma TB_spec_read_frame) with the registers recv_srf_at gives, and the piece is one application of
   the callee contract (lib/B/Prog/spec_read_frame_cg.v transport_spec_read_frame_cg, recv_calls' fourth conjunct)
   by SRr_bind in the caller's G journal (lib/A/W_journalG.v ajournal_gx TG.G_HARNESS_B 0 []) at k + 1 events,
   followed by the continuation at the state the callee returns.

   The contract's instance: b = a, len, fp = spZ regs - RECV_FRAME = spZ regsT (the struct spec_frame: the 80 bytes
   at receive's sp + 0 .. sp + 79), frame = bytes. Its premises and what gives each:
     ret_ok, 4096 <= ra, a0, a1, a2     recv_srf_at's own premises;
     gp, tp                             recv_regs_keep and recv_fix;
     sp mod 16 = 0, the window          spZ regsT = spZ regs - 128 (recv_regs_keep), spZ regs mod 16 = 0 (recv_fix),
                                        sp0 - STK <= spZ regs - RECV_STK with RECV_STK = 128 + ASTACK and
                                        SRF_STK = 48 + ESTACK <= ASTACK;
     0 < a, 0 <= len <= n               recv_cur's 4096 <= a; recv_srf_at's range;
     garr8 of bytes at a                recv_blk;
     trans_src_ok of [a, a + len)       DgnTransportBCg.v decode_in_block: the block (a, max 1 n) is in
                                        ablocks B ly2 S2 (recv_cur's Permutation);
     decode_off_win of [a, a + len)     the block lies below alloc_ceiling (AR_laws' al_blocks), the call's window
                                        above it (the journal's astk_ok);
     [a, a + len) apart from srf_wr fp  the struct lies above alloc_ceiling;
     fp mod 8 = 0                       spZ regs mod 16 = 0;
     transport_twr_ok_g of the struct   TransportGCg.v transport_twr_ok_g_intro: each byte lies in the journal's
                                        window [sp0 - STK, sp0) and at or above the call's sp;
     decode_rd_ok of the struct         present by the journal's window clause; the machine stack's shadow
                                        (DgnTransportBCg.v stack_zshadow_ra); amem_range: high memory;
     decode_off_win, ~ inG              the struct starts at the call's sp; the stack lies above G's hull
                                        (DgnTransportBCg.v inG_G_HARNESS_hull);
     the event bound                    recv_fix's st_nev S + k + RECV_EV <= EV_MAX, RECV_EV = 2, SRF_EV = 0.
   Its post (TransportGCg.v transport_cg_post_out, out cell [(fp, 80)], no event) gives the continuation's facts:
     recv_cur     the journal at k + 1; the frames; the Permutation (the callee's, then recv_cur's); the meter
                  (YC5d.v mo_le_trans: recv_cur's mo_le, then the callee's mo_le ... 0); the kept fact: the callee's
                  acall_kept_g is stated at its call state (ly2, S2) with the written range srf_wr fp, so srf_kept_low
                  first moves it to the caller's call state (lyc, Sc) with no written range (srf_wr fp lies at or
                  above alloc_ceiling, where its block and frame clauses never look: al_blocks, frames_bounds), then
                  TransportGCg.v dk_kept_trans_out_g folds it into recv_cur's (the struct lies in receive's own window
                  [spZ regs - RECV_STK, spZ regs), present at the return by the post's X); the six saved words (entry
                  sp - 48 .. entry sp - 1, above the struct and above the call's window: the callee's first kept
                  clause, with TransportGCg.v gover_out_aview outside the out cell);
     recv_blk     the block's bytes: the callee's block clause (the block lies below alloc_ceiling, so outside
                  srf_wr fp and the out cell);
     tw_at Bm     the post's gx_kept (TWorldB.v tw_kept_GB, TransportGCg.v gx_kept_rows);
     registers    the post's aregs_preserved regsT regs3;
     the struct   the post's X: garr8 of TContract.sf_bytes a (srf_f bytes len) at fp. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import spec_read_frame_cg receive_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import receive_seg_cut.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require TContract.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TCt := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T.TContract.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* Small facts                                                         *)
(* ------------------------------------------------------------------ *)

(* One out cell, read as a range. *)
Lemma srf_inG1 : forall b m x, inG [(b, m)] x -> b <= x < b + m.
Proof.
intros b m x H. apply inG_cons in H as [H | H]; [unfold in_zr in H; cbn [fst snd] in H; exact H|].
exfalso. exact (inG_nil x H).
Qed.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.

(* A byte of a garr8 array is visible. *)
Lemma srf_garr8_vis : forall (Hh : word -> bool) m base (l : list Z) x,
  garr8 segs (mrestrict Hh m) base l -> base <= x < base + Z.of_nat (length l) ->
  aview segs Hh m x <> None.
Proof.
intros Hh m base l x HG Hx.
assert (Hj : (Z.to_nat (x - base) < length l)%nat) by lia.
pose proof (garr8_mbyte segs (mrestrict Hh m) base l (Z.to_nat (x - base)) HG Hj) as Hm.
replace (base + Z.of_nat (Z.to_nat (x - base))) with x in Hm by lia.
unfold aview. rewrite Hm. discriminate.
Qed.

(* A callee's kept fact, stated at its call state (ly2, S2) with a written range E that lies at or above
   alloc_ceiling, is a kept fact at the caller's call state (lyc, Sc) with no written range: its block and frame
   clauses look only at block and frame bytes (and the frames' shadow), which AR puts below alloc_ceiling, and the
   caller's blocks and frames are among the callee's at the same frame addresses. *)
Lemma srf_kept_low : forall (G : list (Z * Z)) lyc Sc ly2 S2 (W2 : world segs) mem2 md2 (W3 : world segs) memY
    slo shi (E : Z -> Prop),
  AR_laws segs B -> AR segs B ly2 S2 W2 mem2 md2 ->
  (forall x, E x -> alloc_ceiling <= x) ->
  (forall cid pos, frame_addr ly2 cid pos = frame_addr lyc cid pos) ->
  (forall f, In f (frames Sc) -> In f (frames S2)) ->
  (forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly2 S2)) ->
  acall_kept_g segs B G ly2 S2 W2 mem2 W3 memY slo shi E ->
  acall_kept_g segs B G lyc Sc W2 mem2 W3 memY slo shi (fun _ => False).
Proof.
intros G lyc Sc ly2 S2 W2 mem2 md2 W3 memY slo shi E LAWS HAR HE Hfa Hfr Hbl (L1 & L2 & L3 & L4 & L5 & L6).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
split; [exact L1|]. split.
- intros b m i Hb Hi _. pose proof (Hbl _ Hb) as Hb2.
  destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 b m HAR Hb2) as (_ & _ & Hce & _).
  apply (L2 b m i Hb2 Hi). intros X. pose proof (HE _ X). lia.
- split; [exact L3|]. split; [|split; [exact L5 | exact L6]].
  intros cid pos x Hin Hr _. pose proof (Hfr _ Hin) as Hin2.
  assert (Hr2 : in_zr x (frame_rng ly2 (cid, pos)) \/
                in_zr x (shadow_addr (frame_addr ly2 cid pos), fs_frame_bytes cid / 8))
    by (unfold frame_rng in *; cbn [fst snd] in *; rewrite Hfa; exact Hr).
  destruct (frames_bounds segs B LAWS ly2 S2 W2 mem2 md2 cid pos HAR Hin2) as (F4096 & Fce & _).
  pose proof (fs_frame_bytes_nonneg cid) as Hfs.
  assert (Hx : x < alloc_ceiling).
  { destruct Hr2 as [Hr2 | Hr2]; unfold in_zr, frame_rng in Hr2; cbn [fst snd] in Hr2; [lia|].
    pose proof (shadow_range_end (frame_addr ly2 cid pos) (fs_frame_bytes cid) Hfs) as Hse.
    assert (Hd : (frame_addr ly2 cid pos + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
    pose proof (Z.div_pos (frame_addr ly2 cid pos) 8 ltac:(lia) ltac:(lia)).
    unfold shadow_addr, SHADOW_OFF in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia. }
  apply (L4 cid pos x Hin2 Hr2). intros X. pose proof (HE _ X). lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The piece                                                           *)
(* ------------------------------------------------------------------ *)

Lemma recv_srf : @recv_srf_stmt fx rc B MT.
Proof.
unfold recv_srf_stmt, recv_srf_at.
intros LAWS0 CALLS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p by_poll pf T bytes Bw ch a
  ly2 S2 W2 mem2 md2 regsT len Bm Q HFIX HCUR HBLK HTW HREGS Hret Hra H10 H11 H12 Hlen HQ.
pose proof LAWS0 as (_ & _ & _ & _ & _ & _ & _ & _ & LAWS & MTL & _ & _).
pose proof CALLS as (_ & _ & _ & SRFC & _).
pose proof HFIX as (HJ0 & _ & _ & Hgp & Htp & _ & _ & _ & _ & _ & Hsp16 & Hwlo & Hwhi & _ & _ & Hn64 & _ & _ & _ &
  _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hnev & _).
pose proof HCUR as (HJ2 & Hfr2 & Hperm2 & Hmo2 & HK2 & Hsaved & Ha4096).
pose proof HREGS as (R2 & R3 & R4 & _).
unfold recv_blk in HBLK.
pose proof (Nat2Z.is_nonneg (length bytes)) as Hn0.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
(* ---- the journal at the caller's call state and at the current state ---- *)
pose proof HJ0 as (_ & _ & (memS0 & HJi0 & _) & _). rewrite !Z.add_0_r in HJi0.
pose proof HJi0 as (HARc & Hlyc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof Hlyc as (_ & _ & _ & _ & _ & ELFc & _).
clear HJi0 memS0.
pose proof HJ2 as (_ & _ & (memS2 & HJi2 & _) & _). rewrite !Z.add_0_r in HJi2.
pose proof HJi2 as (HAR2 & Hly2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
pose proof Hly2 as (_ & _ & _ & _ & _ & ELF2 & _ & _ & _ & Elo2 & Ehi2 & _).
clear HJi2 memS2.
assert (ERS : RECV_STK = 16512) by reflexivity.
assert (EFR : RECV_FRAME = 128) by reflexivity.
assert (ESR : SRF_STK = 4144) by reflexivity.
assert (ESZ : SRF_SIZE = 80) by reflexivity.
assert (EES : ESTACK = 4096) by reflexivity.
assert (HspR : alloc_ceiling + 16512 <= spZ regs) by lia.
assert (HspH : spZ regs <= 2 ^ 47) by lia.
assert (USP : spZ regsT = spZ regs - 128).
{ change (spZ regsT) with (bv_unsigned (YK11.getr regsT 2)). rewrite R2.
  unfold w64. rewrite EFR. apply unsigned_lit_small. lia. }
(* ---- the frame's block (a, max (n, 1)): in the current blocks, below alloc_ceiling ---- *)
assert (Hinb2 : In (a, Z.max 1 (Z.of_nat (length bytes))) (ablocks B ly2 S2))
  by exact (Permutation_in _ (Permutation_sym Hperm2) (in_eq _ _)).
assert (ERQ : req_size (Z.max 1 (Z.of_nat (length bytes))) = Z.max 1 (Z.of_nat (length bytes))).
{ unfold req_size. destruct (Z.max 1 (Z.of_nat (length bytes)) =? 0) eqn:E; [apply Z.eqb_eq in E; lia | reflexivity]. }
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 a _ HAR2 Hinb2) as (_ & _ & Hceila & _).
rewrite ERQ in Hceila.
(* ---- spec_read_frame's premises ---- *)
assert (P3 : YK11.getr regsT 3 = w64 (as_gp B)) by exact (eq_trans R3 Hgp).
assert (P4 : YK11.getr regsT 4 = w64 (as_tp B)) by exact (eq_trans R4 Htp).
assert (PS16 : spZ regsT mod 16 = 0).
{ rewrite USP. replace (spZ regs - 128) with (spZ regs + (-8) * 16) by lia. rewrite Z_mod_plus_full. exact Hsp16. }
assert (PWLO : sp0 - STK <= spZ regsT - SRF_STK) by (rewrite USP; lia).
assert (PWHI : spZ regsT <= sp0) by (rewrite USP; lia).
assert (PA0 : 0 < a) by lia.
assert (PSRC : trans_src_ok B ly2 S2 W2 mem2 a len).
{ unfold trans_src_ok, decode_in_block. left. exists a, (Z.max 1 (Z.of_nat (length bytes))).
  split; [exact Hinb2 | lia]. }
assert (POFF : decode_off_win regsT SRF_STK a len) by (unfold decode_off_win; left; rewrite USP; lia).
assert (PAP : forall x, a <= x < a + len -> ~ srf_wr (spZ regs - RECV_FRAME) x)
  by (intros x Hx; unfold srf_wr; lia).
assert (PAL : (spZ regs - RECV_FRAME) mod 8 = 0).
{ rewrite EFR. replace (spZ regs - 128) with ((spZ regs / 16 * 2 - 16) * 8)
    by (pose proof (Z.div_mod (spZ regs) 16 ltac:(lia)); lia).
  apply Z_mod_mult. }
assert (PTWR : transport_twr_ok_g segs B TG.G_HARNESS_B STK sp0 FP ly S ly2 S2 own W2 mem2 (spZ regsT)
                 (spZ regs - RECV_FRAME) SRF_SIZE).
{ apply (transport_twr_ok_g_intro segs B LAWS TG.G_HARNESS_B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2
    (k + 1) (spZ regsT) (spZ regs - RECV_FRAME) SRF_SIZE HJ2).
  intros x Hx. left. split; [unfold awr_byte; left; lia | rewrite USP; lia]. }
assert (PRD : decode_rd_ok W2 mem2 (spZ regs - RECV_FRAME) SRF_SIZE).
{ destruct (stack_zshadow_ra B ly2 S2 W2 mem2 md2 (spZ regs - RECV_FRAME) SRF_SIZE HAR2
    ltac:(lia) ltac:(lia) ltac:(lia)) as [HRA HHL].
  split; [|split; [exact HRA | split; [exact HHL | split; [|split]]]].
  - intros x Hx. apply aview_some_of_apresent. apply Hpres2. lia.
  - unfold amem_range. right. lia.
  - lia.
  - lia. }
assert (POFF2 : decode_off_win regsT SRF_STK (spZ regs - RECV_FRAME) SRF_SIZE)
  by (unfold decode_off_win; right; rewrite USP; lia).
assert (PNG : forall x, spZ regs - RECV_FRAME <= x < spZ regs - RECV_FRAME + SRF_SIZE -> ~ inG TG.G_HARNESS_B x).
{ intros x Hx Hg. pose proof (inG_G_HARNESS_hull x Hg) as Gh. unfold TG.G_HARNESS_B_HI in Gh. lia. }
assert (PEV : st_nev S + (k + 1) + SRF_EV <= EV_MAX) by (unfold SRF_EV; unfold RECV_EV in Hnev; lia).
(* ---- the call: spec_read_frame in the caller's G journal ---- *)
eapply SRr_bind.
{ exact (SRFC fx STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 (k + 1) regsT a len (spZ regs - RECV_FRAME)
    bytes HJ2 Hret Hra P3 P4 H10 H11 H12 PS16 PWLO PWHI PA0 Hlen HBLK PSRC POFF PAP PAL PTWR PRD POFF2 PNG PEV). }
intros W3 c3 _ HQ3.
unfold transport_srf_post, transport_cg_post_out in HQ3. cbv beta in HQ3.
destruct HQ3 as (ly3 & S3 & regs3 & mem3 & md3 & e & Hc3 & He3 & HJ3 & HP3 & Hfr3 & Hperm3 & HKc & Hmo3 & _ & HSB
  & HGK).
assert (He0 : e = 0) by (unfold SRF_EV in He3; lia). subst e.
rewrite Z.add_0_r in HJ3. subst c3.
(* ---- the struct's bytes are present at the returned memory ---- *)
assert (HPo : forall x, inG [(spZ regs - RECV_FRAME, SRF_SIZE)] x -> apresent (w_H W3) mem3 x).
{ intros x Hx. pose proof (srf_inG1 _ _ _ Hx) as Hr. rewrite ESZ in Hr.
  apply (apresent_of_aview segs (w_H W3) mem3 x ltac:(lia)).
  - intros Him. pose proof (transportb_segs_low x Him). unfold kLowMemEnd in *. lia.
  - apply (srf_garr8_vis (w_H W3) mem3 (spZ regs - RECV_FRAME) _ x HSB).
    unfold TW.zs. rewrite length_map, srf_size_bytes, ESZ. lia. }
(* ---- the callee's kept fact, at the caller's call state, folded into recv_cur's ---- *)
assert (Hfa : forall cid pos, frame_addr ly2 cid pos = frame_addr lyc cid pos)
  by (intros c q; unfold frame_addr; rewrite ELF2, ELFc; reflexivity).
assert (KS : acall_kept_g segs B TG.G_HARNESS_B lyc Sc W2 mem2 W3 (gover [(spZ regs - RECV_FRAME, SRF_SIZE)] mem3 mem2)
               (spZ regsT - SRF_STK) (spZ regsT) (fun _ => False)).
{ apply (srf_kept_low TG.G_HARNESS_B lyc Sc ly2 S2 W2 mem2 md2 W3 _ _ _ (srf_wr (spZ regs - RECV_FRAME)) LAWS HAR2).
  - intros x Hx. unfold srf_wr in Hx. lia.
  - exact Hfa.
  - intros f Hf. rewrite Hfr2. exact Hf.
  - intros bm Hbm. exact (Permutation_in _ (Permutation_sym Hperm2) (in_cons _ _ _ Hbm)).
  - exact HKc. }
assert (K3 : acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W3 mem3 (spZ regs - RECV_STK) (spZ regs)
               (recv_wr bytes)).
{ apply (dk_kept_trans_out_g segs B LAWS transportb_segs_low TG.G_HARNESS_B [(spZ regs - RECV_FRAME, SRF_SIZE)]
    lyc Sc W memc mdc W2 mem2 W3 mem3 (spZ regs - RECV_STK) (spZ regs) (spZ regsT - SRF_STK) (spZ regsT)
    (recv_wr bytes) (fun _ => False) HARc).
  - lia.
  - lia.
  - intros x Hx. pose proof (srf_inG1 _ _ _ Hx) as Hr. rewrite ESZ in Hr. lia.
  - exact HPo.
  - exact HK2.
  - exact KS.
  - rewrite USP. lia.
  - rewrite USP. lia.
  - intros x [] . }
(* ---- the saved words: above the struct and above the call's window ---- *)
assert (KSAV : forall x, spZ regs - 48 <= x < spZ regs -> aview segs (w_H W3) mem3 x = aview segs (w_H W2) mem2 x).
{ intros x Hx.
  assert (Hng : ~ inG [(spZ regs - RECV_FRAME, SRF_SIZE)] x)
    by (intros Hg; pose proof (srf_inG1 _ _ _ Hg) as Hr; rewrite ESZ in Hr; lia).
  refine (eq_trans (eq_sym (gover_out_aview segs _ (w_H W3) mem3 mem2 x ltac:(lia) Hng)) _).
  pose proof HKc as (L1 & _). apply L1; [lia | rewrite USP; lia]. }
assert (HSo : forall o, In o RECV_SAVED -> 8 <= fst o <= 48).
{ intros o Ho. unfold RECV_SAVED in Ho. cbn [In] in Ho.
  repeat (destruct Ho as [<- | Ho]; [cbn [fst]; lia|]). destruct Ho. }
(* ---- the frame's bytes in the block: below alloc_ceiling, outside srf_wr and the out cell ---- *)
assert (KBLK : forall x, a <= x < a + Z.of_nat (length bytes) ->
  aview segs (w_H W3) mem3 x = aview segs (w_H W2) mem2 x).
{ intros x Hx.
  assert (Hng : ~ inG [(spZ regs - RECV_FRAME, SRF_SIZE)] x)
    by (intros Hg; pose proof (srf_inG1 _ _ _ Hg) as Hr; rewrite ESZ in Hr; lia).
  refine (eq_trans (eq_sym (gover_out_aview segs _ (w_H W3) mem3 mem2 x ltac:(lia) Hng)) _).
  pose proof HKc as (_ & L2 & _).
  pose proof (L2 a (Z.max 1 (Z.of_nat (length bytes))) (x - a) Hinb2 ltac:(rewrite ERQ; lia)
    ltac:(unfold srf_wr; lia)) as E2.
  replace (a + (x - a)) with x in E2 by lia. exact E2. }
assert (GARR : garr8 segs (mrestrict (w_H W3) mem3) a (TW.zs bytes)).
{ apply (garr8_frame segs _ _ _ _ HBLK). intros x Hx. unfold TW.zs in Hx. rewrite length_map in Hx.
  apply mbyte_of_aview. exact (KBLK x Hx). }
(* ---- the world relation: G kept ---- *)
assert (HTW3 : tw_at TMAP_B (aview segs (w_H W3) mem3) Bm).
{ apply (tw_kept_GB _ _ _ HTW). intros b m i Hin Hi. exact (gx_kept_rows segs _ _ _ _ _ HGK b m i Hin Hi). }
pose proof (mo_le_trans MT MTL _ _ _ _ _ Hmo2 Hmo3) as M3. rewrite Z.add_0_r in M3.
(* ---- the continuation ---- *)
apply (HQ ly3 S3 W3 mem3 md3 regs3).
- unfold recv_cur.
  split; [exact HJ3|].
  split; [rewrite Hfr3; exact Hfr2|].
  split; [exact (Permutation_trans Hperm3 Hperm2)|].
  split; [exact M3|].
  split; [exact K3|].
  split; [|exact Ha4096].
  rewrite Forall_forall in Hsaved |- *. intros o Ho. rewrite <- (Hsaved o Ho).
  pose proof (HSo o Ho) as Hob. apply rdword_ext. intros i Hi. apply KSAV. lia.
- unfold recv_blk. exact GARR.
- exact HTW3.
- exact HP3.
- exact HSB.
Qed.
End s.
