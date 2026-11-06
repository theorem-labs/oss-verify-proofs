(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, origin/cold/pg-prog), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/CanKit.v, with its module names changed; 492 of its 559 lines of code are new or changed and 457 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/SrxDeskKit.v, with its module paths and module names changed; 505 of its 560 lines of code are new or changed and 504 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/LLVMFuzzerTestOneInput_seg_recv.v, with its addresses and numbers changed; 424 of its 660 lines of code are new or changed and 324 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput_seg_bar2: Lemma lc_bar2_ok, the segment BAR2 of the image-A walk of LLVMFuzzerTestOneInput
   (lib/A/Prog/LLVMFuzzerTestOneInput_segs.v lc_bar2_stmt), from the cut lc_st_bar2 (+0xa9c) to the loop tail
   lc_st_tail (+0x12ec). The code (pc = 0x81264 + offset):
     +0xa9c   jal build_and_receive (0x857e0), return address +0xaa0: op 2's call, a0 = SPEC_BCAST, a1 = DESK,
              a2 = a3 = a4 = 0, a5 = the command, a6 = body (frame + 96, in the own class-2 frame), a7 = 34;
              build_and_receive is a G-form callee in the walk's own G journal (build_and_receive_cg.v
              transport_build_and_receive_cg at CTX_build_and_receive, the premise lp_bar);
     +0xaa0   li a0, -8; +0xaa4 .. +0xab4  sb a0, 12 .. 16(s2): body's five shadow bytes 0xf8 (out of scope);
     +0xab8   ld s4, 160(s1): g_fail_next's page from its spill slot;
     +0xabc   j +0x12e8;
     +0x12e8  li s6, 7, then the tail.
   The callee's pre at +0xa9c is BAR1's (LLVMFuzzerTestOneInput_seg_bar1.v): dst and src are read-only MACs (K2, their
   bytes from K1 and LLVMFuzzerTestOneInput_st.v lc_rom_bytes: b1_mac_ok, b1_rom_garr8), the model's Some from
   TSim/LoopOk.v op_ok through LLVMFuzzerTestOneInput_st.v lc_ann_eq, the run invariants and g_fail_next <= 1 (K6),
   recv_dn_each of the frame (K5) and the frame-pointer chain (K7); but body lies in the own class-2 frame
   (decode_in_fake), readable from the frame's shadow (decode_rd_ok: shadow bytes 12 .. 15 are 0 and 16 is 2). The jal
   and the call keep the loop's facts with body in scope (LLVMFuzzerTestOneInput_seg_recv.v lc_lcore_run, and
   lc_lcore_call_sh: seg_recv.v's lc_lcore_call with the shadow flags of the cut carried). One run of the
   position-abstract engine covers +0xaa0 .. +0x12ec: it writes the five shadow bytes (a region of the own frame's
   shadow) and reads the spill slot; lc_lcore_sh carries the loop's facts over it with body out of scope. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop YI16 YE00 YE01 YO09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportSyms DgnTransportList DgnTransportAddr DgnTransportPa DgnTransportImg DgnTransportPaLib YC4b YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v Img0 AE2k ACfn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AsanCells TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportCg TransportGCg TransportGRwA TransportGRunA CanKit TransportGNotice TransportGFrame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_tick_cg diginet_session_rx_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import send_data_cg on_announce_cg on_data_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_poll_cg receive_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import build_and_receive_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
LLVMFuzzerTestOneInput_cg LLVMFuzzerTestOneInput_segs LLVMFuzzerTestOneInput_st LLVMFuzzerTestOneInput_seg_recv
LLVMFuzzerTestOneInput_seg_bar1.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TSess0 TSess TCb TOps TNeed
  TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require Agree QueueFacts LoopOk LinksProof RxOpLib.
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
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TOP := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TOps.
Module AG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim.Agree.
Module QF := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim.QueueFacts.
Module LOK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim.LoopOk.
Module LP := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim.LinksProof.
Module RXL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim.RxOpLib.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 1. op_announce's call: the model and the body                       *)
(* ------------------------------------------------------------------ *)

(* The operation's model equation from build_and_receive's answer, and build_and_receive's Some from the
   operation's (LLVMFuzzerTestOneInput_st.v lc_ann_eq). *)
Lemma lc_b2_op : forall (I : TI.timg) (Bw : list byte) (a : Z) (D : list byte) (c : TOP.fuzz_in) (k : nat)
    (Bw' : list byte),
  lc_opc D c = 2 ->
  TOP.build_and_receive_m I Bw a TC.SPEC_BCAST TC.DESK 0 0 0
    (lc_acmd (av_sel (lc_ann_vals D (lc_oc D c)))) (av_body3 (lc_ann_vals D (lc_oc D c))) = Some (Bw', tt) ->
  TOP.LLVMFuzzerTestOneInput_op_m I Bw (fun _ => a) D c k = Some (Bw', (av_c (lc_ann_vals D (lc_oc D c)), S k)).
Proof.
intros I Bw a D c k Bw' Ho E. rewrite (lc_ann_eq I Bw (fun _ => a) D c k Ho). cbv beta zeta. rewrite E.
reflexivity.
Qed.

Lemma lc_b2_ne : forall (I : TI.timg) (Bw : list byte) (A : nat -> Z) (D : list byte) (c : TOP.fuzz_in) (k : nat) x,
  lc_opc D c = 2 ->
  TOP.LLVMFuzzerTestOneInput_op_m I Bw A D c k = Some x ->
  TOP.build_and_receive_m I Bw (A k) TC.SPEC_BCAST TC.DESK 0 0 0
    (lc_acmd (av_sel (lc_ann_vals D (lc_oc D c)))) (av_body3 (lc_ann_vals D (lc_oc D c))) <> None.
Proof.
intros I Bw A D c k x Ho E Hn. rewrite (lc_ann_eq I Bw A D c k Ho) in E. cbv zeta in E. rewrite Hn in E.
discriminate E.
Qed.

(* The three names are at most 8 bytes. *)
Lemma lc_name_len : forall k, (length (nth k TOP.op_announce_NAME []) <= 8)%nat.
Proof.
intros k. unfold TOP.op_announce_NAME.
destruct k as [|[|[|k]]]; [cbn; lia | cbn; lia | cbn; lia | destruct k; cbn; lia].
Qed.

(* body[34]: the 34 zeros, the MAC, "1.37" and the name stay 34 bytes. *)
Lemma lc_body_len : forall D c1, length (av_body3 (lc_ann_vals D c1)) = 34%nat.
Proof.
intros D c1. unfold lc_ann_vals.
destruct (TOP.fuzz_u8_m D c1) as [c1' sel].
destruct (TOP.fuzz_u8_m D c1') as [c2 m].
destruct (TOP.fuzz_u8_m D c2) as [c3 nm].
cbv zeta. cbn [av_body3].
pose proof (Z.mod_pos_bound m 16 ltac:(lia)) as Hm.
assert (L0 : length (repeat (DSpec.b8 0) (Z.to_nat (TC.SPEC_ANN_MIN + 1))) = 34%nat)
  by (rewrite repeat_length; reflexivity).
assert (LH : length TC.HOST = 6%nat) by reflexivity.
assert (LO : length TC.OTHER = 6%nat) by reflexivity.
assert (LV : length TOP.ANN_VERSION_137 = 4%nat) by reflexivity.
lazymatch goal with |- length (TW.upd (TW.upd ?b1 _ _) _ _) = _ =>
  assert (L1 : length b1 = 34%nat) end.
{ destruct (Z.ltb_spec (m mod 16) 10).
  - rewrite TWL.length_upd; [exact L0 | lia | rewrite L0, LH; lia].
  - destruct (Z.ltb_spec (m mod 16) 13).
    + rewrite TWL.length_upd; [exact L0 | lia | rewrite L0, LO; lia].
    + exact L0. }
lazymatch goal with |- length (TW.upd ?b2 _ _) = _ => assert (L2 : length b2 = 34%nat) end.
{ rewrite TWL.length_upd;
    [exact L1 | unfold TC.SPEC_ANN_VERSION; lia | rewrite L1, LV; unfold TC.SPEC_ANN_VERSION; lia]. }
pose proof (lc_name_len (Z.to_nat (nm mod 3))) as LN.
rewrite TWL.length_upd; [exact L2 | unfold TC.SPEC_ANN_NAME; lia | rewrite L2; unfold TC.SPEC_ANN_NAME; lia].
Qed.

(* ------------------------------------------------------------------ *)
(* 2. body in the own frame, and the frame's shadow maps                *)
(* ------------------------------------------------------------------ *)

(* Granules 12 .. 15 of the frame have shadow 0 and granule 16 has 2: [F + 96, F + 130) is addressable. *)
Lemma lc_body_ra : forall (rd : Z -> option Z) F, 0 <= F -> F mod 8 = 0 ->
  (forall i, 12 <= i < 17 -> rd (SHADOW_OFF + F / 8 + i) = Some (nth (Z.to_nat i) (lf_shm false true) 0)) ->
  range_addressable rd SHADOW_OFF (F + 96) 34.
Proof.
intros rd F HF0 HF8 HSH x Hx.
pose proof (Z.div_mod F 8 ltac:(lia)) as DF. rewrite HF8, Z.add_0_r in DF.
assert (Ex : x / 8 = F / 8 + (x - F) / 8).
{ replace x with (F / 8 * 8 + (x - F)) at 1 by lia. rewrite Z.div_add_l by lia. reflexivity. }
assert (Hg1 : 12 <= (x - F) / 8) by (apply Z.div_le_lower_bound; lia).
assert (Hg2 : (x - F) / 8 < 17) by (apply Z.div_lt_upper_bound; lia).
pose proof (Z.mul_div_le (x - F) 8 ltac:(lia)) as Hmd.
unfold shadow_of_addr. rewrite Ex, Z.add_assoc, (HSH _ (conj Hg1 Hg2)).
destruct (Z_lt_le_dec ((x - F) / 8) 16) as [Hlt | Hge].
- exists 0. split; [|left; reflexivity].
  assert (E : (x - F) / 8 = 12 \/ (x - F) / 8 = 13 \/ (x - F) / 8 = 14 \/ (x - F) / 8 = 15) by lia.
  destruct E as [E | [E | [E | E]]]; rewrite E; reflexivity.
- assert (E : (x - F) / 8 = 16) by lia. rewrite E. exists 2. split; [reflexivity|]. right.
  assert (Hx8 : x mod 8 = x - F - 128).
  { symmetry. apply (Z.mod_unique x 8 (F / 8 + 16) (x - F - 128)); [left; lia | lia]. }
  lia.
Qed.

(* body's 34 bytes in the own frame are readable: present, addressable, their shadow hull visible. *)
Lemma lc_body_rd {rc : YM05.RunCeil} : forall (W : world tfibsegs) mem F, 4096 <= F -> F mod 64 = 0 -> in_app F 256 ->
  (forall a, F <= a < F + 256 -> apresent (w_H W) mem a) ->
  (forall i, 0 <= i < 32 ->
     aview tfibsegs (w_H W) mem (SHADOW_OFF + F / 8 + i) = Some (nth (Z.to_nat i) (lf_shm false true) 0)) ->
  decode_rd_ok W mem (F + 96) 34.
Proof.
intros W mem F HF0 HF64 Happ Hpres Hsh.
assert (HF8 : F mod 8 = 0).
{ pose proof (Z.div_mod F 64 ltac:(lia)) as D. rewrite HF64, Z.add_0_r in D. rewrite D.
  replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by lia. apply Z_mod_mult. }
pose proof asan_consts as ((CVlo & CVhi) & _).
split; [|split; [|split; [|split; [|split]]]].
- intros a Ha. apply (can_aview_vis (segs := tfibsegs)). apply Hpres. lia.
- apply lc_body_ra; [lia | exact HF8 | intros i Hi; apply Hsh; lia].
- apply (frame_hull_vis _ F 256); [lia | exact HF64 | reflexivity | lia | lia | lia |].
  intros i Hi. change (256 / 8) with 32 in Hi. unfold shadow_addr. rewrite Hsh by lia. discriminate.
- unfold amem_range. unfold in_app in Happ. destruct Happ as (_ & [HL | [HH1 HH2]]); [left | right];
    unfold kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *; lia.
- lia.
- unfold in_app in Happ. destruct Happ as (_ & [HL | [HH1 HH2]]);
    unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia.
Qed.

(* The shadow maps with body in and out of scope agree outside body's five bytes, which are 0xf8 out of scope. *)
Lemma lc_shm_out : forall cin n, (n < 32)%nat -> ~ (12 <= n < 17)%nat ->
  nth n (lf_shm cin true) 0 = nth n (lf_shm cin false) 0.
Proof.
intros cin n Hn Hm. destruct cin; (do 32 (destruct n as [|n]; [first [reflexivity | exfalso; lia] |])); lia.
Qed.
Lemma lc_shm_in : forall cin n, (12 <= n < 17)%nat -> nth n (lf_shm cin false) 0 = 0xf8.
Proof.
intros cin n Hn. destruct cin; (do 17 (destruct n as [|n]; [first [reflexivity | exfalso; lia] |])); lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 3. The run after the call                                            *)
(* ------------------------------------------------------------------ *)

(* +0xaa0, the return of build_and_receive, and the tail. *)
Definition B2_RET : Z := 0xaa0.
(* s2's shadow bytes 12 .. 16 (written), and the spill slot at s1 + 160 (read: g_fail_next's page LF_S4). s2 is the
   frame's shadow address, in [SHADOW_OFF, 2 ^ 47]: the written window lies apart from the shadow span (0, 0). *)
Definition b2_rg_sh : YP09.region := YP09.mkRegion (Some 18%nat) 12 17 12 17 [].
Definition b2_rg_sp : YP09.region :=
  YP09.mkRegion (Some 9%nat) 160 168 0 0 [YP09.mkChunk 160 (YP09.CVal 8 (SLit LF_S4))].
Definition b2_facts : facts := mkFacts [(18%nat, mkAF SHADOW_OFF (2 ^ 47) 0)] [] [].
Definition ss_b2r : sstate := mkSS B2_RET sr_atoms [b2_rg_sh; b2_rg_sp] None b2_facts.

(* A byte a region of a symbolic state holds, read off the view. *)
Lemma b2_rg_view : forall (H : word -> bool) (mem : word -> option byte) (E : env) n lo hi wlo whi cs off w v b,
  region_ok tfibsegs E (mrestrict H mem) (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
  bv_unsigned (ew E n) = b -> In (YP09.mkChunk off (YP09.CVal w v)) cs -> 0 < Z.of_N w ->
  aview tfibsegs H mem (b + off) = Some (bv_unsigned (byte_of_word (sv_denot E v) 0)).
Proof.
intros H mem E n lo hi wlo whi cs off w v b (_ & _ & _ & Hcs) Hn Hin Hw.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hck. cbn [YP09.r_base base_val] in Hck. rewrite Hn in Hck.
destruct (Hck 0 ltac:(cbn [YP09.c_len YP09.cv_len YP09.c_val]; lia)) as (bb & Hb & Hm).
cbn [cbyte YP09.c_val YP09.c_off] in Hb, Hm. injection Hb as <-.
unfold aview. rewrite Z.add_0_r in Hm. rewrite Hm. reflexivity.
Qed.

(* Name the machine state of HS. *)
Ltac b2_name HS x :=
  lazymatch type of HS with
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok _ _ _ (restrict _ ?m) => rename m into x
  | st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into x
  end.

Section seg. Context {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

(* At +0xaa0: s2 = the frame's shadow address SH (bytes 12 .. 16 present), s1 = sp1 (the spill slot at sp1 + 160
   holds LF_S4). *)
Lemma b2_entry1 : forall (fx : YK11.FPState) (W : world segs) regs mem SH sp1,
  YK11.getr regs 18 = w64 SH -> YK11.getr regs 9 = w64 sp1 ->
  SHADOW_OFF <= SH -> SH <= 2 ^ 47 -> 0 <= sp1 -> sp1 + 168 <= 2 ^ 64 -> SH + 17 <= sp1 + 160 ->
  (forall i, 12 <= i < 17 -> apresent (w_H W) mem (SH + i)) ->
  rdword (aview segs (w_H W) mem) (sp1 + 160) = Some LF_S4 ->
  st_ok_pi segs VAL (lr_E0 regs) ss_b2r
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + B2_RET)) mem (YK11.seg_rom segs))).
Proof.
intros fx W regs mem SH sp1 R18 R9 H0 H1 H2 H3 Hd Hp Hw.
unfold SHADOW_OFF in H0.
assert (EW : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (lr_E0 regs) n = YK11.getr regs r)
  by (intros n r Hn; unfold lr_E0; apply can_ew_Eimg_Ereg_nat; exact Hn).
assert (U18 : bv_unsigned (ew (lr_E0 regs) 18) = SH)
  by (rewrite (EW 18%nat 18%bv eq_refl), R18; unfold w64; apply unsigned_lit_small; lia).
assert (U9 : bv_unsigned (ew (lr_E0 regs) 9) = sp1)
  by (rewrite (EW 9%nat 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. unfold ss_b2r.
apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [b2_rg_sh b2_rg_sp YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
    rewrite ?U18, ?U9.
  + split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable segs). apply Hp. lia.
  + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val segs (lr_E0 regs) _ sp1 160 8 (SLit LF_S4) LF_S4).
    * reflexivity.
    * split; [apply Z.leb_le | apply Z.ltb_lt]; vm_compute; reflexivity.
    * apply Z.leb_le. vm_compute. reflexivity.
    * exact (val_mem_of_rdword segs _ _ _ _ Hw).
- apply pairwise_disjoint_of_extents.
  unfold extent_of_region, b2_rg_sh, b2_rg_sp. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite U18, U9. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat split; first [exact I | lia].
- unfold b2_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U18. rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; try exact I; unfold SHADOW_OFF in *; lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 4. The loop's common facts across the call and across the stores    *)
(* ------------------------------------------------------------------ *)

(* LLVMFuzzerTestOneInput_seg_recv.v lc_lcore_call with the frame's shadow flags of the cut (cin, bin) carried:
   op 2 calls build_and_receive with body in scope. *)
Lemma lc_lcore_call_sh : forall cx op cin bin ly' S' (W : world segs) regs' mem' md' e (X : Z) (E : Z -> Prop)
    (COST : Z) ly2 S2 (W2 : world segs) regs2 mem2 md2 e2,
  @lp_prem rc B MT XL RLO RHI -> @lc_base rc B MT XL RLO RHI cx ->
  @lc_lcore rc B MT cx op cin bin (lo_k op) ly' S' W regs' mem' md' e ->
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS 0 [] LLVMF_STK (lc_sp0 cx) []
    (l_ly cx) (l_S cx) (l_W cx) (l_mem cx) (l_md cx) [(LF_CID, l_fpos cx)] ly2 S2 W2 mem2 md2 (e + e2) ->
  0 <= e2 <= RECV_EV ->
  aregs_preserved regs' regs2 -> frames S2 = frames S' -> Permutation (ablocks B ly2 S2) (ablocks B ly' S') ->
  acall_kept_g segs B TG.G_HARNESS ly' S' W mem' W2 mem2 (lc_sp1 cx - X) (lc_sp1 cx) E ->
  0 <= X <= LLVMF_STK - 336 ->
  (forall a, E a -> TG.G_HARNESS_LO <= a < TG.G_HARNESS_HI) ->
  mo_le MT S' S2 COST -> COST <= lf_rcost MT ->
  @lc_lcore rc B MT cx op cin bin (S (lo_k op)) ly2 S2 W2 regs2 mem2 md2 (e + e2).
Proof.
intros cx op cin bin ly' S' W regs' mem' md' e X E COST ly2 S2 W2 regs2 mem2 md2 e2 HP HB HL HJ2 He2 HPR Hfr2 Hperm2
  HK HX HE Hmo Hcost.
pose proof (lp_laws _ _ _ _ _ HP) as LAWS. pose proof (lp_meter_laws _ _ _ _ _ HP) as MTL.
pose proof HL as (HC & (R18 & R26) & HSP & HFSH & HOPOK & He & HMET & R21).
pose proof HOPOK as (_ & Hops & _ & _ & Hk).
pose proof (lc_geom B MT XL RLO RHI cx ly' S' W regs' mem' md' e HB HC) as G.
destruct G as [HARg Hsp0al Hstk Hsp1c HFaddr HFin Hn HINg HLIVEg].
pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hsp1 & _ & _ & HF4096 & _ & HFceil & _).
destruct Hstk as (Hceil & Hslo & Hshi & H47).
pose proof asan_consts as ((CVlo & CVhi) & _).
change (2 ^ 47) with 140737488355328 in H47.
unfold LF_FRAME, LF_FBYTES in *.
pose proof HK as (K1 & K2 & _ & K4 & _).
assert (KF : forall a, lc_F cx <= a < lc_F cx + 256 \/ lc_SH cx <= a < lc_SH cx + 32 ->
  aview segs (w_H W2) mem2 a = aview segs (w_H W) mem' a).
{ intros a Ha. apply (K4 LF_CID (l_fpos cx) a HFin).
  - unfold in_zr, frame_rng. cbn [fst snd]. rewrite HFaddr, lf_fbytes. unfold LF_FBYTES.
    change (256 / 8) with 32. unfold shadow_addr. unfold lc_SH in Ha. lia.
  - intros Hw. pose proof (HE a Hw) as Hh. destruct Ha as [Ha | Ha].
    + apply (frm_img segs B LAWS ly' S' W mem' md' LF_CID (l_fpos cx) a HARg HFin).
      * rewrite HFaddr, lf_fbytes. unfold LF_FBYTES. exact Ha.
      * exact (lc_hull_img a Hh).
    + unfold lc_SH, SHADOW_OFF, TG.G_HARNESS_LO, TG.G_HARNESS_HI in *.
      pose proof (Z.div_pos (lc_F cx) 8 ltac:(lia) ltac:(lia)). lia. }
assert (HC2 : @lc_core rc B cx ly2 S2 W2 regs2 mem2 md2 (e + e2)).
{ apply (lc_core_kept B MT XL RLO RHI cx ly' S' W regs' mem' md' e X ly2 S2 W2 regs2 mem2 md2 (e + e2) LAWS HB HC
    HJ2 Hfr2 Hperm2 HPR HX).
  - intros a Ha Hw. exact (K1 a Ha Hw).
  - intros b m i Hin Hi. apply (K2 b m i Hin Hi). intros Hw.
    apply (blk_img segs B LAWS ly' S' W mem' md' b m (b + i) HARg Hin ltac:(lia)).
    exact (lc_hull_img _ (HE _ Hw)).
  - intros a Ha. apply KF. unfold LF_FBYTES in Ha. exact Ha. }
split; [exact HC2|].
split; [split; [exact (lc_reg_kept regs' regs2 18 _ HPR ltac:(hnf; lia) R18)
              | exact (lc_reg_kept regs' regs2 26 _ HPR ltac:(hnf; lia) R26)]|].
split.
{ apply (lc_spills_kept cx _ (aview segs (w_H W) mem') (aview segs (w_H W2) mem2)); [| | exact HSP].
  - intros o Ho.
    pose proof (lf_spill_vals (lc_F cx) ltac:(lia) ltac:(unfold LF_FBYTES; change (2 ^ 63) with 9223372036854775808; lia))
      as SV.
    rewrite Forall_forall in SV. destruct (SV o Ho) as (_ & _ & H8 & H192). lia.
  - intros a Ha. apply K1; [change (2 ^ 64) with 18446744073709551616; unfold lc_sp0 in *; lia | lia]. }
split; [apply (lc_fsh_kept cx (aview segs (w_H W) mem')); [intros a Ha; apply KF; right; exact Ha | exact HFSH]|].
split; [exact HOPOK|].
split; [rewrite Nat2Z.inj_succ; change RECV_EV with 2 in *; lia|].
split.
{ destruct HMET as (Hle & Hok). unfold lc_meter.
  assert (R0 : 0 <= lf_rcost MT).
  { unfold lf_rcost. pose proof (mo_malloc_nonneg MT MTL 65535 ltac:(lia)). pose proof (mo_free_nonneg MT MTL). lia. }
  rewrite Nat2Z.inj_succ.
  set (K := Z.of_nat (lo_k op)) in *.
  assert (HK1 : K + 1 <= TC.OPS_MAX) by lia.
  split.
  - apply (mle_weaken MT (l_S cx) S2 (K * lf_rcost MT + COST)); [exact MTL | |].
    + exact (mle_station MT (l_S cx) S' S2 _ _ MTL Hle Hmo).
    + rewrite Z.mul_succ_l. lia.
  - apply (mok_station MT S' S2 ((TC.OPS_MAX - K) * lf_rcost MT) COST); [exact MTL | exact Hok | exact Hmo | |].
    + apply Z.mul_nonneg_nonneg; lia.
    + replace ((TC.OPS_MAX - K) * lf_rcost MT) with ((TC.OPS_MAX - Z.succ K) * lf_rcost MT + lf_rcost MT) by ring.
      lia. }
exact (lc_reg_kept regs' regs2 21 _ HPR ltac:(hnf; lia) R21).
Qed.

(* A run that writes body's five shadow bytes 0xf8 (and no other byte) and keeps sp, gp, tp, s0, s1, s2, s5 and s10
   keeps the loop's common facts, body now out of scope. *)
Lemma lc_lcore_sh : forall cx op cin k ly' S' (W : world segs) regs' mem' md' e regs2 mem2 md2,
  @lp_prem rc B MT XL RLO RHI -> @lc_base rc B MT XL RLO RHI cx ->
  @lc_lcore rc B MT cx op cin true k ly' S' W regs' mem' md' e ->
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS 0 [] LLVMF_STK (lc_sp0 cx) []
    (l_ly cx) (l_S cx) (l_W cx) (l_mem cx) (l_md cx) [(LF_CID, l_fpos cx)] ly' S' W mem2 md2 e ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lc_SH cx + 12 <= a < lc_SH cx + 17) ->
     aview segs (w_H W) mem2 a = aview segs (w_H W) mem' a) ->
  (forall i, 12 <= i < 17 -> aview segs (w_H W) mem2 (lc_SH cx + i) = Some 0xf8) ->
  (forall a, apresent (w_H W) mem' a -> apresent (w_H W) mem2 a) ->
  YK11.getr regs2 2 = YK11.getr regs' 2 -> YK11.getr regs2 3 = YK11.getr regs' 3 ->
  YK11.getr regs2 4 = YK11.getr regs' 4 -> YK11.getr regs2 8 = YK11.getr regs' 8 ->
  YK11.getr regs2 9 = YK11.getr regs' 9 -> YK11.getr regs2 18 = YK11.getr regs' 18 ->
  YK11.getr regs2 21 = YK11.getr regs' 21 -> YK11.getr regs2 26 = YK11.getr regs' 26 ->
  @lc_lcore rc B MT cx op cin false k ly' S' W regs2 mem2 md2 e.
Proof.
intros cx op cin k ly' S' W regs' mem' md' e regs2 mem2 md2 HP HB HL HJ2 KR KV GR E2 E3 E4 E8 E9 E18 E21 E26.
pose proof (lp_laws _ _ _ _ _ HP) as LAWS.
destruct HL as (HC & (R18 & R26) & HSP & HFSH & HOPOK & He & HMET & R21).
pose proof (lc_geom B MT XL RLO RHI cx ly' S' W regs' mem' md' e HB HC) as G.
destruct G as [HARg Hsp0al Hstk Hsp1c HFaddr HFin Hn HINg HLIVEg].
destruct (frames_bounds segs B LAWS ly' S' W mem' md' LF_CID (l_fpos cx) HARg HFin) as (_ & _ & HFapp).
rewrite HFaddr in HFapp. change (fs_frame_bytes LF_CID) with 256 in HFapp.
destruct HC as (_ & Hfrs & HlyF & HPERM & Rsp & R8 & R9 & Rgp & Rtp & Hsp1 & Hsp1al & HSAV & HF4096 & HFal & HFceil &
  HFpres & HFL & HIN).
destruct Hstk as (Hceil & Hslo & Hshi & H47).
pose proof asan_consts as ((CVlo & CVhi) & _).
change (2 ^ 47) with 140737488355328 in H47.
unfold LF_FRAME, LF_FBYTES in *.
assert (HF8 : 0 <= lc_F cx / 8 /\ 8 * (lc_F cx / 8) <= lc_F cx)
  by (split; [apply Z.div_pos; lia | apply Z.mul_div_le; lia]).
assert (HSHb : 2147450880 <= lc_SH cx /\ lc_SH cx + 32 <= alloc_ceiling) by (unfold lc_SH, SHADOW_OFF; lia).
(* every byte away from the frame's 32 shadow bytes is kept *)
assert (KS : forall a, 0 <= a < 2 ^ 64 -> a < lc_SH cx \/ lc_SH cx + 32 <= a ->
  aview segs (w_H W) mem2 a = aview segs (w_H W) mem' a) by (intros a Ha Hn'; apply KR; [exact Ha | lia]).
(* the frame's bytes lie apart from its shadow bytes (in_app: low memory below the shadow, or high memory) *)
assert (HFS : lc_F cx + 256 <= lc_SH cx \/ lc_SH cx + 32 <= lc_F cx).
{ unfold in_app in HFapp. destruct HFapp as (_ & [HL | [HH1 HH2]]); [left | right];
    unfold lc_SH, SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *; lia. }
split.
{ split; [exact HJ2|]. split; [exact Hfrs|]. split; [exact HlyF|]. split; [exact HPERM|].
  split; [exact (eq_trans E2 Rsp)|]. split; [exact (eq_trans E8 R8)|]. split; [exact (eq_trans E9 R9)|].
  split; [exact (eq_trans E3 Rgp)|]. split; [exact (eq_trans E4 Rtp)|].
  split; [exact Hsp1|]. split; [exact Hsp1al|].
  split.
  { unfold lc_saved in HSAV |- *. rewrite Forall_forall in HSAV |- *. intros o Ho.
    assert (Hor : 8 <= fst o <= 104).
    { unfold LF_SAVED in Ho. repeat (destruct Ho as [<- | Ho]; [cbn; lia|]). destruct Ho. }
    rewrite (rdword_ext (aview segs (w_H W) mem') (aview segs (w_H W) mem2) (lc_sp0 cx - fst o))
      by (intros j Hj; apply KS; lia).
    exact (HSAV o Ho). }
  split; [exact HF4096|]. split; [exact HFal|]. split; [exact HFceil|].
  split; [intros a Ha; exact (GR a (HFpres a Ha))|].
  split.
  { rewrite (rdword_ext (aview segs (w_H W) mem') (aview segs (w_H W) mem2) (lc_F cx + LF_FBYTES - 8))
      by (intros j Hj; unfold LF_FBYTES; apply KS; unfold LF_FBYTES in Hj; lia).
    exact HFL. }
  destruct HIN as (HPAYg & HPAYv).
  destruct (Z_lt_le_dec 0 (l_n cx)) as [Hn0 | Hn0].
  - pose proof (HINg Hn0) as InP.
    destruct (al_blocks _ _ LAWS ly' S' W mem' md' (l_p cx) (l_n cx) HARg InP) as (_ & H4096 & Hce & _ & _ & _ & Hnb).
    pose proof (req_size_pos (l_n cx) (proj1 Hnb)) as [_ Hreq].
    assert (KI : forall j, 0 <= j < l_n cx ->
      aview segs (w_H W) mem2 (l_p cx + j) = aview segs (w_H W) mem' (l_p cx + j)).
    { intros j Hj.
      pose proof (amem_range_of_block segs B LAWS ly' S' W mem' md' (l_p cx) (l_n cx) (l_p cx + j) 1 HARg InP
        ltac:(lia) ltac:(lia)) as Ham.
      apply KS; [lia|].
      unfold amem_range in Ham. unfold lc_SH, SHADOW_OFF, kLowMemEnd, kHighMemBeg, kHighMemEnd in *. lia. }
    split.
    + apply (lc_garr8_kept (w_H W) (w_H W) mem' mem2 (l_p cx) _); [|exact HPAYg].
      intros j Hj. rewrite length_map in Hj. destruct Hn as (_ & Hnl). rewrite <- Hnl in Hj. exact (KI j Hj).
    + intros i Hi. rewrite (KI i Hi). exact (HPAYv i Hi).
  - destruct Hn as (Hn1 & Hnl). split.
    + destruct (l_pl cx) as [|b0 pl0] eqn:Epl; [apply garr8_nil|]. exfalso. cbn [length] in Hnl. lia.
    + intros i Hi. lia. }
split; [split; [exact (eq_trans E18 R18) | exact (eq_trans E26 R26)]|].
split.
{ unfold lc_spills in HSP |- *. rewrite Forall_forall in HSP |- *. intros o Ho.
  pose proof (lf_spill_vals (lc_F cx) ltac:(lia) ltac:(unfold LF_FBYTES; change (2 ^ 63) with 9223372036854775808; lia))
    as SV.
  rewrite Forall_forall in SV. destruct (SV o Ho) as (_ & _ & H8 & H192).
  rewrite (rdword_ext (aview segs (w_H W) mem') (aview segs (w_H W) mem2) (lc_sp1 cx + fst o))
    by (intros j Hj; apply KS; lia).
  exact (HSP o Ho). }
split.
{ intros i Hi. destruct (Z_lt_le_dec i 12) as [Hi1 | Hi1]; [|destruct (Z_lt_le_dec i 17) as [Hi2 | Hi2]].
  - rewrite KR by lia. rewrite (HFSH i Hi). f_equal. apply lc_shm_out; lia.
  - rewrite (KV i ltac:(lia)). f_equal. symmetry. apply lc_shm_in. lia.
  - rewrite KR by lia. rewrite (HFSH i Hi). f_equal. apply lc_shm_out; lia. }
split; [exact HOPOK|]. split; [exact He|]. split; [exact HMET|]. exact (eq_trans E21 R21).
Qed.

(* ------------------------------------------------------------------ *)
(* 5. The segment                                                       *)
(* ------------------------------------------------------------------ *)

Lemma lc_bar2_ok (K1 : @lc_rom_view_stmt rc B MT XL RLO RHI) (K2 : @lc_src_ro_stmt rc B MT XL RLO RHI)
    (K5 : lc_dn_each_stmt) (K6 : lc_runinv_stmt) (K7 : @lc_chain_stmt rc B MT XL RLO RHI) :
  @lc_bar2_stmt rc B MT XL RLO RHI.
Proof.
unfold lc_bar2_stmt. intros HP cx op W c HB HST.
destruct HST as (ly' & S' & regs' & mem' & md' & e & HST). cbv zeta in HST.
destruct HST as (-> & Hopc & HL & Htw & Hbody & R10 & R11 & R12 & R13 & R14 & R15 & R16 & R17 & (R24 & R23)).
set (D := l_pl cx) in *.
set (av := lc_ann_vals D (lc_oc D (lo_c op))) in *.
pose proof HL as (HC & (R18 & R26) & HSP & HFSH & HOPOK & He & HMET & R21).
pose proof HOPOK as (HAG & Hops & Hcin & Hcn & Hk).
assert (HBL : length (av_body3 av) = 34%nat) by exact (lc_body_len _ _).
set (body := av_body3 av) in *.
set (cmd := lc_acmd (av_sel av)) in *.
assert (Hcmd : 0 <= cmd < 2 ^ 8).
{ unfold cmd, lc_acmd. destruct (Z.land (av_sel av) 1 =? 0); unfold TC.SPEC_CMD_E0, TC.SPEC_CMD_E1;
  change (2 ^ 8) with 256; lia. }
set (frame := bar_frame TC.SPEC_BCAST TC.DESK 0 0 0 cmd body).
assert (Hfl : Z.of_nat (length frame) <= 1514)
  by (unfold frame, bar_frame; apply RXL.spec_build_frame_len; rewrite HBL; lia).
pose proof (lp_laws _ _ _ _ _ HP) as LAWS.
pose proof (lp_meter_laws _ _ _ _ _ HP) as MTL.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned _ _ _ _ _ HP)) as HGX.
pose proof HC as (HJ & Hfrs & _ & _ & R2 & R8 & R9 & R3 & R4 & Hsp1 & Hsp1al & _ & HF4096 & HFal & HFceil & HFpres &
  _ & _).
pose proof (lc_geom B MT XL RLO RHI cx ly' S' W regs' mem' md' e HB HC) as G.
destruct G as [HARg Hsp0al Hstk Hsp1c HFaddr HFin Hn HINg HLIVEg].
destruct Hstk as (Hceil & Hslo & Hshi & H47).
pose proof asan_consts as ((CVlo & CVhi) & _).
change (2 ^ 47) with 140737488355328 in H47.
unfold LF_FRAME in Hsp1. unfold LF_FBYTES in HFceil.
destruct (frames_bounds segs B LAWS ly' S' W mem' md' LF_CID (l_fpos cx) HARg HFin) as (_ & _ & HFapp).
rewrite HFaddr in HFapp. change (fs_frame_bytes LF_CID) with 256 in HFapp.
assert (HF8 : 0 <= lc_F cx / 8 /\ 8 * (lc_F cx / 8) <= lc_F cx)
  by (split; [apply Z.div_pos; lia | apply Z.mul_div_le; lia]).
assert (HSHb : 2147450880 <= lc_SH cx /\ lc_SH cx + 32 <= alloc_ceiling) by (unfold lc_SH, SHADOW_OFF; lia).
(* the model: build_and_receive answers at every address the malloc can return *)
assert (HMOD : forall a, recv_addr_ok a ->
  TOP.build_and_receive_m timg_A (lo_B op) a TC.SPEC_BCAST TC.DESK 0 0 0 cmd body <> None).
{ intros a (Ha1 & Ha2).
  destruct (LOK.op_ok LP.links_holds timg_A (lo_ops op) (lo_B op) (fun _ => a) D (lo_c op) (lo_k op) HAG Hops Hcin Hcn
    Ha1 Ha2) as (B' & c' & k'' & E' & _).
  exact (lc_b2_ne timg_A (lo_B op) (fun _ => a) D (lo_c op) (lo_k op) _ Hopc E'). }
(* the run invariants and receive's invariant (3) at the operation's start world *)
destruct (K6 (lo_ops op) (lo_B op) HAG) as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & Hgf).
assert (Hdn : recv_dn_each timg_A (lo_B op) frame 0 0)
  by (apply (K5 (lo_ops op) (lo_B op) frame 0 0 HAG Hops); lia).
(* the events, the live bytes and the meter *)
pose proof HB as HB2. unfold lc_base, tfib_lib_pre_x in HB2.
destruct HB2 as (_ & _ & _ & _ & _ & _ & _ & _ & Hev & _).
pose proof transport_llvmf_events_ok as HEV. unfold transport_llvmf_events in HEV.
assert (PEV : st_nev (l_S cx) + e + BAR_EV <= EV_MAX) by (change BAR_EV with 2; change RECV_EV with 2 in *; lia).
assert (PLIVE : blocks_bytes S' + RECV_LIVE <= LIVE_MAX) by (unfold RECV_LIVE, LIVE_LIB in *; lia).
pose proof HMET as (Hmle & Hmok).
assert (R0 : 0 <= lf_rcost MT).
{ unfold lf_rcost. pose proof (mo_malloc_nonneg MT MTL 65535 ltac:(lia)). pose proof (mo_free_nonneg MT MTL). lia. }
assert (Hcost : recv_cost MT (Z.of_nat (length frame)) <= lf_rcost MT).
{ unfold recv_cost, lf_rcost.
  pose proof (mo_malloc_mono MT MTL (Z.max 1 (Z.of_nat (length frame))) 65535 ltac:(lia)). lia. }
assert (PCOST : recv_cost MT (Z.of_nat (length frame)) <= (TC.OPS_MAX - Z.of_nat (lo_k op)) * lf_rcost MT).
{ assert (H1 : 1 <= TC.OPS_MAX - Z.of_nat (lo_k op)) by lia.
  pose proof (Z.mul_le_mono_nonneg_r 1 (TC.OPS_MAX - Z.of_nat (lo_k op)) (lf_rcost MT) R0 H1). lia. }
(* ---- +0xa9c: jal build_and_receive ---- *)
pose proof (@paj_run_x (l_fx cx) rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS
  HGX 0 []) as RUN.
pose proof (@paj_run_to_x (l_fx cx) rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS
  HGX 0 []) as RUNTO.
pose proof (lr_entry0 (l_fx cx) W regs' mem' LO_BAR2) as HS.
set (E := lr_E0 regs') in HS.
assert (HEI : img_env VAL A_LIM E) by (unfold E, lr_E0; apply Eimg_env).
assert (EW : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs' r)
  by (intros n r Hn0; unfold E, lr_E0; apply can_ew_Eimg_Ereg_nat; exact Hn0).
assert (SHOK : sh_ok segs (SLit 0) (@nil shent) E (mrestrict (w_H W) mem')) by constructor.
unfold lc_cfg.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst (l_fx cx) regs' (Z_to_bv 64 (BASE + LO_BAR2)) mem' (YK11.seg_rom segs)) md')
    Q) end.
paj_run_tok RUN HS HJ SHOK LR_B0.
{ lr_awr. }
lr_kept HFr KC W mem' ms.
assert (GC : forall x, apresent (w_H W) mem' x -> apresent (w_H W) (ms_mem ms) x)
  by (intros x Hx; exact (apresent_grows _ _ _ x HG Hx)).
clear HF HFr HG.
lr_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 2720)) C1 ltac:(apply codeptr_val; exact HEI).
lr_keq HS EW regs' (2%bv : bv 5) 2%nat C2. lr_keq HS EW regs' (3%bv : bv 5) 3%nat C3.
lr_keq HS EW regs' (4%bv : bv 5) 4%nat C4. lr_keq HS EW regs' (8%bv : bv 5) 8%nat C8.
lr_keq HS EW regs' (9%bv : bv 5) 9%nat C9. lr_keq HS EW regs' (10%bv : bv 5) 10%nat C10.
lr_keq HS EW regs' (11%bv : bv 5) 11%nat C11. lr_keq HS EW regs' (12%bv : bv 5) 12%nat C12.
lr_keq HS EW regs' (13%bv : bv 5) 13%nat C13. lr_keq HS EW regs' (14%bv : bv 5) 14%nat C14.
lr_keq HS EW regs' (15%bv : bv 5) 15%nat C15. lr_keq HS EW regs' (16%bv : bv 5) 16%nat C16.
lr_keq HS EW regs' (17%bv : bv 5) 17%nat C17. lr_keq HS EW regs' (18%bv : bv 5) 18%nat C18.
lr_keq HS EW regs' (21%bv : bv 5) 21%nat C21. lr_keq HS EW regs' (23%bv : bv 5) 23%nat C23.
lr_keq HS EW regs' (24%bv : bv 5) 24%nat C24. lr_keq HS EW regs' (26%bv : bv 5) 26%nat C26.
pmkst HS.
lazymatch goal with |- SRr _ _ (mkCfg (@YK11.mkst _ ?rg _ ?mm _) ?mdx) _ =>
  set (regsC := rg) in *; set (memC := mm) in *; set (mdC := mdx) in * end.
(* the loop's facts at the call, body in scope *)
assert (HLC : @lc_lcore rc B MT cx op false true (lo_k op) ly' S' W regsC memC mdC e)
  by exact (lc_lcore_run B MT cx op false true (lo_k op) ly' S' W regs' mem' md' e regsC memC mdC HL HJ KC GC
              C2 C3 C4 C8 C9 C18 C21 C26).
pose proof HLC as (HCC & _ & _ & HFSHC & _).
pose proof HCC as (HJC & _).
assert (USPC : spZ regsC = lc_sp1 cx)
  by (unfold spZ; rewrite C2, R2; unfold w64; apply unsigned_lit_small; lia).
assert (S0C : s0Z regsC = lc_sp0 cx)
  by (unfold s0Z; rewrite C8, R8; unfold w64; apply unsigned_lit_small; unfold lc_sp0 in *; lia).
assert (RAC : raZ regsC = 0x81d04) by (unfold raZ; rewrite C1; vm_compute; reflexivity).
pose proof (K1 HP cx ly' S' W regsC memC mdC e HB HCC) as PROM.
destruct (K7 HP cx ly' S' W regsC memC mdC e HB HCC) as (ch & Hch & Hspine).
(* dst = SPEC_BCAST and src = DESK: read-only MACs of the image *)
assert (Hdm : In (TRANS_SPEC_BCAST, TC.SPEC_BCAST) b1_macs) by (unfold b1_macs; b1_in).
assert (Hsm : In (TRANS_DESK, TC.DESK) b1_macs) by (unfold b1_macs; b1_in).
destruct (b1_mac_ok _ _ Hdm) as (Hdrom & Hdlen & Hdk2 & Hdro).
destruct (b1_mac_ok _ _ Hsm) as (Hsrom & Hslen & Hsk2 & Hsro).
assert (Pdg : garr8 segs (mrestrict (w_H W) memC) TRANS_SPEC_BCAST (TW.zs TC.SPEC_BCAST))
  by (apply (b1_rom_garr8 W memC _ _ PROM Hdrom); rewrite Hdlen; exact Hdro).
assert (Psg : garr8 segs (mrestrict (w_H W) memC) TRANS_DESK (TW.zs TC.DESK))
  by (apply (b1_rom_garr8 W memC _ _ PROM Hsrom); rewrite Hslen; exact Hsro).
pose proof (K2 HP cx ly' S' W regsC memC mdC e TRANS_SPEC_BCAST 6 HB HCC Hdk2) as Pds.
pose proof (K2 HP cx ly' S' W regsC memC mdC e TRANS_DESK 6 HB HCC Hsk2) as Pss.
assert (Pdw : decode_off_win regsC BAR_STK TRANS_SPEC_BCAST BAR_MAC).
{ pose proof (trans_ro_rd_bounds _ (Hdro 5 ltac:(lia))) as Hb.
  left. rewrite USPC, b1_stk. unfold BAR_MAC. lia. }
assert (Psw : decode_off_win regsC BAR_STK TRANS_DESK BAR_MAC).
{ pose proof (trans_ro_rd_bounds _ (Hsro 5 ltac:(lia))) as Hb.
  left. rewrite USPC, b1_stk. unfold BAR_MAC. lia. }
(* body: 34 bytes of the own class-2 frame, in scope *)
assert (Pbg : garr8 segs (mrestrict (w_H W) memC) (lc_F cx + 96) (TW.zs body)).
{ apply (lc_garr8_kept (w_H W) (w_H W) mem' memC (lc_F cx + 96) _); [|exact Hbody].
  intros j Hj. unfold TW.zs in Hj. rewrite length_map, HBL in Hj. change (Z.of_nat 34) with 34 in Hj.
  apply KC. lia. }
assert (HRD : decode_rd_ok W memC (lc_F cx + 96) 34).
{ apply (lc_body_rd W memC (lc_F cx) HF4096 HFal HFapp).
  - intros a Ha. apply GC. apply HFpres. unfold LF_FBYTES. exact Ha.
  - intros i Hi. exact (HFSHC i Hi). }
assert (Pbs : (0 < length body)%nat ->
  trans_src_ok B ly' S' W memC (lc_F cx + 96) (Z.of_nat (length body)) /\
  decode_off_win regsC BAR_STK (lc_F cx + 96) (Z.of_nat (length body))).
{ intros _. rewrite HBL. change (Z.of_nat 34) with 34. split.
  - right. split; [|exact HRD]. left. exists LF_CID, (l_fpos cx).
    split; [rewrite Hfrs; left; reflexivity|]. rewrite HFaddr, lf_fbytes. unfold LF_FBYTES. lia.
  - left. rewrite USPC, b1_stk. lia. }
assert (Ptw : tw_at TMAP_A (aview segs (w_H W) memC) (lo_B op)).
{ unfold lc_tw in Htw. apply (tw_kept TMAP_A (aview segs (w_H W) mem')); [exact Htw|].
  intros x Hx. pose proof (TMAP_A_hull x Hx) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh. apply KC. lia. }
assert (PC5 : count_cid BAR_CID (frames S') + 2 < fs_frames BAR_CID) by (rewrite Hfrs; vm_compute; reflexivity).
assert (PC1 : count_cid SRX_CID (frames S') < fs_frames SRX_CID) by (rewrite Hfrs; vm_compute; reflexivity).
assert (PC4 : count_cid ONANN_CID (frames S') < fs_frames ONANN_CID) by (rewrite Hfrs; vm_compute; reflexivity).
assert (PC0 : count_cid SENDDATA_CID (frames S') < fs_frames SENDDATA_CID) by (rewrite Hfrs; vm_compute; reflexivity).
assert (PC2 : count_cid ONDATA_CID (frames S') + 2 < fs_frames ONDATA_CID) by (rewrite Hfrs; vm_compute; reflexivity).
(* +0xa9c: build_and_receive *)
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst (l_fx cx) rg (Z_to_bv 64 (transport_sigma TS_build_and_receive)) mm rom) mdx) Q)
end.
eapply SRr_bind.
{ exact (lp_bar _ _ _ _ _ HP (l_fx cx) LLVMF_STK (lc_sp0 cx) _ (l_ly cx) (l_S cx) (l_W cx) (l_mem cx) (l_md cx)
    [(LF_CID, l_fpos cx)] ly' S' W memC mdC e regsC TRANS_SPEC_BCAST TRANS_DESK (lc_F cx + 96) 0 0 0 cmd
    ((TC.OPS_MAX - Z.of_nat (lo_k op)) * lf_rcost MT) TC.SPEC_BCAST TC.DESK body (lo_B op) ch
    HJC
    ltac:(rewrite C1; apply (ret_ok_codeptr_v (PI := PI_transport)); [lia | reflexivity])
    ltac:(rewrite RAC; lia)
    (eq_trans C3 R3) (eq_trans C4 R4) (eq_trans C10 R10) (eq_trans C11 R11)
    ltac:(rewrite C12, R12; reflexivity) ltac:(rewrite C13, R13; reflexivity)
    (eq_trans C14 R14) (eq_trans C15 R15) (eq_trans C16 R16)
    ltac:(rewrite C17, R17, HBL; reflexivity)
    ltac:(rewrite USPC, S0C; exact Hch)
    ltac:(rewrite RAC, b1_ctx_at; destruct Hspine as [Hsp | Hsp]; rewrite Hsp;
          [left; reflexivity | right; left; reflexivity])
    ltac:(rewrite USPC; pose proof (Z.div_mod (lc_sp1 cx) 32 ltac:(lia)) as Dm;
          rewrite Hsp1al, Z.add_0_r in Dm; rewrite Dm;
          replace (32 * (lc_sp1 cx / 32)) with ((2 * (lc_sp1 cx / 32)) * 16) by ring; apply Z.mod_mul; lia)
    ltac:(rewrite USPC, b1_stk; unfold LLVMF_STK; lia)
    ltac:(rewrite USPC; lia)
    ltac:(change (2 ^ 16) with 65536; lia) ltac:(change (2 ^ 32) with 4294967296; lia)
    ltac:(change (2 ^ 8) with 256; lia) Hcmd
    Hdlen Pdg Pds Pdw Hslen Psg Pss Psw Pbg Pbs Ptw Hgf HMOD PROM I1 I2 I3 I4 I5 I6 I7 Hdn
    PC5 PC1 PC4 PC0 PC2 PEV PLIVE Hmok PCOST). }
cbv beta. intros W3 c3 _ HPOST.
unfold transport_bar_post, transport_cg_post in HPOST. cbv beta in HPOST.
destruct HPOST as (ly3 & S3 & regs3 & mem3 & md3 & e3 & -> & He3 & HJ3 & HP3 & Hfr3 & Hperm3 & HK3 & Hmo3 &
  (a & Bw' & Haok & Hbm & Htw3 & Hgf3)).
rewrite USPC in HK3.
assert (HL3 : @lc_lcore rc B MT cx op false true (S (lo_k op)) ly3 S3 W3 regs3 mem3 md3 (e + e3))
  by exact (lc_lcore_call_sh cx op false true ly' S' W regsC memC mdC e BAR_STK (recv_wr frame)
              (recv_cost MT (Z.of_nat (length frame))) ly3 S3 W3 regs3 mem3 md3 e3 HP HB HLC HJ3 He3 HP3 Hfr3 Hperm3
              HK3 ltac:(rewrite b1_stk; unfold LLVMF_STK; lia) (lc_recv_wr_hull frame) Hmo3 Hcost).
(* ---- +0xaa0 .. +0x12ec: body's shadow out of scope, s4 reloaded, `j`, s6 = 7 ---- *)
rewrite C1.
pose proof HL3 as (HC3 & _ & HSP3 & _).
pose proof (lc_geom B MT XL RLO RHI cx ly3 S3 W3 regs3 mem3 md3 (e + e3) HB HC3) as G3.
destruct G3 as [HAR3 _ _ _ HFaddr3 HFin3 _ _ _].
destruct (al_frames _ _ LAWS _ _ _ _ _ LF_CID (l_fpos cx) HAR3 HFin3) as (_ & _ & _ & HFsh3).
rewrite HFaddr3 in HFsh3. change (fs_frame_bytes LF_CID / 8) with 32 in HFsh3.
assert (P18 : YK11.getr regs3 18 = w64 (lc_SH cx))
  by exact (lc_reg_kept regsC regs3 18 _ HP3 ltac:(hnf; lia) (eq_trans C18 R18)).
assert (P9 : YK11.getr regs3 9 = w64 (lc_sp1 cx))
  by exact (lc_reg_kept regsC regs3 9 _ HP3 ltac:(hnf; lia) (eq_trans C9 R9)).
assert (HS4w : rdword (aview segs (w_H W3) mem3) (lc_sp1 cx + 160) = Some LF_S4).
{ unfold lc_spills in HSP3. rewrite Forall_forall in HSP3. apply (HSP3 (160, LF_S4)).
  unfold lf_spill_loop, lf_spill_init, lf_spill_scal, lf_spill_sm. b1_in. }
pose proof (b2_entry1 (l_fx cx) W3 regs3 mem3 (lc_SH cx) (lc_sp1 cx) P18 P9 ltac:(unfold SHADOW_OFF; lia)
  ltac:(pose proof (@alloc_ceiling_lt rc); lia) ltac:(lia)
  ltac:(unfold lc_sp0 in *; lia) ltac:(lia) (fun i Hi => proj1 (HFsh3 i ltac:(lia))) HS4w) as HS2.
set (E3 := lr_E0 regs3) in HS2.
assert (HEI3 : img_env VAL A_LIM E3) by (unfold E3, lr_E0; apply Eimg_env).
assert (EW3 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E3 n = YK11.getr regs3 r)
  by (intros n r Hn0; unfold E3, lr_E0; apply can_ew_Eimg_Ereg_nat; exact Hn0).
assert (U18 : bv_unsigned (ew E3 18) = lc_SH cx)
  by (rewrite (EW3 18%nat 18%bv eq_refl), P18; unfold w64; apply unsigned_lit_small; lia).
assert (U9 : bv_unsigned (ew E3 9) = lc_sp1 cx)
  by (rewrite (EW3 9%nat 9%bv eq_refl), P9; unfold w64; apply unsigned_lit_small; unfold lc_sp0 in *; lia).
assert (SHOK3 : sh_ok segs (SLit 0) (@nil shent) E3 (mrestrict (w_H W3) mem3)) by constructor.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst (l_fx cx) regs3 (Z_to_bv 64 (BASE + B2_RET)) mem3 (YK11.seg_rom segs)) md3)
    Q) end.
paj_run_to_tok RUNTO HS2 HJ3 SHOK3 LR_B0 LO_TAIL.
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
  eapply (awr_ok_x_cons_own _ _ _ _ _ _ _ _ _ _ _ _ LF_CID (l_fpos cx)); [left; reflexivity | |].
  - intros x Hx. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx. rewrite U18 in Hx.
    right. unfold in_zr. cbn [fst snd]. rewrite HFaddr3. change (fs_frame_bytes LF_CID / 8) with 32.
    unfold shadow_addr. unfold lc_SH in Hx. lia.
  - apply awr_ok_x_cons; [intros x Hx; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx; lia |].
    apply awr_ok_x_nil. }
b2_name HS2 msR.
(* the run wrote body's five shadow bytes only *)
assert (K4 : forall x, 0 <= x < 2 ^ 64 -> ~ (lc_SH cx + 12 <= x < lc_SH cx + 17) ->
  aview segs (w_H W3) (ms_mem msR) x = aview segs (w_H W3) mem3 x).
{ intros x Hx Hnx.
  apply (kept_of_frame _ _ _ _ _ (fun y => lc_SH cx + 12 <= y < lc_SH cx + 17) HFr); [| exact Hx | exact Hnx].
  intros b wlo whi y Hin Hy.
  lazymatch type of Hin with In ?z ?l => let l' := eval vm_compute in l in change (In z l') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hy; rewrite ?U18, ?U9 in Hy; lia |]).
  destruct Hin. }
assert (GR4 : forall x, apresent (w_H W3) mem3 x -> apresent (w_H W3) (ms_mem msR) x)
  by (intros x Hx; exact (apresent_grows _ _ _ x HG Hx)).
(* the five shadow bytes the run stored *)
lazymatch type of HS2 with st_ok_pi _ _ ?Ex ?ssx (restrict ?Hh ?msx) =>
  let rr := eval vm_compute in (nth_error (ss_mem ssx) 0) in
  lazymatch rr with Some ?r0 => pose proof (can_region_nth (segs := segs) Ex _ (restrict Hh msx) 0 r0 HS2 eq_refl) as HR0 end
end.
cbn [ms_mem restrict] in HR0.
assert (KV : forall i, 12 <= i < 17 -> aview segs (w_H W3) (ms_mem msR) (lc_SH cx + i) = Some 0xf8).
{ intros i Hi. assert (Ei : i = 12 \/ i = 13 \/ i = 14 \/ i = 15 \/ i = 16) by lia.
  destruct Ei as [-> | [-> | [-> | [-> | ->]]]];
    lazymatch goal with |- aview _ _ _ (lc_SH cx + ?o) = _ =>
      rewrite (b2_rg_view _ _ _ _ _ _ _ _ _ o _ _ _ HR0 U18 ltac:(b1_in) ltac:(cbn; lia)) end;
    vm_compute; reflexivity. }
(* the registers at +0x12ec *)
lr_keq HS2 EW3 regs3 (2%bv : bv 5) 2%nat G2. lr_keq HS2 EW3 regs3 (3%bv : bv 5) 3%nat G3.
lr_keq HS2 EW3 regs3 (4%bv : bv 5) 4%nat G4. lr_keq HS2 EW3 regs3 (8%bv : bv 5) 8%nat G8.
lr_keq HS2 EW3 regs3 (9%bv : bv 5) 9%nat G9. lr_keq HS2 EW3 regs3 (18%bv : bv 5) 18%nat G18.
lr_keq HS2 EW3 regs3 (21%bv : bv 5) 21%nat G21. lr_keq HS2 EW3 regs3 (26%bv : bv 5) 26%nat G26.
lr_keq HS2 EW3 regs3 (23%bv : bv 5) 23%nat G23. lr_keq HS2 EW3 regs3 (24%bv : bv 5) 24%nat G24.
lr_reg HS2 (20%bv : bv 5) (w64 LF_S4) G20 ltac:(reflexivity).
lr_reg HS2 (22%bv : bv 5) (w64 7) G22 ltac:(reflexivity).
pmkst HS2.
apply SRr_ret.
lazymatch goal with |- context [mkCfg _ ?mdx] => set (mdR := mdx) in * end.
assert (HL4 : @lc_lcore rc B MT cx op false false (S (lo_k op)) ly3 S3 W3 (ms_regs msR) (ms_mem msR) mdR (e + e3))
  by exact (lc_lcore_sh cx op false (S (lo_k op)) ly3 S3 W3 regs3 mem3 md3 (e + e3) (ms_regs msR) (ms_mem msR) mdR
              HP HB HL3 HJ3 K4 KV GR4 G2 G3 G4 G8 G9 G18 G21 G26).
exists ly3, S3, (ms_regs msR), (ms_mem msR), mdR, (e + e3), a, Bw', (av_c av), (S (lo_k op)).
split; [unfold lc_cfg; reflexivity|].
split; [exact HL4|].
split; [exact Haok|].
split; [exact (lc_b2_op timg_A (lo_B op) a D (lo_c op) (lo_k op) Bw' Hopc Hbm)|].
split.
{ unfold lc_tw. apply (tw_kept TMAP_A (aview segs (w_H W3) mem3)); [exact Htw3|].
  intros x Hx. pose proof (TMAP_A_hull x Hx) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
  apply K4; [lia | lia]. }
split; [split; [exact (eq_trans G24 (lc_reg_kept regsC regs3 24 _ HP3 ltac:(hnf; lia) (eq_trans C24 R24)))
              | exact (eq_trans G23 (lc_reg_kept regsC regs3 23 _ HP3 ltac:(hnf; lia) (eq_trans C23 R23)))]|].
split; [exact G20 | exact G22].
Qed.

End seg.

Print Assumptions lc_bar2_ok.
