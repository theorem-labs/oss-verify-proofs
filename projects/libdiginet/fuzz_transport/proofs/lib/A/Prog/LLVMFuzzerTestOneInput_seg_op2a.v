(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, origin/cold/pg-prog), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/CanKit.v, with its module names changed; 492 of its 559 lines of code are new or changed and 457 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/SrxDeskKit.v, with its module names changed; 1766 of its 1847 lines of code are new or changed and 478 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput_seg_op2a: the segment OP2A of the image-A walk of fuzz_transport.asan's
   LLVMFuzzerTestOneInput, `Lemma lc_op2a_ok`, the statement lc_op2a_stmt of
   lib/A/Prog/LLVMFuzzerTestOneInput_segs.v: from the first instruction of arm 2 (+0x564, lc_st_arm cx op 2) to
   +0x9f8 (lc_st_ann cx op), the start of op_announce (fuzz_transport.c:1052-1066) up to the copy of the MAC.

   The code (pin addresses 0x81264 + offset):
     +0x564  `beqz s7` (no byte left after the op byte) to +0x854 (s3 = 0);
     +0x568 .. +0x57c  the checked load of sel (s3) at s8 = s9 + 1, s8 = s9 + 2, `beq s11, 2` to +0x858;
     +0x588 .. +0x59c  the checked load of the mac byte (a0) at s9 + 2, s8 = s9 + 3, `bne s11, 3` to +0x990;
     +0x5a8 .. +0x5b0  (three bytes) s7 = 0, s4 = 0, `j` +0x9ac;
     +0x990 .. +0x9a8  the checked load of the name byte (s4) at s9 + 3, s8 = s9 + 4, s7 = s11 - 4;
     +0x9ac .. +0x9d8  s6 = a0 & 15 (mac), body's shadow into scope (`sb zero, 12 .. 15(s2)`, `sb 2, 16(s2)`),
                       a2 = 34, s9 = 104(s1) = body, a0 = s9, a1 = 0, `jal __asan_memset` (body, 0, 34);
     +0x858 .. +0x880  the same shadow stores and __asan_memset with one byte or none left; back at +0x884,
                       s7 = s4 = s6 = 0, `j` +0x9e4;
     +0x9dc .. +0x9e0  `bgeu s6, 10` to +0xac0;
     +0x9e4 .. +0x9f4  a0 = s9 + s6, a1 = HOST, a2 = 6, `jal __asan_memcpy` (body + mac, HOST, 6), back at +0x9f8;
     +0xac0 .. +0xad8  `bltu 12, s6` to +0x9f8 (mac > 12: no copy), a0 = 8(s1) + s6 = body - 10 + mac,
                       a1 = OTHER, `j` +0x9f0 (the memcpy above).
   The three checked loads' slow paths (+0x1344, +0x1398, +0x1404) and reports (0x82ca4, 0x82cd4, 0x82cf8) are not
   reached: each check is a shadow token whose obligation is the input block's addressability (a2_ob).

   The proof:
   0. the model's values (lc_ann_vals by the bytes left after the op byte) and the body bytes (a2_body_garr8);
   1. a2_core_kept: lc_core across a step that writes only body's bytes and the frame's shadow (st.v
      lc_core_kept keeps the whole frame and its shadow); a2_lcore_move: the loop facts across such a step, with
      body's shadow put into scope;
   2. the runs (the Pa engine over the G journal, lib/A/Prog/TransportGRunA.v paj_run_x / paj_run_to_x), the two
      intrinsic calls (TransportGCg.v gx_intrin_at at lp_memset / lp_memcpy), and the composition lc_op2a_ok.
   The walk's G journal is used as lc_core states it; nothing here depends on its FP list. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v Img0 ACfn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG AE2y.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportCg DgnTransportCgRun CanKit TransportGFrame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TransportGRwA TransportGRunA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
  LLVMFuzzerTestOneInput_cg LLVMFuzzerTestOneInput_segs LLVMFuzzerTestOneInput_st.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
  LLVMFuzzerTestOneInput_kit_rom_view LLVMFuzzerTestOneInput_kit_src_ro.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require QueueFacts.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TOP := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TOps.
Module QF := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim.QueueFacts.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
(* lia over x / 8 (the frame's shadow granules). *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* ------------------------------------------------------------------ *)
(* 0. The model's values and the body bytes                             *)
(* ------------------------------------------------------------------ *)

(* op_announce's reads from the cursor c1 after the op byte, by the number of bytes left (TOps.v fuzz_u8_m). *)
Lemma a2_vals : forall D c1, 0 <= TOP.fi_n c1 ->
  let av := lc_ann_vals D c1 in
  let o := TOP.fi_off c1 in let n := TOP.fi_n c1 in
  av_sel av = (if n =? 0 then 0 else DSpec.at8 D (Z.to_nat o)) /\
  av_mac av = (if n <=? 1 then 0 else DSpec.at8 D (Z.to_nat (o + 1)) mod 16) /\
  av_nm av = (if n <=? 2 then 0 else DSpec.at8 D (Z.to_nat (o + 2))) /\
  av_c av = (if n <? 3 then TOP.FuzzIn (o + n) 0 else TOP.FuzzIn (o + 3) (n - 3)) /\
  av_body1 av =
    (if av_mac av <? 10 then TW.upd (repeat (DSpec.b8 0) 34) (av_mac av) TC.HOST
     else if av_mac av <? 13 then TW.upd (repeat (DSpec.b8 0) 34) (av_mac av - 10) TC.OTHER
     else repeat (DSpec.b8 0) 34).
Proof.
intros D [o n] Hn. cbn [TOP.fi_off TOP.fi_n] in *. cbv zeta.
unfold lc_ann_vals, TOP.fuzz_u8_m. cbn [TOP.fi_off TOP.fi_n].
repeat (cbn -[DSpec.at8 TW.upd Z.modulo TC.HOST TC.OTHER];
  match goal with
  | |- context [?a =? ?b] => destruct (Z.eqb_spec a b); try lia
  | |- context [?a <=? ?b] => destruct (Z.leb_spec a b); try lia
  | |- context [?a <? ?b] => destruct (Z.ltb_spec a b); try lia
  end).
all: repeat split; try reflexivity; f_equal; lia.
Qed.

Lemma a2_nth_repeat : forall {A : Type} (x d : A) m j, (j < m)%nat -> nth j (repeat x m) d = x.
Proof. intros A x d m. induction m as [|m IH]; intros j Hj; [lia|]. destruct j; [reflexivity|]. cbn. apply IH. lia. Qed.
Lemma a2_nth_skipn : forall {A : Type} (l : list A) (d : A) m j, nth j (skipn m l) d = nth (m + j) l d.
Proof.
intros A l d m. revert l. induction m as [|m IH]; intros l j; [reflexivity|].
destruct l as [|x l]; [cbn; destruct j; reflexivity|]. cbn. apply IH.
Qed.
Lemma a2_nth_firstn : forall {A : Type} (l : list A) (d : A) m j, (j < m)%nat -> nth j (firstn m l) d = nth j l d.
Proof.
intros A l d m. revert l. induction m as [|m IH]; intros l j Hj; [lia|].
destruct l as [|x l]; [cbn; destruct j; reflexivity|]. destruct j; [reflexivity|]. cbn. apply IH. lia.
Qed.

(* The 34 bytes of body after the zero fill and the copy of src (6 bytes) at offset k. *)
Lemma a2_upd_nth : forall (src : list byte) k j, length src = 6%nat -> 0 <= k -> k + 6 <= 34 -> (j < 34)%nat ->
  bv_unsigned (nth j (TW.upd (repeat (DSpec.b8 0) 34) k src) (Z_to_bv 8 0)) =
  if (k <=? Z.of_nat j) && (Z.of_nat j <? k + 6) then bv_unsigned (nth (j - Z.to_nat k) src (Z_to_bv 8 0)) else 0.
Proof.
intros src k j Hl Hk Hk6 Hj. unfold TW.upd. rewrite Hl.
assert (Lf : length (firstn (Z.to_nat k) (repeat (DSpec.b8 0) 34)) = Z.to_nat k)
  by (rewrite length_firstn, repeat_length; lia).
destruct (Z.leb_spec k (Z.of_nat j)) as [H1 | H1]; destruct (Z.ltb_spec (Z.of_nat j) (k + 6)) as [H2 | H2];
  cbn [andb].
- rewrite app_nth2 by lia. rewrite Lf. rewrite app_nth1 by (rewrite Hl; lia). reflexivity.
- rewrite app_nth2 by lia. rewrite Lf. rewrite app_nth2 by (rewrite Hl; lia). rewrite Hl.
  rewrite a2_nth_skipn. rewrite a2_nth_repeat by lia. reflexivity.
- rewrite app_nth1 by lia. rewrite a2_nth_firstn by lia. rewrite a2_nth_repeat by lia. reflexivity.
- lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 1. The loop facts across a step that writes body and its shadow      *)
(* ------------------------------------------------------------------ *)

Section op2a. Context {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
Local Abbreviation segs := tfibsegs.
Local Abbreviation av W m := (aview tfibsegs (w_H W) m).

(* The walk's journal, as lc_core states it. *)
Definition a2_J (cx : lcx) (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model)
    (e2 : Z) : Prop :=
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS 0 [] LLVMF_STK (lc_sp0 cx) []
    (l_ly cx) (l_S cx) (l_W cx) (l_mem cx) (l_md cx) [(LF_CID, l_fpos cx)] ly2 S2 W2 mem2 md2 e2.

(* lc_core across a step that keeps the stack above sp1 - X, the input, the frame's presence, the frame's last word
   and sp, s0, s1, gp, tp (st.v lc_core_kept, without keeping the frame's other bytes). *)
Lemma a2_core_kept : forall cx ly' S' W' regs' mem' md' e (X : Z) ly2 S2 (W2 : world segs) regs2 mem2 md2 e2,
  AR_laws segs B -> @lc_base rc B MT XL RLO RHI cx ->
  @lc_core rc B cx ly' S' W' regs' mem' md' e ->
  a2_J cx ly2 S2 W2 mem2 md2 e2 ->
  frames S2 = frames S' ->
  Permutation (ablocks B ly2 S2) (ablocks B ly' S') ->
  (forall r, In r [2; 3; 4; 8; 9] -> YK11.getr regs2 (Z_to_bv 5 r) = YK11.getr regs' (Z_to_bv 5 r)) ->
  0 <= X <= LLVMF_STK - 336 ->
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (lc_sp1 cx - X <= a < lc_sp1 cx) -> av W2 mem2 a = av W' mem' a) ->
  (forall i, 0 <= i < l_n cx -> av W2 mem2 (l_p cx + i) = av W' mem' (l_p cx + i)) ->
  (forall a, lc_F cx <= a < lc_F cx + LF_FBYTES -> apresent (w_H W2) mem2 a) ->
  (forall a, lc_F cx + LF_FBYTES - 8 <= a < lc_F cx + LF_FBYTES -> av W2 mem2 a = av W' mem' a) ->
  @lc_core rc B cx ly2 S2 W2 regs2 mem2 md2 e2.
Proof.
intros cx ly' S' W' regs' mem' md' e X ly2 S2 W2 regs2 mem2 md2 e2 LAWS HB HC HJ2 HFR2 HP2 HPR HX KA KIN KFP KFL.
pose proof (lc_geom B MT XL RLO RHI cx ly' S' W' regs' mem' md' e HB HC) as G.
destruct G as [HARg Hsp0al Hstk Hsp1c HFaddr HFin Hn HINg HLIVEg].
destruct HC as (HJ & Hfrs & HlyF & HPERM & Rsp & R8 & R9 & Rgp & Rtp & Hsp1 & Hsp1al & HSAV & HF4096 & HFal & HFceil &
  HFpres & HFL & HIN).
pose proof HJ2 as (_ & _ & (memS2 & HJd2 & _) & _).
pose proof HJd2 as (HAR2 & Hly2 & _).
destruct Hly2 as (_ & _ & _ & _ & _ & EF2 & _).
destruct Hstk as (Hceil & Hslo & Hshi & H47).
change (2 ^ 47) with 140737488355328 in H47.
pose proof asan_consts as ((CVlo & CVhi) & _).
assert (KAhi : forall a, lc_sp1 cx <= a <= lc_sp0 cx -> av W2 mem2 a = av W' mem' a).
{ intros a Ha. apply KA; [change (2 ^ 64) with 18446744073709551616; lia | lia]. }
split; [exact HJ2|].
split; [rewrite HFR2; exact Hfrs|].
split; [exact EF2|].
split; [exact (Permutation_trans HP2 HPERM)|].
split; [exact (eq_trans (HPR 2 ltac:(cbn; tauto)) Rsp)|].
split; [exact (eq_trans (HPR 8 ltac:(cbn; tauto)) R8)|].
split; [exact (eq_trans (HPR 9 ltac:(cbn; tauto)) R9)|].
split; [exact (eq_trans (HPR 3 ltac:(cbn; tauto)) Rgp)|].
split; [exact (eq_trans (HPR 4 ltac:(cbn; tauto)) Rtp)|].
split; [exact Hsp1|]. split; [exact Hsp1al|].
split.
{ unfold lc_saved in HSAV |- *. rewrite Forall_forall in HSAV |- *. intros o Ho.
  assert (Hor : 8 <= fst o <= 104).
  { unfold LF_SAVED in Ho. repeat (destruct Ho as [<- | Ho]; [cbn; lia|]). destruct Ho. }
  rewrite (rdword_ext (av W' mem') (av W2 mem2) (lc_sp0 cx - fst o))
    by (intros j Hj; apply KAhi; unfold LF_FRAME in Hsp1; lia).
  exact (HSAV o Ho). }
split; [exact HF4096|]. split; [exact HFal|]. split; [exact HFceil|].
split; [exact KFP|].
split; [rewrite (rdword_ext (av W' mem') (av W2 mem2) (lc_F cx + LF_FBYTES - 8))
          by (intros j Hj; apply KFL; unfold LF_FBYTES in *; lia); exact HFL|].
destruct HIN as (HPAYg & HPAYv).
destruct (Z_lt_le_dec 0 (l_n cx)) as [Hn0 | Hn0].
- split.
  + apply (lc_garr8_kept (w_H W') (w_H W2) mem' mem2 (l_p cx) _); [|exact HPAYg].
    intros j Hj. rewrite length_map in Hj. destruct Hn as (_ & Hnl). rewrite <- Hnl in Hj.
    exact (KIN j ltac:(lia)).
  + intros i Hi. rewrite (KIN i Hi). exact (HPAYv i Hi).
- destruct Hn as (Hn1 & Hnl). split.
  + destruct (l_pl cx) as [|b0 pl0] eqn:Epl; [apply garr8_nil|]. exfalso. cbn [length] in Hnl. lia.
  + intros i Hi. lia.
Qed.

(* The bytes a step of this segment may change: the callee stack window [sp1 - X, sp1), body [F + 96, F + 130) and
   body's five shadow bytes [SH + 12, SH + 17). *)
Definition a2_out (cx : lcx) (X a : Z) : Prop :=
  (lc_sp1 cx - X <= a < lc_sp1 cx) \/ (lc_F cx + 96 <= a < lc_F cx + 130) \/ (lc_SH cx + 12 <= a < lc_SH cx + 17).

(* The loop facts and the world relation across such a step, at the same allocator state, events and W: the frame's
   shadow is given by the caller (bin' says whether body's is in scope). *)
Lemma a2_move : forall cx op cin bin bin' k ly S (W : world segs) regs mem md e regs2 mem2 md2 X,
  AR_laws segs B -> gx_ok segs B TG.G_HARNESS -> @lc_base rc B MT XL RLO RHI cx ->
  @lc_lcore rc B MT cx op cin bin k ly S W regs mem md e -> lc_tw W mem (lo_B op) ->
  a2_J cx ly S W mem2 md2 e ->
  (forall r, In r [2; 3; 4; 8; 9; 18; 21; 26] -> YK11.getr regs2 (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)) ->
  0 <= X <= LLVMF_STK - 336 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ a2_out cx X a -> av W mem2 a = av W mem a) ->
  (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem2 a) ->
  lc_fsh cx (av W mem2) cin bin' ->
  @lc_lcore rc B MT cx op cin bin' k ly S W regs2 mem2 md2 e /\ lc_tw W mem2 (lo_B op).
Proof.
intros cx op cin bin bin' k ly S W regs mem md e regs2 mem2 md2 X LAWS HGX HB HL HTW HJ2 HR HX K Hgr HSH2.
destruct HL as (HC & (F18 & F26) & HSP & HSH & HOK & Hev & HM & R21).
pose proof (lc_geom B MT XL RLO RHI cx ly S W regs mem md e HB HC) as G.
destruct G as [HARg Hsp0al Hstk Hsp1c HFaddr HFin Hn HINg HLIVEg].
pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hsp1 & _ & _ & HF4096 & HFal & HFceil & HFpres & _).
destruct (frames_bounds segs B LAWS ly S W mem md LF_CID (l_fpos cx) HARg HFin) as (_ & _ & HFapp).
rewrite HFaddr in HFapp. change (fs_frame_bytes LF_CID) with 256 in HFapp.
destruct Hstk as (Hceil & Hslo & Hshi & H47).
pose proof asan_consts as ((CVlo & CVhi) & C2 & C3 & C4 & C5).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
assert (ESH : lc_SH cx = SHADOW_OFF + lc_F cx / 8) by reflexivity.
assert (HSHr : SHADOW_OFF <= lc_SH cx /\ lc_SH cx + 32 <= alloc_ceiling)
  by (rewrite ESH; unfold SHADOW_OFF in *; unfold LF_FBYTES in HFceil; lia).
unfold LLVMF_STK in HX.
(* the bytes from alloc_ceiling up: off body (below the ceiling) and off its shadow (below the ceiling) *)
assert (KA : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (lc_sp1 cx - X <= a < lc_sp1 cx) -> av W mem2 a = av W mem a).
{ intros a Ha Hw. apply K; [lia|]. unfold a2_out, LF_FBYTES in HFceil |- *.
  intros [H1 | [H1 | H1]]; [exact (Hw H1) | clear - H1 Ha HFceil; lia | clear - H1 Ha HSHr; lia]. }
(* the input: a block, below the ceiling, off the frame, in application memory *)
assert (KIN : forall i, 0 <= i < l_n cx -> av W mem2 (l_p cx + i) = av W mem (l_p cx + i)).
{ intros i Hi. pose proof (HINg ltac:(lia)) as InP.
  destruct (al_blocks _ _ LAWS ly S W mem md (l_p cx) (l_n cx) HARg InP) as (_ & Hb4 & Hbc & Hbapp & _).
  pose proof (sep_block_frame segs B LAWS ly S W mem md _ _ _ _ HARg InP HFin) as Hd.
  rewrite HFaddr in Hd. change (fs_frame_bytes LF_CID) with 256 in Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd.
  pose proof (req_size_pos (l_n cx) ltac:(lia)) as (Hq1 & Hq2).
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hbapp.
  apply K; [lia|]. unfold a2_out. unfold SHADOW_OFF, LLVMF_STK, LF_FRAME in *. lia. }
split.
- split.
  { apply (a2_core_kept cx ly S W regs mem md e X ly S W regs2 mem2 md2 e LAWS HB HC HJ2 eq_refl
      (Permutation_refl _)).
    + intros r Hr. apply HR. cbn [In] in Hr |- *. tauto.
    + exact HX.
    + exact KA.
    + exact KIN.
    + intros a Ha. apply Hgr. exact (HFpres a Ha).
    + intros a Ha. unfold SHADOW_OFF, LLVMF_STK, LF_FRAME, LF_FBYTES in *.
      apply K; [lia | unfold a2_out; lia]. }
  split; [split; [exact (eq_trans (HR 18 ltac:(cbn; tauto)) F18) | exact (eq_trans (HR 26 ltac:(cbn; tauto)) F26)]|].
  split.
  { apply (lc_spills_kept cx (lf_spill_loop (lc_F cx)) (av W mem) (av W mem2));
      [|intros a Ha; apply KA; unfold LLVMF_STK, LF_FRAME in *; lia|exact HSP].
    intros o Ho.
    pose proof (lf_spill_vals (lc_F cx) ltac:(lia) ltac:(unfold LF_FBYTES in *; lia)) as HV.
    rewrite Forall_forall in HV. destruct (HV o Ho) as (_ & _ & H8 & H192). lia. }
  split; [exact HSH2|]. split; [exact HOK|]. split; [exact Hev|]. split; [exact HM|].
  exact (eq_trans (HR 21 ltac:(cbn; tauto)) R21).
- apply (tw_kept_GA (av W mem) (av W mem2) (lo_B op) HTW).
  intros b n i Hin Hi.
  pose proof (TG.G_HARNESS_in_hull (b, n) Hin) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh. cbn in Hh.
  apply K; [lia|].
  unfold a2_out. intros [Hw | [Hb | Hs]].
  + unfold LLVMF_STK, LF_FRAME in *. lia.
  + (* body is a frame byte, not an image byte; every byte of G is *)
    assert (HinG : inG TG.G_HARNESS (b + i))
      by (unfold inG; apply Exists_exists; exists (b, n); split; [exact Hin | unfold in_zr; cbn; lia]).
    destruct (HGX _ HinG) as [Himg _].
    apply (frm_img segs B LAWS ly S W mem md LF_CID (l_fpos cx) (b + i) HARg HFin); [|exact Himg].
    rewrite HFaddr. change (fs_frame_bytes LF_CID) with 256. lia.
  + unfold SHADOW_OFF in *. lia.
Qed.

(* body's five shadow bytes after the stores of +0x9b8 .. +0x9c8 (or +0x85c ..): 0, 0, 0, 0, 2. *)
Definition A2_BSH : list Z := [0; 0; 0; 0; 2].

Lemma a2_body_hull : forall cx (r : reader) d n,
  lc_F cx mod 64 = 0 -> 0 <= lc_F cx -> lc_F cx + 96 <= d -> d + n <= lc_F cx + 130 -> 0 < n ->
  (forall i, 0 <= i < 32 -> r (lc_SH cx + i) <> None) ->
  shadow_hull_vis r d n.
Proof.
intros cx r d n HF64 HF0 Hd Hdn Hn Hvis s Hs.
pose proof (Z.div_mod (lc_F cx) 64 ltac:(lia)) as DF. rewrite HF64, Z.add_0_r in DF.
set (k := lc_F cx / 64) in *.
assert (HF8 : lc_F cx / 8 = 8 * k) by (rewrite DF; replace (64 * k) with (8 * k * 8) by lia; apply Z.div_mul; lia).
assert (ESH : lc_SH cx = SHADOW_OFF + 8 * k) by (unfold lc_SH; rewrite HF8; reflexivity).
unfold shadow_addr, SHADOW_OFF in Hs. unfold SHADOW_OFF in ESH.
pose proof (Z.div_mod d 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound d 8 ltac:(lia)) as M1.
pose proof (Z.div_mod (d + n - 1) 8 ltac:(lia)) as D2. pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)) as M2.
set (u := d / 8) in *. set (v := (d + n - 1) / 8) in *.
pose proof (Z.div_mod (2147450880 + u) 8 ltac:(lia)) as D3. pose proof (Z.mod_pos_bound (2147450880 + u) 8 ltac:(lia)) as M3.
pose proof (Z.div_mod (2147450880 + v) 8 ltac:(lia)) as D4. pose proof (Z.mod_pos_bound (2147450880 + v) 8 ltac:(lia)) as M4.
replace s with (lc_SH cx + (s - lc_SH cx)) by lia. apply Hvis. rewrite ESH. lia.
Qed.

(* The intrinsic's address. *)
Definition a2_ipc (o : memop) : Z :=
  match o with OCpy => transport_sigma TS___asan_memcpy | OSet => transport_sigma TS___asan_memset end.

(* A call of memset or memcpy whose destination is in body, with body's shadow in scope: the loop facts and the world
   relation hold after it, at the same allocator state and events. *)
Lemma a2_icall : forall cx op k (o : memop) ly S (W : world segs) regsT memT mdT e d x n raw,
  @lp_prem rc B MT XL RLO RHI -> @lc_base rc B MT XL RLO RHI cx ->
  @lc_lcore rc B MT cx op false true k ly S W regsT memT mdT e -> lc_tw W memT (lo_B op) ->
  YK11.getr regsT 10 = w64 d -> YK11.getr regsT 11 = w64 x -> YK11.getr regsT 12 = w64 n ->
  YK11.getr regsT 1 = raw -> YK0s.ret_ok raw ->
  lc_F cx + 96 <= d -> d + n <= lc_F cx + 130 -> 0 < n ->
  (match o with OCpy => (x = TRANS_HOST \/ x = TRANS_OTHER) /\ n = 6 | OSet => True end) ->
  SRr segs W (mkCfg (@YK11.mkst (l_fx cx) regsT (Z_to_bv 64 (a2_ipc o)) memT (YK11.seg_rom segs)) mdT)
    (fun W' c' => W' = W /\ exists regs2 mem2 md2,
       c' = mkCfg (@YK11.mkst (l_fx cx) regs2 raw mem2 (YK11.seg_rom segs)) md2 /\
       @lc_lcore rc B MT cx op false true k ly S W regs2 mem2 md2 e /\ lc_tw W mem2 (lo_B op) /\
       aregs_preserved regsT regs2 /\
       (forall i, 0 <= i < n -> av W mem2 (d + i) =
          match o with OCpy => av W memT (x + i) | OSet => Some (x mod 256) end) /\
       (forall a, lc_F cx + 96 <= a < lc_F cx + 130 -> ~ (d <= a < d + n) -> av W mem2 a = av W memT a)).
Proof.
intros cx op k o ly S W regsT memT mdT e d x n raw HP HB HL HTW R10 R11 R12 R1 Hraw Hd Hdn Hn Ho.
pose proof (lp_laws _ _ _ _ _ HP) as LAWS.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned _ _ _ _ _ HP)) as HGX.
pose proof HL as (HC & HFR & HSP & HFSH & HOK & He & HMT & R21).
pose proof (lc_geom B MT XL RLO RHI cx ly S W regsT memT mdT e HB HC) as GEO.
destruct GEO as [HAR Hsp0al Hstk Hsp1c HFaddr HFin Hn0 HINg HLIVE].
pose proof HC as (HJ & Hfrs & HlyF & HPERM & Rsp & R8 & R9 & Rgp & Rtp & Hsp1 & Hsp1al & HSAV & HF4096 & HFal &
  HFceil & HFpres & HFL & HIN).
destruct (frames_bounds segs B LAWS ly S W memT mdT LF_CID (l_fpos cx) HAR HFin) as (_ & _ & HFapp).
rewrite HFaddr in HFapp. change (fs_frame_bytes LF_CID) with 256 in HFapp.
destruct Hstk as (Hceil & Hslo & Hshi & H47).
pose proof asan_consts as (CC1 & CC2 & CC3 & CC4 & CC5).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
unfold LLVMF_STK, LF_FRAME, LF_FBYTES in *.
assert (HspZ : spZ regsT = lc_sp1 cx).
{ unfold spZ. refine (eq_trans (f_equal (@bv_unsigned 64) Rsp) _). apply unsigned_lit_small. lia. }
(* body's shadow and the frame's shadow bytes *)
assert (HVIS : forall i, 0 <= i < 32 -> av W memT (lc_SH cx + i) <> None) by (intros i Hi; rewrite (HFSH i Hi); discriminate).
assert (HRA : range_addressable (av W memT) SHADOW_OFF (lc_F cx + 96) 34).
{ intros a Ha.
  assert (Hq : lc_F cx = 64 * (lc_F cx / 64)) by (pose proof (Z.div_mod (lc_F cx) 64 ltac:(lia)); lia).
  assert (HF8 : lc_F cx / 8 = 8 * (lc_F cx / 64)).
  { rewrite Hq at 1. replace (64 * (lc_F cx / 64)) with (8 * (lc_F cx / 64) * 8) by lia. apply Z.div_mul. lia. }
  pose proof (Z.div_mod a 8 ltac:(lia)) as D8. pose proof (Z.mod_pos_bound a 8 ltac:(lia)) as M8.
  pose proof (HFSH (a / 8 - lc_F cx / 8) ltac:(lia)) as H.
  unfold lc_SH in H. unfold shadow_of_addr.
  replace (SHADOW_OFF + lc_F cx / 8 + (a / 8 - lc_F cx / 8)) with (SHADOW_OFF + a / 8) in H by lia.
  eexists. split; [exact H|]. unfold saddr_ok.
  assert (E : a / 8 - lc_F cx / 8 = 12 \/ a / 8 - lc_F cx / 8 = 13 \/ a / 8 - lc_F cx / 8 = 14 \/
              a / 8 - lc_F cx / 8 = 15 \/ a / 8 - lc_F cx / 8 = 16) by lia.
  destruct E as [E | [E | [E | [E | E]]]]; rewrite E;
    match goal with |- context [Z.to_nat ?k] => let v := eval vm_compute in (Z.to_nat k) in change (Z.to_nat k) with v end;
    cbn; [left; reflexivity .. |].
  right. clear - Ha D8 M8 HF8 Hq E. lia. }
(* the call *)
eapply SRr_mono.
{ eapply (gx_intrin_at (fx := l_fx cx) (SK := AE2k.tfib_sink_head) segs B LAWS transport_segs_low o (a2_ipc o)
    ltac:(destruct o; [exact (lp_memcpy _ _ _ _ _ HP (l_fx cx)) | exact (lp_memset _ _ _ _ _ HP (l_fx cx))])
    TG.G_HARNESS W regsT memT LLVMF_STK (lc_sp0 cx) [] (l_ly cx) (l_S cx) (l_W cx) (l_mem cx) (l_md cx)
    [(LF_CID, l_fpos cx)] ly S mdT e d x n (lc_sp1 cx - lc_sp0 cx) raw HGX G_HARNESS_rw HJ R10 R11 R12).
  - lia.
  - lia.
  - lia.
  - lia.
  - pose proof (Z.div_mod (lc_sp1 cx) 32 ltac:(lia)) as D1. rewrite Hsp1al, Z.add_0_r in D1.
    pose proof (Z.div_mod (lc_sp0 cx) 16 ltac:(lia)) as D2. rewrite Hsp0al, Z.add_0_r in D2.
    rewrite D1, D2. replace (32 * (lc_sp1 cx / 32) - 16 * (lc_sp0 cx / 16)) with
      ((2 * (lc_sp1 cx / 32) - lc_sp0 cx / 16) * 16) by ring. apply Z.mod_mul. lia.
  - lia.
  - unfold ESTACK, LLVMF_STK. lia.
  - exact Rgp.
  - exact Rtp.
  - exact R1.
  - exact Hraw.
  - eapply (transport_twr_ok_g_intro segs B LAWS); [exact HJ|].
    intros a Ha. left. split.
    + right. right. right. exists LF_CID, (l_fpos cx). split; [left; reflexivity|]. left.
      unfold in_zr. cbn [fst snd]. rewrite HFaddr. change (fs_frame_bytes LF_CID) with 256. lia.
    + rewrite HspZ. unfold ESTACK. lia.
  - unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd. lia.
  - eapply range_addressable_sub; [exact HRA | lia | lia].
  - intros _. apply (a2_body_hull cx _ d n HFal ltac:(lia) Hd Hdn Hn HVIS).
  - destruct o; [|exact I].
    destruct Ho as (Hx & ->).
    pose proof (lc_src_ro_ok B MT XL RLO RHI (lc_rom_view_ok B MT XL RLO RHI) HP cx ly S W regsT memT mdT e x 6 HB HC
      ltac:(destruct Hx as [-> | ->]; cbn; tauto)) as HSRC.
    assert (Hximg : forall a, x <= a < x + 6 -> in_img segs a).
    { intros a Ha. destruct Hx as [-> | ->].
      all: apply (seg_rom_in_img segs a ltac:(unfold TRANS_HOST, TRANS_OTHER in *; lia)).
      all: destruct (trans_ro_rd_rom_clean a) as (_ & bb & Hbb); [|rewrite Hbb; discriminate].
      all: unfold trans_in_ro_rd, TRANS_RO_RD, TRANS_RO_GLOBALS; apply Exists_exists.
      - exists (TRANS_HOST, 6). split; [cbn; tauto | unfold in_zr; cbn [fst snd]; lia].
      - exists (TRANS_OTHER, 6). split; [cbn; tauto | unfold in_zr; cbn [fst snd]; lia]. }
    destruct HSRC as [HBLK | (_ & HRD)].
    { exfalso. destruct HBLK as (bA & nA & Hin & H1 & H2).
      pose proof (req_size_pos nA ltac:(destruct (al_blocks _ _ LAWS ly S W memT mdT bA nA HAR Hin) as (Hnn & _); lia))
        as (Hq1 & Hq2).
      exact (blk_img segs B LAWS ly S W memT mdT bA nA x HAR Hin ltac:(lia) (Hximg x ltac:(lia))). }
    destruct HRD as (HV & HRAx & HHV & HAM & Hx0 & Hx1).
    assert (Hdimg : forall a, d <= a < d + 6 -> ~ in_img segs a).
    { intros a Ha Hi. apply (frm_img segs B LAWS ly S W memT mdT LF_CID (l_fpos cx) a HAR HFin); [|exact Hi].
      rewrite HFaddr. change (fs_frame_bytes LF_CID) with 256. lia. }
    split; [lia|]. split; [lia|]. split.
    { intros a Ha. split; [exact (HV a Ha)|]. rewrite HspZ. unfold ESTACK.
      pose proof (transport_segs_low a (Hximg a Ha)) as Hl. unfold kLowMemEnd in Hl. lia. }
    split.
    { destruct (Z_le_gt_dec (d + 6) x) as [H1 | H1]; [left; exact H1|].
      destruct (Z_le_gt_dec (x + 6) d) as [H2 | H2]; [right; exact H2|].
      exfalso. destruct (Z_le_gt_dec d x) as [H3 | H3].
      - exact (Hdimg x ltac:(lia) (Hximg x ltac:(lia))).
      - exact (Hdimg d ltac:(lia) (Hximg d ltac:(lia))). }
    split; [exact HAM|]. split; [exact HRAx|]. intros _. exact HHV. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HPR & R10' & HBY & HK & HPG).
split; [reflexivity|]. exists regs2, mem2, md2. split; [reflexivity|].
assert (KO : forall a, 0 <= a < 2 ^ 64 -> ~ a2_out cx 4096 a -> av W mem2 a = av W memT a).
{ intros a Ha Hout. apply HK; [exact Ha | | ].
  - intros Ha'. apply Hout. right. left. lia.
  - replace (lc_sp0 cx + (lc_sp1 cx - lc_sp0 cx) - ESTACK) with (lc_sp1 cx - 4096) by (unfold ESTACK; lia).
    replace (lc_sp0 cx + (lc_sp1 cx - lc_sp0 cx)) with (lc_sp1 cx) by lia.
    intros Hw. apply Hout. left. exact Hw. }
destruct (a2_move cx op false true true k ly S W regsT memT mdT e regs2 mem2 md2 4096 LAWS HGX HB HL HTW HJ2)
  as [HL2 HTW2].
- intros r Hr. apply HPR. unfold acallee_saved. cbn [In] in Hr. lia.
- unfold LLVMF_STK. lia.
- exact KO.
- exact HPG.
- assert (HSHb : SHADOW_OFF <= lc_SH cx /\ lc_SH cx + 32 <= 17594333495296).
  { pose proof (Z.div_pos (lc_F cx) 8 ltac:(lia) ltac:(lia)).
    assert (lc_F cx / 8 <= 0x7fffff800000 / 8) by (apply Z.div_le_mono; lia).
    change (0x7fffff800000 / 8) with 0xffffff00000 in *. unfold lc_SH, SHADOW_OFF in *. lia. }
  intros i Hi. rewrite (HK (lc_SH cx + i)); [exact (HFSH i Hi) | unfold SHADOW_OFF in *; lia | | ].
  + unfold SHADOW_OFF in *. lia.
  + replace (lc_sp0 cx + (lc_sp1 cx - lc_sp0 cx) - ESTACK) with (lc_sp1 cx - 4096) by (unfold ESTACK; lia).
    replace (lc_sp0 cx + (lc_sp1 cx - lc_sp0 cx)) with (lc_sp1 cx) by lia. unfold SHADOW_OFF in *. lia.
- refine (conj HL2 (conj HTW2 (conj HPR (conj HBY _)))).
  intros a Ha Hd'. apply HK; [lia | exact Hd' |].
  replace (lc_sp0 cx + (lc_sp1 cx - lc_sp0 cx) - ESTACK) with (lc_sp1 cx - 4096) by (unfold ESTACK; lia).
  replace (lc_sp0 cx + (lc_sp1 cx - lc_sp0 cx)) with (lc_sp1 cx) by lia. lia.
Qed.

End op2a.

(* ------------------------------------------------------------------ *)
(* 2. The seats of the runs                                             *)
(* ------------------------------------------------------------------ *)

(* Atoms 0 .. 31: the registers at the run's start; 32 .. 34: the input bytes sel, mac, name; 35, 36: the spill values
   body = F + 96 and body - 10 = F + 86. *)
Definition a2_rgI1 : YP09.region := YP09.mkRegion (Some 24%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))].
Definition a2_rgI2 : YP09.region :=
  YP09.mkRegion (Some 25%nat) 2 4 0 0 [YP09.mkChunk 2 (CVal 1 (SOff 33 0)); YP09.mkChunk 3 (CVal 1 (SOff 34 0))].
Definition a2_rgSH : YP09.region := YP09.mkRegion (Some 18%nat) 12 17 12 17 [].
Definition a2_rgS : YP09.region :=
  YP09.mkRegion (Some 9%nat) 8 112 0 0 [YP09.mkChunk 8 (CVal 8 (SOff 36 0)); YP09.mkChunk 104 (CVal 8 (SOff 35 0))].
Definition a2_ss3 : sstate :=
  mkSS 0x564 sr_atoms [a2_rgI1; a2_rgI2] None
    (mkFacts [(23%nat, mkAF 3 (2 ^ 47) 0); (27%nat, mkAF 4 (2 ^ 47) 0); (24%nat, YC4b.PTR 0); (25%nat, YC4b.PTR 0);
              (26%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
              (32%nat, mkAF 0 255 0); (33%nat, mkAF 0 255 0); (34%nat, mkAF 0 255 0)] [] []).
Definition a2_rgI2a : YP09.region := YP09.mkRegion (Some 25%nat) 2 3 0 0 [YP09.mkChunk 2 (CVal 1 (SOff 33 0))].
(* The seats of cases n1 = 0, 1, 2 at the arm. *)
Definition a2_ssK (k : Z) : sstate :=
  mkSS 0x564 sr_atoms (if k =? 0 then [] else if k =? 1 then [a2_rgI1] else [a2_rgI1; a2_rgI2a]) None
    (mkFacts [(23%nat, mkAF k k 0); (27%nat, mkAF (k + 1) (k + 1) 0); (24%nat, YC4b.PTR 0); (25%nat, YC4b.PTR 0);
              (26%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (32%nat, mkAF 0 255 0); (33%nat, mkAF 0 255 0)] [] []).
(* The seat of the stretch that brings body's shadow into scope and calls memset, at +0x9ac or +0x858. *)
Definition a2_ssB (pc : Z) : sstate :=
  mkSS pc sr_atoms [a2_rgSH; a2_rgS] None (mkFacts [(18%nat, mkAF SHADOW_OFF (2 ^ 46) 0)] [] []).
(* The seats of the stretch to memcpy: at +0x9dc (s6 in [lo, hi], the spill slot 8(s1) read) and at +0x884. *)
Definition a2_ssC (lo hi : Z) : sstate :=
  mkSS 0x9dc sr_atoms [a2_rgS] None (mkFacts [(22%nat, mkAF lo hi 0)] [] []).
Definition a2_ssD : sstate := mkSS 0x884 sr_atoms [] None (mkFacts [] [] []).
Definition A2_Bx : sv := SOff 26 0.

Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

Definition a2_E (regs : bvmap 5 word) (b1 b2 b3 F : Z) : env :=
  Eimg (PI := PI_transport) (Ereg regs [w64 b1; w64 b2; w64 b3; w64 (F + 96); w64 (F + 86)]).

Lemma a2_env_img : forall regs b1 b2 b3 F, img_env VAL A_LIM (a2_E regs b1 b2 b3 F).
Proof. intros. unfold a2_E. apply Eimg_env. Qed.
Lemma a2_ew_reg : forall regs b1 b2 b3 F n (r : bv 5), Z.of_nat n = bv_unsigned r ->
  ew (a2_E regs b1 b2 b3 F) n = YK11.getr regs r.
Proof. intros. unfold a2_E. apply can_ew_Eimg_Ereg_nat. assumption. Qed.
Lemma a2_ew_x : forall regs b1 b2 b3 F j, (j < 5)%nat ->
  ew (a2_E regs b1 b2 b3 F) (32 + j) = nth j [w64 b1; w64 b2; w64 b3; w64 (F + 96); w64 (F + 86)] (Z_to_bv 64 0).
Proof. intros. unfold a2_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. Qed.

(* The seat of case n1 >= 3 at the arm (+0x564). q = p + o0 (s9), the op byte's address. *)
Lemma a2_entry3 : forall (W : world segs) regs mem q n1 b1 b2 b3 F,
  YK11.getr regs 25 = w64 q -> YK11.getr regs 24 = w64 (q + 1) -> YK11.getr regs 23 = w64 n1 ->
  YK11.getr regs 27 = w64 (n1 + 1) -> YK11.getr regs 26 = w64 SHADOW_OFF ->
  4096 <= q -> q + 4 <= YM05.alloc_ceiling -> 3 <= n1 <= 2 ^ 47 - 1 ->
  val_mem segs (mrestrict (w_H W) mem) (q + 1) 1 b1 -> val_mem segs (mrestrict (w_H W) mem) (q + 2) 1 b2 ->
  val_mem segs (mrestrict (w_H W) mem) (q + 3) 1 b3 ->
  0 <= b1 < 256 -> 0 <= b2 < 256 -> 0 <= b3 < 256 ->
  st_ok_pi segs VAL (a2_E regs b1 b2 b3 F) a2_ss3
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + 0x564)) mem (YK11.seg_rom segs))).
Proof.
intros W regs mem q n1 b1 b2 b3 F R25 R24 R23 R27 R26 Hq0 Hq1 Hn1 V1 V2 V3 B1 B2 B3.
set (E := a2_E regs b1 b2 b3 F).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs r)
  by (intros; apply a2_ew_reg; assumption).
pose proof (a2_ew_x regs b1 b2 b3 F 0 ltac:(lia)) as E32. pose proof (a2_ew_x regs b1 b2 b3 F 1 ltac:(lia)) as E33.
pose proof (a2_ew_x regs b1 b2 b3 F 2 ltac:(lia)) as E34.
cbn [Nat.add nth] in E32, E33, E34. fold E in E32, E33, E34.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (U24 : bv_unsigned (ew E 24) = q + 1) by (rewrite (EE 24%nat 24%bv eq_refl), R24; apply unsigned_lit_small; lia).
assert (U25 : bv_unsigned (ew E 25) = q) by (rewrite (EE 25%nat 25%bv eq_refl), R25; apply unsigned_lit_small; lia).
assert (U23 : bv_unsigned (ew E 23) = n1) by (rewrite (EE 23%nat 23%bv eq_refl), R23; apply unsigned_lit_small; lia).
assert (U27 : bv_unsigned (ew E 27) = n1 + 1)
  by (rewrite (EE 27%nat 27%bv eq_refl), R27; apply unsigned_lit_small; lia).
assert (U26 : bv_unsigned (ew E 26) = SHADOW_OFF)
  by (rewrite (EE 26%nat 26%bv eq_refl), R26; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U32 : bv_unsigned (ew E 32) = b1) by (rewrite E32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = b2) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = b3) by (rewrite E34; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. unfold a2_ss3.
apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold a2_rgI1, a2_rgI2.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
    rewrite ?U24, ?U25.
  + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val segs E _ (q + 1) 0 1 (SOff 32 0) b1);
      [rewrite denot_lit_U, (U_atom E 32 b1 E32 ltac:(lia)); reflexivity | cbn; lia | cbn; lia |].
    rewrite Z.add_0_r. exact V1.
  + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    * apply (chunk_ok_val segs E _ q 2 1 (SOff 33 0) b2);
        [rewrite denot_lit_U, (U_atom E 33 b2 E33 ltac:(lia)); reflexivity | cbn; lia | cbn; lia | exact V2].
    * apply (chunk_ok_val segs E _ q 3 1 (SOff 34 0) b3);
        [rewrite denot_lit_U, (U_atom E 34 b3 E34 ltac:(lia)); reflexivity | cbn; lia | cbn; lia | exact V3].
- apply pairwise_disjoint_of_extents.
  unfold a2_rgI1, a2_rgI2, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val zpairwise_disjoint zall_disjoint].
  rewrite U24, U25. unfold zdisj. cbn [fst snd]. lia.
- unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok, YC4b.PTR. cbn [af_lo af_hi af_al2].
  rewrite U23, U27, U24, U25, U26, U32, U33, U34, !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; try exact I; unfold SHADOW_OFF in *; lia.
Qed.

(* The seat of case n1 = k in {0, 1, 2} at the arm. *)
Lemma a2_entryK : forall (W : world segs) regs mem q k b1 b2 F,
  YK11.getr regs 25 = w64 q -> YK11.getr regs 24 = w64 (q + 1) -> YK11.getr regs 23 = w64 k ->
  YK11.getr regs 27 = w64 (k + 1) -> YK11.getr regs 26 = w64 SHADOW_OFF ->
  4096 <= q -> q + 1 <= YM05.alloc_ceiling -> k = 0 \/ k = 1 \/ k = 2 ->
  (1 <= k -> val_mem segs (mrestrict (w_H W) mem) (q + 1) 1 b1) ->
  (2 <= k -> val_mem segs (mrestrict (w_H W) mem) (q + 2) 1 b2) ->
  0 <= b1 < 256 -> 0 <= b2 < 256 ->
  st_ok_pi segs VAL (a2_E regs b1 b2 0 F) (a2_ssK k)
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + 0x564)) mem (YK11.seg_rom segs))).
Proof.
intros W regs mem q k b1 b2 F R25 R24 R23 R27 R26 Hq0 Hq1 Hk V1 V2 B1 B2.
set (E := a2_E regs b1 b2 0 F).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs r)
  by (intros; apply a2_ew_reg; assumption).
pose proof (a2_ew_x regs b1 b2 0 F 0 ltac:(lia)) as E32. pose proof (a2_ew_x regs b1 b2 0 F 1 ltac:(lia)) as E33.
cbn [Nat.add nth] in E32, E33. fold E in E32, E33.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (U24 : bv_unsigned (ew E 24) = q + 1) by (rewrite (EE 24%nat 24%bv eq_refl), R24; apply unsigned_lit_small; lia).
assert (U25 : bv_unsigned (ew E 25) = q) by (rewrite (EE 25%nat 25%bv eq_refl), R25; apply unsigned_lit_small; lia).
assert (U23 : bv_unsigned (ew E 23) = k) by (rewrite (EE 23%nat 23%bv eq_refl), R23; apply unsigned_lit_small; lia).
assert (U27 : bv_unsigned (ew E 27) = k + 1)
  by (rewrite (EE 27%nat 27%bv eq_refl), R27; apply unsigned_lit_small; lia).
assert (U26 : bv_unsigned (ew E 26) = SHADOW_OFF)
  by (rewrite (EE 26%nat 26%bv eq_refl), R26; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U32 : bv_unsigned (ew E 32) = b1) by (rewrite E32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = b2) by (rewrite E33; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx.
destruct Hk as [-> | [-> | ->]]; unfold a2_ssK; cbn [Z.eqb Pos.eqb].
all: apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport);
  [ apply regs_ok_Eimg_Ereg | vm_compute; reflexivity | | | ].
all: try (unfold facts_ok; cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok];
  unfold afact_ok, YC4b.PTR; cbn [af_lo af_hi af_al2];
  rewrite U23, U27, U24, U25, U26, U32, U33, !Z.pow_0_r, !Z.mod_1_r;
  repeat match goal with |- _ /\ _ => split end; try exact I; unfold SHADOW_OFF in *; lia).
all: try (apply pairwise_disjoint_of_extents; unfold a2_rgI1, a2_rgI2a, extent_of_region;
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val zpairwise_disjoint zall_disjoint]; rewrite ?U24, ?U25;
    unfold zdisj; cbn [fst snd]; try exact I; repeat split; lia).
all: try apply Forall_nil.
all: unfold a2_rgI1, a2_rgI2a.
all: repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
  rewrite ?U24, ?U25.
all: split; [lia|]; split; [lia|]; split; [intros o Ho; lia|].
all: apply Forall_cons; [|apply Forall_nil].
1,2: apply (chunk_ok_val segs E _ (q + 1) 0 1 (SOff 32 0) b1);
    [rewrite denot_lit_U, (U_atom E 32 b1 E32 ltac:(lia)); reflexivity | cbn; lia | cbn; lia |];
  rewrite Z.add_0_r; apply V1; lia.
apply (chunk_ok_val segs E _ q 2 1 (SOff 33 0) b2);
  [rewrite denot_lit_U, (U_atom E 33 b2 E33 ltac:(lia)); reflexivity | cbn; lia | cbn; lia | apply V2; lia].
Qed.

(* The seat at +0x9ac / +0x858: s2 = SH, body's five shadow bytes writable; the two spill slots at s1 = sp1. *)
Lemma a2_entryB : forall (W : world segs) regs mem pc F sp1 SH,
  YK11.getr regs 18 = w64 SH -> YK11.getr regs 9 = w64 sp1 ->
  SHADOW_OFF <= SH -> SH + 32 <= 17594333495296 -> YM05.alloc_ceiling <= sp1 -> sp1 + 112 <= 2 ^ 63 ->
  val_mem segs (mrestrict (w_H W) mem) (sp1 + 8) 8 (F + 86) ->
  val_mem segs (mrestrict (w_H W) mem) (sp1 + 104) 8 (F + 96) -> 0 <= F + 86 -> F + 96 < 2 ^ 64 ->
  (forall a, SH + 12 <= a < SH + 17 -> apresent (w_H W) mem a) ->
  st_ok_pi segs VAL (a2_E regs 0 0 0 F) (a2_ssB pc)
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + pc)) mem (YK11.seg_rom segs))).
Proof.
intros W regs mem pc F sp1 SH R18 R9 HSH0 HSH1 Hs0 Hs1 VS8 VS104 HF0 HF1 Hpres.
set (E := a2_E regs 0 0 0 F).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs r)
  by (intros; apply a2_ew_reg; assumption).
pose proof (a2_ew_x regs 0 0 0 F 3 ltac:(lia)) as E35. pose proof (a2_ew_x regs 0 0 0 F 4 ltac:(lia)) as E36.
cbn [Nat.add nth] in E35, E36. fold E in E35, E36.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (U18 : bv_unsigned (ew E 18) = SH)
  by (rewrite (EE 18%nat 18%bv eq_refl), R18; apply unsigned_lit_small; unfold SHADOW_OFF in *; lia).
assert (U9 : bv_unsigned (ew E 9) = sp1) by (rewrite (EE 9%nat 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. unfold a2_ssB.
apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold a2_rgSH, a2_rgS.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
    rewrite ?U18, ?U9.
  + split; [unfold SHADOW_OFF in *; lia|]. split; [lia|]. split; [|apply Forall_nil].
    intros o Ho. apply (apresent_writable segs). apply Hpres. lia.
  + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    * apply (chunk_ok_val segs E _ sp1 8 8 (SOff 36 0) (F + 86));
        [rewrite denot_lit_U, (U_atom E 36 (F + 86) E36 ltac:(lia)); reflexivity | cbn; lia | cbn; lia | exact VS8].
    * apply (chunk_ok_val segs E _ sp1 104 8 (SOff 35 0) (F + 96));
        [rewrite denot_lit_U, (U_atom E 35 (F + 96) E35 ltac:(lia)); reflexivity | cbn; lia | cbn; lia | exact VS104].
- apply pairwise_disjoint_of_extents.
  unfold a2_rgSH, a2_rgS, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val zpairwise_disjoint zall_disjoint].
  rewrite U18, U9. unfold zdisj. cbn [fst snd]. unfold SHADOW_OFF in *. lia.
- unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U18, !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; try exact I; unfold SHADOW_OFF in *; lia.
Qed.
(* The seat at +0x9dc: s6 = mac in [lo, hi], the spill slots at s1 = sp1. *)
Lemma a2_entryC : forall (W : world segs) regs mem F sp1 mac lo hi,
  YK11.getr regs 9 = w64 sp1 -> YK11.getr regs 22 = w64 mac -> lo <= mac <= hi -> 0 <= lo -> hi < 2 ^ 64 ->
  YM05.alloc_ceiling <= sp1 -> sp1 + 112 <= 2 ^ 63 ->
  val_mem segs (mrestrict (w_H W) mem) (sp1 + 8) 8 (F + 86) ->
  val_mem segs (mrestrict (w_H W) mem) (sp1 + 104) 8 (F + 96) -> 0 <= F + 86 -> F + 96 < 2 ^ 64 ->
  st_ok_pi segs VAL (a2_E regs 0 0 0 F) (a2_ssC lo hi)
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + 0x9dc)) mem (YK11.seg_rom segs))).
Proof.
intros W regs mem F sp1 mac lo hi R9 R22 Hm Hlo Hhi Hs0 Hs1 VS8 VS104 HF0 HF1.
set (E := a2_E regs 0 0 0 F).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs r)
  by (intros; apply a2_ew_reg; assumption).
pose proof (a2_ew_x regs 0 0 0 F 3 ltac:(lia)) as E35. pose proof (a2_ew_x regs 0 0 0 F 4 ltac:(lia)) as E36.
cbn [Nat.add nth] in E35, E36. fold E in E35, E36.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (U9 : bv_unsigned (ew E 9) = sp1) by (rewrite (EE 9%nat 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
assert (U22 : bv_unsigned (ew E 22) = mac) by (rewrite (EE 22%nat 22%bv eq_refl), R22; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. unfold a2_ssC.
apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold a2_rgS. apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  + apply (chunk_ok_val segs E _ sp1 8 8 (SOff 36 0) (F + 86));
      [rewrite denot_lit_U, (U_atom E 36 (F + 86) E36 ltac:(lia)); reflexivity | cbn; lia | cbn; lia | exact VS8].
  + apply (chunk_ok_val segs E _ sp1 104 8 (SOff 35 0) (F + 96));
      [rewrite denot_lit_U, (U_atom E 35 (F + 96) E35 ltac:(lia)); reflexivity | cbn; lia | cbn; lia | exact VS104].
- apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. exact (conj I I).
- unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U22, !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

Lemma a2_entryD : forall (W : world segs) regs mem F,
  st_ok_pi segs VAL (a2_E regs 0 0 0 F) a2_ssD
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + 0x884)) mem (YK11.seg_rom segs))).
Proof.
intros W regs mem F. rewrite restrict_mkst_fx. unfold a2_ssD.
apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. exact I.
- unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. repeat split; exact I.
Qed.
End e.

(* The run tactics of LLVMFuzzerTestOneInput_seg_op4s.v (op_reg, op_region, op_awr_rs, op_after, op_kept_tac,
   op_byte_view), here under a2_ names. *)
(* The value of register r in the machine state of HS: its symbolic value, computed, then tac. *)
Ltac a2_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | ?T => idtac "a2_reg: no match for" T; fail
  end.
(* Region i of the symbolic state HS, at the machine state's memory. *)
Ltac a2_region HS i HR :=
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
(* The write rights of a run: the regions, computed. *)
Ltac a2_awr_rs :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
(* After a run: the model generalized. *)
Ltac a2_after :=
  lazymatch goal with |- SRr _ _ (mkCfg _ (with_vm_backing (m_vm_lazy ?m0) ?mt ?m0)) _ =>
    let md := fresh "mdw" in set (md := with_vm_backing (m_vm_lazy m0) mt m0) in *; clearbody md; clear mt end.

(* A one-byte chunk of a literal, read through the view. *)
Lemma a2_byte_view : forall (sg : list Segment) E (H : word -> bool) (m : word -> option byte) base off n,
  YP09.chunk_ok sg E (mrestrict H m) base (YP09.mkChunk off (CVal 1 (SLit n))) ->
  aview sg H m (base + off) = Some (bv_unsigned (YP09.byte_of_word (Z_to_bv 64 n) 0)).
Proof.
  intros sg E H m base off n Hc. destruct (Hc 0 ltac:(cbn; lia)) as (b & Eb & Mb).
  cbn [YP09.cbyte YP09.c_val YP09.c_off sv_denot] in Eb, Mb. injection Eb as <-. rewrite Z.add_0_r in Mb.
  unfold aview. rewrite Mb. reflexivity.
Qed.

Ltac a2_ifs H := repeat match type of H with
  | context [?a =? ?b] => destruct (Z.eqb_spec a b); try lia
  | context [?a <=? ?b] => destruct (Z.leb_spec a b); try lia
  | context [?a <? ?b] => destruct (Z.ltb_spec a b); try lia end.

Section h. Context {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).
Local Abbreviation av W m := (aview tfibsegs (w_H W) m).

(* A run of bytes read through the view, as garr8 (TransportGNotice.v garr8_of_aview). *)
Lemma a2_garr8_of_aview : forall H (m : word -> option byte) base (l : list Z),
  (forall j, (j < length l)%nat -> aview segs H m (base + Z.of_nat j) = Some (nth j l 0)) ->
  garr8 segs (mrestrict H m) base l.
Proof.
intros H m base l Hv j Hj.
destruct (aview_byte segs H m _ _ (Hv j Hj)) as (b & _ & _ & Hr).
exact (conj (OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.AE2y.val_mem1_of_aview H m _ _ (Hv j Hj)) Hr).
Qed.

Lemma a2_pres_grow : forall (H : word -> bool) (m m' : word -> option byte) a,
  YK1b.mem_grows (mrestrict H m) (mrestrict H m') -> apresent H m a -> apresent H m' a.
Proof.
intros H m m' a G (Ha & b & Hb). split; [exact Ha|]. specialize (G (Z_to_bv 64 a)). unfold mrestrict in G.
rewrite Ha, Hb in G. destruct (m' (Z_to_bv 64 a)) as [b'|];
  [exists b'; reflexivity | exfalso; apply G; [discriminate | reflexivity]].
Qed.

Definition a2_retB (z : bool) : Z := if z then 0x884 else 0x9dc.

(* The stretch from +0x9ac (z = false) or +0x858 (z = true) through the call of memset: body's shadow into scope (bytes
   12 .. 16 = 0, 0, 0, 0, 2), s6 = a0 & 15 (z = false), s9 = 104(s1) = body, memset (body, 0, 34); back at +0x9dc or
   +0x884. *)
Lemma a2_setB : forall cx op (z : bool) ly S (W : world segs) regs mem md e,
  @lp_prem rc B MT XL RLO RHI -> @lc_base rc B MT XL RLO RHI cx ->
  @lc_lcore rc B MT cx op false false (lo_k op) ly S W regs mem md e -> lc_tw W mem (lo_B op) ->
  SRr segs W (lc_cfg cx (if z then 0x858 else 0x9ac) regs mem md)
    (fun W' c' => exists regs2 mem2 md2, c' = lc_cfg cx (a2_retB z) regs2 mem2 md2 /\
       @lc_lcore rc B MT cx op false true (lo_k op) ly S W' regs2 mem2 md2 e /\ lc_tw W' mem2 (lo_B op) /\
       garr8 segs (mrestrict (w_H W') mem2) (lc_F cx + 96) (repeat 0 34) /\
       (forall r, In r [19; 20; 23; 24] -> YK11.getr regs2 (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)) /\
       YK11.getr regs2 25 = w64 (lc_F cx + 96) /\
       (z = false -> YK11.getr regs2 22 = w64 (Z.land (bv_unsigned (YK11.getr regs 10)) 15))).
Proof.
intros cx op z ly S W regs mem md e HP HB HL HTW.
pose proof (lp_laws _ _ _ _ _ HP) as LAWS.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned _ _ _ _ _ HP)) as HGX.
pose proof HL as (HC & HFR & HSP & HFSH & HOK & He & HMT & R21).
pose proof (lc_geom B MT XL RLO RHI cx ly S W regs mem md e HB HC) as GEO.
destruct GEO as [HAR Hsp0al Hstk Hsp1c HFaddr HFin Hn HINg HLIVE].
pose proof HC as (HJ & Hfrs & HlyF & HPERM & Rsp & R8 & R9 & Rgp & Rtp & Hsp1 & Hsp1al & HSAV & HF4096 & HFal &
  HFceil & HFpres & HFL & HIN).
destruct HFR as (R18 & R26).
pose proof asan_consts as (CC1 & CC2 & CC3 & CC4 & CC5).
destruct (frames_bounds segs B LAWS ly S W mem md LF_CID (l_fpos cx) HAR HFin) as (_ & _ & HFapp).
rewrite HFaddr in HFapp. change (fs_frame_bytes LF_CID) with 256 in HFapp.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
assert (HSPv : forall o v, In (o, v) (lf_spill_loop (lc_F cx)) ->
  val_mem segs (mrestrict (w_H W) mem) (lc_sp1 cx + o) 8 v).
{ intros o v Hin. unfold lc_spills in HSP. rewrite Forall_forall in HSP. apply val_mem_of_rdword. exact (HSP _ Hin). }
pose proof (HSPv 8 (lc_F cx + 86) ltac:(unfold lf_spill_loop; apply in_or_app; right; cbn; tauto)) as VS8.
pose proof (HSPv 104 (lc_F cx + 96) ltac:(unfold lf_spill_loop; apply in_or_app; right; cbn; tauto)) as VS104.
assert (ESH : lc_SH cx = SHADOW_OFF + lc_F cx / 8) by reflexivity.
assert (HSH0 : SHADOW_OFF <= lc_SH cx /\ lc_SH cx + 32 <= 17594333495296).
{ rewrite ESH. unfold SHADOW_OFF, LF_FBYTES in *. split; [pose proof (Z.div_pos (lc_F cx) 8 ltac:(lia) ltac:(lia)); lia|].
  assert (lc_F cx / 8 <= 0x7fffff800000 / 8) by (apply Z.div_le_mono; lia).
  change (0x7fffff800000 / 8) with 0xffffff00000 in *. lia. }
assert (Hpres : forall a, lc_SH cx + 12 <= a < lc_SH cx + 17 -> apresent (w_H W) mem a).
{ intros a Ha. apply (apresent_of_aview segs); [unfold SHADOW_OFF in *; lia | |].
  - intros Hi. pose proof (transport_segs_low a Hi) as Hl. unfold kLowMemEnd, SHADOW_OFF in *. lia.
  - replace a with (lc_SH cx + (a - lc_SH cx)) by lia.
    rewrite (HFSH (a - lc_SH cx) ltac:(lia)). discriminate. }
destruct Hstk as (Hceil & Hslo & Hshi & H47).
unfold LLVMF_STK, LF_FRAME, LF_FBYTES in *.
pose proof (@a2_entryB (l_fx cx) rc W regs mem (if z then 0x858 else 0x9ac) (lc_F cx) (lc_sp1 cx) (lc_SH cx) R18 R9
  (proj1 HSH0) (proj2 HSH0) ltac:(lia) ltac:(lia) VS8 VS104 ltac:(lia) ltac:(lia) Hpres) as HS.
set (E0 := a2_E regs 0 0 0 (lc_F cx)) in *.
assert (HEI : img_env VAL A_LIM E0) by apply a2_env_img.
assert (SHOK : sh_ok segs (SLit 0) [] E0 (mrestrict (w_H W) mem)) by constructor.
assert (EE0 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E0 n = YK11.getr regs r)
  by (intros; apply a2_ew_reg; assumption).
assert (E35 : ew E0 35 = w64 (lc_F cx + 96)).
{ pose proof (a2_ew_x regs 0 0 0 (lc_F cx) 3 ltac:(lia)) as H. exact H. }
assert (U18 : bv_unsigned (ew E0 18) = lc_SH cx).
{ rewrite (EE0 18%nat 18%bv eq_refl), R18. apply unsigned_lit_small. unfold SHADOW_OFF in *. lia. }
pose proof (@paj_run_x (l_fx cx) rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS
  HGX 0 []) as RUN.
unfold lc_cfg. change (w64 (transport_text + if z then 0x858 else 0x9ac)) with (Z_to_bv 64 (BASE + if z then 0x858 else 0x9ac)).
(* after the run: the call of memset *)
lazymatch goal with |- SRr _ _ _ ?Q => set (Q0 := Q) end.
assert (HBASE : BASE = 0x81264) by (vm_compute; reflexivity).
assert (HTT : transport_text = 0x81264) by (vm_compute; reflexivity).
assert (HSHb : SHADOW_OFF <= lc_SH cx /\ lc_SH cx + 32 <= 17594333495296) by exact HSH0.
assert (POST : forall regsT memT md1, a2_J B cx ly S W memT md1 e ->
  (forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 23; 24; 26] -> YK11.getr regsT (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)) ->
  YK11.getr regsT 1 = Z_to_bv 64 (BASE + a2_retB z) ->
  YK11.getr regsT 10 = w64 (lc_F cx + 96) -> YK11.getr regsT 11 = w64 0 ->
  YK11.getr regsT 12 = w64 34 -> YK11.getr regsT 25 = w64 (lc_F cx + 96) ->
  (z = false -> YK11.getr regsT 22 = w64 (Z.land (bv_unsigned (YK11.getr regs 10)) 15)) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lc_SH cx + 12 <= a < lc_SH cx + 17) -> av W memT a = av W mem a) ->
  (forall a, apresent (w_H W) mem a -> apresent (w_H W) memT a) ->
  (forall i, 0 <= i < 5 -> av W memT (lc_SH cx + 12 + i) = Some (nth (Z.to_nat i) A2_BSH 0)) ->
  SRr segs W (mkCfg (@YK11.mkst (l_fx cx) regsT (Z_to_bv 64 (a2_ipc OSet)) memT (YK11.seg_rom segs)) md1) Q0).
{ intros regsT memT md1 HJ1 KR R1 R10 R11 R12 R25 R22 KM KP KS.
  assert (HFSH1 : lc_fsh cx (av W memT) false true).
  { intros i Hi. assert (Hc : (0 <= i < 12 \/ 17 <= i < 32) \/ 12 <= i < 17) by lia.
    destruct Hc as [Hout | Hin].
    - rewrite (KM (lc_SH cx + i)) by (unfold SHADOW_OFF in *; lia). rewrite (HFSH i Hi).
      assert (Hc2 : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10 \/
                    i = 11 \/ i = 17 \/ i = 18 \/ i = 19 \/ i = 20 \/ i = 21 \/ i = 22 \/ i = 23 \/ i = 24 \/ i = 25 \/
                    i = 26 \/ i = 27 \/ i = 28 \/ i = 29 \/ i = 30 \/ i = 31) by lia.
      repeat (destruct Hc2 as [-> | Hc2]; [reflexivity|]). subst i. reflexivity.
    - replace (lc_SH cx + i) with (lc_SH cx + 12 + (i - 12)) by lia. rewrite (KS (i - 12) ltac:(lia)).
      assert (Hc2 : i = 12 \/ i = 13 \/ i = 14 \/ i = 15 \/ i = 16) by lia.
      repeat (destruct Hc2 as [-> | Hc2]; [reflexivity|]). subst i. reflexivity. }
  destruct (a2_move B MT XL RLO RHI cx op false false true (lo_k op) ly S W regs mem md e regsT memT md1 0 LAWS HGX HB HL
    HTW HJ1) as [HL1 HTW1].
  { intros r Hr. apply KR. cbn [In] in Hr |- *. tauto. }
  { unfold LLVMF_STK. lia. }
  { intros a Ha Hout. apply KM; [exact Ha|]. intros Hs. apply Hout. right. right. exact Hs. }
  { exact KP. }
  { exact HFSH1. }
  eapply SRr_mono.
  { apply (a2_icall B MT XL RLO RHI cx op (lo_k op) OSet ly S W regsT memT md1 e (lc_F cx + 96) 0 34
      (Z_to_bv 64 (BASE + a2_retB z)) HP HB HL1 HTW1 R10 R11 R12 R1).
    - apply ret_ok_codeptr_v; destruct z; cbn; lia.
    - lia.
    - lia.
    - lia.
    - exact I. }
  intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HL2 & HTW2 & HPR & HBY & _).
  exists regs2, mem2, md2. split.
  { unfold lc_cfg, w64. rewrite HBASE, HTT. reflexivity. }
  split; [exact HL2|]. split; [exact HTW2|]. split.
  { apply a2_garr8_of_aview. rewrite repeat_length. intros j Hj. rewrite (HBY (Z.of_nat j) ltac:(lia)).
    rewrite a2_nth_repeat by lia. reflexivity. }
  split.
  { intros r Hr. rewrite (HPR r ltac:(unfold acallee_saved; cbn [In] in Hr; lia)). apply KR. cbn [In] in Hr |- *. tauto. }
  split.
  { exact (eq_trans (HPR 25 ltac:(unfold acallee_saved; lia)) R25). }
  intros Hz. exact (eq_trans (HPR 22 ltac:(unfold acallee_saved; lia)) (R22 Hz)). }

destruct z.
- paj_run_tok RUN HS HJ SHOK (0, 0).
  + a2_awr_rs.
    eapply (awr_ok_x_cons_own _ _ _ _ _ _ _ _ _ _ _ _ LF_CID (l_fpos cx)); [left; reflexivity | |].
    * intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U18 in Ha.
      right. unfold in_zr. cbn [fst snd]. rewrite HFaddr. change (fs_frame_bytes LF_CID / 8) with 32.
      unfold lc_SH in Ha. unfold shadow_addr. lia.
    * apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia|].
      apply awr_ok_x_nil.
  + a2_after.
    lazymatch type of HS with context [restrict _ ?m] => rename m into ms1 end.
    lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => rename m into md1 end.
    assert (KM : forall a, 0 <= a < 2 ^ 64 -> ~ (lc_SH cx + 12 <= a < lc_SH cx + 17) -> av W (ms_mem ms1) a = av W mem a).
    { intros a Ha Hn0. apply (kept_of_frame _ _ _ _ _ (fun x => lc_SH cx + 12 <= x < lc_SH cx + 17) HFr);
        [| exact Ha | exact Hn0].
      intros b wlo whi x Hin Hx.
      lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
      cbn [In] in Hin.
      repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; rewrite ?U18 in Hx; lia |]).
      destruct Hin. }
    a2_region HS 0%nat HR.
    destruct HR as (_ & _ & _ & HCH).
    apply Forall_cons_iff in HCH as [H16 HCH]. apply Forall_cons_iff in HCH as [H15 HCH].
    apply Forall_cons_iff in HCH as [H14 HCH]. apply Forall_cons_iff in HCH as [H13 HCH].
    apply Forall_cons_iff in HCH as [H12 _].
    apply a2_byte_view in H16, H15, H14, H13, H12. cbn [YP09.r_base base_val] in H16, H15, H14, H13, H12.
    rewrite U18 in H16, H15, H14, H13, H12.
    a2_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 0x884)) G1 ltac:(apply codeptr_val; exact HEI).
    a2_reg HS (Z_to_bv 5 10) (w64 (lc_F cx + 96)) G10 ltac:(cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    a2_reg HS (Z_to_bv 5 25) (w64 (lc_F cx + 96)) G25 ltac:(cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    a2_reg HS (Z_to_bv 5 11) (w64 0) G11 ltac:(reflexivity).
    a2_reg HS (Z_to_bv 5 12) (w64 34) G12 ltac:(reflexivity).
    a2_reg HS (Z_to_bv 5 2) (YK11.getr regs (Z_to_bv 5 2)) GK2
      ltac:(cbn [sv_denot]; rewrite (EE0 2%nat (Z_to_bv 5 2) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    a2_reg HS (Z_to_bv 5 3) (YK11.getr regs (Z_to_bv 5 3)) GK3
      ltac:(cbn [sv_denot]; rewrite (EE0 3%nat (Z_to_bv 5 3) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    a2_reg HS (Z_to_bv 5 4) (YK11.getr regs (Z_to_bv 5 4)) GK4
      ltac:(cbn [sv_denot]; rewrite (EE0 4%nat (Z_to_bv 5 4) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    a2_reg HS (Z_to_bv 5 8) (YK11.getr regs (Z_to_bv 5 8)) GK8
      ltac:(cbn [sv_denot]; rewrite (EE0 8%nat (Z_to_bv 5 8) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    a2_reg HS (Z_to_bv 5 9) (YK11.getr regs (Z_to_bv 5 9)) GK9
      ltac:(cbn [sv_denot]; rewrite (EE0 9%nat (Z_to_bv 5 9) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    a2_reg HS (Z_to_bv 5 18) (YK11.getr regs (Z_to_bv 5 18)) GK18
      ltac:(cbn [sv_denot]; rewrite (EE0 18%nat (Z_to_bv 5 18) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    a2_reg HS (Z_to_bv 5 19) (YK11.getr regs (Z_to_bv 5 19)) GK19
      ltac:(cbn [sv_denot]; rewrite (EE0 19%nat (Z_to_bv 5 19) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    a2_reg HS (Z_to_bv 5 20) (YK11.getr regs (Z_to_bv 5 20)) GK20
      ltac:(cbn [sv_denot]; rewrite (EE0 20%nat (Z_to_bv 5 20) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    a2_reg HS (Z_to_bv 5 21) (YK11.getr regs (Z_to_bv 5 21)) GK21
      ltac:(cbn [sv_denot]; rewrite (EE0 21%nat (Z_to_bv 5 21) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    a2_reg HS (Z_to_bv 5 23) (YK11.getr regs (Z_to_bv 5 23)) GK23
      ltac:(cbn [sv_denot]; rewrite (EE0 23%nat (Z_to_bv 5 23) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    a2_reg HS (Z_to_bv 5 24) (YK11.getr regs (Z_to_bv 5 24)) GK24
      ltac:(cbn [sv_denot]; rewrite (EE0 24%nat (Z_to_bv 5 24) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    a2_reg HS (Z_to_bv 5 26) (YK11.getr regs (Z_to_bv 5 26)) GK26
      ltac:(cbn [sv_denot]; rewrite (EE0 26%nat (Z_to_bv 5 26) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    assert (GK : forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 23; 24; 26] ->
      YK11.getr (ms_regs ms1) (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)).
    { intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<- | Hr]; [assumption |]). destruct Hr. }
    pmkst HS.
    apply (POST (ms_regs ms1) (ms_mem ms1) md1 HJ GK G1 G10 G11 G12 G25 (fun Hz => match Hz with eq_refl => I end) KM).
    * intros a Ha. exact (a2_pres_grow (w_H W) mem (ms_mem ms1) a HG Ha).
    * intros i Hi. assert (Hc : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4) by lia.
      destruct Hc as [-> | [-> | [-> | [-> | ->]]]];
        [ replace (lc_SH cx + 12 + 0) with (lc_SH cx + 12) by lia; refine (eq_trans H12 _)
        | replace (lc_SH cx + 12 + 1) with (lc_SH cx + 13) by lia; refine (eq_trans H13 _)
        | replace (lc_SH cx + 12 + 2) with (lc_SH cx + 14) by lia; refine (eq_trans H14 _)
        | replace (lc_SH cx + 12 + 3) with (lc_SH cx + 15) by lia; refine (eq_trans H15 _)
        | replace (lc_SH cx + 12 + 4) with (lc_SH cx + 16) by lia; refine (eq_trans H16 _) ]; vm_compute; reflexivity.
- paj_run_tok RUN HS HJ SHOK (0, 0).
  + a2_awr_rs.
    eapply (awr_ok_x_cons_own _ _ _ _ _ _ _ _ _ _ _ _ LF_CID (l_fpos cx)); [left; reflexivity | |].
    * intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U18 in Ha.
      right. unfold in_zr. cbn [fst snd]. rewrite HFaddr. change (fs_frame_bytes LF_CID / 8) with 32.
      unfold lc_SH in Ha. unfold shadow_addr. lia.
    * apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia|].
      apply awr_ok_x_nil.
  + a2_after.
    lazymatch type of HS with context [restrict _ ?m] => rename m into ms1 end.
    lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => rename m into md1 end.
    assert (KM : forall a, 0 <= a < 2 ^ 64 -> ~ (lc_SH cx + 12 <= a < lc_SH cx + 17) -> av W (ms_mem ms1) a = av W mem a).
    { intros a Ha Hn0. apply (kept_of_frame _ _ _ _ _ (fun x => lc_SH cx + 12 <= x < lc_SH cx + 17) HFr);
        [| exact Ha | exact Hn0].
      intros b wlo whi x Hin Hx.
      lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
      cbn [In] in Hin.
      repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; rewrite ?U18 in Hx; lia |]).
      destruct Hin. }
    a2_region HS 0%nat HR.
    destruct HR as (_ & _ & _ & HCH).
    apply Forall_cons_iff in HCH as [H16 HCH]. apply Forall_cons_iff in HCH as [H15 HCH].
    apply Forall_cons_iff in HCH as [H14 HCH]. apply Forall_cons_iff in HCH as [H13 HCH].
    apply Forall_cons_iff in HCH as [H12 _].
    apply a2_byte_view in H16, H15, H14, H13, H12. cbn [YP09.r_base base_val] in H16, H15, H14, H13, H12.
    rewrite U18 in H16, H15, H14, H13, H12.
    a2_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 0x9dc)) G1 ltac:(apply codeptr_val; exact HEI).
    a2_reg HS (Z_to_bv 5 10) (w64 (lc_F cx + 96)) G10 ltac:(cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    a2_reg HS (Z_to_bv 5 25) (w64 (lc_F cx + 96)) G25 ltac:(cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    a2_reg HS (Z_to_bv 5 11) (w64 0) G11 ltac:(reflexivity).
    a2_reg HS (Z_to_bv 5 12) (w64 34) G12 ltac:(reflexivity).
    a2_reg HS (Z_to_bv 5 2) (YK11.getr regs (Z_to_bv 5 2)) GK2
      ltac:(cbn [sv_denot]; rewrite (EE0 2%nat (Z_to_bv 5 2) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    a2_reg HS (Z_to_bv 5 3) (YK11.getr regs (Z_to_bv 5 3)) GK3
      ltac:(cbn [sv_denot]; rewrite (EE0 3%nat (Z_to_bv 5 3) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    a2_reg HS (Z_to_bv 5 4) (YK11.getr regs (Z_to_bv 5 4)) GK4
      ltac:(cbn [sv_denot]; rewrite (EE0 4%nat (Z_to_bv 5 4) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    a2_reg HS (Z_to_bv 5 8) (YK11.getr regs (Z_to_bv 5 8)) GK8
      ltac:(cbn [sv_denot]; rewrite (EE0 8%nat (Z_to_bv 5 8) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    a2_reg HS (Z_to_bv 5 9) (YK11.getr regs (Z_to_bv 5 9)) GK9
      ltac:(cbn [sv_denot]; rewrite (EE0 9%nat (Z_to_bv 5 9) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    a2_reg HS (Z_to_bv 5 18) (YK11.getr regs (Z_to_bv 5 18)) GK18
      ltac:(cbn [sv_denot]; rewrite (EE0 18%nat (Z_to_bv 5 18) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    a2_reg HS (Z_to_bv 5 19) (YK11.getr regs (Z_to_bv 5 19)) GK19
      ltac:(cbn [sv_denot]; rewrite (EE0 19%nat (Z_to_bv 5 19) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    a2_reg HS (Z_to_bv 5 20) (YK11.getr regs (Z_to_bv 5 20)) GK20
      ltac:(cbn [sv_denot]; rewrite (EE0 20%nat (Z_to_bv 5 20) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    a2_reg HS (Z_to_bv 5 21) (YK11.getr regs (Z_to_bv 5 21)) GK21
      ltac:(cbn [sv_denot]; rewrite (EE0 21%nat (Z_to_bv 5 21) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    a2_reg HS (Z_to_bv 5 23) (YK11.getr regs (Z_to_bv 5 23)) GK23
      ltac:(cbn [sv_denot]; rewrite (EE0 23%nat (Z_to_bv 5 23) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    a2_reg HS (Z_to_bv 5 24) (YK11.getr regs (Z_to_bv 5 24)) GK24
      ltac:(cbn [sv_denot]; rewrite (EE0 24%nat (Z_to_bv 5 24) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    a2_reg HS (Z_to_bv 5 26) (YK11.getr regs (Z_to_bv 5 26)) GK26
      ltac:(cbn [sv_denot]; rewrite (EE0 26%nat (Z_to_bv 5 26) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    assert (GK : forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 23; 24; 26] ->
      YK11.getr (ms_regs ms1) (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)).
    { intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<- | Hr]; [assumption |]). destruct Hr. }
    assert (V22 : sv_denot E0 (SAlu ALU_AND (SOff 10 0) (SLit 15)) = w64 (Z.land (bv_unsigned (YK11.getr regs 10)) 15)).
    { rewrite denot_lit_U.
      rewrite U_and_lit by lia.
      unfold w64. f_equal. f_equal.
      rewrite U_SOff.
      rewrite (EE0 10%nat 10%bv eq_refl).
      rewrite Z.add_0_r.
      apply zcanon_id. apply u64_range. }
    a2_reg HS (Z_to_bv 5 22) (w64 (Z.land (bv_unsigned (YK11.getr regs 10)) 15)) G22 ltac:(exact V22).
    pmkst HS.
    apply (POST (ms_regs ms1) (ms_mem ms1) md1 HJ GK G1 G10 G11 G12 G25 (fun _ => G22) KM).
    * intros a Ha. exact (a2_pres_grow (w_H W) mem (ms_mem ms1) a HG Ha).
    * intros i Hi. assert (Hc : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4) by lia.
      destruct Hc as [-> | [-> | [-> | [-> | ->]]]];
        [ replace (lc_SH cx + 12 + 0) with (lc_SH cx + 12) by lia; refine (eq_trans H12 _)
        | replace (lc_SH cx + 12 + 1) with (lc_SH cx + 13) by lia; refine (eq_trans H13 _)
        | replace (lc_SH cx + 12 + 2) with (lc_SH cx + 14) by lia; refine (eq_trans H14 _)
        | replace (lc_SH cx + 12 + 3) with (lc_SH cx + 15) by lia; refine (eq_trans H15 _)
        | replace (lc_SH cx + 12 + 4) with (lc_SH cx + 16) by lia; refine (eq_trans H16 _) ]; vm_compute; reflexivity.
Qed.

(* body after the copy of src (6 bytes) at offset k, as the model states it. *)
Definition a2_body (k : Z) (src : list byte) : list byte := TW.upd (repeat (DSpec.b8 0) 34) k src.

(* The 6 bytes of HOST / OTHER in the image. *)
Lemma a2_src_rom : forall (x : Z) (src : list byte) i, (x, src) = (TRANS_HOST, TC.HOST) \/ (x, src) = (TRANS_OTHER, TC.OTHER) ->
  0 <= i < 6 -> trans_in_ro_rd (x + i) /\
  option_map (fun b : byte => bv_unsigned b) (YK11.seg_rom segs (Z_to_bv 64 (x + i))) =
    Some (bv_unsigned (nth (Z.to_nat i) src (Z_to_bv 8 0))).
Proof.
intros x src i Hx Hi. assert (Hc : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5) by lia.
destruct Hx as [Hx | Hx]; injection Hx as -> ->.
all: split; [unfold trans_in_ro_rd, TRANS_RO_RD, TRANS_RO_GLOBALS; apply Exists_exists|].
- exists (TRANS_HOST, 6). split; [cbn; tauto | unfold in_zr; cbn [fst snd]; lia].
- destruct Hc as [-> | [-> | [-> | [-> | [-> | ->]]]]]; vm_compute; reflexivity.
- exists (TRANS_OTHER, 6). split; [cbn; tauto | unfold in_zr; cbn [fst snd]; lia].
- destruct Hc as [-> | [-> | [-> | [-> | [-> | ->]]]]]; vm_compute; reflexivity.
Qed.

(* The call of memcpy (body + k, src, 6) at +0x9f4 and the return at +0x9f8 (ANN). *)
Lemma a2_cpy : forall cx op ly S (W : world segs) regsT memT mdT e k x (src : list byte),
  @lp_prem rc B MT XL RLO RHI -> @lc_base rc B MT XL RLO RHI cx ->
  @lc_lcore rc B MT cx op false true (lo_k op) ly S W regsT memT mdT e -> lc_tw W memT (lo_B op) ->
  garr8 segs (mrestrict (w_H W) memT) (lc_F cx + 96) (repeat 0 34) ->
  (x, src) = (TRANS_HOST, TC.HOST) \/ (x, src) = (TRANS_OTHER, TC.OTHER) -> 0 <= k <= 28 ->
  YK11.getr regsT 10 = w64 (lc_F cx + 96 + k) -> YK11.getr regsT 11 = w64 x -> YK11.getr regsT 12 = w64 6 ->
  YK11.getr regsT 1 = Z_to_bv 64 (BASE + LO_ANN) ->
  SRr segs W (mkCfg (@YK11.mkst (l_fx cx) regsT (Z_to_bv 64 (a2_ipc OCpy)) memT (YK11.seg_rom segs)) mdT)
    (fun W' c' => exists regs2 mem2 md2, c' = lc_cfg cx LO_ANN regs2 mem2 md2 /\
       @lc_lcore rc B MT cx op false true (lo_k op) ly S W' regs2 mem2 md2 e /\ lc_tw W' mem2 (lo_B op) /\
       garr8 segs (mrestrict (w_H W') mem2) (lc_F cx + 96) (TW.zs (a2_body k src)) /\
       aregs_preserved regsT regs2).
Proof.
intros cx op ly S W regsT memT mdT e k x src HP HB HL HTW HZ Hx Hk R10 R11 R12 R1.
pose proof HL as (HC & _).
pose proof (lc_rom_view_ok B MT XL RLO RHI HP cx ly S W regsT memT mdT e HB HC) as HROM.
assert (HSRC : forall i, 0 <= i < 6 -> av W memT (x + i) = Some (bv_unsigned (nth (Z.to_nat i) src (Z_to_bv 8 0)))).
{ intros i Hi. destruct (a2_src_rom x src i Hx Hi) as (Hro & Hv). rewrite (HROM _ Hro). exact Hv. }
assert (HBASE : BASE = 0x81264) by (vm_compute; reflexivity).
assert (HTT : transport_text = 0x81264) by (vm_compute; reflexivity).
eapply SRr_mono.
{ apply (a2_icall B MT XL RLO RHI cx op (lo_k op) OCpy ly S W regsT memT mdT e (lc_F cx + 96 + k) x 6
    (Z_to_bv 64 (BASE + LO_ANN)) HP HB HL HTW R10 R11 R12 R1).
  - apply ret_ok_codeptr_v; unfold LO_ANN; cbn; lia.
  - lia.
  - lia.
  - lia.
  - split; [destruct Hx as [Hx | Hx]; injection Hx as -> ->; tauto | reflexivity]. }
intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HL2 & HTW2 & HPR & HBY & HK).
exists regs2, mem2, md2. split.
{ unfold lc_cfg, w64. rewrite HBASE, HTT. reflexivity. }
split; [exact HL2|]. split; [exact HTW2|]. split; [|exact HPR].
apply a2_garr8_of_aview. unfold TW.zs. rewrite length_map. unfold a2_body.
assert (Hsl : length src = 6%nat) by (destruct Hx as [Hx | Hx]; injection Hx as -> ->; reflexivity).
assert (Hul : length (TW.upd (repeat (DSpec.b8 0) 34) k src) = 34%nat).
{ unfold TW.upd. rewrite !length_app, length_firstn, length_skipn, !repeat_length, Hsl. lia. }
rewrite Hul. intros j Hj.
rewrite (map_nth (fun b : byte => bv_unsigned b) _ (Z_to_bv 8 0)). change (bv_unsigned (Z_to_bv 8 0)) with 0.
rewrite (a2_upd_nth src k j Hsl ltac:(lia) ltac:(lia) Hj).
destruct ((k <=? Z.of_nat j) && (Z.of_nat j <? k + 6))%bool eqn:Ein.
- apply andb_true_iff in Ein as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
  replace (lc_F cx + 96 + Z.of_nat j) with (lc_F cx + 96 + k + (Z.of_nat j - k)) by lia.
  rewrite (HBY (Z.of_nat j - k) ltac:(lia)). rewrite (HSRC (Z.of_nat j - k) ltac:(lia)).
  do 3 f_equal. lia.
- rewrite (HK (lc_F cx + 96 + Z.of_nat j) ltac:(lia)).
  + destruct (garr8_nthZ segs _ _ _ (Z.of_nat j) HZ ltac:(lia) ltac:(rewrite repeat_length; lia)) as (Hv & _).
    rewrite a2_nth_repeat in Hv by lia.
    rewrite (can_aview_of_val1 segs _ _ _ _ Hv). reflexivity.
  + apply andb_false_iff in Ein as [E1 | E1]; [apply Z.leb_gt in E1 | apply Z.ltb_ge in E1]; lia.
Qed.

Lemma a2_denot_off : forall E n v, ew E n = w64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n 0) = w64 v.
Proof.
intros E n v H Hv. rewrite denot_lit_U, U_SOff, H, Z.add_0_r. unfold w64. f_equal.
rewrite unsigned_lit_small by lia. apply zcanon_id. unfold M64. lia.
Qed.
Lemma a2_denot_add : forall E n m u v, ew E n = w64 u -> ew E m = w64 v -> 0 <= u -> 0 <= v -> u + v < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SOff n 0) (SOff m 0)) = w64 (u + v).
Proof.
intros E n m u v Hn Hm Hu Hv Huv. rewrite denot_lit_U, U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, Hn, Hm, !Z.add_0_r.
unfold w64. f_equal. rewrite !unsigned_lit_small by lia. rewrite !(zcanon_id u), !(zcanon_id v) by (unfold M64; lia).
apply zcanon_id. unfold M64. lia.
Qed.
Lemma a2_denot_img : forall E n, img_env VAL A_LIM E -> (A_TEXT <= n < A_LIM)%nat ->
  sv_denot E (SOff n 0) = w64 (VAL n).
Proof.
intros E n HE Hn. rewrite denot_lit_U, U_SOff, (HE n Hn), Z.add_0_r. unfold w64. f_equal.
apply zcanon_id. rewrite <- (HE n Hn). pose proof (u64_range (ew E n)). exact H.
Qed.

(* body after the copy, as the model states it (lc_ann_vals' body1). *)
Definition a2_body1 (mac : Z) : list byte :=
  if mac <? 10 then a2_body mac TC.HOST else if mac <? 13 then a2_body (mac - 10) TC.OTHER else repeat (DSpec.b8 0) 34.

(* The stretch from +0x9dc (z = false, s6 = mac) or +0x884 (z = true, mac = 0) to ANN (+0x9f8): the copy of HOST to
   body + mac (mac < 10) or of OTHER to body + mac - 10 (10 <= mac <= 12), or nothing (mac > 12). *)
Lemma a2_tail : forall cx op (z : bool) ly S (W : world segs) regs mem md e mac,
  @lp_prem rc B MT XL RLO RHI -> @lc_base rc B MT XL RLO RHI cx ->
  @lc_lcore rc B MT cx op false true (lo_k op) ly S W regs mem md e -> lc_tw W mem (lo_B op) ->
  garr8 segs (mrestrict (w_H W) mem) (lc_F cx + 96) (repeat 0 34) -> YK11.getr regs 25 = w64 (lc_F cx + 96) ->
  (if z then mac = 0 else YK11.getr regs 22 = w64 mac) -> 0 <= mac < 16 ->
  SRr segs W (lc_cfg cx (a2_retB z) regs mem md)
    (fun W' c' => exists regs2 mem2 md2, c' = lc_cfg cx LO_ANN regs2 mem2 md2 /\
       @lc_lcore rc B MT cx op false true (lo_k op) ly S W' regs2 mem2 md2 e /\ lc_tw W' mem2 (lo_B op) /\
       garr8 segs (mrestrict (w_H W') mem2) (lc_F cx + 96) (TW.zs (a2_body1 mac)) /\
       (forall r, In r [19; 24; 25] -> YK11.getr regs2 (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)) /\
       (if z then YK11.getr regs2 20 = w64 0 /\ YK11.getr regs2 23 = w64 0
        else forall r, In r [20; 23] -> YK11.getr regs2 (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r))).
Proof.
intros cx op z ly S W regs mem md e mac HP HB HL HTW HZ R25 Hz Hmac.
pose proof (lp_laws _ _ _ _ _ HP) as LAWS.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned _ _ _ _ _ HP)) as HGX.
pose proof HL as (HC & HFR & HSP & HFSH & HOK & He & HMT & R21).
pose proof (lc_geom B MT XL RLO RHI cx ly S W regs mem md e HB HC) as GEO.
destruct GEO as [HAR Hsp0al Hstk Hsp1c HFaddr HFin Hn HINg HLIVE].
pose proof HC as (HJ & Hfrs & HlyF & HPERM & Rsp & R8 & R9 & Rgp & Rtp & Hsp1 & Hsp1al & HSAV & HF4096 & HFal &
  HFceil & HFpres & HFL & HIN).
pose proof asan_consts as (CC1 & CC2 & CC3 & CC4 & CC5).
assert (HSPv : forall o v, In (o, v) (lf_spill_loop (lc_F cx)) ->
  val_mem segs (mrestrict (w_H W) mem) (lc_sp1 cx + o) 8 v).
{ intros o v Hin. unfold lc_spills in HSP. rewrite Forall_forall in HSP. apply val_mem_of_rdword. exact (HSP _ Hin). }
pose proof (HSPv 8 (lc_F cx + 86) ltac:(unfold lf_spill_loop; apply in_or_app; right; cbn; tauto)) as VS8.
pose proof (HSPv 104 (lc_F cx + 96) ltac:(unfold lf_spill_loop; apply in_or_app; right; cbn; tauto)) as VS104.
destruct Hstk as (Hceil & Hslo & Hshi & H47).
unfold LLVMF_STK, LF_FRAME, LF_FBYTES in *.
assert (HBASE : BASE = 0x81264) by (vm_compute; reflexivity).
assert (HTT : transport_text = 0x81264) by (vm_compute; reflexivity).
pose proof (@paj_run_x (l_fx cx) rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS
  HGX 0 []) as RUN.
pose proof (@paj_run_to_x (l_fx cx) rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS
  HGX 0 []) as RUNTO.
set (E0 := a2_E regs 0 0 0 (lc_F cx)).
assert (HEI : img_env VAL A_LIM E0) by apply a2_env_img.
assert (SHOK : sh_ok segs (SLit 0) [] E0 (mrestrict (w_H W) mem)) by constructor.
assert (EE0 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E0 n = YK11.getr regs r)
  by (intros; apply a2_ew_reg; assumption).
assert (E35 : ew E0 35 = w64 (lc_F cx + 96)) by exact (a2_ew_x regs 0 0 0 (lc_F cx) 3 ltac:(lia)).
assert (E36 : ew E0 36 = w64 (lc_F cx + 86)) by exact (a2_ew_x regs 0 0 0 (lc_F cx) 4 ltac:(lia)).
assert (U25 : bv_unsigned (ew E0 25) = lc_F cx + 96)
  by (rewrite (EE0 25%nat 25%bv eq_refl), R25; apply unsigned_lit_small; lia).
(* after a read-only run to the call of memcpy *)
assert (CALL : forall regsT memT md1 k x (src : list byte),
  a2_J B cx ly S W memT md1 e ->
  (forall r, In r [2; 3; 4; 8; 9; 18; 19; 21; 24; 25; 26] -> YK11.getr regsT (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)) ->
  (if z then YK11.getr regsT 20 = w64 0 /\ YK11.getr regsT 23 = w64 0
   else forall r, In r [20; 23] -> YK11.getr regsT (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)) ->
  (forall a, 0 <= a < 2 ^ 64 -> av W memT a = av W mem a) ->
  (forall a, apresent (w_H W) mem a -> apresent (w_H W) memT a) ->
  (x, src) = (TRANS_HOST, TC.HOST) \/ (x, src) = (TRANS_OTHER, TC.OTHER) -> 0 <= k <= 28 ->
  a2_body1 mac = a2_body k src ->
  YK11.getr regsT 10 = w64 (lc_F cx + 96 + k) -> YK11.getr regsT 11 = w64 x -> YK11.getr regsT 12 = w64 6 ->
  YK11.getr regsT 1 = Z_to_bv 64 (BASE + LO_ANN) ->
  SRr segs W (mkCfg (@YK11.mkst (l_fx cx) regsT (Z_to_bv 64 (a2_ipc OCpy)) memT (YK11.seg_rom segs)) md1)
    (fun W' c' => exists regs2 mem2 md2, c' = lc_cfg cx LO_ANN regs2 mem2 md2 /\
       @lc_lcore rc B MT cx op false true (lo_k op) ly S W' regs2 mem2 md2 e /\ lc_tw W' mem2 (lo_B op) /\
       garr8 segs (mrestrict (w_H W') mem2) (lc_F cx + 96) (TW.zs (a2_body1 mac)) /\
       (forall r, In r [19; 24; 25] -> YK11.getr regs2 (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)) /\
       (if z then YK11.getr regs2 20 = w64 0 /\ YK11.getr regs2 23 = w64 0
        else forall r, In r [20; 23] -> YK11.getr regs2 (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)))).
{ intros regsT memT md1 k x src HJ1 KR KZ KM KP Hx Hk Hb R10 R11 R12 R1.
  destruct (a2_move B MT XL RLO RHI cx op false true true (lo_k op) ly S W regs mem md e regsT memT md1 0 LAWS HGX HB HL
    HTW HJ1) as [HL1 HTW1].
  { intros r Hr. apply KR. cbn [In] in Hr |- *. tauto. }
  { unfold LLVMF_STK. lia. }
  { intros a Ha _. exact (KM a Ha). }
  { exact KP. }
  { intros i Hi. rewrite KM; [exact (HFSH i Hi)|]. pose proof (Z.div_pos (lc_F cx) 8 ltac:(lia) ltac:(lia)).
    unfold lc_SH, SHADOW_OFF. lia. }
  assert (HZ1 : garr8 segs (mrestrict (w_H W) memT) (lc_F cx + 96) (repeat 0 34)).
  { apply (lc_garr8_kept (w_H W) (w_H W) mem memT (lc_F cx + 96) _); [|exact HZ].
    intros j Hj. rewrite repeat_length in Hj. apply KM. lia. }
  eapply SRr_mono.
  { exact (a2_cpy cx op ly S W regsT memT md1 e k x src HP HB HL1 HTW1 HZ1 Hx Hk R10 R11 R12 R1). }
  intros W2 c2 _ (regs2 & mem2 & md2 & -> & HL2 & HTW2 & HG2 & HPR).
  exists regs2, mem2, md2. split; [reflexivity|]. split; [exact HL2|]. split; [exact HTW2|].
  split; [rewrite Hb; exact HG2|]. split.
  { intros r Hr. rewrite (HPR r ltac:(unfold acallee_saved; cbn [In] in Hr; lia)). apply KR. cbn [In] in Hr |- *. tauto. }
  destruct z.
  - destruct KZ as (K20 & K23).
    split; [exact (eq_trans (HPR 20 ltac:(unfold acallee_saved; lia)) K20) |
            exact (eq_trans (HPR 23 ltac:(unfold acallee_saved; lia)) K23)].
  - intros r Hr. rewrite (HPR r ltac:(unfold acallee_saved; cbn [In] in Hr; lia)). apply KZ. exact Hr. }
assert (VHOST : VAL (A_OBJ 6) = TRANS_HOST) by (vm_compute; reflexivity).
assert (VOTHER : VAL 258 = TRANS_OTHER) by (vm_compute; reflexivity).
assert (Hlo : forall v, In v [2; 3; 4; 8; 9; 18; 19; 20; 21; 23; 24; 25; 26] -> True) by (intros; exact I).
destruct z.
- (* +0x884: s7 = s4 = s6 = 0, a0 = s9, a1 = HOST, a2 = 6, memcpy *)
  cbn in Hz. subst mac.
  pose proof (@a2_entryD (l_fx cx) rc W regs mem (lc_F cx)) as HS. fold E0 in HS.
  unfold lc_cfg, a2_retB. change (w64 (transport_text + 0x884)) with (Z_to_bv 64 (BASE + 0x884)).
  paj_run_tok RUN HS HJ SHOK (0, 0).
  { a2_awr_rs. apply awr_ok_x_nil. }
  a2_after.
  lazymatch type of HS with context [restrict _ ?m] => rename m into ms1 end.
  lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => rename m into md1 end.
  assert (KM : forall a, 0 <= a < 2 ^ 64 -> av W (ms_mem ms1) a = av W mem a).
  { intros a Ha. apply (kept_of_frame _ _ _ _ _ (fun _ : Z => False) HFr); [| exact Ha | intros []].
    intros b wlo whi x Hin.
    lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
    destruct Hin. }
  a2_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + LO_ANN)) G1 ltac:(apply codeptr_val; exact HEI).
  a2_reg HS (Z_to_bv 5 10) (w64 (lc_F cx + 96 + 0)) G10
    ltac:(rewrite Z.add_0_r; apply a2_denot_off; [rewrite (EE0 25%nat 25%bv eq_refl); exact R25 | lia]).
  a2_reg HS (Z_to_bv 5 11) (w64 TRANS_HOST) G11 ltac:(rewrite <- VHOST; apply a2_denot_img; [exact HEI | cbv; lia]).
  a2_reg HS (Z_to_bv 5 12) (w64 6) G12 ltac:(reflexivity).
  a2_reg HS (Z_to_bv 5 20) (w64 0) G20 ltac:(reflexivity).
  a2_reg HS (Z_to_bv 5 23) (w64 0) G23 ltac:(reflexivity).
  a2_reg HS (Z_to_bv 5 2) (YK11.getr regs (Z_to_bv 5 2)) GK2
    ltac:(cbn [sv_denot]; rewrite (EE0 2%nat (Z_to_bv 5 2) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  a2_reg HS (Z_to_bv 5 3) (YK11.getr regs (Z_to_bv 5 3)) GK3
    ltac:(cbn [sv_denot]; rewrite (EE0 3%nat (Z_to_bv 5 3) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  a2_reg HS (Z_to_bv 5 4) (YK11.getr regs (Z_to_bv 5 4)) GK4
    ltac:(cbn [sv_denot]; rewrite (EE0 4%nat (Z_to_bv 5 4) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  a2_reg HS (Z_to_bv 5 8) (YK11.getr regs (Z_to_bv 5 8)) GK8
    ltac:(cbn [sv_denot]; rewrite (EE0 8%nat (Z_to_bv 5 8) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  a2_reg HS (Z_to_bv 5 9) (YK11.getr regs (Z_to_bv 5 9)) GK9
    ltac:(cbn [sv_denot]; rewrite (EE0 9%nat (Z_to_bv 5 9) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  a2_reg HS (Z_to_bv 5 18) (YK11.getr regs (Z_to_bv 5 18)) GK18
    ltac:(cbn [sv_denot]; rewrite (EE0 18%nat (Z_to_bv 5 18) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  a2_reg HS (Z_to_bv 5 19) (YK11.getr regs (Z_to_bv 5 19)) GK19
    ltac:(cbn [sv_denot]; rewrite (EE0 19%nat (Z_to_bv 5 19) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  a2_reg HS (Z_to_bv 5 21) (YK11.getr regs (Z_to_bv 5 21)) GK21
    ltac:(cbn [sv_denot]; rewrite (EE0 21%nat (Z_to_bv 5 21) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  a2_reg HS (Z_to_bv 5 24) (YK11.getr regs (Z_to_bv 5 24)) GK24
    ltac:(cbn [sv_denot]; rewrite (EE0 24%nat (Z_to_bv 5 24) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  a2_reg HS (Z_to_bv 5 25) (YK11.getr regs (Z_to_bv 5 25)) GK25
    ltac:(cbn [sv_denot]; rewrite (EE0 25%nat (Z_to_bv 5 25) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  a2_reg HS (Z_to_bv 5 26) (YK11.getr regs (Z_to_bv 5 26)) GK26
    ltac:(cbn [sv_denot]; rewrite (EE0 26%nat (Z_to_bv 5 26) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  assert (GK : forall r, In r [2; 3; 4; 8; 9; 18; 19; 21; 24; 25; 26] ->
    YK11.getr (ms_regs ms1) (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)).
  { intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<- | Hr]; [assumption |]). destruct Hr. }
  pmkst HS.
  apply (CALL (ms_regs ms1) (ms_mem ms1) md1 0 TRANS_HOST TC.HOST HJ GK (conj G20 G23) KM
    (fun a => a2_pres_grow (w_H W) mem (ms_mem ms1) a HG) ltac:(left; reflexivity) ltac:(lia)
    ltac:(reflexivity) G10 G11 G12 G1).
- destruct (Z_lt_le_dec mac 10) as [M1 | M1]; [|destruct (Z_lt_le_dec mac 13) as [M2 | M2]].
  + (* mac < 10: a0 = s9 + s6, a1 = HOST *)
    pose proof (@a2_entryC (l_fx cx) rc W regs mem (lc_F cx) (lc_sp1 cx) mac 0 9 R9 Hz ltac:(lia) ltac:(lia) ltac:(lia)
      ltac:(lia) ltac:(lia) VS8 VS104 ltac:(lia) ltac:(lia)) as HS. fold E0 in HS.
    unfold lc_cfg, a2_retB. change (w64 (transport_text + 0x9dc)) with (Z_to_bv 64 (BASE + 0x9dc)).
    paj_run_tok RUN HS HJ SHOK (0, 0).
    { a2_awr_rs. apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia|].
      apply awr_ok_x_nil. }
    a2_after.
    lazymatch type of HS with context [restrict _ ?m] => rename m into ms1 end.
    lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => rename m into md1 end.
    assert (KM : forall a, 0 <= a < 2 ^ 64 -> av W (ms_mem ms1) a = av W mem a).
    { intros a Ha. apply (kept_of_frame _ _ _ _ _ (fun _ : Z => False) HFr); [| exact Ha | intros []].
      intros b wlo whi x Hin.
      lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
      cbn [In] in Hin. repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; lia |]). destruct Hin. }
    a2_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + LO_ANN)) G1 ltac:(apply codeptr_val; exact HEI).
    a2_reg HS (Z_to_bv 5 10) (w64 (lc_F cx + 96 + mac)) G10
      ltac:(replace (lc_F cx + 96 + mac) with (mac + (lc_F cx + 96)) by lia;
            apply a2_denot_add; [rewrite (EE0 22%nat 22%bv eq_refl); exact Hz | rewrite (EE0 25%nat 25%bv eq_refl); exact R25
                                 | lia | lia | lia]).
    a2_reg HS (Z_to_bv 5 11) (w64 TRANS_HOST) G11 ltac:(rewrite <- VHOST; apply a2_denot_img; [exact HEI | cbv; lia]).
    a2_reg HS (Z_to_bv 5 12) (w64 6) G12 ltac:(reflexivity).
    a2_reg HS (Z_to_bv 5 2) (YK11.getr regs (Z_to_bv 5 2)) GK2
      ltac:(cbn [sv_denot]; rewrite (EE0 2%nat (Z_to_bv 5 2) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    a2_reg HS (Z_to_bv 5 3) (YK11.getr regs (Z_to_bv 5 3)) GK3
      ltac:(cbn [sv_denot]; rewrite (EE0 3%nat (Z_to_bv 5 3) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    a2_reg HS (Z_to_bv 5 4) (YK11.getr regs (Z_to_bv 5 4)) GK4
      ltac:(cbn [sv_denot]; rewrite (EE0 4%nat (Z_to_bv 5 4) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    a2_reg HS (Z_to_bv 5 8) (YK11.getr regs (Z_to_bv 5 8)) GK8
      ltac:(cbn [sv_denot]; rewrite (EE0 8%nat (Z_to_bv 5 8) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    a2_reg HS (Z_to_bv 5 9) (YK11.getr regs (Z_to_bv 5 9)) GK9
      ltac:(cbn [sv_denot]; rewrite (EE0 9%nat (Z_to_bv 5 9) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    a2_reg HS (Z_to_bv 5 18) (YK11.getr regs (Z_to_bv 5 18)) GK18
      ltac:(cbn [sv_denot]; rewrite (EE0 18%nat (Z_to_bv 5 18) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    a2_reg HS (Z_to_bv 5 19) (YK11.getr regs (Z_to_bv 5 19)) GK19
      ltac:(cbn [sv_denot]; rewrite (EE0 19%nat (Z_to_bv 5 19) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    a2_reg HS (Z_to_bv 5 21) (YK11.getr regs (Z_to_bv 5 21)) GK21
      ltac:(cbn [sv_denot]; rewrite (EE0 21%nat (Z_to_bv 5 21) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    a2_reg HS (Z_to_bv 5 24) (YK11.getr regs (Z_to_bv 5 24)) GK24
      ltac:(cbn [sv_denot]; rewrite (EE0 24%nat (Z_to_bv 5 24) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    a2_reg HS (Z_to_bv 5 25) (YK11.getr regs (Z_to_bv 5 25)) GK25
      ltac:(cbn [sv_denot]; rewrite (EE0 25%nat (Z_to_bv 5 25) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    a2_reg HS (Z_to_bv 5 26) (YK11.getr regs (Z_to_bv 5 26)) GK26
      ltac:(cbn [sv_denot]; rewrite (EE0 26%nat (Z_to_bv 5 26) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    assert (GK : forall r, In r [2; 3; 4; 8; 9; 18; 19; 21; 24; 25; 26] ->
      YK11.getr (ms_regs ms1) (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)).
    { intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<- | Hr]; [assumption |]). destruct Hr. }
    a2_reg HS (Z_to_bv 5 20) (YK11.getr regs (Z_to_bv 5 20)) GZ20
      ltac:(cbn [sv_denot]; rewrite (EE0 20%nat (Z_to_bv 5 20) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    a2_reg HS (Z_to_bv 5 23) (YK11.getr regs (Z_to_bv 5 23)) GZ23
      ltac:(cbn [sv_denot]; rewrite (EE0 23%nat (Z_to_bv 5 23) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    assert (GZ : forall r, In r [20; 23] -> YK11.getr (ms_regs ms1) (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)).
    { intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<- | Hr]; [assumption |]). destruct Hr. }
    pmkst HS.
    apply (CALL (ms_regs ms1) (ms_mem ms1) md1 mac TRANS_HOST TC.HOST HJ GK GZ KM
      (fun a => a2_pres_grow (w_H W) mem (ms_mem ms1) a HG) ltac:(left; reflexivity) ltac:(lia)
      ltac:(unfold a2_body1; destruct (Z.ltb_spec mac 10); [reflexivity | lia]) G10 G11 G12 G1).
  + (* 10 <= mac <= 12: a0 = 8(s1) + s6 = body + mac - 10, a1 = OTHER *)
    pose proof (@a2_entryC (l_fx cx) rc W regs mem (lc_F cx) (lc_sp1 cx) mac 10 12 R9 Hz ltac:(lia) ltac:(lia) ltac:(lia)
      ltac:(lia) ltac:(lia) VS8 VS104 ltac:(lia) ltac:(lia)) as HS. fold E0 in HS.
    unfold lc_cfg, a2_retB. change (w64 (transport_text + 0x9dc)) with (Z_to_bv 64 (BASE + 0x9dc)).
    paj_run_tok RUN HS HJ SHOK (0, 0).
    { a2_awr_rs. apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia|].
      apply awr_ok_x_nil. }
    a2_after.
    lazymatch type of HS with context [restrict _ ?m] => rename m into ms1 end.
    lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => rename m into md1 end.
    assert (KM : forall a, 0 <= a < 2 ^ 64 -> av W (ms_mem ms1) a = av W mem a).
    { intros a Ha. apply (kept_of_frame _ _ _ _ _ (fun _ : Z => False) HFr); [| exact Ha | intros []].
      intros b wlo whi x Hin.
      lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
      cbn [In] in Hin. repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; lia |]). destruct Hin. }
    a2_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + LO_ANN)) G1 ltac:(apply codeptr_val; exact HEI).
    a2_reg HS (Z_to_bv 5 10) (w64 (lc_F cx + 96 + (mac - 10))) G10
      ltac:(replace (lc_F cx + 96 + (mac - 10)) with (mac + (lc_F cx + 86)) by lia;
            apply a2_denot_add; [rewrite (EE0 22%nat 22%bv eq_refl); exact Hz | exact E36 | lia | lia | lia]).
    a2_reg HS (Z_to_bv 5 11) (w64 TRANS_OTHER) G11 ltac:(rewrite <- VOTHER; apply a2_denot_img; [exact HEI | cbv; lia]).
    a2_reg HS (Z_to_bv 5 12) (w64 6) G12 ltac:(reflexivity).
    a2_reg HS (Z_to_bv 5 2) (YK11.getr regs (Z_to_bv 5 2)) GK2
      ltac:(cbn [sv_denot]; rewrite (EE0 2%nat (Z_to_bv 5 2) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    a2_reg HS (Z_to_bv 5 3) (YK11.getr regs (Z_to_bv 5 3)) GK3
      ltac:(cbn [sv_denot]; rewrite (EE0 3%nat (Z_to_bv 5 3) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    a2_reg HS (Z_to_bv 5 4) (YK11.getr regs (Z_to_bv 5 4)) GK4
      ltac:(cbn [sv_denot]; rewrite (EE0 4%nat (Z_to_bv 5 4) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    a2_reg HS (Z_to_bv 5 8) (YK11.getr regs (Z_to_bv 5 8)) GK8
      ltac:(cbn [sv_denot]; rewrite (EE0 8%nat (Z_to_bv 5 8) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    a2_reg HS (Z_to_bv 5 9) (YK11.getr regs (Z_to_bv 5 9)) GK9
      ltac:(cbn [sv_denot]; rewrite (EE0 9%nat (Z_to_bv 5 9) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    a2_reg HS (Z_to_bv 5 18) (YK11.getr regs (Z_to_bv 5 18)) GK18
      ltac:(cbn [sv_denot]; rewrite (EE0 18%nat (Z_to_bv 5 18) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    a2_reg HS (Z_to_bv 5 19) (YK11.getr regs (Z_to_bv 5 19)) GK19
      ltac:(cbn [sv_denot]; rewrite (EE0 19%nat (Z_to_bv 5 19) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    a2_reg HS (Z_to_bv 5 21) (YK11.getr regs (Z_to_bv 5 21)) GK21
      ltac:(cbn [sv_denot]; rewrite (EE0 21%nat (Z_to_bv 5 21) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    a2_reg HS (Z_to_bv 5 24) (YK11.getr regs (Z_to_bv 5 24)) GK24
      ltac:(cbn [sv_denot]; rewrite (EE0 24%nat (Z_to_bv 5 24) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    a2_reg HS (Z_to_bv 5 25) (YK11.getr regs (Z_to_bv 5 25)) GK25
      ltac:(cbn [sv_denot]; rewrite (EE0 25%nat (Z_to_bv 5 25) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    a2_reg HS (Z_to_bv 5 26) (YK11.getr regs (Z_to_bv 5 26)) GK26
      ltac:(cbn [sv_denot]; rewrite (EE0 26%nat (Z_to_bv 5 26) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    assert (GK : forall r, In r [2; 3; 4; 8; 9; 18; 19; 21; 24; 25; 26] ->
      YK11.getr (ms_regs ms1) (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)).
    { intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<- | Hr]; [assumption |]). destruct Hr. }
    a2_reg HS (Z_to_bv 5 20) (YK11.getr regs (Z_to_bv 5 20)) GZ20
      ltac:(cbn [sv_denot]; rewrite (EE0 20%nat (Z_to_bv 5 20) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    a2_reg HS (Z_to_bv 5 23) (YK11.getr regs (Z_to_bv 5 23)) GZ23
      ltac:(cbn [sv_denot]; rewrite (EE0 23%nat (Z_to_bv 5 23) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    assert (GZ : forall r, In r [20; 23] -> YK11.getr (ms_regs ms1) (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)).
    { intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<- | Hr]; [assumption |]). destruct Hr. }
    pmkst HS.
    apply (CALL (ms_regs ms1) (ms_mem ms1) md1 (mac - 10) TRANS_OTHER TC.OTHER HJ GK GZ KM
      (fun a => a2_pres_grow (w_H W) mem (ms_mem ms1) a HG) ltac:(right; reflexivity) ltac:(lia)
      ltac:(unfold a2_body1; destruct (Z.ltb_spec mac 10); [lia|]; destruct (Z.ltb_spec mac 13); [reflexivity | lia])
      G10 G11 G12 G1).
  + (* mac >= 13: to ANN with a0 = 12, no copy *)
    pose proof (@a2_entryC (l_fx cx) rc W regs mem (lc_F cx) (lc_sp1 cx) mac 13 15 R9 Hz ltac:(lia) ltac:(lia) ltac:(lia)
      ltac:(lia) ltac:(lia) VS8 VS104 ltac:(lia) ltac:(lia)) as HS. fold E0 in HS.
    unfold lc_cfg, a2_retB. change (w64 (transport_text + 0x9dc)) with (Z_to_bv 64 (BASE + 0x9dc)).
    paj_run_to_tok RUNTO HS HJ SHOK (0, 0) 0x9f8.
    { a2_awr_rs. apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia|].
      apply awr_ok_x_nil. }
    a2_after.
    lazymatch type of HS with context [restrict _ ?m] => rename m into ms1 end.
    lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => rename m into md1 end.
    assert (KM : forall a, 0 <= a < 2 ^ 64 -> av W (ms_mem ms1) a = av W mem a).
    { intros a Ha. apply (kept_of_frame _ _ _ _ _ (fun _ : Z => False) HFr); [| exact Ha | intros []].
      intros b wlo whi x Hin.
      lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
      cbn [In] in Hin. repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; lia |]). destruct Hin. }
    a2_reg HS (Z_to_bv 5 2) (YK11.getr regs (Z_to_bv 5 2)) GK2
      ltac:(cbn [sv_denot]; rewrite (EE0 2%nat (Z_to_bv 5 2) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    a2_reg HS (Z_to_bv 5 3) (YK11.getr regs (Z_to_bv 5 3)) GK3
      ltac:(cbn [sv_denot]; rewrite (EE0 3%nat (Z_to_bv 5 3) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    a2_reg HS (Z_to_bv 5 4) (YK11.getr regs (Z_to_bv 5 4)) GK4
      ltac:(cbn [sv_denot]; rewrite (EE0 4%nat (Z_to_bv 5 4) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    a2_reg HS (Z_to_bv 5 8) (YK11.getr regs (Z_to_bv 5 8)) GK8
      ltac:(cbn [sv_denot]; rewrite (EE0 8%nat (Z_to_bv 5 8) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    a2_reg HS (Z_to_bv 5 9) (YK11.getr regs (Z_to_bv 5 9)) GK9
      ltac:(cbn [sv_denot]; rewrite (EE0 9%nat (Z_to_bv 5 9) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    a2_reg HS (Z_to_bv 5 18) (YK11.getr regs (Z_to_bv 5 18)) GK18
      ltac:(cbn [sv_denot]; rewrite (EE0 18%nat (Z_to_bv 5 18) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    a2_reg HS (Z_to_bv 5 19) (YK11.getr regs (Z_to_bv 5 19)) GK19
      ltac:(cbn [sv_denot]; rewrite (EE0 19%nat (Z_to_bv 5 19) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    a2_reg HS (Z_to_bv 5 20) (YK11.getr regs (Z_to_bv 5 20)) GK20
      ltac:(cbn [sv_denot]; rewrite (EE0 20%nat (Z_to_bv 5 20) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    a2_reg HS (Z_to_bv 5 21) (YK11.getr regs (Z_to_bv 5 21)) GK21
      ltac:(cbn [sv_denot]; rewrite (EE0 21%nat (Z_to_bv 5 21) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    a2_reg HS (Z_to_bv 5 23) (YK11.getr regs (Z_to_bv 5 23)) GK23
      ltac:(cbn [sv_denot]; rewrite (EE0 23%nat (Z_to_bv 5 23) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    a2_reg HS (Z_to_bv 5 24) (YK11.getr regs (Z_to_bv 5 24)) GK24
      ltac:(cbn [sv_denot]; rewrite (EE0 24%nat (Z_to_bv 5 24) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    a2_reg HS (Z_to_bv 5 25) (YK11.getr regs (Z_to_bv 5 25)) GK25
      ltac:(cbn [sv_denot]; rewrite (EE0 25%nat (Z_to_bv 5 25) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    a2_reg HS (Z_to_bv 5 26) (YK11.getr regs (Z_to_bv 5 26)) GK26
      ltac:(cbn [sv_denot]; rewrite (EE0 26%nat (Z_to_bv 5 26) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    pmkst HS.
    apply SRr_ret.
    destruct (a2_move B MT XL RLO RHI cx op false true true (lo_k op) ly S W regs mem md e (ms_regs ms1) (ms_mem ms1) md1 0
      LAWS HGX HB HL HTW HJ) as [HL1 HTW1].
    { intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<- | Hr]; [assumption |]). destruct Hr. }
    { unfold LLVMF_STK. lia. }
    { intros a Ha _. exact (KM a Ha). }
    { exact (fun a => a2_pres_grow (w_H W) mem (ms_mem ms1) a HG). }
    { intros i Hi. rewrite KM; [exact (HFSH i Hi)|]. pose proof (Z.div_pos (lc_F cx) 8 ltac:(lia) ltac:(lia)).
      unfold lc_SH, SHADOW_OFF. lia. }
    exists (ms_regs ms1), (ms_mem ms1), md1. split.
    { unfold lc_cfg, w64, LO_ANN. rewrite HBASE, HTT. reflexivity. }
    split; [exact HL1|]. split; [exact HTW1|]. split.
    { replace (TW.zs (a2_body1 mac)) with (repeat 0 34)
        by (unfold a2_body1; destruct (Z.ltb_spec mac 10); [lia|]; destruct (Z.ltb_spec mac 13); [lia|]; reflexivity).
      apply (lc_garr8_kept (w_H W) (w_H W) mem (ms_mem ms1) (lc_F cx + 96) _); [|exact HZ].
      intros j Hj. rewrite repeat_length in Hj. apply KM. lia. }
    split.
    { intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<- | Hr]; [assumption |]). destruct Hr. }
    intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<- | Hr]; [assumption |]). destruct Hr.
Qed.

(* From +0x858 (z = true) or +0x9ac (z = false) to ANN: a2_setB, then a2_tail. *)
Lemma a2_rest : forall cx op (z : bool) ly S (W : world segs) regs mem md e,
  @lp_prem rc B MT XL RLO RHI -> @lc_base rc B MT XL RLO RHI cx ->
  @lc_lcore rc B MT cx op false false (lo_k op) ly S W regs mem md e -> lc_tw W mem (lo_B op) ->
  lc_opc (l_pl cx) (lo_c op) = 2 ->
  let av := lc_ann_vals (l_pl cx) (lc_oc (l_pl cx) (lo_c op)) in
  YK11.getr regs 19 = w64 (av_sel av) ->
  (if z then av_mac av = 0 /\ av_nm av = 0 /\ YK11.getr regs 24 = w64 (l_p cx + TOP.fi_off (av_c av)) /\
             TOP.fi_n (av_c av) = 0
   else Z.land (bv_unsigned (YK11.getr regs 10)) 15 = av_mac av /\ YK11.getr regs 20 = w64 (av_nm av) /\
        lc_cur cx regs 24 23 (av_c av)) ->
  0 <= av_mac av < 16 ->
  av_body1 av = a2_body1 (av_mac av) ->
  SRr segs W (mkCfg (@YK11.mkst (l_fx cx) regs (Z_to_bv 64 (BASE + if z then 0x858 else 0x9ac)) mem (YK11.seg_rom segs)) md)
    (@lc_st_ann rc B MT cx op).
Proof.
intros cx op z ly S W regs mem md e HP HB HL HTW Hopc av R19 Hz Hmac Hbody.
assert (HBASE : BASE = 0x81264) by (vm_compute; reflexivity).
assert (HTT : transport_text = 0x81264) by (vm_compute; reflexivity).
replace (mkCfg (@YK11.mkst (l_fx cx) regs (Z_to_bv 64 (BASE + if z then 0x858 else 0x9ac)) mem (YK11.seg_rom segs)) md)
  with (lc_cfg cx (if z then 0x858 else 0x9ac) regs mem md) by (unfold lc_cfg, w64; rewrite HBASE, HTT; reflexivity).
eapply SRr_bind; [exact (a2_setB cx op z ly S W regs mem md e HP HB HL HTW)|].
intros W1 c1 _ (regs1 & mem1 & md1 & -> & HL1 & HTW1 & HZ1 & K1 & R25 & R22).
eapply SRr_bind.
{ apply (a2_tail cx op z ly S W1 regs1 mem1 md1 e (av_mac av) HP HB HL1 HTW1 HZ1 R25).
  - destruct z.
    + exact (proj1 Hz).
    + rewrite (R22 eq_refl). f_equal. exact (proj1 Hz).
  - exact Hmac. }
intros W2 c2 _ (regs2 & mem2 & md2 & -> & HL2 & HTW2 & HZ2 & K2 & KZ).
apply SRr_ret.
exists ly, S, regs2, mem2, md2, e. cbv zeta. fold av.
split; [reflexivity|]. split; [exact Hopc|]. split; [exact HL2|]. split; [exact HTW2|].
split; [rewrite Hbody; exact HZ2|].
assert (E19 : YK11.getr regs2 (Z_to_bv 5 19) = YK11.getr regs (Z_to_bv 5 19))
  by exact (eq_trans (K2 19 ltac:(cbn; tauto)) (K1 19 ltac:(cbn; tauto))).
assert (E24 : YK11.getr regs2 (Z_to_bv 5 24) = YK11.getr regs (Z_to_bv 5 24))
  by exact (eq_trans (K2 24 ltac:(cbn; tauto)) (K1 24 ltac:(cbn; tauto))).
assert (E25 : YK11.getr regs2 (Z_to_bv 5 25) = YK11.getr regs1 (Z_to_bv 5 25)) by exact (K2 25 ltac:(cbn; tauto)).
split; [exact (eq_trans E19 R19)|].
destruct z.
- destruct KZ as (K20 & K23). destruct Hz as (Hm & Hn & H24 & Hc).
  split; [refine (eq_trans K20 _); rewrite Hn; reflexivity|].
  split; [exact (eq_trans E25 R25)|].
  split; [exact (eq_trans E24 H24) | refine (eq_trans K23 _); rewrite Hc; reflexivity].
- destruct Hz as (Hm & H20 & H24 & H23).
  assert (E20 : YK11.getr regs2 (Z_to_bv 5 20) = YK11.getr regs (Z_to_bv 5 20))
    by exact (eq_trans (KZ 20 ltac:(cbn; tauto)) (K1 20 ltac:(cbn; tauto))).
  assert (E23 : YK11.getr regs2 (Z_to_bv 5 23) = YK11.getr regs (Z_to_bv 5 23))
    by exact (eq_trans (KZ 23 ltac:(cbn; tauto)) (K1 23 ltac:(cbn; tauto))).
  split; [exact (eq_trans E20 H20)|].
  split; [exact (eq_trans E25 R25)|].
  split; [exact (eq_trans E24 H24) | exact (eq_trans E23 H23)].
Qed.

Lemma a2_at8_range : forall D i, 0 <= DSpec.at8 D i < 256.
Proof.
intros D i. unfold DSpec.at8, DSpec.bz. pose proof (bv_unsigned_in_range 8 (nth i D (DSpec.b8 0))) as H.
unfold bv_modulus in H. change (2 ^ Z.of_N 8) with 256 in H. exact H.
Qed.

Lemma lc_op2a_ok : lc_op2a_stmt B MT XL RLO RHI.
Proof.
unfold lc_op2a_stmt.
intros HP cx op W' c HB (ly' & S' & regs' & mem' & md' & e & -> & Ho & HL & HTW & (C25 & C27) & (C24 & C23) & R20 & R22).
pose proof HL as HLc.
pose proof (lp_laws _ _ _ _ _ HP) as LAWS.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned _ _ _ _ _ HP)) as HGX.
destruct HL as (HC & HFR & HSP & HFSH & HOK & He & HMT & R21).
pose proof HOK as (HAG & Hops & Hfin & Hfn & Hk).
pose proof (lc_geom B MT XL RLO RHI cx ly' S' W' regs' mem' md' e HB HC) as GEO.
destruct GEO as [HAR Hsp0al Hstk Hsp1c HFaddr HFin Hn HINg HLIVE].
pose proof HC as (HJ & Hfrs & HlyF & HPERM & Rsp & R8 & R9 & Rgp & Rtp & Hsp1 & Hsp1al & HSAV & HF4096 & HFal &
  HFceil & HFpres & HFL & HIN).
destruct HFR as (R18 & R26).
pose proof asan_consts as (CC1 & CC2 & CC3 & CC4 & CC5).
set (D := l_pl cx) in *.
destruct (lo_c op) as [o0 n0] eqn:Ec. cbn [TOP.fi_off TOP.fi_n] in *.
assert (Ec1 : lc_oc D (TOP.FuzzIn o0 n0) = TOP.FuzzIn (o0 + 1) (n0 - 1)).
{ unfold lc_oc, TOP.fuzz_u8_m. cbn [TOP.fi_n TOP.fi_off]. destruct (Z.eqb_spec n0 0); [lia|reflexivity]. }
rewrite Ec1 in C24, C23. cbn [TOP.fi_off TOP.fi_n] in C24, C23.
destruct Hfin as (Hfo & Hfn' & Hfl). cbn [TOP.fi_off TOP.fi_n] in Hfo, Hfn', Hfl.
destruct Hn as (Hn1 & Hnl). fold D in Hnl.
(* the input block *)
pose proof (HINg ltac:(lia)) as InP.
destruct (al_blocks _ _ LAWS ly' S' W' mem' md' (l_p cx) (l_n cx) HAR InP) as (_ & Hb4 & Hbc & Hbapp & _).
pose proof (req_size_pos (l_n cx) ltac:(lia)) as (Hq1 & Hq2).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hbapp.
set (q := l_p cx + o0).
destruct HIN as (HPAYg & HPAYv).
assert (VB : forall j, 0 <= j < l_n cx ->
  val_mem segs (mrestrict (w_H W') mem') (l_p cx + j) 1 (DSpec.at8 D (Z.to_nat j)) /\ 0 <= DSpec.at8 D (Z.to_nat j) < 256).
{ intros j Hj.
  assert (Hjl : (Z.to_nat j < length (map (fun b : byte => bv_unsigned b) D))%nat) by (rewrite length_map; lia).
  destruct (garr8_nthZ segs _ _ _ j HPAYg ltac:(lia) Hjl) as (Hv & Hr).
  unfold DSpec.at8, DSpec.bz. rewrite <- (map_nth (fun b : byte => bv_unsigned b) D (DSpec.b8 0)).
  change (bv_unsigned (DSpec.b8 0)) with 0. exact (conj Hv Hr). }
set (b1 := DSpec.at8 D (Z.to_nat (o0 + 1))). set (b2 := DSpec.at8 D (Z.to_nat (o0 + 2))).
set (b3 := DSpec.at8 D (Z.to_nat (o0 + 3))).
pose proof (a2_at8_range D (Z.to_nat (o0 + 1))) as B1. pose proof (a2_at8_range D (Z.to_nat (o0 + 2))) as B2.
pose proof (a2_at8_range D (Z.to_nat (o0 + 3))) as B3. fold b1 in B1. fold b2 in B2. fold b3 in B3.
assert (V1 : 1 <= n0 - 1 -> val_mem segs (mrestrict (w_H W') mem') (q + 1) 1 b1).
{ intros Hk1. replace (q + 1) with (l_p cx + (o0 + 1)) by (unfold q; lia). exact (proj1 (VB (o0 + 1) ltac:(lia))). }
assert (V2 : 2 <= n0 - 1 -> val_mem segs (mrestrict (w_H W') mem') (q + 2) 1 b2).
{ intros Hk1. replace (q + 2) with (l_p cx + (o0 + 2)) by (unfold q; lia). exact (proj1 (VB (o0 + 2) ltac:(lia))). }
assert (V3 : 3 <= n0 - 1 -> val_mem segs (mrestrict (w_H W') mem') (q + 3) 1 b3).
{ intros Hk1. replace (q + 3) with (l_p cx + (o0 + 3)) by (unfold q; lia). exact (proj1 (VB (o0 + 3) ltac:(lia))). }
(* the spills *)
assert (HSPv : forall o v, In (o, v) (lf_spill_loop (lc_F cx)) ->
  val_mem segs (mrestrict (w_H W') mem') (lc_sp1 cx + o) 8 v).
{ intros o v Hin. unfold lc_spills in HSP. rewrite Forall_forall in HSP. apply val_mem_of_rdword. exact (HSP _ Hin). }
pose proof (HSPv 8 (lc_F cx + 86) ltac:(unfold lf_spill_loop; apply in_or_app; right; cbn; tauto)) as VS8.
pose proof (HSPv 104 (lc_F cx + 96) ltac:(unfold lf_spill_loop; apply in_or_app; right; cbn; tauto)) as VS104.
(* the frame's shadow *)
assert (ESH : lc_SH cx = SHADOW_OFF + lc_F cx / 8) by reflexivity.
assert (HSH0 : SHADOW_OFF <= lc_SH cx /\ lc_SH cx + 32 <= 17594333495296).
{ rewrite ESH. unfold SHADOW_OFF, LF_FBYTES in *. split; [pose proof (Z.div_pos (lc_F cx) 8 ltac:(lia) ltac:(lia)); lia|].
  assert (lc_F cx / 8 <= 0x7fffff800000 / 8) by (apply Z.div_le_mono; lia).
  change (0x7fffff800000 / 8) with 0xffffff00000 in *. lia. }
assert (Hpres : forall a, lc_SH cx + 12 <= a < lc_SH cx + 17 -> apresent (w_H W') mem' a).
{ intros a Ha. apply (apresent_of_aview segs); [unfold SHADOW_OFF in *; lia | |].
  - intros Hi. pose proof (transport_segs_low a Hi) as Hl. unfold kLowMemEnd, SHADOW_OFF in *. lia.
  - replace a with (lc_SH cx + (a - lc_SH cx)) by lia.
    rewrite (HFSH (a - lc_SH cx) ltac:(lia)). discriminate. }
destruct Hstk as (Hceil & Hslo & Hshi & H47).
unfold LLVMF_STK, LF_FRAME, LF_FBYTES in *.
assert (C25' : YK11.getr regs' 25 = w64 q) by exact C25.
assert (C24' : YK11.getr regs' 24 = w64 (q + 1)) by (refine (eq_trans C24 _); unfold q; f_equal; lia).
assert (C23' : YK11.getr regs' 23 = w64 (n0 - 1)) by exact C23.
assert (C27' : YK11.getr regs' 27 = w64 (n0 - 1 + 1)) by (refine (eq_trans C27 _); f_equal; lia).
pose proof (@paj_run_to_x (l_fx cx) rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS
  HGX 0 []) as RUNTO.
unfold lc_cfg.
change (w64 (transport_text + lo_arm 2)) with (Z_to_bv 64 (BASE + 1380)).
assert (Hk4 : n0 - 1 = 0 \/ n0 - 1 = 1 \/ n0 - 1 = 2 \/ 3 <= n0 - 1) by lia.
destruct Hk4 as [HK | [HK | [HK | HK]]].
- (* n1 = 0 *)
  pose proof (@a2_entryK (l_fx cx) rc W' regs' mem' q (n0 - 1) b1 b2 (lc_F cx) C25' C24' C23' C27' R26
    ltac:(unfold q; lia) ltac:(unfold q; lia) ltac:(lia) V1 V2 B1 B2) as HS.
  rewrite HK in HS.
  set (E0 := a2_E regs' b1 b2 0 (lc_F cx)) in *.
  assert (HEI : img_env VAL A_LIM E0) by apply a2_env_img.
  assert (SHOK : sh_ok segs A2_Bx [] E0 (mrestrict (w_H W') mem')) by constructor.
  assert (EE0 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E0 n = YK11.getr regs' r)
    by (intros; apply a2_ew_reg; assumption).
  assert (UE24 : forall k, 0 <= k <= 8 -> U E0 (SOff 24 k) = q + 1 + k).
  { intros k Hk0. apply U_atom_off; [rewrite (EE0 24%nat 24%bv eq_refl); exact C24' | lia | lia]. }
  assert (UE25 : forall k, 0 <= k <= 8 -> U E0 (SOff 25 k) = q + k).
  { intros k Hk0. apply U_atom_off; [rewrite (EE0 25%nat 25%bv eq_refl); exact C25' | lia | lia]. }
  pose proof (paj_branch (fx := l_fx cx) (PI := PI_transport)) as BR.
  (* +0x564 `beqz s7`: s7 = 0, so the fall-through is refuted *)
  psrr_branch_tok RUNTO BR HS SHOK YC4b.Bspan.
  2:{ exfalso. cbn [sv_denot] in Hc. rewrite (EE0 23%nat 23%bv eq_refl), C23', HK in Hc.
      vm_compute in Hc. discriminate Hc. }
  clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan 0x858.
  all: try (cbn [ms_mem]; eapply (obl_of_block segs B LAWS ly' S' W' mem' md' E0 (SOff 26 0) _ 1 (l_p cx) (l_n cx) HAR InP);
    [ apply U_atom; [rewrite (EE0 26%nat 26%bv eq_refl); exact R26 | unfold SHADOW_OFF; lia]
    | rewrite ?UE24, ?UE25 by lia; unfold q; lia | rewrite ?UE24, ?UE25 by lia; unfold q; lia ]).
  all: try (a2_awr_rs; intros a (r & Hin & Hr); cbn [In] in Hin;
    repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_wlo YP09.r_whi] in Hr; lia|]); destruct Hin).
  all: try (a2_awr_rs; apply awr_ok_x_nil).
  a2_after.
  lazymatch type of HS with context [restrict _ ?m] => rename m into ms1 end.
  lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => rename m into md1 end.
  assert (KM : forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W') (ms_mem ms1) a = aview segs (w_H W') mem' a).
  { intros a Ha. apply (kept_of_frame _ _ _ _ _ (fun _ : Z => False) HFr); [| exact Ha | intros []].
    intros b wlo whi x Hin.
    lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
    cbn [In] in Hin. repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; lia |]). destruct Hin. }
  lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
    assert (AGX : forall n, (n < 240)%nat -> ew Ex n = ew E0 n)
      by (intros nn Hnn; repeat rewrite ew_ewset_other by lia; reflexivity) end.
  assert (KP : forall a, apresent (w_H W') mem' a -> apresent (w_H W') (ms_mem ms1) a)
    by (intros a Ha; exact (a2_pres_grow _ _ _ a HG Ha)).
  a2_reg HS (Z_to_bv 5 2) (YK11.getr regs' (Z_to_bv 5 2)) GK2
    ltac:(cbn [sv_denot]; (try rewrite AGX by lia); rewrite (EE0 2%nat (Z_to_bv 5 2) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  a2_reg HS (Z_to_bv 5 3) (YK11.getr regs' (Z_to_bv 5 3)) GK3
    ltac:(cbn [sv_denot]; (try rewrite AGX by lia); rewrite (EE0 3%nat (Z_to_bv 5 3) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  a2_reg HS (Z_to_bv 5 4) (YK11.getr regs' (Z_to_bv 5 4)) GK4
    ltac:(cbn [sv_denot]; (try rewrite AGX by lia); rewrite (EE0 4%nat (Z_to_bv 5 4) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  a2_reg HS (Z_to_bv 5 8) (YK11.getr regs' (Z_to_bv 5 8)) GK8
    ltac:(cbn [sv_denot]; (try rewrite AGX by lia); rewrite (EE0 8%nat (Z_to_bv 5 8) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  a2_reg HS (Z_to_bv 5 9) (YK11.getr regs' (Z_to_bv 5 9)) GK9
    ltac:(cbn [sv_denot]; (try rewrite AGX by lia); rewrite (EE0 9%nat (Z_to_bv 5 9) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  a2_reg HS (Z_to_bv 5 18) (YK11.getr regs' (Z_to_bv 5 18)) GK18
    ltac:(cbn [sv_denot]; (try rewrite AGX by lia); rewrite (EE0 18%nat (Z_to_bv 5 18) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  a2_reg HS (Z_to_bv 5 21) (YK11.getr regs' (Z_to_bv 5 21)) GK21
    ltac:(cbn [sv_denot]; (try rewrite AGX by lia); rewrite (EE0 21%nat (Z_to_bv 5 21) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  a2_reg HS (Z_to_bv 5 26) (YK11.getr regs' (Z_to_bv 5 26)) GK26
    ltac:(cbn [sv_denot]; (try rewrite AGX by lia); rewrite (EE0 26%nat (Z_to_bv 5 26) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  a2_reg HS (Z_to_bv 5 19) (w64 0) G19 ltac:(reflexivity).
  a2_reg HS (Z_to_bv 5 24) (YK11.getr regs' (Z_to_bv 5 24)) G24
    ltac:(cbn [sv_denot]; (try rewrite AGX by lia); rewrite (EE0 24%nat (Z_to_bv 5 24) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  pmkst HS.
  destruct (a2_move B MT XL RLO RHI cx op false false false (lo_k op) ly' S' W' regs' mem' md' e (ms_regs ms1) (ms_mem ms1) md1 0
    LAWS HGX HB HLc HTW HJ) as [HL1 HTW1].
  { intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<- | Hr]; [assumption |]). destruct Hr. }
  { unfold LLVMF_STK. lia. }
  { intros a Ha _. exact (KM a Ha). }
  { exact KP. }
  { intros i Hi. rewrite KM; [exact (HFSH i Hi)|]. pose proof (Z.div_pos (lc_F cx) 8 ltac:(lia) ltac:(lia)).
    unfold lc_SH, SHADOW_OFF. lia. }
  pose proof (a2_vals D (TOP.FuzzIn (o0 + 1) (n0 - 1)) ltac:(cbn; lia)) as AV. cbv zeta in AV.
  cbn [TOP.fi_off TOP.fi_n] in AV.
  destruct AV as (AS & AM & AN & AC & AB).
  rewrite <- Ec1, <- Ec in AS, AM, AN, AC, AB.
  set (avv := lc_ann_vals D (lc_oc D (lo_c op))) in AS, AM, AN, AC, AB.
  a2_ifs AS. a2_ifs AM. a2_ifs AN. a2_ifs AC.
  change (Z_to_bv 64 (BASE + 0x858)) with (Z_to_bv 64 (BASE + if true then 0x858 else 0x9ac)).
  apply (a2_rest cx op true ly' S' W' (ms_regs ms1) (ms_mem ms1) md1 e HP HB HL1 HTW1 ltac:(rewrite Ec; symmetry; exact Ho)).
  all: cbv zeta; fold D; fold avv.
  + rewrite AS. exact G19.
  + rewrite AM, AN, AC. cbn [TOP.fi_off TOP.fi_n].
    split; [reflexivity|]. split; [reflexivity|]. split; [|reflexivity].
    refine (eq_trans G24 _). refine (eq_trans C24' _). unfold w64. f_equal. unfold q. lia.
  + rewrite AM. lia.
  + rewrite AB. reflexivity.
- (* n1 = 1 *)
  pose proof (@a2_entryK (l_fx cx) rc W' regs' mem' q (n0 - 1) b1 b2 (lc_F cx) C25' C24' C23' C27' R26
    ltac:(unfold q; lia) ltac:(unfold q; lia) ltac:(lia) V1 V2 B1 B2) as HS.
  rewrite HK in HS.
  set (E0 := a2_E regs' b1 b2 0 (lc_F cx)) in *.
  assert (HEI : img_env VAL A_LIM E0) by apply a2_env_img.
  assert (SHOK : sh_ok segs A2_Bx [] E0 (mrestrict (w_H W') mem')) by constructor.
  assert (EE0 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E0 n = YK11.getr regs' r)
    by (intros; apply a2_ew_reg; assumption).
  assert (UE24 : forall k, 0 <= k <= 8 -> U E0 (SOff 24 k) = q + 1 + k).
  { intros k Hk0. apply U_atom_off; [rewrite (EE0 24%nat 24%bv eq_refl); exact C24' | lia | lia]. }
  assert (UE25 : forall k, 0 <= k <= 8 -> U E0 (SOff 25 k) = q + k).
  { intros k Hk0. apply U_atom_off; [rewrite (EE0 25%nat 25%bv eq_refl); exact C25' | lia | lia]. }
  paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan 0x858.
  all: try (cbn [ms_mem]; eapply (obl_of_block segs B LAWS ly' S' W' mem' md' E0 (SOff 26 0) _ 1 (l_p cx) (l_n cx) HAR InP);
    [ apply U_atom; [rewrite (EE0 26%nat 26%bv eq_refl); exact R26 | unfold SHADOW_OFF; lia]
    | rewrite ?UE24, ?UE25 by lia; unfold q; lia | rewrite ?UE24, ?UE25 by lia; unfold q; lia ]).
  all: try (a2_awr_rs; intros a (r & Hin & Hr); cbn [In] in Hin;
    repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_wlo YP09.r_whi] in Hr; lia|]); destruct Hin).
  all: try (a2_awr_rs; apply awr_ok_x_nil).
  a2_after.
  lazymatch type of HS with context [restrict _ ?m] => rename m into ms1 end.
  lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => rename m into md1 end.
  assert (KM : forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W') (ms_mem ms1) a = aview segs (w_H W') mem' a).
  { intros a Ha. apply (kept_of_frame _ _ _ _ _ (fun _ : Z => False) HFr); [| exact Ha | intros []].
    intros b wlo whi x Hin.
    lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
    cbn [In] in Hin. repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; lia |]). destruct Hin. }
  lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
    assert (AGX : forall n, (n < 240)%nat -> ew Ex n = ew E0 n)
      by (intros nn Hnn; repeat rewrite ew_ewset_other by lia; reflexivity) end.
  (* the branch at +0x584: s11 = 2 *)
  rename KM into KM0, AGX into AGX0, HG into HG0, ms1 into ms0, md1 into md0. clear HF HFr.
  pose proof (paj_branch (fx := l_fx cx) (PI := PI_transport)) as BR.
  psrr_branch_tok RUNTO BR HS SHOK YC4b.Bspan.
  2:{ exfalso. cbn [sv_denot] in Hc. rewrite AGX0 in Hc by lia. rewrite (EE0 27%nat 27%bv eq_refl), C27', HK in Hc.
      vm_compute in Hc. discriminate Hc. }
  clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan 0x858.
  all: try (a2_awr_rs; intros a (r & Hin & Hr); cbn [In] in Hin;
    repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_wlo YP09.r_whi] in Hr; lia|]); destruct Hin).
  all: try (a2_awr_rs; apply awr_ok_x_nil).
  a2_after.
  lazymatch type of HS with context [restrict _ ?m] => rename m into ms1 end.
  lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => rename m into md1 end.
  assert (KM1 : forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W') (ms_mem ms1) a = aview segs (w_H W') (ms_mem ms0) a).
  { intros a Ha. apply (kept_of_frame _ _ _ _ _ (fun _ : Z => False) HFr); [| exact Ha | intros []].
    intros b wlo whi x Hin.
    lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
    cbn [In] in Hin. repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; lia |]). destruct Hin. }
  assert (KM : forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W') (ms_mem ms1) a = aview segs (w_H W') mem' a)
    by (intros a Ha; rewrite (KM1 a Ha); exact (KM0 a Ha)).
  assert (KP : forall a, apresent (w_H W') mem' a -> apresent (w_H W') (ms_mem ms1) a)
    by (intros a Ha; exact (a2_pres_grow _ _ _ a HG (a2_pres_grow _ _ _ a HG0 Ha))).
  lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
    assert (AGX : forall n, (n < 240)%nat -> ew Ex n = ew E0 n)
      by (intros nn Hnn; repeat rewrite ew_ewset_other by lia; first [reflexivity | apply AGX0; exact Hnn]) end.
  a2_reg HS (Z_to_bv 5 2) (YK11.getr regs' (Z_to_bv 5 2)) GK2
    ltac:(cbn [sv_denot]; (try rewrite AGX by lia); rewrite (EE0 2%nat (Z_to_bv 5 2) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  a2_reg HS (Z_to_bv 5 3) (YK11.getr regs' (Z_to_bv 5 3)) GK3
    ltac:(cbn [sv_denot]; (try rewrite AGX by lia); rewrite (EE0 3%nat (Z_to_bv 5 3) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  a2_reg HS (Z_to_bv 5 4) (YK11.getr regs' (Z_to_bv 5 4)) GK4
    ltac:(cbn [sv_denot]; (try rewrite AGX by lia); rewrite (EE0 4%nat (Z_to_bv 5 4) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  a2_reg HS (Z_to_bv 5 8) (YK11.getr regs' (Z_to_bv 5 8)) GK8
    ltac:(cbn [sv_denot]; (try rewrite AGX by lia); rewrite (EE0 8%nat (Z_to_bv 5 8) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  a2_reg HS (Z_to_bv 5 9) (YK11.getr regs' (Z_to_bv 5 9)) GK9
    ltac:(cbn [sv_denot]; (try rewrite AGX by lia); rewrite (EE0 9%nat (Z_to_bv 5 9) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  a2_reg HS (Z_to_bv 5 18) (YK11.getr regs' (Z_to_bv 5 18)) GK18
    ltac:(cbn [sv_denot]; (try rewrite AGX by lia); rewrite (EE0 18%nat (Z_to_bv 5 18) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  a2_reg HS (Z_to_bv 5 21) (YK11.getr regs' (Z_to_bv 5 21)) GK21
    ltac:(cbn [sv_denot]; (try rewrite AGX by lia); rewrite (EE0 21%nat (Z_to_bv 5 21) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  a2_reg HS (Z_to_bv 5 26) (YK11.getr regs' (Z_to_bv 5 26)) GK26
    ltac:(cbn [sv_denot]; (try rewrite AGX by lia); rewrite (EE0 26%nat (Z_to_bv 5 26) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  a2_reg HS (Z_to_bv 5 19) (w64 b1) G19 ltac:(apply a2_denot_off; [(try rewrite AGX by lia); exact (a2_ew_x regs' b1 b2 0 (lc_F cx) 0 ltac:(lia)) | lia]).
  a2_reg HS (Z_to_bv 5 24) (w64 (q + 2)) G24
    ltac:(rewrite denot_lit_U, (U_atom_off _ 25 q 2)
      by (first [(try rewrite AGX by lia); rewrite (EE0 25%nat 25%bv eq_refl); exact C25' | unfold q in *; lia]); reflexivity).
  pmkst HS.
  destruct (a2_move B MT XL RLO RHI cx op false false false (lo_k op) ly' S' W' regs' mem' md' e (ms_regs ms1) (ms_mem ms1) md1 0
    LAWS HGX HB HLc HTW HJ) as [HL1 HTW1].
  { intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<- | Hr]; [assumption |]). destruct Hr. }
  { unfold LLVMF_STK. lia. }
  { intros a Ha _. exact (KM a Ha). }
  { exact KP. }
  { intros i Hi. rewrite KM; [exact (HFSH i Hi)|]. pose proof (Z.div_pos (lc_F cx) 8 ltac:(lia) ltac:(lia)).
    unfold lc_SH, SHADOW_OFF. lia. }
  pose proof (a2_vals D (TOP.FuzzIn (o0 + 1) (n0 - 1)) ltac:(cbn; lia)) as AV. cbv zeta in AV.
  cbn [TOP.fi_off TOP.fi_n] in AV.
  destruct AV as (AS & AM & AN & AC & AB).
  rewrite <- Ec1, <- Ec in AS, AM, AN, AC, AB.
  set (avv := lc_ann_vals D (lc_oc D (lo_c op))) in AS, AM, AN, AC, AB.
  a2_ifs AS. a2_ifs AM. a2_ifs AN. a2_ifs AC.
  change (Z_to_bv 64 (BASE + 0x858)) with (Z_to_bv 64 (BASE + if true then 0x858 else 0x9ac)).
  apply (a2_rest cx op true ly' S' W' (ms_regs ms1) (ms_mem ms1) md1 e HP HB HL1 HTW1 ltac:(rewrite Ec; symmetry; exact Ho)).
  all: cbv zeta; fold D; fold avv.
  + rewrite AS. exact G19.
  + rewrite AM, AN, AC. cbn [TOP.fi_off TOP.fi_n].
    split; [reflexivity|]. split; [reflexivity|]. split; [|reflexivity].
    refine (eq_trans G24 _). unfold w64. f_equal. unfold q. lia.
  + rewrite AM. lia.
  + rewrite AB. reflexivity.
- (* n1 = 2 *)
  pose proof (@a2_entryK (l_fx cx) rc W' regs' mem' q (n0 - 1) b1 b2 (lc_F cx) C25' C24' C23' C27' R26
    ltac:(unfold q; lia) ltac:(unfold q; lia) ltac:(lia) V1 V2 B1 B2) as HS.
  rewrite HK in HS.
  set (E0 := a2_E regs' b1 b2 0 (lc_F cx)) in *.
  assert (HEI : img_env VAL A_LIM E0) by apply a2_env_img.
  assert (SHOK : sh_ok segs A2_Bx [] E0 (mrestrict (w_H W') mem')) by constructor.
  assert (EE0 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E0 n = YK11.getr regs' r)
    by (intros; apply a2_ew_reg; assumption).
  assert (UE24 : forall k, 0 <= k <= 8 -> U E0 (SOff 24 k) = q + 1 + k).
  { intros k Hk0. apply U_atom_off; [rewrite (EE0 24%nat 24%bv eq_refl); exact C24' | lia | lia]. }
  assert (UE25 : forall k, 0 <= k <= 8 -> U E0 (SOff 25 k) = q + k).
  { intros k Hk0. apply U_atom_off; [rewrite (EE0 25%nat 25%bv eq_refl); exact C25' | lia | lia]. }
  paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan 0x9ac.
  all: try (cbn [ms_mem]; eapply (obl_of_block segs B LAWS ly' S' W' mem' md' E0 (SOff 26 0) _ 1 (l_p cx) (l_n cx) HAR InP);
    [ apply U_atom; [rewrite (EE0 26%nat 26%bv eq_refl); exact R26 | unfold SHADOW_OFF; lia]
    | rewrite ?UE24, ?UE25 by lia; unfold q; lia | rewrite ?UE24, ?UE25 by lia; unfold q; lia ]).
  all: try (a2_awr_rs; intros a (r & Hin & Hr); cbn [In] in Hin;
    repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_wlo YP09.r_whi] in Hr; lia|]); destruct Hin).
  all: try (a2_awr_rs; apply awr_ok_x_nil).
  a2_after.
  lazymatch type of HS with context [restrict _ ?m] => rename m into ms1 end.
  lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => rename m into md1 end.
  assert (KM : forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W') (ms_mem ms1) a = aview segs (w_H W') mem' a).
  { intros a Ha. apply (kept_of_frame _ _ _ _ _ (fun _ : Z => False) HFr); [| exact Ha | intros []].
    intros b wlo whi x Hin.
    lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
    cbn [In] in Hin. repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; lia |]). destruct Hin. }
  lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
    assert (AGX : forall n, (n < 240)%nat -> ew Ex n = ew E0 n)
      by (intros nn Hnn; repeat rewrite ew_ewset_other by lia; reflexivity) end.
  (* the branch at +0x5a4: s11 = 3 *)
  rename KM into KM0, AGX into AGX0, HG into HG0, ms1 into ms0, md1 into md0. clear HF HFr.
  pose proof (paj_branch (fx := l_fx cx) (PI := PI_transport)) as BR.
  psrr_branch_tok RUNTO BR HS SHOK YC4b.Bspan.
  1:{ exfalso. cbn [sv_denot] in Hc. rewrite AGX0 in Hc by lia. rewrite (EE0 27%nat 27%bv eq_refl), C27', HK in Hc.
      vm_compute in Hc. discriminate Hc. }
  clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan 0x9ac.
  all: try (a2_awr_rs; intros a (r & Hin & Hr); cbn [In] in Hin;
    repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_wlo YP09.r_whi] in Hr; lia|]); destruct Hin).
  all: try (a2_awr_rs; apply awr_ok_x_nil).
  a2_after.
  lazymatch type of HS with context [restrict _ ?m] => rename m into ms1 end.
  lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => rename m into md1 end.
  assert (KM1 : forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W') (ms_mem ms1) a = aview segs (w_H W') (ms_mem ms0) a).
  { intros a Ha. apply (kept_of_frame _ _ _ _ _ (fun _ : Z => False) HFr); [| exact Ha | intros []].
    intros b wlo whi x Hin.
    lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
    cbn [In] in Hin. repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; lia |]). destruct Hin. }
  assert (KM : forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W') (ms_mem ms1) a = aview segs (w_H W') mem' a)
    by (intros a Ha; rewrite (KM1 a Ha); exact (KM0 a Ha)).
  assert (KP : forall a, apresent (w_H W') mem' a -> apresent (w_H W') (ms_mem ms1) a)
    by (intros a Ha; exact (a2_pres_grow _ _ _ a HG (a2_pres_grow _ _ _ a HG0 Ha))).
  lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
    assert (AGX : forall n, (n < 240)%nat -> ew Ex n = ew E0 n)
      by (intros nn Hnn; repeat rewrite ew_ewset_other by lia; first [reflexivity | apply AGX0; exact Hnn]) end.
  a2_reg HS (Z_to_bv 5 2) (YK11.getr regs' (Z_to_bv 5 2)) GK2
    ltac:(cbn [sv_denot]; (try rewrite AGX by lia); rewrite (EE0 2%nat (Z_to_bv 5 2) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  a2_reg HS (Z_to_bv 5 3) (YK11.getr regs' (Z_to_bv 5 3)) GK3
    ltac:(cbn [sv_denot]; (try rewrite AGX by lia); rewrite (EE0 3%nat (Z_to_bv 5 3) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  a2_reg HS (Z_to_bv 5 4) (YK11.getr regs' (Z_to_bv 5 4)) GK4
    ltac:(cbn [sv_denot]; (try rewrite AGX by lia); rewrite (EE0 4%nat (Z_to_bv 5 4) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  a2_reg HS (Z_to_bv 5 8) (YK11.getr regs' (Z_to_bv 5 8)) GK8
    ltac:(cbn [sv_denot]; (try rewrite AGX by lia); rewrite (EE0 8%nat (Z_to_bv 5 8) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  a2_reg HS (Z_to_bv 5 9) (YK11.getr regs' (Z_to_bv 5 9)) GK9
    ltac:(cbn [sv_denot]; (try rewrite AGX by lia); rewrite (EE0 9%nat (Z_to_bv 5 9) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  a2_reg HS (Z_to_bv 5 18) (YK11.getr regs' (Z_to_bv 5 18)) GK18
    ltac:(cbn [sv_denot]; (try rewrite AGX by lia); rewrite (EE0 18%nat (Z_to_bv 5 18) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  a2_reg HS (Z_to_bv 5 21) (YK11.getr regs' (Z_to_bv 5 21)) GK21
    ltac:(cbn [sv_denot]; (try rewrite AGX by lia); rewrite (EE0 21%nat (Z_to_bv 5 21) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  a2_reg HS (Z_to_bv 5 26) (YK11.getr regs' (Z_to_bv 5 26)) GK26
    ltac:(cbn [sv_denot]; (try rewrite AGX by lia); rewrite (EE0 26%nat (Z_to_bv 5 26) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  a2_reg HS (Z_to_bv 5 19) (w64 b1) G19 ltac:(apply a2_denot_off; [(try rewrite AGX by lia); exact (a2_ew_x regs' b1 b2 0 (lc_F cx) 0 ltac:(lia)) | lia]).
  a2_reg HS (Z_to_bv 5 24) (w64 (q + 3)) G24
    ltac:(rewrite denot_lit_U, (U_atom_off _ 25 q 3)
      by (first [(try rewrite AGX by lia); rewrite (EE0 25%nat 25%bv eq_refl); exact C25' | unfold q in *; lia]); reflexivity).
  a2_reg HS (Z_to_bv 5 10) (w64 b2) G10 ltac:(apply a2_denot_off; [(try rewrite AGX by lia); exact (a2_ew_x regs' b1 b2 0 (lc_F cx) 1 ltac:(lia)) | lia]).
  a2_reg HS (Z_to_bv 5 20) (w64 0) G20 ltac:(reflexivity).
  a2_reg HS (Z_to_bv 5 23) (w64 0) G23 ltac:(reflexivity).
  pmkst HS.
  destruct (a2_move B MT XL RLO RHI cx op false false false (lo_k op) ly' S' W' regs' mem' md' e (ms_regs ms1) (ms_mem ms1) md1 0
    LAWS HGX HB HLc HTW HJ) as [HL1 HTW1].
  { intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<- | Hr]; [assumption |]). destruct Hr. }
  { unfold LLVMF_STK. lia. }
  { intros a Ha _. exact (KM a Ha). }
  { exact KP. }
  { intros i Hi. rewrite KM; [exact (HFSH i Hi)|]. pose proof (Z.div_pos (lc_F cx) 8 ltac:(lia) ltac:(lia)).
    unfold lc_SH, SHADOW_OFF. lia. }
  pose proof (a2_vals D (TOP.FuzzIn (o0 + 1) (n0 - 1)) ltac:(cbn; lia)) as AV. cbv zeta in AV.
  cbn [TOP.fi_off TOP.fi_n] in AV.
  destruct AV as (AS & AM & AN & AC & AB).
  rewrite <- Ec1, <- Ec in AS, AM, AN, AC, AB.
  set (avv := lc_ann_vals D (lc_oc D (lo_c op))) in AS, AM, AN, AC, AB.
  a2_ifs AS. a2_ifs AM. a2_ifs AN. a2_ifs AC.
  change (Z_to_bv 64 (BASE + 0x9ac)) with (Z_to_bv 64 (BASE + if false then 0x858 else 0x9ac)).
  apply (a2_rest cx op false ly' S' W' (ms_regs ms1) (ms_mem ms1) md1 e HP HB HL1 HTW1 ltac:(rewrite Ec; symmetry; exact Ho)).
  all: cbv zeta; fold D; fold avv.
  + rewrite AS. exact G19.
  + rewrite AM, AN, AC. cbn [TOP.fi_off TOP.fi_n].
    split; [lazymatch goal with |- context [bv_unsigned (YK11.getr (ms_regs ms1) ?r)] =>
              rewrite (G10 : YK11.getr (ms_regs ms1) r = w64 b2) end; rewrite unsigned_lit_small by lia; change 15 with (Z.ones 4); rewrite Z.land_ones by lia;
            unfold b2; do 3 f_equal; lia|].
    split; [exact G20|].
    split; [refine (eq_trans G24 _); unfold w64; f_equal; cbn [TOP.fi_off]; unfold q; lia | refine (eq_trans G23 _); reflexivity].
  + rewrite AM. apply Z.mod_pos_bound. lia.
  + rewrite AB. reflexivity.

- (* n1 >= 3 *)
  pose proof (@a2_entry3 (l_fx cx) rc W' regs' mem' q (n0 - 1) b1 b2 b3 (lc_F cx) C25' C24' C23' C27' R26
    ltac:(unfold q; lia) ltac:(unfold q; lia) ltac:(lia) (V1 ltac:(lia)) (V2 ltac:(lia)) (V3 ltac:(lia)) B1 B2 B3) as HS.
  set (E0 := a2_E regs' b1 b2 b3 (lc_F cx)) in *.
  assert (HEI : img_env VAL A_LIM E0) by apply a2_env_img.
  assert (SHOK : sh_ok segs A2_Bx [] E0 (mrestrict (w_H W') mem')) by constructor.
  assert (EE0 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E0 n = YK11.getr regs' r)
    by (intros; apply a2_ew_reg; assumption).
  assert (UE24 : forall k, 0 <= k <= 8 -> U E0 (SOff 24 k) = q + 1 + k).
  { intros k Hk0. apply U_atom_off; [rewrite (EE0 24%nat 24%bv eq_refl); exact C24' | lia | lia]. }
  assert (UE25 : forall k, 0 <= k <= 8 -> U E0 (SOff 25 k) = q + k).
  { intros k Hk0. apply U_atom_off; [rewrite (EE0 25%nat 25%bv eq_refl); exact C25' | lia | lia]. }
  paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan 0x9ac.
  all: try (cbn [ms_mem]; eapply (obl_of_block segs B LAWS ly' S' W' mem' md' E0 (SOff 26 0) _ 1 (l_p cx) (l_n cx) HAR InP);
    [ apply U_atom; [rewrite (EE0 26%nat 26%bv eq_refl); exact R26 | unfold SHADOW_OFF; lia]
    | rewrite ?UE24, ?UE25 by lia; unfold q; lia | rewrite ?UE24, ?UE25 by lia; unfold q; lia ]).
  all: try (a2_awr_rs; intros a (r & Hin & Hr); cbn [In] in Hin;
    repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_wlo YP09.r_whi] in Hr; lia|]); destruct Hin).
  all: try (a2_awr_rs; apply awr_ok_x_nil).
  a2_after.
  lazymatch type of HS with context [restrict _ ?m] => rename m into ms1 end.
  lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => rename m into md1 end.
  assert (KM : forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W') (ms_mem ms1) a = aview segs (w_H W') mem' a).
  { intros a Ha. apply (kept_of_frame _ _ _ _ _ (fun _ : Z => False) HFr); [| exact Ha | intros []].
    intros b wlo whi x Hin.
    lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end.
    cbn [In] in Hin. repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; lia |]). destruct Hin. }
  lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
    assert (AGX : forall n, (n < 240)%nat -> ew Ex n = ew E0 n)
      by (intros nn Hnn; repeat rewrite ew_ewset_other by lia; reflexivity) end.
  assert (KP : forall a, apresent (w_H W') mem' a -> apresent (w_H W') (ms_mem ms1) a)
    by (intros a Ha; exact (a2_pres_grow _ _ _ a HG Ha)).
  a2_reg HS (Z_to_bv 5 2) (YK11.getr regs' (Z_to_bv 5 2)) GK2
    ltac:(cbn [sv_denot]; (try rewrite AGX by lia); rewrite (EE0 2%nat (Z_to_bv 5 2) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  a2_reg HS (Z_to_bv 5 3) (YK11.getr regs' (Z_to_bv 5 3)) GK3
    ltac:(cbn [sv_denot]; (try rewrite AGX by lia); rewrite (EE0 3%nat (Z_to_bv 5 3) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  a2_reg HS (Z_to_bv 5 4) (YK11.getr regs' (Z_to_bv 5 4)) GK4
    ltac:(cbn [sv_denot]; (try rewrite AGX by lia); rewrite (EE0 4%nat (Z_to_bv 5 4) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  a2_reg HS (Z_to_bv 5 8) (YK11.getr regs' (Z_to_bv 5 8)) GK8
    ltac:(cbn [sv_denot]; (try rewrite AGX by lia); rewrite (EE0 8%nat (Z_to_bv 5 8) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  a2_reg HS (Z_to_bv 5 9) (YK11.getr regs' (Z_to_bv 5 9)) GK9
    ltac:(cbn [sv_denot]; (try rewrite AGX by lia); rewrite (EE0 9%nat (Z_to_bv 5 9) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  a2_reg HS (Z_to_bv 5 18) (YK11.getr regs' (Z_to_bv 5 18)) GK18
    ltac:(cbn [sv_denot]; (try rewrite AGX by lia); rewrite (EE0 18%nat (Z_to_bv 5 18) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  a2_reg HS (Z_to_bv 5 21) (YK11.getr regs' (Z_to_bv 5 21)) GK21
    ltac:(cbn [sv_denot]; (try rewrite AGX by lia); rewrite (EE0 21%nat (Z_to_bv 5 21) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  a2_reg HS (Z_to_bv 5 26) (YK11.getr regs' (Z_to_bv 5 26)) GK26
    ltac:(cbn [sv_denot]; (try rewrite AGX by lia); rewrite (EE0 26%nat (Z_to_bv 5 26) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
  a2_reg HS (Z_to_bv 5 19) (w64 b1) G19 ltac:(apply a2_denot_off; [(try rewrite AGX by lia); exact (a2_ew_x regs' b1 b2 b3 (lc_F cx) 0 ltac:(lia)) | lia]).
  a2_reg HS (Z_to_bv 5 24) (w64 (q + 4)) G24
    ltac:(rewrite denot_lit_U, (U_atom_off _ 25 q 4)
      by (first [(try rewrite AGX by lia); rewrite (EE0 25%nat 25%bv eq_refl); exact C25' | unfold q in *; lia]); reflexivity).
  a2_reg HS (Z_to_bv 5 10) (w64 b2) G10 ltac:(apply a2_denot_off; [(try rewrite AGX by lia); exact (a2_ew_x regs' b1 b2 b3 (lc_F cx) 1 ltac:(lia)) | lia]).
  a2_reg HS (Z_to_bv 5 20) (w64 b3) G20 ltac:(apply a2_denot_off; [(try rewrite AGX by lia); exact (a2_ew_x regs' b1 b2 b3 (lc_F cx) 2 ltac:(lia)) | lia]).
  a2_reg HS (Z_to_bv 5 23) (w64 (n0 - 1 - 3)) G23
    ltac:(rewrite denot_lit_U, (U_atom_off _ 27 (n0 - 1 + 1) (-4)); [unfold w64; f_equal; lia | (try rewrite AGX by lia); rewrite (EE0 27%nat (Z_to_bv 5 27) eq_refl); exact C27' | lia | lia]).
  pmkst HS.
  destruct (a2_move B MT XL RLO RHI cx op false false false (lo_k op) ly' S' W' regs' mem' md' e (ms_regs ms1) (ms_mem ms1) md1 0
    LAWS HGX HB HLc HTW HJ) as [HL1 HTW1].
  { intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<- | Hr]; [assumption |]). destruct Hr. }
  { unfold LLVMF_STK. lia. }
  { intros a Ha _. exact (KM a Ha). }
  { exact KP. }
  { intros i Hi. rewrite KM; [exact (HFSH i Hi)|]. pose proof (Z.div_pos (lc_F cx) 8 ltac:(lia) ltac:(lia)).
    unfold lc_SH, SHADOW_OFF. lia. }
  pose proof (a2_vals D (TOP.FuzzIn (o0 + 1) (n0 - 1)) ltac:(cbn; lia)) as AV. cbv zeta in AV.
  cbn [TOP.fi_off TOP.fi_n] in AV.
  destruct AV as (AS & AM & AN & AC & AB).
  rewrite <- Ec1, <- Ec in AS, AM, AN, AC, AB.
  set (avv := lc_ann_vals D (lc_oc D (lo_c op))) in AS, AM, AN, AC, AB.
  a2_ifs AS. a2_ifs AM. a2_ifs AN. a2_ifs AC.
  change (Z_to_bv 64 (BASE + 0x9ac)) with (Z_to_bv 64 (BASE + if false then 0x858 else 0x9ac)).
  apply (a2_rest cx op false ly' S' W' (ms_regs ms1) (ms_mem ms1) md1 e HP HB HL1 HTW1 ltac:(rewrite Ec; symmetry; exact Ho)).
  all: cbv zeta; fold D; fold avv.
  + rewrite AS. exact G19.
  + rewrite AM, AN, AC. cbn [TOP.fi_off TOP.fi_n].
    split; [lazymatch goal with |- context [bv_unsigned (YK11.getr (ms_regs ms1) ?r)] =>
              rewrite (G10 : YK11.getr (ms_regs ms1) r = w64 b2) end; rewrite unsigned_lit_small by lia; change 15 with (Z.ones 4); rewrite Z.land_ones by lia;
            unfold b2; do 3 f_equal; lia|].
    split; [refine (eq_trans G20 _); unfold b3; do 3 f_equal; lia|].
    split; [refine (eq_trans G24 _); unfold w64; f_equal; cbn [TOP.fi_off]; unfold q; lia | refine (eq_trans G23 _); reflexivity].
  + rewrite AM. apply Z.mod_pos_bound. lia.
  + rewrite AB. reflexivity.
Qed.

End h.
