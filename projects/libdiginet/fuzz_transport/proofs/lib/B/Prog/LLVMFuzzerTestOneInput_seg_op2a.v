(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported from proofs/cgif/cgif_file_fuzzer/lib/A/AFip.v (segA: the run of a
   wrapper over its own instruction table, the application of a runtime-entry contract at a call site and the
   rebuilding of the symbolic state after the call), A/AFis.v (at_ST's frame and window conjuncts,
   kept_of_frame, chunk_val_at) and A/AF0x.v (st_ok_pin_reg, the val_mem / apresent / fpchain helpers) to
   libreac/fuzz_decode's calloc wrapper in image A (fuzz_decode.asan); module paths changed, and every address,
   cell and offset below is decode's own. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_decode/lib/A/DecodeCallocWrap.v, with its module paths and module names changed; 3365 of its 3449 lines of code are new or changed and 788 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/B/Prog/LLVMFuzzerTestOneInput_seg_cfg.v, with its module names changed; 1835 of its 1987 lines of code are new or changed and 3297 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput_seg_op2a: the segment OP2A of the image-B walk of fuzz_transport.asan-ubsan's
   LLVMFuzzerTestOneInput, `Lemma lc_op2a_ok`, the statement lc_op2a_stmt of
   lib/B/Prog/LLVMFuzzerTestOneInput_segs.v: from the first instruction of arm 2 (+0x6e8, lc_st_arm cx op 2) to
   +0xdcc (lc_st_ann cx op), op_announce (fuzz_transport.c:1052-1066) up to the copy of the MAC.

   The code (pin addresses 0x812a0 + offset; s9 = q the op byte's address, s8 = q + 1, s7 = n0, s11 = n1 = n0 - 1,
   s6 = 1, s10 = the shadow base):
     +0x6e8           `beqz s11` (no byte left after the op byte) to +0xa70 (s5 = 0);
     +0x6ec .. +0x700  the UBSan cursor test `bltu s6, s8 + 1` (trap edge 0x81994), the shadow address of s8;
     +0x700 .. +0x708  the shadow byte of s8 and `beqz` to the load, else `j` to the slow path +0x16d0 .. +0x16d8
                       (`andi`, `bge` to the report 0x82f14, `j` back);
     +0x70c .. +0x730  sel (s5), s8 = s9 + 2, `beq s7, 2` to +0xa74, the UBSan test of s8 + 1 (trap edge 0x819c4),
                       the shadow address of s8;
     +0x730 .. +0x738  the shadow byte and `beqz`, else the slow path +0x1730 .. +0x1738 (report 0x82f54);
     +0x73c .. +0x754  the mac byte (a0), s8 = s9 + 3, `bne s7, 3` to +0xd3c, else s11 = s6 = 0 and `j` +0xd78;
     +0xd3c .. +0xd74  the UBSan test of s8 + 1 (trap edge 0x81fe0), the checked load of the name byte (`bnez` to the
                       slow path +0x179c .. +0x17a4, `blt` back, else the report 0x82f90), s6 = name mod 3 by the
                       divisor constant 0x5555555555555556 at 0x10310 (TRANS_K_LLVMF), s11 = s7 - 4, s8 = s9 + 4;
     +0xd78 .. +0xda4  s7 = a0 & 15 (mac), body's shadow into scope (`sb` 12 .. 16 of s2: 0, 0, 0, 0, 2), s9 = 96(s1) =
                       body, `jal __asan_memset` (body, 0, 34), back at +0xda8;
     +0xa70 .. +0xaac  the same with no byte or one byte left: s5 = 0 (+0xa70), the shadow stores and the memset
                       (+0xa9c), back at +0xaa0: s11 = s6 = s7 = 0, `j` +0xdb0;
     +0xda8 .. +0xdc8  `bltu 9, s7` to +0xe90; the UBSan test of body + mac (`bltu` 72(s1) = ~body, s7: trap edge
                       0x82054), a0 = body + mac, a1 = HOST, a2 = 6, `jal __asan_memcpy`, back at +0xdcc (ANN);
     +0xe90 .. +0xec0  `bltu 12, s7` to +0xdcc (mac > 12: no copy); the UBSan tests of body + mac (0x8213c) and of
                       body + mac - 10 (`beq` 10: 0x82148, `bltu` 10: 0x82150), a0 = body + mac - 10, a1 = OTHER,
                       `j` +0xdc4 (the memcpy above).
   The UBSan trap word +0x1b44 is not reached: each test is decided by the engine from the facts of the run's state
   (the input block below 2 ^ 47, s6 = 1, the frame below alloc_ceiling). The reports are not reached: the checks of
   sel and mac are split at the shadow test (`beqz` to the load, `j` to the slow path: the engine's token cannot
   follow that shape), with the shadow byte s of the cursor x a read-only region of the run at its shadow address;
   the input block's shadow (YCbq.v range_addressable_of_block) gives s = 0 or x mod 8 < s < 8, which decides the
   slow path's `bge`. The name byte's check is a token of the engine (`bnez` to the `blt` slow path), whose obligation
   is the input block's addressability (YCbq.v obl_of_block).

   The proof:
   0. the model's values (lc_ann_vals by the bytes left after the op byte), the body bytes and name mod 3;
   1. b2_move: the loop facts across a step that writes only body, its shadow and the callee window (st.v
      lc_core_kept_run), with body's shadow put into scope; b2_icall: the two intrinsic calls (TransportGCg.v
      gx_intrin_at at lp_memset / lp_memcpy; the source's facts by the kit statement K2, lc_src_ro_stmt);
   2. the symbolic states of the runs (the Pa engine over the G journal, lib/B/Prog/TransportGRunB.v paj_run_x /
      paj_run_to_x) and their entry lemmas;
   3. the stretches from the end backwards (the copy, the tail, the fill, the name, the mac, sel) and lc_op2a_ok.
   The kit statements K1 (lc_rom_view_stmt: HOST, OTHER and the divisor constant read as the image) and K2
   (lc_src_ro_stmt: the memcpy source's facts) are arguments of lc_op2a_ok. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib YC1g YC1h CanKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v Img0 YCfn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k YE2y AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg TransportGRwB TransportGRunB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
  LLVMFuzzerTestOneInput_cg LLVMFuzzerTestOneInput_segs LLVMFuzzerTestOneInput_st.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require QueueFacts.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TOP := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TOps.
Module QF := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim.QueueFacts.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.
(* lia over x / 8 (the frame's shadow granules). *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* ------------------------------------------------------------------ *)
(* 0. The model's values, the body bytes and name mod 3                 *)
(* ------------------------------------------------------------------ *)

(* op_announce's reads from the cursor c1 after the op byte, by the number of bytes left (TOps.v fuzz_u8_m). *)
Lemma b2_vals : forall D c1, 0 <= TOP.fi_n c1 ->
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

Lemma b2_nth_repeat : forall {A : Type} (x d : A) m j, (j < m)%nat -> nth j (repeat x m) d = x.
Proof. intros A x d m. induction m as [|m IH]; intros j Hj; [lia|]. destruct j; [reflexivity|]. cbn. apply IH. lia. Qed.
Lemma b2_nth_skipn : forall {A : Type} (l : list A) (d : A) m j, nth j (skipn m l) d = nth (m + j) l d.
Proof.
intros A l d m. revert l. induction m as [|m IH]; intros l j; [reflexivity|].
destruct l as [|x l]; [cbn; destruct j; reflexivity|]. cbn. apply IH.
Qed.
Lemma b2_nth_firstn : forall {A : Type} (l : list A) (d : A) m j, (j < m)%nat -> nth j (firstn m l) d = nth j l d.
Proof.
intros A l d m. revert l. induction m as [|m IH]; intros l j Hj; [lia|].
destruct l as [|x l]; [cbn; destruct j; reflexivity|]. destruct j; [reflexivity|]. cbn. apply IH. lia.
Qed.

(* The 34 bytes of body after the zero fill and the copy of src (6 bytes) at offset k. *)
Lemma b2_upd_nth : forall (src : list byte) k j, length src = 6%nat -> 0 <= k -> k + 6 <= 34 -> (j < 34)%nat ->
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
  rewrite b2_nth_skipn. rewrite b2_nth_repeat by lia. reflexivity.
- rewrite app_nth1 by lia. rewrite b2_nth_firstn by lia. rewrite b2_nth_repeat by lia. reflexivity.
- lia.
Qed.

(* s6 at +0xd78 as the engine leaves it from the name byte (atom 34): name - 3 * ((name * K) >> 64) with
   K = 0x5555555555555556, the divisor constant at TRANS_K_LLVMF (+0xd5c .. +0xd74). *)
Definition B2_K3 : Z := 6148914691236517206.
Definition b2_eM : sv :=
  SAlu ALU_SUB (SAlu ALU_SUB (SOff 34 0) (SMd M_MULHU (SOff 34 0) (SLit B2_K3)))
    (SAlu ALU_SLL (SMd M_MULHU (SOff 34 0) (SLit B2_K3)) (SLit 1)).
(* A closed valuation with atom n = v. *)
Definition b2_envz (n : nat) (v : Z) : env :=
  mkEnv (fun i => if Nat.eqb i n then Z_to_bv 64 v else Z_to_bv 64 0) (fun _ => []).
Lemma b2_eM_dec : forallb (fun i : nat =>
  Z.eqb (bv_unsigned (sv_denot (b2_envz 34 (Z.of_nat i)) b2_eM)) (Z.of_nat i mod 3)) (seq 0 256) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma b2_fin : forall (f : nat -> bool) z, forallb f (seq 0 256) = true -> 0 <= z < 256 -> f (Z.to_nat z) = true.
Proof. intros f z H Hz. rewrite forallb_forall in H. apply H. apply in_seq. lia. Qed.
Lemma b2_eM_val : forall E nm, ew E 34 = Z_to_bv 64 nm -> 0 <= nm < 256 -> sv_denot E b2_eM = Z_to_bv 64 (nm mod 3).
Proof.
intros E nm H34 Hnm.
assert (EQ : sv_denot E b2_eM = sv_denot (b2_envz 34 nm) b2_eM).
{ unfold b2_eM. cbn [sv_denot]. cbn [ew b2_envz Nat.eqb]. rewrite H34. reflexivity. }
rewrite EQ. pose proof (b2_fin _ nm b2_eM_dec Hnm) as D. cbv beta in D. rewrite Z2Nat.id in D by lia.
apply Z.eqb_eq in D. apply bv_eq. rewrite D. symmetry. apply unsigned_lit_small.
pose proof (Z.mod_pos_bound nm 3 ltac:(lia)). lia.
Qed.

Ltac b2_in := repeat (first [left; reflexivity | right]).

(* ------------------------------------------------------------------ *)
(* 1. The loop facts across a step that writes body and its shadow      *)
(* ------------------------------------------------------------------ *)

Section op2a. Context {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
Local Abbreviation segs := tfibsegs.
Local Abbreviation av W m := (aview tfibsegs (w_H W) m).

(* The walk's journal, as lc_core states it. *)
Definition b2_J (cx : lcx) (ly2 : alayout) (S2 : astate) (W2 : world segs) (mem2 : word -> option byte) (md2 : Model)
    (e2 : Z) : Prop :=
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] LLVMF_STK (lc_sp0 cx) []
    (l_ly cx) (l_S cx) (l_W cx) (l_mem cx) (l_md cx) [(LF_CID, l_fpos cx)] ly2 S2 W2 mem2 md2 e2.

(* The bytes a step of this segment may change: the callee stack window [sp1 - X, sp1), body [F + 96, F + 130) and
   body's five shadow bytes [SH + 12, SH + 17). *)
Definition b2_out (cx : lcx) (X a : Z) : Prop :=
  (lc_sp1 cx - X <= a < lc_sp1 cx) \/ (lc_F cx + 96 <= a < lc_F cx + 130) \/ (lc_SH cx + 12 <= a < lc_SH cx + 17).

(* The loop facts and the world relation across such a step, at the same allocator state, events and W: the frame's
   shadow is given by the caller (bin' says whether body's is in scope). *)
Lemma b2_move : forall cx op cin bin bin' k ly S (W : world segs) regs mem md e regs2 mem2 md2 X,
  AR_laws segs B -> gx_ok segs B TG.G_HARNESS_B -> @lc_base rc B MT XL RLO RHI cx ->
  @lc_lcore rc B MT cx op cin bin k ly S W regs mem md e -> lc_tw W mem (lo_B op) ->
  b2_J cx ly S W mem2 md2 e ->
  (forall r, In r [2; 3; 4; 8; 9; 18; 19; 26] -> YK11.getr regs2 (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)) ->
  0 <= X <= LLVMF_STK - 336 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ b2_out cx X a -> av W mem2 a = av W mem a) ->
  (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem2 a) ->
  lc_fsh cx (av W mem2) cin bin' ->
  @lc_lcore rc B MT cx op cin bin' k ly S W regs2 mem2 md2 e /\ lc_tw W mem2 (lo_B op).
Proof.
intros cx op cin bin bin' k ly S W regs mem md e regs2 mem2 md2 X LAWS HGX HB HL HTW HJ2 HR HX K Hgr HSH2.
destruct HL as (HC & (F18 & F26) & HSP & HSH & HOK & Hev & HM & R19).
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
unfold LLVMF_STK in HX. unfold LF_FRAME in Hsp1.
(* the bytes from alloc_ceiling up: off body (below the ceiling) and off its shadow (below the ceiling) *)
assert (KA : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (lc_sp1 cx - X <= a < lc_sp1 cx) -> av W mem2 a = av W mem a).
{ intros a Ha Hw. apply K; [lia|]. unfold b2_out, LF_FBYTES in HFceil |- *.
  intros [H1 | [H1 | H1]]; [exact (Hw H1) | clear - H1 Ha HFceil; lia | clear - H1 Ha HSHr; lia]. }
(* the input: a block, below the ceiling, off the frame, in application memory *)
assert (KIN : forall i, 0 <= i < l_n cx -> av W mem2 (l_p cx + i) = av W mem (l_p cx + i)).
{ intros i Hi. pose proof (HINg ltac:(lia)) as InP.
  destruct (al_blocks _ _ LAWS ly S W mem md (l_p cx) (l_n cx) HARg InP) as (_ & Hb4 & Hbc & Hbapp & _).
  pose proof (sep_block_frame segs B LAWS ly S W mem md _ _ _ _ HARg InP HFin) as Hd.
  rewrite HFaddr in Hd. change (fs_frame_bytes LF_CID) with 256 in Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd.
  pose proof (req_size_pos (l_n cx) ltac:(lia)) as (Hq1 & Hq2).
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hbapp.
  apply K; [lia|]. unfold b2_out. unfold SHADOW_OFF, LF_FRAME in *. lia. }
split.
- split.
  { apply (lc_core_kept_run B MT XL RLO RHI cx ly S W regs mem md e ly S W regs2 mem2 md2 e HB HC HJ2 eq_refl
      (Permutation_refl _)).
    + intros r Hr. apply HR. cbn [In] in Hr |- *. tauto.
    + intros a Ha. apply KA; [lia | lia].
    + exact KIN.
    + intros a Ha. unfold SHADOW_OFF, LF_FBYTES in *.
      apply K; [lia | unfold b2_out; lia].
    + intros a Ha _. apply Hgr. exact (HFpres a Ha). }
  split; [split; [exact (eq_trans (HR 18 ltac:(cbn; tauto)) F18) | exact (eq_trans (HR 26 ltac:(cbn; tauto)) F26)]|].
  split.
  { apply (lc_spills_kept cx (lf_spill_loop (lc_F cx)) (av W mem) (av W mem2));
      [|intros a Ha; apply KA; lia|exact HSP].
    intros o Ho.
    pose proof (lf_spill_vals (lc_F cx) ltac:(lia) ltac:(unfold LF_FBYTES in *; lia)) as HV.
    rewrite Forall_forall in HV. destruct (HV o Ho) as (_ & _ & H8 & H192). lia. }
  split; [exact HSH2|]. split; [exact HOK|]. split; [exact Hev|]. split; [exact HM|].
  exact (eq_trans (HR 19 ltac:(cbn; tauto)) R19).
- apply (tw_kept_GB (av W mem) (av W mem2) (lo_B op) HTW).
  intros b n i Hin Hi.
  pose proof (TG.G_HARNESS_B_in_hull (b, n) Hin) as Hh. unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh. cbn in Hh.
  apply K; [lia|].
  unfold b2_out. intros [Hw | [Hb | Hs]].
  + lia.
  + (* body is a frame byte, not an image byte; every byte of G is *)
    assert (HinG : inG TG.G_HARNESS_B (b + i))
      by (unfold inG; apply Exists_exists; exists (b, n); split; [exact Hin | unfold in_zr; cbn; lia]).
    destruct (HGX _ HinG) as [Himg _].
    apply (frm_img segs B LAWS ly S W mem md LF_CID (l_fpos cx) (b + i) HARg HFin); [|exact Himg].
    rewrite HFaddr. change (fs_frame_bytes LF_CID) with 256. lia.
  + unfold SHADOW_OFF in *. lia.
Qed.

(* body's five shadow bytes after the stores of +0xd7c .. +0xd90 (or +0xa74 ..): 0, 0, 0, 0, 2. *)
Definition B2_BSH : list Z := [0; 0; 0; 0; 2].

Lemma b2_body_hull : forall cx (r : reader) d n,
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
Definition b2_ipc (o : memop) : Z :=
  match o with OCpy => transportb_sigma TB___asan_memcpy | OSet => transportb_sigma TB___asan_memset end.

(* HOST and OTHER are TRANS_RO_RD bytes. *)
Lemma b2_src_ro : forall x a, (x = TRANS_HOST \/ x = TRANS_OTHER) -> x <= a < x + 6 -> trans_in_ro_rd a.
Proof.
intros x a Hx Ha. unfold trans_in_ro_rd. apply Exists_exists.
destruct Hx as [-> | ->]; [exists (TRANS_HOST, 6) | exists (TRANS_OTHER, 6)];
  (split; [unfold TRANS_RO_RD, TRANS_RO_GLOBALS; cbn [app]; b2_in | unfold in_zr; cbn [fst snd]; lia]).
Qed.

(* A call of memset or memcpy whose destination is in body, with body's shadow in scope: the loop facts and the world
   relation hold after it, at the same allocator state and events. *)
Lemma b2_icall (K2 : lc_src_ro_stmt B MT XL RLO RHI) :
  forall cx op k (o : memop) ly S (W : world segs) regsT memT mdT e d x n raw,
  @lp_prem rc B MT XL RLO RHI -> @lc_base rc B MT XL RLO RHI cx ->
  @lc_lcore rc B MT cx op false true k ly S W regsT memT mdT e -> lc_tw W memT (lo_B op) ->
  YK11.getr regsT 10 = w64 d -> YK11.getr regsT 11 = w64 x -> YK11.getr regsT 12 = w64 n ->
  YK11.getr regsT 1 = raw -> YK0s.ret_ok raw ->
  lc_F cx + 96 <= d -> d + n <= lc_F cx + 130 -> 0 < n ->
  (match o with OCpy => (x = TRANS_HOST \/ x = TRANS_OTHER) /\ n = 6 | OSet => True end) ->
  SRr segs W (mkCfg (@YK11.mkst (l_fx cx) regsT (Z_to_bv 64 (b2_ipc o)) memT (YK11.seg_rom segs)) mdT)
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
pose proof HL as (HC & HFR & HSP & HFSH & HOK & He & HMT & R19).
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
{ eapply (gx_intrin_at (fx := l_fx cx) (SK := YE2k.tfib_sink_head) segs B LAWS transportb_segs_low o (b2_ipc o)
    ltac:(destruct o; [exact (lp_memcpy _ _ _ _ _ HP (l_fx cx)) | exact (lp_memset _ _ _ _ _ HP (l_fx cx))])
    TG.G_HARNESS_B W regsT memT LLVMF_STK (lc_sp0 cx) [] (l_ly cx) (l_S cx) (l_W cx) (l_mem cx) (l_md cx)
    [(LF_CID, l_fpos cx)] ly S mdT e d x n (lc_sp1 cx - lc_sp0 cx) raw HGX G_HARNESS_B_rw HJ R10 R11 R12).
  - lia.
  - lia.
  - lia.
  - unfold LLVMF_STK. lia.
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
  - intros _. apply (b2_body_hull cx _ d n HFal ltac:(lia) Hd Hdn Hn HVIS).
  - destruct o; [|exact I].
    destruct Ho as (Hx & ->).
    pose proof (K2 HP cx ly S W regsT memT mdT e x 6 HB HC
      ltac:(destruct Hx as [-> | ->]; cbn [In]; b2_in)) as HSRC.
    assert (Hximg : forall a, x <= a < x + 6 -> in_img segs a)
      by (intros a Ha; exact (trans_ro_img a (b2_src_ro x a Hx Ha))).
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
      pose proof (transportb_segs_low a (Hximg a Ha)) as Hl. unfold kLowMemEnd in Hl. lia. }
    split.
    { destruct (Z_le_gt_dec (d + 6) x) as [H1 | H1]; [left; exact H1|].
      destruct (Z_le_gt_dec (x + 6) d) as [H2 | H2]; [right; exact H2|].
      exfalso. destruct (Z_le_gt_dec d x) as [H3 | H3].
      - exact (Hdimg x ltac:(lia) (Hximg x ltac:(lia))).
      - exact (Hdimg d ltac:(lia) (Hximg d ltac:(lia))). }
    split; [exact HAM|]. split; [exact HRAx|]. intros _. exact HHV. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HPR & R10' & HBY & HK & HPG).
split; [reflexivity|]. exists regs2, mem2, md2. split; [reflexivity|].
assert (KO : forall a, 0 <= a < 2 ^ 64 -> ~ b2_out cx 4096 a -> av W mem2 a = av W memT a).
{ intros a Ha Hout. apply HK; [exact Ha | | ].
  - intros Ha'. apply Hout. right. left. lia.
  - replace (lc_sp0 cx + (lc_sp1 cx - lc_sp0 cx) - ESTACK) with (lc_sp1 cx - 4096) by (unfold ESTACK; lia).
    replace (lc_sp0 cx + (lc_sp1 cx - lc_sp0 cx)) with (lc_sp1 cx) by lia.
    intros Hw. apply Hout. left. exact Hw. }
destruct (b2_move cx op false true true k ly S W regsT memT mdT e regs2 mem2 md2 4096 LAWS HGX HB HL HTW HJ2)
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
(* 2. The symbolic states of the runs                                   *)
(* ------------------------------------------------------------------ *)

(* The top of the pointer facts (YC4b.PTR): every block, frame and spill address is at most this. *)
Definition B2_PHI : Z := 140737479966720.

(* Atoms 0 .. 31: the registers at the run's start; 32 .. 36: the seat's extra values. *)
(* ARM, +0x6e8: s6 = 1 (atom 22), s8 = q + 1 (atom 24), s10 the shadow base, s11 = n1 (atom 27) in [lo, hi]. *)
Definition b2_ssA (lo hi : Z) : sstate :=
  mkSS 0x6e8 sr_atoms [] None
    (mkFacts [(22%nat, mkAF 1 1 0); (24%nat, YC4b.PTR 0); (26%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
              (27%nat, mkAF lo hi 0)] [] []).
(* SH1, +0x700: a0 (atom 10) the shadow address of s8 = q + 1 (atom 24), its shadow byte atom 32 and sel atom 33;
   s7 = n0 (atom 23) in [lo, hi], s9 = q (atom 25). *)
Definition b2_rgS1 : YP09.region := YP09.mkRegion (Some 10%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))].
Definition b2_rgB1 : YP09.region := YP09.mkRegion (Some 24%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 33 0))].
Definition b2_ssS1 (lo hi : Z) : sstate :=
  mkSS 0x700 sr_atoms [b2_rgS1; b2_rgB1] None
    (mkFacts [(10%nat, mkAF SHADOW_OFF (2 ^ 46) 0); (22%nat, mkAF 1 1 0); (23%nat, mkAF lo hi 0);
              (24%nat, YC4b.PTR 0); (25%nat, YC4b.PTR 0); (26%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
              (32%nat, mkAF 0 7 0); (33%nat, mkAF 0 255 0)] [] []).
(* SH2, +0x730: a1 (atom 11) the shadow address of s8 = q + 2, its shadow byte atom 32. *)
Definition b2_rgS2 : YP09.region := YP09.mkRegion (Some 11%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))].
Definition b2_ssS2 : sstate :=
  mkSS 0x730 sr_atoms [b2_rgS2] None (mkFacts [(11%nat, mkAF SHADOW_OFF (2 ^ 46) 0); (32%nat, mkAF 0 7 0)] [] []).
(* J2, +0x73c: s8 = q + 2 (atom 24) holds mac (atom 33); with four bytes or more left, s9 + 3 holds the name byte
   (atom 34) and object 15 (TRANS_K_LLVMF) the divisor constant. *)
Definition b2_rgB2 : YP09.region := YP09.mkRegion (Some 24%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 33 0))].
Definition b2_rgB3 : YP09.region := YP09.mkRegion (Some 25%nat) 3 4 0 0 [YP09.mkChunk 3 (CVal 1 (SOff 34 0))].
Definition b2_rgK : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 15)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SLit B2_K3))].
Definition b2_ssJ (three : bool) : sstate :=
  mkSS 0x73c sr_atoms (if three then [b2_rgB2] else [b2_rgB2; b2_rgB3; b2_rgK]) None
    (mkFacts [(22%nat, mkAF 1 1 0); (23%nat, if three then mkAF 3 3 0 else mkAF 4 (2 ^ 26) 0);
              (24%nat, YC4b.PTR 0); (25%nat, YC4b.PTR 0); (26%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
              (33%nat, mkAF 0 255 0); (34%nat, mkAF 0 255 0)] [] []).
Definition B2_Bx : sv := SOff 26 0.
(* SB, +0xa74 / +0xd78: s2 (atom 18) = SH, body's five shadow bytes writable; 96(s1) = body (atom 35). *)
Definition b2_rgSH : YP09.region := YP09.mkRegion (Some 18%nat) 12 17 12 17 [].
Definition b2_rgSP : YP09.region := YP09.mkRegion (Some 9%nat) 96 104 0 0 [YP09.mkChunk 96 (CVal 8 (SOff 35 0))].
Definition b2_ssB (pc : Z) : sstate :=
  mkSS pc sr_atoms [b2_rgSH; b2_rgSP] None (mkFacts [(18%nat, mkAF SHADOW_OFF (2 ^ 46) 0)] [] []).
(* T, +0xaa0 / +0xda8: s7 = mac (atom 23) in [lo, hi], s9 = body (atom 25), 72(s1) = ~body (atom 36). *)
Definition b2_rgT : YP09.region := YP09.mkRegion (Some 9%nat) 72 80 0 0 [YP09.mkChunk 72 (CVal 8 (SOff 36 0))].
Definition b2_ssT (pc lo hi : Z) : sstate :=
  mkSS pc sr_atoms [b2_rgT] None
    (mkFacts [(23%nat, mkAF lo hi 0); (25%nat, mkAF 4192 B2_PHI 0);
              (36%nat, mkAF (2 ^ 64 - 1 - B2_PHI) (2 ^ 64 - 1 - 4192) 0)] [] []).

Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

Definition b2_E (regs : bvmap 5 word) (v32 v33 v34 v35 v36 : Z) : env :=
  Eimg (PI := PI_transportb) (Ereg regs [w64 v32; w64 v33; w64 v34; w64 v35; w64 v36]).

Lemma b2_env_img : forall regs a b c d f, img_env VAL A_LIM (b2_E regs a b c d f).
Proof. intros. unfold b2_E. apply Eimg_env. Qed.
Lemma b2_ew_reg : forall regs a b c d f n (r : bv 5), Z.of_nat n = bv_unsigned r ->
  ew (b2_E regs a b c d f) n = YK11.getr regs r.
Proof. intros. unfold b2_E. apply can_ew_Eimg_Ereg_nat. assumption. Qed.
Lemma b2_ew_x : forall regs a b c d f j, (j < 5)%nat ->
  ew (b2_E regs a b c d f) (32 + j) = nth j [w64 a; w64 b; w64 c; w64 d; w64 f] (Z_to_bv 64 0).
Proof. intros. unfold b2_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. Qed.

Lemma b2_entryA : forall (W : world segs) regs mem x n1 lo hi,
  YK11.getr regs 22 = w64 1 -> YK11.getr regs 24 = w64 x -> YK11.getr regs 26 = w64 SHADOW_OFF ->
  YK11.getr regs 27 = w64 n1 -> 4096 <= x <= B2_PHI -> 0 <= lo <= n1 -> n1 <= hi < 2 ^ 64 ->
  st_ok_pi segs VAL (b2_E regs 0 0 0 0 0) (b2_ssA lo hi)
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + 0x6e8)) mem (YK11.seg_rom segs))).
Proof.
intros W regs mem x n1 lo hi R22 R24 R26 R27 Hx Hlo Hhi.
set (E := b2_E regs 0 0 0 0 0).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs r)
  by (intros; apply b2_ew_reg; assumption).
unfold B2_PHI in Hx.
assert (U22 : bv_unsigned (ew E 22) = 1) by (rewrite (EE 22%nat 22%bv eq_refl), R22; apply unsigned_lit_small; lia).
assert (U24 : bv_unsigned (ew E 24) = x) by (rewrite (EE 24%nat 24%bv eq_refl), R24; apply unsigned_lit_small; lia).
assert (U26 : bv_unsigned (ew E 26) = SHADOW_OFF)
  by (rewrite (EE 26%nat 26%bv eq_refl), R26; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U27 : bv_unsigned (ew E 27) = n1) by (rewrite (EE 27%nat 27%bv eq_refl), R27; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. unfold b2_ssA.
apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. exact I.
- unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok, YC4b.PTR. cbn [af_lo af_hi af_al2].
  rewrite U22, U24, U26, U27, !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; try exact I; unfold SHADOW_OFF in *; lia.
Qed.

Lemma b2_entryS1 : forall (W : world segs) regs mem q n0 lo hi sb b1,
  YK11.getr regs 10 = w64 (SHADOW_OFF + (q + 1) / 8) -> YK11.getr regs 22 = w64 1 -> YK11.getr regs 23 = w64 n0 ->
  YK11.getr regs 24 = w64 (q + 1) -> YK11.getr regs 25 = w64 q -> YK11.getr regs 26 = w64 SHADOW_OFF ->
  4096 <= q -> q + 1 <= B2_PHI -> 0 <= lo <= n0 -> n0 <= hi < 2 ^ 64 ->
  (q + 2 <= SHADOW_OFF + (q + 1) / 8 \/ SHADOW_OFF + (q + 1) / 8 + 1 <= q + 1) ->
  val_mem segs (mrestrict (w_H W) mem) (SHADOW_OFF + (q + 1) / 8) 1 sb ->
  val_mem segs (mrestrict (w_H W) mem) (q + 1) 1 b1 -> 0 <= sb <= 7 -> 0 <= b1 < 256 ->
  st_ok_pi segs VAL (b2_E regs sb b1 0 0 0) (b2_ssS1 lo hi)
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + 0x700)) mem (YK11.seg_rom segs))).
Proof.
intros W regs mem q n0 lo hi sb b1 R10 R22 R23 R24 R25 R26 Hq Hq1 Hlo Hhi Hdj VS V1 Hsb Hb1.
set (E := b2_E regs sb b1 0 0 0).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs r)
  by (intros; apply b2_ew_reg; assumption).
pose proof (b2_ew_x regs sb b1 0 0 0 0 ltac:(lia)) as E32. pose proof (b2_ew_x regs sb b1 0 0 0 1 ltac:(lia)) as E33.
cbn [Nat.add nth] in E32, E33. fold E in E32, E33.
unfold B2_PHI in Hq1.
assert (HS8 : 0 <= (q + 1) / 8 <= 17592185995776) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
assert (U10 : bv_unsigned (ew E 10) = SHADOW_OFF + (q + 1) / 8)
  by (rewrite (EE 10%nat 10%bv eq_refl), R10; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U22 : bv_unsigned (ew E 22) = 1) by (rewrite (EE 22%nat 22%bv eq_refl), R22; apply unsigned_lit_small; lia).
assert (U23 : bv_unsigned (ew E 23) = n0) by (rewrite (EE 23%nat 23%bv eq_refl), R23; apply unsigned_lit_small; lia).
assert (U24 : bv_unsigned (ew E 24) = q + 1) by (rewrite (EE 24%nat 24%bv eq_refl), R24; apply unsigned_lit_small; lia).
assert (U25 : bv_unsigned (ew E 25) = q) by (rewrite (EE 25%nat 25%bv eq_refl), R25; apply unsigned_lit_small; lia).
assert (U26 : bv_unsigned (ew E 26) = SHADOW_OFF)
  by (rewrite (EE 26%nat 26%bv eq_refl), R26; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U32 : bv_unsigned (ew E 32) = sb) by (rewrite E32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = b1) by (rewrite E33; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. unfold b2_ssS1.
apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold b2_rgS1, b2_rgB1.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
    rewrite ?U10, ?U24.
  + split; [unfold SHADOW_OFF; lia|]. split; [unfold SHADOW_OFF; lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val segs E _ (SHADOW_OFF + (q + 1) / 8) 0 1 (SOff 32 0) sb);
      [rewrite denot_lit_U, (U_atom E 32 sb E32 ltac:(lia)); reflexivity | cbn; lia | cbn; lia |].
    rewrite Z.add_0_r. exact VS.
  + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val segs E _ (q + 1) 0 1 (SOff 33 0) b1);
      [rewrite denot_lit_U, (U_atom E 33 b1 E33 ltac:(lia)); reflexivity | cbn; lia | cbn; lia |].
    rewrite Z.add_0_r. exact V1.
- apply pairwise_disjoint_of_extents.
  unfold b2_rgS1, b2_rgB1, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val zpairwise_disjoint zall_disjoint].
  rewrite U10, U24. unfold zdisj. cbn [fst snd]. repeat split; first [exact I | lia].
- unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok, YC4b.PTR. cbn [af_lo af_hi af_al2].
  rewrite U10, U22, U23, U24, U25, U26, U32, U33, !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; try exact I; unfold SHADOW_OFF in *; lia.
Qed.

Lemma b2_entryS2 : forall (W : world segs) regs mem x sb,
  YK11.getr regs 11 = w64 (SHADOW_OFF + x / 8) -> 0 <= x <= B2_PHI ->
  val_mem segs (mrestrict (w_H W) mem) (SHADOW_OFF + x / 8) 1 sb -> 0 <= sb <= 7 ->
  st_ok_pi segs VAL (b2_E regs sb 0 0 0 0) b2_ssS2
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + 0x730)) mem (YK11.seg_rom segs))).
Proof.
intros W regs mem x sb R11 Hx VS Hsb.
set (E := b2_E regs sb 0 0 0 0).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs r)
  by (intros; apply b2_ew_reg; assumption).
pose proof (b2_ew_x regs sb 0 0 0 0 0 ltac:(lia)) as E32. cbn [Nat.add nth] in E32. fold E in E32.
unfold B2_PHI in Hx.
assert (HS8 : 0 <= x / 8 <= 17592185995776) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
assert (U11 : bv_unsigned (ew E 11) = SHADOW_OFF + x / 8)
  by (rewrite (EE 11%nat 11%bv eq_refl), R11; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U32 : bv_unsigned (ew E 32) = sb) by (rewrite E32; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. unfold b2_ssS2.
apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold b2_rgS2. apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U11.
  split; [unfold SHADOW_OFF; lia|]. split; [unfold SHADOW_OFF; lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val segs E _ (SHADOW_OFF + x / 8) 0 1 (SOff 32 0) sb);
    [rewrite denot_lit_U, (U_atom E 32 sb E32 ltac:(lia)); reflexivity | cbn; lia | cbn; lia |].
  rewrite Z.add_0_r. exact VS.
- apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. exact (conj I I).
- unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U11, U32, !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; try exact I; unfold SHADOW_OFF in *; lia.
Qed.

Lemma b2_valK : VAL (A_OBJ 15) = TRANS_K_LLVMF.
Proof. vm_compute. reflexivity. Qed.

Lemma b2_entryJ : forall (W : world segs) regs mem q n0 b2 b3 (three : bool),
  YK11.getr regs 22 = w64 1 -> YK11.getr regs 23 = w64 n0 -> YK11.getr regs 24 = w64 (q + 2) ->
  YK11.getr regs 25 = w64 q -> YK11.getr regs 26 = w64 SHADOW_OFF ->
  4096 <= q -> q + 3 <= B2_PHI -> (if three then n0 = 3 else 4 <= n0 <= 2 ^ 26) ->
  val_mem segs (mrestrict (w_H W) mem) (q + 2) 1 b2 ->
  (three = false -> val_mem segs (mrestrict (w_H W) mem) (q + 3) 1 b3) ->
  (three = false -> val_mem segs (mrestrict (w_H W) mem) TRANS_K_LLVMF 8 B2_K3) ->
  (three = false -> q + 4 <= TRANS_K_LLVMF \/ TRANS_K_LLVMF + 8 <= q + 2) ->
  0 <= b2 < 256 -> 0 <= b3 < 256 ->
  st_ok_pi segs VAL (b2_E regs 0 b2 b3 0 0) (b2_ssJ three)
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + 0x73c)) mem (YK11.seg_rom segs))).
Proof.
intros W regs mem q n0 b2 b3 three R22 R23 R24 R25 R26 Hq Hq3 Hn0 V2 V3 VK Hdk Hb2 Hb3.
set (E := b2_E regs 0 b2 b3 0 0).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs r)
  by (intros; apply b2_ew_reg; assumption).
pose proof (b2_ew_x regs 0 b2 b3 0 0 1 ltac:(lia)) as E33. pose proof (b2_ew_x regs 0 b2 b3 0 0 2 ltac:(lia)) as E34.
cbn [Nat.add nth] in E33, E34. fold E in E33, E34.
unfold B2_PHI in Hq3.
assert (Hn0' : 3 <= n0 <= 2 ^ 26) by (destruct three; lia).
assert (U22 : bv_unsigned (ew E 22) = 1) by (rewrite (EE 22%nat 22%bv eq_refl), R22; apply unsigned_lit_small; lia).
assert (U23 : bv_unsigned (ew E 23) = n0) by (rewrite (EE 23%nat 23%bv eq_refl), R23; apply unsigned_lit_small; lia).
assert (U24 : bv_unsigned (ew E 24) = q + 2) by (rewrite (EE 24%nat 24%bv eq_refl), R24; apply unsigned_lit_small; lia).
assert (U25 : bv_unsigned (ew E 25) = q) by (rewrite (EE 25%nat 25%bv eq_refl), R25; apply unsigned_lit_small; lia).
assert (U26 : bv_unsigned (ew E 26) = SHADOW_OFF)
  by (rewrite (EE 26%nat 26%bv eq_refl), R26; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U33 : bv_unsigned (ew E 33) = b2) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = b3) by (rewrite E34; apply unsigned_lit_small; lia).
assert (UK : bv_unsigned (ew E (A_OBJ 15)) = TRANS_K_LLVMF).
{ unfold E, b2_E. rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia).
  rewrite b2_valK. apply unsigned_lit_small. unfold TRANS_K_LLVMF. lia. }
assert (C2 : YP09.chunk_ok segs E (mrestrict (w_H W) mem) (q + 2) (YP09.mkChunk 0 (CVal 1 (SOff 33 0)))).
{ apply (chunk_ok_val segs E _ (q + 2) 0 1 (SOff 33 0) b2);
    [rewrite denot_lit_U, (U_atom E 33 b2 E33 ltac:(lia)); reflexivity | cbn; lia | cbn; lia |].
  rewrite Z.add_0_r. exact V2. }
assert (FOK : facts_ok E (ss_facts (b2_ssJ three))).
{ unfold b2_ssJ, facts_ok. cbn [ss_facts f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok, YC4b.PTR. cbn [af_lo af_hi af_al2].
  rewrite U22, U23, U24, U25, U26, U33, U34, !Z.pow_0_r, !Z.mod_1_r.
  destruct three; cbn [af_lo af_hi af_al2]; rewrite ?Z.pow_0_r, ?Z.mod_1_r;
    repeat match goal with |- _ /\ _ => split end; try exact I; unfold SHADOW_OFF in *; lia. }
rewrite restrict_mkst_fx.
destruct three.
- unfold b2_ssJ in FOK |- *. cbn [ss_facts] in FOK.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold b2_rgB2. apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U24.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [exact C2 | apply Forall_nil].
  + apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. exact (conj I I).
  + exact FOK.
- unfold b2_ssJ in FOK |- *. cbn [ss_facts] in FOK.
  specialize (V3 eq_refl). specialize (VK eq_refl). specialize (Hdk eq_refl).
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold b2_rgB2, b2_rgB3, b2_rgK.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
      rewrite ?U24, ?U25, ?UK.
    * split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [exact C2 | apply Forall_nil].
    * split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val segs E _ q 3 1 (SOff 34 0) b3);
        [rewrite denot_lit_U, (U_atom E 34 b3 E34 ltac:(lia)); reflexivity | cbn; lia | cbn; lia | exact V3].
    * split; [unfold TRANS_K_LLVMF; lia|]. split; [unfold TRANS_K_LLVMF; lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val segs E _ TRANS_K_LLVMF 0 8 (SLit B2_K3) B2_K3);
        [reflexivity | change (8 * Z.of_N 8) with 64; unfold B2_K3; lia | cbn; lia |].
      rewrite Z.add_0_r. exact VK.
  + apply pairwise_disjoint_of_extents.
    unfold b2_rgB2, b2_rgB3, b2_rgK, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val zpairwise_disjoint zall_disjoint].
    rewrite U24, U25, UK. unfold zdisj. cbn [fst snd].
    repeat split; first [exact I | lia].
  + exact FOK.
Qed.

Lemma b2_entryB : forall (W : world segs) regs mem pc F sp1 SH,
  YK11.getr regs 18 = w64 SH -> YK11.getr regs 9 = w64 sp1 ->
  SHADOW_OFF <= SH -> SH + 32 <= 17594333495296 -> YM05.alloc_ceiling <= sp1 -> sp1 + 104 <= 2 ^ 63 ->
  val_mem segs (mrestrict (w_H W) mem) (sp1 + 96) 8 (F + 96) -> 0 <= F + 96 < 2 ^ 64 ->
  (forall a, SH + 12 <= a < SH + 17 -> apresent (w_H W) mem a) ->
  st_ok_pi segs VAL (b2_E regs 0 0 0 (F + 96) 0) (b2_ssB pc)
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + pc)) mem (YK11.seg_rom segs))).
Proof.
intros W regs mem pc F sp1 SH R18 R9 HSH0 HSH1 Hs0 Hs1 VS96 HF Hpres.
set (E := b2_E regs 0 0 0 (F + 96) 0).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs r)
  by (intros; apply b2_ew_reg; assumption).
pose proof (b2_ew_x regs 0 0 0 (F + 96) 0 3 ltac:(lia)) as E35. cbn [Nat.add nth] in E35. fold E in E35.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (U18 : bv_unsigned (ew E 18) = SH)
  by (rewrite (EE 18%nat 18%bv eq_refl), R18; apply unsigned_lit_small; unfold SHADOW_OFF in *; lia).
assert (U9 : bv_unsigned (ew E 9) = sp1) by (rewrite (EE 9%nat 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. unfold b2_ssB.
apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold b2_rgSH, b2_rgSP.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
    rewrite ?U18, ?U9.
  + split; [unfold SHADOW_OFF in *; lia|]. split; [lia|]. split; [|apply Forall_nil].
    intros o Ho. apply (apresent_writable segs). apply Hpres. lia.
  + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val segs E _ sp1 96 8 (SOff 35 0) (F + 96));
      [rewrite denot_lit_U, (U_atom E 35 (F + 96) E35 ltac:(lia)); reflexivity | cbn; lia | cbn; lia | exact VS96].
- apply pairwise_disjoint_of_extents.
  unfold b2_rgSH, b2_rgSP, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val zpairwise_disjoint zall_disjoint].
  rewrite U18, U9. unfold zdisj. cbn [fst snd]. unfold SHADOW_OFF in *. lia.
- unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U18, !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; try exact I; unfold SHADOW_OFF in *; lia.
Qed.

Lemma b2_entryT : forall (W : world segs) regs mem pc lo hi F sp1,
  YK11.getr regs 25 = w64 (F + 96) -> YK11.getr regs 9 = w64 sp1 ->
  lo <= bv_unsigned (YK11.getr regs 23) <= hi ->
  4096 <= F -> F + 96 <= B2_PHI -> YM05.alloc_ceiling <= sp1 -> sp1 + 80 <= 2 ^ 63 ->
  val_mem segs (mrestrict (w_H W) mem) (sp1 + 72) 8 (2 ^ 64 - 1 - (F + 96)) ->
  st_ok_pi segs VAL (b2_E regs 0 0 0 0 (2 ^ 64 - 1 - (F + 96))) (b2_ssT pc lo hi)
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + pc)) mem (YK11.seg_rom segs))).
Proof.
intros W regs mem pc lo hi F sp1 R25 R9 H23 HF0 HF1 Hs0 Hs1 VS72.
set (E := b2_E regs 0 0 0 0 (2 ^ 64 - 1 - (F + 96))).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs r)
  by (intros; apply b2_ew_reg; assumption).
pose proof (b2_ew_x regs 0 0 0 0 (2 ^ 64 - 1 - (F + 96)) 4 ltac:(lia)) as E36. cbn [Nat.add nth] in E36. fold E in E36.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold B2_PHI in HF1.
assert (U9 : bv_unsigned (ew E 9) = sp1) by (rewrite (EE 9%nat 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
assert (U23 : bv_unsigned (ew E 23) = bv_unsigned (YK11.getr regs 23)) by (rewrite (EE 23%nat 23%bv eq_refl); reflexivity).
assert (U25 : bv_unsigned (ew E 25) = F + 96) by (rewrite (EE 25%nat 25%bv eq_refl), R25; apply unsigned_lit_small; lia).
assert (U36 : bv_unsigned (ew E 36) = 2 ^ 64 - 1 - (F + 96)) by (rewrite E36; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. unfold b2_ssT.
apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold b2_rgT. apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val segs E _ sp1 72 8 (SOff 36 0) (2 ^ 64 - 1 - (F + 96)));
    [rewrite denot_lit_U, (U_atom E 36 _ E36 ltac:(lia)); reflexivity | cbn; lia | cbn; lia | exact VS72].
- apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. exact (conj I I).
- unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok, B2_PHI. cbn [af_lo af_hi af_al2]. rewrite U23, U25, U36, !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.
End e.

(* ------------------------------------------------------------------ *)
(* 3. The stretches                                                     *)
(* ------------------------------------------------------------------ *)

(* The value of register r in the machine state of HS: its symbolic value, computed, then tac. *)
Ltac b2_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | ?T => idtac "b2_reg: no match for" T; fail
  end.
(* The low atoms of a run's valuation are its start's (AGX, when the run made tokens). *)
Ltac b2_agx := try (match goal with HA : forall nn : nat, (nn < 240)%nat -> ew _ nn = ew _ nn |- _ =>
  rewrite HA by lia end).
(* Register r (nat nn, Z zz) of HS kept from the run's start registers rg (valuation E0, EE0 its registers). *)
Ltac b2_kreg HS EE0 rg nn zz G :=
  b2_reg HS (Z_to_bv 5 zz) (YK11.getr rg (Z_to_bv 5 zz)) G
    ltac:(cbn [sv_denot]; b2_agx; rewrite (EE0 nn (Z_to_bv 5 zz) eq_refl), Z.add_0_r,
          Z_to_bv_bv_unsigned; reflexivity).
(* Region i of the symbolic state HS, at the machine state's memory. *)
Ltac b2_region HS i HR :=
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
Ltac b2_awr_rs :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
(* The write rights of a run whose regions write no byte. *)
Ltac b2_awr_ro :=
  b2_awr_rs;
  repeat (apply awr_ok_x_cons;
          [let a := fresh "a" in let Ha := fresh "Ha" in
           intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |]);
  apply awr_ok_x_nil.
(* After a run: the model generalized. *)
Ltac b2_after :=
  lazymatch goal with |- SRr _ _ (mkCfg _ (with_vm_backing (m_vm_lazy ?m0) ?mt ?m0)) _ =>
    let md := fresh "mdw" in set (md := with_vm_backing (m_vm_lazy m0) mt m0) in *; clearbody md; clear mt end.

(* A one-byte chunk of a literal, read through the view. *)
Lemma b2_byte_view : forall (sg : list Segment) E (H : word -> bool) (m : word -> option byte) base off n,
  YP09.chunk_ok sg E (mrestrict H m) base (YP09.mkChunk off (CVal 1 (SLit n))) ->
  aview sg H m (base + off) = Some (bv_unsigned (YP09.byte_of_word (Z_to_bv 64 n) 0)).
Proof.
  intros sg E H m base off n Hc. destruct (Hc 0 ltac:(cbn; lia)) as (b & Eb & Mb).
  cbn [YP09.cbyte YP09.c_val YP09.c_off sv_denot] in Eb, Mb. injection Eb as <-. rewrite Z.add_0_r in Mb.
  unfold aview. rewrite Mb. reflexivity.
Qed.

Ltac b2_ifs H := repeat match type of H with
  | context [?a =? ?b] => destruct (Z.eqb_spec a b); try lia
  | context [?a <=? ?b] => destruct (Z.leb_spec a b); try lia
  | context [?a <? ?b] => destruct (Z.ltb_spec a b); try lia end.

Lemma b2_pres_grow : forall (H : word -> bool) (m m' : word -> option byte) a,
  YK1b.mem_grows (mrestrict H m) (mrestrict H m') -> apresent H m a -> apresent H m' a.
Proof.
intros H m m' a G (Ha & b & Hb). split; [exact Ha|]. specialize (G (Z_to_bv 64 a)). unfold mrestrict in G.
rewrite Ha, Hb in G. destruct (m' (Z_to_bv 64 a)) as [b'|];
  [exists b'; reflexivity | exfalso; apply G; [discriminate | reflexivity]].
Qed.

(* After a run whose regions write no byte: the running facts KV (the view at the current memory is the view at the
   reference memory) and GP (presence grows from the reference memory) move to the run's end. *)
Ltac b2_step W KV GP :=
  match goal with HFr : frame_of _ _ (mrestrict _ ?mp) (mrestrict _ ?mn), HG : YK1b.mem_grows _ _ |- _ =>
    let KD := fresh "KD" in
    assert (KD : forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H W) mn a = aview tfibsegs (w_H W) mp a)
      by (let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
          apply (kept_of_frame _ _ _ _ _ (fun _ : Z => False) HFr); [| exact Ha | intros []];
          let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in
          let x := fresh "x" in let Hin := fresh "Hin" in
          intros b wlo whi x Hin;
          lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end;
          cbn [In] in Hin; repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; lia |]); destruct Hin);
    let K2 := fresh "K" in let G2 := fresh "G" in
    pose proof (fun a Ha => eq_trans (KD a Ha) (KV a Ha)) as K2;
    pose proof (fun a Ha => b2_pres_grow _ _ _ a HG (GP a Ha)) as G2;
    clear KD KV GP HFr HG; rename K2 into KV; rename G2 into GP;
    try match goal with HF0 : frame_of _ _ _ _ |- _ => clear HF0 end
  end.

(* `beqz` on an atom m holding n: the test n = 0. *)
Lemma b2_beqz : forall E (m : nat) n b, ew E m = Z_to_bv 64 n -> 0 <= n < 2 ^ 64 ->
  branch_taken BC_EQ (sv_denot E (SOff m 0)) (sv_denot E (SLit 0)) = b -> (n =? 0) = b.
Proof.
intros E m n b Hm Hn Hb. rewrite <- Hb.
rewrite (denot_lit_U E (SOff m 0)), U_SOff, Hm, unsigned_lit_small by lia. rewrite Z.add_0_r, (zcanon_id n) by (unfold M64; lia).
change (sv_denot E (SLit 0)) with (Z_to_bv 64 0). cbn [branch_taken].
unfold bv_eqb. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite !Z.mod_small by lia. reflexivity.
Qed.

(* `bge` of two small values. *)
Lemma b2_ge_small : forall u s, 0 <= u < 8 -> 0 <= s < 8 ->
  branch_taken BC_GE (Z_to_bv 64 u) (Z_to_bv 64 s) = (s <=? u).
Proof.
intros u s Hu Hs.
assert (Hu8 : u = 0 \/ u = 1 \/ u = 2 \/ u = 3 \/ u = 4 \/ u = 5 \/ u = 6 \/ u = 7) by lia.
assert (Hs8 : s = 0 \/ s = 1 \/ s = 2 \/ s = 3 \/ s = 4 \/ s = 5 \/ s = 6 \/ s = 7) by lia.
destruct Hu8 as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]];
  destruct Hs8 as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]; vm_compute; reflexivity.
Qed.

(* The slow path's `bge (x & 7), s` with s the shadow byte of x, not 0: x is addressable (saddr_ok), so x mod 8 < s and
   the branch to the report is not taken. *)
Lemma b2_bge : forall E (n m : nat) x s b, ew E n = Z_to_bv 64 x -> ew E m = Z_to_bv 64 s -> 0 <= x < 2 ^ 64 ->
  saddr_ok x s -> s <> 0 ->
  branch_taken BC_GE (sv_denot E (SAlu ALU_AND (SOff n 0) (SLit 7))) (sv_denot E (SOff m 0)) = b -> b = false.
Proof.
intros E n m x s b Hn Hm Hx Hok Hs0 Hb. rewrite <- Hb.
unfold saddr_ok in Hok. destruct Hok as [-> | (H1 & H2)]; [lia|].
pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as M8.
rewrite (denot_lit_U E (SAlu _ _ _)), U_and_lit by lia. rewrite (U_atom E n x Hn Hx).
rewrite (denot_lit_U E (SOff m 0)), (U_atom E m s Hm ltac:(lia)).
change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
rewrite (b2_ge_small (x mod 8) s M8 ltac:(lia)). apply Z.leb_gt. exact H1.
Qed.

Lemma b2_rng : forall x, 0 <= x < 256 -> 0 <= x < 2 ^ 64.
Proof. intros x H. lia. Qed.
Lemma b2_denot_off : forall E n v, ew E n = w64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n 0) = w64 v.
Proof.
intros E n v H Hv. rewrite denot_lit_U, U_SOff, H, Z.add_0_r. unfold w64. f_equal.
rewrite unsigned_lit_small by lia. apply zcanon_id. unfold M64. lia.
Qed.
Lemma b2_denot_add : forall E n m c u v, ew E n = w64 u -> ew E m = w64 v -> 0 <= u < 2 ^ 64 -> 0 <= u + c ->
  0 <= v < 2 ^ 64 -> u + c + v < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SOff n c) (SOff m 0)) = w64 (u + c + v).
Proof.
intros E n m c u v Hn Hm Hu Huc Hv Huv. rewrite denot_lit_U, U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, Hn, Hm, Z.add_0_r.
unfold w64. f_equal. rewrite !unsigned_lit_small by lia. rewrite (zcanon_id (u + c)), (zcanon_id v) by (unfold M64; lia).
apply zcanon_id. unfold M64. lia.
Qed.
Section dimg. Context {rc : YM05.RunCeil}.
Lemma b2_denot_img : forall E n, img_env (@pa_val _ transportb_listing PI_transportb) A_LIM E ->
  (A_TEXT <= n < A_LIM)%nat -> sv_denot E (SOff n 0) = w64 (@pa_val _ transportb_listing PI_transportb n).
Proof.
intros E n HE Hn. rewrite denot_lit_U, U_SOff, (HE n Hn), Z.add_0_r. unfold w64. f_equal.
apply zcanon_id. rewrite <- (HE n Hn). pose proof (u64_range (ew E n)). exact H.
Qed.
End dimg.
(* `srli x, s, 3; add x, x, s10` at s = q + c: the shadow address of q + c. *)
Lemma b2_denot_shadow : forall E n m c q, ew E n = w64 q -> ew E m = w64 SHADOW_OFF ->
  0 <= q -> 0 <= c <= 8 -> q + c <= B2_PHI ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff n c) (SLit 3)) (SOff m 0)) = w64 (SHADOW_OFF + (q + c) / 8).
Proof.
intros E n m c q Hn Hm Hq Hc Hqc. unfold B2_PHI in Hqc.
assert (HD : 0 <= (q + c) / 8 <= 17592185995776) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
rewrite denot_lit_U. unfold w64. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom_off E n q c Hn ltac:(lia) ltac:(lia)), (U_atom E m SHADOW_OFF Hm ltac:(unfold SHADOW_OFF; lia)).
rewrite U_SLit, (zcanon_id 3) by (unfold M64; lia).
change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
rewrite (zcanon_id ((q + c) / 8)) by (unfold M64; lia).
rewrite (Z.add_comm ((q + c) / 8) SHADOW_OFF). apply zcanon_id. unfold M64, SHADOW_OFF. lia.
Qed.

(* A run of bytes read through the view, as garr8. *)
Lemma b2_garr8_of_aview : forall H (m : word -> option byte) base (l : list Z),
  (forall j, (j < length l)%nat -> aview tfibsegs H m (base + Z.of_nat j) = Some (nth j l 0)) ->
  garr8 tfibsegs (mrestrict H m) base l.
Proof.
intros H m base l Hv j Hj.
destruct (aview_byte tfibsegs H m _ _ (Hv j Hj)) as (b & _ & _ & Hr).
exact (conj (YE2y.val_mem1_of_aview H m _ _ (Hv j Hj)) Hr).
Qed.

(* A region of the G journal whose writable bytes are bytes of a frame the journal owns, or that frame's shadow bytes
   (TransportGFrame.v awr_ok_x_cons_own). *)
Lemma b2_awr_own : forall E r rs G OUT STK sp0 FP bl0 blc ly own cid pos,
  In (cid, pos) own ->
  (forall a, base_val E (YP09.r_base r) + YP09.r_wlo r <= a < base_val E (YP09.r_base r) + YP09.r_whi r ->
     in_zr a (frame_addr ly cid pos, fs_frame_bytes cid) \/
     in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8)) ->
  awr_ok_x E rs G 0 OUT STK sp0 FP bl0 blc ly own -> awr_ok_x E (r :: rs) G 0 OUT STK sp0 FP bl0 blc ly own.
Proof.
intros E r rs G OUT STK sp0 FP bl0 blc ly own cid pos Hin Hr H.
apply awr_ok_x_cons; [|exact H].
intros a Ha. left. split; [|lia].
unfold awr_byte. right; right; right. unfold in_frames. exists cid, pos. split; [exact Hin | exact (Hr a Ha)].
Qed.

Lemma b2_rdword : forall (rd : reader) a (f : Z -> Z), (forall i, 0 <= i < 8 -> rd (a + i) = Some (f i)) ->
  rdword rd a = Some (f 0 + 256 * (f 1 + 256 * (f 2 + 256 * (f 3 + 256 * (f 4 + 256 * (f 5 + 256 * (f 6 + 256 * f 7))))))).
Proof.
intros rd a f H. unfold rdword.
pose proof (H 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0.
rewrite H0, (H 1 ltac:(lia)), (H 2 ltac:(lia)), (H 3 ltac:(lia)), (H 4 ltac:(lia)), (H 5 ltac:(lia)),
  (H 6 ltac:(lia)), (H 7 ltac:(lia)). reflexivity.
Qed.

(* The divisor constant's word, read as the image (K1's trans_rom_view_rd, st.v lc_rom_bytes). *)
Lemma b2_kval : forall (W : world tfibsegs) mem, trans_rom_view_rd W mem ->
  val_mem tfibsegs (mrestrict (w_H W) mem) TRANS_K_LLVMF 8 B2_K3.
Proof.
intros W mem HR. apply YE2y.val_mem_of_rdword.
assert (LP : length (TW.put 8 0x5555555555555556) = 8%nat) by (vm_compute; reflexivity).
assert (HB : forall i, 0 <= i < 8 -> aview tfibsegs (w_H W) mem (TRANS_K_LLVMF + i) =
  Some ((fun j => bv_unsigned (nth (Z.to_nat j) (TW.put 8 0x5555555555555556) (Z_to_bv 8 0))) i)).
{ intros i Hi. rewrite (HR (TRANS_K_LLVMF + i)).
  - replace (TRANS_K_LLVMF + i) with (TRANS_K_LLVMF + Z.of_nat (Z.to_nat i)) by lia.
    apply lc_rom_bytes; [unfold lc_rom_tab; cbn [In]; b2_in | rewrite LP; lia].
  - unfold trans_in_ro_rd. apply Exists_exists. exists (TRANS_K_LLVMF, 8).
    split; [unfold TRANS_RO_RD; cbn [In app]; b2_in | unfold in_zr; cbn [fst snd]; lia]. }
rewrite (b2_rdword _ _ _ HB). vm_compute. reflexivity.
Qed.

(* body after the copy of src (6 bytes) at offset k, and after the copy as the model states it (lc_ann_vals' body1). *)
Definition b2_body (k : Z) (src : list byte) : list byte := TW.upd (repeat (DSpec.b8 0) 34) k src.
Definition b2_body1 (mac : Z) : list byte :=
  if mac <? 10 then b2_body mac TC.HOST else if mac <? 13 then b2_body (mac - 10) TC.OTHER else repeat (DSpec.b8 0) 34.

(* The 6 bytes of HOST / OTHER in the image (st.v lc_rom_bytes). *)
Lemma b2_src_rom : forall (x : Z) (src : list byte) i, (x, src) = (TRANS_HOST, TC.HOST) \/ (x, src) = (TRANS_OTHER, TC.OTHER) ->
  0 <= i < 6 -> trans_in_ro_rd (x + i) /\
  option_map (fun b : byte => bv_unsigned b) (YK11.seg_rom tfibsegs (Z_to_bv 64 (x + i))) =
    Some (bv_unsigned (nth (Z.to_nat i) src (Z_to_bv 8 0))).
Proof.
intros x src i Hx Hi.
assert (Hl : length src = 6%nat) by (destruct Hx as [Hx | Hx]; injection Hx as -> ->; reflexivity).
split.
- apply (b2_src_ro x (x + i)); [destruct Hx as [Hx | Hx]; injection Hx as -> ->; tauto | lia].
- replace (x + i) with (x + Z.of_nat (Z.to_nat i)) by lia.
  apply lc_rom_bytes; [|rewrite Hl; lia].
  destruct Hx as [Hx | Hx]; injection Hx as -> ->; unfold lc_rom_tab; cbn [In]; b2_in.
Qed.

Section h. Context {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).
Local Abbreviation av W m := (aview tfibsegs (w_H W) m).

Lemma b2_base : BASE = 0x812a0 /\ transportb_text = 0x812a0.
Proof. split; vm_compute; reflexivity. Qed.

Definition b2_retB (z : bool) : Z := if z then 0xaa0 else 0xda8.

(* The stretch from +0xa74 (z = true) or +0xd78 (z = false) through the call of memset: s7 = a0 & 15 (z = false),
   body's shadow into scope (bytes 12 .. 16 = 0, 0, 0, 0, 2), s9 = 96(s1) = body, memset (body, 0, 34); back at
   +0xaa0 or +0xda8. *)
Lemma b2_setB (K2 : lc_src_ro_stmt B MT XL RLO RHI) : forall cx op (z : bool) ly S (W : world segs) regs mem md e,
  @lp_prem rc B MT XL RLO RHI -> @lc_base rc B MT XL RLO RHI cx ->
  @lc_lcore rc B MT cx op false false (lo_k op) ly S W regs mem md e -> lc_tw W mem (lo_B op) ->
  SRr segs W (lc_cfg cx (if z then 0xa74 else 0xd78) regs mem md)
    (fun W' c' => exists regs2 mem2 md2, c' = lc_cfg cx (b2_retB z) regs2 mem2 md2 /\
       @lc_lcore rc B MT cx op false true (lo_k op) ly S W' regs2 mem2 md2 e /\ lc_tw W' mem2 (lo_B op) /\
       garr8 segs (mrestrict (w_H W') mem2) (lc_F cx + 96) (repeat 0 34) /\
       (forall r, In r [19; 20; 21; 22; 24; 27] -> YK11.getr regs2 (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)) /\
       YK11.getr regs2 25 = w64 (lc_F cx + 96) /\
       (z = false -> YK11.getr regs2 23 = w64 (Z.land (bv_unsigned (YK11.getr regs 10)) 15))).
Proof.
intros cx op z ly S W regs mem md e HP HB HL HTW.
pose proof (lp_laws _ _ _ _ _ HP) as LAWS.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned _ _ _ _ _ HP)) as HGX.
pose proof HL as (HC & HFR & HSP & HFSH & HOK & He & HMT & R19).
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
{ intros o v Hin. unfold lc_spills in HSP. rewrite Forall_forall in HSP. apply YE2y.val_mem_of_rdword. exact (HSP _ Hin). }
pose proof (HSPv 96 (lc_F cx + 96) ltac:(unfold lf_spill_loop; apply in_or_app; right; cbn; tauto)) as VS96.
assert (ESH : lc_SH cx = SHADOW_OFF + lc_F cx / 8) by reflexivity.
assert (HSH0 : SHADOW_OFF <= lc_SH cx /\ lc_SH cx + 32 <= 17594333495296).
{ rewrite ESH. unfold SHADOW_OFF, LF_FBYTES in *. split; [pose proof (Z.div_pos (lc_F cx) 8 ltac:(lia) ltac:(lia)); lia|].
  assert (lc_F cx / 8 <= 0x7fffff800000 / 8) by (apply Z.div_le_mono; lia).
  change (0x7fffff800000 / 8) with 0xffffff00000 in *. lia. }
assert (Hpres : forall a, lc_SH cx + 12 <= a < lc_SH cx + 17 -> apresent (w_H W) mem a).
{ intros a Ha. apply (apresent_of_aview segs); [unfold SHADOW_OFF in *; lia | |].
  - intros Hi. pose proof (transportb_segs_low a Hi) as Hl. unfold kLowMemEnd, SHADOW_OFF in *. lia.
  - replace a with (lc_SH cx + (a - lc_SH cx)) by lia.
    rewrite (HFSH (a - lc_SH cx) ltac:(lia)). discriminate. }
destruct Hstk as (Hceil & Hslo & Hshi & H47).
unfold LLVMF_STK, LF_FRAME, LF_FBYTES in *.
pose proof (@b2_entryB (l_fx cx) rc W regs mem (if z then 0xa74 else 0xd78) (lc_F cx) (lc_sp1 cx) (lc_SH cx) R18 R9
  (proj1 HSH0) (proj2 HSH0) ltac:(lia) ltac:(lia) VS96 ltac:(lia) Hpres) as HS.
set (E0 := b2_E regs 0 0 0 (lc_F cx + 96) 0) in *.
assert (HEI : img_env VAL A_LIM E0) by apply b2_env_img.
assert (SHOK : sh_ok segs (SLit 0) [] E0 (mrestrict (w_H W) mem)) by constructor.
assert (EE0 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E0 n = YK11.getr regs r)
  by (intros; apply b2_ew_reg; assumption).
assert (E35 : ew E0 35 = w64 (lc_F cx + 96)).
{ pose proof (b2_ew_x regs 0 0 0 (lc_F cx + 96) 0 3 ltac:(lia)) as H. exact H. }
assert (U18 : bv_unsigned (ew E0 18) = lc_SH cx).
{ rewrite (EE0 18%nat 18%bv eq_refl), R18. apply unsigned_lit_small. unfold SHADOW_OFF in *. lia. }
pose proof (@paj_run_x (l_fx cx) rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B
  HGX 0 []) as RUN.
unfold lc_cfg. change (w64 (transportb_text + if z then 0xa74 else 0xd78))
  with (Z_to_bv 64 (BASE + if z then 0xa74 else 0xd78)).
(* after the run: the call of memset *)
lazymatch goal with |- SRr _ _ _ ?Q => set (Q0 := Q) end.
destruct b2_base as (HBASE & HTT).
assert (POST : forall regsT memT md1, b2_J B cx ly S W memT md1 e ->
  (forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 24; 26; 27] ->
     YK11.getr regsT (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)) ->
  YK11.getr regsT 1 = Z_to_bv 64 (BASE + b2_retB z) ->
  YK11.getr regsT 10 = w64 (lc_F cx + 96) -> YK11.getr regsT 11 = w64 0 ->
  YK11.getr regsT 12 = w64 34 -> YK11.getr regsT 25 = w64 (lc_F cx + 96) ->
  (z = false -> YK11.getr regsT 23 = w64 (Z.land (bv_unsigned (YK11.getr regs 10)) 15)) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lc_SH cx + 12 <= a < lc_SH cx + 17) -> av W memT a = av W mem a) ->
  (forall a, apresent (w_H W) mem a -> apresent (w_H W) memT a) ->
  (forall i, 0 <= i < 5 -> av W memT (lc_SH cx + 12 + i) = Some (nth (Z.to_nat i) B2_BSH 0)) ->
  SRr segs W (mkCfg (@YK11.mkst (l_fx cx) regsT (Z_to_bv 64 (b2_ipc OSet)) memT (YK11.seg_rom segs)) md1) Q0).
{ intros regsT memT md1 HJ1 KR R1 R10 R11 R12 R25 R23 KM KP KS.
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
  destruct (b2_move B MT XL RLO RHI cx op false false true (lo_k op) ly S W regs mem md e regsT memT md1 0 LAWS HGX HB HL
    HTW HJ1) as [HL1 HTW1].
  { intros r Hr. apply KR. cbn [In] in Hr |- *. tauto. }
  { unfold LLVMF_STK. lia. }
  { intros a Ha Hout. apply KM; [exact Ha|]. intros Hs. apply Hout. right. right. exact Hs. }
  { exact KP. }
  { exact HFSH1. }
  eapply SRr_mono.
  { apply (b2_icall B MT XL RLO RHI K2 cx op (lo_k op) OSet ly S W regsT memT md1 e (lc_F cx + 96) 0 34
      (Z_to_bv 64 (BASE + b2_retB z)) HP HB HL1 HTW1 R10 R11 R12 R1).
    - apply ret_ok_codeptr_v; destruct z; cbn; lia.
    - lia.
    - lia.
    - lia.
    - exact I. }
  intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HL2 & HTW2 & HPR & HBY & _).
  exists regs2, mem2, md2. split.
  { unfold lc_cfg, w64. rewrite HBASE, HTT. reflexivity. }
  split; [exact HL2|]. split; [exact HTW2|]. split.
  { apply b2_garr8_of_aview. rewrite repeat_length. intros j Hj. rewrite (HBY (Z.of_nat j) ltac:(lia)).
    rewrite b2_nth_repeat by lia. reflexivity. }
  split.
  { intros r Hr. rewrite (HPR r ltac:(unfold acallee_saved; cbn [In] in Hr; lia)). apply KR. cbn [In] in Hr |- *. tauto. }
  split.
  { exact (eq_trans (HPR 25 ltac:(unfold acallee_saved; lia)) R25). }
  intros Hz. exact (eq_trans (HPR 23 ltac:(unfold acallee_saved; lia)) (R23 Hz)). }
assert (AWR : forall rs, awr_ok_x E0 rs TG.G_HARNESS_B 0 [] LLVMF_STK (lc_sp0 cx) []
    (ablocks B (l_ly cx) (l_S cx)) (ablocks B ly S) ly [(LF_CID, l_fpos cx)] ->
  awr_ok_x E0 (b2_rgSH :: rs) TG.G_HARNESS_B 0 [] LLVMF_STK (lc_sp0 cx) []
    (ablocks B (l_ly cx) (l_S cx)) (ablocks B ly S) ly [(LF_CID, l_fpos cx)]).
{ intros rs H. apply (b2_awr_own _ _ _ _ _ _ _ _ _ _ _ _ LF_CID (l_fpos cx)); [left; reflexivity | | exact H].
  intros a Ha. cbn [b2_rgSH YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U18 in Ha.
  right. unfold in_zr. cbn [fst snd]. rewrite HFaddr. change (fs_frame_bytes LF_CID / 8) with 32.
  unfold lc_SH in Ha. unfold shadow_addr. lia. }
destruct z.
all: paj_run_tok RUN HS HJ SHOK (0, 0).
1, 3: b2_awr_rs; apply AWR; apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia|];
  apply awr_ok_x_nil.
all: b2_after.
all: lazymatch type of HS with context [restrict _ ?m] => rename m into ms1 end.
all: lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => rename m into md1 end.
all: assert (KM : forall a, 0 <= a < 2 ^ 64 -> ~ (lc_SH cx + 12 <= a < lc_SH cx + 17) -> av W (ms_mem ms1) a = av W mem a)
  by (intros a Ha Hn0; apply (kept_of_frame _ _ _ _ _ (fun x => lc_SH cx + 12 <= x < lc_SH cx + 17) HFr);
      [| exact Ha | exact Hn0];
      intros b wlo whi x Hin Hx;
      lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end;
      cbn [In] in Hin;
      repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; rewrite ?U18 in Hx; lia |]);
      destruct Hin).
all: b2_region HS 0%nat HR.
all: destruct HR as (_ & _ & _ & HCH).
all: apply Forall_cons_iff in HCH as [H16 HCH]; apply Forall_cons_iff in HCH as [H15 HCH];
  apply Forall_cons_iff in HCH as [H14 HCH]; apply Forall_cons_iff in HCH as [H13 HCH];
  apply Forall_cons_iff in HCH as [H12 _].
all: apply b2_byte_view in H16, H15, H14, H13, H12; cbn [YP09.r_base base_val] in H16, H15, H14, H13, H12;
  rewrite U18 in H16, H15, H14, H13, H12.
all: assert (KS : forall i, 0 <= i < 5 -> av W (ms_mem ms1) (lc_SH cx + 12 + i) = Some (nth (Z.to_nat i) B2_BSH 0))
  by (intros i Hi; assert (Hc : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4) by lia;
      destruct Hc as [-> | [-> | [-> | [-> | ->]]]];
        [ replace (lc_SH cx + 12 + 0) with (lc_SH cx + 12) by lia; refine (eq_trans H12 _)
        | replace (lc_SH cx + 12 + 1) with (lc_SH cx + 13) by lia; refine (eq_trans H13 _)
        | replace (lc_SH cx + 12 + 2) with (lc_SH cx + 14) by lia; refine (eq_trans H14 _)
        | replace (lc_SH cx + 12 + 3) with (lc_SH cx + 15) by lia; refine (eq_trans H15 _)
        | replace (lc_SH cx + 12 + 4) with (lc_SH cx + 16) by lia; refine (eq_trans H16 _) ]; vm_compute; reflexivity).
all: b2_reg HS (Z_to_bv 5 10) (w64 (lc_F cx + 96)) G10
  ltac:(cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
all: b2_reg HS (Z_to_bv 5 25) (w64 (lc_F cx + 96)) G25
  ltac:(cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
all: b2_reg HS (Z_to_bv 5 11) (w64 0) G11 ltac:(reflexivity).
all: b2_reg HS (Z_to_bv 5 12) (w64 34) G12 ltac:(reflexivity).
all: b2_kreg HS EE0 regs 2%nat 2 GK2. all: b2_kreg HS EE0 regs 3%nat 3 GK3. all: b2_kreg HS EE0 regs 4%nat 4 GK4.
all: b2_kreg HS EE0 regs 8%nat 8 GK8. all: b2_kreg HS EE0 regs 9%nat 9 GK9. all: b2_kreg HS EE0 regs 18%nat 18 GK18.
all: b2_kreg HS EE0 regs 19%nat 19 GK19. all: b2_kreg HS EE0 regs 20%nat 20 GK20.
all: b2_kreg HS EE0 regs 21%nat 21 GK21. all: b2_kreg HS EE0 regs 22%nat 22 GK22.
all: b2_kreg HS EE0 regs 24%nat 24 GK24. all: b2_kreg HS EE0 regs 26%nat 26 GK26.
all: b2_kreg HS EE0 regs 27%nat 27 GK27.
all: assert (GK : forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 24; 26; 27] ->
  YK11.getr (ms_regs ms1) (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r))
  by (intros r Hr; cbn [In] in Hr; repeat (destruct Hr as [<- | Hr]; [assumption |]); destruct Hr).
- b2_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 0xaa0)) G1 ltac:(apply codeptr_val; exact HEI).
  pmkst HS.
  apply (POST (ms_regs ms1) (ms_mem ms1) md1 HJ GK G1 G10 G11 G12 G25 (fun Hz => ltac:(discriminate Hz)) KM
    (fun a Ha => b2_pres_grow (w_H W) mem (ms_mem ms1) a HG Ha) KS).
- b2_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 0xda8)) G1 ltac:(apply codeptr_val; exact HEI).
  assert (V23 : sv_denot E0 (SAlu ALU_AND (SOff 10 0) (SLit 15)) = w64 (Z.land (bv_unsigned (YK11.getr regs 10)) 15)).
  { rewrite denot_lit_U. rewrite U_and_lit by lia. unfold w64. f_equal. f_equal.
    rewrite U_SOff. rewrite (EE0 10%nat 10%bv eq_refl). rewrite Z.add_0_r. apply zcanon_id. apply u64_range. }
  b2_reg HS (Z_to_bv 5 23) (w64 (Z.land (bv_unsigned (YK11.getr regs 10)) 15)) G23 ltac:(exact V23).
  pmkst HS.
  apply (POST (ms_regs ms1) (ms_mem ms1) md1 HJ GK G1 G10 G11 G12 G25 (fun _ => G23) KM
    (fun a Ha => b2_pres_grow (w_H W) mem (ms_mem ms1) a HG Ha) KS).
Qed.

(* The call of memcpy (body + k, src, 6) at +0xdc8 and the return at +0xdcc (ANN). *)
Lemma b2_cpy (K1 : lc_rom_view_stmt B MT XL RLO RHI) (K2 : lc_src_ro_stmt B MT XL RLO RHI) :
  forall cx op ly S (W : world segs) regsT memT mdT e k x (src : list byte),
  @lp_prem rc B MT XL RLO RHI -> @lc_base rc B MT XL RLO RHI cx ->
  @lc_lcore rc B MT cx op false true (lo_k op) ly S W regsT memT mdT e -> lc_tw W memT (lo_B op) ->
  garr8 segs (mrestrict (w_H W) memT) (lc_F cx + 96) (repeat 0 34) ->
  (x, src) = (TRANS_HOST, TC.HOST) \/ (x, src) = (TRANS_OTHER, TC.OTHER) -> 0 <= k <= 28 ->
  YK11.getr regsT 10 = w64 (lc_F cx + 96 + k) -> YK11.getr regsT 11 = w64 x -> YK11.getr regsT 12 = w64 6 ->
  YK11.getr regsT 1 = Z_to_bv 64 (BASE + LO_ANN) ->
  SRr segs W (mkCfg (@YK11.mkst (l_fx cx) regsT (Z_to_bv 64 (b2_ipc OCpy)) memT (YK11.seg_rom segs)) mdT)
    (fun W' c' => exists regs2 mem2 md2, c' = lc_cfg cx LO_ANN regs2 mem2 md2 /\
       @lc_lcore rc B MT cx op false true (lo_k op) ly S W' regs2 mem2 md2 e /\ lc_tw W' mem2 (lo_B op) /\
       garr8 segs (mrestrict (w_H W') mem2) (lc_F cx + 96) (TW.zs (b2_body k src)) /\
       aregs_preserved regsT regs2).
Proof.
intros cx op ly S W regsT memT mdT e k x src HP HB HL HTW HZ Hx Hk R10 R11 R12 R1.
pose proof HL as (HC & _).
pose proof (K1 HP cx ly S W regsT memT mdT e HB HC) as HROM.
assert (HSRC : forall i, 0 <= i < 6 -> av W memT (x + i) = Some (bv_unsigned (nth (Z.to_nat i) src (Z_to_bv 8 0)))).
{ intros i Hi. destruct (b2_src_rom x src i Hx Hi) as (Hro & Hv). rewrite (HROM _ Hro). exact Hv. }
destruct b2_base as (HBASE & HTT).
eapply SRr_mono.
{ apply (b2_icall B MT XL RLO RHI K2 cx op (lo_k op) OCpy ly S W regsT memT mdT e (lc_F cx + 96 + k) x 6
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
apply b2_garr8_of_aview. unfold TW.zs. rewrite length_map. unfold b2_body.
assert (Hsl : length src = 6%nat) by (destruct Hx as [Hx | Hx]; injection Hx as -> ->; reflexivity).
assert (Hul : length (TW.upd (repeat (DSpec.b8 0) 34) k src) = 34%nat).
{ unfold TW.upd. rewrite !length_app, length_firstn, length_skipn, !repeat_length, Hsl. lia. }
rewrite Hul. intros j Hj.
rewrite (map_nth (fun b : byte => bv_unsigned b) _ (Z_to_bv 8 0)). change (bv_unsigned (Z_to_bv 8 0)) with 0.
rewrite (b2_upd_nth src k j Hsl ltac:(lia) ltac:(lia) Hj).
destruct ((k <=? Z.of_nat j) && (Z.of_nat j <? k + 6))%bool eqn:Ein.
- apply andb_true_iff in Ein as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
  replace (lc_F cx + 96 + Z.of_nat j) with (lc_F cx + 96 + k + (Z.of_nat j - k)) by lia.
  rewrite (HBY (Z.of_nat j - k) ltac:(lia)). rewrite (HSRC (Z.of_nat j - k) ltac:(lia)).
  do 3 f_equal. lia.
- rewrite (HK (lc_F cx + 96 + Z.of_nat j) ltac:(lia)).
  + destruct (garr8_nthZ segs _ _ _ (Z.of_nat j) HZ ltac:(lia) ltac:(rewrite repeat_length; lia)) as (Hv & _).
    rewrite b2_nth_repeat in Hv by lia.
    rewrite (can_aview_of_val1 segs _ _ _ _ Hv). reflexivity.
  + apply andb_false_iff in Ein as [E1 | E1]; [apply Z.leb_gt in E1 | apply Z.ltb_ge in E1]; lia.
Qed.

(* The stretch from +0xaa0 (z = true: s11 = s6 = s7 = 0, mac = 0) or +0xda8 (z = false, s7 = mac) to ANN (+0xdcc):
   the copy of HOST to body + mac (mac < 10) or of OTHER to body + mac - 10 (10 <= mac <= 12), or nothing
   (mac > 12), each after its UBSan tests (decided by the run). *)
Lemma b2_tail (K1 : lc_rom_view_stmt B MT XL RLO RHI) (K2 : lc_src_ro_stmt B MT XL RLO RHI) :
  forall cx op (z : bool) ly S (W : world segs) regs mem md e mac,
  @lp_prem rc B MT XL RLO RHI -> @lc_base rc B MT XL RLO RHI cx ->
  @lc_lcore rc B MT cx op false true (lo_k op) ly S W regs mem md e -> lc_tw W mem (lo_B op) ->
  garr8 segs (mrestrict (w_H W) mem) (lc_F cx + 96) (repeat 0 34) -> YK11.getr regs 25 = w64 (lc_F cx + 96) ->
  (if z then mac = 0 else YK11.getr regs 23 = w64 mac) -> 0 <= mac < 16 ->
  SRr segs W (lc_cfg cx (b2_retB z) regs mem md)
    (fun W' c' => exists regs2 mem2 md2, c' = lc_cfg cx LO_ANN regs2 mem2 md2 /\
       @lc_lcore rc B MT cx op false true (lo_k op) ly S W' regs2 mem2 md2 e /\ lc_tw W' mem2 (lo_B op) /\
       garr8 segs (mrestrict (w_H W') mem2) (lc_F cx + 96) (TW.zs (b2_body1 mac)) /\
       (forall r, In r [19; 20; 21; 24; 25] -> YK11.getr regs2 (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)) /\
       (if z then YK11.getr regs2 22 = w64 0 /\ YK11.getr regs2 27 = w64 0
        else forall r, In r [22; 27] -> YK11.getr regs2 (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r))).
Proof.
intros cx op z ly S W regs mem md e mac HP HB HL HTW HZ R25 Hz Hmac.
pose proof (lp_laws _ _ _ _ _ HP) as LAWS.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned _ _ _ _ _ HP)) as HGX.
pose proof HL as (HC & HFR & HSP & HFSH & HOK & He & HMT & R19).
pose proof (lc_geom B MT XL RLO RHI cx ly S W regs mem md e HB HC) as GEO.
destruct GEO as [HAR Hsp0al Hstk Hsp1c HFaddr HFin Hn HINg HLIVE].
pose proof HC as (HJ & Hfrs & HlyF & HPERM & Rsp & R8 & R9 & Rgp & Rtp & Hsp1 & Hsp1al & HSAV & HF4096 & HFal &
  HFceil & HFpres & HFL & HIN).
pose proof asan_consts as (CC1 & CC2 & CC3 & CC4 & CC5).
assert (HSPv : forall o v, In (o, v) (lf_spill_loop (lc_F cx)) ->
  val_mem segs (mrestrict (w_H W) mem) (lc_sp1 cx + o) 8 v).
{ intros o v Hin. unfold lc_spills in HSP. rewrite Forall_forall in HSP. apply YE2y.val_mem_of_rdword. exact (HSP _ Hin). }
pose proof (HSPv 72 (2 ^ 64 - 1 - (lc_F cx + 96)) ltac:(unfold lf_spill_loop; apply in_or_app; right; cbn; tauto))
  as VS72.
destruct Hstk as (Hceil & Hslo & Hshi & H47).
unfold LLVMF_STK, LF_FRAME, LF_FBYTES in *.
destruct b2_base as (HBASE & HTT).
pose proof (@paj_run_x (l_fx cx) rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B
  HGX 0 []) as RUN.
pose proof (@paj_run_to_x (l_fx cx) rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
  TG.G_HARNESS_B HGX 0 []) as RUNTO.
set (E0 := b2_E regs 0 0 0 0 (2 ^ 64 - 1 - (lc_F cx + 96))).
assert (HEI : img_env VAL A_LIM E0) by apply b2_env_img.
assert (SHOK : sh_ok segs (SLit 0) [] E0 (mrestrict (w_H W) mem)) by constructor.
assert (EE0 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E0 n = YK11.getr regs r)
  by (intros; apply b2_ew_reg; assumption).
assert (VHOST : VAL (A_OBJ 6) = TRANS_HOST) by (vm_compute; reflexivity).
assert (VOTHER : VAL (A_OBJ 18) = TRANS_OTHER) by (vm_compute; reflexivity).
(* after a read-only run to the call of memcpy *)
assert (CALL : forall regsT memT md1 k x (src : list byte),
  b2_J B cx ly S W memT md1 e ->
  (forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 24; 25; 26] -> YK11.getr regsT (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)) ->
  (if z then YK11.getr regsT 22 = w64 0 /\ YK11.getr regsT 27 = w64 0
   else forall r, In r [22; 27] -> YK11.getr regsT (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)) ->
  (forall a, 0 <= a < 2 ^ 64 -> av W memT a = av W mem a) ->
  (forall a, apresent (w_H W) mem a -> apresent (w_H W) memT a) ->
  (x, src) = (TRANS_HOST, TC.HOST) \/ (x, src) = (TRANS_OTHER, TC.OTHER) -> 0 <= k <= 28 ->
  b2_body1 mac = b2_body k src ->
  YK11.getr regsT 10 = w64 (lc_F cx + 96 + k) -> YK11.getr regsT 11 = w64 x -> YK11.getr regsT 12 = w64 6 ->
  YK11.getr regsT 1 = Z_to_bv 64 (BASE + LO_ANN) ->
  SRr segs W (mkCfg (@YK11.mkst (l_fx cx) regsT (Z_to_bv 64 (b2_ipc OCpy)) memT (YK11.seg_rom segs)) md1)
    (fun W' c' => exists regs2 mem2 md2, c' = lc_cfg cx LO_ANN regs2 mem2 md2 /\
       @lc_lcore rc B MT cx op false true (lo_k op) ly S W' regs2 mem2 md2 e /\ lc_tw W' mem2 (lo_B op) /\
       garr8 segs (mrestrict (w_H W') mem2) (lc_F cx + 96) (TW.zs (b2_body1 mac)) /\
       (forall r, In r [19; 20; 21; 24; 25] -> YK11.getr regs2 (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)) /\
       (if z then YK11.getr regs2 22 = w64 0 /\ YK11.getr regs2 27 = w64 0
        else forall r, In r [22; 27] -> YK11.getr regs2 (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)))).
{ intros regsT memT md1 k x src HJ1 KR KZ KM KP Hx Hk Hb R10 R11 R12 R1.
  destruct (b2_move B MT XL RLO RHI cx op false true true (lo_k op) ly S W regs mem md e regsT memT md1 0 LAWS HGX HB HL
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
  { exact (b2_cpy K1 K2 cx op ly S W regsT memT md1 e k x src HP HB HL1 HTW1 HZ1 Hx Hk R10 R11 R12 R1). }
  intros W2 c2 _ (regs2 & mem2 & md2 & -> & HL2 & HTW2 & HG2 & HPR).
  exists regs2, mem2, md2. split; [reflexivity|]. split; [exact HL2|]. split; [exact HTW2|].
  split; [rewrite Hb; exact HG2|]. split.
  { intros r Hr. rewrite (HPR r ltac:(unfold acallee_saved; cbn [In] in Hr; lia)). apply KR. cbn [In] in Hr |- *. tauto. }
  destruct z.
  - destruct KZ as (K22 & K27).
    split; [exact (eq_trans (HPR 22 ltac:(unfold acallee_saved; lia)) K22) |
            exact (eq_trans (HPR 27 ltac:(unfold acallee_saved; lia)) K27)].
  - intros r Hr. rewrite (HPR r ltac:(unfold acallee_saved; cbn [In] in Hr; lia)). apply KZ. exact Hr. }
assert (H23 : forall lo hi, (if z then True else lo <= mac <= hi) -> (z = true -> lo = 0 /\ hi = 2 ^ 64 - 1) ->
  lo <= bv_unsigned (YK11.getr regs 23) <= hi).
{ intros lo hi Hlh Hzl. destruct z.
  - destruct (Hzl eq_refl) as (-> & ->). pose proof (u64_range (YK11.getr regs 23)). unfold M64 in *. lia.
  - cbn in Hz. rewrite Hz. rewrite unsigned_lit_small by lia. exact Hlh. }
assert (EV : forall regsT, (forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 24; 25; 26] ->
  YK11.getr regsT (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)) -> True) by (intros; exact I).
destruct z.
- (* +0xaa0: s11 = s6 = s7 = 0, a0 = s9, a1 = HOST, a2 = 6, memcpy *)
  cbn in Hz. subst mac.
  pose proof (@b2_entryT (l_fx cx) rc W regs mem 0xaa0 0 (2 ^ 64 - 1) (lc_F cx) (lc_sp1 cx) R25 R9
    (H23 0 (2 ^ 64 - 1) I (fun _ => conj eq_refl eq_refl)) ltac:(lia) ltac:(unfold B2_PHI; lia) ltac:(lia) ltac:(lia)
    VS72) as HS. fold E0 in HS.
  unfold lc_cfg, b2_retB. change (w64 (transportb_text + 0xaa0)) with (Z_to_bv 64 (BASE + 0xaa0)).
  paj_run_tok RUN HS HJ SHOK (0, 0).
  { b2_awr_ro. }
  b2_after.
  lazymatch type of HS with context [restrict _ ?m] => rename m into ms1 end.
  lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => rename m into md1 end.
  assert (KV : forall a, 0 <= a < 2 ^ 64 -> av W mem a = av W mem a) by (intros; reflexivity).
  assert (GP : forall a, apresent (w_H W) mem a -> apresent (w_H W) mem a) by (intros a Ha; exact Ha).
  b2_step W KV GP.
  b2_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + LO_ANN)) G1 ltac:(apply codeptr_val; exact HEI).
  b2_reg HS (Z_to_bv 5 10) (w64 (lc_F cx + 96 + 0)) G10
    ltac:(rewrite Z.add_0_r; apply b2_denot_off; [rewrite (EE0 25%nat 25%bv eq_refl); exact R25 | lia]).
  b2_reg HS (Z_to_bv 5 11) (w64 TRANS_HOST) G11 ltac:(rewrite <- VHOST; apply b2_denot_img; [exact HEI | cbv; lia]).
  b2_reg HS (Z_to_bv 5 12) (w64 6) G12 ltac:(reflexivity).
  b2_reg HS (Z_to_bv 5 22) (w64 0) G22 ltac:(reflexivity).
  b2_reg HS (Z_to_bv 5 27) (w64 0) G27 ltac:(reflexivity).
  b2_kreg HS EE0 regs 2%nat 2 GK2. b2_kreg HS EE0 regs 3%nat 3 GK3. b2_kreg HS EE0 regs 4%nat 4 GK4.
  b2_kreg HS EE0 regs 8%nat 8 GK8. b2_kreg HS EE0 regs 9%nat 9 GK9. b2_kreg HS EE0 regs 18%nat 18 GK18.
  b2_kreg HS EE0 regs 19%nat 19 GK19. b2_kreg HS EE0 regs 20%nat 20 GK20. b2_kreg HS EE0 regs 21%nat 21 GK21.
  b2_kreg HS EE0 regs 24%nat 24 GK24. b2_kreg HS EE0 regs 25%nat 25 GK25. b2_kreg HS EE0 regs 26%nat 26 GK26.
  assert (GK : forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 24; 25; 26] ->
    YK11.getr (ms_regs ms1) (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)).
  { intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<- | Hr]; [assumption |]). destruct Hr. }
  pmkst HS.
  apply (CALL (ms_regs ms1) (ms_mem ms1) md1 0 TRANS_HOST TC.HOST HJ GK (conj G22 G27) KV GP
    ltac:(left; reflexivity) ltac:(lia) ltac:(reflexivity) G10 G11 G12 G1).
- cbn in Hz.
  assert (Hmc : (0 <= mac <= 9) \/ (10 <= mac <= 12) \/ (13 <= mac <= 15)) by lia.
  destruct Hmc as [Hm | [Hm | Hm]].
  + (* mac < 10: a0 = s9 + s7, a1 = HOST *)
    pose proof (@b2_entryT (l_fx cx) rc W regs mem 0xda8 0 9 (lc_F cx) (lc_sp1 cx) R25 R9
      (H23 0 9 Hm (fun H => ltac:(discriminate H))) ltac:(lia) ltac:(unfold B2_PHI; lia) ltac:(lia) ltac:(lia)
      VS72) as HS. fold E0 in HS.
    unfold lc_cfg, b2_retB. change (w64 (transportb_text + 0xda8)) with (Z_to_bv 64 (BASE + 0xda8)).
    paj_run_tok RUN HS HJ SHOK (0, 0).
    { b2_awr_ro. }
    b2_after.
    lazymatch type of HS with context [restrict _ ?m] => rename m into ms1 end.
    lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => rename m into md1 end.
    assert (KV : forall a, 0 <= a < 2 ^ 64 -> av W mem a = av W mem a) by (intros; reflexivity).
    assert (GP : forall a, apresent (w_H W) mem a -> apresent (w_H W) mem a) by (intros a Ha; exact Ha).
    b2_step W KV GP.
    b2_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + LO_ANN)) G1 ltac:(apply codeptr_val; exact HEI).
    b2_reg HS (Z_to_bv 5 10) (w64 (lc_F cx + 96 + mac)) G10
      ltac:(replace (lc_F cx + 96 + mac) with (mac + 0 + (lc_F cx + 96)) by lia;
            apply b2_denot_add; [rewrite (EE0 23%nat 23%bv eq_refl); exact Hz | rewrite (EE0 25%nat 25%bv eq_refl); exact R25
                                 | lia | lia | lia | lia]).
    b2_reg HS (Z_to_bv 5 11) (w64 TRANS_HOST) G11 ltac:(rewrite <- VHOST; apply b2_denot_img; [exact HEI | cbv; lia]).
    b2_reg HS (Z_to_bv 5 12) (w64 6) G12 ltac:(reflexivity).
    b2_kreg HS EE0 regs 2%nat 2 GK2. b2_kreg HS EE0 regs 3%nat 3 GK3. b2_kreg HS EE0 regs 4%nat 4 GK4.
    b2_kreg HS EE0 regs 8%nat 8 GK8. b2_kreg HS EE0 regs 9%nat 9 GK9. b2_kreg HS EE0 regs 18%nat 18 GK18.
    b2_kreg HS EE0 regs 19%nat 19 GK19. b2_kreg HS EE0 regs 20%nat 20 GK20. b2_kreg HS EE0 regs 21%nat 21 GK21.
    b2_kreg HS EE0 regs 24%nat 24 GK24. b2_kreg HS EE0 regs 25%nat 25 GK25. b2_kreg HS EE0 regs 26%nat 26 GK26.
    b2_kreg HS EE0 regs 22%nat 22 GZ22. b2_kreg HS EE0 regs 27%nat 27 GZ27.
    assert (GK : forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 24; 25; 26] ->
      YK11.getr (ms_regs ms1) (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)).
    { intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<- | Hr]; [assumption |]). destruct Hr. }
    assert (GZ : forall r, In r [22; 27] -> YK11.getr (ms_regs ms1) (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)).
    { intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<- | Hr]; [assumption |]). destruct Hr. }
    pmkst HS.
    apply (CALL (ms_regs ms1) (ms_mem ms1) md1 mac TRANS_HOST TC.HOST HJ GK GZ KV GP
      ltac:(left; reflexivity) ltac:(lia)
      ltac:(unfold b2_body1; destruct (Z.ltb_spec mac 10); [reflexivity | lia]) G10 G11 G12 G1).
  + (* 10 <= mac <= 12: a0 = s7 - 10 + s9, a1 = OTHER *)
    pose proof (@b2_entryT (l_fx cx) rc W regs mem 0xda8 10 12 (lc_F cx) (lc_sp1 cx) R25 R9
      (H23 10 12 Hm (fun H => ltac:(discriminate H))) ltac:(lia) ltac:(unfold B2_PHI; lia) ltac:(lia) ltac:(lia)
      VS72) as HS. fold E0 in HS.
    unfold lc_cfg, b2_retB. change (w64 (transportb_text + 0xda8)) with (Z_to_bv 64 (BASE + 0xda8)).
    paj_run_tok RUN HS HJ SHOK (0, 0).
    { b2_awr_ro. }
    b2_after.
    lazymatch type of HS with context [restrict _ ?m] => rename m into ms1 end.
    lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => rename m into md1 end.
    assert (KV : forall a, 0 <= a < 2 ^ 64 -> av W mem a = av W mem a) by (intros; reflexivity).
    assert (GP : forall a, apresent (w_H W) mem a -> apresent (w_H W) mem a) by (intros a Ha; exact Ha).
    b2_step W KV GP.
    b2_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + LO_ANN)) G1 ltac:(apply codeptr_val; exact HEI).
    b2_reg HS (Z_to_bv 5 10) (w64 (lc_F cx + 96 + (mac - 10))) G10
      ltac:(replace (lc_F cx + 96 + (mac - 10)) with (mac + (-10) + (lc_F cx + 96)) by lia;
            apply b2_denot_add; [rewrite (EE0 23%nat 23%bv eq_refl); exact Hz | rewrite (EE0 25%nat 25%bv eq_refl); exact R25
                                 | lia | lia | lia | lia]).
    b2_reg HS (Z_to_bv 5 11) (w64 TRANS_OTHER) G11 ltac:(rewrite <- VOTHER; apply b2_denot_img; [exact HEI | cbv; lia]).
    b2_reg HS (Z_to_bv 5 12) (w64 6) G12 ltac:(reflexivity).
    b2_kreg HS EE0 regs 2%nat 2 GK2. b2_kreg HS EE0 regs 3%nat 3 GK3. b2_kreg HS EE0 regs 4%nat 4 GK4.
    b2_kreg HS EE0 regs 8%nat 8 GK8. b2_kreg HS EE0 regs 9%nat 9 GK9. b2_kreg HS EE0 regs 18%nat 18 GK18.
    b2_kreg HS EE0 regs 19%nat 19 GK19. b2_kreg HS EE0 regs 20%nat 20 GK20. b2_kreg HS EE0 regs 21%nat 21 GK21.
    b2_kreg HS EE0 regs 24%nat 24 GK24. b2_kreg HS EE0 regs 25%nat 25 GK25. b2_kreg HS EE0 regs 26%nat 26 GK26.
    b2_kreg HS EE0 regs 22%nat 22 GZ22. b2_kreg HS EE0 regs 27%nat 27 GZ27.
    assert (GK : forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 24; 25; 26] ->
      YK11.getr (ms_regs ms1) (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)).
    { intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<- | Hr]; [assumption |]). destruct Hr. }
    assert (GZ : forall r, In r [22; 27] -> YK11.getr (ms_regs ms1) (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)).
    { intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<- | Hr]; [assumption |]). destruct Hr. }
    pmkst HS.
    apply (CALL (ms_regs ms1) (ms_mem ms1) md1 (mac - 10) TRANS_OTHER TC.OTHER HJ GK GZ KV GP
      ltac:(right; reflexivity) ltac:(lia)
      ltac:(unfold b2_body1; destruct (Z.ltb_spec mac 10); [lia|]; destruct (Z.ltb_spec mac 13); [reflexivity | lia])
      G10 G11 G12 G1).
  + (* mac >= 13: to ANN, no copy *)
    pose proof (@b2_entryT (l_fx cx) rc W regs mem 0xda8 13 15 (lc_F cx) (lc_sp1 cx) R25 R9
      (H23 13 15 Hm (fun H => ltac:(discriminate H))) ltac:(lia) ltac:(unfold B2_PHI; lia) ltac:(lia) ltac:(lia)
      VS72) as HS. fold E0 in HS.
    unfold lc_cfg, b2_retB. change (w64 (transportb_text + 0xda8)) with (Z_to_bv 64 (BASE + 0xda8)).
    paj_run_to_tok RUNTO HS HJ SHOK (0, 0) 0xdcc.
    { b2_awr_ro. }
    b2_after.
    lazymatch type of HS with context [restrict _ ?m] => rename m into ms1 end.
    lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => rename m into md1 end.
    assert (KV : forall a, 0 <= a < 2 ^ 64 -> av W mem a = av W mem a) by (intros; reflexivity).
    assert (GP : forall a, apresent (w_H W) mem a -> apresent (w_H W) mem a) by (intros a Ha; exact Ha).
    b2_step W KV GP.
    b2_kreg HS EE0 regs 2%nat 2 GK2. b2_kreg HS EE0 regs 3%nat 3 GK3. b2_kreg HS EE0 regs 4%nat 4 GK4.
    b2_kreg HS EE0 regs 8%nat 8 GK8. b2_kreg HS EE0 regs 9%nat 9 GK9. b2_kreg HS EE0 regs 18%nat 18 GK18.
    b2_kreg HS EE0 regs 19%nat 19 GK19. b2_kreg HS EE0 regs 20%nat 20 GK20. b2_kreg HS EE0 regs 21%nat 21 GK21.
    b2_kreg HS EE0 regs 22%nat 22 GK22. b2_kreg HS EE0 regs 24%nat 24 GK24. b2_kreg HS EE0 regs 25%nat 25 GK25.
    b2_kreg HS EE0 regs 26%nat 26 GK26. b2_kreg HS EE0 regs 27%nat 27 GK27.
    pmkst HS.
    apply SRr_ret.
    destruct (b2_move B MT XL RLO RHI cx op false true true (lo_k op) ly S W regs mem md e (ms_regs ms1) (ms_mem ms1) md1 0
      LAWS HGX HB HL HTW HJ) as [HL1 HTW1].
    { intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<- | Hr]; [assumption |]). destruct Hr. }
    { unfold LLVMF_STK. lia. }
    { intros a Ha _. exact (KV a Ha). }
    { exact GP. }
    { intros i Hi. rewrite (KV (lc_SH cx + i) ltac:(pose proof (Z.div_pos (lc_F cx) 8 ltac:(lia) ltac:(lia));
        unfold lc_SH, SHADOW_OFF; lia)). exact (HFSH i Hi). }
    exists (ms_regs ms1), (ms_mem ms1), md1. split.
    { unfold lc_cfg, w64, LO_ANN. rewrite HBASE, HTT. reflexivity. }
    split; [exact HL1|]. split; [exact HTW1|]. split.
    { replace (TW.zs (b2_body1 mac)) with (repeat 0 34)
        by (unfold b2_body1; destruct (Z.ltb_spec mac 10); [lia|]; destruct (Z.ltb_spec mac 13); [lia|]; reflexivity).
      apply (lc_garr8_kept (w_H W) (w_H W) mem (ms_mem ms1) (lc_F cx + 96) _); [|exact HZ].
      intros j Hj. rewrite repeat_length in Hj. apply KV. lia. }
    split.
    { intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<- | Hr]; [assumption |]). destruct Hr. }
    intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<- | Hr]; [assumption |]). destruct Hr.
Qed.

(* From +0xa74 (z = true) or +0xd78 (z = false) to ANN: b2_setB, then b2_tail. *)
Lemma b2_rest (K1 : lc_rom_view_stmt B MT XL RLO RHI) (K2 : lc_src_ro_stmt B MT XL RLO RHI) :
  forall cx op (z : bool) ly S (W : world segs) regs mem md e,
  @lp_prem rc B MT XL RLO RHI -> @lc_base rc B MT XL RLO RHI cx ->
  @lc_lcore rc B MT cx op false false (lo_k op) ly S W regs mem md e -> lc_tw W mem (lo_B op) ->
  lc_opc (l_pl cx) (lo_c op) = 2 ->
  let av := lc_ann_vals (l_pl cx) (lc_oc (l_pl cx) (lo_c op)) in
  YK11.getr regs 21 = w64 (av_sel av) -> YK11.getr regs 20 = w64 (lc_F cx + 32) ->
  (if z then av_mac av = 0 /\ av_nm av = 0 /\ YK11.getr regs 24 = w64 (l_p cx + TOP.fi_off (av_c av)) /\
             TOP.fi_n (av_c av) = 0
   else Z.land (bv_unsigned (YK11.getr regs 10)) 15 = av_mac av /\ YK11.getr regs 22 = w64 (av_nm av mod 3) /\
        lc_cur cx regs 24 27 (av_c av)) ->
  0 <= av_mac av < 16 ->
  av_body1 av = b2_body1 (av_mac av) ->
  SRr segs W (mkCfg (@YK11.mkst (l_fx cx) regs (Z_to_bv 64 (BASE + if z then 0xa74 else 0xd78)) mem (YK11.seg_rom segs)) md)
    (@lc_st_ann rc B MT cx op).
Proof.
intros cx op z ly S W regs mem md e HP HB HL HTW Hopc av R21 R20 Hz Hmac Hbody.
destruct b2_base as (HBASE & HTT).
replace (mkCfg (@YK11.mkst (l_fx cx) regs (Z_to_bv 64 (BASE + if z then 0xa74 else 0xd78)) mem (YK11.seg_rom segs)) md)
  with (lc_cfg cx (if z then 0xa74 else 0xd78) regs mem md) by (unfold lc_cfg, w64; rewrite HBASE, HTT; reflexivity).
eapply SRr_bind; [exact (b2_setB K2 cx op z ly S W regs mem md e HP HB HL HTW)|].
intros W1 c1 _ (regs1 & mem1 & md1 & -> & HL1 & HTW1 & HZ1 & K1r & R25 & R23).
eapply SRr_bind.
{ apply (b2_tail K1 K2 cx op z ly S W1 regs1 mem1 md1 e (av_mac av) HP HB HL1 HTW1 HZ1 R25).
  - destruct z.
    + exact (proj1 Hz).
    + rewrite (R23 eq_refl). f_equal. exact (proj1 Hz).
  - exact Hmac. }
intros W2 c2 _ (regs2 & mem2 & md2 & -> & HL2 & HTW2 & HZ2 & K2r & KZ).
apply SRr_ret.
exists ly, S, regs2, mem2, md2, e. cbv zeta. fold av.
split; [reflexivity|]. split; [exact Hopc|]. split; [exact HL2|]. split; [exact HTW2|].
split; [rewrite Hbody; exact HZ2|].
assert (E21 : YK11.getr regs2 (Z_to_bv 5 21) = YK11.getr regs (Z_to_bv 5 21))
  by exact (eq_trans (K2r 21 ltac:(cbn; tauto)) (K1r 21 ltac:(cbn; tauto))).
assert (E20 : YK11.getr regs2 (Z_to_bv 5 20) = YK11.getr regs (Z_to_bv 5 20))
  by exact (eq_trans (K2r 20 ltac:(cbn; tauto)) (K1r 20 ltac:(cbn; tauto))).
assert (E24 : YK11.getr regs2 (Z_to_bv 5 24) = YK11.getr regs (Z_to_bv 5 24))
  by exact (eq_trans (K2r 24 ltac:(cbn; tauto)) (K1r 24 ltac:(cbn; tauto))).
assert (E25 : YK11.getr regs2 (Z_to_bv 5 25) = YK11.getr regs1 (Z_to_bv 5 25)) by exact (K2r 25 ltac:(cbn; tauto)).
split; [exact (eq_trans E21 R21)|].
destruct z.
- destruct KZ as (K22 & K27). destruct Hz as (Hm & Hn & H24 & Hc).
  split; [refine (eq_trans K22 _); rewrite Hn; reflexivity|].
  split; [exact (eq_trans E25 R25)|].
  split; [split; [exact (eq_trans E24 H24) | refine (eq_trans K27 _); rewrite Hc; reflexivity]|].
  exact (eq_trans E20 R20).
- destruct Hz as (Hm & H22 & H24 & H27).
  assert (E22 : YK11.getr regs2 (Z_to_bv 5 22) = YK11.getr regs (Z_to_bv 5 22))
    by exact (eq_trans (KZ 22 ltac:(cbn; tauto)) (K1r 22 ltac:(cbn; tauto))).
  assert (E27 : YK11.getr regs2 (Z_to_bv 5 27) = YK11.getr regs (Z_to_bv 5 27))
    by exact (eq_trans (KZ 27 ltac:(cbn; tauto)) (K1r 27 ltac:(cbn; tauto))).
  split; [exact (eq_trans E22 H22)|].
  split; [exact (eq_trans E25 R25)|].
  split; [split; [exact (eq_trans E24 H24) | exact (eq_trans E27 H27)]|].
  exact (eq_trans E20 R20).
Qed.

(* An input byte at offset j: its value (the model's byte), its shadow byte (the block's shadow: 0, or above j's
   offset in its granule), the block's bounds, the byte apart from its own shadow byte, and outside the image. *)
Lemma b2_inb : forall cx ly S (W : world segs) regs mem md e j,
  AR_laws segs B -> @lc_base rc B MT XL RLO RHI cx -> @lc_core rc B cx ly S W regs mem md e ->
  0 <= j < l_n cx ->
  val_mem segs (mrestrict (w_H W) mem) (l_p cx + j) 1 (DSpec.at8 (l_pl cx) (Z.to_nat j)) /\
  0 <= DSpec.at8 (l_pl cx) (Z.to_nat j) < 256 /\
  (exists s, av W mem (SHADOW_OFF + (l_p cx + j) / 8) = Some s /\ saddr_ok (l_p cx + j) s) /\
  4096 <= l_p cx /\ l_p cx + l_n cx <= B2_PHI /\
  (l_p cx + j + 1 <= SHADOW_OFF + (l_p cx + j) / 8 \/ SHADOW_OFF + (l_p cx + j) / 8 + 1 <= l_p cx + j) /\
  ~ in_img segs (l_p cx + j).
Proof.
intros cx ly S W regs mem md e j LAWS HB HC Hj.
pose proof (lc_geom B MT XL RLO RHI cx ly S W regs mem md e HB HC) as GEO.
destruct GEO as [HAR Hsp0al Hstk Hsp1c HFaddr HFin Hn HINg HLIVE].
pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HIN).
destruct HIN as (HPAYg & _).
destruct Hn as (Hn1 & Hnl).
pose proof (HINg ltac:(lia)) as InP.
destruct (al_blocks _ _ LAWS ly S W mem md (l_p cx) (l_n cx) HAR InP) as (_ & Hb4 & Hbc & Hbapp & _).
pose proof (req_size_pos (l_n cx) ltac:(lia)) as (Hq1 & Hq2).
pose proof asan_consts as ((CVlo & CVhi) & C2 & C3 & C4 & C5).
assert (Hjl : (Z.to_nat j < length (map (fun b : byte => bv_unsigned b) (l_pl cx)))%nat) by (rewrite length_map; lia).
destruct (garr8_nthZ segs _ _ _ j HPAYg ltac:(lia) Hjl) as (Hv & Hr).
assert (EB : nth (Z.to_nat j) (map (fun b : byte => bv_unsigned b) (l_pl cx)) 0 = DSpec.at8 (l_pl cx) (Z.to_nat j)).
{ unfold DSpec.at8, DSpec.bz. rewrite <- (map_nth (fun b : byte => bv_unsigned b) (l_pl cx) (DSpec.b8 0)). reflexivity. }
rewrite EB in Hv, Hr.
pose proof (range_addressable_of_block segs B LAWS ly S W mem md (l_p cx) (l_n cx) (l_p cx + j) 1 HAR InP
  ltac:(lia) ltac:(lia)) as HRA.
destruct (HRA (l_p cx + j) ltac:(lia)) as (s & Hs & Hok). unfold shadow_of_addr in Hs.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hbapp.
split; [exact Hv|]. split; [exact Hr|]. split; [exists s; exact (conj Hs Hok)|].
split; [lia|]. split; [unfold B2_PHI; lia|]. split.
- unfold SHADOW_OFF. lia.
- exact (blk_img segs B LAWS ly S W mem md (l_p cx) (l_n cx) (l_p cx + j) HAR InP ltac:(lia)).
Qed.

(* From +0x73c (n0 >= 3, after the mac byte's shadow test): the mac byte, s8 = s9 + 3; with n0 = 3 s11 = s6 = 0 and
   `j` +0xd78; else the UBSan test of s8 + 1, the name byte's checked load (a token of the engine whose obligation is
   the input block's addressability), s6 = name mod 3 by the divisor constant, s11 = s7 - 4, s8 = s9 + 4; then from
   +0xd78 to ANN (b2_rest). *)
Lemma b2_j2 (K1 : lc_rom_view_stmt B MT XL RLO RHI) (K2 : lc_src_ro_stmt B MT XL RLO RHI) :
  forall cx op ly S (W : world segs) regs mem md e o0 n0,
  @lp_prem rc B MT XL RLO RHI -> @lc_base rc B MT XL RLO RHI cx ->
  @lc_lcore rc B MT cx op false false (lo_k op) ly S W regs mem md e -> lc_tw W mem (lo_B op) ->
  lc_opc (l_pl cx) (lo_c op) = 2 -> lo_c op = TOP.FuzzIn o0 n0 -> 3 <= n0 ->
  YK11.getr regs 20 = w64 (lc_F cx + 32) -> YK11.getr regs 21 = w64 (DSpec.at8 (l_pl cx) (Z.to_nat (o0 + 1))) ->
  YK11.getr regs 22 = w64 1 -> YK11.getr regs 23 = w64 n0 -> YK11.getr regs 24 = w64 (l_p cx + o0 + 2) ->
  YK11.getr regs 25 = w64 (l_p cx + o0) -> YK11.getr regs 27 = w64 (n0 - 1) ->
  SRr segs W (mkCfg (@YK11.mkst (l_fx cx) regs (Z_to_bv 64 (BASE + 0x73c)) mem (YK11.seg_rom segs)) md)
    (@lc_st_ann rc B MT cx op).
Proof.
intros cx op ly S W regs mem md e o0 n0 HP HB HL HTW Hopc Ec Hn0 R20 R21 R22 R23 R24 R25 R27.
pose proof (lp_laws _ _ _ _ _ HP) as LAWS.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned _ _ _ _ _ HP)) as HGX.
pose proof HL as (HC & (R18 & R26) & HSP & HFSH & HOK & He & HMT & R19).
pose proof HOK as (HAG & Hops & Hfin & Hfn & Hk).
rewrite Ec in Hfin. destruct Hfin as (Hfo & Hfn' & Hfl). cbn [TOP.fi_off TOP.fi_n] in Hfo, Hfn', Hfl.
pose proof (lc_geom B MT XL RLO RHI cx ly S W regs mem md e HB HC) as GEO.
destruct GEO as [HAR Hsp0al Hstk Hsp1c HFaddr HFin Hn HINg HLIVE].
pose proof HC as (HJ & Hfrs & HlyF & HPERM & Rsp & R8 & R9 & Rgp & Rtp & Hsp1 & Hsp1al & HSAV & HF4096 & HFal &
  HFceil & HFpres & HFL & HIN).
destruct Hn as (Hn1 & Hnl).
pose proof asan_consts as (CC1 & CC2 & CC3 & CC4 & CC5).
pose proof (HINg ltac:(lia)) as InP.
set (D := l_pl cx) in *.
set (q := l_p cx + o0) in *.
assert (Ec1 : lc_oc D (TOP.FuzzIn o0 n0) = TOP.FuzzIn (o0 + 1) (n0 - 1)).
{ unfold lc_oc, TOP.fuzz_u8_m. cbn [TOP.fi_n TOP.fi_off]. destruct (Z.eqb_spec n0 0); [lia|reflexivity]. }
destruct (b2_inb cx ly S W regs mem md e (o0 + 2) LAWS HB HC ltac:(lia)) as (V2 & B2r & _ & Hp4096 & HpPHI & _ & Himg2).
replace (l_p cx + (o0 + 2)) with (q + 2) in V2, Himg2 by (unfold q; lia).
change (l_pl cx) with D in V2, B2r.
set (b2 := DSpec.at8 D (Z.to_nat (o0 + 2))) in *.
pose proof (K1 HP cx ly S W regs mem md e HB HC) as HROM.
pose proof (@paj_run_to_x (l_fx cx) rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
  TG.G_HARNESS_B HGX 0 []) as RUNTO.
pose proof (b2_vals D (TOP.FuzzIn (o0 + 1) (n0 - 1)) ltac:(cbn; lia)) as AV. cbv zeta in AV.
cbn [TOP.fi_off TOP.fi_n] in AV.
destruct AV as (AS & AM & AN & AC & AB).
rewrite <- Ec1, <- Ec in AS, AM, AN, AC, AB.
set (avv := lc_ann_vals D (lc_oc D (lo_c op))) in AS, AM, AN, AC, AB.
b2_ifs AS. b2_ifs AM.
assert (KVS : forall i, 0 <= i < 32 -> 0 <= lc_SH cx + i < 2 ^ 64).
{ intros i Hi. pose proof (Z.div_pos (lc_F cx) 8 ltac:(lia) ltac:(lia)). unfold LF_FBYTES in HFceil.
  unfold lc_SH, SHADOW_OFF. lia. }
assert (Hc3 : n0 = 3 \/ 4 <= n0) by lia.
destruct Hc3 as [Hn3 | Hn4].
- (* n0 = 3: no name byte *)
  b2_ifs AN. b2_ifs AC.
  pose proof (@b2_entryJ (l_fx cx) rc W regs mem q n0 b2 0 true R22 R23 R24 R25 R26 ltac:(unfold q; lia)
    ltac:(unfold B2_PHI in *; unfold q; lia) Hn3 V2 (fun H => ltac:(discriminate H)) (fun H => ltac:(discriminate H))
    (fun H => ltac:(discriminate H)) B2r ltac:(lia)) as HS.
  assert (R23z : YK11.getr regs 23 = Z_to_bv 64 3) by (rewrite R23, Hn3; reflexivity).
  pose proof (st_ok_pi_pin_reg' _ _ _ (23%bv) 3 HS R23z eq_refl) as HSq. clear HS. rename HSq into HS.
  set (E0 := b2_E regs 0 b2 0 0 0) in *.
  assert (HEI : img_env VAL A_LIM E0) by apply b2_env_img.
  assert (SHOK : sh_ok segs B2_Bx [] E0 (mrestrict (w_H W) mem)) by constructor.
  assert (EE0 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E0 n = YK11.getr regs r)
    by (intros; apply b2_ew_reg; assumption).
  paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan 0xd78.
  all: try (b2_awr_ro; fail).
  b2_after.
  lazymatch type of HS with context [restrict _ ?m] => rename m into ms1 end.
  lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => rename m into md1 end.
  assert (KV : forall a, 0 <= a < 2 ^ 64 -> av W mem a = av W mem a) by (intros; reflexivity).
  assert (GP : forall a, apresent (w_H W) mem a -> apresent (w_H W) mem a) by (intros a Ha; exact Ha).
  b2_step W KV GP.
  b2_reg HS (Z_to_bv 5 10) (w64 b2) G10
    ltac:(apply b2_denot_off; [exact (b2_ew_x regs 0 b2 0 0 0 1 ltac:(lia)) | exact (b2_rng _ B2r)]).
  b2_reg HS (Z_to_bv 5 22) (w64 0) G22 ltac:(reflexivity).
  b2_reg HS (Z_to_bv 5 27) (w64 0) G27 ltac:(reflexivity).
  b2_reg HS (Z_to_bv 5 24) (w64 (q + 3)) G24
    ltac:(rewrite denot_lit_U, (U_atom_off _ 25 q 3)
      by (first [b2_agx; rewrite (EE0 25%nat 25%bv eq_refl); exact R25 | unfold B2_PHI in *; unfold q in *; lia]);
          reflexivity).
  b2_kreg HS EE0 regs 2%nat 2 GK2. b2_kreg HS EE0 regs 3%nat 3 GK3. b2_kreg HS EE0 regs 4%nat 4 GK4.
  b2_kreg HS EE0 regs 8%nat 8 GK8. b2_kreg HS EE0 regs 9%nat 9 GK9. b2_kreg HS EE0 regs 18%nat 18 GK18.
  b2_kreg HS EE0 regs 19%nat 19 GK19. b2_kreg HS EE0 regs 20%nat 20 GK20. b2_kreg HS EE0 regs 21%nat 21 GK21.
  b2_kreg HS EE0 regs 26%nat 26 GK26.
  pmkst HS.
  destruct (b2_move B MT XL RLO RHI cx op false false false (lo_k op) ly S W regs mem md e (ms_regs ms1) (ms_mem ms1) md1 0
    LAWS HGX HB HL HTW HJ) as [HL1 HTW1].
  { intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<- | Hr]; [assumption |]). destruct Hr. }
  { unfold LLVMF_STK. lia. }
  { intros a Ha _. exact (KV a Ha). }
  { exact GP. }
  { intros i Hi. rewrite (KV (lc_SH cx + i) (KVS i Hi)). exact (HFSH i Hi). }
  change (Z_to_bv 64 (BASE + 0xd78)) with (Z_to_bv 64 (BASE + if false then 0xa74 else 0xd78)).
  apply (b2_rest K1 K2 cx op false ly S W (ms_regs ms1) (ms_mem ms1) md1 e HP HB HL1 HTW1 Hopc).
  all: cbv zeta; fold D; fold avv.
  + rewrite AS. exact (eq_trans GK21 R21).
  + exact (eq_trans GK20 R20).
  + rewrite AM, AN, AC. cbn [TOP.fi_off TOP.fi_n].
    split; [lazymatch goal with |- context [bv_unsigned (YK11.getr (ms_regs ms1) ?r)] =>
              rewrite (G10 : YK11.getr (ms_regs ms1) r = w64 b2) end; rewrite unsigned_lit_small by lia;
            change 15 with (Z.ones 4); rewrite Z.land_ones by lia; unfold b2; do 3 f_equal; lia|].
    split; [exact G22|].
    split; [refine (eq_trans G24 _); unfold w64, q; f_equal; cbn; lia
           | refine (eq_trans G27 _); unfold w64; f_equal; cbn; lia].
  + rewrite AM. apply Z.mod_pos_bound. lia.
  + rewrite AB. reflexivity.
- (* n0 >= 4: the name byte *)
  b2_ifs AN. b2_ifs AC.
  destruct (b2_inb cx ly S W regs mem md e (o0 + 3) LAWS HB HC ltac:(lia)) as (V3 & B3r & _ & _ & _ & _ & Himg3).
  replace (l_p cx + (o0 + 3)) with (q + 3) in V3, Himg3 by (unfold q; lia).
  change (l_pl cx) with D in V3, B3r.
  set (b3 := DSpec.at8 D (Z.to_nat (o0 + 3))) in *.
  pose proof (b2_kval W mem HROM) as VK.
  assert (HKimg : forall a, TRANS_K_LLVMF <= a < TRANS_K_LLVMF + 8 -> in_img segs a).
  { intros a Ha. apply trans_ro_img. unfold trans_in_ro_rd. apply Exists_exists. exists (TRANS_K_LLVMF, 8).
    split; [unfold TRANS_RO_RD; cbn [In app]; b2_in | unfold in_zr; cbn [fst snd]; lia]. }
  assert (Hdk : q + 4 <= TRANS_K_LLVMF \/ TRANS_K_LLVMF + 8 <= q + 2).
  { destruct (Z_le_gt_dec (q + 4) TRANS_K_LLVMF) as [Hk1 | Hk1]; [left; exact Hk1|].
    destruct (Z_le_gt_dec (TRANS_K_LLVMF + 8) (q + 2)) as [Hk2 | Hk2]; [right; exact Hk2|].
    exfalso. destruct (Z_le_gt_dec TRANS_K_LLVMF (q + 2)) as [Hk3 | Hk3].
    - exact (Himg2 (HKimg (q + 2) ltac:(lia))).
    - exact (Himg3 (HKimg (q + 3) ltac:(lia))). }
  pose proof (@b2_entryJ (l_fx cx) rc W regs mem q n0 b2 b3 false R22 R23 R24 R25 R26 ltac:(unfold q; lia)
    ltac:(unfold B2_PHI in *; unfold q; lia) ltac:(cbn; lia) V2 (fun _ => V3) (fun _ => VK) (fun _ => Hdk) B2r B3r)
    as HS.
  set (E0 := b2_E regs 0 b2 b3 0 0) in *.
  assert (HEI : img_env VAL A_LIM E0) by apply b2_env_img.
  assert (SHOK : sh_ok segs B2_Bx [] E0 (mrestrict (w_H W) mem)) by constructor.
  assert (EE0 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E0 n = YK11.getr regs r)
    by (intros; apply b2_ew_reg; assumption).
  assert (UE25 : forall k, 0 <= k <= 8 -> U E0 (SOff 25 k) = q + k).
  { intros k Hk0. apply U_atom_off; [rewrite (EE0 25%nat 25%bv eq_refl); exact R25 | unfold B2_PHI in *; unfold q; lia
                                    | unfold B2_PHI in *; unfold q; lia]. }
  paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan 0xd78.
  all: try (cbn [ms_mem]; eapply (obl_of_block segs B LAWS ly S W mem md E0 (SOff 26 0) _ 1 (l_p cx) (l_n cx) HAR InP);
    [ apply U_atom; [rewrite (EE0 26%nat 26%bv eq_refl); exact R26 | unfold SHADOW_OFF; lia]
    | rewrite ?UE25 by lia; unfold q; lia
    | rewrite ?UE25 by lia; pose proof (req_size_pos (l_n cx) ltac:(lia)) as (Hq1 & Hq2); unfold q; lia ]).
  all: try (b2_awr_ro; fail).
  b2_after.
  lazymatch type of HS with context [restrict _ ?m] => rename m into ms1 end.
  lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => rename m into md1 end.
  assert (KV : forall a, 0 <= a < 2 ^ 64 -> av W mem a = av W mem a) by (intros; reflexivity).
  assert (GP : forall a, apresent (w_H W) mem a -> apresent (w_H W) mem a) by (intros a Ha; exact Ha).
  b2_step W KV GP.
  lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
    assert (AGX : forall n, (n < 240)%nat -> ew Ex n = ew E0 n)
      by (intros nn Hnn; repeat rewrite ew_ewset_other by lia; reflexivity) end.
  b2_reg HS (Z_to_bv 5 10) (w64 b2) G10
    ltac:(apply b2_denot_off; [b2_agx; exact (b2_ew_x regs 0 b2 b3 0 0 1 ltac:(lia)) | lia]).
  b2_reg HS (Z_to_bv 5 22) (w64 (b3 mod 3)) G22
    ltac:(apply b2_eM_val; [b2_agx; exact (b2_ew_x regs 0 b2 b3 0 0 2 ltac:(lia)) | lia]).
  b2_reg HS (Z_to_bv 5 24) (w64 (q + 4)) G24
    ltac:(rewrite denot_lit_U, (U_atom_off _ 25 q 4)
      by (first [b2_agx; rewrite (EE0 25%nat 25%bv eq_refl); exact R25 | unfold B2_PHI in *; unfold q in *; lia]);
          reflexivity).
  b2_reg HS (Z_to_bv 5 27) (w64 (n0 - 4)) G27
    ltac:(rewrite denot_lit_U, (U_atom_off _ 23 n0 (-4)) by (first [b2_agx; rewrite (EE0 23%nat 23%bv eq_refl); exact R23 | lia]);
          unfold w64; f_equal; lia).
  b2_kreg HS EE0 regs 2%nat 2 GK2. b2_kreg HS EE0 regs 3%nat 3 GK3. b2_kreg HS EE0 regs 4%nat 4 GK4.
  b2_kreg HS EE0 regs 8%nat 8 GK8. b2_kreg HS EE0 regs 9%nat 9 GK9. b2_kreg HS EE0 regs 18%nat 18 GK18.
  b2_kreg HS EE0 regs 19%nat 19 GK19. b2_kreg HS EE0 regs 20%nat 20 GK20. b2_kreg HS EE0 regs 21%nat 21 GK21.
  b2_kreg HS EE0 regs 26%nat 26 GK26.
  pmkst HS.
  destruct (b2_move B MT XL RLO RHI cx op false false false (lo_k op) ly S W regs mem md e (ms_regs ms1) (ms_mem ms1) md1 0
    LAWS HGX HB HL HTW HJ) as [HL1 HTW1].
  { intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<- | Hr]; [assumption |]). destruct Hr. }
  { unfold LLVMF_STK. lia. }
  { intros a Ha _. exact (KV a Ha). }
  { exact GP. }
  { intros i Hi. rewrite (KV (lc_SH cx + i) (KVS i Hi)). exact (HFSH i Hi). }
  change (Z_to_bv 64 (BASE + 0xd78)) with (Z_to_bv 64 (BASE + if false then 0xa74 else 0xd78)).
  apply (b2_rest K1 K2 cx op false ly S W (ms_regs ms1) (ms_mem ms1) md1 e HP HB HL1 HTW1 Hopc).
  all: cbv zeta; fold D; fold avv.
  + rewrite AS. exact (eq_trans GK21 R21).
  + exact (eq_trans GK20 R20).
  + rewrite AM, AN, AC. cbn [TOP.fi_off TOP.fi_n].
    split; [lazymatch goal with |- context [bv_unsigned (YK11.getr (ms_regs ms1) ?r)] =>
              rewrite (G10 : YK11.getr (ms_regs ms1) r = w64 b2) end; rewrite unsigned_lit_small by lia;
            change 15 with (Z.ones 4); rewrite Z.land_ones by lia; unfold b2; do 3 f_equal; lia|].
    split; [refine (eq_trans G22 _); unfold b3; do 4 f_equal; lia|].
    split; [refine (eq_trans G24 _); unfold w64, q; f_equal; cbn; lia
           | refine (eq_trans G27 _); unfold w64; f_equal; cbn; lia].
  + rewrite AM. apply Z.mod_pos_bound. lia.
  + rewrite AB. reflexivity.
Qed.

(* From +0x730 (n0 >= 3): the shadow byte of s8 = q + 2 and its test `beqz` (+0x734), split: 0 goes on to +0x73c;
   in (0, 8) runs the slow path +0x1730 .. +0x1738, whose `bge` to the report 0x82f54 is refuted (b2_bge) and whose
   `j` returns to +0x73c; then b2_j2. *)
Lemma b2_mac (K1 : lc_rom_view_stmt B MT XL RLO RHI) (K2 : lc_src_ro_stmt B MT XL RLO RHI) :
  forall cx op ly S (W : world segs) regs mem md e o0 n0,
  @lp_prem rc B MT XL RLO RHI -> @lc_base rc B MT XL RLO RHI cx ->
  @lc_lcore rc B MT cx op false false (lo_k op) ly S W regs mem md e -> lc_tw W mem (lo_B op) ->
  lc_opc (l_pl cx) (lo_c op) = 2 -> lo_c op = TOP.FuzzIn o0 n0 -> 3 <= n0 ->
  YK11.getr regs 11 = w64 (SHADOW_OFF + (l_p cx + o0 + 2) / 8) ->
  YK11.getr regs 20 = w64 (lc_F cx + 32) -> YK11.getr regs 21 = w64 (DSpec.at8 (l_pl cx) (Z.to_nat (o0 + 1))) ->
  YK11.getr regs 22 = w64 1 -> YK11.getr regs 23 = w64 n0 -> YK11.getr regs 24 = w64 (l_p cx + o0 + 2) ->
  YK11.getr regs 25 = w64 (l_p cx + o0) -> YK11.getr regs 27 = w64 (n0 - 1) ->
  SRr segs W (mkCfg (@YK11.mkst (l_fx cx) regs (Z_to_bv 64 (BASE + 0x730)) mem (YK11.seg_rom segs)) md)
    (@lc_st_ann rc B MT cx op).
Proof.
intros cx op ly S W regs mem md e o0 n0 HP HB HL HTW Hopc Ec Hn0 R11 R20 R21 R22 R23 R24 R25 R27.
pose proof (lp_laws _ _ _ _ _ HP) as LAWS.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned _ _ _ _ _ HP)) as HGX.
pose proof HL as (HC & (R18 & R26) & HSP & HFSH & HOK & He & HMT & R19).
pose proof HOK as (HAG & Hops & Hfin & Hfn & Hk).
rewrite Ec in Hfin. destruct Hfin as (Hfo & Hfn' & Hfl). cbn [TOP.fi_off TOP.fi_n] in Hfo, Hfn', Hfl.
pose proof (lc_geom B MT XL RLO RHI cx ly S W regs mem md e HB HC) as GEO.
destruct GEO as [HAR Hsp0al Hstk Hsp1c HFaddr HFin Hn HINg HLIVE].
pose proof HC as (HJ & Hfrs & HlyF & HPERM & Rsp & R8 & R9 & Rgp & Rtp & Hsp1 & Hsp1al & HSAV & HF4096 & HFal &
  HFceil & HFpres & HFL & HIN).
destruct Hn as (Hn1 & Hnl).
pose proof asan_consts as (CC1 & CC2 & CC3 & CC4 & CC5).
set (q := l_p cx + o0) in *.
destruct (b2_inb cx ly S W regs mem md e (o0 + 2) LAWS HB HC ltac:(lia))
  as (_ & _ & (sb & Hsb & Hok) & Hp4096 & HpPHI & _ & _).
replace (l_p cx + (o0 + 2)) with (q + 2) in Hsb, Hok by (unfold q; lia).
assert (Hsbr : 0 <= sb <= 7) by (unfold saddr_ok in Hok; pose proof (Z.mod_pos_bound (q + 2) 8 ltac:(lia)); lia).
pose proof (YE2y.val_mem1_of_aview (w_H W) mem _ _ Hsb) as VS.
assert (KVS : forall i, 0 <= i < 32 -> 0 <= lc_SH cx + i < 2 ^ 64).
{ intros i Hi. pose proof (Z.div_pos (lc_F cx) 8 ltac:(lia) ltac:(lia)). unfold LF_FBYTES in HFceil.
  unfold lc_SH, SHADOW_OFF. lia. }
pose proof (@b2_entryS2 (l_fx cx) rc W regs mem (q + 2) sb R11 ltac:(unfold B2_PHI in *; unfold q; lia) VS Hsbr) as HS.
set (E0 := b2_E regs sb 0 0 0 0) in *.
assert (HEI : img_env VAL A_LIM E0) by apply b2_env_img.
assert (SHOK : sh_ok segs (SLit 0) [] E0 (mrestrict (w_H W) mem)) by constructor.
assert (EE0 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E0 n = YK11.getr regs r)
  by (intros; apply b2_ew_reg; assumption).
assert (E32 : ew E0 32 = Z_to_bv 64 sb) by exact (b2_ew_x regs sb 0 0 0 0 0 ltac:(lia)).
assert (E24 : ew E0 24 = Z_to_bv 64 (q + 2)) by (rewrite (EE0 24%nat 24%bv eq_refl); exact R24).
pose proof (@paj_run_x (l_fx cx) rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B
  HGX 0 []) as RUN.
pose proof (@paj_run_to_x (l_fx cx) rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
  TG.G_HARNESS_B HGX 0 []) as RUNTO.
pose proof (paj_branch (fx := l_fx cx) (PI := PI_transportb)) as BR.
assert (KV : forall a, 0 <= a < 2 ^ 64 -> av W mem a = av W mem a) by (intros; reflexivity).
assert (GP : forall a, apresent (w_H W) mem a -> apresent (w_H W) mem a) by (intros a Ha; exact Ha).
(* +0x730 .. +0x734: the shadow byte and `beqz` *)
paj_run_tok RUN HS HJ SHOK (0, 0).
{ b2_awr_ro. }
b2_after. b2_step W KV GP.
psrr_branch_tok RUN BR HS SHOK (0, 0).
(* goal 2: the shadow byte is in (0, 8), the slow path, whose `bge` to the report is refuted; goal 1: it is 0 *)
2: (pose proof (b2_beqz _ 32 sb false E32 ltac:(lia) Hc) as Hs0; apply Z.eqb_neq in Hs0; clear Hc;
    paj_run_tok RUN HS HJ SHOK (0, 0); try (b2_awr_ro; fail); b2_after; b2_step W KV GP;
    psrr_branch_tok RUN BR HS SHOK (0, 0);
    first [ exfalso;
            pose proof (b2_bge _ 24 32 (q + 2) sb true E24 E32 ltac:(unfold B2_PHI in *; unfold q; lia) Hok Hs0 Hc);
            discriminate
          | clear Hc ]).
1: clear Hc.
all: paj_run_to_tok RUNTO HS HJ SHOK (0, 0) 0x73c.
all: try (b2_awr_ro; fail).
all: b2_after.
all: b2_step W KV GP.
(* +0x73c, from either path *)
all: lazymatch type of HS with context [restrict _ ?m] => rename m into msF end.
all: lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => rename m into mdF end.
all: b2_kreg HS EE0 regs 2%nat 2 GK2. all: b2_kreg HS EE0 regs 3%nat 3 GK3. all: b2_kreg HS EE0 regs 4%nat 4 GK4.
all: b2_kreg HS EE0 regs 8%nat 8 GK8. all: b2_kreg HS EE0 regs 9%nat 9 GK9. all: b2_kreg HS EE0 regs 18%nat 18 GK18.
all: b2_kreg HS EE0 regs 19%nat 19 GK19. all: b2_kreg HS EE0 regs 20%nat 20 GK20.
all: b2_kreg HS EE0 regs 21%nat 21 GK21. all: b2_kreg HS EE0 regs 22%nat 22 GK22.
all: b2_kreg HS EE0 regs 23%nat 23 GK23. all: b2_kreg HS EE0 regs 24%nat 24 GK24.
all: b2_kreg HS EE0 regs 25%nat 25 GK25. all: b2_kreg HS EE0 regs 26%nat 26 GK26.
all: b2_kreg HS EE0 regs 27%nat 27 GK27.
all: pmkst HS.
all: destruct (b2_move B MT XL RLO RHI cx op false false false (lo_k op) ly S W regs mem md e (ms_regs msF) (ms_mem msF) mdF
  0 LAWS HGX HB HL HTW HJ) as [HL1 HTW1];
  [ intros r Hr; cbn [In] in Hr; repeat (destruct Hr as [<- | Hr]; [assumption |]); destruct Hr
  | unfold LLVMF_STK; lia
  | intros a Ha _; exact (KV a Ha)
  | exact GP
  | intros i Hi; rewrite (KV (lc_SH cx + i) (KVS i Hi)); exact (HFSH i Hi)
  | ].
all: exact (b2_j2 K1 K2 cx op ly S W (ms_regs msF) (ms_mem msF) mdF e o0 n0 HP HB HL1 HTW1 Hopc Ec Hn0
  (eq_trans GK20 R20) (eq_trans GK21 R21) (eq_trans GK22 R22) (eq_trans GK23 R23) (eq_trans GK24 R24)
  (eq_trans GK25 R25) (eq_trans GK27 R27)).
Qed.

(* From +0x700 (n0 >= 2): the shadow byte of s8 = q + 1 and its test (+0x704), split as in b2_mac (slow path
   +0x16d0 .. +0x16d8, report 0x82f14), sel (s5), s8 = s9 + 2, `beq s7, 2`: n0 = 2 to +0xa74 (b2_rest), else the
   UBSan test of s8 + 1 and the shadow address of s8 to +0x730 (b2_mac). *)
Lemma b2_sel (K1 : lc_rom_view_stmt B MT XL RLO RHI) (K2 : lc_src_ro_stmt B MT XL RLO RHI) :
  forall cx op ly S (W : world segs) regs mem md e o0 n0,
  @lp_prem rc B MT XL RLO RHI -> @lc_base rc B MT XL RLO RHI cx ->
  @lc_lcore rc B MT cx op false false (lo_k op) ly S W regs mem md e -> lc_tw W mem (lo_B op) ->
  lc_opc (l_pl cx) (lo_c op) = 2 -> lo_c op = TOP.FuzzIn o0 n0 -> 2 <= n0 ->
  YK11.getr regs 10 = w64 (SHADOW_OFF + (l_p cx + o0 + 1) / 8) ->
  YK11.getr regs 20 = w64 (lc_F cx + 32) ->
  YK11.getr regs 22 = w64 1 -> YK11.getr regs 23 = w64 n0 -> YK11.getr regs 24 = w64 (l_p cx + o0 + 1) ->
  YK11.getr regs 25 = w64 (l_p cx + o0) -> YK11.getr regs 27 = w64 (n0 - 1) ->
  SRr segs W (mkCfg (@YK11.mkst (l_fx cx) regs (Z_to_bv 64 (BASE + 0x700)) mem (YK11.seg_rom segs)) md)
    (@lc_st_ann rc B MT cx op).
Proof.
intros cx op ly S W regs mem md e o0 n0 HP HB HL HTW Hopc Ec Hn0 R10 R20 R22 R23 R24 R25 R27.
pose proof (lp_laws _ _ _ _ _ HP) as LAWS.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned _ _ _ _ _ HP)) as HGX.
pose proof HL as (HC & (R18 & R26) & HSP & HFSH & HOK & He & HMT & R19).
pose proof HOK as (HAG & Hops & Hfin & Hfn & Hk).
rewrite Ec in Hfin. destruct Hfin as (Hfo & Hfn' & Hfl). cbn [TOP.fi_off TOP.fi_n] in Hfo, Hfn', Hfl.
pose proof (lc_geom B MT XL RLO RHI cx ly S W regs mem md e HB HC) as GEO.
destruct GEO as [HAR Hsp0al Hstk Hsp1c HFaddr HFin Hn HINg HLIVE].
pose proof HC as (HJ & Hfrs & HlyF & HPERM & Rsp & R8 & R9 & Rgp & Rtp & Hsp1 & Hsp1al & HSAV & HF4096 & HFal &
  HFceil & HFpres & HFL & HIN).
destruct Hn as (Hn1 & Hnl).
pose proof asan_consts as (CC1 & CC2 & CC3 & CC4 & CC5).
set (D := l_pl cx) in *.
set (q := l_p cx + o0) in *.
assert (Ec1 : lc_oc D (TOP.FuzzIn o0 n0) = TOP.FuzzIn (o0 + 1) (n0 - 1)).
{ unfold lc_oc, TOP.fuzz_u8_m. cbn [TOP.fi_n TOP.fi_off]. destruct (Z.eqb_spec n0 0); [lia|reflexivity]. }
destruct (b2_inb cx ly S W regs mem md e (o0 + 1) LAWS HB HC ltac:(lia))
  as (V1 & B1r & (sb & Hsb & Hok) & Hp4096 & HpPHI & Hdj & _).
replace (l_p cx + (o0 + 1)) with (q + 1) in V1, Hsb, Hok, Hdj by (unfold q; lia).
replace (q + 1 + 1) with (q + 2) in Hdj by lia.
change (l_pl cx) with D in V1, B1r.
set (b1 := DSpec.at8 D (Z.to_nat (o0 + 1))) in *.
assert (Hsbr : 0 <= sb <= 7) by (unfold saddr_ok in Hok; pose proof (Z.mod_pos_bound (q + 1) 8 ltac:(lia)); lia).
pose proof (YE2y.val_mem1_of_aview (w_H W) mem _ _ Hsb) as VS.
assert (KVS : forall i, 0 <= i < 32 -> 0 <= lc_SH cx + i < 2 ^ 64).
{ intros i Hi. pose proof (Z.div_pos (lc_F cx) 8 ltac:(lia) ltac:(lia)). unfold LF_FBYTES in HFceil.
  unfold lc_SH, SHADOW_OFF. lia. }
pose proof (b2_vals D (TOP.FuzzIn (o0 + 1) (n0 - 1)) ltac:(cbn; lia)) as AV. cbv zeta in AV.
cbn [TOP.fi_off TOP.fi_n] in AV.
destruct AV as (AS & AM & AN & AC & AB).
rewrite <- Ec1, <- Ec in AS, AM, AN, AC, AB.
set (avv := lc_ann_vals D (lc_oc D (lo_c op))) in AS, AM, AN, AC, AB.
b2_ifs AS.
pose proof (@paj_run_x (l_fx cx) rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B
  HGX 0 []) as RUN.
pose proof (@paj_run_to_x (l_fx cx) rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
  TG.G_HARNESS_B HGX 0 []) as RUNTO.
pose proof (paj_branch (fx := l_fx cx) (PI := PI_transportb)) as BR.
assert (KV : forall a, 0 <= a < 2 ^ 64 -> av W mem a = av W mem a) by (intros; reflexivity).
assert (GP : forall a, apresent (w_H W) mem a -> apresent (w_H W) mem a) by (intros a Ha; exact Ha).
assert (Hc2 : n0 = 2 \/ 3 <= n0) by lia.
destruct Hc2 as [Hn2 | Hn3].
- (* n0 = 2: sel only; `beq s7, 2` to +0xa74 *)
  b2_ifs AM. b2_ifs AN. b2_ifs AC.
  pose proof (@b2_entryS1 (l_fx cx) rc W regs mem q n0 2 2 sb b1 R10 R22 R23 R24 R25 R26 ltac:(unfold q; lia)
    ltac:(unfold B2_PHI in *; unfold q; lia) ltac:(lia) ltac:(lia) Hdj VS V1 Hsbr B1r) as HS.
  assert (R23z : YK11.getr regs 23 = Z_to_bv 64 2) by (rewrite R23, Hn2; reflexivity).
  pose proof (st_ok_pi_pin_reg' _ _ _ (23%bv) 2 HS R23z eq_refl) as HSq. clear HS. rename HSq into HS.
  set (E0 := b2_E regs sb b1 0 0 0) in *.
  assert (HEI : img_env VAL A_LIM E0) by apply b2_env_img.
  assert (SHOK : sh_ok segs (SLit 0) [] E0 (mrestrict (w_H W) mem)) by constructor.
  assert (EE0 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E0 n = YK11.getr regs r)
    by (intros; apply b2_ew_reg; assumption).
  assert (E32 : ew E0 32 = Z_to_bv 64 sb) by exact (b2_ew_x regs sb b1 0 0 0 0 ltac:(lia)).
  assert (E24 : ew E0 24 = Z_to_bv 64 (q + 1)) by (rewrite (EE0 24%nat 24%bv eq_refl); exact R24).
  paj_run_tok RUN HS HJ SHOK (0, 0).
  { b2_awr_ro. }
  b2_after. b2_step W KV GP.
  psrr_branch_tok RUN BR HS SHOK (0, 0).
  2: (pose proof (b2_beqz _ 32 sb false E32 ltac:(lia) Hc) as Hs0; apply Z.eqb_neq in Hs0; clear Hc;
      paj_run_tok RUN HS HJ SHOK (0, 0); try (b2_awr_ro; fail); b2_after; b2_step W KV GP;
      psrr_branch_tok RUN BR HS SHOK (0, 0);
      first [ exfalso;
              pose proof (b2_bge _ 24 32 (q + 1) sb true E24 E32 ltac:(unfold B2_PHI in *; unfold q; lia) Hok Hs0 Hc);
              discriminate
            | clear Hc ]).
  1: clear Hc.
  all: paj_run_to_tok RUNTO HS HJ SHOK (0, 0) 0xa74.
  all: try (b2_awr_ro; fail).
  all: b2_after.
  all: b2_step W KV GP.
  all: lazymatch type of HS with context [restrict _ ?m] => rename m into msF end.
  all: lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => rename m into mdF end.
  all: b2_reg HS (Z_to_bv 5 21) (w64 b1) G21
    ltac:(apply b2_denot_off; [exact (b2_ew_x regs sb b1 0 0 0 1 ltac:(lia)) | lia]).
  all: b2_reg HS (Z_to_bv 5 24) (w64 (q + 2)) G24
    ltac:(rewrite denot_lit_U, (U_atom_off _ 25 q 2)
      by (first [rewrite (EE0 25%nat 25%bv eq_refl); exact R25 | unfold B2_PHI in *; unfold q in *; lia]); reflexivity).
  all: b2_kreg HS EE0 regs 2%nat 2 GK2. all: b2_kreg HS EE0 regs 3%nat 3 GK3. all: b2_kreg HS EE0 regs 4%nat 4 GK4.
  all: b2_kreg HS EE0 regs 8%nat 8 GK8. all: b2_kreg HS EE0 regs 9%nat 9 GK9. all: b2_kreg HS EE0 regs 18%nat 18 GK18.
  all: b2_kreg HS EE0 regs 19%nat 19 GK19. all: b2_kreg HS EE0 regs 20%nat 20 GK20.
  all: b2_kreg HS EE0 regs 26%nat 26 GK26.
  all: pmkst HS.
  all: destruct (b2_move B MT XL RLO RHI cx op false false false (lo_k op) ly S W regs mem md e (ms_regs msF) (ms_mem msF)
    mdF 0 LAWS HGX HB HL HTW HJ) as [HL1 HTW1];
    [ intros r Hr; cbn [In] in Hr; repeat (destruct Hr as [<- | Hr]; [assumption |]); destruct Hr
    | unfold LLVMF_STK; lia
    | intros a Ha _; exact (KV a Ha)
    | exact GP
    | intros i Hi; rewrite (KV (lc_SH cx + i) (KVS i Hi)); exact (HFSH i Hi)
    | ].
  all: change (Z_to_bv 64 (BASE + 0xa74)) with (Z_to_bv 64 (BASE + if true then 0xa74 else 0xd78)).
  all: apply (b2_rest K1 K2 cx op true ly S W (ms_regs msF) (ms_mem msF) mdF e HP HB HL1 HTW1 Hopc).
  all: cbv zeta; fold D; fold avv.
  all: try (rewrite AS; exact G21).
  all: try exact (eq_trans GK20 R20).
  all: try (rewrite AM, AN, AC; cbn [TOP.fi_off TOP.fi_n];
    split; [reflexivity|]; split; [reflexivity|]; split; [|reflexivity];
    refine (eq_trans G24 _); unfold w64, q; f_equal; cbn; lia).
  all: try (rewrite AM; lia).
  all: rewrite AB; reflexivity.
- (* n0 >= 3: on to the mac byte *)
  pose proof (@b2_entryS1 (l_fx cx) rc W regs mem q n0 3 (2 ^ 26) sb b1 R10 R22 R23 R24 R25 R26 ltac:(unfold q; lia)
    ltac:(unfold B2_PHI in *; unfold q; lia) ltac:(lia) ltac:(lia) Hdj VS V1 Hsbr B1r) as HS.
  set (E0 := b2_E regs sb b1 0 0 0) in *.
  assert (HEI : img_env VAL A_LIM E0) by apply b2_env_img.
  assert (SHOK : sh_ok segs (SLit 0) [] E0 (mrestrict (w_H W) mem)) by constructor.
  assert (EE0 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E0 n = YK11.getr regs r)
    by (intros; apply b2_ew_reg; assumption).
  assert (E32 : ew E0 32 = Z_to_bv 64 sb) by exact (b2_ew_x regs sb b1 0 0 0 0 ltac:(lia)).
  assert (E24 : ew E0 24 = Z_to_bv 64 (q + 1)) by (rewrite (EE0 24%nat 24%bv eq_refl); exact R24).
  paj_run_tok RUN HS HJ SHOK (0, 0).
  { b2_awr_ro. }
  b2_after. b2_step W KV GP.
  psrr_branch_tok RUN BR HS SHOK (0, 0).
  2: (pose proof (b2_beqz _ 32 sb false E32 ltac:(lia) Hc) as Hs0; apply Z.eqb_neq in Hs0; clear Hc;
      paj_run_tok RUN HS HJ SHOK (0, 0); try (b2_awr_ro; fail); b2_after; b2_step W KV GP;
      psrr_branch_tok RUN BR HS SHOK (0, 0);
      first [ exfalso;
              pose proof (b2_bge _ 24 32 (q + 1) sb true E24 E32 ltac:(unfold B2_PHI in *; unfold q; lia) Hok Hs0 Hc);
              discriminate
            | clear Hc ]).
  1: clear Hc.
  all: paj_run_to_tok RUNTO HS HJ SHOK (0, 0) 0x730.
  all: try (b2_awr_ro; fail).
  all: b2_after.
  all: b2_step W KV GP.
  all: lazymatch type of HS with context [restrict _ ?m] => rename m into msF end.
  all: lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => rename m into mdF end.
  all: b2_reg HS (Z_to_bv 5 21) (w64 b1) G21
    ltac:(apply b2_denot_off; [exact (b2_ew_x regs sb b1 0 0 0 1 ltac:(lia)) | lia]).
  all: b2_reg HS (Z_to_bv 5 24) (w64 (q + 2)) G24
    ltac:(rewrite denot_lit_U, (U_atom_off _ 25 q 2)
      by (first [rewrite (EE0 25%nat 25%bv eq_refl); exact R25 | unfold B2_PHI in *; unfold q in *; lia]); reflexivity).
  all: b2_reg HS (Z_to_bv 5 11) (w64 (SHADOW_OFF + (q + 2) / 8)) G11
    ltac:(apply b2_denot_shadow; [rewrite (EE0 25%nat 25%bv eq_refl); exact R25 | rewrite (EE0 26%nat 26%bv eq_refl); exact R26
                                  | unfold q; lia | lia | unfold B2_PHI in *; unfold q; lia]).
  all: b2_kreg HS EE0 regs 2%nat 2 GK2. all: b2_kreg HS EE0 regs 3%nat 3 GK3. all: b2_kreg HS EE0 regs 4%nat 4 GK4.
  all: b2_kreg HS EE0 regs 8%nat 8 GK8. all: b2_kreg HS EE0 regs 9%nat 9 GK9. all: b2_kreg HS EE0 regs 18%nat 18 GK18.
  all: b2_kreg HS EE0 regs 19%nat 19 GK19. all: b2_kreg HS EE0 regs 20%nat 20 GK20.
  all: b2_kreg HS EE0 regs 22%nat 22 GK22. all: b2_kreg HS EE0 regs 23%nat 23 GK23.
  all: b2_kreg HS EE0 regs 25%nat 25 GK25. all: b2_kreg HS EE0 regs 26%nat 26 GK26.
  all: b2_kreg HS EE0 regs 27%nat 27 GK27.
  all: pmkst HS.
  all: destruct (b2_move B MT XL RLO RHI cx op false false false (lo_k op) ly S W regs mem md e (ms_regs msF) (ms_mem msF)
    mdF 0 LAWS HGX HB HL HTW HJ) as [HL1 HTW1];
    [ intros r Hr; cbn [In] in Hr; repeat (destruct Hr as [<- | Hr]; [assumption |]); destruct Hr
    | unfold LLVMF_STK; lia
    | intros a Ha _; exact (KV a Ha)
    | exact GP
    | intros i Hi; rewrite (KV (lc_SH cx + i) (KVS i Hi)); exact (HFSH i Hi)
    | ].
  all: exact (b2_mac K1 K2 cx op ly S W (ms_regs msF) (ms_mem msF) mdF e o0 n0 HP HB HL1 HTW1 Hopc Ec Hn3
    G11 (eq_trans GK20 R20) G21 (eq_trans GK22 R22)
    (eq_trans GK23 R23) G24 (eq_trans GK25 R25) (eq_trans GK27 R27)).
Qed.

(* OP2A, from the arm (+0x6e8). *)
Lemma lc_op2a_ok (K1 : lc_rom_view_stmt B MT XL RLO RHI) (K2 : lc_src_ro_stmt B MT XL RLO RHI) :
  lc_op2a_stmt B MT XL RLO RHI.
Proof.
unfold lc_op2a_stmt.
intros HP cx op W' c HB (ly' & S' & regs' & mem' & md' & e & -> & Ho & HL & HTW & (C25 & C23) & (C24 & C27) & (R20 & R22)).
pose proof (lp_laws _ _ _ _ _ HP) as LAWS.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned _ _ _ _ _ HP)) as HGX.
pose proof HL as (HC & (R18 & R26) & HSP & HFSH & HOK & He & HMT & R19).
pose proof HOK as (HAG & Hops & Hfin & Hfn & Hk).
pose proof (lc_geom B MT XL RLO RHI cx ly' S' W' regs' mem' md' e HB HC) as GEO.
destruct GEO as [HAR Hsp0al Hstk Hsp1c HFaddr HFin Hn HINg HLIVE].
pose proof HC as (HJ & Hfrs & HlyF & HPERM & Rsp & R8 & R9 & Rgp & Rtp & Hsp1 & Hsp1al & HSAV & HF4096 & HFal &
  HFceil & HFpres & HFL & HIN).
destruct Hn as (Hn1 & Hnl).
pose proof asan_consts as (CC1 & CC2 & CC3 & CC4 & CC5).
set (D := l_pl cx) in *.
destruct (lo_c op) as [o0 n0] eqn:Ec. cbn [TOP.fi_off TOP.fi_n] in *.
assert (Hopc : lc_opc D (lo_c op) = 2) by (rewrite Ec; symmetry; exact Ho).
destruct Hfin as (Hfo & Hfn' & Hfl). cbn [TOP.fi_off TOP.fi_n] in Hfo, Hfn', Hfl.
assert (Ec1 : lc_oc D (TOP.FuzzIn o0 n0) = TOP.FuzzIn (o0 + 1) (n0 - 1)).
{ unfold lc_oc, TOP.fuzz_u8_m. cbn [TOP.fi_n TOP.fi_off]. destruct (Z.eqb_spec n0 0); [lia|reflexivity]. }
rewrite Ec1 in C24, C27. cbn [TOP.fi_off TOP.fi_n] in C24, C27.
set (q := l_p cx + o0) in *.
destruct (b2_inb cx ly' S' W' regs' mem' md' e o0 LAWS HB HC ltac:(lia)) as (_ & _ & _ & Hp4096 & HpPHI & _ & _).
assert (C24' : YK11.getr regs' 24 = w64 (q + 1)) by (refine (eq_trans C24 _); unfold w64, q; f_equal; lia).
assert (KVS : forall i, 0 <= i < 32 -> 0 <= lc_SH cx + i < 2 ^ 64).
{ intros i Hi. pose proof (Z.div_pos (lc_F cx) 8 ltac:(lia) ltac:(lia)). unfold LF_FBYTES in HFceil.
  unfold lc_SH, SHADOW_OFF. lia. }
pose proof (@paj_run_to_x (l_fx cx) rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
  TG.G_HARNESS_B HGX 0 []) as RUNTO.
assert (KV : forall a, 0 <= a < 2 ^ 64 -> av W' mem' a = av W' mem' a) by (intros; reflexivity).
assert (GP : forall a, apresent (w_H W') mem' a -> apresent (w_H W') mem' a) by (intros a Ha; exact Ha).
unfold lc_cfg.
change (w64 (transportb_text + lo_arm 2)) with (Z_to_bv 64 (BASE + 0x6e8)).
assert (Hc1 : n0 = 1 \/ 2 <= n0) by lia.
destruct Hc1 as [Hn1' | Hn2].
- (* n1 = 0: `beqz s11` to +0xa70, s5 = 0, then the fill (b2_rest) *)
  pose proof (@b2_entryA (l_fx cx) rc W' regs' mem' (q + 1) (n0 - 1) 0 0 R22 C24' R26 C27
    ltac:(unfold B2_PHI in *; unfold q; lia) ltac:(lia) ltac:(lia)) as HS.
  assert (C27z : YK11.getr regs' (27%bv) = Z_to_bv 64 0) by (refine (eq_trans C27 _); rewrite Hn1'; unfold w64; f_equal; lia).
  pose proof (st_ok_pi_pin_reg' _ _ _ (27%bv) 0 HS C27z eq_refl) as HSq. clear HS. rename HSq into HS.
  set (E0 := b2_E regs' 0 0 0 0 0) in *.
  assert (HEI : img_env VAL A_LIM E0) by apply b2_env_img.
  assert (SHOK : sh_ok segs (SLit 0) [] E0 (mrestrict (w_H W') mem')) by constructor.
  assert (EE0 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E0 n = YK11.getr regs' r)
    by (intros; apply b2_ew_reg; assumption).
  paj_run_to_tok RUNTO HS HJ SHOK (0, 0) 0xa74.
  { b2_awr_ro. }
  b2_after.
  lazymatch type of HS with context [restrict _ ?m] => rename m into ms1 end.
  lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => rename m into md1 end.
  b2_step W' KV GP.
  b2_reg HS (Z_to_bv 5 21) (w64 0) G21 ltac:(reflexivity).
  b2_kreg HS EE0 regs' 2%nat 2 GK2. b2_kreg HS EE0 regs' 3%nat 3 GK3. b2_kreg HS EE0 regs' 4%nat 4 GK4.
  b2_kreg HS EE0 regs' 8%nat 8 GK8. b2_kreg HS EE0 regs' 9%nat 9 GK9. b2_kreg HS EE0 regs' 18%nat 18 GK18.
  b2_kreg HS EE0 regs' 19%nat 19 GK19. b2_kreg HS EE0 regs' 20%nat 20 GK20. b2_kreg HS EE0 regs' 24%nat 24 GK24.
  b2_kreg HS EE0 regs' 26%nat 26 GK26.
  pmkst HS.
  destruct (b2_move B MT XL RLO RHI cx op false false false (lo_k op) ly' S' W' regs' mem' md' e (ms_regs ms1) (ms_mem ms1)
    md1 0 LAWS HGX HB HL HTW HJ) as [HL1 HTW1].
  { intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<- | Hr]; [assumption |]). destruct Hr. }
  { unfold LLVMF_STK. lia. }
  { intros a Ha _. exact (KV a Ha). }
  { exact GP. }
  { intros i Hi. rewrite (KV (lc_SH cx + i) (KVS i Hi)). exact (HFSH i Hi). }
  pose proof (b2_vals D (TOP.FuzzIn (o0 + 1) (n0 - 1)) ltac:(cbn; lia)) as AV. cbv zeta in AV.
  cbn [TOP.fi_off TOP.fi_n] in AV.
  destruct AV as (AS & AM & AN & AC & AB).
  rewrite <- Ec1, <- Ec in AS, AM, AN, AC, AB.
  set (avv := lc_ann_vals D (lc_oc D (lo_c op))) in AS, AM, AN, AC, AB.
  b2_ifs AS. b2_ifs AM. b2_ifs AN. b2_ifs AC.
  change (Z_to_bv 64 (BASE + 0xa74)) with (Z_to_bv 64 (BASE + if true then 0xa74 else 0xd78)).
  apply (b2_rest K1 K2 cx op true ly' S' W' (ms_regs ms1) (ms_mem ms1) md1 e HP HB HL1 HTW1 Hopc).
  all: cbv zeta; fold D; fold avv.
  + rewrite AS. exact G21.
  + exact (eq_trans GK20 R20).
  + rewrite AM, AN, AC. cbn [TOP.fi_off TOP.fi_n].
    split; [reflexivity|]. split; [reflexivity|]. split; [|reflexivity].
    refine (eq_trans GK24 _). refine (eq_trans C24' _). unfold w64, q. f_equal. cbn. lia.
  + rewrite AM. lia.
  + rewrite AB. reflexivity.
- (* n1 >= 1: the UBSan test of s8 + 1 and the shadow address of s8, to +0x700 (b2_sel) *)
  pose proof (@b2_entryA (l_fx cx) rc W' regs' mem' (q + 1) (n0 - 1) 1 (2 ^ 26) R22 C24' R26 C27
    ltac:(unfold B2_PHI in *; unfold q; lia) ltac:(lia) ltac:(lia)) as HS.
  set (E0 := b2_E regs' 0 0 0 0 0) in *.
  assert (HEI : img_env VAL A_LIM E0) by apply b2_env_img.
  assert (SHOK : sh_ok segs (SLit 0) [] E0 (mrestrict (w_H W') mem')) by constructor.
  assert (EE0 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E0 n = YK11.getr regs' r)
    by (intros; apply b2_ew_reg; assumption).
  paj_run_to_tok RUNTO HS HJ SHOK (0, 0) 0x700.
  { b2_awr_ro. }
  b2_after.
  lazymatch type of HS with context [restrict _ ?m] => rename m into ms1 end.
  lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => rename m into md1 end.
  b2_step W' KV GP.
  b2_reg HS (Z_to_bv 5 10) (w64 (SHADOW_OFF + (q + 1) / 8)) G10
    ltac:(replace (q + 1) with (q + 1 + 0) by lia;
          apply b2_denot_shadow; [rewrite (EE0 24%nat 24%bv eq_refl); exact C24' | rewrite (EE0 26%nat 26%bv eq_refl); exact R26
                                  | unfold q; lia | lia | unfold B2_PHI in *; unfold q; lia]).
  b2_kreg HS EE0 regs' 2%nat 2 GK2. b2_kreg HS EE0 regs' 3%nat 3 GK3. b2_kreg HS EE0 regs' 4%nat 4 GK4.
  b2_kreg HS EE0 regs' 8%nat 8 GK8. b2_kreg HS EE0 regs' 9%nat 9 GK9. b2_kreg HS EE0 regs' 18%nat 18 GK18.
  b2_kreg HS EE0 regs' 19%nat 19 GK19. b2_kreg HS EE0 regs' 20%nat 20 GK20. b2_kreg HS EE0 regs' 22%nat 22 GK22.
  b2_kreg HS EE0 regs' 23%nat 23 GK23. b2_kreg HS EE0 regs' 24%nat 24 GK24. b2_kreg HS EE0 regs' 25%nat 25 GK25.
  b2_kreg HS EE0 regs' 26%nat 26 GK26. b2_kreg HS EE0 regs' 27%nat 27 GK27.
  pmkst HS.
  destruct (b2_move B MT XL RLO RHI cx op false false false (lo_k op) ly' S' W' regs' mem' md' e (ms_regs ms1) (ms_mem ms1)
    md1 0 LAWS HGX HB HL HTW HJ) as [HL1 HTW1].
  { intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<- | Hr]; [assumption |]). destruct Hr. }
  { unfold LLVMF_STK. lia. }
  { intros a Ha _. exact (KV a Ha). }
  { exact GP. }
  { intros i Hi. rewrite (KV (lc_SH cx + i) (KVS i Hi)). exact (HFSH i Hi). }
  exact (b2_sel K1 K2 cx op ly' S' W' (ms_regs ms1) (ms_mem ms1) md1 e o0 n0 HP HB HL1 HTW1 Hopc Ec Hn2
    G10 (eq_trans GK20 R20) (eq_trans GK22 R22) (eq_trans GK23 C23) (eq_trans GK24 C24') (eq_trans GK25 C25)
    (eq_trans GK27 C27)).
Qed.

End h.
