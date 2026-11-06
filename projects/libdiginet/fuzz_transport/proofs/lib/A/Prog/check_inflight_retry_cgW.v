(* check_inflight_retry_cgW: Theorem transport_check_inflight_retry_cg_holds, the statement
   transport_check_inflight_retry_cg_holds_stmt of lib/A/Prog/check_inflight_retry_cg.v: the caller-journal walk of
   check_inflight_retry (fuzz/fuzz_transport.c:450-474) on fuzz_transport.asan at 0x84268 =
   transport_sigma TS_check_inflight_retry (264 bytes, frame 48).

   The walk, from the contract's premises (cw_holds):
     1. an INNER journal at the entry state (cw_inner, YCbq.v ajournal_sub_init; stack window
        [spZ regs - CIR_STK, spZ regs), no footprint, no frame of its own);
     2. the three footprint runs of lib/A/Prog/check_inflight_retry_seg_run.v (cir_run1_F, cir_run2_F, cir_run3_F),
        each carried into SRr by DgnTransportCgRun.v decode_run; the inner journal is re-established across each by
        YCbq.v ajournal_exec (cw_journal_run: a run writes only the 48 bytes of its own frame, inside the journal's
        stack window);
     3. the two calls of the bcmp wrapper are cut by YCbq.v aj_bcmp_at at the statement's abcmp_realizes premise
        (cw_bcmp). The first compares [fa, fa + 26) with [M + 120, M + 146), the second [fa + 28, fa + len) with
        [M + 148, M + 120 + len). The frame's ranges are read ranges by DgnTransportCg.v trans_src_ok_rd (of the
        statement's trans_src_ok), cut by trans_rd_ok_sub and kept at the call's memory by trans_rd_ok_view; both lie
        outside the call's stack window by decode_off_win. M's ranges (cw_m_rd): their bytes are payload bytes of M
        (tw_at), their shadow is M's zero shadow at the call's AR state (decode_zshadow_rd of trans_cir_cells), and the
        shadow hull past M's last granule is the six guard bytes 0xf9 of trans_cir_cells (const cells of the record,
        YG0n.v am_const); len <= SPEC_MAX_FRAME keeps the second range inside [M + 148, M + 1634). Each answer is 0:
        the model's beq_bytes makes the two ranges agree byte for byte (cw_eq1, cw_eq2: garr8 of the frame against
        tw_read_bytes of M.fly.frame);
     4. every byte the runs read outside the window, and the frame the prologue wrote, are kept across the runs and
        the calls (cir_same: the view outside [spZ regs - CIR_STK, spZ regs) is the entry's; cw_frame_call), so the
        world fields come from tw_at at the entry memory (cw_world_raw, TWorldG.v tw_kept / tw_bytes_at), the shadow
        byte of fp + 30 from the struct's read range (cw_shadow_zero) and f->retry from trans_sframe_at;
     5. the inner journal and the caller's compose by YC85.v ajournal_sub_tok, the kept bytes are YCbq.v
        acall_kept_of_journal of the inner journal (no footprint, no written range), the meter is unchanged
        (YC5d.v mle_start), the frames and the blocks are the call state's, and Bw' = Bw by the model (cw_close).
   The trap at 0x84358 and the error path at 0x8436c are not reached: the runs decide each test from the model's
   facts (PWR.cir_model of the plain walk lib/Prog/T/check_inflight_retry.v) and the shadow byte of fp + 30 is 0. *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00 YI16 YP09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Cells Step Regs6ss.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import Frame ExecF.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require LeafCgKit LeafCgFacts AsanKAProof.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportSyms DgnTransportAddr DgnTransportCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportCgRun YC85.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import check_sent_frame_cg check_inflight_retry_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import check_inflight_retry_seg_run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TWorldLemmas TSess0 TCb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require check_inflight_retry.
Import ListNotations.
Open Scope Z_scope.
Module YKK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module LCK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.LeafCgKit.

(* ---- small facts about bytes, lists and the reader ---- *)

(* Present bytes make a writable stack range (lib/Lib/Frame.v stk). *)
Lemma cw_stk_present : forall (H : word -> bool) m lo hi, 0 <= lo -> hi <= 2 ^ 64 ->
  (forall a, lo <= a < hi -> apresent H m a) -> stk rsegs m lo hi.
Proof.
  intros H m lo hi H0 H1 Hp. split; [exact H0|]. split; [exact H1|].
  intros a Ha. destruct (Hp a Ha) as [_ [b Hb]]. unfold wa. split.
  - unfold wview. rewrite Hb. discriminate.
  - exists b. unfold mrd. rewrite Hb. reflexivity.
Qed.

(* A byte, written as a value and read back as one byte. *)
Lemma cw_b8_bz : forall b : byte, Z_to_bv 8 (le_byte (DSpec.bz b) 1 0) = b.
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as Hbr. unfold bv_modulus in Hbr.
  change (2 ^ Z.of_N 8) with 256 in Hbr. unfold le_byte, DSpec.bz.
  change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
  change (2 ^ 8) with 256. rewrite (Z.mod_small (bv_unsigned b) 256) by lia.
  rewrite (Z.mod_small (bv_unsigned b) 256) by lia.
  apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 8) with 256. rewrite Z.mod_small by lia. reflexivity.
Qed.

(* The byte i of a list a garr8 fact holds, through the walk's view. *)
Lemma cw_view_garr8 : forall (W : world tfibsegs) memc q (l : list byte) i,
  garr8 tfibsegs (mrestrict (w_H W) memc) q (map DSpec.bz l) -> (i < length l)%nat ->
  aview tfibsegs (w_H W) memc (q + Z.of_nat i) = Some (bv_unsigned (nth i l (Z_to_bv 8 0))).
Proof.
  intros W memc q l i HG Hi.
  assert (Hm : (i < length (map DSpec.bz l))%nat) by (rewrite length_map; exact Hi).
  destruct (HG i Hm) as [HV _]. specialize (HV 0%nat ltac:(lia)).
  cbn [Z.of_nat] in HV. rewrite Z.add_0_r in HV.
  unfold aview. cbv beta. rewrite HV. cbn [option_map]. f_equal.
  rewrite (nth_indep (map DSpec.bz l) 0 (DSpec.bz (Z_to_bv 8 0))) by (rewrite length_map; exact Hi).
  rewrite map_nth. f_equal. apply cw_b8_bz.
Qed.

(* A byte read twice at a visible address. *)
Lemma cw_mrd_of_aview : forall (W : world tfibsegs) m m' a,
  w_H W (Z_to_bv 64 a) = false ->
  aview tfibsegs (w_H W) m' a = aview tfibsegs (w_H W) m a ->
  mrd rsegs m' (wa a) = mrd rsegs m (wa a).
Proof.
  intros W m m' a Hv E.
  rewrite (decode_aview_mrd W m' a Hv), (decode_aview_mrd W m a Hv) in E.
  destruct (mrd rsegs m' (wa a)) as [b1|]; destruct (mrd rsegs m (wa a)) as [b2|];
    cbn [option_map] in E; try discriminate E; [|reflexivity].
  injection E as E. f_equal. apply bv_eq. exact E.
Qed.

(* The bytes a run reads, as the load step reads them. *)
Lemma cw_ovr : forall m a bs (n : nat), bytes_at rsegs m a bs -> length bs = n ->
  ov_read_bytes rsegs m (wa a) n = Some bs.
Proof.
  intros m a bs n H L. pose proof H as (H0 & _).
  exact (cir_rd_tp m m 0 0 a bs n (munch_refl [(0, 0)] m) L ltac:(right; lia) H).
Qed.

Lemma cir_nth_skipn : forall (l : list byte) (a b : nat) d, nth b (skipn a l) d = nth (a + b) l d.
Proof.
  intros l a. revert l. induction a as [|a IH]; intros l b d; [reflexivity|].
  destruct l as [|x l]; [destruct b; reflexivity|]. cbn [skipn]. rewrite IH. reflexivity.
Qed.

Lemma cir_nth_firstn : forall (l : list byte) (a b : nat) d, (b < a)%nat -> nth b (firstn a l) d = nth b l d.
Proof.
  induction l as [|x l IH]; intros a b d H; destruct a as [|a]; [lia | destruct b; reflexivity | lia |].
  cbn [firstn]. destruct b as [|b]; [reflexivity|]. cbn [nth]. apply IH. lia.
Qed.

Section Walk.
Context {fx : YKK.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournalA := (@ajournal rc AE2k.tfib_sink_head segs B).

Hypothesis HCELLS : transport_cells B.
Hypothesis HCIR : trans_cir_cells B.
Hypothesis LAWS : AR_laws segs B.
Hypothesis MTL : ameter_laws MT.
Hypothesis ABCMPH : forall fx' : YKK.FPState,
  @abcmp_realizes fx' rc segs B (transport_sigma TS___interceptor_trampoline_bcmp).

(* One constant cell of the record, one byte wide, read at any AR state. *)
Lemma cw_const_vis : forall ly S (W : world segs) m md a v,
  AR segs B ly S W m md -> In (z1 (ANum a) v) (as_const B ly) -> aview segs (w_H W) m a = Some (le_byte v 1 0).
Proof.
  intros ly S W m md a v [M _] Hin.
  pose proof (proj1 (Forall_forall _ _) (am_const _ _ _ _ M) _ Hin) as C.
  unfold cell_holds in C. cbn [c_at c_val c_w z1 c1 aeval] in C.
  specialize (C 0%nat ltac:(lia)). rewrite Z.add_0_r in C. exact C.
Qed.

Section Call.
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
  (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate)
  (W : world segs) (memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word)
  (fa fp : Z) (frame : list byte) (Bw Bw' : list byte).

Hypothesis HJ : ajournalA STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k.
Hypothesis HRET : YK0s.ret_ok (YKK.getr regs 1).
Hypothesis HRA4 : 4096 <= raZ regs.
Hypothesis HGP : YKK.getr regs 3 = w64 (as_gp B).
Hypothesis HTP : YKK.getr regs 4 = w64 (as_tp B).
Hypothesis H10 : YKK.getr regs 10 = w64 fa.
Hypothesis H11 : YKK.getr regs 11 = w64 (Z.of_nat (length frame)).
Hypothesis H12 : YKK.getr regs 12 = w64 fp.
Hypothesis HAL : spZ regs mod 16 = 0.
Hypothesis HWLO : sp0 - STK <= spZ regs - CIR_STK.
Hypothesis HWHI : spZ regs <= sp0.
Hypothesis HFA0 : 0 < fa.
Hypothesis GFR : garr8 segs (mrestrict (w_H W) memc) fa (map DSpec.bz frame).
Hypothesis SRCF : trans_src_ok B lyc Sc W memc fa (Z.of_nat (length frame)).
Hypothesis OWF : decode_off_win regs CIR_STK fa (Z.of_nat (length frame)).
Hypothesis SFR : trans_sframe_at W memc fp fa (TC.rf frame).
Hypothesis SRCP : trans_src_ok B lyc Sc W memc fp SF_SIZE.
Hypothesis OWP : decode_off_win regs CIR_STK fp SF_SIZE.
Hypothesis HW : tw_at TMAP_A (aview segs (w_H W) memc) Bw.
Hypothesis HM : TC.check_inflight_retry_m Bw frame = Some (Bw', tt).
Hypothesis HMAX : TW.M_fly_len Bw <= TC.SPEC_MAX_FRAME.
Hypothesis HNEV : st_nev S + k + CIR_EV <= EV_MAX.

Local Abbreviation RNGW := (LCK.RNG_W (world segs) (@w_H segs) W).
Local Abbreviation LEN := (Z.of_nat (length frame)).

(* ---- what the journal says about the entry state ---- *)

Lemma cw_AR : AR segs B lyc Sc W memc mdc.
Proof. destruct HJ as (HAR & _). exact HAR. Qed.

Lemma cw_stk_ok : astk_ok STK ly sp0.
Proof.
  destruct HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HS & _). exact HS.
Qed.

Lemma cw_pres : forall a, sp0 - STK <= a < sp0 -> apresent (w_H W) memc a.
Proof.
  destruct HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HP & _). exact HP.
Qed.

(* CIR_STK = 48 + 2 * ESTACK = 8240. *)
Lemma cw_sp_rng : YM05.alloc_ceiling + 8240 <= spZ regs /\ spZ regs <= 2 ^ 47.
Proof.
  pose proof cw_stk_ok as (H16 & Hstk0 & Hceil & Hlo & Hhi & H47 & _).
  pose proof HWLO as HL. unfold CIR_STK, CIR_FRAME, ESTACK in HL. lia.
Qed.

Lemma cw_stk : stk rsegs memc (spZ regs - CIR_STK) (spZ regs).
Proof.
  pose proof cw_sp_rng as [SP1 SP2]. unfold CIR_STK, CIR_FRAME, ESTACK in *. pose proof asan_consts as (C1 & _).
  apply (cw_stk_present (w_H W)); [lia | lia|].
  intros a Ha. apply cw_pres. lia.
Qed.

Lemma cw_cells : ACells.asan_cells memc.
Proof. exact (decode_cells_asan B HCELLS lyc Sc W memc mdc (@w_Hoff segs W) cw_AR). Qed.

(* ---- the model's facts (the plain walk's cir_model) and M.fly.len <= SPEC_MAX_FRAME ---- *)

Lemma cw_model :
  Bw' = Bw /\ TW.s32_at Bw 96 <> 0 /\ LEN = TW.u_at Bw 1640 8 /\ 28 <= LEN /\ LEN <= 1514 /\
  firstn 26 frame = TW.sub Bw 120 26 /\ skipn 28 frame = TW.sub Bw 148 (Z.to_nat (LEN - 28)) /\
  DSpec.sf_retry (TC.rf frame) = DSpec.u32 (TW.u_at Bw 108 4 + 1) /\
  DSpec.sf_retry (TC.rf frame) <= TW.u_at Bw 65056 4 /\
  TSess0.u64 (TW.u_at Bw 65052 4 * 1000) <= TSess0.u64 (TW.u_at Bw 65000 8 - TW.u_at Bw 112 8).
Proof.
  destruct (PWR.cir_model Bw Bw' frame HM) as (E0 & E1 & E2 & E3 & _ & E5 & E6 & E7 & E8 & E9).
  pose proof HMAX as HX. change (TW.M_fly_len Bw) with (TW.u_at Bw 1640 8) in HX.
  assert (Hmf : TC.SPEC_MAX_FRAME = 1514) by reflexivity. rewrite Hmf in HX.
  split; [exact E0|]. split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. split; [lia|].
  split; [exact E5|]. split; [exact E6|]. split; [exact E7|]. split; [exact E8 | exact E9].
Qed.

(* The two ranges the walk reads through the statement's trans_src_ok (DgnTransportCg.v trans_src_ok_rd). *)
Lemma cw_rdF : decode_rd_ok W memc fa LEN.
Proof.
  pose proof cw_model as (_ & _ & _ & H28 & _).
  exact (trans_src_ok_rd B LAWS lyc Sc W memc mdc fa LEN cw_AR SRCF ltac:(lia)).
Qed.

Lemma cw_rdP : decode_rd_ok W memc fp SF_SIZE.
Proof. exact (trans_src_ok_rd B LAWS lyc Sc W memc mdc fp SF_SIZE cw_AR SRCP ltac:(unfold SF_SIZE; lia)). Qed.

(* ---- the view outside the window [spZ regs - CIR_STK, spZ regs) ---- *)

Definition cir_same (m : word -> option byte) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> (a + 1 <= spZ regs - CIR_STK \/ spZ regs <= a) ->
    aview segs (w_H W) m a = aview segs (w_H W) memc a.

Lemma cw_same_refl : cir_same memc.
Proof. intros a _ _. reflexivity. Qed.

(* A run writes only its 48-byte frame at the window's top. *)
Lemma cw_same_run : forall m m1, cir_same m -> munch [(spZ regs + -48, spZ regs)] m m1 -> cir_same m1.
Proof.
  intros m m1 Hs MU a Ha Hd. rewrite <- (Hs a Ha Hd). apply aview_eq_of. unfold mrestrict.
  destruct (w_H W (Z_to_bv 64 a)); [reflexivity|].
  apply MU. cbn [outside]. rewrite unsigned_lit by lia.
  unfold CIR_STK, CIR_FRAME, ESTACK in Hd. split; [lia | exact I].
Qed.

(* A call of bcmp changes nothing outside [sp - 48 - 2 * ESTACK, sp - 48). *)
Lemma cw_same_call : forall m1 m2, cir_same m1 ->
  (forall a, 0 <= a < 2 ^ 64 -> (a + 1 <= spZ regs - CIR_STK \/ spZ regs + -48 <= a) ->
     aview segs (w_H W) m2 a = aview segs (w_H W) m1 a) ->
  cir_same m2.
Proof.
  intros m1 m2 H1 H2 a Ha Hd. rewrite (H2 a Ha ltac:(destruct Hd; [left; lia | right; lia])). exact (H1 a Ha Hd).
Qed.

Lemma cw_mrd_same : forall m a, cir_same m -> 0 <= a < 2 ^ 64 ->
  (a + 1 <= spZ regs - CIR_STK \/ spZ regs <= a) -> w_H W (Z_to_bv 64 a) = false ->
  mrd rsegs m (wa a) = mrd rsegs memc (wa a).
Proof. intros m a Hs Ha Hd Hv. exact (cw_mrd_of_aview W memc m a Hv (Hs a Ha Hd)). Qed.

(* bytes_at at a memory with the entry's view, from the entry's view of each byte. *)
Lemma cw_bytes_view : forall m q (bs : list byte), cir_same m -> 0 <= q -> q + Z.of_nat (length bs) <= 2 ^ 64 ->
  (forall i, (i < length bs)%nat ->
     (q + Z.of_nat i + 1 <= spZ regs - CIR_STK \/ spZ regs <= q + Z.of_nat i) /\
     aview segs (w_H W) memc (q + Z.of_nat i) = Some (bv_unsigned (nth i bs (Z_to_bv 8 0)))) ->
  bytes_at rsegs m q bs.
Proof.
  intros m q bs Hs H0 H1 H. split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct (H i Hi) as [Hout Hv].
  pose proof (decode_aview_vis W memc _ _ Hv) as Hvis.
  rewrite (cw_mrd_same m (q + Z.of_nat i) Hs ltac:(lia) Hout Hvis).
  rewrite (decode_aview_mrd W memc _ Hvis) in Hv.
  destruct (mrd rsegs memc (wa (q + Z.of_nat i))) as [b|] eqn:E; [|discriminate Hv].
  cbn [option_map] in Hv. injection Hv as Hv.
  rewrite (nth_error_nth' bs (Z_to_bv 8 0) Hi). f_equal. apply bv_eq. exact Hv.
Qed.

(* The world at a memory with the entry's view: every payload byte lies in G, below the window. *)
Lemma cw_world_raw : forall m, cir_same m ->
  tw_at TMAP_A (fun a => option_map (fun x : byte => bv_unsigned x) (mrd rsegs m (wa a))) Bw.
Proof.
  intros m Hs. apply (tw_kept TMAP_A (aview segs (w_H W) memc)); [exact HW|].
  intros x Hx. pose proof (TMAP_A_hull x Hx) as Hh.
  unfold TransportG.G_HARNESS_LO, TransportG.G_HARNESS_HI in Hh.
  destruct Hx as (o & b & n & Hin & Hb).
  pose proof (proj2 HW o b n (x - b) Hin ltac:(lia)) as Hv. replace (b + (x - b)) with x in Hv by lia.
  pose proof (decode_aview_vis W memc x _ Hv) as Hvis.
  pose proof cw_sp_rng as [SP1 SP2]. pose proof asan_consts as (C1 & _).
  cbv beta. rewrite <- (decode_aview_mrd W m x Hvis).
  apply Hs; [lia | left; unfold CIR_STK, CIR_FRAME, ESTACK; lia].
Qed.

(* The footprint holds every payload range of the world. *)
Lemma cw_rng_world : forall o b n q c, In (o, b, n) TMAP_A -> b <= q -> q + c <= b + n -> rng RNGW q c.
Proof.
  intros o b n q c Hin H1 H2.
  pose proof (tw_row TMAP_A o b n TMAP_A_ok Hin) as (_ & Hn & _ & Hb0 & Hb64).
  apply (decode_rng W); [lia | lia |]. intros x Hx.
  pose proof (proj2 HW o b n (x - b) Hin ltac:(lia)) as Hv. replace (b + (x - b)) with x in Hv by lia.
  exact (decode_aview_vis W memc x _ Hv).
Qed.

(* ---- read ranges at the call's memory ---- *)

(* What abcmp_realizes asks of each range. *)
Definition cir_rd (m : word -> option byte) (q n : Z) : Prop :=
  (forall a, q <= a < q + n -> aview segs (w_H W) m a <> None) /\
  range_addressable (aview segs (w_H W) m) SHADOW_OFF q n /\
  (0 < n -> shadow_hull_vis (aview segs (w_H W) m) q n) /\
  amem_range q n /\ 0 <= q /\ q + n <= 2 ^ 63.

Lemma cw_rd_of_ok : forall m q n, decode_rd_ok W m q n -> cir_rd m q n.
Proof.
  intros m q n (H1 & H2 & H3 & H4 & H5 & H6).
  split; [exact H1|]. split; [exact H2|]. split; [intros _; exact H3|]. exact (conj H4 (conj H5 H6)).
Qed.

(* A read range outside the window keeps decode_rd_ok at a memory with the entry's view (its shadow bytes lie in
   the shadow band, below the window). *)
Lemma cw_rd_view : forall m q n, cir_same m -> decode_rd_ok W memc q n ->
  (q + n <= spZ regs - CIR_STK \/ spZ regs <= q) -> decode_rd_ok W m q n.
Proof.
  intros m q n Hs RD OFF. pose proof RD as (_ & _ & _ & Hm & H0 & H63).
  pose proof cw_sp_rng as [SP1 SP2]. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  apply (trans_rd_ok_view W W memc m q n RD).
  - intros a Ha. apply Hs; [lia | destruct OFF; [left; lia | right; lia]].
  - intros s Hsb. apply Hs; [lia | left; unfold CIR_STK, CIR_FRAME, ESTACK; lia].
Qed.

(* M's two ranges at a call: payload bytes of M, M's zero shadow and the six guard bytes after it. *)
Lemma cw_m_rd : forall m md q n, AR segs B lyc Sc W m md -> cir_same m ->
  TA_M + 120 <= q -> q + n <= TA_M + 1634 -> 0 <= n -> cir_rd m q n.
Proof.
  intros m md q n HAR Hs H1 H2 Hn.
  destruct HCIR as [HZ HC]. destruct (HC lyc) as (G0 & G1 & G2 & G3 & G4 & G5).
  pose proof cw_sp_rng as [SP1 SP2]. pose proof asan_consts as (A1 & A2 & A3 & A4 & A5).
  split; [|split; [|split; [|split; [|split]]]].
  - intros a Ha.
    rewrite (Hs a); [| unfold TA_M in *; lia | left; unfold CIR_STK, CIR_FRAME, ESTACK, TA_M in *; lia].
    pose proof (proj2 HW TW.OFF_M TA_M TW.SZ_M (a - TA_M) TMAP_A_M ltac:(unfold TW.SZ_M; lia)) as Hv.
    replace (TA_M + (a - TA_M)) with a in Hv by lia. rewrite Hv. discriminate.
  - intros x Hx. exists 0. split; [|left; reflexivity].
    replace (shadow_of_addr SHADOW_OFF x) with (ACells.shadow_addr (8 * (x / 8))).
    2: { unfold shadow_of_addr, ACells.shadow_addr, SHADOW_OFF, ACells.ASAN_K.
         rewrite (Z.mul_comm 8), Z.div_mul by lia. lia. }
    pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.mod_pos_bound x 8 ltac:(lia)).
    apply (decode_zshadow_rd B lyc Sc W m md TA_M (TA_M + TW.SZ_M) (8 * (x / 8)) HAR); [| | | exact HZ].
    + rewrite Z.mul_comm. apply Z_mod_mult.
    + unfold TA_M in *. lia.
    + unfold TA_M, TW.SZ_M in *. lia.
  - intros Hn0 s Hs'. unfold shadow_addr, SHADOW_OFF in Hs'.
    assert (Hb : 2148220472 <= s < 2148220672) by (unfold TA_M in *; Z.div_mod_to_equations; lia).
    destruct (Z_le_gt_dec s 2148220665) as [Hl|Hg].
    + replace s with (ACells.shadow_addr (8 * (s - ACells.ASAN_K))).
      2: { unfold ACells.shadow_addr, ACells.ASAN_K. rewrite (Z.mul_comm 8), Z.div_mul by lia. lia. }
      rewrite (decode_zshadow_rd B lyc Sc W m md TA_M (TA_M + TW.SZ_M) (8 * (s - ACells.ASAN_K)) HAR);
        [discriminate | | | | exact HZ].
      * rewrite Z.mul_comm. apply Z_mod_mult.
      * unfold TA_M, ACells.ASAN_K. lia.
      * unfold TA_M, TW.SZ_M, ACells.ASAN_K. lia.
    + change (ACells.shadow_addr (TA_M + TW.SZ_M)) with 2148220666 in G0.
      change (ACells.shadow_addr (TA_M + TW.SZ_M + 8)) with 2148220667 in G1.
      change (ACells.shadow_addr (TA_M + TW.SZ_M + 16)) with 2148220668 in G2.
      change (ACells.shadow_addr (TA_M + TW.SZ_M + 24)) with 2148220669 in G3.
      change (ACells.shadow_addr (TA_M + TW.SZ_M + 32)) with 2148220670 in G4.
      change (ACells.shadow_addr (TA_M + TW.SZ_M + 40)) with 2148220671 in G5.
      assert (Hc : s = 2148220666 \/ s = 2148220667 \/ s = 2148220668 \/ s = 2148220669 \/ s = 2148220670 \/
                   s = 2148220671) by lia.
      destruct Hc as [-> | [-> | [-> | [-> | [-> | -> ]]]]];
        [ rewrite (cw_const_vis _ _ _ _ _ _ _ HAR G0) | rewrite (cw_const_vis _ _ _ _ _ _ _ HAR G1)
        | rewrite (cw_const_vis _ _ _ _ _ _ _ HAR G2) | rewrite (cw_const_vis _ _ _ _ _ _ _ HAR G3)
        | rewrite (cw_const_vis _ _ _ _ _ _ _ HAR G4) | rewrite (cw_const_vis _ _ _ _ _ _ _ HAR G5) ];
        discriminate.
  - left. unfold TA_M, kLowMemEnd in *. lia.
  - unfold TA_M in *. lia.
  - unfold TA_M in *. lia.
Qed.

(* ---- the bytes the two calls compare agree, by the model's beq_bytes ---- *)

Lemma cw_eq1 : forall m, cir_same m ->
  forall i, 0 <= i < 26 -> aview segs (w_H W) m (fa + i) = aview segs (w_H W) m (TA_M + 120 + i).
Proof.
  intros m Hs i Hi.
  pose proof cw_model as (_ & _ & _ & HL & HLM & HEQ1 & _).
  pose proof cw_rdF as (_ & _ & _ & _ & HF0 & HF63).
  pose proof cw_sp_rng as [SP1 SP2]. pose proof asan_consts as (C1 & _).
  pose proof OWF as OW. unfold decode_off_win in OW.
  rewrite (Hs (fa + i)) by (first [lia | destruct OW; [left; lia | right; lia]]).
  rewrite (Hs (TA_M + 120 + i)) by (first [unfold TA_M; lia | left; unfold CIR_STK, CIR_FRAME, ESTACK, TA_M; lia]).
  replace i with (Z.of_nat (Z.to_nat i)) by lia.
  rewrite (cw_view_garr8 W memc fa frame (Z.to_nat i) GFR ltac:(lia)).
  rewrite (tw_read_bytes TMAP_A _ Bw TW.OFF_M TA_M TW.SZ_M 120 26 (Z.to_nat i) TMAP_A_ok HW TMAP_A_M
             ltac:(lia) ltac:(unfold TW.SZ_M; lia) ltac:(lia)).
  change (TW.OFF_M + 120) with 120. rewrite <- HEQ1. rewrite cir_nth_firstn by lia. reflexivity.
Qed.

Lemma cw_eq2 : forall m, cir_same m ->
  forall i, 0 <= i < LEN - 28 -> aview segs (w_H W) m (fa + 28 + i) = aview segs (w_H W) m (TA_M + 148 + i).
Proof.
  intros m Hs i Hi.
  pose proof cw_model as (_ & _ & _ & HL & HLM & _ & HEQ2 & _).
  pose proof cw_rdF as (_ & _ & _ & _ & HF0 & HF63).
  pose proof cw_sp_rng as [SP1 SP2]. pose proof asan_consts as (C1 & _).
  pose proof OWF as OW. unfold decode_off_win in OW.
  rewrite (Hs (fa + 28 + i)) by (first [lia | destruct OW; [left; lia | right; lia]]).
  rewrite (Hs (TA_M + 148 + i)) by (first [unfold TA_M; lia | left; unfold CIR_STK, CIR_FRAME, ESTACK, TA_M; lia]).
  replace (fa + 28 + i) with (fa + Z.of_nat (28 + Z.to_nat i)) by lia.
  replace (TA_M + 148 + i) with (TA_M + 148 + Z.of_nat (Z.to_nat i)) by lia.
  rewrite (cw_view_garr8 W memc fa frame (28 + Z.to_nat i) GFR ltac:(lia)).
  rewrite (tw_read_bytes TMAP_A _ Bw TW.OFF_M TA_M TW.SZ_M 148 (Z.to_nat (LEN - 28)) (Z.to_nat i) TMAP_A_ok HW
             TMAP_A_M ltac:(lia) ltac:(unfold TW.SZ_M; lia) ltac:(lia)).
  change (TW.OFF_M + 148) with 148. rewrite <- HEQ2. rewrite cir_nth_skipn. reflexivity.
Qed.

(* ---- the shadow byte of a granule inside a readable range is 0 ---- *)

Lemma cw_shadow_zero : forall q n x,
  decode_rd_ok W memc q n -> q <= x -> x + 8 <= q + n ->
  w_H W (Z_to_bv 64 (x / 8 + ACells.ASAN_K)) = false /\
  mrd rsegs memc (wa (x / 8 + ACells.ASAN_K)) = Some (Z_to_bv 8 0).
Proof.
  intros q n x (Hv & Hra & Hh & Hm & H0 & H63) H1 H2.
  pose proof (Z.div_mod x 8 ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Hmb.
  destruct (Hra (8 * (x / 8) + 7) ltac:(lia)) as (s & Hs & Hok).
  assert (Ediv : (8 * (x / 8) + 7) / 8 = x / 8).
  { replace (8 * (x / 8) + 7) with (7 + (x / 8) * 8) by lia. rewrite Z.div_add by lia.
    rewrite (Z.div_small 7 8) by lia. lia. }
  assert (Emod : (8 * (x / 8) + 7) mod 8 = 7).
  { replace (8 * (x / 8) + 7) with (7 + (x / 8) * 8) by lia. rewrite Z.mod_add by lia.
    apply Z.mod_small. lia. }
  assert (Es : s = 0) by (unfold saddr_ok in Hok; rewrite Emod in Hok; lia).
  assert (Ea : shadow_of_addr SHADOW_OFF (8 * (x / 8) + 7) = x / 8 + ACells.ASAN_K).
  { unfold shadow_of_addr, SHADOW_OFF, ACells.ASAN_K. rewrite Ediv. lia. }
  rewrite Ea, Es in Hs.
  destruct (decode_aview_some W memc _ 0 Hs) as (Hvis & b & Hb & Eb).
  split; [exact Hvis|]. rewrite Hb. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned.
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. rewrite Eb. reflexivity.
Qed.

(* ---- the inner journal ---- *)

Lemma cw_inner : ajournalA CIR_STK (spZ regs) [] lyc Sc W memc mdc [] lyc Sc W memc mdc 0.
Proof.
  pose proof cw_stk_ok as (Hal16 & _).
  apply (@ajournal_sub_init rc AE2k.tfib_sink_head segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
           CIR_STK (spZ regs) [] (spZ regs - sp0) HJ);
    [lia | rewrite Zminus_mod, HAL, Hal16; reflexivity | lia | unfold CIR_STK, CIR_FRAME, ESTACK; lia | lia].
Qed.

(* The inner journal across one footprint run: the run writes only its own frame, which lies in the journal's
   stack window (YCbq.v ajournal_exec). *)
Lemma cw_journal_run : forall (mem1 mem2 : word -> option byte) (md1 md2 : Model),
  ajournalA CIR_STK (spZ regs) [] lyc Sc W memc mdc [] lyc Sc W mem1 md1 0 ->
  munch [(spZ regs + -48, spZ regs)] mem1 mem2 ->
  wmono rsegs mem1 mem2 ->
  same_but_materialized md1 md2 ->
  ajournalA CIR_STK (spZ regs) [] lyc Sc W memc mdc [] lyc Sc W mem2 md2 0.
Proof.
  intros mem1 mem2 md1 md2 JI MU WM SBM.
  pose proof cw_sp_rng as [SP1 SP2]. unfold CIR_STK, CIR_FRAME, ESTACK in *. pose proof asan_consts as (C1 & _).
  apply (@ajournal_exec rc AE2k.tfib_sink_head segs B LAWS decode_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mem2 md2
           (fun a => spZ regs + -48 <= a < spZ regs) JI).
  - intros x Hx. unfold mrestrict. destruct (w_H W x) eqn:Eh; [reflexivity|].
    apply MU. cbn [outside]. split; [lia | exact I].
  - intros x Hx. unfold mrestrict in *. revert Hx. destruct (w_H W x) eqn:Ehx; intros Hx; [exact Hx|].
    destruct (Z_lt_le_dec (bv_unsigned x) (spZ regs + -48)) as [Hl|Hl];
      [rewrite (MU x); [exact Hx | cbn [outside]; split; [lia | exact I]]|].
    destruct (Z_lt_le_dec (bv_unsigned x) (spZ regs)) as [Hh|Hh];
      [|rewrite (MU x); [exact Hx | cbn [outside]; split; [lia | exact I]]].
    assert (Hw : wview rsegs mem2 x <> None).
    { refine (WM x _). unfold wview. destruct (mem1 x) as [b|] eqn:Em;
        [discriminate | exfalso; first [exact (Hx Em) | exact (Hx eq_refl)]]. }
    unfold wview in Hw. destruct (mem2 x) as [b|] eqn:Em1; [discriminate|]. exfalso.
    rewrite (find_segment_none rsegs (bv_unsigned x)) in Hw; [exact (Hw eq_refl)|].
    intros Him. pose proof (decode_segs_low _ Him) as Hlow. unfold kLowMemEnd in Hlow. lia.
  - intros x Hh.
    destruct (Z_lt_le_dec (bv_unsigned x) (spZ regs + -48)) as [Hl|Hl];
      [apply (MU x); cbn [outside]; split; [lia | exact I]|].
    destruct (Z_lt_le_dec (bv_unsigned x) (spZ regs)) as [Hh2|Hh2];
      [|apply (MU x); cbn [outside]; split; [lia | exact I]].
    exfalso.
    assert (Hxr : sp0 - STK <= bv_unsigned x < sp0) by lia.
    pose proof (proj1 (cw_pres _ Hxr)) as Hhx. rewrite Z_to_bv_bv_unsigned in Hhx. congruence.
  - exact SBM.
  - intros a Ha. cbv beta in Ha. left. lia.
Qed.

(* A writable stack range from the inner journal's present bytes. *)
Lemma cw_stk_of_journal : forall mem2 md2 hi,
  ajournalA CIR_STK (spZ regs) [] lyc Sc W memc mdc [] lyc Sc W mem2 md2 0 ->
  spZ regs - CIR_STK <= hi -> hi <= spZ regs ->
  stk rsegs mem2 (spZ regs - CIR_STK) hi.
Proof.
  intros mem2 md2 hi JI H1 H2.
  pose proof cw_sp_rng as [SP1 SP2]. unfold CIR_STK, CIR_FRAME, ESTACK in *. pose proof asan_consts as (C1 & _).
  destruct JI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HP & _).
  apply (cw_stk_present (w_H W)); [lia | lia|]. intros a Ha. apply HP. lia.
Qed.

(* The frame the prologue wrote is kept by a call whose window lies below it. *)
Lemma cw_frame_call : forall (mem1 mem2 : word -> option byte) (md1 : Model) (cs : list cell),
  ajournalA CIR_STK (spZ regs) [] lyc Sc W memc mdc [] lyc Sc W mem1 md1 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> (a + 1 <= spZ regs - CIR_STK \/ spZ regs + -48 <= a) ->
     aview segs (w_H W) mem2 a = aview segs (w_H W) mem1 a) ->
  (forall a, apresent (w_H W) mem1 a -> apresent (w_H W) mem2 a) ->
  rw_cells rsegs mem1 (spZ regs + -48) cs -> Z.of_nat (cells_size cs) <= 48 ->
  rw_cells rsegs mem2 (spZ regs + -48) cs.
Proof.
  intros mem1 mem2 md1 cs JI Hview Happ FR Hsz.
  pose proof cw_sp_rng as [SP1 SP2]. unfold CIR_STK, CIR_FRAME, ESTACK in *. pose proof asan_consts as (C1 & _).
  pose proof JI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HP & _).
  apply (decode_frame_ext (spZ regs + -48) 48 cs mem1 mem2); [exact Hsz | | exact FR].
  intros i Hi.
  assert (Hp1 : apresent (w_H W) mem1 (spZ regs + -48 + i)) by (apply HP; lia).
  exact (decode_present_eq W mem1 mem2 (spZ regs + -48 + i) Hp1 (Happ _ Hp1)
           (Hview (spZ regs + -48 + i) ltac:(lia) ltac:(right; lia))).
Qed.

(* ---- the close: the inner journal and the caller's compose into the statement's post ---- *)

Lemma cw_close : forall (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model),
  ajournalA CIR_STK (spZ regs) [] lyc Sc W memc mdc [] lyc Sc W mem2 md2 0 ->
  aregs_preserved regs regs2 -> Bw' = Bw ->
  SRr segs W (mkCfg (@YKK.mkst fx regs2 (YKK.getr regs 1) mem2 (YKK.seg_rom segs)) md2)
    (@transport_cir_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw').
Proof.
  intros regs2 mem2 md2 JI HP HBw.
  apply SRr_ret. unfold transport_cir_post, decode_cg_post.
  exists lyc, Sc, regs2, mem2, md2, 0.
  split; [reflexivity|].
  split; [unfold CIR_EV; lia|].
  split.
  { pose proof (ajournal_sub_tok segs B LAWS decode_segs_low STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
                  CIR_STK (spZ regs) [] [] lyc Sc W mem2 md2 0 HJ JI HWLO HWHI
                  ltac:(intros a (r & Hr & _); destruct Hr)) as J.
    cbn [app] in J. exact J. }
  split; [exact HP|].
  split; [reflexivity|].
  split; [apply Permutation_refl|].
  split.
  { exact (acall_kept_of_journal segs B decode_segs_low CIR_STK (spZ regs) [] [] lyc Sc W memc mdc
             lyc Sc W mem2 md2 0 (fun _ => False) JI cw_AR
             ltac:(intros a (r & Hr & _); destruct Hr)
             ltac:(intros bq mq i Hb _ _; exact Hb)
             sink_closed_nil). }
  split; [exact (mle_start MT Sc MTL) | exact HBw].
Qed.

(* The registers the epilogue restores and the ones every step and call kept are the caller's. *)
Lemma cw_pres_ret : forall (g1 spx g3 g4 x5 x6 x7 g8 g9 r10 r11 r12 x13 x14 x15 x16 x17 : word)
    (g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 x28 x29 x30 x31 : word),
  bv_unsigned spx = spZ regs ->
  g3 = YKK.getr regs 3 -> g4 = YKK.getr regs 4 -> g8 = YKK.getr regs 8 -> g9 = YKK.getr regs 9 ->
  g18 = YKK.getr regs 18 -> g19 = YKK.getr regs 19 -> g20 = YKK.getr regs 20 -> g21 = YKK.getr regs 21 ->
  g22 = YKK.getr regs 22 -> g23 = YKK.getr regs 23 -> g24 = YKK.getr regs 24 ->
  g25 = YKK.getr regs 25 -> g26 = YKK.getr regs 26 -> g27 = YKK.getr regs 27 ->
  aregs_preserved regs
    (mkR g1 spx g3 g4 x5 x6 x7 g8 g9 r10 r11 r12 x13 x14 x15 x16 x17
         g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 x28 x29 x30 x31).
Proof.
  intros g1 spx g3 g4 x5 x6 x7 g8 g9 r10 r11 r12 x13 x14 x15 x16 x17
    g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 x28 x29 x30 x31
    Hsp E3 E4 E8 E9 E18 E19 E20 E21 E22 E23 E24 E25 E26 E27 r Hr.
  unfold acallee_saved in Hr.
  assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
               r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  repeat (destruct Hc as [Hc|Hc]); subst r;
    first [ exact E3 | exact E4 | exact E8 | exact E9 | exact E18 | exact E19 | exact E20 | exact E21
          | exact E22 | exact E23 | exact E24 | exact E25 | exact E26 | exact E27 | apply bv_eq; exact Hsp ].
Qed.

(* The registers of a state ms_eqv to a concrete map. *)
Lemma cw_pres_eqv : forall (R F : bvmap 5 word) pc fc rv m ro ms',
  ms_eqv (MS R F pc fc rv m ro) ms' -> aregs_preserved regs R -> aregs_preserved regs (ms_regs ms').
Proof.
  intros R F pc fc rv m ro ms' EQV HP r Hr. unfold acallee_saved in Hr.
  assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
               r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  repeat (destruct Hc as [Hc|Hc]); subst r;
    (rewrite (decode_ms_reg R F pc fc rv m ro ms' _ EQV) by reflexivity);
    apply HP; unfold acallee_saved; lia.
Qed.

(* ---- the two bcmp calls ---- *)

(* One call of the bcmp wrapper on the inner journal (YCbq.v aj_bcmp_at at the statement's abcmp_realizes). *)
Lemma cw_bcmp : forall (regsT : bvmap 5 word) (memT : word -> option byte) (mdT : Model)
    (x y n : Z) (raw : word) (Q : world segs -> config -> Prop),
  ajournalA CIR_STK (spZ regs) [] lyc Sc W memc mdc [] lyc Sc W memT mdT 0 ->
  YKK.getr regsT 10 = w64 x -> YKK.getr regsT 11 = w64 y -> YKK.getr regsT 12 = w64 n ->
  0 <= n < 2 ^ 32 ->
  cir_rd memT x n -> cir_rd memT y n ->
  (x + n <= spZ regs - CIR_STK \/ spZ regs <= x) ->
  (y + n <= spZ regs - CIR_STK \/ spZ regs <= y) ->
  YKK.getr regsT 2 = Z_to_bv 64 (spZ regs + -48) ->
  YKK.getr regsT 3 = w64 (as_gp B) -> YKK.getr regsT 4 = w64 (as_tp B) ->
  YKK.getr regsT 1 = raw -> YK0s.ret_ok raw ->
  (forall i, 0 <= i < n -> aview segs (w_H W) memT (x + i) = aview segs (w_H W) memT (y + i)) ->
  (forall (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model),
     ajournalA CIR_STK (spZ regs) [] lyc Sc W memc mdc [] lyc Sc W mem2 md2 0 ->
     aregs_preserved regsT regs2 -> YKK.getr regs2 10 = w64 0 ->
     (forall a, 0 <= a < 2 ^ 64 -> (a + 1 <= spZ regs - CIR_STK \/ spZ regs + -48 <= a) ->
        aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) ->
     (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a) ->
     SRr segs W (mkCfg (@YKK.mkst fx regs2 raw mem2 (YKK.seg_rom segs)) md2) Q) ->
  SRr segs W
    (mkCfg (@YKK.mkst fx regsT (Z_to_bv 64 (transport_sigma TS___interceptor_trampoline_bcmp)) memT
              (YKK.seg_rom segs)) mdT) Q.
Proof.
  intros regsT memT mdT x y n raw Q JI R10 R11 R12 Hn RDX RDY OFX OFY R2 R3 R4 R1 HRAW HEQ K.
  pose proof cw_sp_rng as [SP1 SP2]. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof RDX as (HvX & HraX & HhX & HmX & H0X & H63X).
  pose proof RDY as (HvY & HraY & HhY & HmY & H0Y & H63Y).
  assert (HspT : spZ regsT = spZ regs + -48)
    by (unfold spZ; rewrite R2; rewrite unsigned_lit; [reflexivity | unfold CIR_STK, CIR_FRAME, ESTACK in *; lia]).
  eapply SRr_bind.
  { apply (@aj_bcmp_at fx rc AE2k.tfib_sink_head segs B LAWS decode_segs_low
             (transport_sigma TS___interceptor_trampoline_bcmp) (ABCMPH fx) W regsT memT
             CIR_STK (spZ regs) [] lyc Sc W memc mdc [] lyc Sc mdT 0 x y n (-48) raw JI).
    - exact R10.
    - exact R11.
    - exact R12.
    - lia.
    - exact H0X.
    - lia.
    - exact H0Y.
    - lia.
    - exact HspT.
    - reflexivity.
    - lia.
    - unfold CIR_STK, CIR_FRAME, ESTACK; lia.
    - exact R3.
    - exact R4.
    - exact R1.
    - exact HRAW.
    - intros a Ha. split; [exact (HvX a Ha)|].
      rewrite HspT. unfold CIR_STK, CIR_FRAME, ESTACK in *. lia.
    - intros a Ha. split; [exact (HvY a Ha)|].
      rewrite HspT. unfold CIR_STK, CIR_FRAME, ESTACK in *. lia.
    - intros a Ha. unfold CIR_STK, CIR_FRAME, ESTACK in *. lia.
    - intros a Ha. unfold CIR_STK, CIR_FRAME, ESTACK in *. lia.
    - exact HmX.
    - exact HmY.
    - exact HraX.
    - exact HhX.
    - exact HraY.
    - exact HhY. }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & JI2 & HP2 & Hv & Hiff & Hview & Happ).
  apply (K regs2 mem2 md2 JI2 HP2).
  - rewrite Hv. apply Hiff. exact HEQ.
  - intros a Ha1 Ha2. apply Hview; [lia|].
    unfold CIR_STK, CIR_FRAME, ESTACK in *. destruct Ha2; lia.
  - exact Happ.
Qed.

(* ---- the walk ---- *)

Lemma cw_holds :
  SRr segs W (@cfg_at fx segs (transport_sigma TS_check_inflight_retry) regs memc mdc)
    (@transport_cir_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw').
Proof using HCELLS HCIR LAWS MTL ABCMPH HJ HRET HRA4 HGP HTP H10 H11 H12 HAL HWLO HWHI HFA0 GFR SRCF OWF SFR SRCP
  OWP HW HM HMAX HNEV.
  pose proof cw_sp_rng as [SP1 SP2].
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof cw_model as (EBW & HON & HLEN & HL28 & HL1514 & HEQ1 & HEQ2 & HRT & HMX & HTM).
  pose proof cw_rdF as (HvF & _ & _ & HmF & HF0 & HF63).
  pose proof cw_rdP as (HvP & _ & _ & HmP & HP0 & HP63). unfold SF_SIZE in HvP, HmP, HP63.
  pose proof SFR as (HFP0 & HFP8 & SB & GSB & LSB & _ & _ & _ & _ & _ & _ & SB30 & _).
  pose proof (tw_len TMAP_A _ Bw HW) as LBW.
  pose proof OWF as OWF'. unfold decode_off_win in OWF'.
  pose proof OWP as OWP'. unfold decode_off_win, SF_SIZE in OWP'.
  assert (GRET : ret_pc (YKK.getr regs (Z_to_bv 5 1)) = YKK.getr regs (Z_to_bv 5 1))
    by exact (LeafCgFacts.ret_ok_stmt_YK0s _ HRET).
  assert (G10 : YKK.getr regs (Z_to_bv 5 10) = w64 fa) by exact H10.
  assert (G11 : YKK.getr regs (Z_to_bv 5 11) = w64 LEN) by exact H11.
  assert (G12 : YKK.getr regs (Z_to_bv 5 12) = w64 fp) by exact H12.
  pose proof cw_cells as (CK & GCK & _).
  pose proof (cw_world_raw memc cw_same_refl) as HWR.
  assert (ESP : bv_unsigned (YKK.getr regs (Z_to_bv 5 2)) = spZ regs) by reflexivity.
  (* ---- run 1: the entry to the first call ---- *)
  eapply decode_run.
  { unfold LCK.ms_of_regs. rewrite G10, G11, G12.
    eapply cir_run1_F with (lo := spZ regs - CIR_STK) (Bw := Bw).
    - exact LBW.
    - exact cw_stk.
    - unfold CIR_STK, CIR_FRAME, ESTACK. lia.
    - pose proof (tw_bytes_at rsegs memc TMAP_A Bw TW.OFF_M TA_M TW.SZ_M 96 4 TMAP_A_ok HWR TMAP_A_M
                    ltac:(lia) ltac:(unfold TW.SZ_M; lia)) as BON.
      change (TW.OFF_M + 96) with 96 in BON. exact BON.
    - pose proof (tw_bytes_at rsegs memc TMAP_A Bw TW.OFF_M TA_M TW.SZ_M 1640 8 TMAP_A_ok HWR TMAP_A_M
                    ltac:(lia) ltac:(unfold TW.SZ_M; lia)) as BLN.
      change (TW.OFF_M + 1640) with 1640 in BLN. exact BLN.
    - exact GCK.
    - exact CK.
    - unfold TA_M, TW.SZ_M, CIR_STK, CIR_FRAME, ESTACK. lia.
    - apply (decode_rng W); [lia | lia |]. intros b Hb.
      apply (proj1 (cw_pres b ltac:(unfold CIR_STK, CIR_FRAME, ESTACK in *; lia))).
    - exact (cw_rng_world _ _ _ (TA_M + 96) 4 TMAP_A_M ltac:(lia) ltac:(unfold TW.SZ_M; lia)).
    - exact (cw_rng_world _ _ _ (TA_M + 1640) 8 TMAP_A_M ltac:(lia) ltac:(unfold TW.SZ_M; lia)).
    - apply (decode_rng W); [unfold ACells.GOT_CELL_K; lia | unfold ACells.GOT_CELL_K; lia |]. intros b Hb.
      assert (Hs : exists sg, In sg segs /\ Z.of_N (seg_base sg) <= b < Z.of_N (seg_base sg) + Z.of_N (seg_size sg))
        by (apply (decode_covers_img ACells.GOT_CELL_K 8 b); [vm_compute; reflexivity | exact Hb]).
      exact (decode_vis_seg W b Hs).
    - apply (decode_rng W); [unfold ACells.CELL_K; lia | unfold ACells.CELL_K; lia |]. intros b Hb.
      assert (Hs : exists sg, In sg segs /\ Z.of_N (seg_base sg) <= b < Z.of_N (seg_base sg) + Z.of_N (seg_size sg))
        by (apply (decode_covers_img ACells.CELL_K 8 b); [vm_compute; reflexivity | exact Hb]).
      exact (decode_vis_seg W b Hs).
    - exact HON.
    - exact HLEN.
    - lia.
    - lia.
    - lia. }
  intros msT mdT (ms0 & (m1 & -> & MU & WM & ST1 & FR) & EQVT) SBMT.
  rewrite (decode_ms_shape _ _ _ _ EQVT).
  pose proof (cw_journal_run memc m1 mdc mdT cw_inner MU WM SBMT) as JI1.
  pose proof (cw_same_run memc m1 cw_same_refl MU) as SM1.
  (* ---- the first call: bcmp (fa, M + 120, 26) ---- *)
  eapply cw_bcmp with (x := fa) (y := TA_M + 120) (n := 26) (raw := Z_to_bv 64 CIR_RET1).
  - exact JI1.
  - rewrite (decode_ms_reg _ _ _ _ _ _ _ _ _ EQVT) by reflexivity. reflexivity.
  - rewrite (decode_ms_reg _ _ _ _ _ _ _ _ _ EQVT) by reflexivity. reflexivity.
  - rewrite (decode_ms_reg _ _ _ _ _ _ _ _ _ EQVT) by reflexivity. reflexivity.
  - lia.
  - apply cw_rd_of_ok. apply (cw_rd_view m1 fa 26 SM1).
    + exact (trans_rd_ok_sub W memc fa LEN fa 26 cw_rdF ltac:(lia) ltac:(lia) ltac:(lia)).
    + lia.
  - exact (cw_m_rd m1 mdT (TA_M + 120) 26 (proj1 JI1) SM1 ltac:(lia) ltac:(lia) ltac:(lia)).
  - lia.
  - left. unfold TA_M, CIR_STK, CIR_FRAME, ESTACK. lia.
  - rewrite (decode_ms_reg _ _ _ _ _ _ _ _ _ EQVT) by reflexivity. reflexivity.
  - rewrite (decode_ms_reg _ _ _ _ _ _ _ _ _ EQVT) by reflexivity. exact HGP.
  - rewrite (decode_ms_reg _ _ _ _ _ _ _ _ _ EQVT) by reflexivity. exact HTP.
  - rewrite (decode_ms_reg _ _ _ _ _ _ _ _ _ EQVT) by reflexivity. reflexivity.
  - apply YK0s.ret_ok_even. vm_compute. reflexivity.
  - exact (cw_eq1 m1 SM1).
  - intros regs2 mem2 md2 JI2 HP2 H2a0 Hview Happ.
    pose proof (cw_same_call m1 mem2 SM1 Hview) as SM2.
    pose proof (cw_frame_call m1 mem2 mdT _ JI1 Hview Happ FR
                  ltac:(unfold cir_fr; cbn [cells_size csize]; lia)) as FR2.
    assert (GA0 : YKK.getr regs2 (Z_to_bv 5 10) = w64 0) by exact H2a0.
    (* ---- run 2: the first call's return to the second call ---- *)
    eapply decode_run.
    { unfold LCK.ms_of_regs.
      rewrite (HP2 2 ltac:(unfold acallee_saved; lia)), (HP2 3 ltac:(unfold acallee_saved; lia)),
        (HP2 4 ltac:(unfold acallee_saved; lia)), (HP2 8 ltac:(unfold acallee_saved; lia)),
        (HP2 9 ltac:(unfold acallee_saved; lia)), (HP2 18 ltac:(unfold acallee_saved; lia)),
        (HP2 19 ltac:(unfold acallee_saved; lia)), (HP2 20 ltac:(unfold acallee_saved; lia)),
        (HP2 21 ltac:(unfold acallee_saved; lia)), (HP2 22 ltac:(unfold acallee_saved; lia)),
        (HP2 23 ltac:(unfold acallee_saved; lia)), (HP2 24 ltac:(unfold acallee_saved; lia)),
        (HP2 25 ltac:(unfold acallee_saved; lia)), (HP2 26 ltac:(unfold acallee_saved; lia)),
        (HP2 27 ltac:(unfold acallee_saved; lia)), GA0.
      rewrite !(decode_ms_reg _ _ _ _ _ _ _ _ _ EQVT) by reflexivity.
      eapply cir_run2_F; [lia | lia]. }
    intros msU mdU (ms0' & -> & EQVU) SBMU.
    rewrite (decode_ms_shape _ _ _ _ EQVU).
    pose proof (cw_journal_run mem2 mem2 md2 mdU JI2 (munch_refl _ _) (wmono_refl rsegs mem2) SBMU) as JI2'.
    (* ---- the second call: bcmp (fa + 28, M + 148, len - 28) ---- *)
    eapply cw_bcmp with (x := fa + 28) (y := TA_M + 148) (n := LEN - 28) (raw := Z_to_bv 64 CIR_RET2).
    + exact JI2'.
    + rewrite (decode_ms_reg _ _ _ _ _ _ _ _ _ EQVU) by reflexivity. reflexivity.
    + rewrite (decode_ms_reg _ _ _ _ _ _ _ _ _ EQVU) by reflexivity. reflexivity.
    + rewrite (decode_ms_reg _ _ _ _ _ _ _ _ _ EQVU) by reflexivity. reflexivity.
    + lia.
    + apply cw_rd_of_ok. apply (cw_rd_view mem2 (fa + 28) (LEN - 28) SM2).
      * exact (trans_rd_ok_sub W memc fa LEN (fa + 28) (LEN - 28) cw_rdF ltac:(lia) ltac:(lia) ltac:(lia)).
      * lia.
    + exact (cw_m_rd mem2 md2 (TA_M + 148) (LEN - 28) (proj1 JI2) SM2 ltac:(lia) ltac:(lia) ltac:(lia)).
    + lia.
    + left. unfold TA_M, CIR_STK, CIR_FRAME, ESTACK. lia.
    + rewrite (decode_ms_reg _ _ _ _ _ _ _ _ _ EQVU) by reflexivity. reflexivity.
    + rewrite (decode_ms_reg _ _ _ _ _ _ _ _ _ EQVU) by reflexivity. exact HGP.
    + rewrite (decode_ms_reg _ _ _ _ _ _ _ _ _ EQVU) by reflexivity. exact HTP.
    + rewrite (decode_ms_reg _ _ _ _ _ _ _ _ _ EQVU) by reflexivity. reflexivity.
    + apply YK0s.ret_ok_even. vm_compute. reflexivity.
    + exact (cw_eq2 mem2 SM2).
    + intros regs3 mem3 md3 JI3 HP3 H3a0 Hview3 Happ3.
      pose proof (cw_same_call mem2 mem3 SM2 Hview3) as SM3.
      pose proof (cw_frame_call mem2 mem3 mdU _ JI2' Hview3 Happ3 FR2
                    ltac:(unfold cir_fr; cbn [cells_size csize]; lia)) as FR3.
      pose proof (cw_stk_of_journal mem3 md3 (spZ regs + -48) JI3
                    ltac:(unfold CIR_STK, CIR_FRAME, ESTACK; lia) ltac:(lia)) as ST3.
      assert (GB0 : YKK.getr regs3 (Z_to_bv 5 10) = w64 0) by exact H3a0.
      (* what run 3 reads at the second call's return *)
      pose proof (cw_world_raw mem3 SM3) as HW3.
      assert (L4 : forall kk, 0 <= kk -> kk + 4 <= Z.of_nat (length Bw) -> length (TW.sub Bw kk 4) = 4%nat)
        by (intros kk H1 H2; exact (TWorldLemmas.length_sub Bw kk 4 H1 H2)).
      assert (L8 : forall kk, 0 <= kk -> kk + 8 <= Z.of_nat (length Bw) -> length (TW.sub Bw kk 8) = 8%nat)
        by (intros kk H1 H2; exact (TWorldLemmas.length_sub Bw kk 8 H1 H2)).
      rewrite LBW in L4, L8. unfold TW.W_LEN in L4, L8.
      pose proof (tw_bytes_at rsegs mem3 TMAP_A Bw TW.OFF_M TA_M TW.SZ_M 108 4 TMAP_A_ok HW3 TMAP_A_M
                    ltac:(lia) ltac:(unfold TW.SZ_M; lia)) as B108.
      change (TW.OFF_M + 108) with 108 in B108.
      pose proof (tw_bytes_at rsegs mem3 TMAP_A Bw TW.OFF_M TA_M TW.SZ_M 112 8 TMAP_A_ok HW3 TMAP_A_M
                    ltac:(lia) ltac:(unfold TW.SZ_M; lia)) as B112.
      change (TW.OFF_M + 112) with 112 in B112.
      pose proof (tw_bytes_at rsegs mem3 TMAP_A Bw TW.OFF_g_cfg TA_g_cfg TW.SZ_g_cfg 32 4 TMAP_A_ok HW3 TMAP_A_g_cfg
                    ltac:(lia) ltac:(unfold TW.SZ_g_cfg; lia)) as BMX.
      change (TW.OFF_g_cfg + 32) with 65056 in BMX.
      pose proof (tw_bytes_at rsegs mem3 TMAP_A Bw TW.OFF_g_cfg TA_g_cfg TW.SZ_g_cfg 28 4 TMAP_A_ok HW3 TMAP_A_g_cfg
                    ltac:(lia) ltac:(unfold TW.SZ_g_cfg; lia)) as BTO.
      change (TW.OFF_g_cfg + 28) with 65052 in BTO.
      pose proof (tw_bytes_at rsegs mem3 TMAP_A Bw TW.OFF_g_now TA_g_now TW.SZ_g_now 0 8 TMAP_A_ok HW3 TMAP_A_g_now
                    ltac:(lia) ltac:(unfold TW.SZ_g_now; lia)) as BNW.
      rewrite !Z.add_0_r in BNW. change TW.OFF_g_now with 65000 in BNW.
      (* the shadow byte of fp + 30: the granule [fp + 24, fp + 32) lies in the struct's 80 bytes *)
      assert (E30 : (fp + 24) / 8 = (fp + 30) / 8).
      { pose proof (Z.div_mod fp 8 ltac:(lia)) as Dm. rewrite HFP8, Z.add_0_r in Dm.
        rewrite Dm. rewrite (Z.mul_comm 8 (fp / 8)).
        rewrite !Z.div_add_l by lia. reflexivity. }
      destruct (cw_shadow_zero fp SF_SIZE (fp + 24) cw_rdP ltac:(lia) ltac:(unfold SF_SIZE; lia)) as [SHV SHM].
      rewrite E30 in SHV, SHM.
      assert (SH3 : mrd rsegs mem3 (wa ((fp + 30) / 8 + ACells.ASAN_K)) = Some (Z_to_bv 8 0)).
      { assert (Hsb : 0 <= (fp + 30) / 8 + ACells.ASAN_K < kHighShadowEnd).
        { pose proof (Z.div_mod (fp + 30) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (fp + 30) 8 ltac:(lia)).
          unfold ACells.ASAN_K, amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *. lia. }
        rewrite (cw_mrd_same mem3 ((fp + 30) / 8 + ACells.ASAN_K) SM3 ltac:(lia)
                   ltac:(left; unfold CIR_STK, CIR_FRAME, ESTACK; lia) SHV).
        exact SHM. }
      (* f->retry at fp + 30: the two bytes of the struct's 80 (trans_sframe_at) *)
      assert (BRT : bytes_at rsegs mem3 (fp + 30) (TW.sub SB 30 2)).
      { assert (LS2 : length (TW.sub SB 30 2) = 2%nat) by (apply TWorldLemmas.length_sub; lia).
        apply (cw_bytes_view mem3 (fp + 30) (TW.sub SB 30 2) SM3); [lia | rewrite LS2; lia |].
        intros i Hi. rewrite LS2 in Hi. split; [lia|].
        rewrite (tw_nth_sub SB 30 2 i (Z_to_bv 8 0)) by lia.
        replace (fp + 30 + Z.of_nat i) with (fp + Z.of_nat (Z.to_nat 30 + i)) by lia.
        exact (cw_view_garr8 W memc fp SB (Z.to_nat 30 + i) GSB ltac:(lia)). }
      (* ---- run 3: the second call's return to the `ret` ---- *)
      eapply decode_run.
      { unfold LCK.ms_of_regs.
        rewrite (HP3 2 ltac:(unfold acallee_saved; lia)), (HP3 3 ltac:(unfold acallee_saved; lia)),
          (HP3 4 ltac:(unfold acallee_saved; lia)), (HP3 8 ltac:(unfold acallee_saved; lia)),
          (HP3 9 ltac:(unfold acallee_saved; lia)), (HP3 18 ltac:(unfold acallee_saved; lia)),
          (HP3 19 ltac:(unfold acallee_saved; lia)), (HP3 20 ltac:(unfold acallee_saved; lia)),
          (HP3 21 ltac:(unfold acallee_saved; lia)), (HP3 22 ltac:(unfold acallee_saved; lia)),
          (HP3 23 ltac:(unfold acallee_saved; lia)), (HP3 24 ltac:(unfold acallee_saved; lia)),
          (HP3 25 ltac:(unfold acallee_saved; lia)), (HP3 26 ltac:(unfold acallee_saved; lia)),
          (HP3 27 ltac:(unfold acallee_saved; lia)), GB0.
        rewrite !(decode_ms_reg _ _ _ _ _ _ _ _ _ EQVU) by reflexivity.
        eapply cir_run3_F with (lo := spZ regs - CIR_STK) (SB := SB) (Bw := Bw).
        - exact (AsanKAProof.rd1 _ _ _ SH3).
        - exact (cw_ovr _ _ _ 2 BRT ltac:(apply TWorldLemmas.length_sub; lia)).
        - exact (cw_ovr _ _ _ 4 B108 (L4 108 ltac:(lia) ltac:(lia))).
        - exact (cw_ovr _ _ _ 4 BMX (L4 65056 ltac:(lia) ltac:(lia))).
        - exact (cw_ovr _ _ _ 8 B112 (L8 112 ltac:(lia) ltac:(lia))).
        - exact (cw_ovr _ _ _ 8 BNW (L8 65000 ltac:(lia) ltac:(lia))).
        - exact (cw_ovr _ _ _ 4 BTO (L4 65052 ltac:(lia) ltac:(lia))).
        - apply (decode_rng W); [lia | lia |]. intros b Hb.
          apply (proj1 (cw_pres b ltac:(unfold CIR_STK, CIR_FRAME, ESTACK in *; lia))).
        - apply (decode_rng W); [unfold ACells.ASAN_K; lia | unfold ACells.ASAN_K; lia |]. intros b Hb.
          replace b with ((fp + 30) / 8 + ACells.ASAN_K) by lia. exact SHV.
        - apply (decode_rng W); [lia | lia |]. intros b Hb.
          destruct (aview segs (w_H W) memc b) as [v|] eqn:Ev; [exact (decode_aview_vis W memc b v Ev)|].
          exfalso. exact (HvP b ltac:(lia) Ev).
        - exact (cw_rng_world _ _ _ (TA_M + 108) 4 TMAP_A_M ltac:(lia) ltac:(unfold TW.SZ_M; lia)).
        - exact (cw_rng_world _ _ _ (TA_M + 112) 8 TMAP_A_M ltac:(lia) ltac:(unfold TW.SZ_M; lia)).
        - exact (cw_rng_world _ _ _ (TA_g_cfg + 28) 8 TMAP_A_g_cfg ltac:(lia) ltac:(unfold TW.SZ_g_cfg; lia)).
        - pose proof (cw_rng_world _ _ _ TA_g_now 8 TMAP_A_g_now ltac:(lia) ltac:(unfold TW.SZ_g_now; lia)) as R.
          exact R.
        - exact ST3.
        - unfold CIR_STK, CIR_FRAME, ESTACK. lia.
        - exact FR3.
        - lia.
        - lia.
        - rewrite SB30. exact HRT.
        - rewrite SB30. exact HMX.
        - exact HTM. }
      intros ms3 md4 (ms0'' & (r10 & r11 & r12 & spx & -> & Hsp & ST4) & EQV3) SBM3.
      rewrite (decode_ms_shape _ _ _ _ EQV3).
      rewrite GRET.
      eapply cw_close.
      * exact (cw_journal_run mem3 mem3 md3 md4 JI3 (munch_refl _ _) (wmono_refl rsegs mem3) SBM3).
      * apply (cw_pres_eqv _ _ _ _ _ _ _ _ EQV3).
        apply cw_pres_ret; first [exact Hsp | reflexivity].
      * exact EBW.
Qed.

End Call.
End Walk.

(* The statement of lib/A/Prog/check_inflight_retry_cg.v. *)
Theorem transport_check_inflight_retry_cg_holds {fx : YKK.FPState} {rc : YM05.RunCeil}
    (B : asyms) (MT : ameter_ops) : @transport_check_inflight_retry_cg_holds_stmt fx rc B MT.
Proof.
  intros HCELLS HCIR LAWS MTL ABCMP.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fa fp frame Bw Bw'.
  intros HJ HRET HRA4 HGP HTP H10 H11 H12 HAL HWLO HWHI HFA0 GFR SRCF OWF SFR SRCP OWP HW HM HMAX HNEV.
  exact (cw_holds B MT HCELLS HCIR LAWS MTL ABCMP STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs
           fa fp frame Bw Bw' HJ HRET HRA4 HGP HTP H10 H11 H12 HAL HWLO HWHI HFA0 GFR SRCF OWF SFR SRCP OWP HW HM
           HMAX HNEV).
Qed.
