(* check_sent_frame_cgW: Theorem transport_check_sent_frame_cg_holds : the statement
   transport_check_sent_frame_cg_holds_stmt of lib/B/Prog/check_sent_frame_cg.v, the caller-journal walk of
   check_sent_frame on fuzz_transport.asan-ubsan at 0x84080 (852 bytes, frame 48, two calls of the bcmp wrapper).
   Image B's twin of lib/A/Prog/check_sent_frame_cgW.v: the same steps, at image B's kit
   (lib/B/Prog/TransportFevt.v, lib/B/Prog/CgBNoTwin.v) and the run statements of
   lib/B/Prog/check_sent_frame_seg_defs.v.

   The walk, from the contract's premises and the three run statements (cw_holds):
     1. an INNER journal at the entry state (cw_inner, YCbq.v ajournal_sub_init; stack window
        [spZ regs - CSF_STK, spZ regs), no footprint, no frame of its own);
     2. the premises read as the bundles of check_sent_frame_seg_defs.v: both trans_src_ok premises through the kit's
        trans_src_ok_rd (lib/B/Prog/DgnTransportBCg.v; cw_rdF, cw_rdP, the only uses of trans_src_ok), the struct's
        bytes and fields from trans_sframe_at, the frame's bytes from garr8, the shadow bytes the checks read
        (range_addressable of the two read ranges), the runtime cells (TransportFevt.v decode_cells_asan),
        M.desk_known and g_cfg.sum_mode from the world relation tw_at (TWorldG.v tw_kept, tw_bytes_at), and the
        model's facts from check_sent_frame_m Bw frame = Some (Bw', tt) (the plain walk's csf_model; cw_mem0, cw_rng0,
        the csf_fx assert); csf_bnd's 0 < fa is the statement's premise;
     3. three footprint runs carried into SRr by TransportFevt.v decode_run: csf_run1_stmt (entry .. the first call),
        csf_mid_stmt (its return .. the second call), csf_tail_stmt (its return .. the ret); the final state of each is
        an mkst state of a register map xregs_eqv to the run's (decode_eqv_mkst, decode_getr_xeqv); the inner journal
        is re-established across the first by CgBNoTwin.v cgb_j_frame (it writes only its 48-byte frame) and across
        the other two by cgb_j_sbm (they write nothing);
     4. the two bcmp calls are cut by YCbq.v aj_bcmp_at at the statement's abcmp_realizes premise (cw_bcmp):
        (fa + 6, HOST, 6) and (fa, M + 4, 6); the ranges are read ranges at the call state (cw_rd_vk for the frame,
        cw_host_rd from trans_rom_view_rd, transport_cells' HOST shadow cell and trans_csf_cells' guard cells of SCALE
        and HOST, cw_m4_rd from tw_at, M's zero shadow and g_last_counter's cells), and the answer is 0 because the
        model makes the bytes agree (cw_cmp1: sub frame 6 6 = HOST, the image's HOST bytes decided; cw_cmp2:
        sub frame 0 6 = M_desk Bw); every byte the runs read lies outside the call's window, so csf_mem and the frame
        are kept across each call (cw_vk_call, cw_mem_vk, cw_frame_call);
     5. the inner journal and the caller's compose by YC85.v ajournal_sub_tok, the kept bytes are YCbq.v
        acall_kept_of_journal of the inner journal, the meter is unchanged (YC5d.v mle_start), the frames and blocks
        are the call state's, and Bw' = Bw is the model's (cw_close). *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00 YI16 YP09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI5b YI5c YK1b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Cells Step Regs6ss.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import Frame ExecF.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require LeafCgKit LeafCgFacts.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBSyms DgnTransportBAddr DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TransportFevt CgBNoTwin YC85.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import check_sent_frame_cg check_sent_frame_seg_defs.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import check_sent_frame_seg_base check_sent_frame_seg_tail.
Import ListNotations.
Open Scope Z_scope.
Module YKK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module LCK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.LeafCgKit.
Module FC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.AsanCells.

(* ---- bytes under the overlay view ---- *)

(* A byte the image view reads is not hidden (YK04.v H_off_segments: a hidden byte lies in no segment). *)
Lemma cw_aview_vis : forall (W : world tfibsegs) mem a v,
  aview tfibsegs (w_H W) mem a = Some v -> w_H W (Z_to_bv 64 a) = false.
Proof.
  intros W mem a v H. destruct (w_H W (Z_to_bv 64 a)) eqn:E; [|reflexivity]. exfalso.
  pose proof (@w_Hoff tfibsegs W _ E) as F.
  unfold aview, YP09.mbyte, mrestrict in H. rewrite E in H.
  unfold YKK.seg_rom, memory_read in H. cbn [Z.of_N] in H. rewrite F in H. discriminate H.
Qed.

Lemma cw_aview_mrd : forall (W : world tfibsegs) mem a, w_H W (Z_to_bv 64 a) = false ->
  aview tfibsegs (w_H W) mem a = option_map (fun b : byte => bv_unsigned b) (mrd rsegs mem (wa a)).
Proof. intros W mem a H. unfold aview, YP09.mbyte, mrestrict, mrd, wa. rewrite H. reflexivity. Qed.

Lemma cw_aview_some : forall (W : world tfibsegs) mem a v, aview tfibsegs (w_H W) mem a = Some v ->
  w_H W (Z_to_bv 64 a) = false /\ exists b : byte, mrd rsegs mem (wa a) = Some b /\ bv_unsigned b = v.
Proof.
  intros W mem a v H. pose proof (cw_aview_vis W mem a v H) as Hv. split; [exact Hv|].
  rewrite (cw_aview_mrd W mem a Hv) in H.
  destruct (mrd rsegs mem (wa a)) as [b|] eqn:E; [|discriminate H]. exists b. split; [reflexivity|].
  injection H as H. exact H.
Qed.

(* A range decode_seg_covers accepts lies in a loaded segment, whose bytes no world hides. *)
Lemma cw_covers_img : forall a n x, decode_seg_covers a n = true -> a <= x < a + n ->
  exists sg, In sg tfibsegs /\ Z.of_N (seg_base sg) <= x < Z.of_N (seg_base sg) + Z.of_N (seg_size sg).
Proof.
  intros a n x H Hx. unfold decode_seg_covers in H. apply existsb_exists in H as (sg & Hin & Hb).
  apply andb_true_iff in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  exists sg. split; [exact Hin | lia].
Qed.

Lemma cw_vis_seg : forall (W : world tfibsegs) a,
  (exists sg, In sg tfibsegs /\ Z.of_N (seg_base sg) <= a < Z.of_N (seg_base sg) + Z.of_N (seg_size sg)) ->
  w_H W (Z_to_bv 64 a) = false.
Proof.
  intros W a (sg & Hin & Hr). destruct (w_H W (Z_to_bv 64 a)) eqn:E; [exfalso|reflexivity].
  pose proof (@w_Hoff tfibsegs W _ E) as F.
  assert (Ha : 0 <= a < kLowMemEnd) by (apply decode_segs_low; exists sg; split; [exact Hin | exact Hr]).
  rewrite (unsigned_lit a) in F by (unfold kLowMemEnd in Ha; lia).
  exact (decode_find_none tfibsegs a 1 sg F Hin ltac:(lia) ltac:(lia)).
Qed.

(* RNG_W W holds on a range of bytes the world does not hide. *)
Lemma cw_rng : forall (W : world tfibsegs) lo len, 0 <= lo -> lo + len <= 2 ^ 64 ->
  (forall b, lo <= b < lo + len -> w_H W (Z_to_bv 64 b) = false) ->
  rng (LCK.RNG_W (world tfibsegs) (@w_H tfibsegs) W) lo len.
Proof.
  intros W lo len H0 H1 H. apply (decode_rng_vis W lo len H0 H1). intros i Hi. apply H. lia.
Qed.

Lemma cw_byte_signed : forall b : byte, bv_unsigned b < 128 -> bv_signed b = bv_unsigned b.
Proof.
  intros b Hb. pose proof (bv_unsigned_in_range 8 b) as R. apply decode_signed_small. lia.
Qed.

(* garr8 of a byte list's values at visible addresses is that byte list under mrd. *)
Lemma cw_bytes_of_garr : forall (W : world tfibsegs) mem p (bs : list byte),
  garr8 tfibsegs (mrestrict (w_H W) mem) p (map DSpec.bz bs) -> 0 <= p -> p + Z.of_nat (length bs) <= 2 ^ 64 ->
  bytes_at rsegs mem p bs.
Proof.
  intros W mem p bs HG H0 Ht. split; [exact H0|]. split; [exact Ht|].
  intros i Hi.
  assert (Hi' : (i < length (map DSpec.bz bs))%nat) by (rewrite length_map; exact Hi).
  pose proof (garr8_mbyte tfibsegs _ p _ i HG Hi') as Hm.
  rewrite (nth_indep _ 0 (DSpec.bz (Z_to_bv 8 0))) in Hm by exact Hi'. rewrite map_nth in Hm.
  assert (Hv : w_H W (Z_to_bv 64 (p + Z.of_nat i)) = false).
  { destruct (w_H W (Z_to_bv 64 (p + Z.of_nat i))) eqn:E; [|reflexivity]. exfalso.
    pose proof (@w_Hoff tfibsegs W _ E) as F.
    unfold mbyte, mrestrict in Hm. rewrite E in Hm.
    unfold YKK.seg_rom, memory_read in Hm. cbn [Z.of_N] in Hm. rewrite F in Hm. discriminate Hm. }
  assert (Em : mrd rsegs mem (wa (p + Z.of_nat i)) = mbyte tfibsegs (mrestrict (w_H W) mem) (p + Z.of_nat i))
    by (unfold mrd, wa, mbyte, mrestrict; rewrite Hv; reflexivity).
  rewrite Em, Hm, (nth_error_nth' bs (Z_to_bv 8 0) Hi). f_equal.
  apply bv_eq. rewrite Z_to_bv_unsigned. unfold DSpec.bz. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

(* The value of the j-th byte of a garr8 array under the overlay view. *)
Lemma cw_garr_view : forall (W : world tfibsegs) mem p (bs : list byte) j,
  garr8 tfibsegs (mrestrict (w_H W) mem) p (map DSpec.bz bs) -> (j < length bs)%nat ->
  aview tfibsegs (w_H W) mem (p + Z.of_nat j) = Some (DSpec.bz (nth j bs (Z_to_bv 8 0))).
Proof.
  intros W mem p bs j HG Hj.
  assert (Hj' : (j < length (map DSpec.bz bs))%nat) by (rewrite length_map; exact Hj).
  pose proof (garr8_mbyte tfibsegs _ p _ j HG Hj') as Hm.
  rewrite (nth_indep _ 0 (DSpec.bz (Z_to_bv 8 0))) in Hm by exact Hj'. rewrite map_nth in Hm.
  unfold aview. rewrite Hm. cbn [option_map]. f_equal. rewrite Z_to_bv_unsigned. unfold DSpec.bz.
  apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

(* A byte read twice at a visible address. *)
Lemma cw_mrd_of_aview : forall (W : world tfibsegs) m m' a,
  w_H W (Z_to_bv 64 a) = false ->
  aview tfibsegs (w_H W) m' a = aview tfibsegs (w_H W) m a ->
  mrd rsegs m' (wa a) = mrd rsegs m (wa a).
Proof. intros W m m' a Hv E. exact (cgb_mrd_eq_of_aview (w_H W) (w_H W) m m' a Hv Hv E). Qed.

Lemma cw_ro8 : forall m a v, bytes_at rsegs m a (le8 v) -> ro_cells rsegs m a [C8 v].
Proof. intros m a v H. split; [cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. exact H. Qed.

(* HOST's six bytes in the image (fuzz_transport.c:109, TCb.v HOST), decided over the loaded segments. *)
Lemma cw_host_rom : forall i, 0 <= i < 6 ->
  option_map (fun b : byte => bv_unsigned b) (YKK.seg_rom tfibsegs (Z_to_bv 64 (CSF_HOST + i)))
  = Some (bv_unsigned (nth (Z.to_nat i) TC.HOST (Z_to_bv 8 0))).
Proof.
  intros i Hi. assert (Hc : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5) by lia.
  destruct Hc as [-> | [-> | [-> | [-> | [-> | ->]]]]]; vm_compute; reflexivity.
Qed.

(* HOST lies in TRANS_RO_RD (its registered global's payload). *)
Lemma cw_host_ro : forall i, 0 <= i < 6 -> trans_in_ro_rd (CSF_HOST + i).
Proof.
  intros i Hi. unfold trans_in_ro_rd, TRANS_RO_RD, TRANS_RO_GLOBALS. apply Exists_exists.
  exists (TRANS_HOST, 6). split; [cbn; tauto|]. unfold in_zr, TRANS_HOST, CSF_HOST. cbn [fst snd]. lia.
Qed.

(* A one-byte constant cell of the record, read at an AR state. *)
Lemma cw_const1 : forall {rc : YM05.RunCeil} (B : asyms) ly S (W : world tfibsegs) mem md a v s,
  @AR rc tfibsegs B ly S W mem md -> In (z1 (ANum a) v) (as_const B ly) -> 0 <= v < 256 -> a = s ->
  aview tfibsegs (w_H W) mem s = Some v.
Proof.
  intros rc B ly S W mem md a v s HAR Hin Hv <-.
  pose proof (am_const _ _ _ _ (proj1 HAR)) as HC.
  pose proof (proj1 (Forall_forall _ _) HC _ Hin) as Hc. unfold z1, c1, cell_holds in Hc.
  cbn [c_at c_w c_val aeval] in Hc. specialize (Hc 0%nat ltac:(lia)). rewrite Z.add_0_r in Hc.
  change (aeval B ly (ANum v)) with v in Hc.
  rewrite Hc. f_equal. unfold le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
  rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite !Z.mod_small by lia. reflexivity.
Qed.

Lemma cw_const1_nn : forall {rc : YM05.RunCeil} (B : asyms) ly S (W : world tfibsegs) mem md a v s,
  @AR rc tfibsegs B ly S W mem md -> In (z1 (ANum a) v) (as_const B ly) -> 0 <= v < 256 -> a = s ->
  aview tfibsegs (w_H W) mem s <> None.
Proof. intros rc B ly S W mem md a v s H1 H2 H3 H4. rewrite (cw_const1 B ly S W mem md a v s H1 H2 H3 H4). discriminate. Qed.

(* The registers of a run's final state read off the register map the run reached (TransportFevt.v
   decode_getr_xeqv), one register at a time: every getr R (Z_to_bv 5 r) becomes getr of the run's map. *)
Ltac cw_regs R XQ :=
  repeat match goal with
  | |- context [YKK.getr R (Z_to_bv 5 ?r)] => rewrite (decode_getr_xeqv _ R XQ (Z_to_bv 5 r))
  end.

Ltac cw_lia := unfold CSF_STK, CSF_FRAME, ESTACK, CSF_HOST, TB_M, TB_g_cfg in *; lia.

Section Walk.
Context {fx : YKK.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation ajournalB := (@ajournal rc YE2k.tfib_sink_head tfibsegs B).

Hypothesis HCELLS : transport_cells B.
Hypothesis HCSF : trans_csf_cells B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis MTL : ameter_laws MT.
Hypothesis ABCMPH : forall fx' : YKK.FPState,
  @abcmp_realizes fx' rc tfibsegs B (transportb_sigma TB___interceptor_trampoline_bcmp).
(* The three footprint runs (check_sent_frame_seg_base.v, check_sent_frame_seg_tail.v). *)
Hypothesis RUN1 : csf_run1_stmt.
Hypothesis MID : csf_mid_stmt.
Hypothesis TAIL : csf_tail_stmt.

Section Call.
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world tfibsegs)
  (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate)
  (W : world tfibsegs) (memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word)
  (fa fp : Z) (frame Bw Bw' : list byte).

Hypothesis HJ : ajournalB STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k.
Hypothesis HRET : YK0s.ret_ok (YKK.getr regs 1).
Hypothesis HRA4 : 4096 <= raZ regs.
Hypothesis HGP : YKK.getr regs 3 = w64 (as_gp B).
Hypothesis HTP : YKK.getr regs 4 = w64 (as_tp B).
Hypothesis H10 : YKK.getr regs 10 = w64 fa.
Hypothesis H11 : YKK.getr regs 11 = w64 (Z.of_nat (length frame)).
Hypothesis H12 : YKK.getr regs 12 = w64 fp.
Hypothesis HAL : spZ regs mod 16 = 0.
Hypothesis HWLO : sp0 - STK <= spZ regs - CSF_STK.
Hypothesis HWHI : spZ regs <= sp0.
Hypothesis HFA0 : 0 < fa.
Hypothesis GFR : garr8 tfibsegs (mrestrict (w_H W) memc) fa (map DSpec.bz frame).
Hypothesis SOF : trans_src_ok B lyc Sc W memc fa (Z.of_nat (length frame)).
Hypothesis OWF : decode_off_win regs CSF_STK fa (Z.of_nat (length frame)).
Hypothesis SFR : trans_sframe_at W memc fp fa (TC.rf frame).
Hypothesis SOP : trans_src_ok B lyc Sc W memc fp SF_SIZE.
Hypothesis OWP : decode_off_win regs CSF_STK fp SF_SIZE.
Hypothesis HROM : trans_rom_view_rd W memc.
Hypothesis HTW : tw_at TMAP_B (aview tfibsegs (w_H W) memc) Bw.
Hypothesis HMOD : TC.check_sent_frame_m Bw frame = Some (Bw', tt).
Hypothesis HNEV : st_nev S + k + CSF_EV <= EV_MAX.

(* ---- what the journal says about the entry state ---- *)

Lemma cw_AR : AR tfibsegs B lyc Sc W memc mdc.
Proof. destruct HJ as (HAR & _). exact HAR. Qed.

Lemma cw_stk_ok : astk_ok STK ly sp0.
Proof.
  destruct HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HS & _). exact HS.
Qed.

Lemma cw_pres : forall a, sp0 - STK <= a < sp0 -> apresent (w_H W) memc a.
Proof.
  destruct HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HP & _). exact HP.
Qed.

Lemma cw_sp_rng : YM05.alloc_ceiling + CSF_STK <= spZ regs /\ spZ regs <= 2 ^ 47.
Proof.
  pose proof cw_stk_ok as (H16 & Hstk0 & Hceil & Hlo & Hhi & H47 & _). lia.
Qed.

(* ---- the model ---- *)

Lemma cw_len : 30 <= Z.of_nat (length frame).
Proof.
  destruct (PCSF.csf_model Bw Bw' frame HMOD) as (_ & Hcode & _).
  destruct (PCSF.csf_rf_ok frame Hcode) as (L30 & _). exact L30.
Qed.

Lemma cw_rdF : decode_rd_ok W memc fa (Z.of_nat (length frame)).
Proof. pose proof cw_len. apply (trans_src_ok_rd B LAWS lyc Sc W memc mdc _ _ cw_AR SOF). lia. Qed.

Lemma cw_rdP : decode_rd_ok W memc fp SF_SIZE.
Proof. apply (trans_src_ok_rd B LAWS lyc Sc W memc mdc _ _ cw_AR SOP). unfold SF_SIZE. lia. Qed.

(* ---- every address csf_mem speaks of: in range, outside the call's stack window, visible ---- *)

Lemma cw_addr_facts : forall a, csf_addr fa fp (Z.of_nat (length frame)) a ->
  0 <= a < 2 ^ 64 /\ (a + 1 <= spZ regs - CSF_STK \/ spZ regs <= a) /\ w_H W (Z_to_bv 64 a) = false.
Proof.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof cw_sp_rng as [SP1 SP2].
  pose proof cw_rdF as (HvF & HraF & HhF & HmF & H0F & H63F).
  pose proof cw_rdP as (HvP & HraP & HhP & HmP & H0P & H63P).
  pose proof OWF as OF. pose proof OWP as OP. pose proof HTW as [LBw HTWr].
  unfold decode_off_win in OF, OP. unfold SF_SIZE in *. unfold CSF_STK, CSF_FRAME, ESTACK in *.
  intros a [Ha | [Ha | [Ha | [Ha | [Ha | [Ha | [Ha | Ha]]]]]]].
  - (* a byte of GOT_CELL_K *)
    assert (Hs : exists sg, In sg tfibsegs /\ Z.of_N (seg_base sg) <= a < Z.of_N (seg_base sg) + Z.of_N (seg_size sg))
      by (apply (cw_covers_img FC.GOT_CELL_K 8 a); [vm_compute; reflexivity | exact Ha]).
    pose proof (decode_segs_low a Hs) as Hlow. unfold kLowMemEnd in Hlow.
    split; [lia|]. split; [left; lia|]. exact (cw_vis_seg W a Hs).
  - (* a byte of CELL_K *)
    assert (Hs : exists sg, In sg tfibsegs /\ Z.of_N (seg_base sg) <= a < Z.of_N (seg_base sg) + Z.of_N (seg_size sg))
      by (apply (cw_covers_img FC.CELL_K 8 a); [vm_compute; reflexivity | exact Ha]).
    pose proof (decode_segs_low a Hs) as Hlow. unfold kLowMemEnd in Hlow.
    split; [lia|]. split; [left; lia|]. exact (cw_vis_seg W a Hs).
  - (* a byte of the struct *)
    split; [lia|]. split; [destruct OP; [left; lia | right; lia]|].
    destruct (aview tfibsegs (w_H W) memc a) as [v|] eqn:Ev; [exact (cw_aview_vis W memc a v Ev)|].
    exfalso. exact (HvP a ltac:(lia) Ev).
  - (* a byte of the frame *)
    split; [lia|]. split; [destruct OF; [left; lia | right; lia]|].
    destruct (aview tfibsegs (w_H W) memc a) as [v|] eqn:Ev; [exact (cw_aview_vis W memc a v Ev)|].
    exfalso. exact (HvF a ltac:(lia) Ev).
  - (* a shadow byte of the struct *)
    destruct Ha as (i & Hi & ->).
    destruct (HraP (fp + i) ltac:(lia)) as (s & Hs & _).
    assert (Ea : shadow_of_addr SHADOW_OFF (fp + i) = (fp + i) / 8 + FC.ASAN_K)
      by (unfold shadow_of_addr, SHADOW_OFF, FC.ASAN_K; lia).
    rewrite Ea in Hs.
    assert (Hxr : 0 <= fp + i < kHighMemEnd) by (unfold amem_range in HmP; lia).
    pose proof (shadow_addr_bounds (fp + i) Hxr) as [SB1 SB2].
    unfold shadow_addr, SHADOW_OFF, FC.ASAN_K in *.
    split; [lia|]. split; [left; lia|]. exact (cw_aview_vis W memc _ s Hs).
  - (* a shadow byte of the frame *)
    destruct Ha as (i & Hi & ->).
    destruct (HraF (fa + i) ltac:(lia)) as (s & Hs & _).
    assert (Ea : shadow_of_addr SHADOW_OFF (fa + i) = (fa + i) / 8 + FC.ASAN_K)
      by (unfold shadow_of_addr, SHADOW_OFF, FC.ASAN_K; lia).
    rewrite Ea in Hs.
    assert (Hxr : 0 <= fa + i < kHighMemEnd) by (unfold amem_range in HmF; lia).
    pose proof (shadow_addr_bounds (fa + i) Hxr) as [SB1 SB2].
    unfold shadow_addr, SHADOW_OFF, FC.ASAN_K in *.
    split; [lia|]. split; [left; lia|]. exact (cw_aview_vis W memc _ s Hs).
  - (* M.desk_known *)
    pose proof (HTWr _ _ _ (a - TB_M) TMAP_B_M ltac:(unfold TW.SZ_M; lia)) as Hv.
    replace (TB_M + (a - TB_M)) with a in Hv by lia.
    split; [unfold TB_M in *; lia|]. split; [left; unfold TB_M in *; lia|]. exact (cw_aview_vis W memc a _ Hv).
  - (* g_cfg.sum_mode *)
    pose proof (HTWr _ _ _ (a - TB_g_cfg) TMAP_B_g_cfg ltac:(unfold TW.SZ_g_cfg; lia)) as Hv.
    replace (TB_g_cfg + (a - TB_g_cfg)) with a in Hv by lia.
    split; [unfold TB_g_cfg in *; lia|]. split; [left; unfold TB_g_cfg in *; lia|].
    exact (cw_aview_vis W memc a _ Hv).
Qed.

Lemma cw_vis : forall a, csf_addr fa fp (Z.of_nat (length frame)) a -> w_H W (Z_to_bv 64 a) = false.
Proof. intros a Ha. exact (proj2 (proj2 (cw_addr_facts a Ha))). Qed.

(* ---- the bundles at the entry ---- *)

Lemma cw_mem0 : forall SB, garr8 tfibsegs (mrestrict (w_H W) memc) fp (map DSpec.bz SB) -> length SB = 80%nat ->
  fp mod 8 = 0 -> csf_mem memc fa fp frame SB Bw.
Proof.
  intros SB GSB LSB Hfp8.
  pose proof (decode_cells_asan B HCELLS lyc Sc W memc mdc cw_AR) as (CK & GCK & _).
  pose proof cw_rdF as (HvF & HraF & HhF & HmF & H0F & H63F).
  pose proof cw_rdP as (HvP & HraP & HhP & HmP & H0P & H63P).
  unfold SF_SIZE in *.
  assert (HTWm : tw_at TMAP_B (fun a => option_map (fun x : byte => bv_unsigned x) (mrd rsegs memc (wa a))) Bw).
  { apply (tw_kept TMAP_B (aview tfibsegs (w_H W) memc)); [exact HTW|].
    intros x (o & b & n & Hin & Hx).
    pose proof (proj2 HTW o b n (x - b) Hin ltac:(lia)) as Hv. replace (b + (x - b)) with x in Hv by lia.
    rewrite <- (cw_aview_mrd W memc x (cw_aview_vis W memc x _ Hv)). reflexivity. }
  split; [exact (cw_ro8 _ _ _ GCK)|].
  split; [exact (cw_ro8 _ _ _ CK)|].
  split; [apply (cw_bytes_of_garr W memc fp SB GSB); rewrite ?LSB; lia|].
  split; [apply (cw_bytes_of_garr W memc fa frame GFR); lia|].
  split.
  { (* the struct's granules: the byte at offset 7 of each lies in the struct, so its shadow value is 0 *)
    intros i Hi.
    pose proof (Z.div_mod (fp + i) 8 ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound (fp + i) 8 ltac:(lia)) as Hmb.
    destruct (HraP (8 * ((fp + i) / 8) + 7) ltac:(Z.div_mod_to_equations; lia)) as (s & Hs & Hok).
    assert (Ediv : (8 * ((fp + i) / 8) + 7) / 8 = (fp + i) / 8).
    { replace (8 * ((fp + i) / 8) + 7) with (7 + ((fp + i) / 8) * 8) by lia. rewrite Z.div_add by lia.
      rewrite (Z.div_small 7 8) by lia. lia. }
    assert (Emod : (8 * ((fp + i) / 8) + 7) mod 8 = 7).
    { replace (8 * ((fp + i) / 8) + 7) with (7 + ((fp + i) / 8) * 8) by lia. rewrite Z.mod_add by lia.
      apply Z.mod_small. lia. }
    assert (Es : s = 0) by (unfold saddr_ok in Hok; rewrite Emod in Hok; lia).
    assert (Ea : shadow_of_addr SHADOW_OFF (8 * ((fp + i) / 8) + 7) = (fp + i) / 8 + FC.ASAN_K).
    { unfold shadow_of_addr, SHADOW_OFF, FC.ASAN_K. rewrite Ediv. lia. }
    rewrite Ea, Es in Hs.
    destruct (cw_aview_some W memc _ 0 Hs) as (_ & b & Hb & Eb).
    rewrite Hb. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. exact Eb. }
  split.
  { (* a frame byte's shadow byte: 0, or above the byte's offset in its granule *)
    intros i Hi.
    destruct (HraF (fa + i) ltac:(lia)) as (s & Hs & Hok).
    assert (Ea : shadow_of_addr SHADOW_OFF (fa + i) = (fa + i) / 8 + FC.ASAN_K)
      by (unfold shadow_of_addr, SHADOW_OFF, FC.ASAN_K; lia).
    rewrite Ea in Hs.
    destruct (cw_aview_some W memc _ s Hs) as (_ & b & Hb & Eb).
    exists b. split; [exact Hb|].
    unfold saddr_ok in Hok. rewrite (cw_byte_signed b ltac:(lia)). lia. }
  split.
  { pose proof (tw_bytes_at rsegs memc TMAP_B Bw TW.OFF_M TB_M TW.SZ_M 0 4 TMAP_B_ok HTWm TMAP_B_M
                  ltac:(lia) ltac:(unfold TW.SZ_M; lia)) as BM.
    rewrite Z.add_0_r in BM. exact BM. }
  exact (tw_bytes_at rsegs memc TMAP_B Bw TW.OFF_g_cfg TB_g_cfg TW.SZ_g_cfg 20 4 TMAP_B_ok HTWm TMAP_B_g_cfg
           ltac:(lia) ltac:(unfold TW.SZ_g_cfg; lia)).
Qed.

Lemma cw_rng0 : csf_rng (LCK.RNG_W (world tfibsegs) (@w_H tfibsegs) W) (spZ regs) fa fp (Z.of_nat (length frame)).
Proof.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof cw_sp_rng as [SP1 SP2]. unfold CSF_STK, CSF_FRAME, ESTACK in *.
  pose proof cw_rdF as (_ & _ & _ & _ & H0F & H63F).
  pose proof cw_rdP as (_ & _ & _ & _ & H0P & H63P). unfold SF_SIZE in *.
  assert (R : forall lo n, 0 < n -> (forall a, lo <= a < lo + n -> csf_addr fa fp (Z.of_nat (length frame)) a) ->
            ExecF.rng (LCK.RNG_W (world tfibsegs) (@w_H tfibsegs) W) lo n).
  { intros lo n Hn H. destruct (cw_addr_facts lo (H lo ltac:(lia))) as (A1 & _).
    destruct (cw_addr_facts (lo + n - 1) (H (lo + n - 1) ltac:(lia))) as (A2 & _).
    apply (cw_rng W); [lia | lia|]. intros b Hb. exact (cw_vis b (H b Hb)). }
  pose proof cw_len as L30.
  split.
  { apply (cw_rng W); [lia | lia|]. intros b Hb.
    exact (proj1 (cw_pres b ltac:(unfold CSF_STK, CSF_FRAME, ESTACK in *; lia))). }
  split; [apply R; [lia|]; intros a Ha; left; exact Ha|].
  split; [apply R; [lia|]; intros a Ha; right; left; exact Ha|].
  split; [apply R; [lia|]; intros a Ha; right; right; left; exact Ha|].
  split; [apply R; [lia|]; intros a Ha; right; right; right; left; exact Ha|].
  split.
  { intros i Hi. apply R; [lia|]. intros a Ha. right; right; right; right; left. exists i. split; [exact Hi | lia]. }
  split.
  { intros i Hi. apply R; [lia|]. intros a Ha. right; right; right; right; right; left. exists i.
    split; [exact Hi | lia]. }
  split; [apply R; [lia|]; intros a Ha; right; right; right; right; right; right; left; exact Ha|].
  apply R; [lia|]. intros a Ha. right; right; right; right; right; right; right. exact Ha.
Qed.

(* ---- the memories after the prologue and after a call: their view outside the call's stack window ---- *)

Definition cw_vk (mm : word -> option byte) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> (a + 1 <= spZ regs - CSF_STK \/ spZ regs <= a) ->
    aview tfibsegs (w_H W) mm a = aview tfibsegs (w_H W) memc a.

Lemma cw_mem_vk : forall mm SB, cw_vk mm -> length SB = 80%nat ->
  csf_mem memc fa fp frame SB Bw -> csf_mem mm fa fp frame SB Bw.
Proof.
  intros mm SB VK LSB M. apply (csf_mem_ext memc mm); [exact LSB | | exact M].
  intros a Ha. destruct (cw_addr_facts a Ha) as (H1 & H2 & H3).
  exact (cw_mrd_of_aview W memc mm a H3 (VK a H1 H2)).
Qed.

Lemma cw_rd_vk : forall mm q n, cw_vk mm -> decode_rd_ok W memc q n ->
  (q + n <= spZ regs - CSF_STK \/ spZ regs <= q) -> decode_rd_ok W mm q n.
Proof.
  intros mm q n VK RD OFF.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof cw_sp_rng as [SP1 SP2]. unfold CSF_STK, CSF_FRAME, ESTACK in *.
  pose proof RD as (_ & _ & _ & Hm & H0 & H63).
  apply (trans_rd_ok_view W W memc mm q n RD).
  - intros a Ha. apply VK; unfold CSF_STK, CSF_FRAME, ESTACK; [lia | destruct OFF; [left; lia | right; lia]].
  - intros s' Hs. apply VK; unfold CSF_STK, CSF_FRAME, ESTACK; [unfold kLowMemEnd, kHighShadowEnd in *; lia | left; unfold kHighShadowEnd in *; lia].
Qed.

Lemma cw_vk_munch : forall mm, munch [(spZ regs + -48, spZ regs)] memc mm -> cw_vk mm.
Proof.
  intros mm MU a Ha Hd. apply aview_eq_of. unfold mrestrict.
  destruct (w_H W (Z_to_bv 64 a)); [reflexivity|].
  pose proof cw_sp_rng as [SP1 SP2]. unfold cw_vk, CSF_STK, CSF_FRAME, ESTACK in *.
  apply MU. cbn [outside]. rewrite unsigned_lit by lia. split; [lia | exact I].
Qed.

Lemma cw_vk_call : forall m1 m2, cw_vk m1 ->
  (forall a, 0 <= a < 2 ^ 64 -> (a + 1 <= spZ regs - CSF_STK \/ spZ regs + -48 <= a) ->
     aview tfibsegs (w_H W) m2 a = aview tfibsegs (w_H W) m1 a) ->
  (forall a, 0 <= a < 2 ^ 64 -> (a + 1 <= spZ regs - CSF_STK \/ spZ regs <= a) ->
     aview tfibsegs (w_H W) m2 a = aview tfibsegs (w_H W) m1 a) -> cw_vk m2.
Proof. intros m1 m2 V1 _ E a H1 H2. rewrite (E a H1 H2). exact (V1 a H1 H2). Qed.

(* ---- the two ranges each call compares, as read ranges at the call state ---- *)

(* HOST's shadow group [0x7fffc1f8, 0x7fffc200): SCALE's four guard bytes (trans_csf_cells), HOST's byte 6
   (transport_cells row 19), HOST's three guard bytes (trans_csf_cells). *)
Lemma cw_host_rd : forall mm ly' S' md', cw_vk mm -> @AR rc tfibsegs B ly' S' W mm md' ->
  decode_rd_ok W mm CSF_HOST 6.
Proof.
  intros mm ly' S' md' VK HAR.
  pose proof cw_sp_rng as [SP1 SP2]. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  unfold CSF_STK, CSF_FRAME, ESTACK in *.
  destruct (HCELLS ly') as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RH & _).
  destruct HCSF as (_ & HC). destruct (HC ly') as (RS32 & RS40 & RS48 & RS56 & RH8 & RH16 & RH24 & _).
  split; [|split; [|split; [|split; [|split]]]].
  - intros a Ha. rewrite (VK a ltac:(cw_lia) ltac:(left; cw_lia)).
    replace a with (CSF_HOST + (a - CSF_HOST)) by lia.
    rewrite (HROM _ (cw_host_ro (a - CSF_HOST) ltac:(lia))), (cw_host_rom (a - CSF_HOST) ltac:(lia)).
    discriminate.
  - intros x Hx. exists 6. split.
    + eapply (cw_const1 B ly' S' W mm md'); [exact HAR | exact RH | lia |].
      unfold FC.shadow_addr, FC.ASAN_K, TRANS_HOST, shadow_of_addr, SHADOW_OFF, CSF_HOST in *.
      Z.div_mod_to_equations. lia.
    + unfold saddr_ok, CSF_HOST in *. right. Z.div_mod_to_equations. lia.
  - intros s' Hs. unfold shadow_addr, SHADOW_OFF, CSF_HOST in Hs. cbn in Hs.
    assert (Hc : s' = 0x7fffc1f8 \/ s' = 0x7fffc1f9 \/ s' = 0x7fffc1fa \/ s' = 0x7fffc1fb \/ s' = 0x7fffc1fc \/
                 s' = 0x7fffc1fd \/ s' = 0x7fffc1fe \/ s' = 0x7fffc1ff) by lia.
    destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]];
      [ eapply cw_const1_nn; [exact HAR | exact RS32 | lia | reflexivity]
      | eapply cw_const1_nn; [exact HAR | exact RS40 | lia | reflexivity]
      | eapply cw_const1_nn; [exact HAR | exact RS48 | lia | reflexivity]
      | eapply cw_const1_nn; [exact HAR | exact RS56 | lia | reflexivity]
      | eapply cw_const1_nn; [exact HAR | exact RH | lia | reflexivity]
      | eapply cw_const1_nn; [exact HAR | exact RH8 | lia | reflexivity]
      | eapply cw_const1_nn; [exact HAR | exact RH16 | lia | reflexivity]
      | eapply cw_const1_nn; [exact HAR | exact RH24 | lia | reflexivity] ].
  - unfold amem_range, kLowMemEnd, CSF_HOST. lia.
  - unfold CSF_HOST. lia.
  - unfold CSF_HOST. lia.
Qed.

(* M + 4's shadow group [0x800b3db8, 0x800b3dc0): g_last_counter's last granule (4) and its three guard bytes
   (trans_csf_cells), then M's zero shadow (decode_zshadow_rd at TB_M, + 8, + 16, + 24). *)
Lemma cw_m4_rd : forall mm ly' S' md', cw_vk mm -> @AR rc tfibsegs B ly' S' W mm md' ->
  decode_rd_ok W mm (TB_M + 4) 6.
Proof.
  intros mm ly' S' md' VK HAR.
  pose proof cw_sp_rng as [SP1 SP2]. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof HTW as [LBw HTWr].
  destruct HCSF as (HZ & HC). destruct (HC ly') as (_ & _ & _ & _ & _ & _ & _ & RG & RG8 & RG16 & RG24).
  assert (ZS : forall T s, T mod 8 = 0 -> TB_M <= T -> T + 8 <= TB_M + TW.SZ_M -> FC.shadow_addr T = s ->
            aview tfibsegs (w_H W) mm s = Some 0).
  { intros T s' H1 H2 H3 <-. exact (decode_zshadow_rd B ly' S' W mm md' TB_M (TB_M + TW.SZ_M) T HAR H1 H2 H3 HZ). }
  split; [|split; [|split; [|split; [|split]]]].
  - intros a Ha. rewrite (VK a ltac:(cw_lia) ltac:(left; cw_lia)).
    pose proof (HTWr _ _ _ (a - TB_M) TMAP_B_M ltac:(unfold TW.SZ_M; lia)) as Hv.
    replace (TB_M + (a - TB_M)) with a in Hv by lia. rewrite Hv. discriminate.
  - intros x Hx. exists 0. split; [|left; reflexivity].
    apply (ZS (8 * (x / 8))); unfold TB_M, TW.SZ_M, FC.shadow_addr, FC.ASAN_K, shadow_of_addr, SHADOW_OFF in *;
      Z.div_mod_to_equations; lia.
  - intros s' Hs. unfold shadow_addr, SHADOW_OFF, TB_M in Hs. cbn in Hs.
    assert (Hc : s' = 0x800b3db8 \/ s' = 0x800b3db9 \/ s' = 0x800b3dba \/ s' = 0x800b3dbb \/ s' = 0x800b3dbc \/
                 s' = 0x800b3dbd \/ s' = 0x800b3dbe \/ s' = 0x800b3dbf) by lia.
    destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]];
      [ eapply cw_const1_nn; [exact HAR | exact RG | lia | reflexivity]
      | eapply cw_const1_nn; [exact HAR | exact RG8 | lia | reflexivity]
      | eapply cw_const1_nn; [exact HAR | exact RG16 | lia | reflexivity]
      | eapply cw_const1_nn; [exact HAR | exact RG24 | lia | reflexivity]
      | rewrite (ZS TB_M); [discriminate | reflexivity | unfold TW.SZ_M; lia | unfold TW.SZ_M; lia | reflexivity]
      | rewrite (ZS (TB_M + 8)); [discriminate | reflexivity | lia | unfold TW.SZ_M; lia | reflexivity]
      | rewrite (ZS (TB_M + 16)); [discriminate | reflexivity | lia | unfold TW.SZ_M; lia | reflexivity]
      | rewrite (ZS (TB_M + 24)); [discriminate | reflexivity | lia | unfold TW.SZ_M; lia | reflexivity] ].
  - unfold amem_range, kLowMemEnd, TB_M. lia.
  - unfold TB_M. lia.
  - unfold TB_M. lia.
Qed.

(* The bytes the first call compares agree: f->src's six bytes are HOST (the model). *)
Lemma cw_cmp1 : forall mm, cw_vk mm -> forall i, 0 <= i < 6 ->
  aview tfibsegs (w_H W) mm (fa + 6 + i) = aview tfibsegs (w_H W) mm (CSF_HOST + i).
Proof.
  intros mm VK i Hi.
  pose proof cw_rdF as (_ & _ & _ & _ & H0F & H63F). pose proof cw_len as L30.
  pose proof OWF as OF. unfold decode_off_win in OF. pose proof cw_sp_rng as [SP1 SP2].
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct (PCSF.csf_model Bw Bw' frame HMOD) as (_ & _ & HHOST & _).
  rewrite (VK (fa + 6 + i) ltac:(cw_lia) ltac:(destruct OF; [left | right]; cw_lia)).
  rewrite (VK (CSF_HOST + i) ltac:(cw_lia) ltac:(left; cw_lia)).
  rewrite (HROM _ (cw_host_ro i Hi)), (cw_host_rom i Hi).
  replace (fa + 6 + i) with (fa + Z.of_nat (Z.to_nat (6 + i))) by lia.
  rewrite (cw_garr_view W memc fa frame (Z.to_nat (6 + i)) GFR ltac:(lia)).
  f_equal. unfold DSpec.bz. f_equal. rewrite <- HHOST.
  rewrite (tw_nth_sub frame 6 6 (Z.to_nat i) (Z_to_bv 8 0)) by lia. f_equal. lia.
Qed.

(* The bytes the second call compares agree: f->dst's six bytes are M.desk (the model). *)
Lemma cw_cmp2 : forall mm, cw_vk mm -> forall i, 0 <= i < 6 ->
  aview tfibsegs (w_H W) mm (fa + i) = aview tfibsegs (w_H W) mm (TB_M + 4 + i).
Proof.
  intros mm VK i Hi.
  pose proof cw_rdF as (_ & _ & _ & _ & H0F & H63F). pose proof cw_len as L30.
  pose proof OWF as OF. unfold decode_off_win in OF. pose proof cw_sp_rng as [SP1 SP2].
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof HTW as [LBw HTWr].
  destruct (PCSF.csf_model Bw Bw' frame HMOD) as (_ & _ & _ & _ & HDESK & _).
  rewrite (VK (fa + i) ltac:(cw_lia) ltac:(destruct OF; [left | right]; cw_lia)).
  rewrite (VK (TB_M + 4 + i) ltac:(cw_lia) ltac:(left; cw_lia)).
  pose proof (HTWr _ _ _ (4 + i) TMAP_B_M ltac:(unfold TW.SZ_M; lia)) as Hv.
  replace (TB_M + (4 + i)) with (TB_M + 4 + i) in Hv by lia. rewrite Hv.
  replace (fa + i) with (fa + Z.of_nat (Z.to_nat i)) by lia.
  rewrite (cw_garr_view W memc fa frame (Z.to_nat i) GFR ltac:(lia)).
  f_equal. unfold DSpec.bz. f_equal.
  assert (E1 : nth (Z.to_nat i) frame (Z_to_bv 8 0) = nth (Z.to_nat i) (TW.sub frame 0 6) (Z_to_bv 8 0))
    by (rewrite (tw_nth_sub frame 0 6 (Z.to_nat i) (Z_to_bv 8 0)) by lia; reflexivity).
  rewrite E1, HDESK. rewrite (tw_nth_sub Bw 4 6 (Z.to_nat i) (Z_to_bv 8 0)) by (first [lia | rewrite LBw; unfold TW.W_LEN; lia]).
  f_equal. unfold TW.OFF_M. lia.
Qed.

(* ---- the inner journal ---- *)

Lemma cw_inner : ajournalB CSF_STK (spZ regs) [] lyc Sc W memc mdc [] lyc Sc W memc mdc 0.
Proof.
  pose proof cw_stk_ok as (Hal16 & _).
  apply (@ajournal_sub_init rc YE2k.tfib_sink_head tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
           CSF_STK (spZ regs) [] (spZ regs - sp0) HJ);
    [lia | rewrite Zminus_mod, HAL, Hal16; reflexivity | lia | unfold CSF_STK, CSF_FRAME, ESTACK; lia | lia].
Qed.

(* ---- the close: the inner journal and the caller's compose into the statement's post ---- *)

Lemma cw_close : forall (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model),
  ajournalB CSF_STK (spZ regs) [] lyc Sc W memc mdc [] lyc Sc W mem2 md2 0 ->
  aregs_preserved regs regs2 ->
  SRr tfibsegs W (mkCfg (@YKK.mkst fx regs2 (YKK.getr regs 1) mem2 (YKK.seg_rom tfibsegs)) md2)
    (@transport_csf_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw').
Proof.
  intros regs2 mem2 md2 JI HP.
  destruct (PCSF.csf_model Bw Bw' frame HMOD) as (EBw & _).
  apply SRr_ret. unfold transport_csf_post, decode_cg_post.
  exists lyc, Sc, regs2, mem2, md2, 0.
  split; [reflexivity|].
  split; [unfold CSF_EV; lia|].
  split.
  { pose proof (ajournal_sub_tok tfibsegs B LAWS decode_segs_low STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
                  CSF_STK (spZ regs) [] [] lyc Sc W mem2 md2 0 HJ JI HWLO HWHI
                  ltac:(intros a (r & Hr & _); destruct Hr)) as J.
    cbn [app] in J. exact J. }
  split; [exact HP|].
  split; [reflexivity|].
  split; [apply Permutation_refl|].
  split.
  { exact (acall_kept_of_journal tfibsegs B decode_segs_low CSF_STK (spZ regs) [] [] lyc Sc W memc mdc
             lyc Sc W mem2 md2 0 (fun _ => False) JI cw_AR
             ltac:(intros a (r & Hr & _); destruct Hr)
             ltac:(intros bq mq i Hb _ _; exact Hb)
             sink_closed_nil). }
  split; [exact (mle_start MT Sc MTL) | exact EBw].
Qed.

(* The registers the epilogue restores are the caller's. *)
Lemma cw_pres_ret : forall (spx r5 r6 r7 r10 r11 r12 r13 r14 r15 r16 r17 r28 r29 r30 r31 : word),
  bv_unsigned spx = spZ regs ->
  aregs_preserved regs
    (mkR (YKK.getr regs 1) spx (YKK.getr regs 3) (YKK.getr regs 4) r5 r6 r7 (YKK.getr regs 8) (YKK.getr regs 9)
         r10 r11 r12 r13 r14 r15 r16 r17 (YKK.getr regs 18) (YKK.getr regs 19) (YKK.getr regs 20) (YKK.getr regs 21)
         (YKK.getr regs 22) (YKK.getr regs 23) (YKK.getr regs 24) (YKK.getr regs 25) (YKK.getr regs 26)
         (YKK.getr regs 27) r28 r29 r30 r31).
Proof.
  intros spx r5 r6 r7 r10 r11 r12 r13 r14 r15 r16 r17 r28 r29 r30 r31 Hsp r Hr.
  unfold acallee_saved in Hr.
  assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
               r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  repeat (destruct Hc as [Hc|Hc]); subst r; try reflexivity.
  apply bv_eq. exact Hsp.
Qed.

(* The callee-saved registers of a map xregs_eqv to one that keeps them. *)
Lemma cw_pres_x : forall R R' : bvmap 5 word,
  aregs_preserved regs R -> Regs6ss.xregs_eqv R R' -> aregs_preserved regs R'.
Proof. intros R R' HP XQ r Hr. rewrite (decode_getr_xeqv R R' XQ). exact (HP r Hr). Qed.

(* A writable stack range from the inner journal's present bytes. *)
Lemma cw_stk_of_journal : forall mem2 md2 hi,
  ajournalB CSF_STK (spZ regs) [] lyc Sc W memc mdc [] lyc Sc W mem2 md2 0 ->
  spZ regs - CSF_STK <= hi -> hi <= spZ regs ->
  stk rsegs mem2 (spZ regs - CSF_STK) hi.
Proof.
  intros mem2 md2 hi JI H1 H2.
  pose proof cw_sp_rng as [SP1 SP2]. unfold CSF_STK, CSF_FRAME, ESTACK in *. pose proof asan_consts as (C1 & _).
  destruct JI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HP & _).
  apply (decode_stk_present (w_H W)); [lia | lia|]. intros a Ha. apply HP. lia.
Qed.

(* The frame the prologue wrote is kept by a call whose window lies below it. *)
Lemma cw_frame_call : forall (mem1 mem2 : word -> option byte) (md1 : Model) (cs : list cell),
  ajournalB CSF_STK (spZ regs) [] lyc Sc W memc mdc [] lyc Sc W mem1 md1 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> (a + 1 <= spZ regs - CSF_STK \/ spZ regs + -48 <= a) ->
     aview tfibsegs (w_H W) mem2 a = aview tfibsegs (w_H W) mem1 a) ->
  (forall a, apresent (w_H W) mem1 a -> apresent (w_H W) mem2 a) ->
  rw_cells rsegs mem1 (spZ regs + -48) cs -> Z.of_nat (cells_size cs) <= 48 ->
  rw_cells rsegs mem2 (spZ regs + -48) cs.
Proof.
  intros mem1 mem2 md1 cs JI Hview Happ FR Hsz.
  pose proof cw_sp_rng as [SP1 SP2]. unfold CSF_STK, CSF_FRAME, ESTACK in *. pose proof asan_consts as (C1 & _).
  pose proof JI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HP & _).
  apply (decode_rw_cells_eq mem1 mem2 (spZ regs + -48) cs FR).
  intros i Hi.
  assert (Hp1 : apresent (w_H W) mem1 (spZ regs + -48 + i)) by (apply HP; lia).
  exact (decode_byte_eq (w_H W) (w_H W) mem1 mem2 (spZ regs + -48 + i) Hp1 (Happ _ Hp1)
           (Hview (spZ regs + -48 + i) ltac:(lia) ltac:(right; lia))).
Qed.

(* One call of bcmp on the inner journal (YCbq.v aj_bcmp_at at the statement's abcmp_realizes). *)
Lemma cw_bcmp : forall (regsT : bvmap 5 word) (memT : word -> option byte) (mdT : Model)
    (x y n : Z) (raw : word) (Q : world tfibsegs -> config -> Prop),
  ajournalB CSF_STK (spZ regs) [] lyc Sc W memc mdc [] lyc Sc W memT mdT 0 ->
  YKK.getr regsT 10 = w64 x -> YKK.getr regsT 11 = w64 y -> YKK.getr regsT 12 = w64 n ->
  0 <= n <= 8 ->
  decode_rd_ok W memT x n -> decode_rd_ok W memT y n ->
  (x + n <= spZ regs - CSF_STK \/ spZ regs <= x) ->
  (y + n <= spZ regs - CSF_STK \/ spZ regs <= y) ->
  YKK.getr regsT 2 = Z_to_bv 64 (spZ regs + -48) ->
  YKK.getr regsT 3 = w64 (as_gp B) -> YKK.getr regsT 4 = w64 (as_tp B) ->
  YKK.getr regsT 1 = raw -> YK0s.ret_ok raw ->
  (forall i, 0 <= i < n -> aview tfibsegs (w_H W) memT (x + i) = aview tfibsegs (w_H W) memT (y + i)) ->
  (forall (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model),
     ajournalB CSF_STK (spZ regs) [] lyc Sc W memc mdc [] lyc Sc W mem2 md2 0 ->
     aregs_preserved regsT regs2 -> YKK.getr regs2 10 = w64 0 ->
     (forall a, 0 <= a < 2 ^ 64 -> (a + 1 <= spZ regs - CSF_STK \/ spZ regs + -48 <= a) ->
        aview tfibsegs (w_H W) mem2 a = aview tfibsegs (w_H W) memT a) ->
     (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a) ->
     SRr tfibsegs W (mkCfg (@YKK.mkst fx regs2 raw mem2 (YKK.seg_rom tfibsegs)) md2) Q) ->
  SRr tfibsegs W
    (mkCfg (@YKK.mkst fx regsT (Z_to_bv 64 (transportb_sigma TB___interceptor_trampoline_bcmp)) memT
              (YKK.seg_rom tfibsegs)) mdT) Q.
Proof.
  intros regsT memT mdT x y n raw Q JI R10 R11 R12 Hn RDX RDY OFX OFY R2 R3 R4 R1 HRAW HEQ K.
  pose proof cw_sp_rng as [SP1 SP2]. unfold CSF_STK, CSF_FRAME, ESTACK in *.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof RDX as (HvX & HraX & HhX & HmX & H0X & H63X).
  pose proof RDY as (HvY & HraY & HhY & HmY & H0Y & H63Y).
  assert (HspT : spZ regsT = spZ regs + -48)
    by (unfold spZ; rewrite R2; rewrite unsigned_lit; [reflexivity | lia]).
  eapply SRr_bind.
  { apply (@aj_bcmp_at fx rc YE2k.tfib_sink_head tfibsegs B LAWS decode_segs_low
             (transportb_sigma TB___interceptor_trampoline_bcmp) (ABCMPH fx) W regsT memT
             CSF_STK (spZ regs) [] lyc Sc W memc mdc [] lyc Sc mdT 0 x y n (-48) raw JI).
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
    - unfold CSF_STK, CSF_FRAME, ESTACK; lia.
    - exact R3.
    - exact R4.
    - exact R1.
    - exact HRAW.
    - intros a Ha. split; [exact (HvX a Ha)|]. rewrite HspT. unfold ESTACK. lia.
    - intros a Ha. split; [exact (HvY a Ha)|]. rewrite HspT. unfold ESTACK. lia.
    - intros a Ha. unfold ESTACK. lia.
    - intros a Ha. unfold ESTACK. lia.
    - exact HmX.
    - exact HmY.
    - exact HraX.
    - intros _. exact HhX.
    - exact HraY.
    - intros _. exact HhY. }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & JI2 & HP2 & Hv & Hiff & Hview & Happ).
  apply (K regs2 mem2 md2 JI2 HP2).
  - rewrite Hv. apply Hiff. exact HEQ.
  - intros a Ha1 Ha2. apply Hview; [lia|]. unfold ESTACK. destruct Ha2; lia.
  - exact Happ.
Qed.

(* ---- the walk ---- *)

Lemma cw_holds :
  SRr tfibsegs W (@cfg_at fx tfibsegs (transportb_sigma TB_check_sent_frame) regs memc mdc)
    (@transport_csf_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw').
Proof.
  pose proof cw_sp_rng as [SP1 SP2]. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof RUN1 as HRUN1. pose proof MID as HMID. pose proof TAIL as HTAIL.
  unfold csf_run1_stmt in HRUN1. unfold csf_mid_stmt in HMID. unfold csf_tail_stmt in HTAIL.
  assert (GRET : ret_pc (YKK.getr regs (Z_to_bv 5 1)) = YKK.getr regs (Z_to_bv 5 1))
    by exact (LeafCgFacts.ret_ok_stmt_YK0s _ HRET).
  assert (G10 : YKK.getr regs (Z_to_bv 5 10) = w64 fa) by exact H10.
  assert (G11 : YKK.getr regs (Z_to_bv 5 11) = w64 (Z.of_nat (length frame))) by exact H11.
  assert (G12 : YKK.getr regs (Z_to_bv 5 12) = w64 fp) by exact H12.
  (* the model and the struct *)
  destruct (PCSF.csf_model Bw Bw' frame HMOD) as (EBw & Hcode & HHOST & HDK & HDESK & HSYS & HN & HZ & HSUM).
  destruct (PCSF.csf_rf_ok frame Hcode) as (L30 & Hsrc & Hdst & Hbody & Hbl0 & Hbl & Hb16).
  pose proof SFR as (Hfp0 & Hfp8 & SB & GSB & LSB & SB0 & SB8 & SB16 & SB24 & SB26 & SB28 & SB30 & SB32 & SB36 & SB40
                     & SB41 & SB48 & SB56 & SB64 & SB72).
  pose proof cw_rdF as RDF. pose proof cw_rdP as RDP.
  pose proof (cw_mem0 SB GSB LSB Hfp8) as MEM0.
  pose proof cw_rng0 as RNG0.
  assert (BND0 : csf_bnd fa fp (Z.of_nat (length frame))).
  { pose proof RDF as (_ & _ & _ & _ & H0F & H63F). pose proof RDP as (_ & _ & _ & _ & H0P & H63P).
    unfold SF_SIZE in *. split; [lia|]. split; [exact Hfp8|]. split; [lia|]. split; lia. }
  assert (FX0 : csf_fx fa frame SB Bw (DS.sf_body_len (TC.rf frame)) (DS.sf_sum (TC.rf frame))).
  { split; [exact LSB|].
    split; [rewrite SB0; exact Hcode|].
    split; [rewrite SB8; unfold TCt.sf_ptr; rewrite Hcode, Hdst; change (0 =? DS.SPEC_OK) with true; cbv iota; lia|].
    split; [rewrite SB16; unfold TCt.sf_ptr; rewrite Hcode, Hsrc; change (0 =? DS.SPEC_OK) with true; cbv iota; lia|].
    split; [rewrite SB48; unfold TCt.sf_ptr; rewrite Hcode, Hbody; change (0 =? DS.SPEC_OK) with true; cbv iota; lia|].
    split; [exact SB56|]. split; [exact SB28|].
    split; [exact HDK|].
    split; [exact Hbl0|]. split; [exact Hbl|]. split; [exact Hb16|].
    split; [exact HSYS|].
    split; [rewrite HN; destruct (Z.ltb_spec (30 + DS.sf_body_len (TC.rf frame)) 60); lia|].
    split.
    { intros kk Hkk. rewrite <- (Z2Nat.id kk) by lia.
      apply (PCSF.csf_zero frame (Z.to_nat (30 + DS.sf_body_len (TC.rf frame))) HZ). lia. }
    split; [|exact (tw_len TMAP_B _ Bw HTW)].
    rewrite HSUM. change (TW.s32_at Bw 65044) with (TW.Cfg_sum_mode Bw).
    destruct (TW.Cfg_sum_mode Bw =? 1); [reflexivity|]. apply PCSF.csf_sum_at; lia. }
  assert (SEP0 : csf_sep (spZ regs) fa fp (Z.of_nat (length frame))).
  { intros a Ha. destruct (cw_addr_facts a Ha) as (A1 & A2 & _). split; [exact A1|].
    unfold CSF_STK, CSF_FRAME, ESTACK in A2. lia. }
  (* the inner journal at the entry *)
  pose proof cw_inner as JI0.
  pose proof JI0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & _).
  assert (STK0 : stk rsegs memc (spZ regs - CSF_STK) (spZ regs))
    by (apply (decode_stk_present (w_H W)); [cw_lia | cw_lia | intros a Ha; apply Hpres0; lia]).
  (* ---- run 1: the entry to the first call ---- *)
  eapply (decode_run W regs memc mdc (transportb_sigma TB_check_sent_frame)).
  { unfold LCK.ms_of_regs. rewrite G10, G11, G12.
    eapply HRUN1 with (lo := spZ regs - CSF_STK);
      [exact MEM0 | exact RNG0 | exact BND0 | exact FX0 | exact SEP0 | exact STK0 |
       change (bv_unsigned (YKK.getr regs (Z_to_bv 5 2))) with (spZ regs); cw_lia]. }
  intros msT msT' mdT (m1 & junk & EmsT & MU & WM & ST1 & FR & MEM1) EQVT HGT SBMT.
  subst msT.
  change (bv_unsigned (YKK.getr regs (Z_to_bv 5 2))) with (spZ regs) in MU, FR, ST1.
  destruct (decode_eqv_mkst _ (Z_to_bv 64 CSF_BCMP) m1 msT' EQVT) as (RT & -> & XQT).
  assert (JI1 : ajournalB CSF_STK (spZ regs) [] lyc Sc W memc mdc [] lyc Sc W m1 mdT 0).
  { apply (@cgb_j_frame rc B LAWS CSF_STK 48 lyc Sc W memc mdc (spZ regs) lyc Sc W memc mdc 0 m1 mdT);
      [unfold CSF_STK, CSF_FRAME, ESTACK; lia | exact cw_inner | | exact HGT | exact SBMT].
    intros x Hx. apply MU. cbn [outside]. split; [lia | exact I]. }
  pose proof (cw_vk_munch m1 MU) as VK1.
  pose proof OWF as OF. unfold decode_off_win in OF.
  (* ---- the first call: bcmp (f->src, HOST, 6) ---- *)
  eapply cw_bcmp with (x := fa + 6) (y := CSF_HOST) (n := 6) (raw := Z_to_bv 64 CSF_RET1).
  { exact JI1. }
  { rewrite (decode_getr_xeqv _ _ XQT). reflexivity. }
  { rewrite (decode_getr_xeqv _ _ XQT). reflexivity. }
  { rewrite (decode_getr_xeqv _ _ XQT). reflexivity. }
  { lia. }
  { apply (trans_rd_ok_sub W m1 fa (Z.of_nat (length frame))); [| lia | lia | lia].
    apply (cw_rd_vk m1 _ _ VK1 RDF). destruct OF; [left | right]; lia. }
  { exact (cw_host_rd m1 lyc Sc mdT VK1 (proj1 JI1)). }
  { destruct OF; [left | right]; lia. }
  { left. cw_lia. }
  { rewrite (decode_getr_xeqv _ _ XQT). reflexivity. }
  { rewrite (decode_getr_xeqv _ _ XQT). exact HGP. }
  { rewrite (decode_getr_xeqv _ _ XQT). exact HTP. }
  { rewrite (decode_getr_xeqv _ _ XQT). reflexivity. }
  { apply YK0s.ret_ok_even. vm_compute. reflexivity. }
  { exact (cw_cmp1 m1 VK1). }
  intros regs2 mem2 md2 JI2 HP2 H2a0 Hview2 Happ2.
  assert (VK2 : cw_vk mem2).
  { apply (cw_vk_call m1 mem2 VK1 Hview2). intros a H1 H2. apply Hview2; [exact H1|].
    destruct H2; [left | right]; cw_lia. }
  pose proof (cw_mem_vk mem2 SB VK2 LSB MEM0) as MEM2.
  pose proof (cw_frame_call m1 mem2 mdT _ JI1 Hview2 Happ2 FR ltac:(unfold csf_fr; cbn [cells_size csize]; lia))
    as FR2.
  assert (GA0 : YKK.getr regs2 (Z_to_bv 5 10) = w64 0) by exact H2a0.
  (* ---- run 2: the first call's return to the second call ---- *)
  eapply (decode_run W regs2 mem2 md2 CSF_RET1).
  { unfold LCK.ms_of_regs.
    rewrite (HP2 2 ltac:(unfold acallee_saved; lia)), (HP2 3 ltac:(unfold acallee_saved; lia)),
      (HP2 4 ltac:(unfold acallee_saved; lia)), (HP2 8 ltac:(unfold acallee_saved; lia)),
      (HP2 9 ltac:(unfold acallee_saved; lia)), (HP2 18 ltac:(unfold acallee_saved; lia)),
      (HP2 19 ltac:(unfold acallee_saved; lia)), (HP2 20 ltac:(unfold acallee_saved; lia)),
      (HP2 21 ltac:(unfold acallee_saved; lia)), (HP2 22 ltac:(unfold acallee_saved; lia)),
      (HP2 23 ltac:(unfold acallee_saved; lia)), (HP2 24 ltac:(unfold acallee_saved; lia)),
      (HP2 25 ltac:(unfold acallee_saved; lia)), (HP2 26 ltac:(unfold acallee_saved; lia)),
      (HP2 27 ltac:(unfold acallee_saved; lia)), GA0.
    cw_regs RT XQT.
    eapply HMID; first [exact MEM2 | exact RNG0 | exact BND0 | exact FX0]. }
  intros msU msU' mdU EmsU EQVU _ SBMU.
  cbv beta in EmsU. subst msU.
  destruct (decode_eqv_mkst _ (Z_to_bv 64 CSF_BCMP) mem2 msU' EQVU) as (RU & -> & XQU).
  pose proof (@cgb_j_sbm rc B LAWS CSF_STK (spZ regs) [] lyc Sc W memc mdc [] lyc Sc W mem2 md2 0 mdU JI2 SBMU)
    as JI2'.
  (* ---- the second call: bcmp (f->dst, M + 4, 6) ---- *)
  eapply cw_bcmp with (x := fa) (y := TB_M + 4) (n := 6) (raw := Z_to_bv 64 CSF_RET2).
  { exact JI2'. }
  { rewrite (decode_getr_xeqv _ _ XQU). reflexivity. }
  { rewrite (decode_getr_xeqv _ _ XQU). reflexivity. }
  { rewrite (decode_getr_xeqv _ _ XQU). reflexivity. }
  { lia. }
  { apply (trans_rd_ok_sub W mem2 fa (Z.of_nat (length frame))); [| lia | lia | lia].
    apply (cw_rd_vk mem2 _ _ VK2 RDF). destruct OF; [left | right]; lia. }
  { exact (cw_m4_rd mem2 lyc Sc mdU VK2 (proj1 JI2')). }
  { destruct OF; [left | right]; lia. }
  { left. cw_lia. }
  { rewrite (decode_getr_xeqv _ _ XQU). reflexivity. }
  { rewrite (decode_getr_xeqv _ _ XQU). exact HGP. }
  { rewrite (decode_getr_xeqv _ _ XQU). exact HTP. }
  { rewrite (decode_getr_xeqv _ _ XQU). reflexivity. }
  { apply YK0s.ret_ok_even. vm_compute. reflexivity. }
  { exact (cw_cmp2 mem2 VK2). }
  intros regs3 mem3 md3 JI3 HP3 H3a0 Hview3 Happ3.
  assert (VK3 : cw_vk mem3).
  { apply (cw_vk_call mem2 mem3 VK2 Hview3). intros a H1 H2. apply Hview3; [exact H1|].
    destruct H2; [left | right]; cw_lia. }
  pose proof (cw_mem_vk mem3 SB VK3 LSB MEM0) as MEM3.
  pose proof (cw_frame_call mem2 mem3 mdU _ JI2' Hview3 Happ3 FR2 ltac:(unfold csf_fr; cbn [cells_size csize]; lia))
    as FR3.
  pose proof (cw_stk_of_journal mem3 md3 (spZ regs + -48) JI3 ltac:(cw_lia) ltac:(lia)) as ST3.
  assert (GB0 : YKK.getr regs3 (Z_to_bv 5 10) = w64 0) by exact H3a0.
  (* ---- run 3: the second call's return to the `ret` ---- *)
  eapply (decode_run W regs3 mem3 md3 CSF_RET2).
  { unfold LCK.ms_of_regs.
    rewrite (HP3 2 ltac:(unfold acallee_saved; lia)), (HP3 3 ltac:(unfold acallee_saved; lia)),
      (HP3 4 ltac:(unfold acallee_saved; lia)), (HP3 8 ltac:(unfold acallee_saved; lia)),
      (HP3 9 ltac:(unfold acallee_saved; lia)), (HP3 18 ltac:(unfold acallee_saved; lia)),
      (HP3 19 ltac:(unfold acallee_saved; lia)), (HP3 20 ltac:(unfold acallee_saved; lia)),
      (HP3 21 ltac:(unfold acallee_saved; lia)), (HP3 22 ltac:(unfold acallee_saved; lia)),
      (HP3 23 ltac:(unfold acallee_saved; lia)), (HP3 24 ltac:(unfold acallee_saved; lia)),
      (HP3 25 ltac:(unfold acallee_saved; lia)), (HP3 26 ltac:(unfold acallee_saved; lia)),
      (HP3 27 ltac:(unfold acallee_saved; lia)), GB0.
    cw_regs RU XQU.
    eapply HTAIL with (lo := spZ regs - CSF_STK);
      first [exact MEM3 | exact RNG0 | exact BND0 | exact FX0 | exact ST3 | exact FR3
            | change (bv_unsigned (YKK.getr regs (Z_to_bv 5 2))) with (spZ regs); cw_lia]. }
  intros msV msV' mdV (x5 & x6 & x7 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & spx
                       & EmsV & Hsp & ST4) EQVV _ SBMV.
  subst msV.
  destruct (decode_eqv_mkst _ _ mem3 msV' EQVV) as (RV & -> & XQV).
  rewrite GRET.
  eapply cw_close.
  - exact (@cgb_j_sbm rc B LAWS CSF_STK (spZ regs) [] lyc Sc W memc mdc [] lyc Sc W mem3 md3 0 mdV JI3 SBMV).
  - refine (cw_pres_x _ RV _ XQV).
    apply cw_pres_ret. exact Hsp.
Qed.

End Call.
End Walk.

(* The walk under the three run statements: the statement of lib/B/Prog/check_sent_frame_cg.v. The statement's
   trans_ro_rd_unowned and trans_rom_no_errno are not used: HOST's bytes are read once, at the first call, straight
   from the call state's trans_rom_view_rd. *)
Lemma transport_check_sent_frame_cg_holds_of_runs :
  csf_run1_stmt -> csf_mid_stmt -> csf_tail_stmt ->
  forall fx rc B MT, @transport_check_sent_frame_cg_holds_stmt fx rc B MT.
Proof.
  intros RUN1 MID TAIL fx rc B MT HCELLS HCSF HOWN HERR LAWS MTL ABCMP.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fa fp frame Bw Bw'.
  intros HJ HRET HRA4 HGP HTP H10 H11 H12 HAL HWLO HWHI HFA0 GFR SOF OWF SFR SOP OWP HROM HTW HMOD HNEV.
  eapply cw_holds with (fa := fa) (fp := fp) (frame := frame) (Bw := Bw) (Bw' := Bw');
    first [ exact HCELLS | exact HCSF | exact LAWS | exact MTL | exact ABCMP | exact RUN1 | exact MID | exact TAIL
          | exact HJ | exact HRET | exact HRA4
          | exact HGP | exact HTP | exact H10 | exact H11 | exact H12 | exact HAL | exact HWLO | exact HWHI
          | exact HFA0 | exact GFR | exact SOF | exact OWF | exact SFR | exact SOP | exact OWP | exact HROM
          | exact HTW | exact HMOD | exact HNEV ].
Qed.

(* The statement of lib/B/Prog/check_sent_frame_cg.v: the walk at the three runs of seg_base and seg_tail. *)
Theorem transport_check_sent_frame_cg_holds :
  forall fx rc B MT, @transport_check_sent_frame_cg_holds_stmt fx rc B MT.
Proof. exact (transport_check_sent_frame_cg_holds_of_runs csf_run1_all csf_mid_all csf_tail_all). Qed.
