(* check_state_desk_cgW: the caller-journal walk of check_state_desk in image B (fuzz_transport.asan-ubsan
   41113a03c82f, 0x854bc = transportb_sigma TB_check_state_desk), and the theorem of lib/B/Prog/check_state_desk_cg.v.
   Image B's twin of lib/A/Prog/check_state_desk_cgW.v: the same walk over image B's kit (DgnTransportBCg.v,
   DgnTransportBCgRun.v, TWorldB.v, TImgB.v) and image B's runs; the model lemma also gives OW.desk_body <> 0 and the
   bundle csd_bnd the announce's alignment, the two facts B's UBSan tests of them need.

   The walk, from the contract's premises:
     1. an INNER journal at the entry state (YCbq.v ajournal_sub_init; stack window [spZ regs - CSDESK_STK, spZ regs),
        no footprint, no frame of its own);
     2. the premises are read as the bundles of lib/B/Prog/check_state_desk_seg_kit.v (csd_mem, csd_rng, csd_bnd,
        csd_sep), with the bridges of lib/B/Prog/check_state_desk_seg_bridge.v: the runtime cells of the shadow base
        (transport_cells through DgnTransportBCgRun.v decode_cells_asan), the world's GOT.desk, OW.desk, OW.desk_off,
        OW.desk_p and OW.desk_body (tw_at at the machine's view), the 72 bytes of the notice and the bytes of the
        heap frame and of the announce (garr8 at the visible bytes of trans_src_ok's decode_rd_ok), the shadow bytes
        those reads check (range_addressable), the device and strips bytes of personalities[] / SPEC_C24 / SPEC_PC
        (trans_rom_view_rd) and their shadow bytes (transport_cells' zero-shadow rows);
     3. the three footprint runs of lib/B/Prog/check_state_desk_seg_runs.v and _seg_tail.v are carried into SRr by
        DgnTransportBCgRun.v decode_run, and the inner journal is re-established across each by YCbq.v ajournal_exec
        (a run writes only the 48 bytes of its own frame, which lie in the journal's stack window);
     4. the two bcmp calls are cut by YCbq.v aj_bcmp_at at the statement's abcmp_realizes premise: the compared
        ranges are sub-ranges of the announce and of the heap frame, both outside the call's 2 * ESTACK window
        (trans_ntc_at's and trans_tframe_at's decode_off_win), and each answer is 0 because the model's beq_bytes
        makes the two ranges agree byte for byte;
     5. the inner journal and the caller's compose by YC85.v ajournal_sub_tok, the kept bytes are YCbq.v
        acall_kept_of_journal of the inner journal (no footprint, no written range), the meter is unchanged
        (YC5d.v mle_start), the frames and the blocks are the call state's, and the post's world is the one the
        contract was given (the model's Bw' = Bw). *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00 YI16 YP09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Cells Step Regs6ss.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import Frame ExecF.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require LeafCgKit LeafCgFacts.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBSyms DgnTransportBAddr DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCgRun YC85.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import check_state_data_cg check_state_desk_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import check_state_desk_seg_kit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import check_state_desk_seg_bridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import check_state_desk_seg_tail.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import check_state_desk_seg_runs.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnLib.
Import ListNotations.
Open Scope Z_scope.
Module YKK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module LCK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.LeafCgKit.
Module ACL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.AsanCells.
Module DL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnLib.

(* ---- small facts the walk uses at every call site ---- *)

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

Lemma cw_stk_present : forall (H : word -> bool) m lo hi, 0 <= lo -> hi <= 2 ^ 64 ->
  (forall a, lo <= a < hi -> apresent H m a) -> stk rsegs m lo hi.
Proof.
  intros H m lo hi H0 H1 Hp. split; [exact H0|]. split; [exact H1|].
  intros a Ha. destruct (Hp a Ha) as [_ [b Hb]]. unfold wa. split.
  - unfold wview. rewrite Hb. discriminate.
  - exists b. unfold mrd. rewrite Hb. reflexivity.
Qed.

(* The two records the personality test may name: personalities[0] with SPEC_C24, personalities[1] with SPEC_PC
   (the other two pairs differ in the device byte, which the model's test rules out). *)
Lemma cw_pers_pair : forall (pn pd : Z) (pr : DL.dgn_personality) (d : DSp.desk),
  TC.personality_ptr timg_B pn = Some pr -> TC.spec_desk_at timg_B pd = Some d ->
  (negb (DL.dp_device pr =? DSp.d_dev d) || negb (DL.dp_strips pr =? DSp.d_strips d))%bool = false ->
  (pn = CSD_PERS0 /\ pd = CSD_C24) \/ (pn = CSD_PERS1 /\ pd = CSD_PC).
Proof.
  intros pn pd pr d HP HD HB.
  unfold TC.personality_ptr in HP. cbn [TI.ti_personalities timg_B] in HP.
  destruct ((pn - 0xa3b00 <? 0) || negb ((pn - 0xa3b00) mod 24 =? 0))%bool eqn:POK; [discriminate HP|].
  apply orb_false_iff in POK as [POK1 POK2].
  apply Z.ltb_ge in POK1. apply negb_false_iff in POK2. apply Z.eqb_eq in POK2.
  unfold TC.spec_desk_at in HD. cbn [TI.ti_spec_c24 TI.ti_spec_pc timg_B] in HD.
  unfold DL.personality_at in HP.
  destruct (Z.to_nat ((pn - 0xa3b00) / 24)) as [|[|kk]] eqn:EK.
  3: { exfalso. assert (HNE : nth_error DL.personalities (S (S kk)) <> None) by (rewrite HP; discriminate).
       apply nth_error_Some in HNE. unfold DL.personalities in HNE. cbn [length] in HNE. lia. }
  all: cbv beta iota delta [nth_error DL.personalities] in HP.
  - assert (Epn : pn = 0xa3b00).
    { pose proof (Z.div_mod (pn - 0xa3b00) 24 ltac:(lia)) as DM. rewrite POK2 in DM.
      pose proof (Z.div_pos (pn - 0xa3b00) 24 ltac:(lia) ltac:(lia)) as DP. lia. }
    injection HP as <-.
    destruct (Z.eqb_spec pd 0xa3a00) as [Epd|Epd]; cbv beta iota in HD.
    + injection HD as <-. left. unfold CSD_PERS0, CSD_C24. cbn [TI.ti_personalities TI.ti_spec_c24 timg_B]. lia.
    + destruct (Z.eqb_spec pd 0xa3a20) as [Epd2|Epd2]; cbv beta iota in HD; [|discriminate HD].
      injection HD as <-. exfalso. vm_compute in HB. discriminate HB.
  - assert (Epn : pn = 0xa3b18).
    { pose proof (Z.div_mod (pn - 0xa3b00) 24 ltac:(lia)) as DM. rewrite POK2 in DM.
      pose proof (Z.div_pos (pn - 0xa3b00) 24 ltac:(lia) ltac:(lia)) as DP. lia. }
    injection HP as <-.
    destruct (Z.eqb_spec pd 0xa3a00) as [Epd|Epd]; cbv beta iota in HD.
    + injection HD as <-. exfalso. vm_compute in HB. discriminate HB.
    + destruct (Z.eqb_spec pd 0xa3a20) as [Epd2|Epd2]; cbv beta iota in HD; [|discriminate HD].
      injection HD as <-. right. unfold CSD_PERS1, CSD_PERS0, CSD_PC.
      cbn [TI.ti_personalities TI.ti_spec_pc timg_B]. lia.
Qed.

(* The personality test's two cases, as one name (so that `lia` does not split on them). *)
Definition cw_pers_ok (pn pd : Z) : Prop :=
  pn = 0 \/ (pn = CSD_PERS0 /\ pd = CSD_C24) \/ (pn = CSD_PERS1 /\ pd = CSD_PC).

(* Two byte lists the model's beq_bytes makes equal: their bytes agree. *)
Lemma cw_bytes_eq : forall (l r : list byte) (q : nat),
  TC.beq_bytes (firstn q l) r = true -> length r = q -> (q <= length l)%nat ->
  forall i, (i < q)%nat -> DS.bz (nth i l (Z_to_bv 8 0)) = DS.bz (nth i r (Z_to_bv 8 0)).
Proof.
  intros l r q HB LR LQ i Hi.
  pose proof (PW.csd_beq _ _ HB) as E. unfold TW.zs in E.
  assert (LF : length (firstn q l) = q) by (rewrite length_firstn; lia).
  pose proof (f_equal (fun z => nth i z 0) E) as Ei. cbn beta in Ei.
  rewrite nth_indep with (d' := DS.bz (Z_to_bv 8 0)) in Ei by (rewrite length_map, LF; lia).
  rewrite map_nth in Ei.
  rewrite nth_indep with (l := map DS.bz r) (d' := DS.bz (Z_to_bv 8 0)) in Ei
    by (rewrite length_map, LR; lia).
  rewrite map_nth in Ei.
  rewrite PW.csd_nth_firstn in Ei by lia. exact Ei.
Qed.

Section Walk.
Context {fx : YKK.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Variable MT : ameter_ops.
Local Notation segs := tfibsegs.
Local Notation ajournalA := (@ajournal rc YE2k.tfib_sink_head segs B).

Hypothesis HCELLS : transport_cells B.
Hypothesis LAWS : AR_laws segs B.
Hypothesis MTL : ameter_laws MT.

(* Every byte the bundle speaks of: in range, outside the call's stack window [sp - CSDESK_STK, sp), and not
   hidden by the world. The image, the two runtime cells, the harness globals and every shadow byte lie below
   alloc_ceiling, which lies below that window; the notice, the heap frame and the announce are placed outside it by
   their decode_off_win. *)
Lemma cw_addr_facts : forall (W : world segs) (memc : word -> option byte) (lyc : alayout) (Sc : astate)
    (mdc : Model) (sp p : Z) (NB : list byte) (fr : TI.tframe) (vn nn : nat),
  @AR rc segs B lyc Sc W memc mdc ->
  decode_zshadow_at B TRANS_PERS (TRANS_PERS + 48) ->
  decode_zshadow_at B TRANS_SPEC_C24 (TRANS_SPEC_C24 + 16) ->
  decode_zshadow_at B TRANS_SPEC_PC (TRANS_SPEC_PC + 16) ->
  decode_rd_ok W memc p 72 ->
  decode_rd_ok W memc (TI.tf_addr fr) (Z.of_nat (length (TI.tf_bytes fr))) ->
  decode_rd_ok W memc (TW.u_at NB 24 8) 20 ->
  (p + 72 <= sp - CSDESK_STK \/ sp <= p) ->
  (TI.tf_addr fr + Z.of_nat (length (TI.tf_bytes fr)) <= sp - CSDESK_STK \/ sp <= TI.tf_addr fr) ->
  (TW.u_at NB 24 8 + 20 <= sp - CSDESK_STK \/ sp <= TW.u_at NB 24 8) ->
  YM05.alloc_ceiling + CSDESK_STK <= sp -> (vn <= 9)%nat -> (nn <= 9)%nat ->
  forall a, csd_addr p NB fr vn nn a ->
    0 <= a < 2 ^ 64 /\ (a + 1 <= sp - CSDESK_STK \/ sp <= a) /\ w_H W (Z_to_bv 64 a) = false.
Proof.
  intros W memc lyc Sc mdc sp p NB fr vn nn HAR ZPERS ZC24 ZPC RDP RDF RDA POFF FOFF AOFF SP1 LVN LNN.
  pose proof asan_consts as (AC1 & AC2 & AC3 & AC4 & AC5).
  assert (SHBND : forall q nq x, decode_rd_ok W memc q nq -> q <= x < q + nq ->
    0 <= x / 8 + ACL.ASAN_K /\ x / 8 + ACL.ASAN_K + 1 <= YM05.alloc_ceiling).
  { intros q nq x (_ & _ & _ & MR & Q0 & _) Hx. clear - MR Q0 Hx AC1.
    assert (Hx47 : 0 <= x <= 2 ^ 47) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in MR; lia).
    clear MR Q0 Hx.
    assert (Hd : 0 <= x / 8 <= 2 ^ 44)
      by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
    clear Hx47. unfold ACL.ASAN_K. lia. }
  (* the placements and the ranges as flat facts, so that no `lia` below splits on a disjunction *)
  assert (FLAT : forall q nq, decode_rd_ok W memc q nq -> 0 <= nq ->
    (q + nq <= sp - CSDESK_STK \/ sp <= q) ->
    0 <= q /\ q + nq <= 2 ^ 47 /\ forall b, q <= b < q + nq -> b + 1 <= sp - CSDESK_STK \/ sp <= b).
  { intros q nq (_ & _ & _ & MR & Q0 & _) Hn HO. clear - MR Q0 Hn HO.
    unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in MR.
    split; [lia|]. split; [lia|]. intros b Hb. destruct HO; [left | right]; lia. }
  destruct (FLAT p 72 RDP ltac:(lia) POFF) as (BP0 & BP47 & OP).
  destruct (FLAT _ _ RDF ltac:(lia) FOFF) as (BF0 & BF47 & OF).
  destruct (FLAT _ _ RDA ltac:(lia) AOFF) as (BA0 & BA47 & OA).
  clear FLAT POFF FOFF AOFF.
  unfold CSDESK_STK, CSDESK_FRAME, ESTACK in *.
    intros a [Ha | [Ha | [Ha | [Ha | [Ha | [Ha | [Ha | [Ha | [Ha | Ha]]]]]]]]].
    - assert (Hs : in_img segs a)
        by (apply (decode_covers_img ACL.GOT_CELL_K 8 a); [decode_seg | exact Ha]).
      pose proof (decode_segs_low a Hs) as Hlow. unfold kLowMemEnd in Hlow.
      split; [lia|]. split; [left; lia|]. exact (decode_vis_seg W a Hs).
    - assert (Hs : in_img segs a)
        by (apply (decode_covers_img ACL.CELL_K 8 a); [decode_seg | exact Ha]).
      pose proof (decode_segs_low a Hs) as Hlow. unfold kLowMemEnd in Hlow.
      split; [lia|]. split; [left; lia|]. exact (decode_vis_seg W a Hs).
    - assert (Hs : in_img segs a).
      { apply trans_g_img. apply Exists_exists. exists (TB_GOT, TW.SZ_GOT).
        split; [exact (TMAP_B_in_G TW.OFF_GOT TB_GOT TW.SZ_GOT TMAP_B_GOT)|].
        unfold in_zr, TW.SZ_GOT. cbn [fst snd]. lia. }
      pose proof (decode_segs_low a Hs) as Hlow. unfold kLowMemEnd in Hlow.
      split; [lia|]. split; [left; lia|]. exact (decode_vis_seg W a Hs).
    - assert (Hs : in_img segs a).
      { apply trans_g_img. apply Exists_exists. exists (TB_OW, TW.SZ_OW).
        split; [exact (TMAP_B_in_G TW.OFF_OW TB_OW TW.SZ_OW TMAP_B_OW)|].
        unfold in_zr, TW.SZ_OW. cbn [fst snd]. lia. }
      pose proof (decode_segs_low a Hs) as Hlow. unfold kLowMemEnd in Hlow.
      split; [lia|]. split; [left; lia|]. exact (decode_vis_seg W a Hs).
    - split; [lia|]. split; [exact (OP a Ha)|]. exact (csd_vis_rd W memc p 72 a RDP Ha).
    - destruct Ha as (j & Hj & ->).
      destruct (SHBND p 72 (p + 8 * j) RDP ltac:(lia)) as [SB1 SB2].
      unfold ACL.ASAN_K in *.
      split; [lia|]. split; [left; lia|].
      exact (proj1 (csd_shadow0 W memc p 72 (p + 8 * j) RDP ltac:(lia) ltac:(lia))).
    - destruct Ha as (c & Hc & Hd).
      assert (HZ : exists lo hi, decode_zshadow_at B lo hi /\ c mod 8 = 0 /\ lo <= c /\ c + 8 <= hi).
      { cbn [In] in Hc. destruct Hc as [<-|[<-|[<-|[<-|[]]]]].
        - exists TRANS_PERS, (TRANS_PERS + 48). split; [exact ZPERS|].
          unfold TRANS_PERS, CSD_P0, CSD_PERS0. cbn [TI.ti_personalities timg_B].
          split; [reflexivity | lia].
        - exists TRANS_PERS, (TRANS_PERS + 48). split; [exact ZPERS|].
          unfold TRANS_PERS, CSD_P1, CSD_PERS1, CSD_PERS0. cbn [TI.ti_personalities timg_B].
          split; [reflexivity | lia].
        - exists TRANS_SPEC_C24, (TRANS_SPEC_C24 + 16). split; [exact ZC24|].
          unfold TRANS_SPEC_C24, CSD_D0, CSD_C24. cbn [TI.ti_spec_c24 timg_B].
          split; [reflexivity | lia].
        - exists TRANS_SPEC_PC, (TRANS_SPEC_PC + 16). split; [exact ZPC|].
          unfold TRANS_SPEC_PC, CSD_D1, CSD_PC. cbn [TI.ti_spec_pc timg_B].
          split; [reflexivity | lia]. }
      destruct HZ as (zlo & zhi & HZc & HZm & HZ1 & HZ2).
      assert (HCB : 4096 <= c < 0xa4000).
      { cbn [In] in Hc. destruct Hc as [<-|[<-|[<-|[<-|[]]]]];
          (split; [vm_compute; discriminate | vm_compute; reflexivity]). }
      destruct Hd as [Hd | Hd].
      + assert (Hs : in_img segs a).
        { apply trans_ro_img. apply Exists_exists. cbn [In] in Hc.
          destruct Hc as [<-|[<-|[<-|[<-|[]]]]].
          - exists (TRANS_PERS, 48). split;
              [unfold TRANS_RO_RD, TRANS_RO_GLOBALS; cbn [In app]; tauto
              | unfold in_zr, TRANS_PERS, CSD_P0, CSD_PERS0 in *;
                cbn [fst snd TI.ti_personalities timg_B] in *; lia].
          - exists (TRANS_PERS, 48). split;
              [unfold TRANS_RO_RD, TRANS_RO_GLOBALS; cbn [In app]; tauto
              | unfold in_zr, TRANS_PERS, CSD_P1, CSD_PERS1, CSD_PERS0 in *;
                cbn [fst snd TI.ti_personalities timg_B] in *; lia].
          - exists (TRANS_SPEC_C24, 16). split;
              [unfold TRANS_RO_RD, TRANS_RO_GLOBALS; cbn [In app]; tauto
              | unfold in_zr, TRANS_SPEC_C24, CSD_D0, CSD_C24 in *;
                cbn [fst snd TI.ti_spec_c24 timg_B] in *; lia].
          - exists (TRANS_SPEC_PC, 16). split;
              [unfold TRANS_RO_RD, TRANS_RO_GLOBALS; cbn [In app]; tauto
              | unfold in_zr, TRANS_SPEC_PC, CSD_D1, CSD_PC in *;
                cbn [fst snd TI.ti_spec_pc timg_B] in *; lia]. }
        pose proof (decode_segs_low a Hs) as Hlow. unfold kLowMemEnd in Hlow.
        split; [lia|]. split; [left; lia|]. exact (decode_vis_seg W a Hs).
      + subst a. pose proof (Z.div_mod c 8 ltac:(lia)) as DMc.
        split; [unfold ACL.ASAN_K; lia|]. split; [left; unfold ACL.ASAN_K; lia|].
        exact (proj1 (csd_zsh_byte B lyc Sc W memc mdc zlo zhi c HAR HZc HZm HZ1 HZ2)).
    - split; [lia|]. split; [exact (OF a Ha)|].
      exact (csd_vis_rd W memc (TI.tf_addr fr) (Z.of_nat (length (TI.tf_bytes fr))) a RDF Ha).
    - destruct Ha as (x & Hx & ->).
      destruct (SHBND (TI.tf_addr fr) (Z.of_nat (length (TI.tf_bytes fr))) x RDF Hx) as [SB1 SB2].
      unfold ACL.ASAN_K in *.
      split; [lia|]. split; [left; lia|].
      exact (proj1 (csd_shadow_any W memc (TI.tf_addr fr) (Z.of_nat (length (TI.tf_bytes fr))) x RDF Hx)).
    - destruct Ha as (x & Hx & Hd).
      assert (HxA : TW.u_at NB 24 8 <= x < TW.u_at NB 24 8 + 20)
        by (destruct Hx as [E|E]; subst x; lia).
      destruct Hd as [Hd | Hd]; subst a.
      + split; [lia|]. split; [exact (OA x HxA)|]. exact (csd_vis_rd W memc (TW.u_at NB 24 8) 20 x RDA HxA).
      + destruct (SHBND (TW.u_at NB 24 8) 20 x RDA HxA) as [SB1 SB2]. unfold ACL.ASAN_K in *.
        split; [lia|]. split; [left; lia|].
        exact (proj1 (csd_shadow_any W memc (TW.u_at NB 24 8) 20 x RDA HxA)).
Qed.

Section Call.
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
  (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate)
  (W : world segs) (memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word)
  (p : Z) (n : TI.ntc) (Fr : option TI.tframe) (Bw Bw' : list byte).

Hypothesis HJ : ajournalA STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k.
Hypothesis HRET : YK0s.ret_ok (YKK.getr regs 1).
Hypothesis HGP : YKK.getr regs 3 = w64 (as_gp B).
Hypothesis HTP : YKK.getr regs 4 = w64 (as_tp B).
Hypothesis H10 : YKK.getr regs 10 = w64 p.
Hypothesis HAL : spZ regs mod 16 = 0.
Hypothesis HWLO : sp0 - STK <= spZ regs - CSDESK_STK.
Hypothesis HWHI : spZ regs <= sp0.
Hypothesis HNTC : trans_ntc_at B lyc Sc W memc regs CSDESK_STK p n.
Hypothesis HTFR : trans_tframe_at B lyc Sc W memc regs CSDESK_STK Fr.
Hypothesis HROM : trans_rom_view_rd W memc.
Hypothesis HTW : tw_at TMAP_B (aview segs (w_H W) memc) Bw.
Hypothesis HM : TC.check_state_desk_m timg_B Fr Bw n = Some (Bw', tt).

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

Lemma cw_sp_rng : YM05.alloc_ceiling + CSDESK_STK <= spZ regs /\ spZ regs <= 2 ^ 47.
Proof.
  pose proof cw_stk_ok as (H16 & Hstk0 & Hceil & Hlo & Hhi & H47 & _). lia.
Qed.

(* ---- the model premise ---- *)

Lemma cw_model : exists (fr : TI.tframe) (an : TI.tann) (vn nn : nat) (vb nb : list byte),
  Fr = Some fr /\ TI.n_ann n = Some an /\ Bw' = Bw /\
  (TW.s32_at Bw TW.A_OW_desk <? TW.s32_at Bw TW.A_GOT_desk) = false /\
  TI.n_mac_offset n = TW.s32_at Bw TW.A_OW_desk_off /\
  (TI.n_pers n =? 0) = (TW.u_at Bw TW.A_OW_desk_p 8 =? 0) /\
  (TI.n_pers n = 0 \/ (TI.n_pers n = CSD_PERS0 /\ TW.u_at Bw TW.A_OW_desk_p 8 = CSD_C24) \/
   (TI.n_pers n = CSD_PERS1 /\ TW.u_at Bw TW.A_OW_desk_p 8 = CSD_PC)) /\
  TC.frame_strz_len (Some fr) (TW.u_at Bw TW.A_OW_desk_body 8 + 15) = Some vn /\
  TC.frame_strz_len (Some fr) (TW.u_at Bw TW.A_OW_desk_body 8 + 24) = Some nn /\
  TC.frame_read (Some fr) (TW.u_at Bw TW.A_OW_desk_body 8 + 15) (Z.of_nat vn) = Some vb /\
  TC.frame_read (Some fr) (TW.u_at Bw TW.A_OW_desk_body 8 + 24) (Z.of_nat nn) = Some nb /\
  TC.beq_bytes (firstn vn (TI.ta_version an)) vb = true /\ (vn < length (TI.ta_version an))%nat /\
  DS.bz (nth vn (TI.ta_version an) (Z_to_bv 8 0)) = 0 /\
  TC.beq_bytes (firstn nn (TI.ta_name an)) nb = true /\ (nn < length (TI.ta_name an))%nat /\
  DS.bz (nth nn (TI.ta_name an) (Z_to_bv 8 0)) = 0 /\
  TW.u_at Bw TW.A_OW_desk_body 8 <> 0.
Proof.
  pose proof HM as HM'. unfold TC.check_state_desk_m in HM'. cbv zeta in HM'.
  unfold TW.OW_desk, TW.GOT_desk, TW.OW_desk_off, TW.OW_desk_p, TW.OW_desk_body in HM'.
  destruct ((TW.s32_at Bw TW.A_OW_desk <? TW.s32_at Bw TW.A_GOT_desk)
            || negb (TI.n_mac_offset n =? TW.s32_at Bw TW.A_OW_desk_off)
            || negb (Bool.eqb (TI.n_pers n =? 0) (TW.u_at Bw TW.A_OW_desk_p 8 =? 0)))%bool eqn:C0;
    [discriminate HM'|].
  apply orb_false_iff in C0 as [C0 C3]. apply orb_false_iff in C0 as [C1 C2].
  apply negb_false_iff in C2. apply negb_false_iff in C3. apply Bool.eqb_prop in C3.
  apply Z.eqb_eq in C2.
  destruct (if TI.n_pers n =? 0 then Some false
            else match TC.personality_ptr timg_B (TI.n_pers n) with
                 | Some pr => match TC.spec_desk_at timg_B (TW.u_at Bw TW.A_OW_desk_p 8) with
                              | Some d => Some (negb (DL.dp_device pr =? DS.d_dev d)
                                                || negb (DL.dp_strips pr =? DS.d_strips d))%bool
                              | None => None end
                 | None => None end) as [bad|] eqn:EB; [|discriminate HM'].
  destruct bad; [discriminate HM'|].
  assert (CP : TI.n_pers n = 0 \/ (TI.n_pers n = CSD_PERS0 /\ TW.u_at Bw TW.A_OW_desk_p 8 = CSD_C24) \/
               (TI.n_pers n = CSD_PERS1 /\ TW.u_at Bw TW.A_OW_desk_p 8 = CSD_PC)).
  { destruct (Z.eqb_spec (TI.n_pers n) 0) as [E0|E0]; [left; exact E0|]. right.
    cbv beta iota in EB.
    destruct (TC.personality_ptr timg_B (TI.n_pers n)) as [pr|] eqn:HP; [|discriminate EB].
    destruct (TC.spec_desk_at timg_B (TW.u_at Bw TW.A_OW_desk_p 8)) as [d|] eqn:HD; [|discriminate EB].
    injection EB as EB.
    exact (cw_pers_pair _ _ pr d HP HD EB). }
  destruct (TI.n_ann n) as [an|] eqn:HVA; [|discriminate HM'].
  destruct (TW.u_at Bw TW.A_OW_desk_body 8 =? 0) eqn:HDB; [discriminate HM'|].
  unfold TC.SPEC_ANN_VERSION, TC.SPEC_ANN_NAME in HM'.
  destruct (TC.frame_strz_len Fr (TW.u_at Bw TW.A_OW_desk_body 8 + 15)) as [vn|] eqn:HVN; [|discriminate HM'].
  destruct (TC.frame_strz_len Fr (TW.u_at Bw TW.A_OW_desk_body 8 + 24)) as [nn|] eqn:HNN; [|discriminate HM'].
  destruct (TC.frame_read Fr (TW.u_at Bw TW.A_OW_desk_body 8 + 15) (Z.of_nat vn)) as [vb|] eqn:HVB;
    [|discriminate HM'].
  destruct (TC.frame_read Fr (TW.u_at Bw TW.A_OW_desk_body 8 + 24) (Z.of_nat nn)) as [nb|] eqn:HNB;
    [|discriminate HM'].
  destruct (TC.beq_bytes (firstn vn (TI.ta_version an)) vb) eqn:HBV; [|discriminate HM'].
  destruct ((length (TI.ta_version an) <=? vn)%nat) eqn:HLV; [discriminate HM'|].
  destruct (TC.truth (DS.bz (nth vn (TI.ta_version an) (DS.b8 0)))) eqn:HZV; [discriminate HM'|].
  destruct (TC.beq_bytes (firstn nn (TI.ta_name an)) nb) eqn:HBN; [|discriminate HM'].
  destruct ((length (TI.ta_name an) <=? nn)%nat) eqn:HLN; [discriminate HM'|].
  destruct (TC.truth (DS.bz (nth nn (TI.ta_name an) (DS.b8 0)))) eqn:HZN; [discriminate HM'|].
  unfold TC.truth in HZV, HZN. apply negb_false_iff in HZV. apply negb_false_iff in HZN.
  apply Z.eqb_eq in HZV. apply Z.eqb_eq in HZN.
  apply Nat.leb_gt in HLV. apply Nat.leb_gt in HLN.
  assert (EFr : exists fr, Fr = Some fr)
    by (destruct Fr as [fr|]; [exists fr; reflexivity | discriminate HVN]).
  destruct EFr as [fr EFr]. rewrite EFr in HVN, HNN, HVB, HNB.
  assert (EB' : Bw' = Bw)
    by (pose proof (f_equal (fun o : option (list byte * unit) => match o with Some (b, _) => b | None => Bw end)
                      HM') as HB; cbv beta iota in HB; symmetry; exact HB).
  change (DS.b8 0) with (Z_to_bv 8 0) in HZV, HZN.
  exists fr, an, vn, nn, vb, nb.
  split; [exact EFr|]. split; [first [exact HVA | reflexivity]|]. split; [exact EB'|]. split; [exact C1|].
  split; [exact C2|]. split; [exact C3|]. split; [exact CP|].
  split; [exact HVN|]. split; [exact HNN|]. split; [exact HVB|]. split; [exact HNB|].
  split; [exact HBV|]. split; [exact HLV|]. split; [exact HZV|].
  split; [exact HBN|]. split; [exact HLN|]. split; [exact HZN | apply Z.eqb_neq; exact HDB].
Qed.

(* One byte of a garr8 span at a visible address. *)
Lemma cw_garr_byte : forall (W' : world segs) (mem : word -> option byte) (A : Z) (bs : list byte) (j : nat),
  w_H W' (Z_to_bv 64 (A + Z.of_nat j)) = false ->
  garr8 segs (mrestrict (w_H W') mem) A (map DS.bz bs) -> (j < length bs)%nat ->
  mrd rsegs mem (wa (A + Z.of_nat j)) = Some (nth j bs (Z_to_bv 8 0)).
Proof.
  intros W' mem A bs j HV HG Hj.
  assert (Hj' : (j < length (map DS.bz bs))%nat) by (rewrite length_map; exact Hj).
  destruct (HG j Hj') as [HV1 HR].
  specialize (HV1 0%nat ltac:(lia)). rewrite Z.add_0_r in HV1.
  rewrite (csd_mrd_of_mbyte W' mem (A + Z.of_nat j) HV), HV1.
  rewrite nth_indep with (d' := DS.bz (Z_to_bv 8 0)) in HR |- * by (rewrite length_map; exact Hj).
  rewrite map_nth in HR |- *.
  f_equal. unfold DS.bz in *.
  pose proof (bv_unsigned_in_range 8 (nth j bs (Z_to_bv 8 0))) as Rb. unfold bv_modulus in Rb.
  change (2 ^ Z.of_N 8) with 256 in Rb.
  unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
  rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite !(Z.mod_small _ 256) by lia.
  apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
  apply Z.mod_small. lia.
Qed.

(* Two image bytes of a TRANS_RO_RD record. *)
Lemma cw_ro2 : forall (W' : world segs) (mem : word -> option byte) (c : Z) (b0 b1 : byte),
  trans_rom_view_rd W' mem -> trans_in_ro_rd c -> trans_in_ro_rd (c + 1) ->
  PropExec.seg_rom rsegs (wa c) = Some b0 -> PropExec.seg_rom rsegs (wa (c + 1)) = Some b1 ->
  0 <= c -> c + 2 <= 2 ^ 64 -> bytes_at rsegs mem c [b0; b1].
Proof.
  intros W' mem c b0 b1 HROM' R0 R1 E0 E1 H0 H1.
  split; [exact H0|]. split; [cbn [length]; lia|].
  intros i Hi. cbn [length] in Hi.
  destruct i as [|[|i]]; [| |cbn in Hi; lia].
  - rewrite Z.add_0_r. rewrite (proj2 (csd_ro_byte W' mem c HROM' R0)). rewrite E0. reflexivity.
  - change (Z.of_nat 1) with 1. rewrite (proj2 (csd_ro_byte W' mem (c + 1) HROM' R1)). rewrite E1. reflexivity.
Qed.

(* ---- the premises as the bundles of check_state_desk_seg_kit.v ---- *)

Lemma cw_bundles : exists (fr : TI.tframe) (NB : list byte) (vn nn : nat),
  csd_mem memc p NB Bw fr vn nn /\
  csd_rng (LCK.RNG_W (world segs) (@w_H segs) W) (spZ regs) p NB fr vn nn /\
  csd_bnd p NB Bw fr /\ csd_sep (spZ regs) p NB fr vn nn /\
  (vn <= 9)%nat /\ (nn <= 9)%nat /\
  (TW.s32_at Bw TW.A_OW_desk <? TW.s32_at Bw TW.A_GOT_desk) = false /\
  TW.s32_at NB 40 = TW.s32_at Bw TW.A_OW_desk_off /\
  (TW.u_at NB 32 8 =? 0) = (TW.u_at Bw TW.A_OW_desk_p 8 =? 0) /\
  cw_pers_ok (TW.u_at NB 32 8) (TW.u_at Bw TW.A_OW_desk_p 8) /\
  TC.frame_strz_len (Some fr) (TW.u_at Bw TW.A_OW_desk_body 8 + 15) = Some vn /\
  TC.frame_strz_len (Some fr) (TW.u_at Bw TW.A_OW_desk_body 8 + 24) = Some nn /\
  (forall i, 0 <= i < Z.of_nat vn ->
     aview segs (w_H W) memc (TW.u_at NB 24 8 + i) =
     aview segs (w_H W) memc (TW.u_at Bw TW.A_OW_desk_body 8 + 15 + i)) /\
  (forall i, 0 <= i < Z.of_nat nn ->
     aview segs (w_H W) memc (TW.u_at NB 24 8 + 10 + i) =
     aview segs (w_H W) memc (TW.u_at Bw TW.A_OW_desk_body 8 + 24 + i)) /\
  decode_rd_ok W memc (TW.u_at NB 24 8) ANN_SIZE /\
  decode_rd_ok W memc (TI.tf_addr fr) (Z.of_nat (length (TI.tf_bytes fr))) /\
  decode_off_win regs CSDESK_STK (TW.u_at NB 24 8) ANN_SIZE /\
  decode_off_win regs CSDESK_STK (TI.tf_addr fr) (Z.of_nat (length (TI.tf_bytes fr))) /\
  TI.tf_addr fr <= TW.u_at Bw TW.A_OW_desk_body 8 + 15 /\
  TW.u_at Bw TW.A_OW_desk_body 8 + 15 + Z.of_nat vn <= TI.tf_addr fr + Z.of_nat (length (TI.tf_bytes fr)) /\
  TI.tf_addr fr <= TW.u_at Bw TW.A_OW_desk_body 8 + 24 /\
  TW.u_at Bw TW.A_OW_desk_body 8 + 24 + Z.of_nat nn <= TI.tf_addr fr + Z.of_nat (length (TI.tf_bytes fr)) /\
  (forall a, csd_addr p NB fr vn nn a ->
     0 <= a < 2 ^ 64 /\ (a + 1 <= spZ regs - CSDESK_STK \/ spZ regs <= a) /\ w_H W (Z_to_bv 64 a) = false) /\
  Bw' = Bw.
Proof.
  pose proof cw_AR as HAR.
  pose proof cw_sp_rng as [SP1 SP2].
  pose proof asan_consts as (AC1 & AC2 & AC3 & AC4 & AC5).
  destruct cw_model as (fr & an & vn & nn & vb & nb & EFr & EAN & EBw & Cdesk & Cmac & Cpers & CP
                        & HVN & HNN & HVB & HNB & BV & LV & ZV & BN & LN & ZN & DBNZ).
  pose proof HNTC as HN'. pose proof HTFR as HF'. rewrite EFr in HF'.
  destruct HN' as (Pnz & Palign & PSRC & POFF & NB & GNB & LNB & Hkind & Hstate & Hold & Hreason & Hpers & Hmac
                   & Hblen & Hcnt & Hretry & GBODY & BSRC & BOFF & Hann).
  rewrite EAN in Hann. destruct Hann as (Anz & Aalign & GVER & GNAM & ASRC & AOFF).
  destruct HF' as (Fnz & GFR & FSRC & FOFF).
  assert (CPh : cw_pers_ok (TW.u_at NB 32 8) (TW.u_at Bw TW.A_OW_desk_p 8))
    by (unfold cw_pers_ok; rewrite Hpers; exact CP).
  clear CP.
  pose proof (PW.csd_strz fr _ vn HVN) as (SV1 & SV2 & SV3 & SV4 & SV5).
  pose proof (PW.csd_strz fr _ nn HNN) as (SN1 & SN2 & SN3 & SN4 & SN5).
  (* the readable ranges *)
  assert (RDP : decode_rd_ok W memc p NTC_SIZE)
    by (eapply trans_src_ok_rd; [exact LAWS | exact HAR | exact PSRC | unfold NTC_SIZE; lia]).
  assert (RDF : decode_rd_ok W memc (TI.tf_addr fr) (Z.of_nat (length (TI.tf_bytes fr))))
    by (eapply trans_src_ok_rd; [exact LAWS | exact HAR | exact FSRC | lia]).
  assert (RDA : decode_rd_ok W memc (TW.u_at NB 24 8) ANN_SIZE)
    by (eapply trans_src_ok_rd; [exact LAWS | exact HAR | exact ASRC | unfold ANN_SIZE; lia]).
  unfold NTC_SIZE in *. unfold ANN_SIZE in *.
  assert (BP : 0 <= p /\ p + 72 <= 2 ^ 63) by (destruct RDP as (_ & _ & _ & _ & H0 & H1); lia).
  assert (BF : 0 <= TI.tf_addr fr /\ TI.tf_addr fr + Z.of_nat (length (TI.tf_bytes fr)) <= 2 ^ 63)
    by (destruct RDF as (_ & _ & _ & _ & H0 & H1); lia).
  assert (BA : 0 <= TW.u_at NB 24 8 /\ TW.u_at NB 24 8 + 20 <= 2 ^ 63)
    by (destruct RDA as (_ & _ & _ & _ & H0 & H1); lia).
  (* the world's bytes, at the machine's view *)
  pose proof (csd_tw_mrd W memc Bw HTW) as HTWm.
  pose proof (decode_cells_asan B HCELLS lyc Sc W memc mdc (@w_Hoff segs W) HAR) as HCA.
  destruct HCA as (CK & GCK & _).
  destruct (HCELLS lyc) as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15
                            & K16 & K17 & Z18 & K19 & K20 & K21 & K22 & Z23 & K24 & Z25 & K26 & K27 & K28
                            & K29 & K30 & K31 & K32 & Z33 & K34 & Z35 & K36 & Z37 & ZC24 & ZPC & Z40 & Z41
                            & Z42 & ZPERS).
  (* the bytes of the two spans the bcmp calls compare, as indexes into the frame *)
  assert (LVB : length vb = vn /\ forall i, (i < vn)%nat ->
    nth i vb (Z_to_bv 8 0)
    = nth (Z.to_nat (TW.u_at Bw TW.A_OW_desk_body 8 + 15 - TI.tf_addr fr) + i) (TI.tf_bytes fr) (Z_to_bv 8 0)).
  { unfold TC.frame_read in HVB.
    destruct (Z.of_nat vn =? 0) eqn:E0.
    - injection HVB as <-. split; [cbn [length]; lia | intros i Hi; lia].
    - destruct ((TW.u_at Bw TW.A_OW_desk_body 8 + 15 - TI.tf_addr fr <? 0) || (Z.of_nat vn <? 0)
                || (Z.of_nat (length (TI.tf_bytes fr)) <?
                    TW.u_at Bw TW.A_OW_desk_body 8 + 15 - TI.tf_addr fr + Z.of_nat vn))%bool eqn:EB2;
        [discriminate HVB|].
      injection HVB as <-. rewrite Nat2Z.id.
      apply orb_false_iff in EB2 as [EB2 EB3]. apply orb_false_iff in EB2 as [EB1 _].
      apply Z.ltb_ge in EB1. apply Z.ltb_ge in EB3.
      split; [apply TWL.length_sub; lia|]. intros i Hi. apply tw_nth_sub; lia. }
  assert (LNB2 : length nb = nn /\ forall i, (i < nn)%nat ->
    nth i nb (Z_to_bv 8 0)
    = nth (Z.to_nat (TW.u_at Bw TW.A_OW_desk_body 8 + 24 - TI.tf_addr fr) + i) (TI.tf_bytes fr) (Z_to_bv 8 0)).
  { unfold TC.frame_read in HNB.
    destruct (Z.of_nat nn =? 0) eqn:E0.
    - injection HNB as <-. split; [cbn [length]; lia | intros i Hi; lia].
    - destruct ((TW.u_at Bw TW.A_OW_desk_body 8 + 24 - TI.tf_addr fr <? 0) || (Z.of_nat nn <? 0)
                || (Z.of_nat (length (TI.tf_bytes fr)) <?
                    TW.u_at Bw TW.A_OW_desk_body 8 + 24 - TI.tf_addr fr + Z.of_nat nn))%bool eqn:EB2;
        [discriminate HNB|].
      injection HNB as <-. rewrite Nat2Z.id.
      apply orb_false_iff in EB2 as [EB2 EB3]. apply orb_false_iff in EB2 as [EB1 _].
      apply Z.ltb_ge in EB1. apply Z.ltb_ge in EB3.
      split; [apply TWL.length_sub; lia|]. intros i Hi. apply tw_nth_sub; lia. }
  pose proof (cw_addr_facts W memc lyc Sc mdc (spZ regs) p NB fr vn nn HAR ZPERS ZC24 ZPC RDP RDF RDA
                POFF FOFF AOFF SP1 SV2 SN2) as ADDR.
  assert (VIS : forall a, csd_addr p NB fr vn nn a -> w_H W (Z_to_bv 64 a) = false)
    by (intros a Ha; exact (proj2 (proj2 (ADDR a Ha)))).
  assert (ROin : forall c, In c [CSD_P0; CSD_P1; CSD_D0; CSD_D1] -> trans_in_ro_rd c /\ trans_in_ro_rd (c + 1)).
  { intros c Hc. cbn [In] in Hc. destruct Hc as [<-|[<-|[<-|[<-|[]]]]].
    - split; apply Exists_exists; exists (TRANS_PERS, 48); split;
        [unfold TRANS_RO_RD, TRANS_RO_GLOBALS; cbn [In app]; tauto
        | unfold in_zr, TRANS_PERS, CSD_P0, CSD_PERS0; cbn [fst snd TI.ti_personalities timg_B]; lia
        | unfold TRANS_RO_RD, TRANS_RO_GLOBALS; cbn [In app]; tauto
        | unfold in_zr, TRANS_PERS, CSD_P0, CSD_PERS0; cbn [fst snd TI.ti_personalities timg_B]; lia].
    - split; apply Exists_exists; exists (TRANS_PERS, 48); split;
        [unfold TRANS_RO_RD, TRANS_RO_GLOBALS; cbn [In app]; tauto
        | unfold in_zr, TRANS_PERS, CSD_P1, CSD_PERS1, CSD_PERS0; cbn [fst snd TI.ti_personalities timg_B]; lia
        | unfold TRANS_RO_RD, TRANS_RO_GLOBALS; cbn [In app]; tauto
        | unfold in_zr, TRANS_PERS, CSD_P1, CSD_PERS1, CSD_PERS0; cbn [fst snd TI.ti_personalities timg_B]; lia].
    - split; apply Exists_exists; exists (TRANS_SPEC_C24, 16); split;
        [unfold TRANS_RO_RD, TRANS_RO_GLOBALS; cbn [In app]; tauto
        | unfold in_zr, TRANS_SPEC_C24, CSD_D0, CSD_C24; cbn [fst snd TI.ti_spec_c24 timg_B]; lia
        | unfold TRANS_RO_RD, TRANS_RO_GLOBALS; cbn [In app]; tauto
        | unfold in_zr, TRANS_SPEC_C24, CSD_D0, CSD_C24; cbn [fst snd TI.ti_spec_c24 timg_B]; lia].
    - split; apply Exists_exists; exists (TRANS_SPEC_PC, 16); split;
        [unfold TRANS_RO_RD, TRANS_RO_GLOBALS; cbn [In app]; tauto
        | unfold in_zr, TRANS_SPEC_PC, CSD_D1, CSD_PC; cbn [fst snd TI.ti_spec_pc timg_B]; lia
        | unfold TRANS_RO_RD, TRANS_RO_GLOBALS; cbn [In app]; tauto
        | unfold in_zr, TRANS_SPEC_PC, CSD_D1, CSD_PC; cbn [fst snd TI.ti_spec_pc timg_B]; lia]. }
  assert (EV0 : nth vn (TI.ta_version an) (Z_to_bv 8 0) = Z_to_bv 8 0)
    by (apply bv_eq; unfold DS.bz in ZV; rewrite ZV; reflexivity).
  assert (EN0 : nth nn (TI.ta_name an) (Z_to_bv 8 0) = Z_to_bv 8 0)
    by (apply bv_eq; unfold DS.bz in ZN; rewrite ZN; reflexivity).
  exists fr, NB, vn, nn.
  (* csd_mem *)
  split.
  { split; [exact GCK|]. split; [exact CK|].
    split.
    { pose proof (tw_bytes_at rsegs memc TMAP_B Bw TW.OFF_GOT TB_GOT TW.SZ_GOT 208 4%nat TMAP_B_ok HTWm TMAP_B_GOT
                    ltac:(lia) ltac:(unfold TW.SZ_GOT; lia)) as H. exact H. }
    split.
    { pose proof (tw_bytes_at rsegs memc TMAP_B Bw TW.OFF_OW TB_OW TW.SZ_OW 208 4%nat TMAP_B_ok HTWm TMAP_B_OW
                    ltac:(lia) ltac:(unfold TW.SZ_OW; lia)) as H. exact H. }
    split.
    { pose proof (tw_bytes_at rsegs memc TMAP_B Bw TW.OFF_OW TB_OW TW.SZ_OW 232 4%nat TMAP_B_ok HTWm TMAP_B_OW
                    ltac:(lia) ltac:(unfold TW.SZ_OW; lia)) as H. exact H. }
    split.
    { pose proof (tw_bytes_at rsegs memc TMAP_B Bw TW.OFF_OW TB_OW TW.SZ_OW 240 8%nat TMAP_B_ok HTWm TMAP_B_OW
                    ltac:(lia) ltac:(unfold TW.SZ_OW; lia)) as H. exact H. }
    split.
    { pose proof (tw_bytes_at rsegs memc TMAP_B Bw TW.OFF_OW TB_OW TW.SZ_OW 248 8%nat TMAP_B_ok HTWm TMAP_B_OW
                    ltac:(lia) ltac:(unfold TW.SZ_OW; lia)) as H. exact H. }
    split; [exact LNB|].
    split.
    { apply (csd_bytes_of_garr W memc p NB); [lia | rewrite LNB; lia | | exact GNB].
      intros b Hb. apply VIS. do 4 right. left. rewrite LNB in Hb. lia. }
    split.
    { intros j Hj. exact (proj2 (csd_shadow0 W memc p 72 (p + 8 * j) RDP ltac:(lia) ltac:(lia))). }
    split.
    { destruct (ROin CSD_P0 ltac:(cbn; tauto)) as [R0 R1].
      exact (cw_ro2 W memc CSD_P0 (Z_to_bv 8 1) (Z_to_bv 8 24) HROM R0 R1
               ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
               ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)). }
    split.
    { destruct (ROin CSD_P1 ltac:(cbn; tauto)) as [R0 R1].
      exact (cw_ro2 W memc CSD_P1 (Z_to_bv 8 0) (Z_to_bv 8 8) HROM R0 R1
               ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
               ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)). }
    split.
    { destruct (ROin CSD_D0 ltac:(cbn; tauto)) as [R0 R1].
      exact (cw_ro2 W memc CSD_D0 (Z_to_bv 8 1) (Z_to_bv 8 24) HROM R0 R1
               ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
               ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)). }
    split.
    { destruct (ROin CSD_D1 ltac:(cbn; tauto)) as [R0 R1].
      exact (cw_ro2 W memc CSD_D1 (Z_to_bv 8 0) (Z_to_bv 8 8) HROM R0 R1
               ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
               ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)). }
    split.
    { intros c Hc.
      assert (HZ : exists lo hi, decode_zshadow_at B lo hi /\ c mod 8 = 0 /\ lo <= c /\ c + 8 <= hi).
      { cbn [In] in Hc. destruct Hc as [<-|[<-|[<-|[<-|[]]]]].
        - exists TRANS_PERS, (TRANS_PERS + 48). split; [exact ZPERS|].
          unfold TRANS_PERS, CSD_P0, CSD_PERS0. cbn [TI.ti_personalities timg_B].
          split; [reflexivity | lia].
        - exists TRANS_PERS, (TRANS_PERS + 48). split; [exact ZPERS|].
          unfold TRANS_PERS, CSD_P1, CSD_PERS1, CSD_PERS0. cbn [TI.ti_personalities timg_B].
          split; [reflexivity | lia].
        - exists TRANS_SPEC_C24, (TRANS_SPEC_C24 + 16). split; [exact ZC24|].
          unfold TRANS_SPEC_C24, CSD_D0, CSD_C24. cbn [TI.ti_spec_c24 timg_B].
          split; [reflexivity | lia].
        - exists TRANS_SPEC_PC, (TRANS_SPEC_PC + 16). split; [exact ZPC|].
          unfold TRANS_SPEC_PC, CSD_D1, CSD_PC. cbn [TI.ti_spec_pc timg_B].
          split; [reflexivity | lia]. }
      destruct HZ as (zlo & zhi & HZc & HZm & HZ1 & HZ2).
      exact (proj2 (csd_zsh_byte B lyc Sc W memc mdc zlo zhi c HAR HZc HZm HZ1 HZ2)). }
    split.
    { apply (csd_bytes_of_garr W memc (TI.tf_addr fr) (TI.tf_bytes fr)); [lia | lia | | exact GFR].
      intros b Hb. apply VIS. do 7 right. left. exact Hb. }
    split.
    { intros x Hx. destruct (csd_shadow_any W memc _ _ x RDF Hx) as (_ & kx & Hk & Ok).
      exists kx. split; [exact Hk | exact Ok]. }
    intros x Hx.
    assert (HxA : TW.u_at NB 24 8 <= x < TW.u_at NB 24 8 + 20) by (destruct Hx as [E|E]; subst x; lia).
    split.
    - destruct Hx as [E|E]; subst x.
      + rewrite (cw_garr_byte W memc (TW.u_at NB 24 8) (TI.ta_version an) vn
                   ltac:(apply VIS; do 9 right; exists (TW.u_at NB 24 8 + Z.of_nat vn);
                         split; [left; reflexivity | left; reflexivity]) GVER LV).
        rewrite EV0. reflexivity.
      + rewrite (cw_garr_byte W memc (TW.u_at NB 24 8 + 10) (TI.ta_name an) nn
                   ltac:(apply VIS; do 9 right; exists (TW.u_at NB 24 8 + 10 + Z.of_nat nn);
                         split; [right; reflexivity | left; reflexivity]) GNAM LN).
        rewrite EN0. reflexivity.
    - destruct (csd_shadow_any W memc _ 20 x RDA HxA) as (_ & kx & Hk & Ok).
      exists kx. split; [exact Hk | exact Ok]. }
  (* csd_rng *)
  split.
  { split.
    { apply (decode_rng W); [unfold CSDESK_STK, CSDESK_FRAME, ESTACK in *; lia | lia |].
      intros b Hb. apply cw_pres. unfold CSDESK_STK, CSDESK_FRAME, ESTACK in *. lia. }
    split.
    { apply (decode_rng W); [vm_compute; discriminate | vm_compute; discriminate |].
      intros b Hb. apply VIS. left. exact Hb. }
    split.
    { apply (decode_rng W); [vm_compute; discriminate | vm_compute; discriminate |].
      intros b Hb. apply VIS. right; left. exact Hb. }
    split.
    { apply (decode_rng W); [vm_compute; discriminate | vm_compute; discriminate |].
      intros b Hb. apply VIS. right; right; left. lia. }
    split.
    { apply (decode_rng W); [vm_compute; discriminate | vm_compute; discriminate |].
      intros b Hb. apply VIS. right; right; right; left. lia. }
    split.
    { apply (decode_rng W); [lia | lia |]. intros b Hb. apply VIS. do 4 right. left. exact Hb. }
    intros a Ha. destruct (ADDR a Ha) as (A1 & _ & A3).
    apply (decode_rng W); [lia | lia |]. intros b Hb. replace b with a by lia. exact A3. }
  (* csd_bnd, csd_sep *)
  split.
  { split; [lia|]. split; [exact Palign|]. split; [lia|]. split; [exact (tw_len TMAP_B _ Bw HTW)|].
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact DBNZ | exact Aalign]. }
  split.
  { intros a Ha. destruct (ADDR a Ha) as (A1 & A2 & _). split; [exact A1|].
    unfold CSDESK_STK, CSDESK_FRAME, ESTACK in A2. lia. }
  split; [exact SV2|]. split; [exact SN2|].
  split; [exact Cdesk|].
  split; [rewrite Hmac; exact Cmac|].
  split; [rewrite Hpers; exact Cpers|].
  split; [exact CPh|].
  split; [exact HVN|]. split; [exact HNN|].
  (* the bytes the two calls compare agree, by the model's beq_bytes *)
  split.
  { intros i Hi.
    rewrite (decode_aview_mrd W memc (TW.u_at NB 24 8 + i)
               ltac:(apply (csd_vis_rd W memc _ 20 _ RDA); lia)).
    rewrite (decode_aview_mrd W memc (TW.u_at Bw TW.A_OW_desk_body 8 + 15 + i)
               ltac:(apply (csd_vis_rd W memc _ _ _ RDF); lia)).
    replace (TW.u_at NB 24 8 + i) with (TW.u_at NB 24 8 + Z.of_nat (Z.to_nat i)) by lia.
    rewrite (cw_garr_byte W memc (TW.u_at NB 24 8) (TI.ta_version an) (Z.to_nat i)
               ltac:(apply (csd_vis_rd W memc _ 20 _ RDA); lia) GVER ltac:(lia)).
    replace (TW.u_at Bw TW.A_OW_desk_body 8 + 15 + i) with
      (TI.tf_addr fr + Z.of_nat (Z.to_nat (TW.u_at Bw TW.A_OW_desk_body 8 + 15 - TI.tf_addr fr) + Z.to_nat i))
      by lia.
    rewrite (cw_garr_byte W memc (TI.tf_addr fr) (TI.tf_bytes fr)
               (Z.to_nat (TW.u_at Bw TW.A_OW_desk_body 8 + 15 - TI.tf_addr fr) + Z.to_nat i)
               ltac:(apply (csd_vis_rd W memc _ _ _ RDF); lia) GFR ltac:(lia)).
    cbn [option_map]. f_equal.
    pose proof (cw_bytes_eq (TI.ta_version an) vb vn BV (proj1 LVB) ltac:(lia) (Z.to_nat i) ltac:(lia)) as EQ.
    rewrite (proj2 LVB (Z.to_nat i) ltac:(lia)) in EQ. unfold DS.bz in EQ. exact EQ. }
  split.
  { intros i Hi.
    rewrite (decode_aview_mrd W memc (TW.u_at NB 24 8 + 10 + i)
               ltac:(apply (csd_vis_rd W memc _ 20 _ RDA); lia)).
    rewrite (decode_aview_mrd W memc (TW.u_at Bw TW.A_OW_desk_body 8 + 24 + i)
               ltac:(apply (csd_vis_rd W memc _ _ _ RDF); lia)).
    replace (TW.u_at NB 24 8 + 10 + i) with (TW.u_at NB 24 8 + 10 + Z.of_nat (Z.to_nat i)) by lia.
    rewrite (cw_garr_byte W memc (TW.u_at NB 24 8 + 10) (TI.ta_name an) (Z.to_nat i)
               ltac:(apply (csd_vis_rd W memc _ 20 _ RDA); lia) GNAM ltac:(lia)).
    replace (TW.u_at Bw TW.A_OW_desk_body 8 + 24 + i) with
      (TI.tf_addr fr + Z.of_nat (Z.to_nat (TW.u_at Bw TW.A_OW_desk_body 8 + 24 - TI.tf_addr fr) + Z.to_nat i))
      by lia.
    rewrite (cw_garr_byte W memc (TI.tf_addr fr) (TI.tf_bytes fr)
               (Z.to_nat (TW.u_at Bw TW.A_OW_desk_body 8 + 24 - TI.tf_addr fr) + Z.to_nat i)
               ltac:(apply (csd_vis_rd W memc _ _ _ RDF); lia) GFR ltac:(lia)).
    cbn [option_map]. f_equal.
    pose proof (cw_bytes_eq (TI.ta_name an) nb nn BN (proj1 LNB2) ltac:(lia) (Z.to_nat i) ltac:(lia)) as EQ.
    rewrite (proj2 LNB2 (Z.to_nat i) ltac:(lia)) in EQ. unfold DS.bz in EQ. exact EQ. }
  split; [exact RDA|]. split; [exact RDF|]. split; [exact AOFF|]. split; [exact FOFF|].
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact ADDR | exact EBw].
Qed.

Lemma cw_stk : stk rsegs memc (spZ regs - CSDESK_STK) (spZ regs).
Proof.
  pose proof cw_sp_rng as [SP1 SP2]. unfold CSDESK_STK, CSDESK_FRAME, ESTACK in *.
  pose proof asan_consts as (C1 & _).
  apply (cw_stk_present (w_H W)); [lia | lia|].
  intros a Ha. apply cw_pres. lia.
Qed.

(* ---- the inner journal ---- *)

Lemma cw_inner : ajournalA CSDESK_STK (spZ regs) [] lyc Sc W memc mdc [] lyc Sc W memc mdc 0.
Proof.
  pose proof cw_stk_ok as (Hal16 & _).
  apply (@ajournal_sub_init rc YE2k.tfib_sink_head segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
           CSDESK_STK (spZ regs) [] (spZ regs - sp0) HJ);
    [lia | rewrite Zminus_mod, HAL, Hal16; reflexivity | lia
    | unfold CSDESK_STK, CSDESK_FRAME, ESTACK; lia | lia].
Qed.

(* The inner journal across one footprint run: the run writes only its own 48-byte frame, which lies in the
   journal's stack window (YCbq.v ajournal_exec). *)
Lemma cw_journal_run : forall (mem1 mem2 : word -> option byte) (md1 md2 : Model),
  ajournalA CSDESK_STK (spZ regs) [] lyc Sc W memc mdc [] lyc Sc W mem1 md1 0 ->
  munch [(spZ regs + -48, spZ regs)] mem1 mem2 ->
  wmono rsegs mem1 mem2 ->
  same_but_materialized md1 md2 ->
  ajournalA CSDESK_STK (spZ regs) [] lyc Sc W memc mdc [] lyc Sc W mem2 md2 0.
Proof.
  intros mem1 mem2 md1 md2 JI MU WM SBM.
  pose proof cw_sp_rng as [SP1 SP2]. unfold CSDESK_STK, CSDESK_FRAME, ESTACK in *.
  pose proof asan_consts as (C1 & _).
  apply (@ajournal_exec rc YE2k.tfib_sink_head segs B LAWS decode_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mem2 md2
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

(* ---- the close: the inner journal and the caller's compose into the statement's post ---- *)

Lemma cw_close : forall (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model),
  ajournalA CSDESK_STK (spZ regs) [] lyc Sc W memc mdc [] lyc Sc W mem2 md2 0 ->
  aregs_preserved regs regs2 -> Bw' = Bw ->
  SRr segs W (mkCfg (@YKK.mkst fx regs2 (YKK.getr regs 1) mem2 (YKK.seg_rom segs)) md2)
    (@transport_csdesk_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw').
Proof.
  intros regs2 mem2 md2 JI HP EBw.
  apply SRr_ret. unfold transport_csdesk_post, decode_cg_post.
  exists lyc, Sc, regs2, mem2, md2, 0.
  split; [reflexivity|].
  split; [unfold CSDESK_EV; lia|].
  split.
  { pose proof (ajournal_sub_tok segs B LAWS decode_segs_low STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
                  CSDESK_STK (spZ regs) [] [] lyc Sc W mem2 md2 0 HJ JI HWLO HWHI
                  ltac:(intros a (r & Hr & _); destruct Hr)) as J.
    cbn [app] in J. exact J. }
  split; [exact HP|].
  split; [reflexivity|].
  split; [apply Permutation_refl|].
  split.
  { exact (acall_kept_of_journal segs B decode_segs_low CSDESK_STK (spZ regs) [] [] lyc Sc W memc mdc
             lyc Sc W mem2 md2 0 (fun _ => False) JI cw_AR
             ltac:(intros a (r & Hr & _); destruct Hr)
             ltac:(intros bq mq i Hb _ _; exact Hb)
             sink_closed_nil). }
  split; [exact (mle_start MT Sc MTL) | exact EBw].
Qed.

(* The registers the epilogue restores are the caller's. *)
Lemma cw_pres_ret : forall (spx r10 r11 r12 r13 r14 r15 r16 r17 x5 x6 x7 x28 x29 x30 x31 : word)
    (g3 g4 g21 g22 g23 g24 g25 g26 g27 : word),
  bv_unsigned spx = spZ regs ->
  g3 = YKK.getr regs 3 -> g4 = YKK.getr regs 4 -> g21 = YKK.getr regs 21 ->
  g22 = YKK.getr regs 22 -> g23 = YKK.getr regs 23 -> g24 = YKK.getr regs 24 ->
  g25 = YKK.getr regs 25 -> g26 = YKK.getr regs 26 -> g27 = YKK.getr regs 27 ->
  aregs_preserved regs
    (mkR (YKK.getr regs 1) spx g3 g4 x5 x6 x7 (YKK.getr regs 8) (YKK.getr regs 9) r10 r11 r12 r13
         r14 r15 r16 r17 (YKK.getr regs 18) (YKK.getr regs 19) (YKK.getr regs 20) g21
         g22 g23 g24 g25 g26 g27 x28 x29 x30 x31).
Proof.
  intros spx r10 r11 r12 r13 r14 r15 r16 r17 x5 x6 x7 x28 x29 x30 x31 g3 g4 g21 g22 g23 g24 g25 g26 g27
    Hsp E3 E4 E21 E22 E23 E24 E25 E26 E27 r Hr.
  unfold acallee_saved in Hr.
  assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
               r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  repeat (destruct Hc as [Hc|Hc]); subst r; try reflexivity;
    try (rewrite E3; reflexivity); try (rewrite E4; reflexivity); try (rewrite E21; reflexivity);
    try (rewrite E22; reflexivity); try (rewrite E23; reflexivity); try (rewrite E24; reflexivity);
    try (rewrite E25; reflexivity); try (rewrite E26; reflexivity); try (rewrite E27; reflexivity).
  apply bv_eq. exact Hsp.
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

(* A writable stack range from the inner journal's present bytes. *)
Lemma cw_stk_of_journal : forall mem2 md2 hi,
  ajournalA CSDESK_STK (spZ regs) [] lyc Sc W memc mdc [] lyc Sc W mem2 md2 0 ->
  spZ regs - CSDESK_STK <= hi -> hi <= spZ regs ->
  stk rsegs mem2 (spZ regs - CSDESK_STK) hi.
Proof.
  intros mem2 md2 hi JI H1 H2.
  pose proof cw_sp_rng as [SP1 SP2]. unfold CSDESK_STK, CSDESK_FRAME, ESTACK in *.
  pose proof asan_consts as (C1 & _).
  destruct JI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HP & _).
  apply (cw_stk_present (w_H W)); [lia | lia|]. intros a Ha. apply HP. lia.
Qed.

(* The frame the prologue wrote is kept by a call whose window lies below it. *)
Lemma cw_frame_call : forall (mem1 mem2 : word -> option byte) (md1 : Model) (cs : list cell),
  ajournalA CSDESK_STK (spZ regs) [] lyc Sc W memc mdc [] lyc Sc W mem1 md1 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> (a + 1 <= spZ regs - CSDESK_STK \/ spZ regs + -48 <= a) ->
     aview segs (w_H W) mem2 a = aview segs (w_H W) mem1 a) ->
  (forall a, apresent (w_H W) mem1 a -> apresent (w_H W) mem2 a) ->
  rw_cells rsegs mem1 (spZ regs + -48) cs -> Z.of_nat (cells_size cs) <= 48 ->
  rw_cells rsegs mem2 (spZ regs + -48) cs.
Proof.
  intros mem1 mem2 md1 cs JI Hview Happ FR Hsz.
  pose proof cw_sp_rng as [SP1 SP2]. unfold CSDESK_STK, CSDESK_FRAME, ESTACK in *.
  pose proof asan_consts as (C1 & _).
  pose proof JI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HP & _).
  apply (decode_frame_ext (spZ regs + -48) 48 cs mem1 mem2); [exact Hsz | | exact FR].
  intros i Hi.
  assert (Hp1 : apresent (w_H W) mem1 (spZ regs + -48 + i)) by (apply HP; lia).
  exact (decode_present_eq W mem1 mem2 (spZ regs + -48 + i) Hp1 (Happ _ Hp1)
           (Hview (spZ regs + -48 + i) ltac:(lia) ltac:(right; lia))).
Qed.

(* ---- the views across the run and the calls ---- *)

Lemma cw_view_run1 : forall m1, munch [(spZ regs + -48, spZ regs)] memc m1 ->
  forall a, 0 <= a < 2 ^ 64 -> (a + 1 <= spZ regs - CSDESK_STK \/ spZ regs <= a) ->
    aview segs (w_H W) m1 a = aview segs (w_H W) memc a.
Proof.
  intros m1 MU a Ha Hd. apply (csd_view_out W memc m1 (spZ regs + -48) (spZ regs) MU a Ha).
  unfold CSDESK_STK, CSDESK_FRAME, ESTACK in Hd. destruct Hd; [left | right]; lia.
Qed.

Lemma cw_view_call : forall mT m2,
  (forall a, 0 <= a < 2 ^ 64 -> (a + 1 <= spZ regs - CSDESK_STK \/ spZ regs + -48 <= a) ->
     aview segs (w_H W) m2 a = aview segs (w_H W) mT a) ->
  (forall a, 0 <= a < 2 ^ 64 -> (a + 1 <= spZ regs - CSDESK_STK \/ spZ regs <= a) ->
     aview segs (w_H W) mT a = aview segs (w_H W) memc a) ->
  forall a, 0 <= a < 2 ^ 64 -> (a + 1 <= spZ regs - CSDESK_STK \/ spZ regs <= a) ->
     aview segs (w_H W) m2 a = aview segs (w_H W) memc a.
Proof.
  intros mT m2 V2 V1 a Ha Hd. rewrite (V2 a Ha); [exact (V1 a Ha Hd)|]. destruct Hd; [left | right]; lia.
Qed.

(* A range placed outside the window by decode_off_win: a sub-range is too. *)
Lemma cw_off_sub : forall q nq q' n', decode_off_win regs CSDESK_STK q nq -> q <= q' -> q' + n' <= q + nq -> 0 <= n' ->
  decode_off_win regs CSDESK_STK q' n'.
Proof. intros q nq q' n' O H1 H2 H3. unfold decode_off_win in *. destruct O; [left | right]; lia. Qed.

(* A view that agrees with memc outside the window keeps every readable range placed outside it (the shadow band
   lies below alloc_ceiling, so below the window). *)
Lemma cw_rd_out : forall (m' : word -> option byte) q nq,
  (forall a, 0 <= a < 2 ^ 64 -> (a + 1 <= spZ regs - CSDESK_STK \/ spZ regs <= a) ->
     aview segs (w_H W) m' a = aview segs (w_H W) memc a) ->
  decode_rd_ok W memc q nq -> decode_off_win regs CSDESK_STK q nq -> decode_rd_ok W m' q nq.
Proof.
  intros m' q nq AG RD OFF.
  pose proof cw_sp_rng as [SP1 SP2]. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof RD as (_ & _ & _ & _ & H0 & H63).
  apply (trans_rd_ok_view W W memc m' q nq RD).
  - intros a Ha. apply AG; [lia|]. unfold decode_off_win in OFF. destruct OFF; [left | right]; lia.
  - intros s Hs. apply AG; [lia|]. left. unfold CSDESK_STK, CSDESK_FRAME, ESTACK in *. lia.
Qed.

(* ... and two ranges whose bytes agree at memc agree there. *)
Lemma cw_eq_out : forall (m' : word -> option byte) x y nq,
  (forall a, 0 <= a < 2 ^ 64 -> (a + 1 <= spZ regs - CSDESK_STK \/ spZ regs <= a) ->
     aview segs (w_H W) m' a = aview segs (w_H W) memc a) ->
  decode_rd_ok W memc x nq -> decode_rd_ok W memc y nq ->
  decode_off_win regs CSDESK_STK x nq -> decode_off_win regs CSDESK_STK y nq ->
  (forall i, 0 <= i < nq -> aview segs (w_H W) memc (x + i) = aview segs (w_H W) memc (y + i)) ->
  forall i, 0 <= i < nq -> aview segs (w_H W) m' (x + i) = aview segs (w_H W) m' (y + i).
Proof.
  intros m' x y nq AG RX RY OX OY E i Hi.
  pose proof RX as (_ & _ & _ & _ & X0 & X63). pose proof RY as (_ & _ & _ & _ & Y0 & Y63).
  unfold decode_off_win in OX, OY.
  rewrite (AG (x + i)) by first [lia | destruct OX; [left | right]; lia].
  rewrite (AG (y + i)) by first [lia | destruct OY; [left | right]; lia].
  exact (E i Hi).
Qed.

(* The memory bundle across a call: every byte it speaks of lies outside the call's window. *)
Lemma cw_mem_call : forall (NB : list byte) (fr : TI.tframe) (vn nn : nat) (mT m2 : word -> option byte),
  (forall a, csd_addr p NB fr vn nn a ->
     0 <= a < 2 ^ 64 /\ (a + 1 <= spZ regs - CSDESK_STK \/ spZ regs <= a) /\ w_H W (Z_to_bv 64 a) = false) ->
  (forall a, 0 <= a < 2 ^ 64 -> (a + 1 <= spZ regs - CSDESK_STK \/ spZ regs + -48 <= a) ->
     aview segs (w_H W) m2 a = aview segs (w_H W) mT a) ->
  csd_mem mT p NB Bw fr vn nn -> csd_mem m2 p NB Bw fr vn nn.
Proof.
  intros NB fr vn nn mT m2 ADDR V MEM. apply (csd_mem_ext mT m2); [|exact MEM].
  intros a Ha. destruct (ADDR a Ha) as (A1 & A2 & A3).
  apply (cw_mrd_of_aview W mT m2 a A3). apply V; [exact A1|].
  destruct A2; [left | right]; lia.
Qed.

(* ---- the two bcmp calls ---- *)

Hypothesis ABCMPH : forall fx' : YKK.FPState,
  @abcmp_realizes fx' rc segs B (transportb_sigma TB___interceptor_trampoline_bcmp).

(* One call of bcmp over two ranges placed outside the window, on the inner journal (YCbq.v aj_bcmp_at at the
   statement's abcmp_realizes). *)
Lemma cw_bcmp : forall (regsT : bvmap 5 word) (memT : word -> option byte) (mdT : Model)
    (x y nq : Z) (raw : word) (Q : world segs -> config -> Prop),
  ajournalA CSDESK_STK (spZ regs) [] lyc Sc W memc mdc [] lyc Sc W memT mdT 0 ->
  YKK.getr regsT 10 = w64 x -> YKK.getr regsT 11 = w64 y -> YKK.getr regsT 12 = w64 nq ->
  0 <= nq <= 9 ->
  decode_rd_ok W memT x nq -> decode_rd_ok W memT y nq ->
  decode_off_win regs CSDESK_STK x nq -> decode_off_win regs CSDESK_STK y nq ->
  YKK.getr regsT 2 = Z_to_bv 64 (spZ regs + -48) ->
  YKK.getr regsT 3 = w64 (as_gp B) -> YKK.getr regsT 4 = w64 (as_tp B) ->
  YKK.getr regsT 1 = raw -> YK0s.ret_ok raw ->
  (forall i, 0 <= i < nq -> aview segs (w_H W) memT (x + i) = aview segs (w_H W) memT (y + i)) ->
  (forall (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model),
     ajournalA CSDESK_STK (spZ regs) [] lyc Sc W memc mdc [] lyc Sc W mem2 md2 0 ->
     aregs_preserved regsT regs2 -> YKK.getr regs2 10 = w64 0 ->
     (forall a, 0 <= a < 2 ^ 64 -> (a + 1 <= spZ regs - CSDESK_STK \/ spZ regs + -48 <= a) ->
        aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) ->
     (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a) ->
     SRr segs W (mkCfg (@YKK.mkst fx regs2 raw mem2 (YKK.seg_rom segs)) md2) Q) ->
  SRr segs W
    (mkCfg (@YKK.mkst fx regsT (Z_to_bv 64 (transportb_sigma TB___interceptor_trampoline_bcmp)) memT
              (YKK.seg_rom segs)) mdT) Q.
Proof.
  intros regsT memT mdT x y nq raw Q JI R10 R11 R12 Hn RDX RDY OFX OFY R2 R3 R4 R1 HRAW HEQ K.
  pose proof cw_sp_rng as [SP1 SP2]. unfold decode_off_win in OFX, OFY.
  unfold CSDESK_STK, CSDESK_FRAME, ESTACK in *.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof RDX as (HvX & HraX & HhX & HmX & H0X & H63X).
  pose proof RDY as (HvY & HraY & HhY & HmY & H0Y & H63Y).
  assert (HspT : spZ regsT = spZ regs + -48)
    by (unfold spZ; rewrite R2; rewrite unsigned_lit; [reflexivity | lia]).
  eapply SRr_bind.
  { apply (@aj_bcmp_at fx rc YE2k.tfib_sink_head segs B LAWS decode_segs_low
             (transportb_sigma TB___interceptor_trampoline_bcmp) (ABCMPH fx) W regsT memT
             CSDESK_STK (spZ regs) [] lyc Sc W memc mdc [] lyc Sc mdT 0 x y nq (-48) raw JI).
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
    - unfold CSDESK_STK, CSDESK_FRAME, ESTACK; lia.
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
  SRr segs W (@cfg_at fx segs (transportb_sigma TB_check_state_desk) regs memc mdc)
    (@transport_csdesk_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw').
Proof.
  destruct cw_bundles as (fr & NB & vn & nn & MEM & RNGH & BND & SEP & LV & LN & Cd & Cm & Cp & CP & HVN & HNN
                          & EQ1 & EQ2 & RDA & RDF & AOFF & FOFF & F1 & F2 & F3 & F4 & ADDR & EBw).
  pose proof cw_sp_rng as [SP1 SP2].
  assert (GRET : ret_pc (YKK.getr regs (Z_to_bv 5 1)) = YKK.getr regs (Z_to_bv 5 1))
    by exact (LeafCgFacts.ret_ok_stmt_YK0s _ HRET).
  assert (G10 : YKK.getr regs (Z_to_bv 5 10) = w64 p) by exact H10.
  assert (HHLO : spZ regs - CSDESK_STK + 48 <= spZ regs) by (unfold CSDESK_STK, CSDESK_FRAME, ESTACK; lia).
  assert (HHLO2 : spZ regs - CSDESK_STK <= spZ regs + -48) by (unfold CSDESK_STK, CSDESK_FRAME, ESTACK; lia).
  (* the four ranges the two calls compare: the announce's version and name, the desk body's two strings *)
  assert (RA1 : decode_rd_ok W memc (TW.u_at NB 24 8) (Z.of_nat vn))
    by (apply (decode_rd_ok_sub W memc _ ANN_SIZE _ _ RDA); unfold ANN_SIZE; lia).
  assert (OA1 : decode_off_win regs CSDESK_STK (TW.u_at NB 24 8) (Z.of_nat vn))
    by (apply (cw_off_sub _ ANN_SIZE _ _ AOFF); unfold ANN_SIZE; lia).
  assert (RF1 : decode_rd_ok W memc (TW.u_at Bw TW.A_OW_desk_body 8 + 15) (Z.of_nat vn))
    by (apply (decode_rd_ok_sub W memc _ _ _ _ RDF); lia).
  assert (OF1 : decode_off_win regs CSDESK_STK (TW.u_at Bw TW.A_OW_desk_body 8 + 15) (Z.of_nat vn))
    by (apply (cw_off_sub _ _ _ _ FOFF); lia).
  assert (RA2 : decode_rd_ok W memc (TW.u_at NB 24 8 + 10) (Z.of_nat nn))
    by (apply (decode_rd_ok_sub W memc _ ANN_SIZE _ _ RDA); unfold ANN_SIZE; lia).
  assert (OA2 : decode_off_win regs CSDESK_STK (TW.u_at NB 24 8 + 10) (Z.of_nat nn))
    by (apply (cw_off_sub _ ANN_SIZE _ _ AOFF); unfold ANN_SIZE; lia).
  assert (RF2 : decode_rd_ok W memc (TW.u_at Bw TW.A_OW_desk_body 8 + 24) (Z.of_nat nn))
    by (apply (decode_rd_ok_sub W memc _ _ _ _ RDF); lia).
  assert (OF2 : decode_off_win regs CSDESK_STK (TW.u_at Bw TW.A_OW_desk_body 8 + 24) (Z.of_nat nn))
    by (apply (cw_off_sub _ _ _ _ FOFF); lia).
  (* ---- the entry .. the first call of bcmp ---- *)
  eapply decode_run.
  { unfold LCK.ms_of_regs. rewrite G10.
    eapply csd_run1_F; [exact MEM | exact RNGH | exact BND | exact SEP | exact cw_stk | exact HHLO | exact Cd
      | exact Cm | exact Cp | exact CP | exact HVN | exact HNN]. }
  intros msT mdT (ms0 & (m1 & y13 & y14 & y15 & y16 & y17 & -> & MU & WM & ST1 & FR & MEM1) & EQVT) SBMT.
  rewrite (decode_ms_shape _ _ _ _ EQVT).
  pose proof (cw_journal_run memc m1 mdc mdT cw_inner MU WM SBMT) as JI1.
  pose proof (cw_view_run1 m1 MU) as V1.
  eapply cw_bcmp with (x := TW.u_at NB 24 8) (y := TW.u_at Bw TW.A_OW_desk_body 8 + 15) (nq := Z.of_nat vn)
    (raw := Z_to_bv 64 CSD_RET1).
  + exact JI1.
  + rewrite (decode_ms_reg _ _ _ _ _ _ _ _ _ EQVT) by reflexivity. reflexivity.
  + rewrite (decode_ms_reg _ _ _ _ _ _ _ _ _ EQVT) by reflexivity. reflexivity.
  + rewrite (decode_ms_reg _ _ _ _ _ _ _ _ _ EQVT) by reflexivity. reflexivity.
  + lia.
  + exact (cw_rd_out m1 _ _ V1 RA1 OA1).
  + exact (cw_rd_out m1 _ _ V1 RF1 OF1).
  + exact OA1.
  + exact OF1.
  + rewrite (decode_ms_reg _ _ _ _ _ _ _ _ _ EQVT) by reflexivity. reflexivity.
  + rewrite (decode_ms_reg _ _ _ _ _ _ _ _ _ EQVT) by reflexivity. exact HGP.
  + rewrite (decode_ms_reg _ _ _ _ _ _ _ _ _ EQVT) by reflexivity. exact HTP.
  + rewrite (decode_ms_reg _ _ _ _ _ _ _ _ _ EQVT) by reflexivity. reflexivity.
  + apply YK0s.ret_ok_even. vm_compute. reflexivity.
  + exact (cw_eq_out m1 _ _ _ V1 RA1 RF1 OA1 OF1 EQ1).
  + (* ---- the return of the first call .. the second call ---- *)
    intros regs2 mem2 md2 JI2 HP2 H2a0 Hview Happ.
    pose proof (cw_mem_call NB fr vn nn m1 mem2 ADDR Hview MEM1) as MEM2.
    pose proof (cw_frame_call m1 mem2 mdT _ JI1 Hview Happ FR
                  ltac:(unfold csd_fr; cbn [cells_size csize]; lia)) as FR2.
    pose proof (cw_view_call m1 mem2 Hview V1) as V2.
    assert (GA0 : YKK.getr regs2 (Z_to_bv 5 10) = w64 0) by exact H2a0.
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
      eapply csd_mid_F; [exact MEM2 | exact RNGH | exact BND | exact LV | exact LN]. }
    intros msT2 mdT2 (ms0' & (z13 & z14 & z15 & ->) & EQVT2) SBMT2.
    rewrite (decode_ms_shape _ _ _ _ EQVT2).
    pose proof (cw_journal_run mem2 mem2 md2 mdT2 JI2 (munch_refl _ _) (wmono_refl rsegs mem2) SBMT2) as JI2'.
    eapply cw_bcmp with (x := TW.u_at NB 24 8 + 10) (y := TW.u_at Bw TW.A_OW_desk_body 8 + 24)
      (nq := Z.of_nat nn) (raw := Z_to_bv 64 CSD_RET2).
    * exact JI2'.
    * rewrite (decode_ms_reg _ _ _ _ _ _ _ _ _ EQVT2) by reflexivity. reflexivity.
    * rewrite (decode_ms_reg _ _ _ _ _ _ _ _ _ EQVT2) by reflexivity. reflexivity.
    * rewrite (decode_ms_reg _ _ _ _ _ _ _ _ _ EQVT2) by reflexivity. reflexivity.
    * lia.
    * exact (cw_rd_out mem2 _ _ V2 RA2 OA2).
    * exact (cw_rd_out mem2 _ _ V2 RF2 OF2).
    * exact OA2.
    * exact OF2.
    * rewrite (decode_ms_reg _ _ _ _ _ _ _ _ _ EQVT2) by reflexivity. reflexivity.
    * rewrite (decode_ms_reg _ _ _ _ _ _ _ _ _ EQVT2) by reflexivity. exact HGP.
    * rewrite (decode_ms_reg _ _ _ _ _ _ _ _ _ EQVT2) by reflexivity. exact HTP.
    * rewrite (decode_ms_reg _ _ _ _ _ _ _ _ _ EQVT2) by reflexivity. reflexivity.
    * apply YK0s.ret_ok_even. vm_compute. reflexivity.
    * exact (cw_eq_out mem2 _ _ _ V2 RA2 RF2 OA2 OF2 EQ2).
    * (* ---- the return of the second call .. the return to the caller ---- *)
      intros regs3 mem3 md3 JI3 HP3 H3a0 Hview3 Happ3.
      pose proof (cw_mem_call NB fr vn nn mem2 mem3 ADDR Hview3 MEM2) as MEM3.
      pose proof (cw_frame_call mem2 mem3 md2 _ JI2 Hview3 Happ3 FR2
                    ltac:(unfold csd_fr; cbn [cells_size csize]; lia)) as FR3.
      pose proof (cw_stk_of_journal mem3 md3 (spZ regs + -48) JI3
                    ltac:(unfold CSDESK_STK, CSDESK_FRAME, ESTACK; lia) ltac:(lia)) as ST3.
      assert (GA0' : YKK.getr regs3 (Z_to_bv 5 10) = w64 0) by exact H3a0.
      eapply decode_run.
      { unfold LCK.ms_of_regs.
        rewrite (HP3 2 ltac:(unfold acallee_saved; lia)), (HP3 3 ltac:(unfold acallee_saved; lia)),
          (HP3 4 ltac:(unfold acallee_saved; lia)), (HP3 8 ltac:(unfold acallee_saved; lia)),
          (HP3 9 ltac:(unfold acallee_saved; lia)), (HP3 18 ltac:(unfold acallee_saved; lia)),
          (HP3 19 ltac:(unfold acallee_saved; lia)), (HP3 20 ltac:(unfold acallee_saved; lia)),
          (HP3 21 ltac:(unfold acallee_saved; lia)), (HP3 22 ltac:(unfold acallee_saved; lia)),
          (HP3 23 ltac:(unfold acallee_saved; lia)), (HP3 24 ltac:(unfold acallee_saved; lia)),
          (HP3 25 ltac:(unfold acallee_saved; lia)), (HP3 26 ltac:(unfold acallee_saved; lia)),
          (HP3 27 ltac:(unfold acallee_saved; lia)), GA0'.
        rewrite !(decode_ms_reg _ _ _ _ _ _ _ _ _ EQVT2) by reflexivity.
        eapply csd_ret_F; [exact MEM3 | exact RNGH | exact BND | exact LV | exact LN | exact ST3 | exact HHLO2
          | exact FR3]. }
      intros ms3 md3' (ms0'' & (r10 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & spx & -> & Hsp & ST4) & EQV3)
        SBM3.
      rewrite (decode_ms_shape _ _ _ _ EQV3).
      rewrite GRET.
      eapply cw_close.
      -- exact (cw_journal_run mem3 mem3 md3 md3' JI3 (munch_refl _ _) (wmono_refl rsegs mem3) SBM3).
      -- apply (cw_pres_eqv _ _ _ _ _ _ _ _ EQV3).
         apply cw_pres_ret; [exact Hsp | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
           | reflexivity | reflexivity | reflexivity | reflexivity].
      -- exact EBw.
Qed.

End Call.
End Walk.

(* The statement of lib/B/Prog/check_state_desk_cg.v: the runtime cells, the allocator and meter laws and the bcmp
   contract give the contract at TB_check_state_desk. *)
Theorem transport_check_state_desk_cg_holds {fx : YKK.FPState} {rc : YM05.RunCeil}
    (B : asyms) (MT : ameter_ops) : @transport_check_state_desk_cg_holds_stmt fx rc B MT.
Proof.
  intros HCELLS HOWN HERR LAWS MTL ABCMP.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p n Fr Bw Bw'.
  intros HJ HRET HRA4 HGP HTP H10 HAL HWLO HWHI HNTC HTFR HROM HTW HM HNEV.
  exact (@cw_holds fx rc B MT HCELLS LAWS MTL STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p n Fr Bw Bw'
           HJ HRET HGP HTP H10 HAL HWLO HWHI HNTC HTFR HROM HTW HM ABCMP).
Qed.

Print Assumptions transport_check_state_desk_cg_holds.
