(* spec_read_frame_cgW: Theorem transport_spec_read_frame_cg_holds : the statement
   transport_spec_read_frame_cg_holds_stmt of lib/B/Prog/spec_read_frame_cg.v, the caller-journal walk of
   spec_read_frame on fuzz_transport.asan-ubsan at 0x839c0 (1728 bytes, frame 48, one call of __asan_memset), in the
   G form (the caller's journal lib/A/W_journalG.v ajournal_gx G_HARNESS_B 0 [], the post TransportGCg.v
   transport_cg_post_out with the out cell [(fp, 80)]).

   The walk (srfw_holds), on the footprint route:
     1. run 1 (lib/B/Prog/spec_read_frame_seg_run.v srf_run1_F, entry .. the `jal __asan_memset`) carried into SRr
        by lib/B/Prog/DgnTransportBCgRun.v decode_run; the G journal re-established by W_journalG.v ajournal_gx_exec
        (the run writes only its 48-byte frame, in the journal's stack window);
     2. __asan_memset (fp, 0, 80) by TransportGCg.v gx_intrin_at (the struct's write right transport_twr_ok_g at the
        call's sp, its shadow from decode_rd_ok);
     3. run 2 (spec_read_frame_seg_head.v srf_run2_F, the memset's return .. the `ret`), from the bundle srf_cx at the
        memory the memset returned (srfw_cx: the frame bytes from garr8, the shadow bytes from range_addressable,
        the five saves from run 1, every one kept by the memset);
     4. the close, lib/B/Prog/spec_read_frame_seg_close.v srf_close. *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00 YP03.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c YK1b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Cells Step Regs6ss.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import Frame ExecF.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBSyms DgnTransportBAddr DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCgRun TransportGRwB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require LeafCgKit LeafCgFacts.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import spec_read_frame_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
  spec_read_frame_seg_run spec_read_frame_seg_head spec_read_frame_seg_close.
Import ListNotations.
Open Scope Z_scope.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.
Module YKK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module LCK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.LeafCgKit.
Module FC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.AsanCells.

(* ---- memory facts (the helpers of lib/A/Prog/check_sent_frame_cgW.v, over image B) ---- *)

Lemma srfw_garr_view : forall (W : world tfibsegs) mem p (bs : list byte) j,
  garr8 tfibsegs (mrestrict (w_H W) mem) p (TW.zs bs) -> (j < length bs)%nat ->
  aview tfibsegs (w_H W) mem (p + Z.of_nat j) = Some (bv_unsigned (nth j bs (Z_to_bv 8 0))).
Proof.
  intros W mem p bs j HG Hj.
  assert (Hj' : (j < length (TW.zs bs))%nat) by (unfold TW.zs; rewrite length_map; exact Hj).
  pose proof (garr8_mbyte tfibsegs _ p _ j HG Hj') as Hm.
  unfold TW.zs in Hm. rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) in Hm by exact Hj'. rewrite map_nth in Hm.
  unfold aview. rewrite Hm. cbn [option_map]. f_equal. rewrite Z_to_bv_unsigned.
  apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Lemma srfw_mrd_of_view : forall (W : world tfibsegs) m a (x : byte),
  aview tfibsegs (w_H W) m a = Some (bv_unsigned x) -> mrd rsegs m (wa a) = Some x.
Proof.
  intros W m a x H. destruct (decode_aview_some W m a _ H) as (_ & bb & Hb & Eb).
  rewrite Hb. f_equal. apply bv_eq. exact Eb.
Qed.

Lemma srfw_stk_present : forall (H : word -> bool) m lo hi, 0 <= lo -> hi <= 2 ^ 64 ->
  (forall a, lo <= a < hi -> apresent H m a) -> stk rsegs m lo hi.
Proof.
  intros H m lo hi H0 H1 Hp. split; [exact H0|]. split; [exact H1|].
  intros a Ha. destruct (Hp a Ha) as [_ [bb Hb]]. unfold wa. split.
  - unfold wview. rewrite Hb. discriminate.
  - exists bb. unfold mrd. rewrite Hb. reflexivity.
Qed.

Lemma srfw_ro8 : forall m a v, bytes_at rsegs m a (le8 v) -> ro_cells rsegs m a [C8 v].
Proof. intros m a v H. split; [cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. exact H. Qed.

Lemma srfw_vis_of_view : forall (W : world tfibsegs) m a, aview tfibsegs (w_H W) m a <> None ->
  w_H W (Z_to_bv 64 a) = false.
Proof.
  intros W m a H. destruct (aview tfibsegs (w_H W) m a) as [v|] eqn:E; [exact (decode_aview_vis W m a v E)|].
  exfalso. exact (H eq_refl).
Qed.

Ltac srfw_regs EQ :=
  repeat match goal with
  | |- context [YKK.getr (ms_regs ?ms) (Z_to_bv 5 ?r)] =>
      rewrite (decode_ms_reg _ _ _ _ _ _ _ _ (Z_to_bv 5 r) EQ eq_refl)
  end.

Section Walk.
Context {fx : YKK.FPState} {rc : YM05.RunCeil}.
Local Abbreviation segs := tfibsegs.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Local Abbreviation G := TG.G_HARNESS_B.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis HCELLS : transport_cells B.
Hypothesis LAWS : AR_laws segs B.
Hypothesis MTL : ameter_laws MT.
Hypothesis HGX : gx_ok segs B G.
Hypothesis HAI : forall fx' : YKK.FPState, @aintrin_realizes fx' rc segs B OSet (transportb_sigma TB___asan_memset).

Section Call.
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
  (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate)
  (W : world segs) (memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word)
  (b len fp : Z) (frame : list byte).

Hypothesis HJ : @W_journalG.ajournal_gx rc tfib_sink_head segs B G 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k.
Hypothesis HRET : YK0s.ret_ok (YKK.getr regs (Z_to_bv 5 1)).
Hypothesis HRA4 : 4096 <= raZ regs.
Hypothesis HGP : YKK.getr regs 3 = w64 (as_gp B).
Hypothesis HTP : YKK.getr regs 4 = w64 (as_tp B).
Hypothesis H10 : YKK.getr regs 10 = w64 b.
Hypothesis H11 : YKK.getr regs 11 = w64 len.
Hypothesis H12 : YKK.getr regs 12 = w64 fp.
Hypothesis HAL : spZ regs mod 16 = 0.
Hypothesis HWLO : sp0 - STK <= spZ regs - SRF_STK.
Hypothesis HWHI : spZ regs <= sp0.
Hypothesis HB0 : 0 < b.
Hypothesis HLEN : 0 <= len <= Z.of_nat (length frame).
Hypothesis GFR : garr8 segs (mrestrict (w_H W) memc) b (TW.zs frame).
Hypothesis SOF : trans_src_ok B lyc Sc W memc b len.
Hypothesis OWF : decode_off_win regs SRF_STK b len.
Hypothesis HDIS : forall x, b <= x < b + len -> ~ srf_wr fp x.
Hypothesis HFP8 : fp mod 8 = 0.
Hypothesis HTWR : transport_twr_ok_g segs B G STK sp0 FP ly S lyc Sc own W memc (spZ regs) fp SRF_SIZE.
Hypothesis HRDP : decode_rd_ok W memc fp SRF_SIZE.
Hypothesis HOWP : decode_off_win regs SRF_STK fp SRF_SIZE.
Hypothesis HNG : forall x, fp <= x < fp + SRF_SIZE -> ~ inG G x.
Hypothesis HNEV : st_nev S + k + SRF_EV <= EV_MAX.

Lemma srfw_donor :
  AR segs B lyc Sc W memc mdc /\ astk_ok STK ly sp0 /\
  (forall a, sp0 - STK <= a < sp0 -> apresent (w_H W) memc a).
Proof.
  destruct HJ as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
  destruct HJi as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
  split; [exact HAR|]. split; [exact Hstk | exact Hpres].
Qed.

Lemma srfw_sp : YM05.alloc_ceiling + SRF_STK <= spZ regs /\ spZ regs <= 2 ^ 47.
Proof.
  destruct srfw_donor as (_ & Hstk & _). pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _). lia.
Qed.

(* The frame lies below 2^63 whatever len is (a block: below alloc_ceiling; else decode_rd_ok). *)
Lemma srfw_src_le : 0 <= b /\ b + len <= 2 ^ 63.
Proof.
  destruct srfw_donor as (HAR & _). pose proof asan_consts as (C1 & _).
  destruct SOF as [(bA & nA & Hin & Hb1 & Hb2) | (_ & (_ & _ & _ & _ & H0 & H63))]; [|lia].
  destruct (al_blocks _ _ LAWS lyc Sc W memc mdc bA nA HAR Hin) as (_ & H4096 & Hce & _ & _ & _ & Hn0).
  pose proof (req_size_pos nA (proj1 Hn0)) as [_ Hreq]. lia.
Qed.

(* What run 1 and the memset keep: everything outside the call's window and the struct (KA), presence there (GA),
   the struct present (PF). *)
Definition srfw_kept (mem2 : word -> option byte) : Prop :=
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - SRF_STK <= a < spZ regs) -> ~ (fp <= a < fp + SRF_SIZE) ->
     aview segs (w_H W) mem2 a = aview segs (w_H W) memc a) /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - SRF_STK <= a < spZ regs) -> ~ (fp <= a < fp + SRF_SIZE) ->
     apresent (w_H W) memc a -> apresent (w_H W) mem2 a) /\
  (forall a, fp <= a < fp + SRF_SIZE -> apresent (w_H W) mem2 a).

(* The bundle of run 2 at the memory mem2 the memset returned. *)
Lemma srfw_cx : forall (mem2 : word -> option byte) junk,
  srfw_kept mem2 ->
  (forall a, fp <= a < fp + SRF_SIZE -> aview segs (w_H W) mem2 a = Some 0) ->
  rw_cells rsegs mem2 (spZ regs + -48)
    (srf_fr junk (YKK.getr regs (Z_to_bv 5 19)) (YKK.getr regs (Z_to_bv 5 18)) (YKK.getr regs (Z_to_bv 5 9)) (YKK.getr regs (Z_to_bv 5 8)) (YKK.getr regs (Z_to_bv 5 1))) ->
  srf_cx (LCK.RNG_W (world segs) (@w_H segs) W) mem2 (YKK.getr regs (Z_to_bv 5 2)) b len fp frame junk
    (YKK.getr regs (Z_to_bv 5 19)) (YKK.getr regs (Z_to_bv 5 18)) (YKK.getr regs (Z_to_bv 5 9)) (YKK.getr regs (Z_to_bv 5 8)) (YKK.getr regs (Z_to_bv 5 1)).
Proof.
  intros mem2 junk (KA & GA & PF) _ FRM.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof srfw_sp as [SP1 SP2]. pose proof srfw_src_le as [BL0 BL1].
  destruct srfw_donor as (HAR & Hstk & Hpres).
  pose proof HRDP as (HvP & HraP & HhP & HmP & H0P & H63P).
  pose proof OWF as OF. pose proof HOWP as OP. unfold decode_off_win, SRF_STK, SRF_FRAME, SRF_SIZE, ESTACK in *.
  unfold srf_wr, SRF_SIZE in HDIS. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HmP.
  change (spZ regs) with (bv_unsigned (YKK.getr regs (Z_to_bv 5 2))) in *.
  set (sp := YKK.getr regs (Z_to_bv 5 2)) in *.
  assert (FPH : fp + 80 <= 2 ^ 47 - 1) by (destruct HmP; lia).
  assert (PSO : forall x, 0 <= x < 2 ^ 47 -> x / 8 + FC.ASAN_K < fp \/ fp + 80 <= x / 8 + FC.ASAN_K)
    by (intros x Hx; unfold FC.ASAN_K; destruct HmP as [Hm|Hm]; [right | left]; Z.div_mod_to_equations; lia).
  (* the frame's read range, when it has bytes *)
  assert (RDF : 0 < len -> decode_rd_ok W memc b len)
    by (intros Hl; exact (trans_src_ok_rd B LAWS lyc Sc W memc mdc b len HAR SOF Hl)).
  assert (FHI : 0 < len -> b + len <= 2 ^ 47 - 1).
  { intros Hl. destruct (RDF Hl) as (_ & _ & _ & Hm & _). unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hm.
    lia. }
  (* a shadow byte of application memory lies outside the window and the struct *)
  assert (KSH : forall x, 0 <= x < 2 ^ 47 -> (x / 8 + FC.ASAN_K < fp \/ fp + 80 <= x / 8 + FC.ASAN_K) ->
            aview segs (w_H W) mem2 (x / 8 + FC.ASAN_K) = aview segs (w_H W) memc (x / 8 + FC.ASAN_K)).
  { intros x Hx Hd. unfold FC.ASAN_K in *.
    apply KA; [Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia | destruct Hd; lia]. }
  unfold srf_cx. split; [|split; [|split]].
  - split; [exact HB0|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact HFP8|].
    split; [lia | lia].
  - split; [|split; [|split]].
    + intros i Hi. specialize (HDIS (b + i) ltac:(lia)). lia.
    + intros i Hi. pose proof (FHI ltac:(lia)). apply PSO. lia.
    + intros i Hi. apply PSO. lia.
    + lia.
  - split; [|split; [|split]].
    + intros i Hi. pose proof (FHI ltac:(lia)).
      assert (Ei : b + i = b + Z.of_nat (Z.to_nat i)) by lia.
      pose proof (srfw_garr_view W memc b frame (Z.to_nat i) GFR ltac:(lia)) as Hv. rewrite <- Ei in Hv.
      apply (srfw_mrd_of_view W). unfold srf_fb. rewrite <- Hv.
      specialize (HDIS (b + i) ltac:(lia)). apply KA; [lia | destruct OF; lia | exact HDIS].
    + intros i Hi. destruct (RDF ltac:(lia)) as (_ & Hra & _). pose proof (FHI ltac:(lia)).
      destruct (Hra (b + i) ltac:(lia)) as (s & Hs & Hok).
      assert (Ea : shadow_of_addr SHADOW_OFF (b + i) = (b + i) / 8 + FC.ASAN_K)
        by (unfold shadow_of_addr, SHADOW_OFF, FC.ASAN_K; lia).
      rewrite Ea in Hs. rewrite <- KSH in Hs; [| lia | apply PSO; lia].
      destruct (decode_aview_some W mem2 _ s Hs) as (_ & bb & Hb & Eb).
      exists bb. split; [exact Hb|].
      unfold saddr_ok in Hok. destruct Hok as [Hok|Hok]; [left | right]; rewrite (decode_byte_signed bb) by lia; lia.
    + intros i Hi.
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
      rewrite Ea, Es in Hs. rewrite <- KSH in Hs; [| lia | apply PSO; lia].
      apply (srfw_mrd_of_view W). exact Hs.
    + exact FRM.
  - destruct (Z_lt_le_dec 0 len) as [Hl | Hl].
    + destruct (RDF Hl) as (HvF & HraF & _). pose proof (FHI Hl).
      assert (VS : forall x, 0 <= x < 2 ^ 47 ->
                (exists s, aview segs (w_H W) memc (shadow_of_addr SHADOW_OFF x) = Some s) ->
                w_H W (Z_to_bv 64 (x / 8 + FC.ASAN_K)) = false).
      { intros x Hx (s & Hs). replace (x / 8 + FC.ASAN_K) with (shadow_of_addr SHADOW_OFF x)
          by (unfold shadow_of_addr, SHADOW_OFF, FC.ASAN_K; lia).
        exact (decode_aview_vis W memc _ s Hs). }
      split; [|split; [|split; [|split]]].
      * apply decode_rng; [lia | lia |]. intros x Hx. exact (proj1 (Hpres x ltac:(lia))).
      * apply decode_rng; [lia | lia |]. intros x Hx. apply (srfw_vis_of_view W memc). apply HvP. lia.
      * apply decode_rng; [lia | lia |]. intros x Hx. apply (srfw_vis_of_view W memc). apply HvF. lia.
      * intros i Hi. apply decode_rng; [unfold FC.ASAN_K; Z.div_mod_to_equations; lia
                                        | unfold FC.ASAN_K; Z.div_mod_to_equations; lia |].
        intros x Hx. replace x with ((fp + i) / 8 + FC.ASAN_K) by lia. apply VS; [lia|].
        destruct (HraP (fp + i) ltac:(lia)) as (s & Hs & _). exists s. exact Hs.
      * intros i Hi. apply decode_rng; [unfold FC.ASAN_K; Z.div_mod_to_equations; lia
                                        | unfold FC.ASAN_K; Z.div_mod_to_equations; lia |].
        intros x Hx. replace x with ((b + i) / 8 + FC.ASAN_K) by lia. apply VS; [lia|].
        destruct (HraF (b + i) ltac:(lia)) as (s & Hs & _). exists s. exact Hs.
    + assert (E0 : len = 0) by lia. subst len.
      split; [|split; [|split; [|split]]].
      * apply decode_rng; [lia | lia |]. intros x Hx. exact (proj1 (Hpres x ltac:(lia))).
      * apply decode_rng; [lia | lia |]. intros x Hx. apply (srfw_vis_of_view W memc). apply HvP. lia.
      * apply decode_rng; [lia | lia |]. intros x Hx. lia.
      * intros i Hi. apply decode_rng; [unfold FC.ASAN_K; Z.div_mod_to_equations; lia
                                        | unfold FC.ASAN_K; Z.div_mod_to_equations; lia |].
        intros x Hx. replace x with (shadow_of_addr SHADOW_OFF (fp + i))
          by (unfold shadow_of_addr, SHADOW_OFF, FC.ASAN_K in *; lia).
        destruct (HraP (fp + i) ltac:(lia)) as (s & Hs & _). exact (decode_aview_vis W memc _ s Hs).
      * intros i Hi. lia.
Qed.

(* The registers the epilogue restores are the caller's. *)
Lemma srfw_pres_ret : forall (spx r5 r6 r7 r10 r11 r12 r13 r14 r15 r16 r17 r28 r29 r30 r31 : word),
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

Lemma srfw_pres_eqv : forall (R F : bvmap 5 word) pc fc rv m ro ms',
  ms_eqv (MS R F pc fc rv m ro) ms' -> aregs_preserved regs R -> aregs_preserved regs (ms_regs ms').
Proof.
  intros R F pc fc rv m ro ms' EQV HP r Hr. unfold acallee_saved in Hr.
  assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
               r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  repeat (destruct Hc as [Hc|Hc]); subst r;
    (rewrite (decode_ms_reg R F pc fc rv m ro ms' _ EQV) by reflexivity);
    apply HP; unfold acallee_saved; lia.
Qed.

Ltac srfw_lia := unfold SRF_STK, SRF_FRAME, SRF_SIZE, ESTACK in *; lia.

(* ---- the walk ---- *)

Lemma srfw_holds :
  SRr segs W (@cfg_at fx segs (transportb_sigma TB_spec_read_frame) regs memc mdc)
    (transport_srf_post B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b fp (srf_f frame len)).
Proof.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof srfw_sp as [SP1 SP2].
  destruct srfw_donor as (HAR & Hstk & Hpres).
  pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
  pose proof HRDP as (HvP & HraP & HhP & HmP & H0P & H63P).
  pose proof OWF as OF. pose proof HOWP as OP. unfold decode_off_win in OF, OP.
  unfold SRF_STK, SRF_FRAME, SRF_SIZE, ESTACK in SP1, OF, OP, HWLO, HvP, HraP, HhP, HmP, H63P.
  assert (Hsp : spZ regs = bv_unsigned (YKK.getr regs (Z_to_bv 5 2))) by reflexivity.
  assert (GRET : ret_pc (YKK.getr regs (Z_to_bv 5 1)) = YKK.getr regs (Z_to_bv 5 1))
    by exact (LeafCgFacts.ret_ok_stmt_YK0s _ HRET).
  assert (G10 : YKK.getr regs (Z_to_bv 5 10) = w64 b) by exact H10.
  assert (G11 : YKK.getr regs (Z_to_bv 5 11) = w64 len) by exact H11.
  assert (G12 : YKK.getr regs (Z_to_bv 5 12) = w64 fp) by exact H12.
  pose proof (decode_cells_asan B HCELLS lyc Sc W memc mdc (@w_Hoff segs W) HAR) as (CK & GCK & _).
  unfold FC.CELL_K, FC.GOT_CELL_K, FC.ASAN_K in CK, GCK.
  (* ---- run 1: the entry to the call of __asan_memset ---- *)
  eapply decode_run.
  { unfold LCK.ms_of_regs. rewrite G10, G11, G12.
    eapply srf_run1_F with (lo := spZ regs - 4144).
    - apply (srfw_stk_present (w_H W)); [lia | lia |]. intros a Ha. apply Hpres. lia.
    - rewrite <- Hsp. lia.
    - exact (srfw_ro8 _ _ _ GCK).
    - exact (srfw_ro8 _ _ _ CK).
    - unfold FC.GOT_CELL_K. rewrite <- Hsp. lia.
    - unfold FC.CELL_K. rewrite <- Hsp. lia.
    - apply decode_rng; [rewrite <- Hsp; lia | rewrite <- Hsp; lia |]. intros x Hx.
      rewrite <- Hsp in Hx. exact (proj1 (Hpres x ltac:(lia))).
    - apply decode_rng; [unfold FC.GOT_CELL_K; lia | unfold FC.GOT_CELL_K; lia |]. intros x Hx. apply decode_vis_seg.
      apply (decode_covers_img FC.GOT_CELL_K 8 x); [vm_compute; reflexivity | exact Hx].
    - apply decode_rng; [unfold FC.CELL_K; lia | unfold FC.CELL_K; lia |]. intros x Hx. apply decode_vis_seg.
      apply (decode_covers_img FC.CELL_K 8 x); [vm_compute; reflexivity | exact Hx]. }
  intros msT mdT (ms0 & (m1 & junk & -> & MU1 & WM1 & ST1 & FR1 & _ & _) & EQV1) SBM1.
  rewrite (decode_ms_shape _ _ _ _ EQV1).
  rewrite <- Hsp in MU1, ST1, FR1.
  (* run 1 wrote only its frame, in the journal's stack window *)
  assert (HJ1 : @W_journalG.ajournal_gx rc tfib_sink_head segs B G 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W m1 mdT k).
  { apply (ajournal_gx_exec segs B LAWS decode_segs_low G 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
             m1 mdT (fun a => spZ regs + -48 <= a < spZ regs) HGX HJ).
    - intros x Hx. unfold mrestrict. destruct (w_H W x); [reflexivity|].
      apply MU1. cbn [outside]. split; [exact Hx | exact I].
    - intros x Hx. unfold mrestrict in *. revert Hx. destruct (w_H W x) eqn:Ehx; intros Hx; [exact Hx|].
      destruct (Z_lt_le_dec (bv_unsigned x) (spZ regs + -48)) as [Hl|Hl];
        [rewrite (MU1 x); [exact Hx | cbn [outside]; split; [lia | exact I]]|].
      destruct (Z_lt_le_dec (bv_unsigned x) (spZ regs)) as [Hh|Hh];
        [|rewrite (MU1 x); [exact Hx | cbn [outside]; split; [lia | exact I]]].
      assert (Hw : wview rsegs m1 x <> None).
      { refine (WM1 x _). unfold wview. destruct (memc x) as [bb|] eqn:Em;
          [discriminate | exfalso; first [exact (Hx Em) | exact (Hx eq_refl)]]. }
      unfold wview in Hw. destruct (m1 x) as [bb|] eqn:Em1; [discriminate|]. exfalso.
      rewrite (find_segment_none rsegs (bv_unsigned x)) in Hw; [exact (Hw eq_refl)|].
      intros Him. pose proof (decode_segs_low _ Him) as Hlow. unfold kLowMemEnd in Hlow. lia.
    - intros x Hh.
      destruct (Z_lt_le_dec (bv_unsigned x) (spZ regs + -48)) as [Hl|Hl];
        [apply (MU1 x); cbn [outside]; split; [lia | exact I]|].
      destruct (Z_lt_le_dec (bv_unsigned x) (spZ regs)) as [Hh2|Hh2];
        [|apply (MU1 x); cbn [outside]; split; [lia | exact I]].
      exfalso. pose proof (proj1 (Hpres (bv_unsigned x) ltac:(lia))) as Hhx.
      rewrite Z_to_bv_bv_unsigned in Hhx. congruence.
    - exact SBM1.
    - intros a Ha. cbv beta in Ha. left. split; [unfold awr_byte; left; lia | lia]. }
  (* what run 1 keeps *)
  assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs + -48 <= a < spZ regs) ->
            m1 (Z_to_bv 64 a) = memc (Z_to_bv 64 a)).
  { intros a Ha Hn. apply MU1. cbn [outside]. rewrite unsigned_lit_small by lia. split; [exact Hn | exact I]. }
  (* ---- __asan_memset (fp, 0, 80) ---- *)
  change (YKK.mkst (ms_regs msT) (Z_to_bv 64 SRF_MEMSET) m1 (YKK.seg_rom segs))
    with (YKK.mkst (ms_regs msT) (Z_to_bv 64 (transportb_sigma TB___asan_memset)) m1 (YKK.seg_rom segs)).
  assert (R1 : YKK.getr (ms_regs msT) 1 = Z_to_bv 64 SRF_RET1)
    by (rewrite (decode_ms_reg _ _ _ _ _ _ _ _ _ EQV1) by reflexivity; reflexivity).
  assert (Hsp1 : spZ (ms_regs msT) = spZ regs - 48).
  { assert (E2 : YKK.getr (ms_regs msT) (Z_to_bv 5 2) = Z_to_bv 64 (spZ regs + -48))
      by (rewrite (decode_ms_reg _ _ _ _ _ _ _ _ _ EQV1) by reflexivity; reflexivity).
    change (spZ (ms_regs msT)) with (bv_unsigned (YKK.getr (ms_regs msT) (Z_to_bv 5 2))).
    rewrite E2, unsigned_lit_small by lia. lia. }
  assert (Hm16 : (spZ regs - 48 - sp0) mod 16 = 0).
  { replace (spZ regs - 48 - sp0) with (spZ regs - sp0 + (-3) * 16) by lia.
    rewrite Z_mod_plus_full, Zminus_mod, HAL, Hsp0a. reflexivity. }
  assert (RD1 : decode_rd_ok W m1 fp 80).
  { apply (trans_rd_ok_view W W memc m1 fp 80 HRDP).
    - intros a Ha. apply aview_eq_of. unfold mrestrict. rewrite K1 by (destruct OP; lia). reflexivity.
    - intros s Hs. apply aview_eq_of. unfold mrestrict.
      rewrite K1 by (unfold kLowMemEnd, kHighShadowEnd in *; lia). reflexivity. }
  pose proof RD1 as (_ & HraP1 & HhP1 & _).
  eapply SRr_bind.
  { apply (gx_intrin_at segs B LAWS decode_segs_low OSet (transportb_sigma TB___asan_memset) (HAI fx) G W
             (ms_regs msT) m1 STK sp0 FP ly S W0 mem0 md0 own lyc Sc mdT k fp 0 80 (spZ regs - 48 - sp0)
             (Z_to_bv 64 SRF_RET1) HGX G_HARNESS_B_rw HJ1).
    - rewrite (decode_ms_reg _ _ _ _ _ _ _ _ _ EQV1) by reflexivity. reflexivity.
    - rewrite (decode_ms_reg _ _ _ _ _ _ _ _ _ EQV1) by reflexivity. reflexivity.
    - rewrite (decode_ms_reg _ _ _ _ _ _ _ _ _ EQV1) by reflexivity. reflexivity.
    - lia.
    - lia.
    - lia.
    - rewrite Hsp1. lia.
    - exact Hm16.
    - lia.
    - unfold ESTACK. lia.
    - rewrite (decode_ms_reg _ _ _ _ _ _ _ _ _ EQV1) by reflexivity. exact HGP.
    - rewrite (decode_ms_reg _ _ _ _ _ _ _ _ _ EQV1) by reflexivity. exact HTP.
    - exact R1.
    - apply YK0s.ret_ok_even. vm_compute. reflexivity.
    - intros a Ha. destruct (HTWR a ltac:(srfw_lia)) as [(Hw & (Hv & bb & Hb) & Ho & _) | HGa]; [left | right; exact HGa].
      split; [exact Hw|]. split; [split; [exact Hv|]; exists bb; rewrite K1 by (destruct OP; lia); exact Hb|].
      split; [exact Ho|]. rewrite Hsp1. unfold ESTACK. destruct OP; lia.
    - exact HmP.
    - exact HraP1.
    - intros _. exact HhP1.
    - exact I. }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & _ & Hset & Heff & Hgr).
  (* what the memset keeps, and the struct it leaves *)
  assert (KT : srfw_kept mem2).
  { split; [|split].
    - intros a Ha Hw Hs. rewrite (Heff a Ha) by (unfold ESTACK; srfw_lia).
      apply aview_eq_of. unfold mrestrict. rewrite K1 by srfw_lia. reflexivity.
    - intros a Ha Hw Hs (Hv & bb & Hb). apply Hgr. split; [exact Hv|]. exists bb.
      rewrite K1 by srfw_lia. exact Hb.
    - intros a Ha. destruct (HTWR a Ha) as [(_ & (Hv & bb & Hb) & _) | HGa]; [| exfalso; exact (HNG a Ha HGa)].
      apply Hgr. split; [exact Hv|]. exists bb. rewrite K1 by (unfold SRF_SIZE in Ha; destruct OP; lia). exact Hb. }
  assert (HZ : forall a, fp <= a < fp + SRF_SIZE -> aview segs (w_H W) mem2 a = Some 0).
  { intros a Ha. replace a with (fp + (a - fp)) by lia. rewrite (Hset (a - fp) ltac:(srfw_lia)). reflexivity. }
  (* the journal's stack window is present at m1 and at mem2 *)
  assert (Hw1 : forall a, sp0 - STK <= a < sp0 -> apresent (w_H W) m1 a).
  { destruct HJ1 as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
    destruct HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hp & _). exact Hp. }
  assert (Hw2 : forall a, sp0 - STK <= a < sp0 -> apresent (w_H W) mem2 a).
  { destruct HJ2 as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
    destruct HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hp & _). exact Hp. }
  (* the five saves, kept by the memset (its window lies below them) *)
  assert (FR2 : rw_cells rsegs mem2 (spZ regs + -48)
                  (srf_fr junk (YKK.getr regs (Z_to_bv 5 19)) (YKK.getr regs (Z_to_bv 5 18))
                     (YKK.getr regs (Z_to_bv 5 9)) (YKK.getr regs (Z_to_bv 5 8)) (YKK.getr regs (Z_to_bv 5 1)))).
  { apply (decode_frame_ext (spZ regs + -48) 48 _ m1 mem2); [unfold srf_fr; cbn [cells_size csize]; lia | | exact FR1].
    intros i Hi.
    exact (decode_present_eq W m1 mem2 (spZ regs + -48 + i) (Hw1 (spZ regs + -48 + i) ltac:(lia))
             (Hw2 (spZ regs + -48 + i) ltac:(lia))
             (Heff (spZ regs + -48 + i) ltac:(lia) ltac:(destruct OP; lia) ltac:(unfold ESTACK; lia))). }
  (* the struct: 80 zero bytes *)
  assert (ST0 : rw_cells rsegs mem2 fp (srf_cells 0 0 0 0 0 0 0 0 0 (Z_to_bv 8 0) (Z_to_bv 8 0) 0 0 0 0)).
  { assert (E : cells_bytes (srf_cells 0 0 0 0 0 0 0 0 0 (Z_to_bv 8 0) (Z_to_bv 8 0) 0 0 0 0)
                = repeat (Z_to_bv 8 0) 80) by reflexivity.
    destruct KT as (_ & _ & PF).
    split; [split|].
    - cbn [cells_wf cell_wf srf_cells]. repeat split.
    - rewrite E. split; [lia|]. split; [rewrite repeat_length; lia|].
      intros i Hi. rewrite repeat_length in Hi. rewrite nth_error_repeat by exact Hi.
      apply (srfw_mrd_of_view W). rewrite (HZ (fp + Z.of_nat i) ltac:(srfw_lia)). reflexivity.
    - split; [lia|]. split; [cbn; lia|]. intros i Hi.
      destruct (PF (fp + i) ltac:(cbn in Hi; srfw_lia)) as [_ [bb Hb]]. unfold wview, wa. rewrite Hb. discriminate. }
  pose proof (srfw_cx mem2 junk KT HZ FR2) as CX.
  (* ---- run 2: the memset's return to the `ret` ---- *)
  change (mkCfg (YKK.mkst regs2 (Z_to_bv 64 SRF_RET1) mem2 (YKK.seg_rom segs)) md2)
    with (@cfg_at fx segs SRF_RET1 regs2 mem2 md2).
  eapply decode_run.
  { unfold LCK.ms_of_regs.
    rewrite (HP2 2 ltac:(unfold acallee_saved; lia)), (HP2 3 ltac:(unfold acallee_saved; lia)),
      (HP2 4 ltac:(unfold acallee_saved; lia)), (HP2 8 ltac:(unfold acallee_saved; lia)),
      (HP2 9 ltac:(unfold acallee_saved; lia)), (HP2 18 ltac:(unfold acallee_saved; lia)),
      (HP2 19 ltac:(unfold acallee_saved; lia)), (HP2 20 ltac:(unfold acallee_saved; lia)),
      (HP2 21 ltac:(unfold acallee_saved; lia)), (HP2 22 ltac:(unfold acallee_saved; lia)),
      (HP2 23 ltac:(unfold acallee_saved; lia)), (HP2 24 ltac:(unfold acallee_saved; lia)),
      (HP2 25 ltac:(unfold acallee_saved; lia)), (HP2 26 ltac:(unfold acallee_saved; lia)),
      (HP2 27 ltac:(unfold acallee_saved; lia)).
    srfw_regs EQV1.
    eapply srf_run2_F; [exact CX | apply munch_refl | apply wmono_refl | exact ST0]. }
  intros ms3 md3 (ms0' & (x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & spx & m'
                          & -> & Hspx & MU2 & WM2 & HB2) & EQV3) SBM3.
  rewrite (decode_ms_shape _ _ _ _ EQV3). rewrite GRET.
  destruct KT as (KA & GA & PF).
  eapply srf_close with (mem2 := mem2) (md2 := md2) (m' := m');
    first [ exact LAWS | exact MTL | exact HGX | exact HJ | exact HWLO | exact HWHI | exact HTWR
          | exact HRDP | exact HOWP | exact HNG | exact HJ2 | exact KA | exact GA | exact PF
          | exact MU2 | exact WM2 | exact HB2 | exact SBM3 | idtac ].
  - apply (srfw_pres_eqv _ _ _ _ _ _ _ _ EQV3). apply srfw_pres_ret. rewrite Hspx. reflexivity.
  - rewrite (decode_ms_reg _ _ _ _ _ _ _ _ _ EQV3) by reflexivity. reflexivity.
Qed.

End Call.
End Walk.

Theorem transport_spec_read_frame_cg_holds : forall fx rc B MT,
  @transport_spec_read_frame_cg_holds_stmt fx rc B MT.
Proof.
  intros fx rc B MT HC LW ML HG HA. unfold transport_spec_read_frame_cg.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs b len fp frame
    HJ HRET HRA4 HGP HTP H10 H11 H12 HAL HWLO HWHI HB0 HLEN GFR SOF OWF HDIS HFP8 HTWR HRDP HOWP HNG HNEV.
  eapply srfw_holds;
    first [ exact HC | exact LW | exact ML | exact HG | exact HA | exact HJ | exact HRET | exact HRA4 | exact HGP
          | exact HTP | exact H10 | exact H11 | exact H12 | exact HAL | exact HWLO | exact HWHI | exact HB0
          | exact HLEN | exact GFR | exact SOF | exact OWF | exact HDIS | exact HFP8 | exact HTWR | exact HRDP
          | exact HOWP | exact HNG | exact HNEV ].
Qed.

Print Assumptions transport_spec_read_frame_cg_holds.
