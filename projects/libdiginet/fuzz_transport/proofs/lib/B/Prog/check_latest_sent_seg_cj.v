(* check_latest_sent_seg_cj: the caller-journal helpers of the ASan image-B walk of check_latest_sent
   (lib/B/Prog/check_latest_sent_cg.v). Each is about the G journal of lib/A/W_journalG.v (over
   lib/B/TransportGB.v G_HARNESS_B) and the world relation of lib/A/Prog/TWorldG.v at lib/B/Prog/TWorldB.v TMAP_B;
   none of them steps the machine.
     - cls_tw_raw / cls_tw_av: the world relation read at the walk's image view (aview) and at the machine's
       view (check_state_wake_c.v csw_view) are the same relation, because every payload byte of TMAP_B is a
       byte of G_HARNESS_B, hence an image byte, which no world hides;
     - cls_jexec: the G journal carried across one footprint run of the walk, from the run's munch and growth
       facts and the placement of every byte the run writes (W_journalG.v ajournal_gx_exec);
     - cls_bcmp: the bcmp wrapper's contract (YG0d.v abcmp_realizes) read at the walk's G journal, through
       YCbq.v aj_bcmp_at and TransportGCg.v gx_call_leaf;
     - cls_tagged: tagged_of's leaf statement (lib/B/Prog/tagged_of_cg.v, read at this unit's model by
       DgnTransportBCg.v transport_leaf_at) at the walk's G journal, through gx_call_leaf and the leaf bridge
       lib/B/Prog/DgnTransportBLeafb.v decode_leafb_journal;
     - cls_close_kept: the walk's acall_kept_g at the memory the post reads the out cell back in;
     - the walk's chaining facts: cls_chain (a run that starts where the last one ended, through
       lib/B/Prog/TransportFevt.v decode_run), the memory facts a call keeps (cls_mem_call, cls_fr_call), the
       constant-pool word read from trans_rom_view_rd (cls_kw_of_rom), and tagged_of_m of a round (cls_tag_m). *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YK11 YK0s YK0o YM05 YK04 YA0i YA0n YG00 YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00 YI04 YP09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c YK1b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Frame Cells Step ExecF Regs6ss.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBAddr DgnTransportBImg DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB check_state_wake_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_set_cg check_latest_sent_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBLeafb TransportFevt.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require LeafCgKit LeafCgGlue AsanKA tagged_of_c
  tagged_of_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import check_latest_sent_seg_model.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require check_latest_sent_seg_kit
  check_latest_sent_seg_runs.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TWorldLemmas TCb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TGJ := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TWJ := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TCJ := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TWLJ := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module DSJ := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module FCJ := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.AsanCells.
Module LCJ := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.LeafCgKit.
Module AKJ := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.AsanKA.
Module TOC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.tagged_of_c.
Module LTJ := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.tagged_of_cg.
Module LMJ := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Mem.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* the model: tagged_of_m of a round                                   *)
(* ------------------------------------------------------------------ *)

(* The round's let*: tagged_of_m of the bytes from pos on finds the serial cls_round names, and keeps the world. *)
Lemma cls_tag_m : forall (Bc body : list byte) len pos s,
  Z.of_nat (length body) = len -> 0 <= pos -> 3 <= len - pos ->
  TWJ.u_at body pos 1 = TCJ.TAG ->
  s = Z.lor (Z.shiftl (TWJ.u_at body (pos + 2) 1) 7) (TWJ.u_at body (pos + 1) 1) ->
  0 <= s < TCJ.CMDS_MAX -> s < TWJ.g_ncmd Bc ->
  TCJ.tagged_of_m Bc (skipn (Z.to_nat pos) body) (len - pos) = Some (Bc, Some s).
Proof.
  intros Bc body len pos s Hlen Hpos H3 HT Hs Hs0 Hsn.
  assert (L : length (skipn (Z.to_nat pos) body) = (Z.to_nat len - Z.to_nat pos)%nat)
    by (rewrite length_skipn; lia).
  assert (A0 : TWJ.u_at body pos 1 = DSJ.at8 (skipn (Z.to_nat pos) body) 0).
  { replace pos with (pos + 0) at 1 by lia. rewrite (cls_u_at8 body pos 0) by lia. reflexivity. }
  assert (A1 : TWJ.u_at body (pos + 1) 1 = DSJ.at8 (skipn (Z.to_nat pos) body) 1).
  { rewrite (cls_u_at8 body pos 1) by lia. reflexivity. }
  assert (A2 : TWJ.u_at body (pos + 2) 1 = DSJ.at8 (skipn (Z.to_nat pos) body) 2).
  { rewrite (cls_u_at8 body pos 2) by lia. reflexivity. }
  unfold TCJ.tagged_of_m.
  rewrite (proj2 (Z.ltb_ge (len - pos) 3) H3).
  rewrite (proj2 (Nat.ltb_ge (length (skipn (Z.to_nat pos) body)) 1)) by lia.
  rewrite <- A0, HT, Z.eqb_refl. cbn [negb].
  rewrite (proj2 (Nat.ltb_ge (length (skipn (Z.to_nat pos) body)) 3)) by lia.
  rewrite <- A1, <- A2, Z.lor_comm, <- Hs.
  rewrite (proj2 (Z.ltb_lt s (TWJ.g_ncmd Bc)) Hsn).
  rewrite (proj2 (Z.leb_gt TCJ.CMDS_MAX s)) by lia.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* the world at the image view and at the machine view                 *)
(* ------------------------------------------------------------------ *)

(* every payload byte of TMAP_B is a byte of G_HARNESS_B *)
Lemma cls_tw_in_G : forall x, tw_in TMAP_B x -> inG TGJ.G_HARNESS_B x.
Proof.
  intros x (o & b & n & Hin & Hx).
  pose proof (TMAP_B_in_G o b n Hin) as HG.
  unfold inG. apply Exists_exists. exists (b, n). split; [exact HG|].
  unfold in_zr. cbn [fst snd]. lia.
Qed.

(* a byte of G_HARNESS_B is an image byte, so no world hides it *)
Lemma cls_vis_G : forall (W : world tfibsegs) x, inG TGJ.G_HARNESS_B x -> w_H W (Z_to_bv 64 x) = false.
Proof.
  intros W x Hx.
  pose proof (trans_g_img x Hx) as Hi.
  pose proof (transportb_segs_low x Hi) as Hl. unfold kLowMemEnd in Hl.
  apply (hidden_not_img tfibsegs W (Z_to_bv 64 x)).
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Z.mod_small by lia. exact Hi.
Qed.

Lemma cls_vis : forall (W : world tfibsegs) x, tw_in TMAP_B x -> w_H W (Z_to_bv 64 x) = false.
Proof. intros W x Hx. exact (cls_vis_G W x (cls_tw_in_G x Hx)). Qed.

(* a visible byte: the image view is the machine view *)
Lemma cls_aview_csw : forall (W : world tfibsegs) (m : word -> option byte) x, w_H W (Z_to_bv 64 x) = false ->
  aview tfibsegs (w_H W) m x = csw_view m x.
Proof.
  intros W m x Hx. unfold csw_view, aview, mbyte, mrestrict, mrd, wa.
  rewrite Hx. reflexivity.
Qed.

Lemma cls_tw_raw : forall (W : world tfibsegs) (m : word -> option byte) Bw,
  tw_at TMAP_B (aview tfibsegs (w_H W) m) Bw -> tw_at TMAP_B (csw_view m) Bw.
Proof.
  intros W m Bw H. apply (tw_kept TMAP_B (aview tfibsegs (w_H W) m) (csw_view m) Bw H).
  intros x Hx. symmetry. exact (cls_aview_csw W m x (cls_vis W x Hx)).
Qed.

Lemma cls_tw_av : forall (W : world tfibsegs) (m : word -> option byte) Bw,
  tw_at TMAP_B (csw_view m) Bw -> tw_at TMAP_B (aview tfibsegs (w_H W) m) Bw.
Proof.
  intros W m Bw H. apply (tw_kept TMAP_B (csw_view m) (aview tfibsegs (w_H W) m) Bw H).
  intros x Hx. exact (cls_aview_csw W m x (cls_vis W x Hx)).
Qed.

(* a visible byte whose view a step keeps keeps its machine read *)
Lemma cls_mrd_kept : forall (W : world tfibsegs) (m m2 : word -> option byte) x,
  w_H W (Z_to_bv 64 x) = false -> aview tfibsegs (w_H W) m2 x = aview tfibsegs (w_H W) m x ->
  mrd rsegs m2 (wa x) = mrd rsegs m (wa x).
Proof.
  intros W m m2 x Hx E.
  rewrite (cls_aview_csw W m2 x Hx), (cls_aview_csw W m x Hx) in E. unfold csw_view in E.
  destruct (mrd rsegs m2 (wa x)) as [b1|]; destruct (mrd rsegs m (wa x)) as [b2|];
    cbn [option_map] in E; try discriminate E; [|reflexivity].
  injection E as E. f_equal. apply bv_eq. exact E.
Qed.

(* ------------------------------------------------------------------ *)
(* the constant-pool word, read from trans_rom_view_rd                  *)
(* ------------------------------------------------------------------ *)

Lemma cls_ksent_ro : forall i, 0 <= i < 8 -> trans_in_ro_rd (66360 + i).
Proof.
  intros i Hi. unfold trans_in_ro_rd, TRANS_RO_RD. apply Exists_app. left.
  do 4 apply Exists_cons_tl. apply Exists_cons_hd. unfold in_zr, TRANS_K_SENT. cbn [fst snd]. lia.
Qed.

(* The 8 bytes at 0x10338 in the image, little-endian: 0xcccccccccccccccd (compared through bv_unsigned, which
   vm_compute decides on closed terms). *)
Lemma cls_ksent_rom_u : forall i, (i < 8)%nat ->
  option_map (fun b : byte => bv_unsigned b) (PropExec.seg_rom rsegs (wa (66360 + Z.of_nat i))) =
  option_map (fun b : byte => bv_unsigned b) (nth_error (le8 (wa 14757395258967641293)) i).
Proof.
  intros i Hi.
  do 8 (destruct i as [|i]; [vm_compute; reflexivity|]). lia.
Qed.

Lemma cls_ksent_rom : forall i, (i < 8)%nat ->
  PropExec.seg_rom rsegs (wa (66360 + Z.of_nat i)) =
  nth_error (le8 (wa 14757395258967641293)) i.
Proof.
  intros i Hi. pose proof (cls_ksent_rom_u i Hi) as E.
  destruct (PropExec.seg_rom rsegs (wa (66360 + Z.of_nat i))) as [b1|];
    destruct (nth_error (le8 (wa 14757395258967641293)) i) as [b2|];
    cbn [option_map] in E; try discriminate E; [|reflexivity].
  injection E as E. f_equal. apply bv_eq. exact E.
Qed.

Lemma cls_kw_of_rom : forall (W : world tfibsegs) (m : word -> option byte),
  trans_rom_view_rd W m ->
  bytes_at rsegs m 66360 (le8 (wa 14757395258967641293)).
Proof.
  intros W m HR. split; [lia|]. split; [rewrite length_le8; lia|].
  intros i Hi. rewrite length_le8 in Hi.
  pose proof (cls_ksent_ro (Z.of_nat i) ltac:(lia)) as Hro.
  pose proof (HR _ Hro) as E.
  assert (Hv : w_H W (Z_to_bv 64 (66360 + Z.of_nat i)) = false).
  { destruct (trans_ro_rd_rom_clean _ Hro) as [_ [b Hb]].
    apply (decode_leafb_aview_vis W m _ (bv_unsigned b)). rewrite E, Hb. reflexivity. }
  rewrite (cls_aview_csw W m _ Hv) in E. unfold csw_view in E.
  rewrite <- (cls_ksent_rom i Hi).
  change (YK11.seg_rom tfibsegs (Z_to_bv 64 (66360 + Z.of_nat i)))
    with (PropExec.seg_rom rsegs (wa (66360 + Z.of_nat i))) in E.
  destruct (mrd rsegs m (wa (66360 + Z.of_nat i))) as [b1|];
    destruct (PropExec.seg_rom rsegs (wa (66360 + Z.of_nat i))) as [b2|];
    cbn [option_map] in E; try discriminate E; [|reflexivity].
  injection E as E. f_equal. apply bv_eq. exact E.
Qed.

(* ------------------------------------------------------------------ *)
(* the walk's chaining facts                                           *)
(* ------------------------------------------------------------------ *)

Lemma cls_ms_eqv_trans : forall a b c, Regs6ss.ms_eqv a b -> Regs6ss.ms_eqv b c -> Regs6ss.ms_eqv a c.
Proof.
  intros a b c (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8) (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8).
  split; [|repeat split; congruence].
  intros r Hr. rewrite (A1 r Hr). exact (B1 r Hr).
Qed.

Section chain. Context {fx : YK11.FPState}.

(* A footprint run that starts at the state the last run ended in (register-equivalent to its MS form): the walk
   goes on with the new run, from every state register-equivalent to one it reaches. *)
Lemma cls_chain : forall (W : world tfibsegs) (R : bvmap 5 word) (pc : Z) (m : word -> option byte) (md' : Model)
    (ms2 : machine_state) (P : machine_state -> Prop) (Q : world tfibsegs -> config -> Prop),
  Regs6ss.ms_eqv (MS R (@YK11.fp_regs fx) (Z_to_bv 64 pc) (@YK11.fp_csr fx) None m (YK11.seg_rom rsegs)) ms2 ->
  ExecF.evtF rsegs (LCJ.RNG_W (world tfibsegs) (@w_H tfibsegs) W) P
    (MS R (@YK11.fp_regs fx) (Z_to_bv 64 pc) (@YK11.fp_csr fx) None m (YK11.seg_rom rsegs)) ->
  (forall ms1 ms3 md'', P ms1 -> Regs6ss.ms_eqv ms1 ms3 -> YK1b.mem_grows m (ms_mem ms1) ->
     same_but_materialized md' md'' -> SRr tfibsegs W (mkCfg ms3 md'') Q) ->
  SRr tfibsegs W (mkCfg ms2 md') Q.
Proof.
  intros W R pc m md' ms2 P Q HE HR K.
  pose proof HE as HE0.
  destruct (@decode_eqv_mkst fx R (Z_to_bv 64 pc) m ms2 HE) as (R' & -> & HX).
  change (mkCfg (@YK11.mkst fx R' (Z_to_bv 64 pc) m (YK11.seg_rom BImg0.rsegs)) md')
    with (@cfg_at fx tfibsegs pc R' m md').
  apply (@decode_run fx W R' m md' pc
           (fun ms => exists ms1, P ms1 /\ Regs6ss.ms_eqv ms1 ms /\ YK1b.mem_grows m (ms_mem ms1))).
  - apply (LeafCgGlue.evtF_eqv rsegs _ P _ _ HR).
    apply (cls_ms_eqv_trans _ _ _ HE0).
    apply Regs6ss.ms_eqv_sym. exact (@LeafCgGlue.ms_of_regs_eqv fx pc R' m).
  - intros ms1 ms3 md'' (ms0 & HP & HE1 & HG1) HE2 _ Hs.
    exact (K ms0 ms3 md'' HP (cls_ms_eqv_trans _ _ _ HE1 HE2) HG1 Hs).
Qed.

End chain.


(* ------------------------------------------------------------------ *)
(* the G journal across one run of the walk, and across the two calls  *)
(* ------------------------------------------------------------------ *)

Section cjj. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis HGX : gx_ok tfibsegs B TGJ.G_HARNESS_B.
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head tfibsegs B).

(* The G journal after a run of the walk's own code: the run wrote only bytes of Wr, each of them a byte the
   journal may change (an awr_byte that is present, or a byte of G), and it only added bytes. *)
Lemma cls_jexec :
  forall STK sp0 FP ly S (W0 : world tfibsegs) mem0 md0 own lyc Sc (W : world tfibsegs)
         (m m' : word -> option byte) mdc mdc' k (Wr : Z -> Prop),
  ajournal_gx TGJ.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W m mdc k ->
  (forall z : word, ~ Wr (bv_unsigned z) -> m' z = m z) ->
  (forall z : word, m z <> None -> m' z <> None) ->
  same_but_materialized mdc mdc' ->
  (forall a, Wr a ->
     (awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ apresent (w_H W) m a)
     \/ inG TGJ.G_HARNESS_B a) ->
  ajournal_gx TGJ.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W m' mdc' k.
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W m m' mdc mdc' k Wr HJ Hfr Hgr Hsame HW.
  apply (@ajournal_gx_exec rc tfib_sink_head tfibsegs B LAWS transportb_segs_low
           TGJ.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W m mdc k m' mdc' Wr HGX HJ).
  - intros z Hz. unfold mrestrict. rewrite (Hfr z Hz). reflexivity.
  - intros z Hz. unfold mrestrict in *. destruct (w_H W z) eqn:E; [exact Hz | exact (Hgr z Hz)].
  - intros z Hh. apply Hfr. intros HWz.
    destruct (HW (bv_unsigned z) HWz) as [(_ & Hp) | Hg].
    + destruct Hp as (Hhid & _). rewrite Z_to_bv_bv_unsigned in Hhid. rewrite Hhid in Hh. discriminate.
    + pose proof (proj1 (HGX (bv_unsigned z) Hg)) as Hi.
      rewrite (hidden_not_img tfibsegs W z Hi) in Hh. discriminate.
  - exact Hsame.
  - intros a Ha. destruct (HW a Ha) as [(Hw & _) | Hg];
      [left; split; [exact Hw | lia] | right; left; exact Hg].
Qed.

(* The bcmp wrapper's contract, read at the walk's own G journal (TransportGCg.v gx_call_leaf over YCbq.v
   aj_bcmp_at): the journal and every byte outside the wrapper's own stack window are kept, and a0 is 0 exactly
   when the two ranges hold the same bytes. *)
Lemma cls_bcmp :
  forall (STK sp0 : Z) FP ly S (W0 : world tfibsegs) mem0 md0 own lyc Sc (W : world tfibsegs)
         (memT : word -> option byte) mdc k (regsT : bvmap 5 word) (x y n o : Z) (raw : word),
  @abcmp_realizes fx rc tfibsegs B (transportb_sigma TB___interceptor_trampoline_bcmp) ->
  ajournal_gx TGJ.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memT mdc k ->
  YK11.getr regsT 10 = w64 x -> YK11.getr regsT 11 = w64 y -> YK11.getr regsT 12 = w64 n ->
  0 <= n < 2 ^ 32 -> 0 <= x -> x + n <= 2 ^ 63 -> 0 <= y -> y + n <= 2 ^ 63 ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 2 * ESTACK - o <= STK ->
  YK11.getr regsT 3 = w64 (as_gp B) -> YK11.getr regsT 4 = w64 (as_tp B) ->
  YK11.getr regsT 1 = raw -> YK0s.ret_ok raw ->
  src_ok tfibsegs W regsT memT x n -> src_ok tfibsegs W regsT memT y n ->
  (forall a, x <= a < x + n -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o)) ->
  (forall a, y <= a < y + n -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o)) ->
  amem_range x n -> amem_range y n ->
  range_addressable (aview tfibsegs (w_H W) memT) SHADOW_OFF x n ->
  (0 < n -> shadow_hull_vis (aview tfibsegs (w_H W) memT) x n) ->
  range_addressable (aview tfibsegs (w_H W) memT) SHADOW_OFF y n ->
  (0 < n -> shadow_hull_vis (aview tfibsegs (w_H W) memT) y n) ->
  SRr tfibsegs W
    (mkCfg (@YK11.mkst fx regsT (Z_to_bv 64 (transportb_sigma TB___interceptor_trampoline_bcmp)) memT
              (YK11.seg_rom tfibsegs)) mdc)
    (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
       c2 = mkCfg (@YK11.mkst fx regs2 raw mem2 (YK11.seg_rom tfibsegs)) md2 /\
       ajournal_gx TGJ.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k /\
       (exists v : word, aregs_preserved regsT regs2 /\ YK11.getr regs2 10 = v /\
          (v = w64 0 <-> forall i, 0 <= i < n ->
             aview tfibsegs (w_H W) memT (x + i) = aview tfibsegs (w_H W) memT (y + i)) /\
          (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o) ->
             aview tfibsegs (w_H W) mem2 a = aview tfibsegs (w_H W) memT a) /\
          (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a))).
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memT mdc k regsT x y n o raw
    AM HJ H10 H11 H12 Hn Hx0 Hxn Hy0 Hyn Hsp Hal Hneg Hbud Hgp Htp Hra Hraw
    Hsx Hsy Hbx Hby Hmx Hmy Hrx Hhx Hry Hhy.
  apply (@gx_call_leaf fx rc tfib_sink_head tfibsegs B TGJ.G_HARNESS_B STK sp0 FP ly S W0 mem0 md0 own
           lyc Sc W memT mdc k _ raw _ HJ).
  intros memS HJi.
  eapply SRr_mono.
  { exact (@aj_bcmp_at fx rc tfib_sink_head tfibsegs B LAWS transportb_segs_low
             (transportb_sigma TB___interceptor_trampoline_bcmp) AM W regsT memT STK sp0 FP ly S W0 memS md0 own
             lyc Sc mdc k x y n o raw HJi H10 H11 H12 Hn Hx0 Hxn Hy0 Hyn Hsp Hal Hneg Hbud Hgp Htp Hra Hraw
             Hsx Hsy Hbx Hby Hmx Hmy Hrx Hhx Hry Hhy). }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & Hc & HJ2 & HP & Hres & Hcmp & Hfr2 & Hpres2).
  split; [reflexivity|]. exists regs2, mem2, md2. split; [exact Hc|]. split; [exact HJ2|].
  exists v. split; [exact HP|]. split; [exact Hres|]. split; [exact Hcmp|]. split; [exact Hfr2 | exact Hpres2].
Qed.

(* tagged_of's leaf statement, read at the walk's own G journal (gx_call_leaf over the leaf bridge
   decode_leafb_journal): the journal and every byte outside the leaf's ESTACK window below sp are kept, the
   callee-saved registers are kept, and a0 is tagged_of_res t. The leaf's own premises are the call state's facts
   (a0 = b, a1 = n, the bytes l at b, the world, tagged_of_m), the stack and runtime cells the journal gives, and
   when 3 <= n the three bytes at b: off the leaf's frame, addressable, visible with their shadow bytes. *)
Lemma cls_tagged :
  forall (STK sp0 : Z) FP ly S (W0 : world tfibsegs) mem0 md0 own lyc Sc (W : world tfibsegs)
         (memT : word -> option byte) mdc k (regsT : bvmap 5 word) (o b n : Z) (l Bw : list byte) (t : option Z),
  transport_cells B ->
  (forall fx' : YK11.FPState, @transport_leaf_at rc B (@LTJ.transport_tagged_of_cg) fx') ->
  ajournal_gx TGJ.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memT mdc k ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
  YK11.getr regsT 3 = w64 (as_gp B) -> YK11.getr regsT 4 = w64 (as_tp B) ->
  YK0s.ret_ok (YK11.getr regsT 1) ->
  YK11.getr regsT 10 = Z_to_bv 64 b -> YK11.getr regsT 11 = Z_to_bv 64 n ->
  0 <= n < 2 ^ 64 -> 0 < b ->
  bytes_at rsegs memT b l ->
  tw_at TMAP_B (csw_view memT) Bw ->
  TCJ.tagged_of_m Bw l n = Some (Bw, t) ->
  (3 <= n -> b + 3 <= spZ regsT - 16 \/ spZ regsT <= b) ->
  (3 <= n -> FCJ.addressable memT b 3) ->
  (3 <= n -> forall i, 0 <= i < 3 -> w_H W (Z_to_bv 64 (b + i)) = false) ->
  (3 <= n -> forall s, FCJ.shadow_addr b <= s <= FCJ.shadow_addr (b + 2) -> w_H W (Z_to_bv 64 s) = false) ->
  SRr tfibsegs W (mkCfg (@YK11.mkst fx regsT (Z_to_bv 64 TOC.TAGGED_OF) memT (YK11.seg_rom tfibsegs)) mdc)
    (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
       c2 = mkCfg (@YK11.mkst fx regs2 (YK11.getr regsT 1) mem2 (YK11.seg_rom tfibsegs)) md2 /\
       ajournal_gx TGJ.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k /\
       (aregs_preserved regsT regs2 /\ YK11.getr regs2 10 = w64 (TOC.tagged_of_res t) /\
        (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regsT - ESTACK <= a < spZ regsT) ->
           aview tfibsegs (w_H W) mem2 a = aview tfibsegs (w_H W) memT a) /\
        (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a))).
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memT mdc k regsT o b n l Bw t
    HCELLS LEAF HJ Hsp Hal Hneg Hbud Hgp Htp Hra H10 H11 Hn Hb0 HBL HTW HTM HOFFB HADB HVB HVS.
  apply (@gx_call_leaf fx rc tfib_sink_head tfibsegs B TGJ.G_HARNESS_B STK sp0 FP ly S W0 mem0 md0 own
           lyc Sc W memT mdc k _ (YK11.getr regsT 1)
           (fun regs2 mem2 md2 => aregs_preserved regsT regs2 /\ YK11.getr regs2 10 = w64 (TOC.tagged_of_res t) /\
              (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regsT - ESTACK <= a < spZ regsT) ->
                 aview tfibsegs (w_H W) mem2 a = aview tfibsegs (w_H W) memT a) /\
              (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)) HJ).
  intros memS HJi.
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
  pose proof Hstk as (_ & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
  pose proof (@YM05.alloc_ceiling_val rc) as [CEIL1 CEIL2].
  eapply SRr_mono.
  { apply (@decode_leafb_journal fx rc tfib_sink_head B LAWS W regsT memT STK sp0 FP ly S W0 memS md0 own
             lyc Sc mdc k o TOC.TAGGED_OF (Some (TOC.tagged_of_res t)) [] (fun _ => Bw = Bw) HJi
             Hsp Hal Hneg Hbud Hra Hgp Htp).
    - intros a Ha. unfold LCJ.in_wr in Ha. inversion Ha.
    - intros HPRE.
      pose proof (LEAF fx) as LF.
      unfold transport_leaf_at, LTJ.transport_tagged_of_cg in LF.
      specialize (LF lyc Sc W regsT memT mdc (sp0 - STK) Bw Bw b n l t HPRE).
      cbv zeta in LF.
      assert (HSP : bv_unsigned (YK11.getr regsT (Z_to_bv 5 2)) = sp0 + o) by exact Hsp.
      unfold ESTACK in Hbud.
      apply LF; clear LF.
      + exact H10.
      + exact H11.
      + exact Hn.
      + exact Hb0.
      + exact HBL.
      + exact HTW.
      + exact HTM.
      + rewrite HSP. apply (decode_leafb_stk_journal B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJi); lia.
      + rewrite HSP. unfold TOC.TAGGED_OF_FRAME. lia.
      + unfold AKJ.off_stk. rewrite HSP.
        unfold TOC.TAGGED_OF_FRAME, TGJ.G_HARNESS_B_LO, TGJ.G_HARNESS_B_HI. lia.
      + exact (decode_leafb_asan_cells B HCELLS lyc Sc W memT mdc (proj1 HPRE)).
      + rewrite HSP. apply (@decode_leafb_app_stack rc). unfold TOC.TAGGED_OF_FRAME. lia.
      + rewrite HSP. apply (@decode_leafb_app_stack rc). lia.
      + unfold AKJ.off_stk. rewrite HSP. unfold TOC.TAGGED_OF_FRAME, FCJ.GOT_CELL_K. lia.
      + unfold AKJ.off_stk. rewrite HSP. unfold TOC.TAGGED_OF_FRAME, FCJ.CELL_K. lia.
      + intros H3. unfold AKJ.off_stk. rewrite HSP. unfold TOC.TAGGED_OF_FRAME.
        specialize (HOFFB H3). rewrite Hsp in HOFFB. lia.
      + exact HADB.
      + rewrite HSP. apply (decode_leafb_rng_journal B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJi);
          unfold TOC.TAGGED_OF_FRAME; lia.
      + exact (proj1 (decode_leafb_rng_cells W)).
      + exact (proj2 (decode_leafb_rng_cells W)).
      + apply decode_rng_vis; [unfold TOC.TAGGED_OF_NCMD, TB_g_ncmd; lia | unfold TOC.TAGGED_OF_NCMD, TB_g_ncmd; lia |].
        intros i Hi. apply cls_vis. exists TWJ.OFF_g_ncmd, TB_g_ncmd, TWJ.SZ_g_ncmd.
        split; [exact TMAP_B_g_ncmd | unfold TOC.TAGGED_OF_NCMD, TWJ.SZ_g_ncmd in *; lia].
      + intros H3. destruct (HADB H3) as (_ & _ & Hend & _). unfold FCJ.APPMEM_END in Hend.
        apply decode_rng_vis; [lia | lia | exact (HVB H3)].
      + intros H3. destruct (HADB H3) as (_ & _ & Hend & _). unfold FCJ.APPMEM_END in Hend.
        apply decode_rng_vis.
        * unfold FCJ.shadow_addr, FCJ.ASAN_K. pose proof (Z.div_pos b 8 ltac:(lia) ltac:(lia)). lia.
        * unfold FCJ.shadow_addr, FCJ.ASAN_K. Z.div_mod_to_equations. lia.
        * intros i Hi. apply (HVS H3).
          assert (FCJ.shadow_addr b <= FCJ.shadow_addr (b + 2))
            by (unfold FCJ.shadow_addr; apply Z.add_le_mono_r; apply Z.div_le_mono; lia).
          lia. }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & Hc & HJ2 & HP & Hres & Heff & Hgr & _).
  split; [reflexivity|]. exists regs2, mem2, md2. split; [exact Hc|]. split; [exact HJ2|].
  split; [exact HP|]. split; [exact (Hres _ eq_refl)|]. split; [|exact Hgr].
  intros a Ha Hw. apply (Heff a Ha Hw). intros Hx. unfold LCJ.in_wr in Hx. inversion Hx.
Qed.

End cjj.

(* ------------------------------------------------------------------ *)
(* what the walk keeps, at the memory the out cell is read back in     *)
(* ------------------------------------------------------------------ *)

Section cjk. Context {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis HGX : gx_ok tfibsegs B TGJ.G_HARNESS_B.

Lemma cls_gover_mem : forall outs (ma mb : word -> option byte) a, 0 <= a < 2 ^ 64 ->
  gover outs ma mb (Z_to_bv 64 a) = if inGb outs a then mb (Z_to_bv 64 a) else ma (Z_to_bv 64 a).
Proof.
  intros outs ma mb a Ha. unfold gover.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
  rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma cls_gover_in : forall outs (H : word -> bool) (ma mb : word -> option byte) a,
  0 <= a < 2 ^ 64 -> inG outs a -> aview tfibsegs H (gover outs ma mb) a = aview tfibsegs H mb a.
Proof.
  intros outs H ma mb a Ha Hin. apply aview_eq_of. unfold mrestrict.
  rewrite (cls_gover_mem outs ma mb a Ha), (proj2 (inGb_spec outs a) Hin). reflexivity.
Qed.

(* every byte the walk stores that is not the caller's int at dp is a byte of a harness global *)
Lemma cls_wr_G : forall dp a, cls_wr dp a -> ~ (dp <= a < dp + 4) -> inG TGJ.G_HARNESS_B a.
Proof.
  intros dp a Hw Hn. unfold inG. apply Exists_exists.
  destruct Hw as [(s & Hs & Hf) | [Hf | [Hf | Hf]]].
  - exists (TB_g_cmd, TWJ.SZ_g_cmd). split.
    + exact (TMAP_B_in_G _ _ _ TMAP_B_g_cmd).
    + unfold twb_fld, TWJ.A_Cmd_st, TWJ.OFF_g_cmd, TB_g_cmd, TWJ.SZ_g_cmd in *.
      unfold TCJ.CMDS_MAX in Hs. unfold in_zr. cbn [fst snd]. lia.
  - exists (TB_g_q, TWJ.SZ_g_q). split.
    + exact (TMAP_B_in_G _ _ _ TMAP_B_g_q).
    + unfold twb_fld, TWJ.OFF_g_q, TB_g_q, TWJ.SZ_g_q in *. unfold in_zr. cbn [fst snd]. lia.
  - exists (TB_g_nq, TWJ.SZ_g_nq). split.
    + exact (TMAP_B_in_G _ _ _ TMAP_B_g_nq).
    + unfold twb_fld, TWJ.OFF_g_nq, TB_g_nq, TWJ.SZ_g_nq in *. unfold in_zr. cbn [fst snd]. lia.
  - exfalso. exact (Hn Hf).
Qed.

Lemma cls_wr_low : forall dp a, cls_wr dp a -> ~ (dp <= a < dp + 4) -> 0 <= a < kLowMemEnd.
Proof.
  intros dp a Hw Hn. apply transportb_segs_low. exact (proj1 (HGX a (cls_wr_G dp a Hw Hn))).
Qed.

(* The walk's own kept fact, at the memory TransportGCg.v transport_cg_post_out reads: the four bytes at dp put
   back as they were at the call, every other byte the walk's runs left. *)
Lemma cls_close_kept :
  forall lyc Sc (W : world tfibsegs) (memc : word -> option byte) mdc (mF : word -> option byte)
         (dp slo shi : Z),
  @AR rc tfibsegs B lyc Sc W memc mdc ->
  @YM05.alloc_ceiling rc <= slo -> shi <= 2 ^ 64 ->
  (forall a, slo <= a < shi -> apresent (w_H W) memc a) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (slo <= a < shi) -> ~ cls_wr dp a ->
     aview tfibsegs (w_H W) mF a = aview tfibsegs (w_H W) memc a) ->
  (forall a, apresent (w_H W) memc a -> apresent (w_H W) mF a) ->
  acall_kept_g tfibsegs B TGJ.G_HARNESS_B lyc Sc W memc W (gover [(dp, 4)] mF memc) slo shi (cls_wr dp).
Proof.
  intros lyc Sc W memc mdc mF dp slo shi HAR Hce Hshi Hpres KA GA.
  pose proof (@YM05.alloc_ceiling_val rc) as [CEIL1 CEIL2].
  assert (HdpG : forall a, 0 <= a < 2 ^ 64 -> inG [(dp, 4)] a -> dp <= a < dp + 4).
  { intros a Ha Hin. apply Exists_exists in Hin as (r & Hr & Hx). cbn [In] in Hr.
    destruct Hr as [<- | []]. unfold in_zr in Hx. cbn [fst snd] in Hx. lia. }
  assert (HdpG' : forall a, dp <= a < dp + 4 -> inG [(dp, 4)] a).
  { intros a Ha. unfold inG. apply Exists_exists. exists (dp, 4). split; [left; reflexivity|].
    unfold in_zr. cbn [fst snd]. lia. }
  apply (@dk_kept_step_g rc tfibsegs B LAWS transportb_segs_low TGJ.G_HARNESS_B lyc Sc W memc mdc memc
           (gover [(dp, 4)] mF memc) slo shi (cls_wr dp)
           (fun a => (slo <= a < shi) \/ (cls_wr dp a /\ ~ (dp <= a < dp + 4))) HAR).
  - apply dk_kept_refl_g. exact Hpres.
  - intros a Ha Hn.
    destruct (Z_le_dec dp a) as [H1|H1]; [destruct (Z_lt_dec a (dp + 4)) as [H2|H2]|].
    + rewrite (cls_gover_in [(dp, 4)] (w_H W) mF memc a Ha (HdpG' a ltac:(lia))). reflexivity.
    + rewrite (gover_out_aview tfibsegs [(dp, 4)] (w_H W) mF memc a Ha
                 ltac:(intros Hin; pose proof (HdpG a Ha Hin); lia)).
      apply KA; [exact Ha | intros Hx; apply Hn; left; exact Hx
                | intros Hx; apply Hn; right; split; [exact Hx | lia]].
    + rewrite (gover_out_aview tfibsegs [(dp, 4)] (w_H W) mF memc a Ha
                 ltac:(intros Hin; pose proof (HdpG a Ha Hin); lia)).
      apply KA; [exact Ha | intros Hx; apply Hn; left; exact Hx
                | intros Hx; apply Hn; right; split; [exact Hx | lia]].
  - intros a (Hh & b & Hb). split; [exact Hh|].
    unfold gover. destruct (inGb [(dp, 4)] (bv_unsigned (Z_to_bv 64 a))).
    + exists b. exact Hb.
    + destruct (GA a (conj Hh (ex_intro _ b Hb))) as (_ & b' & Hb'). exists b'. exact Hb'.
  - intros a [Hw | (Hw & Hn)] Hac.
    + exact Hw.
    + exfalso. pose proof (cls_wr_low dp a Hw Hn) as Hl. unfold kLowMemEnd in Hl. lia.
  - intros b m i Hb Hi [Hw | (Hw & _)]; [|exact Hw]. exfalso.
    destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hb) as (_ & H4096 & Hbc & _). lia.
  - intros a [Hw | (Hw & Hn)] Hi HnG _ _.
    + pose proof (transportb_segs_low a Hi) as Hl. unfold kLowMemEnd in Hl. lia.
    + exact (HnG (cls_wr_G dp a Hw Hn)).
  - intros cid pos a Hin Hr [Hw | (Hw & _)]; [|exact Hw]. exfalso.
    destruct (frames_bounds tfibsegs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (F4096 & Fce & _).
    pose proof (fs_frame_bytes_nonneg cid) as Hfs.
    destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [lia|].
    pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hfs) as Hse.
    assert (Hd : (frame_addr lyc cid pos + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8)
      by (apply Z.div_le_mono; lia).
    pose proof (Z.div_pos (frame_addr lyc cid pos) 8 ltac:(lia) ltac:(lia)).
    unfold shadow_addr, SHADOW_OFF in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia.
Qed.

End cjk.

(* ------------------------------------------------------------------ *)
(* list, interval and model helpers of the glue                        *)
(* ------------------------------------------------------------------ *)

(* the bytes of a suffix of a range *)
Lemma cls_bytes_skipn : forall (m : word -> option byte) A (l : list byte) k,
  bytes_at rsegs m A l -> (k <= length l)%nat -> bytes_at rsegs m (A + Z.of_nat k) (skipn k l).
Proof.
  intros m A l k (H0 & H1 & Hb) Hk.
  split; [lia|]. rewrite length_skipn. split; [lia|].
  intros i Hi. rewrite nth_error_skipn.
  replace (A + Z.of_nat k + Z.of_nat i) with (A + Z.of_nat (k + i)) by lia.
  apply Hb. lia.
Qed.

(* two non-empty ranges with no common byte do not overlap *)
Lemma cls_disj_of_pt : forall a n b p, 0 < n -> 0 < p ->
  (forall x, a <= x < a + n -> ~ (b <= x < b + p)) -> a + n <= b \/ b + p <= a.
Proof.
  intros a n b p Hn Hp H.
  destruct (Z_le_gt_dec (a + n) b) as [E|E]; [left; exact E|].
  destruct (Z_le_gt_dec (b + p) a) as [F|F]; [right; exact F|].
  exfalso. apply (H (Z.max a b)); lia.
Qed.

(* the four bytes of a word built little-endian from them *)
Lemma clsh_le4_bytes : forall b0 b1 b2 b3 : byte,
  le4 (wa (bv_unsigned b0 + 256 * bv_unsigned b1 + 65536 * bv_unsigned b2 + 16777216 * bv_unsigned b3)) =
  [b0; b1; b2; b3].
Proof.
  intros b0 b1 b2 b3.
  pose proof (bv_unsigned_in_range 8 b0) as R0. pose proof (bv_unsigned_in_range 8 b1) as R1.
  pose proof (bv_unsigned_in_range 8 b2) as R2. pose proof (bv_unsigned_in_range 8 b3) as R3.
  unfold bv_modulus in R0, R1, R2, R3. change (2 ^ Z.of_N 8) with 256 in R0, R1, R2, R3.
  assert (E : forall X (b : byte), X mod 256 = bv_unsigned b -> Z_to_bv 8 X = b).
  { intros X b HX. apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
    change (2 ^ Z.of_N 8) with 256. exact HX. }
  assert (S8 : forall x, Z.shiftr x 8 = x / 256).
  { intros x. rewrite Z.shiftr_div_pow2 by lia. reflexivity. }
  unfold le4. rewrite wa_unsigned by lia. cbn [Z_to_le_bytes]. rewrite !S8.
  refine (f_equal2 cons (E _ _ _) (f_equal2 cons (E _ _ _) (f_equal2 cons (E _ _ _)
            (f_equal2 cons (E _ _ _) eq_refl)))); Z.div_mod_to_equations; lia.
Qed.

(* four present bytes are one C4 cell (of the word they hold, little-endian) *)
Lemma cls_c4_present : forall (H : word -> bool) (m : word -> option byte) A,
  0 <= A -> A + 4 <= 2 ^ 64 -> (forall i, 0 <= i < 4 -> apresent H m (A + i)) ->
  exists v : word, Step.rw_cells rsegs m A [Cells.C4 v].
Proof.
  intros H m A H0 H1 Hp.
  destruct (Hp 0 ltac:(lia)) as (_ & b0 & E0).
  destruct (Hp 1 ltac:(lia)) as (_ & b1 & E1).
  destruct (Hp 2 ltac:(lia)) as (_ & b2 & E2).
  destruct (Hp 3 ltac:(lia)) as (_ & b3 & E3).
  exists (wa (bv_unsigned b0 + 256 * bv_unsigned b1 + 65536 * bv_unsigned b2 + 16777216 * bv_unsigned b3)).
  split; [split|].
  - exact (conj I I).
  - cbn [Cells.cells_bytes Cells.cbytes]. rewrite app_nil_r, clsh_le4_bytes.
    split; [exact H0|]. split; [cbn [length]; lia|].
    intros i Hi. cbn [length] in Hi. unfold mrd, wa.
    destruct i as [|[|[|[|i]]]]; cbn [nth_error]; [| | | | lia].
    + replace (A + Z.of_nat 0) with (A + 0) by lia. rewrite E0. reflexivity.
    + replace (A + Z.of_nat 1) with (A + 1) by lia. rewrite E1. reflexivity.
    + replace (A + Z.of_nat 2) with (A + 2) by lia. rewrite E2. reflexivity.
    + replace (A + Z.of_nat 3) with (A + 3) by lia. rewrite E3. reflexivity.
  - split; [exact H0|]. split; [cbn [Cells.cells_size Cells.csize]; lia|].
    intros i Hi. cbn [Cells.cells_size Cells.csize] in Hi.
    destruct (Hp i ltac:(lia)) as (_ & b & Eb). exact (decode_wview_some m _ b Eb).
Qed.

(* a round of the loop changes no byte of g_cmd's payload but the st fields (the first 4 bytes of each command) *)
Lemma cls_agree_round : forall Bc s B2, Z.of_nat (length Bc) = TWJ.W_LEN -> 0 <= s < TCJ.CMDS_MAX ->
  TCJ.q_remove_m (TWJ.set_Cmd_st Bc s TCJ.SENT) s = Some (B2, tt) ->
  forall j i, 0 <= j < 1024 -> 4 <= i < 40 ->
  TWJ.u_at B2 (TWJ.OFF_g_cmd + 40 * j + i) 1 = TWJ.u_at Bc (TWJ.OFF_g_cmd + 40 * j + i) 1.
Proof.
  intros Bc s B2 HL Hs H.
  pose (P := fun X : list byte => forall j i, 0 <= j < 1024 -> 4 <= i < 40 ->
    TWJ.u_at X (TWJ.OFF_g_cmd + 40 * j + i) 1 = TWJ.u_at Bc (TWJ.OFF_g_cmd + 40 * j + i) 1).
  assert (PQ : forall X k v, Z.of_nat (length X) = TWJ.W_LEN -> 0 <= k < TCJ.CMDS_MAX -> P X ->
                 P (TWJ.set_Q_at X k v)).
  { intros X k v HX Hk PX j i Hj Hi. unfold TWJ.set_Q_at.
    rewrite TWLJ.u_at_upd_out by cls_lia. exact (PX j i Hj Hi). }
  assert (PN : forall X v, Z.of_nat (length X) = TWJ.W_LEN -> P X -> P (TWJ.set_g_nq X v)).
  { intros X v HX PX j i Hj Hi. unfold TWJ.set_g_nq.
    rewrite TWLJ.u_at_upd_out by cls_lia. exact (PX j i Hj Hi). }
  assert (P1 : P (TWJ.set_Cmd_st Bc s TCJ.SENT)).
  { intros j i Hj Hi. unfold TWJ.set_Cmd_st. apply TWLJ.u_at_upd_out; cls_lia. }
  destruct (cls_qrm_gen P PQ PN _ s B2 H (cls_len_set_st Bc s TCJ.SENT HL Hs) P1) as (_ & P2 & _).
  exact P2.
Qed.

(* ------------------------------------------------------------------ *)
(* what a call keeps                                                   *)
(* ------------------------------------------------------------------ *)

(* The bytes cls_mem reads: the world's payloads, the caller's int at dp, the body, and the shadow bytes of g_cmd's
   and g_q's payloads, of dp and of the body. *)
Definition cls_mem_bytes (dp bp len : Z) (a : Z) : Prop :=
  tw_in TMAP_B a \/ (dp <= a < dp + 4) \/ (bp <= a < bp + len) \/
  (exists i, 0 <= i < 40960 /\ a = FCJ.shadow_addr (6180992 + i)) \/
  (exists i, 0 <= i < 4096 /\ a = FCJ.shadow_addr (6232192 + i)) \/
  (exists i, 0 <= i < 4 /\ a = FCJ.shadow_addr (dp + i)) \/
  (exists i, 0 <= i < len /\ a = FCJ.shadow_addr (bp + i)).

(* A call that keeps the view of every byte outside its window [lo, hi) and every present byte keeps cls_mem, when
   every byte cls_mem reads is visible and outside the window, and the bytes at dp are present. *)
Lemma cls_mem_call : forall (W : world tfibsegs) (m m2 : word -> option byte) (Bc body : list byte)
    (dp bp len : Z) (v : word) (lo hi : Z),
  check_latest_sent_seg_runs.cls_mem m Bc body dp bp len v ->
  Z.of_nat (length body) = len ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview tfibsegs (w_H W) m2 a = aview tfibsegs (w_H W) m a) ->
  (forall a, apresent (w_H W) m a -> apresent (w_H W) m2 a) ->
  (forall a, cls_mem_bytes dp bp len a ->
     0 <= a < 2 ^ 64 /\ ~ (lo <= a < hi) /\ w_H W (Z_to_bv 64 a) = false) ->
  (forall a, dp <= a < dp + 4 -> apresent (w_H W) m a) ->
  check_latest_sent_seg_runs.cls_mem m2 Bc body dp bp len v.
Proof.
  intros W m m2 Bc body dp bp len v lo hi HM HL KV GP HB HP.
  destruct HM as (Htw & Hrw & Hbody & Ha1 & Ha2 & Ha3 & Ha4 & Hwok).
  assert (MRD : forall a, cls_mem_bytes dp bp len a -> mrd rsegs m2 (wa a) = mrd rsegs m (wa a)).
  { intros a Ha. destruct (HB a Ha) as (R & O & V). exact (cls_mrd_kept W m m2 a V (KV a R O)). }
  assert (ADR : forall p n, FCJ.addressable m p n ->
            (forall i, 0 <= i < n -> cls_mem_bytes dp bp len (FCJ.shadow_addr (p + i))) ->
            FCJ.addressable m2 p n).
  { intros p n (A0 & A1 & A2 & A3) Hs. split; [exact A0|]. split; [exact A1|]. split; [exact A2|].
    intros i Hi. destruct (A3 i Hi) as (Happ & b & Hb & Hok). split; [exact Happ|].
    exists b. split; [|exact Hok]. rewrite (MRD _ (Hs i Hi)). exact Hb. }
  unfold check_latest_sent_seg_runs.cls_mem.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))).
  - apply (tw_kept TMAP_B (csw_view m) (csw_view m2) Bc Htw).
    intros x Hx. unfold csw_view. rewrite (MRD x (or_introl Hx)). reflexivity.
  - apply (decode_rw_cells_eq m m2 dp _ Hrw). intros i Hi. cbn [Cells.cells_size Cells.csize] in Hi.
    pose proof (HP (dp + i) ltac:(lia)) as P1.
    assert (Hd : cls_mem_bytes dp bp len (dp + i)) by (right; left; lia).
    destruct (HB (dp + i) Hd) as (R & O & V).
    exact (decode_byte_eq (w_H W) (w_H W) m m2 (dp + i) P1 (GP _ P1) (KV _ R O)).
  - unfold check_latest_sent_seg_runs.cls_body in *. destruct Hbody as (B0 & B1 & Bb).
    split; [exact B0|]. split; [exact B1|]. intros i Hi. rewrite <- (Bb i Hi).
    apply MRD. right; right; left. lia.
  - apply (ADR _ _ Ha1). intros i Hi. right; right; right; left. exists i. split; [lia | reflexivity].
  - apply (ADR _ _ Ha2). intros i Hi. right; right; right; right; left. exists i. split; [lia | reflexivity].
  - apply (ADR _ _ Ha3). intros i Hi. right; right; right; right; right; left. exists i.
    split; [lia | reflexivity].
  - apply (ADR _ _ Ha4). intros i Hi. right; right; right; right; right; right. exists i.
    split; [lia | reflexivity].
  - unfold check_latest_sent_seg_kit.cls_wok in *. intros a Ha.
    assert (Hb : cls_mem_bytes dp bp len a).
    { destruct Ha as [Ha | [Ha | [Ha | Ha]]].
      - left. exists TWJ.OFF_g_cmd, TB_g_cmd, TWJ.SZ_g_cmd. split; [exact TMAP_B_g_cmd|].
        unfold TB_g_cmd, TWJ.SZ_g_cmd. lia.
      - left. exists TWJ.OFF_g_q, TB_g_q, TWJ.SZ_g_q. split; [exact TMAP_B_g_q|].
        unfold TB_g_q, TWJ.SZ_g_q. lia.
      - left. exists TWJ.OFF_g_nq, TB_g_nq, TWJ.SZ_g_nq. split; [exact TMAP_B_g_nq|].
        unfold TB_g_nq, TWJ.SZ_g_nq. lia.
      - right; left. exact Ha. }
    destruct (HB a Hb) as (R & O & V).
    destruct (m2 (wa a)) as [b2|] eqn:E2.
    + exact (decode_wview_some m2 (wa a) b2 E2).
    + destruct (m (wa a)) as [b1|] eqn:E1.
      * exfalso.
        assert (Pm : apresent (w_H W) m a) by (split; [exact V | exists b1; exact E1]).
        destruct (GP a Pm) as (_ & b' & E'). unfold wa in E2. rewrite E2 in E'. discriminate E'.
      * pose proof (Hwok a Ha) as W1. unfold wview in W1 |- *. rewrite E2. rewrite E1 in W1. exact W1.
Qed.

(* Cells whose bytes are present before and after a step that keeps their view are kept. *)
Lemma cls_cells_call : forall (W : world tfibsegs) (m m2 : word -> option byte) A cs,
  Step.rw_cells rsegs m A cs ->
  (forall i, 0 <= i < Z.of_nat (Cells.cells_size cs) ->
     apresent (w_H W) m (A + i) /\ apresent (w_H W) m2 (A + i) /\
     aview tfibsegs (w_H W) m2 (A + i) = aview tfibsegs (w_H W) m (A + i)) ->
  Step.rw_cells rsegs m2 A cs.
Proof.
  intros W m m2 A cs HC HK.
  apply (decode_rw_cells_eq m m2 A cs HC).
  intros i Hi. destruct (HK i Hi) as (P1 & P2 & E).
  exact (decode_byte_eq (w_H W) (w_H W) m m2 (A + i) P1 P2 E).
Qed.
