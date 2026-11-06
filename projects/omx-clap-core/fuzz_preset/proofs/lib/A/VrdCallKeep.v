(* fuzz_preset, slice S5b, the Ival walk's lane (a Theorem Labs lane): THE ONE transport of parse_items' loop positions across a CALL
   (a Theorem Labs lane's ruling, 2026-10-29: the Ival walk writes it once; the element step's parse_value call (row 231), the key
   step's parse_string call (row 148) and the grow step's grow call (row 281) cite it; IelemE / IproD import it).
   The position after a call, vrd_pos_after_call, is in lib/A/VrdCallPos.v (it needs VrdLedgerStep, which needs
   VrdIStep, which needs this file: moved out to break that import cycle, 2026-10-29, statement unchanged).
   rule 24: no function proved
   rule 24: proves no function (kind: segment lemma). No walk and no callee: the callee is an ABSTRACT journal
   (YCbqG.ajournal_x) whose footprint FP1 is only bounded; no function's text is named here.

   WHAT IT GIVES (vrd_call_keep). A loop position P at the call (vrd_iframe, vrd_ijrn), and a later position P2 whose
   machine state the callee's journal reaches from P's - the two facts YCbqG / VrdArm.vrd_call_W(F) hand back after the
   call: the callee's ajournal_x at the caller's window top (spZ (ie_regs E) + ie_e E), own = [], and the agreement
   over [sp0 - 144, sp0 + e) off FP1 - with sp kept. FP1's bytes are the cursor's p word [q, q + 8), its depth word
   [q + 16, q + 20) or allocator bytes in [4096, alloc_ceiling) (parse_string's [(q, q + 8)], parse_value's rd_fp q
   (kids + 56 n), grow's node fields and arrays all fit). Five conclusions, each about ONE view:
   1. vrd_iframe E P2 - P2's restricted memory view rdW (ip_W P2) (ip_mem P2): the saved words, the spill slots and
      their presence;
   2. vrd_ijrn's caller-window clause at P2 - P2's reader view aview (w_H (ip_W P2)) (ip_mem P2) against the entry's
      aview (w_H (ie_W E)) (ie_mem E);
   3. vrd_ijrn's arodata_okP at P2 - P2's reader view;
   4. vrd_ijrn's chain at P2 - P2's layout and reader view, at the loop's sp; by IelemE's vrd_chain_keep_w (VrdIElem.v,
      a working branch 2e1d73b494d) at ly' := ip_ly P2, with layout_le's ly_top conjunct of the callee's journal;
   5. when every block of P is still a block of P2: rd_keep from P's restricted view rdW (ip_W P) (ip_mem P) to P2's
      (byte values AND write permission) over the node's 56 bytes and the bytes of P's blocks ip_D P, off FP1 - the
      bytes VrdFrame's keep lemmas need for vrd_inode's header, elements, members and free slots;
   WHAT IT DOES NOT GIVE, by design (a Theorem Labs lane's split, 2026-10-29): the shadow facts no journal clause keeps and the
   text's bytes and home. Those are IelemE's lemmas in lib/A/VrdIStep.v (a working branch da5334ad793, Section S),
   stated for ANY later state the entry's journal reaches, about THAT state's view, derived there from the ARx shadow
   laws: vrd_icur_after_call (src_rd of the text, prhReader_home, range_addressable q 24), vrd_node_ra_after_call
   (range_addressable v 56), vrd_lam_shadow (a ledger block's range_addressable and shadow_hull_vis: the kids / keys
   arrays). A caller applies them at P2 beside this lemma; nothing here concludes a shadow fact, so no shadow
   hypothesis is carried. The composed journal (vrd_ijrn's first conjunct), frm_zero / fregs_kept_x and
   rd_blocks_move come from vrd_call_W(F) and the callee's post; the ledger, the cursor's new p and the model from the
   callee's post.
   WHY IT HOLDS. Every byte above alloc_ceiling and at or above the loop's sp is either in [sp0 - 144, sp0 + e) (the
   agreement premise) or above sp0 + e (the journal's above-window clause); FP1 meets that range only in the cursor
   cells, which rd_fp q v excludes. The node and P's blocks are heap or fake-frame bytes, kept by the journal's block and
   frame clauses (the node's place is prhPv_node's prhReader_at at entry, carried to P by rd_blocks_move; its window
   case is empty by vrd_node_low); off the image (AR_laws_x's client-image law) aview equality is raw-byte equality,
   which keeps the write permission too. Image bytes ride on the journal's image clause: FP1 does not hold address 0
   (fp_spares), and the statics are not read-only (H_pst_ro).
   ONE SECTION HYPOTHESIS besides the engine laws, an image fact: H_pst_ro (alloc.c's statics are not read-only
   bytes; IelemE's VrdIStep.v carries the same fact under the same name; discharged at prh_img_A by S1ImgA.v
   pst_not_ro_A).
   SET: a working branch on a working branch da5334ad793 (VrdIElem.v blob b128cf8b1fb1); record texts
   a working branch 49745a1a153 (PRH_FnParse.v blob e21b8b02d69e), texts on walkkit-next 0afb3f76c28
   (PRH_Base.v blob 438b875ec3ce, PRH_FnReader.v blob ba3a5407e12b), YCbqG.v blob 83da015952be. Nothing here reads the
   position pass: the file uses only VrdIElem.v, PRH_Base / PRH_FnParse / PRH_FnReader definitions and the engine
   (ajournal_x, AR_laws_x). A-only: B sites not measured.
   Numerals: 144 (LENGTH, parse_items' frame, as VrdIElem.v states it), 56 / 24 / 20 / 16 / 8 (LENGTH: node, cursor,
   cursor cells), 4096 / 2 ^ 47 / 2 ^ 64 (LENGTH: bounds). No ADDRESS literal.
   A'LEDGER (a Theorem Labs lane, 2026-10-29): the one ledger site takes prh_ledger's g_most / g_own_ran_out fields (kit
   PRH_Base.v blob ee2f5cd7ed35, S1Ledger.prh_ledger_hblock's most own after a k); no statement here changed.
   The kit's CUT (lane RBase, a working branch 7cdbb61b5fa0: PRH_Base.v ef7c8ca98529, PRH_FnParse.v
   f0d92dcec7e9, PRH_FnReader.v f1ae32e3b2cd). DW is gone: the lemmas take the cursor set CW where they took DW. The
   cut's callee posts are BUDGETED (parse_value / parse_string at wbudget CW 0, fuzz_free at wbudget [tr] 0), so
   vrd_call_keep takes the callee's journal at ANY budget WS1 (ajournal_xw; ajournal_x is its WS1 = [] case, so the
   old premise is an instance and no conclusion changes). vrd_reader_call_pre's cursor conclusions follow the cut's
   texts: prh_cur_ok is DELETED (PRH_Base.v:1093), parse_string asks prh_cw_ok B CW (:1483) beside prh_cur_low, and
   parse_value asks prh_cur_entry (no DW, :1111) beside prh_cw_entry B CW (:1488), now one slot. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames YGcfRoomPre YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import
Img0 Listing_prog PAImg_prog PRH_Base PRH_Img PRH_Reader PRH_FnReader PRH_Charge PRH_FnParse VrdFrame VrdIElem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1Ledger.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
(* this file's lia goals over `mod` need Zify's euclidean-division flag on *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PI : PrhImg} {RL : PrhRoomLive}.
#[local] Notation PAI := PI_prog_A.
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PAI).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
#[local] Notation rdW W mem := (mrestrict (w_H W) mem).

(* ---- off the image, two reader views that agree at an address agree on the raw byte there ---- *)
Lemma vc_raw : forall (H H' : word -> bool) (m m' : word -> option byte) a,
  0 <= a < 2 ^ 64 -> ~ in_img SEGS a -> aview SEGS H' m' a = aview SEGS H m a ->
  mrestrict H' m' (Z_to_bv 64 a) = mrestrict H m (Z_to_bv 64 a).
Proof.
  intros H H' m m' a Ha Hi E. unfold aview, mbyte in E.
  rewrite (seg_rom_none SEGS a Ha Hi) in E.
  destruct (mrestrict H' m' (Z_to_bv 64 a)) as [b'|], (mrestrict H m (Z_to_bv 64 a)) as [b|]; cbn in E;
    try discriminate E; [|reflexivity].
  injection E as E. f_equal. apply bv_eq. exact E.
Qed.

(* ... so the byte and its write permission are kept *)
Lemma vc_keep_byte : forall (H H' : word -> bool) (m m' : word -> option byte) a,
  0 <= a < 2 ^ 64 -> ~ in_img SEGS a -> aview SEGS H' m' a = aview SEGS H m a ->
  mbyte SEGS (mrestrict H' m') a = mbyte SEGS (mrestrict H m) a /\
  (writable_at SEGS (mrestrict H m) a -> writable_at SEGS (mrestrict H' m') a).
Proof.
  intros H H' m m' a Ha Hi E. pose proof (vc_raw H H' m m' a Ha Hi E) as R.
  split; [unfold mbyte; rewrite R; reflexivity|].
  unfold writable_at, wview. rewrite R. exact (fun x => x).
Qed.

(* ... and its presence *)
Lemma vc_apresent : forall (H H' : word -> bool) (m m' : word -> option byte) a,
  0 <= a < 2 ^ 64 -> ~ in_img SEGS a -> aview SEGS H' m' a = aview SEGS H m a ->
  apresent H m a -> apresent H' m' a.
Proof.
  intros H H' m m' a Ha Hi E [Hh (b & Hb)]. pose proof (vc_raw H H' m m' a Ha Hi E) as R.
  unfold mrestrict in R. rewrite Hh, Hb in R.
  destruct (H' (Z_to_bv 64 a)) eqn:Eh; [discriminate R|]. split; [exact Eh|]. exists b. exact R.
Qed.

(* the byte-level keep over a set of non-image addresses whose reader views agree *)
Lemma vc_rd_keep : forall (H H' : word -> bool) (m m' : word -> option byte) (Pz : Z -> Prop),
  (forall a, Pz a -> 0 <= a < 2 ^ 64 /\ ~ in_img SEGS a /\ aview SEGS H' m' a = aview SEGS H m a) ->
  rd_keep SEGS (mrestrict H m) (mrestrict H' m') Pz.
Proof.
  intros H H' m m' Pz HP. split; intros a Ha; destruct (HP a Ha) as (Hr & Hi & E);
    destruct (vc_keep_byte H H' m m' a Hr Hi E) as [E1 E2]; [exact E1 | exact E2].
Qed.

Context {HL : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx HL.
(* image fact: alloc.c's statics are not read-only bytes (the statement and name of IelemE's VrdIStep.v H_pst_ro;
   discharged at prh_img_A by S1ImgA.v pst_not_ro_A) *)
Variable H_pst_ro : forall a, Exists (in_zr a) prh_pst -> ~ in_roP SEGS pa_relro_lo pa_relro_hi a.

(* the stack and node bounds of a call of parse_items *)
Lemma vc_bounds : forall CTX CTX0 CW E, pi_frame F_parse_items = 144 -> vrd_ient_ok B ARx CTX CTX0 CW E ->
  alloc_ceiling <= spZ (ie_regs E) - 144 /\ 0 <= ie_e E /\ spZ (ie_regs E) + ie_e E <= 2 ^ 47 /\
  spZ (ie_regs E) <= ie_q E /\ ie_q E + 24 <= spZ (ie_regs E) + ie_e E /\
  4096 <= ie_v E /\ ie_v E + 56 <= alloc_ceiling /\ 144 <= STK_parse_items (ie_d E).
Proof.
  intros CTX CTX0 CW E Himg HEN.
  pose proof (vrd_node_low B ARx HL LAWS CTX CTX0 CW E HEN) as Hvceil.
  assert (HSTK : 144 <= STK_parse_items (ie_d E)).
  { unfold STK_parse_items. rewrite Himg. pose proof (pi_frame_nonneg F_parse_value).
    assert (0 <= LEAF_pv_pi) by (unfold LEAF_pv_pi, zmaxl; cbn [fold_right]; lia).
    assert (0 <= Z.of_nat (PjGrammar.MAXD - ie_d E) * (pi_frame F_parse_value + 144))
      by (apply Z.mul_nonneg_nonneg; lia).
    lia. }
  destruct HEN as ((HAF & _) & _ & _ & _ & HRD & _).
  destruct HAF as (_ & _ & _ & _ & _ & Hstk & _).
  destruct Hstk as (_ & HS0 & Hceil & Hslo & Hshi & H47 & _ & Htop & Htop2).
  destruct HRD as (_ & _ & _ & _ & _ & (He0 & _ & Hetop & _) & Hq0 & Hq24 & _ & _ & _ & _ & (Hv4 & _) & _).
  repeat split; lia.
Qed.

(* ==== THE TRANSPORT. The callee's journal is at any world relation R (implicit): the re-hiding move's callees post
   it at wle' SEGS RZ_cf, and no step here reads its world conjunct ==== *)
Lemma vrd_call_keep {R : world SEGS -> world SEGS -> Prop} : forall CTX CTX0 CW E P P2 STKc FP1 k1 WS1,
  pi_frame F_parse_items = 144 -> pi_s0cur F_parse_items = Some 0 ->
  vrd_ient_ok B ARx CTX CTX0 CW E -> vrd_iframe E P -> vrd_ijrn B ARx SK E P ->
  (* the callee's footprint: the cursor's p and depth words, or allocator bytes *)
  (forall a, inFP FP1 a ->
     ie_q E <= a < ie_q E + 8 \/ ie_q E + 16 <= a < ie_q E + 20 \/ 4096 <= a < alloc_ceiling) ->
  (* the callee's journal from P's state to P2's, at the caller's window top (vrd_call_W(F)'s second journal), at the
     callee's budget WS1 (the kit's cut: the reader callees' posts are budgeted) *)
  ajournal_xwR (SK := SK) SEGS B prh_pst ARx R STKc (spZ (ie_regs E) + ie_e E) FP1
    (ip_ly P) (ip_S P) (ip_Hp P) (ip_W P) (ip_mem P) (ip_md P) []
    (ip_ly P2) (ip_S P2) (ip_Hp P2) (ip_W P2) (ip_mem P2) (ip_md P2) k1 WS1 ->
  (* the frame and the caller window off FP1 (vrd_call_W(F)'s agreement clause) *)
  (forall a, spZ (ie_regs E) - 144 <= a < spZ (ie_regs E) + ie_e E -> ~ inFP FP1 a ->
     aview SEGS (w_H (ip_W P2)) (ip_mem P2) a = aview SEGS (w_H (ip_W P)) (ip_mem P) a) ->
  spZ (ip_regs P2) = spZ (ip_regs P) ->
  (* 1 *) vrd_iframe E P2 /\
  (* 2 *) (forall a, spZ (ie_regs E) <= a < spZ (ie_regs E) + ie_e E -> ~ inFP (rd_fp (ie_q E) (ie_v E)) a ->
             aview SEGS (w_H (ip_W P2)) (ip_mem P2) a = aview SEGS (w_H (ie_W E)) (ie_mem E) a) /\
  (* 3 *) arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H (ip_W P2)) (ip_mem P2)) /\
  (* 4 *) (exists ch', achain (ip_ly P2) (aview SEGS (w_H (ip_W P2)) (ip_mem P2)) (spZ (ie_regs E) - 144) (ie_q E) ch' /\
             spine ch' = spine (ie_ch2 E)) /\
  (* 5 *) ((forall b, In b (ablocks B (ip_ly P) (ip_S P)) -> In b (ablocks B (ip_ly P2) (ip_S P2))) ->
           rd_keep SEGS (rdW (ip_W P) (ip_mem P)) (rdW (ip_W P2) (ip_mem P2))
             (fun a => ~ inFP FP1 a /\ (ie_v E <= a < ie_v E + 56 \/ rd_blk (ip_D P) a))).
Proof.
  intros CTX CTX0 CW E P P2 STKc FP1 k1 WS1 Himg Hs0c HEN HFR HJN HFP1 HJc HWIN Hsp2.
  pose proof asan_consts as (C1 & _ & _ & _ & C5).
  destruct (vc_bounds CTX CTX0 CW E Himg HEN) as (Bc & Be0 & Bse & Bq0 & Bq24 & Bv4 & Bv56 & _).
  pose proof HJN as (HJ & Hwin & Hfz & Hfk & Haro & HBM & Hch).
  pose proof HJ as (HAR & HlyE & _).
  pose proof HJc as (HAR2 & Hlyc & _ & _ & _ & _ & _ & _ & Habove & Hblk & Himgc & Hfrc & _).
  (* FP1 meets the stack only in the cursor cells *)
  assert (Hoff : forall a, alloc_ceiling <= a -> ~ inFP (rd_fp (ie_q E) (ie_v E)) a -> ~ inFP FP1 a).
  { intros a Ha Hn Hin. destruct (HFP1 a Hin) as [H|[H|H]]; [| |lia]; apply Hn.
    - exists (ie_q E, ie_q E + 8). split; [left; reflexivity | cbn [fst snd]; lia].
    - exists (ie_q E + 16, ie_q E + 20). split; [right; left; reflexivity | cbn [fst snd]; lia]. }
  (* image bytes are below the ceiling *)
  assert (Hlow : forall a, in_img SEGS a -> a < alloc_ceiling).
  { intros a Hi. pose proof (@pa_segs_low _ _ PAI a Hi) as Hl. unfold kLowMemEnd in Hl. lia. }
  (* the frame's bytes *)
  assert (Hfr : forall a, spZ (ie_regs E) - 144 <= a < spZ (ie_regs E) ->
            0 <= a < 2 ^ 64 /\ ~ in_img SEGS a /\
            aview SEGS (w_H (ip_W P2)) (ip_mem P2) a = aview SEGS (w_H (ip_W P)) (ip_mem P) a).
  { intros a Ha. split; [lia|]. split; [intros Hi; pose proof (Hlow a Hi); lia|].
    apply HWIN; [lia|]. apply Hoff; [lia|]. intros (r & Hr & Hlo). cbn [rd_fp In] in Hr.
    destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hlo; lia. }
  assert (HKfr : rd_keep SEGS (rdW (ip_W P) (ip_mem P)) (rdW (ip_W P2) (ip_mem P2))
                   (fun x => spZ (ie_regs E) - 144 <= x < spZ (ie_regs E)))
    by (apply vc_rd_keep; exact Hfr).
  (* FP1 does not hold address 0 *)
  assert (Hclosed : ~ YI16.sink_open_fp FP1).
  { intros (r & Hr & Hlo). destruct (HFP1 0 (ex_intro _ r (conj Hr Hlo))) as [H|[H|H]]; lia. }
  (* a byte of a block of P that P2 still has, off FP1 *)
  assert (Hblock : forall p n a, In (p, n) (ablocks B (ip_ly P) (ip_S P)) ->
            In (p, n) (ablocks B (ip_ly P2) (ip_S P2)) -> p <= a < p + req_size n -> ~ inFP FP1 a ->
            0 <= a < 2 ^ 64 /\ ~ in_img SEGS a /\
            aview SEGS (w_H (ip_W P2)) (ip_mem P2) a = aview SEGS (w_H (ip_W P)) (ip_mem P) a).
  { intros p n a Hin Hin2 Hr Hnf.
    destruct (alx_blocks SEGS B ARx LAWS _ _ _ _ _ _ _ _ HAR Hin) as (_ & H4 & Hc & _).
    split; [lia|]. split.
    - exact (proj2 (alx_client_img SEGS B ARx LAWS _ _ _ _ _ _ a HAR
                      (or_introl (ex_intro _ p (ex_intro _ n (conj Hin Hr)))))).
    - pose proof (Hblk p n (a - p) Hin Hin2 ltac:(lia)) as Hk.
      replace (p + (a - p)) with a in Hk by lia. exact (Hk Hnf). }
  split; [|split; [|split; [|split]]].
  - (* 1: the frame *)
    pose proof HFR as (Hf0 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 &
      F17 & Fpres).
    unfold vrd_iframe. cbv zeta.
    split; [rewrite Hsp2; exact Hf0|].
    repeat match goal with
    | |- val_mem _ _ _ _ _ /\ _ => split; [eapply val_mem_keep; [eassumption|];
                                     eapply rd_keep_mono; [exact HKfr | cbn; intros; lia]|]
    end.
    intros a Ha. destruct (Hfr a Ha) as (Hr & Hi & Ea). exact (vc_apresent _ _ _ _ a Hr Hi Ea (Fpres a Ha)).
  - (* 2: the caller window *)
    intros a Ha Hnf. rewrite (HWIN a ltac:(lia) (Hoff a ltac:(lia) Hnf)). exact (Hwin a Ha Hnf).
  - (* 3: the read-only view *)
    intros a Hro Hno Herr.
    assert (Hi : in_img SEGS a).
    { destruct Hro as [(s & Hs & _ & Hr) | Hr]; [exists s; split; [exact Hs | exact Hr] | exact (@pa_relro_img _ _ PAI a Hr)]. }
    rewrite (Himgc a Hi Hno Herr (fun Hp => H_pst_ro a Hp Hro) (fp_spares_closed FP1 a Hclosed)).
    exact (Haro a Hro Hno Herr).
  - (* 4: the chain, by IelemE's vrd_chain_keep_w at the callee's layout *)
    pose proof Hlyc as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
    apply (vrd_chain_keep_w B ARx SK HL LAWS CTX CTX0 CW E P (ip_W P2) (ip_mem P2) (ip_ly P2)
             Himg Hs0c HEN HFR HJN Etop).
    intros a Ha Hnf.
    destruct (Z_lt_le_dec a (spZ (ie_regs E) + ie_e E)) as [Hlt | Hge].
    + apply HWIN; [lia | apply Hoff; [lia | exact Hnf]].
    + apply Habove; lia.
  - (* 5: the node's bytes and P's blocks' bytes *)
    intros Hincl. apply vc_rd_keep. intros a (Hnf & [Hv | Hd]).
    + (* the node's place at entry (prhPv_node's prhReader_at), carried to P by rd_blocks_move *)
      pose proof HEN as (_ & _ & _ & _ & HRD & _).
      destruct HRD as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HNODE & _ & _ & _ & HLED & _).
      destruct HNODE as (_ & _ & _ & _ & HATv & _).
      pose proof HBM as (_ & HABP & HFRP & _).
      pose proof HlyE as (_ & _ & _ & _ & _ & EF & _).
      assert (Hold : forall x, In x (ablocks B (ie_ly E) (ie_S E)) -> In x (ablocks B (ip_ly P) (ip_S P)))
        by (intros x Hx; apply (Permutation_in _ (Permutation_sym HABP)); apply in_or_app; right; exact Hx).
      pose proof (@cf_head_nonneg cp) as Hh0.
      destruct HATv as [(a1 & k1' & Hin1 & Hlo & Hhi) | [(b & m & Hinb & _ & Hlo & Hhi) |
                       [(cid & pos & Hf & Hlo & Hhi) | (Hlo & Hhi)]]].
      * destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ a1 k1' _ _ HLED Hin1) as (Hk1 & Hab1 & _).
        apply (Hblock (a1 - cf_head) (k1' + cf_head) a (Hold _ Hab1) (Hincl _ (Hold _ Hab1))); [|exact Hnf].
        unfold req_size. destruct (Z.eqb_spec (k1' + cf_head) 0); lia.
      * apply (Hblock b m a (Hold _ Hinb) (Hincl _ (Hold _ Hinb))); [|exact Hnf].
        unfold req_size. destruct (Z.eqb_spec m 0); lia.
      * (* a fake frame at entry is a fake frame of P, at the same address *)
        assert (Hf' : In (cid, pos) (frames (ip_S P))) by (apply (Permutation_in _ (Permutation_sym HFRP)); exact Hf).
        assert (Hfa : frame_addr (ip_ly P) cid pos = frame_addr (ie_ly E) cid pos)
          by (unfold frame_addr; rewrite EF; reflexivity).
        split; [lia|]. split.
        -- assert (Hrng : frame_addr (ip_ly P) cid pos <= a < frame_addr (ip_ly P) cid pos + fs_frame_bytes cid)
             by (rewrite Hfa; lia).
           exact (proj2 (alx_client_img SEGS B ARx LAWS _ _ _ _ _ _ a HAR
                    (or_intror (or_introl (ex_intro _ cid (ex_intro _ pos (conj Hf' Hrng))))))).
        -- apply (Hfrc cid pos a Hf'); [left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite Hfa; lia | exact Hnf].
      * (* the window place: v lies below the ceiling *)
        lia.
    + (* a block of P's D: its allocator block is a block of P (rd_blocks_move) *)
      unfold rd_blk in Hd. apply Exists_exists in Hd as ([a0 k0] & Hb & Hx). unfold pj_holdsR in Hx. cbn [fst snd] in Hx.
      pose proof HBM as (_ & HABP & _).
      pose proof (@cf_head_nonneg cp) as Hh0.
      assert (Hab : In (a0 - cf_head, k0 + cf_head) (ablocks B (ip_ly P) (ip_S P))).
      { apply (Permutation_in _ (Permutation_sym HABP)). apply in_or_app. left. unfold prhReader_ab.
        exact (in_map (fun ak => (fst ak - cf_head, snd ak + cf_head)) (ip_D P) (a0, k0) Hb). }
      apply (Hblock _ _ a Hab (Hincl _ Hab)); [|exact Hnf].
      unfold req_size. destruct (Z.eqb_spec (k0 + cf_head) 0); lia.
Qed.

(* ==== THE CALL-STATE PREMISES OF A READER CALL (a Theorem Labs lane's split, 2026-10-29: the Ival walk writes it once; the key
   step's parse_string call at row 148 and the element step's parse_value call at row 231 cite it). A loop position P
   and the call's registers (sp = the loop's sp; s0 = q and ra as the jal set them are the caller's own facts):
   - prh_cw_ok / prh_cur_low (parse_string's text) and prh_cur_entry / prh_cw_entry at the call registers
     (parse_value's text), for both cursor functions, over P's reader view: on image A both keep s0 = q (pi_s0cur 0),
     so the two words are at q - 8 and q - 16. Each is parse_items' saved ra or s0 (vrd_iframe) when q is at the entry
     sp, else a caller-window word, unchanged since the entry (vrd_ijrn's window clause; rd_fp's cells are at and above
     q), where vrd_ient_ok's prh_cur_entry bounds the q - 16 word and its prh_cw_entry places the q - 8 word's trace;
   - the chain at the cursor at any sp at or below the call's: vrd_ijrn's chain (parse_string's chain premise at
     spZ regs - pi_frame F_parse_string, and parse_value's entry chain and the second case of its partitioned premise);
   - the stack facts: spZ regs + 16 <= q, q + 24 <= spZ regs + (e + 144), fwin at e + 144 (the callee's caller
     window [sp0 - 144, sp0 + e): presence from vrd_ijrn's journal window), fpre's arodata conjunct and
     spZ regs + 64 <= ly_stk_hi (fpre's afn_pre_x is vrd_call_W(F)'s own). All about P's view. ==== *)
Lemma vrd_reader_call_pre : forall CTX CTX0 CW E P (regs : bvmap 5 word),
  pi_frame F_parse_items = 144 -> pi_s0cur F_parse_items = Some 0 -> pi_s0cur F_parse_string = Some 0 ->
  vrd_ient_ok B ARx CTX CTX0 CW E -> vrd_iframe E P -> vrd_ijrn B ARx SK E P ->
  spZ regs = spZ (ie_regs E) - 144 ->
  (* s0 holds the cursor at the call (both call sites: vrd_iregs' s0 = q); the entry-cut case of prh_cur_entry's
     HC0 at the call state (PRH_Base.v, the kit's preview 2d523216ac5) *)
  getr regs 8 = w64 (ie_q E) ->
  (forall F, prh_cursor F ->
     prh_cw_ok B CW (ip_W P) (ip_mem P) F (ie_q E) /\ prh_cur_low (ip_W P) (ip_mem P) F (ie_q E)) /\
  (prh_cur_entry (ip_W P) (ip_mem P) regs (ie_q E) /\ prh_cw_entry B CW (ip_W P) (ip_mem P) regs (ie_q E)) /\
  (forall sp', sp' <= spZ regs ->
     exists ch', achain (ip_ly P) (aview SEGS (w_H (ip_W P)) (ip_mem P)) sp' (ie_q E) ch' /\
       spine ch' = spine (ie_ch2 E)) /\
  spZ regs + 16 <= ie_q E /\ ie_q E + 24 <= spZ regs + (ie_e E + 144) /\
  fwin (ip_ly P) (ip_W P) regs (ip_mem P) (ie_e E + 144) /\
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H (ip_W P)) (ip_mem P)) /\
  spZ regs + 64 <= ly_stk_hi (ip_ly P).
Proof.
  intros CTX CTX0 CW E P regs Himg Hs0i Hs0s HEN HFR HJN Hsp Hs08.
  destruct (vc_bounds CTX CTX0 CW E Himg HEN) as (Bc & Be0 & Bse & Bq0 & Bq24 & Bv4 & Bv56 & HSTK).
  pose proof HEN as ((HAFN & _ & Hhi0) & _ & _ & _ & HRD & _ & _ & _ & _ & _ & _ & HCUR & _).
  pose proof HEN as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & HCWE & _)).
  pose proof HAFN as (_ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (Hal16 & _).
  pose proof HRD as (_ & _ & _ & _ & Hpin0 & Hfwin0 & _).
  pose proof Hfwin0 as (_ & He16 & Hetop & _).
  pose proof Hpin0 as (_ & _ & _ & _ & Hq8 & _).
  pose proof HJN as (HJ & HWIN & _ & _ & Haro & _ & Hch).
  pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
  pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _ & Ehi & _).
  pose proof HFR as (_ & H8 & H16 & _).
  (* P's view agrees with the entry's on the caller window below q *)
  assert (Hagr : forall a, spZ (ie_regs E) <= a < ie_q E ->
            aview SEGS (w_H (ip_W P)) (ip_mem P) a = aview SEGS (w_H (ie_W E)) (ie_mem E) a).
  { intros a Ha. apply HWIN; [lia|]. intros (r & Hin & Hr). cbn [rd_fp In] in Hin.
    destruct Hin as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hr; lia. }
  assert (Hra : rdword (aview SEGS (w_H (ip_W P)) (ip_mem P)) (spZ (ie_regs E) - 8) = Some (raZ (ie_regs E))).
  { apply vrd_rdword_of_val_mem; [exact H8|].
    pose proof (bv_unsigned_in_range 64 (getr (ie_regs E) 1)) as Hb. change (bv_modulus 64) with (2 ^ 64) in Hb.
    exact Hb. }
  assert (Hs0 : rdword (aview SEGS (w_H (ip_W P)) (ip_mem P)) (spZ (ie_regs E) - 16) = Some (s0Z (ie_regs E))).
  { apply vrd_rdword_of_val_mem; [exact H16|].
    pose proof (bv_unsigned_in_range 64 (getr (ie_regs E) 8)) as Hb. change (bv_modulus 64) with (2 ^ 64) in Hb.
    exact Hb. }
  (* a word of P's view between q - 16 and q - 8 is the entry's prh_word_entry *)
  assert (Hwe : forall a w, ie_q E - 16 <= a <= ie_q E - 8 -> a mod 8 = 0 ->
            rdword (aview SEGS (w_H (ip_W P)) (ip_mem P)) a = Some w ->
            prh_word_entry (ie_W E) (ie_mem E) (ie_regs E) a w).
  { intros a w Ha Ha8 Hw. unfold prh_word_entry.
    destruct (Z.eqb_spec a (spZ (ie_regs E) - 8)) as [Ea | Na].
    - subst a. rewrite Hra in Hw. injection Hw as <-. reflexivity.
    - destruct (Z.eqb_spec a (spZ (ie_regs E) - 16)) as [Eb | Nb].
      + subst a. rewrite Hs0 in Hw. injection Hw as <-. reflexivity.
      + assert (Hge : spZ (ie_regs E) <= a) by lia.
        rewrite <- Hw. symmetry. apply rdword_ext. intros k Hk. apply Hagr. lia. }
  assert (Hs : forall F, prh_cursor F -> prh_s0 F (ie_q E) = ie_q E).
  { intros F [-> | ->]; unfold prh_s0; [rewrite Hs0s | rewrite Hs0i]; apply Z.add_0_r. }
  (* the q - 8 word of P's view is the entry's prh_word_entry there, whose trace prh_cw_entry places *)
  assert (Hcw : forall F, prh_cursor F -> prh_cw_ok B CW (ip_W P) (ip_mem P) F (ie_q E)).
  { intros F HF r w Hr Hw. rewrite (Hs F HF) in Hw. apply (HCWE F r w HF Hr). rewrite (Hs F HF).
    apply Hwe; [lia | | exact Hw]. lia. }
  assert (Hcur : forall F, prh_cursor F ->
            prh_cw_ok B CW (ip_W P) (ip_mem P) F (ie_q E) /\ prh_cur_low (ip_W P) (ip_mem P) F (ie_q E)).
  { intros F HF. pose proof (proj2 HCUR F HF) as Hlo. split; [exact (Hcw F HF)|]. unfold prh_cur_low.
    rewrite (Hs F HF) in Hlo |- *.
    intros w Hw. apply Hlo. apply Hwe; [lia | | exact Hw]. lia. }
  split; [exact Hcur|]. split.
  { split; [split|].
    { (* the Forall-over-chains conjunct (PRH_Base.v, kit 04388d628fb), by prh_cur_entry_cases at the call's own
         registers: case 2, s0 = q and the word at q - 16 is the entry's cut word (P's view agrees with the entry's
         prh_word_entry there, Hwe) *)
      apply (prh_cur_entry_cases (ip_W P) (ip_mem P) regs (ie_q E) ltac:(lia)).
      right. left. split.
      - unfold s0Z. rewrite Hs08. unfold w64. apply unsigned_lit_small. lia.
      - intros w Hw. pose proof (proj2 HCUR F_parse_items (or_intror eq_refl)) as Hlo.
        rewrite (Hs F_parse_items (or_intror eq_refl)) in Hlo. apply Hlo. apply Hwe; [lia | | exact Hw]. lia. }
    { intros F HF. destruct (Hcur F HF) as [_ Hlo]. unfold prh_cur_low in Hlo.
      unfold prh_word_entry. rewrite (Hs F HF) in Hlo |- *.
      rewrite (proj2 (Z.eqb_neq (ie_q E - 16) (spZ regs - 8)) ltac:(lia)).
      rewrite (proj2 (Z.eqb_neq (ie_q E - 16) (spZ regs - 16)) ltac:(lia)).
      exact Hlo. }
    (* prh_cw_entry at the call registers: q - 8 is above the call's two save slots, so it is P's view word *)
    intros F r w HF Hr Hw. unfold prh_word_entry in Hw. rewrite (Hs F HF) in Hw.
    rewrite (proj2 (Z.eqb_neq (ie_q E - 8) (spZ regs - 8)) ltac:(lia)) in Hw.
    rewrite (proj2 (Z.eqb_neq (ie_q E - 8) (spZ regs - 16)) ltac:(lia)) in Hw.
    apply (Hcw F HF r w Hr). rewrite (Hs F HF). exact Hw. }
  split.
  { intros sp' Hsp'. destruct Hch as (ch' & Hc & Hspn). exists ch'. split; [|exact Hspn].
    eapply achain_lower; [exact Hc | lia]. }
  split; [lia|]. split; [lia|]. split.
  { split; [lia|]. split; [lia|]. split; [rewrite Etop; lia|].
    intros a Ha. apply Hpres. lia. }
  split; [exact Haro|]. rewrite Ehi. lia.
Qed.

End K.

Print Assumptions vrd_call_keep.
Print Assumptions vrd_reader_call_pre.
