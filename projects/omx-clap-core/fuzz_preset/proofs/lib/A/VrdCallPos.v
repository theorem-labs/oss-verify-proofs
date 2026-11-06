(* fuzz_preset, slice S5b (a Theorem Labs lane): THE POSITION AFTER A CALL of parse_items' loop - vrd_pos_after_call, with its
   two helpers vc_fregs_trans / vc_iregs_pres. Written once by the Ival walk (a working branch e5220a09e8f, in
   VrdCallKeep.v) at the S3 walk's request; the parse_string call at row 148 (the S3 walk's VrdIKey.v) and the parse_value call
   at row 231 (the Ival walk's VrdIVal.v) cite it. MOVED here unchanged by the S3 walk (2026-10-29, a Theorem Labs lane's approval): it
   needs VrdLedgerStep.vl_blocks_move_app, VrdLedgerStep needs VrdIStep, and VrdIStep (IelemE) needs VrdCallKeep, so
   it cannot stay in VrdCallKeep.v.
   rule 24: no function proved
   rule 24: proves no function (kind: segment lemma). No walk and no callee: the callee is an abstract journal.
   WHAT IT GIVES. From the call-site position Pc and the later position P2 whose machine state the callee returned:
   vrd_iframe, vrd_iregs and vrd_ijrn at P2 (P2's views), and vrd_call_keep's byte keep from Pc's restricted view
   rdW (ip_W Pc) (ip_mem Pc) to P2's. The callee-specific parts stay with the caller (vrd_icur / vrd_inode at P2, the
   ledger and the model). The composed trace's held peak is a premise.
   SET: a working branch on a working branch 6372b90e841 (texts ee649e1b39d over the kit's preview
   walkkit-next 2d523216ac5 by path; engine set a Theorem Labs lane s1b 7792959a2abb by path; listing v4). A-only.
   Numerals: 144 / 56 / 20 / 16 / 8 (LENGTH, as VrdCallKeep.v), 224 / 512 (LENGTH: the reader's charge, PRH_FnParse.v),
   4096 (LENGTH: bound). No ADDRESS literal. *)
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
Img0 Listing_prog PAImg_prog PRH_Base PRH_Img PRH_Reader PRH_FnReader PRH_Charge PRH_FnParse VrdFrame VrdIElem VrdCallKeep VrdLedgerStep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1Ledger.
(* the re-hiding move's wle' (YA0nH) and preset's zone (YGcfRehidePost.RZ_cf) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
(* an import (through VrdLedgerStep -> VrdIStep) leaves Zify's euclidean-division flag off; set it on *)
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
Context {HL : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx HL.
Variable H_pst_ro : forall a, Exists (in_zr a) prh_pst -> ~ in_roP SEGS pa_relro_lo pa_relro_hi a.

(* ==== THE POSITION AFTER A CALL (the S3 walk's request: the parse_string call at row 148 and the Ival walk's parse_value call
   at row 231 share it; written once). From the call-site position Pc and the later position P2 whose machine state
   the callee returned: vrd_iframe, vrd_iregs and vrd_ijrn at P2, and vrd_call_keep's byte keep. The callee-specific
   parts stay with the caller: vrd_icur / vrd_inode at P2 (IelemE's vrd_icur_after_call / vrd_node_ra_after_call for
   the facts no journal keeps), the ledger and the model. The composed trace's held peak is a premise (it is the
   callee's grammar that bounds it).
   The kit's CUT (lane RBase, 7cdbb61b5fa0): DW -> CW; the callee's journal is at ITS budget WS1 (the reader callees post
   at wbudget CW 0, PRH_FnParse.v f0d92dcec7e9 / PRH_FnReader.v f1ae32e3b2cd) and the composed journal from the
   entry is at the caller's budget ie_CW E followed by WS1 (YCbqGwild.aj_call_xWFb's WS0 ++ WS1), which the callee's
   `wbudget CW 0 WS1` folds back to vrd_ijrn's budget ie_CW E (VrdIElem.vrd_budget_back).
   THE RE-HIDING MOVE: both journals are at wle' SEGS RZ_cf (the callees' texts post at wle', and vrd_ijrn is there);
   the fold-back is YCbqG.ajx_budgetR. ==== *)
Lemma vc_fregs_trans : forall (f1 f2 f3 : YK11.FPState),
  fregs_kept_x f1 f2 -> fregs_kept_x f2 f3 -> fregs_kept_x f1 f3.
Proof. intros f1 f2 f3 H1 H2 r Hr. rewrite (H2 r Hr). exact (H1 r Hr). Qed.

Lemma vc_iregs_pres : forall E P P', vrd_iregs B E P -> aregs_preserved (ip_regs P) (ip_regs P') -> vrd_iregs B E P'.
Proof.
  intros E P P' H HP.
  assert (K : forall r, acallee_saved r -> getr (ip_regs P') (Z_to_bv 5 r) = getr (ip_regs P) (Z_to_bv 5 r))
    by exact HP.
  destruct H as (G3 & G4 & G8 & G9 & G18 & G19 & G20 & G21 & G22 & G23 & G24 & G25 & G26 & G27).
  refine (conj (eq_trans (K 3 _) G3) (conj (eq_trans (K 4 _) G4) (conj (eq_trans (K 8 _) G8)
    (conj (eq_trans (K 9 _) G9) (conj (eq_trans (K 18 _) G18) (conj (eq_trans (K 19 _) G19)
    (conj (eq_trans (K 20 _) G20) (conj (eq_trans (K 21 _) G21) (conj (eq_trans (K 22 _) G22)
    (conj (eq_trans (K 23 _) G23) (conj (eq_trans (K 24 _) G24) (conj (eq_trans (K 25 _) G25)
    (conj (eq_trans (K 26 _) G26) (eq_trans (K 27 _) G27)))))))))))))); unfold acallee_saved; lia.
Qed.

Lemma vrd_pos_after_call : forall CTX CTX0 CW E Pc P2 STKc FP1 k1 WS1 D tr,
  pi_frame F_parse_items = 144 -> pi_s0cur F_parse_items = Some 0 ->
  vrd_ient_ok B ARx CTX CTX0 CW E -> vrd_iframe E Pc -> vrd_iregs B E Pc -> vrd_ijrn B ARx SK E Pc ->
  (* the callee's footprint, its journal from Pc's state (at its budget WS1), and vrd_call_W(F)'s agreement clause *)
  (forall a, inFP FP1 a ->
     ie_q E <= a < ie_q E + 8 \/ ie_q E + 16 <= a < ie_q E + 20 \/ 4096 <= a < alloc_ceiling) ->
  ajournal_xwR (SK := SK) SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf) STKc (spZ (ie_regs E) + ie_e E) FP1
    (ip_ly Pc) (ip_S Pc) (ip_Hp Pc) (ip_W Pc) (ip_mem Pc) (ip_md Pc) []
    (ip_ly P2) (ip_S P2) (ip_Hp P2) (ip_W P2) (ip_mem P2) (ip_md P2) k1 WS1 ->
  (forall a, spZ (ie_regs E) - 144 <= a < spZ (ie_regs E) + ie_e E -> ~ inFP FP1 a ->
     aview SEGS (w_H (ip_W P2)) (ip_mem P2) a = aview SEGS (w_H (ip_W Pc)) (ip_mem Pc) a) ->
  aregs_preserved (ip_regs Pc) (ip_regs P2) ->
  (* vrd_call_W(F)'s composed journal from the entry (the caller's budget, then the callee's), the callee's budget
     within CW (its post's wbudget CW 0), and the callee's float state *)
  ajournal_xwR (SK := SK) SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf) (STK_parse_items (ie_d E) + ie_e E)
    (spZ (ie_regs E) + ie_e E)
    (rd_fp (ie_q E) (ie_v E)) (ie_ly E) (ie_S E) (ie_Hp E) (ie_W E) (ie_mem E) (ie_md E) []
    (ip_ly P2) (ip_S P2) (ip_Hp P2) (ip_W P2) (ip_mem P2) (ip_md P2) (ip_k P2) (ie_CW E ++ WS1) ->
  YCbqGwild.wbudget CW 0 WS1 ->
  frm_zero (@YK11.fp_csr (ip_fx P2)) -> fregs_kept_x (ip_fx Pc) (ip_fx P2) ->
  (* the callee's new blocks and frames, and the trace and blocks of P2 *)
  (forall a k, In (a, k) D -> ~ In (a - cf_head, k + cf_head) (ablocks B (ip_ly Pc) (ip_S Pc))) ->
  Permutation (ablocks B (ip_ly P2) (ip_S P2)) (prhReader_ab D ++ ablocks B (ip_ly Pc) (ip_S Pc)) ->
  Permutation (frames (ip_S P2)) (frames (ip_S Pc)) ->
  ip_D P2 = ip_D Pc ++ D -> ip_tr P2 = ip_tr Pc ++ tr ->
  hpeakR (ip_tr Pc ++ tr) <= 224 * Z.of_nat (length (rest_atR (ie_tb E) (ie_text E) (ie_p E))) +
                             512 * Z.of_nat (PjGrammar.MAXD - ie_d E) ->
  vrd_iframe E P2 /\ vrd_iregs B E P2 /\ vrd_ijrn B ARx SK E P2 /\
  rd_keep SEGS (rdW (ip_W Pc) (ip_mem Pc)) (rdW (ip_W P2) (ip_mem P2))
    (fun a => ~ inFP FP1 a /\ (ie_v E <= a < ie_v E + 56 \/ rd_blk (ip_D Pc) a)).
Proof.
  intros CTX CTX0 CW E Pc P2 STKc FP1 k1 WS1 D tr Himg Hs0c HEN HFR HRG HJN HFP1 HJ1 HWIN HPR HJ2 HWB HFZ2 HFK2
    HBn HBp HBf ED ET HHP.
  assert (HCW : ie_CW E = CW)
    by (destruct HEN as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (HCW & _)); exact HCW).
  assert (Hbk : incl (ie_CW E ++ WS1) (ie_CW E)) by (rewrite HCW; exact (vrd_budget_back CW WS1 HWB)).
  apply (fun HJ => ajx_budgetR (ie_CW E) HJ (wild_incl_mono _ _ _ _ Hbk (ajxR_wild HJ))) in HJ2.
  assert (Hincl : forall b, In b (ablocks B (ip_ly Pc) (ip_S Pc)) -> In b (ablocks B (ip_ly P2) (ip_S P2)))
    by (intros b Hb; apply (Permutation_in _ (Permutation_sym HBp)); apply in_or_app; right; exact Hb).
  assert (HSP : spZ (ip_regs P2) = spZ (ip_regs Pc))
    by (unfold spZ; exact (f_equal bv_unsigned (HPR 2 ltac:(unfold acallee_saved; lia)))).
  destruct (vrd_call_keep B ARx SK LAWS H_pst_ro CTX CTX0 CW E Pc P2 STKc FP1 k1 WS1 Himg Hs0c HEN HFR HJN HFP1 HJ1
              HWIN HSP)
    as (HFR2 & HW2 & HARO2 & HCH2 & HK2).
  pose proof HJN as (_ & _ & _ & HFK & _ & HBM & _).
  split; [exact HFR2|]. split; [exact (vc_iregs_pres E Pc P2 HRG HPR)|].
  split; [|exact (HK2 Hincl)].
  split; [exact HJ2|]. split; [exact HW2|]. split; [exact HFZ2|]. split; [exact (vc_fregs_trans _ _ _ HFK HFK2)|].
  split; [exact HARO2|]. split; [|exact HCH2].
  rewrite ED, ET. apply (vl_blocks_move_app B _ _ (ip_ly Pc) (ip_S Pc)); assumption.
Qed.


(* ==== THE POST-IMPLICATION CONJUNCTS ACROSS A CALL OF THE LOOP (lane A2Step, kit reader text PRH_FnParse.v blob
   94232293d483 / PRH_FnReader.v fb7b12dfa169). One home for what the key path's parse_string call (VrdIKey.v) and the
   element step's parse_value call (VrdIVal.v) both compose: the position transfer, the live requests and the OUTCOME
   of VrdIElem.v's boundaries, by name. Each is VERBATIM the inline conjunct of vrd_imodel / vrd_iexit_a (so a
   destructed conjunct is the definition by delta): vc_xfer S0 S1 t is the transfer from S0 to S1 over rd_hevs t,
   vc_live S0 S1 t the live-request move, vc_outc E P the exit's OUTCOME clause at P. ==== *)
Definition vc_xfer (S0 S1 : astate) (t : list PjGrammar.ev) : Prop :=
  forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
    (H0 : list Z) (hist : list YG00.chunk),
    PresetRoomPos.iface_room_pos sm x os i H0 hist S0 ->
    PRH_Base.prh_run_at sm x os i (PresetReqAt.rd_hevs t) ->
    exists hist', PresetRoomPos.iface_room_pos sm x os (i + length (PresetReqAt.rd_hevs t))%nat H0 hist' S1.

Definition vc_live (S0 S1 : astate) (t : list PjGrammar.ev) : Prop :=
  Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S1))
    (PresetReqAt.hlive_from (PresetRoom.rs_live (YGcfRoom.room_of_cf S0)) (PresetReqAt.rd_hevs t)).

Definition vc_outc (E : vrd_ient) (P : vrd_ipos) : Prop :=
  forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
    (H0 : list Z) (hist : list YG00.chunk),
    PresetRoomPos.iface_room_pos sm x os i H0 hist (ie_S E) ->
    PRH_Base.prh_run_at sm x os i
      (PresetReqAt.rd_hevs (prhPi_gtrace (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E)))) ->
    PRH_Base.prh_cons_from sm x os i
      (length (PresetReqAt.rd_hevs (prhPi_gtrace (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E))))) ->
    (ie_fail E < ie_cnt E \/
     ie_cnt E + Z.of_nat (PjGrammar.calls (prhPi_gtrace (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E))))
       <= ie_fail E) ->
    ip_ran P = ie_ran E /\
    fst (PjGrammar.jr_items ReaderRes.jr_strtod (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E)) []) =
      fst (PjGrammar.jr_items ReaderRes.jr_strtod (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E))
             (ip_ok P)) /\
    exists hist', PresetRoomPos.iface_room_pos sm x os
      (i + length (PresetReqAt.rd_hevs (prhPi_gtrace (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E)))))%nat
      H0 hist' (ip_S P).

(* the transfer and the live move compose over a callee's events (VrdIElem.vrd_xfer_app / vrd_live_app) *)
Lemma vc_xfer_app : forall S1 S2 S3 t1 t2, vc_xfer S1 S2 t1 -> vc_xfer S2 S3 t2 -> vc_xfer S1 S3 (t1 ++ t2).
Proof. intros S1 S2 S3 t1 t2 H1 H2. exact (vrd_xfer_app S1 S2 S3 t1 t2 H1 H2). Qed.

Lemma vc_live_app : forall S1 S2 S3 t1 t2, vc_live S1 S2 t1 -> vc_live S2 S3 t2 -> vc_live S1 S3 (t1 ++ t2).
Proof. intros S1 S2 S3 t1 t2 H1 H2. exact (vrd_live_app S1 S2 S3 t1 t2 H1 H2). Qed.

(* a step that makes no event moves neither *)
Lemma vc_xfer_nil_r : forall S1 S2 t, vc_xfer S1 S2 t -> vc_xfer S1 S2 (t ++ []).
Proof. intros S1 S2 t H. rewrite app_nil_r. exact H. Qed.

(* THE CALL'S ALL-GRANTED TRACE AT A POSITION: the trace so far, then the continuation's granted trace (the model's
   factorisation at okr = [] over the granted prefix, PjGrammar.agrees_jr_items) *)
Lemma vc_gt_split : forall E P, vrd_imodel E P ->
  prhPi_gtrace (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E)) = ip_tr P ++ snd (fst (ip_cont P [])).
Proof.
  intros E P (Hok & Hrun & _).
  set (X := rest_atR (ie_tb E) (ie_text E) (ie_p E)).
  pose proof (PjGrammar.agrees_jr_items prh_jr_strtod (ie_d E) (ie_o E) X (ip_ok P)) as (HA & _).
  assert (HE := HA (fun k _ => eq_trans (f_equal (fun l => nth k l true) Hok) (vrd_nth_rep_true _ k))).
  pose proof (Hrun []) as H0. rewrite app_nil_r in H0. fold X in H0. rewrite H0 in HE.
  apply (f_equal (fun t => snd (fst t))) in HE. cbn [fst snd] in HE.
  unfold prhPi_gtrace. fold X. rewrite <- HE. reflexivity.
Qed.

(* a trace under any outcome list makes at most the calls of the all-granted one (PjGrammar.agrees: the run follows
   the granted one up to its first refusal, which ends it with one EFail) *)
Lemma vc_calls_le_granted : forall (A : Type) (m : PjGrammar.M A) ok, PjGrammar.agrees m ->
  (PjGrammar.calls (snd (fst (m ok))) <= PjGrammar.calls (snd (fst (m []))))%nat.
Proof.
  intros A m ok HA. destruct (PjGrammar.ok_upto_dec ok (PjGrammar.calls (snd (fst (m []))))) as [Hu | (j & Hj & Hf & Hu)].
  - rewrite (proj1 (HA ok) Hu). cbn [fst snd]. lia.
  - destruct (proj2 (HA ok) j Hj Hf Hu) as (P0 & E0 & rest & Hm & Hg & Hc & Hic).
    rewrite Hm. cbn [fst snd]. rewrite Hg, !PjGrammar.calls_app. cbn [PjGrammar.calls PjGrammar.is_call].
    rewrite Hic. lia.
Qed.

(* THE OUTCOME ON A GRANTED PREFIX (VrdIElem.vrd_outcome_granted, in the named form) *)
Lemma vc_outc_granted : forall E P r okr,
  ip_ok P = repeat true (PjGrammar.calls (ip_tr P)) ->
  PjGrammar.jr_items prh_jr_strtod (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E)) (ip_ok P) =
    (r, ip_tr P, okr) ->
  rd_ledger_move (ie_Lam E) (ie_peak E) (ie_cnt E) (ie_fail E) (ie_ran E) (ie_most E) (ip_ok P)
    (prhPi_gtrace (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E))) (ip_tr P)
    (ip_D P) (ip_Lam P) (ip_peak P) (ip_cnt P) (ip_fail P) (ip_ran P) ->
  vc_xfer (ie_S E) (ip_S P) (ip_tr P) ->
  vc_outc E P.
Proof.
  intros E P r okr Hok Hans HLM HXF. unfold vc_outc. unfold vc_xfer in HXF.
  eapply vrd_outcome_granted; [exact Hok | exact Hans | exact HLM | exact HXF].
Qed.

(* THE OUTCOME AT A CALLEE'S REFUSED ARM: a run of the call's all-granted events (the trace so far tr, the callee's
   granted events Eg, the rest), all consumer events, reaches the callee's entry at the position tr gives
   (PRH_Base.prh_run_at_app_iff / prh_cons_from_app_iff), where the callee's exclusion refutes it *)
Lemma vc_outc_refused : forall E P (S1 : astate) (tr : list PjGrammar.ev) (Eg Er : list PresetReqAt.hev),
  PresetReqAt.rd_hevs (prhPi_gtrace (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E))) =
    PresetReqAt.rd_hevs tr ++ Eg ++ Er ->
  vc_xfer (ie_S E) S1 tr ->
  (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
     (H0 : list Z) (hist : list YG00.chunk),
     PresetRoomPos.iface_room_pos sm x os i H0 hist S1 ->
     PRH_Base.prh_run_at sm x os i Eg -> PRH_Base.prh_cons_from sm x os i (length Eg) -> False) ->
  vc_outc E P.
Proof.
  intros E P S1 tr Eg Er HG HXF HEX sm x os i H0 hist HP HR HC. exfalso.
  rewrite HG in HR, HC. rewrite !length_app in HC.
  apply PRH_Base.prh_run_at_app_iff in HR as [HR1 HR2].
  apply PRH_Base.prh_run_at_app_iff in HR2 as [HR2 _].
  apply PRH_Base.prh_cons_from_app_iff in HC as [_ HC].
  apply PRH_Base.prh_cons_from_app_iff in HC as [HC _].
  destruct (HXF sm x os i H0 hist HP HR1) as (h1 & Hh1).
  exact (HEX sm x os _ H0 h1 Hh1 HR2 HC).
Qed.

(* THE OUTCOME AT A CHOSEN FAILURE: the failure index is the counter at a call of the granted run, after a granted
   prefix of k calls, with more granted calls to come; the clause's counter premise refutes it *)
Lemma vc_outc_chosen : forall E P (k : nat),
  ie_fail E = ie_cnt E + Z.of_nat k ->
  (k < PjGrammar.calls (prhPi_gtrace (ie_d E) (ie_o E) (rest_atR (ie_tb E) (ie_text E) (ie_p E))))%nat ->
  vc_outc E P.
Proof. intros E P k Hf Hk sm x os i H0 hist _ _ _ [Hc | Hc]; exfalso; lia. Qed.

(* a callee's ledger move stated over ITS granted trace gt holds over any extension gt ++ rest of it (the refusal peak
   reads only the first calls tr entries of the granted helds, and the run makes at most gt's calls) *)
Lemma vc_lm_gt_ext : forall Lam peak cnt fail ran most ok gt rest tr D Lam' peak' cnt' fail' ran',
  (PjGrammar.calls tr <= PjGrammar.calls gt)%nat ->
  rd_ledger_move Lam peak cnt fail ran most ok gt tr D Lam' peak' cnt' fail' ran' ->
  rd_ledger_move Lam peak cnt fail ran most ok (gt ++ rest) tr D Lam' peak' cnt' fail' ran'.
Proof.
  intros Lam peak cnt fail ran most ok gt rest tr D Lam' peak' cnt' fail' ran' Hk (O & C & F & Pp & Q & N & K).
  refine (conj O (conj C (conj F (conj Pp (conj Q (conj N _)))))).
  rewrite K, vl_ev_helds_app, map_app, vl_refused_peak_app_r; [reflexivity|].
  rewrite length_map, vl_ev_helds_length. exact Hk.
Qed.

End K.

Print Assumptions vrd_pos_after_call.
