(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/S8aNumA.v, with its module paths and module names changed; 1213 of its 1267 lines of code are new or changed and 724 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/BTxString.v, with its module paths and module names changed; 108 of its 138 lines of code are new or changed and 1237 lines of the source are left out. *)
(* fuzz_preset, slice S5b, image A': parse_value's shared epilogue BOUND to the join state vrd_epi_a (lib/A/VrdNum.v)
   on a Theorem Labs lane's green value side at the kit's cut 7cdbb61b5fa0 (a working branch e942c5680fa7: VrdNum.v
   636d54d20156, VrdEpi.v 38bfc716a234). Lane PV-epilogue (worker a Theorem Labs lane, lane WalkAlive).

   rule 24: no function proved. rule 24: proves no function (kind: segment lemma).

   `vrd_epi_step`: an arm that reaches row 225 in vrd_epi_a, with its own answer RQ, meets tparse_value_specX's
   BUDGETED caller-window post (PRH_Base.fpostWFb at the text's budget YCbqGwild.wbudget CW 0; the text's own post is
   fpostWFbm, i.e. fpostWFb at Q := fQmn mem Q') at ANY post body Q, given that Q follows from RQ across the tail's
   writes and the frame's release (HQ). The text concludes SRr' segs RZ_cf, and fpostWFb is an after-free post (its
   journal's world conjunct at YA0nH.wle' segs YGcfRehidePost.RZ_cf): the epilogue runs at wle (VrdEpi.vrd_epi_holds)
   and is lifted once, its run by YA0nH.SRr_SRr' and its post's journal by vlift_aj below.
   THE JOIN STATE OVER R is lib/A/VrdNum.v's vrd_epi_aR: vrd_epi_a's body with its journal at a world relation R
   (ajournal_xwR R); vrd_epi_a is vrd_epi_aR at wle. An arm whose run crosses a free (the container arm, after
   parse_items) reaches row 225 at wle' segs RZ_cf; an arm at wle reaches it there by vrd_epi_a_wle'. vlift_aj /
   vlift_ajw lift a journal from wle to wle' segs RZ_cf (YCbqG.ajournal_xwR_mono at YA0nH.wle_wle'); they state every
   argument, so the entry ghost set Hp is read off the journal.
   THE BUDGET BRIDGE. vrd_epi_a carries the journal from parse_value's entry with the callees' wild budget WS
   (`exists WS, ajournal_xw .. WS /\ wbudget CW 0 WS`), while the epilogue walk VrdEpi.vrd_epi_holds is stated over
   the budget-free journal ajournal_x. The epilogue rows make no allocation, so the bridge is the engine's pair
   (lib/Reusable/YCbqGwild.v 0c63874858e4): ajournal_xw_rebase moves the entry state's depot to the join's (giving
   ajournal_x at set_depot (st_depot S) S0), vrd_epi_holds runs there (its premises read S0 only through frames,
   which set_depot keeps), and ajournal_xw_unbase0 folds the post's journal back to S0 at the same WS, with the
   journal's own wild-part inclusion (ajx_wild). The budget WS is the one vrd_epi_a names.
   Both implicit float states are PINNED: vrd_epi_a's and fpostWFb's {fx} is parse_value's ENTRY float state (the
   Section's fx), the join's is the explicit fx2.
   History: first bound on image A to an earlier join state (blob
   f1fc220d1536, budget-free post fpostWF).
   BY NAME: vrd_epi_a is read through lib/A/VrdNum.v's record vrd_epi_R (vrd_epi_R_of, then its vepi_* projections)
   and built through it (vrd_epi_aR_of_R); fpostWF through the explicit shape guard vfpw below (it states fpostWF's
   conjuncts as the definition has them, proof `exact H`), so a change of it fails at the guard; the journal through
   the engine's ajx_* projections. No numeral. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YGcfNames YCbqG YP0b YPsym YC4aP YGcfRoomPre YGcfRoomKeep YGcallSx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCbqGwild.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import
PRH_Base PRH_Reader PRH_FnReader PRH_Charge PRH_FnParse PRH_Img.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_prog PAImg_prog VrdPro VrdNum VrdEpi.
Import ListNotations.
Local Open Scope Z_scope.

Section c.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PIm : PrhImg} {RL : PrhRoomLive}.
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PI_prog_A).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
(* the laws of VrdEpi.v's Section, verbatim: the journal's (LAWS) and the release rule's (ASFX, FFLX, SFX:
   YGcallSx.v, discharged at ARcf by YGcallScf.v), and the flag byte's presence (FPRES: the first conjunct of
   YG0dcf.v AR_flag_law_cf, proved at ARcf by YG0scf.v AR_flag_law_ok_cf) *)
Context {HL : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx HL.
Hypothesis ASFX : forall ly S Hp W mem md mem' md' cid pos,
  ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  aview SEGS (w_H W) mem' (flag_addr ly cid pos) = Some 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> aowned B ly S a -> a <> flag_addr ly cid pos ->
     aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) ->
  (forall a, aview SEGS (w_H W) mem a <> None -> aview SEGS (w_H W) mem' a <> None) ->
  m_vmmaps md' = m_vmmaps md -> m_vm_lazy md' = m_vm_lazy md -> eager_used md' = eager_used md ->
  (forall a, in_band_rw a -> w_H W (w64 a) = true -> mem' (w64 a) = mem (w64 a)) ->
  ARx ly (stack_free_state cid pos S) Hp W mem' md'.
Hypothesis FFLX : forall ly S Hp (W : world SEGS) mem md cid pos,
  ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  aowned B ly S (flag_addr ly cid pos) /\ (app_addr (flag_addr ly cid pos) /\ ~ in_img SEGS (flag_addr ly cid pos)).
Hypothesis FPRES : forall ly S Hp (W : world SEGS) mem md cid pos,
  ARx ly S Hp W mem md -> In (cid, pos) (frames S) -> apresent (w_H W) mem (flag_addr ly cid pos).
Hypothesis SFX : forall ly S Hp W mem md cid pos, ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  exists l1 l2, frames S = l1 ++ (cid, pos) :: l2 /\ frames (stack_free_state cid pos S) = l1 ++ l2.

#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* fpostWF's shape, stated as lib/A/PRH_Base.v ef7c8ca98529 defines it *)
Lemma vfpw {STK d FP regs ly S Hp W mem md Q W' c'} :
  fpostWF (fx := fx) B ARx SK STK d FP regs ly S Hp W mem md Q W' c' ->
  exists (fx' : YK11.FPState) ly' S' Hp' regs' mem' md' k,
    c' = mkCfg (@YK11.mkst fx' regs' (YK11.getr regs 1) mem' (YK11.seg_rom SEGS)) md' /\
    frm_zero (@YK11.fp_csr fx') /\ fregs_kept_x fx fx' /\
    ajournal_x (SK := SK) SEGS B prh_pst ARx (STK + d) (spZ regs + d) FP ly S Hp W mem md [] ly' S' Hp' W' mem' md' k /\
    (forall a, spZ regs <= a < spZ regs + d -> ~ inFP FP a -> aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) /\
    aregs_preserved regs regs' /\ Q ly' S' Hp' W' regs' mem' md'.
Proof. intros H. exact H. Qed.

(* fpostWFR's shape (PRH_Base.v: the SHARED caller-window post over a world relation R), fpostWF's conjuncts with the
   journal at R *)
Lemma vfpwR {R STK d FP regs ly S Hp W mem md Q W' c'} :
  fpostWFR (fx := fx) B ARx SK R STK d FP regs ly S Hp W mem md Q W' c' ->
  exists (fx' : YK11.FPState) ly' S' Hp' regs' mem' md' k,
    c' = mkCfg (@YK11.mkst fx' regs' (YK11.getr regs 1) mem' (YK11.seg_rom SEGS)) md' /\
    frm_zero (@YK11.fp_csr fx') /\ fregs_kept_x fx fx' /\
    ajournal_xR (SK := SK) SEGS B prh_pst ARx R (STK + d) (spZ regs + d) FP ly S Hp W mem md [] ly' S' Hp' W' mem' md'
      k /\
    (forall a, spZ regs <= a < spZ regs + d -> ~ inFP FP a -> aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) /\
    aregs_preserved regs regs' /\ Q ly' S' Hp' W' regs' mem' md'.
Proof. intros H. exact H. Qed.

(* the journal lifts from wle to the after-free relation wle' segs RZ_cf. Every argument is stated, so a journal
   hypothesis fixes each of them, the entry ghost set Hp included *)
Lemma vlift_ajw {STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k WS} :
  ajournal_xw (SK := SK) SEGS B prh_pst ARx STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k WS ->
  ajournal_xwR (SK := SK) SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf) STK sp0 FP ly S Hp W mem md own
    ly' S' Hp' W' mem' md' k WS.
Proof.
exact (ajournal_xwR_mono SEGS B prh_pst ARx (@wle SEGS) (wle' SEGS YGcfRehidePost.RZ_cf)
  (wle_wle' SEGS YGcfRehidePost.RZ_cf) STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k WS).
Qed.
Lemma vlift_aj {STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k} :
  ajournal_x (SK := SK) SEGS B prh_pst ARx STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
  ajournal_xR (SK := SK) SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf) STK sp0 FP ly S Hp W mem md own
    ly' S' Hp' W' mem' md' k.
Proof. intros H. exact (vlift_ajw H). Qed.

(* a join reached at wle is one at wle' segs RZ_cf: the journal lifted, every other conjunct unchanged *)
Lemma vrd_epi_a_wle' {fx2 d CW e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos rv RQ W c} :
  vrd_epi_a (fx := fx) B ARx SK fx2 d CW e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos rv RQ W c ->
  vrd_epi_aR (fx := fx) B ARx SK (wle' SEGS YGcfRehidePost.RZ_cf) fx2 d CW e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos rv
    RQ W c.
Proof.
intros HD. unfold vrd_epi_a in HD. apply vrd_epi_R_of in HD. destruct HD as (regs & mem & md & ly & S & Hp & k & HR).
apply vrd_epi_aR_of_R with (regs := regs) (mem := mem) (md := md) (ly := ly) (S := S) (Hp := Hp) (k := k).
destruct (vepi_jrn HR) as (WS & HJ & HWB).
refine {| vepi_cfg := vepi_cfg HR; vepi_jrn := ?[jrn]; vepi_win := vepi_win HR; vepi_s0 := vepi_s0 HR;
  vepi_s2 := vepi_s2 HR; vepi_s10 := vepi_s10 HR; vepi_s8 := vepi_s8 HR; vepi_s5 := vepi_s5 HR; vepi_gp := vepi_gp HR;
  vepi_tp := vepi_tp HR; vepi_ra := vepi_ra HR; vepi_saved := vepi_saved HR; vepi_flag := vepi_flag HR;
  vepi_frm := vepi_frm HR; vepi_fregs := vepi_fregs HR; vepi_rq := ?[rq] |}.
[jrn]: { exists WS. split; [exact (vlift_ajw HJ) | exact HWB]. }
[rq]: exact (vepi_rq HR).
Qed.

Theorem vrd_epi_step :
  forall (fx2 : YK11.FPState) (d : nat) (CW : list (list Z)) (e q v : Z)
    (ly0 : alayout) (S0 : astate) (Hp0 : list Z) (W0 : world SEGS) (regs0 : bvmap 5 word)
    (mem0 : word -> option byte) (md0 : Model) (pos rv : Z)
    (RQ : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Prop)
    (Q : alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
    (W : world SEGS) (c : config),
  104 <= STK_parse_value d ->
  (forall (ly : alayout) (S : astate) (Hp : list Z) (mem : word -> option byte)
          (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model),
     RQ ly S Hp W mem ->
     getr regs' 10 = w64 rv -> aregs_preserved regs0 regs' ->
     frames (stack_free_state 0 pos S) = frames S0 ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ in_frames ly [(0, pos)] a -> a <> flag_addr ly 0 pos ->
        aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) ->
     Q ly (stack_free_state 0 pos S) Hp W regs' mem' md') ->
  vrd_epi_a (fx := fx) B ARx SK fx2 d CW e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos rv RQ W c ->
  SRr' SEGS YGcfRehidePost.RZ_cf W c
    (fpostWFb (fx := fx) B ARx SK (YCbqGwild.wbudget CW 0) (STK_parse_value d) e (rd_fp q v) regs0
       ly0 S0 Hp0 W0 mem0 md0 Q).
Proof.
intros fx2 d CW e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos rv RQ Q W c H104 HQ HD.
(* the join BY NAME: VrdNum's record vrd_epi_R at its witnesses (vrd_epi_R_of), read by its projections *)
unfold vrd_epi_a in HD. apply vrd_epi_R_of in HD. destruct HD as (regs & mem & md & ly & S & Hp & k & HR).
pose proof (vepi_cfg HR) as Ec. subst c.
destruct (vepi_jrn HR) as (WS & HJ & HWB).
pose proof (vepi_win HR) as HWIN. pose proof (vepi_s0 HR) as H8. pose proof (vepi_s2 HR) as H18.
pose proof (vepi_s10 HR) as H26. pose proof (vepi_s8 HR) as H24. pose proof (vepi_s5 HR) as H21.
pose proof (vepi_gp HR) as H3. pose proof (vepi_tp HR) as H4. pose proof (vepi_ra HR) as HRA.
pose proof (vepi_saved HR) as HSAV. pose proof (vepi_flag HR) as HFLG. pose proof (vepi_frm HR) as HFRM.
pose proof (vepi_fregs HR) as HFRK. pose proof (vepi_rq HR) as HRQ.
(* the journal's own wild-part inclusion, then the journal rebased to the join's depot (budget-free). The record
   gives the journal in its R form at wle (ajournal_xwR (@wle SEGS)), so the rebase is its R form there *)
pose proof (ajx_wild HJ) as HWild.
apply (YCbqGwild.ajournal_xw_rebaseR SEGS B prh_pst ARx) in HJ.
(* the epilogue at wle (VrdEpi.vrd_epi_holds), lifted once to the text's relation: the run by SRr_SRr', the post's
   journal by vlift_aj *)
apply (SRr_SRr' SEGS YGcfRehidePost.RZ_cf).
eapply SRr_mono.
- exact (vrd_epi_holds (fx := fx) B ARx SK LAWS ASFX FFLX FPRES SFX d fx2 ly0 (set_depot (st_depot S) S0) Hp0 W0
    regs0 mem0 md0 ly S Hp W regs mem md e q v pos rv k Q H104 HJ HWIN H8 H18 H26 H24 H21 H3 H4 HRA HSAV HFLG HFRM HFRK
    (fun regs' mem' md' H10 HAP HFR HMEM => HQ ly S Hp mem regs' mem' md' HRQ H10 HAP HFR HMEM)).
- intros W' c' _ HP.
  destruct (vfpw HP) as (fx' & ly' & S' & Hp' & regs' & mem' & md' & k' & Ec & HFZ & HFK & HJ' & HW' & HAP & HQ').
  exists fx', ly', S', Hp', regs', mem', md', k', WS.
  split; [exact Ec|]. split; [exact HFZ|]. split; [exact HFK|]. split; [exact HWB|].
  split; [eapply (YCbqGwild.ajournal_xw_unbase0R SEGS B prh_pst ARx); [exact (vlift_aj HJ') | exact HWild]|].
  split; [exact HW'|]. split; [exact HAP|]. exact HQ'.
Qed.

End c.

Print Assumptions vrd_epi_step.
Print Assumptions vrd_epi_a_wle'.
(* the wrong-image check (the join's pc names image A': PI_prog_A / A_prog_listing) *)
Set Printing Implicit. Unset Printing Notations.
Print vrd_epi_aR.
Unset Printing Implicit. Set Printing Notations.
