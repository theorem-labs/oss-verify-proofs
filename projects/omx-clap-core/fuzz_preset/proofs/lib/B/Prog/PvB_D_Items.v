(* fuzz_preset image B' (asan-ubsan, #102), parse_value 0x8637c, segment D (the dispatch): the
   CONTAINER ARMS' packaging lemma. The first byte after the white space is '{' (123, o = true) or '[' (91, o = false);
   the machine calls parse_items (q, v, o) and returns its result. pvD_Qm_items turns parse_items' post (the
   tparse_items_specX of the batch kit, a working branch 8ba304fe2f93 lib/A/PRH_FnParse.v, its
   post body taken verbatim as a hypothesis at the call state: the live list and the run position moved by rd_hevs
   tr, the outcome over parse_items' grant-all trace, the ledger move with g_most and the refused peak, the free-order
   tie against prhPi_frees, the capacity words) and the reader state at the call (pv_reader0, its room keep from
   entry) into pv_Qm, the memory part of parse_value's post (lib/B/Prog/PvB_Defs.v pv_Qm): at the opener jr_value IS
   jr_items (pvi_model), so the grant-all traces agree (prhPv_gtrace = prhPi_gtrace), the outcome is parse_items'
   (PvB_Defs.pv_outc_call), and the model frees agree (PvB_Frees.pvf_frees_cont).
   pvi_counts gives the callee's two live-count premises from pv_pre's (the granted runs agree the same way).
   State-free: no machine code is walked here. The model side is PvB_Model.pvm_unfold / pvm_skip_rest / pvm_hpeak.
   pvi_Qm_ext carries pv_Qm to a pointwise-equal memory (the exit run after the call changes no byte), by the tree's
   frame lemmas (PRW_PjExt.pj_nodeR_frame, PvB_X_Tree.pjx_fd_frame / pjx_in_ok_frame / pjx_in_after_frame,
   PRH_PjOrder.pj_foR_frame, PvB_Frees.pvf_ncap_ext).
   Proves no function (kind: segment lemma).
   Numerals: 123 / 91 the opener bytes (WORD), 33 the depth bound of the refused cursor (PRH_FnParse), 224 / 512 the
   bound constants (LENGTH, PjGrammar vspec), 2 ^ 64 the register width. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG YP0b YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnReader PRH_Charge PRH_FnParse.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import PRH_ImgB Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjGrammar PjRoundTrip PjTree.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require PRW_PjExt.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PvB_Defs PvB_Model.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require PvB_X_Tree PvB_Frees.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_PjOrder.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos PresetReqAt PresetRun PresetRoom
  PresetLiveBounds PresetHullBudget.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoom YGcfRoomLive YGcfSecsStep.
Import ListNotations.
Local Open Scope Z_scope.

(* ---- pure: the container arms of the model ---- *)
Lemma pvi_model : forall sm d x (o : bool) y ok, PjGrammar.skip x = (if o then 123 else 91) :: y ->
  PjGrammar.jr_value sm d x ok = PjGrammar.jr_items sm d o ((if o then 123 else 91) :: y) ok.
Proof. intros sm d x o y ok Hs. rewrite pvm_unfold, Hs. destruct o; reflexivity. Qed.

(* ---- the result code: two values in [-1, 0] with the same 64-bit word are equal ---- *)
Lemma pvi_code : forall code c, -1 <= code <= 0 -> -1 <= c <= 0 -> Z_to_bv 64 code = Z_to_bv 64 c -> code = c.
Proof.
intros code c H1 H2 E.
assert (Hcode : code = -1 \/ code = 0) by lia. assert (Hc : c = -1 \/ c = 0) by lia.
destruct Hcode as [->| ->], Hc as [->| ->]; try reflexivity;
  apply (f_equal bv_unsigned) in E; vm_compute in E; discriminate E.
Qed.

(* ---- the refused cursor: a depth lower bound weakens ---- *)
Lemma pvi_after_weak : forall segs m q text len lo lo' hi, lo' <= lo ->
  pj_in_afterR segs m q text len lo hi -> pj_in_afterR segs m q text len lo' hi.
Proof.
intros segs m q text len lo lo' hi Hl (p' & d' & Hp & Hd & R).
exists p', d'. split; [exact Hp|]. split; [lia|exact R].
Qed.

(* split a right-nested conjunction into its conjuncts, so a cut's conjunct is found by its statement, not its place *)
Local Ltac pvi_split H :=
  lazymatch type of H with
  | _ /\ _ => let H1 := fresh "Hc" in destruct H as [H1 H]; pvi_split H
  | _ => idtac
  end.

#[local] Instance PIB : PrhImg := prh_img_B.
Section c. Context {fx0 : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
Context {PA : PAImg B_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.

(* parse_items' two live-count premises at a call state Sc the room keep from entry reaches: pv_pre's over
   parse_value's granted run, which at the opener IS parse_items' granted run (pvi_model at ok = []) *)
Lemma pvi_counts : forall en (o : bool) y Sc, pv_pre B ARx en ->
  PjGrammar.skip (pe_rest en) = (if o then 123 else 91) :: y -> rp_keep (pe_S en) Sc ->
  Z.of_nat (PresetRun.pkR YGcfRoomLive.rl_sec_req (PresetRoom.rs_live (YGcfRoom.room_of_cf Sc))
    (PresetReqAt.rd_hevs (prhPi_gtrace (pe_d en) o ((if o then 123 else 91) :: y))))
    <= PresetLiveBounds.LSEC + PresetLiveBounds.DRV /\
  Z.of_nat (PresetRun.pkR (PresetRoom.in_cls YG00.kBatchClass) (PresetRoom.rs_live (YGcfRoom.room_of_cf Sc))
    (PresetReqAt.rd_hevs (prhPi_gtrace (pe_d en) o ((if o then 123 else 91) :: y))))
    <= PresetLiveBounds.L24 + PresetLiveBounds.DRV.
Proof.
intros en o y Sc Hpre Hsk HK.
assert (E : pe_gt en = prhPi_gtrace (pe_d en) o ((if o then 123 else 91) :: y)).
{ unfold pe_gt, prhPv_gtrace, prhPi_gtrace. rewrite (pvi_model prh_jr_strtod (pe_d en) (pe_rest en) o y [] Hsk).
  reflexivity. }
unfold pv_pre in Hpre. destruct Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HS & H24 & _ & _).
rewrite E in HS, H24.
split; rewrite (rp_keep_pkR (pe_S en) Sc _ _ HK); assumption.
Qed.

(* THE CONTAINER ARMS: parse_items' post at the call (lyc, Sc, pe_Hp en, Wc, memc; q, v, the cursor p1 at the opener,
   the entry's ledger), with the result code in a0, gives pv_Qm. The post is the kit's tpiP_Q (lib/A/PRH_FnParse.v, the post
   of tparse_items_specX), read through its record tpiP_R: its hull use is the value's from the entry (pv_reader0's
   secs_same), its outcome of an injected reading the value's (the runs agree at the opener, pvi_model) *)
Lemma pvD_Qm_items : forall (en : PvEnt) (pos p1 code : Z) (o : bool) (y : list Z) (lyc : alayout) (Sc : astate)
    (Wc : world SEGS) (memc : word -> option byte) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world SEGS)
    (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model),
  pv_pre B ARx en ->
  p1 = pe_text en + pe_len en - Z.of_nat (length (PjGrammar.skip (pe_rest en))) ->
  PjGrammar.skip (pe_rest en) = (if o then 123 else 91) :: y ->
  pv_reader0 B en pos p1 lyc Sc Wc memc ->
  (* parse_items' post Q at d := pe_d en, the call state (lyc, Sc), the entry's ledger and its statics most / own; its
     events are parse_value's (jr_value at the opener IS jr_items, pvi_model: same ok, same trace) *)
  tpiP_Q B (pe_d en) lyc Sc (pe_q en) (pe_text en) (pe_len en) p1 (pe_tb en) (pe_v en) o (pe_Lam en) (pe_peak en)
    (pe_cnt en) (pe_fail en) (pe_ran en) (pe_most en) (pe_own en) ly' S' Hp' W' regs' mem' md' ->
  getr regs' 10 = w64 code ->
  (* ADDED: w64 code determines code only up to 2 ^ 64; the walk takes code := 0 or -1 per parse_items' arm *)
  -1 <= code <= 0 ->
  pv_Qm B en (fun S2 => Permutation (frames S2) ((0, pos) :: frames (pe_S en))) code ly' S' Hp' W' mem'.
Proof.
intros en pos p1 code o y lyc Sc Wc memc ly' S' Hp' W' regs' mem' md' Hpre Hp1 Hsk Hr0 HPI Hc Hcb.
unfold pv_pre in Hpre.
assert (Hrd : rd_pre (fx := fx0) B (pe_STK en) (pe_ly en) (pe_S en) (pe_Hp en) (pe_W en) (pe_regs en)
    (pe_mem en) (pe_Lam en) (pe_peak en) (pe_cnt en) (pe_fail en) (pe_ran en) (pe_most en) (pe_own en) (pe_e en)
    (pe_q en) (pe_text en)
    (pe_len en) (pe_p en) (pe_d en) (pe_tb en) (pe_v en)) by (clear - Hpre; pvi_split Hpre; assumption).
clear Hpre.
unfold rd_pre in Hrd.
assert (Hin0 : pj_in_okR SEGS (mrestrict (w_H (pe_W en)) (pe_mem en)) (pe_q en) (pe_text en) (pe_len en) (pe_p en)
    (Z.of_nat (pe_d en)) (pe_tb en)) by (clear - Hrd; pvi_split Hrd; assumption).
clear Hrd.
destruct Hin0 as (_ & _ & _ & _ & _ & _ & _ & Hpr & Hlen & _).
unfold pv_reader0 in Hr0.
assert (Hfr0 : frames Sc = (0, pos) :: frames (pe_S en)) by (clear - Hr0; pvi_split Hr0; assumption).
assert (Hab0 : ablocks B lyc Sc = ablocks B (pe_ly en) (pe_S en)) by (clear - Hr0; pvi_split Hr0; assumption).
assert (Hbb0 : blocks_bytes Sc = blocks_bytes (pe_S en)) by (clear - Hr0; pvi_split Hr0; assumption).
(* the room keep from entry to the call state (pv_reader0's rp_keep) and the hull meters kept (its secs_same) *)
assert (HK0 : rp_keep (pe_S en) Sc) by (clear - Hr0; pvi_split Hr0; assumption).
assert (HSEC0 : YGcfSecsStep.secs_same (pe_S en) Sc) by (clear - Hr0; pvi_split Hr0; assumption).
clear Hr0.
(* the cursor at the opener *)
pose proof (pvm_skip_rest (pe_tb en) (pe_text en) (pe_len en) (pe_p en) Hlen Hpr) as [Hrest1 _].
change (rest_atR (pe_tb en) (pe_text en) (pe_p en)) with (pe_rest en) in Hrest1.
rewrite <- Hp1 in Hrest1.
pose proof (PjGrammar.skip_len (pe_rest en)) as Hsl.
assert (Hlen1 : (length (rest_atR (pe_tb en) (pe_text en) p1) <= length (pe_rest en))%nat)
  by (rewrite Hrest1; exact Hsl).
apply tpiP_R_of in HPI.
destruct HPI as (ok & res & tr & okr & D & Lam' & peak' & cnt' & fail' & ran' & HR).
pose proof (tpiP_run HR) as Hj. pose proof (tpiP_ledger HR) as Hled. pose proof (tpiP_room HR) as Hroom.
pose proof (tpiP_hull HR) as Hhull. pose proof (tpiP_live HR) as HL. pose proof (tpiP_pos HR) as HP.
pose proof (tpiP_outcome HR) as Hout. pose proof (tpiP_injected HR) as Hinj.
pose proof (tpiP_ledger_move HR) as Hmove. pose proof (tpiP_blocks_move HR) as Hbm.
pose proof (tpiP_bytes HR) as Hbb. pose proof (tpiP_lsum HR) as Hls. pose proof (tpiP_arm HR) as Hres.
clear HR.
destruct Hbm as (Hfresh & Hperm & Hfrm & _).
(* the model: parse_value's container arm is parse_items at the opener *)
assert (Hrest : rest_atR (pe_tb en) (pe_text en) p1 = (if o then 123 else 91) :: y) by (rewrite Hrest1; exact Hsk).
assert (Hjv : PjGrammar.jr_value prh_jr_strtod (pe_d en) (pe_rest en) ok = (res, tr, okr)).
{ rewrite (pvi_model prh_jr_strtod (pe_d en) (pe_rest en) o y ok Hsk), <- Hrest. exact Hj. }
(* the grant-all runs agree (pvi_model at ok = []) *)
assert (Egt : pe_gt en = prhPi_gtrace (pe_d en) o (rest_atR (pe_tb en) (pe_text en) p1)).
{ unfold pe_gt, prhPv_gtrace, prhPi_gtrace. rewrite (pvi_model prh_jr_strtod (pe_d en) (pe_rest en) o y [] Hsk), Hrest.
  reflexivity. }
assert (Ej0 : fst (PjGrammar.jr_value prh_jr_strtod (pe_d en) (pe_rest en) []) =
              fst (PjGrammar.jr_items prh_jr_strtod (pe_d en) o (rest_atR (pe_tb en) (pe_text en) p1) [])).
{ rewrite (pvi_model prh_jr_strtod (pe_d en) (pe_rest en) o y [] Hsk), Hrest. reflexivity. }
(* the model frees agree (PvB_Frees.pvf_frees_cont) *)
assert (Efr : prhPi_frees (pe_d en) o (rest_atR (pe_tb en) (pe_text en) p1) ok = prhPv_frees (pe_d en) (pe_rest en) ok).
{ rewrite Hrest. symmetry. exact (PvB_Frees.pvf_frees_cont (pe_d en) (pe_rest en) ok o y Hsk). }
unfold pv_Qm.
exists ok, res, tr, okr, D, Lam', peak', cnt', fail', ran'.
split; [exact Hjv|]. split; [exact Hled|]. split; [exact Hroom|].
(* the hull use from the entry: the meters kept to the call state, then parse_items' use over the value's events *)
split.
{ rewrite Egt. exact (PresetHullBudget.hull_used_app (pe_S en) Sc S' [] _
    (PresetHullBudget.hull_used_same (pe_S en) Sc [] HSEC0) Hhull). }
split; [exact (rp_call tr (PresetReqAt.rd_hevs tr) (pe_S en) Sc S' S' eq_refl HK0 HL HP (rp_keep_refl S'))|].
split.
{ apply (pv_outc_call en res tr ran' Sc S' S'
    (PresetReqAt.rd_hevs (prhPi_gtrace (pe_d en) o (rest_atR (pe_tb en) (pe_text en) p1))));
    [rewrite Egt; reflexivity | exact HK0 | | exact (rp_keep_refl S')].
  intros sm x os i H0 hist P R C F. rewrite Egt in F.
  destruct (Hout sm x os i H0 hist P R C F) as (E1 & E2 & HP2).
  split; [exact E1|]. split; [rewrite Ej0; exact E2|]. exact HP2. }
(* the outcome of an injected reading: parse_items' at the call state (the keep carries the position), its model run
   being parse_value's at the opener (pvi_model at the model's grant list) *)
split.
{ intros sm x os i H0 hist P R C F.
  pose proof HK0 as [_ K1]. destruct (K1 _ _ _ _ _ _ P) as [h1 P1].
  rewrite (pvi_model prh_jr_strtod (pe_d en) (pe_rest en) o y (PresetReqAt.okk (Z.to_nat (pe_fail en - pe_cnt en)))
    Hsk), <- Hrest in R, C.
  rewrite Egt in F.
  exact (Hinj sm x os i H0 h1 P1 R C F). }
split; [rewrite Egt; exact Hmove|].
split; [intros a k Hak; rewrite <- Hab0; exact (Hfresh a k Hak)|].
split; [rewrite <- Hab0; exact Hperm|].
split; [cbv beta; rewrite <- Hfr0; exact Hfrm|].
split; [pose proof (pvm_hpeak prh_jr_strtod (pe_d en) (pe_rest en) ok) as Hh; rewrite Hjv in Hh; exact Hh|].
split; [rewrite <- Hbb0; exact Hbb|].
split; [exact Hls|].
destruct res as [[t r]|].
- apply tpiP_RSome_of in Hres.
  split; [exact (pvi_code code 0 Hcb ltac:(lia) (eq_trans (eq_sym Hc) (tpiPs_ret Hres)))|].
  split; [intros Hhd n Hn; destruct (tpiPs_freeord Hres Hhd Hn) as (F & HF & HFm); exists F; split;
    [exact HF | rewrite HFm; exact Efr]|].
  split; [exact (tpiPs_in_ok Hres)|]. split; [exact (tpiPs_node Hres)|]. split; [exact (tpiPs_ncap Hres)|].
  pose proof (tpiPs_lsum_le Hres) as Hlsr. lia.
- apply tpiP_RNone_of in Hres.
  split; [exact (pvi_code code (-1) Hcb ltac:(lia) (eq_trans (eq_sym Hc) (tpiPn_ret Hres)))|].
  split; [intros Hhd n Hn; destruct (tpiPn_freeord Hres Hhd Hn) as (F & HF & HFm); exists F; split;
    [exact HF | rewrite HFm; exact Efr]|].
  split; [|exact (tpiPn_fd Hres)].
  apply (pvi_after_weak _ _ _ _ _ (Z.of_nat (pe_d en) + 1)); [lia|exact (tpiPn_in_after Hres)].
Qed.

(* THE POST ACROSS A POINTWISE-EQUAL MEMORY (no functional extensionality): every byte and every writable byte kept *)
Lemma pvi_Qm_ext : forall (en : PvEnt) (fr : astate -> Prop) (code : Z) (ly' : alayout) (S' : astate) (Hp' : list Z)
    (W' : world SEGS) (m m' : word -> option byte),
  (forall x, mrestrict (w_H W') m' x = mrestrict (w_H W') m x) ->
  pv_Qm B en fr code ly' S' Hp' W' m -> pv_Qm B en fr code ly' S' Hp' W' m'.
Proof.
intros en fr code ly' S' Hp' W' m m' E HQ.
assert (EB : forall x, mbyte SEGS (mrestrict (w_H W') m') x = mbyte SEGS (mrestrict (w_H W') m) x)
  by (intros x; unfold mbyte; rewrite E; reflexivity).
assert (EW : forall x, writable_at SEGS (mrestrict (w_H W') m) x -> writable_at SEGS (mrestrict (w_H W') m') x)
  by (intros x Hw; unfold writable_at, wview in *; rewrite E; exact Hw).
(* the free order across the memory change: the order and the blocks are the same, the footprint's bytes kept *)
assert (FT : forall nlo L D ok, pv_ftie en nlo L W' m D ok -> pv_ftie en nlo L W' m' D ok) by
  (intros nlo L D ok Hft Hhd n Hn; destruct (Hft Hhd n Hn) as (F & HF & HFm); exists F; split; [|exact HFm];
   apply (PRH_PjOrder.pj_foR_frame SEGS n _ _ _ _ _ _ _ HF);
   [exact (PRH_PjOrder.pj_foR_lblk SEGS _ _ _ _ _ _ HF)
   |exact (PvB_X_Tree.pjx_agree_of_bytes SEGS _ _ _ (fun x _ => EB x) EW)]).
apply pvQ_R_of in HQ. destruct HQ as (ok & res & tr & okr & D & Lam' & peak' & cnt' & fail' & ran' & HR).
eapply pvQ_of_R.
refine {| pvq_run := pvq_run HR; pvq_ledger := _; pvq_room := pvq_room HR; pvq_hull := pvq_hull HR;
  pvq_rp := pvq_rp HR; pvq_outc := pvq_outc HR; pvq_inj := pvq_inj HR; pvq_move := pvq_move HR;
  pvq_fresh := pvq_fresh HR; pvq_perm := pvq_perm HR; pvq_fr := pvq_fr HR; pvq_peak := pvq_peak HR;
  pvq_bytes := pvq_bytes HR; pvq_lsum := pvq_lsum HR; pvq_arm := _ |}.
{ destruct (pvq_ledger HR) as ((G1 & G2 & G3 & G4 & G5 & (Gm & Gmb) & (Go & Gob) & Gr) & Hnd & HFA & HPP).
  split; [|split; [exact Hnd | split; [|exact HPP]]].
  - split; [exact (PRW_PjExt.pjx_val SEGS _ _ _ _ _ G1 (fun x _ => EB x))|].
    split; [exact (PRW_PjExt.pjx_val SEGS _ _ _ _ _ G2 (fun x _ => EB x))|].
    split; [exact (PRW_PjExt.pjx_val SEGS _ _ _ _ _ G3 (fun x _ => EB x))|].
    split; [exact (PRW_PjExt.pjx_val SEGS _ _ _ _ _ G4 (fun x _ => EB x))|].
    split; [exact (PRW_PjExt.pjx_val SEGS _ _ _ _ _ G5 (fun x _ => EB x))|].
    split; [split; [exact (PRW_PjExt.pjx_val SEGS _ _ _ _ _ Gm (fun x _ => EB x)) | exact Gmb]|].
    split; [split; [exact (PRW_PjExt.pjx_val SEGS _ _ _ _ _ Go (fun x _ => EB x)) | exact Gob] | exact Gr].
  - rewrite Forall_forall in HFA |- *. intros ak Hak. destruct (HFA ak Hak) as (K1 & K2 & K3 & K4 & K5).
    split; [exact K1|]. split; [exact K2|]. split; [exact K3|]. split; [exact K4|].
    exact (PRW_PjExt.pjx_val SEGS _ _ _ _ _ K5 (fun x _ => EB x)). }
pose proof (pvq_arm HR) as Hres.
destruct res as [[t r]|].
- destruct Hres as (Hc & Hft & Hin & Hnd & Hnc & Hsum). split; [exact Hc|].
  split; [exact (FT _ _ D ok Hft)|].
  split; [exact (PvB_X_Tree.pjx_in_ok_frame SEGS _ _ _ _ _ _ _ _ Hin (fun x _ => EB x) (fun x _ Hw => EW x Hw)
                   (fun x _ => EB x))|].
  split; [|split; [exact (PvB_Frees.pvf_ncap_ext SEGS t _ _ _ EB Hnc)|exact Hsum]].
  exact (PRW_PjExt.pj_nodeR_frame SEGS t _ _ _ _ _ Hnd
    (PvB_X_Tree.pjx_agree_of_bytes SEGS _ _ _ (fun x _ => EB x) EW)).
- destruct Hres as (Hc & Hft & Haf & Hfd). split; [exact Hc|].
  split; [exact (FT _ _ D ok Hft)|].
  split; [exact (PvB_X_Tree.pjx_in_after_frame SEGS _ _ _ _ _ _ _ Haf (fun x _ => EB x) (fun x _ Hw => EW x Hw))|].
  exact (PvB_X_Tree.pjx_fd_frame SEGS _ _ _ _ _ _ Hfd (PvB_X_Tree.pjx_agree_of_bytes SEGS _ _ _ (fun x _ => EB x) EW)).
Qed.

End c.
