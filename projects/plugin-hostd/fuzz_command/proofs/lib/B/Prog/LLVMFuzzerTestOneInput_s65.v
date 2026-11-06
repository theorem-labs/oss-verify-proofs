(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the two calls of rec_clear in LLVMFuzzerTestOneInput's ASan+UBSan walk (plugin-hostd/fuzz_command image B, jal at 0x86584 and 0x86af0), the B twin of lib/A/Prog/LLVMFuzzerTestOneInput_s65.v, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh2.v:122-290 (a program call through cl_callS, the callee's statement applied, the caller's facts carried past it). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YP03 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YCfn YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdPaLib
  CmdBase CmdRep CmdObj CmdRo CmdGlob PaCall PaNoChain PaCallPg CmdRecFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import rec_clear_c LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import LLVMFuzzerTestOneInput_defs
  LLVMFuzzerTestOneInput_s01.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* ---- events and the meter ---- *)
(* the call's events: the first rec_clear, then the loop and the second rec_clear *)
Lemma ev_ltoi_from_loc : forall pl, EV_LTOI pl = EV_REC_CLEAR R_ENTRY + ev_from 32 R_ENTRY pl.
Proof. intros pl. unfold EV_LTOI, ev_from. destruct (ev_msgs 32 R_ENTRY pl) as [k Rf]. cbn [fst snd]. ring. Qed.
Lemma bud_arith1_loc : forall f U e, 0 <= f <= U -> 0 <= e -> 2 * f + e * U <= (2 + e) * U.
Proof. intros f U e Hf He. nia. Qed.

(* ---- lists and registers ---- *)
Lemma NoDup_app_disj_loc : forall {A} (l1 l2 : list A) x, List.NoDup (l1 ++ l2) -> In x l1 -> ~ In x l2.
Proof.
intros A l1. induction l1 as [|a l1 IH]; intros l2 x H Hin Hx; [destruct Hin|].
cbn [app] in H. apply NoDup_cons_iff in H as [Hn Hd]. destruct Hin as [<- | Hin].
- apply Hn, in_or_app. right. exact Hx.
- exact (IH l2 x Hd Hin Hx).
Qed.
Lemma preserved_reg_loc : forall regs regs' (r : bv 5) z,
  aregs_preserved regs regs' -> acallee_saved z -> Z_to_bv 5 z = r -> getr regs' r = getr regs r.
Proof. intros regs regs' r z HP Hz <-. exact (HP z Hz). Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the callee's statement, never restated *)
Hypothesis HREC_CLEAR : forall fx0 : YK11.FPState, @trec_clear_spec fx0 rc SK PI B MT.
(* the per-binary facts, with the names of a Theorem Labs lane's RULING-STMT.md section 1 *)
Hypothesis HB : CmdBSyms B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis MTL : ameter_laws MT.
(* the image facts (lib/B/Prog/CmdRecFacts.v): g_rec, record.spill and g_quitting are unowned image bytes
   (CmdRecImg.v cmd_prog_unowned) *)
Hypothesis IMG : cmd_img_facts SEGS B.
Let PGU : forall a, inFP cmd_PG a ->
  in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4) :=
  cmd_prog_unowned SEGS B LAWS HB IMG.

(* the entry's frame chain (s0 the caller's) holds at the call's sp: the stack at and above the entry's sp is kept *)
Lemma lt_chain_entry_loc : forall cx ly S (W : world SEGS) regs mem md k,
  lt_base B MT cx -> lt_frame B cx ly S W regs mem md k -> getr regs 8 = getr (x_regs cx) 8 ->
  achain ly (rdW W mem) (spZ (x_regs cx) + -256) (s0Z regs) (x_ch cx).
Proof.
intros cx ly S W regs mem md k HBs HF R8.
pose proof HBs as (HPRE & _).
pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _ & Hch & _).
pose proof Hstk as (Hal & HS0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HF as (HJ & _).
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & F1 & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
pose proof asan_consts as (C1 & _).
assert (HLS : LTOI_STK = 32768) by reflexivity.
unfold s0Z. rewrite R8. fold (s0Z (x_regs cx)).
apply (achain_lower ly (rdW W mem) (spZ (x_regs cx))); [|lia].
apply (achain_ly_top (x_ly cx)); [exact Etop|].
apply (achain_kept (x_ly cx) (rdW (x_W cx) (x_mem cx)) (rdW W mem) (spZ (x_regs cx)) _ _ (spZ (x_regs cx)) Hch);
  [lia | lia |].
intros a Ha. unfold x_sp0 in F1. apply F1; [lia | lia |].
intros (r & Hr & Hlo & Hhi). unfold cmd_PG, A_G_REC, A_REC_SPILL, A_G_QUITTING in Hr. cbn [In] in Hr.
destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hlo, Hhi; lia.
Qed.

(* the saved registers are kept when their 104 bytes are *)
Lemma lt_saved_kept_loc : forall cx (rd rd' : reader),
  (forall a, x_sp0 cx - 104 <= a < x_sp0 cx -> rd' a = rd a) -> lt_saved cx rd -> lt_saved cx rd'.
Proof.
intros cx rd rd' Hk HS i r Hi.
assert (Hi13 : (i < length LT_SAVED)%nat) by (apply nth_error_Some; congruence).
change (length LT_SAVED) with 13%nat in Hi13.
rewrite (rdword_ext rd rd'); [exact (HS i r Hi)|].
intros j Hj. apply Hk. lia.
Qed.

(* rec_clear's footprint: g_rec and the recorder's blocks O, all below alloc_ceiling; g_quitting is outside it *)
Lemma lt_FP1_low_loc : forall ly S (W : world SEGS) mem md O, AR SEGS B ly S W mem md ->
  (forall pn, In pn O -> In pn (ablocks B ly S)) ->
  forall a, inFP ((A_G_REC, A_G_REC + REC_SIZE) :: ablocks_fp O) a -> a < alloc_ceiling.
Proof.
intros ly S W mem md O HAR HO a Hf. pose proof asan_consts as (C1 & _).
apply inFP_cons in Hf as [Hf | Hf]; [unfold A_G_REC, REC_SIZE in Hf; lia|].
destruct (inFP_ablocks_fp_inv O a Hf) as (p & n & Hin & Ha).
destruct (al_blocks _ _ LAWS ly S W mem md p n HAR (HO _ Hin)) as (_ & _ & Hc & _). lia.
Qed.
Lemma lt_FP1_quit_loc : forall ly S (W : world SEGS) mem md O, AR SEGS B ly S W mem md ->
  (forall pn, In pn O -> In pn (ablocks B ly S)) ->
  forall a, A_G_QUITTING <= a < A_G_QUITTING + 4 -> ~ inFP ((A_G_REC, A_G_REC + REC_SIZE) :: ablocks_fp O) a.
Proof.
intros ly S W mem md O HAR HO a Ha Hf.
apply inFP_cons in Hf as [Hf | Hf]; [unfold A_G_REC, REC_SIZE, A_G_QUITTING in *; lia|].
destruct (inFP_ablocks_fp_inv O a Hf) as (p & n & Hin & Hpa).
pose proof (blk_off_imgP B ly S W mem md p n HAR (HO _ Hin)) as Hoff.
unfold YCbq.off_img in Hoff. unfold A_G_QUITTING in Ha. lia.
Qed.
Lemma lt_FP1_closed_loc : forall ly S (W : world SEGS) mem md O, AR SEGS B ly S W mem md ->
  (forall pn, In pn O -> In pn (ablocks B ly S)) ->
  ~ YI16.sink_open_fp ((A_G_REC, A_G_REC + REC_SIZE) :: ablocks_fp O).
Proof.
intros ly S W mem md O HAR HO.
apply sink_closed_cons; [unfold A_G_REC; cbn [fst]; lia|].
apply sink_closed_ablocks_fp. apply Forall_forall. intros [p n] Hin.
destruct (al_blocks _ _ LAWS ly S W mem md p n HAR (HO _ Hin)) as (_ & H4096 & _). cbn [fst]. lia.
Qed.
(* g_quitting is kept by rec_clear: an unowned image byte outside its footprint *)
Lemma lt_quit_kept_loc : forall ly S (W : world SEGS) mem md ly2 S2 (W2 : world SEGS) mem2 md2 STK1 sp1 O EV1 q,
  AR SEGS B ly S W mem md -> (forall pn, In pn O -> In pn (ablocks B ly S)) ->
  ajournal SEGS B STK1 sp1 ((A_G_REC, A_G_REC + REC_SIZE) :: ablocks_fp O) ly S W mem md [] ly2 S2 W2 mem2 md2 EV1 ->
  aval_mem (rdW W mem) A_G_QUITTING 4 q -> aval_mem (rdW W2 mem2) A_G_QUITTING 4 q.
Proof.
intros ly S W mem md ly2 S2 W2 mem2 md2 STK1 sp1 O EV1 q HAR HO HJ Hq k Hk.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
assert (Ha : A_G_QUITTING <= A_G_QUITTING + Z.of_nat k < A_G_QUITTING + 4) by lia.
assert (Hpg : inFP cmd_PG (A_G_QUITTING + Z.of_nat k)).
{ exists (A_G_QUITTING, A_G_QUITTING + 4). split; [right; right; left; reflexivity | cbn [fst snd]; lia]. }
destruct (PGU _ Hpg) as (Hi & Ho & He).
rewrite (F3 _ Hi Ho He); [exact (Hq k Hk)|].
apply fp_spares_closed;
  [exact (lt_FP1_closed_loc ly S W mem md O HAR HO) | exact (lt_FP1_quit_loc ly S W mem md O HAR HO _ Ha)].
Qed.
(* rec_clear of a recorder whose spill holds no call owns no block *)
Lemma lt_rep_clear_nil_loc : forall ly S rd R O', r_spill R = (0, []) ->
  rec_repA B ly S rd (RecModel.rec_clear R) O' -> O' = [].
Proof.
intros ly S rd R O' Hsp (Q & HA & HO).
destruct HA as (_ & _ & _ & (_ & Hlen & _ & _ & Hspill & _) & Hans & Hrep & _ & _).
cbn [RecModel.rec_clear r_calls length] in Hlen.
assert (Ec : l_calls Q = []) by (apply length_zero_iff_nil; exact Hlen).
destruct Hspill as (_ & _ & HL & _). cbn [RecModel.rec_clear r_spill] in HL. rewrite Hsp in HL. cbn [snd length] in HL.
assert (Es : l_spill Q = []) by (apply length_zero_iff_nil; exact HL).
unfold aanswer_at in Hans. cbn [RecModel.rec_clear r_answer] in Hans.
assert (Ea : l_answer Q = None) by (revert Hans; destruct (l_answer Q); cbn; [intros [] | intros _; reflexivity]).
unfold areply_at in Hrep. cbn [RecModel.rec_clear r_reply] in Hrep.
assert (Er : l_reply Q = None) by (revert Hrep; destruct (l_reply Q); cbn; [intros [] | intros _; reflexivity]).
destruct O' as [|pn O']; [reflexivity|exfalso].
pose proof (proj1 (HO pn) (or_introl eq_refl)) as Hin.
unfold lay_blocks in Hin. rewrite Ec, Es, Ea, Er in Hin. destruct Hin.
Qed.

(* ---- the call of rec_clear from a point of the frame (sp = the entry's sp - 256), through PaCallPg.v's
   cl_callS_pg (PaNoChain.v's cl_callS_wide with footprint g_rec and the recorder's blocks O: a program static, and
   blocks made since the entry), to the return with the caller's facts carried: cgif A/ACh2.v:208-227. The frame
   chain at the call is the caller's ch1 (achain at the callee's sp); rec_clear's post is apost_base, so the return
   is at the same FP state ---- *)
Lemma lt_rc_call_loc : forall cx ly S (W : world SEGS) regs mem md k R O q ch1,
  lt_base B MT cx -> lt_frame B cx ly S W regs mem md k ->
  YK0s.ret_ok (getr regs 1) -> 4096 <= bv_unsigned (getr regs 1) ->
  achain ly (rdW W mem) (spZ (x_regs cx) + -256) (s0Z regs) ch1 ->
  lt_rec B cx ly S W mem R O q [] ->
  st_nev S + EV_REC_CLEAR R <= EV_MAX -> mo_ok MT S (XM_REC_CLEAR MT R) ->
  (forall (W2 : world SEGS) ly2 S2 regs2 mem2 md2,
     lt_frame B cx ly2 S2 W2 regs2 mem2 md2 (k + EV_REC_CLEAR R) -> aregs_preserved regs regs2 ->
     lt_rec B cx ly2 S2 W2 mem2 (RecModel.rec_clear R) [] q [] -> mo_le MT S S2 (XM_REC_CLEAR MT R) ->
     SRr SEGS W2 (mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2) (lt_post B MT cx)) ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + AF_rec_clear)) mem (seg_rom SEGS)) md) (lt_post B MT cx).
Proof.
intros cx ly S W regs mem md k R O q ch1 HBs HF Hraw Hra4 Hch HR HEV HMO HK.
pose proof HBs as (HPRE0 & _).
pose proof HPRE0 as (_ & _ & _ & Hgp0 & Htp0 & Hstk0 & _).
pose proof Hstk0 as (Hal0 & HS00 & Hceil0 & Hslo0 & Hshi0 & H470 & Hbot0 & Htop0 & Htop20).
pose proof HF as (HJ & Hsp & Hgp & Htp & Hsv).
pose proof (proj1 HJ) as HAR.
pose proof HR as (Hrep & Hspill & H2 & Hq & Hq0 & Hperm).
pose proof asan_consts as (C1 & _).
assert (HLS : LTOI_STK = 32768) by reflexivity.
assert (HRS : REC_CLEAR_STK = 16560) by reflexivity.
unfold x_sp1, LT_FRAME in Hsp.
assert (HO : forall pn, In pn O -> In pn (ablocks B ly S)).
{ intros pn Hpn. apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. left. exact Hpn. }
pose proof (lt_ablocks_NoDup B LAWS ly S W mem md HAR) as HND.
pose proof (Permutation_NoDup Hperm HND) as HND2.
pose proof (lt_FP1_low_loc ly S W mem md O HAR HO) as HFlo.
assert (Hsp' : spZ regs = x_sp0 cx + -256) by (unfold x_sp0; lia).
pose proof (lt_arodata_kept B MT LAWS HB IMG cx ly S W mem md [] k HBs HJ) as HRO.
eapply SRr_bind.
{ apply (cl_callS_pg B LAWS W regs mem (Z_to_bv 64 (BASE + AF_rec_clear)) LTOI_STK (x_sp0 cx) cmd_PG
    (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) [] ly S md k REC_CLEAR_STK
    ((A_G_REC, A_G_REC + REC_SIZE) :: ablocks_fp O) (EV_REC_CLEAR R) (-256) (getr regs 1) ch1
    (fun ly' S' (W' : world SEGS) (regs' : bvmap 5 word) mem' md' => exists (O' D : list (Z * Z)),
       rec_repA B ly' S' (rdW W' mem') (RecModel.rec_clear R) O' /\ (forall pn, In pn O' -> In pn O) /\
       (forall pn, In pn D <-> In pn O /\ ~ In pn O') /\ Permutation (ablocks B ly S) (ablocks B ly' S' ++ D) /\
       blocks_bytes S' <= blocks_bytes S + LIVE_REC_CLEAR /\ mo_le MT S S' (XM_REC_CLEAR MT R))
    HJ Hsp' eq_refl ltac:(lia) ltac:(lia) ltac:(rewrite HRS, HLS; lia)
    ltac:(rewrite Hgp; exact Hgp0) ltac:(rewrite Htp; exact Htp0) eq_refl Hraw Hra4 Hch).
  - intros HPRE1. eapply SRr_mono.
    + exact (HREC_CLEAR fx ly S W regs mem md ch1 R O HPRE1 HRO Hrep H2 HEV HMO).
    + intros W3 c3 _ H3. exact H3.
  - intros a Hf. apply inFP_cons in Hf as [Hf | Hf].
    + (* g_rec: a program static of the image, in the walk's footprint *)
      left. assert (Hpg : inFP cmd_PG a).
      { exists (A_G_REC, A_G_REC + 960). split; [left; reflexivity | cbn [fst snd]; unfold REC_SIZE in Hf; lia]. }
      split; [exact Hpg|]. right. split; [|exact (proj1 (PGU a Hpg))].
      rewrite (ts_prog B HB). unfold TFIB_PROG_STATIC. apply Exists_cons_hd. unfold in_zr. cbn [fst snd].
      unfold A_G_REC, REC_SIZE in Hf. lia.
    + (* a block of the recorder: live at the call, made since the entry *)
      destruct (inFP_ablocks_fp_inv O a Hf) as (p & n & Hin & Ha).
      right. unfold in_tmp_block. exists p, n. split; [exact (HO _ Hin)|]. split; [|exact Ha].
      intros Hx. exact (NoDup_app_disj_loc O (x_bl0 B cx ++ []) (p, n) HND2 Hin (in_or_app _ _ _ (or_introl Hx))). }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc & HP & (O' & D & HR' & HO' & HD & HPd & _ & HML)).
pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & JF1 & _).
pose proof (lt_rep_clear_nil_loc ly2 S2 (rdW W2 mem2) R O' Hspill HR') as EO'. subst O'.
apply (HK W2 ly2 S2 regs2 mem2 md2); [ | exact HP | | exact HML].
- split; [exact HJ2|].
  split; [unfold spZ; rewrite (preserved_reg_loc regs regs2 (2%bv : bv 5) 2 HP ltac:(unfold acallee_saved; lia)
    ltac:(apply bv_eq; reflexivity)); unfold x_sp1, LT_FRAME; exact Hsp|].
  split; [rewrite (preserved_reg_loc regs regs2 (3%bv : bv 5) 3 HP ltac:(unfold acallee_saved; lia)
    ltac:(apply bv_eq; reflexivity)); exact Hgp|].
  split; [rewrite (preserved_reg_loc regs regs2 (4%bv : bv 5) 4 HP ltac:(unfold acallee_saved; lia)
    ltac:(apply bv_eq; reflexivity)); exact Htp|].
  apply (lt_saved_kept_loc cx (rdW W mem) (rdW W2 mem2)); [|exact Hsv].
  intros a Ha. unfold x_sp0 in *. rewrite HLS in Hslo0.
  apply JF1; [lia | rewrite HRS; lia | intros Hf; pose proof (HFlo a Hf); lia].
- split; [exact HR'|]. split; [exact Hspill|]. split; [cbn [RecModel.rec_clear r_calls length]; lia|].
  split; [exact (lt_quit_kept_loc ly S W mem md ly2 S2 W2 mem2 md2 _ _ O _ q HAR HO HJc Hq)|].
  split; [exact Hq0|].
  assert (HDO : Permutation D O).
  { apply NoDup_Permutation.
    - pose proof (Permutation_NoDup HPd HND) as H. apply (Permutation_NoDup (Permutation_app_comm _ _)) in H.
      exact (NoDup_app_l_loc D _ H).
    - exact (NoDup_app_l_loc O _ HND2).
    - intros x. split; [intros Hx; exact (proj1 (proj1 (HD x) Hx)) |
        intros Hx; apply (proj2 (HD x)); split; [exact Hx | intros []]]. }
  assert (H1 : Permutation (O ++ ablocks B ly2 S2) (O ++ (x_bl0 B cx ++ []))).
  { eapply Permutation_trans; [apply Permutation_app_comm|].
    eapply Permutation_trans; [apply Permutation_app_head; apply Permutation_sym; exact HDO|].
    eapply Permutation_trans; [apply Permutation_sym; exact HPd|]. exact Hperm. }
  eapply Permutation_app_inv_l. exact H1.
Qed.

(* 0x86584: jal rec_clear, from the entry's recorder (no call, no answer, no reply), s0 the caller's (the entry's
   chain x_ch, at the callee's sp = the entry's sp - 256), to 0x86588 *)
Lemma lt_call_RC1 : LTA_A B MT -> LT_RC1_stmt B MT.
Proof.
intros HA cx ly S W regs mem md R HBs Hfrm HF R1 R25 R23 R24 R8 HR HC HAn HRp HNr HBud.
pose proof HBs as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hev & _ & Hmo).
pose proof HF as (HJ & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev & _).
pose proof HBud as (Hb1 & Hb2 & Hb3 & Hb4 & Hb5 & Hb6).
pose proof pa_B_ok as (HB0 & HB1 & _). pose proof pa_base_lo as HBLO.
assert (HEA : ev_args R = 0) by (unfold ev_args; rewrite HC; reflexivity).
assert (HE2 : EV_REC_CLEAR R = 2) by (unfold EV_REC_CLEAR; rewrite HEA; reflexivity).
assert (HX2 : XM_REC_CLEAR MT R = 2 * mo_free MT) by (unfold XM_REC_CLEAR; rewrite HEA; reflexivity).
pose proof (ev_ltoi_from_loc (x_pl cx)) as HEL. change (EV_REC_CLEAR R_ENTRY) with 2 in HEL.
pose proof (ev_from_nonneg 32 R_ENTRY (x_pl cx)) as HE0.
pose proof (mo_free_nonneg MT MTL) as Mf. pose proof (mo_malloc_nonneg MT MTL 32784 ltac:(lia)) as Mm.
assert (HXL : XM_LTOI MT (x_pl cx) = EV_LTOI (x_pl cx) * LT_U MT) by reflexivity.
assert (HU : 0 <= mo_free MT <= LT_U MT) by (unfold LT_U; lia).
pose proof (bud_arith1_loc (mo_free MT) (LT_U MT) (ev_from 32 R_ENTRY (x_pl cx)) HU HE0) as HAR1.
assert (HeU : 0 <= ev_from 32 R_ENTRY (x_pl cx) * LT_U MT) by (apply Z.mul_nonneg_nonneg; lia).
rewrite HEL in HXL, Hb3, Hev.
apply (lt_rc_call_loc cx ly S W regs mem md 0 R [] 0 (x_ch cx) HBs HF).
- rewrite R1. unfold w64. apply ret_ok_codeptr_v; [unfold LO_RC1RA; lia | reflexivity].
- rewrite R1. unfold w64, LO_RC1RA. rewrite unsigned_lit_small; lia.
- exact (lt_chain_entry_loc cx ly S W regs mem md 0 HBs HF R8).
- exact HR.
- rewrite HE2. lia.
- apply (mok_station MT (x_S cx) S (XM_LTOI MT (x_pl cx)) 0 (XM_REC_CLEAR MT R) MTL Hmo Hb4);
    rewrite HX2; [lia | rewrite HXL; lia].
- intros W2 ly2 S2 regs2 mem2 md2 HF2 HP HR2 HML. rewrite R1.
  apply (HA fx cx ly2 S2 W2 regs2 mem2 md2 (0 + EV_REC_CLEAR R) (0 + XM_REC_CLEAR MT R) (RecModel.rec_clear R) HBs Hfrm
    HF2).
  + rewrite (preserved_reg_loc regs regs2 (25%bv : bv 5) 25 HP ltac:(unfold acallee_saved; lia)
      ltac:(apply bv_eq; reflexivity)). exact R25.
  + rewrite (preserved_reg_loc regs regs2 (23%bv : bv 5) 23 HP ltac:(unfold acallee_saved; lia)
      ltac:(apply bv_eq; reflexivity)). exact R23.
  + rewrite (preserved_reg_loc regs regs2 (24%bv : bv 5) 24 HP ltac:(unfold acallee_saved; lia)
      ltac:(apply bv_eq; reflexivity)). exact R24.
  + exact HR2.
  + reflexivity.
  + reflexivity.
  + reflexivity.
  + reflexivity.
  + unfold lt_bud. split; [rewrite HE2; lia|]. split; [exact HE0|]. split; [rewrite HE2; lia|].
    split; [exact (mo_le_trans MT MTL _ _ _ _ _ Hb4 HML)|]. rewrite HX2, HXL. split; lia.
Qed.

(* 0x86af0: jal rec_clear, from the head with no byte left or after pass 31, s0 = -1 (0x865f0; achain's empty
   case, ly_top ly - 16 <= 2^64 - 1), to 0x86af4 *)
Lemma lt_call_RC2 : LTA_Z2 B MT -> LT_Z_stmt B MT.
Proof.
intros HZ2 cx ly S W regs mem md k acc R O q HBs Hfrm HF R1 R25 R8 HR HBud.
pose proof HBs as (HPRE0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hev & _ & Hmo).
pose proof HF as (HJ & _).
pose proof HJ as (_ & Hly & _ & _ & _ & _ & Hnev & _).
pose proof HBud as (Hb1 & Hb2 & Hb3 & Hb4 & Hb5 & Hb6).
pose proof pa_B_ok as (HB0 & HB1 & _). pose proof pa_base_lo as HBLO.
pose proof (ev_args_nonneg R) as HA0.
pose proof (mo_free_nonneg MT MTL) as Mf. pose proof (mo_malloc_nonneg MT MTL 32784 ltac:(lia)) as Mm.
assert (HU : mo_free MT <= LT_U MT) by (unfold LT_U; lia).
assert (HE0 : 0 <= EV_REC_CLEAR R) by (unfold EV_REC_CLEAR; lia).
assert (HX0 : 0 <= XM_REC_CLEAR MT R) by (unfold XM_REC_CLEAR; apply Z.mul_nonneg_nonneg; lia).
pose proof (xm_rec_clear_le MT MTL R) as HXU.
assert (Hch : achain ly (rdW W mem) (spZ (x_regs cx) + -256) (s0Z regs) []).
{ pose proof HPRE0 as (_ & _ & _ & _ & _ & Hstk0 & _).
  pose proof Hstk0 as (_ & _ & _ & _ & _ & H470 & _ & _ & Htop20).
  pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
  assert (E1 : s0Z regs = 2 ^ 64 - 1) by (unfold s0Z; rewrite R8; vm_compute; reflexivity).
  left. split; [right; left; lia | reflexivity]. }
apply (lt_rc_call_loc cx ly S W regs mem md k R O q [] HBs HF).
- rewrite R1. unfold w64. apply ret_ok_codeptr_v; [unfold LO_RC2RA; lia | reflexivity].
- rewrite R1. unfold w64, LO_RC2RA. rewrite unsigned_lit_small; lia.
- exact Hch.
- exact HR.
- lia.
- exact (mok_station MT (x_S cx) S (XM_LTOI MT (x_pl cx)) acc (XM_REC_CLEAR MT R) MTL Hmo Hb4 HX0 ltac:(lia)).
- intros W2 ly2 S2 regs2 mem2 md2 HF2 HP HR2 HML. rewrite R1.
  apply (HZ2 fx cx ly2 S2 W2 regs2 mem2 md2 (k + EV_REC_CLEAR R) (acc + XM_REC_CLEAR MT R) R q HBs Hfrm HF2).
  + rewrite (preserved_reg_loc regs regs2 (25%bv : bv 5) 25 HP ltac:(unfold acallee_saved; lia)
      ltac:(apply bv_eq; reflexivity)). exact R25.
  + exact HR2.
  + unfold lt_bud. split; [lia|]. split; [lia|]. split; [lia|].
    split; [exact (mo_le_trans MT MTL _ _ _ _ _ Hb4 HML)|]. split; lia.
Qed.

End e.
End f.
End d.
Print Assumptions lt_call_RC1.
Print Assumptions lt_call_RC2.
