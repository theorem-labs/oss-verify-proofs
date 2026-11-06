(* fuzz_preset, slice S5b, lane VstrD: THE STRING ARM of parse_value (image A 0x85f10), rows 135..151 (0x86124..
   0x86164), joining the shared epilogue at ROW 225 (0x8628c).
   rule 24: no function proved
   rule 24: proves no function (kind: segment lemma). vrd_str_a_ok goes from VproC's dispatch state (VrdPro.vrd_disp_a,
   arm VA_str) to VnumD's join state (VrdNum.vrd_epi_aR at wle' with the arm's result VrdNum.vrd_pv_post), with
   parse_string by its published text (PRH_FnReader.tparse_string_specX, blob fb7b12dfa169) as a Section hypothesis.
   The stretches 135..141 and 143..151 run on the engine (YC80xf_inv's paj_run_xf_inv / paj_run_to_xf_inv); the call
   of row 142 is VrdArm.vrd_call_Wb_P; the join is VrdArmStr.vrs_join.
   THE POST-IMPLICATION TEXTS (kit a working branch 3ac20a5c9e30: PRH_FnReader.v blob fb7b12dfa169,
   PRH_FnParse.v blob 94232293d483): parse_string takes no entry position, so the arm supplies nothing about the model
   run before the call; it proves the position AFTER the call (vrd_pv_post's transfer and outcome clauses) from
   parse_string's post arms, choosing the run and position itself (VrdArmStr.vrs_rq). parse_string's two live-count
   premises at the call are vrd_disp_body's conjuncts; the instance fact cf_head = PresetReqAt.HEAD is the Section
   hypothesis HI_head.
   Rows of the #102 pin A' image's disassembly of parse_value: line n is image A 0x85f10 + 4 * (n - 2).
   THE GENERIC INVARIANT (a Theorem Labs lane 12:19Z): an SRr post is opaque once Qed, so an end-state memory invariant must
   be in the segment's STATEMENT; the generic SRr_memnorm was measured NOT provable (a Theorem Labs lane), so it cannot be added
   afterwards. vrd_str_a_okP carries any P with srr_inv_laws through the two runs and, with srr_inv_call, across the
   row-142 call (vrd_call_W_P, by the keep of parse_string's m-form post, fQmn's second conjunct). vrd_str_a_ok is its
   corollary at P := fun _ => True.
   THE ENTRY FLOAT STATE IS PINNED: both statements conclude at `vrd_epi_aR (fx := fx) ..`, the Section's fx being
   parse_value's entry float state, as VrdNum.vrd_num_a_stmt / VrdNumEnd.vrd_num_end_stmt and the consumer
   VrdEpiA.vrd_epi_step / VrdEpiP.vrd_epi_step_P state it. Unpinned, vrd_epi_a's implicit FPState elaborates at the
   bound fx2 (the nearest instance in scope), and its float keep `fregs_kept_x fx2 fx2` is trivial. The join's float
   state is the entry's (fx2 := fx): parse_string's fpostWm returns at the caller's float state.
   THE RE-HIDING MOVE: parse_string's text concludes SRr' segs RZ_cf with its journal at wle' (it frees its block on a
   bad escape), so both statements conclude SRr' and their join is VrdNum.vrd_epi_aR at wle'. Rows 135..141 run at
   wle and their post is the rest of the arm as an SRr' goal (SRr_SRr' with SRrG_bind at wle'); the dispatch journal
   is lifted to wle' for the call (ajournal_xwR_mono with wle_wle'). Rows 143..151 run at wle on a journal that starts
   at parse_string's post state, which ajournal_xw_subR at wle' composes after the journal from parse_value's entry.
   THE HULL BUDGET: both statements take parse_value's entry budget over its all-granted events right after the
   dispatch state, as the container arm does; parse_string's budget is that list (VrdArmStr.vrs_gt_evs) at the
   dispatch state, whose meters are the entry's. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YI16 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC80xf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YSRrMemnorm YC80xf_inv.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YGcfRoomPre YGcfRoomKeep YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos PresetRoomPosKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import
PRH_Base PRH_Reader PRH_FnReader PRH_Charge PRH_FnParse VrdPro.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Listing_prog PAImg_prog VrdNum VrdArm VrdArmStr.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetHullBudget.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* PRW_StepKit (through VrdIStep) loads YF0v.v, which sets Zify's euclidean-division flag off GLOBALLY; this file's lia
   goals over `mod` and `/` need it on (VrdIStep.v does the same) *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* lia over the arithmetic facts only. The arm's context holds the symbolic states, journals and run tables, and lia
   (LiaTuning's zify_prune) walks every hypothesis: here each call took 60-100 s. slia first clears every hypothesis
   that is not an equation, an order fact or a propositional combination of them; it is used only where lia closes
   the goal, so the clearing never reaches another goal. *)
Ltac slia_clear :=
  repeat match goal with
  | H : ?T |- _ =>
      lazymatch type of T with Prop => idtac | _ => fail end;
      lazymatch T with
      | @eq _ _ _ => fail | Z.le _ _ => fail | Z.lt _ _ => fail | Z.ge _ _ => fail | Z.gt _ _ => fail
      | le _ _ => fail | lt _ _ => fail | ge _ _ => fail | gt _ _ => fail
      | _ /\ _ => fail | _ \/ _ => fail | ~ _ => fail | _ <> _ => fail
      | _ => clear H
      end
  end.
Ltac slia := slia_clear; lia.

Section str.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PI : PrhImg} {RL : PrhRoomLive}.
#[local] Abbreviation SEGS := (@pa_segs rc A_prog_listing PI_prog_A).
#[local] Abbreviation ROW := (fun n : nat => A_prog_base + 4 * Z.of_nat (n + 4682)).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Context {HL : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx HL.
Variable d : nat.
Variable CTX0 : list (list Z).
Variable CW : list (list Z).
(* parse_string, the kit's text lib/A/PRH_FnReader.v tparse_string_specX (the kit's cut 7cdbb61b5fa0, blob f1ae32e3b2cd: the
   cursor set CW in place of the run-word list, prh_cw_ok in the slot of the deleted prh_cur_ok, the wild budget
   against CW, the per-event live room, and the post budgeted at wbudget CW 0, fpostWbm) *)
Hypothesis H_parse_string : tparse_string_specX B ARx SK CTX0 CW.
(* INSTANCE FACT (a Theorem Labs lane's ruling, one name in every file whose proofs use it; first introduced with its witness
   in VrdArmStr.v): the allocator's head is the model's HEAD, discharged at the unit's top by reflexivity at
   CfParams_preset. The join (VrdArmStr.vrs_join) reads parse_string's lists as the model's events under it. *)
Hypothesis HI_head : cf_head = PresetReqAt.HEAD.

(* the trivial invariant, for the corollary *)
Lemma vrs_inv_laws_true : srr_inv_laws SEGS (fun _ => True).
Proof. split; intros; exact I. Qed.
Lemma vrs_inv_call_true : srr_inv_call SEGS (fun _ => True).
Proof. intros m m' _ _. exact I. Qed.

(* ---- THE ARM: rows 135..151, joining the epilogue at ROW 225 ---- *)
Lemma vrd_str_a_okP : forall (P : (word -> option byte) -> Prop), srr_inv_laws SEGS P -> srr_inv_call SEGS P ->
  (* the instance facts and the boundaries this arm carries, each named in the report *)
  HL = cf_head -> 8 <= cf_head ->
  (forall a, Exists (in_zr a) prh_pst -> in_img SEGS a) ->
  pi_s0cur F_parse_string = Some 0 -> pi_s0cur F_parse_items = Some 0 ->
  forall ly0 S0 Hp0 W0 regs0 mem0 md0 ch e q v text len p (tb : list Z)
    (Lam : list (Z * Z)) peak cnt fail ran most own W c y,
  fpre B ARx (STK_parse_value d) ly0 S0 Hp0 W0 regs0 mem0 md0 ch ->
  vrd_disp_a B ARx SK ly0 S0 Hp0 W0 regs0 mem0 md0 ch CTX0 CW e q v text len p d tb Lam peak cnt fail ran most own
    W c ->
  PresetHullBudget.hull_budget S0 (PresetReqAt.rd_hevs (prhPv_gtrace d (rest_atR tb text p))) ->
  PjGrammar.skip (rest_atR tb text p) = 34 :: y ->
  STK_parse_string + 176 <= STK_parse_value d ->
  P (ms_mem (cfg_ms c)) ->
  SRr' SEGS YGcfRehidePost.RZ_cf W c (fun W' c' => (exists (fx2 : YK11.FPState) (pos rv : Z),
    vrd_epi_aR (fx := fx) B ARx SK (wle' SEGS YGcfRehidePost.RZ_cf) fx2 d CW e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos rv
      (vrd_pv_post B d e q v text len p tb ly0 S0 Lam peak cnt fail ran most own pos rv) W' c') /\
    P (ms_mem (cfg_ms c'))).
Proof.
intros P PLAW PCALL HLcf Hcfw HPSTi H_s0ps H_s0pi ly0 S0 Hp0 W0 regs0 mem0 md0 ch e q v text len p tb Lam peak cnt
  fail ran most own W c y HPRE HD HHB Hskip HBUD HPM.
destruct HD as (arm & pos & p' & k & ly & S & Hp & regs & mem & md & Hc & HBODY).
unfold vrd_disp_body in HBODY.
destruct HBODY as (Hrest & Hpp & Harm & HJ & Hfrs & Hab
  & HHp & Hsetfs & Hwin & Hfwin & Hframe & Hsaved & Hregs & Hchain_e & Hclos & Hcur & Hcurq & Hinok & HRAq
  & Hnode & HUNIV & Hq1 & Hq2 & Hqv & Hgp0' & Htp0' & HRAok0 & Hra40 & Hinok0 & HdM & Htv & Hnowin0
  & Hu1 & Hu2 & Hmaxrun & Hcntb & Hsrc & Hhome & HLED & HROOMd & Hsec0 & H240 & Hsecs & H24s & Hfrcount
  & HROD & HFZ & HCW & HWRd & HCEIL).
assert (HCNT : cnt + 1 < 2 ^ 64 - 1) by slia.
(* the entry ra is below the ceiling: fpre's fourth conjunct (PRH_Base.v blob ee2f5cd7ed35 :746), read by name. tauto
   runs on HPRE alone: in the full context it would split every disjunctive hypothesis *)
assert (Hra0c : raZ regs0 < alloc_ceiling) by (clear - HPRE; unfold fpre in HPRE; tauto).
(* the node is not in the granted real-stack window: a conjunct of the dispatch state since
   a working branch 09ccdd8bda3, so this lane carries no stand-in for it *)
assert (Hnowin : ~ (spZ regs0 <= v /\ v + 56 <= spZ regs0 + e)) by (intros (A1 & A2); slia).
rewrite Hskip in Harm. destruct Harm as (Harm & Hp'lt & Hnth & Hws & Hb).
replace (vrd_arm_of 34) with VA_str in Harm by (vm_compute; reflexivity). subst arm.
destruct Hnode as (Hv4096 & Hv8 & Hvrw & Hvzero & Hvat & Hvmr & Hvown & Hvra).
destruct Hregs as (Rsp & R9 & R8 & R18 & R26 & R19 & R20 & R21 & R22 & R25 & R23 & R24 & R27 & R3 & R4 & R10 & R12).
subst c. unfold cfg_at.
replace (pa_sigma AS_parse_value + vrd_arm_off VA_str) with (pa_val A_TEXT + VrdArm.vrs_pc0)
  by (vm_compute; reflexivity).
pose proof (@pa_segs_low _ _ PI_prog_A) as Hsegs.
pose proof (@pa_wx _ _ PI_prog_A) as Hwx.
pose proof (proj1 HJ) as HARd. cbv beta in HARd.
assert (Hv47 : 4096 <= v /\ v + 56 <= 2 ^ 47 - 1)
  by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hvmr; slia).
assert (Hv64 : 0 <= v < 2 ^ 64) by slia.
(* the cursor's position and the text after the opening quote *)
assert (Htxp : text <= p' <= text + len)
  by (destruct Hinok as (_ & _ & _ & _ & _ & _ & _ & Ht & _); exact Ht).
assert (Hrest' : rest_atR tb text p' = 34 :: y) by (rewrite Hrest, Hskip; reflexivity).
assert (Hsucc : rest_atR tb text (p' + 1) = y)
  by (rewrite (VrdArm.vrs_rest_succ tb text p' ltac:(slia)), Hrest'; reflexivity).
assert (Hgt : prhPv_gtrace d (rest_atR tb text p) = prhPs_gtrace y) by (apply (VrdArm.vrs_gtrace_str d); exact Hskip).
(* the text is apart from the node: there IS a text here (text <= p' < text + len), so vrd_disp_body's guarded
   conjunct (rd_pre's `0 < len ->` form) applies *)
assert (Htv' : text + len <= v \/ v + 56 <= text) by (apply Htv; slia).
pose proof Hinok as (_ & _ & _ & _ & _ & _ & _ & _ & Hlentb & _).
pose proof Hinok0 as (_ & _ & _ & _ & _ & _ & _ & Htp0 & _).
(* the request bound of the dispatch's room, at parse_string's granted trace *)
assert (HmaxR : prh_maxreq (prhPs_gtrace y) + cf_head < cf_malloc_max)
  by (destruct HROOMd as (_ & Hm & _); rewrite Hgt in Hm; exact Hm).
(* ---- where the node lies: a live block of the dispatch state, or a live fake frame ---- *)
assert (Hplace : (exists b n, In (b, n) (ablocks B ly S) /\ b <= v /\ v + 56 <= b + req_size n) \/
                 (exists cid pos', In (cid, pos') (frames S) /\ frame_addr ly cid pos' <= v /\
                    v + 56 <= frame_addr ly cid pos' + fs_frame_bytes cid)).
{ destruct Hvat as [(a0 & k0 & Hin & Hle & Hhi) | [(b0 & m0 & Hin & _ & Hle & Hhi) | [(cid & pos' & Hin & Hle & Hhi) | Hww]]].
  - left. destruct (vrs_hb B ly S Hp W mem Lam peak cnt fail ran most own a0 k0 HLED Hin) as (Hk0 & Hab0 & _).
    exists (a0 - cf_head), (k0 + cf_head). split; [exact Hab0|].
    pose proof cf_head_nonneg as Hcf.
    unfold req_size. destruct (Z.eqb_spec (k0 + cf_head) 0); slia.
  - left. exists b0, m0. split; [exact Hin|]. unfold req_size. destruct (Z.eqb_spec m0 0); slia.
  - right. exists cid, pos'. split; [exact Hin|]. slia.
  - exfalso. apply Hnowin. exact Hww. }
assert (Hvceil : v + 56 <= alloc_ceiling).
{ destruct Hplace as [(b0 & n0 & Hin & Hle & Hhi) | (cid & pos' & Hin & Hle & Hhi)].
  - destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md b0 n0 HARd Hin) as (_ & _ & Hc0 & _). slia.
  - destruct (alx_sep SEGS B ARx LAWS ly S Hp W mem md HARd) as (_ & Hfa).
    pose proof (proj1 (Forall_forall _ _) Hfa (cid, pos') Hin) as (H1 & H2). cbn [fst snd] in H1, H2. slia. }
(* the node is client memory, so it is not an image byte *)
assert (Hvnimg : forall a, v <= a < v + 56 -> ~ in_img SEGS a).
{ intros a Ha. apply (alx_client_img SEGS B ARx LAWS ly S Hp W mem md a HARd).
  destruct Hplace as [(b0 & n0 & Hin & Hle & Hhi) | (cid & pos' & Hin & Hle & Hhi)].
  - left. exists b0, n0. split; [exact Hin | slia].
  - right. left. exists cid, pos'. split; [exact Hin | slia]. }
(* every harness block's HEAD WORD is apart from the node (this is where 8 <= cf_head is used) *)
assert (HHEAD : forall a kk i, In (a, kk) Lam -> 0 <= i < 8 -> ~ (v <= a - cf_head + i < v + 56)).
{ intros a kk i Hin Hi Hcon.
  destruct (vrs_hb B ly S Hp W mem Lam peak cnt fail ran most own a kk HLED Hin) as (Hk0 & Hab0 & _).
  assert (Hreq : req_size (kk + cf_head) = kk + cf_head)
    by (unfold req_size; destruct (Z.eqb_spec (kk + cf_head) 0); slia).
  destruct Hvat as [(a0 & k0 & Hin0 & Hle0 & Hhi0) | [(b0 & m0 & Hin0 & Hnh & Hle0 & Hhi0) | [(cid & pos' & Hin0 & Hle0 & Hhi0) | Hww]]].
  - destruct (vrs_hb B ly S Hp W mem Lam peak cnt fail ran most own a0 k0 HLED Hin0) as (Hk0' & Hab0' & _).
    assert (Hreq' : req_size (k0 + cf_head) = k0 + cf_head)
      by (unfold req_size; destruct (Z.eqb_spec (k0 + cf_head) 0); slia).
    destruct (Z.eq_dec (a - cf_head) (a0 - cf_head)) as [Heq | Hne].
    + slia.
    + assert (Hpne : (a - cf_head, kk + cf_head) <> (a0 - cf_head, k0 + cf_head))
        by (intros E; injection E as E1 _; exact (Hne E1)).
      pose proof (sep_blocks_x SEGS B ARx LAWS ly S Hp W mem md
        (a - cf_head) (kk + cf_head) (a0 - cf_head) (k0 + cf_head) HARd Hab0 Hab0' Hpne) as Hd.
      unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Hreq, Hreq' in Hd. slia.
  - assert (Hpne : (a - cf_head, kk + cf_head) <> (b0, m0)).
    { intros E; injection E as E1 E2. apply Hnh. replace (b0 + cf_head) with a by slia.
      replace (m0 - cf_head) with kk by slia. exact Hin. }
    pose proof (sep_blocks_x SEGS B ARx LAWS ly S Hp W mem md
      (a - cf_head) (kk + cf_head) b0 m0 HARd Hab0 Hin0 Hpne) as Hd.
    assert (Hreqm : req_size m0 = m0) by (unfold req_size; destruct (Z.eqb_spec m0 0); slia).
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Hreq, Hreqm in Hd. slia.
  - pose proof (sep_block_frame_x SEGS B ARx LAWS ly S Hp W mem md
      (a - cf_head) (kk + cf_head) cid pos' HARd Hab0 Hin0) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Hreq in Hd. slia.
  - exact (Hnowin Hww). }
(* ---- the write premise shared by the two stretches ---- *)
assert (HWR : forall lo hi a, 0 <= lo -> hi <= 56 -> v + lo <= a < v + hi ->
  awr_byte (STK_parse_value d + e) (spZ regs0 + e) (rd_fp q v) (ablocks B ly0 S0) (ablocks B ly S) ly
    [(0, pos)] a \/ wr_fp_frame (rd_fp q v) S0 ly a).
{ intros lo hi a Hlo Hhi Ha.
  assert (HinFP : inFP (rd_fp q v) a)
    by (exists (v, v + 56); split; [right; right; left; reflexivity | cbn [fst snd]; slia]).
  destruct Hplace as [(b0 & n0 & Hin & Hle & Hhi0) | (cid & pos' & Hin & Hle & Hhi0)].
  - left. right. left. split; [exact HinFP|]. exists b0, n0. split; [exact Hin | slia].
  - rewrite Hfrs in Hin. destruct Hin as [Heq | Hin].
    + left. right. right. right. exists 0, pos. split; [left; reflexivity|].
      left. unfold in_zr. cbn [fst snd]. injection Heq as <- <-. slia.
    + right. split; [exact HinFP|]. exists cid, pos'. split; [exact Hin|].
      unfold in_zr, frame_rng. cbn [fst snd]. slia. }
(* ---- the symbolic state at ROW 135 ---- *)
set (E0 := @Eimg _ A_prog_listing PI_prog_A (Ereg regs [])) in *.
assert (HEI : img_env pa_val A_LIM E0) by (unfold E0; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E0 n = ew (Ereg regs []) n)
  by (intros n Hn; unfold E0; apply Eimg_low; exact Hn).
assert (E19 : ew E0 19 = w64 v)
  by (rewrite EL by (unfold A_TEXT; slia); rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl); exact R19).
assert (E23 : ew E0 23 = w64 SHADOW_OFF)
  by (rewrite EL by (unfold A_TEXT; slia); rewrite (ew_Ereg_nat regs _ 23 23%bv eq_refl); exact R23).
assert (U19 : U E0 (SOff 19 0) = v)
  by (rewrite U_SOff, E19; unfold w64; rewrite unsigned_lit_small by slia; rewrite Z.add_0_r;
      apply zcanon_id; unfold M64; slia).
assert (U23 : U E0 (SOff 23 0) = SHADOW_OFF)
  by (rewrite U_SOff, E23; unfold w64, SHADOW_OFF; rewrite unsigned_lit_small by slia; rewrite Z.add_0_r;
      apply zcanon_id; unfold M64; slia).
assert (HS : st_ok_pi SEGS pa_val E0 VrdArm.vrs_ss0
  (restrict (w_H W) (YK11.mkst regs (Z_to_bv 64 (pa_val A_TEXT + VrdArm.vrs_pc0)) mem (YK11.seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute; reflexivity.
  - constructor; [|constructor]. unfold VrdArm.vrs_node, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E19. unfold w64. rewrite unsigned_lit_small by slia.
    split; [slia|]. split; [slia|]. split; [|constructor].
    intros o Ho. apply (proj2 Hvrw). slia.
  - cbn [VrdArm.vrs_node pairwise_disjoint all_disjoint]. exact (conj I I).
  - unfold VrdArm.vrs_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    split; [|split; [exact I | exact I]].
    split; [|split; [|exact I]].
    + unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E19. unfold w64.
      rewrite unsigned_lit_small by slia.
      split; [slia|]. split; [change (2 ^ 3) with 8; exact Hv8 | slia].
    + unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E23. unfold w64, SHADOW_OFF.
      rewrite unsigned_lit_small by slia. split; [slia|]. split; [reflexivity | slia]. }
assert (SHOK : sh_ok SEGS VrdArm.vrs_Bx VrdArm.vrs_SH E0 (mrestrict (w_H W) mem)).
{ unfold sh_ok, VrdArm.vrs_SH. constructor; [|constructor]. unfold shent_ok, VrdArm.vrs_Bx.
  cbn [she_m she_lo she_hi]. rewrite U23, U19. rewrite Z.add_0_r, Z.sub_0_r.
  split; [exact Hvra|].
  unfold app_apart, VrdArm.vrs_Bx. cbn [she_m she_lo she_hi]. rewrite U23, U19.
  intros a Ha. change (Z.min 0 56) with 0 in Ha. change (Z.max 0 56) with 56 in Ha.
  rewrite Z.add_0_r in Ha.
  unfold SHADOW_OFF. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hvmr. slia. }
(* ---- rows 135..141 and the call of row 142 ---- *)
(* the run is at wle and the call concludes SRr' (parse_string's text): the run's post is the rest of the arm as an
   SRr' goal *)
match goal with |- SRr' _ _ ?Wg ?cg ?Qg =>
  eapply (SRrG_bind SEGS (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf) Wg cg
            (fun W' c' => SRr' SEGS YGcfRehidePost.RZ_cf W' c' Qg) Qg);
    [apply SRr_SRr' | intros ? ? _ Hk; exact Hk]
end.
pose (RUN := @paj_run_xf_inv fx rc SK A_prog_listing PL_prog_A PI_prog_A B prh_pst ARx HL LAWS P PLAW).
paj_run_tok_x_inv RUN HS HJ SHOK HPM VrdArm.vrs_Bspan.
- intros a (r & Hin & Hr). cbn [VrdArm.vrs_ss0 ss_mem In] in Hin. destruct Hin as [<- | []].
  cbn [VrdArm.vrs_node YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite E19 in Hr.
  unfold w64 in Hr. rewrite unsigned_lit_small in Hr by slia.
  apply (HWR 0 4 a); slia.
- (* the call of row 142 against the kit's tparse_string_specX *)
  prreg HS (2%bv : bv 5) Q2. prreg HS (1%bv : bv 5) Q1. prreg HS (3%bv : bv 5) Q3.
  prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10.
  assert (EW : forall n (r : bv 5), (n < A_TEXT)%nat -> Z.of_nat n = bv_unsigned r -> ew E0 n = getr regs r)
    by (intros n r Hn Hr; rewrite EL by exact Hn; exact (ew_Ereg_nat regs _ n r Hr)).
  rewrite (EW 2%nat (2%bv : bv 5) ltac:(unfold A_TEXT; slia) eq_refl) in Q2.
  rewrite (EW 3%nat (3%bv : bv 5) ltac:(unfold A_TEXT; slia) eq_refl) in Q3.
  rewrite (EW 4%nat (4%bv : bv 5) ltac:(unfold A_TEXT; slia) eq_refl) in Q4.
  rewrite (EW 8%nat (8%bv : bv 5) ltac:(unfold A_TEXT; slia) eq_refl) in Q8.
  rewrite (EW 20%nat (20%bv : bv 5) ltac:(unfold A_TEXT; slia) eq_refl) in Q10.
  (* the geometry of the dispatch sp *)
  pose proof HJ as HJc.
  pose proof (proj1 HJ) as HARc. cbv beta in HARc.
  destruct HJ as (HARc2 & Hly & _ & Hwle & _ & Hfrs2 & _ & _ & HF1 & HF2 & HF3 & HF4 & _ & HPRESc
    & HSTKOK & HEX & _).
  pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
  destruct HSTKOK as (Hsp16 & HSTKnn & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  destruct Hfwin as (He0 & He16 & Hetop & Hepres).
  assert (Hsp0_16 : spZ regs0 mod 16 = 0) by slia.
  assert (Hm32 : (spZ regs0 - 160) mod 32 = 0 \/ (spZ regs0 - 160) mod 32 = 16) by slia.
  assert (HspR : spZ regs = spZ regs0 - 160 - (spZ regs0 - 160) mod 32).
  { unfold spZ at 1. rewrite Rsp. unfold w64. rewrite unsigned_lit_small by slia. reflexivity. }
  assert (HSTKv : 176 <= STK_parse_value d) by (pose proof VrdArm.vrs_STK_ps_nonneg; slia).
  assert (HspCeil : alloc_ceiling + STK_parse_value d <= spZ regs0) by slia.
  assert (HspLo : spZ regs0 - 176 <= spZ regs <= spZ regs0 - 160) by slia.
  (* rows 135..141 wrote only the node's type word, so every byte outside [v, v + 4) is as it was *)
  assert (HKEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (v <= a < v + 4) ->
    aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem a).
  { intros a Ha Hn. apply (VrdArm.vrs_aview_of_frame W E0 _ mem (ms_mem ms) a HFr); [|exact Ha].
    intros (r & Hin & Hr). cbn [VrdArm.vrs_ss0 ss_mem In] in Hin. destruct Hin as [<- | []].
    cbn [VrdArm.vrs_node YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite E19 in Hr.
    unfold w64 in Hr. rewrite unsigned_lit_small in Hr by slia. slia. }
  assert (HKEEPR : forall a, 0 <= a < 2 ^ 64 -> ~ (v <= a < v + 4) ->
    ms_mem ms (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
  { intros a Ha Hn. apply (VrdArm.vrs_raw_of_frame E0 _ mem (ms_mem ms) a HF); [|exact Ha].
    intros (r & Hin & Hr). cbn [VrdArm.vrs_ss0 ss_mem In] in Hin. destruct Hin as [<- | []].
    cbn [VrdArm.vrs_node YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite E19 in Hr.
    unfold w64 in Hr. rewrite unsigned_lit_small in Hr by slia. slia. }
  (* the node is application memory, so it is apart from every shadow byte *)
  assert (Hvapp : 4096 <= v /\ (v + 56 <= kLowShadowBeg \/ kHighMemBeg <= v)).
  { destruct Hplace as [(b0 & n0 & Hin & Hle & Hhi) | (cid & pos' & Hin & Hle & Hhi)].
    - destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md b0 n0 HARd Hin) as (_ & Hb4096 & _ & Happ & _).
      unfold in_app in Happ. split; [slia|]. destruct Happ as (_ & [HA | [HA HB]]); [left; slia | right; slia].
    - destruct (alx_frames SEGS B ARx LAWS ly S Hp W mem md cid pos' HARd Hin) as (_ & Happ & _).
      unfold in_app in Happ. split; [slia|]. destruct Happ as (_ & [HA | [HA HB]]); [left; slia | right; slia]. }
  assert (HvNS : forall s, SHADOW_OFF <= s < kHighMemBeg -> ~ (v <= s < v + 4))
    by (intros s Hs; unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *; slia).
  (* the shadow byte of any APPLICATION address is inside the shadow band. The bound is STRICT: at x = 2 ^ 47
     exactly (= kHighMemEnd) the shadow byte is kHighMemBeg itself, and amem_range never includes that address. *)
  assert (Hshb : forall x, 0 <= x < 2 ^ 47 -> SHADOW_OFF <= shadow_of_addr SHADOW_OFF x < kHighMemBeg).
  { intros x Hx. unfold shadow_of_addr, SHADOW_OFF, kHighMemBeg.
    change (2 ^ 47) with 140737488355328 in Hx.
    pose proof (Z.div_pos x 8 ltac:(slia) ltac:(slia)).
    pose proof (Z.div_le_mono x 140737488355327 8 ltac:(slia) ltac:(slia)) as Hm.
    change (140737488355327 / 8) with 17592186044415 in Hm. slia. }
  assert (HshK : forall x, 0 <= x < 2 ^ 47 ->
    aview SEGS (w_H W) (ms_mem ms) (shadow_of_addr SHADOW_OFF x) = aview SEGS (w_H W) mem (shadow_of_addr SHADOW_OFF x)).
  { intros x Hx. pose proof (Hshb x Hx) as Hsb. apply HKEEP; [|exact (HvNS _ Hsb)].
    set (s0' := shadow_of_addr SHADOW_OFF x) in *. clearbody s0'. unfold SHADOW_OFF, kHighMemBeg in Hsb. slia. }
  assert (Hs0c : s0Z (ms_regs ms) = spZ regs0)
    by (unfold s0Z; rewrite Q8, R8; unfold w64; rewrite unsigned_lit_small by slia; reflexivity).
  assert (Hspc : spZ (ms_regs ms) = (spZ regs0 + e) + (spZ regs - (spZ regs0 + e)))
    by (unfold spZ; rewrite Q2; slia).
  assert (Hspms : spZ (ms_regs ms) = spZ regs) by slia.
  assert (Ho16 : (spZ regs - (spZ regs0 + e)) mod 16 = 0) by slia.
  assert (Hole : spZ regs - (spZ regs0 + e) <= 0) by slia.
  assert (Hbud2 : STK_parse_string - (spZ regs - (spZ regs0 + e)) <= STK_parse_value d + e) by slia.
  assert (Hoe1 : spZ regs - (spZ regs0 + e) + (spZ regs0 + e - spZ regs) = 0) by slia.
  (* the type word row 140 stored, read off the run's last state before the call *)
  assert (HTY : val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) v 4 4).
  { pose proof (vrs_val_of_st_ok E0 _ ms (w_H W) (Some 19%nat) 0 56 0 4
      [YP09.mkChunk 0 (CVal 4 (SLit 4))] 0 4%N (SLit 4) 4 HS ltac:(cbn [ss_mem setpc]; left; reflexivity)
      ltac:(left; reflexivity) ltac:(reflexivity) ltac:(cbn; slia) ltac:(cbn; slia)) as H0.
    cbn [base_val N.to_nat Pos.to_nat] in H0. rewrite E19 in H0. unfold w64 in H0.
    rewrite (unsigned_lit_small v) in H0 by slia. rewrite Z.add_0_r in H0. exact H0. }
  (* THE CHAINS AT THE CALL: VproC's vrd_disp_chain / vrd_cur_entry_call / vrd_cur_chain_call (vrs_call_chains); at
     the kit's cut the cursor set's prh_cw_ok in the place of prh_cur_ok *)
  pose proof Hsrc as (_ & Htx4 & Htxc & _).
  destruct (vrs_call_chains B CW ly0 ly W0 W mem0 mem (ms_mem ms) regs0 (ms_regs ms) ch e q v p p' text len
      (Z.of_nat d) tb (spZ regs0 + e) (STK_parse_value d + e)
      H_s0ps H_s0pi Hchain_e Hcur HCW Hinok0 Hinok ltac:(slia) ltac:(slia) Hsaved Hra40 Hra0c Hs0c Hepres Hwin HF1
      eq_refl HKEEP HKEEPR Etop ltac:(slia) ltac:(slia) Hsp0_16 Hq1 Hq2 ltac:(slia) Hvceil ltac:(slia) ltac:(slia)
      (pi_frame_nonneg F_parse_string))
    as ((ch2 & Hch2 & _) & HPS3 & HPSCW & HPSLOW).
  (* the read-only view at the call: the node is client memory, so it is not an image byte *)
  assert (Hroimg : forall a, in_roP SEGS pa_relro_lo pa_relro_hi a -> in_img SEGS a).
  { intros a [(s & Hs & _ & Hsb0) | Hr]; [exists s; split; [exact Hs | exact Hsb0]
    | exact (@pa_relro_img _ _ PI_prog_A a Hr)]. }
  assert (HRODc : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) (ms_mem ms))).
  { intros a Hro Hown Herr. pose proof (Hroimg a Hro) as Hi. pose proof (Hsegs a Hi) as Hlow.
    assert (Hna : ~ (v <= a < v + 4)) by (intros Hc0; exact (Hvnimg a ltac:(slia) Hi)).
    rewrite (HKEEP a ltac:(unfold kLowMemEnd in Hlow; slia) Hna).
    exact (HROD a Hro Hown Herr). }
  (* the ledger at the call memory *)
  assert (HLEDc : prh_ledger B ly S Hp W (ms_mem ms) Lam peak cnt fail ran most own).
  { apply ((VrdArm.vrs_ledger_keep B) ly S Hp W mem (ms_mem ms) Lam peak cnt fail ran most own HLED).
    - apply (VrdArm.vrs_pst_keep W mem (ms_mem ms) v (v + 4) HKEEP HPSTi).
      intros a Ha. apply Hvnimg. slia.
    - intros a kk i Hin Hi. apply HKEEP.
      + destruct (vrs_hb B ly S Hp W mem Lam peak cnt fail ran most own a kk HLED Hin) as (Hk0 & Hab0 & _).
        destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md (a - cf_head) (kk + cf_head) HARd Hab0)
          as (_ & Hb4096 & _ & Happ & _).
        assert (Hreq2 : req_size (kk + cf_head) = kk + cf_head)
          by (unfold req_size; pose proof cf_head_nonneg; destruct (Z.eqb_spec (kk + cf_head) 0); slia).
        unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. rewrite Hreq2 in Happ.
        pose proof cf_head_nonneg. slia.
      + intros Hc0. exact (HHEAD a kk i Hin Hi ltac:(slia)). }
  prreg HS (19%bv : bv 5) Q19. prreg HS (23%bv : bv 5) Q23. prreg HS (18%bv : bv 5) Q18.
  prreg HS (26%bv : bv 5) Q26. prreg HS (24%bv : bv 5) Q24. prreg HS (21%bv : bv 5) Q21.
  rewrite (EW 19%nat (19%bv : bv 5) ltac:(unfold A_TEXT; slia) eq_refl) in Q19.
  rewrite (EW 23%nat (23%bv : bv 5) ltac:(unfold A_TEXT; slia) eq_refl) in Q23.
  rewrite (EW 18%nat (18%bv : bv 5) ltac:(unfold A_TEXT; slia) eq_refl) in Q18.
  rewrite (EW 26%nat (26%bv : bv 5) ltac:(unfold A_TEXT; slia) eq_refl) in Q26.
  rewrite (EW 24%nat (24%bv : bv 5) ltac:(unfold A_TEXT; slia) eq_refl) in Q24.
  rewrite (EW 21%nat (21%bv : bv 5) ltac:(unfold A_TEXT; slia) eq_refl) in Q21.
  apply SRr_ret. cbv beta.
  eapply (SRrG_bind SEGS (wle' SEGS YGcfRehidePost.RZ_cf) (wle'_trans SEGS YGcfRehidePost.RZ_cf)).
  { (* parse_string's post is budgeted (fpostWbm at wbudget CW 0) and at wle': the budgeted call rule at wle', the
       caller's journal at the empty budget (ajournal_x is ajournal_xw at [], YCbqG.v) lifted from wle *)
    eapply (vrd_call_Wb_P B ARx SK LAWS P PCALL).
    + exact HS.
    + reflexivity.
    + (* the journal's entry heads are not in its body: name them, so the call rule's own are fixed *)
      apply (ajournal_xwR_mono SEGS B prh_pst ARx (@wle SEGS) (wle' SEGS YGcfRehidePost.RZ_cf)
               (wle_wle' SEGS YGcfRehidePost.RZ_cf) _ _ _ _ _ Hp0).
      exact HJc.
    + exact Hspc.
    + exact Ho16.
    + exact Hole.
    + exact VrdArm.vrs_STK_ps_nonneg.
    + exact Hbud2.
    + exact Hoe1.
    + rewrite Q3, R3. exact Hgp0'.
    + rewrite Q4, R4. exact Htp0'.
    + exact Q1.
    + apply ret_ok_codeptr_v; [slia | reflexivity].
    + pose proof (@pa_B_ok _ _ PI_prog_A) as HBok.
      rewrite unsigned_lit_small by slia. slia.
    + rewrite Hs0c. replace (spZ regs0 + e + (spZ regs - (spZ regs0 + e))) with (spZ (ms_regs ms)) by slia.
      exact Hch2.
    + exact HPM.
    + intros HPRE1. cbn [ss_pc setpc].
      refine (H_parse_string most own ly S Hp W (ms_regs ms) (ms_mem ms) _
                ch2 (spZ regs0 + e - spZ regs) q text len p'
                (Z.of_nat d) tb Lam peak cnt fail ran
                _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
      * split; [exact HPRE1 | split; [exact HRODc | split; [rewrite Hspms; slia|]]].
        (* the return pc of the jal (ROW 143, listing slot 4825) is below the ceiling (VrdArmStr.vrs_ret_slot_ceil) *)
        pose proof vrs_ret_slot_ceil as Hslot.
        pose proof (@pa_B_ok _ _ PI_prog_A) as HBok.
        (* fpre's last conjunct (FRM0-ENTRY, PRH_Base.v blob ee2f5cd7ed35): the rounding mode at the call is the
           dispatch state's, which vrd_disp_body pins at 0 (rows 135..141 run no float instruction) *)
        split; [unfold raZ; rewrite Q1; rewrite unsigned_lit_small by slia; slia | exact HFZ].
      * exact Hclos.
      * exact HPS3.
      * exact HPSLOW.
      * exact HPSCW.
      * rewrite Hspms. slia.
      * exact (proj1 HROOMd).
      * (* the wild budget at the call: the dispatch state is the entry's up to its fake frames (vrd_disp_body's
           `exists f, S = set_fs f S0`), so its depot is the entry's *)
        destruct Hsetfs as (f0 & Ef0). rewrite Ef0. exact HWRd.
      * (* parse_string's live counts at the call: vrd_disp_body's string-arm conjuncts *)
        exact (Hsecs eq_refl).
      * exact (H24s eq_refl).
      * (* parse_string's hull budget: parse_value's entry budget at its all-granted list, which is parse_string's
           (VrdArmStr.vrs_gt_evs); the dispatch state's meters are the entry's, set_fs moving the fake frames only *)
        destruct Hsetfs as (f0 & Ef0). rewrite Ef0, Hsucc, <- (vrs_gt_evs HI_head d _ y Hskip). exact HHB.
      * rewrite Q10, R20. reflexivity.
      * apply (VrdArm.vrs_in_ok_keep W mem (ms_mem ms) q text len p' (Z.of_nat d) tb Hinok).
        -- intros a Ha. apply HKEEP; slia.
        -- intros a Ha. apply HKEEPR; slia.
        -- intros a Ha. destruct Hsrc as (_ & Hs4096 & _ & Hsam & _).
           destruct Hinok as (_ & _ & _ & _ & _ & _ & _ & _ & Hltb & _).
           unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hsam.
           apply HKEEP; slia.
      * exact Hp'lt.
      * exact Hnth.
      * split; [slia|]. split; [slia|]. split.
        -- rewrite Hspms. slia.
        -- intros a Ha. rewrite Hspms in Ha. apply HPRESc. slia.
      * rewrite Hspms. slia.
      * rewrite Hspms. slia.
      * apply (range_addressable_agree (aview SEGS (w_H W) mem) _ SHADOW_OFF q 24); [|exact HRAq].
        intros x Hx. apply HshK. slia.
      * destruct Hsrc as (Hg & Ht1 & Ht2 & Ht3 & Ht4 & Ht5).
        pose proof Ht3 as Ht3u. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Ht3u.
        destruct Hinok as (_ & _ & _ & _ & _ & _ & _ & _ & Hltb & _).
        split; [|split; [exact Ht1 | split; [exact Ht2 | split; [exact Ht3 | split]]]].
        -- apply (VrdArm.vrs_garr8_keep W mem (ms_mem ms) text tb Hg). intros j Hj. apply HKEEP; slia.
        -- apply (range_addressable_agree (aview SEGS (w_H W) mem) _ SHADOW_OFF text (Z.of_nat (length tb)));
             [|exact Ht4].
           intros x Hx. apply HshK. slia.
        -- intros Hpos s Hs. unfold shadow_addr in Hs.
           pose proof (Hshb text ltac:(slia)) as Hs1.
           pose proof (Hshb (text + Z.of_nat (length tb) - 1) ltac:(slia)) as Hs2.
           unfold shadow_of_addr in Hs1, Hs2.
           pose proof (Z.mul_div_le (SHADOW_OFF + text / 8) 8 ltac:(slia)) as Hd1.
           pose proof (Z.mul_div_le (SHADOW_OFF + (text + Z.of_nat (length tb) - 1) / 8) 8 ltac:(slia)) as Hd2.
           pose proof (Z.div_pos text 8 ltac:(slia) ltac:(slia)).
           assert (Hsin : SHADOW_OFF <= s < kHighMemBeg)
             by (clear - Hs1 Hs2 Hd1 Hd2 Hs; unfold SHADOW_OFF, kHighMemBeg in *; slia).
           rewrite HKEEP; [apply Ht5; [exact Hpos | exact Hs]
                          | clear - Hsin; unfold SHADOW_OFF, kHighMemBeg in Hsin; slia
                          | exact (HvNS _ Hsin)].
      * exact Hhome.
      * exact HLEDc.
      * exact HCNT.
      * (* the request bound and the per-event live room of parse_string's all-granted run, from the dispatch
           state's rd_room at the granted value trace (prhPv_gtrace = prhPs_gtrace y here, and prhPs_evs y [] is
           the model's list of that trace, PRH_FnReader.prhPs_evs_model under cf_head = HEAD) *)
        destruct HROOMd as (_ & Hmax & Hlive). rewrite Hgt in Hmax, Hlive.
        split.
        -- intros Q HQ. rewrite Hsucc in HQ.
           pose proof cf_head_nonneg as Hcf0.
           destruct (VrdArm.vrs_gtrace_scan y Q HQ) as [Hg | Hg]; rewrite Hg in Hmax;
             unfold prh_maxreq in Hmax; unfold LIVE_parse_string;
             cbn [map fold_right PjGrammar.esize] in Hmax; slia.
        -- rewrite Hsucc, (prhPs_evs_model y [] HI_head). exact Hlive.
    + intros a Ha. left. destruct Ha as (r & Hin & Hr). cbn [In] in Hin.
      destruct Hin as [<- | []]. cbn [fst snd] in Hr.
      exists (q, q + 8). split; [left; reflexivity | cbn [fst snd]; exact Hr]. }
  (* ======== after the call of row 142: rows 143..151 to the join at ROW 225 ======== *)
  intros W2 c2 Hwle2 (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & WS1 & Hc2 & HWB1 & HJ2 & HJc2 & HWIN2 & HP2 & HQ2
    & HPMc).
  (* P after the call: vrd_call_Wb_P carried it across parse_string's memnorm keep (srr_inv_call) *)
  assert (HPM2 : P mem2) by (rewrite Hc2 in HPMc; exact HPMc).
  clear HPMc.
  (* the pre-call state's symbolic facts are spent: drop them so the arithmetic below runs in a small context *)
  clear HS SHOK HKEEPR HRODc HLEDc HF HFr HG EW HJc HROD HRAq Hsrc Hhome Hroimg HPS3 HPSCW HPSLOW Hch2.
  pose proof (ajxR_ar HJ2) as HAR2.
  (* the layout and the frames at the post state: the callee pushed none *)
  pose proof (ajxR_ly HJc2) as Hly2. pose proof (ajxR_frs HJc2) as Hfrs3.
  assert (Hfa2 : forall cid pos', frame_addr ly2 cid pos' = frame_addr ly cid pos').
  { intros cid pos'.
    exact (proj1 (proj2 (alx_layout SEGS B ARx LAWS ly S Hp W (ms_mem ms) _ ly2 HARc2 Hly2)) cid pos'). }
  (* the registers the second stretch reads, all callee-saved *)
  assert (K19 : getr regs2 19 = w64 v)
    by (rewrite (vrd_kept (ms_regs ms) regs2 19 (19%bv : bv 5) HP2 ltac:(unfold acallee_saved; slia) eq_refl),
        Q19, R19; reflexivity).
  assert (K23 : getr regs2 23 = w64 SHADOW_OFF)
    by (rewrite (vrd_kept (ms_regs ms) regs2 23 (23%bv : bv 5) HP2 ltac:(unfold acallee_saved; slia) eq_refl),
        Q23, R23; reflexivity).
  assert (K18 : getr regs2 18 = w64 (frame_addr ly 0 pos))
    by (rewrite (vrd_kept (ms_regs ms) regs2 18 (18%bv : bv 5) HP2 ltac:(unfold acallee_saved; slia) eq_refl),
        Q18, R18; reflexivity).
  assert (K26 : getr regs2 26 = w64 (frame_addr ly 0 pos))
    by (rewrite (vrd_kept (ms_regs ms) regs2 26 (26%bv : bv 5) HP2 ltac:(unfold acallee_saved; slia) eq_refl),
        Q26, R26; reflexivity).
  assert (K24 : getr regs2 24 = w64 (SHADOW_OFF + frame_addr ly 0 pos / 8))
    by (rewrite (vrd_kept (ms_regs ms) regs2 24 (24%bv : bv 5) HP2 ltac:(unfold acallee_saved; slia) eq_refl),
        Q24, R24; reflexivity).
  assert (K8 : getr regs2 8 = w64 (spZ regs0))
    by (rewrite (vrd_kept (ms_regs ms) regs2 8 (8%bv : bv 5) HP2 ltac:(unfold acallee_saved; slia) eq_refl),
        Q8, R8; reflexivity).
  assert (K3 : getr regs2 3 = getr regs0 3)
    by (rewrite (vrd_kept (ms_regs ms) regs2 3 (3%bv : bv 5) HP2 ltac:(unfold acallee_saved; slia) eq_refl),
        Q3, R3; reflexivity).
  assert (K4 : getr regs2 4 = getr regs0 4)
    by (rewrite (vrd_kept (ms_regs ms) regs2 4 (4%bv : bv 5) HP2 ltac:(unfold acallee_saved; slia) eq_refl),
        Q4, R4; reflexivity).
  (* what the callee's four arms share: the node's block (or frame) is still live, and its hidden head, if it
     has one, is still hidden *)
  destruct HQ2 as (res & Ha0 & HRL2 & HHU2 & HBB2 & HARM). rewrite Hsucc in HARM, HHU2, HBB2.
  assert (HC2 : (forall b n, In (b, n) (ablocks B ly S) -> In (b, n) (ablocks B ly2 S2)) /\
                (forall h, In h Hp -> In h Hp2) /\
                (forall h, In h Hp2 -> In h Hp \/
                   (exists nn, 0 < nn /\ In (h, nn) (ablocks B ly2 S2) /\ ~ In (h, nn) (ablocks B ly S)))).
  { pose proof cf_head_nonneg as Hcf1.
    assert (HKEEPT : Hp2 = Hp -> ablocks B ly2 S2 = ablocks B ly S ->
              (forall b n, In (b, n) (ablocks B ly S) -> In (b, n) (ablocks B ly2 S2)) /\
              (forall h, In h Hp -> In h Hp2) /\
              (forall h, In h Hp2 -> In h Hp \/
                 (exists nn, 0 < nn /\ In (h, nn) (ablocks B ly2 S2) /\ ~ In (h, nn) (ablocks B ly S))))
      by (intros E2 E4; rewrite E2, E4;
          split; [auto | split; [auto | intros h Hh; left; exact Hh]]).
    destruct (PjGrammar.scan y) as [Q|] eqn:Hsc.
    - destruct HARM as [(_ & _ & Heq & Eab & _)
                       |[(_ & _ & Heq & Eab & _)
                       |[(_ & _ & _ & Heq & Eab & _)
                       | (_ & _ & _ & (sv & rv2 & _ & Heq & Eab & _))]]].
      + exact (HKEEPT Heq Eab).
      + exact (HKEEPT Heq Eab).
      + exact (HKEEPT Heq Eab).
      + (* the string arm: one new harness block, appended *)
        assert (Hfresh : ~ In (res - cf_head, Z.of_nat Q + 1 + cf_head) (ablocks B ly S)).
        { intros Hin.
          pose proof ((VrdArm.vrs_sep_last B ARx LAWS) ly2 S2 Hp2 W2 mem2 md2 (ablocks B ly S)
            (res - cf_head, Z.of_nat Q + 1 + cf_head) (res - cf_head) (Z.of_nat Q + 1 + cf_head)
            HAR2 Eab Hin) as Hd.
          unfold zdisjoint, req_size in Hd. cbn [fst snd] in Hd.
          destruct (Z.eqb_spec (Z.of_nat Q + 1 + cf_head) 0); slia. }
        split; [intros b n Hin; rewrite Eab; apply in_or_app; left; exact Hin|].
        split; [intros h Hh; rewrite Heq; right; exact Hh|].
        intros h Hh. rewrite Heq in Hh. destruct Hh as [<- | Hh]; [|left; exact Hh].
        right. exists (Z.of_nat Q + 1 + cf_head).
        split; [slia|]. split; [rewrite Eab; apply in_or_app; right; left; reflexivity | exact Hfresh].
    - destruct HARM as (_ & Heq & Eab & _).
      exact (HKEEPT Heq Eab). }
  destruct HC2 as (HCb & HCh & HCc).
  (* the node is present at the post state *)
  assert (HPRES2 : forall a, v <= a < v + 56 -> apresent (w_H W2) mem2 a).
  { intros a Ha. destruct Hplace as [(b0 & n0 & Hin & Hle & Hhi) | (cid & pos' & Hin & Hle & Hhi)].
    - exact (proj1 (proj1 (proj2 (proj2 (proj2 (proj2 (alx_blocks SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2
        b0 n0 HAR2 (HCb b0 n0 Hin)))))) a ltac:(slia))).
    - rewrite <- (Hfa2 cid pos') in Hle, Hhi.
      exact (proj1 (proj1 (proj2 (proj2 (alx_frames SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 cid pos' HAR2
        ltac:(rewrite Hfrs3; cbn [app]; exact Hin)))) a ltac:(slia))). }
  (* the node's shadow at the post state *)
  assert (HRAc : range_addressable (aview SEGS (w_H W) (ms_mem ms)) SHADOW_OFF v 56).
  { apply (range_addressable_agree (aview SEGS (w_H W) mem) _ SHADOW_OFF v 56); [|exact Hvra].
    intros x Hx. apply HshK. slia. }
  assert (HRA2 : range_addressable (aview SEGS (w_H W2) mem2) SHADOW_OFF v 56).
  { pose proof cf_head_nonneg as Hcf2.
    destruct Hvat as [(a0 & k0 & Hin0 & Hle0 & Hhi0) | [(b0 & m0 & Hin0 & Hnh & Hle0 & Hhi0)
                     | [(cid & pos' & Hin0 & Hle0 & Hhi0) | Hww]]].
    - (* a live HARNESS block: AR_laws_x's field 14 at the instance's head length *)
      destruct (vrs_hb B ly S Hp W mem Lam peak cnt fail ran most own a0 k0 HLED Hin0) as (Hk0' & Hab0' & Hhp0').
      assert (Hreq' : req_size (k0 + cf_head) = k0 + cf_head)
        by (unfold req_size; destruct (Z.eqb_spec (k0 + cf_head) 0); slia).
      destruct (alx_hshadow SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 (a0 - cf_head) (k0 + cf_head) HAR2
                 (HCb _ _ Hab0') (HCh _ Hhp0')) as (Hbs & _).
      rewrite HLcf, Hreq' in Hbs.
      replace (a0 - cf_head + cf_head) with a0 in Hbs by slia.
      replace (k0 + cf_head - cf_head) with k0 in Hbs by slia.
      eapply block_shadow_range; [exact Hbs | slia | slia].
    - (* a live block that hides no harness head: AR_laws_x's field 11 *)
      assert (Hreqm : req_size m0 = m0) by (unfold req_size; destruct (Z.eqb_spec m0 0); slia).
      assert (Hnohead : forall h, In h Hp2 -> ~ (b0 <= h < b0 + req_size m0)).
      { intros h Hh Hcon. destruct (HCc h Hh) as [Hold | (nn & Hnn0 & Hinn & Hnin)].
        - pose proof (Permutation_in h (vrs_heads B ly S Hp W mem Lam peak cnt fail ran most own HLED) Hold) as Hmap.
          apply in_map_iff in Hmap as ((a1 & kk1) & Hfst & Hin1). cbn [fst] in Hfst.
          destruct (vrs_hb B ly S Hp W mem Lam peak cnt fail ran most own a1 kk1 HLED Hin1) as (Hk1 & Hab1 & _).
          assert (Hreq1 : req_size (kk1 + cf_head) = kk1 + cf_head)
            by (unfold req_size; destruct (Z.eqb_spec (kk1 + cf_head) 0); slia).
          pose proof ((VrdArm.vrs_blocks_eq B ARx LAWS) ly S Hp W mem md (a1 - cf_head) (kk1 + cf_head) b0 m0 h HARd
            Hab1 Hin0 ltac:(slia) ltac:(slia)) as Heq1.
          injection Heq1 as E1 E2. apply Hnh.
          replace (b0 + cf_head) with a1 by slia. replace (m0 - cf_head) with kk1 by slia. exact Hin1.
        - pose proof ((VrdArm.vrs_blocks_eq B ARx LAWS) ly2 S2 Hp2 W2 mem2 md2 h nn b0 m0 h HAR2 Hinn (HCb _ _ Hin0)
            ltac:(unfold req_size; destruct (Z.eqb_spec nn 0); slia) ltac:(slia)) as Heq2.
          injection Heq2 as E1 E2. apply Hnin. rewrite E1, E2. exact Hin0. }
      destruct (alx_shadow SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 b0 m0 HAR2 (HCb _ _ Hin0) Hnohead)
        as (Hbs & _).
      rewrite Hreqm in Hbs. eapply block_shadow_range; [exact Hbs | slia | slia].
    - (* a live FAKE FRAME: the callee's journal keeps the frame's shadow bytes *)
      pose proof (ajxR_frm HJc2) as HF4c.
      destruct (alx_frames SEGS B ARx LAWS ly S Hp W (ms_mem ms) _ cid pos' HARc2 Hin0) as (Hf32 & _ & _ & _).
      apply (range_addressable_agree (aview SEGS (w_H W) (ms_mem ms)) _ SHADOW_OFF v 56); [|exact HRAc].
      intros x Hx.
      assert (Hcid : 0 <= cid) by (apply VrdArm.vrs_cid_nonneg; slia).
      assert (Hxlt : 0 <= x < 2 ^ 47)
        by (clear - Hx Hvmr Hv4096; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hvmr; slia).
      pose proof (Hshb x Hxlt) as Hsb.
      apply (HF4c cid pos' (shadow_of_addr SHADOW_OFF x) Hin0).
      + right. unfold in_zr, shadow_addr, shadow_of_addr. cbn [fst snd].
        pose proof (VrdArm.vrs_frame_shadow_in (frame_addr ly cid pos') (fs_frame_bytes cid) x
          ltac:(slia) ltac:(apply VrdArm.vrs_fsb_mod8; exact Hcid) ltac:(apply fs_frame_bytes_nonneg) ltac:(slia)) as HIN.
        exact HIN.
      + intros (rr & Hinr & Hrr). cbn [In] in Hinr. destruct Hinr as [<- | []].
        cbn [fst snd] in Hrr. clear - Hrr Hsb Hq1 Hceil Hslo HSTKv.
        pose proof asan_consts as (AC & _ & _ & _ & _).
        assert (HSO : SHADOW_OFF = 2147450880) by reflexivity.
        assert (HKB : kHighMemBeg = 17594333495296) by reflexivity. slia.
    - exfalso. exact (Hnowin Hww). }
  (* ---- the symbolic state at ROW 143. Rows 143..151 run at wle (below), so the goal is lifted from SRr ---- *)
  apply (SRr_SRr' SEGS YGcfRehidePost.RZ_cf).
  rewrite Hc2.
  match goal with |- SRr _ _ (mkCfg (YK11.mkst _ ?pcw _ _) _) _ =>
    change pcw with (Z_to_bv 64 (pa_val A_TEXT + VrdArm.vrs_pc1)) end.
  set (E1 := @Eimg _ A_prog_listing PI_prog_A (Ereg regs2 [])) in *.
  assert (HEI1 : img_env pa_val A_LIM E1) by (unfold E1; apply Eimg_env).
  assert (EL1 : forall n, (n < A_TEXT)%nat -> ew E1 n = ew (Ereg regs2 []) n)
    by (intros n Hn; unfold E1; apply Eimg_low; exact Hn).
  assert (F19 : ew E1 19 = w64 v)
    by (rewrite EL1 by (unfold A_TEXT; slia); rewrite (ew_Ereg_nat regs2 _ 19 19%bv eq_refl); exact K19).
  assert (F23 : ew E1 23 = w64 SHADOW_OFF)
    by (rewrite EL1 by (unfold A_TEXT; slia); rewrite (ew_Ereg_nat regs2 _ 23 23%bv eq_refl); exact K23).
  assert (V19 : U E1 (SOff 19 0) = v)
    by (rewrite U_SOff, F19; unfold w64; rewrite unsigned_lit_small by slia; rewrite Z.add_0_r;
        apply zcanon_id; unfold M64; slia).
  assert (V23 : U E1 (SOff 23 0) = SHADOW_OFF)
    by (rewrite U_SOff, F23; unfold w64, SHADOW_OFF; rewrite unsigned_lit_small by slia; rewrite Z.add_0_r;
        apply zcanon_id; unfold M64; slia).
  assert (HS1 : st_ok_pi SEGS pa_val E1 VrdArm.vrs_ss1
    (restrict (w_H W2) (YK11.mkst regs2 (Z_to_bv 64 (pa_val A_TEXT + VrdArm.vrs_pc1)) mem2 (YK11.seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
    - apply regs_ok_Eimg_Ereg.
    - vm_compute; reflexivity.
    - constructor; [|constructor]. unfold VrdArm.vrs_node, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite F19. unfold w64. rewrite unsigned_lit_small by slia.
      split; [slia|]. split; [slia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply HPRES2. slia.
    - cbn [VrdArm.vrs_node pairwise_disjoint all_disjoint]. exact (conj I I).
    - unfold VrdArm.vrs_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
      split; [|split; [exact I | exact I]].
      split; [|split; [|exact I]].
      + unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite F19. unfold w64.
        rewrite unsigned_lit_small by slia.
        split; [slia|]. split; [change (2 ^ 3) with 8; exact Hv8 | slia].
      + unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite F23. unfold w64, SHADOW_OFF.
        rewrite unsigned_lit_small by slia. split; [slia|]. split; [reflexivity | slia]. }
  assert (SHOK1 : sh_ok SEGS VrdArm.vrs_Bx VrdArm.vrs_SH E1 (mrestrict (w_H W2) mem2)).
  { unfold sh_ok, VrdArm.vrs_SH. constructor; [|constructor]. unfold shent_ok, VrdArm.vrs_Bx.
    cbn [she_m she_lo she_hi]. rewrite V23, V19. rewrite Z.add_0_r, Z.sub_0_r.
    split; [exact HRA2|].
    unfold app_apart, VrdArm.vrs_Bx. cbn [she_m she_lo she_hi]. rewrite V23, V19.
    intros a Ha. change (Z.min 0 56) with 0 in Ha. change (Z.max 0 56) with 56 in Ha.
    rewrite Z.add_0_r in Ha.
    clear - Ha Hvmr. unfold SHADOW_OFF. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hvmr. slia. }
  (* ---- the run of rows 143..151 to the join at ROW 225. They make no allocator call. They run on a journal that
     STARTS at parse_string's post state (the identity journal at wle, the empty budget), so the run is the engine's
     wle runner; at the join that journal is composed after the journal from parse_value's entry (at wle', by
     ajournal_xw_subR), whose budget it leaves as it is ---- *)
  assert (HJid : ajournal_x (SK := SK) SEGS B prh_pst ARx (STK_parse_value d + e) (spZ regs0 + e) (rd_fp q v)
            ly2 S2 Hp2 W2 mem2 md2 [] ly2 S2 Hp2 W2 mem2 md2 0).
  { pose proof (ajxR_stk HJ2) as Hstk02. pose proof (ajxR_ly HJ2) as Hly02.
    eapply ajx_intro.
    - exact (ajxR_ar HJ2).
    - apply layout_le_refl.
    - apply le_n.
    - apply wle_refl.
    - apply aos_step_refl.
    - reflexivity.
    - slia.
    - slia.
    - intros; reflexivity.
    - intros; reflexivity.
    - intros; reflexivity.
    - intros; reflexivity.
    - intros pp nn i H1 H2. exfalso. exact (H2 H1).
    - exact (ajxR_pres HJ2).
    - destruct Hly02 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop2 & Eslo2 & Eshi2 & _).
      unfold astk_ok, ly_bot in Hstk02 |- *. rewrite Etop2, Eslo2, Eshi2. exact Hstk02.
    - intros; reflexivity.
    - exact (ajxR_qt HJ2).
    - apply incl_appl, incl_refl. }
  (* the write premise of the second stretch, against the identity journal: the node's str field is in a live block
     of the post state, or in a live fake frame of it that the footprint names *)
  assert (HWR2 : forall a, v + 16 <= a < v + 24 ->
    awr_byte (STK_parse_value d + e) (spZ regs0 + e) (rd_fp q v) (ablocks B ly2 S2) (ablocks B ly2 S2) ly2 [] a \/
    wr_fp_frame (rd_fp q v) S2 ly2 a).
  { intros a Ha.
    assert (HinFP : inFP (rd_fp q v) a)
      by (exists (v, v + 56); split; [right; right; left; reflexivity | cbn [fst snd]; slia]).
    destruct Hplace as [(b0 & n0 & Hin & Hle & Hhi) | (cid & pos' & Hin & Hle & Hhi)].
    - left. right. left. split; [exact HinFP|]. exists b0, n0. split; [exact (HCb b0 n0 Hin) | slia].
    - right. split; [exact HinFP|]. exists cid, pos'. split; [rewrite Hfrs3; exact Hin|].
      unfold in_zr, frame_rng. cbn [fst snd]. rewrite Hfa2. slia. }
  pose (RUNTO := @paj_run_to_xf_inv fx rc SK A_prog_listing PL_prog_A PI_prog_A B prh_pst ARx HL LAWS P PLAW).
  paj_run_to_tok_x_inv RUNTO HS1 HJid SHOK1 HPM2 VrdArm.vrs_Bspan VrdArm.vrs_pc2.
  + intros a (r & Hin & Hr). cbn [VrdArm.vrs_ss1 ss_mem In] in Hin. destruct Hin as [<- | []].
    cbn [VrdArm.vrs_node YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite F19 in Hr.
    unfold w64 in Hr. rewrite unsigned_lit_small in Hr by slia.
    apply HWR2. slia.
  + (* ---- the state at the join, ROW 225 ---- *)
    pmkst HS1.
    prreg HS1 (8%bv : bv 5) P8. prreg HS1 (18%bv : bv 5) P18. prreg HS1 (26%bv : bv 5) P26.
    prreg HS1 (24%bv : bv 5) P24. prreg HS1 (21%bv : bv 5) P21. prreg HS1 (3%bv : bv 5) P3.
    prreg HS1 (4%bv : bv 5) P4.
    assert (EW1 : forall n (r : bv 5), (n < A_TEXT)%nat -> Z.of_nat n = bv_unsigned r ->
              ew E1 n = getr regs2 r)
      by (intros n r Hn Hr; rewrite EL1 by exact Hn; exact (ew_Ereg_nat regs2 _ n r Hr)).
    rewrite (EW1 8%nat (8%bv : bv 5) ltac:(unfold A_TEXT; slia) eq_refl) in P8.
    rewrite (EW1 18%nat (18%bv : bv 5) ltac:(unfold A_TEXT; slia) eq_refl) in P18.
    rewrite (EW1 26%nat (26%bv : bv 5) ltac:(unfold A_TEXT; slia) eq_refl) in P26.
    rewrite (EW1 24%nat (24%bv : bv 5) ltac:(unfold A_TEXT; slia) eq_refl) in P24.
    rewrite (EW1 3%nat (3%bv : bv 5) ltac:(unfold A_TEXT; slia) eq_refl) in P3.
    rewrite (EW1 4%nat (4%bv : bv 5) ltac:(unfold A_TEXT; slia) eq_refl) in P4.
    rewrite K8 in P8. rewrite K18 in P18. rewrite K26 in P26. rewrite K24 in P24. rewrite K3 in P3. rewrite K4 in P4.
    assert (F10 : ew E1 10 = w64 res)
      by (rewrite EL1 by (unfold A_TEXT; slia); rewrite (ew_Ereg_nat regs2 _ 10 10%bv eq_refl); exact Ha0).
    rewrite F10 in P21.
    (* the join memory against parse_string's post memory: rows 143..151 write the str field [v + 16, v + 24) *)
    assert (KR2 : forall a, 0 <= a < 2 ^ 64 -> ~ (v + 16 <= a < v + 24) ->
                    aview SEGS (w_H W2) (ms_mem ms0) a = aview SEGS (w_H W2) mem2 a).
    { intros a Ha Hn. apply (VrdArm.vrs_aview_of_frame W2 E1 _ mem2 (ms_mem ms0) a HFr); [|exact Ha].
      intros (r & Hin & Hr). cbn [VrdArm.vrs_ss1 ss_mem In] in Hin. destruct Hin as [<- | []].
      cbn [VrdArm.vrs_node YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite F19 in Hr.
      unfold w64 in Hr. rewrite unsigned_lit_small in Hr by slia. slia. }
    assert (KR2r : forall a, 0 <= a < 2 ^ 64 -> ~ (v + 16 <= a < v + 24) ->
                     ms_mem ms0 (Z_to_bv 64 a) = mem2 (Z_to_bv 64 a)).
    { intros a Ha Hn. apply (VrdArm.vrs_raw_of_frame E1 _ mem2 (ms_mem ms0) a HF); [|exact Ha].
      intros (r & Hin & Hr). cbn [VrdArm.vrs_ss1 ss_mem In] in Hin. destruct Hin as [<- | []].
      cbn [VrdArm.vrs_node YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite F19 in Hr.
      unfold w64 in Hr. rewrite unsigned_lit_small in Hr by slia. slia. }
    (* the str field row 148 stored: the final state's chunk at v + 16 holds a0 = the returned block *)
    assert (V10 : sv_denot E1 (SOff 10 0) = Z_to_bv 64 (bv_unsigned (w64 res))).
    { rewrite Z_to_bv_bv_unsigned. apply bv_eq.
      change (bv_unsigned (sv_denot E1 (SOff 10 0))) with (YP0e.U E1 (SOff 10 0)).
      rewrite U_SOff, F10, Z.add_0_r. apply zcanon_id.
      pose proof (bv_unsigned_in_range 64 (w64 res)) as Hr. unfold M64. change (bv_modulus 64) with (2 ^ 64) in Hr. slia. }
    assert (HstrF : val_mem SEGS (mrestrict (w_H W2) (ms_mem ms0)) (v + 16) 8 (bv_unsigned (w64 res))).
    { pose proof (bv_unsigned_in_range 64 (w64 res)) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
      pose proof (vrd_val_of_st E1 _ ms0 (w_H W2) (Some 19%nat) 0 56 16 24
        [YP09.mkChunk 16 (CVal 8 (SOff 10 0))] 16 8%N (SOff 10 0) (bv_unsigned (w64 res)) HS1
        ltac:(cbn [ss_mem]; left; reflexivity) ltac:(left; reflexivity) V10 ltac:(cbn; slia) ltac:(cbn; slia)) as H0.
      cbn [base_val N.to_nat Pos.to_nat] in H0. rewrite F19 in H0. unfold w64 in H0.
      rewrite (unsigned_lit_small v) in H0 by slia. exact H0. }
    assert (HrwF : rd_rw SEGS (mrestrict (w_H W2) (ms_mem ms0)) v 56).
    { intros x Hx. apply (writable_at_grows SEGS _ _ x HG). apply (apresent_writable SEGS). apply HPRES2. slia. }
    pose proof (vrs_arms_weak B ly S Hp W ly2 S2 Hp2 W2 mem2 q text len p' (Z.of_nat d) tb Lam peak cnt fail ran most
      own res y HARM) as HARMw.
    (* the join journal from parse_value's entry: the journal to parse_string's post (wle', budget [] ++ WS1) and the
       stretch's journal after it (wle, lifted to wle'), composed at wle'; the stretch adds no budget *)
    pose proof (ajournal_xwR_mono SEGS B prh_pst ARx (@wle SEGS) (wle' SEGS YGcfRehidePost.RZ_cf)
      (wle_wle' SEGS YGcfRehidePost.RZ_cf) _ _ _ _ _ Hp2 _ _ _ _ _ _ _ _ _ _ _ _ HJid) as HJidR.
    pose proof (ajournal_xw_subR SEGS B prh_pst ARx LAWS pa_segs_low (wle' SEGS YGcfRehidePost.RZ_cf)
      (wle'_trans SEGS YGcfRehidePost.RZ_cf) _ _ _ _ _ Hp0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      HJ2 HJidR ltac:(slia) ltac:(slia) (fun a Ha => or_introl Ha)) as HJF.
    assert (HWB : YCbqGwild.wbudget CW 0 (([] ++ WS1) ++ [])) by (rewrite app_nil_r; exact HWB1).
    apply SRr_ret.
    split; [|exact HPM2].
    exists fx, pos, (if res =? 0 then -1 else 0).
    replace (pa_val A_TEXT + 19628) with (pa_sigma AS_parse_value + PV_EPI) by (vm_compute; reflexivity).
    apply (vrs_join B ARx SK LAWS d HI_head ly0 S0 Hp0 W0 regs0 mem0 md0 e q v text len p tb Lam peak cnt fail ran most own
      pos y p' ly S Hp W mem (ms_mem ms) md _ _ _
      (spZ regs0 + e + (spZ regs - (spZ regs0 + e))) ly2 S2 Hp2 W2 mem2 md2 k1 (ms_regs ms0) (ms_mem ms0) _ _ res
      CW (([] ++ WS1) ++ []) WS1
      Hcfw HPSTi HdM Hskip Hsucc ltac:(slia) ltac:(slia) Hp'lt Hlentb
      HARd Hfrs Hab Hsetfs HLED HCNT Hplace HHEAD Hvnimg Hv8 Hv4096 Hvceil Hqv Htv' Hq1 Hq2 ltac:(slia) He0 ltac:(slia)
      Hvzero Hvra Hwin Hframe Hsaved HRAok0 HFZ HmaxR HKEEP HTY
      HJc2 ltac:(slia) HWIN2 HRL2 HHU2 HBB2 HARMw HCb
      HJF HWB KR2 KR2r HstrF HrwF P8 P18 P26 P24 P21 P3 P4).
Qed.

(* THE ARM at P := fun _ => True *)
Lemma vrd_str_a_ok :
  (* the instance facts and the boundaries this arm carries, each named in the report *)
  HL = cf_head -> 8 <= cf_head ->
  (forall a, Exists (in_zr a) prh_pst -> in_img SEGS a) ->
  pi_s0cur F_parse_string = Some 0 -> pi_s0cur F_parse_items = Some 0 ->
  forall ly0 S0 Hp0 W0 regs0 mem0 md0 ch e q v text len p (tb : list Z)
    (Lam : list (Z * Z)) peak cnt fail ran most own W c y,
  fpre B ARx (STK_parse_value d) ly0 S0 Hp0 W0 regs0 mem0 md0 ch ->
  vrd_disp_a B ARx SK ly0 S0 Hp0 W0 regs0 mem0 md0 ch CTX0 CW e q v text len p d tb Lam peak cnt fail ran most own
    W c ->
  PresetHullBudget.hull_budget S0 (PresetReqAt.rd_hevs (prhPv_gtrace d (rest_atR tb text p))) ->
  PjGrammar.skip (rest_atR tb text p) = 34 :: y ->
  STK_parse_string + 176 <= STK_parse_value d ->
  SRr' SEGS YGcfRehidePost.RZ_cf W c (fun W' c' => exists (fx2 : YK11.FPState) (pos rv : Z),
    vrd_epi_aR (fx := fx) B ARx SK (wle' SEGS YGcfRehidePost.RZ_cf) fx2 d CW e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos rv
      (vrd_pv_post B d e q v text len p tb ly0 S0 Lam peak cnt fail ran most own pos rv) W' c').
Proof.
intros HLcf Hcfw HPSTi H_s0ps H_s0pi ly0 S0 Hp0 W0 regs0 mem0 md0 ch e q v text len p tb Lam peak cnt fail ran
  most own W c y HPRE HD HHB Hskip HBUD.
eapply (SRrG_mono SEGS (wle' SEGS YGcfRehidePost.RZ_cf)).
{ exact (vrd_str_a_okP (fun _ => True) vrs_inv_laws_true vrs_inv_call_true HLcf Hcfw HPSTi H_s0ps H_s0pi
    ly0 S0 Hp0 W0 regs0 mem0 md0 ch e q v text len p tb Lam peak cnt fail ran most own W c y
    HPRE HD HHB Hskip HBUD I). }
intros W' c' _ (H & _). exact H.
Qed.

End str.

(* the axiom audit of this lane's top lemmas, in the build log of record *)
Print Assumptions vrd_str_a_okP.
Print Assumptions vrd_str_a_ok.
Print Assumptions VrdArm.vrd_call_W.
Print Assumptions VrdArm.vrd_call_WF.
Print Assumptions VrdArm.vrd_call_W_P.
Print Assumptions VrdArm.vrd_call_WF_P.
Print Assumptions VrdArm.vrd_call_Wb_P.
Print Assumptions VrdArm.vrd_call_WFb_P.
Print Assumptions VrdArmStr.vrs_join.
Print Assumptions VrdArmStr.vrs_rq.
