(* reac_served_mark (fuzz_link.asan 0x895a8) on image A: the glue the segment files of its walk share.
   Every lemma is stated over lib/A/Prog/reac_served_markDefs.v's cut interface.
   - the stack pointers (srm_sp_facts, srm_base_sp) and the frame F (srm_F_facts);
   - the contract's write set srm_E: g_nl's request ring or one of the two heap blocks (srm_E_cases), application
     memory below the allocator's ceiling (srm_E_app), and never F, its shadow or its flag byte (srm_E_noside,
     srm_blk_noside);
   - the kept clause and the views at a cut: srm_kept_noside (the base's akept without the taken frame's bytes),
     srm_view_kept (an `akb` byte of the entry outside X has the entry's view), srm_name_view, srm_gtab_view,
     srm_table_view, srm_gsay_at;
   - an own callee called from inside F: srm_call_apre (its apre at the call), srm_call_back (the cut base after its
     apost, at the fx' it returns), srm_akb_entry / srm_akb_frame / srm_akb_img (its read-set bytes);
   - the uniqueness of the views the Post quantifies over (acstr_at_unique, anlk_at_unique, aiftab_at_unique,
     astr_arg_unique, amarks_at_unique), generic in the segments.
   The entry Pre's facts restated at a cut for a callee window (srm_name_at, srm_table_at, srm_policy_at, ...) are in
   lib/A/Prog/reac_served_markKitAt.v.
   Models: lib/A/Prog/LinkWalkSide.v akept_drop_side / apost_side_gen (the frame's bytes), LinkWalkCall.v ajw_mono /
   ajw_frame (copied in proof only while that file waits for the narrowed akb),
   reac_link_alias_readPost.v (the uniqueness lemmas), libreac/fuzz_boxreg BoxTailVis.v (origin/ossv/recipes).

   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AMemFile AB1v AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit LinkWalkSide PcapRelro.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
model_decide_c remember_c reac_code_emit_c reac_served_mark_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import reac_served_markDefs reac_served_markUniq.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* a byte of F's two buffers, kind[32] at F + 0x20 and alias[256] at F + 0x60 *)
Section bf. Context {rc : YM05.RunCeil} {PI : PAImg link_listing}.
Definition srm_bufb (cx : srmcx) (fpos a : Z) : Prop :=
  srm_kind cx fpos <= a < srm_kind cx fpos + KIND_CAP \/ srm_alias cx fpos <= a < srm_alias cx fpos + ALIAS_MAX.
End bf.

(* image A's segments, as booleans over tfibsegs (lib/A/AB1v.v) and the runtime's statics (lib/A/AF0m.v) *)
Definition srm_img_b (lo hi : Z) : bool :=
  existsb (fun s => (Z.of_N (seg_base s) <=? lo) && (hi <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) tfibsegs.
Definition srm_nostatic_b (lo hi : Z) : bool :=
  forallb (fun r : Z * Z => (hi <=? fst r) || (fst r + snd r <=? lo)) Tfib_owned_static.

Lemma srm_img_of_b : forall lo hi a, srm_img_b lo hi = true -> lo <= a < hi -> in_img tfibsegs a.
Proof.
  intros lo hi a H Ha. unfold srm_img_b in H. apply existsb_exists in H as (s & Hs & Hc).
  apply andb_true_iff in Hc as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  exists s. split; [exact Hs | lia].
Qed.

Lemma srm_nostatic_of_b : forall lo hi a, srm_nostatic_b lo hi = true -> lo <= a < hi ->
  ~ Exists (in_zr a) Tfib_owned_static.
Proof.
  intros lo hi a H Ha Hex. unfold srm_nostatic_b in H. rewrite forallb_forall in H.
  apply Exists_exists in Hex as (r & Hr & Hz). specialize (H r Hr). unfold in_zr in Hz.
  apply orb_true_iff in H as [H | H]; apply Z.leb_le in H; lia.
Qed.

Lemma srm_gnl_img_b : srm_img_b LA_G_NL (LA_G_NL + NK_SIZE) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma srm_gnl_nostatic_b : srm_nostatic_b LA_G_NL (LA_G_NL + NK_SIZE) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma srm_gsay_img_b : srm_img_b LA_G_SAY (LA_G_SAY + 8) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma srm_gsay_nostatic_b : srm_nostatic_b LA_G_SAY (LA_G_SAY + 8) = true.
Proof. vm_compute. reflexivity. Qed.

(* eight bytes read as a word are the same when the eight views are *)
Lemma srm_rdword_ext : forall (rd rd' : reader) a,
  (forall x, a <= x < a + 8 -> rd' x = rd x) -> rdword rd' a = rdword rd a.
Proof.
  intros rd rd' a H. unfold rdword.
  rewrite (H a), (H (a + 1)), (H (a + 2)), (H (a + 3)), (H (a + 4)), (H (a + 5)), (H (a + 6)), (H (a + 7))
    by lia.
  reflexivity.
Qed.

Section k. Context {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
#[local] Notation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TB : PcapSyms B.
Hypothesis RELRO_IMG : forall a, PCAP_RLO <= a < PCAP_RHI -> in_img SEGS a.
Hypothesis HSEGS : SEGS = tfibsegs.

Ltac srm_unpre H :=
  unfold srm_pre in H; destruct H as (HA & Prd & HP);
  destruct HA as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14);
  destruct HP as (pkbs & ptab & pnm & pk & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14
                  & P15 & P16).

Ltac srm_unbase H :=
  unfold srm_base in H; cbv zeta in H;
  destruct H as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12 & B13 & B14 & B15 & B16 & B17 & B18
                 & B19 & B20 & B21 & B22 & B23 & B24 & B25 & B26 & B27 & B28 & B29 & B30 & B31 & B32 & B33).

Lemma srm_pow : 2 ^ 47 = 140737488355328 /\ 2 ^ 64 = 18446744073709551616.
Proof. split; reflexivity. Qed.

Lemma srm_segs_low : forall a, in_img SEGS a -> 0 <= a < kLowMemEnd.
Proof. exact pa_segs_low. Qed.

(* what a journal says of its current layout: F's base, the stack row, and AR *)
Lemma srm_aj_ly : forall G XO OUT STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k,
  ajournal_gx SEGS B G XO OUT STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k ->
  ly_F ly' = ly_F ly /\ ly_stk_lo ly' = ly_stk_lo ly /\ ly_stk_hi ly' = ly_stk_hi ly /\
  AR SEGS B ly' S' W' mem' md'.
Proof.
  intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k (_ & _ & (memS & HJ & _) & _).
  destruct HJ as (HAR & Hly & _). destruct Hly as (_ & _ & _ & _ & _ & EF & _ & _ & _ & Elo & Ehi & _).
  split; [exact EF|]. split; [exact Elo|]. split; [exact Ehi | exact HAR].
Qed.

Lemma srm_sp_facts : forall cx, srm_pre SK B cx ->
  srm_sp cx mod 16 = 0 /\ alloc_ceiling + REAC_SERVED_MARK_AK <= srm_sp cx /\ srm_sp cx <= 2 ^ 47 /\
  srm_sp cx - 144 <= srm_sp1 cx <= srm_sp cx - 128 /\ srm_sp1 cx mod 32 = 0.
Proof using LAWS TB RELRO_IMG HSEGS.
  intros cx Hpre. srm_unpre Hpre.
  pose proof A1 as HR. eapply ajournal_gx_row in HR. destruct HR as (R1 & R2 & R3 & R4).
  pose proof A1 as (H0 & HXO & _).
  pose proof REAC_SERVED_MARK_AK_val as HK.
  unfold srm_sp1, srm_sp, SRM_FRAME in *. lia.
Qed.

Lemma srm_lyeq : forall fx cx fpos X ly3 S3 W3 (ms3 : machine_state) md3,
  srm_pre SK B cx -> srm_base fx SK B cx fpos X ly3 S3 W3 ms3 md3 ->
  (forall c q, frame_addr ly3 c q = frame_addr (sm_lyc cx) c q) /\
  (forall c q, flag_addr ly3 c q = flag_addr (sm_lyc cx) c q) /\
  ly_stk_lo ly3 = ly_stk_lo (sm_lyc cx) /\ ly_stk_hi ly3 = ly_stk_hi (sm_lyc cx) /\
  AR SEGS B ly3 S3 W3 (ms_mem ms3) md3.
Proof using LAWS TB RELRO_IMG HSEGS.
  intros fx cx fpos X ly3 S3 W3 ms3 md3 Hpre Hb. srm_unpre Hpre. srm_unbase Hb.
  destruct (srm_aj_ly _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A1) as (F1 & L1 & H1 & _).
  destruct (srm_aj_ly _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ B6) as (F3 & L3 & H3 & HAR3).
  split; [intros c q; unfold frame_addr; rewrite F1, F3; reflexivity|].
  split; [intros c q; unfold flag_addr; rewrite F1, F3; reflexivity|].
  split; [congruence|]. split; [congruence | exact HAR3].
Qed.

Lemma srm_base_sp : forall fx cx fpos X ly3 S3 W3 (ms3 : machine_state) md3,
  srm_pre SK B cx -> srm_base fx SK B cx fpos X ly3 S3 W3 ms3 md3 -> spZ (ms_regs ms3) = srm_sp1 cx.
Proof using LAWS TB RELRO_IMG HSEGS.
  intros fx cx fpos X ly3 S3 W3 ms3 md3 Hpre Hb.
  pose proof (srm_sp_facts cx Hpre) as (Q1 & Q2 & Q3 & Q4 & Q5).
  pose proof asan_consts as ((C1a & C1b) & _). pose proof srm_pow as (P47 & P64).
  pose proof REAC_SERVED_MARK_AK_val as HK.
  srm_unbase Hb. unfold spZ. rewrite B12. unfold w64. apply unsigned_lit_small. lia.
Qed.

Lemma srm_F_facts : forall fx cx fpos X ly3 S3 W3 (ms3 : machine_state) md3,
  srm_pre SK B cx -> srm_base fx SK B cx fpos X ly3 S3 W3 ms3 md3 ->
  4096 <= srm_F cx fpos /\ srm_F cx fpos + SRM_FB <= alloc_ceiling /\ srm_F cx fpos mod 64 = 0 /\
  in_app (srm_F cx fpos) SRM_FB /\ (forall a, srm_F cx fpos <= a < srm_F cx fpos + SRM_FB -> ~ in_img SEGS a) /\
  In (SRM_CID, fpos) (frames S3) /\ frame_addr ly3 SRM_CID fpos = srm_F cx fpos /\
  flag_addr ly3 SRM_CID fpos = srm_FL cx fpos /\
  (forall c q, frame_addr ly3 c q = frame_addr (sm_lyc cx) c q) /\
  ly_stk_lo ly3 = ly_stk_lo (sm_lyc cx) /\ ly_stk_hi ly3 = ly_stk_hi (sm_lyc cx).
Proof using LAWS TB RELRO_IMG HSEGS.
  intros fx cx fpos X ly3 S3 W3 ms3 md3 Hpre Hb.
  destruct (srm_lyeq fx cx fpos X ly3 S3 W3 ms3 md3 Hpre Hb) as (Hfa & Hfl & Hlo & Hhi & HAR3).
  srm_unbase Hb. destruct B11 as (S1 & W1 & mem1 & md1 & HAR1 & Hfrs1 & Eab1).
  assert (Hin1 : In (SRM_CID, fpos) (frames S1)) by (rewrite Hfrs1; left; reflexivity).
  destruct (frames_bounds SEGS B LAWS (sm_lyc cx) S1 W1 mem1 md1 SRM_CID fpos HAR1 Hin1) as (Hf4 & Hfc & Happ).
  pose proof HAR1 as [M _].
  destruct (frame_facts B (sm_lyc cx) S1 _ SRM_CID fpos M Hin1)
    as (_ & _ & _ & _ & Hpg & _ & _ & Hoff & _ & _ & _).
  rewrite SRM_FB_val in Hfc, Happ.
  split; [exact Hf4|]. split; [exact Hfc|].
  split.
  { unfold srm_F, frame_addr, page_aligned in *. rewrite Z.add_mod, Hoff, Z.add_0_r, Z.mod_mod by lia.
    replace (ly_F (sm_lyc cx)) with (64 * (ly_F (sm_lyc cx) / 4096 * 64))
      by (pose proof (Z.div_mod (ly_F (sm_lyc cx)) 4096 ltac:(lia)); lia).
    rewrite Z.mul_comm. apply Z_mod_mult. }
  split; [exact Happ|].
  split.
  { intros a Ha. apply (frm_img SEGS B LAWS (sm_lyc cx) S1 W1 mem1 md1 SRM_CID fpos a HAR1 Hin1).
    rewrite SRM_FB_val. exact Ha. }
  split; [rewrite B7; left; reflexivity|].
  split; [exact (Hfa SRM_CID fpos)|]. split; [exact (Hfl SRM_CID fpos)|].
  split; [exact Hfa|]. split; [exact Hlo | exact Hhi].
Qed.

(* ---- the write set ---- *)
Lemma srm_E_cases : forall cx a, srm_pre SK B cx -> srm_E cx a ->
  (LA_G_NL <= a < LA_G_NL + NK_N_SENT + 4) \/
  (exists b m, In (b, m) (ablocks B (sm_lyc cx) (sm_Sc cx)) /\ b <= a < b + req_size m /\
     ((b = srm_mk cx /\ srm_mk cx <> 0 /\ m = MK_SIZE) \/ (b = sm_sink cx /\ m = AMF_BLOCK))).
Proof using LAWS TB RELRO_IMG HSEGS.
  intros cx a Hpre HE. srm_unpre Hpre.
  unfold srm_E, srm_wr, reac_served_mark_awr in HE.
  destruct HE as (r & Hin & Hr). cbn [In] in Hin.
  destruct Hin as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hr.
  - left. exact Hr.
  - right. unfold aivl in Hr. cbn [fst snd] in Hr.
    assert (E0 : aarg (sm_regs cx) 0 <> 0).
    { intros E0. rewrite E0 in Hr. cbn in Hr. lia. }
    rewrite (proj2 (Z.eqb_neq _ _) E0) in Hr. change (if false then 0 else MK_SIZE) with MK_SIZE in Hr.
    destruct (P2 E0) as (Hl & _). exists (srm_mk cx), MK_SIZE.
    assert (Rq : req_size MK_SIZE = MK_SIZE) by reflexivity.
    split; [exact Hl|]. split; [rewrite Rq; unfold srm_mk; lia|].
    left. split; [reflexivity|]. split; [exact E0 | reflexivity].
  - right. unfold aivl in Hr. cbn [fst snd] in Hr.
    assert (E0 : sm_sink cx <> 0) by exact P10.
    rewrite (proj2 (Z.eqb_neq _ _) E0) in Hr. change (if false then 0 else AMF_BLOCK) with AMF_BLOCK in Hr.
    exists (sm_sink cx), AMF_BLOCK.
    assert (Rq : req_size AMF_BLOCK = AMF_BLOCK) by reflexivity.
    split; [exact P1|]. split; [rewrite Rq; lia|].
    right. split; reflexivity.
Qed.

Lemma srm_E_app : forall cx a, srm_pre SK B cx -> srm_E cx a ->
  4096 <= a < alloc_ceiling /\ (a < kLowMemEnd \/ kHighMemBeg <= a).
Proof using LAWS TB RELRO_IMG HSEGS.
  intros cx a Hpre HE. pose proof Hpre as Hpre'. srm_unpre Hpre'.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  destruct (srm_E_cases cx a Hpre HE) as [Hg | (b & m & Hb & Hr & _)].
  - unfold LA_G_NL, NK_N_SENT, kHighMemBeg, kLowMemEnd in *. lia.
  - destruct (srm_aj_ly _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A1) as (_ & _ & _ & HAR).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hb) as (_ & H4096 & Hbc & Hbapp & _).
    pose proof (in_app_addr _ _ a Hbapp ltac:(lia)) as Hap. unfold app_addr in Hap.
    unfold kLowShadowBeg, ASAN_CEIL, kHighMemBeg, kLowMemEnd in *. lia.
Qed.

Lemma srm_blk_noside : forall fx cx fpos X ly3 S3 W3 (ms3 : machine_state) md3 b m a,
  srm_base fx SK B cx fpos X ly3 S3 W3 ms3 md3 ->
  In (b, m) (ablocks B (sm_lyc cx) (sm_Sc cx)) -> b <= a < b + req_size m ->
  ~ aside_rng (sm_lyc cx) SRM_CID fpos a.
Proof using LAWS TB RELRO_IMG HSEGS.
  intros fx cx fpos X ly3 S3 W3 ms3 md3 b m a Hb Hbm Ha. srm_unbase Hb.
  destruct B11 as (S1 & W1 & mem1 & md1 & HAR1 & Hfrs1 & Eab1).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  set (lyc := sm_lyc cx) in *.
  assert (Hin1 : In (SRM_CID, fpos) (frames S1)) by (rewrite Hfrs1; left; reflexivity).
  assert (Hb1 : In (b, m) (ablocks B lyc S1)) by (rewrite Eab1; exact Hbm).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR1 Hb1) as (_ & H4096 & Hbc & Hbapp & Hpo & _ & _).
  destruct (frames_bounds SEGS B LAWS lyc S1 W1 mem1 md1 SRM_CID fpos HAR1 Hin1) as (Hf4 & Hfc & _).
  destruct (al_flag _ _ LAWS lyc S1 W1 mem1 md1 SRM_CID fpos HAR1 Hin1) as (_ & Hfo & _ & _).
  pose proof (fs_frame_bytes_nonneg SRM_CID) as Hnn.
  pose proof (shadow_addr_bounds (frame_addr lyc SRM_CID fpos) ltac:(lia)) as Hsb1.
  pose proof (shadow_addr_bounds (frame_addr lyc SRM_CID fpos + fs_frame_bytes SRM_CID) ltac:(lia)) as Hsb2.
  pose proof (shadow_range_end (frame_addr lyc SRM_CID fpos) (fs_frame_bytes SRM_CID) Hnn) as Hse.
  intros [Hr | [Hr | Hr]].
  - pose proof (sep_block_frame SEGS B LAWS lyc S1 W1 mem1 md1 b m SRM_CID fpos HAR1 Hb1 Hin1) as Hd.
    unfold zdisjoint, in_zr, frame_rng in Hd, Hr. cbn [fst snd] in Hd, Hr. lia.
  - pose proof (in_app_addr _ _ a Hbapp ltac:(lia)) as Hap. unfold app_addr in Hap.
    unfold in_zr in Hr. cbn [fst snd] in Hr. unfold kLowShadowBeg, ASAN_CEIL in Hap. lia.
  - exact (proj2 (Hpo a ltac:(lia)) (eq_ind_r (fun x => aowned B lyc S1 x) Hfo Hr)).
Qed.

Lemma srm_E_noside : forall fx cx fpos X ly3 S3 W3 (ms3 : machine_state) md3 a,
  srm_pre SK B cx -> srm_base fx SK B cx fpos X ly3 S3 W3 ms3 md3 -> srm_E cx a ->
  ~ aside_rng (sm_lyc cx) SRM_CID fpos a.
Proof using LAWS TB RELRO_IMG HSEGS.
  intros fx cx fpos X ly3 S3 W3 ms3 md3 a Hpre Hb HE.
  destruct (srm_E_cases cx a Hpre HE) as [Hg | (b & m & Hbm & Hr & _)].
  - pose proof Hb as Hb'. srm_unbase Hb'. destruct B11 as (S1 & W1 & mem1 & md1 & HAR1 & Hfrs1 & Eab1).
    assert (Hin1 : In (SRM_CID, fpos) (frames S1)) by (rewrite Hfrs1; left; reflexivity).
    assert (Hlow := srm_segs_low).
    intros Hs.
    assert (Hlo : a < alloc_ceiling /\ ~ in_img SEGS a) by (eapply aside_rng_low; eassumption).
    apply (proj2 Hlo). rewrite HSEGS. apply (srm_img_of_b LA_G_NL (LA_G_NL + NK_SIZE) a srm_gnl_img_b).
    unfold NK_N_SENT, NK_SIZE in *. lia.
  - exact (srm_blk_noside fx cx fpos X ly3 S3 W3 ms3 md3 b m a Hb Hbm Hr).
Qed.

(* ---- the kept clause and the views at a cut ---- *)
Lemma srm_kept_noside : forall fx cx fpos X ly3 S3 W3 (ms3 : machine_state) md3,
  srm_base fx SK B cx fpos X ly3 S3 W3 ms3 md3 ->
  akept SEGS B (sm_lyc cx) (sm_Sc cx) (sm_W cx) (sm_memc cx) W3 (ms_mem ms3)
    (srm_sp cx - REAC_SERVED_MARK_AK) (srm_sp cx) X.
Proof using LAWS TB RELRO_IMG HSEGS.
  intros fx cx fpos X ly3 S3 W3 ms3 md3 Hb. srm_unbase Hb.
  destruct B11 as (S1 & W1 & mem1 & md1 & HAR1 & Hfrs1 & Eab1).
  assert (Hlow := srm_segs_low).
  eapply akept_drop_side; eassumption.
Qed.

Lemma srm_view_kept : forall fx cx fpos X ly3 S3 W3 (ms3 : machine_state) md3 a,
  srm_pre SK B cx -> srm_base fx SK B cx fpos X ly3 S3 W3 ms3 md3 ->
  akb SEGS B (sm_lyc cx) (sm_Sc cx) (srm_sp cx - REAC_SERVED_MARK_AK) (srm_sp cx) a -> ~ X a ->
  aview SEGS (w_H W3) (ms_mem ms3) a = aview SEGS (w_H (sm_W cx)) (sm_memc cx) a.
Proof using LAWS TB RELRO_IMG HSEGS.
  intros fx cx fpos X ly3 S3 W3 ms3 md3 a Hpre Hb Hakb HnX.
  pose proof (srm_kept_noside fx cx fpos X ly3 S3 W3 ms3 md3 Hb) as HK.
  srm_unpre Hpre.
  eapply akept_akb_gx; [eassumption ..].
Qed.

(* an image byte outside the statics and errno, outside g_nl's request ring, is not in X *)
Lemma srm_img_notX : forall cx (X : Z -> Prop) a, srm_pre SK B cx -> (forall a, X a -> srm_E cx a) ->
  in_img SEGS a -> ~ (LA_G_NL <= a < LA_G_NL + NK_N_SENT + 4) -> ~ X a.
Proof using LAWS TB RELRO_IMG HSEGS.
  intros cx X a Hpre HX Hi Hg HXa. pose proof Hpre as Hpre'. srm_unpre Hpre'.
  destruct (srm_E_cases cx a Hpre (HX a HXa)) as [Hg' | (b & m & Hbm & Hr & _)]; [exact (Hg Hg')|].
  destruct (srm_aj_ly _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A1) as (_ & _ & _ & HAR).
  exact (blk_img SEGS B LAWS _ _ _ _ _ b m a HAR Hbm Hr Hi).
Qed.

Lemma srm_gtab_view : forall fx cx fpos X ly3 S3 W3 (ms3 : machine_state) md3 a,
  srm_pre SK B cx -> srm_base fx SK B cx fpos X ly3 S3 W3 ms3 md3 -> (forall a, X a -> srm_E cx a) ->
  LA_G_NL + NK_IF_NAME <= a < LA_G_NL + NK_SIZE ->
  aview SEGS (w_H W3) (ms_mem ms3) a = aview SEGS (w_H (sm_W cx)) (sm_memc cx) a.
Proof using LAWS TB RELRO_IMG HSEGS.
  intros fx cx fpos X ly3 S3 W3 ms3 md3 a Hpre Hb HX Ha.
  assert (Eown : as_owned_static B = Tfib_owned_static) by (destruct TB; assumption).
  assert (Hi : in_img SEGS a).
  { rewrite HSEGS. apply (srm_img_of_b LA_G_NL (LA_G_NL + NK_SIZE) a srm_gnl_img_b).
    unfold NK_IF_NAME, NK_SIZE in *. lia. }
  pose proof Hpre as Hpre'. srm_unpre Hpre'.
  destruct P4 as (_ & _ & _ & _ & Hegnl & _).
  apply (srm_view_kept fx cx fpos X ly3 S3 W3 ms3 md3 a Hpre Hb).
  - right; right; left. split; [exact Hi|]. split.
    + rewrite Eown. apply (srm_nostatic_of_b LA_G_NL (LA_G_NL + NK_SIZE) a srm_gnl_nostatic_b).
      unfold NK_IF_NAME, NK_SIZE in *. lia.
    + unfold apart_gnl in Hegnl. unfold NK_IF_NAME, NK_SIZE in *. lia.
  - apply (srm_img_notX cx X a Hpre HX Hi). unfold NK_IF_NAME, NK_N_SENT in *. lia.
Qed.

(* the read set at the entry: the name's bytes and NUL, a live table string's bytes and NUL *)
Lemma srm_name_akb : forall cx s a, srm_pre SK B cx ->
  astr_arg SEGS (srm_m0 cx) (srm_name cx) (Some s) -> srm_name cx <= a <= srm_name cx + Z.of_nat (length s) ->
  akb SEGS B (sm_lyc cx) (sm_Sc cx) (srm_sp cx - REAC_SERVED_MARK_AK) (srm_sp cx) a.
Proof using LAWS TB RELRO_IMG HSEGS.
  intros cx s a Hpre Hs Ha. destruct (srm_gspan_of_pre SK B cx Hpre) as (Hgn & _).
  exact (Hgn s a Hs Ha).
Qed.

Lemma srm_name_view : forall fx cx fpos X ly3 S3 W3 (ms3 : machine_state) md3 s a,
  srm_pre SK B cx -> srm_base fx SK B cx fpos X ly3 S3 W3 ms3 md3 -> (forall a, X a -> srm_E cx a) ->
  astr_arg SEGS (srm_m0 cx) (srm_name cx) (Some s) -> srm_name cx <= a <= srm_name cx + Z.of_nat (length s) ->
  aview SEGS (w_H W3) (ms_mem ms3) a = aview SEGS (w_H (sm_W cx)) (sm_memc cx) a.
Proof using LAWS TB RELRO_IMG HSEGS.
  intros fx cx fpos X ly3 S3 W3 ms3 md3 s a Hpre Hb HX Hs Ha.
  apply (srm_view_kept fx cx fpos X ly3 S3 W3 ms3 md3 a Hpre Hb (srm_name_akb cx s a Hpre Hs Ha)).
  intros HXa. pose proof Hpre as Hpre'. srm_unpre Hpre'.
  assert (Enm : pnm = Some s) by exact (astr_arg_unique SEGS _ _ _ _ P14 Hs).
  destruct (P15 s Enm) as (_ & _ & Hg & Hf & _ & Hm).
  destruct (srm_E_cases cx a Hpre (HX a HXa)) as [Hr | (b & m & _ & Hr & [(-> & Hmk & ->) | (-> & ->)])].
  - unfold apart_gnl in Hg. unfold srm_name in *. unfold NK_N_SENT, NK_SIZE in *. lia.
  - specialize (Hm Hmk). unfold apart in Hm. assert (Rq : req_size MK_SIZE = MK_SIZE) by reflexivity.
    rewrite Rq in Hr. unfold srm_name, srm_mk in *. lia.
  - unfold apart in Hf. assert (Rq : req_size AMF_BLOCK = AMF_BLOCK) by reflexivity.
    rewrite Rq in Hr. unfold srm_name in *. lia.
Qed.

Lemma srm_table_view : forall fx cx fpos X ly3 S3 W3 (ms3 : machine_state) md3 kbs tab i n2 ix p a,
  srm_pre SK B cx -> srm_base fx SK B cx fpos X ly3 S3 W3 ms3 md3 -> (forall a, X a -> srm_E cx a) ->
  amk_nlk_ok SEGS (srm_m0 cx) kbs tab 2 -> nth_error tab i = Some (n2, ix) ->
  au64_at SEGS (rdW W3 (ms_mem ms3)) (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p -> 0 <= p < 2 ^ 64 ->
  p <= a <= p + Z.of_nat (length n2) ->
  aview SEGS (w_H W3) (ms_mem ms3) a = aview SEGS (w_H (sm_W cx)) (sm_memc cx) a.
Proof using LAWS TB RELRO_IMG HSEGS.
  intros fx cx fpos X ly3 S3 W3 ms3 md3 kbs tab i n2 ix p a Hpre Hb HX Hnlk Hnth Hau Hp Ha.
  pose proof Hpre as Hpre'. srm_unpre Hpre'.
  destruct Hnlk as (Hn1 & _ & _ & _ & _ & Htab & _).
  destruct P3 as (Hp1 & _ & _ & _ & _ & Hptab & _).
  pose proof (anlk_at_unique SEGS _ _ _ _ Hn1 Hp1) as Ek. subst pkbs.
  pose proof (aiftab_at_unique SEGS _ _ _ _ Htab Hptab) as Et. subst ptab.
  pose proof Htab as (_ & Hlen & Hent).
  assert (Hi : (i < length tab)%nat) by (apply nth_error_Some; congruence).
  (* the cell is the entry's *)
  assert (Hau0 : au64_at SEGS (srm_m0 cx) (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p).
  { unfold srm_m0. apply (srm_val_mem_move SEGS (w_H W3) (w_H (sm_W cx)) (ms_mem ms3) (sm_memc cx)); [|exact Hau].
    intros x Hx. change (Z.of_nat 8) with 8 in Hx. symmetry.
    apply (srm_gtab_view fx cx fpos X ly3 S3 W3 ms3 md3 x Hpre Hb HX).
    unfold NK_IF_NAME, NK_SIZE in *. lia. }
  destruct (Hent i n2 ix Hnth) as (_ & p' & Hp' & Hp'0 & Hc' & _).
  pose proof (srm_au64_unique SEGS _ _ _ _ Hp' Hau0) as Ep.
  pose proof (srm_acstr_range SEGS _ _ _ Hc') as Hr'.
  rewrite !Z.mod_small in Ep by lia. subst p'.
  destruct (P7 i n2 ix p Hnth Hau0 Hp) as (_ & Hg & _ & Hf & Hm).
  apply (srm_view_kept fx cx fpos X ly3 S3 W3 ms3 md3 a Hpre Hb).
  - destruct (srm_gspan_of_pre SK B cx Hpre) as (_ & Hgt).
    exact (Hgt kbs tab i n2 ix p a Hn1 Htab Hnth Hau0 Hc' Ha).
  - intros HXa.
    destruct (srm_E_cases cx a Hpre (HX a HXa)) as [Hr | (b & m & _ & Hr & [(-> & Hmk & ->) | (-> & ->)])].
    + unfold apart_gnl in Hg. unfold NK_N_SENT, NK_SIZE in *. lia.
    + specialize (Hm Hmk). unfold apart in Hm. assert (Rq : req_size MK_SIZE = MK_SIZE) by reflexivity.
      rewrite Rq in Hr. unfold srm_mk in *. lia.
    + unfold apart in Hf. assert (Rq : req_size AMF_BLOCK = AMF_BLOCK) by reflexivity.
      rewrite Rq in Hr. lia.
Qed.

Lemma srm_gsay_at : forall fx cx fpos X ly3 S3 W3 (ms3 : machine_state) md3,
  srm_pre SK B cx -> srm_base fx SK B cx fpos X ly3 S3 W3 ms3 md3 -> (forall a, X a -> srm_E cx a) ->
  au64_at SEGS (rdW W3 (ms_mem ms3)) LA_G_SAY (sm_sink cx) /\
  4096 <= sm_sink cx /\ sm_sink cx + AMF_BLOCK <= alloc_ceiling /\ sm_sink cx < 2 ^ 64.
Proof using LAWS TB RELRO_IMG HSEGS.
  intros fx cx fpos X ly3 S3 W3 ms3 md3 Hpre Hb HX.
  assert (Eown : as_owned_static B = Tfib_owned_static) by (destruct TB; assumption).
  pose proof Hpre as Hpre'. srm_unpre Hpre'.
  destruct (srm_aj_ly _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A1) as (_ & _ & _ & HAR).
  split.
  - unfold srm_m0 in P9.
    apply (srm_val_mem_move SEGS (w_H (sm_W cx)) (w_H W3) (sm_memc cx) (ms_mem ms3)); [|exact P9].
    intros x Hx. change (Z.of_nat 8) with 8 in Hx.
    assert (Hi : in_img SEGS x).
    { rewrite HSEGS. apply (srm_img_of_b LA_G_SAY (LA_G_SAY + 8) x srm_gsay_img_b). lia. }
    apply (srm_view_kept fx cx fpos X ly3 S3 W3 ms3 md3 x Hpre Hb).
    + right; right; left. split; [exact Hi|]. split.
      * rewrite Eown. apply (srm_nostatic_of_b LA_G_SAY (LA_G_SAY + 8) x srm_gsay_nostatic_b). lia.
      * unfold apart in P5. lia.
    + apply (srm_img_notX cx X x Hpre HX Hi). unfold LA_G_SAY, LA_G_NL, NK_N_SENT in *. lia.
  - destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR P1) as (_ & H4096 & Hbc & _).
    assert (Rq : req_size AMF_BLOCK = AMF_BLOCK) by reflexivity. rewrite Rq in Hbc.
    pose proof (srm_sp_facts cx Hpre) as (Q1 & Q2 & Q3 & _). pose proof srm_pow as (P47 & P64).
    pose proof REAC_SERVED_MARK_AK_val as HK.
    split; [exact H4096|]. split; [exact Hbc|]. rewrite P64. rewrite P47 in Q3. unfold AMF_BLOCK in Hbc. lia.
Qed.

(* ---- an own callee ---- *)
Lemma srm_call_apre : forall fx cx fpos X ly3 S3 W3 (ms3 : machine_state) md3 (Kc : Z) (SIDEc Wrc : list (Z * Z)),
  srm_pre SK B cx -> srm_base fx SK B cx fpos X ly3 S3 W3 ms3 md3 -> (forall a, X a -> srm_E cx a) ->
  0 <= Kc <= REAC_CODE_EMIT_AK ->
  YK0s.ret_ok (getr (ms_regs ms3) 1) -> 4096 <= raZ (ms_regs ms3) ->
  (forall cd, In cd SIDEc -> exists d, In (fst cd, d) REAC_SERVED_MARK_ASIDE /\
     snd cd + (if SRM_CID =? fst cd then 1 else 0) <= d) ->
  (forall a, inFP Wrc a -> srm_E cx a \/ srm_bufb cx fpos a) ->
  apre SK SEGS PCAP_RLO PCAP_RHI B Kc 0 SIDEc Wrc (sm_G cx) (sm_XO cx) (sm_OUT cx) (sm_STK cx) (sm_sp0 cx)
    (sm_FP cx) (sm_ly cx) (sm_S cx) (sm_W0 cx) (sm_mem0 cx) (sm_md0 cx) ((SRM_CID, fpos) :: sm_own cx)
    ly3 S3 W3 (ms_mem ms3) md3 (sm_k cx) (ms_regs ms3).
Proof using LAWS TB RELRO_IMG HSEGS.
  intros fx cx fpos X ly3 S3 W3 ms3 md3 Kc SIDEc Wrc Hpre Hb HX HKc Hret Hra Hside Hwr.
  pose proof (srm_sp_facts cx Hpre) as (Q1 & Q2 & Q3 & Q4 & Q5). unfold srm_sp in Q1, Q2, Q3, Q4.
  pose proof (srm_base_sp fx cx fpos X ly3 S3 W3 ms3 md3 Hpre Hb) as Hsp.
  destruct (srm_F_facts fx cx fpos X ly3 S3 W3 ms3 md3 Hpre Hb)
    as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & Hfa & Hlo & Hhi).
  pose proof Hpre as Hpre'. srm_unpre Hpre'. pose proof Hb as Hb'. srm_unbase Hb'.
  pose proof A1 as (H0 & HXO & _).
  pose proof A1 as HR. eapply ajournal_gx_row in HR. destruct HR as (R1 & R2 & R3 & R4).
  destruct (srm_aj_ly _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ B6) as (_ & _ & _ & HAR3).
  pose proof REAC_SERVED_MARK_AK_val as HK.
  assert (HKe : REAC_SERVED_MARK_AK = 144 + REAC_CODE_EMIT_AK) by reflexivity.
  assert (Hbl : forall b n, In (b, n) (ablocks B (sm_lyc cx) (sm_Sc cx)) -> In (b, n) (ablocks B ly3 S3)).
  { intros b n Hbn. eapply Permutation_in; [apply Permutation_sym; exact B10 | exact Hbn]. }
  assert (Hbuf : forall a, srm_bufb cx fpos a ->
    frame_addr ly3 SRM_CID fpos <= a < frame_addr ly3 SRM_CID fpos + fs_frame_bytes SRM_CID).
  { intros a Ha. rewrite F7, SRM_FB_val.
    unfold srm_bufb, srm_kind, srm_alias, SRM_KIND, SRM_ALIAS, KIND_CAP, ALIAS_MAX, SRM_FB in *. lia. }
  unfold apre.
  split; [exact B6|]. split; [exact A2|]. split; [exact B32|].
  split; [exact Hret|]. split; [exact Hra|].
  split; [rewrite B21; exact A6|]. split; [rewrite B22; exact A7|].
  split; [rewrite Hsp; lia|]. split; [rewrite Hsp; lia|]. split; [rewrite Hsp; lia|].
  split; [exact A11|].
  split.
  { apply (aside_room_push (sm_Sc cx) S3 REAC_SERVED_MARK_ASIDE SIDEc SRM_CID fpos B7 A12).
    intros c' d' Hin. destruct (Hside (c', d') Hin) as (d & Hd & Hle). exists d. split; [exact Hd | exact Hle]. }
  split.
  { intros a Ha. destruct (Hwr a Ha) as [HE | HB].
    - destruct (A13 a HE) as [(Haw & Hno) | [HGa | Hout]];
        [left | right; left; exact HGa | right; right; exact Hout].
      split; [|exact Hno].
      destruct Haw as [Hs | [(Hf & b & n & Hin & Hr) | [(b & n & Hin & Hn0 & Hr) | (c & q & Hin & Hr)]]].
      + left. exact Hs.
      + right; left. split; [exact Hf|]. exists b, n. split; [exact (Hbl b n Hin) | exact Hr].
      + right; right; left. exists b, n. split; [exact (Hbl b n Hin)|]. split; [exact Hn0 | exact Hr].
      + right; right; right. exists c, q. split; [right; exact Hin|]. rewrite !Hfa. exact Hr.
    - left. split.
      + right; right; right. exists SRM_CID, fpos. split; [left; reflexivity|].
        left. unfold in_zr. cbn [fst snd]. exact (Hbuf a HB).
      + intros Hw. pose proof (Hbuf a HB) as Hr. rewrite F7, SRM_FB_val in Hr. lia. }
  { intros a Ha. destruct (Hwr a Ha) as [HE | HB].
    - exact (A14 a HE).
    - apply (not_ro_off_img SEGS PCAP_RLO PCAP_RHI a RELRO_IMG).
      exact (frm_img SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 SRM_CID fpos a HAR3 F6 (Hbuf a HB)). }
Qed.

Lemma srm_call_back : forall (fx fx' : YK11.FPState) cx fpos X ly3 S3 W3 (ms3 : machine_state) md3
    (Kc : Z) (Ec : Z -> Prop) (P : bvmap 5 word -> (word -> option byte) -> Prop) (W4 : world SEGS) (c4 : config),
  srm_pre SK B cx -> srm_base fx SK B cx fpos X ly3 S3 W3 ms3 md3 -> (forall a, X a -> srm_E cx a) ->
  @BoxBase.fxr fx fx' -> 0 <= Kc <= REAC_CODE_EMIT_AK ->
  (forall a, Ec a -> srm_E cx a \/ srm_bufb cx fpos a) ->
  apost (fx := fx') SK SEGS B Kc 0 Ec (sm_G cx) (sm_XO cx) (sm_OUT cx) (sm_STK cx) (sm_sp0 cx) (sm_FP cx)
    (sm_ly cx) (sm_S cx) (sm_W0 cx) (sm_mem0 cx) (sm_md0 cx) ((SRM_CID, fpos) :: sm_own cx)
    ly3 S3 W3 (ms_mem ms3) md3 (sm_k cx) (ms_regs ms3)
    (fun ly2 S2 W2 regs2 mem2 md2 => S2 = set_fs (st_fs S2) S3 /\
       Permutation (ablocks B ly2 S2) (ablocks B ly3 S3) /\ P regs2 (rdW W2 mem2)) W4 c4 ->
  exists ly4 S4 regs4 mem4 md4,
    c4 = mkCfg (@mkst fx' regs4 (getr (ms_regs ms3) 1) mem4 (seg_rom SEGS)) md4 /\
    srm_base fx' SK B cx fpos (srm_E cx) ly4 S4 W4 (@mkst fx' regs4 (getr (ms_regs ms3) 1) mem4 (seg_rom SEGS)) md4 /\
    aregs_preserved (ms_regs ms3) regs4 /\
    akept SEGS B ly3 S3 W3 (ms_mem ms3) W4 mem4 (spZ (ms_regs ms3) - Kc) (spZ (ms_regs ms3)) Ec /\
    P regs4 (rdW W4 mem4).
Proof using LAWS TB RELRO_IMG HSEGS.
  intros fx fx' cx fpos X ly3 S3 W3 ms3 md3 Kc Ec P W4 c4 Hpre Hb HX Hfx HKc HEc Hpost.
  pose proof (srm_sp_facts cx Hpre) as (Q1 & Q2 & Q3 & Q4 & Q5).
  pose proof (srm_base_sp fx cx fpos X ly3 S3 W3 ms3 md3 Hpre Hb) as Hsp.
  destruct (srm_F_facts fx cx fpos X ly3 S3 W3 ms3 md3 Hpre Hb)
    as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & Hfa & Hlo & Hhi).
  pose proof Hpre as Hpre'. srm_unpre Hpre'. pose proof Hb as Hb'. srm_unbase Hb'.
  pose proof asan_consts as ((C1a & C1b) & _). pose proof srm_pow as (P47 & P64).
  pose proof REAC_SERVED_MARK_AK_val as HK.
  assert (HKe : REAC_SERVED_MARK_AK = 144 + REAC_CODE_EMIT_AK) by reflexivity.
  destruct Hpost as (ly4 & S4 & regs4 & mem4 & md4 & Hc4 & HJ4 & Hpres & Hfr4 & Hfds & Hfs & HKc4 & Hsh4
                     & HS4 & Hperm4 & HP).
  rewrite Z.add_0_r in HJ4.
  destruct (srm_aj_ly _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A1) as (Fc & _ & _ & HARc).
  destruct (srm_aj_ly _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ4) as (Fq & _ & _ & HAR4).
  assert (HEc_lo : forall a, Ec a -> a < alloc_ceiling).
  { intros a Ha. destruct (HEc a Ha) as [HE | HB].
    - exact (proj2 (proj1 (srm_E_app cx a Hpre HE))).
    - unfold srm_bufb, srm_kind, srm_alias, SRM_KIND, SRM_ALIAS, KIND_CAP, ALIAS_MAX, SRM_FB in *. lia. }
  assert (Hkeep_hi : forall a, srm_sp cx - 96 <= a < srm_sp cx ->
    aview SEGS (w_H W4) mem4 a = aview SEGS (w_H W3) (ms_mem ms3) a).
  { intros a Ha. destruct HKc4 as (K1 & _). apply K1; [lia | rewrite Hsp; lia|].
    intros HEa. pose proof (HEc_lo a HEa). lia. }
  assert (Hkeep_fl : forall a, srm_F cx fpos + SRM_FLAGPTR <= a < srm_F cx fpos + SRM_FLAGPTR + 8 ->
    aview SEGS (w_H W4) mem4 a = aview SEGS (w_H W3) (ms_mem ms3) a).
  { intros a Ha. destruct HKc4 as (_ & _ & _ & K4 & _). apply (K4 SRM_CID fpos a F6).
    - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite F7, SRM_FB_val. unfold SRM_FLAGPTR, SRM_FB in *. lia.
    - intros HEa. destruct (HEc a HEa) as [HE | HB].
      + apply (srm_E_noside fx cx fpos X ly3 S3 W3 ms3 md3 a Hpre Hb HE). left.
        unfold in_zr, frame_rng. cbn [fst snd]. change (frame_addr (sm_lyc cx) SRM_CID fpos) with (srm_F cx fpos).
        rewrite SRM_FB_val. unfold SRM_FLAGPTR, SRM_FB in *. lia.
      + unfold srm_bufb, srm_kind, srm_alias, SRM_KIND, SRM_ALIAS, KIND_CAP, ALIAS_MAX, SRM_FLAGPTR in *. lia. }
  assert (Hin4 : In (SRM_CID, fpos) (frames S4)) by (rewrite Hfr4; exact F6).
  assert (Hfa4 : frame_addr ly4 SRM_CID fpos = srm_F cx fpos) by (unfold srm_F, frame_addr; rewrite Fq, Fc; reflexivity).
  destruct (al_frames _ _ LAWS ly4 S4 W4 mem4 md4 SRM_CID fpos HAR4 Hin4) as (_ & _ & Hfb & Hfsh).
  exists ly4, S4, regs4, mem4, md4.
  split; [exact Hc4|].
  split.
  2: { split; [exact Hpres|]. split; [exact HKc4 | exact HP]. }
  unfold srm_base. cbv zeta. cbn [ms_regs ms_mem ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr mkst].
  assert (Pr : forall r : Z, acallee_saved r -> getr regs4 (Z_to_bv 5 r) = getr (ms_regs ms3) (Z_to_bv 5 r))
    by exact Hpres.
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [exact HJ4|].
  split; [rewrite Hfr4; exact B7|].
  split; [exact B8|].
  split; [exact (set_fs_trans S3 S4 (sm_Sc cx) B9 HS4)|].
  split; [exact (perm_trans Hperm4 B10)|].
  split; [exact B11|].
  split; [etransitivity; [exact (Pr 2 ltac:(unfold acallee_saved; lia)) | exact B12]|].
  split; [etransitivity; [exact (Pr 9 ltac:(unfold acallee_saved; lia)) | exact B13]|].
  split; [etransitivity; [exact (Pr 8 ltac:(unfold acallee_saved; lia)) | exact B14]|].
  split; [etransitivity; [exact (Pr 18 ltac:(unfold acallee_saved; lia)) | exact B15]|].
  split; [etransitivity; [exact (Pr 19 ltac:(unfold acallee_saved; lia)) | exact B16]|].
  split; [etransitivity; [exact (Pr 25 ltac:(unfold acallee_saved; lia)) | exact B17]|].
  split; [etransitivity; [exact (Pr 26 ltac:(unfold acallee_saved; lia)) | exact B18]|].
  split; [etransitivity; [exact (Pr 20 ltac:(unfold acallee_saved; lia)) | exact B19]|].
  split; [etransitivity; [exact (Pr 22 ltac:(unfold acallee_saved; lia)) | exact B20]|].
  split; [etransitivity; [exact (Pr 3 ltac:(unfold acallee_saved; lia)) | exact B21]|].
  split; [etransitivity; [exact (Pr 4 ltac:(unfold acallee_saved; lia)) | exact B22]|].
  split; [etransitivity; [exact (Pr 27 ltac:(unfold acallee_saved; lia)) | exact B23]|].
  split.
  { rewrite (srm_rdword_ext (aview SEGS (w_H W3) (ms_mem ms3)) (aview SEGS (w_H W4) mem4) (srm_sp cx - 8))
      by (intros x Hx; apply Hkeep_hi; lia).
    exact B24. }
  split.
  { intros j Hj.
    rewrite (srm_rdword_ext (aview SEGS (w_H W3) (ms_mem ms3)) (aview SEGS (w_H W4) mem4) (srm_sp cx - 16 - 8 * j))
      by (intros x Hx; apply Hkeep_hi; lia).
    exact (B25 j Hj). }
  split.
  { rewrite (srm_rdword_ext (aview SEGS (w_H W3) (ms_mem ms3)) (aview SEGS (w_H W4) mem4)
      (srm_F cx fpos + SRM_FLAGPTR)) by (intros x Hx; apply Hkeep_fl; lia).
    exact B26. }
  split.
  { intros a Ha. apply (proj1 (Hfb a ltac:(rewrite Hfa4, SRM_FB_val; lia))). }
  split.
  { intros a Ha. destruct (Hfsh (a - srm_SH cx fpos)) as (Hpa & _).
    { rewrite SRM_FB_val, SRM_SHN_val. lia. }
    rewrite Hfa4 in Hpa. change (shadow_addr (srm_F cx fpos)) with (srm_SH cx fpos) in Hpa.
    replace (srm_SH cx fpos + (a - srm_SH cx fpos)) with a in Hpa by lia. exact Hpa. }
  split.
  { assert (Hq1 : alloc_ceiling <= srm_sp cx - REAC_SERVED_MARK_AK) by lia.
    assert (Hq2 : srm_sp cx <= 2 ^ 64) by lia.
    assert (Hq3 : srm_sp cx - REAC_SERVED_MARK_AK <= spZ (ms_regs ms3) - Kc) by (rewrite Hsp; lia).
    assert (Hq4 : spZ (ms_regs ms3) <= srm_sp cx) by (rewrite Hsp; lia).
    assert (Hq5 : forall b m, In (b, m) (ablocks B (sm_lyc cx) (sm_Sc cx)) -> In (b, m) (ablocks B ly3 S3)).
    { intros b m Hbm. eapply Permutation_in; [apply Permutation_sym; exact B10 | exact Hbm]. }
    assert (Hq6 : forall f, In f (frames (sm_Sc cx)) -> In f (frames S3)) by (intros f Hf; rewrite B7; right; exact Hf).
    assert (Hq7 : forall a, X a \/ aside_rng (sm_lyc cx) SRM_CID fpos a ->
      srm_E cx a \/ aside_rng (sm_lyc cx) SRM_CID fpos a).
    { intros a [Ha | Ha]; [left; exact (HX a Ha) | right; exact Ha]. }
    assert (Hq8 : forall a, Ec a -> srm_E cx a \/ aside_rng (sm_lyc cx) SRM_CID fpos a).
    { intros a Ha. destruct (HEc a Ha) as [HE | HB]; [left; exact HE|]. right. left.
      unfold in_zr, frame_rng. cbn [fst snd]. change (frame_addr (sm_lyc cx) SRM_CID fpos) with (srm_F cx fpos).
      rewrite SRM_FB_val. unfold srm_bufb, srm_kind, srm_alias, SRM_KIND, SRM_ALIAS, KIND_CAP, ALIAS_MAX, SRM_FB in *.
      lia. }
    assert (Hlow := srm_segs_low).
    eapply akept_trans_ly with (ly1 := ly3) (S1 := S3) (W1 := W3) (m1 := ms_mem ms3)
      (slo1 := spZ (ms_regs ms3) - Kc) (shi1 := spZ (ms_regs ms3))
      (E1 := fun a => X a \/ aside_rng (sm_lyc cx) SRM_CID fpos a) (Ec := Ec); eassumption. }
  split; [rewrite Hfds; exact B30|]. split; [rewrite Hfs; exact B31|].
  split.
  { intros a Hro Hns Herr. destruct HKc4 as (_ & _ & K3 & _).
    assert (Hi : in_img SEGS a).
    { destruct Hro as [(s & Hs & _ & Hr) | Hr]; [exists s; split; [exact Hs | exact Hr] | exact (RELRO_IMG a Hr)]. }
    rewrite (K3 a Hi Hns Herr).
    - exact (B32 a Hro Hns Herr).
    - intros HEa. destruct (HEc a HEa) as [HE | HB]; [exact (A14 a HE Hro)|].
      apply (F5 a); [|exact Hi].
      unfold srm_bufb, srm_kind, srm_alias, SRM_KIND, SRM_ALIAS, KIND_CAP, ALIAS_MAX, SRM_FB in *. lia. }
  exact (fxr_frm0 fx fx' B33 Hfx).
Qed.

(* ---- read-set bytes at a callee ---- *)
Lemma srm_akb_entry : forall fx cx fpos X ly3 S3 W3 (ms3 : machine_state) md3 Kc a,
  srm_pre SK B cx -> srm_base fx SK B cx fpos X ly3 S3 W3 ms3 md3 -> 0 <= Kc <= REAC_CODE_EMIT_AK ->
  akb SEGS B (sm_lyc cx) (sm_Sc cx) (srm_sp cx - REAC_SERVED_MARK_AK) (srm_sp cx) a ->
  akb SEGS B ly3 S3 (spZ (ms_regs ms3) - Kc) (spZ (ms_regs ms3)) a.
Proof using LAWS TB RELRO_IMG HSEGS.
  intros fx cx fpos X ly3 S3 W3 ms3 md3 Kc a Hpre Hb HKc Hakb.
  pose proof (srm_sp_facts cx Hpre) as (Q1 & Q2 & Q3 & Q4 & Q5).
  pose proof (srm_base_sp fx cx fpos X ly3 S3 W3 ms3 md3 Hpre Hb) as Hsp.
  destruct (srm_F_facts fx cx fpos X ly3 S3 W3 ms3 md3 Hpre Hb)
    as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & Hfa & Hlo & Hhi).
  pose proof Hb as Hb'. srm_unbase Hb'.
  pose proof REAC_SERVED_MARK_AK_val as HK.
  assert (HKe : REAC_SERVED_MARK_AK = 144 + REAC_CODE_EMIT_AK) by reflexivity.
  rewrite Hsp.
  destruct Hakb as [(H1 & H2) | [(b & m & Hin & Hr) | [H3 | (c & q & Hin & Hr)]]].
  - left. rewrite Hlo, Hhi. split; [exact H1 | lia].
  - right; left. exists b, m. split; [|exact Hr].
    eapply Permutation_in; [apply Permutation_sym; exact B10 | exact Hin].
  - right; right; left. exact H3.
  - right; right; right. exists c, q. split; [rewrite B7; right; exact Hin|].
    unfold frame_rng in *. cbn [fst snd] in *. rewrite Hfa. exact Hr.
Qed.

Lemma srm_akb_frame : forall fx cx fpos X ly3 S3 W3 (ms3 : machine_state) md3 slo shi a,
  srm_pre SK B cx -> srm_base fx SK B cx fpos X ly3 S3 W3 ms3 md3 ->
  srm_F cx fpos <= a < srm_F cx fpos + SRM_FB -> akb SEGS B ly3 S3 slo shi a.
Proof using LAWS TB RELRO_IMG HSEGS.
  intros fx cx fpos X ly3 S3 W3 ms3 md3 slo shi a Hpre Hb Ha.
  destruct (srm_F_facts fx cx fpos X ly3 S3 W3 ms3 md3 Hpre Hb) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & _).
  right; right; right. exists SRM_CID, fpos. split; [exact F6|].
  unfold in_zr, frame_rng. cbn [fst snd]. rewrite F7, SRM_FB_val. exact Ha.
Qed.

Lemma srm_akb_img : forall ly3 S3 slo shi a,
  in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  akb SEGS B ly3 S3 slo shi a.
Proof using LAWS TB RELRO_IMG HSEGS.
  intros ly3 S3 slo shi a H1 H2 H3. right; right; left. split; [exact H1 | split; [exact H2 | exact H3]].
Qed.
End k.
