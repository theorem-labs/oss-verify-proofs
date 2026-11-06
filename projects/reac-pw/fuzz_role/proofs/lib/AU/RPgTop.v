(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_knock/lib/A/APgLib.v at origin/ossv/recipes 6ebe35ba632
   (lines 132-146 ajournal_fp_nil and 156-159 ajournal_nil_io, from cgif ACfh.v; lines 207-239, the leaf of
   knock_lib_x_body: the contract's post from the walk's return state) for reac-pw/fuzz_role image A: the walk is
   role's chain of five segments over the harness-level cuts of lib/A/RPgHarn.v, with lib/A/RPgCSpec.v's two
   middle contracts in the middle and the malloc(pod) step between them; the leaf is unchanged but for the
   exists-fx' form of RPgCSpec.rl_lib_contract_x. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgTop.v at ad0e022f7af for image B, in the
   form of proofs/reac-pw/fuzz_rate/lib/AU/RtPgTopB.v at 2e01bfcb541: the segment statements are lib/AU/RPgHarn.v's
   continuation form (S_E01 .. S_X01 composed by rh_seg_chain; S_M01 and S_M02 proved here from the two middle
   contracts and the malloc(pod) step rh_S_C23_stmt), the record is lib/AU/RPgImgA.v role_himg_B, the real frame is
   0x200 bytes, the frame for locals is a class-4 frame (1024 bytes, 128 shadow bytes, flag pointer word at F + 0x3f8),
   the two segments' write ranges lie in [F, F + 0x3f8), its shadow and the real frame's cells [R, R + 0x198), and
   the real frame's checked cells come from lib/AU/RPgMem.v rm_B_rz. *)
(* reac-pw/fuzz_role image B (fuzz_role.asan-ubsan, pinned sha256
   b255d4935da5af137a3967dbe33380ea43be8e78bfe05d1e356e0a2be8a69ff0; addresses measured on the unstripped twin
   dc791783f32962615e18a5f5cffae758ba56eb5dc87f70913c3579b101b4406a): THE WHOLE RUN of LLVMFuzzerTestOneInput
   (0x80020), chained.

     role_lib_x : rl_lib_contract_x segs B ameter_triv K XM_LIB XN_LIB RLO RHI A_LLVMF RA_LLVMF ...

   from these Section hypotheses:
     S_E01   RPgHarn.S_E01                      ENTRY 0x80020 -> C1 0x802c4
     M01     RPgCSpec.role_build_contract       C1 -> C2 0x82164 (RPgMainL.role_build_holds over the build's pieces)
     C23     RPgHarn.rh_S_C23_stmt              C2 -> C3 0x82168, the malloc(pod) call
     M02     RPgCSpec.role_check_contract       C3 -> C4 0x82570 (RPgMainL.role_check_holds over the checks' pieces)
     S_X01   RPgHarn.S_X01                      C4 -> the return to RA_LLVMF
   and the static law of the symbols, RPgHarn.rh_static_law (the start-up's const cells and zero-shadow ranges).
   The chaining itself (this file) does three kinds of work:
   - at C1 and C3 it builds the middle contracts' rl_seg_pre from the harness cut (rh_pre): the journal, the cut's
     values and the frame's shadow as they are; the geometry (R mod 16, R + 0x200 <= S, sp0 - LLVMF_STK <= R - ASTACK)
     from the entry's astk_ok and RH_RSZ + 32 + ASTACK <= LLVMF_STK; the read-only agreement through the journal
     (RPgBase.arodata_ok_journalP); the globals', strings', cells' and read-only facts from rh_static_law at the cut's
     AR; the real frame's checked cells from the stack's zero shadow (RPgMem.rm_B_rz); the blocks made since the entry
     are fresh (rh_common's freshness list);
   - it carries what the segments after each contract need and the contracts do not restate (the 13 callee-saved
     words at [S - 0x68, S) and the frame's flag word at F + 0x3f8: RPgHarn.rh_kept) through each "outside the write
     set" clause (rl_seg_post's), by the separations below: the stack lies above alloc_ceiling, the frame and the
     blocks below it and apart (AR_sep_law), the shadow bytes of an application address are not application
     addresses;
   - it turns S_X01's return state into rl_lib_post_x (knock's leaf: the journal at FP = [] weakened to the sink's
     footprint, I/O and file system kept, the sink and the meta table kept by the core's laws, the input bytes kept by
     the journal's block clause). *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK14 YK0s YK15 YK18 YP09 YI04 YI08 YN3v YI00 YI0m YI09.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YCbp.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgBase RPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import RPgImgA RPgSiteA RPgHarn RPgMem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ===================================== numbers ===================================== *)
Lemma rh_u64 : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn [Z.of_N]. lia. Qed.

Lemma rh_fs4 : fs_frame_bytes RH_CID = 1024.
Proof. reflexivity. Qed.

Lemma rh_frame_addr_le : forall n ly ly' cid pos, layout_le n ly ly' -> frame_addr ly' cid pos = frame_addr ly cid pos.
Proof. intros n ly ly' cid pos H. unfold frame_addr. destruct H as (_ & _ & _ & _ & _ & HF & _). rewrite HF. reflexivity. Qed.

Lemma rh_stk_le : forall n ly ly', layout_le n ly ly' -> ly_stk_lo ly' = ly_stk_lo ly /\ ly_stk_hi ly' = ly_stk_hi ly.
Proof. intros n ly ly' H. destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & H1 & H2 & _). split; assumption. Qed.

(* The real frame's base: R = 32 * floor((S - 0x200) / 32). *)
Lemma rh_R_facts : forall S R, R = 32 * ((S - RH_RSZ) / 32) ->
  R mod 16 = 0 /\ R + RH_RSZ <= S /\ S - RH_RSZ - 32 < R.
Proof.
intros S R ->. unfold RH_RSZ.
pose proof (Z.div_mod (S - 0x200) 32 ltac:(lia)) as Hd. pose proof (Z.mod_pos_bound (S - 0x200) 32 ltac:(lia)) as Hm.
set (q := (S - 0x200) / 32) in *. set (r := (S - 0x200) mod 32) in *.
split; [|lia]. replace (32 * q) with ((2 * q) * 16) by lia. apply Z.mod_mul. lia.
Qed.

Lemma rh_mod16_8 : forall x, x mod 16 = 0 -> x mod 8 = 0.
Proof.
intros x H. pose proof (Z.div_mod x 16 ltac:(lia)) as Hd. rewrite H, Z.add_0_r in Hd. rewrite Hd.
replace (16 * (x / 16)) with ((2 * (x / 16)) * 8) by lia. apply Z.mod_mul. lia.
Qed.

(* rh_hcx's projections, with the segments implicit in this file *)
Local Arguments h_ly {segs} _.
Local Arguments h_S {segs} _.
Local Arguments h_W {segs} _.
Local Arguments h_regs {segs} _.
Local Arguments h_mem {segs} _.
Local Arguments h_md {segs} _.
Local Arguments h_p {segs} _.
Local Arguments h_n {segs} _.
Local Arguments h_pl {segs} _.

Section n. Context {rc : YM05.RunCeil}.
(* The bytes the chaining carries (rh_kept) lie off the callees' stack, off the frame's objects [F, F + 0x3f8)
   (every frame range of hi_w1 / hi_w2 lies there), off the frame's 128 shadow bytes and off the real frame's cells
   [R, R + 0x198) (every real-frame range of hi_w1 / hi_w2 lies there). *)
Lemma rh_carried_off : forall S R F a,
  alloc_ceiling + ASTACK <= S - RH_RSZ - 32 -> R + RH_RSZ <= S -> S - RH_RSZ - 32 < R ->
  4096 <= F -> F + 1024 <= alloc_ceiling -> in_app F 1024 -> S <= 2 ^ 47 ->
  (S - 0x68 <= a < S \/ F + 0x3f8 <= a < F + 0x400) ->
  0 <= a < 2 ^ 64 /\ ~ (R - ASTACK <= a < R) /\
  ~ (F <= a < F + 0x3f8) /\ ~ (shadow_addr F <= a < shadow_addr F + 128) /\ ~ (R <= a < R + 0x198).
Proof.
intros S R F a Hst HR1 HR2 HF1 HF2 Happ HS Ha.
pose proof ASAN_CEIL_range as ((Hc1 & Hc2) & _). unfold ASAN_CEIL in Hc1, Hc2.
unfold shadow_addr, SHADOW_OFF, ASTACK, RH_RSZ in *. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
pose proof (Z.div_mod F 8 ltac:(lia)) as Hd. pose proof (Z.mod_pos_bound F 8 ltac:(lia)) as Hm.
set (q := F / 8) in *. set (r := F mod 8) in *.
repeat split; lia.
Qed.
End n.

(* M01's and M02's write ranges, as three runs: the frame's objects, the frame's shadow, the real frame's cells. *)
Lemma rh_inw1 : forall e a, rl_inw e (hi_w1 role_himg_B) a ->
  (e_F e <= a < e_F e + 0x3f8) \/ (shadow_addr (e_F e) <= a < shadow_addr (e_F e) + 128) \/
  (e_R e <= a < e_R e + 0x198).
Proof.
intros e a H. unfold rl_inw in H. cbn [hi_w1 role_himg_B] in H.
rewrite !Exists_cons, Exists_nil in H. cbn [rl_xv fst snd] in H. lia.
Qed.

Lemma rh_inw2 : forall e a, rl_inw e (hi_w2 role_himg_B) a ->
  (e_F e <= a < e_F e + 0x3f8) \/ (shadow_addr (e_F e) <= a < shadow_addr (e_F e) + 128) \/
  (e_R e <= a < e_R e + 0x198).
Proof.
intros e a H. unfold rl_inw in H. cbn [hi_w2 role_himg_B] in H.
rewrite !Exists_cons, Exists_nil in H. cbn [rl_xv fst snd] in H. lia.
Qed.

(* ============================ journal facts [knock APgLib.v:132-159, cgif ACfh.v] ============================ *)
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Lemma rh_ajournal_fp_nil : forall STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
ajournal segs B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
ajournal segs B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k.
Proof.
intros STK sp0 FP ly S W mem md own ly' S' W' mem' md' k
(HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & F5 & HQT).
split; [exact HAR|]. split; [exact Hly|]. split; [exact Hsecs|]. split; [exact Hwle|].
split; [eapply aos_step_mono; [|exact Hio]; intros Ho; exfalso; exact (sink_closed_nil Ho)|].
split; [exact Hfrs|]. split; [exact Hnev|]. split; [exact Hk|]. split; [exact F1|].
split; [intros p n i H1 H2 Hi _; apply (F2 p n i H1 H2 Hi); apply inFP_nil|].
split; [intros a Hi Hns He _; apply (F3 a Hi Hns He); apply fp_spares_closed; intros Ho; exact (sink_closed_nil Ho)|].
split; [intros cid pos a H1 H2 _; apply (F4 cid pos a H1 H2); apply inFP_nil|].
split; [intros p n i H1 H2 Hi; exfalso; exact (inFP_nil _ (Hgone p n i H1 H2 Hi))|].
split; [exact Hpres|]. split; [exact Hstatic|]. split; [exact F5 | exact HQT].
Qed.
Lemma rh_ajournal_nil_io : forall STK sp0 ly S W mem md own ly' S' W' mem' md' k,
ajournal segs B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
m_fds md' = m_fds md /\ m_fs md' = m_fs md.
Proof.
intros STK sp0 ly S W mem md own ly' S' W' mem' md' k HJ. pose proof HJ as (_ & _ & _ & _ & Hos & _).
destruct (aos_step_closed [] md md' sink_closed_nil Hos) as (Efd & Efsys & _ & _).
unfold m_fds, m_fs. rewrite Efd, Efsys. split; reflexivity.
Qed.
End d.

Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Let LAWS : AR_laws segs B := AR_laws_ok segs B.

(* ============================ cells across a kept clause ============================ *)
Lemma rh_cell_kept : forall H mem H' mem' regs regs' e b o v,
  rl_at segs H mem regs e (LCell b o) v ->
  (forall i, 0 <= i < 8 -> aview segs H' mem' (rl_xv e b + o + i) = aview segs H mem (rl_xv e b + o + i)) ->
  rl_at segs H' mem' regs' e (LCell b o) v.
Proof.
intros H mem H' mem' regs regs' e b o v Hv Hk. cbn [rl_at] in *. intros k Hlt.
rewrite (mbyte_of_aview segs H H' mem mem'); [exact (Hv k Hlt) | apply Hk; lia].
Qed.

Lemma rh_kept_tr : forall (hx : rh_hcx segs) pos e H mem H' mem' regs regs',
  Forall (fun f => rl_at segs H mem regs e (fst f) (snd f)) (rh_cells (h_regs hx) (flag_addr (h_ly hx) RH_CID pos)) ->
  (forall a, (e_S e - 0x68 <= a < e_S e \/ e_F e + 0x3f8 <= a < e_F e + 0x400) -> aview segs H' mem' a = aview segs H mem a) ->
  Forall (fun f => rl_at segs H' mem' regs' e (fst f) (snd f)) (rh_cells (h_regs hx) (flag_addr (h_ly hx) RH_CID pos)).
Proof.
intros hx pos e H mem H' mem' regs regs' HK Hkeep.
rewrite Forall_forall in HK |- *. intros f Hf. pose proof (HK f Hf) as Hv.
unfold rh_cells, rh_saves_L in Hf. apply in_app_iff in Hf as [Hf|Hf].
- apply in_map_iff in Hf as (j & <- & Hj). apply in_seq in Hj. cbn [fst snd] in *.
  apply (rh_cell_kept H mem H' mem' regs regs' e XS _ _ Hv). intros i Hi. apply Hkeep. cbn [rl_xv]. lia.
- destruct Hf as [<-|[]]. cbn [fst snd] in *.
  apply (rh_cell_kept H mem H' mem' regs regs' e XF _ _ Hv). intros i Hi. apply Hkeep. cbn [rl_xv]. lia.
Qed.

Section c.
Variables RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK : Z.
(* the harness's stack covers the real frame, its 32-byte alignment slack and the callees' stack *)
Hypothesis HSTK : RH_RSZ + 32 + ASTACK <= LLVMF_STK.
(* the harness's event budget covers the run's four allocator events *)
Hypothesis HEV : RH_EV <= EV_LIB.
(* the read-only range lies in the image *)
Hypothesis HRELRO : forall a, RLO <= a < RHI -> in_img segs a.
Context {RO : ro_below_ofl segs RLO RHI}.
(* the static facts of the symbols *)
Hypothesis HSTAT : rh_static_law segs B RLO RHI.

Local Notation BASE := (rh_base segs B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK).
Local Notation J := (rh_j segs B LLVMF_STK).
Local Notation COMMON := (rh_common segs B LLVMF_STK).
(* the carried bytes (rh_kept): the 13 save slots and the frame's flag word *)
Local Notation CARRIED e a := (e_S e - 0x68 <= a < e_S e \/ e_F e + 0x3f8 <= a < e_F e + 0x400).

(* ============================ the entry's geometry ============================ *)
Lemma rh_geo_facts : forall hx pos e, BASE hx -> rh_geo segs hx pos e ->
  alloc_ceiling + ASTACK <= e_S e - RH_RSZ - 32 /\ e_S e mod 16 = 0 /\
  alloc_ceiling <= ly_stk_lo (h_ly hx) /\ ly_stk_lo (h_ly hx) + LLVMF_STK <= e_S e /\
  e_S e <= ly_stk_hi (h_ly hx) /\ ly_stk_hi (h_ly hx) <= 2 ^ 47 /\
  e_R e mod 16 = 0 /\ e_R e + RH_RSZ <= e_S e /\ e_S e - RH_RSZ - 32 < e_R e /\
  e_S e - LLVMF_STK <= e_R e - ASTACK /\ ly_stk_lo (h_ly hx) <= e_R e.
Proof.
intros hx pos e HB (HS & HR & _). destruct HB as ((_ & _ & _ & _ & _ & Hstk & _) & _).
destruct Hstk as (H16 & _ & Hlo & Hlos & Hhi & H47 & _). rewrite <- HS in *.
destruct (rh_R_facts (e_S e) (e_R e) HR) as (HR16 & HR1 & HR2).
unfold RH_RSZ, ASTACK in *. repeat split; lia.
Qed.

(* the frame for locals at a state of the journal that holds it *)
Lemma rh_frame_facts : forall hx pos e own ly' S' W' mem' md' k,
  BASE hx -> rh_geo segs hx pos e -> J hx own ly' S' W' mem' md' k -> In (RH_CID, pos) (frames S') ->
  e_F e = frame_addr ly' RH_CID pos /\ 4096 <= e_F e /\ e_F e + 1024 <= alloc_ceiling /\ in_app (e_F e) 1024.
Proof.
intros hx pos e own ly' S' W' mem' md' k HB (_ & _ & HF) HJ Hin.
pose proof HJ as (HAR & Hly & _).
assert (EF : e_F e = frame_addr ly' RH_CID pos) by (rewrite HF; symmetry; exact (rh_frame_addr_le _ _ _ _ _ Hly)).
destruct (al_sep _ _ LAWS _ _ _ _ _ HAR) as [_ Hf]. rewrite Forall_forall in Hf. pose proof (Hf _ Hin) as Hb.
destruct (al_frames _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & Happ & _).
cbn [fst snd] in Hb. rewrite rh_fs4 in Hb, Happ. rewrite <- EF in Hb, Happ.
split; [exact EF|]. split; [lia|]. split; [lia | exact Happ].
Qed.

(* a block at a state of the journal *)
Lemma rh_block_facts : forall hx own ly' S' W' mem' md' k p n,
  J hx own ly' S' W' mem' md' k -> In (p, n) (ablocks B ly' S') ->
  p + req_size n <= alloc_ceiling /\ in_app p (req_size n) /\ 0 <= n.
Proof.
intros hx own ly' S' W' mem' md' k p n HJ Hin. pose proof HJ as (HAR & _).
pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & _ & H1 & H2 & _ & _ & H3).
split; [exact H1|]. split; [exact H2|]. lia.
Qed.

(* What a carried byte is apart from at a harness cut: the frame's objects, its shadow, the real frame's cells and
   every block made since the entry. *)
Lemma rh_carried_facts : forall hx pos e rest k bl L ly1 S1 W1 regs1 mem1 md1 a,
  BASE hx -> COMMON hx pos e rest k bl L ly1 S1 W1 regs1 mem1 md1 -> CARRIED e a ->
  ~ (e_F e <= a < e_F e + 0x3f8) /\ ~ (shadow_addr (e_F e) <= a < shadow_addr (e_F e) + 128) /\
  ~ (e_R e <= a < e_R e + 0x198) /\
  (forall p m, In (p, m) bl -> ~ (p <= a < p + m)).
Proof.
intros hx pos e rest k bl L ly1 S1 W1 regs1 mem1 md1 a HB HC Ha.
destruct HC as (HJ & Hfr & Hperm & _ & _ & _ & _ & Hgeo & _).
pose proof (rh_geo_facts hx pos e HB Hgeo) as (Hst & HS16 & Hlo & Hlos & Hhi & H47 & HR16 & HR1 & HR2 & HRs & HRlo).
assert (Hin : In (RH_CID, pos) (frames S1)) by (rewrite Hfr; left; reflexivity).
destruct (rh_frame_facts hx pos e _ _ _ _ _ _ _ HB Hgeo HJ Hin) as (EF & HF1 & HF2 & HFapp).
pose proof HJ as (HAR & Hly & _).
destruct (rh_stk_le _ _ _ Hly) as [Elo Ehi].
destruct (rh_carried_off (e_S e) (e_R e) (e_F e) a Hst HR1 HR2 HF1 HF2 HFapp ltac:(lia) Ha)
  as (_ & _ & N1 & N2 & N3).
split; [exact N1|]. split; [exact N2|]. split; [exact N3|].
intros p m Hpm.
assert (Hin1 : In (p, m) (ablocks B ly1 S1)).
{ apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. exact Hpm. }
destruct (rh_block_facts hx _ _ _ _ _ _ _ _ _ HJ Hin1) as (Hpc & _ & _).
pose proof (sep_block_frame segs B LAWS _ _ _ _ _ _ _ _ _ HAR Hin1 Hin) as Hsep. rewrite rh_fs4, <- EF in Hsep.
unfold zdisjoint in Hsep. cbn [fst snd] in Hsep.
assert (Hreq : m <= req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
unfold RH_RSZ, ASTACK in *. lia.
Qed.

(* ============================ a middle contract's start, from a harness cut ============================ *)
Lemma rh_pre : forall hx pos e rest k bl L ly2 S2 W2 regs2 mem2 md2,
  BASE hx -> k <= RH_EV -> In (e_pp e, Layout.PP_SIZE) bl -> e_pp e <> 0 ->
  COMMON hx pos e rest k bl L ly2 S2 W2 regs2 mem2 md2 ->
  rl_fsh segs (w_H W2) mem2 (e_F e) (hi_shA role_himg_B) ->
  rl_seg_pre segs B LLVMF_STK (spZ (h_regs hx)) [] (h_ly hx) (h_S hx) (h_W hx) (h_mem hx) (h_md hx)
    [(RH_CID, pos)] k regs2 ly2 S2 W2 mem2 md2 role_himg_B RLO RHI e pos.
Proof.
intros hx pos e rest k bl L ly2 S2 W2 regs2 mem2 md2 HB Hk Hppbl Hpp0 HC Hfsh.
pose proof HB as HB'. destruct HB' as (_ & _ & _ & _ & _ & _ & _ & _ & Hev & _ & HROS).
destruct HC as (HJ & Hfr & Hperm & Hfresh & Hr2 & Hr3 & Hr4 & Hgeo & _ & Hok & _ & _).
pose proof (rh_geo_facts hx pos e HB Hgeo) as (Hst & HS16 & Hlo & Hlos & Hhi & H47 & HR16 & HR1 & HR2 & HRs & HRlo).
pose proof HJ as (HAR & Hly & _).
destruct (rh_stk_le _ _ _ Hly) as [Elo Ehi].
assert (Hin3 : In (RH_CID, pos) (frames S2)) by (rewrite Hfr; left; reflexivity).
destruct (rh_frame_facts hx pos e _ _ _ _ _ _ _ HB Hgeo HJ Hin3) as (EF & _).
assert (Haro : arodata_okP segs RLO RHI B (aview segs (w_H W2) mem2)).
{ exact (arodata_ok_journalP segs RLO RHI HRELRO B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HROS). }
destruct (HSTAT ly2 S2 W2 mem2 md2 HAR Haro) as (Hg & Hs & Hc & Hrom).
destruct Hgeo as (HS & _ & _).
unfold rl_seg_pre. change (hi_rsz role_himg_B) with RH_RSZ.
split; [exact HJ|].
split; [unfold RH_EV in *; lia|].
split; [exact Hr2|]. split; [exact Hr3|]. split; [exact Hr4|].
split; [exact HS|]. split; [exact HR16|]. split; [lia|].
split; [unfold T_SEG_STK; rewrite <- HS; lia|].
split; [left; reflexivity|].
split; [exact EF|].
split; [exact Hfsh|].
split; [exact Hpp0|].
split; [apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; right; exact Hppbl|].
split; [exact Hok|].
split; [exact Haro|].
split; [exact Hg|].
split.
{ apply (rm_B_rz segs B ly2 S2 W2 mem2 md2 (e_R e) (e_S e) HAR);
  [rewrite Elo; lia | unfold RH_RSZ in HR1; lia | rewrite Ehi; lia | exact (rh_mod16_8 _ HS16)]. }
split; [exact Hs|]. split; [exact Hc|]. split; [exact Hrom|].
exact (proj1 (Forall_forall _ _) Hfresh _ Hppbl).
Qed.

(* ============================ a harness cut, from a middle contract's post ============================
   The journal, the registers sp / gp / tp, the frames, the blocks and the cut's values come from rl_seg_post; the
   geometry, the header tie and its bounds are facts of e; the carried cells cross the post's "outside the write set"
   clause because no carried byte is in the write set E. *)
Lemma rh_kept_seg : forall hx pos e own ly1 S1 W1 mem1 md1 k regs1 W2 mem2 regs2 (E : Z -> Prop),
  BASE hx -> rh_geo segs hx pos e -> J hx own ly1 S1 W1 mem1 md1 k -> In (RH_CID, pos) (frames S1) ->
  getr regs1 2 = w64 (e_R e) ->
  (forall a, CARRIED e a -> ~ E a) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs1 - T_SEG_STK <= a < spZ regs1) -> ~ E a ->
   aview segs (w_H W2) mem2 a = aview segs (w_H W1) mem1 a) ->
  rh_kept segs hx pos e W1 mem1 regs1 -> rh_kept segs hx pos e W2 mem2 regs2.
Proof.
intros hx pos e own ly1 S1 W1 mem1 md1 k regs1 W2 mem2 regs2 E HB Hgeo HJ Hin Hr2 HnE Hkeep HK.
pose proof (rh_geo_facts hx pos e HB Hgeo) as (Hst & HS16 & Hlo & Hlos & Hhi & H47 & HR16 & HR1 & HR2 & HRs & HRlo).
destruct (rh_frame_facts hx pos e _ _ _ _ _ _ _ HB Hgeo HJ Hin) as (EF & HF1 & HF2 & HFapp).
assert (EspR : spZ regs1 = e_R e).
{ unfold spZ. rewrite Hr2. unfold w64. apply rh_u64. unfold RH_RSZ, ASTACK in *. lia. }
unfold rh_kept in *. apply (rh_kept_tr hx pos e _ _ _ _ regs1 regs2 HK).
intros a Ha.
destruct (rh_carried_off (e_S e) (e_R e) (e_F e) a Hst HR1 HR2 HF1 HF2 HFapp ltac:(lia) Ha) as (Ha64 & HaR & _).
apply Hkeep; [exact Ha64 | unfold T_SEG_STK; rewrite EspR; exact HaR | exact (HnE a Ha)].
Qed.

Lemma rh_common_seg : forall hx pos e rest k bl L ly1 S1 W1 regs1 mem1 md1 L' ly2 S2 W2 regs2 mem2 md2
  (E : Z -> Prop),
  BASE hx -> COMMON hx pos e rest k bl L ly1 S1 W1 regs1 mem1 md1 ->
  J hx [(RH_CID, pos)] ly2 S2 W2 mem2 md2 k ->
  (forall r : Z, r = 2 \/ r = 3 \/ r = 4 -> getr regs2 (Z_to_bv 5 r) = getr regs1 (Z_to_bv 5 r)) ->
  frames S2 = frames S1 ->
  Permutation (ablocks B ly2 S2) (ablocks B ly1 S1) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs1 - T_SEG_STK <= a < spZ regs1) -> ~ E a ->
   aview segs (w_H W2) mem2 a = aview segs (w_H W1) mem1 a) ->
  (forall a, CARRIED e a -> ~ E a) ->
  rl_cut segs (w_H W2) mem2 regs2 e L' ->
  COMMON hx pos e rest k bl L' ly2 S2 W2 regs2 mem2 md2.
Proof.
intros hx pos e rest k bl L ly1 S1 W1 regs1 mem1 md1 L' ly2 S2 W2 regs2 mem2 md2 E
  HB HC HJ2 Hr Hfr2 Hperm2 Hkeep HnE HL'.
destruct HC as (HJ1 & Hfr1 & Hperm1 & Hfresh & Hr2 & Hr3 & Hr4 & Hgeo & Hhdr & Hok & _ & Hkept).
assert (Hin1 : In (RH_CID, pos) (frames S1)) by (rewrite Hfr1; left; reflexivity).
unfold rh_common.
split; [exact HJ2|].
split; [rewrite Hfr2; exact Hfr1|].
split; [exact (Permutation_trans Hperm2 Hperm1)|].
split; [exact Hfresh|].
split; [rewrite <- Hr2; exact (Hr 2 (or_introl eq_refl))|].
split; [rewrite <- Hr3; exact (Hr 3 (or_intror (or_introl eq_refl)))|].
split; [rewrite <- Hr4; exact (Hr 4 (or_intror (or_intror eq_refl)))|].
split; [exact Hgeo|]. split; [exact Hhdr|]. split; [exact Hok|]. split; [exact HL'|].
exact (rh_kept_seg hx pos e _ ly1 S1 W1 mem1 md1 k regs1 W2 mem2 regs2 E HB Hgeo HJ1 Hin1 Hr2 HnE Hkeep Hkept).
Qed.

(* ============================ the two middle segment statements ============================ *)
Section s.
Variable MT : ameter_ops.

(* S_M01: role_build_contract from C1, then the malloc(pod) step from C2. *)
Lemma rh_S_M01 : role_build_contract segs B MT role_himg_B RLO RHI ->
  rh_S_C23_stmt segs B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK ->
  S_M01 segs B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK.
Proof.
intros HBUILD HC23 hx POST HB HF3 pos e rest ly1 S1 W1 regs1 mem1 md1 HC1.
destruct HC1 as (HCm & Hpp0 & Hfsh1 & Hin1).
pose proof (rh_pre hx pos e rest 1 [(e_pp e, Layout.PP_SIZE)] (hi_L1 role_himg_B) ly1 S1 W1 regs1 mem1 md1
  HB ltac:(unfold RH_EV; lia) (or_introl eq_refl) Hpp0 HCm Hfsh1) as HPRE1.
pose proof HCm as (_ & _ & _ & _ & _ & _ & _ & _ & Hhdr & _ & HL1 & _).
pose proof Hhdr as (_ & _ & _ & _ & Hlen).
destruct Hin1 as (Hleft & Harr & Hra & Hsrc & Hhi & Hamem & Hhull & Hdis).
eapply SRr_bind; [exact (HBUILD LLVMF_STK (spZ (h_regs hx)) [] (h_ly hx) (h_S hx) (h_W hx) (h_mem hx) (h_md hx)
  [(RH_CID, pos)] ly1 S1 W1 mem1 md1 1 regs1 e pos rest HPRE1 HL1 Hleft Hlen Harr Hra Hsrc Hhi Hamem Hhull
  Hdis)|].
intros W2 c2 _ (fx2 & ly2 & S2 & regs2 & mem2 & md2 & Ec2 & Efx & HJ2 & Hr & Hfr2 & Hperm2 & Hio2 & Hmo2 & Hkeep2
  & HL2 & Hfsh2 & Hpp2).
subst fx2. subst c2.
refine (HC23 hx POST HB HF3 pos e rest ly2 S2 W2 regs2 mem2 md2 _).
split.
{ apply (rh_common_seg hx pos e rest 1 _ _ ly1 S1 W1 regs1 mem1 md1 _ ly2 S2 W2 regs2 mem2 md2 _
    HB HCm HJ2 Hr Hfr2 Hperm2 Hkeep2); [|exact HL2].
  intros a Ha Hw. cbn beta in Hw.
  destruct (rh_carried_facts hx pos e rest 1 _ _ ly1 S1 W1 regs1 mem1 md1 a HB HCm Ha) as (N1 & N2 & N3 & N5).
  destruct Hw as [Hw|Hw].
  - apply rh_inw1 in Hw. lia.
  - exact (N5 _ _ (or_introl eq_refl) Hw). }
split; [exact Hpp0|]. split; [exact Hfsh2|].
split; [rewrite Hlen; exact (rl_len_bounds rest)|].
exact Hpp2.
Qed.

(* S_M02: role_check_contract from C3, at a float state with a zero rounding mode (the harness's entry gives it). *)
Lemma rh_S_M02 : role_check_contract segs B MT role_himg_B RLO RHI -> YK0o.frm_zero (@fp_csr fx) ->
  S_M02 segs B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK.
Proof.
intros HCHECK HFRM hx POST HB HF4 pos e rest ly3 S3 W3 regs3 mem3 md3 HC3.
destruct HC3 as (HCm & Hpp0 & Hpod0 & Hfsh3 & _ & Hpp3).
pose proof (rh_pre hx pos e rest 2 [(e_pp e, Layout.PP_SIZE); (e_pod e, e_len e)] (hi_L3 role_himg_B)
  ly3 S3 W3 regs3 mem3 md3 HB ltac:(unfold RH_EV; lia) (or_introl eq_refl) Hpp0 HCm Hfsh3) as HPRE3.
pose proof HCm as (_ & _ & Hperm3 & Hfresh3 & _ & _ & _ & _ & Hhdr & _ & HL3 & _).
pose proof Hhdr as (_ & _ & _ & _ & Hlen).
assert (Hpodin : In (e_pod e, e_len e) (ablocks B ly3 S3)).
{ apply (Permutation_in _ (Permutation_sym Hperm3)). apply in_or_app. right. right. left. reflexivity. }
assert (Hpodnin : ~ In (e_pod e, e_len e) (ablocks B (h_ly hx) (h_S hx))).
{ exact (proj1 (Forall_forall _ _) Hfresh3 _ (or_intror (or_introl eq_refl))). }
eapply SRr_bind; [exact (HCHECK LLVMF_STK (spZ (h_regs hx)) [] (h_ly hx) (h_S hx) (h_W hx) (h_mem hx) (h_md hx)
  [(RH_CID, pos)] ly3 S3 W3 mem3 md3 2 regs3 e pos rest HPRE3 HL3 Hlen Hpp3 Hpod0 Hpodin Hpodnin HFRM)|].
intros W4 c4 _ (fx4 & ly4 & S4 & regs4 & mem4 & md4 & Ec4 & Hfxk & HJ4 & Hr & Hfr4 & Hperm4 & Hio4 & Hmo4 & Hkeep4
  & HL4 & Hfsh4).
subst c4.
refine (HF4 fx4 pos e rest ly4 S4 W4 regs4 mem4 md4 _).
split.
{ apply (rh_common_seg hx pos e rest 2 _ _ ly3 S3 W3 regs3 mem3 md3 _ ly4 S4 W4 regs4 mem4 md4 _
    HB HCm HJ4 Hr Hfr4 Hperm4 Hkeep4); [|exact HL4].
  intros a Ha Hw. cbn beta in Hw.
  destruct (rh_carried_facts hx pos e rest 2 _ _ ly3 S3 W3 regs3 mem3 md3 a HB HCm Ha) as (N1 & N2 & N3 & N5).
  destruct Hw as [Hw|Hw].
  - apply rh_inw2 in Hw. lia.
  - exact (N5 _ _ (or_intror (or_introl eq_refl)) Hw). }
split; [exact Hpp0|]. split; [exact Hpod0|]. split; [exact Hfsh4|].
exact (proj2 Hfxk).
Qed.
End s.

(* ============================ the whole run ============================ *)
Section e.
Variable K : asink_syms.
Variables XM_LIB XN_LIB : Z -> Z.
Variable A_LLVMF : Z.
Context {LS : lib_shape}.
(* the harness's entry (image B: 0x80020) *)
Hypothesis HA : A_LLVMF = RH_ENTRY.
(* the core's sink laws at the symbols (the relocated frame's YD1u.tfib_AIL) *)
Hypothesis AIL : asink_img_laws segs B K.
(* the lib shape's one-leaf law (RPgLib.role_lib_x_all_stmt's first premise) *)
Hypothesis LEAF : forall pl fs (Kl : lleaf -> TSet), LIBK pl fs Kl = Kl (LL 0 fs []).
(* S_E01: ENTRY -> C1 *)
Hypothesis HE01 : S_E01 segs B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK.
(* M01: RPgMainL.role_build_holds *)
Hypothesis HBUILD : role_build_contract segs B ameter_triv role_himg_B RLO RHI.
(* the malloc(pod) step: C2 -> C3 *)
Hypothesis HC23 : rh_S_C23_stmt segs B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK.
(* M02: RPgMainL.role_check_holds *)
Hypothesis HCHECK : role_check_contract segs B ameter_triv role_himg_B RLO RHI.
(* S_X01: C4 -> the return *)
Hypothesis HX01 : S_X01 segs B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK.

Theorem role_lib_x : rl_lib_contract_x segs B ameter_triv K XM_LIB XN_LIB RLO RHI
  A_LLVMF RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK.
Proof.
intros ly S W regs mem md p n pl M Kl HAI HPRE HK.
rewrite LEAF.
destruct HPRE as (HPRE0 & Hra & Hp & Hn & Hpn & Hnpl & HPL & Hfr0 & Hev & Hlive & HROS & HSNK & HFD & HSORT
  & HAM & HMOK & HFRM).
set (hx := {| h_ly := ly; h_S := S; h_W := W; h_regs := regs; h_mem := mem; h_md := md; h_p := p; h_n := n;
  h_pl := pl |} : rh_hcx segs).
assert (HB : BASE hx).
{ exact (conj HPRE0 (conj Hra (conj Hp (conj Hn (conj Hpn (conj Hnpl (conj HPL (conj Hfr0 (conj Hev
    (conj Hlive HROS)))))))))). }
assert (HSEG : seg_lemmas segs B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK).
{ split; [exact HE01|].
  split; [exact (rh_S_M01 ameter_triv HBUILD HC23)|].
  split; [exact (rh_S_M02 ameter_triv HCHECK HFRM) | exact HX01]. }
eapply SRr_srealizes; [| exact HAI |].
2: { intros W' c' Hle HAI' HQ. apply (HK _ W' c' Hle HAI'). exact HQ. }
rewrite HA.
eapply SRr_mono; [exact (rh_seg_chain segs B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK HSEG hx HB)|].
intros W' c' _ (fx' & ly' & S' & regs' & mem' & md' & k' & -> & Hfrm' & HJ' & Hk' & HPR & Ha0 & HPerm).
(* the leaf [knock APgLib.v:216-239] *)
exists fx', ly', S', regs', mem', md', k'. split; [reflexivity|]. split; [exact Hfrm'|].
destruct (rh_ajournal_nil_io segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ') as [Efds Efs].
unfold rl_lib_post_x. cbn [ll_fs ll_ret ll_out].
split; [apply rh_ajournal_fp_nil; exact HJ'|].
split; [unfold RH_EV in *; lia|]. split; [exact HPR|]. split; [exact Ha0|]. split; [exact HPerm|].
split; [intros fd; rewrite Efds; reflexivity|].
split; [exact Efs|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact HSORT|].
split; [eapply (asink_none_kept segs B K AIL); [exact HJ' | intros Ho; exact (sink_closed_nil Ho) | exact HSNK]|].
split; [exact (ameta_inv_kept segs B K AIL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ' HAM)|].
split; [exact I|].
intros i Hi. destruct Hpn as [[Hn0 _] | [Hnpos Hpin]]; [exfalso; lia|].
pose proof HJ' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
apply (F2 p n i Hpin).
- eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. exact Hpin.
- unfold req_size. destruct (Z.eqb_spec n 0) as [Heq0|Hne0]; [exfalso; lia | exact Hi].
- apply inFP_nil.
Qed.
End e.
End c.
End g.
