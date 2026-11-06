(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_knock/lib/A/APgLib.v at origin/ossv/recipes 6ebe35ba632
   (lines 132-146 ajournal_fp_nil and 156-159 ajournal_nil_io, from cgif ACfh.v; lines 207-239, the leaf of
   knock_lib_x_body: the contract's post from the walk's return state) for reac-pw/fuzz_role image A: the walk is
   role's chain of five segments over the harness-level cuts of lib/A/RPgHarn.v, with lib/A/RPgCSpec.v's two
   middle contracts in the middle and the malloc(pod) step between them; the leaf is unchanged but for the
   exists-fx' form of RPgCSpec.rl_lib_contract_x. *)
(* reac-pw/fuzz_role image A (fuzz_role.asan, pinned sha256
   614cffc0864cc31d9d1ced61322c4efd567b64bc89fe09a227a05b5126e0debb; addresses measured on the unstripped twin
   6da77bafc5c050954dd89149e1e55a24064c2211e3cbd351822d1c0a20900ad6): THE WHOLE RUN of LLVMFuzzerTestOneInput
   (0x7ff88), chained.

     role_lib_x : rl_lib_contract_x segs B ameter_triv K XM_LIB XN_LIB RLO RHI A_LLVMF RA_LLVMF ...

   from its five segments, each a Section hypothesis:
     S_E01  RPgHarn.rh_S_E01_stmt                 ENTRY 0x7ff88 -> C1 0x80194
     M01    RPgCSpec.role_build_contract (RPgMainL.role_build_holds over the build's pieces)
                                                   C1 -> C2 0x820c0
     C23    RPgHarn.rh_S_C23_stmt                 C2 -> C3 0x820c4, the malloc(pod) call
     M02    RPgCSpec.role_check_contract (RPgMainL.role_check_holds over the checks' pieces)
                                                   C3 -> C4 0x82478
     S_X01  RPgHarn.rh_S_X01_stmt                 C4 -> the return to RA_LLVMF
   and the static law of the symbols, RPgHarn.rh_static_law (the start-up's const cells and zero-shadow ranges).
   The chaining itself (this file) does three kinds of work:
   - at C1 and C3 it builds the middle contracts' rl_seg_pre from the harness cut: the journal and the cut's
     values as they are; the geometry (R mod 16, R + 0x1a0 <= S, sp0 - LLVMF_STK <= R - ASTACK) from the entry's
     astk_ok and RH_RSZ + 32 + ASTACK <= LLVMF_STK; the read-only agreement through the journal
     (RPgBase.arodata_ok_journalP); the globals', strings', cells' and read-only facts from rh_static_law at the
     cut's AR; the real frame's two checked cells from the stack's zero shadow (RPgMem.rm_A_rz); the block made
     since the entry is fresh (it is appended, and AR keeps blocks pairwise disjoint);
   - it carries what the segments after C1 need and the middle contracts do not restate (the 13 callee-saved
     words at [S - 0x68, S) and the frame's flag word at F + 0x1f8: RPgHarn.rh_kept; the frame shadow and the
     block's bytes across the malloc call) through each "outside the write set" clause (rl_seg_post's, the malloc
     rule's acall_kept), by the separations below: the stack lies above alloc_ceiling, the frame and the blocks
     below it and apart (AR_sep_law), the shadow bytes of an application address are not application addresses;
   - it turns S_X01's return state into rl_lib_post_x (knock's leaf: the journal at FP = [] weakened to the
     sink's footprint, I/O and file system kept, the sink and the meta table kept by the core's laws, the input
     bytes kept by the journal's block clause). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgBase RPgCSpec RPgImgA RPgSiteA RPgHarn RPgMem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ===================================== numbers ===================================== *)
Lemma rh_u64 : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn [Z.of_N]. lia. Qed.

Lemma rh_fs3 : fs_frame_bytes RH_CID = 512.
Proof. reflexivity. Qed.

Lemma rh_shA_len : length role_A_shA = 52%nat.
Proof. reflexivity. Qed.

Lemma rh_frame_addr_le : forall n ly ly' cid pos, layout_le n ly ly' -> frame_addr ly' cid pos = frame_addr ly cid pos.
Proof. intros n ly ly' cid pos H. unfold frame_addr. destruct H as (_ & _ & _ & _ & _ & HF & _). rewrite HF. reflexivity. Qed.

Lemma rh_flag_addr_le : forall n ly ly' cid pos, layout_le n ly ly' -> flag_addr ly' cid pos = flag_addr ly cid pos.
Proof. intros n ly ly' cid pos H. unfold flag_addr. destruct H as (_ & _ & _ & _ & _ & HF & _). rewrite HF. reflexivity. Qed.

Lemma rh_stk_le : forall n ly ly', layout_le n ly ly' -> ly_stk_lo ly' = ly_stk_lo ly /\ ly_stk_hi ly' = ly_stk_hi ly.
Proof. intros n ly ly' H. destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & H1 & H2 & _). split; assumption. Qed.

(* The real frame's base: R = 32 * floor((S - 0x1a0) / 32). *)
Lemma rh_R_facts : forall S R, R = 32 * ((S - RH_RSZ) / 32) ->
  R mod 16 = 0 /\ R + RH_RSZ <= S /\ S - RH_RSZ - 32 < R.
Proof.
intros S R ->. unfold RH_RSZ.
pose proof (Z.div_mod (S - 0x1a0) 32 ltac:(lia)) as Hd. pose proof (Z.mod_pos_bound (S - 0x1a0) 32 ltac:(lia)) as Hm.
set (q := (S - 0x1a0) / 32) in *. set (r := (S - 0x1a0) mod 32) in *.
split; [|lia]. replace (32 * q) with ((2 * q) * 16) by lia. apply Z.mod_mul. lia.
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

Lemma rh_mod16_8 : forall x, x mod 16 = 0 -> x mod 8 = 0.
Proof.
intros x H. pose proof (Z.div_mod x 16 ltac:(lia)) as Hd. rewrite H, Z.add_0_r in Hd. rewrite Hd.
replace (16 * (x / 16)) with ((2 * (x / 16)) * 8) by lia. apply Z.mod_mul. lia.
Qed.

Section n. Context {rc : YM05.RunCeil}.
(* The bytes the chaining carries (rh_kept) lie off every write set, and off the callees' stack. *)
Lemma rh_carried_off : forall S R F a,
  alloc_ceiling + ASTACK <= S - RH_RSZ - 32 -> R + RH_RSZ <= S -> S - RH_RSZ - 32 < R ->
  4096 <= F -> F + 512 <= alloc_ceiling -> in_app F 512 -> S <= 2 ^ 47 ->
  (S - 0x68 <= a < S \/ F + 0x1f8 <= a < F + 0x200) ->
  0 <= a < 2 ^ 64 /\ ~ (R - ASTACK <= a < R) /\
  ~ (F + 0x20 <= a < F + 0x180) /\ ~ (shadow_addr F <= a < shadow_addr F + 52) /\ ~ (R <= a < R + 0x138) /\
  ~ (F + 0x180 <= a < F + 0x184) /\ ~ (shadow_addr F + 0x30 <= a < shadow_addr F + 0x30 + 1) /\
  ~ (R + 0xd8 <= a < R + 0xd8 + 0x28) /\ ~ (R + 0x118 <= a < R + 0x118 + 8).
Proof.
intros S R F a Hst HR1 HR2 HF1 HF2 Happ HS Ha.
pose proof ASAN_CEIL_range as ((Hc1 & Hc2) & _). unfold ASAN_CEIL in Hc1, Hc2.
unfold shadow_addr, SHADOW_OFF, ASTACK, RH_RSZ in *. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
pose proof (Z.div_mod F 8 ltac:(lia)) as Hd. pose proof (Z.mod_pos_bound F 8 ltac:(lia)) as Hm.
set (q := F / 8) in *. set (r := F mod 8) in *.
repeat split; lia.
Qed.

Lemma rh_carried_off_block : forall S F p m a,
  alloc_ceiling <= S - 0x68 -> p + m <= alloc_ceiling -> (p + m <= F \/ F + 512 <= p) ->
  (S - 0x68 <= a < S \/ F + 0x1f8 <= a < F + 0x200) -> ~ (p <= a < p + m).
Proof. intros. lia. Qed.

(* A frame's shadow byte is not an application address (RPgMem.rm_shadow_not_app at x = F + 8 i). *)
Lemma rh_shadow_off_app : forall F i p m, in_app F 512 -> 0 <= i < 64 -> in_app p m -> ~ (p <= shadow_addr F + i < p + m).
Proof.
intros F i p m HF Hi Hp.
replace (shadow_addr F + i) with (shadow_of_addr SHADOW_OFF (F + 8 * i)) by (rewrite shadow_of_addr_add8; reflexivity).
apply (rm_shadow_not_app _ p m); [|exact Hp].
pose proof ASAN_CEIL_range as ((Hc1 & Hc2) & _). unfold ASAN_CEIL in Hc1, Hc2.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HF. unfold kHighMemEnd. lia.
Qed.
End n.

Lemma rh_inw1 : forall e a, rl_inw e (hi_w1 role_himg_A) a ->
  (e_F e + 0x20 <= a < e_F e + 0x180) \/ (shadow_addr (e_F e) <= a < shadow_addr (e_F e) + 52) \/
  (e_R e <= a < e_R e + 0x138).
Proof.
intros e a H. unfold rl_inw in H. cbn [hi_w1 role_himg_A] in H.
rewrite !Exists_cons, Exists_nil in H. cbn [rl_xv fst snd] in H. lia.
Qed.

Lemma rh_inw2 : forall e a, rl_inw e (hi_w2 role_himg_A) a ->
  (e_F e + 0x180 <= a < e_F e + 0x184) \/ (shadow_addr (e_F e) + 0x30 <= a < shadow_addr (e_F e) + 0x30 + 1) \/
  (e_R e + 0xd8 <= a < e_R e + 0xd8 + 0x28) \/ (e_R e + 0x118 <= a < e_R e + 0x118 + 8).
Proof.
intros e a H. unfold rl_inw in H. cbn [hi_w2 role_himg_A] in H.
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

(* ============================ cells and blocks across a kept clause ============================ *)
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
  (forall a, (e_S e - 0x68 <= a < e_S e \/ e_F e + 0x1f8 <= a < e_F e + 0x200) -> aview segs H' mem' a = aview segs H mem a) ->
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

Lemma rh_garr8_kept : forall H mem H' mem' a l,
  garr8 segs (mrestrict H mem) a l ->
  (forall j, 0 <= j < Z.of_nat (length l) -> aview segs H' mem' (a + j) = aview segs H mem (a + j)) ->
  garr8 segs (mrestrict H' mem') a l.
Proof.
intros H mem H' mem' a l Hg Hk j Hj. destruct (Hg j Hj) as [Hv Hb]. split; [|exact Hb].
intros k Hlt.
rewrite (mbyte_of_aview segs H H' mem mem'); [exact (Hv k Hlt)|].
rewrite <- Z.add_assoc. apply Hk. lia.
Qed.

(* the carried cells read only S and F of the run's quantities *)
Lemma rh_kept_env : forall (hx : rh_hcx segs) pos e pod W mem regs,
  rh_kept segs hx pos e W mem regs -> rh_kept segs hx pos (rh_env_pod e pod) W mem regs.
Proof.
intros hx pos e pod W mem regs HK. unfold rh_kept in *. rewrite Forall_forall in HK |- *.
intros f Hf. pose proof (HK f Hf) as Hv. unfold rh_cells, rh_saves_L in Hf. apply in_app_iff in Hf as [Hf|Hf].
- apply in_map_iff in Hf as (j & <- & _). exact Hv.
- destruct Hf as [<-|[]]. exact Hv.
Qed.

(* A block appended to the blocks is not among those before it. *)
Lemma rh_fresh_app : forall ly S W mem md l x,
  AR segs B ly S W mem md -> ablocks B ly S = l ++ [x] -> ~ In x l.
Proof.
intros ly S W mem md l x HAR E Hin. apply in_split in Hin as (l1 & l2 & ->).
assert (Hx : In x (ablocks B ly S)) by (rewrite E; apply in_or_app; right; left; reflexivity).
destruct x as [p n].
pose proof (al_blocks _ _ LAWS ly S W mem md p n HAR Hx) as (_ & _ & _ & _ & _ & _ & Hn).
assert (Hd : zdisjoint (block_rng (p, n)) (block_rng (p, n))).
{ apply (sep_blocks_pos segs B LAWS ly S W mem md (p, n) (p, n) l1 l2 [] HAR). rewrite E, <- app_assoc. reflexivity. }
unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. unfold req_size in Hd. destruct (Z.eqb_spec n 0); lia.
Qed.

Section c.
Variables RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK : Z.
Hypothesis HSTK : RH_RSZ + 32 + ASTACK <= LLVMF_STK.
Hypothesis HEV : RH_EV <= EV_LIB.
Hypothesis HRELRO : forall a, RLO <= a < RHI -> in_img segs a.
Context {RO : ro_below_ofl segs RLO RHI}.
Hypothesis HSTAT : rh_static_law segs B RLO RHI.

Local Notation BASE := (rh_base segs B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK).
Local Notation J := (rh_j segs B LLVMF_STK).

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
  e_F e = frame_addr ly' RH_CID pos /\ 4096 <= e_F e /\ e_F e + 512 <= alloc_ceiling /\ in_app (e_F e) 512.
Proof.
intros hx pos e own ly' S' W' mem' md' k HB (_ & _ & HF) HJ Hin.
pose proof HJ as (HAR & Hly & _).
assert (EF : e_F e = frame_addr ly' RH_CID pos) by (rewrite HF; symmetry; exact (rh_frame_addr_le _ _ _ _ _ Hly)).
destruct (al_sep _ _ LAWS _ _ _ _ _ HAR) as [_ Hf]. rewrite Forall_forall in Hf. pose proof (Hf _ Hin) as Hb.
destruct (al_frames _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & Happ & _).
cbn [fst snd] in Hb. rewrite rh_fs3 in Hb, Happ. rewrite <- EF in Hb, Happ.
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

(* ============================ C1: role_build_contract's start ============================ *)
Lemma rh_C1_pre : forall hx pos e rest ly1 S1 W1 regs1 mem1 md1,
  BASE hx -> rh_cut_C1 segs B LLVMF_STK hx pos e rest ly1 S1 W1 regs1 mem1 md1 ->
  rl_seg_pre segs B LLVMF_STK (spZ (h_regs hx)) [] (h_ly hx) (h_S hx) (h_W hx) (h_mem hx) (h_md hx)
  [(RH_CID, pos)] 1 regs1 ly1 S1 W1 mem1 md1 role_himg_A RLO RHI e pos.
Proof.
intros hx pos e rest ly1 S1 W1 regs1 mem1 md1 HB HC.
pose proof HB as HB'. destruct HB' as (_ & _ & _ & _ & _ & _ & _ & Hfr0 & Hev & _ & HROS).
destruct HC as (HJ & Hab & Hr2 & Hr3 & Hr4 & Hgeo & Hfsh & Hpp & Hfl & _ & _ & _).
pose proof (rh_geo_facts hx pos e HB Hgeo) as (Hst & HS16 & Hlo & Hlos & Hhi & H47 & HR16 & HR1 & HR2 & HRs & HRlo).
pose proof HJ as (HAR1 & Hly1 & _ & _ & _ & Hfr1 & Hnev1 & _).
destruct (rh_stk_le _ _ _ Hly1) as [Elo Ehi].
assert (Hin3 : In (RH_CID, pos) (frames S1)) by (rewrite Hfr1; left; reflexivity).
destruct (rh_frame_facts hx pos e _ _ _ _ _ _ _ HB Hgeo HJ Hin3) as (EF & _).
assert (Haro : arodata_okP segs RLO RHI B (aview segs (w_H W1) mem1)).
{ exact (arodata_ok_journalP segs RLO RHI HRELRO B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HROS). }
destruct (HSTAT ly1 S1 W1 mem1 md1 HAR1 Haro) as (Hg & Hs & Hc & Hrom).
destruct Hgeo as (HS & _ & _).
unfold rl_seg_pre. cbn [hi_rsz hi_cid hi_shA hi_globs hi_strs hi_cells hi_rz role_himg_A].
split; [exact HJ|].
split; [unfold RH_EV in HEV; lia|].
split; [exact Hr2|]. split; [exact Hr3|]. split; [exact Hr4|].
split; [exact HS|]. split; [exact HR16|]. split; [unfold RH_RSZ in HR1; lia|].
split; [unfold T_SEG_STK; rewrite <- HS; lia|].
split; [left; reflexivity|].
split; [exact EF|].
split; [exact Hfsh|].
split; [exact Hpp|].
split; [rewrite Hab; apply in_or_app; right; left; reflexivity|].
split; [exact Hfl|].
split; [exact Haro|].
split; [exact Hg|].
split.
{ apply (rm_A_rz segs B ly1 S1 W1 mem1 md1 (e_R e) (e_S e) HAR1);
  [rewrite Elo; lia | unfold RH_RSZ in HR1; lia | rewrite Ehi; lia | exact (rh_mod16_8 _ HS16)]. }
split; [exact Hs|]. split; [exact Hc|]. split; [exact Hrom|].
exact (rh_fresh_app ly1 S1 W1 mem1 md1 _ _ HAR1 Hab).
Qed.

(* ============================ C2: what role_build_contract's post gives the malloc step ============================ *)
Lemma rh_C2_cut : forall hx pos e rest ly1 S1 W1 regs1 mem1 md1 ly2 S2 W2 regs2 mem2 md2,
  BASE hx -> rh_cut_C1 segs B LLVMF_STK hx pos e rest ly1 S1 W1 regs1 mem1 md1 ->
  J hx [(RH_CID, pos)] ly2 S2 W2 mem2 md2 1 ->
  (forall r : Z, r = 2 \/ r = 3 \/ r = 4 -> getr regs2 (Z_to_bv 5 r) = getr regs1 (Z_to_bv 5 r)) ->
  Permutation (ablocks B ly2 S2) (ablocks B ly1 S1) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs1 - T_SEG_STK <= a < spZ regs1) ->
   ~ (rl_inw e (hi_w1 role_himg_A) a \/ e_pp e <= a < e_pp e + Layout.PP_SIZE) ->
   aview segs (w_H W2) mem2 a = aview segs (w_H W1) mem1 a) ->
  rl_cut segs (w_H W2) mem2 regs2 e (hi_L2 role_himg_A) ->
  rh_cut_C2 segs B LLVMF_STK hx pos e ly2 S2 W2 regs2 mem2 md2.
Proof.
intros hx pos e rest ly1 S1 W1 regs1 mem1 md1 ly2 S2 W2 regs2 mem2 md2 HB HC HJ2 Hr Hperm Hkeep HL2.
destruct HC as (HJ1 & Hab & Hr2 & Hr3 & Hr4 & Hgeo & _ & _ & _ & _ & Hin & Hkept).
pose proof (rh_geo_facts hx pos e HB Hgeo) as (Hst & HS16 & Hlo & Hlos & Hhi & H47 & HR16 & HR1 & HR2 & HRs & HRlo).
pose proof HJ1 as (_ & _ & _ & _ & _ & Hfr1 & _).
assert (Hin3 : In (RH_CID, pos) (frames S1)) by (rewrite Hfr1; left; reflexivity).
destruct (rh_frame_facts hx pos e _ _ _ _ _ _ _ HB Hgeo HJ1 Hin3) as (EF & HF1 & HF2 & HFapp).
assert (Hpp1 : In (e_pp e, Layout.PP_SIZE) (ablocks B ly1 S1)) by (rewrite Hab; apply in_or_app; right; left; reflexivity).
destruct (rh_block_facts hx _ _ _ _ _ _ _ _ _ HJ1 Hpp1) as (Hppc & _ & _).
pose proof HJ1 as (HAR1 & _).
pose proof (sep_block_frame segs B LAWS _ _ _ _ _ _ _ _ _ HAR1 Hpp1 Hin3) as Hsep. rewrite rh_fs3, <- EF in Hsep.
unfold zdisjoint in Hsep. cbn [fst snd] in Hsep.
assert (EspR : spZ regs1 = e_R e).
{ unfold spZ. rewrite Hr2. unfold w64. apply rh_u64. unfold RH_RSZ, ASTACK in *. lia. }
destruct Hin as (_ & Hlen & _).
unfold rh_cut_C2.
split; [exact HJ2|].
split; [rewrite <- Hab; exact Hperm|].
split; [rewrite <- Hr2; exact (Hr 2 (or_introl eq_refl))|].
split; [rewrite <- Hr3; exact (Hr 3 (or_intror (or_introl eq_refl)))|].
split; [rewrite <- Hr4; exact (Hr 4 (or_intror (or_intror eq_refl)))|].
split; [exact Hgeo|].
split; [rewrite Hlen; exact (rl_len_bounds rest)|].
split; [exact HL2|].
unfold rh_kept. apply (rh_kept_tr hx pos e _ _ _ _ regs1 regs2 Hkept).
intros a Ha. destruct Hgeo as (HS & _ & _).
destruct (rh_carried_off (e_S e) (e_R e) (e_F e) a Hst HR1 HR2 HF1 HF2 HFapp (ltac:(lia)) Ha)
  as (Ha64 & HaR & Hw1 & Hw2 & Hw3 & _).
apply Hkeep; [exact Ha64 | unfold T_SEG_STK; rewrite EspR; exact HaR |].
intros [Hw|Hw].
- apply rh_inw1 in Hw. lia.
- assert (Hreq : req_size Layout.PP_SIZE = Layout.PP_SIZE) by reflexivity.
  rewrite Hreq in Hppc, Hsep.
  exact (rh_carried_off_block (e_S e) (e_F e) (e_pp e) Layout.PP_SIZE a ltac:(unfold RH_RSZ, ASTACK in Hst; lia)
    Hppc ltac:(lia) Ha Hw).
Qed.

(* ============================ C3: role_check_contract's start ============================ *)
Lemma rh_C3 : forall hx pos e rest ly2 S2 W2 regs2 mem2 md2 W3 c3,
  BASE hx -> rh_cut_C2 segs B LLVMF_STK hx pos e ly2 S2 W2 regs2 mem2 md2 ->
  rl_fsh segs (w_H W2) mem2 (e_F e) role_A_shA ->
  garr8 segs (mrestrict (w_H W2) mem2) (e_pp e)
    (map (fun x : byte => bv_unsigned x) (Layout.pp_bytes (fst (Model.pod_build rest)))) ->
  e_len e = rl_len rest -> e_pp e <> 0 -> 0 <= e_fl e < 256 ->
  ~ In (e_pp e, Layout.PP_SIZE) (ablocks B (h_ly hx) (h_S hx)) ->
  rh_at_C3 segs B LLVMF_STK hx pos e ly2 S2 W2 regs2 mem2 W3 c3 ->
  exists pod ly3 S3 regs3 mem3 md3, c3 = cfg_at segs RH_C3 regs3 mem3 md3 /\
  rl_seg_pre segs B LLVMF_STK (spZ (h_regs hx)) [] (h_ly hx) (h_S hx) (h_W hx) (h_mem hx) (h_md hx)
    [(RH_CID, pos)] 2 regs3 ly3 S3 W3 mem3 md3 role_himg_A RLO RHI (rh_env_pod e pod) pos /\
  rl_cut segs (w_H W3) mem3 regs3 (rh_env_pod e pod) (hi_L3 role_himg_A) /\
  garr8 segs (mrestrict (w_H W3) mem3) (e_pp e)
    (map (fun x : byte => bv_unsigned x) (Layout.pp_bytes (fst (Model.pod_build rest)))) /\
  pod <> 0 /\ In (pod, e_len e) (ablocks B ly3 S3) /\ ~ In (pod, e_len e) (ablocks B (h_ly hx) (h_S hx)) /\
  rh_kept segs hx pos (rh_env_pod e pod) W3 mem3 regs3 /\
  Permutation (ablocks B ly3 S3) (ablocks B (h_ly hx) (h_S hx) ++ [(e_pp e, Layout.PP_SIZE); (pod, e_len e)]).
Proof.
intros hx pos e rest ly2 S2 W2 regs2 mem2 md2 W3 c3 HB HC2 Hfsh2 Hpp2 Hlen Hpp0 Hfl Hfrpp HA3.
destruct HA3 as (pod & ly3 & S3 & regs3 & mem3 & md3 & Ec3 & HJ3 & Hpod & Ha0 & Hcs & Hfr3 & Hab3 & Hkc).
destruct HC2 as (HJ2 & Hperm2 & Hr2 & Hr3 & Hr4 & Hgeo & Hlenb & HL2 & Hkept2).
exists pod, ly3, S3, regs3, mem3, md3. split; [exact Ec3|].
pose proof HB as HB'. destruct HB' as (_ & _ & _ & _ & _ & _ & _ & Hfr0 & Hev & _ & HROS).
pose proof (rh_geo_facts hx pos e HB Hgeo) as (Hst & HS16 & Hlo & Hlos & Hhi & H47 & HR16 & HR1 & HR2 & HRs & HRlo).
pose proof HJ2 as (_ & _ & _ & _ & _ & Hfr2 & _).
pose proof HJ3 as (HAR3 & Hly3 & _ & _ & _ & Hfrs3 & _).
assert (Hin2 : In (RH_CID, pos) (frames S2)) by (rewrite Hfr2; left; reflexivity).
assert (Hin3 : In (RH_CID, pos) (frames S3)) by (rewrite Hfr3; exact Hin2).
destruct (rh_frame_facts hx pos e _ _ _ _ _ _ _ HB Hgeo HJ3 Hin3) as (EF3 & HF1 & HF2 & HFapp).
destruct (rh_frame_facts hx pos e _ _ _ _ _ _ _ HB Hgeo HJ2 Hin2) as (EF2 & _).
assert (Hpod3 : In (pod, e_len e) (ablocks B ly3 S3)) by (rewrite Hab3; apply in_or_app; right; left; reflexivity).
assert (Hpp2in : In (e_pp e, Layout.PP_SIZE) (ablocks B ly2 S2)).
{ apply (Permutation_in _ (Permutation_sym Hperm2)). apply in_or_app. right. left. reflexivity. }
assert (Hpp3 : In (e_pp e, Layout.PP_SIZE) (ablocks B ly3 S3)) by (rewrite Hab3; apply in_or_app; left; exact Hpp2in).
destruct (rh_block_facts hx _ _ _ _ _ _ _ _ _ HJ3 Hpod3) as (Hpodc & Hpodapp & _).
destruct (rh_block_facts hx _ _ _ _ _ _ _ _ _ HJ3 Hpp3) as (Hppc & _ & _).
pose proof (sep_block_frame segs B LAWS _ _ _ _ _ _ _ _ _ HAR3 Hpod3 Hin3) as Hsep. rewrite rh_fs3, <- EF3 in Hsep.
unfold zdisjoint in Hsep. cbn [fst snd] in Hsep.
assert (Hne : (e_pp e, Layout.PP_SIZE) <> (pod, e_len e)).
{ intros E. injection E as _ E. unfold Layout.PP_SIZE in E. lia. }
pose proof (sep_blocks segs B LAWS _ _ _ _ _ _ _ _ _ HAR3 Hpp3 Hpod3 Hne) as Hsepb.
unfold zdisjoint in Hsepb. cbn [fst snd] in Hsepb.
assert (Hreqpp : req_size Layout.PP_SIZE = Layout.PP_SIZE) by reflexivity.
destruct Hkc as (Kc1 & Kc2 & Kc3 & Kc4 & _ & _).
(* the frame shadow, kept by the call *)
assert (Hfsh3 : rl_fsh segs (w_H W3) mem3 (e_F e) role_A_shA).
{ intros i Hi. rewrite rh_shA_len in Hi. rewrite (Kc4 RH_CID pos (shadow_addr (e_F e) + i) Hin2).
  - apply (Hfsh2 i). rewrite rh_shA_len. exact Hi.
  - right. unfold in_zr. cbn [fst snd]. rewrite rh_fs3, <- EF2. change (512 / 8) with 64. lia.
  - exact (rh_shadow_off_app (e_F e) i pod (req_size (e_len e)) HFapp ltac:(lia) Hpodapp). }
(* the block's bytes, kept by the call *)
assert (Hpp3b : garr8 segs (mrestrict (w_H W3) mem3) (e_pp e)
  (map (fun x : byte => bv_unsigned x) (Layout.pp_bytes (fst (Model.pod_build rest))))).
{ apply (rh_garr8_kept _ _ _ _ _ _ Hpp2). intros j Hj.
  assert (Hwf : Model.pod_rec_wf (fst (Model.pod_build rest))).
  { destruct (Model.pod_build rest) as [rr rest'] eqn:Epb. exact (Model.pod_build_wf rest rr rest' Epb). }
  pose proof (Layout.length_pp_bytes _ Hwf) as Hl.
  rewrite length_map, Hl in Hj. rewrite Hreqpp in Hsepb.
  apply (Kc2 (e_pp e) Layout.PP_SIZE j Hpp2in); [rewrite Hreqpp; exact Hj|]. cbn beta. lia. }
(* the carried cells, kept by the call *)
assert (Hkept3 : rh_kept segs hx pos e W3 mem3 regs3).
{ unfold rh_kept. apply (rh_kept_tr hx pos e _ _ _ _ regs2 regs3 Hkept2).
  intros a Ha. destruct Hgeo as (HS & _ & _).
  destruct (rh_carried_off (e_S e) (e_R e) (e_F e) a Hst HR1 HR2 HF1 HF2 HFapp (ltac:(lia)) Ha) as (_ & HaR & _).
  destruct Ha as [Ha|Ha].
  - apply Kc1; [unfold RH_RSZ, ASTACK in Hst; split; lia | exact HaR].
  - apply (Kc4 RH_CID pos a Hin2); [left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite rh_fs3, <- EF2; lia | cbn beta; lia]. }
(* the registers *)
assert (Hcs' : forall r, acallee_saved r -> getr regs3 (Z_to_bv 5 r) = getr regs2 (Z_to_bv 5 r)) by exact Hcs.
assert (Hfrpod : ~ In (pod, e_len e) (ablocks B (h_ly hx) (h_S hx))).
{ intros Hx. apply (rh_fresh_app ly3 S3 W3 mem3 md3 _ _ HAR3 Hab3).
  apply (Permutation_in _ (Permutation_sym Hperm2)). apply in_or_app. left. exact Hx. }
assert (Haro : arodata_okP segs RLO RHI B (aview segs (w_H W3) mem3)).
{ exact (arodata_ok_journalP segs RLO RHI HRELRO B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3 HROS). }
destruct (HSTAT ly3 S3 W3 mem3 md3 HAR3 Haro) as (Hg & Hs & Hc & Hrom).
destruct (rh_stk_le _ _ _ Hly3) as [Elo Ehi].
split.
{ unfold rl_seg_pre. cbn [hi_rsz hi_cid hi_shA hi_globs hi_strs hi_cells hi_rz role_himg_A rh_env_pod e_S e_R e_F e_pp e_fl].
  destruct Hgeo as (HS & _ & _).
  split; [exact HJ3|].
  split; [unfold RH_EV in HEV; lia|].
  split; [transitivity (getr regs2 (Z_to_bv 5 2)); [exact (Hcs 2 ltac:(unfold acallee_saved; lia)) | exact Hr2]|].
  split; [transitivity (getr regs2 (Z_to_bv 5 3)); [exact (Hcs 3 ltac:(unfold acallee_saved; lia)) | exact Hr3]|].
  split; [transitivity (getr regs2 (Z_to_bv 5 4)); [exact (Hcs 4 ltac:(unfold acallee_saved; lia)) | exact Hr4]|].
  split; [exact HS|]. split; [exact HR16|]. split; [unfold RH_RSZ in HR1; lia|].
  split; [unfold T_SEG_STK; rewrite <- HS; lia|].
  split; [left; reflexivity|].
  split; [exact EF3|].
  split; [exact Hfsh3|].
  split; [exact Hpp0|].
  split; [exact Hpp3|].
  split; [exact Hfl|].
  split; [exact Haro|].
  split; [exact Hg|].
  split.
  { apply (rm_A_rz segs B ly3 S3 W3 mem3 md3 (e_R e) (e_S e) HAR3);
    [rewrite Elo; lia | unfold RH_RSZ in HR1; lia | rewrite Ehi; lia | exact (rh_mod16_8 _ HS16)]. }
  split; [exact Hs|]. split; [exact Hc|]. split; [exact Hrom|]. exact Hfrpp. }
split.
{ (* the C3 values from the C2 values: a0 = pod, the callee-saved registers and the R-relative cells kept *)
  unfold rl_cut in *. cbn [hi_L2 hi_L3 role_himg_A] in *. unfold role_A_L23 in *.
  rewrite !Forall_cons_iff in HL2.
  destruct HL2 as (_ & C8 & C9 & C19 & C21 & C23 & C24 & C25 & C26 & C27 & R8 & R28 & R30 & R68 & R78 & R80 & _).
  cbn [fst snd rl_at rl_xv] in *.
  assert (Hcell : forall o v, In o [0x8; 0x28; 0x30; 0x68; 0x78; 0x80] ->
    val_mem segs (mrestrict (w_H W2) mem2) (e_R e + o) 8 v -> val_mem segs (mrestrict (w_H W3) mem3) (e_R e + o) 8 v).
  { intros o v Ho Hv k Hk. rewrite (mbyte_of_aview segs (w_H W2) (w_H W3) mem2 mem3); [exact (Hv k Hk)|].
    cbn [In] in Ho. destruct Hgeo as (HS & _ & _). unfold RH_RSZ, ASTACK in *. apply Kc1; [split|]; lia. }
  assert (Hreg : forall r, acallee_saved r -> forall v, getr regs2 (Z_to_bv 5 r) = v -> getr regs3 (Z_to_bv 5 r) = v).
  { intros r Hr v Hv. rewrite (Hcs r Hr). exact Hv. }
  repeat (apply Forall_cons; [cbn [fst snd rl_at rl_xv rh_env_pod e_S e_R e_F e_pp e_pod e_len e_fl] |]);
  [| | | | | | | | | | | | | | | | apply Forall_nil];
  first
  [ exact Ha0
  | (apply Hreg; [unfold acallee_saved; lia | assumption])
  | (apply Hcell; [cbn [In]; lia | assumption]) ]. }
split; [exact Hpp3b|].
split; [lia|].
split; [exact Hpod3|].
split; [exact Hfrpod|].
split; [exact (rh_kept_env hx pos e pod W3 mem3 regs3 Hkept3)|].
rewrite Hab3. replace (ablocks B (h_ly hx) (h_S hx) ++ [(e_pp e, Layout.PP_SIZE); (pod, e_len e)])
  with ((ablocks B (h_ly hx) (h_S hx) ++ [(e_pp e, Layout.PP_SIZE)]) ++ [(pod, e_len e)])
  by (rewrite <- app_assoc; reflexivity).
apply Permutation_app_tail. exact Hperm2.
Qed.

(* ============================ C4: what role_check_contract's post gives S_X01 ============================ *)
Lemma rh_C4_cut : forall hx pos e ly3 S3 W3 regs3 mem3 ly4 S4 W4 regs4 mem4 md4,
  BASE hx -> rh_geo segs hx pos e -> 8 <= e_len e <= 5440 -> e_pp e <> 0 -> e_pod e <> 0 ->
  getr regs3 2 = w64 (e_R e) -> getr regs3 3 = w64 (as_gp B) -> getr regs3 4 = w64 (as_tp B) ->
  ~ In (e_pp e, Layout.PP_SIZE) (ablocks B (h_ly hx) (h_S hx)) ->
  ~ In (e_pod e, e_len e) (ablocks B (h_ly hx) (h_S hx)) ->
  Permutation (ablocks B ly3 S3) (ablocks B (h_ly hx) (h_S hx) ++ [(e_pp e, Layout.PP_SIZE); (e_pod e, e_len e)]) ->
  rh_kept segs hx pos e W3 mem3 regs3 ->
  J hx [(RH_CID, pos)] ly4 S4 W4 mem4 md4 2 ->
  (forall r : Z, r = 2 \/ r = 3 \/ r = 4 -> getr regs4 (Z_to_bv 5 r) = getr regs3 (Z_to_bv 5 r)) ->
  Permutation (ablocks B ly4 S4) (ablocks B ly3 S3) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs3 - T_SEG_STK <= a < spZ regs3) ->
   ~ (rl_inw e (hi_w2 role_himg_A) a \/ e_pod e <= a < e_pod e + e_len e) ->
   aview segs (w_H W4) mem4 a = aview segs (w_H W3) mem3 a) ->
  rl_cut segs (w_H W4) mem4 regs4 e (hi_L4 role_himg_A) ->
  rl_fsh segs (w_H W4) mem4 (e_F e) role_A_shB ->
  rh_cut_C4 segs B LLVMF_STK hx pos e ly4 S4 W4 regs4 mem4 md4.
Proof.
intros hx pos e ly3 S3 W3 regs3 mem3 ly4 S4 W4 regs4 mem4 md4 HB Hgeo Hlenb Hpp0 Hpod0 Hr2 Hr3 Hr4
  Hfrpp Hfrpod Hperm3 Hkept3 HJ4 Hr Hperm4 Hkeep HL4 Hfsh4.
pose proof (rh_geo_facts hx pos e HB Hgeo) as (Hst & HS16 & Hlo & Hlos & Hhi & H47 & HR16 & HR1 & HR2 & HRs & HRlo).
pose proof HJ4 as (HAR4 & _ & _ & _ & _ & Hfr4 & _).
assert (Hin4 : In (RH_CID, pos) (frames S4)) by (rewrite Hfr4; left; reflexivity).
destruct (rh_frame_facts hx pos e _ _ _ _ _ _ _ HB Hgeo HJ4 Hin4) as (EF4 & HF1 & HF2 & HFapp).
assert (Hperm : Permutation (ablocks B ly4 S4)
  (ablocks B (h_ly hx) (h_S hx) ++ [(e_pp e, Layout.PP_SIZE); (e_pod e, e_len e)]))
  by exact (Permutation_trans Hperm4 Hperm3).
assert (Hpod4 : In (e_pod e, e_len e) (ablocks B ly4 S4)).
{ apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. right. left. reflexivity. }
destruct (rh_block_facts hx _ _ _ _ _ _ _ _ _ HJ4 Hpod4) as (Hpodc & _ & Hlen0).
pose proof (sep_block_frame segs B LAWS _ _ _ _ _ _ _ _ _ HAR4 Hpod4 Hin4) as Hsep. rewrite rh_fs3, <- EF4 in Hsep.
unfold zdisjoint in Hsep. cbn [fst snd] in Hsep.
assert (EspR : spZ regs3 = e_R e).
{ unfold spZ. rewrite Hr2. unfold w64. apply rh_u64. unfold RH_RSZ, ASTACK in *. lia. }
unfold rh_cut_C4.
split; [exact HJ4|]. split; [exact Hperm|]. split; [exact Hfrpp|]. split; [exact Hfrpod|].
split; [rewrite <- Hr2; exact (Hr 2 (or_introl eq_refl))|].
split; [rewrite <- Hr3; exact (Hr 3 (or_intror (or_introl eq_refl)))|].
split; [rewrite <- Hr4; exact (Hr 4 (or_intror (or_intror eq_refl)))|].
split; [exact Hgeo|]. split; [exact Hlenb|]. split; [exact Hpp0|]. split; [exact Hpod0|].
split; [exact HL4|]. split; [exact Hfsh4|].
unfold rh_kept. apply (rh_kept_tr hx pos e _ _ _ _ regs3 regs4 Hkept3).
intros a Ha. destruct Hgeo as (HS & _ & _).
destruct (rh_carried_off (e_S e) (e_R e) (e_F e) a Hst HR1 HR2 HF1 HF2 HFapp (ltac:(lia)) Ha)
  as (Ha64 & HaR & _ & _ & _ & Hv1 & Hv2 & Hv3 & Hv4).
apply Hkeep; [exact Ha64 | unfold T_SEG_STK; rewrite EspR; exact HaR |].
intros [Hw|Hw].
- apply rh_inw2 in Hw. lia.
- assert (Hb : ~ (e_pod e <= a < e_pod e + req_size (e_len e))).
  { apply (rh_carried_off_block (e_S e) (e_F e) (e_pod e) (req_size (e_len e)) a);
    [unfold RH_RSZ, ASTACK in Hst; lia | exact Hpodc | lia | exact Ha]. }
  apply Hb. unfold req_size. destruct (Z.eqb_spec (e_len e) 0); lia.
Qed.

(* ============================ the whole run ============================ *)
Variable K : asink_syms.
Variables XM_LIB XN_LIB : Z -> Z.
Variable A_LLVMF : Z.
Context {LS : lib_shape}.
(* the harness's entry (image A: the relocated frame's ACfn.A_LLVMF; by computation) *)
Hypothesis HA : A_LLVMF = RH_ENTRY.
(* the core's sink laws at the symbols (knock: AD1u.tfib_AIL) *)
Hypothesis AIL : asink_img_laws segs B K.
(* the lib shape's one-leaf law (role_lib_x_all_stmt's first premise) *)
Hypothesis LEAF : forall pl fs (Kl : lleaf -> TSet), LIBK pl fs Kl = Kl (LL 0 fs []).
(* S_E01: ENTRY -> C1 *)
Hypothesis HE01 : rh_S_E01_stmt segs B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK.
(* M01: RPgMainL.role_build_holds *)
Hypothesis HBUILD : role_build_contract segs B ameter_triv role_himg_A RLO RHI.
(* the malloc(pod) step: C2 -> C3 *)
Hypothesis HC23 : rh_S_C23_stmt segs B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK.
(* M02: RPgMainL.role_check_holds *)
Hypothesis HCHECK : role_check_contract segs B ameter_triv role_himg_A RLO RHI.
(* S_X01: C4 -> the return, at every float state *)
Hypothesis HX01 : forall fx' : YK11.FPState,
  rh_S_X01_stmt (fx := fx') segs B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK.

Theorem role_lib_x : rl_lib_contract_x segs B ameter_triv K XM_LIB XN_LIB RLO RHI
  A_LLVMF RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK.
Proof.
intros ly S W regs mem md p n pl M Kl HAI HPRE HK.
rewrite LEAF.
destruct HPRE as (HPRE0 & Hra & Hp & Hn & Hpn & Hnpl & HPL & Hfr0 & Hev & Hlive & HROS & HSNK & HFD & HSORT
  & HAM & HMOK & HFRM).
set (hx := {| h_ly := ly; h_S := S; h_W := W; h_regs := regs; h_mem := mem; h_md := md; h_p := p; h_n := n;
  h_pl := pl |} : rh_hcx segs).
assert (HB : rh_base segs B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK hx).
{ exact (conj HPRE0 (conj Hra (conj Hp (conj Hn (conj Hpn (conj Hnpl (conj HPL (conj Hfr0 (conj Hev
    (conj Hlive HROS)))))))))). }
eapply SRr_srealizes; [| exact HAI |].
2: { intros W' c' Hle HAI' HQ. apply (HK _ W' c' Hle HAI'). exact HQ. }
rewrite HA.
(* S_E01 *)
eapply SRr_bind; [exact (HE01 hx HB)|].
intros W1 c1 _ (pos & e & rest & ly1 & S1 & regs1 & mem1 & md1 & -> & HC1).
pose proof (rh_C1_pre hx pos e rest ly1 S1 W1 regs1 mem1 md1 HB HC1) as HPRE1.
pose proof HC1 as (_ & _ & _ & _ & _ & Hgeo & _ & Hpp0 & Hfl & HL1 & Hin & _).
pose proof Hin as (Hleft & Hlen & Harr & Hra1 & Hsrc & Hhi & Hamem & Hhull & Hdis).
assert (Hfrpp := HPRE1). unfold rl_seg_pre in Hfrpp.
repeat match type of Hfrpp with _ /\ _ => destruct Hfrpp as [_ Hfrpp] end.
(* M01 *)
eapply SRr_bind; [exact (HBUILD LLVMF_STK (spZ regs) [] ly S W mem md [(RH_CID, pos)] ly1 S1 W1 mem1 md1 1 regs1
  e pos rest HPRE1 HL1 Hleft Hlen Harr Hra1 Hsrc Hhi Hamem Hhull Hdis)|].
intros W2 c2 _ (fx2 & ly2 & S2 & regs2 & mem2 & md2 & Ec2 & Efx & HJ2 & Hr2 & Hfr2 & Hperm2 & Hio2 & Hmo2 & Hkept2
  & HL2 & Hfsh2 & Hpp2).
subst fx2. subst c2.
pose proof (rh_C2_cut hx pos e rest ly1 S1 W1 regs1 mem1 md1 ly2 S2 W2 regs2 mem2 md2
  HB HC1 HJ2 Hr2 Hperm2 Hkept2 HL2) as HC2.
(* the malloc(pod) step *)
eapply SRr_bind; [exact (HC23 hx pos e ly2 S2 W2 regs2 mem2 md2 HB HC2)|].
intros W3 c3 _ HA3.
destruct (rh_C3 hx pos e rest ly2 S2 W2 regs2 mem2 md2 W3 c3 HB HC2 Hfsh2 Hpp2 Hlen Hpp0 Hfl Hfrpp HA3)
  as (pod & ly3 & S3 & regs3 & mem3 & md3 & -> & HPRE3 & HL3 & Hpp3 & Hpod0 & Hpod3 & Hfrpod & Hkept3 & Hperm3).
pose proof HPRE3 as (_ & _ & Hr32 & Hr33 & Hr34 & _).
(* M02 *)
eapply SRr_bind; [exact (HCHECK LLVMF_STK (spZ regs) [] ly S W mem md [(RH_CID, pos)] ly3 S3 W3 mem3 md3 2 regs3
  (rh_env_pod e pod) pos rest HPRE3 HL3 Hlen Hpp3 Hpod0 Hpod3 Hfrpod HFRM)|].
intros W4 c4 _ (fx4 & ly4 & S4 & regs4 & mem4 & md4 & -> & Hfxk & HJ4 & Hr4 & Hfr4 & Hperm4 & Hio4 & Hmo4 & Hkept4
  & HL4 & Hfsh4).
pose proof HC2 as (_ & _ & _ & _ & _ & _ & Hlenb & _).
pose proof (rh_C4_cut hx pos (rh_env_pod e pod) ly3 S3 W3 regs3 mem3 ly4 S4 W4 regs4 mem4 md4
  HB Hgeo Hlenb Hpp0 Hpod0 Hr32 Hr33 Hr34 Hfrpp Hfrpod Hperm3 Hkept3 HJ4 Hr4 Hperm4 Hkept4 HL4 Hfsh4) as HC4.
(* S_X01, at the float state M02 returns at *)
eapply SRr_mono; [exact (HX01 fx4 hx pos (rh_env_pod e pod) ly4 S4 W4 regs4 mem4 md4 HB HC4)|].
intros W' c' _ (ly' & S' & regs' & mem' & md' & k' & -> & HJ' & Hk' & HPR & Ha0 & HPerm).
(* the leaf [knock APgLib.v:216-239] *)
exists fx4, ly', S', regs', mem', md', k'. split; [reflexivity|]. split; [exact (proj2 Hfxk)|].
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
End c.
End g.

Print Assumptions role_lib_x.
