(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-30: KF-COUNT F3: HLS1 carries gn_cst (relay_instance_gone's cost at q = 0) *)
(* Theorem Labs, 2026-10: the ARx-GENERIC twin of ARM_gone's phase p3 on image B (lib/B/W_LLVMFuzzerTestOneInput_gone_p3.v,
   a Theorem Labs lane's fee5272ac13 with our adaptation to the kit's CTX_AFREE rig_spec, 4c35818d04c: the relay_instance_gone
   call, GRG to GC1), for the conversion of ARM_gone to the cut invariants of lib/B/W_LLVMFuzzerTestOneInput_cut_x.v.
   _gone_p3.v is not edited.
   - CITED from _gone_p3.v: its AR-free names (gp3_G_RIG, gp3_not_RIG, gp3_rom_out, gp3_others, gp3_errno_g4, ...), with
     the Section variables they were generalized over;
   - RESTATED under their names + _x, merged per item with SmallX's image-A twin
     lib/A/W_LLVMFuzzerTestOneInput_gone_p3_x.v (95a5de32ab2): the journal-keep and slot lemmas that read AR
     (gp3_inner_x, gp3_keeps_x, gp3_slot_kept_x, ...), the callee's afn_pre_x at sp = F (gp3_afn_pre_x, with the chain's
     spine and the room above sp that rig_spec's caller-context premise names), and the phase lemma gp3_rig_c1_x.
   Section hypotheses beyond cut_x's header: _gone.v's RIG in its kit _x form (rig_spec_x at image B's K0 table
   YCk0.CTX_AFREE), RGP, HGRIG, HPAIRS, HFDS, HLSRIG (LS -> LSx), ERRNO_LOW, HGCELLS, GWR, HCE, HRO verbatim, BLKN and HPST
   (the generic relation's facts, as on image A).  Every ghost list is [] (cut_x's HP0). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG FCiface YCe5x YGcallx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_kit_x W_journal_x W_frame_x W_contract_x W_sites_x W_LLVMFuzzerTestOneInput_cut_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_img_x.
(* W_LLVMFuzzerTestOneInput_gone_p3.v's own imports, AFTER the generic kit's: the converted proofs see the names they were written against *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YE01 YE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import
HarnessRep RelayRep CheckRep RelayKeys RelayModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require ListRep RelayRunT drain_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rep W_contract W_sites W_frame W_shadow_pin.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_LLVMFuzzerTestOneInput_gone_base W_LLVMFuzzerTestOneInput_gone_tk.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_contract_xR_relayB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCk0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_LLVMFuzzerTestOneInput_gone_base_x W_LLVMFuzzerTestOneInput_gone_tk_x W_LLVMFuzzerTestOneInput_gone_p3.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* the zify flag as W_LLVMFuzzerTestOneInput_gone_p3.v's proofs see it (true: its imports' last setting), whatever a Required file leaves *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* @@ CONFLICT Ltac Zify *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* the program interface's stack budget, from the generated lib/B/YCfn.v, as the cut names it *)
(* @@ B-ONLY-HDR Local_Notation LLVMF_STK *)
Local Notation LLVMF_STK := YCfn.LLVMF_STK.

(* ------------------------------------------------------------------ generic list helpers *)
(* @@ SECTION gp3 *)
Section gp3.
(* @@ MERGED Context ctx:fx *)
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
(* @@ MERGED #[local]_Notation segs *)
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
(* @@ MERGED Variable B *)
Variable B : asyms.
(* @@ MERGED Variable MT *)
Variable MT : ameter_ops.
(* @@ MERGED Variables XM_LIB *)
Variables XM_LIB : Z -> Z.
(* @@ MERGED Variables RLO *)
Variables RLO RHI : Z.
(* @@ MERGED Variable fr_live_pre *)
Variable fr_live_pre : astate -> Prop.
(* @@ AX-ONLY Variables LIBROOM *)
Variables LIBROOM NP : astate -> Prop.
(* @@ MERGED Variable G_fr *)
Variable G_fr : list (Z * Z).
(* @@ MERGED Variable fr_FP *)
Variable fr_FP : bvmap 5 word -> alayout -> astate -> world segs -> (word -> option byte) -> list (Z * Z).
(* @@ AX-ONLY Variable PST *)
Variable PST : list (Z * Z).
(* @@ AX-ONLY Variable ARx *)
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
(* @@ AX-ONLY Context ctx:hl *)
Context {hl : Z}.
(* @@ MERGED Hypothesis LAWS *)
Hypothesis LAWS : AR_laws_x segs B ARx hl.
(* the instance's ghost poisoned-head set stays empty (a Theorem Labs lane's HP0 ruling): the post's Hp' is read [] through it *)
(* @@ AX-ONLY Hypothesis HP0 *)
Hypothesis HP0 : forall ly S Hp (W : world segs) mem md, ARx ly S Hp W mem md -> Hp = [].
(* @@ MERGED Hypothesis HG *)
Hypothesis HG : gx_ok segs B G_fr.
(* @@ AX-ONLY Variable LSx *)
Variable LSx : lfcx -> Z -> lmod -> alayout -> astate -> Prop.
(* @@ MERGED Variable RINV *)
Variable RINV : lfcx -> Z -> lmod -> Prop.
(* @@ MERGED #[local]_Notation VAL *)
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).
(* @@ MERGED #[local]_Notation BASE *)
#[local] Notation BASE := (@pa_val _ fr_prog_listing PB_fr A_TEXT).

(* ---- what the other lanes owe (the texts the base fixes) ---- *)
(* @@ RESOLVED Variable MMAX *)
Variable MMAX : Z.
(* the room round (ROOM-TEXTS.md (sha256 767baa12f13c; internal record) (d)): the room predicate the callees are taken at (RM := fun S _ => NP S at the
   instance; RPNP below) *)
Variable RP : roomp.
(* relay_instance_gone, W6: lib/B/W_contract.v's rig_spec (Section s6 at CTX_AFREE := image B's K0 table
   YCk0.CTX_AFREE; its last premise is the free's caller context [0x82fb8; 0x84b4c(; 0x82240)]) and rg_place,
   verbatim.  The adaptation to the CTX_AFREE rig_spec is image A's (95cae0d4740), at B's numbers. *)
(* @@ RESOLVED Hypothesis RIG *)
Hypothesis RIG : rig_spec_x (PI := PB_fr) B PST ARx MT RP MMAX fr_RG YCk0.CTX_AFREE (BASE + AF_fr_relay_instance_gone).
(* @@ RESOLVED Hypothesis RGP *)
Hypothesis RGP : rg_place (PI := PB_fr) B fr_RG.
(* the model obligations, by the base's names *)
(* @@ MERGED Hypothesis HGRIG *)
Hypothesis HGRIG : GN_HG_RIG B G_fr.
(* @@ MERGED Hypothesis HPAIRS *)
Hypothesis HPAIRS : GN_RI_pairs RINV.
(* @@ MERGED Hypothesis HFDS *)
Hypothesis HFDS : GN_RI_fds RINV.
(* @@ RESOLVED Hypothesis HLSRIG *)
Hypothesis HLSRIG : GN_LS_rig MT LSx RINV MMAX.
(* ---- the room round (ROOM-TEXTS.md (sha256 767baa12f13c; internal record) (c) / (d)).  RP is the room record the callees are taken at: at the instance
   RM := fun S _ => NP S (so RPNP holds by conversion) and the counts are ReplyCnt's.  gn_pk is the arm's peak
   (s5-r1d's pk_gone).  LSCNT is the arm's count row GN_LS_cnt_x (_gone_base_x.v: s5-r1d's fr_LS3cp_cnt_gone's guards,
   ReplyCnt.msz_ok among them).  CNTRIG is the arm's model count rule GN_CNT_rig (_gone_base.v) at relay_instance_gone's
   premise peak, rig_spec_x's rig_pk of its trace (W_contract_x.v:307) ---- *)
Variable gn_pk : lfcx -> lmod -> list (hsrc * nat) -> (Z -> bool) -> nat.
Hypothesis RPNP : forall S k, rp_RM RP S k <-> NP S.
Hypothesis CNTRIG : GN_CNT_rig gn_pk (fun cx m hs =>
  rig_pk (rig_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (gn_id cx m) (lm_es m) hs)).
Hypothesis LSCNT : GN_LS_cnt_x B LSx RINV RP gn_pk.
(* @@ MERGED Hypothesis ERRNO_LOW *)
Hypothesis ERRNO_LOW : GN_ERRNO_LOW B.
(* the cells amodel_at names lie in the entry's G_fr (the base's name), and the entry's law makes a byte of
   G_fr writable in any state (the cut's glob_wr_law) *)
(* @@ MERGED Hypothesis HGCELLS *)
Hypothesis HGCELLS : GN_HGcells G_fr.
(* @@ RESOLVED Hypothesis GWR *)
Hypothesis GWR : glob_wr_law G_fr.
(* errno is none of the model's cells (the base's name) *)
(* @@ HDR-CITED-IN-AX Hypothesis HCE *)
Hypothesis HCE : GN_CELLS_ERRNO B.
(* the read-only bytes are off G_fr, pinned when the allocator owns them, off errno and off the sink head
   (lib/B/W_journal.v:397 rom_out; B's add walk's HRO; _G.v c_rom_out at G_fr_c): with GN_HG_RIG it gives rom_out at
   G_RIG (gp3_rom_out), so the cut's rom_view survives the callee's journal *)
(* @@ B-ONLY-HDR Hypothesis HRO *)
Hypothesis HRO : rom_out segs B G_fr.

(* the four cells of amodel_at relay_instance_gone neither writes nor re-states *)
(* @@ AX-ONLY Local_Notation AR0 *)
Local Notation AR0 ly S W mem md := (ARx ly S [] W mem md).
(* @@ AX-ONLY Local_Notation AJ0 *)
Local Notation AJ0 G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k :=
  (ajournal_gx_x segs B PST ARx G XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k).
(* @@ AX-ONLY Local_Notation AJi0 *)
Local Notation AJi0 STK sp0 FP ly S W mem md own ly' S' W' mem' md' k :=
  (ajournal_x segs B PST ARx STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k).
(* @@ AX-ONLY Local_Notation AFN0 *)
Local Notation AFN0 STK ly S W regs mem md ch := (afn_pre_x segs B ARx STK ly S [] W regs mem md ch).
(* @@ AX-ONLY Local_Notation LFB0 *)
Local Notation LFB0 cx := (lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx []).
(* a ghost list read off an ARx fact, or off a journal's last state, is [] *)
(* @@ AX-ONLY Ltac hp0a *)
Ltac hp0a H := let E := fresh "EHp" in pose proof (HP0 _ _ _ _ _ _ H) as E;
  lazymatch type of E with ?h = [] => subst h end.
(* @@ AX-ONLY Ltac hp0g *)
Ltac hp0g HJ := let H := fresh "HARg" in
  pose proof (ajournal_gx_AR_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as H; hp0a H; clear H.
(* ---- _gone_p3.v's AR-free items that take section arguments, cited with them ---- *)
(* @@ ALIASES - *)
(* the AR file's AR-free names that take this Section's variables, cited with them *)
Local Notation gp3_errno_g4 := (W_LLVMFuzzerTestOneInput_gone_p3.gp3_errno_g4 B HCE).
Local Notation gp3_not_RIG := (W_LLVMFuzzerTestOneInput_gone_p3.gp3_not_RIG B).
Local Notation gp3_others := (W_LLVMFuzzerTestOneInput_gone_p3.gp3_others B RINV HFDS).
Local Notation gp3_rom_out := (W_LLVMFuzzerTestOneInput_gone_p3.gp3_rom_out B G_fr HGRIG HRO).
(* @@ AX-ONLY Hypothesis BLKN *)
Hypothesis BLKN : forall ly S Hp (W : world segs) mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.
(* the image is off PST (add_x's HPST): the journal's image clause and the ROM-view lemma take it; trivial at PST = [] *)
(* @@ AX-ONLY Hypothesis HPST *)
Hypothesis HPST : forall a, in_img segs a -> ~ Exists (in_zr a) PST.

(* ---------------------------------------------------------------- the walk at the empty ghost list *)
(* @@ MERGED Lemma gp3_nodup_blocks *)
Lemma gp3_nodup_blocks_x : forall ly S (W : world segs) mem md,
  AR0 ly S W mem md -> List.NoDup (ablocks B ly S).
Proof.
  intros ly S W mem md HAR.
  destruct (alx_sep _ _ _ LAWS ly S [] W mem md HAR) as [Hpw _].
  apply pairwise_app_l in Hpw as [Hpw _].
  apply gp3_nodup_of_pairwise; [|exact Hpw].
  intros b Hb. destruct b as [p n]. cbn [snd].
  destruct (gk_blk_x B ARx LAWS BLKN ly S W mem md p n HAR Hb) as (_ & _ & H3).
  pose proof (req_size_pos n ltac:(lia)). lia.
Qed.
(* _gone_p3.v:211 gp3_apart *)
(* @@ MERGED Lemma gp3_apart *)
Lemma gp3_apart_x : forall ly S (W : world segs) mem md (L1 L2 : list (Z * Z)) b1 b2 a,
  AR0 ly S W mem md -> Permutation (ablocks B ly S) (L1 ++ L2) ->
  In b1 L1 -> In b2 L2 ->
  fst b1 <= a < fst b1 + req_size (snd b1) -> fst b2 <= a < fst b2 + req_size (snd b2) -> False.
Proof.
  intros ly S W mem md L1 L2 b1 b2 a HAR HP H1 H2 R1 R2.
  pose proof (Permutation_NoDup HP (gp3_nodup_blocks_x ly S W mem md HAR)) as HND.
  assert (Hne : b1 <> b2) by (intros ->; exact (gp3_nodup_app_neq L1 L2 b2 HND H1 H2)).
  assert (I1 : In b1 (ablocks B ly S))
    by (apply (Permutation_in _ (Permutation_sym HP)); apply in_app_iff; left; exact H1).
  assert (I2 : In b2 (ablocks B ly S))
    by (apply (Permutation_in _ (Permutation_sym HP)); apply in_app_iff; right; exact H2).
  destruct b1 as [p1 n1]; destruct b2 as [p2 n2]. cbn [fst snd] in *.
  pose proof (sep_blocks_x _ _ _ LAWS ly S [] W mem md p1 n1 p2 n2 HAR I1 I2 Hne) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.
(* _gone_p3.v:238 gp3_fp_spares *)
(* @@ MERGED Lemma gp3_fp_spares *)
Lemma gp3_fp_spares_x : forall ly S (W : world segs) mem md (bl : list (Z * Z)),
  AR0 ly S W mem md -> (forall b, In b bl -> In b (ablocks B ly S)) ->
  forall a, fp_spares (ablocks_fp bl) a.
Proof.
  intros ly S W mem md bl HAR Hsub a. apply fp_spares_closed.
  apply sink_closed_ablocks_fp. apply Forall_forall. intros b Hb. destruct b as [p n].
  destruct (gk_blk_x B ARx LAWS BLKN ly S W mem md p n HAR (Hsub _ Hb)) as (H1 & _). cbn [fst]. lia.
Qed.
(* _gone_p3.v:246 gp3_not_fp_shadow *)
(* @@ MERGED Lemma gp3_not_fp_shadow *)
Lemma gp3_not_fp_shadow_x : forall ly S (W : world segs) mem md (bl : list (Z * Z)) a,
  AR0 ly S W mem md -> (forall b, In b bl -> In b (ablocks B ly S)) ->
  kLowShadowBeg <= a < kHighMemBeg -> ~ inFP (ablocks_fp bl) a.
Proof.
  intros ly S W mem md bl a HAR Hsub Ha Hin.
  apply gp3_inFP_fp in Hin as (b & Hb & Hr). destruct b as [p n]. cbn [fst snd] in Hr.
  destruct (al0_blocks B ARx LAWS BLKN ly S W mem md p n HAR (Hsub _ Hb)) as (_ & H4096 & Hceil & Happ & _).
  unfold in_app, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.
(* _gone_p3.v:255 gp3_not_fp_frame *)
(* @@ MERGED Lemma gp3_not_fp_frame *)
Lemma gp3_not_fp_frame_x : forall ly S (W : world segs) mem md (bl : list (Z * Z)) cid pos a,
  AR0 ly S W mem md -> (forall b, In b bl -> In b (ablocks B ly S)) ->
  In (cid, pos) (frames S) ->
  frame_addr ly cid pos <= a < frame_addr ly cid pos + fs_frame_bytes cid ->
  ~ inFP (ablocks_fp bl) a.
Proof.
  intros ly S W mem md bl cid pos a HAR Hsub Hf Ha Hin.
  apply gp3_inFP_fp in Hin as (b & Hb & Hr). destruct b as [p n]. cbn [fst snd] in Hr.
  pose proof (sep_block_frame_x _ _ _ LAWS ly S [] W mem md p n cid pos HAR (Hsub _ Hb) Hf) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.

(* ------------------------------------------------------------------ what a callee's journal keeps *)
(* _gone_p3.v:268 gp3_inner *)
(* @@ MERGED Lemma gp3_inner *)
Lemma gp3_inner_x : forall (G : list (Z * Z)) STK sp0 FP ly S (W : world segs) mem md own
    ly' S' (W' : world segs) mem' md' k,
  AJ0 G 0 [] STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
  exists memS, AJi0 STK sp0 FP ly S W memS md own ly' S' W' mem' md' k /\
    (forall a, 0 <= a < 2 ^ 64 -> ~ inG G a -> aview segs (w_H W) memS a = aview segs (w_H W) mem a).
Proof.
  intros G STK sp0 FP ly S W mem md own ly' S' W' mem' md' k HJ.
  destruct (ajournal_gx_inner_x segs B PST ARx G 0 [] STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k HJ)
    as (memS & HJi & Hag).
  rewrite !Z.add_0_r in HJi. exists memS. split; [exact HJi|].
  intros a Ha HnG. apply Hag. rewrite unsigned_lit_small by lia. exact HnG.
Qed.
(* _gone_p3.v:280 gp3_keeps (the image clause's PST premise from HPST) *)
(* @@ MERGED Lemma gp3_keeps *)
Lemma gp3_keeps_x : forall (G : list (Z * Z)) STK sp0 FP ly S (W : world segs) mem md own
    ly' S' (W' : world segs) mem' md' k,
  AJ0 G 0 [] STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ inG G a -> alloc_ceiling <= a -> ~ (sp0 - STK <= a < sp0) ->
     aview segs (w_H W') mem' a = aview segs (w_H W) mem a) /\
  (forall p n i, In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B ly' S') -> 0 <= i < req_size n ->
     ~ inFP FP (p + i) -> 0 <= p + i < 2 ^ 64 -> ~ inG G (p + i) ->
     aview segs (w_H W') mem' (p + i) = aview segs (w_H W) mem (p + i)) /\
  (forall cid pos a, In (cid, pos) (frames S) ->
     (in_zr a (frame_rng ly (cid, pos)) \/
      in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8)) ->
     ~ inFP FP a -> 0 <= a < 2 ^ 64 -> ~ inG G a ->
     aview segs (w_H W') mem' a = aview segs (w_H W) mem a) /\
  (forall a, in_img segs a -> ~ Exists (in_zr a) (as_owned_static B) ->
     ~ (as_errno B <= a < as_errno B + 4) -> fp_spares FP a -> 0 <= a < 2 ^ 64 -> ~ inG G a ->
     aview segs (w_H W') mem' a = aview segs (w_H W) mem a) /\
  (forall a, sp0 - STK <= a < sp0 -> apresent (w_H W') mem' a) /\
  AR0 ly' S' W' mem' md' /\ frames S' = own ++ frames S /\
  layout_le (length (st_secs S)) ly ly' /\ wle W W'.
Proof.
  intros G STK sp0 FP ly S W mem md own ly' S' W' mem' md' k HJ.
  destruct (gp3_inner_x G STK sp0 FP ly S W mem md own ly' S' W' mem' md' k HJ) as (memS & HJi & Hag).
  pose proof HJi as (HAR' & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & C8 & C9 & C11 & C10 & C12 &
    C13 & Hstk & Cextra & HQT).
  split; [intros a Ha HnG Hc Hout; rewrite (C8 a ltac:(lia) ltac:(lia)); exact (Hag a Ha HnG)|].
  split.
  { intros p n i Hin Hin' Hi Hnf Hrng HnG.
    rewrite (C9 p n i Hin Hin' Hi Hnf). exact (Hag (p + i) Hrng HnG). }
  split.
  { intros cid pos a Hf Hr Hnf Ha HnG.
    rewrite (C10 cid pos a Hf Hr Hnf). exact (Hag a Ha HnG). }
  split.
  { intros a Himg Hown Herr Hsp Ha HnG.
    rewrite (C11 a Himg Hown Herr (HPST a Himg) Hsp). exact (Hag a Ha HnG). }
  split; [exact C13|].
  split; [exact HAR'|]. split; [exact Hfrs|]. split; [exact Hly | exact Hwle].
Qed.

(* ------------------------------------------------------------------ a slot's bytes: the struct, or a block *)
(* _gone_p3.v:649 gp3_slot_kept *)
(* @@ CONFLICT Lemma gp3_rom_out *)
(* (_gone_p3.v gp3_rom_out: cited) *)
(* @@ CONFLICT Lemma gp3_not_RIG *)
(* @@ MERGED Lemma gp3_asrc_split *)
Local Notation gp3_asrc_split := (W_LLVMFuzzerTestOneInput_gone_p3.gp3_asrc_split B).
(* @@ MERGED Lemma gp3_slot_kept *)
Lemma gp3_slot_kept_x : forall ly S (W : world segs) mem md ly' S' (W' : world segs) mem' i o,
  AR0 ly S W mem md -> aslot B ly S W mem i o -> (i < 4)%nat ->
  (forall a, rg_s fr_RG + ASRC * Z.of_nat i <= a < rg_s fr_RG + ASRC * Z.of_nat i + ASRC ->
     abyte_kept W mem W' mem' a) ->
  (forall b, In b (slot_blks o) -> In b (ablocks B ly' S') /\
     (forall a, fst b <= a < fst b + snd b -> abyte_kept W mem W' mem' a)) ->
  aslot B ly' S' W' mem' i o.
Proof.
  intros ly S W mem md ly' S' W' mem' i o HAR Hs Hi KG KB.
  destruct o as [h|]; cbn [aslot slot_blks] in *.
  - apply (asrc_at_kept B ly S W mem ly' S' W' mem' _ h Hs).
    + intros r Hr a Ha.
      destruct (gp3_asrc_split ly S W mem _ h a Hs (ex_intro _ r (conj Hr Ha)))
        as [Hin | (b & Hb & Hrb)]; [apply KG; exact Hin | exact (proj2 (KB b Hb) a Hrb)].
    + intros b Hb. exact (proj1 (KB b Hb)).
  - destruct Hs as [Hz Hw]. split.
    + apply (akept_garr8 W mem); [|exact Hz]. intros x Hx. rewrite repeat_length in Hx.
      apply KG. unfold ASRC in *. lia.
    + apply (akept_awr W mem); [|exact Hw]. intros x Hx. apply KG. lia.
Qed.

(* the callee's afn_pre at sp = F (_gone_p3.v:771 gp3_afn_pre, over the generic pre and journal: YCbqG.afn_pre_x_at,
   W_frame_x.aview_above_of_journal_x, W_journal_x.ajournal_gx_inner_x), with the chain's spine (empty, or the entry's
   return RA_LLVMF) and the room above sp that rig_spec_x's caller-context premise names *)
(* @@ CONFLICT Lemma gp3_others *)
(* (_gone_p3.v gp3_others: cited) *)
(* @@ B-ONLY-HDR Local_Ltac gp3_awr *)
Local Ltac gp3_awr U9 :=
  cbn [ss_mem ss_gp3a];
  repeat (apply awr_ok_x_cons;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [gp3_frR YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
      rewrite ?U9 in Ha;
      left; split; [left; unfold LLVMF_STK in *; lia | lia]
    | ]);
  apply awr_ok_x_nil.
(* a byte outside F+24 .. F+32 is outside the first run's writable window *)
(* @@ B-ONLY-HDR Local_Ltac gp3_nowr *)
Local Ltac gp3_nowr U9 :=
  let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros (r & Hin & Hr); cbn [ss_mem ss_gp3a In] in Hin;
  repeat (destruct Hin as [<- | Hin];
    [ cbn [gp3_frR YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U9 in Hr; lia | ]);
  destruct Hin.

(* ------------------------------------------------------------------ the frame and the input, kept *)
(* B's gframe (no `full` flag): the saved registers, the frame's window, 14 slots F+32 .. F+184, the fake frame's
   three header words and window, its shadow and the shadow's window *)
(* @@ RESOLVED Lemma gp3_ainput_kept *)
Local Notation gp3_ainput_kept := (W_LLVMFuzzerTestOneInput_gone_p3.gp3_ainput_kept B).

(* ------------------------------------------------------------------ the live blocks are distinct and apart *)
(* _gone_p3.v:200 gp3_nodup_blocks *)
(* @@ RESOLVED Ltac gp3_csd *)
Ltac gp3_csd := unfold acallee_saved;
  match goal with |- context [bv_unsigned ?r] => let v := eval vm_compute in (bv_unsigned r) in
    change (bv_unsigned r) with v end; clear; lia.

(* the registers the first run does not write (a0 and ra) *)
(* @@ RESOLVED Lemma gp3_afn_pre *)
Lemma gp3_afn_pre_x : forall cx ly3 S3 fpos k (W : world segs) mem md regs STK1,
  LFB0 cx ->
  AJ0 G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem md k ->
  (forall o r, In (o, r) saved_regs -> sv8 W mem (spZ (c_regs cx) - o) (bv_unsigned (getr (c_regs cx) (Z_to_bv 5 r)))) ->
  spZ regs = lf_F cx -> YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) -> getr regs 8 = getr (c_regs cx) 2 ->
  0 <= STK1 -> STK1 + 352 <= LLVMF_STK ->
  exists ch, AFN0 STK1 ly3 S3 W regs mem md ch /\ (spine ch = [] \/ spine ch = [YCfn.RA_LLVMF]) /\
    spZ regs + 16 < ly_top ly3.
Proof.
  intros cx ly3 S3 fpos k W mem md regs STK1 HB HJ HSV Hsp Hret Hra4 Hgp Htp Hs0 HSTK0 HSTKb.
  destruct HB as (_ & HPRE).
  assert (HRA : raZ (c_regs cx) = YCfn.RA_LLVMF) by (unfold fr_lib_pre_cf_x in HPRE; tauto).
  assert (HPREE : AFN0 LLVMF_STK (c_ly cx) (c_S cx) (c_W cx) (c_regs cx) (c_mem cx) (c_md cx) [])
    by (unfold fr_lib_pre_cf_x in HPRE; tauto).
  pose proof HPREE as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0).
  pose proof Hstk0 as (Hal16 & Hslo0 & Hceil0 & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  destruct (ajournal_gx_inner_x segs B PST ARx G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 [] W mem md k HJ) as (memS & HJ0 & Hmg).
  rewrite !Z.add_0_r in HJ0.
  set (sp0 := spZ (c_regs cx)) in *.
  assert (HF32 : lf_F cx = sp0 - 320 - (sp0 - 320) mod 32) by reflexivity.
  pose proof (Z.mod_pos_bound (sp0 - 320) 32 ltac:(lia)) as Hmb.
  assert (Ho16 : (lf_F cx - sp0) mod 16 = 0).
  { rewrite HF32.
    replace (sp0 - 320 - (sp0 - 320) mod 32 - sp0) with (- (320 + (sp0 - 320) mod 32)) by lia.
    assert (H32 : (sp0 - 320) mod 32 = 0 \/ (sp0 - 320) mod 32 = 16).
    { assert (E16 : (sp0 - 320) mod 16 = 0)
        by (replace (sp0 - 320) with (sp0 + (-20) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16).
      pose proof (Z.div_mod ((sp0 - 320) mod 32) 16 ltac:(lia)) as D.
      assert (E2 : ((sp0 - 320) mod 32) mod 16 = 0)
        by (rewrite <- Znumtheory.Zmod_div_mod by (try lia; exists 2; reflexivity); exact E16).
      rewrite E2, Z.add_0_r in D.
      assert (Hq : (sp0 - 320) mod 32 / 16 = 0 \/ (sp0 - 320) mod 32 / 16 = 1) by lia.
      destruct Hq as [Hq | Hq]; rewrite Hq in D; lia. }
    destruct H32 as [H32 | H32]; rewrite H32; reflexivity. }
  assert (HoNeg : lf_F cx - sp0 <= 0) by (rewrite HF32; lia).
  assert (HoBud : STK1 - (lf_F cx - sp0) <= LLVMF_STK) by (rewrite HF32; lia).
  assert (HTOPeq : ly_top ly3 = ly_top (c_ly cx)).
  { pose proof HJ0 as (_ & Hly & _). pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _). exact Etop. }
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (Hs0Z : s0Z regs = sp0) by (unfold s0Z, sp0, spZ; rewrite Hs0; reflexivity).
  destruct (Z_lt_le_dec sp0 (ly_top (c_ly cx) - 16)) as [Hlt | Hge].
  - pose proof (aview_above_of_journal_x (PI := PB_fr) B PST ARx LLVMF_STK sp0 (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) [] (c_W cx) memS (c_md cx) [(1, fpos)] ly3 S3 [] W mem md k HJ0) as HAB.
    assert (Hra8 : rdword (aview segs (w_H W) mem) (sp0 - 8) = Some (bv_unsigned (getr (c_regs cx) 1))).
    { apply (rdword_of_val_mem segs (w_H W) mem); [exact (HSV 8 1 ltac:(left; reflexivity)) |].
      pose proof (bv_unsigned_in_range 64 (getr (c_regs cx) 1)) as Hr.
      change (bv_modulus 64) with (2 ^ 64) in Hr. lia. }
    assert (Hs016 : rdword (aview segs (w_H W) mem) (sp0 - 16) = Some (bv_unsigned (getr (c_regs cx) 8))).
    { apply (rdword_of_val_mem segs (w_H W) mem); [exact (HSV 16 8 ltac:(right; left; reflexivity)) |].
      pose proof (bv_unsigned_in_range 64 (getr (c_regs cx) 8)) as Hr.
      change (bv_modulus 64) with (2 ^ 64) in Hr. lia. }
    exists ((sp0, bv_unsigned (getr (c_regs cx) 1), bv_unsigned (getr (c_regs cx) 8)) :: []).
    split; [| split; [right; cbn [spine map fst snd]; unfold raZ in HRA; rewrite HRA; reflexivity
                     | rewrite Hsp, HTOPeq, HF32; lia]].
    eapply (afn_pre_x_at segs B PST ARx LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) [] (c_W cx) memS (c_md cx)
      [(1, fpos)] ly3 S3 [] W mem md k regs STK1 (lf_F cx - sp0) _ HJ0);
      [ rewrite Hsp; lia | exact Ho16 | exact HoNeg | exact HSTK0 | exact HoBud | exact Hret | exact Hra4
      | exact Hgp | exact Htp | ].
    rewrite Hsp, Hs0Z.
    apply (achain_ly_top (c_ly cx) ly3 _ _ _ _ ltac:(exact HTOPeq)).
    eapply (achain_push (c_ly cx) (aview segs (w_H (c_W cx)) (c_mem cx)) (aview segs (w_H W) mem)
      sp0 (bv_unsigned (getr (c_regs cx) 8)) (bv_unsigned (getr (c_regs cx) 1)) [] (lf_F cx));
      [ exact Hch0 | lia
      | intros a Ha; rewrite (HAB a ltac:(lia)); apply Hmg; rewrite unsigned_lit_small by lia; intros HGa;
        pose proof (pa_segs_low a (proj1 (HG a HGa))); lia
      | exact Hra8 | exact Hs016
      | unfold raZ in Hra40; lia | lia | lia | lia | rewrite HF32; lia ].
  - exists []. split; [| split; [left; reflexivity | rewrite Hsp, HTOPeq, HF32; lia]].
    eapply (afn_pre_x_at segs B PST ARx LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) [] (c_W cx) memS (c_md cx)
      [(1, fpos)] ly3 S3 [] W mem md k regs STK1 (lf_F cx - sp0) _ HJ0);
      [ rewrite Hsp; lia | exact Ho16 | exact HoNeg | exact HSTK0 | exact HoBud | exact Hret | exact Hra4
      | exact Hgp | exact Htp | ].
    rewrite Hs0Z. left. split; [right; left; rewrite HTOPeq; exact Hge | reflexivity].
Qed.
(* @@ AX-ONLY Lemma gp3_rom_pst *)
Lemma gp3_rom_pst : forall a, in_rom segs a -> ~ Exists (in_zr a) PST.
Proof. intros a (sg & Hin & _ & Hr). apply HPST. exists sg. split; [exact Hin | exact Hr]. Qed.

(* _gone_p3.v:908 gp3_rig_c1, over cut_x's invariants (rule 5: the entry and the cut points at the ghost list []) *)
(* @@ CONFLICT Lemma gp3_rig_c1 *)
Lemma gp3_rig_c1_x : forall cx t m W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
  GRG_x B NP G_fr fr_FP PST ARx LSx RINV cx t m W c ->
  SRr segs W c (fun W' c' => exists m1, GC1_x B MT NP G_fr fr_FP PST ARx LSx RINV cx t m m1 0%nat W' c').
Proof.
  intros cx t m W c HB HRG.
  destruct HRG as (regs & mem0 & md & ly3 & S3 & kk & fpos & -> &
    ((HJ0 & HFR0 & HFLAG0 & H16_0 & H144_0 & H88_0 & HIN0 & HRV0 & HJT0) & HMOD0 & HSEP & HNP) & HLS & HRI & HOP &
    HKR & R26 & R21 & HREADS0 & HAWR0 & HAT0 & HPFX0).
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (gn_nums_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS cx [(1, fpos)] ly3 S3
    W mem0 md kk fpos HB HJ0 eq_refl) as NUMS.
  cbv zeta in NUMS.
  destruct NUMS as (Hsp16 & Hspr & HFm32 & HFr & HFF0 & HFF1 & HFFapp & Hfrs & HAR0).
  destruct HKR as (R2 & R8 & R9 & R18 & R19 & R27 & R3 & R4).
  pose proof YM05.alloc_ceiling_value as AC.
  assert (HlenP : Z.of_nat (length (c_pl cx)) = c_n cx)
    by (destruct HB as (_ & HPRE0); unfold fr_lib_pre_cf_x in HPRE0; symmetry; tauto).
  destruct ERRNO_LOW as (HE0 & HE1).
  assert (HFlo : alloc_ceiling + 8 <= lf_F cx) by (unfold LLVMF_STK in *; lia).
  (* ---- 0x84b40-0x84b48: sd s10,24(s1); mv a0,s5; jal relay_instance_gone ---- *)
  assert (HFw32 : awr W mem0 (lf_F cx) 32).
  { intros i Hi. pose proof HFR0 as (_ & HFW0 & _). apply HFW0. lia. }
  destruct (gp3_entry W regs mem0 (lf_F cx) R9 ltac:(unfold LLVMF_STK in *; lia) ltac:(lia) HFm32 HFw32)
    as [HS SHOK].
  remember (Eimg (Ereg regs gp3_extra)) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs gp3_extra) E)
    by (rewrite HE; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (E21 : ew E 21 = Z_to_bv 64 (gn_id cx m)).
  { subst E. rewrite Eimg_low by (unfold A_TEXT; lia).
    rewrite (ew_Ereg_nat regs _ 21 21%bv eq_refl). exact R21. }
  assert (E26 : ew E 26 = Z_to_bv 64 HI_G_NOUT).
  { subst E. rewrite Eimg_low by (unfold A_TEXT; lia).
    rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl). exact R26. }
  assert (U9 : bv_unsigned (ew E 9) = lf_F cx).
  { subst E. rewrite Eimg_low by (unfold A_TEXT; lia).
    rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl), R9. apply unsigned_lit_small. unfold LLVMF_STK in *. lia. }
  clear HE.
  unfold cfg_at. change (w64 (fr_B0 + AF_gn_rig)) with (Z_to_bv 64 (BASE + AF_gn_rig)).
  pose (RUNTO := paj_run_to_x_x (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS G_fr HG 0 []).
  paj_run_to_tok_x RUNTO HS HJ0 SHOK gp3_span AF_fr_relay_instance_gone.
  { gp3_awr U9. }
  lazymatch goal with Hg : mem_grows _ _ |- _ => rename Hg into HGr end.
  lazymatch goal with Hf : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ => rename Hf into HFRr end.
  (* the run's one store: F+24 := HI_G_NOUT; every other byte kept, every writable byte still writable *)
  assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + 24 <= a < lf_F cx + 32) ->
      aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem0 a)
    by (intros a Ha Hna; apply (aview_kept_out _ _ _ _ _ HFRr a Ha); gp3_nowr U9).
  assert (WK : forall a, writable_at segs (arm W mem0) a -> writable_at segs (arm W (ms_mem ms)) a).
  { intros a Hw. apply (writable_kept (w_H W) mem0 (ms_mem ms) a); [|exact Hw].
    intros Hp. exact (apresent_grows _ _ _ _ HGr Hp). }
  assert (KEEP0 : forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + 24 <= a < lf_F cx + 32) ->
      abyte_kept W mem0 W (ms_mem ms) a)
    by (intros a Ha Hna; split; [exact (K1 a Ha Hna) | apply WK]).
  assert (KLO : forall a, 0 <= a < GK_CEIL8 -> abyte_kept W mem0 W (ms_mem ms) a)
    by (intros a Ha; apply KEEP0; unfold GK_CEIL8 in *; lia).
  pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG0. cbn [ms_mem restrict] in RG0.
  assert (SV24 : sv8 W (ms_mem ms) (lf_F cx + 24) HI_G_NOUT).
  { unfold sv8.
    lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
      apply (field_of_region Ev _ 9%nat (lf_F cx) _ _ _ _ _ 24 8%N (SOff 26 0) HI_G_NOUT RG0) end.
    - exact U9.
    - left. reflexivity.
    - cbn [sv_denot]. rewrite E26, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    - unfold HI_G_NOUT. zside.
    - zside. }
  pmkst HS.
  pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs gp3_extra gp3_kept HS HAE
    ltac:(vm_compute; reflexivity)) as KR.
  prreg HS (1%bv : bv 5) Q1.
  prreg HS (10%bv : bv 5) Q10.
  cbn [ms_regs restrict] in KR.
  set (mem := ms_mem ms) in *.
  set (mdc := with_vm_backing (m_vm_lazy md) mat md) in *.
  rename HJ0 into HJ.
  pose proof (gn_nums_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS cx [(1, fpos)] ly3 S3 W mem mdc kk
    fpos HB HJ eq_refl) as NUMS2.
  cbv zeta in NUMS2. destruct NUMS2 as (_ & _ & _ & _ & _ & _ & _ & _ & HAR).
  (* ---- the cut point's facts at the call's entry ---- *)
  assert (HFR : gframe cx fake_shadow_open (frame_addr ly3 1 fpos) W mem).
  { apply (gp3_gframe_st cx _ _ W mem0 mem HFR0 eq_refl); [lia | | | | exact WK].
    - intros a Ha. apply KEEP0; lia.
    - intros a Ha. apply KLO. unfold GK_CEIL8. lia.
    - intros a Ha. apply KLO. unfold GK_CEIL8, SB in *. lia. }
  assert (HFLAG : sv8 W mem (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos))
    by (apply (gk_sv8_kept W W mem0 mem); [intros x Hx; apply KLO; unfold GK_CEIL8; lia | exact HFLAG0]).
  assert (H16 : sv8 W mem (lf_F cx + 16) (c_p cx + gn_kq cx m))
    by (apply (gk_sv8_kept W W mem0 mem); [intros x Hx; apply KEEP0; lia | exact H16_0]).
  assert (H144 : sv8 W mem (lf_F cx + 144) (c_n cx - gn_kq cx m))
    by (apply (gk_sv8_kept W W mem0 mem); [intros x Hx; apply KEEP0; lia | exact H144_0]).
  assert (H88 : sv8 W mem (lf_F cx + 88) t)
    by (apply (gk_sv8_kept W W mem0 mem); [intros x Hx; apply KEEP0; lia | exact H88_0]).
  pose proof (gk_ainput_kept_x B ARx LAWS BLKN cx ly3 S3 W mem0 md W mem HAR0 HIN0 HlenP KLO) as HIN.
  pose proof (gk_rom_kept W W mem0 mem HRV0 KLO) as HRV.
  pose proof (gk_jt_kept W W mem0 mem HJT0 KLO) as HJT.
  pose proof (gk_amodel_kept_x B ARx LAWS BLKN ly3 S3 W mem0 md W mem m HAR0 HMOD0 HE0 ltac:(unfold GK_CEIL8; lia) KLO)
    as HMOD.
  assert (HREADS : forall j, (j < 4)%nat -> gn_sv4 W mem (lf_F cx + 192 + 4 * Z.of_nat j) (gn_reads m j)).
  { intros j Hj. unfold gn_sv4. apply (akept_vm W mem0); [|exact (HREADS0 j Hj)].
    intros x Hx. apply KEEP0; cbn in Hx; lia. }
  assert (HAWR : awr W mem (lf_F cx + 192) 16)
    by (apply (akept_awr W mem0); [intros x Hx; apply KEEP0; lia | exact HAWR0]).
  assert (HAT : sv8 W mem (lf_F cx + 208) 0)
    by (apply (gk_sv8_kept W W mem0 mem); [intros x Hx; apply KEEP0; lia | exact HAT0]).
  assert (HPFX : gn_prefix_at cx m W mem (frame_addr ly3 1 fpos)).
  { destruct HPFX0 as (P1 & P2 & P3 & P4 & P5).
    split; [intros i Hi; rewrite (proj1 (KLO (frame_addr ly3 1 fpos + 32 + i) ltac:(unfold GK_CEIL8; lia)));
            exact (P1 i Hi)|].
    split; [rewrite (proj1 (KLO (frame_addr ly3 1 fpos + 32 + Z.of_nat (length (gn_pre cx m)))
              ltac:(unfold GK_CEIL8; lia))); exact P2|].
    split; [intros a Ha; rewrite (proj1 (KLO a ltac:(unfold GK_CEIL8; lia))); exact (P3 a Ha)|].
    split; [exact P4 | exact P5]. }
  clear K1 KEEP0 KLO WK RG0 HFRr HGr.
  (* LS_cnt's msz_ok guard and gdone's msz_ok conjunct, from the model at GRG *)
  pose proof (gn_msz_ok B ly3 S3 W mem m HMOD) as HMSZ.
  pose proof HMOD as (HM4 & HSLOT & HREL & HOUT & HGONE & HLOCK & HWAKE & HNFD & HNFDW & HNFDR & HTU &
    HLST & HLSTW).
  destruct (HPAIRS cx t m HRI) as (hs & HPOK).
  pose proof HPOK as (HLENhs & HFORALL & HNODUP).
  pose proof (proj1 (NoDup_ListNoDup _) HNODUP) as HNDl.
  assert (HPOKi : forall i, (i < length (lm_es m))%nat -> re_eof (nth i (lm_es m) gn_e0) = 0 ->
      gn_pair_ok m (nth i (lm_es m) gn_e0) (nth i hs gn_hj0)).
  { intros i Hi Heof.
    assert (Hini : In (nth i (combine (lm_es m) hs) (gn_e0, gn_hj0)) (combine (lm_es m) hs)).
    { apply nth_In. rewrite length_combine. lia. }
    pose proof (proj1 (Forall_forall _ _) HFORALL _ Hini) as POK.
    rewrite (combine_nth (lm_es m) hs i gn_e0 gn_hj0 ltac:(lia)) in POK.
    cbn [fst snd] in POK. exact (POK Heof). }
  assert (HJS4 : forall j, In j (rig_slots (combine (lm_es m) hs)) -> (j < 4)%nat).
  { intros j Hj. apply in_concat in Hj as (l & Hl & Hjl).
    apply in_map_iff in Hl as (p & <- & Hp).
    destruct (Z.eqb_spec (re_eof (fst p)) 0) as [Heq|Hne]; [|destruct Hjl].
    destruct Hjl as [<- | []].
    exact (proj1 (proj1 (Forall_forall _ _) HFORALL p Hp Heq)). }
  pose proof (gp3_perm_slots (lm_hs m) (rig_slots (combine (lm_es m) hs)) HM4 HNDl HJS4) as HPS.
  assert (HSRCS : concat (map (fun j => slot_blks (nth j (lm_hs m) None))
      (rig_slots (combine (lm_es m) hs))) = rig_srcs (combine (lm_es m) hs)).
  { apply (gp3_srcs_of_slots _ (lm_es m) hs HLENhs).
    intros i Hi Heof. destruct (HPOKi i Hi Heof) as (_ & Hnth & _).
    rewrite Hnth. reflexivity. }
  rewrite HSRCS in HPS.
  destruct HSEP as ((rest0 & HPERM0) & HSEPFP).
  set (OTH := concat (map (fun j => slot_blks (nth j (lm_hs m) None))
    (gp3_cs (rig_slots (combine (lm_es m) hs))))) in *.
  assert (HPERM1 : Permutation (ablocks B ly3 S3)
    ((lm_G m, ATABLE) :: concat (map aentry_blks (lm_es m)) ++ rig_srcs (combine (lm_es m) hs) ++
     aout_blks (lm_cap m) (lm_out m) ++ (OTH ++ input_blks cx ++ rest0))).
  { eapply Permutation_trans; [exact HPERM0|]. unfold model_blks.
    eapply Permutation_trans;
      [exact (gp3_perm_cong (input_blks cx) (concat (map aentry_blks (lm_es m)))
         (aout_blks (lm_cap m) (lm_out m)) rest0 _ _ (lm_G m, ATABLE) HPS)|].
    apply gp3_perm_pre. }
  assert (Hsp1 : spZ (ms_regs ms) = lf_F cx).
  { unfold spZ. rewrite (KR 2%bv ltac:(cbv; tauto)), R2. unfold w64. apply unsigned_lit_small.
    unfold LLVMF_STK in *. lia. }
  destruct (gp3_afn_pre_x cx ly3 S3 fpos kk W mem mdc (ms_regs ms) RIG_STK_x HB HJ (proj1 HFR) Hsp1
    ltac:(rewrite Q1; apply ret_ok_codeptr_v; [lia | reflexivity])
    ltac:(unfold raZ; rewrite Q1, unsigned_lit_small by lia; lia)
    ltac:(rewrite (KR 3%bv ltac:(cbv; tauto)); exact R3)
    ltac:(rewrite (KR 4%bv ltac:(cbv; tauto)); exact R4)
    ltac:(rewrite (KR 8%bv ltac:(cbv; tauto)); exact R8)
    ltac:(unfold RIG_STK_x, RIG_STK, RIG_FRAME, DRAIN_STK, DRAIN_FRAME, SL_STK, SL_FRAME, ASTACK; lia)
    ltac:(unfold RIG_STK_x, RIG_STK, RIG_FRAME, DRAIN_STK, DRAIN_FRAME, SL_STK, SL_FRAME, ASTACK, LLVMF_STK; lia))
    as (ch & HPREc & HSPINE & HTOP).
  (* _gone_p3.v:1108: GN_LS_rig's premises at GRG_x, all held: gn_op (HOP), aentry_ok's |re_U| <= APARTIAL, the model
     blocks' sizes not negative (the AR block law over HPERM0), the pending offsets (Hoff), and the CAPOUT clause;
     A f5d40188e29 *)
  pose proof HOP as (_ & HO0 & Ht0 & _).
  assert (HUs : Forall (fun e => Z.of_nat (length (re_U e)) <= APARTIAL) (lm_es m)).
  { pose proof HREL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & GdAE & _).
    rewrite Forall_forall in GdAE |- *. intros ge gHe.
    destruct (GdAE ge gHe) as (_ & _ & _ & _ & _ & _ & GdC7 & GdC8 & _). lia. }
  assert (HMpos : forall b, In b (model_blks m) -> 0 <= snd b).
  { intros [gp gn] gHb. assert (gHin : In (gp, gn) (ablocks B ly3 S3)).
    { apply (Permutation_in _ (Permutation_sym HPERM0)). apply in_or_app. right. apply in_or_app. left. exact gHb. }
    destruct (gk_blk_x B ARx LAWS BLKN ly3 S3 W mem mdc gp gn HAR gHin) as (_ & _ & GdN). cbn [snd]. lia. }
  assert (Hoff : forall k h, nth k (lm_hs m) None = Some h ->
      (hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
      (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))).
  { intros gk gh gHk.
    assert (gHl : (gk < 4)%nat).
    { destruct (Nat.lt_ge_cases gk (length (lm_hs m))) as [Hlt | Hge]; [lia|].
      rewrite nth_overflow in gHk by exact Hge. discriminate gHk. }
    pose proof (HSLOT gk gHl) as GdSl. unfold aslot in GdSl. rewrite gHk in GdSl.
    destruct GdSl as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & GdOFF & _). exact GdOFF. }
  (* GN_LS_rig's g_capout premise: the entry pre's CAPOUT clause (fr_lib_pre_cf_x, its last conjunct) *)
  assert (HCAPO : exists c, val_mem segs (arm (c_W cx) (c_mem cx)) (rg_capout fr_RG) 8 c /\ 0 <= c <= CAPOUT_MAX).
  { pose proof HB as (_ & GdPRE). unfold fr_lib_pre_cf_x in GdPRE.
    repeat match type of GdPRE with _ /\ _ => destruct GdPRE as (_ & GdPRE) end. exact GdPRE. }
  pose proof (HLSRIG cx t m ly3 S3 hs HLS HRI HPOK HOP HUs HMpos Hoff HCAPO) as BUD. cbv zeta in BUD.
  destruct BUD as (Btr1 & Btr2 & Btr3 & _).
  (* rig_spec_x at the ghost list [], taken at kr := 0 *)
  eassert (HCALL : SRr segs W (cfg_at segs (BASE + AF_fr_relay_instance_gone) (ms_regs ms) mem mdc) _).
  { apply (RIG W ly3 S3 [] (ms_regs ms) mem mdc ch (lm_G m) (gn_id cx m) (lm_es m) hs
      (lm_c m) (lm_O m) (lm_mx m) (lm_cap m) (lm_out m)) with (kr := 0%nat).
    - exact HPREc.
    - rewrite Hsp1. exact HFm32.
    - rewrite Hfrs. change (count_cid 1 [(1, fpos)]) with 1. change (fs_frames 1) with 8192. lia.
    - exact RGP.
    - rewrite Q10, E21. reflexivity.
    - exact (gp3_id_rng cx m).
    - exact HLOCK.
    - exact HREL.
    - exact HOUT.
    - exact HRV.
    - exact HLENhs.
    - apply Forall_forall. intros p Hp Heof.
      apply (In_nth _ _ (gn_e0, gn_hj0)) in Hp as (i & Hi & Hpi).
      rewrite length_combine in Hi. rewrite <- Hpi in Heof |- *.
      rewrite (combine_nth (lm_es m) hs i gn_e0 gn_hj0 ltac:(lia)) in Heof |- *.
      cbn [fst snd] in Heof |- *.
      destruct (HPOKi i ltac:(lia) Heof) as (Hj4 & Hnth & Hfd & Hskip & HU & Hps1 & Hps2 & Hps3).
      split; [exact Hj4|]. split.
      + pose proof (HSLOT (snd (nth i hs gn_hj0)) Hj4) as Hsl.
        unfold aslot in Hsl. rewrite Hnth in Hsl. exact Hsl.
      + split.
        * rewrite <- Hfd. exact (gp3_others cx t m ly3 S3 W mem _ (fst (nth i hs gn_hj0)) HRI HMOD Hj4 Hnth).
        * split; [exact Hfd|]. split; [exact Hskip|]. split; [exact HU|].
          split; [exact Hps1|]. split; [exact Hps2 | exact Hps3].
    - exact HNODUP.
    - exists (OTH ++ input_blks cx ++ rest0). exact HPERM1.
    - exact Btr1.
    - exact Btr2.
    - exact Btr3.
    - (* the room round: RM is NP at the instance (RPNP), and NP S3 is the arm's threaded invariant *)
      apply (proj2 (RPNP S3 _)). exact HNP.
    - (* the counts: LS_cnt gives them at the LS state, which IS this call's state, and GN_CNT_rig says rig's
         premise peak fits inside the arm's peak gn_pk *)
      pose proof HOP as (_ & _ & HtO & _).
      pose proof (LSCNT cx t m ly3 S3 hs HLS HRI HPOK HMSZ HtO HUs HMpos Hoff) as HC0.
      unfold cnt_ok_pk in HC0 |- *.
      pose proof (CNTRIG cx m hs (rp_Psec RP)) as Q1s. cbv beta in Q1s.
      pose proof (CNTRIG cx m hs (rp_P24 RP)) as Q2s. cbv beta in Q2s.
      split; [|split].
      + pose proof (proj1 HC0). lia.
      + pose proof (proj1 (proj2 HC0)). lia.
      + intros c Hc. pose proof (proj2 (proj2 HC0) c Hc).
        pose proof (CNTRIG cx m hs (rp_Pcls RP c)) as Q3s. cbv beta in Q3s. lia.
    - (* rig_spec_x's room above sp: from the entry's astk_ok through the journal's layout *)
      exact HTOP.
    - (* the free's caller context: K0's CTX_AFREE rows [0x82fb8; 0x84b4c(; 0x82240)]: relay_instance_gone's free
         returns to pc + 792 = 0x82fb8, relay_instance_gone to AF_gp3_ret = 0x84b4c, LLVMFuzzerTestOneInput to
         RA_LLVMF = 0x82240 when its record is on the chain *)
      destruct HSPINE as [Hsc | Hsc]; rewrite Hsc; unfold raZ; rewrite Q1, unsigned_lit_small by lia;
        vm_compute; repeat (first [left; reflexivity | right]). }
  eapply SRr_bind; [exact HCALL|].
  intros W2 c2 Hwle2 HPOST.
  destruct HPOST as (ly4 & S4 & Hp4 & regs4 & mem4 & md4 & k4 & qs & c4 & O4 & cap4 & out4 & rest4 & -> &
    HJc & HPRES & HAPK & HMO & HRM4 & HLOCK4 & HRREL & HLENq & HREL4 & HOUT4 & HSRC4 & HKEEPS & HPERMa & HPERMb).
  (* the post's ghost list is [] (HP0 on its journal's ARx) *)
  hp0g HJc.
  rewrite Hsp1 in HJc. clear HCALL.
  assert (DEC : forall u v : Z * Z, {u = v} + {u <> v}) by (decide equality; apply Z.eq_dec).
  (* ---- what relay_instance_gone's journal keeps ---- *)
  destruct (gp3_keeps_x (G_RIG B fr_RG) RIG_STK_x (lf_F cx)
    (rig_fp (lm_G m) (lm_es m) hs (lm_cap m) (lm_out m)) ly3 S3 W mem mdc [] ly4 S4 W2 mem4 md4 k4 HJc)
    as (KHI & KBLKv & KFRMv & KIMGv & KPRESc & HAR4 & Hfrs4 & HLY & Hwle4).
  cbn [app] in Hfrs4.
  assert (HFFeq : frame_addr ly4 1 fpos = frame_addr ly3 1 fpos).
  { unfold frame_addr. destruct HLY as (_ & _ & _ & _ & _ & HFly & _). rewrite HFly. reflexivity. }
  assert (HFLeq : flag_addr ly4 1 fpos = flag_addr ly3 1 fpos).
  { unfold flag_addr. destruct HLY as (_ & _ & _ & _ & _ & HFly & _). rewrite HFly. reflexivity. }
  assert (Hin1 : In (1, fpos) (frames S3)) by (rewrite Hfrs; left; reflexivity).
  assert (Hin1' : In (1, fpos) (frames S4)) by (rewrite Hfrs4; exact Hin1).
  assert (HAsub : forall b, In b ((lm_G m, ATABLE) :: concat (map aentry_blks (lm_es m)) ++
      rig_srcs (combine (lm_es m) hs) ++ aout_blks (lm_cap m) (lm_out m)) -> In b (ablocks B ly3 S3)).
  { intros b Hb. apply (Permutation_in _ (Permutation_sym HPERMa)).
    rewrite <- gp3_assoc4. apply in_app_iff. left. exact Hb. }
  assert (HMODBLK : forall b, In b ((lm_G m, ATABLE) :: concat (map aentry_blks (lm_es m)) ++
      rig_srcs (combine (lm_es m) hs) ++ aout_blks (lm_cap m) (lm_out m)) -> In b (model_blks m)).
  { intros b [<- | Hb]; [left; reflexivity|]. unfold model_blks. right.
    apply in_app_iff in Hb as [Hb | Hb]; [apply in_app_iff; left; exact Hb|].
    apply in_app_iff. right. apply in_app_iff in Hb as [Hb | Hb].
    - apply in_app_iff. left. apply (Permutation_in _ (Permutation_sym HPS)). apply in_app_iff. left. exact Hb.
    - apply in_app_iff. right. exact Hb. }
  assert (HFPS : forall a, fp_spares (rig_fp (lm_G m) (lm_es m) hs (lm_cap m) (lm_out m)) a)
    by exact (gp3_fp_spares_x ly3 S3 W mem mdc _ HAR HAsub).
  assert (HAPART : forall b a, In b rest4 -> fst b <= a < fst b + req_size (snd b) ->
      ~ inFP (rig_fp (lm_G m) (lm_es m) hs (lm_cap m) (lm_out m)) a).
  { intros b a Hb Hr Hin. apply gp3_inFP_fp in Hin as (b' & Hb' & Hr').
    refine (gp3_apart_x ly3 S3 W mem mdc _ _ b' b a HAR _ Hb' Hb Hr' Hr).
    rewrite gp3_assoc4. exact HPERMa. }
  assert (HNGblk : forall b a, In b (ablocks B ly3 S3) -> fst b <= a < fst b + req_size (snd b) ->
      ~ inG (G_RIG B fr_RG) a).
  { intros [p n] a Hb Hr HinG. cbn [fst snd] in Hr.
    exact (blk_img_x _ _ _ LAWS ly3 S3 [] W mem mdc p n a HAR Hb Hr (proj1 (HG a (HGRIG a HinG)))). }
  (* ---- the callee's journal inside the arm's (W_journal_x.v ajournal_gx_sub_x) ---- *)
  assert (HFP1 : forall a, inFP (rig_fp (lm_G m) (lm_es m) hs (lm_cap m) (lm_out m)) a ->
      (inFP (lf_FP fr_FP cx) a /\ exists b n, In (b, n) (ablocks B ly3 S3) /\ b <= a < b + req_size n) \/
      in_tmp_block (ablocks B (c_ly cx) (c_S cx)) (ablocks B ly3 S3) a).
  { intros a Hin. apply gp3_inFP_fp in Hin as (b & Hb & Hr).
    destruct (gn_sep_req B fr_FP cx m ly3 S3 (conj (ex_intro _ rest0 HPERM0) HSEPFP) b (HMODBLK b Hb))
      as [Hnew | Hfp].
    - right. exists (fst b), (snd b). rewrite <- surjective_pairing.
      split; [exact (HAsub b Hb)|]. split; [exact Hnew | exact Hr].
    - left. split; [exact (Hfp a Hr)|].
      exists (fst b), (snd b). rewrite <- surjective_pairing. split; [exact (HAsub b Hb) | exact Hr]. }
  assert (HJcG : AJ0 G_fr 0 [] RIG_STK_x (lf_F cx)
      (rig_fp (lm_G m) (lm_es m) hs (lm_cap m) (lm_out m)) ly3 S3 W mem mdc [] ly4 S4 W2 mem4 md4 k4).
  { apply (ajournal_gx_G_mono_x segs B PST ARx (G_RIG B fr_RG) G_fr); [exact HGRIG | exact HJc]. }
  pose proof (ajournal_gx_sub_x segs B PST ARx LAWS pa_segs_low G_fr LLVMF_STK (spZ (c_regs cx)) 0 []
     (lf_FP fr_FP cx) (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 [] W mem mdc kk
     RIG_STK_x (lf_F cx) 0 [] (rig_fp (lm_G m) (lm_es m) hs (lm_cap m) (lm_out m)) [] ly4 S4 [] W2 mem4 md4 k4
     HJ HJcG
     ltac:(unfold RIG_STK_x, RIG_STK, RIG_FRAME, DRAIN_STK, DRAIN_FRAME, SL_STK, SL_FRAME, ASTACK, LLVMF_STK in *; lia)
     ltac:(lia) ltac:(lia)
     ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha))
     HG HFP1) as HJ2.
  cbn [app] in HJ2.
  destruct (gp3_keeps_x G_fr LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx) (c_ly cx) (c_S cx) (c_W cx)
    (c_mem cx) (c_md cx) [(1, fpos)] ly4 S4 W2 mem4 md4 (kk + k4) HJ2) as (_ & _ & _ & _ & KPRES2 & _).
  (* ---- the bytes the cut reads, kept across the call ---- *)
  assert (KSTKv : forall a, lf_F cx <= a < 2 ^ 64 ->
      aview segs (w_H W2) mem4 a = aview segs (w_H W) mem a).
  { intros a Ha. apply KHI; [lia | | lia | lia].
    intros HinG. pose proof (pa_img_range a (proj1 (HG a (HGRIG a HinG)))). lia. }
  assert (KSTK : forall a, lf_F cx <= a < spZ (c_regs cx) -> abyte_kept W mem W2 mem4 a).
  { intros a Ha. split; [apply KSTKv; lia|]. intros _.
    apply gp3_wr_pres. apply KPRES2. unfold LLVMF_STK in *. lia. }
  assert (KFRM : forall a, frame_addr ly3 1 fpos <= a < frame_addr ly3 1 fpos + 128 ->
      abyte_kept W mem W2 mem4 a).
  { intros a Ha.
    assert (HNF : ~ inFP (rig_fp (lm_G m) (lm_es m) hs (lm_cap m) (lm_out m)) a)
      by exact (gp3_not_fp_frame_x ly3 S3 W mem mdc _ 1 fpos a HAR HAsub Hin1
                  ltac:(change (fs_frame_bytes 1) with 128; lia)).
    split.
    - apply (KFRMv 1 fpos a Hin1);
        [left; unfold in_zr, frame_rng; cbn [fst snd]; change (fs_frame_bytes 1) with 128; lia
        | exact HNF | lia |].
      intros HinG. exact (frm_img_x _ _ _ LAWS ly3 S3 [] W mem mdc 1 fpos a HAR Hin1
        ltac:(change (fs_frame_bytes 1) with 128; lia) (proj1 (HG a (HGRIG a HinG)))).
    - intros _. apply gp3_wr_pres.
      destruct (alx_frames _ _ _ LAWS ly4 S4 [] W2 mem4 md4 1 fpos HAR4 Hin1') as (_ & _ & Hb & _).
      rewrite HFFeq in Hb. exact (proj1 (Hb a ltac:(change (fs_frame_bytes 1) with 128; lia))). }
  assert (KSH : forall a, SB + frame_addr ly3 1 fpos / 8 <= a < SB + frame_addr ly3 1 fpos / 8 + 16 ->
      abyte_kept W mem W2 mem4 a).
  { intros a Ha.
    assert (Hsh : in_zr a (shadow_addr (frame_addr ly3 1 fpos), fs_frame_bytes 1 / 8)).
    { unfold in_zr, shadow_addr. cbn [fst snd]. change (fs_frame_bytes 1 / 8) with 16.
      rewrite <- SB_SHADOW_OFF. lia. }
    assert (HNF : ~ inFP (rig_fp (lm_G m) (lm_es m) hs (lm_cap m) (lm_out m)) a).
    { apply (gp3_not_fp_shadow_x ly3 S3 W mem mdc _ a HAR HAsub).
      unfold SB, kLowShadowBeg, kHighMemBeg in *. lia. }
    split.
    - apply (KFRMv 1 fpos a Hin1); [right; exact Hsh | exact HNF | unfold SB in *; lia |].
      intros HinG. pose proof (pa_img_range a (proj1 (HG a (HGRIG a HinG)))). unfold SB in *. lia.
    - intros _. apply gp3_wr_pres.
      destruct (alx_frames _ _ _ LAWS ly4 S4 [] W2 mem4 md4 1 fpos HAR4 Hin1') as (_ & _ & _ & Hsh4).
      rewrite HFFeq in Hsh4.
      assert (Hi : 0 <= a - shadow_addr (frame_addr ly3 1 fpos) < fs_frame_bytes 1 / 8)
        by (unfold in_zr in Hsh; cbn [fst snd] in Hsh; lia).
      specialize (Hsh4 _ Hi).
      replace (shadow_addr (frame_addr ly3 1 fpos) + (a - shadow_addr (frame_addr ly3 1 fpos))) with a
        in Hsh4 by lia.
      exact (proj1 Hsh4). }
  pose proof RGP as (_ & _ & _ & _ & _ & _ & RGP7 & _).
  assert (KIMG : forall a, inG gn_cells a -> ~ inG (G_RIG B fr_RG) a ->
      ~ (as_errno B <= a < as_errno B + 4) -> abyte_kept W mem W2 mem4 a).
  { intros a Hc HnR Herr. pose proof (HGCELLS a Hc) as Hfr. destruct (HG a Hfr) as (Himg & Hown & _).
    split; [|intros _; exact (GWR _ _ a Hfr)].
    apply KIMGv; [exact Himg | exact Hown | exact Herr | apply HFPS | | exact HnR].
    pose proof (pa_img_range a Himg). lia. }
  assert (KG4 : forall a, gp3_g4 a -> abyte_kept W mem W2 mem4 a).
  { intros a H4. pose proof (gp3_errno_g4 a H4) as Herr.
    exact (KIMG a (gp3_g4_cells a H4) (gp3_not_RIG a Herr (or_introl H4)) Herr). }
  assert (KWAKE : forall a, rg_wake fr_RG + 4 <= a < rg_wake fr_RG + 8 -> abyte_kept W mem W2 mem4 a).
  { intros a Ha. pose proof (RGP7 a ltac:(unfold rg_rng; right; right; right; left; exact Ha)) as (_ & _ & Herr).
    exact (KIMG a (gp3_wake_cell a Ha) (gp3_not_RIG a Herr (or_intror Ha)) Herr). }
  assert (Hrest : Permutation rest4 (OTH ++ input_blks cx ++ rest0)).
  { apply (Permutation_app_inv_l ((lm_G m, ATABLE) :: concat (map aentry_blks (lm_es m)) ++
      rig_srcs (combine (lm_es m) hs) ++ aout_blks (lm_cap m) (lm_out m))).
    rewrite !gp3_assoc4. exact (Permutation_trans (Permutation_sym HPERMa) HPERM1). }
  assert (Hrest4 : forall b, In b rest4 -> In b (ablocks B ly4 S4)).
  { intros b Hb. apply (Permutation_in _ (Permutation_sym HPERMb)).
    right. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. right. exact Hb. }
  assert (KBLK : forall b a, In b rest4 -> In b (ablocks B ly3 S3) ->
      fst b <= a < fst b + req_size (snd b) -> abyte_kept W mem W2 mem4 a).
  { intros b a Hb Hb3 Hr. pose proof (Hrest4 b Hb) as Hb4.
    pose proof (HAPART b a Hb Hr) as HNF. pose proof (HNGblk b a Hb3 Hr) as HNR.
    destruct b as [p n]. cbn [fst snd] in Hr.
    destruct (gk_blk_x B ARx LAWS BLKN ly3 S3 W mem mdc p n HAR Hb3) as (P1 & P2 & P3).
    split.
    - replace a with (p + (a - p)) by lia.
      apply (KBLKv p n (a - p) Hb3 Hb4); [lia | | lia |];
        replace (p + (a - p)) with a by lia; assumption.
    - intros _. apply gp3_wr_pres.
      exact (proj1 (proj1 (proj2 (proj2 (proj2 (proj2
        (al0_blocks B ARx LAWS BLKN ly4 S4 W2 mem4 md4 p n HAR4 Hb4))))) a Hr)). }
  (* ---- the model after the call ---- *)
  set (js := rig_slots (combine (lm_es m) hs)) in *.
  set (hs1 := map (gp3_pick (lm_es m) hs qs (lm_hs m)) (seq 0 4)).
  set (m1 := LM (gn_kq cx m) hs1 (lm_G m) (map fst qs) c4 O4 (lm_mx m) cap4 out4 (lm_gn m) (lm_nfd m)).
  assert (Hhs1 : forall j, (j < 4)%nat -> nth j hs1 None = gp3_pick (lm_es m) hs qs (lm_hs m) j)
    by (intros j Hj; exact (gp3_nth_map4 _ None j Hj)).
  assert (Hlen1 : length hs1 = 4%nat) by (unfold hs1; rewrite length_map, length_seq; reflexivity).
  assert (HAFTER : gn_after_rig cx m hs qs c4 O4 cap4 out4 m1).
  { unfold gn_after_rig, m1. cbn [lm_k lm_G lm_es lm_c lm_O lm_mx lm_cap lm_out lm_gn lm_nfd lm_hs].
    do 10 (split; [reflexivity|]). split; [exact Hlen1|]. split.
    - intros j Hj Hnin. rewrite (Hhs1 j Hj). exact (gp3_pick_none _ _ _ _ j HLENhs Hnin).
    - intros i Hi Heof. pose proof (proj1 (HPOKi i Hi Heof)) as Hj4.
      rewrite (Hhs1 _ Hj4). exact (gp3_pick_some _ _ _ _ i Hi HLENhs HNDl Heof). }
  assert (HMOD1 : amodel_at B ly4 S4 W2 mem4 m1).
  { unfold amodel_at, m1. cbn [lm_hs lm_G lm_es lm_c lm_O lm_mx lm_cap lm_out lm_gn lm_nfd].
    split; [exact Hlen1|].
    split.
    { intros i Hi. rewrite (Hhs1 i Hi).
      destruct (in_dec Nat.eq_dec i js) as [Hdr | Hnd].
      - destruct (gp3_in_slots_find (lm_es m) hs i HLENhs Hdr) as (i0 & Hi0 & Heof0 & Hsl0).
        subst i. rewrite (gp3_pick_some (lm_es m) hs qs (lm_hs m) i0 Hi0 HLENhs HNDl Heof0).
        exact (HSRC4 i0 Hi0 Heof0).
      - rewrite (gp3_pick_none (lm_es m) hs qs (lm_hs m) i HLENhs Hnd).
        apply (gp3_slot_kept_x ly3 S3 W mem mdc ly4 S4 W2 mem4 i _ HAR (HSLOT i Hi) Hi).
        + intros a Ha. apply HKEEPS; [unfold ASRC in *; lia|].
          intros j Hj Hrj.
          assert (Hji : j <> i) by (intros ->; exact (Hnd Hj)).
          pose proof (HJS4 j Hj) as Hj4.
          assert (HZ : Z.of_nat j <> Z.of_nat i) by (intros Heq; apply Hji; lia).
          unfold ASRC in *. lia.
        + intros b Hb.
          assert (HbO : In b OTH).
          { unfold OTH. apply in_concat. exists (slot_blks (nth i (lm_hs m) None)). split; [|exact Hb].
            apply in_map_iff. exists i. split; [reflexivity | apply gp3_cs_spec; split; [exact Hi | exact Hnd]]. }
          assert (Hbr : In b rest4)
            by (apply (Permutation_in _ (Permutation_sym Hrest)); apply in_app_iff; left; exact HbO).
          assert (Hb3 : In b (ablocks B ly3 S3)).
          { destruct (nth i (lm_hs m) None) as [h|] eqn:Ei; [|destruct Hb].
            pose proof (HSLOT i Hi) as Hsl. unfold aslot in Hsl. rewrite Ei in Hsl.
            exact (proj2 (gk_asrc_x B ARx LAWS BLKN ly3 S3 W mem mdc _ h HAR Hsl
              ltac:(unfold fr_RG; cbn; unfold ASRC; lia)
              ltac:(unfold fr_RG, GK_CEIL8; cbn; unfold ASRC; pose proof gk_ceil_lo; lia)) b Hb). }
          split; [exact (Hrest4 b Hbr)|].
          intros a Ha. apply (KBLK b a Hbr Hb3). destruct b as [p n]. cbn [fst snd] in *.
          destruct (gk_blk_x B ARx LAWS BLKN ly3 S3 W mem mdc p n HAR Hb3) as (_ & _ & Hn). lia. }
    split; [exact HREL4|].
    split; [exact HOUT4|].
    split.
    { apply (agone_at_kept fr_RG W mem W2 mem4 _ HGONE). intros r Hr a Ha. destruct Hr as [<- | []].
      cbn [fst snd] in Ha. apply KG4. unfold gp3_g4. lia. }
    split; [exact HLOCK4|].
    split.
    { apply (awake_at_kept fr_RG W mem W2 mem4 HWAKE). intros r Hr a Ha. destruct Hr as [<- | []].
      cbn [fst snd] in Ha. apply KWAKE. lia. }
    split; [apply (akept_vm W mem); [intros x Hx; apply KG4; unfold gp3_g4; cbn in Hx; lia | exact HNFD]|].
    split; [apply (akept_awr W mem); [intros x Hx; apply KG4; unfold gp3_g4; lia | exact HNFDW]|].
    split; [exact HNFDR|].
    split; [apply (akept_vm W mem); [intros x Hx; apply KG4; unfold gp3_g4; cbn in Hx; lia | exact HTU]|].
    split; [destruct HLST as [lst Hlst]; exists lst;
            apply (akept_vm W mem); [intros x Hx; apply KG4; unfold gp3_g4; cbn in Hx; lia | exact Hlst]|].
    apply (akept_awr W mem); [intros x Hx; apply KG4; unfold gp3_g4; lia | exact HLSTW]. }
  (* the live blocks after the call: the model's, the input, and the same rest *)
  assert (HP1 : Permutation (ablocks B ly4 S4) (input_blks cx ++ model_blks m1 ++ rest0)).
  { assert (HOTH1 : concat (map (fun j => slot_blks (nth j hs1 None)) (gp3_cs js)) = OTH).
    { unfold OTH. f_equal. apply map_ext_in. intros j Hj. apply gp3_cs_spec in Hj as [Hj4 Hnin].
      rewrite (Hhs1 j Hj4), (gp3_pick_none _ _ _ _ j HLENhs Hnin). reflexivity. }
    assert (HNEW : concat (map (fun j => slot_blks (nth j hs1 None)) js) =
        concat (map (fun p => if re_eof (fst (fst p)) =? 0 then asrc_blks (snd (snd p)) else [])
           (combine (combine (lm_es m) hs) qs))).
    { apply (gp3_newsrcs_of_slots _ (lm_es m) hs qs HLENhs HLENq).
      intros i Hi Heof. pose proof (proj1 (HPOKi i Hi Heof)) as Hj4.
      rewrite (Hhs1 _ Hj4), (gp3_pick_some _ _ _ _ i Hi HLENhs HNDl Heof). reflexivity. }
    pose proof (gp3_perm_slots hs1 js Hlen1 HNDl HJS4) as HPS1.
    rewrite HNEW, HOTH1 in HPS1.
    eapply Permutation_trans; [exact HPERMb|].
    eapply Permutation_trans.
    { apply perm_skip. apply Permutation_app_head. apply Permutation_app_head. apply Permutation_app_head.
      exact Hrest. }
    apply Permutation_sym. unfold model_blks, m1. cbn [lm_G lm_es lm_hs lm_cap lm_out].
    eapply Permutation_trans;
      [exact (gp3_perm_cong (input_blks cx) (concat (map aentry_blks (map fst qs)))
         (aout_blks cap4 out4) rest0 _ _ (lm_G m, ATABLE) HPS1)|].
    apply gp3_perm_pre. }
  assert (HSEP1 : ablocks_sep B fr_FP cx m1 ly4 S4).
  { split; [exists rest0; exact HP1|].
    intros b Hb.
    destruct (in_dec DEC b (ablocks B (c_ly cx) (c_S cx))) as [Hent | Hnent]; [|left; exact Hnent].
    assert (Hb4 : In b (ablocks B ly4 S4))
      by (apply (Permutation_in _ (Permutation_sym HP1)); apply in_app_iff; right; apply in_app_iff; left; exact Hb).
    destruct (in_dec DEC b (ablocks B ly3 S3)) as [Hb3 | Hnb3].
    - assert (Hbm : In b (model_blks m)).
      { pose proof (Permutation_in _ HPERM0 Hb3) as Hb0.
        pose proof (Permutation_NoDup HP1 (gp3_nodup_blocks_x ly4 S4 W2 mem4 md4 HAR4)) as ND1.
        apply in_app_iff in Hb0 as [Hb0 | Hb0].
        - exfalso. exact (gp3_nodup_app_neq _ _ b ND1 Hb0 ltac:(apply in_app_iff; left; exact Hb)).
        - apply in_app_iff in Hb0 as [Hb0 | Hb0]; [exact Hb0|]. exfalso.
          rewrite app_assoc in ND1.
          exact (gp3_nodup_app_neq _ _ b ND1 ltac:(apply in_app_iff; right; exact Hb) Hb0). }
      exact (HSEPFP b Hbm).
    - right. intros a Ha.
      destruct (gp3_inner_x G_fr LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx) (c_ly cx) (c_S cx) (c_W cx)
        (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem mdc kk HJ) as (memS & HJi & _).
      pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & C12 & _).
      destruct b as [p n]. cbn [fst snd] in Ha.
      destruct (gk_blk_x B ARx LAWS BLKN ly4 S4 W2 mem4 md4 p n HAR4 Hb4) as (_ & _ & Hn).
      replace a with (p + (a - p)) by lia.
      apply (C12 p n (a - p) Hent Hnb3). lia. }
  (* the arm's other facts *)
  assert (HFR1 : gframe cx fake_shadow_open (frame_addr ly4 1 fpos) W2 mem4).
  { rewrite HFFeq. apply (gp3_gframe_kept cx _ _ W W2 mem mem4 HFR eq_refl); [lia | exact KSTK | exact KFRM | exact KSH]. }
  assert (HFLAG' : sv8 W2 mem4 (frame_addr ly4 1 fpos + 120) (flag_addr ly4 1 fpos)).
  { rewrite HFFeq, HFLeq. apply (gk_sv8_kept W W2 mem mem4); [intros x Hx; apply KFRM; lia | exact HFLAG]. }
  assert (H16' : sv8 W2 mem4 (lf_F cx + 16) (c_p cx + gn_kq cx m))
    by (apply (gk_sv8_kept W W2 mem mem4); [intros x Hx; apply KSTK; lia | exact H16]).
  assert (H144' : sv8 W2 mem4 (lf_F cx + 144) (c_n cx - gn_kq cx m))
    by (apply (gk_sv8_kept W W2 mem mem4); [intros x Hx; apply KSTK; lia | exact H144]).
  assert (H88' : sv8 W2 mem4 (lf_F cx + 88) t)
    by (apply (gk_sv8_kept W W2 mem mem4); [intros x Hx; apply KSTK; lia | exact H88]).
  assert (SV24' : sv8 W2 mem4 (lf_F cx + 24) HI_G_NOUT)
    by (apply (gk_sv8_kept W W2 mem mem4); [intros x Hx; apply KSTK; lia | exact SV24]).
  assert (HIN' : ainput_at B cx ly4 S4 W2 mem4).
  { apply (gp3_ainput_kept cx ly3 S3 W mem ly4 S4 W2 mem4 HIN HlenP). intros Hn.
    assert (Hb0r : In (c_p cx, c_n cx) rest4).
    { apply (Permutation_in _ (Permutation_sym Hrest)). apply in_app_iff. right. apply in_app_iff. left.
      unfold input_blks. rewrite (proj2 (Z.eqb_neq (c_n cx) 0) ltac:(lia)). left. reflexivity. }
    assert (Hb03 : In (c_p cx, c_n cx) (ablocks B ly3 S3)).
    { destruct HIN as ([(Hn0 & _) | (_ & Hin)] & _); [lia | exact Hin]. }
    split; [exact (Hrest4 _ Hb0r)|].
    intros a Ha. apply (KBLK _ a Hb0r Hb03). cbn [fst snd]. unfold req_size.
    rewrite (proj2 (Z.eqb_neq (c_n cx) 0) ltac:(lia)). lia. }
  assert (HRV' : rom_view segs W2 mem4)
    by exact (ajournal_gx_rom_view_x segs B PST ARx LAWS pa_segs_low (G_RIG B fr_RG) 0 []
                _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc gp3_rom_out gp3_rom_pst HRV).
  assert (HJT' : jt_rom W2 mem4) by exact (gp3_jt_kept W W2 mem mem4 HRV HRV' HJT).
  assert (HREADS' : forall j, (j < 4)%nat -> gn_sv4 W2 mem4 (lf_F cx + 192 + 4 * Z.of_nat j) (gn_reads m j)).
  { intros j Hj. unfold gn_sv4. apply (akept_vm W mem); [|exact (HREADS j Hj)].
    intros x Hx. apply KSTK. cbn in Hx. lia. }
  assert (HAWR' : awr W2 mem4 (lf_F cx + 192) 16)
    by (apply (akept_awr W mem); [intros x Hx; apply KSTK; lia | exact HAWR]).
  assert (HAT' : sv8 W2 mem4 (lf_F cx + 208) 0)
    by (apply (gk_sv8_kept W W2 mem mem4); [intros x Hx; apply KSTK; lia | exact HAT]).
  assert (HPFX' : gn_prefix_at cx m W2 mem4 (frame_addr ly3 1 fpos)).
  { destruct HPFX as (P1 & P2 & P3 & P4 & P5).
    split; [intros i Hi; rewrite (proj1 (KFRM (frame_addr ly3 1 fpos + 32 + i) ltac:(lia))); exact (P1 i Hi)|].
    split; [rewrite (proj1 (KFRM (frame_addr ly3 1 fpos + 32 + Z.of_nat (length (gn_pre cx m))) ltac:(lia)));
            exact P2|].
    split; [intros a Ha; rewrite (proj1 (KFRM a ltac:(lia))); exact (P3 a Ha)|].
    split; [exact P4 | exact P5]. }
  (* what rig_post_x says of the new table: its functional relation, its length, and the model clauses of
     aentry_ok that its arelay_at gives of every entry (the base's gn_rig_ok) *)
  assert (HROK : gn_rig_ok cx m hs qs c4 O4 cap4).
  { split; [exact HRREL|]. split; [exact HLENq|].
    pose proof HREL4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HAEq & HNDq & _).
    split; [|exact HNDq].
    rewrite Forall_forall in HAEq |- *. intros e He.
    destruct (HAEq e He) as (E1 & E2 & E3 & E4 & E5 & _ & _ & _ & _ & _ & E11 & _ & _ & E14 & _).
    exact (conj E1 (conj E2 (conj E3 (conj E4 (conj E5 (conj E11 E14)))))). }
  assert (HDONE : gdone RINV cx t m m1).
  { exists hs, qs, c4, O4, cap4, out4. split; [exact HPOK|]. split; [exact HAFTER|].
    split; [exact HROK|]. split; [exact HRI|]. split; [exact HOP|].
    (* _gone_p3.v:1461: the facts of amodel_at m (GRG_x's gst_x) that gdone carries for GN_RI_step / GN_RI_end *)
    pose proof HREL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HAE0 & _).
    split.
    { rewrite Forall_forall in HAE0 |- *. intros e He.
      destruct (HAE0 e He) as (_ & _ & _ & _ & _ & _ & _ & _ & HU & _ & _ & _ & _ & _ & HK).
      split; [exact HU|].
      rewrite Forall_forall in HK |- *. intros k Hk.
      destruct (HK k Hk) as (_ & _ & Hz & Hl). exact (conj Hz Hl). }
    split.
    { pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
        _ & _ & GdC).
      destruct GdC as [(GdC & _) | (GdC & _)]; lia. }
    split.
    { rewrite Forall_forall in HAE0 |- *. intros ge gHe.
      destruct (HAE0 ge gHe) as (_ & _ & _ & _ & _ & GdC6 & GdC7 & GdC8 & _ & _ & _ & GdC12 & _ & _ & _).
      split; [lia|]. split; [exact GdC6|].
      destruct GdC12 as [GdC12 | (GdH & _ & GdK1 & GdK2 & _)];
        [left; exact GdC12 | right; exact (conj GdH (conj GdK1 GdK2))]. }
    split.
    2: {
      split; [exact HMpos|]. split; [exact HMSZ|].
      { (* GN_CNT_step's C2: the representation clause of the table relay_instance_gone leaves (rig_post's
         arelay_at .. (map fst qs), aentry_ok W_rep.v:134-135) *)
      pose proof HREL4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & GdAEq & _).
      rewrite Forall_forall in GdAEq |- *. intros ge gHe.
      destruct (GdAEq ge gHe) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & GdC12 & _ & _ & _).
      destruct GdC12 as [GdC12 | (GdH & _ & GdK1 & GdK2 & _)];
        [left; exact GdC12 | right; exact (conj GdH (conj GdK1 GdK2))]. }
    }
    rewrite Forall_forall. intros go gHo. apply (In_nth (lm_hs m) go None) in gHo as (gi & gHi & <-).
    pose proof (HSLOT gi ltac:(lia)) as GdSl. unfold aslot in GdSl.
    destruct (nth gi (lm_hs m) None) as [gh0|]; [|exact I].
    destruct GdSl as (_ & _ & _ & _ & _ & _ & _ & _ & _ & GdPL & _ & _ & _ & _ & GdOFF & _).
    split; [exact GdOFF|].
    destruct GdPL as (_ & _ & _ & _ & _ & _ & _ & _ & GdF).
    rewrite Forall_forall in GdF |- *. intros gr gHr. destruct (GdF gr gHr) as (_ & _ & _ & GdNe).
    exact (GdNe eq_refl). }
  (* _gone_p3.v:1515: the block relation from the LS state (ly3, S3) to the state after the call (ly4, S4): HP1
     is at the SAME rest0 as the entry's ablocks_sep (HPERM0); any rest of (ly3, S3) is a permutation of rest0.
     KF-COUNT: the meter cost is relay_instance_gone's own (rig_post_x's HMO), at the pairing hs gdone carries *)
  assert (HLS1 : exists ly0 S0 cst, LSx cx t m ly0 S0 /\ mo_le MT S0 S4 cst /\ gn_cst MT cx m m1 0 cst /\
    gn_tie B cx m ly0 S0 m1 ly4 S4).
  { exists ly3, S3. eexists. split; [exact HLS|]. split; [exact HMO|].
    split.
    { eexists. split; [exists hs, qs, c4, O4, cap4, out4; split; [exact HPOK|]; split; [exact HAFTER | reflexivity]|].
      rewrite Z.add_0_r. apply Z.le_refl. }
    split; [exists rest0; exact HPERM0|].
    intros rest Hr.
    assert (Hrr : Permutation rest rest0).
    { apply (Permutation_app_inv_l (input_blks cx ++ model_blks m)). rewrite <- !app_assoc.
      exact (Permutation_trans (Permutation_sym Hr) HPERM0). }
    eapply Permutation_trans; [exact HP1|].
    apply Permutation_app_head. apply Permutation_app_head. apply Permutation_sym. exact Hrr. }
  (* ---- 0x84b4c: auipc a0,0x554; addi s4,a0,788; addi s5,s1,192; addi s6,s1,208, up to the loop's head ---- *)
  assert (HQ1 : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + AF_gp3_ret)) by (rewrite Q1; reflexivity).
  rewrite HQ1.
  (* NOTE: do not clear HFr; it is gn_nums_x' frame bound, which the run tactics' fresh HFr would shadow *)
  try clear HS SHOK HF.
  assert (RR : forall r : bv 5, acallee_saved (bv_unsigned r) -> In r gp3_kept -> getr regs4 r = getr regs r)
    by (intros r H1 H2; rewrite (gp3_pres (ms_regs ms) regs4 r HPRES H1); exact (KR r H2)).
  destruct (gp3_entry2 W2 regs4 mem4) as [HSb SHOKb].
  remember (Eimg (Ereg regs4 gp3_extra)) as Eb eqn:HEb.
  assert (HEIb : img_env VAL A_LIM Eb) by (subst Eb; apply Eimg_env).
  assert (HAEb : env_agree 32 (Ereg regs4 gp3_extra) Eb)
    by (rewrite HEb; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (Eb9 : ew Eb 9 = Z_to_bv 64 (lf_F cx)).
  { subst Eb. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs4 _ 9 9%bv eq_refl).
    rewrite (RR 9%bv ltac:(gp3_csd) ltac:(cbv; tauto)). exact R9. }
  clear HEb.
  paj_run_to_tok_x RUNTO HSb HJ2 SHOKb gp3_span AF_gn_c1.
  { apply awr_ok_x_nil. }
  pmkst HSb.
  gp3_meq HF Em2.
  pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs4 gp3_extra gp3_kept2 HSb HAEb
    ltac:(vm_compute; reflexivity)) as KR2.
  prreg HSb (20%bv : bv 5) Q20.
  prreg HSb (21%bv : bv 5) Q21.
  prreg HSb (22%bv : bv 5) Q22.
  cbn [ms_regs restrict] in KR2.
  rewrite Em2 in *.
  (* the three registers the loop head reads *)
  assert (UF : bv_unsigned (Z_to_bv 64 (lf_F cx)) = lf_F cx).
  { apply unsigned_lit_small. clear - HFlo HFr Hspr AC C1. unfold LLVMF_STK in *. lia. }
  assert (R20' : getr (ms_regs ms0) 20 = w64 (rg_s fr_RG + ASRC * Z.of_nat 0)).
  { apply bv_eq. rewrite Q20, (HEIb 260%nat ltac:(unfold A_TEXT, A_LIM; lia)). vm_compute. reflexivity. }
  assert (R21' : getr (ms_regs ms0) 21 = w64 (lf_F cx + 192 + 4 * Z.of_nat 0)).
  { rewrite Q21, Eb9, UF.
    replace (lf_F cx + 192 + 4 * Z.of_nat 0) with (lf_F cx + 192) by (cbn [Z.of_nat]; clear; lia). reflexivity. }
  assert (R22' : getr (ms_regs ms0) 22 = w64 (lf_F cx + 208)).
  { rewrite Q22, Eb9, UF. reflexivity. }
  (* the registers kept from the arm's entry *)
  assert (RF : forall r : bv 5, acallee_saved (bv_unsigned r) -> In r gp3_kept -> In r gp3_kept2 ->
      getr (ms_regs ms0) r = getr regs r)
    by (intros r H1 H2 H3; rewrite (KR2 r H3); exact (RR r H1 H2)).
  apply SRr_ret.
  exists m1, (ms_regs ms0), mem4, (with_vm_backing (m_vm_lazy md4) mat0 md4), ly4, S4, (kk + k4), fpos.
  split; [reflexivity|].
  split.
  { split; [|split; [exact HMOD1 | split; [exact HSEP1 | exact (proj1 (RPNP S4 _) HRM4)]]].
    split; [exact HJ2|]. split; [exact HFR1|]. split; [exact HFLAG'|]. split; [exact H16'|].
    split; [exact H144'|]. split; [exact H88'|].
    split; [exact HIN'|]. split; [exact HRV' | exact HJT']. }
  split; [exact HDONE|]. split; [exact HLS1|].
  split.
  { rewrite HFFeq. unfold gn_kregs.
    do 7 (split; [match goal with |- getr _ ?r = _ =>
      rewrite (RF r ltac:(gp3_csd) ltac:(cbv; tauto) ltac:(cbv; tauto)); assumption end|]).
    match goal with |- getr _ ?r = _ =>
      rewrite (RF r ltac:(gp3_csd) ltac:(cbv; tauto) ltac:(cbv; tauto)); assumption end. }
  split; [exact SV24'|].
  split; [exact R20'|]. split; [exact R21'|]. split; [exact R22'|].
  split; [clear; lia|].
  split; [exact HREADS'|]. split; [exact HAWR'|]. split; [exact HAT'|].
  rewrite HFFeq. exact HPFX'.
Qed.
(* @@ END gp3 *)
(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): the R twins of this phase over the R cut points of
   W_LLVMFuzzerTestOneInput_gone_base_x.v (Section gR), as SRrG walks with the G runs.  Strict text above
   unchanged. ---- *)
Section gp3R.
Variable R : world segs -> world segs -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', wle W W' -> R W W'.
(* relay_instance_gone at R: lib/B/W_contract_xR_relayB.v rig_spec_xR *)
Hypothesis RIG_R : W_contract_xR_relayB.rig_spec_xR (PI := PB_fr) B PST ARx R MT RP MMAX fr_RG YCk0.CTX_AFREE
  (BASE + AF_fr_relay_instance_gone).
Local Notation AJ0R G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k :=
  (ajournal_gx_xR segs B PST ARx R G XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k).
Local Notation AJi0R STK sp0 FP ly S W mem md own ly' S' W' mem' md' k :=
  (ajournal_xR segs B PST ARx R STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k).

Ltac hp0gR HJ := let H := fresh "HARg" in
  pose proof (ajournal_gx_AR_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as H; hp0a H; clear H.

Lemma gp3_inner_xR : forall (G : list (Z * Z)) STK sp0 FP ly S (W : world segs) mem md own
    ly' S' (W' : world segs) mem' md' k,
  AJ0R G 0 [] STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
  exists memS, AJi0R STK sp0 FP ly S W memS md own ly' S' W' mem' md' k /\
    (forall a, 0 <= a < 2 ^ 64 -> ~ inG G a -> aview segs (w_H W) memS a = aview segs (w_H W) mem a).
Proof.
  intros G STK sp0 FP ly S W mem md own ly' S' W' mem' md' k HJ.
  destruct (ajournal_gx_inner_xR segs B PST ARx G 0 [] STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k HJ)
    as (memS & HJi & Hag).
  rewrite !Z.add_0_r in HJi. exists memS. split; [exact HJi|].
  intros a Ha HnG. apply Hag. rewrite unsigned_lit_small by lia. exact HnG.
Qed.

Lemma gp3_keeps_xR : forall (G : list (Z * Z)) STK sp0 FP ly S (W : world segs) mem md own
    ly' S' (W' : world segs) mem' md' k,
  AJ0R G 0 [] STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ inG G a -> alloc_ceiling <= a -> ~ (sp0 - STK <= a < sp0) ->
     aview segs (w_H W') mem' a = aview segs (w_H W) mem a) /\
  (forall p n i, In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B ly' S') -> 0 <= i < req_size n ->
     ~ inFP FP (p + i) -> 0 <= p + i < 2 ^ 64 -> ~ inG G (p + i) ->
     aview segs (w_H W') mem' (p + i) = aview segs (w_H W) mem (p + i)) /\
  (forall cid pos a, In (cid, pos) (frames S) ->
     (in_zr a (frame_rng ly (cid, pos)) \/
      in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8)) ->
     ~ inFP FP a -> 0 <= a < 2 ^ 64 -> ~ inG G a ->
     aview segs (w_H W') mem' a = aview segs (w_H W) mem a) /\
  (forall a, in_img segs a -> ~ Exists (in_zr a) (as_owned_static B) ->
     ~ (as_errno B <= a < as_errno B + 4) -> fp_spares FP a -> 0 <= a < 2 ^ 64 -> ~ inG G a ->
     aview segs (w_H W') mem' a = aview segs (w_H W) mem a) /\
  (forall a, sp0 - STK <= a < sp0 -> apresent (w_H W') mem' a) /\
  AR0 ly' S' W' mem' md' /\ frames S' = own ++ frames S /\
  layout_le (length (st_secs S)) ly ly' /\ R W W'.
Proof.
  intros G STK sp0 FP ly S W mem md own ly' S' W' mem' md' k HJ.
  destruct (gp3_inner_xR G STK sp0 FP ly S W mem md own ly' S' W' mem' md' k HJ) as (memS & HJi & Hag).
  pose proof HJi as (HAR' & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & C8 & C9 & C11 & C10 & C12 &
    C13 & Hstk & Cextra & HQT).
  split; [intros a Ha HnG Hc Hout; rewrite (C8 a ltac:(lia) ltac:(lia)); exact (Hag a Ha HnG)|].
  split.
  { intros p n i Hin Hin' Hi Hnf Hrng HnG.
    rewrite (C9 p n i Hin Hin' Hi Hnf). exact (Hag (p + i) Hrng HnG). }
  split.
  { intros cid pos a Hf Hr Hnf Ha HnG.
    rewrite (C10 cid pos a Hf Hr Hnf). exact (Hag a Ha HnG). }
  split.
  { intros a Himg Hown Herr Hsp Ha HnG.
    rewrite (C11 a Himg Hown Herr (HPST a Himg) Hsp). exact (Hag a Ha HnG). }
  split; [exact C13|].
  split; [exact HAR'|]. split; [exact Hfrs|]. split; [exact Hly | exact Hwle].
Qed.

Lemma gp3_afn_pre_xR : forall cx ly3 S3 fpos k (W : world segs) mem md regs STK1,
  LFB0 cx ->
  AJ0R G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem md k ->
  (forall o r, In (o, r) saved_regs -> sv8 W mem (spZ (c_regs cx) - o) (bv_unsigned (getr (c_regs cx) (Z_to_bv 5 r)))) ->
  spZ regs = lf_F cx -> YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) -> getr regs 8 = getr (c_regs cx) 2 ->
  0 <= STK1 -> STK1 + 352 <= LLVMF_STK ->
  exists ch, AFN0 STK1 ly3 S3 W regs mem md ch /\ (spine ch = [] \/ spine ch = [YCfn.RA_LLVMF]) /\
    spZ regs + 16 < ly_top ly3.
Proof.
  intros cx ly3 S3 fpos k W mem md regs STK1 HB HJ HSV Hsp Hret Hra4 Hgp Htp Hs0 HSTK0 HSTKb.
  destruct HB as (_ & HPRE).
  assert (HRA : raZ (c_regs cx) = YCfn.RA_LLVMF) by (unfold fr_lib_pre_cf_x in HPRE; tauto).
  assert (HPREE : AFN0 LLVMF_STK (c_ly cx) (c_S cx) (c_W cx) (c_regs cx) (c_mem cx) (c_md cx) [])
    by (unfold fr_lib_pre_cf_x in HPRE; tauto).
  pose proof HPREE as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0).
  pose proof Hstk0 as (Hal16 & Hslo0 & Hceil0 & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  destruct (ajournal_gx_inner_xR segs B PST ARx G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 [] W mem md k HJ) as (memS & HJ0 & Hmg).
  rewrite !Z.add_0_r in HJ0.
  set (sp0 := spZ (c_regs cx)) in *.
  assert (HF32 : lf_F cx = sp0 - 320 - (sp0 - 320) mod 32) by reflexivity.
  pose proof (Z.mod_pos_bound (sp0 - 320) 32 ltac:(lia)) as Hmb.
  assert (Ho16 : (lf_F cx - sp0) mod 16 = 0).
  { rewrite HF32.
    replace (sp0 - 320 - (sp0 - 320) mod 32 - sp0) with (- (320 + (sp0 - 320) mod 32)) by lia.
    assert (H32 : (sp0 - 320) mod 32 = 0 \/ (sp0 - 320) mod 32 = 16).
    { assert (E16 : (sp0 - 320) mod 16 = 0)
        by (replace (sp0 - 320) with (sp0 + (-20) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16).
      pose proof (Z.div_mod ((sp0 - 320) mod 32) 16 ltac:(lia)) as D.
      assert (E2 : ((sp0 - 320) mod 32) mod 16 = 0)
        by (rewrite <- Znumtheory.Zmod_div_mod by (try lia; exists 2; reflexivity); exact E16).
      rewrite E2, Z.add_0_r in D.
      assert (Hq : (sp0 - 320) mod 32 / 16 = 0 \/ (sp0 - 320) mod 32 / 16 = 1) by lia.
      destruct Hq as [Hq | Hq]; rewrite Hq in D; lia. }
    destruct H32 as [H32 | H32]; rewrite H32; reflexivity. }
  assert (HoNeg : lf_F cx - sp0 <= 0) by (rewrite HF32; lia).
  assert (HoBud : STK1 - (lf_F cx - sp0) <= LLVMF_STK) by (rewrite HF32; lia).
  assert (HTOPeq : ly_top ly3 = ly_top (c_ly cx)).
  { pose proof HJ0 as (_ & Hly & _). pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _). exact Etop. }
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (Hs0Z : s0Z regs = sp0) by (unfold s0Z, sp0, spZ; rewrite Hs0; reflexivity).
  destruct (Z_lt_le_dec sp0 (ly_top (c_ly cx) - 16)) as [Hlt | Hge].
  - pose proof (aview_above_of_journal_xR (PI := PB_fr) B PST ARx LLVMF_STK sp0 (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) [] (c_W cx) memS (c_md cx) [(1, fpos)] ly3 S3 [] W mem md k HJ0) as HAB.
    assert (Hra8 : rdword (aview segs (w_H W) mem) (sp0 - 8) = Some (bv_unsigned (getr (c_regs cx) 1))).
    { apply (rdword_of_val_mem segs (w_H W) mem); [exact (HSV 8 1 ltac:(left; reflexivity)) |].
      pose proof (bv_unsigned_in_range 64 (getr (c_regs cx) 1)) as Hr.
      change (bv_modulus 64) with (2 ^ 64) in Hr. lia. }
    assert (Hs016 : rdword (aview segs (w_H W) mem) (sp0 - 16) = Some (bv_unsigned (getr (c_regs cx) 8))).
    { apply (rdword_of_val_mem segs (w_H W) mem); [exact (HSV 16 8 ltac:(right; left; reflexivity)) |].
      pose proof (bv_unsigned_in_range 64 (getr (c_regs cx) 8)) as Hr.
      change (bv_modulus 64) with (2 ^ 64) in Hr. lia. }
    exists ((sp0, bv_unsigned (getr (c_regs cx) 1), bv_unsigned (getr (c_regs cx) 8)) :: []).
    split; [| split; [right; cbn [spine map fst snd]; unfold raZ in HRA; rewrite HRA; reflexivity
                     | rewrite Hsp, HTOPeq, HF32; lia]].
    eapply (afn_pre_x_atR segs B PST ARx LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) [] (c_W cx) memS (c_md cx)
      [(1, fpos)] ly3 S3 [] W mem md k regs STK1 (lf_F cx - sp0) _ HJ0);
      [ rewrite Hsp; lia | exact Ho16 | exact HoNeg | exact HSTK0 | exact HoBud | exact Hret | exact Hra4
      | exact Hgp | exact Htp | ].
    rewrite Hsp, Hs0Z.
    apply (achain_ly_top (c_ly cx) ly3 _ _ _ _ ltac:(exact HTOPeq)).
    eapply (achain_push (c_ly cx) (aview segs (w_H (c_W cx)) (c_mem cx)) (aview segs (w_H W) mem)
      sp0 (bv_unsigned (getr (c_regs cx) 8)) (bv_unsigned (getr (c_regs cx) 1)) [] (lf_F cx));
      [ exact Hch0 | lia
      | intros a Ha; rewrite (HAB a ltac:(lia)); apply Hmg; rewrite unsigned_lit_small by lia; intros HGa;
        pose proof (pa_segs_low a (proj1 (HG a HGa))); lia
      | exact Hra8 | exact Hs016
      | unfold raZ in Hra40; lia | lia | lia | lia | rewrite HF32; lia ].
  - exists []. split; [| split; [left; reflexivity | rewrite Hsp, HTOPeq, HF32; lia]].
    eapply (afn_pre_x_atR segs B PST ARx LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) [] (c_W cx) memS (c_md cx)
      [(1, fpos)] ly3 S3 [] W mem md k regs STK1 (lf_F cx - sp0) _ HJ0);
      [ rewrite Hsp; lia | exact Ho16 | exact HoNeg | exact HSTK0 | exact HoBud | exact Hret | exact Hra4
      | exact Hgp | exact Htp | ].
    rewrite Hs0Z. left. split; [right; left; rewrite HTOPeq; exact Hge | reflexivity].
Qed.

Lemma gp3_rig_c1_xR : forall cx t m W c,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx [] ->
  GRG_xR B NP G_fr fr_FP PST ARx LSx RINV R cx t m W c ->
  YA0nH.SRrG segs R W c (fun W' c' => exists m1, GC1_xR B MT NP G_fr fr_FP PST ARx LSx RINV R cx t m m1 0%nat W' c').
Proof.
  intros cx t m W c HB HRG.
  destruct HRG as (regs & mem0 & md & ly3 & S3 & kk & fpos & -> &
    ((HJ0 & HFR0 & HFLAG0 & H16_0 & H144_0 & H88_0 & HIN0 & HRV0 & HJT0) & HMOD0 & HSEP & HNP) & HLS & HRI & HOP &
    HKR & R26 & R21 & HREADS0 & HAWR0 & HAT0 & HPFX0).
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (gn_nums_xR B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS R cx [(1, fpos)] ly3 S3
    W mem0 md kk fpos HB HJ0 eq_refl) as NUMS.
  cbv zeta in NUMS.
  destruct NUMS as (Hsp16 & Hspr & HFm32 & HFr & HFF0 & HFF1 & HFFapp & Hfrs & HAR0).
  destruct HKR as (R2 & R8 & R9 & R18 & R19 & R27 & R3 & R4).
  pose proof YM05.alloc_ceiling_value as AC.
  assert (HlenP : Z.of_nat (length (c_pl cx)) = c_n cx)
    by (destruct HB as (_ & HPRE0); unfold fr_lib_pre_cf_x in HPRE0; symmetry; tauto).
  destruct ERRNO_LOW as (HE0 & HE1).
  assert (HFlo : alloc_ceiling + 8 <= lf_F cx) by (unfold LLVMF_STK in *; lia).
  (* ---- 0x84b40-0x84b48: sd s10,24(s1); mv a0,s5; jal relay_instance_gone ---- *)
  assert (HFw32 : awr W mem0 (lf_F cx) 32).
  { intros i Hi. pose proof HFR0 as (_ & HFW0 & _). apply HFW0. lia. }
  destruct (gp3_entry W regs mem0 (lf_F cx) R9 ltac:(unfold LLVMF_STK in *; lia) ltac:(lia) HFm32 HFw32)
    as [HS SHOK].
  remember (Eimg (Ereg regs gp3_extra)) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs gp3_extra) E)
    by (rewrite HE; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (E21 : ew E 21 = Z_to_bv 64 (gn_id cx m)).
  { subst E. rewrite Eimg_low by (unfold A_TEXT; lia).
    rewrite (ew_Ereg_nat regs _ 21 21%bv eq_refl). exact R21. }
  assert (E26 : ew E 26 = Z_to_bv 64 HI_G_NOUT).
  { subst E. rewrite Eimg_low by (unfold A_TEXT; lia).
    rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl). exact R26. }
  assert (U9 : bv_unsigned (ew E 9) = lf_F cx).
  { subst E. rewrite Eimg_low by (unfold A_TEXT; lia).
    rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl), R9. apply unsigned_lit_small. unfold LLVMF_STK in *. lia. }
  clear HE.
  unfold cfg_at. change (w64 (fr_B0 + AF_gn_rig)) with (Z_to_bv 64 (BASE + AF_gn_rig)).
  pose (RUNTOG := paj_run_to_x_xG (PL := PL_fr) (PI := PB_fr) B PST ARx LAWS R G_fr HG 0 []).
  paj_run_to_tok_xR RUNTOG HS HJ0 SHOK gp3_span AF_fr_relay_instance_gone.
  { gp3_awr U9. }
  lazymatch goal with Hg : mem_grows _ _ |- _ => rename Hg into HGr end.
  lazymatch goal with Hf : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ => rename Hf into HFRr end.
  (* the run's one store: F+24 := HI_G_NOUT; every other byte kept, every writable byte still writable *)
  assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + 24 <= a < lf_F cx + 32) ->
      aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem0 a)
    by (intros a Ha Hna; apply (aview_kept_out _ _ _ _ _ HFRr a Ha); gp3_nowr U9).
  assert (WK : forall a, writable_at segs (arm W mem0) a -> writable_at segs (arm W (ms_mem ms)) a).
  { intros a Hw. apply (writable_kept (w_H W) mem0 (ms_mem ms) a); [|exact Hw].
    intros Hp. exact (apresent_grows _ _ _ _ HGr Hp). }
  assert (KEEP0 : forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + 24 <= a < lf_F cx + 32) ->
      abyte_kept W mem0 W (ms_mem ms) a)
    by (intros a Ha Hna; split; [exact (K1 a Ha Hna) | apply WK]).
  assert (KLO : forall a, 0 <= a < GK_CEIL8 -> abyte_kept W mem0 W (ms_mem ms) a)
    by (intros a Ha; apply KEEP0; unfold GK_CEIL8 in *; lia).
  pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG0. cbn [ms_mem restrict] in RG0.
  assert (SV24 : sv8 W (ms_mem ms) (lf_F cx + 24) HI_G_NOUT).
  { unfold sv8.
    lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
      apply (field_of_region Ev _ 9%nat (lf_F cx) _ _ _ _ _ 24 8%N (SOff 26 0) HI_G_NOUT RG0) end.
    - exact U9.
    - left. reflexivity.
    - cbn [sv_denot]. rewrite E26, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    - unfold HI_G_NOUT. zside.
    - zside. }
  pmkst HS.
  pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs gp3_extra gp3_kept HS HAE
    ltac:(vm_compute; reflexivity)) as KR.
  prreg HS (1%bv : bv 5) Q1.
  prreg HS (10%bv : bv 5) Q10.
  cbn [ms_regs restrict] in KR.
  set (mem := ms_mem ms) in *.
  set (mdc := with_vm_backing (m_vm_lazy md) mat md) in *.
  rename HJ0 into HJ.
  pose proof (gn_nums_xR B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr fr_FP PST ARx LAWS R cx [(1, fpos)] ly3 S3 W mem mdc kk
    fpos HB HJ eq_refl) as NUMS2.
  cbv zeta in NUMS2. destruct NUMS2 as (_ & _ & _ & _ & _ & _ & _ & _ & HAR).
  (* ---- the cut point's facts at the call's entry ---- *)
  assert (HFR : gframe cx fake_shadow_open (frame_addr ly3 1 fpos) W mem).
  { apply (gp3_gframe_st cx _ _ W mem0 mem HFR0 eq_refl); [lia | | | | exact WK].
    - intros a Ha. apply KEEP0; lia.
    - intros a Ha. apply KLO. unfold GK_CEIL8. lia.
    - intros a Ha. apply KLO. unfold GK_CEIL8, SB in *. lia. }
  assert (HFLAG : sv8 W mem (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos))
    by (apply (gk_sv8_kept W W mem0 mem); [intros x Hx; apply KLO; unfold GK_CEIL8; lia | exact HFLAG0]).
  assert (H16 : sv8 W mem (lf_F cx + 16) (c_p cx + gn_kq cx m))
    by (apply (gk_sv8_kept W W mem0 mem); [intros x Hx; apply KEEP0; lia | exact H16_0]).
  assert (H144 : sv8 W mem (lf_F cx + 144) (c_n cx - gn_kq cx m))
    by (apply (gk_sv8_kept W W mem0 mem); [intros x Hx; apply KEEP0; lia | exact H144_0]).
  assert (H88 : sv8 W mem (lf_F cx + 88) t)
    by (apply (gk_sv8_kept W W mem0 mem); [intros x Hx; apply KEEP0; lia | exact H88_0]).
  pose proof (gk_ainput_kept_x B ARx LAWS BLKN cx ly3 S3 W mem0 md W mem HAR0 HIN0 HlenP KLO) as HIN.
  pose proof (gk_rom_kept W W mem0 mem HRV0 KLO) as HRV.
  pose proof (gk_jt_kept W W mem0 mem HJT0 KLO) as HJT.
  pose proof (gk_amodel_kept_x B ARx LAWS BLKN ly3 S3 W mem0 md W mem m HAR0 HMOD0 HE0 ltac:(unfold GK_CEIL8; lia) KLO)
    as HMOD.
  assert (HREADS : forall j, (j < 4)%nat -> gn_sv4 W mem (lf_F cx + 192 + 4 * Z.of_nat j) (gn_reads m j)).
  { intros j Hj. unfold gn_sv4. apply (akept_vm W mem0); [|exact (HREADS0 j Hj)].
    intros x Hx. apply KEEP0; cbn in Hx; lia. }
  assert (HAWR : awr W mem (lf_F cx + 192) 16)
    by (apply (akept_awr W mem0); [intros x Hx; apply KEEP0; lia | exact HAWR0]).
  assert (HAT : sv8 W mem (lf_F cx + 208) 0)
    by (apply (gk_sv8_kept W W mem0 mem); [intros x Hx; apply KEEP0; lia | exact HAT0]).
  assert (HPFX : gn_prefix_at cx m W mem (frame_addr ly3 1 fpos)).
  { destruct HPFX0 as (P1 & P2 & P3 & P4 & P5).
    split; [intros i Hi; rewrite (proj1 (KLO (frame_addr ly3 1 fpos + 32 + i) ltac:(unfold GK_CEIL8; lia)));
            exact (P1 i Hi)|].
    split; [rewrite (proj1 (KLO (frame_addr ly3 1 fpos + 32 + Z.of_nat (length (gn_pre cx m)))
              ltac:(unfold GK_CEIL8; lia))); exact P2|].
    split; [intros a Ha; rewrite (proj1 (KLO a ltac:(unfold GK_CEIL8; lia))); exact (P3 a Ha)|].
    split; [exact P4 | exact P5]. }
  clear K1 KEEP0 KLO WK RG0 HFRr HGr.
  (* LS_cnt's msz_ok guard and gdone's msz_ok conjunct, from the model at GRG *)
  pose proof (gn_msz_ok B ly3 S3 W mem m HMOD) as HMSZ.
  pose proof HMOD as (HM4 & HSLOT & HREL & HOUT & HGONE & HLOCK & HWAKE & HNFD & HNFDW & HNFDR & HTU &
    HLST & HLSTW).
  destruct (HPAIRS cx t m HRI) as (hs & HPOK).
  pose proof HPOK as (HLENhs & HFORALL & HNODUP).
  pose proof (proj1 (NoDup_ListNoDup _) HNODUP) as HNDl.
  assert (HPOKi : forall i, (i < length (lm_es m))%nat -> re_eof (nth i (lm_es m) gn_e0) = 0 ->
      gn_pair_ok m (nth i (lm_es m) gn_e0) (nth i hs gn_hj0)).
  { intros i Hi Heof.
    assert (Hini : In (nth i (combine (lm_es m) hs) (gn_e0, gn_hj0)) (combine (lm_es m) hs)).
    { apply nth_In. rewrite length_combine. lia. }
    pose proof (proj1 (Forall_forall _ _) HFORALL _ Hini) as POK.
    rewrite (combine_nth (lm_es m) hs i gn_e0 gn_hj0 ltac:(lia)) in POK.
    cbn [fst snd] in POK. exact (POK Heof). }
  assert (HJS4 : forall j, In j (rig_slots (combine (lm_es m) hs)) -> (j < 4)%nat).
  { intros j Hj. apply in_concat in Hj as (l & Hl & Hjl).
    apply in_map_iff in Hl as (p & <- & Hp).
    destruct (Z.eqb_spec (re_eof (fst p)) 0) as [Heq|Hne]; [|destruct Hjl].
    destruct Hjl as [<- | []].
    exact (proj1 (proj1 (Forall_forall _ _) HFORALL p Hp Heq)). }
  pose proof (gp3_perm_slots (lm_hs m) (rig_slots (combine (lm_es m) hs)) HM4 HNDl HJS4) as HPS.
  assert (HSRCS : concat (map (fun j => slot_blks (nth j (lm_hs m) None))
      (rig_slots (combine (lm_es m) hs))) = rig_srcs (combine (lm_es m) hs)).
  { apply (gp3_srcs_of_slots _ (lm_es m) hs HLENhs).
    intros i Hi Heof. destruct (HPOKi i Hi Heof) as (_ & Hnth & _).
    rewrite Hnth. reflexivity. }
  rewrite HSRCS in HPS.
  destruct HSEP as ((rest0 & HPERM0) & HSEPFP).
  set (OTH := concat (map (fun j => slot_blks (nth j (lm_hs m) None))
    (gp3_cs (rig_slots (combine (lm_es m) hs))))) in *.
  assert (HPERM1 : Permutation (ablocks B ly3 S3)
    ((lm_G m, ATABLE) :: concat (map aentry_blks (lm_es m)) ++ rig_srcs (combine (lm_es m) hs) ++
     aout_blks (lm_cap m) (lm_out m) ++ (OTH ++ input_blks cx ++ rest0))).
  { eapply Permutation_trans; [exact HPERM0|]. unfold model_blks.
    eapply Permutation_trans;
      [exact (gp3_perm_cong (input_blks cx) (concat (map aentry_blks (lm_es m)))
         (aout_blks (lm_cap m) (lm_out m)) rest0 _ _ (lm_G m, ATABLE) HPS)|].
    apply gp3_perm_pre. }
  assert (Hsp1 : spZ (ms_regs ms) = lf_F cx).
  { unfold spZ. rewrite (KR 2%bv ltac:(cbv; tauto)), R2. unfold w64. apply unsigned_lit_small.
    unfold LLVMF_STK in *. lia. }
  destruct (gp3_afn_pre_xR cx ly3 S3 fpos kk W mem mdc (ms_regs ms) RIG_STK_x HB HJ (proj1 HFR) Hsp1
    ltac:(rewrite Q1; apply ret_ok_codeptr_v; [lia | reflexivity])
    ltac:(unfold raZ; rewrite Q1, unsigned_lit_small by lia; lia)
    ltac:(rewrite (KR 3%bv ltac:(cbv; tauto)); exact R3)
    ltac:(rewrite (KR 4%bv ltac:(cbv; tauto)); exact R4)
    ltac:(rewrite (KR 8%bv ltac:(cbv; tauto)); exact R8)
    ltac:(unfold RIG_STK_x, RIG_STK, RIG_FRAME, DRAIN_STK, DRAIN_FRAME, SL_STK, SL_FRAME, ASTACK; lia)
    ltac:(unfold RIG_STK_x, RIG_STK, RIG_FRAME, DRAIN_STK, DRAIN_FRAME, SL_STK, SL_FRAME, ASTACK, LLVMF_STK; lia))
    as (ch & HPREc & HSPINE & HTOP).
  (* _gone_p3.v:1108: GN_LS_rig's premises at GRG_x, all held: gn_op (HOP), aentry_ok's |re_U| <= APARTIAL, the model
     blocks' sizes not negative (the AR block law over HPERM0), the pending offsets (Hoff), and the CAPOUT clause;
     A f5d40188e29 *)
  pose proof HOP as (_ & HO0 & Ht0 & _).
  assert (HUs : Forall (fun e => Z.of_nat (length (re_U e)) <= APARTIAL) (lm_es m)).
  { pose proof HREL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & GdAE & _).
    rewrite Forall_forall in GdAE |- *. intros ge gHe.
    destruct (GdAE ge gHe) as (_ & _ & _ & _ & _ & _ & GdC7 & GdC8 & _). lia. }
  assert (HMpos : forall b, In b (model_blks m) -> 0 <= snd b).
  { intros [gp gn] gHb. assert (gHin : In (gp, gn) (ablocks B ly3 S3)).
    { apply (Permutation_in _ (Permutation_sym HPERM0)). apply in_or_app. right. apply in_or_app. left. exact gHb. }
    destruct (gk_blk_x B ARx LAWS BLKN ly3 S3 W mem mdc gp gn HAR gHin) as (_ & _ & GdN). cbn [snd]. lia. }
  assert (Hoff : forall k h, nth k (lm_hs m) None = Some h ->
      (hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
      (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))).
  { intros gk gh gHk.
    assert (gHl : (gk < 4)%nat).
    { destruct (Nat.lt_ge_cases gk (length (lm_hs m))) as [Hlt | Hge]; [lia|].
      rewrite nth_overflow in gHk by exact Hge. discriminate gHk. }
    pose proof (HSLOT gk gHl) as GdSl. unfold aslot in GdSl. rewrite gHk in GdSl.
    destruct GdSl as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & GdOFF & _). exact GdOFF. }
  (* GN_LS_rig's g_capout premise: the entry pre's CAPOUT clause (fr_lib_pre_cf_x, its last conjunct) *)
  assert (HCAPO : exists c, val_mem segs (arm (c_W cx) (c_mem cx)) (rg_capout fr_RG) 8 c /\ 0 <= c <= CAPOUT_MAX).
  { pose proof HB as (_ & GdPRE). unfold fr_lib_pre_cf_x in GdPRE.
    repeat match type of GdPRE with _ /\ _ => destruct GdPRE as (_ & GdPRE) end. exact GdPRE. }
  pose proof (HLSRIG cx t m ly3 S3 hs HLS HRI HPOK HOP HUs HMpos Hoff HCAPO) as BUD. cbv zeta in BUD.
  destruct BUD as (Btr1 & Btr2 & Btr3 & _).
  (* rig_spec_x at the ghost list [], taken at kr := 0 *)
  eassert (HCALL : YA0nH.SRrG segs R W (cfg_at segs (BASE + AF_fr_relay_instance_gone) (ms_regs ms) mem mdc) _).
  { apply (RIG_R W ly3 S3 [] (ms_regs ms) mem mdc ch (lm_G m) (gn_id cx m) (lm_es m) hs
      (lm_c m) (lm_O m) (lm_mx m) (lm_cap m) (lm_out m)) with (kr := 0%nat).
    - exact HPREc.
    - rewrite Hsp1. exact HFm32.
    - rewrite Hfrs. change (count_cid 1 [(1, fpos)]) with 1. change (fs_frames 1) with 8192. lia.
    - exact RGP.
    - rewrite Q10, E21. reflexivity.
    - exact (gp3_id_rng cx m).
    - exact HLOCK.
    - exact HREL.
    - exact HOUT.
    - exact HRV.
    - exact HLENhs.
    - apply Forall_forall. intros p Hp Heof.
      apply (In_nth _ _ (gn_e0, gn_hj0)) in Hp as (i & Hi & Hpi).
      rewrite length_combine in Hi. rewrite <- Hpi in Heof |- *.
      rewrite (combine_nth (lm_es m) hs i gn_e0 gn_hj0 ltac:(lia)) in Heof |- *.
      cbn [fst snd] in Heof |- *.
      destruct (HPOKi i ltac:(lia) Heof) as (Hj4 & Hnth & Hfd & Hskip & HU & Hps1 & Hps2 & Hps3).
      split; [exact Hj4|]. split.
      + pose proof (HSLOT (snd (nth i hs gn_hj0)) Hj4) as Hsl.
        unfold aslot in Hsl. rewrite Hnth in Hsl. exact Hsl.
      + split.
        * rewrite <- Hfd. exact (gp3_others cx t m ly3 S3 W mem _ (fst (nth i hs gn_hj0)) HRI HMOD Hj4 Hnth).
        * split; [exact Hfd|]. split; [exact Hskip|]. split; [exact HU|].
          split; [exact Hps1|]. split; [exact Hps2 | exact Hps3].
    - exact HNODUP.
    - exists (OTH ++ input_blks cx ++ rest0). exact HPERM1.
    - exact Btr1.
    - exact Btr2.
    - exact Btr3.
    - (* the room round: RM is NP at the instance (RPNP), and NP S3 is the arm's threaded invariant *)
      apply (proj2 (RPNP S3 _)). exact HNP.
    - (* the counts: LS_cnt gives them at the LS state, which IS this call's state, and GN_CNT_rig says rig's
         premise peak fits inside the arm's peak gn_pk *)
      pose proof HOP as (_ & _ & HtO & _).
      pose proof (LSCNT cx t m ly3 S3 hs HLS HRI HPOK HMSZ HtO HUs HMpos Hoff) as HC0.
      unfold cnt_ok_pk in HC0 |- *.
      pose proof (CNTRIG cx m hs (rp_Psec RP)) as Q1s. cbv beta in Q1s.
      pose proof (CNTRIG cx m hs (rp_P24 RP)) as Q2s. cbv beta in Q2s.
      split; [|split].
      + pose proof (proj1 HC0). lia.
      + pose proof (proj1 (proj2 HC0)). lia.
      + intros c Hc. pose proof (proj2 (proj2 HC0) c Hc).
        pose proof (CNTRIG cx m hs (rp_Pcls RP c)) as Q3s. cbv beta in Q3s. lia.
    - (* rig_spec_x's room above sp: from the entry's astk_ok through the journal's layout *)
      exact HTOP.
    - (* the free's caller context: K0's CTX_AFREE rows [0x82fb8; 0x84b4c(; 0x82240)]: relay_instance_gone's free
         returns to pc + 792 = 0x82fb8, relay_instance_gone to AF_gp3_ret = 0x84b4c, LLVMFuzzerTestOneInput to
         RA_LLVMF = 0x82240 when its record is on the chain *)
      destruct HSPINE as [Hsc | Hsc]; rewrite Hsc; unfold raZ; rewrite Q1, unsigned_lit_small by lia;
        vm_compute; repeat (first [left; reflexivity | right]). }
  eapply (YA0nH.SRrG_bind _ R R_trans); [exact HCALL|].
  intros W2 c2 Hwle2 HPOST.
  destruct HPOST as (ly4 & S4 & Hp4 & regs4 & mem4 & md4 & k4 & qs & c4 & O4 & cap4 & out4 & rest4 & -> &
    HJc & HPRES & HAPK & HMO & HRM4 & HLOCK4 & HRREL & HLENq & HREL4 & HOUT4 & HSRC4 & HKEEPS & HPERMa & HPERMb).
  (* the post's ghost list is [] (HP0 on its journal's ARx) *)
  hp0gR HJc.
  rewrite Hsp1 in HJc. clear HCALL.
  assert (DEC : forall u v : Z * Z, {u = v} + {u <> v}) by (decide equality; apply Z.eq_dec).
  (* ---- what relay_instance_gone's journal keeps ---- *)
  destruct (gp3_keeps_xR (G_RIG B fr_RG) RIG_STK_x (lf_F cx)
    (rig_fp (lm_G m) (lm_es m) hs (lm_cap m) (lm_out m)) ly3 S3 W mem mdc [] ly4 S4 W2 mem4 md4 k4 HJc)
    as (KHI & KBLKv & KFRMv & KIMGv & KPRESc & HAR4 & Hfrs4 & HLY & Hwle4).
  cbn [app] in Hfrs4.
  assert (HFFeq : frame_addr ly4 1 fpos = frame_addr ly3 1 fpos).
  { unfold frame_addr. destruct HLY as (_ & _ & _ & _ & _ & HFly & _). rewrite HFly. reflexivity. }
  assert (HFLeq : flag_addr ly4 1 fpos = flag_addr ly3 1 fpos).
  { unfold flag_addr. destruct HLY as (_ & _ & _ & _ & _ & HFly & _). rewrite HFly. reflexivity. }
  assert (Hin1 : In (1, fpos) (frames S3)) by (rewrite Hfrs; left; reflexivity).
  assert (Hin1' : In (1, fpos) (frames S4)) by (rewrite Hfrs4; exact Hin1).
  assert (HAsub : forall b, In b ((lm_G m, ATABLE) :: concat (map aentry_blks (lm_es m)) ++
      rig_srcs (combine (lm_es m) hs) ++ aout_blks (lm_cap m) (lm_out m)) -> In b (ablocks B ly3 S3)).
  { intros b Hb. apply (Permutation_in _ (Permutation_sym HPERMa)).
    rewrite <- gp3_assoc4. apply in_app_iff. left. exact Hb. }
  assert (HMODBLK : forall b, In b ((lm_G m, ATABLE) :: concat (map aentry_blks (lm_es m)) ++
      rig_srcs (combine (lm_es m) hs) ++ aout_blks (lm_cap m) (lm_out m)) -> In b (model_blks m)).
  { intros b [<- | Hb]; [left; reflexivity|]. unfold model_blks. right.
    apply in_app_iff in Hb as [Hb | Hb]; [apply in_app_iff; left; exact Hb|].
    apply in_app_iff. right. apply in_app_iff in Hb as [Hb | Hb].
    - apply in_app_iff. left. apply (Permutation_in _ (Permutation_sym HPS)). apply in_app_iff. left. exact Hb.
    - apply in_app_iff. right. exact Hb. }
  assert (HFPS : forall a, fp_spares (rig_fp (lm_G m) (lm_es m) hs (lm_cap m) (lm_out m)) a)
    by exact (gp3_fp_spares_x ly3 S3 W mem mdc _ HAR HAsub).
  assert (HAPART : forall b a, In b rest4 -> fst b <= a < fst b + req_size (snd b) ->
      ~ inFP (rig_fp (lm_G m) (lm_es m) hs (lm_cap m) (lm_out m)) a).
  { intros b a Hb Hr Hin. apply gp3_inFP_fp in Hin as (b' & Hb' & Hr').
    refine (gp3_apart_x ly3 S3 W mem mdc _ _ b' b a HAR _ Hb' Hb Hr' Hr).
    rewrite gp3_assoc4. exact HPERMa. }
  assert (HNGblk : forall b a, In b (ablocks B ly3 S3) -> fst b <= a < fst b + req_size (snd b) ->
      ~ inG (G_RIG B fr_RG) a).
  { intros [p n] a Hb Hr HinG. cbn [fst snd] in Hr.
    exact (blk_img_x _ _ _ LAWS ly3 S3 [] W mem mdc p n a HAR Hb Hr (proj1 (HG a (HGRIG a HinG)))). }
  (* ---- the callee's journal inside the arm's (W_journal_x.v ajournal_gx_sub_x) ---- *)
  assert (HFP1 : forall a, inFP (rig_fp (lm_G m) (lm_es m) hs (lm_cap m) (lm_out m)) a ->
      (inFP (lf_FP fr_FP cx) a /\ exists b n, In (b, n) (ablocks B ly3 S3) /\ b <= a < b + req_size n) \/
      in_tmp_block (ablocks B (c_ly cx) (c_S cx)) (ablocks B ly3 S3) a).
  { intros a Hin. apply gp3_inFP_fp in Hin as (b & Hb & Hr).
    destruct (gn_sep_req B fr_FP cx m ly3 S3 (conj (ex_intro _ rest0 HPERM0) HSEPFP) b (HMODBLK b Hb))
      as [Hnew | Hfp].
    - right. exists (fst b), (snd b). rewrite <- surjective_pairing.
      split; [exact (HAsub b Hb)|]. split; [exact Hnew | exact Hr].
    - left. split; [exact (Hfp a Hr)|].
      exists (fst b), (snd b). rewrite <- surjective_pairing. split; [exact (HAsub b Hb) | exact Hr]. }
  assert (HJcG : AJ0R G_fr 0 [] RIG_STK_x (lf_F cx)
      (rig_fp (lm_G m) (lm_es m) hs (lm_cap m) (lm_out m)) ly3 S3 W mem mdc [] ly4 S4 W2 mem4 md4 k4).
  { apply (ajournal_gx_G_mono_xR segs B PST ARx (G_RIG B fr_RG) G_fr); [exact HGRIG | exact HJc]. }
  pose proof (ajournal_gx_sub_xR segs B PST ARx LAWS pa_segs_low R_trans G_fr LLVMF_STK (spZ (c_regs cx)) 0 []
     (lf_FP fr_FP cx) (c_ly cx) (c_S cx) [] (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 [] W mem mdc kk
     RIG_STK_x (lf_F cx) 0 [] (rig_fp (lm_G m) (lm_es m) hs (lm_cap m) (lm_out m)) [] ly4 S4 [] W2 mem4 md4 k4
     HJ HJcG
     ltac:(unfold RIG_STK_x, RIG_STK, RIG_FRAME, DRAIN_STK, DRAIN_FRAME, SL_STK, SL_FRAME, ASTACK, LLVMF_STK in *; lia)
     ltac:(lia) ltac:(lia)
     ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha))
     HG HFP1) as HJ2.
  cbn [app] in HJ2.
  destruct (gp3_keeps_xR G_fr LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx) (c_ly cx) (c_S cx) (c_W cx)
    (c_mem cx) (c_md cx) [(1, fpos)] ly4 S4 W2 mem4 md4 (kk + k4) HJ2) as (_ & _ & _ & _ & KPRES2 & _).
  (* ---- the bytes the cut reads, kept across the call ---- *)
  assert (KSTKv : forall a, lf_F cx <= a < 2 ^ 64 ->
      aview segs (w_H W2) mem4 a = aview segs (w_H W) mem a).
  { intros a Ha. apply KHI; [lia | | lia | lia].
    intros HinG. pose proof (pa_img_range a (proj1 (HG a (HGRIG a HinG)))). lia. }
  assert (KSTK : forall a, lf_F cx <= a < spZ (c_regs cx) -> abyte_kept W mem W2 mem4 a).
  { intros a Ha. split; [apply KSTKv; lia|]. intros _.
    apply gp3_wr_pres. apply KPRES2. unfold LLVMF_STK in *. lia. }
  assert (KFRM : forall a, frame_addr ly3 1 fpos <= a < frame_addr ly3 1 fpos + 128 ->
      abyte_kept W mem W2 mem4 a).
  { intros a Ha.
    assert (HNF : ~ inFP (rig_fp (lm_G m) (lm_es m) hs (lm_cap m) (lm_out m)) a)
      by exact (gp3_not_fp_frame_x ly3 S3 W mem mdc _ 1 fpos a HAR HAsub Hin1
                  ltac:(change (fs_frame_bytes 1) with 128; lia)).
    split.
    - apply (KFRMv 1 fpos a Hin1);
        [left; unfold in_zr, frame_rng; cbn [fst snd]; change (fs_frame_bytes 1) with 128; lia
        | exact HNF | lia |].
      intros HinG. exact (frm_img_x _ _ _ LAWS ly3 S3 [] W mem mdc 1 fpos a HAR Hin1
        ltac:(change (fs_frame_bytes 1) with 128; lia) (proj1 (HG a (HGRIG a HinG)))).
    - intros _. apply gp3_wr_pres.
      destruct (alx_frames _ _ _ LAWS ly4 S4 [] W2 mem4 md4 1 fpos HAR4 Hin1') as (_ & _ & Hb & _).
      rewrite HFFeq in Hb. exact (proj1 (Hb a ltac:(change (fs_frame_bytes 1) with 128; lia))). }
  assert (KSH : forall a, SB + frame_addr ly3 1 fpos / 8 <= a < SB + frame_addr ly3 1 fpos / 8 + 16 ->
      abyte_kept W mem W2 mem4 a).
  { intros a Ha.
    assert (Hsh : in_zr a (shadow_addr (frame_addr ly3 1 fpos), fs_frame_bytes 1 / 8)).
    { unfold in_zr, shadow_addr. cbn [fst snd]. change (fs_frame_bytes 1 / 8) with 16.
      rewrite <- SB_SHADOW_OFF. lia. }
    assert (HNF : ~ inFP (rig_fp (lm_G m) (lm_es m) hs (lm_cap m) (lm_out m)) a).
    { apply (gp3_not_fp_shadow_x ly3 S3 W mem mdc _ a HAR HAsub).
      unfold SB, kLowShadowBeg, kHighMemBeg in *. lia. }
    split.
    - apply (KFRMv 1 fpos a Hin1); [right; exact Hsh | exact HNF | unfold SB in *; lia |].
      intros HinG. pose proof (pa_img_range a (proj1 (HG a (HGRIG a HinG)))). unfold SB in *. lia.
    - intros _. apply gp3_wr_pres.
      destruct (alx_frames _ _ _ LAWS ly4 S4 [] W2 mem4 md4 1 fpos HAR4 Hin1') as (_ & _ & _ & Hsh4).
      rewrite HFFeq in Hsh4.
      assert (Hi : 0 <= a - shadow_addr (frame_addr ly3 1 fpos) < fs_frame_bytes 1 / 8)
        by (unfold in_zr in Hsh; cbn [fst snd] in Hsh; lia).
      specialize (Hsh4 _ Hi).
      replace (shadow_addr (frame_addr ly3 1 fpos) + (a - shadow_addr (frame_addr ly3 1 fpos))) with a
        in Hsh4 by lia.
      exact (proj1 Hsh4). }
  pose proof RGP as (_ & _ & _ & _ & _ & _ & RGP7 & _).
  assert (KIMG : forall a, inG gn_cells a -> ~ inG (G_RIG B fr_RG) a ->
      ~ (as_errno B <= a < as_errno B + 4) -> abyte_kept W mem W2 mem4 a).
  { intros a Hc HnR Herr. pose proof (HGCELLS a Hc) as Hfr. destruct (HG a Hfr) as (Himg & Hown & _).
    split; [|intros _; exact (GWR _ _ a Hfr)].
    apply KIMGv; [exact Himg | exact Hown | exact Herr | apply HFPS | | exact HnR].
    pose proof (pa_img_range a Himg). lia. }
  assert (KG4 : forall a, gp3_g4 a -> abyte_kept W mem W2 mem4 a).
  { intros a H4. pose proof (gp3_errno_g4 a H4) as Herr.
    exact (KIMG a (gp3_g4_cells a H4) (gp3_not_RIG a Herr (or_introl H4)) Herr). }
  assert (KWAKE : forall a, rg_wake fr_RG + 4 <= a < rg_wake fr_RG + 8 -> abyte_kept W mem W2 mem4 a).
  { intros a Ha. pose proof (RGP7 a ltac:(unfold rg_rng; right; right; right; left; exact Ha)) as (_ & _ & Herr).
    exact (KIMG a (gp3_wake_cell a Ha) (gp3_not_RIG a Herr (or_intror Ha)) Herr). }
  assert (Hrest : Permutation rest4 (OTH ++ input_blks cx ++ rest0)).
  { apply (Permutation_app_inv_l ((lm_G m, ATABLE) :: concat (map aentry_blks (lm_es m)) ++
      rig_srcs (combine (lm_es m) hs) ++ aout_blks (lm_cap m) (lm_out m))).
    rewrite !gp3_assoc4. exact (Permutation_trans (Permutation_sym HPERMa) HPERM1). }
  assert (Hrest4 : forall b, In b rest4 -> In b (ablocks B ly4 S4)).
  { intros b Hb. apply (Permutation_in _ (Permutation_sym HPERMb)).
    right. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. right. exact Hb. }
  assert (KBLK : forall b a, In b rest4 -> In b (ablocks B ly3 S3) ->
      fst b <= a < fst b + req_size (snd b) -> abyte_kept W mem W2 mem4 a).
  { intros b a Hb Hb3 Hr. pose proof (Hrest4 b Hb) as Hb4.
    pose proof (HAPART b a Hb Hr) as HNF. pose proof (HNGblk b a Hb3 Hr) as HNR.
    destruct b as [p n]. cbn [fst snd] in Hr.
    destruct (gk_blk_x B ARx LAWS BLKN ly3 S3 W mem mdc p n HAR Hb3) as (P1 & P2 & P3).
    split.
    - replace a with (p + (a - p)) by lia.
      apply (KBLKv p n (a - p) Hb3 Hb4); [lia | | lia |];
        replace (p + (a - p)) with a by lia; assumption.
    - intros _. apply gp3_wr_pres.
      exact (proj1 (proj1 (proj2 (proj2 (proj2 (proj2
        (al0_blocks B ARx LAWS BLKN ly4 S4 W2 mem4 md4 p n HAR4 Hb4))))) a Hr)). }
  (* ---- the model after the call ---- *)
  set (js := rig_slots (combine (lm_es m) hs)) in *.
  set (hs1 := map (gp3_pick (lm_es m) hs qs (lm_hs m)) (seq 0 4)).
  set (m1 := LM (gn_kq cx m) hs1 (lm_G m) (map fst qs) c4 O4 (lm_mx m) cap4 out4 (lm_gn m) (lm_nfd m)).
  assert (Hhs1 : forall j, (j < 4)%nat -> nth j hs1 None = gp3_pick (lm_es m) hs qs (lm_hs m) j)
    by (intros j Hj; exact (gp3_nth_map4 _ None j Hj)).
  assert (Hlen1 : length hs1 = 4%nat) by (unfold hs1; rewrite length_map, length_seq; reflexivity).
  assert (HAFTER : gn_after_rig cx m hs qs c4 O4 cap4 out4 m1).
  { unfold gn_after_rig, m1. cbn [lm_k lm_G lm_es lm_c lm_O lm_mx lm_cap lm_out lm_gn lm_nfd lm_hs].
    do 10 (split; [reflexivity|]). split; [exact Hlen1|]. split.
    - intros j Hj Hnin. rewrite (Hhs1 j Hj). exact (gp3_pick_none _ _ _ _ j HLENhs Hnin).
    - intros i Hi Heof. pose proof (proj1 (HPOKi i Hi Heof)) as Hj4.
      rewrite (Hhs1 _ Hj4). exact (gp3_pick_some _ _ _ _ i Hi HLENhs HNDl Heof). }
  assert (HMOD1 : amodel_at B ly4 S4 W2 mem4 m1).
  { unfold amodel_at, m1. cbn [lm_hs lm_G lm_es lm_c lm_O lm_mx lm_cap lm_out lm_gn lm_nfd].
    split; [exact Hlen1|].
    split.
    { intros i Hi. rewrite (Hhs1 i Hi).
      destruct (in_dec Nat.eq_dec i js) as [Hdr | Hnd].
      - destruct (gp3_in_slots_find (lm_es m) hs i HLENhs Hdr) as (i0 & Hi0 & Heof0 & Hsl0).
        subst i. rewrite (gp3_pick_some (lm_es m) hs qs (lm_hs m) i0 Hi0 HLENhs HNDl Heof0).
        exact (HSRC4 i0 Hi0 Heof0).
      - rewrite (gp3_pick_none (lm_es m) hs qs (lm_hs m) i HLENhs Hnd).
        apply (gp3_slot_kept_x ly3 S3 W mem mdc ly4 S4 W2 mem4 i _ HAR (HSLOT i Hi) Hi).
        + intros a Ha. apply HKEEPS; [unfold ASRC in *; lia|].
          intros j Hj Hrj.
          assert (Hji : j <> i) by (intros ->; exact (Hnd Hj)).
          pose proof (HJS4 j Hj) as Hj4.
          assert (HZ : Z.of_nat j <> Z.of_nat i) by (intros Heq; apply Hji; lia).
          unfold ASRC in *. lia.
        + intros b Hb.
          assert (HbO : In b OTH).
          { unfold OTH. apply in_concat. exists (slot_blks (nth i (lm_hs m) None)). split; [|exact Hb].
            apply in_map_iff. exists i. split; [reflexivity | apply gp3_cs_spec; split; [exact Hi | exact Hnd]]. }
          assert (Hbr : In b rest4)
            by (apply (Permutation_in _ (Permutation_sym Hrest)); apply in_app_iff; left; exact HbO).
          assert (Hb3 : In b (ablocks B ly3 S3)).
          { destruct (nth i (lm_hs m) None) as [h|] eqn:Ei; [|destruct Hb].
            pose proof (HSLOT i Hi) as Hsl. unfold aslot in Hsl. rewrite Ei in Hsl.
            exact (proj2 (gk_asrc_x B ARx LAWS BLKN ly3 S3 W mem mdc _ h HAR Hsl
              ltac:(unfold fr_RG; cbn; unfold ASRC; lia)
              ltac:(unfold fr_RG, GK_CEIL8; cbn; unfold ASRC; pose proof gk_ceil_lo; lia)) b Hb). }
          split; [exact (Hrest4 b Hbr)|].
          intros a Ha. apply (KBLK b a Hbr Hb3). destruct b as [p n]. cbn [fst snd] in *.
          destruct (gk_blk_x B ARx LAWS BLKN ly3 S3 W mem mdc p n HAR Hb3) as (_ & _ & Hn). lia. }
    split; [exact HREL4|].
    split; [exact HOUT4|].
    split.
    { apply (agone_at_kept fr_RG W mem W2 mem4 _ HGONE). intros r Hr a Ha. destruct Hr as [<- | []].
      cbn [fst snd] in Ha. apply KG4. unfold gp3_g4. lia. }
    split; [exact HLOCK4|].
    split.
    { apply (awake_at_kept fr_RG W mem W2 mem4 HWAKE). intros r Hr a Ha. destruct Hr as [<- | []].
      cbn [fst snd] in Ha. apply KWAKE. lia. }
    split; [apply (akept_vm W mem); [intros x Hx; apply KG4; unfold gp3_g4; cbn in Hx; lia | exact HNFD]|].
    split; [apply (akept_awr W mem); [intros x Hx; apply KG4; unfold gp3_g4; lia | exact HNFDW]|].
    split; [exact HNFDR|].
    split; [apply (akept_vm W mem); [intros x Hx; apply KG4; unfold gp3_g4; cbn in Hx; lia | exact HTU]|].
    split; [destruct HLST as [lst Hlst]; exists lst;
            apply (akept_vm W mem); [intros x Hx; apply KG4; unfold gp3_g4; cbn in Hx; lia | exact Hlst]|].
    apply (akept_awr W mem); [intros x Hx; apply KG4; unfold gp3_g4; lia | exact HLSTW]. }
  (* the live blocks after the call: the model's, the input, and the same rest *)
  assert (HP1 : Permutation (ablocks B ly4 S4) (input_blks cx ++ model_blks m1 ++ rest0)).
  { assert (HOTH1 : concat (map (fun j => slot_blks (nth j hs1 None)) (gp3_cs js)) = OTH).
    { unfold OTH. f_equal. apply map_ext_in. intros j Hj. apply gp3_cs_spec in Hj as [Hj4 Hnin].
      rewrite (Hhs1 j Hj4), (gp3_pick_none _ _ _ _ j HLENhs Hnin). reflexivity. }
    assert (HNEW : concat (map (fun j => slot_blks (nth j hs1 None)) js) =
        concat (map (fun p => if re_eof (fst (fst p)) =? 0 then asrc_blks (snd (snd p)) else [])
           (combine (combine (lm_es m) hs) qs))).
    { apply (gp3_newsrcs_of_slots _ (lm_es m) hs qs HLENhs HLENq).
      intros i Hi Heof. pose proof (proj1 (HPOKi i Hi Heof)) as Hj4.
      rewrite (Hhs1 _ Hj4), (gp3_pick_some _ _ _ _ i Hi HLENhs HNDl Heof). reflexivity. }
    pose proof (gp3_perm_slots hs1 js Hlen1 HNDl HJS4) as HPS1.
    rewrite HNEW, HOTH1 in HPS1.
    eapply Permutation_trans; [exact HPERMb|].
    eapply Permutation_trans.
    { apply perm_skip. apply Permutation_app_head. apply Permutation_app_head. apply Permutation_app_head.
      exact Hrest. }
    apply Permutation_sym. unfold model_blks, m1. cbn [lm_G lm_es lm_hs lm_cap lm_out].
    eapply Permutation_trans;
      [exact (gp3_perm_cong (input_blks cx) (concat (map aentry_blks (map fst qs)))
         (aout_blks cap4 out4) rest0 _ _ (lm_G m, ATABLE) HPS1)|].
    apply gp3_perm_pre. }
  assert (HSEP1 : ablocks_sep B fr_FP cx m1 ly4 S4).
  { split; [exists rest0; exact HP1|].
    intros b Hb.
    destruct (in_dec DEC b (ablocks B (c_ly cx) (c_S cx))) as [Hent | Hnent]; [|left; exact Hnent].
    assert (Hb4 : In b (ablocks B ly4 S4))
      by (apply (Permutation_in _ (Permutation_sym HP1)); apply in_app_iff; right; apply in_app_iff; left; exact Hb).
    destruct (in_dec DEC b (ablocks B ly3 S3)) as [Hb3 | Hnb3].
    - assert (Hbm : In b (model_blks m)).
      { pose proof (Permutation_in _ HPERM0 Hb3) as Hb0.
        pose proof (Permutation_NoDup HP1 (gp3_nodup_blocks_x ly4 S4 W2 mem4 md4 HAR4)) as ND1.
        apply in_app_iff in Hb0 as [Hb0 | Hb0].
        - exfalso. exact (gp3_nodup_app_neq _ _ b ND1 Hb0 ltac:(apply in_app_iff; left; exact Hb)).
        - apply in_app_iff in Hb0 as [Hb0 | Hb0]; [exact Hb0|]. exfalso.
          rewrite app_assoc in ND1.
          exact (gp3_nodup_app_neq _ _ b ND1 ltac:(apply in_app_iff; right; exact Hb) Hb0). }
      exact (HSEPFP b Hbm).
    - right. intros a Ha.
      destruct (gp3_inner_xR G_fr LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx) (c_ly cx) (c_S cx) (c_W cx)
        (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem mdc kk HJ) as (memS & HJi & _).
      pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & C12 & _).
      destruct b as [p n]. cbn [fst snd] in Ha.
      destruct (gk_blk_x B ARx LAWS BLKN ly4 S4 W2 mem4 md4 p n HAR4 Hb4) as (_ & _ & Hn).
      replace a with (p + (a - p)) by lia.
      apply (C12 p n (a - p) Hent Hnb3). lia. }
  (* the arm's other facts *)
  assert (HFR1 : gframe cx fake_shadow_open (frame_addr ly4 1 fpos) W2 mem4).
  { rewrite HFFeq. apply (gp3_gframe_kept cx _ _ W W2 mem mem4 HFR eq_refl); [lia | exact KSTK | exact KFRM | exact KSH]. }
  assert (HFLAG' : sv8 W2 mem4 (frame_addr ly4 1 fpos + 120) (flag_addr ly4 1 fpos)).
  { rewrite HFFeq, HFLeq. apply (gk_sv8_kept W W2 mem mem4); [intros x Hx; apply KFRM; lia | exact HFLAG]. }
  assert (H16' : sv8 W2 mem4 (lf_F cx + 16) (c_p cx + gn_kq cx m))
    by (apply (gk_sv8_kept W W2 mem mem4); [intros x Hx; apply KSTK; lia | exact H16]).
  assert (H144' : sv8 W2 mem4 (lf_F cx + 144) (c_n cx - gn_kq cx m))
    by (apply (gk_sv8_kept W W2 mem mem4); [intros x Hx; apply KSTK; lia | exact H144]).
  assert (H88' : sv8 W2 mem4 (lf_F cx + 88) t)
    by (apply (gk_sv8_kept W W2 mem mem4); [intros x Hx; apply KSTK; lia | exact H88]).
  assert (SV24' : sv8 W2 mem4 (lf_F cx + 24) HI_G_NOUT)
    by (apply (gk_sv8_kept W W2 mem mem4); [intros x Hx; apply KSTK; lia | exact SV24]).
  assert (HIN' : ainput_at B cx ly4 S4 W2 mem4).
  { apply (gp3_ainput_kept cx ly3 S3 W mem ly4 S4 W2 mem4 HIN HlenP). intros Hn.
    assert (Hb0r : In (c_p cx, c_n cx) rest4).
    { apply (Permutation_in _ (Permutation_sym Hrest)). apply in_app_iff. right. apply in_app_iff. left.
      unfold input_blks. rewrite (proj2 (Z.eqb_neq (c_n cx) 0) ltac:(lia)). left. reflexivity. }
    assert (Hb03 : In (c_p cx, c_n cx) (ablocks B ly3 S3)).
    { destruct HIN as ([(Hn0 & _) | (_ & Hin)] & _); [lia | exact Hin]. }
    split; [exact (Hrest4 _ Hb0r)|].
    intros a Ha. apply (KBLK _ a Hb0r Hb03). cbn [fst snd]. unfold req_size.
    rewrite (proj2 (Z.eqb_neq (c_n cx) 0) ltac:(lia)). lia. }
  assert (HRV' : rom_view segs W2 mem4)
    by exact (ajournal_gx_rom_view_xR segs B PST ARx LAWS pa_segs_low (G_RIG B fr_RG) 0 []
                _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc gp3_rom_out gp3_rom_pst HRV).
  assert (HJT' : jt_rom W2 mem4) by exact (gp3_jt_kept W W2 mem mem4 HRV HRV' HJT).
  assert (HREADS' : forall j, (j < 4)%nat -> gn_sv4 W2 mem4 (lf_F cx + 192 + 4 * Z.of_nat j) (gn_reads m j)).
  { intros j Hj. unfold gn_sv4. apply (akept_vm W mem); [|exact (HREADS j Hj)].
    intros x Hx. apply KSTK. cbn in Hx. lia. }
  assert (HAWR' : awr W2 mem4 (lf_F cx + 192) 16)
    by (apply (akept_awr W mem); [intros x Hx; apply KSTK; lia | exact HAWR]).
  assert (HAT' : sv8 W2 mem4 (lf_F cx + 208) 0)
    by (apply (gk_sv8_kept W W2 mem mem4); [intros x Hx; apply KSTK; lia | exact HAT]).
  assert (HPFX' : gn_prefix_at cx m W2 mem4 (frame_addr ly3 1 fpos)).
  { destruct HPFX as (P1 & P2 & P3 & P4 & P5).
    split; [intros i Hi; rewrite (proj1 (KFRM (frame_addr ly3 1 fpos + 32 + i) ltac:(lia))); exact (P1 i Hi)|].
    split; [rewrite (proj1 (KFRM (frame_addr ly3 1 fpos + 32 + Z.of_nat (length (gn_pre cx m))) ltac:(lia)));
            exact P2|].
    split; [intros a Ha; rewrite (proj1 (KFRM a ltac:(lia))); exact (P3 a Ha)|].
    split; [exact P4 | exact P5]. }
  (* what rig_post_x says of the new table: its functional relation, its length, and the model clauses of
     aentry_ok that its arelay_at gives of every entry (the base's gn_rig_ok) *)
  assert (HROK : gn_rig_ok cx m hs qs c4 O4 cap4).
  { split; [exact HRREL|]. split; [exact HLENq|].
    pose proof HREL4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HAEq & HNDq & _).
    split; [|exact HNDq].
    rewrite Forall_forall in HAEq |- *. intros e He.
    destruct (HAEq e He) as (E1 & E2 & E3 & E4 & E5 & _ & _ & _ & _ & _ & E11 & _ & _ & E14 & _).
    exact (conj E1 (conj E2 (conj E3 (conj E4 (conj E5 (conj E11 E14)))))). }
  assert (HDONE : gdone RINV cx t m m1).
  { exists hs, qs, c4, O4, cap4, out4. split; [exact HPOK|]. split; [exact HAFTER|].
    split; [exact HROK|]. split; [exact HRI|]. split; [exact HOP|].
    (* _gone_p3.v:1461: the facts of amodel_at m (GRG_x's gst_x) that gdone carries for GN_RI_step / GN_RI_end *)
    pose proof HREL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HAE0 & _).
    split.
    { rewrite Forall_forall in HAE0 |- *. intros e He.
      destruct (HAE0 e He) as (_ & _ & _ & _ & _ & _ & _ & _ & HU & _ & _ & _ & _ & _ & HK).
      split; [exact HU|].
      rewrite Forall_forall in HK |- *. intros k Hk.
      destruct (HK k Hk) as (_ & _ & Hz & Hl). exact (conj Hz Hl). }
    split.
    { pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
        _ & _ & GdC).
      destruct GdC as [(GdC & _) | (GdC & _)]; lia. }
    split.
    { rewrite Forall_forall in HAE0 |- *. intros ge gHe.
      destruct (HAE0 ge gHe) as (_ & _ & _ & _ & _ & GdC6 & GdC7 & GdC8 & _ & _ & _ & GdC12 & _ & _ & _).
      split; [lia|]. split; [exact GdC6|].
      destruct GdC12 as [GdC12 | (GdH & _ & GdK1 & GdK2 & _)];
        [left; exact GdC12 | right; exact (conj GdH (conj GdK1 GdK2))]. }
    split.
    2: {
      split; [exact HMpos|]. split; [exact HMSZ|].
      { (* GN_CNT_step's C2: the representation clause of the table relay_instance_gone leaves (rig_post's
         arelay_at .. (map fst qs), aentry_ok W_rep.v:134-135) *)
      pose proof HREL4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & GdAEq & _).
      rewrite Forall_forall in GdAEq |- *. intros ge gHe.
      destruct (GdAEq ge gHe) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & GdC12 & _ & _ & _).
      destruct GdC12 as [GdC12 | (GdH & _ & GdK1 & GdK2 & _)];
        [left; exact GdC12 | right; exact (conj GdH (conj GdK1 GdK2))]. }
    }
    rewrite Forall_forall. intros go gHo. apply (In_nth (lm_hs m) go None) in gHo as (gi & gHi & <-).
    pose proof (HSLOT gi ltac:(lia)) as GdSl. unfold aslot in GdSl.
    destruct (nth gi (lm_hs m) None) as [gh0|]; [|exact I].
    destruct GdSl as (_ & _ & _ & _ & _ & _ & _ & _ & _ & GdPL & _ & _ & _ & _ & GdOFF & _).
    split; [exact GdOFF|].
    destruct GdPL as (_ & _ & _ & _ & _ & _ & _ & _ & GdF).
    rewrite Forall_forall in GdF |- *. intros gr gHr. destruct (GdF gr gHr) as (_ & _ & _ & GdNe).
    exact (GdNe eq_refl). }
  (* _gone_p3.v:1515: the block relation from the LS state (ly3, S3) to the state after the call (ly4, S4): HP1
     is at the SAME rest0 as the entry's ablocks_sep (HPERM0); any rest of (ly3, S3) is a permutation of rest0.
     KF-COUNT: the meter cost is relay_instance_gone's own (rig_post_x's HMO), at the pairing hs gdone carries *)
  assert (HLS1 : exists ly0 S0 cst, LSx cx t m ly0 S0 /\ mo_le MT S0 S4 cst /\ gn_cst MT cx m m1 0 cst /\
    gn_tie B cx m ly0 S0 m1 ly4 S4).
  { exists ly3, S3. eexists. split; [exact HLS|]. split; [exact HMO|].
    split.
    { eexists. split; [exists hs, qs, c4, O4, cap4, out4; split; [exact HPOK|]; split; [exact HAFTER | reflexivity]|].
      rewrite Z.add_0_r. apply Z.le_refl. }
    split; [exists rest0; exact HPERM0|].
    intros rest Hr.
    assert (Hrr : Permutation rest rest0).
    { apply (Permutation_app_inv_l (input_blks cx ++ model_blks m)). rewrite <- !app_assoc.
      exact (Permutation_trans (Permutation_sym Hr) HPERM0). }
    eapply Permutation_trans; [exact HP1|].
    apply Permutation_app_head. apply Permutation_app_head. apply Permutation_sym. exact Hrr. }
  (* ---- 0x84b4c: auipc a0,0x554; addi s4,a0,788; addi s5,s1,192; addi s6,s1,208, up to the loop's head ---- *)
  assert (HQ1 : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + AF_gp3_ret)) by (rewrite Q1; reflexivity).
  rewrite HQ1.
  (* NOTE: do not clear HFr; it is gn_nums_x' frame bound, which the run tactics' fresh HFr would shadow *)
  try clear HS SHOK HF.
  assert (RR : forall r : bv 5, acallee_saved (bv_unsigned r) -> In r gp3_kept -> getr regs4 r = getr regs r)
    by (intros r H1 H2; rewrite (gp3_pres (ms_regs ms) regs4 r HPRES H1); exact (KR r H2)).
  destruct (gp3_entry2 W2 regs4 mem4) as [HSb SHOKb].
  remember (Eimg (Ereg regs4 gp3_extra)) as Eb eqn:HEb.
  assert (HEIb : img_env VAL A_LIM Eb) by (subst Eb; apply Eimg_env).
  assert (HAEb : env_agree 32 (Ereg regs4 gp3_extra) Eb)
    by (rewrite HEb; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (Eb9 : ew Eb 9 = Z_to_bv 64 (lf_F cx)).
  { subst Eb. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs4 _ 9 9%bv eq_refl).
    rewrite (RR 9%bv ltac:(gp3_csd) ltac:(cbv; tauto)). exact R9. }
  clear HEb.
  paj_run_to_tok_xR RUNTOG HSb HJ2 SHOKb gp3_span AF_gn_c1.
  { apply awr_ok_x_nil. }
  pmkst HSb.
  gp3_meq HF Em2.
  pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs4 gp3_extra gp3_kept2 HSb HAEb
    ltac:(vm_compute; reflexivity)) as KR2.
  prreg HSb (20%bv : bv 5) Q20.
  prreg HSb (21%bv : bv 5) Q21.
  prreg HSb (22%bv : bv 5) Q22.
  cbn [ms_regs restrict] in KR2.
  rewrite Em2 in *.
  (* the three registers the loop head reads *)
  assert (UF : bv_unsigned (Z_to_bv 64 (lf_F cx)) = lf_F cx).
  { apply unsigned_lit_small. clear - HFlo HFr Hspr AC C1. unfold LLVMF_STK in *. lia. }
  assert (R20' : getr (ms_regs ms0) 20 = w64 (rg_s fr_RG + ASRC * Z.of_nat 0)).
  { apply bv_eq. rewrite Q20, (HEIb 260%nat ltac:(unfold A_TEXT, A_LIM; lia)). vm_compute. reflexivity. }
  assert (R21' : getr (ms_regs ms0) 21 = w64 (lf_F cx + 192 + 4 * Z.of_nat 0)).
  { rewrite Q21, Eb9, UF.
    replace (lf_F cx + 192 + 4 * Z.of_nat 0) with (lf_F cx + 192) by (cbn [Z.of_nat]; clear; lia). reflexivity. }
  assert (R22' : getr (ms_regs ms0) 22 = w64 (lf_F cx + 208)).
  { rewrite Q22, Eb9, UF. reflexivity. }
  (* the registers kept from the arm's entry *)
  assert (RF : forall r : bv 5, acallee_saved (bv_unsigned r) -> In r gp3_kept -> In r gp3_kept2 ->
      getr (ms_regs ms0) r = getr regs r)
    by (intros r H1 H2 H3; rewrite (KR2 r H3); exact (RR r H1 H2)).
  apply (YA0nH.SRrG_ret _ R R_refl).
  exists m1, (ms_regs ms0), mem4, (with_vm_backing (m_vm_lazy md4) mat0 md4), ly4, S4, (kk + k4), fpos.
  split; [reflexivity|].
  split.
  { split; [|split; [exact HMOD1 | split; [exact HSEP1 | exact (proj1 (RPNP S4 _) HRM4)]]].
    split; [exact HJ2|]. split; [exact HFR1|]. split; [exact HFLAG'|]. split; [exact H16'|].
    split; [exact H144'|]. split; [exact H88'|].
    split; [exact HIN'|]. split; [exact HRV' | exact HJT']. }
  split; [exact HDONE|]. split; [exact HLS1|].
  split.
  { rewrite HFFeq. unfold gn_kregs.
    do 7 (split; [match goal with |- getr _ ?r = _ =>
      rewrite (RF r ltac:(gp3_csd) ltac:(cbv; tauto) ltac:(cbv; tauto)); assumption end|]).
    match goal with |- getr _ ?r = _ =>
      rewrite (RF r ltac:(gp3_csd) ltac:(cbv; tauto) ltac:(cbv; tauto)); assumption end. }
  split; [exact SV24'|].
  split; [exact R20'|]. split; [exact R21'|]. split; [exact R22'|].
  split; [clear; lia|].
  split; [exact HREADS'|]. split; [exact HAWR'|]. split; [exact HAT'|].
  rewrite HFFeq. exact HPFX'.
Qed.

End gp3R.

End gp3.

