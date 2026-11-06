(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/CrcB.v, with its module paths and module names changed; 479 of its 545 lines of code are new or changed and 448 lines of the source are left out. *)
(* fuzz_preset, image B' (#102 pins: asan-ubsan sha256 d663f82d7f488d30): S1 of the walk of padded - the entry seat,
   the prologue (B' 0x830a8-0x830cc), the raw malloc wrapper's call (0x830d0, Listing_prog.v 8bcc2c9e7809 :1680
   PCall AS___wrap_malloc) through YGcallMxmnKeep.v aj_malloc_x_m_keep at the cf instance (the call's memnorm keep is
   its last conjunct; pd_mn carries it to the post's keep), the return to PD_TEST (0x830d8), and
   the close by pd_s2_stmt. Split out of Padded102B.v (the frozen interface + the shared seat) so that the interface
   file stays cheap for the rows: the closed listing table PL_pd_B is S1's alone.
   rule 24: proves function padded (reuse search: the internal file REWALK-102-PLAN.md section D3: none exists).
   Inputs: as Padded102B.v's header. Numerals: as Padded102B.v's header; 6664 (DERIVED: PD_OFF + PD_RETM, padded's
   return site of the wrapper call). No ADDRESS literal. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG YCbqGcall.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames YGcallx YGcallcf YGcallMx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG01cf YG00cf YG0ncf YG0dcf YG0sshcf YGcfRoomPre YG0lawscf YGcfApath.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YSRrMemnorm YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YGcfRoomKeep YGcfRoomLive.
(* the keep twins of the malloc call: the rule and the callee's keep text *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallMxmnKeep YGcfMallocComposeKeep.
(* the hull: the call's secondary count rule (secs_malloc_step) and preset's budget leaf (hull_ok_of_budget) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfSecsStep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PresetHullPay.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetLiveBounds PresetRoomPos PresetRun
  PresetReqAt PresetRoomPosKeep PresetHullBudget.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnAlloc PRH_FnReader
  PRH_FnCheck CfParamsPreset.
(* lib/A/CfRoomLivePreset.v is NOT Required: it pulls lib/Spec/PresetLiveSec.v and PresetGate.v, whose closure reaches
   lib/Prog/SlotSizes.v -> PjWriteHyp -> lib/Contract -> lib/ZImage.v, which did not build on the #102 facts
   preset-tree-at-2026-10-29T12-03-17Z.tsv (sha256 43b6000a63b5; internal record) (ZImage.v:38 pins the PLAIN image
   entry; measured by the tx_put A' walk, log of a build of those facts). At the kit cut preset-tree-at-2026-10-30T04-57-22Z.tsv
   (sha256 652fe98064b9; internal record) ZImage.v builds again (PRH_Refute below holds it in its closure), but the text
   names the room counts in the leaf's words, so the live-set bounds the malloc keep needs stay ONE named entry argument
   in the kit's spelling over the LEAF lib/Spec/PresetLiveBounds.v (it Requires only PresetReqAt). *)
(* the refutation family of the refused arms (lib/A/PRH_Refute.v (sha256 fe030135cfdc; internal record) at the kit cut, a consumer-tree
   file, NOT a kit text): prh_refute_at closes the kit's outcome clause on the NULL arm (pd_dead). Its closure (PresetCfnA)
   builds at the cut (whole-unit landing build of the fuzz_preset tree preset-tree-at-2026-10-30T04-43-07Z.tsv (sha256 ca64a61eb0bb; internal record), 2026-10-30T04:44Z: PRH_Refute.vo compiled). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Refute.
(* the closure's fifth clause at padded's observed context (lib/A/PRH_Witness.v
   c5_padded_trace_B; a consumer-tree file, NOT a kit text): the wrapper call's trace over the caller's
   chain is a FIXED trace, from the text's own prh_univ_closure and prh_ctx premises *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Witness.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import Padded102B Padded102B_Home.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

(* ======== S1 at the walk's room instance ========
   The interface above is generic in the class PrhRoomLive (the kit's spelling). S1 makes an allocator call, and the keep
   of room_live_cf across malloc_cf (YGcfRoomLive.v:1433 RL_malloc_step) is the allocator-model owner's, so S1 is stated at
   RL := prh_room_live_a8 (PRH_Base.v:272, the instance every walk takes; PRH_Base.v's header) - the rows stay generic. *)
Section s1. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg}.
Context {SK : YI16.sink_head}.
Context {PA : PAImg B_prog_listing}.
#[local] Existing Instance prh_img_B.
#[local] Instance pd_RL : PrhRoomLive := prh_room_live_a8 (cp := CfParams_preset).
#[local] Notation CP := CfParams_preset.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation VAL := (@pa_val _ B_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
#[local] Notation PST := (@prh_pst prh_img_B).
Variable B : asyms.
#[local] Notation ARc := (fun ly S Hp W mem md => ARcf (cp := CP) SEGS B ly S Hp W mem md /\ xs_placed_cf ly S).
(* the allocator's laws at ARcf (AR_laws_ok_cf, YG0lawscf.v) and AR_laws_x from them (YGcallcf.v) *)
Let LAWS_cf : AR_laws_cf (cp := CP) SEGS B := AR_laws_ok_cf (cp := CP) SEGS B.
Let LAWS : AR_laws_x SEGS B ARc (@cf_head CP) := AR_laws_x_xs (cp := CP) SEGS B LAWS_cf.
(* S1's callee: the raw malloc wrapper's KEEP text (YGcfMallocComposeKeep.v amalloc_realizes_cf_keep: YG0dcf.v's
   amalloc_realizes_cf with the memnorm keep at the leaf's end). The two facts of the unit's
   binding of B it reads are pd_img's fields pdi_malloc / pdi_env, not separate hypotheses. *)
Hypothesis AMALLOC : YGcfMallocComposeKeep.amalloc_realizes_cf_keep (cp := CP) SEGS B.

(* the write permission of the prologue's five stores: the one window is the stack region [-48, 0) of the entry sp
   (FuzzStrdupB.v:234 sd_awr, at the frame 48) *)
Ltac pd_awr rg HU :=
lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0 ?bc ?ly' ?own' =>
let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0 bc ly' own') end;
lazymatch goal with |- awr_ok _ _ _ ?sp0' _ _ _ _ _ =>
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spZ rg - sp0')) end;
[ reflexivity
| cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth]; rewrite ?ew_ewset_other by lia;
rewrite ?ew_havoc_old by (cbv; lia); rewrite HU; lia
| cbn [YP09.r_wlo stack_region]; lia
| cbn [YP09.r_whi stack_region]; lia
| apply awr_ok_nil ].

(* ======== S1 (mine): the entry seat, the prologue, the wrapper call, the run to PD_TEST ======== *)
(* the entry environment: the machine registers, no extra atom (FuzzStrdupB.v:70 SD_EI) *)
Definition pd_E0 (regs : bvmap 5 word) : env := @Eimg _ B_prog_listing PA (Ereg regs []).

(* the entry seat: one stack region with the write window [-48, 0), a1 = size bounded (FuzzStrdupB.v:288 sd_entry,
   at the frame 48 and with the size fact) *)
Lemma pd_entry : forall STK ly S Hp W regs mem md ch,
  afn_pre_x SEGS B ARc STK ly S Hp W regs mem md ch -> 48 <= STK ->
  0 <= bv_unsigned (getr regs 11%bv) <= 2 ^ 40 ->
  (forall E, img_env VAL A_LIM E -> alias_ok E B_alias_hints) ->
  st_ok_pi SEGS VAL (pd_E0 regs) pd_ss0 (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + PD_OFF)) mem (seg_rom SEGS)))
  /\ sh_ok SEGS PD_Bx [] (pd_E0 regs) (mrestrict (w_H W) mem).
Proof.
intros STK ly S Hp W regs mem md ch HPRE H48 H11 HAL.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof alloc_ceiling_value as [CL _].
assert (Rsp : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
rewrite restrict_mkst_fx.
set (E := pd_E0 regs) in *.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold pd_E0; apply Eimg_env).
assert (E2 : ew E 2 = getr regs 2)
  by (subst E; unfold pd_E0; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E11 : ew E 11 = getr regs 11)
  by (subst E; unfold pd_E0; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 11 11%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
split.
- unfold pd_ss0. apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold stack_region. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
    intros q Hq. apply (apresent_writable SEGS). apply Hpres. lia.
  + cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
  + split; [|split; [exact I | exact (HAL E HEI)]].
    cbn [pd_facts0 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E11. change (2 ^ 4) with 16. rewrite Z.pow_0_r, Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; lia.
- unfold sh_ok. apply Forall_nil.
Qed.
(* the call's trace through the caller's chain is padded's return site prepended to the chain's spine *)
Lemma pd_trace_eq : forall pc0 sp ra s0 (ch : list (Z * Z * Z)),
  unwind_of_chain pc0 ((sp, ra, s0) :: ch) = prh_trace pc0 ra (spine ch).
Proof.
intros pc0 sp ra s0 ch. unfold unwind_of_chain, prh_trace, spine. f_equal. f_equal.
cbn [flat_map]. f_equal. induction ch as [|((a1, a2), a3) ch IH]; [reflexivity|].
cbn [flat_map map fst snd]. rewrite IH. reflexivity.
Qed.

(* S1's other call-rule arguments (FuzzMallocB.v:276-279's Lets) *)
Let OWNLOW := ARx_owned_low_law_xs SEGS B LAWS_cf.
Let WFL := ARx_wf_law_xs (cp := CP) SEGS B.
Let XSL := ARx_xs_law_xs (cp := CP) SEGS B.
Let AMALLOCx := YGcallMxmnKeep.amalloc_realizes_x_xs_keep SEGS B AMALLOC.

(* ---- the one MARKED image fact Padded102B_Home.v's pdh_src_rd_at takes beyond the allocator (its Section hypothesis
   pdh_img_vis, verbatim at ARx := ARc): img_shadow_vis_cf (lib/Reusable/YGcfAmx2.v), NOT derivable from
   ARcf. S1 needs it only to move the source window's src_rd across the wrapper call (the shadow of the source is
   re-derived at the new allocator state, as the call keeps no shadow byte). Its other hypothesis pdh_zs_al is NOT a
   premise: S1 derives it from the entry's ARcf (YG0f.v asyms_ok aso_zshadow, amc_syms), FuzzStrdupB.v:471's way. ---- *)
Hypothesis pd1_img_band : 0 <= @pa_lo _ B_prog_listing PA /\ @pa_hi _ B_prog_listing PA <= 2 ^ 47.
Hypothesis pd1_img_vis : forall ly S Hp W mem md a, ARc ly S Hp W mem md -> @pa_lo _ B_prog_listing PA <= a < @pa_hi _ B_prog_listing PA ->
  aview SEGS (w_H W) mem (shadow_addr a) <> None.
(* ---- the cf layer's read-only fact at the call memory (YGcallcf.v QMm_cf's last conjunct: arodata_ok_cf at the
   class instance ci), from the walk entry's reader form over PA's RELRO bounds (fpre's arodata_okP). A MARKED image
   fact: it ties ci's RELRO range and read-only reads to PA's image, as the driver sites' drv_aro_link
   (lib/AU/PresetD1sitesB.v) does. At CfImg_B and PI_prog_B it is YGcfAroBridge.arodata_ok_cf_of_P over
   lib/AU/CfAroPresetB.v's rows (Padded102B_Inst.v pdi_aro_link_B). ---- *)
Hypothesis pd1_aro : forall (W : world SEGS) (mem : word -> option byte),
  arodata_okP SEGS (@pa_relro_lo _ _ PA) (@pa_relro_hi _ _ PA) B (aview SEGS (w_H W) mem) ->
  arodata_ok_cf SEGS B mem.

(* a chunk of a region of a symbolic memory is a val_mem of the machine memory (FuzzMallocB.v:232 fm_chunk_val) *)
Lemma pd_chunk_val : forall E (m : word -> option byte) rs i r off n e v,
  mem_ok SEGS E m rs -> nth_error rs i = Some r -> In (YP09.mkChunk off (CVal n e)) (YP09.r_chunks r) ->
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N n) -> Z.of_N n <= 8 ->
  val_mem SEGS m (base_val E (YP09.r_base r) + off) (N.to_nat n) v.
Proof.
intros E m rs i r off n e v (Hwf & Hrs & Hpd) Hi Hc He Hv Hn.
pose proof (proj1 (Forall_forall _ _) Hrs r (nth_error_In _ _ Hi)) as (_ & _ & _ & Hcs).
exact (val_of_chunk_ok SEGS E m _ off n e v (proj1 (Forall_forall _ _) Hcs _ Hc) He Hv Hn).
Qed.

(* a val_mem of eight bytes is the rdword of the view (lib/Reusable/YCem.v:101 rdword_of_val_mem, copied body for body:
   YCem.v's closure reaches lib/Reusable/YImgCellsB.v, which does not build on the #102 pins' IMG_TOP_B) *)
Lemma pd_rdword_of_val_mem : forall H mem a v,
  val_mem SEGS (mrestrict H mem) a 8 v -> 0 <= v < 2 ^ 64 -> rdword (aview SEGS H mem) a = Some v.
Proof.
intros H mem a v Hv Hr.
assert (B0 : forall k, (k < 8)%nat -> aview SEGS H mem (a + Z.of_nat k) = Some (le_byte v 8 k)).
{ intros k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. unfold le_byte. apply Z.mod_mod. lia. }
unfold rdword.
rewrite <- (Z.add_0_r a) at 1. change 0 with (Z.of_nat 0) at 1. rewrite (B0 0%nat) by lia.
change 1 with (Z.of_nat 1). rewrite (B0 1%nat) by lia. change 2 with (Z.of_nat 2) at 1. rewrite (B0 2%nat) by lia.
change 3 with (Z.of_nat 3). rewrite (B0 3%nat) by lia. change 4 with (Z.of_nat 4). rewrite (B0 4%nat) by lia.
change 5 with (Z.of_nat 5). rewrite (B0 5%nat) by lia. change 6 with (Z.of_nat 6). rewrite (B0 6%nat) by lia.
change 7 with (Z.of_nat 7). rewrite (B0 7%nat) by lia.
f_equal. apply le_bytes8. exact Hr.
Qed.

(* a saved word of the frame, read back at a later memory that keeps its eight bytes *)
Lemma pd_frame_word : forall E (W W2 : world SEGS) m m2 rs r off (k : nat) v,
  mem_ok SEGS E (mrestrict (w_H W) m) rs -> nth_error rs 0 = Some r -> YP09.r_base r = Some 2%nat ->
  In (YP09.mkChunk off (CVal 8 (SOff k 0))) (YP09.r_chunks r) -> bv_unsigned (ew E k) = v ->
  (forall i, 0 <= i < 8 -> aview SEGS (w_H W2) m2 (bv_unsigned (ew E 2) + off + i) =
     aview SEGS (w_H W) m (bv_unsigned (ew E 2) + off + i)) ->
  rdword (aview SEGS (w_H W2) m2) (bv_unsigned (ew E 2) + off) = Some v.
Proof.
intros E W W2 m m2 rs r off k v HM Hn Hb Hc Hv HK.
assert (Rv : 0 <= v < 2 ^ 64) by (subst v; apply bv_unsigned_in_range).
assert (Hval : val_mem SEGS (mrestrict (w_H W) m) (base_val E (YP09.r_base r) + off) (N.to_nat 8) v).
{ apply (pd_chunk_val E _ rs 0 r off 8 (SOff k 0) v HM Hn Hc).
  - cbn [sv_denot]. rewrite Z.add_0_r, <- Hv, Z_to_bv_bv_unsigned. reflexivity.
  - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). exact Rv.
  - lia. }
rewrite Hb in Hval. cbn [base_val] in Hval. change (N.to_nat 8) with 8%nat in Hval.
rewrite (rdword_ext (aview SEGS (w_H W) m) (aview SEGS (w_H W2) m2) _ HK).
exact (pd_rdword_of_val_mem (w_H W) m _ v Hval Rv).
Qed.

(* a block appended to a pairwise-disjoint block list of nonnegative sizes: its base was no base before
   (FuzzMallocB.v:333 fm_new_block, at the base) *)
Lemma pd_new_block : forall (bl : list (Z * Z)) x, Forall (fun b => 0 <= snd b) bl -> 0 <= snd x ->
  YG0f.pairwise zdisjoint (map (fun b => (fst b, req_size (snd b))) (bl ++ [x])) -> ~ In (fst x) (map fst bl).
Proof.
intros bl x Hnn Hx Hp Hin. apply in_map_iff in Hin as (y & Hy & Hiny). rewrite map_app in Hp. cbn [map] in Hp.
pose proof (prh_pw_last zdisjoint _ _ Hp (fst y, req_size (snd y))
  (in_map (fun b => (fst b, req_size (snd b))) bl y Hiny)) as Hd.
pose proof (proj1 (Forall_forall _ _) Hnn y Hiny) as Hy0.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Hy in Hd.
pose proof (prh_req_size_pos (snd x) Hx). pose proof (prh_req_size_pos (snd y) Hy0). lia.
Qed.

(* a member of a pairwise-disjoint list is disjoint from the appended block *)
Lemma pd_old_apart : forall (bl : list (Z * Z)) x y,
  YG0f.pairwise zdisjoint (map (fun b => (fst b, req_size (snd b))) (bl ++ [x])) -> In y bl ->
  fst y + req_size (snd y) <= fst x \/ fst x + req_size (snd x) <= fst y.
Proof.
intros bl x y Hp Hin. rewrite map_app in Hp. cbn [map] in Hp.
pose proof (prh_pw_last zdisjoint _ _ Hp (fst y, req_size (snd y))
  (in_map (fun b => (fst b, req_size (snd b))) bl y Hin)) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. exact Hd.
Qed.

(* the reader's home survives a growth of the allocator's block list (its raw-block arm), Lam and Hp unchanged *)
Lemma pd_home_grow : forall ly S ly2 S2 Hp Lam p n,
  (forall bm, In bm (ablocks B ly S) -> In bm (ablocks B ly2 S2)) ->
  PRH_FnReader.prhReader_home B ly S Hp Lam p n -> PRH_FnReader.prhReader_home B ly2 S2 Hp Lam p n.
Proof.
intros ly S ly2 S2 Hp Lam p n Hsub [Hk | (b & m & Hin & Hn & H1 & H2)]; [left; exact Hk|].
right. exists b, m. exact (conj (Hsub _ Hin) (conj Hn (conj H1 H2))).
Qed.
(* S1 STATES THE KIT'S TEXT VERBATIM: PRH_FnCheck.v de94d3f3a7f1 tpadded_specX at this Section's image (prh_img_B, PA),
   CfParams_preset, the walk's room instance pd_RL and ARx := ARc; no premise beyond the text *)
Lemma pd_s1 : pd_img B -> pd_s2_stmt B ->
  forall CTX0, tpadded_specX (cp := CP) (PI := prh_img_B) (RL := pd_RL) (PA := PA) B ARc SK CTX0.
Proof.
intros IMG PS2 CTX0. unfold tpadded_specX.
intros ly S Hp W regs mem md ch data x fill Lam peak cnt fail ran most own
  [HPRE [HROD [HTOP [HRAZ HFRM]]]] HROOM HUNIV HCTX HSEC HC24 HHB H10 H11 H12 Hfill Hsz Hd0 Hdsz HSRC HHOME HMAX
  HLIVE HLED.
(* the wrapper call's trace over the caller's chain, at every return site of padded's malloc call: a FIXED trace,
   by the closure's fifth clause at the observed context raZ regs :: spine ch (PRH_Witness.v c5_padded_trace_B) *)
pose proof (PRH_Witness.c5_padded_trace_B (ci := ci) B CTX0 (raZ regs) (spine ch) HUNIV HCTX) as HTR.
set (size := Z.of_nat (length x)) in *.
pose proof (@pa_segs_low _ _ PA) as Hsegs.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FS : 48 <= @STK_padded prh_img_B) by (apply Z.leb_le; vm_compute; reflexivity).
assert (Rsz : 0 <= size <= 3 * 2 ^ 20) by (subst size; lia).
assert (H11u : 0 <= bv_unsigned (getr regs 11%bv) <= 2 ^ 40)
  by (rewrite H11; unfold w64; rewrite unsigned_lit_small by lia; lia).
destruct (pd_entry _ ly S Hp W regs mem md ch HPRE FS H11u (pdi_alias B IMG)) as [HS SHOK].
pose proof (ajournal_x_init (SK := SK) SEGS B PST ARc (@STK_padded prh_img_B) [] ly S Hp W regs mem md ch HPRE) as HJ.
set (E := pd_E0 regs) in *.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold pd_E0; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs []) n)
  by (intros n Hn; subst E; unfold pd_E0; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs []) E)
  by (subst E; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clearbody E.
pose (RUN := @paj_run_x_inv fx rc SK B_prog_listing PL_pd_B PA B PST ARc _ LAWS
  (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m)
  (srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) mem (srr_inv_laws_memnorm_k SEGS))).
assert (HPM : YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS mem) by (intros h; exact h).
unfold cfg_at. rewrite (pdi_entry B IMG). change (w64 (BASE + PD_OFF)) with (Z_to_bv 64 (BASE + PD_OFF)).
(* ---- slots 0..9 (B' 0x830a8-0x830cc): the frame, the five saves, s1 = fill, s2 = size, s3 = data,
   a0 = size + 16; the run stops at the wrapper's call (0x830d0) ---- *)
paj_run_tok_x_inv RUN HS HJ SHOK HPM PD_Bspan; [pd_awr regs Usp|].
rename HFr into HFr1. clear HF HG.
(* ---- the wrapper call at n = size + 16 (YGcallx aj_malloc_x at the cf instance, FuzzMallocB.v:551's form) ---- *)
lazymatch goal with HSx : st_ok _ _ ?ssx (restrict _ ?msc), HJx : ajournal_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  |- SRr _ _ (mkCfg _ ?mdc) _ =>
  prreg HSx (1%bv : bv 5) R1; prreg HSx (2%bv : bv 5) R2; prreg HSx (3%bv : bv 5) R3;
  prreg HSx (4%bv : bv 5) R4; prreg HSx (8%bv : bv 5) R8; prreg HSx (10%bv : bv 5) R10;
  prreg HSx (9%bv : bv 5) R9; prreg HSx (18%bv : bv 5) R18; prreg HSx (19%bv : bv 5) R19;
  prreg HSx (20%bv : bv 5) R20; prreg HSx (21%bv : bv 5) R21; prreg HSx (22%bv : bv 5) R22;
  prreg HSx (23%bv : bv 5) R23; prreg HSx (24%bv : bv 5) R24; prreg HSx (25%bv : bv 5) R25;
  prreg HSx (26%bv : bv 5) R26; prreg HSx (27%bv : bv 5) R27;
  pose proof (st_ok_mem_ok SEGS E ssx (restrict (w_H W) msc) HSx) as HMO;
  cbn [ss_mem restrict ms_mem setpc] in HMO;
  let l := eval vm_compute in (ss_mem ssx) in change (ss_mem ssx) with l in HMO;
  rename HSx into HSc; rename HJx into HJc; rename msc into msC; set (mdC := mdc) in *
end.
(* the entry registers through the environment (ew E r = getr regs r below the image atoms) *)
assert (EG : forall (n : nat) (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs r).
{ intros n r Hn Hr. rewrite EL by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hr. }
assert (E3 : ew E 3 = getr regs 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E8 : ew E 8 = getr regs 8) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 8 8%bv eq_refl)).
assert (E11 : ew E 11 = getr regs 11)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 11 11%bv eq_refl)).
pose proof (pdi_env B IMG) as HENV.
pose proof (pdi_base B IMG) as HBASE.
assert (Hsp1 : spZ (ms_regs msC) = spZ regs - 48)
  by (unfold spZ at 1; rewrite R2, Usp, unsigned_lit_small by lia; lia).
assert (Hra1 : raZ (ms_regs msC) = BASE + 6664)
  by (unfold raZ; rewrite R1, HBASE, unsigned_lit_small by (unfold B_prog_base; lia); reflexivity).
assert (Hs01 : s0Z (ms_regs msC) = s0Z regs) by (unfold s0Z; rewrite R8, E8; reflexivity).
pose proof alloc_ceiling_value as [[CL CM] _].
assert (Rsp : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
(* ---- the prologue's frame: the run wrote [spZ regs - 48, spZ regs) only ---- *)
assert (HFk : forall a, 0 <= a < 2 ^ 64 -> (a < spZ regs - 48 \/ spZ regs <= a) ->
  aview SEGS (w_H W) (ms_mem msC) a = aview SEGS (w_H W) mem a).
{ intros a Ha Hout. unfold aview, mbyte.
  assert (Hx : mrestrict (w_H W) (ms_mem msC) (Z_to_bv 64 a) = mrestrict (w_H W) mem (Z_to_bv 64 a)).
  { apply HFr1. intros (r & Hr & Hw). cbv [ss_mem pd_ss0] in Hr. destruct Hr as [<-|[]].
    cbn [base_val stack_region YP09.r_base YP09.r_wlo YP09.r_whi] in Hw.
    rewrite unsigned_lit_small, Usp in Hw by lia. lia. }
  rewrite Hx. reflexivity. }
assert (HROimg : forall a, in_roP SEGS (@pa_relro_lo _ _ PA) (@pa_relro_hi _ _ PA) a -> in_img SEGS a).
{ intros a [(sg & Hin & _ & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr] | exact (@pa_relro_img _ _ PA a Hr)]. }
(* the entry's reader form of the read-only bytes at the call memory: they are image bytes, below the frame *)
assert (HROc : arodata_okP SEGS (@pa_relro_lo _ _ PA) (@pa_relro_hi _ _ PA) B (aview SEGS (w_H W) (ms_mem msC))).
{ intros a Hro Hn He. pose proof (Hsegs a (HROimg a Hro)) as Hlo. unfold kLowMemEnd in Hlo.
  rewrite (HFk a ltac:(lia) ltac:(lia)). exact (HROD a Hro Hn He). }
pose proof HJc as (HARc & Hlyc & _ & _ & _ & _ & _ & _ & HJhic & _).
(* ---- the call's QMm_cf at the call memory: the room, the hull admission from the text's budget (A/PresetHullPay.v
   hull_ok_of_budget) and the read-only fact (pd1_aro over HROc) ---- *)
assert (HQMm : QMm_cf (cp := CP) SEGS B S (ms_mem msC))
  by exact (QMm_cf_of_room (cp := CP) SEGS B ly S Hp W (ms_mem msC) mdC (proj1 HARc) HQT
             (YGcfRoomKeep.RK_room S YGcfRoomKeep.RK_realloc (YGcfRoomLive.room_live_room_k S HROOM))
             (PresetHullPay.hull_ok_of_budget S _ HHB) (pd1_aro W (ms_mem msC) HROc)).
eapply SRr_bind.
{ eapply (YGcallMxmnKeep.aj_malloc_x_m_keep (SK := SK) SEGS B PST ARc (@QM_cf CP) (QMm_cf (cp := CP) SEGS B)
    malloc_cf (@cf_malloc_max CP) free_cf (@Wf_cf CP (as_universe B)) xs_cf LAWS pa_segs_low HENV OWNLOW WFL
    (alloc_model_laws_x_cf (cp := CP) B (universe_ok_of_ARcf (cp := CP) SEGS B ly S Hp W mem md (proj1 HAR)))
    (QMQ_cf (cp := CP) SEGS B) XSL AMALLOCx
    W E _ msC (@STK_padded prh_img_B) (spZ regs) [] ly S Hp W mem md [] ly S Hp mdC 0 (size + 16) (-48)
    (getr regs 2) (Z_to_bv 64 (BASE + 6664)) ch HSc (pdi_malloc B IMG) eq_refl HJc).
  - rewrite R10, E11, H11. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
  - lia.
  - exact HLIVE.
  - rewrite R2. reflexivity.
  - exact E2.
  - reflexivity.
  - reflexivity.
  - lia.
  - unfold ASTACK. apply Z.leb_le. vm_compute. reflexivity.
  - rewrite R3, E3. exact Hgp.
  - rewrite R4, E4. exact Htp.
  - exact R1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - exact HQMm.
  - apply (achain_chain_pre ly _ (spZ regs) (s0Z regs) ch).
    + apply (achain_kept ly (aview SEGS (w_H W) mem) _ (spZ regs) (s0Z regs) ch (spZ regs) Hch ltac:(lia) ltac:(lia)).
      intros a Ha. apply HJhic; lia.
    + rewrite Hsp1. lia.
    + exact Hs01.
    + rewrite Hra1. rewrite HBASE. unfold B_prog_base. lia.
  - (* the wrapper's text asks the trace ADMITTED by the universe at this state (the Univ form, P''); padded's trace
       is a FIXED trace (HTR: the closure's fifth clause, membership in u_fix), and a fixed trace is admitted at
       every state (YG01.v admits_fix, over universe_ok from the entry ARcf) *)
    unfold call_trace0. rewrite pd_trace_eq, Hra1, HBASE.
    apply (admits_fix (as_universe B) _ _
      (universe_ok_of_ARcf (cp := CP) SEGS B ly S Hp W mem md (proj1 HAR))).
    apply HTR. cbn. left. reflexivity. }
intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & res & -> & HJ2 & HP2 & Hres & Hfrs2 & HPREc & Htrc &
  (pM & trc & Hpath & Hgf & Hleaf & Hpiff & Hpaddr) & HARM & HMN2).
set (k2 := 0 + (st_nev S2 - st_nev S)) in *.
set (regsC := ms_regs msC) in *. set (memC := ms_mem msC) in *.
(* ---- the hull use: the call's one secondary-count step on its path (YGcfSecsStep.secs_malloc_step), as
   PresetHullBudget.v hull_used_of_call reads it ---- *)
assert (HHU : PresetHullBudget.hull_used S S2 [PresetReqAt.HMal (size + 16)])
  by exact (PresetHullBudget.hull_used_of_call (size + 16) S pM S2
             (YGcfSecsStep.secs_malloc_step _ _ S trc (pM, S2) Hpath)).
(* THE UNIV FORM's journal (P''): the wrapper's post journals the trace it stored (ajournal_xw .. [call_trace ..]). The
   trace is a FIXED one - the frame-0 case by HTR (the closure's fifth clause), the bare [pc0] case by
   prh_univ_closure's first conjunct - so it leaves the budget (YCbqG.v ajournal_xw_fix1) and the journal is the cut's
   ajournal_x again. *)
assert (HFIX : In (call_trace ly (pc_malloc_ra0 (as_code B)) regsC ch) (u_fix (as_universe B))).
{ apply call_trace_in.
  - exact (proj1 HUNIV RT_malloc).
  - unfold call_trace0. rewrite pd_trace_eq, Hra1, HBASE. apply HTR. cbn. left. reflexivity. }
apply (ajournal_xw_fix1 HFIX) in HJ2.
pose proof HJ2 as (HAR2 & Hly2 & _ & _ & _ & _ & _ & _ & HJhi2 & HJb2 & HJi2 & _).
assert (Hsub : forall bm, In bm (ablocks B ly S) -> In bm (ablocks B ly2 S2)).
{ destruct HARM as [(_ & -> & _) | (_ & -> & _)]; intros bm H; [exact H | apply in_or_app; left; exact H]. }
(* ---- the memory facts: the wrapper's keep, over the prologue's frame (HFk) ---- *)
assert (Hk1 : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (spZ regs + -48 - ASTACK <= a < spZ regs + -48) ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memC a)
  by (destruct HARM as [(_ & _ & (K & _) & _) | (_ & _ & (K & _))]; exact K).
assert (Hk3 : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memC a)
  by (destruct HARM as [(_ & _ & (_ & _ & K & _) & _) | (_ & _ & (_ & _ & K & _))]; exact K).
assert (KIMG : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) ->
  ~ (as_errno B <= a < as_errno B + 4) -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem a).
{ intros a Hi Ho He. rewrite (Hk3 a Hi Ho He). pose proof (Hsegs a Hi). apply HFk; unfold kLowMemEnd in *; lia. }
assert (KPST : forall a, Exists (in_zr a) PST -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem a)
  by (intros a Ha; exact (KIMG a (pdi_pst_ok B IMG a Ha) (pdi_pst_owned B IMG a Ha) (pdi_pst_errno B IMG a Ha))).
(* ---- the ledger and the own flag at the wrapper's return ---- *)
assert (HLED2 : prh_ledger (cp := CP) (PI := prh_img_B) (PA := PA) B ly2 S2 Hp W2 mem2 Lam peak cnt fail ran most own).
{ apply (prh_ledger_kept_aview B ly S Hp W mem ly2 S2 Hp W2 mem2 Lam peak cnt fail ran most own HLED KPST).
  - intros a k0 i Hin Hi.
    destruct (prh_ledger_hblock B ly S Hp W mem Lam peak cnt fail ran a k0 most own HLED Hin) as (Hk0 & Hblk & _).
    apply (HJb2 (a - cf_head) (k0 + cf_head) i Hblk (Hsub _ Hblk)).
    + change (@cf_head CP) with 16 in *. unfold req_size. destruct (Z.eqb_spec (k0 + 16) 0); lia.
    + apply inFP_nil.
  - intros a k0 _ H. exact (Hsub _ H).
  - apply Permutation_refl. }
(* ---- the source window: kept by the journal, then re-read at the new allocator state ---- *)
(* the image's zero-shadow ranges are whole granules: a conjunct of ARcf's symbol invariant (asyms_ok aso_zshadow) *)
assert (ZSAL : forall r, In r (as_zero_shadow B) -> fst r mod 8 = 0 /\ snd r mod 8 = 0).
{ intros r Hin. destruct (proj1 (Forall_forall _ _) (aso_zshadow _ (amc_syms _ _ _ _ _ (proj1 (proj1 HAR)))) r Hin)
    as (_ & _ & Z3 & Z4 & _). exact (conj Z3 Z4). }
assert (HHOME2 : 0 < size -> PRH_FnReader.prhReader_home B ly2 S2 Hp Lam data size)
  by (intros Hp0; exact (pd_home_grow ly S ly2 S2 Hp Lam data size Hsub (HHOME Hp0))).
assert (KSRC : forall a, data <= a < data + size -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem a).
{ intros a Ha. assert (Hp0 : 0 < size) by lia.
  destruct (pdh_home_place (cp := CP) B ly S Hp W mem Lam peak cnt fail ran most own data size HLED (HHOME Hp0) a Ha)
    as [(b & m & Hin & Hb) | (Hi & Hro & Ho & He)].
  - replace a with (b + (a - b)) by lia. apply (HJb2 b m (a - b) Hin (Hsub _ Hin)); [lia | apply inFP_nil].
  - apply HJi2; [exact Hi | exact Ho | exact He | intros Hps; exact (pdi_pst_rw B IMG a Hps Hro) |].
    apply fp_spares_closed. intros (r & Hr & _). destruct Hr. }
assert (HSRC2 : src_rd (PA := PA) W2 mem2 data x).
{ destruct (Z_lt_le_dec 0 size) as [Hp0 | Hp0].
  - exact (pdh_src_rd_at (cp := CP) B ARc LAWS pd1_img_band pd1_img_vis ZSAL ly2 S2 Hp W2 mem2 md2 Lam peak cnt fail
      ran most own W mem data x HAR2 HLED2 (HHOME2 Hp0) HSRC KSRC).
  - assert (Ex : x = []) by (destruct x; [reflexivity | cbn in size; subst size; lia]). subst x.
    destruct HSRC as (Hby & H4096 & Hc & Ham & Hra0 & _).
    split; [unfold bytes_at in *; apply (pdh_garr8_move W W2 mem mem2 data data [] Hby); intros j Hj; cbn in Hj; lia |].
    split; [exact H4096|]. split; [exact Hc|]. split; [exact Ham|].
    split; [apply range_addressable_nil; cbn; lia | intros Hn; cbn in Hn; lia]. }
(* ---- the arodata view ---- *)
assert (HROD2 : arodata_okP SEGS (@pa_relro_lo _ _ PA) (@pa_relro_hi _ _ PA) B (aview SEGS (w_H W2) mem2)).
{ intros a Hro Hn He. rewrite (KIMG a (HROimg a Hro) Hn He). exact (HROD a Hro Hn He). }
(* ---- the room ---- *)
assert (HPREcf : acall_pre_cf (cp := CP) SEGS B ly S Hp W regsC memC mdC ch)
  by exact (acall_pre_x_xs_cf (cp := CP) SEGS B _ _ _ _ _ _ _ _ HPREc).
assert (HRSEC : YGcfRoomLive.rl_sec_ok (cp := CP) (PresetLiveBounds.LSEC + PresetLiveBounds.DRV) S).
{ split; [exact HSEC|]. apply Z.ltb_lt. vm_compute. reflexivity. }
assert (HR24 : YGcfRoomLive.rl_b24_ok (PresetLiveBounds.L24 + PresetLiveBounds.DRV) S).
{ split; [exact HC24|]. apply Z.leb_le. vm_compute. reflexivity. }
assert (HROOM2 : room_live_cf S2).
{ exact (YGcfRoomLive.RL_malloc_step (cp := CP) SEGS B ly S Hp W regsC memC mdC ch
    (PresetLiveBounds.LSEC + PresetLiveBounds.DRV) (PresetLiveBounds.L24 + PresetLiveBounds.DRV) (size + 16) _ trc
    (pM, S2) HPREcf HRSEC HR24 HROOM Hpath). }
(* ---- the five saved words, read back at the wrapper's return (the call keeps [sp0 - 48, sp0)) ---- *)
assert (KFR : forall a, spZ regs - 48 <= a < spZ regs -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memC a).
{ intros a Ha. apply Hk1; [lia | unfold ASTACK; lia]. }
assert (HFW : forall off (k : nat) (rr : bv 5), -48 <= off -> off + 8 <= 0 ->
  In (YP09.mkChunk off (CVal 8 (SOff k 0)))
     [YP09.mkChunk (-40) (CVal 8 (SOff 19 0)); YP09.mkChunk (-32) (CVal 8 (SOff 18 0));
      YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0));
      YP09.mkChunk (-8) (CVal 8 (SOff 1 0))] ->
  (k < 32)%nat -> Z.of_nat k = bv_unsigned rr ->
  rdword (aview SEGS (w_H W2) mem2) (spZ regs + off) = Some (bv_unsigned (getr regs rr))).
{ intros off k rr Ho1 Ho2 Hc Hk Hr. rewrite <- Usp.
  apply (pd_frame_word E W W2 memC mem2 _ _ off k _ HMO eq_refl eq_refl Hc).
  - rewrite (EG k rr Hk Hr). reflexivity.
  - intros i Hi. apply KFR. rewrite Usp. lia. }
(* ---- 0x830d4 `mv s0, a0` (addi x8, x10, 0): one concrete step to PD_TEST ---- *)
pose proof (@pa_wx _ _ PA) as Hwx.
assert (EO : PD_OFF = 6620) by reflexivity.
assert (Hfetch : fetch_word SEGS (Z_to_bv 64 (pd_pc PD_RETM)) = Some (Z_to_bv 32 0x50413)).
{ apply pa_fetch_ok.
  pose proof (pi_check_lookup asym (clookup (@pa_tbl _ B_prog_listing PA)) VAL SIGMA B_prog_listing (PD_OFF + PD_RETM)
    (PW 0x50413) (@pa_cert _ B_prog_listing PA) ltac:(vm_compute; reflexivity)) as Hck.
  unfold pi_slot_check in Hck. unfold pd_pc. rewrite <- Z.add_assoc.
  destruct (clookup (@pa_tbl _ B_prog_listing PA) (BASE + (PD_OFF + PD_RETM))) as [wz|] eqn:Hl; [|discriminate Hck].
  apply Z.eqb_eq in Hck. subst wz. reflexivity. }
assert (Hdec : decode_any (Z_to_bv 32 0x50413) = Some (OpImm ALU_ADD 8%bv 10%bv (Z_to_bv 12 0), 4%Z))
  by vm_refl_bv.
assert (Hec : is_ecall (Z_to_bv 32 0x50413) = false) by (vm_compute; reflexivity).
assert (Epc : BASE + 6664 = pd_pc PD_RETM) by (unfold pd_pc, PD_RETM; rewrite EO; lia).
rewrite Epc.
eapply (SRr_step SEGS Hwx W2); [reflexivity | |].
{ rewrite restrict_mkst_fx.
  apply (step_addi_at SEGS _ _ _ _ _ _ _ _ (getr regs2 10%bv) Hfetch Hec Hdec); [reflexivity |].
  unfold v_addi. change (bv_signed (Z_to_bv 12 0)) with 0. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
intros md' Hs. cbn [ms_mem mkst]. rewrite unrestrict_mkst_mrestrict.
assert (Ept : v_addi (Z_to_bv 64 (pd_pc PD_RETM)) 4 = Z_to_bv 64 (pd_pc PD_TEST)).
{ unfold v_addi. rewrite unsigned_lit_small by (unfold pd_pc, PD_RETM; rewrite EO, HBASE; unfold B_prog_base; lia).
  f_equal. unfold pd_pc, PD_RETM, PD_TEST. lia. }
rewrite Ept.
set (regs3 := regupd regs2 8%bv (getr regs2 10%bv)).
(* the cut's entry data D given explicitly: pd_post D is the text's post by conversion, which unification cannot
   invert through the record projections *)
apply (PS2 IMG (mkPdIn ly S Hp W regs mem md ch data fill x Lam peak cnt fail ran most own) ly2 S2 Hp W2 regs3 mem2 md'
  k2 res).
assert (HP2' : forall r, acallee_saved r -> getr regs2 (Z_to_bv 5 r) = getr regsC (Z_to_bv 5 r)) by exact HP2.
assert (G3 : forall r : bv 5, r <> 8%bv -> getr regs3 r = getr regs2 r) by (intros r Hr; apply getr_other; exact Hr).
unfold pd_at_test, pd_base, pd_regsat, pd_saved, pd_sp0, pd_size, pd_J, pd_mn.
cbn [din_ly din_S din_Hp din_W din_regs din_mem din_md
  din_ch din_data din_fill din_x din_Lam din_peak din_cnt din_fail din_ran din_most din_own].
split.
{ (* ---- pd_base ---- *)
  split; [exact Hra|].
  split.
  { rewrite (same_but_materialized_wvb md2 md' Hs).
    apply (ajournal_x_materialize (SK := SK) SEGS B PST ARc LAWS Hsegs). exact HJ2. }
  split.
  { repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
      replace (spZ regs - 48 + 40) with (spZ regs + -8) by lia;
      replace (spZ regs - 48 + 32) with (spZ regs + -16) by lia;
      replace (spZ regs - 48 + 24) with (spZ regs + -24) by lia;
      replace (spZ regs - 48 + 16) with (spZ regs + -32) by lia;
      replace (spZ regs - 48 + 8) with (spZ regs + -40) by lia.
    - apply (HFW (-8) 1%nat 1%bv); [lia | lia | cbn; tauto | lia | reflexivity].
    - apply (HFW (-16) 8%nat 8%bv); [lia | lia | cbn; tauto | lia | reflexivity].
    - apply (HFW (-24) 9%nat 9%bv); [lia | lia | cbn; tauto | lia | reflexivity].
    - apply (HFW (-32) 18%nat 18%bv); [lia | lia | cbn; tauto | lia | reflexivity].
    - apply (HFW (-40) 19%nat 19%bv); [lia | lia | cbn; tauto | lia | reflexivity]. }
  split.
  { split; [rewrite G3 by reg_neq_tac; transitivity (getr regsC 2%bv);
      [exact (HP2' 2 ltac:(unfold acallee_saved; lia)) | rewrite R2, Usp; unfold w64; f_equal; lia] |].
    split; [unfold regs3; rewrite getr_same by reg_neq_tac; exact Hres |].
    split; [rewrite G3 by reg_neq_tac; transitivity (getr regsC 9%bv);
      [exact (HP2' 9 ltac:(unfold acallee_saved; lia)) | rewrite R9, (EG 12%nat 12%bv ltac:(lia) eq_refl); exact H12] |].
    split; [rewrite G3 by reg_neq_tac; transitivity (getr regsC 18%bv);
      [exact (HP2' 18 ltac:(unfold acallee_saved; lia)) | rewrite R18, E11; exact H11] |].
    split; [rewrite G3 by reg_neq_tac; transitivity (getr regsC 19%bv);
      [exact (HP2' 19 ltac:(unfold acallee_saved; lia)) | rewrite R19, (EG 10%nat 10%bv ltac:(lia) eq_refl); exact H10] |].
    split; [rewrite G3 by reg_neq_tac; transitivity (getr regsC 3%bv);
      [exact (HP2' 3 ltac:(unfold acallee_saved; lia)) | rewrite R3, E3; reflexivity] |].
    split; [rewrite G3 by reg_neq_tac; transitivity (getr regsC 4%bv);
      [exact (HP2' 4 ltac:(unfold acallee_saved; lia)) | rewrite R4, E4; reflexivity] |].
    intros r Hr.
    assert (Hne : Z_to_bv 5 r <> 8%bv).
    { intros Hc. apply (f_equal bv_unsigned) in Hc. rewrite Z_to_bv_unsigned in Hc.
      change (bv_unsigned (8%bv : bv 5)) with 8 in Hc. unfold bv_wrap in Hc. change (bv_modulus 5) with 32 in Hc.
      rewrite Z.mod_small in Hc by lia. lia. }
    rewrite (G3 _ Hne), (HP2' r ltac:(unfold acallee_saved; lia)).
    assert (Hcase : r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    destruct Hcase as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]].
    - transitivity (ew E 20); [exact R20 | exact (EG 20%nat (Z_to_bv 5 20) ltac:(lia) ltac:(reflexivity))].
    - transitivity (ew E 21); [exact R21 | exact (EG 21%nat (Z_to_bv 5 21) ltac:(lia) ltac:(reflexivity))].
    - transitivity (ew E 22); [exact R22 | exact (EG 22%nat (Z_to_bv 5 22) ltac:(lia) ltac:(reflexivity))].
    - transitivity (ew E 23); [exact R23 | exact (EG 23%nat (Z_to_bv 5 23) ltac:(lia) ltac:(reflexivity))].
    - transitivity (ew E 24); [exact R24 | exact (EG 24%nat (Z_to_bv 5 24) ltac:(lia) ltac:(reflexivity))].
    - transitivity (ew E 25); [exact R25 | exact (EG 25%nat (Z_to_bv 5 25) ltac:(lia) ltac:(reflexivity))].
    - transitivity (ew E 26); [exact R26 | exact (EG 26%nat (Z_to_bv 5 26) ltac:(lia) ltac:(reflexivity))].
    - transitivity (ew E 27); [exact R27 | exact (EG 27%nat (Z_to_bv 5 27) ltac:(lia) ltac:(reflexivity))]. }
  split; [exact Hgp|]. split; [exact Htp|]. split; [exact HROD2|].
  split; [intros Hm; exact (HMN2 (HPM Hm))|]. split; [reflexivity|]. split; [exact HLED2|].
  split; [exact HROOM2|]. split; [exact HSRC2|]. split; [exact HHOME|]. split; [subst size; lia | exact HHU]. }
split; [unfold regs3; rewrite G3 by reg_neq_tac; exact Hres|].
(* ---- the two outcomes ---- *)
destruct (Z.eq_dec res 0) as [Hr0 | Hr0].
- (* REFUSED: the wrapper's NULL *)
  left. split; [exact Hr0|].
  destruct HARM as [(_ & Eab2 & _ & Herr & _) | (H4096 & _)]; [|lia].
  assert (HpN : pM = PNull) by (apply Hpiff; exact Hr0). subst pM.
  (* the kit's OUTCOME clause on this arm: at a CONSUMER position whose next event is this raw malloc the NULL cannot
     happen. The call is made at the entry allocator state S (the prologue makes no allocator step), the position is
     held there, and the wrapper's text gave the NULL on a GRANTED path (Hpath / Hgf): PRH_Refute.prh_refute_at. *)
  assert (HDEAD : pd_dead (mkPdIn ly S Hp W regs mem md ch data fill x Lam peak cnt fail ran most own)).
  { unfold pd_dead, pd_size. cbn [din_S din_x].
    intros sm x0 os i H0 hist Hpos Hrun Hcons. apply prh_run_at_one in Hrun.
    destruct (YGcfRoomLive.rl_of_acall_pre_cf (cp := CP) _ _ _ _ _ _ _ _ _ _ HPREcf) as (W0 & _).
    refine (PRH_Refute.prh_refute_at (cp := CP) _ sm x0 os i _ _ H0 hist S Hcons _ Hrun eq_refl Hpos W0 _).
    - cbn [length]. lia.
    - left. do 4 eexists. split; [exact Hpath | exact Hgf]. }
  split; [|exact HDEAD].
  unfold pd_nullblk. cbn [din_ly din_S].
  split; [exact Eab2|].
  split.
  { (* P0's position: no event, so the position the caller holds at the entry is kept *)
    intros sm x0 os i H0 hist Hpos _. exists hist. cbn [length]. rewrite Nat.add_0_r.
    eapply PresetRoomPosKeep.room_pos_keep_alloc_null; [exact HPREcf | idtac | exact HLIVE | exact HFIX
      | exact Hpath | exact Hpos]; lia. }
  split; [exact Herr|].
  exists ly, S, Hp, W, regsC, memC, mdC, W2,
    (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + 6664)) mem2 (seg_rom SEGS)) md2).
  exact (malloc_cf_null_post_of_leaf SEGS B ly S Hp W regsC memC mdC (size + 16) ch _ trc S2 W2 _ HPREcf Hpath Hgf
    (malloc_leaf_x_xs_cf (cp := CP) SEGS B _ _ _ _ _ _ _ _ _ _ _ Hleaf)).
- (* OK: a fresh raw block of size + 16 *)
  right. destruct HARM as [(Hr0' & _) | (H4096 & Eab2 & _)]; [lia|].
  assert (HpN : pM <> PNull) by (intros E0; apply Hr0; apply Hpiff; exact E0).
  assert (Hin2 : In (res, size + 16) (ablocks B ly2 S2)) by (rewrite Eab2; apply in_or_app; right; left; reflexivity).
  destruct (alx_blocks SEGS B ARc LAWS ly2 S2 Hp W2 mem2 md2 res (size + 16) HAR2 Hin2)
    as (Hal_r & _ & Hbc & Happ & Hpr & Hpw).
  assert (Rq : req_size (size + 16) = size + 16) by (unfold req_size; destruct (Z.eqb_spec (size + 16) 0); lia).
  rewrite Rq in Hbc, Happ. rewrite Eab2 in Hpw.
  pose proof (prh_ablocks_nonneg_cf B ly S Hp W mem md (proj1 HAR)) as Hnn.
  assert (Hfresh : ~ In res (map fst (ablocks B ly S)))
    by exact (pd_new_block (ablocks B ly S) (res, size + 16) Hnn ltac:(cbn; lia) Hpw).
  assert (HLamb : forall a k0, In (a, k0) Lam -> a - @cf_head CP <> res).
  { intros a k0 Hin Ea. destruct (prh_ledger_hblock B ly S Hp W mem Lam peak cnt fail ran a k0 most own HLED Hin) as (_ & Hblk & _).
    apply Hfresh. rewrite <- Ea. exact (in_map fst _ _ Hblk). }
  assert (HnHp : ~ In res Hp).
  { intros Hin. pose proof HLED as (_ & _ & _ & Hperm). apply (Permutation_in _ Hperm) in Hin.
    apply in_map_iff in Hin as ((a, k0) & Ea & Hin). exact (HLamb a k0 Hin Ea). }
  assert (Hhd : hd_skip (cp := CP) Hp res = 0).
  { unfold hd_skip. destruct (existsb (Z.eqb res) Hp) eqn:Ee; [|reflexivity]. exfalso.
    apply existsb_exists in Ee as (y & Hy & Hyy). apply Z.eqb_eq in Hyy. subst y. exact (HnHp Hy). }
  destruct (AR_shadow_law_ok_cf_al SEGS B ly2 S2 Hp W2 mem2 md2 res (size + 16) (proj1 HAR2) Hin2
    ltac:(rewrite Hhd; reflexivity)) as [Hbs Hhv].
  rewrite Hhd, Rq, Z.add_0_r, Z.sub_0_r in Hbs. rewrite Rq in Hhv.
  split; [|split].
  + unfold pd_okblk, pd_size.
    cbn [din_own din_ly din_S din_Lam din_x].
    split; [exact Hr0|]. split; [reflexivity|]. split; [exact H4096|]. split; [lia|]. split; [exact Hfresh|].
    split; [rewrite Eab2; apply Permutation_sym, Permutation_cons_append|].
    split; [exact HLamb|].
    split; [intros a Ha; apply (apresent_writable SEGS); destruct (Hpr a ltac:(rewrite Rq; lia)) as [Hpa _]; exact Hpa|].
    split; [eapply (block_shadow_range _ SHADOW_OFF res (size + 16) res (size + 16) Hbs); lia|].
    split; [exact Hhv|].
    (* P1's position: the run's next event is the copy's raw malloc, so it advances by one *)
    intros sm x0 os i H0 hist Hpos Hrun. apply prh_run_at_one in Hrun. exists hist. cbn [length].
    replace (i + 1)%nat with (Datatypes.S i) by lia.
    eapply PresetRoomPosKeep.room_pos_keep_alloc; [exact HPREcf | idtac | exact HLIVE | exact HFIX | exact Hpath
      | exact HpN | exact Hpos | exact Hrun]; lia.
  + exact HnHp.
  + unfold pd_src_apart, pd_size. cbn [din_data din_x].
    assert (PT : forall a, data <= a < data + size -> 0 <= a < alloc_ceiling /\ ~ (res <= a < res + size + 16)).
    { intros a Ha. pose proof HSRC as (_ & Hd4096 & Hdc & _).
      split; [lia|]. intros Hra'. assert (Hp0 : 0 < size) by lia.
      destruct (pdh_home_place (cp := CP) B ly S Hp W mem Lam peak cnt fail ran most own data size HLED (HHOME Hp0) a Ha)
        as [(b & m & Hin & Hb) | (Hi & _)].
      - destruct (pd_old_apart (ablocks B ly S) (res, size + 16) (b, m) Hpw Hin) as [D1|D1];
          cbn [fst snd] in D1; try rewrite Rq in D1; lia.
      - exact (blk_img_x SEGS B ARc LAWS ly2 S2 Hp W2 mem2 md2 res (size + 16) a HAR2 Hin2
          ltac:(rewrite Rq; lia) Hi). }
    split; [|exact PT].
    destruct (Z_lt_le_dec 0 size) as [Hp0|Hp0]; [|lia].
    destruct (Z_le_gt_dec (data + size) res) as [L1|L1]; [left; exact L1|].
    destruct (Z_le_gt_dec (res + size) data) as [L2|L2]; [right; exact L2|].
    exfalso. destruct (PT (Z.max data res) ltac:(lia)) as [_ Hn]. apply Hn. lia.
Qed.
End s1.
