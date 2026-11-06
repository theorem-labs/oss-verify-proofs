(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: SEGMENT TAIL of the ASan walk of fuzz_reply's relay_instance_gone
   (fuzz_reply.asan 0x82fa4 .. 0x83094), the statement W_relay_instance_gone_cx.v rig_tail_stmt: from the cut RGU
   (every entry done, g_lock held) to rig_post.  In the form of lib/A/W_relay_remove.v (the fd < 0 arm: the flag
   store, the return) and lane W7's lib/A/W_drain_epi.v (a fresh symbolic state seated at a cut).

   0x82fa4  a0 = &g_lock; jal pthread_mutex_unlock        (seat 1: no region; W_sites_x.v aunlock_realizes_x lifted by
                                                           aj_gx_entry_at_x: the lock word 16 -> 0)
   0x82fb0  the frame's release: the retired magic at F, the 16 shadow bytes of F := 0xf5, *FL = 0 (the flag store
            that frees the class-1 fake frame, W_frame_x.v aj_flag_store_pi_x), j 0x83058; the epilogue (13 loads from
            s0 - 104 .., sp = s0) and ret                 (seat 2: the frame slots at s1 + 16 / + 24, the saved
                                                           registers at s0 - 104 .., F with its flag word, F's
                                                           shadow at s5, the flag cell; every address an atom)
   The tail writes only g_lock + 4 .. + 8, unlock's scratch below sp, F + 0 .. + 8, F's shadow and the flag cell,
   so every byte the table, the output stream and the sources are represented over is kept (the cx premises HRGP /
   HRGI place the globals; the blocks are apart from the frame, its shadow and its flag by the allocator's laws).
   ROUTE (b), STEP 3 (CONVERSION.md (sha256 1015972e02a9; internal record); the RIG_x round): over any allocator relation
   ARx with its laws and the room record RP, at W_relay_instance_gone_cx.v's generic Section c (its list copied
   verbatim).  The journal is ajournal_gx_x from the entry's head set to the cut's Hp1, which the unlock and the
   release keep; rig_post_x's room `rp_RM RP S' kr` is gbud's room at the empty remaining trace (grest at |es|),
   through the release by RPF_stack_free.  The AR-free helpers below (tinb .. tl_kept_trans) keep their statements;
   W_rig_top.v uses them. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_syms W_listing W_pl W_kit W_contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI00 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep gestures_end_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require relay_remove_b_c relay_instance_gone_b_c drain_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require RelayModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_frame W_journal W_sites W_rep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG YGcallx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_journal_x W_sites_x W_contract_x W_frame_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_relay_instance_gone_cx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_contract_xR_relay.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).

(* ---- The two seats.  SEAT 1 at 0x82fa4 (RGU's pc): no region (the three instructions to the call touch no
   memory).  SEAT 2 at 0x82fb0 (the return of pthread_mutex_unlock): the extra atoms 32 .. 44 are the caller's
   thirteen saved registers (RIG_SAVED), 45 is F, 46 is FL; s0 (atom 8) is the entry sp, s1 (atom 9) is sp, s5
   (atom 21) is F's shadow. ---- *)
Definition A_rt_rel : Z := A_rig_unlock + 12.          (* 0x82fb0 *)
Definition ss_rt0 : sstate := mkSS A_rig_unlock sr_atoms [] None (mkFacts [] [] []).
Definition rt_regions : smem :=
[ YP09.mkRegion (Some 46%nat) 0 1 0 1 [];
  fframe_region 45 46 1 [];
  fshadow_region 21 1 0 16 [];
  YP09.mkRegion (Some 9%nat) 16 32 16 16
    [YP09.mkChunk 16 (CVal 8 (SOff 45 0)); YP09.mkChunk 24 (CVal 8 (SOff 45 0))];
  YP09.mkRegion (Some 8%nat) (-104) 0 (-104) (-104)
    (map (fun i => YP09.mkChunk (-104 + 8 * Z.of_nat i) (CVal 8 (SOff (32 + i) 0))) (seq 0 13)) ].
Definition rt_facts : facts := mkFacts [ (45%nat, HPTR 5); (46%nat, HPTR 0) ] [] [].
Definition ss_rt : sstate := mkSS A_rt_rel sr_atoms rt_regions None rt_facts.
Definition rt_extra (regsE : bvmap 5 word) (F FL : Z) : list word :=
map (getr regsE) RIG_SAVED ++ [Z_to_bv 64 F; Z_to_bv 64 FL].
Lemma nth_rt_extra : forall regsE F FL i, (i < 13)%nat ->
nth i (rt_extra regsE F FL) (Z_to_bv 64 0) = getr regsE (nth i RIG_SAVED 0%bv).
Proof.
intros regsE F FL i Hi. unfold rt_extra. rewrite app_nth1 by (rewrite length_map; cbn; lia).
rewrite (nth_indep _ _ (getr regsE 0%bv)) by (rewrite length_map; cbn; lia). rewrite List.map_nth. reflexivity.
Qed.

Lemma rt_entry0 : forall (W : world SEGS) regs mem,
st_ok_pi SEGS VAL (Eimg (Ereg regs [])) ss_rt0
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_rig_unlock)) mem (seg_rom SEGS))).
Proof.
intros W regs mem. rewrite restrict_mkst_fx. unfold ss_rt0. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor.
- cbn [pairwise_disjoint]. exact I.
- split; [exact I | split; [exact I | exact I]].
Qed.

Lemma rt_entry : forall (W : world SEGS) regsX memX regsE F FL,
bv_unsigned (getr regsX 9) = spZ regsX -> bv_unsigned (getr regsX 8) = spZ regsX + 224 ->
getr regsX 21 = w64 (shadow_addr F) ->
alloc_ceiling <= spZ regsX -> spZ regsX + 224 <= 2 ^ 47 ->
4096 <= F -> F + 128 <= alloc_ceiling -> F mod 32 = 0 -> in_app F 128 ->
4096 <= FL < alloc_ceiling -> ~ (F <= FL < F + 128) -> ~ (shadow_addr F <= FL < shadow_addr F + 16) ->
(forall o, 0 <= o < 128 -> apresent (w_H W) memX (F + o)) ->
(forall o, 0 <= o < 16 -> apresent (w_H W) memX (shadow_addr F + o)) ->
apresent (w_H W) memX FL ->
val_mem SEGS (mrestrict (w_H W) memX) (F + 120) 8 FL ->
val_mem SEGS (mrestrict (w_H W) memX) (spZ regsX + 16) 8 F ->
val_mem SEGS (mrestrict (w_H W) memX) (spZ regsX + 24) 8 F ->
(forall i, (i < 13)%nat ->
 val_mem SEGS (mrestrict (w_H W) memX) (spZ regsX + 120 + 8 * Z.of_nat i) 8
   (bv_unsigned (getr regsE (nth i RIG_SAVED 0%bv)))) ->
st_ok_pi SEGS VAL (Eimg (Ereg regsX (rt_extra regsE F FL))) ss_rt
(restrict (w_H W) (mkst regsX (Z_to_bv 64 (BASE + A_rt_rel)) memX (seg_rom SEGS))).
Proof.
intros W regsX memX regsE F FL H9 H8 H21 Hlo Hhi HF4 HFc HFal HFapp HFL HFLF HFLS HPF HPS HPL V120 V16 V24 VSV.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regsX (rt_extra regsE F FL))).
assert (EL : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsX r)
by (intros n r Hn; subst E; pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5;
rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
assert (E45 : ew E 45 = Z_to_bv 64 F)
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsX _ 13)).
assert (E46 : ew E 46 = Z_to_bv 64 FL)
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsX _ 14)).
assert (EX : forall i, (i < 13)%nat -> ew E (32 + i) = getr regsE (nth i RIG_SAVED 0%bv)).
{ intros i Hi. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite ew_Ereg_extra. exact (nth_rt_extra regsE F FL i Hi). }
assert (HF8 : F = 8 * (F / 8) + F mod 8) by (apply Z.div_mod; lia).
pose proof (Z.mod_pos_bound F 8 ltac:(lia)) as HF8m.
assert (SF : shadow_addr F = 2147450880 + F / 8) by (unfold shadow_addr, SHADOW_OFF; lia).
assert (U9 : bv_unsigned (ew E 9) = spZ regsX) by (rewrite (EL 9%nat 9%bv eq_refl); exact H9).
assert (U8 : bv_unsigned (ew E 8) = spZ regsX + 224) by (rewrite (EL 8%nat 8%bv eq_refl); exact H8).
assert (U21 : bv_unsigned (ew E 21) = shadow_addr F)
by (rewrite (EL 21%nat 21%bv eq_refl), H21; unfold w64; apply unsigned_lit_small; lia).
assert (U45 : bv_unsigned (ew E 45) = F) by (rewrite E45; apply unsigned_lit_small; lia).
assert (U46 : bv_unsigned (ew E 46) = FL) by (rewrite E46; apply unsigned_lit_small; lia).
unfold ss_rt, A_rt_rel. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold rt_regions, fframe_region, fshadow_region. change (fs_frame_bytes 1) with 128. change (128 / 8) with 16.
  repeat apply Forall_cons; try apply Forall_nil.
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U46.
    split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). replace (FL + o) with FL by lia. exact HPL.
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val app]. rewrite U45.
    split; [lia|]. split; [lia|]. split.
    * intros o Ho. apply (apresent_writable SEGS). exact (HPF o Ho).
    * apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ F (128 - 8) 8 _ FL);
      [cbn [sv_denot]; rewrite E46, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      replace (F + (128 - 8)) with (F + 120) by lia. exact V120.
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U21.
    split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). exact (HPS o Ho).
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    * apply (chunk_ok_val SEGS E _ (spZ regsX) 16 8 _ F);
      [cbn [sv_denot]; rewrite E45, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V16].
    * apply (chunk_ok_val SEGS E _ (spZ regsX) 24 8 _ F);
      [cbn [sv_denot]; rewrite E45, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V24].
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U8.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_map. apply Forall_forall. intros i Hi. apply in_seq in Hi. cbn [Nat.add] in Hi.
    apply (chunk_ok_val SEGS E _ (spZ regsX + 224) (-104 + 8 * Z.of_nat i) 8 _ (bv_unsigned (getr regsE (nth i RIG_SAVED 0%bv)))).
    * cbn [sv_denot]. rewrite (EX i ltac:(lia)). rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    * pose proof (bv_unsigned_in_range 64 (getr regsE (nth i RIG_SAVED 0%bv))) as R. change (bv_modulus 64) with (2 ^ 64) in R. zside.
    * zside.
    * replace (spZ regsX + 224 + (-104 + 8 * Z.of_nat i)) with (spZ regsX + 120 + 8 * Z.of_nat i) by lia. exact (VSV i ltac:(lia)).
- apply pairwise_disjoint_of_extents.
  unfold rt_regions, fframe_region, fshadow_region, extent_of_region. change (fs_frame_bytes 1) with 128. change (128 / 8) with 16.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U46, U45, U21, U9, U8.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp. rewrite SF in *.
  revert HF4 HFc HFapp HFL HFLF HFLS Hlo Hhi HF8 HF8m C1. clear. intros.
  repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [rt_facts f_atoms atoms_ok]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
  rewrite U45, U46. change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
  revert HF4 HFc HFL HFal C1. clear. intros. repeat match goal with |- _ /\ _ => split end; (exact I || lia).
Qed.

Section c.
Variable B : asyms.
(* the program statics of the generic journal (YCbqG.ajournal_x's image clause exempts them) *)
Variable PST : list (Z * Z).
(* the allocator relation, its third argument the head set Hp *)
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable MT : ameter_ops.
(* the room round (ROOM-TEXTS.md v3 sha256 767baa12f13c; internal record): the allocator's room invariant and the live counts, after MT *)
Variable RP : roomp.
Variable MMAX : Z.
Variable RG : rep_globals.
(* the free interceptor's caller-context table (K0_SITES' CTX_AFREE) *)
Variable CTX_AFREE : list (list Z).
Context {hl : Z}.
(* ---- The Section hypotheses every segment file copies (the names are the contracts'): W_relay_instance_gone_cx.v
   Section c's list, verbatim (its literals' facts at the cx's glit_at_x).  Each is either the AR walk's (AR-free,
   verbatim), its _x twin, or an instance fact that the instance supplies where RIG_x is plugged (top_x); the AR
   re-derivation was deleted (W_relay_instance_gone.v's header says why). ---- *)
(* the instance's laws, over ARx *)
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
(* no hidden head in any ARx state (a Theorem Labs lane's HP0 ruling; W_journal_x.v range_addressable_of_block_hp0_x) *)
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis MLAW : ameter_laws MT.
(* the frame twins' hypotheses (W_frame_x.v), in place of ML / SMP: the image cover IMGC (frm_off_imgP_x); a live
   block's size is non-negative (W_kit_x.v's BLKN); the owned-low law OWNLOW, the model invariant WFx with its law WFL,
   and the two facts the twins read off model_laws / stack_malloc_progressP (SFREE, SMALLOC) *)
Hypothesis IMGC : forall ly S Hp W mem md, ARx ly S Hp W mem md ->
fst (ly_img ly) <= 0x10000 /\ 0x5fb000 <= fst (ly_img ly) + snd (ly_img ly).
Hypothesis BLKN : forall ly S Hp W mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.
Hypothesis OWNLOW : ARx_owned_low_law SEGS B ARx.
Variable WFx : astate -> Prop.
Hypothesis WFL : ARx_wf_law SEGS ARx WFx.
Hypothesis SFREE : forall s cid pos, WFx s -> In (cid, pos) (frames s) ->
exists l1 l2, frames s = l1 ++ (cid, pos) :: l2 /\ frames (stack_free_state cid pos s) = l1 ++ l2.
Hypothesis SMALLOC : forall s cid, WFx s -> 0 <= cid <= 10 -> count_cid cid (frames s) < fs_frames cid ->
exists pos s', apath (stack_malloc cid s) [] (PFake cid pos, s') /\ (exists f, s' = set_fs f s) /\
frames s' = (cid, pos) :: frames s /\ ~ In (cid, pos) (frames s).
(* the fake frame's laws over ARx: __asan_stack_malloc_1 (class 1), the release's flag store and frame free *)
Hypothesis ASMP : astack_malloc_pres_x SEGS B ARx 1.
Hypothesis ASF : astack_free_law_x SEGS B ARx.
Hypothesis FFL : frame_flag_lawP_x SEGS B ARx.
(* the meter does not charge the fake frame's seat or its release, both a set_fs of the state (W8's ruling, KF-COUNT
   #4: the old text over an ablocks equation is false at the count meter) *)
Hypothesis MO_FR : forall s f, mo_le MT s (set_fs f s) 0.
Hypothesis HGRIG : gx_ok SEGS B (G_RIG B RG).
(* the register images of g_nsrc / g_src: the auipc's of 0x82d58 (kept at 72(sp), listing A_HI 44) and 0x82d74
   (s6, A_HI 45).  The abstract placement does not fix them against the objects (W_rebase.v:7-15); PB_fr discharges
   both by vm_compute, as W_send_line_cx.v's HH17 .. HH24. *)
Hypothesis HH44 : VAL (A_HI 44) = rg_nsrc RG + RIG_HI_NSRC.
Hypothesis HH45 : VAL (A_HI 45) = rg_src RG + RIG_HI_SRC.
(* the relay's and the output's global cells are pairwise apart, and errno with them; the four that neither rg_place
   nor gx_ok places are image bytes (so apart from the frames, the fake frame's shadow and the stack).  The pinned
   placement decides both by vm_compute at fr_globals, as W7's W_drain_cx.v HRGD / HGSB. *)
Hypothesis HRGP : zpairwise_disjoint
[(rg_lock RG, rg_lock RG + 12); (rg_s RG, rg_s RG + 4 * ASRC); (rg_src RG, rg_src RG + 8);
 (rg_nsrc RG, rg_nsrc RG + 4); (rg_capsrc RG, rg_capsrc RG + 4); (rg_send_max RG, rg_send_max RG + 8);
 (rg_nout RG, rg_nout RG + 8); (rg_capout RG, rg_capout RG + 8); (rg_out RG, rg_out RG + 8);
 (rg_client RG, rg_client RG + 4); (rg_client_broken RG, rg_client_broken RG + 1);
 (rg_send_dead RG, rg_send_dead RG + 1); (rg_send_eintr RG, rg_send_eintr RG + 1); (rg_wake RG + 4, rg_wake RG + 8);
 (as_errno B, as_errno B + 4)].
Hypothesis HRGI : forall a,
(rg_capsrc RG <= a < rg_capsrc RG + 4 \/ rg_send_max RG <= a < rg_send_max RG + 8 \/
 rg_client RG <= a < rg_client RG + 4 \/ rg_send_dead RG <= a < rg_send_dead RG + 1) ->
in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B).
(* no read-only image byte is owned by the runtime (W_gesture_end.v's HROMO form): rom_view survives the stack
   allocator's calls (W_journal_x.v ajournal_gx_rom_view_x) *)
Hypothesis HROMO : rom_out SEGS B (G_RIG B RG).
(* the allocator instance's granule-tail fact (W7's ALLOC_TAIL over ARx, as W_drain_cx_x.v states it; there a theorem
   of the laws, alloc_tail_x): a held key is represented over its |text| + 1 bytes (ruling (A)); a word read of a
   key to the end of its last granule is visible *)
Hypothesis ALLOC_TAIL : forall ly S Hp W mem md p n a,
ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) ->
p + req_size n - 1 < a < p + req_size n - 1 - (p + req_size n - 1) mod 8 + 8 ->
aview SEGS (w_H W) mem a <> None.
(* the runtime entries relay_instance_gone calls, at their SIGMA pcs, over ARx (W_sites_x.v / W_contract_x.v /
   W_journal_x.v Section hc; the free rule at the room record RP).  snprintf: a Theorem Labs lane's statement at fuzz_reply's
   addresses (W_sites.v asnprintf_realizes, its twin W_sites_x.v asnprintf_realizes_x), which the snprintf chain
   (commit 9067b7156f9, lib/A/RT_pf_vf.v snprintf_chain_ok, through a Theorem Labs lane's evt -> SRr bridge) discharges. *)
Hypothesis ALOCK : alock_realizes_x B ARx (SIGMA WS_pthread_mutex_lock).
Hypothesis AUNLOCK : aunlock_realizes_x B ARx (SIGMA WS_pthread_mutex_unlock).
Hypothesis AFREE : afree_cf_rule_c_x SEGS B PST ARx MT RP CTX_AFREE.
Hypothesis ASNPRINTF : asnprintf_realizes_x B ARx (SIGMA WS_snprintf) FR_GOT_GUARD FR_GUARD.
Hypothesis ASTRLEN : astrlen_realizes_x B ARx (SIGMA WS_strlen).
Hypothesis ASTRNCMP : astrncmp_realizes_x B ARx (SIGMA WS_strncmp).
(* the program functions relay_instance_gone calls (W7's drain, W4's gesture_end), by their published _x room specs *)
Hypothesis DRAIN : dr_spec_x B PST ARx MT RP MMAX RG (BASE + AF_fr_drain).
Hypothesis GE : ge_spec_x B PST ARx MT RP MMAX RG (BASE + AF_fr_gesture_end).
(* the bytes of " end\0" (.str.4, read-only .rodata), which gse_spec's / ge_spec's premise garr8 (VAL A_lit_end5)
   (bzs END5) needs with rom_view (no zero-shadow fact: the literal's last shadow granule is partial): k3's HEND5L, verbatim (W_drain_cx.v dlit_at form; PB_fr
   by vm_compute) *)
Hypothesis HEND5L : forall k, (k < 5)%nat -> YG0d.in_rom SEGS (VAL A_lit_end5 + Z.of_nat k) /\
  seg_rom SEGS (Z_to_bv 64 (VAL A_lit_end5 + Z.of_nat k)) = nth_error END5 k.
(* snprintf's stack-protector cells (see the header): the GOT word, a fact of every ARx state (at ARi0: the AR fact
   of lib/A/AE22.v got_canary_of_AR); the canary, image bytes *)
Hypothesis HGOTG : forall ly S Hp W mem md, ARx ly S Hp W mem md ->
  rdword (aview SEGS (w_H W) mem) FR_GOT_GUARD = Some FR_GUARD.
(* the canary's bytes are image bytes (seg_rom SEGS at FR_GUARD .. + 8 is Some 0), so aview reads them in EVERY state
   through mbyte's seg_rom fallback: aguard_ok's second half needs nothing carried (a Theorem Labs lane's ruling; a Theorem Labs lane's
   pin measurement).  PB_fr decides it by vm_compute. *)
Hypothesis HCANR : forall a, FR_GUARD <= a < FR_GUARD + 8 -> seg_rom SEGS (Z_to_bv 64 a) <> None.
(* the two literals of the snprintf call and " end\0" (.str.4, A_lit_end5 = A_OBJ 31), in the cx's glit_at_x form
   over ARx (W_relay_instance_gone_cx.v: bytes, in_rom, ashp_x, the granule's tail) *)
Hypothesis HLIT20 : glit_at_x ARx 20 (RIG_FMT ++ [0]).
Hypothesis HLIT21 : glit_at_x ARx 21 (RelayModel.K_GESTURE ++ [0]).
(* the two literals lie in .rodata below the GOT word FR_GOT_GUARD = 0x9e658, |"%s %d "| + 1 = 7 and
   |"param_gesture"| + 1 + 8 = 22 bytes: the location premises M1 / M3 of the narrowed asnprintf_realizes_x
   (W_sites_x.v), which this abstract placement does not fix.  PB_fr decides it by vm_compute: SnpNarrowSites.v
   HLITGOT_PB_fr, whose statement is this text at PI := PB_fr (commit 2f48fc47493's hypothesis, carried here). *)
Hypothesis HLITGOT : VAL (A_OBJ 20) + 7 <= FR_GOT_GUARD /\ VAL (A_OBJ 21) + 22 <= FR_GOT_GUARD.
Hypothesis HLIT31 : glit_at_x ARx 31 ([32; 101; 110; 100] ++ [0]).
(* The program statics PST hold no byte this walk carries through a journal's image clause, which exempts PST
   (YCbqG.v ajournal_x): no read-only byte (ajournal_gx_rom_view_x, the literals and " end\0"), and no byte of the
   relay's and the output's global cells (G_RIG, and the cells of HRGP that G_RIG does not name: g_src, g_nsrc,
   g_capsrc, g_send_max, g_client, g_send_dead).  At PST := [] both hold trivially (the template's PSTR / PSTC /
   PSTO, lib/A/W_relay_finish_h.v). *)
Hypothesis PSTR : forall a, in_rom SEGS a -> ~ Exists (in_zr a) PST.
Hypothesis PSTG : forall a,
(inG (G_RIG B RG) a \/ rg_src RG <= a < rg_src RG + 8 \/ rg_nsrc RG <= a < rg_nsrc RG + 4 \/
 rg_capsrc RG <= a < rg_capsrc RG + 4 \/ rg_send_max RG <= a < rg_send_max RG + 8 \/
 rg_client RG <= a < rg_client RG + 4 \/ rg_send_dead RG <= a < rg_send_dead RG + 1) ->
~ Exists (in_zr a) PST.

(* the runners over the generic journal (lib/A/W_relay_finish_h.v's Lets): the plain run and the run to a call on
   ajournal_x, the flag store that frees the fake frame (aj_flag_store_pi_x: ASF, FFL, WFx / WFL / SFREE) *)
Let RUNP := SRr_run_pi_AJ_x (PL := PL_fr) B PST ARx LAWS.
Let RUNC := SRr_run_pi_AJ_call_x (PL := PL_fr) B PST ARx LAWS.
Let RUNF := aj_flag_store_pi_x (PL := PL_fr) B PST ARx LAWS ASF FFL WFx WFL SFREE.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_fr) (PI := PI).

(* ---- Where the representations' bytes are: a global cell, or a byte of a live block. ---- *)
Definition tinb (ly : alayout) (S : astate) (a : Z) : Prop :=
exists p n, In (p, n) (ablocks B ly S) /\ p <= a < p + req_size n.
Lemma tinb_of : forall ly S p n a, In (p, n) (ablocks B ly S) -> 0 <= n -> p <= a < p + n -> tinb ly S a.
Proof. intros ly S p n a Hin Hn Ha. exists p, n. split; [exact Hin|]. pose proof (req_size_pos n Hn). lia. Qed.
Lemma tl_recs_len : forall rs, length (concat (map text_rec rs)) = (16 * length rs)%nat.
Proof.
intros rs. induction rs as [|r rs IH]; [reflexivity|].
cbn [map concat length]. rewrite length_app, IH. unfold text_rec. rewrite length_app, !Mem.length_le8. lia.
Qed.
Lemma tl_key_ptrs_len : forall ks, length (key_ptrs ks) = (8 * length ks)%nat.
Proof.
intros ks. unfold key_ptrs. induction ks as [|k ks IH]; [reflexivity|].
cbn [map concat length]. rewrite length_app, IH. cbn [length]. rewrite Mem.length_le8. lia.
Qed.

Lemma tl_alist_fp : forall ly S W mem LA l lines, alist_at B ly S W mem LA l lines ->
forall r, In r (alist_fp LA l) -> forall a, fst r <= a < snd r -> (LA <= a < LA + 16) \/ tinb ly S a.
Proof.
intros ly S W mem LA l lines HL r Hr a Ha.
pose proof HL as (_ & _ & _ & _ & Hn & Hv & _ & _ & Hrecs).
unfold alist_fp in Hr. cbn [In] in Hr. destruct Hr as [<- | Hr]; [left; cbn [fst snd] in Ha; lia|]. right.
apply in_app_or in Hr. destruct Hr as [Hr | Hr].
- destruct (Z.eqb_spec (hl_cap l) 0) as [Hc0|Hc0]; cbn [In] in Hr; [destruct Hr|].
  destruct Hr as [<- | []]. unfold gfp in Ha. cbn [fst snd] in Ha.
  unfold bzs in Ha. rewrite length_map, length_app, tl_recs_len in Ha.
  destruct Hv as [(Hc & _)|(Hc & Hin & Hj & _)]; [lia|].
  apply (tinb_of ly S (hl_v l) (AREC * hl_cap l) a Hin); [unfold AREC; lia|].
  unfold hl_n, AREC in *. revert Ha Hj Hn Hc. clear. intros. lia.
- apply in_map_iff in Hr as (q & <- & Hq). unfold gfp in Ha. cbn [fst snd] in Ha.
  unfold bzs in Ha. rewrite length_map, length_app in Ha. cbn [length] in Ha.
  rewrite Forall_forall in Hrecs. destruct (Hrecs q Hq) as (Hin & _).
  apply (tinb_of ly S (fst q) (Z.of_nat (length (snd q)) + 1) a Hin); lia.
Qed.
Lemma tl_alist_blks : forall ly S W mem LA l lines, alist_at B ly S W mem LA l lines ->
forall b, In b (alist_blks l) -> In b (ablocks B ly S).
Proof.
intros ly S W mem LA l lines (_ & _ & _ & _ & _ & Hv & _ & _ & Hrecs) b Hb.
unfold alist_blks in Hb. apply in_app_or in Hb. destruct Hb as [Hb | Hb].
- destruct (Z.eqb_spec (hl_cap l) 0) as [Hc0|Hc0]; cbn [In] in Hb; [destruct Hb|].
  destruct Hb as [<- | []]. destruct Hv as [(Hc & _)|(_ & Hin & _)]; [lia | exact Hin].
- apply in_map_iff in Hb as (q & <- & Hq). rewrite Forall_forall in Hrecs. exact (proj1 (Hrecs q Hq)).
Qed.

Lemma tl_asrc_fp : forall ly S W mem HA h, asrc_at B ly S W mem HA h ->
forall r, In r (asrc_fp HA h) -> forall a, fst r <= a < snd r -> (HA <= a < HA + ASRC) \/ tinb ly S a.
Proof.
intros ly S W mem HA h HS r Hr a Ha.
pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpb & Hpj & _ & _ &
  Hexp & Hheld & _).
unfold asrc_fp in Hr. cbn [In] in Hr. destruct Hr as [<- | [<- | Hr]].
- left. cbn [fst snd] in Ha. lia.
- right. unfold gfp in Ha. cbn [fst snd] in Ha. unfold bzs in Ha. rewrite length_map in Ha.
  apply (tinb_of ly S (hs_partial h) APARTIAL a Hpb); [unfold APARTIAL; lia | lia].
- apply in_app_or in Hr. destruct Hr as [Hr | Hr].
  + destruct (tl_alist_fp ly S W mem (HA + 16) _ false Hpend r Hr a Ha) as [H | H]; [left; unfold ASRC; lia | right; exact H].
  + apply in_app_or in Hr. destruct Hr as [Hr | Hr].
    * destruct (tl_alist_fp ly S W mem (HA + 64) _ true Hexp r Hr a Ha) as [H | H]; [left; unfold ASRC; lia | right; exact H].
    * destruct (tl_alist_fp ly S W mem (HA + 80) _ true Hheld r Hr a Ha) as [H | H]; [left; unfold ASRC; lia | right; exact H].
Qed.
Lemma tl_asrc_blks : forall ly S W mem HA h, asrc_at B ly S W mem HA h ->
forall b, In b (asrc_blks h) -> In b (ablocks B ly S).
Proof.
intros ly S W mem HA h HS b Hb.
pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpb & _ & _ & _ &
  Hexp & Hheld & _).
unfold asrc_blks in Hb. cbn [In] in Hb. destruct Hb as [<- | Hb]; [exact Hpb|].
apply in_app_or in Hb. destruct Hb as [Hb | Hb]; [exact (tl_alist_blks _ _ _ _ _ _ _ Hpend b Hb)|].
apply in_app_or in Hb. destruct Hb as [Hb | Hb]; [exact (tl_alist_blks _ _ _ _ _ _ _ Hexp b Hb)|].
exact (tl_alist_blks _ _ _ _ _ _ _ Hheld b Hb).
Qed.

Lemma tl_aentry_fp : forall ly S W mem e, aentry_ok B ly S W mem e ->
forall r, In r (aentry_fp e) -> forall a, fst r <= a < snd r -> tinb ly S a.
Proof.
intros ly S W mem e HE r Hr a Ha.
pose proof HE as (_ & _ & _ & _ & _ & _ & HU & _ & _ & Hbuf & _ & Hhp & _ & _ & Hks).
unfold aentry_fp in Hr. apply in_app_or in Hr. destruct Hr as [Hr | Hr].
- destruct (Z.eqb_spec (re_cap e) 0) as [Hc0|Hc0]; cbn [In] in Hr; [destruct Hr|].
  destruct Hr as [<- | []]. unfold gfp in Ha. cbn [fst snd] in Ha. unfold bzs in Ha.
  rewrite length_map, length_app in Ha.
  destruct Hbuf as [(Hc & _)|(Hc & Hin & Hj & _)]; [lia|].
  apply (tinb_of ly S (re_buf e) (re_cap e) a Hin); lia.
- cbn [In] in Hr. destruct Hr as [<- | Hr].
  + unfold gfp in Ha. cbn [fst snd] in Ha. unfold bzs in Ha. rewrite length_map, tl_key_ptrs_len in Ha.
    destruct Hhp as [(Hz & Hke)|(Hz & Hin & Hk1 & Hk2 & _)].
    * rewrite Hke in Ha. cbn [length] in Ha. lia.
    * apply (tinb_of ly S (re_hp e) (re_kh e) a Hin); [lia|]. unfold re_nheld in Hk1. lia.
  + apply in_map_iff in Hr as (k & <- & Hk). unfold gfp in Ha. cbn [fst snd] in Ha.
    unfold bzs in Ha. rewrite length_map, length_app in Ha. cbn [length] in Ha.
    rewrite Forall_forall in Hks. destruct (Hks k Hk) as (Hin & _).
    apply (tinb_of ly S (key_addr k) (Z.of_nat (length (key_text k)) + 1) a Hin); lia.
Qed.
Lemma tl_aentry_blks : forall ly S W mem e, aentry_ok B ly S W mem e ->
forall b, In b (aentry_blks e) -> In b (ablocks B ly S).
Proof.
intros ly S W mem e HE b Hb.
pose proof HE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hbuf & _ & Hhp & _ & _ & Hks).
unfold aentry_blks in Hb. apply in_app_or in Hb. destruct Hb as [Hb | Hb].
- destruct (Z.eqb_spec (re_cap e) 0) as [Hc0|Hc0]; cbn [In] in Hb; [destruct Hb|].
  destruct Hb as [<- | []]. destruct Hbuf as [(Hc & _)|(_ & Hin & _)]; [lia | exact Hin].
- apply in_app_or in Hb. destruct Hb as [Hb | Hb].
  + destruct (Z.eqb_spec (re_hp e) 0) as [Hz0|Hz0]; cbn [In] in Hb; [destruct Hb|].
    destruct Hb as [<- | []]. destruct Hhp as [(Hz & _)|(_ & Hin & _)]; [lia | exact Hin].
  + apply in_map_iff in Hb as (k & <- & Hk). rewrite Forall_forall in Hks. exact (proj1 (Hks k Hk)).
Qed.

Lemma tl_arelay_fp : forall ly S W mem G es, arelay_at B RG ly S W mem G es ->
forall r, In r (arelay_fp RG G es) -> forall a, fst r <= a < snd r ->
(rg_src RG <= a < rg_src RG + 8 \/ rg_nsrc RG <= a < rg_nsrc RG + 4 \/ rg_capsrc RG <= a < rg_capsrc RG + 4) \/
tinb ly S a.
Proof.
intros ly S W mem G es HR r Hr a Ha.
pose proof HR as (_ & _ & _ & _ & _ & _ & _ & HG & _ & HE & _).
unfold arelay_fp in Hr. cbn [In] in Hr.
destruct Hr as [<- | [<- | [<- | [<- | Hr]]]]; cbn [fst snd] in Ha.
- left; left; lia.
- left; right; left; lia.
- left; right; right; lia.
- right. apply (tinb_of ly S G ATABLE a HG); [unfold ATABLE; lia | lia].
- right. apply in_concat in Hr as (fp & Hfp & Hr). apply in_map_iff in Hfp as (e & <- & He).
  rewrite Forall_forall in HE. exact (tl_aentry_fp ly S W mem e (HE e He) r Hr a Ha).
Qed.
Lemma tl_arelay_blks : forall ly S W mem G es, arelay_at B RG ly S W mem G es ->
forall b, In b (arelay_blks G es) -> In b (ablocks B ly S).
Proof.
intros ly S W mem G es HR b Hb.
pose proof HR as (_ & _ & _ & _ & _ & _ & _ & HG & _ & HE & _).
unfold arelay_blks in Hb. cbn [In] in Hb. destruct Hb as [<- | Hb]; [exact HG|].
apply in_concat in Hb as (bl & Hbl & Hb). apply in_map_iff in Hbl as (e & <- & He).
rewrite Forall_forall in HE. exact (tl_aentry_blks ly S W mem e (HE e He) b Hb).
Qed.

Lemma tl_aout_fp : forall ly S W mem c O mx no cap out, aout_at B RG ly S W mem c O mx no cap out ->
forall r, In r (aout_fp B RG cap out) -> forall a, fst r <= a < snd r ->
(rg_send_max RG <= a < rg_send_max RG + 8 \/ rg_nout RG <= a < rg_nout RG + 8 \/
 rg_capout RG <= a < rg_capout RG + 8 \/ rg_out RG <= a < rg_out RG + 8 \/ rg_client RG <= a < rg_client RG + 4 \/
 rg_client_broken RG <= a < rg_client_broken RG + 1 \/ rg_send_dead RG <= a < rg_send_dead RG + 1 \/
 rg_send_eintr RG <= a < rg_send_eintr RG + 1 \/ as_errno B <= a < as_errno B + 4) \/ tinb ly S a.
Proof.
intros ly S W mem c O mx no cap out HO r Hr a Ha.
pose proof HO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hblk).
unfold aout_fp in Hr. cbn [In] in Hr.
destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | Hr]]]]]]]]]; cbn [fst snd] in Ha.
- left; left; lia.
- left; right; left; lia.
- left; right; right; left; lia.
- left; right; right; right; left; lia.
- left; right; right; right; right; left; lia.
- left; right; right; right; right; right; left; lia.
- left; right; right; right; right; right; right; left; lia.
- left; right; right; right; right; right; right; right; left; lia.
- left; right; right; right; right; right; right; right; right; lia.
- right. destruct (Z.eqb_spec cap 0) as [Hc0|Hc0]; cbn [In] in Hr; [destruct Hr|].
  destruct Hr as [<- | []]. cbn [fst snd] in Ha.
  destruct Hblk as [(Hc & _) | (Hcp & _ & Hin & _)]; [lia|].
  apply (tinb_of ly S out cap a Hin); lia.
Qed.
Lemma tl_aout_blks : forall ly S W mem c O mx no cap out, aout_at B RG ly S W mem c O mx no cap out ->
forall b, In b (aout_blks cap out) -> In b (ablocks B ly S).
Proof.
intros ly S W mem c O mx no cap out HO b Hb.
pose proof HO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hblk).
unfold aout_blks in Hb. destruct (Z.eqb_spec cap 0) as [Hc0|Hc0]; cbn [In] in Hb; [destruct Hb|].
destruct Hb as [<- | []]. destruct Hblk as [(Hc & _) | (_ & _ & Hin & _)]; [lia | exact Hin].
Qed.

Lemma tl_kept_trans : forall (W W' W'' : world SEGS) m m' m'' a,
abyte_kept W m W' m' a -> abyte_kept W' m' W'' m'' a -> abyte_kept W m W'' m'' a.
Proof.
intros W W' W'' m m' m'' a (H1 & H2) (H3 & H4). split; [rewrite H3; exact H1 | intros Hw; exact (H4 (H2 Hw))].
Qed.
Lemma tl_preserved_at : forall regs regs' (r : bv 5), aregs_preserved regs regs' -> acallee_saved (bv_unsigned r) ->
getr regs' r = getr regs r.
Proof. intros regs regs' r HP Hr. pose proof (HP _ Hr) as H. rewrite !Z_to_bv_bv_unsigned in H. exact H. Qed.

(* ---- TAIL. ---- *)
Theorem rig_tail : rig_tail_stmt B PST ARx MT RP MMAX RG.
Proof.
unfold rig_tail_stmt. intros cx W1 c1 HB HU.
destruct HU as (regs1 & ly1 & S1 & m1 & md1 & k1 & F & FL & qd & c2 & O2 & cap2 & out2 & spent & -> & HRB & H21 & HGL & HGO).
destruct HGL as (fpos & Hp1 & HJ & HROM1 & HPK & HFR & HLK).
destruct HFR as (HFa & HFl & HFL120 & HS16 & HS24 & HS80 & HSV).
destruct HRB as (Hsp1 & Hgp1 & Htp1 & H8 & H9 & H18).
destruct HB as (HPRE & H32 & HCNT & RGP & H10 & RID & HLK0 & HREL0 & HOUT0 & HROM0 & HLEN & HDRS0 & HND & HPERM0 & HTRM & HLIVE & HMOK
  & HRMB & HCKB).
destruct RGP as (RGLOCK & RGNSRC & RGSRC & RGAL8 & RGAL4 & RGSAL & RGIMG & RGWR & RGSEP).
destruct HGO as (Hle & Hlq & Hrel & Hrly & Hout & Hsrc & Hdrs & Hgs & Hperm & Hbud).
destruct HJ as (HSTK & _ & (memS & HJi & Hag) & _).
rewrite !Z.add_0_r in HJi.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : RIG_STK_x = 17200) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & _ & _ & _).
pose proof HJi as (HAR1 & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres1 & Hstatic & _ & _).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _ & _ & _).
assert (SP1 : spZ regs1 = gsp0 cx - 224) by (rewrite Hsp1; reflexivity).
assert (SPR : alloc_ceiling + 12880 <= gsp0 cx - 4320 /\ gsp0 cx <= 2 ^ 47) by (unfold gsp0 in *; rewrite WS in Hslo; lia).
(* the frame (1, fpos), its shadow and its flag cell at S1 *)
assert (Hfin : In (1, fpos) (frames S1)) by (rewrite Hfrs; left; reflexivity).
destruct (alx_frames _ _ _ LAWS _ _ _ _ _ _ 1 fpos HAR1 Hfin) as (HFal & HFapp & HFpres & HFSpres).
destruct (FFL _ _ _ _ _ _ 1 fpos HAR1 Hfin) as (HFLp & HFLo & (HFLapp & HFLimg) & (HFL4096 & HFLz & HFLc)).
destruct (frames_bounds_x SEGS B ARx LAWS _ _ _ _ _ _ 1 fpos HAR1 Hfin) as (HF4096 & HFceil & HFhigh).
change (fs_frame_bytes 1) with 128 in *. change (128 / 8) with 16 in *.
rewrite HFa, HFl in *.
assert (HFLF : ~ (F <= FL < F + 128)) by (intros Hx; exact (proj2 (HFpres FL Hx) HFLo)).
assert (HFLS : ~ (shadow_addr F <= FL < shadow_addr F + 16)).
{ intros Hx. apply (proj2 (HFSpres (FL - shadow_addr F) ltac:(lia))).
  replace (shadow_addr F + (FL - shadow_addr F)) with FL by lia. exact HFLo. }
assert (HF8 : F = 8 * (F / 8) + F mod 8) by (apply Z.div_mod; lia).
pose proof (Z.mod_pos_bound F 8 ltac:(lia)) as HF8m.
assert (SF : shadow_addr F = 2147450880 + F / 8) by (unfold shadow_addr, SHADOW_OFF; lia).
assert (HFLapp' := HFLapp). unfold app_addr, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFLapp'.
(* the bytes no allocator law lets be image bytes *)
assert (NIMG : forall a, (F <= a < F + 128 \/ a = FL) -> ~ in_img SEGS a).
{ intros a Ha Hi. refine (proj2 (alx_client_img _ _ _ LAWS _ _ _ _ _ _ a HAR1 _) Hi). right.
  destruct Ha as [Ha | ->]; [left | right]; exists 1, fpos; split; try exact Hfin;
  rewrite ?HFa, ?HFl; change (fs_frame_bytes 1) with 128; first [lia | reflexivity]. }
(* ---- SEAT 1 and the run to the call (auipc, addi, jal) ---- *)
unfold cfg_at, w64.
remember (Eimg (Ereg regs1 [])) as E1 eqn:HE1.
pose proof (rt_entry0 W1 regs1 m1) as HS. rewrite <- HE1 in HS.
assert (HEI1 : img_env VAL A_LIM E1) by (subst E1; apply Eimg_env).
assert (EE1 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E1 n = getr regs1 r)
by (intros n r Hn; subst E1; pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5;
rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
clear HE1.
paj_run_shc_x RUNP RUNC HS HJi.
{ intros a (r & Hin & _). cbn in Hin. destruct Hin. }
rename ms into ms0, mat into mat0, HF into HF1, HFr into HFr1, HG into HG1.
pmkst HS.
prreg HS (1%bv : bv 5) QRA. prreg HS (2%bv : bv 5) QSP. prreg HS (3%bv : bv 5) QGP. prreg HS (4%bv : bv 5) QTP.
prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (21%bv : bv 5) Q21.
prreg HS (10%bv : bv 5) QA0.
assert (M01 : forall a, aview SEGS (w_H W1) (ms_mem ms0) a = aview SEGS (w_H W1) m1 a).
{ intros a. apply aview_eq_of. apply HFr1. intros (r & Hin & _). cbn in Hin. destruct Hin. }
assert (P01 : forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) (ms_mem ms0) a)
by (intros a Hp; eapply apresent_grows; [exact HG1 | exact Hp]).
assert (HSPc : spZ (ms_regs ms0) = gsp0 cx + -224).
{ unfold spZ at 1. rewrite QSP, (EE1 2%nat 2%bv eq_refl). fold (spZ regs1). lia. }
assert (QA0' : getr (ms_regs ms0) 10 = w64 (rg_lock RG)).
{ rewrite QA0. change 247%nat with (A_OBJ 6). rewrite (img_env_atomP E1 (A_OBJ 6) HEI1 ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
  rewrite RGLOCK. reflexivity. }
(* g_lock's twelve bytes *)
pose proof HLK as (LK0 & LK4 & LK8 & LKW). unfold arm in LK0, LK4, LK8, LKW.
assert (LKI : forall a, rg_lock RG <= a < rg_lock RG + 12 ->
  in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4))
by (intros a Ha; apply RGIMG; unfold rg_rng; tauto).
assert (LKV : forall a, rg_lock RG <= a < rg_lock RG + 12 -> aview SEGS (w_H W1) m1 a <> None).
{ intros a Ha. unfold aview.
  destruct (Z_lt_ge_dec a (rg_lock RG + 4)) as [h1|h1]; [|destruct (Z_lt_ge_dec a (rg_lock RG + 8)) as [h2|h2]].
  - pose proof (LK0 (Z.to_nat (a - rg_lock RG)) ltac:(lia)) as X. rewrite Z2Nat.id in X by lia.
    replace (rg_lock RG + (a - rg_lock RG)) with a in X by lia. rewrite X. discriminate.
  - pose proof (LK4 (Z.to_nat (a - (rg_lock RG + 4))) ltac:(lia)) as X. rewrite Z2Nat.id in X by lia.
    replace (rg_lock RG + 4 + (a - (rg_lock RG + 4))) with a in X by lia. rewrite X. discriminate.
  - pose proof (LK8 (Z.to_nat (a - (rg_lock RG + 8))) ltac:(lia)) as X. rewrite Z2Nat.id in X by lia.
    replace (rg_lock RG + 8 + (a - (rg_lock RG + 8))) with a in X by lia. rewrite X. discriminate. }
assert (LKlo : forall a, rg_lock RG <= a < rg_lock RG + 12 -> 0 <= a < kLowMemEnd)
by (intros a Ha; exact (Hsegs a (proj1 (LKI a Ha)))).
eassert (HJX : ajournal_gx_x (SK := SK) SEGS B PST ARx (G_RIG B RG) 0 [] RIG_STK_x (gsp0 cx) (gFP cx)
  (gxly cx) (gxS cx) (gxHp cx) (gxW cx) (gxmem cx) (gxmd cx) [(1, fpos)] ly1 S1 Hp1 W1 (ms_mem ms0) _ k1).
{ eapply ajournal_gx_pack_x; [rewrite WS; lia | lia | rewrite !Z.add_0_r; exact HJi | exact Hag | intros a Ha; lia]. }
(* ---- pthread_mutex_unlock (&g_lock) ---- *)
eapply SRr_bind.
{ eapply (aj_gx_entry_at_x B PST ARx LAWS (G_RIG B RG) 0 [] ESTACK (SIGMA WS_pthread_mutex_unlock)
    (fun a => rg_lock RG + 4 <= a < rg_lock RG + 8)
    (fun (regs' : bvmap 5 word) (mem' : word -> option byte) =>
       getr regs' 10 = w64 0 /\ val_mem SEGS (mrestrict (w_H W1) mem') (rg_lock RG + 4) 4 0)
    W1 _ _ RIG_STK_x (gsp0 cx) (gFP cx) (gxly cx) (gxS cx) (gxHp cx) (gxW cx) (gxmem cx) (gxmd cx) _ _ _ _ _ _ (-224) _ HGRIG eq_refl HJX).
  - exact HSPc.
  - reflexivity.
  - lia.
  - lia.
  - rewrite WS, Hes. lia.
  - rewrite QGP, (EE1 3%nat 3%bv eq_refl), Hgp1. exact Hgp.
  - rewrite QTP, (EE1 4%nat 4%bv eq_refl), Htp1. exact Htp.
  - exact QRA.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros a. destruct (Z_lt_ge_dec a (rg_lock RG + 4)); [right; lia|].
    destruct (Z_lt_ge_dec a (rg_lock RG + 8)); [left; lia | right; lia].
  - intros a Ha _. rewrite (M01 a). exact (LKV a ltac:(lia)).
  - intros a Ha HnG. exfalso. apply HnG. unfold G_RIG. apply inG_cons. left. unfold in_zr. cbn [fst snd]. lia.
  - intros HPRE2 HSC. apply (AUNLOCK _ _ _ _ _ _ _ (rg_lock RG) HPRE2).
    + exact QA0'.
    + pose proof (LKlo (rg_lock RG) ltac:(lia)). pose proof (Hsegs _ (proj1 (LKI (rg_lock RG) ltac:(lia)))).
      destruct (Z.eq_dec (rg_lock RG) 0) as [E0|E0]; [|lia].
      exfalso. pose proof (pa_obj_img 6 ltac:(lia)) as HlkR. rewrite <- RGLOCK in HlkR. lia.
    + pose proof (Z.div_mod (rg_lock RG) 8 ltac:(lia)). pose proof (Z.div_mod (rg_lock RG) 4 ltac:(lia)).
      pose proof (Z.mod_pos_bound (rg_lock RG) 4 ltac:(lia)). lia.
    + pose proof (LKlo (rg_lock RG) ltac:(lia)). unfold kLowMemEnd in *. lia.
    + apply (val_mem_kept SEGS (w_H W1) (w_H W1) m1 (ms_mem ms0) _ 4 _); [intros kk _; apply M01 | exact LK0].
    + apply (val_mem_kept SEGS (w_H W1) (w_H W1) m1 (ms_mem ms0) _ 4 _); [intros kk _; apply M01 | exact LK4].
    + apply (val_mem_kept SEGS (w_H W1) (w_H W1) m1 (ms_mem ms0) _ 4 _); [intros kk _; apply M01 | exact LK8].
    + intros a Ha. split; [rewrite (M01 a); exact (LKV a Ha)|]. rewrite HSPc. pose proof (LKlo a Ha).
      unfold kLowMemEnd in *. unfold ESTACK. lia.
    + intros a Ha. destruct (LKI a ltac:(lia)) as (Hi & Ho & He). split; [|split].
      * apply (RGWR (w_H W1) (ms_mem ms0) a); [left; lia | exact (hidden_not_img SEGS W1 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by (pose proof (LKlo a ltac:(lia)); unfold kLowMemEnd in *; lia); exact Hi))].
      * intros Hown. apply Ho. exact (proj1 (alx_owned_image _ _ _ LAWS _ _ _ _ _ _ a (proj1 HJi) Hi) Hown).
      * rewrite HSPc. pose proof (LKlo a ltac:(lia)). unfold kLowMemEnd in *. unfold ESTACK. lia.
    + intros a Ha HK. refine (proj2 (proj2 (HGRIG a _)) (proj1 (proj2 HK))). unfold G_RIG. apply inG_cons. left. unfold in_zr. cbn [fst snd]. lia. }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJX3 & HP3 & (HA03 & HLK3) & Hfr3 & Hpres3).
(* what the unlock kept *)
assert (K13 : forall a, 0 <= a < 2 ^ 64 -> ~ (rg_lock RG + 4 <= a < rg_lock RG + 8) -> ~ (gsp0 cx - 4320 <= a < gsp0 cx - 224) ->
  aview SEGS (w_H W1) mem3 a = aview SEGS (w_H W1) m1 a).
{ intros a Ha H1 H2. rewrite (Hfr3 a Ha H1 ltac:(unfold ESTACK; lia)). apply M01. }
assert (P13 : forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) mem3 a) by (intros a Hp; apply Hpres3, P01, Hp).
assert (G3 : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs3 r = getr (ms_regs ms0) r)
by (intros r Hr; exact (tl_preserved_at _ _ r HP3 Hr)).
assert (G3_2 : getr regs3 2 = getr regs1 2) by (rewrite (G3 2%bv ltac:(unfold acallee_saved; change (bv_unsigned (2%bv : bv 5)) with 2; lia)), QSP; exact (EE1 2%nat 2%bv eq_refl)).
assert (G3_3 : getr regs3 3 = getr regs1 3) by (rewrite (G3 3%bv ltac:(unfold acallee_saved; change (bv_unsigned (3%bv : bv 5)) with 3; lia)), QGP; exact (EE1 3%nat 3%bv eq_refl)).
assert (G3_4 : getr regs3 4 = getr regs1 4) by (rewrite (G3 4%bv ltac:(unfold acallee_saved; change (bv_unsigned (4%bv : bv 5)) with 4; lia)), QTP; exact (EE1 4%nat 4%bv eq_refl)).
assert (G3_8 : getr regs3 8 = getr regs1 8) by (rewrite (G3 8%bv ltac:(unfold acallee_saved; change (bv_unsigned (8%bv : bv 5)) with 8; lia)), Q8; exact (EE1 8%nat 8%bv eq_refl)).
assert (G3_9 : getr regs3 9 = getr regs1 9) by (rewrite (G3 9%bv ltac:(unfold acallee_saved; change (bv_unsigned (9%bv : bv 5)) with 9; lia)), Q9; exact (EE1 9%nat 9%bv eq_refl)).
assert (G3_21 : getr regs3 21 = getr regs1 21) by (rewrite (G3 21%bv ltac:(unfold acallee_saved; change (bv_unsigned (21%bv : bv 5)) with 21; lia)), Q21; exact (EE1 21%nat 21%bv eq_refl)).
assert (SP3 : spZ regs3 = gsp0 cx - 224) by (unfold spZ; rewrite G3_2; fold (spZ regs1); exact SP1).
assert (V13 : forall a n v, gsp0 cx - 224 <= a -> a + Z.of_nat n <= gsp0 cx ->
  val_mem SEGS (mrestrict (w_H W1) m1) a n v -> val_mem SEGS (mrestrict (w_H W1) mem3) a n v).
{ intros a n v Ha Hn Hv. apply (val_mem_kept SEGS (w_H W1) (w_H W1) m1 mem3 a n v); [|exact Hv].
  intros kk Hk. apply K13; [lia | | lia]. intros Hx. pose proof (LKlo (a + kk) ltac:(lia)). unfold kLowMemEnd in *. lia. }
assert (VF13 : val_mem SEGS (mrestrict (w_H W1) mem3) (F + 120) 8 FL).
{ apply (val_mem_kept SEGS (w_H W1) (w_H W1) m1 mem3 _ 8 _); [|exact HFL120].
  intros kk Hk. apply K13; [lia | | lia]. intros Hx. apply (NIMG (F + 120 + kk) ltac:(cbn in Hk; lia)).
  exact (proj1 (LKI (F + 120 + kk) ltac:(lia))). }
try rewrite QRA. change (BASE + 3268) with (BASE + A_rt_rel).
(* ---- SEAT 2 at 0x82fb0 ---- *)
pose proof (rt_entry W1 regs3 mem3 (gxregs cx) F FL) as HS2.
specialize (HS2 ltac:(rewrite G3_9, H9, SP3; unfold w64, gsp1, RIG_FRAME; rewrite unsigned_lit_small by lia; lia)
  ltac:(rewrite G3_8, H8, SP3; unfold w64; rewrite unsigned_lit_small by lia; lia)
  ltac:(rewrite G3_21; exact H21) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HFal HFapp ltac:(lia) HFLF HFLS
  ltac:(intros o Ho; apply P13; exact (proj1 (HFpres (F + o) ltac:(lia))))
  ltac:(intros o Ho; apply P13; exact (proj1 (HFSpres o Ho)))
  ltac:(apply P13; exact HFLp) VF13
  ltac:(rewrite SP3; apply V13; [lia | cbn; lia | exact HS16])
  ltac:(rewrite SP3; apply V13; [lia | cbn; lia | exact HS24])
  ltac:(intros i Hi; rewrite SP3; apply V13; [lia | cbn; lia |];
        replace (gsp0 cx - 224 + 120 + 8 * Z.of_nat i) with (gsp1 cx + 120 + 8 * Z.of_nat i) by (unfold gsp1, RIG_FRAME; lia);
        exact (HSV i Hi))).
remember (Eimg (Ereg regs3 (rt_extra (gxregs cx) F FL))) as E2 eqn:HE2.
assert (HEI2 : img_env VAL A_LIM E2) by (subst E2; apply Eimg_env).
assert (EE2 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E2 n = getr regs3 r)
by (intros n r Hn; subst E2; pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5;
rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
assert (EX2 : forall i, (i < 13)%nat -> ew E2 (32 + i) = getr (gxregs cx) (nth i RIG_SAVED 0%bv)).
{ intros i Hi. subst E2. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite ew_Ereg_extra. exact (nth_rt_extra _ F FL i Hi). }
assert (U45 : bv_unsigned (ew E2 45) = F)
by (subst E2; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_extra regs3 _ 13); cbn; apply unsigned_lit_small; lia).
assert (U46 : bv_unsigned (ew E2 46) = FL)
by (subst E2; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_extra regs3 _ 14); cbn; apply unsigned_lit_small; lia).
assert (U21 : bv_unsigned (ew E2 21) = shadow_addr F)
by (rewrite (EE2 21%nat 21%bv eq_refl), G3_21, H21; unfold w64; apply unsigned_lit_small; lia).
assert (U9 : bv_unsigned (ew E2 9) = gsp0 cx - 224)
by (rewrite (EE2 9%nat 9%bv eq_refl), G3_9, H9; unfold w64, gsp1, RIG_FRAME; apply unsigned_lit_small; lia).
assert (U8 : bv_unsigned (ew E2 8) = gsp0 cx)
by (rewrite (EE2 8%nat 8%bv eq_refl), G3_8, H8; unfold w64; apply unsigned_lit_small; lia).
clear HE2.
destruct HJX3 as (_ & _ & (memS3 & HJ3 & Hag3) & _).
rewrite !Z.add_0_r in HJ3.
(* ---- the release (retired magic, shadow 0xf5, *FL = 0) and the epilogue, to the ret ---- *)
paj_run_flag_sh_x RUNF HS2 HJ3.
{ lia. }
{ intros a (r & Hin & Hr).
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
  cbn [In] in Hin. rewrite HFl.
  repeat (destruct Hin as [<- | Hin];
  [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U45, ?U46, ?U21, ?U9, ?U8 in Hr;
    first [ lia
    | right; lia
    | left; right; right; right; exists 1, fpos; split; [left; reflexivity|]; rewrite HFa;
      change (fs_frame_bytes 1) with 128; change (128 / 8) with 16;
      first [ left; unfold in_zr; cbn [fst snd]; lia
      | right; unfold in_zr; cbn [fst snd]; lia ] ]
  | ]).
  destruct Hin. }
{ intros msr HSr. rewrite HFl.
  lazymatch type of HSr with st_ok_pi _ _ ?Ex ?ssx _ =>
  pose proof (st_ok_pi_region_nth Ex ssx msr 0 _ HSr eq_refl) as HR;
  lazymatch type of HR with region_ok _ _ _ (YP09.mkRegion (Some ?n) ?lo ?hi ?wlo ?whi ?cs) =>
  pose proof (field_of_region Ex (ms_mem msr) n _ cs lo hi wlo whi 0 1%N (SLit 0) 0 HR U46
  ltac:(left; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V end end.
  rewrite Z.add_0_r in V. pose proof (V 0%nat ltac:(lia)) as V0. cbn [Z.of_nat] in V0. rewrite Z.add_0_r in V0. exact V0. }
rename ms into ms2, mat into mat2, HF into HF2, HFr into HFr2, HG into HG2.
prreg HS2 (1%bv : bv 5) R1. prreg HS2 (2%bv : bv 5) R2. prreg HS2 (3%bv : bv 5) R3. prreg HS2 (4%bv : bv 5) R4.
prreg HS2 (8%bv : bv 5) R8. prreg HS2 (9%bv : bv 5) R9. prreg HS2 (18%bv : bv 5) R18. prreg HS2 (19%bv : bv 5) R19.
prreg HS2 (20%bv : bv 5) R20. prreg HS2 (21%bv : bv 5) R21. prreg HS2 (22%bv : bv 5) R22. prreg HS2 (23%bv : bv 5) R23.
prreg HS2 (24%bv : bv 5) R24. prreg HS2 (25%bv : bv 5) R25. prreg HS2 (26%bv : bv 5) R26. prreg HS2 (27%bv : bv 5) R27.
eapply (RET W1 _ _ _ _ _ HS2 eq_refl ltac:(vm_compute; reflexivity)).
intros matR.
(* ---- what the tail kept: every byte but g_lock + 4 .. + 8, unlock's scratch, F, F's shadow and FL ---- *)
cbn [ms_mem mkst] in HF2, HFr2, HG2.
assert (NWR : forall a, ~ (F <= a < F + 128) -> ~ (shadow_addr F <= a < shadow_addr F + 16) -> a <> FL ->
  ~ in_wrange E2 (ss_mem ss_rt) a).
{ intros a N1 N2 N3 (r & Hin & Hr).
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [<- | Hin];
  [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U45, ?U46, ?U21, ?U9, ?U8 in Hr; lia | ]).
  destruct Hin. }
assert (K2e : forall a, 0 <= a < 2 ^ 64 -> ~ (F <= a < F + 128) -> ~ (shadow_addr F <= a < shadow_addr F + 16) -> a <> FL ->
  aview SEGS (w_H W1) (ms_mem ms2) a = aview SEGS (w_H W1) mem3 a)
by (intros a Ha N1 N2 N3; exact (aview_kept_out E2 (ss_mem ss_rt) (w_H W1) mem3 (ms_mem ms2) HFr2 a Ha (NWR a N1 N2 N3))).
assert (P2e : forall a, apresent (w_H W1) mem3 a -> apresent (w_H W1) (ms_mem ms2) a)
by (intros a Hp; eapply apresent_grows; [exact HG2 | exact Hp]).
assert (KALL : forall a, 0 <= a < 2 ^ 64 -> ~ (rg_lock RG + 4 <= a < rg_lock RG + 8) ->
  ~ (gsp0 cx - 4320 <= a < gsp0 cx - 224) -> ~ (F <= a < F + 128) -> ~ (shadow_addr F <= a < shadow_addr F + 16) ->
  a <> FL -> abyte_kept W1 m1 W1 (ms_mem ms2) a).
{ intros a Ha N0 N1 N2 N3 N4. split.
  - rewrite (K2e a Ha N2 N3 N4). exact (K13 a Ha N0 N1).
  - unfold arm. apply writable_kept. intros Hp. apply P2e, P13, Hp. }
assert (KIMG : forall a, in_img SEGS a -> ~ (rg_lock RG + 4 <= a < rg_lock RG + 8) -> abyte_kept W1 m1 W1 (ms_mem ms2) a).
{ intros a Hi Hl. pose proof (Hsegs a Hi) as Ha. rewrite C5 in Ha. apply KALL; try exact Hl.
  - lia.
  - destruct SPR as [SPa SPb]. revert Ha SPa C1. clear. intros. lia.
  - intros Hx. exact (NIMG a (or_introl Hx) Hi).
  - rewrite SF. revert Ha HF4096 HF8 HF8m. clear. intros. lia.
  - intros ->. exact (NIMG FL (or_intror eq_refl) Hi). }
assert (KBLK : forall a, tinb ly1 S1 a -> abyte_kept W1 m1 W1 (ms_mem ms2) a).
{ intros a (p & n & Hin & Ha).
  destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ p n HAR1 Hin) as (_ & Hp4 & Hpc & Happ & Hpo & _).
  pose proof (sep_block_frame_x SEGS B ARx LAWS _ _ _ _ _ _ p n 1 fpos HAR1 Hin Hfin) as Hd.
  rewrite HFa in Hd. change (fs_frame_bytes 1) with 128 in Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd.
  assert (Hni : ~ in_img SEGS a).
  { intros Hi. refine (proj2 (alx_client_img _ _ _ LAWS _ _ _ _ _ _ a HAR1 _) Hi). left. exists p, n. split; [exact Hin | lia]. }
  apply KALL.
  - lia.
  - intros Hl. apply Hni. exact (proj1 (LKI a ltac:(lia))).
  - destruct SPR as [SPa SPb]. lia.
  - lia.
  - intros Hs. rewrite SF in Hs. apply (fshadow_not_app F 16 p (req_size n) a); [lia | lia | exact Happ | lia | lia].
  - intros ->. exact (proj2 (Hpo FL Ha) HFLo). }
assert (GLOB : forall a,
  (rg_src RG <= a < rg_src RG + 8 \/ rg_nsrc RG <= a < rg_nsrc RG + 4 \/ rg_capsrc RG <= a < rg_capsrc RG + 4 \/
   rg_s RG <= a < rg_s RG + 4 * ASRC \/
   rg_send_max RG <= a < rg_send_max RG + 8 \/ rg_nout RG <= a < rg_nout RG + 8 \/
   rg_capout RG <= a < rg_capout RG + 8 \/ rg_out RG <= a < rg_out RG + 8 \/ rg_client RG <= a < rg_client RG + 4 \/
   rg_client_broken RG <= a < rg_client_broken RG + 1 \/ rg_send_dead RG <= a < rg_send_dead RG + 1 \/
   rg_send_eintr RG <= a < rg_send_eintr RG + 1 \/ as_errno B <= a < as_errno B + 4) ->
  abyte_kept W1 m1 W1 (ms_mem ms2) a).
{ intros a Ha.
  pose proof HRGP as (HL & _). cbn [zall_disjoint] in HL. unfold zdisj in HL. cbn [fst snd] in HL.
  destruct HL as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13 & D14 & _).
  assert (GI : forall x l, In (x, l) (G_RIG B RG) -> x <= a < x + l -> in_img SEGS a).
  { intros x l Hxl Hx. apply (proj1 (HGRIG a ltac:(unfold inG; apply Exists_exists; exists (x, l); split; [exact Hxl | unfold in_zr; cbn [fst snd]; lia]))). }
  assert (RI : rg_rng RG a -> in_img SEGS a) by (intros Hr; exact (proj1 (RGIMG a Hr))).
  unfold rg_rng in RI.
  destruct Ha as [Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|Ha]]]]]]]]]]]]; apply KIMG.
  - apply RI. right; right; left. exact Ha.
  - clear - D2 Ha. lia.
  - apply RI. right; left. exact Ha.
  - clear - D3 Ha. lia.
  - apply (proj1 (HRGI a ltac:(left; exact Ha))).
  - clear - D4 Ha. lia.
  - apply RI. right; right; right; right. exact Ha.
  - clear - D1 Ha. lia.
  - apply (proj1 (HRGI a ltac:(right; left; exact Ha))).
  - clear - D5 Ha. lia.
  - apply (GI (rg_nout RG) 8); [unfold G_RIG, G_DR, G_SL; right; right; right; right; left; reflexivity | exact Ha].
  - clear - D6 Ha. lia.
  - apply (GI (rg_capout RG) 8); [unfold G_RIG, G_DR, G_SL; right; right; right; right; right; left; reflexivity | exact Ha].
  - clear - D7 Ha. lia.
  - apply (GI (rg_out RG) 8); [unfold G_RIG, G_DR, G_SL; right; right; right; right; right; right; left; reflexivity | exact Ha].
  - clear - D8 Ha. lia.
  - apply (proj1 (HRGI a ltac:(right; right; left; exact Ha))).
  - clear - D9 Ha. lia.
  - apply (GI (rg_client_broken RG) 1); [unfold G_RIG, G_DR, G_SL; right; right; left; reflexivity | exact Ha].
  - clear - D10 Ha. lia.
  - apply (proj1 (HRGI a ltac:(right; right; right; exact Ha))).
  - clear - D11 Ha. lia.
  - apply (GI (rg_send_eintr RG) 1); [unfold G_RIG, G_DR, G_SL; right; right; right; left; reflexivity | exact Ha].
  - clear - D12 Ha. lia.
  - apply (GI (as_errno B) 4); [unfold G_RIG, G_DR, G_SL; right; right; right; right; right; right; right; left; reflexivity | exact Ha].
  - clear - D14 Ha. lia. }
assert (AKR : forall G es, arelay_at B RG ly1 S1 W1 m1 G es -> akept W1 m1 W1 (ms_mem ms2) (arelay_fp RG G es)).
{ intros G es HR r Hr a Ha. destruct (tl_arelay_fp _ _ _ _ _ _ HR r Hr a Ha) as [Hg | Hb]; [|exact (KBLK a Hb)].
  apply GLOB. destruct Hg as [Hg | [Hg | Hg]]; [left | right; left | right; right; left]; exact Hg. }
assert (AKO : forall c O mx no cap out, aout_at B RG ly1 S1 W1 m1 c O mx no cap out ->
  akept W1 m1 W1 (ms_mem ms2) (aout_fp B RG cap out)).
{ intros c O mx no cap out HO r Hr a Ha. destruct (tl_aout_fp _ _ _ _ _ _ _ _ _ _ HO r Hr a Ha) as [Hg | Hb]; [|exact (KBLK a Hb)].
  apply GLOB. right; right; right; right. exact Hg. }
assert (AKS : forall (j : nat) h, (j < 4)%nat -> asrc_at B ly1 S1 W1 m1 (rg_s RG + ASRC * Z.of_nat j) h ->
  akept W1 m1 W1 (ms_mem ms2) (asrc_fp (rg_s RG + ASRC * Z.of_nat j) h)).
{ intros j h Hj HSr r Hr a Ha. destruct (tl_asrc_fp _ _ _ _ _ _ HSr r Hr a Ha) as [Hg | Hb]; [|exact (KBLK a Hb)].
  apply GLOB. right; right; right; left. unfold ASRC in *. lia. }
(* ---- rig_post ---- *)
assert (EabF : ablocks B ly1 (stack_free_state 1 fpos S1) = ablocks B ly1 S1)
by (unfold ablocks; rewrite blocks_stack_free_state; reflexivity).
assert (HFA : firstn (length (gxes cx)) (gps cx) = gps cx)
by (apply firstn_all2; unfold gps; rewrite length_combine, HLEN; lia).
assert (HSK : skipn (length (gxes cx)) (gxes cx) = []) by (apply skipn_all).
assert (HSKp : skipn (length (gxes cx)) (gps cx) = [])
by (apply skipn_all2; unfold gps; rewrite length_combine, HLEN; lia).
rewrite HFA in Hrel, Hgs, Hperm. rewrite HSK, app_nil_r in Hrly. rewrite HSK, app_nil_r, HSKp in Hperm.
unfold gPOST, rig_post_x.
lazymatch goal with |- exists _ _ _ _ _ _ _ _ _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ =>
exists ly1, (stack_free_state 1 fpos S1), Hp1, r, m, d, k1, qd, c2, O2, cap2, out2, (gxrest cx) end.
split.
{ pose proof (EX2 12%nat ltac:(lia)) as X12. cbn [Nat.add nth RIG_SAVED] in X12.
  rewrite R1, X12. unfold ret_ok in Hra. rewrite Hra. reflexivity. }
split.
{ eapply ajournal_gx_pack_x; [rewrite WS; lia | lia | rewrite !Z.add_0_r; apply (ajournal_x_materialize SEGS B PST ARx LAWS Hsegs);
    exact HJ3 | exact Hag3 | intros a Ha; lia]. }
split.
{ intros r Hr. unfold acallee_saved in Hr.
  assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/
    r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  destruct Hr' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]].
  + replace (Z_to_bv 5 2) with (2%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite R2, (EE2 8%nat 8%bv eq_refl), G3_8, H8. unfold w64, gsp0, spZ. apply Z_to_bv_bv_unsigned.
  + replace (Z_to_bv 5 3) with (3%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite R3, (EE2 3%nat 3%bv eq_refl), G3_3. exact Hgp1.
  + replace (Z_to_bv 5 4) with (4%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite R4, (EE2 4%nat 4%bv eq_refl), G3_4. exact Htp1.
  + replace (Z_to_bv 5 8) with (8%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R8. exact (EX2 11%nat ltac:(lia)).
  + replace (Z_to_bv 5 9) with (9%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R9. exact (EX2 10%nat ltac:(lia)).
  + replace (Z_to_bv 5 18) with (18%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R18. exact (EX2 9%nat ltac:(lia)).
  + replace (Z_to_bv 5 19) with (19%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R19. exact (EX2 8%nat ltac:(lia)).
  + replace (Z_to_bv 5 20) with (20%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R20. exact (EX2 7%nat ltac:(lia)).
  + replace (Z_to_bv 5 21) with (21%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R21. exact (EX2 6%nat ltac:(lia)).
  + replace (Z_to_bv 5 22) with (22%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R22. exact (EX2 5%nat ltac:(lia)).
  + replace (Z_to_bv 5 23) with (23%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R23. exact (EX2 4%nat ltac:(lia)).
  + replace (Z_to_bv 5 24) with (24%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R24. exact (EX2 3%nat ltac:(lia)).
  + replace (Z_to_bv 5 25) with (25%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R25. exact (EX2 2%nat ltac:(lia)).
  + replace (Z_to_bv 5 26) with (26%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R26. exact (EX2 1%nat ltac:(lia)).
  + replace (Z_to_bv 5 27) with (27%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R27. exact (EX2 0%nat ltac:(lia)). }
split.
{ intros a Hi Ho He Hp. apply P2e, P13. exact (HPK a Hi Ho He Hp). }
assert (GR0 : grest cx (length (gxes cx)) (Z.of_nat (length O2)) cap2 = []).
{ unfold grest. rewrite !skipn_all2 by (rewrite ?HLEN; lia). reflexivity. }
split.
{ destruct Hbud as (Hmo & Hsp0 & Hsc & _ & _).
  rewrite GR0 in Hsc. change (tr_cost MT []) with 0 in Hsc.
  apply (mle_weaken MT _ _ (spent + 0)); [exact MLAW | | unfold gtr in Hsc; lia].
  (* the release's state is a set_fs of S1 (YG01.v stack_free_state): MO_FR at (S1, its fake stack) *)
  exact (mle_station MT _ S1 _ spent 0 MLAW Hmo
    (MO_FR S1 (mkFS (fs_hint (st_fs S1)) (del_pos (fs_live (st_fs S1)) 1 fpos)))). }
(* the room round: gbud's room at the empty remaining trace is the entry's budget gxkr; the release's state is a
   set_fs of S1 (YG01.v stack_free_state), which keeps the room (RPF_stack_free) *)
split.
{ destruct Hbud as (_ & _ & _ & _ & _ & Hrm & _).
  rewrite GR0 in Hrm. change (tr_cost MT_rk []) with 0 in Hrm. cbn [Z.to_nat Nat.add] in Hrm.
  exact (RPF_stack_free RP S1 1 fpos (gxkr cx) Hrm). }
split.
{ split; [|split; [|split]].
  - apply (akept_vm W1 m1 W1 (ms_mem ms2) (rg_lock RG) 4 0); [|exact LK0].
    intros x Hx. cbn in Hx. apply KIMG; [exact (proj1 (LKI x ltac:(lia))) | lia].
  - change (if false then 16 else 0) with 0. unfold arm.
    apply (val_mem_kept SEGS (w_H W1) (w_H W1) mem3 (ms_mem ms2) _ 4 _); [|exact HLK3].
    intros kk Hk. cbn in Hk. pose proof (LKI (rg_lock RG + 4 + kk) ltac:(lia)) as (Hi & _ & _).
    pose proof (Hsegs _ Hi) as Hlo. rewrite C5 in Hlo.
    apply K2e; [lia | intros Hx; exact (NIMG _ (or_introl Hx) Hi) | rewrite SF; revert Hlo HF4096 HF8 HF8m; clear; intros; lia
      | intros Hx; rewrite Hx in Hi; exact (NIMG FL (or_intror eq_refl) Hi)].
  - apply (akept_vm W1 m1 W1 (ms_mem ms2) (rg_lock RG + 8) 4 0); [|exact LK8].
    intros x Hx. cbn in Hx. apply KIMG; [exact (proj1 (LKI x ltac:(lia))) | lia].
  - intros i Hi. unfold arm. apply (writable_kept (w_H W1) m1 (ms_mem ms2)); [intros Hp; apply P2e, P13, Hp | exact (LKW i Hi)]. }
split; [exact Hrel|].
split; [exact Hlq|].
split.
{ apply (arelay_at_kept B RG ly1 S1 W1 m1 ly1 _ W1 (ms_mem ms2) _ _ Hrly); [exact (AKR _ _ Hrly)|].
  intros b Hb. rewrite EabF. exact (tl_arelay_blks _ _ _ _ _ _ Hrly b Hb). }
split.
{ apply (aout_at_kept B RG ly1 S1 W1 m1 ly1 _ W1 (ms_mem ms2) _ _ _ _ _ _ Hout); [exact (AKO _ _ _ _ _ _ Hout)|].
  intros b Hb. rewrite EabF. exact (tl_aout_blks _ _ _ _ _ _ _ _ _ _ Hout b Hb). }
split.
{ intros i Hi Heof.
  pose proof (Hsrc i Hi Heof) as HSi. unfold gslot, ghj in HSi.
  assert (Hj4 : (snd (nth i (gxhs cx) relay_instance_gone_b_c.no_hj) < 4)%nat).
  { rewrite Forall_forall in HDRS0.
    assert (Hin : In (nth i (gps cx) (relay_remove_b_c.no_entry, relay_instance_gone_b_c.no_hj)) (gps cx))
    by (apply nth_In; unfold gps; rewrite length_combine, HLEN; lia).
    pose proof (HDRS0 _ Hin) as Hd. unfold gps in Hd. rewrite combine_nth in Hd by exact (eq_sym HLEN).
    cbn [fst snd] in Hd. exact (proj1 (Hd Heof)). }
  apply (asrc_at_kept B ly1 S1 W1 m1 ly1 _ W1 (ms_mem ms2) _ _ HSi); [exact (AKS _ _ Hj4 HSi)|].
  intros b Hb. rewrite EabF. exact (tl_asrc_blks _ _ _ _ _ _ HSi b Hb). }
split.
{ intros a Ha Hnj.
  apply (tl_kept_trans (gxW cx) W1 W1 (gxmem cx) m1 (ms_mem ms2) a); [exact (Hgs a Ha Hnj)|].
  apply GLOB. right; right; right; left. exact Ha. }
split; [exact HPERM0|].
rewrite EabF. exact Hperm.
Qed.

(* ---- route R (G8 rig, A): TAIL over a world relation R, concluding W_relay_instance_gone_cx.v Section wR's
   rig_tail_stmt_xR.  The runs go through W_frame_x.v's G twins at R (RUNPR, RUNCR, RUNFR); the unlock is bound by
   SRrG_bind and entered by W_sites_x.v aj_gx_entry_at_xR (its contract AUNLOCK stays strict); the final ret is the
   strict RET, lifted by SRr_SRrG (WLE_R). ---- *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Let RUNPR := SRrG_run_pi_AJ_xG (PL := PL_fr) B PST ARx LAWS (R := R).
Let RUNCR := SRrG_run_pi_AJ_call_xG (PL := PL_fr) B PST ARx LAWS (R := R).
Let RUNFR := aj_flag_store_pi_xG (PL := PL_fr) B PST ARx LAWS ASF FFL WFx WFL SFREE (R := R).

(* W_rig_tail.v:497 rig_tail at R *)
Theorem rig_tail_xR : rig_tail_stmt_xR B PST ARx MT RP MMAX RG R.
Proof.
unfold rig_tail_stmt_xR. intros cx W1 c1 HB HU.
destruct HU as (regs1 & ly1 & S1 & m1 & md1 & k1 & F & FL & qd & c2 & O2 & cap2 & out2 & spent & -> & HRB & H21 & HGL & HGO).
destruct HGL as (fpos & Hp1 & HJ & HROM1 & HPK & HFR & HLK).
destruct HFR as (HFa & HFl & HFL120 & HS16 & HS24 & HS80 & HSV).
destruct HRB as (Hsp1 & Hgp1 & Htp1 & H8 & H9 & H18).
destruct HB as (HPRE & H32 & HCNT & RGP & H10 & RID & HLK0 & HREL0 & HOUT0 & HROM0 & HLEN & HDRS0 & HND & HPERM0 & HTRM & HLIVE & HMOK
  & HRMB & HCKB).
destruct RGP as (RGLOCK & RGNSRC & RGSRC & RGAL8 & RGAL4 & RGSAL & RGIMG & RGWR & RGSEP).
destruct HGO as (Hle & Hlq & Hrel & Hrly & Hout & Hsrc & Hdrs & Hgs & Hperm & Hbud).
destruct HJ as (HSTK & _ & (memS & HJi & Hag) & _).
rewrite !Z.add_0_r in HJi.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : RIG_STK_x = 17200) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & _ & _ & _).
pose proof HJi as (HAR1 & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres1 & Hstatic & _ & _).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _ & _ & _).
assert (SP1 : spZ regs1 = gsp0 cx - 224) by (rewrite Hsp1; reflexivity).
assert (SPR : alloc_ceiling + 12880 <= gsp0 cx - 4320 /\ gsp0 cx <= 2 ^ 47) by (unfold gsp0 in *; rewrite WS in Hslo; lia).
(* the frame (1, fpos), its shadow and its flag cell at S1 *)
assert (Hfin : In (1, fpos) (frames S1)) by (rewrite Hfrs; left; reflexivity).
destruct (alx_frames _ _ _ LAWS _ _ _ _ _ _ 1 fpos HAR1 Hfin) as (HFal & HFapp & HFpres & HFSpres).
destruct (FFL _ _ _ _ _ _ 1 fpos HAR1 Hfin) as (HFLp & HFLo & (HFLapp & HFLimg) & (HFL4096 & HFLz & HFLc)).
destruct (frames_bounds_x SEGS B ARx LAWS _ _ _ _ _ _ 1 fpos HAR1 Hfin) as (HF4096 & HFceil & HFhigh).
change (fs_frame_bytes 1) with 128 in *. change (128 / 8) with 16 in *.
rewrite HFa, HFl in *.
assert (HFLF : ~ (F <= FL < F + 128)) by (intros Hx; exact (proj2 (HFpres FL Hx) HFLo)).
assert (HFLS : ~ (shadow_addr F <= FL < shadow_addr F + 16)).
{ intros Hx. apply (proj2 (HFSpres (FL - shadow_addr F) ltac:(lia))).
  replace (shadow_addr F + (FL - shadow_addr F)) with FL by lia. exact HFLo. }
assert (HF8 : F = 8 * (F / 8) + F mod 8) by (apply Z.div_mod; lia).
pose proof (Z.mod_pos_bound F 8 ltac:(lia)) as HF8m.
assert (SF : shadow_addr F = 2147450880 + F / 8) by (unfold shadow_addr, SHADOW_OFF; lia).
assert (HFLapp' := HFLapp). unfold app_addr, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFLapp'.
(* the bytes no allocator law lets be image bytes *)
assert (NIMG : forall a, (F <= a < F + 128 \/ a = FL) -> ~ in_img SEGS a).
{ intros a Ha Hi. refine (proj2 (alx_client_img _ _ _ LAWS _ _ _ _ _ _ a HAR1 _) Hi). right.
  destruct Ha as [Ha | ->]; [left | right]; exists 1, fpos; split; try exact Hfin;
  rewrite ?HFa, ?HFl; change (fs_frame_bytes 1) with 128; first [lia | reflexivity]. }
(* ---- SEAT 1 and the run to the call (auipc, addi, jal) ---- *)
unfold cfg_at, w64.
remember (Eimg (Ereg regs1 [])) as E1 eqn:HE1.
pose proof (rt_entry0 W1 regs1 m1) as HS. rewrite <- HE1 in HS.
assert (HEI1 : img_env VAL A_LIM E1) by (subst E1; apply Eimg_env).
assert (EE1 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E1 n = getr regs1 r)
by (intros n r Hn; subst E1; pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5;
rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
clear HE1.
paj_run_shc_x RUNPR RUNCR HS HJi.
{ intros a (r & Hin & _). cbn in Hin. destruct Hin. }
rename ms into ms0, mat into mat0, HF into HF1, HFr into HFr1, HG into HG1.
pmkst HS.
prreg HS (1%bv : bv 5) QRA. prreg HS (2%bv : bv 5) QSP. prreg HS (3%bv : bv 5) QGP. prreg HS (4%bv : bv 5) QTP.
prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (21%bv : bv 5) Q21.
prreg HS (10%bv : bv 5) QA0.
assert (M01 : forall a, aview SEGS (w_H W1) (ms_mem ms0) a = aview SEGS (w_H W1) m1 a).
{ intros a. apply aview_eq_of. apply HFr1. intros (r & Hin & _). cbn in Hin. destruct Hin. }
assert (P01 : forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) (ms_mem ms0) a)
by (intros a Hp; eapply apresent_grows; [exact HG1 | exact Hp]).
assert (HSPc : spZ (ms_regs ms0) = gsp0 cx + -224).
{ unfold spZ at 1. rewrite QSP, (EE1 2%nat 2%bv eq_refl). fold (spZ regs1). lia. }
assert (QA0' : getr (ms_regs ms0) 10 = w64 (rg_lock RG)).
{ rewrite QA0. change 247%nat with (A_OBJ 6). rewrite (img_env_atomP E1 (A_OBJ 6) HEI1 ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
  rewrite RGLOCK. reflexivity. }
(* g_lock's twelve bytes *)
pose proof HLK as (LK0 & LK4 & LK8 & LKW). unfold arm in LK0, LK4, LK8, LKW.
assert (LKI : forall a, rg_lock RG <= a < rg_lock RG + 12 ->
  in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4))
by (intros a Ha; apply RGIMG; unfold rg_rng; tauto).
assert (LKV : forall a, rg_lock RG <= a < rg_lock RG + 12 -> aview SEGS (w_H W1) m1 a <> None).
{ intros a Ha. unfold aview.
  destruct (Z_lt_ge_dec a (rg_lock RG + 4)) as [h1|h1]; [|destruct (Z_lt_ge_dec a (rg_lock RG + 8)) as [h2|h2]].
  - pose proof (LK0 (Z.to_nat (a - rg_lock RG)) ltac:(lia)) as X. rewrite Z2Nat.id in X by lia.
    replace (rg_lock RG + (a - rg_lock RG)) with a in X by lia. rewrite X. discriminate.
  - pose proof (LK4 (Z.to_nat (a - (rg_lock RG + 4))) ltac:(lia)) as X. rewrite Z2Nat.id in X by lia.
    replace (rg_lock RG + 4 + (a - (rg_lock RG + 4))) with a in X by lia. rewrite X. discriminate.
  - pose proof (LK8 (Z.to_nat (a - (rg_lock RG + 8))) ltac:(lia)) as X. rewrite Z2Nat.id in X by lia.
    replace (rg_lock RG + 8 + (a - (rg_lock RG + 8))) with a in X by lia. rewrite X. discriminate. }
assert (LKlo : forall a, rg_lock RG <= a < rg_lock RG + 12 -> 0 <= a < kLowMemEnd)
by (intros a Ha; exact (Hsegs a (proj1 (LKI a Ha)))).
eassert (HJX : ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_RIG B RG) 0 [] RIG_STK_x (gsp0 cx) (gFP cx)
  (gxly cx) (gxS cx) (gxHp cx) (gxW cx) (gxmem cx) (gxmd cx) [(1, fpos)] ly1 S1 Hp1 W1 (ms_mem ms0) _ k1).
{ eapply ajournal_gx_pack_xR; [rewrite WS; lia | lia | rewrite !Z.add_0_r; exact HJi | exact Hag | intros a Ha; lia]. }
(* ---- pthread_mutex_unlock (&g_lock) ---- *)
eapply (YA0nH.SRrG_bind SEGS R R_trans).
{ eapply (aj_gx_entry_at_xR B PST ARx LAWS R_trans WLE_R (G_RIG B RG) 0 [] ESTACK (SIGMA WS_pthread_mutex_unlock)
    (fun a => rg_lock RG + 4 <= a < rg_lock RG + 8)
    (fun (regs' : bvmap 5 word) (mem' : word -> option byte) =>
       getr regs' 10 = w64 0 /\ val_mem SEGS (mrestrict (w_H W1) mem') (rg_lock RG + 4) 4 0)
    W1 _ _ RIG_STK_x (gsp0 cx) (gFP cx) (gxly cx) (gxS cx) (gxHp cx) (gxW cx) (gxmem cx) (gxmd cx) _ _ _ _ _ _ (-224) _ HGRIG eq_refl HJX).
  - exact HSPc.
  - reflexivity.
  - lia.
  - lia.
  - rewrite WS, Hes. lia.
  - rewrite QGP, (EE1 3%nat 3%bv eq_refl), Hgp1. exact Hgp.
  - rewrite QTP, (EE1 4%nat 4%bv eq_refl), Htp1. exact Htp.
  - exact QRA.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros a. destruct (Z_lt_ge_dec a (rg_lock RG + 4)); [right; lia|].
    destruct (Z_lt_ge_dec a (rg_lock RG + 8)); [left; lia | right; lia].
  - intros a Ha _. rewrite (M01 a). exact (LKV a ltac:(lia)).
  - intros a Ha HnG. exfalso. apply HnG. unfold G_RIG. apply inG_cons. left. unfold in_zr. cbn [fst snd]. lia.
  - intros HPRE2 HSC. apply (AUNLOCK _ _ _ _ _ _ _ (rg_lock RG) HPRE2).
    + exact QA0'.
    + pose proof (LKlo (rg_lock RG) ltac:(lia)). pose proof (Hsegs _ (proj1 (LKI (rg_lock RG) ltac:(lia)))).
      destruct (Z.eq_dec (rg_lock RG) 0) as [E0|E0]; [|lia].
      exfalso. pose proof (pa_obj_img 6 ltac:(lia)) as HlkR. rewrite <- RGLOCK in HlkR. lia.
    + pose proof (Z.div_mod (rg_lock RG) 8 ltac:(lia)). pose proof (Z.div_mod (rg_lock RG) 4 ltac:(lia)).
      pose proof (Z.mod_pos_bound (rg_lock RG) 4 ltac:(lia)). lia.
    + pose proof (LKlo (rg_lock RG) ltac:(lia)). unfold kLowMemEnd in *. lia.
    + apply (val_mem_kept SEGS (w_H W1) (w_H W1) m1 (ms_mem ms0) _ 4 _); [intros kk _; apply M01 | exact LK0].
    + apply (val_mem_kept SEGS (w_H W1) (w_H W1) m1 (ms_mem ms0) _ 4 _); [intros kk _; apply M01 | exact LK4].
    + apply (val_mem_kept SEGS (w_H W1) (w_H W1) m1 (ms_mem ms0) _ 4 _); [intros kk _; apply M01 | exact LK8].
    + intros a Ha. split; [rewrite (M01 a); exact (LKV a Ha)|]. rewrite HSPc. pose proof (LKlo a Ha).
      unfold kLowMemEnd in *. unfold ESTACK. lia.
    + intros a Ha. destruct (LKI a ltac:(lia)) as (Hi & Ho & He). split; [|split].
      * apply (RGWR (w_H W1) (ms_mem ms0) a); [left; lia | exact (hidden_not_img SEGS W1 (Z_to_bv 64 a) ltac:(rewrite unsigned_lit_small by (pose proof (LKlo a ltac:(lia)); unfold kLowMemEnd in *; lia); exact Hi))].
      * intros Hown. apply Ho. exact (proj1 (alx_owned_image _ _ _ LAWS _ _ _ _ _ _ a (proj1 HJi) Hi) Hown).
      * rewrite HSPc. pose proof (LKlo a ltac:(lia)). unfold kLowMemEnd in *. unfold ESTACK. lia.
    + intros a Ha HK. refine (proj2 (proj2 (HGRIG a _)) (proj1 (proj2 HK))). unfold G_RIG. apply inG_cons. left. unfold in_zr. cbn [fst snd]. lia. }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJX3 & HP3 & (HA03 & HLK3) & Hfr3 & Hpres3).
(* what the unlock kept *)
assert (K13 : forall a, 0 <= a < 2 ^ 64 -> ~ (rg_lock RG + 4 <= a < rg_lock RG + 8) -> ~ (gsp0 cx - 4320 <= a < gsp0 cx - 224) ->
  aview SEGS (w_H W1) mem3 a = aview SEGS (w_H W1) m1 a).
{ intros a Ha H1 H2. rewrite (Hfr3 a Ha H1 ltac:(unfold ESTACK; lia)). apply M01. }
assert (P13 : forall a, apresent (w_H W1) m1 a -> apresent (w_H W1) mem3 a) by (intros a Hp; apply Hpres3, P01, Hp).
assert (G3 : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs3 r = getr (ms_regs ms0) r)
by (intros r Hr; exact (tl_preserved_at _ _ r HP3 Hr)).
assert (G3_2 : getr regs3 2 = getr regs1 2) by (rewrite (G3 2%bv ltac:(unfold acallee_saved; change (bv_unsigned (2%bv : bv 5)) with 2; lia)), QSP; exact (EE1 2%nat 2%bv eq_refl)).
assert (G3_3 : getr regs3 3 = getr regs1 3) by (rewrite (G3 3%bv ltac:(unfold acallee_saved; change (bv_unsigned (3%bv : bv 5)) with 3; lia)), QGP; exact (EE1 3%nat 3%bv eq_refl)).
assert (G3_4 : getr regs3 4 = getr regs1 4) by (rewrite (G3 4%bv ltac:(unfold acallee_saved; change (bv_unsigned (4%bv : bv 5)) with 4; lia)), QTP; exact (EE1 4%nat 4%bv eq_refl)).
assert (G3_8 : getr regs3 8 = getr regs1 8) by (rewrite (G3 8%bv ltac:(unfold acallee_saved; change (bv_unsigned (8%bv : bv 5)) with 8; lia)), Q8; exact (EE1 8%nat 8%bv eq_refl)).
assert (G3_9 : getr regs3 9 = getr regs1 9) by (rewrite (G3 9%bv ltac:(unfold acallee_saved; change (bv_unsigned (9%bv : bv 5)) with 9; lia)), Q9; exact (EE1 9%nat 9%bv eq_refl)).
assert (G3_21 : getr regs3 21 = getr regs1 21) by (rewrite (G3 21%bv ltac:(unfold acallee_saved; change (bv_unsigned (21%bv : bv 5)) with 21; lia)), Q21; exact (EE1 21%nat 21%bv eq_refl)).
assert (SP3 : spZ regs3 = gsp0 cx - 224) by (unfold spZ; rewrite G3_2; fold (spZ regs1); exact SP1).
assert (V13 : forall a n v, gsp0 cx - 224 <= a -> a + Z.of_nat n <= gsp0 cx ->
  val_mem SEGS (mrestrict (w_H W1) m1) a n v -> val_mem SEGS (mrestrict (w_H W1) mem3) a n v).
{ intros a n v Ha Hn Hv. apply (val_mem_kept SEGS (w_H W1) (w_H W1) m1 mem3 a n v); [|exact Hv].
  intros kk Hk. apply K13; [lia | | lia]. intros Hx. pose proof (LKlo (a + kk) ltac:(lia)). unfold kLowMemEnd in *. lia. }
assert (VF13 : val_mem SEGS (mrestrict (w_H W1) mem3) (F + 120) 8 FL).
{ apply (val_mem_kept SEGS (w_H W1) (w_H W1) m1 mem3 _ 8 _); [|exact HFL120].
  intros kk Hk. apply K13; [lia | | lia]. intros Hx. apply (NIMG (F + 120 + kk) ltac:(cbn in Hk; lia)).
  exact (proj1 (LKI (F + 120 + kk) ltac:(lia))). }
try rewrite QRA. change (BASE + 3268) with (BASE + A_rt_rel).
(* ---- SEAT 2 at 0x82fb0 ---- *)
pose proof (rt_entry W1 regs3 mem3 (gxregs cx) F FL) as HS2.
specialize (HS2 ltac:(rewrite G3_9, H9, SP3; unfold w64, gsp1, RIG_FRAME; rewrite unsigned_lit_small by lia; lia)
  ltac:(rewrite G3_8, H8, SP3; unfold w64; rewrite unsigned_lit_small by lia; lia)
  ltac:(rewrite G3_21; exact H21) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HFal HFapp ltac:(lia) HFLF HFLS
  ltac:(intros o Ho; apply P13; exact (proj1 (HFpres (F + o) ltac:(lia))))
  ltac:(intros o Ho; apply P13; exact (proj1 (HFSpres o Ho)))
  ltac:(apply P13; exact HFLp) VF13
  ltac:(rewrite SP3; apply V13; [lia | cbn; lia | exact HS16])
  ltac:(rewrite SP3; apply V13; [lia | cbn; lia | exact HS24])
  ltac:(intros i Hi; rewrite SP3; apply V13; [lia | cbn; lia |];
        replace (gsp0 cx - 224 + 120 + 8 * Z.of_nat i) with (gsp1 cx + 120 + 8 * Z.of_nat i) by (unfold gsp1, RIG_FRAME; lia);
        exact (HSV i Hi))).
remember (Eimg (Ereg regs3 (rt_extra (gxregs cx) F FL))) as E2 eqn:HE2.
assert (HEI2 : img_env VAL A_LIM E2) by (subst E2; apply Eimg_env).
assert (EE2 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E2 n = getr regs3 r)
by (intros n r Hn; subst E2; pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5;
rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
assert (EX2 : forall i, (i < 13)%nat -> ew E2 (32 + i) = getr (gxregs cx) (nth i RIG_SAVED 0%bv)).
{ intros i Hi. subst E2. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite ew_Ereg_extra. exact (nth_rt_extra _ F FL i Hi). }
assert (U45 : bv_unsigned (ew E2 45) = F)
by (subst E2; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_extra regs3 _ 13); cbn; apply unsigned_lit_small; lia).
assert (U46 : bv_unsigned (ew E2 46) = FL)
by (subst E2; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_extra regs3 _ 14); cbn; apply unsigned_lit_small; lia).
assert (U21 : bv_unsigned (ew E2 21) = shadow_addr F)
by (rewrite (EE2 21%nat 21%bv eq_refl), G3_21, H21; unfold w64; apply unsigned_lit_small; lia).
assert (U9 : bv_unsigned (ew E2 9) = gsp0 cx - 224)
by (rewrite (EE2 9%nat 9%bv eq_refl), G3_9, H9; unfold w64, gsp1, RIG_FRAME; apply unsigned_lit_small; lia).
assert (U8 : bv_unsigned (ew E2 8) = gsp0 cx)
by (rewrite (EE2 8%nat 8%bv eq_refl), G3_8, H8; unfold w64; apply unsigned_lit_small; lia).
clear HE2.
destruct HJX3 as (_ & _ & (memS3 & HJ3 & Hag3) & _).
rewrite !Z.add_0_r in HJ3.
(* ---- the release (retired magic, shadow 0xf5, *FL = 0) and the epilogue, to the ret ---- *)
paj_run_flag_sh_x RUNFR HS2 HJ3.
{ lia. }
{ intros a (r & Hin & Hr).
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
  cbn [In] in Hin. rewrite HFl.
  repeat (destruct Hin as [<- | Hin];
  [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U45, ?U46, ?U21, ?U9, ?U8 in Hr;
    first [ lia
    | right; lia
    | left; right; right; right; exists 1, fpos; split; [left; reflexivity|]; rewrite HFa;
      change (fs_frame_bytes 1) with 128; change (128 / 8) with 16;
      first [ left; unfold in_zr; cbn [fst snd]; lia
      | right; unfold in_zr; cbn [fst snd]; lia ] ]
  | ]).
  destruct Hin. }
{ intros msr HSr. rewrite HFl.
  lazymatch type of HSr with st_ok_pi _ _ ?Ex ?ssx _ =>
  pose proof (st_ok_pi_region_nth Ex ssx msr 0 _ HSr eq_refl) as HR;
  lazymatch type of HR with region_ok _ _ _ (YP09.mkRegion (Some ?n) ?lo ?hi ?wlo ?whi ?cs) =>
  pose proof (field_of_region Ex (ms_mem msr) n _ cs lo hi wlo whi 0 1%N (SLit 0) 0 HR U46
  ltac:(left; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V end end.
  rewrite Z.add_0_r in V. pose proof (V 0%nat ltac:(lia)) as V0. cbn [Z.of_nat] in V0. rewrite Z.add_0_r in V0. exact V0. }
rename ms into ms2, mat into mat2, HF into HF2, HFr into HFr2, HG into HG2.
prreg HS2 (1%bv : bv 5) R1. prreg HS2 (2%bv : bv 5) R2. prreg HS2 (3%bv : bv 5) R3. prreg HS2 (4%bv : bv 5) R4.
prreg HS2 (8%bv : bv 5) R8. prreg HS2 (9%bv : bv 5) R9. prreg HS2 (18%bv : bv 5) R18. prreg HS2 (19%bv : bv 5) R19.
prreg HS2 (20%bv : bv 5) R20. prreg HS2 (21%bv : bv 5) R21. prreg HS2 (22%bv : bv 5) R22. prreg HS2 (23%bv : bv 5) R23.
prreg HS2 (24%bv : bv 5) R24. prreg HS2 (25%bv : bv 5) R25. prreg HS2 (26%bv : bv 5) R26. prreg HS2 (27%bv : bv 5) R27.
apply (YA0nH.SRr_SRrG SEGS R WLE_R).
eapply (RET W1 _ _ _ _ _ HS2 eq_refl ltac:(vm_compute; reflexivity)).
intros matR.
(* ---- what the tail kept: every byte but g_lock + 4 .. + 8, unlock's scratch, F, F's shadow and FL ---- *)
cbn [ms_mem mkst] in HF2, HFr2, HG2.
assert (NWR : forall a, ~ (F <= a < F + 128) -> ~ (shadow_addr F <= a < shadow_addr F + 16) -> a <> FL ->
  ~ in_wrange E2 (ss_mem ss_rt) a).
{ intros a N1 N2 N3 (r & Hin & Hr).
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [<- | Hin];
  [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U45, ?U46, ?U21, ?U9, ?U8 in Hr; lia | ]).
  destruct Hin. }
assert (K2e : forall a, 0 <= a < 2 ^ 64 -> ~ (F <= a < F + 128) -> ~ (shadow_addr F <= a < shadow_addr F + 16) -> a <> FL ->
  aview SEGS (w_H W1) (ms_mem ms2) a = aview SEGS (w_H W1) mem3 a)
by (intros a Ha N1 N2 N3; exact (aview_kept_out E2 (ss_mem ss_rt) (w_H W1) mem3 (ms_mem ms2) HFr2 a Ha (NWR a N1 N2 N3))).
assert (P2e : forall a, apresent (w_H W1) mem3 a -> apresent (w_H W1) (ms_mem ms2) a)
by (intros a Hp; eapply apresent_grows; [exact HG2 | exact Hp]).
assert (KALL : forall a, 0 <= a < 2 ^ 64 -> ~ (rg_lock RG + 4 <= a < rg_lock RG + 8) ->
  ~ (gsp0 cx - 4320 <= a < gsp0 cx - 224) -> ~ (F <= a < F + 128) -> ~ (shadow_addr F <= a < shadow_addr F + 16) ->
  a <> FL -> abyte_kept W1 m1 W1 (ms_mem ms2) a).
{ intros a Ha N0 N1 N2 N3 N4. split.
  - rewrite (K2e a Ha N2 N3 N4). exact (K13 a Ha N0 N1).
  - unfold arm. apply writable_kept. intros Hp. apply P2e, P13, Hp. }
assert (KIMG : forall a, in_img SEGS a -> ~ (rg_lock RG + 4 <= a < rg_lock RG + 8) -> abyte_kept W1 m1 W1 (ms_mem ms2) a).
{ intros a Hi Hl. pose proof (Hsegs a Hi) as Ha. rewrite C5 in Ha. apply KALL; try exact Hl.
  - lia.
  - destruct SPR as [SPa SPb]. revert Ha SPa C1. clear. intros. lia.
  - intros Hx. exact (NIMG a (or_introl Hx) Hi).
  - rewrite SF. revert Ha HF4096 HF8 HF8m. clear. intros. lia.
  - intros ->. exact (NIMG FL (or_intror eq_refl) Hi). }
assert (KBLK : forall a, tinb ly1 S1 a -> abyte_kept W1 m1 W1 (ms_mem ms2) a).
{ intros a (p & n & Hin & Ha).
  destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ p n HAR1 Hin) as (_ & Hp4 & Hpc & Happ & Hpo & _).
  pose proof (sep_block_frame_x SEGS B ARx LAWS _ _ _ _ _ _ p n 1 fpos HAR1 Hin Hfin) as Hd.
  rewrite HFa in Hd. change (fs_frame_bytes 1) with 128 in Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd.
  assert (Hni : ~ in_img SEGS a).
  { intros Hi. refine (proj2 (alx_client_img _ _ _ LAWS _ _ _ _ _ _ a HAR1 _) Hi). left. exists p, n. split; [exact Hin | lia]. }
  apply KALL.
  - lia.
  - intros Hl. apply Hni. exact (proj1 (LKI a ltac:(lia))).
  - destruct SPR as [SPa SPb]. lia.
  - lia.
  - intros Hs. rewrite SF in Hs. apply (fshadow_not_app F 16 p (req_size n) a); [lia | lia | exact Happ | lia | lia].
  - intros ->. exact (proj2 (Hpo FL Ha) HFLo). }
assert (GLOB : forall a,
  (rg_src RG <= a < rg_src RG + 8 \/ rg_nsrc RG <= a < rg_nsrc RG + 4 \/ rg_capsrc RG <= a < rg_capsrc RG + 4 \/
   rg_s RG <= a < rg_s RG + 4 * ASRC \/
   rg_send_max RG <= a < rg_send_max RG + 8 \/ rg_nout RG <= a < rg_nout RG + 8 \/
   rg_capout RG <= a < rg_capout RG + 8 \/ rg_out RG <= a < rg_out RG + 8 \/ rg_client RG <= a < rg_client RG + 4 \/
   rg_client_broken RG <= a < rg_client_broken RG + 1 \/ rg_send_dead RG <= a < rg_send_dead RG + 1 \/
   rg_send_eintr RG <= a < rg_send_eintr RG + 1 \/ as_errno B <= a < as_errno B + 4) ->
  abyte_kept W1 m1 W1 (ms_mem ms2) a).
{ intros a Ha.
  pose proof HRGP as (HL & _). cbn [zall_disjoint] in HL. unfold zdisj in HL. cbn [fst snd] in HL.
  destruct HL as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13 & D14 & _).
  assert (GI : forall x l, In (x, l) (G_RIG B RG) -> x <= a < x + l -> in_img SEGS a).
  { intros x l Hxl Hx. apply (proj1 (HGRIG a ltac:(unfold inG; apply Exists_exists; exists (x, l); split; [exact Hxl | unfold in_zr; cbn [fst snd]; lia]))). }
  assert (RI : rg_rng RG a -> in_img SEGS a) by (intros Hr; exact (proj1 (RGIMG a Hr))).
  unfold rg_rng in RI.
  destruct Ha as [Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|Ha]]]]]]]]]]]]; apply KIMG.
  - apply RI. right; right; left. exact Ha.
  - clear - D2 Ha. lia.
  - apply RI. right; left. exact Ha.
  - clear - D3 Ha. lia.
  - apply (proj1 (HRGI a ltac:(left; exact Ha))).
  - clear - D4 Ha. lia.
  - apply RI. right; right; right; right. exact Ha.
  - clear - D1 Ha. lia.
  - apply (proj1 (HRGI a ltac:(right; left; exact Ha))).
  - clear - D5 Ha. lia.
  - apply (GI (rg_nout RG) 8); [unfold G_RIG, G_DR, G_SL; right; right; right; right; left; reflexivity | exact Ha].
  - clear - D6 Ha. lia.
  - apply (GI (rg_capout RG) 8); [unfold G_RIG, G_DR, G_SL; right; right; right; right; right; left; reflexivity | exact Ha].
  - clear - D7 Ha. lia.
  - apply (GI (rg_out RG) 8); [unfold G_RIG, G_DR, G_SL; right; right; right; right; right; right; left; reflexivity | exact Ha].
  - clear - D8 Ha. lia.
  - apply (proj1 (HRGI a ltac:(right; right; left; exact Ha))).
  - clear - D9 Ha. lia.
  - apply (GI (rg_client_broken RG) 1); [unfold G_RIG, G_DR, G_SL; right; right; left; reflexivity | exact Ha].
  - clear - D10 Ha. lia.
  - apply (proj1 (HRGI a ltac:(right; right; right; exact Ha))).
  - clear - D11 Ha. lia.
  - apply (GI (rg_send_eintr RG) 1); [unfold G_RIG, G_DR, G_SL; right; right; right; left; reflexivity | exact Ha].
  - clear - D12 Ha. lia.
  - apply (GI (as_errno B) 4); [unfold G_RIG, G_DR, G_SL; right; right; right; right; right; right; right; left; reflexivity | exact Ha].
  - clear - D14 Ha. lia. }
assert (AKR : forall G es, arelay_at B RG ly1 S1 W1 m1 G es -> akept W1 m1 W1 (ms_mem ms2) (arelay_fp RG G es)).
{ intros G es HR r Hr a Ha. destruct (tl_arelay_fp _ _ _ _ _ _ HR r Hr a Ha) as [Hg | Hb]; [|exact (KBLK a Hb)].
  apply GLOB. destruct Hg as [Hg | [Hg | Hg]]; [left | right; left | right; right; left]; exact Hg. }
assert (AKO : forall c O mx no cap out, aout_at B RG ly1 S1 W1 m1 c O mx no cap out ->
  akept W1 m1 W1 (ms_mem ms2) (aout_fp B RG cap out)).
{ intros c O mx no cap out HO r Hr a Ha. destruct (tl_aout_fp _ _ _ _ _ _ _ _ _ _ HO r Hr a Ha) as [Hg | Hb]; [|exact (KBLK a Hb)].
  apply GLOB. right; right; right; right. exact Hg. }
assert (AKS : forall (j : nat) h, (j < 4)%nat -> asrc_at B ly1 S1 W1 m1 (rg_s RG + ASRC * Z.of_nat j) h ->
  akept W1 m1 W1 (ms_mem ms2) (asrc_fp (rg_s RG + ASRC * Z.of_nat j) h)).
{ intros j h Hj HSr r Hr a Ha. destruct (tl_asrc_fp _ _ _ _ _ _ HSr r Hr a Ha) as [Hg | Hb]; [|exact (KBLK a Hb)].
  apply GLOB. right; right; right; left. unfold ASRC in *. lia. }
(* ---- rig_post ---- *)
assert (EabF : ablocks B ly1 (stack_free_state 1 fpos S1) = ablocks B ly1 S1)
by (unfold ablocks; rewrite blocks_stack_free_state; reflexivity).
assert (HFA : firstn (length (gxes cx)) (gps cx) = gps cx)
by (apply firstn_all2; unfold gps; rewrite length_combine, HLEN; lia).
assert (HSK : skipn (length (gxes cx)) (gxes cx) = []) by (apply skipn_all).
assert (HSKp : skipn (length (gxes cx)) (gps cx) = [])
by (apply skipn_all2; unfold gps; rewrite length_combine, HLEN; lia).
rewrite HFA in Hrel, Hgs, Hperm. rewrite HSK, app_nil_r in Hrly. rewrite HSK, app_nil_r, HSKp in Hperm.
unfold gPOST_xR, W_contract_xR_relay.rig_post_xR.
lazymatch goal with |- exists _ _ _ _ _ _ _ _ _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ =>
exists ly1, (stack_free_state 1 fpos S1), Hp1, r, m, d, k1, qd, c2, O2, cap2, out2, (gxrest cx) end.
split.
{ pose proof (EX2 12%nat ltac:(lia)) as X12. cbn [Nat.add nth RIG_SAVED] in X12.
  rewrite R1, X12. unfold ret_ok in Hra. rewrite Hra. reflexivity. }
split.
{ eapply ajournal_gx_pack_xR; [rewrite WS; lia | lia | rewrite !Z.add_0_r; apply (ajournal_x_materializeR SEGS B PST ARx LAWS Hsegs);
    exact HJ3 | exact Hag3 | intros a Ha; lia]. }
split.
{ intros r Hr. unfold acallee_saved in Hr.
  assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/
    r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  destruct Hr' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]].
  + replace (Z_to_bv 5 2) with (2%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite R2, (EE2 8%nat 8%bv eq_refl), G3_8, H8. unfold w64, gsp0, spZ. apply Z_to_bv_bv_unsigned.
  + replace (Z_to_bv 5 3) with (3%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite R3, (EE2 3%nat 3%bv eq_refl), G3_3. exact Hgp1.
  + replace (Z_to_bv 5 4) with (4%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite R4, (EE2 4%nat 4%bv eq_refl), G3_4. exact Htp1.
  + replace (Z_to_bv 5 8) with (8%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R8. exact (EX2 11%nat ltac:(lia)).
  + replace (Z_to_bv 5 9) with (9%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R9. exact (EX2 10%nat ltac:(lia)).
  + replace (Z_to_bv 5 18) with (18%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R18. exact (EX2 9%nat ltac:(lia)).
  + replace (Z_to_bv 5 19) with (19%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R19. exact (EX2 8%nat ltac:(lia)).
  + replace (Z_to_bv 5 20) with (20%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R20. exact (EX2 7%nat ltac:(lia)).
  + replace (Z_to_bv 5 21) with (21%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R21. exact (EX2 6%nat ltac:(lia)).
  + replace (Z_to_bv 5 22) with (22%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R22. exact (EX2 5%nat ltac:(lia)).
  + replace (Z_to_bv 5 23) with (23%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R23. exact (EX2 4%nat ltac:(lia)).
  + replace (Z_to_bv 5 24) with (24%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R24. exact (EX2 3%nat ltac:(lia)).
  + replace (Z_to_bv 5 25) with (25%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R25. exact (EX2 2%nat ltac:(lia)).
  + replace (Z_to_bv 5 26) with (26%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R26. exact (EX2 1%nat ltac:(lia)).
  + replace (Z_to_bv 5 27) with (27%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R27. exact (EX2 0%nat ltac:(lia)). }
split.
{ intros a Hi Ho He Hp. apply P2e, P13. exact (HPK a Hi Ho He Hp). }
assert (GR0 : grest cx (length (gxes cx)) (Z.of_nat (length O2)) cap2 = []).
{ unfold grest. rewrite !skipn_all2 by (rewrite ?HLEN; lia). reflexivity. }
split.
{ destruct Hbud as (Hmo & Hsp0 & Hsc & _ & _).
  rewrite GR0 in Hsc. change (tr_cost MT []) with 0 in Hsc.
  apply (mle_weaken MT _ _ (spent + 0)); [exact MLAW | | unfold gtr in Hsc; lia].
  (* the release's state is a set_fs of S1 (YG01.v stack_free_state): MO_FR at (S1, its fake stack) *)
  exact (mle_station MT _ S1 _ spent 0 MLAW Hmo
    (MO_FR S1 (mkFS (fs_hint (st_fs S1)) (del_pos (fs_live (st_fs S1)) 1 fpos)))). }
(* the room round: gbud's room at the empty remaining trace is the entry's budget gxkr; the release's state is a
   set_fs of S1 (YG01.v stack_free_state), which keeps the room (RPF_stack_free) *)
split.
{ destruct Hbud as (_ & _ & _ & _ & _ & Hrm & _).
  rewrite GR0 in Hrm. change (tr_cost MT_rk []) with 0 in Hrm. cbn [Z.to_nat Nat.add] in Hrm.
  exact (RPF_stack_free RP S1 1 fpos (gxkr cx) Hrm). }
split.
{ split; [|split; [|split]].
  - apply (akept_vm W1 m1 W1 (ms_mem ms2) (rg_lock RG) 4 0); [|exact LK0].
    intros x Hx. cbn in Hx. apply KIMG; [exact (proj1 (LKI x ltac:(lia))) | lia].
  - change (if false then 16 else 0) with 0. unfold arm.
    apply (val_mem_kept SEGS (w_H W1) (w_H W1) mem3 (ms_mem ms2) _ 4 _); [|exact HLK3].
    intros kk Hk. cbn in Hk. pose proof (LKI (rg_lock RG + 4 + kk) ltac:(lia)) as (Hi & _ & _).
    pose proof (Hsegs _ Hi) as Hlo. rewrite C5 in Hlo.
    apply K2e; [lia | intros Hx; exact (NIMG _ (or_introl Hx) Hi) | rewrite SF; revert Hlo HF4096 HF8 HF8m; clear; intros; lia
      | intros Hx; rewrite Hx in Hi; exact (NIMG FL (or_intror eq_refl) Hi)].
  - apply (akept_vm W1 m1 W1 (ms_mem ms2) (rg_lock RG + 8) 4 0); [|exact LK8].
    intros x Hx. cbn in Hx. apply KIMG; [exact (proj1 (LKI x ltac:(lia))) | lia].
  - intros i Hi. unfold arm. apply (writable_kept (w_H W1) m1 (ms_mem ms2)); [intros Hp; apply P2e, P13, Hp | exact (LKW i Hi)]. }
split; [exact Hrel|].
split; [exact Hlq|].
split.
{ apply (arelay_at_kept B RG ly1 S1 W1 m1 ly1 _ W1 (ms_mem ms2) _ _ Hrly); [exact (AKR _ _ Hrly)|].
  intros b Hb. rewrite EabF. exact (tl_arelay_blks _ _ _ _ _ _ Hrly b Hb). }
split.
{ apply (aout_at_kept B RG ly1 S1 W1 m1 ly1 _ W1 (ms_mem ms2) _ _ _ _ _ _ Hout); [exact (AKO _ _ _ _ _ _ Hout)|].
  intros b Hb. rewrite EabF. exact (tl_aout_blks _ _ _ _ _ _ _ _ _ _ Hout b Hb). }
split.
{ intros i Hi Heof.
  pose proof (Hsrc i Hi Heof) as HSi. unfold gslot, ghj in HSi.
  assert (Hj4 : (snd (nth i (gxhs cx) relay_instance_gone_b_c.no_hj) < 4)%nat).
  { rewrite Forall_forall in HDRS0.
    assert (Hin : In (nth i (gps cx) (relay_remove_b_c.no_entry, relay_instance_gone_b_c.no_hj)) (gps cx))
    by (apply nth_In; unfold gps; rewrite length_combine, HLEN; lia).
    pose proof (HDRS0 _ Hin) as Hd. unfold gps in Hd. rewrite combine_nth in Hd by exact (eq_sym HLEN).
    cbn [fst snd] in Hd. exact (proj1 (Hd Heof)). }
  apply (asrc_at_kept B ly1 S1 W1 m1 ly1 _ W1 (ms_mem ms2) _ _ HSi); [exact (AKS _ _ Hj4 HSi)|].
  intros b Hb. rewrite EabF. exact (tl_asrc_blks _ _ _ _ _ _ HSi b Hb). }
split.
{ intros a Ha Hnj.
  apply (tl_kept_trans (gxW cx) W1 W1 (gxmem cx) m1 (ms_mem ms2) a); [exact (Hgs a Ha Hnj)|].
  apply GLOB. right; right; right; left. exact Ha. }
split; [exact HPERM0|].
rewrite EabF. exact Hperm.
Qed.
End wR.


End c.
End b.
End a.
