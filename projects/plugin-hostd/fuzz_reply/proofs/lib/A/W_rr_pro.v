(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: SEGMENT PRO of the ASan walk of fuzz_reply's relay_remove (fuzz_reply.asan
   0x83de4 .. 0x83f14), against W_relay_remove_cx.v's rr_pro_stmt, in the form of lib/A/W_relay_remove.v (whose
   prologue, fake-frame seat and fd < 0 arm it takes) and of W5's lib/A/W_relay_add.v (the lock call).
   The prologue saves eleven registers, takes the class-0 fake frame from __asan_stack_malloc_0 and poisons its
   header; fd < 0 releases the frame (the flag store) and returns (rr_post, nothing changed); else
   pthread_mutex_lock (g_lock), g_nsrc <= 0 goes to the unlock tail (RRU None), and the scan's setup reaches the
   loop head (RRL 0).  Nothing but the frame, the fake frame, its shadow, its flag and g_lock's lock word is
   written, so every representation of the entry is carried to the cut. *)
(* Modified by Theorem Labs, 2026-10: ROUTE (b), STEP 3 (a Theorem Labs lane, lane RR_x): PRO over ARx in the room form (Section c
   is W_relay_remove_cx.v's generic block; the runners, the frame twins and the journal lemmas are their _x forms).  The
   seat is W_frame_x.v's aj_stack_malloc_pres_at_raw_x (S2 = set_fs f S), so RBASE's room budget reaches RHELD by
   RPF_of (the lock keeps S2) and its count fact by the blocks' equality; the fd < 0 arm's rr_post_x budget kr is
   RBASE's by RMM_of, kept across the seat (RPF_of) and the release (RPF_stack_free). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require relay_remove_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_frame W_journal W_sites W_rep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG YGcallx YC80x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_kit_x W_journal_x W_sites_x W_contract_x W_frame_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ReplyCnt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_relay_remove_cx.
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
Section c.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable MT : ameter_ops.
(* the room round (W_journal_x.v Record roomp): the allocator's room invariant and the live counts, after MT *)
Variable RP : roomp.
Variable MMAX : Z.
Variable RG : rep_globals.
(* the free interceptor's caller-context table (one table for free and free(NULL): K0_SITES' CTX_AFREE) *)
Variable CTX_AFREE : list (list Z).
Context {hl : Z}.
(* ---- The Section hypotheses every segment file copies (the names are the contracts'). ---- *)
(* the generic relation's laws and its empty head set (CONVERSION.md (sha256 1015972e02a9; internal record) 1.) *)
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
(* the frame twins' hypotheses (W_frame_x.v): the image cover IMGC (frm_off_imgP_x, blk_off_imgP_x), a live block's
   size non-negative (BLKN, W_kit_x.v), the owned-low law OWNLOW, the model invariant WFx with its law WFL and the two
   facts the twins read off model_laws / stack_malloc_progressP (SFREE, SMALLOC) *)
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
Hypothesis ASMP : astack_malloc_pres_x SEGS B ARx 0.
Hypothesis ASF : astack_free_law_x SEGS B ARx.
Hypothesis FFL : frame_flag_lawP_x SEGS B ARx.
Hypothesis HG : gx_ok SEGS B (G_RR B RG).
(* the register images of g_nsrc / g_src: the auipc's of 0x83ee8 (s7, listing A_HI 59) and 0x83ef8 (s9, A_HI 60).
   The abstract placement does not fix them against the objects (W_rebase.v:7-15); PB_fr discharges both by
   vm_compute, as W_send_line_cx.v's HH17 .. HH24. *)
Hypothesis HH59 : VAL (A_HI 59) = rg_nsrc RG + RR_HI_NSRC.
Hypothesis HH60 : VAL (A_HI 60) = rg_src RG + RR_HI_SRC.
(* g_wake[1], read at 0x83fe0 by PLdHi (A_OBJ 4) (W5's HV4, verbatim) *)
Hypothesis HV4 : VAL (A_OBJ 4) = rg_wake RG + 4.
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
   allocator's calls (W_journal.v ajournal_gx_rom_view) *)
Hypothesis HROMO : rom_out SEGS B (G_RR B RG).
Hypothesis MLAW : ameter_laws MT.
(* the live-state meter does not see the fake frame: its seat and its release are set_fs steps (W8's ruling, the
   lead's KF-COUNT #4: the ablocks form is false at the count meter) *)
Hypothesis MO_FR : forall s f, mo_le MT s (set_fs f s) 0.
(* the runtime entries relay_remove calls, at their SIGMA pcs (W_sites.v / the donor's YG0d.v / W_journal.v) *)
Hypothesis ALOCK : alock_realizes_x B ARx (SIGMA WS_pthread_mutex_lock).
Hypothesis AUNLOCK : aunlock_realizes_x B ARx (SIGMA WS_pthread_mutex_unlock).
Hypothesis AFREE : afree_cf_rule_c_x SEGS B PST ARx MT RP CTX_AFREE.
Hypothesis AMEMCPY : aintrin_realizes_x SEGS B ARx OCpy (SIGMA WS_asan_memcpy).
Hypothesis AMEMCPYS : amemcpy_same_realizes_x B ARx (SIGMA WS_asan_memcpy).
(* the program functions relay_remove calls (W7's drain, W4's gestures_end), by their published _x specs *)
Hypothesis DRAIN : dr_spec_x B PST ARx MT RP MMAX RG (BASE + AF_fr_drain).
Hypothesis GSE : gse_spec_x B PST ARx MT RP MMAX RG (BASE + AF_fr_gestures_end).
(* free (s->buf) at 0x83f94 with s->buf = NULL (an entry with cap 0) *)
Hypothesis AFREEN : afree_null_cf_rule_c_x SEGS B PST ARx MT RP CTX_AFREE.
(* the bytes of " end\0" (.str.4, read-only .rodata), which gse_spec's / ge_spec's premise garr8 (VAL A_lit_end5)
   (bzs END5) needs with rom_view (no zero-shadow fact: the literal's last shadow granule is partial): k3's HEND5L, verbatim (W_drain_cx.v dlit_at form; PB_fr
   by vm_compute) *)
Hypothesis HEND5L : forall k, (k < 5)%nat -> YG0d.in_rom SEGS (VAL A_lit_end5 + Z.of_nat k) /\
  seg_rom SEGS (Z_to_bv 64 (VAL A_lit_end5 + Z.of_nat k)) = nth_error END5 k.
(* The program statics PST hold no byte the walk carries through a journal's image clause, which exempts PST
   (YCbqG.v ajournal_x): no read-only byte (ajournal_gx_rom_view_x) and no byte of the relay's / output's cells or
   errno (rr_gcells, HRGP's list).  At PST := [] both hold trivially (W_relay_finish_h.v's PSTR / PSTC form). *)
Hypothesis PSTR : forall a, in_rom SEGS a -> ~ Exists (in_zr a) PST.
Hypothesis PSTG : forall a, Exists (fun r => fst r <= a < snd r) (rr_gcells B RG) -> ~ Exists (in_zr a) PST.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
(* the plain token runner on the donor journal ajournal_x (commit 3d17f490d56, lib/A/W_relay_finish_h.v's RUN0) *)
Let RUN0 := SRr_run_pi_tok_AJx (SK := SK) wsym SEGS B PST ARx LAWS pa_segs_low pa_wx (clookup pa_tbl) VAL SIGMA
fr_prog_listing (@pl_tpi fr_prog_listing PL_fr) (@pl_tw fr_prog_listing PL_fr) pa_fetch_ok pa_cert pa_B_ok A_LIM
A_LIM_text (@pl_lim fr_prog_listing PL_fr) (@pl_len fr_prog_listing PL_fr) (@pl_tpi_eq fr_prog_listing PL_fr)
(@pl_tw_eq fr_prog_listing PL_fr).
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_fr) (PI := PI).
Let RUNP := SRr_run_pi_AJ_x (PL := PL_fr) B PST ARx LAWS. Let RUNTOP := SRr_run_to_pi_AJ_x (PL := PL_fr) B PST ARx LAWS.
Let RUNC := SRr_run_pi_AJ_call_x (PL := PL_fr) B PST ARx LAWS.
Let RUNF := aj_flag_store_pi_x (PL := PL_fr) B PST ARx LAWS ASF FFL WFx WFL SFREE.

(* ---- The entry state (lib/A/W_relay_remove.v:70-157). ---- *)
Definition Bx : sv := SOff 33 0.
Definition Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition rr_regions0 : smem :=
[ stack_region RR_FRAME; got_regionP; bcell_regionP 33; uar_got_regionP 32; uar_cell_regionP 32 ].
Definition rr_atoms0 : list (nat * afact) :=
[ (2%nat, mkAF (2^46) (2^47) 5); (32%nat, mkAF 0x10000 0x5fb000 2); (33%nat, mkAF SB SB 0) ].
Definition ss_rr0 : sstate := mkSS A_rr_entry sr_atoms rr_regions0 None (mkFacts rr_atoms0 [] []).
Definition rr_extra : list word := map (Z_to_bv 64) [as_uar_cell B; SB].
Lemma rr_entry : forall W ly S Hp regs mem md ch,
afn_pre_x SEGS B ARx RR_STK_x ly S Hp W regs mem md ch -> spZ regs mod 32 = 0 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs rr_extra)) ss_rr0
(restrict (w_H W) (mkst regs (Z_to_bv 64 A_rr_entryP) mem (seg_rom SEGS)))
/\ sh_ok SEGS Bx [] (Eimg (Ereg regs rr_extra)) (mrestrict (w_H W) mem).
Proof.
intros W ly S Hp regs mem md ch HPRE H32.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (FFS : RR_STK_x = 17072) by reflexivity.
destruct (alx_const _ _ _ LAWS ly S Hp W mem md HAR) as (Kcell & Kuar & Kgot & Kguar).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell. rewrite (palf_got_uar B TLF) in Kguar.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs rr_extra)). pose proof pa_B_ok as HBASE.
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 (as_uar_cell B)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E242 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E273 : ew E (A_OBJ 32) = Z_to_bv 64 (VAL (A_OBJ 32))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (pa_obj_img 0 ltac:(lia)) as Hob0. pose proof (pa_obj_img 1 ltac:(lia)) as Hob1. pose proof (pa_obj_img 32 ltac:(lia)) as Hob32.
pose proof (palf_uar_img B TLF) as Huar. pose proof (palf_uar_al B TLF) as Huar4.
pose proof (palf_sep B TLF) as Hsep. cbn [zseps zseps_from fst snd] in Hsep.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
split.
- unfold ss_rr0, A_rr_entryP. apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold rr_regions0, stack_region, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP, RR_FRAME.
    repeat apply Forall_cons; try apply Forall_nil.
    * unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp.
      split; [lia|]. split; [lia|]. split; [|constructor]. intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
    * unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 32) 0) (VAL (A_OBJ 32)));
      [cbn [sv_denot]; rewrite E273, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 32)); zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
    * unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      rewrite (VB (A_OBJ 32) (VAL (A_OBJ 32)) E273) by (pose proof (pa_val_range (A_OBJ 32)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 32)) 0 8 (SOff 33 0) SB);
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
    * unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E242) by (pose proof (pa_val_range (A_OBJ 1)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff 32 0) (as_uar_cell B));
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kguar).
    * unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      rewrite (VB 32%nat (as_uar_cell B) E32) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (as_uar_cell B) 0 4 (SLit 1) 1); [reflexivity | zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rd32 SEGS (w_H W) mem _ _ Kuar).
  + apply pairwise_disjoint_of_extents.
    unfold rr_regions0, stack_region, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP, extent_of_region, RR_FRAME.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite (VB 32%nat (as_uar_cell B) E32) by lia.
    rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
    rewrite (VB (A_OBJ 32) (VAL (A_OBJ 32)) E273) by (pose proof (pa_val_range (A_OBJ 32)); lia).
    rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E242) by (pose proof (pa_val_range (A_OBJ 1)); lia).
    cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    revert Hslo Hshi H47 Hceil C1 C3 FFS Hstk0 Hob0 Hob1 Hob32 Huar Hsep. clear.
    unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros.
    rewrite !Z.add_0_r. repeat match goal with H : _ /\ _ |- _ => destruct H as [? ?] end.
    repeat split; first [ assumption | (apply or_comm; assumption)
    | (repeat match goal with H : pa_val (A_OBJ _) + 8 <= _ \/ _ |- _ => clear H | H : as_uar_cell _ + 4 <= _ \/ _ |- _ => clear H end; lia) ].
  + split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok rr_atoms0]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E32, E33, !unsigned_lit_small by (unfold SB; lia).
    change (2 ^ 5) with 32. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
    revert Hslo Hshi H47 Hceil C1 C3 FFS Hstk0 Hal16 H32 Huar Huar4. clear.
    unfold SB, zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros.
    repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok. constructor.
Qed.
Lemma fd_signed : forall fd, - 2 ^ 31 <= fd < 2 ^ 31 -> bv_signed (Z_to_bv 64 fd) = fd.
Proof.
intros fd Hfd. assert (HU : bv_unsigned (Z_to_bv 64 fd) = if fd <? 0 then fd + 2 ^ 64 else fd).
{ rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
destruct (Z.ltb_spec fd 0); [symmetry; apply (Z.mod_unique fd (2 ^ 64) (-1)); lia | apply Z.mod_small; lia]. }
destruct (Z.ltb_spec fd 0).
- rewrite bv_signed_hi by lia. lia.
- rewrite bv_signed_small by lia. lia.
Qed.
(* The footprint of relay_remove's journal names heap blocks only, so it is closed to the sink. *)
Lemma rr_fp_closed : forall ly S Hp W mem md bl rest,
ARx ly S Hp W mem md -> Permutation (ablocks B ly S) (bl ++ rest) -> ~ YI16.sink_open_fp (ablocks_fp bl).
Proof.
intros ly S Hp W mem md bl rest HAR HP. apply sink_closed_ablocks_fp. apply Forall_forall. intros [p n] Hin.
assert (Hb : In (p, n) (ablocks B ly S)) by (apply (Permutation_in _ (Permutation_sym HP)); apply in_or_app; left; exact Hin).
destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ p n HAR Hb) as (_ & H4096 & _). cbn [fst]. lia.
Qed.

(* YCbq.v:2602 region_kept_stack_aj over YCbqG.v's journal ajournal_x (no kit twin; commit 3d17f490d56,
   lib/A/W_relay_finish_h.v rf_region_kept_stack_aj_x: the same proof, which reads only the journal's stack presence
   and stack geometry and the call's acall_kept frame clause) *)
Lemma rr_region_kept_stack_aj_x : forall E lyc Sc W memc W2 mem2 slo shi (Er : Z -> Prop) n lo hi wlo whi cs sp0 sp
STK FP ly S Hp W0 mem md own ly2 S2 Hp2 md2 k,
acall_kept SEGS B lyc Sc W memc W2 mem2 slo shi Er ->
ajournal_x (SK := SK) SEGS B PST ARx STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 k ->
bv_unsigned (ew E n) = sp -> shi <= sp + lo -> sp0 - STK <= sp + lo -> sp + hi <= sp0 -> lo <= wlo -> whi <= hi ->
region_kept SEGS E (mrestrict (w_H W) memc) (mrestrict (w_H W2) mem2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E lyc Sc W memc W2 mem2 slo shi Er n lo hi wlo whi cs sp0 sp STK FP ly S Hp W0 mem md own ly2 S2 Hp2 md2 k
(K1 & _) HJ Hn Hshi Hlo Hhi Hw1 Hw2.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & (Hal & Hstk0 & Hceil & Hslo & Hsh & H47 & _) & _ & HQT).
pose proof asan_consts as (C1 & _).
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview SEGS). apply K1; zlia.
- intros _. apply (apresent_writable SEGS). apply Hpres. zlia.
Qed.

(* ---- What the walk carries.  It writes the frame, the fake frame, its shadow, its flag and g_lock's lock word
   only; every byte the entry's representations read is an image byte not owned by the runtime or a byte of a live
   block of the entry (rr_wt), and is kept. ---- *)
Definition rr_wt (ly : alayout) (S : astate) (a : Z) : Prop :=
(in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B)) \/
(exists p n, In (p, n) (ablocks B ly S) /\ p <= a < p + req_size n).
Definition rr_lkw (a : Z) : Prop := rg_lock RG + 4 <= a < rg_lock RG + 8.
Lemma rr_wt_blk : forall ly S p n a, In (p, n) (ablocks B ly S) -> p <= a < p + n -> rr_wt ly S a.
Proof.
intros ly S p n a Hin Ha. right. exists p, n. split; [exact Hin|].
destruct (Z_le_gt_dec 0 n) as [Hn | Hn]; [pose proof (req_size_pos n Hn); lia | lia].
Qed.
Lemma rr_wt_lo : forall ly S Hp (W : world SEGS) m md a, ARx ly S Hp W m md -> rr_wt ly S a ->
4096 <= a < alloc_ceiling.
Proof.
intros ly S Hp W m md a HAR [(Hi & _) | (p & n & Hin & Ha)].
- pose proof (pa_img_range a Hi). pose proof asan_consts as (C1 & _). lia.
- destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ p n HAR Hin) as (_ & H4096 & Hceil & _). lia.
Qed.
(* the fake frame (0, fpos), its shadow and its flag hold no watched byte *)
Lemma rr_wt_fr : forall ly S S2 Hp (W : world SEGS) m md fpos a,
ARx ly S2 Hp W m md -> In (0, fpos) (frames S2) -> ablocks B ly S2 = ablocks B ly S -> rr_wt ly S a ->
~ (frame_addr ly 0 fpos <= a < frame_addr ly 0 fpos + 64) /\
~ (SB + frame_addr ly 0 fpos / 8 <= a < SB + frame_addr ly 0 fpos / 8 + 8) /\ a <> flag_addr ly 0 fpos.
Proof.
intros ly S S2 Hp W m md fpos a HAR Hin Eab Hw.
pose proof asan_consts as (C1 & _).
pose proof (frm_off_imgP_x B ARx LAWS IMGC _ _ _ _ _ _ 0 fpos HAR Hin) as HFimg.
destruct (alx_frames _ _ _ LAWS _ _ _ _ _ _ 0 fpos HAR Hin) as (HFal & HFapp & _ & _).
destruct (frames_bounds_x SEGS B ARx LAWS _ _ _ _ _ _ 0 fpos HAR Hin) as (HF4096 & HFceil & _).
destruct (FFL _ _ _ _ _ _ 0 fpos HAR Hin) as (_ & HFLo & (_ & HFLimg) & _).
change (fs_frame_bytes 0) with 64 in *. unfold off_img in HFimg.
set (F := frame_addr ly 0 fpos) in *.
assert (HF8 : 0 <= F / 8 <= 17592184995840) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
destruct Hw as [(Hi & _) | (p & n & Hb & Ha)].
- pose proof (pa_img_range a Hi). split; [lia|]. split; [unfold SB; lia|]. intros ->. exact (HFLimg Hi).
- rewrite <- Eab in Hb.
  destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ p n HAR Hb) as (_ & H4096 & Hceil & Happ & Hown & _).
  pose proof (sep_block_frame_x SEGS B ARx LAWS _ _ _ _ _ _ p n 0 fpos HAR Hb Hin) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (fs_frame_bytes 0) with 64 in Hd. fold F in Hd.
  split; [lia|]. split.
  + unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ, HFapp. unfold SB. lia.
  + intros ->. exact (proj2 (Hown _ Ha) HFLo).
Qed.
(* a watched byte that is not an image byte (a live block's) is none of g_lock's *)
Lemma rr_wt_nlk : forall a, rg_place B RG -> ~ in_img SEGS a -> ~ (rg_lock RG <= a < rg_lock RG + 12).
Proof.
intros a RGP Hni Ha. destruct RGP as (_ & _ & _ & _ & _ & _ & RGIMG & _).
apply Hni. apply (RGIMG a). unfold rg_rng. left. exact Ha.
Qed.
Lemma kv_run : forall E rs (W : world SEGS) mem m1 m2 (P : Z -> Prop),
(forall a, P a -> aview SEGS (w_H W) m1 a = aview SEGS (w_H W) mem a) ->
frame_of E rs (mrestrict (w_H W) m1) (mrestrict (w_H W) m2) ->
(forall a, P a -> 0 <= a < 2 ^ 64 /\ ~ in_wrange E rs a) ->
forall a, P a -> aview SEGS (w_H W) m2 a = aview SEGS (w_H W) mem a.
Proof.
intros E rs W mem m1 m2 P K HF Hn a Ha. destruct (Hn a Ha) as [H1 H2].
rewrite (aview_kept_out E rs (w_H W) m1 m2 HF a H1 H2). exact (K a Ha).
Qed.
Lemma kv_smalloc : forall ly S S2 Hp Hp2 (W : world SEGS) mem m1 m2 md1 md2 lo hi (P : Z -> Prop),
ARx ly S Hp W m1 md1 -> ARx ly S2 Hp2 W m2 md2 -> alloc_ceiling <= lo ->
acall_kept SEGS B ly S W m1 W m2 lo hi (fun _ => False) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ aowned B ly S a -> ~ aowned B ly S2 a -> ~ (lo <= a < hi) ->
 aview SEGS (w_H W) m2 a = aview SEGS (w_H W) m1 a) ->
(forall a, P a -> rr_wt ly S a) ->
(forall a, P a -> aview SEGS (w_H W) m1 a = aview SEGS (w_H W) mem a) ->
forall a, P a -> aview SEGS (w_H W) m2 a = aview SEGS (w_H W) mem a.
Proof.
intros ly S S2 Hp Hp2 W mem m1 m2 md1 md2 lo hi P HAR1 HAR2 Hlo HK HRAW HPw KV a Ha. rewrite <- (KV a Ha).
destruct (HPw a Ha) as [(Hi & Ho) | (p & n & Hin & Hpa)].
- pose proof (pa_img_range a Hi). pose proof asan_consts as (C1 & _).
  apply HRAW; [lia | intros Hown; exact (Ho (proj1 (alx_owned_image _ _ _ LAWS _ _ _ _ _ _ a HAR1 Hi) Hown))
  | intros Hown; exact (Ho (proj1 (alx_owned_image _ _ _ LAWS _ _ _ _ _ _ a HAR2 Hi) Hown)) | lia].
- destruct HK as (_ & HKb & _). replace a with (p + (a - p)) by lia. apply (HKb p n); [exact Hin | lia | intros []].
Qed.
Lemma pres_grow : forall (H : word -> bool) (m0 m1 m2 : word -> option byte),
(forall a, in_img SEGS a -> apresent H m0 a -> apresent H m1 a) ->
mem_grows (mrestrict H m1) (mrestrict H m2) ->
forall a, in_img SEGS a -> apresent H m0 a -> apresent H m2 a.
Proof.
intros H m0 m1 m2 P Hgr a Hi Ha. exact (apresent_grows _ _ _ _ Hgr (P a Hi Ha)).
Qed.
(* the windows of a state (the frame's stack, the fake frame (atom 38), its shadow (513), its flag (512), read-only
   regions) hold no watched byte: WA bundles the byte's facts, WB the stack's floor *)
Ltac rr_nowin_cases WA WB :=
let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
intros (r & Hin & Hr);
lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin];
 [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
   repeat match goal with Hu : bv_unsigned (ew _ _) = _ |- _ => progress rewrite Hu in Hr end;
   revert Hr; clear - WA WB; intros Hr; unfold SB in *; lia | ]);
destruct Hin.
Ltac rr_nowin WA WB :=
split; [revert WA; pose proof asan_consts as (Cx & _); revert Cx; clear; intros; lia | rr_nowin_cases WA WB].
(* after a plain run: its frame over the unhidden memory as HFr, its growth as HGr; the raw frame dropped *)
Ltac rr_grab :=
lazymatch goal with Hf : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ => rename Hf into HFr_x; rename HFr_x into HFr end;
lazymatch goal with Hg : mem_grows (mrestrict _ _) (mrestrict _ _) |- _ => rename Hg into HGr_x; rename HGr_x into HGr end;
try match goal with Hf : frame_of _ _ ?x _ |- _ => lazymatch x with mrestrict _ _ => fail | _ => clear Hf end end.

(* g_lock's twelve bytes are watched (rg_place): kept, they keep alock_at *)
Lemma rr_alock_carry : forall ly S (W : world SEGS) mem m1 (X : Z -> Prop) b,
(forall a, rr_wt ly S a -> ~ X a -> aview SEGS (w_H W) m1 a = aview SEGS (w_H W) mem a) ->
(forall a, in_img SEGS a -> apresent (w_H W) mem a -> apresent (w_H W) m1 a) ->
(forall a, rg_lock RG <= a < rg_lock RG + 12 -> ~ X a) ->
rg_place B RG -> alock_at RG W mem b -> alock_at RG W m1 b.
Proof.
intros ly S W mem m1 X b KV PR HX RGP HL. destruct RGP as (_ & _ & _ & _ & _ & _ & RGIMG & _).
apply (alock_at_kept RG W mem W m1 b HL). intros r Hr a Ha. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
destruct (RGIMG a ltac:(unfold rg_rng; left; exact Ha)) as (Hi & Ho & _).
split; [apply KV; [left; split; assumption | exact (HX a Ha)]|].
unfold arm. apply writable_kept. intros Hp. exact (PR a Hi Hp).
Qed.
(* ---- The entry's representations at a later memory m1 of the same world: every watched byte (outside X, a part
   of g_lock's lock word) kept, image presence kept, the live blocks the same. ---- *)
Ltac rr_in := repeat (first [left; reflexivity | right]).
Lemma rr_recs_len : forall rs, length (concat (map text_rec rs)) = (16 * length rs)%nat.
Proof.
intros rs. induction rs as [|r rs IH]; [reflexivity|].
cbn [map concat length]. rewrite length_app, IH. unfold text_rec.
rewrite length_app, !OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.length_le8. lia.
Qed.
Lemma rr_kptrs_len : forall ks, length (key_ptrs ks) = (8 * length ks)%nat.
Proof.
intros ks. induction ks as [|k ks IH]; [reflexivity|]. unfold key_ptrs in *. cbn [map concat]. rewrite length_app, IH.
rewrite OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.length_le8. cbn [length]. lia.
Qed.
(* the bytes an entry's predicate reads lie in its blocks, which are live *)
Lemma rr_entry_fp : forall ly S (W : world SEGS) mem e, aentry_ok B ly S W mem e ->
(forall r, In r (aentry_fp e) -> forall a, fst r <= a < snd r ->
  exists p n, In (p, n) (ablocks B ly S) /\ p <= a < p + n) /\
(forall b, In b (aentry_blks e) -> In b (ablocks B ly S)).
Proof.
intros ly S W mem e (_ & _ & _ & _ & _ & _ & HU & _ & _ & Hbuf & _ & Hhp & _ & _ & Hks).
split.
- intros r Hr a Ha. unfold aentry_fp in Hr. apply in_app_or in Hr. destruct Hr as [Hr | [<- | Hr]].
  + destruct (Z.eqb_spec (re_cap e) 0) as [Hc0 | Hc0]; cbn [In] in Hr; [destruct Hr|].
    destruct Hr as [<- | []]. unfold gfp, bzs in Ha. cbn [fst snd] in Ha. rewrite length_map, length_app in Ha.
    destruct Hbuf as [(Hc & _) | (Hc & Hin & Hj & _)]; [lia|].
    exists (re_buf e), (re_cap e). split; [exact Hin | lia].
  + unfold gfp, bzs in Ha. cbn [fst snd] in Ha. rewrite length_map, rr_kptrs_len in Ha.
    destruct Hhp as [(_ & Hk0) | (_ & Hin & Hk1 & _)].
    * rewrite Hk0 in Ha. cbn [length] in Ha. lia.
    * exists (re_hp e), (re_kh e). split; [exact Hin|]. unfold re_nheld in Hk1. lia.
  + apply in_map_iff in Hr as (k & <- & Hk). unfold gfp, bzs in Ha. cbn [fst snd] in Ha.
    rewrite length_map, length_app in Ha. cbn [length] in Ha.
    rewrite Forall_forall in Hks. destruct (Hks k Hk) as (Hin & _).
    exists (key_addr k), (Z.of_nat (length (key_text k)) + 1). split; [exact Hin | lia].
- intros b Hb. unfold aentry_blks in Hb. apply in_app_or in Hb. destruct Hb as [Hb | Hb].
  + destruct (Z.eqb_spec (re_cap e) 0) as [Hc0 | Hc0]; cbn [In] in Hb; [destruct Hb|].
    destruct Hb as [<- | []]. destruct Hbuf as [(Hc & _) | (_ & Hin & _)]; [lia | exact Hin].
  + apply in_app_or in Hb. destruct Hb as [Hb | Hb].
    * destruct (Z.eqb_spec (re_hp e) 0) as [Hh0 | Hh0]; cbn [In] in Hb; [destruct Hb|].
      destruct Hb as [<- | []]. destruct Hhp as [(Hh & _) | (_ & Hin & _)]; [lia | exact Hin].
    * apply in_map_iff in Hb as (k & <- & Hk). rewrite Forall_forall in Hks. exact (proj1 (Hks k Hk)).
Qed.
(* the same for a list header at LA (bytes of g_s) and the blocks it names *)
Lemma rr_alist_fp : forall ly S (W : world SEGS) mem LA l lines, alist_at B ly S W mem LA l lines ->
(forall r, In r (alist_fp LA l) -> forall a, fst r <= a < snd r ->
  LA <= a < LA + 16 \/ exists p n, In (p, n) (ablocks B ly S) /\ p <= a < p + n) /\
(forall b, In b (alist_blks l) -> In b (ablocks B ly S)).
Proof.
intros ly S W mem LA l lines (_ & _ & _ & _ & Hn & Hv & _ & _ & Hrecs).
split.
- intros r Hr a Ha. unfold alist_fp in Hr. destruct Hr as [<- | Hr]; [left; cbn [fst snd] in Ha; lia|].
  right. apply in_app_or in Hr. destruct Hr as [Hr | Hr].
  + destruct (Z.eqb_spec (hl_cap l) 0) as [Hc0 | Hc0]; cbn [In] in Hr; [destruct Hr|].
    destruct Hr as [<- | []]. unfold gfp, bzs in Ha. cbn [fst snd] in Ha.
    rewrite length_map, length_app, rr_recs_len in Ha.
    destruct Hv as [(Hc & _) | (Hc & Hin & Hj & _)]; [lia|].
    exists (hl_v l), (AREC * hl_cap l). split; [exact Hin|]. unfold hl_n in *. unfold AREC in *. lia.
  + apply in_map_iff in Hr as (q & <- & Hq). unfold gfp, bzs in Ha. cbn [fst snd] in Ha.
    rewrite length_map, length_app in Ha. cbn [length] in Ha.
    rewrite Forall_forall in Hrecs. destruct (Hrecs q Hq) as (Hin & _).
    exists (fst q), (Z.of_nat (length (snd q)) + 1). split; [exact Hin | lia].
- intros b Hb. unfold alist_blks in Hb. apply in_app_or in Hb. destruct Hb as [Hb | Hb].
  + destruct (Z.eqb_spec (hl_cap l) 0) as [Hc0 | Hc0]; cbn [In] in Hb; [destruct Hb|].
    destruct Hb as [<- | []]. destruct Hv as [(Hc & _) | (_ & Hin & _)]; [lia | exact Hin].
  + apply in_map_iff in Hb as (q & <- & Hq). rewrite Forall_forall in Hrecs. exact (proj1 (Hrecs q Hq)).
Qed.
Lemma rr_carry : forall ly S S1 HpA HpB (W : world SEGS) mem md m1 md1 G0 es c O mx cap out h j FD (X : Z -> Prop),
ARx ly S HpA W mem md -> ARx ly S1 HpB W m1 md1 -> ablocks B ly S1 = ablocks B ly S ->
(forall a, rr_wt ly S a -> ~ X a -> aview SEGS (w_H W) m1 a = aview SEGS (w_H W) mem a) ->
(forall a, in_img SEGS a -> apresent (w_H W) mem a -> apresent (w_H W) m1 a) ->
(forall a, X a -> rr_lkw a) ->
rg_place B RG ->
arelay_at B RG ly S W mem G0 es ->
aout_at B RG ly S W mem c O mx (Z.of_nat (length O)) cap out ->
awake_at RG W mem ->
(forall i, (i < length es)%nat -> re_fd (nth i es relay_remove_b_c.no_entry) = FD ->
   re_eof (nth i es relay_remove_b_c.no_entry) = 0 -> dr_src_ok B RG ly S W mem (nth i es relay_remove_b_c.no_entry) h j) ->
arelay_at B RG ly S1 W m1 G0 es /\ aout_at B RG ly S1 W m1 c O mx (Z.of_nat (length O)) cap out /\
awake_at RG W m1 /\ (forall a, rg_s RG <= a < rg_s RG + 4 * ASRC -> abyte_kept W mem W m1 a) /\
(forall i, (i < length es)%nat -> re_fd (nth i es relay_remove_b_c.no_entry) = FD ->
   re_eof (nth i es relay_remove_b_c.no_entry) = 0 -> dr_src_ok B RG ly S1 W m1 (nth i es relay_remove_b_c.no_entry) h j).
Proof.
intros ly S S1 HpA HpB W mem md m1 md1 G0 es c O mx cap out h j FD X HAR HAR1 Eab KV PR HX RGP HREL HOUT HWAKE HSRC.
pose proof RGP as (RGLOCK & RGNSRC & RGSRC & RGAL8 & RGAL4 & RGSAL & RGIMG & RGWR & RGSEP).
assert (K : forall a, rr_wt ly S a -> ~ rr_lkw a -> abyte_kept W mem W m1 a).
{ intros a Hw Hl. split; [apply KV; [exact Hw | intros Hx; exact (Hl (HX a Hx))]|].
  destruct Hw as [(Hi & _) | (p & n & Hin & Ha)].
  - unfold arm. apply writable_kept. intros Hp. exact (PR a Hi Hp).
  - intros _. unfold arm. apply (apresent_writable SEGS). rewrite <- Eab in Hin.
    destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ p n HAR1 Hin) as (_ & _ & _ & _ & Hpr & _). exact (proj1 (Hpr a Ha)). }
assert (KB : forall p n a, In (p, n) (ablocks B ly S) -> p <= a < p + n -> abyte_kept W mem W m1 a).
{ intros p n a Hin Ha. apply K; [exact (rr_wt_blk ly S p n a Hin Ha)|]. intros Hl.
  assert (Hn : 0 <= n) by lia. pose proof (req_size_pos n Hn) as (_ & Hrq).
  assert (Hpa : p <= a < p + req_size n) by lia.
  apply (proj2 (alx_client_img _ _ _ LAWS ly S HpA W mem md a HAR (or_introl (ex_intro _ p (ex_intro _ n (conj Hin Hpa)))))).
  apply RGIMG. unfold rg_rng. left. unfold rr_lkw in Hl. lia. }
assert (KR : forall a, rg_rng RG a -> ~ rr_lkw a -> abyte_kept W mem W m1 a).
{ intros a Ha Hl. destruct (RGIMG a Ha) as (Hi & Ho & _). apply K; [left; split; assumption | exact Hl]. }
assert (KG : forall x n a, In (x, n) (G_RR B RG) -> x <= a < x + n -> ~ rr_lkw a -> abyte_kept W mem W m1 a).
{ intros x n a Hin Ha Hl. destruct (HG a) as (Hi & Ho & _).
  { unfold inG. apply Exists_exists. exists (x, n). split; [exact Hin | unfold in_zr; cbn [fst snd]; lia]. }
  apply K; [left; split; assumption | exact Hl]. }
assert (KI : forall a, in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) -> ~ rr_lkw a -> abyte_kept W mem W m1 a).
{ intros a Ha Hl. apply K; [left; exact Ha | exact Hl]. }
(* g_lock's word apart from each cell, one quantified fact per cell (no disjunction left in the context) *)
pose proof HRGP as (HLK & _). cbn [zall_disjoint] in HLK. unfold zdisj in HLK. cbn [fst snd] in HLK.
destruct HLK as (D_s & D_src & D_nsrc & D_capsrc & D_smax & D_nout & D_capout & D_out & D_client & D_cbr & D_sdead
  & D_seintr & D_wake & D_errno & _).
assert (N_s : forall a, rg_s RG <= a < rg_s RG + 4 * ASRC -> ~ rr_lkw a) by (intros a Ha; unfold rr_lkw; revert Ha D_s; clear; lia).
assert (N_src : forall a, rg_src RG <= a < rg_src RG + 8 -> ~ rr_lkw a) by (intros a Ha; unfold rr_lkw; revert Ha D_src; clear; lia).
assert (N_nsrc : forall a, rg_nsrc RG <= a < rg_nsrc RG + 4 -> ~ rr_lkw a) by (intros a Ha; unfold rr_lkw; revert Ha D_nsrc; clear; lia).
assert (N_capsrc : forall a, rg_capsrc RG <= a < rg_capsrc RG + 4 -> ~ rr_lkw a) by (intros a Ha; unfold rr_lkw; revert Ha D_capsrc; clear; lia).
assert (N_smax : forall a, rg_send_max RG <= a < rg_send_max RG + 8 -> ~ rr_lkw a) by (intros a Ha; unfold rr_lkw; revert Ha D_smax; clear; lia).
assert (N_nout : forall a, rg_nout RG <= a < rg_nout RG + 8 -> ~ rr_lkw a) by (intros a Ha; unfold rr_lkw; revert Ha D_nout; clear; lia).
assert (N_capout : forall a, rg_capout RG <= a < rg_capout RG + 8 -> ~ rr_lkw a) by (intros a Ha; unfold rr_lkw; revert Ha D_capout; clear; lia).
assert (N_out : forall a, rg_out RG <= a < rg_out RG + 8 -> ~ rr_lkw a) by (intros a Ha; unfold rr_lkw; revert Ha D_out; clear; lia).
assert (N_client : forall a, rg_client RG <= a < rg_client RG + 4 -> ~ rr_lkw a) by (intros a Ha; unfold rr_lkw; revert Ha D_client; clear; lia).
assert (N_cbr : forall a, rg_client_broken RG <= a < rg_client_broken RG + 1 -> ~ rr_lkw a) by (intros a Ha; unfold rr_lkw; revert Ha D_cbr; clear; lia).
assert (N_sdead : forall a, rg_send_dead RG <= a < rg_send_dead RG + 1 -> ~ rr_lkw a) by (intros a Ha; unfold rr_lkw; revert Ha D_sdead; clear; lia).
assert (N_seintr : forall a, rg_send_eintr RG <= a < rg_send_eintr RG + 1 -> ~ rr_lkw a) by (intros a Ha; unfold rr_lkw; revert Ha D_seintr; clear; lia).
assert (N_wake : forall a, rg_wake RG + 4 <= a < rg_wake RG + 8 -> ~ rr_lkw a) by (intros a Ha; unfold rr_lkw; revert Ha D_wake; clear; lia).
assert (N_errno : forall a, as_errno B <= a < as_errno B + 4 -> ~ rr_lkw a) by (intros a Ha; unfold rr_lkw; revert Ha D_errno; clear; lia).
clear D_s D_src D_nsrc D_capsrc D_smax D_nout D_capout D_out D_client D_cbr D_sdead D_seintr D_wake D_errno.
split.
{ apply (arelay_at_kept B RG ly S W mem ly S1 W m1 G0 es HREL).
  - intros r Hr a Ha. unfold arelay_fp in Hr. cbn [In] in Hr.
    destruct Hr as [<- | [<- | [<- | [<- | Hr]]]]; cbn [fst snd] in Ha.
    + apply KR; [unfold rg_rng; tauto | exact (N_src a Ha)].
    + apply KR; [unfold rg_rng; tauto | exact (N_nsrc a Ha)].
    + apply KI; [exact (HRGI a (or_introl Ha)) | exact (N_capsrc a Ha)].
    + pose proof HREL as (_ & _ & _ & _ & _ & _ & _ & HGin & _). exact (KB G0 ATABLE a HGin Ha).
    + apply in_concat in Hr as (l & Hl & Hr). apply in_map_iff in Hl as (e & <- & He).
      pose proof HREL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HEN & _). rewrite Forall_forall in HEN.
      destruct (proj1 (rr_entry_fp ly S W mem e (HEN e He)) r Hr a Ha) as (p & n & Hin & Hpa).
      exact (KB p n a Hin Hpa).
  - intros b Hb. rewrite Eab. unfold arelay_blks in Hb. destruct Hb as [<- | Hb].
    + pose proof HREL as (_ & _ & _ & _ & _ & _ & _ & HGin & _). exact HGin.
    + apply in_concat in Hb as (l & Hl & Hb). apply in_map_iff in Hl as (e & <- & He).
      pose proof HREL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HEN & _). rewrite Forall_forall in HEN.
      exact (proj2 (rr_entry_fp ly S W mem e (HEN e He)) b Hb). }
split.
{ apply (aout_at_kept B RG ly S W mem ly S1 W m1 c O mx (Z.of_nat (length O)) cap out HOUT).
  - intros r Hr a Ha. unfold aout_fp in Hr. cbn [In] in Hr.
    destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | Hr]]]]]]]]]; cbn [fst snd] in Ha.
    + apply KI; [exact (HRGI a (or_intror (or_introl Ha))) | exact (N_smax a Ha)].
    + apply (KG (rg_nout RG) 8 a); [unfold G_RR, G_DR, G_SL; rr_in | exact Ha | exact (N_nout a Ha)].
    + apply (KG (rg_capout RG) 8 a); [unfold G_RR, G_DR, G_SL; rr_in | exact Ha | exact (N_capout a Ha)].
    + apply (KG (rg_out RG) 8 a); [unfold G_RR, G_DR, G_SL; rr_in | exact Ha | exact (N_out a Ha)].
    + apply KI; [exact (HRGI a (or_intror (or_intror (or_introl Ha)))) | exact (N_client a Ha)].
    + apply (KG (rg_client_broken RG) 1 a); [unfold G_RR, G_DR, G_SL; rr_in | exact Ha | exact (N_cbr a Ha)].
    + apply KI; [exact (HRGI a (or_intror (or_intror (or_intror Ha)))) | exact (N_sdead a Ha)].
    + apply (KG (rg_send_eintr RG) 1 a); [unfold G_RR, G_DR, G_SL; rr_in | exact Ha | exact (N_seintr a Ha)].
    + apply (KG (as_errno B) 4 a); [unfold G_RR, G_DR, G_SL; rr_in | exact Ha | exact (N_errno a Ha)].
    + destruct (cap =? 0) eqn:Hc0; cbn [In] in Hr; [destruct Hr|]. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
      pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hblk).
      destruct Hblk as [(Hc & _) | (_ & _ & Hin & _)]; [apply Z.eqb_neq in Hc0; lia|].
      exact (KB out cap a Hin Ha).
  - intros b Hb. rewrite Eab. unfold aout_blks in Hb. destruct (cap =? 0) eqn:Hc0; [destruct Hb|].
    destruct Hb as [<- | []].
    pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hblk).
    destruct Hblk as [(Hc & _) | (_ & _ & Hin & _)]; [apply Z.eqb_neq in Hc0; lia | exact Hin]. }
split.
{ apply (awake_at_kept RG W mem W m1 HWAKE). intros r Hr a Ha. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
  apply KR; [unfold rg_rng; tauto | exact (N_wake a Ha)]. }
assert (GS : forall a, rg_s RG <= a < rg_s RG + 4 * ASRC -> abyte_kept W mem W m1 a).
{ intros a Ha. apply KR; [unfold rg_rng; tauto | exact (N_s a Ha)]. }
split; [exact GS|].
intros i Hi Hfd Heof. destruct (HSRC i Hi Hfd Heof) as (Hj & HA & HO & R). split; [exact Hj|].
assert (HAr : rg_s RG <= rg_s RG + ASRC * Z.of_nat j /\ rg_s RG + ASRC * Z.of_nat j + ASRC <= rg_s RG + 4 * ASRC)
by (unfold ASRC; lia).
split.
{ apply (asrc_at_kept B ly S W mem ly S1 W m1 _ h HA).
  - pose proof HA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpb & _ & _ & _ & Hexp & Hheld & _).
    intros r Hr a Ha. unfold asrc_fp in Hr. destruct Hr as [<- | [<- | Hr]].
    + cbn [fst snd] in Ha. apply GS. lia.
    + unfold gfp, bzs in Ha. cbn [fst snd] in Ha. rewrite length_map in Ha.
      pose proof HA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPJ & _).
      apply (KB (hs_partial h) APARTIAL a Hpb). lia.
    + apply in_app_or in Hr. destruct Hr as [Hr | Hr]; [|apply in_app_or in Hr; destruct Hr as [Hr | Hr]].
      * destruct (proj1 (rr_alist_fp ly S W mem _ _ _ Hpend) r Hr a Ha) as [Hl | (p & n & Hin & Hpa)];
        [apply GS; unfold ASRC in *; lia | exact (KB p n a Hin Hpa)].
      * destruct (proj1 (rr_alist_fp ly S W mem _ _ _ Hexp) r Hr a Ha) as [Hl | (p & n & Hin & Hpa)];
        [apply GS; unfold ASRC in *; lia | exact (KB p n a Hin Hpa)].
      * destruct (proj1 (rr_alist_fp ly S W mem _ _ _ Hheld) r Hr a Ha) as [Hl | (p & n & Hin & Hpa)];
        [apply GS; unfold ASRC in *; lia | exact (KB p n a Hin Hpa)].
  - pose proof HA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpb & _ & _ & _ & Hexp & Hheld & _).
    intros b Hb. rewrite Eab. unfold asrc_blks in Hb. destruct Hb as [<- | Hb]; [exact Hpb|].
    apply in_app_or in Hb. destruct Hb as [Hb | Hb]; [|apply in_app_or in Hb; destruct Hb as [Hb | Hb]].
    + exact (proj2 (rr_alist_fp ly S W mem _ _ _ Hpend) b Hb).
    + exact (proj2 (rr_alist_fp ly S W mem _ _ _ Hexp) b Hb).
    + exact (proj2 (rr_alist_fp ly S W mem _ _ _ Hheld) b Hb). }
split; [|exact R].
intros i' Hi' Hne. destruct (HO i' Hi' Hne) as (f & o & Vf & Vo & Hfo). exists f, o.
assert (Hi4 : rg_s RG <= rg_s RG + ASRC * Z.of_nat i' /\ rg_s RG + ASRC * Z.of_nat i' + 8 <= rg_s RG + 4 * ASRC)
by (unfold ASRC; lia).
split; [apply (akept_vm W mem); [intros x Hx; apply GS; cbn in Hx; lia | exact Vf]|].
split; [apply (akept_vm W mem); [intros x Hx; apply GS; cbn in Hx; lia | exact Vo] | exact Hfo].
Qed.
(* ---- The state at 0x83ee8, where pthread_mutex_lock returns.  From there to the scan's head the walk reads only
   g_nsrc (atom 32 = |es|) and g_src (atom 33 = G0) and writes nothing, so a fresh seat with those two read-only
   regions runs it, and the memory is the lock's own (frame_of_read_only). ---- *)
Definition A_rr_held : Z := AF_fr_relay_remove + 0x104.
Definition rr_hregions : smem :=
[ YP09.mkRegion (Some (A_OBJ 7)) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 32 0))];
  YP09.mkRegion (Some (A_OBJ 8)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 33 0))] ].
Definition ss_rrh : sstate := mkSS A_rr_held sr_atoms rr_hregions None (mkFacts [] [] []).
Definition rr_hextra (n g : Z) : list word := map (Z_to_bv 64) [n; g].
(* the registers the lock's return and the scan's setup leave alone (a0 .. a3 and s7 .. s9 excepted) *)
Definition RRP_KEPT : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 26; 27]%bv.

(* the index of the region whose base atom is n (the state's regions are a concrete list) *)
Fixpoint rr_find_reg (n : nat) (rs : smem) : nat :=
match rs with
| [] => 0%nat
| r :: t => match YP09.r_base r with
            | Some m => if Nat.eqb m n then 0%nat else S (rr_find_reg n t)
            | None => S (rr_find_reg n t)
            end
end.
Ltac rr_region HS n Hn :=
lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ =>
  let i := eval vm_compute in (rr_find_reg n (ss_mem ssx)) in
  pose proof (st_ok_pi_region_nth _ _ _ i _ HS eq_refl) as Hn end.

(* the eleven saved registers, read off the frame's stack region (W7's pro_saved_of_region) *)
Definition rr_saved_atoms : list nat := [25; 24; 23; 22; 21; 20; 19; 18; 9; 8; 1]%nat.
Lemma rr_saved_of_region : forall E (W : world SEGS) memX regs lo hi wlo whi cs,
region_ok SEGS E (mrestrict (w_H W) memX) (YP09.mkRegion (Some 2%nat) lo hi wlo whi cs) ->
(forall i, (i < 11)%nat -> In (YP09.mkChunk (-88 + 8 * Z.of_nat i) (CVal 8 (SOff (nth i rr_saved_atoms 0%nat) 0))) cs) ->
(forall (n : nat) (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs r) ->
forall i, (i < 11)%nat ->
val_mem SEGS (arm W memX) (bv_unsigned (ew E 2) - RR_FRAME + 8 + 8 * Z.of_nat i) 8
  (bv_unsigned (getr regs (nth i RR_SAVED 0%bv))).
Proof.
intros E W memX regs lo hi wlo whi cs HR Hin EREG i Hi.
assert (Hew : ew E (nth i rr_saved_atoms 0%nat) = getr regs (nth i RR_SAVED 0%bv)).
{ apply EREG; (do 11 (destruct i as [|i]; [first [reflexivity | cbn [nth rr_saved_atoms]; lia] |])); lia. }
replace (bv_unsigned (ew E 2) - RR_FRAME + 8 + 8 * Z.of_nat i)
  with (bv_unsigned (ew E 2) + (-88 + 8 * Z.of_nat i)) by (unfold RR_FRAME; lia).
unfold arm.
apply (slot_of_region E _ _ cs lo hi wlo whi _ (SOff (nth i rr_saved_atoms 0%nat) 0) _ HR eq_refl (Hin i Hi)).
- cbn [sv_denot]. rewrite Hew, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
- pose proof (bv_unsigned_in_range 64 (getr regs (nth i RR_SAVED 0%bv))) as R.
  change (bv_modulus 64) with (2 ^ 64) in R. lia.
Qed.
(* a value kept by the ASan view is kept in memory *)
Lemma rr_vm_keep : forall (W : world SEGS) m m' a (n : nat) v,
(forall x, a <= x < a + Z.of_nat n -> aview SEGS (w_H W) m' x = aview SEGS (w_H W) m x) ->
val_mem SEGS (arm W m) a n v -> val_mem SEGS (arm W m') a n v.
Proof.
intros W m m' a n v HK HV. unfold arm in *.
apply (val_mem_kept SEGS (w_H W) (w_H W) m m' a n v); [intros k Hk; apply HK; lia | exact HV].
Qed.
(* a register's symbolic value, as a numeral *)
Lemma rr_den : forall E e v, U E e = v -> sv_denot E e = w64 v.
Proof. intros E e v H. unfold w64. rewrite <- H. unfold U. symmetry. apply Z_to_bv_bv_unsigned. Qed.
Lemma rr_off : forall E n c v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
sv_denot E (SOff n c) = w64 (v + c).
Proof. intros E n c v Hn Hv Hc. apply rr_den. exact (U_atom_off E n v c Hn Hv Hc). Qed.
(* the blez at 0x83ef0 and the 56 |es| of 0x83f00-0x83f08: |es| <= 16, so both are decided by cases *)
Ltac rr_n16 Hd := repeat (destruct Hd as [->|Hd]); try (match goal with H : _ = _ |- _ => subst end);
  vm_compute; reflexivity.
Lemma rr_blez : forall (x : word) n, x = Z_to_bv 64 n -> 0 <= n <= 16 ->
branch_taken BC_GE (Z_to_bv 64 0) (sext 64 (bv_extract 0 32 x)) = (n =? 0).
Proof.
intros x n -> Hn.
assert (Hd : n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/ n = 7 \/ n = 8 \/ n = 9 \/ n = 10 \/
  n = 11 \/ n = 12 \/ n = 13 \/ n = 14 \/ n = 15 \/ n = 16) by lia.
rr_n16 Hd.
Qed.
Lemma rr_a2 : forall (x : word) n, x = Z_to_bv 64 n -> 0 <= n <= 16 ->
alu64 ALU_SUB (alu64 ALU_SLL (sext 64 (bv_extract 0 32 x)) (Z_to_bv 64 6))
              (alu64 ALU_SLL (sext 64 (bv_extract 0 32 x)) (Z_to_bv 64 3)) = w64 (AENT * n).
Proof.
intros x n -> Hn. unfold AENT.
assert (Hd : n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/ n = 7 \/ n = 8 \/ n = 9 \/ n = 10 \/
  n = 11 \/ n = 12 \/ n = 13 \/ n = 14 \/ n = 15 \/ n = 16) by lia.
rr_n16 Hd.
Qed.
(* the shadow pointer of the table's first entry (W_rr_scan's AD3 at k = 0) *)
Lemma rr_srl8 : forall x, 0 <= x < 2 ^ 64 -> alu64 ALU_SRL (Z_to_bv 64 x) (Z_to_bv 64 3) = Z_to_bv 64 (x / 8).
Proof.
intros x Hx. assert (Hd : 0 <= x / 8 < 2 ^ 64)
  by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
apply bv_eq. rewrite alu64_unsigned. cbn [zalu_raw]. rewrite !unsigned_lit_small by lia.
change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. lia.
Qed.


Theorem rr_pro : rr_pro_stmt B PST ARx MT RP MMAX RG.
Proof.
intros [regs ly S Hp W mem md ch G0 FD es j h c O mx cap out rest kr] HB KL KU.
unfold RBASE in HB.
cbn [rxregs rxly rxS rxHp rxW rxmem rxmd rxch rxG0 rxFD rxes rxj rxh rxc rxO rxmx rxcap rxout rxrest rxkr rsp0 rN rFP rtr rnth] in HB.
destruct HB as (HPRE & H32 & HCNT & RGP & H10 & RFD & HLOCK & HWAKE & HREL & HOUT & HROM & HSRC & HPERM & HTRM & HLIVE & HMOK
  & HRM & HCNTP).
cbn [rxregs rxW rxmem rxmd].
pose proof RGP as RGPx. destruct RGP as (RGLOCK & RGNSRC & RGSRC & RGAL8 & RGAL4 & RGSAL & RGIMG & RGWR & RGSEP).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
destruct (rr_entry W ly S Hp regs mem md ch HPRE H32) as [HS SHOK].
pose proof (ajournal_x_init (SK := SK) SEGS B PST ARx RR_STK_x (rr_fp G0 FD es h cap out) ly S Hp W regs mem md ch HPRE) as HJ.
assert (HFPcl : ~ YI16.sink_open_fp (rr_fp G0 FD es h cap out)).
{ unfold rr_fp. apply (rr_fp_closed ly S Hp W mem md _ rest (proj1 HPRE)). cbn [app]. rewrite <- !app_assoc. exact HPERM. }
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
remember (Eimg (Ereg regs rr_extra)) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
by (intros n r Hn; subst E; pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5;
rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 (as_uar_cell B)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (HAE : env_agree 32 (Ereg regs rr_extra) E) by (rewrite HE; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clear HE.
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : RR_STK_x = 17072) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
unfold cfg_at. change (w64 A_rr_entryP) with (Z_to_bv 64 A_rr_entryP). unfold A_rr_entryP, A_rr_entry.
paj_run_tok_x RUN0 HS HJ SHOK Bspan. { awr_ok_tac. exact Usp. }
rr_grab.
assert (WB : alloc_ceiling + 16944 <= spZ regs) by lia.
(* the prologue's stores are into the frame: every watched byte kept, presence grows *)
assert (KV1 : forall a, rr_wt ly S a -> aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem a).
{ apply (kv_run E _ W mem mem (ms_mem ms) (rr_wt ly S) (fun a _ => eq_refl) HFr).
  intros a Hw. pose proof (rr_wt_lo ly S Hp W mem md a HAR Hw) as WA. rr_nowin WA WB. }
pose proof (pres_grow (w_H W) mem mem (ms_mem ms) (fun a _ Ha => Ha) HGr) as PRES. clear HFr HGr.
(* the call to __asan_stack_malloc_0 (64): the fake frame *)
pmkst HS.
prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
rewrite (palf_sm0 B TLF).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
  eapply (aj_stack_malloc_pres_at_raw_x SEGS B PST ARx LAWS Hsegs (pal_env B TL) OWNLOW WFx WFL SMALLOC 0 ASMP ltac:(lia)
  W rg mm RR_STK_x (spZ regs) (rr_fp G0 FD es h cap out) ly S Hp W mem md [] ly S Hp _ 0 (-96) _ HJ) end.
  - unfold spZ at 1. rewrite R2, Usp. rewrite unsigned_lit_small by (unfold spZ in *; lia). lia.
  - reflexivity. - lia. - rewrite WS, Hes. lia.
  - rewrite R3, (EE 3%nat 3%bv eq_refl). exact Hgp. - rewrite R4, (EE 4%nat 4%bv eq_refl). exact Htp.
  - exact R1. - apply ret_ok_codeptr_v; [lia | reflexivity].
  - exact HCNT. }
cbv beta. intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & fpos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2 & Hbb2 & Hz & Hflag & HK & HPR0 & HRAW & HFS).
(* the room round: the seat's state is a set_fs of S, so RPF_of carries RBASE's room to it (the lock keeps S2); the
   meter: the seat is a set_fs step, so MO_FR charges it nothing *)
pose proof HFS as (fS & ES2). pose proof (RPF_of RP S fS _ HRM) as HRM2. rewrite <- ES2 in HRM2.
pose proof (MO_FR S fS) as HMOs. rewrite <- ES2 in HMOs. clear HFS ES2 fS.
assert (KV2 : forall a, rr_wt ly S a -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem a).
{ eapply (kv_smalloc ly S S2 Hp Hp W mem _ mem2 _ md2 _ _ (rr_wt ly S) (proj1 HJ) (proj1 HJ2)); [idtac | exact HK | exact HRAW | auto | exact KV1].
  lia. }
pose proof (fun a Hi Ha => HPR0 a Hi (PRES a Hi Ha)) as PRES2. clear PRES HPR0 HRAW KV1. rename PRES2 into PRES.
set (F := frame_addr ly 0 fpos) in *. set (FL := flag_addr ly 0 fpos) in *.
pose proof (proj1 HJ) as HARa. pose proof (proj1 HJ2) as HARb.
destruct (alx_const _ _ _ LAWS _ _ _ _ _ _ HARa) as (Kc1 & Ku1 & Kg1 & Kgu1).
destruct (alx_const _ _ _ LAWS _ _ _ _ _ _ HARb) as (Kc2 & Ku2 & Kg2 & Kgu2).
rewrite HBgot, HBcell in Kg1, Kg2. rewrite HBcell in Kc1, Kc2. rewrite (palf_got_uar B TLF) in Kgu1, Kgu2.
pose proof (palf_uar_img B TLF) as HuR.
jafter_call_keep_pi HS 34%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2; 3; 4]%nat HS2.
match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| | | | | apply Forall_nil].
  - eapply rr_region_kept_stack_aj_x; [exact HK | exact HJ2 | exact Usp | lia | lia | lia | cbn; lia | cbn; lia].
  - apply (region_kept_val_at E _ _ (A_OBJ 0) (VAL (A_OBJ 0)) 8 (VAL (A_OBJ 32)));
    [exact (HEI (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact (val_mem_of_rdword SEGS _ _ _ _ Kg1) | exact (val_mem_of_rdword SEGS _ _ _ _ Kg2) | lia].
  - apply (region_kept_val_at E _ _ (A_OBJ 32) (VAL (A_OBJ 32)) 8 SHADOW_OFF);
    [exact (HEI (A_OBJ 32) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact (val_mem_of_rdword SEGS _ _ _ _ Kc1) | exact (val_mem_of_rdword SEGS _ _ _ _ Kc2) | lia].
  - apply (region_kept_val_at E _ _ (A_OBJ 1) (VAL (A_OBJ 1)) 8 (as_uar_cell B));
    [exact (HEI (A_OBJ 1) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact (val_mem_of_rdword SEGS _ _ _ _ Kgu1) | exact (val_mem_of_rdword SEGS _ _ _ _ Kgu2) | lia].
  - apply (region_kept_val_at E _ _ 32 (as_uar_cell B) 4 1);
    [rewrite E32; apply unsigned_lit_small; lia | exact (val_mem_of_rd32 SEGS _ _ _ _ Ku1) | exact (val_mem_of_rd32 SEGS _ _ _ _ Ku2) | lia]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 34 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall m, (m < 34)%nat -> ew Ea m = ew E m) by (intros m Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
assert (HAEa : env_agree 32 (Ereg regs rr_extra) Ea) by (rewrite HEa; apply env_agree_havoc_ge; [cbv; lia | exact HAE]).
clear HEa.
prreg HS (10%bv : bv 5) RF.
(* seat the fake frame: F at atom 38 (a0), its flag FL at 512, the frame's shadow SB + F / 8 at 513 *)
assert (Hfin2 : In (0, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (frames_bounds_x SEGS B ARx LAWS _ _ _ _ _ _ 0 fpos HARb Hfin2) as (HF4096 & HFceil & HFhigh).
destruct (alx_frames _ _ _ LAWS _ _ _ _ _ _ 0 fpos HARb Hfin2) as (HFal & HFapp & HFpres & HFSpres).
pose proof (frm_off_imgP_x B ARx LAWS IMGC _ _ _ _ _ _ 0 fpos HARb Hfin2) as HFimg.
destruct (FFL _ _ _ _ _ _ 0 fpos HARb Hfin2) as (HFLp & HFLo & (HFLapp & HFLimg) & (HFL4096 & HFLz & HFLc)).
change (fs_frame_bytes 0) with 64 in *. change (64 / 8) with 8 in *. fold F FL in HFal, HFapp, HFpres, HFSpres, HFimg, HFLp, HFLo, HFLapp, HFLimg, HFL4096, HFLz, HFLc, HF4096, HFceil, HFhigh.
assert (RF' : ew Ea 38 = Z_to_bv 64 F) by (rewrite <- RF, Ha0; reflexivity).
pose proof (st_ok_pi_havoc_hi 512 Ea _ _ [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] HS ltac:(vm_compute; reflexivity)) as HS3.
clear HS. rename HS3 into HS.
remember (havoc Ea 512 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)]) as Eb eqn:HEb in HS.
assert (HEIb : img_env VAL A_LIM Eb) by (rewrite HEb; apply img_env_havoc_hi; [exact HEIa | cbv; lia]).
assert (OLDb : forall m, (m < 512)%nat -> ew Eb m = ew Ea m) by (intros m Hm; rewrite HEb; apply YN3v.ew_havoc_old; exact Hm).
assert (E512 : ew Eb 512 = Z_to_bv 64 FL) by (rewrite HEb; exact (ew_havoc_new _ 512 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 0 (Z_to_bv 64 0) ltac:(cbn; lia))).
assert (E513 : ew Eb 513 = Z_to_bv 64 (SB + F / 8)) by (rewrite HEb; exact (ew_havoc_new _ 512 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 1 (Z_to_bv 64 0) ltac:(cbn; lia))).
assert (HAEb : env_agree 32 (Ereg regs rr_extra) Eb) by (rewrite HEb; apply env_agree_havoc_ge; [cbv; lia | exact HAEa]).
clear HEb.
assert (E38 : ew Eb 38 = Z_to_bv 64 F) by (rewrite OLDb by lia; exact RF').
assert (E33b : ew Eb 33 = Z_to_bv 64 SB) by (rewrite OLDb, OLDa by lia; exact E33).
assert (HFq : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(lia)); lia).
assert (HF8 : F / 8 = 4 * (F / 32)) by (rewrite HFq at 1; replace (32 * (F / 32)) with (4 * (F / 32) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
assert (HF8lo : 512 <= F / 8) by (apply Z.div_le_lower_bound; lia).
assert (HF8hi : F / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia).
pose proof (st_ok_pi_add_fact Eb _ _ 38 (HPTR 5) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite E38, unsigned_lit_small by lia; change (2 ^ 5) with 32; lia)) as HS3.
clear HS; rename HS3 into HS.
pose proof (st_ok_pi_add_fact Eb _ _ 512 (HPTR 0) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite E512, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS3.
clear HS; rename HS3 into HS.
pose proof (st_ok_pi_add_fact Eb _ _ 513 (mkAF (SB + 512) (SB + 17592186044416) 2) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E513, unsigned_lit_small by (unfold SB; lia); change (2 ^ 2) with 4; unfold SB;
split; [lia|]; split; [rewrite HF8; replace (2147450880 + 4 * (F / 32)) with ((536862720 + F / 32) * 4) by lia; apply Z_mod_mult | lia])) as HS3.
clear HS; rename HS3 into HS.
pose proof (st_ok_pi_add_alias Eb _ _ _ _ HS (shadow_decl_ok Eb 38 33 513 F SB E38 ltac:(lia) E33b E513)) as HS3.
clear HS; rename HS3 into HS. norm_ss HS.
assert (U2b : bv_unsigned (ew Eb 2) = spZ regs) by (rewrite OLDb, OLDa by lia; exact Usp).
assert (U241 : bv_unsigned (ew Eb 241) = VAL (A_OBJ 0)) by exact (HEIb (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
assert (U242 : bv_unsigned (ew Eb 242) = VAL (A_OBJ 1)) by exact (HEIb (A_OBJ 1) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
assert (U273 : bv_unsigned (ew Eb 273) = VAL (A_OBJ 32)) by exact (HEIb (A_OBJ 32) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
assert (U32 : bv_unsigned (ew Eb 32) = as_uar_cell B) by (rewrite OLDb, OLDa, E32 by lia; apply unsigned_lit_small; lia).
assert (U38 : bv_unsigned (ew Eb 38) = F) by (rewrite E38; apply unsigned_lit_small; lia).
assert (U512 : bv_unsigned (ew Eb 512) = FL) by (rewrite E512; apply unsigned_lit_small; lia).
assert (U513 : bv_unsigned (ew Eb 513) = SB + F / 8) by (rewrite E513; apply unsigned_lit_small; unfold SB; lia).
pose proof (pa_obj_img 32 ltac:(lia)) as HcellR. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR. pose proof (pa_obj_img 1 ltac:(lia)) as HguR.
(* (palf_sep's zseps is not needed here: kept out of the context, whose lia calls it would make exponential) *)
pose proof (pa_val_range (A_OBJ 0)) as PV0. pose proof (pa_val_range (A_OBJ 1)) as PV1. pose proof (pa_val_range (A_OBJ 32)) as PV32.
(* the geometry facts in numerals, once: each region's lia then sees only what it reverts (W5's W_relay_add.v:940) *)
unfold SB, zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in C1, C3, Hslo, Hshi, H47, Hceil, Hstk0,
HcellR, HgotR, HguR, HuR, HFimg, HFapp, HF4096, HFceil, HFhigh, HFLapp, HFLimg, HFL4096, HFLc.
pose proof (st_ok_pi_add_region Eb _ _ (fframe_region 38 512 0 []) HS eq_refl
ltac:(unfold region_ok, fframe_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
change (fs_frame_bytes 0) with 64; rewrite U38; split; [lia|]; split; [lia|]; split;
[ intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFpres (F + o) ltac:(lia)))
| apply Forall_cons; [|apply Forall_nil]; apply (chunk_ok_val SEGS Eb _ F (64 - 8) 8 _ FL);
[cbn [sv_denot]; rewrite E512, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | replace (F + (64 - 8)) with (F + 64 - 8) by lia; exact (val_mem_of_rdword SEGS _ _ _ _ Hflag)] ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint, fframe_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
change (fs_frame_bytes 0) with 64; rewrite U38, U2b, U241, U242, U273, U32;
revert Hslo Hshi H47 Hceil Hstk0 C1 C3 WS HF4096 HFceil HFhigh HFimg HFapp HgotR HcellR HguR HuR PV0 PV1 PV32; clear; intros;
unfold off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; repeat split; lia)) as HS3.
clear HS; rename HS3 into HS.
pose proof (st_ok_pi_add_region Eb _ _ (fshadow_region 513 0 0 8 [YP09.mkChunk 0 (CVal 8 (SLit 0))]) HS eq_refl
ltac:(unfold region_ok, fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
change (fs_frame_bytes 0 / 8) with 8; rewrite U513; split; [unfold SB; lia|]; split; [unfold SB; lia|]; split;
[ intros o Ho; apply (apresent_writable SEGS); unfold shadow_addr in HFSpres; rewrite <- SB_SHADOW_OFF in HFSpres; apply (proj1 (HFSpres o ltac:(lia)))
| apply Forall_cons; [|apply Forall_nil]; apply (chunk_ok_val SEGS Eb _ (SB + F / 8) 0 8 _ 0); [reflexivity | zside | zside |];
rewrite Z.add_0_r; apply val_mem_zero8; intros i Hi; unfold zero_shadow, shadow_of_addr in Hz; rewrite <- SB_SHADOW_OFF in Hz; apply Hz; change (64 / 8) with 8; lia ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint, fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
change (fs_frame_bytes 0 / 8) with 8; rewrite U513, U38, U2b, U241, U242, U273, U32;
revert Hslo Hshi H47 Hceil Hstk0 C1 C3 WS HF4096 HFceil HFhigh HFimg HFapp HgotR HcellR HguR HuR PV0 PV1 PV32 HF8lo HF8hi HFq HF8; clear; intros;
unfold SB, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, alloc_ceiling in *; repeat split; lia)) as HS3.
clear HS; rename HS3 into HS. norm_ss HS.
(* the frame header and the shadow poison: a plain run, to the fd test *)
paj_run_sh_x RUNP HS HJ2.
{ intros a (r & Hin & Hr).
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [<- | Hin];
  [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U2b, ?U38, ?U513, ?U241, ?U242, ?U273, ?U32 in Hr;
    first [ lia
    | left; unfold RR_STK_x, RR_STK, RR_FRAME, DRAIN_STK_x, DRAIN_STK, DRAIN_FRAME, SL_STK, SL_FRAME, ASTACK; lia
    | right; right; right; exists 0, fpos; split; [left; reflexivity|];
      change (frame_addr ly 0 fpos) with F; change (fs_frame_bytes 0) with 64;
      first [ left; unfold in_zr; cbn [fst snd]; lia
      | right; unfold in_zr, shadow_addr; rewrite <- SB_SHADOW_OFF; cbn [fst snd]; change (64 / 8) with 8; lia ] ]
  | ]).
  destruct Hin. }
rr_grab.
assert (WAF : forall a, rr_wt ly S a -> (4096 <= a < alloc_ceiling) /\
  ~ (F <= a < F + 64) /\ ~ (SB + F / 8 <= a < SB + F / 8 + 8) /\ a <> FL).
{ intros a Hw. split; [exact (rr_wt_lo ly S Hp W mem md a HAR Hw)|].
  exact (rr_wt_fr ly S S2 Hp W mem2 md2 fpos a HARb Hfin2 Eab Hw). }
lazymatch type of HFr with frame_of _ _ _ (mrestrict _ ?m2) =>
assert (KV3 : forall a, rr_wt ly S a -> aview SEGS (w_H W) m2 a = aview SEGS (w_H W) mem a) end.
{ apply (kv_run Eb _ W mem _ _ (rr_wt ly S) KV2 HFr).
  intros a Hw. pose proof (WAF a Hw) as WA. rr_nowin WA WB. }
pose proof (pres_grow (w_H W) mem _ _ PRES HGr) as PRES3. clear PRES HFr HGr KV2. rename PRES3 into PRES.
assert (E10b : sv_denot Eb (SOff 10 0) = Z_to_bv 64 FD)
by (cbn [sv_denot]; rewrite OLDb, OLDa, (EE 10%nat 10%bv eq_refl), H10 by lia; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
psrr_branch_pi_x RUNP BR HS.
-
(* fd < 0: nothing under the lock; the frame's release 0x84000 and the return *)
assert (Hneg : FD < 0).
{ cbn [branch_taken] in Hc. rewrite E10b, bv_lts_signed in Hc. apply Z.ltb_lt in Hc.
  rewrite (fd_signed FD RFD) in Hc. change (bv_signed (sv_denot Eb (SLit 0))) with 0 in Hc. exact Hc. }
destruct (FFL _ _ _ _ _ _ 0 fpos (proj1 HJ2) Hfin2) as (HFLp' & HFLo' & _ & _).
destruct (alx_frames _ _ _ LAWS _ _ _ _ _ _ 0 fpos (proj1 HJ2) Hfin2) as (_ & _ & HFpres' & HFSpres').
change (fs_frame_bytes 0) with 64 in *. change (64 / 8) with 8 in *. fold F FL in HFLp', HFLo', HFpres', HFSpres'.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 512%nat) 0 1 0 1 []) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite U512; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable SEGS); replace (FL + o) with FL by lia; exact HFLp')
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite U512, U513, U38, U2b, U241, U242, U273, U32;
repeat split;
lazymatch goal with
| |- ?fl + 1 <= F + ?l \/ F + ?h <= ?fl + 0 =>
  destruct (Z_lt_ge_dec fl (F + l)) as [Hlt | Hge]; [left; lia|];
  destruct (Z_lt_ge_dec fl (F + h)) as [Hlt2 | Hge2]; [exfalso | right; lia];
  exact (proj2 (HFpres' FL ltac:(lia)) HFLo')
| |- ?fl + 1 <= 2147450880 + F / 8 + ?l \/ 2147450880 + F / 8 + ?h <= ?fl + 0 =>
  destruct (Z_lt_ge_dec fl (2147450880 + F / 8 + l)) as [Hlt | Hge]; [left; lia|];
  destruct (Z_lt_ge_dec fl (2147450880 + F / 8 + h)) as [Hlt2 | Hge2]; [exfalso | right; lia];
  unfold shadow_addr in HFSpres'; rewrite <- SB_SHADOW_OFF in HFSpres'; unfold SB in HFSpres';
  exact (proj2 (HFSpres' (FL - (2147450880 + F / 8)) ltac:(lia)) ltac:(replace (2147450880 + F / 8 + (FL - (2147450880 + F / 8))) with FL by lia; exact HFLo'))
| |- ?fl + 1 <= SB + F / 8 + ?l \/ SB + F / 8 + ?h <= ?fl + 0 =>
  destruct (Z_lt_ge_dec fl (SB + F / 8 + l)) as [Hlt | Hge]; [left; lia|];
  destruct (Z_lt_ge_dec fl (SB + F / 8 + h)) as [Hlt2 | Hge2]; [exfalso | right; lia];
  unfold shadow_addr in HFSpres'; rewrite <- SB_SHADOW_OFF in HFSpres';
  exact (proj2 (HFSpres' (FL - (SB + F / 8)) ltac:(lia)) ltac:(replace (SB + F / 8 + (FL - (SB + F / 8))) with FL by lia; exact HFLo'))
| |- _ =>
  revert Hslo Hshi H47 Hceil Hstk0 C1 C3 WS HgotR HcellR HguR HuR PV0 PV1 PV32 HFL4096 HFLz HFLc; clear; intros;
  unfold SB, zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia
end)) as HS3 end.
clear HS; rename HS3 into HS. norm_ss HS.
paj_run_flag_sh_x RUNF HS HJ2.
{ lia. }
{ intros a (r & Hin & Hr).
lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
cbn [In] in Hin. change (flag_addr ly 0 fpos) with FL.
repeat (destruct Hin as [<- | Hin];
[ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
  repeat match goal with Hu : bv_unsigned (ew _ _) = _ |- _ => progress rewrite Hu in Hr end;
  first [ revert Hr; clear; intros Hr; lia
  | right; revert Hr; clear; intros Hr; lia
  | left; left; revert Hr; clear; intros Hr; assert (Hws : RR_STK_x = 17072) by reflexivity; lia
  | left; right; right; right; exists 0, fpos; split; [left; reflexivity|];
    change (frame_addr ly 0 fpos) with F; change (fs_frame_bytes 0) with 64;
    first [ left; unfold in_zr; cbn [fst snd]; revert Hr; clear; intros Hr; lia
    | right; unfold in_zr, shadow_addr; rewrite <- SB_SHADOW_OFF; cbn [fst snd]; change (64 / 8) with 8;
      revert Hr; clear; intros Hr; lia ]
  ]
| ]).
destruct Hin. }
{ intros msr HSr. change (flag_addr ly 0 fpos) with FL.
lazymatch type of HSr with st_ok_pi _ _ ?Ex ?ssx _ =>
pose proof (st_ok_pi_region_nth Ex ssx msr 0 _ HSr eq_refl) as HR;
lazymatch type of HR with region_ok _ _ _ (YP09.mkRegion (Some ?n) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex (ms_mem msr) n _ cs lo hi wlo whi 0 1%N (SLit 0) 0 HR U512
ltac:(left; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V end end.
rewrite Z.add_0_r in V. pose proof (V 0%nat ltac:(lia)) as V0. cbn [Z.of_nat] in V0. rewrite Z.add_0_r in V0. exact V0. }
rr_grab.
lazymatch type of HFr with frame_of _ _ _ (mrestrict _ ?m2) =>
assert (KV4 : forall a, rr_wt ly S a -> aview SEGS (w_H W) m2 a = aview SEGS (w_H W) mem a) end.
{ apply (kv_run _ _ W mem _ _ (rr_wt ly S) KV3 HFr).
  intros a Hw. pose proof (WAF a Hw) as WA. rr_nowin WA WB. }
pose proof (pres_grow (w_H W) mem _ _ PRES HGr) as PRES4. clear PRES HFr HGr KV3. rename PRES4 into PRES.
prreg HS (1%bv : bv 5) Rr1.
assert (EabF : ablocks B ly (stack_free_state 0 fpos S2) = ablocks B ly S)
by (rewrite <- Eab; unfold ablocks; rewrite blocks_stack_free_state; reflexivity).
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold rPOST, rr_post_x.
cbn [rxregs rxly rxS rxHp rxW rxmem rxmd rxG0 rxFD rxes rxj rxh rxc rxO rxmx rxcap rxout rxkr].
lazymatch type of HJ2 with ajournal_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?lyx ?Sx ?Hpx _ _ _ ?kx =>
lazymatch goal with |- exists _ _ _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists lyx, Sx, Hpx, r, m, d, kx end end.
destruct (rr_carry ly S (stack_free_state 0 fpos S2) Hp Hp W mem md _ _ G0 es c O mx cap out h j FD (fun _ => False)
  HAR (proj1 HJ2) EabF (fun a Hw _ => KV4 a Hw) PRES (fun a (f : False) => match f with end) RGPx HREL HOUT HWAKE HSRC)
  as (CREL & COUT & CWAKE & CGS & _).
split; [cbn [ms_regs]; rewrite Rr1, OLDb, OLDa, (EE 1%nat 1%bv eq_refl), Hra by lia; reflexivity|].
split.
{ cbn [ms_mem]. eapply ajournal_gx_pack_x; [unfold RR_STK_x, RR_STK, RR_FRAME, DRAIN_STK_x, DRAIN_STK, DRAIN_FRAME, SL_STK, SL_FRAME, ASTACK; lia | lia | | apply gagree_refl | intros a Ha; lia].
  rewrite !Z.add_0_r. apply (ajournal_x_materialize SEGS B PST ARx LAWS Hsegs). exact HJ2. }
split. { eapply (aregs_preserved_of_st_ok SEGS _ Eb _ _ regs rr_extra HS); [exact HAEb | vm_compute; reflexivity]. }
split. { intros a Hi _ _ Ha. exact (PRES a Hi Ha). }
split. { unfold rr_tr. rewrite (proj2 (Z.ltb_lt FD 0) Hneg).
  (* the seat (HMOs) then the release, a set_fs of S2 (YG01.v stack_free_state): both free at MO_FR *)
  exact (mle_station MT S S2 (stack_free_state 0 fpos S2) 0 0 MLAW HMOs
    (MO_FR S2 (mkFS (fs_hint (st_fs S2)) (del_pos (fs_live (st_fs S2)) 0 fpos)))). }
(* the room round: kr is below RBASE's budget (RMM_of), kept across the seat (HRM2, RPF_of) and the release *)
split. { apply RPF_stack_free. eapply (RMM_of RP S2 kr); [|exact HRM2]. lia. }
split. { exact (rr_alock_carry ly S W mem _ (fun _ => False) false (fun a Hw _ => KV4 a Hw) PRES (fun a _ f => f) RGPx HLOCK). }
split. { exact CWAKE. }
split. { intros a Ha _. exact (CGS a Ha). }
split. { intros _. split; [exact CREL|]. split; [exact COUT|]. rewrite EabF. apply Permutation_refl. }
intros i Hi Hge. lia.
-
(* fd >= 0: a0 = &g_lock (0x83edc-0x83ee0), pthread_mutex_lock (0x83ee4) *)
assert (Hpos : 0 <= FD).
{ cbn [branch_taken] in Hc. rewrite E10b, bv_lts_signed in Hc. apply Z.ltb_ge in Hc.
  rewrite (fd_signed FD RFD) in Hc. change (bv_signed (sv_denot Eb (SLit 0))) with 0 in Hc. exact Hc. }
paj_run_shc_x RUNP RUNC HS HJ2.
{ intros a (r & Hin & Hr).
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [<- | Hin];
  [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U2b, ?U38, ?U513, ?U241, ?U242, ?U273, ?U32 in Hr;
    first [ lia
    | left; unfold RR_STK_x, RR_STK, RR_FRAME, DRAIN_STK_x, DRAIN_STK, DRAIN_FRAME, SL_STK, SL_FRAME, ASTACK; lia
    | right; right; right; exists 0, fpos; split; [left; reflexivity|];
      change (frame_addr ly 0 fpos) with F; change (fs_frame_bytes 0) with 64;
      first [ left; unfold in_zr; cbn [fst snd]; lia
      | right; unfold in_zr, shadow_addr; rewrite <- SB_SHADOW_OFF; cbn [fst snd]; change (64 / 8) with 8; lia ] ]
  | ]).
  destruct Hin. }
rr_grab.
lazymatch type of HFr with frame_of _ _ _ (mrestrict _ ?m2) =>
assert (KV4 : forall a, rr_wt ly S a -> aview SEGS (w_H W) m2 a = aview SEGS (w_H W) mem a) end.
{ apply (kv_run Eb _ W mem _ _ (rr_wt ly S) KV3 HFr).
  intros a Hw. pose proof (WAF a Hw) as WA. rr_nowin WA WB. }
pose proof (pres_grow (w_H W) mem _ _ PRES HGr) as PRES4. clear PRES HFr HGr KV3. rename PRES4 into PRES.
(* the frame's cells, read off the state's regions before the call *)
assert (EEb : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew Eb n = getr regs r)
  by (intros n r Hn Hr; rewrite OLDb, OLDa by lia; exact (EE n r Hr)).
pose proof (st_ok_region_nth _ _ _ 2%nat _ HS eq_refl) as HRstk.
pose proof (st_ok_region_nth _ _ _ 1%nat _ HS eq_refl) as HRfr.
cbn [ms_mem restrict] in HRstk, HRfr.
eassert (HSV0 : forall i, (i < 11)%nat -> val_mem SEGS (arm W _) (spZ regs - RR_FRAME + 8 + 8 * Z.of_nat i) 8
  (bv_unsigned (getr regs (nth i RR_SAVED 0%bv)))).
{ rewrite <- U2b. apply (rr_saved_of_region Eb W _ regs _ _ _ _ _ HRstk); [|exact EEb].
  intros i Hi. do 11 (destruct i as [|i]; [cbn [nth rr_saved_atoms Z.of_nat]; cbn [In]; rr_in|]). lia. }
eassert (HFL0 : val_mem SEGS (arm W _) (F + 56) 8 FL).
{ apply (field_of_region Eb _ 38%nat F _ _ _ _ _ 56 8%N (SOff 512 0) FL HRfr U38
    ltac:(clear; cbn [In]; rr_in) ltac:(cbn [sv_denot]; rewrite E512, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
    ltac:(cbn; lia) ltac:(cbn; lia)). }
cbn [ms_mem restrict] in HSV0, HFL0.
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (10%bv : bv 5) Q10.
prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20.
prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22. prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
assert (Z2b : ew Eb 2 = Z_to_bv 64 (spZ regs)) by (rewrite <- U2b, Z_to_bv_bv_unsigned; reflexivity).
assert (HSPc : spZ (ms_regs ms1) = spZ regs + -96).
{ unfold spZ at 1. rewrite Q2, U2b. apply unsigned_lit_small. unfold spZ in *. lia. }
(* the base registers at the call, carried to the cut by aregs_preserved (all callee-saved) *)
assert (Lr2 : getr (ms_regs ms1) 2 = w64 (spZ regs - RR_FRAME))
  by (rewrite Q2, U2b; unfold w64, RR_FRAME; f_equal; lia).
assert (Lr3 : getr (ms_regs ms1) 3 = getr regs 3) by (rewrite Q3; exact (EEb 3%nat 3%bv ltac:(lia) eq_refl)).
assert (Lr4 : getr (ms_regs ms1) 4 = getr regs 4) by (rewrite Q4; exact (EEb 4%nat 4%bv ltac:(lia) eq_refl)).
assert (Lr8 : getr (ms_regs ms1) 8 = w64 (spZ regs)) by (rewrite Q8, Z2b; reflexivity).
assert (Lr9 : getr (ms_regs ms1) 9 = w64 (spZ regs - RR_FRAME))
  by (rewrite Q9, U2b; unfold w64, RR_FRAME; f_equal; lia).
assert (Lr18 : getr (ms_regs ms1) 18 = w64 F) by (rewrite Q18; exact E38).
assert (Lr19 : getr (ms_regs ms1) 19 = w64 FD)
  by (rewrite Q19, (EEb 10%nat 10%bv ltac:(lia) eq_refl); exact H10).
assert (Lr20 : getr (ms_regs ms1) 20 = w64 F) by (rewrite Q20; exact E38).
assert (Lr21 : getr (ms_regs ms1) 21 = w64 (shadow_addr F))
  by (rewrite Q21, E513; unfold shadow_addr; rewrite <- SB_SHADOW_OFF; reflexivity).
assert (Lr22 : getr (ms_regs ms1) 22 = w64 SHADOW_OFF)
  by (rewrite Q22, E33b; rewrite <- SB_SHADOW_OFF; reflexivity).
assert (Lr26 : getr (ms_regs ms1) 26 = getr regs 26) by (rewrite Q26; exact (EEb 26%nat 26%bv ltac:(lia) eq_refl)).
assert (Lr27 : getr (ms_regs ms1) 27 = getr regs 27) by (rewrite Q27; exact (EEb 27%nat 27%bv ltac:(lia) eq_refl)).
assert (QA0 : getr (ms_regs ms1) 10 = w64 (rg_lock RG)).
{ rewrite Q10. change 247%nat with (A_OBJ 6).
  rewrite (img_env_atomP Eb (A_OBJ 6) HEIb ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)), RGLOCK. reflexivity. }
pose proof (pa_obj_img 6 ltac:(lia)) as HlkR. rewrite <- RGLOCK in HlkR.
assert (LKc : alock_at RG W (ms_mem ms1) false)
  by (exact (rr_alock_carry ly S W mem _ (fun _ => False) false (fun a Hw _ => KV4 a Hw) PRES (fun a _ f => f) RGPx HLOCK)).
pose proof LKc as (LK0 & LK4 & LK8 & LKW). unfold arm in LK0, LK4, LK8, LKW.
assert (LKV : forall a, rg_lock RG <= a < rg_lock RG + 12 -> aview SEGS (w_H W) (ms_mem ms1) a <> None).
{ intros a Ha. unfold aview.
  destruct (Z_lt_ge_dec a (rg_lock RG + 4)) as [h1|h1]; [|destruct (Z_lt_ge_dec a (rg_lock RG + 8)) as [h2|h2]].
  - pose proof (LK0 (Z.to_nat (a - rg_lock RG)) ltac:(lia)) as X. rewrite Z2Nat.id in X by lia.
    replace (rg_lock RG + (a - rg_lock RG)) with a in X by lia. rewrite X. discriminate.
  - pose proof (LK4 (Z.to_nat (a - (rg_lock RG + 4))) ltac:(lia)) as X. rewrite Z2Nat.id in X by lia.
    replace (rg_lock RG + 4 + (a - (rg_lock RG + 4))) with a in X by lia. rewrite X. discriminate.
  - pose proof (LK8 (Z.to_nat (a - (rg_lock RG + 8))) ltac:(lia)) as X. rewrite Z2Nat.id in X by lia.
    replace (rg_lock RG + 8 + (a - (rg_lock RG + 8))) with a in X by lia. rewrite X. discriminate. }
assert (LKtb : aview SEGS (w_H W) (ms_mem ms1) (rg_lock RG) = Some 0).
{ unfold aview. pose proof (LK0 0%nat ltac:(lia)) as X. cbn [Z.of_nat] in X.
  rewrite Z.add_0_r in X. rewrite X. vm_compute. reflexivity. }
pose proof (proj1 HJ2) as HARl.
eassert (HJX : ajournal_gx_x (SK := SK) SEGS B PST ARx (G_RR B RG) 0 [] RR_STK_x (spZ regs) (rr_fp G0 FD es h cap out)
  ly S Hp W mem md _ _ _ _ _ _ _ _).
{ eapply ajournal_gx_pack_x; [rewrite WS; lia | lia | rewrite !Z.add_0_r; exact HJ2 | apply gagree_refl | intros a Ha Hn; lia]. }
assert (HNOWN : forall a, rg_lock RG <= a < rg_lock RG + 12 -> ~ aowned B ly S2 a).
{ intros a Ha Ho. destruct (RGIMG a ltac:(unfold rg_rng; left; exact Ha)) as (Hi & Hno & _).
  apply Hno. exact (proj1 (alx_owned_image _ _ _ LAWS ly S2 Hp W (ms_mem ms1) _ a HARl Hi) Ho). }
eapply SRr_bind.
{ eapply (aj_gx_entry_at_x B PST ARx LAWS (G_RR B RG) 0 [] ESTACK (SIGMA WS_pthread_mutex_lock)
    (fun a => rg_lock RG + 4 <= a < rg_lock RG + 8)
    (fun (_ : bvmap 5 word) (mem' : word -> option byte) => val_mem SEGS (mrestrict (w_H W) mem') (rg_lock RG + 4) 4 16)
    W _ _ RR_STK_x (spZ regs) (rr_fp G0 FD es h cap out) ly S Hp W mem md _ _ _ _ _ _ (-96) _ HG eq_refl HJX).
  - exact HSPc.
  - reflexivity.
  - lia.
  - lia.
  - rewrite WS, Hes. lia.
  - rewrite Q3, (EEb 3%nat 3%bv ltac:(lia) eq_refl). exact Hgp.
  - rewrite Q4, (EEb 4%nat 4%bv ltac:(lia) eq_refl). exact Htp.
  - exact Q1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros a. destruct (Z_lt_ge_dec a (rg_lock RG + 4)); [right; lia|].
    destruct (Z_lt_ge_dec a (rg_lock RG + 8)); [left; lia | right; lia].
  - intros a Ha _. exact (LKV a ltac:(lia)).
  - intros a Ha HnG. exfalso. apply HnG. unfold G_RR. apply inG_cons. left. unfold in_zr. cbn [fst snd]. lia.
  - intros HPRE2 HSC. apply (ALOCK _ _ _ _ _ _ _ (rg_lock RG) 0 HPRE2).
    + exact QA0.
    + lia.
    + pose proof (Z.div_mod (rg_lock RG) 8 ltac:(lia)). pose proof (Z.div_mod (rg_lock RG) 4 ltac:(lia)).
      pose proof (Z.mod_pos_bound (rg_lock RG) 4 ltac:(lia)). lia.
    + lia.
    + exact LKtb.
    + reflexivity.
    + exact LK4.
    + intros a Ha. split; [exact (LKV a ltac:(lia))|]. rewrite HSPc. unfold ESTACK. unfold spZ in *. lia.
    + intros a Ha. split; [|split].
      * apply (RGWR (w_H W) (ms_mem ms1) a); [left; lia|].
        apply (hidden_not_img SEGS W (Z_to_bv 64 a)). rewrite unsigned_lit_small by lia.
        exact (proj1 (RGIMG a ltac:(unfold rg_rng; left; lia))).
      * exact (HNOWN a ltac:(lia)).
      * rewrite HSPc. unfold ESTACK. unfold spZ in *. lia.
    + intros a Ha HKp. refine (proj2 (proj2 (HG a _)) (proj1 (proj2 HKp))). unfold G_RR. apply inG_cons. left. unfold in_zr. cbn [fst snd]. lia. }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & HLK3 & Hfr3 & Hpres3).
assert (KV5 : forall a, rr_wt ly S a -> ~ rr_lkw a -> aview SEGS (w_H W) mem3 a = aview SEGS (w_H W) mem a).
{ intros a Hw Hl. pose proof (rr_wt_lo ly S Hp W mem md a HAR Hw) as WA.
  rewrite (Hfr3 a ltac:(revert WA; pose proof asan_consts as (Cx & _); revert Cx; clear; intros; lia) ltac:(exact Hl)
    ltac:(revert WA WB; clear; unfold ESTACK; intros; lia)).
  exact (KV4 a Hw). }
pose proof (fun a Hi Ha => Hpres3 a (PRES a Hi Ha)) as PRES5. clear PRES KV4. rename PRES5 into PRES.
pose proof (ajournal_gx_AR_x SEGS B PST ARx (G_RR B RG) 0 [] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HAR3.
destruct (rr_carry ly S S2 Hp Hp W mem md mem3 md3 G0 es c O mx cap out h j FD rr_lkw HAR HAR3 Eab KV5 PRES
  (fun a (Hx : rr_lkw a) => Hx) RGPx HREL HOUT HWAKE HSRC) as (CREL & COUT & CWAKE & CGS & CSRC).
(* the base registers at regs3: the lock keeps the callee-saved ones *)
assert (M2 : getr regs3 2 = w64 (spZ regs - RR_FRAME)) by (etransitivity; [apply (HP3 2 ltac:(unfold acallee_saved; lia)) | exact Lr2]).
assert (M3 : getr regs3 3 = getr regs 3) by (etransitivity; [apply (HP3 3 ltac:(unfold acallee_saved; lia)) | exact Lr3]).
assert (M4 : getr regs3 4 = getr regs 4) by (etransitivity; [apply (HP3 4 ltac:(unfold acallee_saved; lia)) | exact Lr4]).
assert (M8 : getr regs3 8 = w64 (spZ regs)) by (etransitivity; [apply (HP3 8 ltac:(unfold acallee_saved; lia)) | exact Lr8]).
assert (M9 : getr regs3 9 = w64 (spZ regs - RR_FRAME)) by (etransitivity; [apply (HP3 9 ltac:(unfold acallee_saved; lia)) | exact Lr9]).
assert (M18 : getr regs3 18 = w64 F) by (etransitivity; [apply (HP3 18 ltac:(unfold acallee_saved; lia)) | exact Lr18]).
assert (M19 : getr regs3 19 = w64 FD) by (etransitivity; [apply (HP3 19 ltac:(unfold acallee_saved; lia)) | exact Lr19]).
assert (M20 : getr regs3 20 = w64 F) by (etransitivity; [apply (HP3 20 ltac:(unfold acallee_saved; lia)) | exact Lr20]).
assert (M21 : getr regs3 21 = w64 (shadow_addr F)) by (etransitivity; [apply (HP3 21 ltac:(unfold acallee_saved; lia)) | exact Lr21]).
assert (M22 : getr regs3 22 = w64 SHADOW_OFF) by (etransitivity; [apply (HP3 22 ltac:(unfold acallee_saved; lia)) | exact Lr22]).
assert (M26 : getr regs3 26 = getr regs 26) by (etransitivity; [apply (HP3 26 ltac:(unfold acallee_saved; lia)) | exact Lr26]).
assert (M27 : getr regs3 27 = getr regs 27) by (etransitivity; [apply (HP3 27 ltac:(unfold acallee_saved; lia)) | exact Lr27]).
(* ---- the seat at 0x83ee8: only g_nsrc and g_src are read, and nothing is written ---- *)
pose proof CREL as (CV8 & CW8 & CV4 & CW4 & CV4c & CW4c & Clen & CGin & Ctab & Cok & Cnd).
pose proof (pa_obj_img 7 ltac:(lia)) as Ho7. pose proof (pa_obj_img 8 ltac:(lia)) as Ho8.
pose proof (pa_val_range (A_OBJ 7)) as PV7. pose proof (pa_val_range (A_OBJ 8)) as PV8.
pose proof HRGP as (_ & _ & (Dsn & _) & _). unfold zdisj in Dsn. cbn [fst snd] in Dsn.
remember (Eimg (Ereg regs3 (rr_hextra (Z.of_nat (length es)) G0))) as En eqn:HEn.
assert (HEIn : img_env VAL A_LIM En) by (subst En; apply Eimg_env).
assert (HAEn : env_agree 32 (Ereg regs3 (rr_hextra (Z.of_nat (length es)) G0)) En)
  by (rewrite HEn; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (En32 : ew En 32 = Z_to_bv 64 (Z.of_nat (length es)))
  by (subst En; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 0)).
assert (En33 : ew En 33 = Z_to_bv 64 G0)
  by (subst En; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 1)).
assert (EEn : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew En n = getr regs3 r)
  by (intros n r Hn; subst En; pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5;
      rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
assert (En7 : ew En (A_OBJ 7) = Z_to_bv 64 (VAL (A_OBJ 7)))
  by (apply img_env_atomP; [exact HEIn | unfold A_OBJ, A_TEXT, A_LIM; lia]).
assert (En8 : ew En (A_OBJ 8) = Z_to_bv 64 (VAL (A_OBJ 8)))
  by (apply img_env_atomP; [exact HEIn | unfold A_OBJ, A_TEXT, A_LIM; lia]).
assert (HSn : st_ok_pi SEGS VAL En ss_rrh
  (restrict (w_H W) (mkst regs3 (Z_to_bv 64 (BASE + A_rr_held)) mem3 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_rrh. apply pa_entry_st_ok_full.
  - subst En. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold rr_hregions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite En7, unsigned_lit_small by lia. rewrite <- RGNSRC.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS En _ (rg_nsrc RG) 0 4 (SOff 32 0) (Z.of_nat (length es)));
      [cbn [sv_denot]; rewrite En32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. exact CV4.
    + rewrite En8, unsigned_lit_small by lia. rewrite <- RGSRC.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS En _ (rg_src RG) 0 8 (SOff 33 0) G0);
      [cbn [sv_denot]; rewrite En33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | cbn; destruct (alx_blocks _ _ _ LAWS ly S2 Hp W mem3 md3 G0 ATABLE HAR3 CGin) as (_ & Hg1 & Hg2 & _);
        change (req_size ATABLE) with 896 in Hg2; pose proof asan_consts as (Cz & _); lia
      | cbn; lia |].
      rewrite Z.add_0_r. exact CV8.
  - apply pairwise_disjoint_of_extents. unfold rr_hregions, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite En7, En8, !unsigned_lit_small by lia. rewrite <- RGNSRC, <- RGSRC.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; first [exact I | revert Dsn; clear; intros; lia].
  - unfold facts_ok; cbn; tauto. }
clear HEn HS.
destruct HJ3 as (HSTKz & HXOz & (memS & HJi & Hagz) & Houtz).
paj_run_sh_x RUNP HSn HJi.
{ intros a (r & Hin & Hr). cbn [ss_mem ss_rrh rr_hregions In] in Hin.
  repeat (destruct Hin as [<- | Hin];
    [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; lia|]). destruct Hin. }
lazymatch goal with HF : frame_of ?Ex ?rs ?m (ms_mem ?x) |- _ =>
  pose proof (frame_of_read_only Ex rs m (ms_mem x) ltac:(vm_compute; reflexivity) HF) as Em1 end.
(* what both cuts need of the locked state *)
assert (SPhi : spZ regs <= 2 ^ 47) by (revert Hshi H47; clear; intros; lia).
assert (SPlo : 0 <= spZ regs - RR_FRAME < 2 ^ 64)
  by (revert SPhi WB; pose proof asan_consts as (Cz & _); revert Cz; unfold RR_FRAME; clear; intros; lia).
assert (HSV1 : forall i, (i < 11)%nat -> val_mem SEGS (arm W mem3) (spZ regs - RR_FRAME + 8 + 8 * Z.of_nat i) 8
  (bv_unsigned (getr regs (nth i RR_SAVED 0%bv)))).
{ intros i Hi. apply (rr_vm_keep W (ms_mem ms1) mem3); [|exact (HSV0 i Hi)].
  intros x Hx. apply Hfr3;
  [ revert Hx Hi SPhi WB; unfold RR_FRAME; pose proof asan_consts as (Cz & _); revert Cz; clear; intros; lia
  | revert Hx HlkR WB; unfold RR_FRAME; pose proof asan_consts as (Cz & _); revert Cz; clear; intros; lia
  | revert Hx; unfold RR_FRAME, ESTACK; clear; intros; lia ]. }
assert (HFL1 : val_mem SEGS (arm W mem3) (F + 56) 8 FL).
{ apply (rr_vm_keep W (ms_mem ms1) mem3); [|exact HFL0].
  intros x Hx. apply Hfr3;
  [ revert Hx HF4096 HFceil; pose proof asan_consts as (Cz & _); revert Cz; clear; intros; lia
  | revert Hx HlkR HFimg; clear; intros; lia
  | revert Hx HFceil WB; pose proof asan_consts as (Cz & _); revert Cz; unfold ESTACK, RR_FRAME; clear; intros; lia ]. }
assert (LKt : alock_at RG W mem3 true).
{ split; [|split; [exact HLK3 | split]].
  - apply (rr_vm_keep W (ms_mem ms1) mem3); [|exact LK0].
    intros x Hx. apply Hfr3; [revert Hx HlkR; clear; intros; lia | revert Hx; clear; intros; lia
    | revert Hx HlkR WB; pose proof asan_consts as (Cz & _); revert Cz; unfold ESTACK, RR_FRAME; clear; intros; lia].
  - apply (rr_vm_keep W (ms_mem ms1) mem3); [|exact LK8].
    intros x Hx. apply Hfr3; [revert Hx HlkR; clear; intros; lia | revert Hx; clear; intros; lia
    | revert Hx HlkR WB; pose proof asan_consts as (Cz & _); revert Cz; unfold ESTACK, RR_FRAME; clear; intros; lia].
  - intros i Hi. unfold arm. apply (RGWR (w_H W) mem3 (rg_lock RG + i)); [left; lia|].
    apply (hidden_not_img SEGS W). rewrite unsigned_lit_small by lia.
    exact (proj1 (RGIMG (rg_lock RG + i) ltac:(unfold rg_rng; left; lia))). }
assert (HNle : 0 <= Z.of_nat (length es) <= 16) by (revert Clen; clear; intros; lia).
assert (HJg : forall mX mdX kX, ajournal_x (SK := SK) SEGS B PST ARx (RR_STK_x + 0) (spZ regs + 0) (rr_fp G0 FD es h cap out)
    ly S Hp W memS md [(0, fpos)] ly S2 Hp W mX mdX kX ->
  ajournal_gx_x (SK := SK) SEGS B PST ARx (G_RR B RG) 0 [] RR_STK_x (spZ regs) (rr_fp G0 FD es h cap out) ly S Hp W mem md
    [(0, fpos)] ly S2 Hp W mX mdX kX).
{ intros mX mdX kX HJx. eapply ajournal_gx_pack_x; [rewrite WS; lia | lia | exact HJx | exact Hagz | intros a Ha Hn; lia]. }
psrr_branch_pi_x RUNP BR HSn.
+ (* g_nsrc <= 0: the table is empty, to the unlock tail 0x83fc4 with RRU None *)
  cbn [sv_denot] in Hc0. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned, En32 in Hc0.
  rewrite (rr_blez _ (Z.of_nat (length es)) eq_refl HNle) in Hc0. apply Z.eqb_eq in Hc0.
  assert (Hnil : es = []) by (destruct es; [reflexivity | cbn [length] in Hc0; lia]).
  paj_run_to_sh_x RUNTOP HSn HJi A_rr_unlock.
  { intros a (r & Hin & Hr). cbn [ss_mem ss_rrh rr_hregions In] in Hin.
    repeat (destruct Hin as [<- | Hin];
      [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; lia|]). destruct Hin. }
  lazymatch goal with HF : frame_of ?Ex ?rs ?m (ms_mem ?x) |- _ =>
    pose proof (frame_of_read_only Ex rs m (ms_mem x) ltac:(vm_compute; reflexivity) HF) as Em2 end.
  lazymatch type of HSn with st_ok_pi _ _ _ _ (restrict _ ?msx) =>
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs3 _ RRP_KEPT HSn HAEn ltac:(vm_compute; reflexivity)) as HKr;
    cbn [ms_regs restrict] in HKr end.
  pmkst HSn. rewrite Em2, Em1 in HJi |- *.
  apply KU. unfold RRU, rregs_base, RHELD, RLIVE, rr_frame, rr_saved.
  cbn [rsp0 rN rFP rtr rnth rxregs rxly rxS rxHp rxW rxmem rxmd rxch rxG0 rxFD rxes rxj rxh rxc rxO rxmx rxcap rxout rxrest rxkr].
  eexists _, ly, S2, Hp, mem3, _, _, F, FL.
  split; [reflexivity|].
  split.
  { split; [unfold spZ; rewrite (HKr 2%bv ltac:(cbv; tauto)), M2;
            unfold w64; apply unsigned_lit_small; unfold RR_FRAME in SPlo |- *; exact SPlo|].
    split; [rewrite (HKr 3%bv ltac:(cbv; tauto)); exact M3|].
    split; [rewrite (HKr 4%bv ltac:(cbv; tauto)); exact M4|].
    split; [rewrite (HKr 8%bv ltac:(cbv; tauto)); exact M8|].
    split; [rewrite (HKr 9%bv ltac:(cbv; tauto)); exact M9|].
    split; [rewrite (HKr 18%bv ltac:(cbv; tauto)); exact M18|].
    split; [rewrite (HKr 20%bv ltac:(cbv; tauto)); exact M20|].
    split; [rewrite (HKr 21%bv ltac:(cbv; tauto)); exact M21|].
    split; [rewrite (HKr 22%bv ltac:(cbv; tauto)); exact M22|].
    split; [rewrite (HKr 26%bv ltac:(cbv; tauto)); exact M26|].
    rewrite (HKr 27%bv ltac:(cbv; tauto)); exact M27. }
  split; [exact Hpos|].
  split.
  { split.
    { exists fpos. split; [exact (HJg _ _ _ HJi)|].
      split; [eapply (ajournal_gx_rom_view_x SEGS B PST ARx);
        first [exact LAWS | exact Hsegs | exact (HJg _ _ _ HJi) | exact HROMO | exact PSTR | exact HROM]|].
      split; [intros a Hi _ _ Ha; exact (PRES a Hi Ha)|].
      split; [split; [reflexivity | split; [reflexivity | split; [exact HFL1 | exact HSV1]]]|].
      split; [exact LKt | exact CWAKE]. }
    split; [exact CREL|]. split; [exact COUT|].
    split; [rewrite Eab; exact HPERM|].
    split; [exact CGS|]. split; [exact CSRC|].
    split; [exact HMOs|]. split; [rewrite Hbb2; exact HLIVE|].
    (* the room round: RBASE's budget at S2 (HRM2, RPF_of at the seat) and its count fact (the blocks are the
       entry's) *)
    split; [exact HRM2 | rewrite Eab; exact HCNTP]. }
  rewrite Hnil. intros e He. destruct He.
+ (* g_nsrc > 0: the scan's setup 0x83ef4-0x83f10, to the loop head 0x83f14 with RRL 0 *)
  cbn [sv_denot] in Hc0. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned, En32 in Hc0.
  rewrite (rr_blez _ (Z.of_nat (length es)) eq_refl HNle) in Hc0. apply Z.eqb_neq in Hc0.
  assert (Hne : (0 < length es)%nat) by lia.
  paj_run_to_sh_x RUNTOP HSn HJi A_rr_scan.
  { intros a (r & Hin & Hr). cbn [ss_mem ss_rrh rr_hregions In] in Hin.
    repeat (destruct Hin as [<- | Hin];
      [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; lia|]). destruct Hin. }
  lazymatch goal with HF : frame_of ?Ex ?rs ?m (ms_mem ?x) |- _ =>
    pose proof (frame_of_read_only Ex rs m (ms_mem x) ltac:(vm_compute; reflexivity) HF) as Em2 end.
  (* the loop's registers: a1 = G0, a2 = 56 |es|, a3 = SHADOW_OFF + G0 / 8, s7, s8 = 0, s9 *)
  destruct (alx_blocks _ _ _ LAWS ly S2 Hp W mem3 md3 G0 ATABLE HAR3 CGin) as (_ & HG4096 & HGceil & _).
  change (req_size ATABLE) with 896 in HGceil.
  assert (HG64 : 0 <= G0 < 2 ^ 64) by (pose proof asan_consts as (Cz & _); lia).
  prreg HSn (11%bv : bv 5) N11. prreg HSn (12%bv : bv 5) N12. prreg HSn (13%bv : bv 5) N13.
  prreg HSn (23%bv : bv 5) N23. prreg HSn (24%bv : bv 5) N24. prreg HSn (25%bv : bv 5) N25.
  lazymatch type of HSn with st_ok_pi _ _ _ _ (restrict _ ?msx) =>
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs3 _ RRP_KEPT HSn HAEn ltac:(vm_compute; reflexivity)) as HKr;
    cbn [ms_regs restrict] in HKr end.
  rewrite En32, (rr_a2 _ (Z.of_nat (length es)) eq_refl HNle) in N12.
  rewrite En33, (rr_srl8 G0 HG64) in N13.
  rewrite (EEn 22%nat 22%bv eq_refl), M22 in N13.
  rewrite YI08.alu64_add_lit in N13.
  change 339%nat with (A_HI 59) in N23. change 340%nat with (A_HI 60) in N25.
  rewrite (img_env_atomP En (A_HI 59) HEIn ltac:(unfold A_HI, A_TEXT, A_LIM; lia)), HH59 in N23.
  rewrite (img_env_atomP En (A_HI 60) HEIn ltac:(unfold A_HI, A_TEXT, A_LIM; lia)), HH60 in N25.
  pmkst HSn. rewrite Em2, Em1 in HJi |- *.
  apply KL. unfold RRL, rregs_held, rregs_base, RHELD, RLIVE, rr_frame, rr_saved.
  cbn [rsp0 rN rFP rtr rnth rxregs rxly rxS rxHp rxW rxmem rxmd rxch rxG0 rxFD rxes rxj rxh rxc rxO rxmx rxcap rxout rxrest rxkr].
  eexists _, ly, S2, Hp, mem3, _, _, F, FL.
  split; [reflexivity|].
  split.
  { split.
    { split; [unfold spZ; rewrite (HKr 2%bv ltac:(cbv; tauto)), M2;
              unfold w64; apply unsigned_lit_small; unfold RR_FRAME in SPlo |- *; exact SPlo|].
      split; [rewrite (HKr 3%bv ltac:(cbv; tauto)); exact M3|].
      split; [rewrite (HKr 4%bv ltac:(cbv; tauto)); exact M4|].
      split; [rewrite (HKr 8%bv ltac:(cbv; tauto)); exact M8|].
      split; [rewrite (HKr 9%bv ltac:(cbv; tauto)); exact M9|].
      split; [rewrite (HKr 18%bv ltac:(cbv; tauto)); exact M18|].
      split; [rewrite (HKr 20%bv ltac:(cbv; tauto)); exact M20|].
      split; [rewrite (HKr 21%bv ltac:(cbv; tauto)); exact M21|].
      split; [rewrite (HKr 22%bv ltac:(cbv; tauto)); exact M22|].
      split; [rewrite (HKr 26%bv ltac:(cbv; tauto)); exact M26|].
      rewrite (HKr 27%bv ltac:(cbv; tauto)); exact M27. }
    split; [rewrite (HKr 19%bv ltac:(cbv; tauto)); exact M19|].
    exact N23. }
  split; [exact N25|].
  split; [rewrite N11; exact En33|].
  split; [exact N12|].
  split; [rewrite N13; unfold w64; f_equal; cbn [Z.of_nat]; lia|].
  split; [rewrite N24; reflexivity|].
  split; [exact Hpos|]. split; [exact Hne|].
  split; [intros i Hi; lia|].
  split.
  { exists fpos. split; [exact (HJg _ _ _ HJi)|].
    split; [eapply (ajournal_gx_rom_view_x SEGS B PST ARx);
      first [exact LAWS | exact Hsegs | exact (HJg _ _ _ HJi) | exact HROMO | exact PSTR | exact HROM]|].
    split; [intros a Hi _ _ Ha; exact (PRES a Hi Ha)|].
    split; [split; [reflexivity | split; [reflexivity | split; [exact HFL1 | exact HSV1]]]|].
    split; [exact LKt | exact CWAKE]. }
  split; [exact CREL|]. split; [exact COUT|].
  split; [rewrite Eab; exact HPERM|].
  split; [exact CGS|]. split; [exact CSRC|].
  split; [exact HMOs|]. split; [rewrite Hbb2; exact HLIVE|].
  split; [exact HRM2 | rewrite Eab; exact HCNTP].
Qed.

(* ---- route R (a Theorem Labs lane crew, G8-A; a Theorem Labs lane): PRO at a world relation R, over a Theorem Labs lane 1's R statements
   (W_relay_remove_cx.v Section wR: rr_pro_stmt_xR, RRL_xR / RRU_xR / rPOST_xR).  PRO's input RBASE has no journal, so
   the strict walk is kept as the CORE (strict SRr to the disjunction of its three exits); each strict exit gives its R
   exit at every R containing wle (the journal by ajournal_gx_xR_mono, rPOST by W_contract_xR_relay.rr_post_xR_of_x),
   and the core is lifted (SRr_SRrG) and bound (SRrG_bind) to the R continuations.  The copied proof changes only at
   its three exits (a Theorem Labs lane's routeR/g8/mkpro.py). ---- *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Lemma RLIVE_xR_of_x : forall cx F FL ly1 S1 Hp1 W1 m1 md1 k1,
  RLIVE B PST ARx RG cx F FL ly1 S1 Hp1 W1 m1 md1 k1 -> RLIVE_xR B PST ARx RG R cx F FL ly1 S1 Hp1 W1 m1 md1 k1.
Proof.
intros cx F FL ly1 S1 Hp1 W1 m1 md1 k1 (fpos & HJ & REST). exists fpos. split; [|exact REST].
eapply ajournal_gx_xR_mono; [exact WLE_R | exact HJ].
Qed.
Lemma RHELD_xR_of_x : forall cx F FL ly1 S1 Hp1 W1 m1 md1 k1,
  RHELD B PST ARx MT RP RG cx F FL ly1 S1 Hp1 W1 m1 md1 k1 -> RHELD_xR B PST ARx MT RP RG R cx F FL ly1 S1 Hp1 W1 m1 md1 k1.
Proof. intros cx F FL ly1 S1 Hp1 W1 m1 md1 k1 (HL & REST). split; [exact (RLIVE_xR_of_x cx F FL ly1 S1 Hp1 W1 m1 md1 k1 HL) | exact REST]. Qed.
Lemma RRL_xR_of_x : forall cx k W1 c1, RRL B PST ARx MT RP RG cx k W1 c1 -> RRL_xR B PST ARx MT RP RG R cx k W1 c1.
Proof.
intros cx k W1 c1 H. unfold RRL in H. unfold RRL_xR.
destruct H as (regs1 & ly1 & S1 & Hp1 & m1 & md1 & k1 & F & FL & H).
exists regs1, ly1, S1, Hp1, m1, md1, k1, F, FL.
repeat match type of H with _ /\ _ => let Ha := fresh "Ha" in destruct H as [Ha H]; split; [exact Ha|] end.
exact (RHELD_xR_of_x _ _ _ _ _ _ _ _ _ _ H).
Qed.
Lemma RRU_xR_of_x_None : forall cx W1 c1, RRU B PST ARx MT RP RG cx None W1 c1 -> RRU_xR B PST ARx MT RP RG R cx None W1 c1.
Proof.
intros cx W1 c1 H. unfold RRU in H. unfold RRU_xR.
destruct H as (regs1 & ly1 & S1 & Hp1 & m1 & md1 & k1 & F & FL & Hc & Hb & Hfd & HH & Hne).
exists regs1, ly1, S1, Hp1, m1, md1, k1, F, FL.
split; [exact Hc|]. split; [exact Hb|]. split; [exact Hfd|].
split; [exact (RHELD_xR_of_x _ _ _ _ _ _ _ _ _ _ HH) | exact Hne].
Qed.
Theorem rr_pro_xR : rr_pro_stmt_xR B PST ARx MT RP MMAX RG R.
Proof.
unfold rr_pro_stmt_xR. intros cx HB KL KU.
enough (CORE : SRr SEGS (rxW cx) (cfg_at SEGS A_rr_entryP (rxregs cx) (rxmem cx) (rxmd cx))
  (fun W2 c2 => RRL B PST ARx MT RP RG cx 0 W2 c2 \/ RRU B PST ARx MT RP RG cx None W2 c2 \/ rPOST B PST ARx MT RP RG cx W2 c2)).
{ eapply (YA0nH.SRrG_bind SEGS R R_trans); [apply (YA0nH.SRr_SRrG SEGS R WLE_R); exact CORE|].
  intros W2 c2 _ [H2 | [H2 | H2]].
  - exact (KL W2 c2 (RRL_xR_of_x cx 0 W2 c2 H2)).
  - exact (KU W2 c2 (RRU_xR_of_x_None cx W2 c2 H2)).
  - apply (YA0nH.SRrG_ret SEGS R R_refl). unfold rPOST in H2. unfold rPOST_xR.
    exact (W_contract_xR_relay.rr_post_xR_of_x B PST ARx R WLE_R MT RP RG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H2). }
clear KL KU. revert HB. destruct cx as [regs ly S Hp W mem md ch G0 FD es j h c O mx cap out rest kr]. intros HB.
unfold RBASE in HB.
cbn [rxregs rxly rxS rxHp rxW rxmem rxmd rxch rxG0 rxFD rxes rxj rxh rxc rxO rxmx rxcap rxout rxrest rxkr rsp0 rN rFP rtr rnth] in HB.
destruct HB as (HPRE & H32 & HCNT & RGP & H10 & RFD & HLOCK & HWAKE & HREL & HOUT & HROM & HSRC & HPERM & HTRM & HLIVE & HMOK
  & HRM & HCNTP).
cbn [rxregs rxW rxmem rxmd].
pose proof RGP as RGPx. destruct RGP as (RGLOCK & RGNSRC & RGSRC & RGAL8 & RGAL4 & RGSAL & RGIMG & RGWR & RGSEP).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
destruct (rr_entry W ly S Hp regs mem md ch HPRE H32) as [HS SHOK].
pose proof (ajournal_x_init (SK := SK) SEGS B PST ARx RR_STK_x (rr_fp G0 FD es h cap out) ly S Hp W regs mem md ch HPRE) as HJ.
assert (HFPcl : ~ YI16.sink_open_fp (rr_fp G0 FD es h cap out)).
{ unfold rr_fp. apply (rr_fp_closed ly S Hp W mem md _ rest (proj1 HPRE)). cbn [app]. rewrite <- !app_assoc. exact HPERM. }
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
remember (Eimg (Ereg regs rr_extra)) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
by (intros n r Hn; subst E; pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5;
rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 (as_uar_cell B)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (HAE : env_agree 32 (Ereg regs rr_extra) E) by (rewrite HE; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clear HE.
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : RR_STK_x = 17072) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
unfold cfg_at. change (w64 A_rr_entryP) with (Z_to_bv 64 A_rr_entryP). unfold A_rr_entryP, A_rr_entry.
paj_run_tok_x RUN0 HS HJ SHOK Bspan. { awr_ok_tac. exact Usp. }
rr_grab.
assert (WB : alloc_ceiling + 16944 <= spZ regs) by lia.
(* the prologue's stores are into the frame: every watched byte kept, presence grows *)
assert (KV1 : forall a, rr_wt ly S a -> aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem a).
{ apply (kv_run E _ W mem mem (ms_mem ms) (rr_wt ly S) (fun a _ => eq_refl) HFr).
  intros a Hw. pose proof (rr_wt_lo ly S Hp W mem md a HAR Hw) as WA. rr_nowin WA WB. }
pose proof (pres_grow (w_H W) mem mem (ms_mem ms) (fun a _ Ha => Ha) HGr) as PRES. clear HFr HGr.
(* the call to __asan_stack_malloc_0 (64): the fake frame *)
pmkst HS.
prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
rewrite (palf_sm0 B TLF).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
  eapply (aj_stack_malloc_pres_at_raw_x SEGS B PST ARx LAWS Hsegs (pal_env B TL) OWNLOW WFx WFL SMALLOC 0 ASMP ltac:(lia)
  W rg mm RR_STK_x (spZ regs) (rr_fp G0 FD es h cap out) ly S Hp W mem md [] ly S Hp _ 0 (-96) _ HJ) end.
  - unfold spZ at 1. rewrite R2, Usp. rewrite unsigned_lit_small by (unfold spZ in *; lia). lia.
  - reflexivity. - lia. - rewrite WS, Hes. lia.
  - rewrite R3, (EE 3%nat 3%bv eq_refl). exact Hgp. - rewrite R4, (EE 4%nat 4%bv eq_refl). exact Htp.
  - exact R1. - apply ret_ok_codeptr_v; [lia | reflexivity].
  - exact HCNT. }
cbv beta. intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & fpos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2 & Hbb2 & Hz & Hflag & HK & HPR0 & HRAW & HFS).
(* the room round: the seat's state is a set_fs of S, so RPF_of carries RBASE's room to it (the lock keeps S2); the
   meter: the seat is a set_fs step, so MO_FR charges it nothing *)
pose proof HFS as (fS & ES2). pose proof (RPF_of RP S fS _ HRM) as HRM2. rewrite <- ES2 in HRM2.
pose proof (MO_FR S fS) as HMOs. rewrite <- ES2 in HMOs. clear HFS ES2 fS.
assert (KV2 : forall a, rr_wt ly S a -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem a).
{ eapply (kv_smalloc ly S S2 Hp Hp W mem _ mem2 _ md2 _ _ (rr_wt ly S) (proj1 HJ) (proj1 HJ2)); [idtac | exact HK | exact HRAW | auto | exact KV1].
  lia. }
pose proof (fun a Hi Ha => HPR0 a Hi (PRES a Hi Ha)) as PRES2. clear PRES HPR0 HRAW KV1. rename PRES2 into PRES.
set (F := frame_addr ly 0 fpos) in *. set (FL := flag_addr ly 0 fpos) in *.
pose proof (proj1 HJ) as HARa. pose proof (proj1 HJ2) as HARb.
destruct (alx_const _ _ _ LAWS _ _ _ _ _ _ HARa) as (Kc1 & Ku1 & Kg1 & Kgu1).
destruct (alx_const _ _ _ LAWS _ _ _ _ _ _ HARb) as (Kc2 & Ku2 & Kg2 & Kgu2).
rewrite HBgot, HBcell in Kg1, Kg2. rewrite HBcell in Kc1, Kc2. rewrite (palf_got_uar B TLF) in Kgu1, Kgu2.
pose proof (palf_uar_img B TLF) as HuR.
jafter_call_keep_pi HS 34%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2; 3; 4]%nat HS2.
match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| | | | | apply Forall_nil].
  - eapply rr_region_kept_stack_aj_x; [exact HK | exact HJ2 | exact Usp | lia | lia | lia | cbn; lia | cbn; lia].
  - apply (region_kept_val_at E _ _ (A_OBJ 0) (VAL (A_OBJ 0)) 8 (VAL (A_OBJ 32)));
    [exact (HEI (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact (val_mem_of_rdword SEGS _ _ _ _ Kg1) | exact (val_mem_of_rdword SEGS _ _ _ _ Kg2) | lia].
  - apply (region_kept_val_at E _ _ (A_OBJ 32) (VAL (A_OBJ 32)) 8 SHADOW_OFF);
    [exact (HEI (A_OBJ 32) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact (val_mem_of_rdword SEGS _ _ _ _ Kc1) | exact (val_mem_of_rdword SEGS _ _ _ _ Kc2) | lia].
  - apply (region_kept_val_at E _ _ (A_OBJ 1) (VAL (A_OBJ 1)) 8 (as_uar_cell B));
    [exact (HEI (A_OBJ 1) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact (val_mem_of_rdword SEGS _ _ _ _ Kgu1) | exact (val_mem_of_rdword SEGS _ _ _ _ Kgu2) | lia].
  - apply (region_kept_val_at E _ _ 32 (as_uar_cell B) 4 1);
    [rewrite E32; apply unsigned_lit_small; lia | exact (val_mem_of_rd32 SEGS _ _ _ _ Ku1) | exact (val_mem_of_rd32 SEGS _ _ _ _ Ku2) | lia]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 34 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall m, (m < 34)%nat -> ew Ea m = ew E m) by (intros m Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
assert (HAEa : env_agree 32 (Ereg regs rr_extra) Ea) by (rewrite HEa; apply env_agree_havoc_ge; [cbv; lia | exact HAE]).
clear HEa.
prreg HS (10%bv : bv 5) RF.
(* seat the fake frame: F at atom 38 (a0), its flag FL at 512, the frame's shadow SB + F / 8 at 513 *)
assert (Hfin2 : In (0, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (frames_bounds_x SEGS B ARx LAWS _ _ _ _ _ _ 0 fpos HARb Hfin2) as (HF4096 & HFceil & HFhigh).
destruct (alx_frames _ _ _ LAWS _ _ _ _ _ _ 0 fpos HARb Hfin2) as (HFal & HFapp & HFpres & HFSpres).
pose proof (frm_off_imgP_x B ARx LAWS IMGC _ _ _ _ _ _ 0 fpos HARb Hfin2) as HFimg.
destruct (FFL _ _ _ _ _ _ 0 fpos HARb Hfin2) as (HFLp & HFLo & (HFLapp & HFLimg) & (HFL4096 & HFLz & HFLc)).
change (fs_frame_bytes 0) with 64 in *. change (64 / 8) with 8 in *. fold F FL in HFal, HFapp, HFpres, HFSpres, HFimg, HFLp, HFLo, HFLapp, HFLimg, HFL4096, HFLz, HFLc, HF4096, HFceil, HFhigh.
assert (RF' : ew Ea 38 = Z_to_bv 64 F) by (rewrite <- RF, Ha0; reflexivity).
pose proof (st_ok_pi_havoc_hi 512 Ea _ _ [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] HS ltac:(vm_compute; reflexivity)) as HS3.
clear HS. rename HS3 into HS.
remember (havoc Ea 512 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)]) as Eb eqn:HEb in HS.
assert (HEIb : img_env VAL A_LIM Eb) by (rewrite HEb; apply img_env_havoc_hi; [exact HEIa | cbv; lia]).
assert (OLDb : forall m, (m < 512)%nat -> ew Eb m = ew Ea m) by (intros m Hm; rewrite HEb; apply YN3v.ew_havoc_old; exact Hm).
assert (E512 : ew Eb 512 = Z_to_bv 64 FL) by (rewrite HEb; exact (ew_havoc_new _ 512 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 0 (Z_to_bv 64 0) ltac:(cbn; lia))).
assert (E513 : ew Eb 513 = Z_to_bv 64 (SB + F / 8)) by (rewrite HEb; exact (ew_havoc_new _ 512 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 1 (Z_to_bv 64 0) ltac:(cbn; lia))).
assert (HAEb : env_agree 32 (Ereg regs rr_extra) Eb) by (rewrite HEb; apply env_agree_havoc_ge; [cbv; lia | exact HAEa]).
clear HEb.
assert (E38 : ew Eb 38 = Z_to_bv 64 F) by (rewrite OLDb by lia; exact RF').
assert (E33b : ew Eb 33 = Z_to_bv 64 SB) by (rewrite OLDb, OLDa by lia; exact E33).
assert (HFq : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(lia)); lia).
assert (HF8 : F / 8 = 4 * (F / 32)) by (rewrite HFq at 1; replace (32 * (F / 32)) with (4 * (F / 32) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
assert (HF8lo : 512 <= F / 8) by (apply Z.div_le_lower_bound; lia).
assert (HF8hi : F / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia).
pose proof (st_ok_pi_add_fact Eb _ _ 38 (HPTR 5) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite E38, unsigned_lit_small by lia; change (2 ^ 5) with 32; lia)) as HS3.
clear HS; rename HS3 into HS.
pose proof (st_ok_pi_add_fact Eb _ _ 512 (HPTR 0) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite E512, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS3.
clear HS; rename HS3 into HS.
pose proof (st_ok_pi_add_fact Eb _ _ 513 (mkAF (SB + 512) (SB + 17592186044416) 2) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E513, unsigned_lit_small by (unfold SB; lia); change (2 ^ 2) with 4; unfold SB;
split; [lia|]; split; [rewrite HF8; replace (2147450880 + 4 * (F / 32)) with ((536862720 + F / 32) * 4) by lia; apply Z_mod_mult | lia])) as HS3.
clear HS; rename HS3 into HS.
pose proof (st_ok_pi_add_alias Eb _ _ _ _ HS (shadow_decl_ok Eb 38 33 513 F SB E38 ltac:(lia) E33b E513)) as HS3.
clear HS; rename HS3 into HS. norm_ss HS.
assert (U2b : bv_unsigned (ew Eb 2) = spZ regs) by (rewrite OLDb, OLDa by lia; exact Usp).
assert (U241 : bv_unsigned (ew Eb 241) = VAL (A_OBJ 0)) by exact (HEIb (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
assert (U242 : bv_unsigned (ew Eb 242) = VAL (A_OBJ 1)) by exact (HEIb (A_OBJ 1) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
assert (U273 : bv_unsigned (ew Eb 273) = VAL (A_OBJ 32)) by exact (HEIb (A_OBJ 32) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
assert (U32 : bv_unsigned (ew Eb 32) = as_uar_cell B) by (rewrite OLDb, OLDa, E32 by lia; apply unsigned_lit_small; lia).
assert (U38 : bv_unsigned (ew Eb 38) = F) by (rewrite E38; apply unsigned_lit_small; lia).
assert (U512 : bv_unsigned (ew Eb 512) = FL) by (rewrite E512; apply unsigned_lit_small; lia).
assert (U513 : bv_unsigned (ew Eb 513) = SB + F / 8) by (rewrite E513; apply unsigned_lit_small; unfold SB; lia).
pose proof (pa_obj_img 32 ltac:(lia)) as HcellR. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR. pose proof (pa_obj_img 1 ltac:(lia)) as HguR.
(* (palf_sep's zseps is not needed here: kept out of the context, whose lia calls it would make exponential) *)
pose proof (pa_val_range (A_OBJ 0)) as PV0. pose proof (pa_val_range (A_OBJ 1)) as PV1. pose proof (pa_val_range (A_OBJ 32)) as PV32.
(* the geometry facts in numerals, once: each region's lia then sees only what it reverts (W5's W_relay_add.v:940) *)
unfold SB, zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in C1, C3, Hslo, Hshi, H47, Hceil, Hstk0,
HcellR, HgotR, HguR, HuR, HFimg, HFapp, HF4096, HFceil, HFhigh, HFLapp, HFLimg, HFL4096, HFLc.
pose proof (st_ok_pi_add_region Eb _ _ (fframe_region 38 512 0 []) HS eq_refl
ltac:(unfold region_ok, fframe_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
change (fs_frame_bytes 0) with 64; rewrite U38; split; [lia|]; split; [lia|]; split;
[ intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFpres (F + o) ltac:(lia)))
| apply Forall_cons; [|apply Forall_nil]; apply (chunk_ok_val SEGS Eb _ F (64 - 8) 8 _ FL);
[cbn [sv_denot]; rewrite E512, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | replace (F + (64 - 8)) with (F + 64 - 8) by lia; exact (val_mem_of_rdword SEGS _ _ _ _ Hflag)] ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint, fframe_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
change (fs_frame_bytes 0) with 64; rewrite U38, U2b, U241, U242, U273, U32;
revert Hslo Hshi H47 Hceil Hstk0 C1 C3 WS HF4096 HFceil HFhigh HFimg HFapp HgotR HcellR HguR HuR PV0 PV1 PV32; clear; intros;
unfold off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; repeat split; lia)) as HS3.
clear HS; rename HS3 into HS.
pose proof (st_ok_pi_add_region Eb _ _ (fshadow_region 513 0 0 8 [YP09.mkChunk 0 (CVal 8 (SLit 0))]) HS eq_refl
ltac:(unfold region_ok, fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
change (fs_frame_bytes 0 / 8) with 8; rewrite U513; split; [unfold SB; lia|]; split; [unfold SB; lia|]; split;
[ intros o Ho; apply (apresent_writable SEGS); unfold shadow_addr in HFSpres; rewrite <- SB_SHADOW_OFF in HFSpres; apply (proj1 (HFSpres o ltac:(lia)))
| apply Forall_cons; [|apply Forall_nil]; apply (chunk_ok_val SEGS Eb _ (SB + F / 8) 0 8 _ 0); [reflexivity | zside | zside |];
rewrite Z.add_0_r; apply val_mem_zero8; intros i Hi; unfold zero_shadow, shadow_of_addr in Hz; rewrite <- SB_SHADOW_OFF in Hz; apply Hz; change (64 / 8) with 8; lia ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint, fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
change (fs_frame_bytes 0 / 8) with 8; rewrite U513, U38, U2b, U241, U242, U273, U32;
revert Hslo Hshi H47 Hceil Hstk0 C1 C3 WS HF4096 HFceil HFhigh HFimg HFapp HgotR HcellR HguR HuR PV0 PV1 PV32 HF8lo HF8hi HFq HF8; clear; intros;
unfold SB, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, alloc_ceiling in *; repeat split; lia)) as HS3.
clear HS; rename HS3 into HS. norm_ss HS.
(* the frame header and the shadow poison: a plain run, to the fd test *)
paj_run_sh_x RUNP HS HJ2.
{ intros a (r & Hin & Hr).
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [<- | Hin];
  [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U2b, ?U38, ?U513, ?U241, ?U242, ?U273, ?U32 in Hr;
    first [ lia
    | left; unfold RR_STK_x, RR_STK, RR_FRAME, DRAIN_STK_x, DRAIN_STK, DRAIN_FRAME, SL_STK, SL_FRAME, ASTACK; lia
    | right; right; right; exists 0, fpos; split; [left; reflexivity|];
      change (frame_addr ly 0 fpos) with F; change (fs_frame_bytes 0) with 64;
      first [ left; unfold in_zr; cbn [fst snd]; lia
      | right; unfold in_zr, shadow_addr; rewrite <- SB_SHADOW_OFF; cbn [fst snd]; change (64 / 8) with 8; lia ] ]
  | ]).
  destruct Hin. }
rr_grab.
assert (WAF : forall a, rr_wt ly S a -> (4096 <= a < alloc_ceiling) /\
  ~ (F <= a < F + 64) /\ ~ (SB + F / 8 <= a < SB + F / 8 + 8) /\ a <> FL).
{ intros a Hw. split; [exact (rr_wt_lo ly S Hp W mem md a HAR Hw)|].
  exact (rr_wt_fr ly S S2 Hp W mem2 md2 fpos a HARb Hfin2 Eab Hw). }
lazymatch type of HFr with frame_of _ _ _ (mrestrict _ ?m2) =>
assert (KV3 : forall a, rr_wt ly S a -> aview SEGS (w_H W) m2 a = aview SEGS (w_H W) mem a) end.
{ apply (kv_run Eb _ W mem _ _ (rr_wt ly S) KV2 HFr).
  intros a Hw. pose proof (WAF a Hw) as WA. rr_nowin WA WB. }
pose proof (pres_grow (w_H W) mem _ _ PRES HGr) as PRES3. clear PRES HFr HGr KV2. rename PRES3 into PRES.
assert (E10b : sv_denot Eb (SOff 10 0) = Z_to_bv 64 FD)
by (cbn [sv_denot]; rewrite OLDb, OLDa, (EE 10%nat 10%bv eq_refl), H10 by lia; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
psrr_branch_pi_x RUNP BR HS.
-
(* fd < 0: nothing under the lock; the frame's release 0x84000 and the return *)
assert (Hneg : FD < 0).
{ cbn [branch_taken] in Hc. rewrite E10b, bv_lts_signed in Hc. apply Z.ltb_lt in Hc.
  rewrite (fd_signed FD RFD) in Hc. change (bv_signed (sv_denot Eb (SLit 0))) with 0 in Hc. exact Hc. }
destruct (FFL _ _ _ _ _ _ 0 fpos (proj1 HJ2) Hfin2) as (HFLp' & HFLo' & _ & _).
destruct (alx_frames _ _ _ LAWS _ _ _ _ _ _ 0 fpos (proj1 HJ2) Hfin2) as (_ & _ & HFpres' & HFSpres').
change (fs_frame_bytes 0) with 64 in *. change (64 / 8) with 8 in *. fold F FL in HFLp', HFLo', HFpres', HFSpres'.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 512%nat) 0 1 0 1 []) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite U512; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable SEGS); replace (FL + o) with FL by lia; exact HFLp')
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite U512, U513, U38, U2b, U241, U242, U273, U32;
repeat split;
lazymatch goal with
| |- ?fl + 1 <= F + ?l \/ F + ?h <= ?fl + 0 =>
  destruct (Z_lt_ge_dec fl (F + l)) as [Hlt | Hge]; [left; lia|];
  destruct (Z_lt_ge_dec fl (F + h)) as [Hlt2 | Hge2]; [exfalso | right; lia];
  exact (proj2 (HFpres' FL ltac:(lia)) HFLo')
| |- ?fl + 1 <= 2147450880 + F / 8 + ?l \/ 2147450880 + F / 8 + ?h <= ?fl + 0 =>
  destruct (Z_lt_ge_dec fl (2147450880 + F / 8 + l)) as [Hlt | Hge]; [left; lia|];
  destruct (Z_lt_ge_dec fl (2147450880 + F / 8 + h)) as [Hlt2 | Hge2]; [exfalso | right; lia];
  unfold shadow_addr in HFSpres'; rewrite <- SB_SHADOW_OFF in HFSpres'; unfold SB in HFSpres';
  exact (proj2 (HFSpres' (FL - (2147450880 + F / 8)) ltac:(lia)) ltac:(replace (2147450880 + F / 8 + (FL - (2147450880 + F / 8))) with FL by lia; exact HFLo'))
| |- ?fl + 1 <= SB + F / 8 + ?l \/ SB + F / 8 + ?h <= ?fl + 0 =>
  destruct (Z_lt_ge_dec fl (SB + F / 8 + l)) as [Hlt | Hge]; [left; lia|];
  destruct (Z_lt_ge_dec fl (SB + F / 8 + h)) as [Hlt2 | Hge2]; [exfalso | right; lia];
  unfold shadow_addr in HFSpres'; rewrite <- SB_SHADOW_OFF in HFSpres';
  exact (proj2 (HFSpres' (FL - (SB + F / 8)) ltac:(lia)) ltac:(replace (SB + F / 8 + (FL - (SB + F / 8))) with FL by lia; exact HFLo'))
| |- _ =>
  revert Hslo Hshi H47 Hceil Hstk0 C1 C3 WS HgotR HcellR HguR HuR PV0 PV1 PV32 HFL4096 HFLz HFLc; clear; intros;
  unfold SB, zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia
end)) as HS3 end.
clear HS; rename HS3 into HS. norm_ss HS.
paj_run_flag_sh_x RUNF HS HJ2.
{ lia. }
{ intros a (r & Hin & Hr).
lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
cbn [In] in Hin. change (flag_addr ly 0 fpos) with FL.
repeat (destruct Hin as [<- | Hin];
[ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
  repeat match goal with Hu : bv_unsigned (ew _ _) = _ |- _ => progress rewrite Hu in Hr end;
  first [ revert Hr; clear; intros Hr; lia
  | right; revert Hr; clear; intros Hr; lia
  | left; left; revert Hr; clear; intros Hr; assert (Hws : RR_STK_x = 17072) by reflexivity; lia
  | left; right; right; right; exists 0, fpos; split; [left; reflexivity|];
    change (frame_addr ly 0 fpos) with F; change (fs_frame_bytes 0) with 64;
    first [ left; unfold in_zr; cbn [fst snd]; revert Hr; clear; intros Hr; lia
    | right; unfold in_zr, shadow_addr; rewrite <- SB_SHADOW_OFF; cbn [fst snd]; change (64 / 8) with 8;
      revert Hr; clear; intros Hr; lia ]
  ]
| ]).
destruct Hin. }
{ intros msr HSr. change (flag_addr ly 0 fpos) with FL.
lazymatch type of HSr with st_ok_pi _ _ ?Ex ?ssx _ =>
pose proof (st_ok_pi_region_nth Ex ssx msr 0 _ HSr eq_refl) as HR;
lazymatch type of HR with region_ok _ _ _ (YP09.mkRegion (Some ?n) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex (ms_mem msr) n _ cs lo hi wlo whi 0 1%N (SLit 0) 0 HR U512
ltac:(left; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V end end.
rewrite Z.add_0_r in V. pose proof (V 0%nat ltac:(lia)) as V0. cbn [Z.of_nat] in V0. rewrite Z.add_0_r in V0. exact V0. }
rr_grab.
lazymatch type of HFr with frame_of _ _ _ (mrestrict _ ?m2) =>
assert (KV4 : forall a, rr_wt ly S a -> aview SEGS (w_H W) m2 a = aview SEGS (w_H W) mem a) end.
{ apply (kv_run _ _ W mem _ _ (rr_wt ly S) KV3 HFr).
  intros a Hw. pose proof (WAF a Hw) as WA. rr_nowin WA WB. }
pose proof (pres_grow (w_H W) mem _ _ PRES HGr) as PRES4. clear PRES HFr HGr KV3. rename PRES4 into PRES.
prreg HS (1%bv : bv 5) Rr1.
assert (EabF : ablocks B ly (stack_free_state 0 fpos S2) = ablocks B ly S)
by (rewrite <- Eab; unfold ablocks; rewrite blocks_stack_free_state; reflexivity).
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. cbv beta. right; right. unfold rPOST, rr_post_x.
cbn [rxregs rxly rxS rxHp rxW rxmem rxmd rxG0 rxFD rxes rxj rxh rxc rxO rxmx rxcap rxout rxkr].
lazymatch type of HJ2 with ajournal_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?lyx ?Sx ?Hpx _ _ _ ?kx =>
lazymatch goal with |- exists _ _ _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists lyx, Sx, Hpx, r, m, d, kx end end.
destruct (rr_carry ly S (stack_free_state 0 fpos S2) Hp Hp W mem md _ _ G0 es c O mx cap out h j FD (fun _ => False)
  HAR (proj1 HJ2) EabF (fun a Hw _ => KV4 a Hw) PRES (fun a (f : False) => match f with end) RGPx HREL HOUT HWAKE HSRC)
  as (CREL & COUT & CWAKE & CGS & _).
split; [cbn [ms_regs]; rewrite Rr1, OLDb, OLDa, (EE 1%nat 1%bv eq_refl), Hra by lia; reflexivity|].
split.
{ cbn [ms_mem]. eapply ajournal_gx_pack_x; [unfold RR_STK_x, RR_STK, RR_FRAME, DRAIN_STK_x, DRAIN_STK, DRAIN_FRAME, SL_STK, SL_FRAME, ASTACK; lia | lia | | apply gagree_refl | intros a Ha; lia].
  rewrite !Z.add_0_r. apply (ajournal_x_materialize SEGS B PST ARx LAWS Hsegs). exact HJ2. }
split. { eapply (aregs_preserved_of_st_ok SEGS _ Eb _ _ regs rr_extra HS); [exact HAEb | vm_compute; reflexivity]. }
split. { intros a Hi _ _ Ha. exact (PRES a Hi Ha). }
split. { unfold rr_tr. rewrite (proj2 (Z.ltb_lt FD 0) Hneg).
  (* the seat (HMOs) then the release, a set_fs of S2 (YG01.v stack_free_state): both free at MO_FR *)
  exact (mle_station MT S S2 (stack_free_state 0 fpos S2) 0 0 MLAW HMOs
    (MO_FR S2 (mkFS (fs_hint (st_fs S2)) (del_pos (fs_live (st_fs S2)) 0 fpos)))). }
(* the room round: kr is below RBASE's budget (RMM_of), kept across the seat (HRM2, RPF_of) and the release *)
split. { apply RPF_stack_free. eapply (RMM_of RP S2 kr); [|exact HRM2]. lia. }
split. { exact (rr_alock_carry ly S W mem _ (fun _ => False) false (fun a Hw _ => KV4 a Hw) PRES (fun a _ f => f) RGPx HLOCK). }
split. { exact CWAKE. }
split. { intros a Ha _. exact (CGS a Ha). }
split. { intros _. split; [exact CREL|]. split; [exact COUT|]. rewrite EabF. apply Permutation_refl. }
intros i Hi Hge. lia.
-
(* fd >= 0: a0 = &g_lock (0x83edc-0x83ee0), pthread_mutex_lock (0x83ee4) *)
assert (Hpos : 0 <= FD).
{ cbn [branch_taken] in Hc. rewrite E10b, bv_lts_signed in Hc. apply Z.ltb_ge in Hc.
  rewrite (fd_signed FD RFD) in Hc. change (bv_signed (sv_denot Eb (SLit 0))) with 0 in Hc. exact Hc. }
paj_run_shc_x RUNP RUNC HS HJ2.
{ intros a (r & Hin & Hr).
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [<- | Hin];
  [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U2b, ?U38, ?U513, ?U241, ?U242, ?U273, ?U32 in Hr;
    first [ lia
    | left; unfold RR_STK_x, RR_STK, RR_FRAME, DRAIN_STK_x, DRAIN_STK, DRAIN_FRAME, SL_STK, SL_FRAME, ASTACK; lia
    | right; right; right; exists 0, fpos; split; [left; reflexivity|];
      change (frame_addr ly 0 fpos) with F; change (fs_frame_bytes 0) with 64;
      first [ left; unfold in_zr; cbn [fst snd]; lia
      | right; unfold in_zr, shadow_addr; rewrite <- SB_SHADOW_OFF; cbn [fst snd]; change (64 / 8) with 8; lia ] ]
  | ]).
  destruct Hin. }
rr_grab.
lazymatch type of HFr with frame_of _ _ _ (mrestrict _ ?m2) =>
assert (KV4 : forall a, rr_wt ly S a -> aview SEGS (w_H W) m2 a = aview SEGS (w_H W) mem a) end.
{ apply (kv_run Eb _ W mem _ _ (rr_wt ly S) KV3 HFr).
  intros a Hw. pose proof (WAF a Hw) as WA. rr_nowin WA WB. }
pose proof (pres_grow (w_H W) mem _ _ PRES HGr) as PRES4. clear PRES HFr HGr KV3. rename PRES4 into PRES.
(* the frame's cells, read off the state's regions before the call *)
assert (EEb : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew Eb n = getr regs r)
  by (intros n r Hn Hr; rewrite OLDb, OLDa by lia; exact (EE n r Hr)).
pose proof (st_ok_region_nth _ _ _ 2%nat _ HS eq_refl) as HRstk.
pose proof (st_ok_region_nth _ _ _ 1%nat _ HS eq_refl) as HRfr.
cbn [ms_mem restrict] in HRstk, HRfr.
eassert (HSV0 : forall i, (i < 11)%nat -> val_mem SEGS (arm W _) (spZ regs - RR_FRAME + 8 + 8 * Z.of_nat i) 8
  (bv_unsigned (getr regs (nth i RR_SAVED 0%bv)))).
{ rewrite <- U2b. apply (rr_saved_of_region Eb W _ regs _ _ _ _ _ HRstk); [|exact EEb].
  intros i Hi. do 11 (destruct i as [|i]; [cbn [nth rr_saved_atoms Z.of_nat]; cbn [In]; rr_in|]). lia. }
eassert (HFL0 : val_mem SEGS (arm W _) (F + 56) 8 FL).
{ apply (field_of_region Eb _ 38%nat F _ _ _ _ _ 56 8%N (SOff 512 0) FL HRfr U38
    ltac:(clear; cbn [In]; rr_in) ltac:(cbn [sv_denot]; rewrite E512, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
    ltac:(cbn; lia) ltac:(cbn; lia)). }
cbn [ms_mem restrict] in HSV0, HFL0.
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (10%bv : bv 5) Q10.
prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20.
prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22. prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
assert (Z2b : ew Eb 2 = Z_to_bv 64 (spZ regs)) by (rewrite <- U2b, Z_to_bv_bv_unsigned; reflexivity).
assert (HSPc : spZ (ms_regs ms1) = spZ regs + -96).
{ unfold spZ at 1. rewrite Q2, U2b. apply unsigned_lit_small. unfold spZ in *. lia. }
(* the base registers at the call, carried to the cut by aregs_preserved (all callee-saved) *)
assert (Lr2 : getr (ms_regs ms1) 2 = w64 (spZ regs - RR_FRAME))
  by (rewrite Q2, U2b; unfold w64, RR_FRAME; f_equal; lia).
assert (Lr3 : getr (ms_regs ms1) 3 = getr regs 3) by (rewrite Q3; exact (EEb 3%nat 3%bv ltac:(lia) eq_refl)).
assert (Lr4 : getr (ms_regs ms1) 4 = getr regs 4) by (rewrite Q4; exact (EEb 4%nat 4%bv ltac:(lia) eq_refl)).
assert (Lr8 : getr (ms_regs ms1) 8 = w64 (spZ regs)) by (rewrite Q8, Z2b; reflexivity).
assert (Lr9 : getr (ms_regs ms1) 9 = w64 (spZ regs - RR_FRAME))
  by (rewrite Q9, U2b; unfold w64, RR_FRAME; f_equal; lia).
assert (Lr18 : getr (ms_regs ms1) 18 = w64 F) by (rewrite Q18; exact E38).
assert (Lr19 : getr (ms_regs ms1) 19 = w64 FD)
  by (rewrite Q19, (EEb 10%nat 10%bv ltac:(lia) eq_refl); exact H10).
assert (Lr20 : getr (ms_regs ms1) 20 = w64 F) by (rewrite Q20; exact E38).
assert (Lr21 : getr (ms_regs ms1) 21 = w64 (shadow_addr F))
  by (rewrite Q21, E513; unfold shadow_addr; rewrite <- SB_SHADOW_OFF; reflexivity).
assert (Lr22 : getr (ms_regs ms1) 22 = w64 SHADOW_OFF)
  by (rewrite Q22, E33b; rewrite <- SB_SHADOW_OFF; reflexivity).
assert (Lr26 : getr (ms_regs ms1) 26 = getr regs 26) by (rewrite Q26; exact (EEb 26%nat 26%bv ltac:(lia) eq_refl)).
assert (Lr27 : getr (ms_regs ms1) 27 = getr regs 27) by (rewrite Q27; exact (EEb 27%nat 27%bv ltac:(lia) eq_refl)).
assert (QA0 : getr (ms_regs ms1) 10 = w64 (rg_lock RG)).
{ rewrite Q10. change 247%nat with (A_OBJ 6).
  rewrite (img_env_atomP Eb (A_OBJ 6) HEIb ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)), RGLOCK. reflexivity. }
pose proof (pa_obj_img 6 ltac:(lia)) as HlkR. rewrite <- RGLOCK in HlkR.
assert (LKc : alock_at RG W (ms_mem ms1) false)
  by (exact (rr_alock_carry ly S W mem _ (fun _ => False) false (fun a Hw _ => KV4 a Hw) PRES (fun a _ f => f) RGPx HLOCK)).
pose proof LKc as (LK0 & LK4 & LK8 & LKW). unfold arm in LK0, LK4, LK8, LKW.
assert (LKV : forall a, rg_lock RG <= a < rg_lock RG + 12 -> aview SEGS (w_H W) (ms_mem ms1) a <> None).
{ intros a Ha. unfold aview.
  destruct (Z_lt_ge_dec a (rg_lock RG + 4)) as [h1|h1]; [|destruct (Z_lt_ge_dec a (rg_lock RG + 8)) as [h2|h2]].
  - pose proof (LK0 (Z.to_nat (a - rg_lock RG)) ltac:(lia)) as X. rewrite Z2Nat.id in X by lia.
    replace (rg_lock RG + (a - rg_lock RG)) with a in X by lia. rewrite X. discriminate.
  - pose proof (LK4 (Z.to_nat (a - (rg_lock RG + 4))) ltac:(lia)) as X. rewrite Z2Nat.id in X by lia.
    replace (rg_lock RG + 4 + (a - (rg_lock RG + 4))) with a in X by lia. rewrite X. discriminate.
  - pose proof (LK8 (Z.to_nat (a - (rg_lock RG + 8))) ltac:(lia)) as X. rewrite Z2Nat.id in X by lia.
    replace (rg_lock RG + 8 + (a - (rg_lock RG + 8))) with a in X by lia. rewrite X. discriminate. }
assert (LKtb : aview SEGS (w_H W) (ms_mem ms1) (rg_lock RG) = Some 0).
{ unfold aview. pose proof (LK0 0%nat ltac:(lia)) as X. cbn [Z.of_nat] in X.
  rewrite Z.add_0_r in X. rewrite X. vm_compute. reflexivity. }
pose proof (proj1 HJ2) as HARl.
eassert (HJX : ajournal_gx_x (SK := SK) SEGS B PST ARx (G_RR B RG) 0 [] RR_STK_x (spZ regs) (rr_fp G0 FD es h cap out)
  ly S Hp W mem md _ _ _ _ _ _ _ _).
{ eapply ajournal_gx_pack_x; [rewrite WS; lia | lia | rewrite !Z.add_0_r; exact HJ2 | apply gagree_refl | intros a Ha Hn; lia]. }
assert (HNOWN : forall a, rg_lock RG <= a < rg_lock RG + 12 -> ~ aowned B ly S2 a).
{ intros a Ha Ho. destruct (RGIMG a ltac:(unfold rg_rng; left; exact Ha)) as (Hi & Hno & _).
  apply Hno. exact (proj1 (alx_owned_image _ _ _ LAWS ly S2 Hp W (ms_mem ms1) _ a HARl Hi) Ho). }
eapply SRr_bind.
{ eapply (aj_gx_entry_at_x B PST ARx LAWS (G_RR B RG) 0 [] ESTACK (SIGMA WS_pthread_mutex_lock)
    (fun a => rg_lock RG + 4 <= a < rg_lock RG + 8)
    (fun (_ : bvmap 5 word) (mem' : word -> option byte) => val_mem SEGS (mrestrict (w_H W) mem') (rg_lock RG + 4) 4 16)
    W _ _ RR_STK_x (spZ regs) (rr_fp G0 FD es h cap out) ly S Hp W mem md _ _ _ _ _ _ (-96) _ HG eq_refl HJX).
  - exact HSPc.
  - reflexivity.
  - lia.
  - lia.
  - rewrite WS, Hes. lia.
  - rewrite Q3, (EEb 3%nat 3%bv ltac:(lia) eq_refl). exact Hgp.
  - rewrite Q4, (EEb 4%nat 4%bv ltac:(lia) eq_refl). exact Htp.
  - exact Q1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros a. destruct (Z_lt_ge_dec a (rg_lock RG + 4)); [right; lia|].
    destruct (Z_lt_ge_dec a (rg_lock RG + 8)); [left; lia | right; lia].
  - intros a Ha _. exact (LKV a ltac:(lia)).
  - intros a Ha HnG. exfalso. apply HnG. unfold G_RR. apply inG_cons. left. unfold in_zr. cbn [fst snd]. lia.
  - intros HPRE2 HSC. apply (ALOCK _ _ _ _ _ _ _ (rg_lock RG) 0 HPRE2).
    + exact QA0.
    + lia.
    + pose proof (Z.div_mod (rg_lock RG) 8 ltac:(lia)). pose proof (Z.div_mod (rg_lock RG) 4 ltac:(lia)).
      pose proof (Z.mod_pos_bound (rg_lock RG) 4 ltac:(lia)). lia.
    + lia.
    + exact LKtb.
    + reflexivity.
    + exact LK4.
    + intros a Ha. split; [exact (LKV a ltac:(lia))|]. rewrite HSPc. unfold ESTACK. unfold spZ in *. lia.
    + intros a Ha. split; [|split].
      * apply (RGWR (w_H W) (ms_mem ms1) a); [left; lia|].
        apply (hidden_not_img SEGS W (Z_to_bv 64 a)). rewrite unsigned_lit_small by lia.
        exact (proj1 (RGIMG a ltac:(unfold rg_rng; left; lia))).
      * exact (HNOWN a ltac:(lia)).
      * rewrite HSPc. unfold ESTACK. unfold spZ in *. lia.
    + intros a Ha HKp. refine (proj2 (proj2 (HG a _)) (proj1 (proj2 HKp))). unfold G_RR. apply inG_cons. left. unfold in_zr. cbn [fst snd]. lia. }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & HLK3 & Hfr3 & Hpres3).
assert (KV5 : forall a, rr_wt ly S a -> ~ rr_lkw a -> aview SEGS (w_H W) mem3 a = aview SEGS (w_H W) mem a).
{ intros a Hw Hl. pose proof (rr_wt_lo ly S Hp W mem md a HAR Hw) as WA.
  rewrite (Hfr3 a ltac:(revert WA; pose proof asan_consts as (Cx & _); revert Cx; clear; intros; lia) ltac:(exact Hl)
    ltac:(revert WA WB; clear; unfold ESTACK; intros; lia)).
  exact (KV4 a Hw). }
pose proof (fun a Hi Ha => Hpres3 a (PRES a Hi Ha)) as PRES5. clear PRES KV4. rename PRES5 into PRES.
pose proof (ajournal_gx_AR_x SEGS B PST ARx (G_RR B RG) 0 [] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HAR3.
destruct (rr_carry ly S S2 Hp Hp W mem md mem3 md3 G0 es c O mx cap out h j FD rr_lkw HAR HAR3 Eab KV5 PRES
  (fun a (Hx : rr_lkw a) => Hx) RGPx HREL HOUT HWAKE HSRC) as (CREL & COUT & CWAKE & CGS & CSRC).
(* the base registers at regs3: the lock keeps the callee-saved ones *)
assert (M2 : getr regs3 2 = w64 (spZ regs - RR_FRAME)) by (etransitivity; [apply (HP3 2 ltac:(unfold acallee_saved; lia)) | exact Lr2]).
assert (M3 : getr regs3 3 = getr regs 3) by (etransitivity; [apply (HP3 3 ltac:(unfold acallee_saved; lia)) | exact Lr3]).
assert (M4 : getr regs3 4 = getr regs 4) by (etransitivity; [apply (HP3 4 ltac:(unfold acallee_saved; lia)) | exact Lr4]).
assert (M8 : getr regs3 8 = w64 (spZ regs)) by (etransitivity; [apply (HP3 8 ltac:(unfold acallee_saved; lia)) | exact Lr8]).
assert (M9 : getr regs3 9 = w64 (spZ regs - RR_FRAME)) by (etransitivity; [apply (HP3 9 ltac:(unfold acallee_saved; lia)) | exact Lr9]).
assert (M18 : getr regs3 18 = w64 F) by (etransitivity; [apply (HP3 18 ltac:(unfold acallee_saved; lia)) | exact Lr18]).
assert (M19 : getr regs3 19 = w64 FD) by (etransitivity; [apply (HP3 19 ltac:(unfold acallee_saved; lia)) | exact Lr19]).
assert (M20 : getr regs3 20 = w64 F) by (etransitivity; [apply (HP3 20 ltac:(unfold acallee_saved; lia)) | exact Lr20]).
assert (M21 : getr regs3 21 = w64 (shadow_addr F)) by (etransitivity; [apply (HP3 21 ltac:(unfold acallee_saved; lia)) | exact Lr21]).
assert (M22 : getr regs3 22 = w64 SHADOW_OFF) by (etransitivity; [apply (HP3 22 ltac:(unfold acallee_saved; lia)) | exact Lr22]).
assert (M26 : getr regs3 26 = getr regs 26) by (etransitivity; [apply (HP3 26 ltac:(unfold acallee_saved; lia)) | exact Lr26]).
assert (M27 : getr regs3 27 = getr regs 27) by (etransitivity; [apply (HP3 27 ltac:(unfold acallee_saved; lia)) | exact Lr27]).
(* ---- the seat at 0x83ee8: only g_nsrc and g_src are read, and nothing is written ---- *)
pose proof CREL as (CV8 & CW8 & CV4 & CW4 & CV4c & CW4c & Clen & CGin & Ctab & Cok & Cnd).
pose proof (pa_obj_img 7 ltac:(lia)) as Ho7. pose proof (pa_obj_img 8 ltac:(lia)) as Ho8.
pose proof (pa_val_range (A_OBJ 7)) as PV7. pose proof (pa_val_range (A_OBJ 8)) as PV8.
pose proof HRGP as (_ & _ & (Dsn & _) & _). unfold zdisj in Dsn. cbn [fst snd] in Dsn.
remember (Eimg (Ereg regs3 (rr_hextra (Z.of_nat (length es)) G0))) as En eqn:HEn.
assert (HEIn : img_env VAL A_LIM En) by (subst En; apply Eimg_env).
assert (HAEn : env_agree 32 (Ereg regs3 (rr_hextra (Z.of_nat (length es)) G0)) En)
  by (rewrite HEn; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (En32 : ew En 32 = Z_to_bv 64 (Z.of_nat (length es)))
  by (subst En; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 0)).
assert (En33 : ew En 33 = Z_to_bv 64 G0)
  by (subst En; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 1)).
assert (EEn : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew En n = getr regs3 r)
  by (intros n r Hn; subst En; pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5;
      rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
assert (En7 : ew En (A_OBJ 7) = Z_to_bv 64 (VAL (A_OBJ 7)))
  by (apply img_env_atomP; [exact HEIn | unfold A_OBJ, A_TEXT, A_LIM; lia]).
assert (En8 : ew En (A_OBJ 8) = Z_to_bv 64 (VAL (A_OBJ 8)))
  by (apply img_env_atomP; [exact HEIn | unfold A_OBJ, A_TEXT, A_LIM; lia]).
assert (HSn : st_ok_pi SEGS VAL En ss_rrh
  (restrict (w_H W) (mkst regs3 (Z_to_bv 64 (BASE + A_rr_held)) mem3 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_rrh. apply pa_entry_st_ok_full.
  - subst En. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold rr_hregions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite En7, unsigned_lit_small by lia. rewrite <- RGNSRC.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS En _ (rg_nsrc RG) 0 4 (SOff 32 0) (Z.of_nat (length es)));
      [cbn [sv_denot]; rewrite En32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. exact CV4.
    + rewrite En8, unsigned_lit_small by lia. rewrite <- RGSRC.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS En _ (rg_src RG) 0 8 (SOff 33 0) G0);
      [cbn [sv_denot]; rewrite En33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | cbn; destruct (alx_blocks _ _ _ LAWS ly S2 Hp W mem3 md3 G0 ATABLE HAR3 CGin) as (_ & Hg1 & Hg2 & _);
        change (req_size ATABLE) with 896 in Hg2; pose proof asan_consts as (Cz & _); lia
      | cbn; lia |].
      rewrite Z.add_0_r. exact CV8.
  - apply pairwise_disjoint_of_extents. unfold rr_hregions, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite En7, En8, !unsigned_lit_small by lia. rewrite <- RGNSRC, <- RGSRC.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; first [exact I | revert Dsn; clear; intros; lia].
  - unfold facts_ok; cbn; tauto. }
clear HEn HS.
destruct HJ3 as (HSTKz & HXOz & (memS & HJi & Hagz) & Houtz).
paj_run_sh_x RUNP HSn HJi.
{ intros a (r & Hin & Hr). cbn [ss_mem ss_rrh rr_hregions In] in Hin.
  repeat (destruct Hin as [<- | Hin];
    [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; lia|]). destruct Hin. }
lazymatch goal with HF : frame_of ?Ex ?rs ?m (ms_mem ?x) |- _ =>
  pose proof (frame_of_read_only Ex rs m (ms_mem x) ltac:(vm_compute; reflexivity) HF) as Em1 end.
(* what both cuts need of the locked state *)
assert (SPhi : spZ regs <= 2 ^ 47) by (revert Hshi H47; clear; intros; lia).
assert (SPlo : 0 <= spZ regs - RR_FRAME < 2 ^ 64)
  by (revert SPhi WB; pose proof asan_consts as (Cz & _); revert Cz; unfold RR_FRAME; clear; intros; lia).
assert (HSV1 : forall i, (i < 11)%nat -> val_mem SEGS (arm W mem3) (spZ regs - RR_FRAME + 8 + 8 * Z.of_nat i) 8
  (bv_unsigned (getr regs (nth i RR_SAVED 0%bv)))).
{ intros i Hi. apply (rr_vm_keep W (ms_mem ms1) mem3); [|exact (HSV0 i Hi)].
  intros x Hx. apply Hfr3;
  [ revert Hx Hi SPhi WB; unfold RR_FRAME; pose proof asan_consts as (Cz & _); revert Cz; clear; intros; lia
  | revert Hx HlkR WB; unfold RR_FRAME; pose proof asan_consts as (Cz & _); revert Cz; clear; intros; lia
  | revert Hx; unfold RR_FRAME, ESTACK; clear; intros; lia ]. }
assert (HFL1 : val_mem SEGS (arm W mem3) (F + 56) 8 FL).
{ apply (rr_vm_keep W (ms_mem ms1) mem3); [|exact HFL0].
  intros x Hx. apply Hfr3;
  [ revert Hx HF4096 HFceil; pose proof asan_consts as (Cz & _); revert Cz; clear; intros; lia
  | revert Hx HlkR HFimg; clear; intros; lia
  | revert Hx HFceil WB; pose proof asan_consts as (Cz & _); revert Cz; unfold ESTACK, RR_FRAME; clear; intros; lia ]. }
assert (LKt : alock_at RG W mem3 true).
{ split; [|split; [exact HLK3 | split]].
  - apply (rr_vm_keep W (ms_mem ms1) mem3); [|exact LK0].
    intros x Hx. apply Hfr3; [revert Hx HlkR; clear; intros; lia | revert Hx; clear; intros; lia
    | revert Hx HlkR WB; pose proof asan_consts as (Cz & _); revert Cz; unfold ESTACK, RR_FRAME; clear; intros; lia].
  - apply (rr_vm_keep W (ms_mem ms1) mem3); [|exact LK8].
    intros x Hx. apply Hfr3; [revert Hx HlkR; clear; intros; lia | revert Hx; clear; intros; lia
    | revert Hx HlkR WB; pose proof asan_consts as (Cz & _); revert Cz; unfold ESTACK, RR_FRAME; clear; intros; lia].
  - intros i Hi. unfold arm. apply (RGWR (w_H W) mem3 (rg_lock RG + i)); [left; lia|].
    apply (hidden_not_img SEGS W). rewrite unsigned_lit_small by lia.
    exact (proj1 (RGIMG (rg_lock RG + i) ltac:(unfold rg_rng; left; lia))). }
assert (HNle : 0 <= Z.of_nat (length es) <= 16) by (revert Clen; clear; intros; lia).
assert (HJg : forall mX mdX kX, ajournal_x (SK := SK) SEGS B PST ARx (RR_STK_x + 0) (spZ regs + 0) (rr_fp G0 FD es h cap out)
    ly S Hp W memS md [(0, fpos)] ly S2 Hp W mX mdX kX ->
  ajournal_gx_x (SK := SK) SEGS B PST ARx (G_RR B RG) 0 [] RR_STK_x (spZ regs) (rr_fp G0 FD es h cap out) ly S Hp W mem md
    [(0, fpos)] ly S2 Hp W mX mdX kX).
{ intros mX mdX kX HJx. eapply ajournal_gx_pack_x; [rewrite WS; lia | lia | exact HJx | exact Hagz | intros a Ha Hn; lia]. }
psrr_branch_pi_x RUNP BR HSn.
+ (* g_nsrc <= 0: the table is empty, to the unlock tail 0x83fc4 with RRU None *)
  cbn [sv_denot] in Hc0. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned, En32 in Hc0.
  rewrite (rr_blez _ (Z.of_nat (length es)) eq_refl HNle) in Hc0. apply Z.eqb_eq in Hc0.
  assert (Hnil : es = []) by (destruct es; [reflexivity | cbn [length] in Hc0; lia]).
  paj_run_to_sh_x RUNTOP HSn HJi A_rr_unlock.
  { intros a (r & Hin & Hr). cbn [ss_mem ss_rrh rr_hregions In] in Hin.
    repeat (destruct Hin as [<- | Hin];
      [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; lia|]). destruct Hin. }
  lazymatch goal with HF : frame_of ?Ex ?rs ?m (ms_mem ?x) |- _ =>
    pose proof (frame_of_read_only Ex rs m (ms_mem x) ltac:(vm_compute; reflexivity) HF) as Em2 end.
  lazymatch type of HSn with st_ok_pi _ _ _ _ (restrict _ ?msx) =>
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs3 _ RRP_KEPT HSn HAEn ltac:(vm_compute; reflexivity)) as HKr;
    cbn [ms_regs restrict] in HKr end.
  pmkst HSn. rewrite Em2, Em1 in HJi |- *.
  apply SRr_ret; right; left. unfold RRU, rregs_base, RHELD, RLIVE, rr_frame, rr_saved.
  cbn [rsp0 rN rFP rtr rnth rxregs rxly rxS rxHp rxW rxmem rxmd rxch rxG0 rxFD rxes rxj rxh rxc rxO rxmx rxcap rxout rxrest rxkr].
  eexists _, ly, S2, Hp, mem3, _, _, F, FL.
  split; [reflexivity|].
  split.
  { split; [unfold spZ; rewrite (HKr 2%bv ltac:(cbv; tauto)), M2;
            unfold w64; apply unsigned_lit_small; unfold RR_FRAME in SPlo |- *; exact SPlo|].
    split; [rewrite (HKr 3%bv ltac:(cbv; tauto)); exact M3|].
    split; [rewrite (HKr 4%bv ltac:(cbv; tauto)); exact M4|].
    split; [rewrite (HKr 8%bv ltac:(cbv; tauto)); exact M8|].
    split; [rewrite (HKr 9%bv ltac:(cbv; tauto)); exact M9|].
    split; [rewrite (HKr 18%bv ltac:(cbv; tauto)); exact M18|].
    split; [rewrite (HKr 20%bv ltac:(cbv; tauto)); exact M20|].
    split; [rewrite (HKr 21%bv ltac:(cbv; tauto)); exact M21|].
    split; [rewrite (HKr 22%bv ltac:(cbv; tauto)); exact M22|].
    split; [rewrite (HKr 26%bv ltac:(cbv; tauto)); exact M26|].
    rewrite (HKr 27%bv ltac:(cbv; tauto)); exact M27. }
  split; [exact Hpos|].
  split.
  { split.
    { exists fpos. split; [exact (HJg _ _ _ HJi)|].
      split; [eapply (ajournal_gx_rom_view_x SEGS B PST ARx);
        first [exact LAWS | exact Hsegs | exact (HJg _ _ _ HJi) | exact HROMO | exact PSTR | exact HROM]|].
      split; [intros a Hi _ _ Ha; exact (PRES a Hi Ha)|].
      split; [split; [reflexivity | split; [reflexivity | split; [exact HFL1 | exact HSV1]]]|].
      split; [exact LKt | exact CWAKE]. }
    split; [exact CREL|]. split; [exact COUT|].
    split; [rewrite Eab; exact HPERM|].
    split; [exact CGS|]. split; [exact CSRC|].
    split; [exact HMOs|]. split; [rewrite Hbb2; exact HLIVE|].
    (* the room round: RBASE's budget at S2 (HRM2, RPF_of at the seat) and its count fact (the blocks are the
       entry's) *)
    split; [exact HRM2 | rewrite Eab; exact HCNTP]. }
  rewrite Hnil. intros e He. destruct He.
+ (* g_nsrc > 0: the scan's setup 0x83ef4-0x83f10, to the loop head 0x83f14 with RRL 0 *)
  cbn [sv_denot] in Hc0. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned, En32 in Hc0.
  rewrite (rr_blez _ (Z.of_nat (length es)) eq_refl HNle) in Hc0. apply Z.eqb_neq in Hc0.
  assert (Hne : (0 < length es)%nat) by lia.
  paj_run_to_sh_x RUNTOP HSn HJi A_rr_scan.
  { intros a (r & Hin & Hr). cbn [ss_mem ss_rrh rr_hregions In] in Hin.
    repeat (destruct Hin as [<- | Hin];
      [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; lia|]). destruct Hin. }
  lazymatch goal with HF : frame_of ?Ex ?rs ?m (ms_mem ?x) |- _ =>
    pose proof (frame_of_read_only Ex rs m (ms_mem x) ltac:(vm_compute; reflexivity) HF) as Em2 end.
  (* the loop's registers: a1 = G0, a2 = 56 |es|, a3 = SHADOW_OFF + G0 / 8, s7, s8 = 0, s9 *)
  destruct (alx_blocks _ _ _ LAWS ly S2 Hp W mem3 md3 G0 ATABLE HAR3 CGin) as (_ & HG4096 & HGceil & _).
  change (req_size ATABLE) with 896 in HGceil.
  assert (HG64 : 0 <= G0 < 2 ^ 64) by (pose proof asan_consts as (Cz & _); lia).
  prreg HSn (11%bv : bv 5) N11. prreg HSn (12%bv : bv 5) N12. prreg HSn (13%bv : bv 5) N13.
  prreg HSn (23%bv : bv 5) N23. prreg HSn (24%bv : bv 5) N24. prreg HSn (25%bv : bv 5) N25.
  lazymatch type of HSn with st_ok_pi _ _ _ _ (restrict _ ?msx) =>
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs3 _ RRP_KEPT HSn HAEn ltac:(vm_compute; reflexivity)) as HKr;
    cbn [ms_regs restrict] in HKr end.
  rewrite En32, (rr_a2 _ (Z.of_nat (length es)) eq_refl HNle) in N12.
  rewrite En33, (rr_srl8 G0 HG64) in N13.
  rewrite (EEn 22%nat 22%bv eq_refl), M22 in N13.
  rewrite YI08.alu64_add_lit in N13.
  change 339%nat with (A_HI 59) in N23. change 340%nat with (A_HI 60) in N25.
  rewrite (img_env_atomP En (A_HI 59) HEIn ltac:(unfold A_HI, A_TEXT, A_LIM; lia)), HH59 in N23.
  rewrite (img_env_atomP En (A_HI 60) HEIn ltac:(unfold A_HI, A_TEXT, A_LIM; lia)), HH60 in N25.
  pmkst HSn. rewrite Em2, Em1 in HJi |- *.
  apply SRr_ret; left. unfold RRL, rregs_held, rregs_base, RHELD, RLIVE, rr_frame, rr_saved.
  cbn [rsp0 rN rFP rtr rnth rxregs rxly rxS rxHp rxW rxmem rxmd rxch rxG0 rxFD rxes rxj rxh rxc rxO rxmx rxcap rxout rxrest rxkr].
  eexists _, ly, S2, Hp, mem3, _, _, F, FL.
  split; [reflexivity|].
  split.
  { split.
    { split; [unfold spZ; rewrite (HKr 2%bv ltac:(cbv; tauto)), M2;
              unfold w64; apply unsigned_lit_small; unfold RR_FRAME in SPlo |- *; exact SPlo|].
      split; [rewrite (HKr 3%bv ltac:(cbv; tauto)); exact M3|].
      split; [rewrite (HKr 4%bv ltac:(cbv; tauto)); exact M4|].
      split; [rewrite (HKr 8%bv ltac:(cbv; tauto)); exact M8|].
      split; [rewrite (HKr 9%bv ltac:(cbv; tauto)); exact M9|].
      split; [rewrite (HKr 18%bv ltac:(cbv; tauto)); exact M18|].
      split; [rewrite (HKr 20%bv ltac:(cbv; tauto)); exact M20|].
      split; [rewrite (HKr 21%bv ltac:(cbv; tauto)); exact M21|].
      split; [rewrite (HKr 22%bv ltac:(cbv; tauto)); exact M22|].
      split; [rewrite (HKr 26%bv ltac:(cbv; tauto)); exact M26|].
      rewrite (HKr 27%bv ltac:(cbv; tauto)); exact M27. }
    split; [rewrite (HKr 19%bv ltac:(cbv; tauto)); exact M19|].
    exact N23. }
  split; [exact N25|].
  split; [rewrite N11; exact En33|].
  split; [exact N12|].
  split; [rewrite N13; unfold w64; f_equal; cbn [Z.of_nat]; lia|].
  split; [rewrite N24; reflexivity|].
  split; [exact Hpos|]. split; [exact Hne|].
  split; [intros i Hi; lia|].
  split.
  { exists fpos. split; [exact (HJg _ _ _ HJi)|].
    split; [eapply (ajournal_gx_rom_view_x SEGS B PST ARx);
      first [exact LAWS | exact Hsegs | exact (HJg _ _ _ HJi) | exact HROMO | exact PSTR | exact HROM]|].
    split; [intros a Hi _ _ Ha; exact (PRES a Hi Ha)|].
    split; [split; [reflexivity | split; [reflexivity | split; [exact HFL1 | exact HSV1]]]|].
    split; [exact LKt | exact CWAKE]. }
  split; [exact CREL|]. split; [exact COUT|].
  split; [rewrite Eab; exact HPERM|].
  split; [exact CGS|]. split; [exact CSRC|].
  split; [exact HMOs|]. split; [rewrite Hbb2; exact HLIVE|].
  split; [exact HRM2 | rewrite Eab; exact HCNTP].
Qed.
End wR.
End c.
End b.
End a.
