(* CARRIED from commit 886368392e934bec75bf4485ad77505063da7c16,
   proofs/cgif/cgif_file_fuzzer/lib/YGcfInstReallocK.v, sha256 d05d719650b68a7033c82c204ffe2e8c4d11aad9c3ac5650c323d2f131457e86 (donor version not released; internal record).
   DO NOT EDIT in this tree: change it on that branch and carry it again. The changes made here are in the Require lines only:
   the module prefix OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib -> OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable
   (lib.Spec -> fuzz_reply.lib.Spec).
   Modules that are per image in this tree name lib/B; a sentence is split at a directory change, the module order kept.
*)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-30: taken back by path from commit 2d97a7029501,
   proofs/omx-clap-core/fuzz_preset/lib/Reusable/YGcfInstReallocK.v (the P'' text), with this unit's module prefixes and
   two changes for this layer: (1) the FIT CHECK against YGcfInstAllocTop is kept, in its own file YGcfInstReallocKFit.v
   (so this file needs no YGcfInstAllocTop, and a unit that carries this file without lane M's top can still build it);
   (2) the two start-state lemmas of Section SAT take YGcfInstBase.ARXq_cf_nil_init's cells premise (exh_cell_cf /
   errb_cells_cf at init_state) and its lazy-in-maps premise (the lazy ranges are mapped at init), which this layer's
   call-site relation carries.  The preset text itself was taken from
   this layer's commit bbe791f0bb0 with these changes:
   - U := admits: the trace premise of arealloc_realizes_cf_k / arealloc_null_realizes_cf_k is
     admits (as_universe B) tr S (YG01.v:156), the form YGcfRealloc.v / YGcfReallocCompose.rentry_cf take on this base
     (a Theorem Labs lane 2026-10-29 22:05Z), in place of the source's In tr (as_universe B);
   - acall_prefix is not a named premise at the instance: YGcfInstRealloc.acall_prefix_cf_ok (acall_pre_cf's
     ACALL_PREFIX conjunct, YG0dcf.v:52);
   - the source's FIT CHECK against YGcfInstAllocTop is not in the preset text (lib/A there); it is kept in
     YGcfInstReallocKFit.v.
   Modified by Theorem Labs, 2026-10-30 (route R, R-1; lane F1): realloc(p, n) is PRIMED in place, under the same names.
   realloc(p, n) frees the old block inside the call, a re-hide crossing, so arealloc_realizes_cf_k now reads at
   amreal' segs RZ_cf with the leaf YG0dcfR.realloc_leaf_cf_rh (YGcfReallocComposeRh.arealloc_realizes_cf_rp_h_rh's
   body), and arealloc_realizes_cf_k_of_parts / _inst take the primed composition
   (YGcfReallocComposeRh.arealloc_realizes_cf_rp_rh_of_parts), the primed Deallocate contract
   (YGcfMallocComposeERh.adealloc_realizes_raw_cf_em_m_rh) and the primed walk record (wrap_realloc_walk_cf_rh).  The
   caller's hull admission is the ENTRY headroom cf_hull_adm S n (CfParams) in place of the path form; the end-state
   admission is derived from it once, in arealloc_realizes_cf_k_of_parts.  The unprimed end rule with the caller's room
   at RK_realloc (the old _r2 form) and its _of_parts are deleted (no consumer outside this file in any unit).
   realloc(NULL, n) frees no live block: its
   rule stays unprimed.

   The realloc end rule YGcfRealloc.arealloc_realizes_cf from YGcfReallocCompose's bridge takes the batch class's room
   after the inner malloc from the relation (ARX_br), which is not satisfiable at the layer's relations (ROOM_cf is the
   CALLER's, YGcfInstBase.v). This file states the end rule with the caller's room at the entry instead:
   - arealloc_realizes_cf_k (k): realloc(p, n) with ROOM_cf_k S (RK_realloc + k) at the entry (YGcfRoomKeep.v: two
     units, the inner malloc and the free of the old block) and ROOM_cf_k (snd r) k in the post, so a caller threads
     room from call to call; the composition's room after the inner malloc is room_mid_cf (realloc_room_rp_k);
   - arealloc_null_realizes_cf_k (k): realloc(NULL, n) with ROOM_cf_k S (RK_malloc + k) at the entry and ROOM_cf_k
     (snd r) k in the post.
   The post's room is YGcfRoomStep.realloc_room_keep_cf over the granted path (YG0dHc.amreal'_apath_gflag; for the
   null rule RGtop.rg_apath_gflag). realloc(NULL, n) needs no new bridge: YGcfInstRealloc's
   arealloc_null_realizes_cf_inst (which does not use ARX_br) and the room of the null tree (rk_realloc_null_cf).
   No image constant; no function is proved here (rule 24). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YK0j YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YGcfTok YG06bcf YG07cf YGcfRoomPre YG03cf YG03dcf YGcfApath YG0lawscf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require AllocG DeallocG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require ReallocG ReallocP.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require RGtop YGcfRmodel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ErrnoGcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YGcfRealloc YG0s YGcfXs.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YGcfMallocCompose YGcfMallocComposeE.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfAmx YGcfRoomKeep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YGcfRoomStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YGcfReallocCompose.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YGcfSecsStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase YGcfImgRows.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YGcfInstBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH YG0dH YG0dHc.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YGcfRehidePost YG0dcfR YGcfMallocComposeERh.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YGcfInstRealloc YGcfReallocComposeRh.
(* stdpp, through the LPS modules, shadows several list names; In and remove here are Stdlib's, as in YGcfRealloc.v. *)
From Stdlib Require Import List.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section G. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.

(* ---------------------------------------------------------------------------- *)
(* 1. The model's room across realloc's first two steps and across the null tree. *)

(* The entry's room for two units, the frame free_cf PNull, then one malloc_cf: the batch class still has room. *)
Lemma room_mid_cf : forall S S1 S2 (q : sptr) n tr trc1 trc2, YGcfRoomStep.room_shape_cf S -> ROOM_cf_k S RK_realloc ->
apath (free_cf PNull tr S) trc1 (tt, S1) -> apath (malloc_cf n tr S1) trc2 (q, S2) -> batch_room_cf S2.
Proof.
intros S S1 S2 q n tr trc1 trc2 IV R Hp1 Hp2.
pose proof (YGcfRoomStep.ipost_apath _ _ _ _ (YGcfRoomStep.rk_free_null tr S) Hp1) as N1. cbn [snd] in N1.
pose proof (YGcfRoomStep.rk_nt_inv _ _ N1 IV) as I1.
destruct (YGcfRoomStep.rk_nt_meas _ _ N1) as (R1 & E1 & A1).
assert (R1' : ROOM_cf_k S1 RK_realloc) by (unfold ROOM_cf_k, ERRB_ROOM_k in *; rewrite R1, E1, A1; exact R).
pose proof (YGcfRoomStep.malloc_room_keep_cf 1 n tr S1 trc2 q S2 I1 R1' Hp2) as R2.
exact (proj2 (proj2 (RK_room S2 1 R2))).
Qed.

(* The null tree, free_cf PNull then malloc_cf, moves the three room measures by at most one malloc's. *)
Lemma rk_realloc_null_cf : forall n tr s, YGcfRoomStep.room_shape_cf s ->
ipost (ReallocP.realloc_null_tree_with malloc_cf free_cf n tr s) (fun r =>
Z.of_nat (length (st_sec_arr (snd r))) <= Z.of_nat (length (st_sec_arr s)) + 1 /\
errb_size_cf (snd r) <= errb_size_cf s + 100 /\
rg_mapped_user (reg (snd r) kBatchClass) <= rg_mapped_user (reg s kBatchClass) + kUserMapSize).
Proof.
intros n tr s IV. unfold ReallocP.realloc_null_tree_with. apply YGcfRoomStep.rk_bind.
eapply ipost_mono; [|apply YGcfRoomStep.rk_free_null]. intros [u s1] N1. cbn [fst snd] in *.
pose proof (YGcfRoomStep.rk_nt_inv _ _ N1 IV) as I1. destruct (YGcfRoomStep.rk_nt_meas _ _ N1) as (R1 & E1 & A1).
eapply ipost_mono; [|exact (YGcfRoomStep.rk_malloc n tr s1 I1)]. intros [q s2] (I2 & L2 & E2 & M2). cbn [fst snd] in *.
rewrite A1 in L2. rewrite E1 in E2. rewrite R1 in M2.
assert (Hb : (if from_primary n then 0 else 1) <= 1) by (destruct (from_primary n); lia).
split; [lia|]. split; [exact E2 | exact M2].
Qed.

Section J.
Variable segs : list Segment.
Variable B : asyms.

(* ---------------------------------------------------------------------------- *)
(* 2. The end rules with the caller's room at the entry.                          *)

(* realloc(p, n) with headroom k, PRIMED (route R, R-1: realloc frees the old block, a re-hide crossing):
   YGcfReallocComposeRh.arealloc_realizes_cf_rp_h_rh's body at RP := ROOM_cf_k S (RK_realloc + k), with the room in
   the post, over amreal' segs RZ_cf and YG0dcfR.realloc_leaf_cf_rh.  The caller's hull admission is the ENTRY
   headroom cf_hull_adm S n (CfParams, the call's charge), a plain premise after the trace premise; the admission at
   every end state is derived from it once, in arealloc_realizes_cf_k_of_parts. *)
Definition arealloc_realizes_cf_k (Hp : list Z) (pc : Z) (k : nat) : Prop :=
forall ly S W regs mem md p n_old n ch,
acall_pre_cf segs B ly S Hp W regs mem md ch -> ROOM_cf_k S (RK_realloc + k) ->
In (p, n_old) (blocks S) -> getr regs 10 = w64 (sptr_addr B ly p) ->
~ In (sptr_addr B ly p) Hp ->
getr regs 11 = w64 n ->
1 <= n < cf_malloc_max -> blocks_bytes S + n <= LIVE_MAX ->
admits (as_universe B) (call_trace ly cf_pc_realloc_ra0 regs ch) S ->
cf_hull_adm S n ->
amreal' segs RZ_cf (ReallocP.realloc_tree_with malloc_cf free_cf p n (call_trace ly cf_pc_realloc_ra0 regs ch) S) W
(cfg_at segs pc regs mem md)
(fun r W' c' => (realloc_leaf_cf_rh segs B ly S Hp W regs mem md p n_old n r W' c' /\
 (fst r = PNull -> ReallocP.mt_refused malloc_cf free_cf n (call_trace ly cf_pc_realloc_ra0 regs ch) S (snd r))) /\
 ROOM_cf_k (snd r) k).

(* YGcfRealloc.arealloc_null_realizes_cf (YGcfRealloc.v:106, arealloc_null_realizesP at the instance) written out, with
   ROOM_cf_k S (RK_malloc + k) at the entry and ROOM_cf_k (snd r) k after. *)
Definition arealloc_null_realizes_cf_k (Hp : list Z) (pc : Z) (k : nat) : Prop :=
forall ly S W regs mem md n ch,
acall_pre_cf segs B ly S Hp W regs mem md ch -> ROOM_cf_k S (RK_malloc + k) ->
getr regs 10 = w64 0 -> getr regs 11 = w64 n ->
1 <= n < cf_malloc_max -> blocks_bytes S + n <= LIVE_MAX ->
admits (as_universe B) (call_trace ly cf_pc_realloc_ra0 regs ch) S ->
amreal segs (ReallocP.realloc_null_tree_with malloc_cf free_cf n (call_trace ly cf_pc_realloc_ra0 regs ch) S) W
(cfg_at segs pc regs mem md)
(fun r W' c' => (malloc_leaf_cf segs B ly S Hp W regs mem md n r W' c' /\
 (fst r = PNull -> ReallocP.mt_refused malloc_cf free_cf n (call_trace ly cf_pc_realloc_ra0 regs ch) S (snd r))) /\
 ROOM_cf_k (snd r) k).

(* realloc(NULL, n) with room: the end rule YGcfRealloc.arealloc_null_realizes_cf and the null tree's room. *)
Theorem arealloc_null_realizes_cf_k_of : forall Hp pc,
YGcfRealloc.arealloc_null_realizes_cf segs B Hp pc -> forall k, arealloc_null_realizes_cf_k Hp pc k.
Proof.
intros Hp pc HN k ly S W regs mem md n ch PRE RMk H10 H11 Hn Hlive Htr.
pose proof (HN ly S W regs mem md n ch PRE I H10 H11 Hn Hlive Htr) as A. cbv beta in A.
pose proof (RGtop.rg_apath_gflag segs _ _ _ _ A) as A2.
eapply amreal_mono; [|exact A2].
intros r W' c' [[L R] (trc & Hpt & _)]. split; [exact (conj L R)|].
pose proof (YGcfRoomStep.ipost_apath _ _ _ _ (rk_realloc_null_cf n _ S
  (YGcfRoomStep.room_shape_of_acall_pre_cf segs B ly S Hp W regs mem md ch PRE)) Hpt) as (L1 & E1 & M1).
unfold ROOM_cf_k, ERRB_ROOM_k, RK_malloc in *. unfold kUserMapSize, kFreeArrayOffset, kPage in *. lia.
Qed.

(* The mid-walk room the primed composition asks (YGcfReallocComposeRh.realloc_room_rp), at the caller's room
   ROOM_cf_k S RK_realloc: room_mid_cf over the entry's room shape. *)
Lemma realloc_room_rp_k : forall ARX,
YGcfReallocComposeRh.realloc_room_rp segs B (fun S => ROOM_cf_k S RK_realloc) ARX.
Proof.
intros ARX ly S Hp W regs mem md ch tr trc1 S1 n trc2 q S2 inst ly2 W2 mem2 md2 PRE R Hp1 Hp2 _.
exact (room_mid_cf S S1 S2 q n tr trc1 trc2
  (YGcfRoomStep.room_shape_of_acall_pre_cf segs B ly S Hp W regs mem md ch PRE) R Hp1 Hp2).
Qed.

Section R.
(* YGcfReallocCompose's Section R variables, in its order (YGcfReallocCompose.v:186). *)
Variables (nmax al atp acf atpD : Z).

(* realloc(p, n) with headroom k, primed: YGcfReallocComposeRh.arealloc_realizes_cf_rp_rh_of_parts (the primed
   composition) at RP := fun S => ROOM_cf_k S RK_realloc, the post's room by YGcfRoomStep.realloc_room_keep_cf over a
   granted path (YG0dHc.amreal'_apath_gflag), and the end-state hull admission from the entry's (the derivation's one
   place): one realloc moves the section counts by at most its call's charge (YGcfSecsStep.secs_realloc_step), so
   CfParams's law cf_hull_adm_post gives cf_hull_ok on every path. *)
Theorem arealloc_realizes_cf_k_of_parts : forall (ARX : ARXh_t segs) (K1 : YGcfReallocCompose.K1r_t segs)
(K2 K3 : YGcfReallocCompose.K2r_t segs),
YGcfReallocCompose.acall_prefix_cf segs B -> YGcfReallocCompose.acall_xs_cf segs B -> YGcfReallocCompose.errno_word_cf B ->
relro_seg_t segs -> errno_relro_t B ->
nmax_cf_ok nmax -> ARX_ARcf segs B ARX -> ARX_xs segs ARX -> YGcfReallocCompose.ARX_qmh segs ARX ->
aalloc_realizes_cf_em_m segs B nmax al atp acf ARX ->
adealloc_realizes_raw_cf_em_m_rh segs B atpD ARX ->
YGcfReallocComposeRh.wrap_realloc_walk_cf_rh segs B nmax al atp acf atpD ARX K1 K2 K3 ->
forall Hp k, arealloc_realizes_cf_k Hp cf_pc_wrap_realloc k.
Proof.
intros ARX K1 K2 K3 HPFX HXSP HEW HRS HER HNM HAR HXS HQM HAM HDM HW Hp k.
intros ly S W regs mem md p n_old n ch PRE RMk Hin H10 NIN H11 Hn Hlive Htr HADM.
assert (HADMp : forall trc r S', apath (ReallocP.realloc_tree_with malloc_cf free_cf p n
    (call_trace ly cf_pc_realloc_ra0 regs ch) S) trc (r, S') -> cf_hull_ok S')
  by (intros trc r S' Hpt; exact (cf_hull_adm_post S n r S' HADM (YGcfSecsStep.secs_realloc_step p n _ S trc (r, S') Hpt))).
pose proof (YGcfReallocComposeRh.arealloc_realizes_cf_rp_rh_of_parts segs B nmax al atp acf atpD
  (fun S => ROOM_cf_k S RK_realloc) ARX K1 K2 K3
  HPFX HXSP HEW HRS HER HNM HAR HXS HQM (realloc_room_rp_k ARX) HAM HDM HW Hp
  ly S W regs mem md p n_old n ch PRE (RK_mono S (RK_realloc + k) RK_realloc (Nat.le_add_r _ _) RMk)
  Hin H10 NIN H11 Hn Hlive Htr HADMp) as A.
pose proof (amreal'_apath_gflag segs RZ_cf _ _ _ _ A) as A2.
eapply amreal'_mono; [|exact A2].
intros r W' c' [[L R] (trc & Hpt & _)]. split; [exact (conj L R)|].
destruct r as [q s'].
exact (YGcfRoomStep.realloc_room_keep_cf k p n _ S trc q s'
  (YGcfRoomStep.room_shape_of_acall_pre_cf segs B ly S Hp W regs mem md ch PRE) RMk Hpt).
Qed.
End R.
End J.
End G.

(* ---------------------------------------------------------------------------- *)
(* 3. At the layer's call-site relation (YGcfInstBase.ARXq_cf), as YGcfInstRealloc.v, without room_br.            *)
Section INST. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {IM : AImg}.
Variable B : asyms.
Variable IOK : Z -> Prop.
Variable acf : Z.
Local Abbreviation segs := im_segs.
Local Abbreviation ARX := (ARXq_cf B IOK).
(* The named premises of the source's YGcfInstRealloc.v except room_br, which the entry's room replaces, and
   acall_prefix, which is YGcfInstRealloc.acall_prefix_cf_ok on this base.  realloc(p, n) takes the PRIMED Deallocate
   contract (YGcfMallocComposeERh.adealloc_realizes_raw_cf_em_m_rh); realloc(NULL, n) frees no live block and takes
   none. *)
Hypothesis aalloc_realizes_cf_em_m_cf : aalloc_realizes_cf_em_m segs B cf_malloc_max al_cf atp_cf acf ARX.
Hypothesis adealloc_realizes_raw_cf_em_m_rh_cf : adealloc_realizes_raw_cf_em_m_rh segs B atp_cf ARX.
Hypothesis errno_word : YGcfReallocCompose.errno_word_cf B.
(* field round 3's two unit image rows (YG0ncf.v), which the realloc composition reads at Allocate's and
   Deallocate's entries (part 3b: Allocate's too) *)
Hypothesis relro_seg : relro_seg_t segs.
Hypothesis errno_relro : errno_relro_t B.

Theorem arealloc_realizes_cf_k_inst :
forall (K1 : YGcfReallocCompose.K1r_t segs) (K2 K3 : YGcfReallocCompose.K2r_t segs),
YGcfReallocComposeRh.wrap_realloc_walk_cf_rh segs B cf_malloc_max al_cf atp_cf acf atp_cf ARX K1 K2 K3 ->
forall Hp k, arealloc_realizes_cf_k segs B Hp cf_pc_wrap_realloc k.
Proof.
intros K1 K2 K3 HW.
exact (arealloc_realizes_cf_k_of_parts segs B cf_malloc_max al_cf atp_cf acf atp_cf ARX K1 K2 K3
  (YGcfInstRealloc.acall_prefix_cf_ok segs B) (YGcfInstRealloc.acall_xs_cf_ok B) errno_word relro_seg errno_relro
  nmax_cf_ok_of_w (ARXq_cf_ARcf B IOK) (ARXq_cf_xs B IOK)
  (YGcfInstRealloc.ARX_qm_cfq B IOK) aalloc_realizes_cf_em_m_cf adealloc_realizes_raw_cf_em_m_rh_cf HW).
Qed.

Theorem arealloc_null_realizes_cf_k_inst : forall (Kn : YGcfReallocCompose.Knr_t segs),
YGcfReallocCompose.wrap_realloc_null_walk_cf segs B cf_malloc_max al_cf atp_cf acf ARX Kn ->
forall Hp k, arealloc_null_realizes_cf_k segs B Hp cf_pc_wrap_realloc k.
Proof.
intros Kn HW Hp k.
exact (arealloc_null_realizes_cf_k_of segs B Hp cf_pc_wrap_realloc
  (YGcfInstRealloc.arealloc_null_realizes_cf_inst B IOK acf aalloc_realizes_cf_em_m_cf relro_seg errno_relro Kn HW Hp) k).
Qed.
End INST.

(* ---------------------------------------------------------------------------- *)
(* 4. Satisfiability at the start state (VERIFY 2026-10-29 21:38Z): the entry's new premise, ROOM_cf_k at
   RK_realloc + k (realloc(p, n)) or RK_malloc + k (realloc(NULL, n)), holds at init_state whenever that level is at
   most K_INIT (YGcfRoomKeep.ROOM_cf_init_k), together with the call-site relation (YGcfInstBase.ARXq_cf_nil_init). *)
Section SAT. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {IM : AImg}.
Variable B : asyms.
Variable IOK : Z -> Prop.

Lemma realloc_k_entry_init : forall k inst ly (W : world im_segs) mem md,
  (RK_realloc + k <= K_INIT)%nat -> IOK inst -> AR im_segs B ly init_state W mem md -> AI im_segs (w_H W) (w_A W) md ->
  start_cells_cf im_segs B ly init_state W mem -> start_pf_cf im_segs B ly W mem ->
  (forall x, YK0g.covered (vm_noaccess (m_vmmaps md) ++ m_vm_lazy md) x = true ->
     YK0g.covered (vm_maps (m_vmmaps md)) x = true) ->
  EXH_OFF_t /\ errb_obj_owned_t B /\ errb_ial_apart_t B -> pf_cells_owned_t B ->
  ROOM_cf_k init_state (RK_realloc + k) /\
  exists W', wle W W' /\ AI im_segs (w_H W') (w_A W') md /\ ARXq_cf B IOK [] inst ly init_state W' mem md.
Proof.
intros k inst ly W mem md Hk I A HAI HC HPF HLZ HO HPO.
exact (conj (ROOM_cf_init_k _ Hk) (ARXq_cf_nil_init B IOK inst ly W mem md I A HAI HC HPF HLZ HO HPO)).
Qed.

Lemma realloc_null_k_entry_init : forall k inst ly (W : world im_segs) mem md,
  (RK_malloc + k <= K_INIT)%nat -> IOK inst -> AR im_segs B ly init_state W mem md -> AI im_segs (w_H W) (w_A W) md ->
  start_cells_cf im_segs B ly init_state W mem -> start_pf_cf im_segs B ly W mem ->
  (forall x, YK0g.covered (vm_noaccess (m_vmmaps md) ++ m_vm_lazy md) x = true ->
     YK0g.covered (vm_maps (m_vmmaps md)) x = true) ->
  EXH_OFF_t /\ errb_obj_owned_t B /\ errb_ial_apart_t B -> pf_cells_owned_t B ->
  ROOM_cf_k init_state (RK_malloc + k) /\
  exists W', wle W W' /\ AI im_segs (w_H W') (w_A W') md /\ ARXq_cf B IOK [] inst ly init_state W' mem md.
Proof.
intros k inst ly W mem md Hk I A HAI HC HPF HLZ HO HPO.
exact (conj (ROOM_cf_init_k _ Hk) (ARXq_cf_nil_init B IOK inst ly W mem md I A HAI HC HPF HLZ HO HPO)).
Qed.
End SAT.

Print Assumptions arealloc_realizes_cf_k_of_parts.
Print Assumptions arealloc_null_realizes_cf_k_of.
Print Assumptions arealloc_realizes_cf_k_inst.
Print Assumptions arealloc_null_realizes_cf_k_inst.
Print Assumptions realloc_k_entry_init.
Print Assumptions realloc_null_k_entry_init.
