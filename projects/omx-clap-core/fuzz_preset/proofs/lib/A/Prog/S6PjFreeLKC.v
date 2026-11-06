(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/pj_free_seg_lk.v, with its module paths, module names and numbers changed; 358 of its 671 lines of code are new or changed and 336 lines of the source are left out. *)
(* fuzz_preset image A, slice S6 (WalkS6): pj_free's walk (lib/A/Prog/S6PjFree.v), the KEY and BOUND-TEST segments.
   rule 24: proves no function (kind: segment lemma of pj_free's walk).
   - pf_seg_LK (pfs_LK d'): from the cut pf_LK (slot 39, AF_pf + 156, the recursive call's return site) the ASan check
     of v+32 (decided by v's shadow entry), keys := v->keys, `beqz keys`: keys = NULL (ks = false, Dk = []) goes to
     the cut pf_LC (AF_pf + 200) with nothing freed; keys <> NULL (ks = true) computes keys + 8 i, its ASan check
     (decided: the slot lies in the keys block, a harness block live in the current ledger), loads the key x and
     calls fuzz_free (returning at AF_pf + 200), crossed by aj_call_xWR with the callee text tfuzz_free_specO PB FX
     (x = NULL: pfk_acct_null; else the head (x, k) of Dk: pfk_acct_free), the memory invariant kept by PCALL from
     the callee's memnorm keep; then the continuation at pf_LC.
   - pf_seg_LC (pfs_LC d'): from the cut pf_LC (slot 50, AF_pf + 200) the ASan check of v+40, n := v->n, i += 1,
     8 i += 8, 56 i += 56, `bltu s8, a0`: taken (i + 1 < n) to pf_LH (i + 1) at AF_pf + 136, not taken (i + 1 = n)
     to pf_LX at AF_pf + 228 (no slot left: Dr = Fr = []).
   The structure is image B's lib/B/Prog/pj_free_seg_lk.v / pj_free_seg_lc.v (h-rw-man-5) over A's listing, registers
   (s0 = v, s1 = v+32, s2 = v+40, s4 = the shadow offset, s5 = cell(v+40), s6 / s7 / s8 = 56 i / 8 i / i, s9 / s10 =
   cell(v+24) / cell(v+32)) and frame; A has no UBSan checks.
   Section hypotheses: AR_laws_x at cf_head (LAWS); YGcfFsVis.ARx_frame_hull_vis (VISF, a MARKED kit fact the instance
   discharges by ARx_frame_hull_vis_cf_ok); the image facts PAB (the image start), pal_pst_ro (alloc.c's statics are
   no read-only bytes) and pal_ret_free (pj_free's fuzz_free return sites), discharged at PI_prog_A; the memory
   invariant's laws PLAW / PCALL; the callee text FREE (tfuzz_free_specO PB FX, PjFreeCommon).
   THE RE-HIDING MOVE: fuzz_free can hide shadow again, so both segments conclude SRr' SEGS RZ_cf (YA0nH) and run over
   R := wle' SEGS RZ_cf: the _invR runners (YC1fPx), paj_branchR (YSRrG), the call by YCbqGcallW.aj_call_xWR, the
   frame's journal at wle' (pf_frameR), and the after-call facts by S6PjFreeKeep's / S6PjFreeGlue's R forms.
   Re-fitted to the #102 kit (pfs_LK / pfs_LC take no DW binder, S6PjFree.v:401-415): the ledger's most / own (fe_most /
   fe_own) threaded through the ledger lemmas and the call of FREE; fpre's last conjunct frm_zero (FRM0-ENTRY)
   passes from pj_free's fpre to fuzz_free's (same float state fx); pf_pre's pf_safe is used at fe_v en <> 0.
   Numerals: 156 / 200 / 136 / 228 (DERIVED: S6PjFree.v PF_LK / PF_LC / PF_LH / PF_LX), 96 (LENGTH: pj_free's frame),
   56 / 8 / 32 / 40 / 24 (LENGTH: struct pj and its fields, a key pointer), 2 ^ 42 / 2 ^ 45 / 2 ^ 46 / 2 ^ 47 / 4096
   (DERIVED bounds of the seat's atoms); atoms 32 .. 34 (the first atoms after the registers). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG YCbqGcall YGcallMx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames YCbqGcallW YC80xf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YSRrMemnorm YC80xf_inv YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoomLive.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetLiveBounds PresetRoomPos.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Listing_prog PAImg_prog PRH_Base PRH_Img.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Reader PRH_FnReader PRH_FnAlloc PRH_FnPj.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1Ledger PRW_StepKit S6PjCommon.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PjStringCommon.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfFsVis.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfHeadSh.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_PjOrder.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PjFreeCommon PjFreePure S6PjFree.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S6PjFreeKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S6PjFreeGlue.
From Stdlib Require Import FunctionalExtensionality.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YSRrG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ======== the key segment's seat at AF_pf + 156 (pf_LK) ======== *)
(* s1 = v + 32 (atom 8 at 32), s10 = the ASan cell of v + 32; every other register its own atom (s0 = v, s4 = the shadow
   offset, s7 = 8 i); v's keys word at v + 32: atom 32 (an object, ks = true) or the literal 0 (an array); for an object
   also keys + 8 i (atom 33, an alias of keys + s7) and the key keys[i] there (atom 34) *)
Definition pfk_sregs : list sv :=
  Eval vm_compute in sr_set (sr_set sr_atoms 9%bv (SOff 8 32)) 26%bv (pft_cell (SOff 8 32)).
Lemma pfk_sregs_eq : pfk_sregs = sr_set (sr_set sr_atoms 9%bv (SOff 8 32)) 26%bv (pft_cell (SOff 8 32)).
Proof. vm_compute. reflexivity. Qed.
Definition pfk_vhdr (ks : bool) : YP09.region :=
  YP09.mkRegion (Some 8%nat) 0 56 0 0 [YP09.mkChunk 32 (CVal 8 (if ks then SOff 32 0 else SLit 0))].
Definition pfk_kslot : YP09.region := YP09.mkRegion (Some 33%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 34 0))].
Definition pfk_mem (ks : bool) : smem := if ks then [pfk_vhdr true; pfk_kslot] else [pfk_vhdr false].
Definition pfk_atoms : list (nat * afact) :=
  [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (8%nat, mkAF 4096 (2 ^ 47 - 64) 3);
   (20%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (23%nat, mkAF 0 (2 ^ 45) 3)].
Definition pfk_alias : list (sv * sv) :=
  [(SAlu ALU_ADD (SOff 32 0) (SOff 23 0), SOff 33 0); (SAlu ALU_ADD (SOff 23 0) (SOff 32 0), SOff 33 0)].
Definition pfk_facts (ks : bool) : facts :=
  if ks then mkFacts ((32%nat, mkAF 4096 (2 ^ 47 - 4096) 4) :: (33%nat, mkAF 4096 (2 ^ 47 - 8) 3) :: pfk_atoms) []
    pfk_alias
  else mkFacts pfk_atoms [] [].
Definition pfk_ss (ks : bool) (pc : Z) : sstate := mkSS pc pfk_sregs (pfk_mem ks) None (pfk_facts ks).
Definition PFK_Bx : sv := SOff 20 0.
Definition pfk_SH (ks : bool) : list shent := if ks then [mkSHE 8 0 56; mkSHE 33 0 8] else [mkSHE 8 0 56].

(* ---- small U facts (image B's pj_free_glue.v pfg_U_add / pfg_U_srl3 / pfg_U_cell / pfg_reg_of_U) ---- *)
Lemma pfk_denot_U : forall E e, sv_denot E e = Z_to_bv 64 (U E e).
Proof. intros E e. unfold U. symmetry. apply Z_to_bv_bv_unsigned. Qed.


Ltac pfk_cs :=
  lazymatch goal with |- acallee_saved (bv_unsigned ?x) =>
    let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v end;
  unfold acallee_saved; lia.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {RL : PrhRoomLive}.
Variable SK : YI16.sink_head.
Context {PA : PAImg A_prog_listing}.
#[local] Notation CP := CfParams_preset.
#[local] Abbreviation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Abbreviation VAL := (@pa_val _ A_prog_listing PA).
#[local] Abbreviation SIGMA := (@pa_sigma _ A_prog_listing PA).
#[local] Abbreviation BASE := (@pa_val _ A_prog_listing PA A_TEXT).
#[local] Notation PST := (@prh_pst prh_img_A).
#[local] Existing Instance prh_img_A.
#[local] Existing Instance CfParams_preset.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
(* the fixed re-hideable zone of the cf layer (YGcfRehidePost.v) at this section's run ceiling *)
#[local] Notation RZ_cf := (@YGcfRehidePost.RZ_cf rc).

(* the key segment's environment: the registers, then keys, keys + 8 i and the key (atoms 32 .. 34) *)
Definition PFK_E (regs : bvmap 5 word) (keys ka x : Z) : env :=
  @Eimg _ A_prog_listing PA (Ereg regs [w64 keys; w64 ka; w64 x]).

(* what the seat needs of the keys block: an object's keys + 8 i is a readable, addressable slot holding the key, apart
   from v's node and from the shadow; an array's keys word is 0 *)
Definition pfk_kfacts (ks : bool) (W : world SEGS) (mem : word -> option byte) (v keys i x : Z) : Prop :=
  if ks then
    4096 <= keys <= 2 ^ 47 - 4096 /\ keys mod 16 = 0 /\ keys + 8 * i + 8 <= 2 ^ 47 /\
    rd_u64 SEGS (rdW W mem) (keys + 8 * i) x /\
    range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (keys + 8 * i) 8 /\
    (forall y, keys + 8 * i <= y < keys + 8 * i + 8 -> ~ (SHADOW_OFF <= y < SHADOW_OFF + 17592186044416)) /\
    (keys + 8 * i + 8 <= v \/ v + 56 <= keys + 8 * i)
  else keys = 0.

Lemma pfk_seat : forall en i (ks : bool) keys x (W : world SEGS) regs mem pc,
  pf_vregs en regs -> pf_lregs en regs i ->
  2 ^ 46 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
  4096 <= fe_v en <= 2 ^ 47 - 64 -> fe_v en mod 8 = 0 -> 0 <= i < 2 ^ 42 ->
  rd_u64 SEGS (rdW W mem) (fe_v en + 32) keys ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (fe_v en) 56 -> amem_range (fe_v en) 56 ->
  pfk_kfacts ks W mem (fe_v en) keys i x ->
  (st_ok_pi SEGS VAL (PFK_E regs keys (keys + 8 * i) x) (pfk_ss ks pc)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))) /\
   sh_ok SEGS PFK_Bx (pfk_SH ks) (PFK_E regs keys (keys + 8 * i) x) (mrestrict (w_H W) mem)) /\
  regs_ok (PFK_E regs keys (keys + 8 * i) x) pfk_sregs regs.
Proof.
intros en i ks keys x W regs mem pc HVR HLR Hsp Hal Hv Hv8 Hi Hkeys Hra Hamr HKF.
pose proof HVR as (R8 & R9 & R18 & R19 & R20 & R21).
pose proof HLR as (R22 & R23 & R24 & R25 & R26).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (v := fe_v en) in *.
set (E := PFK_E regs keys (keys + 8 * i) x).
assert (Er : forall n0 (r : bv 5), (n0 < 32)%nat -> Z.of_nat n0 = bv_unsigned r -> ew E n0 = getr regs r).
{ intros n0 r Hn Hr. unfold E, PFK_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat regs _ n0 r Hr). }
assert (EX : forall j, (j < 3)%nat -> ew E (32 + j) = nth j [w64 keys; w64 (keys + 8 * i); w64 x] (Z_to_bv 64 0)).
{ intros j Hj. unfold E, PFK_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ j). }
assert (E32 : ew E 32 = w64 keys) by exact (EX 0%nat ltac:(lia)).
assert (E33 : ew E 33 = w64 (keys + 8 * i)) by exact (EX 1%nat ltac:(lia)).
assert (E34 : ew E 34 = w64 x) by exact (EX 2%nat ltac:(lia)).
assert (U8 : forall c, 0 <= c <= 56 -> U E (SOff 8 c) = v + c).
{ intros c Hc. apply (U_atom_off E 8 v c); [rewrite (Er 8%nat 8%bv) by (first [lia | reflexivity]); exact R8 | lia | lia]. }
assert (U20 : U E (SOff 20 0) = SHADOW_OFF).
{ apply (U_atom E 20 SHADOW_OFF); [rewrite (Er 20%nat 20%bv) by (first [lia | reflexivity]); exact R20 | unfold SHADOW_OFF; lia]. }
assert (U23 : U E (SOff 23 0) = 8 * i).
{ apply (U_atom E 23 (8 * i)); [rewrite (Er 23%nat 23%bv) by (first [lia | reflexivity]); exact R23 | lia]. }
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (Er 2%nat 2%bv) by (first [lia | reflexivity]); reflexivity).
assert (Uv : bv_unsigned (ew E 8) = v).
{ rewrite (Er 8%nat 8%bv) by (first [lia | reflexivity]). rewrite R8. apply unsigned_lit_small. lia. }
assert (Hcell : forall c, 0 <= c <= 56 -> U E (pft_cell (SOff 8 c)) = (v + c) / 8 + SHADOW_OFF).
{ intros c Hc. unfold pft_cell. apply pfa_U_cell; [apply U8; lia | exact U20 | lia]. }
assert (HRG : regs_ok E pfk_sregs regs).
{ rewrite pfk_sregs_eq.
  apply regs_ok_pin; [|pft_regne|rewrite R26, pfk_denot_U, Hcell by lia; reflexivity].
  apply regs_ok_pin; [|pft_regne|rewrite R9, pfk_denot_U, U8 by lia; reflexivity].
  unfold E, PFK_E. apply regs_ok_Eimg_Ereg. }
clearbody E.
split; [|exact HRG].
assert (HAT : atoms_ok E pfk_atoms).
{ unfold pfk_atoms. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp, Uv.
  rewrite (Er 20%nat 20%bv), (Er 23%nat 23%bv) by (first [lia | reflexivity]).
  rewrite R20, R23. unfold w64.
  rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
  change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; try exact I; try exact Hal; try exact Hv8; try lia.
  all: Z.div_mod_to_equations; lia. }
assert (SH8 : shent_ok SEGS PFK_Bx E (mrestrict (w_H W) mem) (mkSHE 8 0 56)).
{ apply (shent_ok_of_range SEGS (w_H W) mem E PFK_Bx 8 v 56 v 0 56 Hra).
  + unfold PFK_Bx. exact U20.
  + rewrite U8 by lia. lia.
  + lia. + lia.
  + intros y Hy. unfold amem_range in Hamr. unfold SHADOW_OFF in *. lia. }
destruct ks; cbn [pfk_kfacts] in HKF.
- (* an object: the keys slot *)
  destruct HKF as (Hk1 & Hk16 & Hkc & Hx & Hkra & Hkapp & Hkv).
  assert (Uk : U E (SOff 32 0) = keys) by (apply (U_atom E 32 keys); [exact E32 | lia]).
  assert (Uka : U E (SOff 33 0) = keys + 8 * i) by (apply (U_atom E 33 (keys + 8 * i)); [exact E33 | lia]).
  assert (Uka' : bv_unsigned (ew E 33) = keys + 8 * i) by (rewrite E33; apply unsigned_lit_small; lia).
  split.
  + rewrite restrict_mkst_fx. unfold pfk_ss, pfk_mem, pfk_facts.
    apply pa_entry_st_ok_full; [exact HRG | vm_compute; reflexivity | | | ].
    * apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      -- unfold region_ok, pfk_vhdr.
         cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Uv.
         split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
         apply Forall_cons; [|apply Forall_nil].
         apply (chunk_ok_val SEGS E _ _ 32 8 (SOff 32 0) keys);
           [rewrite pfk_denot_U, Uk; reflexivity | cbn; exact (proj1 Hkeys) | cbn; lia | exact (proj2 Hkeys)].
      -- unfold region_ok, pfk_kslot.
         cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Uka'.
         split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
         apply Forall_cons; [|apply Forall_nil].
         apply (chunk_ok_val SEGS E _ _ 0 8 (SOff 34 0) x);
           [rewrite pfk_denot_U, (U_atom E 34 x); [reflexivity | exact E34 | exact (proj1 Hx)]
           | cbn; exact (proj1 Hx) | cbn; lia | rewrite Z.add_0_r; exact (proj2 Hx)].
    * cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, pfk_vhdr, pfk_kslot, base_val.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi].
      rewrite Uv, Uka'. split; [split; [lia | exact I] | split; [exact I | exact I]].
    * split; [|split; [exact I|]].
      -- cbn [atoms_ok]. split; [|split; [|exact HAT]]; unfold afact_ok; cbn [af_lo af_hi af_al2].
         ++ rewrite E32. unfold w64. rewrite unsigned_lit_small by lia. change (2 ^ 4) with 16.
            repeat split; first [lia | Z.div_mod_to_equations; lia].
         ++ rewrite Uka'. change (2 ^ 3) with 8. repeat split; first [lia | Z.div_mod_to_equations; lia].
      -- unfold pfk_alias. cbn [alias_ok].
         split; [|split; [|exact I]]; apply U_inj; rewrite pfa_U_add, Uk, U23, Uka; rewrite Z.mod_small by lia; lia.
  + unfold sh_ok, pfk_SH. constructor; [exact SH8|]. constructor; [|constructor].
    apply (shent_ok_of_range SEGS (w_H W) mem E PFK_Bx 33 (keys + 8 * i) 8 (keys + 8 * i) 0 8 Hkra).
    * unfold PFK_Bx. exact U20.
    * exact Uka.
    * lia. * lia.
    * intros y Hy. apply Hkapp. lia.
- (* an array: keys = 0 *)
  subst keys.
  split.
  + rewrite restrict_mkst_fx. unfold pfk_ss, pfk_mem, pfk_facts.
    apply pa_entry_st_ok_full; [exact HRG | vm_compute; reflexivity | | | ].
    * apply Forall_cons; [|apply Forall_nil].
      unfold region_ok, pfk_vhdr.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Uv.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ _ 32 8 (SLit 0) 0);
        [rewrite pfk_denot_U, U_SLit; reflexivity | cbn; lia | cbn; lia | exact (proj2 Hkeys)].
    * cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
    * split; [exact HAT | split; exact I].
  + unfold sh_ok, pfk_SH. constructor; [exact SH8 | constructor].
Qed.

(* ---- the registers a stretch keeps (its symbolic values those of the seat), and (glue another loop segment can use: pfk_keepregs,
   pfk_pres_vlregs) those a call keeps ---- *)
Lemma pfk_kept_pi : forall E ss (ms : machine_state) regs (H : word -> bool),
  st_ok_pi SEGS VAL E ss (restrict H ms) -> regs_ok E pfk_sregs regs ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (sr_get pfk_sregs r))
    [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 21%bv; 22%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv] = true ->
  forall r, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 21%bv; 22%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv] ->
    getr (ms_regs ms) r = getr regs r.
Proof.
intros E ss ms regs H HS HR Hb r Hr. rewrite (st_ok_pi_restrict_reg H E ss ms r HS), (HR r).
f_equal. apply sv_eqb_eq. exact (proj1 (forallb_forall _ _) Hb r Hr).
Qed.
Lemma pfk_kept_c : forall E ss (ms : machine_state) regs (H : word -> bool),
  st_ok SEGS E ss (restrict H ms) -> regs_ok E pfk_sregs regs ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (sr_get pfk_sregs r))
    [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 21%bv; 22%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv] = true ->
  forall r, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 21%bv; 22%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv] ->
    getr (ms_regs ms) r = getr regs r.
Proof.
intros E ss ms regs H HS HR Hb r Hr. rewrite (st_ok_restrict_reg SEGS H E ss ms r HS), (HR r).
f_equal. apply sv_eqb_eq. exact (proj1 (forallb_forall _ _) Hb r Hr).
Qed.
Lemma pfk_keepregs : forall en i (rg rg2 : bvmap 5 word),
  (forall r, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 21%bv; 22%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv] ->
     getr rg2 r = getr rg r) ->
  pf_vregs en rg -> pf_lregs en rg i ->
  pf_vregs en rg2 /\ pf_lregs en rg2 i /\ getr rg2 2 = getr rg 2 /\ getr rg2 3 = getr rg 3 /\ getr rg2 4 = getr rg 4 /\
  getr rg2 27 = getr rg 27.
Proof.
intros en i rg rg2 K HV HL.
pose proof HV as (R8 & R9 & R18 & R19 & R20 & R21).
pose proof HL as (R22 & R23 & R24 & R25 & R26).
unfold pf_vregs, pf_lregs.
rewrite !K by (cbn [In]; repeat first [left; reflexivity | right]).
repeat split; assumption.
Qed.
Lemma pfk_pres_vlregs : forall en i rg rg2, aregs_preserved rg rg2 -> pf_vregs en rg -> pf_lregs en rg i ->
  pf_vregs en rg2 /\ pf_lregs en rg2 i /\ getr rg2 2 = getr rg 2 /\ getr rg2 3 = getr rg 3 /\ getr rg2 4 = getr rg 4 /\
  getr rg2 27 = getr rg 27.
Proof.
intros en i rg rg2 HP HV HL. apply (pfk_keepregs en i rg rg2); [|exact HV | exact HL].
intros r Hr. apply (pfa_pres rg rg2 r HP).
cbn [In] in Hr. repeat (destruct Hr as [<- | Hr]; [pfk_cs|]). destruct Hr.
Qed.

(* ---- the fuzz_free call's return site AF_pf + 200 (= PF_LC): a text address below the ceiling, a code pointer ---- *)
Lemma pfk_lc_lt : 0 <= AF_pf + PF_LC < 2 ^ 40.
Proof. lazymatch eval vm_compute in (AF_pf + PF_LC) with ?n => change (AF_pf + PF_LC) with n end. lia. Qed.
Lemma pfk_ra_lt : BASE + (AF_pf + PF_LC) < YM05.alloc_ceiling.
Proof. apply (pa_slot_lt_ceil_b (PL := PL_prog_A) (PI := PA) (AF_pf + PF_LC) pfk_lc_lt). vm_compute. reflexivity. Qed.
Lemma pfk_ra_ok : YK0s.ret_ok (Z_to_bv 64 (BASE + (AF_pf + PF_LC))).
Proof. apply (ret_ok_codeptr_v (PI := PA) (AF_pf + PF_LC) pfk_lc_lt). vm_compute. reflexivity. Qed.

Section e.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Hypothesis LAWS : AR_laws_x SEGS B ARx (@cf_head CP).
Hypothesis VISF : YGcfFsVis.ARx_frame_hull_vis SEGS B ARx.
(* image facts, discharged at PI_prog_A: the image start; alloc.c's statics are no read-only bytes (S1ImgA.v
   pst_not_ro_A); pj_free's four `jal fuzz_free` return sites (AF_pf + 200 / 252 / 276 / 304), by vm_compute *)
Hypothesis PAB : @pa_lo _ _ PA = IMG_LO.
Hypothesis pal_pst_ro : forall a, Exists (in_zr a) PST -> ~ in_roP SEGS (@pa_relro_lo _ _ PA) (@pa_relro_hi _ _ PA) a.
Hypothesis pal_ret_free : forall off, In off [200; 252; 276; 304] ->
  In (BASE + AF_pf + off) (@pi_ret_sites prh_img_A F_pj_free RT_fuzz_free).
Variable Pm : (word -> option byte) -> Prop.
Hypothesis PLAW : srr_inv_laws SEGS Pm.
(* the segment crosses fuzz_free, whose keep is the memnorm one *)
Hypothesis PCALL : srr_inv_call SEGS Pm.
Variable CTX0 : list (list Z).
Variable PB : astate -> Prop.
Variable FX : pf_obs.
(* the callee: the instrumented fuzz_free text (PjFreeCommon) *)
Hypothesis FREE : tfuzz_free_specO (PA := PA) B ARx SK PB FX.
#[local] Notation AJ := (ajournal_x (SK := SK) SEGS B PST ARx).






(* ---- glue another loop segment can use: what every loop cut gives: the kids block holds the n slots, the slot index and the stack
   numbers ---- *)
Lemma pfl_basics : forall en nd i ly S Hp W regs mem md k,
  pf_pre B ARx CTX0 PB FX en -> pf_node en nd -> 0 <= i < fn_n nd ->
  pf_frameR SK B ARx Pm (wle' SEGS RZ_cf) en ly S Hp W regs mem md k ->
  (exists kk, In (fn_kids nd, kk) (fe_Lam en) /\ 56 * fn_n nd <= kk /\ fn_Dk nd = [(fn_kids nd, kk)] /\
     4096 <= fn_kids nd /\ fn_kids nd + kk <= YM05.alloc_ceiling /\ fn_kids nd mod 16 = 0) /\
  0 <= i < 2 ^ 42 /\ 2 ^ 46 <= spZ regs <= 2 ^ 47 /\ spZ regs mod 16 = 0 /\
  YM05.alloc_ceiling <= fe_sp0 en - 96.
Proof.
intros en nd i ly S Hp W regs mem md k HPRE HND Hi HFR.
pose proof HFR as (_ & _ & Hsp & _).
pose proof HPRE as (HFPRE0 & _ & _ & _ & _ & _ & _ & HLED0).
pose proof HFPRE0 as (HAFN0 & _ & _).
pose proof HAFN0 as (HAR0 & _).
pose proof HND as (_ & _ & _ & _ & HKIDSn & _).
pose proof (YM05.alloc_ceiling_value) as HAC0.
destruct (pf_sp B ARx CTX0 PB FX en HPRE) as (S46 & S47 & S16 & SCE).
pose proof (pf_stk0 (fe_n en)) as [FS FS2].
assert (Hkk : exists kk, In (fn_kids nd, kk) (fe_Lam en) /\ 56 * fn_n nd <= kk /\ fn_Dk nd = [(fn_kids nd, kk)] /\
  4096 <= fn_kids nd /\ fn_kids nd + kk <= YM05.alloc_ceiling /\ fn_kids nd mod 16 = 0).
{ destruct HKIDSn as [(_ & Hn0 & _) | (kk & Hin & Hkn & HDk)]; [lia|].
  destruct ((pfa_lam_blk B ARx LAWS) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HAR0 HLED0 Hin) as (Hk0 & Ha0 & Hak & Ha16 & _). change (@cf_head CP) with 16 in *.
  exists kk. repeat split; first [assumption | lia]. }
split; [exact Hkk|].
destruct Hkk as (kk & _ & Hkkn & _ & Hkid4 & Hkidc & _).
split; [lia|]. split; [lia|]. split; [rewrite Hsp; Z.div_mod_to_equations; lia|]. lia.
Qed.


Theorem pf_seg_LC : forall d', pfs_LC SK B ARx Pm CTX0 PB FX d'.
Proof.
intros d' en nd i ly S Hp W regs mem md k HPRE HND Hvnz HLC KLH KLX.
pose proof HLC as (En & Hi & HFR & HVR & HLR & Fd & Lam & Dr & Fr & HAC & HVN & HPD & HIT).
pose proof HFR as (HJ & HWIN & Hsp & HSV & HPRES & H3 & H4 & H27 & HROD & HPM).
pose proof HVR as (R8 & R9 & R18 & R19 & R20 & R21).
pose proof HLR as (R22 & R23 & R24 & R25 & R26).
pose proof HVN as (Hv4096 & Hv56 & Hv8 & Hamr & Hstr & Hkids & Hkeys & Hnn & _ & _ & Hvra & _).
destruct (pfl_basics en nd i ly S Hp W regs mem md k HPRE HND Hi HFR) as (_ & Hi42 & Hspr & Hal & Hceil0).
pose proof (YM05.alloc_ceiling_value) as HAC0.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (pft_seat en nd W regs mem (AF_pf + PF_LC) HVR Hspr Hal ltac:(lia) Hv8 Hstr Hkids Hkeys Hnn Hvra Hamr)
  as [HS SHOK].
set (E := PFT_E regs nd) in HS, SHOK.
assert (HEI : img_env VAL A_LIM E) by (unfold E, PFT_E; apply Eimg_env).
assert (Er : forall n0 (r : bv 5), (n0 < 32)%nat -> Z.of_nat n0 = bv_unsigned r -> ew E n0 = getr regs r).
{ intros n0 r Hn Hr. unfold E, PFT_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat regs _ n0 r Hr). }
assert (EX : forall j, (j < 4)%nat -> ew E (32 + j) =
  nth j [w64 (fn_str nd); w64 (fn_kids nd); w64 (fn_keys nd); w64 (fn_n nd)] (Z_to_bv 64 0)).
{ intros j Hj. unfold E, PFT_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ j). }
assert (HAE : env_agree 32 (Ereg regs [w64 (fn_str nd); w64 (fn_kids nd); w64 (fn_keys nd); w64 (fn_n nd)]) E)
  by (unfold E, PFT_E; split; [intros n0 Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (Un : U E (SOff 35 0) = fn_n nd).
{ pose proof (EX 3%nat ltac:(lia)) as X3. change (32 + 3)%nat with 35%nat in X3. cbn [nth] in X3.
  apply (U_atom E 35 (fn_n nd)); [exact X3 | exact (proj1 Hnn)]. }
assert (U8 : forall c, 0 <= c <= 56 -> U E (SOff 8 c) = fe_v en + c).
{ intros c Hc. apply (U_atom_off E 8 (fe_v en) c); [rewrite (Er 8%nat 8%bv) by (first [lia | reflexivity]); exact R8 | lia | lia]. }
assert (U20 : U E (SOff 20 0) = SHADOW_OFF).
{ apply (U_atom E 20 SHADOW_OFF); [rewrite (Er 20%nat 20%bv) by (first [lia | reflexivity]); exact R20 | unfold SHADOW_OFF; lia]. }
assert (Ucell : forall c, 0 <= c <= 56 -> U E (pft_cell (SOff 8 c)) = (fe_v en + c) / 8 + SHADOW_OFF).
{ intros c Hc. unfold pft_cell. apply pfa_U_cell; [apply U8; lia | exact U20 | lia]. }
assert (U22 : U E (SOff 22 56) = 56 * (i + 1)).
{ rewrite (U_atom_off E 22 (56 * i) 56); [lia | rewrite (Er 22%nat 22%bv) by (first [lia | reflexivity]); exact R22 | lia | lia]. }
assert (U23 : U E (SOff 23 8) = 8 * (i + 1)).
{ rewrite (U_atom_off E 23 (8 * i) 8); [lia | rewrite (Er 23%nat 23%bv) by (first [lia | reflexivity]); exact R23 | lia | lia]. }
assert (U24 : U E (SOff 24 1) = i + 1).
{ apply (U_atom_off E 24 i 1); [rewrite (Er 24%nat 24%bv) by (first [lia | reflexivity]); exact R24 | lia | lia]. }
clearbody E.
pose (RUN := @paj_run_x_invR fx rc SK A_prog_listing PL_prog_A PA B PST ARx _ LAWS (fun m => Pm (fe_mem en) -> Pm m)
  (srr_inv_laws_imp SEGS Pm (fe_mem en) PLAW) (wle' SEGS RZ_cf) (wle'_refl SEGS RZ_cf) (wle'_trans SEGS RZ_cf)).
pose (RUNTO := @paj_run_to_x_invR fx rc SK A_prog_listing PL_prog_A PA B PST ARx _ LAWS (fun m => Pm (fe_mem en) -> Pm m)
  (srr_inv_laws_imp SEGS Pm (fe_mem en) PLAW) (wle' SEGS RZ_cf) (wle'_refl SEGS RZ_cf) (wle'_trans SEGS RZ_cf)).
pose (BR := paj_branchR (PI := PA) (wle' SEGS RZ_cf)).
unfold pf_cfg.
(* slots 50-55: the ASan check of v+40, n, i += 1, 8 i += 8, 56 i += 56; stop at `bltu s8, a0` *)
paj_run_tok_x_inv RUN HS HJ SHOK HPM PF_Bspan; [gs_awr0|].
gs_memeq HF M1. clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK PF_Bspan.
- (* taken: i + 1 < n, to the loop head at slot i + 1 *)
  assert (Hlt : i + 1 < fn_n nd).
  { rewrite branch_ltu_U, U24, Un in Hc. apply Z.ltb_lt in Hc. exact Hc. }
  clear Hc.
  paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM PF_Bspan (AF_pf + PF_LH); [gs_awr0|].
  gs_memeq HF M2. clear HF HFr HG.
  pfa_reg HS (9%bv : bv 5) Q9. pfa_reg HS (18%bv : bv 5) Q18. pfa_reg HS (19%bv : bv 5) Q19.
  pfa_reg HS (21%bv : bv 5) Q21. pfa_reg HS (22%bv : bv 5) Q22. pfa_reg HS (23%bv : bv 5) Q23.
  pfa_reg HS (24%bv : bv 5) Q24.
  pose proof (regs_kept_of_st_ok_pi (PI := PA) E _ _ regs _ [2%bv; 3%bv; 4%bv; 8%bv; 20%bv; 25%bv; 26%bv; 27%bv] HS HAE
    ltac:(vm_compute; reflexivity)) as KR.
  cbn [ms_regs restrict] in KR.
  pmkst HS.
  rewrite M2, M1 in HJ, HPM |- *.
  lazymatch goal with |- SRrG _ _ _ (mkCfg (mkst ?rg (Z_to_bv 64 (_ + ?pc)) _ _) ?dd) _ =>
    replace pc with (AF_pf + PF_LH) by (vm_compute; reflexivity);
    apply (KLH ly S Hp W rg mem dd k) end.
  split; [exact En|]. split; [lia|].
  split; [apply ((pfa_frame_sameR SK B ARx Pm (wle' SEGS RZ_cf)) en ly S Hp W regs _ mem md _ k HFR HJ); apply KR; cbn [In]; tauto|].
  split.
  { unfold pf_vregs. unfold w64.
    split; [rewrite (KR 8%bv) by (cbn [In]; tauto); exact R8|].
    split; [apply (pfa_reg_of_U E _ _ _ Q9); apply U8; lia|].
    split; [apply (pfa_reg_of_U E _ _ _ Q18); apply U8; lia|].
    split; [apply (pfa_reg_of_U E _ _ _ Q19); apply U8; lia|].
    split; [rewrite (KR 20%bv) by (cbn [In]; tauto); exact R20|].
    apply (pfa_reg_of_U E _ _ _ Q21). apply (Ucell 40); lia. }
  split.
  { unfold pf_lregs. unfold w64.
    split; [apply (pfa_reg_of_U E _ _ _ Q22); exact U22|].
    split; [apply (pfa_reg_of_U E _ _ _ Q23); exact U23|].
    split; [apply (pfa_reg_of_U E _ _ _ Q24); exact U24|].
    split; [rewrite (KR 25%bv) by (cbn [In]; tauto); exact R25|].
    rewrite (KR 26%bv) by (cbn [In]; tauto); exact R26. }
  exists Fd, Lam, Dr, Fr. split; [exact HAC|]. split; [exact HVN|]. split; [exact HPD | exact HIT].
- (* not taken: i + 1 = n, after the loop *)
  assert (Hge : fn_n nd <= i + 1).
  { rewrite branch_ltu_U, U24, Un in Hc. apply Z.ltb_ge in Hc. exact Hc. }
  clear Hc.
  paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM PF_Bspan (AF_pf + PF_LX); [gs_awr0|].
  gs_memeq HF M2. clear HF HFr HG.
  pfa_reg HS (9%bv : bv 5) Q9. pfa_reg HS (18%bv : bv 5) Q18. pfa_reg HS (19%bv : bv 5) Q19.
  pfa_reg HS (21%bv : bv 5) Q21.
  pose proof (regs_kept_of_st_ok_pi (PI := PA) E _ _ regs _ [2%bv; 3%bv; 4%bv; 8%bv; 20%bv; 27%bv] HS HAE
    ltac:(vm_compute; reflexivity)) as KR.
  cbn [ms_regs restrict] in KR.
  pmkst HS.
  rewrite M2, M1 in HJ, HPM |- *.
  lazymatch goal with |- SRrG _ _ _ (mkCfg (mkst ?rg (Z_to_bv 64 (_ + ?pc)) _ _) ?dd) _ =>
    replace pc with (AF_pf + PF_LX) by (vm_compute; reflexivity);
    apply (KLX ly S Hp W rg mem dd k) end.
  replace (Z.to_nat (fn_n nd - (i + 1))) with O in HIT by lia. destruct HIT as [-> ->].
  split; [apply ((pfa_frame_sameR SK B ARx Pm (wle' SEGS RZ_cf)) en ly S Hp W regs _ mem md _ k HFR HJ); apply KR; cbn [In]; tauto|].
  split.
  { unfold pf_vregs. unfold w64.
    split; [rewrite (KR 8%bv) by (cbn [In]; tauto); exact R8|].
    split; [apply (pfa_reg_of_U E _ _ _ Q9); apply U8; lia|].
    split; [apply (pfa_reg_of_U E _ _ _ Q18); apply U8; lia|].
    split; [apply (pfa_reg_of_U E _ _ _ Q19); apply U8; lia|].
    split; [rewrite (KR 20%bv) by (cbn [In]; tauto); exact R20|].
    apply (pfa_reg_of_U E _ _ _ Q21). apply (Ucell 40); lia. }
  exists Fd, Lam. split; [exact HAC|]. split; [exact HVN|]. exact HPD.
Qed.

(* ---- THE KEY: AF_pf + 156 .. `jal fuzz_free` (AF_pf + 196, returning at AF_pf + 200 = PF_LC), or keys = NULL straight
   to AF_pf + 200 ---- *)
Theorem pf_seg_LK : forall d', pfs_LK SK B ARx Pm CTX0 PB FX d'.
Proof.
intros d' en nd i ly S Hp W regs mem md k HPRE HND Hvnz HLK KLC.
pose proof HLK as (En & Hi & HFR & HVR & HLR & Fd & Lam & Dk & Dr & Fr & HAC & HVN & HPD & HKEY & HIT).
pose proof HFR as (HJ & HWIN & Hsp & HSV & HPRES & H3 & H4 & H27 & HROD & HPM).
pose proof HVR as (R8 & R9 & R18 & R19 & R20 & R21).
pose proof HLR as (R22 & R23 & R24 & R25 & R26).
pose proof HVN as (Hv4096 & Hv56 & Hv8 & Hamr & Hstr & Hkids & Hkeys & Hnn & Hrw & Hown & Hvra & Hvhull & Hplace).
pose proof HAC as (HROOM & HLED & HPL & HPB & EF & HRE).
pose proof HPRE as (HFPRE0 & HUNIV & _ & _ & HWIN0 & _ & HSAFE & HLED0).
pose proof HFPRE0 as (HAFN0 & HROD0 & HSTKHI0 & HRAZ0 & HFRM0).
pose proof HAFN0 as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & Hqt0).
pose proof HWIN0 as (Hd0 & Hd16 & Hdtop & Hdpres).
pose proof HND as (HNDD & HAPD & HHDR & HSTRn & HKIDSn & HKEYSn & HPDn & HFDn & HITn).
pose proof (YM05.alloc_ceiling_value) as HAC0.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (pf_sp B ARx CTX0 PB FX en HPRE) as (S46 & S47 & S16 & SCE).
pose proof (pf_stk0 (fe_n en)) as [FS FS2].
pose proof (ajxR_ar HJ) as HAR. pose proof (ajxR_ly HJ) as Hly.
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
pose proof (@pa_segs_low _ _ PA) as Hsegs.
destruct (pfl_basics en nd i ly S Hp W regs mem md k HPRE HND Hi HFR)
  as ((kk & Hkkin & Hkkn & HDkk & Hkk4 & Hkkc & Hkk16) & Hi42 & Hspr & Hal & Hceil0).
assert (Hvb : 4096 <= fe_v en <= 2 ^ 47 - 64) by lia.
pose (RUN := @paj_run_x_invR fx rc SK A_prog_listing PL_prog_A PA B PST ARx _ LAWS (fun m => Pm (fe_mem en) -> Pm m)
  (srr_inv_laws_imp SEGS Pm (fe_mem en) PLAW) (wle' SEGS RZ_cf) (wle'_refl SEGS RZ_cf) (wle'_trans SEGS RZ_cf)).
pose (RUNTO := @paj_run_to_x_invR fx rc SK A_prog_listing PL_prog_A PA B PST ARx _ LAWS (fun m => Pm (fe_mem en) -> Pm m)
  (srr_inv_laws_imp SEGS Pm (fe_mem en) PLAW) (wle' SEGS RZ_cf) (wle'_refl SEGS RZ_cf) (wle'_trans SEGS RZ_cf)).
unfold pf_cfg.
destruct HKEYSn as [(Ekeys & Eks & EDy) | (Eks & ky & Hky & Hkyn & EDy)].
- (* ======== an array: keys = NULL, the beqz goes to AF_pf + 200 with nothing freed ======== *)
  rewrite Eks in HKEY. cbn [pj_keyR] in HKEY. subst Dk.
  destruct (pfk_seat en i false (fn_keys nd) 0 W regs mem (AF_pf + PF_LK) HVR HLR Hspr Hal Hvb Hv8 Hi42
    Hkeys Hvra Hamr Ekeys) as [[HS SHOK] HRG].
  set (E := PFK_E regs (fn_keys nd) (fn_keys nd + 8 * i) 0) in HS, SHOK, HRG.
  assert (HEI : img_env VAL A_LIM E) by (unfold E, PFK_E; apply Eimg_env).
  clearbody E.
  paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM PF_Bspan (AF_pf + PF_LC); [gs_awr0|].
  gs_memeq HF M1. clear HF HFr HG.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into msA end.
  destruct (pfk_keepregs en i regs (ms_regs msA)
    (pfk_kept_pi E _ msA regs _ HS HRG ltac:(vm_compute; reflexivity)) HVR HLR)
    as (HVR1 & HLR1 & E21 & E31 & E41 & E271).
  pmkst HS.
  rewrite M1 in HJ, HPM |- *.
  lazymatch goal with |- SRrG _ _ _ (mkCfg (mkst ?rg (Z_to_bv 64 (_ + ?pc)) _ _) ?dd) _ =>
    replace pc with (AF_pf + PF_LC) by (vm_compute; reflexivity);
    apply (KLC ly S Hp W rg mem dd k) end.
  split; [exact En|]. split; [exact Hi|].
  split; [apply ((pfa_frame_sameR SK B ARx Pm (wle' SEGS RZ_cf)) en ly S Hp W regs _ mem md _ k HFR HJ); assumption|].
  split; [exact HVR1|]. split; [exact HLR1|].
  exists Fd, Lam, Dr, Fr. split; [exact HAC|]. split; [exact HVN|]. split; [exact HPD | exact HIT].
- (* ======== an object: keys <> NULL ======== *)
  assert (HyD : In (fn_keys nd, ky) (fe_D en)).
  { apply (Permutation_in _ (Permutation_sym HPDn)). rewrite EDy, !in_app_iff. cbn [In]. tauto. }
  assert (ND : NoDup (Fd ++ Dk ++ Dr ++ fn_own nd)) by exact (pfa_nd_perm _ _ HPD HNDD).
  assert (NDr : NoDup (Dk ++ Dr ++ fn_own nd)) by exact (pfa_ndr _ _ ND).
  assert (HinD : forall b, In b (Fd ++ Dk ++ Dr ++ fn_own nd) -> In b (fe_D en))
    by (intros b Hb; exact (Permutation_in _ (Permutation_sym HPD) Hb)).
  assert (HyOwn : In (fn_keys nd, ky) (fn_own nd)) by (unfold fn_own; rewrite EDy, !in_app_iff; cbn [In]; tauto).
  assert (HkOwn : In (fn_kids nd, kk) (fn_own nd)) by (unfold fn_own; rewrite HDkk; left; reflexivity).
  assert (HyLam : In (fn_keys nd, ky) Lam).
  { apply (pfa_lam_now (fe_Lam en) Fd Lam _ HPL Hky). intros Hf.
    apply (pfa_nd_app Fd _ _ ND Hf). rewrite !in_app_iff. tauto. }
  assert (HkLam : In (fn_kids nd, kk) Lam).
  { apply (pfa_lam_now (fe_Lam en) Fd Lam _ HPL Hkkin). intros Hf.
    apply (pfa_nd_app Fd _ _ ND Hf). rewrite !in_app_iff. tauto. }
  assert (HownDk : forall b, In b (fn_own nd) -> ~ In b Dk).
  { intros b Ho Hk. apply (pfa_nd_app Dk (Dr ++ fn_own nd) b NDr Hk). apply in_or_app; right; exact Ho. }
  assert (HDrDk : forall b, In b Dr -> ~ In b Dk).
  { intros b Hr Hk. apply (pfa_nd_app Dk (Dr ++ fn_own nd) b NDr Hk). apply in_or_app; left; exact Hr. }
  assert (HDkD : forall b, In b Dk -> In b (fe_D en)).
  { intros b Hb. apply HinD. apply in_or_app; right; apply in_or_app; left; exact Hb. }
  destruct ((pfa_lam_blk B ARx LAWS) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HAR HLED HyLam) as (Hky0 & Hk4 & Hkc & Hk16 & Hyab & Hyhp). change (@cf_head CP) with 16 in *.
  rewrite Eks in HKEY. cbn [pj_keyR] in HKEY. destruct HKEY as (x & Hxu & Hxc).
  (* the key: NULL (no block) or a harness block of the ledger, one of D's *)
  assert (HXK : exists kx, (x = 0 /\ Dk = []) \/ (x <> 0 /\ In (x, kx) Lam /\ Dk = [(x, kx)])).
  { destruct Hxc as [(Ex & EDk) | (kx & Hkx & EDk)]; [exists 0; left; split; assumption|].
    exists kx. right. unfold prh_lin in Hkx.
    destruct ((pfa_lam_blk B ARx LAWS) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HAR HLED Hkx) as (_ & Hx4 & _). change (@cf_head CP) with 16 in *.
    split; [lia|]. split; assumption. }
  destruct HXK as (kx & HXK). clear Hxc.
  assert (HDkL : forall b, In b Dk -> In b Lam).
  { intros b Hb. destruct HXK as [(_ & EDk) | (_ & Hkx & EDk)]; rewrite EDk in Hb; [destruct Hb|].
    destruct Hb as [<- | []]. exact Hkx. }
  destruct ((pfa_hb_vis B ARx LAWS) ly S Hp W mem md Lam _ _ _ _ _ _ (fn_keys nd) ky (fn_keys nd + 8 * i) 8 HAR HLED HyLam
    ltac:(lia) ltac:(lia) ltac:(lia)) as (Hkra & _ & Hkamr & _).
  assert (Hkapp : forall y, fn_keys nd + 8 * i <= y < fn_keys nd + 8 * i + 8 ->
    ~ (SHADOW_OFF <= y < SHADOW_OFF + 17592186044416)).
  { intros y Hy. unfold amem_range in Hkamr. unfold SHADOW_OFF. lia. }
  pose proof (HAPD (fn_keys nd, ky) (fn_keys nd + 8 * i) HyD ltac:(unfold pj_holdsR; cbn [fst snd]; lia)) as A1.
  pose proof (HAPD (fn_keys nd, ky) (fn_keys nd + 8 * i + 7) HyD ltac:(unfold pj_holdsR; cbn [fst snd]; lia)) as A2.
  destruct (pfk_seat en i true (fn_keys nd) x W regs mem (AF_pf + PF_LK) HVR HLR Hspr Hal Hvb Hv8 Hi42
    Hkeys Hvra Hamr) as [[HS SHOK] HRG].
  { cbn [pfk_kfacts]. split; [lia|]. split; [exact Hk16|]. split; [lia|]. split; [exact Hxu|].
    split; [exact Hkra|]. split; [exact Hkapp|]. lia. }
  set (E := PFK_E regs (fn_keys nd) (fn_keys nd + 8 * i) x) in HS, SHOK, HRG.
  assert (HEI : img_env VAL A_LIM E) by (unfold E, PFK_E; apply Eimg_env).
  assert (E34 : ew E 34 = w64 x).
  { unfold E, PFK_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 2). }
  clearbody E.
  (* slots 39-49: the ASan check of v+32, keys <> NULL, keys + 8 i and its ASan check, the key, `jal fuzz_free` *)
  paj_run_tok_x_inv RUN HS HJ SHOK HPM PF_Bspan; [gs_awr0|].
  gs_memeq HF M1. clear HF HFr HG.
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?m) => rename m into msA end.
  pfa_reg HS (10%bv : bv 5) Q10.
  prreg HS (1%bv : bv 5) R1c.
  destruct (pfk_keepregs en i regs (ms_regs msA)
    (pfk_kept_c E _ msA regs _ HS HRG ltac:(vm_compute; reflexivity)) HVR HLR)
    as (HVRc & HLRc & E2c & E3c & E4c & E27c).
  pmkst HS.
  rewrite M1 in HJ, HPM |- *.
  set (regsc := ms_regs msA) in *.
  lazymatch goal with |- SRrG _ _ _ (mkCfg (mkst _ _ _ _) ?dd) _ => set (mdc := dd) in * end.
  assert (HRA1 : getr regsc 1 = Z_to_bv 64 (BASE + (AF_pf + PF_LC))).
  { rewrite R1c. lazymatch goal with |- Z_to_bv 64 (_ + ?n) = _ =>
      replace n with (AF_pf + PF_LC) by (vm_compute; reflexivity) end. reflexivity. }
  assert (HGP : getr regsc 3 = w64 (as_gp B)) by (rewrite E3c, H3; exact Hgp0).
  assert (HTP : getr regsc 4 = w64 (as_tp B)) by (rewrite E4c, H4; exact Htp0).
  assert (HSPC : spZ regsc = fe_sp0 en - 96) by (unfold spZ; rewrite E2c; exact Hsp).
  pose proof pfk_ra_lt as HRAlt. pose proof pfk_lc_lt as HLClt. pose proof pfk_ra_ok as HRAW.
  pose proof (pa_base_lo (PL := PL_prog_A) (PI := PA)) as HBLO. rewrite PAB in HBLO. unfold IMG_LO in HBLO.
  assert (HRAu : bv_unsigned (Z_to_bv 64 (BASE + (AF_pf + PF_LC))) = BASE + (AF_pf + PF_LC))
    by (apply unsigned_lit_small; lia).
  assert (HRA4 : 4096 <= bv_unsigned (Z_to_bv 64 (BASE + (AF_pf + PF_LC)))) by (rewrite HRAu; lia).
  assert (HS0LOW : s0Z regsc < YM05.alloc_ceiling).
  { unfold s0Z. pose proof HVRc as (R8c & _). rewrite R8c. unfold w64. rewrite unsigned_lit_small by lia. lia. }
  assert (HSPO : spZ regsc = fe_sp0 en + fe_d en + (-96 - fe_d en)) by (rewrite HSPC; lia).
  assert (Hal' : (-96 - fe_d en) mod 16 = 0) by (Z.div_mod_to_equations; lia).
  assert (Hneg : -96 - fe_d en <= 0) by lia.
  pose proof pfa_stk_ff as HSTKF.
  assert (Hbud : STK_fuzz_free - (-96 - fe_d en) <= STK_pj_free (fe_n en) + fe_d en) by lia.
  assert (He0 : 0 <= 0) by lia.
  assert (Hetop : -96 - fe_d en + 0 <= 0) by lia.
  assert (HA10 : getr regsc 10 = w64 x).
  { rewrite Q10, pfk_denot_U, (U_atom E 34 x E34 (proj1 Hxu)). reflexivity. }
  (* the free's trace: [pc0], or pc0 and the return site AF_pf + 200, one of pj_free's fuzz_free sites *)
  assert (HTR : In (call_trace ly (pc_free_ra0 (as_code B)) regsc []) (as_universe B)).
  { unfold call_trace. destruct (frame0_ok ly regsc).
    - change (In (prh_trace (prh_pc0 B RT_fuzz_free) (raZ regsc) []) (as_universe B)).
      apply (prh_univ_closure_lit B CTX0 F_pj_free RT_fuzz_free (raZ regsc) HUNIV).
      unfold raZ. rewrite HRA1, HRAu.
      replace (BASE + (AF_pf + PF_LC)) with (BASE + AF_pf + 200) by (unfold PF_LC; lia).
      apply pal_ret_free. cbn [In]. left. reflexivity.
    - destruct HUNIV as (HU1 & _). exact (HU1 RT_fuzz_free). }
  (* PB at the call: the order so far reached it *)
  assert (HPBS : PB S) by exact (pf_safe_here FX PB _ ly S (pf_safe_after FX PB _ _ _ _ _ _ (HSAFE Hvnz) HRE)).
  assert (HPKX : x = 0 \/ In (x, kx) Lam) by (destruct HXK as [(Ex & _) | (_ & Hkx & _)]; [left | right]; assumption).
  (* the callee's footprint: the key's block, or nothing *)
  set (FP1 := if x =? 0 then [] else ablocks_fp [(x - cf_head, kx + cf_head)]).
  assert (HFPD : forall y, inFP FP1 y ->
    exists a' k', In (a', k') Dk /\ a' - 16 <= y < a' - 16 + req_size (k' + 16)).
  { intros y Hy. unfold FP1 in Hy. destruct HXK as [(Ex & EDk) | (Ex & Hkx & EDk)].
    - rewrite Ex, Z.eqb_refl in Hy. destruct Hy as (r & Hr & _). destruct Hr.
    - apply Z.eqb_neq in Ex. rewrite Ex in Hy. destruct Hy as (r & Hr & Hry).
      cbn [ablocks_fp map In] in Hr. destruct Hr as [<- | []]. cbn [fst snd] in Hry.
      change (@cf_head CP) with 16 in Hry.
      exists x, kx. split; [rewrite EDk; left; reflexivity | lia]. }
  assert (Hv0b : (fe_v en =? 0) = false) by (apply Z.eqb_neq; exact Hvnz).
  assert (HSH : spZ regsc + 64 <= ly_stk_hi ly) by (rewrite HSPC, Eshi; unfold fe_sp0 in *; lia).
  (* fpre's return-address bound: the jal's return pc AF_pf + 200, a text slot below the ceiling *)
  assert (HRAc : raZ regsc < YM05.alloc_ceiling) by (unfold raZ; rewrite HRA1, HRAu; exact HRAlt).
  (* ======== the call: fuzz_free's text at the key x, callee window 0 ======== *)
  eapply (SRr'_bind SEGS RZ_cf).
  { eapply (aj_call_xWR (fx := fx) (SK := SK) SEGS B PST ARx LAWS Hsegs (wle' SEGS RZ_cf) (wle'_refl SEGS RZ_cf)
      (wle'_trans SEGS RZ_cf) W regsc mem (SIGMA AS_fuzz_free)
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ STK_fuzz_free 0 FP1 (-96 - fe_d en) (Z_to_bv 64 (BASE + (AF_pf + PF_LC))) [] _
      HJ HSPO Hal' Hneg HSTKF Hbud He0 eq_refl Hetop HGP HTP HRA1 HRAW HRA4 (achain_low _ _ _ _ HS0LOW)).
    - intros HPRE1 HWIN1.
      eapply (SRrG_mono SEGS (wle' SEGS RZ_cf)); [exact (FREE (fe_most en) (fe_own en) ly S Hp W regsc mem mdc [] x kx Lam (fe_peak en) (fe_cnt en)
        (fe_fail en) (fe_ran en) (conj HPRE1 (conj HROD (conj HSH (conj HRAc HFRM0)))) HROOM HPBS HTR HA10 HPKX HLED)|].
      intros W' c' _ HQ. exact (fpostW_x_of_apostR (SK := SK) SEGS B PST ARx (wle' SEGS RZ_cf) _ _ _ _ _ _ _ _ _ _ _ _ HQ).
    - (* the footprint: the key's block, one of D's *)
      intros a Ha. left. destruct (HFPD a Ha) as (a' & k' & HinDk & Hr).
      unfold fe_FP. rewrite Hv0b. apply inFP_cons. right. exact (pfa_inFP_hbl _ a' k' a (HDkD _ HinDk) Hr). }
  cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ2 & HJc & HX & HP2 & HK).
  cbv beta in HK. unfold fQmn in HK. destruct HK as ((HFX & HROOM2 & HKK) & HMN2).
  apply (KLC ly2 S2 Hp2 W2 regs2 mem2 md2 (k + k1)).
  (* ---- the accounts after the free ---- *)
  assert (POST : exists Lam2, pf_acct B FX en ly2 S2 Hp2 W2 mem2 (Fd ++ Dk) (Fr ++ fn_own nd) Lam2 /\
    prh_ledger (PA := PA) B ly2 S2 Hp2 W2 mem2 Lam2 (fe_peak en) (fe_cnt en) (fe_fail en) (fe_ran en) (fe_most en)
      (fe_own en) /\
    (forall b, In b Lam -> ~ In b Dk -> In b Lam2) /\ (forall b, In b Lam2 -> In b Lam) /\
    (forall b, In b (ablocks B ly S) -> ~ In b (ablocks B ly2 S2) ->
       exists a k0, In (a, k0) Dk /\ b = (a - cf_head, k0 + cf_head))).
  { destruct HXK as [(Ex & EDk) | (Ex & Hkx & EDk)].
    - (* fuzz_free (NULL) *)
      subst Dk. rewrite Ex, Z.eqb_refl in HFX.
      destruct HKK as [(_ & EHp & Eab & HLED2) | (Hx0 & _)]; [|exfalso; exact (Hx0 Ex)].
      exists Lam. rewrite app_nil_r. split; [|split; [exact HLED2|]].
      + exact (pfk_acct_null B FX en ly S Hp W mem Fd (Fr ++ fn_own nd) Lam ly2 S2 Hp2 W2 mem2 HAC HFX HROOM2 Eab HLED2).
      + split; [intros b Hb _; exact Hb|]. split; [intros b Hb; exact Hb|].
        intros b Hb Hn. rewrite Eab in Hn. contradiction.
    - (* the key's block *)
      subst Dk. pose proof Ex as Ex'. apply Z.eqb_neq in Ex'. rewrite Ex' in HFX.
      destruct HKK as [(Hx0 & _) | (_ & EHp & Eab & l1 & l2 & ELam & HLED2)]; [exfalso; exact (Ex Hx0)|].
      exists (l1 ++ l2). split; [|split; [exact HLED2|]].
      + exact (pfk_acct_free B FX en ly S Hp W mem Fd (x, kx) (Fr ++ fn_own nd) Lam ly2 S2 Hp2 W2 mem2 l1 l2 HAC HFX
          HROOM2 ELam Eab HLED2).
      + split.
        { intros b Hb Hn. rewrite ELam in Hb. apply in_app_or in Hb. apply in_or_app.
          destruct Hb as [Hb | [<- | Hb]]; [left; exact Hb | exfalso; apply Hn; left; reflexivity | right; exact Hb]. }
        split.
        { intros b Hb. rewrite ELam. apply in_app_or in Hb. apply in_or_app.
          destruct Hb as [Hb | Hb]; [left; exact Hb | right; right; exact Hb]. }
        intros b Hb Hn. destruct Eab as (b1 & b2 & Eb1 & Eb2). rewrite Eb1 in Hb. rewrite Eb2 in Hn.
        apply in_app_or in Hb. destruct Hb as [Hb | [<- | Hb]].
        * exfalso. apply Hn. apply in_or_app. left. exact Hb.
        * exists x, kx. split; [left; reflexivity | reflexivity].
        * exfalso. apply Hn. apply in_or_app. right. exact Hb. }
  destruct POST as (Lam2 & HAC2 & HLED2 & HL2a & HL2b & HAB).
  (* ---- what the call kept ---- *)
  pose proof (ajxR_ar HJ) as HARc.
  replace (fe_sp0 en + fe_d en + (-96 - fe_d en) + 0) with (fe_sp0 en - 96) in HJc by lia.
  assert (HFRc : pf_frameR SK B ARx Pm (wle' SEGS RZ_cf) en ly S Hp W regsc mem mdc k).
  { apply ((pfa_frame_sameR SK B ARx Pm (wle' SEGS RZ_cf)) en ly S Hp W regs regsc mem md mdc k HFR HJ); assumption. }
  destruct (pfk_pres_vlregs en i regsc regs2 HP2 HVRc HLRc) as (HVR2 & HLR2 & E22 & E32' & E42' & E272').
  assert (Esp2 : spZ regs2 = spZ regsc) by (unfold spZ; rewrite E22; reflexivity).
  assert (HSINK : ~ YI16.sink_open_fp FP1).
  { unfold FP1. destruct (x =? 0) eqn:Ex0.
    - exact (sink_closed_ablocks_fp [] (Forall_nil _)).
    - apply sink_closed_ablocks_fp. constructor; [|constructor]. cbn [fst].
      destruct HXK as [(Ex & _) | (_ & Hkx & _)]; [apply Z.eqb_neq in Ex0; contradiction|].
      destruct ((pfa_lam_blk B ARx LAWS) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HAR HLED Hkx) as (_ & Hx4 & _). change (@cf_head CP) with 16 in *.
      change (@cf_head CP) with 16. lia. }
  assert (HFPblk : forall y, inFP FP1 y -> exists b m, In (b, m) (ablocks B ly S) /\ b <= y < b + req_size m).
  { intros y Hy. destruct (HFPD y Hy) as (a' & k' & HinDk & Hr).
    destruct ((pfa_lam_blk B ARx LAWS) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HAR HLED (HDkL _ HinDk)) as (_ & _ & _ & _ & Hab & _). change (@cf_head CP) with 16 in *.
    exists (a' - 16), (k' + 16). split; [exact Hab | exact Hr]. }
  (* a harness block of Lam that is not the key's: its user bytes miss FP1 *)
  assert (HNFP : forall a0 k0 y, In (a0, k0) Lam -> ~ In (a0, k0) Dk -> a0 <= y < a0 + k0 -> ~ inFP FP1 y).
  { intros a0 k0 y Hin Hn Hy Hfp. destruct (HFPD y Hfp) as (a' & k' & HinDk & Hr).
    assert (Hne : (a0, k0) <> (a', k')) by (intros Ee; rewrite Ee in Hn; exact (Hn HinDk)).
    exact ((pfa_hb_apart B ARx LAWS) ly S Hp W mem md Lam _ _ _ _ _ _ a0 k0 a' k' y HAR HLED Hin (HDkL _ HinDk) Hne Hy Hr). }
  pose proof (pfk_frameR SK B ARx pal_pst_ro Pm CTX0 PB FX (wle' SEGS RZ_cf) en ly S Hp W regsc mem mdc k (STK_fuzz_free + 0) FP1
    ly2 S2 Hp2 W2 regs2 mem2 md2 k1 HPRE HFRc HJc HJ2 HSINK Esp2 E32' E42' E272' (fun h => PCALL _ _ HMN2 h)) as HFR2.
  split; [exact En|]. split; [exact Hi|]. split; [exact HFR2|].
  split; [exact HVR2|]. split; [exact HLR2|].
  exists (Fd ++ Dk), Lam2, Dr, Fr.
  split; [exact HAC2|].
  split.
  { apply (pfk_vnodeR SK B ARx LAWS VISF (wle' SEGS RZ_cf) en nd ly S Hp W mem mdc Lam ly2 S2 Hp2 W2 mem2 md2 Lam2 (STK_fuzz_free + 0)
      (fe_sp0 en - 96) FP1 k1 (fe_peak en) (fe_cnt en) (fe_fail en) (fe_ran en) (fe_most en) (fe_own en)
      (fe_peak en) (fe_cnt en) (fe_fail en) (fe_ran en) (fe_most en) (fe_own en) HVN HARc HLED HJc HLED2).
    - intros y Hy. destruct (HFPD y Hy) as (a' & k' & HinDk & Hr).
      exact ((pfa_v_apart B ARx LAWS) en nd ly S Hp W mem md Lam _ _ _ _ _ _ a' k' y HVN HAR HLED (HDkL _ HinDk) (HDkD _ HinDk) Hr).
    - intros b Hb Hnb. destruct (HAB b Hb Hnb) as (a & k0 & HinDk & ->).
      exists a, k0. split; [exact (HDkD _ HinDk)|]. split; [exact (HDkL _ HinDk) | reflexivity].
    - intros a0 k0 Hin Hn. apply HL2a; [exact Hin|]. intros H1. exact (Hn (HDkD _ H1)).
    - intros a0 k0 Hin. exact (HL2b _ Hin).
    - exact HFPblk. }
  split; [rewrite <- app_assoc; exact HPD|].
  (* the slots i + 1 .. n - 1 *)
  apply (pfk_itemsR SK B ARx LAWS (wle' SEGS RZ_cf) d' ly S Hp W mem mdc Lam ly2 S2 Hp2 W2 mem2 md2 Lam2 (STK_fuzz_free + 0) (fe_sp0 en - 96)
    FP1 k1 (fe_peak en) (fe_cnt en) (fe_fail en) (fe_ran en) (fe_most en) (fe_own en) (fe_peak en) (fe_cnt en)
    (fe_fail en) (fe_ran en) (fe_most en) (fe_own en) _ _ _ _ Dr Fr HARc HLED HJc HLED2 HIT).
  + intros y Hy. unfold pf_ofoot in Hy. rewrite Z2Nat.id in Hy by lia.
    destruct Hy as [Hy | [(Hks & Hy) | ((bx & bk) & Hb & Hh)]].
    * assert (HkDk : ~ In (fn_kids nd, kk) Dk) by exact (HownDk _ HkOwn).
      split; [exact (HNFP _ _ y HkLam HkDk ltac:(lia))|].
      exists (fn_kids nd), kk. split; [exact HkLam|]. split; [exact (HL2a _ HkLam HkDk) | lia].
    * assert (HyDk : ~ In (fn_keys nd, ky) Dk) by exact (HownDk _ HyOwn).
      split; [exact (HNFP _ _ y HyLam HyDk ltac:(lia))|].
      exists (fn_keys nd), ky. split; [exact HyLam|]. split; [exact (HL2a _ HyLam HyDk) | lia].
    * unfold pj_holdsR in Hh. cbn [fst snd] in Hh.
      pose proof (pf_oitemsR_lblk SEGS _ _ _ _ _ _ _ _ _ HIT bx bk Hb) as HbL. unfold prh_lin in HbL.
      split; [exact (HNFP _ _ y HbL (HDrDk _ Hb) Hh)|].
      exists bx, bk. split; [exact HbL|]. split; [exact (HL2a _ HbL (HDrDk _ Hb)) | exact Hh].
  + intros x0 k0 Hin. pose proof (pf_oitemsR_lblk SEGS _ _ _ _ _ _ _ _ _ HIT x0 k0 Hin) as HbL. unfold prh_lin in HbL.
    exact (HL2a _ HbL (HDrDk _ Hin)).
Qed.

End e.
End d.

Print Assumptions pf_seg_LC.
Print Assumptions pf_seg_LK.
(* the Section hypotheses each segment lemma takes as premises *)
About pf_seg_LK.
About pf_seg_LC.
