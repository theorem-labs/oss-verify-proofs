(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: lib/A/RPgCheckStr.v at 77f59d02b01 (the engine run from a fresh entry state and
   its re-seat at a fixed pc) for the value dispatch and the Int arm of reac-pw/fuzz_role's image-A segment M02
   (0x82318 .. 0x823e0). *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgM02KeyI.v at 7e8cf15c304 (the run / branch
   / exit pattern of a value dispatch, the entry state re-seated once the value entry's address is formed) and
   proofs/reac-pw/fuzz_role/lib/A/RPgM02KeyBase.v at 7e8cf15c304 (m2k_ent_type_slice, m2k_ent_size_slice,
   m2k_ent_word_slice) for reac-pw/fuzz_headamp image A: the m2i_ / m2k_ prefixes are renamed hvd_, every address
   is headamp's own, role's two arms and its MAL exit are replaced by headamp's Bool and Int arms with their five
   exits, and the cuts are lib/A/HPgSegM.v's and lib/A/HPgM3dBase.v's. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/A/HPgM3dDisp.v, with its module names and addresses changed; 1442 of its 1596 lines of code are new or changed and 516 lines of the source are left out. *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; every address measured on the unstripped twin
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff, the same loaded bytes except .note.gnu.build-id): the dispatch step from cut VAL of the
   piece value of the walk of LLVMFuzzerTestOneInput, lib/AU/HPgM3dBaseU.v hvu_piece_disp_stmt
   (VAL 0x83490 -> FA 0x83578 / TAIL 0x83694 / CELL 0x836e4 / RF 0x836a0). Proves no function
   (kind: segment lemma).

   THE CODE. 0x83490 .. 0x8349c: the two UBSan checks of &pp->ent[v] (the index below 33 and the pointer sum
   below 2 ^ 64), both to `unimp` 0x83a14; 0x834a0 .. 0x834b8: a0 := &ent[v], its instrumented check and
   `lw a1,0(a0)` = ent[v].type; 0x834bc .. 0x834d4: the three type tests (6 -> the Float arm, 4 -> the Int arm,
   not 2 -> the refusal fold); 0x834d8 .. 0x83520: the Bool arm (the size and body checks, the size test and
   `snez s2`); 0x83524 .. 0x83574: the Int arm (the same with `sd a6,0x90(s1)` and the range test against 256).

   THE RUNS. A run of the kit's engine decides an instrumented check by itself only where the checked address is
   a register of its entry state (lib/Reusable/YCbn.v covered: the address must be an atom plus a ground offset),
   so the lane is a chain of eight block lemmas, each entered at a pc where the next check's address is in a
   register: hvu_q1 (0x83490 -> 0x834a8), hvu_q2 (0x834a8 -> the four arms), hvu_q3 / hvu_q4 / hvu_q5 (the Bool
   arm), hvu_q6 / hvu_q7 / hvu_q8 (the Int arm). Every shadow byte the lane reads is a granule of the first block
   (pp, 19744 bytes, a multiple of 8), so each check's slow block is never entered. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YN0d YA0d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Cursor Model Layout Accessors.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec HPgM3dVal.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgImgB HPgSeg HPgSegM HPgM3dBaseU.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require HPgSteps HPgMem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ================================ the facts and the shadow entries ================================ *)
(* atom 9 is s1 = R, atom 27 is s11 = the runtime's shadow offset, atom 10 is a0, atom 11 is a1 *)
Definition hvu_facts (ns : list nat) : facts :=
mkFacts ((9%nat, mkAF (2 ^ 46) (2 ^ 47) 4) :: (27%nat, mkAF SHADOW_OFF SHADOW_OFF 0)
         :: map (fun n => (n, mkAF 4096 0x7fffff800000 0)) ns) [] [].

Lemma hvu_facts_ok0 : forall E R, bv_unsigned (ew E 9) = R -> 2 ^ 46 <= R <= 2 ^ 47 -> R mod 16 = 0 ->
bv_unsigned (ew E 27) = SHADOW_OFF -> facts_ok E (hvu_facts []).
Proof.
intros E R H9 HR Hal H27. split; [|split; [exact I | exact I]].
cbn [hvu_facts f_atoms atoms_ok map]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite H9, H27. change (2 ^ 4) with 16. change (2 ^ 0) with 1.
repeat split; try lia. all: try apply Z.mod_1_r.
Qed.

Lemma hvu_facts_ok1 : forall E R (n : nat) a,
bv_unsigned (ew E 9) = R -> 2 ^ 46 <= R <= 2 ^ 47 -> R mod 16 = 0 ->
bv_unsigned (ew E 27) = SHADOW_OFF ->
bv_unsigned (ew E n) = a -> 4096 <= a <= 0x7fffff800000 -> facts_ok E (hvu_facts [n]).
Proof.
intros E R n a H9 HR Hal H27 Hn Ha. split; [|split; [exact I | exact I]].
cbn [hvu_facts f_atoms atoms_ok map]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite H9, H27, Hn. change (2 ^ 4) with 16. change (2 ^ 0) with 1.
repeat split; try lia. all: try apply Z.mod_1_r.
Qed.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

(* one instrumented check, over the atom n that holds its address *)
Lemma hvu_sh1 : forall (W : world rsegs) mem E (n : nat) a len,
U E HVU_Bx = SHADOW_OFF -> U E (SOff n 0) = a ->
range_addressable (aview rsegs (w_H W) mem) SHADOW_OFF a len -> 0 <= len ->
(a + len <= kLowShadowBeg \/ kHighMemBeg <= a) -> 0 <= a -> a + len <= 2 ^ 47 ->
sh_ok rsegs HVU_Bx [mkSHE n 0 len] E (mrestrict (w_H W) mem).
Proof.
intros W mem E n a len HB Hn Hra Hlen Happ Ha0 Ha1. apply Forall_cons; [|apply Forall_nil].
apply (YCbq.shent_ok_of_range rsegs (w_H W) mem E HVU_Bx n a len a 0 len Hra HB Hn ltac:(lia) ltac:(lia)).
intros x Hx. cbn [Z.min Z.max] in Hx. unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
Qed.

End s.

(* the write obligation: read-only regions, and the real frame (atom 9 = R) whose write window lies in the
   journal's stack window [sp0 - STK, sp0) *)
Ltac hvu_awr :=
idtac; lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own);
repeat first
[ apply awr_ok_nil
| (apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|])
| lazymatch goal with E9 : bv_unsigned (ew E 9) = ?R |- _ =>
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (R - sp0));
  [reflexivity | rewrite E9; lia | cbn [YP09.r_wlo YP09.r_whi]; lia | cbn [YP09.r_wlo YP09.r_whi]; lia |] end ]
end.

(* A run that decides an instrumented check gives its token a fresh atom (34 and up, since the entry states
   below use the atoms 0 .. 33). The symbolic values of the entry state do not mention those atoms, so their
   meaning is the entry environment's. *)
Lemma hvu_U_ewset : forall E (j : nat) w (x : sv),
sv_atoms_lt 34 x = true -> (34 <= j)%nat -> U (ewset E j w) x = U E x.
Proof.
intros E j w x Hx Hj. apply (U_agree 34 E (ewset E j w) x); [|exact Hx].
eapply env_agree_le; [|apply env_agree_ewset]. lia.
Qed.

Ltac hvu_unext H :=
rewrite !denot_lit_U in H;
rewrite !hvu_U_ewset in H by (first [lia | (vm_compute; reflexivity)]).
Ltac hvu_unextg :=
rewrite !denot_lit_U;
rewrite !hvu_U_ewset by (first [lia | (vm_compute; reflexivity)]).

(* the kept registers and the block post of a run that allocated fresh atoms: the entry environment's
   agreement is chained through the run's ewset / havoc steps *)
Ltac hvu_keptx kept :=
lazymatch goal with HS : st_ok _ ?E' ?ss' (restrict _ ?ms), HAE : env_agree 32 (Ereg ?rg ?ex0) _ |- _ =>
  intros r Hr; exact (YI04.regs_kept_of_st_ok rsegs E' ss' (restrict _ ms) rg ex0 kept HS
    ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity) r Hr) end.
Ltac hvu_post0x B kept :=
lazymatch goal with HS : st_ok _ _ _ (restrict _ ?ms), HM : ms_mem ?ms = _,
  HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
  rewrite HM in HJ;
  eapply (hvu_post0_intro B); [exact HS | reflexivity | reflexivity | exact HM | exact HJ | hvu_io
                              | hvu_keptx kept | ] end.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.

(* ================================ q1: 0x83490 -> 0x834a8 ================================
   `li a0,33; bgeu s2,a0 -> unimp; ld a0,0xf0(s1); bltu a0,s8 -> unimp; ld a0,0xf8(s1); add a0,a0,s8`.
   The two UBSan traps are not taken: the entry index is at most 32 and the entry's address is below 2 ^ 64. *)
Definition hvu_q1_kept : list (bv 5) :=
map (Z_to_bv 5) [1; 2; 3; 4; 5; 6; 7; 8; 9; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27;
  28; 29; 30; 31].
Definition hvu_q1_R : YP09.region := YP09.mkRegion (Some 9%nat) 0xf0 0x100 0 0
  [YP09.mkChunk 0xf0 (CVal 8 (SOff 33 0)); YP09.mkChunk 0xf8 (CVal 8 (SOff 34 0))].
Definition hvu_q1_ss0 : sstate := mkSS HQU_VAL sr_atoms [hvu_q1_R] None (mkFacts [] [] []).
Definition hvu_q1_extra (vnot vb : Z) : list word :=
  [Z_to_bv 64 HPgSteps.SBr; Z_to_bv 64 vnot; Z_to_bv 64 vb].

Lemma hvu_q1 : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
(R i o vb : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs (Z_to_bv 5 9) = w64 R -> getr regs (Z_to_bv 5 18) = w64 i -> getr regs (Z_to_bv 5 24) = w64 o ->
0 <= R -> R + 0x100 <= 2 ^ 64 -> 0 <= i <= 32 -> 0 <= o -> 0 <= vb -> vb + o + 16 <= 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xf0) 8 (hqu_not vb mod 2 ^ 64) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xf8) 8 (vb mod 2 ^ 64) ->
SRr rsegs W (cfg_at rsegs HQU_VAL regs memc mdc)
(hvu_post0 B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs 0x834a8 hvu_q1_kept
  (fun regs2 => getr regs2 (Z_to_bv 5 10) = w64 (vb + o))).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R i o vb HJ H9 H18 H24
  HR0 HR1 Hi Ho Hvb Hsum Vf0 Vf8.
pose proof HPgSteps.img_wx as Hwx. pose proof HPgSteps.img_segs_low as Hsegs.
pose proof (AR_laws_ok rsegs B) as LAWS.
rewrite (hqu_not_mod vb ltac:(lia)) in Vf0.
rewrite (Z.mod_small vb (2 ^ 64)) in Vf8 by lia.
remember (hvu_q1_extra (2 ^ 64 - 1 - vb) vb) as ex eqn:Hex.
assert (EA : forall (m : nat) (r : bv 5), Z.of_nat m = bv_unsigned r -> ew (Ereg regs ex) m = getr regs r)
  by (intros m r Hm; exact (ew_Ereg_nat regs _ m r Hm)).
assert (E9 : ew (Ereg regs ex) 9 = Z_to_bv 64 R) by (rewrite (EA 9%nat (Z_to_bv 5 9) eq_refl); exact H9).
assert (E18 : ew (Ereg regs ex) 18 = Z_to_bv 64 i) by (rewrite (EA 18%nat (Z_to_bv 5 18) eq_refl); exact H18).
assert (E24 : ew (Ereg regs ex) 24 = Z_to_bv 64 o) by (rewrite (EA 24%nat (Z_to_bv 5 24) eq_refl); exact H24).
assert (E33 : ew (Ereg regs ex) 33 = Z_to_bv 64 (2 ^ 64 - 1 - vb)) by (subst ex; exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew (Ereg regs ex) 34 = Z_to_bv 64 vb) by (subst ex; exact (ew_Ereg_extra regs _ 2)).
assert (HS : st_ok rsegs (Ereg regs ex) hvu_q1_ss0
  (restrict (w_H W) (mkst regs (Z_to_bv 64 HQU_VAL) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold hvu_q1_ss0. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    apply (HPgMem.hm_ro_region rsegs _ (w_H W) memc 9 R); [rewrite E9; apply unsigned_lit_small; lia | lia | lia |].
    constructor; [|constructor; [|constructor]].
    + exact (hvu_slot_chunk _ _ _ R 0xf0 (2 ^ 64 - 1 - vb) 33 E33 ltac:(rewrite Z.mod_small by lia; exact Vf0)).
    + exact (hvu_slot_chunk _ _ _ R 0xf8 vb 34 E34 ltac:(rewrite Z.mod_small by lia; exact Vf8)).
  - cbn. tauto.
  - split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. exact I. }
assert (SHOK : sh_ok rsegs HPgSteps.RTBx [] (Ereg regs ex) (mrestrict (w_H W) memc)) by constructor.
remember (Ereg regs ex) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs ex) E) by (subst E; apply env_agree_refl).
clear HE EA Hex.
unfold cfg_at. change (w64 HQU_VAL) with (Z_to_bv 64 HQU_VAL).
(* 0x83490, stop at the `bgeu` *)
hvu_run HPgSteps.RTBspan awr_ok_tac. hvu_mem.
hvu_branch HPgSteps.RTBspan Hc1.
all: rewrite !hvu_denot0, E18 in Hc1.
all: cbn [sv_denot] in Hc1.
all: rewrite YO0c.branch_geu, !unsigned_lit_small in Hc1 by lia.
- (* taken: 33 <= i, impossible *)
  exfalso. apply negb_true_iff, Z.ltb_ge in Hc1. lia.
- (* not taken: `ld a0,0xf0(s1)`, stop at the `bltu` *)
  hvu_run_to HPgSteps.RTBspan awr_ok_tac 0x8349c. hvu_mem.
  hvu_branch HPgSteps.RTBspan Hc2.
  all: rewrite !hvu_denot0, E24, E33 in Hc2.
  all: rewrite YO0c.branch_ltu, !unsigned_lit_small in Hc2 by lia.
  + (* taken: the pointer sum overflows, impossible *)
    exfalso. apply Z.ltb_lt in Hc2. lia.
  + (* not taken: `ld a0,0xf8(s1); add a0,a0,s8` *)
    hvu_run_to HPgSteps.RTBspan awr_ok_tac 0x834a8. hvu_mem.
    apply SRr_ret. hvu_post0_tac B hvu_q1_kept.
    lazymatch goal with HS : st_ok _ ?E' ?ss' (restrict _ ?ms) |- _ =>
      rewrite !(st_ok_restrict_reg rsegs _ E' ss' ms _ HS) end.
    hvu_sv. rewrite denot_lit_U. unfold w64. f_equal.
    rewrite U_SAlu. cbn [zalu_raw].
    rewrite (U_atom E 34 vb E34 ltac:(lia)), (U_atom E 24 o E24 ltac:(lia)).
    unfold zcanon, M64. rewrite Z.mod_small by lia. lia.
Qed.


(* ================================ q2a: 0x834a8 -> 0x834c0 ================================
   the instrumented check of &ent[v] (covered by the shadow entry over a0), `lw a1,0(a0)` = ent[v].type and
   `li a2,6`. The check's slow block 0x837ac is not entered. *)
Definition hvu_q2a_kept : list (bv 5) :=
map (Z_to_bv 5) [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28;
  29; 30; 31].
Definition hvu_q2a_ent : YP09.region :=
  YP09.mkRegion (Some 10%nat) 0 16 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 33 0))].
Definition hvu_q2a_ss0 : sstate :=
  mkSS 0x834a8 sr_atoms [hvu_q2a_ent] None (hvu_facts [10%nat]).
Definition hvu_q2a_extra (ty : Z) : list word := [Z_to_bv 64 HPgSteps.SBr; Z_to_bv 64 ty].

Lemma hvu_q2a : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
(R A ty : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs (Z_to_bv 5 9) = w64 R -> getr regs (Z_to_bv 5 10) = w64 A ->
getr regs (Z_to_bv 5 27) = w64 SHADOW_OFF ->
2 ^ 46 <= R <= 2 ^ 47 -> R mod 16 = 0 ->
4096 <= A -> A + 16 <= 0x7fffff800000 -> 0 <= ty < 2 ^ 32 ->
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF A 16 ->
(A + 16 <= kLowShadowBeg \/ kHighMemBeg <= A) ->
val_mem rsegs (mrestrict (w_H W) memc) A 4 ty ->
SRr rsegs W (cfg_at rsegs 0x834a8 regs memc mdc)
(hvu_post0 B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs 0x834c0 hvu_q2a_kept
  (fun regs2 => getr regs2 (Z_to_bv 5 11) = w64 (hvm_sx ty) /\ getr regs2 (Z_to_bv 5 12) = w64 6)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R A ty HJ H9 H10 H27
  HR Hal HA0 HA1 Hty Hra Happ VA.
pose proof HPgSteps.img_wx as Hwx. pose proof HPgSteps.img_segs_low as Hsegs.
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof (hvm_sx_range ty Hty) as Hsx.
remember (hvu_q2a_extra ty) as ex eqn:Hex.
assert (EA : forall (m : nat) (r : bv 5), Z.of_nat m = bv_unsigned r -> ew (Ereg regs ex) m = getr regs r)
  by (intros m r Hm; exact (ew_Ereg_nat regs _ m r Hm)).
assert (E9 : ew (Ereg regs ex) 9 = Z_to_bv 64 R) by (rewrite (EA 9%nat (Z_to_bv 5 9) eq_refl); exact H9).
assert (E10 : ew (Ereg regs ex) 10 = Z_to_bv 64 A) by (rewrite (EA 10%nat (Z_to_bv 5 10) eq_refl); exact H10).
assert (E27 : ew (Ereg regs ex) 27 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite (EA 27%nat (Z_to_bv 5 27) eq_refl); exact H27).
assert (E33 : ew (Ereg regs ex) 33 = Z_to_bv 64 ty) by (subst ex; exact (ew_Ereg_extra regs _ 1)).
assert (HS : st_ok rsegs (Ereg regs ex) hvu_q2a_ss0
  (restrict (w_H W) (mkst regs (Z_to_bv 64 0x834a8) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold hvu_q2a_ss0. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    apply (HPgMem.hm_ro_region rsegs _ (w_H W) memc 10 A);
      [rewrite E10; apply unsigned_lit_small; lia | lia | lia |].
    constructor; [|constructor].
    eapply (chunk_ok_val rsegs _ _ A 0 4 (SOff 33 0) ty);
      [rewrite hvu_denot0, E33; reflexivity | lia | cbn; lia | rewrite Z.add_0_r; exact VA].
  - cbn. tauto.
  - exact (hvu_facts_ok1 _ R 10 A ltac:(rewrite E9; apply unsigned_lit_small; lia) ltac:(lia) Hal
            ltac:(rewrite E27; apply unsigned_lit_small; unfold SHADOW_OFF; lia)
            ltac:(rewrite E10; apply unsigned_lit_small; lia) ltac:(lia)). }
assert (SHOK : sh_ok rsegs HVU_Bx [mkSHE 10 0 16] (Ereg regs ex) (mrestrict (w_H W) memc)).
{ apply (hvu_sh1 W memc _ 10 A 16);
  [ unfold HVU_Bx; rewrite (U_atom _ 27 SHADOW_OFF E27 ltac:(unfold SHADOW_OFF; lia)); reflexivity
  | rewrite (U_atom _ 10 A E10 ltac:(lia)); reflexivity | exact Hra | lia | exact Happ | lia | lia ]. }
remember (Ereg regs ex) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs ex) E) by (subst E; apply env_agree_refl).
clear HE EA Hex.
assert (Uty : U E (SExt true 32 (SOff 33 0)) = hvm_sx ty) by (apply hvu_U_sext32; [exact E33 | lia]).
unfold cfg_at. change (w64 0x834a8) with (Z_to_bv 64 0x834a8).
hvu_run_to HVU_Bspan awr_ok_tac 0x834c0. hvu_mem.
apply SRr_ret. hvu_post0x B hvu_q2a_kept.
lazymatch goal with HS : st_ok _ ?E' ?ss' (restrict _ ?ms) |- _ =>
  rewrite !(st_ok_restrict_reg rsegs _ E' ss' ms _ HS) end.
split.
- hvu_sv. exact (hvu_denot_of_U E _ _ Uty).
- hvu_sv. cbn [sv_denot]. reflexivity.
Qed.

(* ================================ q2b: 0x834c0 -> the four arms ================================
   `ld a3,0x100(s1)` and the three type tests: 6 -> FA 0x83578, 4 -> the Int arm (one instruction past its head,
   0x83528), 2 -> the Bool arm (0x834dc), anything else -> the refusal fold 0x836a0. *)
Definition hvu_q2b_kept : list (bv 5) :=
map (Z_to_bv 5) [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29;
  30; 31].
Definition hvu_q2b_R : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0x100 0x108 0 0 [YP09.mkChunk 0x100 (CVal 8 (SOff 33 0))].
Definition hvu_q2b_ss0 : sstate := mkSS 0x834c0 sr_atoms [hvu_q2b_R] None (mkFacts [] [] []).
Definition hvu_q2b_extra (vb4 : Z) : list word := [Z_to_bv 64 HPgSteps.SBr; Z_to_bv 64 vb4].

Lemma hvu_q2b : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
(R o sx vb4 : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs (Z_to_bv 5 9) = w64 R -> getr regs (Z_to_bv 5 11) = w64 sx ->
getr regs (Z_to_bv 5 12) = w64 6 -> getr regs (Z_to_bv 5 24) = w64 o ->
0 <= R -> R + 0x108 <= 2 ^ 64 -> 0 <= sx < 2 ^ 64 -> 0 <= o -> 0 <= vb4 -> vb4 + o < 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x100) 8 (vb4 mod 2 ^ 64) ->
SRr rsegs W (cfg_at rsegs 0x834c0 regs memc mdc)
(fun W2 c2 =>
 (sx = 6 /\ hvu_post0 B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HVU_FA hvu_q2b_kept
    (fun regs2 => getr regs2 (Z_to_bv 5 13) = w64 vb4) W2 c2) \/
 (sx = 4 /\ hvu_post0 B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs 0x83528 hvu_q2b_kept
    (fun regs2 => getr regs2 (Z_to_bv 5 11) = w64 (vb4 + o)) W2 c2) \/
 (sx = 2 /\ hvu_post0 B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs 0x834dc hvu_q2b_kept
    (fun regs2 => getr regs2 (Z_to_bv 5 11) = w64 (vb4 + o)) W2 c2) \/
 (sx <> 6 /\ sx <> 4 /\ sx <> 2 /\
  hvu_post0 B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HQU_RF hvu_q2b_kept
    (fun _ => True) W2 c2)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R o sx vb4 HJ H9 H11 H12 H24
  HR0 HR1 Hsx Ho Hvb4 Hsum V100.
pose proof HPgSteps.img_wx as Hwx. pose proof HPgSteps.img_segs_low as Hsegs.
pose proof (AR_laws_ok rsegs B) as LAWS.
rewrite (Z.mod_small vb4 (2 ^ 64)) in V100 by lia.
remember (hvu_q2b_extra vb4) as ex eqn:Hex.
assert (EA : forall (m : nat) (r : bv 5), Z.of_nat m = bv_unsigned r -> ew (Ereg regs ex) m = getr regs r)
  by (intros m r Hm; exact (ew_Ereg_nat regs _ m r Hm)).
assert (E9 : ew (Ereg regs ex) 9 = Z_to_bv 64 R) by (rewrite (EA 9%nat (Z_to_bv 5 9) eq_refl); exact H9).
assert (E11 : ew (Ereg regs ex) 11 = Z_to_bv 64 sx) by (rewrite (EA 11%nat (Z_to_bv 5 11) eq_refl); exact H11).
assert (E12 : ew (Ereg regs ex) 12 = Z_to_bv 64 6) by (rewrite (EA 12%nat (Z_to_bv 5 12) eq_refl); exact H12).
assert (E24 : ew (Ereg regs ex) 24 = Z_to_bv 64 o) by (rewrite (EA 24%nat (Z_to_bv 5 24) eq_refl); exact H24).
assert (E33 : ew (Ereg regs ex) 33 = Z_to_bv 64 vb4) by (subst ex; exact (ew_Ereg_extra regs _ 1)).
assert (HS : st_ok rsegs (Ereg regs ex) hvu_q2b_ss0
  (restrict (w_H W) (mkst regs (Z_to_bv 64 0x834c0) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold hvu_q2b_ss0. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    apply (HPgMem.hm_ro_region rsegs _ (w_H W) memc 9 R);
      [rewrite E9; apply unsigned_lit_small; lia | lia | lia |].
    constructor; [|constructor].
    exact (hvu_slot_chunk _ _ _ R 0x100 vb4 33 E33 ltac:(rewrite Z.mod_small by lia; exact V100)).
  - cbn. tauto.
  - split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. exact I. }
assert (SHOK : sh_ok rsegs HPgSteps.RTBx [] (Ereg regs ex) (mrestrict (w_H W) memc)) by constructor.
remember (Ereg regs ex) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs ex) E) by (subst E; apply env_agree_refl).
clear HE EA Hex.
unfold cfg_at. change (w64 0x834c0) with (Z_to_bv 64 0x834c0).
(* `ld a3,0x100(s1)`; stop at the first `beq` *)
hvu_run HPgSteps.RTBspan awr_ok_tac. hvu_mem.
hvu_branch HPgSteps.RTBspan Hc6.
all: rewrite !hvu_denot0, E11, E12 in Hc6.
all: rewrite YO0c.branch_eq, !unsigned_lit_small in Hc6 by lia.
- (* the Float arm *)
  hvu_run_to HPgSteps.RTBspan awr_ok_tac HVU_FA. hvu_mem.
  apply SRr_ret; left. split; [apply Z.eqb_eq in Hc6; exact Hc6|].
  hvu_post0_tac B hvu_q2b_kept.
  lazymatch goal with HS : st_ok _ ?E' ?ss' (restrict _ ?ms) |- _ =>
    rewrite !(st_ok_restrict_reg rsegs _ E' ss' ms _ HS) end.
  hvu_sv. rewrite hvu_denot0, E33. reflexivity.
- (* not 6 *)
  apply Z.eqb_neq in Hc6.
  hvu_run HPgSteps.RTBspan awr_ok_tac. hvu_mem.
  hvu_branch HPgSteps.RTBspan Hc4.
  all: rewrite !hvu_denot0, E11 in Hc4.
  all: cbn [sv_denot] in Hc4.
  all: rewrite YO0c.branch_eq, !unsigned_lit_small in Hc4 by lia.
  + (* the Int arm *)
    hvu_run_to HPgSteps.RTBspan awr_ok_tac 0x83528. hvu_mem.
    apply SRr_ret; right; left. split; [apply Z.eqb_eq in Hc4; exact Hc4|].
    hvu_post0_tac B hvu_q2b_kept.
    lazymatch goal with HS : st_ok _ ?E' ?ss' (restrict _ ?ms) |- _ =>
      rewrite !(st_ok_restrict_reg rsegs _ E' ss' ms _ HS) end.
    hvu_sv. rewrite denot_lit_U. unfold w64. f_equal.
    rewrite U_SAlu. cbn [zalu_raw].
    rewrite (U_atom E 33 vb4 E33 ltac:(lia)), (U_atom E 24 o E24 ltac:(lia)).
    unfold zcanon, M64. rewrite Z.mod_small by lia. lia.
  + (* not 4 *)
    apply Z.eqb_neq in Hc4.
    hvu_run HPgSteps.RTBspan awr_ok_tac. hvu_mem.
    hvu_branch HPgSteps.RTBspan Hc2.
    all: rewrite !hvu_denot0, E11 in Hc2.
    all: cbn [sv_denot] in Hc2.
    all: rewrite YO0c.branch_ne, !unsigned_lit_small in Hc2 by lia.
    * (* not 2: the refusal fold *)
      hvu_run_to HPgSteps.RTBspan awr_ok_tac HQU_RF. hvu_mem.
      apply SRr_ret; right; right; right.
      split; [exact Hc6|]. split; [exact Hc4|].
      split; [apply negb_true_iff, Z.eqb_neq in Hc2; exact Hc2|].
      hvu_post0_tac B hvu_q2b_kept. exact I.
    * (* the Bool arm *)
      hvu_run_to HPgSteps.RTBspan awr_ok_tac 0x834dc. hvu_mem.
      apply SRr_ret; right; right; left.
      split; [apply negb_false_iff, Z.eqb_eq in Hc2; exact Hc2|].
      hvu_post0_tac B hvu_q2b_kept.
      lazymatch goal with HS : st_ok _ ?E' ?ss' (restrict _ ?ms) |- _ =>
        rewrite !(st_ok_restrict_reg rsegs _ E' ss' ms _ HS) end.
      hvu_sv. rewrite denot_lit_U. unfold w64. f_equal.
      rewrite U_SAlu. cbn [zalu_raw].
      rewrite (U_atom E 33 vb4 E33 ltac:(lia)), (U_atom E 24 o E24 ltac:(lia)).
      unfold zcanon, M64. rewrite Z.mod_small by lia. lia.
Qed.

(* ================================ the Bool arm ================================ *)
(* q3a 0x834dc -> RF 0x836a0 / 0x834f8: the size check, `lw a0,4(a0)` and the size test *)
(* the slow block 0x837bc of this check writes a3 as well (`andi a3,a1,7`), so a3 is not kept *)
Definition hvu_q3a_kept : list (bv 5) :=
map (Z_to_bv 5) [1; 2; 3; 4; 5; 6; 7; 8; 9; 11; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28;
  29; 30; 31].
Definition hvu_q3a_ent : YP09.region :=
  YP09.mkRegion (Some 10%nat) 4 8 0 0 [YP09.mkChunk 4 (CVal 4 (SOff 33 0))].
Definition hvu_q3a_ss0 : sstate := mkSS 0x834dc sr_atoms [hvu_q3a_ent] None (hvu_facts [11%nat]).
Definition hvu_q3a_extra (sz : Z) : list word := [Z_to_bv 64 HPgSteps.SBr; Z_to_bv 64 sz].

Lemma hvu_q3a : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
(R A sz : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs (Z_to_bv 5 9) = w64 R -> getr regs (Z_to_bv 5 10) = w64 A ->
getr regs (Z_to_bv 5 11) = w64 (A + 4) -> getr regs (Z_to_bv 5 27) = w64 SHADOW_OFF ->
2 ^ 46 <= R <= 2 ^ 47 -> R mod 16 = 0 ->
4096 <= A -> A + 16 <= 0x7fffff800000 -> 0 <= sz <= 45 ->
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF (A + 4) 4 ->
(A + 16 <= kLowShadowBeg \/ kHighMemBeg <= A) ->
val_mem rsegs (mrestrict (w_H W) memc) (A + 4) 4 sz ->
SRr rsegs W (cfg_at rsegs 0x834dc regs memc mdc)
(fun W2 c2 =>
 (sz < 4 /\ hvu_post0 B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HQU_RF hvu_q3a_kept
    (fun _ => True) W2 c2) \/
 (4 <= sz /\ hvu_post0 B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs 0x834f8 hvu_q3a_kept
    (fun _ => True) W2 c2)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R A sz HJ H9 H10 H11 H27
  HR Hal HA0 HA1 Hsz Hra Happ VA.
pose proof HPgSteps.img_wx as Hwx. pose proof HPgSteps.img_segs_low as Hsegs.
pose proof (AR_laws_ok rsegs B) as LAWS.
remember (hvu_q3a_extra sz) as ex eqn:Hex.
assert (EA : forall (m : nat) (r : bv 5), Z.of_nat m = bv_unsigned r -> ew (Ereg regs ex) m = getr regs r)
  by (intros m r Hm; exact (ew_Ereg_nat regs _ m r Hm)).
assert (E9 : ew (Ereg regs ex) 9 = Z_to_bv 64 R) by (rewrite (EA 9%nat (Z_to_bv 5 9) eq_refl); exact H9).
assert (E10 : ew (Ereg regs ex) 10 = Z_to_bv 64 A) by (rewrite (EA 10%nat (Z_to_bv 5 10) eq_refl); exact H10).
assert (E11 : ew (Ereg regs ex) 11 = Z_to_bv 64 (A + 4))
  by (rewrite (EA 11%nat (Z_to_bv 5 11) eq_refl); exact H11).
assert (E27 : ew (Ereg regs ex) 27 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite (EA 27%nat (Z_to_bv 5 27) eq_refl); exact H27).
assert (E33 : ew (Ereg regs ex) 33 = Z_to_bv 64 sz) by (subst ex; exact (ew_Ereg_extra regs _ 1)).
assert (HS : st_ok rsegs (Ereg regs ex) hvu_q3a_ss0
  (restrict (w_H W) (mkst regs (Z_to_bv 64 0x834dc) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold hvu_q3a_ss0. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    apply (HPgMem.hm_ro_region rsegs _ (w_H W) memc 10 A);
      [rewrite E10; apply unsigned_lit_small; lia | lia | lia |].
    constructor; [|constructor].
    eapply (chunk_ok_val rsegs _ _ A 4 4 (SOff 33 0) sz);
      [rewrite hvu_denot0, E33; reflexivity | lia | cbn; lia | exact VA].
  - cbn. tauto.
  - exact (hvu_facts_ok1 _ R 11 (A + 4) ltac:(rewrite E9; apply unsigned_lit_small; lia) ltac:(lia) Hal
            ltac:(rewrite E27; apply unsigned_lit_small; unfold SHADOW_OFF; lia)
            ltac:(rewrite E11; apply unsigned_lit_small; lia) ltac:(lia)). }
assert (SHOK : sh_ok rsegs HVU_Bx [mkSHE 11 0 4] (Ereg regs ex) (mrestrict (w_H W) memc)).
{ apply (hvu_sh1 W memc _ 11 (A + 4) 4);
  [ unfold HVU_Bx; rewrite (U_atom _ 27 SHADOW_OFF E27 ltac:(unfold SHADOW_OFF; lia)); reflexivity
  | rewrite (U_atom _ 11 (A + 4) E11 ltac:(lia)); reflexivity | exact Hra | lia
  | destruct Happ as [Hp|Hp]; [left; lia | right; lia] | lia | lia ]. }
remember (Ereg regs ex) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs ex) E) by (subst E; apply env_agree_refl).
clear HE EA Hex.
assert (Usz : U E (SExt true 32 (SOff 33 0)) = sz)
  by (rewrite (hvu_U_sext32 E 33 sz E33 ltac:(lia)); apply hvm_sx_id; lia).
unfold cfg_at. change (w64 0x834dc) with (Z_to_bv 64 0x834dc).
hvu_run HVU_Bspan awr_ok_tac. hvu_mem.
hvu_branch HVU_Bspan Hc.
(* the engine's run allocated fresh atoms (34 and up) for the check's token: normalise the environment of the
   branch's operands back to the entry environment, whose atoms are all below 34 *)
all: hvu_unext Hc.
all: rewrite Usz, U_SLit in Hc.
all: change (zcanon 4) with 4 in Hc.
all: rewrite YO0c.branch_ltu, !unsigned_lit_small in Hc by lia.
- hvu_run_to HVU_Bspan awr_ok_tac HQU_RF. hvu_mem.
  apply SRr_ret; left. split; [apply Z.ltb_lt in Hc; exact Hc|].
  hvu_post0x B hvu_q3a_kept. exact I.
- hvu_run_to HVU_Bspan awr_ok_tac 0x834f8. hvu_mem.
  apply SRr_ret; right. split; [apply Z.ltb_ge in Hc; exact Hc|].
  hvu_post0x B hvu_q3a_kept. exact I.
Qed.

(* q3b 0x834f8 -> 0x83500: `ld a0,0xe0(s1); add a0,a0,s8` *)
Definition hvu_q3b_kept : list (bv 5) :=
map (Z_to_bv 5) [1; 2; 3; 4; 5; 6; 7; 8; 9; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27;
  28; 29; 30; 31].
Definition hvu_q3b_R : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0xe0 0xe8 0 0 [YP09.mkChunk 0xe0 (CVal 8 (SOff 33 0))].
Definition hvu_q3b_ss0 : sstate := mkSS 0x834f8 sr_atoms [hvu_q3b_R] None (mkFacts [] [] []).
Definition hvu_q3b_extra (vb8 : Z) : list word := [Z_to_bv 64 HPgSteps.SBr; Z_to_bv 64 vb8].

Lemma hvu_q3b : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
(R o vb8 : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs (Z_to_bv 5 9) = w64 R -> getr regs (Z_to_bv 5 24) = w64 o ->
0 <= R -> R + 0xe8 <= 2 ^ 64 -> 0 <= o -> 0 <= vb8 -> vb8 + o < 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xe0) 8 (vb8 mod 2 ^ 64) ->
SRr rsegs W (cfg_at rsegs 0x834f8 regs memc mdc)
(hvu_post0 B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs 0x83500 hvu_q3b_kept
  (fun regs2 => getr regs2 (Z_to_bv 5 10) = w64 (vb8 + o))).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R o vb8 HJ H9 H24
  HR0 HR1 Ho Hvb8 Hsum V.
pose proof HPgSteps.img_wx as Hwx. pose proof HPgSteps.img_segs_low as Hsegs.
pose proof (AR_laws_ok rsegs B) as LAWS.
rewrite (Z.mod_small vb8 (2 ^ 64)) in V by lia.
remember (hvu_q3b_extra vb8) as ex eqn:Hex.
assert (EA : forall (m : nat) (r : bv 5), Z.of_nat m = bv_unsigned r -> ew (Ereg regs ex) m = getr regs r)
  by (intros m r Hm; exact (ew_Ereg_nat regs _ m r Hm)).
assert (E9 : ew (Ereg regs ex) 9 = Z_to_bv 64 R) by (rewrite (EA 9%nat (Z_to_bv 5 9) eq_refl); exact H9).
assert (E24 : ew (Ereg regs ex) 24 = Z_to_bv 64 o) by (rewrite (EA 24%nat (Z_to_bv 5 24) eq_refl); exact H24).
assert (E33 : ew (Ereg regs ex) 33 = Z_to_bv 64 vb8) by (subst ex; exact (ew_Ereg_extra regs _ 1)).
assert (HS : st_ok rsegs (Ereg regs ex) hvu_q3b_ss0
  (restrict (w_H W) (mkst regs (Z_to_bv 64 0x834f8) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold hvu_q3b_ss0. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    apply (HPgMem.hm_ro_region rsegs _ (w_H W) memc 9 R);
      [rewrite E9; apply unsigned_lit_small; lia | lia | lia |].
    constructor; [|constructor].
    exact (hvu_slot_chunk _ _ _ R 0xe0 vb8 33 E33 ltac:(rewrite Z.mod_small by lia; exact V)).
  - cbn. tauto.
  - split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. exact I. }
assert (SHOK : sh_ok rsegs HPgSteps.RTBx [] (Ereg regs ex) (mrestrict (w_H W) memc)) by constructor.
remember (Ereg regs ex) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs ex) E) by (subst E; apply env_agree_refl).
clear HE EA Hex.
unfold cfg_at. change (w64 0x834f8) with (Z_to_bv 64 0x834f8).
hvu_run_to HPgSteps.RTBspan awr_ok_tac 0x83500. hvu_mem.
apply SRr_ret. hvu_post0_tac B hvu_q3b_kept.
lazymatch goal with HS : st_ok _ ?E' ?ss' (restrict _ ?ms) |- _ =>
  rewrite !(st_ok_restrict_reg rsegs _ E' ss' ms _ HS) end.
hvu_sv. rewrite denot_lit_U. unfold w64. f_equal.
rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom E 33 vb8 E33 ltac:(lia)), (U_atom E 24 o E24 ltac:(lia)).
unfold zcanon, M64. rewrite Z.mod_small by lia. lia.
Qed.

(* q4 0x83500 -> 0x83518: the body check and `ld a0,0xe8(s1); add s8,a0,s8` *)
Definition hvu_q4_kept : list (bv 5) :=
map (Z_to_bv 5) [1; 2; 3; 4; 5; 6; 7; 8; 9; 11; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 25; 26; 27; 28; 29;
  30; 31].
Definition hvu_q4_R : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0xe8 0xf0 0 0 [YP09.mkChunk 0xe8 (CVal 8 (SOff 33 0))].
Definition hvu_q4_ss0 : sstate := mkSS 0x83500 sr_atoms [hvu_q4_R] None (hvu_facts [10%nat]).
Definition hvu_q4_extra (vb8 : Z) : list word := [Z_to_bv 64 HPgSteps.SBr; Z_to_bv 64 vb8].

Lemma hvu_q4 : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
(R Ab o vb8 : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs (Z_to_bv 5 9) = w64 R -> getr regs (Z_to_bv 5 10) = w64 Ab ->
getr regs (Z_to_bv 5 24) = w64 o -> getr regs (Z_to_bv 5 27) = w64 SHADOW_OFF ->
2 ^ 46 <= R <= 2 ^ 47 -> R mod 16 = 0 -> R + 0xf0 <= 2 ^ 64 ->
4096 <= Ab -> Ab + 4 <= 0x7fffff800000 -> 0 <= o -> 0 <= vb8 -> vb8 + o < 2 ^ 64 ->
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF Ab 4 ->
(Ab + 4 <= kLowShadowBeg \/ kHighMemBeg <= Ab) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xe8) 8 (vb8 mod 2 ^ 64) ->
SRr rsegs W (cfg_at rsegs 0x83500 regs memc mdc)
(hvu_post0 B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs 0x83518 hvu_q4_kept
  (fun regs2 => getr regs2 (Z_to_bv 5 24) = w64 (vb8 + o))).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R Ab o vb8 HJ H9 H10 H24 H27
  HR Hal HR1 HA0 HA1 Ho Hvb8 Hsum Hra Happ V.
pose proof HPgSteps.img_wx as Hwx. pose proof HPgSteps.img_segs_low as Hsegs.
pose proof (AR_laws_ok rsegs B) as LAWS.
rewrite (Z.mod_small vb8 (2 ^ 64)) in V by lia.
remember (hvu_q4_extra vb8) as ex eqn:Hex.
assert (EA : forall (m : nat) (r : bv 5), Z.of_nat m = bv_unsigned r -> ew (Ereg regs ex) m = getr regs r)
  by (intros m r Hm; exact (ew_Ereg_nat regs _ m r Hm)).
assert (E9 : ew (Ereg regs ex) 9 = Z_to_bv 64 R) by (rewrite (EA 9%nat (Z_to_bv 5 9) eq_refl); exact H9).
assert (E10 : ew (Ereg regs ex) 10 = Z_to_bv 64 Ab) by (rewrite (EA 10%nat (Z_to_bv 5 10) eq_refl); exact H10).
assert (E24 : ew (Ereg regs ex) 24 = Z_to_bv 64 o) by (rewrite (EA 24%nat (Z_to_bv 5 24) eq_refl); exact H24).
assert (E27 : ew (Ereg regs ex) 27 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite (EA 27%nat (Z_to_bv 5 27) eq_refl); exact H27).
assert (E33 : ew (Ereg regs ex) 33 = Z_to_bv 64 vb8) by (subst ex; exact (ew_Ereg_extra regs _ 1)).
assert (HS : st_ok rsegs (Ereg regs ex) hvu_q4_ss0
  (restrict (w_H W) (mkst regs (Z_to_bv 64 0x83500) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold hvu_q4_ss0. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    apply (HPgMem.hm_ro_region rsegs _ (w_H W) memc 9 R);
      [rewrite E9; apply unsigned_lit_small; lia | lia | lia |].
    constructor; [|constructor].
    exact (hvu_slot_chunk _ _ _ R 0xe8 vb8 33 E33 ltac:(rewrite Z.mod_small by lia; exact V)).
  - cbn. tauto.
  - exact (hvu_facts_ok1 _ R 10 Ab ltac:(rewrite E9; apply unsigned_lit_small; lia) ltac:(lia) Hal
            ltac:(rewrite E27; apply unsigned_lit_small; unfold SHADOW_OFF; lia)
            ltac:(rewrite E10; apply unsigned_lit_small; lia) ltac:(lia)). }
assert (SHOK : sh_ok rsegs HVU_Bx [mkSHE 10 0 4] (Ereg regs ex) (mrestrict (w_H W) memc)).
{ apply (hvu_sh1 W memc _ 10 Ab 4);
  [ unfold HVU_Bx; rewrite (U_atom _ 27 SHADOW_OFF E27 ltac:(unfold SHADOW_OFF; lia)); reflexivity
  | rewrite (U_atom _ 10 Ab E10 ltac:(lia)); reflexivity | exact Hra | lia | exact Happ | lia | lia ]. }
remember (Ereg regs ex) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs ex) E) by (subst E; apply env_agree_refl).
clear HE EA Hex.
unfold cfg_at. change (w64 0x83500) with (Z_to_bv 64 0x83500).
hvu_run_to HVU_Bspan awr_ok_tac 0x83518. hvu_mem.
apply SRr_ret. hvu_post0x B hvu_q4_kept.
lazymatch goal with HS : st_ok _ ?E' ?ss' (restrict _ ?ms) |- _ =>
  rewrite !(st_ok_restrict_reg rsegs _ E' ss' ms _ HS) end.
hvu_sv. rewrite denot_lit_U. unfold w64. f_equal.
rewrite !hvu_U_ewset by (first [lia | (vm_compute; reflexivity)]).
rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom E 33 vb8 E33 ltac:(lia)), (U_atom E 24 o E24 ltac:(lia)).
unfold zcanon, M64. rewrite Z.mod_small by lia. lia.
Qed.

(* q5 0x83518 -> CELL 0x836e4: `lw a0,0(s8); snez s2,a0; j` *)
Definition hvu_q5_kept : list (bv 5) :=
map (Z_to_bv 5) [1; 2; 3; 4; 5; 6; 7; 8; 9; 11; 12; 13; 14; 15; 16; 17; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28;
  29; 30; 31].
Definition hvu_q5_R : YP09.region :=
  YP09.mkRegion (Some 24%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 33 0))].
Definition hvu_q5_ss0 : sstate := mkSS 0x83518 sr_atoms [hvu_q5_R] None (mkFacts [] [] []).
Definition hvu_q5_extra (bw : Z) : list word := [Z_to_bv 64 HPgSteps.SBr; Z_to_bv 64 bw].

Lemma hvu_q5 : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
(Ab bw : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs (Z_to_bv 5 24) = w64 Ab ->
0 <= Ab -> Ab + 4 <= 2 ^ 64 -> 0 <= bw < 2 ^ 32 ->
val_mem rsegs (mrestrict (w_H W) memc) Ab 4 bw ->
SRr rsegs W (cfg_at rsegs 0x83518 regs memc mdc)
(hvu_post0 B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HQU_CELL hvu_q5_kept
  (fun regs2 => getr regs2 (Z_to_bv 5 18) = w64 (if 0 <? hvm_sx bw then 1 else 0))).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Ab bw HJ H24 HA0 HA1 Hbw V.
pose proof HPgSteps.img_wx as Hwx. pose proof HPgSteps.img_segs_low as Hsegs.
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof (hvm_sx_range bw Hbw) as Hsx.
remember (hvu_q5_extra bw) as ex eqn:Hex.
assert (EA : forall (m : nat) (r : bv 5), Z.of_nat m = bv_unsigned r -> ew (Ereg regs ex) m = getr regs r)
  by (intros m r Hm; exact (ew_Ereg_nat regs _ m r Hm)).
assert (E24 : ew (Ereg regs ex) 24 = Z_to_bv 64 Ab) by (rewrite (EA 24%nat (Z_to_bv 5 24) eq_refl); exact H24).
assert (E33 : ew (Ereg regs ex) 33 = Z_to_bv 64 bw) by (subst ex; exact (ew_Ereg_extra regs _ 1)).
assert (HS : st_ok rsegs (Ereg regs ex) hvu_q5_ss0
  (restrict (w_H W) (mkst regs (Z_to_bv 64 0x83518) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold hvu_q5_ss0. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    apply (HPgMem.hm_ro_region rsegs _ (w_H W) memc 24 Ab);
      [rewrite E24; apply unsigned_lit_small; lia | lia | lia |].
    constructor; [|constructor].
    eapply (chunk_ok_val rsegs _ _ Ab 0 4 (SOff 33 0) bw);
      [rewrite hvu_denot0, E33; reflexivity | lia | cbn; lia | rewrite Z.add_0_r; exact V].
  - cbn. tauto.
  - split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. exact I. }
assert (SHOK : sh_ok rsegs HPgSteps.RTBx [] (Ereg regs ex) (mrestrict (w_H W) memc)) by constructor.
remember (Ereg regs ex) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs ex) E) by (subst E; apply env_agree_refl).
clear HE EA Hex.
assert (Ubw : U E (SExt true 32 (SOff 33 0)) = hvm_sx bw) by (apply hvu_U_sext32; [exact E33 | lia]).
unfold cfg_at. change (w64 0x83518) with (Z_to_bv 64 0x83518).
hvu_run_to HPgSteps.RTBspan awr_ok_tac HQU_CELL. hvu_mem.
apply SRr_ret. hvu_post0_tac B hvu_q5_kept.
lazymatch goal with HS : st_ok _ ?E' ?ss' (restrict _ ?ms) |- _ =>
  rewrite !(st_ok_restrict_reg rsegs _ E' ss' ms _ HS) end.
hvu_sv. rewrite denot_lit_U. unfold w64. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite Ubw, U_SLit.
change (zcanon 0) with 0.
destruct (0 <? hvm_sx bw); vm_compute; reflexivity.
Qed.

(* ================================ the Int arm ================================ *)
(* the bytes of an 8-byte chunk the engine holds after a store: the converse of hvu_slot_chunk *)
Lemma hvu_chunk8_val : forall E m base off v val,
sv_denot E v = Z_to_bv 64 val -> 0 <= val < 2 ^ 64 ->
YP09.chunk_ok rsegs E m base (YP09.mkChunk off (CVal 8 v)) ->
val_mem rsegs m (base + off) 8 val.
Proof.
intros E m base off v val Hv Hval H k Hk.
destruct (H (Z.of_nat k) ltac:(cbn; lia)) as (b & Hb1 & Hb2).
cbn [YP09.c_off YP09.c_val cbyte] in Hb1, Hb2.
injection Hb1 as <-.
rewrite Hb2. f_equal. unfold byte_of_word, YO0f.le_byte. rewrite Hv. apply bv_eq.
rewrite !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 64) with (2 ^ 64). change (bv_modulus 8) with 256.
change (8 * Z.of_nat 8) with 64. rewrite (Z.mod_small val (2 ^ 64)) by lia.
rewrite Z.mod_mod by lia. reflexivity.
Qed.

(* q6a 0x83528 -> RF 0x836a0 / 0x83544: the Int arm's size check and size test *)
(* the slow block 0x837cc writes a3 as well, so a3 is not kept *)
Definition hvu_q6a_kept : list (bv 5) :=
map (Z_to_bv 5) [1; 2; 3; 4; 5; 6; 7; 8; 9; 11; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28;
  29; 30; 31].
Definition hvu_q6a_ss0 : sstate := mkSS 0x83528 sr_atoms [hvu_q3a_ent] None (hvu_facts [11%nat]).

Lemma hvu_q6a : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
(R A sz : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs (Z_to_bv 5 9) = w64 R -> getr regs (Z_to_bv 5 10) = w64 A ->
getr regs (Z_to_bv 5 11) = w64 (A + 4) -> getr regs (Z_to_bv 5 27) = w64 SHADOW_OFF ->
2 ^ 46 <= R <= 2 ^ 47 -> R mod 16 = 0 ->
4096 <= A -> A + 16 <= 0x7fffff800000 -> 0 <= sz <= 45 ->
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF (A + 4) 4 ->
(A + 16 <= kLowShadowBeg \/ kHighMemBeg <= A) ->
val_mem rsegs (mrestrict (w_H W) memc) (A + 4) 4 sz ->
SRr rsegs W (cfg_at rsegs 0x83528 regs memc mdc)
(fun W2 c2 =>
 (sz < 4 /\ hvu_post0 B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HQU_RF hvu_q6a_kept
    (fun _ => True) W2 c2) \/
 (4 <= sz /\ hvu_post0 B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs 0x83544 hvu_q6a_kept
    (fun _ => True) W2 c2)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R A sz HJ H9 H10 H11 H27
  HR Hal HA0 HA1 Hsz Hra Happ VA.
pose proof HPgSteps.img_wx as Hwx. pose proof HPgSteps.img_segs_low as Hsegs.
pose proof (AR_laws_ok rsegs B) as LAWS.
remember (hvu_q3a_extra sz) as ex eqn:Hex.
assert (EA : forall (m : nat) (r : bv 5), Z.of_nat m = bv_unsigned r -> ew (Ereg regs ex) m = getr regs r)
  by (intros m r Hm; exact (ew_Ereg_nat regs _ m r Hm)).
assert (E9 : ew (Ereg regs ex) 9 = Z_to_bv 64 R) by (rewrite (EA 9%nat (Z_to_bv 5 9) eq_refl); exact H9).
assert (E10 : ew (Ereg regs ex) 10 = Z_to_bv 64 A) by (rewrite (EA 10%nat (Z_to_bv 5 10) eq_refl); exact H10).
assert (E11 : ew (Ereg regs ex) 11 = Z_to_bv 64 (A + 4))
  by (rewrite (EA 11%nat (Z_to_bv 5 11) eq_refl); exact H11).
assert (E27 : ew (Ereg regs ex) 27 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite (EA 27%nat (Z_to_bv 5 27) eq_refl); exact H27).
assert (E33 : ew (Ereg regs ex) 33 = Z_to_bv 64 sz) by (subst ex; exact (ew_Ereg_extra regs _ 1)).
assert (HS : st_ok rsegs (Ereg regs ex) hvu_q6a_ss0
  (restrict (w_H W) (mkst regs (Z_to_bv 64 0x83528) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold hvu_q6a_ss0. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    apply (HPgMem.hm_ro_region rsegs _ (w_H W) memc 10 A);
      [rewrite E10; apply unsigned_lit_small; lia | lia | lia |].
    constructor; [|constructor].
    eapply (chunk_ok_val rsegs _ _ A 4 4 (SOff 33 0) sz);
      [rewrite hvu_denot0, E33; reflexivity | lia | cbn; lia | exact VA].
  - cbn. tauto.
  - exact (hvu_facts_ok1 _ R 11 (A + 4) ltac:(rewrite E9; apply unsigned_lit_small; lia) ltac:(lia) Hal
            ltac:(rewrite E27; apply unsigned_lit_small; unfold SHADOW_OFF; lia)
            ltac:(rewrite E11; apply unsigned_lit_small; lia) ltac:(lia)). }
assert (SHOK : sh_ok rsegs HVU_Bx [mkSHE 11 0 4] (Ereg regs ex) (mrestrict (w_H W) memc)).
{ apply (hvu_sh1 W memc _ 11 (A + 4) 4);
  [ unfold HVU_Bx; rewrite (U_atom _ 27 SHADOW_OFF E27 ltac:(unfold SHADOW_OFF; lia)); reflexivity
  | rewrite (U_atom _ 11 (A + 4) E11 ltac:(lia)); reflexivity | exact Hra | lia
  | destruct Happ as [Hp|Hp]; [left; lia | right; lia] | lia | lia ]. }
remember (Ereg regs ex) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs ex) E) by (subst E; apply env_agree_refl).
clear HE EA Hex.
assert (Usz : U E (SExt true 32 (SOff 33 0)) = sz)
  by (rewrite (hvu_U_sext32 E 33 sz E33 ltac:(lia)); apply hvm_sx_id; lia).
unfold cfg_at. change (w64 0x83528) with (Z_to_bv 64 0x83528).
hvu_run HVU_Bspan awr_ok_tac. hvu_mem.
hvu_branch HVU_Bspan Hc.
all: hvu_unext Hc.
all: rewrite Usz, U_SLit in Hc.
all: change (zcanon 4) with 4 in Hc.
all: rewrite YO0c.branch_ltu, !unsigned_lit_small in Hc by lia.
- hvu_run_to HVU_Bspan awr_ok_tac HQU_RF. hvu_mem.
  apply SRr_ret; left. split; [apply Z.ltb_lt in Hc; exact Hc|].
  hvu_post0x B hvu_q6a_kept. exact I.
- hvu_run_to HVU_Bspan awr_ok_tac 0x83544. hvu_mem.
  apply SRr_ret; right. split; [apply Z.ltb_ge in Hc; exact Hc|].
  hvu_post0x B hvu_q6a_kept. exact I.
Qed.

(* q7 0x83550 -> 0x83568: the Int arm's body check and `ld a0,0xe8(s1); add s8,a0,s8` *)
Definition hvu_q7_ss0 : sstate := mkSS 0x83550 sr_atoms [hvu_q4_R] None (hvu_facts [10%nat]).

Lemma hvu_q7 : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
(R Ab o vb8 : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs (Z_to_bv 5 9) = w64 R -> getr regs (Z_to_bv 5 10) = w64 Ab ->
getr regs (Z_to_bv 5 24) = w64 o -> getr regs (Z_to_bv 5 27) = w64 SHADOW_OFF ->
2 ^ 46 <= R <= 2 ^ 47 -> R mod 16 = 0 -> R + 0xf0 <= 2 ^ 64 ->
4096 <= Ab -> Ab + 4 <= 0x7fffff800000 -> 0 <= o -> 0 <= vb8 -> vb8 + o < 2 ^ 64 ->
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF Ab 4 ->
(Ab + 4 <= kLowShadowBeg \/ kHighMemBeg <= Ab) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xe8) 8 (vb8 mod 2 ^ 64) ->
SRr rsegs W (cfg_at rsegs 0x83550 regs memc mdc)
(hvu_post0 B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs 0x83568 hvu_q4_kept
  (fun regs2 => getr regs2 (Z_to_bv 5 24) = w64 (vb8 + o))).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R Ab o vb8 HJ H9 H10 H24 H27
  HR Hal HR1 HA0 HA1 Ho Hvb8 Hsum Hra Happ V.
pose proof HPgSteps.img_wx as Hwx. pose proof HPgSteps.img_segs_low as Hsegs.
pose proof (AR_laws_ok rsegs B) as LAWS.
rewrite (Z.mod_small vb8 (2 ^ 64)) in V by lia.
remember (hvu_q4_extra vb8) as ex eqn:Hex.
assert (EA : forall (m : nat) (r : bv 5), Z.of_nat m = bv_unsigned r -> ew (Ereg regs ex) m = getr regs r)
  by (intros m r Hm; exact (ew_Ereg_nat regs _ m r Hm)).
assert (E9 : ew (Ereg regs ex) 9 = Z_to_bv 64 R) by (rewrite (EA 9%nat (Z_to_bv 5 9) eq_refl); exact H9).
assert (E10 : ew (Ereg regs ex) 10 = Z_to_bv 64 Ab) by (rewrite (EA 10%nat (Z_to_bv 5 10) eq_refl); exact H10).
assert (E24 : ew (Ereg regs ex) 24 = Z_to_bv 64 o) by (rewrite (EA 24%nat (Z_to_bv 5 24) eq_refl); exact H24).
assert (E27 : ew (Ereg regs ex) 27 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite (EA 27%nat (Z_to_bv 5 27) eq_refl); exact H27).
assert (E33 : ew (Ereg regs ex) 33 = Z_to_bv 64 vb8) by (subst ex; exact (ew_Ereg_extra regs _ 1)).
assert (HS : st_ok rsegs (Ereg regs ex) hvu_q7_ss0
  (restrict (w_H W) (mkst regs (Z_to_bv 64 0x83550) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold hvu_q7_ss0. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    apply (HPgMem.hm_ro_region rsegs _ (w_H W) memc 9 R);
      [rewrite E9; apply unsigned_lit_small; lia | lia | lia |].
    constructor; [|constructor].
    exact (hvu_slot_chunk _ _ _ R 0xe8 vb8 33 E33 ltac:(rewrite Z.mod_small by lia; exact V)).
  - cbn. tauto.
  - exact (hvu_facts_ok1 _ R 10 Ab ltac:(rewrite E9; apply unsigned_lit_small; lia) ltac:(lia) Hal
            ltac:(rewrite E27; apply unsigned_lit_small; unfold SHADOW_OFF; lia)
            ltac:(rewrite E10; apply unsigned_lit_small; lia) ltac:(lia)). }
assert (SHOK : sh_ok rsegs HVU_Bx [mkSHE 10 0 4] (Ereg regs ex) (mrestrict (w_H W) memc)).
{ apply (hvu_sh1 W memc _ 10 Ab 4);
  [ unfold HVU_Bx; rewrite (U_atom _ 27 SHADOW_OFF E27 ltac:(unfold SHADOW_OFF; lia)); reflexivity
  | rewrite (U_atom _ 10 Ab E10 ltac:(lia)); reflexivity | exact Hra | lia | exact Happ | lia | lia ]. }
remember (Ereg regs ex) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs ex) E) by (subst E; apply env_agree_refl).
clear HE EA Hex.
unfold cfg_at. change (w64 0x83550) with (Z_to_bv 64 0x83550).
hvu_run_to HVU_Bspan awr_ok_tac 0x83568. hvu_mem.
apply SRr_ret. hvu_post0x B hvu_q4_kept.
lazymatch goal with HS : st_ok _ ?E' ?ss' (restrict _ ?ms) |- _ =>
  rewrite !(st_ok_restrict_reg rsegs _ E' ss' ms _ HS) end.
hvu_sv. rewrite denot_lit_U. unfold w64. f_equal.
rewrite !hvu_U_ewset by (first [lia | (vm_compute; reflexivity)]).
rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom E 33 vb8 E33 ltac:(lia)), (U_atom E 24 o E24 ltac:(lia)).
unfold zcanon, M64. rewrite Z.mod_small by lia. lia.
Qed.

(* q8 0x83568 -> TAIL 0x83694 / RF 0x836a0: `lw s2,0(s8); li a0,256; bltu s2,a0` *)
Definition hvu_q8_kept : list (bv 5) :=
map (Z_to_bv 5) [1; 2; 3; 4; 5; 6; 7; 8; 9; 11; 12; 13; 14; 15; 16; 17; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28;
  29; 30; 31].
Definition hvu_q8_ss0 : sstate := mkSS 0x83568 sr_atoms [hvu_q5_R] None (mkFacts [] [] []).

Lemma hvu_q8 : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
(Ab bw : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs (Z_to_bv 5 24) = w64 Ab ->
0 <= Ab -> Ab + 4 <= 2 ^ 64 -> 0 <= bw < 2 ^ 32 ->
val_mem rsegs (mrestrict (w_H W) memc) Ab 4 bw ->
SRr rsegs W (cfg_at rsegs 0x83568 regs memc mdc)
(fun W2 c2 =>
 (bw <= 255 /\ hvu_post0 B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HVU_TAIL hvu_q8_kept
    (fun regs2 => getr regs2 (Z_to_bv 5 18) = w64 bw) W2 c2) \/
 (255 < bw /\ hvu_post0 B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HQU_RF hvu_q8_kept
    (fun _ => True) W2 c2)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Ab bw HJ H24 HA0 HA1 Hbw V.
pose proof HPgSteps.img_wx as Hwx. pose proof HPgSteps.img_segs_low as Hsegs.
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof (hvm_sx_range bw Hbw) as Hsx.
remember (hvu_q5_extra bw) as ex eqn:Hex.
assert (EA : forall (m : nat) (r : bv 5), Z.of_nat m = bv_unsigned r -> ew (Ereg regs ex) m = getr regs r)
  by (intros m r Hm; exact (ew_Ereg_nat regs _ m r Hm)).
assert (E24 : ew (Ereg regs ex) 24 = Z_to_bv 64 Ab) by (rewrite (EA 24%nat (Z_to_bv 5 24) eq_refl); exact H24).
assert (E33 : ew (Ereg regs ex) 33 = Z_to_bv 64 bw) by (subst ex; exact (ew_Ereg_extra regs _ 1)).
assert (HS : st_ok rsegs (Ereg regs ex) hvu_q8_ss0
  (restrict (w_H W) (mkst regs (Z_to_bv 64 0x83568) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold hvu_q8_ss0. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    apply (HPgMem.hm_ro_region rsegs _ (w_H W) memc 24 Ab);
      [rewrite E24; apply unsigned_lit_small; lia | lia | lia |].
    constructor; [|constructor].
    eapply (chunk_ok_val rsegs _ _ Ab 0 4 (SOff 33 0) bw);
      [rewrite hvu_denot0, E33; reflexivity | lia | cbn; lia | rewrite Z.add_0_r; exact V].
  - cbn. tauto.
  - split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. exact I. }
assert (SHOK : sh_ok rsegs HPgSteps.RTBx [] (Ereg regs ex) (mrestrict (w_H W) memc)) by constructor.
remember (Ereg regs ex) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs ex) E) by (subst E; apply env_agree_refl).
clear HE EA Hex.
assert (Ubw : U E (SExt true 32 (SOff 33 0)) = hvm_sx bw) by (apply hvu_U_sext32; [exact E33 | lia]).
unfold cfg_at. change (w64 0x83568) with (Z_to_bv 64 0x83568).
hvu_run HPgSteps.RTBspan awr_ok_tac. hvu_mem.
hvu_branch HPgSteps.RTBspan Hc.
all: rewrite (hvu_denot_of_U E _ _ Ubw) in Hc.
all: cbn [sv_denot] in Hc.
all: rewrite YO0c.branch_ltu, !unsigned_lit_small in Hc by lia.
- (* taken: the value is below 256, so the Int value is the body word *)
  hvu_run_to HPgSteps.RTBspan awr_ok_tac HVU_TAIL. hvu_mem.
  assert (Hle : bw <= 255) by (apply Z.ltb_lt in Hc; pose proof (hvm_sx_256 bw Hbw); lia).
  apply SRr_ret; left. split; [exact Hle|].
  hvu_post0_tac B hvu_q8_kept.
  lazymatch goal with HS : st_ok _ ?E' ?ss' (restrict _ ?ms) |- _ =>
    rewrite !(st_ok_restrict_reg rsegs _ E' ss' ms _ HS) end.
  hvu_sv. rewrite (hvu_denot_of_U E _ _ Ubw). unfold w64. f_equal.
  rewrite (proj1 (hvm_sx_s32 bw Hbw Hle)). exact (proj2 (hvm_sx_s32 bw Hbw Hle)).
- (* not taken: 255 < the value *)
  hvu_run_to HPgSteps.RTBspan awr_ok_tac HQU_RF. hvu_mem.
  assert (Hgt : 255 < bw) by (apply Z.ltb_ge in Hc; pose proof (hvm_sx_256 bw Hbw); lia).
  apply SRr_ret; right. split; [exact Hgt|].
  hvu_post0_tac B hvu_q8_kept. exact I.
Qed.


End d.
End b.

Print Assumptions hvu_q1.
Print Assumptions hvu_q2a.
Print Assumptions hvu_q2b.
Print Assumptions hvu_q3a.
Print Assumptions hvu_q3b.
Print Assumptions hvu_q4.
Print Assumptions hvu_q5.
Print Assumptions hvu_q6a.
Print Assumptions hvu_q7.
Print Assumptions hvu_q8.

(* ================================ the entry's fields, out of the pp block ================================ *)
(* the first word of the body: the entry's bytes 8 .. 11 (the slice equations of the type and the size are
   lib/A/HPgM3bScan.v hs_slice_type / hs_slice_size) *)
Lemma hvu_slice_body : forall e, (4 <= length (Model.e_body e))%nat ->
HPgMem.hm_slice (Layout.ent_mem e) 8 4 = firstn 4 (Model.e_body e).
Proof.
intros e H. unfold HPgMem.hm_slice, Layout.ent_mem.
rewrite skipn_app, (skipn_all2 (Cursor.le32 (Model.e_type e))) by (rewrite Cursor.length_le32; lia).
rewrite Cursor.length_le32. cbn [app].
rewrite skipn_app, (skipn_all2 (Cursor.le32 (Model.e_size e))) by (rewrite Cursor.length_le32; lia).
rewrite Cursor.length_le32. cbn [app]. change (8 - 4 - 4)%nat with 0%nat. rewrite skipn_O.
rewrite firstn_app. replace (4 - length (Model.e_body e))%nat with 0%nat by lia.
rewrite firstn_O, app_nil_r. reflexivity.
Qed.


Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.

(* q6b 0x83544 -> 0x83550: `sd a6,0x90(s1)` (the param into the real frame), `ld a0,0xe0(s1); add a0,a0,s8` *)
Definition hvu_q6b_kept : list (bv 5) :=
map (Z_to_bv 5) [1; 2; 3; 4; 5; 6; 7; 8; 9; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27;
  28; 29; 30; 31].
Definition hvu_q6b_R : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0x90 0xe8 0x90 0x98 [YP09.mkChunk 0xe0 (CVal 8 (SOff 33 0))].
Definition hvu_q6b_ss0 : sstate := mkSS 0x83544 sr_atoms [hvu_q6b_R] None (hvu_facts []).
Definition hvu_q6b_extra (vb8 : Z) : list word := [Z_to_bv 64 HPgSteps.SBr; Z_to_bv 64 vb8].

Lemma hvu_q6b : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
(R o p vb8 : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs (Z_to_bv 5 9) = w64 R -> getr regs (Z_to_bv 5 16) = w64 p -> getr regs (Z_to_bv 5 24) = w64 o ->
getr regs (Z_to_bv 5 27) = w64 SHADOW_OFF ->
2 ^ 46 <= R <= 2 ^ 47 -> R mod 16 = 0 -> sp0 - STK <= R -> R + 0x220 <= sp0 ->
0 <= o -> 0 <= vb8 -> vb8 + o < 2 ^ 64 -> 0 <= p < 2 ^ 64 ->
(forall a, R + 0x90 <= a < R + 0x98 -> apresent (w_H W) memc a) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xe0) 8 (vb8 mod 2 ^ 64) ->
SRr rsegs W (cfg_at rsegs 0x83544 regs memc mdc)
(hvu_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs 0x83550 hvu_q6b_kept
  (fun a => R + 0x90 <= a < R + 0x98)
  (fun regs2 mem2 => getr regs2 (Z_to_bv 5 10) = w64 (vb8 + o) /\
     val_mem rsegs (mrestrict (w_H W) mem2) (R + 0x90) 8 (p mod 2 ^ 64))).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R o p vb8 HJ H9 H16 H24 H27
  HR Hal Hstk0 Hstk1 Ho Hvb8 Hsum Hp Hpres V.
pose proof HPgSteps.img_wx as Hwx. pose proof HPgSteps.img_segs_low as Hsegs.
pose proof (AR_laws_ok rsegs B) as LAWS.
rewrite (Z.mod_small vb8 (2 ^ 64)) in V by lia.
rewrite (Z.mod_small p (2 ^ 64)) by lia.
remember (hvu_q6b_extra vb8) as ex eqn:Hex.
assert (EA : forall (m : nat) (r : bv 5), Z.of_nat m = bv_unsigned r -> ew (Ereg regs ex) m = getr regs r)
  by (intros m r Hm; exact (ew_Ereg_nat regs _ m r Hm)).
assert (E9 : ew (Ereg regs ex) 9 = Z_to_bv 64 R) by (rewrite (EA 9%nat (Z_to_bv 5 9) eq_refl); exact H9).
assert (E16 : ew (Ereg regs ex) 16 = Z_to_bv 64 p) by (rewrite (EA 16%nat (Z_to_bv 5 16) eq_refl); exact H16).
assert (E24 : ew (Ereg regs ex) 24 = Z_to_bv 64 o) by (rewrite (EA 24%nat (Z_to_bv 5 24) eq_refl); exact H24).
assert (E33 : ew (Ereg regs ex) 33 = Z_to_bv 64 vb8) by (subst ex; exact (ew_Ereg_extra regs _ 1)).
assert (E27 : ew (Ereg regs ex) 27 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite (EA 27%nat (Z_to_bv 5 27) eq_refl); exact H27).
assert (E9u : bv_unsigned (ew (Ereg regs ex) 9) = R) by (rewrite E9; apply unsigned_lit_small; lia).
assert (HS : st_ok rsegs (Ereg regs ex) hvu_q6b_ss0
  (restrict (w_H W) (mkst regs (Z_to_bv 64 0x83544) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold hvu_q6b_ss0. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    apply (HPgMem.hm_rw_region rsegs _ (w_H W) memc 9 R 0x90 0xe8 0x90 0x98);
      [exact E9u | lia | lia | intros q Hq; apply Hpres; lia |].
    constructor; [|constructor].
    exact (hvu_slot_chunk _ _ _ R 0xe0 vb8 33 E33 ltac:(rewrite Z.mod_small by lia; exact V)).
  - cbn. tauto.
  - exact (hvu_facts_ok0 _ R ltac:(rewrite E9; apply unsigned_lit_small; lia) ltac:(lia) Hal
            ltac:(rewrite E27; apply unsigned_lit_small; unfold SHADOW_OFF; lia)). }
assert (SHOK : sh_ok rsegs HPgSteps.RTBx [] (Ereg regs ex) (mrestrict (w_H W) memc)) by constructor.
remember (Ereg regs ex) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs ex) E) by (subst E; apply env_agree_refl).
clear HE EA Hex.
unfold cfg_at. change (w64 0x83544) with (Z_to_bv 64 0x83544).
hvu_run_to HPgSteps.RTBspan hvu_awr 0x83550.
apply SRr_ret.
lazymatch goal with
| HS2 : st_ok _ ?E2 ?ss2 (restrict _ ?ms2), HJ2 : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
  HFr : frame_of _ _ _ _ |- _ =>
  eapply (hvu_post_intro B);
  [ exact HS2 | reflexivity | reflexivity | exact HJ2 | hvu_io | hvu_keptx hvu_q6b_kept
  | exact (hvu_kept_run (fun a => R + 0x90 <= a < R + 0x98) _ _ (w_H W) memc memc _
      (fun a _ _ => eq_refl) HFr
      ltac:(intros a Hin; destruct Hin as (r0 & Hin & Hr0);
            unfold hvu_q6b_ss0 in Hin; cbn [ss_mem In] in Hin;
            destruct Hin as [Hin|[]]; subst r0;
            unfold hvu_q6b_R in Hr0; cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Hr0;
            rewrite E9u in Hr0; lia)) | ]
end.
split.
- lazymatch goal with HS2 : st_ok _ ?E2 ?ss2 (restrict _ ?ms2) |- _ =>
    rewrite !(st_ok_restrict_reg rsegs _ E2 ss2 ms2 _ HS2) end.
  hvu_sv. rewrite denot_lit_U. unfold w64. f_equal.
  rewrite U_SAlu. cbn [zalu_raw].
  rewrite (U_atom E 33 vb8 E33 ltac:(lia)), (U_atom E 24 o E24 ltac:(lia)).
  unfold zcanon, M64. rewrite Z.mod_small by lia. lia.
- lazymatch goal with HS2 : st_ok _ ?E2 ?ss2 (restrict _ ?ms2) |- _ =>
    pose proof (YN0d.st_ok_chunk rsegs E2 ss2 (restrict (w_H W) ms2) 0%nat _
                  (YP09.mkChunk 0x90 (CVal 8 (SOff 16 0))) HS2
                  ltac:(vm_compute; reflexivity) ltac:(cbn; tauto)) as HC;
    pose proof (hvu_chunk8_val E2 _ (base_val E2 (Some 9%nat)) 0x90 (SOff 16 0) p
                  ltac:(rewrite hvu_denot0; exact E16) ltac:(lia) HC) as VV
  end.
  assert (Hbv : base_val E (Some 9%nat) = R) by (rewrite <- E9u; reflexivity).
  rewrite Hbv in VV. exact VV.
Qed.

End w.

Print Assumptions hvu_q6b.

(* ================================ the lane ================================ *)
(* the only bytes a run of this lane writes: the param's cell R+0x90 (`sd a6,0x90(s1)` of the Int arm) *)
Definition hvu_wr (cx : hsu_scx rsegs) (a : Z) : Prop :=
  e_R (x_e rsegs cx) + 0x90 <= a < e_R (x_e rsegs cx) + 0x98.

(* a location the runs of this lane keep: a register of kept, or a real-frame cell apart from R+0x90 *)
Definition hvu_locb2 (kept : list (bv 5)) (f : hd_loc * Z) : bool :=
match fst f with
| LReg r => existsb (fun c => bv_eqb c (Z_to_bv 5 r)) kept
| LCell XR o => ((o + 8 <=? 0x90) || (0x98 <=? o)) && (0 <=? o) && (o <=? 0x1f0)
| LCell _ _ => false
end.

(* the type and the size as fields of the entry's 104 bytes: the statements and proofs of
   lib/A/HPgM3bScan.v hs_firstn4 / hs_slice_type / hs_slice_size, prefix-renamed and written
   out here because a file of image B must not Require a file of image A (lib/A/Img0's rsegs would shadow
   lib/AU/Img0U's). *)
Lemma hvu_firstn4 : forall (a b : list byte), length a = 4%nat -> firstn 4 (a ++ b) = a.
Proof. intros a b H. rewrite firstn_app, H, Nat.sub_diag, firstn_O, app_nil_r. apply firstn_all2. lia. Qed.

Lemma hvu_type_slice : forall e,
HPgMem.hm_slice (Layout.ent_mem e) 0 4 = Z_to_le_bytes 4 (Model.e_type e).
Proof.
intros e. unfold HPgMem.hm_slice, Layout.ent_mem. cbn [skipn].
apply hvu_firstn4. apply Cursor.length_le32.
Qed.

Lemma hvu_size_slice : forall e,
HPgMem.hm_slice (Layout.ent_mem e) 4 4 = Z_to_le_bytes 4 (Model.e_size e).
Proof.
intros e. unfold HPgMem.hm_slice, Layout.ent_mem.
rewrite skipn_app, Cursor.length_le32, Nat.sub_diag, skipn_O.
rewrite skipn_all2 by (rewrite Cursor.length_le32; lia). cbn [app].
apply hvu_firstn4. apply Cursor.length_le32.
Qed.

(* the body's first four bytes as a field of the entry's 104, for every size: ent_mem pads the body with zeros,
   and trailing zeros do not change a little-endian value *)
Lemma hvu_word_slice : forall e, Model.ent_wf e ->
HPgMem.hm_slice (Layout.ent_mem e) 8 4 = Z_to_le_bytes 4 (Cursor.rd32 (Model.e_body e)).
Proof.
assert (Hzero : forall k, bytes_le_to_Z (repeat Cursor.NUL k) = 0).
{ induction k as [|k IH]; [reflexivity|]. cbn [repeat]. rewrite HPgMem.hm_lez_cons, IH. reflexivity. }
assert (Hpad : forall (l : list byte) (k : nat), bytes_le_to_Z (l ++ repeat Cursor.NUL k) = bytes_le_to_Z l).
{ induction l as [|b l IH]; intros k; [cbn [app]; apply Hzero|].
  cbn [app]. rewrite !HPgMem.hm_lez_cons, IH. reflexivity. }
intros e (_ & Hb & Hs). unfold HPgMem.hm_slice, Layout.ent_mem.
assert (E8 : forall (a b : Z) (X : list byte), skipn 8 (Cursor.le32 a ++ Cursor.le32 b ++ X) = X)
by (intros; reflexivity).
rewrite E8.
assert (Hlen : length (Model.e_body e ++ Cursor.zeros (96 - length (Model.e_body e))) = 96%nat).
{ unfold Cursor.zeros. rewrite length_app, repeat_length. lia. }
assert (Hfr : forall (a : byte) (n k : nat), firstn n (repeat a k) = repeat a (Nat.min n k)).
{ induction n as [|n IH]; intros [|k]; cbn [firstn repeat Nat.min]; try reflexivity. rewrite IH. reflexivity. }
set (X := firstn 4 (Model.e_body e ++ Cursor.zeros (96 - length (Model.e_body e)))).
assert (HX4 : length X = 4%nat) by (subst X; rewrite length_firstn, Hlen; reflexivity).
assert (Hval : bytes_le_to_Z X = Cursor.rd32 (Model.e_body e)).
{ subst X. unfold Cursor.rd32, Cursor.zeros. rewrite firstn_app, Hfr. apply Hpad. }
rewrite <- Hval, <- HX4. symmetry. apply YA0d.Z_to_le_bytes_to_Z.
Qed.

(* what hm_pp_ent asks of a record *)
Lemma hvu_pp_ok : forall r, Model.pod_rec_wf r ->
Z.of_nat (length (Model.buf r)) <= Layout.POD_BUF_MAX /\
Forall (fun e => (length (Model.e_body e) <= 96)%nat) (Model.ents r).
Proof.
intros r Hw. split.
- pose proof Hw as (Hs & Hk & He & Hl & HL & Hc). unfold Model.buf. destruct (Model.p_corr r) as [[off bs]|].
  + destruct Hc as (Ho & Hb & _). unfold Model.overwrite. rewrite !length_app, length_firstn, length_skipn.
    unfold Layout.POD_BUF_MAX. lia.
  + unfold Layout.POD_BUF_MAX. lia.
- pose proof (Model.ents_wf r Hw) as [_ HF]. eapply Forall_impl; [|exact HF]. intros e (_ & Hb & Hs).
  cbv beta. lia.
Qed.

(* `snez s2,a0` of the Bool arm, as Headamp.cell_value reads a Bool *)
Lemma hvu_snez_eq : forall bw, 0 <= bw < 2 ^ 32 ->
(if 0 <? hvm_sx bw then 1 else 0) = (if bw =? 0 then 0 else 1).
Proof.
intros bw Hbw. unfold hvm_sx.
destruct (Z.eqb_spec bw 0) as [->|Hn].
- vm_compute. reflexivity.
- replace (0 <? (if bw <? 2 ^ 31 then bw else bw + (2 ^ 64 - 2 ^ 32))) with true;
    [reflexivity | symmetry; apply Z.ltb_lt; destruct (Z.ltb_spec bw (2 ^ 31)); lia].
Qed.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis errno_low : api_env rsegs B.

(* a block of the segment's own state lies below the allocator's ceiling *)
Lemma hvu_blk_low : forall (cx : hsu_scx rsegs) (sh : list Z) (p n : Z),
hsu_pre rsegs B headamp_himg_B cx sh -> In (p, n) (ablocks B (x_lyc rsegs cx) (x_Sc rsegs cx)) ->
p mod 16 = 0 /\ 4096 <= p /\ p + req_size n <= alloc_ceiling.
Proof using.
intros cx sh p n Hpre Hin.
pose proof Hpre as Hpre'. unfold hsu_pre, hd_seg_pre in Hpre'.
destruct Hpre' as (HJ & _).
pose proof HJ as (HAR & _).
destruct (al_blocks _ _ (AR_laws_ok rsegs B) _ _ _ _ _ _ _ HAR Hin) as (Hnz & H0 & Hc & _).
split; [exact Hnz|]. split; [exact H0 | exact Hc].
Qed.

(* the answer's cap, as hd_seg_pre fixes it *)
Lemma hvu_cap : forall (cx : hsu_scx rsegs) (sh : list Z),
hsu_pre rsegs B headamp_himg_B cx sh -> 0 <= e_cap (x_e rsegs cx) <= 9.
Proof using. intros cx sh H. unfold hsu_pre, hd_seg_pre in H. tauto. Qed.

(* the errno cell lies in the image, far below the allocator's ceiling *)
Lemma hvu_errno_low : forall i, 0 <= i < 4 -> 0 <= as_errno B + i < alloc_ceiling.
Proof using errno_low.
intros i Hi. destruct errno_low as ((H0 & H1) & _ & _).
pose proof asan_consts as (C1 & _). unfold kLowMemEnd in H1. lia.
Qed.

(* a cut's facts across a run of this lane *)
Lemma hvu_at_carry : forall (cx : hsu_scx rsegs) (W : world rsegs) mem mem' regs regs' (kept : list (bv 5)) L,
hsu_at rsegs (w_H W) mem regs (x_e rsegs cx) L ->
(forall a, 0 <= a < 2 ^ 64 -> ~ hvu_wr cx a -> aview rsegs (w_H W) mem' a = aview rsegs (w_H W) mem a) ->
(forall r, In r kept -> getr regs' r = getr regs r) ->
forallb (hvu_locb2 kept) L = true ->
0 <= e_R (x_e rsegs cx) -> e_R (x_e rsegs cx) + 0x200 <= 2 ^ 64 ->
hsu_at rsegs (w_H W) mem' regs' (x_e rsegs cx) L.
Proof using.
intros cx W mem mem' regs regs' kept L HAT HK Hk Hb HR0 HR1.
unfold hsu_at in *.
apply (HPgMem.hm_atl_kept rsegs (w_H W) mem (w_H W) mem' regs regs' (x_e rsegs cx) L HAT).
intros f Hf. pose proof (proj1 (forallb_forall _ _) Hb f Hf) as Hl.
apply (HPgMem.hm_keeps_of rsegs (fun a => ~ (0 <= a < 2 ^ 64) \/ hvu_wr cx a)).
- intros x Hx. apply HK.
  + destruct (Z.le_gt_cases 0 x); destruct (Z.lt_ge_cases x (2 ^ 64)); try lia;
    exfalso; apply Hx; left; lia.
  + intros Hw. apply Hx. right. exact Hw.
- unfold hvu_locb2 in Hl. destruct f as [[rr|bb o] v]; cbn [fst] in Hl |- *.
  + apply existsb_exists in Hl as (c & Hc & Hcb). apply bv_eqb_eq in Hcb. subst c. exact (Hk _ Hc).
  + destruct bb; try discriminate Hl.
    apply andb_prop in Hl as [Hl Ho2]. apply andb_prop in Hl as [Hl Ho1].
    apply Z.leb_le in Ho1. apply Z.leb_le in Ho2.
    intros i Hi [Hn|Hw]; [apply Hn; cbn [hd_xv]; lia|]. unfold hvu_wr in Hw. cbn [hd_xv] in Hw.
    apply orb_prop in Hl as [Hl|Hl]; apply Z.leb_le in Hl; lia.
Qed.

(* the frame object x across a run of this lane *)
Lemma hvu_x_kept : forall (cx : hsu_scx rsegs) (W : world rsegs) mem mem' cs keys rf,
hsu_pre rsegs B headamp_himg_B cx (hi_shA headamp_himg_B) ->
hqu_x_at rsegs cx W mem cs keys rf ->
(forall a, 0 <= a < 2 ^ 64 -> ~ hvu_wr cx a -> aview rsegs (w_H W) mem' a = aview rsegs (w_H W) mem a) ->
hqu_x_at rsegs cx W mem' cs keys rf.
Proof using.
intros cx W mem mem' cs keys rf Hpre (Hg & Hl & Hrest) HK. split; [|split; [exact Hl | exact Hrest]].
destruct (hvu_stack B cx _ Hpre) as (_ & _ & _ & _ & Hceil & H46 & _).
destruct (hvu_apart B cx _ Hpre) as (_ & _ & _ & _ & _ & HF0 & HFc & _).
apply (proj1 (HPgMem.hm_bytes_zbytes rsegs (w_H W) mem' _ _)).
apply (HPgMem.hm_bytes_kept rsegs (w_H W) mem);
  [exact (proj2 (HPgMem.hm_bytes_zbytes rsegs (w_H W) mem _ _) Hg)|].
rewrite (hqu_x_open_len cs keys rf Hl). intros y Hy.
unfold hvu_wr, HQU_XO, T_SEG_STK, ASTACK in *. apply HK; lia.
Qed.

(* hsu_core across a run that writes at most R+0x90 .. R+0x98, which lies in M03's write set [R, R+0x160) *)
Lemma hvu_core_run : forall (cx : hsu_scx rsegs) ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3,
hsu_core rsegs B MT cx (hqu_E3 rsegs B cx) ly2 S2 W2 regs2 mem2 md2 ->
ajournal rsegs B (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx)
  (x_W0 rsegs cx) (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) ly2 S2 W2 mem3 md3 (x_k rsegs cx) ->
same_io md2 md3 ->
(forall q : Z, q = 2 \/ q = 3 \/ q = 4 -> getr regs3 (Z_to_bv 5 q) = getr regs2 (Z_to_bv 5 q)) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ hvu_wr cx a -> aview rsegs (w_H W2) mem3 a = aview rsegs (w_H W2) mem2 a) ->
hsu_core rsegs B MT cx (hqu_E3 rsegs B cx) ly2 S2 W2 regs3 mem3 md3.
Proof using.
intros cx ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 Hcore HJ3 Hio3 H234 HK.
unfold hsu_core, hsu_mid in Hcore |- *.
destruct Hcore as (_ & Hr234 & Hfr & Hperm & Hio & Hmo & Hmem).
split; [exact HJ3|].
split; [intros q Hq; rewrite (H234 q Hq); exact (Hr234 q Hq)|].
split; [exact Hfr|]. split; [exact Hperm|]. split; [exact (same_io_trans _ _ _ Hio Hio3)|].
split; [exact Hmo|].
intros a Ha Hs He. rewrite (HK a Ha); [exact (Hmem a Ha Hs He)|].
intros Hw. apply He. unfold hqu_E3. left. unfold hd_inw. cbn [hi_w3 headamp_himg_B].
apply Exists_cons_tl. apply Exists_cons_tl. apply Exists_cons_hd. cbn [fst snd hd_xv].
unfold hvu_wr in Hw. lia.
Qed.

(* what every cut inside M03 carries, across a run of this lane *)
Lemma hvu_base3_run : forall (cx : hsu_scx rsegs) r ev (fx2 : YK11.FPState) ly2 S2 W2 regs2 mem2 md2
regs3 mem3 md3,
@hqu_start_M03 fx rc SK rsegs B cx r ev ->
@hqu_base3 fx rc SK rsegs B MT cx fx2 r hqu_shX ly2 S2 W2 regs2 mem2 md2 ->
ajournal rsegs B (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx)
  (x_W0 rsegs cx) (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) ly2 S2 W2 mem3 md3 (x_k rsegs cx) ->
same_io md2 md3 ->
(forall q : Z, q = 2 \/ q = 3 \/ q = 4 -> getr regs3 (Z_to_bv 5 q) = getr regs2 (Z_to_bv 5 q)) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ hvu_wr cx a -> aview rsegs (w_H W2) mem3 a = aview rsegs (w_H W2) mem2 a) ->
@hqu_base3 fx rc SK rsegs B MT cx fx2 r hqu_shX ly2 S2 W2 regs3 mem3 md3.
Proof using errno_low.
intros cx r ev fx2 ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 HS Hb HJ3 Hio3 H234 HK.
pose proof HS as (Hpre & _ & Hwf & Hlen & _ & _ & Hpodb & _ & _ & _ & _ & Houtb & _).
destruct (hvu_stack B cx _ Hpre) as (_ & _ & _ & _ & Hceil & H46 & _).
destruct (hvu_apart B cx _ Hpre) as (_ & _ & Hpp0 & Hppc & _ & HF0 & HFc & _).
destruct (hvu_cap cx _ Hpre) as (Hcap0 & Hcap9).
destruct Hpodb as (_ & Hpodin & _). destruct Houtb as (_ & Houtin & _).
destruct (hvu_blk_low cx _ _ _ Hpre Hpodin) as (_ & Hpod0 & Hpodc).
destruct (hvu_blk_low cx _ _ _ Hpre Houtin) as (_ & Hout0 & Houtc).
pose proof (@alloc_ceiling_value rc) as ((Hc0 & Hc1) & _).
unfold T_SEG_STK, ASTACK in Hceil.
assert (KL : forall a, 0 <= a < alloc_ceiling -> aview rsegs (w_H W2) mem3 a = aview rsegs (w_H W2) mem2 a).
{ intros a Ha. apply HK; [lia|]. unfold hvu_wr. lia. }
assert (Hreq : forall n, 0 <= n -> n <= req_size n)
  by (intros n Hn; unfold req_size; destruct (Z.eqb_spec n 0); lia).
destruct Hb as (Hcore & Hfxk & Hfsh & Hrom & Hpp & Hpod & Hout & Hres & (ev2 & Herr)).
split; [exact (hvu_core_run cx ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 Hcore HJ3 Hio3 H234 HK)|].
split; [exact Hfxk|].
split.
{ unfold hsu_fsh_at in *. apply (HPgMem.hm_fsh_kept rsegs (w_H W2) mem2 (w_H W2) mem3 _ _ Hfsh).
  intros i Hi. rewrite hqu_shX_len in Hi. apply KL. unfold shadow_addr, SHADOW_OFF.
  assert (Hd0 : 0 <= e_F (x_e rsegs cx) / 8) by (apply Z.div_pos; lia).
  assert (Hd1 : e_F (x_e rsegs cx) / 8 <= 17592184995840) by (apply Z.div_le_upper_bound; lia).
  lia. }
split.
{ apply (HPgMem.hm_rom_kept rsegs W2 W2 mem2 mem3 Hrom). intros a (sg & Hin & _ & Hsb).
  assert (Himg : in_img rsegs a) by (exists sg; split; [exact Hin | exact Hsb]).
  pose proof (HPgSteps.img_segs_low a Himg) as Hlow. unfold kLowMemEnd in Hlow. apply KL. lia. }
split.
{ unfold hsu_pp_at in *. apply (proj1 (HPgMem.hm_bytes_zbytes rsegs (w_H W2) mem3 _ _)).
  apply (HPgMem.hm_bytes_kept rsegs (w_H W2) mem2);
    [exact (proj2 (HPgMem.hm_bytes_zbytes rsegs (w_H W2) mem2 _ _) Hpp)|].
  rewrite (Layout.length_pp_bytes r Hwf). intros x Hx. apply KL. lia. }
split.
{ apply (proj1 (HPgMem.hm_bytes_zbytes rsegs (w_H W2) mem3 _ _)).
  apply (HPgMem.hm_bytes_kept rsegs (w_H W2) mem2);
    [exact (proj2 (HPgMem.hm_bytes_zbytes rsegs (w_H W2) mem2 _ _) Hpod)|].
  rewrite <- Hlen. intros x Hx. pose proof (Hreq (e_len (x_e rsegs cx)) ltac:(lia)). apply KL. lia. }
split.
{ apply (proj1 (HPgMem.hm_bytes_zbytes rsegs (w_H W2) mem3 _ _)).
  apply (HPgMem.hm_bytes_kept rsegs (w_H W2) mem2);
    [exact (proj2 (HPgMem.hm_bytes_zbytes rsegs (w_H W2) mem2 _ _) Hout)|].
  pose proof (Headamp.parse_props_total (hd_props (e_null (x_e rsegs cx)) (Model.buf r))
    (e_cap (x_e rsegs cx)) ltac:(lia)) as Hok.
  fold (hqu_ans rsegs cx r) in Hok.
  apply answer_ok_parts in Hok as (Hcase & _).
  assert (Hlc : Z.of_nat (length (ans_cells (hqu_ans rsegs cx r))) <= e_cap (x_e rsegs cx))
    by (destruct Hcase as [(_ & Hc & _)|(Hr & Hl & _)]; [rewrite Hc; cbn [length]; lia | lia]).
  rewrite length_ha_cells_bytes. intros x Hx.
  pose proof (Hreq (3 * (e_cap (x_e rsegs cx) + 1)) ltac:(lia)). apply KL. lia. }
split.
{ apply (proj1 (HPgMem.hm_bytes_zbytes rsegs (w_H W2) mem3 _ _)).
  apply (HPgMem.hm_bytes_kept rsegs (w_H W2) mem2);
    [exact (proj2 (HPgMem.hm_bytes_zbytes rsegs (w_H W2) mem2 _ _) Hres)|].
  unfold ans_res_bytes. rewrite length_ha_res_bytes. intros x Hx. apply KL. unfold HQU_RES in Hx. lia. }
exists ev2. intros j Hj.
assert (Hj' : 0 <= Z.of_nat j < 4) by lia.
pose proof (hvu_errno_low (Z.of_nat j) Hj') as He.
rewrite (KL _ He). exact (Herr j Hj).
Qed.

(* the value entry ent[m + 1] in the first block: its three words, their shadow, its place *)
Lemma hvu_ent : forall (cx : hsu_scx rsegs) r ev (fx2 : YK11.FPState) ly2 S2 W2 regs2 mem2 md2 m k v cs keys rf,
@hqu_start_M03 fx rc SK rsegs B cx r ev ->
@hqu_base3 fx rc SK rsegs B MT cx fx2 r hqu_shX ly2 S2 W2 regs2 mem2 md2 ->
hqu_pair_inv rsegs cx r m k v cs keys rf ->
Model.ent_wf v /\ (S m < 32)%nat /\
val_mem rsegs (mrestrict (w_H W2) mem2) (hvu_entA cx m) 4 (Model.e_type v) /\
val_mem rsegs (mrestrict (w_H W2) mem2) (hvu_entA cx m + 4) 4 (Model.e_size v) /\
val_mem rsegs (mrestrict (w_H W2) mem2) (hvu_entA cx m + 8) 4 (Cursor.rd32 (Model.e_body v)) /\
range_addressable (aview rsegs (w_H W2) mem2) SHADOW_OFF (hvu_entA cx m) 16 /\
range_addressable (aview rsegs (w_H W2) mem2) SHADOW_OFF (hvu_entA cx m + 4) 4 /\
range_addressable (aview rsegs (w_H W2) mem2) SHADOW_OFF (hvu_entA cx m + 8) 4 /\
4096 <= hvu_entA cx m /\ hvu_entA cx m + 16 <= alloc_ceiling /\
(hvu_entA cx m + 16 <= kLowShadowBeg \/ kHighMemBeg <= hvu_entA cx m).
Proof using.
intros cx r ev fx2 ly2 S2 W2 regs2 mem2 md2 m k v cs keys rf HS Hb (Hv & _ & HSm & _).
pose proof HS as (Hpre & _ & Hwf & _).
destruct (hvu_apart B cx _ Hpre) as (Hppin & Hpp16 & Hpp0 & Hppc & Happ & _).
destruct Hb as (Hcore & _ & _ & _ & Hpp & _).
destruct Hcore as (HJ & _ & _ & Hperm & _).
pose proof HJ as (HAR & _).
pose proof (Model.ents_wf r Hwf) as (Hn32 & Hall).
assert (Hvwf : Model.ent_wf v)
  by (rewrite Hv; apply (proj1 (Forall_forall _ _) Hall); apply nth_In; exact HSm).
destruct (hvu_pp_ok r Hwf) as (Hbm & Hbod).
assert (Hent : HPgMem.hm_bytes rsegs (w_H W2) mem2 (hvu_entA cx m) (Layout.ent_mem v)).
{ unfold hsu_pp_at in Hpp. apply (proj2 (HPgMem.hm_bytes_zbytes rsegs _ _ _ _)) in Hpp.
  unfold Layout.pp_bytes in Hpp.
  pose proof (HPgMem.hm_pp_ent rsegs _ _ _ _ _ _ Hbm Hn32 Hbod _ _ _ (S m) Hpp HSm) as He.
  rewrite <- Hv in He.
  replace (hvu_entA cx m)
    with (e_pp (x_e rsegs cx) + (Layout.OFF_ENT + Layout.ENT_SIZE * Z.of_nat (S m)))
    by (unfold hvu_entA; rewrite Nat2Z.inj_succ; unfold Layout.OFF_ENT, Layout.ENT_SIZE; lia).
  exact He. }
assert (Hlen : length (Layout.ent_mem v) = 104%nat)
  by (apply Layout.length_ent_mem; destruct Hvwf as (_ & Hbl & Hz); lia).
assert (Hreq : req_size Layout.PP_SIZE = Layout.PP_SIZE) by reflexivity.
unfold Layout.PP_SIZE in Hppc, Happ, Hreq.
assert (HA0 : 4096 <= hvu_entA cx m)
  by (unfold hvu_entA, Layout.OFF_ENT, Layout.ENT_SIZE; lia).
assert (HA1 : hvu_entA cx m + 104 <= e_pp (x_e rsegs cx) + 19744)
  by (unfold hvu_entA, Layout.OFF_ENT, Layout.ENT_SIZE; lia).
assert (HRA : forall b n, hvu_entA cx m <= b -> b + n <= hvu_entA cx m + 16 ->
  range_addressable (aview rsegs (w_H W2) mem2) SHADOW_OFF b n).
{ intros b n Hb0 Hb1.
  destruct (HPgMem.hm_blk_ra rsegs B ly2 S2 W2 mem2 md2 _ _ b n HAR
    (Permutation_in _ (Permutation_sym Hperm) Hppin)) as (Hra & _);
  [unfold hvu_entA, Layout.OFF_ENT, Layout.ENT_SIZE in Hb0 |- *; lia
  | unfold Layout.PP_SIZE; rewrite Hreq; unfold hvu_entA, Layout.OFF_ENT, Layout.ENT_SIZE in Hb1 |- *; lia
  | exact Hra]. }
split; [exact Hvwf|]. split; [lia|].
split.
{ pose proof (HPgMem.hm_bytes_field rsegs _ _ _ _ 0 4 _ Hent (hvu_type_slice v) ltac:(lia)) as X.
  change (Z.of_nat 0) with 0 in X. rewrite Z.add_0_r in X. exact X. }
split.
{ pose proof (HPgMem.hm_bytes_field rsegs _ _ _ _ 4 4 _ Hent (hvu_size_slice v) ltac:(lia)) as X.
  change (Z.of_nat 4) with 4 in X. exact X. }
split.
{ pose proof (HPgMem.hm_bytes_field rsegs _ _ _ _ 8 4 _ Hent (hvu_word_slice v Hvwf) ltac:(lia)) as X.
  change (Z.of_nat 8) with 8 in X. exact X. }
split; [apply HRA; lia|].
split; [apply HRA; lia|].
split; [apply HRA; lia|].
split; [exact HA0|].
split; [unfold hvu_entA, Layout.OFF_ENT, Layout.ENT_SIZE in HA1 |- *; lia|].
unfold hvu_entA, Layout.OFF_ENT, Layout.ENT_SIZE in Happ |- *. lia.
Qed.

(* the VAL cut's facts every exit of this lane carries: all but s2 = m + 1 and s8 = 104 (m + 1) *)
Definition hvu_L (cx : hsu_scx rsegs) (m : nat) (ch p : Z) : list (hd_loc * Z) :=
  hqu_L_seg rsegs cx ++ hqu_L_loopc rsegs cx ++ hqu_L_t56 rsegs cx ++ hqu_L_body rsegs cx (Z.of_nat m + 2) ++
  [(LReg 16, p); (LReg 23, hvm_top p); (LReg 21, ch); (LReg 15, Headamp.REFUSE_OUT_OF_RANGE)].

(* the registers no block of this lane writes: all but a0, a1, a2, a3, s2 and s8 *)
Definition hvu_keptD : list (bv 5) :=
map (Z_to_bv 5) [1; 2; 3; 4; 5; 6; 7; 8; 9; 14; 15; 16; 17; 19; 20; 21; 22; 23; 25; 26; 27; 28; 29; 30; 31].

Ltac hvu_incl := intros Hr0; apply in_map_iff in Hr0 as (z & <- & Hz); apply in_map;
                 cbn [In] in Hz |- *; lia.
Ltac hvu_subL HL :=
apply (hvu_at_sub _ _ _ _ _ _ HL);
let y := fresh "y" in let Hy := fresh "Hy" in
intros y Hy; unfold hvu_L in Hy; hvu_unf; cbn [In app] in Hy |- *;
repeat (destruct Hy as [<-|Hy]; [repeat (first [left; reflexivity | right]) |]); destruct Hy.
(* the target list is a sub-list of a list built on hvu_L *)
Ltac hvu_subF HL :=
apply (hvu_at_sub _ _ _ _ _ _ HL);
let y := fresh "y" in let Hy := fresh "Hy" in
intros y Hy; unfold hvu_L;
unfold hqu_L_seg, hqu_L_frame, hqu_L_loopc, hqu_L_t56, hqu_L_body in Hy |- *;
cbn [In app] in Hy |- *;
repeat (destruct Hy as [<-|Hy]; [repeat (first [left; reflexivity | right]) |]); destruct Hy.

Theorem hvu_disp_B : @hvu_piece_disp_stmt fx rc SK B MT.
Proof.
unfold hvu_piece_disp_stmt. intros cx POST r ev at0 m HS HCELL HRF HTAIL HFA.
unfold hqu_from_VAL. intros fx2 ly2 S2 W2 regs2 mem2 md2 k v ch p cs keys rf Hcut.
destruct Hcut as (Hb3 & Hat & Hf1 & Hf2 & Hf3 & Hlive & Ham & Hkey & Hpair & Hkcs & Hx).
pose proof (hvu_start_pre B cx r ev HS) as Hpre.
destruct (hvu_stack B cx _ Hpre) as (HspR & HR32 & HRS & Hwin & Hceil & HRrng & Hsp47 & Hevv & G2 & G3 & G4).
destruct (hvu_apart B cx _ Hpre) as (Hppin & Hpp16 & Hpp0 & Hppc & Happ & HF0 & HFc & HF32 & Hown).
pose proof (@alloc_ceiling_value rc) as ((Hc0 & Hc1) & _).
unfold T_SEG_STK, ASTACK in Hwin, Hceil.
assert (HR16 : e_R (x_e rsegs cx) mod 16 = 0).
{ apply Z.mod_divide; [lia|]. apply (Z.divide_trans _ 32);
  [exists 2; reflexivity | apply Z.mod_divide; [lia | exact HR32]]. }
destruct (hvu_ent cx r ev fx2 ly2 S2 W2 regs2 mem2 md2 m k v cs keys rf HS Hb3 Hpair)
  as (Hvwf & Hm32 & Vt & Vs & Vb & Hra16 & Hra4 & Hra8 & HA0 & HA1 & HAapp).
destruct (hvm_ent_bounds v Hvwf) as (Ht & Hsz).
pose proof (Cursor.rd32_range (Model.e_body v)) as Hbw.
destruct (hvm_key_cell _ ch p Hkey) as (Hch & Hp).
assert (Hpr : 0 <= p < 2 ^ 64)
  by (unfold Headamp.HA_PHANTOM, Headamp.HA_PAD, Headamp.HA_SENS in Hp; lia).
pose proof Hb3 as ((HJ & _) & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
unfold hsu_at_cx in Hat.
pose proof (hvu_at_get _ _ _ _ _ 9 (e_R (x_e rsegs cx)) Hat ltac:(hvu_in)) as R9.
pose proof (hvu_at_get _ _ _ _ _ 27 SHADOW_OFF Hat ltac:(hvu_in)) as R27.
pose proof (hvu_at_get _ _ _ _ _ 18 (Z.of_nat m + 1) Hat ltac:(hvu_in)) as R18.
pose proof (hvu_at_get _ _ _ _ _ 24 (Layout.ENT_SIZE * (Z.of_nat m + 1)) Hat ltac:(hvu_in)) as R24.
pose proof (hvu_at_get _ _ _ _ _ 16 p Hat ltac:(hvu_in)) as R16.
pose proof (hvu_at_cell _ _ _ _ _ XR 0xf0 (hqu_not (e_pp (x_e rsegs cx) + Layout.OFF_ENT)) Hat
  ltac:(hvu_in)) as Cf0.
pose proof (hvu_at_cell _ _ _ _ _ XR 0xf8 (e_pp (x_e rsegs cx) + Layout.OFF_ENT) Hat ltac:(hvu_in)) as Cf8.
pose proof (hvu_at_cell _ _ _ _ _ XR 0x100 (e_pp (x_e rsegs cx) + Layout.OFF_ENT + 4) Hat
  ltac:(hvu_in)) as C100.
pose proof (hvu_at_cell _ _ _ _ _ XR 0xe0 (e_pp (x_e rsegs cx) + Layout.OFF_ENT + 8) Hat ltac:(hvu_in)) as Ce0.
pose proof (hvu_at_cell _ _ _ _ _ XR 0xe8 (e_pp (x_e rsegs cx) + Layout.OFF_ENT + 8) Hat ltac:(hvu_in)) as Ce8.
cbn [hd_xv] in Cf0, Cf8, C100, Ce0, Ce8.
assert (HatL : hsu_at rsegs (w_H W2) mem2 regs2 (x_e rsegs cx) (hvu_L cx m ch p)) by hvu_subL Hat.
assert (HAe : hvu_entA cx m = e_pp (x_e rsegs cx) + Layout.OFF_ENT + Layout.ENT_SIZE * (Z.of_nat m + 1))
  by reflexivity.
unfold Layout.OFF_ENT, Layout.ENT_SIZE in HAe.
unfold Layout.PP_SIZE in Hppc.
assert (Hm31 : (Z.of_nat m + 1 <= 31)%Z) by lia.
(* VAL 0x83490 -> 0x834a8 *)
eapply SRr_bind.
{ eapply (hvu_q1 (fx := fx2) B);
  try first [ exact HJ | exact R9 | exact R18 | exact R24 | exact Cf0 | exact Cf8 ];
  try (unfold hvu_entA, Layout.OFF_ENT, Layout.ENT_SIZE in * ); lia. }
intros W3 c3 _ (-> & regs3 & md3 & -> & HJ3 & Hio3 & Hk3 & Q10).
(* 0x834a8 -> 0x834c0 *)
assert (P9 : getr regs3 (Z_to_bv 5 9) = w64 (e_R (x_e rsegs cx)))
  by (rewrite Hk3; [exact R9 | unfold hvu_q1_kept; apply in_map; cbn [In]; lia]).
assert (P27 : getr regs3 (Z_to_bv 5 27) = w64 SHADOW_OFF)
  by (rewrite Hk3; [exact R27 | unfold hvu_q1_kept; apply in_map; cbn [In]; lia]).
assert (P24 : getr regs3 (Z_to_bv 5 24) = w64 (Layout.ENT_SIZE * (Z.of_nat m + 1)))
  by (rewrite Hk3; [exact R24 | unfold hvu_q1_kept; apply in_map; cbn [In]; lia]).
assert (QA : getr regs3 (Z_to_bv 5 10) = w64 (hvu_entA cx m)) by (rewrite Q10; rewrite HAe; reflexivity).
eapply SRr_bind.
{ eapply (hvu_q2a (fx := fx2) B);
  try first [ exact HJ3 | exact P9 | exact QA | exact P27 | exact HR16 | exact Hra16 | exact HAapp | exact Vt ];
  try (unfold hvu_entA, Layout.OFF_ENT, Layout.ENT_SIZE in * ); lia. }
intros W4 c4 _ (-> & regs4 & md4 & -> & HJ4 & Hio4 & Hk4 & (Q11 & Q12)).
(* 0x834c0 -> the four arms *)
assert (S9 : getr regs4 (Z_to_bv 5 9) = w64 (e_R (x_e rsegs cx)))
  by (rewrite Hk4; [exact P9 | unfold hvu_q2a_kept; apply in_map; cbn [In]; lia]).
assert (S24 : getr regs4 (Z_to_bv 5 24) = w64 (Layout.ENT_SIZE * (Z.of_nat m + 1)))
  by (rewrite Hk4; [exact P24 | unfold hvu_q2a_kept; apply in_map; cbn [In]; lia]).
assert (S27 : getr regs4 (Z_to_bv 5 27) = w64 SHADOW_OFF)
  by (rewrite Hk4; [exact P27 | unfold hvu_q2a_kept; apply in_map; cbn [In]; lia]).
assert (SA : getr regs4 (Z_to_bv 5 10) = w64 (hvu_entA cx m))
  by (rewrite Hk4; [exact QA | unfold hvu_q2a_kept; apply in_map; cbn [In]; lia]).
pose proof (hvm_sx_range (Model.e_type v) Ht) as Hsxr.
eapply SRr_bind.
{ eapply (hvu_q2b (fx := fx2) B);
  try first [ exact HJ4 | exact S9 | exact Q11 | exact Q12 | exact S24 | exact C100 ];
  try (unfold hvu_entA, Layout.OFF_ENT, Layout.ENT_SIZE in * ); lia. }
intros W5 c5 _ [(E6 & -> & regs5 & md5 & -> & HJ5 & Hio5 & Hk5 & Q13)
              | [(E4 & -> & regs5 & md5 & -> & HJ5 & Hio5 & Hk5 & Q11b)
              | [(E2 & -> & regs5 & md5 & -> & HJ5 & Hio5 & Hk5 & Q11b)
              |  (N6 & N4 & N2 & -> & regs5 & md5 & -> & HJ5 & Hio5 & Hk5 & _)]]].
(* what every arm carries out of the dispatch *)
all: assert (Hio25 : same_io md2 md5)
  by exact (same_io_trans _ _ _ Hio3 (same_io_trans _ _ _ Hio4 Hio5)).
all: assert (HkD : forall r0, In r0 hvu_keptD -> getr regs5 r0 = getr regs2 r0)
  by (intros r0 Hr0;
      rewrite (Hk5 r0 ltac:(revert Hr0; unfold hvu_keptD, hvu_q2b_kept; hvu_incl));
      rewrite (Hk4 r0 ltac:(revert Hr0; unfold hvu_keptD, hvu_q2a_kept; hvu_incl));
      exact (Hk3 r0 ltac:(revert Hr0; unfold hvu_keptD, hvu_q1_kept; hvu_incl))).
all: assert (H234 : forall q : Z, q = 2 \/ q = 3 \/ q = 4 ->
  getr regs5 (Z_to_bv 5 q) = getr regs2 (Z_to_bv 5 q))
  by (intros q Hq; apply HkD; destruct Hq as [->|[->| ->]]; unfold hvu_keptD; apply in_map; cbn [In]; lia).
all: assert (HatD : hsu_at rsegs (w_H W2) mem2 regs5 (x_e rsegs cx) (hvu_L cx m ch p))
  by (apply (hvu_at_keep _ _ _ _ _ HatL regs5 hvu_keptD HkD); vm_compute; reflexivity).
all: assert (T9 : getr regs5 (Z_to_bv 5 9) = w64 (e_R (x_e rsegs cx)))
  by (rewrite HkD; [exact R9 | unfold hvu_keptD; apply in_map; cbn [In]; lia]).
all: assert (T27 : getr regs5 (Z_to_bv 5 27) = w64 SHADOW_OFF)
  by (rewrite HkD; [exact R27 | unfold hvu_keptD; apply in_map; cbn [In]; lia]).
all: assert (T16 : getr regs5 (Z_to_bv 5 16) = w64 p)
  by (rewrite HkD; [exact R16 | unfold hvu_keptD; apply in_map; cbn [In]; lia]).
all: assert (T10 : getr regs5 (Z_to_bv 5 10) = w64 (hvu_entA cx m))
  by (rewrite Hk5; [exact SA | unfold hvu_q2b_kept; apply in_map; cbn [In]; lia]).
all: assert (T24 : getr regs5 (Z_to_bv 5 24) = w64 (Layout.ENT_SIZE * (Z.of_nat m + 1)))
  by (rewrite Hk5; [exact S24 | unfold hvu_q2b_kept; apply in_map; cbn [In]; lia]).
all: assert (Hb5 : @hqu_base3 fx rc SK rsegs B MT cx fx2 r hqu_shX ly2 S2 W2 regs5 mem2 md5)
  by exact (hvu_base3_regs B MT cx fx2 r hqu_shX ly2 S2 W2 regs2 mem2 md2 regs5 md5 Hb3 HJ5 Hio25 H234).
- (* the Float arm: the entry's type is POD_FLOAT *)
  assert (Hty6 : Model.e_type v = Model.POD_FLOAT)
    by (apply (proj1 (hvm_sx_eq (Model.e_type v) 6 Ht ltac:(lia))); exact E6).
  apply (HFA fx2 ly2 S2 W2 regs5 mem2 md5 k v ch p cs keys rf).
  split; [exact Hb5|].
  split.
  { unfold hsu_at_cx.
    assert (HatF : hsu_at rsegs (w_H W2) mem2 regs5 (x_e rsegs cx)
      ((LReg 10, hvu_entA cx m) :: (LReg 13, e_pp (x_e rsegs cx) + Layout.OFF_ENT + 4)
       :: (LReg 24, Layout.ENT_SIZE * (Z.of_nat m + 1)) :: hvu_L cx m ch p)).
    { apply Forall_cons; [cbn [fst snd hd_at]; exact T10|].
      apply Forall_cons; [cbn [fst snd hd_at]; exact Q13|].
      apply Forall_cons; [cbn [fst snd hd_at]; exact T24 | exact HatD]. }
    hvu_subF HatF. }
  split; [exact Hf1|]. split; [exact Hf2|]. split; [exact Hf3|]. split; [exact Hlive|].
  split; [exact Ham|]. split; [exact Hkey|]. split; [exact Hty6|].
  split; [exact Hpair|]. split; [exact Hkcs | exact Hx].
- (* the Int arm: the entry's type is POD_INT *)
  assert (Hty4 : Model.e_type v = Model.POD_INT)
    by (apply (proj1 (hvm_sx_eq (Model.e_type v) 4 Ht ltac:(lia))); exact E4).
  assert (T11 : getr regs5 (Z_to_bv 5 11) = w64 (hvu_entA cx m + 4))
    by (rewrite Q11b; rewrite HAe; unfold Layout.OFF_ENT, Layout.ENT_SIZE; f_equal; lia).
  eapply SRr_bind.
  { eapply (hvu_q6a (fx := fx2) B);
  try first [ exact HJ5 | exact T9 | exact T10 | exact T11 | exact T27 | exact HR16 | exact Hra4 | exact HAapp | exact Vs ];
  try (unfold hvu_entA, Layout.OFF_ENT, Layout.ENT_SIZE in * ); lia. }
  intros W6 c6 _ [(Hs4 & -> & regs6 & md6 & -> & HJ6 & Hio6 & Hk6 & _)
                | (Hs4 & -> & regs6 & md6 & -> & HJ6 & Hio6 & Hk6 & _)].
  + apply (HRF fx2 ly2 S2 W2 regs6 mem2 md6 k v Headamp.REFUSE_OUT_OF_RANGE cs keys rf).
    assert (HkD6 : forall r0, In r0 hvu_keptD -> getr regs6 r0 = getr regs2 r0)
      by (intros r0 Hr0; rewrite (Hk6 r0 ltac:(revert Hr0; unfold hvu_keptD, hvu_q6a_kept; hvu_incl));
          exact (HkD r0 Hr0)).
    split.
    { apply (hvu_base3_regs B MT cx fx2 r hqu_shX ly2 S2 W2 regs2 mem2 md2 regs6 md6 Hb3 HJ6
        (same_io_trans _ _ _ Hio25 Hio6)).
      intros q Hq. apply HkD6. destruct Hq as [->|[->| ->]]; unfold hvu_keptD; apply in_map; cbn [In]; lia. }
    split.
    { unfold hsu_at_cx.
      assert (HatR : hsu_at rsegs (w_H W2) mem2 regs6 (x_e rsegs cx) (hvu_L cx m ch p))
        by (apply (hvu_at_keep _ _ _ _ _ HatL regs6 hvu_keptD HkD6); vm_compute; reflexivity).
      hvu_subF HatR. }
    split; [exact Hf1|]. split; [exact Hf2|]. split; [exact Hf3|]. split; [exact Hlive|].
    split; [exact Ham|].
    split; [apply (hvm_cell_inl k v ch p Hkey); left; rewrite (hvm_cv_small v Hvwf ltac:(lia)); lia|].
    split; [right; reflexivity|]. split; [exact Hpair | exact Hx].
  + assert (U9 : getr regs6 (Z_to_bv 5 9) = w64 (e_R (x_e rsegs cx)))
      by (rewrite Hk6; [exact T9 | unfold hvu_q6a_kept; apply in_map; cbn [In]; lia]).
    assert (U27 : getr regs6 (Z_to_bv 5 27) = w64 SHADOW_OFF)
      by (rewrite Hk6; [exact T27 | unfold hvu_q6a_kept; apply in_map; cbn [In]; lia]).
    assert (U16 : getr regs6 (Z_to_bv 5 16) = w64 p)
      by (rewrite Hk6; [exact T16 | unfold hvu_q6a_kept; apply in_map; cbn [In]; lia]).
    assert (U24 : getr regs6 (Z_to_bv 5 24) = w64 (Layout.ENT_SIZE * (Z.of_nat m + 1)))
      by (rewrite Hk6; [exact T24 | unfold hvu_q6a_kept; apply in_map; cbn [In]; lia]).
    eapply SRr_bind.
    { eapply (hvu_q6b (fx := fx2) B);
  try first [ exact HJ6 | exact U9 | exact U16 | exact U24 | exact U27 | exact HR16 | exact Ce0 | (intros a Ha; apply Hpres; lia) ];
  try (unfold hvu_entA, Layout.OFF_ENT, Layout.ENT_SIZE in * ); lia. }
    intros W7 c7 _ (-> & regs7 & mem7 & md7 & -> & HJ7 & Hio7 & Hk7 & KE7 & (Q10b & C90)).
    assert (V9 : getr regs7 (Z_to_bv 5 9) = w64 (e_R (x_e rsegs cx)))
      by (rewrite Hk7; [exact U9 | unfold hvu_q6b_kept; apply in_map; cbn [In]; lia]).
    assert (V27 : getr regs7 (Z_to_bv 5 27) = w64 SHADOW_OFF)
      by (rewrite Hk7; [exact U27 | unfold hvu_q6b_kept; apply in_map; cbn [In]; lia]).
    assert (V24 : getr regs7 (Z_to_bv 5 24) = w64 (Layout.ENT_SIZE * (Z.of_nat m + 1)))
      by (rewrite Hk7; [exact U24 | unfold hvu_q6b_kept; apply in_map; cbn [In]; lia]).
    assert (V10 : getr regs7 (Z_to_bv 5 10) = w64 (hvu_entA cx m + 8))
      by (rewrite Q10b; rewrite HAe; unfold Layout.OFF_ENT, Layout.ENT_SIZE; f_equal; lia).
    assert (KM7 : forall a, 0 <= a < 2 ^ 64 -> ~ hvu_wr cx a ->
      aview rsegs (w_H W2) mem7 a = aview rsegs (w_H W2) mem2 a) by exact KE7.
    assert (Ce8' : val_mem rsegs (mrestrict (w_H W2) mem7) (e_R (x_e rsegs cx) + 0xe8) 8
      ((e_pp (x_e rsegs cx) + Layout.OFF_ENT + 8) mod 2 ^ 64)).
    { apply (val_mem_kept rsegs (w_H W2) (w_H W2) mem2 mem7 _ 8 _); [|exact Ce8].
      intros j Hj. change (Z.of_nat 8) with 8 in Hj. apply KM7; [lia | unfold hvu_wr; lia]. }
    assert (Vb7 : val_mem rsegs (mrestrict (w_H W2) mem7) (hvu_entA cx m + 8) 4
      (Cursor.rd32 (Model.e_body v))).
    { apply (val_mem_kept rsegs (w_H W2) (w_H W2) mem2 mem7 _ 4 _); [|exact Vb].
      intros j Hj. change (Z.of_nat 4) with 4 in Hj. apply KM7;
        [unfold hvu_entA, Layout.OFF_ENT, Layout.ENT_SIZE in * ; lia
        | unfold hvu_wr, hvu_entA, Layout.OFF_ENT, Layout.ENT_SIZE in * ; lia]. }
    assert (Hra8' : range_addressable (aview rsegs (w_H W2) mem7) SHADOW_OFF (hvu_entA cx m + 8) 4).
    { apply (HPgMem.hm_ra_kept rsegs (w_H W2) mem2 (w_H W2) mem7 _ _ _ Hra8). intros y Hy.
      assert (Hd0 : 0 <= y / 8) by (apply Z.div_pos;
        [unfold hvu_entA, Layout.OFF_ENT, Layout.ENT_SIZE in * ; lia | lia]).
      assert (Hd1 : y / 8 <= 17592184995840) by (apply Z.div_le_upper_bound;
        [lia | unfold hvu_entA, Layout.OFF_ENT, Layout.ENT_SIZE in * ; lia]).
      apply KM7; unfold shadow_of_addr, SHADOW_OFF, hvu_wr in * ; lia. }
    eapply SRr_bind.
    { eapply (hvu_q7 (fx := fx2) B);
  try first [ exact HJ7 | exact V9 | exact V10 | exact V24 | exact V27 | exact HR16 | exact Hra8' | exact Ce8' ];
  try (unfold hvu_entA, Layout.OFF_ENT, Layout.ENT_SIZE in * ); lia. }
    intros W8 c8 _ (-> & regs8 & md8 & -> & HJ8 & Hio8 & Hk8 & Q24b).
    assert (W24 : getr regs8 (Z_to_bv 5 24) = w64 (hvu_entA cx m + 8))
      by (rewrite Q24b; rewrite HAe; unfold Layout.OFF_ENT, Layout.ENT_SIZE; f_equal; lia).
    eapply SRr_bind.
    { eapply (hvu_q8 (fx := fx2) B);
  try first [ exact HJ8 | exact W24 | exact Vb7 ];
  try (unfold hvu_entA, Layout.OFF_ENT, Layout.ENT_SIZE in * ); lia. }
    intros W9 c9 _ [(Hle & -> & regs9 & md9 & -> & HJ9 & Hio9 & Hk9 & Q18)
                  | (Hgt & -> & regs9 & md9 & -> & HJ9 & Hio9 & Hk9 & _)].
    * assert (HkD9 : forall r0, In r0 hvu_keptD -> getr regs9 r0 = getr regs2 r0).
      { intros r0 Hr0.
        rewrite (Hk9 r0 ltac:(revert Hr0; unfold hvu_keptD, hvu_q8_kept; hvu_incl)).
        rewrite (Hk8 r0 ltac:(revert Hr0; unfold hvu_keptD, hvu_q4_kept; hvu_incl)).
        rewrite (Hk7 r0 ltac:(revert Hr0; unfold hvu_keptD, hvu_q6b_kept; hvu_incl)).
        rewrite (Hk6 r0 ltac:(revert Hr0; unfold hvu_keptD, hvu_q6a_kept; hvu_incl)).
        exact (HkD r0 Hr0). }
      assert (Hio29 : same_io md2 md9)
        by exact (same_io_trans _ _ _ Hio25 (same_io_trans _ _ _ Hio6
                   (same_io_trans _ _ _ Hio7 (same_io_trans _ _ _ Hio8 Hio9)))).
      apply (HTAIL fx2 ly2 S2 W2 regs9 mem7 md9 k v ch p (Cursor.rd32 (Model.e_body v)) cs keys rf).
      split.
      { apply (hvu_base3_run cx r ev fx2 ly2 S2 W2 regs2 mem2 md2 regs9 mem7 md9 HS Hb3 HJ9 Hio29);
        [intros q Hq; apply HkD9; destruct Hq as [->|[->| ->]]; unfold hvu_keptD; apply in_map; cbn [In]; lia
        | exact KM7]. }
      split.
      { unfold hsu_at_cx.
        assert (HatT : hsu_at rsegs (w_H W2) mem7 regs9 (x_e rsegs cx)
          ((LReg 18, Cursor.rd32 (Model.e_body v)) :: (LCell XR 0x90, p) :: hvu_L cx m ch p)).
        { apply Forall_cons; [cbn [fst snd hd_at]; exact Q18|].
          apply Forall_cons; [cbn [fst snd hd_at]; exact C90|].
          apply (hvu_at_carry cx W2 mem2 mem7 regs2 regs9 hvu_keptD _ HatL KM7 HkD9
            ltac:(vm_compute; reflexivity)); lia. }
        hvu_subF HatT. }
      split; [exact Hf1|]. split; [exact Hf2|]. split; [exact Hf3|]. split; [exact Hlive|].
      split; [exact Ham|]. split; [exact Hkey|].
      split; [rewrite (hvm_cv_int v Hvwf Hty4 ltac:(lia)), (proj2 (Z.leb_le _ _) Hle); reflexivity|].
      split; [lia|]. split; [exact Hpair|].
      split; [exact Hkcs | exact (hvu_x_kept cx W2 mem2 mem7 cs (keys + 1) rf Hpre Hx KM7)].
    * assert (HkD9 : forall r0, In r0 hvu_keptD -> getr regs9 r0 = getr regs2 r0).
      { intros r0 Hr0.
        rewrite (Hk9 r0 ltac:(revert Hr0; unfold hvu_keptD, hvu_q8_kept; hvu_incl)).
        rewrite (Hk8 r0 ltac:(revert Hr0; unfold hvu_keptD, hvu_q4_kept; hvu_incl)).
        rewrite (Hk7 r0 ltac:(revert Hr0; unfold hvu_keptD, hvu_q6b_kept; hvu_incl)).
        rewrite (Hk6 r0 ltac:(revert Hr0; unfold hvu_keptD, hvu_q6a_kept; hvu_incl)).
        exact (HkD r0 Hr0). }
      assert (Hio29 : same_io md2 md9)
        by exact (same_io_trans _ _ _ Hio25 (same_io_trans _ _ _ Hio6
                   (same_io_trans _ _ _ Hio7 (same_io_trans _ _ _ Hio8 Hio9)))).
      apply (HRF fx2 ly2 S2 W2 regs9 mem7 md9 k v Headamp.REFUSE_OUT_OF_RANGE cs keys rf).
      split.
      { apply (hvu_base3_run cx r ev fx2 ly2 S2 W2 regs2 mem2 md2 regs9 mem7 md9 HS Hb3 HJ9 Hio29);
        [intros q Hq; apply HkD9; destruct Hq as [->|[->| ->]]; unfold hvu_keptD; apply in_map; cbn [In]; lia
        | exact KM7]. }
      split.
      { unfold hsu_at_cx.
        assert (HatR : hsu_at rsegs (w_H W2) mem7 regs9 (x_e rsegs cx) (hvu_L cx m ch p))
          by (apply (hvu_at_carry cx W2 mem2 mem7 regs2 regs9 hvu_keptD _ HatL KM7 HkD9
               ltac:(vm_compute; reflexivity)); lia).
        hvu_subF HatR. }
      split; [exact Hf1|]. split; [exact Hf2|]. split; [exact Hf3|]. split; [exact Hlive|].
      split; [exact Ham|].
      split.
      { apply (hvm_cell_inl k v ch p Hkey). left.
        rewrite (hvm_cv_int v Hvwf Hty4 ltac:(lia)), (proj2 (Z.leb_gt _ _) Hgt). lia. }
      split; [right; reflexivity|].
      split; [exact Hpair | exact (hvu_x_kept cx W2 mem2 mem7 cs (keys + 1) rf Hpre Hx KM7)].
- (* the Bool arm: the entry's type is POD_BOOL *)
  assert (Hty2 : Model.e_type v = Model.POD_BOOL)
    by (apply (proj1 (hvm_sx_eq (Model.e_type v) 2 Ht ltac:(lia))); exact E2).
  assert (T11 : getr regs5 (Z_to_bv 5 11) = w64 (hvu_entA cx m + 4))
    by (rewrite Q11b; rewrite HAe; unfold Layout.OFF_ENT, Layout.ENT_SIZE; f_equal; lia).
  eapply SRr_bind.
  { eapply (hvu_q3a (fx := fx2) B);
  try first [ exact HJ5 | exact T9 | exact T10 | exact T11 | exact T27 | exact HR16 | exact Hra4 | exact HAapp | exact Vs ];
  try (unfold hvu_entA, Layout.OFF_ENT, Layout.ENT_SIZE in * ); lia. }
  intros W6 c6 _ [(Hs4 & -> & regs6 & md6 & -> & HJ6 & Hio6 & Hk6 & _)
                | (Hs4 & -> & regs6 & md6 & -> & HJ6 & Hio6 & Hk6 & _)].
  + apply (HRF fx2 ly2 S2 W2 regs6 mem2 md6 k v Headamp.REFUSE_OUT_OF_RANGE cs keys rf).
    assert (HkD6 : forall r0, In r0 hvu_keptD -> getr regs6 r0 = getr regs2 r0)
      by (intros r0 Hr0; rewrite (Hk6 r0 ltac:(revert Hr0; unfold hvu_keptD, hvu_q3a_kept; hvu_incl));
          exact (HkD r0 Hr0)).
    split.
    { apply (hvu_base3_regs B MT cx fx2 r hqu_shX ly2 S2 W2 regs2 mem2 md2 regs6 md6 Hb3 HJ6
        (same_io_trans _ _ _ Hio25 Hio6)).
      intros q Hq. apply HkD6. destruct Hq as [->|[->| ->]]; unfold hvu_keptD; apply in_map; cbn [In]; lia. }
    split.
    { unfold hsu_at_cx.
      assert (HatR : hsu_at rsegs (w_H W2) mem2 regs6 (x_e rsegs cx) (hvu_L cx m ch p))
        by (apply (hvu_at_keep _ _ _ _ _ HatL regs6 hvu_keptD HkD6); vm_compute; reflexivity).
      hvu_subF HatR. }
    split; [exact Hf1|]. split; [exact Hf2|]. split; [exact Hf3|]. split; [exact Hlive|].
    split; [exact Ham|].
    split; [apply (hvm_cell_inl k v ch p Hkey); left; rewrite (hvm_cv_small v Hvwf ltac:(lia)); lia|].
    split; [right; reflexivity|]. split; [exact Hpair | exact Hx].
  + assert (U9 : getr regs6 (Z_to_bv 5 9) = w64 (e_R (x_e rsegs cx)))
      by (rewrite Hk6; [exact T9 | unfold hvu_q3a_kept; apply in_map; cbn [In]; lia]).
    assert (U27 : getr regs6 (Z_to_bv 5 27) = w64 SHADOW_OFF)
      by (rewrite Hk6; [exact T27 | unfold hvu_q3a_kept; apply in_map; cbn [In]; lia]).
    assert (U24 : getr regs6 (Z_to_bv 5 24) = w64 (Layout.ENT_SIZE * (Z.of_nat m + 1)))
      by (rewrite Hk6; [exact T24 | unfold hvu_q3a_kept; apply in_map; cbn [In]; lia]).
    eapply SRr_bind.
    { eapply (hvu_q3b (fx := fx2) B);
  try first [ exact HJ6 | exact U9 | exact U24 | exact Ce0 ];
  try (unfold hvu_entA, Layout.OFF_ENT, Layout.ENT_SIZE in * ); lia. }
    intros W7 c7 _ (-> & regs7 & md7 & -> & HJ7 & Hio7 & Hk7 & Q10b).
    assert (V9 : getr regs7 (Z_to_bv 5 9) = w64 (e_R (x_e rsegs cx)))
      by (rewrite Hk7; [exact U9 | unfold hvu_q3b_kept; apply in_map; cbn [In]; lia]).
    assert (V27 : getr regs7 (Z_to_bv 5 27) = w64 SHADOW_OFF)
      by (rewrite Hk7; [exact U27 | unfold hvu_q3b_kept; apply in_map; cbn [In]; lia]).
    assert (V24 : getr regs7 (Z_to_bv 5 24) = w64 (Layout.ENT_SIZE * (Z.of_nat m + 1)))
      by (rewrite Hk7; [exact U24 | unfold hvu_q3b_kept; apply in_map; cbn [In]; lia]).
    assert (V10 : getr regs7 (Z_to_bv 5 10) = w64 (hvu_entA cx m + 8))
      by (rewrite Q10b; rewrite HAe; unfold Layout.OFF_ENT, Layout.ENT_SIZE; f_equal; lia).
    eapply SRr_bind.
    { eapply (hvu_q4 (fx := fx2) B);
  try first [ exact HJ7 | exact V9 | exact V10 | exact V24 | exact V27 | exact HR16 | exact Hra8 | exact Ce8 ];
  try (unfold hvu_entA, Layout.OFF_ENT, Layout.ENT_SIZE in * ); lia. }
    intros W8 c8 _ (-> & regs8 & md8 & -> & HJ8 & Hio8 & Hk8 & Q24b).
    assert (W24 : getr regs8 (Z_to_bv 5 24) = w64 (hvu_entA cx m + 8))
      by (rewrite Q24b; rewrite HAe; unfold Layout.OFF_ENT, Layout.ENT_SIZE; f_equal; lia).
    eapply SRr_bind.
    { eapply (hvu_q5 (fx := fx2) B);
  try first [ exact HJ8 | exact W24 | exact Vb ];
  try (unfold hvu_entA, Layout.OFF_ENT, Layout.ENT_SIZE in * ); lia. }
    intros W9 c9 _ (-> & regs9 & md9 & -> & HJ9 & Hio9 & Hk9 & Q18).
    assert (HkD9 : forall r0, In r0 hvu_keptD -> getr regs9 r0 = getr regs2 r0).
    { intros r0 Hr0.
      rewrite (Hk9 r0 ltac:(revert Hr0; unfold hvu_keptD, hvu_q5_kept; hvu_incl)).
      rewrite (Hk8 r0 ltac:(revert Hr0; unfold hvu_keptD, hvu_q4_kept; hvu_incl)).
      rewrite (Hk7 r0 ltac:(revert Hr0; unfold hvu_keptD, hvu_q3b_kept; hvu_incl)).
      rewrite (Hk6 r0 ltac:(revert Hr0; unfold hvu_keptD, hvu_q3a_kept; hvu_incl)).
      exact (HkD r0 Hr0). }
    assert (Hio29 : same_io md2 md9)
      by exact (same_io_trans _ _ _ Hio25 (same_io_trans _ _ _ Hio6
                 (same_io_trans _ _ _ Hio7 (same_io_trans _ _ _ Hio8 Hio9)))).
    pose proof (hvm_cv_bool v Hvwf Hty2 ltac:(lia)) as Hcv.
    rewrite (hvu_snez_eq (Cursor.rd32 (Model.e_body v)) Hbw) in Q18.
    pose proof (hvm_top_bounds p) as Htop.
    assert (Hv01 : 0 <= Headamp.cell_value v <= 1)
      by (rewrite Hcv; destruct (Cursor.rd32 (Model.e_body v) =? 0); lia).
    apply (HCELL fx2 ly2 S2 W2 regs9 mem2 md9 k v ch p (Headamp.cell_value v) cs keys rf).
    split.
    { apply (hvu_base3_regs B MT cx fx2 r hqu_shX ly2 S2 W2 regs2 mem2 md2 regs9 md9 Hb3 HJ9 Hio29).
      intros q Hq. apply HkD9. destruct Hq as [->|[->| ->]]; unfold hvu_keptD; apply in_map; cbn [In]; lia. }
    split.
    { unfold hsu_at_cx.
      assert (HatC : hsu_at rsegs (w_H W2) mem2 regs9 (x_e rsegs cx)
        ((LReg 18, Headamp.cell_value v) :: hvu_L cx m ch p)).
      { apply Forall_cons; [cbn [fst snd hd_at]; rewrite Hcv; exact Q18|].
        apply (hvu_at_keep _ _ _ _ _ HatL regs9 hvu_keptD HkD9); vm_compute; reflexivity. }
      hvu_subF HatC. }
    split; [exact Hf1|]. split; [exact Hf2|]. split; [exact Hf3|]. split; [exact Hlive|].
    split; [exact Ham|].
    split; [apply (hvm_cell_inr k v ch p Hkey); lia|].
    split; [apply hvm_valid; [exact Hch | exact Hp | lia]|].
    split; [exact Hpair|]. split; [exact Hkcs | exact Hx].
- (* the type is none of Bool, Int, Float: the refusal fold *)
  assert (Hcv : Headamp.cell_value v = -1).
  { apply (hvm_cv_other v Hvwf);
    [ intros Hc; apply N2; exact (proj2 (hvm_sx_eq (Model.e_type v) 2 Ht ltac:(lia)) Hc)
    | intros Hc; apply N4; exact (proj2 (hvm_sx_eq (Model.e_type v) 4 Ht ltac:(lia)) Hc)
    | intros Hc; apply N6; exact (proj2 (hvm_sx_eq (Model.e_type v) 6 Ht ltac:(lia)) Hc) ]. }
  apply (HRF fx2 ly2 S2 W2 regs5 mem2 md5 k v Headamp.REFUSE_OUT_OF_RANGE cs keys rf).
  split; [exact Hb5|].
  split; [unfold hsu_at_cx; hvu_subF HatD|].
  split; [exact Hf1|]. split; [exact Hf2|]. split; [exact Hf3|]. split; [exact Hlive|].
  split; [exact Ham|].
  split; [apply (hvm_cell_inl k v ch p Hkey); left; lia|].
  split; [right; reflexivity|]. split; [exact Hpair | exact Hx].
Qed.

End c.

Print Assumptions hvu_disp_B.
