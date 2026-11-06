(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; every address measured on the unstripped twin
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff, the same loaded bytes except .note.gnu.build-id): the step from cut TAIL of the
   piece value of the walk of LLVMFuzzerTestOneInput, lib/AU/HPgM3dBaseU.v hvu_piece_tail_stmt. Proves no function
   (kind: segment lemma).

   THE CODE (TAIL 0x83694 .. 0x8369c, expect_of's range test fuzz_headamp.c:141-142)
     0x83694  sext.w a0,s2          a0 := val (0 <= val <= 255)
     0x83698  ld a6,0x90(s1)        a6 := the param p (R+0x90)
     0x8369c  bgeu s7,a0,0x836e4    top >= val -> CELL 0x836e4; else the refusal fold RF 0x836a0 (a5 = 5)
   No store, no call, no instrumented check: this step writes no byte and changes no float register.

   HOW. hvu_tl_blk is the lane as a block lemma over the machine state at TAIL (the registers as atoms, the cell
   R+0x90 as a read-only region over one extra atom); the engine runs it to the branch, splits, and stops at CELL or
   at RF. hvu_tail_B reads the TAIL cut, runs hvu_tl_blk at the run's own float state, and builds the CELL cut
   (expect_cell gives the cell (ch, p, val), which is valid) or the RF cut (expect_cell refuses with
   OUT_OF_RANGE). *)
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

(* ================================ the entry state ================================ *)
(* the registers the lane does not write: all but a0 and a6 *)
Definition hvu_tl_kept : list (bv 5) :=
map (Z_to_bv 5) [1; 2; 3; 4; 5; 6; 7; 8; 9; 11; 12; 13; 14; 15; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29;
  30; 31].

(* atom 32 is the token base of the kit's no-check runs (HPgSteps.rt_extra); atom 33 is the cell R+0x90 *)
Definition hvu_tl_R : YP09.region := YP09.mkRegion (Some 9%nat) 0x90 0x98 0 0
  [YP09.mkChunk 0x90 (CVal 8 (SOff 33 0))].
Definition hvu_tl_ss0 : sstate := mkSS HVU_TAIL sr_atoms [hvu_tl_R] None (mkFacts [] [] []).
Definition hvu_tl_extra (p : Z) : list word := [Z_to_bv 64 HPgSteps.SBr; Z_to_bv 64 p].

(* what both arms compute *)
Definition hvu_tl_RR (val p : Z) (regs2 : bvmap 5 word) : Prop :=
getr regs2 (Z_to_bv 5 10) = w64 val /\ getr regs2 (Z_to_bv 5 16) = w64 p.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.

Lemma hvu_tl_blk : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
(R val top p : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs (Z_to_bv 5 9) = w64 R -> getr regs (Z_to_bv 5 18) = w64 val -> getr regs (Z_to_bv 5 23) = w64 top ->
0 <= R -> R + 0x98 <= 2 ^ 64 -> 0 <= val <= 255 -> 0 <= top < 2 ^ 63 -> 0 <= p < 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x90) 8 (p mod 2 ^ 64) ->
SRr rsegs W (cfg_at rsegs HVU_TAIL regs memc mdc)
(fun W2 c2 =>
 (val <= top /\
  hvu_post0 B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HQU_CELL hvu_tl_kept (hvu_tl_RR val p) W2 c2) \/
 (top < val /\
  hvu_post0 B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HQU_RF hvu_tl_kept (hvu_tl_RR val p) W2 c2)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R val top p HJ H9 H18 H23 HR0 HR1 Hv Ht Hp V90.
pose proof HPgSteps.img_wx as Hwx. pose proof HPgSteps.img_segs_low as Hsegs.
pose proof (AR_laws_ok rsegs B) as LAWS.
remember (hvu_tl_extra p) as ex eqn:Hex.
assert (EA : forall (m : nat) (r : bv 5), Z.of_nat m = bv_unsigned r -> ew (Ereg regs ex) m = getr regs r)
  by (intros m r Hm; exact (ew_Ereg_nat regs _ m r Hm)).
assert (E9 : ew (Ereg regs ex) 9 = Z_to_bv 64 R) by (rewrite (EA 9%nat (Z_to_bv 5 9) eq_refl); exact H9).
assert (E18 : ew (Ereg regs ex) 18 = Z_to_bv 64 val) by (rewrite (EA 18%nat (Z_to_bv 5 18) eq_refl); exact H18).
assert (E23 : ew (Ereg regs ex) 23 = Z_to_bv 64 top) by (rewrite (EA 23%nat (Z_to_bv 5 23) eq_refl); exact H23).
assert (E33 : ew (Ereg regs ex) 33 = Z_to_bv 64 p) by (subst ex; exact (ew_Ereg_extra regs _ 1)).
assert (HS : st_ok rsegs (Ereg regs ex) hvu_tl_ss0
  (restrict (w_H W) (mkst regs (Z_to_bv 64 HVU_TAIL) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold hvu_tl_ss0. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    apply (HPgMem.hm_ro_region rsegs _ (w_H W) memc 9 R); [rewrite E9; apply unsigned_lit_small; lia | lia | lia |].
    constructor; [|constructor].
    exact (hvu_slot_chunk _ _ _ R 0x90 p 33 E33 V90).
  - cbn. tauto.
  - split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. exact I. }
assert (SHOK : sh_ok rsegs HPgSteps.RTBx [] (Ereg regs ex) (mrestrict (w_H W) memc)) by constructor.
remember (Ereg regs ex) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs ex) E) by (subst E; apply env_agree_refl).
clear HE EA Hex.
unfold cfg_at. change (w64 HVU_TAIL) with (Z_to_bv 64 HVU_TAIL).
(* 0x83694 .. 0x83698, stop at the `bgeu` *)
hvu_run HPgSteps.RTBspan awr_ok_tac. hvu_mem.
hvu_branch HPgSteps.RTBspan Hc.
all: assert (Ua0 : U E (SAluw ALU_ADD (SOff 18 0) (SLit 0)) = val)
  by (apply hvu_U_sextw; [apply (U_atom E 18 val E18); lia | lia]).
all: rewrite !hvu_denot0, E23, (hvu_denot_of_U E _ val Ua0), hvu_bgeu in Hc by lia.
- (* taken: top >= val, to CELL 0x836e4 *)
  hvu_run_to HPgSteps.RTBspan awr_ok_tac HQU_CELL. hvu_mem.
  apply SRr_ret; left. split; [apply negb_true_iff, Z.ltb_ge in Hc; exact Hc|].
  hvu_post0_tac B hvu_tl_kept.
  unfold hvu_tl_RR. lazymatch goal with HS : st_ok _ ?E' ?ss' (restrict _ ?ms) |- _ =>
    rewrite !(st_ok_restrict_reg rsegs _ E' ss' ms _ HS) end.
  split.
  + hvu_sv. exact (hvu_denot_of_U E _ val Ua0).
  + hvu_sv. rewrite hvu_denot0, E33. reflexivity.
- (* not taken: top < val, to RF 0x836a0 *)
  hvu_run_to HPgSteps.RTBspan awr_ok_tac HQU_RF. hvu_mem.
  apply SRr_ret; right. split; [apply negb_false_iff, Z.ltb_lt in Hc; exact Hc|].
  hvu_post0_tac B hvu_tl_kept.
  unfold hvu_tl_RR. lazymatch goal with HS : st_ok _ ?E' ?ss' (restrict _ ?ms) |- _ =>
    rewrite !(st_ok_restrict_reg rsegs _ E' ss' ms _ HS) end.
  split.
  + hvu_sv. exact (hvu_denot_of_U E _ val Ua0).
  + hvu_sv. rewrite hvu_denot0, E33. reflexivity.
Qed.
End d.
End b.

(* ================================ the cuts ================================ *)
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.

Theorem hvu_tail_B : @hvu_piece_tail_stmt fx rc SK B MT.
Proof.
unfold hvu_piece_tail_stmt. intros cx POST r ev at0 m HS HCELL HRF.
unfold hvu_from_TAIL. intros fx2 ly2 S2 W2 regs2 mem2 md2 k v ch p val cs keys rf Hcut.
destruct Hcut as (Hb3 & Hat & Hf1 & Hf2 & Hf3 & Hlive & Ham & Hkey & Hcv & Hval & Hpair & Hkcs & Hx).
pose proof Hb3 as (Hcore & _).
pose proof Hcore as (HJ & _).
pose proof (hvu_stack B cx (hi_shA headamp_himg_B) (hvu_start_pre B cx r ev HS)) as (_ & _ & _ & _ & _ & HRr & _).
pose proof (hvm_top_bounds p) as Htop.
pose proof (hvm_key_cell _ ch p Hkey) as (Hch & Hp).
assert (Hp3 : 0 <= p < 3)
  by (unfold Headamp.HA_PHANTOM, Headamp.HA_PAD, Headamp.HA_SENS in Hp; destruct Hp as [->|[->| ->]]; lia).
unfold hsu_at_cx in Hat.
pose proof (hvu_at_get _ _ _ _ _ 9 (e_R (x_e rsegs cx)) Hat ltac:(hvu_in)) as R9.
pose proof (hvu_at_get _ _ _ _ _ 18 val Hat ltac:(hvu_in)) as R18.
pose proof (hvu_at_get _ _ _ _ _ 23 (hvm_top p) Hat ltac:(hvu_in)) as R23.
pose proof (hvu_at_cell _ _ _ _ _ XR 0x90 p Hat ltac:(hvu_in)) as C90.
cbn [hd_xv] in C90.
eapply SRr_bind.
{ apply (hvu_tl_blk (fx := fx2) B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs2 (e_R (x_e rsegs cx)) val (hvm_top p) p
    HJ R9 R18 R23); try lia; exact C90. }
intros W3 c3 _ [(Hle & -> & regs3 & md3 & -> & HJ3 & Hio3 & Hk3 & HRR)
              | (Hgt & -> & regs3 & md3 & -> & HJ3 & Hio3 & Hk3 & HRR)].
- (* CELL: the value is in range *)
  destruct HRR as (Q10 & Q16).
  pose proof (hvu_at_keep _ _ _ _ _ Hat regs3 hvu_tl_kept Hk3 ltac:(vm_compute; reflexivity)) as Hat3.
  apply (HCELL fx2 ly2 S2 W2 regs3 mem2 md3 k v ch p val cs keys rf).
  split.
  { apply (hvu_base3_regs B MT cx fx2 r hqu_shX ly2 S2 W2 regs2 mem2 md2 regs3 md3 Hb3 HJ3 Hio3).
    intros q Hq. destruct Hq as [->|[->| ->]]; apply Hk3; unfold hvu_tl_kept; hvu_kin. }
  split.
  { unfold hsu_at_cx. apply hvu_at_app; split; [hvu_sub Hat3|].
    apply hvu_at_app; split; [hvu_sub Hat3|].
    apply hvu_at_app; split; [hvu_sub Hat3|].
    apply hvu_at_app; split; [hvu_sub Hat3|].
    unfold hsu_at. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [hd_at fst snd].
    - exact (hvu_at_get _ _ _ _ _ 18 val Hat3 ltac:(hvu_in)).
    - exact (hvu_at_get _ _ _ _ _ 21 ch Hat3 ltac:(hvu_in)).
    - exact Q16. }
  split; [exact Hf1|]. split; [exact Hf2|]. split; [exact Hf3|]. split; [exact Hlive|].
  split; [exact Ham|].
  split; [rewrite <- Hcv; apply (hvm_cell_inr k v ch p Hkey); lia|].
  split; [apply (hvm_valid ch p val Hch Hp); lia|].
  split; [exact Hpair|]. split; [exact Hkcs | exact Hx].
- (* RF: the value is above the param's top *)
  pose proof (hvu_at_keep _ _ _ _ _ Hat regs3 hvu_tl_kept Hk3 ltac:(vm_compute; reflexivity)) as Hat3.
  apply (HRF fx2 ly2 S2 W2 regs3 mem2 md3 k v Headamp.REFUSE_OUT_OF_RANGE cs keys rf).
  split.
  { apply (hvu_base3_regs B MT cx fx2 r hqu_shX ly2 S2 W2 regs2 mem2 md2 regs3 md3 Hb3 HJ3 Hio3).
    intros q Hq. destruct Hq as [->|[->| ->]]; apply Hk3; unfold hvu_tl_kept; hvu_kin. }
  split.
  { unfold hsu_at_cx. apply hvu_at_app; split; [hvu_sub Hat3|].
    apply hvu_at_app; split; [hvu_sub Hat3|].
    apply hvu_at_app; split; [hvu_sub Hat3|].
    apply hvu_at_app; split; [hvu_sub Hat3|].
    hvu_sub Hat3. }
  split; [exact Hf1|]. split; [exact Hf2|]. split; [exact Hf3|]. split; [exact Hlive|].
  split; [exact Ham|].
  split; [apply (hvm_cell_inl k v ch p Hkey); right; lia|].
  split; [right; reflexivity|].
  split; [exact Hpair | exact Hx].
Qed.
End c.

Print Assumptions hvu_tail_B.
