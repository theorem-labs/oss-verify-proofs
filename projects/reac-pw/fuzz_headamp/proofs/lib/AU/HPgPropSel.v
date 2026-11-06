(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/cgif/cgif_file_fuzzer/lib/A/AC8j.v at c8557374ad2e (st_ok_region_nth, field_of_region, as pa_i_region_nth over a restricted state and pa_i_field) and proofs/reac-pw/fuzz_role/lib/Reusable/YCbq.v at a0d3fb0309b (aj_intrin_at, as pa_i_memset_at: at OSet on rsegs, its post adds same_io from the contract's same_but_materialized); the rest of the file is new: the block lemma pa_int7 of LLVMFuzzerTestOneInput's shape-7 Int pod block and its helpers. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgPropIntB.v at a529a88a6181 (the block lemma pa_int7 and its helpers) and the piece pa_piece_int7 of proofs/reac-pw/fuzz_role/lib/A/RPgProp.v at the same commit, for reac-pw/fuzz_rate image A: rate's pcs (SEL7 0x80e6c, the memset call 0x80fec to 0x51cfc with return 0x80ff0, LATCH7 0x82530), registers (s6 / s7 / s2 for role's s4 / s5 / s7) and real-frame cells (i at R+0xf8, -0x3ffd at R+0x130, -0x4001 at R+0x118 and in s10); rate's block keeps what is left of the input (s8) in s10 across the pad and restores s8 and s10 at its end, so both join the clobbered set and the block's relation states their end values; the call is lib/A/RtPgSteps.v rts_intrin_at (in place of pa_i_memset_at), the region lemma its rts_region_nth (in place of pa_i_region_nth); the block post is RtPgSteps' rts_post; the cut lists of the piece are lib/A/RtPgSeg.v's. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgPropIntB.v, with its module paths changed; 334 of its 388 lines of code are new or changed and 536 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgPropSelB.v at a529a88a618 (pa_sel, its two
   entry states and pa_s_div8, as hbp_sel / hbp_sel1 / hbp_sel0 / hbp_s_div8) and proofs/reac-pw/fuzz_role/lib/A/RPgProp.v
   at a529a88a618 (pa_piece_sel, as hbp_piece_sel) for reac-pw/fuzz_headamp's image B: the walk is image B's own code
   (the cursor in s2 and what is left in t3 instead of the cells R+0xc8 / R+0xf8, the UBSan cursor test 0x8149c, the
   out-of-line slow block 0x82afc, the shape flag R+0xf8 read after the byte, no store and no pp->len read), the post
   HPgSteps.hdu_blk_postE, the cut states of lib/AU/HPgSeg.v. *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; every address below is measured on its
   unstripped twin sha256 1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff): the selector of one
   property of the property loop of LLVMFuzzerTestOneInput (0x80c40, pod.h:399-401 with fuzz.h:37-43), N 0x81494 ->
   SEL7 0x814d4 (shape 7) / SELK 0x81590, as the block lemma hbp_sel and the piece lemma hbp_piece_sel :
   HPgSeg.hsu_piece_W4_sel_stmt at headamp_himg_B / headamp_bld_B. Proves no function (kind: segment lemma).
     0x81494 beqz t3,0x814c4                      no byte left
     0x81498 addi t2,s2,1; 0x8149c bltu s10,t2    the UBSan cursor test (s10 = 1): taken, as the cursor is >= 1;
                                                  its other arm 0x814a0 j 0x83a14 (the trap) is not reached
     0x814a4 srli a0,s2,3; add a0,a0,s11; lb a0,0(a0)   the shadow byte s of the cursor (s11 = K)
     0x814b0 beqz a0,0x814b8; 0x814b4 j 0x82afc   s <> 0: 0x82afc andi a1,s2,7; bge a1,a0,0x82b08 (-> 0x83d28, the
                                                  report, not reached: cursor mod 8 < s by saddr_ok); j 0x814b8
     0x814b8 lbu a1,0(s2); addi t3,t3,-1; j 0x814cc      the byte
     0x814c4 li a1,0; mv t2,s2                    nothing left: the byte is 0, the cursor stays (fuzz.h:37-43)
     0x814cc ld a0,0xf8(s1); 0x814d0 beqz a0,0x81590    R+0xf8 = (sh = 7): 0 -> SELK, else SEL7
   The walk splits on t3 = 0 before its entry state. With t3 > 0 the input byte b is a region based at the cursor's
   atom (s2) and its shadow byte s a region based at a fresh atom (the cursor's shadow address, tied to the cursor by
   an alias fact); s = 0 runs on, s <> 0 goes through 0x82afc, whose report arm dies by saddr_ok (hm_ra_slow_bv).
   REGISTERS AND CELLS (for a port by a register / slot map): reads s1 = R, s2 = the cursor, t3 = what is left,
   s10 = 1, s11 = K and the cell R+0xf8; writes a0, a1, t2, t3; no store (the block's write set is empty). At the
   exits t2 is the cursor after the selector byte, t3 what is left after it and a1 the byte (0 when nothing was
   left). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgImgB HPgSteps HPgMem HPgSeg HPgPropKit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Local Arguments x_STK {segs} _.
Local Arguments x_sp0 {segs} _.
Local Arguments x_FP {segs} _.
Local Arguments x_ly {segs} _.
Local Arguments x_S {segs} _.
Local Arguments x_W0 {segs} _.
Local Arguments x_mem0 {segs} _.
Local Arguments x_md0 {segs} _.
Local Arguments x_own {segs} _.
Local Arguments x_k {segs} _.
Local Arguments x_regs {segs} _.
Local Arguments x_lyc {segs} _.
Local Arguments x_Sc {segs} _.
Local Arguments x_W {segs} _.
Local Arguments x_memc {segs} _.
Local Arguments x_mdc {segs} _.
Local Arguments x_RLO {segs} _.
Local Arguments x_RHI {segs} _.
Local Arguments x_e {segs} _.
Local Arguments x_pos {segs} _.

(* ---- the entry states ----
   env slots (hbp_extra): 32 K, 33 f7 = the cell R+0xf8; with bytes left also 34 b = the byte at the cursor,
   35 sa = the cursor's shadow address, 36 s = its shadow byte *)
Definition hbp_s_rf8 : YP09.region :=
YP09.mkRegion (Some 9%nat) 0xf8 0x100 0 0 [ YP09.mkChunk 0xf8 (CVal 8 (SOff 33 0)) ].
Definition hbp_s_rin : YP09.region := YP09.mkRegion (Some 18%nat) 0 1 0 0 [ YP09.mkChunk 0 (CVal 1 (SOff 34 0)) ].
Definition hbp_s_rsh : YP09.region := YP09.mkRegion (Some 35%nat) 0 1 0 0 [ YP09.mkChunk 0 (CVal 1 (SOff 36 0)) ].
(* the cursor (atom 18) and what is left (atom 28) are at least 1 and below 2^63, s10 (atom 26) is 1 *)
Definition hbp_s_G1 : facts := mkFacts
[ (18%nat, mkAF 1 9223372036854775807 0); (26%nat, mkAF 1 1 0); (28%nat, mkAF 1 9223372036854775807 0);
  (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (33%nat, mkAF 0 1 0); (34%nat, mkAF 0 255 0); (36%nat, mkAF 0 7 0) ] []
[ (SAlu ALU_ADD (SAlu ALU_SRL (SOff 18 0) (SLit 3)) (SOff 27 0), SOff 35 0) ].
Definition hbp_s_G0 : facts := mkFacts
[ (28%nat, mkAF 0 0 0); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (33%nat, mkAF 0 1 0) ] [] [].
Definition hbp_ss_sel1 : sstate := mkSS HBP_N sr_atoms [hbp_s_rf8; hbp_s_rin; hbp_s_rsh] None hbp_s_G1.
Definition hbp_ss_sel0 : sstate := mkSS HBP_N sr_atoms [hbp_s_rf8] None hbp_s_G0.

(* x / 8 as an atom lia can use *)
Lemma hbp_s_div8 : forall x, 0 <= x -> 0 <= x / 8 /\ 8 * (x / 8) <= x /\ x < 8 * (x / 8) + 8.
Proof.
intros x Hx. pose proof (Z.div_mod x 8 ltac:(lia)) as D. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as M.
split; [apply Z.div_pos; lia | lia].
Qed.

(* the relation at the exits: t2 = the cursor after the selector byte, t3 = what is left after it, a1 = the byte *)
Definition hbp_sel_R (cur nl b : Z) (W2 : world rsegs) (regs2 : bvmap 5 word) (mem2 : word -> option byte) : Prop :=
getr regs2 7 = w64 (if nl =? 0 then cur else cur + 1) /\
getr regs2 28 = w64 (if nl =? 0 then 0 else nl - 1) /\
getr regs2 11 = w64 (if nl =? 0 then 0 else b).

(* 0x814d0 beqz a0 (the cell R+0xf8, f7 at slot 33): taken -> SELK, else SEL7; run to the target, leaf; the relation
   is left in both goals *)
Ltac hbp_s_fin sh E33 Hf7r extra :=
let Hc7 := fresh "Hc7" in
hbp_branch Hc7; rewrite branch_eq_U, U_SOff, E33, U_SLit, unsigned_lit_small in Hc7 by lia;
rewrite !zcanon_id in Hc7 by (unfold M64; lia); rewrite Z.add_0_r in Hc7;
first [apply (proj1 (Z.eqb_eq _ _)) in Hc7 | apply (proj1 (Z.eqb_neq _ _)) in Hc7];
[ replace (if sh =? 7 then HBP_SEL7 else HBP_SELK) with HBP_SELK
    by (let X := fresh "X" in let Y := fresh "Y" in
        destruct (Z.eqb_spec sh 7) as [X|X];
        [exfalso; destruct Hf7r as [[_ Y]|[Y _]]; [rewrite Y in Hc7; discriminate Hc7 | exact (Y X)] | reflexivity]);
  hbp_run HBP_SELK; hbp_keep hbp_kwr_ro; hbp_leaf extra
| replace (if sh =? 7 then HBP_SEL7 else HBP_SELK) with HBP_SEL7
    by (let X := fresh "X" in let Y := fresh "Y" in
        destruct (Z.eqb_spec sh 7) as [X|X];
        [reflexivity | exfalso; destruct Hf7r as [[Y _]|[_ Y]]; [exact (X Y) | exact (Hc7 Y)]]);
  hbp_run HBP_SEL7; hbp_keep hbp_kwr_ro; hbp_leaf extra ].
(* the relation, bytes left: t2 = s2 + 1, t3 = t3 - 1, a1 = b *)
Ltac hbp_s_rel1 Hnz W18 W28 E34 :=
unfold hbp_sel_R; cbv beta; rewrite Hnz; cbv iota;
hbp_reg (7%bv : bv 5); hbp_reg (28%bv : bv 5); hbp_reg (11%bv : bv 5);
unfold w64; rewrite !denot_lit_U, !U_SOff, W18, W28, E34, !unsigned_lit_small by lia;
rewrite !zcanon_id by (unfold M64; lia);
refine (conj _ (conj _ _)); f_equal; lia.
(* the relation, nothing left: t2 = s2, t3 = 0, a1 = 0 *)
Ltac hbp_s_rel0 W18 W28 :=
unfold hbp_sel_R; cbv beta; rewrite Z.eqb_refl; cbv iota;
hbp_reg (7%bv : bv 5); hbp_reg (28%bv : bv 5); hbp_reg (11%bv : bv 5);
unfold w64; rewrite !denot_lit_U, !U_SOff, ?U_SLit, W18, W28, !unsigned_lit_small by lia;
rewrite !zcanon_id by (unfold M64; lia);
refine (conj _ (conj _ _)); f_equal; try lia.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.

(* the goal of the block, for both entry states *)
Definition hbp_sel_goal STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
  (sh cur nl b : Z) : Prop :=
SRr rsegs W (cfg_at rsegs HBP_N regs memc mdc)
(hdu_blk_postE B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc
 (if sh =? 7 then HBP_SEL7 else HBP_SELK) [7; 10; 11; 28]%bv (fun _ => False) (hbp_sel_R cur nl b)).

(* bytes left: the byte at the cursor is read *)
Lemma hbp_sel1 : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
  (R sh cur nl b : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs 9 = w64 R -> getr regs 18 = w64 cur -> getr regs 28 = w64 nl ->
getr regs 26 = w64 1 -> getr regs 27 = w64 SHADOW_OFF ->
2 ^ 46 <= R -> R + 0x100 <= 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xf8) 8 (if sh =? 7 then 1 else 0) ->
0 < cur -> 0 < nl -> cur + nl <= 2 ^ 63 ->
val_mem rsegs (mrestrict (w_H W) memc) cur 1 b -> 0 <= b < 256 ->
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF cur 1 ->
amem_range cur 1 -> ~ (R + 0xf8 <= cur < R + 0x100) ->
hbp_sel_goal STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs sh cur nl b.
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R sh cur nl b
  HJ H9 H18 H28 H26 H27 HR0 HR1 Vf8 Hcur0 Hnl Hcurn Vb Hb HRAc Hamr HnR.
unfold hbp_sel_goal.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamr.
destruct (hm_ra_cell _ _ _ HRAc) as (s & Hs & Hsok).
destruct (hm_aview_val1 rsegs _ _ _ _ Hs) as (_ & Hs256).
assert (Hs8 : 0 <= s < 8) by (destruct Hsok as [-> | [_ Hs8]]; lia).
set (sa := shadow_of_addr SHADOW_OFF cur) in Hs.
assert (Hsa : sa = 0x7fff8000 + cur / 8) by reflexivity.
pose proof (hbp_s_div8 cur ltac:(lia)) as Hcur8.
remember (if sh =? 7 then 1 else 0) as f7 eqn:Hf7.
assert (Hf7r : (sh = 7 /\ f7 = 1) \/ (sh <> 7 /\ f7 = 0))
  by (subst f7; destruct (Z.eqb_spec sh 7); [left | right]; auto).
clear Hf7.
assert (Hf01 : 0 <= f7 <= 1) by (destruct Hf7r as [[_ ->]|[_ ->]]; lia).
assert (Hnz : (nl =? 0) = false) by (apply Z.eqb_neq; lia).
set (E := Ereg regs (hbp_extra [f7; b; sa; s])).
assert (E9 : bv_unsigned (ew E 9) = R)
  by (unfold E; rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl), H9; unfold w64; apply unsigned_lit_small; lia).
assert (W18 : ew E 18 = Z_to_bv 64 cur) by (unfold E; rewrite (ew_Ereg_nat regs _ 18 18%bv eq_refl), H18; reflexivity).
assert (E18 : bv_unsigned (ew E 18) = cur) by (rewrite W18; apply unsigned_lit_small; lia).
assert (W28 : ew E 28 = Z_to_bv 64 nl) by (unfold E; rewrite (ew_Ereg_nat regs _ 28 28%bv eq_refl), H28; reflexivity).
assert (E28 : bv_unsigned (ew E 28) = nl) by (rewrite W28; apply unsigned_lit_small; lia).
assert (E26 : bv_unsigned (ew E 26) = 1) by (unfold E; rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl), H26; reflexivity).
assert (E27 : bv_unsigned (ew E 27) = SHADOW_OFF)
  by (unfold E; rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl), H27; reflexivity).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by reflexivity.
assert (E33 : ew E 33 = Z_to_bv 64 f7) by reflexivity.
assert (E34 : ew E 34 = Z_to_bv 64 b) by reflexivity.
assert (E35 : ew E 35 = Z_to_bv 64 sa) by reflexivity.
assert (E36 : ew E 36 = Z_to_bv 64 s) by reflexivity.
assert (Hsa64 : 0 <= sa < 2 ^ 46) by (rewrite Hsa; unfold SHADOW_OFF; lia).
(* the entry state *)
assert (HS : st_ok rsegs E hbp_ss_sel1 (restrict (w_H W) (mkst regs (Z_to_bv 64 HBP_N) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs); fold E.
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil.
    + apply (hm_ro_region rsegs E _ _ 9 R); [exact E9 | lia | lia |].
      constructor; [|constructor]. apply (hbp_chunk8 E _ R 0xf8 (SOff 33 0) f7); [| lia | exact Vf8].
      cbn [sv_denot]. rewrite E33, unsigned_lit_small, Z.add_0_r by lia. reflexivity.
    + apply (hm_cell_region rsegs E _ _ 18 cur b); [exact E18 | apply (hm_val1_aview rsegs); assumption | | lia | lia].
      cbn [sv_denot]. rewrite E34, unsigned_lit_small, Z.add_0_r by lia. reflexivity.
    + apply (hm_cell_region rsegs E _ _ 35 sa s); [rewrite E35; apply unsigned_lit_small; lia | exact Hs | | lia | lia].
      cbn [sv_denot]. rewrite E36, unsigned_lit_small, Z.add_0_r by lia. reflexivity.
  - unfold hbp_s_rf8, hbp_s_rin, hbp_s_rsh.
    cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite E9, E18, E35, unsigned_lit_small by lia.
    repeat split; lia.
  - split; [|split; [exact I|]].
    + cbn [hbp_s_G1 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E18, E26, E28, E32, E33, E34, E36, !unsigned_lit_small by (unfold SHADOW_OFF; lia).
      change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia.
    + cbn [hbp_s_G1 f_alias alias_ok]. split; [|exact I].
      apply U_inj. rewrite U_SAlu, U_srl3, !U_SOff, E18, E27, E35, unsigned_lit_small by lia.
      cbn [zalu_raw]. rewrite !Z.add_0_r.
      rewrite (zcanon_id cur), (zcanon_id SHADOW_OFF), (zcanon_id sa) by (unfold M64, SHADOW_OFF; lia).
      rewrite zcanon_id by (unfold M64, SHADOW_OFF; lia). rewrite Hsa. unfold SHADOW_OFF. lia. }
assert (HAE : env_agree 32 (Ereg regs (hbp_extra [f7; b; sa; s])) E) by apply env_agree_refl.
clearbody E.
assert (SHOK : sh_ok rsegs HBPBx [] E (mrestrict (w_H W) memc)) by constructor.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview rsegs (w_H W) memc a = aview rsegs (w_H W) memc a)
  by (intros; reflexivity).
unfold cfg_at. change (w64 HBP_N) with (Z_to_bv 64 HBP_N).
(* 0x81494 .. 0x814ac (the beqz t3 and the bltu of 0x8149c decided by the facts), stop at the beqz 0x814b0 on s *)
hbp_runb. hbp_keep hbp_kwr_ro.
hbp_branch Hc; rewrite branch_eq_U, U_SOff, E36, U_SLit, unsigned_lit_small in Hc by lia;
rewrite !zcanon_id in Hc by (unfold M64; lia); rewrite Z.add_0_r in Hc;
first [apply (proj1 (Z.eqb_eq _ _)) in Hc | apply (proj1 (Z.eqb_neq _ _)) in Hc].
- (* s = 0: 0x814b8 .. 0x814cc, stop at the beqz 0x814d0 *)
  hbp_runb. hbp_keep hbp_kwr_ro.
  hbp_s_fin sh E33 Hf7r (hbp_extra [f7; b; sa; s]); hbp_s_rel1 Hnz W18 W28 E34.
- (* s <> 0: 0x814b4 j 0x82afc, andi a1,s2,7; stop at the bge 0x82b00 *)
  hbp_runb. hbp_keep hbp_kwr_ro.
  hbp_branch Hg.
  + (* the report arm: cursor mod 8 >= s contradicts saddr_ok *)
    exfalso.
    assert (G1 : sv_denot E (SAlu ALU_AND (SOff 18 0) (SLit 7)) = Z_to_bv 64 (cur mod 8)).
    { cbn [sv_denot]. rewrite W18, unsigned_lit_small, Z.add_0_r by lia. apply alu_and7. unfold M64. lia. }
    assert (G2 : sv_denot E (SOff 36 0) = Z_to_bv 64 s).
    { cbn [sv_denot]. rewrite E36, unsigned_lit_small, Z.add_0_r by lia. reflexivity. }
    rewrite G1, G2 in Hg. cbn [branch_taken] in Hg. rewrite (hm_ra_slow_bv cur s Hsok Hc) in Hg.
    cbn in Hg. discriminate Hg.
  + (* 0x82b04 j 0x814b8 .. 0x814cc, stop at the beqz 0x814d0 *)
    clear Hg. hbp_runb. hbp_keep hbp_kwr_ro.
    hbp_s_fin sh E33 Hf7r (hbp_extra [f7; b; sa; s]); hbp_s_rel1 Hnz W18 W28 E34.
Qed.

(* nothing left: the byte is 0 and the cursor stays *)
Lemma hbp_sel0 : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
  (R sh cur b : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs 9 = w64 R -> getr regs 18 = w64 cur -> getr regs 28 = w64 0 ->
0 <= R -> R + 0x100 <= 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xf8) 8 (if sh =? 7 then 1 else 0) ->
0 <= cur < 2 ^ 64 ->
hbp_sel_goal STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs sh cur 0 b.
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R sh cur b HJ H9 H18 H28 HR0 HR1 Vf8 Hcur.
unfold hbp_sel_goal.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
remember (if sh =? 7 then 1 else 0) as f7 eqn:Hf7.
assert (Hf7r : (sh = 7 /\ f7 = 1) \/ (sh <> 7 /\ f7 = 0))
  by (subst f7; destruct (Z.eqb_spec sh 7); [left | right]; auto).
clear Hf7.
assert (Hf01 : 0 <= f7 <= 1) by (destruct Hf7r as [[_ ->]|[_ ->]]; lia).
set (E := Ereg regs (hbp_extra [f7])).
assert (E9 : bv_unsigned (ew E 9) = R)
  by (unfold E; rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl), H9; unfold w64; apply unsigned_lit_small; lia).
assert (W18 : ew E 18 = Z_to_bv 64 cur) by (unfold E; rewrite (ew_Ereg_nat regs _ 18 18%bv eq_refl), H18; reflexivity).
assert (W28 : ew E 28 = Z_to_bv 64 0) by (unfold E; rewrite (ew_Ereg_nat regs _ 28 28%bv eq_refl), H28; reflexivity).
assert (E28 : bv_unsigned (ew E 28) = 0) by (rewrite W28; reflexivity).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by reflexivity.
assert (E33 : ew E 33 = Z_to_bv 64 f7) by reflexivity.
(* the entry state *)
assert (HS : st_ok rsegs E hbp_ss_sel0 (restrict (w_H W) (mkst regs (Z_to_bv 64 HBP_N) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs); fold E.
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    apply (hm_ro_region rsegs E _ _ 9 R); [exact E9 | lia | lia |].
    constructor; [|constructor]. apply (hbp_chunk8 E _ R 0xf8 (SOff 33 0) f7); [| lia | exact Vf8].
    cbn [sv_denot]. rewrite E33, unsigned_lit_small, Z.add_0_r by lia. reflexivity.
  - exact (conj I I).
  - split; [|split; exact I].
    cbn [hbp_s_G0 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E28, E32, E33, !unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia. }
assert (HAE : env_agree 32 (Ereg regs (hbp_extra [f7])) E) by apply env_agree_refl.
clearbody E.
assert (SHOK : sh_ok rsegs HBPBx [] E (mrestrict (w_H W) memc)) by constructor.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview rsegs (w_H W) memc a = aview rsegs (w_H W) memc a)
  by (intros; reflexivity).
unfold cfg_at. change (w64 HBP_N) with (Z_to_bv 64 HBP_N).
(* 0x81494 beqz t3: the facts do not decide t3 = 0, split *)
hbp_branch Hc; rewrite branch_eq_U, U_SOff, E28, U_SLit in Hc;
rewrite !zcanon_id in Hc by (unfold M64; lia); rewrite Z.add_0_r, Z.eqb_refl in Hc.
- (* taken: 0x814c4 li a1,0; mv t2,s2; ld a0,0xf8(s1); stop at the beqz 0x814d0 *)
  hbp_runb. hbp_keep hbp_kwr_ro.
  hbp_s_fin sh E33 Hf7r (hbp_extra [f7]); hbp_s_rel0 W18 W28.
- (* not taken: t3 <> 0, false *)
  discriminate Hc.
Qed.

(* ---- the selector N 0x81494 -> SEL7 0x814d4 (sh = 7) / SELK 0x81590 ---- *)
Lemma hbp_sel : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
  (R sh cur nl b : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs 9 = w64 R -> getr regs 18 = w64 cur -> getr regs 28 = w64 nl ->
getr regs 26 = w64 1 -> getr regs 27 = w64 SHADOW_OFF ->
2 ^ 46 <= R -> R + 0x100 <= 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xf8) 8 (if sh =? 7 then 1 else 0) ->
0 < cur -> 0 <= nl -> cur + nl <= 2 ^ 63 ->
(0 < nl -> val_mem rsegs (mrestrict (w_H W) memc) cur 1 b /\ 0 <= b < 256 /\
  range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF cur 1 /\
  amem_range cur 1 /\ ~ (R + 0xf8 <= cur < R + 0x100)) ->
SRr rsegs W (cfg_at rsegs HBP_N regs memc mdc)
(hdu_blk_postE B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc
 (if sh =? 7 then HBP_SEL7 else HBP_SELK) [7; 10; 11; 28]%bv (fun _ => False) (hbp_sel_R cur nl b)).
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R sh cur nl b
  HJ H9 H18 H28 H26 H27 HR0 HR1 Vf8 Hcur0 Hnl Hcurn Hin.
destruct (Z.eq_dec nl 0) as [-> | Hnz].
- exact (hbp_sel0 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R sh cur b
    HJ H9 H18 H28 ltac:(lia) HR1 Vf8 ltac:(lia)).
- destruct (Hin ltac:(lia)) as (Vb & Hb & HRAc & Hamr & HnR).
  exact (hbp_sel1 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R sh cur nl b
    HJ H9 H18 H28 H26 H27 HR0 HR1 Vf8 Hcur0 ltac:(lia) Hcurn Vb Hb HRAc Hamr HnR).
Qed.

(* ================================ the piece: N -> SEL7 / SELK ================================ *)
Lemma hbp_piece_sel : hsu_piece_W4_sel_stmt rsegs B MT headamp_himg_B headamp_bld_B.
Proof using MTL LAWS.
unfold hsu_piece_W4_sel_stmt. intros cx POST rest i Hst HS7 HSK.
destruct Hst as (Hpre & Hc1 & Hlen0 & Hin0).
pose proof (hbp_R_bounds B cx _ Hpre) as (RB1 & RB2 & RB3 & RB4 & RB5 & RB6 & RB7).
unfold hsu_from_N. intros ly2 S2 W2 regs2 mem2 md2 sh np ps r Hlen Hcut.
destruct Hcut as (Hcore & Hat & Hfsh & Hpp & Hin & Hsuf & Hwf & Hsh & Hnp & Hps & Hnp3 & Hloop).
pose proof Hin as (Hleft & _ & _ & _ & Hamr & Hsrc0 & Hsrcn & Hapart).
pose proof Hsuf as (j & Hj & Er).
assert (Lr : length r = (length rest - j)%nat) by (rewrite Er; apply length_skipn).
assert (Hcur : hsu_cur rsegs cx rest r = e_src (x_e cx) + Z.of_nat j) by (unfold hsu_cur; rewrite Lr; lia).
unfold hsu_at_cx in Hat.
hbp_take Hat (LReg 9) (e_R (x_e cx)) A9.
hbp_take Hat (LReg 18) (hsu_cur rsegs cx rest r) A18.
hbp_take Hat (LReg 28) (Z.of_nat (length r)) A28.
hbp_take Hat (LReg 26) 1 A26.
hbp_take Hat (LReg 27) SHADOW_OFF A27.
hbp_take Hat (LCell XR 0xf8) (if sh =? 7 then 1 else 0) Af8.
rewrite Z.mod_small in Af8 by (destruct (sh =? 7); lia).
pose proof Hcore as (HJ & _).
(* the byte at the cursor, its shadow and where it lies, when a byte is left *)
assert (Hinp : 0 < Z.of_nat (length r) ->
  val_mem rsegs (mrestrict (w_H W2) mem2) (hsu_cur rsegs cx rest r) 1 (fst (fuzz_u8 r)) /\
  0 <= fst (fuzz_u8 r) < 256 /\
  range_addressable (aview rsegs (w_H W2) mem2) SHADOW_OFF (hsu_cur rsegs cx rest r) 1 /\
  amem_range (hsu_cur rsegs cx rest r) 1 /\
  ~ (e_R (x_e cx) + 0xf8 <= hsu_cur rsegs cx rest r < e_R (x_e cx) + 0x100)).
{ intros Hnz. rewrite Hcur. destruct r as [|bb r''] eqn:Er'; [cbn in Hnz; lia|]. cbn [fuzz_u8 fst].
  destruct (hbp_nth_skipn rest j bb r'' (eq_sym Er)) as (Hjl & Hnth).
  destruct (hbp_input_now B MT LAWS cx rest ly2 S2 W2 regs2 mem2 md2 (Z.of_nat j) Hpre Hin Hcore Hfsh ltac:(lia))
    as (V & RA).
  assert (Hb : nth (Z.to_nat (Z.of_nat j)) (hd_zbytes rest) 0 = bv_unsigned bb).
  { rewrite Nat2Z.id. unfold hd_zbytes. rewrite hm_nth_map, Hnth. reflexivity. }
  rewrite Hb in V. destruct (Hapart (e_src (x_e cx) + Z.of_nat j) ltac:(lia)) as (N1 & N2 & N3).
  split; [exact V|]. split; [apply hm_byte_range|].
  split; [exact RA|]. split; [unfold amem_range in Hamr |- *; lia|].
  intros X. apply N2. unfold hd_inw. cbn [hi_w1 headamp_himg_B].
  apply Exists_cons_tl. apply Exists_cons_tl. apply Exists_cons_hd. cbn [fst snd hd_xv]. lia. }
eapply SRr_bind.
{ refine (hbp_sel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs2 (e_R (x_e cx)) sh (hsu_cur rsegs cx rest r)
    (Z.of_nat (length r)) (fst (fuzz_u8 r)) HJ A9 A18 A28 A26 A27 _ _ Af8 _ _ _ Hinp); rewrite ?Hcur; lia. }
intros W3 c3 Hle (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & Hkeep & Hfr & Hperm & Hio & Hmo & Hmem & HR).
destruct HR as (R7 & R28 & R11).
pose proof (hbp_mem_all _ _ _ _ Hmem) as Hall.
(* the cursor after the selector byte, what is left after it, and the byte *)
assert (Hstep : getr regs3 7 = w64 (hsu_cur rsegs cx rest (snd (fuzz_u8 r))) /\
  getr regs3 28 = w64 (Z.of_nat (length (snd (fuzz_u8 r)))) /\ getr regs3 11 = w64 (fst (fuzz_u8 r))).
{ destruct r as [|bb r''] eqn:Er'.
  - cbn [fuzz_u8 fst snd length Z.of_nat Z.eqb] in R7, R28, R11 |- *.
    split; [exact R7|]. split; [exact R28 | exact R11].
  - cbn [fuzz_u8 fst snd length] in R7, R28, R11 |- *.
    replace (Z.of_nat (S (length r'')) =? 0) with false in R7, R28, R11 by (symmetry; apply Z.eqb_neq; lia).
    cbv iota in R7, R28, R11.
    split; [rewrite R7; f_equal; unfold hsu_cur; cbn [length]; lia|].
    split; [rewrite R28; f_equal; lia | exact R11]. }
destruct Hstep as (R7' & R28' & R11').
assert (Hcore3 : hsu_core rsegs B MT cx (hsu_E1 rsegs headamp_himg_B cx) ly3 S3 W3 regs3 mem3 md3).
{ refine (hbp_core_step B MT MTL cx _ (fun _ => False) _ _ _ _ _ _ _ _ _ _ _ _ Hcore HJ3 _ Hfr Hperm Hio Hmo Hmem _);
  [hbp_regs234 Hkeep | intros a []]. }
assert (Hfsh3 : hsu_fsh_at rsegs cx W3 mem3 (hsu_P0 headamp_himg_B)).
{ unfold hsu_fsh_at in *. eapply (hm_fsh_kept rsegs); [exact Hfsh|]. intros jj Hjj. apply Hall. }
assert (Hpp3 : hsu_pp_at rsegs cx W3 mem3 (pc_image (PbCut sh ps None))).
{ unfold hsu_pp_at in *.
  eapply (hm_bytes_kept rsegs _ _ _ _ _ (pc_image (PbCut sh ps None))); [exact Hpp|].
  intros x Hx. apply Hall. }
(* the facts of N the block keeps *)
assert (Hat3 : hsu_at rsegs (w_H W3) mem3 regs3 (x_e cx)
  (hsu_Rc1 rsegs cx ++ hsu_Kc rsegs cx sh np ++ [(LReg 5, Z.of_nat (length ps)); (LReg 20, hsu_seen ps)])).
{ assert (Hat' : hsu_at rsegs (w_H W2) mem2 regs2 (x_e cx)
    (hsu_Rc1 rsegs cx ++ hsu_Kc rsegs cx sh np ++ [(LReg 5, Z.of_nat (length ps)); (LReg 20, hsu_seen ps)]))
    by (hbp_list; hbp_from Hat).
  eapply hbp_at_move; [exact Hat'|]. hbp_kept Hkeep ltac:(apply Hall). }
assert (HatS : hsu_at rsegs (w_H W3) mem3 regs3 (x_e cx) (hsu_L_SEL rsegs cx sh np ps rest (snd (fuzz_u8 r)))).
{ hbp_list; first [hbp_from Hat3 | idtac].
  - cbn [hd_at]. exact R7'.
  - cbn [hd_at]. exact R28'. }
destruct (Z.eqb_spec sh 7) as [E7|E7].
- replace (if sh =? 7 then HBP_SEL7 else HBP_SELK) with HBP_SEL7
    by (rewrite (proj2 (Z.eqb_eq sh 7) E7); reflexivity).
  change (SRr rsegs W3 (cfg_at rsegs (bi_SEL7 headamp_bld_B) regs3 mem3 md3) POST).
  apply (HS7 ly3 S3 W3 regs3 mem3 md3 np ps (snd (fuzz_u8 r)) Hlen).
  rewrite E7 in Hwf, Hloop, Hsh, HatS, Hpp3.
  split.
  { split; [exact Hcore3|]. split; [exact Hfsh3|]. split; [exact Hin|].
    split; [apply hbp_suffix_step; exact Hsuf|]. split; [exact Hwf|]. split; [exact Hlen0|].
    split; [rewrite <- Hloop; reflexivity|]. split; [exact Hsh|]. split; [exact Hnp|]. split; [exact Hps | exact Hnp3]. }
  split; [exact HatS|]. split; [exact Hpp3|].
  rewrite <- Hloop. reflexivity.
- replace (if sh =? 7 then HBP_SEL7 else HBP_SELK) with HBP_SELK
    by (rewrite (proj2 (Z.eqb_neq sh 7) E7); reflexivity).
  change (SRr rsegs W3 (cfg_at rsegs (bi_SELK headamp_bld_B) regs3 mem3 md3) POST).
  apply (HSK ly3 S3 W3 regs3 mem3 md3 sh np (fst (fuzz_u8 r)) ps (snd (fuzz_u8 r)) Hlen).
  split.
  { split; [exact Hcore3|]. split; [exact Hfsh3|]. split; [exact Hin|].
    split; [apply hbp_suffix_step; exact Hsuf|]. split; [exact Hwf|]. split; [exact Hlen0|].
    split; [rewrite <- Hloop; reflexivity|]. split; [exact Hsh|]. split; [exact Hnp|]. split; [exact Hps | exact Hnp3]. }
  split.
  { unfold hsu_at_cx. apply hbp_at_app; [exact HatS|].
    unfold hsu_at. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
    - cbn [hd_at]. exact R11'.
    - hbp_from Hat3.
    - hbp_from Hat3. }
  split; [exact Hpp3|]. split; [exact E7|].
  split; [destruct r as [|bb r'']; cbn [fuzz_u8 fst]; [lia | apply hm_byte_range]|].
  rewrite <- Hloop. cbn [snd]. destruct (fuzz_u8 r); reflexivity.
Qed.

End d.
End b.

Print Assumptions hbp_sel.
Print Assumptions hbp_piece_sel.
