(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgPropIntB.v at a529a88a618 (pa_i_memset_at, as
   hbp_i_memset_at; pa_i_bv5_cases, pa_i_cs, pa_i_pres and pa_i_mod16_sub, as hbp_i_*; pa_int7's route, one engine state
   up to each call and a fresh one after it) and proofs/reac-pw/fuzz_role/lib/A/RPgProp.v at a529a88a618
   (pa_piece_int7, as hbp_piece_int7) for reac-pw/fuzz_headamp's image B: the block walked new against image B's own
   instructions (the scope stores of e, __asan_memset of e's body, the two header words, the out-of-line pod_write_ent
   under PweSpec.pod_write_ent_specX, the restores of the loop's three values), the cut states of lib/AU/HPgSeg.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/AU/HPgPropInt.v, with its module paths and module names changed; 242 of its 312 lines of code are new or changed and 891 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgPropSel.v at a529a88a6181 (the latch blocks
   pa_latch / pa_latch7) and the latch piece pa_piece_latch of proofs/reac-pw/fuzz_role/lib/A/RPgProp.v at the same
   commit, for reac-pw/fuzz_rate image A: rate's pcs and real-frame cells (i at R+0xf8, seen' at R+0xc8, np at
   R+0xd0); the latch's third entry 0x8252c (pa_latchi, from the Int-7 piece with i in a6) is new; the block post is
   lib/A/RtPgSteps.v rts_post; the cut lists are lib/A/RtPgSeg.v's. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgPropSel.v at a67a3bd733f9 for image B
   (fuzz_rate.asan-ubsan): image B's latch has two entries (no LATCHI): 0x82578 (seen from R+0x98) and 0x8257c (seen in
   a3), the index in t0, the cursor moved from s10 to s2 and seen into s6 by the latch itself, np from R+0x118; the
   block post is lib/AU/RtPgStepsB.v rtsb_post; the cut lists are lib/AU/RtPgSegB.v's. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/AU/RtPgPropBLatch.v at 6aea585e8b5b for
   reac-pw/fuzz_role image B (fuzz_role.asan-ubsan): module paths fuzz_rate -> fuzz_role, the segments lib/AU/Img0.v
   rsegs; role B's latch 0x81d84 (seen from R+0x80) / 0x81d88 (seen in a2), the index in t1, the cursor moved from a7
   to s4 and seen into s2 by the latch itself, np from R+0x108, the exits N 0x80770 / P1 0x81e70; the block post is
   lib/AU/RPgSteps.v rl_wpost, the kit lib/AU/RPgPropKit.v and lib/AU/RPgPropLib.v, the cut lists lib/AU/RPgSeg.v's;
   pab_ becomes pa_. *)
(* reac-pw/fuzz_role image B (fuzz_role.asan-ubsan, pinned sha256
   b255d4935da5af137a3967dbe33380ea43be8e78bfe05d1e356e0a2be8a69ff0; every address below is measured on its unstripped
   twin sha256 dc791783f32962615e18a5f5cffae758ba56eb5dc87f70913c3579b101b4406a, same loaded bytes): the property
   loop's latch of LLVMFuzzerTestOneInput, from its two entries, as block lemmas over lib/AU/RPgPropKit.v, and the
   piece rs_piece_W4_latch_stmt (LATCH / LATCH7 -> N / P1) of lib/AU/RPgSeg.v. Proves no function (kind: segment
   lemma).
     0x81d84 ld a2,0x80(s1)   seen         (LATCH, from the Struct's close)
     0x81d88 addiw t1,t1,1    i + 1        (LATCH7, from the shape-7 and the Int-7 pieces: seen already in a2)
     0x81d8c mv s4,a7         the cursor
     0x81d90 mv s2,a2         seen
     0x81d94 ld a0,0x108(s1)  np
     0x81d98 beq t1,a0,0x81e70 (P1)
     0x81d9c j 0x80770 (N)
   The block writes no memory and holds no trap branch and no instrumented check. *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgBase RPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import Img0 RPgImgA RPgSteps RPgMem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import RPgSeg RPgPropKit RPgPropLib.
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

(* the value of an atom plus a constant *)
Lemma pa_l_soff : forall {fx : YK11.FPState} E n v c, ew E n = Z_to_bv 64 v -> sv_denot E (SOff n c) = Z_to_bv 64 (v + c).
Proof.
intros fx E n v c H. apply bv_eq. rewrite denot_SOff, H, !Z_to_bv_unsigned. unfold zcanon, M64, bv_wrap.
change (bv_modulus 64) with (2 ^ 64). rewrite Z.add_mod_idemp_l by lia. reflexivity.
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.
Local Abbreviation pa_post := (rl_wpost B MT).

(* what the latch computes, from either entry: t1 = i + 1, s4 = the cursor, s2 = seen, a0 = np *)
Definition pa_latch_R (i seen np cur : Z) (W2 : world rsegs) (regs2 : bvmap 5 word) (mem2 : word -> option byte)
: Prop :=
getr regs2 6 = w64 (i + 1) /\ getr regs2 20 = w64 cur /\ getr regs2 18 = w64 seen /\ getr regs2 10 = w64 np.

(* ---- the latch 0x81d84 -> N 0x80770 / P1 0x81e70: seen and np from their cells ---- *)
Definition pa_latch_facts : facts :=
mkFacts [ (6%nat, mkAF 0 2 0); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (33%nat, mkAF 0 1 0); (34%nat, mkAF 1 3 0) ]
[] [].
Definition pa_ss_latch : sstate :=
mkSS PA_LATCH sr_atoms
[ YP09.mkRegion (Some 9%nat) 0x80 0x110 0 0
  [ YP09.mkChunk 0x80 (CVal 8 (SOff 33 0)); YP09.mkChunk 0x108 (CVal 8 (SOff 34 0)) ] ]
None pa_latch_facts.
Lemma pa_latch : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
  (R i seen np cur : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs 9 = w64 R -> getr regs 6 = w64 i -> getr regs 17 = w64 cur -> 0 <= R -> R + 0x110 <= 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x80) 8 seen ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x108) 8 np ->
0 <= i -> i < np -> np <= 3 -> 0 <= seen <= 1 ->
SRr rsegs W (cfg_at rsegs PA_LATCH regs memc mdc)
(pa_post STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc (if i + 1 =? np then PA_P1 else PA_N)
[6; 10; 12; 18; 20]%bv (fun _ => False) (pa_latch_R i seen np cur)).
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R i seen np cur HJ H9 H6 H17 HR0 HR1 Vs Vn
  Hi0 Hin Hn3 Hs.
pose proof rl_wx as Hwx. pose proof rl_segs_low as Hsegs.
assert (E9 : bv_unsigned (ew (Ereg regs (pa_extra [seen; np])) 9) = R) by (rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl), H9; unfold w64; apply unsigned_lit_small; lia).
assert (E6 : ew (Ereg regs (pa_extra [seen; np])) 6 = Z_to_bv 64 i) by (rewrite (ew_Ereg_nat regs _ 6 6%bv eq_refl), H6; reflexivity).
assert (E17 : ew (Ereg regs (pa_extra [seen; np])) 17 = Z_to_bv 64 cur) by (rewrite (ew_Ereg_nat regs _ 17 17%bv eq_refl), H17; reflexivity).
assert (E33 : ew (Ereg regs (pa_extra [seen; np])) 33 = Z_to_bv 64 seen) by reflexivity.
assert (E34 : ew (Ereg regs (pa_extra [seen; np])) 34 = Z_to_bv 64 np) by reflexivity.
assert (HS : st_ok rsegs (Ereg regs (pa_extra [seen; np])) pa_ss_latch (restrict (w_H W) (mkst regs (Z_to_bv 64 PA_LATCH) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E9.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat constructor; (eapply pa_chunk8; [ cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; eassumption
      | lia | eassumption ]).
  - apply pairwise_disjoint_of_extents. cbn. tauto.
  - split; [|split; [exact I | exact I]]. cbn [pa_latch_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E6, E33, E34, pa_extra_K. rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
    repeat split; try lia; apply Z.mod_1_r. }
remember (Ereg regs (pa_extra [seen; np])) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs (pa_extra [seen; np])) E) by (subst E; apply env_agree_refl).
clear HE.
assert (SHOK : sh_ok rsegs PABx [] E (mrestrict (w_H W) memc)) by constructor.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview rsegs (w_H W) memc a = aview rsegs (w_H W) memc a)
by (intros; reflexivity).
unfold cfg_at. change (w64 PA_LATCH) with (Z_to_bv 64 PA_LATCH).
(* 0x81d84 .. 0x81d94, stop at the beq 0x81d98 *)
pa_runb. pa_keep pa_kwr_ro.
pa_branch Hc; rewrite branch_eq_U, !U_SOff, E6, E34, !unsigned_lit_small in Hc by lia;
rewrite !zcanon_id in Hc by (unfold M64; lia);
first [apply (proj1 (Z.eqb_eq _ _)) in Hc | apply (proj1 (Z.eqb_neq _ _)) in Hc].
- replace (if i + 1 =? np then PA_P1 else PA_N) with PA_P1 by (destruct (Z.eqb_spec (i + 1) np); [reflexivity | lia]).
  pa_run PA_P1. pa_keep pa_kwr_ro.
  pa_leaf (pa_extra [seen; np]).
  unfold pa_latch_R. pa_reg (6%bv : bv 5). pa_reg (20%bv : bv 5). pa_reg (18%bv : bv 5). pa_reg (10%bv : bv 5).
  unfold w64. rewrite (pa_l_soff E 6 i 1 E6), (pa_l_soff E 17 cur 0 E17), (pa_l_soff E 33 seen 0 E33),
    (pa_l_soff E 34 np 0 E34), !Z.add_0_r. auto.
- replace (if i + 1 =? np then PA_P1 else PA_N) with PA_N by (destruct (Z.eqb_spec (i + 1) np); [lia | reflexivity]).
  pa_run PA_N. pa_keep pa_kwr_ro.
  pa_leaf (pa_extra [seen; np]).
  unfold pa_latch_R. pa_reg (6%bv : bv 5). pa_reg (20%bv : bv 5). pa_reg (18%bv : bv 5). pa_reg (10%bv : bv 5).
  unfold w64. rewrite (pa_l_soff E 6 i 1 E6), (pa_l_soff E 17 cur 0 E17), (pa_l_soff E 33 seen 0 E33),
    (pa_l_soff E 34 np 0 E34), !Z.add_0_r. auto.
Qed.

(* ---- the latch's second entry 0x81d88 (from the shape-7 and the Int-7 pieces: seen already in a2) ---- *)
Definition pa_latch7_facts : facts :=
mkFacts [ (6%nat, mkAF 0 2 0); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (33%nat, mkAF 1 3 0) ] [] [].
Definition pa_ss_latch7 : sstate :=
mkSS PA_LATCH7 sr_atoms
[ YP09.mkRegion (Some 9%nat) 0x108 0x110 0 0 [ YP09.mkChunk 0x108 (CVal 8 (SOff 33 0)) ] ]
None pa_latch7_facts.
Lemma pa_latch7 : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
  (R i seen np cur : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs 9 = w64 R -> getr regs 6 = w64 i -> getr regs 17 = w64 cur -> getr regs 12 = w64 seen ->
0 <= R -> R + 0x110 <= 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x108) 8 np ->
0 <= i -> i < np -> np <= 3 ->
SRr rsegs W (cfg_at rsegs PA_LATCH7 regs memc mdc)
(pa_post STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc (if i + 1 =? np then PA_P1 else PA_N)
[6; 10; 18; 20]%bv (fun _ => False) (pa_latch_R i seen np cur)).
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R i seen np cur HJ H9 H6 H17 H12 HR0 HR1 Vn
  Hi0 Hin Hn3.
pose proof rl_wx as Hwx. pose proof rl_segs_low as Hsegs.
assert (E9 : bv_unsigned (ew (Ereg regs (pa_extra [np])) 9) = R) by (rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl), H9; unfold w64; apply unsigned_lit_small; lia).
assert (E6 : ew (Ereg regs (pa_extra [np])) 6 = Z_to_bv 64 i) by (rewrite (ew_Ereg_nat regs _ 6 6%bv eq_refl), H6; reflexivity).
assert (E17 : ew (Ereg regs (pa_extra [np])) 17 = Z_to_bv 64 cur) by (rewrite (ew_Ereg_nat regs _ 17 17%bv eq_refl), H17; reflexivity).
assert (E12 : ew (Ereg regs (pa_extra [np])) 12 = Z_to_bv 64 seen) by (rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl), H12; reflexivity).
assert (E33 : ew (Ereg regs (pa_extra [np])) 33 = Z_to_bv 64 np) by reflexivity.
assert (HS : st_ok rsegs (Ereg regs (pa_extra [np])) pa_ss_latch7 (restrict (w_H W) (mkst regs (Z_to_bv 64 PA_LATCH7) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E9.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat constructor; (eapply pa_chunk8; [ cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; eassumption
      | lia | eassumption ]).
  - apply pairwise_disjoint_of_extents. cbn. tauto.
  - split; [|split; [exact I | exact I]]. cbn [pa_latch7_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E6, E33, pa_extra_K. rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
    repeat split; try lia; apply Z.mod_1_r. }
remember (Ereg regs (pa_extra [np])) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs (pa_extra [np])) E) by (subst E; apply env_agree_refl).
clear HE.
assert (SHOK : sh_ok rsegs PABx [] E (mrestrict (w_H W) memc)) by constructor.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview rsegs (w_H W) memc a = aview rsegs (w_H W) memc a)
by (intros; reflexivity).
unfold cfg_at. change (w64 PA_LATCH7) with (Z_to_bv 64 PA_LATCH7).
(* 0x81d88 .. 0x81d94, stop at the beq 0x81d98 *)
pa_runb. pa_keep pa_kwr_ro.
pa_branch Hc; rewrite branch_eq_U, !U_SOff, E6, E33, !unsigned_lit_small in Hc by lia;
rewrite !zcanon_id in Hc by (unfold M64; lia);
first [apply (proj1 (Z.eqb_eq _ _)) in Hc | apply (proj1 (Z.eqb_neq _ _)) in Hc].
- replace (if i + 1 =? np then PA_P1 else PA_N) with PA_P1 by (destruct (Z.eqb_spec (i + 1) np); [reflexivity | lia]).
  pa_run PA_P1. pa_keep pa_kwr_ro.
  pa_leaf (pa_extra [np]).
  unfold pa_latch_R. pa_reg (6%bv : bv 5). pa_reg (20%bv : bv 5). pa_reg (18%bv : bv 5). pa_reg (10%bv : bv 5).
  unfold w64. rewrite (pa_l_soff E 6 i 1 E6), (pa_l_soff E 17 cur 0 E17), (pa_l_soff E 12 seen 0 E12),
    (pa_l_soff E 33 np 0 E33), !Z.add_0_r. auto.
- replace (if i + 1 =? np then PA_P1 else PA_N) with PA_N by (destruct (Z.eqb_spec (i + 1) np); [lia | reflexivity]).
  pa_run PA_N. pa_keep pa_kwr_ro.
  pa_leaf (pa_extra [np]).
  unfold pa_latch_R. pa_reg (6%bv : bv 5). pa_reg (20%bv : bv 5). pa_reg (18%bv : bv 5). pa_reg (10%bv : bv 5).
  unfold w64. rewrite (pa_l_soff E 6 i 1 E6), (pa_l_soff E 17 cur 0 E17), (pa_l_soff E 12 seen 0 E12),
    (pa_l_soff E 33 np 0 E33), !Z.add_0_r. auto.
Qed.

End d.
End b.

(* ================================ the latch piece: LATCH / LATCH7 -> N / P1 ================================ *)
Section p. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.

(* the locations of rs_L_LATCH the latch block keeps (all but t1, which it increments) *)
Definition pa_L_kept (cx : rs_scx rsegs) (sh np : Z) (rest r : list byte) : list (rl_loc * Z) :=
rs_Rc rsegs cx ++ rs_Kc rsegs cx sh np ++
[(LReg 28, Z.of_nat (length r)); (LReg 17, rs_cur rsegs cx rest r); (LReg 22, e_pp (x_e cx) + 0x4000)].
(* the end of the latch from either entry: the block's post at regs3 / mem3 with every location of pa_L_kept kept,
   t1 = |ps|, s4 = the cursor and s2 = seen, into the head N (another property is due) or the builder's end P1 *)
Lemma pa_latch_end : forall cx POST rest i ly2 S2 W2 regs2 mem2 md2 sh np ps r W3 ly3 S3 regs3 mem3 md3,
e_len (x_e cx) = rl_len rest ->
rs_from_N rsegs B MT cx POST rest (S i) -> rs_from_P1 rsegs B MT cx POST rest ->
(length ps = S i)%nat ->
rs_latch_body rsegs B MT cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 ->
rs_core rsegs B MT cx (rs_E1 rsegs cx) ly3 S3 W3 regs3 mem3 md3 ->
rs_at rsegs (w_H W3) mem3 regs3 (x_e cx) (pa_L_kept cx sh np rest r) ->
rs_fsh_at rsegs cx W3 mem3 rs_P0 -> rs_pp_at rsegs cx W3 mem3 (pc_image (PbCut sh ps None)) ->
getr regs3 6 = w64 (Z.of_nat (length ps) - 1 + 1) -> getr regs3 20 = w64 (rs_cur rsegs cx rest r) ->
getr regs3 18 = w64 (rs_seen ps) ->
SRr rsegs W3 (mkCfg (mkst regs3 (w64 (if Z.of_nat (length ps) - 1 + 1 =? np then PA_P1 else PA_N)) mem3
  (seg_rom rsegs)) md3) POST.
Proof.
intros cx POST rest i ly2 S2 W2 regs2 mem2 md2 sh np ps r W3 ly3 S3 regs3 mem3 md3 Hlen0 HN HP1 Hlen Hb Hcore3 Hat3
  Hfsh3 Hpp3 R6 R20 R18.
unfold pa_L_kept in Hat3.
destruct Hb as (_ & _ & _ & Hin & Hsuf & Hwf & Hsh & Hnp & Hps & Hnp3 & Hloop).
destruct (Z.eqb_spec (Z.of_nat (length ps) - 1 + 1) np) as [Heq|Hne].
- change (mkCfg (mkst regs3 (w64 PA_P1) mem3 (seg_rom rsegs)) md3) with (cfg_at rsegs RS_P1 regs3 mem3 md3).
  apply (HP1 ly3 S3 W3 regs3 mem3 md3 sh np ps r).
  split.
  + split; [exact Hcore3|]. split; [exact Hfsh3|]. split; [exact Hpp3|]. split; [exact Hin|]. split; [exact Hsuf|].
    split; [exact Hwf|]. split; [exact Hlen0|]. split; [exact Hsh|]. split; [exact Hnp|]. split; [lia | exact Hloop].
  + pa_list; pa_from Hat3.
- change (mkCfg (mkst regs3 (w64 PA_N) mem3 (seg_rom rsegs)) md3) with (cfg_at rsegs RS_N regs3 mem3 md3).
  apply (HN ly3 S3 W3 regs3 mem3 md3 sh np ps r Hlen).
  split; [exact Hcore3|]. split.
  + pa_list; first [pa_from Hat3 | idtac].
    * cbn [rl_at]. refine (eq_trans R6 _). f_equal. lia.
    * cbn [rl_at]. exact R18.
    * cbn [rl_at]. exact R20.
  + split; [exact Hfsh3|]. split; [exact Hpp3|]. split; [exact Hin|]. split; [exact Hsuf|]. split; [exact Hwf|].
    split; [exact Hsh|]. split; [exact Hnp|]. split; [lia|]. split; [exact Hnp3 | exact Hloop].
Qed.

Lemma pa_piece_latch : rs_piece_W4_latch_stmt rsegs B MT.
Proof using MTL LAWS.
unfold rs_piece_W4_latch_stmt. intros cx POST rest i Hst HN HP1.
destruct Hst as (Hpre & Hfsh0 & Hc1 & Hlen0 & Hin0).
pose proof (pa_R_bounds B cx Hpre) as (RB1 & RB2 & RB3 & RB4 & RB5 & RB6 & RB7).
pose proof asan_consts as (C1 & _).
assert (Hseen : forall ps, 0 <= rs_seen ps <= 1) by (intros ps; unfold rs_seen; destruct (existsb _ _); cbn; lia).
(* what either entry leaves of the cut: the journal-and-frame part, the frame's shadow and the first block, for a
   block that writes nothing *)
assert (Hstep : forall ly2 S2 W2 regs2 mem2 md2 sh np ps r W3 ly3 S3 regs3 mem3 md3,
  rs_latch_body rsegs B MT cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 ->
  ajournal rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx)
    ly3 S3 W3 mem3 md3 (x_k cx) ->
  (forall r0 : Z, r0 = 2 \/ r0 = 3 \/ r0 = 4 -> getr regs3 (Z_to_bv 5 r0) = getr regs2 (Z_to_bv 5 r0)) ->
  frames S3 = frames S2 -> Permutation (ablocks B ly3 S3) (ablocks B ly2 S2) -> same_io md2 md3 -> mo_le MT S2 S3 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a) ->
  rs_core rsegs B MT cx (rs_E1 rsegs cx) ly3 S3 W3 regs3 mem3 md3 /\
  rs_fsh_at rsegs cx W3 mem3 rs_P0 /\ rs_pp_at rsegs cx W3 mem3 (pc_image (PbCut sh ps None))).
{ intros ly2 S2 W2 regs2 mem2 md2 sh np ps r W3 ly3 S3 regs3 mem3 md3 Hb HJ3 Hr3 Hfr Hperm Hio Hmo Hmem.
  pose proof Hb as (Hcore & Hfsh & Hpp & _).
  pose proof (pa_mem_all _ _ _ _ Hmem) as Hall.
  split; [|split].
  - refine (pa_core_step B MT MTL cx _ (fun _ => False) _ _ _ _ _ _ _ _ _ _ _ _ Hcore HJ3 Hr3 Hfr Hperm Hio Hmo Hmem _).
    intros a [].
  - unfold rs_fsh_at in *. eapply rm_fsh_kept; [exact Hfsh|]. intros j Hj. apply Hall.
  - unfold rs_pp_at in *. eapply (rm_bytes_kept rsegs); [exact Hpp|]. intros x Hx. apply Hall. }
split.
- (* LATCH 0x81d84: seen and np from their cells *)
  unfold rs_from_LATCH. intros ly2 S2 W2 regs2 mem2 md2 sh np ps r Hlen Hcut.
  destruct Hcut as [Hb Hat]. pose proof Hb as (Hcore & _ & _ & Hin & _ & _ & _ & _ & Hps & Hnp3 & _).
  unfold rs_at_cx in Hat.
  pa_take Hat (LReg 9) (e_R (x_e cx)) A9.
  pa_take Hat (LReg 6) (Z.of_nat (length ps) - 1) A6.
  pa_take Hat (LReg 17) (rs_cur rsegs cx rest r) A17.
  pa_take Hat (LCell XR 0x80) (rs_seen ps) As.
  pa_take Hat (LCell XR 0x108) np An.
  pose proof (Hseen ps) as Hs.
  rewrite Z.mod_small in As, An by lia.
  pose proof Hcore as (HJ & _).
  eapply SRr_bind.
  { refine (pa_latch B MT MTL LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs2 (e_R (x_e cx)) (Z.of_nat (length ps) - 1)
      (rs_seen ps) np (rs_cur rsegs cx rest r) HJ A9 A6 A17 _ _ As An _ _ _ Hs); lia. }
  intros W3 c3 Hle (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & Hkeep & Hfr & Hperm & Hio & Hmo & Hmem & HR).
  destruct HR as (R6 & R20 & R18 & R10).
  pose proof (pa_mem_all _ _ _ _ Hmem) as Hall.
  destruct (Hstep ly2 S2 W2 regs2 mem2 md2 sh np ps r W3 ly3 S3 regs3 mem3 md3 Hb HJ3
    ltac:(pa_regs234 Hkeep) Hfr Hperm Hio Hmo Hmem) as (Hcore3 & Hfsh3 & Hpp3).
  assert (Hat' : rs_at rsegs (w_H W2) mem2 regs2 (x_e cx) (pa_L_kept cx sh np rest r)).
  { unfold pa_L_kept. pa_list; pa_from Hat. }
  assert (Hat3 : rs_at rsegs (w_H W3) mem3 regs3 (x_e cx) (pa_L_kept cx sh np rest r)).
  { eapply pa_at_move; [exact Hat'|]. unfold pa_L_kept. pa_kept Hkeep ltac:(apply Hall). }
  exact (pa_latch_end cx POST rest i ly2 S2 W2 regs2 mem2 md2 sh np ps r W3 ly3 S3 regs3 mem3 md3
    Hlen0 HN HP1 Hlen Hb Hcore3 Hat3 Hfsh3 Hpp3 R6 R20 R18).
- (* LATCH7 0x81d88: seen in a2; np from its cell *)
  unfold rs_from_LATCH7. intros ly2 S2 W2 regs2 mem2 md2 sh np ps r Hlen Hcut.
  destruct Hcut as [Hb Hat]. pose proof Hb as (Hcore & _ & _ & Hin & _ & _ & _ & _ & Hps & Hnp3 & _).
  unfold rs_at_cx in Hat.
  pa_take Hat (LReg 9) (e_R (x_e cx)) A9.
  pa_take Hat (LReg 6) (Z.of_nat (length ps) - 1) A6.
  pa_take Hat (LReg 17) (rs_cur rsegs cx rest r) A17.
  pa_take Hat (LReg 12) (rs_seen ps) A12.
  pa_take Hat (LCell XR 0x108) np An.
  rewrite Z.mod_small in An by lia.
  pose proof Hcore as (HJ & _).
  eapply SRr_bind.
  { refine (pa_latch7 B MT MTL LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs2 (e_R (x_e cx)) (Z.of_nat (length ps) - 1)
      (rs_seen ps) np (rs_cur rsegs cx rest r) HJ A9 A6 A17 A12 _ _ An _ _ _); lia. }
  intros W3 c3 Hle (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & Hkeep & Hfr & Hperm & Hio & Hmo & Hmem & HR).
  destruct HR as (R6 & R20 & R18 & R10).
  pose proof (pa_mem_all _ _ _ _ Hmem) as Hall.
  destruct (Hstep ly2 S2 W2 regs2 mem2 md2 sh np ps r W3 ly3 S3 regs3 mem3 md3 Hb HJ3
    ltac:(pa_regs234 Hkeep) Hfr Hperm Hio Hmo Hmem) as (Hcore3 & Hfsh3 & Hpp3).
  assert (Hat' : rs_at rsegs (w_H W2) mem2 regs2 (x_e cx) (pa_L_kept cx sh np rest r)).
  { unfold pa_L_kept. pa_list; pa_from Hat. }
  assert (Hat3 : rs_at rsegs (w_H W3) mem3 regs3 (x_e cx) (pa_L_kept cx sh np rest r)).
  { eapply pa_at_move; [exact Hat'|]. unfold pa_L_kept. pa_kept Hkeep ltac:(apply Hall). }
  exact (pa_latch_end cx POST rest i ly2 S2 W2 regs2 mem2 md2 sh np ps r W3 ly3 S3 regs3 mem3 md3
    Hlen0 HN HP1 Hlen Hb Hcore3 Hat3 Hfsh3 Hpp3 R6 R20 R18).
Qed.
End p.

Print Assumptions pa_piece_latch.
