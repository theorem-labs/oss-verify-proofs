(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgPropIntB.v at a529a88a618 (pa_i_memset_at, as
   hbp_i_memset_at; pa_i_bv5_cases, pa_i_cs, pa_i_pres and pa_i_mod16_sub, as hbp_i_*; pa_int7's route, one engine state
   up to each call and a fresh one after it) and proofs/reac-pw/fuzz_role/lib/A/RPgProp.v at a529a88a618
   (pa_piece_int7, as hbp_piece_int7) for reac-pw/fuzz_headamp's image B: the block walked new against image B's own
   instructions (the scope stores of e, __asan_memset of e's body, the two header words, the out-of-line pod_write_ent
   under PweSpec.pod_write_ent_specX, the restores of the loop's three values), the cut states of lib/AU/HPgSeg.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/AU/HPgPropInt.v, with its module paths and module names changed; 245 of its 314 lines of code are new or changed and 892 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgPropSel.v at a529a88a6181 (the latch blocks
   pa_latch / pa_latch7) and the latch piece pa_piece_latch of proofs/reac-pw/fuzz_role/lib/A/RPgProp.v at the same
   commit, for reac-pw/fuzz_rate image A: rate's pcs and real-frame cells (i at R+0xf8, seen' at R+0xc8, np at
   R+0xd0); the latch's third entry 0x8252c (pa_latchi, from the Int-7 piece with i in a6) is new; the block post is
   lib/A/RtPgSteps.v rts_post; the cut lists are lib/A/RtPgSeg.v's. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgPropSel.v at a67a3bd733f9 for image B
   (fuzz_rate.asan-ubsan): image B's latch has two entries (no LATCHI): 0x82578 (seen from R+0x98) and 0x8257c (seen in
   a3), the index in t0, the cursor moved from s10 to s2 and seen into s6 by the latch itself, np from R+0x118; the
   block post is lib/AU/RtPgStepsB.v rtsb_post; the cut lists are lib/AU/RtPgSegB.v's. *)
(* reac-pw/fuzz_rate image B (fuzz_rate.asan-ubsan, pinned sha256
   c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14; every address below is measured on its unstripped
   twin sha256 a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1): the property loop's latch of
   LLVMFuzzerTestOneInput, from its two entries, as block lemmas over lib/AU/RtPgPropBKit.v, and the piece
   rsb_piece_W4_latch_stmt (LATCH / LATCH7 -> N / P1) of lib/AU/RtPgSegB.v. Proves no function (kind: segment
   lemma).
     0x82578 ld a3,0x98(s1)   seen         (LATCH, from the Struct's close)
     0x8257c addiw t0,t0,1    i + 1        (LATCH7, from the shape-7 and the Int-7 pieces: seen already in a3)
     0x82580 mv s2,s10        the cursor
     0x82584 mv s6,a3         seen
     0x82588 ld a0,0x118(s1)  np
     0x8258c beq t0,a0,0x82688 (P1)
     0x82590 j 0x80fb4 (N)
   The block writes no memory. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Model Layout.
Require OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgImgB RtPgStepsB RtPgMemB.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgSegB RtPgPropBKit RtPgPropBLib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* image B's loaded segments, as lib/AU/RtPgStepsB.v names them *)
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.M.loaded_segments.

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
Lemma pab_l_soff : forall {fx : YK11.FPState} E n v c, ew E n = Z_to_bv 64 v -> sv_denot E (SOff n c) = Z_to_bv 64 (v + c).
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
Local Notation pab_post := (rtsb_post B MT).

(* what the latch computes, from either entry: t0 = i + 1, s2 = the cursor, s6 = seen, a0 = np *)
Definition pab_latch_R (i seen np cur : Z) (W2 : world rsegs) (regs2 : bvmap 5 word) (mem2 : word -> option byte)
: Prop :=
getr regs2 5 = w64 (i + 1) /\ getr regs2 18 = w64 cur /\ getr regs2 22 = w64 seen /\ getr regs2 10 = w64 np.

(* ---- the latch 0x82578 -> N 0x80fb4 / P1 0x82688: seen and np from their cells ---- *)
Definition pab_latch_facts : facts :=
mkFacts [ (5%nat, mkAF 0 2 0); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (33%nat, mkAF 0 1 0); (34%nat, mkAF 1 3 0) ]
[] [].
Definition pab_ss_latch : sstate :=
mkSS PAB_LATCH sr_atoms
[ YP09.mkRegion (Some 9%nat) 0x98 0x120 0 0
  [ YP09.mkChunk 0x98 (CVal 8 (SOff 33 0)); YP09.mkChunk 0x118 (CVal 8 (SOff 34 0)) ] ]
None pab_latch_facts.
Lemma pab_latch : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
  (R i seen np cur : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs 9 = w64 R -> getr regs 5 = w64 i -> getr regs 26 = w64 cur -> 0 <= R -> R + 0x120 <= 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x98) 8 seen ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x118) 8 np ->
0 <= i -> i < np -> np <= 3 -> 0 <= seen <= 1 ->
SRr rsegs W (cfg_at rsegs PAB_LATCH regs memc mdc)
(pab_post STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc (if i + 1 =? np then PAB_P1 else PAB_N)
[5; 10; 13; 18; 22]%bv (fun _ => False) (pab_latch_R i seen np cur)).
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R i seen np cur HJ H9 H5 H26 HR0 HR1 Vs Vn
  Hi0 Hin Hn3 Hs.
pose proof rtsb_wx as Hwx. pose proof rtsb_segs_low as Hsegs.
assert (E9 : bv_unsigned (ew (Ereg regs (pab_extra [seen; np])) 9) = R) by (rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl), H9; unfold w64; apply unsigned_lit_small; lia).
assert (E5 : ew (Ereg regs (pab_extra [seen; np])) 5 = Z_to_bv 64 i) by (rewrite (ew_Ereg_nat regs _ 5 5%bv eq_refl), H5; reflexivity).
assert (E26 : ew (Ereg regs (pab_extra [seen; np])) 26 = Z_to_bv 64 cur) by (rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl), H26; reflexivity).
assert (E33 : ew (Ereg regs (pab_extra [seen; np])) 33 = Z_to_bv 64 seen) by reflexivity.
assert (E34 : ew (Ereg regs (pab_extra [seen; np])) 34 = Z_to_bv 64 np) by reflexivity.
assert (HS : st_ok rsegs (Ereg regs (pab_extra [seen; np])) pab_ss_latch (restrict (w_H W) (mkst regs (Z_to_bv 64 PAB_LATCH) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E9.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat constructor; (eapply pab_chunk8; [ cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; eassumption
      | lia | eassumption ]).
  - apply pairwise_disjoint_of_extents. cbn. tauto.
  - split; [|split; [exact I | exact I]]. cbn [pab_latch_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E5, E33, E34, pab_extra_K. rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
    repeat split; try lia; apply Z.mod_1_r. }
remember (Ereg regs (pab_extra [seen; np])) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs (pab_extra [seen; np])) E) by (subst E; apply env_agree_refl).
clear HE.
assert (SHOK : sh_ok rsegs PABBx [] E (mrestrict (w_H W) memc)) by constructor.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview rsegs (w_H W) memc a = aview rsegs (w_H W) memc a)
by (intros; reflexivity).
unfold cfg_at. change (w64 PAB_LATCH) with (Z_to_bv 64 PAB_LATCH).
(* 0x82578 .. 0x82588, stop at the beq 0x8258c *)
pab_runb. pab_keep pab_kwr_ro.
pab_branch Hc; rewrite branch_eq_U, !U_SOff, E5, E34, !unsigned_lit_small in Hc by lia;
rewrite !zcanon_id in Hc by (unfold M64; lia);
first [apply (proj1 (Z.eqb_eq _ _)) in Hc | apply (proj1 (Z.eqb_neq _ _)) in Hc].
- replace (if i + 1 =? np then PAB_P1 else PAB_N) with PAB_P1 by (destruct (Z.eqb_spec (i + 1) np); [reflexivity | lia]).
  pab_run PAB_P1. pab_keep pab_kwr_ro.
  pab_leaf (pab_extra [seen; np]).
  unfold pab_latch_R. pab_reg (5%bv : bv 5). pab_reg (18%bv : bv 5). pab_reg (22%bv : bv 5). pab_reg (10%bv : bv 5).
  unfold w64. rewrite (pab_l_soff E 5 i 1 E5), (pab_l_soff E 26 cur 0 E26), (pab_l_soff E 33 seen 0 E33),
    (pab_l_soff E 34 np 0 E34), !Z.add_0_r. auto.
- replace (if i + 1 =? np then PAB_P1 else PAB_N) with PAB_N by (destruct (Z.eqb_spec (i + 1) np); [lia | reflexivity]).
  pab_run PAB_N. pab_keep pab_kwr_ro.
  pab_leaf (pab_extra [seen; np]).
  unfold pab_latch_R. pab_reg (5%bv : bv 5). pab_reg (18%bv : bv 5). pab_reg (22%bv : bv 5). pab_reg (10%bv : bv 5).
  unfold w64. rewrite (pab_l_soff E 5 i 1 E5), (pab_l_soff E 26 cur 0 E26), (pab_l_soff E 33 seen 0 E33),
    (pab_l_soff E 34 np 0 E34), !Z.add_0_r. auto.
Qed.

(* ---- the latch's second entry 0x8257c (from the shape-7 and the Int-7 pieces: seen already in a3) ---- *)
Definition pab_latch7_facts : facts :=
mkFacts [ (5%nat, mkAF 0 2 0); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (33%nat, mkAF 1 3 0) ] [] [].
Definition pab_ss_latch7 : sstate :=
mkSS PAB_LATCH7 sr_atoms
[ YP09.mkRegion (Some 9%nat) 0x118 0x120 0 0 [ YP09.mkChunk 0x118 (CVal 8 (SOff 33 0)) ] ]
None pab_latch7_facts.
Lemma pab_latch7 : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
  (R i seen np cur : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs 9 = w64 R -> getr regs 5 = w64 i -> getr regs 26 = w64 cur -> getr regs 13 = w64 seen ->
0 <= R -> R + 0x120 <= 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x118) 8 np ->
0 <= i -> i < np -> np <= 3 ->
SRr rsegs W (cfg_at rsegs PAB_LATCH7 regs memc mdc)
(pab_post STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc (if i + 1 =? np then PAB_P1 else PAB_N)
[5; 10; 18; 22]%bv (fun _ => False) (pab_latch_R i seen np cur)).
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R i seen np cur HJ H9 H5 H26 H13 HR0 HR1 Vn
  Hi0 Hin Hn3.
pose proof rtsb_wx as Hwx. pose proof rtsb_segs_low as Hsegs.
assert (E9 : bv_unsigned (ew (Ereg regs (pab_extra [np])) 9) = R) by (rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl), H9; unfold w64; apply unsigned_lit_small; lia).
assert (E5 : ew (Ereg regs (pab_extra [np])) 5 = Z_to_bv 64 i) by (rewrite (ew_Ereg_nat regs _ 5 5%bv eq_refl), H5; reflexivity).
assert (E26 : ew (Ereg regs (pab_extra [np])) 26 = Z_to_bv 64 cur) by (rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl), H26; reflexivity).
assert (E13 : ew (Ereg regs (pab_extra [np])) 13 = Z_to_bv 64 seen) by (rewrite (ew_Ereg_nat regs _ 13 13%bv eq_refl), H13; reflexivity).
assert (E33 : ew (Ereg regs (pab_extra [np])) 33 = Z_to_bv 64 np) by reflexivity.
assert (HS : st_ok rsegs (Ereg regs (pab_extra [np])) pab_ss_latch7 (restrict (w_H W) (mkst regs (Z_to_bv 64 PAB_LATCH7) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E9.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat constructor; (eapply pab_chunk8; [ cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; eassumption
      | lia | eassumption ]).
  - apply pairwise_disjoint_of_extents. cbn. tauto.
  - split; [|split; [exact I | exact I]]. cbn [pab_latch7_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E5, E33, pab_extra_K. rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
    repeat split; try lia; apply Z.mod_1_r. }
remember (Ereg regs (pab_extra [np])) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regs (pab_extra [np])) E) by (subst E; apply env_agree_refl).
clear HE.
assert (SHOK : sh_ok rsegs PABBx [] E (mrestrict (w_H W) memc)) by constructor.
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview rsegs (w_H W) memc a = aview rsegs (w_H W) memc a)
by (intros; reflexivity).
unfold cfg_at. change (w64 PAB_LATCH7) with (Z_to_bv 64 PAB_LATCH7).
(* 0x8257c .. 0x82588, stop at the beq 0x8258c *)
pab_runb. pab_keep pab_kwr_ro.
pab_branch Hc; rewrite branch_eq_U, !U_SOff, E5, E33, !unsigned_lit_small in Hc by lia;
rewrite !zcanon_id in Hc by (unfold M64; lia);
first [apply (proj1 (Z.eqb_eq _ _)) in Hc | apply (proj1 (Z.eqb_neq _ _)) in Hc].
- replace (if i + 1 =? np then PAB_P1 else PAB_N) with PAB_P1 by (destruct (Z.eqb_spec (i + 1) np); [reflexivity | lia]).
  pab_run PAB_P1. pab_keep pab_kwr_ro.
  pab_leaf (pab_extra [np]).
  unfold pab_latch_R. pab_reg (5%bv : bv 5). pab_reg (18%bv : bv 5). pab_reg (22%bv : bv 5). pab_reg (10%bv : bv 5).
  unfold w64. rewrite (pab_l_soff E 5 i 1 E5), (pab_l_soff E 26 cur 0 E26), (pab_l_soff E 13 seen 0 E13),
    (pab_l_soff E 33 np 0 E33), !Z.add_0_r. auto.
- replace (if i + 1 =? np then PAB_P1 else PAB_N) with PAB_N by (destruct (Z.eqb_spec (i + 1) np); [lia | reflexivity]).
  pab_run PAB_N. pab_keep pab_kwr_ro.
  pab_leaf (pab_extra [np]).
  unfold pab_latch_R. pab_reg (5%bv : bv 5). pab_reg (18%bv : bv 5). pab_reg (22%bv : bv 5). pab_reg (10%bv : bv 5).
  unfold w64. rewrite (pab_l_soff E 5 i 1 E5), (pab_l_soff E 26 cur 0 E26), (pab_l_soff E 13 seen 0 E13),
    (pab_l_soff E 33 np 0 E33), !Z.add_0_r. auto.
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

(* the locations of rsb_L_LATCH the latch block keeps (all but t0, which it increments) *)
Definition pab_L_kept (cx : rsb_scx rsegs) (sh np : Z) (rest r : list byte) : list (rt_loc * Z) :=
rsb_Rc rsegs cx ++ rsb_Kc rsegs cx sh np ++ rsb_Hc rsegs cx ++
[(LReg 29, Z.of_nat (length r)); (LReg 26, rsb_cur rsegs cx rest r); (LReg 25, 1)].
(* the end of the latch from either entry: the block's post at regs3 / mem3 with every location of pab_L_kept kept,
   t0 = |ps|, s2 = the cursor and s6 = seen, into the head N (another property is due) or the builder's end P1 *)
Lemma pab_latch_end : forall cx POST rest i ly2 S2 W2 regs2 mem2 md2 sh np ps r W3 ly3 S3 regs3 mem3 md3,
q_len (x_e cx) = rt_len rest ->
rsb_from_N rsegs B MT cx POST rest (S i) -> rsb_from_P1 rsegs B MT cx POST rest ->
(length ps = S i)%nat ->
rsb_latch_body rsegs B MT cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 ->
rsb_core rsegs B MT cx (rsb_E1 rsegs cx) ly3 S3 W3 regs3 mem3 md3 ->
rsb_at rsegs (w_H W3) mem3 regs3 (x_e cx) (pab_L_kept cx sh np rest r) ->
rsb_fsh_at rsegs cx W3 mem3 rsb_P0 -> rsb_pp_at rsegs cx W3 mem3 (pc_image (PbCut sh ps None)) ->
getr regs3 5 = w64 (Z.of_nat (length ps) - 1 + 1) -> getr regs3 18 = w64 (rsb_cur rsegs cx rest r) ->
getr regs3 22 = w64 (rsb_seen ps) ->
SRr rsegs W3 (mkCfg (mkst regs3 (w64 (if Z.of_nat (length ps) - 1 + 1 =? np then PAB_P1 else PAB_N)) mem3
  (seg_rom rsegs)) md3) POST.
Proof.
intros cx POST rest i ly2 S2 W2 regs2 mem2 md2 sh np ps r W3 ly3 S3 regs3 mem3 md3 Hlen0 HN HP1 Hlen Hb Hcore3 Hat3
  Hfsh3 Hpp3 R5 R18 R22.
unfold pab_L_kept in Hat3.
destruct Hb as (_ & _ & _ & Hin & Hsuf & Hwf & Hsh & Hnp & Hps & Hnp3 & Hloop).
destruct (Z.eqb_spec (Z.of_nat (length ps) - 1 + 1) np) as [Heq|Hne].
- change (mkCfg (mkst regs3 (w64 PAB_P1) mem3 (seg_rom rsegs)) md3) with (cfg_at rsegs RSB_P1 regs3 mem3 md3).
  apply (HP1 ly3 S3 W3 regs3 mem3 md3 sh np ps r).
  split.
  + split; [exact Hcore3|]. split; [exact Hfsh3|]. split; [exact Hpp3|]. split; [exact Hin|]. split; [exact Hsuf|].
    split; [exact Hwf|]. split; [exact Hlen0|]. split; [exact Hsh|]. split; [exact Hnp|]. split; [lia | exact Hloop].
  + pab_list; pab_from Hat3.
- change (mkCfg (mkst regs3 (w64 PAB_N) mem3 (seg_rom rsegs)) md3) with (cfg_at rsegs RSB_N regs3 mem3 md3).
  apply (HN ly3 S3 W3 regs3 mem3 md3 sh np ps r Hlen).
  split; [exact Hcore3|]. split.
  + pab_list; first [pab_from Hat3 | idtac].
    * cbn [rt_at]. refine (eq_trans R5 _). f_equal. lia.
    * cbn [rt_at]. exact R22.
    * cbn [rt_at]. exact R18.
  + split; [exact Hfsh3|]. split; [exact Hpp3|]. split; [exact Hin|]. split; [exact Hsuf|]. split; [exact Hwf|].
    split; [exact Hsh|]. split; [exact Hnp|]. split; [lia|]. split; [exact Hnp3 | exact Hloop].
Qed.

Lemma pab_piece_latch : rsb_piece_W4_latch_stmt rsegs B MT.
Proof using MTL LAWS.
unfold rsb_piece_W4_latch_stmt. intros cx POST rest i Hst HN HP1.
destruct Hst as (Hpre & Hfsh0 & Hc1 & Hlen0 & Hin0).
pose proof (pab_R_bounds B cx Hpre) as (RB1 & RB2 & RB3 & RB4 & RB5 & RB6 & RB7).
pose proof asan_consts as (C1 & _).
assert (Hseen : forall ps, 0 <= rsb_seen ps <= 1) by (intros ps; unfold rsb_seen; destruct (existsb _ _); cbn; lia).
(* what either entry leaves of the cut: the journal-and-frame part, the frame's shadow and the first block, for a
   block that writes nothing *)
assert (Hstep : forall ly2 S2 W2 regs2 mem2 md2 sh np ps r W3 ly3 S3 regs3 mem3 md3,
  rsb_latch_body rsegs B MT cx sh np ps rest r ly2 S2 W2 regs2 mem2 md2 ->
  ajournal rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx)
    ly3 S3 W3 mem3 md3 (x_k cx) ->
  (forall r0 : Z, r0 = 2 \/ r0 = 3 \/ r0 = 4 -> getr regs3 (Z_to_bv 5 r0) = getr regs2 (Z_to_bv 5 r0)) ->
  frames S3 = frames S2 -> Permutation (ablocks B ly3 S3) (ablocks B ly2 S2) -> same_io md2 md3 -> mo_le MT S2 S3 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a) ->
  rsb_core rsegs B MT cx (rsb_E1 rsegs cx) ly3 S3 W3 regs3 mem3 md3 /\
  rsb_fsh_at rsegs cx W3 mem3 rsb_P0 /\ rsb_pp_at rsegs cx W3 mem3 (pc_image (PbCut sh ps None))).
{ intros ly2 S2 W2 regs2 mem2 md2 sh np ps r W3 ly3 S3 regs3 mem3 md3 Hb HJ3 Hr3 Hfr Hperm Hio Hmo Hmem.
  pose proof Hb as (Hcore & Hfsh & Hpp & _).
  pose proof (pab_mem_all _ _ _ _ Hmem) as Hall.
  split; [|split].
  - refine (pab_core_step B MT MTL cx _ (fun _ => False) _ _ _ _ _ _ _ _ _ _ _ _ Hcore HJ3 Hr3 Hfr Hperm Hio Hmo Hmem _).
    intros a [].
  - unfold rsb_fsh_at in *. eapply rtmb_fsh_kept; [exact Hfsh|]. intros j Hj. apply Hall.
  - unfold rsb_pp_at in *. eapply (rtmb_bytes_kept rsegs); [exact Hpp|]. intros x Hx. apply Hall. }
split.
- (* LATCH 0x82578: seen and np from their cells *)
  unfold rsb_from_LATCH. intros ly2 S2 W2 regs2 mem2 md2 sh np ps r Hlen Hcut.
  destruct Hcut as [Hb Hat]. pose proof Hb as (Hcore & _ & _ & Hin & _ & _ & _ & _ & Hps & Hnp3 & _).
  unfold rsb_at_cx in Hat.
  pab_take Hat (LReg 9) (q_R (x_e cx)) A9.
  pab_take Hat (LReg 5) (Z.of_nat (length ps) - 1) A5.
  pab_take Hat (LReg 26) (rsb_cur rsegs cx rest r) A26.
  pab_take Hat (LCell XR 0x98) (rsb_seen ps) As.
  pab_take Hat (LCell XR 0x118) np An.
  pose proof (Hseen ps) as Hs.
  rewrite Z.mod_small in As, An by lia.
  pose proof Hcore as (HJ & _).
  eapply SRr_bind.
  { refine (pab_latch B MT MTL LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs2 (q_R (x_e cx)) (Z.of_nat (length ps) - 1)
      (rsb_seen ps) np (rsb_cur rsegs cx rest r) HJ A9 A5 A26 _ _ As An _ _ _ Hs); lia. }
  intros W3 c3 Hle (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & Hkeep & Hfr & Hperm & Hio & Hmo & Hmem & HR).
  destruct HR as (R5 & R18 & R22 & R10).
  pose proof (pab_mem_all _ _ _ _ Hmem) as Hall.
  destruct (Hstep ly2 S2 W2 regs2 mem2 md2 sh np ps r W3 ly3 S3 regs3 mem3 md3 Hb HJ3
    ltac:(pab_regs234 Hkeep) Hfr Hperm Hio Hmo Hmem) as (Hcore3 & Hfsh3 & Hpp3).
  assert (Hat' : rsb_at rsegs (w_H W2) mem2 regs2 (x_e cx) (pab_L_kept cx sh np rest r)).
  { unfold pab_L_kept. pab_list; pab_from Hat. }
  assert (Hat3 : rsb_at rsegs (w_H W3) mem3 regs3 (x_e cx) (pab_L_kept cx sh np rest r)).
  { eapply pab_at_move; [exact Hat'|]. unfold pab_L_kept. pab_kept Hkeep ltac:(apply Hall). }
  exact (pab_latch_end cx POST rest i ly2 S2 W2 regs2 mem2 md2 sh np ps r W3 ly3 S3 regs3 mem3 md3
    Hlen0 HN HP1 Hlen Hb Hcore3 Hat3 Hfsh3 Hpp3 R5 R18 R22).
- (* LATCH7 0x8257c: seen in a3; np from its cell *)
  unfold rsb_from_LATCH7. intros ly2 S2 W2 regs2 mem2 md2 sh np ps r Hlen Hcut.
  destruct Hcut as [Hb Hat]. pose proof Hb as (Hcore & _ & _ & Hin & _ & _ & _ & _ & Hps & Hnp3 & _).
  unfold rsb_at_cx in Hat.
  pab_take Hat (LReg 9) (q_R (x_e cx)) A9.
  pab_take Hat (LReg 5) (Z.of_nat (length ps) - 1) A5.
  pab_take Hat (LReg 26) (rsb_cur rsegs cx rest r) A26.
  pab_take Hat (LReg 13) (rsb_seen ps) A13.
  pab_take Hat (LCell XR 0x118) np An.
  rewrite Z.mod_small in An by lia.
  pose proof Hcore as (HJ & _).
  eapply SRr_bind.
  { refine (pab_latch7 B MT MTL LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs2 (q_R (x_e cx)) (Z.of_nat (length ps) - 1)
      (rsb_seen ps) np (rsb_cur rsegs cx rest r) HJ A9 A5 A26 A13 _ _ An _ _ _); lia. }
  intros W3 c3 Hle (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & Hkeep & Hfr & Hperm & Hio & Hmo & Hmem & HR).
  destruct HR as (R5 & R18 & R22 & R10).
  pose proof (pab_mem_all _ _ _ _ Hmem) as Hall.
  destruct (Hstep ly2 S2 W2 regs2 mem2 md2 sh np ps r W3 ly3 S3 regs3 mem3 md3 Hb HJ3
    ltac:(pab_regs234 Hkeep) Hfr Hperm Hio Hmo Hmem) as (Hcore3 & Hfsh3 & Hpp3).
  assert (Hat' : rsb_at rsegs (w_H W2) mem2 regs2 (x_e cx) (pab_L_kept cx sh np rest r)).
  { unfold pab_L_kept. pab_list; pab_from Hat. }
  assert (Hat3 : rsb_at rsegs (w_H W3) mem3 regs3 (x_e cx) (pab_L_kept cx sh np rest r)).
  { eapply pab_at_move; [exact Hat'|]. unfold pab_L_kept. pab_kept Hkeep ltac:(apply Hall). }
  exact (pab_latch_end cx POST rest i ly2 S2 W2 regs2 mem2 md2 sh np ps r W3 ly3 S3 regs3 mem3 md3
    Hlen0 HN HP1 Hlen Hb Hcore3 Hat3 Hfsh3 Hpp3 R5 R18 R22).
Qed.
End p.

Print Assumptions pab_piece_latch.
