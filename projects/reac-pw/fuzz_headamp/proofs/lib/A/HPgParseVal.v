(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the run plumbing of proofs/reac-pw/fuzz_role/lib/A/RPgCfgChanges.v at 964efd2f474 (cfg_keep, cfg_kwr_ro and the same_io chain of cfg_leaf, as l_keep, l_kwr and l_post) and of proofs/reac-pw/fuzz_qdisc/lib/A/QPgCheck.v at b0f706c04a1 (awr_stk, as l_awr: the writable window is the frame [F, F + 0x60) at atom 2), for a segment of reac_role_prop_parse's walk that starts and ends at the cuts of lib/A/RPgParseBase.v; the entry states, exits, string lemmas and the walk below are new. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgParseL.v at afaa3cb55c1d; for reac-pw/fuzz_rate's reac_rate_prop_parse at image A: module paths and the rl_ / Role names changed to rate's (rt_cstr, rt_fxk, Rate.harness_parse, Rate.RATE_KEY, RtPgStrcmp's rt_cstr_args and cstr_at_of_rt_cstr; kept_run and same_io_wvb from RtPgParseBase), the pcs and image constants are fuzz_rate.asan's (key 0x21720, strcmp wrapper 0x4219c), and on the three next-child paths the foreach back edge 0x84728 beqz is the taken side to L2 (its fall-through 0x8472c j 0x84554 is the impossible one). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgParseL.v; 499 of its 567 lines of code are new or changed and 845 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgParseF.v at afaa3cb55c1d for reac-pw/fuzz_rate's
   reac_rate_prop_parse: module paths and the rl_ / Role names changed to rate's; the pcs are image A's of
   fuzz_rate.asan; the find loop's back edge is 0x845cc beqz -> L1 (taken: the next pass) with 0x845d0 j 0x84554
   (not taken: impossible, r' = 0 mod 4). *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgParseF.v at f7246d55e8c3 for image B
   (fuzz_rate.asan-ubsan); the image is lib/AU/Img0.v's and the cut vocabulary lib/AU/RtPgParseBaseB.v's; the pcs are
   image B's; P + 8 is in a1 (atom 11) at L1, image A's a0; the ret 0 leaves go through 0x84804 li a0,0; the trap
   branch 0x848ac is new and image A's alignment branch 0x84638 is gone. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/AU/RtPgParseFB.v, with its module paths and module names changed; 1564 of its 1625 lines of code are new or changed and 506 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_headamp/lib/Prog/Seg/ParseValue.v at 3e9fc5c8969 (pv_range,
   pv_body, pv_res_big, pv_res_bad, pv_res_bool, pv_res_int, pv_res_flt: the model of value_pod_to_byte and
   value_in_range) with module paths changed and the names prefixed hv_; the engine form of the value read in the
   form of proofs/reac-pw/fuzz_role/lib/A/RPgParseK.v at afaa3cb55c1 (the entry split on the child's size, the pod
   region with the size / type / body chunks, asm_eq / U_asm for the four body bytes put together, br_big / br_ty)
   and the step chain of the double instructions in the form of proofs/reac-pw/fuzz_role/lib/A/RPgParseFV.v at
   afaa3cb55c1 (fvw_auipc, fvw_beq_tk / fvw_beq_ft, fvw_jal0, fv_getr_upd / fv_getr_set), restated for headamp's
   cut states (lib/A/HPgParseCut.v) and the frame hole (lib/A/HPgHole.v). *)
(* reac_headamp_prop_parse_result 0x845b4 of reac-pw/fuzz_headamp's ASan image A (fuzz_headamp.asan, pinned sha256
   f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47; unstripped twin
   b5f352154c54a97c66fd92dfa228e8a854498f6cd313dba0107900546b043f9a, the same loaded bytes except .note.gnu.build-id), segment VAL of its walk:
   lib/A/HPgParseCut.v's segVAL_stmt, from the cut VAL 0x84b30 (the key read as (ch, p); its value is the child at
   cc, s7 = P + cc, a6 = the shadow address of s7) to ADV 0x84b00 (a refusal, or the cell written) or EXIT 0x84890
   (n >= cap). Proves no function by itself (kind: segment lemma).

   The code (measured on the pinned image):
     0x84b30 .. 0x84b34  the instrumented check of s7 (shadow byte at a6; slow path 0x84d70);
     0x84b38 lwu a1,0(s7) = size; 0x84b44 bnez (size >> 20): size >= 2^20 -> 0x84c10 (the refusal);
     0x84b48 .. 0x84b5c  the instrumented lw of the type at s7 + 4 (slow path 0x84d80); a0 = s7 + 8;
     0x84b68 bltu size,4 / 0x84b70 bne type,2: the Bool body (instrumented lw, slow path 0x84d90), snez;
     0x84c28 bltu size,4 / 0x84c30 bne type,4: the Int body (instrumented lw, slow path 0x84dc4), bgeu 255,body;
     0x84c58 bltu size,4 / 0x84c60 bne type,6: the Float body: the 1-byte checks of s7 + 8 and s7 + 11 (slow paths
       0x84dd4 / 0x84de0), four lbu, the u32 put together, sw a0,56(sp); then the double steps 0x84cb4 .. 0x84cf0:
       flw fa5,56(sp); fld fa4 = 0.5 (0x10378); fcvt.d.s; fadd.d; fle.d fs0 (= +0.0), fa5; fld fa4 = 256.0
       (0x10340); flt.d; fcvt.l.d rtz; fcvt.d.l; flt.d; sub a2,a0,a1 = the nearest value; j 0x84b8c;
     every other pod -> 0x84cf4 (the refusal);
     the refusal 0x84c10 / 0x84cf4 / 0x84ba8: a1 = [sp + 24] = rf, a4 = [sp + 32], a5 = 8, a6 = [sp + 48], a7 = 5,
       0x84af0 beqz a1 (rf' = rf, or 5 when rf = 0), s8 = 0, s9 = rf', ADV;
     the value 0x84b8c: a0 = zext.b a2; the reloads; t0 = [sp + 8] (the bound); bgeu a0,t0 -> the refusal;
       0x84bac bge s4,s2 (n >= cap) -> 0x84e40 s9 = [sp + 24], EXIT; else the cell: a0 = s3 + 3 s4 and three
       instrumented sb (ch, p, value; slow paths 0x84da0, 0x84dac, 0x84db8), s8 = 0, addiw s4, s9 = [sp + 24],
       0x849d4 the reloads of a4, a5, a6, ADV.
   The walk is split at internal points, each with its own entry state over HPgParseGKit.hk_env: VAL itself (the
   pod's size, type and body as a region at s7 = atom 23), FL 0x84cb4 (the Float body word stored at sp + 56; the
   double steps are stepped one by one with lib/A/HPgParseFP.v to VV or RF), VV 0x84b8c (the value in a2, atom 55),
   CW 0x84bb0 (the cell's three stores at out + 3 n, atom 54) and RF 0x84cf4 (the refusal). *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05 YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YO0a.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require FP.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Cursor Model Accessors Spa SpaBool Nearest Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog Require ParseFP.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A.Rt Require Import FMupoison.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import Img0 HPgBase HPgCSpec HPgImgA HPgHole.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgParseBase HPgParseCut HPgParseFP.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgParseGKit HPgParseGKey HPgParseGWalk.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require HPgSat.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================================= the model ======================================= *)
(* value_in_range (reac_headamp_prop.c:89-100) is the code's test value < bound (0x84ba8) *)
Definition hv_bnd (p : Z) : Z := if p =? Headamp.HA_SENS then 0x38 else 2.
Lemma hv_range : forall p v, 0 <= p <= Headamp.HA_SENS -> Headamp.value_in_range p v = (v <? hv_bnd p).
Proof.
intros p v Hp. unfold Headamp.HA_SENS in Hp. unfold hv_bnd.
assert (E : p = 0 \/ p = 1 \/ p = 2) by lia.
destruct E as [-> | [-> | ->]];
  unfold Headamp.value_in_range, Headamp.HA_PHANTOM, Headamp.HA_PAD, Headamp.HA_SENS, Headamp.REAC_HEADAMP_SENS_MAX;
  cbv [Z.eqb Pos.eqb orb];
  apply eq_true_iff_eq; rewrite Z.leb_le, Z.ltb_lt; lia.
Qed.

Lemma hv_body : forall bs o, 4 <= Spa.u32_at bs o -> Cursor.rd32 (Model.e_body (Spa.child_at bs o)) = Spa.u32_at bs (o + 8).
Proof.
intros bs o H. unfold Spa.child_at. cbn [Model.e_body]. unfold Cursor.rd32 at 1. rewrite firstn_firstn.
replace (Nat.min 4 (Z.to_nat (Spa.u32_at bs o))) with 4%nat by lia. reflexivity.
Qed.

Lemma hv_res_big : forall bs o, 2 ^ 20 <= Spa.u32_at bs o -> Headamp.parse_value (Spa.child_at bs o) = None.
Proof.
intros bs o H. unfold Headamp.parse_value, SpaBool.spa_get_bool, Spa.spa_get_int, Spa.spa_get_float.
replace (Model.e_size (Spa.child_at bs o)) with (Spa.u32_at bs o) by reflexivity.
unfold Spa.SPA_POD_MAX_SIZE. rewrite (proj2 (Z.ltb_ge _ _) H). reflexivity.
Qed.

Lemma hv_res_bad : forall bs o, Spa.u32_at bs o < 2 ^ 20 ->
(Spa.u32_at bs o < 4 \/ (Spa.u32_at bs (o + 4) <> 2 /\ Spa.u32_at bs (o + 4) <> 4 /\ Spa.u32_at bs (o + 4) <> 6)) ->
Headamp.parse_value (Spa.child_at bs o) = None.
Proof.
intros bs o H1 H2. unfold Headamp.parse_value, SpaBool.spa_get_bool, Spa.spa_get_int, Spa.spa_get_float.
replace (Model.e_size (Spa.child_at bs o)) with (Spa.u32_at bs o) by reflexivity.
replace (Model.e_type (Spa.child_at bs o)) with (Spa.u32_at bs (o + 4)) by reflexivity.
unfold Spa.SPA_POD_MAX_SIZE, Model.POD_BOOL, Model.POD_INT, Model.POD_FLOAT. rewrite (proj2 (Z.ltb_lt _ _) H1).
destruct H2 as [H2|(H3 & H4 & H5)].
- rewrite (proj2 (Z.leb_gt _ _) H2). rewrite !andb_false_r. reflexivity.
- rewrite (proj2 (Z.eqb_neq _ _) H3), (proj2 (Z.eqb_neq _ _) H4), (proj2 (Z.eqb_neq _ _) H5). reflexivity.
Qed.

Lemma hv_res_bool : forall bs o, Spa.u32_at bs o < 2 ^ 20 -> 4 <= Spa.u32_at bs o -> Spa.u32_at bs (o + 4) = 2 ->
Headamp.parse_value (Spa.child_at bs o) = Some (if Spa.u32_at bs (o + 8) =? 0 then 0 else 1).
Proof.
intros bs o H1 H2 H3. unfold Headamp.parse_value, SpaBool.spa_get_bool.
replace (Model.e_size (Spa.child_at bs o)) with (Spa.u32_at bs o) by reflexivity.
replace (Model.e_type (Spa.child_at bs o)) with (Spa.u32_at bs (o + 4)) by reflexivity.
unfold Spa.SPA_POD_MAX_SIZE, Model.POD_BOOL. rewrite H3, (proj2 (Z.ltb_lt _ _) H1), (proj2 (Z.leb_le _ _) H2).
rewrite (hv_body bs o H2). destruct (Spa.u32_at bs (o + 8) =? 0); reflexivity.
Qed.

Lemma hv_res_int : forall bs o, Spa.u32_at bs o < 2 ^ 20 -> 4 <= Spa.u32_at bs o -> Spa.u32_at bs (o + 4) = 4 ->
Headamp.parse_value (Spa.child_at bs o) =
if (Accessors.s32 (Spa.u32_at bs (o + 8)) <? 0) || (255 <? Accessors.s32 (Spa.u32_at bs (o + 8))) then None
else Some (Accessors.s32 (Spa.u32_at bs (o + 8))).
Proof.
intros bs o H1 H2 H3. unfold Headamp.parse_value, SpaBool.spa_get_bool, Spa.spa_get_int.
replace (Model.e_size (Spa.child_at bs o)) with (Spa.u32_at bs o) by reflexivity.
replace (Model.e_type (Spa.child_at bs o)) with (Spa.u32_at bs (o + 4)) by reflexivity.
unfold Spa.SPA_POD_MAX_SIZE, Model.POD_BOOL, Model.POD_INT. rewrite H3, (proj2 (Z.ltb_lt _ _) H1), (proj2 (Z.leb_le _ _) H2).
rewrite (hv_body bs o H2). reflexivity.
Qed.

Lemma hv_res_flt : forall bs o, Spa.u32_at bs o < 2 ^ 20 -> 4 <= Spa.u32_at bs o -> Spa.u32_at bs (o + 4) = 6 ->
Headamp.parse_value (Spa.child_at bs o) = Nearest.nearest (Spa.u32_at bs (o + 8)) 0 255.
Proof.
intros bs o H1 H2 H3. unfold Headamp.parse_value, SpaBool.spa_get_bool, Spa.spa_get_int, Spa.spa_get_float.
replace (Model.e_size (Spa.child_at bs o)) with (Spa.u32_at bs o) by reflexivity.
replace (Model.e_type (Spa.child_at bs o)) with (Spa.u32_at bs (o + 4)) by reflexivity.
unfold Spa.SPA_POD_MAX_SIZE, Model.POD_BOOL, Model.POD_INT, Model.POD_FLOAT.
rewrite H3, (proj2 (Z.ltb_lt _ _) H1), (proj2 (Z.leb_le _ _) H2).
rewrite (hv_body bs o H2). reflexivity.
Qed.

(* the verdict of the value cell for a value v the code computed: inr (ch, p, v) when in range, else the refusal *)
Definition hv_cellv (ch p v : Z) : Z + Headamp.cell :=
if Headamp.value_in_range p v then inr (ch, p, v) else inl Headamp.REFUSE_OUT_OF_RANGE.
Lemma hv_vcell_some : forall ch p e v, Headamp.parse_value e = Some v -> hp_vcell ch p e = hv_cellv ch p v.
Proof. intros ch p e v H. unfold hp_vcell, hv_cellv. rewrite H. reflexivity. Qed.
Lemma hv_vcell_none : forall ch p e, Headamp.parse_value e = None -> hp_vcell ch p e = inl Headamp.REFUSE_OUT_OF_RANGE.
Proof. intros ch p e H. unfold hp_vcell. rewrite H. reflexivity. Qed.

(* ======================================= the engine's states ======================================= *)
(* The env is HPgParseGKit.hk_env (slots 47 .. the segment's values); the token runs take hk_Bx = s11 (atom 27) and
   hk_Bspan; hk_atoms (sp = spa, s0 = sp0, s10, s11) head every state's atom facts.
   The segment's atoms: 47 the child's size, 48 its type, 49 its body, 50 the bound [sp + 8], 51 rf [sp + 24],
   52 P + r + 16 [sp + 32], 53 the shadow address of s7 [sp + 48], 54 O + 3 n, 55 the value. *)
Definition HV_PHI : Z := 0x7fffff800000.
(* a6 at VAL: the shadow address of s7, in the engine's form of `srli; add s11` *)
Definition hv_a6 : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 23 0) (SLit 3)) (SOff 27 0).
(* the frame cells the segment reads, in the temporaries [sp, sp + 0x80) (HPgParseGKit.hk_temps' extent): writable
   only at [sp + 56, sp + 60) on the way from VAL (the Float path's `sw a0,56(sp)`), read-only from VV and RF; every
   other byte of the frame is kept by the runs, the pair loop's cells [sp + 16], [sp + 32], [sp + 40] with it *)
Definition hv_fcs : list YP09.chunk :=
[YP09.mkChunk 8 (CVal 8 (SOff 50 0)); YP09.mkChunk 24 (CVal 8 (SOff 51 0));
 YP09.mkChunk 32 (CVal 8 (SOff 52 0)); YP09.mkChunk 48 (CVal 8 (SOff 53 0))].
Definition hv_tr (w : bool) : YP09.region :=
YP09.mkRegion (Some 2%nat) 0 0x80 (if w then 56 else 0) (if w then 60 else 0) hv_fcs.
(* the child at s7 = P + cc: size, type and, when the size is at least 4, the body *)
Definition hv_hi (big : bool) : Z := if big then 12 else 8.
Definition hv_pod (big : bool) : YP09.region := YP09.mkRegion (Some 23%nat) 0 (hv_hi big) 0 0
  ([YP09.mkChunk 0 (CVal 4 (SOff 47 0)); YP09.mkChunk 4 (CVal 4 (SOff 48 0))] ++
   if big then [YP09.mkChunk 8 (CVal 4 (SOff 49 0))] else []).
(* the out cell [O + 3 n, O + 3 n + 3) at atom 54; the engine's form of s3 + 3 s4, aliased to it *)
Definition hv_out : YP09.region := YP09.mkRegion (Some 54%nat) 0 3 0 3 [].
Definition hv_oaddr : sv := SAlu ALU_ADD (SOff 19 0) (SMd M_MUL (SOff 20 0) (SLit 3)).
Definition hv_atoms_val (big : bool) : list (nat * afact) :=
[(23%nat, mkAF 16 (2 ^ 47 - hv_hi big) 3);
 (20%nat, mkAF 0 9 0); (18%nat, mkAF 0 9 0); (24%nat, mkAF 0 47 0); (13%nat, mkAF 0 2 0);
 (47%nat, if big then mkAF 4 (2 ^ 32 - 1) 0 else mkAF 0 3 0); (48%nat, mkAF 0 (2 ^ 32 - 1) 0);
 (49%nat, mkAF 0 (2 ^ 32 - 1) 0); (50%nat, mkAF 2 56 0); (51%nat, mkAF 0 5 0); (52%nat, mkAF 0 (2 ^ 47) 0);
 (53%nat, mkAF 0 (2 ^ 48) 0)].
Definition hv_ss_val (big : bool) : sstate :=
mkSS PC_VAL (sr_set sr_atoms (16%bv : bv 5) hv_a6) [hv_tr true; hv_pod big] None
  (mkFacts (hk_atoms ++ hv_atoms_val big) [] []).
Definition hv_SH_val (big : bool) : list shent := [mkSHE 23 0 (hv_hi big)].
(* VV 0x84b8c: the value in a2 (atom 55), the frame read-only *)
Definition PC_VV : Z := 0x84b8c.
Definition hv_atoms_vv : list (nat * afact) :=
[(20%nat, mkAF 0 9 0); (18%nat, mkAF 0 9 0); (24%nat, mkAF 0 47 0);
 (13%nat, mkAF 0 2 0); (50%nat, mkAF 2 56 0); (51%nat, mkAF 0 5 0); (52%nat, mkAF 0 (2 ^ 47) 0);
 (53%nat, mkAF 0 (2 ^ 48) 0); (55%nat, mkAF 0 255 0)].
Definition hv_ss_vv : sstate :=
mkSS PC_VV (sr_set sr_atoms (12%bv : bv 5) (SOff 55 0)) [hv_tr false] None (mkFacts (hk_atoms ++ hv_atoms_vv) [] []).
(* CW 0x84bb0: the cell's three stores at O + 3 n (atom 54), out's cell writable *)
Definition PC_CW : Z := 0x84bb0.
Definition hv_atoms_cw : list (nat * afact) :=
[(20%nat, mkAF 0 8 0); (18%nat, mkAF 1 9 0); (19%nat, mkAF 4096 HV_PHI 0); (24%nat, mkAF 0 47 0);
 (13%nat, mkAF 0 2 0); (51%nat, mkAF 0 5 0); (52%nat, mkAF 0 (2 ^ 47) 0);
 (53%nat, mkAF 0 (2 ^ 48) 0); (54%nat, mkAF 4096 HV_PHI 0); (55%nat, mkAF 0 255 0)].
Definition hv_ss_cw : sstate :=
mkSS PC_CW (sr_set sr_atoms (12%bv : bv 5) (SOff 55 0)) [hv_tr false; hv_out] None
  (mkFacts (hk_atoms ++ hv_atoms_cw) [] [(hv_oaddr, SOff 54 0)]).
Definition hv_SH_cw : list shent := [mkSHE 54 0 3].
(* RF 0x84cf4: the refusal *)
Definition PC_RF : Z := 0x84cf4.
Definition hv_atoms_rf : list (nat * afact) :=
[(51%nat, mkAF 0 5 0); (52%nat, mkAF 0 (2 ^ 47) 0); (53%nat, mkAF 0 (2 ^ 48) 0)].
Definition hv_ss_rf : sstate := mkSS PC_RF sr_atoms [hv_tr false] None (mkFacts (hk_atoms ++ hv_atoms_rf) [] []).
(* the Float path's stop after `sw a0,56(sp)` *)
Definition PC_FL : Z := 0x84cb4.

(* the engine's form of the four Float body bytes put together (RPgParseK.v asm_sv, at atom 49) *)
Abbreviation hv_asm := (SAlu ALU_OR
  (SAlu ALU_OR (SAlu ALU_SLL (SAlu ALU_SRL (SOff 49 0) (SLit 24)) (SLit 24))
     (SAlu ALU_SLL (SExt false 8 (SAlu ALU_SRL (SOff 49 0) (SLit 16))) (SLit 16)))
  (SAlu ALU_OR (SAlu ALU_SLL (SExt false 8 (SAlu ALU_SRL (SOff 49 0) (SLit 8))) (SLit 8))
     (SExt false 8 (SOff 49 0)))) (only parsing).

(* ---------------------------------- the engine's arithmetic ---------------------------------- *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgParseK.v at afaa3cb55c1 (asm_eq, U_asm) at
   atom 49 and lib/A/HPgParseFind.v at 3f58f17126dc (hfa_U_srl). *)
(* the 4 bytes of a u32 put together by shifts and ors *)
Lemma hv_asm_eq : forall b, 0 <= b < 2 ^ 32 ->
Z.lor (Z.lor (Z.shiftl (Z.shiftr b 24) 24) (Z.shiftl (Z.shiftr b 16 mod 2 ^ 8) 16))
      (Z.lor (Z.shiftl (Z.shiftr b 8 mod 2 ^ 8) 8) (b mod 2 ^ 8)) = b.
Proof.
intros b Hb. apply Z.bits_inj'. intros i Hi. rewrite !Z.lor_spec.
destruct (Z.lt_ge_cases i 8) as [H8|H8]; [|destruct (Z.lt_ge_cases i 16) as [H16|H16];
  [|destruct (Z.lt_ge_cases i 24) as [H24|H24]]].
- rewrite (Z.shiftl_spec_low (Z.shiftr b 24) 24 i) by lia.
  rewrite (Z.shiftl_spec_low (Z.shiftr b 16 mod 2 ^ 8) 16 i) by lia.
  rewrite (Z.shiftl_spec_low (Z.shiftr b 8 mod 2 ^ 8) 8 i) by lia.
  rewrite (Z.mod_pow2_bits_low b 8 i) by lia. reflexivity.
- rewrite (Z.shiftl_spec_low (Z.shiftr b 24) 24 i) by lia.
  rewrite (Z.shiftl_spec_low (Z.shiftr b 16 mod 2 ^ 8) 16 i) by lia.
  rewrite (Z.shiftl_spec (Z.shiftr b 8 mod 2 ^ 8) 8 i) by lia.
  rewrite (Z.mod_pow2_bits_low (Z.shiftr b 8) 8 (i - 8)) by lia.
  rewrite (Z.shiftr_spec b 8 (i - 8)) by lia. replace (i - 8 + 8) with i by lia.
  rewrite (Z.mod_pow2_bits_high b 8 i) by lia. destruct (Z.testbit b i); reflexivity.
- rewrite (Z.shiftl_spec_low (Z.shiftr b 24) 24 i) by lia.
  rewrite (Z.shiftl_spec (Z.shiftr b 16 mod 2 ^ 8) 16 i) by lia.
  rewrite (Z.mod_pow2_bits_low (Z.shiftr b 16) 8 (i - 16)) by lia.
  rewrite (Z.shiftr_spec b 16 (i - 16)) by lia. replace (i - 16 + 16) with i by lia.
  rewrite (Z.shiftl_spec (Z.shiftr b 8 mod 2 ^ 8) 8 i) by lia.
  rewrite (Z.mod_pow2_bits_high (Z.shiftr b 8) 8 (i - 8)) by lia.
  rewrite (Z.mod_pow2_bits_high b 8 i) by lia. destruct (Z.testbit b i); reflexivity.
- rewrite (Z.shiftl_spec (Z.shiftr b 24) 24 i) by lia.
  rewrite (Z.shiftr_spec b 24 (i - 24)) by lia. replace (i - 24 + 24) with i by lia.
  rewrite (Z.shiftl_spec (Z.shiftr b 16 mod 2 ^ 8) 16 i) by lia.
  rewrite (Z.mod_pow2_bits_high (Z.shiftr b 16) 8 (i - 16)) by lia.
  rewrite (Z.shiftl_spec (Z.shiftr b 8 mod 2 ^ 8) 8 i) by lia.
  rewrite (Z.mod_pow2_bits_high (Z.shiftr b 8) 8 (i - 8)) by lia.
  rewrite (Z.mod_pow2_bits_high b 8 i) by lia. destruct (Z.testbit b i); reflexivity.
Qed.

Lemma hv_U_asm : forall E b, U E (SOff 49 0) = b -> 0 <= b < 2 ^ 32 -> U E hv_asm = b.
Proof.
intros E b U0 Hb.
assert (Rs : forall k, 0 <= k -> 0 <= Z.shiftr b k <= b).
{ intros k Hk. rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia]|].
  apply Z.div_le_upper_bound; [apply Z.pow_pos_nonneg; lia|]. assert (1 <= 2 ^ k) by (apply Z.pow_le_mono_r with (a := 2) in Hk; lia). nia. }
assert (Us : forall k, 0 <= k < 64 -> U E (SAlu ALU_SRL (SOff 49 0) (SLit k)) = Z.shiftr b k).
{ intros k Hk. rewrite U_SAlu, U0, U_SLit. cbn [zalu_raw]. rewrite (zcanon_id k) by (unfold M64; lia).
  replace (Z.land k 63) with k by (change 63 with (Z.ones 6); rewrite Z.land_ones by lia; rewrite Z.mod_small; [reflexivity|]; change (2 ^ 6) with 64; lia).
  pose proof (Rs k ltac:(lia)). apply zcanon_id. unfold M64. lia. }
assert (Ue : forall e v, U E e = v -> U E (SExt false 8 e) = v mod 2 ^ 8).
{ intros e v Hv. rewrite U_SExt, Hv. cbv iota. change (2 ^ Z.of_N 8) with (2 ^ 8).
  apply zcanon_id. pose proof (Z.mod_pos_bound v (2 ^ 8) ltac:(lia)). unfold M64. lia. }
assert (Ul : forall e v k, U E e = v -> 0 <= k < 64 -> 0 <= Z.shiftl v k < 2 ^ 32 -> U E (SAlu ALU_SLL e (SLit k)) = Z.shiftl v k).
{ intros e v k Hv Hk Hr. rewrite U_SAlu, Hv, U_SLit. cbn [zalu_raw]. rewrite (zcanon_id k) by (unfold M64; lia).
  replace (Z.land k 63) with k by (change 63 with (Z.ones 6); rewrite Z.land_ones by lia; rewrite Z.mod_small; [reflexivity|]; change (2 ^ 6) with 64; lia).
  apply zcanon_id. unfold M64. lia. }
assert (Uo : forall e1 e2 v1 v2, U E e1 = v1 -> U E e2 = v2 -> 0 <= v1 < 2 ^ 32 -> 0 <= v2 < 2 ^ 32 ->
  U E (SAlu ALU_OR e1 e2) = Z.lor v1 v2 /\ 0 <= Z.lor v1 v2 < 2 ^ 32).
{ intros e1 e2 v1 v2 H1 H2 R1 R2. pose proof (YO0a.lor_range v1 v2 32 R1 R2) as R.
  split; [|exact R]. rewrite U_SAlu, H1, H2. cbn [zalu_raw]. apply zcanon_id. unfold M64. lia. }
assert (Bm : forall v, 0 <= v mod 2 ^ 8 < 2 ^ 8) by (intros v; apply Z.mod_pos_bound; lia).
assert (Bl : forall v k, 0 <= v < 2 ^ 8 -> 0 <= k <= 24 -> 0 <= Z.shiftl v k < 2 ^ (8 + k)).
{ intros v k Hv Hk. rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.pow_add_r by lia.
  assert (0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia). nia. }
assert (B24 : 0 <= Z.shiftr b 24 < 2 ^ 8).
{ rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia. }
pose proof (Bl _ 24 B24 ltac:(lia)) as L3.
pose proof (Bl _ 16 (Bm (Z.shiftr b 16)) ltac:(lia)) as L2.
pose proof (Bl _ 8 (Bm (Z.shiftr b 8)) ltac:(lia)) as L1.
change (2 ^ (8 + 24)) with (2 ^ 32) in L3.
assert (L2' : 0 <= Z.shiftl (Z.shiftr b 16 mod 2 ^ 8) 16 < 2 ^ 32) by (change (2 ^ (8 + 16)) with (2 ^ 24) in L2; lia).
assert (L1' : 0 <= Z.shiftl (Z.shiftr b 8 mod 2 ^ 8) 8 < 2 ^ 32) by (change (2 ^ (8 + 8)) with (2 ^ 16) in L1; lia).
assert (L0 : 0 <= b mod 2 ^ 8 < 2 ^ 32) by (pose proof (Bm b); lia).
destruct (Uo _ _ _ _ (Ul _ _ 24 (Us 24 ltac:(lia)) ltac:(lia) L3)
  (Ul _ _ 16 (Ue _ _ (Us 16 ltac:(lia))) ltac:(lia) L2') L3 L2') as [UA RA].
destruct (Uo _ _ _ _ (Ul _ _ 8 (Ue _ _ (Us 8 ltac:(lia))) ltac:(lia) L1') (Ue _ _ U0) L1' L0) as [UB RB].
destruct (Uo _ _ _ _ UA UB RA RB) as [UC _]. rewrite UC. apply hv_asm_eq. exact Hb.
Qed.

Lemma hv_U_srl : forall E a b, 0 <= U E b < 64 -> U E (SAlu ALU_SRL a b) = U E a / 2 ^ (U E b).
Proof.
intros E a b H. rewrite U_SAlu. cbn [zalu_raw].
replace 63 with (Z.ones 6) by reflexivity. rewrite Z.land_ones by lia.
change (2 ^ 6) with 64. rewrite (Z.mod_small (U E b)) by lia.
rewrite Z.shiftr_div_pow2 by lia. pose proof (U_range E a) as Ha.
assert (0 < 2 ^ U E b) by (apply Z.pow_pos_nonneg; lia).
assert (U E a / 2 ^ U E b <= U E a) by (apply Z.div_le_upper_bound; [lia|]; nia).
assert (0 <= U E a / 2 ^ U E b) by (apply Z.div_pos; lia).
unfold zcanon, M64. apply Z.mod_small. unfold M64 in Ha. lia.
Qed.

(* sltu of 0 and the sign-extended word: the word is not 0 *)
Lemma hv_U_snez : forall E e w, U E e = w -> U E (SAlu ALU_SLTU (SLit 0) e) = if w =? 0 then 0 else 1.
Proof.
intros E e w Hw. rewrite U_SAlu, U_SLit, Hw. cbn [zalu_raw]. pose proof (U_range E e) as R. rewrite Hw in R.
change (zcanon 0) with 0. destruct (Z.eqb_spec w 0) as [->|Hn].
- reflexivity.
- rewrite (proj2 (Z.ltb_lt 0 w)) by (unfold M64 in R; lia). reflexivity.
Qed.

#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Local Notation pctx := (@hp_ctx rsegs).

(* ======================================= the runs' plumbing ======================================= *)
(* Modified by Theorem Labs, 2026-10: lib/A/HPgParseFind.v at 3f58f17126dc (hfa_kept, hfa_same_io_wvb, hfa_kio,
   hfa_reg_of, hfa_frame_val) generalized to the kept set Wr, to hk_env and to any writable window. *)
Lemma hv_tr_ok : forall E m w, region_ok rsegs E m (hk_temps hv_fcs) -> region_ok rsegs E m (hv_tr w).
Proof.
intros E m w H. unfold region_ok, hk_temps, hv_tr in *.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks] in *.
destruct H as (H1 & H2 & H3 & H4). split; [exact H1|]. split; [exact H2|]. split; [|exact H4].
intros o Ho. apply H3. destruct w; lia.
Qed.

(* a run keeps every byte outside its write windows, hence outside any Wr holding them *)
Lemma hv_kept : forall E rs (H : word -> bool) (m0 m1 m2 : word -> option byte) (Wr : Z -> Prop),
(forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> mrestrict H m1 (Z_to_bv 64 a) = mrestrict H m0 (Z_to_bv 64 a)) ->
frame_of E rs (mrestrict H m1) (mrestrict H m2) ->
(forall a, in_wrange E rs a -> Wr a) ->
forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> mrestrict H m2 (Z_to_bv 64 a) = mrestrict H m0 (Z_to_bv 64 a).
Proof.
intros E rs H m0 m1 m2 Wr HK HF HW a Ha Hn.
rewrite <- (HK a Ha Hn). apply HF. rewrite unsigned_lit_small by exact Ha. intros X. exact (Hn (HW a X)).
Qed.

(* a cell outside the changed bytes *)
Lemma hv_vm_kept : forall (m m2 : word -> option byte) a (n : nat) v (Wr : Z -> Prop),
(forall b, 0 <= b < 2 ^ 64 -> ~ Wr b -> m2 (Z_to_bv 64 b) = m (Z_to_bv 64 b)) ->
0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> (forall b, a <= b < a + Z.of_nat n -> ~ Wr b) ->
val_mem rsegs m a n v -> val_mem rsegs m2 a n v.
Proof.
intros m m2 a n v Wr K H0 H1 H2 HV k Hk. rewrite <- (HV k Hk). unfold mbyte.
rewrite K; [reflexivity | lia | apply H2; lia].
Qed.

Lemma hv_same_io_wvb : forall md l X, same_io md (with_vm_backing l X md).
Proof. intros md l X. unfold same_io. repeat split; reflexivity. Qed.
Ltac hv_kio := let rec go := first [ apply same_io_refl | (eapply same_io_trans; [| apply hv_same_io_wvb]); go ] in go.

Section fs. Context {fs : YK11.FPState}.
(* a register the walk did not touch: still the one it entered with *)
Lemma hv_reg_of : forall regs E0 E ss ms (H : word -> bool) (q : bv 5) (n k : nat),
st_ok rsegs E ss (restrict H ms) -> sr_get (ss_regs ss) q = SOff n 0 ->
env_agree k E0 E -> (n < k)%nat -> ew E0 n = getr regs q ->
getr (ms_regs ms) q = getr regs q.
Proof.
intros regs E0 E ss ms H q n k HS Hsr HAE Hn Hq.
rewrite (st_ok_restrict_reg rsegs H E ss ms q HS), Hsr.
cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. rewrite (proj1 HAE n Hn). exact Hq.
Qed.

(* a cell of the temporaries region (the first region, at sp) after a run *)
Lemma hv_frame_val : forall E ss ms (H : word -> bool) rest wlo whi cs off (n : N) e v,
st_ok rsegs E ss (restrict H ms) -> ss_mem ss = YP09.mkRegion (Some 2%nat) 0 0x80 wlo whi cs :: rest ->
In (YP09.mkChunk off (CVal n e)) cs -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N n) -> Z.of_N n <= 8 ->
val_mem rsegs (mrestrict H (ms_mem ms)) (bv_unsigned (ew E 2) + off) (N.to_nat n) v.
Proof.
intros E ss ms H rest wlo whi cs off n e v HS Hm Hin He Hv Hn.
pose proof (st_ok_mem_ok rsegs E ss (restrict H ms) HS) as (_ & HF & _).
rewrite Hm in HF. inversion HF as [|r0 l0 HR _]; subst.
destruct HR as (_ & _ & _ & HC). cbn [YP09.r_chunks YP09.r_base base_val] in HC.
apply (val_of_chunk_ok rsegs E _ _ off n e v); [| exact He | exact Hv | exact Hn].
rewrite Forall_forall in HC. exact (HC _ Hin).
Qed.

(* a byte of out's cell (the second region, at atom 54) after a run *)
Lemma hv_out_val : forall E ss ms (H : word -> bool) r0 rest cs off e v,
st_ok rsegs E ss (restrict H ms) -> ss_mem ss = r0 :: YP09.mkRegion (Some 54%nat) 0 3 0 3 cs :: rest ->
In (YP09.mkChunk off (CVal 1 e)) cs -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 256 ->
val_mem rsegs (mrestrict H (ms_mem ms)) (bv_unsigned (ew E 54) + off) 1 v.
Proof.
intros E ss ms H r0 rest cs off e v HS Hm Hin He Hv.
pose proof (st_ok_mem_ok rsegs E ss (restrict H ms) HS) as (_ & HF & _).
rewrite Hm in HF. inversion HF as [|r1 l1 _ HF2]; subst. inversion HF2 as [|r2 l2 HR _]; subst.
destruct HR as (_ & _ & _ & HC). cbn [YP09.r_chunks YP09.r_base base_val] in HC.
apply (val_of_chunk_ok rsegs E _ _ off 1 e v); [| exact He | cbn; lia | cbn; lia].
rewrite Forall_forall in HC. exact (HC _ Hin).
Qed.
End fs.

(* ======================================= the Float path's double steps ======================================= *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgParseFV.v at afaa3cb55c1 (fvw_auipc,
   fvw_beq_tk, fvw_beq_ft, fvw_jal0, fv_getr_upd, fv_getr_set, fv_dec, and the chain of fv_head / fv_mid / fv_tail)
   over image A's table pa_tbl and pcs 0x84cb4 .. 0x84cf0, with lib/A/HPgParseFP.v's double steps. *)
Definition D_HALF : Z := 0x3fe0000000000000.
Definition D_256 : Z := 0x4070000000000000.
Ltac hv_dec := first [ (vm_compute; reflexivity) | vm_refl_bv ].

Lemma hv_bv_neq1 : forall (j k : bv 5), bv_unsigned k <> bv_unsigned j -> bv_eqb j k = false.
Proof. intros j k H. unfold bv_eqb. apply Z.eqb_neq. intros E. apply H. symmetry. exact E. Qed.
Lemma hv_bv_neq2 : forall (j k : bv 5), bv_unsigned j <> bv_unsigned k -> bv_eqb j k = false.
Proof. intros j k H. unfold bv_eqb. apply Z.eqb_neq. exact H. Qed.
Ltac hv_fneq := apply hv_bv_neq1; assumption.
Ltac hv_rneq := apply hv_bv_neq2; assumption.

Lemma hv_auipc_lit : forall z i, v_auipc (Z_to_bv 64 z) i = Z_to_bv 64 (i + z).
Proof.
intros z i. unfold v_auipc. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 64) with (2 ^ 64). apply Zplus_mod_idemp_r.
Qed.

Section fw. Context {fs : YK11.FPState}.
Lemma hvw_auipc : forall regs mem rom p q wz rd (imm : bv 20) (t : Z),
  clookup pa_tbl p = Some wz -> is_ecall (Z_to_bv 32 wz) = false ->
  decode_any (Z_to_bv 32 wz) = Some (Auipc rd imm, 4%Z) ->
  bv_eqb rd 0 = false -> q = p + 4 -> t = Z.shiftl (bv_signed imm) 12 + p ->
  RiscvSemantics.step rsegs (@mkst fs regs (Z_to_bv 64 p) mem rom) =
  MachineOk (@mkst fs (regupd regs rd (Z_to_bv 64 t)) (Z_to_bv 64 q) mem rom).
Proof.
intros regs mem rom p q wz rd imm t Hc He Hd Hrd Hq Ht.
rewrite (step_auipc rsegs regs (Z_to_bv 64 p) mem rom (Z_to_bv 32 wz) rd imm (pa_tbl_ok p wz Hc) He Hd).
rewrite Hrd, Hq, hfp_addi_lit, hv_auipc_lit, Ht. reflexivity.
Qed.

Lemma hvw_jal0 : forall regs mem rom p q wz (imm : bv 21),
  clookup pa_tbl p = Some wz -> is_ecall (Z_to_bv 32 wz) = false ->
  decode_any (Z_to_bv 32 wz) = Some (Jal 0 imm, 4%Z) -> q = p + bv_signed imm ->
  RiscvSemantics.step rsegs (@mkst fs regs (Z_to_bv 64 p) mem rom) =
  MachineOk (@mkst fs regs (Z_to_bv 64 q) mem rom).
Proof.
intros regs mem rom p q wz imm Hc He Hd Hq.
rewrite (step_jal_x0 rsegs regs (Z_to_bv 64 p) mem rom (Z_to_bv 32 wz) imm (pa_tbl_ok p wz Hc) He Hd).
unfold btgt. rewrite hfp_addi_lit, Hq. reflexivity.
Qed.

Lemma hvw_beq_tk : forall regs mem rom p q wz rs1 rs2 (imm : bv 13),
  clookup pa_tbl p = Some wz -> is_ecall (Z_to_bv 32 wz) = false ->
  decode_any (Z_to_bv 32 wz) = Some (Branch BC_EQ rs1 rs2 imm, 4%Z) ->
  getr regs rs1 = getr regs rs2 -> q = p + bv_signed imm ->
  RiscvSemantics.step rsegs (@mkst fs regs (Z_to_bv 64 p) mem rom) =
  MachineOk (@mkst fs regs (Z_to_bv 64 q) mem rom).
Proof.
intros regs mem rom p q wz rs1 rs2 imm Hc He Hd Hr Hq.
rewrite (step_branch_tk_gen rsegs regs (Z_to_bv 64 p) mem rom (Z_to_bv 32 wz) BC_EQ rs1 rs2 imm
  (pa_tbl_ok p wz Hc) He Hd).
- unfold btgt. rewrite hfp_addi_lit, Hq. reflexivity.
- cbn [branch_taken]. rewrite Hr. apply bv_eqb_refl.
Qed.

Lemma hvw_beq_ft : forall regs mem rom p q wz rs1 rs2 (imm : bv 13) (u v : Z),
  clookup pa_tbl p = Some wz -> is_ecall (Z_to_bv 32 wz) = false ->
  decode_any (Z_to_bv 32 wz) = Some (Branch BC_EQ rs1 rs2 imm, 4%Z) ->
  getr regs rs1 = Z_to_bv 64 u -> getr regs rs2 = Z_to_bv 64 v ->
  0 <= u < 2 ^ 64 -> 0 <= v < 2 ^ 64 -> u <> v -> q = p + 4 ->
  RiscvSemantics.step rsegs (@mkst fs regs (Z_to_bv 64 p) mem rom) =
  MachineOk (@mkst fs regs (Z_to_bv 64 q) mem rom).
Proof.
intros regs mem rom p q wz rs1 rs2 imm u v Hc He Hd H1 H2 Hu Hv Hne Hq.
rewrite (step_branch_ft_gen rsegs regs (Z_to_bv 64 p) mem rom (Z_to_bv 32 wz) BC_EQ rs1 rs2 imm
  (pa_tbl_ok p wz Hc) He Hd).
- rewrite Hq, hfp_addi_lit. reflexivity.
- cbn [branch_taken]. rewrite H1, H2. unfold bv_eqb.
  rewrite !unsigned_lit_small by assumption. apply Z.eqb_neq. exact Hne.
Qed.

Lemma hvw_sub : forall regs mem rom p q wz rd rs1 rs2 (v : word),
  clookup pa_tbl p = Some wz -> is_ecall (Z_to_bv 32 wz) = false ->
  decode_any (Z_to_bv 32 wz) = Some (Op ALU_SUB rd rs1 rs2, 4%Z) ->
  bv_eqb rd 0 = false -> q = p + 4 -> v_sub (getr regs rs1) (getr regs rs2) = v ->
  RiscvSemantics.step rsegs (@mkst fs regs (Z_to_bv 64 p) mem rom) =
  MachineOk (@mkst fs (regupd regs rd v) (Z_to_bv 64 q) mem rom).
Proof.
intros regs mem rom p q wz rd rs1 rs2 v Hc He Hd Hrd Hq Hv.
rewrite (step_sub_at rsegs regs (Z_to_bv 64 p) mem rom (Z_to_bv 32 wz) rd rs1 rs2 v (pa_tbl_ok p wz Hc) He Hd Hrd Hv).
rewrite Hq, hfp_addi_lit. reflexivity.
Qed.
End fw.

Lemma hv_getr_upd : forall regs (r r' : bv 5) v, bv_eqb r' r = false -> getr (regupd regs r v) r' = getr regs r'.
Proof.
intros regs r r' v H. unfold getr, regupd. destruct (bv_eqb r' 0); [reflexivity|].
unfold reg_get. rewrite bvmap_get_set_other; [reflexivity|].
intros E. unfold bv_eqb in H. apply Z.eqb_neq in H. apply H. rewrite E. reflexivity.
Qed.
Lemma hv_getr_set : forall regs (r r' : bv 5) v, bv_eqb r' r = true -> bv_eqb r' 0 = false ->
  getr (regupd regs r v) r' = v.
Proof.
intros regs r r' v H H0. unfold bv_eqb in H. apply Z.eqb_eq in H. apply bv_eq in H. subst r'.
unfold getr, regupd. rewrite H0. unfold reg_get. rewrite bvmap_get_set_same. reflexivity.
Qed.
Ltac hv_reg := repeat (rewrite hv_getr_upd by (vm_compute; reflexivity));
  try (rewrite hv_getr_set by (vm_compute; reflexivity)).
Ltac hv_freg := repeat (rewrite FP.freg_get_other by (vm_compute; reflexivity));
  try (rewrite FP.freg_get_same by (vm_compute; reflexivity)).

(* 0x84cb4 .. 0x84cf0: flw fa5 = the body word b; fld fa4 = 0.5; fa5 = (double)b + 0.5 (= ParseFP.rfn_d b);
   a0 = (fs0 <= fa5), beqz -> RF; fld fa4 = 256.0; a0 = (fa5 < 256.0), beqz -> RF; a0 = (long)fa5 rtz,
   fa4 = (double)a0, a1 = (fa5 < fa4), a2 = a0 - a1 (= ParseFP.rfn_r b), j VV. *)
Lemma hv_fl_steps : forall (F : bvmap 5 word) (C : bv 32) regs M b spa,
frm_zero C -> Sem.reg_get F 8 = Z_to_bv 64 0 -> getr regs 2 = Z_to_bv 64 spa -> 0 <= b < 2 ^ 32 ->
val_mem rsegs M (spa + 56) 4 b -> val_mem rsegs M 0x10378 8 D_HALF -> val_mem rsegs M 0x10340 8 D_256 ->
exists G C' regs1 pc1,
  msteps rsegs (@mkst (mkFP F C) regs (Z_to_bv 64 PC_FL) M (seg_rom rsegs))
    (@mkst (mkFP G C') regs1 (Z_to_bv 64 pc1) M (seg_rom rsegs)) /\ frm_zero C' /\
  (forall k : bv 5, bv_unsigned k <> 14 -> bv_unsigned k <> 15 -> Sem.reg_get G k = Sem.reg_get F k) /\
  (forall r : bv 5, bv_unsigned r <> 10 -> bv_unsigned r <> 11 -> bv_unsigned r <> 12 -> getr regs1 r = getr regs r) /\
  (if ParseFP.rfn_in b (Z_to_bv 64 0) (Z_to_bv 64 D_256)
   then pc1 = PC_VV /\ getr regs1 12 = Z_to_bv 64 (ParseFP.rfn_r b) else pc1 = PC_RF).
Proof.
intros F C regs M b spa HC H8 H2 Hb Hvb Hhalf H256.
set (rom := seg_rom rsegs).
set (F1 := bvmap_set (15%bv : bv 5) (nan_box (Z_to_bv 32 b)) F).
set (F2 := bvmap_set (14%bv : bv 5) (Z_to_bv 64 D_HALF) F1).
set (R1 := regupd regs 10 (Z_to_bv 64 0xfcb8)).
assert (S1 : RiscvSemantics.step rsegs (@mkst (mkFP F C) regs (Z_to_bv 64 PC_FL) M rom) =
  MachineOk (@mkst (mkFP F1 C) regs (Z_to_bv 64 0x84cb8) M rom)).
{ unfold PC_FL. apply (hfp_tw_flw rsegs pa_tbl pa_tbl_ok (mkFP F C) regs M rom 0x84cb4 0x84cb8 0x03812787 15 2 56 spa
    (spa + 56) b); [hv_dec | hv_dec | hv_dec | reflexivity | exact H2 | vm_compute; reflexivity | exact Hb | exact Hvb]. }
assert (S2 : RiscvSemantics.step rsegs (@mkst (mkFP F1 C) regs (Z_to_bv 64 0x84cb8) M rom) =
  MachineOk (@mkst (mkFP F1 C) R1 (Z_to_bv 64 0x84cbc) M rom)).
{ apply (hvw_auipc regs M rom 0x84cb8 0x84cbc 0xfff8b517 10 0xfff8b 0xfcb8);
    [hv_dec | hv_dec | hv_dec | hv_dec | reflexivity | vm_compute; reflexivity]. }
assert (S3 : RiscvSemantics.step rsegs (@mkst (mkFP F1 C) R1 (Z_to_bv 64 0x84cbc) M rom) =
  MachineOk (@mkst (mkFP F2 C) R1 (Z_to_bv 64 0x84cc0) M rom)).
{ apply (hfp_tw_fld rsegs pa_tbl pa_tbl_ok (mkFP F1 C) R1 M rom 0x84cbc 0x84cc0 0x6c053707 14 10 1728 0xfcb8 0x10378
    D_HALF); [hv_dec | hv_dec | hv_dec | reflexivity | unfold R1; hv_reg; reflexivity | vm_compute; reflexivity
    | unfold D_HALF; lia | exact Hhalf]. }
destruct (hfp_tw_fcvt_d_s rsegs pa_tbl pa_tbl_ok F2 C R1 M rom 0x84cc0 0x84cc4 0x420787d3 15 15 0 (nan_box (Z_to_bv 32 b))
  ltac:(hv_dec) ltac:(hv_dec) ltac:(hv_dec) ltac:(vm_compute; reflexivity) eq_refl
  ltac:(unfold F2, F1; hv_freg; reflexivity) HC) as (C1 & S4 & HC1).
set (F3 := bvmap_set (15%bv : bv 5) (FP.fcvt_d_s RNE (nan_box (Z_to_bv 32 b))) F2) in S4.
destruct (hfp_tw_fadd_d rsegs pa_tbl pa_tbl_ok F3 C1 R1 M rom 0x84cc4 0x84cc8 0x02e7f7d3 15 15 14 7
  (FP.fcvt_d_s RNE (nan_box (Z_to_bv 32 b))) (Z_to_bv 64 D_HALF)
  ltac:(hv_dec) ltac:(hv_dec) ltac:(hv_dec) ltac:(vm_compute; reflexivity) eq_refl
  ltac:(unfold F3; hv_freg; reflexivity) ltac:(unfold F3, F2, F1; hv_freg; reflexivity) HC1) as (C2 & S5 & HC2).
set (F4 := bvmap_set (15%bv : bv 5) (FP.fadd_d RNE (FP.fcvt_d_s RNE (nan_box (Z_to_bv 32 b))) (Z_to_bv 64 D_HALF)) F3) in S5.
assert (HF4 : Sem.reg_get F4 15 = ParseFP.rfn_d b) by (unfold F4; hv_freg; apply hfp_rfn_d).
assert (HF4k : forall k : bv 5, bv_unsigned k <> 14 -> bv_unsigned k <> 15 -> Sem.reg_get F4 k = Sem.reg_get F k).
{ intros k H14 H15. unfold F4, F3, F2, F1.
  rewrite !FP.freg_get_other by hv_fneq. reflexivity. }
destruct (hfp_tw_fle_d rsegs pa_tbl pa_tbl_ok F4 C2 R1 M rom 0x84cc8 0x84ccc 0xa2f40553 10 8 15
  (Z_to_bv 64 0) (ParseFP.rfn_d b) ltac:(hv_dec) ltac:(hv_dec) ltac:(hv_dec) ltac:(vm_compute; reflexivity) eq_refl
  ltac:(rewrite (HF4k 8%bv) by (vm_compute; congruence); exact H8) HF4 HC2) as (C3 & S6 & HC3).
set (R2 := regupd R1 10 (if FP.fle_d (Z_to_bv 64 0) (ParseFP.rfn_d b) then Z_to_bv 64 1 else Z_to_bv 64 0)) in S6.
assert (P6 : msteps rsegs (@mkst (mkFP F C) regs (Z_to_bv 64 PC_FL) M rom) (@mkst (mkFP F4 C3) R2 (Z_to_bv 64 0x84ccc) M rom)).
{ eapply mst_step; [reflexivity | exact S1 |]. eapply mst_step; [reflexivity | exact S2 |].
  eapply mst_step; [reflexivity | exact S3 |]. eapply mst_step; [reflexivity | exact S4 |].
  eapply mst_step; [reflexivity | exact S5 |]. eapply mst_step; [reflexivity | exact S6 |]. apply mst_refl. }
assert (HR2k : forall r : bv 5, bv_unsigned r <> 10 -> getr R2 r = getr regs r).
{ intros r Hr. unfold R2, R1. rewrite !hv_getr_upd by hv_rneq. reflexivity. }
rewrite hfp_rfn_in. change (Z_to_bv 64 0x4070000000000000) with (Z_to_bv 64 D_256).
destruct (FP.fle_d (Z_to_bv 64 0) (ParseFP.rfn_d b)) eqn:Efle.
2:{ (* below the range: 0x84ccc beqz a0 -> RF *)
  assert (S7 : RiscvSemantics.step rsegs (@mkst (mkFP F4 C3) R2 (Z_to_bv 64 0x84ccc) M rom) =
    MachineOk (@mkst (mkFP F4 C3) R2 (Z_to_bv 64 PC_RF) M rom)).
  { unfold PC_RF. apply (hvw_beq_tk R2 M rom 0x84ccc 0x84cf4 0x02050463 10 0 40);
      [hv_dec | hv_dec | hv_dec | | vm_compute; reflexivity].
    unfold R2. try rewrite Efle. hv_reg. reflexivity. }
  exists F4, C3, R2, PC_RF. split; [|split; [exact HC3 | split; [exact HF4k | split]]].
  - eapply msteps_trans; [exact P6|]. eapply mst_step; [reflexivity | exact S7 | apply mst_refl].
  - intros r H10 _ _. exact (HR2k r H10).
  - cbn [andb]. reflexivity. }
(* the low test passed: 0x84ccc .. 0x84cd8 *)
assert (S7 : RiscvSemantics.step rsegs (@mkst (mkFP F4 C3) R2 (Z_to_bv 64 0x84ccc) M rom) =
  MachineOk (@mkst (mkFP F4 C3) R2 (Z_to_bv 64 0x84cd0) M rom)).
{ apply (hvw_beq_ft R2 M rom 0x84ccc 0x84cd0 0x02050463 10 0 40 1 0);
    [hv_dec | hv_dec | hv_dec | unfold R2; try rewrite Efle; hv_reg; reflexivity | reflexivity | lia | lia | lia | reflexivity]. }
set (R3 := regupd R2 10 (Z_to_bv 64 0xfcd0)).
assert (S8 : RiscvSemantics.step rsegs (@mkst (mkFP F4 C3) R2 (Z_to_bv 64 0x84cd0) M rom) =
  MachineOk (@mkst (mkFP F4 C3) R3 (Z_to_bv 64 0x84cd4) M rom)).
{ apply (hvw_auipc R2 M rom 0x84cd0 0x84cd4 0xfff8b517 10 0xfff8b 0xfcd0);
    [hv_dec | hv_dec | hv_dec | hv_dec | reflexivity | vm_compute; reflexivity]. }
set (F5 := bvmap_set (14%bv : bv 5) (Z_to_bv 64 D_256) F4).
assert (S9 : RiscvSemantics.step rsegs (@mkst (mkFP F4 C3) R3 (Z_to_bv 64 0x84cd4) M rom) =
  MachineOk (@mkst (mkFP F5 C3) R3 (Z_to_bv 64 0x84cd8) M rom)).
{ apply (hfp_tw_fld rsegs pa_tbl pa_tbl_ok (mkFP F4 C3) R3 M rom 0x84cd4 0x84cd8 0x67053707 14 10 1648 0xfcd0 0x10340
    D_256); [hv_dec | hv_dec | hv_dec | reflexivity | unfold R3; hv_reg; reflexivity | vm_compute; reflexivity
    | unfold D_256; lia | exact H256]. }
assert (HF5 : Sem.reg_get F5 15 = ParseFP.rfn_d b) by (unfold F5; hv_freg; exact HF4).
destruct (hfp_tw_flt_d rsegs pa_tbl pa_tbl_ok F5 C3 R3 M rom 0x84cd8 0x84cdc 0xa2e79553 10 15 14
  (ParseFP.rfn_d b) (Z_to_bv 64 D_256) ltac:(hv_dec) ltac:(hv_dec) ltac:(hv_dec) ltac:(vm_compute; reflexivity) eq_refl
  HF5 ltac:(unfold F5; hv_freg; reflexivity) HC3) as (C4 & S10 & HC4).
set (R4 := regupd R3 10 (if FP.flt_d (ParseFP.rfn_d b) (Z_to_bv 64 D_256) then Z_to_bv 64 1 else Z_to_bv 64 0)) in S10.
assert (P10 : msteps rsegs (@mkst (mkFP F C) regs (Z_to_bv 64 PC_FL) M rom) (@mkst (mkFP F5 C4) R4 (Z_to_bv 64 0x84cdc) M rom)).
{ eapply msteps_trans; [exact P6|].
  eapply mst_step; [reflexivity | exact S7 |]. eapply mst_step; [reflexivity | exact S8 |].
  eapply mst_step; [reflexivity | exact S9 |]. eapply mst_step; [reflexivity | exact S10 |]. apply mst_refl. }
assert (HF5k : forall k : bv 5, bv_unsigned k <> 14 -> bv_unsigned k <> 15 -> Sem.reg_get F5 k = Sem.reg_get F k).
{ intros k H14 H15. unfold F5. rewrite FP.freg_get_other by hv_fneq. exact (HF4k k H14 H15). }
assert (HR4k : forall r : bv 5, bv_unsigned r <> 10 -> getr R4 r = getr regs r).
{ intros r Hr. unfold R4, R3. rewrite !hv_getr_upd by hv_rneq. exact (HR2k r Hr). }
destruct (FP.flt_d (ParseFP.rfn_d b) (Z_to_bv 64 D_256)) eqn:Eflt.
2:{ (* above the range: 0x84cdc beqz a0 -> RF *)
  assert (S11 : RiscvSemantics.step rsegs (@mkst (mkFP F5 C4) R4 (Z_to_bv 64 0x84cdc) M rom) =
    MachineOk (@mkst (mkFP F5 C4) R4 (Z_to_bv 64 PC_RF) M rom)).
  { unfold PC_RF. apply (hvw_beq_tk R4 M rom 0x84cdc 0x84cf4 0x00050c63 10 0 24);
      [hv_dec | hv_dec | hv_dec | | vm_compute; reflexivity].
    unfold R4. try rewrite Eflt. hv_reg. reflexivity. }
  exists F5, C4, R4, PC_RF. split; [|split; [exact HC4 | split; [exact HF5k | split]]].
  - eapply msteps_trans; [exact P10|]. eapply mst_step; [reflexivity | exact S11 | apply mst_refl].
  - intros r H10 _ _. exact (HR4k r H10).
  - cbn [andb]. reflexivity. }
(* in range: 0x84cdc .. 0x84cf0 *)
assert (S11 : RiscvSemantics.step rsegs (@mkst (mkFP F5 C4) R4 (Z_to_bv 64 0x84cdc) M rom) =
  MachineOk (@mkst (mkFP F5 C4) R4 (Z_to_bv 64 0x84ce0) M rom)).
{ apply (hvw_beq_ft R4 M rom 0x84cdc 0x84ce0 0x00050c63 10 0 24 1 0);
    [hv_dec | hv_dec | hv_dec | unfold R4; try rewrite Eflt; hv_reg; reflexivity | reflexivity | lia | lia | lia | reflexivity]. }
destruct (hfp_tw_fcvt_l_d rsegs pa_tbl pa_tbl_ok F5 C4 R4 M rom 0x84ce0 0x84ce4 0xc2279553 10 15 1 (ParseFP.rfn_d b)
  ltac:(hv_dec) ltac:(hv_dec) ltac:(hv_dec) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl
  HF5 HC4) as (C5 & S12 & HC5).
rewrite hfp_rfn_t in S12.
set (R5 := regupd R4 10 (ParseFP.rfn_t b)) in S12.
destruct (hfp_tw_fcvt_d_l rsegs pa_tbl pa_tbl_ok F5 C5 R5 M rom 0x84ce4 0x84ce8 0xd2257753 14 10 7 (ParseFP.rfn_t b)
  ltac:(hv_dec) ltac:(hv_dec) ltac:(hv_dec) ltac:(vm_compute; reflexivity) eq_refl
  ltac:(unfold R5; hv_reg; reflexivity) HC5) as (C6 & S13 & HC6).
set (F6 := bvmap_set (14%bv : bv 5) (FP.fcvt_d_l RNE (ParseFP.rfn_t b)) F5) in S13.
destruct (hfp_tw_flt_d rsegs pa_tbl pa_tbl_ok F6 C6 R5 M rom 0x84ce8 0x84cec 0xa2e795d3 11 15 14
  (ParseFP.rfn_d b) (FP.fcvt_d_l RNE (ParseFP.rfn_t b)) ltac:(hv_dec) ltac:(hv_dec) ltac:(hv_dec)
  ltac:(vm_compute; reflexivity) eq_refl ltac:(unfold F6; hv_freg; exact HF5) ltac:(unfold F6; hv_freg; reflexivity) HC6)
  as (C7 & S14 & HC7).
set (R6 := regupd R5 11 (if FP.flt_d (ParseFP.rfn_d b) (FP.fcvt_d_l RNE (ParseFP.rfn_t b)) then Z_to_bv 64 1
  else Z_to_bv 64 0)) in S14.
assert (S15 : RiscvSemantics.step rsegs (@mkst (mkFP F6 C7) R6 (Z_to_bv 64 0x84cec) M rom) =
  MachineOk (@mkst (mkFP F6 C7) (regupd R6 12 (Z_to_bv 64 (ParseFP.rfn_r b))) (Z_to_bv 64 0x84cf0) M rom)).
{ apply (hvw_sub R6 M rom 0x84cec 0x84cf0 0x40b50633 12 10 11); [hv_dec | hv_dec | hv_dec | hv_dec | reflexivity |].
  unfold R6, R5.
  rewrite (hv_getr_upd (regupd R4 10 (ParseFP.rfn_t b)) 11 10) by (vm_compute; reflexivity).
  rewrite (hv_getr_set R4 10 10) by (vm_compute; reflexivity).
  rewrite (hv_getr_set (regupd R4 10 (ParseFP.rfn_t b)) 11 11) by (vm_compute; reflexivity).
  apply hfp_sub_r. }
assert (S16 : RiscvSemantics.step rsegs (@mkst (mkFP F6 C7) (regupd R6 12 (Z_to_bv 64 (ParseFP.rfn_r b))) (Z_to_bv 64 0x84cf0) M rom) =
  MachineOk (@mkst (mkFP F6 C7) (regupd R6 12 (Z_to_bv 64 (ParseFP.rfn_r b))) (Z_to_bv 64 PC_VV) M rom)).
{ unfold PC_VV. apply (hvw_jal0 _ M rom 0x84cf0 0x84b8c 0xe9dff06f (Z_to_bv 21 (-356)));
    [hv_dec | hv_dec | hv_dec | vm_compute; reflexivity]. }
exists F6, C7, (regupd R6 12 (Z_to_bv 64 (ParseFP.rfn_r b))), PC_VV.
split; [|split; [exact HC7 | split; [|split]]].
- eapply msteps_trans; [exact P10|].
  eapply mst_step; [reflexivity | exact S11 |]. eapply mst_step; [reflexivity | exact S12 |].
  eapply mst_step; [reflexivity | exact S13 |]. eapply mst_step; [reflexivity | exact S14 |].
  eapply mst_step; [reflexivity | exact S15 |]. eapply mst_step; [reflexivity | exact S16 |]. apply mst_refl.
- intros k H14 H15. unfold F6. rewrite FP.freg_get_other by hv_fneq. exact (HF5k k H14 H15).
- intros r H10 H11 H12. unfold R6, R5. rewrite !hv_getr_upd by hv_rneq. exact (HR4k r H10).
- cbn [andb]. split; [reflexivity|]. hv_reg. reflexivity.
Qed.

(* ======================================= the segment's cuts ======================================= *)
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis errno_low : api_env rsegs B.
Hypothesis HBerrno : as_errno B = 0x5d7cac.
Implicit Types x : pctx.

(* the model facts of VAL but its answer *)
Definition hv_cx (x : pctx) (r cc : Z) (n : nat) (ch p : Z) (cl : list Headamp.cell) (keys rf : Z) : Prop :=
hx_null x = 0 /\ hp_st_ok x r /\ r + 16 <= cc /\ cc mod 8 = 0 /\ hp_child_in x r cc /\
(Z.to_nat (r + 16 + hp_vs x r - cc) < S n)%nat /\ hp_st x cl keys rf /\
0 <= ch < Headamp.REAC_HEADAMP_MAX_CH /\ 0 <= p <= Headamp.HA_SENS.
Definition hv_rest (x : pctx) (r cc : Z) (n : nat) : list (list byte * Model.ent) :=
hp_walk_pairs (hx_bs x) r (hp_next x cc) n None.
(* what VAL, VV and RF share: VAL_at without a6 and the answer *)
Definition VX_at (x : pctx) (r cc : Z) (n : nat) (ch p : Z) (cl : list Headamp.cell) (keys rf : Z)
  (F : bvmap 5 word) (fc : bv 32) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
hp_core B x PAT_KEY cl (ha_res_bytes 0 0 0) regs mem md /\ hp_fxw F fc /\ hv_cx x r cc n ch p cl keys rf /\
pa_loop x r cl (keys + 1) regs mem /\
getr regs 23 = w64 (hx_P x + cc) /\ getr regs 24 = w64 ch /\ getr regs 13 = w64 p /\
val_mem rsegs (hx_rd x mem) (hx_spa x + 8) 8 (hv_bnd p) /\
val_mem rsegs (hx_rd x mem) (hx_spa x + 24) 8 rf /\
val_mem rsegs (hx_rd x mem) (hx_spa x + 48) 8 (shadow_addr (hx_P x + cc)).
Definition VV_ok (x : pctx) (r cc : Z) (n : nat) (ch p : Z) (cl : list Headamp.cell) (keys rf v : Z) : Prop :=
forall F fc regs mem md, VX_at x r cc n ch p cl keys rf F fc regs mem md ->
getr regs 12 = w64 v -> 0 <= v <= 255 ->
hx_res x = Headamp.ha_result (hp_fold_after (hx_cap x) (hv_cellv ch p v) (hv_rest x r cc n) cl keys rf) ->
SRr rsegs (hx_W x) (cfg_at (fx := mkFP F fc) rsegs PC_VV regs mem md) (PPOST B MT x).
Definition RF_ok (x : pctx) (r cc : Z) (n : nat) (ch p : Z) (cl : list Headamp.cell) (keys rf : Z) : Prop :=
forall F fc regs mem md, VX_at x r cc n ch p cl keys rf F fc regs mem md ->
hx_res x = Headamp.ha_result (hp_fold_after (hx_cap x) (inl Headamp.REFUSE_OUT_OF_RANGE) (hv_rest x r cc n) cl keys rf) ->
SRr rsegs (hx_W x) (cfg_at (fx := mkFP F fc) rsegs PC_RF regs mem md) (PPOST B MT x).
(* CW 0x84bb0: the value in range, a cell left (n < cap); the three stores of the cell follow *)
Definition CW_ok (x : pctx) (r cc : Z) (n : nat) (ch p : Z) (cl : list Headamp.cell) (keys rf v : Z) : Prop :=
forall F fc regs mem md, VX_at x r cc n ch p cl keys rf F fc regs mem md ->
getr regs 12 = w64 v -> 0 <= v <= 255 -> Z.of_nat (length cl) < hx_cap x ->
hx_res x = Headamp.ha_result (Headamp.ha_fold Headamp.parse_cell (hx_cap x) (hv_rest x r cc n) (cl ++ [(ch, p, v)])
  (keys + 1) rf) ->
SRr rsegs (hx_W x) (cfg_at (fx := mkFP F fc) rsegs PC_CW regs mem md) (PPOST B MT x).

Lemma hv_VAL : forall x r cc n ch p cl keys rf F fc regs mem md,
VAL_at B x r cc n ch p cl keys rf F fc regs mem md ->
VX_at x r cc n ch p cl keys rf F fc regs mem md /\ getr regs 16 = w64 (shadow_addr (hx_P x + cc)) /\
hx_res x = Headamp.ha_result (hp_fold_after (hx_cap x) (hp_vcell ch p (Spa.child_at (hx_bs x) cc))
  (hv_rest x r cc n) cl keys rf).
Proof.
intros x r cc n ch p cl keys rf F fc regs mem md
  (HC & Hfx & (Hn & Hso & Hc16 & Hc8 & Hin & Hfu & Hst & Hch & Hp & Hres) & Hloop & H23 & H24 & H13 & H16 & Hb & Hr & Hs).
split; [|split; [exact H16 | exact Hres]].
split; [exact HC|]. split; [exact Hfx|].
split; [repeat (split; [assumption|]); exact Hp|].
split; [exact Hloop|]. split; [exact H23|]. split; [exact H24|]. split; [exact H13|].
split; [exact Hb|]. split; [exact Hr | exact Hs].
Qed.

(* ---------------------------------- the model steps of the ways out ---------------------------------- *)
Definition hv_rf' (rf : Z) : Z := if rf =? Headamp.REFUSE_NONE then Headamp.REFUSE_OUT_OF_RANGE else rf.

Lemma hv_m_refuse : forall x r cc n ch p cl keys rf, hv_cx x r cc n ch p cl keys rf ->
hx_res x = Headamp.ha_result (hp_fold_after (hx_cap x) (inl Headamp.REFUSE_OUT_OF_RANGE) (hv_rest x r cc n) cl keys rf) ->
hp_m_adv x r cc n None cl (keys + 1) (hv_rf' rf).
Proof.
intros x r cc n ch p cl keys rf (Hn & Hso & Hc16 & Hc8 & Hin & Hfu & (Hcl & Hk & Hrf) & _) Hres.
unfold hp_m_adv. do 6 (split; [assumption|]). split; [intros ck X; discriminate X|].
split; [unfold hp_st, hv_rf', Headamp.REFUSE_NONE, Headamp.REFUSE_OUT_OF_RANGE; destruct (rf =? 0); lia|].
exact Hres.
Qed.

Lemma hv_m_cell : forall x r cc n ch p cl keys rf v, hv_cx x r cc n ch p cl keys rf ->
Z.of_nat (length cl) < hx_cap x ->
hx_res x = Headamp.ha_result (Headamp.ha_fold Headamp.parse_cell (hx_cap x) (hv_rest x r cc n) (cl ++ [(ch, p, v)])
  (keys + 1) rf) ->
hp_m_adv x r cc n None (cl ++ [(ch, p, v)]) (keys + 1) rf.
Proof.
intros x r cc n ch p cl keys rf v (Hn & Hso & Hc16 & Hc8 & Hin & Hfu & (Hcl & Hk & Hrf) & _) Hlt Hres.
unfold hp_m_adv. do 6 (split; [assumption|]). split; [intros ck X; discriminate X|].
split; [unfold hp_st; rewrite length_app; cbn [length]; lia|]. exact Hres.
Qed.

Lemma hv_m_exit : forall x r cc n ch p cl keys rf, hv_cx x r cc n ch p cl keys rf ->
hx_res x = Headamp.ha_result (cl, keys + 1, rf) -> hp_m_exit x cl (keys + 1) rf.
Proof.
intros x r cc n ch p cl keys rf (Hn & _ & _ & _ & _ & _ & (Hcl & Hk & Hrf) & _) Hres.
split; [exact Hn|]. split; [unfold hp_st; lia | exact Hres].
Qed.

(* ---------------------------------- the cuts the segment reaches ---------------------------------- *)
Abbreviation hv_KW x mem mem2 Wr :=
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> hx_rd x mem2 (Z_to_bv 64 a) = hx_rd x mem (Z_to_bv 64 a)) (only parsing).
Abbreviation hv_J x mem2 md2 := (ajournal rsegs B (hx_STK x) (hx_sp0 x) (hx_FP x) (hx_ly x) (hx_S x) (hx_W0 x)
  (hx_mem0 x) (hx_md0 x) (hx_own x) (hx_lyc x) (hx_Sc x) (hx_W x) (unpoison (hU (hx_fr x) PAT_KEY) mem2) md2 (hx_k x))
  (only parsing).

(* the facts of a VX state that a run keeping every byte outside [spa + 56, spa + 60) keeps *)
Lemma hv_vx_keep : forall x r cc n ch p cl keys rf F fc regs mem md regs2 mem2 md2, call_ok B x ->
VX_at x r cc n ch p cl keys rf F fc regs mem md ->
hv_KW x mem mem2 (fun a => hx_spa x + 56 <= a < hx_spa x + 60) -> hv_J x mem2 md2 -> same_io md md2 ->
hk_cregs x regs2 ->
hp_core B x PAT_KEY cl (ha_res_bytes 0 0 0) regs2 mem2 md2 /\
val_mem rsegs (hx_rd x mem2) (hx_spa x + 8) 8 (hv_bnd p) /\
val_mem rsegs (hx_rd x mem2) (hx_spa x + 16) 8 ((hx_P x + r + 8) mod 8 + 3) /\
val_mem rsegs (hx_rd x mem2) (hx_spa x + 24) 8 rf /\
val_mem rsegs (hx_rd x mem2) (hx_spa x + 32) 8 (hx_P x + r + 16) /\
val_mem rsegs (hx_rd x mem2) (hx_spa x + 40) 8 (keys + 1) /\
val_mem rsegs (hx_rd x mem2) (hx_spa x + 48) 8 (shadow_addr (hx_P x + cc)).
Proof.
intros x r cc n ch p cl keys rf F fc regs mem md regs2 mem2 md2 Hc
  (HC & _ & (_ & _ & _ & _ & _ & _ & (Hcl & _) & _) & (_ & _ & _ & L16 & L32 & L40) & _ & _ & _ & Hb & Hr & Hs)
  KW HJ2 Hio HCR.
pose proof (hk_frame_win B x Hc) as (FW1 & FW2 & _ & _ & FW5).
pose proof (hk_stack B x Hc) as (_ & _ & _ & S4 & S5 & S6 & _).
assert (KV : forall o v, 0 <= o -> o + 8 <= 56 -> val_mem rsegs (hx_rd x mem) (hx_spa x + o) 8 v ->
  val_mem rsegs (hx_rd x mem2) (hx_spa x + o) 8 v).
{ intros o v Ho Ho8 HV. apply (hv_vm_kept _ _ _ _ _ (fun a => hx_spa x + 56 <= a < hx_spa x + 60) KW); [lia | | | exact HV].
  - cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. unfold hx_sp in *. lia.
  - intros b Hb' Hw. cbn in Hb'. lia. }
split; [exact (hk_core_frame B pa_segs_low x PAT_KEY cl (ha_res_bytes 0 0 0) regs mem md regs2 mem2 md2 56 60
  errno_low Hc HC ltac:(lia) eq_refl ltac:(lia) ltac:(lia) KW HJ2 Hio HCR)|].
split; [exact (KV 8 _ ltac:(lia) ltac:(lia) Hb)|]. split; [exact (KV 16 _ ltac:(lia) ltac:(lia) L16)|].
split; [exact (KV 24 _ ltac:(lia) ltac:(lia) Hr)|]. split; [exact (KV 32 _ ltac:(lia) ltac:(lia) L32)|].
split; [exact (KV 40 _ ltac:(lia) ltac:(lia) L40)|]. exact (KV 48 _ ltac:(lia) ltac:(lia) Hs).
Qed.

(* a VX state at a later pc (the Bool and Int values, the Float steps' ends) *)
Lemma hv_to_VX : forall x r cc n ch p cl keys rf F fc regs mem md F2 fc2 regs2 mem2 md2, call_ok B x ->
VX_at x r cc n ch p cl keys rf F fc regs mem md -> hp_fxw F2 fc2 ->
hv_KW x mem mem2 (fun a => hx_spa x + 56 <= a < hx_spa x + 60) -> hv_J x mem2 md2 -> same_io md md2 ->
hk_cregs x regs2 ->
getr regs2 20 = getr regs 20 -> getr regs2 21 = getr regs 21 -> getr regs2 22 = getr regs 22 ->
getr regs2 23 = getr regs 23 -> getr regs2 24 = getr regs 24 -> getr regs2 13 = getr regs 13 ->
VX_at x r cc n ch p cl keys rf F2 fc2 regs2 mem2 md2.
Proof.
intros x r cc n ch p cl keys rf F fc regs mem md F2 fc2 regs2 mem2 md2 Hc HV Hfx2 KW HJ2 Hio HCR R20 R21 R22 R23 R24 R13.
destruct (hv_vx_keep x r cc n ch p cl keys rf F fc regs mem md regs2 mem2 md2 Hc HV KW HJ2 Hio HCR)
  as (HC2 & V8 & V16 & V24 & V32 & V40 & V48).
destruct HV as (_ & _ & Hcx & (L20 & L21 & L22 & _) & H23 & H24 & H13 & _).
split; [exact HC2|]. split; [exact Hfx2|]. split; [exact Hcx|].
split; [unfold pa_loop; rewrite R20, R21, R22; repeat (split; [assumption|]); exact V40|].
rewrite R23, R24, R13. repeat (split; [assumption|]). exact V48.
Qed.

(* ADV with no new cell: a refusal *)
Lemma hv_to_ADV : forall x r cc n ch p cl keys rf rf' F fc regs mem md regs2 mem2 md2, call_ok B x ->
VX_at x r cc n ch p cl keys rf F fc regs mem md ->
hv_KW x mem mem2 (fun a => hx_spa x + 56 <= a < hx_spa x + 60) -> hv_J x mem2 md2 -> same_io md md2 ->
hk_cregs x regs2 ->
getr regs2 20 = getr regs 20 -> getr regs2 21 = getr regs 21 -> getr regs2 22 = getr regs 22 ->
getr regs2 23 = getr regs 23 -> getr regs2 14 = w64 (hx_P x + r + 16) -> getr regs2 15 = w64 8 ->
getr regs2 24 = w64 0 -> getr regs2 25 = w64 rf' -> getr regs2 16 = w64 (shadow_addr (hx_P x + cc)) ->
hp_m_adv x r cc n None cl (keys + 1) rf' ->
ADV_at B x r cc n None cl (keys + 1) rf' F fc regs2 mem2 md2.
Proof.
intros x r cc n ch p cl keys rf rf' F fc regs mem md regs2 mem2 md2 Hc HV KW HJ2 Hio HCR
  R20 R21 R22 R23 R14 R15 R24 R25 R16 Hm.
destruct (hv_vx_keep x r cc n ch p cl keys rf F fc regs mem md regs2 mem2 md2 Hc HV KW HJ2 Hio HCR)
  as (HC2 & V8 & V16 & V24 & V32 & V40 & V48).
destruct HV as (_ & Hfx & _ & (L20 & L21 & L22 & _) & H23 & _).
split; [exact HC2|]. split; [exact Hfx|]. split; [exact Hm|].
split; [unfold pa_loop; rewrite R20, R21, R22; repeat (split; [assumption|]); exact V40|].
split; [split; assumption|]. rewrite R23. cbn [hp_keyv]. repeat (split; [assumption|]). exact R16.
Qed.

(* EXIT: n >= cap *)
Lemma hv_to_EXIT : forall x r cc n ch p cl keys rf F fc regs mem md regs2 mem2 md2, call_ok B x ->
VX_at x r cc n ch p cl keys rf F fc regs mem md ->
hv_KW x mem mem2 (fun a => hx_spa x + 56 <= a < hx_spa x + 60) -> hv_J x mem2 md2 -> same_io md md2 ->
hk_cregs x regs2 -> getr regs2 20 = getr regs 20 -> getr regs2 25 = w64 rf ->
hp_m_exit x cl (keys + 1) rf ->
EXIT_at B x cl (keys + 1) rf F fc regs2 mem2 md2.
Proof.
intros x r cc n ch p cl keys rf F fc regs mem md regs2 mem2 md2 Hc HV KW HJ2 Hio HCR R20 R25 Hm.
destruct (hv_vx_keep x r cc n ch p cl keys rf F fc regs mem md regs2 mem2 md2 Hc HV KW HJ2 Hio HCR)
  as (HC2 & V8 & V16 & V24 & V32 & V40 & V48).
destruct HV as (_ & (Hfx & _) & _ & (L20 & _) & _).
split; [exact HC2|]. split; [exact Hfx|]. split; [exact Hm|]. rewrite R20.
split; [exact L20|]. split; [exact R25 | exact V40].
Qed.

(* the out cells after the new cell's three bytes *)
Lemma hv_cells_len : forall cl, length (ha_cells_bytes cl) = (3 * length cl)%nat.
Proof.
induction cl as [|[[a b] c] cl IH]; [reflexivity|].
unfold ha_cells_bytes in *. cbn [flat_map ha_cell_bytes app length]. rewrite IH. lia.
Qed.

Lemma hv_cells_snoc : forall (m : word -> option byte) O cl ch p v,
garr8 rsegs m O (hd_zbytes (ha_cells_bytes cl)) ->
val_mem rsegs m (O + 3 * Z.of_nat (length cl)) 1 ch -> val_mem rsegs m (O + 3 * Z.of_nat (length cl) + 1) 1 p ->
val_mem rsegs m (O + 3 * Z.of_nat (length cl) + 2) 1 v ->
0 <= ch < 256 -> 0 <= p < 256 -> 0 <= v < 256 ->
garr8 rsegs m O (hd_zbytes (ha_cells_bytes (cl ++ [(ch, p, v)]))).
Proof.
intros m O cl ch p v HG H0 H1 H2 R0 R1 R2.
unfold ha_cells_bytes. rewrite flat_map_app. unfold hd_zbytes. rewrite map_app.
apply garr8_app. split; [exact HG|].
rewrite length_map. fold (ha_cells_bytes cl). rewrite hv_cells_len.
intros j Hj. cbn [flat_map ha_cell_bytes app map length] in Hj |- *.
rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
rewrite (Z.mod_small ch), (Z.mod_small p), (Z.mod_small v) by lia.
destruct j as [|[|[|j]]]; cbn [nth]; [ | | | lia].
- split; [|lia]. replace (O + Z.of_nat (3 * length cl) + Z.of_nat 0) with (O + 3 * Z.of_nat (length cl)) by lia. exact H0.
- split; [|lia]. replace (O + Z.of_nat (3 * length cl) + Z.of_nat 1) with (O + 3 * Z.of_nat (length cl) + 1) by lia. exact H1.
- split; [|lia]. replace (O + Z.of_nat (3 * length cl) + Z.of_nat 2) with (O + 3 * Z.of_nat (length cl) + 2) by lia. exact H2.
Qed.

(* ADV with the new cell (ch, p, v) at out[3 n, 3 n + 3) *)
Lemma hv_to_ADVc : forall x r cc n ch p cl keys rf v F fc regs mem md regs2 mem2 md2, call_ok B x ->
VX_at x r cc n ch p cl keys rf F fc regs mem md -> 0 <= v <= 255 -> Z.of_nat (length cl) < hx_cap x ->
hv_KW x mem mem2 (fun a => hx_O x + 3 * Z.of_nat (length cl) <= a < hx_O x + 3 * Z.of_nat (length cl) + 3) ->
val_mem rsegs (hx_rd x mem2) (hx_O x + 3 * Z.of_nat (length cl)) 1 ch ->
val_mem rsegs (hx_rd x mem2) (hx_O x + 3 * Z.of_nat (length cl) + 1) 1 p ->
val_mem rsegs (hx_rd x mem2) (hx_O x + 3 * Z.of_nat (length cl) + 2) 1 v ->
hv_J x mem2 md2 -> same_io md md2 -> hk_cregs x regs2 ->
getr regs2 20 = w64 (Z.of_nat (length cl) + 1) -> getr regs2 21 = getr regs 21 -> getr regs2 22 = getr regs 22 ->
getr regs2 23 = getr regs 23 -> getr regs2 14 = w64 (hx_P x + r + 16) -> getr regs2 15 = w64 8 ->
getr regs2 24 = w64 0 -> getr regs2 25 = w64 rf -> getr regs2 16 = w64 (shadow_addr (hx_P x + cc)) ->
hp_m_adv x r cc n None (cl ++ [(ch, p, v)]) (keys + 1) rf ->
ADV_at B x r cc n None (cl ++ [(ch, p, v)]) (keys + 1) rf F fc regs2 mem2 md2.
Proof.
intros x r cc n ch p cl keys rf v F fc regs mem md regs2 mem2 md2 Hc HV Hv Hlt KW C0 C1 C2 HJ2 Hio HCR
  R20 R21 R22 R23 R14 R15 R24 R25 R16 Hm.
pose proof HV as (HC & Hfx & (_ & _ & _ & _ & _ & _ & (Hcl & _) & Hch & Hp) & (L20 & L21 & L22 & L16 & L32 & L40) & H23 & _).
pose proof (hk_frame_win B x Hc) as (FW1 & FW2 & _ & _ & FW5).
pose proof (hk_stack B x Hc) as (_ & _ & _ & S4 & S5 & S6 & _).
pose proof (hk_out B x Hc) as (Hcap & _ & _ & _ & _ & HO4 & HOc & _ & _ & HOoff & _).
pose proof asan_consts as ((AC1 & AC2) & _).
unfold Headamp.REAC_HEADAMP_MAX_CH, Headamp.HA_SENS in Hch, Hp.
set (o := hx_O x + 3 * Z.of_nat (length cl)) in *.
assert (Ho : hx_O x <= o /\ o + 3 <= hx_O x + 3 * (hx_cap x + 1)) by (subst o; lia).
assert (KV : forall a, 0 <= a < 2 ^ 64 -> ~ (o <= a < o + 3) -> hx_view x mem2 a = hx_view x mem a).
{ intros a Ha Hn. unfold hx_view, aview, mbyte. change (mrestrict (w_H (hx_W x)) mem2) with (hx_rd x mem2).
  change (mrestrict (w_H (hx_W x)) mem) with (hx_rd x mem). rewrite (KW a Ha Hn). reflexivity. }
(* a byte of out's cell is none of the call's other places *)
assert (AP : forall a, o <= a < o + 3 -> ~ (hx_sp x - T_parse_STK <= a < hx_sp x) /\ ~ hp_hole x a /\
  ~ in_img rsegs a /\ (hx_R x <> 0 -> ~ (hx_R x <= a < hx_R x + 12))).
{ intros a Ha. pose proof (hgk_out_apart B x (a - hx_O x) Hc ltac:(lia)) as (A1 & A2 & A3 & A4 & _).
  replace (hx_O x + (a - hx_O x)) with a in * by lia. exact (conj A1 (conj A2 (conj A3 A4))). }
assert (KVM : forall b m', hx_spa x <= b -> b + 8 <= hx_spa x + 0x80 ->
  val_mem rsegs (hx_rd x mem) b 8 m' -> val_mem rsegs (hx_rd x mem2) b 8 m').
{ intros b m' Hb1 Hb2 HVm. apply (hv_vm_kept _ _ _ _ _ (fun a => o <= a < o + 3) KW); [lia | cbn; unfold hx_sp in *; lia | | exact HVm].
  intros c Hc1 Hw. destruct (AP c Hw) as (A1 & _). apply A1. cbn in Hc1. unfold hx_sp in *. lia. }
pose proof HC as ((_ & _ & HPAT) & _ & _ & _ & HO & HR & HE & _).
assert (HC2 : hp_core B x PAT_KEY (cl ++ [(ch, p, v)]) (ha_res_bytes 0 0 0) regs2 mem2 md2).
{ apply (hk_core_step B pa_segs_low x PAT_KEY PAT_KEY cl (cl ++ [(ch, p, v)]) (ha_res_bytes 0 0 0) (ha_res_bytes 0 0 0)
    regs mem md regs2 mem2 md2 (fun a => o <= a < o + 3) errno_low Hc HC).
  - rewrite length_app. lia.
  - rewrite length_app. cbn [length]. lia.
  - exact KV.
  - intros a Ha. right. right. unfold hp_pw. left. rewrite length_app. cbn [length]. subst o. lia.
  - exact HJ2.
  - reflexivity.
  - unfold PAT_KEY. repeat constructor; lia.
  - apply (hk_hpat_kept x mem mem2 PAT_KEY); [|exact HPAT].
    intros i Hi. cbn [length PAT_KEY Z.of_nat] in Hi.
    pose proof (hk_hole_band B x (hx_shf x + i) Hc ltac:(unfold hp_hole; lia)) as [Hb1 Hb2].
    apply KV; [unfold kHighShadowEnd, SHADOW_OFF in *; lia|].
    intros Hw. destruct (AP _ Hw) as (_ & A2 & _). apply A2. unfold hp_hole. lia.
  - exact Hio.
  - apply hv_cells_snoc; [ | exact C0 | exact C1 | exact C2 | lia | lia | lia ].
    apply (hk_garr8_kept x mem mem2 (hx_O x) _); [|exact HO].
    intros a Ha. unfold hd_zbytes in Ha. rewrite length_map, hv_cells_len in Ha.
    apply KV; [lia|]. subst o. lia.
  - intros HR0. apply (hk_garr8_kept x mem mem2 (hx_R x) _); [|exact (HR HR0)].
    intros a Ha. cbn in Ha.
    pose proof (hgk_res_apart B pa_segs_low x (a - hx_R x) Hc HR0 ltac:(lia)) as (_ & _ & _ & _ & R5).
    replace (hx_R x + (a - hx_R x)) with a in R5 by lia.
    apply KV; [lia|]. intros Hw. destruct (AP a Hw) as (_ & _ & _ & A4). exact (A4 HR0 ltac:(lia)).
  - destruct HE as (ev & HEv). exists ev.
    apply (hk_rd32_kept (hx_view x mem) (hx_view x mem2) (as_errno B) ev); [|exact HEv].
    intros k Hk. pose proof (hgk_errno_apart B errno_low x k Hc Hk) as (_ & _ & E3 & E4).
    apply KV; [unfold kLowMemEnd in E4; lia|]. intros Hw. destruct (AP _ Hw) as (_ & _ & A3 & _). exact (A3 E3).
  - exact HCR. }
split; [exact HC2|]. split; [exact Hfx|]. split; [exact Hm|].
split.
{ unfold pa_loop. rewrite length_app. cbn [length].
  replace (Z.of_nat (length cl + 1)) with (Z.of_nat (length cl) + 1) by lia. rewrite R21, R22.
  split; [exact R20|]. split; [exact L21|]. split; [exact L22|].
  split; [apply KVM; [lia | lia | exact L16]|]. split; [apply KVM; [lia | lia | exact L32]|].
  apply KVM; [lia | lia | exact L40]. }
split; [split; assumption|]. rewrite R23. cbn [hp_keyv]. repeat (split; [assumption|]). exact R16.
Qed.

(* ---------------------------------- the env ---------------------------------- *)
Definition hv_L (x : pctx) (r cc p : Z) (cl : list Headamp.cell) (rf v : Z) : list word :=
map (Z_to_bv 64) [Spa.u32_at (hx_bs x) cc; Spa.u32_at (hx_bs x) (cc + 4); Spa.u32_at (hx_bs x) (cc + 8);
  hv_bnd p; rf; hx_P x + r + 16; shadow_addr (hx_P x + cc); hx_O x + 3 * Z.of_nat (length cl); v].
Definition hv_E (x : pctx) (regs : bvmap 5 word) (r cc p : Z) (cl : list Headamp.cell) (rf v : Z) : env :=
hk_env x regs (hv_L x r cc p cl rf v).

Lemma hv_Eseg : forall x regs r cc p cl rf v, let E := hv_E x regs r cc p cl rf v in
ew E 47 = Z_to_bv 64 (Spa.u32_at (hx_bs x) cc) /\ ew E 48 = Z_to_bv 64 (Spa.u32_at (hx_bs x) (cc + 4)) /\
ew E 49 = Z_to_bv 64 (Spa.u32_at (hx_bs x) (cc + 8)) /\ ew E 50 = Z_to_bv 64 (hv_bnd p) /\
ew E 51 = Z_to_bv 64 rf /\ ew E 52 = Z_to_bv 64 (hx_P x + r + 16) /\
ew E 53 = Z_to_bv 64 (shadow_addr (hx_P x + cc)) /\ ew E 54 = Z_to_bv 64 (hx_O x + 3 * Z.of_nat (length cl)) /\
ew E 55 = Z_to_bv 64 v.
Proof.
intros x regs r cc p cl rf v E. subst E. unfold hv_E.
repeat split; lazymatch goal with |- ew _ ?k = _ =>
  let j := eval vm_compute in (k - 47)%nat in change k with (47 + j)%nat; rewrite hk_env_seg; reflexivity end.
Qed.

Lemma hv_Ereg : forall x regs r cc p cl rf v (n : nat) (rr : bv 5) z, Z.of_nat n = bv_unsigned rr -> getr regs rr = w64 z ->
ew (hv_E x regs r cc p cl rf v) n = Z_to_bv 64 z.
Proof. intros x regs r cc p cl rf v n rr z Hn H. unfold hv_E. rewrite (hk_env_reg x regs _ n rr Hn). exact H. Qed.

Lemma hv_ub : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> bv_unsigned (ew E n) = v.
Proof. intros E n v H Hv. rewrite H. apply unsigned_lit_small. exact Hv. Qed.

(* the child at cc lies inside the Struct body, the Struct inside the pod *)
Lemma hv_child : forall x r cc, hp_st_ok x r -> hp_child_in x r cc -> r + 16 <= cc ->
cc + 8 + Spa.u32_at (hx_bs x) cc <= r + 16 + hp_vs x r /\ r + 16 + hp_vs x r <= hx_len x.
Proof.
intros x r cc (Hr16 & Hr8 & Hvs & Hle) Hin Hc.
destruct (hgw_inside_bounds (hx_bs x) (r + 16) (hp_vs x r) cc Hin) as (_ & _ & H). lia.
Qed.

(* the shadow address in the engine's form of `srli x,3; add x,x,s11` (lib/A/HPgParseGWalk.v hgw_U_shadow) *)
Lemma hv_U_sh : forall E (m : nat) a, ew E m = Z_to_bv 64 a -> ew E 27 = Z_to_bv 64 SHADOW_OFF -> 0 <= a < 2 ^ 47 ->
sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff m 0) (SLit 3)) (SOff 27 0)) = w64 (shadow_addr a).
Proof.
intros E m a Hm H27 Ha. rewrite denot_lit_U. unfold w64. f_equal.
apply hgw_U_shadow; [apply (U_atom E m a Hm); lia | apply (U_atom E 27 SHADOW_OFF H27); unfold SHADOW_OFF; lia | exact Ha].
Qed.

(* ---------------------------------- the entry at VAL ---------------------------------- *)
Lemma hv_entry_val : forall x r cc n ch p cl keys rf F fc regs mem md big, call_ok B x ->
VAL_at B x r cc n ch p cl keys rf F fc regs mem md -> (4 <=? Spa.u32_at (hx_bs x) cc) = big ->
st_ok (fx := mkFP F fc) rsegs (hv_E x regs r cc p cl rf 0) (hv_ss_val big)
  (restrict (w_H (hx_W x)) (@mkst (mkFP F fc) regs (Z_to_bv 64 PC_VAL) mem (seg_rom rsegs))) /\
sh_ok rsegs hk_Bx (hv_SH_val big) (hv_E x regs r cc p cl rf 0) (mrestrict (w_H (hx_W x)) mem).
Proof.
intros x r cc n ch p cl keys rf F fc regs mem md big Hc HV Hbig.
destruct (hv_VAL x r cc n ch p cl keys rf F fc regs mem md HV)
  as ((HC & Hfx & (Hn & Hso & Hc16 & Hc8 & Hin & Hfu & Hst & Hch & Hp) & Hloop & H23 & H24 & H13 & Hb & Hr & Hs) & H16 & Hres).
pose proof (hk_core_cregs B x _ _ _ _ _ _ HC) as Hcr.
pose proof Hcr as (R2 & R8 & R3 & R4 & R9 & R18 & R19 & R26 & R27).
pose proof (hk_pod B x Hc Hn) as (HP0 & HP16 & (Hl8 & Hl16k) & _ & _ & HP63 & _ & _ & _ & _ & _ & _ & _ & HAM & _).
pose proof (hk_pod_side B x Hc Hn) as Hside.
pose proof (hk_frame_win B x Hc) as (FW1 & FW2 & FW3 & FW4 & FW5).
pose proof (hk_stack B x Hc) as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & S13).
pose proof asan_consts as ((AC1 & AC2) & _).
destruct Hst as (Hcl & Hk0 & Hrf).
pose proof (hk_pod_at_cut B pa_segs_low x PAT_KEY cl (ha_res_bytes 0 0 0) regs mem md errno_low Hc Hn HC ltac:(lia))
  as (HG & HRA & _).
pose proof (hv_child x r cc Hso Hin Hc16) as [Hcc Hvs]. pose proof Hso as (Hr16 & Hr8 & Hvs20 & _).
pose proof (hgw_u32_range (hx_bs x) cc) as RS. pose proof (hgw_u32_range (hx_bs x) (cc + 4)) as RT.
pose proof (hgw_u32_range (hx_bs x) (cc + 8)) as RB.
assert (Hb4 : big = true -> 4 <= Spa.u32_at (hx_bs x) cc) by (intros ->; apply Z.leb_le; exact Hbig).
assert (Hb3 : big = false -> Spa.u32_at (hx_bs x) cc < 4) by (intros ->; apply Z.leb_gt; exact Hbig).
assert (Hhi : cc + hv_hi big <= hx_len x) by (destruct big; unfold hv_hi; [specialize (Hb4 eq_refl) | ]; lia).
assert (HAM' : hx_P x + hx_len x <= 2 ^ 47) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HAM; lia).
set (E := hv_E x regs r cc p cl rf 0).
pose proof (hv_Eseg x regs r cc p cl rf 0) as (E47 & E48 & E49 & E50 & E51 & E52 & E53 & E54 & E55).
fold E in E47, E48, E49, E50, E51, E52, E53, E54, E55.
assert (E2 : ew E 2 = Z_to_bv 64 (hx_spa x)) by exact (hv_Ereg x regs r cc p cl rf 0 2 2%bv _ eq_refl R2).
assert (E23 : ew E 23 = Z_to_bv 64 (hx_P x + cc)) by exact (hv_Ereg x regs r cc p cl rf 0 23 23%bv _ eq_refl H23).
assert (E27 : ew E 27 = Z_to_bv 64 SHADOW_OFF) by exact (hv_Ereg x regs r cc p cl rf 0 27 27%bv _ eq_refl R27).
assert (E20 : ew E 20 = Z_to_bv 64 (Z.of_nat (length cl))) by exact (hv_Ereg x regs r cc p cl rf 0 20 20%bv _ eq_refl (proj1 Hloop)).
assert (E18 : ew E 18 = Z_to_bv 64 (hx_cap x)) by exact (hv_Ereg x regs r cc p cl rf 0 18 18%bv _ eq_refl R18).
assert (E24 : ew E 24 = Z_to_bv 64 ch) by exact (hv_Ereg x regs r cc p cl rf 0 24 24%bv _ eq_refl H24).
assert (E13 : ew E 13 = Z_to_bv 64 p) by exact (hv_Ereg x regs r cc p cl rf 0 13 13%bv _ eq_refl H13).
pose proof (hk_out B x Hc) as (Hcap & _).
assert (Hbnd : 2 <= hv_bnd p <= 56) by (unfold hv_bnd; destruct (p =? Headamp.HA_SENS); lia).
split.
- rewrite restrict_mkst_fx. unfold hv_ss_val. apply (entry_st_ok_full (fx := mkFP F fc) rsegs).
  + apply regs_ok_pin; [unfold hv_E, hk_env; apply regs_ok_Ereg | intros X; apply (f_equal bv_unsigned) in X; discriminate X |].
    rewrite H16. symmetry. apply hv_U_sh; [exact E23 | exact E27 | lia].
  + destruct big; vm_compute; reflexivity.
  + apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    * apply hv_tr_ok. apply (hk_temps_ok B x PAT_KEY cl (ha_res_bytes 0 0 0) regs mem md _ hv_fcs Hc HC).
      unfold hv_fcs. repeat apply Forall_cons; try apply Forall_nil.
      -- apply (chunk_ok_val rsegs _ _ _ 8 8 (SOff 50 0) (hv_bnd p)); [rewrite hk_sv_SOff0; exact E50 | zside | zside | exact Hb].
      -- apply (chunk_ok_val rsegs _ _ _ 24 8 (SOff 51 0) rf); [rewrite hk_sv_SOff0; exact E51 | zside | zside | exact Hr].
      -- apply (chunk_ok_val rsegs _ _ _ 32 8 (SOff 52 0) (hx_P x + r + 16)); [rewrite hk_sv_SOff0; exact E52 | zside | zside |].
         exact (proj1 (proj2 (proj2 (proj2 (proj2 Hloop))))).
      -- apply (chunk_ok_val rsegs _ _ _ 48 8 (SOff 53 0) (shadow_addr (hx_P x + cc)));
         [rewrite hk_sv_SOff0; exact E53 | unfold shadow_addr, SHADOW_OFF; zside | zside | exact Hs].
    * unfold region_ok, hv_pod. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      change (Ereg regs (w64 SHADOW_OFF :: hk_saved_vals x ++ hk_fs0 :: hv_L x r cc p cl rf 0)) with E.
      rewrite (hv_ub E 23 _ E23) by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      assert (C0 : YP09.chunk_ok rsegs E (hx_rd x mem) (hx_P x + cc) (YP09.mkChunk 0 (CVal 4 (SOff 47 0)))).
      { apply (chunk_ok_val rsegs _ _ _ 0 4 (SOff 47 0) (Spa.u32_at (hx_bs x) cc)); [rewrite hk_sv_SOff0; exact E47 | zside | zside |].
        rewrite Z.add_0_r. apply hgw_pod_u32; [exact HG | lia | unfold hx_len in *; lia]. }
      assert (C4 : YP09.chunk_ok rsegs E (hx_rd x mem) (hx_P x + cc) (YP09.mkChunk 4 (CVal 4 (SOff 48 0)))).
      { apply (chunk_ok_val rsegs _ _ _ 4 4 (SOff 48 0) (Spa.u32_at (hx_bs x) (cc + 4))); [rewrite hk_sv_SOff0; exact E48 | zside | zside |].
        rewrite <- Z.add_assoc. apply hgw_pod_u32; [exact HG | lia | unfold hx_len in *; lia]. }
      destruct big; cbn [app]; repeat apply Forall_cons; try apply Forall_nil; try exact C0; try exact C4.
      apply (chunk_ok_val rsegs _ _ _ 8 4 (SOff 49 0) (Spa.u32_at (hx_bs x) (cc + 8))); [rewrite hk_sv_SOff0; exact E49 | zside | zside |].
      rewrite <- Z.add_assoc. apply hgw_pod_u32; [exact HG | lia | unfold hx_len, hv_hi in *; lia].
  + cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, hv_tr, hv_pod.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
    change (Ereg regs (w64 SHADOW_OFF :: hk_saved_vals x ++ hk_fs0 :: hv_L x r cc p cl rf 0)) with E.
    rewrite (hv_ub E 2 _ E2), (hv_ub E 23 _ E23) by lia.
    split; [split; [|exact I] | split; [exact I | exact I]]. unfold hx_len in *. destruct Hside; lia.
  + split; [|split; [exact I | exact I]].
    apply (hk_atoms_ok B x regs _ _ Hc Hcr).
    unfold hv_atoms_val. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    change (hk_env x regs (hv_L x r cc p cl rf 0)) with E.
    pose proof (hgw_u32_range (hx_bs x) (r + 8)) as RV.
    unfold Headamp.REAC_HEADAMP_MAX_CH, Headamp.HA_SENS, hp_vs, hx_len in *.
    rewrite E23, E20, E18, E24, E13, E47, E48, E49, E50, E51, E52, E53.
    rewrite !unsigned_lit_small by (unfold shadow_addr, SHADOW_OFF in *; lia).
    change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    destruct big; cbn [af_lo af_hi af_al2]; rewrite ?Z.pow_0_r, ?Z.mod_1_r; unfold hv_hi;
    [specialize (Hb4 eq_refl) | specialize (Hb3 eq_refl)];
    unfold shadow_addr, SHADOW_OFF in *; repeat split; lia.
- unfold sh_ok, hv_SH_val. apply Forall_cons; [|apply Forall_nil].
  apply (hk_shent_pod B x _ _ E 23 cc 0 (hv_hi big) Hc Hn E27 E23 HRA); unfold hx_len in *; [lia | lia | destruct big; unfold hv_hi; lia | lia].
Qed.

(* ---------------------------------- the entries at VV, CW and RF ---------------------------------- *)
(* the frame cells of a VX state, and the facts every VX entry shares *)
Lemma hv_vx_facts : forall x r cc n ch p cl keys rf F fc regs mem md v, call_ok B x ->
VX_at x r cc n ch p cl keys rf F fc regs mem md ->
let E := hv_E x regs r cc p cl rf v in
Forall (region_ok rsegs E (hx_rd x mem)) [hv_tr false] /\ hk_cregs x regs /\
0 <= hx_spa x /\ hx_spa x + 0x80 <= hx_sp x - 0x80 /\ hx_sp x - T_parse_STK <= hx_spa x /\ hx_sp x <= 2 ^ 47 /\
Z.of_nat (length cl) <= hx_cap x <= 9 /\ 0 <= ch < 48 /\ 0 <= p <= 2 /\ 2 <= hv_bnd p <= 56 /\ 0 <= rf <= 5 /\
4096 <= hx_O x /\ hx_O x + 3 * (hx_cap x + 1) <= 0x7fffff800000 /\
0 <= hx_P x /\ 0 <= hx_P x + r + 16 <= 2 ^ 47 /\ 0 <= hx_P x + cc <= 2 ^ 47 - 8 /\
ew E 2 = Z_to_bv 64 (hx_spa x) /\ ew E 27 = Z_to_bv 64 SHADOW_OFF /\
ew E 20 = Z_to_bv 64 (Z.of_nat (length cl)) /\ ew E 18 = Z_to_bv 64 (hx_cap x) /\ ew E 19 = Z_to_bv 64 (hx_O x) /\
ew E 24 = Z_to_bv 64 ch /\ ew E 13 = Z_to_bv 64 p.
Proof.
intros x r cc n ch p cl keys rf F fc regs mem md v Hc HV E.
pose proof HV as (HC & _ & (Hn & Hso & Hc16 & Hc8 & Hin & _ & (Hcl & _ & Hrf) & Hch & Hp) & Hloop & H23 & H24 & H13 & Hb & Hr & Hs).
pose proof (hk_core_cregs B x _ _ _ _ _ _ HC) as Hcr.
pose proof Hcr as (R2 & R8 & R3 & R4 & R9 & R18 & R19 & R26 & R27).
pose proof (hk_pod B x Hc Hn) as (HP0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HAM & _).
pose proof (hk_frame_win B x Hc) as (FW1 & FW2 & _ & _ & FW5).
pose proof (hk_stack B x Hc) as (S1 & _ & _ & S4 & S5 & S6 & _).
pose proof (hk_out B x Hc) as (Hcap & _ & _ & _ & _ & HO4 & HOc & _).
pose proof asan_consts as ((AC1 & AC2) & _).
pose proof (hv_child x r cc Hso Hin Hc16) as [Hcc Hvs].
pose proof (hgw_u32_range (hx_bs x) cc) as RS. pose proof (hgw_u32_range (hx_bs x) (r + 8)) as RV.
assert (HAM' : hx_P x + hx_len x <= 2 ^ 47) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HAM; lia).
pose proof (hv_Eseg x regs r cc p cl rf v) as (E47 & E48 & E49 & E50 & E51 & E52 & E53 & E54 & E55).
fold E in E47, E48, E49, E50, E51, E52, E53, E54, E55.
unfold Headamp.REAC_HEADAMP_MAX_CH, Headamp.HA_SENS in Hch, Hp.
pose proof Hso as (Hr16 & Hr8 & Hvs20 & Hle). unfold hp_vs in *.
split.
{ apply Forall_cons; [|apply Forall_nil]. apply hv_tr_ok.
  apply (hk_temps_ok B x PAT_KEY cl (ha_res_bytes 0 0 0) regs mem md _ hv_fcs Hc HC).
  assert (Hbnd : 2 <= hv_bnd p <= 56) by (unfold hv_bnd; destruct (p =? Headamp.HA_SENS); lia).
  unfold hv_fcs. repeat apply Forall_cons; try apply Forall_nil.
  - apply (chunk_ok_val rsegs _ _ _ 8 8 (SOff 50 0) (hv_bnd p)); [rewrite hk_sv_SOff0; exact E50 | zside | zside | exact Hb].
  - apply (chunk_ok_val rsegs _ _ _ 24 8 (SOff 51 0) rf); [rewrite hk_sv_SOff0; exact E51 | zside | zside | exact Hr].
  - apply (chunk_ok_val rsegs _ _ _ 32 8 (SOff 52 0) (hx_P x + r + 16)); [rewrite hk_sv_SOff0; exact E52 | zside | zside |].
    exact (proj1 (proj2 (proj2 (proj2 (proj2 Hloop))))).
  - apply (chunk_ok_val rsegs _ _ _ 48 8 (SOff 53 0) (shadow_addr (hx_P x + cc)));
      [rewrite hk_sv_SOff0; exact E53 | unfold shadow_addr, SHADOW_OFF; zside | zside | exact Hs]. }
split; [exact Hcr|].
do 4 (split; [unfold hx_sp in *; lia|]).
split; [lia|]. split; [lia|]. split; [lia|]. split; [unfold hv_bnd; destruct (p =? Headamp.HA_SENS); lia|]. split; [lia|].
split; [lia|]. split; [lia|]. split; [lia|].
split; [unfold hx_len, hp_vs in *; lia|]. split; [unfold hx_len in *; lia|].
split; [exact (hv_Ereg x regs r cc p cl rf v 2 2%bv _ eq_refl R2)|].
split; [exact (hv_Ereg x regs r cc p cl rf v 27 27%bv _ eq_refl R27)|].
split; [exact (hv_Ereg x regs r cc p cl rf v 20 20%bv _ eq_refl (proj1 Hloop))|].
split; [exact (hv_Ereg x regs r cc p cl rf v 18 18%bv _ eq_refl R18)|].
split; [exact (hv_Ereg x regs r cc p cl rf v 19 19%bv _ eq_refl R19)|].
split; [exact (hv_Ereg x regs r cc p cl rf v 24 24%bv _ eq_refl H24)|].
exact (hv_Ereg x regs r cc p cl rf v 13 13%bv _ eq_refl H13).
Qed.

Lemma hv_entry_vv : forall x r cc n ch p cl keys rf v F fc regs mem md, call_ok B x ->
VX_at x r cc n ch p cl keys rf F fc regs mem md -> getr regs 12 = w64 v -> 0 <= v <= 255 ->
st_ok (fx := mkFP F fc) rsegs (hv_E x regs r cc p cl rf v) hv_ss_vv
  (restrict (w_H (hx_W x)) (@mkst (mkFP F fc) regs (Z_to_bv 64 PC_VV) mem (seg_rom rsegs))).
Proof.
intros x r cc n ch p cl keys rf v F fc regs mem md Hc HV H12 Hv.
destruct (hv_vx_facts x r cc n ch p cl keys rf F fc regs mem md v Hc HV)
  as (HR & Hcr & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & E2 & E27 & E20 & E18 & E19 & E24 & E13).
set (E := hv_E x regs r cc p cl rf v) in *.
pose proof (hv_Eseg x regs r cc p cl rf v) as (E47 & E48 & E49 & E50 & E51 & E52 & E53 & E54 & E55).
fold E in E47, E48, E49, E50, E51, E52, E53, E54, E55.
rewrite restrict_mkst_fx. unfold hv_ss_vv. apply (entry_st_ok_full (fx := mkFP F fc) rsegs).
- apply regs_ok_pin; [unfold E, hv_E, hk_env; apply regs_ok_Ereg | intros X; apply (f_equal bv_unsigned) in X; discriminate X |].
  rewrite hk_sv_SOff0, H12. symmetry. exact E55.
- vm_compute; reflexivity.
- exact HR.
- cbn [pairwise_disjoint all_disjoint]. split; exact I.
- split; [|split; [exact I | exact I]].
  apply (hk_atoms_ok B x regs _ _ Hc Hcr).
  unfold hv_atoms_vv. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  change (hk_env x regs (hv_L x r cc p cl rf v)) with E.
  rewrite E20, E18, E24, E13, E50, E51, E52, E53, E55.
  rewrite !unsigned_lit_small by (unfold shadow_addr, SHADOW_OFF in *; lia).
  rewrite !Z.pow_0_r, !Z.mod_1_r. unfold shadow_addr, SHADOW_OFF in *. repeat split; lia.
Qed.

Lemma hv_entry_rf : forall x r cc n ch p cl keys rf F fc regs mem md, call_ok B x ->
VX_at x r cc n ch p cl keys rf F fc regs mem md ->
st_ok (fx := mkFP F fc) rsegs (hv_E x regs r cc p cl rf 0) hv_ss_rf
  (restrict (w_H (hx_W x)) (@mkst (mkFP F fc) regs (Z_to_bv 64 PC_RF) mem (seg_rom rsegs))).
Proof.
intros x r cc n ch p cl keys rf F fc regs mem md Hc HV.
destruct (hv_vx_facts x r cc n ch p cl keys rf F fc regs mem md 0 Hc HV)
  as (HR & Hcr & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & E2 & E27 & E20 & E18 & E19 & E24 & E13).
set (E := hv_E x regs r cc p cl rf 0) in *.
pose proof (hv_Eseg x regs r cc p cl rf 0) as (E47 & E48 & E49 & E50 & E51 & E52 & E53 & E54 & E55).
fold E in E47, E48, E49, E50, E51, E52, E53, E54, E55.
rewrite restrict_mkst_fx. unfold hv_ss_rf. apply (entry_st_ok_full (fx := mkFP F fc) rsegs).
- unfold E, hv_E, hk_env; apply regs_ok_Ereg.
- vm_compute; reflexivity.
- exact HR.
- cbn [pairwise_disjoint all_disjoint]. split; exact I.
- split; [|split; [exact I | exact I]].
  apply (hk_atoms_ok B x regs _ _ Hc Hcr).
  unfold hv_atoms_rf. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  change (hk_env x regs (hv_L x r cc p cl rf 0)) with E.
  rewrite E51, E52, E53.
  rewrite !unsigned_lit_small by (unfold shadow_addr, SHADOW_OFF in *; lia).
  rewrite !Z.pow_0_r, !Z.mod_1_r. unfold shadow_addr, SHADOW_OFF in *. repeat split; lia.
Qed.

Lemma hv_entry_cw : forall x r cc n ch p cl keys rf v F fc regs mem md, call_ok B x ->
VX_at x r cc n ch p cl keys rf F fc regs mem md -> getr regs 12 = w64 v -> 0 <= v <= 255 ->
Z.of_nat (length cl) < hx_cap x ->
st_ok (fx := mkFP F fc) rsegs (hv_E x regs r cc p cl rf v) hv_ss_cw
  (restrict (w_H (hx_W x)) (@mkst (mkFP F fc) regs (Z_to_bv 64 PC_CW) mem (seg_rom rsegs))) /\
sh_ok rsegs hk_Bx hv_SH_cw (hv_E x regs r cc p cl rf v) (mrestrict (w_H (hx_W x)) mem).
Proof.
intros x r cc n ch p cl keys rf v F fc regs mem md Hc HV H12 Hv Hlt.
destruct (hv_vx_facts x r cc n ch p cl keys rf F fc regs mem md v Hc HV)
  as (HR & Hcr & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & E2 & E27 & E20 & E18 & E19 & E24 & E13).
set (E := hv_E x regs r cc p cl rf v) in *.
pose proof (hv_Eseg x regs r cc p cl rf v) as (E47 & E48 & E49 & E50 & E51 & E52 & E53 & E54 & E55).
fold E in E47, E48, E49, E50, E51, E52, E53, E54, E55.
pose proof HV as (HC & _).
pose proof (hk_out_at_cut B pa_segs_low x PAT_KEY cl (ha_res_bytes 0 0 0) regs mem md errno_low Hc HC ltac:(lia))
  as (HRA & HPR).
pose proof (hk_out B x Hc) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HOoff & _).
assert (Hside : hx_O x + 3 * Z.of_nat (length cl) + 3 <= hx_spa x \/ hx_spa x + 0x80 <= hx_O x + 3 * Z.of_nat (length cl)).
{ destruct (Z_le_gt_dec (hx_O x + 3 * Z.of_nat (length cl) + 3) (hx_spa x)) as [Hle|Hgt]; [left; exact Hle|right].
  destruct (Z_le_gt_dec (hx_spa x + 0x80) (hx_O x + 3 * Z.of_nat (length cl))) as [Hle|Hgt2]; [exact Hle|].
  exfalso. apply (HOoff (Z.max (hx_O x + 3 * Z.of_nat (length cl)) (hx_spa x))); [lia|].
  unfold hx_sp in *. lia. }
split.
- rewrite restrict_mkst_fx. unfold hv_ss_cw. apply (entry_st_ok_full (fx := mkFP F fc) rsegs).
  + apply regs_ok_pin; [unfold E, hv_E, hk_env; apply regs_ok_Ereg | intros X; apply (f_equal bv_unsigned) in X; discriminate X |].
    rewrite hk_sv_SOff0, H12. symmetry. exact E55.
  + vm_compute; reflexivity.
  + inversion HR as [|r0 l0 HR0 _]; subst. apply Forall_cons; [exact HR0|]. apply Forall_cons; [|apply Forall_nil].
    unfold region_ok, hv_out. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    change (Ereg regs (w64 SHADOW_OFF :: hk_saved_vals x ++ hk_fs0 :: hv_L x r cc p cl rf v)) with E.
    rewrite (hv_ub E 54 _ E54) by lia.
    split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
    intros o Ho. apply (apresent_writable rsegs). apply HPR. lia.
  + cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, hv_tr, hv_out.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
    change (Ereg regs (w64 SHADOW_OFF :: hk_saved_vals x ++ hk_fs0 :: hv_L x r cc p cl rf v)) with E.
    rewrite (hv_ub E 2 _ E2), (hv_ub E 54 _ E54) by lia.
    split; [split; [|exact I] | split; [exact I | exact I]]. lia.
  + split; [|split; [exact I|]].
    * apply (hk_atoms_ok B x regs _ _ Hc Hcr).
      unfold hv_atoms_cw. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      change (hk_env x regs (hv_L x r cc p cl rf v)) with E.
      rewrite E20, E18, E19, E24, E13, E51, E52, E53, E54, E55.
      rewrite !unsigned_lit_small by (unfold shadow_addr, SHADOW_OFF in *; lia).
      rewrite !Z.pow_0_r, !Z.mod_1_r. unfold HV_PHI, shadow_addr, SHADOW_OFF in *. repeat split; lia.
    * cbn [alias_ok]. split; [|exact I]. unfold hv_oaddr.
      change (Ereg regs (w64 SHADOW_OFF :: hk_saved_vals x ++ hk_fs0 :: hv_L x r cc p cl rf v)) with E.
      change (hk_env x regs (hv_L x r cc p cl rf v)) with E.
      rewrite !denot_lit_U. f_equal.
      rewrite U_SAlu, U_SMd, U_SLit, (U_atom E 19 _ E19) by lia. rewrite (U_atom E 20 _ E20) by lia.
      rewrite (U_atom E 54 _ E54) by lia. cbn [zalu_raw zmd_raw]. unfold zcanon, M64.
      rewrite (Z.mod_small 3) by lia. rewrite (Z.mod_small (Z.of_nat (length cl) * 3)) by lia.
      rewrite Z.mod_small by lia. lia.
- unfold sh_ok, hv_SH_cw. apply Forall_cons; [|apply Forall_nil].
  apply (hk_shent_out B x _ _ E 54 (3 * Z.of_nat (length cl)) 0 3 Hc E27 E54 HRA); lia.
Qed.

(* ======================================= the runs ======================================= *)
(* a region at sp whose write window lies in the temporaries *)
Lemma hv_awr_sp : forall x E r rs U, call_ok B x -> YP09.r_base r = Some 2%nat -> bv_unsigned (ew E 2) = hx_spa x ->
0 <= YP09.r_wlo r -> YP09.r_whi r <= 0x80 ->
awr_okH E rs (hx_STK x) (hx_sp0 x) (hx_FP x) (ablocks B (hx_ly x) (hx_S x)) (ablocks B (hx_lyc x) (hx_Sc x))
  (hx_lyc x) (hx_own x) U ->
awr_okH E (r :: rs) (hx_STK x) (hx_sp0 x) (hx_FP x) (ablocks B (hx_ly x) (hx_S x))
  (ablocks B (hx_lyc x) (hx_Sc x)) (hx_lyc x) (hx_own x) U.
Proof.
intros x E r rs U Hc Hb H2 Hlo Hhi H.
pose proof (hk_stack B x Hc) as HS. pose proof (hk_frame_win B x Hc) as HW.
apply (awr_okH_cons_gen E r rs _ _ _ _ _ _ _ U 2%nat (hx_spa x) Hb H2); [|exact H].
intros a Ha. left. left. unfold T_parse_STK, T_PARSE_FRAME, ESTACK in *. lia.
Qed.

(* Modified by Theorem Labs, 2026-10: lib/A/HPgParseFind.v at 3f58f17126dc (hfa_B2, hfa_awr, hfa_keep, hfa_upd,
   hfa_run, hfa_run_to, hfa_br, hfa_hc, hfa_rg, hfa_rkeep, hfa_cregs) over this segment's regions and kept sets. *)
Ltac hv_Bk HAE B0 k E Bk :=
lazymatch type of B0 with bv_unsigned (ew _ k) = ?F =>
assert (Bk : bv_unsigned (ew E k) = F) by (first [exact B0 | rewrite (proj1 HAE k ltac:(lia)); exact B0]) end.
(* the write set of a run: the temporaries (read-only or [sp + 56, sp + 60)), the pod read-only, out's cell *)
Ltac hv_awr x Hc HAE B20 B540 :=
lazymatch goal with |- awr_okH ?E ?rs _ _ _ _ _ _ _ _ =>
let B2 := fresh "B2" in hv_Bk HAE B20 2%nat E B2;
let B54 := fresh "B54" in try hv_Bk HAE B540 54%nat E B54;
let rs' := eval vm_compute in rs in change rs with rs';
repeat first
[ apply awr_okH_nil
| (apply awr_okH_cons_ro; [cbn; lia|])
| (eapply (hv_awr_sp x E); [exact Hc | reflexivity | exact B2 | cbn; lia | cbn; lia |])
| (eapply (hk_awr_out B x E _ _ _ 54%nat); [exact Hc | reflexivity | exact B54 | cbn [YP09.r_wlo YP09.r_whi]; intros ? ?; lia |]) ]
end.
(* after a run: every byte outside the kept set's complement as before the segment *)
Ltac hv_keep HAE B20 B540 :=
lazymatch goal with HFr : frame_of ?E _ (mrestrict _ _) (mrestrict _ _),
  KW : forall a, _ -> ~ _ -> mrestrict _ _ (Z_to_bv 64 a) = _ |- _ =>
let B2 := fresh "B2" in hv_Bk HAE B20 2%nat E B2;
let B54 := fresh "B54" in try hv_Bk HAE B540 54%nat E B54;
let KS := fresh "KS" in
pose proof (hv_kept _ _ _ _ _ _ _ KW HFr) as KS;
lazymatch type of KS with ?P -> _ => let KX := fresh "KX" in assert (KX : P) by (
  let a := fresh "a" in let rg := fresh "rg" in let Hrg := fresh "Hrg" in let Hb := fresh "Hb" in
  intros a (rg & Hrg & Hb); cbv beta;
  lazymatch type of Hrg with In _ ?rs => let rs' := eval vm_compute in rs in change (In rg rs') in Hrg end;
  repeat (destruct Hrg as [<- | Hrg];
    [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; rewrite ?B2 in Hb; try rewrite B54 in Hb; lia | ]);
  destruct Hrg);
  specialize (KS KX); clear KX KW HFr B2; try clear B54; rename KS into KW end
end;
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
Ltac hv_upd HAE :=
lazymatch goal with HS : st_ok _ ?E' _ _ |- _ =>
lazymatch type of HAE with env_agree ?k ?E0 ?E =>
let H := fresh in assert (H : env_agree k E0 E') by env_agree_chain HAE; clear HAE; rename H into HAE end end.
Ltac hv_run x Hc HAE B20 B540 :=
lazymatch goal with HS : st_ok _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
aj_run_tokH pa_tbl_ok HS HJ SHOK hk_Bspan; [ idtac .. | hv_awr x Hc HAE B20 B540 | hv_keep HAE B20 B540; hv_upd HAE] end.
Ltac hv_run_to x Hc HAE B20 B540 stop :=
lazymatch goal with HS : st_ok _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
aj_run_to_tokH pa_tbl_ok HS HJ SHOK hk_Bspan stop; [ idtac .. | hv_awr x Hc HAE B20 B540 | hv_keep HAE B20 B540; hv_upd HAE] end.
Ltac hv_br Hc :=
lazymatch goal with HS : st_ok _ _ _ _, SH : sh_ok _ _ _ _ _ |- _ => srr_branch_tok pa_tbl_ok HS SH hk_Bspan end;
lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into Hc end.
Ltac hv_hc HAE H :=
rewrite ?branch_eq_U, ?branch_ne_U, ?branch_ltu_U, ?branch_geu_U in H;
lazymatch type of HAE with env_agree ?k ?E0 ?E =>
tryif constr_eq E0 E then idtac else (repeat (rewrite (U_agree k E0 E _ HAE) in H by (vm_compute; reflexivity))) end.
(* a register goal at the end of a run, reduced to the U value of its symbolic value in the entry env *)
Ltac hv_rg HAE :=
lazymatch goal with |- getr (ms_regs ?ms) ?q = _ =>
lazymatch goal with HS : st_ok ?segs ?E ?ss (restrict ?H ms) |- _ =>
  let e := eval vm_compute in (sr_get (ss_regs ss) q) in
  rewrite (st_ok_restrict_reg segs H E ss ms q HS);
  change (sr_get (ss_regs ss) q) with e;
  unfold w64; rewrite denot_lit_U; f_equal;
  lazymatch type of HAE with env_agree ?k ?E0 _ =>
    tryif constr_eq E0 E then idtac else rewrite (U_agree k E0 E e HAE ltac:(vm_compute; reflexivity)) end
end end.
Ltac hv_Uv := first [ (apply U_lit; lia) | (apply U_atom; [eassumption | unfold shadow_addr, SHADOW_OFF; lia]) ].
(* a register the run kept *)
Ltac hv_rkeep x regs HAE n q :=
lazymatch goal with HS : st_ok _ ?E ?ss (restrict (w_H ?W) ?ms) |- _ =>
lazymatch type of HAE with env_agree ?k ?E0 _ =>
  rewrite (hv_reg_of regs E0 E ss ms (w_H W) q n k HS ltac:(vm_compute; reflexivity) HAE ltac:(lia)
                   ltac:(unfold hv_E; apply hk_env_reg; reflexivity)) end
end.
Ltac hv_cregs x regs HAE HCR :=
apply (hk_cregs_same _ regs _ HCR);
[ hv_rkeep x regs HAE 2%nat (2%bv : bv 5); reflexivity
| hv_rkeep x regs HAE 3%nat (3%bv : bv 5); reflexivity
| hv_rkeep x regs HAE 4%nat (4%bv : bv 5); reflexivity
| hv_rkeep x regs HAE 8%nat (8%bv : bv 5); reflexivity
| hv_rkeep x regs HAE 9%nat (9%bv : bv 5); reflexivity
| hv_rkeep x regs HAE 18%nat (18%bv : bv 5); reflexivity
| hv_rkeep x regs HAE 19%nat (19%bv : bv 5); reflexivity
| hv_rkeep x regs HAE 26%nat (26%bv : bv 5); reflexivity
| hv_rkeep x regs HAE 27%nat (27%bv : bv 5); reflexivity ].
Ltac hv_mkst x :=
lazymatch goal with HS : st_ok _ _ _ (restrict _ _) |- _ =>
  rewrite (st_ok_restrict_mkst rsegs (w_H (hx_W x)) _ _ _ HS ltac:(vm_compute; reflexivity)) end.
(* the way out to ADV with no new cell *)
Ltac hv_adv x regs HAE HCR Hc HV HADV :=
hv_mkst x;
eapply HADV;
eapply (hv_to_ADV x _ _ _ _ _ _ _ _ _ _ _ regs _ _ _ _ _ Hc HV);
[ lazymatch goal with KW : forall a, _ -> ~ _ -> mrestrict _ _ (Z_to_bv 64 a) = _ |- _ => exact KW end
| lazymatch goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => exact HJ end
| hv_kio
| hv_cregs x regs HAE HCR
| hv_rkeep x regs HAE 20%nat (20%bv : bv 5); reflexivity
| hv_rkeep x regs HAE 21%nat (21%bv : bv 5); reflexivity
| hv_rkeep x regs HAE 22%nat (22%bv : bv 5); reflexivity
| hv_rkeep x regs HAE 23%nat (23%bv : bv 5); reflexivity
| hv_rg HAE; hv_Uv | hv_rg HAE; hv_Uv | hv_rg HAE; hv_Uv
| hv_rg HAE
| hv_rg HAE; hv_Uv
| ].

(* ---------------------------------- RF 0x84cf4 -> ADV ---------------------------------- *)
Lemma hv_rf_ok : forall x r cc n ch p cl keys rf, call_ok B x ->
(forall cl' rf', ADV_ok B MT x r cc n None cl' (keys + 1) rf') -> RF_ok x r cc n ch p cl keys rf.
Proof.
intros x r cc n ch p cl keys rf Hc HADV F fc regs mem md HV Hres.
unfold ADV_ok, cfg_at in *.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof (hv_m_refuse x r cc n ch p cl keys rf (proj1 (proj2 (proj2 HV))) Hres) as Hm.
pose proof (hv_entry_rf x r cc n ch p cl keys rf F fc regs mem md Hc HV) as HS.
destruct (hv_vx_facts x r cc n ch p cl keys rf F fc regs mem md 0 Hc HV)
  as (_ & HCR & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & E2 & E27 & E20 & E18 & E19 & E24 & E13).
pose proof (hv_Eseg x regs r cc p cl rf 0) as (E47 & E48 & E49 & E50 & E51 & E52 & E53 & E54 & E55).
assert (SHOK : sh_ok rsegs hk_Bx [] (hv_E x regs r cc p cl rf 0) (mrestrict (w_H (hx_W x)) mem)) by apply Forall_nil.
pose proof HV as (((HJ & _ & _) & _) & _).
let K := eval vm_compute in (run_K 0 hk_Bx [] hv_ss_rf) in
assert (HAE : env_agree K (hv_E x regs r cc p cl rf 0) (hv_E x regs r cc p cl rf 0)) by apply env_agree_refl.
assert (B20 : bv_unsigned (ew (hv_E x regs r cc p cl rf 0) 2) = hx_spa x) by (rewrite E2; apply unsigned_lit_small; lia).
assert (B540 : bv_unsigned (ew (hv_E x regs r cc p cl rf 0) 54) = hx_O x + 3 * Z.of_nat (length cl))
  by (rewrite E54; apply unsigned_lit_small; lia).
assert (KW : forall a, 0 <= a < 2 ^ 64 -> ~ (hx_spa x + 56 <= a < hx_spa x + 60) ->
  mrestrict (w_H (hx_W x)) mem (Z_to_bv 64 a) = mrestrict (w_H (hx_W x)) mem (Z_to_bv 64 a)) by reflexivity.
change (w64 PC_RF) with (Z_to_bv 64 PC_RF).
(* 0x84cf4 .. 0x84d08 the reloads, a7 = 5; 0x84af0 beqz a1 (rf = 0) *)
hv_run x Hc HAE B20 B540. hv_br Hb1; hv_hc HAE Hb1;
rewrite (U_atom _ 51 rf E51) in Hb1 by lia; rewrite U_lit in Hb1 by lia.
- apply Z.eqb_eq in Hb1. subst rf.
  hv_run_to x Hc HAE B20 B540 PC_ADV.
  hv_adv x regs HAE HCR Hc HV (HADV cl (hv_rf' 0)); first [exact Hm | apply U_lit; lia].
- apply Z.eqb_neq in Hb1.
  hv_run_to x Hc HAE B20 B540 PC_ADV.
  hv_adv x regs HAE HCR Hc HV (HADV cl (hv_rf' rf));
    first [exact Hm | unfold hv_rf', Headamp.REFUSE_NONE; rewrite (proj2 (Z.eqb_neq rf 0) Hb1); hv_Uv].
Qed.

(* ---------------------------------- CW 0x84bb0 -> ADV: the cell (ch, p, v) written ---------------------------------- *)
Lemma hv_cw_ok : forall x r cc n ch p cl keys rf v, call_ok B x ->
(forall cl' rf', ADV_ok B MT x r cc n None cl' (keys + 1) rf') -> CW_ok x r cc n ch p cl keys rf v.
Proof.
intros x r cc n ch p cl keys rf v Hc HADV F fc regs mem md HV H12 Hv Hlt Hres.
unfold ADV_ok, cfg_at in *.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof (hv_m_cell x r cc n ch p cl keys rf v (proj1 (proj2 (proj2 HV))) Hlt Hres) as Hm.
destruct (hv_entry_cw x r cc n ch p cl keys rf v F fc regs mem md Hc HV H12 Hv Hlt) as [HS SHOK].
destruct (hv_vx_facts x r cc n ch p cl keys rf F fc regs mem md v Hc HV)
  as (_ & HCR & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & E2 & E27 & E20 & E18 & E19 & E24 & E13).
pose proof (hv_Eseg x regs r cc p cl rf v) as (E47 & E48 & E49 & E50 & E51 & E52 & E53 & E54 & E55).
pose proof HV as (((HJ & _ & _) & _) & _).
let K := eval vm_compute in (run_K 0 hk_Bx hv_SH_cw hv_ss_cw) in
assert (HAE : env_agree K (hv_E x regs r cc p cl rf v) (hv_E x regs r cc p cl rf v)) by apply env_agree_refl.
assert (B20 : bv_unsigned (ew (hv_E x regs r cc p cl rf v) 2) = hx_spa x) by (rewrite E2; apply unsigned_lit_small; lia).
assert (B540 : bv_unsigned (ew (hv_E x regs r cc p cl rf v) 54) = hx_O x + 3 * Z.of_nat (length cl))
  by (rewrite E54; apply unsigned_lit_small; lia).
assert (KW : forall a, 0 <= a < 2 ^ 64 ->
  ~ (hx_O x + 3 * Z.of_nat (length cl) <= a < hx_O x + 3 * Z.of_nat (length cl) + 3) ->
  mrestrict (w_H (hx_W x)) mem (Z_to_bv 64 a) = mrestrict (w_H (hx_W x)) mem (Z_to_bv 64 a)) by reflexivity.
change (w64 PC_CW) with (Z_to_bv 64 PC_CW).
(* 0x84bb0 .. 0x84c0c: the three instrumented sb (ch, p, v), s8 = 0, addiw s4, s9 = [sp + 24]; 0x849d4 the reloads *)
hv_run_to x Hc HAE B20 B540 PC_ADV.
hv_mkst x.
lazymatch goal with HS : st_ok _ ?E ?ss (restrict _ ?ms) |- _ =>
  hv_Bk HAE B540 54%nat E B54;
  let m := eval vm_compute in (ss_mem ss) in
  lazymatch m with ?r0 :: YP09.mkRegion _ _ _ _ _ ?cs :: ?rest =>
    assert (Hmem : ss_mem ss = r0 :: YP09.mkRegion (Some 54%nat) 0 3 0 3 cs :: rest) by (vm_compute; reflexivity);
    pose proof (fun off e w => hv_out_val E ss ms (w_H (hx_W x)) r0 rest cs off e w HS Hmem) as HOV;
    rewrite B54 in HOV
  end
end.
eapply (HADV (cl ++ [(ch, p, v)]) rf).
eapply (hv_to_ADVc x r cc n ch p cl keys rf v F fc regs mem md _ _ _ Hc HV Hv Hlt).
- lazymatch goal with KW : forall a, _ -> ~ _ -> mrestrict _ _ (Z_to_bv 64 a) = _ |- _ => exact KW end.
- rewrite <- (Z.add_0_r (hx_O x + 3 * Z.of_nat (length cl))).
  apply (HOV 0 (SOff 24 0) ch); [cbn [In]; tauto | | lia].
  rewrite hk_sv_SOff0, (proj1 HAE 24%nat ltac:(lia)). exact E24.
- apply (HOV 1 (SOff 13 0) p); [cbn [In]; tauto | | lia].
  rewrite hk_sv_SOff0, (proj1 HAE 13%nat ltac:(lia)). exact E13.
- apply (HOV 2 (SOff 55 0) v); [cbn [In]; tauto | | lia].
  rewrite hk_sv_SOff0, (proj1 HAE 55%nat ltac:(lia)). exact E55.
- lazymatch goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => exact HJ end.
- hv_kio.
- hv_cregs x regs HAE HCR.
- hv_rg HAE. apply (U_atom_off _ 20 _ 1 E20); lia.
- hv_rkeep x regs HAE 21%nat (21%bv : bv 5); reflexivity.
- hv_rkeep x regs HAE 22%nat (22%bv : bv 5); reflexivity.
- hv_rkeep x regs HAE 23%nat (23%bv : bv 5); reflexivity.
- hv_rg HAE; hv_Uv.
- hv_rg HAE; hv_Uv.
- hv_rg HAE; hv_Uv.
- hv_rg HAE; hv_Uv.
- hv_rg HAE; hv_Uv.
- exact Hm.
Qed.

(* ---------------------------------- VV 0x84b8c: the bound and the cap ---------------------------------- *)
Lemma hv_bge : forall E a b u w, U E a = u -> U E b = w -> 0 <= u < 2 ^ 63 -> 0 <= w < 2 ^ 63 ->
branch_taken BC_GE (sv_denot E a) (sv_denot E b) = negb (u <? w).
Proof.
intros E a b u w Ha Hb Hu Hw. rewrite !denot_lit_U, Ha, Hb. cbn [branch_taken]. unfold bv_lts.
rewrite !Z_to_bv_signed, !bv_swrap_small by (change (bv_half_modulus 64) with (2 ^ 63); lia). reflexivity.
Qed.

Lemma hv_vv_ok : forall x r cc n ch p cl keys rf v, call_ok B x ->
(forall cl' rf', ADV_ok B MT x r cc n None cl' (keys + 1) rf') -> EXIT_ok B MT x ->
CW_ok x r cc n ch p cl keys rf v -> VV_ok x r cc n ch p cl keys rf v.
Proof.
intros x r cc n ch p cl keys rf v Hc HADV HEXIT HCW F fc regs mem md HV H12 Hv Hres.
unfold ADV_ok, EXIT_ok, CW_ok, cfg_at in *.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof (proj1 (proj2 (proj2 HV))) as Hcx.
pose proof Hcx as (Hn & Hso & Hc16 & Hc8 & Hin & Hfu & (Hcl & Hk & Hrf) & Hch & Hp).
pose proof (hv_entry_vv x r cc n ch p cl keys rf v F fc regs mem md Hc HV H12 Hv) as HS.
destruct (hv_vx_facts x r cc n ch p cl keys rf F fc regs mem md v Hc HV)
  as (_ & HCR & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & E2 & E27 & E20 & E18 & E19 & E24 & E13).
pose proof (hv_Eseg x regs r cc p cl rf v) as (E47 & E48 & E49 & E50 & E51 & E52 & E53 & E54 & E55).
assert (SHOK : sh_ok rsegs hk_Bx [] (hv_E x regs r cc p cl rf v) (mrestrict (w_H (hx_W x)) mem)) by apply Forall_nil.
pose proof HV as (((HJ & _ & _) & _) & _).
let K := eval vm_compute in (run_K 0 hk_Bx [] hv_ss_vv) in
assert (HAE : env_agree K (hv_E x regs r cc p cl rf v) (hv_E x regs r cc p cl rf v)) by apply env_agree_refl.
assert (B20 : bv_unsigned (ew (hv_E x regs r cc p cl rf v) 2) = hx_spa x) by (rewrite E2; apply unsigned_lit_small; lia).
assert (B540 : bv_unsigned (ew (hv_E x regs r cc p cl rf v) 54) = hx_O x + 3 * Z.of_nat (length cl))
  by (rewrite E54; apply unsigned_lit_small; lia).
assert (KW : forall a, 0 <= a < 2 ^ 64 -> ~ (hx_spa x + 56 <= a < hx_spa x + 60) ->
  mrestrict (w_H (hx_W x)) mem (Z_to_bv 64 a) = mrestrict (w_H (hx_W x)) mem (Z_to_bv 64 a)) by reflexivity.
assert (Hvr : Headamp.value_in_range p v = (v <? hv_bnd p)) by (apply hv_range; exact Hp).
change (w64 PC_VV) with (Z_to_bv 64 PC_VV).
(* 0x84b8c .. 0x84ba4: a0 = zext.b a2 and the reloads; 0x84ba8 bgeu a0,t0 (value >= bound) *)
hv_run x Hc HAE B20 B540. hv_br Hb1; hv_hc HAE Hb1;
rewrite (U_and_lit _ _ 255) in Hb1 by lia; rewrite (U_atom _ 55 v E55), (U_atom _ 50 _ E50) in Hb1 by lia;
replace (Z.land v 255) with v in Hb1 by (change 255 with (Z.ones 8); rewrite Z.land_ones by lia;
  change (2 ^ 8) with 256; rewrite Z.mod_small by lia; reflexivity).
- (* taken: out of range, the refusal *)
  apply negb_true_iff, Z.ltb_ge in Hb1.
  assert (Hres' : hx_res x = Headamp.ha_result (hp_fold_after (hx_cap x) (inl Headamp.REFUSE_OUT_OF_RANGE)
    (hv_rest x r cc n) cl keys rf)).
  { rewrite Hres. unfold hv_cellv. rewrite Hvr, (proj2 (Z.ltb_ge _ _) Hb1). reflexivity. }
  pose proof (hv_m_refuse x r cc n ch p cl keys rf Hcx Hres') as Hm.
  hv_run x Hc HAE B20 B540. hv_br Hb2; hv_hc HAE Hb2;
  rewrite (U_atom _ 51 rf E51) in Hb2 by lia; rewrite U_lit in Hb2 by lia.
  + apply Z.eqb_eq in Hb2. subst rf.
    hv_run_to x Hc HAE B20 B540 PC_ADV.
    hv_adv x regs HAE HCR Hc HV (HADV cl (hv_rf' 0)); first [exact Hm | apply U_lit; lia].
  + apply Z.eqb_neq in Hb2.
    hv_run_to x Hc HAE B20 B540 PC_ADV.
    hv_adv x regs HAE HCR Hc HV (HADV cl (hv_rf' rf));
      first [exact Hm | unfold hv_rf', Headamp.REFUSE_NONE; rewrite (proj2 (Z.eqb_neq rf 0) Hb2); hv_Uv].
- (* not taken: in range *)
  apply negb_false_iff, Z.ltb_lt in Hb1.
  assert (Hin' : hv_cellv ch p v = inr (ch, p, v))
    by (unfold hv_cellv; rewrite Hvr, (proj2 (Z.ltb_lt _ _) Hb1); reflexivity).
  rewrite Hin' in Hres. cbn [hp_fold_after] in Hres.
  (* 0x84bac bge s4,s2 (n >= cap) *)
  hv_run x Hc HAE B20 B540. hv_br Hb3;
  lazymatch type of Hb3 with branch_taken BC_GE (sv_denot ?E' _) _ = _ =>
    rewrite (hv_bge E' (SOff 20 0) (SOff 18 0) (Z.of_nat (length cl)) (hx_cap x)) in Hb3;
    [ | try rewrite (U_agree _ _ E' _ HAE) by (vm_compute; reflexivity); apply U_atom; [exact E20 | lia]
      | try rewrite (U_agree _ _ E' _ HAE) by (vm_compute; reflexivity); apply U_atom; [exact E18 | lia] | lia | lia ]
  end.
  + (* taken: no cell left; EXIT *)
    apply negb_true_iff, Z.ltb_ge in Hb3.
    rewrite (proj2 (Z.leb_le _ _) Hb3) in Hres.
    pose proof (hv_m_exit x r cc n ch p cl keys rf Hcx Hres) as Hm.
    hv_run_to x Hc HAE B20 B540 PC_EXIT.
    hv_mkst x. eapply (HEXIT cl (keys + 1) rf).
    eapply (hv_to_EXIT x r cc n ch p cl keys rf F fc regs mem md _ _ _ Hc HV).
    * lazymatch goal with KW : forall a, _ -> ~ _ -> mrestrict _ _ (Z_to_bv 64 a) = _ |- _ => exact KW end.
    * lazymatch goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => exact HJ end.
    * hv_kio.
    * hv_cregs x regs HAE HCR.
    * hv_rkeep x regs HAE 20%nat (20%bv : bv 5); reflexivity.
    * hv_rg HAE; hv_Uv.
    * exact Hm.
  + (* not taken: the cell *)
    apply negb_false_iff, Z.ltb_lt in Hb3.
    rewrite (proj2 (Z.leb_gt _ _) Hb3) in Hres.
    hv_run_to x Hc HAE B20 B540 PC_CW.
    hv_mkst x. eapply HCW; [ | | exact Hv | exact Hb3 | exact Hres ].
    * eapply (hv_to_VX x r cc n ch p cl keys rf F fc regs mem md F fc _ _ _ Hc HV (proj1 (proj2 HV))).
      -- lazymatch goal with KW : forall a, _ -> ~ _ -> mrestrict _ _ (Z_to_bv 64 a) = _ |- _ => exact KW end.
      -- lazymatch goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => exact HJ end.
      -- hv_kio.
      -- hv_cregs x regs HAE HCR.
      -- hv_rkeep x regs HAE 20%nat (20%bv : bv 5); reflexivity.
      -- hv_rkeep x regs HAE 21%nat (21%bv : bv 5); reflexivity.
      -- hv_rkeep x regs HAE 22%nat (22%bv : bv 5); reflexivity.
      -- hv_rkeep x regs HAE 23%nat (23%bv : bv 5); reflexivity.
      -- hv_rkeep x regs HAE 24%nat (24%bv : bv 5); reflexivity.
      -- hv_rkeep x regs HAE 13%nat (13%bv : bv 5); reflexivity.
    * hv_rg HAE; hv_Uv.
Qed.

(* ---------------------------------- FL 0x84cb4: the double steps, then VV or RF ---------------------------------- *)
(* Modified by Theorem Labs, 2026-10: lib/AU/HPgParseV.v at fc99ac52adf7 (pbV_fxw_keep, and pbV_flt's reading of the
   read-only doubles at the cut). *)
Lemma hv_fxw_keep : forall F fc G fc', hp_fxw F fc ->
  (forall k : bv 5, bv_unsigned k <> 14 -> bv_unsigned k <> 15 -> Sem.reg_get G k = Sem.reg_get F k) ->
  YK0o.frm_zero fc' -> hp_fxw G fc'.
Proof.
intros F fc G fc' ((HF & _) & H8) HG HZ. split; [split|].
- intros k Hk. change (Sem.reg_get G k = Sem.reg_get (@fp_regs fx) k).
  rewrite HG; [exact (HF k Hk) | |]; intros E; apply Hk; rewrite E; cbn; auto.
- exact HZ.
- rewrite HG by (vm_compute; lia). exact H8.
Qed.

Lemma hv_fl_ok : forall x r cc n ch p cl keys rf, call_ok B x ->
(forall v, VV_ok x r cc n ch p cl keys rf v) -> RF_ok x r cc n ch p cl keys rf ->
forall b F fc regs mem md, VX_at x r cc n ch p cl keys rf F fc regs mem md -> 0 <= b < 2 ^ 32 ->
val_mem rsegs (hx_rd x mem) (hx_spa x + 56) 4 b ->
hx_res x = Headamp.ha_result (hp_fold_after (hx_cap x)
  (match Nearest.nearest b 0 255 with Some v => hv_cellv ch p v | None => inl Headamp.REFUSE_OUT_OF_RANGE end)
  (hv_rest x r cc n) cl keys rf) ->
SRr rsegs (hx_W x) (cfg_at (fx := mkFP F fc) rsegs PC_FL regs mem md) (PPOST B MT x).
Proof.
intros x r cc n ch p cl keys rf Hc HVV HRF b F fc regs mem md HV Hb V56 Hres.
unfold VV_ok, RF_ok, cfg_at in *.
pose proof HV as (HC & Hfx & (_ & _ & _ & _ & _ & _ & (Hcl & _) & _) & _).
pose proof Hfx as ((HFk & HZ) & H8).
pose proof (hk_core_cregs B x _ _ _ _ _ _ HC) as HCR. pose proof HCR as (H2 & _).
pose proof HC as ((HJ & _ & _) & _).
pose proof (hk_out B x Hc) as (Hcap & _).
(* the two read-only doubles, at the cut *)
destruct (hk_call_args B x Hc) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hro0 & _).
assert (Hro : hd_ro_cells rsegs (w_H (hx_W x)) mem (hi_dcs headamp_himg_A)).
{ apply (hk_ro_cells_at_cut B pa_segs_low x PAT_KEY cl (ha_res_bytes 0 0 0) regs mem md _ Hc HC ltac:(lia) Hro0).
  change (hi_dcs headamp_himg_A) with headamp_A_dcs. unfold headamp_A_dcs.
  repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; intros kk Hkk; (split;
  [ lazymatch goal with |- in_img _ (?a + kk) =>
      apply (HPgSat.img_chk_ok rsegs a 8 ltac:(vm_compute; reflexivity) kk); lia end | rewrite HBerrno; lia ]). }
unfold hd_ro_cells in Hro. rewrite Forall_forall in Hro.
assert (DH : val_mem rsegs (mrestrict (w_H (hx_W x)) mem) 0x10378 8 D_HALF)
  by (apply (Hro (0x10378, D_HALF)); vm_compute; auto).
assert (D256 : val_mem rsegs (mrestrict (w_H (hx_W x)) mem) 0x10340 8 D_256)
  by (apply (Hro (0x10340, D_256)); vm_compute; auto).
clear Hro Hro0.
change (w64 (hx_spa x)) with (Z_to_bv 64 (hx_spa x)) in H2.
destruct (hv_fl_steps F fc regs (mrestrict (w_H (hx_W x)) mem) b (hx_spa x) HZ H8 H2 Hb V56 DH D256)
  as (G & C' & regs1 & pc1 & P & HC' & HG & HR & Hcase).
assert (HF2 : hp_fxw G C') by exact (hv_fxw_keep F fc G C' Hfx HG HC').
eapply (SRr_msteps rsegs pa_wx).
{ rewrite restrict_mkst_fx. exact P. }
intros md' Hsame Hcl'. rewrite (same_but_materialized_wvb md md' Hsame), unrestrict_mkst_mrestrict.
pose proof (AR_laws_ok rsegs B) as LAWS.
assert (HJ2 : ajournal rsegs B (hx_STK x) (hx_sp0 x) (hx_FP x) (hx_ly x) (hx_S x) (hx_W0 x) (hx_mem0 x) (hx_md0 x)
  (hx_own x) (hx_lyc x) (hx_Sc x) (hx_W x) (unpoison (hU (hx_fr x) PAT_KEY) mem)
  (with_vm_backing (m_vm_lazy md) (m_vm_materialized md') md) (hx_k x))
  by (eapply ajournal_materialize; first [exact LAWS | exact pa_segs_low | exact HJ]).
assert (HVX : VX_at x r cc n ch p cl keys rf G C' regs1 mem (with_vm_backing (m_vm_lazy md) (m_vm_materialized md') md)).
{ apply (hv_to_VX x r cc n ch p cl keys rf F fc regs mem md G C' regs1 mem _ Hc HV HF2 (fun _ _ _ => eq_refl) HJ2
    (hv_same_io_wvb _ _ _)).
  - apply (hk_cregs_same _ regs _ HCR); apply HR; vm_compute; lia.
  - apply HR; vm_compute; lia.
  - apply HR; vm_compute; lia.
  - apply HR; vm_compute; lia.
  - apply HR; vm_compute; lia.
  - apply HR; vm_compute; lia.
  - apply HR; vm_compute; lia. }
pose proof (hfp_nearest b Hb) as HN.
destruct (ParseFP.rfn_in b (Z_to_bv 64 0) (Z_to_bv 64 D_256)) eqn:Ein.
- destruct Hcase as (-> & H12).
  unfold D_256 in Ein. rewrite Ein in HN.
  pose proof (hfp_in_r_range b Hb Ein) as Hrr.
  apply (HVV (ParseFP.rfn_r b) G C' regs1 mem _ HVX); [exact H12 | lia |].
  rewrite Hres, HN. reflexivity.
- subst pc1. unfold D_256 in Ein. rewrite Ein in HN.
  apply (HRF G C' regs1 mem _ HVX). rewrite Hres, HN. reflexivity.
Qed.

(* ---------------------------------- VAL 0x84b30: the pod's size, type and body ---------------------------------- *)
Lemma hv_div20 : forall s, 0 <= s -> (s / 2 ^ 20 =? 0) = (s <? 2 ^ 20).
Proof.
intros s Hs. destruct (Z.ltb_spec s (2 ^ 20)) as [H|H].
- rewrite Z.div_small by lia. reflexivity.
- apply Z.eqb_neq. assert (1 <= s / 2 ^ 20) by (apply Z.div_le_lower_bound; lia). lia.
Qed.

Lemma hv_s32_small : forall w, 0 <= w <= 255 -> Accessors.s32 w = w.
Proof. intros w H. unfold Accessors.s32. rewrite (proj2 (Z.ltb_lt w (2 ^ 31))) by lia. reflexivity. Qed.

Lemma hv_val_ok : forall x r cc n ch p cl keys rf, call_ok B x ->
(forall cl' rf', ADV_ok B MT x r cc n None cl' (keys + 1) rf') -> EXIT_ok B MT x -> VAL_ok B MT x r cc n ch p cl keys rf.
Proof.
intros x r cc n ch p cl keys rf Hc HADV HEXIT.
assert (HRF : RF_ok x r cc n ch p cl keys rf) by (apply hv_rf_ok; [exact Hc | exact HADV]).
assert (HVV : forall v, VV_ok x r cc n ch p cl keys rf v).
{ intros v. apply hv_vv_ok; [exact Hc | exact HADV | exact HEXIT |]. apply hv_cw_ok; [exact Hc | exact HADV]. }
intros F fc regs mem md HVal.
destruct (hv_VAL x r cc n ch p cl keys rf F fc regs mem md HVal) as (HV & H16 & Hres).
unfold ADV_ok, VV_ok, cfg_at in *.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof (proj1 (proj2 (proj2 HV))) as Hcx.
pose proof Hcx as (Hn & Hso & Hc16 & Hc8 & Hin & Hfu & (Hcl & Hk & Hrf) & Hch & Hp).
pose proof HV as (HC & Hfx & _).
destruct (hv_vx_facts x r cc n ch p cl keys rf F fc regs mem md 0 Hc HV)
  as (_ & HCR & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & E2 & E27 & E20 & E18 & E19 & E24 & E13).
pose proof (hv_Eseg x regs r cc p cl rf 0) as (E47 & E48 & E49 & E50 & E51 & E52 & E53 & E54 & E55).
pose proof HC as ((HJ & _ & _) & _).
set (s := Spa.u32_at (hx_bs x) cc) in *. set (t := Spa.u32_at (hx_bs x) (cc + 4)) in *.
set (b := Spa.u32_at (hx_bs x) (cc + 8)) in *.
pose proof (hgw_u32_range (hx_bs x) cc) as RS. pose proof (hgw_u32_range (hx_bs x) (cc + 4)) as RT.
pose proof (hgw_u32_range (hx_bs x) (cc + 8)) as RB. fold s t b in RS, RT, RB.
assert (B20 : bv_unsigned (ew (hv_E x regs r cc p cl rf 0) 2) = hx_spa x) by (rewrite E2; apply unsigned_lit_small; lia).
assert (B540 : bv_unsigned (ew (hv_E x regs r cc p cl rf 0) 54) = hx_O x + 3 * Z.of_nat (length cl))
  by (rewrite E54; apply unsigned_lit_small; lia).
assert (KW : forall a, 0 <= a < 2 ^ 64 -> ~ (hx_spa x + 56 <= a < hx_spa x + 60) ->
  mrestrict (w_H (hx_W x)) mem (Z_to_bv 64 a) = mrestrict (w_H (hx_W x)) mem (Z_to_bv 64 a)) by reflexivity.
(* the refusal's model *)
assert (HmR : Headamp.parse_value (Spa.child_at (hx_bs x) cc) = None ->
  hp_m_adv x r cc n None cl (keys + 1) (hv_rf' rf)).
{ intros HN. apply (hv_m_refuse x r cc n ch p cl keys rf Hcx). rewrite Hres, (hv_vcell_none ch p _ HN). reflexivity. }
change (w64 PC_VAL) with (Z_to_bv 64 PC_VAL).
destruct (4 <=? s) eqn:Hbig.
- (* size >= 4 *)
  apply Z.leb_le in Hbig.
  destruct (hv_entry_val x r cc n ch p cl keys rf F fc regs mem md true Hc HVal ltac:(apply Z.leb_le; exact Hbig))
    as [HS SHOK].
  let K := eval vm_compute in (run_K 0 hk_Bx (hv_SH_val true) (hv_ss_val true)) in
  assert (HAE : env_agree K (hv_E x regs r cc p cl rf 0) (hv_E x regs r cc p cl rf 0)) by apply env_agree_refl.
  (* 0x84b30 .. 0x84b44: the check of s7, lwu size; bnez size >> 20 *)
  hv_run x Hc HAE B20 B540. hv_br Hb1; hv_hc HAE Hb1.
  all: rewrite hv_U_srl in Hb1 by (rewrite U_lit; lia). all: rewrite U_lit in Hb1 by lia.
  all: rewrite (U_atom _ 47 s E47) in Hb1 by lia. all: rewrite U_lit in Hb1 by lia.
  all: rewrite hv_div20 in Hb1 by lia.
  + (* size >= 2^20: the refusal *)
    apply negb_true_iff, Z.ltb_ge in Hb1.
    pose proof (HmR (hv_res_big (hx_bs x) cc Hb1)) as Hm.
    hv_run x Hc HAE B20 B540. hv_br Hb2; hv_hc HAE Hb2;
    rewrite (U_atom _ 51 rf E51) in Hb2 by lia; rewrite U_lit in Hb2 by lia;
    hv_run_to x Hc HAE B20 B540 PC_ADV;
    hv_adv x regs HAE HCR Hc HV (HADV cl (hv_rf' rf));
    first [ exact Hm | unfold hv_rf', Headamp.REFUSE_NONE, Headamp.REFUSE_OUT_OF_RANGE; rewrite Hb2; cbv iota; hv_Uv ].
  + apply negb_false_iff, Z.ltb_lt in Hb1.
    (* 0x84b48 .. 0x84b70: the type; bne type,2 *)
    hv_run x Hc HAE B20 B540. hv_br Hb2; hv_hc HAE Hb2.
    all: rewrite U_lit in Hb2 by lia. all: rewrite (hgw_U_sext32_eqb _ 48 t 2) in Hb2 by first [apply U_atom; [exact E48 | lia] | lia].
    * (* type <> 2 *)
      apply negb_true_iff, Z.eqb_neq in Hb2.
      hv_run x Hc HAE B20 B540. hv_br Hb3; hv_hc HAE Hb3.
      all: rewrite U_lit in Hb3 by lia. all: rewrite (hgw_U_sext32_eqb _ 48 t 4) in Hb3 by first [apply U_atom; [exact E48 | lia] | lia].
      -- (* type <> 4 *)
        apply negb_true_iff, Z.eqb_neq in Hb3.
        hv_run x Hc HAE B20 B540. hv_br Hb4; hv_hc HAE Hb4.
        all: rewrite U_lit in Hb4 by lia. all: rewrite (hgw_U_sext32_eqb _ 48 t 6) in Hb4 by first [apply U_atom; [exact E48 | lia] | lia].
        ++ (* other types: the refusal *)
          apply negb_true_iff, Z.eqb_neq in Hb4.
          pose proof (HmR (hv_res_bad (hx_bs x) cc Hb1 (or_intror (conj Hb2 (conj Hb3 Hb4))))) as Hm.
          hv_run x Hc HAE B20 B540. hv_br Hb5; hv_hc HAE Hb5;
          rewrite (U_atom _ 51 rf E51) in Hb5 by lia; rewrite U_lit in Hb5 by lia;
          hv_run_to x Hc HAE B20 B540 PC_ADV;
          hv_adv x regs HAE HCR Hc HV (HADV cl (hv_rf' rf));
          first [ exact Hm | unfold hv_rf', Headamp.REFUSE_NONE, Headamp.REFUSE_OUT_OF_RANGE; rewrite Hb5; cbv iota; hv_Uv ].
        ++ (* Float *)
          apply negb_false_iff, Z.eqb_eq in Hb4.
          pose proof (hv_res_flt (hx_bs x) cc Hb1 Hbig Hb4) as Hpv.
          hv_run_to x Hc HAE B20 B540 PC_FL.
          lazymatch goal with HS : st_ok _ ?E ?ss (restrict _ ?ms) |- _ =>
            hv_Bk HAE B20 2%nat E B2;
            let m := eval vm_compute in (ss_mem ss) in
            lazymatch m with YP09.mkRegion _ _ _ ?wlo ?whi ?cs :: ?rest =>
              assert (Hmem : ss_mem ss = YP09.mkRegion (Some 2%nat) 0 0x80 wlo whi cs :: rest) by (vm_compute; reflexivity);
              assert (V56 : val_mem rsegs (mrestrict (w_H (hx_W x)) (ms_mem ms)) (hx_spa x + 56) 4 b)
                by (rewrite <- B2; apply (hv_frame_val E ss ms (w_H (hx_W x)) rest wlo whi cs 56 4 hv_asm b HS Hmem);
                    [ vm_compute; tauto
                    | rewrite denot_lit_U; unfold w64; f_equal;
                      lazymatch type of HAE with env_agree ?k ?E0 _ =>
                        rewrite (U_agree k E0 E hv_asm HAE) by (vm_compute; reflexivity) end;
                      apply hv_U_asm; [apply U_atom; [exact E49 | lia] | lia]
                    | cbn; lia | cbn; lia ])
            end
          end.
          hv_mkst x.
          apply (hv_fl_ok x r cc n ch p cl keys rf Hc HVV HRF b F fc).
          ** eapply (hv_to_VX x r cc n ch p cl keys rf F fc regs mem md F fc _ _ _ Hc HV Hfx).
             --- lazymatch goal with KW : forall a, _ -> ~ _ -> mrestrict _ _ (Z_to_bv 64 a) = _ |- _ => exact KW end.
             --- lazymatch goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => exact HJ end.
             --- hv_kio.
             --- hv_cregs x regs HAE HCR.
             --- hv_rkeep x regs HAE 20%nat (20%bv : bv 5); reflexivity.
             --- hv_rkeep x regs HAE 21%nat (21%bv : bv 5); reflexivity.
             --- hv_rkeep x regs HAE 22%nat (22%bv : bv 5); reflexivity.
             --- hv_rkeep x regs HAE 23%nat (23%bv : bv 5); reflexivity.
             --- hv_rkeep x regs HAE 24%nat (24%bv : bv 5); reflexivity.
             --- hv_rkeep x regs HAE 13%nat (13%bv : bv 5); reflexivity.
          ** exact RB.
          ** exact V56.
          ** rewrite Hres. destruct (Nearest.nearest b 0 255) eqn:EN.
             --- rewrite (hv_vcell_some ch p _ _ (eq_trans Hpv EN)). reflexivity.
             --- rewrite (hv_vcell_none ch p _ (eq_trans Hpv EN)). reflexivity.
      -- (* Int *)
        apply negb_false_iff, Z.eqb_eq in Hb3.
        pose proof (hv_res_int (hx_bs x) cc Hb1 Hbig Hb3) as Hpv. fold b in Hpv.
        hv_run x Hc HAE B20 B540. hv_br Hb4; hv_hc HAE Hb4.
        all: rewrite U_lit in Hb4 by lia. all: rewrite (hgw_U_sext32 _ 49 b) in Hb4 by first [apply U_atom; [exact E49 | lia] | lia].
        ++ (* body <= 255: the value *)
          apply negb_true_iff, Z.ltb_ge in Hb4.
          assert (Hb255 : b <= 255) by (destruct (b <? 2 ^ 31); lia).
          rewrite (proj2 (Z.ltb_lt b (2 ^ 31))) in Hb4 by lia.
          rewrite hv_s32_small in Hpv by lia.
          rewrite (proj2 (Z.ltb_ge b 0)), (proj2 (Z.ltb_ge 255 b)) in Hpv by lia. cbn [orb] in Hpv.
          hv_run_to x Hc HAE B20 B540 PC_VV.
          hv_mkst x. eapply (HVV b).
          ** eapply (hv_to_VX x r cc n ch p cl keys rf F fc regs mem md F fc _ _ _ Hc HV Hfx).
             --- lazymatch goal with KW : forall a, _ -> ~ _ -> mrestrict _ _ (Z_to_bv 64 a) = _ |- _ => exact KW end.
             --- lazymatch goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => exact HJ end.
             --- hv_kio.
             --- hv_cregs x regs HAE HCR.
             --- hv_rkeep x regs HAE 20%nat (20%bv : bv 5); reflexivity.
             --- hv_rkeep x regs HAE 21%nat (21%bv : bv 5); reflexivity.
             --- hv_rkeep x regs HAE 22%nat (22%bv : bv 5); reflexivity.
             --- hv_rkeep x regs HAE 23%nat (23%bv : bv 5); reflexivity.
             --- hv_rkeep x regs HAE 24%nat (24%bv : bv 5); reflexivity.
             --- hv_rkeep x regs HAE 13%nat (13%bv : bv 5); reflexivity.
          ** hv_rg HAE. rewrite (hgw_U_sext32 _ 49 b) by first [apply U_atom; [exact E49 | lia] | lia].
             rewrite (proj2 (Z.ltb_lt b (2 ^ 31))) by lia. reflexivity.
          ** lia.
          ** rewrite Hres, (hv_vcell_some ch p _ _ Hpv). reflexivity.
        ++ (* body > 255: the refusal *)
          apply negb_false_iff, Z.ltb_lt in Hb4.
          assert (HN : Headamp.parse_value (Spa.child_at (hx_bs x) cc) = None).
          { rewrite Hpv. unfold Accessors.s32. destruct (Z.ltb_spec b (2 ^ 31)) as [Hs|Hs]; cbv iota in Hb4 |- *.
            - rewrite (proj2 (Z.ltb_lt 255 b)) by lia. rewrite orb_true_r. reflexivity.
            - rewrite (proj2 (Z.ltb_lt (b - 2 ^ 32) 0)) by lia. reflexivity. }
          pose proof (HmR HN) as Hm.
          hv_run x Hc HAE B20 B540. hv_br Hb5; hv_hc HAE Hb5;
          rewrite (U_atom _ 51 rf E51) in Hb5 by lia; rewrite U_lit in Hb5 by lia;
          hv_run_to x Hc HAE B20 B540 PC_ADV;
          hv_adv x regs HAE HCR Hc HV (HADV cl (hv_rf' rf));
          first [ exact Hm | unfold hv_rf', Headamp.REFUSE_NONE, Headamp.REFUSE_OUT_OF_RANGE; rewrite Hb5; cbv iota; hv_Uv ].
    * (* Bool *)
      apply negb_false_iff, Z.eqb_eq in Hb2.
      pose proof (hv_res_bool (hx_bs x) cc Hb1 Hbig Hb2) as Hpv. fold b in Hpv.
      hv_run_to x Hc HAE B20 B540 PC_VV.
      hv_mkst x. eapply (HVV (if b =? 0 then 0 else 1)).
      -- eapply (hv_to_VX x r cc n ch p cl keys rf F fc regs mem md F fc _ _ _ Hc HV Hfx).
         ++ lazymatch goal with KW : forall a, _ -> ~ _ -> mrestrict _ _ (Z_to_bv 64 a) = _ |- _ => exact KW end.
         ++ lazymatch goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => exact HJ end.
         ++ hv_kio.
         ++ hv_cregs x regs HAE HCR.
         ++ hv_rkeep x regs HAE 20%nat (20%bv : bv 5); reflexivity.
         ++ hv_rkeep x regs HAE 21%nat (21%bv : bv 5); reflexivity.
         ++ hv_rkeep x regs HAE 22%nat (22%bv : bv 5); reflexivity.
         ++ hv_rkeep x regs HAE 23%nat (23%bv : bv 5); reflexivity.
         ++ hv_rkeep x regs HAE 24%nat (24%bv : bv 5); reflexivity.
         ++ hv_rkeep x regs HAE 13%nat (13%bv : bv 5); reflexivity.
      -- hv_rg HAE. rewrite (hv_U_snez _ _ (U (hv_E x regs r cc p cl rf 0) (SExt true 32 (SOff 49 0))) eq_refl).
         rewrite (hgw_U_sext32_eqb _ 49 b 0) by first [apply U_atom; [exact E49 | lia] | lia]. reflexivity.
      -- destruct (b =? 0); lia.
      -- rewrite Hres, (hv_vcell_some ch p _ _ Hpv). reflexivity.
- (* size < 4: the refusal *)
  apply Z.leb_gt in Hbig.
  destruct (hv_entry_val x r cc n ch p cl keys rf F fc regs mem md false Hc HVal ltac:(apply Z.leb_gt; exact Hbig))
    as [HS SHOK].
  let K := eval vm_compute in (run_K 0 hk_Bx (hv_SH_val false) (hv_ss_val false)) in
  assert (HAE : env_agree K (hv_E x regs r cc p cl rf 0) (hv_E x regs r cc p cl rf 0)) by apply env_agree_refl.
  pose proof (HmR (hv_res_bad (hx_bs x) cc ltac:(lia) (or_introl Hbig))) as Hm.
  hv_run x Hc HAE B20 B540. hv_br Hb1; hv_hc HAE Hb1.
  all: rewrite hv_U_srl in Hb1 by (rewrite U_lit; lia). all: rewrite U_lit in Hb1 by lia.
  all: rewrite (U_atom _ 47 s E47) in Hb1 by lia. all: rewrite U_lit in Hb1 by lia.
  all: rewrite hv_div20 in Hb1 by lia.
  + apply negb_true_iff, Z.ltb_ge in Hb1. lia.
  + hv_run x Hc HAE B20 B540. hv_br Hb2; hv_hc HAE Hb2;
    rewrite (U_atom _ 51 rf E51) in Hb2 by lia; rewrite U_lit in Hb2 by lia;
    hv_run_to x Hc HAE B20 B540 PC_ADV;
    hv_adv x regs HAE HCR Hc HV (HADV cl (hv_rf' rf));
    first [ exact Hm | unfold hv_rf', Headamp.REFUSE_NONE, Headamp.REFUSE_OUT_OF_RANGE; rewrite Hb2; cbv iota; hv_Uv ].
Qed.

(* ======================================= the segment ======================================= *)
Theorem hp_segVAL_A : segVAL_stmt B MT.
Proof. intros x r cc n ch p cl keys rf Hc HADV HEXIT. exact (hv_val_ok x r cc n ch p cl keys rf Hc HADV HEXIT). Qed.

End c.

Print Assumptions hp_segVAL_A.
