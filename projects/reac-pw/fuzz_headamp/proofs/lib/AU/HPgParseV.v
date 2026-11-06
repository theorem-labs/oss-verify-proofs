(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the run plumbing of proofs/reac-pw/fuzz_role/lib/A/RPgCfgChanges.v at 964efd2f474 (cfg_keep, cfg_kwr_ro and the same_io chain of cfg_leaf, as l_keep, l_kwr and l_post) and of proofs/reac-pw/fuzz_qdisc/lib/A/QPgCheck.v at b0f706c04a1 (awr_stk, as l_awr: the writable window is the frame [F, F + 0x60) at atom 2), for a segment of reac_role_prop_parse's walk that starts and ends at the cuts of lib/A/RPgParseBase.v; the entry states, exits, string lemmas and the walk below are new. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_role/lib/A/RPgParseL.v; 492 of its 562 lines of code are new or changed and 844 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_role/lib/A/RPgParseF.v, with its module paths and module names changed; 2013 of its 2077 lines of code are new or changed and 498 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_headamp/lib/U/Prog/Seg/ParseValue.v at 3e9fc5c8969; the model
   lemmas pv_range, pv_body, pv_res_big, pv_res_bad, pv_res_bool, pv_res_int, pv_res_flt kept, with the module paths
   changed and the names prefixed pbV_. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgParseFV.v at afaa3cb55c1; the one-instruction
   forms fvw_ld / fvw_addi / fvw_auipc / fvw_jal0 / fvw_beq_tk / fvw_beq_ft and the double steps restated over image
   B's table and code (pbV_tw_*, pbV_fA / pbV_fB / pbV_fC / pbV_fRef). *)
(* reac_headamp_prop_parse_result 0x849ac of reac-pw/fuzz_headamp's ASan + UBSan image B (fuzz_headamp.asan-ubsan,
   pinned sha256 53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94): the segment VAL of its walk,
   lib/AU/HPgParseCut.v segVAL_stmt. Proves no function (kind: segment lemma of reac_headamp_prop_parse_result).

   THE CODE (VAL 0x84f0c; s7 = P + cc the child, s8 = ch, a3 = p, a1 = 0 for sens else 1, a7 = the shadow address
   of s7, [spa + 24] = keys + 1, [spa + 48] = the shadow address of s7):
     0x84f0c .. 0x84f20  the instrumented check of the 4 bytes at s7 through a7 (slow arm 0x85190), CS = lwu 0(s7),
                         t0 = 5, CS >> 20 <> 0 -> the refusal 0x84ec4;
     0x84f24 .. 0x84f3c  the check of s7 + 4 (slow arm 0x851a0), the type = lw 4(s7), a0 = s7 + 8;
     Bool (CS >= 4, type 2): the check of s7 + 8 (slow arm 0x851b0), a2 = (lw 8(s7) <> 0), j 0x84fa0;
     Int (CS >= 4, type 4): the check (slow arm 0x851e4), a2 = lw 8(s7); a2 >u 255 -> 0x85118; else 0x84f94;
     Float (CS >= 4, type 6, 0x85050): the checks of the first and the last of the 4 value bytes (slow arms 0x851f4,
                         0x85200), the 4 bytes put together, sw at spa + 56, then the double steps 0x850ac .. 0x85114
                         (lib/A/HPgParseFP.v): fle.d against fs0 = +0.0, flt.d against 256.0 (the refusal 0x85118
                         when either fails), the cast checks 0x850e4 / 0x850f4 (never taken), fcvt.l.d rtz,
                         fcvt.d.l, flt.d, t - 1 with the check 0x8510c (never taken), j 0x84f94;
     any other value pod: 0x85118 (a4 = [spa + 40], a6 = 8, a7 = [spa + 48], t0 = 5) -> 0x84ec4;
     0x84f94 .. 0x84f9c  a6 = 8, a7 = [spa + 48], t0 = 5;
     0x84fa0 .. 0x84fbc  a0 = a2 & 0xff, a4 = [spa + 40]; the bound 2 (a1 <> 0) or 0x38 (a1 = 0): a0 >=u bound ->
                         0x84ec4 (Headamp.value_in_range fails);
     0x84fc0             n >= cap -> 0x85214 s9 = [spa + 24], then EXIT 0x85218;
     0x84fc4 .. 0x8504c  out + 3 n with the three checks 0x84fd8 / 0x84fec / 0x84ff0 (never taken), the three
                         instrumented 1-byte stores out[3 n] = ch, out[3 n + 1] = p, out[3 n + 2] = the value (slow arms
                         0x851c0, 0x851cc, 0x851d8), s8 = 0, s4 = n + 1, s9 = [spa + 24], a4 = [spa + 40], j ADV;
     0x84ec4 .. 0x84ed8  the refusal: rf' = (rf <> 0 ? rf : t0) -> [spa + 32], s8 = 0, s9 = [spa + 24], then ADV.
   The walk is cut at four inner points of its own: REF 0x84ec4 (a refusal with t0 = 5), TAIL 0x84fa0 (the value v
   in [0, 255] in a2), CELL 0x84fc4 (the value in range, room for the cell) and FLT 0x850ac (the float's 4 bytes at
   spa + 56). The engine of lib/Reusable walks every piece but the double steps 0x850ac .. 0x85114, 0x84f94 ..
   0x84f9c and 0x85118 .. 0x85128 after FLT, which are stepped one instruction at a time. Section hypotheses:
   errno_low (api_env rsegs B) and HBerrno (as_errno B = 0x5d812c, image B's errno cell: it puts the errno cell apart
   from the four read-only doubles and from out's bytes). *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05 YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require FP.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Cursor Model Accessors Spa SpaBool Nearest Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog Require ParseFP.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A.Rt Require Import FMupoison.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec HPgHole HPgParseBase HPgParseFP.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgParseGFind HPgParseGKit HPgParseGEx HPgParseGWalk.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgImgB HPgParseCut.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================================= the model ======================================= *)
(* value_in_range (reac_headamp_prop.c:89-100) is the code's test value < bound (0x84fb0 / 0x84fbc) *)
Lemma pbV_range : forall p v, 0 <= p <= Headamp.HA_SENS ->
  Headamp.value_in_range p v = (v <? (if p =? Headamp.HA_SENS then 0x38 else 2)).
Proof.
intros p v Hp. unfold Headamp.HA_SENS in Hp.
assert (E : p = 0 \/ p = 1 \/ p = 2) by lia.
destruct E as [-> | [-> | ->]];
  unfold Headamp.value_in_range, Headamp.HA_PHANTOM, Headamp.HA_PAD, Headamp.HA_SENS, Headamp.REAC_HEADAMP_SENS_MAX;
  cbv [Z.eqb Pos.eqb orb]; apply eq_true_iff_eq; rewrite Z.leb_le, Z.ltb_lt; lia.
Qed.

(* the body word of a value pod of size >= 4 *)
Lemma pbV_body : forall bs o, 4 <= Spa.u32_at bs o -> Cursor.rd32 (Model.e_body (Spa.child_at bs o)) = Spa.u32_at bs (o + 8).
Proof.
intros bs o H. unfold Spa.child_at. cbn [Model.e_body]. unfold Cursor.rd32 at 1. rewrite firstn_firstn.
replace (Nat.min 4 (Z.to_nat (Spa.u32_at bs o))) with 4%nat by lia. reflexivity.
Qed.

Lemma pbV_res_big : forall bs o, 2 ^ 20 <= Spa.u32_at bs o -> Headamp.parse_value (Spa.child_at bs o) = None.
Proof.
intros bs o H. unfold Headamp.parse_value, SpaBool.spa_get_bool, Spa.spa_get_int, Spa.spa_get_float.
replace (Model.e_size (Spa.child_at bs o)) with (Spa.u32_at bs o) by reflexivity.
unfold Spa.SPA_POD_MAX_SIZE. rewrite (proj2 (Z.ltb_ge _ _) H). reflexivity.
Qed.

Lemma pbV_res_bad : forall bs o, Spa.u32_at bs o < 2 ^ 20 ->
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

Lemma pbV_res_bool : forall bs o, Spa.u32_at bs o < 2 ^ 20 -> 4 <= Spa.u32_at bs o -> Spa.u32_at bs (o + 4) = 2 ->
  Headamp.parse_value (Spa.child_at bs o) = Some (if Spa.u32_at bs (o + 8) =? 0 then 0 else 1).
Proof.
intros bs o H1 H2 H3. unfold Headamp.parse_value, SpaBool.spa_get_bool.
replace (Model.e_size (Spa.child_at bs o)) with (Spa.u32_at bs o) by reflexivity.
replace (Model.e_type (Spa.child_at bs o)) with (Spa.u32_at bs (o + 4)) by reflexivity.
unfold Spa.SPA_POD_MAX_SIZE, Model.POD_BOOL. rewrite H3, (proj2 (Z.ltb_lt _ _) H1), (proj2 (Z.leb_le _ _) H2).
rewrite (pbV_body bs o H2). destruct (Spa.u32_at bs (o + 8) =? 0); reflexivity.
Qed.

Lemma pbV_res_int : forall bs o, Spa.u32_at bs o < 2 ^ 20 -> 4 <= Spa.u32_at bs o -> Spa.u32_at bs (o + 4) = 4 ->
  Headamp.parse_value (Spa.child_at bs o) =
  if (Accessors.s32 (Spa.u32_at bs (o + 8)) <? 0) || (255 <? Accessors.s32 (Spa.u32_at bs (o + 8))) then None
  else Some (Accessors.s32 (Spa.u32_at bs (o + 8))).
Proof.
intros bs o H1 H2 H3. unfold Headamp.parse_value, SpaBool.spa_get_bool, Spa.spa_get_int.
replace (Model.e_size (Spa.child_at bs o)) with (Spa.u32_at bs o) by reflexivity.
replace (Model.e_type (Spa.child_at bs o)) with (Spa.u32_at bs (o + 4)) by reflexivity.
unfold Spa.SPA_POD_MAX_SIZE, Model.POD_BOOL, Model.POD_INT. rewrite H3, (proj2 (Z.ltb_lt _ _) H1), (proj2 (Z.leb_le _ _) H2).
rewrite (pbV_body bs o H2). reflexivity.
Qed.

Lemma pbV_res_flt : forall bs o, Spa.u32_at bs o < 2 ^ 20 -> 4 <= Spa.u32_at bs o -> Spa.u32_at bs (o + 4) = 6 ->
  Headamp.parse_value (Spa.child_at bs o) = Nearest.nearest (Spa.u32_at bs (o + 8)) 0 255.
Proof.
intros bs o H1 H2 H3. unfold Headamp.parse_value, SpaBool.spa_get_bool, Spa.spa_get_int, Spa.spa_get_float.
replace (Model.e_size (Spa.child_at bs o)) with (Spa.u32_at bs o) by reflexivity.
replace (Model.e_type (Spa.child_at bs o)) with (Spa.u32_at bs (o + 4)) by reflexivity.
unfold Spa.SPA_POD_MAX_SIZE, Model.POD_BOOL, Model.POD_INT, Model.POD_FLOAT.
rewrite H3, (proj2 (Z.ltb_lt _ _) H1), (proj2 (Z.leb_le _ _) H2).
rewrite (pbV_body bs o H2). reflexivity.
Qed.

(* the Int body read by `lw`: in [0, 255] exactly when the sign-extended word is <=u 255 *)
Lemma pbV_int_in : forall w, 0 <= w < 2 ^ 32 -> w <= 255 ->
  (Accessors.s32 w <? 0) || (255 <? Accessors.s32 w) = false /\ Accessors.s32 w = w.
Proof.
intros w Hw H. unfold Accessors.s32. rewrite (proj2 (Z.ltb_lt w (2 ^ 31))) by lia.
rewrite (proj2 (Z.ltb_ge w 0)) by lia. rewrite (proj2 (Z.ltb_ge 255 w)) by lia. split; reflexivity.
Qed.

Lemma pbV_int_out : forall w, 0 <= w < 2 ^ 32 -> 255 < w ->
  (Accessors.s32 w <? 0) || (255 <? Accessors.s32 w) = true.
Proof.
intros w Hw H. unfold Accessors.s32. destruct (Z.ltb_spec w (2 ^ 31)).
- rewrite (proj2 (Z.ltb_lt 255 w)) by lia. apply orb_true_r.
- rewrite (proj2 (Z.ltb_lt (w - 2 ^ 32) 0)) by lia. reflexivity.
Qed.

(* the value cell of a key whose verdict is (ch, p) on a value pod parse_value reads as v *)
Lemma pbV_vcell_some : forall ch p e v, 0 <= p <= Headamp.HA_SENS -> Headamp.parse_value e = Some v ->
  hp_vcell ch p e = if v <? (if p =? Headamp.HA_SENS then 0x38 else 2) then inr (ch, p, v)
                    else inl Headamp.REFUSE_OUT_OF_RANGE.
Proof. intros ch p e v Hp He. unfold hp_vcell. rewrite He, (pbV_range p v Hp). reflexivity. Qed.

Lemma pbV_vcell_none : forall ch p e, Headamp.parse_value e = None -> hp_vcell ch p e = inl Headamp.REFUSE_OUT_OF_RANGE.
Proof. intros ch p e He. unfold hp_vcell. rewrite He. reflexivity. Qed.

(* ---- the fold's next state, from VAL's model fact ---- *)
Section m. Context {segs : list Segment}.
Local Notation pctx := (@hp_ctx segs).

(* a refusal: the next child with the key slot empty, keys + 1 and the first refusal kept *)
Lemma pbV_m_ref : forall (x : pctx) r cc n ch p cl keys rf,
  hp_m_val x r cc n ch p cl keys rf ->
  hp_vcell ch p (Spa.child_at (hx_bs x) cc) = inl Headamp.REFUSE_OUT_OF_RANGE ->
  hp_m_adv x r cc n None cl (keys + 1) (if rf =? 0 then 5 else rf).
Proof.
intros x r cc n ch p cl keys rf (H0 & Hst & Hc16 & Hc8 & Hin & Hfu & (Hcap & Hk & Hrf) & _ & _ & Hres) Hv.
rewrite Hv in Hres. cbn [hp_fold_after] in Hres.
unfold hp_m_adv. split; [exact H0|]. split; [exact Hst|]. split; [exact Hc16|]. split; [exact Hc8|].
split; [exact Hin|]. split; [exact Hfu|]. split; [intros ck Hck; discriminate Hck|].
split; [unfold hp_st; split; [exact Hcap|]; split; [lia|]; destruct (Z.eqb_spec rf 0); lia|].
rewrite Hres. unfold Headamp.REFUSE_NONE, Headamp.REFUSE_OUT_OF_RANGE. cbn [hp_l2key]. reflexivity.
Qed.

(* a cell with no room (n >= cap): the walk's end, keys + 1 *)
Lemma pbV_m_exit : forall (x : pctx) r cc n ch p cl keys rf cv,
  hp_m_val x r cc n ch p cl keys rf -> hp_vcell ch p (Spa.child_at (hx_bs x) cc) = inr cv ->
  hx_cap x <= Z.of_nat (length cl) -> hp_m_exit x cl (keys + 1) rf.
Proof.
intros x r cc n ch p cl keys rf cv (H0 & _ & _ & _ & _ & _ & (Hcap & Hk & Hrf) & _ & _ & Hres) Hv Hn.
rewrite Hv in Hres. cbn [hp_fold_after] in Hres. rewrite (proj2 (Z.leb_le _ _) Hn) in Hres.
split; [exact H0|]. split; [unfold hp_st; lia|]. exact Hres.
Qed.

(* a cell written (n < cap): the next child with the key slot empty, the cell appended, keys + 1 *)
Lemma pbV_m_cell : forall (x : pctx) r cc n ch p cl keys rf cv,
  hp_m_val x r cc n ch p cl keys rf -> hp_vcell ch p (Spa.child_at (hx_bs x) cc) = inr cv ->
  Z.of_nat (length cl) < hx_cap x -> hp_m_adv x r cc n None (cl ++ [cv]) (keys + 1) rf.
Proof.
intros x r cc n ch p cl keys rf cv (H0 & Hst & Hc16 & Hc8 & Hin & Hfu & (Hcap & Hk & Hrf) & _ & _ & Hres) Hv Hn.
rewrite Hv in Hres. cbn [hp_fold_after] in Hres. rewrite (proj2 (Z.leb_gt _ _) Hn) in Hres.
unfold hp_m_adv. split; [exact H0|]. split; [exact Hst|]. split; [exact Hc16|]. split; [exact Hc8|].
split; [exact Hin|]. split; [exact Hfu|]. split; [intros ck Hck; discriminate Hck|].
split; [unfold hp_st; rewrite length_app; cbn [length]; lia|].
rewrite Hres. reflexivity.
Qed.
End m.

(* ======================================= one instruction at a literal pc ======================================= *)
Lemma pbV_tw_ld : forall (fs : YK11.FPState) regs mem rom p q wz rd rs (imm : bv 12) base a v,
  clookup pb_tbl p = Some wz -> is_ecall (Z_to_bv 32 wz) = false ->
  decode_any (Z_to_bv 32 wz) = Some (Load SZ8 true rd rs imm, 4%Z) ->
  bv_eqb rd 0 = false -> q = p + 4 ->
  getr regs rs = Z_to_bv 64 base -> a = base + bv_signed imm ->
  val_mem rsegs mem a 8 v -> 0 <= v < 2 ^ 64 ->
  RiscvSemantics.step rsegs (@mkst fs regs (Z_to_bv 64 p) mem rom) =
  MachineOk (@mkst fs (regupd regs rd (Z_to_bv 64 v)) (Z_to_bv 64 q) mem rom).
Proof.
intros fs regs mem rom p q wz rd rs imm base a v Hc He Hd Hrd Hq Hrs Ha HM Hv.
rewrite (step_ld rsegs regs (Z_to_bv 64 p) mem rom (Z_to_bv 32 wz) rd rs imm (hfp_bytes 8 v) (Z_to_bv 64 v)
  (pb_tbl_ok p wz Hc) He Hd).
- rewrite Hrd, Hq, hfp_addi_lit. reflexivity.
- rewrite Hrs, hfp_addi_lit, <- Ha. apply hfp_rdn8. exact HM.
- rewrite hfp_bytes_Z. change (8 * Z.of_nat 8) with 64. rewrite Z.mod_small by lia.
  symmetry. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn [Z.of_N]. lia.
Qed.

Lemma pbV_tw_addi : forall (fs : YK11.FPState) regs mem rom p q wz rd rs (imm : bv 12) (v : word),
  clookup pb_tbl p = Some wz -> is_ecall (Z_to_bv 32 wz) = false ->
  decode_any (Z_to_bv 32 wz) = Some (OpImm ALU_ADD rd rs imm, 4%Z) ->
  bv_eqb rd 0 = false -> q = p + 4 ->
  v = v_addi (getr regs rs) (bv_signed imm) ->
  RiscvSemantics.step rsegs (@mkst fs regs (Z_to_bv 64 p) mem rom) =
  MachineOk (@mkst fs (regupd regs rd v) (Z_to_bv 64 q) mem rom).
Proof.
intros fs regs mem rom p q wz rd rs imm v Hc He Hd Hrd Hq Hv.
rewrite (step_addi rsegs regs (Z_to_bv 64 p) mem rom (Z_to_bv 32 wz) rd rs imm (pb_tbl_ok p wz Hc) He Hd).
rewrite Hrd, Hq, hfp_addi_lit, Hv. reflexivity.
Qed.

Lemma pbV_auipc_lit : forall z i, v_auipc (Z_to_bv 64 z) i = Z_to_bv 64 (i + z).
Proof.
intros z i. unfold v_auipc. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 64) with (2 ^ 64). apply Zplus_mod_idemp_r.
Qed.

Lemma pbV_tw_auipc : forall (fs : YK11.FPState) regs mem rom p q wz rd (imm : bv 20) (t : Z),
  clookup pb_tbl p = Some wz -> is_ecall (Z_to_bv 32 wz) = false ->
  decode_any (Z_to_bv 32 wz) = Some (Auipc rd imm, 4%Z) ->
  bv_eqb rd 0 = false -> q = p + 4 -> Z_to_bv 64 t = Z_to_bv 64 (Z.shiftl (bv_signed imm) 12 + p) ->
  RiscvSemantics.step rsegs (@mkst fs regs (Z_to_bv 64 p) mem rom) =
  MachineOk (@mkst fs (regupd regs rd (Z_to_bv 64 t)) (Z_to_bv 64 q) mem rom).
Proof.
intros fs regs mem rom p q wz rd imm t Hc He Hd Hrd Hq Ht.
rewrite (step_auipc rsegs regs (Z_to_bv 64 p) mem rom (Z_to_bv 32 wz) rd imm (pb_tbl_ok p wz Hc) He Hd).
rewrite Hrd, Hq, hfp_addi_lit, pbV_auipc_lit, Ht. reflexivity.
Qed.

Lemma pbV_tw_jal0 : forall (fs : YK11.FPState) regs mem rom p q wz (imm : bv 21),
  clookup pb_tbl p = Some wz -> is_ecall (Z_to_bv 32 wz) = false ->
  decode_any (Z_to_bv 32 wz) = Some (Jal 0 imm, 4%Z) -> q = p + bv_signed imm ->
  RiscvSemantics.step rsegs (@mkst fs regs (Z_to_bv 64 p) mem rom) =
  MachineOk (@mkst fs regs (Z_to_bv 64 q) mem rom).
Proof.
intros fs regs mem rom p q wz imm Hc He Hd Hq.
rewrite (step_jal_x0 rsegs regs (Z_to_bv 64 p) mem rom (Z_to_bv 32 wz) imm (pb_tbl_ok p wz Hc) He Hd).
unfold btgt. rewrite hfp_addi_lit, Hq. reflexivity.
Qed.

Lemma pbV_tw_br_tk : forall (fs : YK11.FPState) regs mem rom p q wz c rs1 rs2 (imm : bv 13),
  clookup pb_tbl p = Some wz -> is_ecall (Z_to_bv 32 wz) = false ->
  decode_any (Z_to_bv 32 wz) = Some (Branch c rs1 rs2 imm, 4%Z) ->
  branch_taken c (getr regs rs1) (getr regs rs2) = true -> q = p + bv_signed imm ->
  RiscvSemantics.step rsegs (@mkst fs regs (Z_to_bv 64 p) mem rom) =
  MachineOk (@mkst fs regs (Z_to_bv 64 q) mem rom).
Proof.
intros fs regs mem rom p q wz c rs1 rs2 imm Hc He Hd Hb Hq.
rewrite (step_branch_tk_gen rsegs regs (Z_to_bv 64 p) mem rom (Z_to_bv 32 wz) c rs1 rs2 imm
  (pb_tbl_ok p wz Hc) He Hd Hb).
unfold btgt. rewrite hfp_addi_lit, Hq. reflexivity.
Qed.

Lemma pbV_tw_br_ft : forall (fs : YK11.FPState) regs mem rom p q wz c rs1 rs2 (imm : bv 13),
  clookup pb_tbl p = Some wz -> is_ecall (Z_to_bv 32 wz) = false ->
  decode_any (Z_to_bv 32 wz) = Some (Branch c rs1 rs2 imm, 4%Z) ->
  branch_taken c (getr regs rs1) (getr regs rs2) = false -> q = p + 4 ->
  RiscvSemantics.step rsegs (@mkst fs regs (Z_to_bv 64 p) mem rom) =
  MachineOk (@mkst fs regs (Z_to_bv 64 q) mem rom).
Proof.
intros fs regs mem rom p q wz c rs1 rs2 imm Hc He Hd Hb Hq.
rewrite (step_branch_ft_gen rsegs regs (Z_to_bv 64 p) mem rom (Z_to_bv 32 wz) c rs1 rs2 imm
  (pb_tbl_ok p wz Hc) He Hd Hb).
rewrite Hq, hfp_addi_lit. reflexivity.
Qed.

(* ---- register reads after a chain of writes ---- *)
Lemma pbV_getr_upd : forall regs (r r' : bv 5) v, bv_eqb r' r = false -> getr (regupd regs r v) r' = getr regs r'.
Proof.
intros regs r r' v H. unfold getr, regupd. destruct (bv_eqb r' 0); [reflexivity|].
unfold reg_get. rewrite bvmap_get_set_other; [reflexivity|].
intros E. unfold bv_eqb in H. apply Z.eqb_neq in H. apply H. rewrite E. reflexivity.
Qed.

Lemma pbV_getr_set : forall regs (r r' : bv 5) v, bv_eqb r' r = true -> bv_eqb r' 0 = false ->
  getr (regupd regs r v) r' = v.
Proof.
intros regs r r' v H H0. unfold bv_eqb in H. apply Z.eqb_eq in H. apply bv_eq in H. subst r'.
unfold getr, regupd. rewrite H0. unfold reg_get. rewrite bvmap_get_set_same. reflexivity.
Qed.

Lemma pbV_upd_z : forall (j k : bv 5) (z : Z), bv_unsigned j = z -> z <> bv_unsigned k -> bv_eqb k j = false.
Proof. intros j k z Hj Hk. unfold bv_eqb. apply Z.eqb_neq. rewrite Hj. intros E. apply Hk. symmetry. exact E. Qed.

Lemma pbV_other_z : forall (j k : bv 5) (z : Z), bv_unsigned j = z -> z <> bv_unsigned k -> bv_eqb j k = false.
Proof. intros j k z Hj Hk. unfold bv_eqb. apply Z.eqb_neq. rewrite Hj. exact Hk. Qed.

Ltac pbV_reg := repeat (rewrite pbV_getr_upd by (vm_compute; reflexivity));
  try (rewrite pbV_getr_set by (vm_compute; reflexivity)).
Ltac pbV_freg := repeat (rewrite FP.freg_get_other by (vm_compute; reflexivity));
  try (rewrite FP.freg_get_same by (vm_compute; reflexivity)).
Ltac pbV_dec := first [ (vm_compute; reflexivity) | vm_refl_bv ].

(* ---- frames of a chain of register writes, each in a small context ---- *)
Lemma pbV_gsz : forall regs (j k : bv 5) v (z : Z), bv_unsigned j = z -> z <> bv_unsigned k ->
  getr (regupd regs j v) k = getr regs k.
Proof. intros regs j k v z Hj Hk. apply pbV_getr_upd. exact (pbV_upd_z j k z Hj Hk). Qed.
Lemma pbV_fsz : forall (F : bvmap 5 word) (j k : bv 5) v (z : Z), bv_unsigned j = z -> z <> bv_unsigned k ->
  Sem.reg_get (bvmap_set j v F) k = Sem.reg_get F k.
Proof. intros F j k v z Hj Hk. apply FP.freg_get_other. exact (pbV_other_z j k z Hj Hk). Qed.
Lemma pbV_fr_A : forall regs (r : bv 5) a b, bv_unsigned r <> 10 ->
  getr (regupd (regupd regs 10 a) 10 b) r = getr regs r.
Proof.
intros regs r a b H. assert (N : 10 <> bv_unsigned r) by lia.
rewrite (pbV_gsz _ 10 r b 10 eq_refl N), (pbV_gsz _ 10 r a 10 eq_refl N). reflexivity.
Qed.
Lemma pbV_fr_ref : forall regs (r : bv 5) a b c d,
  bv_unsigned r <> 5 -> bv_unsigned r <> 14 -> bv_unsigned r <> 16 -> bv_unsigned r <> 17 ->
  getr (regupd (regupd (regupd (regupd regs 14 a) 16 b) 17 c) 5 d) r = getr regs r.
Proof.
intros regs r a b c d H5 H14 H16 H17.
assert (N5 : 5 <> bv_unsigned r) by lia. assert (N14 : 14 <> bv_unsigned r) by lia.
assert (N16 : 16 <> bv_unsigned r) by lia. assert (N17 : 17 <> bv_unsigned r) by lia.
rewrite (pbV_gsz _ 5 r d 5 eq_refl N5), (pbV_gsz _ 17 r c 17 eq_refl N17), (pbV_gsz _ 16 r b 16 eq_refl N16),
  (pbV_gsz _ 14 r a 14 eq_refl N14). reflexivity.
Qed.
Lemma pbV_fr_tail3 : forall regs (r : bv 5) a b c,
  bv_unsigned r <> 5 -> bv_unsigned r <> 16 -> bv_unsigned r <> 17 ->
  getr (regupd (regupd (regupd regs 16 a) 17 b) 5 c) r = getr regs r.
Proof.
intros regs r a b c H5 H16 H17.
assert (N5 : 5 <> bv_unsigned r) by lia. assert (N16 : 16 <> bv_unsigned r) by lia.
assert (N17 : 17 <> bv_unsigned r) by lia.
rewrite (pbV_gsz _ 5 r c 5 eq_refl N5), (pbV_gsz _ 17 r b 17 eq_refl N17), (pbV_gsz _ 16 r a 16 eq_refl N16).
reflexivity.
Qed.
Lemma pbV_fr_C6 : forall regs (r : bv 5) a1 a2 a3 a4 t w, bv_unsigned r <> 10 -> bv_unsigned r <> 12 ->
  getr (regupd (regupd (regupd (regupd (regupd (regupd regs 10 a1) 10 a2) 10 a3) 10 a4) 12 t) 10 w) r = getr regs r.
Proof.
intros regs r a1 a2 a3 a4 t w H10 H12.
assert (N10 : 10 <> bv_unsigned r) by lia. assert (N12 : 12 <> bv_unsigned r) by lia.
rewrite (pbV_gsz _ 10 r w 10 eq_refl N10), (pbV_gsz _ 12 r t 12 eq_refl N12), (pbV_gsz _ 10 r a4 10 eq_refl N10),
  (pbV_gsz _ 10 r a3 10 eq_refl N10), (pbV_gsz _ 10 r a2 10 eq_refl N10), (pbV_gsz _ 10 r a1 10 eq_refl N10).
reflexivity.
Qed.
Lemma pbV_fr_dec : forall regs (r : bv 5) a b, bv_unsigned r <> 10 -> bv_unsigned r <> 12 ->
  getr (regupd (regupd regs 10 a) 12 b) r = getr regs r.
Proof.
intros regs r a b H10 H12.
assert (N10 : 10 <> bv_unsigned r) by lia. assert (N12 : 12 <> bv_unsigned r) by lia.
rewrite (pbV_gsz _ 12 r b 12 eq_refl N12), (pbV_gsz _ 10 r a 10 eq_refl N10). reflexivity.
Qed.
Lemma pbV_ff_A : forall (F : bvmap 5 word) (k : bv 5) v1 v2 v3 v4, bv_unsigned k <> 14 -> bv_unsigned k <> 15 ->
  Sem.reg_get (bvmap_set 15 v4 (bvmap_set 15 v3 (bvmap_set 14 v2 (bvmap_set 15 v1 F)))) k = Sem.reg_get F k.
Proof.
intros F k v1 v2 v3 v4 H14 H15.
assert (N14 : 14 <> bv_unsigned k) by lia. assert (N15 : 15 <> bv_unsigned k) by lia.
rewrite (pbV_fsz _ 15 k v4 15 eq_refl N15), (pbV_fsz _ 15 k v3 15 eq_refl N15), (pbV_fsz _ 14 k v2 14 eq_refl N14),
  (pbV_fsz _ 15 k v1 15 eq_refl N15). reflexivity.
Qed.
Lemma pbV_ff_C : forall (F : bvmap 5 word) (k : bv 5) v1 v2 v3, bv_unsigned k <> 14 ->
  Sem.reg_get (bvmap_set 14 v3 (bvmap_set 14 v2 (bvmap_set 14 v1 F))) k = Sem.reg_get F k.
Proof.
intros F k v1 v2 v3 H14. assert (N14 : 14 <> bv_unsigned k) by lia.
rewrite (pbV_fsz _ 14 k v3 14 eq_refl N14), (pbV_fsz _ 14 k v2 14 eq_refl N14), (pbV_fsz _ 14 k v1 14 eq_refl N14).
reflexivity.
Qed.

(* ======================================= the double steps after FLT ======================================= *)
Definition PB_D_HALF : Z := 0x3fe0000000000000.
Definition PB_D_256 : Z := 0x4070000000000000.
Definition PB_D_CLO : Z := 0xc3e0000000000001.
Definition PB_D_CHI : Z := 0x43e0000000000000.
Definition PC_FLT : Z := 0x850ac.
Definition PC_REF : Z := 0x84ec4.
Definition PC_TAIL : Z := 0x84fa0.

Section fs.
Variable M : word -> option byte.
Local Notation ROM := (seg_rom rsegs).

(* 0x850ac .. 0x850c0: f15 = (double) f + 0.5 = rfn_d b, a0 = (+0.0 <= f15) *)
Lemma pbV_fA : forall (F : bvmap 5 word) (C : bv 32) regs (b spa : Z),
  frm_zero C -> Sem.reg_get F 8 = Z_to_bv 64 0 ->
  getr regs 2 = Z_to_bv 64 spa -> 0 <= b < 2 ^ 32 -> val_mem rsegs M (spa + 56) 4 b ->
  val_mem rsegs M 0x10380 8 PB_D_HALF ->
  exists (C' : bv 32) (G R : bvmap 5 word),
    msteps rsegs (@mkst (mkFP F C) regs (Z_to_bv 64 PC_FLT) M ROM) (@mkst (mkFP G C') R (Z_to_bv 64 0x850c4) M ROM)
    /\ frm_zero C'
    /\ (forall k : bv 5, bv_unsigned k <> 14 -> bv_unsigned k <> 15 -> Sem.reg_get G k = Sem.reg_get F k)
    /\ Sem.reg_get G 15 = ParseFP.rfn_d b
    /\ getr R 10 = (if FP.fle_d (Z_to_bv 64 0) (ParseFP.rfn_d b) then Z_to_bv 64 1 else Z_to_bv 64 0)
    /\ (forall r : bv 5, bv_unsigned r <> 10 -> getr R r = getr regs r).
Proof.
intros F C regs b spa HC H8 H2 Hb Hvb Hhalf.
set (F1 := bvmap_set 15 (nan_box (Z_to_bv 32 b)) F).
set (F2 := bvmap_set 14 (Z_to_bv 64 PB_D_HALF) F1).
set (R0 := regupd regs 10 (Z_to_bv 64 0x100b0)).
assert (S1 : RiscvSemantics.step rsegs (@mkst (mkFP F C) regs (Z_to_bv 64 0x850ac) M ROM)
  = MachineOk (@mkst (mkFP F1 C) regs (Z_to_bv 64 0x850b0) M ROM)).
{ apply (hfp_tw_flw rsegs pb_tbl pb_tbl_ok (mkFP F C) regs M ROM 0x850ac 0x850b0 58795911 15 2 56 spa (spa + 56) b);
  [ pbV_dec | pbV_dec | pbV_dec | reflexivity | exact H2 | vm_compute; reflexivity | exact Hb | exact Hvb ]. }
assert (S2 : RiscvSemantics.step rsegs (@mkst (mkFP F1 C) regs (Z_to_bv 64 0x850b0) M ROM)
  = MachineOk (@mkst (mkFP F1 C) R0 (Z_to_bv 64 0x850b4) M ROM)).
{ apply (pbV_tw_auipc (mkFP F1 C) regs M ROM 0x850b0 0x850b4 4294489367 10 1048459 0x100b0);
  [ pbV_dec | pbV_dec | pbV_dec | pbV_dec | reflexivity | vm_compute; reflexivity ]. }
assert (S3 : RiscvSemantics.step rsegs (@mkst (mkFP F1 C) R0 (Z_to_bv 64 0x850b4) M ROM)
  = MachineOk (@mkst (mkFP F2 C) R0 (Z_to_bv 64 0x850b8) M ROM)).
{ apply (hfp_tw_fld rsegs pb_tbl pb_tbl_ok (mkFP F1 C) R0 M ROM 0x850b4 0x850b8 755316487 14 10 720 0x100b0 0x10380
    PB_D_HALF);
  [ pbV_dec | pbV_dec | pbV_dec | reflexivity | unfold R0; apply pbV_getr_set; vm_compute; reflexivity
  | vm_compute; reflexivity | unfold PB_D_HALF; lia | exact Hhalf ]. }
destruct (hfp_tw_fcvt_d_s rsegs pb_tbl pb_tbl_ok F2 C R0 M ROM 0x850b8 0x850bc 1107789779 15 15 0
  (nan_box (Z_to_bv 32 b)) ltac:(pbV_dec) ltac:(pbV_dec) ltac:(pbV_dec) ltac:(vm_compute; reflexivity) eq_refl
  ltac:(unfold F2, F1; pbV_freg; reflexivity) HC) as (C1 & S4 & HC1).
set (F3 := bvmap_set 15 (FP.fcvt_d_s RNE (nan_box (Z_to_bv 32 b))) F2) in S4.
destruct (hfp_tw_fadd_d rsegs pb_tbl pb_tbl_ok F3 C1 R0 M ROM 0x850bc 0x850c0 48756691 15 15 14 7
  (FP.fcvt_d_s RNE (nan_box (Z_to_bv 32 b))) (Z_to_bv 64 PB_D_HALF)
  ltac:(pbV_dec) ltac:(pbV_dec) ltac:(pbV_dec) ltac:(vm_compute; reflexivity) eq_refl
  ltac:(unfold F3; pbV_freg; reflexivity) ltac:(unfold F3, F2; pbV_freg; reflexivity) HC1) as (C2 & S5 & HC2).
unfold PB_D_HALF in S5. rewrite (hfp_rfn_d b) in S5.
set (F4 := bvmap_set 15 (ParseFP.rfn_d b) F3) in S5.
destruct (hfp_tw_fle_d rsegs pb_tbl pb_tbl_ok F4 C2 R0 M ROM 0x850c0 0x850c4 2733901139 10 8 15
  (Z_to_bv 64 0) (ParseFP.rfn_d b)
  ltac:(pbV_dec) ltac:(pbV_dec) ltac:(pbV_dec) ltac:(vm_compute; reflexivity) eq_refl
  ltac:(unfold F4, F3, F2, F1; pbV_freg; exact H8) ltac:(unfold F4; pbV_freg; reflexivity) HC2) as (C3 & S6 & HC3).
exists C3, F4, (regupd R0 10 (if FP.fle_d (Z_to_bv 64 0) (ParseFP.rfn_d b) then Z_to_bv 64 1 else Z_to_bv 64 0)).
split; [|split; [exact HC3 | split; [|split; [|split]]]].
- eapply mst_step; [reflexivity | exact S1 | ].
  eapply mst_step; [reflexivity | exact S2 | ].
  eapply mst_step; [reflexivity | exact S3 | ].
  eapply mst_step; [reflexivity | exact S4 | ].
  eapply mst_step; [reflexivity | exact S5 | ].
  eapply mst_step; [reflexivity | exact S6 | ].
  apply mst_refl.
- intros k H14 H15. exact (pbV_ff_A F k _ _ _ _ H14 H15).
- exact (FP.freg_get_same _ 15 15 _ eq_refl).
- apply pbV_getr_set; vm_compute; reflexivity.
- intros r Hr. exact (pbV_fr_A regs r _ _ Hr).
Qed.

(* 0x85118 .. 0x85128: a4 = [spa + 40], a6 = 8, a7 = [spa + 48], t0 = 5, j REF *)
Lemma pbV_fRef : forall (fs : YK11.FPState) regs (spa a4v shv : Z),
  getr regs 2 = Z_to_bv 64 spa ->
  val_mem rsegs M (spa + 40) 8 a4v -> 0 <= a4v < 2 ^ 64 -> val_mem rsegs M (spa + 48) 8 shv -> 0 <= shv < 2 ^ 64 ->
  exists R : bvmap 5 word,
    msteps rsegs (@mkst fs regs (Z_to_bv 64 0x85118) M ROM) (@mkst fs R (Z_to_bv 64 PC_REF) M ROM)
    /\ getr R 14 = Z_to_bv 64 a4v /\ getr R 16 = Z_to_bv 64 8 /\ getr R 17 = Z_to_bv 64 shv
    /\ getr R 5 = Z_to_bv 64 5
    /\ (forall r : bv 5, bv_unsigned r <> 5 -> bv_unsigned r <> 14 -> bv_unsigned r <> 16 -> bv_unsigned r <> 17 ->
          getr R r = getr regs r).
Proof.
intros fs regs spa a4v shv H2 H40 R40 H48 R48.
set (R1 := regupd regs 14 (Z_to_bv 64 a4v)).
set (R2 := regupd R1 16 (Z_to_bv 64 8)).
set (R3 := regupd R2 17 (Z_to_bv 64 shv)).
set (R4 := regupd R3 5 (Z_to_bv 64 5)).
exists R4. split; [|split; [|split; [|split; [|split]]]].
- eapply mst_step; [reflexivity | | ].
  { apply (pbV_tw_ld fs regs M ROM 0x85118 0x8511c 42022659 14 2 40 spa (spa + 40) a4v);
    [ pbV_dec | pbV_dec | pbV_dec | pbV_dec | reflexivity | exact H2 | vm_compute; reflexivity | exact H40 | exact R40 ]. }
  eapply mst_step; [reflexivity | | ].
  { apply (pbV_tw_addi fs R1 M ROM 0x8511c 0x85120 8390675 16 0 8 (Z_to_bv 64 8));
    [ pbV_dec | pbV_dec | pbV_dec | pbV_dec | reflexivity | ].
    rewrite getr_zero, hfp_addi_lit. reflexivity. }
  eapply mst_step; [reflexivity | | ].
  { apply (pbV_tw_ld fs R2 M ROM 0x85120 0x85124 50411651 17 2 48 spa (spa + 48) shv);
    [ pbV_dec | pbV_dec | pbV_dec | pbV_dec | reflexivity | | vm_compute; reflexivity | exact H48 | exact R48 ].
    unfold R2, R1. pbV_reg. exact H2. }
  eapply mst_step; [reflexivity | | ].
  { apply (pbV_tw_addi fs R3 M ROM 0x85124 0x85128 5243539 5 0 5 (Z_to_bv 64 5));
    [ pbV_dec | pbV_dec | pbV_dec | pbV_dec | reflexivity | ].
    rewrite getr_zero, hfp_addi_lit. reflexivity. }
  eapply mst_step; [reflexivity | | apply mst_refl].
  { unfold PC_REF. apply (pbV_tw_jal0 fs R4 M ROM 0x85128 0x84ec4 3655331951 2096540);
    [ pbV_dec | pbV_dec | pbV_dec | vm_compute; reflexivity ]. }
- unfold R4, R3, R2, R1. pbV_reg. reflexivity.
- unfold R4, R3, R2, R1. pbV_reg. reflexivity.
- unfold R4, R3, R2, R1. pbV_reg. reflexivity.
- unfold R4, R3, R2, R1. pbV_reg. reflexivity.
- intros r H5 H14 H16 H17. exact (pbV_fr_ref regs r _ _ _ _ H5 H14 H16 H17).
Qed.

(* 0x850c4 with a0 = 0 (+0.0 <= d fails): beqz to 0x85118 *)
Lemma pbV_fA_ref : forall (fs : YK11.FPState) regs,
  getr regs 10 = Z_to_bv 64 0 ->
  RiscvSemantics.step rsegs (@mkst fs regs (Z_to_bv 64 0x850c4) M ROM) =
  MachineOk (@mkst fs regs (Z_to_bv 64 0x85118) M ROM).
Proof.
intros fs regs H10.
apply (pbV_tw_br_tk fs regs M ROM 0x850c4 0x85118 67439203 BC_EQ 10 0 84);
  [ pbV_dec | pbV_dec | pbV_dec | | vm_compute; reflexivity ].
rewrite H10, getr_zero. reflexivity.
Qed.

(* 0x850c4 with a0 = 1, then 0x850c8 .. 0x850d0: f14 = 256.0, a0 = (d < 256.0) *)
Lemma pbV_fB : forall (F : bvmap 5 word) (C : bv 32) regs (b : Z),
  frm_zero C -> Sem.reg_get F 15 = ParseFP.rfn_d b -> getr regs 10 = Z_to_bv 64 1 ->
  val_mem rsegs M 0x10340 8 PB_D_256 ->
  exists (C' : bv 32) (R : bvmap 5 word),
    msteps rsegs (@mkst (mkFP F C) regs (Z_to_bv 64 0x850c4) M ROM)
      (@mkst (mkFP (bvmap_set 14 (Z_to_bv 64 PB_D_256) F) C') R (Z_to_bv 64 0x850d4) M ROM)
    /\ frm_zero C'
    /\ getr R 10 = (if FP.flt_d (ParseFP.rfn_d b) (Z_to_bv 64 PB_D_256) then Z_to_bv 64 1 else Z_to_bv 64 0)
    /\ (forall r : bv 5, bv_unsigned r <> 10 -> getr R r = getr regs r).
Proof.
intros F C regs b HC H15 H10 H256.
set (R0 := regupd regs 10 (Z_to_bv 64 0x100c8)).
destruct (hfp_tw_flt_d rsegs pb_tbl pb_tbl_ok (bvmap_set 14 (Z_to_bv 64 PB_D_256) F) C R0 M ROM 0x850d0 0x850d4
  2733086035 10 15 14 (ParseFP.rfn_d b) (Z_to_bv 64 PB_D_256)
  ltac:(pbV_dec) ltac:(pbV_dec) ltac:(pbV_dec) ltac:(vm_compute; reflexivity) eq_refl
  ltac:(pbV_freg; exact H15) ltac:(pbV_freg; reflexivity) HC) as (C1 & S4 & HC1).
exists C1, (regupd R0 10 (if FP.flt_d (ParseFP.rfn_d b) (Z_to_bv 64 PB_D_256) then Z_to_bv 64 1 else Z_to_bv 64 0)).
split; [|split; [exact HC1 | split]].
- eapply mst_step; [reflexivity | | ].
  { apply (pbV_tw_br_ft (mkFP F C) regs M ROM 0x850c4 0x850c8 67439203 BC_EQ 10 0 84);
    [ pbV_dec | pbV_dec | pbV_dec | | reflexivity ].
    rewrite H10, getr_zero. reflexivity. }
  eapply mst_step; [reflexivity | | ].
  { apply (pbV_tw_auipc (mkFP F C) regs M ROM 0x850c8 0x850cc 4294489367 10 1048459 0x100c8);
    [ pbV_dec | pbV_dec | pbV_dec | pbV_dec | reflexivity | vm_compute; reflexivity ]. }
  eapply mst_step; [reflexivity | | ].
  { apply (hfp_tw_fld rsegs pb_tbl pb_tbl_ok (mkFP F C) R0 M ROM 0x850cc 0x850d0 663041799 14 10 632 0x100c8 0x10340
      PB_D_256);
    [ pbV_dec | pbV_dec | pbV_dec | reflexivity | unfold R0; apply pbV_getr_set; vm_compute; reflexivity
    | vm_compute; reflexivity | unfold PB_D_256; lia | exact H256 ]. }
  eapply mst_step; [reflexivity | exact S4 | apply mst_refl].
- apply pbV_getr_set; vm_compute; reflexivity.
- intros r Hr. exact (pbV_fr_A regs r _ _ Hr).
Qed.

(* 0x850d4 with a0 = 0 (d < 256.0 fails): beqz to 0x85118 *)
Lemma pbV_fB_ref : forall (fs : YK11.FPState) regs,
  getr regs 10 = Z_to_bv 64 0 ->
  RiscvSemantics.step rsegs (@mkst fs regs (Z_to_bv 64 0x850d4) M ROM) =
  MachineOk (@mkst fs regs (Z_to_bv 64 0x85118) M ROM).
Proof.
intros fs regs H10.
apply (pbV_tw_br_tk fs regs M ROM 0x850d4 0x85118 67437155 BC_EQ 10 0 68);
  [ pbV_dec | pbV_dec | pbV_dec | | vm_compute; reflexivity ].
rewrite H10, getr_zero. reflexivity.
Qed.

(* 0x850d4 with a0 = 1, the range test passed: the two cast checks (not taken), t = fcvt.l.d rtz d, the floor
   (r = t - 1 when d < (double) t, the check 0x8510c not taken), then 0x84f94 .. 0x84f9c: TAIL with a2 = r. Stated
   over any double d and its conversion t, so that no step unfolds the binary64 arithmetic. *)
Lemma pbV_fC : forall (F : bvmap 5 word) (C : bv 32) regs (d t : word) (spa shv : Z),
  frm_zero C -> Sem.reg_get F 15 = d -> getr regs 10 = Z_to_bv 64 1 ->
  FP.flt_d (Z_to_bv 64 PB_D_CLO) d = true -> FP.flt_d d (Z_to_bv 64 PB_D_CHI) = true ->
  FP.fcvt_l_d RTZ d = t -> - 2 ^ 63 < bv_signed t < 2 ^ 63 ->
  getr regs 2 = Z_to_bv 64 spa -> val_mem rsegs M (spa + 48) 8 shv -> 0 <= shv < 2 ^ 64 ->
  val_mem rsegs M 0x103f0 8 PB_D_CLO -> val_mem rsegs M 0x10358 8 PB_D_CHI ->
  exists (C' : bv 32) (G R : bvmap 5 word),
    msteps rsegs (@mkst (mkFP F C) regs (Z_to_bv 64 0x850d4) M ROM) (@mkst (mkFP G C') R (Z_to_bv 64 PC_TAIL) M ROM)
    /\ frm_zero C'
    /\ (forall k : bv 5, bv_unsigned k <> 14 -> Sem.reg_get G k = Sem.reg_get F k)
    /\ getr R 12 = Z_to_bv 64 (if FP.flt_d d (FP.fcvt_d_l RNE t) then bv_signed t - 1 else bv_signed t)
    /\ getr R 16 = Z_to_bv 64 8 /\ getr R 17 = Z_to_bv 64 shv /\ getr R 5 = Z_to_bv 64 5
    /\ (forall r : bv 5, bv_unsigned r <> 5 -> bv_unsigned r <> 10 -> bv_unsigned r <> 12 -> bv_unsigned r <> 16 ->
          bv_unsigned r <> 17 -> getr R r = getr regs r).
Proof.
intros F C regs d t spa shv HC H15 H10 CLO CHI Et TS H2 H48 R48 Hclo Hchi.
set (FA := bvmap_set 14 (Z_to_bv 64 PB_D_CLO) F).
set (FB := bvmap_set 14 (Z_to_bv 64 PB_D_CHI) FA).
set (R1 := regupd regs 10 (Z_to_bv 64 0x100d8)).
destruct (hfp_tw_flt_d rsegs pb_tbl pb_tbl_ok FA C R1 M ROM 0x850e0 0x850e4 2734101843 10 14 15
  (Z_to_bv 64 PB_D_CLO) d ltac:(pbV_dec) ltac:(pbV_dec) ltac:(pbV_dec) ltac:(vm_compute; reflexivity) eq_refl
  ltac:(unfold FA; pbV_freg; reflexivity) ltac:(unfold FA; pbV_freg; exact H15) HC) as (C1 & S4 & HC1).
rewrite CLO in S4.
set (R2 := regupd R1 10 (Z_to_bv 64 1)) in S4.
set (R3 := regupd R2 10 (Z_to_bv 64 0x100e8)).
destruct (hfp_tw_flt_d rsegs pb_tbl pb_tbl_ok FB C1 R3 M ROM 0x850f0 0x850f4 2733086035 10 15 14
  d (Z_to_bv 64 PB_D_CHI) ltac:(pbV_dec) ltac:(pbV_dec) ltac:(pbV_dec) ltac:(vm_compute; reflexivity) eq_refl
  ltac:(unfold FB, FA; pbV_freg; exact H15) ltac:(unfold FB; pbV_freg; reflexivity) HC1) as (C2 & S8 & HC2).
rewrite CHI in S8.
set (R4 := regupd R3 10 (Z_to_bv 64 1)) in S8.
destruct (hfp_tw_fcvt_l_d rsegs pb_tbl pb_tbl_ok FB C2 R4 M ROM 0x850f8 0x850fc 3257374291 12 15 1 d
  ltac:(pbV_dec) ltac:(pbV_dec) ltac:(pbV_dec) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl
  ltac:(unfold FB, FA; pbV_freg; exact H15) HC2) as (C3 & S10 & HC3).
rewrite Et in S10.
set (R5 := regupd R4 12 t) in S10.
destruct (hfp_tw_fcvt_d_l rsegs pb_tbl pb_tbl_ok FB C3 R5 M ROM 0x850fc 0x85100 3525736275 14 12 7 t
  ltac:(pbV_dec) ltac:(pbV_dec) ltac:(pbV_dec) ltac:(vm_compute; reflexivity) eq_refl
  ltac:(unfold R5; apply pbV_getr_set; vm_compute; reflexivity) HC3) as (C4 & S11 & HC4).
set (FC := bvmap_set 14 (FP.fcvt_d_l RNE t) FB) in S11.
destruct (hfp_tw_flt_d rsegs pb_tbl pb_tbl_ok FC C4 R5 M ROM 0x85100 0x85104 2733086035 10 15 14
  d (FP.fcvt_d_l RNE t) ltac:(pbV_dec) ltac:(pbV_dec) ltac:(pbV_dec) ltac:(vm_compute; reflexivity) eq_refl
  ltac:(unfold FC, FB, FA; pbV_freg; exact H15) ltac:(unfold FC; pbV_freg; reflexivity) HC4) as (C5 & S12 & HC5).
remember (if FP.flt_d d (FP.fcvt_d_l RNE t) then Z_to_bv 64 1 else Z_to_bv 64 0) as w10 eqn:Ew in S12.
(* the head of the path, 0x850d4 .. 0x85104 *)
assert (P1 : msteps rsegs (@mkst (mkFP F C) regs (Z_to_bv 64 0x850d4) M ROM)
  (@mkst (mkFP FC C5) (regupd R5 10 w10) (Z_to_bv 64 0x85104) M ROM)).
{ eapply mst_step; [reflexivity | | ].
  { apply (pbV_tw_br_ft (mkFP F C) regs M ROM 0x850d4 0x850d8 67437155 BC_EQ 10 0 68);
    [ pbV_dec | pbV_dec | pbV_dec | | reflexivity ].
    rewrite H10, getr_zero. reflexivity. }
  eapply mst_step; [reflexivity | | ].
  { apply (pbV_tw_auipc (mkFP F C) regs M ROM 0x850d8 0x850dc 4294489367 10 1048459 0x100d8);
    [ pbV_dec | pbV_dec | pbV_dec | pbV_dec | reflexivity | vm_compute; reflexivity ]. }
  eapply mst_step; [reflexivity | | ].
  { apply (hfp_tw_fld rsegs pb_tbl pb_tbl_ok (mkFP F C) R1 M ROM 0x850dc 0x850e0 830813959 14 10 792 0x100d8 0x103f0
      PB_D_CLO);
    [ pbV_dec | pbV_dec | pbV_dec | reflexivity | unfold R1; apply pbV_getr_set; vm_compute; reflexivity
    | vm_compute; reflexivity | unfold PB_D_CLO; lia | exact Hclo ]. }
  eapply mst_step; [reflexivity | exact S4 | ].
  eapply mst_step; [reflexivity | | ].
  { apply (pbV_tw_br_ft (mkFP FA C1) R2 M ROM 0x850e4 0x850e8 402982499 BC_EQ 10 0 396);
    [ pbV_dec | pbV_dec | pbV_dec | | reflexivity ].
    unfold R2. rewrite pbV_getr_set by (vm_compute; reflexivity). rewrite getr_zero. reflexivity. }
  eapply mst_step; [reflexivity | | ].
  { apply (pbV_tw_auipc (mkFP FA C1) R2 M ROM 0x850e8 0x850ec 4294489367 10 1048459 0x100e8);
    [ pbV_dec | pbV_dec | pbV_dec | pbV_dec | reflexivity | vm_compute; reflexivity ]. }
  eapply mst_step; [reflexivity | | ].
  { apply (hfp_tw_fld rsegs pb_tbl pb_tbl_ok (mkFP FA C1) R3 M ROM 0x850ec 0x850f0 654653191 14 10 624 0x100e8 0x10358
      PB_D_CHI);
    [ pbV_dec | pbV_dec | pbV_dec | reflexivity | unfold R3; apply pbV_getr_set; vm_compute; reflexivity
    | vm_compute; reflexivity | unfold PB_D_CHI; lia | exact Hchi ]. }
  eapply mst_step; [reflexivity | exact S8 | ].
  eapply mst_step; [reflexivity | | ].
  { apply (pbV_tw_br_ft (mkFP FB C2) R4 M ROM 0x850f4 0x850f8 369430115 BC_EQ 10 0 380);
    [ pbV_dec | pbV_dec | pbV_dec | | reflexivity ].
    unfold R4. rewrite pbV_getr_set by (vm_compute; reflexivity). rewrite getr_zero. reflexivity. }
  eapply mst_step; [reflexivity | exact S10 | ].
  eapply mst_step; [reflexivity | exact S11 | ].
  eapply mst_step; [reflexivity | exact S12 | ].
  apply mst_refl. }
(* 0x84f94 .. 0x84f9c from any register file R7 *)
assert (P3 : forall (C7 : bv 32) (R7 : bvmap 5 word), getr R7 2 = Z_to_bv 64 spa ->
  msteps rsegs (@mkst (mkFP FC C7) R7 (Z_to_bv 64 0x84f94) M ROM)
    (@mkst (mkFP FC C7) (regupd (regupd (regupd R7 16 (Z_to_bv 64 8)) 17 (Z_to_bv 64 shv)) 5 (Z_to_bv 64 5))
       (Z_to_bv 64 PC_TAIL) M ROM)).
{ intros C7 R7 H7.
  eapply mst_step; [reflexivity | | ].
  { apply (pbV_tw_addi (mkFP FC C7) R7 M ROM 0x84f94 0x84f98 8390675 16 0 8 (Z_to_bv 64 8));
    [ pbV_dec | pbV_dec | pbV_dec | pbV_dec | reflexivity | ].
    rewrite getr_zero, hfp_addi_lit. reflexivity. }
  eapply mst_step; [reflexivity | | ].
  { apply (pbV_tw_ld (mkFP FC C7) (regupd R7 16 (Z_to_bv 64 8)) M ROM 0x84f98 0x84f9c 50411651 17 2 48 spa (spa + 48) shv);
    [ pbV_dec | pbV_dec | pbV_dec | pbV_dec | reflexivity | | vm_compute; reflexivity | exact H48 | exact R48 ].
    pbV_reg. exact H7. }
  eapply mst_step; [reflexivity | | apply mst_refl].
  { unfold PC_TAIL. apply (pbV_tw_addi (mkFP FC C7) (regupd (regupd R7 16 (Z_to_bv 64 8)) 17 (Z_to_bv 64 shv)) M ROM
      0x84f9c 0x84fa0 5243539 5 0 5 (Z_to_bv 64 5));
    [ pbV_dec | pbV_dec | pbV_dec | pbV_dec | reflexivity | ].
    rewrite getr_zero, hfp_addi_lit. reflexivity. } }
assert (G2 : forall R7 : bvmap 5 word, (forall r : bv 5, bv_unsigned r <> 10 -> bv_unsigned r <> 12 -> getr R7 r = getr regs r) ->
  getr R7 2 = Z_to_bv 64 spa) by (intros R7 HR7; rewrite HR7 by (vm_compute; lia); exact H2).
assert (HR6 : forall r : bv 5, bv_unsigned r <> 10 -> bv_unsigned r <> 12 -> getr (regupd R5 10 w10) r = getr regs r).
{ intros r Hr10 Hr12. exact (pbV_fr_C6 regs r _ _ _ _ _ _ Hr10 Hr12). }
assert (HG : forall k : bv 5, bv_unsigned k <> 14 -> Sem.reg_get FC k = Sem.reg_get F k).
{ intros k Hk. exact (pbV_ff_C F k _ _ _ Hk). }
destruct (FP.flt_d d (FP.fcvt_d_l RNE t)) eqn:Efl.
- (* d < (double) t: a2 = t - 1 *)
  set (R8 := regupd (regupd (regupd R5 10 w10) 10 (Z_to_bv 64 (bv_signed t - 1))) 12 (Z_to_bv 64 (bv_signed t - 1))).
  assert (P2 : msteps rsegs (@mkst (mkFP FC C5) (regupd R5 10 w10) (Z_to_bv 64 0x85104) M ROM)
    (@mkst (mkFP FC C5) R8 (Z_to_bv 64 0x84f94) M ROM)).
  { eapply mst_step; [reflexivity | | ].
    { apply (pbV_tw_br_ft (mkFP FC C5) (regupd R5 10 w10) M ROM 0x85104 0x85108 3892644067 BC_EQ 10 0 7824);
      [ pbV_dec | pbV_dec | pbV_dec | | reflexivity ].
      rewrite pbV_getr_set by (vm_compute; reflexivity). rewrite Ew. try rewrite Efl. rewrite getr_zero. reflexivity. }
    eapply mst_step; [reflexivity | | ].
    { apply (pbV_tw_addi (mkFP FC C5) (regupd R5 10 w10) M ROM 0x85108 0x8510c 4294313235 10 12 4095
        (Z_to_bv 64 (bv_signed t - 1)));
      [ pbV_dec | pbV_dec | pbV_dec | pbV_dec | reflexivity | ].
      pbV_reg. unfold R5. rewrite pbV_getr_set by (vm_compute; reflexivity).
      change (bv_signed (4095%bv : bv 12)) with (-1). symmetry. apply hfp_dec_lit. }
    eapply mst_step; [reflexivity | | ].
    { apply (pbV_tw_br_ft (mkFP FC C5) (regupd (regupd R5 10 w10) 10 (Z_to_bv 64 (bv_signed t - 1))) M ROM 0x8510c
        0x85110 382030435 BC_GE 10 12 356); [ pbV_dec | pbV_dec | pbV_dec | | reflexivity ].
      rewrite pbV_getr_set by (vm_compute; reflexivity). pbV_reg. unfold R5.
      rewrite pbV_getr_set by (vm_compute; reflexivity). rewrite <- hfp_dec_lit. apply hfp_bge_dec. exact TS. }
    eapply mst_step; [reflexivity | | ].
    { apply (pbV_tw_addi (mkFP FC C5) (regupd (regupd R5 10 w10) 10 (Z_to_bv 64 (bv_signed t - 1))) M ROM 0x85110
        0x85114 329235 12 10 0 (Z_to_bv 64 (bv_signed t - 1))); [ pbV_dec | pbV_dec | pbV_dec | pbV_dec | reflexivity | ].
      rewrite pbV_getr_set by (vm_compute; reflexivity). rewrite hfp_addi_lit.
      change (bv_signed (0%bv : bv 12)) with 0. rewrite Z.add_0_r. reflexivity. }
    eapply mst_step; [reflexivity | | apply mst_refl].
    { apply (pbV_tw_jal0 (mkFP FC C5) R8 M ROM 0x85114 0x84f94 3894407279 2096768);
      [ pbV_dec | pbV_dec | pbV_dec | vm_compute; reflexivity ]. } }
  assert (HR8 : forall r : bv 5, bv_unsigned r <> 10 -> bv_unsigned r <> 12 -> getr R8 r = getr regs r).
  { intros r Hr10 Hr12. unfold R8. rewrite (pbV_fr_dec _ r _ _ Hr10 Hr12). apply HR6; assumption. }
  exists C5, FC, (regupd (regupd (regupd R8 16 (Z_to_bv 64 8)) 17 (Z_to_bv 64 shv)) 5 (Z_to_bv 64 5)).
  split; [|split; [exact HC5 | split; [exact HG | split; [|split; [|split; [|split; [|]]]]]]].
  + eapply msteps_trans; [exact P1|]. eapply msteps_trans; [exact P2|]. apply P3. apply G2. exact HR8.
  + pbV_reg. unfold R8. rewrite pbV_getr_set by (vm_compute; reflexivity). reflexivity.
  + pbV_reg. reflexivity.
  + pbV_reg. reflexivity.
  + pbV_reg. reflexivity.
  + intros r H5 H10' H12 H16 H17. rewrite (pbV_fr_tail3 _ r _ _ _ H5 H16 H17). apply HR8; assumption.
- (* d >= (double) t: a2 = t *)
  assert (P2 : msteps rsegs (@mkst (mkFP FC C5) (regupd R5 10 w10) (Z_to_bv 64 0x85104) M ROM)
    (@mkst (mkFP FC C5) (regupd R5 10 w10) (Z_to_bv 64 0x84f94) M ROM)).
  { eapply mst_step; [reflexivity | | apply mst_refl].
    apply (pbV_tw_br_tk (mkFP FC C5) (regupd R5 10 w10) M ROM 0x85104 0x84f94 3892644067 BC_EQ 10 0 7824);
      [ pbV_dec | pbV_dec | pbV_dec | | vm_compute; reflexivity ].
    rewrite pbV_getr_set by (vm_compute; reflexivity). rewrite Ew. try rewrite Efl. rewrite getr_zero. reflexivity. }
  exists C5, FC, (regupd (regupd (regupd (regupd R5 10 w10) 16 (Z_to_bv 64 8)) 17 (Z_to_bv 64 shv)) 5 (Z_to_bv 64 5)).
  split; [|split; [exact HC5 | split; [exact HG | split; [|split; [|split; [|split; [|]]]]]]].
  + eapply msteps_trans; [exact P1|]. eapply msteps_trans; [exact P2|]. apply P3. apply G2. exact HR6.
  + pbV_reg. unfold R5. rewrite pbV_getr_set by (vm_compute; reflexivity). symmetry. apply hfp_lit_signed.
  + pbV_reg. reflexivity.
  + pbV_reg. reflexivity.
  + pbV_reg. reflexivity.
  + intros r H5 H10' H12 H16 H17. rewrite (pbV_fr_tail3 _ r _ _ _ H5 H16 H17). apply HR6; assumption.
Qed.
End fs.

(* ======================================= the engine's states ======================================= *)
(* every entry state is over lib/A/HPgParseGKit.v's env hk_env x regs L (slots 0 .. 31 the registers at the cut, 32
   the shadow base, 33 .. 46 the saved words, 47 .. the segment's own values L) *)
(* a7 = the shadow address of s7 (0x84cdc srli a7,s7,3; add a7,a7,s11) *)
Definition pbV_s7sh : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 23 0) (SLit 3)) (SOff 27 0).
(* the out cell's address s3 + s4 + 2 s4 (0x84fc8 .. 0x84fd0) *)
Definition pbV_oal : sv := SAlu ALU_ADD (SAlu ALU_ADD (SOff 19 0) (SOff 20 0)) (SAlu ALU_SLL (SOff 20 0) (SLit 1)).
(* the frame temporaries the segment reads: [spa + 16] = 3, [spa + 24] = keys + 1, [spa + 32] = rf,
   [spa + 40] = P + r + 16, [spa + 48] = the shadow address of s7 *)
Definition pbV_tcs (rfa k1a b40a : nat) : list YP09.chunk :=
[YP09.mkChunk 16 (CVal 8 (SLit 3)); YP09.mkChunk 24 (CVal 8 (SOff k1a 0)); YP09.mkChunk 32 (CVal 8 (SOff rfa 0));
 YP09.mkChunk 40 (CVal 8 (SOff b40a 0)); YP09.mkChunk 48 (CVal 8 pbV_s7sh)].
(* the child at s7: its size (atom 47), its type (48) and, when the size is >= 4, its 4 value bytes (49) *)
Definition pbV_podr (big : bool) : YP09.region :=
YP09.mkRegion (Some 23%nat) 0 (if big then 12 else 8) 0 0
([YP09.mkChunk 0 (CVal 4 (SOff 47 0)); YP09.mkChunk 4 (CVal 4 (SOff 48 0))] ++
 if big then [YP09.mkChunk 8 (CVal 4 (SOff 49 0))] else []).
(* VAL 0x84f0c: L = CS, type, the value word, rf, keys + 1, P + r + 16 (atoms 47 .. 52) *)
Definition pbV_ssV (big : bool) : sstate :=
mkSS PC_VAL (sr_set sr_atoms (17%bv : bv 5) pbV_s7sh) [hk_temps (pbV_tcs 50 51 52); pbV_podr big] None
(mkFacts (hk_atoms ++ [(23%nat, mkAF 16 (2 ^ 47 - 16) 3); (47%nat, if big then mkAF 4 (2 ^ 32 - 1) 0 else mkAF 0 3 0);
  (48%nat, mkAF 0 (2 ^ 32 - 1) 0); (49%nat, mkAF 0 (2 ^ 32 - 1) 0); (50%nat, mkAF 0 5 0)]) [] []).
Definition pbV_shV (big : bool) : list shent := [mkSHE 23 0 (if big then 12 else 8)].
(* REF 0x84ec4 and TAIL 0x84fa0: L = rf, keys + 1, P + r + 16 (atoms 47 .. 49) *)
Definition pbV_ssR : sstate :=
mkSS PC_REF sr_atoms [hk_temps (pbV_tcs 47 48 49)] None (mkFacts (hk_atoms ++ [(47%nat, mkAF 0 5 0)]) [] []).
Definition pbV_ssT (a1 : Z) : sstate :=
mkSS PC_TAIL sr_atoms [hk_temps (pbV_tcs 47 48 49)] None
(mkFacts (hk_atoms ++ [(11%nat, mkAF a1 a1 0); (12%nat, mkAF 0 255 0); (18%nat, mkAF 0 9 0); (20%nat, mkAF 0 9 0)])
  [] []).
(* CELL 0x84fc4 (n < cap, the value in range): L = rf, keys + 1, P + r + 16, out + 3 n (atoms 47 .. 50); the out
   cell's 3 bytes a writable region at atom 50, with its shadow entry *)
Definition PC_CELL : Z := 0x84fc4.
Definition pbV_outr : YP09.region := YP09.mkRegion (Some 50%nat) 0 3 0 3 [].
Definition pbV_ssC : sstate :=
mkSS PC_CELL sr_atoms [hk_temps (pbV_tcs 47 48 49); pbV_outr] None
(mkFacts (hk_atoms ++ [(19%nat, mkAF 4096 0x7fffff800000 4); (20%nat, mkAF 0 8 0);
  (50%nat, mkAF 4096 (0x7fffff800000 - 3) 0)]) [] [(pbV_oal, SOff 50 0)]).
Definition pbV_shC : list shent := [mkSHE 50 0 3].

(* ---- the engine's values ---- *)
Lemma pbV_U_s7sh : forall E a, ew E 23 = Z_to_bv 64 a -> ew E 27 = Z_to_bv 64 SHADOW_OFF -> 0 <= a < 2 ^ 47 ->
  U E pbV_s7sh = shadow_addr a.
Proof.
intros E a H23 H27 Ha.
assert (U23 : U E (SOff 23 0) = a) by (apply U_atom; [exact H23 | lia]).
assert (U27 : U E (SOff 27 0) = SHADOW_OFF) by (apply U_atom; [exact H27 | unfold SHADOW_OFF; lia]).
assert (U3 : U E (SLit 3) = 3) by (apply U_lit; lia).
assert (Us : U E (SAlu ALU_SRL (SOff 23 0) (SLit 3)) = a / 8).
{ rewrite hpf_U_srl by (rewrite U3; lia). rewrite U23, U3. reflexivity. }
assert (0 <= a / 8 <= a) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
unfold pbV_s7sh. rewrite hpf_U_add by (rewrite Us, U27; unfold SHADOW_OFF; lia). rewrite Us, U27.
unfold shadow_addr. lia.
Qed.

Lemma pbV_br_big : forall E (n : nat) cs, ew E n = Z_to_bv 64 cs -> 0 <= cs < 2 ^ 32 ->
  branch_taken BC_NE (sv_denot E (SAlu ALU_SRL (SOff n 0) (SLit 20))) (sv_denot E (SLit 0)) = negb (cs <? 2 ^ 20).
Proof.
intros E n cs H Hc. rewrite branch_ne_U, U_SAlu, (U_atom E n cs H) by lia. rewrite !U_SLit. cbn [zalu_raw].
change (Z.land (zcanon 20) 63) with 20. change (zcanon 0) with 0.
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 20) with 1048576.
rewrite zcanon_id by (unfold M64; split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia). f_equal.
destruct (Z.ltb_spec cs 1048576).
- apply Z.eqb_eq. apply Z.div_small. lia.
- apply Z.eqb_neq. assert (0 < cs / 1048576) by (apply Z.div_str_pos; lia). lia.
Qed.

Lemma pbV_br_ty : forall E (n : nat) ty k, ew E n = Z_to_bv 64 ty -> 0 <= ty < 2 ^ 32 -> 0 <= k < 2 ^ 31 ->
  branch_taken BC_NE (sv_denot E (SExt true 32 (SOff n 0))) (sv_denot E (SLit k)) = negb (ty =? k).
Proof.
intros E n ty k H Hty Hk. rewrite branch_ne_U. f_equal.
rewrite (U_lit E k) by lia. apply (hpf_U_sx32_eqb E (SOff n 0) ty k); [apply U_atom; [exact H | lia] | exact Hty | exact Hk].
Qed.

(* the sign-extended 32-bit word w as the engine reads it (`lw`) *)
Lemma pbV_U_sx : forall E (n : nat) w, ew E n = Z_to_bv 64 w -> 0 <= w < 2 ^ 32 ->
  U E (SExt true 32 (SOff n 0)) = if w <? 2 ^ 31 then w else w - 2 ^ 32 + 2 ^ 64.
Proof.
intros E n w H Hw. rewrite U_SExt, (U_atom E n w H) by lia. cbv iota.
change (2 ^ Z.of_N 32) with (2 ^ 32). rewrite (Z.mod_small w) by lia.
unfold zcanon, M64, bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
destruct (Z.ltb_spec w (2 ^ 31)).
- rewrite (Z.mod_small (w + 2 ^ 31)) by lia. replace (w + 2 ^ 31 - 2 ^ 31) with w by lia. apply Z.mod_small. lia.
- replace (w + 2 ^ 31) with ((w - 2 ^ 31) + 1 * 2 ^ 32) by lia. rewrite Z.mod_add by lia.
  rewrite (Z.mod_small (w - 2 ^ 31)) by lia.
  replace (w - 2 ^ 31 - 2 ^ 31) with ((w - 2 ^ 32 + 2 ^ 64) + (-1) * 2 ^ 64) by lia.
  rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

(* 0x84f64 snez a2,a0 of the Bool body *)
Lemma pbV_U_snez : forall E (n : nat) w, ew E n = Z_to_bv 64 w -> 0 <= w < 2 ^ 32 ->
  U E (SAlu ALU_SLTU (SLit 0) (SExt true 32 (SOff n 0))) = if w =? 0 then 0 else 1.
Proof.
intros E n w H Hw. rewrite U_SAlu. cbn [zalu_raw]. rewrite (pbV_U_sx E n w H Hw), (U_lit E 0) by lia.
destruct (Z.ltb_spec w (2 ^ 31)); destruct (Z.eqb_spec w 0) as [->|Hn]; cbn; try reflexivity.
- rewrite (proj2 (Z.ltb_lt 0 w)) by lia. reflexivity.
- lia.
- rewrite (proj2 (Z.ltb_lt 0 (w - 2 ^ 32 + 2 ^ 64))) by lia. reflexivity.
Qed.

(* 0x84f90 bltu a0,a2 with a0 = 255 and a2 the Int body *)
Lemma pbV_br_int : forall E (n : nat) w, ew E n = Z_to_bv 64 w -> 0 <= w < 2 ^ 32 ->
  branch_taken BC_LTU (sv_denot E (SLit 255)) (sv_denot E (SExt true 32 (SOff n 0))) = (255 <? w).
Proof.
intros E n w H Hw. rewrite branch_ltu_U, (pbV_U_sx E n w H Hw), (U_lit E 255) by lia.
destruct (Z.ltb_spec w (2 ^ 31)); [reflexivity|].
rewrite (proj2 (Z.ltb_lt 255 (w - 2 ^ 32 + 2 ^ 64))) by lia. symmetry. apply Z.ltb_lt. lia.
Qed.

(* the 4 bytes of a u32 put together by shifts and ors (0x85080 .. 0x850a4) *)
Abbreviation pbV_asm n := (SAlu ALU_OR
  (SAlu ALU_OR (SAlu ALU_SLL (SAlu ALU_SRL (SOff n 0) (SLit 24)) (SLit 24))
     (SAlu ALU_SLL (SExt false 8 (SAlu ALU_SRL (SOff n 0) (SLit 16))) (SLit 16)))
  (SAlu ALU_OR (SAlu ALU_SLL (SExt false 8 (SAlu ALU_SRL (SOff n 0) (SLit 8))) (SLit 8))
     (SExt false 8 (SOff n 0)))) (only parsing).

Lemma pbV_asm_eq : forall b, 0 <= b < 2 ^ 32 ->
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

Lemma pbV_lor_lt : forall a b n, 0 < n -> 0 <= a < 2 ^ n -> 0 <= b < 2 ^ n -> Z.lor a b < 2 ^ n.
Proof.
intros a b n Hn Ha Hb.
assert (L : forall c, 0 <= c < 2 ^ n -> Z.log2 c < n).
{ intros c Hc. destruct (Z.eq_dec c 0) as [->|Hc0]; [cbn; lia|]. apply Z.log2_lt_pow2; lia. }
destruct (Z.eq_dec (Z.lor a b) 0) as [E|E]; [rewrite E; apply Z.pow_pos_nonneg; lia|].
pose proof (Z.lor_nonneg a b) as [_ Hnn]. specialize (Hnn (conj (proj1 Ha) (proj1 Hb))).
apply Z.log2_lt_pow2; [lia|]. rewrite Z.log2_lor by lia. apply Z.max_lub_lt; apply L; assumption.
Qed.

Lemma pbV_U_asm : forall E (n : nat) b, ew E n = Z_to_bv 64 b -> 0 <= b < 2 ^ 32 -> U E (pbV_asm n) = b.
Proof.
intros E n b H Hb.
assert (U0 : U E (SOff n 0) = b) by (apply U_atom; [exact H | lia]).
assert (Rs : forall k, 0 <= k -> 0 <= Z.shiftr b k <= b).
{ intros k Hk. rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia]|].
  apply Z.div_le_upper_bound; [apply Z.pow_pos_nonneg; lia|]. assert (1 <= 2 ^ k) by (apply Z.pow_le_mono_r with (a := 2) in Hk; lia). nia. }
assert (Us : forall k, 0 <= k < 64 -> U E (SAlu ALU_SRL (SOff n 0) (SLit k)) = Z.shiftr b k).
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
{ intros e1 e2 v1 v2 H1 H2 R1 R2. assert (R : 0 <= Z.lor v1 v2 < 2 ^ 32).
  { split; [apply Z.lor_nonneg; lia|]. apply (pbV_lor_lt v1 v2 32 ltac:(lia) R1 R2). }
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
destruct (Uo _ _ _ _ UA UB RA RB) as [UC _]. rewrite UC. apply pbV_asm_eq. exact Hb.
Qed.

(* TAIL 0x84fa0 zext.b a0,a2 of the value v in [0, 255] *)
Lemma pbV_U_zb : forall E (n : nat) v, ew E n = Z_to_bv 64 v -> 0 <= v <= 255 ->
  U E (SAlu ALU_AND (SOff n 0) (SLit 255)) = v.
Proof.
intros E n v H Hv. rewrite U_and_lit by lia. rewrite (U_atom E n v H) by lia.
change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. change (2 ^ 8) with 256. lia.
Qed.

(* TAIL 0x84fc0 bge s4,s2: n >= cap (both small) *)
Lemma pbV_br_ge : forall E (i j : nat) a b, ew E i = Z_to_bv 64 a -> ew E j = Z_to_bv 64 b ->
  0 <= a < 2 ^ 63 -> 0 <= b < 2 ^ 63 ->
  branch_taken BC_GE (sv_denot E (SOff i 0)) (sv_denot E (SOff j 0)) = (b <=? a).
Proof.
intros E i j a b Hi Hj Ha Hb. cbn [branch_taken]. unfold bv_lts.
rewrite !denot_lit_U, (U_atom E i a Hi), (U_atom E j b Hj) by lia. rewrite !Z_to_bv_signed.
rewrite !bv_swrap_small by (change (bv_half_modulus 64) with (2 ^ 63); lia).
destruct (Z.ltb_spec a b); destruct (Z.leb_spec b a); first [reflexivity | lia].
Qed.

(* CELL: the alias out + 3 n, and the check 0x84fec that out + 3 n does not wrap below out *)
Lemma pbV_oal_ok : forall E o nn, ew E 19 = Z_to_bv 64 o -> ew E 20 = Z_to_bv 64 nn -> ew E 50 = Z_to_bv 64 (o + 3 * nn) ->
  0 <= o -> 0 <= nn -> o + 3 * nn < 2 ^ 64 -> sv_denot E pbV_oal = sv_denot E (SOff 50 0).
Proof.
intros E o nn H19 H20 H50 Ho Hn Hl.
rewrite !denot_lit_U. f_equal. unfold pbV_oal.
rewrite (U_atom E 50 (o + 3 * nn) H50) by lia.
assert (U19 : U E (SOff 19 0) = o) by (apply U_atom; [exact H19 | lia]).
assert (U20 : U E (SOff 20 0) = nn) by (apply U_atom; [exact H20 | lia]).
assert (Usl : U E (SAlu ALU_SLL (SOff 20 0) (SLit 1)) = 2 * nn).
{ rewrite U_SAlu, U20, U_SLit. cbn [zalu_raw]. change (Z.land (zcanon 1) 63) with 1.
  rewrite Z.shiftl_mul_pow2 by lia. rewrite zcanon_id by (unfold M64; lia). lia. }
assert (Ua : U E (SAlu ALU_ADD (SOff 19 0) (SOff 20 0)) = o + nn).
{ rewrite hpf_U_add by (rewrite U19, U20; lia). rewrite U19, U20. reflexivity. }
rewrite hpf_U_add by (rewrite Ua, Usl; lia). rewrite Ua, Usl. lia.
Qed.

Lemma pbV_br_wrap : forall E o a, ew E 19 = Z_to_bv 64 o -> ew E 50 = Z_to_bv 64 a -> 0 <= o <= a -> a < 2 ^ 64 ->
  branch_taken BC_EQ
    (sv_denot E (SAlu ALU_XOR (SAlu ALU_XOR (SAlu ALU_SLTU (SOff 50 0) (SOff 19 0)) (SLit 0)) (SLit 1)))
    (sv_denot E (SLit 0)) = false.
Proof.
intros E o a H19 H50 Ho Ha. rewrite branch_eq_U. rewrite !U_SAlu. cbn [zalu_raw].
rewrite (U_atom E 50 a H50), (U_atom E 19 o H19) by lia. rewrite !U_SLit.
rewrite (proj2 (Z.ltb_ge a o)) by lia. reflexivity.
Qed.

(* the child at cc lies inside the Struct body (spa_pod_is_inside passed) *)
Lemma pbV_child_in : forall bs r vs cc, Spa.pod_is_inside bs (r + 16) vs cc = true ->
  r + 16 <= cc /\ cc + 8 + Spa.u32_at bs cc <= r + 16 + vs.
Proof.
intros bs r vs cc H. unfold Spa.pod_is_inside, Spa.ptr_type_inside, Spa.ptrinside, Spa.ptr_remaining in H.
repeat match goal with Hx : (_ && _) = true |- _ => apply andb_prop in Hx as [? ?] end.
repeat match goal with Hx : (_ <=? _) = true |- _ => apply Z.leb_le in Hx end.
lia.
Qed.

(* an 8-byte cell holds a value and its low 64 bits alike *)
Lemma pbV_vm_mod : forall (m : word -> option byte) a v, val_mem rsegs m a 8 v -> val_mem rsegs m a 8 (v mod 2 ^ 64).
Proof.
intros m a v H k Hk. rewrite (H k Hk). unfold YO0f.le_byte.
assert (E : (v mod 2 ^ 64) mod 2 ^ (8 * Z.of_nat 8) = v mod 2 ^ (8 * Z.of_nat 8))
  by (change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64); apply Zmod_mod).
rewrite E. reflexivity.
Qed.

Lemma pbV_w64_mod : forall v, w64 v = Z_to_bv 64 (v mod 2 ^ 64).
Proof. intros v. unfold w64. apply hfp_Z64_eq_mod. rewrite Zmod_mod. reflexivity. Qed.

Section fsx. Context {fs : YK11.FPState}.
(* a cell of the frame temporaries (the first region, at sp) at a run's end *)
Lemma pbV_tval : forall E ss ms (H : word -> bool) rest cs off (n : N) e v,
  st_ok rsegs E ss (restrict H ms) -> ss_mem ss = YP09.mkRegion (Some 2%nat) 0 0x80 0 0x80 cs :: rest ->
  In (YP09.mkChunk off (CVal n e)) cs -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N n) -> Z.of_N n <= 8 ->
  val_mem rsegs (mrestrict H (ms_mem ms)) (bv_unsigned (ew E 2) + off) (N.to_nat n) v.
Proof.
intros E ss ms H rest cs off n e v HS Hm Hin He Hv Hn.
pose proof (st_ok_mem_ok rsegs E ss (restrict H ms) HS) as (_ & HF & _).
rewrite Hm in HF. inversion HF as [|r0 l0 HR _]; subst.
destruct HR as (_ & _ & _ & HC). cbn [YP09.r_chunks YP09.r_base base_val] in HC.
apply (val_of_chunk_ok rsegs E _ _ off n e v); [| exact He | exact Hv | exact Hn].
rewrite Forall_forall in HC. exact (HC _ Hin).
Qed.

(* a chunk of the out cell's region (the second region, at atom 50) at a run's end *)
Lemma pbV_tval2 : forall E ss ms (H : word -> bool) r1 rest cs off (n : N) e v,
  st_ok rsegs E ss (restrict H ms) -> ss_mem ss = r1 :: YP09.mkRegion (Some 50%nat) 0 3 0 3 cs :: rest ->
  In (YP09.mkChunk off (CVal n e)) cs -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N n) -> Z.of_N n <= 8 ->
  val_mem rsegs (mrestrict H (ms_mem ms)) (bv_unsigned (ew E 50) + off) (N.to_nat n) v.
Proof.
intros E ss ms H r1 rest cs off n e v HS Hm Hin He Hv Hn.
pose proof (st_ok_mem_ok rsegs E ss (restrict H ms) HS) as (_ & HF & _).
rewrite Hm in HF. inversion HF as [|r0 l0 HR0 HF1 Heq]. inversion HF1 as [|r2 l2 HR HF2 Heq2].
destruct HR as (_ & _ & _ & HC). cbn [YP09.r_chunks YP09.r_base base_val] in HC.
apply (val_of_chunk_ok rsegs E _ _ off n e v); [| exact He | exact Hv | exact Hn].
rewrite Forall_forall in HC. exact (HC _ Hin).
Qed.

(* a register the run left as it was at the entry *)
Lemma pbV_reg_of : forall E0 regs E ss ms (H : word -> bool) (q : bv 5) (n k : nat),
  st_ok rsegs E ss (restrict H ms) -> sr_get (ss_regs ss) q = SOff n 0 -> env_agree k E0 E -> (n < k)%nat ->
  ew E0 n = getr regs q -> getr (ms_regs ms) q = getr regs q.
Proof.
intros E0 regs E ss ms H q n k HS Hsr HAE Hn Hew.
rewrite (st_ok_restrict_reg rsegs H E ss ms q HS), Hsr, hk_sv_SOff0, (proj1 HAE n Hn). exact Hew.
Qed.
End fsx.

(* a run keeps every byte outside its write windows [lib/AU/HPgParseF.v pbf_kept] *)
Lemma pbV_kept : forall E rs (H : word -> bool) (m0 m1 m2 : word -> option byte) lo hi,
(forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> mrestrict H m1 (Z_to_bv 64 a) = mrestrict H m0 (Z_to_bv 64 a)) ->
frame_of E rs (mrestrict H m1) (mrestrict H m2) ->
(forall a, in_wrange E rs a -> lo <= a < hi) ->
forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> mrestrict H m2 (Z_to_bv 64 a) = mrestrict H m0 (Z_to_bv 64 a).
Proof.
intros E rs H m0 m1 m2 lo hi HK HF HW a Ha Hn.
rewrite <- (HK a Ha Hn). apply HF. rewrite unsigned_lit_small by exact Ha. intros X. exact (Hn (HW a X)).
Qed.

Lemma pbV_same_io_wvb : forall md l X, same_io md (with_vm_backing l X md).
Proof. intros md l X. unfold same_io. repeat split; reflexivity. Qed.
Ltac pbV_kio := let rec go := first [ apply same_io_refl | (eapply same_io_trans; [| apply pbV_same_io_wvb]); go ] in go.

(* ---- the plumbing of a run (lib/AU/HPgParseF.v's, over the kit's temporaries [spa, spa + 0x80)) ---- *)
Ltac pbV_B2 HAE B20 E B2 :=
lazymatch type of B20 with bv_unsigned (ew _ 2) = ?F =>
assert (B2 : bv_unsigned (ew E 2) = F) by (first [exact B20 | rewrite (proj1 HAE 2%nat ltac:(lia)); exact B20]) end.
Ltac pbV_awr x Hc HAE B20 :=
lazymatch goal with |- awr_okH ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own ?U =>
let B2 := fresh "B2" in pbV_B2 HAE B20 E B2;
let rs' := eval vm_compute in rs in change (awr_okH E rs' stk sp0 fp b0 bc ly own U);
repeat first
[ apply awr_okH_nil
| apply awr_okH_cons_ro; [cbn; lia|]
| apply (hk_awr_temps _ x E _ _ U Hc B2) ]
end.
Ltac pbV_keep HAE B20 :=
lazymatch goal with HFr : frame_of ?E _ (mrestrict _ _) (mrestrict _ _),
  KW : forall a, _ -> ~ _ -> mrestrict _ _ (Z_to_bv 64 a) = _ |- _ =>
let B2 := fresh "B2" in pbV_B2 HAE B20 E B2;
let KS := fresh "KS" in
pose proof (pbV_kept _ _ _ _ _ _ _ _ KW HFr) as KS;
lazymatch type of KS with ?P -> _ => let KX := fresh "KX" in assert (KX : P) by (
  let a := fresh "a" in let rg := fresh "rg" in let Hrg := fresh "Hrg" in let Hb := fresh "Hb" in
  intros a (rg & Hrg & Hb);
  lazymatch type of Hrg with In _ ?rs => let rs' := eval vm_compute in rs in change (In rg rs') in Hrg end;
  repeat (destruct Hrg as [<- | Hrg]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; first [rewrite B2 in Hb; lia | lia] | ]);
  destruct Hrg);
  specialize (KS KX); clear KX KW HFr B2; rename KS into KW end
end;
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
Ltac pbV_upd HAE :=
lazymatch goal with HS : st_ok _ ?E' _ _ |- _ =>
lazymatch type of HAE with env_agree ?k ?E0 ?E =>
let H := fresh in assert (H : env_agree k E0 E') by env_agree_chain HAE; clear HAE; rename H into HAE end end.
Ltac pbV_run x Hc HAE B20 :=
lazymatch goal with HS : st_ok _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
aj_run_tokH pb_tbl_ok HS HJ SHOK hk_Bspan; [ idtac .. | pbV_awr x Hc HAE B20 | pbV_keep HAE B20; pbV_upd HAE] end.
Ltac pbV_run_to x Hc HAE B20 stop :=
lazymatch goal with HS : st_ok _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
aj_run_to_tokH pb_tbl_ok HS HJ SHOK hk_Bspan stop; [ idtac .. | pbV_awr x Hc HAE B20 | pbV_keep HAE B20; pbV_upd HAE] end.
Ltac pbV_br Hc :=
lazymatch goal with HS : st_ok _ _ _ _, SH : sh_ok _ _ _ _ _ |- _ => srr_branch_tok pb_tbl_ok HS SH hk_Bspan end;
lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into Hc end.
(* a branch's condition over the entry env *)
Ltac pbV_hc HAE H :=
lazymatch type of HAE with env_agree ?k ?E0 ?E =>
tryif constr_eq E0 E then idtac else
  (repeat (rewrite (sv_denot_agree k E0 E _ HAE) in H by (vm_compute; reflexivity))) end.
(* a register at the run's end, as the entry env's value *)
Ltac pbV_rg HAE :=
lazymatch goal with |- getr (ms_regs ?ms) ?q = _ =>
lazymatch goal with HS : st_ok ?segs ?E ?ss (restrict ?H ms) |- _ =>
  let e := eval vm_compute in (sr_get (ss_regs ss) q) in
  rewrite (st_ok_restrict_reg segs H E ss ms q HS);
  change (sr_get (ss_regs ss) q) with e;
  lazymatch type of HAE with env_agree ?k ?E0 _ =>
    tryif constr_eq E0 E then idtac else rewrite (sv_denot_agree k E0 E e HAE ltac:(vm_compute; reflexivity)) end
end end.
Ltac pbV_rkeep E0 regs HAE n q :=
lazymatch goal with HS : st_ok _ ?E ?ss (restrict (w_H ?W) ?ms) |- _ =>
  rewrite (pbV_reg_of E0 regs E ss ms (w_H W) q n _ HS ltac:(vm_compute; reflexivity) HAE ltac:(lia)
                   ltac:(apply hk_env_reg; reflexivity))
end.
Ltac pbV_cregs E0 regs HAE HCR :=
apply (hk_cregs_same _ regs _ HCR);
[ pbV_rkeep E0 regs HAE 2%nat (2%bv : bv 5); reflexivity
| pbV_rkeep E0 regs HAE 3%nat (3%bv : bv 5); reflexivity
| pbV_rkeep E0 regs HAE 4%nat (4%bv : bv 5); reflexivity
| pbV_rkeep E0 regs HAE 8%nat (8%bv : bv 5); reflexivity
| pbV_rkeep E0 regs HAE 9%nat (9%bv : bv 5); reflexivity
| pbV_rkeep E0 regs HAE 18%nat (18%bv : bv 5); reflexivity
| pbV_rkeep E0 regs HAE 19%nat (19%bv : bv 5); reflexivity
| pbV_rkeep E0 regs HAE 26%nat (26%bv : bv 5); reflexivity
| pbV_rkeep E0 regs HAE 27%nat (27%bv : bv 5); reflexivity ].

(* an 8-byte chunk holding any value v (its low 64 bits) *)
Lemma pbV_vm_unmod : forall (m : word -> option byte) a v, val_mem rsegs m a 8 (v mod 2 ^ 64) -> val_mem rsegs m a 8 v.
Proof.
intros m a v H k Hk. rewrite (H k Hk). unfold YO0f.le_byte.
assert (E : (v mod 2 ^ 64) mod 2 ^ (8 * Z.of_nat 8) = v mod 2 ^ (8 * Z.of_nat 8))
  by (change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64); apply Zmod_mod).
rewrite E. reflexivity.
Qed.
Lemma pbV_chunk8 : forall E (m : word -> option byte) base off e v, sv_denot E e = w64 v ->
  val_mem rsegs m (base + off) 8 v -> YP09.chunk_ok rsegs E m base (YP09.mkChunk off (CVal 8 e)).
Proof.
intros E m base off e v He Hv. apply (chunk_ok_val rsegs E m base off 8 e (v mod 2 ^ 64)).
- rewrite He. apply pbV_w64_mod.
- change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). apply Z.mod_pos_bound. lia.
- lia.
- apply pbV_vm_mod. exact Hv.
Qed.

Section seg. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis errno_low : api_env rsegs B.
Hypothesis HBerrno : as_errno B = 0x5d812c.
Local Notation pctx := (@hp_ctx rsegs).

(* ---------------------------------- VAL's inner cuts ---------------------------------- *)
(* what each of them carries: VAL_at's core with the key read as (ch, p) *)
Definition pbV_core (x : pctx) (r cc : Z) (n : nat) (ch p : Z) (cl : list Headamp.cell) (keys rf : Z)
  (F : bvmap 5 word) (fc : bv 32) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
hp_core B x PAT_KEY cl (ha_res_bytes 0 0 0) regs mem md /\ hp_fxw F fc /\ hp_m_val x r cc n ch p cl keys rf /\
pb_loop x r cl rf regs mem /\ getr regs 23 = w64 (hx_P x + cc) /\
val_mem rsegs (hx_rd x mem) (hx_spa x + 24) 8 (keys + 1) /\
val_mem rsegs (hx_rd x mem) (hx_spa x + 48) 8 (shadow_addr (hx_P x + cc)).

(* REF 0x84ec4: a refusal OUT_OF_RANGE (t0 = 5) *)
Definition REF_at (x : pctx) (r cc : Z) (n : nat) (ch p : Z) (cl : list Headamp.cell) (keys rf : Z)
  (F : bvmap 5 word) (fc : bv 32) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
pbV_core x r cc n ch p cl keys rf F fc regs mem md /\ pb_a46 x r regs /\
getr regs 17 = w64 (shadow_addr (hx_P x + cc)) /\ getr regs 5 = w64 5 /\
hp_vcell ch p (Spa.child_at (hx_bs x) cc) = inl Headamp.REFUSE_OUT_OF_RANGE.

(* TAIL 0x84fa0: the value v of the value pod in a2 *)
Definition TAIL_at (x : pctx) (r cc : Z) (n : nat) (ch p : Z) (cl : list Headamp.cell) (keys rf v : Z)
  (F : bvmap 5 word) (fc : bv 32) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
pbV_core x r cc n ch p cl keys rf F fc regs mem md /\
getr regs 24 = w64 ch /\ getr regs 13 = w64 p /\ getr regs 11 = w64 (if p =? Headamp.HA_SENS then 0 else 1) /\
getr regs 12 = w64 v /\ 0 <= v <= 255 /\ getr regs 16 = w64 8 /\ getr regs 17 = w64 (shadow_addr (hx_P x + cc)) /\
getr regs 5 = w64 5 /\ Headamp.parse_value (Spa.child_at (hx_bs x) cc) = Some v.

(* CELL 0x84fc4: the value in range, room for the cell (n < cap) *)
Definition CELL_at (x : pctx) (r cc : Z) (n : nat) (ch p : Z) (cl : list Headamp.cell) (keys rf v : Z)
  (F : bvmap 5 word) (fc : bv 32) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
pbV_core x r cc n ch p cl keys rf F fc regs mem md /\
getr regs 24 = w64 ch /\ getr regs 13 = w64 p /\ getr regs 12 = w64 v /\ 0 <= v <= 255 /\
getr regs 16 = w64 8 /\ getr regs 17 = w64 (shadow_addr (hx_P x + cc)) /\ getr regs 14 = w64 (hx_P x + r + 16) /\
hp_vcell ch p (Spa.child_at (hx_bs x) cc) = inr (ch, p, v) /\ Z.of_nat (length cl) < hx_cap x.

(* FLT 0x850ac: the Float body's 4 bytes at spa + 56 *)
Definition FLT_at (x : pctx) (r cc : Z) (n : nat) (ch p : Z) (cl : list Headamp.cell) (keys rf : Z)
  (F : bvmap 5 word) (fc : bv 32) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
pbV_core x r cc n ch p cl keys rf F fc regs mem md /\
getr regs 24 = w64 ch /\ getr regs 13 = w64 p /\ getr regs 11 = w64 (if p =? Headamp.HA_SENS then 0 else 1) /\
getr regs 16 = w64 8 /\ getr regs 17 = w64 (shadow_addr (hx_P x + cc)) /\ getr regs 5 = w64 5 /\
val_mem rsegs (hx_rd x mem) (hx_spa x + 56) 4 (Spa.u32_at (hx_bs x) (cc + 8)) /\
Headamp.parse_value (Spa.child_at (hx_bs x) cc) = Nearest.nearest (Spa.u32_at (hx_bs x) (cc + 8)) 0 255.

Definition REF_ok (x : pctx) r cc n ch p cl keys rf : Prop := forall F fc regs mem md,
REF_at x r cc n ch p cl keys rf F fc regs mem md ->
SRr rsegs (hx_W x) (cfg_at (fx := mkFP F fc) rsegs PC_REF regs mem md) (PPOST B MT x).
Definition TAIL_ok (x : pctx) r cc n ch p cl keys rf v : Prop := forall F fc regs mem md,
TAIL_at x r cc n ch p cl keys rf v F fc regs mem md ->
SRr rsegs (hx_W x) (cfg_at (fx := mkFP F fc) rsegs PC_TAIL regs mem md) (PPOST B MT x).
Definition CELL_ok (x : pctx) r cc n ch p cl keys rf v : Prop := forall F fc regs mem md,
CELL_at x r cc n ch p cl keys rf v F fc regs mem md ->
SRr rsegs (hx_W x) (cfg_at (fx := mkFP F fc) rsegs PC_CELL regs mem md) (PPOST B MT x).
Definition FLT_ok (x : pctx) r cc n ch p cl keys rf : Prop := forall F fc regs mem md,
FLT_at x r cc n ch p cl keys rf F fc regs mem md ->
SRr rsegs (hx_W x) (cfg_at (fx := mkFP F fc) rsegs PC_FLT regs mem md) (PPOST B MT x).

(* ---------------------------------- small facts ---------------------------------- *)
Lemma pbV_spa : forall x : pctx, call_ok B x ->
  alloc_ceiling <= hx_spa x /\ hx_spa x + 0x100 <= hx_sp x /\ hx_sp x <= 2 ^ 47 /\ hx_spa x mod 32 = 0.
Proof.
intros x Hc. pose proof (hk_stack B x Hc) as (S1 & S2 & S3 & S4 & S5 & S6 & _ & _ & S9 & S10 & _).
pose proof (hk_frame_win B x Hc) as (W1 & W2 & _).
unfold T_parse_STK, T_PARSE_FRAME, ESTACK in *. lia.
Qed.

(* the cut core after a run that wrote only the frame temporaries [spa, spa + 0x80) *)
Lemma pbV_core_frame : forall (x : pctx) cl regs mem md regs2 mem2 md2, call_ok B x ->
  hp_core B x PAT_KEY cl (ha_res_bytes 0 0 0) regs mem md -> Z.of_nat (length cl) <= hx_cap x ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (hx_spa x + 0 <= a < hx_spa x + 0x80) ->
   mrestrict (w_H (hx_W x)) mem2 (Z_to_bv 64 a) = mrestrict (w_H (hx_W x)) mem (Z_to_bv 64 a)) ->
  ajournal rsegs B (hx_STK x) (hx_sp0 x) (hx_FP x) (hx_ly x) (hx_S x) (hx_W0 x) (hx_mem0 x) (hx_md0 x) (hx_own x)
    (hx_lyc x) (hx_Sc x) (hx_W x) (unpoison (hU (hx_fr x) PAT_KEY) mem2) md2 (hx_k x) ->
  same_io md md2 -> hk_cregs x regs2 -> hp_core B x PAT_KEY cl (ha_res_bytes 0 0 0) regs2 mem2 md2.
Proof.
intros x cl regs mem md regs2 mem2 md2 Hc Hcore Hn KW HJ Hio HCR.
exact (hk_core_frame B pb_segs_low x PAT_KEY cl (ha_res_bytes 0 0 0) regs mem md regs2 mem2 md2 0 0x80 errno_low Hc
  Hcore ltac:(lia) eq_refl ltac:(lia) ltac:(lia) KW HJ Hio HCR).
Qed.

Lemma pbV_mk_ADV : forall (x : pctx) r cc n cl keys rf F fc regs2 mem2 md2,
  hp_core B x PAT_KEY cl (ha_res_bytes 0 0 0) regs2 mem2 md2 -> hp_fxw F fc -> hp_m_adv x r cc n None cl keys rf ->
  pb_loop x r cl rf regs2 mem2 -> pb_a46 x r regs2 -> getr regs2 23 = w64 (hx_P x + cc) -> getr regs2 24 = w64 0 ->
  getr regs2 25 = w64 keys -> getr regs2 17 = w64 (shadow_addr (hx_P x + cc)) ->
  ADV_at B x r cc n None cl keys rf F fc regs2 mem2 md2.
Proof.
intros x r cc n cl keys rf F fc regs2 mem2 md2 H1 H2 H3 H4 H5 H6 H7 H8 H9.
unfold ADV_at. cbn [hp_keyv]. repeat (split; [assumption|]). assumption.
Qed.

(* ---------------------------------- REF ---------------------------------- *)
Definition pbV_LR (x : pctx) (r keys rf : Z) : list word := [w64 rf; w64 (keys + 1); w64 (hx_P x + r + 16)].

(* the temporaries' chunks at an entry, from the core *)
Lemma pbV_tcs_ok : forall (x : pctx) r cc n ch p cl keys rf F fc regs mem md L (rfa k1a b40a : nat),
  pbV_core x r cc n ch p cl keys rf F fc regs mem md ->
  ew (hk_env x regs L) rfa = w64 rf -> ew (hk_env x regs L) k1a = w64 (keys + 1) ->
  ew (hk_env x regs L) b40a = w64 (hx_P x + r + 16) -> 0 <= hx_P x + cc < 2 ^ 47 ->
  (hx_P x + r + 8) mod 8 = 0 ->
  Forall (YP09.chunk_ok rsegs (hk_env x regs L) (hx_rd x mem) (hx_spa x)) (pbV_tcs rfa k1a b40a).
Proof.
intros x r cc n ch p cl keys rf F fc regs mem md L rfa k1a b40a HK Erf Ek1 Eb40 HPc Hmod.
destruct HK as (Hcore & _ & _ & (_ & _ & _ & L16 & L32 & L40) & H23 & H24 & H48).
pose proof (hk_core_cregs B x _ _ _ _ _ _ Hcore) as (_ & _ & _ & _ & _ & _ & _ & _ & H27).
unfold pbV_tcs. repeat apply Forall_cons; try apply Forall_nil.
- apply (pbV_chunk8 _ _ _ 16 (SLit 3) 3); [reflexivity|]. rewrite Hmod in L16. exact L16.
- apply (pbV_chunk8 _ _ _ 24 (SOff k1a 0) (keys + 1)); [rewrite hk_sv_SOff0; exact Ek1 | exact H24].
- apply (pbV_chunk8 _ _ _ 32 (SOff rfa 0) rf); [rewrite hk_sv_SOff0; exact Erf | exact L32].
- apply (pbV_chunk8 _ _ _ 40 (SOff b40a 0) (hx_P x + r + 16)); [rewrite hk_sv_SOff0; exact Eb40 | exact L40].
- apply (pbV_chunk8 _ _ _ 48 pbV_s7sh (shadow_addr (hx_P x + cc))); [|exact H48].
  rewrite denot_lit_U. unfold w64. f_equal.
  apply pbV_U_s7sh; [rewrite (hk_env_reg x regs L 23 23%bv eq_refl), H23; reflexivity
    | rewrite (hk_env_reg x regs L 27 27%bv eq_refl), H27; reflexivity | exact HPc].
Qed.

(* the bounds of P + cc, from VAL's model fact and the call *)
Lemma pbV_pc : forall (x : pctx) r cc n ch p cl keys rf, call_ok B x -> hp_m_val x r cc n ch p cl keys rf ->
  16 <= hx_P x + cc /\ hx_P x + cc + 8 + Spa.u32_at (hx_bs x) cc <= hx_P x + hx_len x /\
  hx_P x + hx_len x + 8 <= 2 ^ 47 /\ (hx_P x + cc) mod 8 = 0 /\ (hx_P x + r + 8) mod 8 = 0 /\
  0 < hx_P x /\ hx_P x mod 16 = 0 /\ r + 16 <= cc /\ cc + 8 + Spa.u32_at (hx_bs x) cc <= hx_len x.
Proof.
intros x r cc n ch p cl keys rf Hc (Hn & (Hr16 & Hr8 & Hvs & Hrl) & Hc16 & Hc8 & Hin & _).
pose proof (hk_pod B x Hc Hn) as (P0 & P16 & PL & PL8 & _ & P63 & _ & _ & _ & _ & _ & _ & _ & PAM & _).
pose proof (pbV_child_in (hx_bs x) r (hp_vs x r) cc Hin) as [Ci1 Ci2].
pose proof (hgw_u32_range (hx_bs x) cc) as U32.
unfold amem_range, kLowMemEnd, kHighMemEnd in PAM. unfold hp_vs in *.
repeat split; try lia.
Qed.

Lemma pbV_entryR : forall x r cc n ch p cl keys rf F fc regs mem md, call_ok B x ->
  REF_at x r cc n ch p cl keys rf F fc regs mem md ->
  st_ok (fx := mkFP F fc) rsegs (hk_env x regs (pbV_LR x r keys rf)) pbV_ssR
    (restrict (w_H (hx_W x)) (@mkst (mkFP F fc) regs (Z_to_bv 64 PC_REF) mem (seg_rom rsegs))).
Proof.
intros x r cc n ch p cl keys rf F fc regs mem md Hc HR.
pose proof HR as (HK & _ & _ & _ & _).
pose proof HK as (Hcore & _ & Hm & HL & _ & _ & _).
pose proof Hm as (_ & _ & _ & _ & _ & _ & (_ & _ & Hrf) & _).
pose proof (hk_core_cregs B x _ _ _ _ _ _ Hcore) as HCR.
pose proof HCR as (H2 & _).
pose proof (pbV_spa x Hc) as (S1 & S2 & S3 & S4).
pose proof (pbV_pc x r cc n ch p cl keys rf Hc Hm) as (Q1 & Q2 & Q3 & Q4 & Q5 & _).
pose proof alloc_ceiling_value as [[C1 C2] _].
set (L := pbV_LR x r keys rf).
assert (E2 : bv_unsigned (ew (hk_env x regs L) 2) = hx_spa x).
{ rewrite (hk_env_reg x regs L 2 2%bv eq_refl), H2. unfold w64. apply unsigned_lit_small. lia. }
assert (E47 : bv_unsigned (ew (hk_env x regs L) 47) = rf).
{ change 47%nat with (47 + 0)%nat. rewrite hk_env_seg. cbn [nth L pbV_LR]. unfold w64.
  apply unsigned_lit_small. lia. }
rewrite restrict_mkst_fx. unfold pbV_ssR, hk_env. apply (entry_st_ok_full (fx := mkFP F fc) rsegs);
  fold (hk_env x regs L).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor].
  apply (hk_temps_ok B x PAT_KEY cl (ha_res_bytes 0 0 0) regs mem md L _ Hc Hcore).
  apply (pbV_tcs_ok x r cc n ch p cl keys rf F fc regs mem md L 47 48 49 HK);
  first [exact (hk_env_seg x regs L 0) | exact (hk_env_seg x regs L 1) | exact (hk_env_seg x regs L 2)
        | pose proof (hgw_u32_range (hx_bs x) cc); lia].
- cbn [pairwise_disjoint all_disjoint]. tauto.
- split; [|split; [exact I | exact I]]. cbn [f_atoms].
  apply (hk_atoms_ok B x regs L _ Hc HCR). cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E47. change (2 ^ 0) with 1. rewrite Z.mod_1_r. repeat split; lia.
Qed.

(* 0x84ec4 .. 0x84ed8: rf' = (rf <> 0 ? rf : 5) -> [spa + 32], s8 = 0, s9 = [spa + 24]; ADV *)
Lemma pbV_ref : forall x r cc n ch p cl keys rf, call_ok B x ->
  (forall cl' rf', ADV_ok B MT x r cc n None cl' (keys + 1) rf') -> REF_ok x r cc n ch p cl keys rf.
Proof.
intros x r cc n ch p cl keys rf Hc HADV F fc regs mem md HR.
unfold ADV_ok, cfg_at in *.
pose proof pb_wx as Hwx. pose proof pb_segs_low as Hsegs.
pose proof (pbV_entryR x r cc n ch p cl keys rf F fc regs mem md Hc HR) as HS.
destruct HR as ((Hcore & Hfx & Hm & HL & H23 & H24 & H48) & H46 & H17 & H5 & Hv).
pose proof Hm as (Hn & _ & _ & _ & _ & _ & (Hcap & Hk & Hrf) & _).
pose proof (hk_core_cregs B x _ _ _ _ _ _ Hcore) as HCR.
pose proof HCR as (H2 & _).
pose proof Hcore as ((HJ & HOK & HPAT) & _).
pose proof (pbV_spa x Hc) as (S1 & S2 & S3 & S4).
pose proof (pbV_pc x r cc n ch p cl keys rf Hc Hm) as (Q1 & Q2 & Q3 & Q4 & Q5 & _).
pose proof alloc_ceiling_value as [[C1 C2] _].
destruct HL as (L20 & L21 & L22 & L16 & L32 & L40).
destruct H46 as (H14 & H16).
set (L := pbV_LR x r keys rf) in HS.
assert (SHOK : sh_ok rsegs hk_Bx [] (hk_env x regs L) (mrestrict (w_H (hx_W x)) mem)) by constructor.
assert (HAE : env_agree 50 (hk_env x regs L) (hk_env x regs L)) by apply env_agree_refl.
assert (B20 : bv_unsigned (ew (hk_env x regs L) 2) = hx_spa x).
{ rewrite (hk_env_reg x regs L 2 2%bv eq_refl), H2. unfold w64. apply unsigned_lit_small. lia. }
assert (E47 : ew (hk_env x regs L) 47 = w64 rf) by exact (hk_env_seg x regs L 0).
assert (E48 : ew (hk_env x regs L) 48 = w64 (keys + 1)) by exact (hk_env_seg x regs L 1).
assert (E49 : ew (hk_env x regs L) 49 = w64 (hx_P x + r + 16)) by exact (hk_env_seg x regs L 2).
assert (E5 : ew (hk_env x regs L) 5 = w64 5) by (rewrite (hk_env_reg x regs L 5 5%bv eq_refl); exact H5).
assert (KW : forall a, 0 <= a < 2 ^ 64 -> ~ (hx_spa x + 0 <= a < hx_spa x + 0x80) ->
  mrestrict (w_H (hx_W x)) mem (Z_to_bv 64 a) = mrestrict (w_H (hx_W x)) mem (Z_to_bv 64 a)) by reflexivity.
change (w64 PC_REF) with (Z_to_bv 64 PC_REF).
(* 0x84ec4 ld a0,32(sp); 0x84ec8 beqz a0 *)
pbV_run x Hc HAE B20. pbV_br Hb1; pbV_hc HAE Hb1;
rewrite branch_eq_U, (U_atom _ 47 rf) in Hb1 by (first [exact E47 | lia]); rewrite U_lit in Hb1 by lia.
- (* rf = 0: t0 = 5 stays *)
  apply Z.eqb_eq in Hb1. subst rf.
  pbV_run_to x Hc HAE B20 PC_ADV.
  lazymatch goal with HS : st_ok _ ?E ?ss (restrict _ ?ms) |- _ =>
    pbV_B2 HAE B20 E B2;
    let m := eval vm_compute in (ss_mem ss) in
    lazymatch m with YP09.mkRegion _ _ _ _ _ ?cs :: ?rest =>
      assert (Hmem : ss_mem ss = YP09.mkRegion (Some 2%nat) 0 0x80 0 0x80 cs :: rest) by (vm_compute; reflexivity);
      pose proof (fun off e v => pbV_tval E ss ms (w_H (hx_W x)) rest cs off 8%N e v HS Hmem) as HFV
    end;
    rewrite (st_ok_restrict_mkst rsegs (w_H (hx_W x)) _ _ _ HS ltac:(vm_compute; reflexivity))
  end.
  apply (HADV cl 5).
  eapply pbV_mk_ADV.
  + eapply pbV_core_frame; [exact Hc | exact Hcore | lia | exact KW | exact HJ | pbV_kio | pbV_cregs (hk_env x regs L) regs HAE HCR].
  + exact Hfx.
  + exact (pbV_m_ref x r cc n ch p cl keys 0 Hm Hv).
  + unfold pb_loop.
    split; [pbV_rkeep (hk_env x regs L) regs HAE 20%nat (20%bv : bv 5); exact L20|].
    split; [pbV_rkeep (hk_env x regs L) regs HAE 21%nat (21%bv : bv 5); exact L21|].
    split; [pbV_rkeep (hk_env x regs L) regs HAE 22%nat (22%bv : bv 5); exact L22|].
    split; [rewrite <- B2; rewrite Q5 in L16 |- *; apply pbV_vm_unmod;
            apply (HFV 16 (SLit 3) 3); [cbn [In]; tauto | reflexivity | cbn; lia | cbn; lia]|].
    split; [rewrite <- B2; apply pbV_vm_unmod; apply (HFV 32 (SOff 5 0) 5);
            [cbn [In]; tauto | | cbn; lia | cbn; lia]|].
    { try rewrite (sv_denot_agree 50 (hk_env x regs L) _ (SOff 5 0) HAE) by (vm_compute; reflexivity).
      rewrite hk_sv_SOff0. exact E5. }
    rewrite <- B2. apply pbV_vm_unmod. apply (HFV 40 (SOff 49 0) ((hx_P x + r + 16) mod 2 ^ 64));
      [cbn [In]; tauto | | cbn; apply Z.mod_pos_bound; lia | cbn; lia].
    try rewrite (sv_denot_agree 50 (hk_env x regs L) _ (SOff 49 0) HAE) by (vm_compute; reflexivity).
    rewrite hk_sv_SOff0, E49. apply pbV_w64_mod.
  + split; [pbV_rkeep (hk_env x regs L) regs HAE 14%nat (14%bv : bv 5); exact H14|].
    pbV_rkeep (hk_env x regs L) regs HAE 16%nat (16%bv : bv 5); exact H16.
  + pbV_rkeep (hk_env x regs L) regs HAE 23%nat (23%bv : bv 5); exact H23.
  + pbV_rg HAE. reflexivity.
  + pbV_rg HAE. rewrite hk_sv_SOff0. exact E48.
  + pbV_rkeep (hk_env x regs L) regs HAE 17%nat (17%bv : bv 5); exact H17.
- (* rf <> 0: t0 = rf *)
  apply Z.eqb_neq in Hb1.
  pbV_run_to x Hc HAE B20 PC_ADV.
  lazymatch goal with HS : st_ok _ ?E ?ss (restrict _ ?ms) |- _ =>
    pbV_B2 HAE B20 E B2;
    let m := eval vm_compute in (ss_mem ss) in
    lazymatch m with YP09.mkRegion _ _ _ _ _ ?cs :: ?rest =>
      assert (Hmem : ss_mem ss = YP09.mkRegion (Some 2%nat) 0 0x80 0 0x80 cs :: rest) by (vm_compute; reflexivity);
      pose proof (fun off e v => pbV_tval E ss ms (w_H (hx_W x)) rest cs off 8%N e v HS Hmem) as HFV
    end;
    rewrite (st_ok_restrict_mkst rsegs (w_H (hx_W x)) _ _ _ HS ltac:(vm_compute; reflexivity))
  end.
  apply (HADV cl rf).
  eapply pbV_mk_ADV.
  + eapply pbV_core_frame; [exact Hc | exact Hcore | lia | exact KW | exact HJ | pbV_kio | pbV_cregs (hk_env x regs L) regs HAE HCR].
  + exact Hfx.
  + pose proof (pbV_m_ref x r cc n ch p cl keys rf Hm Hv) as HMA.
    rewrite (proj2 (Z.eqb_neq rf 0) Hb1) in HMA. exact HMA.
  + unfold pb_loop.
    split; [pbV_rkeep (hk_env x regs L) regs HAE 20%nat (20%bv : bv 5); exact L20|].
    split; [pbV_rkeep (hk_env x regs L) regs HAE 21%nat (21%bv : bv 5); exact L21|].
    split; [pbV_rkeep (hk_env x regs L) regs HAE 22%nat (22%bv : bv 5); exact L22|].
    split; [rewrite <- B2; rewrite Q5 in L16 |- *; apply pbV_vm_unmod;
            apply (HFV 16 (SLit 3) 3); [cbn [In]; tauto | reflexivity | cbn; lia | cbn; lia]|].
    split; [rewrite <- B2; apply (HFV 32 (SOff 47 0) rf);
            [cbn [In]; tauto | | cbn; lia | cbn; lia]|].
    { try rewrite (sv_denot_agree 50 (hk_env x regs L) _ (SOff 47 0) HAE) by (vm_compute; reflexivity).
      rewrite hk_sv_SOff0. exact E47. }
    rewrite <- B2. apply pbV_vm_unmod. apply (HFV 40 (SOff 49 0) ((hx_P x + r + 16) mod 2 ^ 64));
      [cbn [In]; tauto | | cbn; apply Z.mod_pos_bound; lia | cbn; lia].
    try rewrite (sv_denot_agree 50 (hk_env x regs L) _ (SOff 49 0) HAE) by (vm_compute; reflexivity).
    rewrite hk_sv_SOff0, E49. apply pbV_w64_mod.
  + split; [pbV_rkeep (hk_env x regs L) regs HAE 14%nat (14%bv : bv 5); exact H14|].
    pbV_rkeep (hk_env x regs L) regs HAE 16%nat (16%bv : bv 5); exact H16.
  + pbV_rkeep (hk_env x regs L) regs HAE 23%nat (23%bv : bv 5); exact H23.
  + pbV_rg HAE. reflexivity.
  + pbV_rg HAE. rewrite hk_sv_SOff0. exact E48.
  + pbV_rkeep (hk_env x regs L) regs HAE 17%nat (17%bv : bv 5); exact H17.
Qed.

(* the expression of the 8-byte chunk at offset off *)
Definition pbV_cat (cs : list YP09.chunk) (off : Z) : sv :=
match find (fun c => Z.eqb (YP09.c_off c) off) cs with
| Some c => match YP09.c_val c with CVal _ e => e | _ => SLit 0 end
| None => SLit 0
end.
(* ---------------------------------- a cut's core after a run ---------------------------------- *)
Lemma pbV_fxw_keep : forall F fc G fc', hp_fxw F fc ->
  (forall k : bv 5, bv_unsigned k <> 14 -> bv_unsigned k <> 15 -> Sem.reg_get G k = Sem.reg_get F k) ->
  YK0o.frm_zero fc' -> hp_fxw G fc'.
Proof.
intros F fc G fc' ((HF & _) & H8) HG HZ. split; [split|].
- intros k Hk. change (Sem.reg_get G k = Sem.reg_get (@fp_regs fx) k).
  rewrite HG; [exact (HF k Hk) | |]; intros E; apply Hk; rewrite E; cbn; auto.
- exact HZ.
- rewrite HG by (vm_compute; lia). exact H8.
Qed.

Lemma pbV_core_of_VAL : forall x r cc n ch p cl keys rf F fc regs mem md,
  VAL_at B x r cc n ch p cl keys rf F fc regs mem md -> pbV_core x r cc n ch p cl keys rf F fc regs mem md.
Proof.
intros x r cc n ch p cl keys rf F fc regs mem md (H1 & H2 & H3 & H4 & _ & H6 & _ & _ & _ & _ & H11 & H12).
exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H6 (conj H11 H12)))))).
Qed.

Lemma pbV_core_mk : forall x r cc n ch p cl keys rf F fc regs mem md regs2 mem2 md2, call_ok B x ->
  pbV_core x r cc n ch p cl keys rf F fc regs mem md ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (hx_spa x + 0 <= a < hx_spa x + 0x80) ->
   mrestrict (w_H (hx_W x)) mem2 (Z_to_bv 64 a) = mrestrict (w_H (hx_W x)) mem (Z_to_bv 64 a)) ->
  ajournal rsegs B (hx_STK x) (hx_sp0 x) (hx_FP x) (hx_ly x) (hx_S x) (hx_W0 x) (hx_mem0 x) (hx_md0 x) (hx_own x)
    (hx_lyc x) (hx_Sc x) (hx_W x) (unpoison (hU (hx_fr x) PAT_KEY) mem2) md2 (hx_k x) ->
  same_io md md2 ->
  getr regs2 2 = getr regs 2 -> getr regs2 3 = getr regs 3 -> getr regs2 4 = getr regs 4 ->
  getr regs2 8 = getr regs 8 -> getr regs2 9 = getr regs 9 -> getr regs2 18 = getr regs 18 ->
  getr regs2 19 = getr regs 19 -> getr regs2 26 = getr regs 26 -> getr regs2 27 = getr regs 27 ->
  getr regs2 20 = getr regs 20 -> getr regs2 21 = getr regs 21 -> getr regs2 22 = getr regs 22 ->
  getr regs2 23 = getr regs 23 ->
  val_mem rsegs (hx_rd x mem2) (hx_spa x + 16) 8 ((hx_P x + r + 8) mod 8 + 3) ->
  val_mem rsegs (hx_rd x mem2) (hx_spa x + 24) 8 (keys + 1) ->
  val_mem rsegs (hx_rd x mem2) (hx_spa x + 32) 8 rf ->
  val_mem rsegs (hx_rd x mem2) (hx_spa x + 40) 8 (hx_P x + r + 16) ->
  val_mem rsegs (hx_rd x mem2) (hx_spa x + 48) 8 (shadow_addr (hx_P x + cc)) ->
  pbV_core x r cc n ch p cl keys rf F fc regs2 mem2 md2.
Proof.
intros x r cc n ch p cl keys rf F fc regs mem md regs2 mem2 md2 Hc (Hcore & Hfx & Hm & (L20 & L21 & L22 & _) & H23 & _)
  KW HJ Hio R2 R3 R4 R8 R9 R18 R19 R26 R27 R20 R21 R22 R23 T16 T24 T32 T40 T48.
pose proof Hm as (_ & _ & _ & _ & _ & _ & (Hcap & _) & _).
pose proof (hk_core_cregs B x _ _ _ _ _ _ Hcore) as HCR.
split; [|split; [exact Hfx|split; [exact Hm|split; [|split; [rewrite R23; exact H23|split; assumption]]]]].
- apply (pbV_core_frame x cl regs mem md regs2 mem2 md2 Hc Hcore Hcap KW HJ Hio).
  apply (hk_cregs_same x regs regs2 HCR); assumption.
- unfold pb_loop. rewrite R20, R21, R22. repeat split; assumption.
Qed.

(* ---- a run's end: the frame temporaries and the kept registers ---- *)
Ltac pbV_prep x HAE B20 :=
lazymatch goal with HS : st_ok _ ?E ?ss (restrict _ ?ms) |- _ =>
  let B2 := fresh "B2" in pbV_B2 HAE B20 E B2;
  let m := eval vm_compute in (ss_mem ss) in
  lazymatch m with YP09.mkRegion _ _ _ _ _ ?cs :: ?rest =>
    let Hmem := fresh "Hmem" in
    assert (Hmem : ss_mem ss = YP09.mkRegion (Some 2%nat) 0 0x80 0 0x80 cs :: rest) by (vm_compute; reflexivity);
    let HFV := fresh "HFV" in
    pose proof (fun off nn e v => pbV_tval E ss ms (w_H (hx_W x)) rest cs off nn e v HS Hmem) as HFV
  end;
  rewrite (st_ok_restrict_mkst rsegs (w_H (hx_W x)) _ _ _ HS ltac:(vm_compute; reflexivity));
  let pc := eval vm_compute in (ss_pc ss) in change (ss_pc ss) with pc
end.
Ltac pbV_rk E0 regs HAE :=
lazymatch goal with |- getr _ ?q = getr _ ?q =>
  let z := eval vm_compute in (Z.to_nat (bv_unsigned q)) in pbV_rkeep E0 regs HAE z q; reflexivity end.
(* the denotation of a temporaries' chunk at a run's end, as the entry's value *)
Ltac pbV_den E0 HAE D48 :=
lazymatch goal with |- sv_denot ?E ?e = _ =>
  first [ reflexivity
        | (try rewrite (sv_denot_agree _ E0 E e HAE) by (vm_compute; reflexivity));
          first [ exact D48 | rewrite hk_sv_SOff0; exact (hk_env_seg _ _ _ _) ] ] end.
Ltac pbV_tmp E0 HAE D48 :=
lazymatch goal with HFV : forall (off : Z) (nn : N) (e : sv) (v : Z), _, B2 : bv_unsigned (ew _ 2) = hx_spa _,
  HS : st_ok _ _ ?ss _ |- val_mem _ _ (hx_spa ?x + ?off) 8 _ =>
  let m := eval vm_compute in (ss_mem ss) in
  lazymatch m with YP09.mkRegion _ _ _ _ _ ?cs :: _ =>
    let e := eval vm_compute in (pbV_cat cs off) in
    rewrite <- B2; apply pbV_vm_unmod;
    apply (HFV off 8%N e); [cbn [In]; tauto | rewrite <- pbV_w64_mod; pbV_den E0 HAE D48
      | change (8 * Z.of_N 8) with 64; apply Z.mod_pos_bound; lia | cbn; lia]
  end end.
Ltac pbV_cmk E0 regs HAE D48 Hc HK0 Q5 :=
eapply pbV_core_mk; [exact Hc | exact HK0 | eassumption | eassumption | pbV_kio | .. ];
first [ pbV_rk E0 regs HAE | (try rewrite Q5); pbV_tmp E0 HAE D48 ].

(* ---------------------------------- VAL's entry ---------------------------------- *)
Definition pbV_LV (x : pctx) (r cc keys rf : Z) : list word :=
[w64 (Spa.u32_at (hx_bs x) cc); w64 (Spa.u32_at (hx_bs x) (cc + 4)); w64 (Spa.u32_at (hx_bs x) (cc + 8));
 w64 rf; w64 (keys + 1); w64 (hx_P x + r + 16)].

Lemma pbV_entryV : forall x r cc n ch p cl keys rf F fc regs mem md (big : bool), call_ok B x ->
  VAL_at B x r cc n ch p cl keys rf F fc regs mem md -> big = (4 <=? Spa.u32_at (hx_bs x) cc) ->
  st_ok (fx := mkFP F fc) rsegs (hk_env x regs (pbV_LV x r cc keys rf)) (pbV_ssV big)
    (restrict (w_H (hx_W x)) (@mkst (mkFP F fc) regs (Z_to_bv 64 PC_VAL) mem (seg_rom rsegs))) /\
  sh_ok rsegs hk_Bx (pbV_shV big) (hk_env x regs (pbV_LV x r cc keys rf)) (mrestrict (w_H (hx_W x)) mem).
Proof.
intros x r cc n ch p cl keys rf F fc regs mem md big Hc HV Hbig.
pose proof (pbV_core_of_VAL x r cc n ch p cl keys rf F fc regs mem md HV) as HK.
destruct HV as (Hcore & Hfx & Hm & HL & H46 & H23 & H24 & H13 & H11 & H17 & V24 & V48).
pose proof Hm as (Hn & (Hr16 & _) & _ & _ & _ & _ & (Hcap & Hk & Hrf) & _).
pose proof (hk_core_cregs B x _ _ _ _ _ _ Hcore) as HCR.
pose proof HCR as (H2 & _ & _ & _ & _ & _ & _ & _ & H27).
pose proof (pbV_spa x Hc) as (S1 & S2 & S3 & S4).
pose proof (pbV_pc x r cc n ch p cl keys rf Hc Hm) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9).
pose proof (hk_pod_at_cut B pb_segs_low x PAT_KEY cl (ha_res_bytes 0 0 0) regs mem md errno_low Hc Hn Hcore
  ltac:(lia)) as (HG & HRA & _).
pose proof (hk_pod_side B x Hc Hn) as HPS.
pose proof (hk_frame_win B x Hc) as (W1 & W2 & _).
pose proof alloc_ceiling_value as [[C1 C2] _].
pose proof (hgw_u32_range (hx_bs x) cc) as U0.
pose proof (hgw_u32_range (hx_bs x) (cc + 4)) as U4.
pose proof (hgw_u32_range (hx_bs x) (cc + 8)) as U8.
assert (Hb12 : big = true -> cc + 12 <= hx_len x).
{ intros Hb. rewrite Hb in Hbig. symmetry in Hbig. apply Z.leb_le in Hbig. lia. }
assert (Hb8 : big = false -> Spa.u32_at (hx_bs x) cc < 4).
{ intros Hb. rewrite Hb in Hbig. symmetry in Hbig. apply Z.leb_gt in Hbig. lia. }
set (L := pbV_LV x r cc keys rf).
assert (E2 : bv_unsigned (ew (hk_env x regs L) 2) = hx_spa x).
{ rewrite (hk_env_reg x regs L 2 2%bv eq_refl), H2. unfold w64. apply unsigned_lit_small. lia. }
assert (E23 : ew (hk_env x regs L) 23 = w64 (hx_P x + cc)) by (rewrite (hk_env_reg x regs L 23 23%bv eq_refl); exact H23).
assert (B23 : bv_unsigned (ew (hk_env x regs L) 23) = hx_P x + cc).
{ rewrite E23. unfold w64. apply unsigned_lit_small. lia. }
assert (E27 : ew (hk_env x regs L) 27 = w64 SHADOW_OFF) by (rewrite (hk_env_reg x regs L 27 27%bv eq_refl); exact H27).
assert (E47 : ew (hk_env x regs L) 47 = w64 (Spa.u32_at (hx_bs x) cc)) by exact (hk_env_seg x regs L 0).
assert (E48 : ew (hk_env x regs L) 48 = w64 (Spa.u32_at (hx_bs x) (cc + 4))) by exact (hk_env_seg x regs L 1).
assert (E49 : ew (hk_env x regs L) 49 = w64 (Spa.u32_at (hx_bs x) (cc + 8))) by exact (hk_env_seg x regs L 2).
assert (E50 : ew (hk_env x regs L) 50 = w64 rf) by exact (hk_env_seg x regs L 3).
assert (B47 : bv_unsigned (ew (hk_env x regs L) 47) = Spa.u32_at (hx_bs x) cc).
{ rewrite E47. unfold w64. apply unsigned_lit_small. lia. }
assert (B48 : bv_unsigned (ew (hk_env x regs L) 48) = Spa.u32_at (hx_bs x) (cc + 4)).
{ rewrite E48. unfold w64. apply unsigned_lit_small. lia. }
assert (B49 : bv_unsigned (ew (hk_env x regs L) 49) = Spa.u32_at (hx_bs x) (cc + 8)).
{ rewrite E49. unfold w64. apply unsigned_lit_small. lia. }
assert (B50 : bv_unsigned (ew (hk_env x regs L) 50) = rf).
{ rewrite E50. unfold w64. apply unsigned_lit_small. lia. }
rewrite restrict_mkst_fx. split.
- unfold pbV_ssV, hk_env. apply (entry_st_ok_full (fx := mkFP F fc) rsegs); fold (hk_env x regs L).
  + apply regs_ok_pin; [apply regs_ok_Ereg | intros E; apply (f_equal bv_unsigned) in E; vm_compute in E; discriminate |].
    rewrite denot_lit_U, (pbV_U_s7sh _ (hx_P x + cc) E23 E27 ltac:(lia)). exact H17.
  + destruct big; vm_compute; reflexivity.
  + constructor; [|constructor; [|constructor]].
    * apply (hk_temps_ok B x PAT_KEY cl (ha_res_bytes 0 0 0) regs mem md L _ Hc Hcore).
      apply (pbV_tcs_ok x r cc n ch p cl keys rf F fc regs mem md L 50 51 52 HK);
      first [exact (hk_env_seg x regs L 3) | exact (hk_env_seg x regs L 4) | exact (hk_env_seg x regs L 5) | lia].
    * unfold region_ok, pbV_podr. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite B23. split; [lia|]. split; [destruct big; lia|]. split; [intros o Ho; lia|].
      apply Forall_app; split; [repeat apply Forall_cons; try apply Forall_nil|destruct big; repeat apply Forall_cons; try apply Forall_nil].
      -- apply (chunk_ok_val rsegs _ _ _ 0 4 (SOff 47 0) (Spa.u32_at (hx_bs x) cc));
           [rewrite hk_sv_SOff0; exact E47 | cbn; lia | cbn; lia |].
         rewrite Z.add_0_r. apply (hgw_pod_u32 _ (hx_P x) (hx_bs x) cc HG); unfold hx_len in *; lia.
      -- apply (chunk_ok_val rsegs _ _ _ 4 4 (SOff 48 0) (Spa.u32_at (hx_bs x) (cc + 4)));
           [rewrite hk_sv_SOff0; exact E48 | cbn; lia | cbn; lia |].
         replace (hx_P x + cc + 4) with (hx_P x + (cc + 4)) by lia.
         apply (hgw_pod_u32 _ (hx_P x) (hx_bs x) (cc + 4) HG); unfold hx_len in *; lia.
      -- apply (chunk_ok_val rsegs _ _ _ 8 4 (SOff 49 0) (Spa.u32_at (hx_bs x) (cc + 8)));
           [rewrite hk_sv_SOff0; exact E49 | cbn; lia | cbn; lia |].
         replace (hx_P x + cc + 8) with (hx_P x + (cc + 8)) by lia.
         specialize (Hb12 eq_refl).
         apply (hgw_pod_u32 _ (hx_P x) (hx_bs x) (cc + 8) HG); unfold hx_len in *; lia.
  + apply pairwise_disjoint_of_extents. unfold extent_of_region, hk_temps, pbV_podr.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E2, B23.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold T_parse_STK, T_PARSE_FRAME, ESTACK in *.
    destruct big; [specialize (Hb12 eq_refl)|]; repeat split; lia.
  + split; [|split; [exact I | exact I]]. cbn [f_atoms].
    apply (hk_atoms_ok B x regs L _ Hc HCR). cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite B23, B47, B48, B49, B50. change (2 ^ 3) with 8. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
    assert (Hb4 : big = true -> 4 <= Spa.u32_at (hx_bs x) cc)
      by (intros Hb; rewrite Hb in Hbig; symmetry in Hbig; apply Z.leb_le in Hbig; exact Hbig).
    destruct big; [specialize (Hb4 eq_refl)|specialize (Hb8 eq_refl)]; cbn [af_lo af_hi af_al2];
    change (2 ^ 0) with 1; rewrite ?Z.mod_1_r; repeat split; lia.
- unfold sh_ok, pbV_shV. constructor; [|constructor].
  apply (hk_shent_pod B x _ mem _ 23 cc 0 (if big then 12 else 8) Hc Hn E27 E23 HRA); [lia | lia | destruct big; lia |].
  destruct big; [specialize (Hb12 eq_refl)|]; lia.
Qed.

(* ---------------------------------- VAL ---------------------------------- *)
Lemma pbV_mk_REF : forall x r cc n ch p cl keys rf F fc regs mem md,
  pbV_core x r cc n ch p cl keys rf F fc regs mem md ->
  getr regs 14 = w64 (hx_P x + r + 16) -> getr regs 16 = w64 8 -> getr regs 17 = w64 (shadow_addr (hx_P x + cc)) ->
  getr regs 5 = w64 5 -> hp_vcell ch p (Spa.child_at (hx_bs x) cc) = inl Headamp.REFUSE_OUT_OF_RANGE ->
  REF_at x r cc n ch p cl keys rf F fc regs mem md.
Proof. intros x r cc n ch p cl keys rf F fc regs mem md H1 H2 H3 H4 H5 H6. exact (conj H1 (conj (conj H2 H3) (conj H4 (conj H5 H6)))). Qed.

(* a register at a run's end: kept from the entry, or the run's value *)
Ltac pbV_rv E0 regs HAE D48 :=
lazymatch goal with |- getr _ ?q = _ =>
  first [ (let z := eval vm_compute in (Z.to_nat (bv_unsigned q)) in pbV_rkeep E0 regs HAE z q; assumption)
        | (pbV_rg HAE; first [ reflexivity | exact D48 | (rewrite hk_sv_SOff0; exact (hk_env_seg _ _ _ _)) ]) ] end.

Lemma pbV_val : forall x r cc n ch p cl keys rf, call_ok B x ->
  REF_ok x r cc n ch p cl keys rf -> (forall v, TAIL_ok x r cc n ch p cl keys rf v) -> FLT_ok x r cc n ch p cl keys rf ->
  VAL_ok B MT x r cc n ch p cl keys rf.
Proof.
intros x r cc n ch p cl keys rf Hc HREF HTAIL HFLT F fc regs mem md HV.
unfold REF_ok, TAIL_ok, FLT_ok, cfg_at in *.
pose proof pb_wx as Hwx. pose proof pb_segs_low as Hsegs.
pose proof (pbV_core_of_VAL x r cc n ch p cl keys rf F fc regs mem md HV) as HK0.
destruct (pbV_entryV x r cc n ch p cl keys rf F fc regs mem md (4 <=? Spa.u32_at (hx_bs x) cc) Hc HV eq_refl)
  as [HS SHOK].
destruct HV as (Hcore & Hfx & Hm & HL & H46 & H23 & H24 & H13 & H11 & H17 & V24 & V48).
pose proof Hm as (Hn & _ & _ & _ & _ & _ & (Hcap & Hk & Hrf) & _ & _ & Hres).
pose proof (hk_core_cregs B x _ _ _ _ _ _ Hcore) as HCR.
pose proof HCR as (H2 & _ & _ & _ & _ & _ & _ & _ & H27).
pose proof Hcore as ((HJ & HOK & HPAT) & _).
pose proof (pbV_spa x Hc) as (S1 & S2 & S3 & S4).
pose proof (pbV_pc x r cc n ch p cl keys rf Hc Hm) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9).
pose proof alloc_ceiling_value as [[C1 C2] _].
pose proof (hgw_u32_range (hx_bs x) cc) as U0.
pose proof (hgw_u32_range (hx_bs x) (cc + 4)) as U4.
pose proof (hgw_u32_range (hx_bs x) (cc + 8)) as U8.
destruct H46 as (H14 & H16).
set (L := pbV_LV x r cc keys rf) in HS, SHOK.
assert (HAE : env_agree 53 (hk_env x regs L) (hk_env x regs L)) by apply env_agree_refl.
assert (B20 : bv_unsigned (ew (hk_env x regs L) 2) = hx_spa x).
{ rewrite (hk_env_reg x regs L 2 2%bv eq_refl), H2. unfold w64. apply unsigned_lit_small. lia. }
assert (E23 : ew (hk_env x regs L) 23 = w64 (hx_P x + cc)) by (rewrite (hk_env_reg x regs L 23 23%bv eq_refl); exact H23).
assert (E27 : ew (hk_env x regs L) 27 = w64 SHADOW_OFF) by (rewrite (hk_env_reg x regs L 27 27%bv eq_refl); exact H27).
assert (E47 : ew (hk_env x regs L) 47 = w64 (Spa.u32_at (hx_bs x) cc)) by exact (hk_env_seg x regs L 0).
assert (E48 : ew (hk_env x regs L) 48 = w64 (Spa.u32_at (hx_bs x) (cc + 4))) by exact (hk_env_seg x regs L 1).
assert (E49 : ew (hk_env x regs L) 49 = w64 (Spa.u32_at (hx_bs x) (cc + 8))) by exact (hk_env_seg x regs L 2).
assert (D48 : sv_denot (hk_env x regs L) pbV_s7sh = w64 (shadow_addr (hx_P x + cc))).
{ rewrite denot_lit_U, (pbV_U_s7sh _ (hx_P x + cc) E23 E27 ltac:(lia)). reflexivity. }
assert (KW : forall a, 0 <= a < 2 ^ 64 -> ~ (hx_spa x + 0 <= a < hx_spa x + 0x80) ->
  mrestrict (w_H (hx_W x)) mem (Z_to_bv 64 a) = mrestrict (w_H (hx_W x)) mem (Z_to_bv 64 a)) by reflexivity.
change (w64 PC_VAL) with (Z_to_bv 64 PC_VAL).
destruct (4 <=? Spa.u32_at (hx_bs x) cc) eqn:Ebig.
- apply Z.leb_le in Ebig.
  (* 0x84f0c .. 0x84f20: CS >> 20 <> 0 -> REF *)
  pbV_run x Hc HAE B20. pbV_br Hb1; pbV_hc HAE Hb1;
  rewrite (pbV_br_big _ 47 (Spa.u32_at (hx_bs x) cc) E47 U0) in Hb1.
  + apply negb_true_iff, Z.ltb_ge in Hb1.
    pbV_run_to x Hc HAE B20 PC_REF.
    pbV_prep x HAE B20. apply (HREF F fc _ _ _).
    apply pbV_mk_REF; [pbV_cmk (hk_env x regs L) regs HAE D48 Hc HK0 Q5 | pbV_rv (hk_env x regs L) regs HAE D48 .. |].
    apply pbV_vcell_none, pbV_res_big. lia.
  + apply negb_false_iff, Z.ltb_lt in Hb1.
    (* 0x84f24 .. 0x84f4c: the type; bne type,2 *)
    pbV_run x Hc HAE B20. pbV_br Hb2; pbV_hc HAE Hb2;
    rewrite (pbV_br_ty _ 48 (Spa.u32_at (hx_bs x) (cc + 4)) 2 E48 U4 ltac:(lia)) in Hb2.
    * apply negb_true_iff, Z.eqb_neq in Hb2.
      (* 0x84f6c .. 0x84f74: bne type,4 *)
      pbV_run x Hc HAE B20. pbV_br Hb3; pbV_hc HAE Hb3;
      rewrite (pbV_br_ty _ 48 (Spa.u32_at (hx_bs x) (cc + 4)) 4 E48 U4 ltac:(lia)) in Hb3.
      -- apply negb_true_iff, Z.eqb_neq in Hb3.
         (* 0x85050 .. 0x85058: bne type,6 *)
         pbV_run x Hc HAE B20. pbV_br Hb4; pbV_hc HAE Hb4;
         rewrite (pbV_br_ty _ 48 (Spa.u32_at (hx_bs x) (cc + 4)) 6 E48 U4 ltac:(lia)) in Hb4.
         ++ (* another type: 0x85118 -> REF *)
            apply negb_true_iff, Z.eqb_neq in Hb4.
            pbV_run_to x Hc HAE B20 PC_REF.
            pbV_prep x HAE B20. apply (HREF F fc _ _ _).
            apply pbV_mk_REF; [pbV_cmk (hk_env x regs L) regs HAE D48 Hc HK0 Q5 | pbV_rv (hk_env x regs L) regs HAE D48 .. |].
            apply pbV_vcell_none, pbV_res_bad; [lia | right; repeat split; assumption].
         ++ (* Float: 0x8505c .. 0x850a8, FLT *)
            apply negb_false_iff, Z.eqb_eq in Hb4.
            pbV_run_to x Hc HAE B20 PC_FLT.
            pbV_prep x HAE B20. apply (HFLT F fc _ _ _).
            refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))).
            ** pbV_cmk (hk_env x regs L) regs HAE D48 Hc HK0 Q5.
            ** pbV_rv (hk_env x regs L) regs HAE D48.
            ** pbV_rv (hk_env x regs L) regs HAE D48.
            ** pbV_rv (hk_env x regs L) regs HAE D48.
            ** pbV_rv (hk_env x regs L) regs HAE D48.
            ** pbV_rv (hk_env x regs L) regs HAE D48.
            ** pbV_rv (hk_env x regs L) regs HAE D48.
            ** lazymatch goal with HFV : forall (off : Z) (nn : N) (e : sv) (v : Z), _,
                 B2 : bv_unsigned (ew _ 2) = hx_spa _, HS : st_ok _ _ ?ss _ |- _ =>
                 let m := eval vm_compute in (ss_mem ss) in
                 lazymatch m with YP09.mkRegion _ _ _ _ _ ?cs :: _ =>
                   let e := eval vm_compute in (pbV_cat cs 56) in
                   rewrite <- B2; apply (HFV 56 4%N e); [cbn [In]; tauto | | cbn; lia | cbn; lia]
                 end end.
               lazymatch goal with |- sv_denot ?E ?e = _ =>
                 try rewrite (sv_denot_agree _ (hk_env x regs L) E e HAE) by (vm_compute; reflexivity) end.
               rewrite denot_lit_U. f_equal. apply (pbV_U_asm _ 49 _ E49 U8).
            ** apply pbV_res_flt; lia.
      -- (* Int: 0x84f78 .. 0x84f90, bltu 255,a2 *)
         apply negb_false_iff, Z.eqb_eq in Hb3.
         pbV_run x Hc HAE B20. pbV_br Hb4; pbV_hc HAE Hb4;
         rewrite (pbV_br_int _ 49 (Spa.u32_at (hx_bs x) (cc + 8)) E49 U8) in Hb4.
         ++ (* the body > 255: REF *)
            apply Z.ltb_lt in Hb4.
            pbV_run_to x Hc HAE B20 PC_REF.
            pbV_prep x HAE B20. apply (HREF F fc _ _ _).
            apply pbV_mk_REF; [pbV_cmk (hk_env x regs L) regs HAE D48 Hc HK0 Q5 | pbV_rv (hk_env x regs L) regs HAE D48 .. |].
            apply pbV_vcell_none. rewrite (pbV_res_int (hx_bs x) cc ltac:(lia) ltac:(lia) Hb3).
            rewrite (pbV_int_out _ U8 Hb4). reflexivity.
         ++ (* the body in [0, 255]: 0x84f94 .. 0x84f9c, TAIL *)
            apply Z.ltb_ge in Hb4.
            pbV_run_to x Hc HAE B20 PC_TAIL.
            pbV_prep x HAE B20. apply (HTAIL (Spa.u32_at (hx_bs x) (cc + 8)) F fc _ _ _).
            refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))))).
            ** pbV_cmk (hk_env x regs L) regs HAE D48 Hc HK0 Q5.
            ** pbV_rv (hk_env x regs L) regs HAE D48.
            ** pbV_rv (hk_env x regs L) regs HAE D48.
            ** pbV_rv (hk_env x regs L) regs HAE D48.
            ** pbV_rg HAE. rewrite denot_lit_U, (pbV_U_sx _ 49 _ E49 U8), (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
            ** lia.
            ** pbV_rv (hk_env x regs L) regs HAE D48.
            ** pbV_rv (hk_env x regs L) regs HAE D48.
            ** pbV_rv (hk_env x regs L) regs HAE D48.
            ** rewrite (pbV_res_int (hx_bs x) cc ltac:(lia) ltac:(lia) Hb3).
               destruct (pbV_int_in _ U8 Hb4) as [-> ->]. reflexivity.
    * (* Bool: 0x84f50 .. 0x84f68, TAIL *)
      apply negb_false_iff, Z.eqb_eq in Hb2.
      pbV_run_to x Hc HAE B20 PC_TAIL.
      pbV_prep x HAE B20.
      apply (HTAIL (if Spa.u32_at (hx_bs x) (cc + 8) =? 0 then 0 else 1) F fc _ _ _).
      refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))))).
      -- pbV_cmk (hk_env x regs L) regs HAE D48 Hc HK0 Q5.
      -- pbV_rv (hk_env x regs L) regs HAE D48.
      -- pbV_rv (hk_env x regs L) regs HAE D48.
      -- pbV_rv (hk_env x regs L) regs HAE D48.
      -- pbV_rg HAE. rewrite denot_lit_U, (pbV_U_snez _ 49 _ E49 U8). reflexivity.
      -- destruct (_ =? 0); lia.
      -- pbV_rv (hk_env x regs L) regs HAE D48.
      -- pbV_rv (hk_env x regs L) regs HAE D48.
      -- pbV_rv (hk_env x regs L) regs HAE D48.
      -- apply pbV_res_bool; lia.
- (* CS < 4: 0x84f0c .. 0x85128, REF *)
  apply Z.leb_gt in Ebig.
  pbV_run x Hc HAE B20. pbV_br Hb1; pbV_hc HAE Hb1;
  rewrite (pbV_br_big _ 47 (Spa.u32_at (hx_bs x) cc) E47 U0) in Hb1;
  [apply negb_true_iff, Z.ltb_ge in Hb1; lia | apply negb_false_iff, Z.ltb_lt in Hb1].
  pbV_run_to x Hc HAE B20 PC_REF.
  pbV_prep x HAE B20. apply (HREF F fc _ _ _).
  apply pbV_mk_REF; [pbV_cmk (hk_env x regs L) regs HAE D48 Hc HK0 Q5 | pbV_rv (hk_env x regs L) regs HAE D48 .. |].
  apply pbV_vcell_none, pbV_res_bad; [lia | left; lia].
Qed.
(* ---------------------------------- TAIL ---------------------------------- *)
Lemma pbV_mk_EXIT : forall x r cc n ch p cl keys rf F fc regs mem md cv,
  pbV_core x r cc n ch p cl keys rf F fc regs mem md -> getr regs 25 = w64 (keys + 1) ->
  hp_vcell ch p (Spa.child_at (hx_bs x) cc) = inr cv -> hx_cap x <= Z.of_nat (length cl) ->
  EXIT_at B x cl (keys + 1) rf F fc regs mem md.
Proof.
intros x r cc n ch p cl keys rf F fc regs mem md cv (Hcore & (Hfx & _) & Hm & (L20 & _ & _ & _ & L32 & _) & _) H25 Hv Hn.
exact (conj Hcore (conj Hfx (conj (pbV_m_exit x r cc n ch p cl keys rf cv Hm Hv Hn) (conj L20 (conj H25 L32))))).
Qed.

Lemma pbV_entryT : forall x r cc n ch p cl keys rf v F fc regs mem md (a1 : Z), call_ok B x ->
  TAIL_at x r cc n ch p cl keys rf v F fc regs mem md -> getr regs 11 = w64 a1 -> 0 <= a1 <= 1 ->
  st_ok (fx := mkFP F fc) rsegs (hk_env x regs (pbV_LR x r keys rf)) (pbV_ssT a1)
    (restrict (w_H (hx_W x)) (@mkst (mkFP F fc) regs (Z_to_bv 64 PC_TAIL) mem (seg_rom rsegs))).
Proof.
intros x r cc n ch p cl keys rf v F fc regs mem md a1 Hc HT H11 Ha1.
destruct HT as (HK & _ & _ & _ & H12 & Hv & _).
pose proof HK as (Hcore & _ & Hm & HL & _ & _ & _).
pose proof Hm as (_ & _ & _ & _ & _ & _ & (Hcap & _ & Hrf) & _).
pose proof (hk_core_cregs B x _ _ _ _ _ _ Hcore) as HCR.
pose proof HCR as (H2 & _ & _ & _ & _ & H18 & _).
pose proof (hk_out B x Hc) as (Hc9 & _).
pose proof (pbV_spa x Hc) as (S1 & S2 & S3 & S4).
pose proof (pbV_pc x r cc n ch p cl keys rf Hc Hm) as (Q1 & Q2 & Q3 & Q4 & Q5 & _).
pose proof (hgw_u32_range (hx_bs x) cc) as U0.
pose proof alloc_ceiling_value as [[C1 C2] _].
destruct HL as (L20 & _).
set (L := pbV_LR x r keys rf).
assert (E2 : bv_unsigned (ew (hk_env x regs L) 2) = hx_spa x).
{ rewrite (hk_env_reg x regs L 2 2%bv eq_refl), H2. unfold w64. apply unsigned_lit_small. lia. }
assert (E11 : bv_unsigned (ew (hk_env x regs L) 11) = a1).
{ rewrite (hk_env_reg x regs L 11 11%bv eq_refl), H11. unfold w64. apply unsigned_lit_small. lia. }
assert (E12 : bv_unsigned (ew (hk_env x regs L) 12) = v).
{ rewrite (hk_env_reg x regs L 12 12%bv eq_refl), H12. unfold w64. apply unsigned_lit_small. lia. }
assert (E18 : bv_unsigned (ew (hk_env x regs L) 18) = hx_cap x).
{ rewrite (hk_env_reg x regs L 18 18%bv eq_refl), H18. unfold w64. apply unsigned_lit_small. lia. }
assert (E20 : bv_unsigned (ew (hk_env x regs L) 20) = Z.of_nat (length cl)).
{ rewrite (hk_env_reg x regs L 20 20%bv eq_refl), L20. unfold w64. apply unsigned_lit_small. lia. }
rewrite restrict_mkst_fx. unfold pbV_ssT, hk_env. apply (entry_st_ok_full (fx := mkFP F fc) rsegs);
  fold (hk_env x regs L).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor].
  apply (hk_temps_ok B x PAT_KEY cl (ha_res_bytes 0 0 0) regs mem md L _ Hc Hcore).
  apply (pbV_tcs_ok x r cc n ch p cl keys rf F fc regs mem md L 47 48 49 HK);
  first [exact (hk_env_seg x regs L 0) | exact (hk_env_seg x regs L 1) | exact (hk_env_seg x regs L 2) | lia].
- cbn [pairwise_disjoint all_disjoint]. tauto.
- split; [|split; [exact I | exact I]]. cbn [f_atoms].
  apply (hk_atoms_ok B x regs L _ Hc HCR). cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E11, E12, E18, E20. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia.
Qed.

Lemma pbV_tail : forall x r cc n ch p cl keys rf v, call_ok B x ->
  REF_ok x r cc n ch p cl keys rf -> EXIT_ok B MT x -> CELL_ok x r cc n ch p cl keys rf v ->
  TAIL_ok x r cc n ch p cl keys rf v.
Proof.
intros x r cc n ch p cl keys rf v Hc HREF HEXIT HCELL F fc regs mem md HT.
unfold REF_ok, CELL_ok, EXIT_ok, cfg_at in *.
pose proof pb_wx as Hwx. pose proof pb_segs_low as Hsegs.
pose proof HT as (HK0 & H24 & H13 & H11 & H12 & Hv & H16 & H17 & H5 & Hpv).
pose proof HK0 as (Hcore & Hfx & Hm & HL & H23 & V24 & V48).
pose proof Hm as (Hn & (Hr16 & _) & _ & _ & _ & _ & (Hcap & Hk & Hrf) & Hch & Hp & Hres).
pose proof (hk_core_cregs B x _ _ _ _ _ _ Hcore) as HCR.
pose proof HCR as (H2 & _ & _ & _ & _ & H18 & _ & _ & H27).
pose proof Hcore as ((HJ & HOK & HPAT) & _).
pose proof (hk_out B x Hc) as (Hc9 & _).
pose proof (pbV_spa x Hc) as (S1 & S2 & S3 & S4).
pose proof (pbV_pc x r cc n ch p cl keys rf Hc Hm) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9).
pose proof alloc_ceiling_value as [[C1 C2] _].
pose proof (hgw_u32_range (hx_bs x) cc) as U0.
pose proof (pbV_vcell_some ch p _ v Hp Hpv) as Hvc.
destruct HL as (L20 & L21 & L22 & L16 & L32 & L40).
set (L := pbV_LR x r keys rf).
assert (HAE : env_agree 50 (hk_env x regs L) (hk_env x regs L)) by apply env_agree_refl.
assert (SHOK : sh_ok rsegs hk_Bx [] (hk_env x regs L) (mrestrict (w_H (hx_W x)) mem)) by constructor.
assert (B20 : bv_unsigned (ew (hk_env x regs L) 2) = hx_spa x).
{ rewrite (hk_env_reg x regs L 2 2%bv eq_refl), H2. unfold w64. apply unsigned_lit_small. lia. }
assert (E12 : ew (hk_env x regs L) 12 = w64 v) by (rewrite (hk_env_reg x regs L 12 12%bv eq_refl); exact H12).
assert (E18 : ew (hk_env x regs L) 18 = w64 (hx_cap x)) by (rewrite (hk_env_reg x regs L 18 18%bv eq_refl); exact H18).
assert (E20 : ew (hk_env x regs L) 20 = w64 (Z.of_nat (length cl)))
  by (rewrite (hk_env_reg x regs L 20 20%bv eq_refl); exact L20).
assert (E23 : ew (hk_env x regs L) 23 = w64 (hx_P x + cc)) by (rewrite (hk_env_reg x regs L 23 23%bv eq_refl); exact H23).
assert (E27 : ew (hk_env x regs L) 27 = w64 SHADOW_OFF) by (rewrite (hk_env_reg x regs L 27 27%bv eq_refl); exact H27).
assert (D48 : sv_denot (hk_env x regs L) pbV_s7sh = w64 (shadow_addr (hx_P x + cc))).
{ rewrite denot_lit_U, (pbV_U_s7sh _ (hx_P x + cc) E23 E27 ltac:(lia)). reflexivity. }
assert (KW : forall a, 0 <= a < 2 ^ 64 -> ~ (hx_spa x + 0 <= a < hx_spa x + 0x80) ->
  mrestrict (w_H (hx_W x)) mem (Z_to_bv 64 a) = mrestrict (w_H (hx_W x)) mem (Z_to_bv 64 a)) by reflexivity.
change (w64 PC_TAIL) with (Z_to_bv 64 PC_TAIL).
destruct (p =? Headamp.HA_SENS) eqn:Ep;
[ pose proof (pbV_entryT x r cc n ch p cl keys rf v F fc regs mem md 0 Hc HT ltac:((try rewrite Ep in H11); exact H11) ltac:(lia)) as HS
| pose proof (pbV_entryT x r cc n ch p cl keys rf v F fc regs mem md 1 Hc HT ltac:((try rewrite Ep in H11); exact H11) ltac:(lia)) as HS ].
all: fold L in HS; (try rewrite Ep in Hvc); cbv beta iota in Hvc.
(* 0x84fa0 .. 0x84fb0 / 0x84fbc *)
all: pbV_run x Hc HAE B20.
(* 0x84fa8 beqz a1 with a1 = 0, when the run stops there *)
all: try (lazymatch goal with HS : st_ok _ _ ?ss _ |- _ => let pc := eval vm_compute in (ss_pc ss) in constr_eq pc 544680 end;
     pbV_br Hb0; pbV_hc HAE Hb0;
     rewrite branch_eq_U, (U_atom _ 11 0 ltac:(rewrite (hk_env_reg x regs L 11 11%bv eq_refl); (try rewrite Ep in H11);
       exact H11) ltac:(lia)), U_lit in Hb0 by lia;
     [ pbV_run x Hc HAE B20 | vm_compute in Hb0; discriminate Hb0 ]).
all: pbV_br Hb1; pbV_hc HAE Hb1; rewrite branch_geu_U, (pbV_U_zb _ 12 v E12 Hv), U_lit in Hb1 by lia.
(* v >= the bound: REF *)
1,3: apply negb_true_iff, Z.ltb_ge in Hb1;
  pbV_run_to x Hc HAE B20 PC_REF;
  pbV_prep x HAE B20; apply (HREF F fc _ _ _);
  apply pbV_mk_REF; [pbV_cmk (hk_env x regs L) regs HAE D48 Hc HK0 Q5 | pbV_rv (hk_env x regs L) regs HAE D48 .. |];
  rewrite Hvc, (proj2 (Z.ltb_ge _ _) Hb1); reflexivity.
(* 0x84fc0 bge s4,s2 *)
all: apply negb_false_iff, Z.ltb_lt in Hb1;
  pbV_run x Hc HAE B20; pbV_br Hb2; pbV_hc HAE Hb2;
  rewrite (pbV_br_ge _ 20 18 (Z.of_nat (length cl)) (hx_cap x) E20 E18 ltac:(lia) ltac:(lia)) in Hb2.
(* no room: 0x85214 .. EXIT *)
1,3: apply Z.leb_le in Hb2;
  pbV_run_to x Hc HAE B20 PC_EXIT;
  pbV_prep x HAE B20; apply (HEXIT cl (keys + 1) rf F fc _ _ _);
  apply (pbV_mk_EXIT x r cc n ch p cl keys rf F fc _ _ _ (ch, p, v));
  [ pbV_cmk (hk_env x regs L) regs HAE D48 Hc HK0 Q5 | pbV_rv (hk_env x regs L) regs HAE D48
  | rewrite Hvc, (proj2 (Z.ltb_lt _ _) Hb1); reflexivity | exact Hb2 ].
(* room: CELL *)
all: apply Z.leb_gt in Hb2;
  pbV_run_to x Hc HAE B20 PC_CELL;
  pbV_prep x HAE B20; apply (HCELL F fc _ _ _);
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))));
  [ pbV_cmk (hk_env x regs L) regs HAE D48 Hc HK0 Q5 | pbV_rv (hk_env x regs L) regs HAE D48
  | pbV_rv (hk_env x regs L) regs HAE D48 | pbV_rv (hk_env x regs L) regs HAE D48 | exact Hv
  | pbV_rv (hk_env x regs L) regs HAE D48 | pbV_rv (hk_env x regs L) regs HAE D48
  | pbV_rv (hk_env x regs L) regs HAE D48
  | rewrite Hvc, (proj2 (Z.ltb_lt _ _) Hb1); reflexivity | exact Hb2 ].
Qed.
(* ---------------------------------- FLT ---------------------------------- *)
Lemma pbV_core_regs : forall x r cc n ch p cl keys rf F fc regs mem md G fc' regs2 X,
  pbV_core x r cc n ch p cl keys rf F fc regs mem md -> hp_fxw G fc' ->
  getr regs2 2 = getr regs 2 -> getr regs2 3 = getr regs 3 -> getr regs2 4 = getr regs 4 ->
  getr regs2 8 = getr regs 8 -> getr regs2 9 = getr regs 9 -> getr regs2 18 = getr regs 18 ->
  getr regs2 19 = getr regs 19 -> getr regs2 26 = getr regs 26 -> getr regs2 27 = getr regs 27 ->
  getr regs2 20 = getr regs 20 -> getr regs2 21 = getr regs 21 -> getr regs2 22 = getr regs 22 ->
  getr regs2 23 = getr regs 23 ->
  pbV_core x r cc n ch p cl keys rf G fc' regs2 mem (with_vm_backing (m_vm_lazy md) X md).
Proof.
intros x r cc n ch p cl keys rf F fc regs mem md G fc' regs2 X (Hcore & _ & Hm & (L20 & L21 & L22 & L16 & L32 & L40) & H23 & V24 & V48)
  Hfx R2 R3 R4 R8 R9 R18 R19 R26 R27 R20 R21 R22 R23.
pose proof (hk_core_cregs B x _ _ _ _ _ _ Hcore) as HCR.
refine (conj _ (conj Hfx (conj Hm (conj _ (conj _ (conj V24 V48)))))).
- apply (hk_core_wvb B pb_segs_low). apply (hk_core_regs B x _ _ _ regs mem md regs2 Hcore).
  apply (hk_cregs_same x regs regs2 HCR); assumption.
- unfold pb_loop. rewrite R20, R21, R22. repeat split; assumption.
- rewrite R23. exact H23.
Qed.

(* a register after hand steps, through the steps' frame facts *)
Ltac pbV_rch :=
repeat match goal with H : forall r : bv 5, _ |- getr ?R ?q = _ =>
  progress (rewrite H by (vm_compute; lia)) end; first [reflexivity | assumption].

Lemma pbV_ff_set14 : forall (G : bvmap 5 word) (k : bv 5) v, bv_unsigned k <> 14 ->
  Sem.reg_get (bvmap_set 14 v G) k = Sem.reg_get G k.
Proof. intros G k v Hk. apply (pbV_fsz G 14 k v 14 eq_refl). lia. Qed.

Lemma pbV_flt : forall x r cc n ch p cl keys rf, call_ok B x ->
  REF_ok x r cc n ch p cl keys rf -> (forall v, TAIL_ok x r cc n ch p cl keys rf v) -> FLT_ok x r cc n ch p cl keys rf.
Proof.
intros x r cc n ch p cl keys rf Hc HREF HTAIL F fc regs mem md HF.
unfold REF_ok, TAIL_ok, cfg_at in *.
destruct HF as (HK0 & H24 & H13 & H11 & H16 & H17 & H5 & V56 & Hpv).
pose proof HK0 as (Hcore & Hfx & Hm & HL & H23 & V24 & V48).
pose proof Hm as (Hn & (Hr16 & _) & _ & _ & _ & _ & (Hcap & Hk & Hrf) & Hch & Hp & Hres).
pose proof (hk_core_cregs B x _ _ _ _ _ _ Hcore) as HCR.
pose proof HCR as (H2 & _).
pose proof Hfx as ((HFk & HZ) & H8).
pose proof (pbV_spa x Hc) as (S1 & S2 & S3 & S4).
pose proof (pbV_pc x r cc n ch p cl keys rf Hc Hm) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9).
pose proof (hgw_u32_range (hx_bs x) (cc + 8)) as Hb.
pose proof (hgw_u32_range (hx_bs x) cc) as U0.
pose proof alloc_ceiling_value as [[C1 C2] _].
destruct HL as (L20 & L21 & L22 & L16 & L32 & L40).
(* the four read-only doubles, at the cut *)
destruct (hk_call_args B x Hc) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hro0 & _).
assert (Hro : hd_ro_cells rsegs (w_H (hx_W x)) mem (hi_dcs headamp_himg_B)).
{ apply (hk_ro_cells_at_cut B pb_segs_low x PAT_KEY cl (ha_res_bytes 0 0 0) regs mem md _ Hc Hcore ltac:(lia) Hro0).
  change (hi_dcs headamp_himg_B) with headamp_B_dcs. unfold headamp_B_dcs.
  repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; intros kk Hkk; (split;
  [ lazymatch goal with |- in_img _ (?a + kk) =>
      apply (HPgSat.img_chk_ok rsegs a 8 ltac:(vm_compute; reflexivity) kk); lia end | rewrite HBerrno; lia ]). }
unfold hd_ro_cells in Hro. rewrite Forall_forall in Hro.
assert (DH : val_mem rsegs (mrestrict (w_H (hx_W x)) mem) 0x10380 8 PB_D_HALF)
  by (apply (Hro (0x10380, PB_D_HALF)); vm_compute; auto).
assert (D256 : val_mem rsegs (mrestrict (w_H (hx_W x)) mem) 0x10340 8 PB_D_256)
  by (apply (Hro (0x10340, PB_D_256)); vm_compute; auto).
assert (DCLO : val_mem rsegs (mrestrict (w_H (hx_W x)) mem) 0x103f0 8 PB_D_CLO)
  by (apply (Hro (0x103f0, PB_D_CLO)); vm_compute; auto).
assert (DCHI : val_mem rsegs (mrestrict (w_H (hx_W x)) mem) 0x10358 8 PB_D_CHI)
  by (apply (Hro (0x10358, PB_D_CHI)); vm_compute; auto).
clear Hro Hro0.
set (b := Spa.u32_at (hx_bs x) (cc + 8)) in *.
assert (HS48 : 0 <= shadow_addr (hx_P x + cc) < 2 ^ 64) by (unfold shadow_addr, SHADOW_OFF; lia).
(* 0x850ac .. 0x850c0 *)
destruct (pbV_fA (mrestrict (w_H (hx_W x)) mem) F fc regs b (hx_spa x) HZ ltac:(exact H8) H2 Hb V56 DH)
  as (C3 & G1 & R1 & P1 & HC1 & HG1 & HG15 & HR10 & HR1k).
assert (HF1 : hp_fxw G1 C3) by exact (pbV_fxw_keep F fc G1 C3 Hfx HG1 HC1).
destruct (FP.fle_d (Z_to_bv 64 0) (ParseFP.rfn_d b)) eqn:Efle; (try rewrite Efle in HR10).
- (* 0x850c4 .. 0x850d0 *)
  destruct (pbV_fB (mrestrict (w_H (hx_W x)) mem) G1 C3 R1 b HC1 HG15 HR10 D256) as (C4 & R2 & P2 & HC2 & HR20 & HR2k).
  assert (HF2 : hp_fxw (bvmap_set 14 (Z_to_bv 64 PB_D_256) G1) C4).
  { apply (pbV_fxw_keep F fc _ C4 Hfx); [|exact HC2]. intros k H14 H15. rewrite (pbV_ff_set14 G1 k _ H14). apply HG1; assumption. }
  destruct (FP.flt_d (ParseFP.rfn_d b) (Z_to_bv 64 PB_D_256)) eqn:Eflt; (try rewrite Eflt in HR20).
  + (* in range: 0x850d4 .. 0x85114, 0x84f94 .. 0x84f9c, TAIL *)
    assert (Hin : ParseFP.rfn_in b (Z_to_bv 64 0) (Z_to_bv 64 4643211215818981376) = true).
    { rewrite hfp_rfn_in, Efle. exact Eflt. }
    pose proof (hfp_in_t_range b Hb Hin) as TR.
    destruct (pbV_fC (mrestrict (w_H (hx_W x)) mem) (bvmap_set 14 (Z_to_bv 64 PB_D_256) G1) C4 R2 (ParseFP.rfn_d b)
      (ParseFP.rfn_t b) (hx_spa x) (shadow_addr (hx_P x + cc)) HC2
      ltac:(rewrite (pbV_ff_set14 G1 15 _ ltac:(vm_compute; lia)); exact HG15) HR20
      (hfp_in_cast_lo b Hb Hin) (hfp_in_cast_hi b Hb Hin) (hfp_rfn_t b) ltac:(lia)
      ltac:(rewrite (HR2k 2%bv ltac:(vm_compute; lia)), (HR1k 2%bv ltac:(vm_compute; lia)); exact H2)
      V48 HS48 DCLO DCHI) as (C5 & G3 & R3 & P3 & HC3 & HG3 & HR312 & HR316 & HR317 & HR35 & HR3k).
    assert (HF3 : hp_fxw G3 C5).
    { apply (pbV_fxw_keep F fc _ C5 Hfx); [|exact HC3]. intros k H14 H15.
      rewrite (HG3 k H14), (pbV_ff_set14 G1 k _ H14). apply HG1; assumption. }
    eapply (SRr_msteps rsegs pb_wx).
    { rewrite restrict_mkst_fx. eapply msteps_trans; [exact P1|]. eapply msteps_trans; [exact P2|]. exact P3. }
    intros md' Hsame Hcl. rewrite (same_but_materialized_wvb md md' Hsame), unrestrict_mkst_mrestrict.
    pose proof (hfp_nearest b Hb) as HN. rewrite Hin in HN.
    apply (HTAIL (ParseFP.rfn_r b) G3 C5 R3 mem _).
    refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))))).
    * apply (pbV_core_regs x r cc n ch p cl keys rf F fc regs mem md G3 C5 R3 _ HK0 HF3); pbV_rch.
    * pbV_rch.
    * pbV_rch.
    * pbV_rch.
    * rewrite HR312, <- hfp_floor_B. reflexivity.
    * exact (Headamp.nearest_range b 0 255 _ HN).
    * exact HR316.
    * exact HR317.
    * exact HR35.
    * rewrite Hpv. exact HN.
  + (* 256.0 or more: 0x850d4 -> 0x85118 .. 0x85128, REF *)
    destruct (pbV_fRef (mrestrict (w_H (hx_W x)) mem) (mkFP (bvmap_set 14 (Z_to_bv 64 PB_D_256) G1) C4) R2 (hx_spa x)
      (hx_P x + r + 16) (shadow_addr (hx_P x + cc))
      ltac:(rewrite (HR2k 2%bv ltac:(vm_compute; lia)), (HR1k 2%bv ltac:(vm_compute; lia)); exact H2)
      L40 ltac:(lia) V48 HS48) as (R3 & P3 & HR314 & HR316 & HR317 & HR35 & HR3k).
    eapply (SRr_msteps rsegs pb_wx).
    { rewrite restrict_mkst_fx. eapply msteps_trans; [exact P1|]. eapply msteps_trans; [exact P2|].
      eapply mst_step; [reflexivity | exact (pbV_fB_ref (mrestrict (w_H (hx_W x)) mem) _ R2 HR20) | exact P3]. }
    intros md' Hsame Hcl. rewrite (same_but_materialized_wvb md md' Hsame), unrestrict_mkst_mrestrict.
    apply (HREF (bvmap_set 14 (Z_to_bv 64 PB_D_256) G1) C4 R3 mem _).
    apply pbV_mk_REF; [ apply (pbV_core_regs x r cc n ch p cl keys rf F fc regs mem md _ C4 R3 _ HK0 HF2); pbV_rch
                      | exact HR314 | exact HR316 | exact HR317 | exact HR35 |].
    apply pbV_vcell_none. rewrite Hpv, (hfp_nearest b Hb), hfp_rfn_in, Efle. unfold PB_D_256 in Eflt. rewrite Eflt. reflexivity.
- (* below +0.0: 0x850c4 -> 0x85118 .. 0x85128, REF *)
  destruct (pbV_fRef (mrestrict (w_H (hx_W x)) mem) (mkFP G1 C3) R1 (hx_spa x)
    (hx_P x + r + 16) (shadow_addr (hx_P x + cc))
    ltac:(rewrite (HR1k 2%bv ltac:(vm_compute; lia)); exact H2)
    L40 ltac:(lia) V48 HS48) as (R3 & P3 & HR314 & HR316 & HR317 & HR35 & HR3k).
  eapply (SRr_msteps rsegs pb_wx).
  { rewrite restrict_mkst_fx. eapply msteps_trans; [exact P1|].
    eapply mst_step; [reflexivity | exact (pbV_fA_ref (mrestrict (w_H (hx_W x)) mem) _ R1 HR10) | exact P3]. }
  intros md' Hsame Hcl. rewrite (same_but_materialized_wvb md md' Hsame), unrestrict_mkst_mrestrict.
  apply (HREF G1 C3 R3 mem _).
  apply pbV_mk_REF; [ apply (pbV_core_regs x r cc n ch p cl keys rf F fc regs mem md _ C3 R3 _ HK0 HF1); pbV_rch
                    | exact HR314 | exact HR316 | exact HR317 | exact HR35 |].
  apply pbV_vcell_none. rewrite Hpv, (hfp_nearest b Hb), hfp_rfn_in, Efle. reflexivity.
Qed.
(* ---------------------------------- CELL ---------------------------------- *)
(* the bytes CELL's runs may write: the frame temporaries and the cell out[3 n, 3 n + 3) *)
Definition pbV_W (x : pctx) (cl : list Headamp.cell) (a : Z) : Prop :=
(hx_spa x <= a < hx_spa x + 0x80) \/
(hx_O x + 3 * Z.of_nat (length cl) <= a < hx_O x + 3 * Z.of_nat (length cl) + 3).

Lemma pbV_keptP : forall E rs (H : word -> bool) (m0 m1 m2 : word -> option byte) (Wp : Z -> Prop),
(forall a, 0 <= a < 2 ^ 64 -> ~ Wp a -> mrestrict H m1 (Z_to_bv 64 a) = mrestrict H m0 (Z_to_bv 64 a)) ->
frame_of E rs (mrestrict H m1) (mrestrict H m2) ->
(forall a, in_wrange E rs a -> Wp a) ->
forall a, 0 <= a < 2 ^ 64 -> ~ Wp a -> mrestrict H m2 (Z_to_bv 64 a) = mrestrict H m0 (Z_to_bv 64 a).
Proof.
intros E rs H m0 m1 m2 Wp HK HF HW a Ha Hn.
rewrite <- (HK a Ha Hn). apply HF. rewrite unsigned_lit_small by exact Ha. intros X. exact (Hn (HW a X)).
Qed.

Lemma pbV_view_kept : forall (x : pctx) (Wp : Z -> Prop) mem mem2,
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wp a ->
   mrestrict (w_H (hx_W x)) mem2 (Z_to_bv 64 a) = mrestrict (w_H (hx_W x)) mem (Z_to_bv 64 a)) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ Wp a -> hx_view x mem2 a = hx_view x mem a.
Proof. intros x Wp mem mem2 KW a Ha Hn. unfold hx_view, aview, mbyte. rewrite (KW a Ha Hn). reflexivity. Qed.


Lemma pbV_cells_app : forall (cl : list Headamp.cell) (ch p v : Z), 0 <= ch < 256 -> 0 <= p < 256 -> 0 <= v < 256 ->
  hd_zbytes (ha_cells_bytes (cl ++ [(ch, p, v)])) = hd_zbytes (ha_cells_bytes cl) ++ [ch; p; v].
Proof.
intros cl ch p v Hch Hp Hv. unfold ha_cells_bytes, hd_zbytes. rewrite flat_map_app, map_app.
cbn [flat_map ha_cell_bytes map app]. rewrite !Z_to_bv_unsigned.
rewrite !bv_wrap_small by (unfold bv_modulus; cbn [Z.of_N]; lia). reflexivity.
Qed.

Lemma pbV_cells_len : forall cl, length (hd_zbytes (ha_cells_bytes cl)) = (3 * length cl)%nat.
Proof.
intros cl. unfold hd_zbytes. rewrite length_map. induction cl as [|[[a b] c] l IH]; [reflexivity|].
unfold ha_cells_bytes in *. cbn [flat_map]. rewrite length_app, IH. cbn [ha_cell_bytes length]. lia.
Qed.

Ltac pbV_Bk HAE B0 k E Bk :=
lazymatch type of B0 with bv_unsigned (ew _ k) = ?F =>
assert (Bk : bv_unsigned (ew E k) = F) by (first [exact B0 | rewrite (proj1 HAE k ltac:(lia)); exact B0]) end.
Ltac pbV_awrC x Hc HAE B20 B500 :=
lazymatch goal with |- awr_okH ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own ?U =>
let B2 := fresh "B2" in pbV_B2 HAE B20 E B2;
let B5 := fresh "B5" in pbV_Bk HAE B500 50%nat E B5;
let rs' := eval vm_compute in rs in change (awr_okH E rs' stk sp0 fp b0 bc ly own U);
repeat first
[ apply awr_okH_nil
| apply awr_okH_cons_ro; [cbn; lia|]
| apply (hk_awr_temps _ x E _ _ U Hc B2)
| (lazymatch type of B5 with _ = ?bv =>
     eapply (hk_awr_out _ x E _ _ U 50%nat bv Hc); [reflexivity | exact B5 | cbn [YP09.r_wlo YP09.r_whi]; intros ? ?; lia | ] end) ]
end.
Ltac pbV_keepC x cl HAE B20 B500 :=
lazymatch goal with HFr : frame_of ?E _ (mrestrict _ _) (mrestrict _ _),
  KW : forall a, _ -> ~ _ -> mrestrict _ _ (Z_to_bv 64 a) = _ |- _ =>
let B2 := fresh "B2" in pbV_B2 HAE B20 E B2;
let B5 := fresh "B5" in pbV_Bk HAE B500 50%nat E B5;
let KS := fresh "KS" in
pose proof (pbV_keptP _ _ _ _ _ _ (pbV_W x cl) KW HFr) as KS;
lazymatch type of KS with ?P -> _ => let KX := fresh "KX" in assert (KX : P) by (
  let a := fresh "a" in let rg := fresh "rg" in let Hrg := fresh "Hrg" in let Hb := fresh "Hb" in
  intros a (rg & Hrg & Hb);
  lazymatch type of Hrg with In _ ?rs => let rs' := eval vm_compute in rs in change (In rg rs') in Hrg end;
  unfold pbV_W;
  repeat (destruct Hrg as [<- | Hrg]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb;
     first [rewrite B2 in Hb; lia | rewrite B5 in Hb; lia | lia] | ]);
  destruct Hrg);
  specialize (KS KX); clear KX KW HFr B2 B5; rename KS into KW end
end;
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
Ltac pbV_runC x cl Hc HAE B20 B500 :=
lazymatch goal with HS : st_ok _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
aj_run_tokH pb_tbl_ok HS HJ SHOK hk_Bspan; [ idtac .. | solve [pbV_awrC x Hc HAE B20 B500] | pbV_keepC x cl HAE B20 B500; pbV_upd HAE] end.
Ltac pbV_run_toC x cl Hc HAE B20 B500 stop :=
lazymatch goal with HS : st_ok _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
aj_run_to_tokH pb_tbl_ok HS HJ SHOK hk_Bspan stop; [ idtac .. | solve [pbV_awrC x Hc HAE B20 B500] | pbV_keepC x cl HAE B20 B500; pbV_upd HAE] end.

Definition pbV_LC (x : pctx) (r keys rf : Z) (cl : list Headamp.cell) : list word :=
[w64 rf; w64 (keys + 1); w64 (hx_P x + r + 16); w64 (hx_O x + 3 * Z.of_nat (length cl))].

Lemma pbV_entryC : forall x r cc n ch p cl keys rf v F fc regs mem md, call_ok B x ->
  CELL_at x r cc n ch p cl keys rf v F fc regs mem md ->
  st_ok (fx := mkFP F fc) rsegs (hk_env x regs (pbV_LC x r keys rf cl)) pbV_ssC
    (restrict (w_H (hx_W x)) (@mkst (mkFP F fc) regs (Z_to_bv 64 PC_CELL) mem (seg_rom rsegs))) /\
  sh_ok rsegs hk_Bx pbV_shC (hk_env x regs (pbV_LC x r keys rf cl)) (mrestrict (w_H (hx_W x)) mem).
Proof.
intros x r cc n ch p cl keys rf v F fc regs mem md Hc HC.
destruct HC as (HK & _ & _ & _ & _ & _ & _ & _ & _ & Hlt).
pose proof HK as (Hcore & _ & Hm & HL & _ & _ & _).
pose proof Hm as (_ & _ & _ & _ & _ & _ & (Hcap & _ & Hrf) & _).
pose proof (hk_core_cregs B x _ _ _ _ _ _ Hcore) as HCR.
pose proof HCR as (H2 & _ & _ & _ & _ & _ & H19 & _ & H27).
pose proof (hk_out B x Hc) as (Hc9 & HO0 & _ & _ & HO16 & HO4096 & HOc & HOapp & _).
pose proof (hk_out_at_cut B pb_segs_low x PAT_KEY cl (ha_res_bytes 0 0 0) regs mem md errno_low Hc Hcore ltac:(lia))
  as (HRAo & Hpres).
pose proof (pbV_spa x Hc) as (S1 & S2 & S3 & S4).
pose proof (pbV_pc x r cc n ch p cl keys rf Hc Hm) as (Q1 & Q2 & Q3 & Q4 & Q5 & _).
pose proof (hgw_u32_range (hx_bs x) cc) as U0.
pose proof alloc_ceiling_value as [[C1 C2] _].
destruct HL as (L20 & _).
set (L := pbV_LC x r keys rf cl).
assert (E2 : bv_unsigned (ew (hk_env x regs L) 2) = hx_spa x).
{ rewrite (hk_env_reg x regs L 2 2%bv eq_refl), H2. unfold w64. apply unsigned_lit_small. lia. }
assert (E19 : ew (hk_env x regs L) 19 = w64 (hx_O x)) by (rewrite (hk_env_reg x regs L 19 19%bv eq_refl); exact H19).
assert (E20 : ew (hk_env x regs L) 20 = w64 (Z.of_nat (length cl)))
  by (rewrite (hk_env_reg x regs L 20 20%bv eq_refl); exact L20).
assert (E27 : ew (hk_env x regs L) 27 = w64 SHADOW_OFF) by (rewrite (hk_env_reg x regs L 27 27%bv eq_refl); exact H27).
assert (E50 : ew (hk_env x regs L) 50 = w64 (hx_O x + 3 * Z.of_nat (length cl))) by exact (hk_env_seg x regs L 3).
assert (B19 : bv_unsigned (ew (hk_env x regs L) 19) = hx_O x).
{ rewrite E19. unfold w64. apply unsigned_lit_small. lia. }
assert (B20' : bv_unsigned (ew (hk_env x regs L) 20) = Z.of_nat (length cl)).
{ rewrite E20. unfold w64. apply unsigned_lit_small. lia. }
assert (B50 : bv_unsigned (ew (hk_env x regs L) 50) = hx_O x + 3 * Z.of_nat (length cl)).
{ rewrite E50. unfold w64. apply unsigned_lit_small. lia. }
rewrite restrict_mkst_fx. split.
- unfold pbV_ssC, hk_env. apply (entry_st_ok_full (fx := mkFP F fc) rsegs); fold (hk_env x regs L).
  + apply regs_ok_Ereg.
  + vm_compute. reflexivity.
  + constructor; [|constructor; [|constructor]].
    * apply (hk_temps_ok B x PAT_KEY cl (ha_res_bytes 0 0 0) regs mem md L _ Hc Hcore).
      apply (pbV_tcs_ok x r cc n ch p cl keys rf F fc regs mem md L 47 48 49 HK);
      first [exact (hk_env_seg x regs L 0) | exact (hk_env_seg x regs L 1) | exact (hk_env_seg x regs L 2) | lia].
    * unfold region_ok, pbV_outr. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite B50. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable rsegs). apply Hpres. lia.
  + apply pairwise_disjoint_of_extents. unfold extent_of_region, hk_temps, pbV_outr.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E2, B50.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  + split; [|split; [exact I | split; [|exact I]]].
    * cbn [f_atoms]. apply (hk_atoms_ok B x regs L _ Hc HCR). cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite B19, B20', B50. change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
      repeat split; lia.
    * apply (pbV_oal_ok _ (hx_O x) (Z.of_nat (length cl)) E19 E20 E50); lia.
- unfold sh_ok, pbV_shC. constructor; [|constructor].
  apply (hk_shent_out B x _ mem _ 50 (3 * Z.of_nat (length cl)) 0 3 Hc E27 E50 HRAo); lia.
Qed.

Ltac pbV_dcell HAE E0 := lazymatch goal with |- sv_denot ?E ?e = _ =>
  (try rewrite (sv_denot_agree _ E0 E e HAE) by (vm_compute; reflexivity)); rewrite hk_sv_SOff0 end.

Lemma pbV_cell : forall x r cc n ch p cl keys rf v, call_ok B x ->
  (forall cl' rf', ADV_ok B MT x r cc n None cl' (keys + 1) rf') -> CELL_ok x r cc n ch p cl keys rf v.
Proof.
intros x r cc n ch p cl keys rf v Hc HADV F fc regs mem md HC.
unfold ADV_ok, cfg_at in *.
pose proof pb_wx as Hwx. pose proof pb_segs_low as Hsegs.
destruct (pbV_entryC x r cc n ch p cl keys rf v F fc regs mem md Hc HC) as [HS SHOK].
destruct HC as (HK0 & H24 & H13 & H12 & Hv & H16 & H17 & H14 & Hvc & Hlt).
pose proof HK0 as (Hcore & Hfx & Hm & HL & H23 & V24 & V48).
pose proof Hm as (Hn & (Hr16 & _) & _ & _ & _ & _ & (Hcap & Hk & Hrf) & Hch & Hp & Hres).
pose proof (hk_core_cregs B x _ _ _ _ _ _ Hcore) as HCR.
pose proof HCR as (H2 & _ & _ & _ & _ & H18 & H19 & _ & H27).
pose proof Hcore as ((HJ & HOK & HPAT) & _).
pose proof (hk_out B x Hc) as (Hc9 & HO0 & _ & _ & HO16 & HO4096 & HOc & HOapp & _).
pose proof (pbV_spa x Hc) as (S1 & S2 & S3 & S4).
pose proof (pbV_pc x r cc n ch p cl keys rf Hc Hm) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9).
pose proof alloc_ceiling_value as [[C1 C2] _].
pose proof (hgw_u32_range (hx_bs x) cc) as U0.
destruct HL as (L20 & L21 & L22 & L16 & L32 & L40).
set (L := pbV_LC x r keys rf cl) in HS, SHOK.
assert (HAE : env_agree 51 (hk_env x regs L) (hk_env x regs L)) by apply env_agree_refl.
assert (B20 : bv_unsigned (ew (hk_env x regs L) 2) = hx_spa x).
{ rewrite (hk_env_reg x regs L 2 2%bv eq_refl), H2. unfold w64. apply unsigned_lit_small. lia. }
assert (B500 : bv_unsigned (ew (hk_env x regs L) 50) = hx_O x + 3 * Z.of_nat (length cl)).
{ rewrite (hk_env_seg x regs L 3). cbn [nth L pbV_LC]. unfold w64. apply unsigned_lit_small. lia. }
assert (E19 : ew (hk_env x regs L) 19 = w64 (hx_O x)) by (rewrite (hk_env_reg x regs L 19 19%bv eq_refl); exact H19).
assert (E23 : ew (hk_env x regs L) 23 = w64 (hx_P x + cc)) by (rewrite (hk_env_reg x regs L 23 23%bv eq_refl); exact H23).
assert (E27 : ew (hk_env x regs L) 27 = w64 SHADOW_OFF) by (rewrite (hk_env_reg x regs L 27 27%bv eq_refl); exact H27).
assert (D48 : sv_denot (hk_env x regs L) pbV_s7sh = w64 (shadow_addr (hx_P x + cc))).
{ rewrite denot_lit_U, (pbV_U_s7sh _ (hx_P x + cc) E23 E27 ltac:(lia)). reflexivity. }
assert (KW : forall a, 0 <= a < 2 ^ 64 -> ~ pbV_W x cl a ->
  mrestrict (w_H (hx_W x)) mem (Z_to_bv 64 a) = mrestrict (w_H (hx_W x)) mem (Z_to_bv 64 a)) by reflexivity.
change (w64 PC_CELL) with (Z_to_bv 64 PC_CELL).
assert (E50 : ew (hk_env x regs L) 50 = w64 (hx_O x + 3 * Z.of_nat (length cl))) by exact (hk_env_seg x regs L 3).
assert (Hch8 : 0 <= ch < 256) by (unfold Headamp.REAC_HEADAMP_MAX_CH in Hch; lia).
assert (Hp8 : 0 <= p < 256) by (unfold Headamp.HA_SENS in Hp; lia).
(* 0x84fc4 .. 0x84fec: the checks of out + 3 n; the one at 0x84fec is not taken (out + 3 n >= out) *)
pbV_runC x cl Hc HAE B20 B500.
pbV_br Hb1; pbV_hc HAE Hb1;
rewrite (pbV_br_wrap _ (hx_O x) (hx_O x + 3 * Z.of_nat (length cl)) E19 E50 ltac:(lia) ltac:(lia)) in Hb1;
[ discriminate Hb1 | ].
(* 0x84ff0 .. 0x8504c: the three stores, s4 = n + 1, s9, a4, a7; ADV *)
pbV_run_toC x cl Hc HAE B20 B500 PC_ADV.
lazymatch goal with HS : st_ok _ ?E ?ss (restrict _ ?ms) |- _ =>
  let B2 := fresh "B2" in pbV_B2 HAE B20 E B2;
  let B5 := fresh "B5" in pbV_Bk HAE B500 50%nat E B5;
  let m := eval vm_compute in (ss_mem ss) in
  lazymatch m with YP09.mkRegion _ _ _ _ _ ?cs :: YP09.mkRegion _ _ _ _ _ ?co :: ?rest =>
    let Hmem := fresh "Hmem" in
    assert (Hmem : ss_mem ss = YP09.mkRegion (Some 2%nat) 0 0x80 0 0x80 cs :: YP09.mkRegion (Some 50%nat) 0 3 0 3 co :: rest)
      by (vm_compute; reflexivity);
    let HFV := fresh "HFV" in
    pose proof (fun off nn e v => pbV_tval E ss ms (w_H (hx_W x)) _ cs off nn e v HS Hmem) as HFV;
    let HFO := fresh "HFO" in
    pose proof (fun off nn e v => pbV_tval2 E ss ms (w_H (hx_W x)) _ rest co off nn e v HS Hmem) as HFO;
    (* the cell's three bytes *)
    assert (NB : forall j, (j < 3)%nat ->
      val_mem rsegs (hx_rd x (ms_mem ms)) (hx_O x + 3 * Z.of_nat (length cl) + Z.of_nat j) 1 (nth j (ch :: p :: v :: nil) 0))
    by (intros j Hj; rewrite <- B5; destruct j as [|[|[|j]]];
        [ apply (HFO 0 1%N (SOff 24 0) ch);
          [ cbn [In]; tauto | pbV_dcell HAE (hk_env x regs L); rewrite (hk_env_reg x regs L 24 24%bv eq_refl); exact H24
          | cbn; lia | cbn; lia ]
        | apply (HFO 1 1%N (SOff 13 0) p);
          [ cbn [In]; tauto | pbV_dcell HAE (hk_env x regs L); rewrite (hk_env_reg x regs L 13 13%bv eq_refl); exact H13
          | cbn; lia | cbn; lia ]
        | apply (HFO 2 1%N (SOff 12 0) v);
          [ cbn [In]; tauto | pbV_dcell HAE (hk_env x regs L); rewrite (hk_env_reg x regs L 12 12%bv eq_refl); exact H12
          | cbn; lia | cbn; lia ]
        | lia ])
  end;
  rewrite (st_ok_restrict_mkst rsegs (w_H (hx_W x)) _ _ _ HS ltac:(vm_compute; reflexivity));
  let pc := eval vm_compute in (ss_pc ss) in change (ss_pc ss) with pc
end.
try clear HFO.
apply (HADV (cl ++ [(ch, p, v)]) rf F fc _ _ _).
apply pbV_mk_ADV.
- (* the core with the cell appended *)
  eapply (hk_core_step B pb_segs_low x PAT_KEY PAT_KEY cl _ (ha_res_bytes 0 0 0) (ha_res_bytes 0 0 0) regs mem md _ _ _
    (pbV_W x cl) errno_low Hc Hcore).
  + rewrite length_app. cbn [length]. lia.
  + rewrite length_app. cbn [length]. lia.
  + apply (pbV_view_kept x (pbV_W x cl) mem _ KW).
  + intros a [Ha|Ha].
    * left. pose proof (hk_frame_win B x Hc) as (W1 & W2 & _). lia.
    * right; right. unfold hp_pw. left. rewrite length_app. cbn [length]. lia.
  + eassumption.
  + reflexivity.
  + unfold PAT_KEY. repeat (apply Forall_cons; [lia|]). apply Forall_nil.
  + apply (hk_hpat_kept x mem _ PAT_KEY); [|exact HPAT].
    intros i Hi. cbn [PAT_KEY length Z.of_nat] in Hi.
    assert (HH : hp_hole x (hx_shf x + i)) by (unfold hp_hole; lia).
    pose proof (hk_hole_band B x _ Hc HH) as (HB1 & HB2).
    apply (pbV_view_kept x (pbV_W x cl) mem _ KW); [unfold SHADOW_OFF, kHighShadowEnd in *; lia|].
    intros [Hw|Hw]; [lia|].
    destruct (pxg_out_apart B _ _ _ _ _ _ _ x (hx_shf x + i - hx_O x) Hc ltac:(lia)) as (_ & Hnh & _).
    apply Hnh. replace (hx_O x + (hx_shf x + i - hx_O x)) with (hx_shf x + i) by lia. exact HH.
  + pbV_kio.
  + rewrite (pbV_cells_app cl ch p v Hch8 Hp8 ltac:(lia)).
    apply garr8_app. split.
    * apply (hk_garr8_kept x mem _ (hx_O x) _); [|exact (proj1 (hk_core_cells B x _ _ _ _ _ _ Hcore))].
      rewrite pbV_cells_len. intros a Ha.
      apply (pbV_view_kept x (pbV_W x cl) mem _ KW); [lia|].
      intros [Hw|Hw]; [|lia].
      destruct (pxg_out_apart B _ _ _ _ _ _ _ x (a - hx_O x) Hc ltac:(lia)) as (Hst & _).
      apply Hst. replace (hx_O x + (a - hx_O x)) with a by lia.
      pose proof (hk_frame_win B x Hc) as (W1 & W2 & _). lia.
    * rewrite pbV_cells_len. intros j Hj. cbn [length] in Hj.
      replace (hx_O x + Z.of_nat (3 * length cl) + Z.of_nat j) with (hx_O x + 3 * Z.of_nat (length cl) + Z.of_nat j) by lia.
      split; [exact (NB j Hj)|]. destruct j as [|[|[|j]]]; cbn [nth]; lia.
  + intros HR0. pose proof (hk_res B pb_segs_low x Hc HR0) as (_ & _ & _ & HRa).
    apply (hk_garr8_kept x mem _ (hx_R x) _); [|exact (proj1 (proj2 (hk_core_cells B x _ _ _ _ _ _ Hcore)) HR0)].
    intros a Ha. change (length (hd_zbytes (ha_res_bytes 0 0 0))) with 12%nat in Ha. cbn [Z.of_nat] in Ha.
    destruct (HRa a ltac:(lia)) as (_ & _ & HRr).
    apply (pbV_view_kept x (pbV_W x cl) mem _ KW); [unfold app_addr, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in HRr; lia|].
    intros [Hw|Hw].
    * destruct (pxg_res_apart B pb_segs_low _ _ _ _ _ _ _ x (a - hx_R x) Hc HR0 ltac:(lia)) as (Hst & _).
      apply Hst. replace (hx_R x + (a - hx_R x)) with a by lia.
      pose proof (hk_frame_win B x Hc) as (W1 & W2 & _). lia.
    * destruct (pxg_out_apart B _ _ _ _ _ _ _ x (a - hx_O x) Hc ltac:(lia)) as (_ & _ & _ & HnR & _).
      apply (HnR HR0). lia.
  + destruct (proj2 (proj2 (hk_core_cells B x _ _ _ _ _ _ Hcore))) as (ev & Hev). exists ev.
    apply (hk_rd32_kept (hx_view x mem) _ (as_errno B) ev); [|exact Hev].
    intros kk Hkk. rewrite HBerrno.
    apply (pbV_view_kept x (pbV_W x cl) mem _ KW); [lia|].
    intros [Hw|Hw]; [lia|].
    destruct (pxg_out_apart B _ _ _ _ _ _ _ x (0x5d812c + kk - hx_O x) Hc ltac:(lia)) as (_ & _ & Hni & _).
    apply Hni. replace (hx_O x + (0x5d812c + kk - hx_O x)) with (0x5d812c + kk) by lia.
    exact (HPgSat.img_chk_ok rsegs 0x5d812c 4 ltac:(vm_compute; reflexivity) kk ltac:(lia)).
  + apply (hk_cregs_same x regs _ HCR); pbV_rk (hk_env x regs L) regs HAE.
- exact Hfx.
- exact (pbV_m_cell x r cc n ch p cl keys rf (ch, p, v) Hm Hvc Hlt).
- unfold pb_loop. refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
  + pbV_rg HAE. rewrite length_app. cbn [length]. unfold w64. cbn [sv_denot].
    rewrite (hk_env_reg x regs L 20 20%bv eq_refl), L20. unfold w64. rewrite unsigned_lit_small by lia. f_equal. lia.
  + pbV_rv (hk_env x regs L) regs HAE D48.
  + pbV_rv (hk_env x regs L) regs HAE D48.
  + rewrite Q5. pbV_tmp (hk_env x regs L) HAE D48.
  + pbV_tmp (hk_env x regs L) HAE D48.
  + pbV_tmp (hk_env x regs L) HAE D48.
- split; pbV_rv (hk_env x regs L) regs HAE D48.
- pbV_rv (hk_env x regs L) regs HAE D48.
- pbV_rv (hk_env x regs L) regs HAE D48.
- pbV_rv (hk_env x regs L) regs HAE D48.
- pbV_rv (hk_env x regs L) regs HAE D48.
Qed.
(* ---------------------------------- the segment ---------------------------------- *)
Theorem segVAL_ok : segVAL_stmt B MT.
Proof.
intros x r cc n ch p cl keys rf Hc HADV HEXIT.
pose proof (pbV_ref x r cc n ch p cl keys rf Hc HADV) as HREF.
assert (HTAIL : forall v, TAIL_ok x r cc n ch p cl keys rf v).
{ intros v. apply (pbV_tail x r cc n ch p cl keys rf v Hc HREF HEXIT). exact (pbV_cell x r cc n ch p cl keys rf v Hc HADV). }
exact (pbV_val x r cc n ch p cl keys rf Hc HREF HTAIL (pbV_flt x r cc n ch p cl keys rf Hc HREF HTAIL)).
Qed.
End seg.
