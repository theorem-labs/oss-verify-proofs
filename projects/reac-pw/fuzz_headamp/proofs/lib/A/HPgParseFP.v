(* reac_headamp_prop_parse_result of reac-pw/fuzz_headamp, both ASan images: the binary64 steps of the inlined
   reac_float_nearest (src/reac_float_near.h:24-34), image A 0x84cb4 .. 0x84ce8 and image B 0x850a8 .. 0x8510c, as
   lemmas a walk applies, and their values read against Pod/Nearest.v [nearest] at the reader's bounds [0, 255]
   through Prog/ParseFP.v. No image is Required: no address, no table, no segment list is fixed here.

   The code (image B; image A is the same up to the 256.0 test, then fcvt.l.d a0 / fcvt.d.l / flt.d a1 / sub):
     sw a0,56(sp); flw fa5,56(sp); auipc; fld fa4 (0.5); fcvt.d.s fa5,fa5 (rm 0); fadd.d fa5,fa5,fa4 (rm dyn);
     fle.d a0,fs0,fa5 (fs0 = +0.0 from fmv.d.x fs0,zero); beqz; fld fa4 (256.0); flt.d a0,fa5,fa4; beqz;
     fld fa4 (-2^63 - 2^11); flt.d a0,fa4,fa5; beqz trap; fld fa4 (2^63); flt.d a0,fa5,fa4; beqz trap;
     fcvt.l.d a2,fa5,rtz; fcvt.d.l fa4,a2 (rm dyn); flt.d a0,fa5,fa4; beqz; addi a0,a2,-1; bge a0,a2 trap.
   Both prologues save fs0 (fsd fs0,144(sp)) and both epilogues reload it (fld fs0,144(sp)).

   - hp_step_*: one step of fcvt.d.s, fadd.d, fle.d, flt.d, fcvt.l.d, fcvt.d.l, any segments, any float state.
   - hfp_tw_*: flw, fld, fsd, fmv.d.x and the six double instructions at a literal pc p of any code table tbl with
     table_ok segs tbl (YP02.v: clookup tbl p = Some wz gives fetch_word segs p = Some wz), next pc q = p + 4. The
     premises clookup tbl p = Some wz, is_ecall (Z_to_bv 32 wz) = false and decode_any (Z_to_bv 32 wz) = Some (i, 4)
     are closed terms: a walk proves each by vm_compute; reflexivity on its own table.
   - the values: an 8-byte read-only cell (val_mem) as the bytes fld loads; the 4-byte word flw reads back after sw;
     the constants +0.0, 256.0, -2^63 - 2^11 and 2^63 as integers; nearest b 0 255 as the hardware's answer; when the
     range test passes, the two cast bounds image B tests, the ranges of t and r, and the floor forms (image A: sub,
     image B: addi -1 and the bge that does not jump).
   Proves no function (kind: helper lemmas for both images' value pieces). *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP09 YP02 YP0k YP03 YN3v YI04.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YN2e YO0f.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require FP.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Nearest.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog Require ParseFP.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* Modified by Theorem Labs, 2026-10: the exact flt.d / fcvt.d.wu steps of proofs/libreac/fuzz_disco/lib/Rt/FpStep.v at
   origin/ossv/recipes a34e09bd40c1 (fp_step_flt_d, fp_step_fcvt_d_wu) restated for fle.d, fcvt.d.s, fadd.d, fcvt.l.d and
   fcvt.d.l. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgParseFV.v at afaa3cb55c1 (lines 26-178, and the
   flw / fld / double forms of lines 312-466 restated over any code table); module paths changed, names hp_step_* and
   hfp_*; the rest is new. *)
(* ---- exact steps of the double instructions (any float state F / fc) ---- *)
Lemma hp_step_fcvt_d_s : forall (F : bvmap 5 word) (fc : bv 32) segs regs pc mem rom w (rd rs : bv 5) (rm : bv 3),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Fcvt FC_D FC_S rd rs rm, 4%Z) -> bv_unsigned rm = 0 ->
  RiscvSemantics.step segs (@mkst (mkFP F fc) regs pc mem rom) =
  MachineOk (@mkst (mkFP (bvmap_set rd (FP.fcvt_d_s RNE (Sem.reg_get F rs)) F)
      (Z_to_bv 32 (Z.lor (bv_unsigned fc)
         (fflags_bits (snd (fp_convert fmt_single fmt_double RNE (bv_unsigned (unbox_s (Sem.reg_get F rs)))))))))
    regs (v_addi pc 4) mem rom).
Proof.
intros F fc segs regs pc mem rom w rd rs rm Hf He Hd Hrm.
fp_pipeline Hf He Hd.
replace (rmode_of_field (bv_unsigned rm) (Z.land (Z.shiftr (bv_unsigned fc) 5) 7)) with (Some RNE)
  by (unfold rmode_of_field, rmode_of_Z; rewrite Hrm; reflexivity).
cbv beta iota. change (fp_format FMT_S) with fmt_single. change (fp_format FMT_D) with fmt_double. unfold FP.fcvt_d_s.
destruct (fp_convert fmt_single fmt_double RNE _) as [v fl]. cbn [fst snd]. rewrite b_npc4. reflexivity.
Qed.

Lemma hp_step_fadd_d : forall (F : bvmap 5 word) (fc : bv 32) segs regs pc mem rom w (rd rs1 rs2 : bv 5) (rm : bv 3),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Fari F_ADD FMT_D rd rs1 rs2 rm, 4%Z) -> bv_unsigned rm = 7 -> frm_zero fc ->
  RiscvSemantics.step segs (@mkst (mkFP F fc) regs pc mem rom) =
  MachineOk (@mkst (mkFP (bvmap_set rd (FP.fadd_d RNE (Sem.reg_get F rs1) (Sem.reg_get F rs2)) F)
      (Z_to_bv 32 (Z.lor (bv_unsigned fc)
         (fflags_bits (snd (fp_add fmt_double RNE (bv_unsigned (Sem.reg_get F rs1)) (bv_unsigned (Sem.reg_get F rs2))))))))
    regs (v_addi pc 4) mem rom).
Proof.
intros F fc segs regs pc mem rom w rd rs1 rs2 rm Hf He Hd Hrm Hz.
fp_pipeline Hf He Hd.
unfold frm_zero in Hz.
replace (rmode_of_field (bv_unsigned rm) (Z.land (Z.shiftr (bv_unsigned fc) 5) 7)) with (Some RNE)
  by (unfold rmode_of_field; rewrite Hrm, Hz; reflexivity).
cbv beta iota. change (fp_format FMT_D) with fmt_double. unfold FP.fadd_d.
destruct (fp_add fmt_double RNE _ _) as [v fl]. cbn [fst snd]. rewrite b_npc4. reflexivity.
Qed.

Lemma hp_step_fle_d : forall (F : bvmap 5 word) (fc : bv 32) segs regs pc mem rom w (rd rs1 rs2 : bv 5),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Fcmp F_LE FMT_D rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step segs (@mkst (mkFP F fc) regs pc mem rom) =
  MachineOk (@mkst (mkFP F (Z_to_bv 32 (Z.lor (bv_unsigned fc)
      (fflags_bits (FP.fcmp_fl F_LE fmt_double (bv_unsigned (Sem.reg_get F rs1)) (bv_unsigned (Sem.reg_get F rs2)))))))
    (if bv_eqb rd 0 then regs else regupd regs rd (if FP.fle_d (Sem.reg_get F rs1) (Sem.reg_get F rs2) then Z_to_bv 64 1 else Z_to_bv 64 0))
    (v_addi pc 4) mem rom).
Proof.
intros F fc segs regs pc mem rom w rd rs1 rs2 Hf He Hd.
assert (E1 : FP.fcmp_fl F_LE fmt_double (bv_unsigned (Sem.reg_get F rs1)) (bv_unsigned (Sem.reg_get F rs2))
  = snd (fp_le fmt_double (bv_unsigned (Sem.reg_get F rs1)) (bv_unsigned (Sem.reg_get F rs2)))) by reflexivity.
assert (E2 : FP.fle_d (Sem.reg_get F rs1) (Sem.reg_get F rs2)
  = fst (fp_le fmt_double (bv_unsigned (Sem.reg_get F rs1)) (bv_unsigned (Sem.reg_get F rs2)))) by reflexivity.
rewrite E1, E2.
fp_pipeline Hf He Hd.
cbv beta iota. change (fp_format FMT_D) with fmt_double.
destruct (fp_le fmt_double _ _) as [v fl]. cbn [fst snd].
rewrite b_npc4. unfold regupd. destruct (is_x0 rd); reflexivity.
Qed.

Lemma hp_step_flt_d : forall (F : bvmap 5 word) (fc : bv 32) segs regs pc mem rom w (rd rs1 rs2 : bv 5),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Fcmp F_LT FMT_D rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step segs (@mkst (mkFP F fc) regs pc mem rom) =
  MachineOk (@mkst (mkFP F (Z_to_bv 32 (Z.lor (bv_unsigned fc)
      (fflags_bits (FP.fcmp_fl F_LT fmt_double (bv_unsigned (Sem.reg_get F rs1)) (bv_unsigned (Sem.reg_get F rs2)))))))
    (if bv_eqb rd 0 then regs else regupd regs rd (if FP.flt_d (Sem.reg_get F rs1) (Sem.reg_get F rs2) then Z_to_bv 64 1 else Z_to_bv 64 0))
    (v_addi pc 4) mem rom).
Proof.
intros F fc segs regs pc mem rom w rd rs1 rs2 Hf He Hd.
assert (E1 : FP.fcmp_fl F_LT fmt_double (bv_unsigned (Sem.reg_get F rs1)) (bv_unsigned (Sem.reg_get F rs2))
  = snd (fp_lt fmt_double (bv_unsigned (Sem.reg_get F rs1)) (bv_unsigned (Sem.reg_get F rs2)))) by reflexivity.
assert (E2 : FP.flt_d (Sem.reg_get F rs1) (Sem.reg_get F rs2)
  = fst (fp_lt fmt_double (bv_unsigned (Sem.reg_get F rs1)) (bv_unsigned (Sem.reg_get F rs2)))) by reflexivity.
rewrite E1, E2.
fp_pipeline Hf He Hd.
cbv beta iota. change (fp_format FMT_D) with fmt_double.
destruct (fp_lt fmt_double _ _) as [v fl]. cbn [fst snd].
rewrite b_npc4. unfold regupd. destruct (is_x0 rd); reflexivity.
Qed.

Lemma hp_step_fcvt_l_d : forall (F : bvmap 5 word) (fc : bv 32) segs regs pc mem rom w (rd rs : bv 5) (rm : bv 3),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Fcvt FC_L FC_D rd rs rm, 4%Z) -> bv_unsigned rm = 1 ->
  RiscvSemantics.step segs (@mkst (mkFP F fc) regs pc mem rom) =
  MachineOk (@mkst (mkFP F (Z_to_bv 32 (Z.lor (bv_unsigned fc)
      (fflags_bits (snd (fp_to_int fmt_double RTZ true 64 (bv_unsigned (Sem.reg_get F rs))))))))
    (if bv_eqb rd 0 then regs else regupd regs rd (FP.fcvt_l_d RTZ (Sem.reg_get F rs)))
    (v_addi pc 4) mem rom).
Proof.
intros F fc segs regs pc mem rom w rd rs rm Hf He Hd Hrm.
fp_pipeline Hf He Hd.
replace (rmode_of_field (bv_unsigned rm) (Z.land (Z.shiftr (bv_unsigned fc) 5) 7)) with (Some RTZ)
  by (unfold rmode_of_field, rmode_of_Z; rewrite Hrm; reflexivity).
cbv beta iota. change (fp_format FMT_D) with fmt_double. unfold FP.fcvt_l_d.
destruct (fp_to_int fmt_double RTZ true 64 _) as [v fl]. cbn [fst snd].
rewrite b_npc4. unfold regupd. destruct (is_x0 rd); reflexivity.
Qed.

Lemma hp_step_fcvt_d_l : forall (F : bvmap 5 word) (fc : bv 32) segs regs pc mem rom w (rd rs : bv 5) (rm : bv 3),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Fcvt FC_D FC_L rd rs rm, 4%Z) -> bv_unsigned rm = 7 -> frm_zero fc ->
  RiscvSemantics.step segs (@mkst (mkFP F fc) regs pc mem rom) =
  MachineOk (@mkst (mkFP (bvmap_set rd (FP.fcvt_d_l RNE (getr regs rs)) F)
      (Z_to_bv 32 (Z.lor (bv_unsigned fc)
         (fflags_bits (snd (fp_of_int fmt_double RNE true 64 (bv_unsigned (getr regs rs))))))))
    regs (v_addi pc 4) mem rom).
Proof.
intros F fc segs regs pc mem rom w rd rs rm Hf He Hd Hrm Hz.
fp_pipeline Hf He Hd.
unfold frm_zero in Hz.
replace (rmode_of_field (bv_unsigned rm) (Z.land (Z.shiftr (bv_unsigned fc) 5) 7)) with (Some RNE)
  by (unfold rmode_of_field; rewrite Hrm, Hz; reflexivity).
cbv beta iota. change (fp_format FMT_D) with fmt_double.
replace (if is_x0 rs then Z_to_bv 64 0 else Sem.reg_get regs rs) with (getr regs rs) by reflexivity.
unfold FP.fcvt_d_l.
destruct (fp_of_int fmt_double RNE true 64 _) as [v fl]. cbn [fst snd]. rewrite b_npc4. reflexivity.
Qed.

(* ---- reading a value back out of memory ---- *)
Definition hfp_bytes (n : nat) (v : Z) : list byte := map (fun k => Z_to_bv 8 (YO0f.le_byte v n k)) (seq 0 n).

Lemma hfp_bytes_Z : forall n v, bytes_le_to_Z (hfp_bytes n v) = v mod 2 ^ (8 * Z.of_nat n).
Proof.
intros n v. pose proof (YN2e.bytes_le_to_Z_le_list_gen n v 0) as H.
cbn [Nat.add] in H. change (8 * Z.of_nat 0) with 0 in H. rewrite Z.shiftr_0_r in H. exact H.
Qed.

(* an 8-byte read-only cell (hd_ro_cells: val_mem of the restricted memory) read by fld *)
Lemma hfp_rdn8 : forall segs m a v, val_mem segs m a 8 v -> rdn segs m (Z_to_bv 64 a) 8 = Some (hfp_bytes 8 v).
Proof.
intros segs m a v H. apply (mbytes_at_rdn segs m a (hfp_bytes 8 v)).
intros j Hj. cbn [length hfp_bytes map seq] in Hj.
destruct j as [|[|[|[|[|[|[|[|j]]]]]]]]; try lia; cbn [nth_error hfp_bytes map seq]; apply H; lia.
Qed.

Lemma hfp_rdn4 : forall segs m a v, val_mem segs m a 4 v -> rdn segs m (Z_to_bv 64 a) 4 = Some (hfp_bytes 4 v).
Proof.
intros segs m a v H. apply (mbytes_at_rdn segs m a (hfp_bytes 4 v)).
intros j Hj. cbn [length hfp_bytes map seq] in Hj.
destruct j as [|[|[|[|j]]]]; try lia; cbn [nth_error hfp_bytes map seq]; apply H; lia.
Qed.

Lemma hfp_word8 : forall v, 0 <= v < 2 ^ 64 -> le_bytes_to_word (hfp_bytes 8 v) = Z_to_bv 64 v.
Proof.
intros v Hv. rewrite le_bytes_to_word_Z, hfp_bytes_Z. change (8 * Z.of_nat 8) with 64.
rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma hfp_word4 : forall v, 0 <= v < 2 ^ 32 -> le_bytes_to_word (hfp_bytes 4 v) = Z_to_bv 64 v.
Proof.
intros v Hv. rewrite le_bytes_to_word_Z, hfp_bytes_Z. change (8 * Z.of_nat 4) with 32.
rewrite Z.mod_small by lia. reflexivity.
Qed.

(* the 4 bytes sw writes, read back by flw: the low word of the stored register *)
Lemma hfp_rdn_sw : forall segs mem a (v : word), 0 <= a -> a + 4 <= 2 ^ 64 ->
  rdn segs (wbytes mem (Z_to_bv 64 a) (word_to_le_bytes 4 v)) (Z_to_bv 64 a) 4 = Some (word_to_le_bytes 4 v).
Proof.
intros segs mem a v Ha0 Ha4.
pose proof (rdn_wbytes_hit segs (word_to_le_bytes 4 v) mem (Z_to_bv 64 a)) as H.
rewrite length_N_to_le_bytes in H. apply H.
rewrite unsigned_lit_small by lia. change (Z.of_nat 4) with 4. lia.
Qed.

Lemma hfp_word4_low : forall v : word, bv_extract 0 32 (le_bytes_to_word (word_to_le_bytes 4 v)) = low32 v.
Proof.
intros v. rewrite le_bytes_to_word_Z, bytes_le_N.
change (bv_extract 0 32 (Z_to_bv 64 (bv_unsigned v mod 2 ^ (8 * Z.of_nat 4))))
  with (low32 (Z_to_bv 64 (bv_unsigned v mod 2 ^ (8 * Z.of_nat 4)))).
rewrite low32_lit. unfold low32. apply bv_eq.
rewrite bv_extract_unsigned, Z.shiftr_0_r, Z_to_bv_unsigned.
unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32). change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32).
apply Zmod_mod.
Qed.

(* ---- pc arithmetic ---- *)
Lemma hfp_addi_lit : forall z i, v_addi (Z_to_bv 64 z) i = Z_to_bv 64 (z + i).
Proof.
intros z i. unfold v_addi. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 64) with (2 ^ 64). apply Zplus_mod_idemp_l.
Qed.

(* ======== the float instructions at a literal pc of any code table ======== *)
Section tw.
Variable segs : list Segment.
Variable tbl : ctable.
Hypothesis tbl_ok : table_ok segs tbl.

(* flw of a 4-byte cell holding v *)
Lemma hfp_tw_flw : forall (fs : YK11.FPState) regs mem rom p q wz rd rs (imm : bv 12) base a v,
  clookup tbl p = Some wz -> is_ecall (Z_to_bv 32 wz) = false ->
  decode_any (Z_to_bv 32 wz) = Some (FLoad FMT_S rd rs imm, 4%Z) -> q = p + 4 ->
  getr regs rs = Z_to_bv 64 base -> a = base + bv_signed imm ->
  0 <= v < 2 ^ 32 -> val_mem segs mem a 4 v ->
  RiscvSemantics.step segs (@mkst fs regs (Z_to_bv 64 p) mem rom) =
  MachineOk (@mkst (mkFP (bvmap_set rd (nan_box (Z_to_bv 32 v)) (@fp_regs fs)) (@fp_csr fs))
    regs (Z_to_bv 64 q) mem rom).
Proof.
intros fs regs mem rom p q wz rd rs imm base a v Hc He Hd Hq Hrs Ha Hv HM.
rewrite (fp_step_flw fs segs regs (Z_to_bv 64 p) mem rom (Z_to_bv 32 wz) rd rs imm
  (v_addi (getr regs rs) (bv_signed imm)) (hfp_bytes 4 v)
  (tbl_ok p wz Hc) He Hd eq_refl).
- cbn [fp_regs fp_csr]. rewrite Hq, hfp_addi_lit, hfp_word4 by lia.
  change (bv_extract 0 32 (Z_to_bv 64 v)) with (low32 (Z_to_bv 64 v)). rewrite low32_lit. reflexivity.
- rewrite Hrs, hfp_addi_lit, <- Ha. apply hfp_rdn4. exact HM.
Qed.

(* flw of any 4 bytes bs *)
Lemma hfp_tw_flw_rdn : forall (fs : YK11.FPState) regs mem rom p q wz rd rs (imm : bv 12) base a bs,
  clookup tbl p = Some wz -> is_ecall (Z_to_bv 32 wz) = false ->
  decode_any (Z_to_bv 32 wz) = Some (FLoad FMT_S rd rs imm, 4%Z) -> q = p + 4 ->
  getr regs rs = Z_to_bv 64 base -> a = base + bv_signed imm ->
  rdn segs mem (Z_to_bv 64 a) 4 = Some bs ->
  RiscvSemantics.step segs (@mkst fs regs (Z_to_bv 64 p) mem rom) =
  MachineOk (@mkst (mkFP (bvmap_set rd (nan_box (bv_extract 0 32 (le_bytes_to_word bs))) (@fp_regs fs)) (@fp_csr fs))
    regs (Z_to_bv 64 q) mem rom).
Proof.
intros fs regs mem rom p q wz rd rs imm base a bs Hc He Hd Hq Hrs Ha Hr.
rewrite (fp_step_flw fs segs regs (Z_to_bv 64 p) mem rom (Z_to_bv 32 wz) rd rs imm (Z_to_bv 64 a) bs
  (tbl_ok p wz Hc) He Hd).
- rewrite Hq, hfp_addi_lit. reflexivity.
- rewrite Hrs, hfp_addi_lit, Ha. reflexivity.
- exact Hr.
Qed.

(* flw right after sw v at the same address (image A 0x84cb0 / 0x84cb4, image B 0x850a8 / 0x850ac) *)
Lemma hfp_tw_flw_sw : forall (fs : YK11.FPState) regs mem rom p q wz rd rs (imm : bv 12) base a (v : word),
  clookup tbl p = Some wz -> is_ecall (Z_to_bv 32 wz) = false ->
  decode_any (Z_to_bv 32 wz) = Some (FLoad FMT_S rd rs imm, 4%Z) -> q = p + 4 ->
  getr regs rs = Z_to_bv 64 base -> a = base + bv_signed imm -> 0 <= a -> a + 4 <= 2 ^ 64 ->
  RiscvSemantics.step segs (@mkst fs regs (Z_to_bv 64 p) (wbytes mem (Z_to_bv 64 a) (word_to_le_bytes 4 v)) rom) =
  MachineOk (@mkst (mkFP (bvmap_set rd (nan_box (low32 v)) (@fp_regs fs)) (@fp_csr fs))
    regs (Z_to_bv 64 q) (wbytes mem (Z_to_bv 64 a) (word_to_le_bytes 4 v)) rom).
Proof.
intros fs regs mem rom p q wz rd rs imm base a v Hc He Hd Hq Hrs Ha Ha0 Ha4.
rewrite (hfp_tw_flw_rdn fs regs (wbytes mem (Z_to_bv 64 a) (word_to_le_bytes 4 v)) rom p q wz rd rs imm base a
  (word_to_le_bytes 4 v) Hc He Hd Hq Hrs Ha (hfp_rdn_sw segs mem a v Ha0 Ha4)).
rewrite hfp_word4_low. reflexivity.
Qed.

(* fld of an 8-byte cell holding v (the read-only doubles) *)
Lemma hfp_tw_fld : forall (fs : YK11.FPState) regs mem rom p q wz rd rs (imm : bv 12) base a v,
  clookup tbl p = Some wz -> is_ecall (Z_to_bv 32 wz) = false ->
  decode_any (Z_to_bv 32 wz) = Some (FLoad FMT_D rd rs imm, 4%Z) -> q = p + 4 ->
  getr regs rs = Z_to_bv 64 base -> a = base + bv_signed imm ->
  0 <= v < 2 ^ 64 -> val_mem segs mem a 8 v ->
  RiscvSemantics.step segs (@mkst fs regs (Z_to_bv 64 p) mem rom) =
  MachineOk (@mkst (mkFP (bvmap_set rd (Z_to_bv 64 v) (@fp_regs fs)) (@fp_csr fs))
    regs (Z_to_bv 64 q) mem rom).
Proof.
intros fs regs mem rom p q wz rd rs imm base a v Hc He Hd Hq Hrs Ha Hv HM.
rewrite (fp_step_fld fs segs regs (Z_to_bv 64 p) mem rom (Z_to_bv 32 wz) rd rs imm
  (v_addi (getr regs rs) (bv_signed imm)) (hfp_bytes 8 v)
  (tbl_ok p wz Hc) He Hd eq_refl).
- cbn [fp_regs fp_csr]. rewrite Hq, hfp_addi_lit, hfp_word8 by lia.
  rewrite bv_extract_0_64. reflexivity.
- rewrite Hrs, hfp_addi_lit, <- Ha. apply hfp_rdn8. exact HM.
Qed.

(* fld of any 8 bytes bs *)
Lemma hfp_tw_fld_rdn : forall (fs : YK11.FPState) regs mem rom p q wz rd rs (imm : bv 12) base a bs,
  clookup tbl p = Some wz -> is_ecall (Z_to_bv 32 wz) = false ->
  decode_any (Z_to_bv 32 wz) = Some (FLoad FMT_D rd rs imm, 4%Z) -> q = p + 4 ->
  getr regs rs = Z_to_bv 64 base -> a = base + bv_signed imm ->
  rdn segs mem (Z_to_bv 64 a) 8 = Some bs ->
  RiscvSemantics.step segs (@mkst fs regs (Z_to_bv 64 p) mem rom) =
  MachineOk (@mkst (mkFP (bvmap_set rd (le_bytes_to_word bs) (@fp_regs fs)) (@fp_csr fs))
    regs (Z_to_bv 64 q) mem rom).
Proof.
intros fs regs mem rom p q wz rd rs imm base a bs Hc He Hd Hq Hrs Ha Hr.
rewrite (fp_step_fld fs segs regs (Z_to_bv 64 p) mem rom (Z_to_bv 32 wz) rd rs imm (Z_to_bv 64 a) bs
  (tbl_ok p wz Hc) He Hd).
- rewrite Hq, hfp_addi_lit, bv_extract_0_64. reflexivity.
- rewrite Hrs, hfp_addi_lit, Ha. reflexivity.
- exact Hr.
Qed.

(* fld of the 8 bytes an earlier fsd / sd of the word v left (the epilogue's fld fs0,144(sp)) *)
Lemma hfp_tw_fld_word : forall (fs : YK11.FPState) regs mem rom p q wz rd rs (imm : bv 12) base a (v : word),
  clookup tbl p = Some wz -> is_ecall (Z_to_bv 32 wz) = false ->
  decode_any (Z_to_bv 32 wz) = Some (FLoad FMT_D rd rs imm, 4%Z) -> q = p + 4 ->
  getr regs rs = Z_to_bv 64 base -> a = base + bv_signed imm ->
  rdn segs mem (Z_to_bv 64 a) 8 = Some (word_to_le_bytes 8 v) ->
  RiscvSemantics.step segs (@mkst fs regs (Z_to_bv 64 p) mem rom) =
  MachineOk (@mkst (mkFP (bvmap_set rd v (@fp_regs fs)) (@fp_csr fs)) regs (Z_to_bv 64 q) mem rom).
Proof.
intros fs regs mem rom p q wz rd rs imm base a v Hc He Hd Hq Hrs Ha Hr.
rewrite (hfp_tw_fld_rdn fs regs mem rom p q wz rd rs imm base a (word_to_le_bytes 8 v) Hc He Hd Hq Hrs Ha Hr).
rewrite le_bytes_to_word_Z, bytes_le_to_Z_8, Z_to_bv_bv_unsigned. reflexivity.
Qed.

(* fsd (the prologue's fsd fs0,144(sp)) *)
Lemma hfp_tw_fsd : forall (fs : YK11.FPState) regs mem rom p q wz rs1 rs2 (imm : bv 12) base a,
  clookup tbl p = Some wz -> is_ecall (Z_to_bv 32 wz) = false ->
  decode_any (Z_to_bv 32 wz) = Some (FStore FMT_D rs1 rs2 imm, 4%Z) -> q = p + 4 ->
  getr regs rs1 = Z_to_bv 64 base -> a = base + bv_signed imm ->
  RiscvSemantics.store_ok segs mem (Z_to_bv 64 a) 8 = true ->
  RiscvSemantics.step segs (@mkst fs regs (Z_to_bv 64 p) mem rom) =
  MachineOk (@mkst fs regs (Z_to_bv 64 q)
    (wbytes mem (Z_to_bv 64 a) (word_to_le_bytes 8 (reg_get (@fp_regs fs) rs2))) rom).
Proof.
intros fs regs mem rom p q wz rs1 rs2 imm base a Hc He Hd Hq Hrs Ha Hok.
rewrite (fp_step_fsd fs segs regs (Z_to_bv 64 p) mem rom (Z_to_bv 32 wz) rs1 rs2 imm (Z_to_bv 64 a)
  (tbl_ok p wz Hc) He Hd).
- rewrite Hq, hfp_addi_lit. reflexivity.
- rewrite Hrs, hfp_addi_lit, Ha. reflexivity.
- exact Hok.
Qed.

(* fmv.d.x (fmv.d.x fs0,zero: fs0 := the bits of +0.0) *)
Lemma hfp_tw_fmv_d_x : forall (fs : YK11.FPState) regs mem rom p q wz rd rs (x : word),
  clookup tbl p = Some wz -> is_ecall (Z_to_bv 32 wz) = false ->
  decode_any (Z_to_bv 32 wz) = Some (Fmv FMV_F_X FMT_D rd rs, 4%Z) -> q = p + 4 -> getr regs rs = x ->
  RiscvSemantics.step segs (@mkst fs regs (Z_to_bv 64 p) mem rom) =
  MachineOk (@mkst (mkFP (bvmap_set rd x (@fp_regs fs)) (@fp_csr fs)) regs (Z_to_bv 64 q) mem rom).
Proof.
intros fs regs mem rom p q wz rd rs x Hc He Hd Hq Hx.
rewrite (fp_step_fmv_d_x fs segs regs (Z_to_bv 64 p) mem rom (Z_to_bv 32 wz) rd rs (tbl_ok p wz Hc) He Hd).
rewrite Hq, hfp_addi_lit, Hx. reflexivity.
Qed.

(* ---- the double instructions; the fcsr is kept abstract (only its rounding field matters) ---- *)
Lemma hfp_tw_fcvt_d_s : forall (F : bvmap 5 word) (C : bv 32) regs mem rom p q wz rd rs (rm : bv 3) (src : word),
  clookup tbl p = Some wz -> is_ecall (Z_to_bv 32 wz) = false ->
  decode_any (Z_to_bv 32 wz) = Some (Fcvt FC_D FC_S rd rs rm, 4%Z) ->
  bv_unsigned rm = 0 -> q = p + 4 -> Sem.reg_get F rs = src -> frm_zero C ->
  exists C' : bv 32,
    RiscvSemantics.step segs (@mkst (mkFP F C) regs (Z_to_bv 64 p) mem rom) =
    MachineOk (@mkst (mkFP (bvmap_set rd (FP.fcvt_d_s RNE src) F) C') regs (Z_to_bv 64 q) mem rom)
    /\ frm_zero C'.
Proof.
intros F C regs mem rom p q wz rd rs rm src Hc He Hd Hrm Hq Hsrc HC. eexists. split.
- rewrite (hp_step_fcvt_d_s F C segs regs (Z_to_bv 64 p) mem rom (Z_to_bv 32 wz) rd rs rm
    (tbl_ok p wz Hc) He Hd Hrm).
  rewrite Hq, hfp_addi_lit, Hsrc. reflexivity.
- apply fp_frm_zero_accrue; [apply fp_fflags_bits_range | exact HC].
Qed.

Lemma hfp_tw_fadd_d : forall (F : bvmap 5 word) (C : bv 32) regs mem rom p q wz rd rs1 rs2 (rm : bv 3) (x y : word),
  clookup tbl p = Some wz -> is_ecall (Z_to_bv 32 wz) = false ->
  decode_any (Z_to_bv 32 wz) = Some (Fari F_ADD FMT_D rd rs1 rs2 rm, 4%Z) ->
  bv_unsigned rm = 7 -> q = p + 4 -> Sem.reg_get F rs1 = x -> Sem.reg_get F rs2 = y -> frm_zero C ->
  exists C' : bv 32,
    RiscvSemantics.step segs (@mkst (mkFP F C) regs (Z_to_bv 64 p) mem rom) =
    MachineOk (@mkst (mkFP (bvmap_set rd (FP.fadd_d RNE x y) F) C') regs (Z_to_bv 64 q) mem rom)
    /\ frm_zero C'.
Proof.
intros F C regs mem rom p q wz rd rs1 rs2 rm x y Hc He Hd Hrm Hq Hx Hy HC. eexists. split.
- rewrite (hp_step_fadd_d F C segs regs (Z_to_bv 64 p) mem rom (Z_to_bv 32 wz) rd rs1 rs2 rm
    (tbl_ok p wz Hc) He Hd Hrm HC).
  rewrite Hq, hfp_addi_lit, Hx, Hy. reflexivity.
- apply fp_frm_zero_accrue; [apply fp_fflags_bits_range | exact HC].
Qed.

Lemma hfp_tw_fle_d : forall (F : bvmap 5 word) (C : bv 32) regs mem rom p q wz rd rs1 rs2 (x y : word),
  clookup tbl p = Some wz -> is_ecall (Z_to_bv 32 wz) = false ->
  decode_any (Z_to_bv 32 wz) = Some (Fcmp F_LE FMT_D rd rs1 rs2, 4%Z) ->
  bv_eqb rd 0 = false -> q = p + 4 -> Sem.reg_get F rs1 = x -> Sem.reg_get F rs2 = y -> frm_zero C ->
  exists C' : bv 32,
    RiscvSemantics.step segs (@mkst (mkFP F C) regs (Z_to_bv 64 p) mem rom) =
    MachineOk (@mkst (mkFP F C')
      (regupd regs rd (if FP.fle_d x y then Z_to_bv 64 1 else Z_to_bv 64 0)) (Z_to_bv 64 q) mem rom)
    /\ frm_zero C'.
Proof.
intros F C regs mem rom p q wz rd rs1 rs2 x y Hc He Hd Hrd Hq Hx Hy HC. eexists. split.
- rewrite (hp_step_fle_d F C segs regs (Z_to_bv 64 p) mem rom (Z_to_bv 32 wz) rd rs1 rs2
    (tbl_ok p wz Hc) He Hd).
  rewrite Hrd, Hq, hfp_addi_lit, Hx, Hy. reflexivity.
- apply fp_frm_zero_accrue; [apply fp_fflags_bits_range | exact HC].
Qed.

Lemma hfp_tw_flt_d : forall (F : bvmap 5 word) (C : bv 32) regs mem rom p q wz rd rs1 rs2 (x y : word),
  clookup tbl p = Some wz -> is_ecall (Z_to_bv 32 wz) = false ->
  decode_any (Z_to_bv 32 wz) = Some (Fcmp F_LT FMT_D rd rs1 rs2, 4%Z) ->
  bv_eqb rd 0 = false -> q = p + 4 -> Sem.reg_get F rs1 = x -> Sem.reg_get F rs2 = y -> frm_zero C ->
  exists C' : bv 32,
    RiscvSemantics.step segs (@mkst (mkFP F C) regs (Z_to_bv 64 p) mem rom) =
    MachineOk (@mkst (mkFP F C')
      (regupd regs rd (if FP.flt_d x y then Z_to_bv 64 1 else Z_to_bv 64 0)) (Z_to_bv 64 q) mem rom)
    /\ frm_zero C'.
Proof.
intros F C regs mem rom p q wz rd rs1 rs2 x y Hc He Hd Hrd Hq Hx Hy HC. eexists. split.
- rewrite (hp_step_flt_d F C segs regs (Z_to_bv 64 p) mem rom (Z_to_bv 32 wz) rd rs1 rs2
    (tbl_ok p wz Hc) He Hd).
  rewrite Hrd, Hq, hfp_addi_lit, Hx, Hy. reflexivity.
- apply fp_frm_zero_accrue; [apply fp_fflags_bits_range | exact HC].
Qed.

Lemma hfp_tw_fcvt_l_d : forall (F : bvmap 5 word) (C : bv 32) regs mem rom p q wz rd rs (rm : bv 3) (x : word),
  clookup tbl p = Some wz -> is_ecall (Z_to_bv 32 wz) = false ->
  decode_any (Z_to_bv 32 wz) = Some (Fcvt FC_L FC_D rd rs rm, 4%Z) ->
  bv_unsigned rm = 1 -> bv_eqb rd 0 = false -> q = p + 4 -> Sem.reg_get F rs = x -> frm_zero C ->
  exists C' : bv 32,
    RiscvSemantics.step segs (@mkst (mkFP F C) regs (Z_to_bv 64 p) mem rom) =
    MachineOk (@mkst (mkFP F C') (regupd regs rd (FP.fcvt_l_d RTZ x)) (Z_to_bv 64 q) mem rom)
    /\ frm_zero C'.
Proof.
intros F C regs mem rom p q wz rd rs rm x Hc He Hd Hrm Hrd Hq Hx HC. eexists. split.
- rewrite (hp_step_fcvt_l_d F C segs regs (Z_to_bv 64 p) mem rom (Z_to_bv 32 wz) rd rs rm
    (tbl_ok p wz Hc) He Hd Hrm).
  rewrite Hrd, Hq, hfp_addi_lit, Hx. reflexivity.
- apply fp_frm_zero_accrue; [apply fp_fflags_bits_range | exact HC].
Qed.

Lemma hfp_tw_fcvt_d_l : forall (F : bvmap 5 word) (C : bv 32) regs mem rom p q wz rd rs (rm : bv 3) (x : word),
  clookup tbl p = Some wz -> is_ecall (Z_to_bv 32 wz) = false ->
  decode_any (Z_to_bv 32 wz) = Some (Fcvt FC_D FC_L rd rs rm, 4%Z) ->
  bv_unsigned rm = 7 -> q = p + 4 -> getr regs rs = x -> frm_zero C ->
  exists C' : bv 32,
    RiscvSemantics.step segs (@mkst (mkFP F C) regs (Z_to_bv 64 p) mem rom) =
    MachineOk (@mkst (mkFP (bvmap_set rd (FP.fcvt_d_l RNE x) F) C') regs (Z_to_bv 64 q) mem rom)
    /\ frm_zero C'.
Proof.
intros F C regs mem rom p q wz rd rs rm x Hc He Hd Hrm Hq Hx HC. eexists. split.
- rewrite (hp_step_fcvt_d_l F C segs regs (Z_to_bv 64 p) mem rom (Z_to_bv 32 wz) rd rs rm
    (tbl_ok p wz Hc) He Hd Hrm HC).
  rewrite Hq, hfp_addi_lit, Hx. reflexivity.
- apply fp_frm_zero_accrue; [apply fp_fflags_bits_range | exact HC].
Qed.
End tw.

(* ======== the values: Prog/ParseFP.v at headamp's constants ======== *)
(* The words the path computes: f15 after flw / fcvt.d.s / fadd.d is rfn_d b; fcvt.l.d rtz of it is rfn_t b. *)
Lemma hfp_rfn_d : forall b,
  FP.fadd_d RNE (FP.fcvt_d_s RNE (nan_box (Z_to_bv 32 b))) (Z_to_bv 64 0x3FE0000000000000) = ParseFP.rfn_d b.
Proof. reflexivity. Qed.

Lemma hfp_rfn_t : forall b, FP.fcvt_l_d RTZ (ParseFP.rfn_d b) = ParseFP.rfn_t b.
Proof. reflexivity. Qed.

(* the range test: fle.d against fs0 = +0.0 (the bits 0), flt.d against 256.0 *)
Lemma hfp_rfn_in : forall b,
  ParseFP.rfn_in b (Z_to_bv 64 0) (Z_to_bv 64 0x4070000000000000) =
  FP.fle_d (Z_to_bv 64 0) (ParseFP.rfn_d b) && FP.flt_d (ParseFP.rfn_d b) (Z_to_bv 64 0x4070000000000000).
Proof. reflexivity. Qed.

(* the four double constants as integers: +0.0 = 0, 256.0 = 256, and the two cast bounds of role_consts *)
Lemma hfp_consts :
  ParseFP.f64_is_int (Z_to_bv 64 0) 0 = true /\
  ParseFP.f64_is_int (Z_to_bv 64 0x4070000000000000) 256 = true /\
  ParseFP.f64_is_int (Z_to_bv 64 0xc3e0000000000001) (- 2 ^ 63 - 2 ^ 11) = true /\
  ParseFP.f64_is_int (Z_to_bv 64 0x43e0000000000000) (2 ^ 63) = true.
Proof.
destruct ParseFP.role_consts as (_ & _ & H3 & H4).
refine (conj _ (conj _ (conj H3 H4))); vm_compute; reflexivity.
Qed.

(* (a) the model's answer (Pod/Headamp.v parse_value: nearest f 0 255) is the hardware's *)
Lemma hfp_nearest : forall b, 0 <= b < 2 ^ 32 ->
  Nearest.nearest b 0 255 =
  if ParseFP.rfn_in b (Z_to_bv 64 0) (Z_to_bv 64 0x4070000000000000) then Some (ParseFP.rfn_r b) else None.
Proof.
intros b Hb. destruct hfp_consts as (H0 & H256 & _ & _).
exact (ParseFP.rfn_hw_nearest b 0 255 (Z_to_bv 64 0) (Z_to_bv 64 0x4070000000000000) Hb
  ltac:(lia) ltac:(lia) H0 H256).
Qed.

Lemma hfp_near_bounds : forall b lo hi r, Nearest.nearest b lo hi = Some r -> lo <= r <= hi.
Proof.
intros b lo hi r H. unfold Nearest.nearest in H.
destruct (Nearest.near_f32 b) as [q|]; [|discriminate].
destruct ((lo <=? q) && (q <=? hi)) eqn:E; [|discriminate]. injection H as <-.
apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2. lia.
Qed.

(* (b) the range test passed *)
Section inr.
Variable b : Z.
Hypothesis Hb : 0 <= b < 2 ^ 32.
Hypothesis Hin : ParseFP.rfn_in b (Z_to_bv 64 0) (Z_to_bv 64 0x4070000000000000) = true.

Lemma hfp_in_nearest : Nearest.nearest b 0 255 = Some (ParseFP.rfn_r b).
Proof using Hb Hin. rewrite (hfp_nearest b Hb), Hin. reflexivity. Qed.

(* image B 0x850e0: -2^63 - 2^11 < d *)
Lemma hfp_in_cast_lo : FP.flt_d (Z_to_bv 64 0xc3e0000000000001) (ParseFP.rfn_d b) = true.
Proof using Hb Hin.
destruct hfp_consts as (H0 & H256 & H3 & _).
exact (ParseFP.rfn_hw_above b 0 255 (Z_to_bv 64 0) (Z_to_bv 64 0x4070000000000000) Hb
  ltac:(lia) ltac:(lia) H0 H256 Hin (Z_to_bv 64 0xc3e0000000000001) (- 2 ^ 63 - 2 ^ 11) H3 ltac:(lia)).
Qed.

(* image B 0x850f0: d < 2^63 *)
Lemma hfp_in_cast_hi : FP.flt_d (ParseFP.rfn_d b) (Z_to_bv 64 0x43e0000000000000) = true.
Proof using Hb Hin.
destruct hfp_consts as (H0 & H256 & _ & H4).
exact (ParseFP.rfn_hw_below b 0 255 (Z_to_bv 64 0) (Z_to_bv 64 0x4070000000000000) Hb
  ltac:(lia) ltac:(lia) H0 H256 Hin (Z_to_bv 64 0x43e0000000000000) (2 ^ 63) H4 ltac:(lia)).
Qed.

(* t = (long long)d *)
Lemma hfp_in_t_range : 0 <= bv_signed (ParseFP.rfn_t b) <= 256.
Proof using Hb Hin.
destruct hfp_consts as (H0 & H256 & _ & _).
exact (ParseFP.rfn_hw_t_range b 0 255 (Z_to_bv 64 0) (Z_to_bv 64 0x4070000000000000) Hb
  ltac:(lia) ltac:(lia) H0 H256 Hin).
Qed.

Lemma hfp_in_r_range : 0 <= ParseFP.rfn_r b <= 255.
Proof using Hb Hin. exact (hfp_near_bounds b 0 255 (ParseFP.rfn_r b) hfp_in_nearest). Qed.
End inr.

(* image B's floor form: r = t - 1 when d < (double)t, else t *)
Lemma hfp_floor_B : forall b, ParseFP.rfn_r b =
  (if FP.flt_d (ParseFP.rfn_d b) (FP.fcvt_d_l RNE (ParseFP.rfn_t b))
   then bv_signed (ParseFP.rfn_t b) - 1 else bv_signed (ParseFP.rfn_t b)).
Proof.
intros b. unfold ParseFP.rfn_r.
destruct (FP.flt_d (ParseFP.rfn_d b) (FP.fcvt_d_l RNE (ParseFP.rfn_t b))); lia.
Qed.

(* ---- words: a signed read back as a literal, and the two integer tails ---- *)
Lemma hfp_Z64_eq_mod : forall x y, x mod 2 ^ 64 = y mod 2 ^ 64 -> Z_to_bv 64 x = Z_to_bv 64 y.
Proof.
intros x y H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 64) with (2 ^ 64). exact H.
Qed.

Lemma hfp_signed_mod : forall w : word, bv_signed w mod 2 ^ 64 = bv_unsigned w mod 2 ^ 64.
Proof.
intros w. unfold bv_signed, bv_swrap, bv_wrap.
change (bv_half_modulus 64) with (2 ^ 63). change (bv_modulus 64) with (2 ^ 64).
set (u := bv_unsigned w).
rewrite (Z.mod_eq (u + 2 ^ 63) (2 ^ 64)) by lia.
replace (u + 2 ^ 63 - 2 ^ 64 * ((u + 2 ^ 63) / 2 ^ 64) - 2 ^ 63)
  with (u + (- ((u + 2 ^ 63) / 2 ^ 64)) * 2 ^ 64) by ring.
apply Z_mod_plus_full.
Qed.

Lemma hfp_lit_signed : forall w : word, Z_to_bv 64 (bv_signed w) = w.
Proof.
intros w. apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite hfp_signed_mod. apply Z.mod_small. apply u64_range.
Qed.

Lemma hfp_sub_lit : forall (t : word) c, 0 <= c < 2 ^ 64 -> v_sub t (Z_to_bv 64 c) = Z_to_bv 64 (bv_signed t - c).
Proof.
intros t c Hc. unfold v_sub. apply hfp_Z64_eq_mod. rewrite unsigned_lit_small by exact Hc.
rewrite (Zminus_mod (bv_unsigned t) c (2 ^ 64)), (Zminus_mod (bv_signed t) c (2 ^ 64)), hfp_signed_mod.
reflexivity.
Qed.

(* image A 0x84cec: sub a2,a0,a1 with a0 = t, a1 = (d < (double)t) *)
Lemma hfp_sub_r : forall b,
  v_sub (ParseFP.rfn_t b)
    (if FP.flt_d (ParseFP.rfn_d b) (FP.fcvt_d_l RNE (ParseFP.rfn_t b)) then Z_to_bv 64 1 else Z_to_bv 64 0)
  = Z_to_bv 64 (ParseFP.rfn_r b).
Proof.
intros b. unfold ParseFP.rfn_r.
destruct (FP.flt_d (ParseFP.rfn_d b) (FP.fcvt_d_l RNE (ParseFP.rfn_t b)));
  apply hfp_sub_lit; lia.
Qed.

(* image B 0x85108: addi a0,a2,-1 with a2 = t *)
Lemma hfp_dec_lit : forall t : word, v_addi t (-1) = Z_to_bv 64 (bv_signed t - 1).
Proof.
intros t. rewrite <- (hfp_lit_signed t) at 1. rewrite hfp_addi_lit. f_equal; lia.
Qed.

Lemma hfp_dec_signed : forall t : word, - 2 ^ 63 < bv_signed t < 2 ^ 63 ->
  bv_signed (v_addi t (-1)) = bv_signed t - 1.
Proof.
intros t Ht. rewrite hfp_dec_lit, Z_to_bv_signed.
apply bv_swrap_small. change (bv_half_modulus 64) with (2 ^ 63). lia.
Qed.

(* image B 0x8510c: bge a0,a2 with a0 = t - 1, a2 = t does not jump *)
Lemma hfp_bge_dec : forall t : word, - 2 ^ 63 < bv_signed t < 2 ^ 63 ->
  branch_taken BC_GE (v_addi t (-1)) t = false.
Proof.
intros t Ht. cbn [branch_taken]. unfold bv_lts. rewrite (hfp_dec_signed t Ht).
replace (bv_signed t - 1 <? bv_signed t) with true by (symmetry; apply Z.ltb_lt; lia).
reflexivity.
Qed.

Print Assumptions hp_step_fcvt_d_s.
Print Assumptions hp_step_fadd_d.
Print Assumptions hp_step_fle_d.
Print Assumptions hp_step_flt_d.
Print Assumptions hp_step_fcvt_l_d.
Print Assumptions hp_step_fcvt_d_l.
Print Assumptions hfp_rdn8.
Print Assumptions hfp_rdn4.
Print Assumptions hfp_word8.
Print Assumptions hfp_word4.
Print Assumptions hfp_rdn_sw.
Print Assumptions hfp_word4_low.
Print Assumptions hfp_tw_flw.
Print Assumptions hfp_tw_flw_rdn.
Print Assumptions hfp_tw_flw_sw.
Print Assumptions hfp_tw_fld.
Print Assumptions hfp_tw_fld_rdn.
Print Assumptions hfp_tw_fld_word.
Print Assumptions hfp_tw_fsd.
Print Assumptions hfp_tw_fmv_d_x.
Print Assumptions hfp_tw_fcvt_d_s.
Print Assumptions hfp_tw_fadd_d.
Print Assumptions hfp_tw_fle_d.
Print Assumptions hfp_tw_flt_d.
Print Assumptions hfp_tw_fcvt_l_d.
Print Assumptions hfp_tw_fcvt_d_l.
Print Assumptions hfp_rfn_d.
Print Assumptions hfp_rfn_t.
Print Assumptions hfp_rfn_in.
Print Assumptions hfp_consts.
Print Assumptions hfp_nearest.
Print Assumptions hfp_near_bounds.
Print Assumptions hfp_in_nearest.
Print Assumptions hfp_in_cast_lo.
Print Assumptions hfp_in_cast_hi.
Print Assumptions hfp_in_t_range.
Print Assumptions hfp_in_r_range.
Print Assumptions hfp_floor_B.
Print Assumptions hfp_lit_signed.
Print Assumptions hfp_sub_lit.
Print Assumptions hfp_sub_r.
Print Assumptions hfp_dec_lit.
Print Assumptions hfp_dec_signed.
Print Assumptions hfp_bge_dec.
