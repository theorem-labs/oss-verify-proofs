(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib HRep HRepFacts HFpu HFpuU1.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs LibIface LbB_Bridge LbB_Conv.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_HEmpF.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_ff5490 : bv 32 := 0x000aa787.
Lemma F_ff5490 : fetch_word asegs (Z_to_bv 64 0xf5490) = Some W_ff5490. Proof. vm_refl. Qed.
Lemma D_ff5490 : decode_any W_ff5490 = Some (FLoad FMT_S 15 21 0, 4%Z). Proof. vm_refl. Qed.
Definition W_ff5494 : bv 32 := 0xd0357753.
Lemma F_ff5494 : fetch_word asegs (Z_to_bv 64 0xf5494) = Some W_ff5494. Proof. vm_refl. Qed.
Lemma D_ff5494 : decode_any W_ff5494 = Some (Fcvt FC_S FC_LU 14 10 7, 4%Z). Proof. vm_refl. Qed.
Definition W_ff54a8 : bv 32 := 0xd03df6d3.
Lemma F_ff54a8 : fetch_word asegs (Z_to_bv 64 0xf54a8) = Some W_ff54a8. Proof. vm_refl. Qed.
Lemma D_ff54a8 : decode_any W_ff54a8 = Some (Fcvt FC_S FC_LU 13 27 7, 4%Z). Proof. vm_refl. Qed.
Definition W_ff54ac : bv 32 := 0x10d7f6d3.
Lemma F_ff54ac : fetch_word asegs (Z_to_bv 64 0xf54ac) = Some W_ff54ac. Proof. vm_refl. Qed.
Lemma D_ff54ac : decode_any W_ff54ac = Some (Fari F_MUL FMT_S 13 15 13 7, 4%Z). Proof. vm_refl. Qed.
Definition W_ff54b0 : bv 32 := 0xa0e695d3.
Lemma F_ff54b0 : fetch_word asegs (Z_to_bv 64 0xf54b0) = Some W_ff54b0. Proof. vm_refl. Qed.
Lemma D_ff54b0 : decode_any W_ff54b0 = Some (Fcmp F_LT FMT_S 11 13 14, 4%Z). Proof. vm_refl. Qed.
Definition W_ff54dc : bv 32 := 0x18f777d3.
Lemma F_ff54dc : fetch_word asegs (Z_to_bv 64 0xf54dc) = Some W_ff54dc. Proof. vm_refl. Qed.
Lemma D_ff54dc : decode_any W_ff54dc = Some (Fari F_DIV FMT_S 15 14 15 7, 4%Z). Proof. vm_refl. Qed.
Definition W_ff54e4 : bv 32 := 0xf0058753.
Lemma F_ff54e4 : fetch_word asegs (Z_to_bv 64 0xf54e4) = Some W_ff54e4. Proof. vm_refl. Qed.
Lemma D_ff54e4 : decode_any W_ff54e4 = Some (Fmv FMV_F_X FMT_S 14 11, 4%Z). Proof. vm_refl. Qed.
Definition W_ff54e8 : bv 32 := 0x20f7a6d3.
Lemma F_ff54e8 : fetch_word asegs (Z_to_bv 64 0xf54e8) = Some W_ff54e8. Proof. vm_refl. Qed.
Lemma D_ff54e8 : decode_any W_ff54e8 = Some (Fsgnj F_SGNJX FMT_S 13 15 15, 4%Z). Proof. vm_refl. Qed.
Definition W_ff54ec : bv 32 := 0xa0e695d3.
Lemma F_ff54ec : fetch_word asegs (Z_to_bv 64 0xf54ec) = Some W_ff54ec. Proof. vm_refl. Qed.
Lemma D_ff54ec : decode_any W_ff54ec = Some (Fcmp F_LT FMT_S 11 13 14, 4%Z). Proof. vm_refl. Qed.
Definition W_ff54f8 : bv 32 := 0xc007b5d3.
Lemma F_ff54f8 : fetch_word asegs (Z_to_bv 64 0xf54f8) = Some W_ff54f8. Proof. vm_refl. Qed.
Lemma D_ff54f8 : decode_any W_ff54f8 = Some (Fcvt (if true then FC_W else FC_WU) FC_S 11 15 3, 4%Z). Proof. vm_refl. Qed.
Definition W_ff54fc : bv 32 := 0xd005b753.
Lemma F_ff54fc : fetch_word asegs (Z_to_bv 64 0xf54fc) = Some W_ff54fc. Proof. vm_refl. Qed.
Lemma D_ff54fc : decode_any W_ff54fc = Some (Fcvt FC_S (if true then FC_W else FC_WU) 14 11 3, 4%Z). Proof. vm_refl. Qed.
Definition W_ff5500 : bv 32 := 0x20f707d3.
Lemma F_ff5500 : fetch_word asegs (Z_to_bv 64 0xf5500) = Some W_ff5500. Proof. vm_refl. Qed.
Lemma D_ff5500 : decode_any W_ff5500 = Some (Fsgnj F_SGNJ FMT_S 15 14 15, 4%Z). Proof. vm_refl. Qed.
Definition W_ff5508 : bv 32 := 0xf0058753.
Lemma F_ff5508 : fetch_word asegs (Z_to_bv 64 0xf5508) = Some W_ff5508. Proof. vm_refl. Qed.
Lemma D_ff5508 : decode_any W_ff5508 = Some (Fmv FMV_F_X FMT_S 14 11, 4%Z). Proof. vm_refl. Qed.
Definition W_ff550c : bv 32 := 0xa0f715d3.
Lemma F_ff550c : fetch_word asegs (Z_to_bv 64 0xf550c) = Some W_ff550c. Proof. vm_refl. Qed.
Lemma D_ff550c : decode_any W_ff550c = Some (Fcmp F_LT FMT_S 11 14 15, 4%Z). Proof. vm_refl. Qed.
Definition W_ff551c : bv 32 := 0xf0058753.
Lemma F_ff551c : fetch_word asegs (Z_to_bv 64 0xf551c) = Some W_ff551c. Proof. vm_refl. Qed.
Lemma D_ff551c : decode_any W_ff551c = Some (Fmv FMV_F_X FMT_S 14 11, 4%Z). Proof. vm_refl. Qed.
Definition W_ff5520 : bv 32 := 0xa0e795d3.
Lemma F_ff5520 : fetch_word asegs (Z_to_bv 64 0xf5520) = Some W_ff5520. Proof. vm_refl. Qed.
Lemma D_ff5520 : decode_any W_ff5520 = Some (Fcmp F_LT FMT_S 11 15 14, 4%Z). Proof. vm_refl. Qed.
Definition W_ff5534 : bv 32 := 0xc0379553.
Lemma F_ff5534 : fetch_word asegs (Z_to_bv 64 0xf5534) = Some W_ff5534. Proof. vm_refl. Qed.
Lemma D_ff5534 : decode_any W_ff5534 = Some (Fcvt (if false then FC_L else FC_LU) FC_S 10 15 1, 4%Z). Proof. vm_refl. Qed.

Lemma lf_fpN : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (rom : word -> option byte) (obj sz bc : Z),
  0 <= sz -> sz + 1 < 2 ^ 24 -> 0 <= bc < 2 ^ 24 ->
  0 <= obj -> obj + 40 <= 2 ^ 47 ->
  PropExec.rdn asegs m (Z_to_bv 64 (obj + 32)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0x3f800000)) ->
  frm_zero fc ->
  evt asegs (fun x => exists F' fc' a1, x = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 1) a1 x12 x13 x14 x15 x16 x17
                                               x18 x19 x20 (Z_to_bv 64 (obj + 32)) x22 x23 x25 x25 x26 (Z_to_bv 64 bc)
                                               x28 x29 x30 (Z_to_bv 64 (2 ^ 60)))
                                          F' (Z_to_bv 64 (if (bc =? 0) || (bc <? sz + 1) then 0xf54c4 else 0xf54b8)) fc' None m rom
               /\ frm_zero fc' /\ fholds (PropExec.mkFP F' fc') 15 one32 /\ fholds (PropExec.mkFP F' fc') 14 (ieee (sz + 1)))
           (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 (sz + 1)) x11 x12 x13 x14 x15 x16 x17
                    x18 x19 x20 (Z_to_bv 64 (obj + 32)) x22 x23 x24 x25 x26 (Z_to_bv 64 bc) x28 x29 x30 x31)
               F (Z_to_bv 64 0xf5490) fc None m rom).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x28 x29 x30 x31 F fc m rom obj sz bc
    Hsz Hsz1 Hbc Ho0 Ho1 RD FZ.
  pose proof (ieee_range (sz + 1) ltac:(lia)) as IE1.
  set (R := mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 (sz + 1)) x11 x12 x13 x14 x15 x16 x17
              x18 x19 x20 (Z_to_bv 64 (obj + 32)) x22 x23 x24 x25 x26 (Z_to_bv 64 bc) x28 x29 x30 x31).
  eapply evt_step.
  { split; [reflexivity|].
    eapply (fp_step_flw (PropExec.mkFP F fc) asegs R (Z_to_bv 64 0xf5490) m rom W_ff5490 15%bv 21%bv 0%bv (Z_to_bv 64 (obj + 32)) _
              F_ff5490 eq_refl D_ff5490); [change (PropExec.getr R 21) with (Z_to_bv 64 (obj + 32)); change (bv_signed 0%bv) with 0;
                                          rewrite v_addi_Z by lia; f_equal; lia | exact RD]. }
  cbn [PropExec.fp_regs PropExec.fp_csr]. rewrite flw_nan_box by lia. rewrite mkst_MS. rewrite v_addi_Z by lia. npc. subst R.
  f_slu F_ff5494 D_ff5494 (10%bv : reg) (sz + 1).
  step. step. step.
  destruct (Z.eq_dec bc 0) as [Hb0 | Hb1].
  - subst bc. replace ((0 =? 0) || (0 <? sz + 1)) with true by reflexivity.
    step. brc.
    apply evt_done. eexists _, _, _. split; [reflexivity|]. split; [fz|]. split; fh.
  - replace ((bc =? 0) || (bc <? sz + 1)) with (bc <? sz + 1) by (rewrite (proj2 (Z.eqb_neq bc 0) Hb1); reflexivity).
    pose proof (ieee_range bc ltac:(lia)) as IE2.
    step. rewrite eqbZ by lia. rewrite (proj2 (Z.eqb_neq bc 0) Hb1). brc.
    f_slu F_ff54a8 D_ff54a8 (27%bv : reg) bc.
    f_ari F_ff54ac D_ff54ac one32 (ieee bc) mul_one_val.
    f_cmp F_ff54b0 D_ff54b0 (ieee bc) (ieee (sz + 1)) lt_val.
    destruct (bc <? sz + 1) eqn:LT.
    + step. brc. apply evt_done. eexists _, _, _. split; [reflexivity|]. split; [fz|]. split; fh.
    + step. brc. apply evt_done. eexists _, _, _. split; [reflexivity|]. split; [fz|]. split; fh.
Qed.

Lemma tl_fpN : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (rom : word -> option byte) (f bc n : Z),
  0 <= f <= 1 -> 0 <= bc < 2 ^ 24 -> 1 <= n < 2 ^ 24 -> frm_zero fc ->
  fholds (PropExec.mkFP F fc) 15 (ieee n) ->
  evt asegs (fun x => exists F' fc' v10 v11, x = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 v10 v11 x12 x13 x14 x15 x16 x17
                                                    x18 x19 x20 x21 x22 x23 x24 x25 x26 (Z_to_bv 64 (gmax f bc n))
                                                    x28 x29 x30 x31)
                                          F' (Z_to_bv 64 0xf5540) fc' None m rom /\ frm_zero fc')
           (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 f) x11 x12 x13 x14 x15 x16 x17
                    x18 x19 x20 x21 x22 x23 x24 x25 x26 (Z_to_bv 64 bc) x28 x29 x30 x31)
               F (Z_to_bv 64 0xf5504) fc None m rom).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 F fc m rom f bc n
    Hf Hbc Hn FZ H15.
  pose proof (ieee_range n Hn) as IE.
  step.
  f_mvx F_ff5508 D_ff5508 (11%bv : reg).
  f_cmp F_ff550c D_ff550c neg1f (ieee n) lt_neg1_val.
  step. brc.
  step.
  f_mvx F_ff551c D_ff551c (11%bv : reg).
  f_cmp F_ff5520 D_ff5520 (ieee n) two64f lt_two64_val.
  step. brc.
  step. step.
  rewrite (u64_of_Z bc) by lia. rewrite Z.shiftl_mul_pow2 by lia. replace (bc * 2 ^ 1) with (2 * bc) by lia.
  rewrite (u64_of_Z f) by lia. rewrite (u64_of_Z (2 * bc)) by lia. rewrite lor_bit by lia.
  f_cvlu F_ff5534 D_ff5534 (ieee n) n.
  step. rewrite ltuZ by lia. unfold gmax.
  destruct (n <? 2 * bc + f) eqn:LT; brc.
  - apply evt_done. eexists _, _, _, _. split; [reflexivity | fz].
  - step. apply evt_done. eexists _, _, _, _. split; [reflexivity | fz].
Qed.

Ltac dv_tacN n :=
  f_ari F_ff54dc D_ff54dc (ieee n) one32 div_one_val;
  step;
  f_mvx F_ff54e4 D_ff54e4 (11%bv : reg);
  f_sgnj F_ff54e8 D_ff54e8 (ieee n) (ieee n);
  f_cmp F_ff54ec D_ff54ec (ieee n) two23f lt_two23_val;
  step.
Ltac rd_tacN n :=
  f_cvw F_ff54f8 D_ff54f8 (ieee n) n;
  f_csw F_ff54fc D_ff54fc (11%bv : reg) n;
  f_sgnj F_ff5500 D_ff5500 (ieee n) (ieee n).
Ltac tl_tacN n :=
  eapply evt_mono; [eapply tl_fpN with (n := n); [try destruct (0 <? Z.land _ (_ + -1)); lia | lia | lia | fz | fh] |];
  intros ms' (F' & fc' & v10 & v11 & -> & FZ'); eexists _, _, _, _; split; [reflexivity | exact FZ'].

Lemma gr_fpN : forall (x1 x2 x3 x4 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (rom : word -> option byte) (S1 obj bc n : Z) (w640 w664 : word),
  0 <= bc < 2 ^ 24 -> 1 <= n < 2 ^ 24 -> 0 <= S1 -> S1 + 672 <= 2 ^ 47 -> 0 <= obj < 2 ^ 47 ->
  rw_cells asegs m (S1 + 632) [C8 (Z_to_bv 64 (obj + 8)); C8 w640] -> rw_cells asegs m (S1 + 656) [C8 (Z_to_bv 64 obj); C8 w664] ->
  frm_zero fc -> fholds (PropExec.mkFP F fc) 15 one32 -> fholds (PropExec.mkFP F fc) 14 (ieee n) ->
  evt asegs (fun x => exists F' fc' v10 v11, x = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 (Z_to_bv 64 S1) v10 v11 x12 x13 x14 x15 x16 x17
                                                    x18 x19 x20 x21 (Z_to_bv 64 (obj + 8)) x23 x24 (Z_to_bv 64 obj) x26
                                                    (Z_to_bv 64 (grq bc n)) x28 x29 x30 x31)
                                          F' (Z_to_bv 64 0xf5540) fc' None m rom /\ frm_zero fc')
           (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 (Z_to_bv 64 S1) (Z_to_bv 64 1) x11 x12 x13 x14 x15 x16 x17
                    x18 x19 x20 x21 x22 x23 x24 x25 x26 (Z_to_bv 64 bc) x28 x29 x30 x31)
               F (Z_to_bv 64 0xf54c4) fc None m rom).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 F fc m rom S1 obj bc n w640 w664
    Hbc Hn HS0 HS1 Ho C632 C656 FZ H15 H14.
  pose proof (ieee_range n Hn) as IE.
  step.
  step.
  step. rewrite ltuZ by lia. unfold grq, grflag.
  destruct (bc <? 3) eqn:B3; brc.
  - dv_tacN n.
    destruct (n <? 2 ^ 23) eqn:E23.
    + step. brc. rd_tacN n. tl_tacN n.
    + step. brc. tl_tacN n.
  - apply Z.ltb_ge in B3.
    step. step. step.
    rewrite (u64_of_Z bc), (u64_of_Z (bc + -1)) by lia.
    pose proof (land_lt64 bc (bc + -1) ltac:(lia)) as LB.
    unfold BLPropExec.v_sltu, BLPropExec.c_ltu. rewrite ltuZ by lia. rewrite ifZ.
    dv_tacN n.
    destruct (n <? 2 ^ 23) eqn:E23.
    + step. brc. rd_tacN n. tl_tacN n.
    + step. brc. tl_tacN n.
Qed.
