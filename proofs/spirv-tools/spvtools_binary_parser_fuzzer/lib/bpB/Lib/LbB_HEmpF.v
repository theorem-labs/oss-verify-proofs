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
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_f9d38 : bv 32 := 0x0005a787.
Lemma F_f9d38 : fetch_word asegs (Z_to_bv 64 0xfa6b8) = Some W_f9d38. Proof. vm_refl. Qed.
Lemma D_f9d38 : decode_any W_f9d38 = Some (FLoad FMT_S 15 11 0, 4%Z). Proof. vm_refl. Qed.
Definition W_f9d40 : bv 32 := 0xd0367753.
Lemma F_f9d40 : fetch_word asegs (Z_to_bv 64 0xfa6c0) = Some W_f9d40. Proof. vm_refl. Qed.
Lemma D_f9d40 : decode_any W_f9d40 = Some (Fcvt FC_S FC_LU 14 12 7, 4%Z). Proof. vm_refl. Qed.
Definition W_f9d44 : bv 32 := 0xd03a76d3.
Lemma F_f9d44 : fetch_word asegs (Z_to_bv 64 0xfa6c8) = Some W_f9d44. Proof. vm_refl. Qed.
Lemma D_f9d44 : decode_any W_f9d44 = Some (Fcvt FC_S FC_LU 13 20 7, 4%Z). Proof. vm_refl. Qed.
Definition W_f9d48 : bv 32 := 0x10d7f6d3.
Lemma F_f9d48 : fetch_word asegs (Z_to_bv 64 0xfa6cc) = Some W_f9d48. Proof. vm_refl. Qed.
Lemma D_f9d48 : decode_any W_f9d48 = Some (Fari F_MUL FMT_S 13 15 13 7, 4%Z). Proof. vm_refl. Qed.
Definition W_f9d4c : bv 32 := 0xa0e695d3.
Lemma F_f9d4c : fetch_word asegs (Z_to_bv 64 0xfa6d0) = Some W_f9d4c. Proof. vm_refl. Qed.
Lemma D_f9d4c : decode_any W_f9d4c = Some (Fcmp F_LT FMT_S 11 13 14, 4%Z). Proof. vm_refl. Qed.

Lemma of_int_zero : forall md, fp_of_int F32 md false 64 0 = (0, no_flags).
Proof. intros md. destruct md; vm_compute; reflexivity. Qed.
Lemma mul_one_zero : forall md, fp_mul F32 md one32 0 = (0, no_flags).
Proof. intros md. destruct md; vm_compute; reflexivity. Qed.
Lemma lt_zero_one : fp_lt F32 0 (ieee 1) = (true, no_flags).
Proof. vm_compute. reflexivity. Qed.

Lemma ltuZ : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> bv_ltu (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof. intros a b Ha Hb. unfold bv_ltu. rewrite !u64_of_Z by lia. reflexivity. Qed.
Lemma eqbZ : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 b) = (a =? b).
Proof. intros a b Ha Hb. unfold bv_eqb. rewrite !u64_of_Z by lia. reflexivity. Qed.
Lemma ifZ : forall b : bool, (if b then Z_to_bv 64 1 else Z_to_bv 64 0) = Z_to_bv 64 (if b then 1 else 0).
Proof. intros b. destruct b; reflexivity. Qed.
Lemma land_lt64 : forall a b, 0 <= a < 2 ^ 64 -> 0 <= Z.land a b < 2 ^ 64.
Proof.
  intros a b Ha.
  assert (E : Z.land a b = Z.land a b mod 2 ^ 64).
  { rewrite <- Z.land_ones by lia. rewrite <- Z.land_assoc, (Z.land_comm b), Z.land_assoc.
    rewrite (Z.land_ones a 64) by lia. rewrite Z.mod_small by lia. reflexivity. }
  rewrite E. apply Z.mod_pos_bound. lia.
Qed.
Lemma lor_bit : forall f x, 0 <= f <= 1 -> 0 <= x -> Z.lor f (2 * x) = 2 * x + f.
Proof.
  intros f x Hf Hx.
  assert (L : Z.land f (2 * x) = 0).
  { destruct (Z.eq_dec f 0) as [->|Hn]; [reflexivity|]. replace f with 1 by lia.
    rewrite Z.land_comm. pose proof (Z.land_ones (2 * x) 1 ltac:(lia)) as E. change (Z.ones 1) with 1 in E.
    rewrite E. rewrite Z.mul_comm. change (2 ^ 1) with 2. apply Z_mod_mult. }
  rewrite <- (Z.lxor_lor f (2 * x) L). rewrite <- (Z.add_nocarry_lxor f (2 * x) L). lia.
Qed.

Ltac npc :=
  lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?e) _ _ _ _) =>
    let v := eval vm_compute in e in change (Z_to_bv 64 e) with (Z_to_bv 64 v) end.
Ltac brc :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then ?t else ?e) _ _ _ _) =>
      let v := eval vm_compute in c in
      lazymatch v with
      | true => change (if c then t else e) with t
      | false => change (if c then t else e) with e
      end
  | _ => idtac
  end.
Ltac fz := cbn [PropExec.fp_csr]; repeat apply frm_zero_accrue_csr; assumption.
Ltac fbnd := unfold one32, two23f, neg1f, two64f; lia.
Ltac rmok := first [right; reflexivity | left; vm_compute; intros X; discriminate X].
Ltac fh := first [ match goal with Hf : fholds _ _ _ |- _ => exact Hf end
                 | apply fholds_set_same; fbnd
                 | apply fholds_set_other; [intros X; discriminate X | fh] ].
Ltac fnorm S :=
  repeat match type of S with context [bv_eqb ?r 0%bv] => replace (bv_eqb r 0%bv) with false in S by reflexivity end;
  cbv beta iota in S; unfold PropExec.regupd in S.
Ltac fgo S :=
  eapply evt_step; [split; [reflexivity | exact S] |]; clear S;
  rewrite mkst_MS, v_addi_Z by lia; cbn [PropExec.fp_regs PropExec.fp_csr]; npc.

Ltac f_cmp Fw Dw a b VAL :=
  lazymatch goal with |- evt ?sg _ (MS ?R ?F (Z_to_bv 64 ?pc) ?fc None ?m ?rom) =>
    let S := fresh "S" in
    pose proof (hp_step_fcmp_s (PropExec.mkFP F fc) sg R (Z_to_bv 64 pc) m rom _ _ _ _ _ a b Fw eq_refl Dw
                  ltac:(fh) ltac:(fh) ltac:(fbnd) ltac:(fbnd)) as S;
    cbv zeta in S; cbn [fcmp_op] in S; rewrite VAL in S by lia; cbn [fst snd] in S; fnorm S; fgo S
  end.
Ltac f_ari Fw Dw a b VAL :=
  lazymatch goal with |- evt ?sg _ (MS ?R ?F (Z_to_bv 64 ?pc) ?fc None ?m ?rom) =>
    let md := fresh "md" in let S := fresh "S" in
    destruct (hp_step_fari_s (PropExec.mkFP F fc) sg R (Z_to_bv 64 pc) m rom _ _ _ _ _ _ a b Fw eq_refl Dw
                ltac:(fz) ltac:(rmok) ltac:(fh) ltac:(fh) ltac:(fbnd) ltac:(fbnd)) as [md S];
    cbv zeta in S; cbn [fari_op] in S; rewrite VAL in S by lia; cbn [fst snd] in S; clear md; fgo S
  end.
Ltac f_slu Fw Dw rs v :=
  lazymatch goal with |- evt ?sg _ (MS ?R ?F (Z_to_bv 64 ?pc) ?fc None ?m ?rom) =>
    let md := fresh "md" in let S := fresh "S" in let A := fresh "A" in
    assert (A : PropExec.getr R rs = Z_to_bv 64 v) by reflexivity;
    destruct (hp_step_fcvt_s_lu (PropExec.mkFP F fc) sg R (Z_to_bv 64 pc) m rom _ _ _ _ Fw eq_refl Dw ltac:(fz) ltac:(rmok)) as [md S];
    cbv zeta in S; rewrite A, u64_of_Z, of_int_val in S by lia; cbn [fst snd] in S; clear A md; fgo S
  end.
Ltac f_sgnj Fw Dw a b :=
  lazymatch goal with |- evt ?sg _ (MS ?R ?F (Z_to_bv 64 ?pc) ?fc None ?m ?rom) =>
    let S := fresh "S" in
    pose proof (hp_step_fsgnj_s (PropExec.mkFP F fc) sg R (Z_to_bv 64 pc) m rom _ _ _ _ _ a b Fw eq_refl Dw
                  ltac:(fh) ltac:(fh) ltac:(fbnd) ltac:(fbnd) ltac:(discriminate)) as S;
    fgo S
  end.
Ltac f_mvx Fw Dw rs :=
  lazymatch goal with |- evt ?sg _ (MS ?R ?F (Z_to_bv 64 ?pc) ?fc None ?m ?rom) =>
    let c := eval vm_compute in (bv_unsigned (PropExec.getr R rs)) in
    let v := eval vm_compute in (c mod 2 ^ 32) in
    let S := fresh "S" in
    pose proof (hp_step_fmv_w_x (PropExec.mkFP F fc) sg R (Z_to_bv 64 pc) m rom _ _ _ c Fw eq_refl Dw
                  ltac:(apply bv_eq; vm_compute; reflexivity)) as S;
    change (c mod 2 ^ 32) with v in S; fgo S
  end.
Ltac f_cvw Fw Dw a n :=
  lazymatch goal with |- evt ?sg _ (MS ?R ?F (Z_to_bv 64 ?pc) ?fc None ?m ?rom) =>
    let md := fresh "md" in let Hmd := fresh "Hmd" in let S := fresh "S" in
    destruct (hp_step_fcvt_w_s (PropExec.mkFP F fc) sg R (Z_to_bv 64 pc) m rom _ true _ _ _ a Fw eq_refl Dw
                ltac:(fz) ltac:(rmok) ltac:(fh) ltac:(fbnd)) as (md & Hmd & S);
    cbv zeta in S; rewrite (to_w_val md n) in S by lia; cbn [fst snd] in S; rewrite sext64_w_small in S by lia;
    fnorm S; clear Hmd md; fgo S
  end.
Ltac f_csw Fw Dw rs v :=
  lazymatch goal with |- evt ?sg _ (MS ?R ?F (Z_to_bv 64 ?pc) ?fc None ?m ?rom) =>
    let md := fresh "md" in let Hmd := fresh "Hmd" in let S := fresh "S" in let A := fresh "A" in
    assert (A : PropExec.getr R rs = Z_to_bv 64 v) by reflexivity;
    destruct (hp_step_fcvt_s_w (PropExec.mkFP F fc) sg R (Z_to_bv 64 pc) m rom _ true _ _ _ Fw eq_refl Dw ltac:(fz) ltac:(rmok)) as (md & Hmd & S);
    cbv zeta in S; rewrite A, u64_of_Z, (of_int_val_gen md true 32 v) in S by lia; cbn [fst snd] in S; clear A Hmd md; fgo S
  end.
Ltac f_cvlu Fw Dw a n :=
  lazymatch goal with |- evt ?sg _ (MS ?R ?F (Z_to_bv 64 ?pc) ?fc None ?m ?rom) =>
    let md := fresh "md" in let Hmd := fresh "Hmd" in let S := fresh "S" in
    destruct (hp_step_fcvt_l_s (PropExec.mkFP F fc) sg R (Z_to_bv 64 pc) m rom _ false _ _ _ a Fw eq_refl Dw
                ltac:(fz) ltac:(rmok) ltac:(fh) ltac:(fbnd)) as (md & Hmd & S);
    cbv zeta in S; rewrite (to_lu_val md n) in S by lia; cbn [fst snd] in S; fnorm S; clear Hmd md; fgo S
  end.

Lemma lf_fp : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (rom : word -> option byte) (obj sz bc : Z),
  0 <= sz -> sz + 1 < 2 ^ 24 -> 0 <= bc < 2 ^ 24 ->
  0 <= obj -> obj + 40 <= 2 ^ 47 ->
  PropExec.rdn asegs m (Z_to_bv 64 (obj + 32)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0x3f800000)) ->
  frm_zero fc ->
  evt asegs (fun x => exists F' fc' a1, x = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 a1 (Z_to_bv 64 (sz + 1)) x13 x14 x15 x16 x17
                                               x18 x19 (Z_to_bv 64 bc) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                                          F' (Z_to_bv 64 (if (bc =? 0) || (bc <? sz + 1) then 0xfa6d8 else 0xfa7a4)) fc' None m rom
               /\ frm_zero fc' /\ fholds (PropExec.mkFP F' fc') 15 one32 /\ fholds (PropExec.mkFP F' fc') 14 (ieee (sz + 1)))
           (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (Z_to_bv 64 (obj + 32)) (Z_to_bv 64 sz) x13 x14 x15 x16 x17
                    x18 x19 (Z_to_bv 64 bc) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
               F (Z_to_bv 64 0xfa6b8) fc None m rom).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m rom obj sz bc Hsz Hsz1 Hbc Ho0 Ho1 RD FZ.
  pose proof (ieee_range (sz + 1) ltac:(lia)) as IE1.
  set (R := mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (Z_to_bv 64 (obj + 32)) (Z_to_bv 64 sz) x13 x14 x15 x16 x17
              x18 x19 (Z_to_bv 64 bc) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  eapply evt_step.
  { split; [reflexivity|].
    eapply (fp_step_flw (PropExec.mkFP F fc) asegs R (Z_to_bv 64 0xfa6b8) m rom W_f9d38 15%bv 11%bv 0%bv (Z_to_bv 64 (obj + 32)) _
              F_f9d38 eq_refl D_f9d38); [change (PropExec.getr R 11) with (Z_to_bv 64 (obj + 32)); change (bv_signed 0%bv) with 0;
                                          rewrite v_addi_Z by lia; f_equal; lia | exact RD]. }
  cbn [PropExec.fp_regs PropExec.fp_csr]. rewrite flw_nan_box by lia. rewrite mkst_MS. rewrite v_addi_Z by lia. npc. subst R.
  step.
  f_slu F_f9d40 D_f9d40 (12%bv : reg) (sz + 1).
  destruct (Z.eq_dec bc 0) as [Hb0 | Hb1].
  - subst bc. replace ((0 =? 0) || (0 <? sz + 1)) with true by reflexivity.
    step. brc.
    apply evt_done. eexists _, _, _. split; [reflexivity|]. split; [fz|]. split; fh.
  - replace ((bc =? 0) || (bc <? sz + 1)) with (bc <? sz + 1) by (rewrite (proj2 (Z.eqb_neq bc 0) Hb1); reflexivity).
    pose proof (ieee_range bc ltac:(lia)) as IE2.
    step. rewrite eqbZ by lia. rewrite (proj2 (Z.eqb_neq bc 0) Hb1). brc.
    f_slu F_f9d44 D_f9d44 (20%bv : reg) bc.
    f_ari F_f9d48 D_f9d48 one32 (ieee bc) mul_one_val.
    f_cmp F_f9d4c D_f9d4c (ieee bc) (ieee (sz + 1)) lt_val.
    destruct (bc <? sz + 1) eqn:LT.
    + step. brc. apply evt_done. eexists _, _, _. split; [reflexivity|]. split; [fz|]. split; fh.
    + step. brc. apply evt_done. eexists _, _, _. split; [reflexivity|]. split; [fz|]. split; fh.
Qed.

Definition W_fdiv : bv 32 := 0x18f777d3.
Definition W_fcvlu : bv 32 := 0xc0379553.
Lemma F_f9d74 : fetch_word asegs (Z_to_bv 64 0xfa6ec) = Some W_fdiv. Proof. vm_refl. Qed.
Lemma F_f9d78 : fetch_word asegs (Z_to_bv 64 0xfa75c) = Some W_fcvlu. Proof. vm_refl. Qed.
Lemma F_f9e5c : fetch_word asegs (Z_to_bv 64 0xfa70c) = Some W_fdiv. Proof. vm_refl. Qed.
Lemma D_fdiv : decode_any W_fdiv = Some (Fari F_DIV FMT_S 15 14 15 7, 4%Z). Proof. vm_refl. Qed.
Lemma D_fcvlu : decode_any W_fcvlu = Some (Fcvt (if false then FC_L else FC_LU) FC_S 10 15 1, 4%Z). Proof. vm_refl. Qed.
Definition W_fmvx : bv 32 := 0xf0060753.
Definition W_fabs : bv 32 := 0x20f7a6d3.
Definition W_flt23 : bv 32 := 0xa0e69653.
Definition W_fcvtw : bv 32 := 0xc007b653.
Definition W_fcvsw : bv 32 := 0xd0063753.
Definition W_fsgnj : bv 32 := 0x20f707d3.
Definition W_fltn1 : bv 32 := 0xa0f71653.
Definition W_flt64 : bv 32 := 0xa0e79653.
Lemma F_fa6f4 : fetch_word asegs (Z_to_bv 64 0xfa6f4) = Some W_fmvx. Proof. vm_refl. Qed.
Lemma F_fa6f8 : fetch_word asegs (Z_to_bv 64 0xfa6f8) = Some W_fabs. Proof. vm_refl. Qed.
Lemma F_fa6fc : fetch_word asegs (Z_to_bv 64 0xfa6fc) = Some W_flt23. Proof. vm_refl. Qed.
Lemma F_fa714 : fetch_word asegs (Z_to_bv 64 0xfa714) = Some W_fmvx. Proof. vm_refl. Qed.
Lemma F_fa718 : fetch_word asegs (Z_to_bv 64 0xfa718) = Some W_fabs. Proof. vm_refl. Qed.
Lemma F_fa71c : fetch_word asegs (Z_to_bv 64 0xfa71c) = Some W_flt23. Proof. vm_refl. Qed.
Lemma F_fa724 : fetch_word asegs (Z_to_bv 64 0xfa724) = Some W_fcvtw. Proof. vm_refl. Qed.
Lemma F_fa728 : fetch_word asegs (Z_to_bv 64 0xfa728) = Some W_fcvsw. Proof. vm_refl. Qed.
Lemma F_fa72c : fetch_word asegs (Z_to_bv 64 0xfa72c) = Some W_fsgnj. Proof. vm_refl. Qed.
Lemma F_fa734 : fetch_word asegs (Z_to_bv 64 0xfa734) = Some W_fmvx. Proof. vm_refl. Qed.
Lemma F_fa738 : fetch_word asegs (Z_to_bv 64 0xfa738) = Some W_fltn1. Proof. vm_refl. Qed.
Lemma F_fa744 : fetch_word asegs (Z_to_bv 64 0xfa744) = Some W_fmvx. Proof. vm_refl. Qed.
Lemma F_fa748 : fetch_word asegs (Z_to_bv 64 0xfa748) = Some W_flt64. Proof. vm_refl. Qed.
Lemma D_fmvx : decode_any W_fmvx = Some (Fmv FMV_F_X FMT_S 14 12, 4%Z). Proof. vm_refl. Qed.
Lemma D_fabs : decode_any W_fabs = Some (Fsgnj F_SGNJX FMT_S 13 15 15, 4%Z). Proof. vm_refl. Qed.
Lemma D_flt23 : decode_any W_flt23 = Some (Fcmp F_LT FMT_S 12 13 14, 4%Z). Proof. vm_refl. Qed.
Lemma D_fcvtw : decode_any W_fcvtw = Some (Fcvt (if true then FC_W else FC_WU) FC_S 12 15 3, 4%Z). Proof. vm_refl. Qed.
Lemma D_fcvsw : decode_any W_fcvsw = Some (Fcvt FC_S (if true then FC_W else FC_WU) 14 12 3, 4%Z). Proof. vm_refl. Qed.
Lemma D_fsgnj : decode_any W_fsgnj = Some (Fsgnj F_SGNJ FMT_S 15 14 15, 4%Z). Proof. vm_refl. Qed.
Lemma D_fltn1 : decode_any W_fltn1 = Some (Fcmp F_LT FMT_S 12 14 15, 4%Z). Proof. vm_refl. Qed.
Lemma D_flt64 : decode_any W_flt64 = Some (Fcmp F_LT FMT_S 12 15 14, 4%Z). Proof. vm_refl. Qed.

Definition gmax (f bc n : Z) : Z := if n <? 2 * bc + f then 2 * bc + f else n.
Definition grflag (bc : Z) : Z := if bc <? 3 then 1 else if 0 <? Z.land bc (bc + -1) then 1 else 0.
Definition grq (bc n : Z) : Z := gmax (grflag bc) bc n.

Ltac dv_tac Fd Fm Fa Fl n :=
  f_ari Fd D_fdiv (ieee n) one32 div_one_val;
  step;
  f_mvx Fm D_fmvx (12%bv : reg);
  f_sgnj Fa D_fabs (ieee n) (ieee n);
  f_cmp Fl D_flt23 (ieee n) two23f lt_two23_val.
Ltac rd_tac n :=
  f_cvw F_fa724 D_fcvtw (ieee n) n;
  f_csw F_fa728 D_fcvsw (12%bv : reg) n;
  f_sgnj F_fa72c D_fsgnj (ieee n) (ieee n).

Lemma tl_fp : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (rom : word -> option byte) (p f bc n : Z),
  0 <= p < 2 ^ 64 -> 0 <= f <= 1 -> 0 <= bc < 2 ^ 24 -> 1 <= n < 2 ^ 24 -> frm_zero fc ->
  fholds (PropExec.mkFP F fc) 15 (ieee n) ->
  evt asegs (fun x => exists F' fc' v10 v12 v20, x = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 v10 (Z_to_bv 64 (gmax f bc n)) v12 x13 x14 x15 x16 x17
                                                        x18 x19 v20 x21 x22 x23 (Z_to_bv 64 p) x25 x26 x27 x28 x29 x30 x31)
                                          F' (Z_to_bv 64 0xfa768) fc' None m rom /\ frm_zero fc')
           (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 p) (Z_to_bv 64 f) x12 x13 x14 x15 x16 x17
                    x18 x19 (Z_to_bv 64 bc) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
               F (Z_to_bv 64 0xfa730) fc None m rom).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m rom p f bc n Hp Hf Hbc Hn FZ H15.
  pose proof (ieee_range n Hn) as IE.
  step.
  f_mvx F_fa734 D_fmvx (12%bv : reg).
  f_cmp F_fa738 D_fltn1 neg1f (ieee n) lt_neg1_val.
  step. brc.
  step.
  f_mvx F_fa744 D_fmvx (12%bv : reg).
  f_cmp F_fa748 D_flt64 (ieee n) two64f lt_two64_val.
  step. brc.
  step. step. step.
  rewrite (u64_of_Z bc) by lia. rewrite Z.shiftl_mul_pow2 by lia. replace (bc * 2 ^ 1) with (2 * bc) by lia.
  rewrite (u64_of_Z f) by lia. rewrite (u64_of_Z (2 * bc)) by lia. rewrite lor_bit by lia.
  f_cvlu F_f9d78 D_fcvlu (ieee n) n.
  step. rewrite ltuZ by lia. unfold gmax.
  destruct (n <? 2 * bc + f) eqn:LT; brc.
  - apply evt_done. eexists _, _, _, _, _. split; [reflexivity | fz].
  - step. apply evt_done. eexists _, _, _, _, _. split; [reflexivity | fz].
Qed.

Lemma gr_fp : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (rom : word -> option byte) (p bc n : Z),
  0 <= p < 2 ^ 64 -> 0 <= bc < 2 ^ 24 -> 1 <= n < 2 ^ 24 -> frm_zero fc ->
  fholds (PropExec.mkFP F fc) 15 one32 -> fholds (PropExec.mkFP F fc) 14 (ieee n) ->
  evt asegs (fun x => exists F' fc' v10 v12 v20, x = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 v10 (Z_to_bv 64 (grq bc n)) v12 x13 x14 x15 x16 x17
                                                        x18 x19 v20 x21 x22 x23 (Z_to_bv 64 p) x25 x26 x27 x28 x29 x30 x31)
                                          F' (Z_to_bv 64 0xfa768) fc' None m rom /\ frm_zero fc')
           (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 p) x11 x12 x13 x14 x15 x16 x17
                    x18 x19 (Z_to_bv 64 bc) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
               F (Z_to_bv 64 0xfa6d8) fc None m rom).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m rom p bc n Hp Hbc Hn FZ H15 H14.
  pose proof (ieee_range n Hn) as IE.
  step.
  step. rewrite ltuZ by lia. unfold grq, grflag.
  destruct (bc <? 3) eqn:B3; brc.
  - step.
    dv_tac F_f9e5c F_fa714 F_fa718 F_fa71c n.
    destruct (n <? 2 ^ 23) eqn:E23.
    + step. brc. rd_tac n.
      eapply evt_mono; [eapply tl_fp with (n := n); [lia | try destruct (0 <? Z.land bc (bc + -1)); lia | lia | lia | fz | fh] |].
      intros ms' (F' & fc' & v10 & v12 & v20 & -> & FZ'). eexists _, _, _, _, _. split; [reflexivity | exact FZ'].
    + step. brc.
      eapply evt_mono; [eapply tl_fp with (n := n); [lia | try destruct (0 <? Z.land bc (bc + -1)); lia | lia | lia | fz | fh] |].
      intros ms' (F' & fc' & v10 & v12 & v20 & -> & FZ'). eexists _, _, _, _, _. split; [reflexivity | exact FZ'].
  - apply Z.ltb_ge in B3.
    step. step. step.
    rewrite (u64_of_Z bc), (u64_of_Z (bc + -1)) by lia.
    pose proof (land_lt64 bc (bc + -1) ltac:(lia)) as LB.
    unfold BLPropExec.v_sltu, BLPropExec.c_ltu. rewrite ltuZ by lia. rewrite ifZ.
    dv_tac F_f9d74 F_fa6f4 F_fa6f8 F_fa6fc n.
    destruct (n <? 2 ^ 23) eqn:E23.
    + step. brc. rd_tac n.
      eapply evt_mono; [eapply tl_fp with (n := n); [lia | try destruct (0 <? Z.land bc (bc + -1)); lia | lia | lia | fz | fh] |].
      intros ms' (F' & fc' & v10 & v12 & v20 & -> & FZ'). eexists _, _, _, _, _. split; [reflexivity | exact FZ'].
    + step. brc. step.
      eapply evt_mono; [eapply tl_fp with (n := n); [lia | try destruct (0 <? Z.land bc (bc + -1)); lia | lia | lia | fz | fh] |].
      intros ms' (F' & fc' & v10 & v12 & v20 & -> & FZ'). eexists _, _, _, _, _. split; [reflexivity | exact FZ'].
Qed.
