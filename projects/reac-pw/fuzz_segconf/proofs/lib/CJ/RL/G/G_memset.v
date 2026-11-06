(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib Require Import Tac Arr.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Spec Require Import StrFun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.P Require Import STRW_memset.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc Require RProgAt.
Import OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc.RProgAt.RTac.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.G Require G_memcpy.
Import OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.G.G_memcpy.GSTRW_tac. From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc Require Import RProgNotJ. From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc Require Import RProgNot. From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc Require RegFold. From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc Require RProgAt. From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc Require JunkAbs.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Definition memset_prog (B : Z) : RStep.ptree :=
  PNode 124%Z
  (PNode 60%Z
    (PLeaf
        (PJ_Branch_BC_EQ_nnn 0 12 0 244 4
        (PJ_Store_SZ1_nnn 4 10 11 0 4
        (PJ_Op_ALU_ADD_nnn 8 13 10 12 4
        (PJ_OpImm_ALU_ADD_nnn 12 14 0 3 4
        (PJ_Store_SZ1_nnn 16 13 11 4095 4
        (PJ_Branch_BC_LTU_nnn 20 12 14 224 4
        (PJ_Store_SZ1_nnn 24 10 11 1 4
        (PJ_Store_SZ1_nnn 28 10 11 2 4
        (PJ_OpImm_ALU_ADD_nnn 32 14 0 7 4
        (PJ_Store_SZ1_nnn 36 13 11 4093 4
        (PJ_Store_SZ1_nnn 40 13 11 4094 4
        (PJ_Branch_BC_LTU_nnn 44 12 14 200 4
        (PJ_Store_SZ1_nnn 48 10 11 3 4
        (PJ_OpImm_ALU_ADD_nnn 52 15 0 9 4
        (PJ_Store_SZ1_nnn 56 13 11 4092 4 nil))))))))))))))))
    (PLeaf
        (PJ_Branch_BC_LTU_nnn 60 12 15 184 4
        (PJ_Op32_ALU_SUB_nnn 64 13 0 10 4
        (PJ_ShiftImm_ALU_SLL_nnn 68 16 11 56 4
        (PJ_Lui_nn 72 11 65793 4
        (PJ_OpImm_ALU_AND_nnn 76 13 13 3 4
        (PJ_ShiftImm_ALU_SLL_nnn 80 14 11 4 4
        (PJ_Op_ALU_SUB_nnn 84 12 12 13 4
        (PJ_Op_ALU_ADD_nnn 88 11 10 13 4
        (PJ_OpImm_ALU_ADD_nnn 92 13 14 256 4
        (PJ_OpImm_ALU_AND_nnn 96 14 12 4092 4
        (PJ_Mul_M_MULHU_nnn 100 12 16 13 4
        (PJ_Store_SZ4_nnn 104 11 12 0 4
        (PJ_Op_ALU_ADD_nnn 108 13 11 14 4
        (PJ_Store_SZ4_nnn 112 13 12 4092 4
        (PJ_Branch_BC_LTU_nnn 116 14 15 128 4
        (PJ_Store_SZ4_nnn 120 11 12 4 4 nil))))))))))))))))))
  (PNode 184%Z
    (PLeaf
        (PJ_Store_SZ4_nnn 124 11 12 8 4
        (PJ_OpImm_ALU_ADD_nnn 128 15 0 25 4
        (PJ_Store_SZ4_nnn 132 13 12 4084 4
        (PJ_Store_SZ4_nnn 136 13 12 4088 4
        (PJ_Branch_BC_LTU_nnn 140 14 15 104 4
        (PJ_Store_SZ4_nnn 144 11 12 12 4
        (PJ_Store_SZ4_nnn 148 11 12 16 4
        (PJ_Store_SZ4_nnn 152 11 12 20 4
        (PJ_Store_SZ4_nnn 156 11 12 24 4
        (PJ_OpImm_ALU_AND_nnn 160 15 11 4 4
        (PJ_OpImm_ALU_ADD_nnn 164 16 0 32 4
        (PJ_OpImm_ALU_ADD_nnn 168 15 15 24 4
        (PJ_Op_ALU_SUB_nnn 172 14 14 15 4
        (PJ_Store_SZ4_nnn 176 13 12 4068 4
        (PJ_Store_SZ4_nnn 180 13 12 4072 4 nil))))))))))))))))
    (PLeaf
        (PJ_Store_SZ4_nnn 184 13 12 4076 4
        (PJ_Store_SZ4_nnn 188 13 12 4080 4
        (PJ_Branch_BC_LTU_nnn 192 14 16 52 4
        (PJ_ShiftImm_ALU_SLL_nnn 196 12 12 32 4
        (PJ_Op_ALU_ADD_nnn 200 11 11 15 4
        (PJ_ShiftImm_ALU_SRL_nnn 204 13 12 32 4
        (PJ_Op_ALU_OR_nnn 208 12 12 13 4
        (PJ_OpImm_ALU_ADD_nnn 212 13 0 31 4
        (PJ_Store_SZ8_nnn 216 11 12 0 4
        (PJ_Store_SZ8_nnn 220 11 12 8 4
        (PJ_Store_SZ8_nnn 224 11 12 16 4
        (PJ_Store_SZ8_nnn 228 11 12 24 4
        (PJ_OpImm_ALU_ADD_nnn 232 14 14 4064 4
        (PJ_OpImm_ALU_ADD_nnn 236 11 11 32 4
        (PJ_Branch_BC_LTU_nnn 240 13 14 8168 4
        (PJ_Jalr_nnn 244 0 1 0 4 nil)))))))))))))))))).

(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib.Step.step2_with rp rpm vh ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_with rp rpm vh.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib.SysStep.step_ecall ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc.RProgAt.RTac.astep_ecall.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib.Step.solve_load ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc.RProgAt.RTac.asolve_load.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib.Step.solve_cond ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc.RProgAt.RTac.asolve_cond.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib.Step.step ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib.Step.stepz ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib.Step.stepz_fast ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc.RProgAt.RTac.astep2_fast.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib.SysStep.sys_nret ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc.RProgAt.RTac.asys_nret.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib.Tac.post_call segs m ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc.RProgAt.RTac.apost_call segs m.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.G Require G_memcpy.
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.P.Exit_tac.STRW_tac.cur_mem_addr ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.G.G_memcpy.GSTRW_tac.acur_mem_addr.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib.Step.simp_regs ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc.RegFold.simp_regs_f.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc.RProgAt.RTac.find_t_eval k t ::= OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc.RProgAt.find_t_eval_at k t.
Definition PROGAT_CODE_memset (IMG : RImg) := memset_prog (sym 0x21738).
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib.Step.split_for_access H segs m A cs kn n ::=
  OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.Reloc.JunkAbs.split_for_access_abs H segs m A cs kn n.
Section Img.
  Context {IMG : RImg}.
  Context {CODE_memset : CodeAtT img_segs (sym 0x21738) (PROGAT_CODE_memset IMG)}.
  Context {RB_memset : RelCode (sym 0x21738) 248}.
  Collection ImgHyps := IMG CODE_memset RB_memset.



Definition memset_entry := (sym 0x21738)%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac with_arr tac :=
  lazymatch goal with
  | ARR : u8arr ?segs ?m ?A ?bs, FIL : filled ?cb ?bs _, LEN : length ?bs = _ |- _ => tac segs ARR FIL LEN A cb
  end.

(* [comment removed for export] *)
Ltac brute256 c Rc :=
  first [ apply word_eq_of_eqb | apply Z.eqb_eq | idtac ];
  repeat match goal with H : context [c] |- _ => tryif constr_eq H Rc then fail else clear H end;
  revert c Rc; apply brute256_ok; vm_compute; reflexivity.

(* [comment removed for export] *)
Ltac reg_val r :=
  lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
    let p := eval vm_compute in (bv_key (Z_to_bv 5 r)) in
    eval cbv beta iota delta [tget mkR] in (match tget p R with Some v => v | None => w0 end)
  end.
(* [comment removed for export] *)
Ltac setreg r v' tac := let v := reg_val r in replace v with v' by tac.

Lemma land4_of_aligned : forall x, (0 <= x)%Z -> (x mod 4 = 0)%Z -> Z.land x 4 = (x mod 8)%Z.
Proof.
  intros x Hx H4.
  transitivity (Z.land (x mod 8) 4).
  { change 8%Z with (2^3)%Z. rewrite <- Z.land_ones by lia. change (Z.ones 3) with 7%Z.
    rewrite <- Z.land_assoc. reflexivity. }
  assert (R : (x mod 8 = 0 \/ x mod 8 = 4)%Z) by (Z.div_mod_to_equations; lia).
  destruct R as [R|R]; rewrite R; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition memset_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 a2 : word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom img_segs)
    /\ munch [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z m m' /\ wmono img_segs m m' /\ mem_inv img_segs m'
    /\ rw_cells img_segs m' (bv_unsigned a0)
         [CB (Z.to_nat (bv_unsigned a2)) (repeat (Z_to_bv 8 (bv_unsigned a1 mod 256)) (Z.to_nat (bv_unsigned a2)))].

Section Proofs.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Hypothesis MI0 : mem_inv img_segs m.
  Hypothesis AB : (0 <= bv_unsigned a0 /\ bv_unsigned a0 + bv_unsigned a2 <= 2^64 /\ 0 <= bv_unsigned a2 < 2^64)%Z.

  Notation A := (bv_unsigned a0).
  Notation n := (bv_unsigned a2).
  Notation W := [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z.
  Notation POST := (memset_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 m).
  (* [comment removed for export] *)
  Notation ST pc mm x11 x12 x13 x14 x15 x16 :=
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 x11 x12 x13 x14 x15 x16 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom img_segs)).

  (* [comment removed for export] *)
  Ltac fin_with cover :=
    zstep;
    with_arr ltac:(fun segs ARR FIL LEN A cb =>
      let E := fresh "E" in
      pose proof (filled_all _ _ _ FIL ltac:(cover)) as E;
      rewrite LEN in E; rewrite E in ARR;
      apply rw_cells_of_u8arr in ARR; rewrite repeat_length in ARR);
    finish; subst; assumption.
  Ltac fin := fin_with ltac:(intros j Hj; cbv beta; lia).
  Ltac disj_lia := first [ lia | right; lia | left; disj_lia ].

  (* [comment removed for export] *)
  Lemma memset_loop : forall (K : nat) (c p r e : Z) (m1 : word -> option byte) (bs : list byte) (Q : Z -> Prop)
      (x15 x16 : word),
    Z.to_nat r = K ->
    c = (bv_unsigned a1 mod 256)%Z ->
    u8arr img_segs m1 A bs -> filled (Z_to_bv 8 c) bs Q -> length bs = Z.to_nat n ->
    mem_inv img_segs m1 -> munch W m m1 -> wmono img_segs m m1 ->
    (forall j, (0 <= j < p \/ e <= j < n) -> Q j)%Z ->
    (0 <= p)%Z -> (32 <= r)%Z -> (exists q, r = 4 * q)%Z -> (p + r <= n)%Z -> (e + 28 <= p + r)%Z ->
    evt img_segs POST (ST (sym 0x21738 + 216) m1 (Z_to_bv 64 (A + p)) (Z_to_bv 64 (c * BC8)) (Z_to_bv 64 31) (Z_to_bv 64 r) x15 x16).
  Proof using AB ImgHyps.
    induction K as [K IH] using lt_wf_ind; intros c p r e m1 bs Q x15 x16 HK Hc ARR FIL LEN MI MU WM HQ Hp Hr [q4 Hq4] Hpr He;
      assert (Rc : (0 <= c < 256)%Z) by (subst c; apply Z.mod_pos_bound; lia).
    mst p 8%nat ltac:(symmetry; apply le8_bcast; lia).
    mst (p + 8)%Z 8%nat ltac:(symmetry; apply le8_bcast; lia).
    mst (p + 16)%Z 8%nat ltac:(symmetry; apply le8_bcast; lia).
    mst (p + 24)%Z 8%nat ltac:(symmetry; apply le8_bcast; lia).
    zstep. zstep. zstep.
    if_cases KK; zify_cond KK.
    - (* [comment removed for export] *)
      replace (A + p + 32)%Z with (A + (p + 32))%Z by lia.
      replace (r + -32)%Z with (r - 32)%Z by lia.
      eapply (IH (Z.to_nat (r - 32)) ltac:(lia) c (p + 32)%Z (r - 32)%Z e _ _ _ x15 x16 eq_refl Hc ARR); try eassumption; try lia.
      2:{ exists (q4 - 8)%Z. lia. }
      intros j Hj.
      destruct (Z_lt_le_dec j p) as [Hlt|Hge]. { left; left; left; left. apply HQ. lia. }
      destruct (Z_lt_le_dec j (p + 32)) as [Hlt2|Hge2]. 2:{ left; left; left; left. apply HQ. lia. }
      assert (D : ((p <= j < p + 8 \/ p + 8 <= j < p + 16) \/ (p + 16 <= j < p + 24 \/ p + 24 <= j < p + 32))%Z) by lia.
      destruct D as [[?|?]|[?|?]]; [left; left; left; right| left; left; right| left; right| right]; lia.
    - fin_with ltac:(intros j Hj; destruct (Z_lt_le_dec j p); [repeat left; apply HQ; lia|];
                      destruct (Z_lt_le_dec j (p + 32)); [|repeat left; apply HQ; lia]; disj_lia).
  Qed.

  Lemma memset_body : forall junk,
    rw_cells img_segs m A [CB (Z.to_nat n) junk] ->
    evt img_segs POST (ST (sym 0x21738) m a1 a2 a3 a4 a5 a6).
  Proof using AB MI0 ImgHyps.
    intros junk DST. pose proof MI0 as MI.
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl img_segs m) as WM.
    pose proof (zr_word a1) as R1. unfold inr64 in R1.
    remember (bv_unsigned a1 mod 256)%Z as c eqn:Hc.
    assert (Rc : (0 <= c < 256)%Z) by (subst c; apply Z.mod_pos_bound; lia).
    pose proof (u8arr_of_rw_cells _ _ _ _ _ DST) as ARR.
    pose proof (rw_cells_CB_length _ _ _ _ _ DST) as LEN.
    pose proof (filled_init (Z_to_bv 8 c) junk) as FIL.
    (* [comment removed for export] *)
    zstep. if_cases K0; zify_cond K0. { fin. }
    assert (MF : ms_facts A n 0 1) by (unfold ms_facts; lia).
    pose proof (ms_store_ok img_segs _ A n _ 0 1 a0 ARR LEN MF (eq_sym (Z_to_bv_plus0 a0))) as SOK.
    zstep. ms_arr_store MF ltac:(rewrite Hc, le1_byte; reflexivity).
    zstep. zstep. mst (n - 1)%Z 1%nat ltac:(rewrite Hc, le1_byte; reflexivity).
    zstep. if_cases K3; zify_cond K3. { fin. }
    mst 1%Z 1%nat ltac:(rewrite Hc, le1_byte; reflexivity).
    mst 2%Z 1%nat ltac:(rewrite Hc, le1_byte; reflexivity).
    zstep.
    mst (n - 3)%Z 1%nat ltac:(rewrite Hc, le1_byte; reflexivity).
    mst (n - 2)%Z 1%nat ltac:(rewrite Hc, le1_byte; reflexivity).
    zstep. if_cases K7; zify_cond K7. { fin. }
    mst 3%Z 1%nat ltac:(rewrite Hc, le1_byte; reflexivity).
    zstep.
    mst (n - 4)%Z 1%nat ltac:(rewrite Hc, le1_byte; reflexivity).
    zstep. if_cases K9; zify_cond K9. { fin. }
    (* [comment removed for export] *)
    zstep. zstep.
    setreg 16%Z (Z_to_bv 64 (c * 2^56)) ltac:(apply Z_to_bv_eqm; rewrite Z.shiftl_mul_pow2 by lia; subst c; Z.div_mod_to_equations; lia).
    zstep. zstep.
    remember (Z.land (bv_swrap 32 (0 - A) mod 18446744073709551616) 3) as k eqn:Hk.
    assert (Rk : (0 <= k < 4 /\ (A + k) mod 4 = 0)%Z).
    { subst k. change 3%Z with (2^2 - 1)%Z. rewrite zb_land_mask by lia.
      unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
      change (2 ^ (Z.of_N 32 - 1))%Z with (2^31)%Z. change (2 ^ Z.of_N 32)%Z with (2^32)%Z.
      Z.div_mod_to_equations. lia. }
    clear Hk.
    zstep. zstep. zstep. zstep. zstep.
    change 18446744073709551612%Z with (2^64 - 2^2)%Z. rewrite land_align_down by lia.
    remember (n - k - (n - k) mod 2^2)%Z as n4 eqn:Hn4.
    assert (Rn4 : (exists q, n4 = 4 * q)%Z /\ (n - k - 3 <= n4 <= n - k)%Z).
    { split. { exists ((n - k) / 4)%Z. subst n4. Z.div_mod_to_equations. lia. } subst n4. Z.div_mod_to_equations. lia. }
    clear Hn4. destruct Rn4 as [[q4 Hq4] Rn4].
    zstep. setreg 12%Z (Z_to_bv 64 (c * BC4)) ltac:(unfold BC4; brute256 c Rc).
    (* [comment removed for export] *)
    mst k 4%nat ltac:(symmetry; apply le4_bcast; lia).
    zstep. mst (k + n4 - 4)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
    zstep. if_cases K9'; zify_cond K9'. { fin. }
    mst (k + 4)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
    mst (k + 8)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
    zstep.
    mst (k + n4 - 12)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
    mst (k + n4 - 8)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
    zstep. if_cases K25; zify_cond K25. { fin. }
    mst (k + 12)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
    mst (k + 16)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
    mst (k + 20)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
    mst (k + 24)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
    (* [comment removed for export] *)
    zstep.
    remember (Z.land (A + k) 4) as k4 eqn:Hk4.
    assert (Rk4 : ((k4 = 0 \/ k4 = 4) /\ (A + k + k4 + 24) mod 8 = 0)%Z).
    { subst k4. rewrite land4_of_aligned by lia. Z.div_mod_to_equations. lia. }
    clear Hk4.
    zstep. zstep. zstep.
    mst (k + n4 - 28)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
    mst (k + n4 - 24)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
    mst (k + n4 - 20)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
    mst (k + n4 - 16)%Z 4%nat ltac:(symmetry; apply le4_bcast; lia).
    zstep. if_cases K32; zify_cond K32. { fin. }
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. setreg 12%Z (Z_to_bv 64 (c * BC8)) ltac:(unfold BC4, BC8; brute256 c Rc).
    zstep.
    replace (A + k + (k4 + 24))%Z with (A + (k + k4 + 24))%Z by lia.
    eapply (memset_loop _ c (k + k4 + 24) _ (k + n4 - 28) _ _ _ _ _ eq_refl Hc ARR); try eassumption; try lia.
    exists (q4 - Z.div k4 4 - 6)%Z. lia.
  Qed.
End Proofs.

Lemma memset_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (junk : list byte),
  rw_cells img_segs m (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) junk] ->
  mem_inv img_segs m ->
  evt img_segs (memset_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (sym 0x21738)) fc None m (seg_rom img_segs)).
Proof.
  intros until junk. intros DST MI.
  eapply memset_body; [exact MI | | exact DST].
  pose proof (rw_cells_bound _ _ _ _ DST) as B. cbn [cells_size csize Nat.add] in B.
  pose proof (bv_unsigned_in_range 64 a2) as R. unfold bv_modulus in R. cbn in R. cbn. lia.
Qed.

(* [comment removed for export] *)
Definition memset_contract : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (junk : list byte),
  rw_cells img_segs m (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) junk] ->
  mem_inv img_segs m ->
  evt img_segs (memset_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (sym 0x21738)) fc None m (seg_rom img_segs)).
Lemma memset_contract_ok : memset_contract.
Proof. exact memset_spec. Qed.


End Img.
(* [comment removed for export] *)
Ltac with_arr tac :=
  lazymatch goal with
  | ARR : u8arr ?segs ?m ?A ?bs, FIL : filled ?cb ?bs _, LEN : length ?bs = _ |- _ => tac segs ARR FIL LEN A cb
  end.
Ltac brute256 c Rc :=
  first [ apply word_eq_of_eqb | apply Z.eqb_eq | idtac ];
  repeat match goal with H : context [c] |- _ => tryif constr_eq H Rc then fail else clear H end;
  revert c Rc; apply brute256_ok; vm_compute; reflexivity.
Ltac reg_val r :=
  lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
    let p := eval vm_compute in (bv_key (Z_to_bv 5 r)) in
    eval cbv beta iota delta [tget mkR] in (match tget p R with Some v => v | None => w0 end)
  end.
Ltac setreg r v' tac := let v := reg_val r in replace v with v' by tac.

(* [comment removed for export] *)
Existing Class memset_contract.
