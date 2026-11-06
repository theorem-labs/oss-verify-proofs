(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Shadow.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Bigint_defs Bigint_shl.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFA Require Import A_cap.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require Import B_rt_stmt B_rt_lemmas B_long_mul_stmt B_pow5_stmt B_shl_stmt B_pow10_stmt.

Module B_large_mul_stmt.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Shadow.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Bigint_defs.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require Import B_rt_stmt B_long_mul_stmt.
Local Ltac lia ::= lia_tc.  (* [comment removed for export] *)
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.

Notation BSEGS := AsanUbsan.M.loaded_segments.

(* [comment removed for export] *)
Notation LGM_ENTRY := 0x971d8%Z.

Definition large_mul_entry : Z := LGM_ENTRY.
Definition large_mul_need : Z := 2544.

Definition large_mul_W (sp A FS : Z) : list ivl :=
  [(sp - 2544, sp); (A, A + 498);
   (FS + FK5_HINT, FS + FK5_HINT + 8); (FS + FK5_FLAGS, FS + FK5_FLAGS + FK5_NFLAGS);
   (FS + FK5_LO, FS + FK5_HI); (ASAN_B + FS / 8 + FK5_SLO, ASAN_B + FS / 8 + FK5_SHI)]%Z.

Definition large_mul_post
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (A : Z) (ws : list word) (len : Z) (v : rt_vals)
    (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte)
                    (ws' : list word) (len' : Z) (h5' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom BSEGS)
    /\ munch (large_mul_W (bv_unsigned sp) A (rt_FS v)) m m'
    /\ wmono BSEGS m m'
    /\ stk BSEGS m' (bv_unsigned sp - 2544) (bv_unsigned sp)
    /\ u64arr BSEGS m' A ws'
    /\ length ws' = 62%nat
    /\ rw_cells BSEGS m' (A + 496) [C2 (Z_to_bv 64 len')]
    /\ (0 <= len' <= 62)%Z
    /\ (len' <= len + 6)%Z
    /\ bnorm ws' (Z.to_nat len')
    /\ pristine m' IMG_LO ROD_HI
    /\ RT m' v
    /\ fk5_inv m' (rt_FS v) h5'.

Definition large_mul_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (ws : list word) (len : Z) (v : rt_vals) (h5 : word),
    let FS := rt_FS v in
    stk BSEGS m (bv_unsigned sp - 2544) (bv_unsigned sp) ->
    (bv_unsigned sp mod 16 = 0)%Z ->
    (IMG_END <= bv_unsigned sp - 2544)%Z ->
    pristine m IMG_LO ROD_HI ->
    u64arr BSEGS m (bv_unsigned a0) ws -> length ws = 62%nat ->
    rw_cells BSEGS m (bv_unsigned a0 + 496) [C2 (Z_to_bv 64 len)] ->
    (0 <= len <= 62)%Z -> (bv_unsigned a0 mod 8 = 0)%Z ->
    bnorm ws (Z.to_nat len) ->
    a1 = Z_to_bv 64 B_LARGE_POW5 -> a2 = Z_to_bv 64 5 ->
    (len + 5 <= LM_T)%Z ->                     (* [comment removed for export] *)
    (bv_unsigned a0 + 498 <= bv_unsigned sp - 2544 \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
    (* [comment removed for export] *)
    tp = Z_to_bv 64 TPV ->
    pristine m RELRO_LO RELRO_HI -> pristine m REALTAB_LO REALTAB_HI ->
    RT m v ->
    fk5_inv m FS h5 ->
    (* [comment removed for export] *)
    (KHI <= bv_unsigned sp - 2544)%Z -> (bv_unsigned sp <= KTOP)%Z ->
    (app2r (bv_unsigned a0) (bv_unsigned a0 + 504))%Z -> (bv_unsigned a0 + 504 <= KTOP)%Z ->
    (FS + FSSIZE <= bv_unsigned sp - 2544)%Z ->
    (FS + 4231168 <= bv_unsigned a0 /\ bv_unsigned a0 + 632 <= FS + FK5_LO)%Z ->
    rt_disj v (bv_unsigned sp - 2544) (bv_unsigned sp) ->
    rt_disj v (bv_unsigned a0) (bv_unsigned a0 + 498) ->
    rt_disj v FS (FS + FSSIZE) ->
    (* [comment removed for export] *)
    shz BSEGS m (ASAN_B + bv_unsigned a0 / 8) 63 ->
    shz BSEGS m POW5TAB_SH POW5TAB_SHN ->
    rdbl BSEGS m (ASAN_B + bv_unsigned a0 / 8 - 8) 79 ->
    rdbl BSEGS m (ASAN_B + FS / 8 + FK_SH_LO) FK_SH_N ->
    RTX v fc ->   (* [comment removed for export] *)
    (* [comment removed for export] *)
    shz BSEGS m (ASAN_B + (bv_unsigned sp - 2544) / 8) 318 ->
    evt BSEGS (large_mul_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                 F fc (bv_unsigned a0) ws len v m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 LGM_ENTRY) fc None m (seg_rom BSEGS)).
End B_large_mul_stmt.

Module B_large_mul.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Shadow.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Bigint_defs.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_rt_stmt B_rt_lemmas B_long_mul_stmt.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_rt_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_rt_lemmas OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_long_mul_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_pow10.B_large_mul_stmt.
Local Ltac lia ::= lia_tc.  (* [comment removed for export] *)
Local Ltac step ::=
  app2_lin_all;
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) => step_core segs R F pc fc rv m ro; try decide_lit_if
  | |- evt _ _ (MS _ _ ?pc _ _ _ _) => fail "pc is not a literal:" pc
  end.  (* [comment removed for export] *)
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac simpl_arr_sizes ::= tryif kp_sas_pre5 then (rewrite ?u32s_length, ?u64s_length, ?upd_length, ?zeros_length in *) else idtac.      (* [comment removed for export] *)

(* [comment removed for export] *)
Ltac solve_W_ok_rt := solve_W_rt.  (* [comment removed for export] *)

(* [comment removed for export] *)
Ltac open_fk5 H :=
  let a := fresh "FK1" in let b := fresh "FK2" in let c := fresh "FK3" in let d := fresh "FK4" in let e := fresh "FK5" in
  destruct H as (a & b & c & d & e); unfold fs_cells_ok in a.
Ltac close_fk5 := unfold fk5_inv, fs_cells_ok; repeat match goal with |- _ /\ _ => split end; eassumption.

Section Main.
  Hypothesis long_mul_spec : long_mul_stmt.

  #[using="long_mul_spec"] Lemma large_mul_spec : large_mul_stmt.
  Proof. LiaFast.lf_pins (fun (long_mul_spec : LiaFast.U) => LiaFast.u0).
    unfold large_mul_stmt. intros until h5. cbv zeta.
    intros ST AL SPLO PR LIMBS L62 LENC Hlen A8 NORM Ha1 Ha2 CAP SEP TP PRG PRT RTH FK KSP KSP2 KA0 KA1 SFS SEPF RD1 RD2 RD3 SHX SHT RBX RBF RTX0 SHW.
    subst a1 a2.
    pose proof (munch_refl (large_mul_W (bv_unsigned sp) (bv_unsigned a0) (rt_FS v)) m) as MU.
    cbv delta [large_mul_W] in MU.
    pose proof (wmono_refl BSEGS m) as WM.
    pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
    pose proof (u64arr_bound _ _ _ _ LIMBS) as Bl. rewrite L62 in Bl.
    pose proof (rw_cells_bound _ _ _ _ LENC) as Bc. cbn [cells_size csize Nat.add] in Bc.
    open_RT_keep RTH.
    destruct RTP as (Hbeg & Hblk & Hblk1 & Hctx & Hthr & HFS1 & HFS2 & HFS3 & Hc1 & Hc2 & Ht1 & Ht2 & Hb1 & Hb2).
    clear RT1 RT2 RT2b RT3 RT4 RT5 RT6 RT7 RT8 RT9 RT10 RT11 RT12 RT13 RT14 Hfb fb.
    open_fk5 FK.
    carve_frame 16%nat ST.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    pose proof (unsigned_lit (bv_unsigned sp + -16) ltac:(lia)) as ULs.
    step. (* [comment removed for export] *)
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      eapply evt_cut; [ eapply long_mul_spec with (v := v) (h5 := h5) (ws := ws) (len := len) | post_call BSEGS mc ] end.
    1:{ rewrite ULs. replace (bv_unsigned sp + -16 - 2528)%Z with (bv_unsigned sp - 2544)%Z by lia. exact ST. }
    1:{ rewrite ULs. Z.div_mod_to_equations. lia. }
    1:{ rewrite ULs. lia. }
    1:{ exact PR. } 1:{ exact LIMBS. } 1:{ exact L62. } 1:{ exact LENC. } 1:{ exact Hlen. } 1:{ exact A8. } 1:{ exact NORM. }
    1:{ reflexivity. } 1:{ reflexivity. } 1:{ exact CAP. }
    1:{ rewrite ULs. lia. }
    1:{ exact TP. } 1:{ exact PRG. } 1:{ exact PRT. }
    1:{ eapply RT_transport; [exact RTH | exact MU | solve_W_ok_rt]. }
    1:{ close_fk5. }
    1:{ rewrite ULs. lia. } 1:{ rewrite ULs. lia. } 1:{ exact KA0. } 1:{ exact KA1. }
    1:{ rewrite ULs. lia. } 1:{ exact SEPF. }
    1:{ rewrite ULs. eapply rt_disj_sub; [exact RD1 | lia | lia]. }
    1:{ exact RD2. } 1:{ exact RD3. }
    1:{ exact SHX. } 1:{ exact SHT. } 1:{ exact RBX. } 1:{ exact RBF. } 1:{ exact RTX0. } 1:{ vm_compute; reflexivity. }
    1:{ rewrite ULs. eapply shz_sub; [exact SHW | Z.div_mod_to_equations; lia | lia | Z.div_mod_to_equations; lia]. }
    rewrite ?ULs in *.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. step. step. (* [comment removed for export] *)
    match goal with H : stk BSEGS _ (bv_unsigned sp + -16 - 2528) _ |- _ => rename H into ST2 end.
    replace (bv_unsigned sp + -16 - 2528)%Z with (bv_unsigned sp - 2544)%Z in ST2 by lia.
    release_frame FR ST2 (bv_unsigned sp).
    unfold large_mul_post. finish.
    all: try eassumption. all: try lia.
  Qed.
End Main.
End B_large_mul.

Module B_pow5_A.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Shadow.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Bigint_defs Bigint_shl.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require Import B_app2.
Local Ltac lia ::= lia_tc.  (* [comment removed for export] *)
Local Ltac step ::=
  app2_lin_all;
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) => step_core segs R F pc fc rv m ro; try decide_lit_if
  | |- evt _ _ (MS _ _ ?pc _ _ _ _) => fail "pc is not a literal:" pc
  end.  (* [comment removed for export] *)
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation BSEGS := AsanUbsan.M.loaded_segments.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section smulM.
  Variables (x1 x2 x3 x4 x5 x6 x8 x9 x10 x12 x13 x14 x20 x21 x22 x23 x24 x25 x26 x27 : word).
  Variables (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte).
  Variables (A y : Z) (ws : list word) (len : Z).
  Hypothesis L62 : length ws = 62%nat.
  Hypothesis LEN : (0 < len <= 62)%Z.
  Hypothesis Hy : (0 <= y < 2 ^ 64)%Z.
  Hypothesis KA : (app2r A (A + 504)).
  Hypothesis KA' : (A + 504 <= KTOP)%Z.

  Definition smulM_post (m : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists (c' : Z) (q' cnt' lo' lo2' ex' : word) (m' : word -> option byte) (cur : list word),
      ms' = MS (mkR x1 x2 x3 x4 x5 x6 (Z_to_bv 64 c') x8 x9 x10 q' x12 x13 x14 (Z_to_bv 64 y) (Z_to_bv 64 len) (Z_to_bv 64 63) ex' (Z_to_bv 64 ASAN_B) x20 x21 x22 x23 x24 x25 x26 x27 cnt' (Z_to_bv 64 (A + 8 * len)) lo' lo2')
               F (Z_to_bv 64 0x97024) fc None m' (seg_rom BSEGS)
      /\ munch [(A, A + 8 * len)]%Z m m'
      /\ wmono BSEGS m m'
      /\ u64arr BSEGS m' A cur
      /\ length cur = 62%nat
      /\ smul_inv ws cur y (Z.to_nat len) c'.

  Definition smulM_ok (k : nat) : Prop :=
    forall (i : nat) (p q cnt lo lo2 ex : word) (c : Z) (cur : list word) (m : word -> option byte),
      (Z.to_nat len - i = k)%nat -> (i < Z.to_nat len)%nat ->
      bv_unsigned p = (A + 8 * Z.of_nat i)%Z ->
      bv_unsigned q = (A + 8 * Z.of_nat i)%Z ->
      bv_unsigned cnt = (63 - Z.of_nat i)%Z ->
      u64arr BSEGS m A cur -> length cur = 62%nat ->
      smul_inv ws cur y i c ->
      shz BSEGS m (ASAN_B + A / 8) 63 ->
      munch [(A, A + 8 * len)]%Z m0 m -> wmono BSEGS m0 m ->
      evt BSEGS (smulM_post m0)
        (MS (mkR x1 x2 x3 x4 x5 x6 (Z_to_bv 64 c) x8 x9 x10 q x12 x13 x14 (Z_to_bv 64 y) (Z_to_bv 64 len) (Z_to_bv 64 63) ex (Z_to_bv 64 ASAN_B) x20 x21 x22 x23 x24 x25 x26 x27 cnt p lo lo2)
            F (Z_to_bv 64 0x96fe0) fc None m (seg_rom BSEGS)).

  #[using="L62 LEN Hy KA"] Lemma smulM_body : forall k, smulM_ok k -> smulM_ok (S k).
  Proof. LiaFast.lf_pins (fun (L62 LEN Hy KA : LiaFast.U) => LiaFast.u0).
    intros k IH. unfold smulM_ok. intros i p q cnt lo lo2 ex c cur m Hk Hi Hp Hq Hcnt CUR Hcur INV SHZ MU WM.
    pose proof (u64arr_bound _ _ _ _ CUR) as Bd. rewrite Hcur in Bd.
    pose proof (bv_unsigned_in_range 64 q) as Rq. unfold bv_modulus in Rq.
    destruct INV as (Hv & Hag & Hc & Hlc).
    pose proof (Hag i ltac:(lia)) as Hnth.
    destruct (nth_error cur i) as [w|] eqn:Hn. 2:{ exfalso. apply nth_error_None in Hn. lia. }
    assert (Hw : w = nth i ws w0). { rewrite <- Hnth. symmetry. apply nth_error_nth. exact Hn. }
    pose proof (bv_unsigned_in_range 64 w) as Rw. unfold bv_modulus in Rw.
    step. (* [comment removed for export] *)
    if_not_taken.
    step. (* [comment removed for export] *) shr3. rewrite Hq.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    pose proof (u64arr_read BSEGS m A cur (Z.of_nat i) w p CUR ltac:(rewrite Nat2Z.id; exact Hn) ltac:(lia) ltac:(symmetry; apply wa_of_var; lia)) as RD.
    step. (* [comment removed for export] *)
    clear RD.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite ?(unsigned_lit y), ?(unsigned_lit c) by lia.
    pose proof (u64arr_store_ok BSEGS m A cur (Z.of_nat i) p CUR ltac:(lia) ltac:(symmetry; apply wa_of_var; lia)) as SOK.
    step. (* [comment removed for export] *)
    pose proof (u64arr_write BSEGS m A cur (Z.of_nat i) (Z_to_bv 64 (bv_unsigned w * y + c)) CUR ltac:(lia)) as CUR'.
    replace (A + 8 * Z.of_nat i)%Z with (bv_unsigned p + 0)%Z in CUR' by lia. rewrite Nat2Z.id in CUR'.
    store_done.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite ?(unsigned_lit y) by lia.
    rewrite ?(lm_smul_carry_word (bv_unsigned w) y c), ?(lm_smul_carry_word' (bv_unsigned w) y c) by lia.
    assert (INV' : smul_inv ws (upd cur i (Z_to_bv 64 (bv_unsigned w * y + c))) y (S i) (mul_cout (limbZ ws i) y c)).
    { replace (bv_unsigned w * y)%Z with (limbZ ws i * y)%Z by (unfold limbZ; rewrite <- Hw; reflexivity).
      apply smul_inv_step; [split; [exact Hv| split; [exact Hag| split; [exact Hc| exact Hlc]]] | lia | rewrite L62; lia |].
      unfold limbZ. rewrite <- Hw. apply lm_smul_lo_word; lia. }
    replace (bv_unsigned w) with (limbZ ws i) by (unfold limbZ; rewrite <- Hw; reflexivity).
    step. (* [comment removed for export] *)
    if_cases Hb.
    - cond_cleanup Hb.
      eapply (IH (S i) (Z_to_bv 64 (bv_unsigned p + 8)) (Z_to_bv 64 (bv_unsigned q + 8)) (Z_to_bv 64 (bv_unsigned cnt + -1)));
        try eassumption; try lia.
      + rewrite unsigned_lit by lia. lia.
      + rewrite unsigned_lit by lia. lia.
      + rewrite unsigned_lit by lia. lia.
      + rewrite upd_length. exact Hcur.
    - cond_cleanup Hb.
      assert (Hil : S i = Z.to_nat len) by lia.
      apply evt_done. unfold smulM_post.
      exists (mul_cout (limbZ ws i) y c). do 5 eexists. exists m1, (upd cur i (Z_to_bv 64 (limbZ ws i * y + c))).
      split. { f_equal. replace (bv_unsigned p + 8)%Z with (A + 8 * len)%Z by lia. reflexivity. }
      split; [exact MU|]. split; [exact WM|].
      split. { replace (limbZ ws i) with (bv_unsigned w) by (unfold limbZ; rewrite <- Hw; reflexivity). exact CUR'. }
      split; [rewrite upd_length; exact Hcur|].
      rewrite <- Hil. replace (limbZ ws i * y)%Z with (bv_unsigned w * y)%Z by (unfold limbZ; rewrite <- Hw; reflexivity). exact INV'.
  Qed.

  #[using="L62 LEN Hy KA"] Lemma smulM_loop : forall k, smulM_ok k.
  Proof. LiaFast.lf_pins (fun (L62 LEN Hy KA : LiaFast.U) => LiaFast.u0). induction k as [|k IH]. - unfold smulM_ok; intros; exfalso; lia. - apply smulM_body; exact IH. Qed.

  (* [comment removed for export] *)
  #[using="L62 LEN Hy KA KA'"] Lemma smulM_run : forall (p q cnt lo lo2 ex : word) (cur : list word),
    bv_unsigned p = A -> bv_unsigned q = A -> bv_unsigned cnt = 63%Z ->
    u64arr BSEGS m0 A cur -> length cur = 62%nat -> (forall j, nth j cur w0 = nth j ws w0) ->
    shz BSEGS m0 (ASAN_B + A / 8) 63 ->
    evt BSEGS (smulM_post m0)
      (MS (mkR x1 x2 x3 x4 x5 x6 (Z_to_bv 64 0) x8 x9 x10 q x12 x13 x14 (Z_to_bv 64 y) (Z_to_bv 64 len) (Z_to_bv 64 63) ex (Z_to_bv 64 ASAN_B) x20 x21 x22 x23 x24 x25 x26 x27 cnt p lo lo2)
          F (Z_to_bv 64 0x96fe0) fc None m0 (seg_rom BSEGS)).
  Proof. LiaFast.lf_pins (fun (L62 LEN Hy KA KA' : LiaFast.U) => LiaFast.u0).
    pose proof KA' as KAtop.  (* [comment removed for export] *)
    intros p q cnt lo lo2 ex cur Hp Hq Hcnt CUR Hcur Hag SHZ.
    eapply (smulM_loop (Z.to_nat len) 0%nat); try eassumption; try lia.
    - split; [cbn; lia|]. split; [intros; apply Hag|]. split; [lia|]. rewrite Hcur, L62. reflexivity.
    - apply munch_refl.
    - apply wmono_refl.
  Qed.
End smulM.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section smulF.
  Variables (x1 x2 x3 x4 x8 x9 x10 x11 x13 x18 x20 x21 x22 x23 x24 x25 x26 x27 x30 x31 : word).
  Variables (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte).
  Variables (A y : Z) (ws : list word) (len : Z).
  Hypothesis L62 : length ws = 62%nat.
  Hypothesis LEN : (0 < len <= 62)%Z.
  Hypothesis Hy : (0 <= y < 2 ^ 64)%Z.
  Hypothesis KA : (app2r A (A + 504)).
  Hypothesis KA' : (A + 504 <= KTOP)%Z.

  Definition smulF_post (m : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists (c' : Z) (q' cnt' lo' lo2' ex' : word) (m' : word -> option byte) (cur : list word),
      ms' = MS (mkR x1 x2 x3 x4 (Z_to_bv 64 (A + 8 * len)) cnt' lo' x8 x9 x10 x11 q' x13 (Z_to_bv 64 len) (Z_to_bv 64 c') (Z_to_bv 64 y) (Z_to_bv 64 63) x18 (Z_to_bv 64 ASAN_B) x20 x21 x22 x23 x24 x25 x26 x27 lo2' ex' x30 x31)
               F (Z_to_bv 64 0x97114) fc None m' (seg_rom BSEGS)
      /\ munch [(A, A + 8 * len)]%Z m m'
      /\ wmono BSEGS m m'
      /\ u64arr BSEGS m' A cur
      /\ length cur = 62%nat
      /\ smul_inv ws cur y (Z.to_nat len) c'.

  Definition smulF_ok (k : nat) : Prop :=
    forall (i : nat) (p q cnt lo lo2 ex : word) (c : Z) (cur : list word) (m : word -> option byte),
      (Z.to_nat len - i = k)%nat -> (i < Z.to_nat len)%nat ->
      bv_unsigned p = (A + 8 * Z.of_nat i)%Z ->
      bv_unsigned q = (A + 8 * Z.of_nat i)%Z ->
      bv_unsigned cnt = (63 - Z.of_nat i)%Z ->
      u64arr BSEGS m A cur -> length cur = 62%nat ->
      smul_inv ws cur y i c ->
      shz BSEGS m (ASAN_B + A / 8) 63 ->
      munch [(A, A + 8 * len)]%Z m0 m -> wmono BSEGS m0 m ->
      evt BSEGS (smulF_post m0)
        (MS (mkR x1 x2 x3 x4 p cnt lo x8 x9 x10 x11 q x13 (Z_to_bv 64 len) (Z_to_bv 64 c) (Z_to_bv 64 y) (Z_to_bv 64 63) x18 (Z_to_bv 64 ASAN_B) x20 x21 x22 x23 x24 x25 x26 x27 lo2 ex x30 x31)
            F (Z_to_bv 64 0x970d0) fc None m (seg_rom BSEGS)).

  #[using="L62 LEN Hy KA"] Lemma smulF_body : forall k, smulF_ok k -> smulF_ok (S k).
  Proof. LiaFast.lf_pins (fun (L62 LEN Hy KA : LiaFast.U) => LiaFast.u0).
    intros k IH. unfold smulF_ok. intros i p q cnt lo lo2 ex c cur m Hk Hi Hp Hq Hcnt CUR Hcur INV SHZ MU WM.
    pose proof (u64arr_bound _ _ _ _ CUR) as Bd. rewrite Hcur in Bd.
    pose proof (bv_unsigned_in_range 64 q) as Rq. unfold bv_modulus in Rq.
    destruct INV as (Hv & Hag & Hc & Hlc).
    pose proof (Hag i ltac:(lia)) as Hnth.
    destruct (nth_error cur i) as [w|] eqn:Hn. 2:{ exfalso. apply nth_error_None in Hn. lia. }
    assert (Hw : w = nth i ws w0). { rewrite <- Hnth. symmetry. apply nth_error_nth. exact Hn. }
    pose proof (bv_unsigned_in_range 64 w) as Rw. unfold bv_modulus in Rw.
    step. (* [comment removed for export] *)
    if_not_taken.
    step. (* [comment removed for export] *) shr3. rewrite Hq.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    pose proof (u64arr_read BSEGS m A cur (Z.of_nat i) w p CUR ltac:(rewrite Nat2Z.id; exact Hn) ltac:(lia) ltac:(symmetry; apply wa_of_var; lia)) as RD.
    step. (* [comment removed for export] *)
    clear RD.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite ?(unsigned_lit y), ?(unsigned_lit c) by lia.
    pose proof (u64arr_store_ok BSEGS m A cur (Z.of_nat i) p CUR ltac:(lia) ltac:(symmetry; apply wa_of_var; lia)) as SOK.
    step. (* [comment removed for export] *)
    pose proof (u64arr_write BSEGS m A cur (Z.of_nat i) (Z_to_bv 64 (bv_unsigned w * y + c)) CUR ltac:(lia)) as CUR'.
    replace (A + 8 * Z.of_nat i)%Z with (bv_unsigned p + 0)%Z in CUR' by lia. rewrite Nat2Z.id in CUR'.
    store_done.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite ?(unsigned_lit y) by lia.
    rewrite ?(lm_smul_carry_word (bv_unsigned w) y c), ?(lm_smul_carry_word' (bv_unsigned w) y c) by lia.
    assert (INV' : smul_inv ws (upd cur i (Z_to_bv 64 (bv_unsigned w * y + c))) y (S i) (mul_cout (limbZ ws i) y c)).
    { replace (bv_unsigned w * y)%Z with (limbZ ws i * y)%Z by (unfold limbZ; rewrite <- Hw; reflexivity).
      apply smul_inv_step; [split; [exact Hv| split; [exact Hag| split; [exact Hc| exact Hlc]]] | lia | rewrite L62; lia |].
      unfold limbZ. rewrite <- Hw. apply lm_smul_lo_word; lia. }
    replace (bv_unsigned w) with (limbZ ws i) by (unfold limbZ; rewrite <- Hw; reflexivity).
    step. (* [comment removed for export] *)
    if_cases Hb.
    - cond_cleanup Hb.
      eapply (IH (S i) (Z_to_bv 64 (bv_unsigned p + 8)) (Z_to_bv 64 (bv_unsigned q + 8)) (Z_to_bv 64 (bv_unsigned cnt + -1)));
        try eassumption; try lia.
      + rewrite unsigned_lit by lia. lia.
      + rewrite unsigned_lit by lia. lia.
      + rewrite unsigned_lit by lia. lia.
      + rewrite upd_length. exact Hcur.
    - cond_cleanup Hb.
      assert (Hil : S i = Z.to_nat len) by lia.
      apply evt_done. unfold smulF_post.
      exists (mul_cout (limbZ ws i) y c). do 5 eexists. exists m1, (upd cur i (Z_to_bv 64 (limbZ ws i * y + c))).
      split. { f_equal. replace (bv_unsigned p + 8)%Z with (A + 8 * len)%Z by lia. reflexivity. }
      split; [exact MU|]. split; [exact WM|].
      split. { replace (limbZ ws i) with (bv_unsigned w) by (unfold limbZ; rewrite <- Hw; reflexivity). exact CUR'. }
      split; [rewrite upd_length; exact Hcur|].
      rewrite <- Hil. replace (limbZ ws i * y)%Z with (bv_unsigned w * y)%Z by (unfold limbZ; rewrite <- Hw; reflexivity). exact INV'.
  Qed.

  #[using="L62 LEN Hy KA"] Lemma smulF_loop : forall k, smulF_ok k.
  Proof. LiaFast.lf_pins (fun (L62 LEN Hy KA : LiaFast.U) => LiaFast.u0). induction k as [|k IH]. - unfold smulF_ok; intros; exfalso; lia. - apply smulF_body; exact IH. Qed.

  (* [comment removed for export] *)
  #[using="L62 LEN Hy KA KA'"] Lemma smulF_run : forall (p q cnt lo lo2 ex : word) (cur : list word),
    bv_unsigned p = A -> bv_unsigned q = A -> bv_unsigned cnt = 63%Z ->
    u64arr BSEGS m0 A cur -> length cur = 62%nat -> (forall j, nth j cur w0 = nth j ws w0) ->
    shz BSEGS m0 (ASAN_B + A / 8) 63 ->
    evt BSEGS (smulF_post m0)
      (MS (mkR x1 x2 x3 x4 p cnt lo x8 x9 x10 x11 q x13 (Z_to_bv 64 len) (Z_to_bv 64 0) (Z_to_bv 64 y) (Z_to_bv 64 63) x18 (Z_to_bv 64 ASAN_B) x20 x21 x22 x23 x24 x25 x26 x27 lo2 ex x30 x31)
          F (Z_to_bv 64 0x970d0) fc None m0 (seg_rom BSEGS)).
  Proof. LiaFast.lf_pins (fun (L62 LEN Hy KA KA' : LiaFast.U) => LiaFast.u0).
    pose proof KA' as KAtop.  (* [comment removed for export] *)
    intros p q cnt lo lo2 ex cur Hp Hq Hcnt CUR Hcur Hag SHZ.
    eapply (smulF_loop (Z.to_nat len) 0%nat); try eassumption; try lia.
    - split; [cbn; lia|]. split; [intros; apply Hag|]. split; [lia|]. rewrite Hcur, L62. reflexivity.
    - apply munch_refl.
    - apply wmono_refl.
  Qed.
End smulF.


End B_pow5_A.

Module B_pow5_B.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Step.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Tac OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Step.ZBridge.
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Shadow.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Bigint_defs Bigint_shl.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFA Require Import A_cap.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_rt_stmt B_rt_lemmas B_long_mul_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_pow5_stmt.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_rt_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_rt_lemmas OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_long_mul_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_pow10.B_large_mul_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_pow5_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_pow10.B_pow5_A.
Local Ltac lia ::= lia_tc.  (* [comment removed for export] *)
Local Ltac step ::=
  app2_lin_all;
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) => step_core segs R F pc fc rv m ro; try decide_lit_if
  | |- evt _ _ (MS _ _ ?pc _ _ _ _) => fail "pc is not a literal:" pc
  end.  (* [comment removed for export] *)
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac simpl_arr_sizes ::= tryif kp_sas_pre5 then (rewrite ?u32s_length, ?u64s_length, ?upd_length, ?zeros_length, ?repeat_length in *) else idtac.      (* [comment removed for export] *)

Ltac name_mem X := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into X end.

Ltac solve_W_ok_rt := solve_W_rt.  (* [comment removed for export] *)
Lemma stk_sub5 : forall m lo hi lo' hi',
  stk BSEGS m lo hi -> (lo <= lo')%Z -> (hi' <= hi)%Z -> (lo' <= hi')%Z -> stk BSEGS m lo' hi'.
Proof.
  intros m lo hi lo' hi' ST H1 H2 H3.
  destruct (stk_split BSEGS m lo lo' hi ST ltac:(lia)) as [_ ST1].
  destruct (stk_split BSEGS m lo' hi' hi ST1 ltac:(lia)) as [ST2 _]. exact ST2.
Qed.
Ltac ulit := repeat (rewrite unsigned_lit by lia).
Ltac zlia := ulit; first [lia | Z.div_mod_to_equations; lia].
Ltac side5 :=
  lazymatch goal with
  | |- evt _ _ _ => idtac
  | |- RT _ _ => first [eassumption | eapply RT_transport; [eassumption | eassumption | solve_W_ok_rt]]
  | |- fk5_inv _ _ _ => eassumption
  | |- rt_disj _ _ _ => ulit; match goal with H : rt_disj _ _ _ |- _ => eapply rt_disj_sub; [exact H | lia | lia] end
  | |- shz _ _ _ _ => ulit; first [eassumption | match goal with H : shz _ _ _ _ |- _ => eapply shz_sub; [exact H | zlia | zlia | zlia] end]
  | |- stk _ _ _ _ => ulit; first [eassumption | match goal with H : stk _ _ _ _ |- _ => eapply stk_sub5; [exact H | lia | lia | lia] end]
  | |- @eq word _ _ => first [eassumption | reflexivity | ulit; reflexivity]
  | |- _ => first [eassumption | reflexivity | zlia]
  end.

Section Loops.
  Hypothesis large_mul_spec : large_mul_stmt.
  Variables (sp va gp tp x21 x22 x23 x24 x25 x26 x27 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (ws : list word) (len e0 : Z) (v : rt_vals).
  Notation A := (bv_unsigned va).
  Notation SP' := (bv_unsigned sp + -48)%Z.
  Notation X := (bval ws (Z.to_nat len)).
  Notation FS := (rt_FS v).
  Notation BB := (Z_to_bv 64 ASAN_B).
  Hypothesis L62 : length ws = 62%nat.
  Hypothesis Hlen : (0 <= len <= 62)%Z.
  Hypothesis A8 : (A mod 8 = 0)%Z.
  Hypothesis AL : (bv_unsigned sp mod 16 = 0)%Z.
  Hypothesis SEP : (A + 498 <= bv_unsigned sp - 2592 \/ bv_unsigned sp <= A)%Z.
  Hypothesis SPLO : (IMG_END <= bv_unsigned sp - 2592)%Z.
  Hypothesis Rsp : (0 <= bv_unsigned sp < 2 ^ 64)%Z.
  Hypothesis HA : (0 <= A /\ A + 498 <= 2 ^ 64)%Z.
  Hypothesis He0 : (0 <= e0 < 2 ^ 31)%Z.
  Hypothesis CAPL : (len + pow5_growth e0 <= LM_T)%Z.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis TP : tp = Z_to_bv 64 TPV.
  Hypothesis KSP : (KHI <= bv_unsigned sp - 2592)%Z.
  Hypothesis KSP2 : (bv_unsigned sp <= KTOP)%Z.
  Hypothesis KA0 : (app2r (A) (A + 504))%Z.
  Hypothesis KA1 : (A + 504 <= KTOP)%Z.
  Hypothesis SFS : (FS + FSSIZE <= bv_unsigned sp - 2592)%Z.
  Hypothesis RTX0 : RTX v fc.
  Hypothesis SEPF : (FS + 4231168 <= A /\ A + 632 <= FS + FK5_LO)%Z.
  Hypothesis RD1 : rt_disj v (bv_unsigned sp - 2592) (bv_unsigned sp).
  Hypothesis RD2 : rt_disj v A (A + 498).
  Hypothesis RD3 : rt_disj v FS (FS + FSSIZE).
  Hypotheses (KF1 : (app2r (FS) (FS + FSSIZE))%Z) (KF2 : (FS + FSSIZE <= KTOP)%Z) (KF8 : (FS mod 4096 = 0)%Z).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition big_W : list ivl :=
    [(bv_unsigned sp - 2592, SP'); (A, A + 498);
     (FS + FK5_HINT, FS + FK5_HINT + 8); (FS + FK5_FLAGS, FS + FK5_FLAGS + FK5_NFLAGS);
     (FS + FK5_LO, FS + FK5_HI); (ASAN_B + FS / 8 + FK5_SLO, ASAN_B + FS / 8 + FK5_SHI)]%Z.

  Definition big_post (m0 : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists (e' : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word)
                      (m' : word -> option byte) (wsk : list word) (lenk : Z) (h5 : word),
      ms' = MS (mkR x1 (Z_to_bv 64 SP') gp tp x5 x6 x7 va (Z_to_bv 64 e') x10 x11 x12 x13 x14 x15 x16 x17
                   (Z_to_bv 64 B_LARGE_POW5) BB (Z_to_bv 64 134) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
               F (Z_to_bv 64 0x96f8c) fc None m' (seg_rom BSEGS)
      /\ munch big_W m0 m'
      /\ wmono BSEGS m0 m'
      /\ u64arr BSEGS m' A wsk /\ length wsk = 62%nat
      /\ rw_cells BSEGS m' (A + 496) [C2 (Z_to_bv 64 lenk)] /\ (0 <= lenk <= 62)%Z
      /\ bnorm wsk (Z.to_nat lenk)
      /\ (0 <= e' < 135)%Z /\ (e' <= e0)%Z
      /\ (lenk + pow5_growth e' <= len + pow5_growth e0)%Z
      /\ stk BSEGS m' (bv_unsigned sp - 2592) SP'
      /\ pristine m' IMG_LO ROD_HI /\ pristine m' RELRO_LO RELRO_HI /\ pristine m' REALTAB_LO REALTAB_HI
      /\ RT m' v /\ fk5_inv m' FS h5
      /\ shz BSEGS m' (ASAN_B + A / 8) 63 /\ shz BSEGS m' POW5TAB_SH POW5TAB_SHN
      /\ rdbl BSEGS m' (ASAN_B + A / 8 - 8) 79 /\ rdbl BSEGS m' (ASAN_B + FS / 8 + FK_SH_LO) FK_SH_N
      /\ shz BSEGS m' (ASAN_B + (bv_unsigned sp - 2592) / 8) 324.

  Definition big_ok (n : nat) : Prop :=
    forall (m0 : word -> option byte) (e : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word)
           (m : word -> option byte) (wsk : list word) (lenk : Z) (h5 : word),
      (Z.to_nat e <= n)%nat -> (135 <= e <= e0)%Z ->
      u64arr BSEGS m A wsk -> length wsk = 62%nat ->
      rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 lenk)] -> (0 <= lenk <= 62)%Z ->
      bnorm wsk (Z.to_nat lenk) ->
      (lenk + pow5_growth e <= len + pow5_growth e0)%Z ->
      stk BSEGS m (bv_unsigned sp - 2592) SP' ->
      pristine m IMG_LO ROD_HI -> pristine m RELRO_LO RELRO_HI -> pristine m REALTAB_LO REALTAB_HI ->
      RT m v -> fk5_inv m FS h5 ->
      shz BSEGS m (ASAN_B + A / 8) 63 -> shz BSEGS m POW5TAB_SH POW5TAB_SHN ->
      rdbl BSEGS m (ASAN_B + A / 8 - 8) 79 -> rdbl BSEGS m (ASAN_B + FS / 8 + FK_SH_LO) FK_SH_N ->
      shz BSEGS m (ASAN_B + (bv_unsigned sp - 2592) / 8) 324 ->
      munch big_W m0 m -> wmono BSEGS m0 m ->
      evt BSEGS (big_post m0)
        (MS (mkR x1 (Z_to_bv 64 SP') gp tp x5 x6 x7 va (Z_to_bv 64 e) x10 x11 x12 x13 x14 x15 x16 x17
                 (Z_to_bv 64 B_LARGE_POW5) BB (Z_to_bv 64 134) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x96f70) fc None m (seg_rom BSEGS)).

  #[using="large_mul_spec ws L62 A8 AL SEP SPLO Rsp HA He0 CAPL TP KSP KSP2 KA0 SFS RTX0 SEPF RD1 RD3 KF1 KF8"] Lemma big_body : forall n, big_ok n -> big_ok (S n).
  Proof. LiaFast.lf_pins (fun (large_mul_spec ws L62 A8 AL SEP SPLO Rsp HA He0 CAPL TP KSP KSP2 KA0 SFS RTX0 SEPF RD1 RD3 KF1 KF8 : LiaFast.U) => LiaFast.u0).
    intros n IH. unfold big_ok.
    intros m0 e x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m wsk lenk h5 Hn He XA Lx LENC Hlenk BN VAL ST PR PRG PRT RTH FK SHX SHT RBX RBF SHW MU WM.
    cbv delta [big_W] in MU.
    pose proof (bval_nonneg ws (Z.to_nat len)) as X0.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    pose proof (unsigned_lit SP' ltac:(lia)) as ULs.
    step. (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      eapply evt_cut; [ eapply large_mul_spec with (v := v) (h5 := h5) (ws := wsk) (len := lenk) | post_call BSEGS mc ] end.
    all: try side5.
    1:{ pose proof (pow5_growth_135 e ltac:(lia)). pose proof (pow5_growth_nonneg (e - 135)%Z ltac:(lia)). lia. }
    rewrite ?ULs in *.
    step. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    rewrite swrap32_small by lia.
    step. (* [comment removed for export] *)
    if_cases Hmore.
    - cond_cleanup Hmore.
      replace (SP' - 2544)%Z with (bv_unsigned sp - 2592)%Z in * by lia.
      eapply (IH m0 (e + -135)%Z); try eassumption; try lia.
      all: lazymatch goal with
           | |- (_ + pow5_growth _ <= _)%Z => pose proof (pow5_growth_135 e ltac:(lia)); replace (e + -135)%Z with (e - 135)%Z by lia; lia
           | |- munch _ _ _ => cbv delta [big_W]; assumption
           | |- stk _ _ _ _ => assumption
           end.
    - cond_cleanup Hmore.
      apply evt_done. unfold big_post.
      exists (e + -135)%Z. do 16 eexists. eexists _, _, _, _.
      split; [reflexivity|].
      split. { cbv delta [big_W]. assumption. } split. { assumption. }
      split. { eassumption. } split. { assumption. } split. { eassumption. } split. { lia. }
      split. { assumption. } split. { lia. } split. { lia. }
      split. { pose proof (pow5_growth_135 e ltac:(lia)). replace (e + -135)%Z with (e - 135)%Z by lia. lia. }
      split. { replace (SP' - 2544)%Z with (bv_unsigned sp - 2592)%Z in * by lia. assumption. }
      repeat match goal with |- _ /\ _ => split end; eassumption.
  Qed.

  #[using="large_mul_spec ws L62 A8 AL SEP SPLO Rsp HA He0 CAPL TP KSP KSP2 KA0 SFS RTX0 SEPF RD1 RD3 KF1 KF8"] Lemma big_loop : forall n, big_ok n.
  Proof. LiaFast.lf_pins (fun (large_mul_spec ws L62 A8 AL SEP SPLO Rsp HA He0 CAPL TP KSP KSP2 KA0 SFS RTX0 SEPF RD1 RD3 KF1 KF8 : LiaFast.U) => LiaFast.u0). induction n as [|n IHn]. - unfold big_ok; intros; exfalso; lia. - apply big_body; exact IHn. Qed.

  #[using="large_mul_spec ws L62 A8 AL SEP SPLO Rsp HA He0 CAPL TP KSP KSP2 KA0 SFS RTX0 SEPF RD1 RD3 KF1 KF8"] Lemma big_run : forall (e : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word)
           (m : word -> option byte) (wsk : list word) (lenk : Z) (h5 : word),
      (135 <= e <= e0)%Z ->
      u64arr BSEGS m A wsk -> length wsk = 62%nat ->
      rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 lenk)] -> (0 <= lenk <= 62)%Z ->
      bnorm wsk (Z.to_nat lenk) ->
      (lenk + pow5_growth e <= len + pow5_growth e0)%Z ->
      stk BSEGS m (bv_unsigned sp - 2592) SP' ->
      pristine m IMG_LO ROD_HI -> pristine m RELRO_LO RELRO_HI -> pristine m REALTAB_LO REALTAB_HI ->
      RT m v -> fk5_inv m FS h5 ->
      shz BSEGS m (ASAN_B + A / 8) 63 -> shz BSEGS m POW5TAB_SH POW5TAB_SHN ->
      rdbl BSEGS m (ASAN_B + A / 8 - 8) 79 -> rdbl BSEGS m (ASAN_B + FS / 8 + FK_SH_LO) FK_SH_N ->
      shz BSEGS m (ASAN_B + (bv_unsigned sp - 2592) / 8) 324 ->
      evt BSEGS (big_post m)
        (MS (mkR x1 (Z_to_bv 64 SP') gp tp x5 x6 x7 va (Z_to_bv 64 e) x10 x11 x12 x13 x14 x15 x16 x17
                 (Z_to_bv 64 B_LARGE_POW5) BB (Z_to_bv 64 134) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x96f70) fc None m (seg_rom BSEGS)).
  Proof. LiaFast.lf_pins (fun (large_mul_spec ws L62 A8 AL SEP SPLO Rsp HA He0 CAPL TP KSP KSP2 KA0 SFS RTX0 SEPF RD1 RD3 KF1 KF8 : LiaFast.U) => LiaFast.u0).
    intros. eapply (big_loop (Z.to_nat e) m e); try eassumption; try lia.
    - cbv delta [big_W]. apply munch_refl. - apply wmono_refl.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Notation LENP := (Z_to_bv 64 (A + 496)).
  Notation SHL := (Z_to_bv 64 ((A + 496) / 8 + ASAN_B)).

  Definition mid_post (x1 x6 x13 x20 : word) (m0 : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists (e' : Z) (x7 x11 x18 x28 x29 x30 x31 : word)
                      (m' : word -> option byte) (wsk : list word) (lenk : Z),
      ms' = MS (mkR x1 (Z_to_bv 64 SP') gp tp (Z_to_bv 64 61) x6 x7 va (Z_to_bv 64 e') LENP x11 SHL x13 (Z_to_bv 64 26) (Z_to_bv 64 POW5_27) (Z_to_bv 64 lenk) (Z_to_bv 64 63)
                   x18 BB x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
               F (Z_to_bv 64 0x97070) fc None m' (seg_rom BSEGS)
      /\ munch [(A, A + 498)]%Z m0 m'
      /\ wmono BSEGS m0 m'
      /\ u64arr BSEGS m' A wsk /\ length wsk = 62%nat
      /\ rw_cells BSEGS m' (A + 496) [C2 (Z_to_bv 64 lenk)] /\ (0 <= lenk <= 62)%Z
      /\ bnorm wsk (Z.to_nat lenk)
      /\ (0 <= e' < 27)%Z /\ (e' <= e0)%Z
      /\ (lenk + pow5_growth e' <= len + pow5_growth e0)%Z.

  Definition mid_ok (x1 x6 x13 x20 : word) (m0 : word -> option byte) (n : nat) : Prop :=
    forall (e : Z) (x7 x11 x18 x28 x29 x30 x31 : word) (m : word -> option byte) (wsk : list word) (lenk : Z),
      (Z.to_nat e <= n)%nat -> (27 <= e <= e0)%Z -> (e < 135)%Z ->
      bv_unsigned x13 = (2 ^ 64 - 1 - A)%Z ->
      u64arr BSEGS m A wsk -> length wsk = 62%nat ->
      rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 lenk)] -> (0 <= lenk <= 62)%Z ->
      bnorm wsk (Z.to_nat lenk) ->
      (lenk + pow5_growth e <= len + pow5_growth e0)%Z ->
      shz BSEGS m (ASAN_B + A / 8) 63 ->
      munch [(A, A + 498)]%Z m0 m -> wmono BSEGS m0 m ->
      evt BSEGS (mid_post x1 x6 x13 x20 m0)
        (MS (mkR x1 (Z_to_bv 64 SP') gp tp (Z_to_bv 64 61) x6 x7 va (Z_to_bv 64 e) LENP x11 SHL x13 (Z_to_bv 64 26) (Z_to_bv 64 POW5_27) (Z_to_bv 64 lenk) (Z_to_bv 64 63)
                 x18 BB x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x96fcc) fc None m (seg_rom BSEGS)).

  #[using="ws v L62 A8 AL SPLO Rsp HA CAPL KSP KSP2 KA0 KA1 SFS SEPF KF1 KF8"] Lemma mid_body : forall x1 x6 x13 x20 m0 n,
    mid_ok x1 x6 x13 x20 m0 n -> mid_ok x1 x6 x13 x20 m0 (S n).
  Proof. LiaFast.lf_pins (fun (ws v L62 A8 AL SPLO Rsp HA CAPL KSP KSP2 KA0 KA1 SFS SEPF KF1 KF8 : LiaFast.U) => LiaFast.u0).
    intros x1 x6 x13 x20 m0 n IH. unfold mid_ok.
    intros e x7 x11 x18 x28 x29 x30 x31 m wsk lenk Hn He He135 H13 XA Lx LENC Hlenk BN VAL SHX MU WM.
    pose proof (bval_nonneg ws (Z.to_nat len)) as X0.
    pose proof (rw_cells_bound _ _ _ _ LENC) as Bc. cbn [cells_size csize Nat.add] in Bc.
    assert (P27 : (0 < 5 ^ 27)%Z) by (apply Z.pow_pos_nonneg; lia).
    assert (G27 : (pow5_growth e = 1 + pow5_growth (e - 27))%Z) by (apply pow5_growth_27; lia).
    pose proof (pow5_growth_nonneg (e - 27)%Z ltac:(lia)) as G0.
    assert (LEN60 : (lenk <= 60)%Z) by lia.
    step. (* [comment removed for export] *)
    if_cases Hl0.
    - (* [comment removed for export] *)
      cond_cleanup Hl0.
      zstep. (* [comment removed for export] *)
      rewrite swrap32_small by lia.
      step. (* [comment removed for export] *)
      if_cases Hmore.
      + cond_cleanup Hmore.
        eapply (IH (e + -27)%Z); try eassumption; try lia.
        all: try (replace (e + -27)%Z with (e - 27)%Z by lia; lia).
      + cond_cleanup Hmore.
        step. (* [comment removed for export] *)
        apply evt_done. unfold mid_post. exists (e + -27)%Z. do 7 eexists. eexists _, wsk, lenk.
        split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact XA|]. split; [exact Lx|].
        split; [exact LENC|]. split; [lia|]. split; [exact BN|]. split; [lia|]. split; [lia|].
        replace (e + -27)%Z with (e - 27)%Z by lia; lia.
    - cond_cleanup Hl0.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      name_mem mc.
      call (@smulM_run _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
               F fc mc A POW5_27 wsk lenk Lx ltac:(lia) ltac:(unfold POW5_27; lia) KA0 KA1).
      all: try lia.
      all: try (rewrite unsigned_lit by lia; lia).
      1:{ exact XA. } 1:{ exact Lx. } 1:{ intros j; reflexivity. } 1:{ exact SHX. }
      match goal with H : smul_inv _ _ _ _ ?c |- _ => rename H into INV; rename c into c' end.
      match goal with H : u64arr BSEGS _ A ?cu |- _ => rename H into CUR; rename cu into cur end.
      pose proof INV as (Hv & Hag & Hc' & Hlc).
      assert (CAPy : (POW5_27 * bval wsk (Z.to_nat lenk) < BIG_CAP)%Z).
      { apply cap_of_len; [unfold POW5_27; lia | rewrite Z2Nat.id by lia; lia]. }
      step. (* [comment removed for export] *)
      if_cases Hcz.
      + (* [comment removed for export] *)
        cond_cleanup Hcz.
        zstep. (* [comment removed for export] *)
        rewrite swrap32_small by lia.
        assert (VAL' : (lenk + pow5_growth (e + -27) <= len + pow5_growth e0)%Z).
        { replace (e + -27)%Z with (e - 27)%Z by lia. lia. }
        assert (BN' : bnorm cur (Z.to_nat lenk)).
        { apply bnorm_of_value; [lia|].
          pose proof (bnorm_lower wsk (Z.to_nat lenk) BN ltac:(lia)) as LO.
          rewrite (smul_inv_finish_nocarry wsk cur POW5_27 (Z.to_nat lenk)) by (rewrite <- Hcz; exact INV).
          unfold POW5_27. nia. }
        step. (* [comment removed for export] *)
        if_cases Hmore.
        * cond_cleanup Hmore.
          eapply (IH (e + -27)%Z); try eassumption; try lia.
        all: try (replace (e + -27)%Z with (e - 27)%Z by lia; lia).
        * cond_cleanup Hmore.
          step. (* [comment removed for export] *)
          apply evt_done. unfold mid_post. exists (e + -27)%Z. do 7 eexists. eexists _, cur, lenk.
          split; [reflexivity|]. split; [assumption|]. split; [assumption|]. split; [exact CUR|]. split; [assumption|].
          split; [eassumption|]. split; [lia|]. split; [exact BN'|]. split; [lia|]. split; [lia|].
          exact VAL'.
      + (* [comment removed for export] *)
        cond_cleanup Hcz.
        pose proof (smul_carry_room wsk _ _ _ _ INV ltac:(lia) CAPy) as ROOM.
        step. (* [comment removed for export] *)
        if_not_taken.
        zstep. (* [comment removed for export] *)
        rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3)%Z with 8%Z.
        step. (* [comment removed for export] *)
        if_cases Ht; [ cond_cleanup Ht; rewrite ?unsigned_lit in Ht by lia; exfalso; lia | clear Ht ].
        zstep. (* [comment removed for export] *)
        replace (A + lenk * 8)%Z with (A + 8 * lenk)%Z by lia.
        step. (* [comment removed for export] *) shr3.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
          pose proof (u64arr_store_ok BSEGS m1 _ _ lenk (Z_to_bv 64 (A + 8 * lenk)) CUR ltac:(rewrite Hlc, Lx; lia) eq_refl) as SOK end.
        step. (* [comment removed for export] *)
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m1 _ _) _) =>
          pose proof (u64arr_write BSEGS m1 _ _ lenk (Z_to_bv 64 c') CUR ltac:(rewrite Hlc, Lx; lia)) as CUR2 end.
        store_done.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        zstep. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        zstep. (* [comment removed for export] *)
        rewrite swrap32_small by lia.
        assert (VAL' : (lenk + 1 + pow5_growth (e + -27) <= len + pow5_growth e0)%Z).
        { replace (e + -27)%Z with (e - 27)%Z by lia. lia. }
        assert (BN' : bnorm (upd cur (Z.to_nat lenk) (Z_to_bv 64 c')) (Z.to_nat (lenk + 1))).
        { replace (Z.to_nat (lenk + 1)) with (S (Z.to_nat lenk)) by lia. apply bnorm_push; [rewrite Hlc, Lx; lia|].
          rewrite unsigned_lit by lia. lia. }
        step. (* [comment removed for export] *)
        if_cases Hmore.
        * cond_cleanup Hmore.
          eapply (IH (e + -27)%Z); try eassumption; try lia.
        all: try (replace (e + -27)%Z with (e - 27)%Z by lia; lia).
          all: first [rewrite upd_length, Hlc; exact Lx | exact VAL'].
        * cond_cleanup Hmore.
          step. (* [comment removed for export] *)
          apply evt_done. unfold mid_post. exists (e + -27)%Z. do 7 eexists. eexists _, _, (lenk + 1)%Z.
          split; [reflexivity|]. split; [assumption|]. split; [assumption|]. split; [exact CUR2|].
          split; [rewrite upd_length, Hlc; exact Lx|].
          split; [eassumption|]. split; [lia|]. split; [exact BN'|]. split; [lia|]. split; [lia|].
          exact VAL'.
  Qed.

  #[using="ws v L62 A8 AL SPLO Rsp HA CAPL KSP KSP2 KA0 KA1 SFS SEPF KF1 KF8"] Lemma mid_loop : forall x1 x6 x13 x20 m0 n, mid_ok x1 x6 x13 x20 m0 n.
  Proof. LiaFast.lf_pins (fun (ws v L62 A8 AL SPLO Rsp HA CAPL KSP KSP2 KA0 KA1 SFS SEPF KF1 KF8 : LiaFast.U) => LiaFast.u0). intros. induction n as [|n IHn]. - unfold mid_ok; intros; exfalso; lia. - apply mid_body; exact IHn. Qed.

  #[using="ws v L62 A8 AL SPLO Rsp HA CAPL KSP KSP2 KA0 KA1 SFS SEPF KF1 KF8"] Lemma mid_run : forall (x1 x6 x13 x20 : word) (e : Z) (x7 x11 x18 x28 x29 x30 x31 : word)
           (m : word -> option byte) (wsk : list word) (lenk : Z),
      (27 <= e <= e0)%Z -> (e < 135)%Z ->
      bv_unsigned x13 = (2 ^ 64 - 1 - A)%Z ->
      u64arr BSEGS m A wsk -> length wsk = 62%nat ->
      rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 lenk)] -> (0 <= lenk <= 62)%Z ->
      bnorm wsk (Z.to_nat lenk) ->
      (lenk + pow5_growth e <= len + pow5_growth e0)%Z ->
      shz BSEGS m (ASAN_B + A / 8) 63 ->
      evt BSEGS (mid_post x1 x6 x13 x20 m)
        (MS (mkR x1 (Z_to_bv 64 SP') gp tp (Z_to_bv 64 61) x6 x7 va (Z_to_bv 64 e) LENP x11 SHL x13 (Z_to_bv 64 26) (Z_to_bv 64 POW5_27) (Z_to_bv 64 lenk) (Z_to_bv 64 63)
                 x18 BB x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x96fcc) fc None m (seg_rom BSEGS)).
  Proof. LiaFast.lf_pins (fun (ws v L62 A8 AL SPLO Rsp HA CAPL KSP KSP2 KA0 KA1 SFS SEPF KF1 KF8 : LiaFast.U) => LiaFast.u0).
    intros. eapply (mid_loop x1 x6 x13 x20 m (Z.to_nat e) e); try eassumption; try lia.
    - apply munch_refl. - apply wmono_refl.
  Qed.
End Loops.
End B_pow5_B.

Module B_pow5.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Step.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Tac OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Step.ZBridge.
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Shadow.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Bigint_defs Bigint_shl.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFA Require Import A_cap.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_rt_stmt B_rt_lemmas B_long_mul_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_pow5_stmt.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_rt_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_rt_lemmas OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_long_mul_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_pow10.B_large_mul_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_pow5_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_pow10.B_pow5_A OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_pow10.B_pow5_B.
Local Ltac lia ::= lia_tc.  (* [comment removed for export] *)
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac step ::=
  app2_lin_all;
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) => step_core segs R F pc fc rv m ro; try decide_lit_if
  | |- evt _ _ (MS _ _ ?pc _ _ _ _) => fail "pc is not a literal:" pc
  end.  (* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac simpl_arr_sizes ::= tryif kp_sas_pre5 then (rewrite ?u32s_length, ?u64s_length, ?upd_length, ?zeros_length, ?repeat_length in *) else idtac.      (* [comment removed for export] *)

Lemma B_SP5_tbl : table_b BSEGS B_SMALL_POW5 8 (fun v => le8 (Z_to_bv 64 v)) SMALL_POW5 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma SMALL_POW5_length : length SMALL_POW5 = 28%nat.
Proof. reflexivity. Qed.

Ltac open_fk5 H :=
  let a := fresh "FK1" in let b := fresh "FK2" in let c := fresh "FK3" in let d := fresh "FK4" in let e := fresh "FK5" in
  destruct H as (a & b & c & d & e); unfold fs_cells_ok in a.
Ltac close_fk5 := unfold fk5_inv, fs_cells_ok; repeat match goal with |- _ /\ _ => split end; eassumption.

Ltac solve_W_top := solve_W_rt.  (* [comment removed for export] *)

Section Main.
  Hypothesis large_mul_spec : large_mul_stmt.

  Section Fixed.
  Variables (ra sp gp tp a0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
            (ws : list word) (len e0 : Z) (v : rt_vals).
  Notation A := (bv_unsigned a0).
  Notation SP' := (bv_unsigned sp + -48)%Z.
  Notation X := (bval ws (Z.to_nat len)).
  Notation FS := (rt_FS v).
  Notation BB := (Z_to_bv 64 ASAN_B).
  Notation LENP := (Z_to_bv 64 (A + 496)).
  Notation SHL := (Z_to_bv 64 ((A + 496) / 8 + ASAN_B)).
  Notation SHA := (Z_to_bv 64 (ASAN_B + A / 8)).
  Notation POST := (pow5_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A e0 ws len v m).
  Notation W := (pow5_W (bv_unsigned sp) A FS).
  Notation FRAME mm := (rw_cells BSEGS mm SP' [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  Hypothesis L62 : length ws = 62%nat.
  Hypothesis Hlen : (0 <= len <= 62)%Z.
  Hypothesis A8 : (A mod 8 = 0)%Z.
  Hypothesis AL : (bv_unsigned sp mod 16 = 0)%Z.
  Hypothesis SEP : (A + 498 <= bv_unsigned sp - 2592 \/ bv_unsigned sp <= A)%Z.
  Hypothesis SPLO : (IMG_END <= bv_unsigned sp - 2592)%Z.
  Hypothesis Rsp : (0 <= bv_unsigned sp < 2 ^ 64)%Z.
  Hypothesis HA : (0 <= A /\ A + 498 <= 2 ^ 64)%Z.
  Hypothesis He0 : (0 <= e0 < 2 ^ 31)%Z.
  Hypothesis CAPL : (len + pow5_growth e0 <= LM_T)%Z.   (* [comment removed for export] *)
  Hypothesis KSP : (KHI <= bv_unsigned sp - 2592)%Z.
  Hypothesis KSP2 : (bv_unsigned sp <= KTOP)%Z.
  Hypothesis KA0 : (app2r (A) (A + 504))%Z.
  Hypothesis KA1 : (A + 504 <= KTOP)%Z.
  Hypothesis RTH : RT m v.
  Hypothesis SFS : (FS + FSSIZE <= bv_unsigned sp - 2592)%Z.
  Hypothesis RTX0 : RTX v fc.
  Hypothesis SEPF : (FS + 4231168 <= A /\ A + 632 <= FS + FK5_LO)%Z.
  Hypothesis RD1 : rt_disj v (bv_unsigned sp - 2592) (bv_unsigned sp).
  Hypothesis RD2 : rt_disj v A (A + 498).
  Hypothesis RD3 : rt_disj v FS (FS + FSSIZE).
  Hypotheses (Kc1 : rt_app (rt_ctx v) 160) (Kc2 : (rt_ctx v + 160 <= KTOP)%Z) (Kt1 : rt_app (rt_thr v) 80)
             (Kt2 : (rt_thr v + 80 <= KTOP)%Z) (Kb1 : rt_app (rt_blk v) 32) (Kb2 : (rt_blk v + 32 <= KTOP)%Z)
             (KF1 : (app2r (FS) (FS + 11571200))%Z) (KF2 : (FS + 11571200 <= KTOP)%Z) (KF8 : (FS mod 4096 = 0)%Z).

  Ltac solve_W := solve_W_rt.  (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[using="L62 SPLO HA KSP2 KA0 RTH SFS SEPF RD1 RD3 Kc1 Kt1 Kb1 KF1"] Lemma exit_11996c : forall (x1 x5 x6 x7 x8 x9 x10 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 : word)
      (m' : word -> option byte) (wsf : list word) (lenf : Z) (h5 : word),
      u64arr BSEGS m' A wsf -> length wsf = 62%nat ->
      rw_cells BSEGS m' (A + 496) [C2 (Z_to_bv 64 lenf)] -> (0 <= lenf <= 62)%Z ->
      bnorm wsf (Z.to_nat lenf) ->
      (lenf <= len + pow5_growth e0)%Z ->
      FRAME m' ->
      stk BSEGS m' (bv_unsigned sp - 2592) SP' ->
      pristine m' IMG_LO ROD_HI ->
      fk5_inv m' FS h5 ->
      munch W m m' -> wmono BSEGS m m' ->
      evt BSEGS POST
        (MS (mkR x1 (Z_to_bv 64 SP') gp tp x5 x6 x7 x8 x9 x10 (Z_to_bv 64 1) x12 x13 x14 x15 x16 x17
                 x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x9715c) fc None m' (seg_rom BSEGS)).
  Proof. LiaFast.lf_pins (fun (L62 SPLO HA KSP2 KA0 RTH SFS SEPF RD1 RD3 Kc1 Kt1 Kb1 KF1 : LiaFast.U) => LiaFast.u0).
    intros * XA Lx LENC Hl BN VAL FR ST PR FK MU WM.
    cbv delta [pow5_W] in MU.
    step. (* [comment removed for export] *)
    do 8 step.
    release_frame FR ST (bv_unsigned sp).
    unfold pow5_post. finish. all: try eassumption. all: try lia.
    eapply RT_transport; [exact RTH | exact MU | solve_W].
  Qed.

  (* [comment removed for export] *)
  #[using="L62 A8 AL SEP SPLO HA CAPL KSP KSP2 KA0 KA1 RTH SFS SEPF RD1 RD3 Kc1 Kt1 Kb1 KF1 KF8"] Lemma from_119880 : forall (e2 : Z) (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x20 x28 x29 x30 x31 : word)
      (m1 : word -> option byte) (wsk : list word) (lenk : Z) (h5 : word),
      (0 <= e2 < 27)%Z -> (e2 <= e0)%Z ->
      u64arr BSEGS m1 A wsk -> length wsk = 62%nat ->
      rw_cells BSEGS m1 (A + 496) [C2 (Z_to_bv 64 lenk)] -> (0 <= lenk <= 62)%Z ->
      bnorm wsk (Z.to_nat lenk) ->
      (lenk + pow5_growth e2 <= len + pow5_growth e0)%Z ->
      FRAME m1 ->
      stk BSEGS m1 (bv_unsigned sp - 2592) SP' ->
      pristine m1 IMG_LO ROD_HI ->
      shz BSEGS m1 (ASAN_B + A / 8) 63 -> shz BSEGS m1 POW5TAB_SH POW5TAB_SHN ->
      fk5_inv m1 FS h5 ->
      munch W m m1 -> wmono BSEGS m m1 ->
      evt BSEGS POST
        (MS (mkR x1 (Z_to_bv 64 SP') gp tp x5 x6 x7 a0 (Z_to_bv 64 e2) LENP x11 x12 x13 x14 x15 x16 x17
                 x18 BB x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x97070) fc None m1 (seg_rom BSEGS)).
  Proof. LiaFast.lf_pins (fun (L62 A8 AL SEP SPLO HA CAPL KSP KSP2 KA0 KA1 RTH SFS SEPF RD1 RD3 Kc1 Kt1 Kb1 KF1 KF8 : LiaFast.U) => LiaFast.u0).
    intros * He2 He2' XA Lx LENC Hl BN VAL FR ST PR SHX SHT FK MU WM.
    cbv delta [pow5_W] in MU.
    pose proof (bval_nonneg ws (Z.to_nat len)) as X0.
    pose proof (rw_cells_bound _ _ _ _ LENC) as Bc. cbn [cells_size csize Nat.add] in Bc.
    open_fk5 FK.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hz.
    - cond_cleanup Hz.
      eapply exit_11996c; try eassumption; try lia.
      all: first [pose proof (pow5_growth_nonneg e2 ltac:(lia)); lia | close_fk5 | cbv delta [pow5_W]; exact MU].
    - cond_cleanup Hz.
      zstep. (* [comment removed for export] *)
      rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3)%Z with 8%Z.
      step. step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Ht; [ cond_cleanup Ht; rewrite ?zb_lxor_ones in Ht by lia; rewrite ?unsigned_lit in Ht by lia; exfalso; lia | clear Ht ].
      zstep. (* [comment removed for export] *)
      replace (152456 + e2 * 8)%Z with (152456 + 8 * e2)%Z by lia.
      step. (* [comment removed for export] *) shr3.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *) shr3.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
        pose proof (table_read BSEGS (fun v => le8 (Z_to_bv 64 v)) SMALL_POW5 B_SMALL_POW5 8 mc IMG_LO ROD_HI
                      B_SP5_tbl PR ltac:(lia) ltac:(rewrite SMALL_POW5_length; cbn; lia) e2
                      ltac:(rewrite SMALL_POW5_length; cbn; lia)) as RD end.
      change (Z.of_nat 8) with 8%Z in RD. rewrite (SMALL_POW5_nth (Z.to_nat e2)) in RD by lia. rewrite Z2Nat.id in RD by lia.
      step. (* [comment removed for export] *)
      clear RD.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      rewrite zx16_lit_small by lia.
      step. (* [comment removed for export] *)
      if_cases Hl0.
      + cond_cleanup Hl0.
        eapply exit_11996c; try eassumption; try lia.
        all: first [pose proof (pow5_growth_nonneg e2 ltac:(lia)); lia | close_fk5 | cbv delta [pow5_W]; exact MU].
      + cond_cleanup Hl0.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        assert (Py : (0 < 5 ^ e2 < 2 ^ 64)%Z).
        { split; [apply Z.pow_pos_nonneg; lia|]. apply (Z.le_lt_trans _ (5 ^ 27)); [apply Z.pow_le_mono_r; lia|]. cbn; lia. }
        assert (LEN60 : (lenk <= 60)%Z) by (pose proof (pow5_growth_small e2 ltac:(lia)); lia).
        name_mem mc.
        call (@smulF_run _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                 F fc mc A (5 ^ e2) wsk lenk Lx ltac:(lia) ltac:(lia) KA0 KA1).
        all: try lia.
        all: try (rewrite unsigned_lit by lia; lia).
        1:{ exact XA. } 1:{ exact Lx. } 1:{ intros j; reflexivity. } 1:{ exact SHX. }
        match goal with H : smul_inv _ _ _ _ ?c |- _ => rename H into INV; rename c into c' end.
        match goal with H : u64arr BSEGS _ A ?cu |- _ => rename H into CUR; rename cu into cur end.
        pose proof INV as (Hv & Hag & Hc' & Hlc).
        assert (CAPy : (5 ^ e2 * bval wsk (Z.to_nat lenk) < BIG_CAP)%Z) by (apply cap_of_len; [lia | rewrite Z2Nat.id by lia; lia]).
        step. (* [comment removed for export] *)
        if_cases Hcz.
        * (* [comment removed for export] *)
          cond_cleanup Hcz.
          eapply exit_11996c; try eassumption; try lia.
          all: first [ cbv delta [pow5_W]; assumption
                     | close_fk5
                     | apply bnorm_of_value; [lia|];
                       pose proof (bnorm_lower wsk (Z.to_nat lenk) BN ltac:(lia)) as LO;
                       rewrite (smul_inv_finish_nocarry wsk cur (5 ^ e2) (Z.to_nat lenk)) by (rewrite <- Hcz; exact INV); nia
                     | pose proof (pow5_growth_small e2 ltac:(lia)); lia ].
        * (* [comment removed for export] *)
          cond_cleanup Hcz.
          pose proof (smul_carry_room wsk _ _ _ _ INV ltac:(lia) CAPy) as ROOM.
          step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          if_not_taken.
          zstep. (* [comment removed for export] *)
          rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3)%Z with 8%Z.
          step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          if_cases Ht; [ cond_cleanup Ht; rewrite ?zb_lxor_ones in Ht by lia; rewrite ?unsigned_lit in Ht by lia; exfalso; lia | clear Ht ].
          zstep. (* [comment removed for export] *)
          replace (A + lenk * 8)%Z with (A + 8 * lenk)%Z by lia.
          step. (* [comment removed for export] *) shr3.
          step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
            pose proof (u64arr_store_ok BSEGS m1 _ _ lenk (Z_to_bv 64 (A + 8 * lenk)) CUR ltac:(rewrite Hlc, Lx; lia) eq_refl) as SOK end.
          step. (* [comment removed for export] *)
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m1 _ _) _) =>
            pose proof (u64arr_write BSEGS m1 _ _ lenk (Z_to_bv 64 c') CUR ltac:(rewrite Hlc, Lx; lia)) as CUR2 end.
          store_done.
          step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          zstep. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          eapply exit_11996c; try eassumption; try lia.
          all: first [ cbv delta [pow5_W]; assumption
                     | close_fk5
                     | rewrite upd_length, Hlc; exact Lx
                     | replace (Z.to_nat (lenk + 1)) with (S (Z.to_nat lenk)) by lia; apply bnorm_push; [rewrite Hlc, Lx; lia|]; rewrite unsigned_lit by lia; lia
                     | pose proof (pow5_growth_small e2 ltac:(lia)); lia ].
  Qed.

  (* [comment removed for export] *)
  #[using="L62 A8 AL SEP SPLO Rsp HA CAPL KSP KSP2 KA0 KA1 RTH SFS SEPF RD1 RD3 Kc1 Kt1 Kb1 KF1 KF8"] Lemma from_11979c : forall (e1 : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x28 x29 x30 x31 : word)
      (m1 : word -> option byte) (wsk : list word) (lenk : Z) (h5 : word),
      (0 <= e1 < 135)%Z -> (e1 <= e0)%Z ->
      u64arr BSEGS m1 A wsk -> length wsk = 62%nat ->
      rw_cells BSEGS m1 (A + 496) [C2 (Z_to_bv 64 lenk)] -> (0 <= lenk <= 62)%Z ->
      bnorm wsk (Z.to_nat lenk) ->
      (lenk + pow5_growth e1 <= len + pow5_growth e0)%Z ->
      FRAME m1 ->
      stk BSEGS m1 (bv_unsigned sp - 2592) SP' ->
      pristine m1 IMG_LO ROD_HI ->
      shz BSEGS m1 (ASAN_B + A / 8) 63 -> shz BSEGS m1 POW5TAB_SH POW5TAB_SHN ->
      fk5_inv m1 FS h5 ->
      munch W m m1 -> wmono BSEGS m m1 ->
      evt BSEGS POST
        (MS (mkR x1 (Z_to_bv 64 SP') gp tp x5 x6 x7 a0 (Z_to_bv 64 e1) x10 x11 x12 x13 x14 x15 x16 x17
                 x18 BB x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x96f8c) fc None m1 (seg_rom BSEGS)).
  Proof. LiaFast.lf_pins (fun (L62 A8 AL SEP SPLO Rsp HA CAPL KSP KSP2 KA0 KA1 RTH SFS SEPF RD1 RD3 Kc1 Kt1 Kb1 KF1 KF8 : LiaFast.U) => LiaFast.u0).
    intros * He1 He1' XA Lx LENC Hl BN VAL FR ST PR SHX SHT FK MU WM.
    cbv delta [pow5_W] in MU.
    pose proof (rw_cells_bound _ _ _ _ LENC) as Bc. cbn [cells_size csize Nat.add] in Bc.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases H27.
    - cond_cleanup H27.
      eapply from_119880; try eassumption; try lia. all: cbv delta [pow5_W]; exact MU.
    - cond_cleanup H27.
      open_fk5 FK.
      step. (* [comment removed for export] *) shr3.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      rewrite ?zb_lxor_ones by lia.
      step. (* [comment removed for export] *)
      rewrite zx16_lit_small by lia.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      change 7450580596923828125%Z with POW5_27.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      name_mem mc.
      eapply evt_cut; [ eapply mid_run with (ws:=ws) (len:=len) | post_call BSEGS mc ].
      all: try eassumption; try lia.
      all: try (rewrite unsigned_lit by lia; lia).
      eapply from_119880; try eassumption; try lia. all: first [close_fk5 | cbv delta [pow5_W]; assumption].
  Qed.
  End Fixed.

  #[using="large_mul_spec"] Lemma pow5_spec : pow5_stmt.
  Proof. LiaFast.lf_pins (fun (large_mul_spec : LiaFast.U) => LiaFast.u0).
    unfold pow5_stmt. intros until h5. cbv zeta.
    intros ST AL SPLO PR LIMBS L62 LENC Hlen A8 NORM He CAP SEP TP PRG PRT RTH FK KSP KSP2 KA0 KA1 SFS SEPF RD1 RD2 RD3 SHX SHT RBX RBF RTX0 SHW.
    pose proof (munch_refl (pow5_W (bv_unsigned sp) (bv_unsigned a0) (rt_FS v)) m) as MU.
    cbv delta [pow5_W] in MU.
    pose proof (wmono_refl BSEGS m) as WM.
    pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
    pose proof (bv_unsigned_in_range 64 a1) as Re. unfold bv_modulus in Re.
    pose proof (u64arr_bound _ _ _ _ LIMBS) as Bl. rewrite L62 in Bl.
    pose proof (rw_cells_bound _ _ _ _ LENC) as Bc. cbn [cells_size csize Nat.add] in Bc.
    assert (HA : (0 <= bv_unsigned a0 /\ bv_unsigned a0 + 498 <= 2 ^ 64)%Z) by lia.
    clear Bl Bc.
    pose proof RTH as RTH0. open_RT_keep RTH.
    destruct RTP as (Hbeg & Hblk & Hblk1 & Hctx & Hthr & HFS1 & HFS2 & HFS3 & Kc1 & Kc2 & Kt1 & Kt2 & Kb1 & Kb2).
    assert (BC : ro_cells BSEGS m 943736 [C8 (Z_to_bv 64 ASAN_B)]).
    { change [C8 (Z_to_bv 64 ASAN_B); C4 (Z_to_bv 64 1)] with ([C8 (Z_to_bv 64 ASAN_B)] ++ [C4 (Z_to_bv 64 1)]) in RT1.
      apply (proj1 (proj1 (ro_cells_app BSEGS m 943736 _ _) RT1)). }
    clear RT1 RT2 RT2b RT3 RT4 RT5 RT6 RT7 RT8 RT9 RT10 RT11 RT12 RT13 RT14 Hfb fb.
    open_fk5 FK.
    remember (bv_unsigned a1) as e0 eqn:Ee0.
    rewrite <- (Z_to_bv_bv_unsigned a1), <- Ee0.
    carve_frame 48%nat ST.
    do 7 step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases H135.
    - (* [comment removed for export] *)
      cond_cleanup H135.
      eapply from_11979c; try eassumption; try lia.
      all: first [rewrite Z.sub_diag, Z.pow_0_r; ring | close_fk5 | cbv delta [pow5_W]; exact MU].
    - cond_cleanup H135.
      step. step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      name_mem mc.
      eapply evt_cut; [ eapply (big_run large_mul_spec) with (ws:=ws) (len:=len) (v:=v) (h5:=h5) | post_call BSEGS mc ].
      all: try eassumption; try lia.
      all: try (rewrite Z.sub_diag, Z.pow_0_r; ring).
      all: try close_fk5.
      all: try (eapply RT_transport; [exact RTH0 | exact MU | solve_W_top]).
      eapply from_11979c; try eassumption; try lia. all: cbv delta [pow5_W]; assumption.
  Qed.
End Main.
End B_pow5.

Local Ltac lia ::= lia_tc.  (* [comment removed for export] *)
Local Ltac step ::=
  app2_lin_all;
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) => step_core segs R F pc fc rv m ro; try decide_lit_if
  | |- evt _ _ (MS _ _ ?pc _ _ _ _) => fail "pc is not a literal:" pc
  end.  (* [comment removed for export] *)
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac simpl_arr_sizes ::= tryif kp_sas_pre5 then (rewrite ?u32s_length, ?u64s_length, ?upd_length, ?zeros_length in *) else idtac.      (* [comment removed for export] *)

Ltac solve_W_ok_rt := solve_W_rt.  (* [comment removed for export] *)
Ltac open_fk5 H :=
  let a := fresh "FK1" in let b := fresh "FK2" in let c := fresh "FK3" in let d := fresh "FK4" in let e := fresh "FK5" in
  destruct H as (a & b & c & d & e); unfold fs_cells_ok in a.
Ltac close_fk5 := unfold fk5_inv, fs_cells_ok; repeat match goal with |- _ /\ _ => split end; eassumption.
Ltac name_mem X := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into X end.

Section Main.
  Hypothesis pow5_spec : pow5_stmt.
  Hypothesis shl_spec : shl_stmt.

  #[using="pow5_spec shl_spec"] Lemma pow10_spec : pow10_stmt.
  Proof. LiaFast.lf_pins (fun (pow5_spec shl_spec : LiaFast.U) => LiaFast.u0).
    unfold pow10_stmt. intros until h5. cbv zeta.
    intros ST AL SPLO PR LIMBS L62 LENC Hlen A8 NORM He CAP CAP2 SEP TP PRG PRT RTH FK KSP KSP2 KA0 KA1 SFS SEPF RD1 RD2 RD3 SHX SHT RBX RBF RTX0 SHW.
    pose proof (munch_refl (pow10_W (bv_unsigned sp) (bv_unsigned a0) (rt_FS v)) m) as MU.
    cbv delta [pow10_W] in MU.
    pose proof (wmono_refl BSEGS m) as WM.
    pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
    pose proof (bv_unsigned_in_range 64 a1) as Re. unfold bv_modulus in Re.
    pose proof (u64arr_bound _ _ _ _ LIMBS) as Bl. rewrite L62 in Bl.
    pose proof (rw_cells_bound _ _ _ _ LENC) as Bc. cbn [cells_size csize Nat.add] in Bc.
    assert (HA : (0 <= bv_unsigned a0 /\ bv_unsigned a0 + 498 <= 2 ^ 64)%Z) by lia.
    clear Bl Bc.
    open_RT_keep RTH.
    destruct RTP as (Hbeg & Hblk & Hblk1 & Hctx & Hthr & HFS1 & HFS2 & HFS3 & Hc1 & Hc2 & Ht1 & Ht2 & Hb1 & Hb2).
    clear RT1 RT2 RT2b RT3 RT4 RT5 RT6 RT7 RT8 RT9 RT10 RT11 RT12 RT13 RT14 Hfb fb.
    open_fk5 FK.
    pose proof (bval_nonneg ws (Z.to_nat len)) as X0.
    pose proof CAP as CAP5.
    carve_frame 32%nat ST.
    do 4 step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    pose proof (unsigned_lit (bv_unsigned sp + -32) ltac:(lia)) as ULs.
    step. (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      eapply evt_cut; [ eapply pow5_spec with (v := v) (h5 := h5) (ws := ws) (len := len) | post_call BSEGS mc ] end.
    1:{ rewrite ULs. replace (bv_unsigned sp + -32 - 2592)%Z with (bv_unsigned sp - 2624)%Z by lia. exact ST. }
    1:{ rewrite ULs. Z.div_mod_to_equations. lia. }
    1:{ rewrite ULs. lia. }
    1:{ exact PR. } 1:{ exact LIMBS. } 1:{ exact L62. } 1:{ exact LENC. } 1:{ exact Hlen. } 1:{ exact A8. } 1:{ exact NORM. }
    1:{ lia. } 1:{ exact CAP5. }
    1:{ rewrite ULs. lia. }
    1:{ exact TP. } 1:{ exact PRG. } 1:{ exact PRT. }
    1:{ eapply RT_transport; [exact RTH | exact MU | solve_W_ok_rt]. }
    1:{ close_fk5. }
    1:{ rewrite ULs. lia. } 1:{ rewrite ULs. lia. } 1:{ exact KA0. } 1:{ exact KA1. }
    1:{ rewrite ULs. lia. } 1:{ exact SEPF. }
    1:{ rewrite ULs. eapply rt_disj_sub; [exact RD1 | lia | lia]. }
    1:{ exact RD2. } 1:{ exact RD3. }
    1:{ exact SHX. } 1:{ exact SHT. } 1:{ exact RBX. } 1:{ exact RBF. } 1:{ exact RTX0. }
    1:{ rewrite ULs. eapply shz_sub; [exact SHW | Z.div_mod_to_equations; lia | lia | Z.div_mod_to_equations; lia]. }
    rewrite ?ULs in *.
    match goal with H : u64arr BSEGS _ (bv_unsigned a0) ?w |- _ => rename H into XA5; rename w into ws5 end.
    match goal with H : rw_cells BSEGS _ (bv_unsigned a0 + 496) [C2 (Z_to_bv 64 ?l)] |- _ => rename H into LENC5; rename l into len5 end.
    match goal with H : (len5 <= len + pow5_growth _)%Z |- _ => rename H into VAL5 end.
    match goal with H : bnorm ws5 _ |- _ => rename H into BN5 end.
    match goal with H : stk BSEGS _ (bv_unsigned sp + -32 - 2592) _ |- _ => rename H into ST5 end.
    match goal with H : RT _ v |- _ => rename H into RTH5 end.
    match goal with H : fk5_inv _ (rt_FS v) ?hh |- _ => rename H into FK5'; rename hh into h5b end.
    clear FK1 FK4 FK5. open_fk5 FK5'.
    step. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    rewrite ?shl32_shr32m, ?shl32_shr32 by lia.
    try rewrite (Z.mod_small (bv_unsigned a1) 4294967296) by lia. rewrite ?(Z_to_bv_bv_unsigned a1).
    step. (* [comment removed for export] *)
    do 4 step. (* [comment removed for export] *)
    replace (bv_unsigned sp + -32 - 2592)%Z with (bv_unsigned sp - 2624)%Z in ST5 by lia.
    release_frame FR ST5 (bv_unsigned sp).
    step. (* [comment removed for export] *)
    (* [comment removed for export] *)
    destruct (stk_split BSEGS _ _ (bv_unsigned sp - 2384) _ ST5 ltac:(lia)) as [STlo SThi].
    clear ST5.
    name_mem m5.
    pose proof (munch_refl [(bv_unsigned sp - 2624, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + 498)]%Z m5) as MU5.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      eapply evt_cut; [ eapply shl_spec with (v := v) (ws := ws5) (len := len5) | post_call BSEGS mc ] end.
    1:{ exact SThi. } 1:{ exact AL. } 1:{ exact XA5. } 1:{ assumption. } 1:{ exact LENC5. } 1:{ lia. } 1:{ exact A8. } 1:{ lia. }
    1:{ exact PRG. } 1:{ exact PRT. } 1:{ exact RTH5. }
    1:{ eapply rt_disj_sub; [exact RD1 | lia | lia]. }
    1:{ exact RD2. }
    1:{ lia. } 1:{ lia. } 1:{ exact KSP2. } 1:{ exact KA0. } 1:{ exact KA1. }
    1:{ exact SHX. } 1:{ exact RBX. }
    match goal with H : bnorm ws5 _ -> _ |- _ => rename H into COND end.
    destruct (COND BN5) as (Hb & VAL' & BN').
    { apply cap_of_len_pow2; [lia | rewrite Z2Nat.id by lia; lia]. }
    { lia. }
    subst.
    match goal with H : stk BSEGS _ (bv_unsigned sp - 2384) _ |- _ => rename H into SThi' end.
    pose proof (stk_merge BSEGS _ _ _ _ STlo SThi' ltac:(lia)) as STall.
    unfold pow10_post. finish.
    all: try eassumption. all: try lia.
    all: try (eapply RT_transport; [exact RTH5 | exact MU5 | solve_W_ok_rt]).
    all: try close_fk5.
  Qed.
End Main.
