(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA SysStep.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow IcptSpec.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout R_small R_m2s R_thread I_consts I_qck X_atexit F_memchr D_kit I_ikit I_memchrw I_strnlenw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
(* [comment removed for export] *)
Local Definition zal (k x r : Z) : Prop := (x mod k = r)%Z.
Local Lemma zal_ex : forall k x r : Z, (0 < k)%Z -> (x mod k = r)%Z -> exists q, x = (k * q + r)%Z.
Proof. intros k x r Hk H. exists (x / k)%Z. rewrite <- H. apply Z.div_mod. lia. Qed.
Local Ltac zlit x := lazymatch x with Zpos _ => idtac | Z0 => idtac | Zneg _ => idtac end.
Local Ltac zget_mod t :=
  lazymatch type of t with
  | (?x mod ?k = ?r)%Z => let H' := fresh "Hzm" in pose proof t as H'
  | ?A /\ ?B => first [ zget_mod constr:(proj1 t) | zget_mod constr:(proj2 t) ]
  end.
Local Ltac zhide :=
  repeat match goal with
  | H : context [(?x mod ?k)%Z] |- _ => zlit x; zlit k; let v := eval cbv in (x mod k)%Z in change (x mod k)%Z with v in H
  end;
  repeat match goal with
  | H : (?x mod ?k = ?r)%Z |- _ =>
      let q := fresh "zq" in let Hq := fresh "Hzq" in
      destruct (zal_ex k x r (eq_refl : (0 < k)%Z) H) as [q Hq]; change (zal k x r) in H
  | H : context [(?x mod ?k = ?r)%Z] |- _ =>
      lazymatch type of H with (_ mod _ = _)%Z => fail | _ => idtac end;
      (try zget_mod H); change (x mod k = r)%Z with (zal k x r) in H
  end;
  repeat match goal with
  | H : context [(2 ^ ?k)%Z] |- _ => let T := type of H in zify_arith_prop T;
      let v := eval cbv in (2 ^ k)%Z in lazymatch v with Zpos _ => change (2 ^ k)%Z with v in H end
  end.
(* [comment removed for export] *)
Local Definition zidle (P : Prop) : Prop := P.
Local Ltac zidle1 H := let T := type of H in change (zidle T) in H.
Local Ltac zidle_nsp H A sp := lazymatch A with context [bv_unsigned sp] => fail | _ => zidle1 H end.
Local Ltac zidle_begin sp n MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
    pose proof (munch_refl [(bv_unsigned sp - n, bv_unsigned sp)]%Z m) as MUz; pose proof (wmono_refl segs m) as WMz;
    repeat match goal with
    | H : rw_cells segs m ?A _ |- _ => zidle_nsp H A sp
    | H : ro_cells segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u8arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u32arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u64arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : bytes_at segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u8ro segs m ?A _ |- _ => zidle_nsp H A sp
    end
  end.
Local Ltac zidle_end MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch type of MUz with munch _ ?m _ =>
      try unfold zidle in *; transport_after_call segs m mm MUz WMz; clear MUz WMz end end.
(* [comment removed for export] *)
Local Ltac zidle_end_m m :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with MU : munch _ m mm, WM : wmono _ m mm |- _ =>
      unfold zidle in *; transport_after_call asegs m mm MU WM end end.
(* [comment removed for export] *)
Local Ltac zidle_nspz H A SP := lazymatch A with context [SP] => fail | _ => zidle1 H end.
Local Ltac zidle_beginz SP n MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
    pose proof (munch_refl [(SP - n, SP)]%Z m) as MUz; pose proof (wmono_refl segs m) as WMz;
    repeat match goal with
    | H : rw_cells segs m ?A _ |- _ => zidle_nspz H A SP
    | H : ro_cells segs m ?A _ |- _ => zidle_nspz H A SP
    | H : u8arr segs m ?A _ |- _ => zidle_nspz H A SP
    | H : u32arr segs m ?A _ |- _ => zidle_nspz H A SP
    | H : u64arr segs m ?A _ |- _ => zidle_nspz H A SP
    | H : bytes_at segs m ?A _ |- _ => zidle_nspz H A SP
    | H : u8ro segs m ?A _ |- _ => zidle_nspz H A SP
    end
  end.
Ltac showpc := match goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc end.





Section WithRIP.
Hypothesis RIP : rip_stmt.

Definition istrnlen_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (r : Z) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - ISTRNLEN_IDEPTH, bv_unsigned sp)] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp).

Theorem istrnlen_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (s n : Z) (buf : list byte) (lo : Z),
  a0 = Z_to_bv 64 s -> a1 = Z_to_bv 64 n ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - ISTRNLEN_IDEPTH -> kHighShadowEnd + 8 <= lo -> bv_unsigned sp < 2^63 ->
  0 < s <= 2^47 -> 0 <= n < 2^40 -> s + strnlen_chk n buf <= 2^47 ->
  bytes_at asegs m s buf -> strnlen_ok s n buf -> (s + Z.of_nat (length buf) <= lo \/ bv_unsigned sp <= s) ->
  chk_ok m s (strnlen_chk n buf) -> m2s_cells m -> icells_sn m -> mem_inv asegs m ->
  evt asegs (istrnlen_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (strnlen_res n buf) lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1ac8fc) fc None m (seg_rom asegs)).
Proof using RIP.
  intros until lo. intros -> -> ST LO LOLO SPH S0 N0 SH BUF OK SEPS CS M2S IC MI.
  unfold strnlen_ok, strnlen_chk, kHighShadowEnd in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  pose proof (munch_refl [(usp - 4384, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof IC as (G70 & G2 & RM & RS & SHC & AI & ISL).
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  assert (EUs : bv_unsigned (Z_to_bv 64 s) = s) by (apply unsigned_lit; lia).
  assert (EUn : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  assert (EU2144 : bv_unsigned (Z_to_bv 64 (usp + -2144)) = usp + -2144) by (apply unsigned_lit; lia).
  assert (LEN : 0 <= memchr_chk 0 n buf <= n /\ memchr_chk 0 n buf = Z.min (strnlen_res n buf + 1) n).
  { unfold memchr_chk, strnlen_res. destruct (find_byte 0 (firstn (Z.to_nat n) buf)) as [i|] eqn:FB.
    - destruct (find_byte_Some _ _ _ FB) as (Hi & _). rewrite length_firstn in Hi. lia.
    - lia. }
  carve_frame 64%nat ST. rename FR into FRs. carve_frame 2080%nat ST.
  zidle_beginz usp 2144%Z MUz1 WMz1.
  zhide.
  do 14 lstep.
  zidle_end MUz1 WMz1.
  call try_init_spec; [exact AI| rewrite EU2144; exact ST| lia| lia| assumption|].
  lazymatch goal with H : stk asegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EU2144 in H; rename H into ST2 end.
  do 6 lstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (CS1 : chk_ok mm s (memchr_chk 0 n buf))
      by (apply (chk_ok_agree m mm s _ CS ltac:(lia) ltac:(lia));
          apply (agree_of_munch _ _ _ _ MU); intros y Hy; cbn [outside]; split; [lia| exact I]);
    assert (M2S1 : m2s_cells mm) by (destruct M2S as (M1 & M2 & M3); split; [| split];
      [ apply (rw_cells_agree asegs m mm _ _ M1); [| exact WM]; apply (agree_of_munch _ _ _ _ MU); intros y Hy; cbn in Hy |- *; lia
      | apply (rw_cells_agree asegs m mm _ _ M2); [| exact WM]; apply (agree_of_munch _ _ _ _ MU); intros y Hy; cbn in Hy |- *; lia
      | apply (rw_cells_agree asegs m mm _ _ M3); [| exact WM]; apply (agree_of_munch _ _ _ _ MU); intros y Hy; cbn in Hy |- *; lia ]);
    assert (IC1 : icells_mc mm) by (split; [exact G2| split; [exact RM| split; [exact SHC| exact AI]]])
  end.
  call (musl_strnlen_spec RIP); [reflexivity| reflexivity| rewrite EU2144; exact ST2| rewrite EU2144; lia| unfold kHighShadowEnd; lia
        | rewrite EU2144; lia| lia| lia| exact SH| exact BUF| exact OK| rewrite EU2144; lia
        | exact CS1| exact M2S1| exact IC1| assumption|].
  lazymatch goal with H : stk asegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EU2144 in H; rename H into ST3 end.
  clear CS1 M2S1 IC1.
  assert (RR : 0 <= strnlen_res n buf <= n).
  { unfold strnlen_res. destruct (find_byte 0 (firstn (Z.to_nat n) buf)) as [i|] eqn:FB.
    - destruct (find_byte_Some _ _ _ FB) as (Hi & _). rewrite length_firstn in Hi. lia.
    - lia. }
  set (r := strnlen_res n buf) in *.
  assert (EUr : bv_unsigned (Z_to_bv 64 r) = r) by (apply unsigned_lit; lia).
  assert (EUr1 : bv_unsigned (Z_to_bv 64 (r + 1)) = r + 1) by (apply unsigned_lit; lia).
  assert (EUns : bv_unsigned (Z_to_bv 64 (18446744073709551615 - s)) = 18446744073709551615 - s) by (apply unsigned_lit; lia).
  lstep. if_false. do 3 lstep. lstep. if_false.
  lstep. lstep. if_cases K; zify_cond K.
  - (* [comment removed for export] *)
    do 4 lstep. lstep. rewrite (lxor_ones64 s) by lia. if_true.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (CS2 : chk_ok mm s n)
        by (replace n with (memchr_chk 0 n buf) by (destruct LEN as (_ & E); rewrite E; lia);
            apply (chk_ok_agree m mm s _ CS ltac:(lia) ltac:(lia));
            apply (agree_of_munch _ _ _ _ MU); intros y Hy; cbn [outside]; split; [lia| exact I]);
      assert (M2S2 : m2s_cells mm) by (destruct M2S as (M1 & M2 & M3); split; [| split];
        [ apply (rw_cells_agree asegs m mm _ _ M1); [| exact WM]; apply (agree_of_munch _ _ _ _ MU); intros y Hy; cbn in Hy |- *; lia
        | apply (rw_cells_agree asegs m mm _ _ M2); [| exact WM]; apply (agree_of_munch _ _ _ _ MU); intros y Hy; cbn in Hy |- *; lia
        | apply (rw_cells_agree asegs m mm _ _ M3); [| exact WM]; apply (agree_of_munch _ _ _ _ MU); intros y Hy; cbn in Hy |- *; lia ]);
      assert (IC2 : icells_sn mm) by (split; [exact G70| split; [exact G2| split; [exact RM| split; [exact RS| split; [exact SHC| split; [exact AI| exact ISL]]]]]])
    end.
    call (istrnlen_chk RIP usp s n); [exact ST3| lia| unfold kHighShadowEnd; lia| lia| lia| lia| lia
          | exact CS2| exact M2S2| exact IC2| assumption|].
    lazymatch goal with H : stk asegs _ lo (usp + -2144) |- _ => rename H into ST4 end.
    do 10 lstep.
    release_frame FR ST4 (usp + -64). release_frame FRs ST4 usp.
    lstep.
    unfold istrnlen_post. sys_finish.
    + rewrite EU. eapply munch_weaken; [| exact MU]. unfold sub_fp; cbn [outside]; intros; lia.
    + rewrite EU. assumption.
  - (* [comment removed for export] *)
    do 3 lstep. lstep. rewrite (lxor_ones64 s) by lia. if_false.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (CS2 : chk_ok mm s (r + 1))
        by (replace (r + 1) with (memchr_chk 0 n buf) by (destruct LEN as (_ & E); rewrite E; lia);
            apply (chk_ok_agree m mm s _ CS ltac:(lia) ltac:(lia));
            apply (agree_of_munch _ _ _ _ MU); intros y Hy; cbn [outside]; split; [lia| exact I]);
      assert (M2S2 : m2s_cells mm) by (destruct M2S as (M1 & M2 & M3); split; [| split];
        [ apply (rw_cells_agree asegs m mm _ _ M1); [| exact WM]; apply (agree_of_munch _ _ _ _ MU); intros y Hy; cbn in Hy |- *; lia
        | apply (rw_cells_agree asegs m mm _ _ M2); [| exact WM]; apply (agree_of_munch _ _ _ _ MU); intros y Hy; cbn in Hy |- *; lia
        | apply (rw_cells_agree asegs m mm _ _ M3); [| exact WM]; apply (agree_of_munch _ _ _ _ MU); intros y Hy; cbn in Hy |- *; lia ]);
      assert (IC2 : icells_sn mm) by (split; [exact G70| split; [exact G2| split; [exact RM| split; [exact RS| split; [exact SHC| split; [exact AI| exact ISL]]]]]])
    end.
    call (istrnlen_chk RIP usp s (r + 1)); [exact ST3| lia| unfold kHighShadowEnd; lia| lia| lia| lia| lia
          | exact CS2| exact M2S2| exact IC2| assumption|].
    lazymatch goal with H : stk asegs _ lo (usp + -2144) |- _ => rename H into ST4 end.
    do 10 lstep.
    release_frame FR ST4 (usp + -64). release_frame FRs ST4 usp.
    lstep.
    unfold istrnlen_post. sys_finish.
    + rewrite EU. eapply munch_weaken; [| exact MU]. unfold sub_fp; cbn [outside]; intros; lia.
    + rewrite EU. assumption.
Qed.

End WithRIP.
