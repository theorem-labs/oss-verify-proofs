(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac ImageA Nodes RzCPS NodesA SysStep.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim Canon Stdio Prog.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout R_small R_m2s R_thread I_consts I_qck RT_iface I_readw2 I_memcpyw F_memcpy F_fwritex D_kit FX_Layout FX_Stdio_iface Imp_xifaceA X_ixdefs X_ixdefs2 RT_trans.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac Startup_glue Pj_loc_kit.
From OssFuzzTheorems.simdjson.fuzz_implementations.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

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

Local Ltac zidle_end_m m :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with MU : munch _ m mm, WM : wmono _ m mm |- _ =>
      unfold zidle in *; transport_after_call bsegs m mm MU WM end end.

Ltac if_lit :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => let v := eval vm_compute in c in change c with v; cbv iota
  end.

Lemma qc_word_zero : forall (m : mem) a n p, acc bsegs m a n -> a <= 64 * (p / 64) -> 64 * (p / 64) + 64 <= a + n -> 0 <= p ->
  ro_cells bsegs m (8 * ((p / 8 + 2147450880) / 8)) [C8 (Z_to_bv 64 0)].
Proof.
  intros m a n p AC H1 H2 P0.
  assert (E : 8 * ((p / 8 + 2147450880) / 8) = shad (64 * (p / 64))) by (unfold shad, SHB; Z.div_mod_to_equations; lia).
  rewrite E. apply (acc_word_zero m (64 * (p / 64))); [Z.div_mod_to_equations; lia|].
  apply (acc_sub bsegs m a n _ 64 AC); lia.
Qed.

Section Walk.

Variables (sp0 : Z).

Theorem iwcrtomb_ok : iwcrtomb_stmt (ixit2 sp0) (sp0 - STACK_WIN).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m D PS lo j
         -> -> -> DC DLO DHI PSC PS0 PSH ST LOD GLO XL SPH [IXm XCm] MI.
  pose proof XCm as ((SPW & SPT) & RF & (G2 & G1 & RM & SHC & RI) & GM & AB & AS).
  pose proof IXm as (AI & _ & _ & _ & _ & _ & RWC & GMB & MBS & _).
  unfold g_asan_inited, g_REAL_wcrtomb, e_musl_wcrtomb, g_GOT_mbstate_t_sz, g_mbstate_t_sz, g_GOT_REAL_memcpy, IOSBLK, IOSBLK_LEN,
    ICPT_DEPTH, STACK_WIN, GLOBALS_TOP, USTACK_TOP in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  pose proof (bv_unsigned_in_range 64 sp) as USR. unfold bv_modulus in USR. change (bv_unsigned sp) with usp in USR.
  pose proof (stk_top_le m lo usp ST ltac:(lia) MI) as UT.
  pose proof (rw_cells_top_le m D _ DC MI ltac:(cbn; lia)) as DT. cbn [cells_size csize Nat.add length] in DT.
  assert (LO0 : 0x7fff7f800000 <= lo) by lia.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(lo, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  assert (EUD : bv_unsigned (Z_to_bv 64 D) = D) by (apply unsigned_lit; lia).
  assert (EUP : bv_unsigned (Z_to_bv 64 PS) = PS) by (apply unsigned_lit; lia).
  unfold F_IWCRTOMB.

  carve_frame 72%nat ST. rename FR into FRt.
  carve_frame 2104%nat ST. rename FR into FRb.
  zhide.
  do 15 step.

  step. step. step.
  carve_frame 16%nat ST. rename FR into FRa.
  step. change (Z_to_le_bytes 8 486224) with (le8 (Z_to_bv 64 486224)). mem_after_store.
  step.
  do 6 step. if_false.
  do 4 step.
  release_frame FRa ST (usp + -2176).

  step. if_false.
  step. step.
  step. if_cases K0; zify_cond K0. { exfalso. clear - K0 PS0. rewrite ?unsigned_lit in K0 by lia. lia. }
  step. step. step.
  step. step. if_cases K1; zify_cond K1. { exfalso. clear - K1 PS0 PSH. rewrite lxor_ones64 in K1 by lia. rewrite ?unsigned_lit in K1 by lia. lia. }
  step. step. step. match goal with |- ?g => idtac "GOALA" g end. if_lit.

  do 11 step.
  rewrite !EUP. change (8 mod 2 ^ 32) with 8. replace (PS + 8 + -1) with (PS + 7) by lia. rewrite (unsigned_lit (PS + 7)) by lia.
  assert (E1 : Z.land (bv_unsigned (Z_to_bv 64 (2147450880 + PS ≫ 3))) 18446744073709551608 = 8 * ((PS / 8 + 2147450880) / 8)).
  { rewrite unsigned_lit_wrap, Z.shiftr_div_pow2 by lia. change (2^3) with 8. rewrite Z.mod_small by (Z.div_mod_to_equations; lia).
    rewrite land_m8' by (Z.div_mod_to_equations; lia). f_equal. f_equal. lia. }
  assert (E2 : Z.land (bv_unsigned (Z_to_bv 64 (2147450880 + (PS + 7) ≫ 3))) 18446744073709551608 = 8 * (((PS + 7) / 8 + 2147450880) / 8)).
  { rewrite unsigned_lit_wrap, Z.shiftr_div_pow2 by lia. change (2^3) with 8. rewrite Z.mod_small by (Z.div_mod_to_equations; lia).
    rewrite land_m8' by (Z.div_mod_to_equations; lia). f_equal. f_equal. lia. }
  rewrite E1, E2. clear E1 E2.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (AB0 : acc bsegs mm 7062656 1984) by (apply (acc_transport _ m mm _ _ AB MU); [lia| unfold shad, SHB; cbn; repeat split; try exact I; Z.div_mod_to_equations; lia]) end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (qc_word_zero mm _ _ PS AB0 ltac:(Z.div_mod_to_equations; lia) ltac:(Z.div_mod_to_equations; lia) ltac:(lia)) as W1;
    pose proof (qc_word_zero mm _ _ (PS + 7) AB0 ltac:(Z.div_mod_to_equations; lia) ltac:(Z.div_mod_to_equations; lia) ltac:(lia)) as W2 end.
  step. step. step. step. if_lit.

  step. if_cases K2; zify_cond K2. { exfalso. clear - K2 DLO LOD LO0. rewrite ?unsigned_lit in K2 by lia. lia. }

  step. step.
  do 28 (step; change (le1 (Z_to_bv 64 170)) with [Z_to_bv 8 170 : byte]; mem_after_store).
  step.
  do 4 (step; change (le1 (Z_to_bv 64 170)) with [Z_to_bv 8 170 : byte]; mem_after_store).
  do 4 step.
  step.

  step. step. if_cases K3; zify_cond K3. { exfalso. clear - K3 LOD LO0. rewrite ?unsigned_lit in K3 by lia. lia. }
  step. step. if_lit.
  step. change (le1 z64) with [Z_to_bv 8 0 : byte]. mem_after_store.
  step. step.

  step. step. step. if_lit.
  step. step. if_lit.
  step. step. if_cases K4; zify_cond K4. { exfalso. clear - K4 DT DLO LOD LO0. rewrite lxor_ones64 in K4 by lia. rewrite ?unsigned_lit in K4 by lia. lia. }
  step. if_lit.
  do 11 step.
  rewrite ?EUD.
  assert (E1 : Z.land (bv_unsigned (Z_to_bv 64 (2147450880 + D ≫ 3))) 18446744073709551608 = 8 * ((D / 8 + 2147450880) / 8)).
  { rewrite unsigned_lit_wrap, Z.shiftr_div_pow2 by lia. change (2^3) with 8. rewrite Z.mod_small by (Z.div_mod_to_equations; lia).
    rewrite land_m8' by (Z.div_mod_to_equations; lia). f_equal. f_equal. lia. }
  rewrite !E1. clear E1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (AS0 : acc bsegs mm (sp0 - 8388608) (140737488355328 - (sp0 - 8388608)))
      by (apply (acc_transport _ m mm _ _ AS MU); [lia| unfold shad, SHB; cbn; repeat split; try exact I; Z.div_mod_to_equations; lia]) end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (qc_word_zero mm _ _ D AS0 ltac:(Z.div_mod_to_equations; lia) ltac:(Z.div_mod_to_equations; lia) ltac:(lia)) as W3 end.
  step. step. step. step. if_lit.

  do 8 step.
  lazymatch goal with DCx : rw_cells _ ?mm D [CB 4 ?jj], LOCx : rw_cells _ _ (usp + -2176) (C1 (Z_to_bv 8 0) :: ?rest) |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    pose proof (rw_cells_split_CB bsegs mc D [] 4 jj [] [1; 3]%nat DCx eq_refl) as DS; cbn [mk_CB_cells app] in DS;
    apply (proj1 (F_fwritex.rw_cells_app bsegs _ _ [_] _)) in DS; destruct DS as [DSa DSb]; cbn [cells_size csize Nat.add] in DSb;
    pose proof (rw_cells_split_n bsegs mc (usp + -2176) _ 1%nat (usp + -2176 + 1) LOCx eq_refl) as [L0 _]; cbv [firstn] in L0;
    pose proof (proj2 (proj1 L0)) as SRC0; cbn [cells_bytes cbytes app] in SRC0
  end.
  assert (EUL : bv_unsigned (Z_to_bv 64 (usp + -2176)) = usp + -2176) by (apply unsigned_lit; lia).
  eapply evt_cut.
  { eapply (memcpy_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ [Z_to_bv 8 0] (firstn 1 j));
      [ rewrite EUL; exact SRC0 | rewrite (unsigned_lit 1) by lia; reflexivity | rewrite EUD, (unsigned_lit 1) by lia; exact DSa
      | rewrite EUD, EUL, (unsigned_lit 1) by lia; lia | assumption ]. }
  intros ms' PO. destruct_exs PO. destruct PO as [E [MUc [WMc [MIc [DSTc SRCc]]]]]. subst ms'.
  rewrite ?EUD, ?(unsigned_lit 1) in MUc by lia. rewrite ?EUD, ?(unsigned_lit 1) in DSTc by lia. cbn [Z.to_nat Pos.to_nat] in DSTc.
  lazymatch type of MUc with munch _ ?ma ?mb =>
    lazymatch goal with FRtx : rw_cells _ ma (usp + -72) ?cst, LOCx : rw_cells _ ma (usp + -2176) (C1 (Z_to_bv 8 0) :: C1 _ :: ?rest), STx : stk _ ma lo ?top |- _ =>
      assert (FRt' : rw_cells bsegs mb (usp + -72) cst)
        by (apply (rw_cells_agree bsegs _ _ _ _ FRtx); [apply (agree_of_munch _ _ _ _ MUc); intros xq Hxq; cbn [cells_size csize Nat.add length] in Hxq; cbn [outside]; lia| exact WMc]);
      assert (LOC' : rw_cells bsegs mb (usp + -2176) (C1 (Z_to_bv 8 0) :: C1 (Z_to_bv 8 170) :: rest))
        by (apply (rw_cells_agree bsegs _ _ _ _ LOCx); [apply (agree_of_munch _ _ _ _ MUc); intros xq Hxq; cbn [cells_size csize Nat.add length] in Hxq; cbn [outside]; lia| exact WMc]);
      assert (ST' : stk bsegs mb lo top)
        by (apply (stk_agree bsegs _ _ _ _ STx); [apply (agree_of_munch _ _ _ _ MUc); intros xq Hxq; cbn [outside]; lia| exact WMc]);
      assert (DSb' : rw_cells bsegs mb (D + Z.of_nat 1) [CB 3 (firstn 3 (skipn 1 j))])
        by (apply (rw_cells_agree bsegs _ _ _ _ DSb); [apply (agree_of_munch _ _ _ _ MUc); intros xq Hxq; cbn [cells_size csize Nat.add length] in Hxq; cbn [outside]; lia| exact WMc]);
      assert (MU' : munch [(lo, usp); (D, D + 4)] m mb)
        by (apply (munch_trans _ m ma mb); [eapply munch_weaken; [| exact MU] | eapply munch_weaken; [| exact MUc]]; unfold sub_fp; cbn [outside]; intros; lia);
      assert (WM' : wmono bsegs m mb) by exact (wmono_trans _ _ _ _ WM WMc);
      clear FRtx LOCx STx DSb MU WM MUc WMc L0 SRC0 DSa; try match goal with H : rw_cells _ _ D [CB 4 _] |- _ => clear H end; rename MU' into MU; rename WM' into WM; rename ST' into ST
    end end.
  lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?r)] => rewrite (ret_pc_even r) by (cbn; lia) end.

  pose proof (rw_cells_glue bsegs _ D _ _ _ DSTc DSb' eq_refl) as DST4. cbv [app] in DST4. merge_at DST4 0%nat 2%nat. clear DSTc DSb'.

  step. step. step.
  do 9 step.
  release_frame LOC' ST (usp + -72). release_frame FRt' ST usp.
  step. step.
  try rewrite ESP. unfold iwcrtomb_post. sys_finish.
  - rewrite EU. exact MU.
  - rewrite EU. exact ST.
  - exact DST4.
  - apply (IX2_frame sp0 _ lo (D + 4) m x13 (conj IXm XCm) MU WM); [unfold STACK_WIN; lia|].
    intros xq Hxq. unfold XWI, XTPLOC in Hxq. cbn [outside] in Hxq |- *. rewrite ?EU in *. lia.
Qed.
End Walk.
