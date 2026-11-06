(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require PropExec FxLin FxCore FxSubst FxSound FxMem FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxDrv FxFrame FxCall FxRgs FxFn.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.PropExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCall OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFn.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Mem Cells Exec Frame Arr Step Image RegsEquiv MState.
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Shadow.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Bigint_defs.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFA Require A_app2 A_rt_stmt A_long_mul_stmt.

Module A_long_mul_N.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Shadow.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Bigint_defs Bigint_shl.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFA Require Import A_app2.
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

Notation ASEGS := Asan.M.loaded_segments.

Section Norm.
  (* [comment removed for export] *)
  Variables (x1 x2 x3 x4 x5 x6 x7 x8 x9 x14 x15 x16 x17 x18 x19 x24 x25 x27 x28 x29 x30 x31 : word).
  Variables (va : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (cur : list word).
  Notation A := (bv_unsigned va).
  Notation LENP := (Z_to_bv 64 (A + 496)).
  Notation SHL := (Z_to_bv 64 ((A + 496) / 8 + ASAN_B)).
  Notation BB := (Z_to_bv 64 ASAN_B).
  Hypothesis Hcur : length cur = 62%nat.
  Hypothesis KA : (app2r (A) (A + 504))%Z.
  Hypothesis KA' : (A + 504 <= KTOP)%Z.

  Definition norm_post (l : Z) (m : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists (l' : Z) (a0 a2 a3 : word) (m' : word -> option byte),
      ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 a0 (Z_to_bv 64 l') a2 a3 x14 x15 x16 x17
                   x18 x19 va (Z_to_bv 64 1) SHL LENP x24 x25 BB x27 x28 x29 x30 x31)
               F (Z_to_bv 64 0x97540) fc None m' (seg_rom ASEGS)
      /\ munch [(A + 496, A + 498)]%Z m m'
      /\ wmono ASEGS m m'
      /\ rw_cells ASEGS m' (A + 496) [C2 (Z_to_bv 64 l')]
      /\ (0 <= l' <= l)%Z
      /\ bnorm cur (Z.to_nat l')
      /\ bval cur (Z.to_nat l') = bval cur (Z.to_nat l).

  (* [comment removed for export] *)
  Definition norm_ok (m0 : word -> option byte) (l0 : Z) (k : nat) : Prop :=
    forall (l : Z) (a0 a2 a3 : word) (m : word -> option byte),
      (Z.to_nat l <= k)%nat -> (0 < l <= l0)%Z ->
      u64arr ASEGS m A cur ->
      rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 l)] ->
      shz ASEGS m (ASAN_B + A / 8) 63 ->
      bval cur (Z.to_nat l) = bval cur (Z.to_nat l0) ->
      munch [(A + 496, A + 498)]%Z m0 m -> wmono ASEGS m0 m ->
      evt ASEGS (norm_post l0 m0)
        (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 a0 (Z_to_bv 64 l) a2 a3 x14 x15 x16 x17
                 x18 x19 va (Z_to_bv 64 1) SHL LENP x24 x25 BB x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x973e4) fc None m (seg_rom ASEGS)).

  #[using="Hcur KA KA'"] Lemma norm_body : forall m0 l0 k, (0 <= l0 <= 62)%Z -> norm_ok m0 l0 k -> norm_ok m0 l0 (S k).
  Proof. LiaFast.lf_pins (fun (Hcur KA KA' : LiaFast.U) => LiaFast.u0).
    intros m0 l0 k Hl0 IH. unfold norm_ok. intros l a0 a2 a3 m Hk Hl CUR LENC SHX VAL MU WM.
    pose proof (u64arr_bound _ _ _ _ CUR) as Bd. rewrite Hcur in Bd.
    zstep. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    rewrite shl48_shr45 by lia.
    zstep. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    destruct (nth_error cur (Z.to_nat (l - 1))) as [w|] eqn:Hn. 2:{ exfalso. apply nth_error_None in Hn. lia. }
    step. (* [comment removed for export] *) shr3.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      pose proof (u64arr_read ASEGS mc A cur (l - 1) w _ CUR Hn ltac:(lia) eq_refl) as RD end.
    step. (* [comment removed for export] *)
    clear RD.
    assert (Hw : limbZ cur (Z.to_nat l - 1) = bv_unsigned w).
    { unfold limbZ. replace (Z.to_nat l - 1)%nat with (Z.to_nat (l - 1)) by lia. rewrite (nth_error_nth _ _ _ Hn). reflexivity. }
    step. (* [comment removed for export] *)
    if_cases Hnz.
    - (* [comment removed for export] *)
      cond_cleanup Hnz.
      apply evt_done. unfold norm_post. exists l. do 3 eexists. exists m.
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact LENC|]. split; [lia|].
      split; [| exact VAL]. right. rewrite Hw. exact Hnz.
    - cond_cleanup Hnz.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      zstep. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hz.
      + cond_cleanup Hz.
        assert (Hl1 : (l + -1 <> 0)%Z). { intros E. apply Hz. apply (shl48_zero_iff (l + -1)); lia. }
        eapply IH; try eassumption; try lia.
        rewrite <- VAL. replace (Z.to_nat (l + -1)) with (Z.to_nat l - 1)%nat by lia. symmetry. apply bval_drop_zero_top; [lia|]. rewrite Hw. exact Hnz.
      + (* [comment removed for export] *)
        cond_cleanup Hz. apply (shl48_zero_iff (l + -1)) in Hz; [|lia].
        step. (* [comment removed for export] *)
        apply evt_done. unfold norm_post. eexists (l + -1)%Z. do 3 eexists. eexists.
        split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact LENC|]. split; [lia|].
        split. { left. lia. }
        rewrite <- VAL. replace (Z.to_nat (l + -1)) with (Z.to_nat l - 1)%nat by lia. symmetry. apply bval_drop_zero_top; [lia|]. rewrite Hw. exact Hnz.
  Qed.

  #[using="Hcur KA KA'"] Lemma norm_loop : forall m0 l0 k, (0 <= l0 <= 62)%Z -> norm_ok m0 l0 k.
  Proof. LiaFast.lf_pins (fun (Hcur KA KA' : LiaFast.U) => LiaFast.u0). intros m0 l0 k H. induction k as [|k IH]. - unfold norm_ok; intros; exfalso; lia. - apply norm_body; [exact H| exact IH]. Qed.

  (* [comment removed for export] *)
  #[using="Hcur KA KA'"] Lemma norm_run : forall (l : Z) (a0 a1 a2 a3 x21 : word) (m : word -> option byte),
    (0 <= l <= 62)%Z ->
    u64arr ASEGS m A cur ->
    rw_cells ASEGS m (A + 496) [C2 (Z_to_bv 64 l)] ->
    shz ASEGS m (ASAN_B + A / 8) 63 ->
    evt ASEGS (norm_post l m)
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 a0 a1 a2 a3 x14 x15 x16 x17
               x18 x19 va x21 SHL LENP x24 x25 BB x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x973c8) fc None m (seg_rom ASEGS)).
  Proof. LiaFast.lf_pins (fun (Hcur KA KA' : LiaFast.U) => LiaFast.u0).
    intros l a0 a1 a2 a3 x21 m Hl CUR LENC SHX.
    pose proof (u64arr_bound _ _ _ _ CUR) as Bd. rewrite Hcur in Bd.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite zx16_lit_small by lia.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hz.
    - cond_cleanup Hz. subst l.
      apply evt_done. unfold norm_post. eexists 0%Z. do 3 eexists. eexists.
      split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact LENC|]. split; [lia|].
      split; [apply bnorm_0| reflexivity].
    - cond_cleanup Hz.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      eapply (norm_loop m l (Z.to_nat l)); try eassumption; try lia.
      + apply munch_refl. + apply wmono_refl.
  Qed.
End Norm.
End A_long_mul_N.

Import OSSVerify.Proofs.fast_float.from_chars.lib.FFA.A_app2 OSSVerify.Proofs.fast_float.from_chars.lib.FFA.A_rt_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFA.A_long_mul_stmt OSSVerify.Proofs.fast_float.from_chars.lib.KX.KxLMn.A_long_mul_N.
From OSSVerify.Proofs.fast_float.from_chars.lib Require M4A_kfn.
From OSSVerify.Proofs.fast_float.from_chars.lib Require M4A_kfn M4A_lm.
Import OSSVerify.Proofs.fast_float.from_chars.lib.M4A_kfn.M4A_tmpl OSSVerify.Proofs.fast_float.from_chars.lib.M4A_kfn OSSVerify.Proofs.fast_float.from_chars.lib.M4A_lm.
From OSSVerify.Proofs.fast_float.from_chars.lib.KX Require Import KxBridge KxRun KxTac KxRt.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Abbreviation ASEGS := Asan.M.loaded_segments.

Lemma fact_at : forall E fs k f, Forall (fact_ok E) fs -> nth_error fs k = Some f -> fact_ok E f.
Proof. intros E fs k f H Hk. rewrite Forall_forall in H. apply H. exact (nth_error_In _ _ Hk). Qed.

(* [comment removed for export] *)
Lemma diff_small : forall a b lo hi, 0 <= a < two64 -> 0 <= b -> b + hi < two64 -> 0 <= lo ->
  lo <= (a - b) mod two64 <= hi -> b + lo <= a <= b + hi.
Proof.
  intros a b lo hi Ha Hb Hbh Hlo H. destruct (Z.le_gt_cases b a) as [Hle|Hlt].
  - rewrite Z.mod_small in H by (unfold two64 in *; lia). lia.
  - assert (Hm : (a - b) mod two64 = a - b + two64) by (symmetry; apply Z.mod_unique with (q := -1); unfold two64 in *; lia).
    rewrite Hm in H. unfold two64 in *. lia.
Qed.

(* [comment removed for export] *)
Lemma lmn_facts : forall c E1 ms1, (c = 0 \/ c = 16) -> sden ASEGS E1 (with_pc (LM_TAIL_Q c) 0x973c8) ms1 ->
  let q := bv_unsigned (E1 10%positive) in let xq := bv_unsigned (E1 30%positive) in
  0 <= bv_unsigned (E1 235%positive) <= 62 /\ 0 <= bv_unsigned (E1 235%positive) - bv_unsigned (E1 31%positive) <= 6 /\
  1594 <= q <= 34359735543 /\ 512 * q + 528896 <= xq <= 512 * q + 528896 + 131072 - 79 /\
  (KHI <= 4096 * q \/ 4096 * q + 11571200 <= SH_LO) /\
  bv_unsigned (lden E1 XA) = 8 * xq /\ bv_unsigned (lden E1 XS) = ASAN_B + xq /\
  app2r (8 * xq) (8 * xq + 504) /\ 8 * xq + 504 <= KTOP /\ (8 * xq) mod 8 = 0.
Proof.
  intros c E1 ms1 Hcc HD1 q xq.
  destruct (sden_0 _ _ _ _ HD1) as (_ & _ & _ & _ & _ & _ & HF & _). cbn [s_facts with_pc LM_TAIL_Q] in HF.
  pose proof (bv_unsigned_in_range _ (E1 30%positive)) as B30. pose proof (bv_unsigned_in_range _ (E1 10%positive)) as B10.
  pose proof (bv_unsigned_in_range _ (E1 31%positive)) as B31. pose proof (bv_unsigned_in_range _ (E1 235%positive)) as B235.
  unfold bv_modulus in B30, B10, B31, B235. change (2 ^ Z.of_N 64) with two64 in B30, B10, B31, B235.
  assert (HFx : forall k f, nth_error (LM_FQ c) k = Some f -> fact_ok E1 f) by (intros k f Hk; exact (fact_at E1 _ k f HF Hk)).
  assert (X : Forall (fact_ok E1) [FRange LEN 0 56; FRange (lsub XS (fsh AR4)) 0 (2 ^ 17 - 63 - 16); FRange FSP (IMG_END / 4096) ((KTOP - 0xb09000) / 4096);
                                  FRange (lsub FS (lconst KHI)) 0 (2 ^ 64 + SH_LO - 0xb09000 - KHI); FRange L0V 0 62; FRange (lsub L0V LEN) 0 6]).
  { destruct Hcc as [->| ->]; repeat apply Forall_cons; try apply Forall_nil;
      [ exact (HFx 3%nat _ eq_refl) | exact (HFx 5%nat _ eq_refl) | exact (HFx 9%nat _ eq_refl) | exact (HFx 10%nat _ eq_refl) | exact (HFx 40%nat _ eq_refl) | exact (HFx 41%nat _ eq_refl)
      | exact (HFx 3%nat _ eq_refl) | exact (HFx 5%nat _ eq_refl) | exact (HFx 9%nat _ eq_refl) | exact (HFx 10%nat _ eq_refl) | exact (HFx 40%nat _ eq_refl) | exact (HFx 41%nat _ eq_refl) ]. }
  clear HF HFx.
  apply Forall_cons_iff in X as [F3 X]. apply Forall_cons_iff in X as [F5 X]. apply Forall_cons_iff in X as [F9 X]. apply Forall_cons_iff in X as [F10 X].
  apply Forall_cons_iff in X as [F40 X]. apply Forall_cons_iff in X as [F41 _].
  cbn [fact_ok] in F3, F5, F9, F10, F40, F41.
  lnorm_s_in F3. lnorm_s_in F5. lnorm_s_in F9. lnorm_s_in F10. lnorm_s_in F40. lnorm_s_in F41. rewrite ?u_Z_to_bv in F5, F10, F41. unfold vz in *.
  change (IMG_END / 4096) with 1594 in F9. change ((KTOP - 0xb09000) / 4096) with 34359735543 in F9.
  fold q xq in F5, F9, F10.
  assert (Hxq : 512 * q + 528896 <= xq <= 512 * q + 528896 + 131072 - 79).
  { replace (-528896 + (-512 * q + (1 * xq + 0))) with (xq - (512 * q + 528896)) in F5 by ring.
    pose proof (diff_small xq (512 * q + 528896) 0 (131072 - 79) ltac:(unfold two64 in *; lia) ltac:(lia) ltac:(unfold two64 in *; lia) ltac:(lia) F5) as D.
    lia. }
  assert (Hcls : KHI <= 4096 * q \/ 4096 * q + 11571200 <= SH_LO).
  { replace (-17594333495296 + (4096 * q + 0)) with (4096 * q - 17594333495296) in F10 by ring.
    destruct (Z.le_gt_cases 17594333495296 (4096 * q)) as [Hh|Hl]; [left; unfold KHI; lia | right].
    assert (Hm : (4096 * q - 17594333495296) mod two64 = 4096 * q - 17594333495296 + two64)
      by (symmetry; apply Z.mod_unique with (q := -1); unfold two64 in *; lia).
    rewrite Hm in F10. unfold two64, SH_LO, KHI in *. lia. }
  assert (HA : bv_unsigned (lden E1 XA) = 8 * xq).
  { lnorm. rewrite u_Z_to_bv. unfold vz. fold xq. rewrite Z.add_0_r, Z.add_0_l, Z.mod_small by (unfold two64 in *; lia). reflexivity. }
  assert (HS : bv_unsigned (lden E1 XS) = ASAN_B + xq).
  { lnorm. rewrite u_Z_to_bv. unfold vz. fold xq. rewrite Z.add_0_r, Z.mod_small by (unfold two64 in *; lia). unfold SHB. ring. }
  replace (0 + (-1 * bv_unsigned (E1 31%positive) + (1 * bv_unsigned (E1 235%positive) + 0))) with
          (bv_unsigned (E1 235%positive) - bv_unsigned (E1 31%positive)) in F41 by ring.
  assert (H41 : 0 <= bv_unsigned (E1 235%positive) - bv_unsigned (E1 31%positive) <= 6).
  { pose proof (diff_small (bv_unsigned (E1 235%positive)) (bv_unsigned (E1 31%positive)) 0 6 ltac:(unfold two64 in *; lia) ltac:(lia)
                  ltac:(unfold two64 in *; lia) ltac:(lia) F41) as D. lia. }
  refine (conj F40 (conj H41 (conj F9 (conj Hxq (conj Hcls (conj HA (conj HS _))))))).
  unfold app2r, KHI, KTOP, SH_LO in *. split; [|split; [lia | rewrite Z.mul_comm, Z_mod_mult; reflexivity]].
  destruct Hcls as [Hh|Hl]; [right | left]; lia.
Qed.

(* [comment removed for export] *)
Definition bs_wf (n : positive) (R : region) : bool := (lwf n (rg_base R) && lwf n (rg_size R))%bool.
Lemma rgs_disj_agree_bs : forall n E1 E2 rgs, forallb (bs_wf n) rgs = true -> agree n E1 E2 -> rgs_disj E1 rgs -> rgs_disj E2 rgs.
Proof.
  intros n E1 E2 rgs. induction rgs as [|R rs IH]; intros Hw Ha Hd; [exact I|].
  cbn [forallb] in Hw. apply andb_prop in Hw as [HwR Hws]. destruct Hd as [Hx Hrs]. split; [|exact (IH Hws Ha Hrs)].
  apply Forall_forall. intros R' HR'. rewrite Forall_forall in Hx. pose proof (Hx R' HR') as Hd.
  rewrite forallb_forall in Hws. pose proof (Hws R' HR') as HwR'.
  unfold bs_wf in HwR, HwR'. apply andb_prop in HwR as [HbR HsR]. apply andb_prop in HwR' as [HbR' HsR'].
  unfold rg_disj, rsz in *. rewrite <- (lden_agree n E1 E2 _ HbR Ha), <- (lden_agree n E1 E2 _ HbR' Ha),
    <- (lden_agree n E1 E2 _ HsR Ha), <- (lden_agree n E1 E2 _ HsR' Ha). exact Hd.
Qed.

(* [comment removed for export] *)
Lemma rg_ok_rw_rt : forall E m b sz c, rg_ok ASEGS E m (RG b sz RW c) -> rg_ok ASEGS E m (RG b sz FxCore.RT c).
Proof.
  intros E m b sz c (H1 & H2 & H3 & H4). unfold rg_ok, rsz in *. cbn [rg_base rg_size rg_kind rg_cont] in *.
  split; [exact H1|]. split; [exact H2|]. split; [|exact H4]. intros i Hi. exact (proj1 (H3 i Hi)).
Qed.

Section EPI.
Variable c : Z.
Variable E1 : valu.
Variable ms1 : machine_state.
Variables (l' : Z) (a0' a2' a3' : word) (m2 : word -> option byte).
Local Abbreviation R1 := (ms_regs ms1).
Local Abbreviation A1 := (bv_unsigned (lden E1 XA)).
Definition E2 : valu := upds E1 [(210%positive, a0'); (211%positive, Z_to_bv 64 l'); (212%positive, a2'); (213%positive, a3'); (235%positive, Z_to_bv 64 l')].
Definition ms2 : machine_state :=
  MS (mkR (getr R1 1) (getr R1 2) (getr R1 3) (getr R1 4) (getr R1 5) (getr R1 6) (getr R1 7) (getr R1 8) (getr R1 9)
          a0' (Z_to_bv 64 l') a2' a3' (getr R1 14) (getr R1 15) (getr R1 16) (getr R1 17) (getr R1 18) (getr R1 19)
          (lden E1 XA) (Z_to_bv 64 1) (Z_to_bv 64 ((A1 + 496) / 8 + ASAN_B)) (Z_to_bv 64 (A1 + 496)) (getr R1 24) (getr R1 25)
          (Z_to_bv 64 ASAN_B) (getr R1 27) (getr R1 28) (getr R1 29) (getr R1 30) (getr R1 31))
     (ms_fregs ms1) (Z_to_bv 64 0x97540) (ms_fcsr ms1) None m2 (seg_rom ASEGS).

Hypothesis Hcc : c = 0 \/ c = 16.
Hypothesis HD1 : sden ASEGS E1 (with_pc (LM_TAIL_Q c) 0x973c8) ms1.
Hypothesis MU : munch [(A1 + 496, A1 + 498)] (ms_mem ms1) m2.
Hypothesis LC2 : rw_cells ASEGS m2 (A1 + 496) [C2 (Z_to_bv 64 l')].
Hypothesis Hl' : 0 <= l' <= 62.

#[using="Type"] Lemma E2_agree : agree 200 E1 E2.
Proof. LiaFast.lf_pins LiaFast.u0. apply upds_agree. repeat constructor; cbn [fst]; lia. Qed.
#[using="Type"] Lemma E2_235 : E2 235%positive = Z_to_bv 64 l'.
Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.

#[using="Hcc HD1 MU LC2 Hl'"] Lemma lmn_epi : sden ASEGS E2 (LM_EPI_P0 c) ms2.
Proof. LiaFast.lf_pins (fun (Hcc HD1 MU LC2 Hl' : LiaFast.U) => LiaFast.u0).
  pose proof (lmn_facts c E1 ms1 Hcc HD1) as (F40 & F41 & F9 & Hxq & Hcls & HA & HS & KA & KA' & A8).
  destruct (sden_0 _ _ _ _ HD1) as (Hpc & Hsvc & Hresv & HR & HG & HD & HF & Hfrm).
  cbn [s_pc s_regs s_rgs s_facts s_resv with_pc LM_TAIL_Q] in Hpc, Hresv, HR, HG, HD, HF.
  apply sden0_sden; [destruct Hcc as [->| ->]; vm_compute; reflexivity|].
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))); cbn [s_pc s_regs s_rgs s_facts s_resv LM_EPI_P0 ms2 MS ms_pc_val ms_svc_pending ms_resv ms_regs ms_mem ms_fcsr].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - (* [comment removed for export] *)
    assert (X22 : Z_to_bv 64 ((A1 + 496) / 8 + ASAN_B) = lden E2 (laddc XS 62)).
    { change (lden E2 (laddc XS 62)) with (lden E1 (laddc XS 62)). rewrite lden_laddc, HS, HA. f_equal.
      replace (8 * bv_unsigned (E1 30%positive) + 496) with ((bv_unsigned (E1 30%positive) + 62) * 8) by ring. rewrite Z.div_mul by lia.
      ring. }
    assert (X23 : Z_to_bv 64 (A1 + 496) = lden E2 (laddc XA 496)).
    { change (lden E2 (laddc XA 496)) with (lden E1 (laddc XA 496)). rewrite lden_laddc, HA. reflexivity. }
    apply regs_ok_of_cases. intros n Hn.
    destruct Hcc as [->| ->].
    all: do 32 (destruct n as [|n];
           [ getr_mkR_norm; rget_norm;
             first [ reflexivity | exact X22 | exact X23
                   | (rewrite (HR _); rget_norm; reflexivity)
                   | (lnorm; reflexivity) ]
           |]).
    all: lia.
  - (* [comment removed for export] *)
    assert (B2 : bv_unsigned (lden E1 (laddc XA 496)) = A1 + 496).
    { rewrite lden_laddc, u_Z_to_bv, HA, Z.mod_small by (unfold app2r, two64, KTOP in *; lia). reflexivity. }
    assert (HW : forall x, (forall j Rj, In j [2%nat] -> nth_error (LM_RGS_T c RW false) j = Some Rj ->
                   ~ (bv_unsigned (lden E1 (rg_base Rj)) <= x < bv_unsigned (lden E1 (rg_base Rj)) + rsz E1 Rj)) ->
                 Frame.outside [(A1 + 496, A1 + 498)] x).
    { intros x Hx. pose proof (Hx 2%nat _ ltac:(cbn; tauto) ltac:(destruct Hcc as [->| ->]; reflexivity)) as N2.
      unfold rsz in N2. cbn [rg_base rg_size track] in N2. rewrite B2 in N2. change (bv_unsigned (lden E1 (lconst 2))) with 2 in N2.
      cbn [Frame.outside]. lia. }
    assert (UW : forall i R, nth_error (LM_RGS_T c RW false) i = Some R -> ~ In i [2%nat] -> rg_ok ASEGS E1 (ms_mem ms1) R -> rg_ok ASEGS E1 m2 R).
    { intros i R Hi Hni HR0. exact (rg_ok_unwritten ASEGS E1 (ms_mem ms1) m2 (LM_RGS_T c RW false) _ [2%nat] i R HD Hi Hni MU HW HR0). }
    clear HW.
    destruct Hcc as [->| ->].
    all: pose proof HG as HG'; unfold LM_RGS_T in HG' |- *; cbn [app] in HG' |- *.
    all: clear HG; rename HG' into HG; apply Forall_cons_iff in HG as [G0 HG]; apply Forall_cons_iff in HG as [G1 HG]; apply Forall_cons_iff in HG as [G2 HG]; apply Forall_cons_iff in HG as [G3 HG]; apply Forall_cons_iff in HG as [G4 HG]; apply Forall_cons_iff in HG as [G5 HG]; apply Forall_cons_iff in HG as [G6 HG]; apply Forall_cons_iff in HG as [G7 HG]; apply Forall_cons_iff in HG as [G8 HG]; apply Forall_cons_iff in HG as [G9 HG]; apply Forall_cons_iff in HG as [G10 HG]; apply Forall_cons_iff in HG as [G11 HG]; apply Forall_cons_iff in HG as [G12 HG]; apply Forall_cons_iff in HG as [G13 HG]; apply Forall_cons_iff in HG as [G14 HG]; apply Forall_cons_iff in HG as [G15 HG]; apply Forall_cons_iff in HG as [G16 HG]; apply Forall_cons_iff in HG as [G17 HG]; apply Forall_cons_iff in HG as [G18 HG]; apply Forall_cons_iff in HG as [G19 HG]; apply Forall_cons_iff in HG as [G20 HG]; apply Forall_cons_iff in HG as [G21 HG]; apply Forall_cons_iff in HG as [G22 HG]; apply Forall_cons_iff in HG as [G23 HG]; apply Forall_cons_iff in HG as [G24 HG]; apply Forall_cons_iff in HG as [G25 HG]; apply Forall_cons_iff in HG as [G26 HG]; apply Forall_cons_iff in HG as [G27 HG]; apply Forall_cons_iff in HG as [G28 HG]; apply Forall_cons_iff in HG as [G29 HG]; clear HG.
    all: constructor; [apply (rg_ok_agree ASEGS 200 E1 E2); [vm_compute; reflexivity | exact E2_agree | exact (UW 0%nat _ eq_refl ltac:(cbn; intuition discriminate) G0)]|].
    all: constructor; [apply (rg_ok_agree ASEGS 200 E1 E2); [vm_compute; reflexivity | exact E2_agree | apply rg_ok_rw_rt; exact (UW 1%nat _ eq_refl ltac:(cbn; intuition discriminate) G1)]|].
    all: constructor; [|].
    1, 3: (* [comment removed for export] *)
      apply track_of_bytes_at; [ | lia | unfold rsz; cbn [rg_size]; rewrite lden_lconst, u_Z_to_bv, Z.mod_small by (unfold two64; lia); cbn [length]; lia | ];
      [ apply (rg_ok_of_rw_cells ASEGS E2 m2 _ (A1 + 496) [C2 (Z_to_bv 64 l')]); [reflexivity | reflexivity | | | exact LC2];
        [ cbn [rg_base]; change (lden E2 (laddc XA 496)) with (lden E1 (laddc XA 496)); exact B2
        | unfold rsz; cbn [rg_size]; rewrite lden_lconst, u_Z_to_bv, Z.mod_small by (unfold two64; lia); reflexivity ]
      | cbn [rg_base]; change (lden E2 (laddc XA 496)) with (lden E1 (laddc XA 496)); rewrite B2, Z.add_0_r;
        apply (bytes_at_ext ASEGS _ _ _ _ (proj2 (proj1 LC2))); cbn [cells_bytes cbytes List.map bden]; rewrite app_nil_r; unfold le2; cbn [Z_to_le_bytes];
        change (lden E2 L0V) with (lden E2 (lvar 235)); rewrite lden_lvar, E2_235, Z.shiftr_0_r; reflexivity ].
    all: constructor; [apply (rg_ok_agree ASEGS 200 E1 E2); [vm_compute; reflexivity | exact E2_agree | exact (UW 3%nat _ eq_refl ltac:(cbn; intuition discriminate) G3)]|].
    all: constructor; [apply (rg_ok_agree ASEGS 200 E1 E2); [vm_compute; reflexivity | exact E2_agree | exact (UW 4%nat _ eq_refl ltac:(cbn; intuition discriminate) G4)]|].
    all: constructor; [apply (rg_ok_agree ASEGS 200 E1 E2); [vm_compute; reflexivity | exact E2_agree | exact (UW 5%nat _ eq_refl ltac:(cbn; intuition discriminate) G5)]|].
    all: constructor; [apply (rg_ok_agree ASEGS 200 E1 E2); [vm_compute; reflexivity | exact E2_agree | exact (UW 6%nat _ eq_refl ltac:(cbn; intuition discriminate) G6)]|].
    all: constructor; [apply (rg_ok_agree ASEGS 200 E1 E2); [vm_compute; reflexivity | exact E2_agree | exact (UW 7%nat _ eq_refl ltac:(cbn; intuition discriminate) G7)]|].
    all: constructor; [apply (rg_ok_agree ASEGS 200 E1 E2); [vm_compute; reflexivity | exact E2_agree | exact (UW 8%nat _ eq_refl ltac:(cbn; intuition discriminate) G8)]|].
    all: constructor; [apply (rg_ok_agree ASEGS 200 E1 E2); [vm_compute; reflexivity | exact E2_agree | exact (UW 9%nat _ eq_refl ltac:(cbn; intuition discriminate) G9)]|].
    all: constructor; [apply (rg_ok_agree ASEGS 200 E1 E2); [vm_compute; reflexivity | exact E2_agree | exact (UW 10%nat _ eq_refl ltac:(cbn; intuition discriminate) G10)]|].
    all: constructor; [apply (rg_ok_agree ASEGS 200 E1 E2); [vm_compute; reflexivity | exact E2_agree | exact (UW 11%nat _ eq_refl ltac:(cbn; intuition discriminate) G11)]|].
    all: constructor; [apply (rg_ok_agree ASEGS 200 E1 E2); [vm_compute; reflexivity | exact E2_agree | exact (UW 12%nat _ eq_refl ltac:(cbn; intuition discriminate) G12)]|].
    all: constructor; [apply (rg_ok_agree ASEGS 200 E1 E2); [vm_compute; reflexivity | exact E2_agree | exact (UW 13%nat _ eq_refl ltac:(cbn; intuition discriminate) G13)]|].
    all: constructor; [apply (rg_ok_agree ASEGS 200 E1 E2); [vm_compute; reflexivity | exact E2_agree | exact (UW 14%nat _ eq_refl ltac:(cbn; intuition discriminate) G14)]|].
    all: constructor; [apply (rg_ok_agree ASEGS 200 E1 E2); [vm_compute; reflexivity | exact E2_agree | exact (UW 15%nat _ eq_refl ltac:(cbn; intuition discriminate) G15)]|].
    all: constructor; [apply (rg_ok_agree ASEGS 200 E1 E2); [vm_compute; reflexivity | exact E2_agree | exact (UW 16%nat _ eq_refl ltac:(cbn; intuition discriminate) G16)]|].
    all: constructor; [apply (rg_ok_agree ASEGS 200 E1 E2); [vm_compute; reflexivity | exact E2_agree | exact (UW 17%nat _ eq_refl ltac:(cbn; intuition discriminate) G17)]|].
    all: constructor; [apply (rg_ok_agree ASEGS 200 E1 E2); [vm_compute; reflexivity | exact E2_agree | exact (UW 18%nat _ eq_refl ltac:(cbn; intuition discriminate) G18)]|].
    all: constructor; [apply (rg_ok_agree ASEGS 200 E1 E2); [vm_compute; reflexivity | exact E2_agree | exact (UW 19%nat _ eq_refl ltac:(cbn; intuition discriminate) G19)]|].
    all: constructor; [apply (rg_ok_agree ASEGS 200 E1 E2); [vm_compute; reflexivity | exact E2_agree | exact (UW 20%nat _ eq_refl ltac:(cbn; intuition discriminate) G20)]|].
    all: constructor; [apply (rg_ok_agree ASEGS 200 E1 E2); [vm_compute; reflexivity | exact E2_agree | exact (UW 21%nat _ eq_refl ltac:(cbn; intuition discriminate) G21)]|].
    all: constructor; [apply (rg_ok_agree ASEGS 200 E1 E2); [vm_compute; reflexivity | exact E2_agree | exact (UW 22%nat _ eq_refl ltac:(cbn; intuition discriminate) G22)]|].
    all: constructor; [apply (rg_ok_agree ASEGS 200 E1 E2); [vm_compute; reflexivity | exact E2_agree | exact (UW 23%nat _ eq_refl ltac:(cbn; intuition discriminate) G23)]|].
    all: constructor; [apply (rg_ok_agree ASEGS 200 E1 E2); [vm_compute; reflexivity | exact E2_agree | exact (UW 24%nat _ eq_refl ltac:(cbn; intuition discriminate) G24)]|].
    all: constructor; [apply (rg_ok_agree ASEGS 200 E1 E2); [vm_compute; reflexivity | exact E2_agree | exact (UW 25%nat _ eq_refl ltac:(cbn; intuition discriminate) G25)]|].
    all: constructor; [apply (rg_ok_agree ASEGS 200 E1 E2); [vm_compute; reflexivity | exact E2_agree | exact (UW 26%nat _ eq_refl ltac:(cbn; intuition discriminate) G26)]|].
    all: constructor; [apply (rg_ok_agree ASEGS 200 E1 E2); [vm_compute; reflexivity | exact E2_agree | exact (UW 27%nat _ eq_refl ltac:(cbn; intuition discriminate) G27)]|].
    all: constructor; [apply (rg_ok_agree ASEGS 200 E1 E2); [vm_compute; reflexivity | exact E2_agree | exact (UW 28%nat _ eq_refl ltac:(cbn; intuition discriminate) G28)]|].
    all: constructor; [apply (rg_ok_agree ASEGS 200 E1 E2); [vm_compute; reflexivity | exact E2_agree | exact (UW 29%nat _ eq_refl ltac:(cbn; intuition discriminate) G29)]|].
    all: constructor.

  - (* [comment removed for export] *)
    apply (rgs_disj_agree_bs 200 E1 E2); [destruct Hcc as [->| ->]; vm_compute; reflexivity | exact E2_agree |].
    apply (rgs_disj_shape E1 (LM_RGS_T c RW false)); [destruct Hcc as [->| ->]; vm_compute; reflexivity | exact HD].
  - (* [comment removed for export] *)
    unfold LM_FE. apply Forall_app. split.
    + unfold LM_FQ in HF. apply Forall_app in HF as [HF1 _].
      assert (Hw : forallb (fwf 200) (LM_F c) = true) by (destruct Hcc as [->| ->]; vm_compute; reflexivity).
      rewrite forallb_forall in Hw. rewrite Forall_forall in HF1 |- *. intros f Hf.
      exact (fact_ok_agree 200 E1 E2 f (Hw f Hf) E2_agree (HF1 f Hf)).
    + constructor; [|constructor]. cbn [fact_ok]. change (lden E2 L0V) with (lden E2 (lvar 235)). rewrite lden_lvar, E2_235, u_Z_to_bv.
      rewrite Z.mod_small by (unfold two64; lia). lia.
  - exact Hfrm.
Qed.
End EPI.

(* [comment removed for export] *)
Theorem lmn_run : forall c E1 ms1 (POST : machine_state -> Prop), (c = 0 \/ c = 16) ->
  sden ASEGS E1 (with_pc (LM_TAIL_Q c) 0x973c8) ms1 -> ms_rom ms1 = seg_rom ASEGS ->
  (forall ws1 l' a0' a2' a3' m2,
     u64arr ASEGS (ms_mem ms1) (bv_unsigned (lden E1 XA)) ws1 -> length ws1 = 62%nat ->
     bnorm ws1 (Z.to_nat l') -> 0 <= l' <= bv_unsigned (E1 235%positive) ->
     munch [(bv_unsigned (lden E1 XA) + 496, bv_unsigned (lden E1 XA) + 498)] (ms_mem ms1) m2 -> wmono ASEGS (ms_mem ms1) m2 ->
     sden ASEGS (E2 E1 l' a0' a2' a3') (LM_EPI_P0 c) (ms2 E1 ms1 l' a0' a2' a3' m2) ->
     evt ASEGS POST (ms2 E1 ms1 l' a0' a2' a3' m2)) ->
  evt ASEGS POST ms1.
Proof.
  intros c E1 ms1 POST Hcc HD1 Hrom K.
  pose proof (lmn_facts c E1 ms1 Hcc HD1) as (F40 & F41 & F9 & Hxq & Hcls & HA & HS & KA & KA' & A8).
  destruct (sden_0 _ _ _ _ HD1) as (Hpc & Hsvc & Hresv & HR & HG & HD & HF & Hfrm).
  cbn [s_pc s_regs s_rgs s_facts s_resv with_pc LM_TAIL_Q] in Hpc, Hresv, HR, HG, HD, HF. unfold rsv_ok in Hresv.
  set (A1 := bv_unsigned (lden E1 XA)) in *.
  assert (KA1 : app2r A1 (A1 + 504)) by (rewrite HA; exact KA). assert (KA1' : A1 + 504 <= KTOP) by (rewrite HA; exact KA').
  (* [comment removed for export] *)
  assert (R20 : getr (ms_regs ms1) 20 = lden E1 XA) by (rewrite (HR _); destruct Hcc as [->| ->]; rget_norm; reflexivity).
  assert (R22 : getr (ms_regs ms1) 22 = Z_to_bv 64 ((A1 + 496) / 8 + ASAN_B)).
  { rewrite (HR _). assert (X : rget (LM_TQ_R c) (rkey 22) = laddc XS 62) by (destruct Hcc as [->| ->]; vm_compute; reflexivity).
    rewrite X, lden_laddc, HS, HA. f_equal.
    replace (8 * bv_unsigned (E1 30%positive) + 496) with ((bv_unsigned (E1 30%positive) + 62) * 8) by ring. rewrite Z.div_mul by lia. ring. }
  assert (R23 : getr (ms_regs ms1) 23 = Z_to_bv 64 (A1 + 496)).
  { rewrite (HR _). assert (X : rget (LM_TQ_R c) (rkey 23) = laddc XA 496) by (destruct Hcc as [->| ->]; vm_compute; reflexivity).
    rewrite X, lden_laddc. reflexivity. }
  assert (R26 : getr (ms_regs ms1) 26 = Z_to_bv 64 ASAN_B) by (rewrite (HR _); destruct Hcc as [->| ->]; rget_norm; lnorm; reflexivity).
  (* [comment removed for export] *)
  assert (G1 : rg_ok ASEGS E1 (ms_mem ms1) (RG XA (lconst 496) RW TEmpty)).
  { rewrite Forall_forall in HG. apply HG. destruct Hcc as [->| ->]; unfold LM_RGS_T; cbn [app]; right; left; reflexivity. }
  assert (G2 : rg_ok ASEGS E1 (ms_mem ms1) (track (RG (laddc XA 496) (lconst 2) RW TEmpty) 0 [BV L0V 0; BV L0V 1])).
  { rewrite Forall_forall in HG. apply HG. destruct Hcc as [->| ->]; unfold LM_RGS_T; cbn [app]; right; right; left; reflexivity. }
  assert (G3 : rg_ok ASEGS E1 (ms_mem ms1) xsh_c).
  { rewrite Forall_forall in HG. apply HG. destruct Hcc as [->| ->]; unfold LM_RGS_T; cbn [app]; right; right; right; left; reflexivity. }
  assert (B2 : bv_unsigned (lden E1 (laddc XA 496)) = A1 + 496).
  { rewrite lden_laddc, u_Z_to_bv, Z.mod_small by (rewrite HA in *; unfold app2r, two64, KTOP in *; lia). reflexivity. }
  destruct (u64arr_of_rg ASEGS E1 _ _ A1 62 G1 ltac:(left; reflexivity) eq_refl
              ltac:(unfold rsz; cbn [rg_size]; rewrite lden_lconst, u_Z_to_bv, Z.mod_small by (unfold two64; lia); reflexivity)) as (ws1 & CUR & L62).
  assert (LENC1 : rw_cells ASEGS (ms_mem ms1) (A1 + 496) [C2 (Z_to_bv 64 (bv_unsigned (E1 235%positive)))]).
  { split; [split; [cbn; tauto|] |].
    - pose proof (track_bytes_at ASEGS E1 (ms_mem ms1) _ 0 _ G2 ltac:(lia) ltac:(cbn; lia)) as X. cbn [rg_base] in X. rewrite B2, Z.add_0_r in X.
      apply (bytes_at_ext ASEGS _ _ _ _ X). cbn [cells_bytes cbytes List.map bden]. rewrite app_nil_r. unfold le2. cbn [Z_to_le_bytes].
      change (lden E1 L0V) with (lden E1 (lvar 235)). rewrite lden_lvar, Z_to_bv_bv_unsigned, Z.shiftr_0_r. reflexivity.
    - cbn [cells_size csize]. change (Z.of_nat (2 + 0)) with 2.
      pose proof (wr_at_of_rg ASEGS E1 _ _ _ _ (rg_ok_untrack ASEGS E1 _ _ _ _ _ _ G2) ltac:(left; reflexivity) ltac:(cbn [rg_base]; exact B2) eq_refl) as W.
      unfold rsz in W. cbn [rg_size] in W. rewrite lden_lconst, u_Z_to_bv, Z.mod_small in W by (unfold two64; lia). exact W. }
  assert (SHX1 : shz ASEGS (ms_mem ms1) (ASAN_B + A1 / 8) 63).
  { split; [lia|]. replace (A1 / 8) with (bv_unsigned (E1 30%positive)) by (rewrite HA, Z.mul_comm, Z.div_mul by lia; reflexivity).
    exact (zeros_bytes_of_rt ASEGS E1 _ _ _ 63 G3 ltac:(vm_compute; reflexivity) ltac:(lia) HS). }
  (* [comment removed for export] *)
  assert (Heqv : ms_eqv (kms ASEGS ms1) ms1).
  { pose proof (kms_eqv ASEGS ms1 Hsvc) as X. rewrite <- Hrom, with_rom_eta in X. exact X. }
  apply (evt_eqv_l ASEGS _ ms1 (kms ASEGS ms1) (ms_eqv_sym _ _ Heqv)).
  unfold kms, mkR_of. rewrite Hpc, Hresv, R20, R22, R23, R26.
  eapply evt_cut.
  { exact (norm_run (getr (ms_regs ms1) 1) (getr (ms_regs ms1) 2) (getr (ms_regs ms1) 3) (getr (ms_regs ms1) 4) (getr (ms_regs ms1) 5)
             (getr (ms_regs ms1) 6) (getr (ms_regs ms1) 7) (getr (ms_regs ms1) 8) (getr (ms_regs ms1) 9) (getr (ms_regs ms1) 14)
             (getr (ms_regs ms1) 15) (getr (ms_regs ms1) 16) (getr (ms_regs ms1) 17) (getr (ms_regs ms1) 18) (getr (ms_regs ms1) 19)
             (getr (ms_regs ms1) 24) (getr (ms_regs ms1) 25) (getr (ms_regs ms1) 27) (getr (ms_regs ms1) 28) (getr (ms_regs ms1) 29)
             (getr (ms_regs ms1) 30) (getr (ms_regs ms1) 31) (lden E1 XA) (ms_fregs ms1) (ms_fcsr ms1) ws1 L62 KA1 KA1'
             (bv_unsigned (E1 235%positive)) (getr (ms_regs ms1) 10) (getr (ms_regs ms1) 11) (getr (ms_regs ms1) 12) (getr (ms_regs ms1) 13)
             (getr (ms_regs ms1) 21) (ms_mem ms1) F40 CUR LENC1 SHX1). }
  intros ms' HP. unfold norm_post in HP. destruct HP as (l' & a0' & a2' & a3' & m2 & Hms & MU & WM & LC2 & Hl' & BN & _). subst ms'.
  apply (K ws1 l' a0' a2' a3' m2 CUR L62 BN Hl' MU WM).
  exact (lmn_epi c E1 ms1 l' a0' a2' a3' m2 Hcc HD1 MU LC2 ltac:(lia)).
Qed.

(* [comment removed for export] *)
Definition is_ro (k : rkind) : bool := match k with RO => true | _ => false end.
Fixpoint kinds_ok_acc (wi : list nat) (j : nat) (rgs : list region) : bool :=
  match rgs with
  | [] => true
  | R :: rs => ((existsb (Nat.eqb j) wi || is_rt (rg_kind R) || is_ro (rg_kind R)) && kinds_ok_acc wi (S j) rs)%bool
  end.
Definition kinds_ok (wi : list nat) (rgs : list region) : bool := kinds_ok_acc wi 0 rgs.

Lemma kinds_ok_acc_spec : forall wi rgs j0 j R, kinds_ok_acc wi j0 rgs = true -> nth_error rgs j = Some R -> ~ In (j0 + j)%nat wi ->
  is_rt (rg_kind R) = true \/ rg_kind R = RO.
Proof.
  intros wi rgs. induction rgs as [|R0 rs IH]; intros j0 j R H Hj Hni; [destruct j; discriminate|].
  cbn [kinds_ok_acc] in H. apply andb_prop in H as [H1 H2]. destruct j as [|j].
  - cbn in Hj. injection Hj as ->. rewrite Nat.add_0_r in Hni.
    apply orb_prop in H1 as [H1|H1]; [apply orb_prop in H1 as [H1|H1]|].
    + exfalso. apply existsb_exists in H1 as (k & Hk & Hk2). apply Nat.eqb_eq in Hk2. subst k. exact (Hni Hk).
    + left. exact H1.
    + right. unfold is_ro in H1. destruct (rg_kind R); try discriminate. reflexivity.
  - cbn in Hj. apply (IH (S j0) j R H2 Hj). replace (S j0 + j)%nat with (j0 + S j)%nat by lia. exact Hni.
Qed.
Lemma kinds_ok_spec : forall wi rgs j R, kinds_ok wi rgs = true -> nth_error rgs j = Some R -> ~ In j wi ->
  is_rt (rg_kind R) = true \/ rg_kind R = RO.
Proof. intros wi rgs j R H Hj Hni. exact (kinds_ok_acc_spec wi rgs 0 j R H Hj Hni). Qed.

Lemma ro_none : forall segs E m rgs R x, Forall (rg_ok segs E m) rgs -> In R rgs -> rg_kind R = RO -> in_rg E R x -> m x = None.
Proof.
  intros segs E m rgs R x HF Hin Hk Hx. rewrite Forall_forall in HF. destruct (HF R Hin) as (H1 & H2 & H3 & _).
  unfold in_rg in Hx. pose proof (H3 (bv_unsigned x - bv_unsigned (lden E (rg_base R))) ltac:(lia)) as X. rewrite Hk in X.
  destruct X as (X & _). replace (bv_unsigned (lden E (rg_base R)) + (bv_unsigned x - bv_unsigned (lden E (rg_base R)))) with (bv_unsigned x) in X by ring.
  rewrite Z_to_bv_bv_unsigned in X. exact X.
Qed.

Lemma frame_idx : forall E rgs (wi : list nat) (m m' : word -> option byte) x,
  kinds_ok wi rgs = true ->
  (forall j R, In j wi -> nth_error rgs j = Some R -> ~ in_rg E R x) ->
  (fr_pt E rgs x -> m' x = m x) ->
  (forall R, In R rgs -> rg_kind R = RO -> in_rg E R x -> m x = None /\ m' x = None) ->
  m' x = m x.
Proof.
  intros E rgs wi m m' x Hk Hw Hfr Hro.
  assert (Hcl : fr_pt E rgs x \/ exists R, In R rgs /\ rg_kind R = RO /\ in_rg E R x).
  { destruct (Exists_dec (fun R => in_rg E R x) rgs) as [He|Hn].
    - intros R. unfold in_rg. destruct (Z_le_gt_dec (bv_unsigned (lden E (rg_base R))) (bv_unsigned x)) as [A1|A1];
        [destruct (Z_lt_ge_dec (bv_unsigned x) (bv_unsigned (lden E (rg_base R)) + rsz E R)) as [B1|B1]|]; [left; lia | right; lia | right; lia].
    - apply Exists_exists in He as (R & HR & Hx). apply In_nth_error in HR as (j & Hj).
      destruct (In_dec Nat.eq_dec j wi) as [Hi|Hni]; [exfalso; exact (Hw j R Hi Hj Hx)|].
      destruct (kinds_ok_spec wi rgs j R Hk Hj Hni) as [Hrt|Hro'].
      + left. right. apply Exists_exists. exists R. split; [exact (nth_error_In _ _ Hj) | split; [exact Hrt | exact Hx]].
      + right. exists R. split; [exact (nth_error_In _ _ Hj) | split; [exact Hro' | exact Hx]].
    - left. left. unfold FxStep.outside. rewrite Forall_forall. intros R HR.
      destruct (Z_le_gt_dec (bv_unsigned (lden E (rg_base R))) (bv_unsigned x)) as [A1|A1]; [|left; lia].
      destruct (Z_lt_ge_dec (bv_unsigned x) (bv_unsigned (lden E (rg_base R)) + rsz E R)) as [B1|B1]; [|right; lia].
      exfalso. apply Hn. apply Exists_exists. exists R. split; [exact HR | unfold in_rg; lia]. }
  destruct Hcl as [Hf|(R & HR & Hro' & Hx)]; [exact (Hfr Hf)|].
  destruct (Hro R HR Hro' Hx) as (H1 & H2). rewrite H1, H2. reflexivity.
Qed.
