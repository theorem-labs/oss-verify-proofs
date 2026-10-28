(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA Walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Str_memset.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import F_memset R_cache_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

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
      unfold zidle in *; transport_after_call asegs m mm MU WM end end.
Open Scope bv_scope.
Notation mem := (word -> option byte).

Definition imemset_entry : Z := 0x94ac4.

Ltac with_arr_i tac :=
  lazymatch goal with
  | ARR : u8arr ?segs ?m ?A ?bs, FIL : filled ?cb ?bs _, LEN : length ?bs = _ |- _ => tac segs ARR FIL LEN A cb
  end.
Ltac fin_i cover :=
  zstep;
  with_arr_i ltac:(fun segs ARR FIL LEN A cb =>
    let E := fresh "E" in
    pose proof (filled_all _ _ _ FIL ltac:(cover)) as E;
    rewrite LEN in E; rewrite E in ARR;
    apply rw_cells_of_u8arr in ARR; rewrite repeat_length in ARR);
  finish; subst; first [assumption | rewrite Z.mod_small by lia; assumption].

Section IMS.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m : mem) (D C N : Z).
Hypothesis HD : (0 <= D)%Z.
Hypothesis HN : (0 < N)%Z.
Hypothesis HDN : (D + N < 2^64)%Z.
Hypothesis HC : (0 <= C < 256)%Z.

Definition ims_Q := memset_postZ ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D C N m.

Lemma ims_bytes : forall (k : nat) p (m1 : mem) (bs : list byte) (Q : Z -> Prop) (ptr : word),
  ptr = Z_to_bv 64 (D + p) ->
  (p + Z.of_nat k = N)%Z -> (1 <= k)%nat -> (0 <= p)%Z ->
  u8arr asegs m1 D bs -> filled (Z_to_bv 8 C) bs Q -> length bs = Z.to_nat N ->
  (forall j, (0 <= j < p)%Z -> Q j) ->
  mem_inv asegs m1 -> munch [(D, D + N)]%Z m m1 -> wmono asegs m m1 ->
  evt asegs ims_Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 C) (Z_to_bv 64 (D + N)) ptr a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x94adc) fc None m1 (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros p m1 bs Q ptr Eptr Hk H1 Hp ARR FIL LEN HQ MI MU WM; [lia|]. subst ptr.
  mst p 1%nat ltac:(rewrite le1_byte, unsigned_lit, Z.mod_small by lia; reflexivity).
  zhide.
  zstep. zstep.
  destruct k as [|k].
  - ifF. zstep.
    fin_i ltac:(intros j Hj; cbv beta; destruct (Z_lt_le_dec j p); [left; apply HQ; lia| right; lia]).
  - ifT. replace (D + p + 1)%Z with (D + (p + 1))%Z by lia.
    eapply (IH (p + 1)%Z); try eassumption; try lia; [reflexivity|].
    intros j Hj. cbv beta. destruct (Z_lt_le_dec j p); [left; apply HQ; lia| right; lia].
Qed.

Lemma ims_words : forall (k : nat) p (m1 : mem) (bs : list byte) (Q : Z -> Prop) (ptr : word),
  ptr = Z_to_bv 64 (D + p) ->
  (p + 16 * Z.of_nat k = N)%Z -> (1 <= k)%nat -> (0 <= p)%Z ->
  u8arr asegs m1 D bs -> filled (Z_to_bv 8 C) bs Q -> length bs = Z.to_nat N ->
  (forall j, (0 <= j < p)%Z -> Q j) ->
  mem_inv asegs m1 -> munch [(D, D + N)]%Z m m1 -> wmono asegs m m1 ->
  evt asegs ims_Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 (C * BC8)) (Z_to_bv 64 (D + N)) ptr
             a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x94b10) fc None m1 (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros p m1 bs Q ptr Eptr Hk H1 Hp ARR FIL LEN HQ MI MU WM; [lia|]. subst ptr.
  mst p 8%nat ltac:(symmetry; apply le8_bcast; lia).
  replace (D + p + 8)%Z with (D + (p + 8))%Z by lia.
  mst (p + 8)%Z 8%nat ltac:(symmetry; apply le8_bcast; lia).
  zhide.
  zstep. zstep.
  destruct k as [|k].
  - ifF.
    fin_i ltac:(intros j Hj; cbv beta; destruct (Z_lt_le_dec j p); [left; left; apply HQ; lia|];
                destruct (Z_lt_le_dec j (p + 8)); [left; right; lia| right; lia]).
  - ifT. replace (D + p + 16)%Z with (D + (p + 16))%Z by lia.
    eapply (IH (p + 16)%Z); try eassumption; try lia; [reflexivity|].
    intros j Hj. cbv beta. destruct (Z_lt_le_dec j p); [left; left; apply HQ; lia|].
    destruct (Z_lt_le_dec j (p + 8)); [left; right; lia| right; lia].
Qed.
End IMS.

Lemma land15_lor : forall x y, (0 <= x)%Z -> (0 <= y)%Z -> Z.land (Z.lor x y) 15 = 0%Z -> (x mod 16 = 0 /\ y mod 16 = 0)%Z.
Proof.
  intros x y Hx Hy H. rewrite Z.land_lor_distr_l in H. apply Z.lor_eq_0_iff in H. destruct H as [H1 H2].
  change 15%Z with (Z.ones 4) in H1, H2. rewrite Z.land_ones in H1, H2 by lia. split; assumption.
Qed.

Lemma imemset_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (D C N : Z) (junk : list byte),
  rw_cells asegs m D [CB (Z.to_nat N) junk] -> mem_inv asegs m ->
  (0 <= D)%Z -> (0 <= N)%Z -> (D + N < 2^64)%Z -> (0 <= C < 256)%Z ->
  evt asegs (memset_postZ ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D C N m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 C) (Z_to_bv 64 N) a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 imemset_entry) fc None m (seg_rom asegs)).
Proof.
  intros until junk. intros DST MI HD HN HDN HC. unfold imemset_entry.
  pose proof (munch_refl [(D, D + N)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (u8arr_of_rw_cells _ _ _ _ _ DST) as ARR.
  pose proof (rw_cells_CB_length _ _ _ _ _ DST) as LEN.
  pose proof (filled_init (Z_to_bv 8 C) junk) as FIL.
  clear DST.
  zhide.
  do 3 zstep.
  assert (RL : (0 <= Z.land (Z.lor N D) 15 < 16)%Z).
  { change 15%Z with (Z.ones 4). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
  destruct (Z.eqb_spec (Z.land (Z.lor N D) 15) 0) as [AL|AL].
  - ifT. zstep.
    destruct (Z.eq_dec N 0) as [N0|N0].
    + ifT. fin_i ltac:(intros j Hj; lia).
    + ifF.
      destruct (land15_lor N D ltac:(lia) ltac:(lia) AL) as [AN AD].
      do 7 zstep.
      setreg 11%Z (Z_to_bv 64 (C * BC8)) ltac:(unfold BC8; brute256 C HC).
      zstep.
      eapply ims_words with (k := Z.to_nat (N / 16)) (p := 0%Z) (ptr := Z_to_bv 64 D).
      all: first [ eassumption | (f_equal; lia) | lia | (intros j Hj; lia) ].
  - ifF. zstep.
    destruct (Z.eq_dec N 0) as [N0|N0].
    + ifT. fin_i ltac:(intros j Hj; lia).
    + ifF. do 2 zstep.
      eapply ims_bytes with (k := Z.to_nat N) (p := 0%Z) (ptr := Z_to_bv 64 D).
      all: first [ eassumption | (f_equal; lia) | lia | (intros j Hj; lia) ].
Qed.
