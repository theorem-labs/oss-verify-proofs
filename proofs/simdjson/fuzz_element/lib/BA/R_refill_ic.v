(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac ImageA Arr Walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import R_sizeclass.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout R_small R_m2s. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import R_cache_defs R_classid R_refill.
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

Definition icache (m : mem) (T : Z) (cnt mc cs : Z -> Z) : Prop :=
  forall j, (1 <= j <= 31)%Z -> pc_cells m (pc_addr T j) (cnt j) (mc j) (cs j).
Definition ic_ranges (cnt mc cs : Z -> Z) : Prop :=
  forall j, (1 <= j <= 31)%Z -> (0 <= cnt j < 2^31)%Z /\ (0 <= mc j < 2^31)%Z /\ (0 <= cs j < 2^63)%Z.

Definition mix (i : Z) (f g : Z -> Z) : Z -> Z := fun j => if (j <? i)%Z then f j else g j.

Definition size_e (i : Z) : Z :=
  (Z.land (Z.shiftr (bv_signed (Z_to_bv 64 (Z.shiftl i 63))) 63 mod 18446744073709551616)
         (Z.shiftr (Z.shiftl 512 (Z.shiftr (i - 16) 1 mod 64) mod 18446744073709551616) 1)
   + Z.shiftl 512 (Z.shiftr (i - 16) 1 mod 64))%Z.
Lemma size_large_ok : forall i, (17 <= i <= 30)%Z -> size_e i = ClassSize i.
Proof. intros i Hi. exact (brute_eq size_e ClassSize 17 30 ltac:(vm_compute; reflexivity) i Hi). Qed.

Lemma maxcount_eq : forall i, (1 <= i <= 31)%Z ->
  ((Z.min 8 (1024 / ClassSize i) + Z.b2z (Z.min 8 (1024 / ClassSize i) =? 0)) * 2 = MaxCount i)%Z.
Proof.
  intros i Hi. exact (brute_eq (fun i => (Z.min 8 (1024 / ClassSize i) + Z.b2z (Z.min 8 (1024 / ClassSize i) =? 0)) * 2)%Z
                               MaxCount 1 31 ltac:(vm_compute; reflexivity) i Hi).
Qed.

Lemma maxcount_code : forall i, (1 <= i <= 31)%Z ->
  Z.shiftl ((Z.min 8 (1024 / ClassSize i) + Z.b2z (Z.min 8 (1024 / ClassSize i) <? 1)) mod 18446744073709551616) 1 = MaxCount i.
Proof.
  intros i Hi. exact (brute_eq (fun i => Z.shiftl ((Z.min 8 (1024 / ClassSize i) + Z.b2z (Z.min 8 (1024 / ClassSize i) <? 1)) mod 18446744073709551616) 1)
                               MaxCount 1 31 ltac:(vm_compute; reflexivity) i Hi).
Qed.

Lemma ClassSize_large : forall i, (17 <= i <= 30)%Z -> (768 <= ClassSize i)%Z.
Proof.
  intros i Hi. apply Z.leb_le.
  exact (allb_ok (fun i => 768 <=? ClassSize i)%Z 17 30 ltac:(vm_compute; reflexivity) i Hi).
Qed.

Definition ic_head : Z := 0x605b4.
Definition ic_join : Z := 0x60590.

Section Loop.
Variables (ra sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 s0o : word) (F : bvmap 5 word) (fc : bv 32).
Variables (ACEIL T c P lo : Z) (cnt mc cs : Z -> Z) (m0 : mem) (junk : list byte).
Hypothesis HT : T_ok ACEIL T.
Hypothesis Hc : (1 <= c <= 31)%Z.
Hypothesis EP : P = pc_addr T c.
Hypothesis HR : ic_ranges cnt mc cs.
Hypothesis HLO : (ACEIL <= lo)%Z.
Hypothesis HLOH : (kHighShadowEnd + 8 <= lo)%Z.
Hypothesis HLO2 : (lo <= bv_unsigned sp - 32)%Z.
Hypothesis HSP : (bv_unsigned sp <= 2^47)%Z.

Definition ic_W : list (Z * Z) := [(cacheT T, cstats T); (bv_unsigned sp - 32, bv_unsigned sp)]%Z.
Definition ic_post : machine_state -> Prop :=
  refill_A_post ra sp gp tp s0o s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc T c P (MaxCount c / 2) lo ic_W m0
    (fun m' => icache m' T cnt MaxCount ClassSize).

Lemma ic_body : forall (i : Z) (t5' : word) (m : mem),
  (1 <= i <= 31)%Z ->
  icache m T cnt (mix i MaxCount mc) (mix i ClassSize cs) ->
  rw_cells asegs m (bv_unsigned sp - 32) [CB 8 junk; C8 s1; C8 s0o; C8 ra] ->
  stk asegs m lo (bv_unsigned sp - 32) ->
  munch ic_W m0 m -> wmono asegs m0 m -> mem_inv asegs m ->
  (forall (m2 : mem) (t5'' : word),
     icache m2 T cnt (mix (i + 1) MaxCount mc) (mix (i + 1) ClassSize cs) ->
     rw_cells asegs m2 (bv_unsigned sp - 32) [CB 8 junk; C8 s1; C8 s0o; C8 ra] ->
     stk asegs m2 lo (bv_unsigned sp - 32) ->
     munch ic_W m0 m2 -> wmono asegs m0 m2 -> mem_inv asegs m2 ->
     evt asegs ic_post
       (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp - 32)) gp tp (Z_to_bv 64 16) (Z_to_bv 64 17) (Z_to_bv 64 512) (Z_to_bv 64 P) s1
             (Z_to_bv 64 (cacheT T)) (Z_to_bv 64 (T + 208 + 80 * (i + 1) + 8)) (Z_to_bv 64 INST) (Z_to_bv 64 (32 * (i + 1)))
             (Z_to_bv 64 c) (Z_to_bv 64 (i + 1 - 16)) (Z_to_bv 64 15) (Z_to_bv 64 1024) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             (Z_to_bv 64 (ClassSize i)) (Z_to_bv 64 (MaxCount i)) t5'' t6)
        F (Z_to_bv 64 0x605b0) fc None m2 (seg_rom asegs))) ->
  evt asegs ic_post
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp - 32)) gp tp (Z_to_bv 64 16) (Z_to_bv 64 17) (Z_to_bv 64 512) (Z_to_bv 64 P) s1
             (Z_to_bv 64 (cacheT T)) (Z_to_bv 64 (T + 208 + 80 * i + 8)) (Z_to_bv 64 INST) (Z_to_bv 64 (32 * i)) (Z_to_bv 64 c)
             (Z_to_bv 64 (i - 16)) (Z_to_bv 64 15) (Z_to_bv 64 1024) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             (Z_to_bv 64 (ClassSize i)) (Z_to_bv 64 (Z.min 8 (1024 / ClassSize i))) t5' t6)
        F (Z_to_bv 64 ic_join) fc None m (seg_rom asegs)).
Proof.
  intros i t5' m Hi31 FAM FR ST MU WM MI K.
  pose proof HT as (HT1 & HT2 & HT3 & HT4 & HT5). unfold kHighShadowEnd in *.
  pose proof (ClassSize_range i Hi31) as [HCS _].
  pose proof (FAM i Hi31) as CI. unfold pc_cells, pc_addr, mix in CI. rewrite Z.ltb_irrefl in CI.
  pose proof (HR i Hi31) as (Rc & Rm & Rs).
  remember (T + 208 + 80 * i)%Z as Q eqn:EQ.
  replace (T + 208 + 80 * i + 8)%Z with (Q + 8)%Z by lia.
  pose proof (munch_refl [(Q + 4, Q + 16)]%Z m) as MUb. pose proof (wmono_refl asegs m) as WMb.
  unfold ic_join, ic_W, cacheT, cstats in *.
  zhide.
  do 5 zstep.
  let e := getreg 29%Z in lazymatch e with Z_to_bv 64 ?E =>
    replace E with (MaxCount i) by (exact (eq_sym (maxcount_code i Hi31))) end.
  pose proof (MaxCount_range i Hi31) as [HMC _].
  do 3 zstep.
  replace (Q + 88)%Z with (T + 208 + 80 * (i + 1) + 8)%Z by lia.
  replace (32 * i + 32)%Z with (32 * (i + 1))%Z by lia.
  replace (i - 16 + 1)%Z with (i + 1 - 16)%Z by lia.
  apply K; try assumption.
  intros j Hj. unfold mix. destruct (Z.eq_dec j i) as [->|Hne].
  - rewrite (proj2 (Z.ltb_lt i (i + 1))) by lia. unfold pc_cells, pc_addr. rewrite <- EQ. exact CI.
  - pose proof (FAM j Hj) as Cj. unfold mix in Cj.
    replace (j <? i + 1)%Z with (j <? i)%Z by (destruct (Z.ltb_spec j i); destruct (Z.ltb_spec j (i + 1)); lia).
    unfold pc_cells, pc_addr in Cj |- *.
    eapply rw_cells_transport; [exact Cj| exact MUb| exact WMb|].
    unfold disjoint_from. cbn [cells_size csize Nat.add]. cbn -[Z.mul Z.add]. lia.
Qed.

Lemma ic_loop : forall (k : nat) (i : Z) (t3 t4 t5 : word) (m : mem),
  i = (31 - Z.of_nat k)%Z -> (1 <= i)%Z ->
  icache m T cnt (mix i MaxCount mc) (mix i ClassSize cs) ->
  rw_cells asegs m (bv_unsigned sp - 32) [CB 8 junk; C8 s1; C8 s0o; C8 ra] ->
  stk asegs m lo (bv_unsigned sp - 32) ->
  munch ic_W m0 m -> wmono asegs m0 m -> mem_inv asegs m ->
  evt asegs ic_post
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp - 32)) gp tp (Z_to_bv 64 16) (Z_to_bv 64 17) (Z_to_bv 64 512) (Z_to_bv 64 P) s1
             (Z_to_bv 64 (cacheT T)) (Z_to_bv 64 (T + 208 + 80 * i + 8)) (Z_to_bv 64 INST) (Z_to_bv 64 (32 * i)) (Z_to_bv 64 c)
             (Z_to_bv 64 (i - 16)) (Z_to_bv 64 15) (Z_to_bv 64 1024) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ic_head) fc None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros i t3 t4 t5 m Ei Hi FAM FR ST MU WM MI;
    pose proof HT as (HT1 & HT2 & HT3 & HT4 & HT5); unfold kHighShadowEnd in *; unfold ic_head.
  -
    cbn [Z.of_nat] in Ei. replace i with 31%Z in * by lia. clear Ei Hi.
    zhide.
    zstep. ifTw.
    do 4 zstep. rewrite v_divuw_small by lia. ifFw.
    do 3 zstep.
    replace (Z_to_bv 64 64) with (Z_to_bv 64 (ClassSize 31)) by reflexivity.
    replace (Z_to_bv 64 8) with (Z_to_bv 64 (Z.min 8 (1024 / ClassSize 31))) by reflexivity.
    replace (T + 2696)%Z with (T + 208 + 80 * 31 + 8)%Z by lia.
    apply (ic_body 31); [lia| assumption..|].
    intros m2 t5'' FAM' FR' ST' MU' WM' MI'. change (31 + 1)%Z with 32%Z in *.
    zstep. ifTw.

    pose proof (FAM' c Hc) as CC. unfold mix in CC. rewrite (proj2 (Z.ltb_lt c 32)) in CC by lia.
    pose proof (HR c Hc) as (Rc & Rm & Rs). pose proof (MaxCount_range c Hc) as [HMCc _].
    unfold pc_cells in CC. rewrite <- EP in CC.
    assert (EPz : P = (T + 208 + 80 * c)%Z) by (rewrite EP; reflexivity).
    zstep. rewrite (sx32_small_A (MaxCount c)) by lia.
    do 9 zstep. rewrite (srliw1_small (MaxCount c)) by lia.
    unfold cacheT, cstats, INST, g_instance in *.
    replace (T + 208 + 2560)%Z with (T + 2768)%Z by lia.
    finish; [eassumption|].
    intros j Hj. pose proof (FAM' j Hj) as Cj. unfold mix in Cj. rewrite (proj2 (Z.ltb_lt j 32)) in Cj by lia. exact Cj.
  -
    rewrite Nat2Z.inj_succ in Ei.
    assert (Hi30 : (1 <= i <= 30)%Z) by lia.
    pose proof (ClassSize_range i ltac:(lia)) as [HCS _].
    zstep. ifFw.
    do 3 zstep. replace (i - 16 + 16)%Z with i by lia.
    destruct (Z.le_gt_cases i 16) as [Hs|Hl].
    +
      assert (ES : ClassSize i = (32 * i)%Z) by (unfold ClassSize; rewrite (proj2 (Z.eqb_neq i 31)) by lia; rewrite (proj2 (Z.leb_le i 16)) by lia; reflexivity).
      ifTw.
      zstep. rewrite v_divuw_small by lia.
      do 2 zstep. if_cases K; zify_cond K.
      *
        replace (Z_to_bv 64 (1024 / (32 * i))) with (Z_to_bv 64 (Z.min 8 (1024 / ClassSize i))) by (rewrite ES; f_equal; lia).
        rewrite <- ES at 2.
        apply (ic_body i); [lia| assumption..|].
        intros m2 t5'' FAM' FR' ST' MU' WM' MI'.
        zstep. ifFw.
        apply (IH (i + 1)%Z); [lia| lia| assumption..].
      *
        do 2 zstep.
        replace (Z_to_bv 64 8) with (Z_to_bv 64 (Z.min 8 (1024 / ClassSize i))) by (rewrite ES; f_equal; lia).
        rewrite <- ES at 2.
        apply (ic_body i); [lia| assumption..|].
        intros m2 t5'' FAM' FR' ST' MU' WM' MI'.
        zstep. ifFw.
        apply (IH (i + 1)%Z); [lia| lia| assumption..].
    +
      pose proof (ClassSize_large i ltac:(lia)) as HCL.
      ifFw.
      do 7 zstep.
      let e := getreg 28%Z in lazymatch e with Z_to_bv 64 ?E => replace E with (ClassSize i) by (exact (eq_sym (size_large_ok i ltac:(lia)))) end.
      zstep. rewrite v_divuw_small by lia.
      assert (HD : (1024 / ClassSize i < 8)%Z) by (apply Z.div_lt_upper_bound; lia).
      do 2 zstep. ifTw.
      replace (Z_to_bv 64 (1024 / ClassSize i)) with (Z_to_bv 64 (Z.min 8 (1024 / ClassSize i))) by (f_equal; lia).
      apply (ic_body i); [lia| assumption..|].
      intros m2 t5'' FAM' FR' ST' MU' WM' MI'.
      zstep. ifFw.
      apply (IH (i + 1)%Z); [lia| lia| assumption..].
Qed.
End Loop.

Lemma refill_AI_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (ACEIL T c lo : Z) (cnt mc cs : Z -> Z),
  (1 <= c <= 31)%Z ->
  icache m T cnt mc cs -> ic_ranges cnt mc cs -> mc c = 0%Z ->
  T_ok ACEIL T ->
  stk asegs m lo (bv_unsigned sp) -> (ACEIL <= lo)%Z -> (kHighShadowEnd + 8 <= lo)%Z -> (lo <= bv_unsigned sp - 32)%Z ->
  (bv_unsigned sp <= 2^47)%Z ->
  mem_inv asegs m ->
  evt asegs (refill_A_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc T c (pc_addr T c) (MaxCount c / 2) lo
               [(cacheT T, cstats T); (bv_unsigned sp - 32, bv_unsigned sp)]%Z m (fun m' => icache m' T cnt MaxCount ClassSize))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (cacheT T)) (Z_to_bv 64 (pc_addr T c)) (Z_to_bv 64 INST) (Z_to_bv 64 c)
             a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 refill_entry) fc None m (seg_rom asegs)).
Proof.
  intros until cs. intros Hc FAM HR Hmc0 HT ST HLO HLOH HLO2 HSP MI.
  pose proof HT as (HT1 & HT2 & HT3 & HT4 & HT5). unfold kHighShadowEnd in *.
  pose proof (FAM c Hc) as CC. pose proof (HR c Hc) as (Rc & Rm & Rs). rewrite Hmc0 in CC.
  unfold pc_cells in CC. unfold pc_addr in *.
  remember (T + 208 + 80 * c)%Z as P eqn:EP.
  pose proof (munch_refl [(cacheT T, cstats T); (bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MUb.
  unfold cacheT, cstats, INST, refill_entry, g_instance in *.
  carve_frame 32%nat ST.
  zhide.
  do 7 zstep. rewrite (sx32_small_A 0) by lia. zstep. ifT.
  do 9 zstep.
  replace (T + 296)%Z with (T + 208 + 80 * 1 + 8)%Z by lia.
  replace (bv_unsigned sp + -32)%Z with (bv_unsigned sp - 32)%Z in * by lia.
  eapply (ic_loop ra sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 s0 F fc ACEIL T c P lo cnt mc cs m) with (k := 30%nat) (i := 1%Z);
    try eassumption; try (rewrite EP; reflexivity); try (cbn; lia); try lia.
  intros j Hj. unfold mix. rewrite (proj2 (Z.ltb_ge j 1)) by lia.
  pose proof (FAM j Hj) as Cj. unfold pc_cells, pc_addr in Cj |- *.
  eapply rw_cells_transport; [exact Cj| exact MUb| exact WM|].
  unfold disjoint_from. cbn [cells_size csize Nat.add]. cbn -[Z.mul Z.add]. lia.
Qed.
