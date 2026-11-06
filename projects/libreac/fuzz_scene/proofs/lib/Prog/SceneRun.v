From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_scene.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Prog Require Import reac_scene_struct SceneTac.
Import ListNotations.
Open Scope Z_scope.

Ltac show_g := match goal with |- ?G => idtac "GOAL:" G end.

Section SceneRun.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).

Definition saved : list cell :=
  [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition S0 : Z := bv_unsigned sp + -9072.

Definition Qret (m1 : word -> option byte) (ms' : machine_state) : Prop :=
  exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7'
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m1 (seg_rom rsegs).

Lemma scene_exit : forall (ra' t0' t1' t2' x8 x9 a0' a1' a2' a3' a4' a5' a6' a7'
                          x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3' t4' t5' t6' : word)
                          (m1 : word -> option byte),
  9072 <= bv_unsigned sp ->
  rw_cells rsegs m1 (bv_unsigned sp + -104) saved ->
  evt rsegs (Qret m1)
    (MS (mkR ra' (Z_to_bv 64 S0) gp tp t0' t1' t2' x8 x9 a0' a1' a2' a3' a4' a5' a6' a7'
             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3' t4' t5' t6')
        F (Z_to_bv 64 0x15348) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra' t0' t1' t2' x8 x9 a0' a1' a2' a3' a4' a5' a6' a7' x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
         t3' t4' t5' t6' m1 HSP FS.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  unfold saved in FS. unfold S0.
  do 19 zstep.
  unfold Qret. finish.
Qed.

Definition lenZ (data : list byte) : Z := Z.of_nat (length data).

Lemma len_cond : forall u, 0 <= u < 2 ^ 26 ->
  negb (bv_eqb (Z_to_bv 64 (Z.shiftr u 26)) (Z_to_bv 64 0)) = false.
Proof. intros u Hu. rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by lia. reflexivity. Qed.

Definition nE (b0 b1 b2 : Z) : Z := if Z.land b0 1 =? 0 then b1 + 256 * b2 else 8904.

Definition nbE (n : Z) : Z := if n =? 0 then 1 else n.

Definition sx16 (v : Z) : Z := if v <? 32768 then v else v - 65536.

Lemma lor_b2b1 : forall x y : Z, 0 <= x < 256 -> 0 <= y < 256 ->
  Z.lor (Z.shiftl y 8 mod 18446744073709551616) x = x + 256 * y.
Proof.
  intros x y Hx Hy. rewrite Z.mod_small.
  - rewrite Z.lor_comm. apply lor_shiftl8_add; lia.
  - rewrite Z.shiftl_mul_pow2 by lia. lia.
Qed.

Lemma nb_b2z : forall v, 0 <= v -> v + Z.b2z (v <? 1) = nbE v.
Proof. intros v Hv. unfold nbE. destruct (Z.eqb_spec v 0); destruct (Z.ltb_spec v 1); cbn; lia. Qed.

Lemma sx16_shift : forall v, 0 <= v < 65536 ->
  Z.shiftr (bv_signed (Z_to_bv 64 (v * 281474976710656))) 48 = sx16 v.
Proof.
  intros v Hv. rewrite zb_signed. rewrite unsigned_lit by lia.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 48) with 281474976710656.
  unfold sx16.
  destruct (Z.ltb_spec (v * 281474976710656) (2 ^ 63)); destruct (Z.ltb_spec v 32768); try lia.
  all: first [ rewrite Z.div_mul by lia; reflexivity
             | replace (v * 281474976710656 - 2 ^ 64) with ((v - 65536) * 281474976710656) by lia;
               rewrite Z.div_mul by lia; reflexivity ].
Qed.

Lemma lor_b4b3 : forall b3 b4, 0 <= b3 < 256 -> 0 <= b4 < 256 ->
  Z.lor (Z.shiftl b4 56 mod 18446744073709551616) (Z.shiftl b3 48 mod 18446744073709551616) =
  (b3 + 256 * b4) * 281474976710656.
Proof.
  intros b3 b4 H3 H4.
  rewrite (Z.mod_small (Z.shiftl b4 56)) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  rewrite (Z.mod_small (Z.shiftl b3 48)) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  replace (Z.shiftl b4 56) with (Z.shiftl (Z.shiftl b4 8) 48) by (rewrite Z.shiftl_shiftl by lia; reflexivity).
  rewrite <- Z.shiftl_lor. rewrite Z.lor_comm. rewrite lor_shiftl8_add by lia.
  rewrite Z.shiftl_mul_pow2 by lia. reflexivity.
Qed.

Lemma shl_b4 : forall b4, 0 <= b4 < 256 -> Z.shiftl b4 56 = (0 + 256 * b4) * 281474976710656.
Proof. intros b4 H. rewrite Z.shiftl_mul_pow2 by lia. lia. Qed.

Lemma shl_b3 : forall b3, 0 <= b3 < 256 ->
  Z.lor 0 (Z.shiftl b3 48 mod 18446744073709551616) = (b3 + 0) * 281474976710656.
Proof.
  intros b3 H. rewrite Z.lor_0_l. rewrite Z.mod_small by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  rewrite Z.shiftl_mul_pow2 by lia. lia.
Qed.

Definition gbz (data : list byte) (i : nat) : Z :=
  match nth_error data i with Some b => bv_unsigned b | None => 0 end.
Definition cE (data : list byte) : Z := Z.min (lenZ data) 11.
Definition inp_cells (data : list byte) : list cell :=
  map C1 (firstn 11 data) ++ [CB (length (skipn 11 data)) (skipn 11 data)].

Definition QE (m : word -> option byte) (lo p n c r st s7v fl : Z) (inp : list cell) (ms' : machine_state) : Prop :=
  exists (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
          x28 x29 x30 x31 : word) (m' : word -> option byte) (macb : list byte),
    ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
                  x27 x28 x29 x30 x31) F (Z_to_bv 64 0x16698) fc None m' (seg_rom rsegs) /\
    x1 = Z_to_bv 64 0x14fa4 /\ bv_unsigned x2 = bv_unsigned sp - 9072 /\ x3 = gp /\ x4 = tp /\ x8 = s0 /\ x9 = s1 /\
    bv_unsigned x10 = nbE n /\ x18 = x10 /\ bv_unsigned x19 = p + c /\ x20 = Z_to_bv 64 st /\
    bv_unsigned x22 = r /\ x23 = Z_to_bv 64 s7v /\ bv_unsigned x24 = n /\ x25 = s9 /\ x26 = s10 /\ x27 = s11 /\
    x21 = Z_to_bv 64 fl /\
    munch [(bv_unsigned sp - 9072, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
    stk rsegs m' lo (bv_unsigned sp) /\
    bytes_at rsegs m' (bv_unsigned sp - 104) (cells_bytes saved) /\
    bytes_at rsegs m' (bv_unsigned sp - 110) macb /\ length macb = 6%nat /\
    rw_cells rsegs m' p inp.

Definition entry_stmt (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : word -> option byte) (lo : Z)
    (p : word) (data : list byte) : Prop :=
  rw_cells rsegs m (bv_unsigned p) (inp_cells data) ->
  mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> lo + 9072 <= bv_unsigned sp ->
  bv_unsigned sp mod 16 = 0 ->
  (bv_unsigned p + lenZ data <= lo \/ bv_unsigned sp <= bv_unsigned p) ->
  lenZ data < 2 ^ 26 -> bv_unsigned p + lenZ data < 2 ^ 64 ->
  evt rsegs (QE m lo (bv_unsigned p) (nE (gbz data 0) (gbz data 1) (gbz data 2)) (cE data) (lenZ data - cE data)
               (sx16 (gbz data 3 + 256 * gbz data 4)) (sx16 (256 * gbz data 4)) (gbz data 0) (inp_cells data))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 p (Z_to_bv 64 (lenZ data)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x14e98) fc None m (seg_rom rsegs)).

End SceneRun.

Ltac byte_ranges :=
  repeat match goal with
  | b : bv 8 |- _ =>
      lazymatch goal with
      | _ : 0 <= bv_unsigned b < 256 |- _ => fail
      | _ => let Hb := fresh "Rb" in pose proof (bv_unsigned_in_range 8 b) as Hb; unfold bv_modulus in Hb;
             change (2 ^ Z.of_N 8) with 256 in Hb
      end
  end.

Ltac entry_cases HL :=
  lazymatch type of HL with context [length ?data] =>
    destruct data as [|b0 [|b1 [|b2 [|b3 [|b4 [|b5 [|b6 [|b7 [|b8 [|b9 [|b10 rest]]]]]]]]]]];
    cbn [length] in HL; try (exfalso; lia)
  end;
  unfold entry_stmt; intros HD HMI ST LO SPA DJ HN HPW;
  unfold inp_cells, gbz, cE, lenZ in *; cbn [firstn skipn map app length nth_error] in *;
  try (match goal with r : list byte |- _ =>
         change (firstn 0 r) with (@nil byte) in *; change (skipn 0 r) with r in *; cbn [map app] in * end).

Ltac carve_as n := match goal with ST : stk _ _ _ _ |- _ => carve_frame n ST end.

Ltac rel_at sp a hi := match goal with
  | F1 : rw_cells _ _ (bv_unsigned sp + a) _, ST : stk _ _ _ _ |- _ => release_frame F1 ST hi end.

Ltac entry_run sp :=
  match goal with HD : rw_cells _ _ (bv_unsigned ?p) _, HM : mem_inv _ ?m, ST : stk _ _ _ _ |- _ =>
    pose proof (bv_unsigned_in_range 64 sp) as Rsp; pose proof (bv_unsigned_in_range 64 p) as Rp;
    unfold bv_modulus in Rsp, Rp;
    pose proof ST as [Hlo0 _];
    pose proof (munch_refl [(bv_unsigned sp - 9072, bv_unsigned sp)] m) as MU;
    pose proof (wmono_refl rsegs m) as WM
  end;
  carve_as 104%nat; rename FR into FRs;
  carve_as 6%nat; rename FR into FRm;
  carve_as 3005%nat; rename FR into FRb;
  carve_as 3005%nat; rename FR into FRa;
  carve_as 8%nat; rename FR into FRp;
  carve_as 2944%nat; rename FR into FRl;
  do 16 zstep;
  replace (bv_unsigned sp + -2032 - 4096) with (bv_unsigned sp + -6128) by lia;
  zstep; zstep;
  replace (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -6128)) + -2048) with (bv_unsigned sp + -8176)
    by (rewrite unsigned_lit by lia; lia);
  zstep; zstep; zstep;
  lazymatch goal with |- context [Z.shiftr ?u 26] => if_false_by (len_cond u ltac:(lia)) end;
  zr_until 0x14f88;
  zstep;
  first [ if_true | if_false | (let EF := fresh "EF" in if_cases EF; zify_cond EF) ];
  zr_until 0x16698;
  match goal with
  | F1 : rw_cells _ _ (bv_unsigned sp + -104) _, F2 : rw_cells _ _ (bv_unsigned sp + -110) _ |- _ =>
      pose proof (proj2 (proj1 F1)) as SBs; pose proof (proj2 (proj1 F2)) as SBm
  end;
  rel_at sp (-9072) (bv_unsigned sp + -6128);
  rel_at sp (-6128) (bv_unsigned sp + -6120);
  rel_at sp (-6120) (bv_unsigned sp + -3115);
  rel_at sp (-3115) (bv_unsigned sp + -110);
  rel_at sp (-110) (bv_unsigned sp + -104);
  rel_at sp (-104) (bv_unsigned sp);
  unfold QE; finish.

Ltac entry_vals sp :=
  try reflexivity;
  byte_ranges;
  rewrite ?lor_b2b1, ?lor_b4b3, ?shl_b4, ?shl_b3 by lia;
  rewrite ?sx16_shift by lia;
  rewrite ?nb_b2z by lia;
  try reflexivity;
  try (rewrite unsigned_lit by (unfold nbE; repeat (case_match; try lia); lia);
       unfold nE; repeat (match goal with EF : Z.land _ 1 = 0 |- _ => rewrite EF end); cbn; lia);
  try (rewrite unsigned_lit by (unfold nbE; repeat (case_match; try lia); lia);
       unfold nE; repeat (match goal with EF : Z.land _ 1 = 0 |- _ => rewrite EF end); cbn -[nbE];
       f_equal; lia);
  try (rewrite unsigned_lit by lia; lia);
  try (match goal with SBm : bytes_at _ _ (bv_unsigned sp + -110) _ |- _ => eexact SBm end);
  try reflexivity;
  try (unfold nE; match goal with |- context [Z.land (bv_unsigned ?b) 1 =? 0] =>
         destruct (Z.eqb_spec (Z.land (bv_unsigned b) 1) 0) as [EZ|EZ]; [exfalso; lia | ] end;
       match goal with |- ?G => sclosed G end; vm_compute; reflexivity);
  try lia.
