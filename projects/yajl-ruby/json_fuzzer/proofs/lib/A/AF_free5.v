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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA AImages.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import AF_place AF_kit AF_kit2 AF_poison AF_qkit.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanConsts AsanSizeClass.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import StrFun.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import SecRanges.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Zify.zify_internal_to_euclidean_division_equations ::= OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA.LiaFastA.zify_fast_euclid3.   (* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= force_section_ranges.   (* [comment removed for export] *)
Ltac pg := match goal with |- ?g => idtac "GOAL:"; idtac g end.
Ltac phyps := match goal with |- _ => repeat match goal with H : ?t |- _ => idtac H ":" t; fail end end.
Ltac djs := cbn [disjoint_from length cells_size csize Nat.add Nat.mul Z.of_nat Pos.of_succ_nat Pos.succ Pos.mul Pos.add]; rewrite ?length_le8, ?length_le4; repeat split; try exact I; lia.

(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac lia ::=
  first [ LiaTuning.zify_prune; LiaTuning.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | LiaTuning.zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ].
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac aceil :=
  lazymatch goal with
  | H : _ <= alloc_ceiling <= _ |- _ => idtac
  | |- context [alloc_ceiling] => repeat match goal with H : True |- _ => clear H end; pose proof alloc_ceiling_range as CEILB
  | H : context [alloc_ceiling] |- _ => repeat match goal with H' : True |- _ => clear H' end; pose proof alloc_ceiling_range as CEILB
  | _ => first [ pose proof I as CEILB | idtac ]
  end.
(* [comment removed for export] *)
Local Ltac slia ::= first [ exact I | dlia | split; [dlia | exact I] ].
Local Ltac flia ::= first [ assumption | lia ].
Local Definition carry_skip (P : Prop) := P.
Local Ltac skipH H := lazymatch type of H with ?TS => change TS with (carry_skip TS) in H end.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac dlia1 := dlia.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac incl_leaves xq Hq :=
  repeat match type of Hq with _ /\ _ => let Q := fresh "Q" in destruct Hq as [Q Hq] end;
  repeat match goal with |- _ /\ _ => split end; try exact I;
  let C := fresh "C" in intros C;
  first [ match goal with Q : ~ (_ <= xq < _) |- _ => apply Q; LiaA.lia_probe end
        | match goal with D : _ \/ _ |- _ => destruct D as [XD|XD]; match goal with Q : ~ (_ <= xq < _) |- _ => apply Q; LiaA.lia_probe end end ].
(* [comment removed for export] *)
Local Ltac solve_covers ::=
  let lo := fresh "lo" in let hi := fresh "hi" in let Hin := fresh "Hin" in
  intros lo hi Hin; cbn [In app] in Hin;
  repeat match type of Hin with
  | _ \/ _ => destruct Hin as [Hin|Hin]; [injection Hin as <- <-; do 2 eexists; split; [cover_member| cbn [fst snd b_addr]; LiaA.lia_probe] |]
  | _ = _ => injection Hin as <- <-; do 2 eexists; split; [cover_member| cbn [fst snd b_addr]; LiaA.lia_probe]
  | False => contradiction
  end.
Local Ltac carry_rw H MU WM ::= eapply rw_cells_transport in H; [| exact MU| exact WM| cbn; repeat match goal with |- _ /\ _ => split end; first [exact I | dlia1]].
Local Ltac carry_all mc m' MUc WMc ::=
  repeat match goal with
  | H : rw_cells asegs mc _ _ |- _ => first [ carry_rw H MUc WMc | skipH H ]
  | H : bytes_at asegs mc _ _ |- _ => first [ eapply bytes_at_transport in H; [| exact MUc| cbn [disjoint_from length]; rewrite ?repeat_length, ?length_le8, ?length_le4; lia] | skipH H ]
  | H : stk asegs mc _ _ |- _ => first [ eapply stk_transport in H; [| exact MUc| exact WMc| intros; left; cbn; lia] | skipH H ]
  | H : wr_at asegs mc _ _ |- _ => first [ eapply wr_at_transport in H; [| exact WMc] | skipH H ]
  | H : u8arr asegs mc _ _ |- _ => first [ eapply u8arr_transport in H; [| exact MUc| exact WMc| cbn [disjoint_from length]; rewrite ?repeat_length; lia] | skipH H ]
  | H : u64arr asegs mc _ _ |- _ => first [ eapply u64arr_transport in H; [| exact MUc| exact WMc| cbn [disjoint_from length]; lia] | skipH H ]
  | H : u32arr asegs mc _ _ |- _ => first [ eapply u32arr_transport in H; [| exact MUc| exact WMc| cbn [disjoint_from length]; lia] | skipH H ]
  | H : munch ?W ?ma mc |- _ =>
      let H2 := fresh in
      first [ assert (H2 : munch W ma m')
          by (eapply munch_trans; [exact H| eapply munch_weaken; [| exact MUc];
              first [ sub_fp_fast | let xq := fresh "xq" in let Hq := fresh "Hq" in intros xq Hq; cbn in Hq |- *; decompose [and] Hq; clear Hq; repeat match goal with |- _ /\ _ => split end; try exact I; match goal with O : ~ (_ <= xq < _)%Z |- _ => clear -O; let R := fresh in intros R; apply O; lia end ]]);
        clear H; rename H2 into H | skipH H ]
  | H : wmono asegs ?ma mc |- _ =>
      let H2 := fresh in
      assert (H2 : wmono asegs ma m') by (eapply wmono_trans; [exact H| exact WMc]);
      clear H; rename H2 into H
  end;
  repeat match goal with H : carry_skip _ |- _ => unfold carry_skip in H end.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma size_lo_ok : forall c, 1 <= c <= 16 -> Z.shiftl c 5 = class_size c.
Proof. aceil. intros c Hc. rewrite Z.shiftl_mul_pow2 by lia. unfold class_size, kMidClass, kMinSize. replace (c <=? 16) with true by (symmetry; apply Z.leb_le; lia). lia. Qed.
Lemma size_hi_ok : forall c, 17 <= c <= 30 ->
  Z.land (Z.shiftr (bv_signed (Z_to_bv 64 (Z.shiftl c 63))) 63 mod 18446744073709551616) (Z.shiftr ((Z.shiftl 512 (Z.shiftr (c + -16) 1 mod 64)) mod 18446744073709551616) 1)
  + Z.shiftl 512 (Z.shiftr (c + -16) 1 mod 64) = class_size c.
Proof. aceil.
  intros c Hc. assert (IN : In c (zrange 17 30)) by (apply In_zrange; lia). cbn in IN.
  repeat (destruct IN as [<-|IN]; [vm_compute; reflexivity|]). contradiction.
Qed.
Lemma v_divuw_small : forall x y, 0 <= x < 2^64 -> 0 < y < 2^31 -> (x mod 2^32) / y < 2^31 ->
  v_divuw (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 ((x mod 2^32) / y).
Proof. aceil.
  intros x y Hx Hy Hq. unfold v_divuw. rewrite !unsigned_lit by lia.
  change (bv_wrap 32 y) with (y mod 2^32). change (bv_wrap 32 x) with (x mod 2^32). rewrite (Z.mod_small y) by lia.
  replace (y =? 0) with false by (symmetry; apply Z.eqb_neq; lia). f_equal.
  change (bv_swrap 32 ?q) with ((q + 2^31) mod 2^32 - 2^31).
  pose proof (Z.div_pos (x mod 2^32) y ltac:(Z.div_mod_to_equations; lia) ltac:(lia)). rewrite Z.mod_small by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma land_mul256_small : forall k c, 0 <= k -> 0 <= c < 4 -> Z.land (256 * k) c = 0.
Proof. aceil.
  intros k c Hk Hc. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases i 2).
  - replace (256 * k) with (Z.shiftl (64 * k) 2) by (rewrite Z.shiftl_mul_pow2 by lia; lia). rewrite Z.shiftl_spec_low by lia. reflexivity.
  - rewrite (Z.bits_above_log2 c i); [apply andb_false_r| lia|].
    destruct (Z.eq_dec c 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; [lia|]. apply (Z.lt_le_trans _ (2^2)); [lia|]. apply Z.pow_le_mono_r; lia.
Qed.
Lemma hdr_cas_val3 : forall k, 0 <= k -> Z.lxor (3 + 256 * k) (Z.land (Z.lxor (3 + 256 * k) 0) 255) = 256 * k.
Proof. aceil.
  intros k Hk. rewrite Z.lxor_0_r.
  replace (Z.land (3 + 256 * k) 255) with 3 by (change 255 with (Z.ones 8); rewrite Z.land_ones by lia; change (2^8) with 256; Z.div_mod_to_equations; lia).
  assert (E3 : 256 * k + 3 = Z.lxor (256 * k) 3) by (apply Z.add_nocarry_lxor; apply land_mul256_small; lia).
  replace (3 + 256 * k) with (256 * k + 3) by lia. rewrite E3, Z.lxor_assoc. change (Z.lxor 3 3) with 0. apply Z.lxor_0_r.
Qed.

Section QCBR.
Variable P : acc -> Prop.
Variables (ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variable Q : machine_state -> Prop.
Variables (usp lo : Z) (CBP cb SB RI c idx mu ab : Z) (b1 nhi nlo : Z) (aidw cachep stackp : word).
Notation INST := 0xaa518.
Definition off : Z := cb - SB.
Definition hk : Z := b1 + 256 * nhi.
Definition n : Z := nhi * 2^32 + nlo.

Hypothesis LOC : alloc_ceiling <= lo.
Hypothesis LO : lo <= usp - 160.
Hypothesis SPH : usp <= 2^47.
Hypothesis SPA : usp mod 16 = 0.
Hypothesis HSB : 0x603000 <= SB /\ SB mod 4096 = 0 /\ SB + kSpaceSize + 4096 <= alloc_ceiling.
Hypothesis HRI : RI = SB + kSpaceSize.
Hypothesis HCB : SB <= cb /\ cb + 24 <= SB + kSpaceSize /\ cb mod 16 = 0.
Hypothesis HC : 1 <= c <= kLargestClassID /\ off / 2^32 = c.
Hypothesis HIDX : idx = (off mod 2^32) / class_size c.
Hypothesis HMU : (idx + 1) * class_size c <= mu /\ 0 <= mu <= 0xE0000000.
Hypothesis HAB : ab = SB + c * 2^32 + idx * class_size c /\ ab <= cb.
Hypothesis HB1 : 0 <= b1 < 256.
Hypothesis HNHI : 0 <= nhi < 256.
Hypothesis HNLO : 0 <= nlo < 2^32.
Hypothesis PSTK : forall a k, lo <= a -> a + Z.of_nat k <= usp -> P (Z_to_bv 64 a, k).
Hypothesis PDAT : forall a k, 0xa4000 <= a -> a + Z.of_nat k <= 0x603000 -> P (Z_to_bv 64 a, k).
Hypothesis PRO : forall a k, 0x10000 <= a -> a + Z.of_nat k <= 0x31000 -> P (Z_to_bv 64 a, k).
Hypothesis PCH : forall a k, cb <= a -> a + Z.of_nat k <= cb + 24 -> P (Z_to_bv 64 a, k).
Hypothesis PAB : forall a k, ab <= a -> a + Z.of_nat k <= ab + 16 -> P (Z_to_bv 64 a, k).
Hypothesis PRIR : forall a k, RI + 128 * c <= a -> a + Z.of_nat k <= RI + 128 * c + 128 -> P (Z_to_bv 64 a, k).

(* [comment removed for export] *)
Lemma qcbr_A : forall mx,
  mem_inv asegs mx -> stk asegs mx lo usp ->
  rw_cells asegs mx 0xaa538 [C8 (Z_to_bv 64 SB); C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 RI)] ->
  rw_cells asegs mx (RI + 128 * c + 48) [C8 (Z_to_bv 64 mu)] ->
  (forall m' (a2' a3' a4' a5' a6' a7' : word),
     mem_inv asegs m' -> stk asegs m' lo (usp + -48) -> munch [(usp + -48, usp)] mx m' -> wmono asegs mx m' ->
     rw_cells asegs m' (usp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
     rw_cells asegs m' 0xaa538 [C8 (Z_to_bv 64 SB); C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 RI)] ->
     rw_cells asegs m' (RI + 128 * c + 48) [C8 (Z_to_bv 64 mu)] ->
     evtA asegs P Q (MS (mkR ra (Z_to_bv 64 (usp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 CBP) (Z_to_bv 64 cb) (Z_to_bv 64 SB) (Z_to_bv 64 (SB + 2^37)) a2' a3' a4' a5' a6' a7'
                             (Z_to_bv 64 ab) (Z_to_bv 64 INST) (Z_to_bv 64 (2^37)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x34f44) fc None m' (seg_rom asegs))) ->
  evtA asegs P Q (MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 CBP) (Z_to_bv 64 cb) a2 a3 a4 a5 a6 a7
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x34e58) fc None mx (seg_rom asegs)).
Proof. aceil.
  intros mx MI SK INS RIM CONT.
  pose proof LOC as LOC0. aceil. unfold kSpaceSize in HSB, HCB, HRI. unfold kLargestClassID in HC.
  pose proof (class_size_mod c ltac:(lia)) as [CSM CSR].
  assert (MU : munch [(usp + -48, usp)] mx mx) by apply munch_refl.
  assert (WM : wmono asegs mx mx) by apply wmono_refl.
  rewrite <- (Z_to_bv_bv_unsigned' (Z_to_bv 64 usp)) in SK |- * || idtac.
  carve_frame 48%nat SK.
  frame_stores 7 FR. (* [comment removed for export] *)
  do 2 zstepA. (* [comment removed for export] *)
  do 2 zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  do 2 zstepA. (* [comment removed for export] *)
  zstepA. if_cases K1; zify_cond K1. { exfalso. revert K1. rewrite ?unsigned_lit by lia. lia. } clear K1. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. if_cases K2; zify_cond K2. { exfalso. revert K2. rewrite ?unsigned_lit by lia. lia. } clear K2. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  assert (EC1 : Z.shiftr (cb - SB) 32 = c) by (rewrite Z.shiftr_div_pow2 by lia; fold off; lia).
  assert (EC2 : Z.land (Z.shiftr (cb - SB) 32) 31 = c) by (rewrite EC1; change 31 with (Z.ones 5); rewrite Z.land_ones by lia; apply Z.mod_small; lia).
  rewrite EC2, EC1.
  zstepA. if_cases K3; zify_cond K3. { exfalso. revert K3. rewrite ?unsigned_lit by lia. lia. } clear K3. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m9 end.
  (* [comment removed for export] *)
  set (MID := fun ms1 => exists (a6' a7' : word), ms1 = MS (mkR ra (Z_to_bv 64 (usp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 CBP) (Z_to_bv 64 cb) (Z_to_bv 64 SB) (Z_to_bv 64 (SB + 137438953472)) (Z_to_bv 64 c) (Z_to_bv 64 c) (Z_to_bv 64 (cb - SB)) (Z_to_bv 64 (class_size c)) a6' a7'
                                  s2 (Z_to_bv 64 697624) (Z_to_bv 64 137438953472) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x34f08) fc None m9 (seg_rom asegs)).
  assert (KMID : forall ms1, MID ms1 -> evtA asegs P Q ms1).
  { intros ms1 (a6' & a7' & ->).
    zstepA. (* [comment removed for export] *)
    rewrite (v_divuw_small (cb - SB) (class_size c)); [| lia| lia| clear -CEILB CSR HCB; Z.div_mod_to_equations; nia].
    rewrite <- HIDX || (unfold off in HIDX; rewrite <- HIDX) || idtac "HIDX".
    zstepA. (* [comment removed for export] *)
    zstepA. (* [comment removed for export] *)
    zstepA. (* [comment removed for export] *)
    zstepA. (* [comment removed for export] *)
    zstepA. (* [comment removed for export] *)
    zstepA. (* [comment removed for export] *)
    replace (Z_to_bv 64 (RI + Z.shiftl c 7)) with (Z_to_bv 64 (RI + 128 * c)) by (f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
    zstepA. (* [comment removed for export] *)
    zstepA. (* [comment removed for export] *)
    zstepA. (* [comment removed for export] *)
    zstepA. (* [comment removed for export] *)
    zstepA. (* [comment removed for export] *)
    zstepA. (* [comment removed for export] *)
    zstepA. (* [comment removed for export] *)
    zstepA. (* [comment removed for export] *)
    assert (HIDXR : 0 <= idx < 2^27) by (rewrite HIDX; split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; [lia|]; clear -CEILB CSR; Z.div_mod_to_equations; nia]).
    replace (idx mod 4294967296) with idx in * by (symmetry; apply Z.mod_small; lia).
    replace (mu <? class_size c * idx + class_size c) with false in * by (symmetry; apply Z.ltb_ge; lia).
    cbn [Z.b2z]. change ((0 + -1) mod 18446744073709551616) with (Z.ones 64).
    rewrite Z.land_comm, Z.land_ones by lia.
    replace (((Z.shiftl c 32 + SB + class_size c * idx) mod 18446744073709551616) mod 2 ^ 64) with ab.
    2:{ rewrite Z.shiftl_mul_pow2 by lia. change (2^64) with 18446744073709551616. rewrite Z.mod_mod by lia. rewrite Z.mod_small; [lia|]. clear -CEILB HAB HCB HSB HC HIDXR CSR HMU. nia. }
    eapply CONT; [exact MI| exact SK| exact MU| exact WM| exact FR| exact INS| exact RIM].
  }
  zstepA. if_cases K4; zify_cond K4.
  - (* [comment removed for export] *)
    eapply (evtA_cut asegs P MID); [| exact KMID].
    do 9 zstepA. (* [comment removed for export] *)
    rewrite (size_hi_ok c) by (revert K4; rewrite ?unsigned_lit by lia; intros K4; lia).
    apply evtA_done. do 2 eexists. reflexivity.
  - (* [comment removed for export] *)
    eapply (evtA_cut asegs P MID); [| exact KMID].
    zstepA. if_cases K5; zify_cond K5. { exfalso. revert K5. rewrite ?unsigned_lit by lia. lia. } clear K5. (* [comment removed for export] *)
    zstepA. (* [comment removed for export] *)
    zstepA. (* [comment removed for export] *)
    rewrite (size_lo_ok c) by (revert K4; rewrite ?unsigned_lit by lia; intros K4; lia).
    apply evtA_done. do 2 eexists. reflexivity.
Qed.

Definition l8 : Z := (n + 7) / 8.                  (* [comment removed for export] *)
Hypothesis HSBH : kHighMemBeg + 8 <= SB.
Hypothesis HN : cb + 16 + n <= SB + kSpaceSize.

(* [comment removed for export] *)
Lemma qcbr_B : forall mx (g : Z) (a2x a3x a4x a5x a6x a7x mw : word) (shj : list byte),
  8 * g = cb + 16 ->
  mem_inv asegs mx -> stk asegs mx lo (usp + -48) ->
  rw_cells asegs mx cb [C4 (Z_to_bv 64 (3 + 256 * hk)); C4 (Z_to_bv 64 nlo); C8 aidw] ->
  (ab <> cb -> rw_cells asegs mx ab [C8 (Z_to_bv 64 kAllocBegMagicVal); C8 mw]) ->
  rw_cells asegs mx (0x7fff8000 + g) [CB (Z.to_nat l8) shj] ->
  poison_globals mx ->
  (forall a k, 0x7fff8000 + g <= a -> a + Z.of_nat k <= 0x7fff8000 + g + l8 -> P (Z_to_bv 64 a, k)) ->
  (forall m' (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
     mem_inv asegs m' -> stk asegs m' lo (usp + -48) -> munch [(usp + -112, usp + -48); (cb, cb + 4); (ab, ab + 8); (0x7fff8000 + g, 0x7fff8000 + g + l8)] mx m' -> wmono asegs mx m' ->
     rw_cells asegs m' cb [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 nhi); C4 (Z_to_bv 64 nlo); C8 aidw] ->
     (ab <> cb -> rw_cells asegs m' ab [C8 (Z_to_bv 64 0); C8 mw]) ->
     rw_cells asegs m' (0x7fff8000 + g) [CB (Z.to_nat l8) (repeat (Z_to_bv 8 0xfa) (Z.to_nat l8))] ->
     poison_globals m' ->
     evtA asegs P Q (MS (mkR (Z_to_bv 64 0x34fc4) (Z_to_bv 64 (usp + -48)) gp tp t0' t1' t2' (Z_to_bv 64 CBP) (Z_to_bv 64 cb) a0' a1' a2' a3' a4' a5' a6' a7'
                             (Z_to_bv 64 ab) (Z_to_bv 64 INST) (Z_to_bv 64 (2^37)) s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x34fc4) fc None m' (seg_rom asegs))) ->
  evtA asegs P Q (MS (mkR ra (Z_to_bv 64 (usp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 CBP) (Z_to_bv 64 cb) (Z_to_bv 64 SB) (Z_to_bv 64 (SB + 2^37)) a2x a3x a4x a5x a6x a7x
                          (Z_to_bv 64 ab) (Z_to_bv 64 INST) (Z_to_bv 64 (2^37)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x34f44) fc None mx (seg_rom asegs)).
Proof. aceil.
  intros mx g a2x a3x a4x a5x a6x a7x mw shj Hg8 MI SK HDR MAG SH PG PSH CONT.
  pose proof LOC as LOC0. aceil. unfold kSpaceSize in HSB, HCB, HRI. unfold kLargestClassID in HC.
  rewrite kHighMemBeg_val in HSBH.
  pose proof (class_size_mod c ltac:(lia)) as [CSM CSR].
  assert (HIDXR : 0 <= idx) by (rewrite HIDX; apply Z.div_pos; lia).
  assert (HKR : 0 <= hk < 2^16) by (unfold hk; lia).
  assert (HAB8 : ab mod 16 = 0) by (destruct HAB as [E _]; rewrite E; clear -CEILB HSB CSM HIDXR HC; Z.div_mod_to_equations; nia).
  pose proof HMU as HMU_dep.   (* [comment removed for export] *)
  hideH HIDX. hideH HMU. hideH HMU_dep.   (* [comment removed for export] *)
  assert (Hn0 : 0 <= n < 2^40) by (unfold n; lia).
  assert (SHR : 0 <= l8 /\ 8 * l8 <= n + 7 /\ 0x7fff8000 + g + l8 <= 17594333495296) by (unfold l8; unfold kSpaceSize in HN; clear -CEILB HN Hg8 Hn0 HSB HCB; Z.div_mod_to_equations; lia).
  assert (MU : munch [(usp + -112, usp + -48); (cb, cb + 4); (ab, ab + 8); (0x7fff8000 + g, 0x7fff8000 + g + l8)] mx mx) by apply munch_refl.
  assert (WM : wmono asegs mx mx) by apply wmono_refl.
  zstepA. if_cases K1; zify_cond K1. { exfalso. revert K1. rewrite ?unsigned_lit by lia. lia. } clear K1. (* [comment removed for export] *)
  zstepA. if_cases K2; zify_cond K2. { exfalso. revert K2. rewrite ?unsigned_lit by lia. lia. } clear K2. (* [comment removed for export] *)
  (* [comment removed for export] *)
  assert (REST : forall m1 (a0x a3x' a4x' : word),
    mem_inv asegs m1 -> stk asegs m1 lo (usp + -48) -> munch [(usp + -112, usp + -48); (cb, cb + 4); (ab, ab + 8); (0x7fff8000 + g, 0x7fff8000 + g + l8)] mx m1 -> wmono asegs mx m1 ->
    rw_cells asegs m1 cb [C4 (Z_to_bv 64 (3 + 256 * hk)); C4 (Z_to_bv 64 nlo); C8 aidw] ->
    (ab <> cb -> rw_cells asegs m1 ab [C8 (Z_to_bv 64 0); C8 mw]) ->
    rw_cells asegs m1 (0x7fff8000 + g) [CB (Z.to_nat l8) shj] -> poison_globals m1 ->
    evtA asegs P Q (MS (mkR ra (Z_to_bv 64 (usp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 CBP) (Z_to_bv 64 cb) a0x (Z_to_bv 64 (SB + 137438953472)) a2x a3x' a4x' a5x a6x a7x
                            (Z_to_bv 64 ab) (Z_to_bv 64 697624) (Z_to_bv 64 137438953472) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x34f68) fc None m1 (seg_rom asegs))).
  { clear MI SK MU WM HDR MAG SH PG. intros m1 a0x a3x' a4x' MI SK MU WM HDR MAG SH PG.
    destruct PG as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
    (* [comment removed for export] *)
    destruct (Z.eq_dec ab cb) as [EQab|NEab]; [clear MAG| specialize (MAG NEab)].
    all: do 6 zstepA. (* [comment removed for export] *)
    all: replace (Z.land cb 18446744073709551612) with cb by (change 18446744073709551612 with (2^64 - 2^2); rewrite land_align_down by lia; change (2^2) with 4; Z.div_mod_to_equations; lia).
    all: replace ((Z.shiftl cb 3 mod 18446744073709551616) mod 32) with 0 by (rewrite Z.shiftl_mul_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia).
    all: change (bv_swrap 32 (Z.shiftl 255 0)) with 255; change (bv_swrap 32 (Z.shiftl 3 0)) with 3.
    all: zstepA. (* [comment removed for export] *)
    all: rewrite (fsx32_small' (3 + 256 * hk)) by lia.
    all: zstepA. (* [comment removed for export] *)
    all: replace (Z.land (3 + 256 * hk) 255) with 3 by (change 255 with (Z.ones 8); rewrite Z.land_ones by lia; change (2^8) with 256; Z.div_mod_to_equations; lia).
    all: cstep. (* [comment removed for export] *)
    all: do 3 zstepA. (* [comment removed for export] *)
    all: rewrite (hdr_cas_val3 hk) by lia.
    all: zstepA. (* [comment removed for export] *)
    all: cstep. (* [comment removed for export] *)
    (* [comment removed for export] *)
    all: match goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mc _) =>
      assert (HDRB : rw_cells asegs mc cb [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 nhi); C4 (Z_to_bv 64 nlo); C8 aidw]);
      [ eapply rw_cells_reshape; [| | exact HDR]; [cells_wf_triv|];
        cbn [cells_bytes cbytes map app]; unfold le4, le2; rewrite !Z_to_bv_unsigned; cbn [Z_to_le_bytes map app];
        rewrite !Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 8) with 256; change (bv_modulus 64) with (2^64);
        unfold hk; rewrite !Z.shiftr_div_pow2 by lia; change (2^8) with 256; rewrite ?app_nil_r;
        rewrite !(Z.mod_small _ (2^64)) by lia;
        repeat (apply f_equal2; [clear -HB1 HNHI; Z.div_mod_to_equations; lia|]); reflexivity
      | clear HDR ] end.
    all: zstepA. (* [comment removed for export] *)
    all: rewrite fzx16_small by lia.
    all: zstepA. (* [comment removed for export] *)
    all: rewrite fzx32_small' by lia.
    all: zstepA. (* [comment removed for export] *)
    all: zstepA; zstepA. (* [comment removed for export] *)
    all: replace (Z.shiftl nhi 32 mod 18446744073709551616) with (Z.shiftl nhi 32) by (symmetry; apply Z.mod_small; rewrite Z.shiftl_mul_pow2 by lia; lia).
    all: rewrite (lor_shiftl nhi nlo 32) by lia.
    all: fold n.
    all: zstepA; zstepA. (* [comment removed for export] *)
    all: replace ((n + 7) mod 18446744073709551616) with (n + 7) by (symmetry; apply Z.mod_small; lia).
    all: replace (Z.land (n + 7) 18446744073709551608) with (8 * l8) by (change 18446744073709551608 with (2^64 - 2^3); rewrite land_align_down by lia; unfold l8; change (2^3) with 8; clear -CEILB Hn0; Z.div_mod_to_equations; lia).
    all: zstepA. (* [comment removed for export] *)
    all: zstepA. (* [comment removed for export] *)
    all: eapply evtA_cut;
      [ eapply (poison_walk P _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo (cb + 16) (8 * l8) 250 shj);
        (* [comment removed for export] *)
        [rewrite unsigned_lit by (clear -LO LOC0 CEILB SPH; lia); exact SK| exact LOC0| rewrite unsigned_lit by (clear -LO LOC0 CEILB SPH; lia); clear -LO LOC0 CEILB SPH; lia
        | rewrite unsigned_lit by (clear -LO LOC0 CEILB SPH; lia); clear -LO LOC0 CEILB SPH; lia| eassumption| exact (conj G1 (conj G2 (conj G3 (conj G4 (conj G5 (conj G6 G7))))))
        | clear -CEILB HCB; Z.div_mod_to_equations; lia| clear -CEILB SHR; lia| clear -SHR; lia| clear -HCB HSB; lia| unfold kSpaceSize in HN; aceil; clear -HN HCB HSB SHR CEILB; lia
        | right; rewrite kHighMemBeg_val; split; [clear -HCB HSB HSBH; lia| left; clear -HCB HSB HSBH; lia]| clear; lia| left; clear; lia
        | replace ((cb + 16) / 8) with g by (clear -Hg8; lia); replace (8 * l8 / 8) with l8 by (clear; lia); exact SH
        | rewrite unsigned_lit by (clear -LO LOC0 CEILB SPH; lia); intros; apply PSTK; LiaA.lia_probe| exact PDAT
        | replace ((cb + 16) / 8) with g by (clear -Hg8; lia); replace (8 * l8 / 8) with l8 by (clear; lia); unfold kShadowBase; exact PSH]
      |].
    all: clear G1 G2 G3 G4 G5 G6 G7 SH.
    all: cbv beta; intros ms' POST; unfold poison_post in POST; destruct POST as (t0' & t1' & t2' & a0' & a1' & a2'' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MUc & WMc & MI' & SK' & SH' & PG').
    all: unfold kShadowBase in MUc, SH'; rewrite !unsigned_lit in MUc, SK' by (clear -LO LOC0 CEILB SPH; lia); replace ((cb + 16) / 8) with g in MUc, SH' by (clear -Hg8; lia); replace (8 * l8 / 8) with l8 in MUc, SH' by (clear; lia).
    all: clear MI SK; lazymatch type of MUc with munch _ ?mc _ => after_call mc m' MUc WMc end; ret_pc_lit.
    all: eapply CONT; [exact MI'| exact SK'| exact MU| exact WM| exact HDRB| first [intros _; exact MAG | intros NE'; exfalso; exact (NE' EQab)]| | exact PG'].
    all: rewrite Nat2Z.id in SH' || idtac.
    all: exact SH' || (revert SH'; rewrite ?Z2Nat.id by lia; intros SH'; exact SH'). }
  zstepA. if_cases K3; zify_cond K3.
  - (* [comment removed for export] *)
    eapply REST; [exact MI| exact SK| exact MU| exact WM| exact HDR| intros NE; exfalso; apply NE; revert K3; rewrite ?unsigned_lit by lia; intros K3; lia| exact SH| exact PG].
  - assert (NE : ab <> cb) by (intros E; apply K3; rewrite E; reflexivity).
    specialize (MAG NE).
    zstepA. zstepA. (* [comment removed for export] *)
    zstepA. (* [comment removed for export] *)
    cstep. (* [comment removed for export] *)
    zstepA. (* [comment removed for export] *)
    cstep. (* [comment removed for export] *)
    eapply REST; [exact MI| exact SK| exact MU| exact WM| exact HDR| intros _; exact MAG| exact SH| ].
    eapply poison_globals_agree; [exact PG|]. intros a Ha. apply MU. unfold wa. rewrite unsigned_lit by lia. cbn. repeat match goal with |- _ /\ _ => split end; first [exact I | dlia1].
Qed.

Lemma class_recompute : forall r, 0 <= r < 2^32 -> Z.shiftr (Z.shiftl (c * 2^32 + r) 27 mod 18446744073709551616) 59 = c.
Proof. aceil.
  intros r Hr. unfold kLargestClassID in HC. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  rewrite Z.mod_small by (clear -CEILB Hr HC; nia). clear -CEILB Hr HC. Z.div_mod_to_equations. nia.
Qed.

(* [comment removed for export] *)
Lemma qcbr_C : forall mx (rax t0x t1x t2x a0x a1x a2x a3x a4x a5x a6x a7x t3x t4x t5x t6x : word) (TSD CTX T rf rfd : Z),
  mem_inv asegs mx -> stk asegs mx lo (usp + -48) ->
  rw_cells asegs mx (usp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells asegs mx 0xaa538 [C8 (Z_to_bv 64 SB); C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 RI)] ->
  rw_cells asegs mx cb [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 nhi); C4 (Z_to_bv 64 nlo); C8 aidw] ->
  rw_cells asegs mx CBP [C8 cachep; C8 stackp] -> usp <= CBP -> CBP + 16 <= 2^47 ->
  thread_cells mx tp TSD CTX T -> 0x5cfdd0 <= TSD -> TSD + 8 <= 0x603000 -> placed_s CTX 4096 -> placed_s T 4096 ->   (* [comment removed for export] *)
  0x5cfdd0 + 88 <= bv_unsigned tp < 0x603000 -> (CTX + 160 <= T \/ T + 4096 <= CTX) ->
  (T + 4096 <= SB \/ SB + kSpaceSize + 4096 <= T) -> (CTX + 4096 <= SB \/ SB + kSpaceSize + 4096 <= CTX) ->
  rw_cells asegs mx (T + 2840) [C8 (Z_to_bv 64 rf); C8 (Z_to_bv 64 rfd)] -> 0 <= rf < 2^64 -> 0 <= rfd < 2^64 ->
  P (Z_to_bv 64 (CTX + 152), 8%nat) -> (forall a k, T <= a -> a + Z.of_nat k <= T + 4096 -> P (Z_to_bv 64 a, k)) ->
  (forall a k, CBP <= a -> a + Z.of_nat k <= CBP + 16 -> P (Z_to_bv 64 a, k)) ->
  (forall m' (t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' : word),
     mem_inv asegs m' -> stk asegs m' lo usp -> munch [(usp + -80, usp); (T + 2840, T + 2856)] mx m' -> wmono asegs mx m' ->
     rw_cells asegs m' (T + 2840) [C8 (Z_to_bv 64 (rf + 1)); C8 (Z_to_bv 64 (n + rfd))] ->
     thread_cells m' tp TSD CTX T ->
     evtA asegs P Q (MS (mkR ra (Z_to_bv 64 usp) gp tp t0' t1' t2' s0 s1 cachep (Z_to_bv 64 INST) (Z_to_bv 64 c) (Z_to_bv 64 ab) a4' a5' a6' a7'
                             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x3525c) fc None m' (seg_rom asegs))) ->
  evtA asegs P Q (MS (mkR rax (Z_to_bv 64 (usp + -48)) gp tp t0x t1x t2x (Z_to_bv 64 CBP) (Z_to_bv 64 cb) a0x a1x a2x a3x a4x a5x a6x a7x
                          (Z_to_bv 64 ab) (Z_to_bv 64 INST) (Z_to_bv 64 (2^37)) s5 s6 s7 s8 s9 s10 s11 t3x t4x t5x t6x) F (Z_to_bv 64 0x34fc4) fc None mx (seg_rom asegs)).
Proof. aceil.
  intros mx rax t0x t1x t2x a0x a1x a2x a3x a4x a5x a6x a7x t3x t4x t5x t6x TSD CTX T rf rfd MI SK FR INS HDRB CBC HCB1 HCB2 TC HT1 HT2 HCp HTp HTP HTC HTSB HCSB TST HRF HRFD PCTX PT PCBP CONT.
  (* [comment removed for export] *)
  pose proof HCp as (HC1 & HC2 & _). pose proof HTp as (HT3 & HT4 & _).
  unfold kSpaceSize in HTSB, HCSB.
  pose proof LOC as LOC0. aceil. unfold kSpaceSize in HSB, HCB, HRI, HN. unfold kLargestClassID in HC.
  pose proof (class_size_mod c ltac:(lia)) as [CSM CSR].
  assert (HIDXR : 0 <= idx) by (rewrite HIDX; apply Z.div_pos; lia).
  hideH HIDX.   (* [comment removed for export] *)
  pose proof SPA as SPA_dep. pose proof HN as HN_dep.   (* [comment removed for export] *)
  assert (Hn0 : 0 <= n < 2^40) by (unfold n; lia).
  destruct TC as (TC1 & TC2 & TC3 & TC4 & TC5).
  assert (MU : munch [(usp + -80, usp); (T + 2840, T + 2856)] mx mx) by apply munch_refl.
  assert (WM : wmono asegs mx mx) by apply wmono_refl.
  zstepA. (* [comment removed for export] *)
  eapply evtA_cut.
  { eapply (gcts_walk P _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo TSD CTX T);
      [rewrite unsigned_lit by lia; exact SK| exact LOC0| rewrite unsigned_lit by lia; lia| rewrite unsigned_lit by lia; lia| exact MI
      | exact (conj TC1 (conj TC2 (conj TC3 (conj TC4 TC5))))| lia| exact HT2| lia| aceil; lia| lia| lia
      | rewrite unsigned_lit by lia; intros; apply PSTK; lia| exact PDAT| exact PCTX]. }
  cbv beta. intros ms' POST. unfold gcts_post in POST. destruct POST as (a1' & m' & -> & MUc & WMc & MI' & SK').
  rewrite !unsigned_lit in MUc, SK' by lia.
  clear MI SK. lazymatch type of MUc with munch _ ?mc _ => after_call mc m' MUc WMc end. ret_pc_lit.
  zstepA. (* [comment removed for export] *) rewrite fzx16_small by lia.
  zstepA. (* [comment removed for export] *) rewrite fzx32_small' by lia.
  zstepA. zstepA. (* [comment removed for export] *)
  zstepA. zstepA. (* [comment removed for export] *)
  replace (Z.shiftl nhi 32 mod 18446744073709551616) with (Z.shiftl nhi 32) by (symmetry; apply Z.mod_small; rewrite Z.shiftl_mul_pow2 by lia; lia).
  rewrite (lor_shiftl nhi nlo 32) by lia. fold n.
  zstepA. zstepA. (* [comment removed for export] *)
  pose proof HTp as (_ & _ & HTg & _). unfold A_IMG_END in HTg.
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  clear HTg.
  zstepA. if_cases K1; zify_cond K1. { exfalso. revert K1. rewrite ?unsigned_lit by lia. lia. } clear K1. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. if_cases K2; zify_cond K2. { exfalso. revert K2. rewrite ?unsigned_lit by lia. lia. } clear K2. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. if_cases K3; zify_cond K3. { exfalso. revert K3. rewrite ?unsigned_lit by lia. lia. } clear K3. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. zstepA. zstepA. (* [comment removed for export] *)
  replace (ab - SB) with (c * 2^32 + idx * class_size c) by lia.
  rewrite (class_recompute (idx * class_size c)) by (clear -CEILB HMU HIDXR CSR; nia).
  zstepA. zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  do 7 zstepA. (* [comment removed for export] *)
  release_frame FR SK' usp.
  zstepA. (* [comment removed for export] *)
  match goal with H : rw_cells asegs _ (T + 2840) _ |- _ => rename H into TST' end.
  eapply CONT; [exact MI'| exact SK'| exact MU| exact WM| exact TST'| exact (conj TC1 (conj TC2 (conj TC3 (conj TC4 TC5))))].
Qed.

(* [comment removed for export] *)
Lemma qcbr_prim_walk : forall mx (g : Z) (mw : word) (shj : list byte) (TSD CTX T rf rfd : Z),
  8 * g = cb + 16 ->
  mem_inv asegs mx -> stk asegs mx lo usp ->
  rw_cells asegs mx 0xaa538 [C8 (Z_to_bv 64 SB); C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 RI)] ->
  rw_cells asegs mx (RI + 128 * c + 48) [C8 (Z_to_bv 64 mu)] ->
  rw_cells asegs mx cb [C4 (Z_to_bv 64 (3 + 256 * hk)); C4 (Z_to_bv 64 nlo); C8 aidw] ->
  (ab <> cb -> rw_cells asegs mx ab [C8 (Z_to_bv 64 kAllocBegMagicVal); C8 mw]) ->
  rw_cells asegs mx (0x7fff8000 + g) [CB (Z.to_nat l8) shj] ->
  poison_globals mx ->
  rw_cells asegs mx CBP [C8 cachep; C8 stackp] -> usp <= CBP -> CBP + 16 <= 2^47 ->
  thread_cells mx tp TSD CTX T -> 0x5cfdd0 <= TSD -> TSD + 8 <= 0x603000 -> placed_s CTX 4096 -> placed_s T 4096 ->   (* [comment removed for export] *)
  0x5cfdd0 + 88 <= bv_unsigned tp < 0x603000 -> (CTX + 160 <= T \/ T + 4096 <= CTX) ->
  (T + 4096 <= SB \/ SB + kSpaceSize + 4096 <= T) -> (CTX + 4096 <= SB \/ SB + kSpaceSize + 4096 <= CTX) ->
  rw_cells asegs mx (T + 2840) [C8 (Z_to_bv 64 rf); C8 (Z_to_bv 64 rfd)] -> 0 <= rf < 2^64 -> 0 <= rfd < 2^64 ->
  (forall a k, 0x7fff8000 + g <= a -> a + Z.of_nat k <= 0x7fff8000 + g + l8 -> P (Z_to_bv 64 a, k)) ->
  P (Z_to_bv 64 (CTX + 152), 8%nat) -> (forall a k, T <= a -> a + Z.of_nat k <= T + 4096 -> P (Z_to_bv 64 a, k)) ->
  (forall a k, CBP <= a -> a + Z.of_nat k <= CBP + 16 -> P (Z_to_bv 64 a, k)) ->
  (forall m' (t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' : word),
     mem_inv asegs m' -> stk asegs m' lo usp ->
     munch [(usp + -112, usp); (cb, cb + 4); (ab, ab + 8); (0x7fff8000 + g, 0x7fff8000 + g + l8); (T + 2840, T + 2856)] mx m' -> wmono asegs mx m' ->
     rw_cells asegs m' 0xaa538 [C8 (Z_to_bv 64 SB); C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 RI)] ->
     rw_cells asegs m' (RI + 128 * c + 48) [C8 (Z_to_bv 64 mu)] ->
     rw_cells asegs m' cb [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 nhi); C4 (Z_to_bv 64 nlo); C8 aidw] ->
     (ab <> cb -> rw_cells asegs m' ab [C8 (Z_to_bv 64 0); C8 mw]) ->
     rw_cells asegs m' (0x7fff8000 + g) [CB (Z.to_nat l8) (repeat (Z_to_bv 8 0xfa) (Z.to_nat l8))] ->
     poison_globals m' ->
     rw_cells asegs m' CBP [C8 cachep; C8 stackp] ->
     thread_cells m' tp TSD CTX T ->
     rw_cells asegs m' (T + 2840) [C8 (Z_to_bv 64 (rf + 1)); C8 (Z_to_bv 64 (n + rfd))] ->
     evtA asegs P Q (MS (mkR ra (Z_to_bv 64 usp) gp tp t0' t1' t2' s0 s1 cachep (Z_to_bv 64 INST) (Z_to_bv 64 c) (Z_to_bv 64 ab) a4' a5' a6' a7'
                             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x3525c) fc None m' (seg_rom asegs))) ->
  evtA asegs P Q (MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 CBP) (Z_to_bv 64 cb) a2 a3 a4 a5 a6 a7
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x34e58) fc None mx (seg_rom asegs)).
Proof. aceil.
  intros mx g mw shj TSD CTX T rf rfd Hg8 MI SK INS RIM HDR MAG SH PG CBC HCB1 HCB2 TC HT1 HT2 HCp HTp HTP HTC HTSB HCSB TST HRF HRFD PSH PCTX PT PCBP CONT.
  pose proof HCp as (HC1 & HC2 & HCg & HCs). pose proof HTp as (HT3 & HT4 & HTg & HTs). unfold A_IMG_END in HCg, HTg. unfold A_LOWAPP_END, A_HIGH_BEG in HCs, HTs.
  pose proof HTSB as HTSB0. pose proof HCSB as HCSB0. unfold kSpaceSize in HTSB, HCSB.
  pose proof LOC as LOC0. pose proof HSB as HSB0. pose proof HCB as HCBx. pose proof HRI as HRI0. pose proof HC as HCx.
  aceil. unfold kSpaceSize in HSB, HCBx, HRI0. unfold kLargestClassID in HCx.
  pose proof HN as HN0. unfold kSpaceSize in HN0.
  pose proof (class_size_mod c ltac:(lia)) as [CSM CSR].
  assert (HIDXR : 0 <= idx) by (rewrite HIDX; apply Z.div_pos; lia).
  assert (Hn0 : 0 <= n < 2^40) by (unfold n; lia).
  assert (SHR : 0 <= l8 /\ 8 * l8 <= n + 7 /\ 0x7fff8000 + g + l8 <= 17594333495296) by (unfold l8; clear -CEILB HN0 Hg8 Hn0 HSB HCBx; Z.div_mod_to_equations; lia).
  rewrite kHighMemBeg_val in HSBH.
  destruct TC as (TC1 & TC2 & TC3 & TC4 & TC5).
  eapply qcbr_A; [exact MI| exact SK| exact INS| exact RIM|].
  clear MI SK INS RIM. intros m1 a2' a3' a4' a5' a6' a7' MI SK MU1 WM1 FR INS RIM.
  carry_all mx m1 MU1 WM1.
  assert (MAG1 : ab <> cb -> rw_cells asegs m1 ab [C8 (Z_to_bv 64 kAllocBegMagicVal); C8 mw]).
  { intros NE. specialize (MAG NE). carry_rw MAG MU1 WM1. exact MAG. }
  assert (PG1 : poison_globals m1) by (eapply poison_globals_agree; [exact PG|]; intros a Ha; apply MU1; unfold wa; rewrite unsigned_lit by lia; cbn; repeat match goal with |- _ /\ _ => split end; first [exact I | dlia1]).
  clear MAG PG.
  eapply (qcbr_B m1 g); [exact Hg8| exact MI| exact SK| exact HDR| exact MAG1| exact SH| exact PG1| exact PSH|].
  clear MI SK HDR MAG1 SH PG1. intros m2 t0' t1' t2' a0' a1' a2'' a3'' a4'' a5'' a6'' a7'' t3' t4' t5' t6' MI SK MU2 WM2 HDRB MAG SH PG.
  carry_all m1 m2 MU2 WM2.
  eapply (qcbr_C m2); [exact MI| exact SK| exact FR| exact INS| exact HDRB| exact CBC| exact HCB1| exact HCB2| exact (conj TC1 (conj TC2 (conj TC3 (conj TC4 TC5))))
    | exact HT1| exact HT2| exact HCp| exact HTp| exact HTP| exact HTC| exact HTSB0| exact HCSB0| exact TST| exact HRF| exact HRFD| exact PCTX| exact PT| exact PCBP|].
  clear MI SK FR TST. intros m3 t0'' t1'' t2'' a4x a5x a6x a7x t3'' t4'' t5'' t6'' MI SK MU3 WM3 TST TC.
  carry_all m2 m3 MU3 WM3.
  assert (MAG3 : ab <> cb -> rw_cells asegs m3 ab [C8 (Z_to_bv 64 0); C8 mw]).
  { intros NE. specialize (MAG NE). carry_rw MAG MU3 WM3. exact MAG. }
  assert (PG3 : poison_globals m3) by (eapply poison_globals_agree; [exact PG|]; intros a Ha; apply MU3; unfold wa; rewrite unsigned_lit by lia; cbn; repeat match goal with |- _ /\ _ => split end; first [exact I | dlia1]).
  eapply CONT; [exact MI| exact SK| | | exact INS| exact RIM| exact HDRB| exact MAG3| exact SH| exact PG3| exact CBC| exact TC| exact TST].
  - eapply munch_trans; [eapply munch_cover; [exact MU1| solve_covers]|]. eapply munch_trans; [eapply munch_cover; [exact MU2| solve_covers]|]. eapply munch_cover; [exact MU3| solve_covers].
  - first [exact WM1| eapply wmono_trans; [exact WM1|]; eapply wmono_trans; [exact WM2| exact WM3]].
Qed.
End QCBR.
End RC__1.
