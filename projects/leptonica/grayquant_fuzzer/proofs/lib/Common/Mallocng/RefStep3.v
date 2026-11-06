(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import decidable.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk MmapSim AllocSim ShapeAlg ShapeNodes
  PureModel VmLedger AllocIface AsanCeil AgentLib RefMemcpyLib.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocOps MallocShape RefLrSc RefStep RefStmts RefSys RefPieces.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Open Scope malloc_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Notation "'zpc+' base off" :=
  (ltac:(let v := eval vm_compute in (bv_unsigned base + off)%Z in exact (Z_to_bv 64 v)))
  (at level 10, base constr at level 9, off constr at level 9, only parsing).
Notation "'pc+' base off" :=
  (ltac:(let v := eval vm_compute in (bv_unsigned base + off)%Z in
         exact (@BV 64 v ltac:(vm_compute; exact I))))
  (at level 10, base constr at level 9, off constr at level 9, only parsing).

Section Gen.
Context {fx : FPState}.

(* [comment removed for export] *)
Lemma rz_msteps_p : forall segs ms ms' md T,
  md_pure md -> msteps segs ms ms' -> realizes segs (mkCfg ms' md) T -> realizes segs (mkCfg ms md) T.
Proof. intros segs ms ms' md T [Hh Hl Hm] Hms H. eapply rz_msteps; eassumption. Qed.

Lemma lor_shiftl_small : forall a y k, 0 <= k -> 0 <= a < 2^k -> 0 <= y ->
  Z.lor a (Z.shiftl y k) = a + y * 2^k.
Proof.
  intros a y k Hk Ha Hy.
  rewrite <- Z.shiftl_mul_pow2 by lia.
  pose proof (Z.add_lor_land a (Z.shiftl y k)) as H.
  assert (Hz : Z.land a (Z.shiftl y k) = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z_lt_dec i k) as [Hl|Hl].
    - rewrite Z.shiftl_spec_low by lia. apply andb_false_r.
    - rewrite (Z_testbit_high k a i) by lia. reflexivity. }
  lia.
Qed.

Lemma Z_to_le_bytes_to_Z : forall bs, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|].
  cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (u8_range b) as Hb. pose proof (bytes_le_to_Z_nonneg bs) as Hr.
  rewrite lor_shiftl_small by lia.
  f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with (2^8).
    rewrite Z_mod_plus_full. apply Z.mod_small. lia.
  - rewrite Z.shiftr_div_pow2 by lia.
    rewrite Z_div_plus_full by lia. rewrite Z.div_small by lia. rewrite Z.add_0_l. exact IH.
Qed.

Lemma w2l_le_val : forall bs : list byte, length bs = 8%nat -> word_to_le_bytes 8 (le_val bs) = bs.
Proof.
  intros bs Hlen. unfold word_to_le_bytes. rewrite <- (le_val_u bs) by (rewrite Hlen; lia).
  rewrite <- Hlen. apply Z_to_le_bytes_to_Z.
Qed.

Lemma b_cases : forall b : bool, b = true \/ b = false.
Proof. intros [|]; [left|right]; reflexivity. Qed.

Lemma c_eq_eq : forall a b : word, c_eq a b = true -> a = b.
Proof. intros a b H. unfold c_eq in H. apply bv_eqb_eq in H. exact H. Qed.

Lemma c_ltu_lt : forall a b : word, c_ltu a b = true -> bv_unsigned a < bv_unsigned b.
Proof. intros a b H. unfold c_ltu, bv_ltu in H. apply Z.ltb_lt in H. exact H. Qed.

Lemma acc_ok_cases : forall s (a : word) n, acc_ok s a n = true ->
  bv_unsigned a + n <= ms_lo s \/ (ms_hi s <= bv_unsigned a /\ bv_unsigned a + n <= 2^64).
Proof.
  intros s a n H. unfold acc_ok in H. apply Bool.orb_true_iff in H. destruct H as [H|H].
  - left. apply Z.leb_le in H. exact H.
  - right. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.
End Gen.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma u_Z64 : forall z, 0 <= z < 2^64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. apply Z_to_bv_small_unsigned. exact Hz. Qed.

Lemma is0_u : forall v : word, MallocOps.is0 v = (bv_unsigned v =? 0).
Proof. intros v. unfold MallocOps.is0, c_eq, bv_eqb, MallocOps.w0. rewrite u_Z64 by lia. reflexivity. Qed.

Lemma c_eq_u : forall a b : word, c_eq a b = (bv_unsigned a =? bv_unsigned b).
Proof. reflexivity. Qed.

Lemma c_ltu_u : forall a b : word, c_ltu a b = (bv_unsigned a <? bv_unsigned b).
Proof. reflexivity. Qed.

Lemma land_1 : forall z, 0 <= z -> Z.land z 1 = z mod 2.
Proof. intros z Hz. change 1 with (Z.ones 1). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma land2_half : forall z, 0 <= z -> Z.land (z / 2) 1 = Z.land z 2 / 2.
Proof.
  intros z Hz. change 2 with (2 ^ 1) at 1. change (Z.land z 2 / 2) with (Z.land z 2 / 2 ^ 1).
  rewrite <- !Z.shiftr_div_pow2 by lia.
  rewrite Z.shiftr_land. reflexivity.
Qed.

Lemma land2_even : forall z, Z.odd (Z.land z 2) = false.
Proof. intros z. rewrite <- Z.bit0_odd, Z.land_spec. change (Z.testbit 2 0) with false. apply andb_false_r. Qed.

Lemma is0_andi1 : forall x : word, MallocOps.is0 (v_andi x 1) = (Z.land (bv_unsigned x) 1 =? 0).
Proof.
  intros x. rewrite is0_u. unfold v_andi. pose proof (u64_range x).
  change (bv_wrap 64 1) with 1.
  pose proof (Z_land_range (bv_unsigned x) 1 ltac:(lia) ltac:(lia)).
  rewrite u_Z64 by lia. reflexivity.
Qed.

Lemma ceq0_andi2 : forall x : word, c_eq (v_andi x 2) (Z_to_bv 64 0) = (Z.land (bv_unsigned x) 2 =? 0).
Proof.
  intros x. rewrite c_eq_u. unfold v_andi. pose proof (u64_range x).
  change (bv_wrap 64 2) with 2.
  pose proof (Z_land_range (bv_unsigned x) 2 ltac:(lia) ltac:(lia)).
  rewrite !u_Z64 by lia. reflexivity.
Qed.

Lemma u_srliw1 : forall x : word, bv_unsigned x < 2^31 -> bv_unsigned (v_srliw x 1) = bv_unsigned x / 2.
Proof.
  intros x Hx. pose proof (u64_range x). unfold v_srliw.
  rewrite (bv_wrap_small 32) by (change (bv_modulus 32) with (2^32); lia).
  rewrite Z.shiftr_div_pow2 by lia. change (2^1) with 2.
  rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2^31); lia).
  apply u_Z64. lia.
Qed.

Lemma andi2_srliw : forall x : word, bv_unsigned x < 2^31 ->
  MallocOps.is0 (v_andi (v_srliw x 1) 1) = c_eq (v_andi x 2) (Z_to_bv 64 0).
Proof.
  intros x Hx. rewrite is0_andi1, ceq0_andi2, u_srliw1 by exact Hx.
  pose proof (u64_range x) as Hx0.
  rewrite land2_half by lia.
  pose proof (land2_even (bv_unsigned x)) as He.
  pose proof (Z_land_range (bv_unsigned x) 2 ltac:(lia) ltac:(lia)) as Hr.
  set (w := Z.land (bv_unsigned x) 2) in *.
  destruct (Z.eq_dec w 0) as [E|E]; [rewrite E; reflexivity|].
  assert (Hodd : w <> 1) by (intros E1; rewrite E1 in He; discriminate He).
  destruct (w / 2 =? 0) eqn:E2; destruct (w =? 0) eqn:E3; try reflexivity.
  - apply Z.eqb_eq in E2. apply Z.eqb_neq in E3. exfalso.
    pose proof (Z.div_mod w 2 ltac:(lia)). pose proof (Z.mod_pos_bound w 2 ltac:(lia)).
    assert (w = w mod 2) by lia.
    rewrite Zmod_odd in H1. rewrite He in H1. lia.
  - apply Z.eqb_neq in E2. apply Z.eqb_eq in E3. lia.
Qed.

Lemma u_slliw2_0 : forall x : word, bv_unsigned x = 0 -> bv_unsigned (v_slliw x 2) = 0.
Proof.
  intros x Hx. unfold v_slliw. rewrite Hx, Z.shiftl_0_l. rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2^31); lia).
  apply u_Z64. lia.
Qed.

Lemma u_srli_mul_0 : forall (s x : word) k, 0 <= k -> bv_unsigned x = 0 -> bv_unsigned (v_srli (v_mul s x) k) = 0.
Proof.
  intros s x k Hk Hx. unfold v_srli, v_mul. rewrite Hx, Z.mul_0_r. rewrite (u_Z64 0) by lia.
  rewrite Z.shiftr_0_l. apply u_Z64. lia.
Qed.

Lemma u_lbu : forall b : byte, bv_unsigned (Z_to_bv 64 (bv_unsigned b)) < 256.
Proof.
  intros b. pose proof (bv_unsigned_in_range _ b) as Hb. change (bv_modulus 8) with 256 in Hb.
  rewrite u_Z64 by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma halveF_odd : forall usage k x, MallocOps.is0 (v_andi x 1) = false -> halveF usage k x = x.
Proof. intros usage [|k] x H; [reflexivity|]. rewrite halveF_S, H. reflexivity. Qed.

Lemma halveF_le : forall usage k x, bv_unsigned x < 2^31 -> bv_unsigned (halveF usage k x) <= bv_unsigned x.
Proof.
  intros usage k. induction k as [|k IH]; intros x Hx; [rewrite halveF_O; lia|].
  rewrite halveF_S. destruct (negb (MallocOps.is0 (v_andi x 1))); [lia|].
  destruct (negb (c_ltu usage (v_slliw x 2))); [lia|].
  pose proof (u_srliw1 x Hx). pose proof (u64_range x).
  specialize (IH (v_srliw x 1) ltac:(lia)). lia.
Qed.

Lemma shrinkF_le : forall size k x, bv_unsigned x < 2^31 -> bv_unsigned (shrinkF size k x) <= bv_unsigned x.
Proof.
  intros size k. induction k as [|k IH]; intros x Hx; [rewrite shrinkF_O; lia|].
  rewrite shrinkF_S. destruct (MallocOps.is0 (v_srli (v_mul size x) 20)); [lia|].
  pose proof (u_srliw1 x Hx). pose proof (u64_range x).
  specialize (IH (v_srliw x 1) ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Lemma nosmall_word : forall b : word,
  negb (c_ltu b (Z_to_bv 64 100)) = negb (c_eq (v_xori (v_sltiu b 100) 1) (Z_to_bv 64 0)).
Proof.
  intros b. rewrite c_ltu_u, c_eq_u. unfold v_xori, v_sltiu.
  change (bv_wrap 64 100) with 100. change (bv_wrap 64 1) with 1. rewrite (u_Z64 100) by lia. rewrite (u_Z64 0) by lia.
  destruct (bv_unsigned b <? 100); cbn [negb].
  - rewrite (u_Z64 1) by lia. change (Z.lxor 1 1) with 0. rewrite (u_Z64 0) by lia. reflexivity.
  - rewrite (u_Z64 0) by lia. change (Z.lxor 0 1) with 1. rewrite (u_Z64 1) by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma and_seqz_sltu : forall x y z : word,
  c_eq (v_and (v_sltiu x 1) (v_sltu y z)) (Z_to_bv 64 0)
  = negb (c_eq x (Z_to_bv 64 0) && c_ltu y z).
Proof.
  intros x y z. rewrite !c_eq_u. unfold v_and, v_sltiu, v_sltu.
  change (bv_wrap 64 1) with 1. rewrite (u_Z64 0) by lia. pose proof (u64_range x).
  replace (bv_unsigned x <? 1) with (bv_unsigned x =? 0)
    by (destruct (bv_unsigned x =? 0) eqn:E; [apply Z.eqb_eq in E; rewrite E; reflexivity
        | apply Z.eqb_neq in E; symmetry; apply Z.ltb_ge; lia]).
  destruct (bv_unsigned x =? 0); destruct (c_ltu y z); rewrite ?u_Z64 by lia; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma m_divu_tot : forall a b : word, mul_div M_DIVU a b = MallocOps.v_divu a b.
Proof.
  intros a b. unfold MallocOps.v_divu.
  change (mul_div M_DIVU a b) with (if (bv_unsigned b =? 0)%Z then Z_to_bv 64 (-1) else bv_divu a b).
  destruct (bv_unsigned b =? 0) eqn:E.
  - apply bv_eq. vm_compute. reflexivity.
  - apply Z.eqb_neq in E. apply bv_eq. rewrite bv_divu_unsigned, Z_to_bv_unsigned.
    symmetry; apply bv_wrap_small. change (bv_modulus 64) with (2^64)%Z.
    pose proof (u64_range a). pose proof (u64_range b).
    split; [apply Z.div_pos; lia|].
    apply Z.le_lt_trans with (bv_unsigned a); [|lia].
    apply Z.div_le_upper_bound; nia.
Qed.

Section Divu.
Context {fx : FPState}.
Lemma step_divu_tot : forall segs regs pc mem rom w rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Mul M_DIVU rd rs1 rs2, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs
                   else regupd regs rd (MallocOps.v_divu (getr regs rs1) (getr regs rs2)))
                  (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs1 rs2 Hf He Hd.
  erewrite step_mul_gen by eassumption. rewrite m_divu_tot. reflexivity.
Qed.
End Divu.

(* [comment removed for export] *)
Ltac mach Hp HS ::=
  cur_instr ltac:(fun w i =>
    lazymatch i with
    | OpImm ALU_ADD _ _ _   => rz_plain Hp HS step_addi
    | OpImm ALU_AND _ _ _   => rz_plain Hp HS step_andi
    | OpImm ALU_OR _ _ _    => rz_plain Hp HS step_ori
    | OpImm ALU_XOR _ _ _   => rz_plain Hp HS step_xori
    | OpImm ALU_SLT _ _ _   => rz_plain Hp HS step_slti
    | OpImm ALU_SLTU _ _ _  => rz_plain Hp HS step_sltiu
    | ShiftImm ALU_SLL _ _ _ => rz_plain Hp HS step_slli
    | ShiftImm ALU_SRL _ _ _ => rz_plain Hp HS PropExec.step_srli
    | ShiftImm ALU_SRA _ _ _ => rz_plain Hp HS step_srai
    | Op ALU_ADD _ _ _  => rz_plain Hp HS step_add
    | Op ALU_SUB _ _ _  => rz_plain Hp HS step_sub
    | Op ALU_AND _ _ _  => rz_plain Hp HS step_and
    | Op ALU_OR _ _ _   => rz_plain Hp HS step_or
    | Op ALU_XOR _ _ _  => rz_plain Hp HS step_xor
    | Op ALU_SLL _ _ _  => rz_plain Hp HS step_sll
    | Op ALU_SRL _ _ _  => rz_plain Hp HS step_srl
    | Op ALU_SRA _ _ _  => rz_plain Hp HS step_sra
    | Op ALU_SLT _ _ _  => rz_plain Hp HS step_slt
    | Op ALU_SLTU _ _ _ => rz_plain Hp HS step_sltu
    | OpImm32 _ _ _     => rz_plain Hp HS step_addiw
    | Op32 ALU_ADD _ _ _ => rz_plain Hp HS step_addw
    | Op32 ALU_SUB _ _ _ => rz_plain Hp HS step_subw
    | Op32 ALU_SLL _ _ _ => rz_plain Hp HS step_sllw
    | Op32 ALU_SRL _ _ _ => rz_plain Hp HS step_srlw
    | Op32 ALU_SRA _ _ _ => rz_plain Hp HS step_sraw
    | ShiftImm32 ALU_SLL _ _ _ => rz_plain Hp HS step_slliw
    | ShiftImm32 ALU_SRL _ _ _ => rz_plain Hp HS step_srliw
    | ShiftImm32 ALU_SRA _ _ _ => rz_plain Hp HS step_sraiw
    | Mul M_MUL _ _ _   => rz_plain Hp HS step_mul
    | Mul M_MULHU _ _ _ => rz_plain Hp HS step_mulhu
    | Mul M_DIVU _ _ _  => rz_plain Hp HS step_divu_tot
    | Lui _ _           => rz_plain Hp HS step_lui
    | Auipc _ _         => rz_plain Hp HS step_auipc
    | Jal _ _           => rz_plain Hp HS step_jal_x0
    | _ => fail "mach: not a plain instruction:" i
    end).


Lemma word_pred_nat : forall k : nat, Z.of_nat (S k) < 2^64 ->
  v_addi (Z_to_bv 64 (Z.of_nat (S k))) (-1) = Z_to_bv 64 (Z.of_nat k).
Proof.
  intros k Hk. apply bv_eq. unfold v_addi. rewrite !Z_to_bv_unsigned.
  rewrite (bv_wrap_small 64 (Z.of_nat (S k))) by (change (bv_modulus 64) with (2^64); lia).
  f_equal. lia.
Qed.

Lemma c_eq0_nat : forall k : nat, Z.of_nat k < 2^64 ->
  c_eq (Z_to_bv 64 (Z.of_nat k)) (Z_to_bv 64 0) = (Z.of_nat k =? 0).
Proof. intros k Hk. rewrite c_eq_u, !u_Z64 by lia. reflexivity. Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac addi_nf l :=
  lazymatch l with
  | v_addi (v_addi ?x ?a) ?b =>
      let z := eval vm_compute in (a + b)%Z in
      lazymatch z with
      | 0%Z => addi_nf x
      | _ => addi_nf (v_addi x z)
      end
  | v_addi ?x 0%Z => addi_nf x
  | _ => l
  end.

Ltac call_side Hp Hag HI HW HS ::=
  cbv delta [ALLOC_STACK];
  lazymatch goal with
  | |- md_pure _ => mpure Hp
  | |- ms_vm _ = m_vmmaps _ => symmetry; apply with_vmmaps_vmmaps
  | |- magree _ _ => exact Hag
  | |- minv _ _ => exact HI
  | |- wtop _ => exact (minv_ceil _ _ HI)
  | |- bv_unsigned (getr _ _) = _ => sys_reg
  | |- bytes_le_to_Z ?b = _ =>
      match goal with
      | Hv : bytes_le_to_Z b = bv_unsigned (le_val b), Hc : c_eq (le_val b) _ = true |- _ =>
          rewrite Hv, (c_eq_eq _ _ Hc); vm_compute; reflexivity
      end
  | |- rdn _ _ _ _ = Some _ =>
      first [ assumption
            | eapply (magree_rd _ _ _ _ _ Hag (minv_lo64 _ _ HI)); eassumption ]
  | |- getr _ _ = ?v =>
      (* [comment removed for export] *)
      regnorm;
      lazymatch goal with |- ?l = ?r =>
        tryif has_evar r then
          (imm_norm;
           lazymatch goal with |- ?l1 = _ =>
             let l' := addi_nf l1 in
             tryif constr_eq l1 l' then reflexivity
             else (transitivity l';
                   [ rewrite ?v_addi_addi'; zsum_norm; rewrite ?v_addi_0;
                     first [reflexivity | klitsg; first [reflexivity | bveq]]
                   | reflexivity ])
           end)
        else (imm_norm; rewrite ?v_addi_addi', ?v_addi_0;
              first [reflexivity | apply v_addi_back; reflexivity | klitsg; first [reflexivity | bveq]])
      end
  | |- _ = negb (c_eq (getr _ _) _) => regnorm; first [ apply nosmall_word | vm_compute; reflexivity | reflexivity ]
  | |- bv_unsigned _ mod 16 = 0 => first [assumption | apply sp_mod16; [assumption | reflexivity | uaddr; alia]]
  | |- ret_ok _ => first [assumption | apply ret_ok_even; vm_compute; reflexivity]
  | |- wtop _ => exact (minv_ceil _ _ HI)
  | |- tsafe _ _ => first [ exact HS | exact (tsafe_bind_inv _ _ _ HS) ]
  | |- forall a : word, _ -> ?m a <> None => win_nn
  | |- @aslot_at _ _ _ => assumption
  | |- context [alloc_ceiling] => rewrite alloc_ceiling_val; uaddr; alia
  | |- _ => uaddr; alia
  end.

(* [comment removed for export] *)
Ltac mach_cutk_core HS Hag HI HW XTY PCF wl XR CUT Kx :=
  lazymatch type of HI with minv ?s0 _ =>
  lazymatch goal with
  | |- realizes ?segs (mkCfg (mkst ?Rf _ ?mmF ?rom) (with_vmmaps _ ?md0)) (tshape (MallocTree.mbind ?M ?K ?s) ?L) =>
    lazymatch type of HS with tsafe _ ?P =>
    set (Kx := K) in HS |- *;
    enough (CUT : forall (x : XTY) (s' : mstate) (mm' : word -> option byte) (R' : bvmap 5 word),
        magree s' mm' -> minv s0 s' ->
        (forall a : word, ms_lo s0 <= bv_unsigned a < ms_hi s0 -> mm' a = mmF a) ->
        (forall r : reg, wreg wl r = false -> getr R' r = getr Rf r) ->
        XR x R' ->
        tsafe (Kx x s') P ->
        realizes segs (mkCfg (mkst R' (PCF x) mm' rom) (with_vmmaps (ms_vm s') md0)) (tshape (Kx x s') L));
    [ | join_intro_k Kx Hag HI HW HS ]
    end
  end end.
Tactic Notation "mach_cutk" constr(HS) constr(Hag) constr(HI) constr(HW)
    constr(XTY) constr(PCF) constr(wl) constr(XR) "as" ident(CUT) ident(Kx) :=
  mach_cutk_core HS Hag HI HW XTY PCF wl XR CUT Kx.

(* [comment removed for export] *)
Ltac cond_facts :=
  repeat match goal with
         | H : ?c = true |- context [?c'] => constr_eq c c'; lazymatch c with true => fail | _ => rewrite H end
         | H : ?c = false |- context [?c'] => constr_eq c c'; lazymatch c with false => fail | _ => rewrite H end
         end;
  cbv beta match delta [andb orb negb fst snd].

(* [comment removed for export] *)
Ltac bool_to_Z :=
  repeat match goal with
  | H : c_eq _ _ = true |- _ => rewrite c_eq_u in H; apply Z.eqb_eq in H
  | H : c_eq _ _ = false |- _ => rewrite c_eq_u in H; apply Z.eqb_neq in H
  | H : c_ltu _ _ = true |- _ => rewrite c_ltu_u in H; apply Z.ltb_lt in H
  | H : c_ltu _ _ = false |- _ => rewrite c_ltu_u in H; apply Z.ltb_ge in H
  | H : MallocOps.is0 _ = true |- _ => rewrite is0_u in H; apply Z.eqb_eq in H
  | H : MallocOps.is0 _ = false |- _ => rewrite is0_u in H; apply Z.eqb_neq in H
  end;
  repeat match goal with
  | H : context [bv_unsigned (Z_to_bv 64 ?z)] |- _ =>
      lazymatch z with
      | bv_unsigned _ => fail
      | _ => let v := eval vm_compute in (bv_unsigned (Z_to_bv 64 z)) in
             change (bv_unsigned (Z_to_bv 64 z)) with v in H
      end
  end.
Ltac blia := bool_to_Z; arith_only; lia.

(* [comment removed for export] *)
Ltac xr_extra := fail.
Ltac xr_tac :=
  cbv beta match; repeat split;
  try (first [ xr_extra
             | regnorm; imm_norm; rewrite ?v_addi_0; cond_facts;
               first [ reflexivity | klitsg; first [reflexivity | bveq] | assumption | xr_extra | alia ]
             | exfalso; blia ]).

Ltac use_cut_k CUT Kx Hag HI HS ::=
  lazymatch goal with
  | |- realizes _ _ (tshape (Kx ?x ?sb) _) =>
      eapply (CUT x sb); [ exact Hag | exact HI | win_same | keep_tac | xr_tac | exact HS ]
  end.

Ltac use_cut_kx CUT Kx Hag HI HS ::=
  lazymatch goal with
  | |- realizes _ _ (tshape (Kx ?x ?sb) _) =>
      eapply (CUT x sb); [ exact Hag | exact HI | win_pres | win_nn | keep_tac | xr_tac | exact HS ]
  end.

(* [comment removed for export] *)
Ltac mach_vjoin_core J wl XR CUT :=
  let J := eval vm_compute in J in
  let Jlit := constr:(@BV 64 J ltac:(vm_compute; exact I)) in
  lazymatch goal with
  | |- realizes ?segs (mkCfg (mkst ?Rf _ ?mmF ?rom) ?mdl) ?T =>
      enough (CUT : forall R' : bvmap 5 word,
        (forall r : reg, wreg wl r = false -> getr R' r = getr Rf r) -> XR R' ->
        realizes segs (mkCfg (mkst R' Jlit mmF rom) mdl) T)
  end.
Ltac vjoin_intro :=
  let R' := fresh "R" in let Hkeep := fresh "Hkeep" in let HX := fresh "HX" in
  intros R' Hkeep HX; keep_facts Hkeep; cbv beta in HX.
Tactic Notation "mach_vjoin" constr(J) constr(wl) constr(XR) "as" ident(CUT) :=
  mach_vjoin_core J wl XR CUT; [ | vjoin_intro ].

Ltac use_vcut CUT := eapply CUT; [ keep_tac | xr_tac ].

(* [comment removed for export] *)
Ltac mach_brc Hp HS :=
  branch_cond ltac:(fun t =>
    first
      [ match goal with Hc : ?t' = _ |- _ => unify t' t; mach_if Hp HS Hc end
      | check_closed_term t;
        let b := eval vm_compute in t in
        let Hc := fresh "Hc" in
        assert (Hc : t = b) by (vm_compute; reflexivity);
        mach_if Hp HS Hc; clear Hc
      | let Hc := fresh "Hc" in
        destruct (b_cases t) as [Hc|Hc]; mach_if Hp HS Hc ]).

(* [comment removed for export] *)
Ltac mach_pure Hp HS J :=
  let J := eval vm_compute in J in
  repeat (cur_pc ltac:(fun u =>
    tryif constr_eq u J then fail else
    cur_instr ltac:(fun w i =>
      lazymatch i with
      | Branch _ _ _ _ => mach_brc Hp HS
      | _ => mach Hp HS
      end))).

(* [comment removed for export] *)
Ltac mach_pload HS :=
  let bs := fresh "bs" in let Hok := fresh "Hok" in let Hrd := fresh "Hrd" in
  let Hv := fresh "Hv" in let EQ := fresh "EQ" in
  first
    [ destruct (tsafe_lbu_inv _ _ _ _ HS) as (bs & Hok & Hrd & EQ)
    | destruct (tsafe_ld_inv _ _ _ _ HS) as (bs & Hok & Hrd & Hv & EQ)
    | destruct (tsafe_lw_inv _ _ _ _ HS) as (bs & Hok & Hrd & Hv & EQ) ];
  rewrite EQ in HS; rewrite EQ; clear EQ;
  lazymatch type of Hrd with rdn _ ?m ?a ?n = Some _ =>
    match goal with
    | H' : rdn _ m a n = Some ?b0 |- _ =>
        tryif constr_eq b0 bs then fail else
          (rewrite H' in Hrd; injection Hrd as Hrd; subst bs; clear Hok)
    end
  end;
  mnorm HS.

(* [comment removed for export] *)
Ltac mnorm HS ::=
  repeat first
    [ progress (cbv beta match zeta delta [negb andb orb fst snd] in HS;
                cbv beta match zeta delta [negb andb orb fst snd])
    | progress (rewrite mbind_assoc in HS; rewrite mbind_assoc)
    | progress (rewrite mret_bind in HS; rewrite mret_bind)
    | progress (rewrite mbind_assoc_k in HS; rewrite mbind_assoc_k)
    | progress (rewrite mret_bind_k in HS; rewrite mret_bind_k)
    | progress (rewrite mbind_mlet in HS; rewrite mbind_mlet)
    | progress (snorm_in HS; rewrite ?upd_mem, ?upd_vm, ?upd_upd) ];
  try match goal with Hag : magree _ _ |- _ => snorm_in Hag end;
  try match goal with HI : minv _ _ |- _ => snorm_in HI end.

Ltac tnorm_eq ::=
  repeat first
    [ progress (cbv beta match zeta delta [negb andb orb fst snd])
    | progress (rewrite mbind_assoc)
    | progress (rewrite mret_bind)
    | progress (rewrite mbind_assoc_k)
    | progress (rewrite mret_bind_k)
    | progress (rewrite mbind_mlet)
    | progress (rewrite ?upd_mem, ?upd_vm, ?upd_upd) ];
  reflexivity.

(* [comment removed for export] *)
Ltac lits64 HS :=
  let one z :=
    let v := eval vm_compute in (2^64 - z)%Z in
    try change (Z_to_bv 64 (2^64 - z)) with (Z_to_bv 64 v) in HS |- * in
  one 1%Z; one 16%Z; one 20%Z; one 4096%Z.

(* [comment removed for export] *)
Ltac model_crash HS :=
  exfalso; clear -HS;
  cbv beta match delta [MallocTree.mbind mcrash tbind tsafe mlet] in HS;
  first [ exact HS | cbn in HS; exact HS ].

(* [comment removed for export] *)
Ltac in_zlist u l :=
  lazymatch l with
  | nil => fail
  | cons ?x ?t => tryif constr_eq u x then idtac else in_zlist u t
  end.
Ltac mach_pure_l Hp HS stops :=
  let stops := eval vm_compute in stops in
  repeat (cur_pc ltac:(fun u =>
    tryif in_zlist u stops then fail else
    cur_instr ltac:(fun w i =>
      lazymatch i with
      | Branch _ _ _ _ => mach_brc Hp HS
      | _ => mach Hp HS
      end))).

(* [comment removed for export] *)
Ltac mach_vlet_core J wl XR CUT HS :=
  lazymatch goal with
  | |- realizes _ _ (tshape (mlet ?E ?F ?sb) _) =>
      let XRE := constr:(XR E) in
      mach_vjoin_core J wl XRE CUT;
      [ | let R' := fresh "R" in let Hkeep := fresh "Hkeep" in let HX := fresh "HX" in
          let v := fresh "vj" in let HE := fresh "HvE" in
          intros R' Hkeep HX; keep_facts Hkeep; cbv beta in HX;
          remember E as v eqn:HE in *; clear HE;
          rewrite (mlet_eq v F) in HS |- *; cbv beta in HS; cbv beta; mnorm HS;
          revert HS; revert HX; revert v ]
  end.
(* [comment removed for export] *)
Tactic Notation "mach_vlet" constr(J) constr(wl) constr(XR) "as" ident(CUT) constr(HS) :=
  mach_vlet_core J wl XR CUT HS.



(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac pc_lit :=
  lazymatch goal with
  | |- realizes _ (mkCfg (mkst _ (@BV 64 _ _) _ _) _) _ => idtac
  | |- realizes _ _ _ => eapply rz_at_pc; [ | symmetry; pc_tac ]
  end.

(* [comment removed for export] *)
Ltac use_cut_kx CUT Kx Hag HI HS ::=
  lazymatch goal with
  | |- realizes _ _ (tshape (Kx ?x ?sb) _) =>
      eapply (CUT x sb);
      [ exact Hag | exact HI | win_pres | win_nn | keep_tac
      | hnf; xr_tac
      | exact HS ]
  end.

(* [comment removed for export] *)
Ltac piece_exit HK K Hag HI HS :=
  lazymatch goal with
  | |- realizes _ _ (tshape (K ?x ?sb) _) =>
      eapply rz_at_pc;
      [ eapply (HK x sb);
        [ exact Hag | exact HI | win_pres | win_nn | keep_tac | hnf; xr_tac | exact HS ]
      | bveq ]
  end.

(* [comment removed for export] *)
Ltac piece_intro Hag HI HW HS :=
  let x := fresh "x" in let s' := fresh "s" in let mm' := fresh "mm" in let R' := fresh "R" in
  let Hag' := fresh "Hag" in let Hkeep := fresh "Hkeep" in let HJ := fresh "HJ" in let HJn := fresh "HJnn" in
  let HInew := fresh "HI" in let HX := fresh "HX" in let HP := fresh "HS" in
  first
    [ (* [comment removed for export] *)
      intros x s' mm' R' Hag' HInew HJ HJn Hkeep HX HP;
      lazymatch type of HP with tsafe _ _ => idtac end;
      uaddrH HJ; uaddrH HJn
    | (* [comment removed for export] *)
      intros x s' mm' R' Hag' HInew HJ Hkeep HX HP;
      lazymatch type of HP with tsafe _ _ => idtac end;
      uaddrH HJ ];
  clear HS Hag HI; rename HP into HS; rename Hag' into Hag; rename HInew into HI;
  note_win HI;
  frame_facts HW mm';
  keep_facts Hkeep;
  revert HS; revert HX; revert x.

(* [comment removed for export] *)
Ltac use_piece_core PL Hp Hag HI HW HS :=
  lazymatch type of HI with minv ?s0 _ =>
  cur_mstate HS ltac:(fun sb =>
  lazymatch goal with
  | |- realizes _ (mkCfg (mkst ?R _ ?mm ?rom) (with_vmmaps _ ?md)) _ =>
      eapply rz_at_pc;
      [ eapply (PL md R mm rom s0 sb);
        first [ lazymatch goal with |- forall (x : _) (s' : mstate), _ => piece_intro Hag HI HW HS end
              | call_side Hp Hag HI HW HS ]
      | bveq ]
  end) end.
Tactic Notation "use_piece" uconstr(PL) constr(Hp) constr(Hag) constr(HI) constr(HW) constr(HS) :=
  use_piece_core PL Hp Hag HI HW HS.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac mach_pload_new HS :=
  let bs := fresh "pbs" in let Hok := fresh "Hpok" in let Hrd := fresh "Hprd" in
  let Hv := fresh "Hpv" in let EQ := fresh "EQ" in
  destruct (tsafe_ld_inv _ _ _ _ HS) as (bs & Hok & Hrd & Hv & EQ);
  rewrite EQ in HS; rewrite EQ; clear EQ; mnorm HS.

Ltac sys_calls Hp HS Hag HI HW t others :=
  let pmm := eval vm_compute in (bv_unsigned PC_MMAP) in
  let pmu := eval vm_compute in (bv_unsigned PC_MUNMAP) in
  let pmp := eval vm_compute in (bv_unsigned PC_MPROTECT) in
  tryif constr_eq t pmm then
    lazymatch goal with
    | |- realizes _ _ (tshape (MallocTree.mbind (sys_mmap ?k _) _ _) _) =>
        match goal with MM : forall k', mmap_stmt k' |- _ => mach_call Hp HS Hag HI HW (MM k) end
    | |- realizes _ _ (tshape (MallocTree.mbind (sys_mmap_fixed_none _ _) _ _) _) =>
        match goal with MF : mmap_fixed_stmt |- _ => mach_call Hp HS Hag HI HW MF end
    end
  else tryif constr_eq t pmu then
    match goal with MU : munmap_stmt |- _ => mach_call Hp HS Hag HI HW MU end
  else tryif constr_eq t pmp then
    (* [comment removed for export] *)
    mach_pload_new HS; mach_passert HS;
    match goal with MP : mprotect_stmt |- _ => mach_call Hp HS Hag HI HW MP end
  else others t.

(* [comment removed for export] *)
Ltac piece_run Hp HS Hag HI HW HK Hret calls K PCF :=
  repeat first
    [ progress (mrun_to_k Hp HS Hag HI HW HK Hret calls K PCF)
    | lazymatch goal with
      | |- realizes _ _ (tshape (MallocTree.mbind sys_brk_query _ _) _) => mach_sys_brk_query Hp HS Hag HI
      | |- realizes _ _ (tshape (MallocTree.mbind (sys_brk_grow _) _ _) _) => mach_sys_brk_grow Hp HS Hag HI
      end ].

(* [comment removed for export] *)
Ltac use_piece2_core PL a1 a2 Hp Hag HI HW HS :=
  lazymatch type of HI with minv ?s0 _ =>
  cur_mstate HS ltac:(fun sb =>
  lazymatch goal with
  | |- realizes _ (mkCfg (mkst ?R _ ?mm ?rom) (with_vmmaps _ ?md)) _ =>
      eapply rz_at_pc;
      [ eapply (PL md R mm rom s0 sb a1 a2);
        first [ lazymatch goal with |- forall (x : _) (s' : mstate), _ => piece_intro Hag HI HW HS end
              | call_side Hp Hag HI HW HS ]
      | bveq ]
  end) end.
Tactic Notation "use_piece2" uconstr(PL) constr(a1) constr(a2) constr(Hp) constr(Hag) constr(HI) constr(HW) constr(HS) :=
  use_piece2_core PL a1 a2 Hp Hag HI HW HS.

(* [comment removed for export] *)
Ltac keeps_facts Hk :=
  let one z :=
    let r := constr:(@BV 5 z I) in
    try (let H := fresh "Hk" in assert (H : getr _ r = getr _ r) by (apply Hk; cbv; tauto)) in
  one 1%Z; one 2%Z; one 3%Z; one 4%Z; one 8%Z; one 9%Z; one 10%Z; one 18%Z; one 19%Z; one 20%Z; one 21%Z;
  one 22%Z; one 23%Z; one 24%Z; one 25%Z; one 26%Z; one 27%Z.

(* [comment removed for export] *)
Lemma keeps_wreg : forall (wl : list Z) (R1 R2 : bvmap 5 word) (r : reg),
  keeps R1 R2 ->
  forallb (fun z => existsb (Z.eqb z) wl) [5;6;7;11;12;13;14;15;16;17;28;29;30;31]%Z = true ->
  wreg wl r = false -> getr R2 r = getr R1 r.
Proof.
  intros wl R1 R2 r Hk Hsub Hr.
  assert (Hin : forall z, In z [5;6;7;11;12;13;14;15;16;17;28;29;30;31]%Z -> bv_unsigned r <> z).
  { intros z Hz E. rewrite forallb_forall in Hsub. specialize (Hsub z Hz). cbn beta in Hsub.
    unfold wreg in Hr. rewrite <- E in Hsub. rewrite Hsub in Hr. discriminate. }
  destruct (reg_enum r) as
    [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]];
    first [ reflexivity
          | apply Hk; cbv [callee_kept In]; intuition congruence
          | exfalso; refine (Hin _ _ eq_refl); cbv [In]; intuition congruence ].
Qed.

(* [comment removed for export] *)
Definition NONCS : list Z := [0;1;5;6;7;10;11;12;13;14;15;16;17;28;29;30;31]%Z.

Lemma callee_saved_of_wreg : forall (wl : list Z) (r : reg),
  forallb (fun z => existsb (Z.eqb z) wl) NONCS = true ->
  wreg wl r = false -> AllocIface.callee_saved r.
Proof.
  intros wl r Hsub Hr. pose proof (wreg_sub wl _ r Hsub Hr) as H. clear Hsub Hr.
  unfold wreg, NONCS in H. unfold AllocIface.callee_saved.
  destruct (reg_enum r) as
    [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]];
    first [ cbv in H; discriminate H
          | do 5 right; split; apply Z.leb_le; vm_compute; reflexivity
          | left; reflexivity
          | right; left; reflexivity
          | right; right; left; reflexivity
          | right; right; right; left; reflexivity
          | right; right; right; right; left; reflexivity ].
Qed.

Ltac keep_tac ::=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr;
  lazymatch type of Hr with wreg ?wl _ = false =>
    repeat first
      [ (* [comment removed for export] *)
        lazymatch goal with
        | |- getr (regupd ?R0 ?r0 ?v0) r = _ =>
            let R := constr:(regupd R0 r0 v0) in
            let bl := gf_reify R in
            lazymatch bl with
            | (?base, ?l) => rewrite (getr_upds_test (wreg wl) base l r eq_refl Hr : getr R r = getr base r)
            end
        end
      | rewrite (getr_other_w wl _ _ _ r); [ | reflexivity | exact Hr ]
      | match goal with
        | Hk : forall r' : reg, wreg ?wl' r' = false -> getr ?R1 r' = getr _ r' |- getr ?R1 r = _ =>
            rewrite (Hk r (wreg_sub wl wl' r eq_refl Hr))
        | Hk : forall r' : reg, AllocIface.callee_saved r' -> getr ?R1 r' = getr _ r' |- getr ?R1 r = _ =>
            rewrite (Hk r (callee_saved_of_wreg wl r eq_refl Hr))
        | Hk : keeps ?R0 ?R1 |- getr ?R1 r = _ =>
            rewrite (keeps_wreg wl R0 R1 r Hk eq_refl Hr)
        end ]
  end;
  reflexivity.
