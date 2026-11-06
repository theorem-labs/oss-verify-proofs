(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac StoreOk MemSplit Hoare ShapeAlg SRealizes MmapSim
  RefMemcpyLib LibIface LibEff ZStores SymExec3 SymExec3Sound SymRun3 SumWalkTac.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContLib ContStmts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HLib.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require PeLia.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma mdef_defined : forall M a n, CRep.mdef M a n <-> HRep.defined M a n.
Proof. intros M a n. reflexivity. Qed.

Lemma mdef_sub : forall M a n b k, mdef M a n -> a <= b -> b + k <= a + n -> mdef M b k.
Proof. intros M a n b k Hd Hab Hbk i Hi. replace (b + i) with (a + (b - a + i)) by lia. apply Hd. lia. Qed.

Lemma mdef_wbytes : forall M a n (d : word) bs, mdef M a n -> mdef (wbytes M d bs) a n.
Proof. intros M a n d bs Hd i Hi. apply wbytes_grows. apply Hd. exact Hi. Qed.

Section WithSegs.
Context {AC : AllocCeiling}.
Variable SEGS : list Segment.

Lemma fld_cellw : forall M a (w : N) v,
  fld SEGS M a (N.to_nat w) v -> 0 <= v < 2 ^ (8 * Z.of_N w) -> cellw SEGS M a w v.
Proof using SEGS. intros M a w v HF Hv. split; [exact Hv | exact HF]. Qed.

Lemma kwr_of_mdef : forall E M (n : N) (base off len : Z),
  ev E n = Z_to_bv 64 base -> 0 <= base < 2 ^ 64 -> 0 <= base + off < 2 ^ 64 -> base + off + len <= 2 ^ 64 -> 0 <= len < 2 ^ 64 ->
  mdef M (base + off) len ->
  kentry_ok SEGS E M (KWr (SA (EVar n) off) (ELit len)).
Proof using SEGS.
  intros E M n base off len Hn Hb H0 H1 Hl Hd. cbn [kentry_ok].
  unfold flat, estart, elenZ. cbn [a_base a_off edenot]. rewrite Hn, !u64_of_Z by lia.
  split; [lia|]. intros d m Hdd Hdm. destruct m as [|m']; [reflexivity|].
  rewrite <- (Nat2Z.id (S m')). apply store_ok_of_defined; [lia | lia |].
  intros i Hi. replace (base + off + d + i) with (base + off + (d + i)) by lia. apply Hd. lia.
Qed.

Lemma kwr_abs_of_mdef : forall E M (a len : Z),
  0 <= a < 2 ^ 64 -> a + len <= 2 ^ 64 -> 0 <= len < 2 ^ 64 -> mdef M a len ->
  kentry_ok SEGS E M (KWr (SA (ELit 0) a) (ELit len)).
Proof using SEGS.
  intros E M a len H0 H1 Hl Hd. cbn [kentry_ok].
  unfold flat, estart, elenZ. cbn [a_base a_off edenot]. rewrite !u64_of_Z by lia.
  split; [lia|]. intros d m Hdd Hdm. destruct m as [|m']; [reflexivity|].
  rewrite <- (Nat2Z.id (S m')). rewrite Z.add_0_l. apply store_ok_of_defined; [lia | lia |].
  intros i Hi. replace (a + d + i) with (a + (d + i)) by lia. apply Hd. lia.
Qed.

Lemma kimg_of_clear : forall E M lo hi,
  0 <= lo -> hi <= 2 ^ 64 -> (forall a, lo <= a < hi -> M (Z_to_bv 64 a) = None) ->
  kentry_ok SEGS E M (KImg lo hi).
Proof using SEGS. intros. apply kimg_abs; assumption. Qed.

End WithSegs.

Ltac fld_fix HF :=
  lazymatch goal with |- CRep.fld _ _ ?a _ _ =>
    lazymatch type of HF with CRep.fld _ _ ?a' _ _ =>
      first [ constr_eq a a' | replace a with a' by lia ]; exact HF end end.

Ltac cw_fix H :=
  lazymatch goal with |- cellw _ _ ?a ?w _ =>
    lazymatch type of H with
    | cellw _ _ ?a' _ _ => first [ constr_eq a a' | replace a with a' by lia ]; exact H
    | CRep.fld _ _ ?a' _ _ => eapply fld_cellw; [first [ constr_eq a a' | replace a with a' by lia ]; exact H | cbn; lia]
    end
  end.

Ltac kwv HF Hreg :=
  lazymatch type of Hreg with
  | _ = Z_to_bv 64 ?b =>
    eapply (kword_var _ _ _ _ b);
    [ cw_fix HF
    | cbn; lia
    | evs; first [exact Hreg | reflexivity]
    | lia | lia | cbn; lia
    | evs; cbn [nth]; first [reflexivity | symmetry; apply Z_to_bv_bv_unsigned | f_equal; lia] ]
  end.

Ltac kwa HF :=
  eapply kword_abs;
  [ cw_fix HF
  | cbn; lia | lia | cbn; lia
  | evs; first [reflexivity | symmetry; apply Z_to_bv_bv_unsigned | f_equal; lia] ].

Ltac krv Hreg := eapply krange_var; [evs; first [exact Hreg | reflexivity] | lia | lia].

Section KD.
Context {AC : AllocCeiling}.
Variable SEGS : list Segment.
Lemma kdisj_ok : forall E M (a1 a2 : saddr) (n1 n2 : expr) (b1 l1 b2 l2 : Z),
  edenot E (a_base a1) = Z_to_bv 64 b1 -> edenot E n1 = Z_to_bv 64 l1 ->
  edenot E (a_base a2) = Z_to_bv 64 b2 -> edenot E n2 = Z_to_bv 64 l2 ->
  0 <= b1 < 2 ^ 64 -> 0 <= l1 < 2 ^ 64 -> 0 <= b2 < 2 ^ 64 -> 0 <= l2 < 2 ^ 64 ->
  (b1 + a_off a1 + l1 <= b2 + a_off a2 \/ b2 + a_off a2 + l2 <= b1 + a_off a1) ->
  kentry_ok SEGS E M (KDisj a1 n1 a2 n2).
Proof using SEGS.
  intros E M a1 a2 n1 n2 b1 l1 b2 l2 H1 H2 H3 H4 R1 R2 R3 R4 H. cbn [kentry_ok].
  unfold estart, elenZ. rewrite H1, H2, H3, H4, !u64_of_Z by lia. exact H.
Qed.
End KD.

Definition zar (op : aluop) (x y : Z) : Z :=
  match op with
  | ALU_ADD => (x + y) mod 2 ^ 64
  | ALU_SUB => (x - y) mod 2 ^ 64
  | ALU_AND => Z.land x y
  | ALU_OR => Z.lor x y
  | ALU_XOR => Z.lxor x y
  | ALU_SRL => x / 2 ^ (y mod 64)
  | ALU_SLL => (x * 2 ^ (y mod 64)) mod 2 ^ 64
  | ALU_SLTU => if x <? y then 1 else 0
  | _ => zalu op x y
  end.

Lemma zfast_ref_zar : forall op x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> zfast_ref op x y = zar op x y.
Proof.
  intros op x y Hx Hy. unfold zfast_ref, zar, SymExec3.SX2.two64.
  pose proof (Z.mod_pos_bound y 64 ltac:(lia)) as Hk.
  destruct op; try reflexivity.
  - destruct (Z.ltb_spec (x + y) (2 ^ 64)).
    + rewrite Z.mod_small by lia. reflexivity.
    + rewrite <- (Z.mod_add _ (-1)) by lia. rewrite Z.mod_small by lia. lia.
  - destruct (Z.leb_spec 0 (x - y)).
    + rewrite Z.mod_small by lia. reflexivity.
    + rewrite <- (Z.mod_add _ 1) by lia. rewrite Z.mod_small by lia. lia.
  - rewrite Z.shiftl_mul_pow2 by lia. reflexivity.
  - rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Lemma alu_Z : forall op x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  alu64 op (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (zar op x y).
Proof.
  intros op x y Hx Hy. rewrite <- zfast_ref_zar, <- zfast_ref_eq, zfast_eq by (unfold SymExec3.SX2.two64; lia).
  unfold zalu. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

Lemma alu_Z_range : forall op x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> 0 <= zar op x y < 2 ^ 64.
Proof.
  intros op x y Hx Hy. rewrite <- zfast_ref_zar, <- zfast_ref_eq, zfast_eq by (unfold SymExec3.SX2.two64; lia).
  unfold zalu. apply u64_range.
Qed.

Lemma mul_Z : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  mul_div M_MUL (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 ((x * y) mod 2 ^ 64).
Proof.
  intros x y Hx Hy.
  transitivity (Z_to_bv 64 (zmd M_MUL x y)); [unfold zmd; symmetry; apply Z_to_bv_bv_unsigned|].
  rewrite <- zfastm_eq by (unfold SymExec3.SX2.two64; lia). rewrite zfastm_ref_eq. reflexivity.
Qed.

Lemma ext_Z_val : forall lo n x, 0 <= x < 2 ^ 64 ->
  ext_val false lo n (Z_to_bv 64 x) = Z_to_bv 64 ((x / 2 ^ (8 * Z.of_nat lo)) mod 2 ^ (8 * Z.of_nat n)).
Proof. intros lo n x Hx. unfold ext_val, ext_Z. rewrite u64_of_Z by lia. reflexivity. Qed.

Lemma mod_range64 : forall x m, 0 < m -> m <= 2 ^ 64 -> 0 <= x mod m < 2 ^ 64.
Proof. intros x m Hm Hm'. pose proof (Z.mod_pos_bound x m Hm). lia. Qed.

Lemma lit_wrap : forall z, Z_to_bv 64 z = Z_to_bv 64 (z mod 2 ^ 64).
Proof. intros z. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite Z.mod_mod by lia. reflexivity. Qed.

Ltac zlit :=
  repeat match goal with
  | |- context [Z_to_bv 64 ?c] =>
      lazymatch c with
      | Zneg _ => rewrite (lit_wrap c); let c' := eval vm_compute in (c mod 2 ^ 64) in change (c mod 2 ^ 64) with c'
      end
  end.

Ltac zrange :=
  first [ lia
        | apply alu_Z_range; zrange
        | apply mod_range64; lia
        | apply Z.mod_pos_bound; lia
        | split; [apply Z.mod_pos_bound; lia | eapply Z.lt_le_trans; [apply Z.mod_pos_bound; lia | lia]] ].
Ltac zsimp1 :=
  first [ rewrite alu_Z by zrange
        | rewrite mul_Z by zrange
        | rewrite ext_Z_val by zrange ].

Lemma land_ones : forall k j, 0 <= j -> Z.land k (2 ^ j - 1) = k mod 2 ^ j.
Proof. intros k j Hj. rewrite <- (Z.land_ones k j Hj). unfold Z.ones. rewrite Z.shiftl_1_l. reflexivity. Qed.
Lemma land_1' : forall k, Z.land k 1 = k mod 2.
Proof. intros k. change 1 with (2 ^ 1 - 1) at 1. rewrite land_ones by lia. reflexivity. Qed.
Lemma land_255 : forall k, Z.land k 255 = k mod 256.
Proof. intros k. change 255 with (2 ^ 8 - 1). rewrite land_ones by lia. reflexivity. Qed.
Lemma land_ffff : forall k, Z.land k 65535 = k mod 2 ^ 16.
Proof. intros k. change 65535 with (2 ^ 16 - 1). rewrite land_ones by lia. reflexivity. Qed.
Lemma land_32 : forall k, Z.land k 4294967295 = k mod 2 ^ 32.
Proof. intros k. change 4294967295 with (2 ^ 32 - 1). rewrite land_ones by lia. reflexivity. Qed.

Ltac zconst :=
  repeat match goal with
  | |- context [Z.of_nat ?n] => lazymatch n with O => change (Z.of_nat O) with 0 | S _ => let c := eval vm_compute in (Z.of_nat n) in change (Z.of_nat n) with c end
  end;
  repeat match goal with
  | |- context [2 ^ ?k] => lazymatch k with Zpos _ => let c := eval vm_compute in (2 ^ k) in change (2 ^ k) with c | Z0 => change (2 ^ 0) with 1 end
  | |- context [8 * ?k] => lazymatch k with Zpos _ => let c := eval vm_compute in (8 * k) in change (8 * k) with c | Z0 => change (8 * 0) with 0 end
  end;
  rewrite ?Z.div_1_r.

Ltac regsub :=
  repeat match goal with
  | H : getr ?R ?r = ?v |- context [getr ?R2 ?r'] => constr_eq R R2; replace (getr R2 r') with v by (first [exact H | symmetry; exact H])
  end.

Ltac znorm := zlit; repeat zsimp1; cbn [zar]; zconst; rewrite ?land_1', ?land_255, ?land_ffff, ?land_32; rewrite ?v_addi_Z by zrange.
Ltac zsimp := cbn [edenot]; evs; regsub; znorm.

Definition mlia_done (x y : Z) : Prop := True.
Ltac mlia_dm x y :=
  lazymatch goal with
  | _ : mlia_done x y |- _ => fail
  | _ => pose proof (Z_div_mod_eq_full x y); pose proof (Z.mod_pos_bound x y ltac:(lia)); pose proof (I : mlia_done x y)
  end.
Ltac mlia_step :=
  match goal with
  | |- context [Z.div ?x ?y] => mlia_dm x y
  | |- context [Z.modulo ?x ?y] => mlia_dm x y
  end.
Ltac mlia := first [ repeat mlia_step; PeLia.pe_zify_prune; Zify.zify; xlia zchecker
                   | Z.to_euclidean_division_equations; lia ].

Lemma bv_signed_small63 : forall z, 0 <= z < 2 ^ 63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. unfold bv_signed. rewrite (SymExec3.SX2.swrap_small 64 (bv_unsigned (Z_to_bv 64 z)) (2 ^ 63) (2 ^ 64));
    [| reflexivity | reflexivity | rewrite u64_of_Z by lia; lia | lia].
  rewrite u64_of_Z by lia. destruct (Z.ltb_spec z (2 ^ 63)); lia.
Qed.
Lemma br_lt : forall x y, 0 <= x < 2 ^ 63 -> 0 <= y < 2 ^ 63 ->
  branch_taken BC_LT (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof. intros x y Hx Hy. cbn [branch_taken]. unfold bv_lts. rewrite !bv_signed_small63 by lia. reflexivity. Qed.
Lemma br_ge : forall x y, 0 <= x < 2 ^ 63 -> 0 <= y < 2 ^ 63 ->
  branch_taken BC_GE (Z_to_bv 64 x) (Z_to_bv 64 y) = negb (x <? y).
Proof. intros x y Hx Hy. cbn [branch_taken]. unfold bv_lts. rewrite !bv_signed_small63 by lia. reflexivity. Qed.

Ltac zbr :=
  cbn [sc_denot]; zsimp;
  first [ rewrite br_eq by zrange | rewrite br_ne by zrange | rewrite br_ltu by zrange | rewrite br_geu by zrange
        | rewrite br_lt by mlia | rewrite br_ge by mlia | idtac ];
  cbn [negb].

Ltac zif :=
  repeat match goal with
  | |- context [if ?a <? ?b then _ else _] =>
      first [ replace (a <? b) with true by (symmetry; apply Z.ltb_lt; mlia)
            | replace (a <? b) with false by (symmetry; apply Z.ltb_ge; mlia) ]; cbn match
  | |- context [if ?a <=? ?b then _ else _] =>
      first [ replace (a <=? b) with true by (symmetry; apply Z.leb_le; mlia)
            | replace (a <=? b) with false by (symmetry; apply Z.leb_gt; mlia) ]; cbn match
  end.

Ltac zbr_auto := zbr; zif; first [reflexivity | apply Z.eqb_eq; mlia | apply Z.eqb_neq; mlia | apply Z.ltb_lt; mlia | apply Z.ltb_ge; mlia
                                  | apply (proj2 (Bool.negb_true_iff _)); first [apply Z.eqb_neq; mlia | apply Z.ltb_ge; mlia]
                                  | apply (proj2 (Bool.negb_false_iff _)); first [apply Z.eqb_eq; mlia | apply Z.ltb_lt; mlia] ].

Definition RET_WORD : bv 32 := Z_to_bv 32 0x8067.

Lemma ret_at : forall {fx : FPState} segs (pc : Z) (R : bvmap 5 word) (M rom : word -> option byte) (ret : word),
  fetch_word segs (Z_to_bv 64 pc) = Some RET_WORD ->
  getr R 1%bv = ret -> ret_ok ret ->
  msteps segs (@mkst fx R (Z_to_bv 64 pc) M rom) (@mkst fx R ret M rom).
Proof.
  intros fx segs pc R M rom ret HF Hra Hret.
  eapply mst_step; [reflexivity | |].
  - eapply (step_jalr_gen segs R (Z_to_bv 64 pc) M rom RET_WORD 0%bv 1%bv 0%bv HF); vm_refl_bv.
  - cbn [bv_eqb]. rewrite Hra.
    unfold ret_ok, v_jalr in Hret. unfold jalr_tgt.
    lazymatch goal with |- msteps _ (mkst _ ?p _ _) _ => replace p with ret by (symmetry; exact Hret) end.
    apply mst_refl.
Qed.

Ltac regsub_in H :=
  repeat match goal with
  | G : getr ?R ?r = ?v |- _ =>
      lazymatch type of H with
      | context [getr ?R2 ?r'] => constr_eq R R2; replace (getr R2 r') with v in H by (symmetry; exact G)
      end
  end.

Ltac wnorm_in H :=
  unfold adenot in H; cbn [a_base a_off edenot] in H; evs_in H; regsub_in H;
  revert H; znorm; intros H;
  rewrite ?Z.add_0_r in H; repeat rewrite Z.mod_small in H by lia.

Lemma Z_to_bv_eqm : forall a b, a mod 2 ^ 64 = b mod 2 ^ 64 -> Z_to_bv 64 a = Z_to_bv 64 b.
Proof. intros a b H. rewrite (lit_wrap a), (lit_wrap b), H. reflexivity. Qed.

Ltac regval HR r v X :=
  let H := fresh in
  rreg HR r H;
  lazymatch type of HR with regs_ok _ _ ?R' =>
  assert (X : getr R' r = Z_to_bv 64 v) end;
  [ rewrite H; regsub; znorm;
    first [ reflexivity | assumption | apply Z_to_bv_eqm; first [reflexivity | mlia] | f_equal; mlia ]
  | clear H ].

Ltac kwe HF Hreg :=
  lazymatch type of Hreg with
  | _ = Z_to_bv 64 ?b =>
    eapply (kword_var _ _ _ _ b);
    [ cw_fix HF
    | cbn; lia
    | evs; first [exact Hreg | reflexivity]
    | lia | lia | cbn; lia
    | evs; cbn [nth]; regsub; rewrite ?alu_Z by lia; cbn [zar]; rewrite ?Z.mod_small by lia; rewrite ?u64_of_Z by lia;
      first [reflexivity | symmetry; apply Z_to_bv_bv_unsigned | f_equal; lia] ]
  end.

Ltac stores_tower :=
  repeat (eapply stores_in_wbytes_more;
          [ | lia
            | rewrite ?length_N_to_le_bytes, ?repeat_length; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; lia
            | intros ? ?; rewrite ?length_N_to_le_bytes, ?repeat_length in *; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in *; unfold zwin; lia ]);
  apply stores_in_refl.

Ltac peel_len := rewrite ?length_N_to_le_bytes, ?repeat_length; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Nat.add]; lia.

Ltac peel_hit :=
  lazymatch goal with
  | |- rdn _ (wbytes _ (Z_to_bv 64 ?b) (word_to_le_bytes ?n ?w)) (Z_to_bv 64 ?a) ?k = Some (word_to_le_bytes ?k' ?w') =>
      let n2 := eval cbv in n in let k2 := eval cbv in k in let k3 := eval cbv in k' in
      constr_eq n2 k2; constr_eq k2 k3;
      first [ constr_eq a b | replace (Z_to_bv 64 a) with (Z_to_bv 64 b) by (f_equal; lia) ];
      first [ constr_eq w w' | replace w' with w by (first [ reflexivity | f_equal; lia | apply Z_to_bv_eqm; mlia | symmetry; apply Z_to_bv_bv_unsigned | rewrite Z_to_bv_bv_unsigned; reflexivity ]) ];
      change k with k2; change n with k2; change k' with k2;
      lazymatch k2 with
      | 8%nat => apply rdn_wbytes_hit8
      | 4%nat => apply ContLib.rdn_wbytes_hit4
      | 1%nat => apply ContLib.rdn_wbytes_hit1
      end; rewrite u64_of_Z by lia; lia
  end.

Ltac peel :=
  repeat first [ peel_hit
               | rewrite SumWalkTac.rdn_wbytes_out_Z by peel_len ].

Ltac xrun_at HR HK fxg pc rom fuel stops scr nx :=
  lazymatch type of HR with
  | regs_ok ?E ?sr ?R =>
    lazymatch type of HK with
    | know_ok ?segs _ ?M ?kn =>
        let r := eval vm_compute in (sym_exec segs fuel true stops scr (SS pc sr [] kn nx) []) in
        lazymatch r with
        | (?ss', ?scs, ?scr') =>
            let Hsc := fresh "Hsc" in
            assert (Hsc : scs_denot segs M E scs);
            [ | let R' := fresh "R'" in let HR' := fresh "HR'" in
                let Hlf := fresh "Hlf" in let Hms := fresh "Hms" in
                destruct (@run_sound fxg segs fuel stops scr pc sr kn nx ss' scs scr' E M rom R
                           ltac:(vm_cast_no_check (@eq_refl _ (ss', scs, scr'))) HR HK Hsc)
                  as (R' & HR' & Hlf & Hms);
                clear Hsc; cbn [s_pc s_regs s_log mem_denot] in HR', Hlf, Hms ]
        end
    end
  end.

Ltac zflat :=
  cbn [sc_denot]; unfold flat, estart, elenZ; cbn [a_base a_off]; zsimp;
  rewrite ?Z.mod_small by lia; rewrite !u64_of_Z by zrange; mlia.

Ltac zso :=
  cbn [sc_denot]; unfold adenot; cbn [a_base a_off]; zsimp;
  rewrite ?Z.mod_small by lia; rewrite ?v_addi_Z by lia; rewrite ?Z.add_0_r;
  lazymatch goal with |- store_ok _ _ (Z_to_bv 64 ?a) ?n = true =>
    rewrite <- (Nat2Z.id n); apply store_ok_of_defined; [lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | ];
    repeat apply mdef_wbytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]
  end.

Ltac sc_auto :=
  lazymatch goal with
  | |- sc_denot _ _ _ (SCBr _ _ _ _) => zbr_auto
  | |- sc_denot _ _ _ (SCFlat _ _) => first [sc_fl | zflat]
  | |- sc_denot _ _ _ (SCStoreOk _ _) => zso
  | |- sc_denot _ _ _ (SCDisj _ _ _ _) => zflat
  | |- sc_denot _ _ _ (SCInside _ _ _ _) => zflat
  | |- sc_denot _ _ _ (SCReadBase _ _ _ _) => match goal with H : cellw _ _ _ _ _ |- _ => sc_rd H end
  | |- _ => idtac
  end.

Ltac scs_auto := repeat apply Forall_cons; try apply Forall_nil; sc_auto.

Ltac gnorm rr :=
  repeat match goal with
  | |- context [getr ?Rx (Z_to_bv 5 (Z.of_N ?k))] => change (getr Rx (Z_to_bv 5 (Z.of_N k))) with (getr Rx rr)
  end.

Ltac kept_via HR3 Y HR1 :=
  lazymatch goal with |- getr _ ?rr = _ =>
    let H := fresh in rreg HR3 rr H; rewrite H; clear H; gnorm rr;
    rewrite ?Y by ninl;
    try (let H1 := fresh in rreg HR1 rr H1; rewrite H1; clear H1; gnorm rr);
    regsub;
    first [ reflexivity
          | znorm; first [reflexivity | apply Z_to_bv_eqm; mlia | f_equal; mlia] ]
  end.

Lemma stack_room_mono : forall segs M sp S S',
  stack_room segs M sp S -> 0 <= S' <= S -> S <= sp -> sp < 2 ^ 63 -> stack_room segs M sp S'.
Proof.
  intros segs M sp S S' HR HS HSsp Hsp. unfold stack_room.
  eapply stack_room_sub; [exact HR | lia | lia | lia | lia].
Qed.

Section Slots.
Context {AC : AllocCeiling}.
Variable SEGS : list Segment.

Definition slots (M : mem) (sp : Z) (vs : list word) : Prop :=
  forall k, (k < length vs)%nat -> cellw SEGS M (sp - 8 - 8 * Z.of_nat k) 8 (bv_unsigned (nth k vs (Z_to_bv 64 0))).

Lemma slots_agree : forall M M' sp vs,
  slots M sp vs -> 8 * Z.of_nat (length vs) <= sp -> sp < 2 ^ 63 ->
  CRep.agree_on (zwin (sp - 8 * Z.of_nat (length vs)) sp) M M' -> slots M' sp vs.
Proof using SEGS.
  intros M M' sp vs SL Hlo Hhi HA k Hk. destruct (SL k Hk) as [Hv HF]. split; [exact Hv|].
  eapply fld_agree; [lia | cbn; lia | exact HF |].
  eapply agree_on_weaken; [exact HA|]. intros a Ha. unfold zwin in *. cbn in Ha. lia.
Qed.
End Slots.

Ltac slot_one :=
  cbn [nth Z.of_nat Pos.of_succ_nat Pos.succ Pos.mul Z.mul]; split;
  [ lazymatch goal with |- 0 <= bv_unsigned ?v < _ => pose proof (u64_range v); cbn; lia end
  | rewrite Z_to_bv_bv_unsigned; peel;
    lazymatch goal with |- rdn _ (wbytes _ _ _) _ _ = _ => fail | |- _ => assumption end ].
Ltac slots_tower :=
  let k := fresh "k" in let Hk := fresh "Hk" in
  intros k Hk; cbn [length] in Hk;
  do 24 (first [ exfalso; clear - Hk; cbn in Hk; lia | destruct k as [|k]; [once slot_one|] ]);
  exfalso; clear - Hk; cbn in Hk; lia.

Ltac kept_fin HRn :=
  lazymatch goal with |- getr _ ?rr = _ =>
    let H := fresh in rreg HRn rr H; rewrite H; clear H; gnorm rr; regsub;
    first [ reflexivity
          | znorm; first [reflexivity | apply Z_to_bv_eqm; mlia | f_equal; mlia] ]
  end.

Ltac wnorm_goal :=
  unfold adenot; cbn [a_base a_off edenot]; evs; regsub; znorm;
  rewrite ?Z.add_0_r; repeat rewrite Z.mod_small by lia.

Ltac kdj_den :=
  evs; first [ reflexivity | eassumption | symmetry; eassumption
             | regsub; znorm; first [reflexivity | apply Z_to_bv_eqm; mlia] ].
Ltac kdj b1 l1 b2 l2 :=
  eapply (kdisj_ok _ _ _ _ _ _ _ b1 l1 b2 l2);
  [ kdj_den | kdj_den | kdj_den | kdj_den | lia | lia | lia | lia | cbn [a_off] ].

Ltac khop H rr :=
  lazymatch type of H with
  | regs_ok _ _ _ => let X := fresh in rreg H rr X; rewrite X; clear X; gnorm rr
  | _ => first [ rewrite (H rr) by inl | rewrite (H rr) by ninl ]
  end.
Ltac kept_close := regsub; first [ reflexivity | znorm; first [reflexivity | apply Z_to_bv_eqm; mlia | f_equal; mlia] ].
Tactic Notation "kept_chain" constr(H1) := lazymatch goal with |- getr _ ?rr = _ => khop H1 rr; kept_close end.
Tactic Notation "kept_chain" constr(H1) constr(H2) :=
  lazymatch goal with |- getr _ ?rr = _ => khop H1 rr; try khop H2 rr; kept_close end.
Tactic Notation "kept_chain" constr(H1) constr(H2) constr(H3) :=
  lazymatch goal with |- getr _ ?rr = _ => khop H1 rr; try khop H2 rr; try khop H3 rr; kept_close end.
Tactic Notation "kept_chain" constr(H1) constr(H2) constr(H3) constr(H4) :=
  lazymatch goal with |- getr _ ?rr = _ => khop H1 rr; try khop H2 rr; try khop H3 rr; try khop H4 rr; kept_close end.
Tactic Notation "kept_chain" constr(H1) constr(H2) constr(H3) constr(H4) constr(H5) :=
  lazymatch goal with |- getr _ ?rr = _ => khop H1 rr; try khop H2 rr; try khop H3 rr; try khop H4 rr; try khop H5 rr; kept_close end.
Tactic Notation "kept_chain" constr(H1) constr(H2) constr(H3) constr(H4) constr(H5) constr(H6) :=
  lazymatch goal with |- getr _ ?rr = _ => khop H1 rr; try khop H2 rr; try khop H3 rr; try khop H4 rr; try khop H5 rr; try khop H6 rr; kept_close end.
Tactic Notation "kept_chain" constr(H1) constr(H2) constr(H3) constr(H4) constr(H5) constr(H6) constr(H7) :=
  lazymatch goal with |- getr _ ?rr = _ => khop H1 rr; try khop H2 rr; try khop H3 rr; try khop H4 rr; try khop H5 rr; try khop H6 rr; try khop H7 rr; kept_close end.

Lemma rdn_pointwise : forall segs M n (a : word) bs (x : word),
  rdn segs M a n = Some bs ->
  (bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat n)%Z -> (bv_unsigned a + Z.of_nat n <= 2 ^ 64)%Z ->
  M x <> None \/ seg_rom segs x <> None.
Proof.
  intros segs M n. induction n as [|n IH]; intros a bs x HR Hx Hnw; [lia|].
  cbn [rdn] in HR.
  destruct (M a) as [b|] eqn:Ema.
  - destruct (rdn segs M (a + 1) n) as [rest|] eqn:ER; [|discriminate HR].
    destruct (Z.eq_dec (bv_unsigned x) (bv_unsigned a)) as [E|Hne].
    + left. replace x with a by (apply bv_eq; lia). rewrite Ema. discriminate.
    + pose proof (u64_range a). pose proof (u64_range x).
      eapply (IH (a + 1)%bv rest x ER); rewrite w_add_1, u64_of_Z by lia; lia.
  - destruct (seg_rom segs a) as [b|] eqn:Es; [|discriminate HR].
    destruct (rdn segs M (a + 1) n) as [rest|] eqn:ER; [|discriminate HR].
    destruct (Z.eq_dec (bv_unsigned x) (bv_unsigned a)) as [E|Hne].
    + right. replace x with a by (apply bv_eq; lia). rewrite Es. discriminate.
    + pose proof (u64_range a). pose proof (u64_range x).
      eapply (IH (a + 1)%bv rest x ER); rewrite w_add_1, u64_of_Z by lia; lia.
Qed.

Lemma sbuf_eq_dec : forall m m' : sbuf, {m = m'} + {m <> m'}.
Proof. decide equality; apply Z.eq_dec. Qed.

Lemma sub_1 : forall {T : Type} (bs : list T) i (d : T), (i < length bs)%nat -> sub bs i 1 = [nth i bs d].
Proof.
  intros T bs. induction bs as [|b bs IH]; intros i d Hi; cbn [length] in Hi; [lia|].
  destruct i as [|i]; [reflexivity|]. unfold sub in *. cbn [skipn nth]. apply IH. lia.
Qed.
