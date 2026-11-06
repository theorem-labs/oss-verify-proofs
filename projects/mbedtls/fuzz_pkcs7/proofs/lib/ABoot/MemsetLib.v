(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk MemSplit MmapSim RefMemcpyLib.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_MemsetLib () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "ms_chain"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Logic.ex"; "Stdlib.Lists.List.In"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.Lists.List.incl"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.bool"; "ms_cov"; "Corelib.Init.Datatypes.true"; "Corelib.Init.Datatypes.nat"; "Stdlib.ZArith.BinInt.Z.of_nat"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "OSSVerify.KrLib.ABoot.CatExec.wbytes"; "CFill.cfill"; "OSSVerify.KrLib.ABoot.Hoare.at_"; "Corelib.Lists.ListDef.repeat"; "Corelib.Init.Datatypes.cons"; "Stdlib.ZArith.BinInt.Z.to_nat"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.store_ok"; "Stdlib.ZArith.BinInt.Z.pow"; "OSSVerify.KrLib.ABoot.PropExec.v_sub"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.sub"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.fetch_word"; "Corelib.Init.Datatypes.Some"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.is_ecall"; "Corelib.Init.Datatypes.false"; "LinuxProcessSemantics.Riscv.Instr.instr"; "LinuxProcessSemantics.Riscv.DecodeC.decode_any"; "LinuxProcessSemantics.Riscv.Instr.Op32"; "LinuxProcessSemantics.Riscv.Instr.ALU_SUB"; "LinuxProcessSemantics.Riscv.Prelude.bv_eqb"; "stdpp.bitvector.definitions.BV"; "Corelib.Init.Logic.I"; "OSSVerify.KrLib.ABoot.PropExec.v_subw"; "OSSVerify.KrLib.ABoot.PropExec.getr"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_result"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.step"; "OSSVerify.KrLib.ABoot.PropExec.mkst"; "asanreflect_fx"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.MachineOk"; "OSSVerify.KrLib.ABoot.PropExec.regupd"; "OSSVerify.KrLib.ABoot.PropExec.v_addi"; "LinuxProcessSemantics.Riscv.Instr.Mul"; "LinuxProcessSemantics.Riscv.Instr.M_MULHU"; "OSSVerify.KrLib.ABoot.PropExec.v_mulhu"; "LinuxProcessSemantics.Riscv.Instr.Op"; "LinuxProcessSemantics.Riscv.Instr.ALU_OR"; "OSSVerify.KrLib.ABoot.PropExec.v_or"; "LinuxProcessSemantics.Riscv.Instr.Store"; "LinuxProcessSemantics.Riscv.Instr.SZ1"; "stdpp.bitvector.definitions.bv_signed"; "cfill"; "cbyte"; "LinuxProcessSemantics.Riscv.Instr.SZ4"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.word_to_le_bytes"; "LinuxProcessSemantics.Riscv.Instr.SZ8"; "ms_agree"; "ms_clob"].


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ms_inb (i : Z) (iv : Z * Z) : bool := (fst iv <=? i) && (i <? fst iv + snd iv).
Definition ms_cov (L : list (Z * Z)) (i : Z) : bool := existsb (ms_inb i) L.

Lemma ms_inb_true : forall i o m, ms_inb i (o, m) = true <-> o <= i < o + m.
Proof.
  intros i o m. unfold ms_inb. cbn [fst snd]. rewrite andb_true_iff, Z.leb_le, Z.ltb_lt. tauto.
Qed.

Lemma ms_cov_cons : forall iv L i, ms_cov (iv :: L) i = ms_inb i iv || ms_cov L i.
Proof. reflexivity. Qed.

Lemma ms_cov_app : forall L1 L2 i, ms_cov (L1 ++ L2) i = ms_cov L1 i || ms_cov L2 i.
Proof. intros. unfold ms_cov. apply existsb_app. Qed.

Lemma ms_cov_In : forall L i o m, In (o, m) L -> o <= i < o + m -> ms_cov L i = true.
Proof.
  intros L i o m Hin Hi. unfold ms_cov. apply existsb_exists. exists (o, m). split; [exact Hin|].
  apply ms_inb_true. exact Hi.
Qed.

(* [comment removed for export] *)
Fixpoint ms_chain (from to : Z) (L : list (Z * Z)) : Prop :=
  match L with
  | [] => to <= from
  | (o, m) :: L' => o <= from /\ ms_chain (o + m) to L'
  end.

Lemma ms_chain_cov : ltac2:(CDefT.buildp (gd_tbl_MemsetLib ()) "PL,(0.(1.$2.$2.))Pfrom,$2.Pto,$2.Pi,$2.P,(3.R3.R2.R4.)P,(4.(5.R4.R2.)(6.R2.R3.))(7.$2.Lo,$2.(7.$2.Lm,$2.(4.(8.(1.$2.$2.)(9.$2.$2.R2.R1.)R8.)(4.(5.R2.R5.)(6.R5.(:.R2.R1.))))))")
(* [comment removed for export] *).
Proof.
  induction L as [|[o m] L IH]; intros from to i Hc Hi; cbn [ms_chain] in Hc.
  - lia.
  - destruct Hc as [Ho Hc].
    destruct (Z.lt_ge_cases i (o + m)) as [Hlt|Hge].
    + exists o, m. split; [left; reflexivity | lia].
    + destruct (IH (o + m) to i Hc ltac:(lia)) as (o' & m' & Hin & Hi').
      exists o', m'. split; [right; exact Hin | exact Hi'].
Qed.

(* [comment removed for export] *)
Lemma ms_cov_by_chain : ltac2:(CDefT.buildp (gd_tbl_MemsetLib ()) "PL,(0.(1.$2.$2.))PL',(0.(1.$2.$2.))Pn,$2.P,(;.(1.$2.$2.)R2.R3.)P,(3.=R2.R3.)Pi,$2.P,(4.(5.=R1.)(6.R1.R4.))(<.$=.(>.R7.R2.)$?.)")
(* [comment removed for export] *).
Proof.
  intros L L' n Hincl Hc i Hi.
  destruct (ms_chain_cov L' 0 n i Hc Hi) as (o & m & Hin & Hom).
  apply (ms_cov_In L i o m); [apply Hincl, Hin | exact Hom].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section CFill.
  Variable mem0 : word -> option byte.
  Variable d : word.
  Variable n : Z.
  Variable c : byte.
  Hypothesis Hn : 0 <= n.
  Hypothesis Hnw : bv_unsigned d + n < 2 ^ 64.

  Definition cfill (L : list (Z * Z)) : word -> option byte :=
    fun x => if (bv_unsigned d <=? bv_unsigned x) && (bv_unsigned x <? bv_unsigned d + n)
                && ms_cov L (bv_unsigned x - bv_unsigned d)
             then Some c else mem0 x.

  #[using="Type"] Lemma cfill_nil : cfill [] = mem0.
  Proof.
    apply functional_extensionality. intro x. unfold cfill. cbn [ms_cov existsb].
    rewrite andb_false_r. reflexivity.
  Qed.

  #[using="Type"] Lemma cfill_grows : forall L, mem_grows mem0 (cfill L).
  Proof.
    intros L x Hx. unfold cfill. destruct (_ && _); [discriminate | exact Hx].
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma cfill_ext : forall L1 L2,
    (forall i, 0 <= i < n -> ms_cov L1 i = ms_cov L2 i) -> cfill L1 = cfill L2.
  Proof.
    intros L1 L2 H. apply functional_extensionality. intro x. unfold cfill.
    destruct (Z.leb_spec (bv_unsigned d) (bv_unsigned x)); [|reflexivity].
    destruct (Z.ltb_spec (bv_unsigned x) (bv_unsigned d + n)); [|reflexivity].
    cbn [andb]. rewrite H by lia. reflexivity.
  Qed.

  (* [comment removed for export] *)
  #[using="Hnw"] Lemma cfill_store : ltac2:(CDefT.buildp (gd_tbl_MemsetLib ()) "PL,(0.(1.$2.$2.))Po,$2.Pm,$10.P,(5.=R2.)P,(5.(:.R3.(11.R2.))Vn,)(<.P,(12.&40.)(13.(12.&8.))(14.(15.R5.)(16.Vd,R4.)(17.(12.&8.)Vc,R3.))(15.(18.(1.$2.$2.)(9.$2.$2.R4.(11.R3.))R5.)))")
(* [comment removed for export] *).
  Proof.
    intros L o m Ho Hm. apply functional_extensionality. intro x.
    pose proof (u64_range d). pose proof (u64_range x).
    assert (Ha : bv_unsigned (at_ d o) = bv_unsigned d + o) by (apply at_u; lia).
    destruct (Z.lt_ge_cases (bv_unsigned x) (bv_unsigned d + o)) as [Hlo|Hge];
      [| destruct (Z.lt_ge_cases (bv_unsigned x) (bv_unsigned d + o + Z.of_nat m)) as [Hin|Hhi]].
    - rewrite wbytes_outside by (rewrite repeat_length, Ha; lia).
      unfold cfill. rewrite ms_cov_cons.
      replace (ms_inb (bv_unsigned x - bv_unsigned d) (o, Z.of_nat m)) with false
        by (symmetry; apply not_true_iff_false; rewrite ms_inb_true; lia).
      reflexivity.
    - rewrite wbytes_inside by (rewrite repeat_length, Ha; lia).
      rewrite nth_repeat_lt by (rewrite Ha; lia). unfold cfill. rewrite ms_cov_cons.
      replace (ms_inb (bv_unsigned x - bv_unsigned d) (o, Z.of_nat m)) with true
        by (symmetry; apply ms_inb_true; lia).
      destruct (Z.leb_spec (bv_unsigned d) (bv_unsigned x)); [|lia].
      destruct (Z.ltb_spec (bv_unsigned x) (bv_unsigned d + n)); [|lia].
      reflexivity.
    - rewrite wbytes_outside by (rewrite repeat_length, Ha; lia).
      unfold cfill. rewrite ms_cov_cons.
      replace (ms_inb (bv_unsigned x - bv_unsigned d) (o, Z.of_nat m)) with false
        by (symmetry; apply not_true_iff_false; rewrite ms_inb_true; lia).
      reflexivity.
  Qed.

  (* [comment removed for export] *)
  #[using="Hn Hnw"] Lemma cfill_full : ltac2:(CDefT.buildp (gd_tbl_MemsetLib ()) "PL,(0.(1.$2.$2.))P,Pi,$2.P,(4.(5.=R1.)(6.R1.Vn,))(<.$=.(>.R3.R2.)$?.)(<.P,(12.&40.)(13.(12.&8.))(15.R2.)(14.Vmem0,Vd,(17.(12.&8.)Vc,(19.Vn,))))")
(* [comment removed for export] *).
  Proof.
    intros L Hcov. apply functional_extensionality. intro x.
    pose proof (u64_range d). pose proof (u64_range x).
    unfold cfill.
    destruct (Z.leb_spec (bv_unsigned d) (bv_unsigned x)) as [H1|H1].
    - destruct (Z.ltb_spec (bv_unsigned x) (bv_unsigned d + n)) as [H2|H2]; cbn [andb].
      + rewrite Hcov by lia. rewrite wbytes_inside by (rewrite repeat_length; lia).
        rewrite nth_repeat_lt by lia. reflexivity.
      + rewrite wbytes_outside by (rewrite repeat_length; lia). reflexivity.
    - cbn [andb]. rewrite wbytes_outside by (rewrite repeat_length; lia). reflexivity.
  Qed.

  #[using="Hn Hnw"] Lemma cfill_full_chain : ltac2:(CDefT.buildp (gd_tbl_MemsetLib ()) "PL,(0.(1.$2.$2.))PL',(0.(1.$2.$2.))P,(;.(1.$2.$2.)R1.R2.)P,(3.=Vn,R2.)(<.P,(12.&40.)(13.(12.&8.))(15.R4.)(14.Vmem0,Vd,(17.(12.&8.)Vc,(19.Vn,))))")
(* [comment removed for export] *).
  Proof. intros L L' Hi Hc. apply cfill_full. apply (ms_cov_by_chain L L'); assumption. Qed.

  (* [comment removed for export] *)
  #[using="Hnw"] Lemma cfill_store_ok : ltac2:(CDefT.buildp (gd_tbl_MemsetLib ()) "Psegs,(0.$1:.)PL,(0.(1.$2.$2.))Po,$2.Pm,$10.P,(<.$=.(1;.R4.Vmem0,Vd,(19.Vn,))$?.)P,(5.=R3.)P,(5.(:.R4.(11.R3.))Vn,)(<.$=.(1;.R7.(15.R6.)(16.Vd,R5.)R4.)$?.)")
(* [comment removed for export] *).
  Proof.
    intros segs L o m Hok Ho Hm. pose proof (u64_range d).
    apply (store_ok_mono segs m mem0); [apply cfill_grows|].
    apply (store_ok_sub segs mem0 d (at_ d o) (Z.to_nat n) m); try (rewrite ?at_u; lia). exact Hok.
  Qed.
End CFill.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma mod4_mod_pow2_gen : forall t k j, 0 <= j <= k -> (t mod 2 ^ k) mod 2 ^ j = t mod 2 ^ j.
Proof.
  intros t k j Hk. apply Z.mod_mod_divide.
  exists (2 ^ (k - j)). rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.

(* [comment removed for export] *)
Definition cbyte (cv : word) : byte := Z_to_bv 8 (bv_unsigned cv).
(* [comment removed for export] *)
Definition cbz (cv : word) : Z := bv_unsigned cv mod 256.
(* [comment removed for export] *)
Definition c32 (cv : word) : word := Z_to_bv 64 (cbz cv * 16843009).
(* [comment removed for export] *)
Definition c32h (cv : word) : word := Z_to_bv 64 (cbz cv * 16843009 * 2 ^ 32).
(* [comment removed for export] *)
Definition c64 (cv : word) : word := Z_to_bv 64 (cbz cv * 72340172838076673).

Lemma cbz_range : forall cv, 0 <= cbz cv < 256.
Proof. intros cv. unfold cbz. apply Z.mod_pos_bound. lia. Qed.

Lemma cbyte_mod : forall cv, Z_to_bv 8 (bv_unsigned cv mod 256) = cbyte cv.
Proof.
  intros cv. unfold cbyte. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap8_mod. apply Z.mod_mod. lia.
Qed.

Lemma cbyte_cbz : forall cv, cbyte cv = Z_to_bv 8 (cbz cv).
Proof. intros cv. unfold cbz. symmetry. apply cbyte_mod. Qed.

(* [comment removed for export] *)
Lemma cbyte_Z : forall z, cbyte (Z_to_bv 64 z) = Z_to_bv 8 z.
Proof.
  intros z. unfold cbyte. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap8_mod, bv_wrap64_mod.
  apply mod4_mod_pow2_gen. lia.
Qed.

(* [comment removed for export] *)
Fixpoint ms_repl (k : nat) : Z := match k with O => 0 | S k' => 1 + 256 * ms_repl k' end.

Lemma ms_repl_nonneg : forall k, 0 <= ms_repl k.
Proof. induction k; cbn [ms_repl]; lia. Qed.

Lemma Z_to_le_bytes_ms_repl : forall k z, 0 <= z < 256 ->
  Z_to_le_bytes k (z * ms_repl k) = repeat (Z_to_bv 8 z) k.
Proof.
  induction k as [|k IH]; intros z Hz; [reflexivity|].
  cbn [Z_to_le_bytes ms_repl repeat]. pose proof (ms_repl_nonneg k). f_equal.
  - apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap8_mod.
    replace (z * (1 + 256 * ms_repl k)) with (z + (z * ms_repl k) * 256) by lia.
    rewrite Z.mod_add by lia. reflexivity.
  - rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
    replace (z * (1 + 256 * ms_repl k)) with (z + (z * ms_repl k) * 256) by lia.
    rewrite Z.div_add by lia. rewrite Z.div_small by lia. rewrite Z.add_0_l. apply IH. exact Hz.
Qed.

Lemma u_c32 : forall cv, bv_unsigned (c32 cv) = cbz cv * 16843009.
Proof. intros cv. pose proof (cbz_range cv). unfold c32. apply u_Z2bv; lia. Qed.

Lemma u_c32h : forall cv, bv_unsigned (c32h cv) = cbz cv * 16843009 * 2 ^ 32.
Proof. intros cv. pose proof (cbz_range cv). unfold c32h. apply u_Z2bv; lia. Qed.

Lemma u_c64 : forall cv, bv_unsigned (c64 cv) = cbz cv * 72340172838076673.
Proof. intros cv. pose proof (cbz_range cv). unfold c64. apply u_Z2bv; lia. Qed.

Lemma wleb4_c32 : forall cv, word_to_le_bytes 4 (c32 cv) = repeat (cbyte cv) 4.
Proof.
  intros cv. unfold word_to_le_bytes. rewrite u_c32, cbyte_cbz.
  change 16843009 with (ms_repl 4). apply Z_to_le_bytes_ms_repl. apply cbz_range.
Qed.

Lemma wleb8_c64 : forall cv, word_to_le_bytes 8 (c64 cv) = repeat (cbyte cv) 8.
Proof.
  intros cv. unfold word_to_le_bytes. rewrite u_c64, cbyte_cbz.
  change 72340172838076673 with (ms_repl 8). apply Z_to_le_bytes_ms_repl. apply cbz_range.
Qed.

(* [comment removed for export] *)
Lemma u_slli56 : forall cv, bv_unsigned (v_slli cv 56) = cbz cv * 2 ^ 56.
Proof.
  intros cv. unfold v_slli, cbz. rewrite Z_to_bv_unsigned, Z.shiftl_mul_pow2 by lia.
  pose proof (u64_range cv).
  unfold bv_wrap. change (bv_modulus 64) with (2 ^ 56 * 256).
  rewrite Z.mul_comm, Z.mul_mod_distr_l by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma mulhu_c32 : forall cv (m : word), bv_unsigned m = 4311810304 ->
  v_mulhu (v_slli cv 56) m = c32 cv.
Proof.
  intros cv m Hm. unfold v_mulhu, c32. f_equal. rewrite u_slli56, Hm.
  rewrite Z.shiftr_div_pow2 by lia.
  replace (cbz cv * 2 ^ 56 * 4311810304) with ((cbz cv * 16843009) * 2 ^ 64) by lia.
  apply Z.div_mul. lia.
Qed.

Lemma slli32_c32 : forall cv, v_slli (c32 cv) 32 = c32h cv.
Proof.
  intros cv. unfold v_slli, c32h. f_equal. rewrite u_c32, Z.shiftl_mul_pow2 by lia. reflexivity.
Qed.

Lemma srli32_c32h : forall cv, v_srli (c32h cv) 32 = c32 cv.
Proof.
  intros cv. unfold v_srli, c32. f_equal. rewrite u_c32h, Z.shiftr_div_pow2 by lia.
  apply Z.div_mul. lia.
Qed.

Lemma lor_disjoint_shift32 : forall a b, 0 <= a -> 0 <= b < 2 ^ 32 ->
  Z.lor (a * 2 ^ 32) b = a * 2 ^ 32 + b.
Proof.
  intros a b Ha Hb.
  assert (Hl : Z.land (a * 2 ^ 32) b = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i 32).
    - rewrite <- Z.shiftl_mul_pow2, Z.shiftl_spec by lia. rewrite (Z.testbit_neg_r a) by lia. reflexivity.
    - rewrite (Z_testbit_high 32 b) by lia. apply andb_false_r. }
  rewrite <- Z.lxor_lor by exact Hl. symmetry. apply Z.add_nocarry_lxor. exact Hl.
Qed.

Lemma or_c64 : forall cv, v_or (c32h cv) (c32 cv) = c64 cv.
Proof.
  intros cv. pose proof (cbz_range cv). unfold v_or, c64. f_equal. rewrite u_c32h, u_c32.
  rewrite lor_disjoint_shift32 by lia. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma mod4_mod_pow2' : forall t k, 2 <= k -> (t mod 2 ^ k) mod 4 = t mod 4.
Proof.
  intros t k Hk. apply Z.mod_mod_divide.
  exists (2 ^ (k - 2)). change 4 with (2 ^ 2). rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma negw_and3 : forall x : word,
  v_andi (v_subw (Z_to_bv 64 0) x) 3 = Z_to_bv 64 ((- bv_unsigned x) mod 4).
Proof.
  intros x. unfold v_andi, v_subw. f_equal.
  change (bv_wrap 64 3) with (Z.ones 2). rewrite Z.land_ones by lia.
  rewrite Z_to_bv_unsigned. change (bv_unsigned (Z_to_bv 64 0)) with 0.
  unfold bv_swrap. rewrite bv_wrap64_mod.
  change (bv_half_modulus 32) with (2 ^ 31).
  unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32). change (2 ^ 2) with 4.
  rewrite mod4_mod_pow2' by lia.
  rewrite <- Zminus_mod_idemp_l.
  rewrite mod4_mod_pow2' by lia.
  replace (0 - bv_unsigned x + 2 ^ 31) with ((- bv_unsigned x) + 536870912 * 4) by lia.
  rewrite Z.mod_add by lia.
  rewrite Zminus_mod_idemp_l.
  replace (- bv_unsigned x - 2 ^ 31) with ((- bv_unsigned x) + (- 536870912) * 4) by lia.
  rewrite Z.mod_add by lia. reflexivity.
Qed.

Lemma neg_mod4_range : forall u, 0 <= (- u) mod 4 <= 3.
Proof. intros u. pose proof (Z.mod_pos_bound (- u) 4). lia. Qed.

Lemma neg_mod4_aligns : forall u, (u + (- u) mod 4) mod 4 = 0.
Proof.
  intros u. rewrite Z.add_mod, Z.mod_mod by lia.
  rewrite <- Z.add_mod by lia. replace (u + - u) with 0 by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma land_trunc4 : forall a, 0 <= a < 2 ^ 64 -> Z.land a (2 ^ 64 - 4) = a - a mod 4.
Proof.
  intros a Ha.
  replace (2 ^ 64 - 4) with (Z.ldiff (Z.ones 64) (Z.ones 2)).
  2:{ rewrite Z.ldiff_land, <- Z.sub_land_same_l, Z.land_ones by lia.
      rewrite Z.ones_mod_pow2 by lia. rewrite !Z.ones_equiv. lia. }
  rewrite Z.ldiff_land, Z.land_assoc, Z.land_ones by lia.
  rewrite Z.mod_small by lia.
  rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia.
  rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
  pose proof (Z.div_mod a 4 ltac:(lia)). lia.
Qed.

Lemma andi_m4 : forall m, 0 <= m < 2 ^ 64 ->
  v_andi (Z_to_bv 64 m) (-4) = Z_to_bv 64 (m - m mod 4).
Proof.
  intros m Hm. unfold v_andi. f_equal. rewrite u_Z2bv by lia.
  change (bv_wrap 64 (-4)) with (2 ^ 64 - 4). apply land_trunc4. exact Hm.
Qed.

(* [comment removed for export] *)
Lemma land_4_cases : forall a, 0 <= a -> Z.land a 4 = 0 \/ Z.land a 4 = 4.
Proof.
  intros a Ha.
  destruct (Z.testbit a 2) eqn:E; [right|left];
    apply Z.bits_inj'; intros i Hi; rewrite Z.land_spec;
    change 4 with (2 ^ 2); rewrite Z.pow2_bits_eqb by lia;
    destruct (Z.eqb_spec 2 i) as [<-|Hne]; rewrite ?E, ?Z.bits_0; try reflexivity;
    apply andb_false_r.
Qed.

Lemma andi_4_cases : forall x : word, exists s4, v_andi x 4 = Z_to_bv 64 s4 /\ (s4 = 0 \/ s4 = 4).
Proof.
  intros x. exists (Z.land (bv_unsigned x) 4). split.
  - unfold v_andi. f_equal.
  - apply land_4_cases. apply u64_range.
Qed.

(* [comment removed for export] *)
Lemma ms_v_add_Z : forall (x : word) z, 0 <= z < 2 ^ 64 ->
  v_add x (Z_to_bv 64 z) = at_ x z.
Proof. intros x z Hz. unfold v_add, at_. rewrite u_Z2bv by lia. reflexivity. Qed.

Lemma ms_v_add_at_Z : forall (x : word) o z, 0 <= z < 2 ^ 64 ->
  v_add (at_ x o) (Z_to_bv 64 z) = at_ x (o + z).
Proof. intros x o z Hz. rewrite ms_v_add_Z by lia. apply at_at. Qed.

Lemma ms_v_sub_ZZ : ltac2:(CDefT.buildp (gd_tbl_MemsetLib ()) "Pa,$2.Pb,$2.P,(4.(5.=R1.)(5.R1.R2.))P,(6.R3.(1<.+2.+40.))(<.(12.&40.)(1=.(1>.&40.R4.)(1>.&40.R3.))(1>.&40.(1?.R4.R3.)))")
(* [comment removed for export] *).
Proof. intros a b H1 H2. unfold v_sub. rewrite !u_Z2bv by lia. reflexivity. Qed.

Lemma ms_v_addi_Z : forall a i, 0 <= a < 2 ^ 64 ->
  v_addi (Z_to_bv 64 a) i = Z_to_bv 64 (a + i).
Proof. intros a i Ha. unfold v_addi. rewrite u_Z2bv by lia. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ms_step_subw_at : ltac2:(CDefT.buildp (gd_tbl_MemsetLib ()) "Psegs,(0.$1:.)Pregs,(20.&5.(12.&40.))Ppc,(12.&40.)Pmem,P,(12.&40.)(13.(12.&8.))Prom,P,(12.&40.)(13.(12.&8.))Pw,(12.&20.)Prd,(12.&5.)Prs1,(12.&5.)Prs2,(12.&5.)Pv,(12.&40.)P,(<.(13.(12.&20.))(21.R:.R8.)(22.(12.&20.)R5.))P,(<.$=.(23.R6.)$24.)P,(<.(13.(1.$25.$2.))(26.R7.)(22.(1.$25.$2.)(9.$25.$2.(27.$28.R6.R5.R4.)+4.)))P,(<.$=.(29.&5.R7.(2:.&5.=$2;.))$24.)P,(<.(12.&40.)(2<.(2=.R=.R7.)(2=.R=.R6.))R5.)(<.(2>.$2?.)(30.R?.(31.$32.R>.R=.R<.R;.))(33.$2?.(31.$32.(34.R>.R9.R6.)(35.R=.+4.)R<.R;.)))")
(* [comment removed for export] *).
Proof.
  intros segs regs pc mem rom w rd rs1 rs2 v Hf He Hd Hrd Hv.
  rewrite (step_subw segs regs pc mem rom w rd rs1 rs2 Hf He Hd). rewrite Hrd, Hv. reflexivity.
Qed.

Lemma ms_step_mulhu_at : ltac2:(CDefT.buildp (gd_tbl_MemsetLib ()) "Psegs,(0.$1:.)Pregs,(20.&5.(12.&40.))Ppc,(12.&40.)Pmem,P,(12.&40.)(13.(12.&8.))Prom,P,(12.&40.)(13.(12.&8.))Pw,(12.&20.)Prd,(12.&5.)Prs1,(12.&5.)Prs2,(12.&5.)Pv,(12.&40.)P,(<.(13.(12.&20.))(21.R:.R8.)(22.(12.&20.)R5.))P,(<.$=.(23.R6.)$24.)P,(<.(13.(1.$25.$2.))(26.R7.)(22.(1.$25.$2.)(9.$25.$2.(36.$37.R6.R5.R4.)+4.)))P,(<.$=.(29.&5.R7.(2:.&5.=$2;.))$24.)P,(<.(12.&40.)(38.(2=.R=.R7.)(2=.R=.R6.))R5.)(<.(2>.$2?.)(30.R?.(31.$32.R>.R=.R<.R;.))(33.$2?.(31.$32.(34.R>.R9.R6.)(35.R=.+4.)R<.R;.)))")
(* [comment removed for export] *).
Proof.
  intros segs regs pc mem rom w rd rs1 rs2 v Hf He Hd Hrd Hv.
  rewrite (step_mulhu segs regs pc mem rom w rd rs1 rs2 Hf He Hd). rewrite Hrd, Hv. reflexivity.
Qed.

Lemma ms_step_or_at : ltac2:(CDefT.buildp (gd_tbl_MemsetLib ()) "Psegs,(0.$1:.)Pregs,(20.&5.(12.&40.))Ppc,(12.&40.)Pmem,P,(12.&40.)(13.(12.&8.))Prom,P,(12.&40.)(13.(12.&8.))Pw,(12.&20.)Prd,(12.&5.)Prs1,(12.&5.)Prs2,(12.&5.)Pv,(12.&40.)P,(<.(13.(12.&20.))(21.R:.R8.)(22.(12.&20.)R5.))P,(<.$=.(23.R6.)$24.)P,(<.(13.(1.$25.$2.))(26.R7.)(22.(1.$25.$2.)(9.$25.$2.(39.$3:.R6.R5.R4.)+4.)))P,(<.$=.(29.&5.R7.(2:.&5.=$2;.))$24.)P,(<.(12.&40.)(3;.(2=.R=.R7.)(2=.R=.R6.))R5.)(<.(2>.$2?.)(30.R?.(31.$32.R>.R=.R<.R;.))(33.$2?.(31.$32.(34.R>.R9.R6.)(35.R=.+4.)R<.R;.)))")
(* [comment removed for export] *).
Proof.
  intros segs regs pc mem rom w rd rs1 rs2 v Hf He Hd Hrd Hv.
  rewrite (step_or segs regs pc mem rom w rd rs1 rs2 Hf He Hd). rewrite Hrd, Hv. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Stores.
  Variable segs : list Segment.
  Variable mem0 : word -> option byte.
  Variable d : word.
  Variable n : Z.
  Variable cv : word.
  Hypothesis Hn : 0 <= n.
  Hypothesis Hnw : bv_unsigned d + n < 2 ^ 64.
  Hypothesis Hok : store_ok segs mem0 d (Z.to_nat n) = true.

  #[local] Abbreviation CF := (cfill mem0 d n (cbyte cv)).

  #[using="Hnw Hok"] Lemma cf_sb : ltac2:(CDefT.buildp (gd_tbl_MemsetLib ()) "Pregs,(20.&5.(12.&40.))Ppc,(12.&40.)Prom,P,(12.&40.)(13.(12.&8.))Pw,(12.&20.)Prs1,(12.&5.)Prs2,(12.&5.)Pimm,(12.&<.)PL,(0.(1.$2.$2.))Po0,$2.Po,$2.P,(<.(13.(12.&20.))(21.Vsegs,R9.)(22.(12.&20.)R7.))P,(<.$=.(23.R8.)$24.)P,(<.(13.(1.$25.$2.))(26.R9.)(22.(1.$25.$2.)(9.$25.$2.(3<.$3=.R8.R7.R6.)+4.)))P,(<.(12.&40.)(2=.R=.R9.)(16.Vd,R5.))P,(<.$2.(:.R6.(3>.&<.R8.))R5.)P,(<.(12.&40.)(2=.R?.R:.)Vcv,)P,(5.=R7.)P,(5.(:.R8.+1.)Vn,)(<.(2>.$2?.)(30.Vsegs,(31.$32.R12.R11.(3?.Vmem0,Vd,Vn,(40.Vcv,)R;.)R10.))(33.$2?.(31.$32.R12.(35.R11.+4.)(3?.Vmem0,Vd,Vn,(40.Vcv,)(18.(1.$2.$2.)(9.$2.$2.R9.+1.)R;.))R10.)))")
(* [comment removed for export] *).
  Proof.
    intros regs pc rom w rs1 rs2 imm L o0 o Hf He Hdc Hrs1 Ho Hrs2 H0 H1.
    replace ((o, 1) :: L) with ((o, Z.of_nat 1) :: L) by reflexivity.
    rewrite <- (cfill_store mem0 d n (cbyte cv) Hnw L o 1) by lia.
    eapply step_sb_at; [exact Hf | exact He | exact Hdc | | exact Hrs2 | reflexivity |].
    - rewrite Hrs1, at_addi, Ho. reflexivity.
    - apply (cfill_store_ok mem0 d n (cbyte cv) Hnw segs); assumption || lia.
  Qed.

  #[using="Hnw Hok"] Lemma cf_sw : ltac2:(CDefT.buildp (gd_tbl_MemsetLib ()) "Pregs,(20.&5.(12.&40.))Ppc,(12.&40.)Prom,P,(12.&40.)(13.(12.&8.))Pw,(12.&20.)Prs1,(12.&5.)Prs2,(12.&5.)Pimm,(12.&<.)PL,(0.(1.$2.$2.))Po0,$2.Po,$2.Pv,(12.&40.)P,(<.(13.(12.&20.))(21.Vsegs,R:.)(22.(12.&20.)R8.))P,(<.$=.(23.R9.)$24.)P,(<.(13.(1.$25.$2.))(26.R:.)(22.(1.$25.$2.)(9.$25.$2.(3<.$41.R9.R8.R7.)+4.)))P,(<.(12.&40.)(2=.R>.R:.)(16.Vd,R6.))P,(<.$2.(:.R7.(3>.&<.R9.))R6.)P,(<.(12.&40.)(2=.R10.R;.)R6.)P,(<.(0.(12.&8.))(42.#4.R7.)(17.(12.&8.)(40.Vcv,)#4.))P,(5.=R9.)P,(5.(:.R:.+4.)Vn,)(<.(2>.$2?.)(30.Vsegs,(31.$32.R14.R13.(3?.Vmem0,Vd,Vn,(40.Vcv,)R=.)R12.))(33.$2?.(31.$32.R14.(35.R13.+4.)(3?.Vmem0,Vd,Vn,(40.Vcv,)(18.(1.$2.$2.)(9.$2.$2.R;.+4.)R=.))R12.)))")
(* [comment removed for export] *).
  Proof.
    intros regs pc rom w rs1 rs2 imm L o0 o v Hf He Hdc Hrs1 Ho Hrs2 Hv H0 H1.
    replace ((o, 4) :: L) with ((o, Z.of_nat 4) :: L) by reflexivity.
    rewrite <- (cfill_store mem0 d n (cbyte cv) Hnw L o 4) by lia.
    rewrite <- Hv.
    eapply step_sw_at; [exact Hf | exact He | exact Hdc | | exact Hrs2 |].
    - rewrite Hrs1, at_addi, Ho. reflexivity.
    - apply (cfill_store_ok mem0 d n (cbyte cv) Hnw segs); assumption || lia.
  Qed.

  #[using="Hnw Hok"] Lemma cf_sd : ltac2:(CDefT.buildp (gd_tbl_MemsetLib ()) "Pregs,(20.&5.(12.&40.))Ppc,(12.&40.)Prom,P,(12.&40.)(13.(12.&8.))Pw,(12.&20.)Prs1,(12.&5.)Prs2,(12.&5.)Pimm,(12.&<.)PL,(0.(1.$2.$2.))Po0,$2.Po,$2.Pv,(12.&40.)P,(<.(13.(12.&20.))(21.Vsegs,R:.)(22.(12.&20.)R8.))P,(<.$=.(23.R9.)$24.)P,(<.(13.(1.$25.$2.))(26.R:.)(22.(1.$25.$2.)(9.$25.$2.(3<.$43.R9.R8.R7.)+4.)))P,(<.(12.&40.)(2=.R>.R:.)(16.Vd,R6.))P,(<.$2.(:.R7.(3>.&<.R9.))R6.)P,(<.(12.&40.)(2=.R10.R;.)R6.)P,(<.(0.(12.&8.))(42.#8.R7.)(17.(12.&8.)(40.Vcv,)#8.))P,(5.=R9.)P,(5.(:.R:.+8.)Vn,)(<.(2>.$2?.)(30.Vsegs,(31.$32.R14.R13.(3?.Vmem0,Vd,Vn,(40.Vcv,)R=.)R12.))(33.$2?.(31.$32.R14.(35.R13.+4.)(3?.Vmem0,Vd,Vn,(40.Vcv,)(18.(1.$2.$2.)(9.$2.$2.R;.+8.)R=.))R12.)))")
(* [comment removed for export] *).
  Proof.
    intros regs pc rom w rs1 rs2 imm L o0 o v Hf He Hdc Hrs1 Ho Hrs2 Hv H0 H1.
    replace ((o, 8) :: L) with ((o, Z.of_nat 8) :: L) by reflexivity.
    rewrite <- (cfill_store mem0 d n (cbyte cv) Hnw L o 8) by lia.
    rewrite <- Hv.
    eapply step_sd_at; [exact Hf | exact He | exact Hdc | | exact Hrs2 |].
    - rewrite Hrs1, at_addi, Ho. reflexivity.
    - apply (cfill_store_ok mem0 d n (cbyte cv) Hnw segs); assumption || lia.
  Qed.
End Stores.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ms_clob : list reg := [11; 12; 13; 14; 15; 16]%bv.
Definition ms_agree (regs regs' : bvmap 5 word) : Prop :=
  regs_agree (fun r => In r ms_clob) regs regs'.

Lemma ms_agree_refl : forall regs, ms_agree regs regs.
Proof. intros regs. apply regs_agree_refl. Qed.

Lemma ms_agree_trans : forall r1 r2 r3, ms_agree r1 r2 -> ms_agree r2 r3 -> ms_agree r1 r3.
Proof. intros r1 r2 r3. apply regs_agree_trans. Qed.

Lemma ms_agree_upd : ltac2:(CDefT.buildp (gd_tbl_MemsetLib ()) "Pregs,(20.&5.(12.&40.))Pregs',(20.&5.(12.&40.))Prd,(12.&5.)Pv,(12.&40.)P,(44.R4.R3.)P,(8.(12.&5.)R3.$45.)(44.R6.(34.R5.R4.R3.))")
(* [comment removed for export] *).
Proof. intros regs regs' rd v H Hin. apply regs_agree_upd; assumption. Qed.

Lemma ms_agree_getr : forall regs regs' (r : reg),
  ms_agree regs regs' -> ~ In r ms_clob -> getr regs' r = getr regs r.
Proof. intros regs regs' r H Hn. apply H. exact Hn. Qed.

Lemma ms_agree_keeps : forall regs regs', ms_agree regs regs' -> keeps regs regs'.
Proof.
  intros regs regs' H r Hr. apply H. unfold callee_kept in Hr. unfold ms_clob. cbn [In] in *.
  intros Hc. decompose [or] Hr; subst; decompose [or] Hc; try discriminate; auto.
Qed.

Ltac in_clob := cbn [ms_clob In]; repeat first [ left; reflexivity | right ].
Ltac solve_ms_agree :=
  repeat (apply ms_agree_upd; [| in_clob]); first [apply ms_agree_refl | assumption].
