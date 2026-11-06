(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Ref Require Import RSegs. (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import F_syscalls MallocRep F_malloc_free.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos37Corelib4Init5Logichf2eq01Z79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentdF_malloc_free~~~~~~jb3sxv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent9MallocRep~~~~~~o72wz35stdpp9bitvectorbdefinitionsse7Z_to_bvse2bvse8bv_swrap46Stdlib6ZArith6BinInt1Zhg57testbit37Corelib4Init9Datatypeshi84boolhf3andhg52lehg52lthg53powhf2orhg53addhg56modulohg53subhg53lebhi85falsehg54landhg53mulhg53opphf2ex79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~hq96lowbithq95ctz32sebbv_unsigned79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~ig83le4hi84list" s.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma swrap_word : ltac2:(zQ "80!h9!j3!j8!o1!s9!ub!v5!va>1x$2@3$1@1$6@1$0#k0@2$5@1$0#k0@2$7@1$0#i0^1@1$4@1$3^1").
Proof. intros x. unfold wz, sxv. rewrite Z_to_bv_mod64. reflexivity. Qed.

Lemma sxv_testbit_lo' : ltac2:(zQ "80!j8!hhd!hk0!hk8!j3!o1!hke!hl4>1v$0>1i$0>0@2$3@2$6Z^1@2$7^1+i0@3$4$2@2$1@1$5^3^2@2$1^3^2").
Proof. intros v i.
  intros. rewrite <- (Z.mod_pow2_bits_low (sxv v) 32 i) by lia. rewrite sxv_mod32. apply Z.mod_pow2_bits_low. lia.
Qed.

(* [comment removed for export] *)
Lemma sxv_cases' : ltac2:(zQ "b0!hla!j8!hk8!j3!o1!hm1!hm6!hke!hl4!hmd!hn7>1v$1=1u$1@2$9^1@2$0+2+i0@2$5@2$2@2$8^1@2$0+2+hf@3$3$1@1$4^2^1@2$2@2$7@2$0+2+hf^1@3$3$1@1$4^2@2$a@2$6^1@2$0+2+k0@2$0+2+i0").
Proof. intros v.
  cbv zeta. pose proof (Z.mod_pos_bound v (2^32) ltac:(lia)).
  rewrite <- (sxv_congr (v mod 2^32) v) by (apply Z.mod_mod; lia).
  destruct (sxv_cases (v mod 2^32) ltac:(lia)); tauto.
Qed.

Lemma testbit_31_mod32 : ltac2:(zQ "70!hla!hk0!j3!j8!hne!hmd!hhd>1v$3@3$2$1@2$6^1+hf@2$4@2$0+2+hf@2$5^1@2$0+2+i0").
Proof. intros v.
  rewrite <- (Z.mod_pow2_bits_low v 32 31) by lia. rewrite Z.testbit_eqb by lia.
  pose proof (Z.mod_pos_bound v (2^32) ltac:(lia)).
  destruct (Z.leb_spec (2^31) (v mod 2^32)).
  - replace (v mod 2^32 / 2^31) with 1 by (Z.div_mod_to_equations; nia). reflexivity.
  - rewrite Z.div_small by lia. reflexivity.
Qed.

Lemma sxv_testbit_hi : ltac2:(zQ "80!j8!hhd!hk0!hk8!j3!o1!hke!hl4>1v$0>1i$0>0@2$3@2$6+hf^1@2$7^1+k0@3$4$2@2$1@1$5^3^2@2$1^3+hf").
Proof. intros v i.
  intros Hi. rewrite testbit_31_mod32. rewrite Z.testbit_eqb by lia.
  assert (P31 : 2^31 <= 2^i) by (apply Z.pow_le_mono_r; lia).
  assert (P63 : 2^i <= 2^63) by (apply Z.pow_le_mono_r; lia).
  assert (E64 : 2^64 = 2^(64-i) * 2^i) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  assert (E2 : 2^(64-i) = 2 * 2^(64-i-1)) by (rewrite <- Z.pow_succ_r by lia; f_equal; lia).
  assert (P1 : 1 <= 2^(64-i-1)) by (apply Z.pow_le_mono_r with (b:=0) in Hi || idtac; apply (Z.pow_le_mono_r 2 0); lia).
  destruct (sxv_cases' v) as [[Hu E]|[Hu E]]; rewrite E.
  - rewrite Z.div_small by lia. cbn. symmetry. apply Z.leb_gt. lia.
  - pose proof (Z.mod_pos_bound v (2^32) ltac:(lia)).
    replace ((v mod 2^32 + 2^64 - 2^32) / 2^i) with (2^(64-i) - 1) by (Z.div_mod_to_equations; nia).
    rewrite E2. replace (2 * 2^(64-i-1) - 1) with (1 + (2^(64-i-1) - 1) * 2) by lia.
    rewrite Z.mod_add by lia. cbn. symmetry. apply Z.leb_le. lia.
Qed.

Lemma sxv_testbit_high : ltac2:(zQ "70!j8!hk0!ho5!j3!o1!hke!hhd>1v$0>1i$0>0@2$5+k0^1@3$3$1@2$6@1$4^3^2$2").
Proof. intros v i.
  intros. pose proof (sxv_range v). destruct (Z.eq_dec (sxv v) 0) as [->|]. apply Z.bits_0.
  apply Z.bits_above_log2; [lia|]. apply (Z.lt_le_trans _ 64); [apply Z.log2_lt_pow2; lia | lia].
Qed.

Lemma sxv_land : ltac2:(zQ "40!j8!o1!hoe!j3>1a$0>1b$0@3$3$0@2$2@1$1^2@1$1^1@1$1@2$2^2^1").
Proof. intros a b.
  apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
  destruct (Z.lt_ge_cases i 32); [| destruct (Z.lt_ge_cases i 64)].
  - rewrite !sxv_testbit_lo' by lia. symmetry. apply Z.land_spec.
  - rewrite !sxv_testbit_hi by lia. rewrite Z.land_spec. reflexivity.
  - rewrite !sxv_testbit_high by lia. reflexivity.
Qed.

Lemma sxv_idem : ltac2:(zQ "30!o1!j8!j3>1v$1@3$2$1@1$0@1$0^1@1$0^1").
Proof. intros v. apply sxv_congr. apply sxv_mod32. Qed.

(* [comment removed for export] *)
Lemma land_opp_odd : ltac2:(zQ "60!j8!hm6!hp6!j3!hoe!hpd>1a$0@3$3$0@2$4@2$1@2$2+2^1+1@1$5@2$1@2$2+2^1+1+1").
Proof. intros a.
  apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec.
  rewrite Z.bits_opp by lia. replace (Z.pred (2 * a + 1)) with (2 * a) by lia.
  destruct (Z.eq_dec n 0) as [->|].
  - rewrite Z.testbit_odd_0, Z.testbit_even_0. reflexivity.
  - replace n with (Z.succ (n - 1)) by lia. rewrite Z.testbit_odd_succ, Z.testbit_even_succ by lia.
    rewrite andb_negb_r. change 1 with (2^0). rewrite Z.pow2_bits_eqb by lia. symmetry. apply Z.eqb_neq. lia.
Qed.

Lemma land_opp_even : ltac2:(zQ "50!hp6!j8!hoe!hpd!j3>1a$1@3$4$1@2$2@2$0+2^1@1$3@2$0+2^1@2$0+2@2$2^1@1$3^1").
Proof. intros a.
  apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec. replace (- (2 * a)) with (2 * (- a)) by lia.
  destruct (Z.eq_dec n 0) as [->|].
  - rewrite !Z.testbit_even_0. reflexivity.
  - replace n with (Z.succ (n - 1)) by lia. rewrite !Z.testbit_even_succ by lia. symmetry. apply Z.land_spec.
Qed.

Lemma lowbit_pow2 : ltac2:(zQ "90!j8!hk8!hke!hla!j3!hq4!hoe!hl4!hpd>1m$0>0@2$7Z^1@2$5$0\1k$0@2$1@2$2Z^1@2$1@3$4$0@2$6^3@1$8^3@2$3+2^1@2$2@2$3+2^1^3").
Proof.
  intros m Hm.
  pose proof (Wf_Z.Zlt_0_ind (fun x => 0 < x -> exists k, 0 <= k /\ Z.land x (- x) = 2 ^ k /\ 2 ^ k <= x)) as G.
  cbv beta in G. apply G; [|lia|lia]. clear G m Hm.
  intros x IH Hx0 Hx.
  destruct (Z.Even_or_Odd x) as [[a ->]|[a ->]].
  - ndestruct (IH a ltac:(lia) ltac:(lia)) as (k & Hk & E & L).
    exists (k + 1). rewrite land_opp_even, E, Z.pow_add_r by lia. change (2^1) with 2. lia.
  - exists 0. rewrite land_opp_odd. change (2^0) with 1. lia.
Qed.

Lemma land_opp_pow2 : ltac2:(zQ "60!hla!j8!j3!hoe!hke!hpd>1k$1>0@2$4Z^1@3$2$1@2$3@2$0+2^2@1$5@2$0+2^2@2$0+2^2").
Proof. intros k.
  intros Hk. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_opp, Z.pow2_bits_eqb by lia.
  rewrite <- Z.ones_equiv, Z.testbit_ones by lia.
  destruct (Z.eqb_spec k n); cbn [andb]; [|reflexivity].
  subst. replace (n <? n) with false by (symmetry; apply Z.ltb_irrefl). destruct (0 <=? n); reflexivity.
Qed.

(* [comment removed for export] *)
Lemma lowbit_nonzero : ltac2:(zQ "80!j8!hk8!hke!hla!j3!hq4!hu7!hl4>1m$0>0@2$7Z^1@2$5$0\1k$0@2$1@2$2Z^1@2$1@3$4$0@1$6^3@2$3+2^1@2$2@2$3+2^1^3").
Proof. intros m. intros. unfold lowbit. apply lowbit_pow2. assumption. Qed.

Lemma lowbit_0 : ltac2:(zQ "30!j3!j8!hu7@3$0$1@1$2ZZ").
Proof. reflexivity. Qed.

Lemma ctz32_pow2 : ltac2:(zQ "50!j8!j3!hv1!hke!hla>1k$0>0@2$3Z^1@3$1$0@1$2@2$4+2^2^2").
Proof. intros k. intros. unfold ctz32, lowbit. rewrite land_opp_pow2 by lia. apply Z.log2_pow2. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma negw_and_lowbit : ltac2:(zQ "h00!h9!o1!s9!hva!ub!hk8!j3!j8!hu7!hoe!hke!hl4!hla!hn7!v5!va>1v$7>0@2$5@2$aZ^1@2$b^1@2$c+2+i0@3$6@1$e@1$0#k0@2$4@1$0#k0@2$9@2$3@1$0#k0@2$4@1$0#k0@2$f@1$0#i0@2$dZ@2$3@1$0#k0@1$2@1$1^2@2$3@1$0#k0@1$2@1$1^2@1$2@1$1@1$8^2").
Proof. intros v.
  intros Hv. rewrite swrap_word. rewrite !wz_unsigned by apply sxv_range.
  rewrite sxv_land. unfold lowbit, wz. f_equal.
  rewrite (Z.land_comm v (- v)).
  transitivity (sxv (Z.land (sxv (0 - sxv v)) (sxv v))); [rewrite sxv_land, sxv_idem; reflexivity|].
  transitivity (sxv (Z.land (sxv (- v)) (sxv v))); [| rewrite sxv_land, sxv_idem; reflexivity].
  f_equal. f_equal. apply sxv_congr.
  rewrite <- Zminus_mod_idemp_r, sxv_mod32, Zminus_mod_idemp_r. replace (0 - v) with (- v) by lia. reflexivity.
Qed.

(* [comment removed for export] *)
  (* [comment removed for export] *)

(* [comment removed for export] *)

Lemma le4_avail_sub : ltac2:(zQ "d0!o1!j8!s9!ik2!hke!hn7!ik9!hk8!j3!h9!hl4!hla!v5>1a$1>1b$1>0@2$7@2$4Z^1@2$4^1^2>0@2$a^3@2$b+2+i0@3$8@1$6@1$c@1$9#8@1$3@1$2@1$0@2$5@1$0^4@1$0^3@1$3@1$2@2$5^4^3").
Proof. intros a b.
  intros. apply le4_congr. rewrite !wz_unsigned by (first [apply sxv_range | lia]).
  rewrite sxv_mod32, <- Zminus_mod_idemp_r, sxv_mod32, <- Zminus_mod_idemp_l, sxv_mod32, Zminus_mod_idemp_l, Zminus_mod_idemp_r.
  reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac mem_after_store ::=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m (wa (?A + Z.of_nat ?kn)) ?bs) ?ro) =>
    let c' := cell_of_bytes bs in
    let n := eval cbv in (csize c') in
    lazymatch goal with
    | H : rw_cells segs m A ?cs0 |- _ =>
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          let HB := fresh "HB" in
          pose proof (rw_cells_bound segs m A cs H) as HB; cbn [cells_size csize Nat.add] in HB;
          try lazymatch goal with
          | HI : mem_inv segs m |- _ =>
              apply (mem_inv_store_cbytes segs m (wa (A + Z.of_nat kn)) c') in HI;
              [ | exact I | apply (rw_cells_store_ok segs m A cs kn c0 _ H); [cells_cbv; reflexivity | reflexivity] ]
          end;
          change bs with (cbytes c');
          let H' := fresh "CH" in
          pose proof (rw_cells_write segs m A cs kn c0 c' H ltac:(cells_cbv; reflexivity) ltac:(reflexivity) I) as H';
          clear H;
          cbv beta iota zeta delta [cell_upd csize Nat.eqb Nat.sub] in H';
          transport_chunks segs m (A + Z.of_nat kn)%Z (cbytes c');
          footprint_after_store segs m (A + Z.of_nat kn)%Z (cbytes c');
          let m' := fresh "m" in
          let E := fresh "EQ" m' in
          remember (write_to_mem m (wa (A + Z.of_nat kn)) (cbytes c')) as m' eqn:E;
          clear HB; try rename H' into H
        end
    end
  end.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac mem_after_store ::=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m (wa (?A + Z.of_nat ?kn)) ?bs) ?ro) =>
    let c' := cell_of_bytes bs in
    let n := eval cbv in (csize c') in
    lazymatch goal with
    | H : rw_cells segs m A ?cs0 |- _ =>
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          let HB := fresh "HB" in
          pose proof (rw_cells_bound segs m A cs H) as HB; cbn [cells_size csize Nat.add] in HB;
          try lazymatch goal with
          | HI : mem_inv segs m |- _ =>
              apply (mem_inv_store_cbytes segs m (wa (A + Z.of_nat kn)) c') in HI;
              [ | exact I | apply (rw_cells_store_ok segs m A cs kn c0 _ H); [cells_cbv; reflexivity | reflexivity] ]
          end;
          change bs with (cbytes c');
          let H' := fresh "CH" in
          pose proof (rw_cells_write segs m A cs kn c0 c' H ltac:(cells_cbv; reflexivity) ltac:(reflexivity) I) as H';
          clear H;
          cbv beta iota zeta delta [cell_upd csize Nat.eqb Nat.sub] in H';
          transport_chunks segs m (A + Z.of_nat kn)%Z (cbytes c');
          footprint_after_store segs m (A + Z.of_nat kn)%Z (cbytes c');
          let m' := fresh "m" in
          remember (write_to_mem m (wa (A + Z.of_nat kn)) (cbytes c')) as m' eqn:Heqm;
          clear Heqm; clear HB; try clear m; try rename H' into H
        end
    end
  end.
(* [comment removed for export] *)
