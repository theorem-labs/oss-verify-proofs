(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac
     AxSymExec3 AxSymExec3Sound AsanPlanCore AsanPlanSoundSums L5Defs L5Core L5CoreKit. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import Bs0Sums_u Bs0_code_ra93ac_a9404_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

#[local] Abbreviation RSEGS := Ubsan.M.loaded_segments.

(* [comment removed for export] *)
Module PMCP.
Section Generic.
Variable segs : list Segment. Context {bmK : BMode}.   (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rdn_of_defined (M : word -> option byte) : forall (k : nat) (a : Z),
  0 <= a -> a + Z.of_nat k <= 2 ^ 64 -> L5.defined M a (Z.of_nat k) ->
  exists bs, rdn segs M (Z_to_bv 64 a) k = Some bs /\ length bs = k.
Proof.
  induction k as [|k IH]; intros a Ha Hk D. { exists []. split; reflexivity. }
  cbn [rdn]. pose proof (D 0 ltac:(lia)) as D0. rewrite Z.add_0_r in D0.
  destruct (M (Z_to_bv 64 a)) as [b|] eqn:E; [|congruence].
  destruct (IH (a + 1) ltac:(lia) ltac:(lia)) as (bs & RB & LB).
  { intros i Hi. replace (a + 1 + i) with (a + (1 + i)) by lia. apply D. lia. }
  replace (Z_to_bv 64 a + 1)%bv with (Z_to_bv 64 (a + 1)).
  2:{ apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. change (bv_unsigned (1%bv : bv 64)) with 1. unfold bv_wrap.
      change (bv_modulus 64) with (2 ^ 64). rewrite Zplus_mod_idemp_l. reflexivity. }
  rewrite RB. exists (b :: bs). split; [reflexivity| cbn; lia].
Qed.

(* [comment removed for export] *)
Lemma wbytes_defined (M : word -> option byte) (dst : Z) (bs : list byte) :
  0 <= dst -> dst + Z.of_nat (length bs) <= 2 ^ 64 -> L5.defined (wbytes M (Z_to_bv 64 dst) bs) dst (Z.of_nat (length bs)).
Proof.
  intros Hd Hn i Hi.
  replace (dst + i) with (bv_unsigned (Z_to_bv 64 dst) + Z.of_nat (Z.to_nat i)) by (rewrite L5.unsigned_lit by lia; lia).
  rewrite AX2S.wbytes_nth; [discriminate| rewrite L5.unsigned_lit by lia; lia| lia].
Qed.
Lemma wbytes_out (M : word -> option byte) (dst : Z) (bs : list byte) (a : Z) :
  0 <= dst < 2 ^ 64 -> dst + Z.of_nat (length bs) <= 2 ^ 64 -> 0 <= a < 2 ^ 64 -> ~ (dst <= a < dst + Z.of_nat (length bs)) ->
  wbytes M (Z_to_bv 64 dst) bs (Z_to_bv 64 a) = M (Z_to_bv 64 a).
Proof.
  intros Hd Hn Ha Hout. destruct (Z_lt_le_dec a dst) as [Lo|Hi].
  - apply wbytes_below; rewrite !L5.unsigned_lit by lia; lia.
  - apply wbytes_above. rewrite !L5.unsigned_lit by lia. lia.
Qed.

(* [comment removed for export] *)
Definition copy1_spec (pc : Z) : Prop :=
  forall (fx : FPState) mem0 (dst src : word) (n : Z) (bs : list byte) (regs : bvmap 5 word) (ret : word),
    1 <= n -> length bs = Z.to_nat n ->
    rdn segs mem0 src (length bs) = Some bs ->
    store_ok segs mem0 dst (length bs) = true ->
    (bv_unsigned dst + n <= bv_unsigned src \/ bv_unsigned src + n <= bv_unsigned dst) ->
    bv_unsigned src + n < 2 ^ 63 -> bv_unsigned dst + n < 2 ^ 63 ->
    ret_ok ret -> getr regs 1%bv = ret ->
    getr regs 10%bv = dst -> getr regs 11%bv = src -> getr regs 12%bv = Z_to_bv 64 n ->
    exists regs',
      msteps segs (@mkst fx regs (Z_to_bv 64 pc) mem0 (seg_rom segs)) (@mkst fx regs' ret (wbytes mem0 dst bs) (seg_rom segs))
      /\ APSX.kept_ok regs regs' /\ getr regs' 10%bv = dst.

Lemma copy1_of_copy_spec pc : (forall fx, @APSX.copy_spec fx segs pc) -> copy1_spec pc.
Proof.
  intros C fx mem0 dst src n bs regs ret Hn LEN RD ST AP Hs Hd RET R1 R10 R11 R12.
  apply (C fx mem0 dst src n bs regs ret); try assumption; lia.
Qed.

Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom segs)).

(* [comment removed for export] *)
Lemma copy_run (pc : Z) (CPY : copy1_spec pc) (fx : FPState) R M (dst src n r : Z) :
  getr R (reg 10) = Z_to_bv 64 dst -> getr R (reg 11) = Z_to_bv 64 src -> getr R (reg 12) = Z_to_bv 64 n ->
  getr R (reg 1) = Z_to_bv 64 r -> L5.ra_ok r ->
  1 <= n -> 0 <= dst -> dst + n < 2 ^ 63 -> 0 <= src -> src + n < 2 ^ 63 -> (dst + n <= src \/ src + n <= dst) ->
  L5.writable segs M dst n -> L5.defined M src n ->
  exists R3 M3, msteps segs (st fx R pc M) (st fx R3 r M3)
    /\ mem_grows M M3
    /\ (forall a, 0 <= a < 2 ^ 64 -> ~ (dst <= a < dst + n) -> M3 (Z_to_bv 64 a) = M (Z_to_bv 64 a))
    /\ L5.defined M3 dst n
    /\ (forall i, In i L5K.CS -> getr R3 (reg i) = getr R (reg i)) /\ getr R3 (reg 10) = Z_to_bv 64 dst.
Proof.
  intros H10 H11 H12 H1 RA Hn Hd Hdn Hs Hsn AP W D.
  destruct (rdn_of_defined M (Z.to_nat n) src Hs ltac:(lia)) as (bs & RD & LEN). { rewrite Z2Nat.id by lia. exact D. }
  destruct (CPY fx M (Z_to_bv 64 dst) (Z_to_bv 64 src) n bs R (Z_to_bv 64 r) Hn LEN
              ltac:(rewrite LEN; exact RD)
              ltac:(rewrite LEN; replace (Z_to_bv 64 dst) with (Z_to_bv 64 (dst + 0)) by (f_equal; lia); apply W; lia)
              ltac:(rewrite !L5.unsigned_lit by lia; lia) ltac:(rewrite L5.unsigned_lit by lia; lia) ltac:(rewrite L5.unsigned_lit by lia; lia)
              (L5K.ret_ok_lit r RA) H1 H10 H11 H12) as (R3 & MS & KO & A10).
  exists R3, (wbytes M (Z_to_bv 64 dst) bs). split; [exact MS|]. split; [apply wbytes_grows|].
  split. { intros a Ha Hout. apply wbytes_out; [lia| rewrite LEN; lia| exact Ha| rewrite LEN, Z2Nat.id by lia; exact Hout]. }
  split. { pose proof (wbytes_defined M dst bs Hd ltac:(rewrite LEN; lia)) as X. rewrite LEN, Z2Nat.id in X by lia. exact X. }
  split; [intros i Hi; apply (L5K.kept_ok_index R R3 i KO Hi)| exact A10].
Qed.

End Generic.
End PMCP.

(* [comment removed for export] *)
(* [comment removed for export] *)
Module PMCPS.
Open Scope bv_scope.
Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)

Lemma a4_val (n : Z) : (1 <= n < 2 ^ 62)%Z ->
  bv_unsigned (v_sub (Z_to_bv 64 0) (v_slli (Z_to_bv 64 n) 1)) = (2 ^ 64 - 2 * n)%Z.
Proof.
  intros Hn. unfold v_sub, v_slli. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64)%Z.
  rewrite (Z.mod_small n) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1)%Z with 2%Z.
  rewrite (Z.mod_small 0) by lia. rewrite (Z.mod_small (n * 2)) by lia.
  replace (0 - n * 2)%Z with (2 ^ 64 - 2 * n + (-1) * 2 ^ 64)%Z by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
Lemma a3_val (d s : word) (n : Z) : (1 <= n)%Z -> (bv_unsigned d + n < 2 ^ 63)%Z -> (bv_unsigned s + n < 2 ^ 63)%Z ->
  bv_unsigned (v_sub s (v_add (Z_to_bv 64 n) d)) = ((bv_unsigned s - bv_unsigned d - n) mod 2 ^ 64)%Z.
Proof.
  intros Hn Hdn Hsn. pose proof (bv_unsigned_in_range _ d) as Bd. pose proof (bv_unsigned_in_range _ s) as Bs.
  unfold v_sub, v_add. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64)%Z in *.
  rewrite (Z.mod_small n) by lia. rewrite (Z.mod_small (n + bv_unsigned d)) by lia.
  f_equal. lia.
Qed.

Theorem memmove_disjoint : PMCP.copy1_spec RSEGS 0xab884.
Proof.
  intros fx0 mem0 dst src n bs regs ret Hn LEN RD ST AP Hs Hd RET R1 R10 R11 R12.
  pose proof (bv_unsigned_in_range _ dst) as Bd. pose proof (bv_unsigned_in_range _ src) as Bs.
  change (bv_modulus 64) with (2 ^ 64)%Z in Bd, Bs.
  assert (NE : c_eq (getr regs 10) (getr regs 11) = false).
  { rewrite R10, R11. unfold c_eq. apply bv_eqb_neq. intros E. rewrite E in AP. lia. }
  assert (GE : c_ltu (v_sub (Z_to_bv 64 0) (v_slli (Z_to_bv 64 n) 1)) (v_sub src (v_add (Z_to_bv 64 n) dst)) = false).
  { unfold c_ltu, bv_ltu. apply Z.ltb_ge. rewrite a4_val by lia.
    rewrite a3_val by lia.
    destruct AP as [A|A].
    - rewrite Z.mod_small by lia. lia.
    - replace (bv_unsigned src - bv_unsigned dst - n)%Z with (2 ^ 64 + bv_unsigned src - bv_unsigned dst - n + (-1) * 2 ^ 64)%Z by lia.
      rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia. }
  destruct (Bs0Sums_u.src0_copy_spec_memcpy fx0 mem0 dst src n bs
              (regupd (regupd (regupd (regupd regs 13 (v_add (getr regs 12) (getr regs 10))) 14 (v_slli (getr regs 12) 1))
                              13 (v_sub (getr regs 11) (v_add (getr regs 12) (getr regs 10)))) 14 (v_sub (Z_to_bv 64 0) (v_slli (getr regs 12) 1)))
              ret ltac:(lia) LEN RD ST AP ltac:(lia) ltac:(lia) RET) as (regs' & MS & KO & A10).
  1-4: gres; assumption.
  exists regs'. split; [|split; [|exact A10]].
  - stepb_ft F_aa250 D_aa250 ltac:(exact NE).
    stepn F_aa254 D_aa254.
    stepn F_aa258 D_aa258.
    stepn F_aa25c D_aa25c.
    stepn F_aa260 D_aa260.
    stepb_tk F_aa264 D_aa264 ltac:(rewrite ?R10, ?R11, ?R12; exact GE).
    stepn F_aa2a4 D_aa2a4.
    lazymatch goal with |- msteps _ (mkst _ ?p _ _) _ => replace p with (Z_to_bv 64 0xab480) by (apply bv_eq; reflexivity) end.
    exact MS.
  - intros r Hr0 Hr. rewrite (KO r Hr0 Hr). 
    assert (r <> 13 /\ r <> 14) as (N13 & N14).
    { split; intros ->; apply Hr; vm_compute; tauto. }
    rewrite !getr_other by assumption. reflexivity.
Qed.
End FPX_1.

Lemma memcpy_copy1 : PMCP.copy1_spec RSEGS 0xab480.
Proof. apply PMCP.copy1_of_copy_spec. exact Bs0Sums_u.src0_copy_spec_memcpy. Qed.

Definition memcpy_run := PMCP.copy_run RSEGS 0xab480 memcpy_copy1.
Definition memmove_run := PMCP.copy_run RSEGS 0xab884 (fun fx => @memmove_disjoint fx).

End PMCPS.
