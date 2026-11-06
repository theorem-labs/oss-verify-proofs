(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac RefMemcpyLib MemSplit As0StepLib Ea0MemIsZero Ea0RegionPoisoned Ea0AsanMemset Ea0AsanMemcpy Ea0StrlenIcpt.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import
  Ea0_code_r4dae8_4daec Ea0_code_r52640_526bc Ea0_code_r66e54_66ef4 Ea0_code_r69654_69674 Ea0_code_r61f50_61f68 Ea0_code_rcd208_cd224
  Ea0_code_rcc154_cc178 Ea0_code_r76d68_770b8.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import OtfKit.
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_encoder.images.Asan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_encoder.images.Asan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_encoder.images.Asan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_encoder.images.Asan.M.loaded_segments) pc.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.

Lemma v_lw_small : forall z, (0 <= z < 2 ^ 31)%Z -> v_lw (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
intros z Hz. unfold v_lw. f_equal. rewrite u_Z2bv by lia. unfold bv_swrap, bv_wrap.
change (bv_half_modulus 32) with (2 ^ 31)%Z. change (bv_modulus 32) with (2 ^ 32)%Z. rewrite Z.mod_small; lia.
Qed.
Lemma zbv_mod : forall z, Z_to_bv 64 (z mod 2 ^ 64) = Z_to_bv 64 z.
Proof.
intros z. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64)%Z. apply Z.mod_mod. lia.
Qed.

Section FPX_1. Context {fx : PropExec.FPState}.

#[local] Ltac rwH :=
  repeat match goal with
         | H : getr ?rg ?i = _ |- context [getr ?rg ?i] => rewrite !H
         end.
#[local] Ltac unorm :=
  repeat match goal with
         | |- context [bv_unsigned (Z_to_bv 64 ?z)] =>
             lazymatch z with context [Z_to_bv 64 _] => fail | _ => rewrite (u_Z2bv z) by lia end
         end.
#[local] Ltac cond :=
  rwH; unfold at_, v_addi, v_add, c_eq, c_ltu, bv_eqb, bv_ltu; imm_norm; unorm;
  first [apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge]; lia.
#[local] Ltac wval :=
  gres; rwH; unfold at_, v_addi, v_add, v_sub, v_srli, v_slli; imm_norm; unorm; rewrite ?Z.shiftr_div_pow2, ?Z.shiftl_mul_pow2 by lia;
  try change (2 ^ 3)%Z with 8%Z; try change (2 ^ 4)%Z with 16%Z; first [reflexivity | f_equal; lia].
#[local] Ltac vlit := gres; rwH; apply bv_eq; vm_compute; reflexivity.
#[local] Ltac maddr z := match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 z) by (symmetry; wval) end.
(* [comment removed for export] *)
#[local] Ltac mldq F D z R :=
  chain_step; [reflexivity
    | eapply step_ld with (bs := word_to_le_bytes 8 (Z_to_bv 64 _)); [exact F | reflexivity | exact D | maddr z; exact R | exact (bytes_le_to_Z_8 _)]
    | step_simpl; vnorm].
#[local] Ltac mlwq F D z R :=
  chain_step; [reflexivity
    | eapply step_lw with (bs := word_to_le_bytes 4 (Z_to_bv 64 _)); [exact F | reflexivity | exact D | maddr z; exact R | apply bytes_le_to_Z_4; unorm; lia]
    | step_simpl; vnorm; rewrite v_lw_small by lia].
#[local] Ltac mlbuq F D z R :=
  chain_step; [reflexivity
    | eapply step_lbu; [exact F | reflexivity | exact D | maddr z; exact R]
    | step_simpl; vnorm].
#[local] Ltac peel :=
  rewrite rdn_wbytes_out;
    [ | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; imm_norm; unorm; lia | cbn [Z.of_nat Pos.to_nat]; imm_norm; unorm; lia
      | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; imm_norm; unorm; lia ].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma musl_tls_get_addr_run : forall regs (M rom : word -> option byte) (ret : word) (d tpv md off dtv ent : Z),
  getr regs 10 = Z_to_bv 64 d -> getr regs 4 = Z_to_bv 64 tpv -> getr regs 1 = ret -> ret_ok ret ->
  (0 <= d /\ d + 16 <= 2 ^ 64)%Z -> (8 <= tpv < 2 ^ 64)%Z -> (0 <= md < 2 ^ 16)%Z -> (0 <= off < 2 ^ 64)%Z -> (0 <= dtv /\ dtv + 8 * md + 8 <= 2 ^ 64)%Z -> (0 <= ent < 2 ^ 64)%Z ->
  rdn ASEGS M (Z_to_bv 64 d) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 md)) ->
  rdn ASEGS M (Z_to_bv 64 (d + 8)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 off)) ->
  rdn ASEGS M (Z_to_bv 64 (tpv - 8)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 dtv)) ->
  rdn ASEGS M (Z_to_bv 64 (dtv + 8 * md)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 ent)) ->
  exists regs',
    msteps ASEGS (mkst regs (0x12c46c : word) M rom) (mkst regs' ret M rom)
    /\ getr regs' 10 = Z_to_bv 64 ((ent + off) mod 2 ^ 64) /\ keeps_but [1]%bv regs regs'.
Proof.
intros regs M rom ret d tpv md off dtv ent H10 H4 H1 Hret Hd Htp Hmd Hoff Hdtv Hent R1 R2 R3 R4.
pose proof (Z.mod_pos_bound (ent + off) (2 ^ 64) ltac:(lia)) as Hm.
eexists. split.
- stepiv (ltac:(oF' 0x12c46c%Z)) (ltac:(oD' 0x12c46c%Z)) (Z_to_bv 64 tpv) ltac:(wval).
mldq (ltac:(oF' 0x12c470%Z)) (ltac:(oD' 0x12c470%Z)) d R1.
mldq (ltac:(oF' 0x12c474%Z)) (ltac:(oD' 0x12c474%Z)) (tpv - 8)%Z R3.
mldq (ltac:(oF' 0x12c478%Z)) (ltac:(oD' 0x12c478%Z)) (d + 8)%Z R2.
stepiv (ltac:(oF' 0x12c47c%Z)) (ltac:(oD' 0x12c47c%Z)) (Z_to_bv 64 (8 * md)) ltac:(wval).
stepiv (ltac:(oF' 0x12c480%Z)) (ltac:(oD' 0x12c480%Z)) (Z_to_bv 64 (dtv + 8 * md)) ltac:(wval).
mldq (ltac:(oF' 0x12c484%Z)) (ltac:(oD' 0x12c484%Z)) (dtv + 8 * md)%Z R4.
stepiv (ltac:(oF' 0x12c488%Z)) (ltac:(oD' 0x12c488%Z)) (Z_to_bv 64 ((ent + off) mod 2 ^ 64)) ltac:(gres; rwH; unfold v_add; unorm; rewrite zbv_mod; f_equal; lia).
stepret (ltac:(oF' 0x12c48c%Z)) (ltac:(oD' 0x12c48c%Z)) ret ltac:(rwH; reflexivity).
apply mst_refl.
- split; [gres; reflexivity | solve_keeps_but].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma get_current_thread_run : forall regs (M rom : word -> option byte) (ret : word) (t tpv key tsd ctx th : Z),
  getr regs 2 = Z_to_bv 64 t -> getr regs 4 = Z_to_bv 64 tpv -> getr regs 1 = ret -> ret_ok ret ->
  (0x1000000 <= t - 16)%Z -> (t < 2 ^ 64)%Z -> (96 <= tpv < 2 ^ 64)%Z -> (0 <= key < 2 ^ 28)%Z ->
  (0 <= tsd /\ tsd + 8 * key + 8 <= 2 ^ 64)%Z -> (0 < ctx /\ ctx + 160 <= 2 ^ 64)%Z -> (0 <= th < 2 ^ 64)%Z ->
  store_ok ASEGS M (Z_to_bv 64 (t - 16)) 16%nat = true ->
  (* [comment removed for export] *)
  (forall M', (forall x : word, (bv_unsigned x < t - 16 \/ t <= bv_unsigned x)%Z -> M' x = M x) ->
     rdn ASEGS M' (0x141260 : word) 1%nat = Some [Z_to_bv 8 1] /\
     rdn ASEGS M' (0x141264 : word) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 key)) /\
     rdn ASEGS M' (Z_to_bv 64 (tpv - 88)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 tsd)) /\
     rdn ASEGS M' (Z_to_bv 64 (tsd + 8 * key)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 ctx)) /\
     rdn ASEGS M' (Z_to_bv 64 (ctx + 152)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 th))) ->
  exists regs',
    msteps ASEGS (mkst regs (0x84268 : word) M rom) (mkst regs' ret (wbytes M (Z_to_bv 64 (t - 8)) (word_to_le_bytes 8 ret)) rom)
    /\ getr regs' 10 = Z_to_bv 64 th /\ getr regs' 2 = Z_to_bv 64 t /\ getr regs' 1 = ret /\ keeps_but [1; 2]%bv regs regs'.
Proof. intros regs M rom ret t tpv key tsd ctx th.
intros H2 H4 H1 Hret Ht1 Ht2 Htp Hkey Htsd Hctx Hth Hok HC.
set (M1 := wbytes M (Z_to_bv 64 (t - 8)) (word_to_le_bytes 8 ret)).
destruct (HC M1) as (C1 & C2 & C3 & C4 & C5).
{ intros x Hx. unfold M1. pose proof (u64_range x).
destruct Hx as [Hx|Hx]; [rewrite wbytes_below; [reflexivity | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia | unorm; lia]
| rewrite wbytes_above; [reflexivity | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia]]. }
assert (Hra : ret_ok (0x84274 : word)) by (unfold ret_ok; apply bv_eq; vm_compute; reflexivity).
eexists. split.
- stepiv (ltac:(oF' 0x84268%Z)) (ltac:(oD' 0x84268%Z)) (Z_to_bv 64 (t - 16)) ltac:(wval).
stepsd (ltac:(oF' 0x8426c%Z)) (ltac:(oD' 0x8426c%Z)) (Z_to_bv 64 (t - 8)) ret
ltac:(apply (store_ok_sub ASEGS M (Z_to_bv 64 (t - 16)) _ 16%nat); [unorm; cbn; lia | exact Hok | unorm; lia | unorm; cbn; lia]).
change (wbytes M (Z_to_bv 64 (t - 8)) (word_to_le_bytes 8 ret)) with M1.
stepn (ltac:(oF' 0x84270%Z)) (ltac:(oD' 0x84270%Z)).
stepn (ltac:(oF' 0x7c8e8%Z)) (ltac:(oD' 0x7c8e8%Z)).
stepn (ltac:(oF' 0x7c8ec%Z)) (ltac:(oD' 0x7c8ec%Z)).
mlbu (ltac:(oF' 0x7c8f0%Z)) (ltac:(oD' 0x7c8f0%Z)) (0x141260 : word) C1.
stepb_ft (ltac:(oF' 0x7c8f4%Z)) (ltac:(oD' 0x7c8f4%Z)) ltac:(cond).
mlw (ltac:(oF' 0x7c8f8%Z)) (ltac:(oD' 0x7c8f8%Z)) (0x141264 : word) C2.
stepn (ltac:(oF' 0x7c8fc%Z)) (ltac:(oD' 0x7c8fc%Z)).
stepiv (ltac:(oF' 0x12e0b4%Z)) (ltac:(oD' 0x12e0b4%Z)) (Z_to_bv 64 tpv) ltac:(wval).
mldq (ltac:(oF' 0x12e0b8%Z)) (ltac:(oD' 0x12e0b8%Z)) (tpv - 88)%Z C3.
stepiv (ltac:(oF' 0x12e0bc%Z)) (ltac:(oD' 0x12e0bc%Z)) (Z_to_bv 64 (key * 2 ^ 32)) ltac:(gres; rwH; rewrite v_lw_small by lia; wval).
stepiv (ltac:(oF' 0x12e0c0%Z)) (ltac:(oD' 0x12e0c0%Z)) (Z_to_bv 64 (8 * key))
ltac:(gres; rwH; unfold v_srli; imm_norm; unorm; rewrite Z.shiftr_div_pow2 by lia;
replace (key * 2 ^ 32)%Z with (8 * key * 2 ^ 29)%Z by lia; rewrite Z.div_mul by lia; reflexivity).
stepiv (ltac:(oF' 0x12e0c4%Z)) (ltac:(oD' 0x12e0c4%Z)) (Z_to_bv 64 (tsd + 8 * key)) ltac:(wval).
mldq (ltac:(oF' 0x12e0c8%Z)) (ltac:(oD' 0x12e0c8%Z)) (tsd + 8 * key)%Z C4.
stepret (ltac:(oF' 0x12e0cc%Z)) (ltac:(oD' 0x12e0cc%Z)) (0x84274 : word) ltac:(rwH; first [reflexivity | apply bv_eq; vm_compute; reflexivity]).
stepb_ft (ltac:(oF' 0x84274%Z)) (ltac:(oD' 0x84274%Z)) ltac:(cond).
mldq (ltac:(oF' 0x84278%Z)) (ltac:(oD' 0x84278%Z)) (ctx + 152)%Z C5.
stepld (ltac:(oF' 0x8427c%Z)) (ltac:(oD' 0x8427c%Z)) ret ltac:(maddr (t - 8)%Z; unfold M1; apply rdn_wbytes_hit8; unorm; lia).
stepiv (ltac:(oF' 0x84280%Z)) (ltac:(oD' 0x84280%Z)) (Z_to_bv 64 t) ltac:(wval).
stepret (ltac:(oF' 0x84284%Z)) (ltac:(oD' 0x84284%Z)) ret ltac:(rwH; reflexivity).
apply mst_refl.
- repeat split; gres; rwH; try reflexivity. solve_keeps_but.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section DTLS.
  Variable M : word -> option byte.
  Variable rom : word -> option byte.
  Variable ret : word.
  Variables t tpv d md F V verb dto blk rec : Z.
  Hypothesis Hret : ret_ok ret.
  Hypothesis Ht : (0x1000000 <= t - 144)%Z /\ (t < 2 ^ 64)%Z.
  Hypothesis Htp : (0 <= tpv < 2 ^ 64)%Z.
  Hypothesis Hd : (0 <= d /\ d + 16 <= 2 ^ 64)%Z.
  Hypothesis Hmd : (0 <= md < 255)%Z.
  Hypothesis HF : (0 <= F /\ F + 256 <= 2 ^ 64)%Z.
  Hypothesis HV : (0 <= V /\ V + 4 <= 2 ^ 64)%Z.
  Hypothesis Hverb : (0 <= verb < 3)%Z.
  Hypothesis Hdto : (0 <= dto /\ 0 <= dto + tpv /\ dto + tpv + 8 <= 2 ^ 64)%Z.
  Hypothesis Hblk : (0 < blk /\ blk + 16 * 255 <= 2 ^ 64 - 1)%Z.      (* [comment removed for export] *)
  Hypothesis Hrec : (0 < rec < 2 ^ 64)%Z.
  Hypothesis Hok : store_ok ASEGS M (Z_to_bv 64 (t - 144)) 144%nat = true.
  (* [comment removed for export] *)
  Hypothesis HC : forall M', (forall x : word, (bv_unsigned x < t - 144 \/ t <= bv_unsigned x)%Z -> M' x = M x) ->
     rdn ASEGS M' (0x1391a8 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 F)) /\
     rdn ASEGS M' (Z_to_bv 64 (F + 137)) 1%nat = Some [Z_to_bv 8 1] /\
     rdn ASEGS M' (0x139208 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 V)) /\
     rdn ASEGS M' (Z_to_bv 64 V) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 verb)) /\
     rdn ASEGS M' (0x139fc0 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 dto)) /\
     rdn ASEGS M' (Z_to_bv 64 (dto + tpv)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 blk)) /\
     rdn ASEGS M' (Z_to_bv 64 d) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 md)) /\
     rdn ASEGS M' (Z_to_bv 64 (blk + 16 * md + 8)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 rec)).

  (* [comment removed for export] *)
  Definition M13 (rg : bvmap 5 word) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes M
      (Z_to_bv 64 (t - 8)) (word_to_le_bytes 8 ret))
      (Z_to_bv 64 (t - 16)) (word_to_le_bytes 8 (getr rg 8)))
      (Z_to_bv 64 (t - 24)) (word_to_le_bytes 8 (getr rg 9)))
      (Z_to_bv 64 (t - 32)) (word_to_le_bytes 8 (getr rg 18)))
      (Z_to_bv 64 (t - 40)) (word_to_le_bytes 8 (getr rg 19)))
      (Z_to_bv 64 (t - 48)) (word_to_le_bytes 8 (getr rg 20)))
      (Z_to_bv 64 (t - 56)) (word_to_le_bytes 8 (getr rg 21)))
      (Z_to_bv 64 (t - 64)) (word_to_le_bytes 8 (getr rg 22)))
      (Z_to_bv 64 (t - 72)) (word_to_le_bytes 8 (getr rg 23)))
      (Z_to_bv 64 (t - 80)) (word_to_le_bytes 8 (getr rg 24)))
      (Z_to_bv 64 (t - 88)) (word_to_le_bytes 8 (getr rg 25)))
      (Z_to_bv 64 (t - 96)) (word_to_le_bytes 8 (getr rg 26)))
      (Z_to_bv 64 (t - 104)) (word_to_le_bytes 8 (getr rg 27)).
  Definition MD (rg : bvmap 5 word) : word -> option byte :=
    wbytes (wbytes (M13 rg)
      (Z_to_bv 64 (t - 128)) (word_to_le_bytes 8 (getr rg 12)))
      (Z_to_bv 64 (t - 120)) (word_to_le_bytes 8 (getr rg 13)).

  Lemma M13_out : forall rg (x : word), (bv_unsigned x < t - 144 \/ t <= bv_unsigned x)%Z -> M13 rg x = M x.
Proof.
intros rg x Hx. unfold M13. pose proof (u64_range x).
destruct Hx as [Hx|Hx].
- rewrite !wbytes_below; first [reflexivity | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia | unorm; lia].
- rewrite !wbytes_above; first [reflexivity | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia].
Qed.
  Lemma MD_out : forall rg (x : word), (bv_unsigned x < t - 144 \/ t <= bv_unsigned x)%Z -> MD rg x = M x.
Proof.
intros rg x Hx. unfold MD. pose proof (u64_range x). rewrite <- (M13_out rg x Hx).
destruct Hx as [Hx|Hx].
- rewrite !wbytes_below; first [reflexivity | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia | unorm; lia].
- rewrite !wbytes_above; first [reflexivity | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia].
Qed.

  #[local] Ltac sok := first [apply (store_ok_mono _ _ M); [repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl|];
                              apply (store_ok_sub ASEGS M (Z_to_bv 64 (t - 144)) _ 144%nat); [unorm; cbn; lia | exact Hok | unorm; lia | unorm; cbn; lia]].
  #[local] Ltac slot := repeat peel; apply rdn_wbytes_hit8; unorm; lia.

  Lemma dtls_fast_run : forall regs (a1v : word),
    getr regs 10 = Z_to_bv 64 d -> getr regs 11 = a1v -> getr regs 2 = Z_to_bv 64 t -> getr regs 4 = Z_to_bv 64 tpv -> getr regs 1 = ret ->
    exists regs',
      msteps ASEGS (mkst regs (0x91998 : word) M rom) (mkst regs' ret (MD regs) rom)
      /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 2 = Z_to_bv 64 t /\ getr regs' 1 = ret
      /\ keeps_but [1; 2]%bv regs regs'.
Proof. intros regs a1v.
intros H10 H11 H2 H4 H1.
destruct (HC (M13 regs) (M13_out regs)) as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8).
destruct (HC (MD regs) (MD_out regs)) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8).
unfold MD, M13 in *.
eexists. split.
- stepiv (ltac:(oF' 0x91998%Z)) (ltac:(oD' 0x91998%Z)) (Z_to_bv 64 (t - 144)) ltac:(wval).
stepsd (ltac:(oF' 0x9199c%Z)) (ltac:(oD' 0x9199c%Z)) (Z_to_bv 64 (t - 8)) ret ltac:(sok).
stepsd (ltac:(oF' 0x919a0%Z)) (ltac:(oD' 0x919a0%Z)) (Z_to_bv 64 (t - 16)) (getr regs 8) ltac:(sok).
stepsd (ltac:(oF' 0x919a4%Z)) (ltac:(oD' 0x919a4%Z)) (Z_to_bv 64 (t - 24)) (getr regs 9) ltac:(sok).
stepsd (ltac:(oF' 0x919a8%Z)) (ltac:(oD' 0x919a8%Z)) (Z_to_bv 64 (t - 32)) (getr regs 18) ltac:(sok).
stepsd (ltac:(oF' 0x919ac%Z)) (ltac:(oD' 0x919ac%Z)) (Z_to_bv 64 (t - 40)) (getr regs 19) ltac:(sok).
stepsd (ltac:(oF' 0x919b0%Z)) (ltac:(oD' 0x919b0%Z)) (Z_to_bv 64 (t - 48)) (getr regs 20) ltac:(sok).
stepsd (ltac:(oF' 0x919b4%Z)) (ltac:(oD' 0x919b4%Z)) (Z_to_bv 64 (t - 56)) (getr regs 21) ltac:(sok).
stepsd (ltac:(oF' 0x919b8%Z)) (ltac:(oD' 0x919b8%Z)) (Z_to_bv 64 (t - 64)) (getr regs 22) ltac:(sok).
stepsd (ltac:(oF' 0x919bc%Z)) (ltac:(oD' 0x919bc%Z)) (Z_to_bv 64 (t - 72)) (getr regs 23) ltac:(sok).
stepsd (ltac:(oF' 0x919c0%Z)) (ltac:(oD' 0x919c0%Z)) (Z_to_bv 64 (t - 80)) (getr regs 24) ltac:(sok).
stepsd (ltac:(oF' 0x919c4%Z)) (ltac:(oD' 0x919c4%Z)) (Z_to_bv 64 (t - 88)) (getr regs 25) ltac:(sok).
stepsd (ltac:(oF' 0x919c8%Z)) (ltac:(oD' 0x919c8%Z)) (Z_to_bv 64 (t - 96)) (getr regs 26) ltac:(sok).
stepsd (ltac:(oF' 0x919cc%Z)) (ltac:(oD' 0x919cc%Z)) (Z_to_bv 64 (t - 104)) (getr regs 27) ltac:(sok).
stepn (ltac:(oF' 0x919d0%Z)) (ltac:(oD' 0x919d0%Z)).
stepn (ltac:(oF' 0x919d4%Z)) (ltac:(oD' 0x919d4%Z)).
mld (ltac:(oF' 0x919d8%Z)) (ltac:(oD' 0x919d8%Z)) (0x1391a8 : word) C1.
mlbuq (ltac:(oF' 0x919dc%Z)) (ltac:(oD' 0x919dc%Z)) (F + 137)%Z C2.
stepb_ft (ltac:(oF' 0x919e0%Z)) (ltac:(oD' 0x919e0%Z)) ltac:(cond).
stepiv (ltac:(oF' 0x919e4%Z)) (ltac:(oD' 0x919e4%Z)) (Z_to_bv 64 d) ltac:(wval).
stepn (ltac:(oF' 0x919e8%Z)) (ltac:(oD' 0x919e8%Z)).
mld (ltac:(oF' 0x919ec%Z)) (ltac:(oD' 0x919ec%Z)) (0x139208 : word) C3.
mldq (ltac:(oF' 0x919f0%Z)) (ltac:(oD' 0x919f0%Z)) d C7.
stepn (ltac:(oF' 0x919f4%Z)) (ltac:(oD' 0x919f4%Z)).
mlwq (ltac:(oF' 0x919f8%Z)) (ltac:(oD' 0x919f8%Z)) V C4.
mld (ltac:(oF' 0x919fc%Z)) (ltac:(oD' 0x919fc%Z)) (0x139fc0 : word) C5.
stepn (ltac:(oF' 0x91a00%Z)) (ltac:(oD' 0x91a00%Z)).
stepiv (ltac:(oF' 0x91a04%Z)) (ltac:(oD' 0x91a04%Z)) (Z_to_bv 64 (dto + tpv)) ltac:(wval).
stepb_ft (ltac:(oF' 0x91a08%Z)) (ltac:(oD' 0x91a08%Z)) ltac:(cond).
mldq (ltac:(oF' 0x91a0c%Z)) (ltac:(oD' 0x91a0c%Z)) (dto + tpv)%Z C6.
stepn (ltac:(oF' 0x91a10%Z)) (ltac:(oD' 0x91a10%Z)).
stepfence (ltac:(oF' 0x91a14%Z)) (ltac:(oD' 0x91a14%Z)).
stepb_ft (ltac:(oF' 0x91a18%Z)) (ltac:(oD' 0x91a18%Z)) ltac:(cond).
stepb_tk (ltac:(oF' 0x91a1c%Z)) (ltac:(oD' 0x91a1c%Z)) ltac:(cond).
stepb_ft (ltac:(oF' 0x91aa0%Z)) (ltac:(oD' 0x91aa0%Z)) ltac:(cond).
stepsd (ltac:(oF' 0x91aa4%Z)) (ltac:(oD' 0x91aa4%Z)) (Z_to_bv 64 (t - 128)) (getr regs 12) ltac:(sok).
stepsd (ltac:(oF' 0x91aa8%Z)) (ltac:(oD' 0x91aa8%Z)) (Z_to_bv 64 (t - 120)) (getr regs 13) ltac:(sok).
stepn (ltac:(oF' 0x91aac%Z)) (ltac:(oD' 0x91aac%Z)).
stepb_tk (ltac:(oF' 0x91ab0%Z)) (ltac:(oD' 0x91ab0%Z)) ltac:(cond).
stepiv (ltac:(oF' 0x91b60%Z)) (ltac:(oD' 0x91b60%Z)) (Z_to_bv 64 blk) ltac:(wval).
stepiv (ltac:(oF' 0x91b64%Z)) (ltac:(oD' 0x91b64%Z)) (Z_to_bv 64 (16 * md)) ltac:(wval).
stepiv (ltac:(oF' 0x91b68%Z)) (ltac:(oD' 0x91b68%Z)) (Z_to_bv 64 (blk + 16 * md)) ltac:(wval).
mldq (ltac:(oF' 0x91b6c%Z)) (ltac:(oD' 0x91b6c%Z)) (blk + 16 * md + 8)%Z E8.
stepb_ft (ltac:(oF' 0x91b70%Z)) (ltac:(oD' 0x91b70%Z)) ltac:(cond).
stepn (ltac:(oF' 0x91b74%Z)) (ltac:(oD' 0x91b74%Z)).
stepld (ltac:(oF' 0x91b78%Z)) (ltac:(oD' 0x91b78%Z)) ret ltac:(maddr (t - 8)%Z; slot).
stepld (ltac:(oF' 0x91b7c%Z)) (ltac:(oD' 0x91b7c%Z)) (getr regs 8) ltac:(maddr (t - 16)%Z; slot).
stepld (ltac:(oF' 0x91b80%Z)) (ltac:(oD' 0x91b80%Z)) (getr regs 9) ltac:(maddr (t - 24)%Z; slot).
stepld (ltac:(oF' 0x91b84%Z)) (ltac:(oD' 0x91b84%Z)) (getr regs 18) ltac:(maddr (t - 32)%Z; slot).
stepld (ltac:(oF' 0x91b88%Z)) (ltac:(oD' 0x91b88%Z)) (getr regs 19) ltac:(maddr (t - 40)%Z; slot).
stepld (ltac:(oF' 0x91b8c%Z)) (ltac:(oD' 0x91b8c%Z)) (getr regs 20) ltac:(maddr (t - 48)%Z; slot).
stepld (ltac:(oF' 0x91b90%Z)) (ltac:(oD' 0x91b90%Z)) (getr regs 21) ltac:(maddr (t - 56)%Z; slot).
stepld (ltac:(oF' 0x91b94%Z)) (ltac:(oD' 0x91b94%Z)) (getr regs 22) ltac:(maddr (t - 64)%Z; slot).
stepld (ltac:(oF' 0x91b98%Z)) (ltac:(oD' 0x91b98%Z)) (getr regs 23) ltac:(maddr (t - 72)%Z; slot).
stepld (ltac:(oF' 0x91b9c%Z)) (ltac:(oD' 0x91b9c%Z)) (getr regs 24) ltac:(maddr (t - 80)%Z; slot).
stepld (ltac:(oF' 0x91ba0%Z)) (ltac:(oD' 0x91ba0%Z)) (getr regs 25) ltac:(maddr (t - 88)%Z; slot).
stepld (ltac:(oF' 0x91ba4%Z)) (ltac:(oD' 0x91ba4%Z)) (getr regs 26) ltac:(maddr (t - 96)%Z; slot).
stepld (ltac:(oF' 0x91ba8%Z)) (ltac:(oD' 0x91ba8%Z)) (getr regs 27) ltac:(maddr (t - 104)%Z; slot).
stepiv (ltac:(oF' 0x91bac%Z)) (ltac:(oD' 0x91bac%Z)) (Z_to_bv 64 t) ltac:(wval).
stepret (ltac:(oF' 0x91bb0%Z)) (ltac:(oD' 0x91bb0%Z)) ret ltac:(rwH; reflexivity).
apply mst_refl.
- split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; rwH; reflexivity|].
match goal with |- keeps_but _ _ ?rg =>
assert (KD : keeps_but [1; 2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv regs rg) by solve_keeps_but end.
intros r Hr HL.
destruct (decide (r = 8%bv)) as [->|N8]; [gres; reflexivity|]. destruct (decide (r = 9%bv)) as [->|N9]; [gres; reflexivity|].
destruct (decide (r = 18%bv)) as [->|N18]; [gres; reflexivity|]. destruct (decide (r = 19%bv)) as [->|N19]; [gres; reflexivity|].
destruct (decide (r = 20%bv)) as [->|N20]; [gres; reflexivity|]. destruct (decide (r = 21%bv)) as [->|N21]; [gres; reflexivity|].
destruct (decide (r = 22%bv)) as [->|N22]; [gres; reflexivity|]. destruct (decide (r = 23%bv)) as [->|N23]; [gres; reflexivity|].
destruct (decide (r = 24%bv)) as [->|N24]; [gres; reflexivity|]. destruct (decide (r = 25%bv)) as [->|N25]; [gres; reflexivity|].
destruct (decide (r = 26%bv)) as [->|N26]; [gres; reflexivity|]. destruct (decide (r = 27%bv)) as [->|N27]; [gres; reflexivity|].
apply KD; [exact Hr|]. cbv. cbv in HL. intuition congruence.
Qed.
End DTLS.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section ICPT.
  Variable mem0 : word -> option byte.
  Variable rom : word -> option byte.
  Variables sp ra : word.
  Variables s tpv d md off dtv ent key tsd ctx th tb te F V verb dto blk rec : Z.
  Hypothesis Hs_def : bv_unsigned sp = s.
  Hypothesis Hret : ret_ok ra.
  Hypothesis Hs : (0x1000000 <= s - 176)%Z /\ (s < 2 ^ 64)%Z.
  Hypothesis Hok : store_ok ASEGS mem0 (Z_to_bv 64 (s - 176)) 176%nat = true.
  Hypothesis Htp : (96 <= tpv < 2 ^ 64)%Z.
  Hypothesis Hd : (0 <= d /\ d + 16 <= 2 ^ 64)%Z.
  Hypothesis Hmd : (0 <= md < 255)%Z.
  Hypothesis Hoff : (0 <= off < 2 ^ 64)%Z.
  Hypothesis Hdtv : (0 <= dtv /\ dtv + 8 * md + 8 <= 2 ^ 64)%Z.
  Hypothesis Hent : (0 <= ent < 2 ^ 64)%Z.
  Hypothesis Hkey : (0 <= key < 2 ^ 28)%Z.
  Hypothesis Htsd : (0 <= tsd /\ tsd + 8 * key + 8 <= 2 ^ 64)%Z.
  Hypothesis Hctx : (0 < ctx /\ ctx + 160 <= 2 ^ 64)%Z.
  Hypothesis Hth : (0 < th /\ th + 64 <= 2 ^ 64)%Z.
  Hypothesis Htbe : (0 <= tb < 2 ^ 64)%Z /\ (0 <= te < 2 ^ 64)%Z.
  Hypothesis HF : (0 <= F /\ F + 256 <= 2 ^ 64)%Z.
  Hypothesis HV : (0 <= V /\ V + 4 <= 2 ^ 64)%Z.
  Hypothesis Hverb : (0 <= verb < 3)%Z.
  Hypothesis Hdto : (0 <= dto /\ 0 <= dto + tpv /\ dto + tpv + 8 <= 2 ^ 64)%Z.
  Hypothesis Hblk : (0 < blk /\ blk + 16 * 255 <= 2 ^ 64 - 1)%Z.
  Hypothesis Hrec : (0 < rec < 2 ^ 64)%Z.
  (* [comment removed for export] *)
  Definition tls_cells (M' : word -> option byte) : Prop :=
     rdn ASEGS M' (0x1426d8 : word) 1%nat = Some [Z_to_bv 8 1] /\                                        (* [comment removed for export] *)
     rdn ASEGS M' (0x13b0b8 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x12c46c)) /\            (* [comment removed for export] *)
     rdn ASEGS M' (Z_to_bv 64 d) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 md)) /\                  (* [comment removed for export] *)
     rdn ASEGS M' (Z_to_bv 64 (d + 8)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 off)) /\           (* [comment removed for export] *)
     rdn ASEGS M' (Z_to_bv 64 (tpv - 8)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 dtv)) /\         (* [comment removed for export] *)
     rdn ASEGS M' (Z_to_bv 64 (dtv + 8 * md)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 ent)) /\    (* [comment removed for export] *)
     rdn ASEGS M' (0x141260 : word) 1%nat = Some [Z_to_bv 8 1] /\                                        (* [comment removed for export] *)
     rdn ASEGS M' (0x141264 : word) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 key)) /\              (* [comment removed for export] *)
     rdn ASEGS M' (Z_to_bv 64 (tpv - 88)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 tsd)) /\        (* [comment removed for export] *)
     rdn ASEGS M' (Z_to_bv 64 (tsd + 8 * key)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 ctx)) /\   (* [comment removed for export] *)
     rdn ASEGS M' (Z_to_bv 64 (ctx + 152)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 th)) /\       (* [comment removed for export] *)
     rdn ASEGS M' (Z_to_bv 64 (th + 48)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 tb)) /\         (* [comment removed for export] *)
     rdn ASEGS M' (Z_to_bv 64 (th + 56)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 te)) /\         (* [comment removed for export] *)
     rdn ASEGS M' (0x1391a8 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 F)) /\                (* [comment removed for export] *)
     rdn ASEGS M' (Z_to_bv 64 (F + 137)) 1%nat = Some [Z_to_bv 8 1] /\                                  (* [comment removed for export] *)
     rdn ASEGS M' (0x139208 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 V)) /\                (* [comment removed for export] *)
     rdn ASEGS M' (Z_to_bv 64 V) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 verb)) /\
     rdn ASEGS M' (0x139fc0 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 dto)) /\              (* [comment removed for export] *)
     rdn ASEGS M' (Z_to_bv 64 (dto + tpv)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 blk)) /\
     rdn ASEGS M' (Z_to_bv 64 (blk + 16 * md + 8)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 rec)).
  Hypothesis HC0 : forall M', (forall x : word, (bv_unsigned x < s - 176 \/ s <= bv_unsigned x)%Z -> M' x = mem0 x) -> tls_cells M'.

  Definition tls_res : Z := ((ent + off) mod 2 ^ 64)%Z.

  Lemma sp_s : sp = Z_to_bv 64 s.
Proof. rewrite <- Hs_def. symmetry. apply Z_to_bv_bv_unsigned. Qed.
  #[local] Ltac oout := intros x Hx; pose proof (u64_range x);
     destruct Hx as [Hx|Hx]; [rewrite !wbytes_below; first [reflexivity | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; imm_norm; unorm; lia | unorm; lia]
                            | rewrite !wbytes_above; first [reflexivity | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; imm_norm; unorm; lia]].
  Lemma MD_grows' : forall M1 r t1 rg, mem_grows M1 (MD M1 r t1 rg).
Proof. intros. unfold MD, M13. repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. Qed.

  #[local] Ltac sok0 := first [apply (store_ok_mono _ _ mem0); [repeat (eapply mem_grows_trans; [|first [apply wbytes_grows | apply MD_grows']]); apply mem_grows_refl|];
                              apply (store_ok_sub ASEGS mem0 (Z_to_bv 64 (s - 176)) _ 176%nat); [unorm; cbn; lia | exact Hok | unorm; lia | unorm; cbn; lia]].

  Theorem tls_icpt_run : forall regs,
    getr regs 10 = Z_to_bv 64 d -> getr regs 4 = Z_to_bv 64 tpv -> getr regs 2 = sp -> getr regs 1 = ra ->
    exists regs' M',
      msteps ASEGS (mkst regs (0x6ba18 : word) mem0 rom) (mkst regs' ra M' rom)
      /\ getr regs' 10 = Z_to_bv 64 tls_res /\ getr regs' 2 = sp /\ getr regs' 1 = ra /\ keeps_cs regs regs'
      /\ (forall x : word, (bv_unsigned x < s - 176 \/ s <= bv_unsigned x)%Z -> M' x = mem0 x) /\ mem_grows mem0 M'.
Proof. intros regs.
intros H10 H4 H2 H1.
rewrite sp_s in H2.
set (M4 := wbytes (wbytes (wbytes (wbytes mem0 (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ra)) (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
(Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9))) (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (getr regs 18))).
set (M6 := wbytes (wbytes M4 (Z_to_bv 64 (s - 32 - 8)) (word_to_le_bytes 8 (0x6ba34 : word))) (Z_to_bv 64 (s - 32 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 d))).
set (M7 := wbytes M6 (Z_to_bv 64 (s - 32 - 8)) (word_to_le_bytes 8 (0x6ba54 : word))).
assert (O4 : forall x : word, (bv_unsigned x < s - 176 \/ s <= bv_unsigned x)%Z -> M4 x = mem0 x) by (unfold M4; oout).
assert (O6 : forall x : word, (bv_unsigned x < s - 176 \/ s <= bv_unsigned x)%Z -> M6 x = mem0 x).
{ intros x Hx. rewrite <- (O4 x Hx). unfold M6. revert x Hx. oout. }
assert (O7 : forall x : word, (bv_unsigned x < s - 176 \/ s <= bv_unsigned x)%Z -> M7 x = mem0 x).
{ intros x Hx. rewrite <- (O6 x Hx). unfold M7. revert x Hx. oout. }
destruct (HC0 M4 O4) as (A1 & A2 & _).
destruct (HC0 M6 O6) as (B1 & B2 & B3 & B4 & B5 & B6 & _).
assert (Hr1 : ret_ok (0x6ba34 : word)) by (unfold ret_ok; apply bv_eq; vm_compute; reflexivity).
assert (Hr2 : ret_ok (0x6ba48 : word)) by (unfold ret_ok; apply bv_eq; vm_compute; reflexivity).
assert (Hr3 : ret_ok (0x6ba54 : word)) by (unfold ret_ok; apply bv_eq; vm_compute; reflexivity).
assert (Hr4 : ret_ok (0x6ba78 : word)) by (unfold ret_ok; apply bv_eq; vm_compute; reflexivity).
assert (S1 : exists r1, msteps ASEGS (mkst regs (0x6ba18 : word) mem0 rom) (mkst r1 (0x81a68 : word) M4 rom)
/\ (getr r1 8 = Z_to_bv 64 d /\ getr r1 4 = Z_to_bv 64 tpv /\ getr r1 2 = Z_to_bv 64 (s - 32) /\ getr r1 1 = (0x6ba34 : word)
/\ keeps_but [1; 2; 8; 9; 18]%bv regs r1)).
{ unfold M4. eexists. split.
- stepiv (ltac:(oF' 0x6ba18%Z)) (ltac:(oD' 0x6ba18%Z)) (Z_to_bv 64 (s - 32)) ltac:(wval).
stepsd (ltac:(oF' 0x6ba1c%Z)) (ltac:(oD' 0x6ba1c%Z)) (Z_to_bv 64 (s - 8)) ra ltac:(sok0).
stepsd (ltac:(oF' 0x6ba20%Z)) (ltac:(oD' 0x6ba20%Z)) (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok0).
stepsd (ltac:(oF' 0x6ba24%Z)) (ltac:(oD' 0x6ba24%Z)) (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok0).
stepsd (ltac:(oF' 0x6ba28%Z)) (ltac:(oD' 0x6ba28%Z)) (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok0).
stepiv (ltac:(oF' 0x6ba2c%Z)) (ltac:(oD' 0x6ba2c%Z)) (Z_to_bv 64 d) ltac:(wval).
stepn (ltac:(oF' 0x6ba30%Z)) (ltac:(oD' 0x6ba30%Z)).
apply mst_refl.
- repeat split; gres; rwH; try reflexivity; try (apply bv_eq; vm_compute; reflexivity). solve_keeps_but. }
destruct S1 as (r1 & RUN1 & Q8 & Q4 & Q2 & Q1 & K1).
destruct (tryinit_fast_run r1 M4 rom (0x6ba34 : word) (s - 32) Q2 Q1 Hr1 ltac:(lia) ltac:(lia)
ltac:(unfold M4; replace (s - 32 - 16)%Z with (s - 48)%Z by lia; sok0) A1) as (r2 & RUN2 & U10 & U2 & U8 & U1 & K2).
rewrite Q8 in RUN2. change (wbytes (wbytes M4 (Z_to_bv 64 (s - 32 - 8)) (word_to_le_bytes 8 (0x6ba34 : word))) (Z_to_bv 64 (s - 32 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 d))) with M6 in RUN2.
rewrite Q8 in U8.
assert (U4 : getr r2 4 = Z_to_bv 64 tpv) by (rewrite (K2 4%bv) by (first [cbv; tauto | cbv; intuition discriminate]); exact Q4).
assert (S3 : exists r3, msteps ASEGS (mkst r2 (0x6ba34 : word) M6 rom) (mkst r3 (0x12c46c : word) M6 rom)
/\ (getr r3 10 = Z_to_bv 64 d /\ getr r3 4 = Z_to_bv 64 tpv /\ getr r3 18 = Z_to_bv 64 1 /\ getr r3 8 = Z_to_bv 64 d
/\ getr r3 2 = Z_to_bv 64 (s - 32) /\ getr r3 1 = (0x6ba48 : word) /\ keeps_but [1; 2; 8; 9; 18]%bv r2 r3)).
{ eexists. split.
- stepn (ltac:(oF' 0x6ba34%Z)) (ltac:(oD' 0x6ba34%Z)).
mld (ltac:(oF' 0x6ba38%Z)) (ltac:(oD' 0x6ba38%Z)) (0x13b0b8 : word) B2.
stepiv (ltac:(oF' 0x6ba3c%Z)) (ltac:(oD' 0x6ba3c%Z)) (Z_to_bv 64 1) ltac:(wval).
stepiv (ltac:(oF' 0x6ba40%Z)) (ltac:(oD' 0x6ba40%Z)) (Z_to_bv 64 d) ltac:(wval).
stepjr (ltac:(oF' 0x6ba44%Z)) (ltac:(oD' 0x6ba44%Z)) (Z_to_bv 64 0x12c46c) ltac:(gres; reflexivity).
vnorm. apply mst_refl.
- repeat split; gres; rwH; try reflexivity; try (apply bv_eq; vm_compute; reflexivity). solve_keeps_but. }
destruct S3 as (r3 & RUN3 & V10 & V4 & V18 & V8 & V2 & V1 & K3).
destruct (musl_tls_get_addr_run r3 M6 rom (0x6ba48 : word) d tpv md off dtv ent V10 V4 V1 Hr2 Hd ltac:(lia) ltac:(lia) Hoff Hdtv Hent B3 B4 B5 B6)
as (r4 & RUN4 & W10 & K4).
assert (W18 : getr r4 18 = Z_to_bv 64 1) by (rewrite (K4 18%bv) by (first [cbv; tauto | cbv; intuition discriminate]); exact V18).
assert (W8 : getr r4 8 = Z_to_bv 64 d) by (rewrite (K4 8%bv) by (first [cbv; tauto | cbv; intuition discriminate]); exact V8).
assert (W2 : getr r4 2 = Z_to_bv 64 (s - 32)) by (rewrite (K4 2%bv) by (first [cbv; tauto | cbv; intuition discriminate]); exact V2).
assert (W4 : getr r4 4 = Z_to_bv 64 tpv) by (rewrite (K4 4%bv) by (first [cbv; tauto | cbv; intuition discriminate]); exact V4).
pose proof (Z.mod_pos_bound (ent + off) (2 ^ 64) ltac:(lia)) as Hres.
unfold tls_res. remember ((ent + off) mod 2 ^ 64)%Z as tres eqn:Htres.
assert (S5 : exists r5, msteps ASEGS (mkst r4 (0x6ba48 : word) M6 rom) (mkst r5 (0x84268 : word) M6 rom)
/\ (getr r5 9 = Z_to_bv 64 tres /\ getr r5 4 = Z_to_bv 64 tpv /\ getr r5 8 = Z_to_bv 64 d
/\ getr r5 2 = Z_to_bv 64 (s - 32) /\ getr r5 1 = (0x6ba54 : word) /\ keeps_but [1; 2; 8; 9; 18]%bv r4 r5)).
{ eexists. split.
- stepiv (ltac:(oF' 0x6ba48%Z)) (ltac:(oD' 0x6ba48%Z)) (Z_to_bv 64 tres) ltac:(wval).
stepb_ft (ltac:(oF' 0x6ba4c%Z)) (ltac:(oD' 0x6ba4c%Z)) ltac:(cond).
stepn (ltac:(oF' 0x6ba50%Z)) (ltac:(oD' 0x6ba50%Z)).
apply mst_refl.
- repeat split; gres; rwH; try reflexivity; try (apply bv_eq; vm_compute; reflexivity). solve_keeps_but. }
destruct S5 as (r5 & RUN5 & X9 & X4 & X8 & X2 & X1 & K5).
destruct (get_current_thread_run r5 M6 rom (0x6ba54 : word) (s - 32) tpv key tsd ctx th X2 X4 X1 Hr3 ltac:(lia) ltac:(lia) Htp Hkey Htsd Hctx ltac:(lia)
ltac:(unfold M6, M4; replace (s - 32 - 16)%Z with (s - 48)%Z by lia; sok0)) as (r6 & RUN6 & Y10 & Y2 & Y1 & K6).
{ intros M' HM'. assert (O' : forall x : word, (bv_unsigned x < s - 176 \/ s <= bv_unsigned x)%Z -> M' x = mem0 x).
{ intros x Hx. rewrite (HM' x) by lia. apply O6. exact Hx. }
destruct (HC0 M' O') as (_ & _ & _ & _ & _ & _ & C7 & C8 & C9 & C10 & C11 & _). repeat split; assumption. }
change (wbytes M6 (Z_to_bv 64 (s - 32 - 8)) (word_to_le_bytes 8 (0x6ba54 : word))) with M7 in RUN6.
assert (Y9 : getr r6 9 = Z_to_bv 64 tres) by (rewrite (K6 9%bv) by (first [cbv; tauto | cbv; intuition discriminate]); exact X9).
assert (Y8 : getr r6 8 = Z_to_bv 64 d) by (rewrite (K6 8%bv) by (first [cbv; tauto | cbv; intuition discriminate]); exact X8).
assert (Y4 : getr r6 4 = Z_to_bv 64 tpv) by (rewrite (K6 4%bv) by (first [cbv; tauto | cbv; intuition discriminate]); exact X4).
destruct (HC0 M7 O7) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & D12 & D13 & _).
assert (S7 : exists r7, msteps ASEGS (mkst r6 (0x6ba54 : word) M7 rom) (mkst r7 (0x91998 : word) M7 rom)
/\ (getr r7 10 = Z_to_bv 64 d /\ getr r7 11 = Z_to_bv 64 tres /\ getr r7 2 = Z_to_bv 64 (s - 32) /\ getr r7 4 = Z_to_bv 64 tpv
/\ getr r7 1 = (0x6ba78 : word) /\ getr r7 9 = Z_to_bv 64 tres /\ keeps_but [1; 2; 8; 9; 18]%bv r6 r7)).
{ eexists. split.
- stepb_ft (ltac:(oF' 0x6ba54%Z)) (ltac:(oD' 0x6ba54%Z)) ltac:(cond).
mldq (ltac:(oF' 0x6ba58%Z)) (ltac:(oD' 0x6ba58%Z)) (th + 48)%Z D12.
mldq (ltac:(oF' 0x6ba5c%Z)) (ltac:(oD' 0x6ba5c%Z)) (th + 56)%Z D13.
stepn (ltac:(oF' 0x6ba60%Z)) (ltac:(oD' 0x6ba60%Z)).
stepiv (ltac:(oF' 0x6ba6c%Z)) (ltac:(oD' 0x6ba6c%Z)) (Z_to_bv 64 d) ltac:(wval).
stepiv (ltac:(oF' 0x6ba70%Z)) (ltac:(oD' 0x6ba70%Z)) (Z_to_bv 64 tres) ltac:(wval).
stepn (ltac:(oF' 0x6ba74%Z)) (ltac:(oD' 0x6ba74%Z)).
apply mst_refl.
- repeat split; gres; rwH; try reflexivity; try (apply bv_eq; vm_compute; reflexivity). solve_keeps_but. }
destruct S7 as (r7 & RUN7 & Z10 & Z11 & Z2 & Z4 & Z1 & Z9 & K7).
destruct (dtls_fast_run M7 rom (0x6ba78 : word) (s - 32) tpv d md F V verb dto blk rec Hr4 ltac:(lia) ltac:(lia) Hd Hmd HF HV Hverb Hdto Hblk Hrec
ltac:(unfold M7, M6, M4; replace (s - 32 - 144)%Z with (s - 176)%Z by lia; sok0)
ltac:(intros M' HM'; assert (O' : forall x : word, (bv_unsigned x < s - 176 \/ s <= bv_unsigned x)%Z -> M' x = mem0 x)
by (intros x Hx; rewrite (HM' x) by lia; apply O7; exact Hx);
destruct (HC0 M' O') as (_ & _ & E3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & E14 & E15 & E16 & E17 & E18 & E19 & E20);
repeat split; assumption)
r7 (Z_to_bv 64 tres) Z10 Z11 Z2 Z4 Z1) as (r8 & RUN8 & T10 & T2 & T1 & K8).
set (M8 := MD M7 (0x6ba78 : word) (s - 32) r7) in RUN8.
assert (O8 : forall x : word, (bv_unsigned x < s - 176 \/ s <= bv_unsigned x)%Z -> M8 x = mem0 x).
{ intros x Hx. unfold M8. rewrite MD_out by lia. apply O7. exact Hx. }
assert (T9 : getr r8 9 = Z_to_bv 64 tres) by (rewrite (K8 9%bv) by (first [cbv; tauto | cbv; intuition discriminate]); exact Z9).
assert (SL : forall k v, (k = 8 /\ v = ra \/ k = 16 /\ v = getr regs 8 \/ k = 24 /\ v = getr regs 9 \/ k = 32 /\ v = getr regs 18)%Z ->
rdn ASEGS M8 (Z_to_bv 64 (s - k)) 8%nat = Some (word_to_le_bytes 8 v)).
{ intros k v Hk.
assert (Hk' : (8 <= k <= 32)%Z) by lia.
rewrite (rdn_ext ASEGS 8 M8 M4); [| unorm; cbn; lia |].
- unfold M4. destruct Hk as [[-> ->]|[[-> ->]|[[-> ->]|[-> ->]]]]; repeat peel; apply rdn_wbytes_hit8; unorm; lia.
- intros x Hx. rewrite u_Z2bv in Hx by lia. cbn [Z.of_nat Pos.to_nat] in Hx. unfold M8. rewrite MD_out by lia.
unfold M7, M6. pose proof (u64_range x).
rewrite !wbytes_above; first [reflexivity | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; imm_norm; unorm; lia]. }
#[local] Ltac slv := first [left; split; reflexivity | right; left; split; reflexivity | right; right; left; split; reflexivity | right; right; right; split; reflexivity].
eexists. exists M8. split.
- eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3|].
eapply msteps_trans; [exact RUN4|]. eapply msteps_trans; [exact RUN5|]. eapply msteps_trans; [exact RUN6|].
eapply msteps_trans; [exact RUN7|]. eapply msteps_trans; [exact RUN8|].
stepiv (ltac:(oF' 0x6ba78%Z)) (ltac:(oD' 0x6ba78%Z)) (Z_to_bv 64 tres) ltac:(wval).
stepld (ltac:(oF' 0x6ba7c%Z)) (ltac:(oD' 0x6ba7c%Z)) ra ltac:(maddr (s - 8)%Z; apply SL; slv).
stepld (ltac:(oF' 0x6ba80%Z)) (ltac:(oD' 0x6ba80%Z)) (getr regs 8) ltac:(maddr (s - 16)%Z; apply SL; slv).
stepld (ltac:(oF' 0x6ba84%Z)) (ltac:(oD' 0x6ba84%Z)) (getr regs 9) ltac:(maddr (s - 24)%Z; apply SL; slv).
stepld (ltac:(oF' 0x6ba88%Z)) (ltac:(oD' 0x6ba88%Z)) (getr regs 18) ltac:(maddr (s - 32)%Z; apply SL; slv).
stepiv (ltac:(oF' 0x6ba8c%Z)) (ltac:(oD' 0x6ba8c%Z)) (Z_to_bv 64 s) ltac:(wval).
stepret (ltac:(oF' 0x6ba90%Z)) (ltac:(oD' 0x6ba90%Z)) ra ltac:(rwH; reflexivity).
apply mst_refl.
- split; [gres; reflexivity|]. split; [gres; symmetry; apply sp_s|]. split; [gres; reflexivity|].
split.
+ assert (KB : keeps_but [1; 2; 8; 9; 18]%bv regs r8).
{ eapply keeps_but_trans; [exact K1|]. eapply keeps_but_trans; [intros r Hr HL; apply K2; [exact Hr | cbv in HL |- *; intuition]|].
eapply keeps_but_trans; [exact K3|]. eapply keeps_but_trans; [intros r Hr HL; apply K4; [exact Hr | cbv in HL |- *; intuition]|].
eapply keeps_but_trans; [exact K5|]. eapply keeps_but_trans; [intros r Hr HL; apply K6; [exact Hr | cbv in HL |- *; intuition]|].
eapply keeps_but_trans; [exact K7|]. intros r Hr HL; apply K8; [exact Hr | cbv in HL |- *; intuition]. }
intros r Hr. destruct (decide (r = 1%bv)) as [->|N1]; [gres; rewrite H1; reflexivity|].
destruct (decide (r = 2%bv)) as [->|N2]; [gres; rewrite H2; reflexivity|].
destruct (decide (r = 8%bv)) as [->|N8]; [gres; reflexivity|]. destruct (decide (r = 9%bv)) as [->|N9]; [gres; reflexivity|].
destruct (decide (r = 18%bv)) as [->|N18]; [gres; reflexivity|].
repeat (rewrite getr_other; [| intros ->; first [congruence | cbv in Hr; intuition discriminate]]).
apply KB; [exact Hr|]. cbv. intuition congruence.
+ split; [exact O8|]. unfold M8. eapply mem_grows_trans; [|apply MD_grows'].
unfold M7, M6, M4. repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl.
Qed.

  (* [comment removed for export] *)
  Corollary wrap_tls_get_addr_run : forall regs,
    getr regs 10 = Z_to_bv 64 d -> getr regs 4 = Z_to_bv 64 tpv -> getr regs 2 = sp -> getr regs 1 = ra ->
    exists regs' M',
      msteps ASEGS (mkst regs (0x63d74 : word) mem0 rom) (mkst regs' ra M' rom)
      /\ getr regs' 10 = Z_to_bv 64 tls_res /\ getr regs' 2 = sp /\ getr regs' 1 = ra /\ keeps_cs regs regs'
      /\ (forall x : word, (bv_unsigned x < s - 176 \/ s <= bv_unsigned x)%Z -> M' x = mem0 x) /\ mem_grows mem0 M'.
Proof.
intros regs H10 H4 H2 H1.
destruct (tls_icpt_run regs H10 H4 H2 H1) as (r' & M' & RUN & REST).
exists r', M'. split; [|exact REST].
eapply msteps_trans; [|exact RUN].
stepn (ltac:(oF' 0x63d74%Z)) (ltac:(oD' 0x63d74%Z)).
apply mst_refl.
Qed.
End ICPT.
End FPX_1.
