(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim RefMemcpyLib MemSplit As0StepLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0RegionPoisoned_b Ba0AsanMemset_b Ba0AsanMemcpy_b Ba0StrlenIcpt_b Ba0TlsGetAddr_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0_code_r48448_48dd8_b Ba0_code_r4dae8_4daec_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.

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
  gres; rwH; unfold at_, v_addi, v_add, v_sub, v_srli; imm_norm; unorm; rewrite ?Z.shiftr_div_pow2 by lia;
  try change (2 ^ 3)%Z with 8%Z; first [reflexivity | f_equal; lia].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma memtoshadow47_run : forall regs (M rom : word -> option byte) (ret : word) (p : Z),
  rt_layout_globs M -> in_app p ->
  getr regs 10 = Z_to_bv 64 p -> getr regs 1 = ret -> ret_ok ret ->
  exists regs',
    msteps ASEGS (mkst regs (0x5e39c : word) M rom) (mkst regs' ret M rom)
    /\ getr regs' 10 = Z_to_bv 64 (p / 8 + SB) /\ keeps_cs regs regs'.
Proof.
  intros regs M rom ret p (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8) Hp H10 H1 Hret.
  unfold in_app, LOWEND, HIGHBEG, HIGHEND in Hp. unfold SB in *.
  pose proof (Z.div_mod p 8 ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound p 8 ltac:(lia)) as Hmd.
  destruct Hp as [Hlow|Hhigh].
  - eexists. split.
    + stepn F_5df84 D_5df84.                                     (* [comment removed for export] *)
      mld F_5df88 D_5df88 (0x1374c0 : word) G1.                     (* [comment removed for export] *)
      mld F_5df8c D_5df8c (0x13fc38 : word) G2.                     (* [comment removed for export] *)
      stepn F_5df90 D_5df90.                                     (* [comment removed for export] *)
      stepn F_5df94 D_5df94.                                     (* [comment removed for export] *)
      stepn F_5df98 D_5df98.                                     (* [comment removed for export] *)
      stepn F_5df9c D_5df9c.                                     (* [comment removed for export] *)
      stepb_tk F_5dfa0 D_5dfa0 ltac:(cond).                      (* [comment removed for export] *)
      stepiv F_5dfe4 D_5dfe4 (Z_to_bv 64 (p / 8)) ltac:(wval).    (* [comment removed for export] *)
      stepiv F_5dfe8 D_5dfe8 (Z_to_bv 64 (p / 8 + 0x7fff8000)) ltac:(wval).   (* [comment removed for export] *)
      stepret F_5dfec D_5dfec ret ltac:(rwH; reflexivity).
      apply mst_refl.
    + split; [gres; reflexivity | solve_keeps_cs].
  - eexists. split.
    + stepn F_5df84 D_5df84.
      mld F_5df88 D_5df88 (0x1374c0 : word) G1.
      mld F_5df8c D_5df8c (0x13fc38 : word) G2.
      stepn F_5df90 D_5df90.
      stepn F_5df94 D_5df94.
      stepn F_5df98 D_5df98.
      stepn F_5df9c D_5df9c.
      stepb_ft F_5dfa0 D_5dfa0 ltac:(cond).                      (* [comment removed for export] *)
      stepn F_5dfa4 D_5dfa4.                                     (* [comment removed for export] *)
      mld F_5dfa8 D_5dfa8 (0x1374c8 : word) G3.                     (* [comment removed for export] *)
      stepn F_5dfac D_5dfac.                                     (* [comment removed for export] *)
      mld F_5dfb0 D_5dfb0 (0x1374d0 : word) G5.                     (* [comment removed for export] *)
      mld F_5dfb4 D_5dfb4 (0x140928 : word) G4.                     (* [comment removed for export] *)
      mld F_5dfb8 D_5dfb8 (0x140930 : word) G6.                     (* [comment removed for export] *)
      stepn F_5dfbc D_5dfbc.                                     (* [comment removed for export] *)
      stepb_tk F_5dfc0 D_5dfc0 ltac:(cond).                      (* [comment removed for export] *)
      stepn F_5dfc8 D_5dfc8.                                     (* [comment removed for export] *)
      mld F_5dfcc D_5dfcc (0x1374d8 : word) G7.                     (* [comment removed for export] *)
      mld F_5dfd0 D_5dfd0 (0x140920 : word) G8.                     (* [comment removed for export] *)
      stepn F_5dfd4 D_5dfd4.                                     (* [comment removed for export] *)
      stepn F_5dfd8 D_5dfd8.                                     (* [comment removed for export] *)
      stepb_ft F_5dfdc D_5dfdc ltac:(cond).                      (* [comment removed for export] *)
      stepb_ft F_5dfe0 D_5dfe0 ltac:(cond).                      (* [comment removed for export] *)
      stepiv F_5dfe4 D_5dfe4 (Z_to_bv 64 (p / 8)) ltac:(wval).
      stepiv F_5dfe8 D_5dfe8 (Z_to_bv 64 (p / 8 + 0x7fff8000)) ltac:(wval).
      stepret F_5dfec D_5dfec ret ltac:(rwH; reflexivity).
      apply mst_refl.
    + split; [gres; reflexivity | solve_keeps_cs].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma land_8191 : forall a, Z.land a 8191 = (a mod 8192)%Z.
Proof. intros a. change 8191%Z with (Z.ones 13). rewrite Z.land_ones by lia. reflexivity. Qed.

Section FSM1.
  Variable mem0 : word -> option byte.
  Variable rom : word -> option byte.
  Variables sp ra a0v : word.
  (* [comment removed for export] *)
  Variables s tpv md off dtv ent key tsd ctx th tb te F V verb dto blk rec : Z.
  (* [comment removed for export] *)
  Variables fs h pos ff : Z.
  Hypothesis Hs_def : bv_unsigned sp = s.
  Hypothesis Hret : ret_ok ra.
  Hypothesis Hs : (0x1000000 <= s - 208)%Z /\ (s < 2 ^ 64)%Z.          (* [comment removed for export] *)
  Hypothesis Hok : store_ok ASEGS mem0 (Z_to_bv 64 (s - 208)) 208%nat = true.
  Hypothesis Htp : (96 <= tpv < 2 ^ 64)%Z.
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
  Hypothesis HC0 : forall M', (forall x : word, (bv_unsigned x < s - 208 \/ s <= bv_unsigned x)%Z -> M' x = mem0 x) ->
    tls_cells tpv 0x1382b8 md off dtv ent key tsd ctx th tb te F V verb dto blk rec M'.
  (* [comment removed for export] *)
  Hypothesis Hfs : (0x696000 <= fs)%Z /\ (fs + 4096 + 32768 + 11 * 2 ^ 20 <= s - 208 \/ s <= fs)%Z /\ (fs + 4096 + 32768 + 11 * 2 ^ 20 < 2 ^ 47)%Z.
  Hypothesis Hh : (0 <= h < 2 ^ 62)%Z.
  Hypothesis Hpos_def : pos = (h mod 8192)%Z.
  Hypothesis Hff_def : ff = (fs + 4096 + 32768 + 2 ^ 20 + 128 * pos)%Z.
  Definition tls_r : Z := tls_res off ent.
  Hypothesis Hr : (0 <= tls_r /\ tls_r + 8 < 2 ^ 64)%Z /\ (tls_r + 8 <= s - 208 \/ s <= tls_r)%Z /\ (tls_r + 8 <= fs \/ fs + 4096 + 32768 + 11 * 2 ^ 20 <= tls_r)%Z.
  Hypothesis HRfs : rdn ASEGS mem0 (Z_to_bv 64 tls_r) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 fs)).
  Hypothesis Hng : rdn ASEGS mem0 (Z_to_bv 64 (fs + 96)) 1%nat = Some [Z_to_bv 8 0].                     (* [comment removed for export] *)
  Hypothesis Hssl : rdn ASEGS mem0 (Z_to_bv 64 (fs + 88)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 20)).   (* [comment removed for export] *)
  Hypothesis Hhint : rdn ASEGS mem0 (Z_to_bv 64 (fs + 8)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 h)). (* [comment removed for export] *)
  Hypothesis Hflag : rdn ASEGS mem0 (Z_to_bv 64 (fs + 4096 + 16384 + pos)) 1%nat = Some [Z_to_bv 8 0].      (* [comment removed for export] *)
  Hypothesis Hwfs : store_ok ASEGS mem0 (Z_to_bv 64 fs) (Z.to_nat (4096 + 32768 + 11 * 2 ^ 20)) = true.   (* [comment removed for export] *)
  Hypothesis HG : rt_layout_globs mem0.
  Hypothesis Happ : in_app ff.
  Hypothesis Hshadow_ok : store_ok ASEGS mem0 (Z_to_bv 64 (SB + ff / 8)) 16%nat = true.
  Hypothesis Hshadow_dj : (SB + ff / 8 + 16 <= s - 208 \/ s <= SB + ff / 8)%Z /\ (SB + ff / 8 + 16 <= 0x1374c0 \/ 0x140938 <= SB + ff / 8)%Z.

  #[local] Ltac hide_dj := try hide Hfs; try hide Hr; try hide Hshadow_dj.

  (* [comment removed for export] *)
  Definition F4 (rg : bvmap 5 word) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes mem0 (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ra)) (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr rg 8)))
           (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr rg 9))) (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (getr rg 18)).

  (* [comment removed for export] *)
  Definition fsm1_mem (Mj : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes Mj
      (Z_to_bv 64 (fs + 8)) (word_to_le_bytes 8 (Z_to_bv 64 (h + 1))))                 (* [comment removed for export] *)
      (Z_to_bv 64 (fs + 4096 + 16384 + pos)) [Z_to_bv 8 1])                             (* [comment removed for export] *)
      (Z_to_bv 64 (ff + 24)) (word_to_le_bytes 8 (Z_to_bv 64 s)))                      (* [comment removed for export] *)
      (Z_to_bv 64 (ff + 120)) (word_to_le_bytes 8 (Z_to_bv 64 (fs + 4096 + 16384 + pos))))   (* [comment removed for export] *)
      (Z_to_bv 64 (SB + ff / 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))                   (* [comment removed for export] *)
      (Z_to_bv 64 (SB + ff / 8 + 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)).                (* [comment removed for export] *)

  Lemma sp_s1 : sp = Z_to_bv 64 s.  Proof. rewrite <- Hs_def. symmetry. apply Z_to_bv_bv_unsigned. Qed.

(* [comment removed for export] *)
End FSM1.
End FPX_1.
