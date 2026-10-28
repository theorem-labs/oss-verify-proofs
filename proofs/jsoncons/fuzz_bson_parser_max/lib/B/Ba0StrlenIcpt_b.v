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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac RefMemcpyLib MemSplit As0StepLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0MemIsZero_b Ba0RegionPoisoned_b Ba0AsanMemset_b Ba0AsanMemcpy_b Ba0Readers_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.muslA Require Import Ba0Memchr_b Ba0SegStrlen_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0_code_r4da8c_4da94_b Ba0_code_r4db30_4ddc4_b Ba0_code_r66e54_66ef4_b.
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
#[local] Ltac xval := gres; rwH; unfold v_xori; imm_norm; unorm; rewrite lxor_ones64 by lia; first [reflexivity | f_equal; lia].
#[local] Ltac vlit := gres; rwH; apply bv_eq; vm_compute; reflexivity.
#[local] Ltac peel0 :=
  rewrite rdn_wbytes_out;
    [ | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; imm_norm; unorm; lia | cbn [Z.of_nat Pos.to_nat]; imm_norm; unorm; lia
      | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; imm_norm; unorm; lia ].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma tryinit_fast_run : forall regs (M rom : word -> option byte) (ret : word) (t : Z),
  getr regs 2 = Z_to_bv 64 t -> getr regs 1 = ret -> ret_ok ret ->
  (0x1000000 <= t - 16)%Z -> (t < 2 ^ 64)%Z ->
  store_ok ASEGS M (Z_to_bv 64 (t - 16)) 16%nat = true ->
  rdn ASEGS M (0x140918 : word) 1%nat = Some [Z_to_bv 8 1] ->
  exists regs',
    msteps ASEGS (mkst regs (0x810e4 : word) M rom)
                 (mkst regs' ret (wbytes (wbytes M (Z_to_bv 64 (t - 8)) (word_to_le_bytes 8 ret)) (Z_to_bv 64 (t - 16)) (word_to_le_bytes 8 (getr regs 8))) rom)
    /\ getr regs' 10 = Z_to_bv 64 1 /\ getr regs' 2 = Z_to_bv 64 t /\ getr regs' 8 = getr regs 8 /\ getr regs' 1 = ret
    /\ keeps_but [1; 2; 8]%bv regs regs'.
Proof.
  intros regs M rom ret t H2 H1 Hret Ht1 Ht2 Hok HI.
  assert (HI' : rdn ASEGS (wbytes (wbytes M (Z_to_bv 64 (t - 8)) (word_to_le_bytes 8 ret)) (Z_to_bv 64 (t - 16)) (word_to_le_bytes 8 (getr regs 8)))
                  (0x140918 : word) 1%nat = Some [Z_to_bv 8 1]).
  { peel0. peel0. exact HI. }
  eexists. split.
  - stepiv F_80ccc D_80ccc (Z_to_bv 64 (t - 16)) ltac:(wval).                                          (* [comment removed for export] *)
    stepsd F_80cd0 D_80cd0 (Z_to_bv 64 (t - 8)) ret
      ltac:(apply (store_ok_sub ASEGS M (Z_to_bv 64 (t - 16)) _ 16%nat); [unorm; cbn; lia | exact Hok | unorm; lia | unorm; cbn; lia]).   (* [comment removed for export] *)
    stepsd F_80cd4 D_80cd4 (Z_to_bv 64 (t - 16)) (getr regs 8)
      ltac:(apply (store_ok_mono _ _ M); [apply wbytes_grows|];
            apply (store_ok_sub ASEGS M (Z_to_bv 64 (t - 16)) _ 16%nat); [unorm; cbn; lia | exact Hok | unorm; lia | unorm; cbn; lia]).  (* [comment removed for export] *)
    stepn F_80cd8 D_80cd8.                                                                              (* [comment removed for export] *)
    stepn F_80cdc D_80cdc.                                                                              (* [comment removed for export] *)
    mlb F_80ce0 D_80ce0 (0x140918 : word) HI'.                                                           (* [comment removed for export] *)
    stepn F_80ce4 D_80ce4.                                                                              (* [comment removed for export] *)
    stepfence F_80ce8 D_80ce8.                                                                          (* [comment removed for export] *)
    stepb_ft F_80cec D_80cec ltac:(cond).                                                               (* [comment removed for export] *)
    stepld F_80cf0 D_80cf0 ret ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (t - 8)) by (symmetry; wval) end;
                                     peel0; apply rdn_wbytes_hit8; unorm; lia).                          (* [comment removed for export] *)
    stepld F_80cf4 D_80cf4 (getr regs 8) ltac:(match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 (t - 16)) by (symmetry; wval) end;
                                              apply rdn_wbytes_hit8; unorm; lia).                        (* [comment removed for export] *)
    stepiv F_80cf8 D_80cf8 (Z_to_bv 64 t) ltac:(wval).                                                 (* [comment removed for export] *)
    stepret F_80cfc D_80cfc ret ltac:(rwH; reflexivity).
    apply mst_refl.
  - repeat split; gres; rwH; try reflexivity. solve_keeps_but.
Qed.

(* [comment removed for export] *)
Definition sl_icpt_globs (M : word -> option byte) : Prop :=
  rdn ASEGS M (0x140918 : word) 1%nat = Some [Z_to_bv 8 1] /\                                   (* [comment removed for export] *)
  rdn ASEGS M (0x1392d8 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x12a1e8)) /\       (* [comment removed for export] *)
  rdn ASEGS M (0x1374b0 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x1d1768)) /\      (* [comment removed for export] *)
  rdn ASEGS M (0x1d1863 : word) 1%nat = Some [Z_to_bv 8 1].                                      (* [comment removed for export] *)

#[local] Definition RIPL : list reg := [1; 2; 8; 9; 18; 19; 20; 21; 22]%bv.      (* [comment removed for export] *)

Section ASL.
  Variable mem0 : word -> option byte.
  Variable rom : word -> option byte.
  Variables sp ra : word.
  Variables p K n s : Z.                           (* [comment removed for export] *)
  Variable buf : list byte.                        (* [comment removed for export] *)
  Variables kS fS lS faS laS : Z.                  (* [comment removed for export] *)
  Hypothesis Hs_def : bv_unsigned sp = s.
  Hypothesis Hn_def : n = (K + 1)%Z.
  Hypothesis HfS_def : fS = (SB + p / 8)%Z.           Hypothesis HlS_def : lS = (SB + (p + n - 1) / 8)%Z.
  Hypothesis HfaS_def : faS = (fS - fS mod 8)%Z.       Hypothesis HlaS_def : laS = (lS - lS mod 8)%Z.
  Hypothesis HK : (0 <= K)%Z /\ (K + 1 <= 2 ^ 40)%Z.
  Hypothesis HappS : in_app8 p n.
  Hypothesis Hs : (0x1000000 <= s - 2216)%Z /\ (s < 2 ^ 64)%Z.       (* [comment removed for export] *)
  Hypothesis HshS : (lS + 8 <= s - 2216)%Z.
  Hypothesis HSL : slenH mem0 (Z_to_bv 64 p) buf K.
  Hypothesis HdjS : (p + Z.of_nat (length buf) <= s - 2216 \/ s <= p)%Z.   (* [comment removed for export] *)
  Hypothesis Hok : store_ok ASEGS mem0 (Z_to_bv 64 (s - 2216)) 2216%nat = true.
  Hypothesis Hret : ret_ok ra.
  Hypothesis HG : rt_layout_globs mem0.
  Hypothesis HI : sl_icpt_globs mem0.
  Hypothesis HZS : (0 < n)%Z -> forall x : word, (fS <= bv_unsigned x < lS)%Z -> mem0 x = Some (Z_to_bv 8 0).
  Hypothesis HLS : (0 < n)%Z -> mem0 (Z_to_bv 64 lS) = Some (Z_to_bv 8 kS).
  Hypothesis HkS : kS = 0%Z \/ ((p + n - 1) mod 8 < kS <= 7)%Z.
  Hypothesis HWS : (0 < n <= 64)%Z -> exists w0 w1, rdn ASEGS mem0 (Z_to_bv 64 faS) 8%nat = Some w0 /\ rdn ASEGS mem0 (Z_to_bv 64 laS) 8%nat = Some w1.

  #[local] Ltac post := repeat split; gres; rwH; try reflexivity; try (f_equal; lia); try solve_keeps_but.
  #[local] Ltac hide_dj := try hide HdjS; try hide HkS; try hide HappS.

  Lemma Hn : (0 <= n <= 2 ^ 40)%Z.  Proof. hide_dj. lia. Qed.
  Lemma sp_s : sp = Z_to_bv 64 s.  Proof. hide_dj. rewrite <- Hs_def. symmetry. apply Z_to_bv_bv_unsigned. Qed.
  Lemma pS_facts : (0 <= p)%Z /\ (p + n + 8 <= HIGHEND)%Z /\ (0 <= p / 8 <= HIGHEND)%Z /\ (0 < n -> p / 8 <= (p + n - 1) / 8 <= HIGHEND)%Z.
  Proof.
    hide_dj.
    unhide HappS.
    unfold in_app8, LOWEND, HIGHBEG, HIGHEND in *. destruct HappS as [[H1 H2]|[H1 H2]];
    (repeat split; [lia | lia | apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia | intros; apply Z.div_le_mono; lia | intros; apply Z.div_le_upper_bound; lia]).
  Qed.
  Lemma pD_facts : (0 <= p)%Z /\ (p + n + 8 <= HIGHEND)%Z /\ (0 <= p / 8 <= HIGHEND)%Z /\ (0 < n -> p / 8 <= (p + n - 1) / 8 <= HIGHEND)%Z.
  Proof. hide_dj. exact pS_facts. Qed.
  Lemma flS_facts : (0 < n)%Z -> (SB <= fS <= lS)%Z /\ (lS + 8 <= s - 2216)%Z /\ (fS - 7 <= faS <= fS)%Z /\ (lS - 7 <= laS <= lS)%Z.
  Proof.
    hide_dj.
    intros Hn0. pose proof pS_facts as (Pp & Ppn & Pp8 & Pq). specialize (Pq Hn0). unfold SB, HIGHEND in *.
    pose proof (Z.mod_pos_bound fS 8 ltac:(lia)). pose proof (Z.mod_pos_bound lS 8 ltac:(lia)). repeat split; lia.
  Qed.

  (* [comment removed for export] *)
  Definition out_agree (M : word -> option byte) : Prop :=
    forall x : word, (bv_unsigned x < s - 2216 \/ s <= bv_unsigned x)%Z -> M x = mem0 x.
  Lemma out_agree_refl : out_agree mem0.  Proof. hide_dj. intros x _. reflexivity. Qed.
  Lemma out_agree_w : forall M k v, out_agree M -> (8 <= k <= 2216)%Z -> out_agree (wbytes M (Z_to_bv 64 (s - k)) (word_to_le_bytes 8 v)).
  Proof.
    hide_dj.
    intros M k v HF Hk x Hx. pose proof (u64_range x).
    destruct Hx as [Hx|Hx].
    - rewrite wbytes_below; [apply HF; lia | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia | unorm; lia].
    - rewrite wbytes_above; [apply HF; lia | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia].
  Qed.
  Lemma out_agree_rdn : forall M (a : word) k, out_agree M -> (bv_unsigned a + Z.of_nat k <= s - 2216)%Z ->
    rdn ASEGS M a k = rdn ASEGS mem0 a k.
  Proof. hide_dj. intros M a k HF Ha. apply rdn_ext; [lia|]. intros x Hx. apply HF. lia. Qed.
  Lemma out_agree_globs : forall M, out_agree M -> rt_layout_globs M /\ sl_icpt_globs M.
  Proof.
    hide_dj.
    intros M HF. destruct HG as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8). destruct HI as (I1 & I2 & I3 & I4).
    unfold rt_layout_globs, sl_icpt_globs. rewrite !(out_agree_rdn M) by (first [exact HF | cbn [Z.of_nat Pos.to_nat]; imm_norm; lia]).
    repeat split; assumption.
  Qed.
  Lemma out_agree_store_ok : forall M k (j : nat), mem_grows mem0 M -> (Z.of_nat j <= k <= 2216)%Z ->
    store_ok ASEGS M (Z_to_bv 64 (s - k)) j = true.
  Proof.
    hide_dj.
    intros M k j HGr Hk. apply (store_ok_mono _ _ mem0 M _ HGr).
    apply (store_ok_sub ASEGS mem0 (Z_to_bv 64 (s - 2216)) _ 2216%nat); [unorm; cbn [Z.of_nat Pos.to_nat]; lia | exact Hok | unorm; lia | unorm; cbn [Z.of_nat Pos.to_nat]; lia].
  Qed.
  (* [comment removed for export] *)
  Lemma out_agree_slenH : forall M, out_agree M -> slenH M (Z_to_bv 64 p) buf K.
  Proof.
    hide_dj.
    intros M HF. pose proof pS_facts as (Pp & Ppn & _). unhide HdjS. unfold HIGHEND in *.
    destruct HSL as [Hbuf Hwin Hnw HK0 Hz Hnz Hro]. rewrite u_Z2bv in Hnw by lia.
    constructor; try assumption.
    - rewrite (rdn_ext ASEGS (length buf) M mem0); [exact Hbuf | unorm; lia|].
      intros x Hx. rewrite u_Z2bv in Hx by lia. apply HF. lia.
    - unorm. lia.
    - intros i Hi. rewrite HF by (unorm; lia). apply Hro. exact Hi.
  Qed.

  #[local] Ltac grows := first [apply mem_grows_refl | eapply mem_grows_trans; [ | apply wbytes_grows ]; grows].
  #[local] Ltac fsok := apply out_agree_store_ok; [grows | cbn [Z.of_nat Pos.to_nat]; lia].
  #[local] Ltac oagree := repeat (apply out_agree_w; [|lia]); apply out_agree_refl.

  (* [comment removed for export] *)
  Definition M9 (rg : bvmap 5 word) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem0
      (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ra))
      (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr rg 8)))
      (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr rg 9)))
      (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (getr rg 18)))
      (Z_to_bv 64 (s - 40)) (word_to_le_bytes 8 (getr rg 19)))
      (Z_to_bv 64 (s - 48)) (word_to_le_bytes 8 (getr rg 20)))
      (Z_to_bv 64 (s - 56)) (word_to_le_bytes 8 (getr rg 21)))
      (Z_to_bv 64 (s - 64)) (word_to_le_bytes 8 (getr rg 22)).
  Definition M11 (rg : bvmap 5 word) : word -> option byte :=
    wbytes (wbytes (M9 rg) (Z_to_bv 64 (s - 2152)) (word_to_le_bytes 8 (0x6348c : word))) (Z_to_bv 64 (s - 2160)) (word_to_le_bytes 8 (Z_to_bv 64 s)).
  Lemma M9_out_agree : forall rg, out_agree (M9 rg).  Proof. hide_dj. intros rg. unfold M9. oagree. Qed.
  Lemma M9_grows : forall rg, mem_grows mem0 (M9 rg).  Proof. hide_dj. intros rg. unfold M9. grows. Qed.
  Lemma M11_out_agree : forall rg, out_agree (M11 rg).  Proof. hide_dj. intros rg. unfold M11, M9. oagree. Qed.
  Lemma M11_grows : forall rg, mem_grows mem0 (M11 rg).  Proof. hide_dj. intros rg. unfold M11, M9. grows. Qed.

  Definition slots_ok (regs0 : bvmap 5 word) (M : word -> option byte) : Prop :=
    rdn ASEGS M (Z_to_bv 64 (s - 8)) 8%nat = Some (word_to_le_bytes 8 ra) /\
    rdn ASEGS M (Z_to_bv 64 (s - 16)) 8%nat = Some (word_to_le_bytes 8 (getr regs0 8)) /\
    rdn ASEGS M (Z_to_bv 64 (s - 24)) 8%nat = Some (word_to_le_bytes 8 (getr regs0 9)) /\
    rdn ASEGS M (Z_to_bv 64 (s - 32)) 8%nat = Some (word_to_le_bytes 8 (getr regs0 18)) /\
    rdn ASEGS M (Z_to_bv 64 (s - 40)) 8%nat = Some (word_to_le_bytes 8 (getr regs0 19)) /\
    rdn ASEGS M (Z_to_bv 64 (s - 48)) 8%nat = Some (word_to_le_bytes 8 (getr regs0 20)) /\
    rdn ASEGS M (Z_to_bv 64 (s - 56)) 8%nat = Some (word_to_le_bytes 8 (getr regs0 21)) /\
    rdn ASEGS M (Z_to_bv 64 (s - 64)) 8%nat = Some (word_to_le_bytes 8 (getr regs0 22)).
  Definition FR (regs0 : bvmap 5 word) (M : word -> option byte) : Prop := out_agree M /\ mem_grows mem0 M /\ slots_ok regs0 M.

  #[local] Ltac peel :=
    rewrite rdn_wbytes_out;
      [ | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia | cbn [Z.of_nat Pos.to_nat]; unorm; lia
        | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia ].
  #[local] Ltac slot := repeat peel; apply rdn_wbytes_hit8; unorm; lia.
  Lemma M11_FR : forall regs0, FR regs0 (M11 regs0).
  Proof. hide_dj. intros regs0. split; [apply M11_out_agree | split; [apply M11_grows|]]. unfold M11, M9. repeat split; slot. Qed.

  Lemma rdn_slot_ext : forall (M1 M2 : word -> option byte) k,
    (forall x : word, (s - 2144 <= bv_unsigned x < s)%Z -> M1 x = M2 x) -> (8 <= k <= 2144)%Z ->
    rdn ASEGS M1 (Z_to_bv 64 (s - k)) 8%nat = rdn ASEGS M2 (Z_to_bv 64 (s - k)) 8%nat.
  Proof.
    hide_dj.
    intros M1 M2 k HE Hk. apply rdn_ext; [unorm; cbn [Z.of_nat Pos.to_nat]; lia|].
    intros x Hx. rewrite u_Z2bv in Hx by lia. cbn [Z.of_nat Pos.to_nat] in Hx. apply HE. lia.
  Qed.
  Lemma slots_ok_ext : forall regs0 (M1 M2 : word -> option byte),
    (forall x : word, (s - 2144 <= bv_unsigned x < s)%Z -> M2 x = M1 x) -> slots_ok regs0 M1 -> slots_ok regs0 M2.
  Proof.
    hide_dj.
    intros regs0 M1 M2 HE (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8). unfold slots_ok.
    rewrite !(rdn_slot_ext M2 M1) by (first [exact HE | lia]). repeat split; assumption.
  Qed.
  Lemma FR_region : forall regs0 M M', FR regs0 M -> frame_only M (s - 2144) M' -> mem_grows M M' -> FR regs0 M'.
  Proof.
    hide_dj.
    intros regs0 M M' (O & G & R) HF HGr. split; [|split].
    - intros x Hx. rewrite (HF x) by lia. apply O. exact Hx.
    - eapply mem_grows_trans; [exact G | exact HGr].
    - apply (slots_ok_ext regs0 M M'); [|exact R]. intros x Hx. apply HF. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma rdnWS : forall M, out_agree M -> (0 < n <= 64)%Z -> exists w0 w1,
    rdn ASEGS M (Z_to_bv 64 faS) 8%nat = Some w0 /\ rdn ASEGS M (Z_to_bv 64 laS) 8%nat = Some w1
    /\ (0 <= bytes_le_to_Z w0 < 2 ^ 64)%Z /\ (0 <= bytes_le_to_Z w1 < 2 ^ 64)%Z.
  Proof.
    hide_dj.
    intros M HO Hn64. pose proof (flS_facts ltac:(lia)) as (F1 & F2 & F3 & F4). unfold SB in *.
    destruct (HWS Hn64) as (w0 & w1 & R0 & R1). exists w0, w1.
    rewrite !(out_agree_rdn M) by (first [exact HO | unorm; cbn [Z.of_nat Pos.to_nat]; lia]).
    split; [exact R0 | split; [exact R1 | split; [exact (bytes8_range _ _ _ _ R0) | exact (bytes8_range _ _ _ _ R1)]]].
  Qed.
  Lemma rdn1S : forall M z, out_agree M -> (0 < n)%Z -> (fS <= z < lS)%Z -> rdn ASEGS M (Z_to_bv 64 z) 1%nat = Some [Z_to_bv 8 0].
  Proof.
    hide_dj.
    intros M z HO Hn0 Hz. pose proof (flS_facts ltac:(lia)) as (F1 & F2 & _). unfold SB in *.
    cbn [rdn]. rewrite HO by (unorm; lia). rewrite (HZS Hn0) by (unorm; lia). reflexivity.
  Qed.
  Lemma rdnLS : forall M z, out_agree M -> (0 < n)%Z -> z = lS -> rdn ASEGS M (Z_to_bv 64 z) 1%nat = Some [Z_to_bv 8 kS].
  Proof.
    hide_dj.
    intros M z HO Hn0 ->. pose proof (flS_facts ltac:(lia)) as (F1 & F2 & _). unfold SB in *.
    cbn [rdn]. rewrite HO by (unorm; lia). rewrite (HLS Hn0). reflexivity.
  Qed.
  #[local] Ltac maddr z := match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 z) by (symmetry; wval) end.
  #[local] Ltac mlbu0 F D z RD :=
    chain_step; [reflexivity
      | eapply step_lbu; [exact F | reflexivity | exact D | maddr z; apply RD; [assumption | lia | lia]]
      | step_simpl; vnorm].
  #[local] Ltac mlbk F D z RD k :=
    chain_step; [reflexivity
      | eapply step_lb; [exact F | reflexivity | exact D | maddr z; apply RD; [assumption | lia | lia]]
      | step_simpl; vnorm; rewrite (v_lb_k k ltac:(lia))].
  #[local] Ltac mldw F D z R w :=
    chain_step; [reflexivity
      | eapply step_ld with (bs := w) (v := Z_to_bv 64 (bytes_le_to_Z w)); [exact F | reflexivity | exact D | maddr z; exact R | unorm; reflexivity]
      | step_simpl; vnorm].

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition c1_post (rg : bvmap 5 word) : Prop :=
    getr rg 10 = Z_to_bv 64 K /\ getr rg 9 = Z_to_bv 64 n /\ getr rg 18 = Z_to_bv 64 p /\ getr rg 8 = Z_to_bv 64 s
    /\ getr rg 2 = Z_to_bv 64 (s - 2144).
  Lemma ret_ok_6306c : ret_ok (0x63484 : word).  Proof. hide_dj. unfold ret_ok. apply bv_eq. vm_compute. reflexivity. Qed.
  Lemma ret_ok_63074 : ret_ok (0x6348c : word).  Proof. hide_dj. unfold ret_ok. apply bv_eq. vm_compute. reflexivity. Qed.
  Lemma ret_ok_63088 : ret_ok (0x634a0 : word).  Proof. hide_dj. unfold ret_ok. apply bv_eq. vm_compute. reflexivity. Qed.

  Lemma c1_run : forall regs,
    getr regs 10 = Z_to_bv 64 p -> getr regs 2 = sp -> getr regs 1 = ra ->
    exists regs',
      msteps ASEGS (mkst regs (0x63450 : word) mem0 rom) (mkst regs' (0x634b8 : word) (M11 regs) rom)
      /\ c1_post regs' /\ keeps_but RIPL regs regs'.
  Proof.
    hide_dj.
    intros regs H10 H2 H1. rewrite sp_s in H2.
    pose proof pS_facts as (PSp & PSn & _). unfold HIGHEND in *.
    pose proof (out_agree_globs (M9 regs) (M9_out_agree regs)) as (_ & (I1 & I2 & I3 & I4)).
    pose proof (out_agree_globs (M11 regs) (M11_out_agree regs)) as (_ & (J1 & J2 & J3 & J4)).
    (* [comment removed for export] *)
    assert (S1 : exists r1, msteps ASEGS (mkst regs (0x63450 : word) mem0 rom) (mkst r1 (0x801d4 : word) (M9 regs) rom)
              /\ (getr r1 18 = Z_to_bv 64 p /\ getr r1 8 = Z_to_bv 64 s /\ getr r1 2 = Z_to_bv 64 (s - 2144) /\ getr r1 1 = (0x63484 : word)
                  /\ keeps_but RIPL regs r1)).
    { unfold M9. eexists. split.
      - stepiv F_63038 D_63038 (Z_to_bv 64 (s - 2032)) ltac:(wval).                     (* [comment removed for export] *)
        stepsd F_6303c D_6303c (Z_to_bv 64 (s - 8)) ra ltac:(fsok).                        (* [comment removed for export] *)
        stepsd F_63040 D_63040 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(fsok).             (* [comment removed for export] *)
        stepsd F_63044 D_63044 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(fsok).             (* [comment removed for export] *)
        stepsd F_63048 D_63048 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(fsok).            (* [comment removed for export] *)
        stepsd F_6304c D_6304c (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(fsok).            (* [comment removed for export] *)
        stepsd F_63050 D_63050 (Z_to_bv 64 (s - 48)) (getr regs 20) ltac:(fsok).            (* [comment removed for export] *)
        stepsd F_63054 D_63054 (Z_to_bv 64 (s - 56)) (getr regs 21) ltac:(fsok).            (* [comment removed for export] *)
        stepsd F_63058 D_63058 (Z_to_bv 64 (s - 64)) (getr regs 22) ltac:(fsok).            (* [comment removed for export] *)
        stepiv F_6305c D_6305c (Z_to_bv 64 s) ltac:(wval).                                  (* [comment removed for export] *)
        stepiv F_63060 D_63060 (Z_to_bv 64 (s - 2144)) ltac:(wval).                         (* [comment removed for export] *)
        stepiv F_63064 D_63064 (Z_to_bv 64 p) ltac:(wval).                                  (* [comment removed for export] *)
        stepn F_63068 D_63068.                                                               (* [comment removed for export] *)
        apply mst_refl.
      - repeat split; gres; rwH; try reflexivity; try (apply bv_eq; vm_compute; reflexivity). solve_keeps_but. }
    destruct S1 as (r1 & RUN1 & Q18 & Q8 & Q2 & Q1 & K1).
    destruct (asan_inited_run r1 (M9 regs) rom (0x63484 : word) Q1 ret_ok_6306c I1) as (r2 & RUN2 & V10 & OA).
    assert (V18 : getr r2 18 = Z_to_bv 64 p) by (rewrite (OA 18%bv) by (intros E; discriminate E); exact Q18).
    assert (V8 : getr r2 8 = Z_to_bv 64 s) by (rewrite (OA 8%bv) by (intros E; discriminate E); exact Q8).
    assert (V2 : getr r2 2 = Z_to_bv 64 (s - 2144)) by (rewrite (OA 2%bv) by (intros E; discriminate E); exact Q2).
    assert (K2 : keeps_but RIPL r1 r2) by (intros r Hr HL; apply OA; intros ->; cbv in Hr; intuition discriminate).
    (* [comment removed for export] *)
    assert (S3 : exists r3, msteps ASEGS (mkst r2 (0x63484 : word) (M9 regs) rom) (mkst r3 (0x810e4 : word) (M9 regs) rom)
              /\ (getr r3 18 = Z_to_bv 64 p /\ getr r3 8 = Z_to_bv 64 s /\ getr r3 2 = Z_to_bv 64 (s - 2144) /\ getr r3 1 = (0x6348c : word)
                  /\ keeps_but RIPL r2 r3)).
    { eexists. split.
      - stepb_ft F_6306c D_6306c ltac:(cond).                                              (* [comment removed for export] *)
        stepn F_63070 D_63070.                                                               (* [comment removed for export] *)
        apply mst_refl.
      - repeat split; gres; rwH; try reflexivity; try (apply bv_eq; vm_compute; reflexivity). solve_keeps_but. }
    destruct S3 as (r3 & RUN3 & T18 & T8 & T2 & T1 & K3).
    destruct (tryinit_fast_run r3 (M9 regs) rom (0x6348c : word) (s - 2144) T2 T1 ret_ok_63074 ltac:(lia) ltac:(lia)
                ltac:(replace (s - 2144 - 16)%Z with (s - 2160)%Z by lia; apply out_agree_store_ok; [apply M9_grows | cbn; lia]) I1)
      as (r4 & RUN4 & U10 & U2 & U8 & U1 & K4).
    replace (s - 2144 - 8)%Z with (s - 2152)%Z in RUN4 by lia. replace (s - 2144 - 16)%Z with (s - 2160)%Z in RUN4 by lia.
    rewrite T8 in RUN4. change (wbytes (wbytes (M9 regs) (Z_to_bv 64 (s - 2152)) (word_to_le_bytes 8 (0x6348c : word))) (Z_to_bv 64 (s - 2160)) (word_to_le_bytes 8 (Z_to_bv 64 s))) with (M11 regs) in RUN4.
    assert (U18 : getr r4 18 = Z_to_bv 64 p) by (rewrite (K4 18%bv) by (first [cbv; tauto | cbv; intuition discriminate]); exact T18).
    rewrite T8 in U8.
    (* [comment removed for export] *)
    assert (S5 : exists r5, msteps ASEGS (mkst r4 (0x6348c : word) (M11 regs) rom) (mkst r5 (0x12a1e8 : word) (M11 regs) rom)
              /\ (getr r5 10 = Z_to_bv 64 p /\ getr r5 9 = Z_to_bv 64 1 /\ getr r5 18 = Z_to_bv 64 p /\ getr r5 8 = Z_to_bv 64 s
                  /\ getr r5 2 = Z_to_bv 64 (s - 2144) /\ getr r5 1 = (0x634a0 : word) /\ keeps_but RIPL r4 r5)).
    { eexists. split.
      - stepn F_63074 D_63074.                                                               (* [comment removed for export] *)
        mld F_63078 D_63078 (0x1392d8 : word) J2.                                             (* [comment removed for export] *)
        stepiv F_6307c D_6307c (Z_to_bv 64 1) ltac:(wval).                                  (* [comment removed for export] *)
        stepiv F_63080 D_63080 (Z_to_bv 64 p) ltac:(wval).                                  (* [comment removed for export] *)
        stepjr F_63084 D_63084 (Z_to_bv 64 0x12a1e8) ltac:(gres; reflexivity).                (* [comment removed for export] *)
        vnorm. apply mst_refl.
      - repeat split; gres; rwH; try reflexivity; try (apply bv_eq; vm_compute; reflexivity). solve_keeps_but. }
    destruct S5 as (r5 & RUN5 & W10 & W9 & W18 & W8 & W2 & W1 & K5).
    destruct (ref_strlen (M11 regs) (Z_to_bv 64 p) buf K rom r5 (0x634a0 : word) (out_agree_slenH (M11 regs) (M11_out_agree regs))
                ret_ok_63088 W1 W10) as (r6 & RUN6 & AG6 & X10).
    assert (X9 : getr r6 9 = Z_to_bv 64 1) by (rewrite (sl_agree_getr _ _ 9%bv AG6) by (cbv; intuition discriminate); exact W9).
    assert (X18 : getr r6 18 = Z_to_bv 64 p) by (rewrite (sl_agree_getr _ _ 18%bv AG6) by (cbv; intuition discriminate); exact W18).
    assert (X8 : getr r6 8 = Z_to_bv 64 s) by (rewrite (sl_agree_getr _ _ 8%bv AG6) by (cbv; intuition discriminate); exact W8).
    assert (X2 : getr r6 2 = Z_to_bv 64 (s - 2144)) by (rewrite (sl_agree_getr _ _ 2%bv AG6) by (cbv; intuition discriminate); exact W2).
    assert (K6 : keeps_but RIPL r5 r6).
    { intros r Hr HL. apply (sl_agree_getr _ _ r AG6). unfold sl_clob. cbv in Hr. cbn [In]. intuition (subst; discriminate). }
    (* [comment removed for export] *)
    eexists. split.
    - eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3|].
      eapply msteps_trans; [exact RUN4|]. eapply msteps_trans; [exact RUN5|]. eapply msteps_trans; [exact RUN6|].
      stepb_ft F_63088 D_63088 ltac:(cond).                                                (* [comment removed for export] *)
      stepn F_6308c D_6308c.                                                               (* [comment removed for export] *)
      mld F_63090 D_63090 (0x1374b0 : word) J3.                                             (* [comment removed for export] *)
      mlbu F_63094 D_63094 (0x1d1863 : word) J4.                                           (* [comment removed for export] *)
      stepb_ft F_63098 D_63098 ltac:(cond).                                                (* [comment removed for export] *)
      stepiv F_6309c D_6309c (Z_to_bv 64 n) ltac:(wval).                                  (* [comment removed for export] *)
      apply mst_refl.
    - unfold c1_post. split; [repeat split; gres; rwH; try reflexivity; f_equal; lia|].
      eapply keeps_but_trans; [exact K1|]. eapply keeps_but_trans; [exact K2|]. eapply keeps_but_trans; [exact K3|].
      eapply keeps_but_trans; [| eapply keeps_but_trans; [exact K5 | eapply keeps_but_trans; [exact K6 |]]].
      + intros r Hr HL. apply K4; [exact Hr|]. cbv in HL |- *. intuition.
      + solve_keeps_but.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition cR_pre (rg : bvmap 5 word) : Prop :=
    getr rg 10 = Z_to_bv 64 K /\ getr rg 9 = Z_to_bv 64 n /\ getr rg 18 = Z_to_bv 64 p /\ getr rg 8 = Z_to_bv 64 s
    /\ getr rg 2 = Z_to_bv 64 (s - 2144).
  Definition cR_post (rg : bvmap 5 word) : Prop :=
    getr rg 10 = Z_to_bv 64 K /\ getr rg 2 = Z_to_bv 64 (s - 2144).

  (* [comment removed for export] *)
  Lemma ret_ok_6320c : ret_ok (0x63624 : word).  Proof. hide_dj. unfold ret_ok. apply bv_eq. vm_compute. reflexivity. Qed.
  Lemma cRr_run : forall regs0 M regs,
    cR_pre regs -> FR regs0 M -> (64 < n)%Z ->
    exists regs' M',
      msteps ASEGS (mkst regs (0x634b8 : word) M rom) (mkst regs' (0x63508 : word) M' rom)
      /\ cR_post regs' /\ keeps_but RIPL regs regs' /\ FR regs0 M'.
  Proof.
    hide_dj.
    intros regs0 M regs (H10 & H9 & H18 & H8 & H2) HFR Hn64. pose proof HFR as (HO & HGr & HR).
    pose proof pS_facts as (Pp & Ppn & Pp8 & Pq). specialize (Pq ltac:(lia)). pose proof pS_facts as (XSp & XSn & XS8 & XSq). pose proof pD_facts as (XDp & XDn & XD8 & XDq). unfold HIGHEND in *.
    assert (S1 : exists r1, msteps ASEGS (mkst regs (0x634b8 : word) M rom) (mkst r1 (0x7b4c0 : word) M rom)
              /\ (getr r1 10 = Z_to_bv 64 p /\ getr r1 11 = Z_to_bv 64 n /\ getr r1 2 = Z_to_bv 64 (s - 2144) /\ getr r1 1 = (0x63624 : word)
                  /\ getr r1 21 = Z_to_bv 64 K /\ getr r1 9 = Z_to_bv 64 n /\ getr r1 18 = Z_to_bv 64 p /\ getr r1 8 = Z_to_bv 64 s /\ keeps_but RIPL regs r1)).
    { eexists. split.
      - stepiv F_630a0 D_630a0 (Z_to_bv 64 (2 ^ 64 - 1 - p)) ltac:(xval).
        stepiv F_630a4 D_630a4 (Z_to_bv 64 (s - 2048)) ltac:(wval).
        stepiv F_630a8 D_630a8 (Z_to_bv 64 (s - 2136)) ltac:(wval).
        stepb_ft F_630ac D_630ac ltac:(cond).
        stepn F_630b0 D_630b0.
        stepb_tk F_630b4 D_630b4 ltac:(cond).                                          (* [comment removed for export] *)
        stepiv F_631b8 D_631b8 (Z_to_bv 64 K) ltac:(wval).                                 (* [comment removed for export] *)
        stepb_tk F_631bc D_631bc ltac:(cond).                                            (* [comment removed for export] *)
        stepiv F_63200 D_63200 (Z_to_bv 64 p) ltac:(wval).                                 (* [comment removed for export] *)
        stepiv F_63204 D_63204 (Z_to_bv 64 n) ltac:(wval).                                 (* [comment removed for export] *)
        stepn F_63208 D_63208.                                                             (* [comment removed for export] *)
        apply mst_refl.
      - repeat split; gres; rwH; try reflexivity; try (f_equal; lia); try (apply bv_eq; vm_compute; reflexivity). solve_keeps_but. }
    destruct S1 as (r1 & RUN1 & Q10 & Q11 & Q2 & Q1 & Q21 & Q9 & Q18 & Q8 & K1).
    pose proof (out_agree_globs M HO) as (HGM & _).
    pose proof (region_is_poisoned_run M rom (Z_to_bv 64 (s - 2144)) (0x63624 : word) p n (s - 2144)
                  ltac:(unorm; reflexivity) ltac:(lia) HappS ltac:(lia) ltac:(unfold SB in *; lia)
                  ltac:(replace (s - 2144 - 72)%Z with (s - 2216)%Z by lia; apply out_agree_store_ok; [exact HGr | cbn; lia])
                  (ret_ok_6320c) HGM kS) as RP.
    specialize (RP ltac:(intros x Hx; rewrite (HO x) by (unfold SB in *; lia); apply HZS; [lia | unfold SB in *; lia])).
    specialize (RP ltac:(rewrite HO by (unfold SB in *; unorm; lia); rewrite <- HlS_def; apply HLS; lia) HkS).
    destruct (RP r1 Q10 Q11 Q2 Q1) as (r2 & M2 & RUN2 & V10 & V2 & V1 & K2 & F2 & G2).
    assert (S21 : getr r2 21 = Z_to_bv 64 K) by (rewrite (K2 21%bv) by (cbv; tauto); exact Q21).
    assert (S9 : getr r2 9 = Z_to_bv 64 n) by (rewrite (K2 9%bv) by (cbv; tauto); exact Q9).
    assert (S18 : getr r2 18 = Z_to_bv 64 p) by (rewrite (K2 18%bv) by (cbv; tauto); exact Q18).
    assert (S8 : getr r2 8 = Z_to_bv 64 s) by (rewrite (K2 8%bv) by (cbv; tauto); exact Q8).
    eexists. exists M2. split; [|split; [|split; [|eapply FR_region; eassumption]]].
    - eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|].
      stepb_tk F_6320c D_6320c ltac:(cond).                                          (* [comment removed for export] *)
      stepiv F_632c4 D_632c4 (Z_to_bv 64 K) ltac:(wval).                                  (* [comment removed for export] *)
      stepn F_632c8 D_632c8.                                                                (* [comment removed for export] *)
      apply mst_refl.
    - unfold cR_post. post.
    - eapply keeps_but_trans; [exact K1|]. solve_keeps_but.
  Qed.

  (* [comment removed for export] *)
  Definition cRqa_post (u0 u1 : Z) (rg : bvmap 5 word) : Prop :=
    getr rg 11 = Z_to_bv 64 fS /\ getr rg 12 = Z_to_bv 64 lS /\ getr rg 13 = Z_to_bv 64 (p + n - 1) /\ getr rg 14 = Z_to_bv 64 (Z.lor u1 u0)
    /\ getr rg 10 = Z_to_bv 64 K /\ getr rg 9 = Z_to_bv 64 n /\ getr rg 18 = Z_to_bv 64 p /\ getr rg 8 = Z_to_bv 64 s /\ getr rg 2 = Z_to_bv 64 (s - 2144).
  Lemma cRqa_run : forall M regs w0 w1,
    cR_pre regs -> out_agree M -> (0 < n <= 64)%Z ->
    rdn ASEGS M (Z_to_bv 64 faS) 8%nat = Some w0 -> rdn ASEGS M (Z_to_bv 64 laS) 8%nat = Some w1 ->
    (0 <= bytes_le_to_Z w0 < 2 ^ 64)%Z -> (0 <= bytes_le_to_Z w1 < 2 ^ 64)%Z ->
    exists regs',
      msteps ASEGS (mkst regs (0x634b8 : word) M rom) (mkst regs' (0x63504 : word) M rom)
      /\ cRqa_post (bytes_le_to_Z w0) (bytes_le_to_Z w1) regs' /\ keeps_but RIPL regs regs'.
  Proof.
    hide_dj.
    intros M regs w0 w1 (H10 & H9 & H18 & H8 & H2) HO Hn64 R0 R1 B0 B1.
    pose proof pS_facts as (Pp & Ppn & Pp8 & Pq). specialize (Pq ltac:(lia)). pose proof pS_facts as (XSp & XSn & XS8 & XSq). pose proof pD_facts as (XDp & XDn & XD8 & XDq).
    pose proof (flS_facts ltac:(lia)) as (F1 & F2 & F3 & F4).
    pose proof (out_agree_globs M HO) as ((G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8) & _).
    unfold SB, HIGHEND in *.
    pose proof (Z.div_mod p 8 ltac:(lia)) as Dp. pose proof (Z.mod_pos_bound p 8 ltac:(lia)) as Mp.
    pose proof (Z.mod_pos_bound fS 8 ltac:(lia)) as Mf. pose proof (Z.mod_pos_bound lS 8 ltac:(lia)) as Ml.
    pose proof (lor_bound64 (bytes_le_to_Z w1) (bytes_le_to_Z w0) B1 B0) as BL.
    eexists. split.
    - stepiv F_630a0 D_630a0 (Z_to_bv 64 (2 ^ 64 - 1 - p)) ltac:(xval).
      stepiv F_630a4 D_630a4 (Z_to_bv 64 (s - 2048)) ltac:(wval).                                   (* [comment removed for export] *)
      stepiv F_630a8 D_630a8 (Z_to_bv 64 (s - 2136)) ltac:(wval).                                   (* [comment removed for export] *)
      stepb_ft F_630ac D_630ac ltac:(cond).
      stepn F_630b0 D_630b0.
      stepb_ft F_630b4 D_630b4 ltac:(cond).                                            (* [comment removed for export] *)
      stepn F_630b8 D_630b8.                                                         (* [comment removed for export] *)
      mld F_630bc D_630bc (0x1374c0 : word) G1.                                       (* [comment removed for export] *)
      mld F_630c0 D_630c0 (0x13fc38 : word) G2.                                           (* [comment removed for export] *)
      stepiv F_630c4 D_630c4 (Z_to_bv 64 (p + n - 1)) ltac:(wval).                      (* [comment removed for export] *)
      stepiv F_630c8 D_630c8 (Z_to_bv 64 (p / 8)) ltac:(wval).                          (* [comment removed for export] *)
      stepiv F_630cc D_630cc (Z_to_bv 64 ((p + n - 1) / 8)) ltac:(wval).                (* [comment removed for export] *)
      stepiv F_630d0 D_630d0 (Z_to_bv 64 fS) ltac:(wval).                               (* [comment removed for export] *)
      stepiv F_630d4 D_630d4 (Z_to_bv 64 lS) ltac:(wval).                               (* [comment removed for export] *)
      stepiv F_630d8 D_630d8 (Z_to_bv 64 faS)
        ltac:(gres; rwH; unfold v_andi; imm_norm; replace (bv_wrap 64 (-8)) with (2 ^ 64 - 8)%Z by reflexivity; unorm; rewrite land_down8 by lia; f_equal; lia).
      stepiv F_630dc D_630dc (Z_to_bv 64 laS)
        ltac:(gres; rwH; unfold v_andi; imm_norm; replace (bv_wrap 64 (-8)) with (2 ^ 64 - 8)%Z by reflexivity; unorm; rewrite land_down8 by lia; f_equal; lia).
      mldw F_630e0 D_630e0 faS R0 w0.                                                    (* [comment removed for export] *)
      mldw F_630e4 D_630e4 laS R1 w1.                                                    (* [comment removed for export] *)
      stepov F_630e8 D_630e8 (Z_to_bv 64 (Z.lor (bytes_le_to_Z w1) (bytes_le_to_Z w0))) ltac:(gres; rwH; unfold v_or; unorm; reflexivity).
      apply mst_refl.
    - unfold cRqa_post. split; [post | solve_keeps_but].
  Qed.

  (* [comment removed for export] *)
  Definition qlR_inv (rg : bvmap 5 word) (i : Z) : Prop :=
    getr rg 11 = Z_to_bv 64 (fS + i) /\ getr rg 12 = Z_to_bv 64 lS /\ getr rg 10 = Z_to_bv 64 0 /\ getr rg 21 = Z_to_bv 64 K /\ getr rg 9 = Z_to_bv 64 n /\ getr rg 18 = Z_to_bv 64 p /\ getr rg 8 = Z_to_bv 64 s /\ getr rg 2 = Z_to_bv 64 (s - 2144).
  Definition qlR_post (rg : bvmap 5 word) : Prop :=
    getr rg 10 = Z_to_bv 64 0 /\ getr rg 21 = Z_to_bv 64 K /\ getr rg 9 = Z_to_bv 64 n /\ getr rg 18 = Z_to_bv 64 p /\ getr rg 8 = Z_to_bv 64 s /\ getr rg 2 = Z_to_bv 64 (s - 2144).
  Lemma qloopR_run : forall M (q : nat) regs i,
    out_agree M -> (0 < n)%Z -> qlR_inv regs i -> (0 <= i)%Z -> (fS + i + Z.of_nat q + 1 = lS)%Z ->
    exists regs',
      msteps ASEGS (mkst regs (0x63600 : word) M rom) (mkst regs' (0x63610 : word) M rom)
      /\ qlR_post regs' /\ keeps_but RIPL regs regs'.
  Proof.
    hide_dj.
    intros M q. induction q as [|q IH]; intros regs i HO Hn0 (H13 & H14 & H15 & H21 & H9 & H18 & H8 & H2) Hi Hq; 
      pose proof (flS_facts Hn0) as (F1 & F2 & _); unfold SB in *.
    - eexists. split.
      + mlbu0 F_631e8 D_631e8 (fS + i)%Z rdn1S.                                      (* [comment removed for export] *)
        stepiv F_631ec D_631ec (Z_to_bv 64 (fS + i + 1)) ltac:(wval).                (* [comment removed for export] *)
        stepov F_631f0 D_631f0 (Z_to_bv 64 0) ltac:(vlit).                            (* [comment removed for export] *)
        stepb_ft F_631f4 D_631f4 ltac:(cond).                                        (* [comment removed for export] *)
        apply mst_refl.
      + unfold qlR_post. post.
    - eapply (runs_trans ASEGS _ (fun rg => mkst rg (0x63600 : word) M rom) (fun rg => qlR_inv rg (i + 1) /\ keeps_but RIPL regs rg)).
      + eexists. split.
        * mlbu0 F_631e8 D_631e8 (fS + i)%Z rdn1S.
          stepiv F_631ec D_631ec (Z_to_bv 64 (fS + i + 1)) ltac:(wval).
          stepov F_631f0 D_631f0 (Z_to_bv 64 0) ltac:(vlit).
          stepb_tk F_631f4 D_631f4 ltac:(cond).                                      (* [comment removed for export] *)
          apply mst_refl.
        * unfold qlR_inv. post.
      + cbv beta. intros r1 (I1 & K1).
        destruct (IH r1 (i + 1)%Z HO Hn0 I1 ltac:(lia) ltac:(lia)) as (r2 & RUN & P2 & K2).
        exists r2. split; [exact RUN | split; [exact P2 | eapply keeps_but_trans; eassumption]].
  Qed.

  (* [comment removed for export] *)
  Lemma cRqf_run : forall M regs u0 u1,
    cRqa_post u0 u1 regs -> (0 <= Z.lor u1 u0 < 2 ^ 64)%Z -> Z.lor u1 u0 = 0%Z ->
    exists regs',
      msteps ASEGS (mkst regs (0x63504 : word) M rom) (mkst regs' (0x63508 : word) M rom)
      /\ cR_post regs' /\ keeps_but RIPL regs regs'.
  Proof.
    hide_dj.
    intros M regs u0 u1 (H13 & H14 & HL' & H15 & H10 & H9 & H18 & H8 & H2) BL E.
    eexists. split.
    - stepb_ft F_630ec D_630ec ltac:(cond).                                           (* [comment removed for export] *)
      apply mst_refl.
    - unfold cR_post. post.
  Qed.

  (* [comment removed for export] *)
  Lemma cRqs_run : forall M regs u0 u1,
    cRqa_post u0 u1 regs -> out_agree M -> (0 < n <= 64)%Z -> (0 <= Z.lor u1 u0 < 2 ^ 64)%Z -> Z.lor u1 u0 <> 0%Z ->
    exists regs',
      msteps ASEGS (mkst regs (0x63504 : word) M rom) (mkst regs' (0x63508 : word) M rom)
      /\ cR_post regs' /\ keeps_but RIPL regs regs'.
  Proof.
    hide_dj.
    intros M regs u0 u1 (H13 & H14 & HL' & H15 & H10 & H9 & H18 & H8 & H2) HO Hn64 BL NE.
    pose proof pS_facts as (Pp & Ppn & Pp8 & Pq). specialize (Pq ltac:(lia)). pose proof pS_facts as (XSp & XSn & XS8 & XSq). pose proof pD_facts as (XDp & XDn & XD8 & XDq).
    pose proof (flS_facts ltac:(lia)) as (F1 & F2 & F3 & F4). unfold SB, HIGHEND in *.
    pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(lia)) as Mq.
    eapply (runs_trans ASEGS _ (fun rg => mkst rg (0x635fc : word) M rom) (fun rg => qlR_inv rg 0 /\ keeps_but RIPL regs rg)).
    { unhide HkS. destruct HkS as [K0|K7].
      - eexists. split.
        + stepb_tk F_630ec D_630ec ltac:(cond).                                       (* [comment removed for export] *)
          stepiv F_631c8 D_631c8 (Z_to_bv 64 K) ltac:(wval).                               (* [comment removed for export] *)
          mlbk F_631cc D_631cc lS rdnLS kS.                                             (* [comment removed for export] *)
          stepiv F_631d0 D_631d0 (Z_to_bv 64 ((p + n - 1) mod 8))
            ltac:(gres; rwH; unfold v_andi; imm_norm; unorm; rewrite land7_mod8; reflexivity). (* [comment removed for export] *)
          stepov F_631d4 D_631d4 (Z_to_bv 64 0)
            ltac:(gres; rwH; unfold v_sltu, c_ltu, bv_ltu; unorm; replace (0 <? kS)%Z with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).
          stepov F_631d8 D_631d8 (Z_to_bv 64 0)
            ltac:(gres; rwH; unfold v_slt, c_lts, bv_lts; rewrite !signed64_small by lia;
                  replace ((p + n - 1) mod 8 <? kS)%Z with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).
          stepiv F_631dc D_631dc (Z_to_bv 64 1) ltac:(vlit).
          stepov F_631e0 D_631e0 (Z_to_bv 64 0) ltac:(vlit).
          apply mst_refl.
        + unfold qlR_inv. post.
      - eexists. split.
        + stepb_tk F_630ec D_630ec ltac:(cond).
          stepiv F_631c8 D_631c8 (Z_to_bv 64 K) ltac:(wval).                               (* [comment removed for export] *)
          mlbk F_631cc D_631cc lS rdnLS kS.
          stepiv F_631d0 D_631d0 (Z_to_bv 64 ((p + n - 1) mod 8))
            ltac:(gres; rwH; unfold v_andi; imm_norm; unorm; rewrite land7_mod8; reflexivity).
          stepov F_631d4 D_631d4 (Z_to_bv 64 1)
            ltac:(gres; rwH; unfold v_sltu, c_ltu, bv_ltu; unorm; replace (0 <? kS)%Z with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
          stepov F_631d8 D_631d8 (Z_to_bv 64 1)
            ltac:(gres; rwH; unfold v_slt, c_lts, bv_lts; rewrite !signed64_small by lia;
                  replace ((p + n - 1) mod 8 <? kS)%Z with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
          stepiv F_631dc D_631dc (Z_to_bv 64 0) ltac:(vlit).
          stepov F_631e0 D_631e0 (Z_to_bv 64 0) ltac:(vlit).
          apply mst_refl.
        + unfold qlR_inv. post. }
    cbv beta. intros r1 ((I13 & I14 & I15 & I21 & I9 & I18 & I8 & I2) & K1).
    eapply (runs_trans ASEGS _ (fun rg => mkst rg (0x63610 : word) M rom) (fun rg => qlR_post rg /\ keeps_but RIPL regs rg)).
    { destruct (Z.lt_ge_cases fS lS) as [Hfl|Hfl].
      - eapply (runs_trans ASEGS _ (fun rg => mkst rg (0x63600 : word) M rom) (fun rg => qlR_inv rg 0 /\ keeps_but RIPL regs rg)).
        + eexists. split.
          * stepb_ft F_631e4 D_631e4 ltac:(cond).                                   (* [comment removed for export] *)
            apply mst_refl.
          * split; [unfold qlR_inv; repeat split; assumption | exact K1].
        + cbv beta. intros r2 (I2' & K2).
          destruct (qloopR_run M (Z.to_nat (lS - fS - 1)) r2 0 HO ltac:(lia) I2' ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia)) as (r3 & RUN3 & P3 & K3).
          exists r3. split; [exact RUN3 | split; [exact P3 | eapply keeps_but_trans; eassumption]].
      - eexists. split.
        + stepb_tk F_631e4 D_631e4 ltac:(cond).                                     (* [comment removed for export] *)
          apply mst_refl.
        + split; [unfold qlR_post; repeat split; assumption | exact K1]. }
    cbv beta. intros r4 ((J15 & J21 & J9 & J18 & J8 & J2) & K4).
    eexists. split.
    - stepiv F_631f8 D_631f8 (Z_to_bv 64 0) ltac:(vlit).                             (* [comment removed for export] *)
      stepb_tk F_631fc D_631fc ltac:(cond).                                           (* [comment removed for export] *)
      stepiv F_632c4 D_632c4 (Z_to_bv 64 K) ltac:(wval).                                  (* [comment removed for export] *)
      stepn F_632c8 D_632c8.                                                                (* [comment removed for export] *)
      apply mst_refl.
    - unfold cR_post. split; [post|]. eapply keeps_but_trans; [exact K4|]. solve_keeps_but.
  Qed.

  (* [comment removed for export] *)
  Lemma cR_run : forall regs0 M regs,
    cR_pre regs -> FR regs0 M ->
    exists regs' M',
      msteps ASEGS (mkst regs (0x634b8 : word) M rom) (mkst regs' (0x63508 : word) M' rom)
      /\ cR_post regs' /\ keeps_but RIPL regs regs' /\ FR regs0 M'.
  Proof.
    hide_dj.
    intros regs0 M regs P1 HFR. pose proof HFR as (HO & HGr & HR).
    destruct (Z.eq_dec n 0) as [Hn0|Hn0].
    { exfalso. lia. }

    destruct (Z.le_gt_cases n 64) as [Hle|Hgt].
    - destruct (rdnWS M HO ltac:(lia)) as (w0 & w1 & R0 & R1 & B0 & B1).
      destruct (cRqa_run M regs w0 w1 P1 HO ltac:(lia) R0 R1 B0 B1) as (r2 & RUN2 & P2 & K2).
      pose proof (lor_bound64 _ _ B1 B0) as BL.
      destruct (Z.eq_dec (Z.lor (bytes_le_to_Z w1) (bytes_le_to_Z w0)) 0) as [E|NE].
      + destruct (cRqf_run M r2 _ _ P2 BL E) as (r3 & RUN3 & P3 & K3). exists r3, M.
        split; [eapply msteps_trans; [exact RUN2 | exact RUN3] | split; [exact P3 | split; [eapply keeps_but_trans; eassumption | exact HFR]]].
      + destruct (cRqs_run M r2 _ _ P2 HO ltac:(lia) BL NE) as (r3 & RUN3 & P3 & K3). exists r3, M.
        split; [eapply msteps_trans; [exact RUN2 | exact RUN3] | split; [exact P3 | split; [eapply keeps_but_trans; eassumption | exact HFR]]].
    - exact (cRr_run regs0 M regs P1 HFR Hgt).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma c3_run : forall regs0 regs M,
    cR_post regs -> FR regs0 M ->
    exists regs',
      msteps ASEGS (mkst regs (0x63508 : word) M rom) (mkst regs' ra M rom)
      /\ getr regs' 10 = Z_to_bv 64 K /\ getr regs' 2 = sp /\ getr regs' 1 = ra
      /\ getr regs' 8 = getr regs0 8 /\ getr regs' 9 = getr regs0 9 /\ getr regs' 18 = getr regs0 18
      /\ getr regs' 19 = getr regs0 19 /\ getr regs' 20 = getr regs0 20 /\ getr regs' 21 = getr regs0 21
      /\ getr regs' 22 = getr regs0 22
      /\ keeps_but RIPL regs regs'.
  Proof.
    hide_dj.
    intros regs0 regs M (H10 & H2) (HO & HGr & (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8)).
    eexists. split.
    - stepiv F_630f0 D_630f0 (Z_to_bv 64 (s - 2032)) ltac:(wval).                        (* [comment removed for export] *)
      stepld F_630f4 D_630f4 ra ltac:(maddr (s - 8)%Z; exact R1).                         (* [comment removed for export] *)
      stepld F_630f8 D_630f8 (getr regs0 8) ltac:(maddr (s - 16)%Z; exact R2).            (* [comment removed for export] *)
      stepld F_630fc D_630fc (getr regs0 9) ltac:(maddr (s - 24)%Z; exact R3).            (* [comment removed for export] *)
      stepld F_63100 D_63100 (getr regs0 18) ltac:(maddr (s - 32)%Z; exact R4).           (* [comment removed for export] *)
      stepld F_63104 D_63104 (getr regs0 19) ltac:(maddr (s - 40)%Z; exact R5).           (* [comment removed for export] *)
      stepld F_63108 D_63108 (getr regs0 20) ltac:(maddr (s - 48)%Z; exact R6).           (* [comment removed for export] *)
      stepld F_6310c D_6310c (getr regs0 21) ltac:(maddr (s - 56)%Z; exact R7).           (* [comment removed for export] *)
      stepld F_63110 D_63110 (getr regs0 22) ltac:(maddr (s - 64)%Z; exact R8).           (* [comment removed for export] *)
      stepiv F_63114 D_63114 (Z_to_bv 64 s) ltac:(wval).                                  (* [comment removed for export] *)
      stepret F_63118 D_63118 ra ltac:(rwH; reflexivity).
      apply mst_refl.
    - repeat split; gres; try reflexivity; [exact H10 | symmetry; apply sp_s | solve_keeps_but].
  Qed.

  (* [comment removed for export] *)
  Theorem strlen_icpt_run : forall regs,
    getr regs 10 = Z_to_bv 64 p -> getr regs 2 = sp -> getr regs 1 = ra ->
    exists regs' M',
      msteps ASEGS (mkst regs (0x63450 : word) mem0 rom) (mkst regs' ra M' rom)
      /\ getr regs' 10 = Z_to_bv 64 K /\ getr regs' 2 = sp /\ getr regs' 1 = ra /\ keeps_cs regs regs'
      /\ out_agree M' /\ mem_grows mem0 M'.
  Proof.
    hide_dj.
    intros regs H10 H2 H1.
    destruct (c1_run regs H10 H2 H1) as (r1 & RUN1 & P1 & K1).
    destruct (cR_run regs (M11 regs) r1 P1 (M11_FR regs)) as (r2 & M2 & RUN2 & P2 & K2 & F2).
    destruct (c3_run regs r2 M2 P2 F2) as (r4 & RUN4 & Q10 & Q2 & Q1 & Q8 & Q9 & Q18 & Q19 & Q20 & Q21 & Q22 & K4).
    exists r4, M2. split.
    - eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. exact RUN4.
    - assert (KB : keeps_but RIPL regs r4).
      { eapply keeps_but_trans; [exact K1|]. eapply keeps_but_trans; [exact K2|]. exact K4. }
      destruct F2 as (HO & HGr & _).
      split; [exact Q10|]. split; [exact Q2|]. split; [exact Q1|]. split; [| split; [exact HO | exact HGr]].
      intros r Hr. destruct (decide (r = 1%bv)) as [->|N1]; [rewrite Q1, H1; reflexivity|].
      destruct (decide (r = 2%bv)) as [->|N2]; [rewrite Q2, H2; reflexivity|].
      destruct (decide (r = 8%bv)) as [->|N8]; [exact Q8|]. destruct (decide (r = 9%bv)) as [->|N9]; [exact Q9|].
      destruct (decide (r = 18%bv)) as [->|N18]; [exact Q18|]. destruct (decide (r = 19%bv)) as [->|N19]; [exact Q19|].
      destruct (decide (r = 20%bv)) as [->|N20]; [exact Q20|]. destruct (decide (r = 21%bv)) as [->|N21]; [exact Q21|].
      destruct (decide (r = 22%bv)) as [->|N22]; [exact Q22|].
      apply KB; [exact Hr|]. cbv. intuition congruence.
  Qed.

  (* [comment removed for export] *)
  Corollary wrap_strlen_run : forall regs,
    getr regs 10 = Z_to_bv 64 p -> getr regs 2 = sp -> getr regs 1 = ra ->
    exists regs' M',
      msteps ASEGS (mkst regs (0x6336c : word) mem0 rom) (mkst regs' ra M' rom)
      /\ getr regs' 10 = Z_to_bv 64 K /\ getr regs' 2 = sp /\ getr regs' 1 = ra /\ keeps_cs regs regs'
      /\ out_agree M' /\ mem_grows mem0 M'.
  Proof.
    hide_dj.
    intros regs H10 H2 H1.
    destruct (strlen_icpt_run regs H10 H2 H1) as (r' & M' & RUN & REST).
    exists r', M'. split; [|exact REST].
    eapply msteps_trans; [|exact RUN].
    stepn F_62f54 D_62f54.                                                                  (* [comment removed for export] *)
    apply mst_refl.
  Qed.
End ASL.
End FPX_1.
