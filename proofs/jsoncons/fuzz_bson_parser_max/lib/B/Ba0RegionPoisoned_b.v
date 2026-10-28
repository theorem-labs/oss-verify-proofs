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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac RefMemcpyLib MemSplit As0StepLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0MemIsZero_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0_code_r60dd4_61420_b Ba0_code_r61770_61ab4_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.

Definition SB : Z := 0x7fff8000.
Definition LOWEND : Z := 0x7fff7fff.         (* [comment removed for export] *)
Definition HIGHBEG : Z := 0x10007fff8000.    (* [comment removed for export] *)
Definition HIGHEND : Z := 0x7fffffffffff.    (* [comment removed for export] *)

Section FPX_1. Context {fx : PropExec.FPState}.

(* [comment removed for export] *)
Definition rt_layout_globs (M : word -> option byte) : Prop :=
  rdn ASEGS M (0x1374c0 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x13fc38)) /\
  rdn ASEGS M (0x13fc38 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 SB)) /\
  rdn ASEGS M (0x1374c8 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x140928)) /\
  rdn ASEGS M (0x140928 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) /\
  rdn ASEGS M (0x1374d0 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x140930)) /\
  rdn ASEGS M (0x140930 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) /\
  rdn ASEGS M (0x1374d8 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x140920)) /\
  rdn ASEGS M (0x140920 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 HIGHEND)).

Definition in_app (p : Z) : Prop := (0 <= p <= LOWEND)%Z \/ (HIGHBEG <= p <= HIGHEND)%Z.

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
#[using="Type"] Lemma memtoshadow_run : forall regs (M rom : word -> option byte) (ret : word) (p : Z),
  rt_layout_globs M -> in_app p ->
  getr regs 10 = Z_to_bv 64 p -> getr regs 1 = ret -> ret_ok ret ->
  exists regs',
    msteps ASEGS (mkst regs (0x7b034 : word) M rom) (mkst regs' ret M rom)
    /\ getr regs' 10 = Z_to_bv 64 (p / 8 + SB) /\ keeps_cs regs regs'.
Proof.
  intros regs M rom ret p (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8) Hp H10 H1 Hret.
  unfold in_app, LOWEND, HIGHBEG, HIGHEND in Hp. unfold SB in *.
  pose proof (Z.div_mod p 8 ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound p 8 ltac:(lia)) as Hmd.
  destruct Hp as [Hlow|Hhigh].
  - eexists. split.
    + stepn F_7ac1c D_7ac1c.                                     (* [comment removed for export] *)
      mld F_7ac20 D_7ac20 (0x1374c0 : word) G1.                     (* [comment removed for export] *)
      mld F_7ac24 D_7ac24 (0x13fc38 : word) G2.                     (* [comment removed for export] *)
      stepn F_7ac28 D_7ac28.                                     (* [comment removed for export] *)
      stepn F_7ac2c D_7ac2c.                                     (* [comment removed for export] *)
      stepn F_7ac30 D_7ac30.                                     (* [comment removed for export] *)
      stepn F_7ac34 D_7ac34.                                     (* [comment removed for export] *)
      stepb_tk F_7ac38 D_7ac38 ltac:(cond).                      (* [comment removed for export] *)
      stepiv F_7ac7c D_7ac7c (Z_to_bv 64 (p / 8)) ltac:(wval).    (* [comment removed for export] *)
      stepiv F_7ac80 D_7ac80 (Z_to_bv 64 (p / 8 + 0x7fff8000)) ltac:(wval).   (* [comment removed for export] *)
      stepret F_7ac84 D_7ac84 ret ltac:(rwH; reflexivity).
      apply mst_refl.
    + split; [gres; reflexivity | solve_keeps_cs].
  - eexists. split.
    + stepn F_7ac1c D_7ac1c.
      mld F_7ac20 D_7ac20 (0x1374c0 : word) G1.
      mld F_7ac24 D_7ac24 (0x13fc38 : word) G2.
      stepn F_7ac28 D_7ac28.
      stepn F_7ac2c D_7ac2c.
      stepn F_7ac30 D_7ac30.
      stepn F_7ac34 D_7ac34.
      stepb_ft F_7ac38 D_7ac38 ltac:(cond).                      (* [comment removed for export] *)
      stepn F_7ac3c D_7ac3c.                                     (* [comment removed for export] *)
      mld F_7ac40 D_7ac40 (0x1374c8 : word) G3.                     (* [comment removed for export] *)
      stepn F_7ac44 D_7ac44.                                     (* [comment removed for export] *)
      mld F_7ac48 D_7ac48 (0x1374d0 : word) G5.                     (* [comment removed for export] *)
      mld F_7ac4c D_7ac4c (0x140928 : word) G4.                     (* [comment removed for export] *)
      mld F_7ac50 D_7ac50 (0x140930 : word) G6.                     (* [comment removed for export] *)
      stepn F_7ac54 D_7ac54.                                     (* [comment removed for export] *)
      stepb_tk F_7ac58 D_7ac58 ltac:(cond).                      (* [comment removed for export] *)
      stepn F_7ac60 D_7ac60.                                     (* [comment removed for export] *)
      mld F_7ac64 D_7ac64 (0x1374d8 : word) G7.                     (* [comment removed for export] *)
      mld F_7ac68 D_7ac68 (0x140920 : word) G8.                     (* [comment removed for export] *)
      stepn F_7ac6c D_7ac6c.                                     (* [comment removed for export] *)
      stepn F_7ac70 D_7ac70.                                     (* [comment removed for export] *)
      stepb_ft F_7ac74 D_7ac74 ltac:(cond).                      (* [comment removed for export] *)
      stepb_ft F_7ac78 D_7ac78 ltac:(cond).                      (* [comment removed for export] *)
      stepiv F_7ac7c D_7ac7c (Z_to_bv 64 (p / 8)) ltac:(wval).
      stepiv F_7ac80 D_7ac80 (Z_to_bv 64 (p / 8 + 0x7fff8000)) ltac:(wval).
      stepret F_7ac84 D_7ac84 ret ltac:(rwH; reflexivity).
      apply mst_refl.
    + split; [gres; reflexivity | solve_keeps_cs].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition keeps_but (L : list reg) (regs regs' : bvmap 5 word) : Prop :=
  forall r : reg, In r callee_saved -> ~ In r L -> getr regs' r = getr regs r.
#[using="Type"] Lemma keeps_but_refl : forall L regs, keeps_but L regs regs.  Proof. intros L regs r _ _. reflexivity. Qed.
#[using="Type"] Lemma keeps_but_trans : forall L r1 r2 r3, keeps_but L r1 r2 -> keeps_but L r2 r3 -> keeps_but L r1 r3.
Proof. intros L r1 r2 r3 A B r Hr HL. rewrite (B r Hr HL). apply A; assumption. Qed.
#[using="Type"] Lemma keeps_but_upd : forall L regs regs' (rd : reg) v,
  keeps_but L regs regs' -> (In rd L \/ ~ In rd callee_saved) -> keeps_but L regs (regupd regs' rd v).
Proof.
  intros L regs regs' rd v K Hrd r Hr HL. rewrite getr_other; [apply K; assumption|].
  intros ->. destruct Hrd as [Hrd|Hrd]; [exact (HL Hrd) | exact (Hrd Hr)].
Qed.
#[using="Type"] Lemma keeps_but_cs : forall L regs regs', keeps_cs regs regs' -> keeps_but L regs regs'.
Proof. intros L regs regs' K r Hr _. apply K, Hr. Qed.
Ltac solve_keeps_but :=
  repeat (apply keeps_but_upd; [| first [left; cbv; tauto | right; not_kept] ]);
  first [apply keeps_but_refl | assumption | apply keeps_but_cs; assumption].
(* [comment removed for export] *)
#[using="Type"] Lemma v_lb_k : forall k, (0 <= k <= 7)%Z -> v_lb (Z_to_bv 8 k) = Z_to_bv 64 k.
Proof.
  intros k Hk7. unfold v_lb. f_equal. rewrite Z_to_bv_signed. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 8) with 128%Z. change (bv_modulus 8) with 256%Z. rewrite Z.mod_small; lia.
Qed.
#[using="Type"] Lemma signed64_small : forall z, (0 <= z < 2 ^ 63)%Z -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite Z_to_bv_signed. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 64) with (2 ^ 63)%Z. change (bv_modulus 64) with (2 ^ 64)%Z. rewrite Z.mod_small; lia.
Qed.
#[using="Type"] Lemma land7_mod8 : forall a, Z.land a 7 = (a mod 8)%Z.
Proof. intros a. change 7%Z with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

#[local] Definition RIPL : list reg := [1; 2; 8; 9; 18; 19; 20; 21]%bv.

Section RIP.
  Variable mem0 : word -> option byte.
  Variable rom : word -> option byte.
  Variables sp ra : word.
  Variables p n s : Z.
  Hypothesis Hs_def : bv_unsigned sp = s.
  Hypothesis Hn : (0 < n <= 2 ^ 40)%Z.                                 (* [comment removed for export] *)
  Hypothesis Happ : (0 <= p /\ p + n + 8 <= LOWEND)%Z \/ (HIGHBEG <= p /\ p + n + 8 <= HIGHEND)%Z.   (* [comment removed for export] *)
  Hypothesis Hs : (0x1000000 <= s - 72)%Z /\ (s < 2 ^ 64)%Z.           (* [comment removed for export] *)
  Hypothesis Hshs : (SB + (p + n - 1) / 8 < s - 72)%Z.                  (* [comment removed for export] *)
  Hypothesis Hok : store_ok ASEGS mem0 (Z_to_bv 64 (s - 72)) 72%nat = true.
  Hypothesis Hret : ret_ok ra.
  Hypothesis HG : rt_layout_globs mem0.
  (* [comment removed for export] *)
  Variable kL : Z.
  Hypothesis HZ : forall x : word, (SB + p / 8 <= bv_unsigned x < SB + (p + n - 1) / 8)%Z -> mem0 x = Some (Z_to_bv 8 0).
  Hypothesis HL : mem0 (Z_to_bv 64 (SB + (p + n - 1) / 8)) = Some (Z_to_bv 8 kL).
  Hypothesis HkL : kL = 0%Z \/ ((p + n - 1) mod 8 < kL <= 7)%Z.

  #[local] Notation A k := (Z_to_bv 64 (s - k)) (only parsing).
  #[local] Notation W M k v := (wbytes M (Z_to_bv 64 (s - k)) (word_to_le_bytes 8 v)) (only parsing).

  #[using="Hs_def"] Lemma sp_s : sp = Z_to_bv 64 s.  Proof. rewrite <- Hs_def. symmetry. apply Z_to_bv_bv_unsigned. Qed.
  #[using="Hn Happ"] Lemma p_facts : (0 <= p)%Z /\ (p + n <= HIGHEND)%Z /\ (0 <= p / 8)%Z /\ (p / 8 <= (p + n - 1) / 8)%Z /\ ((p + n - 1) / 8 <= HIGHEND)%Z.
  Proof.
    unfold LOWEND, HIGHBEG, HIGHEND in *. destruct Happ as [[H1 H2]|[H1 H2]];
    (repeat split; [lia | lia | apply Z.div_pos; lia | apply Z.div_le_mono; lia | apply Z.div_le_upper_bound; lia]).
  Qed.

  (* [comment removed for export] *)
  Definition frame_only (M : word -> option byte) : Prop :=
    forall x : word, (bv_unsigned x < s - 72 \/ s <= bv_unsigned x)%Z -> M x = mem0 x.
  #[using="Type"] Lemma frame_only_refl : frame_only mem0.  Proof. intros x _. reflexivity. Qed.
  #[using="p n Hn Hs"] Lemma frame_only_w : forall M k v, frame_only M -> (8 <= k <= 72)%Z -> frame_only (W M k v).
  Proof.
    intros M k v HF Hk x Hx. pose proof (u64_range x).
    destruct Hx as [Hx|Hx].
    - rewrite wbytes_below; [apply HF; lia | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia | unorm; lia].
    - rewrite wbytes_above; [apply HF; lia | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia].
  Qed.
  #[using="p n Hs HG"] Lemma frame_only_globs : forall M, frame_only M -> rt_layout_globs M.
  Proof.
    intros M HF. destruct HG as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
    assert (EQ : forall (a : word) k, (bv_unsigned a + Z.of_nat k <= 0x1000000)%Z -> rdn ASEGS M a k = rdn ASEGS mem0 a k).
    { intros a k Ha. apply rdn_ext; [lia|]. intros x Hx. apply HF. lia. }
    unfold rt_layout_globs. rewrite !EQ by (cbn [Z.of_nat Pos.to_nat]; imm_norm; lia). repeat split; assumption.
  Qed.
  #[using="Hshs HZ"] Lemma frame_only_zero : forall M (x : word), frame_only M ->
    (SB + p / 8 <= bv_unsigned x < SB + (p + n - 1) / 8)%Z -> M x = Some (Z_to_bv 8 0).
  Proof. intros M x HF Hx. rewrite HF by lia. apply HZ. exact Hx. Qed.
  #[using="Hn Happ Hshs HL"] Lemma frame_only_last : forall M, frame_only M -> M (Z_to_bv 64 (SB + (p + n - 1) / 8)) = Some (Z_to_bv 8 kL).
  Proof.
    intros M HF. pose proof p_facts as (Pp & Ppn & Pp8 & Pmono & Phi). unfold SB, HIGHEND in *.
    rewrite HF by (unorm; lia). exact HL.
  Qed.
  #[using="p n Hn Hs Hok"] Lemma frame_only_store_ok : forall M k (j : nat), mem_grows mem0 M -> (Z.of_nat j <= k <= 72)%Z ->
    store_ok ASEGS M (Z_to_bv 64 (s - k)) j = true.
  Proof.
    intros M k j HGr Hk. apply (store_ok_mono _ _ mem0 M _ HGr).
    apply (store_ok_sub ASEGS mem0 (Z_to_bv 64 (s - 72)) _ 72%nat); [unorm; cbn [Z.of_nat Pos.to_nat]; lia | exact Hok | unorm; lia | unorm; cbn [Z.of_nat Pos.to_nat]; lia].
  Qed.

  #[local] Ltac grows := first [apply mem_grows_refl | eapply mem_grows_trans; [ | apply wbytes_grows ]; grows].
  #[local] Ltac fsok := apply frame_only_store_ok; [grows | cbn [Z.of_nat Pos.to_nat]; lia].
  #[local] Ltac fonly := repeat (apply frame_only_w; [|lia]); apply frame_only_refl.

  (* [comment removed for export] *)
  Definition M7 (rg : bvmap 5 word) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem0
      (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ra))
      (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr rg 8)))
      (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr rg 9)))
      (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (getr rg 18)))
      (Z_to_bv 64 (s - 40)) (word_to_le_bytes 8 (getr rg 19)))
      (Z_to_bv 64 (s - 48)) (word_to_le_bytes 8 (getr rg 20)))
      (Z_to_bv 64 (s - 56)) (word_to_le_bytes 8 (getr rg 21)).
  #[using="p n Hn Hs"] Lemma M7_frame_only : forall rg, frame_only (M7 rg).  Proof. intros rg. unfold M7. fonly. Qed.

  Definition c1_post (regs rg : bvmap 5 word) : Prop :=
    getr rg 9 = Z_to_bv 64 n /\ getr rg 8 = Z_to_bv 64 p /\ getr rg 21 = Z_to_bv 64 0x13fc38 /\ getr rg 11 = Z_to_bv 64 SB
    /\ getr rg 12 = Z_to_bv 64 LOWEND /\ getr rg 2 = Z_to_bv 64 (s - 64) /\ getr rg 1 = ra.

  (* [comment removed for export] *)
  #[using="Hs_def Hn Happ Hs Hok HG kL HkL"] Lemma c1_run : forall regs,
    getr regs 10 = Z_to_bv 64 p -> getr regs 11 = Z_to_bv 64 n -> getr regs 2 = sp -> getr regs 1 = ra ->
    exists regs',
      msteps ASEGS (mkst regs (0x7b4c0 : word) mem0 rom) (mkst regs' (0x7b508 : word) (M7 regs) rom)
      /\ c1_post regs regs' /\ keeps_but RIPL regs regs'.
  Proof.
    intros regs H10 H11 H2 H1. rewrite sp_s in H2. pose proof p_facts as (Pp & Ppn & Pp8 & Pmono & Phi). unfold HIGHEND in *.
    pose proof (frame_only_globs (M7 regs) (M7_frame_only regs)) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
    unfold M7 in *.
    eexists. split.
    - stepiv F_7b0a8 D_7b0a8 (Z_to_bv 64 (s - 64)) ltac:(wval).                       (* [comment removed for export] *)
      stepsd F_7b0ac D_7b0ac (Z_to_bv 64 (s - 8)) ra ltac:(fsok).                        (* [comment removed for export] *)
      stepsd F_7b0b0 D_7b0b0 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(fsok).             (* [comment removed for export] *)
      stepsd F_7b0b4 D_7b0b4 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(fsok).             (* [comment removed for export] *)
      stepsd F_7b0b8 D_7b0b8 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(fsok).            (* [comment removed for export] *)
      stepsd F_7b0bc D_7b0bc (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(fsok).            (* [comment removed for export] *)
      stepsd F_7b0c0 D_7b0c0 (Z_to_bv 64 (s - 48)) (getr regs 20) ltac:(fsok).            (* [comment removed for export] *)
      stepsd F_7b0c4 D_7b0c4 (Z_to_bv 64 (s - 56)) (getr regs 21) ltac:(fsok).            (* [comment removed for export] *)
      stepb_ft F_7b0c8 D_7b0c8 ltac:(cond).                                                (* [comment removed for export] *)
      stepiv F_7b0cc D_7b0cc (Z_to_bv 64 n) ltac:(wval).                                  (* [comment removed for export] *)
      stepiv F_7b0d0 D_7b0d0 (Z_to_bv 64 p) ltac:(wval).                                  (* [comment removed for export] *)
      stepn F_7b0d4 D_7b0d4.                                                               (* [comment removed for export] *)
      mld F_7b0d8 D_7b0d8 (0x1374c0 : word) G1.                                             (* [comment removed for export] *)
      mld F_7b0dc D_7b0dc (0x13fc38 : word) G2.                                             (* [comment removed for export] *)
      stepn F_7b0e0 D_7b0e0.                                                               (* [comment removed for export] *)
      stepn F_7b0e4 D_7b0e4.                                                               (* [comment removed for export] *)
      stepn F_7b0e8 D_7b0e8.                                                               (* [comment removed for export] *)
      stepn F_7b0ec D_7b0ec.                                                               (* [comment removed for export] *)
      apply mst_refl.
    - unfold c1_post, SB, LOWEND. split; [repeat split; gres; rwH; try reflexivity | solve_keeps_but].
  Qed.

  Definition c2_post (rg : bvmap 5 word) : Prop :=
    getr rg 18 = Z_to_bv 64 (p + n) /\ getr rg 9 = Z_to_bv 64 n /\ getr rg 8 = Z_to_bv 64 p /\ getr rg 21 = Z_to_bv 64 0x13fc38
    /\ getr rg 11 = Z_to_bv 64 SB /\ getr rg 2 = Z_to_bv 64 (s - 64) /\ getr rg 1 = ra.

  (* [comment removed for export] *)
  #[using="sp Hn Happ Hs HG kL HkL"] Lemma c2_run : forall regs0 regs,
    c1_post regs0 regs ->
    exists regs',
      msteps ASEGS (mkst regs (0x7b508 : word) (M7 regs0) rom) (mkst regs' (0x7b594 : word) (M7 regs0) rom)
      /\ c2_post regs' /\ keeps_but RIPL regs regs'.
  Proof.
    intros regs0 regs (H9 & H8 & H21 & H11 & H12 & H2 & H1).
    pose proof p_facts as (Pp & Ppn & Pp8 & Pmono & Phi).
    pose proof (frame_only_globs (M7 regs0) (M7_frame_only regs0)) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
    unfold SB, LOWEND, HIGHBEG, HIGHEND in *.
    destruct Happ as [[Hl1 Hl2]|[Hh1 Hh2]].
    - eexists. split.
      + stepb_tk F_7b0f0 D_7b0f0 ltac:(cond).                                  (* [comment removed for export] *)
        stepiv F_7b134 D_7b134 (Z_to_bv 64 (p + n)) ltac:(wval).               (* [comment removed for export] *)
        stepb_tk F_7b138 D_7b138 ltac:(cond).                                  (* [comment removed for export] *)
        apply mst_refl.
      + unfold c2_post, SB. split; [repeat split; gres; rwH; reflexivity | solve_keeps_but].
    - eexists. split.
      + stepb_ft F_7b0f0 D_7b0f0 ltac:(cond).
        stepn F_7b0f4 D_7b0f4.  mld F_7b0f8 D_7b0f8 (0x1374c8 : word) G3.
        stepn F_7b0fc D_7b0fc.  mld F_7b100 D_7b100 (0x1374d0 : word) G5.
        mld F_7b104 D_7b104 (0x140928 : word) G4.  mld F_7b108 D_7b108 (0x140930 : word) G6.
        stepn F_7b10c D_7b10c.                                                 (* [comment removed for export] *)
        stepb_tk F_7b110 D_7b110 ltac:(cond).                                  (* [comment removed for export] *)
        stepn F_7b118 D_7b118.  mld F_7b11c D_7b11c (0x1374d8 : word) G7.  mld F_7b120 D_7b120 (0x140920 : word) G8.
        stepn F_7b124 D_7b124.  stepn F_7b128 D_7b128.                         (* [comment removed for export] *)
        stepb_ft F_7b12c D_7b12c ltac:(cond).                                  (* [comment removed for export] *)
        stepb_ft F_7b130 D_7b130 ltac:(cond).                                  (* [comment removed for export] *)
        stepiv F_7b134 D_7b134 (Z_to_bv 64 (p + n)) ltac:(wval).               (* [comment removed for export] *)
        stepb_ft F_7b138 D_7b138 ltac:(cond).                                  (* [comment removed for export] *)
        stepn F_7b13c D_7b13c.  mld F_7b140 D_7b140 (0x1374c8 : word) G3.
        stepn F_7b144 D_7b144.  mld F_7b148 D_7b148 (0x1374d0 : word) G5.
        mld F_7b14c D_7b14c (0x140928 : word) G4.  mld F_7b150 D_7b150 (0x140930 : word) G6.
        stepn F_7b154 D_7b154.                                                 (* [comment removed for export] *)
        stepb_tk F_7b158 D_7b158 ltac:(cond).                                  (* [comment removed for export] *)
        stepn F_7b160 D_7b160.  mld F_7b164 D_7b164 (0x1374d8 : word) G7.  mld F_7b168 D_7b168 (0x140920 : word) G8.
        stepn F_7b16c D_7b16c.  stepn F_7b170 D_7b170.                         (* [comment removed for export] *)
        stepb_ft F_7b174 D_7b174 ltac:(cond).                                  (* [comment removed for export] *)
        stepb_ft F_7b178 D_7b178 ltac:(cond).                                  (* [comment removed for export] *)
        apply mst_refl.
      + unfold c2_post, SB. split; [repeat split; gres; rwH; reflexivity | solve_keeps_but].
  Qed.

  #[local] Notation AB := (p + 7 - (p + 7) mod 8)%Z (only parsing).      (* [comment removed for export] *)
  #[local] Notation AE := (p + n - (p + n) mod 8)%Z (only parsing).      (* [comment removed for export] *)

  Definition c3_post (rg : bvmap 5 word) : Prop :=
    getr rg 19 = Z_to_bv 64 ((p + 7 - (p + 7) mod 8) / 8 + SB) /\ getr rg 10 = Z_to_bv 64 ((p + n - (p + n) mod 8) / 8 + SB)
    /\ getr rg 20 = Z_to_bv 64 (p + n - (p + n) mod 8)
    /\ getr rg 18 = Z_to_bv 64 (p + n) /\ getr rg 9 = Z_to_bv 64 n /\ getr rg 8 = Z_to_bv 64 p /\ getr rg 21 = Z_to_bv 64 0x13fc38
    /\ getr rg 2 = Z_to_bv 64 (s - 64).

  #[using="Type"] Lemma ret_ok_lit1 : ret_ok (0x7b5a8 : word).  Proof. unfold ret_ok. apply bv_eq. vm_compute. reflexivity. Qed.
  #[using="Type"] Lemma ret_ok_lit2 : ret_ok (0x7b5b4 : word).  Proof. unfold ret_ok. apply bv_eq. vm_compute. reflexivity. Qed.

  (* [comment removed for export] *)
  #[using="sp Hn Happ Hs HG kL HkL"] Lemma c3_run : forall regs0 regs,
    c2_post regs ->
    exists regs',
      msteps ASEGS (mkst regs (0x7b594 : word) (M7 regs0) rom) (mkst regs' (0x7b5b4 : word) (M7 regs0) rom)
      /\ c3_post regs' /\ keeps_but RIPL regs regs'.
  Proof.
    intros regs0 regs (H18 & H9 & H8 & H21 & H11 & H2 & H1).
    pose proof p_facts as (Pp & Ppn & Pp8 & Pmono & Phi).
    pose proof (frame_only_globs (M7 regs0) (M7_frame_only regs0)) as HGM.
    pose proof (Z.mod_pos_bound (p + 7) 8 ltac:(lia)) as Hm1. pose proof (Z.mod_pos_bound (p + n) 8 ltac:(lia)) as Hm2.
    pose proof (Z.mod_le (p + n) 8 ltac:(lia) ltac:(lia)) as Hm3. pose proof (Z.mod_le (p + 7) 8 ltac:(lia) ltac:(lia)) as Hm4.
    assert (Hab_app : in_app AB) by (unfold in_app, LOWEND, HIGHBEG, HIGHEND in *; destruct Happ as [[? ?]|[? ?]]; [left|right]; lia).
    assert (Hae_app : in_app AE).
    { unfold in_app, LOWEND, HIGHBEG, HIGHEND in *. destruct Happ as [[? ?]|[? ?]]; [left; lia|right].
      pose proof (Z.div_mod (p + n) 8 ltac:(lia)) as Hdm. set (q := ((p + n) / 8)%Z) in *. assert (2199291686912 <= q)%Z by lia. lia. }
    unfold SB, LOWEND, HIGHBEG, HIGHEND in *.
    assert (HAB8 : (0 <= AB / 8 <= 17592186044416)%Z) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
    assert (HAE8 : (0 <= AE / 8 <= 17592186044416)%Z) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
    (* [comment removed for export] *)
    eapply (runs_trans ASEGS _ (fun rg => mkst rg (0x7b034 : word) (M7 regs0) rom)
             (fun rg => getr rg 10 = Z_to_bv 64 AB /\ getr rg 1 = (0x7b5a8 : word) /\ getr rg 20 = Z_to_bv 64 AE
                        /\ getr rg 18 = Z_to_bv 64 (p + n) /\ getr rg 9 = Z_to_bv 64 n /\ getr rg 8 = Z_to_bv 64 p
                        /\ getr rg 21 = Z_to_bv 64 0x13fc38 /\ getr rg 2 = Z_to_bv 64 (s - 64) /\ keeps_but RIPL regs rg)).
    { eexists. split.
      - stepb_ft F_7b17c D_7b17c ltac:(cond).                                   (* [comment removed for export] *)
        stepiv F_7b180 D_7b180 (Z_to_bv 64 (p + 7)) ltac:(wval).                (* [comment removed for export] *)
        stepiv F_7b184 D_7b184 (Z_to_bv 64 AB)
          ltac:(gres; unfold v_andi; imm_norm; replace (bv_wrap 64 (-8)) with (2 ^ 64 - 8)%Z by reflexivity; unorm; rewrite land_down8 by lia; reflexivity).
        stepiv F_7b188 D_7b188 (Z_to_bv 64 AE)
          ltac:(gres; rwH; unfold v_andi; imm_norm; replace (bv_wrap 64 (-8)) with (2 ^ 64 - 8)%Z by reflexivity; unorm; rewrite land_down8 by lia; reflexivity).
        stepn F_7b18c D_7b18c.                                                  (* [comment removed for export] *)
        apply mst_refl.
      - repeat split; gres; rwH; try reflexivity; try (apply bv_eq; reflexivity). solve_keeps_but. }
    cbv beta. intros r1 (R10 & R1 & R20 & R18 & R9 & R8 & R21 & R2 & K1).
    destruct (memtoshadow_run r1 (M7 regs0) rom (0x7b5a8 : word) AB HGM Hab_app R10 R1 ret_ok_lit1) as (r2 & RUN2 & Q10 & K2). unfold SB in Q10.
    (* [comment removed for export] *)
    eapply (runs_trans ASEGS _ (fun rg => mkst rg (0x7b034 : word) (M7 regs0) rom)
             (fun rg => getr rg 10 = Z_to_bv 64 AE /\ getr rg 1 = (0x7b5b4 : word) /\ getr rg 19 = Z_to_bv 64 (AB / 8 + 2147450880)
                        /\ getr rg 20 = Z_to_bv 64 AE /\ getr rg 18 = Z_to_bv 64 (p + n) /\ getr rg 9 = Z_to_bv 64 n /\ getr rg 8 = Z_to_bv 64 p
                        /\ getr rg 21 = Z_to_bv 64 0x13fc38 /\ getr rg 2 = Z_to_bv 64 (s - 64) /\ keeps_but RIPL regs rg)).
    { assert (S20 : getr r2 20 = Z_to_bv 64 AE) by (rewrite (K2 20%bv) by (cbv; tauto); exact R20).
      eexists. split.
      - eapply msteps_trans; [exact RUN2|].
        stepiv F_7b190 D_7b190 (Z_to_bv 64 (AB / 8 + 2147450880)) ltac:(gres; rewrite Q10; unfold v_addi; imm_norm; unorm; f_equal; lia).  (* [comment removed for export] *)
        stepiv F_7b194 D_7b194 (Z_to_bv 64 AE) ltac:(gres; rewrite S20; unfold v_addi; imm_norm; unorm; f_equal; lia).                    (* [comment removed for export] *)
        stepn F_7b198 D_7b198.                                                  (* [comment removed for export] *)
        apply mst_refl.
      - repeat split; gres; try reflexivity; try (apply bv_eq; reflexivity);
          try (rewrite (K2 _) by (cbv; tauto); assumption).
        eapply keeps_but_trans; [exact K1|]. solve_keeps_but. }
    cbv beta. intros r3 (T10 & T1 & T19 & T20 & T18 & T9 & T8 & T21 & T2 & K3).
    destruct (memtoshadow_run r3 (M7 regs0) rom (0x7b5b4 : word) AE HGM Hae_app T10 T1 ret_ok_lit2) as (r4 & RUN4 & U10 & K4). unfold SB in U10.
    exists r4. split; [exact RUN4|]. split.
    - unfold c3_post, SB. repeat split; try (rewrite (K4 _) by (cbv; tauto); assumption). exact U10.
    - eapply keeps_but_trans; [exact K3|]. apply keeps_but_cs. exact K4.
  Qed.

  (* [comment removed for export] *)
  #[using="Hn Happ Hs Hshs HZ"] Lemma rdn1_M7 : forall regs0 z, (SB + p / 8 <= z < SB + (p + n - 1) / 8)%Z ->
    rdn ASEGS (M7 regs0) (Z_to_bv 64 z) 1%nat = Some [Z_to_bv 8 0].
  Proof.
    intros regs0 z Hz. pose proof p_facts as (Pp & Ppn & Pp8 & Pmono & Phi). unfold SB, HIGHEND in *.
    cbn [rdn]. rewrite (frame_only_zero (M7 regs0) (Z_to_bv 64 z) (M7_frame_only regs0)) by (unfold SB; unorm; lia). reflexivity.
  Qed.
  #[using="Hn Happ Hs Hshs HL"] Lemma rdn1_M7_last : forall regs0 z, (z = SB + (p + n - 1) / 8)%Z ->
    rdn ASEGS (M7 regs0) (Z_to_bv 64 z) 1%nat = Some [Z_to_bv 8 kL].
  Proof.
    intros regs0 z ->. cbn [rdn]. rewrite (frame_only_last (M7 regs0) (M7_frame_only regs0)). reflexivity.
  Qed.
  #[local] Ltac maddr z := match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 z) by (symmetry; wval) end.
  #[local] Ltac mlb0 F D z :=
    chain_step; [reflexivity
      | eapply step_lb; [exact F | reflexivity | exact D | maddr z; apply rdn1_M7; unfold SB; lia]
      | step_simpl; vnorm].
  (* [comment removed for export] *)
  #[local] Ltac mlbk F D z :=
    chain_step; [reflexivity
      | eapply step_lb; [exact F | reflexivity | exact D | maddr z; apply rdn1_M7_last; unfold SB; lia]
      | step_simpl; vnorm; rewrite (v_lb_k kL ltac:(lia))].

  Definition c4_post (rg : bvmap 5 word) : Prop :=
    getr rg 19 = Z_to_bv 64 ((p + 7 - (p + 7) mod 8) / 8 + SB) /\ getr rg 10 = Z_to_bv 64 ((p + n - (p + n) mod 8) / 8 + SB)
    /\ getr rg 2 = Z_to_bv 64 (s - 64).

  (* [comment removed for export] *)
  #[local] Ltac conds :=
    rwH; unfold c_lts, bv_lts, v_andi; imm_norm; unorm; rewrite ?land7_mod8; unorm; rewrite !signed64_small by lia;
    first [apply Z.ltb_lt | apply Z.ltb_ge]; lia.
  #[using="sp Hn Happ Hs Hshs HG kL HZ HL HkL"] Lemma c4_run : forall regs0 regs,
    c3_post regs ->
    exists regs',
      msteps ASEGS (mkst regs (0x7b5b4 : word) (M7 regs0) rom) (mkst regs' (0x7b624 : word) (M7 regs0) rom)
      /\ c4_post regs' /\ keeps_but RIPL regs regs'.
  Proof.
    intros regs0 regs (H19 & H10 & H20 & H18 & H9 & H8 & H21 & H2).
    pose proof p_facts as (Pp & Ppn & Pp8 & Pmono & Phi).
    pose proof (frame_only_globs (M7 regs0) (M7_frame_only regs0)) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
    pose proof (Z.div_mod p 8 ltac:(lia)) as Dp. pose proof (Z.mod_pos_bound p 8 ltac:(lia)) as Mp.
    pose proof (Z.div_mod (p + n - 1) 8 ltac:(lia)) as Dq. pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(lia)) as Mq.
    unfold SB, LOWEND, HIGHBEG, HIGHEND in *.
    destruct (Z.lt_ge_cases (p / 8) ((p + n - 1) / 8)) as [Hlt|Hge].
    - (* [comment removed for export] *)
      destruct HkL as [Hk0|Hk7].
      + eexists. split.
        * mld F_7b19c D_7b19c (0x13fc38 : word) G2.                                       (* [comment removed for export] *)
          stepiv F_7b1a0 D_7b1a0 (Z_to_bv 64 (p / 8)) ltac:(wval).                        (* [comment removed for export] *)
          stepiv F_7b1a4 D_7b1a4 (Z_to_bv 64 (2147450880 + p / 8)) ltac:(wval).           (* [comment removed for export] *)
          mlb0 F_7b1a8 D_7b1a8 (2147450880 + p / 8)%Z.                                    (* [comment removed for export] *)
          stepb_tk F_7b1ac D_7b1ac ltac:(cond).                                           (* [comment removed for export] *)
          stepiv F_7b1b8 D_7b1b8 (Z_to_bv 64 (p + n - 1)) ltac:(wval).                    (* [comment removed for export] *)
          stepiv F_7b1bc D_7b1bc (Z_to_bv 64 ((p + n - 1) / 8)) ltac:(wval).              (* [comment removed for export] *)
          stepiv F_7b1c0 D_7b1c0 (Z_to_bv 64 (2147450880 + (p + n - 1) / 8)) ltac:(wval). (* [comment removed for export] *)
          mlbk F_7b1c4 D_7b1c4 (2147450880 + (p + n - 1) / 8)%Z.                          (* [comment removed for export] *)
          stepb_tk F_7b1c8 D_7b1c8 ltac:(cond).                                           (* [comment removed for export] *)
          apply mst_refl.
        * unfold c4_post, SB. split; [repeat split; gres; rwH; reflexivity | solve_keeps_but].
      + eexists. split.
        * mld F_7b19c D_7b19c (0x13fc38 : word) G2.
          stepiv F_7b1a0 D_7b1a0 (Z_to_bv 64 (p / 8)) ltac:(wval).
          stepiv F_7b1a4 D_7b1a4 (Z_to_bv 64 (2147450880 + p / 8)) ltac:(wval).
          mlb0 F_7b1a8 D_7b1a8 (2147450880 + p / 8)%Z.
          stepb_tk F_7b1ac D_7b1ac ltac:(cond).
          stepiv F_7b1b8 D_7b1b8 (Z_to_bv 64 (p + n - 1)) ltac:(wval).
          stepiv F_7b1bc D_7b1bc (Z_to_bv 64 ((p + n - 1) / 8)) ltac:(wval).
          stepiv F_7b1c0 D_7b1c0 (Z_to_bv 64 (2147450880 + (p + n - 1) / 8)) ltac:(wval).
          mlbk F_7b1c4 D_7b1c4 (2147450880 + (p + n - 1) / 8)%Z.                          (* [comment removed for export] *)
          stepb_ft F_7b1c8 D_7b1c8 ltac:(cond).                                           (* [comment removed for export] *)
          stepn F_7b1cc D_7b1cc.                                                          (* [comment removed for export] *)
          stepb_tk F_7b1d0 D_7b1d0 ltac:(conds).                                          (* [comment removed for export] *)
          apply mst_refl.
        * unfold c4_post, SB. split; [repeat split; gres; rwH; reflexivity | solve_keeps_but].
    - (* [comment removed for export] *)
      assert (Heq : (p / 8 = (p + n - 1) / 8)%Z) by lia.
      destruct HkL as [Hk0|Hk7].
      + eexists. split.
        * mld F_7b19c D_7b19c (0x13fc38 : word) G2.
          stepiv F_7b1a0 D_7b1a0 (Z_to_bv 64 (p / 8)) ltac:(wval).
          stepiv F_7b1a4 D_7b1a4 (Z_to_bv 64 (2147450880 + (p + n - 1) / 8)) ltac:(wval).
          mlbk F_7b1a8 D_7b1a8 (2147450880 + (p + n - 1) / 8)%Z.                          (* [comment removed for export] *)
          stepb_tk F_7b1ac D_7b1ac ltac:(cond).
          stepiv F_7b1b8 D_7b1b8 (Z_to_bv 64 (p + n - 1)) ltac:(wval).
          stepiv F_7b1bc D_7b1bc (Z_to_bv 64 ((p + n - 1) / 8)) ltac:(wval).
          stepiv F_7b1c0 D_7b1c0 (Z_to_bv 64 (2147450880 + (p + n - 1) / 8)) ltac:(wval).
          mlbk F_7b1c4 D_7b1c4 (2147450880 + (p + n - 1) / 8)%Z.
          stepb_tk F_7b1c8 D_7b1c8 ltac:(cond).
          apply mst_refl.
        * unfold c4_post, SB. split; [repeat split; gres; rwH; try reflexivity; f_equal; lia | solve_keeps_but].
      + eexists. split.
        * mld F_7b19c D_7b19c (0x13fc38 : word) G2.
          stepiv F_7b1a0 D_7b1a0 (Z_to_bv 64 (p / 8)) ltac:(wval).
          stepiv F_7b1a4 D_7b1a4 (Z_to_bv 64 (2147450880 + (p + n - 1) / 8)) ltac:(wval).
          mlbk F_7b1a8 D_7b1a8 (2147450880 + (p + n - 1) / 8)%Z.                          (* [comment removed for export] *)
          stepb_ft F_7b1ac D_7b1ac ltac:(cond).
          stepn F_7b1b0 D_7b1b0.                                                          (* [comment removed for export] *)
          stepb_ft F_7b1b4 D_7b1b4 ltac:(conds).                                          (* [comment removed for export] *)
          stepiv F_7b1b8 D_7b1b8 (Z_to_bv 64 (p + n - 1)) ltac:(wval).
          stepiv F_7b1bc D_7b1bc (Z_to_bv 64 ((p + n - 1) / 8)) ltac:(wval).
          stepiv F_7b1c0 D_7b1c0 (Z_to_bv 64 (2147450880 + (p + n - 1) / 8)) ltac:(wval).
          mlbk F_7b1c4 D_7b1c4 (2147450880 + (p + n - 1) / 8)%Z.
          stepb_ft F_7b1c8 D_7b1c8 ltac:(cond).
          stepn F_7b1cc D_7b1cc.
          stepb_tk F_7b1d0 D_7b1d0 ltac:(conds).
          apply mst_refl.
        * unfold c4_post, SB. split; [repeat split; gres; rwH; try reflexivity; f_equal; lia | solve_keeps_but].
  Qed.

  (* [comment removed for export] *)
  Definition reload_ok (regs0 : bvmap 5 word) (M : word -> option byte) : Prop :=
    frame_only M /\
    rdn ASEGS M (Z_to_bv 64 (s - 8)) 8%nat = Some (word_to_le_bytes 8 ra) /\
    rdn ASEGS M (Z_to_bv 64 (s - 16)) 8%nat = Some (word_to_le_bytes 8 (getr regs0 8)) /\
    rdn ASEGS M (Z_to_bv 64 (s - 24)) 8%nat = Some (word_to_le_bytes 8 (getr regs0 9)) /\
    rdn ASEGS M (Z_to_bv 64 (s - 32)) 8%nat = Some (word_to_le_bytes 8 (getr regs0 18)) /\
    rdn ASEGS M (Z_to_bv 64 (s - 40)) 8%nat = Some (word_to_le_bytes 8 (getr regs0 19)) /\
    rdn ASEGS M (Z_to_bv 64 (s - 48)) 8%nat = Some (word_to_le_bytes 8 (getr regs0 20)) /\
    rdn ASEGS M (Z_to_bv 64 (s - 56)) 8%nat = Some (word_to_le_bytes 8 (getr regs0 21)).

  #[local] Ltac peel :=
    rewrite rdn_wbytes_out;
      [ | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia | cbn [Z.of_nat Pos.to_nat]; unorm; lia
        | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia ].
  #[local] Ltac slot := repeat peel; apply rdn_wbytes_hit8; unorm; lia.

  #[using="p n Hn Hs"] Lemma M7_reload : forall regs0, reload_ok regs0 (M7 regs0).
  Proof.
    intros regs0. split; [apply M7_frame_only|]. unfold M7. repeat split; slot.
  Qed.
  #[using="p n Hn Hs"] Lemma W72_reload : forall regs0 M v, reload_ok regs0 M ->
    reload_ok regs0 (wbytes M (Z_to_bv 64 (s - 72)) (word_to_le_bytes 8 v)).
  Proof.
    intros regs0 M v (HF & R1 & R2 & R3 & R4 & R5 & R6 & R7). split; [apply frame_only_w; [exact HF | lia]|].
    repeat split; (peel; assumption).
  Qed.

  (* [comment removed for export] *)
  #[using="sp Hn Happ Hs Hshs Hok kL HZ HL HkL"] Lemma c5_run : forall regs0 regs,
    c4_post regs ->
    exists regs' M',
      msteps ASEGS (mkst regs (0x7b624 : word) (M7 regs0) rom) (mkst regs' (0x7b638 : word) M' rom)
      /\ reload_ok regs0 M' /\ getr regs' 2 = Z_to_bv 64 (s - 64) /\ keeps_but RIPL regs regs' /\ mem_grows mem0 M'.
  Proof.
    intros regs0 regs (H19 & H10 & H2).
    pose proof p_facts as (Pp & Ppn & Pp8 & Pmono & Phi).
    pose proof (Z.mod_pos_bound (p + 7) 8 ltac:(lia)) as Hm1. pose proof (Z.mod_pos_bound (p + n) 8 ltac:(lia)) as Hm2.
    pose proof (Z.mod_le (p + n) 8 ltac:(lia) ltac:(lia)) as Hm3. pose proof (Z.mod_le (p + 7) 8 ltac:(lia) ltac:(lia)) as Hm4.
    unfold SB, LOWEND, HIGHBEG, HIGHEND in *.
    assert (HAB8 : (p / 8 <= AB / 8 <= 17592186044416)%Z) by (split; [apply Z.div_le_mono; lia | apply Z.div_le_upper_bound; lia]).
    assert (HAE8 : (0 <= AE / 8 <= (p + n) / 8)%Z) by (split; [apply Z.div_pos; lia | apply Z.div_le_mono; lia]).
    assert (Hpn8 : ((p + n) / 8 <= (p + n - 1) / 8 + 1)%Z).
    { pose proof (Z.div_mod (p + n) 8 ltac:(lia)). pose proof (Z.div_mod (p + n - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(lia)). lia. }
    assert (HAE8' : (AE / 8 - 1 <= (p + n - 1) / 8)%Z).
    { pose proof (Z.div_mod AE 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound AE 8 ltac:(lia)).
      pose proof (Z.div_mod (p + n - 1) 8 ltac:(lia)) as D2. pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(lia)). lia. }
    pose proof (Z.div_mod p 8 ltac:(lia)) as Dp. pose proof (Z.mod_pos_bound p 8 ltac:(lia)) as Mp.
    pose proof (Z.div_mod (p + n) 8 ltac:(lia)) as Dpn.
    set (sb := (2147450880 + AB / 8)%Z) in *. set (se := (2147450880 + AE / 8)%Z) in *.
    assert (E19 : getr regs 19 = Z_to_bv 64 sb) by (rewrite H19; f_equal; lia).
    assert (E10 : getr regs 10 = Z_to_bv 64 se) by (rewrite H10; f_equal; lia).
    destruct (Z.le_gt_cases se sb) as [Hskip|Hgo].
    - exists regs, (M7 regs0). split; [|split; [apply M7_reload | split; [exact H2 | split; [apply keeps_but_refl | unfold M7; grows]]]].
      stepb_tk F_7b20c D_7b20c ltac:(rewrite E19, E10; unfold c_ltu, bv_ltu; unorm; apply Z.ltb_ge; lia).   (* [comment removed for export] *)
      apply mst_refl.
    - (* [comment removed for export] *)
      assert (S1 : exists r1, msteps ASEGS (mkst regs (0x7b624 : word) (M7 regs0) rom) (mkst r1 (0x8b9ac : word) (M7 regs0) rom)
                /\ (getr r1 10 = Z_to_bv 64 sb /\ getr r1 11 = Z_to_bv 64 (se - sb) /\ getr r1 2 = Z_to_bv 64 (s - 64) /\ getr r1 1 = (0x7b634 : word)
                    /\ keeps_but RIPL regs r1)).
      { eexists. split.
        - stepb_ft F_7b20c D_7b20c ltac:(rewrite E19, E10; unfold c_ltu, bv_ltu; unorm; apply Z.ltb_lt; lia).  (* [comment removed for export] *)
          stepiv F_7b210 D_7b210 (Z_to_bv 64 (se - sb)) ltac:(gres; rewrite E19, E10; unfold v_sub; unorm; f_equal; lia).   (* [comment removed for export] *)
          stepiv F_7b214 D_7b214 (Z_to_bv 64 sb) ltac:(gres; rewrite E19; unfold v_addi; imm_norm; unorm; f_equal; lia).       (* [comment removed for export] *)
          stepn F_7b218 D_7b218.                                                                                          (* [comment removed for export] *)
          apply mst_refl.
        - repeat split; gres; rwH; try reflexivity; try (apply bv_eq; reflexivity). solve_keeps_but. }
      destruct S1 as (r1 & RUN1 & Q10 & Q11 & Q2 & Q1 & K1).
      assert (Hret2 : ret_ok (0x7b634 : word)) by (unfold ret_ok; apply bv_eq; vm_compute; reflexivity).
      pose proof (mem_is_zero_run (M7 regs0) (Z_to_bv 64 sb) (Z_to_bv 64 (s - 64)) (0x7b634 : word) (se - sb) sb (s - 64) se
                    (sb + 7 - (sb + 7) mod 8) (se - se mod 8) rom) as MZ.
      specialize (MZ ltac:(unorm; reflexivity) ltac:(unorm; reflexivity) ltac:(lia) eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
      specialize (MZ ltac:(replace (s - 64 - 8)%Z with (s - 72)%Z by lia; apply frame_only_store_ok; [unfold M7; grows | cbn; lia]) Hret2).
      assert (HZI : forall x : word, (sb <= bv_unsigned x < sb + (se - sb))%Z -> M7 regs0 x = Some (Z_to_bv 8 0)).
      { intros x Hx. destruct (Z.lt_ge_cases (bv_unsigned x) (2147450880 + (p + n - 1) / 8)) as [Hxl|Hxh].
        - apply (frame_only_zero (M7 regs0) x (M7_frame_only regs0)). unfold SB. lia.
        - (* [comment removed for export] *)
          assert (Ex : x = Z_to_bv 64 (SB + (p + n - 1) / 8)) by (apply bv_eq; unfold SB; unorm; lia).
          pose proof (Z.div_mod AE 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound AE 8 ltac:(lia)).
          pose proof (Z.div_mod (p + n - 1) 8 ltac:(lia)) as D2. pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(lia)).
          assert (kL = 0)%Z as Hk0 by lia.
          rewrite Ex, (frame_only_last (M7 regs0) (M7_frame_only regs0)), Hk0. reflexivity. }
      specialize (MZ HZI).
      destruct (MZ r1 Q10 Q11 Q2 Q1) as (r2 & RUN2 & V10 & V2 & V1 & K2).
      replace (s - 64 - 8)%Z with (s - 72)%Z in RUN2 by lia.
      eexists. exists (wbytes (M7 regs0) (Z_to_bv 64 (s - 72)) (word_to_le_bytes 8 (0x7b634 : word))). split; [|split; [apply W72_reload, M7_reload|]].
      + eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|].
        stepb_ft F_7b21c D_7b21c ltac:(rewrite V10; unfold c_eq, bv_eqb; unorm; apply Z.eqb_neq; lia).   (* [comment removed for export] *)
        apply mst_refl.
      + split; [gres; exact V2|]. split; [|unfold M7; grows].
        eapply keeps_but_trans; [exact K1|]. apply keeps_but_cs. exact K2.
  Qed.

  (* [comment removed for export] *)
  #[using="p n Hs_def Hn Happ Hs Hret kL HkL"] Lemma c6_run : forall regs0 regs M,
    reload_ok regs0 M -> getr regs 2 = Z_to_bv 64 (s - 64) ->
    exists regs',
      msteps ASEGS (mkst regs (0x7b638 : word) M rom) (mkst regs' ra M rom)
      /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 2 = sp /\ getr regs' 1 = ra
      /\ getr regs' 8 = getr regs0 8 /\ getr regs' 9 = getr regs0 9 /\ getr regs' 18 = getr regs0 18
      /\ getr regs' 19 = getr regs0 19 /\ getr regs' 20 = getr regs0 20 /\ getr regs' 21 = getr regs0 21
      /\ keeps_but RIPL regs regs'.
  Proof.
    intros regs0 regs M (HF & R1 & R2 & R3 & R4 & R5 & R6 & R7) H2.
    eexists. split.
    - stepn F_7b220 D_7b220.                                                       (* [comment removed for export] *)
      stepn F_7b224 D_7b224.                                                       (* [comment removed for export] *)
      stepld F_7b228 D_7b228 ra ltac:(maddr (s - 8)%Z; exact R1).                 (* [comment removed for export] *)
      stepld F_7b22c D_7b22c (getr regs0 8) ltac:(maddr (s - 16)%Z; exact R2).    (* [comment removed for export] *)
      stepld F_7b230 D_7b230 (getr regs0 9) ltac:(maddr (s - 24)%Z; exact R3).    (* [comment removed for export] *)
      stepld F_7b234 D_7b234 (getr regs0 18) ltac:(maddr (s - 32)%Z; exact R4).   (* [comment removed for export] *)
      stepld F_7b238 D_7b238 (getr regs0 19) ltac:(maddr (s - 40)%Z; exact R5).   (* [comment removed for export] *)
      stepld F_7b23c D_7b23c (getr regs0 20) ltac:(maddr (s - 48)%Z; exact R6).   (* [comment removed for export] *)
      stepld F_7b240 D_7b240 (getr regs0 21) ltac:(maddr (s - 56)%Z; exact R7).   (* [comment removed for export] *)
      stepiv F_7b244 D_7b244 (Z_to_bv 64 s) ltac:(wval).                          (* [comment removed for export] *)
      stepret F_7b248 D_7b248 ra ltac:(rwH; reflexivity).
      apply mst_refl.
    - repeat split; gres; try reflexivity; [symmetry; apply sp_s | solve_keeps_but].
  Qed.

  (* [comment removed for export] *)
  #[using="Hs_def Hn Happ Hs Hshs Hok Hret HG kL HZ HL HkL"] Theorem region_is_poisoned_run : forall regs,
    getr regs 10 = Z_to_bv 64 p -> getr regs 11 = Z_to_bv 64 n -> getr regs 2 = sp -> getr regs 1 = ra ->
    exists regs' M',
      msteps ASEGS (mkst regs (0x7b4c0 : word) mem0 rom) (mkst regs' ra M' rom)
      /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 2 = sp /\ getr regs' 1 = ra /\ keeps_cs regs regs'
      /\ frame_only M' /\ mem_grows mem0 M'.
  Proof.
    intros regs H10 H11 H2 H1.
    destruct (c1_run regs H10 H11 H2 H1) as (r1 & RUN1 & P1 & K1).
    destruct (c2_run regs r1 P1) as (r2 & RUN2 & P2 & K2).
    destruct (c3_run regs r2 P2) as (r3 & RUN3 & P3 & K3).
    destruct (c4_run regs r3 P3) as (r4 & RUN4 & P4 & K4).
    destruct (c5_run regs r4 P4) as (r5 & M5 & RUN5 & RL5 & S5 & K5 & G5).
    destruct (c6_run regs r5 M5 RL5 S5) as (r6 & RUN6 & Q10 & Q2 & Q1 & Q8 & Q9 & Q18 & Q19 & Q20 & Q21 & K6).
    exists r6, M5. split.
    - eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3|].
      eapply msteps_trans; [exact RUN4|]. eapply msteps_trans; [exact RUN5|]. exact RUN6.
    - assert (KB : keeps_but RIPL regs r6).
      { eapply keeps_but_trans; [exact K1|]. eapply keeps_but_trans; [exact K2|]. eapply keeps_but_trans; [exact K3|].
        eapply keeps_but_trans; [exact K4|]. eapply keeps_but_trans; [exact K5|]. exact K6. }
      repeat split; try assumption.
      + intros r Hr. destruct (decide (r = 1%bv)) as [->|N1]; [rewrite Q1, H1; reflexivity|].
        destruct (decide (r = 2%bv)) as [->|N2]; [rewrite Q2, H2; reflexivity|].
        destruct (decide (r = 8%bv)) as [->|N8]; [exact Q8|]. destruct (decide (r = 9%bv)) as [->|N9]; [exact Q9|].
        destruct (decide (r = 18%bv)) as [->|N18]; [exact Q18|]. destruct (decide (r = 19%bv)) as [->|N19]; [exact Q19|].
        destruct (decide (r = 20%bv)) as [->|N20]; [exact Q20|]. destruct (decide (r = 21%bv)) as [->|N21]; [exact Q21|].
        apply KB; [exact Hr|]. cbv. intuition congruence.
      + exact (proj1 RL5).
  Qed.
End RIP.
End FPX_1.
