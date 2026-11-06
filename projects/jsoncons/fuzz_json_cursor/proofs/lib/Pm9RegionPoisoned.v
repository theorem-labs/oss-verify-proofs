(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac RefMemcpyLib MemSplit As0StepLib Pm9MemIsZero.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import Pm9_code_82000_83000 .
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.

Definition SB : Z := 0x7fff8000.
Definition LOWEND : Z := 0x7fff7fff.
Definition HIGHBEG : Z := 0x10007fff8000.
Definition HIGHEND : Z := 0x7fffffffffff.

Section FPX_1. Context {fx : PropExec.FPState}.

Definition rt_layout_globs (M : word -> option byte) : Prop :=
  rdn ASEGS M (0x154500 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x15dcf8)) /\
  rdn ASEGS M (0x15dcf8 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 SB)) /\
  rdn ASEGS M (0x154508 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x15e9e8)) /\
  rdn ASEGS M (0x15e9e8 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) /\
  rdn ASEGS M (0x154510 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x15e9f0)) /\
  rdn ASEGS M (0x15e9f0 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) /\
  rdn ASEGS M (0x154518 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x15e9e0)) /\
  rdn ASEGS M (0x15e9e0 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 HIGHEND)).

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

Lemma memtoshadow_run : forall regs (M rom : word -> option byte) (ret : word) (p : Z),
  rt_layout_globs M -> in_app p ->
  getr regs 10 = Z_to_bv 64 p -> getr regs 1 = ret -> ret_ok ret ->
  exists regs',
    msteps ASEGS (mkst regs (0x825d4 : word) M rom) (mkst regs' ret M rom)
    /\ getr regs' 10 = Z_to_bv 64 (p / 8 + SB) /\ keeps_cs regs regs'.
Proof.
  intros regs M rom ret p (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8) Hp H10 H1 Hret.
  unfold in_app, LOWEND, HIGHBEG, HIGHEND in Hp. unfold SB in *.
  pose proof (Z.div_mod p 8 ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound p 8 ltac:(lia)) as Hmd.
  destruct Hp as [Hlow|Hhigh].
  - eexists. split.
    + stepn F_8258c D_8258c.
      mld F_82590 D_82590 (0x154500 : word) G1.
      mld F_82594 D_82594 (0x15dcf8 : word) G2.
      stepn F_82598 D_82598.
      stepn F_8259c D_8259c.
      stepn F_825a0 D_825a0.
      stepn F_825a4 D_825a4.
      stepb_tk F_825a8 D_825a8 ltac:(cond).
      stepiv F_825ec D_825ec (Z_to_bv 64 (p / 8)) ltac:(wval).
      stepiv F_825f0 D_825f0 (Z_to_bv 64 (p / 8 + 0x7fff8000)) ltac:(wval).
      stepret F_825f4 D_825f4 ret ltac:(rwH; reflexivity).
      apply mst_refl.
    + split; [gres; reflexivity | solve_keeps_cs].
  - eexists. split.
    + stepn F_8258c D_8258c.
      mld F_82590 D_82590 (0x154500 : word) G1.
      mld F_82594 D_82594 (0x15dcf8 : word) G2.
      stepn F_82598 D_82598.
      stepn F_8259c D_8259c.
      stepn F_825a0 D_825a0.
      stepn F_825a4 D_825a4.
      stepb_ft F_825a8 D_825a8 ltac:(cond).
      stepn F_825ac D_825ac.
      mld F_825b0 D_825b0 (0x154508 : word) G3.
      stepn F_825b4 D_825b4.
      mld F_825b8 D_825b8 (0x154510 : word) G5.
      mld F_825bc D_825bc (0x15e9e8 : word) G4.
      mld F_825c0 D_825c0 (0x15e9f0 : word) G6.
      stepn F_825c4 D_825c4.
      stepb_tk F_825c8 D_825c8 ltac:(cond).
      stepn F_825d0 D_825d0.
      mld F_825d4 D_825d4 (0x154518 : word) G7.
      mld F_825d8 D_825d8 (0x15e9e0 : word) G8.
      stepn F_825dc D_825dc.
      stepn F_825e0 D_825e0.
      stepb_ft F_825e4 D_825e4 ltac:(cond).
      stepb_ft F_825e8 D_825e8 ltac:(cond).
      stepiv F_825ec D_825ec (Z_to_bv 64 (p / 8)) ltac:(wval).
      stepiv F_825f0 D_825f0 (Z_to_bv 64 (p / 8 + 0x7fff8000)) ltac:(wval).
      stepret F_825f4 D_825f4 ret ltac:(rwH; reflexivity).
      apply mst_refl.
    + split; [gres; reflexivity | solve_keeps_cs].
Qed.

Definition keeps_but (L : list reg) (regs regs' : bvmap 5 word) : Prop :=
  forall r : reg, In r callee_saved -> ~ In r L -> getr regs' r = getr regs r.
Lemma keeps_but_refl : forall L regs, keeps_but L regs regs.  Proof. intros L regs r _ _. reflexivity. Qed.
Lemma keeps_but_trans : forall L r1 r2 r3, keeps_but L r1 r2 -> keeps_but L r2 r3 -> keeps_but L r1 r3.
Proof. intros L r1 r2 r3 A B r Hr HL. rewrite (B r Hr HL). apply A; assumption. Qed.
Lemma keeps_but_upd : forall L regs regs' (rd : reg) v,
  keeps_but L regs regs' -> (In rd L \/ ~ In rd callee_saved) -> keeps_but L regs (regupd regs' rd v).
Proof.
  intros L regs regs' rd v K Hrd r Hr HL. rewrite getr_other; [apply K; assumption|].
  intros ->. destruct Hrd as [Hrd|Hrd]; [exact (HL Hrd) | exact (Hrd Hr)].
Qed.
Lemma keeps_but_cs : forall L regs regs', keeps_cs regs regs' -> keeps_but L regs regs'.
Proof. intros L regs regs' K r Hr _. apply K, Hr. Qed.
Ltac solve_keeps_but :=
  repeat (apply keeps_but_upd; [| first [left; cbv; tauto | right; not_kept] ]);
  first [apply keeps_but_refl | assumption | apply keeps_but_cs; assumption].

Lemma v_lb_k : forall k, (0 <= k <= 7)%Z -> v_lb (Z_to_bv 8 k) = Z_to_bv 64 k.
Proof.
  intros k Hk7. unfold v_lb. f_equal. rewrite Z_to_bv_signed. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 8) with 128%Z. change (bv_modulus 8) with 256%Z. rewrite Z.mod_small; lia.
Qed.
Lemma signed64_small : forall z, (0 <= z < 2 ^ 63)%Z -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite Z_to_bv_signed. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 64) with (2 ^ 63)%Z. change (bv_modulus 64) with (2 ^ 64)%Z. rewrite Z.mod_small; lia.
Qed.
Lemma land7_mod8 : forall a, Z.land a 7 = (a mod 8)%Z.
Proof. intros a. change 7%Z with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

#[local] Definition RIPL : list reg := [1; 2; 8; 9; 18; 19; 20; 21]%bv.

Section RIP.
  Variable mem0 : word -> option byte.
  Variable rom : word -> option byte.
  Variables sp ra : word.
  Variables p n s : Z.
  Hypothesis Hs_def : bv_unsigned sp = s.
  Hypothesis Hn : (0 < n <= 2 ^ 40)%Z.
  Hypothesis Happ : (0 <= p /\ p + n + 8 <= LOWEND)%Z \/ (HIGHBEG <= p /\ p + n + 8 <= HIGHEND)%Z.
  Hypothesis Hs : (0x1000000 <= s - 72)%Z /\ (s < 2 ^ 64)%Z.
  Hypothesis Hshs : (SB + (p + n - 1) / 8 < s - 72)%Z.
  Hypothesis Hok : store_ok ASEGS mem0 (Z_to_bv 64 (s - 72)) 72%nat = true.
  Hypothesis Hret : ret_ok ra.
  Hypothesis HG : rt_layout_globs mem0.

  Variable kL : Z.
  Hypothesis HZ : forall x : word, (SB + p / 8 <= bv_unsigned x < SB + (p + n - 1) / 8)%Z -> mem0 x = Some (Z_to_bv 8 0).
  Hypothesis HL : mem0 (Z_to_bv 64 (SB + (p + n - 1) / 8)) = Some (Z_to_bv 8 kL).
  Hypothesis HkL : kL = 0%Z \/ ((p + n - 1) mod 8 < kL <= 7)%Z.

  #[local] Notation A k := (Z_to_bv 64 (s - k)) (only parsing).
  #[local] Notation W M k v := (wbytes M (Z_to_bv 64 (s - k)) (word_to_le_bytes 8 v)) (only parsing).

  Lemma sp_s : sp = Z_to_bv 64 s.  Proof. rewrite <- Hs_def. symmetry. apply Z_to_bv_bv_unsigned. Qed.
  Lemma p_facts : (0 <= p)%Z /\ (p + n <= HIGHEND)%Z /\ (0 <= p / 8)%Z /\ (p / 8 <= (p + n - 1) / 8)%Z /\ ((p + n - 1) / 8 <= HIGHEND)%Z.
  Proof.
    unfold LOWEND, HIGHBEG, HIGHEND in *. destruct Happ as [[H1 H2]|[H1 H2]];
    (repeat split; [lia | lia | apply Z.div_pos; lia | apply Z.div_le_mono; lia | apply Z.div_le_upper_bound; lia]).
  Qed.

  Definition frame_only (M : word -> option byte) : Prop :=
    forall x : word, (bv_unsigned x < s - 72 \/ s <= bv_unsigned x)%Z -> M x = mem0 x.
  Lemma frame_only_refl : frame_only mem0.  Proof. intros x _. reflexivity. Qed.
  Lemma frame_only_w : forall M k v, frame_only M -> (8 <= k <= 72)%Z -> frame_only (W M k v).
  Proof.
    intros M k v HF Hk x Hx. pose proof (u64_range x).
    destruct Hx as [Hx|Hx].
    - rewrite wbytes_below; [apply HF; lia | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia | unorm; lia].
    - rewrite wbytes_above; [apply HF; lia | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.to_nat]; unorm; lia].
  Qed.
  Lemma frame_only_globs : forall M, frame_only M -> rt_layout_globs M.
  Proof.
    intros M HF. destruct HG as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
    assert (EQ : forall (a : word) k, (bv_unsigned a + Z.of_nat k <= 0x1000000)%Z -> rdn ASEGS M a k = rdn ASEGS mem0 a k).
    { intros a k Ha. apply rdn_ext; [lia|]. intros x Hx. apply HF. lia. }
    unfold rt_layout_globs. rewrite !EQ by (cbn [Z.of_nat Pos.to_nat]; imm_norm; lia). repeat split; assumption.
  Qed.
  Lemma frame_only_zero : forall M (x : word), frame_only M ->
    (SB + p / 8 <= bv_unsigned x < SB + (p + n - 1) / 8)%Z -> M x = Some (Z_to_bv 8 0).
  Proof. intros M x HF Hx. rewrite HF by lia. apply HZ. exact Hx. Qed.
  Lemma frame_only_last : forall M, frame_only M -> M (Z_to_bv 64 (SB + (p + n - 1) / 8)) = Some (Z_to_bv 8 kL).
  Proof.
    intros M HF. pose proof p_facts as (Pp & Ppn & Pp8 & Pmono & Phi). unfold SB, HIGHEND in *.
    rewrite HF by (unorm; lia). exact HL.
  Qed.
  Lemma frame_only_store_ok : forall M k (j : nat), mem_grows mem0 M -> (Z.of_nat j <= k <= 72)%Z ->
    store_ok ASEGS M (Z_to_bv 64 (s - k)) j = true.
  Proof.
    intros M k j HGr Hk. apply (store_ok_mono _ _ mem0 M _ HGr).
    apply (store_ok_sub ASEGS mem0 (Z_to_bv 64 (s - 72)) _ 72%nat); [unorm; cbn [Z.of_nat Pos.to_nat]; lia | exact Hok | unorm; lia | unorm; cbn [Z.of_nat Pos.to_nat]; lia].
  Qed.

  #[local] Ltac grows := first [apply mem_grows_refl | eapply mem_grows_trans; [ | apply wbytes_grows ]; grows].
  #[local] Ltac fsok := apply frame_only_store_ok; [grows | cbn [Z.of_nat Pos.to_nat]; lia].
  #[local] Ltac fonly := repeat (apply frame_only_w; [|lia]); apply frame_only_refl.

  Definition M7 (rg : bvmap 5 word) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem0
      (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ra))
      (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr rg 8)))
      (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr rg 9)))
      (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (getr rg 18)))
      (Z_to_bv 64 (s - 40)) (word_to_le_bytes 8 (getr rg 19)))
      (Z_to_bv 64 (s - 48)) (word_to_le_bytes 8 (getr rg 20)))
      (Z_to_bv 64 (s - 56)) (word_to_le_bytes 8 (getr rg 21)).
  Lemma M7_frame_only : forall rg, frame_only (M7 rg).  Proof. intros rg. unfold M7. fonly. Qed.

  Definition c1_post (regs rg : bvmap 5 word) : Prop :=
    getr rg 9 = Z_to_bv 64 n /\ getr rg 8 = Z_to_bv 64 p /\ getr rg 21 = Z_to_bv 64 0x15dcf8 /\ getr rg 11 = Z_to_bv 64 SB
    /\ getr rg 12 = Z_to_bv 64 LOWEND /\ getr rg 2 = Z_to_bv 64 (s - 64) /\ getr rg 1 = ra.

  Lemma c1_run : forall regs,
    getr regs 10 = Z_to_bv 64 p -> getr regs 11 = Z_to_bv 64 n -> getr regs 2 = sp -> getr regs 1 = ra ->
    exists regs',
      msteps ASEGS (mkst regs (0x82a60 : word) mem0 rom) (mkst regs' (0x82aa8 : word) (M7 regs) rom)
      /\ c1_post regs regs' /\ keeps_but RIPL regs regs'.
  Proof.
    intros regs H10 H11 H2 H1. rewrite sp_s in H2. pose proof p_facts as (Pp & Ppn & Pp8 & Pmono & Phi). unfold HIGHEND in *.
    pose proof (frame_only_globs (M7 regs) (M7_frame_only regs)) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
    unfold M7 in *.
    eexists. split.
    - stepiv F_82a18 D_82a18 (Z_to_bv 64 (s - 64)) ltac:(wval).
      stepsd F_82a1c D_82a1c (Z_to_bv 64 (s - 8)) ra ltac:(fsok).
      stepsd F_82a20 D_82a20 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(fsok).
      stepsd F_82a24 D_82a24 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(fsok).
      stepsd F_82a28 D_82a28 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(fsok).
      stepsd F_82a2c D_82a2c (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(fsok).
      stepsd F_82a30 D_82a30 (Z_to_bv 64 (s - 48)) (getr regs 20) ltac:(fsok).
      stepsd F_82a34 D_82a34 (Z_to_bv 64 (s - 56)) (getr regs 21) ltac:(fsok).
      stepb_ft F_82a38 D_82a38 ltac:(cond).
      stepiv F_82a3c D_82a3c (Z_to_bv 64 n) ltac:(wval).
      stepiv F_82a40 D_82a40 (Z_to_bv 64 p) ltac:(wval).
      stepn F_82a44 D_82a44.
      mld F_82a48 D_82a48 (0x154500 : word) G1.
      mld F_82a4c D_82a4c (0x15dcf8 : word) G2.
      stepn F_82a50 D_82a50.
      stepn F_82a54 D_82a54.
      stepn F_82a58 D_82a58.
      stepn F_82a5c D_82a5c.
      apply mst_refl.
    - unfold c1_post, SB, LOWEND. split; [repeat split; gres; rwH; try reflexivity | solve_keeps_but].
  Qed.

  Definition c2_post (rg : bvmap 5 word) : Prop :=
    getr rg 18 = Z_to_bv 64 (p + n) /\ getr rg 9 = Z_to_bv 64 n /\ getr rg 8 = Z_to_bv 64 p /\ getr rg 21 = Z_to_bv 64 0x15dcf8
    /\ getr rg 11 = Z_to_bv 64 SB /\ getr rg 2 = Z_to_bv 64 (s - 64) /\ getr rg 1 = ra.

  Lemma c2_run : forall regs0 regs,
    c1_post regs0 regs ->
    exists regs',
      msteps ASEGS (mkst regs (0x82aa8 : word) (M7 regs0) rom) (mkst regs' (0x82b34 : word) (M7 regs0) rom)
      /\ c2_post regs' /\ keeps_but RIPL regs regs'.
  Proof.
    intros regs0 regs (H9 & H8 & H21 & H11 & H12 & H2 & H1).
    pose proof p_facts as (Pp & Ppn & Pp8 & Pmono & Phi).
    pose proof (frame_only_globs (M7 regs0) (M7_frame_only regs0)) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
    unfold SB, LOWEND, HIGHBEG, HIGHEND in *.
    destruct Happ as [[Hl1 Hl2]|[Hh1 Hh2]].
    - eexists. split.
      + stepb_tk F_82a60 D_82a60 ltac:(cond).
        stepiv F_82aa4 D_82aa4 (Z_to_bv 64 (p + n)) ltac:(wval).
        stepb_tk F_82aa8 D_82aa8 ltac:(cond).
        apply mst_refl.
      + unfold c2_post, SB. split; [repeat split; gres; rwH; reflexivity | solve_keeps_but].
    - eexists. split.
      + stepb_ft F_82a60 D_82a60 ltac:(cond).
        stepn F_82a64 D_82a64.  mld F_82a68 D_82a68 (0x154508 : word) G3.
        stepn F_82a6c D_82a6c.  mld F_82a70 D_82a70 (0x154510 : word) G5.
        mld F_82a74 D_82a74 (0x15e9e8 : word) G4.  mld F_82a78 D_82a78 (0x15e9f0 : word) G6.
        stepn F_82a7c D_82a7c.
        stepb_tk F_82a80 D_82a80 ltac:(cond).
        stepn F_82a88 D_82a88.  mld F_82a8c D_82a8c (0x154518 : word) G7.  mld F_82a90 D_82a90 (0x15e9e0 : word) G8.
        stepn F_82a94 D_82a94.  stepn F_82a98 D_82a98.
        stepb_ft F_82a9c D_82a9c ltac:(cond).
        stepb_ft F_82aa0 D_82aa0 ltac:(cond).
        stepiv F_82aa4 D_82aa4 (Z_to_bv 64 (p + n)) ltac:(wval).
        stepb_ft F_82aa8 D_82aa8 ltac:(cond).
        stepn F_82aac D_82aac.  mld F_82ab0 D_82ab0 (0x154508 : word) G3.
        stepn F_82ab4 D_82ab4.  mld F_82ab8 D_82ab8 (0x154510 : word) G5.
        mld F_82abc D_82abc (0x15e9e8 : word) G4.  mld F_82ac0 D_82ac0 (0x15e9f0 : word) G6.
        stepn F_82ac4 D_82ac4.
        stepb_tk F_82ac8 D_82ac8 ltac:(cond).
        stepn F_82ad0 D_82ad0.  mld F_82ad4 D_82ad4 (0x154518 : word) G7.  mld F_82ad8 D_82ad8 (0x15e9e0 : word) G8.
        stepn F_82adc D_82adc.  stepn F_82ae0 D_82ae0.
        stepb_ft F_82ae4 D_82ae4 ltac:(cond).
        stepb_ft F_82ae8 D_82ae8 ltac:(cond).
        apply mst_refl.
      + unfold c2_post, SB. split; [repeat split; gres; rwH; reflexivity | solve_keeps_but].
  Qed.

  #[local] Notation AB := (p + 7 - (p + 7) mod 8)%Z (only parsing).
  #[local] Notation AE := (p + n - (p + n) mod 8)%Z (only parsing).

  Definition c3_post (rg : bvmap 5 word) : Prop :=
    getr rg 19 = Z_to_bv 64 ((p + 7 - (p + 7) mod 8) / 8 + SB) /\ getr rg 10 = Z_to_bv 64 ((p + n - (p + n) mod 8) / 8 + SB)
    /\ getr rg 20 = Z_to_bv 64 (p + n - (p + n) mod 8)
    /\ getr rg 18 = Z_to_bv 64 (p + n) /\ getr rg 9 = Z_to_bv 64 n /\ getr rg 8 = Z_to_bv 64 p /\ getr rg 21 = Z_to_bv 64 0x15dcf8
    /\ getr rg 2 = Z_to_bv 64 (s - 64).

  Lemma ret_ok_lit1 : ret_ok (0x82b48 : word).  Proof. unfold ret_ok. apply bv_eq. vm_compute. reflexivity. Qed.
  Lemma ret_ok_lit2 : ret_ok (0x82b54 : word).  Proof. unfold ret_ok. apply bv_eq. vm_compute. reflexivity. Qed.

  Lemma c3_run : forall regs0 regs,
    c2_post regs ->
    exists regs',
      msteps ASEGS (mkst regs (0x82b34 : word) (M7 regs0) rom) (mkst regs' (0x82b54 : word) (M7 regs0) rom)
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

    eapply (runs_trans ASEGS _ (fun rg => mkst rg (0x825d4 : word) (M7 regs0) rom)
             (fun rg => getr rg 10 = Z_to_bv 64 AB /\ getr rg 1 = (0x82b48 : word) /\ getr rg 20 = Z_to_bv 64 AE
                        /\ getr rg 18 = Z_to_bv 64 (p + n) /\ getr rg 9 = Z_to_bv 64 n /\ getr rg 8 = Z_to_bv 64 p
                        /\ getr rg 21 = Z_to_bv 64 0x15dcf8 /\ getr rg 2 = Z_to_bv 64 (s - 64) /\ keeps_but RIPL regs rg)).
    { eexists. split.
      - stepb_ft F_82aec D_82aec ltac:(cond).
        stepiv F_82af0 D_82af0 (Z_to_bv 64 (p + 7)) ltac:(wval).
        stepiv F_82af4 D_82af4 (Z_to_bv 64 AB)
          ltac:(gres; unfold v_andi; imm_norm; replace (bv_wrap 64 (-8)) with (2 ^ 64 - 8)%Z by reflexivity; unorm; rewrite land_down8 by lia; reflexivity).
        stepiv F_82af8 D_82af8 (Z_to_bv 64 AE)
          ltac:(gres; rwH; unfold v_andi; imm_norm; replace (bv_wrap 64 (-8)) with (2 ^ 64 - 8)%Z by reflexivity; unorm; rewrite land_down8 by lia; reflexivity).
        stepn F_82afc D_82afc.
        apply mst_refl.
      - repeat split; gres; rwH; try reflexivity; try (apply bv_eq; reflexivity). solve_keeps_but. }
    cbv beta. intros r1 (R10 & R1 & R20 & R18 & R9 & R8 & R21 & R2 & K1).
    destruct (memtoshadow_run r1 (M7 regs0) rom (0x82b48 : word) AB HGM Hab_app R10 R1 ret_ok_lit1) as (r2 & RUN2 & Q10 & K2). unfold SB in Q10.

    eapply (runs_trans ASEGS _ (fun rg => mkst rg (0x825d4 : word) (M7 regs0) rom)
             (fun rg => getr rg 10 = Z_to_bv 64 AE /\ getr rg 1 = (0x82b54 : word) /\ getr rg 19 = Z_to_bv 64 (AB / 8 + 2147450880)
                        /\ getr rg 20 = Z_to_bv 64 AE /\ getr rg 18 = Z_to_bv 64 (p + n) /\ getr rg 9 = Z_to_bv 64 n /\ getr rg 8 = Z_to_bv 64 p
                        /\ getr rg 21 = Z_to_bv 64 0x15dcf8 /\ getr rg 2 = Z_to_bv 64 (s - 64) /\ keeps_but RIPL regs rg)).
    { assert (S20 : getr r2 20 = Z_to_bv 64 AE) by (rewrite (K2 20%bv) by (cbv; tauto); exact R20).
      eexists. split.
      - eapply msteps_trans; [exact RUN2|].
        stepiv F_82b00 D_82b00 (Z_to_bv 64 (AB / 8 + 2147450880)) ltac:(gres; rewrite Q10; unfold v_addi; imm_norm; unorm; f_equal; lia).
        stepiv F_82b04 D_82b04 (Z_to_bv 64 AE) ltac:(gres; rewrite S20; unfold v_addi; imm_norm; unorm; f_equal; lia).
        stepn F_82b08 D_82b08.
        apply mst_refl.
      - repeat split; gres; try reflexivity; try (apply bv_eq; reflexivity);
          try (rewrite (K2 _) by (cbv; tauto); assumption).
        eapply keeps_but_trans; [exact K1|]. solve_keeps_but. }
    cbv beta. intros r3 (T10 & T1 & T19 & T20 & T18 & T9 & T8 & T21 & T2 & K3).
    destruct (memtoshadow_run r3 (M7 regs0) rom (0x82b54 : word) AE HGM Hae_app T10 T1 ret_ok_lit2) as (r4 & RUN4 & U10 & K4). unfold SB in U10.
    exists r4. split; [exact RUN4|]. split.
    - unfold c3_post, SB. repeat split; try (rewrite (K4 _) by (cbv; tauto); assumption). exact U10.
    - eapply keeps_but_trans; [exact K3|]. apply keeps_but_cs. exact K4.
  Qed.

  Lemma rdn1_M7 : forall regs0 z, (SB + p / 8 <= z < SB + (p + n - 1) / 8)%Z ->
    rdn ASEGS (M7 regs0) (Z_to_bv 64 z) 1%nat = Some [Z_to_bv 8 0].
  Proof.
    intros regs0 z Hz. pose proof p_facts as (Pp & Ppn & Pp8 & Pmono & Phi). unfold SB, HIGHEND in *.
    cbn [rdn]. rewrite (frame_only_zero (M7 regs0) (Z_to_bv 64 z) (M7_frame_only regs0)) by (unfold SB; unorm; lia). reflexivity.
  Qed.
  Lemma rdn1_M7_last : forall regs0 z, (z = SB + (p + n - 1) / 8)%Z ->
    rdn ASEGS (M7 regs0) (Z_to_bv 64 z) 1%nat = Some [Z_to_bv 8 kL].
  Proof.
    intros regs0 z ->. cbn [rdn]. rewrite (frame_only_last (M7 regs0) (M7_frame_only regs0)). reflexivity.
  Qed.
  #[local] Ltac maddr z := match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 z) by (symmetry; wval) end.
  #[local] Ltac mlb0 F D z :=
    chain_step; [reflexivity
      | eapply step_lb; [exact F | reflexivity | exact D | maddr z; apply rdn1_M7; unfold SB; lia]
      | step_simpl; vnorm].

  #[local] Ltac mlbk F D z :=
    chain_step; [reflexivity
      | eapply step_lb; [exact F | reflexivity | exact D | maddr z; apply rdn1_M7_last; unfold SB; lia]
      | step_simpl; vnorm; rewrite (v_lb_k kL ltac:(lia))].

  Definition c4_post (rg : bvmap 5 word) : Prop :=
    getr rg 19 = Z_to_bv 64 ((p + 7 - (p + 7) mod 8) / 8 + SB) /\ getr rg 10 = Z_to_bv 64 ((p + n - (p + n) mod 8) / 8 + SB)
    /\ getr rg 2 = Z_to_bv 64 (s - 64).

  #[local] Ltac conds :=
    rwH; unfold c_lts, bv_lts, v_andi; imm_norm; unorm; rewrite ?land7_mod8; unorm; rewrite !signed64_small by lia;
    first [apply Z.ltb_lt | apply Z.ltb_ge]; lia.
  Lemma c4_run : forall regs0 regs,
    c3_post regs ->
    exists regs',
      msteps ASEGS (mkst regs (0x82b54 : word) (M7 regs0) rom) (mkst regs' (0x82bc4 : word) (M7 regs0) rom)
      /\ c4_post regs' /\ keeps_but RIPL regs regs'.
  Proof.
    intros regs0 regs (H19 & H10 & H20 & H18 & H9 & H8 & H21 & H2).
    pose proof p_facts as (Pp & Ppn & Pp8 & Pmono & Phi).
    pose proof (frame_only_globs (M7 regs0) (M7_frame_only regs0)) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
    pose proof (Z.div_mod p 8 ltac:(lia)) as Dp. pose proof (Z.mod_pos_bound p 8 ltac:(lia)) as Mp.
    pose proof (Z.div_mod (p + n - 1) 8 ltac:(lia)) as Dq. pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(lia)) as Mq.
    unfold SB, LOWEND, HIGHBEG, HIGHEND in *.
    destruct (Z.lt_ge_cases (p / 8) ((p + n - 1) / 8)) as [Hlt|Hge].
    -
      destruct HkL as [Hk0|Hk7].
      + eexists. split.
        * mld F_82b0c D_82b0c (0x15dcf8 : word) G2.
          stepiv F_82b10 D_82b10 (Z_to_bv 64 (p / 8)) ltac:(wval).
          stepiv F_82b14 D_82b14 (Z_to_bv 64 (2147450880 + p / 8)) ltac:(wval).
          mlb0 F_82b18 D_82b18 (2147450880 + p / 8)%Z.
          stepb_tk F_82b1c D_82b1c ltac:(cond).
          stepiv F_82b28 D_82b28 (Z_to_bv 64 (p + n - 1)) ltac:(wval).
          stepiv F_82b2c D_82b2c (Z_to_bv 64 ((p + n - 1) / 8)) ltac:(wval).
          stepiv F_82b30 D_82b30 (Z_to_bv 64 (2147450880 + (p + n - 1) / 8)) ltac:(wval).
          mlbk F_82b34 D_82b34 (2147450880 + (p + n - 1) / 8)%Z.
          stepb_tk F_82b38 D_82b38 ltac:(cond).
          apply mst_refl.
        * unfold c4_post, SB. split; [repeat split; gres; rwH; reflexivity | solve_keeps_but].
      + eexists. split.
        * mld F_82b0c D_82b0c (0x15dcf8 : word) G2.
          stepiv F_82b10 D_82b10 (Z_to_bv 64 (p / 8)) ltac:(wval).
          stepiv F_82b14 D_82b14 (Z_to_bv 64 (2147450880 + p / 8)) ltac:(wval).
          mlb0 F_82b18 D_82b18 (2147450880 + p / 8)%Z.
          stepb_tk F_82b1c D_82b1c ltac:(cond).
          stepiv F_82b28 D_82b28 (Z_to_bv 64 (p + n - 1)) ltac:(wval).
          stepiv F_82b2c D_82b2c (Z_to_bv 64 ((p + n - 1) / 8)) ltac:(wval).
          stepiv F_82b30 D_82b30 (Z_to_bv 64 (2147450880 + (p + n - 1) / 8)) ltac:(wval).
          mlbk F_82b34 D_82b34 (2147450880 + (p + n - 1) / 8)%Z.
          stepb_ft F_82b38 D_82b38 ltac:(cond).
          stepn F_82b3c D_82b3c.
          stepb_tk F_82b40 D_82b40 ltac:(conds).
          apply mst_refl.
        * unfold c4_post, SB. split; [repeat split; gres; rwH; reflexivity | solve_keeps_but].
    -
      assert (Heq : (p / 8 = (p + n - 1) / 8)%Z) by lia.
      destruct HkL as [Hk0|Hk7].
      + eexists. split.
        * mld F_82b0c D_82b0c (0x15dcf8 : word) G2.
          stepiv F_82b10 D_82b10 (Z_to_bv 64 (p / 8)) ltac:(wval).
          stepiv F_82b14 D_82b14 (Z_to_bv 64 (2147450880 + (p + n - 1) / 8)) ltac:(wval).
          mlbk F_82b18 D_82b18 (2147450880 + (p + n - 1) / 8)%Z.
          stepb_tk F_82b1c D_82b1c ltac:(cond).
          stepiv F_82b28 D_82b28 (Z_to_bv 64 (p + n - 1)) ltac:(wval).
          stepiv F_82b2c D_82b2c (Z_to_bv 64 ((p + n - 1) / 8)) ltac:(wval).
          stepiv F_82b30 D_82b30 (Z_to_bv 64 (2147450880 + (p + n - 1) / 8)) ltac:(wval).
          mlbk F_82b34 D_82b34 (2147450880 + (p + n - 1) / 8)%Z.
          stepb_tk F_82b38 D_82b38 ltac:(cond).
          apply mst_refl.
        * unfold c4_post, SB. split; [repeat split; gres; rwH; try reflexivity; f_equal; lia | solve_keeps_but].
      + eexists. split.
        * mld F_82b0c D_82b0c (0x15dcf8 : word) G2.
          stepiv F_82b10 D_82b10 (Z_to_bv 64 (p / 8)) ltac:(wval).
          stepiv F_82b14 D_82b14 (Z_to_bv 64 (2147450880 + (p + n - 1) / 8)) ltac:(wval).
          mlbk F_82b18 D_82b18 (2147450880 + (p + n - 1) / 8)%Z.
          stepb_ft F_82b1c D_82b1c ltac:(cond).
          stepn F_82b20 D_82b20.
          stepb_ft F_82b24 D_82b24 ltac:(conds).
          stepiv F_82b28 D_82b28 (Z_to_bv 64 (p + n - 1)) ltac:(wval).
          stepiv F_82b2c D_82b2c (Z_to_bv 64 ((p + n - 1) / 8)) ltac:(wval).
          stepiv F_82b30 D_82b30 (Z_to_bv 64 (2147450880 + (p + n - 1) / 8)) ltac:(wval).
          mlbk F_82b34 D_82b34 (2147450880 + (p + n - 1) / 8)%Z.
          stepb_ft F_82b38 D_82b38 ltac:(cond).
          stepn F_82b3c D_82b3c.
          stepb_tk F_82b40 D_82b40 ltac:(conds).
          apply mst_refl.
        * unfold c4_post, SB. split; [repeat split; gres; rwH; try reflexivity; f_equal; lia | solve_keeps_but].
  Qed.

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

  Lemma M7_reload : forall regs0, reload_ok regs0 (M7 regs0).
  Proof.
    intros regs0. split; [apply M7_frame_only|]. unfold M7. repeat split; slot.
  Qed.
  Lemma W72_reload : forall regs0 M v, reload_ok regs0 M ->
    reload_ok regs0 (wbytes M (Z_to_bv 64 (s - 72)) (word_to_le_bytes 8 v)).
  Proof.
    intros regs0 M v (HF & R1 & R2 & R3 & R4 & R5 & R6 & R7). split; [apply frame_only_w; [exact HF | lia]|].
    repeat split; (peel; assumption).
  Qed.

  Lemma c5_run : forall regs0 regs,
    c4_post regs ->
    exists regs' M',
      msteps ASEGS (mkst regs (0x82bc4 : word) (M7 regs0) rom) (mkst regs' (0x82bd8 : word) M' rom)
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
      stepb_tk F_82b7c D_82b7c ltac:(rewrite E19, E10; unfold c_ltu, bv_ltu; unorm; apply Z.ltb_ge; lia).
      apply mst_refl.
    -
      assert (S1 : exists r1, msteps ASEGS (mkst regs (0x82bc4 : word) (M7 regs0) rom) (mkst r1 (0x92f4c : word) (M7 regs0) rom)
                /\ (getr r1 10 = Z_to_bv 64 sb /\ getr r1 11 = Z_to_bv 64 (se - sb) /\ getr r1 2 = Z_to_bv 64 (s - 64) /\ getr r1 1 = (0x82bd4 : word)
                    /\ keeps_but RIPL regs r1)).
      { eexists. split.
        - stepb_ft F_82b7c D_82b7c ltac:(rewrite E19, E10; unfold c_ltu, bv_ltu; unorm; apply Z.ltb_lt; lia).
          stepiv F_82b80 D_82b80 (Z_to_bv 64 (se - sb)) ltac:(gres; rewrite E19, E10; unfold v_sub; unorm; f_equal; lia).
          stepiv F_82b84 D_82b84 (Z_to_bv 64 sb) ltac:(gres; rewrite E19; unfold v_addi; imm_norm; unorm; f_equal; lia).
          stepn F_82b88 D_82b88.
          apply mst_refl.
        - repeat split; gres; rwH; try reflexivity; try (apply bv_eq; reflexivity). solve_keeps_but. }
      destruct S1 as (r1 & RUN1 & Q10 & Q11 & Q2 & Q1 & K1).
      assert (Hret2 : ret_ok (0x82bd4 : word)) by (unfold ret_ok; apply bv_eq; vm_compute; reflexivity).
      pose proof (mem_is_zero_run (M7 regs0) (Z_to_bv 64 sb) (Z_to_bv 64 (s - 64)) (0x82bd4 : word) (se - sb) sb (s - 64) se
                    (sb + 7 - (sb + 7) mod 8) (se - se mod 8) rom) as MZ.
      specialize (MZ ltac:(unorm; reflexivity) ltac:(unorm; reflexivity) ltac:(lia) eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
      specialize (MZ ltac:(replace (s - 64 - 8)%Z with (s - 72)%Z by lia; apply frame_only_store_ok; [unfold M7; grows | cbn; lia]) Hret2).
      assert (HZI : forall x : word, (sb <= bv_unsigned x < sb + (se - sb))%Z -> M7 regs0 x = Some (Z_to_bv 8 0)).
      { intros x Hx. destruct (Z.lt_ge_cases (bv_unsigned x) (2147450880 + (p + n - 1) / 8)) as [Hxl|Hxh].
        - apply (frame_only_zero (M7 regs0) x (M7_frame_only regs0)). unfold SB. lia.
        -
          assert (Ex : x = Z_to_bv 64 (SB + (p + n - 1) / 8)) by (apply bv_eq; unfold SB; unorm; lia).
          pose proof (Z.div_mod AE 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound AE 8 ltac:(lia)).
          pose proof (Z.div_mod (p + n - 1) 8 ltac:(lia)) as D2. pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(lia)).
          assert (kL = 0)%Z as Hk0 by lia.
          rewrite Ex, (frame_only_last (M7 regs0) (M7_frame_only regs0)), Hk0. reflexivity. }
      specialize (MZ HZI).
      destruct (MZ r1 Q10 Q11 Q2 Q1) as (r2 & RUN2 & V10 & V2 & V1 & K2).
      replace (s - 64 - 8)%Z with (s - 72)%Z in RUN2 by lia.
      eexists. exists (wbytes (M7 regs0) (Z_to_bv 64 (s - 72)) (word_to_le_bytes 8 (0x82bd4 : word))). split; [|split; [apply W72_reload, M7_reload|]].
      + eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|].
        stepb_ft F_82b8c D_82b8c ltac:(rewrite V10; unfold c_eq, bv_eqb; unorm; apply Z.eqb_neq; lia).
        apply mst_refl.
      + split; [gres; exact V2|]. split; [|unfold M7; grows].
        eapply keeps_but_trans; [exact K1|]. apply keeps_but_cs. exact K2.
  Qed.

  Lemma c6_run : forall regs0 regs M,
    reload_ok regs0 M -> getr regs 2 = Z_to_bv 64 (s - 64) ->
    exists regs',
      msteps ASEGS (mkst regs (0x82bd8 : word) M rom) (mkst regs' ra M rom)
      /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 2 = sp /\ getr regs' 1 = ra
      /\ getr regs' 8 = getr regs0 8 /\ getr regs' 9 = getr regs0 9 /\ getr regs' 18 = getr regs0 18
      /\ getr regs' 19 = getr regs0 19 /\ getr regs' 20 = getr regs0 20 /\ getr regs' 21 = getr regs0 21
      /\ keeps_but RIPL regs regs'.
  Proof.
    intros regs0 regs M (HF & R1 & R2 & R3 & R4 & R5 & R6 & R7) H2.
    eexists. split.
    - stepn F_82b90 D_82b90.
      stepn F_82b94 D_82b94.
      stepld F_82b98 D_82b98 ra ltac:(maddr (s - 8)%Z; exact R1).
      stepld F_82b9c D_82b9c (getr regs0 8) ltac:(maddr (s - 16)%Z; exact R2).
      stepld F_82ba0 D_82ba0 (getr regs0 9) ltac:(maddr (s - 24)%Z; exact R3).
      stepld F_82ba4 D_82ba4 (getr regs0 18) ltac:(maddr (s - 32)%Z; exact R4).
      stepld F_82ba8 D_82ba8 (getr regs0 19) ltac:(maddr (s - 40)%Z; exact R5).
      stepld F_82bac D_82bac (getr regs0 20) ltac:(maddr (s - 48)%Z; exact R6).
      stepld F_82bb0 D_82bb0 (getr regs0 21) ltac:(maddr (s - 56)%Z; exact R7).
      stepiv F_82bb4 D_82bb4 (Z_to_bv 64 s) ltac:(wval).
      stepret F_82bb8 D_82bb8 ra ltac:(rwH; reflexivity).
      apply mst_refl.
    - repeat split; gres; try reflexivity; [symmetry; apply sp_s | solve_keeps_but].
  Qed.

  Theorem region_is_poisoned_run : forall regs,
    getr regs 10 = Z_to_bv 64 p -> getr regs 11 = Z_to_bv 64 n -> getr regs 2 = sp -> getr regs 1 = ra ->
    exists regs' M',
      msteps ASEGS (mkst regs (0x82a60 : word) mem0 rom) (mkst regs' ra M' rom)
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
