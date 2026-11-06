(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac RefMemcpyLib MemSplit As0StepLib Bo0MemIsZero.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import Bo0_code_611e4_61830 Bo0_code_61b80_61ec4.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
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
  rdn ASEGS M (0xd64c8 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xde738)) /\
  rdn ASEGS M (0xde738 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 SB)) /\
  rdn ASEGS M (0xd64d0 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xdf428)) /\
  rdn ASEGS M (0xdf428 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) /\
  rdn ASEGS M (0xd64d8 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xdf430)) /\
  rdn ASEGS M (0xdf430 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) /\
  rdn ASEGS M (0xd64e0 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xdf420)) /\
  rdn ASEGS M (0xdf420 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 HIGHEND)).

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
Lemma memtoshadow_run : forall regs (M rom : word -> option byte) (ret : word) (p : Z),
  rt_layout_globs M -> in_app p ->
  getr regs 10 = Z_to_bv 64 p -> getr regs 1 = ret -> ret_ok ret ->
  exists regs',
    msteps ASEGS (mkst regs (0x616f4 : word) M rom) (mkst regs' ret M rom)
    /\ getr regs' 10 = Z_to_bv 64 (p / 8 + SB) /\ keeps_cs regs regs'.
Proof.
  intros regs M rom ret p (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8) Hp H10 H1 Hret.
  unfold in_app, LOWEND, HIGHBEG, HIGHEND in Hp. unfold SB in *.
  pose proof (Z.div_mod p 8 ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound p 8 ltac:(lia)) as Hmd.
  destruct Hp as [Hlow|Hhigh].
  - eexists. split.
    + stepn F_616f4 D_616f4.                                     (* [comment removed for export] *)
      mld F_616f8 D_616f8 (0xd64c8 : word) G1.                     (* [comment removed for export] *)
      mld F_616fc D_616fc (0xde738 : word) G2.                     (* [comment removed for export] *)
      stepn F_61700 D_61700.                                     (* [comment removed for export] *)
      stepn F_61704 D_61704.                                     (* [comment removed for export] *)
      stepn F_61708 D_61708.                                     (* [comment removed for export] *)
      stepn F_6170c D_6170c.                                     (* [comment removed for export] *)
      stepb_tk F_61710 D_61710 ltac:(cond).                      (* [comment removed for export] *)
      stepiv F_61754 D_61754 (Z_to_bv 64 (p / 8)) ltac:(wval).    (* [comment removed for export] *)
      stepiv F_61758 D_61758 (Z_to_bv 64 (p / 8 + 0x7fff8000)) ltac:(wval).   (* [comment removed for export] *)
      stepret F_6175c D_6175c ret ltac:(rwH; reflexivity).
      apply mst_refl.
    + split; [gres; reflexivity | solve_keeps_cs].
  - eexists. split.
    + stepn F_616f4 D_616f4.
      mld F_616f8 D_616f8 (0xd64c8 : word) G1.
      mld F_616fc D_616fc (0xde738 : word) G2.
      stepn F_61700 D_61700.
      stepn F_61704 D_61704.
      stepn F_61708 D_61708.
      stepn F_6170c D_6170c.
      stepb_ft F_61710 D_61710 ltac:(cond).                      (* [comment removed for export] *)
      stepn F_61714 D_61714.                                     (* [comment removed for export] *)
      mld F_61718 D_61718 (0xd64d0 : word) G3.                     (* [comment removed for export] *)
      stepn F_6171c D_6171c.                                     (* [comment removed for export] *)
      mld F_61720 D_61720 (0xd64d8 : word) G5.                     (* [comment removed for export] *)
      mld F_61724 D_61724 (0xdf428 : word) G4.                     (* [comment removed for export] *)
      mld F_61728 D_61728 (0xdf430 : word) G6.                     (* [comment removed for export] *)
      stepn F_6172c D_6172c.                                     (* [comment removed for export] *)
      stepb_tk F_61730 D_61730 ltac:(cond).                      (* [comment removed for export] *)
      stepn F_61738 D_61738.                                     (* [comment removed for export] *)
      mld F_6173c D_6173c (0xd64e0 : word) G7.                     (* [comment removed for export] *)
      mld F_61740 D_61740 (0xdf420 : word) G8.                     (* [comment removed for export] *)
      stepn F_61744 D_61744.                                     (* [comment removed for export] *)
      stepn F_61748 D_61748.                                     (* [comment removed for export] *)
      stepb_ft F_6174c D_6174c ltac:(cond).                      (* [comment removed for export] *)
      stepb_ft F_61750 D_61750 ltac:(cond).                      (* [comment removed for export] *)
      stepiv F_61754 D_61754 (Z_to_bv 64 (p / 8)) ltac:(wval).
      stepiv F_61758 D_61758 (Z_to_bv 64 (p / 8 + 0x7fff8000)) ltac:(wval).
      stepret F_6175c D_6175c ret ltac:(rwH; reflexivity).
      apply mst_refl.
    + split; [gres; reflexivity | solve_keeps_cs].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
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
(* [comment removed for export] *)
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

  Lemma sp_s : sp = Z_to_bv 64 s.  Proof. rewrite <- Hs_def. symmetry. apply Z_to_bv_bv_unsigned. Qed.
  Lemma p_facts : (0 <= p)%Z /\ (p + n <= HIGHEND)%Z /\ (0 <= p / 8)%Z /\ (p / 8 <= (p + n - 1) / 8)%Z /\ ((p + n - 1) / 8 <= HIGHEND)%Z.
  Proof.
    unfold LOWEND, HIGHBEG, HIGHEND in *. destruct Happ as [[H1 H2]|[H1 H2]];
    (repeat split; [lia | lia | apply Z.div_pos; lia | apply Z.div_le_mono; lia | apply Z.div_le_upper_bound; lia]).
  Qed.

  (* [comment removed for export] *)
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
  Lemma M7_frame_only : forall rg, frame_only (M7 rg).  Proof. intros rg. unfold M7. fonly. Qed.

  Definition c1_post (regs rg : bvmap 5 word) : Prop :=
    getr rg 9 = Z_to_bv 64 n /\ getr rg 8 = Z_to_bv 64 p /\ getr rg 21 = Z_to_bv 64 0xde738 /\ getr rg 11 = Z_to_bv 64 SB
    /\ getr rg 12 = Z_to_bv 64 LOWEND /\ getr rg 2 = Z_to_bv 64 (s - 64) /\ getr rg 1 = ra.

  (* [comment removed for export] *)
  Lemma c1_run : forall regs,
    getr regs 10 = Z_to_bv 64 p -> getr regs 11 = Z_to_bv 64 n -> getr regs 2 = sp -> getr regs 1 = ra ->
    exists regs',
      msteps ASEGS (mkst regs (0x61b80 : word) mem0 rom) (mkst regs' (0x61bc8 : word) (M7 regs) rom)
      /\ c1_post regs regs' /\ keeps_but RIPL regs regs'.
  Proof.
    intros regs H10 H11 H2 H1. rewrite sp_s in H2. pose proof p_facts as (Pp & Ppn & Pp8 & Pmono & Phi). unfold HIGHEND in *.
    pose proof (frame_only_globs (M7 regs) (M7_frame_only regs)) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
    unfold M7 in *.
    eexists. split.
    - stepiv F_61b80 D_61b80 (Z_to_bv 64 (s - 64)) ltac:(wval).                       (* [comment removed for export] *)
      stepsd F_61b84 D_61b84 (Z_to_bv 64 (s - 8)) ra ltac:(fsok).                        (* [comment removed for export] *)
      stepsd F_61b88 D_61b88 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(fsok).             (* [comment removed for export] *)
      stepsd F_61b8c D_61b8c (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(fsok).             (* [comment removed for export] *)
      stepsd F_61b90 D_61b90 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(fsok).            (* [comment removed for export] *)
      stepsd F_61b94 D_61b94 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(fsok).            (* [comment removed for export] *)
      stepsd F_61b98 D_61b98 (Z_to_bv 64 (s - 48)) (getr regs 20) ltac:(fsok).            (* [comment removed for export] *)
      stepsd F_61b9c D_61b9c (Z_to_bv 64 (s - 56)) (getr regs 21) ltac:(fsok).            (* [comment removed for export] *)
      stepb_ft F_61ba0 D_61ba0 ltac:(cond).                                                (* [comment removed for export] *)
      stepiv F_61ba4 D_61ba4 (Z_to_bv 64 n) ltac:(wval).                                  (* [comment removed for export] *)
      stepiv F_61ba8 D_61ba8 (Z_to_bv 64 p) ltac:(wval).                                  (* [comment removed for export] *)
      stepn F_61bac D_61bac.                                                               (* [comment removed for export] *)
      mld F_61bb0 D_61bb0 (0xd64c8 : word) G1.                                             (* [comment removed for export] *)
      mld F_61bb4 D_61bb4 (0xde738 : word) G2.                                             (* [comment removed for export] *)
      stepn F_61bb8 D_61bb8.                                                               (* [comment removed for export] *)
      stepn F_61bbc D_61bbc.                                                               (* [comment removed for export] *)
      stepn F_61bc0 D_61bc0.                                                               (* [comment removed for export] *)
      stepn F_61bc4 D_61bc4.                                                               (* [comment removed for export] *)
      apply mst_refl.
    - unfold c1_post, SB, LOWEND. split; [repeat split; gres; rwH; try reflexivity | solve_keeps_but].
  Qed.

  Definition c2_post (rg : bvmap 5 word) : Prop :=
    getr rg 18 = Z_to_bv 64 (p + n) /\ getr rg 9 = Z_to_bv 64 n /\ getr rg 8 = Z_to_bv 64 p /\ getr rg 21 = Z_to_bv 64 0xde738
    /\ getr rg 11 = Z_to_bv 64 SB /\ getr rg 2 = Z_to_bv 64 (s - 64) /\ getr rg 1 = ra.

  (* [comment removed for export] *)
  Lemma c2_run : forall regs0 regs,
    c1_post regs0 regs ->
    exists regs',
      msteps ASEGS (mkst regs (0x61bc8 : word) (M7 regs0) rom) (mkst regs' (0x61c54 : word) (M7 regs0) rom)
      /\ c2_post regs' /\ keeps_but RIPL regs regs'.
  Proof.
    intros regs0 regs (H9 & H8 & H21 & H11 & H12 & H2 & H1).
    pose proof p_facts as (Pp & Ppn & Pp8 & Pmono & Phi).
    pose proof (frame_only_globs (M7 regs0) (M7_frame_only regs0)) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
    unfold SB, LOWEND, HIGHBEG, HIGHEND in *.
    destruct Happ as [[Hl1 Hl2]|[Hh1 Hh2]].
    - eexists. split.
      + stepb_tk F_61bc8 D_61bc8 ltac:(cond).                                  (* [comment removed for export] *)
        stepiv F_61c0c D_61c0c (Z_to_bv 64 (p + n)) ltac:(wval).               (* [comment removed for export] *)
        stepb_tk F_61c10 D_61c10 ltac:(cond).                                  (* [comment removed for export] *)
        apply mst_refl.
      + unfold c2_post, SB. split; [repeat split; gres; rwH; reflexivity | solve_keeps_but].
    - eexists. split.
      + stepb_ft F_61bc8 D_61bc8 ltac:(cond).
        stepn F_61bcc D_61bcc.  mld F_61bd0 D_61bd0 (0xd64d0 : word) G3.
        stepn F_61bd4 D_61bd4.  mld F_61bd8 D_61bd8 (0xd64d8 : word) G5.
        mld F_61bdc D_61bdc (0xdf428 : word) G4.  mld F_61be0 D_61be0 (0xdf430 : word) G6.
        stepn F_61be4 D_61be4.                                                 (* [comment removed for export] *)
        stepb_tk F_61be8 D_61be8 ltac:(cond).                                  (* [comment removed for export] *)
        stepn F_61bf0 D_61bf0.  mld F_61bf4 D_61bf4 (0xd64e0 : word) G7.  mld F_61bf8 D_61bf8 (0xdf420 : word) G8.
        stepn F_61bfc D_61bfc.  stepn F_61c00 D_61c00.                         (* [comment removed for export] *)
        stepb_ft F_61c04 D_61c04 ltac:(cond).                                  (* [comment removed for export] *)
        stepb_ft F_61c08 D_61c08 ltac:(cond).                                  (* [comment removed for export] *)
        stepiv F_61c0c D_61c0c (Z_to_bv 64 (p + n)) ltac:(wval).               (* [comment removed for export] *)
        stepb_ft F_61c10 D_61c10 ltac:(cond).                                  (* [comment removed for export] *)
        stepn F_61c14 D_61c14.  mld F_61c18 D_61c18 (0xd64d0 : word) G3.
        stepn F_61c1c D_61c1c.  mld F_61c20 D_61c20 (0xd64d8 : word) G5.
        mld F_61c24 D_61c24 (0xdf428 : word) G4.  mld F_61c28 D_61c28 (0xdf430 : word) G6.
        stepn F_61c2c D_61c2c.                                                 (* [comment removed for export] *)
        stepb_tk F_61c30 D_61c30 ltac:(cond).                                  (* [comment removed for export] *)
        stepn F_61c38 D_61c38.  mld F_61c3c D_61c3c (0xd64e0 : word) G7.  mld F_61c40 D_61c40 (0xdf420 : word) G8.
        stepn F_61c44 D_61c44.  stepn F_61c48 D_61c48.                         (* [comment removed for export] *)
        stepb_ft F_61c4c D_61c4c ltac:(cond).                                  (* [comment removed for export] *)
        stepb_ft F_61c50 D_61c50 ltac:(cond).                                  (* [comment removed for export] *)
        apply mst_refl.
      + unfold c2_post, SB. split; [repeat split; gres; rwH; reflexivity | solve_keeps_but].
  Qed.

  #[local] Notation AB := (p + 7 - (p + 7) mod 8)%Z (only parsing).      (* [comment removed for export] *)
  #[local] Notation AE := (p + n - (p + n) mod 8)%Z (only parsing).      (* [comment removed for export] *)

  Definition c3_post (rg : bvmap 5 word) : Prop :=
    getr rg 19 = Z_to_bv 64 ((p + 7 - (p + 7) mod 8) / 8 + SB) /\ getr rg 10 = Z_to_bv 64 ((p + n - (p + n) mod 8) / 8 + SB)
    /\ getr rg 20 = Z_to_bv 64 (p + n - (p + n) mod 8)
    /\ getr rg 18 = Z_to_bv 64 (p + n) /\ getr rg 9 = Z_to_bv 64 n /\ getr rg 8 = Z_to_bv 64 p /\ getr rg 21 = Z_to_bv 64 0xde738
    /\ getr rg 2 = Z_to_bv 64 (s - 64).

  Lemma ret_ok_lit1 : ret_ok (0x61c68 : word).  Proof. unfold ret_ok. apply bv_eq. vm_compute. reflexivity. Qed.
  Lemma ret_ok_lit2 : ret_ok (0x61c74 : word).  Proof. unfold ret_ok. apply bv_eq. vm_compute. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma c3_run : forall regs0 regs,
    c2_post regs ->
    exists regs',
      msteps ASEGS (mkst regs (0x61c54 : word) (M7 regs0) rom) (mkst regs' (0x61c74 : word) (M7 regs0) rom)
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
    eapply (runs_trans ASEGS _ (fun rg => mkst rg (0x616f4 : word) (M7 regs0) rom)
             (fun rg => getr rg 10 = Z_to_bv 64 AB /\ getr rg 1 = (0x61c68 : word) /\ getr rg 20 = Z_to_bv 64 AE
                        /\ getr rg 18 = Z_to_bv 64 (p + n) /\ getr rg 9 = Z_to_bv 64 n /\ getr rg 8 = Z_to_bv 64 p
                        /\ getr rg 21 = Z_to_bv 64 0xde738 /\ getr rg 2 = Z_to_bv 64 (s - 64) /\ keeps_but RIPL regs rg)).
    { eexists. split.
      - stepb_ft F_61c54 D_61c54 ltac:(cond).                                   (* [comment removed for export] *)
        stepiv F_61c58 D_61c58 (Z_to_bv 64 (p + 7)) ltac:(wval).                (* [comment removed for export] *)
        stepiv F_61c5c D_61c5c (Z_to_bv 64 AB)
          ltac:(gres; unfold v_andi; imm_norm; replace (bv_wrap 64 (-8)) with (2 ^ 64 - 8)%Z by reflexivity; unorm; rewrite land_down8 by lia; reflexivity).
        stepiv F_61c60 D_61c60 (Z_to_bv 64 AE)
          ltac:(gres; rwH; unfold v_andi; imm_norm; replace (bv_wrap 64 (-8)) with (2 ^ 64 - 8)%Z by reflexivity; unorm; rewrite land_down8 by lia; reflexivity).
        stepn F_61c64 D_61c64.                                                  (* [comment removed for export] *)
        apply mst_refl.
      - repeat split; gres; rwH; try reflexivity; try (apply bv_eq; reflexivity). solve_keeps_but. }
    cbv beta. intros r1 (R10 & R1 & R20 & R18 & R9 & R8 & R21 & R2 & K1).
    destruct (memtoshadow_run r1 (M7 regs0) rom (0x61c68 : word) AB HGM Hab_app R10 R1 ret_ok_lit1) as (r2 & RUN2 & Q10 & K2). unfold SB in Q10.
    (* [comment removed for export] *)
    eapply (runs_trans ASEGS _ (fun rg => mkst rg (0x616f4 : word) (M7 regs0) rom)
             (fun rg => getr rg 10 = Z_to_bv 64 AE /\ getr rg 1 = (0x61c74 : word) /\ getr rg 19 = Z_to_bv 64 (AB / 8 + 2147450880)
                        /\ getr rg 20 = Z_to_bv 64 AE /\ getr rg 18 = Z_to_bv 64 (p + n) /\ getr rg 9 = Z_to_bv 64 n /\ getr rg 8 = Z_to_bv 64 p
                        /\ getr rg 21 = Z_to_bv 64 0xde738 /\ getr rg 2 = Z_to_bv 64 (s - 64) /\ keeps_but RIPL regs rg)).
    { assert (S20 : getr r2 20 = Z_to_bv 64 AE) by (rewrite (K2 20%bv) by (cbv; tauto); exact R20).
      eexists. split.
      - eapply msteps_trans; [exact RUN2|].
        stepiv F_61c68 D_61c68 (Z_to_bv 64 (AB / 8 + 2147450880)) ltac:(gres; rewrite Q10; unfold v_addi; imm_norm; unorm; f_equal; lia).  (* [comment removed for export] *)
        stepiv F_61c6c D_61c6c (Z_to_bv 64 AE) ltac:(gres; rewrite S20; unfold v_addi; imm_norm; unorm; f_equal; lia).                    (* [comment removed for export] *)
        stepn F_61c70 D_61c70.                                                  (* [comment removed for export] *)
        apply mst_refl.
      - repeat split; gres; try reflexivity; try (apply bv_eq; reflexivity);
          try (rewrite (K2 _) by (cbv; tauto); assumption).
        eapply keeps_but_trans; [exact K1|]. solve_keeps_but. }
    cbv beta. intros r3 (T10 & T1 & T19 & T20 & T18 & T9 & T8 & T21 & T2 & K3).
    destruct (memtoshadow_run r3 (M7 regs0) rom (0x61c74 : word) AE HGM Hae_app T10 T1 ret_ok_lit2) as (r4 & RUN4 & U10 & K4). unfold SB in U10.
    exists r4. split; [exact RUN4|]. split.
    - unfold c3_post, SB. repeat split; try (rewrite (K4 _) by (cbv; tauto); assumption). exact U10.
    - eapply keeps_but_trans; [exact K3|]. apply keeps_but_cs. exact K4.
  Qed.

  (* [comment removed for export] *)
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
  Lemma c4_run : forall regs0 regs,
    c3_post regs ->
    exists regs',
      msteps ASEGS (mkst regs (0x61c74 : word) (M7 regs0) rom) (mkst regs' (0x61ce4 : word) (M7 regs0) rom)
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
        * mld F_61c74 D_61c74 (0xde738 : word) G2.                                       (* [comment removed for export] *)
          stepiv F_61c78 D_61c78 (Z_to_bv 64 (p / 8)) ltac:(wval).                        (* [comment removed for export] *)
          stepiv F_61c7c D_61c7c (Z_to_bv 64 (2147450880 + p / 8)) ltac:(wval).           (* [comment removed for export] *)
          mlb0 F_61c80 D_61c80 (2147450880 + p / 8)%Z.                                    (* [comment removed for export] *)
          stepb_tk F_61c84 D_61c84 ltac:(cond).                                           (* [comment removed for export] *)
          stepiv F_61c90 D_61c90 (Z_to_bv 64 (p + n - 1)) ltac:(wval).                    (* [comment removed for export] *)
          stepiv F_61c94 D_61c94 (Z_to_bv 64 ((p + n - 1) / 8)) ltac:(wval).              (* [comment removed for export] *)
          stepiv F_61c98 D_61c98 (Z_to_bv 64 (2147450880 + (p + n - 1) / 8)) ltac:(wval). (* [comment removed for export] *)
          mlbk F_61c9c D_61c9c (2147450880 + (p + n - 1) / 8)%Z.                          (* [comment removed for export] *)
          stepb_tk F_61ca0 D_61ca0 ltac:(cond).                                           (* [comment removed for export] *)
          apply mst_refl.
        * unfold c4_post, SB. split; [repeat split; gres; rwH; reflexivity | solve_keeps_but].
      + eexists. split.
        * mld F_61c74 D_61c74 (0xde738 : word) G2.
          stepiv F_61c78 D_61c78 (Z_to_bv 64 (p / 8)) ltac:(wval).
          stepiv F_61c7c D_61c7c (Z_to_bv 64 (2147450880 + p / 8)) ltac:(wval).
          mlb0 F_61c80 D_61c80 (2147450880 + p / 8)%Z.
          stepb_tk F_61c84 D_61c84 ltac:(cond).
          stepiv F_61c90 D_61c90 (Z_to_bv 64 (p + n - 1)) ltac:(wval).
          stepiv F_61c94 D_61c94 (Z_to_bv 64 ((p + n - 1) / 8)) ltac:(wval).
          stepiv F_61c98 D_61c98 (Z_to_bv 64 (2147450880 + (p + n - 1) / 8)) ltac:(wval).
          mlbk F_61c9c D_61c9c (2147450880 + (p + n - 1) / 8)%Z.                          (* [comment removed for export] *)
          stepb_ft F_61ca0 D_61ca0 ltac:(cond).                                           (* [comment removed for export] *)
          stepn F_61ca4 D_61ca4.                                                          (* [comment removed for export] *)
          stepb_tk F_61ca8 D_61ca8 ltac:(conds).                                          (* [comment removed for export] *)
          apply mst_refl.
        * unfold c4_post, SB. split; [repeat split; gres; rwH; reflexivity | solve_keeps_but].
    - (* [comment removed for export] *)
      assert (Heq : (p / 8 = (p + n - 1) / 8)%Z) by lia.
      destruct HkL as [Hk0|Hk7].
      + eexists. split.
        * mld F_61c74 D_61c74 (0xde738 : word) G2.
          stepiv F_61c78 D_61c78 (Z_to_bv 64 (p / 8)) ltac:(wval).
          stepiv F_61c7c D_61c7c (Z_to_bv 64 (2147450880 + (p + n - 1) / 8)) ltac:(wval).
          mlbk F_61c80 D_61c80 (2147450880 + (p + n - 1) / 8)%Z.                          (* [comment removed for export] *)
          stepb_tk F_61c84 D_61c84 ltac:(cond).
          stepiv F_61c90 D_61c90 (Z_to_bv 64 (p + n - 1)) ltac:(wval).
          stepiv F_61c94 D_61c94 (Z_to_bv 64 ((p + n - 1) / 8)) ltac:(wval).
          stepiv F_61c98 D_61c98 (Z_to_bv 64 (2147450880 + (p + n - 1) / 8)) ltac:(wval).
          mlbk F_61c9c D_61c9c (2147450880 + (p + n - 1) / 8)%Z.
          stepb_tk F_61ca0 D_61ca0 ltac:(cond).
          apply mst_refl.
        * unfold c4_post, SB. split; [repeat split; gres; rwH; try reflexivity; f_equal; lia | solve_keeps_but].
      + eexists. split.
        * mld F_61c74 D_61c74 (0xde738 : word) G2.
          stepiv F_61c78 D_61c78 (Z_to_bv 64 (p / 8)) ltac:(wval).
          stepiv F_61c7c D_61c7c (Z_to_bv 64 (2147450880 + (p + n - 1) / 8)) ltac:(wval).
          mlbk F_61c80 D_61c80 (2147450880 + (p + n - 1) / 8)%Z.                          (* [comment removed for export] *)
          stepb_ft F_61c84 D_61c84 ltac:(cond).
          stepn F_61c88 D_61c88.                                                          (* [comment removed for export] *)
          stepb_ft F_61c8c D_61c8c ltac:(conds).                                          (* [comment removed for export] *)
          stepiv F_61c90 D_61c90 (Z_to_bv 64 (p + n - 1)) ltac:(wval).
          stepiv F_61c94 D_61c94 (Z_to_bv 64 ((p + n - 1) / 8)) ltac:(wval).
          stepiv F_61c98 D_61c98 (Z_to_bv 64 (2147450880 + (p + n - 1) / 8)) ltac:(wval).
          mlbk F_61c9c D_61c9c (2147450880 + (p + n - 1) / 8)%Z.
          stepb_ft F_61ca0 D_61ca0 ltac:(cond).
          stepn F_61ca4 D_61ca4.
          stepb_tk F_61ca8 D_61ca8 ltac:(conds).
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

  (* [comment removed for export] *)
  Lemma c5_run : forall regs0 regs,
    c4_post regs ->
    exists regs' M',
      msteps ASEGS (mkst regs (0x61ce4 : word) (M7 regs0) rom) (mkst regs' (0x61cf8 : word) M' rom)
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
      stepb_tk F_61ce4 D_61ce4 ltac:(rewrite E19, E10; unfold c_ltu, bv_ltu; unorm; apply Z.ltb_ge; lia).   (* [comment removed for export] *)
      apply mst_refl.
    - (* [comment removed for export] *)
      assert (S1 : exists r1, msteps ASEGS (mkst regs (0x61ce4 : word) (M7 regs0) rom) (mkst r1 (0x71b10 : word) (M7 regs0) rom)
                /\ (getr r1 10 = Z_to_bv 64 sb /\ getr r1 11 = Z_to_bv 64 (se - sb) /\ getr r1 2 = Z_to_bv 64 (s - 64) /\ getr r1 1 = (0x61cf4 : word)
                    /\ keeps_but RIPL regs r1)).
      { eexists. split.
        - stepb_ft F_61ce4 D_61ce4 ltac:(rewrite E19, E10; unfold c_ltu, bv_ltu; unorm; apply Z.ltb_lt; lia).  (* [comment removed for export] *)
          stepiv F_61ce8 D_61ce8 (Z_to_bv 64 (se - sb)) ltac:(gres; rewrite E19, E10; unfold v_sub; unorm; f_equal; lia).   (* [comment removed for export] *)
          stepiv F_61cec D_61cec (Z_to_bv 64 sb) ltac:(gres; rewrite E19; unfold v_addi; imm_norm; unorm; f_equal; lia).       (* [comment removed for export] *)
          stepn F_61cf0 D_61cf0.                                                                                          (* [comment removed for export] *)
          apply mst_refl.
        - repeat split; gres; rwH; try reflexivity; try (apply bv_eq; reflexivity). solve_keeps_but. }
      destruct S1 as (r1 & RUN1 & Q10 & Q11 & Q2 & Q1 & K1).
      assert (Hret2 : ret_ok (0x61cf4 : word)) by (unfold ret_ok; apply bv_eq; vm_compute; reflexivity).
      pose proof (mem_is_zero_run (M7 regs0) (Z_to_bv 64 sb) (Z_to_bv 64 (s - 64)) (0x61cf4 : word) (se - sb) sb (s - 64) se
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
      eexists. exists (wbytes (M7 regs0) (Z_to_bv 64 (s - 72)) (word_to_le_bytes 8 (0x61cf4 : word))). split; [|split; [apply W72_reload, M7_reload|]].
      + eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|].
        stepb_ft F_61cf4 D_61cf4 ltac:(rewrite V10; unfold c_eq, bv_eqb; unorm; apply Z.eqb_neq; lia).   (* [comment removed for export] *)
        apply mst_refl.
      + split; [gres; exact V2|]. split; [|unfold M7; grows].
        eapply keeps_but_trans; [exact K1|]. apply keeps_but_cs. exact K2.
  Qed.

  (* [comment removed for export] *)
  Lemma c6_run : forall regs0 regs M,
    reload_ok regs0 M -> getr regs 2 = Z_to_bv 64 (s - 64) ->
    exists regs',
      msteps ASEGS (mkst regs (0x61cf8 : word) M rom) (mkst regs' ra M rom)
      /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 2 = sp /\ getr regs' 1 = ra
      /\ getr regs' 8 = getr regs0 8 /\ getr regs' 9 = getr regs0 9 /\ getr regs' 18 = getr regs0 18
      /\ getr regs' 19 = getr regs0 19 /\ getr regs' 20 = getr regs0 20 /\ getr regs' 21 = getr regs0 21
      /\ keeps_but RIPL regs regs'.
  Proof.
    intros regs0 regs M (HF & R1 & R2 & R3 & R4 & R5 & R6 & R7) H2.
    eexists. split.
    - stepn F_61cf8 D_61cf8.                                                       (* [comment removed for export] *)
      stepn F_61cfc D_61cfc.                                                       (* [comment removed for export] *)
      stepld F_61d00 D_61d00 ra ltac:(maddr (s - 8)%Z; exact R1).                 (* [comment removed for export] *)
      stepld F_61d04 D_61d04 (getr regs0 8) ltac:(maddr (s - 16)%Z; exact R2).    (* [comment removed for export] *)
      stepld F_61d08 D_61d08 (getr regs0 9) ltac:(maddr (s - 24)%Z; exact R3).    (* [comment removed for export] *)
      stepld F_61d0c D_61d0c (getr regs0 18) ltac:(maddr (s - 32)%Z; exact R4).   (* [comment removed for export] *)
      stepld F_61d10 D_61d10 (getr regs0 19) ltac:(maddr (s - 40)%Z; exact R5).   (* [comment removed for export] *)
      stepld F_61d14 D_61d14 (getr regs0 20) ltac:(maddr (s - 48)%Z; exact R6).   (* [comment removed for export] *)
      stepld F_61d18 D_61d18 (getr regs0 21) ltac:(maddr (s - 56)%Z; exact R7).   (* [comment removed for export] *)
      stepiv F_61d1c D_61d1c (Z_to_bv 64 s) ltac:(wval).                          (* [comment removed for export] *)
      stepret F_61d20 D_61d20 ra ltac:(rwH; reflexivity).
      apply mst_refl.
    - repeat split; gres; try reflexivity; [symmetry; apply sp_s | solve_keeps_but].
  Qed.

  (* [comment removed for export] *)
  Theorem region_is_poisoned_run : forall regs,
    getr regs 10 = Z_to_bv 64 p -> getr regs 11 = Z_to_bv 64 n -> getr regs 2 = sp -> getr regs 1 = ra ->
    exists regs' M',
      msteps ASEGS (mkst regs (0x61b80 : word) mem0 rom) (mkst regs' ra M' rom)
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
