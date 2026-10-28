(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2 LeptArithB LeptExec LeptExecX LeptExecB.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23LeptRbLib.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptBase V23LeptErr V23ExecUb V23_code_red_count V23_code_red_acc.
Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Ltac exB_sc_hook ::=
  first [ v23_sc_hook
        | (repeat rewrite ext_val_sx_id by (first [ lia | (rewrite ?u_Z2bv by lia; ex_pow2; lia) ]);
           rewrite ?w_addw; rewrite ?zbv_addw_small by lia; ex_br) ].

Ltac sok_in SOK :=
  store_ok_peel;
  first [ exact SOK
        | eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].
Ltac zand F D LEM EQ := stepiv F D (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite LEM; unorm; rewrite EQ; reflexivity).
Ltac vfin := rewrite ?alu_sltu, ?alu_and; rewrite ?zbv_snez by lia; first [ reflexivity | (apply bv_eq; reflexivity) | (f_equal; lia) ].

Definition PC_pixCountPixels : Z := 0x7e6fc.

(* [comment removed for export] *)
Definition FCP (m : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m
    (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret))
    (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
    (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9)))
    (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (getr regs 18)))
    (Z_to_bv 64 (s - 40)) (word_to_le_bytes 8 (getr regs 19)))
    (Z_to_bv 64 (s - 48)) (word_to_le_bytes 8 (getr regs 20)))
    (Z_to_bv 64 (s - 56)) (word_to_le_bytes 8 (getr regs 21)))
    (Z_to_bv 64 (s - 64)) (word_to_le_bytes 8 (getr regs 22)))
    (Z_to_bv 64 (s - 72)) (word_to_le_bytes 8 (getr regs 23)))
    (Z_to_bv 64 (s - 80)) (word_to_le_bytes 8 (getr regs 24)))
    (Z_to_bv 64 (s - 88)) (word_to_le_bytes 8 (getr regs 25)))
    (Z_to_bv 64 (s - 96)) (word_to_le_bytes 8 (getr regs 26)).
(* [comment removed for export] *)
Definition MCP_A (m : word -> option byte) (s pc : Z) (ret : word) (regs : bvmap 5 word) : word -> option byte :=
  wbytes (FCP m s ret regs) (Z_to_bv 64 pc) (word_to_le_bytes 4 (Z_to_bv 64 0)).
Definition pop8 (k : Z) : Z :=
  k mod 2 + (k / 2) mod 2 + (k / 4) mod 2 + (k / 8) mod 2 + (k / 16) mod 2 + (k / 32) mod 2 + (k / 64) mod 2 + k / 128.

Lemma z256 : forall f : Z -> bool, forallb f (map Z.of_nat (seq 0 256)) = true -> forall k : Z, (0 <= k < 256)%Z -> f k = true.
Proof.
  intros f H k Hk. rewrite forallb_forall in H. apply H. apply in_map_iff. exists (Z.to_nat k).
  split; [apply Z2Nat.id; lia | apply in_seq; lia].
Qed.
Ltac z256_bv k :=
  apply bv_eqb_eq;
  lazymatch goal with |- ?b = true =>
    let F := eval pattern k in b in
    lazymatch F with ?f k =>
      let H := fresh in
      assert (H : forallb f (map Z.of_nat (seq 0 256)) = true) by (vm_compute; reflexivity);
      exact (z256 f H k ltac:(lia)) end end.
Lemma pop8_bnd : forall k, (0 <= k < 256)%Z -> (0 <= pop8 k <= 8)%Z.
Proof.
  intros k Hk. pose proof (z256 (fun z => (0 <=? pop8 z) && (pop8 z <=? 8))%Z ltac:(vm_compute; reflexivity) k Hk) as H.
  apply andb_true_iff in H as [H1 H2]. apply Z.leb_le in H1, H2. lia.
Qed.
Lemma ext_sx4_small : forall z, (0 <= z < 2 ^ 31)%Z -> ext_val true 0 4 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold ext_val, ext_Z. rewrite u_Z2bv by lia. cbv beta iota zeta.
  change (8 * Z.of_nat 0)%Z with 0%Z. change (8 * Z.of_nat 4)%Z with 32%Z. change (8 * N.of_nat 4)%N with 32%N.
  rewrite Z.pow_0_r, Z.div_1_r, Z.mod_small by lia. rewrite sw32_eq, sw32_small by lia. reflexivity.
Qed.
Lemma sraw5 : forall w, (0 <= w < 2 ^ 31)%Z -> v_sraw (Z_to_bv 64 w) (Z_to_bv 64 5) = Z_to_bv 64 (w / 32).
Proof.
  intros w Hw. unfold v_sraw. rewrite !u_Z2bv by lia. rewrite sw32_eq. rewrite (sw32_eq w), (sw32_small w) by lia.
  change (5 mod 32)%Z with 5%Z. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 5)%Z with 32%Z.
  assert (0 <= w / 32 <= w)%Z by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  rewrite sw32_small by lia. reflexivity.
Qed.
Lemma and31 : forall w, (0 <= w < 2 ^ 64)%Z -> v_and (Z_to_bv 64 w) (Z_to_bv 64 31) = Z_to_bv 64 (w mod 32).
Proof.
  intros w Hw. unfold v_and. rewrite !u_Z2bv by lia. change 31%Z with (Z.ones 5). rewrite Z.land_ones by lia. reflexivity.
Qed.
Lemma not64 : forall t, (0 <= t < 2 ^ 64)%Z -> v_xor (Z_to_bv 64 t) (Z_to_bv 64 (-1)) = Z_to_bv 64 (2 ^ 64 - 1 - t).
Proof.
  intros t Ht. unfold v_xor. rewrite (u_Z2bv t) by lia.
  replace (bv_unsigned (Z_to_bv 64 (-1))) with (2 ^ 64 - 1)%Z by reflexivity. rewrite lxor_ones64B by lia. reflexivity.
Qed.
Lemma vand255 : forall w, (0 <= w < 2 ^ 64)%Z -> v_and (Z_to_bv 64 w) (Z_to_bv 64 255) = Z_to_bv 64 (w mod 256).
Proof.
  intros w Hw. unfold v_and. rewrite !u_Z2bv by lia. change 255%Z with (Z.ones 8). rewrite Z.land_ones by lia. reflexivity.
Qed.
Lemma land1020 : forall y, (0 <= y)%Z -> Z.land y 1020 = (4 * (Z.land y 1020 / 4))%Z /\ (0 <= Z.land y 1020 / 4 < 256)%Z.
Proof.
  intros y Hy.
  assert (H4 : (Z.land y 1020 mod 4 = 0)%Z).
  { change 4%Z with (2 ^ 2)%Z. rewrite <- Z.land_ones by lia. rewrite <- Z.land_assoc.
    change (Z.land 1020 (Z.ones 2)) with 0%Z. apply Z.land_0_r. }
  assert (H10 : (Z.land y 1020 < 1024)%Z).
  { assert (E : Z.land y 1020 = Z.land (Z.land y 1020) (Z.ones 10)).
    { rewrite <- Z.land_assoc. change (Z.land 1020 (Z.ones 10)) with 1020%Z. reflexivity. }
    rewrite E, Z.land_ones by lia. pose proof (Z.mod_pos_bound (Z.land y 1020) (2 ^ 10) ltac:(lia)) as B.
    change (2 ^ 10)%Z with 1024%Z in *. lia. }
  pose proof (proj2 (Z.land_nonneg y 1020) (or_introl Hy)) as N.
  pose proof (Z.div_mod (Z.land y 1020) 4 ltac:(lia)) as D.
  rewrite H4, Z.add_0_r in D. split; [exact D | lia].
Qed.
Lemma vsrl_c : forall w k, (0 <= w < 2 ^ 64)%Z -> (0 <= k < 64)%Z -> v_srl (Z_to_bv 64 w) (Z_to_bv 64 k) = Z_to_bv 64 (w / 2 ^ k).
Proof.
  intros w k Hw Hk. unfold v_srl. rewrite !u_Z2bv by lia. rewrite (Z.mod_small k 64) by lia.
  rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.
Lemma ta12 : forall w k, (0 <= w < 2 ^ 64)%Z -> (0 <= k < 64)%Z ->
  v_and (v_srl (Z_to_bv 64 w) (Z_to_bv 64 k)) (Z_to_bv 64 1020) = Z_to_bv 64 (4 * (Z.land (w / 2 ^ k) 1020 / 4)).
Proof.
  intros w k Hw Hk. rewrite vsrl_c by lia.
  assert (P : (1 <= 2 ^ k)%Z) by (change 1%Z with (2 ^ 0)%Z; apply Z.pow_le_mono_r; lia).
  assert (Q : (0 <= w / 2 ^ k < 2 ^ 64)%Z) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; nia]).
  unfold v_and. rewrite !u_Z2bv by lia. destruct (land1020 (w / 2 ^ k) ltac:(lia)) as [E _]. rewrite <- E. reflexivity.
Qed.
Lemma ta3 : forall w, (0 <= w < 2 ^ 32)%Z -> v_srlw (Z_to_bv 64 w) (Z_to_bv 64 24) = Z_to_bv 64 (w / 2 ^ 24).
Proof.
  intros w Hw. unfold v_srlw. rewrite !u_Z2bv by lia. rewrite wrap32_small by lia. change (24 mod 32)%Z with 24%Z.
  rewrite Z.shiftr_div_pow2 by lia.
  assert (Q : (0 <= w / 2 ^ 24 < 256)%Z) by (change (2 ^ 24)%Z with 16777216%Z; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  rewrite sw32_eq, sw32_small by lia. reflexivity.
Qed.
Lemma ta3m : forall x, (0 <= x < 2 ^ 64)%Z -> v_srlw (Z_to_bv 64 x) (Z_to_bv 64 24) = Z_to_bv 64 (x mod 2 ^ 32 / 2 ^ 24).
Proof.
  intros x Hx. unfold v_srlw. rewrite !u_Z2bv by lia. unfold bv_wrap, bv_modulus. change (Z.of_N 32) with 32%Z.
  change (24 mod 32)%Z with 24%Z. rewrite Z.shiftr_div_pow2 by lia.
  pose proof (Z.mod_pos_bound x (2 ^ 32) ltac:(lia)) as M.
  assert (Q : (0 <= x mod 2 ^ 32 / 2 ^ 24 < 256)%Z)
    by (change (2 ^ 24)%Z with 16777216%Z; change (2 ^ 32)%Z with 4294967296%Z in *; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  rewrite sw32_eq, sw32_small by lia. reflexivity.
Qed.
Ltac addn := repeat first [ rewrite ex_ptr_val | rewrite zbv_add | rewrite w_addw | rewrite zbv_addw_small by lia ].
Ltac tabval :=
  rewrite bytes_le_to_Z_4 by (rewrite u_Z2bv by lia; lia); rewrite u_Z2bv by lia;
  unfold extz; cbv beta iota zeta; change (8 * N.of_nat 4)%N with 32%N; rewrite sw32_eq, sw32_small by lia; reflexivity.
Ltac tabrd R t :=
  exists (word_to_le_bytes 4 (Z_to_bv 64 t)); split;
  [ rewrite ?ext_val_zx_id by (rewrite ?u_Z2bv by lia; ex_pow2; lia);
    rewrite ?w_srlw, ?alu_srl, ?alu_and, ?m_mul;
    rewrite ?vand255, ?ta12, ?ta3 by lia;
    rewrite ?zbv_mul, ?ex_ptr_val, ?zbv_addi, ?Z.add_0_r; exact R
  | tabval ].
Ltac tabrdE R t HX :=
  exists (word_to_le_bytes 4 (Z_to_bv 64 t)); split;
  [ rewrite ?w_srlw, ?alu_srl, ?alu_and, ?m_mul; rewrite HX;
    rewrite ?vand255, ?ta12, ?ta3m by lia;
    rewrite ?zbv_mul, ?ex_ptr_val, ?zbv_addi, ?Z.add_0_r; exact R
  | tabval ].
Ltac eanorm := rewrite ?m_mul, ?zbv_mul, ?ex_ptr_val; rewrite ?u_Z2bv by lia.
(* [comment removed for export] *)
Definition DIMC (m : word -> option byte) (s : Z) (w h : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes m
    (Z_to_bv 64 (s - 100)) (word_to_le_bytes 4 (Z_to_bv 64 0)))
    (Z_to_bv 64 (s - 104)) (word_to_le_bytes 4 (Z_to_bv 64 0)))
    (Z_to_bv 64 (s - 100)) (word_to_le_bytes 4 (Z_to_bv 64 w)))
    (Z_to_bv 64 (s - 104)) (word_to_le_bytes 4 (Z_to_bv 64 h)).
Definition TAB8 (m : word -> option byte) (tab : Z) : Prop :=
  forall k : Z, (0 <= k < 256)%Z -> exists t : Z, (0 <= t <= 8)%Z /\ rdn SEGS m (Z_to_bv 64 (tab + 4 * k)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 t)).

Section Count.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V23Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Section Segs.
  Variable rom : word -> option byte.

  (* [comment removed for export] *)
  Lemma cp_A : forall regs m (s pixs pc : Z) (v : pixv) (ret : word),
    (128 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pixs)%Z -> PIXat m pixs v -> (pixs + 64 <= s - 112)%Z -> p_d v = 1%Z ->
    (s <= pc)%Z -> (pc + 4 < 2 ^ 64)%Z -> (pc mod 4 = 0)%Z -> (pixs mod 8 = 0)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 112)) 112 = true -> store_ok SEGS m (Z_to_bv 64 pc) 4 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pixs -> getr regs 11 = Z_to_bv 64 pc -> getr regs 12 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x7e6fc : word) m rom) (mkst regs' (0x10e6e0 : word) (MCP_A m s pc ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 112) /\ getr regs' 1 = Z_to_bv 64 0x7e778
      /\ getr regs' 10 = Z_to_bv 64 256 /\ getr regs' 11 = Z_to_bv 64 4
      /\ getr regs' 9 = Z_to_bv 64 pc /\ getr regs' 20 = Z_to_bv 64 pixs /\ getr regs' 8 = Z_to_bv 64 0
      /\ getr regs' 18 = Z_to_bv 64 0 /\ getr regs' 19 = Z_to_bv 64 256
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 18; 19; 20]%list) regs regs'.
  Proof.
    intros regs m s pixs pc v ret Hs Hs64 Hp1 PX Hpix Hd Hpc Hpc64 ALpc ALp SOK SOKc H2 H1 H10 H11 H12.
    pose proof (PIX_rd_d SEGS _ _ _ PX) as RD. rewrite Hd in RD.
    replace (0x7e6fc : word) with (Z_to_bv 64 0x7e6fc) by (apply bv_eq; reflexivity).
    replace (0x10e6e0 : word) with (Z_to_bv 64 0x10e6e0) by (apply bv_eq; reflexivity).
    ex_entry regs (@nil Z) HR.
    assert (HK : know_ok SEGS (ex_env regs []) m
                   [KWr (SA (EVar 2) (-112)) 112; KWr (SA (EVar 11) 0) 4;
                    KRange (EVar 2) 128 (2 ^ 64 - 1); KRange (EVar 10) 1 (2 ^ 64 - 177); KRange (EVar 11) 128 (2 ^ 64 - 5);
                    KAlign (EVar 11) 4; KAlign (EVar 10) 8;
                    KDisj (SA (EVar 10) 0) 64 (SA (EVar 2) (-112)) 112; KDisj (SA (EVar 10) 0) 64 (SA (EVar 11) 0) 4;
                    KWord (SA (EVar 10) 8) 4 (ELit 1)]%Z).
    { ex_know regs. all: match goal with |- ?g => fail 1 "LEFT:" g end. }
    ex_run 400%nat [0x10e6e0]%Z (SCR [] [] []) HR HK R' HR' Hms.
    all: cycle 1.
    { exists R'. split.
      - unfold MCP_A, FCP. subst ret. ex_mem regs Hms.
      - repeat split; try (ex_reg regs HR'). ex_agree HR HR'. }
    all: match goal with |- ?g => fail 1 "SIDE:" g end.
  Qed.

  Lemma cp_An : forall regs m (s pc : Z) (ret : word),
    (128 <= s)%Z -> (s < 2 ^ 64)%Z -> (s <= pc)%Z -> (pc + 4 < 2 ^ 64)%Z -> (pc mod 4 = 0)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 112)) 112 = true -> store_ok SEGS m (Z_to_bv 64 pc) 4 = true ->
    rdn SEGS (MCP_A m s pc ret regs) (Z_to_bv 64 0x126a70) 8 = Some (Z_to_le_bytes 8 0x127c60) ->
    rdn SEGS (MCP_A m s pc ret regs) (Z_to_bv 64 0x127c60) 4 = Some (Z_to_le_bytes 4 3) ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 0 -> getr regs 11 = Z_to_bv 64 pc ->
    exists regs',
      msteps SEGS (mkst regs (0x7e6fc : word) m rom) (mkst regs' (0x63670 : word) (MCP_A m s pc ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret
      /\ getr regs' 10 = Z_to_bv 64 0x1189d /\ getr regs' 11 = Z_to_bv 64 0x1629e /\ getr regs' 12 = Z_to_bv 64 1
      /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9 /\ getr regs' 18 = getr regs 18 /\ getr regs' 19 = getr regs 19
      /\ getr regs' 20 = getr regs 20 /\ getr regs' 21 = getr regs 21 /\ getr regs' 22 = getr regs 22 /\ getr regs' 23 = getr regs 23
      /\ getr regs' 24 = getr regs 24 /\ getr regs' 25 = getr regs 25 /\ getr regs' 26 = getr regs 26
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12; 18; 19; 20; 21; 22; 23; 24; 25; 26]%list) regs regs'.
  Proof.
    intros regs m s pc ret Hs Hs64 Hpc Hpc64 ALpc SOK SOKc Rg Rs H2 H1 H10 H11.
    eexists. split.
    - zv F_7e6fc D_7e6fc (Z_to_bv 64 (s - 112)).
      stepST F_7e700 D_7e700 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_7e704 D_7e704 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_7e708 D_7e708 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepST F_7e70c D_7e70c (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
      stepST F_7e710 D_7e710 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
      stepST F_7e714 D_7e714 (Z_to_bv 64 (s - 48)) (getr regs 20) ltac:(sok_in SOK).
      stepST F_7e718 D_7e718 (Z_to_bv 64 (s - 56)) (getr regs 21) ltac:(sok_in SOK).
      stepST F_7e71c D_7e71c (Z_to_bv 64 (s - 64)) (getr regs 22) ltac:(sok_in SOK).
      stepST F_7e720 D_7e720 (Z_to_bv 64 (s - 72)) (getr regs 23) ltac:(sok_in SOK).
      stepST F_7e724 D_7e724 (Z_to_bv 64 (s - 80)) (getr regs 24) ltac:(sok_in SOK).
      stepST F_7e728 D_7e728 (Z_to_bv 64 (s - 88)) (getr regs 25) ltac:(sok_in SOK).
      stepST F_7e72c D_7e72c (Z_to_bv 64 (s - 96)) (getr regs 26) ltac:(sok_in SOK).
      fold (FCP m s ret regs).
      stepb_ft F_7e730 D_7e730 ltac:(condZ).
      sn F_7e734 D_7e734. sn F_7e738 D_7e738.
      zand F_7e73c D_7e73c andi_3 ALpc.
      stepb_ft F_7e740 D_7e740 ltac:(condZ).
      stepST F_7e744 D_7e744 (Z_to_bv 64 pc) (Z_to_bv 64 0) ltac:(sok_in SOKc).
      fold (MCP_A m s pc ret regs).
      stepb_tk F_7e748 D_7e748 ltac:(condZ).
      sn F_7eab0 D_7eab0.
      stepLD F_7eab4 D_7eab4 (Z_to_le_bytes 8 0x127c60) (Z_to_bv 64 0x127c60) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
      stepLD F_7eab8 D_7eab8 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; rewrite ?Z.add_0_r; exact Rs) ltac:(apply lez4; lia).
      sn F_7eabc D_7eabc. stepb_ft F_7eac0 D_7eac0 ltac:(condZ).
      sn F_7eac4 D_7eac4. sn F_7eac8 D_7eac8. sn F_7eacc D_7eacc. sn F_7ead0 D_7ead0.
      stepj F_7ead4 D_7ead4.
      sn F_7eafc D_7eafc. unfold MCP_A, FCP.
      stepLD8 F_7eb00 D_7eb00 ret. stepLD8 F_7eb04 D_7eb04 (getr regs 8). stepLD8 F_7eb08 D_7eb08 (getr regs 9).
      stepLD8 F_7eb0c D_7eb0c (getr regs 18). stepLD8 F_7eb10 D_7eb10 (getr regs 19). stepLD8 F_7eb14 D_7eb14 (getr regs 20).
      stepLD8 F_7eb18 D_7eb18 (getr regs 21). stepLD8 F_7eb1c D_7eb1c (getr regs 22). stepLD8 F_7eb20 D_7eb20 (getr regs 23).
      stepLD8 F_7eb24 D_7eb24 (getr regs 24). stepLD8 F_7eb28 D_7eb28 (getr regs 25). stepLD8 F_7eb2c D_7eb2c (getr regs 26).
      zv F_7eb30 D_7eb30 (Z_to_bv 64 s).
      stepj F_7eb34 D_7eb34.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  Lemma cp_T0 : forall regs m (tab : Z), (4096 <= tab)%Z -> (tab + 1024 < 2 ^ 64)%Z -> (tab mod 4 = 0)%Z -> getr regs 10 = Z_to_bv 64 tab ->
    exists regs',
      msteps SEGS (mkst regs (0x7e778 : word) m rom) (mkst regs' (0x7e798 : word) m rom)
      /\ getr regs' 18 = Z_to_bv 64 tab /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 11 = Z_to_bv 64 1 /\ getr regs' 12 = Z_to_bv 64 1
      /\ getr regs' 13 = Z_to_bv 64 tab /\ getr regs' 14 = Z_to_bv 64 tab
      /\ regs_agree (fun r => In r [10; 11; 12; 13; 14; 18]%list) regs regs'.
  Proof.
    intros regs m tab Ht Ht2 ALt H10.
    replace (0x7e778 : word) with (Z_to_bv 64 0x7e778) by (apply bv_eq; reflexivity).
    replace (0x7e798 : word) with (Z_to_bv 64 0x7e798) by (apply bv_eq; reflexivity).
    ex_entry regs (@nil Z) HR.
    assert (HK : know_ok SEGS (ex_env regs []) m [KRange (EVar 10) 4096 (2 ^ 64 - 1025); KAlign (EVar 10) 4]%Z).
    { ex_know regs. all: match goal with |- ?g => fail 1 "LEFT:" g end. }
    ex_run 100%nat [0x7e798]%Z (SCR [] [] []) HR HK R' HR' Hms.
    all: cycle 1.
    { exists R'. split; [exact Hms | repeat split; try (ex_reg regs HR'); try vfin; ex_agree HR HR']. }
    all: match goal with |- ?g => fail 1 "SIDE:" g end.
  Qed.

  Lemma cp_T : forall regs m (tab k : Z), (0 <= k < 256)%Z -> (4096 <= tab)%Z -> (tab + 1024 < 2 ^ 64)%Z -> (tab mod 4 = 0)%Z ->
    store_ok SEGS m (Z_to_bv 64 (tab + 4 * k)) 4 = true ->
    getr regs 18 = Z_to_bv 64 tab -> getr regs 11 = Z_to_bv 64 1 -> getr regs 12 = Z_to_bv 64 1 -> getr regs 10 = Z_to_bv 64 k ->
    getr regs 13 = Z_to_bv 64 (tab + 4 * k) -> getr regs 14 = Z_to_bv 64 (tab + 4 * k) -> getr regs 19 = Z_to_bv 64 (256 - k) ->
    exists regs' (tv : Z), (0 <= tv <= 8)%Z /\
      msteps SEGS (mkst regs (0x7e798 : word) m rom)
        (mkst regs' (0x7e814 : word) (wbytes m (Z_to_bv 64 (tab + 4 * k)) (word_to_le_bytes 4 (Z_to_bv 64 tv))) rom)
      /\ getr regs' 10 = Z_to_bv 64 (k + 1) /\ getr regs' 13 = Z_to_bv 64 (tab + 4 * (k + 1)) /\ getr regs' 14 = Z_to_bv 64 (tab + 4 * (k + 1))
      /\ getr regs' 19 = Z_to_bv 64 (256 - (k + 1))
      /\ regs_agree (fun r => In r [5; 6; 7; 10; 13; 14; 15; 16; 17; 19; 28; 29]%list) regs regs'.
  Proof.
    intros regs m tab k Hk Ht Ht2 ALt SOK H18 H11 H12 H10 H13 H14 H19.
    replace (0x7e798 : word) with (Z_to_bv 64 0x7e798) by (apply bv_eq; reflexivity).
    replace (0x7e814 : word) with (Z_to_bv 64 0x7e814) by (apply bv_eq; reflexivity).
    ex_entry regs (@nil Z) HR.
    assert (HK : know_ok SEGS (ex_env regs []) m
                   [KWr (SA (EVar 13) 0) 4;
                    KRange (EVar 18) 4096 (2 ^ 64 - 1025); KAlign (EVar 18) 4; KRange (EVar 11) 1 1; KRange (EVar 12) 1 1;
                    KRange (EVar 10) 0 255; KRange (EVar 13) 4096 (2 ^ 64 - 5); KRange (EVar 14) 4096 (2 ^ 64 - 5);
                    KRange (EVar 19) 1 256]%Z).
    { ex_know regs. all: match goal with |- ?g => fail 1 "LEFT:" g end. }
    ex_run 200%nat [0x7e814]%Z (SCR [false] [] []) HR HK R' HR' Hms.
    all: cycle 1.
    { exists R', (pop8 k). split; [| split].
      - apply pop8_bnd; lia.
      - eapply ex_msteps_mem; [exact Hms |]. cbn [mem_denot s_log e_addr e_width e_val].
        apply ex_wbytes_eq; [reflexivity | ex_addr_eq regs |].
        apply (f_equal (fun w => word_to_le_bytes 4 w)). symmetry.
        ex_unfoldE; cbn [edenot ev ex_envL vals_ev map app ex_regs_list nth Nat.add]. rewrite H10.
        z256_bv k.
      - repeat split; try (ex_reg regs HR'). ex_agree HR HR'. }
    all: match goal with |- ?g => fail 1 "SIDE:" g end.
  Qed.

  Lemma cp_Tn : forall regs m (n : Z), (1 <= n < 2 ^ 64)%Z -> getr regs 19 = Z_to_bv 64 n ->
    msteps SEGS (mkst regs (0x7e814 : word) m rom) (mkst regs (0x7e798 : word) m rom).
  Proof.
    intros regs m n Hn H19.
    stepb_tk F_7e814 D_7e814 ltac:(condZ).
    apply mst_refl.
  Qed.

  Lemma cp_Tx : forall regs m, getr regs 19 = Z_to_bv 64 0 ->
    msteps SEGS (mkst regs (0x7e814 : word) m rom) (mkst regs (0x7e818 : word) m rom).
  Proof.
    intros regs m H19.
    stepb_ft F_7e814 D_7e814 ltac:(condZ).
    apply mst_refl.
  Qed.

  Lemma cp_B : forall regs m (s pixs tab : Z) (v : pixv),
    (128 <= s)%Z -> (s < 2 ^ 64)%Z -> (s mod 16 = 0)%Z -> (1 <= pixs)%Z -> PIXat m pixs v -> (pixs + 64 <= s - 112)%Z -> (pixs mod 8 = 0)%Z ->
    (1 <= p_w v < 2 ^ 31)%Z -> (1 <= p_h v < 2 ^ 31)%Z -> (1 <= p_wpl v < 2 ^ 24)%Z ->
    (4096 <= p_data v < 2 ^ 64)%Z -> (p_data v mod 4 = 0)%Z -> (4096 <= tab)%Z -> (tab + 1024 < 2 ^ 64)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 112)) 112 = true ->
    getr regs 2 = Z_to_bv 64 (s - 112) -> getr regs 20 = Z_to_bv 64 pixs -> getr regs 18 = Z_to_bv 64 tab ->
    exists regs',
      msteps SEGS (mkst regs (0x7e818 : word) m rom) (mkst regs' (0x7e884 : word) (DIMC m s (p_w v) (p_h v)) rom)
      /\ getr regs' 10 = Z_to_bv 64 (p_data v) /\ getr regs' 29 = Z_to_bv 64 (p_data v)
      /\ getr regs' 19 = Z_to_bv 64 (p_wpl v) /\ getr regs' 11 = Z_to_bv 64 (p_h v)
      /\ getr regs' 12 = Z_to_bv 64 0 /\ getr regs' 13 = Z_to_bv 64 0
      /\ getr regs' 5 = Z_to_bv 64 (p_w v / 32) /\ getr regs' 7 = Z_to_bv 64 (p_w v / 32) /\ getr regs' 17 = Z_to_bv 64 (p_w v mod 32)
      /\ getr regs' 14 = Z_to_bv 64 (2 ^ 64 - 1 - tab) /\ getr regs' 15 = Z_to_bv 64 (4 * p_wpl v)
      /\ getr regs' 16 = Z_to_bv 64 0 /\ getr regs' 28 = Z_to_bv 64 1
      /\ regs_agree (fun r => In r [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 19; 28; 29]%list) regs regs'.
  Proof.
    intros regs m s pixs tab v Hs Hs64 ALs Hp1 PX Hpix ALp Hw Hh Hwpl Hd ALd Ht Ht2 SOK H2 H20 H18.
    pose proof (PIX_rd_w SEGS _ _ _ PX) as RW. pose proof (PIX_rd_h SEGS _ _ _ PX) as RH.
    pose proof (PIX_rd_wpl SEGS _ _ _ PX) as RWPL. pose proof (PIX_rd_data SEGS _ _ _ PX) as RDATA.
    assert (ALs4 : ((s - 112) mod 4 = 0)%Z) by (apply mod0_sub; [lia | apply mod16_to4; exact ALs | reflexivity]).
    replace (0x7e818 : word) with (Z_to_bv 64 0x7e818) by (apply bv_eq; reflexivity).
    replace (0x7e884 : word) with (Z_to_bv 64 0x7e884) by (apply bv_eq; reflexivity).
    ex_entry regs [p_w v; p_h v; p_wpl v; p_data v] HR.
    assert (HK : know_ok SEGS (ex_env regs [p_w v; p_h v; p_wpl v; p_data v]) m
                   [KWr (SA (EVar 2) 0) 112;
                    KRange (EVar 2) 16 (2 ^ 64 - 113); KAlign (EVar 2) 4;
                    KRange (EVar 20) 1 (2 ^ 64 - 177); KAlign (EVar 20) 8;
                    KRange (EVar 18) 4096 (2 ^ 64 - 1025);
                    KDisj (SA (EVar 20) 0) 64 (SA (EVar 2) 0) 112;
                    KWord (SA (EVar 20) 0) 4 (EVar 32); KWord (SA (EVar 20) 4) 4 (EVar 33);
                    KWord (SA (EVar 20) 16) 4 (EVar 34); KWord (SA (EVar 20) 56) 8 (EVar 35);
                    KRange (EVar 32) 1 (2 ^ 31 - 1); KRange (EVar 33) 1 (2 ^ 31 - 1); KRange (EVar 34) 1 (2 ^ 24 - 1);
                    KRange (EVar 35) 4096 (2 ^ 64 - 1); KAlign (EVar 35) 4]%Z).
    { ex_know regs. all: match goal with |- ?g => fail 1 "LEFT:" g end. }
    ex_run 400%nat [0x7e884]%Z (SCR [] [] []) HR HK R' HR' Hms.
    all: cycle 1.
    { exists R'. split.
      - unfold DIMC. ex_mem2 regs Hms.
      - repeat split; try (exB_reg regs HR'); try vfin.
        all: try (rewrite !ext_sx4_small by lia; reflexivity).
        all: try (apply sraw5; lia).
        all: try (apply and31; lia).
        all: try (apply not64; lia).
        all: ex_agree HR HR'. }
    all: match goal with |- ?g => fail 1 "SIDE:" g end.
  Qed.

  Lemma cp_Rw : forall regs m (fw line : Z), (1 <= fw < 2 ^ 26)%Z -> (4096 <= line < 2 ^ 64)%Z ->
    getr regs 5 = Z_to_bv 64 fw -> getr regs 7 = Z_to_bv 64 fw -> getr regs 10 = Z_to_bv 64 line -> getr regs 29 = Z_to_bv 64 line ->
    getr regs 28 = Z_to_bv 64 1 ->
    exists regs',
      msteps SEGS (mkst regs (0x7e884 : word) m rom) (mkst regs' (0x7e8b0 : word) m rom)
      /\ getr regs' 30 = Z_to_bv 64 1 /\ getr regs' 31 = Z_to_bv 64 1 /\ getr regs' 20 = Z_to_bv 64 fw
      /\ getr regs' 21 = Z_to_bv 64 line /\ getr regs' 22 = Z_to_bv 64 line
      /\ regs_agree (fun r => In r [20; 21; 22; 30; 31]%list) regs regs'.
  Proof.
    intros regs m fw line Hfw Hl H5 H7 H10 H29 H28.
    replace (0x7e884 : word) with (Z_to_bv 64 0x7e884) by (apply bv_eq; reflexivity).
    replace (0x7e8b0 : word) with (Z_to_bv 64 0x7e8b0) by (apply bv_eq; reflexivity).
    ex_entry regs (@nil Z) HR.
    assert (HK : know_ok SEGS (ex_env regs []) m
                   [KRange (EVar 5) 1 (2 ^ 26 - 1); KRange (EVar 7) 1 (2 ^ 26 - 1); KRange (EVar 10) 4096 (2 ^ 64 - 1);
                    KRange (EVar 29) 4096 (2 ^ 64 - 1); KRange (EVar 28) 1 1]%Z).
    { ex_know regs. all: match goal with |- ?g => fail 1 "LEFT:" g end. }
    ex_run 100%nat [0x7e8b0]%Z (SCR [] [] []) HR HK R' HR' Hms.
    all: cycle 1.
    { exists R'. split; [exact Hms | repeat split; try (ex_reg regs HR'); try vfin; ex_agree HR HR']. }
    all: match goal with |- ?g => fail 1 "SIDE:" g end.
  Qed.

  Lemma cp_R0 : forall regs m (eb line : Z), (1 <= eb < 32)%Z -> (4096 <= line < 2 ^ 64)%Z ->
    getr regs 5 = Z_to_bv 64 0 -> getr regs 17 = Z_to_bv 64 eb -> getr regs 10 = Z_to_bv 64 line ->
    exists regs',
      msteps SEGS (mkst regs (0x7e884 : word) m rom) (mkst regs' (0x7e994 : word) m rom)
      /\ getr regs' 30 = Z_to_bv 64 1 /\ getr regs' 31 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [30; 31]%list) regs regs'.
  Proof.
    intros regs m eb line Heb Hl H5 H17 H10.
    replace (0x7e884 : word) with (Z_to_bv 64 0x7e884) by (apply bv_eq; reflexivity).
    replace (0x7e994 : word) with (Z_to_bv 64 0x7e994) by (apply bv_eq; reflexivity).
    ex_entry regs (@nil Z) HR.
    assert (HK : know_ok SEGS (ex_env regs []) m [KRange (EVar 5) 0 0; KRange (EVar 17) 1 31; KRange (EVar 10) 4096 (2 ^ 64 - 1)]%Z).
    { ex_know regs. all: match goal with |- ?g => fail 1 "LEFT:" g end. }
    ex_run 100%nat [0x7e994]%Z (SCR [] [] []) HR HK R' HR' Hms.
    all: cycle 1.
    { exists R'. split; [exact Hms | repeat split; try (ex_reg regs HR'); try vfin; ex_agree HR HR']. }
    all: match goal with |- ?g => fail 1 "SIDE:" g end.
  Qed.

  Lemma cp_Wn : forall regs m (p n : Z), (0 <= p)%Z -> (p + 4 < 2 ^ 64)%Z -> (2 <= n < 2 ^ 26)%Z ->
    getr regs 22 = Z_to_bv 64 p -> getr regs 21 = Z_to_bv 64 p -> getr regs 20 = Z_to_bv 64 n ->
    exists regs',
      msteps SEGS (mkst regs (0x7e8a0 : word) m rom) (mkst regs' (0x7e8b0 : word) m rom)
      /\ getr regs' 22 = Z_to_bv 64 (p + 4) /\ getr regs' 21 = Z_to_bv 64 (p + 4) /\ getr regs' 20 = Z_to_bv 64 (n - 1)
      /\ regs_agree (fun r => In r [20; 21; 22]%list) regs regs'.
  Proof.
    intros regs m p n Hp Hp4 Hn H22 H21 H20.
    replace (0x7e8a0 : word) with (Z_to_bv 64 0x7e8a0) by (apply bv_eq; reflexivity).
    replace (0x7e8b0 : word) with (Z_to_bv 64 0x7e8b0) by (apply bv_eq; reflexivity).
    ex_entry regs (@nil Z) HR.
    assert (HK : know_ok SEGS (ex_env regs []) m
                   [KRange (EVar 20) 2 (2 ^ 26 - 1); KRange (EVar 21) 0 (2 ^ 64 - 5); KRange (EVar 22) 0 (2 ^ 64 - 5)]%Z).
    { ex_know regs. all: match goal with |- ?g => fail 1 "LEFT:" g end. }
    ex_run 100%nat [0x7e8b0]%Z (SCR [] [] []) HR HK R' HR' Hms.
    all: cycle 1.
    { exists R'. split; [exact Hms | repeat split; try (ex_reg regs HR'); try vfin; ex_agree HR HR']. }
    all: match goal with |- ?g => fail 1 "SIDE:" g end.
  Qed.

  Lemma cp_Wx : forall regs m (p : Z), (0 <= p)%Z -> (p + 4 < 2 ^ 64)%Z ->
    getr regs 22 = Z_to_bv 64 p -> getr regs 21 = Z_to_bv 64 p -> getr regs 20 = Z_to_bv 64 1 ->
    exists regs',
      msteps SEGS (mkst regs (0x7e8a0 : word) m rom) (mkst regs' (0x7e980 : word) m rom)
      /\ regs_agree (fun r => In r [20; 21; 22]%list) regs regs'.
  Proof.
    intros regs m p Hp Hp4 H22 H21 H20.
    replace (0x7e8a0 : word) with (Z_to_bv 64 0x7e8a0) by (apply bv_eq; reflexivity).
    replace (0x7e980 : word) with (Z_to_bv 64 0x7e980) by (apply bv_eq; reflexivity).
    ex_entry regs (@nil Z) HR.
    assert (HK : know_ok SEGS (ex_env regs []) m
                   [KRange (EVar 20) 1 1; KRange (EVar 21) 0 (2 ^ 64 - 5); KRange (EVar 22) 0 (2 ^ 64 - 5)]%Z).
    { ex_know regs. all: match goal with |- ?g => fail 1 "LEFT:" g end. }
    ex_run 100%nat [0x7e980]%Z (SCR [] [] []) HR HK R' HR' Hms.
    all: cycle 1.
    { exists R'. split; [exact Hms | ex_agree HR HR']. }
    all: match goal with |- ?g => fail 1 "SIDE:" g end.
  Qed.

  Lemma cp_Xe : forall regs m (fw eb : Z), (1 <= eb < 32)%Z -> getr regs 5 = Z_to_bv 64 fw -> getr regs 17 = Z_to_bv 64 eb ->
    exists regs',
      msteps SEGS (mkst regs (0x7e980 : word) m rom) (mkst regs' (0x7e994 : word) m rom)
      /\ getr regs' 31 = Z_to_bv 64 fw /\ regs_agree (fun r => In r [31]%list) regs regs'.
  Proof.
    intros regs m fw eb Heb H5 H17.
    replace (0x7e980 : word) with (Z_to_bv 64 0x7e980) by (apply bv_eq; reflexivity).
    replace (0x7e994 : word) with (Z_to_bv 64 0x7e994) by (apply bv_eq; reflexivity).
    ex_entry regs (@nil Z) HR.
    assert (HK : know_ok SEGS (ex_env regs []) m [KRange (EVar 17) 1 31]%Z).
    { ex_know regs. all: match goal with |- ?g => fail 1 "LEFT:" g end. }
    ex_run 100%nat [0x7e994]%Z (SCR [] [] []) HR HK R' HR' Hms.
    all: cycle 1.
    { exists R'. split; [exact Hms | repeat split; try (ex_reg regs HR'); ex_agree HR HR']. }
    all: match goal with |- ?g => fail 1 "SIDE:" g end.
  Qed.

  Lemma cp_Xn : forall regs m, getr regs 17 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x7e980 : word) m rom) (mkst regs' (0x7ea70 : word) m rom)
      /\ regs_agree (fun r => In r [31]%list) regs regs'.
  Proof.
    intros regs m H17.
    replace (0x7e980 : word) with (Z_to_bv 64 0x7e980) by (apply bv_eq; reflexivity).
    replace (0x7ea70 : word) with (Z_to_bv 64 0x7ea70) by (apply bv_eq; reflexivity).
    ex_entry regs (@nil Z) HR.
    assert (HK : know_ok SEGS (ex_env regs []) m [KRange (EVar 17) 0 0]%Z).
    { ex_know regs. all: match goal with |- ?g => fail 1 "LEFT:" g end. }
    ex_run 100%nat [0x7ea70]%Z (SCR [] [] []) HR HK R' HR' Hms.
    all: cycle 1.
    { exists R'. split; [exact Hms | ex_agree HR HR']. }
    all: match goal with |- ?g => fail 1 "SIDE:" g end.
  Qed.

  #[local] Ltac exB_sc_hook ::=
    lazymatch goal with
    | |- exists _, _ => fail
    | _ => repeat rewrite ext_val_sx_id by (first [ lia | (rewrite ?u_Z2bv by lia; ex_pow2; lia) ]); addn; ex_br
    end.

  (* [comment removed for export] *)
  Lemma cp_Wd : forall regs m (line p tab c : Z) (bs : list byte),
    (4096 <= line <= p)%Z -> (p + 4 < 2 ^ 64)%Z -> (p mod 4 = 0)%Z ->
    (4096 <= tab)%Z -> (tab + 1024 < 2 ^ 64)%Z -> (tab mod 4 = 0)%Z -> (0 <= c)%Z -> (c + 32 < 2 ^ 31)%Z ->
    rdn SEGS m (Z_to_bv 64 p) 4 = Some bs -> TAB8 m tab ->
    getr regs 10 = Z_to_bv 64 line -> getr regs 22 = Z_to_bv 64 p -> getr regs 21 = Z_to_bv 64 p -> getr regs 18 = Z_to_bv 64 tab ->
    getr regs 14 = Z_to_bv 64 (2 ^ 64 - 1 - tab) -> getr regs 12 = Z_to_bv 64 c -> getr regs 30 = Z_to_bv 64 1 -> getr regs 31 = Z_to_bv 64 1 ->
    exists regs' (d : Z), (0 <= d <= 32)%Z /\
      msteps SEGS (mkst regs (0x7e8b0 : word) m rom) (mkst regs' (0x7e8a0 : word) m rom)
      /\ getr regs' 12 = Z_to_bv 64 (c + d)
      /\ regs_agree (fun r => In r [12; 23; 24; 25; 26]%list) regs regs'.
  Proof.
    intros regs m line p tab c bs Hp Hp4 ALp Ht Ht2 ALt Hc Hc2 RB TB H10 H22 H21 H18 H14 H12 H30 H31.
    pose proof (rdn_length _ _ _ _ _ RB) as LB.
    pose proof (bytes_le_to_Z_nonneg bs) as W0. pose proof (bytes_le_to_Z_bound bs) as W1. rewrite LB in W1.
    change (8 * Z.of_nat 4)%Z with 32%Z in W1.
    assert (RW : rdn SEGS m (Z_to_bv 64 (p + 0)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 (bytes_le_to_Z bs)))).
    { rewrite Z.add_0_r, word_to_le_bytes_of_lez by (first [exact LB | lia]). exact RB. }
    clear RB. revert RW W0 W1. generalize (bytes_le_to_Z bs) as wv. intros wv RW W0 W1.
    remember (2 ^ 64 - 1 - tab)%Z as ntab eqn:Entab.
    replace (0x7e8b0 : word) with (Z_to_bv 64 0x7e8b0) by (apply bv_eq; reflexivity).
    replace (0x7e8a0 : word) with (Z_to_bv 64 0x7e8a0) by (apply bv_eq; reflexivity).
    destruct (Z.eq_dec wv 0) as [Hz | Hnz].
    - subst wv. ex_entry regs [p] HR.
      assert (HK : know_ok SEGS (ex_env regs [p]) m
                     [KRange (EVar 32) 4096 (2 ^ 64 - 5); KAlign (EVar 32) 4; KWord (SA (EVar 32) 0) 4 (ELit 0)]%Z).
      { ex_know regs. all: match goal with |- ?g => fail 1 "LEFT:" g end. }
      ex_run 100%nat [0x7e8a0]%Z (SCR [false] [] []) HR HK R' HR' Hms.
      all: cycle 1.
      { exists R', 0%Z. split; [lia | split; [exact Hms | split; [ex_reg regs HR'; try (rewrite Z.add_0_r; exact H12) | ex_agree HR HR']]]. }
      all: match goal with |- ?g => fail 1 "SIDE:" g end.
    - destruct (TB (wv mod 256) ltac:(apply Z.mod_pos_bound; lia)) as (t0 & T0 & R0).
      destruct (TB (Z.land (wv / 2 ^ 6) 1020 / 4) (proj2 (land1020 (wv / 2 ^ 6) ltac:(apply Z.div_pos; lia)))) as (t1 & T1 & R1).
      destruct (TB (Z.land (wv / 2 ^ 14) 1020 / 4) (proj2 (land1020 (wv / 2 ^ 14) ltac:(apply Z.div_pos; lia)))) as (t2 & T2 & R2).
      destruct (TB (wv / 2 ^ 24) ltac:(change (2 ^ 24)%Z with 16777216%Z; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia])) as (t3 & T3 & R3).
      ex_entry regs [p; wv; t0; t1; t2; t3] HR.
      assert (HK : know_ok SEGS (ex_env regs [p; wv; t0; t1; t2; t3]) m
                     [KRange (EVar 32) 4096 (2 ^ 64 - 5); KAlign (EVar 32) 4;
                      KWord (SA (EVar 32) 0) 4 (EVar 33); KRange (EVar 33) 1 (2 ^ 32 - 1);
                      KRange (EVar 18) 4096 (2 ^ 64 - 1025); KAlign (EVar 18) 4; KRange (EVar 14) 1024 (2 ^ 64 - 4097);
                      KRange (EVar 12) 0 (2 ^ 31 - 33);
                      KRange (EVar 34) 0 8; KRange (EVar 35) 0 8; KRange (EVar 36) 0 8; KRange (EVar 37) 0 8]%Z).
      { ex_know regs. all: match goal with |- ?g => fail 1 "LEFT:" g end. }
      ex_run 300%nat [0x7e8a0]%Z (SCR [false; false; false; false; true] [EVar 34; EVar 35; EVar 36; EVar 37] []) HR HK R' HR' Hms.
      all: try (solve [addn; ex_br]).
      all: try (solve [tabrd R0 t0 | tabrd R1 t1 | tabrd R2 t2 | tabrd R3 t3]).
      all: match goal with |- exists _ _, _ => idtac | |- ?g => fail 1 "SIDE:" g end.
      exists R', (t0 + t1 + t2 + t3)%Z. split; [lia | split; [exact Hms | split; [ | ex_agree HR HR']]].
      ex_reg regs HR'. all: addn; f_equal; lia.
  Qed.

  Ltac eb_sc RB Hsv HX :=
    first [ (eanorm; lia)
          | (eanorm; ex_br)
          | (eanorm; rewrite ?alu_sltu, ?alu_xor; rewrite WalksLib.v_sltu_Z by lia; rewrite (proj2 (Z.ltb_ge _ 1)) by lia; reflexivity)
          | (rewrite alu_and, HX; ex_br)
          | (eexists; split; [eanorm; rewrite ?zbv_addi, ?Z.add_0_r; exact RB | rewrite Hsv; reflexivity]) ].

  (* [comment removed for export] *)
  Lemma cp_Eb : forall regs m (line fw tab c : Z) (bs : list byte),
    (4096 <= line)%Z -> (0 <= fw < 2 ^ 26)%Z -> (line + 4 * fw + 4 < 2 ^ 64)%Z -> (line mod 4 = 0)%Z ->
    (4096 <= tab)%Z -> (tab + 1024 < 2 ^ 64)%Z -> (tab mod 4 = 0)%Z -> (0 <= c)%Z -> (c + 32 < 2 ^ 31)%Z ->
    rdn SEGS m (Z_to_bv 64 (line + 4 * fw)) 4 = Some bs -> TAB8 m tab ->
    getr regs 10 = Z_to_bv 64 line -> getr regs 31 = Z_to_bv 64 fw -> getr regs 18 = Z_to_bv 64 tab ->
    getr regs 14 = Z_to_bv 64 (2 ^ 64 - 1 - tab) -> getr regs 12 = Z_to_bv 64 c -> getr regs 16 = Z_to_bv 64 0 ->
    getr regs 30 = Z_to_bv 64 1 ->
    exists regs' (d : Z), (0 <= d <= 32)%Z /\
      msteps SEGS (mkst regs (0x7e994 : word) m rom) (mkst regs' (0x7ea70 : word) m rom)
      /\ getr regs' 12 = Z_to_bv 64 (c + d)
      /\ regs_agree (fun r => In r [12; 20; 21; 22; 31]%list) regs regs'.
  Proof.
    intros regs m line fw tab c bs Hl Hfw Hl2 ALl Ht Ht2 ALt Hc Hc2 RB TB H10 H31 H18 H14 H12 H16 H30.
    remember (2 ^ 64 - 1 - tab)%Z as ntab eqn:Entab.
    remember (extz true 4 (bytes_le_to_Z bs)) as sv eqn:Hsv.
    remember (bv_unsigned (v_and (Z_to_bv 64 sv) (getr regs 6))) as x eqn:Ex.
    assert (HX : v_and (Z_to_bv 64 sv) (getr regs 6) = Z_to_bv 64 x) by (rewrite Ex; symmetry; apply Z_to_bv_bv_unsigned).
    assert (Xr : (0 <= x < 2 ^ 64)%Z)
      by (rewrite Ex; pose proof (bv_unsigned_in_range 64 (v_and (Z_to_bv 64 sv) (getr regs 6))) as Q; unfold bv_modulus in Q; exact Q).
    replace (0x7e994 : word) with (Z_to_bv 64 0x7e994) by (apply bv_eq; reflexivity).
    replace (0x7ea70 : word) with (Z_to_bv 64 0x7ea70) by (apply bv_eq; reflexivity).
    destruct (Z.eq_dec x 0) as [Hz | Hnz].
    - ex_entry regs [line; fw; sv] HR.
      assert (HK : know_ok SEGS (ex_env regs [line; fw; sv]) m
                     [KRange (EVar 32) 4096 (2 ^ 64 - 1); KAlign (EVar 32) 4; KRange (EVar 33) 0 (2 ^ 26 - 1)]%Z).
      { ex_know regs. all: match goal with |- ?g => fail 1 "LEFT:" g end. }
      ex_run 100%nat [0x7ea70]%Z (SCR [false; false; true] [EVar 34] []) HR HK R' HR' Hms.
      all: try (solve [eb_sc RB Hsv HX]).
      all: match goal with |- exists _ _, _ => idtac | |- ?g => fail 1 "SIDE:" g end.
      exists R', 0%Z. split; [lia | split; [exact Hms | split; [ex_reg regs HR'; try (rewrite Z.add_0_r; exact H12) | ex_agree HR HR']]].
    - destruct (TB (x mod 256) ltac:(apply Z.mod_pos_bound; lia)) as (t0 & T0 & R0).
      destruct (TB (Z.land (x / 2 ^ 6) 1020 / 4) (proj2 (land1020 (x / 2 ^ 6) ltac:(apply Z.div_pos; lia)))) as (t1 & T1 & R1).
      destruct (TB (Z.land (x / 2 ^ 14) 1020 / 4) (proj2 (land1020 (x / 2 ^ 14) ltac:(apply Z.div_pos; lia)))) as (t2 & T2 & R2).
      assert (K3 : (0 <= x mod 2 ^ 32 / 2 ^ 24 < 256)%Z)
        by (pose proof (Z.mod_pos_bound x (2 ^ 32) ltac:(lia)); change (2 ^ 24)%Z with 16777216%Z;
            change (2 ^ 32)%Z with 4294967296%Z in *; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
      destruct (TB (x mod 2 ^ 32 / 2 ^ 24) K3) as (t3 & T3 & R3).
      ex_entry regs [line; fw; sv; t0; t1; t2; t3] HR.
      assert (HK : know_ok SEGS (ex_env regs [line; fw; sv; t0; t1; t2; t3]) m
                     [KRange (EVar 32) 4096 (2 ^ 64 - 1); KAlign (EVar 32) 4; KRange (EVar 33) 0 (2 ^ 26 - 1);
                      KRange (EVar 18) 4096 (2 ^ 64 - 1025); KAlign (EVar 18) 4; KRange (EVar 14) 1024 (2 ^ 64 - 4097);
                      KRange (EVar 12) 0 (2 ^ 31 - 33);
                      KRange (EVar 35) 0 8; KRange (EVar 36) 0 8; KRange (EVar 37) 0 8; KRange (EVar 38) 0 8]%Z).
      { ex_know regs. all: match goal with |- ?g => fail 1 "LEFT:" g end. }
      ex_run 300%nat [0x7ea70]%Z (SCR [false; false; false; false; false; false; false; false] [EVar 34; EVar 35; EVar 36; EVar 37; EVar 38] []) HR HK R' HR' Hms.
      all: try (solve [addn; ex_br]).
      all: try (solve [eb_sc RB Hsv HX]).
      all: try (solve [tabrdE R0 t0 HX | tabrdE R1 t1 HX | tabrdE R2 t2 HX | tabrdE R3 t3 HX]).
      all: try (solve [rewrite ?w_srlw, ?alu_srl, ?alu_and, ?m_mul; rewrite HX; rewrite ?ta3m by lia; rewrite ?zbv_mul, ?ex_ptr_val;
                       rewrite ?u_Z2bv by lia; first [lia | ex_br]]).
      all: match goal with |- exists _ _, _ => idtac | |- ?g => fail 1 "SIDE:" g end.
      exists R', (t0 + t1 + t2 + t3)%Z. split; [lia | split; [exact Hms | split; [ | ex_agree HR HR']]].
      ex_reg regs HR'. all: addn; f_equal; lia.
  Qed.

  Ltac flagchk :=
    eanorm; rewrite ?alu_xor, ?alu_sltu, ?alu_slt; rewrite ?v_sltu_Z, ?v_slt_Z by lia;
    repeat (rewrite (proj2 (Z.ltb_ge _ _)) by lia); reflexivity.

  (* [comment removed for export] *)
  Lemma cp_Nn : forall regs m (i h wpl line : Z), (0 <= i)%Z -> (i + 1 < h)%Z -> (h < 2 ^ 31)%Z -> (1 <= wpl < 2 ^ 24)%Z ->
    (4096 <= line)%Z -> (line + 4 * wpl < 2 ^ 64)%Z ->
    getr regs 13 = Z_to_bv 64 i -> getr regs 11 = Z_to_bv 64 h ->
    getr regs 10 = Z_to_bv 64 line -> getr regs 29 = Z_to_bv 64 line -> getr regs 15 = Z_to_bv 64 (4 * wpl) -> getr regs 19 = Z_to_bv 64 wpl ->
    getr regs 30 = Z_to_bv 64 1 ->
    exists regs',
      msteps SEGS (mkst regs (0x7ea70 : word) m rom) (mkst regs' (0x7e884 : word) m rom)
      /\ getr regs' 13 = Z_to_bv 64 (i + 1) /\ getr regs' 10 = Z_to_bv 64 (line + 4 * wpl) /\ getr regs' 29 = Z_to_bv 64 (line + 4 * wpl)
      /\ regs_agree (fun r => In r [10; 13; 20; 29; 30; 31]%list) regs regs'.
  Proof.
    intros regs m i h wpl line Hi Hih Hh Hw Hl Hl2 H13 H11 H10 H29 H15 H19 H30.
    replace (0x7ea70 : word) with (Z_to_bv 64 0x7ea70) by (apply bv_eq; reflexivity).
    replace (0x7e884 : word) with (Z_to_bv 64 0x7e884) by (apply bv_eq; reflexivity).
    remember (4 * wpl)%Z as wb eqn:Ewb.
    ex_entry regs [line] HR.
    assert (HK : know_ok SEGS (ex_env regs [line]) m
                   [KRange (EVar 32) 4096 (2 ^ 64 - 1); KRange (EVar 13) 0 (2 ^ 31 - 3); KRange (EVar 11) 2 (2 ^ 31 - 1);
                    KRange (EVar 15) 4 (2 ^ 26 - 1); KRange (EVar 19) 1 (2 ^ 24 - 1)]%Z).
    { ex_know regs. all: match goal with |- ?g => fail 1 "LEFT:" g end. }
    ex_run 100%nat [0x7e884]%Z (SCR [false; false; true] [] []) HR HK R' HR' Hms.
    all: try (solve [flagchk]).
    all: match goal with |- exists _, _ => idtac | |- ?g => fail 1 "SIDE:" g end.
    exists R'. split; [exact Hms | repeat split; [ | | | ex_agree HR HR']].
    all: ex_reg regs HR'. all: addn; f_equal; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma cp_Nx : forall regs m (i wpl line pc tab c : Z), (0 <= i)%Z -> (i + 1 < 2 ^ 31)%Z -> (1 <= wpl < 2 ^ 24)%Z ->
    (4096 <= line)%Z -> (line + 4 * wpl < 2 ^ 64)%Z -> (0 <= pc)%Z -> (pc + 4 < 2 ^ 64)%Z -> (0 <= c < 2 ^ 31)%Z ->
    store_ok SEGS m (Z_to_bv 64 pc) 4 = true ->
    getr regs 13 = Z_to_bv 64 i -> getr regs 11 = Z_to_bv 64 (i + 1) ->
    getr regs 10 = Z_to_bv 64 line -> getr regs 29 = Z_to_bv 64 line -> getr regs 15 = Z_to_bv 64 (4 * wpl) -> getr regs 19 = Z_to_bv 64 wpl ->
    getr regs 30 = Z_to_bv 64 1 -> getr regs 9 = Z_to_bv 64 pc -> getr regs 8 = Z_to_bv 64 0 -> getr regs 18 = Z_to_bv 64 tab ->
    getr regs 12 = Z_to_bv 64 c ->
    exists regs',
      msteps SEGS (mkst regs (0x7ea70 : word) m rom)
        (mkst regs' (0x10e818 : word) (wbytes m (Z_to_bv 64 pc) (word_to_le_bytes 4 (Z_to_bv 64 c))) rom)
      /\ getr regs' 1 = Z_to_bv 64 0x7eb84 /\ getr regs' 10 = Z_to_bv 64 tab
      /\ regs_agree (fun r => In r [1; 10; 13; 20; 29; 30; 31]%list) regs regs'.
  Proof.
    intros regs m i wpl line pc tab c Hi Hi2 Hw Hl Hl2 Hpc Hpc2 Hc SOK H13 H11 H10 H29 H15 H19 H30 H9 H8 H18 H12.
    replace (0x7ea70 : word) with (Z_to_bv 64 0x7ea70) by (apply bv_eq; reflexivity).
    replace (0x10e818 : word) with (Z_to_bv 64 0x10e818) by (apply bv_eq; reflexivity).
    remember (4 * wpl)%Z as wb eqn:Ewb.
    remember (i + 1)%Z as h eqn:Eh.
    ex_entry regs [line] HR.
    assert (HK : know_ok SEGS (ex_env regs [line]) m
                   [KWr (SA (EVar 9) 0) 4; KRange (EVar 9) 0 (2 ^ 64 - 5);
                    KRange (EVar 32) 4096 (2 ^ 64 - 1); KRange (EVar 13) 0 (2 ^ 31 - 2); KRange (EVar 11) 1 (2 ^ 31 - 1);
                    KRange (EVar 15) 4 (2 ^ 26 - 1); KRange (EVar 19) 1 (2 ^ 24 - 1)]%Z).
    { ex_know regs. all: match goal with |- ?g => fail 1 "LEFT:" g end. }
    ex_run 100%nat [0x10e818]%Z (SCR [false; false; false] [] []) HR HK R' HR' Hms.
    all: try (solve [flagchk]).
    all: try (solve [addn; ex_br]).
    all: match goal with |- exists _, _ => idtac | |- ?g => fail 1 "SIDE:" g end.
    exists R'. split; [ex_mem regs Hms | repeat split; [ | | ex_agree HR HR']].
    all: ex_reg regs HR'.
  Qed.

  (* [comment removed for export] *)
  Lemma cp_F : forall regs m (s : Z) (ret s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v : word),
    (128 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret ->
    cellsZ m [(s - 8, ret); (s - 16, s0v); (s - 24, s1v); (s - 32, s2v); (s - 40, s3v); (s - 48, s4v);
              (s - 56, s5v); (s - 64, s6v); (s - 72, s7v); (s - 80, s8v); (s - 88, s9v); (s - 96, s10v)]%Z ->
    getr regs 2 = Z_to_bv 64 (s - 112) ->
    exists regs',
      msteps SEGS (mkst regs (0x7eb84 : word) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 0
      /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v /\ getr regs' 20 = s4v
      /\ getr regs' 21 = s5v /\ getr regs' 22 = s6v /\ getr regs' 23 = s7v /\ getr regs' 24 = s8v /\ getr regs' 25 = s9v
      /\ getr regs' 26 = s10v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 18; 19; 20; 21; 22; 23; 24; 25; 26]%list) regs regs'.
  Proof.
    intros regs m s ret s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v Hs Hs64 Hret
      (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & _) H2.
    eexists. split.
    - stepj F_7eb84 D_7eb84.
      sn F_7eaa8 D_7eaa8.
      stepj F_7eaac D_7eaac.
      stepLD F_7eb3c D_7eb3c (word_to_le_bytes 8 ret) ret ltac:(addr_norm; exact C1) ltac:(apply bytes_le_to_Z_8).
      stepLD F_7eb40 D_7eb40 (word_to_le_bytes 8 s0v) s0v ltac:(addr_norm; exact C2) ltac:(apply bytes_le_to_Z_8).
      stepLD F_7eb44 D_7eb44 (word_to_le_bytes 8 s1v) s1v ltac:(addr_norm; exact C3) ltac:(apply bytes_le_to_Z_8).
      stepLD F_7eb48 D_7eb48 (word_to_le_bytes 8 s2v) s2v ltac:(addr_norm; exact C4) ltac:(apply bytes_le_to_Z_8).
      stepLD F_7eb4c D_7eb4c (word_to_le_bytes 8 s3v) s3v ltac:(addr_norm; exact C5) ltac:(apply bytes_le_to_Z_8).
      stepLD F_7eb50 D_7eb50 (word_to_le_bytes 8 s4v) s4v ltac:(addr_norm; exact C6) ltac:(apply bytes_le_to_Z_8).
      stepLD F_7eb54 D_7eb54 (word_to_le_bytes 8 s5v) s5v ltac:(addr_norm; exact C7) ltac:(apply bytes_le_to_Z_8).
      stepLD F_7eb58 D_7eb58 (word_to_le_bytes 8 s6v) s6v ltac:(addr_norm; exact C8) ltac:(apply bytes_le_to_Z_8).
      stepLD F_7eb5c D_7eb5c (word_to_le_bytes 8 s7v) s7v ltac:(addr_norm; exact C9) ltac:(apply bytes_le_to_Z_8).
      stepLD F_7eb60 D_7eb60 (word_to_le_bytes 8 s8v) s8v ltac:(addr_norm; exact C10) ltac:(apply bytes_le_to_Z_8).
      stepLD F_7eb64 D_7eb64 (word_to_le_bytes 8 s9v) s9v ltac:(addr_norm; exact C11) ltac:(apply bytes_le_to_Z_8).
      stepLD F_7eb68 D_7eb68 (word_to_le_bytes 8 s10v) s10v ltac:(addr_norm; exact C12) ltac:(apply bytes_le_to_Z_8).
      zv F_7eb6c D_7eb6c (Z_to_bv 64 s).
      stepret F_7eb70 D_7eb70 ret ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
End Segs.
End Count.
