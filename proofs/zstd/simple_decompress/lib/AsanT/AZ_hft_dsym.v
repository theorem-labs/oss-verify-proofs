(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdHufFse.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk PropExec MState.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit FseWalkMem FseRdKit MemRange ZdWalkKit ZdCellKit ZdHufWY SepHide.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXGoF KXLean KXAsan KXAutoA.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase RtCells AZ_kit AZ_globals AZ_globalsR AZ_huf_iface AZ_hft_iface AZ_hft_initds.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation zlen l := (Z.of_nat (length l)).

Notation isbyte := (fun v : Z => 0 <= v < 256).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fd_tblv (tl fast : Z) (tb : list Z) : Prop :=
  zlen tb = 4 * 2^tl /\ 0 <= fast <= 1 /\ Forall isbyte tb /\ forall u, 0 <= u < 2^tl -> fse_cell_ok tl fast tb u.

(* [comment removed for export] *)
Definition fc_nb (tb : list Z) (st : Z) : Z := Znth (4 * st + 3) tb.
Definition fc_sy (tb : list Z) (st : Z) : Z := Znth (4 * st + 2) tb.
Definition fc_nx (tb : list Z) (st : Z) : Z := Znth (4 * st) tb + 256 * Znth (4 * st + 1) tb.

Lemma fd_cell : forall tl fast tb st, fd_tblv tl fast tb -> 0 <= tl -> 0 <= st < 2^tl ->
  0 <= fc_nb tb st <= tl /\ (fast = 1 -> 1 <= fc_nb tb st) /\ 0 <= fc_nx tb st /\ fc_nx tb st + 2^(fc_nb tb st) <= 2^tl
  /\ 0 <= fc_sy tb st < 256 /\ 0 <= Znth (4 * st) tb < 256 /\ 0 <= Znth (4 * st + 1) tb < 256.
Proof.
  intros tl fast tb st (L & FR & BY & OK) TL HS. specialize (OK st HS). unfold fse_cell_ok in OK. cbv zeta in OK.
  unfold fc_nb, fc_sy, fc_nx. destruct OK as (A & B & C & D).
  split; [exact A|]. split; [exact B|]. split; [exact C|]. split; [exact D|].
  split; [apply (Forall_Znth _ tb (4 * st + 2) BY); lia|]. split; [apply (Forall_Znth _ tb (4 * st) BY); lia| apply (Forall_Znth _ tb (4 * st + 1) BY); lia].
Qed.

(* [comment removed for export] *)
Lemma fast_bits_lt : forall x nb, 0 <= x < 2^64 -> 1 <= nb <= 63 ->
  0 <= Z.shiftr x ((bv_swrap 32 (0 - nb) mod 18446744073709551616) mod 64) < 2^nb.
Proof.
  intros x nb Hx Hn. rewrite (FseWalkKit.swrap32_small (0 - nb)) by lia.
  replace ((0 - nb) mod 18446744073709551616) with (18446744073709551616 - nb) by (apply Z.mod_unique with (q := -1); lia).
  replace ((18446744073709551616 - nb) mod 64) with (64 - nb) by (apply Z.mod_unique with (q := 288230376151711743); lia).
  rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; [lia| apply Z.pow_pos_nonneg; lia]|].
  apply Z.div_lt_upper_bound; [apply Z.pow_pos_nonneg; lia|]. rewrite <- Z.pow_add_r by lia. replace (64 - nb + nb) with 64 by lia. lia.
Qed.
(* [comment removed for export] *)
Lemma fast_bits_ltK : forall x nb, 0 <= x < 2^64 -> 1 <= nb <= 63 -> 0 <= x / 2 ^ ((-1 * nb) mod 2^64 mod 64) < 2^nb.
Proof.
  intros x nb Hx Hn.
  replace ((-1 * nb) mod 2^64) with (2^64 - nb) by (apply Z.mod_unique with (q := -1); lia).
  replace ((2^64 - nb) mod 64) with (64 - nb) by (apply Z.mod_unique with (q := 288230376151711743); lia).
  split; [apply Z.div_pos; [lia| apply Z.pow_pos_nonneg; lia]|].
  apply Z.div_lt_upper_bound; [apply Z.pow_pos_nonneg; lia|]. rewrite <- Z.pow_add_r by lia. replace (64 - nb + nb) with 64 by lia. lia.
Qed.
(* [comment removed for export] *)
Lemma fast_bits_ltK2 : forall x nb, 0 <= x < 2^64 -> 1 <= nb <= 63 -> 0 <= x / 2 ^ (Z.land ((-1 * nb) mod 2^64) 63 mod 64) < 2^nb.
Proof.
  intros x nb Hx Hn. change 63 with (Z.ones 6). rewrite Z.land_ones by lia. change (2^6) with 64.
  rewrite Z.mod_mod by lia. apply fast_bits_ltK; assumption.
Qed.
(* [comment removed for export] *)
Lemma fuland_mask_lt2 : forall x nb, 0 <= nb <= 62 -> 0 <= Z.land x (2^nb - 1) < 2^nb.
Proof.
  intros x nb Hn. replace (2^nb - 1) with (Z.ones nb) by (rewrite Z.ones_equiv; apply Z.sub_1_r).
  rewrite Z.land_ones by lia. split; [apply Z.mod_pos_bound | apply Z.mod_pos_bound]; apply Z.pow_pos_nonneg; lia.
Qed.

(* [comment removed for export] *)
Lemma sn_nb : forall sy nb, 0 <= sy < 256 -> 0 <= nb < 256 -> Z.shiftr (Z.shiftl (sy + 256 * nb) 16 mod 2^64) 24 = nb.
Proof.
  intros sy nb H1 H2. rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.mod_small by lia. rewrite Z.shiftr_div_pow2 by lia.
  change (2^16) with 65536. change (2^24) with 16777216. Z.div_mod_to_equations; lia.
Qed.
Lemma cell_word : forall nx sn, 0 <= nx < 65536 -> 0 <= sn < 65536 ->
  Z.lor ((Z.shiftl sn 16) mod 18446744073709551616) nx = nx + 65536 * sn.
Proof.
  intros nx sn H1 H2. rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.mod_small by lia.
  rewrite (ZdHufWY.lor_disj_add sn nx 16) by lia. lia.
Qed.
Lemma cell_hi29 : forall nx sy nb, 0 <= nx < 65536 -> 0 <= sy < 256 -> 0 <= nb < 32 ->
  Z.shiftr (nx + 65536 * (sy + 256 * nb)) 29 = 0.
Proof. intros nx sy nb H1 H2 H3. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small. lia. Qed.
(* [comment removed for export] *)
Lemma cell_lo16K : forall nx sn, 0 <= nx < 65536 -> 0 <= sn < 8192 -> ((nx + 65536 * sn) * 2^48) mod 2^64 / 2^48 = nx.
Proof.
  intros nx sn H1 H2. replace ((nx + 65536 * sn) * 2^48) with (nx * 2^48 + sn * 2^64) by lia.
  rewrite Z_mod_plus_full. rewrite Z.mod_small by lia. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma fd_rd1 : forall (m : amem) A (tb : list Z) i, bytes_at bsegs m A (map (Z_to_bv 8) tb) -> Forall isbyte tb ->
  0 <= i -> i + 1 <= zlen tb -> rdval bsegs m (wa (A + i)) 1 false = Z_to_bv 64 (Znth i tb).
Proof.
  intros m A tb i B BY H0 H1.
  rewrite (rdval_bytes_at bsegs m A (map (Z_to_bv 8) tb) i 1 false B) by (rewrite ?length_map; lia).
  rewrite skipn_map, firstn_map. unfold Znth.
  destruct (skipn (Z.to_nat i) tb) as [|x t] eqn:E.
  { exfalso. apply (f_equal (@length Z)) in E. rewrite length_skipn in E. cbn in E. lia. }
  assert (X : nth (Z.to_nat i) tb 0 = x).
  { rewrite <- (Nat.add_0_r (Z.to_nat i)). rewrite <- (nth_skipn _ _ _ 0). rewrite E. reflexivity. }
  rewrite X. pose proof (Forall_Znth _ tb i BY ltac:(lia)) as R. unfold Znth in R. rewrite X in R.
  cbn [firstn map extz]. rewrite bytes_le_to_Z_le_val. cbn [map le_val]. rewrite Z_to_bv_unsigned.
  change (firstn 0 t) with (@nil Z). cbn [map le_val]. unfold bv_wrap. change (bv_modulus 8) with 256. rewrite (Z.mod_small x 256) by lia. f_equal. lia.
Qed.
Lemma fd_rd2 : forall (m : amem) A (tb : list Z) i, bytes_at bsegs m A (map (Z_to_bv 8) tb) -> Forall isbyte tb ->
  0 <= i -> i + 2 <= zlen tb -> rdval bsegs m (wa (A + i)) 2 false = Z_to_bv 64 (Znth i tb + 256 * Znth (i + 1) tb).
Proof.
  intros m A tb i B BY H0 H1.
  rewrite (rdval_bytes_at bsegs m A (map (Z_to_bv 8) tb) i 2 false B) by (rewrite ?length_map; lia).
  rewrite skipn_map, firstn_map. unfold Znth. replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  destruct (skipn (Z.to_nat i) tb) as [|x [|y t]] eqn:E.
  { exfalso. apply (f_equal (@length Z)) in E. rewrite length_skipn in E. cbn in E. lia. }
  { exfalso. apply (f_equal (@length Z)) in E. rewrite length_skipn in E. cbn in E. lia. }
  assert (X : nth (Z.to_nat i) tb 0 = x).
  { rewrite <- (Nat.add_0_r (Z.to_nat i)). rewrite <- (nth_skipn _ _ _ 0). rewrite E. reflexivity. }
  assert (Y : nth (S (Z.to_nat i)) tb 0 = y).
  { replace (S (Z.to_nat i)) with (Z.to_nat i + 1)%nat by lia. rewrite <- (nth_skipn _ _ _ 0). rewrite E. reflexivity. }
  rewrite X, Y. pose proof (Forall_Znth _ tb i BY ltac:(lia)) as R. unfold Znth in R. rewrite X in R.
  pose proof (Forall_Znth _ tb (i + 1) BY ltac:(lia)) as R'. unfold Znth in R'. replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) in R' by lia. rewrite Y in R'.
  cbn [firstn map extz]. rewrite bytes_le_to_Z_le_val. cbn [map le_val]. rewrite !Z_to_bv_unsigned.
  change (firstn 0 t) with (@nil Z). cbn [map le_val]. unfold bv_wrap. change (bv_modulus 8) with 256. rewrite (Z.mod_small x 256), (Z.mod_small y 256) by lia. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma dsym_nb_of_w2 : forall sy nb, 0 <= sy < 256 -> 0 <= nb < 256 -> (65536 * (sy + 256 * nb)) mod 2^64 / 2^24 = nb.
Proof. intros. rewrite Z.mod_small by lia. Z.div_mod_to_equations. lia. Qed.
Lemma dsym_nb_of_w2' : forall sy nb, 0 <= sy < 256 -> 0 <= nb < 256 -> ((sy + 256 * nb) * 65536) mod 2^64 / 2^24 = nb.
Proof. intros. rewrite Z.mod_small by lia. Z.div_mod_to_equations. lia. Qed.
Lemma dsym_lo16_lor : forall hi nx, 0 <= nx < 65536 -> 0 <= hi < 2^32 ->
  (Z.lor ((65536 * hi) mod 2^64) nx * 2^48) mod 2^64 / 2^48 = nx.
Proof.
  intros hi nx Hn Hh. rewrite (Z.mod_small (65536 * hi)) by lia.
  rewrite Z.lor_comm. rewrite (FseRdKit.lor_add_disjoint nx (65536 * hi) 16); [| lia | cbn; lia | replace (65536 * hi) with (hi * 2^16) by lia; apply Z_mod_mult].
  replace ((nx + 65536 * hi) * 2^48) with (nx * 2^48 + hi * 2^64) by lia.
  rewrite Z_mod_plus_full. rewrite Z.mod_small by lia. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
  (* [comment removed for export] *)
