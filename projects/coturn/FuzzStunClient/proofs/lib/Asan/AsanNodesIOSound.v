(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import CheckLite.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SpinAlg AgentLib AgentNodes Nodes RefNodes FileSim AsanAcct AsanAcctShape.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import
  AsanAcctNoLazy.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import
  AsanPlacement BackingAlgebra.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import
  AsanNodesLibE.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import
  RefLayout.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AsanNodesAux AsanIOSpec AsanNodesIO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS. Import ION.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma is_ecall_at_sound : forall SEGS cs,
  is_ecall_at SEGS cs = true ->
  0 <= pc cs /\ pc cs + 4 < two64 /\
  exists w, fetch_word SEGS (Z_to_bv 64 (pc cs)) = Some w /\ is_ecall w = true.
Proof.
  intros SEGS cs H. unfold is_ecall_at in H.
  apply andb_prop in H as [H Hf]. apply andb_prop in H as [H0 H4].
  apply Z.leb_le in H0. apply Z.ltb_lt in H4.
  destruct (fetch_word SEGS (Z_to_bv 64 (pc cs))) as [w|] eqn:Hw; [|discriminate].
  repeat split; try assumption. exists w. auto.
Qed.

Lemma at_sys_sound : forall SEGS cs nr,
  at_sys SEGS cs nr = true ->
  is_ecall_at SEGS cs = true /\ reg_lit cs 17 = Some nr.
Proof.
  intros SEGS cs nr H. unfold at_sys in H. apply andb_prop in H as [He Hr]. split; [exact He|].
  destruct (reg_lit cs 17) as [z|]; [|discriminate]. apply Z.eqb_eq in Hr. subst. reflexivity.
Qed.

Lemma reg_is_sound : forall cs r z, reg_is cs r z = true -> reg_lit cs r = Some z.
Proof.
  intros cs r z H. unfold reg_is in H. destruct (reg_lit cs r) as [z'|]; [|discriminate].
  apply Z.eqb_eq in H. subst. reflexivity.
Qed.

Lemma reg5 : forall n, (n < 32)%nat -> forall r : bv 5, bv_unsigned r = Z.of_nat n -> Z_to_bv 5 (Z.of_nat n) = r.
Proof. intros n Hn r Hr. apply bv_eq. rewrite reg_lit5 by lia. symmetry. exact Hr. Qed.

(* [comment removed for export] *)
Lemma fd_lookup_fds3 : forall e, fd_lookup (fds3 e) (Z_to_bv 64 3) = Some e.
Proof. intros e. reflexivity. Qed.
Lemma fd_remove_fds3 : forall e, fd_remove (fds3 e) (Z_to_bv 64 3) = fds_std.
Proof. intros e. reflexivity. Qed.
Lemma fd_insert_fds3 : forall e e', fd_insert (fds3 e) (Z_to_bv 64 3) e' = fds3 e'.
Proof. intros e e'. reflexivity. Qed.
Lemma fd_insert_std3 : forall e', fd_insert fds_std (Z_to_bv 64 3) e' = fds3 e'.
Proof. intros e'. reflexivity. Qed.
Lemma alloc_fd_std : alloc_fd fds_std = Z_to_bv 64 3.
Proof. reflexivity. Qed.
Lemma fd_lookup_std3 : fd_lookup fds_std (Z_to_bv 64 3) = None.
Proof. reflexivity. Qed.
Lemma fd_lookup_1 : forall fds, (fds = fds_std \/ exists e, fds = fds3 e) ->
  fd_lookup fds (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)).
Proof. intros fds [->|[e ->]]; reflexivity. Qed.

(* [comment removed for export] *)
Definition mdl_sim (m m' : Model) : Prop :=
  m_vmmaps m' = m_vmmaps m /\ m_vm_lazy m' = m_vm_lazy m /\ m_halted m' = m_halted m
  /\ m_tid m' = m_tid m /\ m_fs m' = m_fs m /\ eager_used m' = eager_used m.

Lemma mdl_sim_refl : forall m, mdl_sim m m.
Proof. intros m. repeat split; reflexivity. Qed.
Lemma mdl_sim_with_fds : forall f m, mdl_sim m (with_fds f m).
Proof. intros f m. repeat split; reflexivity. Qed.
Lemma mdl_sim_trans : forall m1 m2 m3, mdl_sim m1 m2 -> mdl_sim m2 m3 -> mdl_sim m1 m3.
Proof. intros m1 m2 m3 (A1&A2&A3&A4&A5&A6) (B1&B2&B3&B4&B5&B6). repeat split; congruence. Qed.
Lemma mdl_sim_materialized : forall m m', same_but_materialized m m' -> mdl_sim m m'.
Proof.
  intros m m' Hs. pose proof (same_but_materialized_frame _ _ Hs) as F.
  repeat split; apply F.
Qed.
Lemma m_fds_with_fds : forall f m, m_fds (with_fds f m) = f.
Proof. reflexivity. Qed.
Lemma m_fs_with_fds : forall f m, m_fs (with_fds f m) = m_fs m.
Proof. reflexivity. Qed.
Lemma MInv_with_fds : forall AA f m, MInv AA m -> MInv AA (with_fds f m).
Proof. intros AA f m H. destruct H; constructor; assumption. Qed.

(* [comment removed for export] *)
Lemma kwritable_x_sound : forall segs E M allkn k b off n,
  know_ok segs E M allkn ->
  know_ok segs E M k -> kwritable_x allkn k b off n = true ->
  (forall m, Z.of_nat m <= elenZ E n ->
     store_ok segs M (Z_to_bv 64 (estart E (SA b off))) m = true)
  /\ 0 <= estart E (SA b off) /\ estart E (SA b off) + elenZ E n <= 2 ^ 64.
Proof.
  intros segs E M allkn k b off n Hall HK H. induction k as [|K rest IH]; [discriminate|].
  apply Forall_cons_iff in HK as [HKK Hrest]. cbn [kwritable_x] in H.
  destruct K; try exact (IH Hrest H).
  lazymatch type of HKK with kentry_ok _ _ _ (KWr ?a ?n) => destruct a as [wb wk]; rename n into wn end.
  assert (H2w : forall c1 c2 : bool, (if c1 then true else if c2 then true else kwritable_x allkn rest b off n) = true ->
                 (c1 || c2)%bool = true \/ kwritable_x allkn rest b off n = true)
    by (intros [|] [|]; cbn; auto).
  apply H2w in H. destruct H as [H|H]; [|exact (IH Hrest H)].
  cbn [kentry_ok] in HKK. destruct HKK as [Hfl Hs]. pose proof Hfl as Hfl'. destruct Hfl' as (F1 & F2 & F3 & F4).
  unfold estart in Hs, F1, F2, F4 |- *. cbn [a_base a_off] in Hs, F1, F2, F4 |- *.
  pose proof (u64_range (edenot E n)) as Hnr.
  assert (CORE : bv_unsigned (edenot E wb) + wk <= bv_unsigned (edenot E b) + off ->
                 bv_unsigned (edenot E b) + off + elenZ E n <= bv_unsigned (edenot E wb) + wk + elenZ E wn ->
                 (forall m, Z.of_nat m <= elenZ E n -> store_ok segs M (Z_to_bv 64 (bv_unsigned (edenot E b) + off)) m = true)
                 /\ 0 <= bv_unsigned (edenot E b) + off /\ bv_unsigned (edenot E b) + off + elenZ E n <= 2 ^ 64).
  { intros A B. split; [|unfold elenZ in *; lia]. intros m Hm.
    replace (bv_unsigned (edenot E b) + off) with (bv_unsigned (edenot E wb) + wk + (bv_unsigned (edenot E b) + off - (bv_unsigned (edenot E wb) + wk))) by lia.
    apply Hs; lia. }
  apply orb_prop in H as [H|H].
  - destruct (expr_eqb b wb && Z.leb wk off)%bool eqn:H01; [|discriminate]. apply andb_prop in H01 as [H0 H1].
    apply expr_eqb_eq in H0. apply Z.leb_le in H1. subst wb.
    destruct (xhi allkn n) as [nh|] eqn:Hxh; [|discriminate].
    destruct (xlo allkn wn) as [wl|] eqn:Hxl; [|discriminate]. apply Z.leb_le in H.
    pose proof (xhi_sound segs E M allkn n nh Hall Hxh). pose proof (xlo_sound segs E M allkn wn wl Hall Hxl).
    apply CORE; unfold elenZ in *; lia.
  - pose proof (xinside_sound segs E M allkn b off n wb wk wn Hall H) as [A B].
    unfold estart in A, B. cbn [a_base a_off] in A, B. apply CORE; lia.
Qed.

(* [comment removed for export] *)
Lemma mem_grows_mrestrict : forall (H : word -> bool) FULL, mem_grows (mrestrict H FULL) FULL.
Proof. intros H FULL a. unfold mrestrict. destruct (H a); [intros X; exfalso; exact (X eq_refl) | auto]. Qed.

Lemma wbytes_nth_off : forall bs m (a : Z) i,
  0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 -> 0 <= i < Z.of_nat (length bs) ->
  wbytes m (Z_to_bv 64 a) bs (Z_to_bv 64 (a + i)) = Some (nth (Z.to_nat i) bs (Z_to_bv 8 0)).
Proof.
  intros bs m a i Ha Hn Hi.
  replace (a + i) with (bv_unsigned (Z_to_bv 64 a) + Z.of_nat (Z.to_nat i)) by (rewrite u64_lit by lia; lia).
  apply wbytes_nth; [rewrite u64_lit by lia; lia | lia].
Qed.

Lemma firstn_In' : forall {T} (n : nat) (l : list T) x, In x (firstn n l) -> In x l.
Proof.
  intros T n. induction n as [|n IH]; intros [|y l] x H; cbn in H; try contradiction.
  destruct H as [<-|H]; [left; reflexivity | right; apply IH; exact H].
Qed.

Lemma cstr_access_len_aux_le : forall mp a fuel, (cstr_access_len_aux mp a fuel <= fuel)%nat.
Proof.
  intros mp a fuel. revert a. induction fuel as [|f IH]; intros a; cbn [cstr_access_len_aux]; [lia|].
  destruct (mp a) as [b|]; [|lia]. destruct (bv_eqb b (Z_to_bv 8 0)); [lia|]. specialize (IH (a + 1)%bv). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma land_shift8_0 : forall x b, 0 <= x -> 0 <= b < 256 -> Z.land (x * 256) b = 0.
Proof.
  intros x b Hx Hb. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases i 8) as [Hlt|Hge].
  - change 256 with (2 ^ 8). rewrite Z.mul_pow2_bits_low by lia. reflexivity.
  - replace (Z.testbit b i) with false; [apply andb_false_r|]. symmetry.
    apply Z.testbit_false; [lia|]. rewrite Z.div_small; [reflexivity|]. split; [lia|].
    apply Z.lt_le_trans with 256; [lia|]. change 256 with (2 ^ 8). apply Z.pow_le_mono_r; lia.
Qed.

Lemma lor_shift8 : forall x b, 0 <= x -> 0 <= b < 256 -> Z.lor (x * 256) b = x * 256 + b.
Proof.
  intros x b Hx Hb. rewrite <- Z.lxor_lor by (apply land_shift8_0; lia).
  symmetry. apply Z.add_nocarry_lxor. apply land_shift8_0; lia.
Qed.

(* [comment removed for export] *)
Lemma blob_byte : forall bs i, 0 <= i ->
  bytes_le_to_Z (blob_bytes bs i 1) = bv_unsigned (nth (Z.to_nat i) bs (Z_to_bv 8 0)).
Proof.
  intros bs i Hi. unfold blob_bytes.
  destruct (skipn (Z.to_nat i) bs) as [|b r] eqn:Hs.
  - cbn. rewrite nth_overflow; [reflexivity|].
    pose proof (f_equal (@length byte) Hs) as L. rewrite length_skipn in L. cbn in L. lia.
  - cbn [firstn bytes_le_to_Z]. rewrite Z.shiftl_0_l, Z.lor_0_r.
    replace (nth (Z.to_nat i) bs (Z_to_bv 8 0)) with (nth 0 (skipn (Z.to_nat i) bs) (Z_to_bv 8 0)) by (rewrite nth_skipn, Nat.add_0_r; reflexivity).
    rewrite Hs. reflexivity.
Qed.

Lemma u_blob_false1 : forall E jb i, 0 <= i ->
  bv_unsigned (edenot E (EBlob false jb i 1)) = bv_unsigned (nth (Z.to_nat i) (eb E jb) (Z_to_bv 8 0)).
Proof.
  intros E jb i Hi. cbn [edenot]. unfold blob_val. rewrite blob_byte by lia.
  pose proof (u8_range (nth (Z.to_nat i) (eb E jb) (Z_to_bv 8 0))). apply u64_lit. lia.
Qed.

Lemma u_blob_true1 : forall E jb i, 0 <= i ->
  bv_unsigned (edenot E (EBlob true jb i 1)) = bv_swrap 8 (bv_unsigned (nth (Z.to_nat i) (eb E jb) (Z_to_bv 8 0))) mod 2 ^ 64.
Proof.
  intros E jb i Hi. cbn [edenot]. unfold blob_val. rewrite blob_byte by lia.
  change (8 * N.of_nat 1)%N with 8%N. rewrite Z_to_bv_unsigned. reflexivity.
Qed.

Lemma swrap8 : forall b, 0 <= b < 256 -> bv_swrap 8 b = (if b <? 128 then b else b - 256).
Proof.
  intros b Hb. unfold bv_swrap, bv_wrap, bv_half_modulus. change (bv_modulus 8) with 256.
  change (256 / 2) with 128. destruct (b <? 128) eqn:E; [apply Z.ltb_lt in E | apply Z.ltb_ge in E]; lia.
Qed.

Lemma CFGX_denot : forall E jb,
  uE E (CFGX jb) = (hbyte 0 (eb E jb) + 256 * hbyte 1 (eb E jb)) mod 32768.
Proof.
  intros E jb. unfold uE, CFGX, XB1S, XB0.
  cbn [edenot]. fold (edenot E (EBlob true jb 1 1)). fold (edenot E (EBlob false jb 0 1)).
  rewrite u_or64, u_srl64, u_mul64, !u64_lit by lia. rewrite u_blob_true1, u_blob_false1 by lia.
  unfold hbyte. change (Z.to_nat 0) with 0%nat. change (Z.to_nat 1) with 1%nat.
  set (b0 := bv_unsigned (nth 0 (eb E jb) (Z_to_bv 8 0))). set (b1 := bv_unsigned (nth 1 (eb E jb) (Z_to_bv 8 0))).
  pose proof (u8_range (nth 0 (eb E jb) (Z_to_bv 8 0))) as R0. pose proof (u8_range (nth 1 (eb E jb) (Z_to_bv 8 0))) as R1.
  fold b0 in R0. fold b1 in R1.
  rewrite swrap8 by lia. change (49 mod 64) with 49.
  assert (E57 : (2 ^ 57 * ((if b1 <? 128 then b1 else b1 - 256) mod 2 ^ 64)) mod 2 ^ 64 / 2 ^ 49 = (b1 mod 128) * 256).
  { destruct (b1 <? 128) eqn:Eb; [apply Z.ltb_lt in Eb | apply Z.ltb_ge in Eb].
    - rewrite (Z.mod_small b1) by lia. rewrite (Z.mod_small b1) by lia.
      replace (2 ^ 57 * b1) with (b1 * 2 ^ 8 * 2 ^ 49) by (rewrite <- !Z.mul_assoc; change (2^8 * 2^49) with (2^57); lia).
      rewrite (Z.mod_small) by nia. rewrite Z.div_mul by lia. lia.
    - replace ((b1 - 256) mod 2 ^ 64) with (2 ^ 64 - 256 + b1) by lia.
      replace (2 ^ 57 * (2 ^ 64 - 256 + b1)) with ((b1 - 128) * 2 ^ 8 * 2 ^ 49 + (2 ^ 57 - 1) * 2 ^ 64) by lia.
      rewrite Z.mod_add by lia. rewrite Z.mod_small by nia. rewrite Z.div_mul by lia. lia. }
  rewrite E57. rewrite lor_shift8 by lia. lia.
Qed.

Lemma XCM_denot : forall E jb, uE E (XCM jb) = hbyte 2 (eb E jb) mod 4.
Proof.
  intros E jb. unfold uE, XCM, XB2. cbn [edenot]. fold (edenot E (EBlob false jb 2 1)).
  rewrite alu_and. unfold v_and. rewrite u64_lit.
  - rewrite u_blob_false1, u64_lit by lia. unfold hbyte. change (Z.to_nat 2) with 2%nat.
    change 3 with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity.
  - rewrite u_blob_false1, u64_lit by lia. change 3 with (Z.ones 2). rewrite Z.land_ones by lia.
    pose proof (Z.mod_pos_bound (bv_unsigned (nth (Z.to_nat 2) (eb E jb) (Z_to_bv 8 0))) (2 ^ 2) ltac:(lia)). lia.
Qed.

Lemma XB1S_denot : forall E jb, uE E (XB1S jb) = bv_swrap 8 (hbyte 1 (eb E jb)) mod 2 ^ 64.
Proof. intros E jb. unfold uE, XB1S, hbyte. rewrite u_blob_true1 by lia. reflexivity. Qed.

Lemma nth_firstn_lt : forall {X} (l : list X) n i d, (i < n)%nat -> nth i (firstn n l) d = nth i l d.
Proof.
  intros X l n. revert l. induction n as [|n IH]; intros l i d Hi; [lia|].
  destruct l as [|x l]; [destruct i; reflexivity|]. destruct i as [|i]; [reflexivity|]. cbn. apply IH. lia.
Qed.

Lemma hbyte_chunk0 : forall i c, (Z.of_nat i < 65536)%Z -> hbyte i (chunk 0 c) = hbyte i c.
Proof.
  intros i c Hi. unfold hbyte, chunk, CH. rewrite Nat.mul_0_r. cbn [skipn]. rewrite nth_firstn_lt by lia. reflexivity.
Qed.

Lemma length_chunk_Z : forall c j, Z.of_nat (length (chunk j c)) = Z.min 65536 (Z.max 0 (Z.of_nat (length c) - 65536 * Z.of_nat j)).
Proof. intros c j. unfold chunk, CH. rewrite firstn_length, length_skipn. lia. Qed.

(* [comment removed for export] *)
Lemma chunks_flen_le : forall c c',
  (forall j, 65536 * Z.of_nat j < 2 ^ 26 -> chunk j c = chunk j c') -> flen c <= flen c'.
Proof.
  intros c c' H. unfold flen. destruct (Z_lt_le_dec (Z.min (Z.of_nat (length c')) (2 ^ 26)) (Z.min (Z.of_nat (length c)) (2 ^ 26))) as [Hlt|Hle]; [|exact Hle].
  exfalso. set (L := Z.of_nat (length c)) in *. set (L' := Z.of_nat (length c')) in *.
  set (j := Z.to_nat (L' / 65536)).
  assert (Hj : 65536 * Z.of_nat j <= L' /\ L' < 65536 * Z.of_nat j + 65536 /\ 65536 * Z.of_nat j < 2 ^ 26) by (unfold j; rewrite Z2Nat.id by lia; lia).
  pose proof (f_equal (fun l => Z.of_nat (length l)) (H j ltac:(lia))) as E. cbv beta in E.
  rewrite !length_chunk_Z in E. fold L L' in E. lia.
Qed.

Lemma chunks_flen : forall c c',
  (forall j, 65536 * Z.of_nat j < 2 ^ 26 -> chunk j c = chunk j c') -> flen c = flen c'.
Proof.
  intros c c' H. pose proof (chunks_flen_le c c' H). pose proof (chunks_flen_le c' c ltac:(intros j Hj; symmetry; apply H; exact Hj)). lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma residue_window : forall rho c0 m s,
  0 < m -> 0 <= rho <= s -> (rho mod m = c0 mod m) ->
  c0 mod m <= rho <= s - ((s - c0 mod m) mod m).
Proof.
  intros rho c0 m s Hm Hr Hc.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  pose proof (Z.mod_pos_bound rho m Hm). pose proof (Z.mod_pos_bound c0 m Hm).
  pose proof (Z.div_mod rho m ltac:(lia)) as D1.
  set (r0 := c0 mod m) in *.
  split; [nia|].
  (* [comment removed for export] *)
  pose proof (Z.mod_pos_bound (s - r0) m Hm). pose proof (Z.div_mod (s - r0) m ltac:(lia)) as D2.
  assert (rho / m <= (s - r0) / m) by (apply Z.div_le_lower_bound; nia).
  nia.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

(* [comment removed for export] *)
Lemma valid_argv_path1 : forall argv, valid_argv argv -> (2 <= length argv)%nat ->
  path_has_slash (nth 1 argv []) = false /\ nth 1 argv [] <> dotdot_path.
Proof.
  intros argv Hva H2. destruct Hva as (_ & _ & _ & _ & Hp).
  destruct argv as [|a0 [|a1 r]]; cbn [length] in H2; try lia.
  cbn [tl nth] in *. apply Forall_cons_iff in Hp as [[Hs Hd] _]. split; [exact Hs|].
  intros E. rewrite E in Hd. cbv in Hd. discriminate.
Qed.

Section IOSound.
  Variable SEGS : list Segment.
  Variable A : atable.
  Variable nx0 : N.
  Variable LIMIT : Z.
  Variable SINV : env -> (word -> option byte) -> Prop.
  Variable argH : env -> word -> bool.
  Variable FS0 : Fs.Fs.
  Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
  Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
  Hypothesis HULL_ok : hull_ok A.
  Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
  Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
  Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
  Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
  Hypothesis nx0_ge7 : APS.nx0_ok nx0.   (* [comment removed for export] *)
  Variable T : iotab.

  (* [comment removed for export] *)
  Variable ph : PhdrInfo.
  Variable sp : word.
  Variable rdraw : EntryDraw.   (* [comment removed for export] *)
  Variables argv envp : list (list byte).
  Variable uid : word.                  (* [comment removed for export] *)
  Variable hw : word.   (* [comment removed for export] *)
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hsp_lo : sp_window_lo <= bv_unsigned sp.
  Hypothesis Hsp_hi : bv_unsigned sp <= sp_window_hi.
  Let usp := bv_unsigned sp.
  Let argc := Z.of_nat (length argv).
  Let envc := Z.of_nat (length envp).
  Let argv0 := nth 0 argv [].
  Let argv1 := nth 1 argv [].
  Let STR1 := usp + 8 * argc + 8 * envc + 184 + Z.of_nat (length argv0) + 1.   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Hypothesis H_vals : forall E M, SINV E M ->
    ev E V_ARGC = Z_to_bv 64 argc /\ (2 <= argc -> uE E e_str1 = STR1)
    /\ uE E e_sp0 = usp.   (* [comment removed for export] *)
  Hypothesis H_str1 : forall E M (a : word), SINV E M -> 2 <= argc ->
    STR1 <= bv_unsigned a <= STR1 + Z.of_nat (length argv1) -> M a = wrap_mem ph sp argv envp uid hw rdraw a.

  (* [comment removed for export] *)
  Hypothesis H_open : match io_open T with
    | ONone => True
    | OTooLong => (4096 <= length argv1)%nat
    | ONoEnt => argv1 = [] \/ (argv1 <> dot_path /\ (length argv1 <= 4095)%nat /\ fs_lookup FS0 argv1 = None)
    | ODir => argv1 = dot_path
    | OFile lo hi => exists c, argv1 <> [] /\ argv1 <> dot_path /\ (length argv1 <= 4095)%nat /\ fs_lookup FS0 argv1 = Some c
                     /\ lo <= flen c <= hi
                     /\ (forall E M, SINV E M -> forall j, 65536 * Z.of_nat j < 2 ^ 26 -> eb E (io_blob T + j)%nat = chunk j c)
                     /\ hdr_ok T c
    end.

  #[local] Notation cs_ok := (APS.cs_ok SEGS A LIMIT SINV argH FS0).
  #[local] Notation cfg := (cfg_of SEGS).

  (* [comment removed for export] *)
  Lemma vis_ret : forall E cs r k' nx' f' model model',
    m_vmmaps model' = m_vmmaps model -> m_vm_lazy model' = m_vm_lazy model ->
    vis A E (ret_with cs r k' nx' f') model' = vis A E cs model.
  Proof.
    intros E cs r k' nx' f' model model' Hv Hl. apply functional_extensionality. intros a.
    unfold vis, in_allow, in_vis, in_sh. cbn [ret_with a_vis]. rewrite Hv, Hl. reflexivity.
  Qed.

  Lemma hid_ret : forall E cs r k' nx' f' model model',
    m_vmmaps model' = m_vmmaps model -> m_vm_lazy model' = m_vm_lazy model ->
    hid A argH E (ret_with cs r k' nx' f') model' = hid A argH E cs model.
  Proof. intros. unfold hid. apply functional_extensionality. intros a. rewrite (vis_ret _ _ _ _ _ _ _ _ H H0). reflexivity. Qed.

  Lemma allowA_ret : forall E cs r k' nx' f', allowA A E (ret_with cs r k' nx' f') = allowA A E cs.
  Proof. reflexivity. Qed.

  Lemma cs_ok_rebuild : forall E cs R FULL model R' FULL' model' r k' nx' f',
    cs_ok E cs R FULL model ->
    mdl_sim model model' -> MInv (allowA A E cs) model' ->
    regs_ok E (sr_upd (s_regs (a_ss cs)) 10 r) R' ->
    know_ok SEGS E (mrestrict (hid A argH E cs model) FULL') k' ->
    fds_ok E f' model' ->
    (forall a, hid A argH E cs model a = true -> FULL' a = FULL a) ->
    cs_ok E (ret_with cs r k' nx' f') R' FULL' model'.
  Proof.
    intros E cs R FULL model R' FULL' model' r k' nx' f' HC (S1 & S2 & S3 & S4 & S5 & S6) Hinv HR HK Hf Hhid.
    pose proof (hid_ret E cs r k' nx' f' model model' S1 S2) as Hh.
    destruct HC; constructor; cbn [ret_with a_ss a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset kn mk_ss s_regs s_log s_know];
      rewrite ?allowA_ret, ?S1, ?S2, ?S3, ?S4, ?S5, ?S6; try assumption; try reflexivity.
    - unfold Mr. rewrite Hh. exact HK.
    - unfold model_ivs_wf in *. rewrite S1, S2. assumption.
    - intros a Ha. rewrite Hh in Ha. rewrite (Hhid a Ha). auto.
    - eapply SINV_frame; [|eassumption]. intros a Ha. apply Hhid. unfold hid. rewrite Ha. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma regs_ok_a0 : forall E sr R e v,
    regs_ok E sr R -> edenot E e = v -> regs_ok E (sr_upd sr 10 e) (regupd R 10%bv v).
  Proof.
    intros E sr R e v HR Hv.
    replace (10%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 10)) by (apply bv_eq; reflexivity).
    apply regs_ok_set_n; [exact HR | lia | exact Hv].
  Qed.

  (* [comment removed for export] *)
  Lemma at_sys_facts : forall E cs R FULL model nr,
    cs_ok E cs R FULL model -> at_sys SEGS cs nr = true -> 0 <= nr < two64 ->
    0 <= pc cs /\ pc cs + 4 < two64
    /\ (exists w, fetch_word SEGS (Z_to_bv 64 (pc cs)) = Some w /\ is_ecall w = true)
    /\ getr R 17%bv = Z_to_bv 64 nr.
  Proof.
    intros E cs R FULL model nr HC H Hnr. apply at_sys_sound in H as [He H17].
    destruct (is_ecall_at_sound SEGS cs He) as (H0 & H4 & Hw). split; [lia|]. split; [exact H4|]. split; [exact Hw|].
    destruct (reg_lit_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 17 nr HC ltac:(lia) H17) as [G _].
    rewrite <- G. f_equal.
  Qed.

  Lemma reg_is_getr : forall E cs R FULL model n z,
    cs_ok E cs R FULL model -> (0 < n < 32)%nat -> reg_is cs n z = true ->
    getr R (Z_to_bv 5 (Z.of_nat n)) = Z_to_bv 64 z /\ 0 <= z < two64.
  Proof.
    intros E cs R FULL model n z HC Hn H. apply reg_is_sound in H.
    exact (reg_lit_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model n z HC Hn H).
  Qed.

  Lemma pc4 : forall cs, 0 <= pc cs -> pc cs + 4 < two64 ->
    v_addi (Z_to_bv 64 (pc cs)) 4 = Z_to_bv 64 (pc cs + 4).
  Proof. intros cs H0 H4. apply v_addi_lit. unfold two64 in *. lia. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Theorem node_close_sound : node1_stmt SEGS A nx0 LIMIT SINV argH FS0 always (fun cs => node_close SEGS cs).
  Proof.
    intros cs cs' E R FULL model TT HC _ Hn Hk. cbv beta in Hn. unfold node_close in Hn.
    destruct (at_sys SEGS cs 57 && reg_is cs 10 3 && negb (is_std (a_fd cs)))%bool eqn:Hc; [|discriminate].
    injection Hn as <-.
    apply andb_prop in Hc as [Hc Hstd]. apply andb_prop in Hc as [Hsys H10].
    destruct (at_sys_facts E cs R FULL model 57 HC Hsys ltac:(unfold two64; lia)) as (Hp0 & Hp4 & [w [HF HE]] & H17).
    destruct (reg_is_getr E cs R FULL model 10 3 HC ltac:(lia) H10) as [G10 _].
    replace (Z_to_bv 5 (Z.of_nat 10)) with (10%bv : bv 5) in G10 by (apply bv_eq; reflexivity).
    (* [comment removed for export] *)
    assert (Hfds : exists e, m_fds model = fds3 e).
    { pose proof (co_fds _ _ _ _ _ _ _ _ _ _ _ HC) as Hf. destruct (a_fd cs) as [|kb len off|]; [discriminate| |].
      - destruct Hf as [p [c (Hf1 & _)]]. eexists. exact Hf1.
      - exists State.FdDir. exact Hf. }
    destruct Hfds as [e Hfds].
    unfold cfg_of.
    eapply (srz_close_lazy SEGS R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w (Z_to_bv 64 3) e);
      [exact HF | exact HE | exact (co_halt _ _ _ _ _ _ _ _ _ _ _ HC) | exact H17 | exact G10
      | rewrite u64_lit by lia; lia | rewrite Hfds; apply fd_lookup_fds3 |].
    rewrite (pc4 cs Hp0 Hp4).
    specialize (Hk E (regupd R 10%bv (Z_to_bv 64 0)) FULL (with_fds (fd_remove (m_fds model) (Z_to_bv 64 3)) model) (conj (env_agree_refl nx0 E) (env_agree_refl (nxt cs) E))).
    unfold cfg_of, pc in Hk. cbn [ret_with a_ss mk_ss s_pc] in Hk. apply Hk; [|reflexivity].
    apply cs_ok_rebuild with (model := model) (R := R) (FULL := FULL); try exact HC.
    - apply mdl_sim_with_fds.
    - apply MInv_with_fds. exact (co_minv _ _ _ _ _ _ _ _ _ _ _ HC).
    - apply regs_ok_a0; [exact (co_regs _ _ _ _ _ _ _ _ _ _ _ HC) | reflexivity].
    - exact (co_know _ _ _ _ _ _ _ _ _ _ _ HC).
    - cbn [fds_ok]. rewrite m_fds_with_fds, Hfds. apply fd_remove_fds3.
    - intros; reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Theorem node_ioctl_sound : node1_stmt SEGS A nx0 LIMIT SINV argH FS0 always (fun cs => node_ioctl SEGS cs).
  Proof.
    intros cs cs' E R FULL model TT HC _ Hn Hk. cbv beta in Hn. unfold node_ioctl in Hn.
    destruct (at_sys SEGS cs 29 && reg_is cs 10 1 && reg_is cs 11 0x5413)%bool eqn:Hc; [|discriminate].
    injection Hn as <-.
    apply andb_prop in Hc as [Hc H11]. apply andb_prop in Hc as [Hsys H10].
    destruct (at_sys_facts E cs R FULL model 29 HC Hsys ltac:(unfold two64; lia)) as (Hp0 & Hp4 & [w [HF HE]] & H17).
    destruct (reg_is_getr E cs R FULL model 10 1 HC ltac:(lia) H10) as [G10 _].
    replace (Z_to_bv 5 (Z.of_nat 10)) with (10%bv : bv 5) in G10 by (apply bv_eq; reflexivity).
    destruct (reg_is_getr E cs R FULL model 11 0x5413 HC ltac:(lia) H11) as [G11 _].
    replace (Z_to_bv 5 (Z.of_nat 11)) with (11%bv : bv 5) in G11 by (apply bv_eq; reflexivity).
    assert (Hfds : m_fds model = fds_std \/ exists e, m_fds model = fds3 e).
    { pose proof (co_fds _ _ _ _ _ _ _ _ _ _ _ HC) as Hf. destruct (a_fd cs) as [|kb len off|].
      - left. exact Hf.
      - destruct Hf as [p [c (Hf1 & _)]]. right. eexists. exact Hf1.
      - right. eexists. exact Hf. }
    unfold cfg_of.
    eapply (srz_ioctl_winsz_lazy SEGS R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w (Z_to_bv 64 1));
      [exact HF | exact HE | exact (co_halt _ _ _ _ _ _ _ _ _ _ _ HC) | exact H17 | exact G10
      | rewrite u64_lit by lia; lia | apply fd_lookup_1; exact Hfds | exact G11 |].
    rewrite (pc4 cs Hp0 Hp4).
    specialize (Hk E (regupd R 10%bv (errno_ret ENOTTY)) FULL model (conj (env_agree_refl nx0 E) (env_agree_refl (nxt cs) E))).
    unfold cfg_of, pc in Hk. cbn [ret_simple ret_with a_ss mk_ss s_pc] in Hk. apply Hk; [|reflexivity].
    unfold ret_simple. apply cs_ok_rebuild with (model := model) (R := R) (FULL := FULL); try exact HC.
    - apply mdl_sim_refl.
    - exact (co_minv _ _ _ _ _ _ _ _ _ _ _ HC).
    - apply regs_ok_a0; [exact (co_regs _ _ _ _ _ _ _ _ _ _ _ HC) |].
      rewrite edenot_lit. unfold errno_ret, ENOTTY. apply bv_eq. reflexivity.
    - exact (co_know _ _ _ _ _ _ _ _ _ _ _ HC).
    - exact (co_fds _ _ _ _ _ _ _ _ _ _ _ HC).
    - intros; reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma dst_ok_sound : forall E cs R FULL model n db dk,
    cs_ok E cs R FULL model -> dst_ok cs n = Some (db, dk) ->
    getr R 11%bv = Z_to_bv 64 (estart E (SA db dk))
    /\ 0 <= estart E (SA db dk) /\ estart E (SA db dk) + uE E n <= 2 ^ 47 /\ 0 < uE E n
    /\ (forall m, Z.of_nat m <= uE E n -> store_ok SEGS FULL (Z_to_bv 64 (estart E (SA db dk))) m = true)
    /\ (forall m, Z.of_nat m <= uE E n -> store_ok SEGS (Mr A argH E cs model FULL) (Z_to_bv 64 (estart E (SA db dk))) m = true).
  Proof.
    intros E cs R FULL model n db dk HC H. unfold dst_ok in H.
    destruct (split_lit (reg cs 11)) as [b k] eqn:Hs.
    destruct (flat_x (kn cs) b k n && kwritable_x (kn cs) (kn cs) b k n && dst_hi_ok (kn cs) b k n)%bool eqn:Hc; [|discriminate].
    injection H as <- <-. apply andb_prop in Hc as [Hc Hhi]. apply andb_prop in Hc as [Hfl Hwr].
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
    destruct (flat_x_sound SEGS E _ (kn cs) b k n HK Hfl) as (F1 & F2 & F3).
    destruct (kwritable_x_sound SEGS E _ (kn cs) (kn cs) b k n HK HK Hwr) as (W1 & W2 & W3).
    assert (HI : estart E (SA b k) + uE E n <= 2 ^ 47).
    { unfold dst_hi_ok in Hhi.
      destruct (xhi (kn cs) b) as [h|] eqn:Xb; [|discriminate].
      destruct (xhi (kn cs) n) as [hn|] eqn:Xn; [|discriminate].
      apply Z.leb_le in Hhi.
      pose proof (xhi_sound SEGS E _ (kn cs) b h HK Xb) as Bb.
      pose proof (xhi_sound SEGS E _ (kn cs) n hn HK Xn) as Bn.
      unfold estart, uE. cbn [a_base a_off]. lia. }
    unfold uE, elenZ in *. split; [|split; [lia|split; [lia|split; [lia|split]]]].
    - pose proof (reg_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 11 HC ltac:(lia)) as G.
      replace (Z_to_bv 5 (Z.of_nat 11)) with (11%bv : bv 5) in G by (apply bv_eq; reflexivity).
      rewrite G. apply bv_eq. rewrite (u_of_split E (reg cs 11) b k Hs) by lia. rewrite u64_lit by lia. reflexivity.
    - intros m Hm. eapply store_ok_mono; [apply mem_grows_mrestrict | apply W1; exact Hm].
    - exact W1.
  Qed.

  (* [comment removed for export] *)
  Lemma store_ok_Mr_visible : forall E cs model FULL (a : Z) n,
    0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
    store_ok SEGS (Mr A argH E cs model FULL) (Z_to_bv 64 a) n = true ->
    forall i, 0 <= i < Z.of_nat n -> hid A argH E cs model (Z_to_bv 64 (a + i)) = false.
  Proof.
    intros E cs model FULL a n Ha Hn Hst i Hi.
    pose proof (store_ok_all SEGS (Mr A argH E cs model FULL) n (Z_to_bv 64 a) ltac:(rewrite u64_lit by lia; lia) Hst
                  (Z_to_bv 64 (a + i)) ltac:(rewrite !u64_lit by lia; lia)) as W.
    destruct (hid A argH E cs model (Z_to_bv 64 (a + i))) eqn:Hh; [|reflexivity].
    exfalso. apply W. unfold wview, Mr, mrestrict. rewrite Hh.
    rewrite (H_off_segments_cs SEGS A SEGS_in_hull HULL_ok argH argH_high E cs model _ Hh). reflexivity.
  Qed.

  Lemma cnt_ok_sound : forall E cs R FULL model,
    cs_ok E cs R FULL model -> cnt_ok cs = true -> 1 <= uE E (reg cs 12) <= 65536.
  Proof.
    intros E cs R FULL model HC H. unfold cnt_ok, CHZ in H.
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
    destruct (xlo (kn cs) (reg cs 12)) as [lo|] eqn:Hlo; [|discriminate].
    destruct (xhi (kn cs) (reg cs 12)) as [hi|] eqn:Hhi; [|discriminate].
    apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
    pose proof (xlo_sound SEGS E _ (kn cs) _ lo HK Hlo). pose proof (xhi_sound SEGS E _ (kn cs) _ hi HK Hhi).
    unfold uE. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Theorem node_read_dir_sound : node1_stmt SEGS A nx0 LIMIT SINV argH FS0 always (fun cs => node_read_dir SEGS cs).
  Proof.
    intros cs cs' E R FULL model TT HC _ Hn Hk. cbv beta in Hn. unfold node_read_dir in Hn.
    pose proof (co_fds _ _ _ _ _ _ _ _ _ _ _ HC) as Hf.
    destruct (a_fd cs) as [|kb len off|] eqn:Efd; try discriminate.
    destruct (at_sys SEGS cs 63 && reg_is cs 10 3 && cnt_ok cs)%bool eqn:Hc; [|discriminate].
    destruct (dst_ok cs (reg cs 12)) as [[db dk]|] eqn:Hd; [|discriminate]. injection Hn as <-.
    apply andb_prop in Hc as [Hc Hcnt]. apply andb_prop in Hc as [Hsys H10].
    destruct (at_sys_facts E cs R FULL model 63 HC Hsys ltac:(unfold two64; lia)) as (Hp0 & Hp4 & [w [HF HE]] & H17).
    destruct (reg_is_getr E cs R FULL model 10 3 HC ltac:(lia) H10) as [G10 _].
    replace (Z_to_bv 5 (Z.of_nat 10)) with (10%bv : bv 5) in G10 by (apply bv_eq; reflexivity).
    destruct (dst_ok_sound E cs R FULL model _ _ _ HC Hd) as (G11 & D1 & D2 & D3 & Dst & DstM).
    pose proof (cnt_ok_sound E cs R FULL model HC Hcnt) as Hcn.
    pose proof (reg_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 12 HC ltac:(lia)) as G12.
    replace (Z_to_bv 5 (Z.of_nat 12)) with (12%bv : bv 5) in G12 by (apply bv_eq; reflexivity).
    cbn [fds_ok] in Hf.
    unfold cfg_of.
    eapply (srz_read_dir_lazy SEGS R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w (Z_to_bv 64 3) (uE E (reg cs 12)));
      [exact HF | exact HE | exact (co_halt _ _ _ _ _ _ _ _ _ _ _ HC) | exact H17 | exact G10
      | rewrite u64_lit by lia; lia | rewrite Hf; apply fd_lookup_fds3
      | rewrite G12; unfold uE; symmetry; apply Z_to_bv_bv_unsigned
      | lia | lia
      | rewrite G11; apply Dst; rewrite Z2Nat.id by lia; lia
      | rewrite G11, u64_lit by lia; unfold TASK_SIZE; lia |].
    rewrite (pc4 cs Hp0 Hp4).
    specialize (Hk E (regupd R 10%bv (errno_ret EISDIR)) FULL model (conj (env_agree_refl nx0 E) (env_agree_refl (nxt cs) E))).
    unfold cfg_of, pc in Hk. cbn [ret_simple ret_with a_ss mk_ss s_pc] in Hk. apply Hk; [|reflexivity].
    unfold ret_simple. rewrite Efd. apply cs_ok_rebuild with (model := model) (R := R) (FULL := FULL); try exact HC.
    - apply mdl_sim_refl.
    - exact (co_minv _ _ _ _ _ _ _ _ _ _ _ HC).
    - apply regs_ok_a0; [exact (co_regs _ _ _ _ _ _ _ _ _ _ _ HC) |].
      rewrite edenot_lit. unfold errno_ret, EISDIR. apply bv_eq. reflexivity.
    - exact (co_know _ _ _ _ _ _ _ _ _ _ _ HC).
    - cbn [fds_ok]. exact Hf.
    - intros; reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma file_read_nil_at_end : forall c (off cnt : word),
    Z.of_nat (length c) <= bv_unsigned off -> file_read c off cnt = [].
  Proof.
    intros c off cnt H. pose proof (length_file_read c off cnt) as L.
    destruct (file_read c off cnt) as [|b r]; [reflexivity|]. exfalso. cbn [length] in L.
    unfold word_to_nat in L. lia.
  Qed.

  Theorem node_read_eof_sound : node1_stmt SEGS A nx0 LIMIT SINV argH FS0 always (fun cs => node_read_eof SEGS cs).
  Proof.
    intros cs cs' E R FULL model TT HC _ Hn Hk. cbv beta in Hn. unfold node_read_eof in Hn.
    pose proof (co_fds _ _ _ _ _ _ _ _ _ _ _ HC) as Hf. pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
    destruct (a_fd cs) as [|kb len off|] eqn:Efd; try discriminate.
    lazymatch type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
    destruct (dst_ok cs (reg cs 12)) as [[db dk]|] eqn:Hd; [|discriminate]. injection Hn as <-.
    apply andb_prop in Hc as [Hc Hcap]. apply andb_prop in Hc as [Hc Hcnt]. apply andb_prop in Hc as [Hc Heq]. apply andb_prop in Hc as [Hsys H10].
    destruct (xhi (kn cs) len) as [lh|] eqn:Hlh; [|discriminate]. apply Z.ltb_lt in Hcap.
    pose proof (xhi_sound SEGS E _ (kn cs) len lh HK Hlh) as Blh.
    destruct (at_sys_facts E cs R FULL model 63 HC Hsys ltac:(unfold two64; lia)) as (Hp0 & Hp4 & [w [HF HE]] & H17).
    destruct (reg_is_getr E cs R FULL model 10 3 HC ltac:(lia) H10) as [G10 _].
    replace (Z_to_bv 5 (Z.of_nat 10)) with (10%bv : bv 5) in G10 by (apply bv_eq; reflexivity).
    destruct (dst_ok_sound E cs R FULL model _ _ _ HC Hd) as (G11 & D1 & D2 & D3 & Dst & DstM).
    pose proof (cnt_ok_sound E cs R FULL model HC Hcnt) as Hcn.
    pose proof (reg_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 12 HC ltac:(lia)) as G12.
    replace (Z_to_bv 5 (Z.of_nat 12)) with (12%bv : bv 5) in G12 by (apply bv_eq; reflexivity).
    pose proof (len_eqb_sound SEGS E _ (kn cs) off len HK Heq) as Hol.
    cbn [fds_ok] in Hf. destruct Hf as [p [c (Hf1 & Hf2 & Hf3 & Hf4 & Hf5)]].
    (* [comment removed for export] *)
    assert (Hnil : file_read c (edenot E off) (getr R 12%bv) = []).
    { apply file_read_nil_at_end. unfold uE in Hf3, Hf4, Blh. unfold flen, FCAP in *. rewrite Hol, Hf3. lia. }
    unfold cfg_of.
    eapply (srz_read_file_mat SEGS R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w (Z_to_bv 64 3) p (edenot E off) c (uE E (reg cs 12)));
      [exact HF | exact HE | exact (co_halt _ _ _ _ _ _ _ _ _ _ _ HC) | exact H17 | exact G10
      | rewrite u64_lit by lia; lia | rewrite Hf1; apply fd_lookup_fds3 | rewrite m_fs_with_fds || exact Hf2
      | rewrite G12; unfold uE; symmetry; apply Z_to_bv_bv_unsigned
      | lia | lia
      | rewrite G11; apply Dst; rewrite Z2Nat.id by lia; lia
      | rewrite G11, u64_lit by lia; unfold TASK_SIZE; lia | | ].
    - (* [comment removed for export] *)
      rewrite Hnil. cbn [delivered_writes write_accesses]. apply AsanAcct.materialize_model_accesses_nil.
    - rewrite Hnil. cbn [wbytes]. rewrite (pc4 cs Hp0 Hp4).
      set (model' := with_fds _ model).
      specialize (Hk E (regupd R 10%bv (len_word (@nil byte))) FULL model' (conj (env_agree_refl nx0 E) (env_agree_refl (nxt cs) E))).
      unfold cfg_of, pc in Hk. cbn [ret_simple ret_with a_ss mk_ss s_pc] in Hk. apply Hk; [|reflexivity].
      unfold ret_simple. rewrite ?Efd. apply cs_ok_rebuild with (model := model) (R := R) (FULL := FULL); try exact HC.
      + apply mdl_sim_with_fds.
      + apply MInv_with_fds. exact (co_minv _ _ _ _ _ _ _ _ _ _ _ HC).
      + apply regs_ok_a0; [exact (co_regs _ _ _ _ _ _ _ _ _ _ _ HC) | rewrite edenot_lit; reflexivity].
      + exact HK.
      + cbn [fds_ok]. exists p, c. unfold model'. rewrite m_fds_with_fds, m_fs_with_fds, Hf1, fd_insert_fds3.
        rewrite bv_add_0_r by reflexivity.
        rewrite <- Hol.
        repeat split; try assumption; unfold uE in *; lia.
      + intros; reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma len_av : 1 <= argc <= 1024.
  Proof. unfold argc. destruct Hva as [H _]. lia. Qed.
  Lemma len_ev : 0 <= envc <= 256.
  Proof. unfold envc. destruct Hve as [H _]. lia. Qed.
  Lemma usp_lo : 0x7fff80000000 <= usp.
  Proof. unfold usp. unfold sp_window_lo in Hsp_lo. lia. Qed.
  Lemma usp_hi : usp <= 0x800000000000.
  Proof. unfold usp. unfold sp_window_hi in Hsp_hi. lia. Qed.
  Lemma len_argv0 : Z.of_nat (length argv0) <= 131071.
  Proof. unfold argv0. apply (valid_argv_str_len argv 0 Hva). destruct Hva as [H _]. lia. Qed.
  Lemma len_argv1 : 2 <= argc -> Z.of_nat (length argv1) <= 131071.
  Proof. intros H. unfold argv1. apply (valid_argv_str_len argv 1 Hva). unfold argc in H. lia. Qed.
  Lemma argv1_nz : 2 <= argc -> ~ In (Z_to_bv 8 0) argv1.
  Proof. intros H. unfold argv1. apply (valid_argv_str_nz argv 1 Hva). unfold argc in H. lia. Qed.
  (* [comment removed for export] *)
  Lemma argv1_path_ok : 2 <= argc -> path_has_slash argv1 = false /\ argv1 <> dotdot_path.
  Proof. intros H2. unfold argv1. apply valid_argv_path1; [exact Hva | unfold argc in H2; lia]. Qed.

  Lemma bsb_nw : usp + Z.of_nat (length (build_stack_bytes ph sp argv envp uid hw rdraw)) < 2 ^ 64.
  Proof. unfold usp. apply lay_bsb_nw; assumption. Qed.

  Lemma STR1_eq : 2 <= argc -> cat_argv_ptr sp argv envp 1 = Z_to_bv 64 STR1.
  Proof.
    intros H2. pose proof len_av. pose proof len_ev. pose proof usp_lo. pose proof usp_hi. pose proof len_argv0.
    apply bv_eq. rewrite (u_cat_argv_ptr ph sp rdraw argv envp uid hw Hva Hve Hsp_lo Hsp_hi 1) by (unfold argc in H2; lia).
    rewrite u64_lit by (unfold STR1; lia).
    assert (Hf1 : forall l : list (list byte), l <> [] -> firstn 1 l = [nth 0 l []]) by (intros [|x l'] Hl; [congruence | reflexivity]).
    rewrite (Hf1 argv) by (intros Hn; unfold argc in H2; rewrite Hn in H2; cbn in H2; lia).
    rewrite total_arg_bytes_cons. change (total_arg_bytes_nat []) with 0%nat.
    unfold STR1, cat_struct_size, auxv_size, usp, argc, envc, argv0. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma rd_argv1 : forall M, 2 <= argc ->
    (forall a : word, STR1 <= bv_unsigned a <= STR1 + Z.of_nat (length argv1) -> M a = wrap_mem ph sp argv envp uid hw rdraw a) ->
    rdn SEGS M (Z_to_bv 64 STR1) (length argv1 + 1) = Some (argv1 ++ [Z_to_bv 8 0]).
  Proof.
    intros M H2 HM. pose proof len_av. pose proof len_ev. pose proof usp_lo. pose proof usp_hi. pose proof len_argv0. pose proof (len_argv1 H2).
    rewrite (rdn_ext SEGS (length argv1 + 1) M (wrap_mem ph sp argv envp uid hw rdraw)).
    - rewrite rdn_wrap_stack_above; [| rewrite u64_lit; unfold STR1 in *; lia | rewrite u64_lit; unfold STR1 in *; [rewrite Nat2Z.inj_add; cbn [Z.of_nat Pos.of_succ_nat]|]; lia].
      rewrite <- (STR1_eq H2). unfold argv1. apply read_argv_cstr_k; [unfold argc in H2; lia | exact bsb_nw].
    - rewrite u64_lit; unfold STR1 in *; [rewrite Nat2Z.inj_add; cbn [Z.of_nat Pos.of_succ_nat]|]; lia.
    - intros a Ha. rewrite u64_lit in Ha by (unfold STR1 in *; lia). rewrite Nat2Z.inj_add in Ha. cbn [Z.of_nat Pos.of_succ_nat] in Ha.
      apply HM. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma openat_args_sound : forall E cs R FULL model,
    cs_ok E cs R FULL model -> openat_args_ok SEGS cs = true ->
    0 <= pc cs /\ pc cs + 4 < two64
    /\ (exists w, fetch_word SEGS (Z_to_bv 64 (pc cs)) = Some w /\ is_ecall w = true)
    /\ getr R 17%bv = Z_to_bv 64 56
    /\ fd32 (getr R 10%bv) = AT_FDCWD32
    /\ getr R 11%bv = Z_to_bv 64 STR1
    /\ Z.ldiff (bv_unsigned (getr R 12%bv)) open_ignored_flags = 0
    /\ 2 <= argc
    /\ (forall a : word, STR1 <= bv_unsigned a <= STR1 + Z.of_nat (length argv1) -> FULL a = wrap_mem ph sp argv envp uid hw rdraw a)
    /\ m_fds model = fds_std
    /\ materialize_model_accesses model (path_reads SEGS R FULL) = Some model
    /\ (forall f, materialize_model_accesses (with_fds f model) (path_reads SEGS R FULL) = Some (with_fds f model)).
  Proof.
    intros E cs R FULL model HC H. unfold openat_args_ok in H.
    apply andb_prop in H as [H Hstd]. apply andb_prop in H as [H Hargc]. apply andb_prop in H as [H Hfl].
    apply andb_prop in H as [H H11]. apply andb_prop in H as [Hsys H10].
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK. pose proof (co_sinv _ _ _ _ _ _ _ _ _ _ _ HC) as HS.
    pose proof len_av as Lav. pose proof len_ev as Lev. pose proof usp_lo as U1. pose proof usp_hi as U2. pose proof len_argv0 as L0.
    destruct (at_sys_facts E cs R FULL model 56 HC Hsys ltac:(unfold two64; lia)) as (Hp0 & Hp4 & Hw & H17).
    destruct (H_vals E FULL HS) as (Vargc & Vstr1 & _).
    (* [comment removed for export] *)
    destruct (xlo (kn cs) (EVar V_ARGC)) as [alo|] eqn:Halo; [|discriminate Hargc]. apply Z.leb_le in Hargc.
    pose proof (xlo_sound SEGS E _ (kn cs) (EVar V_ARGC) alo HK Halo) as Bargc. cbn [edenot] in Bargc.
    rewrite Vargc, u64_lit in Bargc by lia.
    assert (Hargc2 : 2 <= argc) by lia. specialize (Vstr1 Hargc2). pose proof (len_argv1 Hargc2) as L1.
    (* [comment removed for export] *)
    destruct (reg_lit cs 10) as [z10|] eqn:Hr10; [|discriminate H10]. apply Z.eqb_eq in H10.
    destruct (reg_lit_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 10 z10 HC ltac:(lia) Hr10) as [G10 Hz10].
    replace (Z_to_bv 5 (Z.of_nat 10)) with (10%bv : bv 5) in G10 by (apply bv_eq; reflexivity).
    (* [comment removed for export] *)
    pose proof (len_eqb_sound SEGS E _ (kn cs) (reg cs 11) e_str1 HK H11) as H11e.
    pose proof (reg_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 11 HC ltac:(lia)) as G11.
    replace (Z_to_bv 5 (Z.of_nat 11)) with (11%bv : bv 5) in G11 by (apply bv_eq; reflexivity).
    rewrite H11e in G11.
    assert (G11' : getr R 11%bv = Z_to_bv 64 STR1).
    { rewrite G11. apply bv_eq. unfold uE in Vstr1. rewrite Vstr1, u64_lit by (unfold STR1; lia). reflexivity. }
    (* [comment removed for export] *)
    destruct (reg_lit cs 12) as [z12|] eqn:Hr12; [|discriminate Hfl]. apply Z.eqb_eq in Hfl.
    destruct (reg_lit_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 12 z12 HC ltac:(lia) Hr12) as [G12 Hz12].
    replace (Z_to_bv 5 (Z.of_nat 12)) with (12%bv : bv 5) in G12 by (apply bv_eq; reflexivity).
    (* [comment removed for export] *)
    pose proof (co_fds _ _ _ _ _ _ _ _ _ _ _ HC) as Hf. destruct (a_fd cs); try discriminate Hstd. cbn [fds_ok] in Hf.
    (* [comment removed for export] *)
    assert (ATOPio : alloc_top (m_vmmaps model) = usp - 8388608).
    { destruct (H_vals E FULL (co_sinv _ _ _ _ _ _ _ _ _ _ _ HC)) as (_ & _ & Vsp).
      pose proof (cs_sp0 SEGS A LIMIT SINV argH FS0 E cs R FULL model HC) as Hsp0. rewrite Vsp in Hsp0.
      unfold alloc_top, stack_max_size. lia. }
    assert (MAT : forall m, m_vm_lazy m = m_vm_lazy model -> materialize_model_accesses m (path_reads SEGS R FULL) = Some m).
    { intros m Hm. apply (materialize_above_lazy m (alloc_top (m_vmmaps model))).
      - rewrite Hm. eapply Forall_impl; [|exact (co_lazyb _ _ _ _ _ _ _ _ _ _ _ HC)]. intros iv [_ Hiv]. exact Hiv.
      - unfold path_reads. constructor; [|constructor]. cbn [fst snd]. rewrite G11', u64_lit by (unfold STR1; lia).
        pose proof (cstr_access_len_aux_le (mrb SEGS FULL) (Z_to_bv 64 STR1) path_max). unfold path_max in *. rewrite ATOPio. unfold STR1 in *. lia. }
    split; [exact Hp0|]. split; [exact Hp4|]. split; [exact Hw|]. split; [exact H17|].
    split. { rewrite G10. apply bv_eq. unfold fd32, abi_low32, AT_FDCWD32, AT_FDCWD. rewrite !Z_to_bv_unsigned.
             unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite (Z.mod_small z10) by (unfold two64 in Hz10; lia).
             rewrite H10. reflexivity. }
    split; [exact G11'|].
    split. { rewrite G12, u64_lit by (unfold two64 in Hz12; lia). exact Hfl. }
    split; [exact Hargc2|].
    split. { intros a Ha. eapply H_str1; [exact HS | exact Hargc2 | exact Ha]. }
    split; [exact Hf|].
    split; [apply MAT; reflexivity|].
    intros f. apply MAT. reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Theorem node_openat_err_sound : node1_stmt SEGS A nx0 LIMIT SINV argH FS0 always (fun cs => node_openat_err SEGS T cs).
  Proof.
    intros cs cs' E R FULL model TT HC _ Hn Hk. cbv beta in Hn. unfold node_openat_err in Hn.
    destruct (openat_args_ok SEGS cs) eqn:Hargs; [|discriminate].
    destruct (openat_args_sound E cs R FULL model HC Hargs)
      as (Hp0 & Hp4 & [w [HF HE]] & H17 & H10 & H11 & H12 & Hargc2 & Hmem & Hfds & Hmat0 & Hmat1).
    pose proof (len_argv1 Hargc2) as L1. pose proof (argv1_nz Hargc2) as NZ1.
    pose proof (rd_argv1 FULL Hargc2 Hmem) as RD. rewrite <- H11 in RD.
    pose proof (co_fs _ _ _ _ _ _ _ _ _ _ _ HC) as Hfs.
    assert (POST : forall (e : Z) T0, cs' = ret_simple cs (ELit (two64 - e)) -> 0 < e < 100 ->
              (forall E' R' FULL' model', env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' cs' R' FULL' model' -> m_fs model' = m_fs model ->
                 srealizes SEGS (cfg R' (pc cs') FULL' model') T0) ->
              srealizes SEGS (mkCfg (mkst (regupd R 10%bv (errno_ret e)) (v_addi (Z_to_bv 64 (pc cs)) 4) FULL (seg_rom SEGS)) model) T0).
    { intros e T0 -> He Hk0. rewrite (pc4 cs Hp0 Hp4).
      specialize (Hk0 E (regupd R 10%bv (errno_ret e)) FULL model (conj (env_agree_refl nx0 E) (env_agree_refl (nxt cs) E))).
      unfold cfg_of, pc in Hk0. cbn [ret_simple ret_with a_ss mk_ss s_pc] in Hk0. apply Hk0; [|reflexivity].
      unfold ret_simple. apply cs_ok_rebuild with (model := model) (R := R) (FULL := FULL); try exact HC.
      - apply mdl_sim_refl.
      - exact (co_minv _ _ _ _ _ _ _ _ _ _ _ HC).
      - apply regs_ok_a0; [exact (co_regs _ _ _ _ _ _ _ _ _ _ _ HC) |].
        rewrite edenot_lit. unfold errno_ret. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
        change (bv_modulus 64) with (2 ^ 64). unfold two64.
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
        rewrite (Z.mod_small (2 ^ 64 - e)) by lia.
        replace (- e) with ((2 ^ 64 - e) + (-1) * 2 ^ 64) by lia. rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. reflexivity.
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
      - exact (co_know _ _ _ _ _ _ _ _ _ _ _ HC).
      - exact (co_fds _ _ _ _ _ _ _ _ _ _ _ HC).
      - intros; reflexivity. }
    unfold cfg_of.
    destruct (io_open T) as [| | | |lo hi] eqn:Eo; try discriminate.
    - (* [comment removed for export] *)
      injection Hn as <-.
      eapply (srz_openat_toolong_lazy SEGS R (Z_to_bv 64 (pc cs)) FULL model w HF HE (co_halt _ _ _ _ _ _ _ _ _ _ _ HC) H17 H10 H12 Hmat0
                (firstn 4096 (argv1 ++ [Z_to_bv 8 0]))).
      + eapply rdn_firstn; [exact RD | lia].
      + rewrite firstn_app, (proj2 (Nat.sub_0_le _ _)) by lia. cbn [firstn]. rewrite app_nil_r.
        intros Hin. apply NZ1. eapply firstn_In'; exact Hin.
      + apply (POST 36); [reflexivity | lia | exact Hk].
    - (* [comment removed for export] *)
      injection Hn as <-.
      destruct argv1 as [|b1 r1] eqn:Ea1.
      + eapply (srz_openat_empty_lazy SEGS R (Z_to_bv 64 (pc cs)) FULL model w HF HE (co_halt _ _ _ _ _ _ _ _ _ _ _ HC) H17 H10 H12 Hmat0).
        * split; [cbn; lia|]. split; [intros []|]. exact RD.
        * apply (POST 2); [reflexivity | lia | exact Hk].
      + destruct H_open as [Hnil | (Hnd & Hlen & Hlk)]; [discriminate|].
        eapply (srz_openat_absent_lazy SEGS R (Z_to_bv 64 (pc cs)) FULL model w HF HE (co_halt _ _ _ _ _ _ _ _ _ _ _ HC) H17 H10 H12 Hmat0 (b1 :: r1)).
        * split; [exact Hlen|]. split; [exact NZ1 | exact RD].
        * discriminate.
        * exact Hnd.
        * pose proof (argv1_path_ok Hargc2) as [_ X]. rewrite Ea1 in X. exact X.
        * pose proof (argv1_path_ok Hargc2) as [X _]. rewrite Ea1 in X. exact X.
        * rewrite Hfs. exact Hlk.
        * apply (POST 2); [reflexivity | lia | exact Hk].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma openat_errno_range : forall e, In e openat_errnos ->
    two64 - 24 <= bv_unsigned (errno_ret e) <= two64 - 12.
  Proof.
    intros e He. unfold openat_errnos, ENOMEM, EACCES, EMFILE, ENFILE in He. cbn [In] in He.
    unfold errno_ret, two64.
    destruct He as [<-|[<-|[<-|[<-|[]]]]]; (split; [apply Z.leb_le | apply Z.leb_le]; vm_compute; reflexivity).
  Qed.

  Theorem node_openat2_sound : forall cs csa csb E R FULL model TA TB,
    cs_ok E cs R FULL model -> node_openat2 SEGS nx0 T cs = Some (csa, csb) ->
    (forall E' R' FULL' model', env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' csa R' FULL' model' -> m_fs model' = m_fs model ->
        srealizes SEGS (cfg R' (pc csa) FULL' model') TA) ->
    (forall E' R' FULL' model', env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' csb R' FULL' model' -> m_fs model' = m_fs model ->
        srealizes SEGS (cfg R' (pc csb) FULL' model') TB) ->
    srealizes SEGS (cfg R (pc cs) FULL model) (t_alt2 TA TB).
  Proof.
    intros cs csa csb E R FULL model TA TB HC Hn HkA HkB. unfold node_openat2 in Hn.
    assert (Hshape : exists lohi : option (Z * Z),
              match io_open T with ODir => lohi = None | OFile lo hi => lohi = Some (lo, hi) | _ => False end
              /\ (openat_args_ok SEGS cs && fresh_ok nx0 cs)%bool = true
              /\ csa = ret_with cs (EVar (nxt cs)) (KRange (EVar (nxt cs)) (two64 - 24) (two64 - 12) :: kn cs) (N.succ (nxt cs)) FdStd
              /\ csb = match lohi with
                       | Some (lo, hi) => ret_with cs (ELit 3) (KRange (EVar (nxt cs)) (Z.max lo 0) (Z.min hi FCAP) :: kn cs) (N.succ (nxt cs))
                                                  (FdFile (io_blob T) (EVar (nxt cs)) (ELit 0))
                       | None => ret_with cs (ELit 3) (kn cs) (N.succ (nxt cs)) FdDir
                       end).
    { destruct (io_open T) as [| | | |lo hi]; try discriminate;
        destruct (openat_args_ok SEGS cs && fresh_ok nx0 cs)%bool; try discriminate;
        injection Hn as <- <-; [exists None | exists (Some (lo, hi))]; repeat split; reflexivity. }
    clear Hn. destruct Hshape as (lohi & Hcase & Hc & -> & ->).
    apply andb_prop in Hc as [Hargs Hfresh].
    destruct (openat_args_sound E cs R FULL model HC Hargs)
      as (Hp0 & Hp4 & [w [HF HE]] & H17 & H10 & H11 & H12 & Hargc2 & Hmem & Hfds & Hmat0 & Hmat1).
    pose proof (len_argv1 Hargc2) as L1. pose proof (argv1_nz Hargc2) as NZ1.
    pose proof (rd_argv1 FULL Hargc2 Hmem) as RD. rewrite <- H11 in RD.
    pose proof (co_fs _ _ _ _ _ _ _ _ _ _ _ HC) as Hfs. pose proof (co_sinv _ _ _ _ _ _ _ _ _ _ _ HC) as HS.
    destruct (fresh_ok_parts nx0 cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
    set (v := nxt cs) in *.
    assert (Hfree : fd_lookup (m_fds model) (alloc_fd (m_fds model)) = None) by (rewrite Hfds; reflexivity).
    assert (Halloc : alloc_fd (m_fds model) = Z_to_bv 64 3) by (rewrite Hfds; reflexivity).
    (* [comment removed for export] *)
    assert (ERR : forall e, In e openat_errnos ->
              srealizes SEGS (mkCfg (mkst (regupd R 10%bv (errno_ret e)) (v_addi (Z_to_bv 64 (pc cs)) 4) FULL (seg_rom SEGS)) model) TA).
    { intros e He. rewrite (pc4 cs Hp0 Hp4).
      set (E' := ext1 E v (errno_ret e)).
      assert (Hag : env_agree v E E') by apply ext1_agree.
      pose proof (cs_ok_agree SEGS A nx0 LIMIT nx0_ge7 SINV argH argH_agree SINV_agree FS0 E E' cs R FULL model Hag Hfresh HC) as HC'.
      specialize (HkA E' (regupd R 10%bv (errno_ret e)) FULL model (conj (env_agree_le nx0 v E E' Hag Fle) Hag)).
      unfold cfg_of, pc in HkA. cbn [ret_with a_ss mk_ss s_pc] in HkA. apply HkA; [|reflexivity].
      apply cs_ok_rebuild with (model := model) (R := R) (FULL := FULL); try exact HC'.
      - apply mdl_sim_refl.
      - exact (co_minv _ _ _ _ _ _ _ _ _ _ _ HC').
      - apply regs_ok_a0; [exact (co_regs _ _ _ _ _ _ _ _ _ _ _ HC') | cbn [edenot]; unfold E'; apply ext1_at].
      - constructor; [|exact (co_know _ _ _ _ _ _ _ _ _ _ _ HC')].
        cbn [kentry_ok edenot]. unfold E'. rewrite ext1_at. apply openat_errno_range. exact He.
      - cbn [fds_ok]. exact Hfds.
      - intros; reflexivity. }
    unfold cfg_of.
    destruct (io_open T) as [| | | |lo hi] eqn:Eo; try contradiction; subst lohi.
    - (* [comment removed for export] *)
      eapply (srz_openat_dot_lazy SEGS R (Z_to_bv 64 (pc cs)) FULL model w HF HE (co_halt _ _ _ _ _ _ _ _ _ _ _ HC) H17 H10 H12 Hmat0 Hfree Hmat1).
      + rewrite H_open in NZ1, RD. split; [cbn; lia|]. split; [exact NZ1 | exact RD].
      + exact ERR.
      + rewrite Halloc, (pc4 cs Hp0 Hp4), Hfds, fd_insert_std3.
        specialize (HkB E (regupd R 10%bv (Z_to_bv 64 3)) FULL (with_fds (fds3 State.FdDir) model) (conj (env_agree_refl nx0 E) (env_agree_refl (nxt cs) E))).
        unfold cfg_of, pc in HkB. cbn [ret_with a_ss mk_ss s_pc] in HkB. apply HkB; [|reflexivity].
        apply cs_ok_rebuild with (model := model) (R := R) (FULL := FULL); try exact HC.
        * apply mdl_sim_with_fds.
        * apply MInv_with_fds. exact (co_minv _ _ _ _ _ _ _ _ _ _ _ HC).
        * apply regs_ok_a0; [exact (co_regs _ _ _ _ _ _ _ _ _ _ _ HC) | rewrite edenot_lit; reflexivity].
        * exact (co_know _ _ _ _ _ _ _ _ _ _ _ HC).
        * cbn [fds_ok]. reflexivity.
        * intros; reflexivity.
    - (* [comment removed for export] *)
      destruct H_open as [c (Hne & Hnd & Hlen & Hlk & Hflen & Hblob & Hhdr)].
      eapply (srz_openat_file_lazy SEGS R (Z_to_bv 64 (pc cs)) FULL model w HF HE (co_halt _ _ _ _ _ _ _ _ _ _ _ HC) H17 H10 H12 Hmat0 Hfree Hmat1 argv1 c).
      + split; [exact Hlen|]. split; [exact NZ1 | exact RD].
      + exact Hne.
      + exact Hnd.
      + exact (proj2 (argv1_path_ok Hargc2)).
      + exact (proj1 (argv1_path_ok Hargc2)).
      + rewrite Hfs. exact Hlk.
      + exact ERR.
      + rewrite Halloc, (pc4 cs Hp0 Hp4), Hfds, fd_insert_std3.
        set (E' := ext1 E v (Z_to_bv 64 (flen c))).
        assert (Hag : env_agree v E E') by apply ext1_agree.
        pose proof (cs_ok_agree SEGS A nx0 LIMIT nx0_ge7 SINV argH argH_agree SINV_agree FS0 E E' cs R FULL model Hag Hfresh HC) as HC'.
        assert (Hv : edenot E' (EVar v) = Z_to_bv 64 (flen c)) by (cbn [edenot]; unfold E'; apply ext1_at).
        assert (Hflen' : 0 <= flen c <= 2 ^ 26) by (unfold flen; lia).
        specialize (HkB E' (regupd R 10%bv (Z_to_bv 64 3)) FULL (with_fds (fds3 (State.FdFile argv1 (Z_to_bv 64 0))) model)
                      (conj (env_agree_le nx0 v E E' Hag Fle) Hag)).
        unfold cfg_of, pc in HkB. cbn [ret_with a_ss mk_ss s_pc] in HkB. apply HkB; [|reflexivity].
        apply cs_ok_rebuild with (model := model) (R := R) (FULL := FULL); try exact HC'.
        * apply mdl_sim_with_fds.
        * apply MInv_with_fds. exact (co_minv _ _ _ _ _ _ _ _ _ _ _ HC').
        * apply regs_ok_a0; [exact (co_regs _ _ _ _ _ _ _ _ _ _ _ HC') | rewrite edenot_lit; reflexivity].
        * constructor; [|exact (co_know _ _ _ _ _ _ _ _ _ _ _ HC')].
          cbn [kentry_ok]. rewrite Hv, u64_lit by lia. unfold FCAP. lia.
        * cbn [fds_ok]. exists argv1, c. rewrite m_fds_with_fds, m_fs_with_fds, edenot_lit, Hfs. unfold uE. rewrite Hv, edenot_lit, !u64_lit by lia.
          split; [reflexivity|]. split; [exact Hlk|]. split; [reflexivity|]. split; [lia|].
          intros j Hj. unfold E'. cbn [eb ext1]. apply (Hblob E FULL HS j Hj).
        * intros; reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma file_read_chunk : forall c (off : word) j,
    bv_unsigned off = 65536 * Z.of_nat j ->
    file_read c off (Z_to_bv 64 65536) = chunk j c.
  Proof.
    intros c off j Hoff. rewrite file_read_unguarded. unfold chunk, CH, word_to_nat. rewrite Hoff, u64_lit by lia.
    f_equal. f_equal. lia.
  Qed.

  Lemma length_chunk : forall c j, length (chunk j c) = Nat.min (Z.to_nat 65536) (length c - Z.to_nat 65536 * j)%nat.
  Proof. intros c j. unfold chunk, CH. rewrite firstn_length, length_skipn. reflexivity. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma know_ok_havoc_img : forall E M M' k b o n,
    know_ok SEGS E M k ->
    (forall x : word, (bv_unsigned x < estart E (SA b o) \/ estart E (SA b o) + elenZ E n <= bv_unsigned x)%Z -> M' x = M x) ->
    mem_grows M M' ->
    know_ok SEGS E M' (kn_havoc_img k b o n).
  Proof.
    intros E M M' k b o n HK Hout Hg. unfold kn_havoc_img.
    destruct b as [z| | | | | | |]; try (eapply know_ok_havoc; eassumption).
    destruct z; try (eapply know_ok_havoc; eassumption).
    destruct n as [nz| | | | | | |]; try (eapply know_ok_havoc; eassumption).
    eapply know_ok_havoc; [apply AsanNodesAux.kimg_cut_sound; exact HK | exact Hout | exact Hg].
  Qed.

  Lemma read_deliver_sound : forall E cs R FULL model TT kb len off p c bs (r : expr) knew (off' : expr) (db : expr) (dk : Z),
    cs_ok E cs R FULL model ->
    a_fd cs = FdFile kb len off ->
    at_sys SEGS cs 63 = true -> reg_is cs 10 3 = true -> reg_is cs 12 CHZ = true ->
    dst_ok cs (ELit CHZ) = Some (db, dk) ->
    m_fds model = fds3 (State.FdFile p (edenot E off)) -> fs_lookup (m_fs model) p = Some c ->
    file_read c (edenot E off) (Z_to_bv 64 65536) = bs ->
    (Z.of_nat (length bs) <= 65536)%Z ->
    edenot E r = len_word bs ->
    edenot E off' = (edenot E off + len_word bs)%bv ->
    uE E off' <= uE E len ->
    (forall M', (forall i, 0 <= i < Z.of_nat (length bs) -> M' (Z_to_bv 64 (estart E (SA db dk) + i)) = Some (nth (Z.to_nat i) bs (Z_to_bv 8 0))) ->
                know_ok SEGS E M' (kn_havoc_img (kn cs) db dk (ELit CHZ)) -> know_ok SEGS E M' (knew ++ kn_havoc_img (kn cs) db dk (ELit CHZ))) ->
    (forall E' R' FULL' model', env_agree nx0 E E' /\ env_agree (nxt cs) E E' ->
        cs_ok E' (ret_with cs r (knew ++ kn_havoc_img (kn cs) db dk (ELit CHZ)) (nxt cs) (FdFile kb len off')) R' FULL' model' ->
        m_fs model' = m_fs model -> srealizes SEGS (cfg R' (pc cs + 4) FULL' model') TT) ->
    srealizes SEGS (cfg R (pc cs) FULL model) TT.
  Proof.
    intros E cs R FULL model TT kb len off p c bs r knew off' db dk HC Efd Hsys H10 H12 Hd Hfds Hlk Hbs Hlen Hr Hoff' Hle Hknew Hk.
    destruct (at_sys_facts E cs R FULL model 63 HC Hsys ltac:(unfold two64; lia)) as (Hp0 & Hp4 & [w [HF HE]] & H17).
    destruct (reg_is_getr E cs R FULL model 10 3 HC ltac:(lia) H10) as [G10 _].
    replace (Z_to_bv 5 (Z.of_nat 10)) with (10%bv : bv 5) in G10 by (apply bv_eq; reflexivity).
    destruct (reg_is_getr E cs R FULL model 12 CHZ HC ltac:(lia) H12) as [G12 _].
    replace (Z_to_bv 5 (Z.of_nat 12)) with (12%bv : bv 5) in G12 by (apply bv_eq; reflexivity). unfold CHZ in G12.
    destruct (dst_ok_sound E cs R FULL model _ _ _ HC Hd) as (G11 & D1 & D2 & D3 & Dst & DstM).
    unfold uE in D2, D3, Dst, DstM. rewrite edenot_lit, u64_lit in D2, D3, Dst, DstM by (unfold CHZ; lia). unfold CHZ in D2, D3, Dst, DstM.
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
    set (dst := estart E (SA db dk)) in *.
    (* [comment removed for export] *)
    assert (VIS : forall i, 0 <= i < Z.of_nat (length bs) -> hid A argH E cs model (Z_to_bv 64 (dst + i)) = false).
    { intros i Hi. apply (store_ok_Mr_visible E cs model FULL dst (Z.to_nat 65536)); try lia. apply DstM. lia. }
    (* [comment removed for export] *)
    set (m1 := with_fds (fd_insert (m_fds model) (Z_to_bv 64 3) (State.FdFile p (edenot E off + len_word bs)%bv)) model).
    assert (Hcov : lazy_cover (hid A argH E cs model) (m_vm_lazy m1) (allowA A E cs)).
    { unfold m1. rewrite with_fds_lazy. exact (lazy_cover_hid SEGS A LIMIT SINV argH FS0 HULL_ok E cs R FULL model HC). }
    assert (Hinv1 : MInv (allowA A E cs) m1) by (unfold m1; apply MInv_with_fds; exact (co_minv _ _ _ _ _ _ _ _ _ _ _ HC)).
    assert (Hav : ranges_avoid (hid A argH E cs model) (write_accesses (delivered_writes (getr R 11%bv) bs))).
    { destruct bs as [|b0 bs']; cbn [delivered_writes write_accesses map fst snd]; [apply ranges_avoid_nil|].
      apply ranges_avoid_cons; [|apply ranges_avoid_nil]. rewrite G11.
      apply range_avoids_by_addr; [lia | lia |]. intros x Hx [Hlo Hhi]. 
      pose proof (VIS (bv_unsigned x - dst) ltac:(lia)) as V.
      replace (Z_to_bv 64 (dst + (bv_unsigned x - dst))) with x in V by (apply bv_eq; rewrite u64_lit by lia; lia).
      rewrite V in Hx. discriminate. }
    destruct (materialize_restricted (hid A argH E cs model) (allowA A E cs) m1 _ Hcov (A_wf_allowA' A E cs) Hinv1 Hav) as [mat' [Hmat Hinv']].
    set (m2 := with_vm_backing (m_vm_lazy m1) mat' m1) in *.
    assert (Hsame : same_but_materialized m1 m2) by (unfold m2; apply with_vm_backing_same).
    pose proof (same_but_materialized_frame _ _ Hsame) as Hfr.
    unfold cfg_of.
    eapply (srz_read_file_mat SEGS R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS) model w (Z_to_bv 64 3) p (edenot E off) c 65536 m2);
      [exact HF | exact HE | exact (co_halt _ _ _ _ _ _ _ _ _ _ _ HC) | exact H17 | exact G10
      | rewrite u64_lit by lia; lia | rewrite Hfds; apply fd_lookup_fds3 | exact Hlk | exact G12
      | lia | lia
      | rewrite G11; apply Dst; rewrite Z2Nat.id by lia; lia
      | rewrite G11, u64_lit by lia; unfold TASK_SIZE; lia | | ].
    - rewrite G12, Hbs. exact Hmat.
    - rewrite G12, Hbs, (pc4 cs Hp0 Hp4).
      specialize (Hk E (regupd R 10%bv (len_word bs)) (wbytes FULL (getr R 11%bv) bs) m2 (conj (env_agree_refl nx0 E) (env_agree_refl (nxt cs) E))).
      unfold cfg_of in Hk. apply Hk; [| unfold m2; replace (m_fs (with_vm_backing _ _ _)) with (m_fs m1) by (symmetry; apply Hfr); reflexivity].
      apply cs_ok_rebuild with (model := model) (R := R) (FULL := FULL); try exact HC.
      + eapply mdl_sim_trans; [apply (mdl_sim_with_fds (fd_insert (m_fds model) (Z_to_bv 64 3) (State.FdFile p (edenot E off + len_word bs)%bv))) | apply mdl_sim_materialized; exact Hsame].
      + exact Hinv'.
      + apply regs_ok_a0; [exact (co_regs _ _ _ _ _ _ _ _ _ _ _ HC) | exact Hr].
      + apply Hknew.
        * intros i Hi. unfold mrestrict. rewrite (VIS i Hi). rewrite G11. apply wbytes_nth_off; lia.
        * apply (know_ok_havoc_img E (Mr A argH E cs model FULL)).
          -- exact HK.
          -- intros x Hx. unfold Mr, mrestrict. destruct (hid A argH E cs model x); [reflexivity|].
             rewrite G11. unfold elenZ in Hx. rewrite edenot_lit, u64_lit in Hx by (unfold CHZ; lia). unfold CHZ in Hx. fold dst in Hx.
             destruct Hx as [Hx|Hx]; [apply wbytes_below | apply wbytes_above]; rewrite ?u64_lit by lia; lia.
          -- intros x Hx. unfold Mr, mrestrict in *. destruct (hid A argH E cs model x); [exact Hx|]. apply wbytes_grows. exact Hx.
      + cbn [fds_ok]. exists p, c.
        replace (m_fds m2) with (m_fds m1) by (symmetry; apply Hfr).
        replace (m_fs m2) with (m_fs m1) by (symmetry; apply Hfr).
        unfold m1. rewrite m_fds_with_fds, m_fs_with_fds, Hfds, fd_insert_fds3, Hoff'.
        pose proof (co_fds _ _ _ _ _ _ _ _ _ _ _ HC) as Hf. rewrite Efd in Hf. cbn [fds_ok] in Hf.
        destruct Hf as [p' [c' (F1 & F2 & F3 & F4 & F5)]].
        rewrite Hfds in F1. injection F1 as <-. rewrite Hlk in F2. injection F2 as <-.
        repeat split; try assumption; reflexivity.
      + intros a Ha. destruct (Z_lt_le_dec (bv_unsigned a) dst) as [Hlt|Hge]; [|destruct (Z_lt_le_dec (bv_unsigned a) (dst + Z.of_nat (length bs))) as [Hin|Hout]].
        * rewrite G11. apply wbytes_below; rewrite ?u64_lit by lia; lia.
        * exfalso. pose proof (VIS (bv_unsigned a - dst) ltac:(lia)) as V.
          replace (Z_to_bv 64 (dst + (bv_unsigned a - dst))) with a in V by (apply bv_eq; rewrite u64_lit by lia; lia).
          rewrite V in Ha. discriminate.
        * rewrite G11. apply wbytes_above. rewrite u64_lit by lia. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma u_len_word : forall bs : list byte, (Z.of_nat (length bs) < 2 ^ 64)%Z -> bv_unsigned (len_word bs) = Z.of_nat (length bs).
  Proof. intros bs H. rewrite len_word_of_nat. apply u64_lit. lia. Qed.

  (* [comment removed for export] *)
  Lemma fdfile_facts : forall E cs R FULL model kb len off,
    cs_ok E cs R FULL model -> a_fd cs = FdFile kb len off ->
    exists p c, m_fds model = fds3 (State.FdFile p (edenot E off)) /\ fs_lookup (m_fs model) p = Some c
      /\ uE E len = flen c /\ uE E off <= uE E len
      /\ (forall j, 65536 * Z.of_nat j < 2 ^ 26 -> eb E (kb + j)%nat = chunk j c).
  Proof. intros E cs R FULL model kb len off HC Efd. pose proof (co_fds _ _ _ _ _ _ _ _ _ _ _ HC) as Hf. rewrite Efd in Hf. exact Hf. Qed.

  Theorem node_read_sound : forall args, node1_stmt SEGS A nx0 LIMIT SINV argH FS0 always (fun cs => node_read SEGS cs args).
  Proof.
    intros args cs cs' E R FULL model TT HC _ Hn Hk. cbv beta in Hn. unfold node_read in Hn.
    destruct args as [|[jz| | | | | | |] [|? ?]]; try discriminate.
    destruct (a_fd cs) as [|kb len off|] eqn:Efd; try discriminate.
    lazymatch type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
    destruct (dst_ok cs (ELit CHZ)) as [[db dk]|] eqn:Hd; [|discriminate].
    destruct (xlo (kn cs) len) as [llo|] eqn:Hllo; [|discriminate].
    destruct (xhi (kn cs) len) as [lhi|] eqn:Hlhi; [|discriminate].
    apply andb_prop in Hc as [Hc Hcap]. apply andb_prop in Hc as [Hc Hoff]. apply andb_prop in Hc as [Hc Hj0].
    apply andb_prop in Hc as [Hc H12]. apply andb_prop in Hc as [Hsys H10].
    apply Z.leb_le in Hcap. apply Z.leb_le in Hj0.
    destruct (lit_of off) as [o|] eqn:Hlit; [|discriminate]. apply Z.eqb_eq in Hoff. subst o.
    destruct (lit_of_sound E off (CHZ * jz) Hlit) as [Eoff _].
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
    pose proof (xlo_sound SEGS E _ (kn cs) len llo HK Hllo) as Bllo. pose proof (xhi_sound SEGS E _ (kn cs) len lhi HK Hlhi) as Blhi.
    destruct (fdfile_facts E cs R FULL model kb len off HC Efd) as [p [c (F1 & F2 & F3 & F4 & F5)]].
    destruct (dst_ok_sound E cs R FULL model _ _ _ HC Hd) as (G11 & D1 & D2 & D3 & Dst & DstM).
    unfold uE in D2, D3. rewrite edenot_lit, u64_lit in D2, D3 by (unfold CHZ; lia). unfold CHZ in D2, D3.
    set (j := Z.to_nat jz).
    assert (Hj : 65536 * Z.of_nat j = CHZ * jz) by (unfold j, CHZ; lia).
    assert (Hoffu : bv_unsigned (edenot E off) = 65536 * Z.of_nat j) by (rewrite Eoff, u64_lit; unfold CHZ, FCAP in *; lia).
    pose proof (file_read_chunk c (edenot E off) j Hoffu) as Hbs.
    pose proof (F5 j ltac:(unfold CHZ, FCAP in *; lia)) as Hblob.
    pose proof (length_chunk c j) as Lbs.
    unfold uE, flen in F3. unfold CHZ, FCAP in *.
    destruct (Z.leb (65536 * (jz + 1)) llo) eqn:Hfull.
    - (* [comment removed for export] *)
      apply Z.leb_le in Hfull. injection Hn as <-.
      assert (Lfull : length (chunk j c) = Z.to_nat 65536) by (rewrite Lbs; lia).
      eapply (read_deliver_sound E cs R FULL model TT kb len off p c (chunk j c) (ELit 65536) [KBlob (SA db dk) (ELit 65536) (kb + j)%nat] (ELit (65536 * (jz + 1))) db dk
                HC Efd Hsys H10 H12 Hd F1 F2 Hbs); try (rewrite Lfull; lia).
      + rewrite edenot_lit, len_word_of_nat, Lfull. reflexivity.
      + rewrite !edenot_lit, len_word_of_nat, Lfull, Eoff. apply bv_eq. rewrite bv_add_unsigned, !u64_lit by lia.
        unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia. lia.
      + unfold uE. rewrite edenot_lit, u64_lit by lia. lia.
      + intros M' HM' HKh. constructor; [|exact HKh]. cbn [kentry_ok].
        split; [unfold flat, elenZ; rewrite edenot_lit, u64_lit by lia; lia|].
        split; [rewrite Hblob, Lfull; unfold elenZ; rewrite edenot_lit, u64_lit by lia; lia|].
        intros i Hi. unfold elenZ in Hi. rewrite edenot_lit, u64_lit in Hi by lia. rewrite Hblob. apply HM'. rewrite Lfull. lia.
      + intros E' R' FULL' model' Hag HC' Hfs. apply (Hk E' R' FULL' model' Hag); [exact HC' | exact Hfs].
    - destruct (Z.leb (65536 * jz) llo && Z.ltb lhi (65536 * (jz + 1)))%bool eqn:Hshort; [|discriminate].
      apply andb_prop in Hshort as [S1 S2]. apply Z.leb_le in S1. apply Z.ltb_lt in S2. injection Hn as <-.
      assert (Lshort : Z.of_nat (length (chunk j c)) = Z.of_nat (length c) - 65536 * jz) by (rewrite Lbs; lia).
      set (n := esub len (ELit (65536 * jz))).
      assert (Hn_u : bv_unsigned (edenot E n) = Z.of_nat (length c) - 65536 * jz).
      { unfold n, esub. rewrite mkAlu_denot, u_sub64, edenot_lit, u64_lit by lia. rewrite Z.mod_small by lia. lia. }
      eapply (read_deliver_sound E cs R FULL model TT kb len off p c (chunk j c) n [KBlob (SA db dk) n (kb + j)%nat] len db dk
                HC Efd Hsys H10 H12 Hd F1 F2 Hbs); try lia.
      + apply bv_eq. rewrite Hn_u, u_len_word by lia. lia.
      + apply bv_eq. rewrite bv_add_unsigned, u_len_word, Hoffu by lia. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
        rewrite Z.mod_small by lia. lia.
      + intros M' HM' HKh. constructor; [|exact HKh]. cbn [kentry_ok].
        split; [unfold flat, elenZ; rewrite Hn_u; lia|].
        split; [rewrite Hblob; unfold elenZ; rewrite Hn_u; lia|].
        intros i Hi. unfold elenZ in Hi. rewrite Hn_u in Hi. rewrite Hblob. apply HM'. lia.
      + intros E' R' FULL' model' Hag HC' Hfs. apply (Hk E' R' FULL' model' Hag); [exact HC' | exact Hfs].
  Qed.

  Theorem node_read_havoc_sound : node1_stmt SEGS A nx0 LIMIT SINV argH FS0 always (fun cs => node_read_havoc SEGS cs).
  Proof.
    intros cs cs' E R FULL model TT HC _ Hn Hk. cbv beta in Hn. unfold node_read_havoc in Hn.
    destruct (a_fd cs) as [|kb len off|] eqn:Efd; try discriminate.
    lazymatch type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
    destruct (dst_ok cs (ELit CHZ)) as [[db dk]|] eqn:Hd; [|discriminate]. injection Hn as <-.
    apply andb_prop in Hc as [Hc Hge]. apply andb_prop in Hc as [Hc H12]. apply andb_prop in Hc as [Hsys H10].
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
    pose proof (lin_ge0_sound SEGS E _ (kn cs) _ _ HK Hge) as Bge. cbn [xt_den] in Bge. unfold CHZ in Bge.
    destruct (fdfile_facts E cs R FULL model kb len off HC Efd) as [p [c (F1 & F2 & F3 & F4 & F5)]].
    unfold uE, flen in F3, F4. pose proof (u64_range (edenot E off)) as Roff.
    set (bs := file_read c (edenot E off) (Z_to_bv 64 65536)).
    assert (Lbs : length bs = Z.to_nat 65536).
    { unfold bs. rewrite length_file_read. unfold word_to_nat. rewrite u64_lit by lia. lia. }
    eapply (read_deliver_sound E cs R FULL model TT kb len off p c bs (ELit CHZ) [] (eaddz off CHZ) db dk
              HC Efd Hsys H10 H12 Hd F1 F2 eq_refl); try (rewrite Lbs; lia).
    - unfold CHZ. rewrite edenot_lit, len_word_of_nat, Lbs. reflexivity.
    - unfold eaddz, CHZ. rewrite mkAlu_denot, len_word_of_nat, Lbs, edenot_lit. apply bv_eq.
      rewrite u_add64, bv_add_unsigned, !u64_lit by lia. reflexivity.
    - unfold uE, eaddz, CHZ. rewrite mkAlu_denot, u_add64, edenot_lit, u64_lit by lia. rewrite Z.mod_small by lia. lia.
    - intros M' _ HKh. exact HKh.
    - intros E' R' FULL' model' Hag HC' Hfs. apply (Hk E' R' FULL' model' Hag); [exact HC' | exact Hfs].
  Qed.

  Theorem node_read_havoc_short_sound : node1_stmt SEGS A nx0 LIMIT SINV argH FS0 always (fun cs => node_read_havoc_short SEGS cs).
  Proof.
    intros cs cs' E R FULL model TT HC _ Hn Hk. cbv beta in Hn. unfold node_read_havoc_short in Hn.
    destruct (a_fd cs) as [|kb len off|] eqn:Efd; try discriminate.
    lazymatch type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
    destruct (dst_ok cs (ELit CHZ)) as [[db dk]|] eqn:Hd; [|discriminate]. injection Hn as <-.
    apply andb_prop in Hc as [Hc Hcap]. apply andb_prop in Hc as [Hc Hlt]. apply andb_prop in Hc as [Hc Hge].
    apply andb_prop in Hc as [Hc H12]. apply andb_prop in Hc as [Hsys H10].
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
    pose proof (lin_ge0_sound SEGS E _ (kn cs) _ _ HK Hge) as Bge. cbn [xt_den] in Bge.
    pose proof (lin_ge0_sound SEGS E _ (kn cs) _ _ HK Hlt) as Blt. cbn [xt_den] in Blt. unfold CHZ in Blt.
    destruct (xhi (kn cs) len) as [lhi|] eqn:Hlhi; [|discriminate]. apply Z.ltb_lt in Hcap.
    pose proof (xhi_sound SEGS E _ (kn cs) len lhi HK Hlhi) as Blhi. unfold FCAP in Hcap.
    destruct (fdfile_facts E cs R FULL model kb len off HC Efd) as [p [c (F1 & F2 & F3 & F4 & F5)]].
    unfold uE, flen in F3, F4. pose proof (u64_range (edenot E off)) as Roff.
    set (bs := file_read c (edenot E off) (Z_to_bv 64 65536)).
    assert (Lbs : Z.of_nat (length bs) = Z.of_nat (length c) - bv_unsigned (edenot E off)).
    { unfold bs. rewrite length_file_read. unfold word_to_nat. rewrite u64_lit by lia. lia. }
    set (n := esub len off).
    assert (Hn_u : bv_unsigned (edenot E n) = Z.of_nat (length c) - bv_unsigned (edenot E off)).
    { unfold n, esub. rewrite mkAlu_denot, u_sub64. rewrite Z.mod_small by lia. lia. }
    eapply (read_deliver_sound E cs R FULL model TT kb len off p c bs n [] len db dk
              HC Efd Hsys H10 H12 Hd F1 F2 eq_refl); try lia.
    - apply bv_eq. rewrite Hn_u, u_len_word by lia. lia.
    - apply bv_eq. rewrite bv_add_unsigned, u_len_word by lia. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
      rewrite Z.mod_small by lia. lia.
    - intros M' _ HKh. exact HKh.
    - intros E' R' FULL' model' Hag HC' Hfs. apply (Hk E' R' FULL' model' Hag); [exact HC' | exact Hfs].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma some_inj_acs' : forall a b : acs, Some a = Some b -> a = b.
  Proof. intros a b H. exact (f_equal (fun o => match o with Some x => x | None => a end) H). Qed.

  (* [comment removed for export] *)
  Lemma lensplit_of_denot : forall E len q r, lensplit_of len = Some (q, r) ->
    bv_unsigned (edenot E len) = (((65536 * bv_unsigned (ev E q)) mod 2 ^ 64 + bv_unsigned (ev E r)) mod 2 ^ 64)%Z.
  Proof.
    intros E len q r H. unfold lensplit_of in H.
    destruct len as [z|v|op a b|op a b|op a b|op a b|sx lo n e|sx k i n]; try discriminate H.
    destruct op; try discriminate H.
    destruct a as [z|v|op2 a1 a2|op2 a1 a2|op2 a1 a2|op2 a1 a2|sx lo n e|sx k i n]; try discriminate H.
    destruct op2; try discriminate H.
    destruct a1 as [c|v1|op3 x1 x2|op3 x1 x2|op3 x1 x2|op3 x1 x2|sx lo n e|sx k i n]; try discriminate H.
    destruct a2 as [z2|q1|op3 x1 x2|op3 x1 x2|op3 x1 x2|op3 x1 x2|sx lo n e|sx k i n]; try discriminate H.
    destruct b as [z3|r1|op3 x1 x2|op3 x1 x2|op3 x1 x2|op3 x1 x2|sx lo n e|sx k i n]; try discriminate H.
    destruct (Z.eqb c CHZ) eqn:Hc; [|discriminate H]. apply Z.eqb_eq in Hc. injection H as <- <-. subst c.
    cbn [edenot]. rewrite u_add64, u_mul64. rewrite u64_lit by (unfold CHZ; lia). reflexivity.
  Qed.

  Theorem node_header_facts_sound : node1_stmt SEGS A nx0 LIMIT SINV argH FS0 always (fun cs => node_header_facts T cs).
  Proof.
    intros cs cs' E R FULL model TT HC _ Hn Hk. cbv beta in Hn. unfold node_header_facts in Hn.
    destruct (io_open T) as [| | | |clo chi] eqn:Eo; try discriminate Hn.
    destruct (a_fd cs) as [|kb len off|] eqn:Efd; try discriminate Hn.
    lazymatch type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate Hn] end.
    apply some_inj_acs' in Hn. rename Hc into Hkb. first [apply Nat.eqb_eq in Hkb | apply N.eqb_eq in Hkb].
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK. pose proof (co_sinv _ _ _ _ _ _ _ _ _ _ _ HC) as HS.
    destruct (fdfile_facts E cs R FULL model kb len off HC Efd) as [p [c0 (F1 & F2 & F3 & F4 & F5)]].
    destruct H_open as [c (Hne & Hnd & Hlen & Hlk & Hflen & Hblob & Hhdr)].
    specialize (Hblob E FULL HS).
    assert (Hfl : flen c0 = flen c).
    { apply chunks_flen. intros j Hj. rewrite <- (F5 j Hj), Hkb. exact (Hblob j Hj). }
    assert (Hb0 : eb E (io_blob T) = chunk 0 c) by (rewrite <- (Hblob 0%nat ltac:(lia)), Nat.add_0_r; reflexivity).
    destruct Hhdr as (Q1 & Q2 & Q3 & Q4).
    subst cs'. specialize (Hk E R FULL model (conj (env_agree_refl _ _) (env_agree_refl _ _))).
    rewrite pc_set_kn in Hk. apply Hk; [|reflexivity].
    apply cs_ok_set_kn; [exact HC|].
    constructor.
    { (* [comment removed for export] *)
      cbn [kentry_ok]. fold (uE E len).
      rewrite F3, Hfl. unfold flen_bounds. unfold room, flenZ, cfglen in Q2. unfold in_opt, cfglen in Q1. unfold flen, FCAP in *.
      destruct (io_room T) as [[rlo' rhi']|]; destruct (io_cfg T) as [[clo' chi']|]; cbn [fst snd]; try lia.
      destruct (Z.leb_spec 0 rlo'); cbn [fst snd]; lia. }
    apply Forall_app. split.
    { (* [comment removed for export] *)
      cbv zeta. unfold q_facts. destruct (lensplit_of len) as [[q r]|] eqn:Hls; [|constructor].
      destruct (xlo (kn cs) (EVar r)) as [rlo|] eqn:Hrlo; [|constructor].
      destruct (xhi (kn cs) (EVar r)) as [rhi|] eqn:Hrhi; [|constructor].
      destruct (xhi (kn cs) (EVar q)) as [qhi|] eqn:Hqhi; [|constructor].
      lazymatch goal with |- Forall _ (if ?c then _ else _) => destruct c eqn:Hc; [|constructor] end.
      apply andb_prop in Hc as [Hc Hnw]. apply andb_prop in Hc as [Hr0 Hlo0].
      apply Z.leb_le in Hr0. apply Z.leb_le in Hlo0. apply Z.ltb_lt in Hnw.
      pose proof (xlo_sound SEGS E _ (kn cs) (EVar r) rlo HK Hrlo) as Brlo.
      pose proof (xhi_sound SEGS E _ (kn cs) (EVar r) rhi HK Hrhi) as Brhi.
      pose proof (xhi_sound SEGS E _ (kn cs) (EVar q) qhi HK Hqhi) as Bqhi.
      cbn [edenot] in Brlo, Brhi, Bqhi.
      assert (HL : (fst (flen_bounds T clo chi) <= uE E len <= snd (flen_bounds T clo chi))%Z).
      { rewrite F3, Hfl. unfold flen_bounds. unfold room, flenZ, cfglen in Q2. unfold in_opt, cfglen in Q1. unfold flen, FCAP in *.
        destruct (io_room T) as [[rlo' rhi']|]; destruct (io_cfg T) as [[clo' chi']|]; cbn [fst snd]; try lia.
        destruct (Z.leb_spec 0 rlo'); cbn [fst snd]; lia. }
      unfold uE in HL. rewrite (lensplit_of_denot E len q r Hls) in HL.
      pose proof (u64_range (ev E q)) as Rq. pose proof (u64_range (ev E r)) as Rr. unfold CHZ, two64 in *.
      rewrite (Z.mod_small (65536 * _)) in HL by nia. rewrite Z.mod_small in HL by nia.
      apply Forall_one. cbn [kentry_ok edenot]. unfold zcdiv0.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
      split; [apply Z.max_lub; [lia|] | apply Z.min_glb; [lia|]]; nia.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
    apply Forall_app. split.
    { (* [comment removed for export] *)
      unfold room_fact_lit. destruct len as [z|v|? ? ?|? ? ?|? ? ?|? ? ?|? ? ? ?|? ? ? ?]; try (apply Forall_nil).
      destruct (xlo (kn cs) (EVar v)) as [vlo|] eqn:Hvlo; [|constructor].
      destruct (xhi (kn cs) (EVar v)) as [vhi|] eqn:Hvhi; [|constructor].
      destruct (Z.eqb vlo vhi) eqn:Hvv; [|constructor]. apply Z.eqb_eq in Hvv. subst vhi.
      pose proof (xlo_sound SEGS E _ (kn cs) (EVar v) vlo HK Hvlo) as Bvlo.
      pose proof (xhi_sound SEGS E _ (kn cs) (EVar v) vlo HK Hvhi) as Bvhi.
      assert (Hv : vlo = uE E (EVar v)) by (unfold uE; lia).
      assert (Rv : 0 <= uE E (EVar v) < 2 ^ 64) by (unfold uE; apply u64_range).
      unfold room_fact. destruct (io_room T) as [[lo hi]|]; [|constructor].
      unfold room, flenZ, cfglen in Q2. unfold flen in F3, Hfl.
      pose proof (Z.mod_pos_bound (hbyte 0 c + 256 * hbyte 1 c) 32768 ltac:(lia)) as Hcfg.
      assert (HCF : uE E (CFGX (io_blob T)) = (hbyte 0 c + 256 * hbyte 1 c) mod 32768) by (rewrite CFGX_denot, Hb0, !hbyte_chunk0 by lia; reflexivity).
      destruct (Z.leb_spec 0 lo) as [Hlo0|Hlo0]; [|destruct (Z.ltb_spec hi 0) as [Hhi0|Hhi0]; [|constructor]]; apply Forall_one; cbn [kentry_ok] in *.
      + fold (uE E (XROOM (io_blob T) (ELit vlo))). unfold XROOM, esub, uE. rewrite !mkAlu_denot, !u_sub64, !edenot_lit, !u64_lit by lia.
        fold (uE E (CFGX (io_blob T))). rewrite HCF. rewrite Hv. rewrite F3, Hfl.
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
        rewrite (Z.mod_small (Z.min _ _ - 6)) by lia. rewrite Z.mod_small by lia. lia.
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
      + fold (uE E (XOVER (io_blob T) (ELit vlo))). unfold XOVER, esub, eaddz, uE. rewrite !mkAlu_denot, u_sub64, u_add64, !edenot_lit, !u64_lit by lia.
        fold (uE E (CFGX (io_blob T))). rewrite HCF. rewrite Hv. rewrite F3, Hfl.
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
        rewrite (Z.mod_small (_ + 6)) by lia. rewrite Z.mod_small by lia. lia.
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
    apply Forall_app. split; [|exact HK].
    unfold header_facts. repeat (apply Forall_app; split).
    - unfold opt_fact. destruct (io_cfg T) as [[lo hi]|]; [|constructor]. apply Forall_one. cbn [kentry_ok in_opt] in *.
      fold (uE E (CFGX (io_blob T))). rewrite CFGX_denot, Hb0, !hbyte_chunk0 by lia. unfold cfglen in Q1. exact Q1.
    - unfold room_fact. destruct (io_room T) as [[lo hi]|]; [|constructor].
      unfold room, flenZ, cfglen in Q2. unfold flen in F3, Hfl.
      pose proof (Z.mod_pos_bound (hbyte 0 c + 256 * hbyte 1 c) 32768 ltac:(lia)) as Hcfg.
      assert (HCF : uE E (CFGX (io_blob T)) = (hbyte 0 c + 256 * hbyte 1 c) mod 32768) by (rewrite CFGX_denot, Hb0, !hbyte_chunk0 by lia; reflexivity).
      destruct (Z.leb_spec 0 lo) as [Hlo0|Hlo0]; [|destruct (Z.ltb_spec hi 0) as [Hhi0|Hhi0]; [|constructor]]; apply Forall_one; cbn [kentry_ok] in *.
      + fold (uE E (XROOM (io_blob T) len)). unfold XROOM, esub, uE. rewrite !mkAlu_denot, !u_sub64, edenot_lit, u64_lit by lia.
        fold (uE E (CFGX (io_blob T))) (uE E len). rewrite HCF. rewrite F3, Hfl.
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
        rewrite (Z.mod_small (Z.min _ _ - 6)) by lia. rewrite Z.mod_small by lia. lia.
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
      + fold (uE E (XOVER (io_blob T) len)). unfold XOVER, esub, eaddz, uE. rewrite !mkAlu_denot, u_sub64, u_add64, edenot_lit, u64_lit by lia.
        fold (uE E (CFGX (io_blob T))) (uE E len). rewrite HCF. rewrite F3, Hfl.
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
        rewrite (Z.mod_small (_ + 6)) by lia. rewrite Z.mod_small by lia. lia.
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    - unfold opt_fact. destruct (io_cmod T) as [[lo hi]|]; [|constructor]. apply Forall_one. cbn [kentry_ok in_opt] in *.
      fold (uE E (XCM (io_blob T))). rewrite XCM_denot, Hb0, hbyte_chunk0 by lia. unfold cmod in Q3. exact Q3.
    - unfold opt_fact. destruct (io_b1s T) as [[lo hi]|]; [|constructor]. apply Forall_one. cbn [kentry_ok in_opt] in *.
      fold (uE E (XB1S (io_blob T))). rewrite XB1S_denot, Hb0, hbyte_chunk0 by lia. unfold b1s in Q4. exact Q4.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma lensplit_len_denot : forall E q r,
    uE E (lensplit_len q r) = (CHZ * bv_unsigned (ev E q) + bv_unsigned (ev E r)) mod two64.
  Proof.
    intros E q r. unfold lensplit_len, eadd, escale, uE. rewrite mkAlu_denot, u_add64, mkMd_denot, u_mul64.
    rewrite edenot_lit, u64_lit by (unfold CHZ; lia). cbn [edenot]. unfold two64.
    rewrite Zplus_mod_idemp_l. reflexivity.
  Qed.

  Hypothesis nx0_le_NX0 : (nx0 <= NX0)%N.   (* [comment removed for export] *)

  Theorem node_lensplit_sound : node1_stmt SEGS A nx0 LIMIT SINV argH FS0 always (fun cs => node_lensplit cs).
  Proof.
    intros cs cs' E R FULL model TT HC _ Hn Hk. cbv beta in Hn. unfold node_lensplit in Hn.
    destruct (a_fd cs) as [|kb len off|] eqn:Efd; try discriminate Hn.
    destruct len as [|v| | | | | |]; try discriminate Hn.
    destruct (xlo (kn cs) (EVar v)) as [lo|] eqn:Hlo; [|discriminate Hn].
    destruct (xhi (kn cs) (EVar v)) as [hi|] eqn:Hhi; [|discriminate Hn].
    lazymatch type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate Hn] end.
    apply andb_prop in Hc as [Hc Hcap]. apply andb_prop in Hc as [Hfresh Hlo0].
    apply Z.leb_le in Hcap. apply Z.leb_le in Hlo0.
    apply some_inj_acs' in Hn.
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
    pose proof (xlo_sound SEGS E _ (kn cs) (EVar v) lo HK Hlo) as Hlo'.
    pose proof (xhi_sound SEGS E _ (kn cs) (EVar v) hi HK Hhi) as Hhi'.
    cbn [edenot] in Hlo', Hhi'.
    destruct (fdfile_facts E cs R FULL model kb (EVar v) off HC Efd) as [p [c (F1 & F2 & F3 & F4 & F5)]].
    unfold uE in F3, F4. cbn [edenot] in F3, F4.
    set (L := bv_unsigned (ev E v)) in *.
    assert (HL : 0 <= L <= FCAP) by lia.
    set (q := nxt cs) in *. set (r := N.succ q) in *.
    set (E1 := APS.ext1 E q (Z_to_bv 64 (L / CHZ))).
    set (E' := APS.ext1 E1 r (Z_to_bv 64 (L mod CHZ))).
    assert (Hag1 : env_agree q E E1) by apply APS.ext1_agree.
    assert (Hag2 : env_agree r E1 E') by apply APS.ext1_agree.
    assert (Hag : env_agree q E E').
    { eapply env_agree_trans; [exact Hag1 | eapply env_agree_le; [exact Hag2 | lia]]. }
    destruct (fresh_ok_parts NX0 cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle9).
    assert (Fle : (nx0 <= nxt cs)%N) by lia.
    assert (Hfresh' : fresh_ok nx0 cs = true).
    { unfold fresh_ok in Hfresh |- *. repeat match type of Hfresh with (_ && _)%bool = true => apply andb_prop in Hfresh as [Hfresh ?X] end.
      repeat (apply andb_true_intro; split); try assumption. first [apply Nat.leb_le | apply N.leb_le]. exact Fle. }
    pose proof (cs_ok_agree SEGS A nx0 LIMIT nx0_ge7 SINV argH argH_agree SINV_agree FS0 E E' cs R FULL model Hag Hfresh' HC) as HC'.
    assert (HqL : 0 <= L / CHZ < 2 ^ 64).
    { unfold CHZ, FCAP in *. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
    assert (HrL : 0 <= L mod CHZ < CHZ) by (unfold CHZ; apply Z.mod_pos_bound; lia).
    assert (Eq : bv_unsigned (ev E' q) = L / CHZ).
    { destruct Hag2 as [A2 _]. unfold E' in A2 |- *.
      transitivity (bv_unsigned (ev E1 q)); [f_equal; symmetry; apply A2; lia|].
      unfold E1. rewrite APS.ext1_at. apply u64_lit. exact HqL. }
    assert (Er : bv_unsigned (ev E' r) = L mod CHZ).
    { unfold E'. rewrite APS.ext1_at. apply u64_lit. unfold CHZ in *. lia. }
    assert (Fv : (v < q)%N).
    { rewrite Efd in Ffd. cbn [fd_vars_lt AP.expr_vars_lt] in Ffd. apply andb_prop in Ffd as [Fv _]. first [apply Nat.ltb_lt in Fv | apply N.ltb_lt in Fv]. exact Fv. }
    assert (Ev : ev E' v = ev E v) by (destruct Hag as [Ag _]; symmetry; apply Ag; exact Fv).
    assert (Hlen : uE E' (lensplit_len q r) = L).
    { rewrite lensplit_len_denot, Eq, Er. unfold CHZ, FCAP, two64 in *.
      rewrite <- (Z_div_mod_eq_full L 65536). apply Z.mod_small. lia. }
    subst cs'. cbn [pc a_ss s_pc mk_ss] in Hk |- *.
    apply (Hk E' R FULL model); [split; [eapply env_agree_le; [exact Hag | exact Fle] | exact Hag] | | reflexivity].
    assert (HKf : know_ok SEGS E' (Mr A argH E' cs model FULL)
             ([KRange (EVar r) 0 (CHZ - 1); KRange (EVar q) (lo / CHZ) (hi / CHZ); KRange (lensplit_len q r) lo hi;
               KRange (mkAlu ALU_SUB (EVar v) (lensplit_len q r)) 0 0] ++ kn cs)).
    { apply Forall_app. split; [|exact (co_know _ _ _ _ _ _ _ _ _ _ _ HC')].
      constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]; cbn [kentry_ok].
      - cbn [edenot]. rewrite Er. lia.
      - cbn [edenot]. rewrite Eq. unfold CHZ in *. split; [apply Z.div_le_mono; lia | apply Z.div_le_mono; lia].
      - fold (uE E' (lensplit_len q r)). rewrite Hlen. lia.
      - (* [comment removed for export] *)
        rewrite mkAlu_denot. cbn [edenot]. rewrite Ev.
        assert (HLe : bv_unsigned (edenot E' (lensplit_len q r)) = L) by exact Hlen.
        assert (X : bv_unsigned (alu64 ALU_SUB (ev E v) (edenot E' (lensplit_len q r))) = 0).
        { cbn [alu64 alu]. rewrite bv_sub_unsigned. fold L. rewrite HLe. rewrite Z.sub_diag. reflexivity. }
        rewrite X. lia. }
    destruct HC'; constructor; cbn [a_ss mk_ss s_regs s_log s_know kn nxt a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset pc]; try assumption.
    - reflexivity.
    - (* [comment removed for export] *)
      rewrite Efd in co_fds0. cbn [fds_ok] in co_fds0 |- *. destruct co_fds0 as [p' [c' (G1 & G2 & G3 & G4 & G5)]].
      exists p', c'. split; [exact G1|]. split; [exact G2|].
      assert (HL' : uE E' (EVar v) = L) by (unfold uE; cbn [edenot]; rewrite Ev; reflexivity).
      rewrite HL' in G3, G4. rewrite Hlen. repeat split; assumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma residue_sharp_sound : forall E E' M M' k e ne logc,
    know_ok SEGS E M k ->
    edenot E' ne = edenot E e ->
    0 <= logc -> (2 ^ logc | bv_unsigned (edenot E e)) ->
    (forall e' s, deand e = (e', s) -> edenot E' e' = edenot E e') ->
    know_ok SEGS E' M' (residue_sharp k e ne logc).
  Proof.
    intros E E' M M' k e ne logc HK Hne Hlogc Hdiv Hag. unfold residue_sharp.
    destruct (deand e) as [e' s] eqn:Hd. destruct (Z.ltb 0 s) eqn:Hs; [|constructor].
    destruct (xlo1 k e') as [lo'|] eqn:H1; [|constructor]. destruct (xhi1 k e') as [hi'|] eqn:H2; [|constructor].
    destruct (Z.leb s lo') eqn:Hsl; [|constructor]. apply Z.leb_le in Hsl.
    destruct (lin_of e') as [c0 ts] eqn:Hl.
    set (a := Z.min (Z.min (ealign k (unlin (0, ts))) logc) 40). set (m := 2 ^ a).
    constructor; [|constructor]. cbn [kentry_ok]. unfold esub. rewrite mkAlu_denot, u_sub64, Hne, (Hag e' s eq_refl).
    destruct (deand_sound E e e' s Hd) as [Hs0 [rho [Hrho Ee]]].
    pose proof (xlo1_sound SEGS E M k e' lo' HK H1) as L1. pose proof (u64_range (edenot E e')) as R'.
    assert (Hue : bv_unsigned (edenot E e) = bv_unsigned (edenot E e') - rho) by (rewrite Ee; apply Z.mod_small; lia).
    rewrite Hue. replace (bv_unsigned (edenot E e') - (bv_unsigned (edenot E e') - rho)) with rho by lia.
    rewrite (Z.mod_small rho (2 ^ 64)) by lia.
    (* [comment removed for export] *)
    destruct (ealign_sound SEGS E M k (unlin (0, ts)) HK) as [Hea Hdv].
    assert (Ha : 0 <= a <= 40) by (unfold a; lia).
    assert (Hm : 0 < m) by (unfold m; apply Z.pow_pos_nonneg; lia).
    assert (Hma : (m | 2 ^ ealign k (unlin (0, ts)))) by (unfold m; apply pow2_divide_le; unfold a; lia).
    assert (Hml : (m | 2 ^ logc)) by (unfold m; apply pow2_divide_le; unfold a; lia).
    assert (Hm64 : (m | 2 ^ 64)) by (unfold m; apply pow2_divide_le; unfold a; lia).
    (* [comment removed for export] *)
    pose proof (lin_of_sound E e') as Hlin. rewrite Hl in Hlin. unfold lden in Hlin. cbn [fst snd] in Hlin.
    pose proof (unlin_sound E (0, ts)) as Hun. unfold lden in Hun. cbn [fst snd] in Hun.
    destruct Hlin as [q1 Hq1]. destruct Hun as [q2 Hq2]. unfold AX2S.uE in Hq1, Hq2.
    (* [comment removed for export] *)
    apply residue_window; [exact Hm | exact Hrho |].
    destruct Hdv as [t Ht]. destruct Hma as [ma Hma']. destruct Hml as [ml Hml']. destruct Hm64 as [m64 Hm64'].
    destruct Hdiv as [d Hd'].
    (* [comment removed for export] *)
    assert (Hrho_eq : rho = (t * ma - d * ml - (q1 + q2) * m64) * m + c0).
    { rewrite Hma' in Ht. rewrite Hml' in Hd'. rewrite Hm64' in Hq1, Hq2.
      replace ((t * ma - d * ml - (q1 + q2) * m64) * m + c0) with (c0 + t * (ma * m) - q2 * (m64 * m) - q1 * (m64 * m) - d * (ml * m)) by ring.
      lia. }
    rewrite Hrho_eq. rewrite Z.add_comm, Z.mod_add by lia. reflexivity.
  Qed.


  Theorem node_fresha_sound : forall r logc base,
    node1_stmt SEGS A nx0 LIMIT SINV argH FS0 always (fun cs => node_fresha cs r logc base).
  Proof.
    intros r logc base cs cs' E R FULL model TT HC _ Hn Hk. cbv beta in Hn. unfold node_fresha in Hn.
    set (b := match base with Some rb => reg cs rb | None => ELit 0 end) in Hn.
    set (e := match base with Some _ => esub (reg cs r) b | None => reg cs r end) in Hn.
    lazymatch type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate Hn] end.
    apply andb_prop in Hc as [Hc Hfresh]. apply andb_prop in Hc as [Hc HveX]. apply andb_prop in Hc as [Hc Hvb].
    apply andb_prop in Hc as [Hc Hal]. apply andb_prop in Hc as [Hc H40]. apply andb_prop in Hc as [Hc H0].
    apply andb_prop in Hc as [Hr0 Hr32].
    first [apply Nat.ltb_lt in Hr0 | apply N.ltb_lt in Hr0]. first [apply Nat.ltb_lt in Hr32 | apply N.ltb_lt in Hr32]. apply Z.leb_le in H0. apply Z.leb_le in H40. apply Z.leb_le in Hal.
    destruct (xlo2 (kn cs) e) as [lo|] eqn:Hlo; [|discriminate Hn].
    destruct (xhi2 (kn cs) e) as [hi|] eqn:Hhi; [|discriminate Hn].
    apply some_inj_acs' in Hn. subst cs'.
    set (c := 2 ^ logc) in *. set (v := nxt cs) in *.
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
    pose proof (xlo2_sound SEGS E _ (kn cs) e lo HK Hlo) as Hlo'.
    pose proof (xhi2_sound SEGS E _ (kn cs) e hi HK Hhi) as Hhi'.
    destruct (ealign_sound SEGS E _ (kn cs) e HK) as [Hea Hdiv].
    assert (Hcpos : 0 < c) by (unfold c; apply Z.pow_pos_nonneg; lia).
    assert (Hc2 : c <= 2 ^ 40) by (unfold c; apply Z.pow_le_mono_r; lia).
    assert (Hcd : (c | bv_unsigned (edenot E e))%Z).
    { eapply Z.divide_trans; [|exact Hdiv]. unfold c. apply pow2_divide_le. lia. }
    destruct Hcd as [q Hq].
    pose proof (u64_range (edenot E e)) as Hue.
    assert (Hq0 : 0 <= q) by nia.
    assert (Hq64 : q < 2 ^ 64) by nia.
    set (a := Z_to_bv 64 q). set (E' := APS.ext1 E v a).
    assert (Hag : env_agree v E E') by apply APS.ext1_agree.
    destruct (fresh_ok_parts NX0 cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle9).
    assert (Fle : (nx0 <= nxt cs)%N) by lia.
    assert (Hfresh' : fresh_ok nx0 cs = true).
    { unfold fresh_ok in Hfresh |- *. repeat match type of Hfresh with (_ && _)%bool = true => apply andb_prop in Hfresh as [Hfresh ?X] end.
      repeat (apply andb_true_intro; split); try assumption. first [apply Nat.leb_le | apply N.leb_le]. exact Fle. }
    pose proof (cs_ok_agree SEGS A nx0 LIMIT nx0_ge7 SINV argH argH_agree SINV_agree FS0 E E' cs R FULL model Hag Hfresh' HC) as HC'.
    assert (Hev : edenot E' e = edenot E e) by (symmetry; eapply (edenot_agree' v); [exact Hag | exact HveX]).
    assert (Hbv : edenot E' b = edenot E b) by (symmetry; eapply (edenot_agree' v); [exact Hag | exact Hvb]).
    assert (Hrv : edenot E' (reg cs r) = edenot E (reg cs r)).
    { symmetry. eapply (edenot_agree' v); [exact Hag|]. unfold reg. apply nth_sr_vars_lt; [exact Fsr | lia]. }
    assert (Hne : edenot E' (escale c (EVar v)) = edenot E e).
    { unfold escale. rewrite mkMd_denot. cbn [edenot]. unfold E'. rewrite APS.ext1_at. unfold a.
      apply bv_eq. rewrite u_mul64. rewrite (u_small c) by lia. rewrite (u_small q) by lia. rewrite Z.mod_small by nia. lia. }
    apply (Hk E' R FULL model); [split; [eapply env_agree_le; [exact Hag | exact Fle] | exact Hag] | | reflexivity].
    assert (HKf : know_ok SEGS E' (Mr A argH E' cs model FULL)
              ((KRange (EVar v) ((lo + c - 1) / c) (hi / c) :: KRange (esub e (escale c (EVar v))) 0 0
                 :: residue_sharp (kn cs) e (escale c (EVar v)) logc)
               ++ kn cs)).
    { apply Forall_app. split; [|exact (co_know _ _ _ _ _ _ _ _ _ _ _ HC')].
      constructor; [|constructor].
      - cbn [kentry_ok edenot]. unfold E' at 1 2. rewrite APS.ext1_at. unfold a. rewrite u_small by lia.
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
        split; nia.
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
      - cbn [kentry_ok]. unfold esub. rewrite !mkAlu_denot, !Hne, !Hev.
        rewrite !u_sub64. rewrite Z.sub_diag, Z.mod_0_l by lia. lia.
      - eapply (residue_sharp_sound E E' _ _ (kn cs) e); [exact HK | exact Hne | lia | exists q; exact Hq |].
        intros e1 s1 Hd1. symmetry. eapply (edenot_agree' v); [exact Hag | exact (deand_vars v e e1 s1 Hd1 HveX)]. }
    destruct HC'; constructor; cbn [bump set_reg add_kn set_kn with_ss a_ss mk_ss s_regs s_log s_know kn a_maps a_totsz a_ylo a_eager a_vis a_abytes a_brk a_fd a_tidset]; try assumption.
    - apply regs_ok_respell; [exact co_regs0 | lia |].
      destruct base as [rb|].
      + (* [comment removed for export] *)
        unfold eadd. rewrite mkAlu_denot, Hne, Hbv. fold (reg cs r). rewrite Hrv.
        assert (He_sem : edenot E e = alu64 ALU_SUB (edenot E (reg cs r)) (edenot E b)) by (unfold e, esub; apply mkAlu_denot).
        rewrite He_sem. apply bv_eq. rewrite u_add64, u_sub64. pose proof (u64_range (edenot E (reg cs r))). pose proof (u64_range (edenot E b)).
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
        rewrite Zplus_mod_idemp_r. replace (bv_unsigned (edenot E b) + (bv_unsigned (edenot E (reg cs r)) - bv_unsigned (edenot E b))) with (bv_unsigned (edenot E (reg cs r))) by lia.
        rewrite Z.mod_small by lia. reflexivity.
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
      + rewrite Hne. symmetry. exact Hev.
    - reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma srl_window_sound : forall E M k x s rlo rhi,
    know_ok SEGS E M k -> srl_window k x s = Some (rlo, rhi) ->
    rlo <= bv_unsigned (edenot E x) mod 2 ^ s <= rhi /\ 1 <= s <= 40
    /\ bv_unsigned (edenot E x) = fst (lin_of x) + tden E (snd (lin_of x)).
  Proof.
    intros E M k x s rlo rhi HK H. unfold srl_window in H.
    destruct (Z.leb 1 s && Z.leb s 40 && lin_nowrap k x)%bool eqn:Hc; [|discriminate].
    apply andb_prop in Hc as [Hc Hnw]. apply andb_prop in Hc as [Hs1 Hs40]. apply Z.leb_le in Hs1. apply Z.leb_le in Hs40.
    destruct (lin_of x) as [c0 ts] eqn:Hl.
    set (al := Z.min (ealign k (unlin (0, ts))) s) in H.
    destruct (Z.leb 1 al) eqn:Hal; [|discriminate]. apply Z.leb_le in Hal.
    injection H as <- <-.
    set (ma := 2 ^ al). set (m := 2 ^ s).
    pose proof (lin_nowrap_sound SEGS E M k x HK Hnw) as Hx. rewrite Hl in Hx. cbn [fst snd] in Hx.
    split; [| split; [lia | exact Hx]].
    destruct (ealign_sound SEGS E M k (unlin (0, ts)) HK) as [Hea Hdv].
    assert (Hal2 : 1 <= al <= s) by (unfold al in *; lia).
    assert (Hma : 0 < ma) by (unfold ma; apply Z.pow_pos_nonneg; lia).
    assert (Hm : 0 < m) by (unfold m; apply Z.pow_pos_nonneg; lia).
    assert (Hmam : (ma | m)) by (unfold ma, m; apply pow2_divide_le; lia).
    assert (Hmae : (ma | 2 ^ ealign k (unlin (0, ts)))) by (unfold ma; apply pow2_divide_le; unfold al; lia).
    assert (Hma64 : (ma | 2 ^ 64)) by (unfold ma; apply pow2_divide_le; lia).
    pose proof (unlin_sound E (0, ts)) as Hun. unfold lden in Hun. cbn [fst snd] in Hun. destruct Hun as [q2 Hq2]. unfold AX2S.uE in Hq2.
    set (ux := bv_unsigned (edenot E x)) in *.
    unfold m. apply residue_window; [exact Hma | pose proof (Z.mod_pos_bound ux (2 ^ s) Hm); lia |]. fold m.
    destruct Hmam as [mm Hmm]. destruct Hmae as [me Hme]. destruct Hma64 as [m64 Hm64']. destruct Hdv as [t Ht].
    rewrite Hme in Ht. rewrite Hm64' in Hq2.
    rewrite (Z.mod_mod_divide ux m ma) by (exists mm; exact Hmm).
    assert (Hux : ux = (t * me - q2 * m64) * ma + c0).
    { replace ((t * me - q2 * m64) * ma + c0) with (c0 + (t * (me * ma) - q2 * (m64 * ma))) by ring. lia. }
    rewrite Hux. rewrite Z.add_comm, Z.mod_add by lia. reflexivity.
  Qed.


  Lemma srl_atom_fact_sound : forall E M k a,
    know_ok SEGS E M k -> know_ok SEGS E M (srl_atom_fact k a).
  Proof.
    intros E M k a HK. unfold srl_atom_fact.
    destruct a as [| |op x [s| | | | | | |]| | | | |]; try constructor; destruct op; try constructor; try (cbn; constructor).
    destruct (Z.leb 1 s && Z.leb s 40 && lin_nowrap k x)%bool eqn:Hc; [|constructor].
    apply andb_prop in Hc as [Hc Hnw]. apply andb_prop in Hc as [Hs1 Hs40]. apply Z.leb_le in Hs1. apply Z.leb_le in Hs40.
    destruct (lin_of x) as [c0 ts] eqn:Hl.
    set (al := Z.min (ealign k (unlin (0, ts))) s).
    destruct (Z.leb 1 al) eqn:Hal; [|constructor]. apply Z.leb_le in Hal.
    set (ma := 2 ^ al). set (m := 2 ^ s).
    pose proof (lin_nowrap_sound SEGS E M k x HK Hnw) as Hx. rewrite Hl in Hx. cbn [fst snd] in Hx.
    destruct (ealign_sound SEGS E M k (unlin (0, ts)) HK) as [Hea Hdv].
    assert (Hal2 : 1 <= al <= s) by (unfold al in *; lia).
    assert (Hma : 0 < ma) by (unfold ma; apply Z.pow_pos_nonneg; lia).
    assert (Hm : 0 < m) by (unfold m; apply Z.pow_pos_nonneg; lia).
    assert (Hm64 : m <= 2 ^ 40) by (unfold m; apply Z.pow_le_mono_r; lia).
    assert (Hmam : (ma | m)) by (unfold ma, m; apply pow2_divide_le; lia).
    assert (Hmae : (ma | 2 ^ ealign k (unlin (0, ts)))) by (unfold ma; apply pow2_divide_le; unfold al; lia).
    assert (Hma64 : (ma | 2 ^ 64)) by (unfold ma; apply pow2_divide_le; lia).
    pose proof (unlin_sound E (0, ts)) as Hun. unfold lden in Hun. cbn [fst snd] in Hun. destruct Hun as [q2 Hq2]. unfold AX2S.uE in Hq2.
    set (ux := bv_unsigned (edenot E x)) in *.
    pose proof (u64_range (edenot E x)) as Rx. fold ux in Rx.
    set (rlo := c0 mod ma). set (rhi := m - 1 - (m - 1 - rlo) mod ma).
    assert (WIN : rlo <= ux mod m <= rhi).
    { unfold rlo, rhi. apply residue_window; [exact Hma | pose proof (Z.mod_pos_bound ux m Hm); lia |].
      destruct Hmam as [mm Hmm]. destruct Hmae as [me Hme]. destruct Hma64 as [m64 Hm64']. destruct Hdv as [t Ht].
      rewrite Hme in Ht. rewrite Hm64' in Hq2.
      rewrite (Z.mod_mod_divide ux m ma) by (exists mm; exact Hmm).
      assert (Hux : ux = (t * me - q2 * m64) * ma + c0).
      { replace ((t * me - q2 * m64) * ma + c0) with (c0 + (t * (me * ma) - q2 * (m64 * ma))) by ring. lia. }
      rewrite Hux. rewrite Z.add_comm, Z.mod_add by lia. reflexivity. }
    constructor.
    - cbn [kentry_ok]. unfold m. rewrite u_srl_rem by lia. fold m. exact WIN.
    - destruct (Z.leb rhi c0 && Z.ltb c0 two64)%bool eqn:Hc0; [|constructor].
      apply andb_prop in Hc0 as [Hc0a Hc0b]. apply Z.leb_le in Hc0a. apply Z.ltb_lt in Hc0b. unfold two64 in Hc0b.
      constructor; [|constructor]. cbn [kentry_ok].
      unfold esub, escale. rewrite mkAlu_denot, u_sub64, mkMd_denot, u_mul64, edenot_lit, u_srl_lit.
      rewrite (u_small m) by lia.
      replace ((s mod two64) mod 64) with s by (unfold two64; rewrite (Z.mod_small s (2^64)) by lia; rewrite Z.mod_small by lia; reflexivity).
      fold m. fold ux.
      (* [comment removed for export] *)
      pose proof (Z.div_mod ux m ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound ux m Hm) as Hmb.
      rewrite (Z.mod_small (m * (ux / m))) by nia.
      (* [comment removed for export] *)
      rewrite <- Zminus_mod_idemp_r.
      replace (bv_unsigned (edenot E (unlin (0, ts))) mod 2 ^ 64) with ((ux - c0) mod 2 ^ 64).
      2:{ rewrite Hq2. replace (0 + tden E ts + q2 * 2 ^ 64) with ((ux - c0) + q2 * 2 ^ 64) by lia. rewrite Z.mod_add by lia. reflexivity. }
      rewrite Zminus_mod_idemp_r.
      replace (m * (ux / m) - (ux - c0)) with (c0 - ux mod m) by lia.
      rewrite Z.mod_small by lia. lia.
  Qed.

  Lemma as_round_eq : forall e m x s, as_round e = Some (m, x, s) -> e = EMd M_MUL (ELit m) (EAlu ALU_SRL x (ELit s)).
  Proof.
    intros e m x s H. unfold as_round in H.
    destruct e; try discriminate H. destruct op; try discriminate H. destruct e1; try discriminate H.
    destruct e2; try discriminate H. destruct op; try discriminate H. destruct e2_2; try discriminate H.
    injection H as <- <- <-. reflexivity.
  Qed.

  Lemma srl_pair_fact_sound : forall E M k e1 e2,
    know_ok SEGS E M k -> know_ok SEGS E M (srl_pair_fact k e1 e2).
  Proof.
    intros E M k e1 e2 HK. unfold srl_pair_fact.
    destruct (as_round e1) as [[[m1 x1] s1]|] eqn:A1; [|constructor].
    destruct (as_round e2) as [[[m2 x2] s2]|] eqn:A2; [|constructor].
    apply as_round_eq in A1. apply as_round_eq in A2. subst e1 e2.
    destruct (lin_of x1) as [c1 ts1] eqn:Hl1. destruct (lin_of x2) as [c2 ts2] eqn:Hl2.
    match goal with |- know_ok _ _ _ (if ?c then _ else _) => destruct c eqn:Hc; [|constructor] end.
    apply andb_prop in Hc as [Hc Hnw2]. apply andb_prop in Hc as [Hc Hnw1]. apply andb_prop in Hc as [Hc Heq].
    apply andb_prop in Hc as [Hc Hm2]. apply andb_prop in Hc as [Hs Hm1].
    apply Z.eqb_eq in Hs. apply Z.eqb_eq in Hm1. apply Z.eqb_eq in Hm2. apply expr_eqb_eq in Heq. subst s2 m1 m2.
    destruct (srl_window k x1 s1) as [[rlo1 rhi1]|] eqn:Hw; [|constructor].
    destruct (srl_window_sound E M k x1 s1 rlo1 rhi1 HK Hw) as (W1 & Hs & Hx1). rewrite Hl1 in Hx1. cbn [fst snd] in Hx1.
    pose proof (lin_nowrap_sound SEGS E M k x2 HK Hnw2) as Hx2. rewrite Hl2 in Hx2. cbn [fst snd] in Hx2.
    set (m := 2 ^ s1) in *.
    match goal with |- know_ok _ _ _ (if ?c then _ else _) => destruct c eqn:Hb; [|constructor] end.
    apply andb_prop in Hb as [Hlo Hhi]. apply Z.leb_le in Hlo. apply Z.ltb_lt in Hhi.
    constructor; [|constructor]. cbn [kentry_ok].
    assert (Hm : 0 < m) by (unfold m; apply Z.pow_pos_nonneg; lia).
    assert (Hm40 : m <= 2 ^ 40) by (unfold m; apply Z.pow_le_mono_r; lia).
    assert (Hm64 : (m | 2 ^ 64)) by (unfold m; apply pow2_divide_le; lia).
    unfold esub. rewrite mkAlu_denot, u_sub64. cbn [edenot]. rewrite !u_mul64, !u_srl64.
    rewrite !(u_small m) by lia. rewrite !(u_small s1) by lia. rewrite !(Z.mod_small s1 64) by lia.
    fold m.
    set (u1 := bv_unsigned (edenot E x1)) in *. set (u2 := bv_unsigned (edenot E x2)) in *.
    pose proof (u64_range (edenot E x1)) as R1. pose proof (u64_range (edenot E x2)) as R2. fold u1 in R1. fold u2 in R2.
    pose proof (unlin_sound E (0, ts1)) as U1. pose proof (unlin_sound E (0, ts2)) as U2.
    unfold lden in U1, U2. cbn [fst snd] in U1, U2. rewrite Heq in U1.
    destruct U1 as [q1 Hq1]. destruct U2 as [q2 Hq2]. unfold AX2S.uE in Hq1, Hq2.
    pose proof (Z.div_mod u1 m ltac:(lia)) as D1. pose proof (Z.mod_pos_bound u1 m Hm) as B1.
    pose proof (Z.div_mod u2 m ltac:(lia)) as D2. pose proof (Z.mod_pos_bound u2 m Hm) as B2.
    rewrite (Z.mod_small (m * (u2 / m))) by nia. rewrite (Z.mod_small (m * (u1 / m))) by nia.
    destruct Hm64 as [w Hw64].
    assert (T12 : tden E ts2 = tden E ts1 + (q1 - q2) * 2 ^ 64) by lia.
    assert (HK2 : u2 = u1 + (c2 - c1) + (q1 - q2) * w * m).
    { rewrite Hw64 in T12. replace ((q1 - q2) * w * m) with ((q1 - q2) * (w * m)) by ring. lia. }
    set (kk := (c2 - c1) mod m) in *.
    pose proof (Z.mod_pos_bound (c2 - c1) m Hm) as Bk. pose proof (Z.div_mod (c2 - c1) m ltac:(lia)) as Dk. fold kk in Bk, Dk.
    (* [comment removed for export] *)
    assert (Hr2 : u2 mod m = (u1 mod m + kk) mod m).
    { rewrite HK2. replace (u1 + (c2 - c1) + (q1 - q2) * w * m) with ((u1 mod m + kk) + (u1 / m + (c2 - c1) / m + (q1 - q2) * w) * m) by lia.
      rewrite Z.mod_add by lia. reflexivity. }
    assert (DIFF : m * (u2 / m) - m * (u1 / m) = (c2 - c1) - kk + (if u1 mod m + kk <? m then 0 else m) + (q1 - q2) * w * m).
    { assert (E2 : m * (u2 / m) = u2 - u2 mod m) by lia. assert (E1 : m * (u1 / m) = u1 - u1 mod m) by lia.
      rewrite E2, E1, Hr2. destruct (Z.ltb_spec (u1 mod m + kk) m).
      - rewrite Z.mod_small by lia. lia.
      - replace ((u1 mod m + kk) mod m) with (u1 mod m + kk - m) by (apply Z.mod_unique with (q := 1); lia). lia. }
    rewrite DIFF.
    replace (c2 - c1 - kk + (if u1 mod m + kk <? m then 0 else m) + (q1 - q2) * w * m) with ((c2 - c1 - kk + (if u1 mod m + kk <? m then 0 else m)) + (q1 - q2) * 2 ^ 64) by (rewrite Hw64; ring).
    rewrite Z.mod_add by lia.
    rewrite Z.mod_small.
    2:{ destruct (u1 mod m + kk <? m) eqn:Hq; destruct (Z.ltb_spec (rhi1 + kk) m); destruct (Z.leb_spec m (rlo1 + kk)); unfold two64 in Hhi; try lia;
        apply Z.ltb_lt in Hq || apply Z.ltb_ge in Hq; lia. }
    destruct (u1 mod m + kk <? m) eqn:Hq; destruct (Z.ltb_spec (rhi1 + kk) m); destruct (Z.leb_spec m (rlo1 + kk));
      (apply Z.ltb_lt in Hq || apply Z.ltb_ge in Hq); lia.
  Qed.

  Theorem node_srlsharp_sound : forall r,
    node1_stmt SEGS A nx0 LIMIT SINV argH FS0 always (fun cs => node_srlsharp cs r).
  Proof.
    intros r cs cs' E R FULL model TT HC _ Hn Hk. cbv beta in Hn. unfold node_srlsharp in Hn.
    destruct (Nat.ltb 0 r && Nat.ltb r 32)%bool; [|discriminate Hn].
    destruct (lin_of (reg cs r)) as [c ts].
    apply some_inj_acs' in Hn. subst cs'.
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
    assert (HF : forall l, know_ok SEGS E (Mr A argH E cs model FULL) (flat_map (fun t : Z * expr => srl_atom_fact (kn cs) (snd t)) l)).
    { induction l as [|t l IH]; [constructor|]. cbn [flat_map]. apply Forall_app. split; [apply srl_atom_fact_sound; exact HK | exact IH]. }
    specialize (Hk E R FULL model (conj (env_agree_refl _ _) (env_agree_refl _ _))).
    rewrite pc_set_kn in Hk. apply Hk; [|reflexivity].
    apply cs_ok_set_kn; [exact HC|]. apply Forall_app. split; [apply HF | exact HK].
  Qed.

  Theorem node_srlsharp2_sound : forall r1 r2,
    node1_stmt SEGS A nx0 LIMIT SINV argH FS0 always (fun cs => node_srlsharp2 cs r1 r2).
  Proof.
    intros r1 r2 cs cs' E R FULL model TT HC _ Hn Hk. cbv beta in Hn. unfold node_srlsharp2 in Hn.
    match type of Hn with (if ?c then _ else _) = _ => destruct c; [|discriminate Hn] end.
    destruct (lin_of (reg cs r1)) as [c1 ts1]. destruct (lin_of (reg cs r2)) as [c2 ts2].
    apply some_inj_acs' in Hn. subst cs'.
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
    assert (HF : forall l, know_ok SEGS E (Mr A argH E cs model FULL) (flat_map (fun t : Z * expr => srl_atom_fact (kn cs) (snd t)) l)).
    { induction l as [|t l IH]; [constructor|]. cbn [flat_map]. apply Forall_app. split; [apply srl_atom_fact_sound; exact HK | exact IH]. }
    specialize (Hk E R FULL model (conj (env_agree_refl _ _) (env_agree_refl _ _))).
    rewrite pc_set_kn in Hk. apply Hk; [|reflexivity].
    apply cs_ok_set_kn; [exact HC|]. apply Forall_app. split; [apply srl_pair_fact_sound; exact HK|].
    apply Forall_app. split; [apply HF|]. apply Forall_app. split; [apply HF | exact HK].
  Qed.


  Theorem node_droplenfacts_sound : node1_stmt SEGS A nx0 LIMIT SINV argH FS0 always (fun cs => node_droplenfacts cs).
  Proof.
    intros cs cs' E R FULL model TT HC _ Hn Hk. cbv beta in Hn. unfold node_droplenfacts in Hn.
    destruct (a_fd cs) as [|kb len off|]; try discriminate Hn.
    apply some_inj_acs' in Hn. subst cs'.
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
    specialize (Hk E R FULL model (conj (env_agree_refl _ _) (env_agree_refl _ _))).
    rewrite pc_set_kn in Hk. apply Hk; [|reflexivity].
    apply cs_ok_set_kn; [exact HC|]. apply Forall_forall. intros K HinK. apply filter_In in HinK as [HinK _].
    exact (proj1 (Forall_forall _ _) HK K HinK).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Theorem io_xn_sound : forall id args,
    node1_stmt SEGS A nx0 LIMIT SINV argH FS0 always (ION.xn SEGS T id args).
  Proof.
    intros id args.
    assert (NONE : node1_stmt SEGS A nx0 LIMIT SINV argH FS0 always (fun _ => None)) by (intros cs cs' E R FULL model TT HC _ Hn Hk; discriminate).
    unfold ION.xn.
    do 10 (destruct id as [|id]; [exact NONE|]).
    destruct id as [|id]; [exact node_openat_err_sound|].
    destruct id as [|id]; [exact (node_read_sound args)|].
    destruct id as [|id]; [exact node_read_havoc_sound|].
    destruct id as [|id]; [exact node_read_eof_sound|].
    destruct id as [|id]; [exact node_read_dir_sound|].
    destruct id as [|id]; [exact node_close_sound|].
    destruct id as [|id]; [exact node_ioctl_sound|].
    destruct id as [|id]; [exact node_read_havoc_short_sound|].
    destruct id as [|id]; [exact node_header_facts_sound|].
    destruct id as [|id]; [exact node_lensplit_sound|].
    destruct id as [|id]; [exact NONE|].
    destruct id as [|id]; [exact NONE|].
    destruct id as [|id].
    { destruct args as [|[zr| | | | | | |] [|[zl| | | | | | |] [|? ?]]]; try exact NONE.
      - destruct (Z.leb 0 zr); [exact (node_fresha_sound (Z.to_nat zr) zl None) | exact NONE].
      - destruct e as [rb| | | | | | |]; try exact NONE. destruct l; [|exact NONE].
        match goal with |- node1_stmt _ _ _ _ _ _ _ _ (fun cs => if ?c then _ else _) => destruct c; [exact (node_fresha_sound (Z.to_nat zr) zl (Some (Z.to_nat rb))) | exact NONE] end. }
    destruct id as [|id].
    { destruct args as [|[zr| | | | | | |] [|[z1| | | | | | |] [|? ?]]]; try exact NONE.
      - destruct (Z.leb 0 zr); [exact (node_srlsharp_sound (Z.to_nat zr)) | exact NONE].
      - match goal with |- node1_stmt _ _ _ _ _ _ _ _ (fun cs => if ?c then _ else _) => destruct c; [exact (node_srlsharp2_sound (Z.to_nat z1) (Z.to_nat zr)) | exact NONE] end. }
    destruct id as [|id]; [exact node_droplenfacts_sound|].
    exact NONE.
  Qed.

  Theorem io_xb_sound : forall id args cs csa csb E R FULL model TA TB,
    cs_ok E cs R FULL model -> ION.xb SEGS nx0 T id args cs = Some (csa, csb) ->
    (forall E' R' FULL' model', env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' csa R' FULL' model' -> m_fs model' = m_fs model ->
        srealizes SEGS (cfg R' (pc csa) FULL' model') TA) ->
    (forall E' R' FULL' model', env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' csb R' FULL' model' -> m_fs model' = m_fs model ->
        srealizes SEGS (cfg R' (pc csb) FULL' model') TB) ->
    srealizes SEGS (cfg R (pc cs) FULL model) (t_alt2 TA TB).
  Proof.
    intros id args cs csa csb E R FULL model TA TB HC Hn HA HB. unfold ION.xb in Hn.
    destruct id as [|id]; [|discriminate].
    eapply node_openat2_sound; eassumption.
  Qed.

  (* [comment removed for export] *)
  Corollary io_ext_stmt : ext_stmt SEGS A nx0 LIMIT (ION.xn SEGS T) SINV argH FS0.
  Proof. exact io_xn_sound. Qed.
  Corollary io_ext2_stmt : ext2_stmt SEGS A nx0 LIMIT (ION.xb SEGS nx0 T) SINV argH FS0.
  Proof. exact io_xb_sound. Qed.

End IOSound.
