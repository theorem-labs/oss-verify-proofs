(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From Stdlib Require Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require PropExec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require MState.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Mem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Cells.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Step.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Frame.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require AImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_rep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_kit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_art.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Ceil.
Module RT_artG.
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Mem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Cells OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Frame OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_kit.RT_shlem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.ABand.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition class_ok_b (s : Z) : bool :=
  (s <=? csize (classid s)) && (1 <=? classid s) && (classid s <=? 30).

(* [comment removed for export] *)
Fixpoint check_upto (f : Z -> bool) (fuel : nat) (z : Z) : bool :=
  match fuel with O => true | S k => f z && check_upto f k (z + 1) end.
Lemma check_upto_sound : forall f fuel z, check_upto f fuel z = true ->
  forall x, z <= x < z + Z.of_nat fuel -> f x = true.
Proof.
  intros f fuel. induction fuel as [|k IH]; intros z H x Hx; [lia|].
  cbn [check_upto] in H. apply andb_true_iff in H as [H1 H2].
  destruct (Z.eq_dec x z) as [->|NE]; [exact H1|]. apply (IH (z + 1) H2). lia.
Qed.

Lemma class_ok_all : check_upto class_ok_b 65536 1 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma class_ok : forall s, 1 <= s <= 65536 -> s <= csize (classid s) /\ 1 <= classid s <= 30.
Proof.
  intros s Hs. pose proof (check_upto_sound _ _ _ class_ok_all s) as H. change (Z.of_nat 65536) with 65536%Z in H. specialize (H ltac:(lia)).
  unfold class_ok_b in H. apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3. lia.
Qed.

Lemma rz_log_range : forall n, 0 <= rz_log n <= 7.
Proof. intros n. unfold rz_log. repeat (destruct (_ <=? _)); lia. Qed.

Lemma rz_size_eq : forall n, rz_size n = 16 * 2 ^ rz_log n.
Proof. intros n. unfold rz_size. rewrite Z.shiftl_mul_pow2 by (pose proof (rz_log_range n); lia). reflexivity. Qed.

Lemma rz_size_range : forall n, 16 <= rz_size n <= 2048 /\ rz_size n mod 16 = 0.
Proof.
  intros n. rewrite rz_size_eq. pose proof (rz_log_range n) as H.
  pose proof (Z.pow_le_mono_r 2 0 (rz_log n) ltac:(lia) ltac:(lia)) as L1.
  pose proof (Z.pow_le_mono_r 2 (rz_log n) 7 ltac:(lia) ltac:(lia)) as L2.
  change (2^0) with 1 in L1. change (2^7) with 128 in L2.
  split; [lia|]. rewrite Z.mul_comm. apply Z_mod_mult.
Qed.

Lemma usz_le_rounded8 : forall n, usz n <= rounded8 n /\ 8 <= rounded8 n /\ rounded8 n mod 8 = 0.
Proof.
  intros n. unfold usz, rounded8, roundup. split; [Z.div_mod_to_equations; lia|]. split; [Z.div_mod_to_equations; lia|].
  apply Z_mod_mult.
Qed.

Lemma needed0_ge : forall n, 24 <= needed0 n.
Proof. intros n. unfold needed0. pose proof (usz_le_rounded8 n). pose proof (rz_size_range n). lia. Qed.

(* [comment removed for export] *)
Lemma prim_facts : forall n, bprim n = true ->
  1 <= pclass n <= 30 /\ rz_size n + usz n <= pslot n /\ 32 <= pslot n /\ pslot n mod 32 = 0 /\ asz n = pslot n.
Proof.
  intros n Hp. unfold bprim, is_primary in Hp. apply Z.leb_le in Hp. unfold KMAXSIZE in Hp.
  pose proof (needed0_ge n). destruct (class_ok (needed0 n) ltac:(lia)) as [C1 C2].
  unfold pslot. unfold pclass. pose proof (usz_le_rounded8 n) as (U1 & U2 & U3).
  assert (E : needed0 n = rounded8 n + rz_size n) by reflexivity.
  split; [exact C2|]. split; [lia|]. split; [apply csize_pos; lia|]. split; [apply csize_mod32; lia|].
  unfold asz, is_primary. rewrite (proj2 (Z.leb_le _ _)); [reflexivity|]. unfold KMAXSIZE. lia.
Qed.

Lemma rz_log_small : forall n, n <= 64512 -> rz_log n <= 6.
Proof.
  intros n Hn. unfold rz_log.
  destruct (Z.leb_spec0 n 48); [lia|]. destruct (Z.leb_spec0 n 96); [lia|].
  destruct (Z.leb_spec0 n 448); [lia|]. destruct (Z.leb_spec0 n 3968); [lia|].
  destruct (Z.leb_spec0 n 16128); [lia|]. destruct (Z.leb_spec0 n 32256); [lia|].
  destruct (Z.leb_spec0 n 64512); lia.
Qed.
Lemma rz_log_big : forall n, 64512 < n -> rz_log n = 7.
Proof.
  intros n Hn. unfold rz_log.
  destruct (Z.leb_spec0 n 48); [lia|]. destruct (Z.leb_spec0 n 96); [lia|].
  destruct (Z.leb_spec0 n 448); [lia|]. destruct (Z.leb_spec0 n 3968); [lia|].
  destruct (Z.leb_spec0 n 16128); [lia|]. destruct (Z.leb_spec0 n 32256); [lia|].
  destruct (Z.leb_spec0 n 64512); [lia|]. reflexivity.
Qed.
Lemma rz_small : forall n, n <= 64512 -> rz_size n <= 1024.
Proof.
  intros n Hn. rewrite rz_size_eq. pose proof (rz_log_small n Hn). pose proof (rz_log_range n).
  pose proof (Z.pow_le_mono_r 2 (rz_log n) 6 ltac:(lia) ltac:(lia)) as L. change (2^6) with 64 in L. lia.
Qed.
Lemma rz_big : forall n, 64512 < n -> rz_size n = 2048.
Proof. intros n Hn. rewrite rz_size_eq, (rz_log_big n Hn). reflexivity. Qed.

(* [comment removed for export] *)
Lemma sec_facts : forall n, bprim n = false ->
  64512 < n /\ rz_size n = 2048 /\ smapsize n mod 4096 = 0 /\ usz n + 8192 <= smapsize n /\ asz n = smapsize n
  /\ needed n = rounded8 n + 4096.
Proof.
  intros n Hp. unfold bprim, is_primary in Hp. apply Z.leb_gt in Hp. unfold KMAXSIZE in Hp.
  pose proof (usz_le_rounded8 n) as (U1 & U2 & U3).
  assert (Hn : 64512 < n).
  { destruct (Z_lt_le_dec 64512 n) as [L|L]; [exact L|]. exfalso.
    pose proof (rz_small n L). unfold needed0 in Hp.
    assert (R : rounded8 n <= 64512) by (unfold rounded8, roundup; Z.div_mod_to_equations; lia). lia. }
  assert (RZ : rz_size n = 2048) by (apply rz_big; exact Hn).
  assert (ND : needed n = rounded8 n + 4096).
  { unfold needed, is_primary, KMAXSIZE. destruct (Z.leb_spec (needed0 n) 65536); [lia|]. unfold needed0. lia. }
  split; [exact Hn|]. split; [exact RZ|]. split; [|split; [|split]].
  - unfold smapsize, roundup. rewrite Z.add_mod, Z_mod_mult, Z.mod_same by lia. reflexivity.
  - unfold smapsize, roundup. rewrite ND. Z.div_mod_to_equations. lia.
  - unfold asz, is_primary, KMAXSIZE. destruct (Z.leb_spec (needed0 n) 65536); [lia| reflexivity].
  - exact ND.
Qed.

Lemma chunk_cptr_eq : forall c j, 1 <= c <= 31 -> 16 * chunk_cptr c j = j * csize c.
Proof.
  intros c j Hc. unfold chunk_cptr. pose proof (csize_mod32 c Hc). 
  assert (csize c mod 16 = 0) by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations. nia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma mod0_add : forall x y a, 0 < a -> x mod a = 0 -> y mod a = 0 -> (x + y) mod a = 0.
Proof. intros x y a Ha Hx Hy. rewrite Z.add_mod, Hx, Hy by lia. apply Z.mod_0_l. lia. Qed.
Lemma mod0_sub : forall x y a, 0 < a -> x mod a = 0 -> y mod a = 0 -> (x - y) mod a = 0.
Proof. intros x y a Ha Hx Hy. rewrite Zminus_mod, Hx, Hy by lia. apply Z.mod_0_l. lia. Qed.
Lemma mod0_trans : forall x a b, 0 < a -> 0 < b -> b mod a = 0 -> x mod b = 0 -> x mod a = 0.
Proof.
  intros x a b Ha Hb H1 H2. apply Z.mod_divide in H1; [|lia]. apply Z.mod_divide in H2; [|lia]. apply Z.mod_divide; [lia|].
  eapply Z.divide_trans; eauto.
Qed.
Lemma mod0_of_sub : forall x y a, 0 < a -> (x - y) mod a = 0 -> y mod a = 0 -> x mod a = 0.
Proof. intros x y a Ha H1 H2. replace x with ((x - y) + y) by lia. apply mod0_add; assumption. Qed.
Lemma le_floor8 : forall a b, a mod 8 = 0 -> a <= b -> a <= b / 8 * 8.
Proof. intros a b Ha Hab. Z.div_mod_to_equations. lia. Qed.
Lemma ceil8_le : forall a e, e mod 8 = 0 -> a < e -> a / 8 * 8 + 8 <= e.
Proof. intros a e He Hae. Z.div_mod_to_equations. lia. Qed.
Lemma roundup16_le : forall x e, e mod 16 = 0 -> x <= e -> roundup x 16 <= e.
Proof. intros. unfold roundup. Z.div_mod_to_equations. lia. Qed.

Section G.
Variable st : rtstate.
Hypothesis WF : RTWF st.

Let P := st_pbase st.
Let S := st_spacebeg st.

Lemma P_range : KHIGHMEM_BEG <= P /\ P + PRIM_RES_SIZE <= alloc_ceiling /\ P mod 4096 = 0.
Proof.
  pose proof (wb_ranges st (wf_base_ok st WF) (P, P + PRIM_RES_SIZE) ltac:(left; reflexivity)) as H. cbn [fst snd] in H.
  pose proof (wb_P_align st (wf_base_ok st WF)). unfold P in *.
  destruct H as ([HS _] & H2 & H3 & H4). unfold sclr, PRIM_RES_SIZE, KLOWSHADOW_BEG in HS.
  pose proof (oclr_lin _ _ (proj1 (wb_ranges st (wf_base_ok st WF) (st_pbase st, st_pbase st + PRIM_RES_SIZE) ltac:(left; reflexivity))) ltac:(cbn [fst snd]; unfold PRIM_RES_SIZE; lia)) as (L0 & _ & _).
  cbn [fst snd] in L0. unfold PRIM_RES_SIZE in *. lia.
Qed.

Lemma S_range : P <= S /\ S + KSPACESIZE + 4096 <= P + PRIM_RES_SIZE /\ S mod 4096 = 0.
Proof. pose proof (wb_P_S st (wf_base_ok st WF)). pose proof (wb_S_align st (wf_base_ok st WF)). unfold P, S in *. lia. Qed.

Lemma rbeg_val : forall c, rbeg st c = S + c * KREGIONSIZE.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma carved_chunk : forall c k, 0 <= c < KNUMCLASSES -> 1 <= c -> carved_cptr st c k ->
  rbeg st c <= cptr_addr st c k /\ cptr_addr st c k + csize c <= rbeg st c + r_allocated (rg st c)
  /\ (cptr_addr st c k - rbeg st c) mod csize c = 0.
Proof.
  intros c k Hc Hc1 (j & Hj & ->). pose proof (wf_class_ok st WF c Hc) as WC.
  pose proof (wc_alloc_carved st c WC) as E. unfold cptr_addr. unfold KNUMCLASSES in Hc.
  rewrite chunk_cptr_eq by lia.
  pose proof (csize_pos c ltac:(lia)) as SP.
  split; [nia|]. split; [rewrite E; nia|]. replace (rbeg st c + j * csize c - rbeg st c) with (j * csize c) by lia. apply Z_mod_mult.
Qed.

Lemma region_range : forall c, 0 <= c < KNUMCLASSES ->
  P <= rbeg st c /\ r_mapped (rg st c) <= KFREEARRAY_OFF /\ rbeg st c + KREGIONSIZE <= S + KSPACESIZE
  /\ rbeg st c mod 4096 = 0 /\ 0 <= r_allocated (rg st c) <= r_mapped (rg st c)
  /\ r_mapped (rg st c) mod 2^18 = 0.
Proof.
  intros c Hc. pose proof (wf_class_ok st WF c Hc) as WC. pose proof S_range as (S1 & S2 & S3).
  pose proof (wc_mapped_max st c WC). pose proof (wc_alloc_mapped st c WC). pose proof (wc_alloc_nonneg st c WC).
  pose proof (wc_mapped_align st c WC).
  rewrite !rbeg_val. unfold KREGIONSIZE, KSPACESIZE, KNUMCLASSES, KFREEARRAY_OFF in *.
  assert (AL : (S + c * 2^32) mod 4096 = 0).
  { apply mod0_add; [lia| exact S3|]. replace (c * 2^32) with ((c * 2^20) * 4096) by lia. apply Z_mod_mult. }
  repeat split; try lia; try exact AL.
Qed.

(* [comment removed for export] *)
Lemma block_geom : forall A n, In (A, n) (all_blocks st) ->
  0 <= n < 2^40 /\ A mod 16 = 0
  /\ ablk (b_lo A n) (b_hi A n) /\ b_lo A n + 16 <= A /\ A + usz n <= b_hi A n /\ b_hi A n <= alloc_ceiling   (* [comment removed for export] *)
  /\ b_lo A n mod 16 = 0 /\ b_hi A n mod 16 = 0 /\ A = b_lo A n + 8 * sh_left n
  /\ (bprim n = true ->
        let c := pclass n in 1 <= c <= 30 /\ rbeg st c <= b_lo A n /\ b_hi A n <= rbeg st c + r_mapped (rg st c)
        /\ P <= b_lo A n /\ b_hi A n + 4096 <= P + PRIM_RES_SIZE /\ b_hi A n = b_lo A n + csize c)
  /\ (bprim n = false ->
        In (b_lo A n, n) (st_sec st) /\ b_hi A n = b_lo A n + smapsize n /\ A + usz n + 2048 <= b_hi A n /\ b_lo A n mod 4096 = 0).
Proof.
  intros A n Hin. pose proof (wk_block st (wf_blocks_ok st WF) (A, n) Hin) as WB.
  unfold wf_block in WB. cbn [fst snd] in WB. destruct WB as (Hn & HA & HP & HS).
  pose proof P_range as (P1 & P2 & P3). pose proof S_range as (S1 & S2 & S3).
  pose proof (rz_size_range n) as (Z1 & Z2).
  destruct (bprim n) eqn:EP.
  - (* [comment removed for export] *)
    destruct (HP eq_refl) as (Hc & Hk & Hab). clear HS HP.
    destruct (prim_facts n EP) as (_ & F2 & F3 & F4 & F5).
    set (c := pclass n) in *.
    unfold pslot in F2, F3, F4. change (pclass n) with c in F2, F3, F4.
    pose proof (csize_pos c ltac:(lia)) as SP.
    assert (Hc32 : 0 <= c < KNUMCLASSES) by (unfold KNUMCLASSES; lia).
    assert (CV : carved_cptr st c (b_cptr st A n)).
    { apply (wc_used_carved st c (wf_class_ok st WF c Hc32)). unfold used_cptrs. rewrite !in_app_iff.
      unfold all_blocks in Hin. apply in_app_iff in Hin. destruct Hin as [Hin|Hin]; [| apply in_app_iff in Hin; destruct Hin as [Hin|Hin]].
      - right; left. unfold live_cptrs. apply in_map_iff. exists (A, n). split; [reflexivity|]. unfold lb_prim. apply filter_In. split; [exact Hin|]. cbn [snd]. rewrite EP. cbn [andb]. apply Z.eqb_refl.
      - right; right; left. unfold quar_cptrs. apply in_map_iff. exists (A, n). split; [reflexivity|]. unfold q_prim. apply filter_In. split; [exact Hin|]. cbn [snd]. rewrite EP. cbn [andb]. apply Z.eqb_refl.
      - right; right; right; left. unfold qpend_cptrs. apply in_map_iff. exists (A, n). split; [reflexivity|]. unfold qp_prim. apply filter_In. split; [exact Hin|]. cbn [snd]. rewrite EP. cbn [andb]. apply Z.eqb_refl. }
    destruct (carved_chunk c (b_cptr st A n) Hc32 ltac:(lia) CV) as (C1 & C2 & C3).
    destruct (region_range c Hc32) as (R1 & R2 & R3 & R4 & R5 & R6).
    assert (Ebl : b_lo A n = cptr_addr st c (b_cptr st A n)) by (unfold b_lo; rewrite EP; exact Hab).
    assert (Ebh : b_hi A n = b_lo A n + csize c) by (unfold b_hi; rewrite F5; reflexivity).
    assert (EA : A = b_lo A n + rz_size n) by (unfold b_lo; rewrite EP; unfold b_alloc_beg; lia).
    assert (Hsl : sh_left n = rz_size n / 8) by (unfold sh_left; rewrite EP; reflexivity).
    pose proof (csize_mod32 c ltac:(lia)) as M32.
    rewrite <- Ebl in C1, C2, C3. clear Ebl.
    set (L := b_lo A n) in *. set (s := csize c) in *. set (rb := rbeg st c) in *.
    unfold KREGIONSIZE, KSPACESIZE, KFREEARRAY_OFF, KNUMCLASSES in *.
    assert (AL16 : L mod 16 = 0).
    { apply (mod0_of_sub L rb 16 ltac:(lia)).
      - apply (mod0_trans _ 16 s); [lia| lia| apply (mod0_trans _ 16 32); [lia|lia|reflexivity|exact M32]| exact C3].
      - apply (mod0_trans _ 16 4096); [lia| lia| reflexivity| exact R4]. }
    assert (AH16 : (L + s) mod 16 = 0).
    { apply mod0_add; [lia| exact AL16| apply (mod0_trans _ 16 32); [lia|lia|reflexivity|exact M32]]. }
    assert (RB : rb + 2^32 <= S + 2^37).
    { subst rb. rewrite rbeg_val. unfold KREGIONSIZE. clear - Hc. nia. }
    assert (AL8 : L mod 8 = 0) by (apply (mod0_trans _ 8 16); [lia|lia|reflexivity|exact AL16]).
    assert (EA8 : A = L + 8 * sh_left n) by (rewrite Hsl; clear - EA Z2 Z1; Z.div_mod_to_equations; lia).
    clear C3 M32 R4 R6 P3 S3 Hsl Hab CV Hk.
    split; [exact Hn|]. split; [exact HA|].
    assert (HBHI : b_hi A n <= alloc_ceiling) by (clear - Ebh C2 R5 R2 RB S2 P2; lia).
    split; [apply ablk_high; [clear - P1 R1 C1; lia| exact HBHI]|]. split; [clear - EA Z1; lia|]. split; [clear - EA F2 Ebh; lia|].
    split; [exact HBHI|].
    split; [exact AL16|]. split; [rewrite Ebh; exact AH16|]. split; [exact EA8|].
    split.
    + intros _. cbn zeta. change (pclass n) with c.
      split; [exact Hc|]. split; [exact C1|]. split; [clear - Ebh C2 R5; lia|].
      split; [clear - R1 C1; lia|]. split; [clear - Ebh C2 R5 R2 RB S2; lia|]. exact Ebh.
    + intros X. discriminate.
  - (* [comment removed for export] *)
    specialize (HS eq_refl). clear HP.
    destruct (sec_facts n EP) as (F1 & F2 & F3 & F4 & F5 & F6).
    destruct (ws_entry st (wf_sec_ok st WF) _ HS) as (_ & _ & MB & _). cbn [fst snd] in MB. pose proof MB as MB'.
    assert (RR : In (b_map_beg A, b_map_beg A + smapsize n) (rt_ranges st)).
    { unfold rt_ranges. do 2 right. rewrite !in_app_iff. right; left. apply in_map_iff. exists (b_map_beg A, n). split; [reflexivity| exact HS]. }
    pose proof (wb_ranges st (wf_base_ok st WF) _ RR) as RG. cbn [fst snd] in RG.
    assert (Ebl : b_lo A n = b_map_beg A) by (unfold b_lo; rewrite EP; reflexivity).
    assert (Ebh : b_hi A n = b_lo A n + smapsize n) by (unfold b_hi; rewrite F5; reflexivity).
    assert (EA : A = b_lo A n + 6144) by (rewrite Ebl; unfold b_map_beg, SEC_RZ, SEC_HDR; lia).
    assert (Hsl : sh_left n = 768) by (unfold sh_left; rewrite EP; reflexivity).
    rewrite Ebl in *. set (L := b_map_beg A) in *.
    assert (AL16 : L mod 16 = 0) by (apply (mod0_trans _ 16 4096); [lia|lia|reflexivity|exact MB]).
    assert (AH16 : (L + smapsize n) mod 16 = 0).
    { apply mod0_add; [lia| exact AL16| apply (mod0_trans _ 16 4096); [lia|lia|reflexivity|exact F3]]. }
    assert (AL8 : L mod 8 = 0) by (apply (mod0_trans _ 8 16); [lia|lia|reflexivity|exact AL16]).
    clear MB F3 P3 S3.
    split; [exact Hn|]. split; [exact HA|].
    split; [rewrite Ebh; apply oclr_ablk; [exact (proj1 RG)| clear - F1 F4; unfold usz in *; lia| clear - RG; lia]|]. split; [clear - EA; lia|]. split; [clear - EA F4 Ebh; lia|].
    split; [clear - Ebh RG; lia|].
    split; [exact AL16|]. split; [rewrite Ebh; exact AH16|]. split; [clear - EA Hsl; lia|].
    split.
    + intros X. discriminate.
    + intros _. split; [exact HS|]. split; [exact Ebh|]. split; [clear - EA F4 Ebh; lia|].
      apply (mod0_trans _ 4096 4096); [lia|lia|reflexivity|]. exact MB'.
Qed.

End G.


End CeilWrap.
End RT_artG.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_wf.
Import RT_artG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition cost_ok_b (n : Z) : bool :=
  is_primary n && (pslot n <=? 2 * n + 32) && (pslot n <=? n + 17408) && (32 <=? pslot n)
  && (negb (is_cl24 n) || ((5880 <? n) && (n <=? 7936))).
Lemma cost_ok_all : check_upto cost_ok_b 64513 0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma cost_ok : forall n, 0 <= n <= 64512 ->
  is_primary n = true /\ pslot n <= 2 * n + 32 /\ pslot n <= n + 17408 /\ 32 <= pslot n /\ (is_cl24 n = true -> 5880 < n <= 7936).
Proof.
  intros n Hn. pose proof (check_upto_sound _ _ _ cost_ok_all n) as H. change (Z.of_nat 64513) with 64513%Z in H. specialize (H ltac:(lia)).
  unfold cost_ok_b in H. apply andb_true_iff in H as [H H5]. apply andb_true_iff in H as [H H4]. apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H1 H2].
  apply Z.leb_le in H2. apply Z.leb_le in H3. apply Z.leb_le in H4.
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
  intros HC. rewrite HC in H5. cbn [negb orb] in H5. apply andb_true_iff in H5 as [A B]. apply Z.ltb_lt in A. apply Z.leb_le in B. lia.
Qed.
(* [comment removed for export] *)
Lemma nonprim_large : forall n, 0 <= n -> is_primary n = false -> 64512 < n.
Proof. intros n Hn H. destruct (Z.le_gt_cases n 64512) as [L|L]; [| exact L]. destruct (cost_ok n ltac:(lia)) as (P & _). congruence. Qed.
Lemma is_cl24_range : forall n, 0 <= n -> is_cl24 n = true -> 5880 < n <= 7936.
Proof.
  intros n Hn H. assert (P : is_primary n = true) by (unfold is_cl24 in H; apply andb_true_iff in H; exact (proj1 H)).
  destruct (Z.le_gt_cases n 64512) as [L|L]; [exact (proj2 (proj2 (proj2 (proj2 (cost_ok n ltac:(lia))))) H)|].
  (* [comment removed for export] *)
  exfalso. unfold is_primary, KMAXSIZE, needed0, rounded8, roundup in P. apply Z.leb_le in P.
  rewrite (rz_big n L) in P. Z.div_mod_to_equations. lia.
Qed.
Lemma smapsize_le : forall n, 0 <= n -> is_primary n = false -> smapsize n <= n + 12296.
Proof.
  intros n Hn HP. pose proof (nonprim_large n Hn HP) as L. unfold smapsize, needed. rewrite HP.
  unfold needed0, rounded8, roundup. rewrite (rz_big n L). Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem cost_malloc_le4 : forall n, 0 <= n -> cost_malloc n <= 4 * n + (69696 + 2^19 + CL24_TAX).
Proof.
  intros n Hn. unfold cost_malloc, asz, SEC_SLOT_TAX, CL24_TAX. destruct (is_primary n) eqn:P.
  - destruct (Z.le_gt_cases n 64512) as [L|L].
    + destruct (cost_ok n ltac:(lia)) as (_ & _ & B & _). destruct (is_cl24 n); lia.
    + exfalso. unfold is_primary, KMAXSIZE, needed0, rounded8, roundup in P. apply Z.leb_le in P.
      rewrite (rz_big n L) in P. Z.div_mod_to_equations. lia.
  - pose proof (smapsize_le n Hn P). assert (C : is_cl24 n = false) by (unfold is_cl24; rewrite P; reflexivity). rewrite C. lia.
Qed.
Theorem cost_malloc_le13_noncl24 : forall n, 0 <= n -> is_cl24 n = false -> cost_malloc n <= 13 * n + 192.
Proof.
  intros n Hn HC. unfold cost_malloc, asz, SEC_SLOT_TAX. rewrite HC. destruct (is_primary n) eqn:P.
  - destruct (Z.le_gt_cases n 64512) as [L|L].
    + destruct (cost_ok n ltac:(lia)) as (_ & A & _). lia.
    + exfalso. unfold is_primary, KMAXSIZE, needed0, rounded8, roundup in P. apply Z.leb_le in P.
      rewrite (rz_big n L) in P. Z.div_mod_to_equations. lia.
  - pose proof (smapsize_le n Hn P). pose proof (nonprim_large n Hn P). lia.
Qed.
Theorem cost_malloc_le8_prim : forall n, 0 <= n <= 64512 -> is_cl24 n = false -> cost_malloc n <= 8 * n + 192.
Proof.
  intros n Hn HC. destruct (cost_ok n Hn) as (P & A & _). unfold cost_malloc, asz, SEC_SLOT_TAX. rewrite HC, P. lia.
Qed.
Theorem cost_malloc_lin : forall n, 0 <= n -> cost_malloc n <= 281 * n + 192.
Proof.
  intros n Hn. destruct (is_cl24 n) eqn:HC; [| pose proof (cost_malloc_le13_noncl24 n Hn HC); lia].
  pose proof (is_cl24_range n Hn HC) as R. destruct (cost_ok n ltac:(lia)) as (P & A & _).
  unfold cost_malloc, asz, SEC_SLOT_TAX, CL24_TAX. rewrite HC, P. lia.
Qed.
Lemma cost_malloc_pos : forall n, 0 <= n -> 192 <= cost_malloc n.
Proof.
  intros n Hn. unfold cost_malloc, asz, SEC_SLOT_TAX, CL24_TAX. destruct (is_primary n) eqn:P.
  - destruct (Z.le_gt_cases n 64512) as [L|L]; [destruct (cost_ok n ltac:(lia)) as (_ & _ & _ & C & _); destruct (is_cl24 n); lia|].
    exfalso. unfold is_primary, KMAXSIZE, needed0, rounded8, roundup in P. apply Z.leb_le in P. rewrite (rz_big n L) in P. Z.div_mod_to_equations. lia.
  - unfold smapsize, roundup, needed. rewrite P. unfold needed0, rounded8, roundup.
    pose proof (rz_size_range n) as [[RZ _] _]. destruct (is_cl24 n); Z.div_mod_to_equations; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma zsum_nonneg_map : forall {A} (f : A -> Z) l, (forall x, In x l -> 0 <= f x) -> 0 <= zsum (map f l).
Proof. intros A f l H. induction l as [|x l IH]; cbn; [lia|]. unfold zsum in *. cbn. specialize (IH ltac:(intros y Hy; apply H; right; exact Hy)). pose proof (H x ltac:(left; reflexivity)). lia. Qed.
Lemma zlen_map : forall {A B} (f : A -> B) l, zlen (map f l) = zlen l.
Proof. intros. unfold zlen. rewrite length_map. reflexivity. Qed.
Lemma zlen_filter_le : forall {A} (f : A -> bool) l, zlen (List.filter f l) <= zlen l.
Proof. intros A f l. unfold zlen. induction l as [|x l IH]; cbn; [lia|]. destruct (f x); cbn; lia. Qed.
(* [comment removed for export] *)
Lemma count_weight : forall {A} (P : A -> bool) (g : A -> Z) K l,
  (forall x, In x l -> 0 <= g x) -> (forall x, In x l -> P x = true -> K <= g x) ->
  K * zlen (List.filter P l) <= zsum (map g l).
Proof.
  intros A P g K l. induction l as [|x l IH]; intros G1 G2; cbn; [unfold zlen, zsum; cbn; lia|].
  unfold zsum in *. cbn. specialize (IH ltac:(intros y Hy; apply G1; right; exact Hy) ltac:(intros y Hy; apply G2; right; exact Hy)).
  pose proof (G1 x ltac:(left; reflexivity)). destruct (P x) eqn:E.
  - pose proof (G2 x ltac:(left; reflexivity) E). rewrite zlen_cons. lia.
  - lia.
Qed.
Lemma zsum_skipn_le : forall (g : Z * Z -> Z) k l, (forall x, In x l -> 0 <= g x) -> zsum (map g (skipn k l)) <= zsum (map g l).
Proof.
  intros g k l. revert k. induction l as [|x l IH]; intros k G; [destruct k; cbn; lia|].
  destruct k as [|k]; cbn; [lia|]. unfold zsum in *. cbn. specialize (IH k ltac:(intros y Hy; apply G; right; exact Hy)).
  pose proof (G x ltac:(left; reflexivity)). cbn in IH. lia.
Qed.

Lemma zsum_skipn_flat_le : forall (g : Z * Z -> Z) (l : list (qbatch * Z)), (forall x, 0 <= g x) ->
  zsum (map g (flat_map (fun bd : qbatch * Z => skipn (Z.to_nat (snd bd)) (qb_elems (fst bd))) l)) <= zsum (map g (flat_map qb_elems (map fst l))).
Proof.
  intros g l G. induction l as [|bd l IH]; [apply Z.le_refl|]. cbn [flat_map map]. rewrite !map_app, !zsum_app.
  pose proof (zsum_skipn_le g (Z.to_nat (snd bd)) (qb_elems (fst bd)) ltac:(intros; apply G)). lia.
Qed.

(* [comment removed for export] *)
Lemma qb_size_eq : forall b, qb_size b = QBATCH_SIZE + zsum (map (fun e : Z * Z => Z.max (snd e) 1) (qb_elems b)).
Proof. intros b. unfold qb_size, zsum. induction (qb_elems b) as [|e l IH]; cbn; [lia|]. cbn in IH. lia. Qed.
Lemma qc_bytes_eq : forall q, qc_bytes q = QBATCH_SIZE * zlen q + zsum (map (fun e : Z * Z => Z.max (snd e) 1) (flat_map qb_elems q)).
Proof.
  induction q as [|b q IH]; [reflexivity|]. cbn [qc_bytes fold_right flat_map]. fold (qc_bytes q). rewrite IH, qb_size_eq, map_app, zsum_app, zlen_cons. lia.
Qed.

Lemma qc_bytes_nonneg' : forall q, 0 <= qc_bytes q.
Proof. intros q. rewrite qc_bytes_eq. pose proof (zlen_nonneg q). pose proof (zsum_nonneg_map (fun e : Z * Z => Z.max (snd e) 1) (flat_map qb_elems q) ltac:(intros; lia)). unfold QBATCH_SIZE. lia. Qed.

Lemma rt_prov_parts_nonneg : forall st, RTWF st ->
  0 <= prov_classes st /\ 0 <= prov_nb st /\ 0 <= prov_q st /\ 0 <= prov_ptr st /\ 0 <= prov_live st /\ 0 <= prov_quar st
  /\ 0 <= prov_depot st /\ 0 <= prov_slots st.
Proof.
  intros st WF. split; [apply prov_classes_nonneg|]. split; [unfold prov_nb; destruct (st_qthread st); unfold NB; lia|].
  split; [apply prov_q_nonneg; apply qc_bytes_nonneg'|]. split; [unfold prov_ptr; lia|]. split.
  { apply prov_live_nonneg. apply Forall_forall. intros b Hb.
    destruct (wk_block st (wf_blocks_ok st WF) b ltac:(unfold all_blocks; apply in_or_app; left; exact Hb)) as [Hn _]. lia. }
  split; [apply prov_quar_nonneg|]. split; [| apply prov_slots_nonneg].
  unfold prov_depot. pose proof (wd_nnb_max st (wf_depot_ok st WF)) as HN. pose proof (wd_nsb_max st (wf_depot_ok st WF)) as HS.
  unfold NODEBLOCK_SIZE, STOREBLOCK_SIZE. nia.
Qed.

Section C24.
Variable st : rtstate.
Hypothesis WF : RTWF st.

Let c24 := fun b : Z * Z => bprim (snd b) && (pclass (snd b) =? 24).
Let g := fun e : Z * Z => Z.max (snd e) 1.

Lemma c24_big : forall b, c24 b = true -> 0 <= snd b -> 5881 <= g b.
Proof.
  intros [A n] H Hn. unfold c24 in H. cbn [snd] in *. unfold g. cbn [snd].
  pose proof (is_cl24_range n Hn ltac:(unfold is_cl24; unfold bprim in H; exact H)). lia.
Qed.

(* [comment removed for export] *)
Lemma quar_weight :
  QBATCH_SIZE * zlen (qall st) + 5881 * zlen (q_prim st 24) <=
  qc_bytes (st_qthread st) + qc_bytes (st_qglobal st) + qc_bytes (st_qtmp st) + qc_bytes (map fst (st_qcur st)).
Proof.
  assert (NN : forall l, (forall x : Z * Z, In x l -> 0 <= g x)) by (intros l x _; unfold g; lia).
  assert (ALL : forall q, qc_bytes q = QBATCH_SIZE * zlen q + zsum (map g (flat_map qb_elems q))) by (intros q; apply qc_bytes_eq).
  rewrite !ALL. unfold qall. rewrite !zlen_app, zlen_map.
  (* [comment removed for export] *)
  assert (QE : 5881 * zlen (q_prim st 24) <=
               zsum (map g (flat_map qb_elems (st_qthread st))) + zsum (map g (flat_map qb_elems (st_qglobal st)))
               + zsum (map g (flat_map qb_elems (st_qtmp st))) + zsum (map g (flat_map qb_elems (map fst (st_qcur st))))).
  { unfold q_prim, qelems. rewrite !flat_map_app.
    assert (W : forall l, (forall b, In b l -> c24 b = true -> 0 <= snd b) -> 5881 * zlen (List.filter c24 l) <= zsum (map g l)).
    { intros l Hl. apply count_weight; [apply NN| intros x Hx Hc; apply c24_big; [exact Hc| exact (Hl x Hx Hc)]]. }
    assert (B : forall b, In b (qelems st) -> c24 b = true -> 0 <= snd b).
    { intros b Hb _. destruct (wk_block st (wf_blocks_ok st WF) b ltac:(unfold all_blocks; apply in_or_app; right; apply in_or_app; left; exact Hb)) as [Hn _]. lia. }
    unfold qelems in B. rewrite !flat_map_app in B.
    rewrite !filter_app, !zlen_app.
    pose proof (W (flat_map qb_elems (st_qthread st)) ltac:(intros b Hb Hc; apply (B b); [rewrite !in_app_iff; tauto| exact Hc])) as W1.
    pose proof (W (flat_map qb_elems (st_qglobal st)) ltac:(intros b Hb Hc; apply (B b); [rewrite !in_app_iff; tauto| exact Hc])) as W2.
    pose proof (W (flat_map qb_elems (st_qtmp st)) ltac:(intros b Hb Hc; apply (B b); [rewrite !in_app_iff; tauto| exact Hc])) as W3.
    pose proof (W (flat_map (fun bd : qbatch * Z => skipn (Z.to_nat (snd bd)) (qb_elems (fst bd))) (st_qcur st))
                  ltac:(intros b Hb Hc; apply (B b); [rewrite !in_app_iff; tauto| exact Hc])) as W4.
    pose proof (zsum_skipn_flat_le g (st_qcur st) ltac:(intros; unfold g; lia)) as SK.
    cbv delta [c24] in W1, W2, W3, W4. lia. }
  unfold QBATCH_SIZE in *. lia.
Qed.

(* [comment removed for export] *)
Lemma prov_l24_le_rt_prov : prov_l24 st <= rt_prov st.
Proof.
  pose proof (rt_prov_parts_nonneg st WF) as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8). pose proof (prov_emb_nonneg st). unfold rt_prov. lia.
Qed.

Theorem class24_populate_ok : rt_prov st <= 2^39 -> navail st 24 < nrefill 24 -> r_mapped (rg st 24) + 2^18 <= KFREEARRAY_OFF.
Proof.
  intros HP HN.
  assert (H24 : 0 <= 24 < KNUMCLASSES) by (unfold KNUMCLASSES; lia).
  pose proof (wf_class_ok st WF 24 H24) as WC.
  pose proof (wc_used_all st 24 WC) as UA. pose proof (wc_alloc_carved st 24 WC) as AC. pose proof (wc_residue st 24 WC) as RS.
  change (csize 24) with 8192 in AC, RS. assert (NR : nrefill 24 = 1) by reflexivity. rewrite NR in HN.
  (* [comment removed for export] *)
  unfold used_cptrs in UA. rewrite !zlen_app in UA. fold (navail st 24) in UA.
  unfold live_cptrs, quar_cptrs, qpend_cptrs, apend_cptrs, batch_cptrs, qbatch_addrs in UA. rewrite Z.eqb_refl in UA. rewrite !zlen_map in UA.
  (* [comment removed for export] *)
  assert (L24 : CL24_TAX * zlen (lb_prim st 24) <= 2^39).
  { pose proof prov_l24_le_rt_prov as LE. unfold prov_l24 in LE. lia. }
  (* [comment removed for export] *)
  pose proof (wq_inflight st (wf_quar_ok st WF)) as [IA IQ].
  pose proof (zlen_filter_le (fun b : Z * Z => bprim (snd b) && (pclass (snd b) =? 24)) (st_qpend st)) as FQ. fold (qp_prim st 24) in FQ.
  pose proof (zlen_filter_le (fun ck : Z * Z => fst ck =? 24) (st_apend st)) as FA.
  (* [comment removed for export] *)
  pose proof quar_weight as QW.
  pose proof (wq_thread_max st (wf_quar_ok st WF)) as T1. pose proof (wq_rec_max st (wf_quar_ok st WF)) as T2.
  pose proof (zlen_nonneg (qall st)). pose proof (zlen_nonneg (q_prim st 24)). pose proof (zlen_nonneg (lb_prim st 24)).
  unfold QBATCH_SIZE, QUAR_MAX_SIZE, QUAR_MAX_CACHE, CL24_TAX, KFREEARRAY_OFF in *.
  nia.
Qed.
End C24.


End CeilWrap.
