(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 922 of its 952 lines of code are new or changed and 218 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/reac_box_model_block_case6.v, with its module names changed; 21 of its 553 lines of code are new or changed and 420 lines of the source are left out. *)
(* GENERATED - do not edit.  C_reac_box_model_blockRB_case6.v is the re-based copy of lib/B/Prog/reac_box_model_block_case6.v at 20372bbcc3a
   (source sha256 39821419f028bad88a64bf9e6cdf195566d2775240cc6aecce4fdef566467587) by gen_rb_modelblock.py
   (its sha256 is cited in the commit that adds this file); the substitutions are listed there.  Dropped here: c6_call_nf, c6_loopr, c6_case6. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcRec RcRecLib RcBox RcBoxLib
  RcSynth RcSynthLib RcParseLib RcKindLib RcLay RcAsan RcAsanLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import RcAsanRT RcAsanFP RcAsanFPLib
  asan_stack_malloc_c asan_memset_c asan_memcpy_c build_dt1_single_c dt1_head_c name_field_c reac_box_model_block_c
  C_reac_box_model_blockRB C_reac_box_model_blockRB_case56.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import ShadowRwOn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import reac_box_model_block_c_on reac_box_model_block_cF_on.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import asan_stack_malloc_c_on asan_memset_c_on asan_memcpy_c_on C_reac_box_model_blockOnHB.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import name_field_c_on.
Import ListNotations.
Open Scope Z_scope.

(* reac_box_model_block, image B (asan-ubsan): the case b = 6 of the jump table at 0x86710 (0x86b24,
   name_field + build_ident_last), from its case PC to the frame release at 0x86e14, where the release
   continuation Hrel (the rel_stmt of the interface pin) takes over.  The ubsan twin is
   lib/U/Prog/C_reac_box_model_blockRB.v (case6, loopr, tail6); here the frame is the ASan frame (FK/BI of
   C_reac_box_model_blockRB.v), the record of build_ident_last is the 21 bytes at A + 35 of the window, and each
   load or store of o and of p has the shadow check before it.  The callee steps, the output block's check
   byte and the outer sum loop come from C_reac_box_model_blockRB_case56.v; the Section hypotheses they were
   proved under are supplied once by the c6_call_* / c6_loop6 wrappers below, because the walk clears those
   hypotheses (PERF). *)

(* The byte stores of this case write a register value, so the cell of a 1-byte store is read off le1 (as in
   the ubsan twin lib/U/Prog/C_reac_box_model_blockRB.v). *)
Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?bb] => constr:(C1 bb)
  | le1 (zxb ?bb) => constr:(C1 bb)
  | le1 ?v => constr:(C1 (Z_to_bv 8 (bv_unsigned v)))
  end.

(* ---- list facts about the window record (firstn / skipn / upd_bytes), proved from scratch ---- *)

Lemma c6_fa : forall (U V : list byte) (k : nat), length U = k -> firstn k (U ++ V) = U.
Proof.
  induction U as [|x U IH]; intros V k L; cbn [length] in L; subst k; [reflexivity|].
  cbn [app firstn]. f_equal. exact (IH V (length U) eq_refl).
Qed.

Lemma c6_sa : forall (U V : list byte) (k t : nat), length U = k -> skipn (k + t) (U ++ V) = skipn t V.
Proof.
  induction U as [|x U IH]; intros V k t L; cbn [length] in L; subst k; [reflexivity|].
  cbn [app]. replace (S (length U) + t)%nat with (S (length U + t))%nat by lia.
  cbn [skipn]. exact (IH V (length U) t eq_refl).
Qed.

Lemma c6_skk : forall (l : list byte) (n m : nat), skipn n (skipn m l) = skipn (n + m) l.
Proof.
  intros l n m. revert l n. induction m as [|m IH]; intros l n.
  - cbn [skipn]. rewrite Nat.add_0_r. reflexivity.
  - replace (n + S m)%nat with (S (n + m))%nat by lia.
    destruct l as [|x l]; cbn [skipn]; [destruct n; reflexivity | exact (IH l n)].
Qed.

Lemma c6_fall : forall (l : list byte) (n : nat), length l = n -> firstn n l = l.
Proof.
  intros l n L. rewrite <- L. clear L n.
  induction l as [|x l IH]; cbn [length firstn]; [reflexivity|]. f_equal. exact IH.
Qed.

Lemma c6_lf : forall (W : list byte) (k : nat), (k <= length W)%nat -> length (firstn k W) = k.
Proof. intros W k H. rewrite length_firstn. lia. Qed.

(* The first k + n bytes of a block whose n bytes at k were replaced by Y. *)
Lemma c6_fu : forall (W Y : list byte) (k n : nat), (k <= length W)%nat -> length Y = n ->
  firstn (k + n) (upd_bytes W k Y) = firstn k W ++ Y.
Proof.
  intros W Y k n HK LY. unfold upd_bytes. rewrite app_assoc.
  apply c6_fa. rewrite length_app, (c6_lf W k HK), LY. reflexivity.
Qed.

(* Past the replaced bytes, the block is the old one. *)
Lemma c6_sk : forall (W Y : list byte) (k n j : nat), (k <= length W)%nat -> length Y = n ->
  skipn (k + n + j) (upd_bytes W k Y) = skipn j (skipn (k + n) W).
Proof.
  intros W Y k n j HK LY. unfold upd_bytes.
  replace (k + n + j)%nat with (k + (n + j))%nat by lia.
  rewrite (c6_sa (firstn k W) _ k (n + j) (c6_lf W k HK)).
  rewrite <- LY. exact (c6_sa Y _ (length Y) j eq_refl).
Qed.

(* Two byte lists of the same length read at the same address are the same list. *)
Lemma c6_le_det : forall (u v : list byte), length u = length v ->
  (forall i, (i < length u)%nat -> nth_error u i = nth_error v i) -> u = v.
Proof.
  induction u as [|x u IH]; intros v L H.
  - destruct v as [|y v]; [reflexivity|]. cbn [length] in L. exfalso. lia.
  - destruct v as [|y v]; [cbn [length] in L; exfalso; lia|].
    cbn [length] in L.
    assert (E0 : nth_error (x :: u) 0 = nth_error (y :: v) 0) by (apply H; cbn [length]; lia).
    cbn [nth_error] in E0. injection E0 as E0. rewrite E0. f_equal.
    apply IH; [lia|]. intros i Hi. exact (H (S i) ltac:(cbn [length]; lia)).
Qed.

Lemma c6_bat_det : forall (mc : word -> option byte) (a : Z) (u v : list byte),
  bytes_at rsegs mc a u -> bytes_at rsegs mc a v -> length u = length v -> u = v.
Proof.
  intros mc a u v (_ & _ & Hu) (_ & _ & Hv) L.
  apply c6_le_det; [exact L|]. intros i Hi.
  rewrite <- (Hu i Hi). rewrite <- (Hv i ltac:(lia)). reflexivity.
Qed.

Section c6_S.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (p b o FS off A : Z) (row nb ob : list byte).
  Hypothesis HSM : asan_stack_malloc_0_contract_on.
  Hypothesis Hoff : off = ASAN_K.
  Hypothesis HA : A = (bv_unsigned sp - 160) / 32 * 32.
  Hypothesis HS16 : bv_unsigned sp mod 16 = 0.
  Hypothesis ST0 : stk rsegs m (bv_unsigned sp - 4272) (bv_unsigned sp).
  Hypothesis MI0 : mem_inv rsegs m.
  Hypothesis AC0 : asan_cells m.
  Hypothesis SR0 : shadow_rw_on (reac_box_model_block_shadow_R (bv_unsigned sp) FS p b o row nb) m.
  Hypothesis HHM : HIGHMEM_BEG <= bv_unsigned sp - 4272.
  Hypothesis HAE : bv_unsigned sp <= APPMEM_END.
  Hypothesis AW0 : addressable m (bv_unsigned sp - 4272) 4272.
  Hypothesis FP0 : fp [0%nat] m (bv_unsigned tp) FS (bv_unsigned sp - 4272) (bv_unsigned sp)
    (reac_box_model_block_W o (bv_unsigned sp)) (reac_box_model_block_D p o).
  Hypothesis TLS0 : reac_box_model_block_tls m (bv_unsigned tp) FS (bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K) (bv_unsigned sp).
  Hypothesis Rp : 0 <= p < 2^64.
  Hypothesis Rb : 0 <= b < 2^64.
  Hypothesis Ro : 0 <= o < 2^64.
  Hypothesis HP : p <> 0 -> p mod 8 = 0 /\ length row = 296%nat /\ bytes_at rsegs m p row /\
    (bv_unsigned sp <= p \/ p + 296 <= bv_unsigned sp - 4272) /\ (o = 0 \/ o + 32 <= p \/ p + 296 <= o).
  Hypothesis HN : p <> 0 -> (b = 5 \/ b = 6) -> has row <> 0 -> rname row <> 0 ->
    name_ok nb /\ bytes_at rsegs m (rname row) nb /\
    (bv_unsigned sp <= rname row \/ rname row + Z.of_nat (length nb) <= bv_unsigned sp - 4272) /\
    (o = 0 \/ o + 32 <= rname row \/ rname row + Z.of_nat (length nb) <= o).
  Hypothesis HO : o <> 0 -> rw_cells rsegs m o [CB 32 ob] /\
    (bv_unsigned sp <= o \/ o + 32 <= bv_unsigned sp - 4272) /\ (o + 32 <= JOIN_0013 \/ JOIN_0014 + 32 <= o).
  Hypothesis AP : p <> 0 -> addressable m p 296.
  Hypothesis ANB : p <> 0 -> (b = 5 \/ b = 6) -> has row <> 0 -> rname row <> 0 ->
    addressable m (rname row) (Z.of_nat (length nb)).
  Hypothesis AO : o <> 0 -> addressable m o 32 /\ app_mem (o + 32) /\ (o + 32 <= RT_LO \/ RT_HI <= o).
  Hypothesis AJ1 : b = 1 -> addressable m JOIN_0014 32.
  Hypothesis AJ2 : b = 2 -> addressable m JOIN_0013 32.
  Hypothesis NDJ : p <> 0 -> (b = 5 \/ b = 6) -> has row <> 0 -> rname row <> 0 ->
    fp_dj [(rname row, rname row + Z.of_nat (length nb))] (fp_w [0%nat] FS).

  Hypothesis HMS : asan_memset_contract_on.
  Hypothesis HMC : asan_memcpy_contract_on.
  Hypothesis HBD : build_dt1_single_contract_on.
  Hypothesis HDH : dt1_head_contract_on.
  Hypothesis HNF : name_field_contract_on.

  (* The release continuation at 0x86e14 (rel_stmt of mbb-interface-pin.md, verbatim). *)
  Hypothesis Hrel : forall (fr f spc j n : Z) (w56 : word) (mc : word -> option byte) (ret : Z)
       (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 : word),
  FK FS A fr f spc j n w56 ->
  ret = (if (p =? 0) || (o =? 0) then -1 else rc row b) ->
  BI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m FS
     (Wf sp FS fr j n ++ (if (p =? 0) || (o =? 0) then [] else [(o, o + 32)])) fr w56 mc ->
  (if (p =? 0) || (o =? 0) then True else bytes_at rsegs mc o (synth row b nb)) ->
  evt rsegs (Q0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb fr j n)
    (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 A) x10 x11 x12 x13 x14 x15 x16 x17
            (Z_to_bv 64 f) (Z_to_bv 64 o) (Z_to_bv 64 p) (Z_to_bv 64 ret) x22 (Z_to_bv 64 fr)
            (Z_to_bv 64 (fr / 8 + off)) (Z_to_bv 64 off) s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x86e14) fc None mc (seg_rom rsegs)).
  Lemma c6_HA1 : A mod 32 = 0 /\ bv_unsigned sp - 176 <= A <= bv_unsigned sp - 160.
  Proof. exact (HA1 sp A HA HS16). Qed.

  (* PERF (mbb-lanes-common.md): lia and Z.div_mod_to_equations never run with the Section's 30 hypotheses in
     scope; every arithmetic step below drops them first, and takes what it needs from a named hypothesis. *)
  Ltac c6_sc :=
    try clear Hrel; try clear HNF; try clear HDH; try clear HBD; try clear HMC; try clear HMS;
    try clear NDJ; try clear AJ2; try clear AJ1; try clear AO; try clear ANB; try clear AP;
    try clear HO; try clear HN; try clear HP; try clear TLS0; try clear FP0; try clear AW0;
    try clear SR0; try clear AC0; try clear MI0; try clear ST0; try clear HS16; try clear HA;
    try clear Hoff; try clear HSM.
  (* The arithmetic context for lia: the Section's hypotheses and every memory fact dropped, the linear facts
     kept. *)
  Ltac c6_ar :=
    c6_sc;
    repeat match goal with
    | H : forall _ : word -> option byte, _ |- _ => clear H
    | H : forall _ : word, _ |- _ => clear H
    | H : forall _ : Z, _ |- _ => clear H
    | H : forall _ : nat, _ |- _ => clear H
    | H : forall _ : list byte, _ |- _ => clear H
    | H : BI _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => clear H
    | H : rw_cells _ _ _ _ |- _ => clear H
    | H : ro_cells _ _ _ _ |- _ => clear H
    | H : bytes_at _ _ _ _ |- _ => clear H
    | H : stk _ _ _ _ |- _ => clear H
    | H : munch _ _ _ |- _ => clear H
    | H : wmono _ _ _ |- _ => clear H
    | H : rd_mono _ _ |- _ => clear H
    | H : addressable _ _ _ |- _ => clear H
    | H : asan_cells _ |- _ => clear H
    | H : shadow_rw _ |- _ => clear H
    | H : mem_inv _ _ |- _ => clear H
    | H : fp_dj _ _ |- _ => clear H
    | H : name_ok _ |- _ => clear H
    | H : ov_read_bytes _ _ _ _ = _ |- _ => clear H
    | H : store_ok _ _ _ _ = _ |- _ => clear H
    end.
  Ltac c6_lia := c6_ar; lia.
  (* lia case-splits on every disjunction in scope (2^k refutations, and a proof term of that size): the walk
     boxes its disjunctive facts and each arithmetic leaf opens only the ones it needs. *)
  Definition c6_box (P : Prop) : Prop := P.
  Ltac c6_hide H := let T := type of H in change (c6_box T) in H.
  Ltac c6_show H := unfold c6_box in H.

  (* The body's fine footprint lies inside the post's write set (sub_post of C_reac_box_model_blockRB_body.v, which
     this file does not import). *)
  Lemma c6_sub_post : forall fr f spc j n w56, FK FS A fr f spc j n w56 ->
    sub_fp (Wf sp FS fr j n ++ (if (p =? 0) || (o =? 0) then [] else [(o, o + 32)]))
           (reac_box_model_block_W o (bv_unsigned sp) ++ reac_box_model_block_X (bv_unsigned sp) FS).
  Proof.
    intros fr f spc j n w56 HK x Hout.
    pose proof c6_HA1 as HAb. pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
    c6_sc.
    assert (outapp : forall (W1 W2 : list ivl) y, outside (W1 ++ W2) y -> outside W1 y /\ outside W2 y).
    { induction W1 as [|[lo hi] W1 IH]; intros W2 y H; cbn [app outside] in *; [split; [exact I | exact H]|].
      destruct H as [H1 H2]. destruct (IH W2 y H2) as [H3 H4]. split; [split; [exact H1 | exact H3]|exact H4]. }
    assert (EH0 : fs_hint FS 0 = FS) by (unfold fs_hint; cbn [Z.of_nat]; lia).
    assert (EF0 : fs_flag FS 0 0 = FS + 4096) by (unfold fs_flag; cbn [Z.of_nat]; lia).
    assert (EFj : fs_flag FS 0 j = FS + 4096 + j) by (unfold fs_flag; cbn [Z.of_nat]; lia).
    assert (EM0 : fs_M 0 = 16384) by reflexivity.
    assert (EFR0 : fs_frame FS 0 0 = FS + 36864) by (unfold fs_frame, fs_B; cbn [Z.of_nat]; lia).
    assert (EFMf : fs_frame FS 0 (fs_M 0) = FS + 1085440).
    { unfold fs_frame, fs_B, fs_M.
      replace (2 ^ (14 - Z.of_nat 0) * (64 * 2 ^ Z.of_nat 0)) with 1048576 by reflexivity.
      replace (Z.of_nat 0 * 2 ^ 20) with 0 by reflexivity. lia. }
    destruct (outapp _ _ _ Hout) as (HoutW & HoutX).
    unfold reac_box_model_block_W, REAC_BOX_MODEL_BLOCK_K in HoutW. cbn [outside fst snd] in HoutW.
    destruct HoutW as (Hwin & HoutO).
    unfold reac_box_model_block_X, REAC_BOX_MODEL_BLOCK_K in HoutX.
    destruct (outapp _ _ _ HoutX) as (HoutFP & HoutWS).
    cbn [fp_w fp_w1 flat_map app outside fst snd] in HoutFP.
    rewrite EFR0, EFMf, EH0, EF0, EM0 in HoutFP.
    destruct HoutFP as (Hhint & Hflag & Hframe & HfrSh & _).
    cbn [outside fst snd] in HoutWS. destruct HoutWS as (HwinSh & _).
    clear Hout outapp.
    apply fl_out_app.
    - unfold Wf. cbn [outside fst snd].
      destruct HK as [(Ef & Efr & Espc & Ej & En) | (Hj & Efr & Ef & Espc & Ew & En)].
      + subst fr j n.
        assert (Esh : shadow_addr (A - 64) + 8 = shadow_addr A)
          by (unfold shadow_addr; Z.div_mod_to_equations; lia).
        assert (G1 : shadow_addr (bv_unsigned sp - 4272) <= shadow_addr (A - 64))
          by (apply acl_sh_ge; lia).
        assert (G2 : shadow_addr A <= shadow_addr (bv_unsigned sp)) by (apply acl_sh_ge; lia).
        split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|exact I].
      + subst fr n.
        change (fs_M 0) with 16384 in Hj.
        assert (Efrv : fs_frame FS 0 j = FS + 36864 + j * 64)
          by (unfold fs_frame, fs_B; cbn [Z.of_nat]; lia).
        assert (Esh : shadow_addr (fs_frame FS 0 j) + 8 = shadow_addr (fs_frame FS 0 j + 64))
          by (unfold shadow_addr; Z.div_mod_to_equations; lia).
        assert (G1 : shadow_addr (FS + 36864) <= shadow_addr (fs_frame FS 0 j))
          by (apply acl_sh_ge; lia).
        assert (G2 : shadow_addr (fs_frame FS 0 j + 64) <= shadow_addr (FS + 1085440))
          by (apply acl_sh_ge; lia).
        split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|exact I].
    - destruct ((p =? 0) || (o =? 0)) eqn:Epo; cbn [outside fst snd]; [exact I|].
      apply orb_false_iff in Epo. destruct Epo as (Ep & Eo).
      split; [|exact I]. rewrite Eo in HoutO. cbn [outside fst snd] in HoutO.
      destruct HoutO as (HoW & _). exact HoW.
  Qed.

  (* ---- the carried footprint ---- *)

  (* The body's fine footprint on the b = 5 / b = 6 path (p <> 0 and o <> 0): the window, the class-0 hint word,
     flag j, the frame and its shadow, and the output block. *)
  Definition c6_W (fr j n : Z) : list ivl := Wf sp FS fr j n ++ [(o, o + 32)].

  Lemma c6_Wu : p <> 0 -> o <> 0 -> forall fr j n,
    Wf sp FS fr j n ++ (if (p =? 0) || (o =? 0) then [] else [(o, o + 32)]) = c6_W fr j n.
  Proof.
    intros Hp0 Ho0 fr j n. unfold c6_W.
    replace ((p =? 0) || (o =? 0)) with false; [reflexivity|].
    symmetry. apply orb_false_iff. split; apply Z.eqb_neq; assumption.
  Qed.

  Lemma c6_Rsp : 0 <= bv_unsigned sp < 2^64.
  Proof. pose proof (zr_word sp) as H. unfold inr64 in H. exact H. Qed.

  (* The class-0 ranges of the side stack that a data range of the contract avoids (fp's D-disjointness). *)
  Lemma c6_dj4 : forall a L, fp_dj [(a, a + L)] (fp_w [0%nat] FS) ->
    (a + L <= FS \/ FS + 8 <= a) /\ (a + L <= FS + 4096 \/ FS + 4096 + 16384 <= a) /\
    (a + L <= fs_frame FS 0 0 \/ fs_frame FS 0 (fs_M 0) <= a).
  Proof.
    intros a L H. unfold fp_dj in H. apply Forall_cons_iff in H. destruct H as [H _]. cbn [fst snd] in H.
    unfold fp_w, fp_w1 in H. cbn [flat_map app] in H.
    apply Forall_cons_iff in H. destruct H as [H1 H].
    apply Forall_cons_iff in H. destruct H as [H2 H].
    apply Forall_cons_iff in H. destruct H as [H3 _].
    unfold ly_dj in H1, H2, H3. cbn [fst snd] in H1, H2, H3.
    c6_sc.
    assert (EH : fs_hint FS 0 = FS) by (unfold fs_hint; cbn [Z.of_nat]; lia).
    assert (EF : fs_flag FS 0 0 = FS + 4096) by (unfold fs_flag; cbn [Z.of_nat]; lia).
    assert (EM : fs_M 0 = 16384) by reflexivity.
    rewrite EH in H1. rewrite EF, EM in H2.
    split; [lia|]. split; [lia | exact H3].
  Qed.

  Lemma c6_dj_o : o <> 0 -> fp_dj [(o, o + 32)] (fp_w [0%nat] FS).
  Proof.
    intros Ho0. pose proof FP0 as (DT & TS & C & T & DB & k & _ & _ & _ & _ & _ & _ & _ & _ & _ & HDd).
    unfold fp_dj in *. rewrite Forall_forall in HDd. constructor; [|constructor].
    apply HDd. unfold reac_box_model_block_D. apply in_or_app. right.
    replace (o =? 0) with false by (symmetry; apply Z.eqb_neq; exact Ho0). left; reflexivity.
  Qed.

  Lemma c6_dj_p : p <> 0 -> fp_dj [(p, p + 296)] (fp_w [0%nat] FS).
  Proof.
    intros Hp0. pose proof FP0 as (DT & TS & C & T & DB & k & _ & _ & _ & _ & _ & _ & _ & _ & _ & HDd).
    unfold fp_dj in *. rewrite Forall_forall in HDd. constructor; [|constructor].
    apply HDd. unfold reac_box_model_block_D. apply in_or_app. left.
    replace (p =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hp0). left; reflexivity.
  Qed.

  (* A data range apart from the window and from the class-0 frames is apart from this frame. *)
  Lemma c6_fr_apart : forall fr f spc j n w56 a L, FK FS A fr f spc j n w56 ->
    (bv_unsigned sp <= a \/ a + L <= bv_unsigned sp - 4272) ->
    (a + L <= fs_frame FS 0 0 \/ fs_frame FS 0 (fs_M 0) <= a) ->
    forall i, 0 <= i < L -> ~ (fr <= a + i < fr + 64).
  Proof.
    intros fr f spc j n w56 a L HK Hw Hfs i Hi.
    pose proof c6_HA1 as (HA32 & HAlo & HAhi).
    c6_sc.
    assert (EFR0 : fs_frame FS 0 0 = FS + 36864) by (unfold fs_frame, fs_B; cbn [Z.of_nat]; lia).
    assert (EFM : fs_frame FS 0 (fs_M 0) = FS + 1085440).
    { unfold fs_frame, fs_B, fs_M.
      replace (2 ^ (14 - Z.of_nat 0) * (64 * 2 ^ Z.of_nat 0)) with 1048576 by reflexivity.
      replace (Z.of_nat 0 * 2 ^ 20) with 0 by reflexivity. lia. }
    destruct HK as [(Ef & Efr & Espc & Ej & En) | (Hj & Efr & Ef & Espc & Ew & En)]; subst fr.
    - lia.
    - change (fs_M 0) with 16384 in Hj.
      assert (Efrv : fs_frame FS 0 j = FS + 36864 + j * 64) by (unfold fs_frame, fs_B; cbn [Z.of_nat]; lia).
      lia.
  Qed.

  (* The shadow byte of an application address outside the frame is outside the fine footprint: every other range
     of the footprint is application memory, and the shadow of an application address is not. *)
  Lemma c6_shout : o <> 0 -> forall fr f spc j n w56 a, FK FS A fr f spc j n w56 -> app_mem a ->
    ~ (fr <= a < fr + 64) -> outside (c6_W fr j n) (shadow_addr a).
  Proof.
    intros Ho0 fr f spc j n w56 a HK Hap Hfr.
    pose proof (rt_app_shadow a Hap) as Hsh.
    destruct (fk_facts sp tp m p o FS off A Hoff HA HS16 ST0 SR0 HHM HAE AW0 FP0 fr f spc j n w56 HK)
      as (FR8 & FRlo & FRhi & _ & _ & FAP & _ & _ & _ & _).
    pose proof FP0 as (DT & TS & C & T & DB & k & _ & _ & (_ & _ & _ & P4 & _) & _ & _ & _ & HFS & HAPP & _).
    destruct (AO Ho0) as (AOa & _ & _).
    assert (Oapp : forall i, 0 <= i < 32 -> app_mem (o + i))
      by (intros i Hi; exact (acl_app_in m o 32 i AOa Hi)).
    assert (G : forall lo hi, (forall y, lo <= y < hi -> app_mem y) -> ~ (lo <= shadow_addr a < hi))
      by (intros lo hi Hall Hin; exact (acl_app_not_shadow _ (Hall _ Hin) Hsh)).
    assert (Hjn : 0 <= j /\ j < 16384 /\ (n = 0 \/ n = 1)).
    { destruct HK as [(_ & _ & _ & Ej & En) | (Hj & _ & _ & _ & _ & En)];
        [clear -Ej En; lia | change (fs_M 0) with 16384 in Hj; clear -Hj En; lia]. }
    unfold FS_SIZE in P4.
    clear HK AOa Hsh Hap.
    c6_sc.
    assert (EFj : fs_flag FS 0 j = FS + 4096 + j) by (unfold fs_flag; cbn [Z.of_nat]; lia).
    unfold c6_W, Wf. cbn [app outside fst snd].
    split; [apply G; intros y Hy; apply HAPP; lia|].
    split; [apply G; intros y Hy; apply P4; lia|].
    split; [apply G; intros y Hy; apply P4; lia|].
    split; [apply G; intros y Hy; replace y with (fr + (y - fr)) by lia; apply FAP; lia|].
    split.
    - intros [H1 H2]. apply Hfr. apply (proj1 (sh_range8 fr a FR8)). split; [exact H1 | lia].
    - split; [|exact I]. apply G. intros y Hy. replace y with (o + (y - o)) by lia. apply Oapp. lia.
  Qed.

  (* A range of m that the walk has not written stays addressable. *)
  Lemma c6_addr_keep : o <> 0 -> forall fr f spc j n w56 mc a L, FK FS A fr f spc j n w56 ->
    munch (c6_W fr j n) m mc -> addressable m a L ->
    (forall i, 0 <= i < L -> ~ (fr <= a + i < fr + 64)) -> addressable mc a L.
  Proof.
    intros Ho0 fr f spc j n w56 mc a L HK MU HAd Hfr.
    apply (addr_munch (c6_W fr j n) m mc a L HAd MU). intros i Hi.
    exact (c6_shout Ho0 fr f spc j n w56 (a + i) HK (acl_app_in m a L i HAd Hi) (Hfr i Hi)).
  Qed.

  (* The shadow byte that the instrumented check of w bytes at X reads, with this build's offset register. *)
  Lemma c6_chk : forall mc q L j w X, addressable mc q L -> 0 <= j -> 1 <= w -> j + w <= L ->
    X mod 8 + w <= 8 -> X = q + j ->
    exists k : byte, ov_read_bytes rsegs mc (wa (X / 8 + off)) 1 = Some [k]
      /\ (bv_signed k = 0 \/ X mod 8 + (w - 1) < bv_signed k) /\ -128 <= bv_signed k < 128.
  Proof.
    intros mc q L j w X H1 H2 H3 H4 H5 H6. rewrite Hoff.
    exact (acl_shadow mc q L j w X H1 H2 H3 H4 H5 H6).
  Qed.

  (* BI survives a callee whose writes lie inside the fine footprint and spare the saved registers, the hint word
     and the frame's flag-address word. *)
  Lemma c6_bi_call : forall fr j n w56 mc mc' (W' : list ivl),
    BI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m FS (c6_W fr j n) fr w56 mc ->
    munch W' mc mc' -> wmono rsegs mc mc' -> rd_mono mc mc' -> mem_inv rsegs mc' ->
    sub_fp W' (c6_W fr j n) ->
    disjoint_from W' (bv_unsigned sp + -88) 88 -> disjoint_from W' FS 8 ->
    disjoint_from W' (fr + 56) 8 ->
    BI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m FS (c6_W fr j n) fr w56 mc'.
  Proof.
    intros fr j n w56 mc mc' W' HB MU WM RM MI HS D1 D2 D3.
    destruct HB as (MU0 & WM0 & RM0 & _ & SV & (hh & HH) & F56).
    split; [eapply munch_trans; [exact MU0 | eapply munch_weaken; [exact HS | exact MU]]|].
    split; [eapply wmono_trans; [exact WM0 | exact WM]|].
    split; [eapply rd_mono_trans; [exact RM0 | exact RM]|].
    split; [exact MI|].
    split.
    { eapply rw_cells_transport; [exact SV | exact MU | exact WM |].
      match goal with |- disjoint_from _ _ ?z => replace z with 88 by reflexivity end. exact D1. }
    split.
    - exists hh. eapply bytes_at_transport; [exact HH | exact MU |].
      match goal with |- disjoint_from _ _ ?z => replace z with 8 by reflexivity end. exact D2.
    - eapply bytes_at_transport; [exact F56 | exact MU |].
      match goal with |- disjoint_from _ _ ?z => replace z with 8 by reflexivity end. exact D3.
  Qed.

  (* The runtime state at a carried memory: asan_cells, the run's shadow region (route (C): SR0's region,
     carried to mc; each callee site narrows it to the callee's region) and the window's bytes. *)
  Lemma c6_rt : forall fr f spc j n w56 mc, FK FS A fr f spc j n w56 -> p <> 0 -> o <> 0 ->
    BI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m FS (c6_W fr j n) fr w56 mc ->
    asan_cells mc /\ shadow_rw_on (reac_box_model_block_shadow_R (bv_unsigned sp) FS p b o row nb) mc /\
    stk rsegs mc (bv_unsigned sp - 4272) (bv_unsigned sp).
  Proof.
    intros fr f spc j n w56 mc HK Hp0 Ho0 HB.
    destruct HB as (MU & WM & RM & MI & _ & _ & _).
    assert (HSsub : sub_fp (c6_W fr j n)
      (reac_box_model_block_W o (bv_unsigned sp) ++ reac_box_model_block_X (bv_unsigned sp) FS)).
    { rewrite <- (c6_Wu Hp0 Ho0 fr j n).
      exact (c6_sub_post fr f spc j n w56 HK). }
    split; [exact (br_ac sp tp m p b o FS row nb ob AC0 HHM HAE FP0 Rp Rb Ro HP HO AO _ mc MU HSsub)|].
    split; [exact (mbHB_carry _ m mc SR0 WM RM) | exact (stk_mono m mc _ _ ST0 WM RM)].
  Qed.

  (* ---- the geometry the callee contracts and the checks need ---- *)

  Lemma c6_geoA : forall fr f spc j n w56, FK FS A fr f spc j n w56 ->
    0 <= bv_unsigned sp < 2^64 /\ A mod 32 = 0 /\ bv_unsigned sp - 176 <= A /\ A <= bv_unsigned sp - 160 /\
    fr mod 8 = 0 /\ FS + 36864 <= fr /\ fr + 64 <= A /\ (spc = A \/ spc = fr) /\
    0 < FS /\ FS + 11571200 <= bv_unsigned sp - 4272 /\
    17594333495296 <= bv_unsigned sp - 4272 /\ bv_unsigned sp <= 140737488355328.
  Proof.
    intros fr f spc j n w56 HK.
    destruct (fk_facts sp tp m p o FS off A Hoff HA HS16 ST0 SR0 HHM HAE AW0 FP0 fr f spc j n w56 HK)
      as (FR8 & FRlo & FRhi & Fsp & _ & _ & _ & _ & _ & _).
    pose proof c6_HA1 as (HA32 & HAlo & HAhi). pose proof c6_Rsp as Rsp.
    pose proof FP0 as (DT & TS & C & T & DB & k & _ & _ & (P1 & _) & _ & _ & _ & HFS & _).
    pose proof HHM as H1. pose proof HAE as H2.
    unfold HIGHMEM_BEG in H1. unfold APPMEM_END in H2. unfold FS_SIZE in HFS.
    clear HK. c6_sc.
    split; [exact Rsp|]. split; [exact HA32|]. split; [lia|]. split; [lia|].
    split; [exact FR8|]. split; [exact FRlo|]. split; [exact FRhi|]. split; [exact Fsp|].
    split; [lia|]. split; [lia|]. split; lia.
  Qed.

  Lemma c6_geoP : p <> 0 ->
    p mod 8 = 0 /\ length row = 296%nat /\ p + 296 <= 140737488355328 /\
    (bv_unsigned sp <= p \/ p + 296 <= bv_unsigned sp - 4272) /\ (o = 0 \/ o + 32 <= p \/ p + 296 <= o) /\
    (forall i, 0 <= i < 296 -> app_mem (p + i)).
  Proof.
    intros Hp0. destruct (HP Hp0) as (Hp8 & Hrow & _ & Dps & Dpo).
    pose proof (AP Hp0) as APa. pose proof APa as (_ & _ & He & _). unfold APPMEM_END in He.
    split; [exact Hp8|]. split; [exact Hrow|]. split; [exact He|]. split; [exact Dps|].
    split; [exact Dpo|]. intros i Hi. exact (acl_app_in m p 296 i APa Hi).
  Qed.

  Lemma c6_geoO : o <> 0 ->
    o + 32 <= 140737488355328 /\ (bv_unsigned sp <= o \/ o + 32 <= bv_unsigned sp - 4272) /\
    (o + 32 <= RT_LO \/ RT_HI <= o) /\ app_mem (o + 32) /\
    (forall i, 0 <= i < 32 -> app_mem (o + i)) /\
    (o + 32 <= FS \/ FS + 8 <= o) /\ (o + 32 <= fs_frame FS 0 0 \/ fs_frame FS 0 (fs_M 0) <= o).
  Proof.
    intros Ho0. destruct (AO Ho0) as (AOa & Hoapp & Drt). destruct (HO Ho0) as (_ & Dos & _).
    pose proof AOa as (_ & _ & He & _). unfold APPMEM_END in He.
    destruct (c6_dj4 o 32 (c6_dj_o Ho0)) as (D1 & _ & D3).
    split; [exact He|]. split; [exact Dos|]. split; [exact Drt|]. split; [exact Hoapp|].
    split; [intros i Hi; exact (acl_app_in m o 32 i AOa Hi)|].
    split; [exact D1 | exact D3].
  Qed.

  (* The frame's place: the side frame is in the class-0 frames, the real frame is the 64 bytes under A. *)
  Lemma c6_frpos : forall fr f spc j n w56, FK FS A fr f spc j n w56 ->
    (spc = A /\ FS + 36864 <= fr /\ fr + 64 <= FS + 1085440) \/ (spc = A - 64 /\ fr = A - 64).
  Proof.
    intros fr f spc j n w56 HK.
    destruct (c6_geoA fr f spc j n w56 HK)
      as (Rsp & HA32 & HAlo & HAhi & FR8 & FRlo & FRhi & Fsp & FSpos & FSsz & HM1 & HM2).
    destruct HK as [(Ef & Efr & Espc & Ej & En) | (Hj & Efr & Ef & Espc & Ew & En)].
    - right. c6_sc. split; lia.
    - left. change (fs_M 0) with 16384 in Hj.
      assert (Efrv : fs_frame FS 0 j = FS + 36864 + j * 64)
        by (c6_sc; unfold fs_frame, fs_B; cbn [Z.of_nat]; lia).
      c6_sc. split; [lia|]. split; [lia|]. rewrite Efr, Efrv. lia.
  Qed.

  Lemma c6_o_fr_iv : o <> 0 -> forall fr f spc j n w56, FK FS A fr f spc j n w56 ->
    o + 32 <= fr \/ fr + 64 <= o.
  Proof.
    intros Ho0 fr f spc j n w56 HK.
    destruct (c6_geoO Ho0) as (HoA & Dos & _ & _ & _ & _ & D3).
    destruct (c6_geoA fr f spc j n w56 HK)
      as (Rsp & HA32 & HAlo & HAhi & FR8 & FRlo & FRhi & Fsp & FSpos & FSsz & HM1 & HM2).
    pose proof (c6_frpos fr f spc j n w56 HK) as FKp.
    clear HK. c6_sc.
    assert (EF0 : fs_frame FS 0 0 = FS + 36864) by (unfold fs_frame, fs_B; cbn [Z.of_nat]; lia).
    assert (EFM : fs_frame FS 0 (fs_M 0) = FS + 1085440).
    { unfold fs_frame, fs_B, fs_M.
      replace (2 ^ (14 - Z.of_nat 0) * (64 * 2 ^ Z.of_nat 0)) with 1048576 by reflexivity.
      replace (Z.of_nat 0 * 2 ^ 20) with 0 by reflexivity. lia. }
    rewrite EF0, EFM in D3. destruct FKp as [(Es & F1 & F2) | (Es & Efr)]; lia.
  Qed.

  Lemma c6_o_fr : o <> 0 -> forall fr f spc j n w56, FK FS A fr f spc j n w56 ->
    forall i, 0 <= i < 32 -> ~ (fr <= o + i < fr + 64).
  Proof.
    intros Ho0 fr f spc j n w56 HK i Hi.
    pose proof (c6_o_fr_iv Ho0 fr f spc j n w56 HK) as H. clear HK. c6_sc. lia.
  Qed.

  (* A data range apart from the window, from the class-0 side stack and from o lies outside the fine footprint. *)
  Lemma c6_out_data : o <> 0 -> forall fr f spc j n w56 a L x, FK FS A fr f spc j n w56 ->
    fp_dj [(a, a + L)] (fp_w [0%nat] FS) ->
    (bv_unsigned sp <= a \/ a + L <= bv_unsigned sp - 4272) -> (o + 32 <= a \/ a + L <= o) ->
    (forall i, 0 <= i < L -> app_mem (a + i)) -> a <= x < a + L -> outside (c6_W fr j n) x.
  Proof.
    intros Ho0 fr f spc j n w56 a L x HK Hdj Dw Do Hap Hx.
    destruct (c6_dj4 a L Hdj) as (D1 & D2 & D3).
    destruct (c6_geoA fr f spc j n w56 HK)
      as (Rsp & HA32 & HAlo & HAhi & FR8 & FRlo & FRhi & Fsp & FSpos & FSsz & HM1 & HM2).
    assert (Hapx : app_mem x) by (replace x with (a + (x - a)) by (clear -Hx; lia); apply Hap; clear -Hx; lia).
    assert (Hjn : 0 <= j /\ j < 16384 /\ (n = 0 \/ n = 1)).
    { destruct HK as [(_ & _ & _ & Ej & En) | (Hj & _ & _ & _ & _ & En)];
        [clear -Ej En; lia | change (fs_M 0) with 16384 in Hj; clear -Hj En; lia]. }
    assert (Hfr : ~ (fr <= x < fr + 64)).
    { replace x with (a + (x - a)) by (clear -Hx; lia).
      exact (c6_fr_apart fr f spc j n w56 a L HK Dw D3 (x - a) ltac:(clear -Hx; lia)). }
    clear HK Hap Hdj D3.
    c6_sc.
    assert (EFj : fs_flag FS 0 j = FS + 4096 + j) by (unfold fs_flag; cbn [Z.of_nat]; lia).
    assert (Hsh : ~ (shadow_addr fr <= x < shadow_addr fr + 8)).
    { replace (shadow_addr fr + 8) with (shadow_addr (fr + 64))
        by (unfold shadow_addr; Z.div_mod_to_equations; lia).
      apply (acl_sh_out x fr (fr + 64) Hapx); [lia | unfold APPMEM_END; lia]. }
    unfold c6_W, Wf. cbn [app outside fst snd].
    split; [lia|]. split; [lia|]. split; [rewrite EFj; lia|].
    split; [exact Hfr|]. split; [exact Hsh|]. split; [lia | exact I].
  Qed.

  Lemma c6_out_p : p <> 0 -> o <> 0 -> forall fr f spc j n w56 x, FK FS A fr f spc j n w56 ->
    p <= x < p + 296 -> outside (c6_W fr j n) x.
  Proof.
    intros Hp0 Ho0 fr f spc j n w56 x HK Hx.
    destruct (c6_geoP Hp0) as (_ & _ & _ & Dps & Dpo & Papp).
    exact (c6_out_data Ho0 fr f spc j n w56 p 296 x HK (c6_dj_p Hp0) Dps
             ltac:(clear -Dpo Ho0; destruct Dpo as [E|E]; [exfalso; exact (Ho0 E) | lia]) Papp Hx).
  Qed.

  Lemma c6_out_nm : p <> 0 -> o <> 0 -> (b = 5 \/ b = 6) -> has row <> 0 -> rname row <> 0 ->
    forall fr f spc j n w56 x, FK FS A fr f spc j n w56 ->
    rname row <= x < rname row + Z.of_nat (length nb) -> outside (c6_W fr j n) x.
  Proof.
    intros Hp0 Ho0 B56 Hh Hnm fr f spc j n w56 x HK Hx.
    destruct (HN Hp0 B56 Hh Hnm) as (_ & _ & Dns & Dno).
    pose proof (ANB Hp0 B56 Hh Hnm) as ANa.
    exact (c6_out_data Ho0 fr f spc j n w56 (rname row) (Z.of_nat (length nb)) x HK
             (NDJ Hp0 B56 Hh Hnm) Dns
             ltac:(clear -Dno Ho0; destruct Dno as [E|E]; [exfalso; exact (Ho0 E) | lia])
             ltac:(intros i Hi; exact (acl_app_in m (rname row) (Z.of_nat (length nb)) i ANa Hi)) Hx).
  Qed.

  (* The window's scratch buffer [A + 35, A + 72) is apart from the frame and addressable at m. *)
  Lemma c6_buf_fr : forall fr f spc j n w56, FK FS A fr f spc j n w56 ->
    forall i, 0 <= i < 37 -> ~ (fr <= A + 35 + i < fr + 64).
  Proof.
    intros fr f spc j n w56 HK i Hi.
    destruct (c6_geoA fr f spc j n w56 HK)
      as (Rsp & HA32 & HAlo & HAhi & FR8 & FRlo & FRhi & Fsp & FSpos & FSsz & HM1 & HM2).
    clear - Hi FRhi. lia.
  Qed.

  Lemma c6_buf_addr : addressable m (A + 35) 37.
  Proof.
    pose proof c6_HA1 as (HA32 & HAlo & HAhi). pose proof c6_Rsp as Rsp.
    pose proof HHM as H1. unfold HIGHMEM_BEG in H1.
    exact (acl_addr_sub m (bv_unsigned sp - 4272) 4272 (A + 35) 37 AW0
             ltac:(clear -HAlo HAhi H1; lia) ltac:(lia) ltac:(clear -HAlo HAhi H1; lia)).
  Qed.

  Lemma c6_addr_o : o <> 0 -> forall fr f spc j n w56 mc, FK FS A fr f spc j n w56 ->
    munch (c6_W fr j n) m mc -> addressable mc o 32.
  Proof.
    intros Ho0 fr f spc j n w56 mc HK MU.
    exact (c6_addr_keep Ho0 fr f spc j n w56 mc o 32 HK MU (proj1 (AO Ho0))
             (c6_o_fr Ho0 fr f spc j n w56 HK)).
  Qed.

  Lemma c6_addr_buf : o <> 0 -> forall fr f spc j n w56 mc, FK FS A fr f spc j n w56 ->
    munch (c6_W fr j n) m mc -> addressable mc (A + 35) 37.
  Proof.
    intros Ho0 fr f spc j n w56 mc HK MU.
    exact (c6_addr_keep Ho0 fr f spc j n w56 mc (A + 35) 37 HK MU c6_buf_addr
             (c6_buf_fr fr f spc j n w56 HK)).
  Qed.

  Lemma c6_addr_p : p <> 0 -> o <> 0 -> forall fr f spc j n w56 mc, FK FS A fr f spc j n w56 ->
    munch (c6_W fr j n) m mc -> addressable mc p 296.
  Proof.
    intros Hp0 Ho0 fr f spc j n w56 mc HK MU.
    destruct (c6_geoP Hp0) as (_ & _ & _ & Dps & _ & _).
    destruct (c6_dj4 p 296 (c6_dj_p Hp0)) as (_ & _ & DF).
    exact (c6_addr_keep Ho0 fr f spc j n w56 mc p 296 HK MU (AP Hp0)
             (c6_fr_apart fr f spc j n w56 p 296 HK Dps DF)).
  Qed.

  Lemma c6_app_win : forall x, bv_unsigned sp - 4272 <= x < bv_unsigned sp -> app_mem x.
  Proof.
    intros x Hx.
    pose proof FP0 as (DT & TS & C & T & DB & k & _ & _ & _ & _ & _ & _ & _ & HAPP & _).
    apply HAPP. exact Hx.
  Qed.

  (* The row bytes at a carried memory. *)
  Lemma c6_rowb : p <> 0 -> o <> 0 -> forall fr f spc j n w56 mc, FK FS A fr f spc j n w56 ->
    munch (c6_W fr j n) m mc -> bytes_at rsegs mc p row.
  Proof.
    intros Hp0 Ho0 fr f spc j n w56 mc HK MU.
    destruct (HP Hp0) as (_ & Hrow & HRB0 & _ & _).
    eapply fl_bytes; [exact HRB0 | exact MU|]. intros x Hx. rewrite Hrow in Hx.
    exact (c6_out_p Hp0 Ho0 fr f spc j n w56 x HK ltac:(clear -Hx; cbn [Z.of_nat] in Hx; lia)).
  Qed.

  (* ---- the callee steps ---- *)

  Lemma c6_p64 : 140737488355328 < 2^64.
  Proof. vm_compute. reflexivity. Qed.

  (* ---- the case56 lemmas with this Section's variables and hypotheses supplied once ----
     The walk clears the Section hypotheses before every arithmetic leaf (PERF), so the lemmas of
     C_reac_box_model_blockRB_case56.v (which take them as arguments outside their own Section) are wrapped
     here, where the hypotheses are still in scope. *)


  (* 0x86d18: the inner byte sum over the window record [A + 35, A + 56) of build_ident_last.  The record is
     in the function's own window, so its loads carry no shadow check (port of the ubsan twin's loopr,
     U line 735). *)

  (* 0x86b24: name_field into the window's buffer at A + 56, the five header bytes of the record at A + 35,
     the record's copy of the name at A + 40, nine checked header bytes into the output block, the six name
     bytes at o + 9, then the record sum, the pre-tail, the outer sum and the release. *)
End c6_S.
(* route (C), HB: SR0 (the region form) names b row nb, so each lemma below, which uses SR0 through
   fk_facts or the carried region, takes them; row and nb are implicit (inferred from SR0), so the
   F twin's calls keep their argument lists. *)
Arguments c6_geoA sp tp m p b o FS off A {row nb}.
Arguments c6_frpos sp tp m p b o FS off A {row nb}.
Arguments c6_o_fr_iv sp tp m p b o FS off A {row nb} ob.
Arguments c6_rowb sp tp m p b o FS off A row {nb}.
Arguments c6_addr_p sp tp m p b o FS off A row {nb}.
Arguments c6_addr_o sp tp m p b o FS off A {row nb} ob.
