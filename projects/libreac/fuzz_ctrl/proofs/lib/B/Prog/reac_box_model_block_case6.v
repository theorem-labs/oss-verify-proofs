(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 922 of its 952 lines of code are new or changed and 218 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcRec RcRecLib RcBox RcBoxLib
  RcSynth RcSynthLib RcParseLib RcKindLib RcLay RcAsan RcAsanLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import RcAsanRT RcAsanFP RcAsanFPLib
  asan_stack_malloc_c asan_memset_c asan_memcpy_c build_dt1_single_c dt1_head_c name_field_c reac_box_model_block_c
  reac_box_model_block reac_box_model_block_case56.
Import ListNotations.
Open Scope Z_scope.

(* Local copy of reac_box_model_block.v:215's store hook: that file made it Local (a Theorem Labs lane, approved by a Theorem Labs lane, 2026-10-30). *)
Local Ltac footprint_after_store segs m a bs ::=
  repeat match goal with
  | MU : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_write Wq mq m a bs) in MU; [ | lia | simpl_sizes; slia | cbn [inside]; simpl_sizes; slia ]
            | fail 100 "store outside the declared footprint:" a ]
  | WMo : wmono segs ?mq m |- _ => apply (wmono_write segs mq m (wa a) bs) in WMo
  | RMo : rd_mono ?mq m |- _ => apply (rd_mono_write mq m (wa a) bs) in RMo
  | STq : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_write segs m loq hiq a bs) in STq; [ | lia | simpl_sizes; slia ]
            | fail 100 "cannot transport stk hypothesis" STq ]
  end.

(* reac_box_model_block, image B (asan-ubsan): the case b = 6 of the jump table at 0x86710 (0x86b24,
   name_field + build_ident_last), from its case PC to the frame release at 0x86e14, where the release
   continuation Hrel (the rel_stmt of the interface pin) takes over.  The ubsan twin is
   lib/U/Prog/reac_box_model_block.v (case6, loopr, tail6); here the frame is the ASan frame (FK/BI of
   reac_box_model_block.v), the record of build_ident_last is the 21 bytes at A + 35 of the window, and each
   load or store of o and of p has the shadow check before it.  The callee steps, the output block's check
   byte and the outer sum loop come from reac_box_model_block_case56.v; the Section hypotheses they were
   proved under are supplied once by the c6_call_* / c6_loop6 wrappers below, because the walk clears those
   hypotheses (PERF). *)

(* The byte stores of this case write a register value, so the cell of a 1-byte store is read off le1 (as in
   the ubsan twin lib/U/Prog/reac_box_model_block.v). *)
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
  Hypothesis HSM : asan_stack_malloc_0_contract.
  Hypothesis Hoff : off = ASAN_K.
  Hypothesis HA : A = (bv_unsigned sp - 160) / 32 * 32.
  Hypothesis HS16 : bv_unsigned sp mod 16 = 0.
  Hypothesis ST0 : stk rsegs m (bv_unsigned sp - 4272) (bv_unsigned sp).
  Hypothesis MI0 : mem_inv rsegs m.
  Hypothesis AC0 : asan_cells m.
  Hypothesis SR0 : shadow_rw m.
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

  Hypothesis HMS : asan_memset_contract.
  Hypothesis HMC : asan_memcpy_contract.
  Hypothesis HBD : build_dt1_single_contract.
  Hypothesis HDH : dt1_head_contract.
  Hypothesis HNF : name_field_contract.

  (* The release continuation at 0x86e14 (rel_stmt of mbb-interface-pin.md, verbatim). *)
  Hypothesis Hrel : forall (fr f spc j n : Z) (w56 : word) (mc : word -> option byte) (ret : Z)
       (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 : word),
  FK FS A fr f spc j n w56 ->
  ret = (if (p =? 0) || (o =? 0) then -1 else rc row b) ->
  BI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m FS
     (Wf sp FS fr j n ++ (if (p =? 0) || (o =? 0) then [] else [(o, o + 32)])) fr w56 mc ->
  (if (p =? 0) || (o =? 0) then True else bytes_at rsegs mc o (synth row b nb)) ->
  evt rsegs (Q0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb)
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

  (* The body's fine footprint lies inside the post's write set (sub_post of reac_box_model_block_body.v, which
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

  (* The runtime state at a carried memory: asan_cells, shadow_rw and the window's bytes. *)
  Lemma c6_rt : forall fr f spc j n w56 mc, FK FS A fr f spc j n w56 -> p <> 0 -> o <> 0 ->
    BI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m FS (c6_W fr j n) fr w56 mc ->
    asan_cells mc /\ shadow_rw mc /\ stk rsegs mc (bv_unsigned sp - 4272) (bv_unsigned sp).
  Proof.
    intros fr f spc j n w56 mc HK Hp0 Ho0 HB.
    destruct HB as (MU & WM & RM & MI & _ & _ & _).
    assert (HSsub : sub_fp (c6_W fr j n)
      (reac_box_model_block_W o (bv_unsigned sp) ++ reac_box_model_block_X (bv_unsigned sp) FS)).
    { rewrite <- (c6_Wu Hp0 Ho0 fr j n).
      exact (c6_sub_post fr f spc j n w56 HK). }
    split; [exact (br_ac sp tp m p b o FS row nb ob AC0 HHM HAE FP0 Rp Rb Ro HP HO AO _ mc MU HSsub)|].
    split; [exact (shadow_rw_mono m mc SR0 WM RM) | exact (stk_mono m mc _ _ ST0 WM RM)].
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
     reac_box_model_block_case56.v (which take them as arguments outside their own Section) are wrapped
     here, where the hypotheses are still in scope. *)

  Lemma c6_call_nf : forall (k ret fr f spc j n : Z) (w56 : word) (mc : word -> option byte) (WB OB : list byte)
      (x5 x6 x7 x12 x13 x14 x15 x16 x17 x21 x22 x28 x29 x30 x31 : word),
    p <> 0 -> o <> 0 -> (b = 5 \/ b = 6) -> has row <> 0 ->
    ret_pc (Z_to_bv 64 ret) = Z_to_bv 64 ret -> 35 <= k -> k + 16 <= 72 ->
    FK FS A fr f spc j n w56 ->
    BI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m FS (c6_W fr j n) fr w56 mc ->
    rw_cells rsegs mc (A + 35) [CB 37 WB] -> rw_cells rsegs mc o [CB 32 OB] ->
    (forall (mc' : word -> option byte) (y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
       BI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m FS (c6_W fr j n) fr w56 mc' ->
       rw_cells rsegs mc' (A + 35) [CB 37 (upd_bytes WB (Z.to_nat (k - 35)) (nmr row nb))] ->
       rw_cells rsegs mc' o [CB 32 OB] ->
       bytes_at rsegs mc' (A + k) (nmr row nb) -> length (nmr row nb) = 16%nat ->
       evt rsegs (Q0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb)
         (MS (mkR (Z_to_bv 64 ret) (Z_to_bv 64 spc) gp tp y5 y6 y7 sp (Z_to_bv 64 A)
                  y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 f) (Z_to_bv 64 o) (Z_to_bv 64 p) x21 x22
                  (Z_to_bv 64 fr) (Z_to_bv 64 (fr / 8 + off)) (Z_to_bv 64 off) s10 s11 y28 y29 y30 y31)
             F (Z_to_bv 64 ret) fc None mc' (seg_rom rsegs))) ->
    evt rsegs (Q0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb)
      (MS (mkR (Z_to_bv 64 ret) (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 A)
               (Z_to_bv 64 p) (Z_to_bv 64 (A + k)) x12 x13 x14 x15 x16 x17 (Z_to_bv 64 f) (Z_to_bv 64 o)
               (Z_to_bv 64 p) x21 x22 (Z_to_bv 64 fr) (Z_to_bv 64 (fr / 8 + off)) (Z_to_bv 64 off) s10 s11
               x28 x29 x30 x31)
          F (Z_to_bv 64 NAME_FIELD) fc None mc (seg_rom rsegs)).
  Proof. intros. eapply c56_call_nf; eassumption. Qed.

  Lemma c6_call_mco : forall (kd ks N ret fr f spc j n : Z) (w56 : word) (mc : word -> option byte)
      (WB OB : list byte) (x5 x6 x7 x13 x14 x15 x16 x17 x21 x22 x28 x29 x30 x31 : word),
    p <> 0 -> o <> 0 -> ret_pc (Z_to_bv 64 ret) = Z_to_bv 64 ret ->
    0 <= kd -> kd + 8 <= 32 -> kd + N <= 32 -> 35 <= ks -> ks + N <= 72 -> 0 <= N ->
    FK FS A fr f spc j n w56 ->
    BI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m FS (c6_W fr j n) fr w56 mc ->
    rw_cells rsegs mc (A + 35) [CB 37 WB] -> rw_cells rsegs mc o [CB 32 OB] ->
    (forall (mc' : word -> option byte) (y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
       BI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m FS (c6_W fr j n) fr w56 mc' ->
       rw_cells rsegs mc' (A + 35) [CB 37 WB] ->
       rw_cells rsegs mc' o
         [CB 32 (upd_bytes OB (Z.to_nat kd) (firstn (Z.to_nat N) (skipn (Z.to_nat (ks - 35)) WB)))] ->
       evt rsegs (Q0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb)
         (MS (mkR (Z_to_bv 64 ret) (Z_to_bv 64 spc) gp tp y5 y6 y7 sp (Z_to_bv 64 A)
                  (Z_to_bv 64 (o + kd)) y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 f) (Z_to_bv 64 o)
                  (Z_to_bv 64 p) x21 x22 (Z_to_bv 64 fr) (Z_to_bv 64 (fr / 8 + off)) (Z_to_bv 64 off) s10 s11
                  y28 y29 y30 y31)
             F (Z_to_bv 64 ret) fc None mc' (seg_rom rsegs))) ->
    evt rsegs (Q0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb)
      (MS (mkR (Z_to_bv 64 ret) (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 A)
               (Z_to_bv 64 (o + kd)) (Z_to_bv 64 (A + ks)) (Z_to_bv 64 N) x13 x14 x15 x16 x17
               (Z_to_bv 64 f) (Z_to_bv 64 o) (Z_to_bv 64 p) x21 x22 (Z_to_bv 64 fr)
               (Z_to_bv 64 (fr / 8 + off)) (Z_to_bv 64 off) s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 ASAN_MEMCPY) fc None mc (seg_rom rsegs)).
  Proof. intros. eapply c56_call_mco; eassumption. Qed.

  Lemma c6_call_mcf : forall (kd ks N ret fr f spc j n : Z) (w56 : word) (mc : word -> option byte)
      (WB OB : list byte) (x5 x6 x7 x13 x14 x15 x16 x17 x21 x22 x28 x29 x30 x31 : word),
    p <> 0 -> o <> 0 -> ret_pc (Z_to_bv 64 ret) = Z_to_bv 64 ret ->
    35 <= kd -> kd + N <= ks -> ks + N <= 72 -> 0 <= N ->
    FK FS A fr f spc j n w56 ->
    BI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m FS (c6_W fr j n) fr w56 mc ->
    rw_cells rsegs mc (A + 35) [CB 37 WB] -> rw_cells rsegs mc o [CB 32 OB] ->
    (forall (mc' : word -> option byte) (y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
       BI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m FS (c6_W fr j n) fr w56 mc' ->
       rw_cells rsegs mc' (A + 35)
         [CB 37 (upd_bytes WB (Z.to_nat (kd - 35)) (firstn (Z.to_nat N) (skipn (Z.to_nat (ks - 35)) WB)))] ->
       rw_cells rsegs mc' o [CB 32 OB] ->
       evt rsegs (Q0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb)
         (MS (mkR (Z_to_bv 64 ret) (Z_to_bv 64 spc) gp tp y5 y6 y7 sp (Z_to_bv 64 A)
                  (Z_to_bv 64 (A + kd)) y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 f) (Z_to_bv 64 o)
                  (Z_to_bv 64 p) x21 x22 (Z_to_bv 64 fr) (Z_to_bv 64 (fr / 8 + off)) (Z_to_bv 64 off) s10 s11
                  y28 y29 y30 y31)
             F (Z_to_bv 64 ret) fc None mc' (seg_rom rsegs))) ->
    evt rsegs (Q0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb)
      (MS (mkR (Z_to_bv 64 ret) (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 A)
               (Z_to_bv 64 (A + kd)) (Z_to_bv 64 (A + ks)) (Z_to_bv 64 N) x13 x14 x15 x16 x17
               (Z_to_bv 64 f) (Z_to_bv 64 o) (Z_to_bv 64 p) x21 x22 (Z_to_bv 64 fr)
               (Z_to_bv 64 (fr / 8 + off)) (Z_to_bv 64 off) s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 ASAN_MEMCPY) fc None mc (seg_rom rsegs)).
  Proof. intros. eapply c56_call_mcf; eassumption. Qed.

  Lemma c6_loop6 : forall (kk i : nat) (X : list byte) (a3w : word) (fr f spc j n : Z) (w56 : word)
      (mc : word -> option byte) (x1 x5 x6 x7 x10 x15 x16 x17 x21 x22 x28 x29 x30 x31 : word),
    p <> 0 -> o <> 0 -> (i + kk = 31)%nat -> (0 < kk)%nat -> length X = 32%nat ->
    bv_unsigned a3w = 18446744073709551615 - o ->
    withchk (firstn 31 X) = synth row b nb -> rc row b = 1 ->
    FK FS A fr f spc j n w56 ->
    BI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m FS (c6_W fr j n) fr w56 mc ->
    rw_cells rsegs mc o [CB 32 X] ->
    evt rsegs (Q0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb)
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 A)
               x10 (Z_to_bv 64 (psum X i)) (Z_to_bv 64 (Z.of_nat i)) a3w (Z_to_bv 64 31) x15 x16 x17
               (Z_to_bv 64 f) (Z_to_bv 64 o) (Z_to_bv 64 p) x21 x22 (Z_to_bv 64 fr)
               (Z_to_bv 64 (fr / 8 + off)) (Z_to_bv 64 off) s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x86d84) fc None mc (seg_rom rsegs)).
  Proof. intros. eapply c56_loop6; eassumption. Qed.

  (* ---- b = 6: the pre-tail, the record sum and the case ---- *)

  (* 0x86d28: the shadow checks of o + 15 and o + 16, the stamp byte (- sum) mod 128 at o + 15 and the 247 at
     o + 16, then the outer sum loop at 0x86d84 (port of the ubsan twin's tail6, U line 707). *)
  Lemma c6_tail6 : forall (X REC : list byte) (fr f spc j n : Z) (w56 : word) (mc : word -> option byte)
      (x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x21 x22 x28 x29 x30 x31 : word),
    p <> 0 -> o <> 0 -> length X = 32%nat ->
    0 <= psum REC 21 < 2^31 ->
    withchk (firstn 31 (upd_bytes X 15 [Z_to_bv 8 ((- psum REC 21) mod 128); bz 247])) = synth row b nb ->
    rc row b = 1 ->
    FK FS A fr f spc j n w56 ->
    BI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m FS (c6_W fr j n) fr w56 mc ->
    rw_cells rsegs mc o [CB 32 X] ->
    evt rsegs (Q0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb)
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 A)
               x10 (Z_to_bv 64 (psum REC 21)) x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 f) (Z_to_bv 64 o) (Z_to_bv 64 p) x21 x22 (Z_to_bv 64 fr)
               (Z_to_bv 64 (fr / 8 + off)) (Z_to_bv 64 off) s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x86d28) fc None mc (seg_rom rsegs)).
  Proof.
    intros X REC fr f spc j n w56 mc x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x21 x22 x28 x29 x30 x31
      Hp0 Ho0 LX PR ES Er HK HB HOc.
    pose proof c6_loop6 as L6. pose proof c6_chk as CHK.
    pose proof (c6_addr_o Ho0 fr f spc j n w56) as AOw.
    destruct (c6_geoA fr f spc j n w56 HK)
      as (Rsp & HA32 & HAlo & HAhi & FR8 & FRlo & FRhi & Fsp & FSpos & FSsz & HM1 & HM2).
    destruct (c6_geoO Ho0) as (HoA & Dos & Drt & Hoapp & Oapp & Dofs & DofsF).
    pose proof (c6_o_fr_iv Ho0 fr f spc j n w56 HK) as Dofr.
    pose proof HB as HB'. destruct HB' as (MU & WM & RM & MI & SV & (hh & HH) & F56).
    assert (RX15 : 0 <= o + 15 < 2^64) by c6_lia.
    assert (RX16 : 0 <= o + 16 < 2^64) by c6_lia.
    unfold c6_W, Wf in MU. cbn [app] in MU. unfold SAVES in SV.
    clear HB Fsp Drt DofsF Oapp Hoapp.
    c6_sc.
    (* 0x86d28: the store at o + 15 does not wrap, then its shadow check *)
    pose proof (CHK _ o 32 15 1 (o + 15) (AOw _ HK MU) ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(pose proof (Z.mod_pos_bound (o + 15) 8 eq_refl); lia) eq_refl) as SH15.
    step. bstep.
    step.
    chk_core (o + 15) RX15 (Z_to_bv 5 13) SH15 pre_sr no_extra.
    (* 0x86d44: negw / andi 127, the stamp byte at o + 15, then the check of o + 16 (on the memory after
       that store) *)
    step. step. step. step. bstep.
    pose proof (CHK _ o 32 16 1 (o + 16) (AOw _ HK MU) ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(pose proof (Z.mod_pos_bound (o + 16) 8 eq_refl); lia) eq_refl) as SH16.
    step.
    chk_core (o + 16) RX16 (Z_to_bv 5 12) SH16 pre_sr no_extra.
    (* 0x86d6c: the 247 at o + 16 and the registers of the outer sum *)
    step. step. step. step. step. step.
    apply (rs_rw_take _ _ _ _ 4) in HOc.
    cbn [firstn skipn cells_size csize cells_bytes cbytes app Nat.add] in HOc.
    rewrite mb_stamp8 in HOc.
    match type of HOc with rw_cells _ _ _ [CB 32 ?X6] =>
      replace X6 with (upd_bytes X 15 [Z_to_bv 8 ((- psum REC 21) mod 128); bz 247]) in HOc end.
    2:{ unfold upd_bytes. rewrite (c6_skk X 1 16). cbn [length Nat.add app]. rewrite ?app_nil_r.
        f_equal. apply mb_cons; [reflexivity|].
        apply mb_cons; [apply Z_to_bv8_mod; vm_compute; reflexivity|]. reflexivity. }
    eapply (L6 31%nat 0%nat (upd_bytes X 15 [Z_to_bv 8 ((- psum REC 21) mod 128); bz 247]) _
              fr f spc j n w56 _);
      [exact Hp0 | exact Ho0 | lia | lia
      | rewrite upd_bytes_length by (cbn [length]; lia); exact LX
      | | exact ES | exact Er | exact HK | | exact HOc].
    - pose proof (zr_word (Z_to_bv 64 o)) as Ruo. unfold inr64 in Ruo.
      rewrite zb_lxor_ones by exact Ruo. rewrite (unsigned_lit o) by lia.
      rewrite unsigned_lit by lia. reflexivity.
    - split; [unfold c6_W, Wf; exact MU|]. split; [assumption|]. split; [assumption|].
      split; [assumption|]. split; [assumption|]. split; [eexists; eassumption | assumption].
  Qed.

  (* 0x86d18: the inner byte sum over the window record [A + 35, A + 56) of build_ident_last.  The record is
     in the function's own window, so its loads carry no shadow check (port of the ubsan twin's loopr,
     U line 735). *)
  Lemma c6_loopr : forall (kk i : nat) (REC X : list byte) (fr f spc j n : Z) (w56 : word)
      (mc : word -> option byte) (x1 x5 x6 x7 x13 x14 x15 x16 x17 x21 x22 x28 x29 x30 x31 : word),
    p <> 0 -> o <> 0 -> (i + kk = 21)%nat -> (0 < kk)%nat ->
    length REC = 21%nat -> length X = 32%nat ->
    bytes_at rsegs mc (A + 35) REC ->
    withchk (firstn 31 (upd_bytes X 15 [Z_to_bv 8 ((- psum REC 21) mod 128); bz 247])) = synth row b nb ->
    rc row b = 1 ->
    FK FS A fr f spc j n w56 ->
    BI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m FS (c6_W fr j n) fr w56 mc ->
    rw_cells rsegs mc o [CB 32 X] ->
    evt rsegs (Q0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb)
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 A)
               (Z_to_bv 64 (A + 35 + Z.of_nat i)) (Z_to_bv 64 (psum REC i)) (Z_to_bv 64 (A + 56))
               x13 x14 x15 x16 x17
               (Z_to_bv 64 f) (Z_to_bv 64 o) (Z_to_bv 64 p) x21 x22 (Z_to_bv 64 fr)
               (Z_to_bv 64 (fr / 8 + off)) (Z_to_bv 64 off) s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x86d18) fc None mc (seg_rom rsegs)).
  Proof.
    induction kk as [|kk IH]; intros i REC X fr f spc j n w56 mc x1 x5 x6 x7 x13 x14 x15 x16 x17 x21 x22
      x28 x29 x30 x31 Hp0 Ho0 Hik Hk LR LX HREC ES Er HK HB HOc; [c6_lia|].
    pose proof c6_tail6 as T6.
    destruct (c6_geoA fr f spc j n w56 HK)
      as (Rsp & HA32 & HAlo & HAhi & FR8 & FRlo & FRhi & Fsp & FSpos & FSsz & HM1 & HM2).
    pose proof (rd_byte rsegs mc (A + 35) REC i HREC ltac:(c6_lia)) as RD.
    pose proof (psum_range REC i) as PR.
    pose proof (psum_range REC 21) as PR21.
    clear Fsp.
    c6_sc.
    step. step. step.
    rewrite psum_S_zxb.
    step.
    rewrite (rc_eqb_lit (A + 35 + Z.of_nat i + 1) (A + 56)) by lia.
    destruct kk as [|kk].
    - replace (A + 35 + Z.of_nat i + 1 =? A + 56) with true by (symmetry; apply Z.eqb_eq; lia).
      cbn [negb]. cbv iota. replace (S i) with 21%nat by lia.
      eapply T6; first [lia | eassumption].
    - replace (A + 35 + Z.of_nat i + 1 =? A + 56) with false by (symmetry; apply Z.eqb_neq; lia).
      cbn [negb]. cbv iota.
      replace (A + 35 + Z.of_nat i + 1) with (A + 35 + Z.of_nat (S i)) by lia.
      eapply (IH (S i)); first [lia | eassumption].
  Qed.

  (* 0x86b24: name_field into the window's buffer at A + 56, the five header bytes of the record at A + 35,
     the record's copy of the name at A + 40, nine checked header bytes into the output block, the six name
     bytes at o + 9, then the record sum, the pre-tail, the outer sum and the release. *)
  Lemma c6_case6 : forall (fr f spc j n : Z) (w56 : word) (mc : word -> option byte)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31 : word),
    b = 6 -> p <> 0 -> o <> 0 ->
    FK FS A fr f spc j n w56 ->
    BI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m FS (Wf sp FS fr j n ++ [(o, o + 32)]) fr w56 mc ->
    rw_cells rsegs mc o [CB 32 (zeros 32)] ->
    evt rsegs (Q0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb)
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 A)
               x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 f) (Z_to_bv 64 o) (Z_to_bv 64 p)
               (Z_to_bv 64 (-1)) x22 (Z_to_bv 64 fr) (Z_to_bv 64 (fr / 8 + off)) (Z_to_bv 64 off) s10 s11
               x28 x29 x30 x31)
          F (Z_to_bv 64 0x86b24) fc None mc (seg_rom rsegs)).
  Proof.
    intros fr f spc j n w56 mc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x28 x29 x30 x31
      Hb Hp0 Ho0 HK HB HOc.
    pose proof c6_call_nf as CNF. pose proof c6_call_mco as CMC. pose proof c6_call_mcf as CMF.
    pose proof c6_loopr as LR. pose proof Hrel as REL. pose proof (c6_Wu Hp0 Ho0 fr j n) as EW.
    pose proof c6_chk as CHK. pose proof c6_rt as RT.
    pose proof (c6_addr_o Ho0 fr f spc j n w56) as AOw.
    pose proof c6_rowb as ROWB. pose proof c6_app_win as APW. pose proof c6_p64 as P64.
    destruct (c6_geoA fr f spc j n w56 HK)
      as (Rsp & HA32 & HAlo & HAhi & FR8 & FRlo & FRhi & Fsp & FSpos & FSsz & HM1 & HM2).
    destruct (c6_geoP Hp0) as (Hp8 & Hrow & HpA & Dps & Dpo & Papp).
    destruct (c6_geoO Ho0) as (HoA & Dos & Drt & Hoapp & Oapp & Dofs & DofsF).
    pose proof (c6_frpos fr f spc j n w56 HK) as FKp.
    pose proof (c6_o_fr_iv Ho0 fr f spc j n w56 HK) as Dofr.
    assert (SPC1 : A - 64 <= spc <= A) by (clear -FKp; destruct FKp as [(E & _) | (E & _)]; lia).
    pose proof HB as HB'. destruct HB' as (MU & WM & RM & MI & SV & (hh & HH) & F56).
    destruct (RT fr f spc j n w56 mc HK Hp0 Ho0 HB) as (AC & SW & ST).
    pose proof (ROWB Hp0 Ho0 fr f spc j n w56 mc HK MU) as HRB.
    pose proof (rs_rd4 rsegs mc p row 56 HRB ltac:(clear -Hrow; lia)) as RD56.
    change (Z.of_nat 56) with 56 in RD56.
    pose proof (rs_rw32_range row 56) as Rh.
    pose proof (c6_addr_p Hp0 Ho0 fr f spc j n w56 mc HK MU) as APm.
    (* the window's scratch buffer [A + 35, A + 72) *)
    destruct (stk_split rsegs mc _ (A + 72) _ ST ltac:(clear -HAlo HAhi; lia)) as [STb _].
    destruct (stk_carve rsegs mc _ (A + 72) 37%nat STb ltac:(clear -HAlo HAhi HM1; cbn [Z.of_nat]; lia))
      as [_ [WB HWB]].
    replace (A + 72 - Z.of_nat 37) with (A + 35) in HWB by (cbn [Z.of_nat]; lia).
    unfold Wf in MU. cbn [app] in MU. unfold SAVES in SV.
    clear Fsp HB ST STb ROWB RT FKp.
    c6_hide Dps. c6_hide Dpo. c6_hide DofsF. c6_hide Drt.
    c6_sc.
    (* 0x86b24: p is 8-aligned, so the alignment branch is not taken *)
    step. step.
    replace (Z.land (bv_unsigned (Z_to_bv 64 p)) 7) with 0
      by (rewrite unsigned_lit by lia; rewrite rc_land7; rewrite Hp8; reflexivity).
    nf.
    (* the instrumented check of the 4 bytes at p + 56 *)
    step.
    assert (RX56 : 0 <= p + 56 < 2^64) by lia.
    pose proof (CHK mc p 296 56 4 (p + 56) APm ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(pose proof (Z.mod_pos_bound p 8 eq_refl); Z.div_mod_to_equations; lia) eq_refl)
      as SH56.
    chk_core (p + 56) RX56 (Z_to_bv 5 12) SH56 pre_sr add1.
    step. step.
    rewrite mb_sx32_eq0 by lia.
    destruct (Z.eqb_spec (rw32 row 56) 0) as [H0|H0]; cbv iota.
    { (* has row = 0: the block stays zero and the return value is 0 *)
      step. step.
      assert (Epo : (p =? 0) || (o =? 0) = false)
        by (apply orb_false_iff; split; apply Z.eqb_neq; assumption).
      eapply (REL fr f spc j n w56 _ 0); [exact HK | | | ].
      - rewrite Epo, Hb, mb_rc6. unfold has. rewrite H0. reflexivity.
      - rewrite EW. split; [unfold c6_W, Wf; exact MU|].
        split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
        split; [eexists; eassumption | assumption].
      - rewrite Epo, Hb, mb_synth6. unfold has. rewrite H0.
        exact (mb_rw1 _ _ _ _ _ HOc). }
    (* name_field (p, A + 56) *)
    step. step. step.
    eapply (CNF 56 0x86b54 fr f spc j n w56 mc WB (zeros 32));
      [exact Hp0 | exact Ho0 | right; exact Hb | unfold has; exact H0
      | apply ret_pc_even; [lia | reflexivity] | lia | lia | exact HK | | exact HWB | exact HOc |].
    { split; [unfold c6_W, Wf; exact MU|]. split; [assumption|]. split; [assumption|].
      split; [assumption|]. split; [assumption|]. split; [eexists; eassumption | assumption]. }
    intros mc2 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 HB2 HWB2 HOB2 HNM LN.
    pose proof HB2 as HB2'. destruct HB2' as (MU2 & WM2 & RM2 & MI2 & SV2 & (hh2 & HH2) & F562).
    unfold c6_W, Wf in MU2. cbn [app] in MU2. unfold SAVES in SV2.
    clear MU WM RM MI SV HH F56 HWB HOc HRB RD56 APm AC SW.
    (* 0x86b54: the five header bytes of the record at A + 35 *)
    step. step. step. step. bstep.
    step. step. bstep.
    step. step. step. step. bstep.
    step. step. bstep.
    step. step. step. step. bstep.
    apply (rs_rw_take _ _ _ _ 6) in HWB2.
    cbn [firstn skipn cells_size csize cells_bytes cbytes app Nat.add] in HWB2.
    match type of HWB2 with rw_cells _ _ _ [CB 37 ?Wv] => remember Wv as W5 eqn:EW5 end.
    pose proof HWB2 as HWB2c. destruct HWB2c as [[Hwf5 _] _].
    cbn [cells_wf cell_wf] in Hwf5. destruct Hwf5 as [LW5 _].
    assert (EH5 : firstn 5 W5 = [bz 5; bz 0; bz 16; bz 0; bz 1]).
    { rewrite EW5. cbn [firstn]. mb_bytes. }
    assert (ENM : firstn 16 (skipn 21 W5) = nmr row nb).
    { pose proof (rs_rw_sub rsegs _ (A + 35) 37 W5 21 16 HWB2 ltac:(lia)) as HS.
      replace (A + 35 + Z.of_nat 21) with (A + 56) in HS by (cbn [Z.of_nat]; lia).
      eapply c6_bat_det;
        [exact (mb_rw1 _ _ _ _ _ HS) | exact HNM
        | rewrite length_firstn, length_skipn, LW5, LN; reflexivity]. }
    assert (ENM2 : skipn 21 W5 = nmr row nb).
    { rewrite <- ENM. symmetry. apply c6_fall. rewrite length_skipn, LW5. reflexivity. }
    clear EW5 HNM.
    (* asan_memcpy (A + 40, A + 56, 16): the record's copy of the name *)
    step. step. step. step.
    eapply (CMF 40 56 16 0x86bb8 fr f spc j n w56 _ W5 _);
      [exact Hp0 | exact Ho0 | apply ret_pc_even; [lia | reflexivity]
      | lia | lia | lia | lia | exact HK | | exact HWB2 | exact HOB2 |].
    { split; [unfold c6_W, Wf; exact MU2|]. split; [assumption|]. split; [assumption|].
      split; [assumption|]. split; [assumption|]. split; [eexists; eassumption | assumption]. }
    intros mc3 u5 u6 u7 u11 u12 u13 u14 u15 u16 u17 u28 u29 u30 u31 HB3 HWB3 HOB3.
    replace (Z.to_nat (40 - 35)) with 5%nat in HWB3 by reflexivity.
    replace (Z.to_nat 16) with 16%nat in HWB3 by reflexivity.
    replace (Z.to_nat (56 - 35)) with 21%nat in HWB3 by reflexivity.
    rewrite ENM in HWB3.
    pose proof HB3 as HB3'. destruct HB3' as (MU3 & WM3 & RM3 & MI3 & SV3 & (hh3 & HH3) & F563).
    unfold c6_W, Wf in MU3. cbn [app] in MU3. unfold SAVES in SV3.
    clear MU2 WM2 RM2 MI2 SV2 HH2 F562 HB2 HWB2 HOB2.
    (* 0x86bb8: the nine checked header bytes of the output block *)
    assert (RXo : 0 <= o < 2^64) by lia.
    pose proof (CHK _ o 32 0 1 o (AOw _ HK MU3) ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(pose proof (Z.mod_pos_bound o 8 eq_refl); lia) ltac:(lia)) as SHo.
    chk_core o RXo (Z_to_bv 5 11) SHo pre_sr no_extra.
    step. step. step. bstep.
    assert (RX1 : 0 <= o + 1 < 2^64) by lia.
    pose proof (CHK _ o 32 1 1 (o + 1) (AOw _ HK MU3) ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(pose proof (Z.mod_pos_bound (o + 1) 8 eq_refl); lia) eq_refl) as SH1.
    step. chk_core (o + 1) RX1 (Z_to_bv 5 12) SH1 pre_sr no_extra.
    step. step. step. bstep.
    assert (RX2 : 0 <= o + 2 < 2^64) by lia.
    pose proof (CHK _ o 32 2 1 (o + 2) (AOw _ HK MU3) ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(pose proof (Z.mod_pos_bound (o + 2) 8 eq_refl); lia) eq_refl) as SH2.
    step. chk_core (o + 2) RX2 (Z_to_bv 5 12) SH2 pre_sr no_extra.
    step. step. bstep.
    assert (RX3 : 0 <= o + 3 < 2^64) by lia.
    pose proof (CHK _ o 32 3 1 (o + 3) (AOw _ HK MU3) ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(pose proof (Z.mod_pos_bound (o + 3) 8 eq_refl); lia) eq_refl) as SH3.
    step. chk_core (o + 3) RX3 (Z_to_bv 5 12) SH3 pre_sr no_extra.
    step. step. step. bstep.
    assert (RX4 : 0 <= o + 4 < 2^64) by lia.
    pose proof (CHK _ o 32 4 1 (o + 4) (AOw _ HK MU3) ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(pose proof (Z.mod_pos_bound (o + 4) 8 eq_refl); lia) eq_refl) as SH4.
    step. chk_core (o + 4) RX4 (Z_to_bv 5 12) SH4 pre_sr no_extra.
    step. step. bstep.
    assert (RX5 : 0 <= o + 5 < 2^64) by lia.
    pose proof (CHK _ o 32 5 1 (o + 5) (AOw _ HK MU3) ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(pose proof (Z.mod_pos_bound (o + 5) 8 eq_refl); lia) eq_refl) as SH5.
    step. chk_core (o + 5) RX5 (Z_to_bv 5 12) SH5 pre_sr no_extra.
    step. step. step. bstep.
    assert (RX6 : 0 <= o + 6 < 2^64) by lia.
    pose proof (CHK _ o 32 6 1 (o + 6) (AOw _ HK MU3) ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(pose proof (Z.mod_pos_bound (o + 6) 8 eq_refl); lia) eq_refl) as SH6.
    step. chk_core (o + 6) RX6 (Z_to_bv 5 12) SH6 pre_sr no_extra.
    step. step. bstep.
    assert (RX7 : 0 <= o + 7 < 2^64) by lia.
    pose proof (CHK _ o 32 7 1 (o + 7) (AOw _ HK MU3) ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(pose proof (Z.mod_pos_bound (o + 7) 8 eq_refl); lia) eq_refl) as SH7.
    step. chk_core (o + 7) RX7 (Z_to_bv 5 12) SH7 pre_sr no_extra.
    step. step. step. bstep.
    assert (RX8 : 0 <= o + 8 < 2^64) by lia.
    pose proof (CHK _ o 32 8 1 (o + 8) (AOw _ HK MU3) ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(pose proof (Z.mod_pos_bound (o + 8) 8 eq_refl); lia) eq_refl) as SH8.
    step. chk_core (o + 8) RX8 (Z_to_bv 5 12) SH8 pre_sr no_extra.
    step. step. step. bstep.
    (* 0x86cec: the window pointer A + 56 does not wrap *)
    step. step. rewrite mb_sltiu1 by lia. step. step. nfc.
    apply (rs_rw_take _ _ _ _ 10) in HOB3.
    cbn [firstn skipn cells_size csize cells_bytes cbytes app Nat.add] in HOB3.
    match type of HOB3 with rw_cells _ _ _ [CB 32 ?X0] =>
      replace X0 with (map bz [4; 2; 0; 13; 0; 2; 0; 254; 8] ++ zeros 23) in HOB3
        by (unfold zeros, bz; cbn [map repeat app skipn]; mb_bytes) end.
    (* asan_memcpy (o + 9, A + 66, 6): the six name bytes of build_ident_last *)
    step. step. step. step.
    eapply (CMC 9 66 6 0x86d0c fr f spc j n w56 _ (upd_bytes W5 5 (nmr row nb)) _);
      [exact Hp0 | exact Ho0 | apply ret_pc_even; [lia | reflexivity]
      | lia | lia | lia | lia | lia | lia | exact HK | | exact HWB3 | exact HOB3 |].
    { split; [unfold c6_W, Wf; exact MU3|]. split; [assumption|]. split; [assumption|].
      split; [assumption|]. split; [assumption|]. split; [eexists; eassumption | assumption]. }
    intros mc4 v5 v6 v7 v11 v12 v13 v14 v15 v16 v17 v28 v29 v30 v31 HB4 HWB4 HOB4.
    replace (Z.to_nat 9) with 9%nat in HOB4 by reflexivity.
    replace (Z.to_nat 6) with 6%nat in HOB4 by reflexivity.
    replace (Z.to_nat (66 - 35)) with (5 + 16 + 10)%nat in HOB4 by reflexivity.
    rewrite (c6_sk W5 (nmr row nb) 5 16 10 ltac:(lia) LN) in HOB4.
    cbn [Nat.add] in HOB4. rewrite ENM2 in HOB4.
    (* the record at A + 35: the five header bytes and the sixteen name bytes *)
    assert (EREC : firstn (5 + 16) (upd_bytes W5 5 (nmr row nb))
                   = [bz 5; bz 0; bz 16; bz 0; bz 1] ++ nmr row nb).
    { rewrite (c6_fu W5 (nmr row nb) 5 16 ltac:(lia) LN). rewrite EH5. reflexivity. }
    assert (HREC : bytes_at rsegs mc4 (A + 35) ([bz 5; bz 0; bz 16; bz 0; bz 1] ++ nmr row nb)).
    { rewrite <- EREC.
      pose proof (rs_rw_sub rsegs mc4 (A + 35) 37 (upd_bytes W5 5 (nmr row nb)) 0 (5 + 16)%nat HWB4
                    ltac:(lia)) as HS.
      replace (A + 35 + Z.of_nat 0) with (A + 35) in HS by (cbn [Z.of_nat]; lia).
      exact (mb_rw1 _ _ _ _ _ HS). }
    (* 0x86d0c: the inner sum over the record *)
    step. step. step.
    replace (Z_to_bv 64 (A + 35)) with (Z_to_bv 64 (A + 35 + Z.of_nat 0))
      by (f_equal; cbn [Z.of_nat]; lia).
    match type of HOB4 with rw_cells _ _ _ [CB 32 ?X6] =>
      eapply (LR 21%nat 0%nat ([bz 5; bz 0; bz 16; bz 0; bz 1] ++ nmr row nb) X6 fr f spc j n w56 _) end;
      [exact Hp0 | exact Ho0 | lia | lia
      | rewrite length_app, LN; reflexivity
      | | exact HREC | | | exact HK | exact HB4 | exact HOB4].
    - rewrite upd_bytes_length
        by (rewrite length_firstn, length_skipn, LN;
            cbn [length map zeros repeat app Nat.min Nat.sub Nat.add]; lia).
      cbn [length map zeros repeat app]. reflexivity.
    - rewrite Hb, mb_synth6. unfold has.
      replace (rw32 row 56 =? 0) with false by (symmetry; apply Z.eqb_neq; exact H0).
      unfold idl. f_equal.
      rewrite mb_idl_eq by first [reflexivity | rewrite length_firstn, length_skipn, LN; reflexivity].
      assert (EPS : psum ([bz 5; bz 0; bz 16; bz 0; bz 1] ++ nmr row nb) 21
                    = 22 + psum (nmr row nb) 16).
      { change (psum ([bz 5; bz 0; bz 16; bz 0; bz 1] ++ nmr row nb) 21)
          with (psum ([bz 5; bz 0; bz 16; bz 0; bz 1] ++ nmr row nb)
                     (length [bz 5; bz 0; bz 16; bz 0; bz 1] + 16)).
        rewrite mb_psum_app; f_equal; vm_compute; reflexivity. }
      rewrite EPS. unfold idl31, idlc. reflexivity.
    - rewrite Hb, mb_rc6. unfold has.
      replace (rw32 row 56 =? 0) with false by (symmetry; apply Z.eqb_neq; exact H0). reflexivity.
  Qed.
End c6_S.
