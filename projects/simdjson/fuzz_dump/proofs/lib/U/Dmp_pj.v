(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Spec Require Import Prelim STree Malloc Monad Stdio StrFun SjModel Target Prog.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Sj Require Import SjTape SjTapeList SjTapeTile SjDmp.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.P Require Import Sj_h_arith Atp_objl.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.U Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_h_kit Atp_defs Atp_kitu Pj_loc_defs Pj_loc_get Pj_os_defs El_os_defs El_ins_iface El_defs Dmp_defs Dmp_pj_iface Dmp_pj_kit Dmp_pj_leaf.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition pj_dbl_case : Prop :=
  forall (D : pjenv) (j32 : list byte) (K : machine_state -> Prop) (x1 gp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
    pjenv_ok D -> os_putX_stmt -> ins_d_stmt ->
    PINV [CB 32 j32] D m -> frm0 fc -> pe_i D + 2 <= pe_n D -> Tf (pe_tws D) (pe_i D) = tword t_dbl 0 ->
    KEXIT D [CB 32 j32] K gp ->
    evt usegs K (DST D (pe_i D) t_dbl x1 gp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F fc m).

Definition pj_str_case : Prop :=
  forall (D : pjenv) (j32 : list byte) (K : machine_state -> Prop) (x1 gp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
    pjenv_ok D -> os_putX_stmt ->
    PINV [CB 32 j32] D m -> frm0 fc -> pe_i D + 1 <= pe_n D -> is_str (Tf (pe_tws D)) (Tf (pe_sbs D)) (pe_sn D) (pe_i D) ->
    KEXIT D [CB 32 j32] K gp ->
    evt usegs K (DST D (pe_i D) t_str x1 gp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F fc m).

Definition pj_arr_case (d : nat) : Prop :=
  forall (D : pjenv) (j32 : list byte) (K : machine_state -> Prop) (x1 gp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (e c cv : Z),
    pjenv_ok D -> os_putX_stmt -> ins_b_stmt -> ins_l_stmt -> ins_ul_stmt -> ins_d_stmt -> pj_stmt d ->
    PINV [CB 32 j32] D m -> frm0 fc -> pe_i D < e -> e + 1 <= pe_n D -> 0 <= cv <= CNT_MAX ->
    Tf (pe_tws D) (pe_i D) = cword t_arr (e + 1) cv -> Tf (pe_tws D) e = tword t_arr_end (pe_i D) -> tiles (elem (Tf (pe_tws D)) (Tf (pe_sbs D)) (pe_sn D) ck_any d) (pe_i D + 1) e c ->
    pe_lo D + pj_need (S d) <= pe_q D ->
    KEXIT D [CB 32 j32] K gp ->
    evt usegs K (DST D (pe_i D) t_arr x1 gp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F fc m).

Definition pj_obj_case (d : nat) : Prop :=
  forall (D : pjenv) (j32 : list byte) (K : machine_state -> Prop) (x1 gp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (e c cv : Z),
    pjenv_ok D -> os_putX_stmt -> ins_b_stmt -> ins_l_stmt -> ins_ul_stmt -> ins_d_stmt -> pj_stmt d ->
    PINV [CB 32 j32] D m -> frm0 fc -> pe_i D < e -> e + 1 <= pe_n D -> 0 <= cv <= CNT_MAX ->
    Tf (pe_tws D) (pe_i D) = cword t_obj (e + 1) cv -> Tf (pe_tws D) e = tword t_obj_end (pe_i D) -> tiles (field (Tf (pe_tws D)) (Tf (pe_sbs D)) (pe_sn D) (elem (Tf (pe_tws D)) (Tf (pe_sbs D)) (pe_sn D) ck_any d)) (pe_i D + 1) e c ->
    pe_lo D + pj_need (S d) <= pe_q D ->
    (forall lc, cells_size lc = 32%nat -> KEXIT D lc K gp) ->
    evt usegs K (DST D (pe_i D) t_obj x1 gp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F fc m).

Section Proof.
  Hypothesis PUT : os_putX_stmt.
  Hypothesis INSB : ins_b_stmt.
  Hypothesis INSL : ins_l_stmt.
  Hypothesis INSUL : ins_ul_stmt.
  Hypothesis INSD : ins_d_stmt.
  Lemma pj_dbl_proof : pj_dbl_case.
  Proof. unfold pj_dbl_case. intros until m. intros DOK PUT' INSD' DI FRM IN TY HK. eapply (pj_dbl D DOK PUT' INSD' j32); eassumption. Qed.

  Lemma pj_str_proof : pj_str_case.
  Proof. unfold pj_str_case. intros until m. intros DOK PUT' DI FRM IN STRI HK. eapply (pj_str D DOK PUT' j32); eassumption. Qed.

  Hypothesis ARR : forall d, pj_arr_case d.
  Hypothesis OBJ : forall d, pj_obj_case d.

  Lemma elem_cases : forall T S sn d i j, elem T S sn ck_any d i j ->
    (j = i + 1 /\ (T i = tword t_true 0 \/ T i = tword t_false 0 \/ T i = tword t_null 0))
    \/ (j = i + 2 /\ (T i = tword t_i64 0 \/ T i = tword t_u64 0 \/ T i = tword t_dbl 0))
    \/ (j = i + 1 /\ is_str T S sn i)
    \/ (exists d' e c cv, d = Datatypes.S d' /\ j = e + 1 /\ 0 <= cv <= CNT_MAX /\
          ((T i = cword t_arr (e + 1) cv /\ T e = tword t_arr_end i /\ tiles (elem T S sn ck_any d') (i + 1) e c)
           \/ (T i = cword t_obj (e + 1) cv /\ T e = tword t_obj_end i /\ tiles (field T S sn (elem T S sn ck_any d')) (i + 1) e c))).
  Proof.
    intros T S sn d i j EL.
    assert (SC : scalar T S sn i j -> (j = i + 1 /\ (T i = tword t_true 0 \/ T i = tword t_false 0 \/ T i = tword t_null 0))
      \/ (j = i + 2 /\ (T i = tword t_i64 0 \/ T i = tword t_u64 0 \/ T i = tword t_dbl 0)) \/ (j = i + 1 /\ is_str T S sn i)
      \/ (exists d' e c cv, d = Datatypes.S d' /\ j = e + 1 /\ 0 <= cv <= CNT_MAX /\
          ((T i = cword t_arr (e + 1) cv /\ T e = tword t_arr_end i /\ tiles (elem T S sn ck_any d') (i + 1) e c)
           \/ (T i = cword t_obj (e + 1) cv /\ T e = tword t_obj_end i /\ tiles (field T S sn (elem T S sn ck_any d')) (i + 1) e c)))).
    { intros [[-> H]|[[-> H]|[-> H]]]; [left; auto| right; left; auto| right; right; left; auto]. }
    destruct d as [|d']; cbn [elem] in EL.
    - destruct EL as [X|[]]. exact (SC X).
    - destruct EL as [X|CO]; [exact (SC X)|]. right; right; right.
      destruct CO as (e & c & cv & -> & CK & HC). unfold ck_any in CK. exists d', e, c, cv.
      split; [reflexivity|]. split; [reflexivity|]. split; [exact CK|]. exact HC.
  Qed.

  Lemma pj_level : forall d, (forall d', d = Datatypes.S d' -> pj_stmt d') -> pj_stmt d.
  Proof.
    intros d IH. unfold pj_stmt. intros until errv.
    intros EL I0 JN NR SBS SNR DOCC QD OSD DH TB T0 T8 TH TI SB S0 SH SI OSXm QO OSH O8 D8 LB DCC DCB SSP TPC ERR ST NEED GLO AL MI FRM.
    pose proof (elem_lt _ _ _ _ _ _ _ EL) as IJ.
    set (D := mkPE q lo OS DOC TAPE SBUF tws sbs i canary m ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
    assert (DOK : pjenv_ok D).
    { unfold pjenv_ok, D; cbn. pose proof (pj_need_pos d). unfold DMP_PJ_FRAME in *. repeat split; try assumption; lia. }
    assert (KX : forall lc, cells_size lc = 32%nat -> KEXIT D lc (pj_post ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo OS canary m) gp).
    { intros lc LCS. unfold KEXIT. intros. eapply (pj_exit D DOK lc); assumption. }
    destruct (elem_cases _ _ _ _ _ _ EL) as [[-> TY]|[[-> TY]|[[-> STRI]|(d' & e & c & cv & Hd & -> & CV & CO)]]].
    - assert (TIR : 0 <= Tf tws i < 2^64) by (destruct TY as [E|[E|E]]; rewrite E; unfold tword, t_true, t_false, t_null; lia).
      eapply (pj_enter D DOK _ gp t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc errv);
        [exact TIR| exact DOCC| exact TB| exact SB| exact OSXm| exact LB| exact DCC| exact DCB| exact SSP| exact TPC| exact ERR| exact ST| exact MI| exact FRM|].
      intros m1 ty j32 y1 y11 y12 y13 y14 DI1 TYC. cbn [pe_tws pe_i D] in TYC.
      destruct TY as [E|[E|E]].
      + assert (Hty : ty = t_true) by (rewrite E, ttype_tword in TYC by lia; unfold t_true, t_false in *; lia). subst ty.
        eapply (pj_bool D DOK PUT INSB j32); [exact DI1| exact FRM| left; exact E| apply KX; reflexivity].
      + assert (Hty : ty = t_true) by (rewrite E, ttype_tword in TYC by lia; unfold t_true, t_false in *; lia). subst ty.
        eapply (pj_bool D DOK PUT INSB j32); [exact DI1| exact FRM| right; exact E| apply KX; reflexivity].
      + assert (Hty : ty = t_null) by (rewrite E, ttype_tword in TYC by lia; unfold t_null, t_false in *; lia). subst ty.
        eapply (pj_null D DOK PUT j32); [exact DI1| exact FRM| exact E| apply KX; reflexivity].
    - assert (TIR : 0 <= Tf tws i < 2^64) by (destruct TY as [E|[E|E]]; rewrite E; unfold tword, t_i64, t_u64, t_dbl; lia).
      eapply (pj_enter D DOK _ gp t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc errv);
        [exact TIR| exact DOCC| exact TB| exact SB| exact OSXm| exact LB| exact DCC| exact DCB| exact SSP| exact TPC| exact ERR| exact ST| exact MI| exact FRM|].
      intros m1 ty j32 y1 y11 y12 y13 y14 DI1 TYC. cbn [pe_tws pe_i D] in TYC.
      destruct TY as [E|[E|E]].
      + assert (Hty : ty = t_i64) by (rewrite E, ttype_tword in TYC by lia; unfold t_i64, t_false in *; lia). subst ty.
        eapply (pj_i64 D DOK PUT INSL j32); [exact DI1| exact FRM| cbn; lia| exact E| apply KX; reflexivity].
      + assert (Hty : ty = t_u64) by (rewrite E, ttype_tword in TYC by lia; unfold t_u64, t_false in *; lia). subst ty.
        eapply (pj_u64 D DOK PUT INSUL j32); [exact DI1| exact FRM| cbn; lia| exact E| apply KX; reflexivity].
      + assert (Hty : ty = t_dbl) by (rewrite E, ttype_tword in TYC by lia; unfold t_dbl, t_false in *; lia). subst ty.
        eapply (pj_dbl_proof D j32); [exact DOK| exact PUT| exact INSD| exact DI1| exact FRM| cbn; lia| exact E| apply KX; reflexivity].
    - pose proof (key_word_range _ _ _ _ STRI SNR) as (TIR & _ & KT).
      eapply (pj_enter D DOK _ gp t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc errv);
        [exact TIR| exact DOCC| exact TB| exact SB| exact OSXm| exact LB| exact DCC| exact DCB| exact SSP| exact TPC| exact ERR| exact ST| exact MI| exact FRM|].
      intros m1 ty j32 y1 y11 y12 y13 y14 DI1 TYC. cbn [pe_tws pe_i D] in TYC.
      assert (Hty : ty = t_str) by (rewrite KT in TYC; unfold t_str, t_false in *; lia). subst ty.
      eapply (pj_str_proof D j32); [exact DOK| exact PUT| exact DI1| exact FRM| cbn; lia| exact STRI| apply KX; reflexivity].
    - pose proof (IH d' Hd) as PJ'.
      assert (LT : i < e).
      { destruct CO as [(_ & _ & HT)|(_ & _ & HT)].
        - pose proof (tiles_le _ (elem_lt _ _ _ _ d') _ _ _ HT). lia.
        - pose proof (tiles_le _ (field_lt _ _ _ _ (elem_lt _ _ _ _ d')) _ _ _ HT). lia. }
      assert (NEED' : lo + pj_need (Datatypes.S d') <= q) by (subst d; exact NEED).
      destruct CO as [(E & EE & HT)|(E & EE & HT)].
      + assert (TIR : 0 <= Tf tws i < 2^64) by (rewrite E; unfold cword, tword, t_arr, CNT_MAX in *; lia).
        eapply (pj_enter D DOK _ gp t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc errv);
          [exact TIR| exact DOCC| exact TB| exact SB| exact OSXm| exact LB| exact DCC| exact DCB| exact SSP| exact TPC| exact ERR| exact ST| exact MI| exact FRM|].
        intros m1 ty j32 y1 y11 y12 y13 y14 DI1 TYC. cbn [pe_tws pe_i D] in TYC.
        assert (Hty : ty = t_arr) by (rewrite E, ttype_cword in TYC by lia; unfold t_arr, t_false in *; lia). subst ty.
        eapply (ARR d' D j32); [exact DOK| exact PUT| exact INSB| exact INSL| exact INSUL| exact INSD| exact PJ'| exact DI1| exact FRM| exact LT| cbn; lia| exact CV
          | exact E| exact EE| exact HT| exact NEED'| apply KX; reflexivity].
      + assert (TIR : 0 <= Tf tws i < 2^64) by (rewrite E; unfold cword, tword, t_obj, CNT_MAX in *; lia).
        eapply (pj_enter D DOK _ gp t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc errv);
          [exact TIR| exact DOCC| exact TB| exact SB| exact OSXm| exact LB| exact DCC| exact DCB| exact SSP| exact TPC| exact ERR| exact ST| exact MI| exact FRM|].
        intros m1 ty j32 y1 y11 y12 y13 y14 DI1 TYC. cbn [pe_tws pe_i D] in TYC.
        assert (Hty : ty = t_obj) by (rewrite E, ttype_cword in TYC by lia; unfold t_obj, t_false in *; lia). subst ty.
        eapply (OBJ d' D j32); [exact DOK| exact PUT| exact INSB| exact INSL| exact INSUL| exact INSD| exact PJ'| exact DI1| exact FRM| exact LT| cbn; lia| exact CV
          | exact E| exact EE| exact HT| exact NEED'| exact KX].
  Qed.

  Theorem pj_proof : forall d, pj_stmt d.
  Proof. induction d as [|d IHd]; apply pj_level; intros d' Hd; [discriminate Hd| injection Hd as <-; exact IHd]. Qed.

  Theorem pj_root : pj_root_stmt.
  Proof. exact (pj_root_of (pj_proof TAPE_MAX_DEPTH)). Qed.
End Proof.

Theorem pj_root_of_parts : os_putX_stmt -> ins_b_stmt -> ins_l_stmt -> ins_ul_stmt -> ins_d_stmt ->
  (forall d, pj_arr_case d) -> (forall d, pj_obj_case d) -> pj_root_stmt.
Proof. intros. eapply pj_root; assumption. Qed.
End WithCeiling0.
