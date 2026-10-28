(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes FP StoreFast SysStep.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjPjNum SjPjDig.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.P Require Import Str_tac Sj_num_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Layout Pj_num_defs Pj_tochars_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Ltac arr_forget UA L :=
  lazymatch type of UA with
  | u8arr _ _ _ (upd_bytes ?bs ?k ?xs) =>
      let L' := fresh "L" in
      assert (L' : length (upd_bytes bs k xs) = length bs)
        by (apply upd_bytes_length; rewrite ?length_le1, ?length_le2, ?length_le4, ?length_le8; cbn [length]; lia);
      rewrite L in L'; clear L; rename L' into L;
      let nb := fresh "bs" in set (nb := upd_bytes bs k xs) in *; clearbody nb
  end.
Ltac arr_store UA L k n := u8_store UA k n; arr_forget UA L.

Section TC.
  Hypothesis HDB : dbox_stmt.
  Hypothesis HFM : fmt_stmt.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (q lo NB : Z) (m0 : word -> option byte).
  Hypothesis ROOM : (lo <= q - TC_STACK)%Z.
  Hypothesis GTOP : (GLOBALS_TOP <= lo)%Z.
  Hypothesis QNB : (q <= NB)%Z.
  Hypothesis NBHI : (NB + 40 < 2^63)%Z.

  Notation POST := (tochars_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo NB m0).
  Notation TCS pc xra xt0 xt1 xt2 xs0 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 F fc m :=
    (MS (mkR xra (Z_to_bv 64 (q + -32)) gp tp xt0 xt1 xt2 xs0 s1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
        F (Z_to_bv 64 pc) fc None m (seg_rom usegs)).

  Definition TUINV (m : word -> option byte) : Prop :=
    (exists j c0 c1, rw_cells usegs m (q + -32) [CB 8 j; CB 4 c0; CB 4 c1; C8 s0; C8 ra]) /\
    (exists nb, u8arr usegs m NB nb /\ length nb = 40%nat) /\
    mem_inv usegs m /\ munch [(q + -128, q); (NB, NB + 40)]%Z m0 m /\ wmono usegs m0 m /\ stk usegs m lo (q + -32).

  Lemma tcu_exit : forall pc e xra xt0 xt1 xt2 xs0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 (F : bvmap 5 word) (fc : bv 32) m,
    pc = 0x405c8%Z \/ pc = 0x4062c%Z ->
    TUINV m -> frm0 fc -> (NB < e <= NB + 27)%Z ->
    evt usegs POST (TCS pc xra xt0 xt1 xt2 xs0 (Z_to_bv 64 e) xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 F fc m).
  Proof using ROOM GTOP QNB NBHI.
    intros until m. intros HPC I FRM HE.
    destruct I as ((j & c0 & c1 & FR) & (nb & NA & NL) & MI & MU & WM & ST).
    unfold TC_STACK, GLOBALS_TOP in *.
    pose proof (stk_lo_nonneg _ _ _ _ ST) as LO0.
    destruct HPC as [-> | ->]; (
      zstep; zstep; zstep; zstep;
      release_frame FR ST q;
      pose proof (rw_cells_of_u8arr usegs _ _ _ NA) as NBC; rewrite NL in NBC;
      replace (q + -128)%Z with (q - 128)%Z in MU by lia;
      apply evt_done; unfold tochars_post, TC_STACK;
      do 16 eexists; exists m, e, nb;
      split; [cbv delta [mkR]; reflexivity|];
      split; [exact MU|]; split; [exact WM|]; split; [exact MI|]; split; [exact ST|]; split; [exact FRM|]; split; [exact HE| exact NBC]).
  Qed.

  Lemma tcu_zero : forall sg xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 (F : bvmap 5 word) (fc : bv 32) m,
    TUINV m -> frm0 fc -> (0 <= sg <= 1)%Z ->
    evt usegs POST (TCS 0x40590 xra xt0 xt1 xt2 (Z_to_bv 64 (NB + sg)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 F fc m).
  Proof using ROOM GTOP QNB NBHI.
    intros until m. intros I FRM HS.
    pose proof tcu_exit as EXIT.
    destruct I as ((j & c0 & c1 & FR) & (nb & NA & NL) & MI & MU & WM & ST).
    unfold TC_STACK, GLOBALS_TOP in *.
    pose proof (stk_lo_nonneg _ _ _ _ ST) as LO0.

    zstep. zstep.
    zstep. if_cases G1; zify_cond G1; [exfalso; rewrite ?unsigned_lit in G1 by lia; lia|].

    zstep. zstep.
    arr_store NA NL sg 1%nat.
    zstep. if_cases G2; zify_cond G2; [exfalso; rewrite ?unsigned_lit in G2 by lia; lia|].

    zstep. zstep.
    arr_store NA NL (sg + 1)%Z 1%nat.
    zstep. if_cases G3; zify_cond G3; [exfalso; rewrite ?unsigned_lit in G3 by lia; lia|].

    zstep. zstep.
    arr_store NA NL (sg + 2)%Z 1%nat.
    eapply evt_eq; [| eapply (EXIT 0x405c8%Z (NB + sg + 3)%Z); [left; reflexivity | | exact FRM | lia]].
    - num_st_eq.
    - split; [do 3 eexists; eassumption|]. split; [eexists; split; eassumption|]. split; [assumption|]. split; [assumption|]. split; assumption.
  Qed.

  Lemma sx32_e : forall e, (SF_EMIN <= e <= SF_EMAX)%Z -> sx32 (Z_to_bv 64 (e mod 4294967296)) = Z_to_bv 64 e.
  Proof.
    intros e H. unfold SF_EMIN, SF_EMAX in H. unfold sx32. f_equal. rewrite unsigned_lit by (Z.div_mod_to_equations; lia).
    rewrite swrap32_Z. Z.div_mod_to_equations. lia.
  Qed.

  Lemma tcu_nonzero : forall sg xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 (F : bvmap 5 word) (fc : bv 32) m,
    TUINV m -> frm0 fc -> (0 <= sg <= 1)%Z ->
    evt usegs POST (TCS 0x405fc xra xt0 xt1 xt2 (Z_to_bv 64 (NB + sg)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 F fc m).
  Proof using HDB HFM ROOM GTOP QNB NBHI.
    intros until m. intros I FRM HS.
    pose proof tcu_exit as EXIT.
    destruct I as ((j & c0 & c1 & FR) & (nb & NA & NL) & MI & MU & WM & ST).
    unfold TC_STACK, GLOBALS_TOP in *.
    pose proof (stk_lo_nonneg _ _ _ _ ST) as LO0.

    zstep. zstep. zstep. zstep. zstep. zstep.
    apply (proj1 (num_rw_cells_app usegs _ _ [CB 8 j] _)) in FR. destruct FR as [F0 FR].
    cbn [cells_size csize Nat.add] in FR. change (Z.of_nat 8) with 8%Z in FR. replace (q + -32 + 8)%Z with (q + -24)%Z in FR by lia.
    lazymatch type of FR with rw_cells _ _ _ (?a :: ?b :: ?rest) =>
      apply (proj1 (num_rw_cells_app usegs _ _ [a; b] rest)) in FR end.
    destruct FR as [CELLS SAVE].
    cbn [cells_size csize Nat.add] in SAVE. change (Z.of_nat 8) with 8%Z in SAVE. replace (q + -24 + 8)%Z with (q + -16)%Z in SAVE by lia.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_cut;
      [ eapply evt_eq; [| eapply (HDB) with (p := (q + -32)%Z) (lo := lo) (NB := NB) (sg := sg) (nb := nb);
                          [exact ST | unfold DBOX_STACK; lia | unfold GLOBALS_TOP; lia | exact MI | lia | lia | exact HS
                          | replace (q + -32 + 8)%Z with (q + -24)%Z by lia; exact CELLS | exact NA | exact NL] ];
        num_st_eq
      | post_call usegs mm ]
    end.
    rename x15 into n. rename x16 into e.
    match goal with H : rw_cells _ _ ?A [C4 (Z_to_bv 64 (_ mod 4294967296)%Z); C4 _] |- _ => rename H into CEL1; replace A with (q + -24)%Z in CEL1 by lia end.
    match goal with H : u8arr _ _ NB ?bs, L : length ?bs = 40%nat |- _ => rename H into NA1; rename L into NL1 end.
    match goal with H : stk _ _ lo (q + -32)%Z |- _ => rename H into ST1 end.
    match goal with H : (1 <= n <= 20)%Z |- _ => rename H into HN end.
    match goal with H : (SF_EMIN <= e <= SF_EMAX)%Z |- _ => rename H into HE end.

    zstep. zstep.
    rewrite (sx32_e e HE).
    replace (sx32 (Z_to_bv 64 n)) with (Z_to_bv 64 n)
      by (unfold sx32; f_equal; rewrite unsigned_lit by lia; symmetry; apply swrap32_id; lia).
    zstep. zstep. zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_cut;
      [ eapply evt_eq; [| eapply (HFM) with (p := (q + -32)%Z) (lo := lo) (NB := NB) (sg := sg) (n := n) (e := e);
                          [exact ST1 | unfold FMT_STACK; lia | unfold GLOBALS_TOP; lia | eassumption | lia | lia | exact HS | exact HN | exact HE
                          | exact NA1 | exact NL1] ];
        num_st_eq
      | post_call usegs mm ]
    end.
    match goal with H : u8arr _ _ NB ?bs, L : length ?bs = 40%nat |- _ => rename H into NA2; rename L into NL2 end.
    match goal with H : stk _ _ lo (q + -32)%Z |- _ => rename H into ST2 end.
    match goal with H : rw_cells _ _ (q + -24)%Z [C4 _; C4 _] |- _ => rename H into CELLS2 end.
    match goal with H : rw_cells _ _ (q + -32)%Z [CB 8 _] |- _ => rename H into F02 end.
    match goal with H : rw_cells _ _ (q + -16)%Z [C8 s0; C8 ra] |- _ => rename H into SAVE2 end.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (proj2 (num_rw_cells_app usegs mm (q + -24)%Z [C4 (Z_to_bv 64 (e mod 4294967296)); C4 (Z_to_bv 64 n)] [C8 s0; C8 ra])) as J1;
      cbn [cells_size csize Nat.add] in J1; change (Z.of_nat 8) with 8%Z in J1; replace (q + -24 + 8)%Z with (q + -16)%Z in J1 by lia;
      specialize (J1 (conj CELLS2 SAVE2)); cbn [app] in J1;
      pose proof (proj2 (num_rw_cells_app usegs mm (q + -32)%Z [CB 8 j] [C4 (Z_to_bv 64 (e mod 4294967296)); C4 (Z_to_bv 64 n); C8 s0; C8 ra])) as J2;
      cbn [cells_size csize Nat.add] in J2; change (Z.of_nat 8) with 8%Z in J2; replace (q + -32 + 8)%Z with (q + -24)%Z in J2 by lia;
      specialize (J2 (conj F02 J1)); cbn [app] in J2
    end.
    lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => idtac end.
    eapply evt_eq; [| eapply (EXIT 0x4062c%Z); [right; reflexivity | | exact FRM | ]].
    - num_st_eq.
    - apply (rw_cells_merge usegs _ _ [CB 8 j] [C4 (Z_to_bv 64 (e mod 4294967296))] [C4 (Z_to_bv 64 n); C8 s0; C8 ra]) in J2.
      cbn [app cells_size csize Nat.add] in J2.
      apply (rw_cells_merge usegs _ _ [CB 8 j; CB 4 _] [C4 (Z_to_bv 64 n)] [C8 s0; C8 ra]) in J2.
      cbn [app cells_size csize Nat.add] in J2.
      split; [do 3 eexists; exact J2|]. split; [eexists; split; eassumption|]. split; [assumption|]. split; [assumption|]. split; assumption.
    - lia.
  Qed.

  Lemma tochars_body : forall t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (junk : list byte),
    stk usegs m0 lo q -> mem_inv usegs m0 -> frm0 fc -> rw_cells usegs m0 NB [CB 40 junk] ->
    evt usegs POST
      (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 NB) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x4056c) fc None m0 (seg_rom usegs)).
  Proof using HDB HFM ROOM GTOP QNB NBHI.
    intros until junk. intros ST MI FRM NBC.
    pose proof tcu_zero as KZERO. pose proof tcu_nonzero as KNZ.
    pose proof ROOM as ROOM'. pose proof GTOP as GTOP'. unfold TC_STACK, GLOBALS_TOP in ROOM', GTOP'.
    pose proof (stk_lo_nonneg _ _ _ _ ST) as LO0.
    pose proof (munch_refl [(q + -128, q); (NB, NB + 40)]%Z m0) as MU. pose proof (wmono_refl usegs m0) as WM.
    zstep. carve_frame 32%nat ST.
    apply (rw_cells_split_CB usegs _ _ [] 32 junk0 [] [8;4;4;8;8]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.
    zstep. zstep.
    pose proof (u8arr_of_rw_cells usegs _ _ _ _ NBC) as NA.
    assert (NL : length junk = 40%nat) by (destruct NBC as [[Hwf _] _]; cbn in Hwf; tauto).
    clear NBC.
    zstep. zstep.
    if_cases K.
    -
      zstep. zstep.
      zstep. if_cases G; zify_cond G; [exfalso; rewrite ?unsigned_lit in G by lia; lia|].

      zstep. zstep.
      arr_store NA NL 0%Z 1%nat.
      zstep. zstep.
      zstep. if_cases KZ.
      + eapply evt_eq; [| eapply (KZERO 1%Z); [ | exact FRM | lia]]; [num_st_eq|].
        split; [do 3 eexists; exact FR|]. split; [eexists; split; eassumption|]. split; [assumption|]. split; [assumption|]. split; assumption.
      + eapply evt_eq; [| eapply (KNZ 1%Z); [ | exact FRM | lia]]; [num_st_eq|].
        split; [do 3 eexists; exact FR|]. split; [eexists; split; eassumption|]. split; [assumption|]. split; [assumption|]. split; assumption.
    -
      zstep. zstep. zstep.
      zstep. if_cases KZ.
      + eapply evt_eq; [| eapply (KNZ 0%Z); [ | exact FRM | lia]]; [num_st_eq|].
        split; [do 3 eexists; exact FR|]. split; [eexists; split; eassumption|]. split; [assumption|]. split; [assumption|]. split; assumption.
      + eapply evt_eq; [| eapply (KZERO 0%Z); [ | exact FRM | lia]]; [num_st_eq|].
        split; [do 3 eexists; exact FR|]. split; [eexists; split; eassumption|]. split; [assumption|]. split; [assumption|]. split; assumption.
  Qed.
End TC.

Theorem tochars_top : dbox_stmt -> fmt_stmt -> tochars_stmt.
Proof.
  intros HDB HFM. unfold tochars_stmt. intros until junk. intros ST ROOM GTOP MI FRM QNB NBHI NBC. unfold TC_ENTRY.
  eapply tochars_body; eassumption.
Qed.

