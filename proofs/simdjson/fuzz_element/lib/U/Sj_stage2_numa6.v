(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList SjNumber.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Sj_stage2_defs Sj_stage2_tapek Sj_tables Sj_stage2_traps Sj_stage2_guard Sj_num_iface
  Sj_stage2_numkit Sj_stage2_numkit2 Sj_stage2_numkit3 Sj_stage2_numa_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac transport_call_extra segs W m m' MU WM ::= s2_timg_call segs W m m' MU WM.
Local Ltac lia ::= s2lia.
Local Ltac tlia ::= s2tlia.
Local Ltac solve_load ::= first [ solve_load_base | s2_load_buf | s2_load_sown | solve_load_image ].
Local Ltac solve_store ::= first [ solve_store0 | s2_store_wr ].
Local Ltac s2_store_done_wr ::= s2_note_tape; s2_store_done_wr_v2.

Section NumA6.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Notation bs := (e_bs E).
  Notation o s := (e_off E (k s)).
  Hypothesis HSLOWF : slowfu_stmt_g usegs 0x5edf4 0x111000.
  Hypothesis HPFF : pffu_stmt_g usegs 0x5eea4 0x111000.

  Hypothesis HROOM : (e_lo E + 368 + NUMU_STACK <= bv_unsigned (e_sp E))%Z.

  Lemma numa_call : forall (Q : machine_state -> Prop) (entry r1 r0 RA off : Z) (nxt : word) (sc : list (bool * Z))
      c0 c1 c2 c3 c4 c5 c6 c7 c8 j72 xt0 xt1 xt2 xs0 xs1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 (F : bvmap 5 word) (fc : bv 32) (m1 : mem),
    numwu_stmt_g usegs entry 0x111000 r1 r0 ->
    (0 <= RA < 2 ^ 64)%Z -> (RA mod 2 = 0)%Z -> (0 <= off <= e_len E)%Z ->
    csize c0 = 8%nat -> csize c1 = 8%nat -> csize c2 = 8%nat -> csize c3 = 8%nat -> csize c4 = 8%nat ->
    csize c5 = 8%nat -> csize c6 = 8%nat -> csize c7 = 8%nat -> csize c8 = 8%nat ->
    MEMI E nxt [c0; c1; c2; c3; c4; c5; c6; c7; c8; CB 8 j72] sc fc m1 ->
    (forall (flag : bool) (v : word) yt0 yt1 yt2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 (F' : bvmap 5 word) (fc' : bv 32) (m' : mem),
       MEMI E nxt [c0; c1; c2; c3; c4; c5; c6; c7; c8; C8 v] sc fc' m' ->
       evt usegs Q (S2R E RA (Z_to_bv 64 (RA)) yt0 yt1 yt2 xs0 xs1 (Z_to_bv 64 ((if flag then r1 else r0))) ya1 ya2 ya3 ya4 ya5 ya6 ya7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 yt3 yt4 yt5 yt6 F' fc' m')) ->
    evt usegs Q (S2R E entry (Z_to_bv 64 (RA)) xt0 xt1 xt2 xs0 xs1 (Z_to_bv 64 (e_BUF E + off)) (Z_to_bv 64 (bv_unsigned (e_sp E) + -296)) xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m1).
  Proof using OK HROOM.
    intros Q entry r1 r0 RA off nxt sc c0 c1 c2 c3 c4 c5 c6 c7 c8 j72 xt0 xt1 xt2 xs0 xs1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m1 HS HRA HRA2 HOFF
      E0 E1 E2 E3 E4 E5 E6 E7 E8 HM K.
    s2_env OK. unfold NUMU_STACK in HROOM.
    s2_open_mem HM.
    lazymatch type of FR with rw_cells _ _ _ (_ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: ?rest) =>
      change (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: c8 :: CB 8 j72 :: rest) with ([c0; c1; c2; c3; c4; c5; c6; c7; c8] ++ [CB 8 j72] ++ rest) in FR end.
    apply rw_cells_app in FR. destruct FR as [FRlo FR]. apply rw_cells_app in FR. destruct FR as [FROUT FRhi].
    cbn [cells_size Nat.add] in FROUT, FRhi. rewrite E0, E1, E2, E3, E4, E5, E6, E7, E8 in FROUT, FRhi. cbn [csize Nat.add] in FROUT, FRhi.
    replace (e_SP E + Z.of_nat 72)%Z with (bv_unsigned (e_sp E) + -296)%Z in * by lia.
    replace (bv_unsigned (e_sp E) + -296 + Z.of_nat 8)%Z with (bv_unsigned (e_sp E) + -288)%Z in * by lia.
    unfold numwu_stmt_g in HS.
    eapply evt_cut.
    { eapply HS with (A := e_BUF E) (off := off) (stop := e_len E) (OUT := (bv_unsigned (e_sp E) + -296)%Z) (lo := e_lo E)
                     (txt := padded_bytes bs) (b := Z_to_bv 8 (B bs (e_len E))) (junk := j72);
        rewrite ?(u64_small (e_SP E)) by lia;
        [ exact MI | exact FRM | exact ST | unfold NUMU_STACK; lia | lia | s2_unhide; lia | exact BUFRO | lia | lia | lia | lia
        | apply nth_error_padded; lia
        | rewrite (B_pad bs (e_len E)) by lia; reflexivity
        | exact FROUT | lia | s2_unhide; lia ]. }
    cbv beta. intros ms' P. unfold numwu_post_g in P.
    destruct P as (q5 & q6 & q7 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & F' & fc' & m' & v & flag & -> & FRM' & MUc & WMc & MIc & OUTc & STc).
    rewrite ?(u64_small (e_SP E)) in MUc, STc by lia. unfold NUMU_STACK in MUc.
    clear FROUT.
    transport_after_call usegs m1 m' MUc WMc.
    clear MUc WMc HS MI FRM.
    replace (ret_pc (Z_to_bv 64 RA)) with (Z_to_bv 64 RA) by (symmetry; apply ret_pc_even; [lia | exact HRA2]).
    eapply (K flag v).
    unfold MEMI. split; [exact FRM'|]. split.
    { change ([c0; c1; c2; c3; c4; c5; c6; c7; c8; C8 v] ++ frame_hi E) with ([c0; c1; c2; c3; c4; c5; c6; c7; c8] ++ [C8 v] ++ frame_hi E).
      apply rw_cells_app; split; [exact FRlo | apply rw_cells_app; split].
      - cbn [cells_size Nat.add]. rewrite E0, E1, E2, E3, E4, E5, E6, E7, E8. cbn [Nat.add].
        replace (e_SP E + Z.of_nat 72)%Z with (bv_unsigned (e_sp E) + -296)%Z by lia. exact OUTc.
      - cbn [cells_size Nat.add]. rewrite E0, E1, E2, E3, E4, E5, E6, E7, E8. cbn [csize Nat.add].
        replace (e_SP E + Z.of_nat 72 + Z.of_nat 8)%Z with (bv_unsigned (e_sp E) + -288)%Z by lia. unfold frame_hi. exact FRhi. }
    unfold impl_cells, doc_cells, s2_W.
    split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
    split; [eexists; split; [eassumption | split; eassumption]|].
    split; [eexists; split; [eassumption | split; eassumption]|].
    split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; eassumption.
  Qed.

  Ltac n_close := unfold NSL; s2_close_mem0.
  Local Ltac n_closed_branch a b ::=
    lazymatch a with 0x48e00%Z => if_false | 0x48e58%Z => first [if_true | if_false] | 0x48de0%Z => first [if_true | if_false] end.
  Ltac fin6 sv KX KC :=
    lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
      lazymatch pc with
      | 0x4ed1c%Z => s2_tape2; s2_kvr KC; [s2_num_word|]; cbn [k depth W sb scopes];
                     repeat match goal with H : rw_cells _ _ _ _ |- _ =>
                       progress (replace (e_TAPE E + 8 * W sv + 16)%Z with (e_TAPE E + 8 * (W sv + 2))%Z in H by lia) end;
                     s2_close_forget; [eassumption | eassumption | eassumption | eassumption | forgets_tac]
      | 0x4bfd0%Z =>
          eapply KX; [s2_errok_code | s2_close_memx]
      end end.
  Ltac cuts6 pc := lazymatch pc with 0x4ed1c%Z => fail | 0x4bfd0%Z => fail | 0x48d7c%Z => fail | _ => idtac end.

  Lemma seg_numa_slow : forall (Q : machine_state -> Prop) (s : st) neg,
    (0 <= k s <= e_n E)%Z -> (0 <= W s)%Z -> (W s + 2 <= e_tcap E)%Z -> Z.of_nat (length (e_tws E)) = W s -> exit_k E Q ->
    (forall v r, num_word v -> arrcont_k (gapp E [v; r] []) Q (mkst (k s + 1) (depth s) (W s + 2) (sb s) (scopes s))) ->
    numa_tailm_k E Q s neg 0x48cbc.
  Proof using OK HSLOWF HROOM.
    intros Q s neg HK HW0 HW GLT KX KC. unfold numa_tailm_k. intros until m1. intros HM.
    pose proof (off_range _ _ (ok_s1 _ OK) (k s) HK) as HOR.
    s2_env OK. unfold NSL in HM. unfold NUMU_STACK in HROOM.
    s2_open_mem HM.
    ngrun_to 0x5edf4%Z.
    eapply (numa_call Q 0x5edf4 9 0 0x48cc8 (o s)); cycle 13; [n_close | | exact HSLOWF | lia | reflexivity | lia | reflexivity ..].
    intros flag v yt0 yt1 yt2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 F' fc' m' HM'.
    clear - OK KX KC HM' HW0 HW GLT. s2_env OK. s2_open_mem HM'.
    destruct flag; ngexp cuts6 ltac:(idtac; fin6 s KX KC).
  Qed.

  Lemma seg_numa_fb : forall (Q : machine_state -> Prop) (s : st) neg,
    (0 <= k s <= e_n E)%Z -> exit_k E Q ->
    numa_tailm_k E Q s neg 0x48d7c ->
    numa_tailm_k E Q s neg 0x48f80.
  Proof using OK HPFF HROOM.
    intros Q s neg HK KX KW. unfold numa_tailm_k. intros until m1. intros HM.
    pose proof (off_range _ _ (ok_s1 _ OK) (k s) HK) as HOR.
    s2_env OK. unfold NSL in HM. unfold NUMU_STACK in HROOM.
    s2_open_mem HM.
    ngrun_to 0x5eea4%Z.
    eapply (numa_call Q 0x5eea4 0 1 0x48f8c (o s)); cycle 13; [n_close | | exact HPFF | lia | reflexivity | lia | reflexivity ..].
    intros flag v yt0 yt1 yt2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 F' fc' m' HM'.
    clear - OK KX KW HM'. s2_env OK. s2_open_mem HM'.
    destruct flag.
    -
      ngrun. if_true. ngexp cuts6 ltac:(idtac; fin6 s KX KX).
    - ngrun. if_false. ngrun_to 0x48d7c%Z.
      eapply KW. eapply MEMI_NSL; [s2_close_mem0 | reflexivity ..].
  Qed.
End NumA6.
