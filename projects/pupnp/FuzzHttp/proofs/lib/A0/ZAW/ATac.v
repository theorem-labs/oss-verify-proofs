(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac STRW_merge Image.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts.
Import ListNotations.
Open Scope Z_scope.

Ltac lit_branch :=
  lazymatch goal with |- evt _ _ (MS _ _ (if ?c then ?a else ?b) _ _ _ _) =>
    first [ replace (if c then a else b) with a by (vm_compute; reflexivity)
          | replace (if c then a else b) with b by (vm_compute; reflexivity) ] end.

Ltac lit_store_fix :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) =>
      lazymatch z with
      | Zneg _ => let b := eval vm_compute in (Z.modulo z 256) in
                  rewrite (STRW_merge.le1_lit_of_mod8 z (Z_to_bv 8 b)) by (vm_compute; reflexivity); mem_after_store
      | _ => fix_lit_store end
  | _ => fix_lit_store
  end.
Ltac sstep := step; lit_store_fix.

Ltac split_chunk FR n H1 H2 :=
  lazymatch type of FR with rw_cells ?segs ?m ?A ?cs =>
    let cs1 := eval cbv beta iota delta [firstn skipn] in (firstn n cs) in
    let cs2 := eval cbv beta iota delta [firstn skipn] in (skipn n cs) in
    change (rw_cells segs m A (cs1 ++ cs2)) in FR;
    destruct (proj1 (rw_cells_app segs m A cs1 cs2) FR) as [H1 H2]; clear FR;
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul] in H2;
    try (lazymatch type of H2 with rw_cells _ _ (?a + ?b + ?c)%Z _ =>
           let v := eval vm_compute in (b + c)%Z in replace (a + b + c)%Z with (a + v)%Z in H2 by lia end)
  end.

Ltac join_chunks H1 H2 H :=
  lazymatch type of H1 with rw_cells ?segs ?m ?A ?cs1 =>
  lazymatch type of H2 with rw_cells _ _ ?A2 ?cs2 =>
    pose proof (proj2 (rw_cells_app segs m A cs1 cs2)) as H;
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul] in H;
    lazymatch type of H with rw_cells _ _ _ _ /\ rw_cells _ _ ?A2' _ -> _ =>
      replace A2' with A2 in H by lia end;
    specialize (H (conj H1 H2)); clear H1 H2; cbn [app] in H
  end end.

Ltac solve_in_live :=
  lazymatch goal with |- in_live ?FI ?st ?A ?n =>
    unfold in_live;
    match goal with
    | L : lb (fs_live FI st) ?A0 ?n0 |- _ => left; apply (lb_sub _ A0 n0 A n L); simpl_sizes; lia
    | L : ls (fs_live FI st) ?A0 ?n0 |- _ => right; left; apply (ls_sub _ A0 n0 A n L); simpl_sizes; lia
    | L : lf (fs_live FI st) A |- _ => right; right; split; [exact L| simpl_sizes; lia]
    end
  end.

Lemma disjoint_from_sub : forall W A0 n0 A n, disjoint_from W A0 n0 -> A0 <= A -> A + n <= A0 + n0 -> disjoint_from W A n.
Proof. induction W as [|[lo hi] W IH]; cbn; intros A0 n0 A n H H1 H2; [exact I|]. destruct H as [H3 H4]. split; [lia| eauto]. Qed.

Ltac dj_rec :=
  first [ exact I | assumption
        | lazymatch goal with |- _ /\ _ => split; [dj_rec | dj_rec] end
        | lia
        | match goal with D : disjoint_from ?W ?A0 ?n0 |- disjoint_from ?W ?A ?n => apply (disjoint_from_sub W A0 n0 A n D); lia end ].
Ltac dj_solve := cbn [disjoint_from]; simpl_sizes; try simpl_arr_sizes; dj_rec.
Ltac clear_other_disj Hi :=
  repeat match goal with H : _ \/ _ |- _ => tryif constr_eq H Hi then fail else clear H end.
Ltac disj_from_hyps :=
  match goal with
  | Hi : _ \/ _ |- _ \/ _ => clear_other_disj Hi; destruct Hi; [ left; lia | right; lia ]
  end.
Ltac sub_fp_solve :=
  unfold sub_fp; cbn [outside]; let xo := fresh "xo" in let Ho := fresh "Ho" in intros xo Ho; destruct_ands Ho;
  repeat split; first [ exact I | assumption | disj_from_hyps | lia ].

Ltac transport_after_call_fk segs m m' MU WM :=
  let W := lazymatch type of MU with munch ?W _ _ => W end in
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_transport segs W m m' A2 bs2) in H; [ | exact MU | dj_solve ]
            | lazymatch goal with FK : fkeep ?FI ?Wc ?st m m' |- _ =>
                apply (bytes_at_fkeep FI Wc st m m' A2 bs2) in H; [ | exact FK | solve_in_live | dj_solve ] end
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_transport segs m m' A2 n2) in H; [ | exact WM ]
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact WM | dj_solve ]
            | lazymatch goal with FK : fkeep ?FI ?Wc ?st m m' |- _ =>
                apply (rw_cells_fkeep FI Wc st m m' A2 cs2) in H; [ | exact FK | exact WM | solve_in_live | dj_solve ] end
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (ro_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | dj_solve ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      first [ apply (u8arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | dj_solve ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u32arr segs m ?A2 ?xs |- _ =>
      first [ apply (u32arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | dj_solve ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u64arr segs m ?A2 ?xs |- _ =>
      first [ apply (u64arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | dj_solve ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8ro segs m ?A2 ?xs |- _ =>
      first [ apply (u8ro_transport segs W m m' A2 xs) in H; [ | exact MU | dj_solve ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_transport_disjoint segs W m m' loq hiq) in H; [ | exact MU | exact WM | dj_solve ]
            | clear H ]
  | H : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_trans Wq mq m m') in H; [ | eapply (munch_weaken W Wq m m'); [ sub_fp_solve | exact MU ] ]
            | fail 100 "callee footprint not inside caller footprint" ]
  | H : wmono segs ?mq m |- _ => apply (wmono_trans segs mq m m') in H; [ | exact WM ]
  end.

Ltac post_call segs m ::=
  let ms' := fresh "ms'" in let PO := fresh "POST" in
  intros ms' PO;
  destruct_exs PO;
  let E := fresh "E" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MI" in
  destruct PO as [E [MUc [WMc PO]]];
  first [ destruct PO as [MIc PO] | rename PO into MIc ];
  subst ms';
  try destruct_ands PO;
  lazymatch type of MUc with
  | munch _ m ?m' =>
      transport_after_call_fk segs m m' MUc WMc;
      clear MUc WMc;
      try match goal with H : mem_inv segs m |- _ => clear H end;
      repeat match goal with H : RFAKE _ _ m |- _ => clear H end;
      try clear m
  end;

  try (lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end).

Ltac fs_interval_ok :=
  first [
          match goal with NFK : forall W A n, _ -> fk_ok ?FI W ?st (A, A + n) |- fk_ok ?FI _ ?st (?A, ?B) =>
            replace B with (A + (B - A)) by lia; apply NFK; cbn [FB_of SB_of]; lia end
        | unfold fk_ok; cbn [fst snd];
          first [ left; cbn [inside]; lia
                | right; left; lia ]
        | cbn [fst snd];
          first [ left; lia
                | right; left; match goal with L : lb ?Lv ?A0 ?n0 |- lb ?Lv _ _ => apply (lb_sub _ A0 n0 _ _ L); lia end
                | right; right; match goal with L : ls ?Lv ?A0 ?n0 |- ls ?Lv _ _ => apply (ls_sub _ A0 n0 _ _ L); lia end   ] ].
Ltac fk_forall := repeat (apply Forall_cons; [fs_interval_ok|]); apply Forall_nil.

Ltac in_live_update_with E :=
  let SUB := lazymatch type of E with
             | ?L' = ?g0 :: ?L => constr:(sub_cons L L' g0 E)
             | ?L' = ?L => constr:(sub_eq L L' E) end in
  lazymatch type of E with ?L' = _ =>
  let L := lazymatch type of E with _ = _ :: ?L => L | _ = ?L => L end in
  repeat match goal with
  | H : lb L ?A ?n |- _ => apply (fun HH => lb_mono L L' A n HH SUB) in H
  | H : ls L ?A ?n |- _ => apply (fun HH => ls_mono L L' A n HH SUB) in H
  | H : lf L ?A |- _ => apply (fun HH => lf_mono L L' A HH SUB) in H
  end end.

Ltac fk_sync FI RF MU0 FK LSUB :=
  lazymatch type of MU0 with munch ?Ws ?ma ?mb =>
  lazymatch type of RF with RFAKE _ ?st ma =>
  lazymatch type of FK with fkeep _ ?Wt ?st0 ?me ma =>
      let FK' := fresh "FK" in
      assert (FK' : fkeep FI Wt st0 me mb);
      [ eapply (fkeep_trans FI Wt st0 me ma mb FK); eapply (fkeep_of_munch FI Wt Ws st0 st ma ma mb RF LSUB MU0);
        unfold ff_size, ff_shsize; cbn [FB_of SB_of]; fk_forall
      | clear FK; rename FK' into FK ]
  end end end.

Ltac fsenv_interval_ok :=
  unfold fsenv_cls; cbn [fst snd];
  first [ left; lia | right; left; lia | right; right; left; lia
        | right; right; right; split; [lia| split; [lia| unfold env_safe; apply Forall_cons; [cbn [fst snd]; lia| apply Forall_nil]]] ].
Ltac fe_sync FI MU0 :=
  lazymatch type of MU0 with munch ?Ws ?ma ?mb =>
    match goal with
    | FE : FSENV FI ma |- _ =>
        let FE' := fresh "FE" in
        first [ assert (FE' : FSENV FI mb) by (eapply (fsenv_frame FI ma mb Ws FE MU0); repeat (apply Forall_cons; [fsenv_interval_ok|]); apply Forall_nil);
                clear FE; rename FE' into FE
              | idtac "note: fe_sync drops" FE "(an interval of the footprint is outside fsenv_cls)"; clear FE ]
    | _ => idtac
    end end.
Ltac rf_sync FI RF MU0 WM0 :=
  fe_sync FI MU0;
  lazymatch type of MU0 with munch ?Ws ?ma ?mb =>
  lazymatch type of RF with RFAKE _ ?st ma =>
      let RF' := fresh "RF" in
      assert (RF' : RFAKE FI st mb);
      [ eapply (rfake_frame FI st ma mb Ws RF MU0 WM0); unfold ff_size, ff_shsize; cbn [FB_of SB_of]; fk_forall
      | clear RF MU0 WM0; rename RF' into RF ]
  end end.
Ltac fs_sync FI RF MU0 WM0 FK LSUB := fk_sync FI RF MU0 FK LSUB; rf_sync FI RF MU0 WM0.

Ltac env_sync AE MU0 WM0 :=
  lazymatch type of MU0 with munch ?Ws ?ma ?mb =>
    let AE' := fresh "AE" in
    assert (AE' : asan_env asegs mb) by (eapply (asan_env_frame asegs ma mb Ws AE MU0 WM0); unfold env_safe; repeat (apply Forall_cons; [cbn [fst snd]; lia|]); apply Forall_nil);
    clear AE; rename AE' into AE end.

Ltac ag_split AG := let G1 := fresh "AG" in let G2 := fresh "AG" in let G3 := fresh "AG" in let G4 := fresh "AG" in
  destruct AG as (G1 & G2 & G3 & G4); unfold A0_GOT_SHADOW, A0_SHADOW_CELL, A0_GOT_UAR, A0_UAR_CELL, SHADOW_OFF in G1, G2, G3, G4.
Ltac ag_solve := unfold asan_globals, A0_GOT_SHADOW, A0_SHADOW_CELL, A0_GOT_UAR, A0_UAR_CELL, SHADOW_OFF;
  repeat match goal with |- _ /\ _ => split end; assumption.

Ltac fs_after_call FI FK FKc LSUB E Ws :=
  lazymatch type of FK with fkeep _ ?Wt ?st0 ?me ?ma =>
  lazymatch type of FKc with fkeep _ ?Wc ?st ma ?mb =>
      let FK' := fresh "FK" in
      assert (FK' : fkeep FI Wt st0 me mb);
      [ eapply (fkeep_trans FI Wt st0 me ma mb FK); eapply (fkeep_weaken FI Wc Wt st st0 ma mb FKc);
        [ sub_fp_solve | exact LSUB ]
      | clear FK FKc; rename FK' into FK;

        lazymatch type of E with
        | fs_live FI ?stn = ?g0 :: fs_live FI st =>
            let L' := fresh "LSUB" in
            assert (L' : forall g, In g (fs_live FI st0) -> In g (fs_live FI stn)) by (intros g Hg; rewrite E; right; exact (LSUB g Hg));
            clear LSUB; rename L' into LSUB; in_live_update_with E
        | fs_live FI ?stn = fs_live FI st =>
            let L' := fresh "LSUB" in
            assert (L' : forall g, In g (fs_live FI st0) -> In g (fs_live FI stn)) by (intros g Hg; rewrite E; exact (LSUB g Hg));
            clear LSUB; rename L' into LSUB; in_live_update_with E
        end;
        pose proof (munch_refl Ws mb) as MU0; pose proof (wmono_refl asegs mb) as WM0 ]
  end end.
