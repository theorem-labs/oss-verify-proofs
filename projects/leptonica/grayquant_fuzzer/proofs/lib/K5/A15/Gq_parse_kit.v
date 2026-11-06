(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Image.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import ImageA.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import Layout.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_lits Lept_env LeptC_kit Lept_chain Lept_leaf Lept_objkit D_iface D_defs
  Gq_numa Gq_gaps Gq_iface Gq_thr_iface.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition EDGE_STR : list Z := [52; 53; 32; 55; 53; 32; 49; 49; 53; 32; 49; 56; 53].   (* [comment removed for export] *)
Definition str_cells (bs : list Z) : list cell := map (fun b => C1 (Z_to_bv 8 b)) bs.

(* [comment removed for export] *)
Lemma edge_lit_bytes : forall m : mem, mem_inv asegs m ->
  bytes_at asegs m LIT_EDGEVALS (map (Z_to_bv 8) EDGE_STR ++ Z_to_bv 8 0 :: [Z_to_bv 8 0; Z_to_bv 8 0]).
Proof.
  intros m MI. apply ro_bytes_at; [exact MI | unfold LIT_EDGEVALS; lia | unfold LIT_EDGEVALS; cbn; lia
                                  | apply Image.ro_bytes_b_sound; vm_compute; reflexivity].
Qed.
Lemma edge_lit_cells : forall m : mem, mem_inv asegs m -> ro_cells asegs m LIT_EDGEVALS (str_cells (EDGE_STR ++ [0])).
Proof.
  intros m MI. split; [cbn; tauto|].
  apply ro_bytes_at; [exact MI | unfold LIT_EDGEVALS; lia | unfold LIT_EDGEVALS; cbn; lia | apply Image.ro_bytes_b_sound; vm_compute; reflexivity].
Qed.
Lemma edge_str_nz : ~ In (Z_to_bv 8 0) (map (Z_to_bv 8) EDGE_STR).
Proof.
  intros H. cbn [EDGE_STR map In] in H.
  repeat (destruct H as [H|H]; [apply (f_equal bv_unsigned) in H; vm_compute in H; discriminate H|]). exact H.
Qed.
Lemma edge_lit_in : In (LIT_EDGEVALS, 14) LEPT_LITS.
Proof. unfold LEPT_LITS, LIT_EDGEVALS. cbn [In]. repeat (first [left; reflexivity | right]). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac shk_reaim :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (if ?c then Z_to_bv 64 ?SLOW else Z_to_bv 64 ?FAST) ?fc ?rv ?m ?ro) =>
      let b := shbyte_of c in
      lazymatch goal with
      | K : shk m b ?X |- _ =>
          instr_at segs SLOW ltac:(fun i =>
            lazymatch i with
            | OpImm ALU_AND ?ru ?rs _ =>
                reg_val rs ltac:(fun v =>
                  lazymatch v with
                  | Z_to_bv 64 ?A => change (shk m b A) in K
                  end)
            end)
      end
  end.
Ltac pwalk1 :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => first [ awalk1 | shk_reaim; shbr ]
  | |- _ => awalk1
  end.
Ltac pwalk stops := repeat (tryif at_stop stops then fail else pwalk1).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac own_cur RT tl ff kf :=
  try (lazymatch goal with OWNx : accok _ _ _ tl 8 |- _ => clear OWNx end);
  lazymatch goal with
  | OWN0x : hid (accok ?lv ?frs ?m0 tl 8), AGFx : agree_on ?P ?m0 ?m1, FINx : In (ff, kf) ?frs |- cps _ (ASTA RT ?S _ _) _ =>
      let N := fresh "OWN" in
      assert (N : accok (rt_live RT S) (rt_frames RT S) m1 tl 8)
        by (unfold hid in OWN0x;
            apply (accok_mono lv frs (rt_live RT S) (rt_frames RT S) m1 tl 8);
            [ apply (accok_keep_P lv frs m0 m1 P tl 8 OWN0x AGFx ltac:(lia));
              let zx := fresh "zx" in let Hzx := fresh "Hzx" in intros zx Hzx;
              change ((8 + 7) / 8) with 1 in Hzx;
              split; [ right; right; right; right; exists ff, kf; split; [exact FINx|];
                       unfold shad, SHB in *; Z.div_mod_to_equations; lia
                     | cbn [outside]; split; [unfold shad, SHB in *; Z.div_mod_to_equations; lia | exact I] ]
            | first [solve [live_sub_tac] | solve [live_add_tac]]
            | solve [frames_sub_tac] ])
  end.
(* [comment removed for export] *)
Ltac tok_ivt tl :=
  cbn [ivls_client]; repeat split; try exact I;
  let zz := fresh "zz" in let Hzz := fresh "Hzz" in
  intros zz Hzz;
  first [ left; ul
        | lazymatch goal with OWNx : accok _ _ _ tl 8 |- aclient _ _ ?spx _ =>
            first [ exact (accok_aclient _ _ _ spx tl 8 zz OWNx ltac:(lia))
                  | apply (aclient_mono _ _ spx _ _ spx zz (accok_aclient _ _ _ spx tl 8 zz OWNx ltac:(lia)));
                    [ first [solve [live_sub_tac] | solve [live_add_tac]] | solve [frames_sub_tac] | lia ] ] end
        | lazymatch type of Hzz with (?p <= _ < ?p + ?n)%Z => right; right; left; exists p, n; split; [solve [in_live_tac] | lia] end ].
Ltac tok_pft PFS Hx :=
  cbn [outside]; pose proof (PFS _ Hx);
  try (lazymatch goal with NCAx : forall a, _ a -> (a < ?p \/ ?p + _ <= a)%Z |- _ => pose proof (NCAx _ Hx) end);
  let Ho := fresh "Ho" in destruct Hx as [Hx Ho]; cbn [outside] in Ho; repeat split; first [exact I | lia].
(* [comment removed for export] *)
Ltac tok_stops k := k (0x50e84 :: 0x6205c :: 0x90e84 :: 0x90c20 :: 0x60ce0 :: 0x68c98 :: 0x68978 :: 0x68ab8 :: 0x68e78 :: 0x68b58 :: @nil Z)%Z.
(* [comment removed for export] *)
Ltac schr RT AF GP GG MST lo usp tl ff kf PFS stops :=
  at_call RT AF ltac:(tok_ivt tl) ltac:(fun Hx => tok_pft PFS Hx);
  eapply cps_seq;
  [ let SC := fresh "SC" in
    pose proof (gg_strchr RT GG) as SC; unfold strchr_seps_icontract in SC; eapply SC with (lo := lo); rt_side ltac:(lia)
  | ];
  after_call RT AF;
  fold_ag ltac:(fun Hx => let Ho := fresh "Ho" in destruct Hx as [Hx Ho]; split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [first [solve [live_sub_tac] | solve [live_add_tac]]| solve [frames_sub_tac]| lia]| lia]);
  repeat match goal with |- context [strchr_seps ?c] => let v := eval vm_compute in (strchr_seps c) in change (strchr_seps c) with v end;
  own_cur RT tl ff kf;
  refresh RT AF; lib_refresh RT GP; unfold shad, SHB in *; unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *;
  walk_to AF MST [(usp - 96, usp); (tl, tl + 8)] stops; pwalk stops.
(* [comment removed for export] *)
Ltac schrs RT AF GP GG MST lo usp tl ff kf PFS stops :=
  repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 0x50e84) _ _ _ _) => idtac end;
          schr RT AF GP GG MST lo usp tl ff kf PFS stops).

(* [comment removed for export] *)
Ltac ppc := lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC:" pc | |- cps _ (ASTA _ _ _ (eq (MS _ _ ?pc _ _ _ _))) _ => idtac "CPS-PC:" pc | |- _ => idtac "(no machine state in the goal)" end.
