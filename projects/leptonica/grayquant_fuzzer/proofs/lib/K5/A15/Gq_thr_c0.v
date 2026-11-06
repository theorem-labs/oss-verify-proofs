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
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import ImageA.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Malloc Require Import MallocKit_AB.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import Layout.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_lits Lept_litmem Lept_env LeptC_kit Lept_leaf Lept_chain LeptC_leaf Lept_objkit LeptL_kit Lept_gmax_defs Lept_fuzzkit
  Gm_iface Gq_iface Gq_cmap_iface Gq_thr_iface Gq_thr2_iface Gm_kit Gm_leaf Gm_livekit Gm_livekit2 Gq_fzkit Gq_opcase Gq_numa Numa_kit Ed_fp Gq_thr_loop Gq_thr_exit.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
(* [comment removed for export] *)
Ltac subfp_tac ::= clear; let z := fresh "z" in let Hz := fresh "Hz" in intros z Hz; cbn [outside] in Hz |- *; cbn [outside]; lia.

(* [comment removed for export] *)
Lemma cps_ASTA_ret : forall (RT : rt_sig) (Σ : rts RT) (PMc : Model -> Prop)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v : word) (Φ : mem -> Prop) (Q : config -> Prop),
  (forall (x : mem) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : word) (x14 : bvmap 5 word) (x15 : bv 32), Φ x ->
     cps asegs (ASTA RT Σ PMc (eq (MS (mkR ra sp gp tp x0 x1 x2 s0 s1 v x3 x4 x5 x6 x7 x8 x9 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x10 x11 x12 x13)
                                       x14 (ret_pc ra) (frm_clear x15) None x (seg_rom asegs)))) Q) ->
  cps asegs (ASTA RT Σ PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms /\ Φ m')) Q.
Proof.
  intros RT Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v Φ Q H.
  apply (cps_ASTA_ex RT); intros m'. apply (cps_ASTA_pure_r RT); intros HΦ. unfold ret_st.
  do 16 (apply (cps_ASTA_ex RT); intros ?). apply (cps_ASTA_eq_sym RT). apply H. exact HΦ.
Qed.
(* [comment removed for export] *)
Lemma cps_ASTA_ret0 : forall (RT : rt_sig) (Σ : rts RT) (PMc : Model -> Prop)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v : word) (Q : config -> Prop),
  (forall (x : mem) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : word) (x14 : bvmap 5 word) (x15 : bv 32),
     cps asegs (ASTA RT Σ PMc (eq (MS (mkR ra sp gp tp x0 x1 x2 s0 s1 v x3 x4 x5 x6 x7 x8 x9 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x10 x11 x12 x13)
                                       x14 (ret_pc ra) (frm_clear x15) None x (seg_rom asegs)))) Q) ->
  cps asegs (ASTA RT Σ PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms)) Q.
Proof.
  intros RT Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v Q H.
  apply (cps_ASTA_ex RT); intros m'. unfold ret_st.
  do 16 (apply (cps_ASTA_ex RT); intros ?). apply (cps_ASTA_eq_sym RT). apply H.
Qed.
(* [comment removed for export] *)
Ltac cps_open RT ::=
  unfold malloc_post, free_post, icpt_post;
  repeat first [ apply cps_ex_l; intro | apply cps_and_pure_r; intro ];
  first [ apply (cps_ASTA_ret RT); intros
        | apply (cps_ASTA_ret0 RT); intros
        | unfold ret_st; repeat (cps_open1 RT) ].

(* [comment removed for export] *)
Lemma open_post1 : forall {A} (P : A -> config -> Prop) (Ψ : A -> Prop) (Q : config -> Prop),
  (forall x, Ψ x -> cps asegs (P x) Q) -> cps asegs (fun cf => exists x, P x cf /\ Ψ x) Q.
Proof. intros A P Ψ Q H. apply cps_ex_l; intros a. apply cps_and_pure_r; intros HΨ. exact (H a HΨ). Qed.
Lemma open_post2 : forall {A B} (P : A -> B -> config -> Prop) (Ψ : A -> B -> Prop) (Q : config -> Prop),
  (forall (x : A) (x0 : B), Ψ x x0 -> cps asegs (P x x0) Q) -> cps asegs (fun cf => exists x x0, P x x0 cf /\ Ψ x x0) Q.
Proof. intros A B P Ψ Q H. apply cps_ex_l; intros a. apply cps_ex_l; intros b. apply cps_and_pure_r; intros HΨ. exact (H a b HΨ). Qed.
Lemma open_post3 : forall {A B C} (P : A -> B -> C -> config -> Prop) (Ψ : A -> B -> C -> Prop) (Q : config -> Prop),
  (forall (x : A) (x0 : B) (x1 : C), Ψ x x0 x1 -> cps asegs (P x x0 x1) Q) -> cps asegs (fun cf => exists x x0 x1, P x x0 x1 cf /\ Ψ x x0 x1) Q.
Proof. intros A B C P Ψ Q H. do 3 (apply cps_ex_l; intros ?). apply cps_and_pure_r; intros HΨ. apply H. exact HΨ. Qed.
Lemma open_post4 : forall {A B C D} (P : A -> B -> C -> D -> config -> Prop) (Ψ : A -> B -> C -> D -> Prop) (Q : config -> Prop),
  (forall (x : A) (x0 : B) (x1 : C) (x2 : D), Ψ x x0 x1 x2 -> cps asegs (P x x0 x1 x2) Q) ->
  cps asegs (fun cf => exists x x0 x1 x2, P x x0 x1 x2 cf /\ Ψ x x0 x1 x2) Q.
Proof. intros A B C D P Ψ Q H. do 4 (apply cps_ex_l; intros ?). apply cps_and_pure_r; intros HΨ. apply H. exact HΨ. Qed.
Ltac cps_open RT ::=
  unfold malloc_post, free_post, icpt_post;
  first [ apply open_post4; do 5 intro | apply open_post3; do 4 intro | apply open_post2; do 3 intro | apply open_post1; do 2 intro | idtac ];
  repeat first [ apply cps_ex_l; intro | apply cps_and_pure_r; intro ];
  first [ apply (cps_ASTA_ret RT); intros
        | apply (cps_ASTA_ret0 RT); intros
        | unfold ret_st; repeat (cps_open1 RT) ].


(* [comment removed for export] *)
Ltac apart2 RT AF NAME p n q k NE :=
  lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ =>
    assert (NAME : p + n <= q \/ q + k <= p)
      by (apply (live_apart2 RT AF S mm p n q k A);
          [ solve [in_live_tac] | solve [in_live_tac] | let E := fresh in intro E; injection E; intros; apply NE; congruence ])
  end.
(* [comment removed for export] *)
Ltac join_cells H1 H2 :=
  lazymatch type of H1 with rw_cells _ ?m ?A ?cs1 =>
  lazymatch type of H2 with rw_cells _ ?m ?B ?cs2 =>
    let J := fresh "J" in
    assert (J : rw_cells asegs m A (cs1 ++ cs2))
      by (apply (proj2 (rw_cells_app m A cs1 cs2)); split;
          [ exact H1
          | cbn [cells_size csize Nat.add]; lazymatch goal with |- rw_cells _ _ ?X _ => replace X with B by (clear; lia) end; exact H2 ]);
    clear H1 H2; cbn [app] in J; rename J into H1 end end.

(* [comment removed for export] *)
Ltac ctx_gc RT :=
  lazymatch goal with
  | |- cps _ (ASTA RT ?S _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
      repeat match goal with
      | H : ART RT _ ?m' |- _ => tryif constr_eq m' mc then fail else clear H
      | H : mem_inv asegs ?m' |- _ => tryif constr_eq m' mc then fail else clear H
      | H : stk asegs ?m' _ _ |- _ => tryif constr_eq m' mc then fail else clear H
      | H : LIBH ?m' |- _ => tryif constr_eq m' mc then fail else clear H
      | H : io_ssp ?m' |- _ => tryif constr_eq m' mc then fail else clear H
      | H : acc asegs ?m' _ _ |- _ => tryif constr_eq m' mc then fail else clear H
      | H : wmono asegs _ _ |- _ => clear H
      | H : True |- _ => clear H
      end;
      repeat match goal with x : word |- _ => clear x end;
      repeat match goal with x : bvmap 5 word |- _ => clear x end;
      repeat match goal with x : bv 32 |- _ => clear x end;
      repeat match goal with x : list byte |- _ => clear x end;
      repeat match goal with x : mem |- _ => clear x end
  end.

(* [comment removed for export] *)
Ltac sigma_gc RT S0 Sx :=
  repeat match goal with S : rts RT |- _ =>
    tryif constr_eq S S0 then fail else tryif constr_eq S Sx then fail else
      (repeat match goal with H : context [S] |- _ => clear H end; clear S) end.
(* [comment removed for export] *)
Ltac park_ne := repeat match goal with H : (?a <> ?b) |- _ => lazymatch type of a with Z => change (a <> b) with (parked (a <> b)) in H end end.
Definition osd_keep (P : Prop) : Prop := P.
Definition osd_strict : Prop := True.
Ltac osd_has T := match goal with _ : osd_keep T |- _ => idtac end.
Ltac osd_mark H :=
  lazymatch type of H with ?T =>
    tryif osd_has T then idtac else (let K := fresh "OSD" in pose proof H as K; change T with (osd_keep T) in K) end.
Ltac osd_mark_about t :=
  repeat match goal with H : ?T |- _ =>
    lazymatch T with
    | osd_keep _ => fail
    | hid _ => fail
    | context [asegs] => fail
    | context [@In] => fail
    | context [rt_live] => fail
    | context [t] => lazymatch type of T with Prop => tryif osd_has T then fail else (let K := fresh "OSD" in pose proof H as K; change T with (osd_keep T) in K) end
    end end.
Ltac osd_clear := repeat match goal with H : osd_keep _ |- _ => clear H | H : osd_strict |- _ => clear H end.
(* [comment removed for export] *)
Ltac osd_prune :=
  repeat match goal with H : ?T |- _ =>
    lazymatch T with
    | osd_keep _ => fail
    | _ => lazymatch type of T with Prop => clear H end
    end end;
  repeat match goal with H : osd_keep ?T |- _ => change (osd_keep T) with T in H; try unfold parked in H end.
Ltac osd_lia := zn_lits; unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, shad, SHB in *; first [lia | Z.div_mod_to_equations; lia].
(* [comment removed for export] *)
Ltac osd_is_strict := lazymatch goal with _ : osd_strict |- _ => idtac end.
Ltac outside_side ::=
  cbn [outside];
  tryif osd_is_strict then
    first [ exact I
          | lazymatch goal with Hx : (_ <= ?x < _)%Z |- _ => revert Hx end;
            osd_prune; intros ?Hx; repeat split; osd_lia ]
  else
  first [ exact I
        | lazymatch goal with _ : osd_keep _ |- _ => idtac end;
          lazymatch goal with Hx : (_ <= ?x < _)%Z |- _ => revert Hx end;
          osd_prune; intros ?Hx; repeat split; osd_lia
        | repeat split; notin_side ].
Ltac static_in_P ::=
  let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
  first [ right; left; exact Ha
        | split; [ right; left; exact Ha
                 | tryif osd_is_strict then
                     first [ cbn [outside]; exact I
                           | cbn [outside]; generalize (client_static_below a Ha); generalize (client_static_ge a Ha);
                             osd_prune; intros ?Hb ?Hc; repeat split; osd_lia ]
                   else
                   first [ cbn [outside]; exact I
                         | lazymatch goal with _ : osd_keep _ |- _ => idtac end;
                           cbn [outside]; generalize (client_static_below a Ha); generalize (client_static_ge a Ha);
                           osd_prune; intros ?Hb ?Hc; repeat split; osd_lia
                         | let Hc := fresh in intros Hc;
                           pose proof (client_static_below a Ha); pose proof (client_static_ge a Ha); unfold SEGTOP_A in *; first [ lia | tlia ]
                         | cbn [outside]; pose proof (client_static_below a Ha); pose proof (client_static_ge a Ha);
                           unfold SEGTOP_A in *; repeat split; tlia ] ] ].
(* [comment removed for export] *)
Ltac fix_ret_pc ::=
  repeat match goal with
  | |- context [ret_pc (Z_to_bv 64 ?z)] => rewrite (ret_pc_even z) by (clear; first [lia | reflexivity])
  end.

(* [comment removed for export] *)
Ltac fold_mkR :=
  lazymatch goal with |- context [MS (TNode
    (TNode (TNode (TNode (TNode (TNode TEmpty (Some ?x31) TEmpty) (Some ?x15) TEmpty) (Some ?x7) (TNode TEmpty (Some ?x23) TEmpty)) (Some ?x3) (TNode (TNode TEmpty (Some ?x19) TEmpty) (Some ?x11) (TNode TEmpty (Some ?x27) TEmpty)))
       (Some ?x1) (TNode (TNode (TNode TEmpty (Some ?x17) TEmpty) (Some ?x9) (TNode TEmpty (Some ?x25) TEmpty)) (Some ?x5) (TNode (TNode TEmpty (Some ?x21) TEmpty) (Some ?x13) (TNode TEmpty (Some ?x29) TEmpty))))
    None
    (TNode (TNode (TNode (TNode TEmpty (Some ?x16) TEmpty) (Some ?x8) (TNode TEmpty (Some ?x24) TEmpty)) (Some ?x4) (TNode (TNode TEmpty (Some ?x20) TEmpty) (Some ?x12) (TNode TEmpty (Some ?x28) TEmpty))) (Some ?x2)
       (TNode (TNode (TNode TEmpty (Some ?x18) TEmpty) (Some ?x10) (TNode TEmpty (Some ?x26) TEmpty)) (Some ?x6) (TNode (TNode TEmpty (Some ?x22) TEmpty) (Some ?x14) (TNode TEmpty (Some ?x30) TEmpty))))) _ _ _ _ _ _] =>
    let t := constr:(mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) in
    lazymatch goal with |- context [MS ?R _ _ _ _ _ _] => change R with t end
  end.

(* [comment removed for export] *)
Ltac local_accn FSH fr idx off n FR64 NAME :=
  let T := fresh "T" in let T2 := fresh "T" in let T3 := fresh "T" in let B := fresh "B" in
  pose proof FSH as T; split_at T idx T2; split_at T2 1%nat T3; clear T T3;
  lazymatch type of T2 with rw_cells _ ?mm _ _ =>
    assert (NAME : acc asegs mm (fr + off) n)
      by (destruct T2 as [[_ B] _]; apply (acc_ushadow asegs mm (fr + off) n); [clear - FR64; Z.div_mod_to_equations; lia| lia| lia|];
          let c := eval vm_compute in (2147450880 + Z.of_nat idx) in
          replace (shad (fr + off)) with (fr / 8 + c) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia);
          exact B) end; clear T2.
(* [comment removed for export] *)
Lemma EVQ_thr : forall (P : machine_state -> Prop) ms ms', evt asegs P ms' -> ms' = ms -> evt asegs P ms.
Proof. intros P ms ms' E <-. exact E. Qed.

(* [comment removed for export] *)
Lemma live_destroy_thr : forall (live : list (Z * Z)) pixd dat rs cmd arr na v cv,
  p_data v = dat -> p_cmap v = cmd -> c_arr cv = arr -> dat <> 0 -> cmd <> 0 -> arr <> 0 ->
  dat <> pixd -> dat <> arr -> dat <> cmd -> arr <> pixd -> cmd <> pixd -> cmd <> arr ->
  (forall e, In e live -> fst e <> pixd) -> (forall e, In e live -> fst e <> dat) ->
  (forall e, In e live -> fst e <> cmd) -> (forall e, In e live -> fst e <> arr) ->
  live_destroy pixd v cv ((dat, rs) :: (pixd, 64) :: (arr, na) :: (cmd, 24) :: live) = live.
Proof.
  intros live pixd dat rs cmd arr na v cv ED EC EA DNZ CNZ ANZ DP DA DC AP CP CA F1 F2 F3 F4.
  unfold live_destroy. rewrite ED, EC, EA. replace (cmd =? 0) with false by (symmetry; apply Z.eqb_neq; exact CNZ).
  rewrite (rm_opt_nz dat _ DNZ), (rm_opt_nz arr _ ANZ), (rm_opt_nz cmd _ CNZ).
  rewrite (live_remove_head dat rs).
  rewrite (live_remove_other dat pixd 64) by (intros E; exact (DP (eq_sym E))).
  rewrite (live_remove_other dat arr na) by (intros E; exact (DA (eq_sym E))).
  rewrite (live_remove_other dat cmd 24) by (intros E; exact (DC (eq_sym E))).
  rewrite (live_remove_fresh dat live F2).
  rewrite (live_remove_other arr pixd 64) by (intros E; exact (AP (eq_sym E))).
  rewrite (live_remove_head arr na).
  rewrite (live_remove_other arr cmd 24) by (intros E; exact (CA E)).
  rewrite (live_remove_fresh arr live F4).
  rewrite (live_remove_other cmd pixd 64) by (intros E; exact (CP (eq_sym E))).
  rewrite (live_remove_head cmd 24).
  rewrite (live_remove_fresh cmd live F3).
  rewrite (live_remove_head pixd 64).
  exact (live_remove_fresh pixd live F1).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac carry AG H acl side :=
  unfold hid in H;
  lazymatch type of AG with agree_on _ ?ma ?mb => lazymatch type of H with rw_cells _ ma ?A ?cs =>
    apply (rw_cells_agree_nw asegs ma mb A cs) in H;
    [| eapply agree_sub; [exact AG|]; cbv beta; let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx;
       unfold pix_cells_rc, pix_cells, cmap_cells in Hx; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Hx;
       first [split; [acl x Hx| cbn [outside]; side Hx] | acl x Hx] ] end end.
(* [comment removed for export] *)
Ltac carry_mu MU H side :=
  unfold hid in H;
  lazymatch type of MU with munch ?W ?ma ?mb => lazymatch type of H with rw_cells _ ma ?A ?cs =>
    apply (rw_cells_agree_nw asegs ma mb A cs) in H;
    [| eapply agree_sub; [exact (agree_of_munch W ma mb (outside W) MU (fun x Hx => Hx))|]; cbv beta;
       let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx;
       unfold pix_cells_rc, pix_cells, cmap_cells in Hx; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Hx; cbn [outside]; side Hx ] end end.
(* [comment removed for export] *)
Ltac drop_foreign_cells fr usp :=
  repeat match goal with H : rw_cells asegs _ ?b _ |- _ =>
    lazymatch b with
    | fr => fail | (fr + _)%Z => fail | (fr / 8 + _)%Z => fail | (fr / 8 + _ + _)%Z => fail
    | usp => fail | (usp + _)%Z => fail | (usp - _)%Z => fail
    | _ => idtac "note: diet drops cells at" b; clear H
    end end;
  repeat match goal with H : u8arr _ _ _ _ |- _ => clear H | H : u32arr _ _ _ _ |- _ => clear H | H : bytes_at _ _ _ |- _ => clear H | H : wr_at asegs _ _ _ |- _ => clear H end.
(* [comment removed for export] *)
Ltac seg_side fr b FR64 LOW LOR Hx :=
  repeat match goal with Hf : parked (fr + 256 <= b \/ _ <= fr) |- _ => unfold parked in Hf; revert Hf end;
  repeat match goal with Hf : parked (b + _ <= fr / 8 + 2147450880 \/ _ <= b) |- _ => unfold parked in Hf; revert Hf end;
  repeat match goal with Hc : b + _ <= rt_sp0 _ _ - 8388608 |- _ => revert Hc end;
  clear - Hx FR64 LOW LOR; intros; unfold shad, SHB in *; cbn [outside]; repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia].
(* [comment removed for export] *)
Ltac flag_side fl b Hx :=
  repeat match goal with Hf : fl < b \/ _ <= fl |- _ => revert Hf end; clear - Hx; intros; cbn [outside]; repeat split; try exact I; lia.
(* [comment removed for export] *)
Ltac stk_side b LOW LOR Hx :=
  repeat match goal with Hc : b + _ <= rt_sp0 _ _ - 8388608 |- _ => revert Hc end; clear - Hx LOW LOR; intros; cbn [outside]; repeat split; try exact I; lia.

(* [comment removed for export] *)
Ltac forget_junk H :=
  repeat match type of H with context [CB _ ?bs] =>
    lazymatch bs with
    | firstn _ _ => let j := fresh "jq" in set (j := bs) in *; clearbody j
    | skipn _ _ => let j := fresh "jq" in set (j := bs) in *; clearbody j
    end end.

Section THR_c0.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis RC : rt_contracts RT.
Hypothesis RERR : returnError_cps RT e_returnErrorPtr.
Hypothesis PCS : pixCreate_sure_cps RT.
Hypothesis PCR : pixCopyResolution_cps RT.
Hypothesis PCI : pixCopyInputFormat_cps RT.
Hypothesis PARSE : parseStringForNumbers_gq_cps RT.
Hypothesis NSORT : numaSort_gq_cps RT.
Hypothesis QTAB : makeGrayQuantTableArb_gq_cps RT.
Hypothesis SETBW : pixcmapSetBlackAndWhite00_cps RT.
Hypothesis NDY : numaDestroy_cps RT.
Hypothesis SCM : pixSetColormap_cps RT.
Hypothesis RMC : pixRemoveColormap_gray_cps RT.
Hypothesis PDRC : pixDestroy_rc_cps RT.
Hypothesis PDY : pixDestroy_cps RT.

Theorem thr_c0 : gq_op_case RT 0 e_pixThresholdGrayArb RA_FUZZ_OP6 11 6 12 THR_COST
            (fun a1 a2 a3 a4 a5 _ => wZ a1 LIT_EDGEVALS /\ wZ a2 8 /\ wZ a3 0 /\ wZ a4 0 /\ wZ a5 0).
Proof using AF GP RC RERR PCS PCR PCI PARSE NSORT QTAB SETBW NDY SCM RMC PDRC PDY.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo pix v cv ras
    FDO MST -> -> (A1 & A2 & A3 & A4 & A5) POBJ VDATA CNZ UC RAF RAS ENV RES AL.
  unfold wZ in A1, A2, A3, A4, A5. subst a1 a2 a3 a4 a5.
  unfold lpost_f, lpost, lenv, keeps, keepsL, lres in *. destruct ENV as (LH & SSP & ART0 & MI & ST & LOW & LOR & SPT & SPA & SPB).
  destruct RES as (FRB & LVB & CRB & LVP).
  pose proof POBJ as (PXC & (PIN & PX0 & PX16 & _) & (HD1 & HW1 & HH1 & HWPL & HRS) & PDATA & _).
  destruct PDATA as [DZ|((DIN & D0 & D16 & DSZ) & DNE)]; [contradiction|].
  unfold THR_COST, OP_COST, is_d8, MSG_COST in *.
  destruct (af_client_consts RT AF Σ m ART0) as (G1 & G2 & G3 & G4).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  unfold entry_st, e_pixThresholdGrayArb, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (USP : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range).
  unfold LSTK, STDERR_STACK in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. unfold SHB in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  pose proof ST as (STa & STb & _).
  set (LVF := rt_live RT Σ) in *.
  set (PF0 := fun a => aclient LVF (rt_frames RT Σ) usp a).
  set (PF := fun a => aclient LVF (rt_frames RT Σ) usp a /\ outside [(pix + 20, pix + 24)] a).
  pose proof (agree_refl PF0 m) as AGF.   (* [comment removed for export] *)
  assert (LVFS : forall e, In e LVF -> In e (rt_live RT Σ)) by (intros e He; exact He).
  assert (PFS : forall a, PF0 a -> usp <= a \/ a < lo).
  { intros a Ha. destruct (aclient_split RT AF Σ m usp a ART0 Ha) as [H|H]; [left; exact H| right; unfold STACK_WIN in H; lia]. }
  assert (PFS1 : forall a, PF a -> usp <= a \/ a < lo) by (intros a [Ha _]; exact (PFS a Ha)).
  assert (PFO : forall a, PF a -> (a < pix + 20 \/ pix + 24 <= a)) by (intros a [_ Ho]; cbn [outside] in Ho; lia).
  chunk_facts RT AF GP pix 64.
  chunk_facts RT AF GP (p_data v) (rsize v).
  unfold pix_cells in PXC.
  assert (PML : forall q k a, In (q, k) (rt_live RT Σ) -> q <= a < q + k -> PF0 a).
  { intros q k a Hq Ha. right; right; left; exists q, k; split; [exact Hq| lia]. }
  pose proof POBJ as POBJ0. hide POBJ0. hide POBJ.
  park_ne. unpark VDATA.
  park_disj.
  carve_frame 256%nat ST.
  idtac "MARK carved".
  Time walk_to AF MST [(usp - 256, usp)] [e_stack_malloc 2%nat].
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx) as P1; clear - P1 LOR; split; [lia| exact I]).
  eapply cps_seq.
  { pose proof (gp_stack_malloc_2 RT GP) as SM2; unfold stack_malloc_contract' in SM2; eapply SM2 with (lo := lo); rt_side idtac.
    all: try (clear - CRB; destruct (p_d v =? 8); unfold RASTER_COST in CRB; lia). }
  after_call RT AF.
  fold_ag ltac:(fun Hx => apply (aclient_mono LVF _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]).
  fframe_open RT AF PF0 (rt_live RT Σ) usp 2%nat 256 ltac:(fun Ha => exact Ha).
  fframe_chunk RT AF fr 2%nat 256 pix 64.
  fframe_chunk RT AF fr 2%nat 256 (p_data v) (4 * (p_wpl v * p_h v)).
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
  idtac "MARK frame open".
  Time walk_to AF MST [(usp - 320, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [0x9f574].
  cps_stop.
  art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
  lazymatch goal with MUx : munch _ ?mm _ |- _ =>
      agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx) as P1; destruct (NFA _ Hx) as [N1 N2]; clear - P1 N1 N2 LOW LOR SPT SPA SPB FR0 FR64;
                                         unfold shad, SHB in *; repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end.
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *.
  local_accn FSH fr 10%nat 80 4 FR64 ACCW. local_accn FSH fr 12%nat 96 4 FR64 ACCH. local_accn FSH fr 14%nat 112 4 FR64 ACCD.
  park_disj.
  idtac "MARK header done".
  forget_junk FR. forget_junk FRM. forget_junk FSH.
  (* [comment removed for export] *)
  Time walk_to AF MST [(usp - 320, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [0x9f5a8; e_parseStringForNumbers; e_stack_malloc 2%nat].
  try fold_mkR.
  idtac "MARK at d test".
  (* [comment removed for export] *)
  assert (DR : 1 <= p_d v <= 32) by (clear - HD1; cbn [In] in HD1; lia).
  rewrite !(sx32_small (p_d v)) by (clear - DR; lia).
  destruct (Z.eq_dec (p_d v) 8) as [D8|DN8].
  all: cycle 1.
  lstep. brT.
  awalk [e_returnErrorPtr].
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx) as P1; destruct (NFA _ Hx) as [N1 N2]; clear - P1 N1 N2 LOW LOR SPT SPA SPB FR0 FR64;
                      unfold shad, SHB in *; repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
  assert (CR4 : 4 <= rt_credit RT Σ) by (clear - CRB DN8; rewrite (proj2 (Z.eqb_neq (p_d v) 8) DN8) in CRB; exact CRB).
  pose proof RERR as RE. unfold returnError_cps in RE.
  eapply cps_seq.
  { eapply RE with (lo := lo); rt_side idtac.
    1: lit_in_fast.
    1: lit_in_fast.
    lenv_tac. }
  idtac "MARK msg applied".
  after_call RT AF.
  fold_ag ltac:(fun Hx => apply (aclient_mono LVF _ usp _ _ _ _ Hx); [first [solve [live_sub_tac] | solve [live_add_tac]]| solve [frames_sub_tac]| lia]).
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
  ctx_gc RT.
  Time walk_to AF MST [(usp - 320, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [0x9ff44].
  frame_release RT AF GP MST Σ fr 2%nat 256 PF0 AGF PFS usp lo 0x9ff4c
        ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
        ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx) as P1; destruct (NFA _ Hx) as [N1 N2]; clear - P1 N1 N2 LOW LOR SPT SPA SPB FR0 FR64;
                        unfold shad, SHB in *; repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
  idtac "MARK msg released".
  refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  Time walk_to AF MST [(usp - 320, usp)] (@nil Z).
  
  cps_stop.
  idtac "MARK msg epilogue".
  apply cps_finish; intros c Hc; subst QF; cbv beta.
  lazymatch type of Hc with ASTA RT ?S _ _ _ => exists S, 0, v, cv end.
  split.
  2: {
  split; [intros _; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity|].
  split; [intros N; exfalso; apply N; reflexivity|].
  split; [repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; exact LVP|].
  split; [repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; unfold LVF; lia|].
  split; [repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity|].
  split; [repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; reflexivity|].
  rewrite (proj2 (Z.eqb_neq (p_d v) 8) DN8). repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H in * end. lia.
  }
  eapply (ASTA_conseq RT); [exact Hc|]; intros ms <-; eexists.
  split; [unfold ret_st; rewrite ?ESP; do 16 eexists; reflexivity|].
  split; [unfold rt_after_f; split; [split; [assumption| split; assumption]| split; assumption]|].
  split; [intros a Ha Ho; apply AGF; exact Ha|].
  split.
  { lazymatch goal with |- pix_obj (rt_live RT ?S) ?mc _ _ _ =>
      assert (KL0 : keeps_live (rt_live RT Σ) m mc) by (intros b kk Hb a Ha; apply AGF; exact (PML b kk _ Hb Ha));
      replace (rt_live RT S) with (rt_live RT Σ) by (symmetry; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; reflexivity);
      unfold hid in POBJ; exact (pix_obj_keep _ m mc pix v cv KL0 POBJ) end. }
  left; reflexivity.
  (* [comment removed for export] *)
  idtac "MARK d8 arm".
  lstep. brF.
  rewrite D8 in *. cbn [Z.eqb Pos.eqb] in CRB.
  (* [comment removed for export] *)
  Time awalk [e_parseStringForNumbers; 0x9f6a0; 0x9f72c].
  try fold_mkR.
  idtac "MARK at parse".
  (* [comment removed for export] *)
  pose proof (bv_unsigned_in_range 64 s0) as RS0. unfold bv_modulus in RS0. change (2 ^ Z.of_N 64) with (2^64) in RS0.
  assert (RALO : 4096 <= bv_unsigned ra < 2^64) by (rewrite RAF; unfold RA_FUZZ_OP6; clear; lia).
  pose proof UC as UCX. unfold uctx in UCX. rewrite ESP in UCX. rewrite unsigned_lit in UCX by (clear - USP0 USP1; lia).
  assert (CHAIN : forall mx, agree_on (fun a => usp <= a < 140737488355328) m mx -> rw_cells asegs mx (usp + -16) [C8 s0; C8 ra] ->
                  chain_ok mx (usp + -256) usp (bv_unsigned ra :: ras)).
  { intros mx AGx RECx. apply (chain_ok_push _ (usp + -256) usp (bv_unsigned ra) (bv_unsigned s0) ras);
      [ clear - USP0; lia | clear - SPA; Z.div_mod_to_equations; lia | clear - SPT; unfold USTACK_TOP; lia | exact RALO | exact RS0
      | rewrite !Z_to_bv_bv_unsigned; exact RECx | ].
    apply (chain_ok_keep ras m _ usp (bv_unsigned s0) UCX). unfold USTACK_TOP. exact AGx. }
  (* [comment removed for export] *)
  assert (AGS0 : forall mx, agree_on PF0 m mx -> agree_on (fun a => usp <= a < 140737488355328) m mx)
    by (intros mx AGx; eapply agree_sub; [exact AGx|]; intros zx Hzx; left; exact Hzx).
  assert (AGS1 : forall mx, agree_on PF m mx -> agree_on (fun a => usp <= a < 140737488355328) m mx)
    by (intros mx AGx; eapply agree_sub; [exact AGx|]; intros zx Hzx; split; [left; exact Hzx| cbn [outside]; clear - Hzx CKR LOW LOR; lia]).
  idtac "MARK chain".
  (* [comment removed for export] *)
  assert (TRP : Forall (fun f => In (f :: bv_unsigned (Z_to_bv 64 0x9f5e0) :: bv_unsigned ra :: ras) CLIENT_TRACES \/ In [f] CLIENT_TRACES) PARSE_RAS).
  { rewrite RAF, RAS. rewrite unsigned_lit by (clear; lia). unfold PARSE_RAS, RA_FUZZ_OP6, D_libiface.RA_TOP.
    repeat (apply Forall_cons; [first [left; apply ct_mem_In; vm_compute; reflexivity | right; apply ct_mem_In; vm_compute; reflexivity] |]). apply Forall_nil. }
  assert (TRP2 : In (0x918dc :: bv_unsigned (Z_to_bv 64 0x9f5e0) :: bv_unsigned ra :: ras) CLIENT_TRACES).
  { rewrite RAF, RAS. rewrite unsigned_lit by (clear; lia). unfold RA_FUZZ_OP6, D_libiface.RA_TOP. apply ct_mem_In; vm_compute; reflexivity. }
  pose proof FR as FRrec. split_before FRrec (C8 s0) FRrec2. clear FRrec.
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx) as P1; destruct (NFA _ Hx) as [N1 N2]; clear - P1 N1 N2 LOW LOR SPT SPA SPB FR0 FR64;
                      unfold shad, SHB in *; repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
  idtac "MARK at_call parse".
  eapply cps_seq.
  { pose proof PARSE as PA; unfold parseStringForNumbers_gq_cps in PA.
    eapply PA with (lo := lo) (ras := bv_unsigned ra :: ras).
    - exact FDO.
    - exact MST.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - unfold uctx. rewrite !unsigned_lit by (clear - USP0 USP1 LOR STa; lia). apply CHAIN; [apply AGS0; exact AGF|].
      lazymatch type of FRrec2 with rw_cells _ _ ?A _ => replace (usp + -16) with A by (clear; lia) end. exact FRrec2.
    - exact TRP.
    - exact TRP2.
    - lenv_tac.
    - unfold lres; repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end;
      cbn [length]; unfold FRAMES_MAX, LIVE_MAX, PARSE_COST in *; unfold LVF in *;
      repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H in * end; repeat split; [clear - FRB; lia| clear - LVB; lia| clear - CRB; unfold RASTER_COST in CRB; cbn in CRB; lia| exact LVP]. }
  idtac "MARK parse applied".
  clear FRrec2.
  after_call RT AF.
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono LVF _ usp _ _ _ _ Hx); [first [solve [live_sub_tac] | solve [live_add_tac]]| solve [frames_sub_tac]| lia]| exact I]).
  idtac "MARK after parse".
  lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ => rename S into Σp; rename A into ARTP; rename mm into mp end.
  lazymatch goal with H : numa_obj _ mp ?n 50 ?ar _ |- _ => rename H into NOBJ; rename n into na; rename ar into arr end.
  lazymatch goal with H : rt_live RT Σp = numa_live na 50 arr _ |- _ => rename H into LVPN end.
  assert (LVPp : rt_live RT Σp = (arr, 200) :: (na, 32) :: rt_live RT Σ) by (rewrite LVPN; unfold numa_live; repeat match goal with E : rt_live RT _ = rt_live RT Σ |- _ => rewrite E end; reflexivity).
  assert (FRSp : rt_frames RT Σp = (fr, 2%nat) :: rt_frames RT Σ) by (repeat match goal with E : rt_frames RT Σp = _ |- _ => rewrite E end; first [exact FRS | assumption]).
  assert (SP0p : rt_sp0 RT Σp = rt_sp0 RT Σ) by (repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; reflexivity).
  assert (CRp : rt_credit RT Σ - 1 - PARSE_COST <= rt_credit RT Σp) by (repeat match goal with E : rt_credit RT _ = _ |- _ => rewrite E in * end; unfold PARSE_COST in *; lia).
  sigma_gc RT Σ Σp.
  assert (NAIN : In (na, 32) (rt_live RT Σp)) by (rewrite LVPp; right; left; reflexivity).
  assert (ARIN : In (arr, 200) (rt_live RT Σp)) by (rewrite LVPp; left; reflexivity).
  assert (LSUBp : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σp)) by (intros e He; rewrite LVPp; do 2 right; exact He).
  pose proof NOBJ as ((npad & NC) & (njunk & NAC) & _ & _ & NANE & NCAP & NLEN). unfold numa_cells in NC.
  change (Z.of_nat (length (map ival_w EDGE_VALS))) with 4 in NC.
  unfold numa_arr_cells, EDGE_VALS in NAC. cbn [map app length Z.of_nat Pos.of_succ_nat Pos.succ] in NAC.
  change (Z.to_nat (4 * 50 - 4 * Z.of_nat 4)) with 184%nat in NAC. change (Z.to_nat (4 * 50 - 4 * 4)) with 184%nat in NAC.
  assert (SUBN : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σp) /\ fst e <> na)
    by (intros e He; split; [exact (LSUBp e He)|];
        apply (fresh_chunk_ne RT AF Σp mp [(arr, 200)] na 32 (rt_live RT Σ) e ARTP LVPp); [cbn [app In]; right; exact He | clear; lia | destruct e as [eq ek]; exact (LVP eq ek He)]).
  assert (SUBAR : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σp) /\ fst e <> arr)
    by (intros e He; split; [exact (LSUBp e He)|];
        apply (fresh_chunk_ne RT AF Σp mp [] arr 200 ((na, 32) :: rt_live RT Σ) e ARTP LVPp); [cbn [app In]; right; exact He | clear; lia | destruct e as [eq ek]; exact (LVP eq ek He)]).
  assert (NCNA : forall a, PF0 a -> a < na \/ na + 32 <= a)
    by (intros a Ha; apply (inner_chunk_apart RT AF Σp mp na 32 (rt_live RT Σ) (rt_frames RT Σ) usp a ARTP NAIN SUBN); [rewrite FRSp; intros e He; right; exact He | rewrite SP0p; ul | exact Ha]).
  assert (NCAR : forall a, PF0 a -> a < arr \/ arr + 200 <= a)
    by (intros a Ha; apply (inner_chunk_apart RT AF Σp mp arr 200 (rt_live RT Σ) (rt_frames RT Σ) usp a ARTP ARIN SUBAR); [rewrite FRSp; intros e He; right; exact He | rewrite SP0p; ul | exact Ha]).
  assert (NNX : na <> pix) by (intro E; exact (proj2 (SUBN (pix, 64) PIN) (eq_sym E))).
  assert (NAX : arr <> pix) by (intro E; exact (proj2 (SUBAR (pix, 64) PIN) (eq_sym E))).
  hide SUBN. hide SUBAR.
  chunk_facts RT AF GP na 32. chunk_facts RT AF GP arr 200.
  fframe_chunk RT AF fr 2%nat 256 na 32. fframe_chunk RT AF fr 2%nat 256 arr 200.
  apart2 RT AF ANX na 32 pix 64 NNX. apart2 RT AF AAX arr 200 pix 64 NAX.
  park_disj. park_ne.
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *.
  local_accn FSH fr 16%nat 128 8 FR64 ACCNA. local_accn FSH fr 20%nat 160 8 FR64 ACCPT. local_accn FSH fr 24%nat 192 8 FR64 ACCCM.
  park_disj.
  ctx_gc RT.
  assert (NA0 : 0 < na) by (destruct NOBJ as (_ & _ & (_ & Q & _) & _); exact Q).
  assert (AR0 : 0 < arr) by (destruct NOBJ as (_ & _ & _ & (_ & Q & _) & _); exact Q).
  assert (NA16 : na mod 16 = 0) by (destruct NOBJ as (_ & _ & (_ & _ & Q & _) & _); exact Q).
  assert (AR16 : arr mod 16 = 0) by (destruct NOBJ as (_ & _ & _ & (_ & _ & Q & _) & _); exact Q).
  idtac "MARK parse names".
  (* [comment removed for export] *)
  Time walk_to AF MST [(usp - 320, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [0x9f5e4].
  cps_stop.
  art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
  lazymatch goal with MUx : munch _ ?mm _, A : ART RT _ ?mm |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
      agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx) as P1; destruct (NFA _ Hx) as [N1 N2]; clear - P1 N1 N2 LOW LOR SPT SPA SPB FR0 FR64;
                                         unfold shad, SHB in *; repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end.
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  ctx_gc RT.
  (* [comment removed for export] *)
  Time walk_to AF MST [(usp - 320, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [e_numaSort; 0x9f5f0; 0x9f6ec; 0x9f764].
  try fold_mkR.
  idtac "MARK at sort".
  (* [comment removed for export] *)
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx) as P1; destruct (NFA _ Hx) as [N1 N2]; clear - P1 N1 N2 LOW LOR SPT SPA SPB FR0 FR64;
                      unfold shad, SHB in *; repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
  lazymatch goal with |- cps _ (ASTA RT ?S _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
    assert (NOBJc : numa_obj (rt_live RT S) mc na 50 arr (map ival_w EDGE_VALS))
      by (unfold numa_obj; split; [exists npad; unfold numa_cells; exact NC
          | split; [exists njunk; unfold numa_arr_cells, EDGE_VALS; cbn [map app length Z.of_nat Pos.of_succ_nat Pos.succ];
                    first [exact NAC | lazymatch type of NAC with rw_cells _ _ _ (_ :: _ :: _ :: _ :: CB ?k _ :: _) => change (Z.to_nat (4 * 50 - 4 * 4)) with k; exact NAC end]
          | destruct NOBJ as (_ & _ & REST); exact REST]]) end.
  idtac "MARK nobj".
  eapply cps_seq.
  { pose proof NSORT as NS; unfold numaSort_gq_cps in NS.
    eapply NS with (lo := lo) (na := na) (arr := arr).
    - exact FDO.
    - exact MST.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - exact NOBJc.
    - lenv_tac.
    - unfold lres; repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end;
      cbn [length]; unfold FRAMES_MAX, LIVE_MAX, NSORT_COST in *; unfold LVF in *;
      repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H in * end; repeat split; [clear - FRB; lia| clear - LVB; lia| clear - CRp CRB; unfold RASTER_COST, PARSE_COST in *; cbn in CRB; lia|].
      intros p n Hp. cbn [In] in Hp. destruct Hp as [E|[E|Hp]]; [injection E as <- <-; clear; lia| injection E as <- <-; clear; lia| exact (LVP p n Hp)]. }
  idtac "MARK sort applied".
  clear NOBJc NC NAC.
  after_call RT AF.
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono LVF _ usp _ _ _ _ Hx); [first [solve [live_sub_tac] | solve [live_add_tac]]| solve [frames_sub_tac]| lia]| exact I]).
  idtac "MARK after sort".
  lazymatch goal with H : numa_obj (rt_live RT Σp) ?mc na 50 arr _, A : ART RT Σp ?mc |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mc _))) _ => rename H into NOBJs end.
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  ctx_gc RT.
  (* [comment removed for export] *)
  Time walk_to AF MST [(usp - 320, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [e_makeGrayQuantTableArb].
  try fold_mkR.
  idtac "MARK at qtab".
  assert (CB8_cell : forall (mm : mem) A bs, rw_cells asegs mm A [CB 8 bs] -> exists x : word, rw_cells asegs mm A [C8 x]).
  { clear.
    assert (RNG : forall bs : list byte, (0 <= bytes_le_to_Z bs < 2^(8 * Z.of_nat (length bs)))%Z).
    { clear. induction bs as [|b bs IH]; cbn [bytes_le_to_Z length]; [cbn; lia|].
      pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. change (2^Z.of_N 8)%Z with (2^8)%Z in Hb.
      assert (Hs : (0 <= Z.shiftl (bytes_le_to_Z bs) 8)%Z) by (apply Z.shiftl_nonneg; lia).
      split. { apply Z.lor_nonneg. lia. }
      pose proof (Z.add_lor_land (bv_unsigned b) (Z.shiftl (bytes_le_to_Z bs) 8)) as E.
      pose proof (Z.land_nonneg (bv_unsigned b) (Z.shiftl (bytes_le_to_Z bs) 8)) as L.
      rewrite Z.shiftl_mul_pow2 in * by lia.
      replace (2 ^ (8 * Z.of_nat (S (length bs))))%Z with (2^8 * 2 ^ (8 * Z.of_nat (length bs)))%Z.
      2:{ rewrite <- Z.pow_add_r by lia. f_equal. lia. }
      nia. }
    intros mq Aq bq Hq. exists (le_bytes_to_word bq). pose proof Hq as [[W _] _]. cbn in W. destruct W as [Lq _].
    apply (rw_cells_recell mq Aq _ [C8 (le_bytes_to_word bq)] Hq); [cbn; tauto | | reflexivity].
    cbn [cells_bytes cbytes app]. f_equal. unfold le8, word_to_le_bytes, le_bytes_to_word.
    pose proof (RNG bq) as HR. rewrite Lq in HR. change (2 ^ (8 * Z.of_nat 8))%Z with (2^64)%Z in HR.
    rewrite unsigned_lit by lia. rewrite <- Lq. apply le_bytes_roundtrip. }
  (* [comment removed for export] *)
  split_at FR 8%nat FQ. split_at FQ 1%nat FRb.
  destruct (CB8_cell _ _ _ FQ) as (xq & FQ1). clear FQ.
  split_last_CB FRM [24%nat; 8%nat; 24%nat; 8%nat; 48%nat].
  split_at FRM 14%nat FC. split_at FC 1%nat FRMb.
  destruct (CB8_cell _ _ _ FC) as (xc & FC1). clear FC.
  pose proof FSH as SHC. split_at SHC 24%nat SHC2. split_at SHC2 1%nat SHC3. clear SHC SHC3.
  idtac "MARK qtab cells".
  assert (TRQ : Forall (fun f => In (f :: bv_unsigned (Z_to_bv 64 0x9f7b0) :: bv_unsigned ra :: ras) CLIENT_TRACES) QTAB_RAS).
  { rewrite RAF, RAS. rewrite unsigned_lit by (clear; lia). unfold QTAB_RAS, RA_FUZZ_OP6, D_libiface.RA_TOP.
    repeat (apply Forall_cons; [apply ct_mem_In; vm_compute; reflexivity|]). apply Forall_nil. }
  pose proof FRb as FRrec. split_before FRrec (C8 s0) FRrec2. clear FRrec.
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx) as P1; destruct (NFA _ Hx) as [N1 N2]; clear - P1 N1 N2 LOW LOR SPT SPA SPB FR0 FR64;
                      unfold shad, SHB in *; repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
  idtac "MARK at_call qtab".
  eapply cps_seq.
  { pose proof QTAB as QT; unfold makeGrayQuantTableArb_gq_cps in QT.
    eapply QT with (lo := lo) (ras := bv_unsigned ra :: ras) (na := na) (arr := arr) (ptab := usp + -112) (pcmap := fr + 192) (x1 := xq) (x2 := xc).
    - exact FDO.
    - exact MST.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - f_equal; clear; lia.
    - reflexivity.
    - exact NOBJs.
    - unfold optrS. rewrite !unsigned_lit by (clear - USP0 USP1 LOR STa; lia). repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end.
      clear - SPB SPA. repeat split; [lia| lia| lia| Z.div_mod_to_equations; lia].
    - unfold optrF. split.
      + exists fr, 2%nat. rewrite FRSp. change (fs_size 2) with 256. split; [left; reflexivity|]. split; [clear; lia|]. split; [clear; lia|].
        split; [clear - FR64; Z.div_mod_to_equations; lia|]. split; [clear - FR0; lia|]. split; [clear - FRHI SP0R1; lia|].
        replace (shad (fr + 192)) with (fr / 8 + 2147450904) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia). destruct SHC2 as [[_ B] _]. exact B.
      + pose proof FRSH as Q; unfold parked in Q. clear - Q FR0 FR64 FRSEG. unfold SEGTOP_A. repeat split; first [lia | Z.div_mod_to_equations; lia].
    - lazymatch type of FQ1 with rw_cells _ _ ?A _ => replace (usp + -112) with A by (clear; lia) end. exact FQ1.
    - exact FC1.
    - clear - FRHI LOW LOR; lia.
    - unfold uctx. rewrite !unsigned_lit by (clear - USP0 USP1 LOR STa; lia). apply CHAIN; [apply AGS0; exact AGF|].
      lazymatch type of FRrec2 with rw_cells _ _ ?A _ => replace (usp + -16) with A by (clear; lia) end. exact FRrec2.
    - exact TRQ.
    - lenv_tac.
    - unfold lres; repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end;
      cbn [length]; unfold FRAMES_MAX, LIVE_MAX, QTAB_COST in *; unfold LVF in *;
      repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H in * end; repeat split; [clear - FRB; lia| clear - LVB; lia| clear - CRp CRB; unfold RASTER_COST, PARSE_COST in *; cbn in CRB; lia|].
      intros p n Hp. cbn [In] in Hp. destruct Hp as [E|[E|Hp]]; [injection E as <- <-; clear; lia| injection E as <- <-; clear; lia| exact (LVP p n Hp)]. }
  idtac "MARK qtab applied".
  clear FRrec2 FQ1 FC1 SHC2.
  osd_mark_about (usp + -112). osd_mark LOW. osd_mark LOR. osd_mark SPT. osd_mark SPB. osd_mark STa. osd_mark SP0R0. osd_mark SP0R1. osd_mark FR0. osd_mark FRHI. osd_mark FRSEG. osd_mark FRSH. osd_mark FR64.
  after_call RT AF.
  osd_clear.
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono LVF _ usp _ _ _ _ Hx); [first [solve [live_sub_tac] | solve [live_add_tac]]| solve [frames_sub_tac]| lia]|
                                 cbn [outside]; pose proof (PFS _ Hx) as P1; destruct (NFA _ Hx) as [N1 N2]; clear - P1 N1 N2 LOR; repeat split; try exact I; lia]).
  idtac "MARK after qtab".
  lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ => rename S into Σq; rename A into ARTQ; rename mm into mq end.
  lazymatch goal with H : rt_live RT Σq = (?t, 1024) :: (?ca, 1024) :: (?cm, 24) :: rt_live RT Σp |- _ => rename H into LVQN; rename t into tab; rename ca into carr; rename cm into cmap end.
  lazymatch goal with H : rw_cells asegs mq (usp + -112) [C8 (Z_to_bv 64 tab)] |- _ => rename H into FQ end.
  lazymatch goal with H : rw_cells asegs mq (fr + 192) [C8 (Z_to_bv 64 cmap)] |- _ => rename H into FC end.
  lazymatch goal with H : u32arr asegs mq tab _ |- _ => rename H into UAT end.
  lazymatch goal with H : cmap_obj (rt_live RT Σq) mq cmap _ |- _ => rename H into CMO end.
  lazymatch goal with H : numa_obj (rt_live RT Σq) mq na 50 arr _ |- _ => rename H into NOBJq end.
  assert (LVQ : rt_live RT Σq = (tab, 1024) :: (carr, 1024) :: (cmap, 24) :: (arr, 200) :: (na, 32) :: rt_live RT Σ) by (rewrite LVQN, LVPp; reflexivity).
  assert (FRSq : rt_frames RT Σq = (fr, 2%nat) :: rt_frames RT Σ) by (repeat match goal with E : rt_frames RT Σq = _ |- _ => rewrite E end; first [exact FRSp | assumption]).
  assert (SP0q : rt_sp0 RT Σq = rt_sp0 RT Σ) by (repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; reflexivity).
  assert (CRq : rt_credit RT Σ - 1 - PARSE_COST - QTAB_COST <= rt_credit RT Σq) by (clear - CRp H24; unfold PARSE_COST, QTAB_COST in *; lia).
  join_cells FR FQ. join_cells FR FRb. join_cells FRM FC. join_cells FRM FRMb.
  sigma_gc RT Σ Σq.
  assert (LSUBq : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σq)) by (intros e He; rewrite LVQ; do 5 right; exact He).
  assert (NAINq : In (na, 32) (rt_live RT Σq)) by (rewrite LVQ; do 4 right; left; reflexivity).
  assert (ARINq : In (arr, 200) (rt_live RT Σq)) by (rewrite LVQ; do 3 right; left; reflexivity).
  assert (CMIN : In (cmap, 24) (rt_live RT Σq)) by (rewrite LVQ; do 2 right; left; reflexivity).
  assert (CAIN : In (carr, 1024) (rt_live RT Σq)) by (rewrite LVQ; right; left; reflexivity).
  assert (TBIN : In (tab, 1024) (rt_live RT Σq)) by (rewrite LVQ; left; reflexivity).
  assert (LVPq : forall e, In e (rt_live RT Σq) -> 0 < snd e).
  { intros [q k] Hq. rewrite LVQ in Hq. cbn [In] in Hq. cbn [snd].
    destruct Hq as [E|[E|[E|[E|[E|Hq]]]]]; [injection E as <- <-; clear; lia| injection E as <- <-; clear; lia| injection E as <- <-; clear; lia| injection E as <- <-; clear; lia| injection E as <- <-; clear; lia| exact (LVP q k Hq)]. }
  assert (NET : forall e, In e ([] ++ (carr, 1024) :: (cmap, 24) :: (arr, 200) :: (na, 32) :: rt_live RT Σ) -> fst e <> tab)
    by (intros e He; apply (fresh_chunk_ne RT AF Σq mq [] tab 1024 _ e ARTQ LVQ He ltac:(clear; lia)); apply LVPq; rewrite LVQ; right; exact He).
  assert (NECA : forall e, In e ([(tab, 1024)] ++ (cmap, 24) :: (arr, 200) :: (na, 32) :: rt_live RT Σ) -> fst e <> carr)
    by (intros e He; apply (fresh_chunk_ne RT AF Σq mq [(tab, 1024)] carr 1024 ((cmap, 24) :: (arr, 200) :: (na, 32) :: rt_live RT Σ) e ARTQ LVQ He ltac:(clear; lia));
        apply LVPq; rewrite LVQ; cbn [app In] in He |- *; tauto).
  assert (NECM : forall e, In e ([(tab, 1024); (carr, 1024)] ++ (arr, 200) :: (na, 32) :: rt_live RT Σ) -> fst e <> cmap)
    by (intros e He; apply (fresh_chunk_ne RT AF Σq mq [(tab, 1024); (carr, 1024)] cmap 24 ((arr, 200) :: (na, 32) :: rt_live RT Σ) e ARTQ LVQ He ltac:(clear; lia));
        apply LVPq; rewrite LVQ; cbn [app In] in He |- *; tauto).
  assert (NCT : forall a, PF0 a -> a < tab \/ tab + 1024 <= a)
    by (intros a Ha; apply (inner_chunk_apart RT AF Σq mq tab 1024 (rt_live RT Σ) (rt_frames RT Σ) usp a ARTQ TBIN); [intros e He; split; [exact (LSUBq e He)| apply NET; cbn [app]; do 4 right; exact He] | rewrite FRSq; intros e He; right; exact He | rewrite SP0q; ul | exact Ha]).
  assert (NCCA : forall a, PF0 a -> a < carr \/ carr + 1024 <= a)
    by (intros a Ha; apply (inner_chunk_apart RT AF Σq mq carr 1024 (rt_live RT Σ) (rt_frames RT Σ) usp a ARTQ CAIN); [intros e He; split; [exact (LSUBq e He)| apply NECA; cbn [app]; do 4 right; exact He] | rewrite FRSq; intros e He; right; exact He | rewrite SP0q; ul | exact Ha]).
  assert (NCCM : forall a, PF0 a -> a < cmap \/ cmap + 24 <= a)
    by (intros a Ha; apply (inner_chunk_apart RT AF Σq mq cmap 24 (rt_live RT Σ) (rt_frames RT Σ) usp a ARTQ CMIN); [intros e He; split; [exact (LSUBq e He)| apply NECM; cbn [app]; do 4 right; exact He] | rewrite FRSq; intros e He; right; exact He | rewrite SP0q; ul | exact Ha]).
  assert (NTX : parked (tab <> pix)) by (intro E; exact (NET (pix, 64) ltac:(cbn [app]; do 4 right; exact PIN) (eq_sym E))).
  assert (NCAX : parked (carr <> pix)) by (intro E; exact (NECA (pix, 64) ltac:(cbn [app]; do 4 right; exact PIN) (eq_sym E))).
  assert (NCMX : parked (cmap <> pix)) by (intro E; exact (NECM (pix, 64) ltac:(cbn [app]; do 4 right; exact PIN) (eq_sym E))).
  chunk_facts RT AF GP tab 1024. chunk_facts RT AF GP carr 1024. chunk_facts RT AF GP cmap 24.
  fframe_chunk RT AF fr 2%nat 256 tab 1024. fframe_chunk RT AF fr 2%nat 256 carr 1024. fframe_chunk RT AF fr 2%nat 256 cmap 24.
  apart2 RT AF ATX tab 1024 pix 64 NTX. apart2 RT AF ACAX carr 1024 pix 64 NCAX. apart2 RT AF ACMX cmap 24 pix 64 NCMX.
  pose proof (af_live_align RT AF Σq mq tab _ ARTQ TBIN) as TB16. pose proof (proj1 (af_live_range RT AF Σq mq tab _ ARTQ TBIN)) as TB0.
  park_disj. park_ne.
  hide NET. hide NECA. hide NECM.
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  ctx_gc RT.
  idtac "MARK qtab names".
  (* [comment removed for export] *)
  Time walk_to AF MST [(usp - 320, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [e_pixcmapSetBlackAndWhite; 0x9f7b4].
  try fold_mkR.
  idtac "MARK at setbw".
  (* [comment removed for export] *)
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx) as P1; destruct (NFA _ Hx) as [N1 N2]; clear - P1 N1 N2 LOW LOR SPT SPA SPB FR0 FR64;
                      unfold shad, SHB in *; repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
  eapply cps_seq.
  { pose proof SETBW as SB; unfold pixcmapSetBlackAndWhite00_cps in SB.
    eapply SB with (lo := lo) (cmap := cmap); [exact FDO| exact MST| reflexivity| reflexivity| reflexivity| reflexivity| exact CMO| lenv_tac|].
    unfold lres; repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end;
    cbn [length]; unfold FRAMES_MAX, LIVE_MAX in *; unfold LVF in *;
    repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H in * end; repeat split; [clear - FRB; lia| clear - LVB; lia| clear - CRq CRB; unfold RASTER_COST, PARSE_COST, QTAB_COST in *; cbn in CRB; lia|].
    intros p n Hp. exact (LVPq (p, n) ltac:(rewrite LVQ; exact Hp)). }
  idtac "MARK setbw applied".
  clear CMO.
  after_call RT AF.
  (* [comment removed for export] *)
  lazymatch goal with AG : agree_on (fun a => aclient ?lv ?frs ?spc a /\ outside [] a) ?ma ?mb |- _ =>
    lazymatch goal with NO : numa_obj ?lv0 ma na 50 arr ?vs |- _ =>
    assert (NOBJb : numa_obj lv mb na 50 arr vs)
      by (apply (numa_obj_keep lv ma mb na 50 arr vs); [intros b k Hb a Ha; apply AG; split; [right; right; left; exists b, k; split; [exact Hb| lia]| exact I]
         | apply (numa_obj_mono lv0); [intros e He; repeat match goal with E : rt_live RT _ = lv0 |- _ => rewrite E end; exact He | exact NO]]);
    clear NO end end.
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono LVF _ usp _ _ _ _ Hx); [first [solve [live_sub_tac] | solve [live_add_tac]]| solve [frames_sub_tac]| lia]| exact I]).
  lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ => rename S into Σb; rename A into ARTB; rename mm into mb end.
  lazymatch goal with H : cmap_obj (rt_live RT Σb) mb cmap _ |- _ => rename H into CMO end.
  (* [comment removed for export] *)
  pose proof CMO as ((cpad & CMCc) & _ & _ & COK & CNE). unfold cmap_cells in CMCc. cbn [c_arr c_depth c_nalloc c_n] in CMCc.
  pose proof (af_live_align RT AF Σb mb cmap _ ARTB ltac:(repeat match goal with E : rt_live RT Σb = _ |- _ => rewrite E end; rewrite LVQ; do 2 right; left; reflexivity)) as CM16.
  pose proof (proj1 (af_live_range RT AF Σb mb cmap _ ARTB ltac:(repeat match goal with E : rt_live RT Σb = _ |- _ => rewrite E end; rewrite LVQ; do 2 right; left; reflexivity))) as CM0.
  pose proof (af_live_align RT AF Σb mb carr _ ARTB ltac:(repeat match goal with E : rt_live RT Σb = _ |- _ => rewrite E end; rewrite LVQ; right; left; reflexivity)) as CA16.
  pose proof (proj1 (af_live_range RT AF Σb mb carr _ ARTB ltac:(repeat match goal with E : rt_live RT Σb = _ |- _ => rewrite E end; rewrite LVQ; right; left; reflexivity))) as CA0.
  clear CMO.
  assert (LVBW : rt_live RT Σb = (tab, 1024) :: (carr, 1024) :: (cmap, 24) :: (arr, 200) :: (na, 32) :: rt_live RT Σ) by (repeat match goal with E : rt_live RT Σb = _ |- _ => rewrite E end; exact LVQ).
  assert (FRSb : rt_frames RT Σb = (fr, 2%nat) :: rt_frames RT Σ) by (repeat match goal with E : rt_frames RT Σb = _ |- _ => rewrite E end; exact FRSq).
  assert (SP0b : rt_sp0 RT Σb = rt_sp0 RT Σ) by (repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; reflexivity).
  assert (CRbw : rt_credit RT Σ - 2 - PARSE_COST - QTAB_COST <= rt_credit RT Σb) by (lazymatch goal with E : rt_credit RT Σq - 1 <= rt_credit RT Σb |- _ => clear - CRq E; lia end).
  assert (LVPb : forall e, In e (rt_live RT Σb) -> 0 < snd e) by (intros e He; apply LVPq; rewrite LVQ, <- LVBW; exact He).
  sigma_gc RT Σ Σb.
  assert (NAINb : In (na, 32) (rt_live RT Σb)) by (rewrite LVBW; do 4 right; left; reflexivity).
  assert (ARINb : In (arr, 200) (rt_live RT Σb)) by (rewrite LVBW; do 3 right; left; reflexivity).
  assert (CMINb : In (cmap, 24) (rt_live RT Σb)) by (rewrite LVBW; do 2 right; left; reflexivity).
  assert (CAINb : In (carr, 1024) (rt_live RT Σb)) by (rewrite LVBW; right; left; reflexivity).
  assert (TBINb : In (tab, 1024) (rt_live RT Σb)) by (rewrite LVBW; left; reflexivity).
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  ctx_gc RT.
  idtac "MARK after setbw".
  (* [comment removed for export] *)
  Time walk_to AF MST [(usp - 320, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [e_numaDestroy].
  split_before FRM (C8 (Z_to_bv 64 na)) FNA. split_at FNA 1%nat FRMb.
  pose proof FSH as SHN. split_at SHN 16%nat SHN2. split_at SHN2 1%nat SHN3. clear SHN SHN3.
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx) as P1; destruct (NFA _ Hx) as [N1 N2]; clear - P1 N1 N2 LOW LOR SPT SPA SPB FR0 FR64;
                      unfold shad, SHB in *; repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
  lazymatch goal with H : numa_obj _ ?mc na 50 arr _ |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mc _))) _ => rename H into NOBJd end.
  eapply cps_seq.
  { pose proof NDY as ND; unfold numaDestroy_cps in ND.
    eapply ND with (lo := lo) (pna := fr + 128) (na := na) (cap := 50) (arr := arr); [exact FDO| exact MST| reflexivity| reflexivity| | exact FNA| | lenv_tac|].
    - unfold optrF. split.
      + exists fr, 2%nat. rewrite FRSb. change (fs_size 2) with 256. split; [left; reflexivity|]. split; [clear; lia|]. split; [clear; lia|].
        split; [clear - FR64; Z.div_mod_to_equations; lia|]. split; [clear - FR0; lia|]. split; [clear - FRHI SP0R1; lia|].
        replace (shad (fr + 128)) with (fr / 8 + 2147450896) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia). destruct SHN2 as [[_ B] _]. exact B.
      + pose proof FRSH as Q; unfold parked in Q. clear - Q FR0 FR64 FRSEG. unfold SEGTOP_A. repeat split; first [lia | Z.div_mod_to_equations; lia].
    - lazymatch goal with |- numa_obj (rt_live RT ?S) _ _ _ _ _ => replace (rt_live RT S) with (rt_live RT Σb) by (repeat match goal with E : rt_live RT S = _ |- _ => rewrite E end; reflexivity) end. exact NOBJd.
    - unfold lres; repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end;
      cbn [length]; unfold FRAMES_MAX, LIVE_MAX in *; unfold LVF in *;
      repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H in * end; repeat split; [clear - FRB; lia| clear - LVB; lia| clear - CRbw CRB; unfold RASTER_COST, PARSE_COST, QTAB_COST in *; cbn in CRB; lia|].
      intros p n Hp. exact (LVPb (p, n) ltac:(rewrite LVBW; exact Hp)). }
  idtac "MARK ndestroy applied".
  clear FNA SHN2 NOBJd.
  (* [comment removed for export] *)
  assert (SUBN : forall e, In e (rt_live RT Σ) -> fst e <> na)
    by (intros e He; apply (fresh_chunk_ne RT AF Σb mb [(tab, 1024); (carr, 1024); (cmap, 24); (arr, 200)] na 32 (rt_live RT Σ) e ARTB LVBW ltac:(cbn [app]; do 4 right; exact He) ltac:(clear; lia));
        apply LVPb; rewrite LVBW; do 5 right; exact He).
  assert (SUBAR : forall e, In e (rt_live RT Σ) -> fst e <> arr)
    by (intros e He; apply (fresh_chunk_ne RT AF Σb mb [(tab, 1024); (carr, 1024); (cmap, 24)] arr 200 ((na, 32) :: rt_live RT Σ) e ARTB LVBW ltac:(cbn [app]; do 4 right; exact He) ltac:(clear; lia));
        apply LVPb; rewrite LVBW; do 5 right; exact He).
  assert (NCMNA : parked (cmap <> na)) by (exact (fresh_chunk_ne RT AF Σb mb [(tab, 1024); (carr, 1024); (cmap, 24); (arr, 200)] na 32 (rt_live RT Σ) (cmap, 24) ARTB LVBW ltac:(cbn; tauto) ltac:(clear; lia) ltac:(cbn; clear; lia))).
  assert (NCMAR : parked (cmap <> arr)) by (exact (fresh_chunk_ne RT AF Σb mb [(tab, 1024); (carr, 1024); (cmap, 24)] arr 200 ((na, 32) :: rt_live RT Σ) (cmap, 24) ARTB LVBW ltac:(cbn; tauto) ltac:(clear; lia) ltac:(cbn; clear; lia))).
  assert (NXNA : parked (pix <> na)) by (exact (SUBN (pix, 64) PIN)).
  assert (NXAR : parked (pix <> arr)) by (exact (SUBAR (pix, 64) PIN)).
  osd_mark_about (fr + 256). osd_mark LOW. osd_mark LOR. osd_mark SPT. osd_mark SPB. osd_mark STa. osd_mark SP0R0. osd_mark SP0R1. osd_mark FR0. osd_mark FRHI. osd_mark FRSEG. osd_mark FRSH. osd_mark FR64.
  after_call RT AF.
  osd_clear.
  lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ => rename S into Σd; rename A into ARTD; rename mm into md end.
  lazymatch goal with H : rt_live RT Σd = numa_gone na arr _ |- _ => rename H into LVDN end.
  lazymatch goal with H : rw_cells asegs md (fr + 128) [C8 (Z_to_bv 64 0)] |- _ => rename H into FNA end.
  unfold hid in NET, NECA, NECM.
  assert (LVD : rt_live RT Σd = (tab, 1024) :: (carr, 1024) :: (cmap, 24) :: rt_live RT Σ).
  { rewrite LVDN, LVBW. unfold numa_gone.
    rewrite (live_remove_other arr tab) by (apply not_eq_sym; exact (NET (arr, 200) ltac:(cbn; tauto))).
    rewrite (live_remove_other arr carr) by (apply not_eq_sym; exact (NECA (arr, 200) ltac:(cbn; tauto))).
    rewrite (live_remove_other arr cmap) by (apply not_eq_sym; exact (NECM (arr, 200) ltac:(cbn; tauto))).
    rewrite live_remove_head. rewrite (live_remove_other arr na) by (unpark NANE; exact (not_eq_sym NANE)).
    rewrite (live_remove_fresh arr (rt_live RT Σ)) by (exact SUBAR).
    rewrite (live_remove_other na tab) by (apply not_eq_sym; exact (NET (na, 32) ltac:(cbn; tauto))).
    rewrite (live_remove_other na carr) by (apply not_eq_sym; exact (NECA (na, 32) ltac:(cbn; tauto))).
    rewrite (live_remove_other na cmap) by (apply not_eq_sym; exact (NECM (na, 32) ltac:(cbn; tauto))).
    rewrite live_remove_head. rewrite (live_remove_fresh na (rt_live RT Σ)) by (exact SUBN). reflexivity. }
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono LVF _ usp _ _ _ _ Hx); [intros e He; rewrite LVD; do 3 right; exact He| solve [frames_sub_tac]| lia]|
                                 cbn [outside]; destruct (NFA _ Hx) as [N1 N2]; clear - N1 N2; repeat split; try exact I; lia]).
  assert (FRSd : rt_frames RT Σd = (fr, 2%nat) :: rt_frames RT Σ) by (repeat match goal with E : rt_frames RT Σd = _ |- _ => rewrite E end; exact FRSb).
  assert (SP0d : rt_sp0 RT Σd = rt_sp0 RT Σ) by (repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; reflexivity).
  assert (CRd : rt_credit RT Σ - 2 - PARSE_COST - QTAB_COST <= rt_credit RT Σd) by (lazymatch goal with E : rt_credit RT Σb <= rt_credit RT Σd |- _ => clear - CRbw E; lia end).
  assert (LVPd : forall e, In e (rt_live RT Σd) -> 0 < snd e) by (intros e He; apply LVPb; rewrite LVBW; rewrite LVD in He; cbn [In] in He |- *; tauto).
  join_cells FRM FNA. join_cells FRM FRMb.
  clear NET NECA NECM SUBN SUBAR. try clear NCNA. try clear NCAR. try clear NNX. try clear NAX. try clear NA0. try clear AR0. try clear NA16. try clear AR16. try clear NANE. try clear NCAP. try clear NLEN. try clear npad. try clear njunk.
  sigma_gc RT Σ Σd.
  assert (LSUBd : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σd)) by (intros e He; rewrite LVD; do 3 right; exact He).
  assert (CMINd : In (cmap, 24) (rt_live RT Σd)) by (rewrite LVD; do 2 right; left; reflexivity).
  assert (CAINd : In (carr, 1024) (rt_live RT Σd)) by (rewrite LVD; right; left; reflexivity).
  assert (TBINd : In (tab, 1024) (rt_live RT Σd)) by (rewrite LVD; left; reflexivity).
  repeat match goal with H : context [arr] |- _ => clear H end. repeat match goal with H : context [na] |- _ => clear H end. try clear arr. try clear na.
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  ctx_gc RT.
  idtac "MARK after ndestroy".
  (* [comment removed for export] *)
  Time walk_to AF MST [(usp - 320, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [e_pixCreate].
  try fold_mkR.
  idtac "MARK at pixCreate".
  try rewrite D8 in PXC.
  pose proof POBJ0 as HP. unfold hid in HP. destruct HP as (_ & _ & HDROK & _).
  (* [comment removed for export] *)
  rewrite !(sx32_small (p_w v)) by (clear - HDROK; destruct HDROK as (_ & Q & _); lia).
  rewrite !(sx32_small (p_h v)) by (clear - HDROK; destruct HDROK as (_ & _ & Q & _); lia).
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); destruct (NFA _ Hx) as [N1 N2]; unfold shad, SHB in *;
                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
  assert (HAO : hdr_args_ok (p_w v) (p_h v) 8).
  { clear - HDROK D8. destruct HDROK as (Q1 & Q2 & Q3 & Q4 & Q5). rewrite D8 in Q4. rewrite Q4 in Q5.
    unfold hdr_args_ok. split; [cbn [In]; tauto|]. split; [exact Q2|]. split; [exact Q3| exact Q5]. }
  assert (LVPt : forall p n, In (p, n) (rt_live RT Σd) -> 0 < n) by (intros p n Hp; exact (LVPd (p, n) Hp)).
  idtac "MARK at pixCreate".
  eapply cps_seq.
  { pose proof PCS as PC1; unfold pixCreate_sure_cps in PC1.
    eapply PC1 with (lo := lo) (w := p_w v) (h := p_h v) (d := 8).
    - exact FDO.
    - exact MST.
    - reflexivity.
    - split; [clear - HAO; unfold hdr_args_ok in HAO; lia| reflexivity].
    - split; [clear - HAO; unfold hdr_args_ok in HAO; lia| reflexivity].
    - split; [lia| reflexivity].
    - exact HAO.
    - lenv_tac.
    - unfold lres; unfold FRAMES_MAX, LIVE_MAX, RASTER_COST, PARSE_COST, QTAB_COST in *; unfold LVF in *;
      split; [rewrite FRSd; cbn [length]; clear - FRB; lia|]; split; [rewrite LVD; cbn [length]; clear - LVB; lia|]; split; [clear - CRB CRd; lia| exact LVPt]. }
  idtac "MARK pixCreate applied".
  after_call RT AF.
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono LVF _ usp _ _ _ _ Hx); [first [solve [live_sub_tac] | solve [live_add_tac]]| solve [frames_sub_tac]| lia]| exact I]).
  idtac "MARK after pixCreate".
  lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ => rename S into Σc; rename A into ARTC end.
  lazymatch goal with H : pix_obj (rt_live RT Σc) _ ?p ?vv _ |- _ => rename H into POD; rename p into pixd; rename vv into v1 end.
  lazymatch goal with H : rt_live RT Σc = _ |- _ => rename H into LVN end.
  lazymatch goal with H : p_w v1 = _ |- _ => rename H into VW end.
  lazymatch goal with H : p_h v1 = _ |- _ => rename H into VH end.
  lazymatch goal with H : p_d v1 = _ |- _ => rename H into VD end.
  lazymatch goal with H : p_data v1 <> 0 |- _ => rename H into VDATA1 end.
  lazymatch goal with H : p_cmap v1 = 0 |- _ => rename H into VCMAP end.
  assert (FRSc : rt_frames RT Σc = (fr, 2%nat) :: rt_frames RT Σ) by (repeat match goal with E : rt_frames RT Σc = _ |- _ => rewrite E end; exact FRSd).
  assert (LVC : rt_live RT Σc = (p_data v1, rsize v1) :: (pixd, 64) :: (tab, 1024) :: (carr, 1024) :: (cmap, 24) :: rt_live RT Σ)
    by (rewrite LVN; rewrite LVD; reflexivity).
  assert (SP0C : rt_sp0 RT Σc = rt_sp0 RT Σ) by (repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; reflexivity).
  lazymatch goal with H : rt_credit RT Σd - _ <= rt_credit RT Σc |- _ => rename H into CRN end.
  assert (CRC : rt_credit RT Σ - (RASTER_COST + 22) <= rt_credit RT Σc) by (clear - CRd CRN; unfold PARSE_COST, QTAB_COST in *; lia).
  pose proof POD as (PXD & (PDIN & PD0 & PD16 & _) & HOKD & PDDATA & _).
  destruct PDDATA as [PDZ|((DDIN & DD0 & DD16 & DDN) & DDNE)]; [exfalso; exact (VDATA1 PDZ)|].
  set (dat := p_data v1) in *. set (rs := rsize v1) in *.
  idtac "MARK names c".
  assert (SUBP : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σc) /\ fst e <> pixd)
    by (intros e He; split; [rewrite LVC; do 5 right; exact He|];
        apply (fresh_chunk_ne RT AF Σc _ [(dat, rs)] pixd 64 _ e ARTC LVC); [ cbn [app In]; do 4 right; exact He | lia | destruct e as [eq ek]; exact (LVP eq ek He) ]).
  assert (SUBD : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σc) /\ fst e <> dat)
    by (intros e He; split; [rewrite LVC; do 5 right; exact He|];
        apply (fresh_chunk_ne RT AF Σc _ [] dat rs _ e ARTC LVC); [ cbn [app In]; do 4 right; exact He | lia | destruct e as [eq ek]; exact (LVP eq ek He) ]).
  assert (NCP : forall a, PF0 a -> a < pixd \/ pixd + 64 <= a)
    by (intros a Ha; apply (inner_chunk_apart RT AF Σc _ pixd 64 (rt_live RT Σ) (rt_frames RT Σ) usp a ARTC PDIN SUBP);
        [ rewrite FRSc; intros e He; right; exact He | rewrite SP0C; ul | exact Ha ]).
  assert (NCD : forall a, PF0 a -> a < dat \/ dat + rs <= a)
    by (intros a Ha; apply (inner_chunk_apart RT AF Σc _ dat rs (rt_live RT Σ) (rt_frames RT Σ) usp a ARTC DDIN SUBD);
        [ rewrite FRSc; intros e He; right; exact He | rewrite SP0C; ul | exact Ha ]).
  assert (NPS : pix <> pixd) by (exact (proj2 (SUBP (pix, 64) PIN))).
  assert (NPS0 : pixd <> pix) by (intro E; apply NPS; symmetry; exact E).
  assert (NDS : pix <> dat) by (exact (proj2 (SUBD (pix, 64) PIN))).
  assert (NDS0 : dat <> pix) by (intro E; apply NDS; symmetry; exact E).
  assert (NSP : p_data v <> pixd) by (exact (proj2 (SUBP (p_data v, 4 * (p_wpl v * p_h v)) DIN))).
  assert (NSD : p_data v <> dat) by (exact (proj2 (SUBD (p_data v, 4 * (p_wpl v * p_h v)) DIN))).
  idtac "MARK apart c".
  chunk_facts RT AF GP pixd 64. chunk_facts RT AF GP dat rs.
  fframe_chunk RT AF fr 2%nat 256 pixd 64. fframe_chunk RT AF fr 2%nat 256 dat rs.
  park_disj.
  unfold pix_cells in PXD. rewrite VW, VH, VD, VCMAP in PXD. fold dat in PXD.
  assert (EWD : p_wpl v1 = p_wpl v) by (destruct HOKD as (_ & _ & _ & Q4 & _); destruct HDROK as (_ & _ & _ & R4 & _); rewrite VW, VD in Q4; rewrite D8 in R4; rewrite Q4, R4; reflexivity).
  assert (ERS : rs = 4 * (p_wpl v * p_h v)) by (unfold rs, rsize; rewrite VH, EWD; reflexivity).
  assert (RSD : 0 < 4 * (p_wpl v * p_h v) <= 67108864) by (destruct HDROK as (_ & _ & _ & _ & Q5); exact Q5).
  rewrite EWD in PXD.
  assert (NPCM : pixd <> cmap) by (intro E; exact (fresh_chunk_ne RT AF Σc _ [(dat, rs)] pixd 64 _ (cmap, 24) ARTC LVC ltac:(cbn; tauto) ltac:(clear; lia) ltac:(cbn; clear; lia) (eq_sym E))).
  assert (NDCM : dat <> cmap) by (intro E; exact (fresh_chunk_ne RT AF Σc _ [] dat rs _ (cmap, 24) ARTC LVC ltac:(cbn; tauto) ltac:(clear - RSD ERS; lia) ltac:(cbn; clear; lia) (eq_sym E))).
  assert (NPCA : pixd <> carr) by (intro E; exact (fresh_chunk_ne RT AF Σc _ [(dat, rs)] pixd 64 _ (carr, 1024) ARTC LVC ltac:(cbn; tauto) ltac:(clear; lia) ltac:(cbn; clear; lia) (eq_sym E))).
  assert (NDCA : dat <> carr) by (intro E; exact (fresh_chunk_ne RT AF Σc _ [] dat rs _ (carr, 1024) ARTC LVC ltac:(cbn; tauto) ltac:(clear - RSD ERS; lia) ltac:(cbn; clear; lia) (eq_sym E))).
  assert (NPTB : pixd <> tab) by (intro E; exact (fresh_chunk_ne RT AF Σc _ [(dat, rs)] pixd 64 _ (tab, 1024) ARTC LVC ltac:(cbn; tauto) ltac:(clear; lia) ltac:(cbn; clear; lia) (eq_sym E))).
  assert (NDTB : dat <> tab) by (intro E; exact (fresh_chunk_ne RT AF Σc _ [] dat rs _ (tab, 1024) ARTC LVC ltac:(cbn; tauto) ltac:(clear - RSD ERS; lia) ltac:(cbn; clear; lia) (eq_sym E))).
  apart2 RT AF APP pixd 64 pix 64 NPS0. apart2 RT AF APCM pixd 64 cmap 24 NPCM.
  apart2 RT AF ADP dat rs pix 64 NDS0. apart2 RT AF ADX dat rs pixd 64 DDNE. apart2 RT AF ADCM dat rs cmap 24 NDCM.
  park_disj.
  hide POD. hide SUBP. hide SUBD. hide HOKD.
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  ctx_gc RT.
  park_ne.
  idtac "MARK before PCR".
  Time walk_to AF MST [(usp - 320, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [e_pixCopyResolution].
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx) as P1; destruct (NFA _ Hx) as [N1 N2]; clear - P1 N1 N2 LOW LOR SPT SPA SPB FR0 FR64;
                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
  assert (LSUB : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σc)) by (intros e He; rewrite LVC; do 5 right; exact He).
  unfold hid in POD, POBJ0.
  lazymatch goal with PX : rw_cells asegs ?mc pixd _, PS : rw_cells asegs ?mc pix _ |- cps _ (ASTA RT Σc _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
    assert (POD1 : pix_obj (rt_live RT Σc) mc pixd v1 (mkCmapv 0 0 0 0))
      by (destruct POD as (_ & CH & HOK & HD & _); split; [unfold pix_cells; rewrite VW, VH, VD, VCMAP, EWD; exact PX| split; [exact CH| split; [exact HOK| split; [exact HD| left; exact VCMAP]]]]);
    assert (POS1 : pix_obj (rt_live RT Σc) mc pix v cv)
      by (apply (pix_obj_mono (rt_live RT Σ) _ mc pix v cv LSUB); apply (pix_obj_agree (rt_live RT Σ) PF0 m mc pix v cv POBJ0 AGF PML); unfold pix_cells; rewrite D8; exact PS) end.
  hide POD. hide POBJ0.
  idtac "MARK objs for PCR".
  eapply cps_seq.
  { pose proof PCR as PCR1; unfold pixCopyResolution_cps in PCR1.
    eapply PCR1 with (lo := lo) (pixd := pixd) (pixs := pix) (vd := v1) (vs := v) (cvd := mkCmapv 0 0 0 0) (cvs := cv) (rc := 1).
    - exact FDO.
    - exact MST.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - exact POD1.
    - exact POS1.
    - exact NPS0.
    - lenv_tac. }
  idtac "MARK PCR applied".
  clear POD1 POS1.
  clear PXD.
  osd_mark_about pixd.
  osd_mark LOW. osd_mark LOR. osd_mark SPT. osd_mark SPB. osd_mark STa. osd_mark SP0R0. osd_mark SP0R1. osd_mark FR0. osd_mark FRHI. osd_mark FRSEG. osd_mark FRSH.
  after_call RT AF.
  osd_clear.
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono LVF _ usp _ _ _ _ Hx); [first [solve [live_sub_tac] | solve [live_add_tac]]| solve [frames_sub_tac]| lia]|
                                  cbn [outside]; pose proof (NCP _ Hx); split; [lia| exact I]]).
  idtac "MARK after PCR".
  lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ => rename S into Σr; rename A into ARTR end.
  lazymatch goal with H : rw_cells asegs _ pixd (pix_cells _) |- _ => rename H into PXD end.
  unfold pix_cells in PXD. cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data] in PXD. rewrite VW, VH, VD, VCMAP, EWD in PXD. fold dat in PXD.
  assert (LVR : rt_live RT Σr = rt_live RT Σc) by (repeat match goal with E : rt_live RT Σr = _ |- _ => rewrite E end; reflexivity).
  assert (FRSr : rt_frames RT Σr = (fr, 2%nat) :: rt_frames RT Σ) by (repeat match goal with E : rt_frames RT Σr = _ |- _ => rewrite E end; exact FRSc).
  assert (SP0r : rt_sp0 RT Σr = rt_sp0 RT Σ) by (repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; reflexivity).
  assert (CRr : rt_credit RT Σ - (RASTER_COST + 22) <= rt_credit RT Σr) by (lazymatch goal with E : rt_credit RT Σc <= rt_credit RT Σr |- _ => clear - E CRC; lia end).
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  ctx_gc RT.
  Time walk_to AF MST [(usp - 320, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [e_pixCopyInputFormat].
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx) as P1; destruct (NFA _ Hx) as [N1 N2]; clear - P1 N1 N2 LOW LOR SPT SPA SPB FR0 FR64;
                      repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
  assert (LSUBr : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σr)) by (intros e He; rewrite LVR; apply LSUB; exact He).
  unfold hid in POD, POBJ0.
  lazymatch goal with PX : rw_cells asegs ?mc pixd _, PS : rw_cells asegs ?mc pix _ |- cps _ (ASTA RT Σr _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
    assert (POD2 : pix_obj (rt_live RT Σr) mc pixd (pv_res v1 v) (mkCmapv 0 0 0 0))
      by (destruct POD as (_ & CH & HOK & HD & _); rewrite LVR;
          split; [unfold pix_cells, pv_res; cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data]; rewrite VW, VH, VD, VCMAP, EWD; exact PX|
          split; [exact CH| split; [exact HOK| split; [exact HD| left; exact VCMAP]]]]);
    assert (POS2 : pix_obj (rt_live RT Σr) mc pix v cv)
      by (apply (pix_obj_mono (rt_live RT Σ) _ mc pix v cv LSUBr); apply (pix_obj_agree (rt_live RT Σ) PF0 m mc pix v cv POBJ0 AGF PML); unfold pix_cells; rewrite D8; exact PS) end.
  hide POD. hide POBJ0.
  eapply cps_seq.
  { pose proof PCI as PCI1; unfold pixCopyInputFormat_cps in PCI1.
    eapply PCI1 with (lo := lo) (pixd := pixd) (pixs := pix) (vd := pv_res v1 v) (vs := v) (cvd := mkCmapv 0 0 0 0) (cvs := cv) (rc := 1).
    - exact FDO.
    - exact MST.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - exact POD2.
    - exact POS2.
    - exact NPS0.
    - lenv_tac. }
  clear POD2 POS2.
  idtac "MARK PCI applied".
  clear PXD.
  osd_mark_about pixd.
  osd_mark LOW. osd_mark LOR. osd_mark SPT. osd_mark SPB. osd_mark STa. osd_mark SP0R0. osd_mark SP0R1. osd_mark FR0. osd_mark FRHI. osd_mark FRSEG. osd_mark FRSH.
  after_call RT AF.
  osd_clear.
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono LVF _ usp _ _ _ _ Hx); [first [solve [live_sub_tac] | solve [live_add_tac]]| solve [frames_sub_tac]| lia]|
                                  cbn [outside]; pose proof (NCP _ Hx); split; [lia| exact I]]).
  lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ => rename S into Σi; rename A into ARTI end.
  lazymatch goal with H : rw_cells asegs _ pixd (pix_cells _) |- _ => rename H into PXD end.
  unfold pix_cells, pv_inf, pv_res in PXD. cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data] in PXD. rewrite VW, VH, VD, VCMAP, EWD in PXD. fold dat in PXD.
  assert (LVI : rt_live RT Σi = rt_live RT Σc) by (repeat match goal with E : rt_live RT Σi = _ |- _ => rewrite E end; exact LVR).
  assert (FRSi : rt_frames RT Σi = (fr, 2%nat) :: rt_frames RT Σ) by (repeat match goal with E : rt_frames RT Σi = _ |- _ => rewrite E end; exact FRSr).
  assert (SP0i : rt_sp0 RT Σi = rt_sp0 RT Σ) by (repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; reflexivity).
  assert (CRi : rt_credit RT Σ - (RASTER_COST + 22) <= rt_credit RT Σi) by (lazymatch goal with E : rt_credit RT Σr <= rt_credit RT Σi |- _ => clear - E CRr; lia end).
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  ctx_gc RT.
  idtac "MARK after PCI".
  (* [comment removed for export] *)
  Time walk_to AF MST [(usp - 320, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [e_pixSetColormap].
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx) as P1; destruct (NFA _ Hx) as [N1 N2]; clear - P1 N1 N2 LOW LOR SPT SPA SPB FR0 FR64;
                      unfold shad, SHB in *; repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
  assert (LSUBi : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σi)) by (intros e He; rewrite LVI; apply LSUB; exact He).
  assert (CMINi : In (cmap, 24) (rt_live RT Σi)) by (rewrite LVI, LVC; do 4 right; left; reflexivity).
  assert (CAINi : In (carr, 1024) (rt_live RT Σi)) by (rewrite LVI, LVC; do 3 right; left; reflexivity).
  unfold hid in POD.
  lazymatch goal with PX : rw_cells asegs ?mc pixd _, CC : rw_cells asegs ?mc cmap _ |- cps _ (ASTA RT Σi _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
    assert (POD3 : pix_obj (rt_live RT Σi) mc pixd (pv_inf (pv_res v1 v) v) (mkCmapv carr 8 256 5))
      by (destruct POD as (_ & CH & HOK & HD & _); rewrite LVI;
          split; [unfold pix_cells, pv_inf, pv_res; cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data]; rewrite VW, VH, VD, VCMAP, EWD; exact PX|
          split; [exact CH| split; [exact HOK| split; [exact HD| left; exact VCMAP]]]]);
    assert (CMOi : cmap_obj (rt_live RT Σi) mc cmap (mkCmapv carr 8 256 5))
      by (split; [exists cpad; unfold cmap_cells; cbn [c_arr c_depth c_nalloc c_n]; exact CC|];
          split; [split; [exact CMINi| split; [exact CM0| split; [exact CM16| clear; lia]]]|];
          split; [cbn [c_arr c_nalloc]; split; [exact CAINi| split; [exact CA0| split; [exact CA16| clear; lia]]]|];
          split; [exact COK| cbn [c_arr]; exact CNE]) end.
  hide POD.
  idtac "MARK objs for setcmap".
  eapply cps_seq.
  { pose proof SCM as SC; unfold pixSetColormap_cps in SC.
    eapply SC with (lo := lo) (pix := pixd) (cmap := cmap) (v := pv_inf (pv_res v1 v) v) (cv := mkCmapv carr 8 256 5).
    - exact FDO.
    - exact MST.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - exact POD3.
    - exact VCMAP.
    - exact VDATA1.
    - exact CMOi.
    - exact (not_eq_sym NPCM).
    - cbn [c_arr]. exact (not_eq_sym NPCA).
    - unfold pv_inf, pv_res; cbn [p_data]. fold dat. exact (not_eq_sym NDCM).
    - unfold pv_inf, pv_res; cbn [p_data c_arr]. fold dat. exact (not_eq_sym NDCA).
    - lenv_tac.
    - unfold lres; repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; rewrite LVI, LVC;
      cbn [length]; unfold FRAMES_MAX, LIVE_MAX in *; unfold LVF in *;
      repeat split; [clear - FRB; lia| clear - LVB; lia| clear - CRi CRB; unfold RASTER_COST in *; lia|].
      intros p n Hp. cbn [In] in Hp. destruct Hp as [E|[E|[E|[E|[E|Hp]]]]]; [injection E as <- <-; first [exact DDN | clear - RSD0 ERS; lia | clear - ERS HRS0 EWD; lia]| injection E as <- <-; clear; lia| injection E as <- <-; clear; lia| injection E as <- <-; clear; lia| injection E as <- <-; clear; lia| exact (LVP p n Hp)]. }
  idtac "MARK setcmap applied".
  clear POD3 CMOi PXD.
  osd_mark_about pixd.
  osd_mark LOW. osd_mark LOR. osd_mark SPT. osd_mark SPB. osd_mark STa. osd_mark SP0R0. osd_mark SP0R1. osd_mark FR0. osd_mark FRHI. osd_mark FRSEG. osd_mark FRSH. osd_mark FR64.
  after_call RT AF.
  osd_clear.
  fold_ag ltac:(fun Hx => split; [apply (aclient_mono LVF _ usp _ _ _ _ Hx); [first [solve [live_sub_tac] | solve [live_add_tac]]| solve [frames_sub_tac]| lia]|
                                  cbn [outside]; pose proof (NCP _ Hx); split; [lia| exact I]]).
  lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ => rename S into Σs; rename A into ARTS end.
  lazymatch goal with H : rw_cells asegs _ pixd (pix_cells _) |- _ => rename H into PXD end.
  unfold pix_cells, pv_inf, pv_res in PXD. cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data] in PXD. rewrite VW, VH, VD, EWD in PXD. fold dat in PXD.
  assert (LVS : rt_live RT Σs = (dat, rs) :: (pixd, 64) :: (tab, 1024) :: (carr, 1024) :: (cmap, 24) :: rt_live RT Σ) by (repeat match goal with E : rt_live RT Σs = _ |- _ => rewrite E end; rewrite LVI; exact LVC).
  assert (FRSs : rt_frames RT Σs = (fr, 2%nat) :: rt_frames RT Σ) by (repeat match goal with E : rt_frames RT Σs = _ |- _ => rewrite E end; exact FRSi).
  assert (SP0s : rt_sp0 RT Σs = rt_sp0 RT Σ) by (repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; reflexivity).
  assert (CRs : rt_credit RT Σ - (RASTER_COST + 28) <= rt_credit RT Σs) by (lazymatch goal with E : rt_credit RT Σi - 6 <= rt_credit RT Σs |- _ => clear - E CRi; lia end).
  sigma_gc RT Σ Σs.
  assert (LSUBs : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σs)) by (intros e He; rewrite LVS; do 5 right; exact He).
  assert (PDINs : In (pixd, 64) (rt_live RT Σs)) by (rewrite LVS; right; left; reflexivity).
  assert (DDINs : In (dat, rs) (rt_live RT Σs)) by (rewrite LVS; left; reflexivity).
  assert (CMINs : In (cmap, 24) (rt_live RT Σs)) by (rewrite LVS; do 4 right; left; reflexivity).
  assert (CAINs : In (carr, 1024) (rt_live RT Σs)) by (rewrite LVS; do 3 right; left; reflexivity).
  assert (TBINs : In (tab, 1024) (rt_live RT Σs)) by (rewrite LVS; do 2 right; left; reflexivity).
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  ctx_gc RT.
  idtac "MARK after setcmap".
  (* [comment removed for export] *)
  Time walk_to AF MST [(usp - 320, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [e_pixRemoveColormap].
  try fold_mkR.
  idtac "MARK at rmc".
  (* [comment removed for export] *)
  assert (TRR : p_cmap v <> 0 -> Forall (fun f => In (f :: bv_unsigned (Z_to_bv 64 0x9fdec) :: bv_unsigned ra :: ras) CLIENT_TRACES \/ In [f] CLIENT_TRACES) REMOVE_RAS).
  { intros _. rewrite RAF, RAS. rewrite unsigned_lit by (clear; lia). unfold REMOVE_RAS, RA_FUZZ_OP6, D_libiface.RA_TOP.
    repeat (apply Forall_cons; [first [left; apply ct_mem_In; vm_compute; reflexivity | right; apply ct_mem_In; vm_compute; reflexivity] |]). apply Forall_nil. }
  pose proof FR as FRrec. split_before FRrec (C8 s0) FRrec2. clear FRrec.
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx) as P1; destruct (NFA _ Hx) as [N1 N2]; clear - P1 N1 N2 LOW LOR SPT SPA SPB FR0 FR64;
                      unfold shad, SHB in *; repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
  unfold hid in POBJ0.
  lazymatch goal with PS : rw_cells asegs ?mc pix _ |- cps _ (ASTA RT Σs _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
    assert (POS : pix_obj (rt_live RT Σs) mc pix v cv)
      by (apply (pix_obj_mono (rt_live RT Σ) _ mc pix v cv LSUBs); apply (pix_obj_agree (rt_live RT Σ) PF0 m mc pix v cv POBJ0 AGF PML); unfold pix_cells; rewrite D8; exact PS) end.
  hide POBJ0.
  idtac "MARK objs for rmc".
  eapply cps_seq.
  { pose proof RMC as RM; unfold pixRemoveColormap_gray_cps in RM.
    eapply RM with (lo := lo) (pix := pix) (v := v) (cv := cv) (ras := bv_unsigned ra :: ras).
    - exact FDO.
    - exact MST.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - exact POS.
    - exact D8.
    - exact VDATA.
    - exact CNZ.
    - unfold uctx. rewrite !unsigned_lit by (clear - USP0 USP1 LOR STa; lia). apply CHAIN; [apply AGS0; exact AGF|].
      lazymatch type of FRrec2 with rw_cells _ _ ?A _ => replace (usp + -16) with A by (clear; lia) end. exact FRrec2.
    - exact TRR.
    - lenv_tac.
    - unfold lres; repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; rewrite LVS;
      cbn [length]; unfold FRAMES_MAX, LIVE_MAX, REMOVE_COST in *; unfold LVF in *;
      repeat split; [clear - FRB; lia| clear - LVB; lia| clear - CRs CRB; unfold RASTER_COST in *; lia|].
      intros p n Hp. cbn [In] in Hp. destruct Hp as [E|[E|[E|[E|[E|Hp]]]]]; [injection E as <- <-; first [exact DDN | clear - RSD0 ERS; lia | clear - ERS HRS0 EWD; lia]| injection E as <- <-; clear; lia| injection E as <- <-; clear; lia| injection E as <- <-; clear; lia| injection E as <- <-; clear; lia| exact (LVP p n Hp)]. }
  idtac "MARK rmc applied".
  clear POS FRrec2. clear PXC.
  (* [comment removed for export] *)
  lazymatch type of AGF with agree_on PF0 m ?mc => assert (AGF1 : agree_on PF m mc) by (eapply agree_sub; [exact AGF| intros zz [Hz _]; exact Hz]) end.
  clear AGF. rename AGF1 into AGF.
  osd_mark_about pix.
  osd_mark LOW. osd_mark LOR. osd_mark SPT. osd_mark SPB. osd_mark STa. osd_mark SP0R0. osd_mark SP0R1. osd_mark FR0. osd_mark FRHI. osd_mark FRSEG. osd_mark FRSH. osd_mark FR64.
  after_call RT AF.
  osd_clear.
  fold_ag ltac:(fun Hx => destruct Hx as [Hx Ho]; split; [apply (aclient_mono LVF _ usp _ _ _ _ Hx); [first [solve [live_sub_tac] | solve [live_add_tac] | intros e He; rewrite LVS; do 5 right; exact He]| solve [frames_sub_tac]| lia]| exact Ho]).
  idtac "MARK after rmc".
  lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ => rename S into Σr; rename A into ARTR; rename mm into mr end.
  lazymatch goal with H : p_cmap v = 0 -> rt_live RT Σr = _ |- _ => rename H into LVR0 end.
  lazymatch goal with H : p_cmap v <> 0 -> rt_live RT Σr = _ |- _ => rename H into LVR1 end.
  assert (FRSr : rt_frames RT Σr = (fr, 2%nat) :: rt_frames RT Σ) by (repeat match goal with E : rt_frames RT Σr = _ |- _ => rewrite E end; exact FRSs).
  assert (SP0r : rt_sp0 RT Σr = rt_sp0 RT Σ) by (repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; reflexivity).
  assert (CRr : rt_credit RT Σ - (2 * RASTER_COST + 44) <= rt_credit RT Σr) by (lazymatch goal with E : rt_credit RT Σs - REMOVE_COST <= rt_credit RT Σr |- _ => clear - E CRs; unfold REMOVE_COST in E; lia end).
  (* [comment removed for export] *)
  local_accn FSH fr 20%nat 160 8 FR64 ACCPT2.
  lazymatch goal with H : _ \/ _ |- cps _ _ _ => destruct H as [(CMZ & EQT & POSR) | (CMNZ & POSR & POTR & VWT & VHT & VDT & VDATAT & VCMAPT)] end.
  - (* [comment removed for export] *)
    idtac "MARK clone case".
    subst x4 || (lazymatch type of EQT with ?r = pix => subst r end).
    specialize (LVR0 CMZ). clear LVR1.
    assert (LVR : rt_live RT Σr = (dat, rs) :: (pixd, 64) :: (tab, 1024) :: (carr, 1024) :: (cmap, 24) :: rt_live RT Σ) by (rewrite LVR0; exact LVS).
    sigma_gc RT Σ Σr.
    pose proof POSR as (PXC2 & _ & _ & _ & _). unfold pix_cells_rc in PXC2. rewrite D8 in PXC2 || idtac.
    assert (LSUBr : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σr)) by (intros e He; rewrite LVR; do 5 right; exact He).
    assert (PDINr : In (pixd, 64) (rt_live RT Σr)) by (rewrite LVR; right; left; reflexivity).
    assert (DDINr : In (dat, rs) (rt_live RT Σr)) by (rewrite LVR; left; reflexivity).
    assert (CMINr : In (cmap, 24) (rt_live RT Σr)) by (rewrite LVR; do 4 right; left; reflexivity).
    assert (CAINr : In (carr, 1024) (rt_live RT Σr)) by (rewrite LVR; do 3 right; left; reflexivity).
    assert (TBINr : In (tab, 1024) (rt_live RT Σr)) by (rewrite LVR; do 2 right; left; reflexivity).
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
    ctx_gc RT.
    idtac "MARK clone names".
    (* [comment removed for export] *)
    Time walk_to AF MST [(usp - 320, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [0xa0018; 0xa0000; 0xa00e4].
    try fold_mkR.
    idtac "MARK clone at loop setup".
    (* [comment removed for export] *)
    assert (HW1 : 0 < p_w v <= 20000) by (clear - HW0 HW2; lia). assert (HH1 : 0 < p_h v <= 20000) by (clear - HH0 HH2; lia).
    assert (WPLB : 0 < p_wpl v <= 5001) by (rewrite HWPL; clear - HW1; Z.div_mod_to_equations; lia).
    rewrite !(sx32_small (p_h v)) by (clear - HH1; lia). rewrite !(sx32_small (p_wpl v)) by (clear - WPLB; lia).
    lstep. brF.
    Time awalk [0xa0040; 0xa00e4].
    rewrite ?(unsigned_lit (p_wpl v)) by (clear - WPLB; lia). replace (p_wpl v * 4) with (4 * p_wpl v) by (clear; lia).
    try fold_mkR.
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
    lazymatch goal with MUx : munch _ ?mm _, A : ART RT _ ?mm |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
      agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; destruct Hx as [Hx Ho]; pose proof (PFS _ Hx) as P1; destruct (NFA _ Hx) as [N1 N2]; clear - P1 N1 N2 LOW LOR SPT SPA SPB FR0 FR64;
                                         unfold shad, SHB in *; repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end.
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
    ctx_gc RT.
    idtac "MARK clone rows art".
    rewrite (sx32_small (p_w v)) in FRM by (clear - HW1; lia). rewrite (sx32_small (p_h v)) in FRM by (clear - HH1; lia).
    pose proof FRM as T. split_before T (C4 (Z_to_bv 64 (p_w v))) T80. split_at T80 1%nat T2. clear T T2.
    pose proof FRM as T. split_before T (C4 (Z_to_bv 64 (p_h v))) T96. split_at T96 1%nat T2. clear T T2.
    pose proof FR as T. split_before T (C8 (Z_to_bv 64 tab)) S144. split_at S144 1%nat T2. clear T T2.
    assert (S8 : p_data v mod 8 = 0) by (clear - D16; Z.div_mod_to_equations; lia).
    assert (SHI : p_data v + 4 * (p_wpl v * p_h v) <= 2 ^ 47) by (clear - CKR0 SP0R1; lia).
    assert (SSH : p_data v + 4 * (p_wpl v * p_h v) <= 0x7fff7000 \/ 0x10007fff8000 <= p_data v) by (clear - CKH0; unfold parked in CKH0; lia).
    assert (SSG : p_data v + 4 * (p_wpl v * p_h v) <= 0x10000 \/ SEGTOP_A <= p_data v) by (clear - CKS0; unfold parked in CKS0; unfold SEGTOP_A; lia).
    assert (T8 : dat mod 8 = 0) by (clear - DD16; Z.div_mod_to_equations; lia).
    lazymatch goal with H : dat + rs <= rt_sp0 RT Σ - _ |- _ => rename H into CKRD end.
    lazymatch goal with H : parked (dat + rs <= 2147446784 \/ _) |- _ => rename H into CKHD end.
    lazymatch goal with H : parked (dat + rs <= 65536 \/ _) |- _ => rename H into CKSD end.
    lazymatch goal with H : parked (fr + 256 <= dat \/ _) |- _ => rename H into FCDD end.
    lazymatch goal with H : parked (dat + rs <= fr / 8 + _ \/ _) |- _ => rename H into FCSD end.
    lazymatch goal with H : tab + 1024 <= rt_sp0 RT Σ - _ |- _ => rename H into CKRT end.
    lazymatch goal with H : parked (tab + 1024 <= 2147446784 \/ _) |- _ => rename H into CKHT end.
    lazymatch goal with H : parked (tab + 1024 <= 65536 \/ _) |- _ => rename H into CKST end.
    assert (THI : dat + 4 * (p_wpl v * p_h v) <= 2 ^ 47) by (clear - CKRD ERS SP0R1; lia).
    assert (TSH : dat + 4 * (p_wpl v * p_h v) <= 0x7fff7000 \/ 0x10007fff8000 <= dat) by (clear - CKHD ERS; unfold parked in CKHD; lia).
    assert (TSG : dat + 4 * (p_wpl v * p_h v) <= 0x10000 \/ SEGTOP_A <= dat) by (clear - CKSD ERS; unfold parked in CKSD; unfold SEGTOP_A; lia).
    assert (Q8 : tab mod 8 = 0) by (clear - TB16; Z.div_mod_to_equations; lia).
    assert (QHI : tab + 1024 <= 2 ^ 47) by (clear - CKRT SP0R1; lia).
    assert (QSH : tab + 1024 <= 0x7fff7000 \/ 0x10007fff8000 <= tab) by (clear - CKHT; unfold parked in CKHT; lia).
    assert (QSG : tab + 1024 <= 0x10000 \/ SEGTOP_A <= tab) by (clear - CKST; unfold parked in CKST; unfold SEGTOP_A; lia).
    lazymatch goal with A : ART RT Σr ?mm |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mm _))) _ =>
      pose proof (live_apart2 RT AF Σr mm (p_data v) (4 * (p_wpl v * p_h v)) dat rs A (LSUBr _ DIN) DDINr ltac:(intros E; injection E as E1 E2; unpark NSD; exact (NSD E1))) as ASD;
      pose proof (live_apart2 RT AF Σr mm tab 1024 dat rs A TBINr DDINr ltac:(intros E; injection E as E1 E2; unpark NDTB; exact (NDTB (eq_sym E1)))) as AQD end.
    assert (ASD' : p_data v + 4 * (p_wpl v * p_h v) <= dat \/ dat + 4 * (p_wpl v * p_h v) <= p_data v) by (clear - ASD ERS; lia). clear ASD.
    assert (AQD' : tab + 1024 <= dat \/ dat + 4 * (p_wpl v * p_h v) <= tab) by (clear - AQD ERS; lia). clear AQD.
    assert (W0 : 0 < fr + 80) by (clear - FR0; lia). assert (WHI : fr + 80 + 4 <= 2 ^ 47) by (clear - FRHI SP0R1; lia).
    assert (WSEP : fr + 80 + 4 <= dat \/ dat + 4 * (p_wpl v * p_h v) <= fr + 80) by (clear - FCDD ERS; unfold parked in FCDD; lia).
    assert (P0 : 0 < fr + 96) by (clear - FR0; lia). assert (PHI : fr + 96 + 4 <= 2 ^ 47) by (clear - FRHI SP0R1; lia).
    assert (PSEP : fr + 96 + 4 <= dat \/ dat + 4 * (p_wpl v * p_h v) <= fr + 96) by (clear - FCDD ERS; unfold parked in FCDD; lia).
    assert (B0 : 0 < usp + -256) by (clear - LOR STa; lia).
    assert (B8 : (usp + -256) mod 8 = 0) by (clear - SPA; Z.div_mod_to_equations; lia).
    assert (BHI : usp + -256 + 152 <= 2 ^ 47) by (clear - SPT; lia).
    assert (BSEP : usp + -256 + 152 <= dat \/ dat + 4 * (p_wpl v * p_h v) <= usp + -256 + 144) by (clear - CKRD ERS LOW LOR; lia).
    (* [comment removed for export] *)
    lazymatch goal with A : ART RT Σr ?mm |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mm _))) _ =>
      destruct (wr_at_rw_CB mm (p_data v) (4 * (p_wpl v * p_h v)) (proj1 (af_acc_live RT AF Σr mm _ _ A (LSUBr _ DIN))) ltac:(clear - HRS1 DSZ; lia)) as (sbs & SBC);
      destruct (wr_at_rw_CB mm dat rs (proj1 (af_acc_live RT AF Σr mm _ _ A DDINr)) ltac:(clear - DDN; lia)) as (dbs & DBC);
      destruct (wr_at_rw_CB mm tab 1024 (proj1 (af_acc_live RT AF Σr mm _ _ A TBINr)) ltac:(clear; lia)) as (qbs & QBC) end.
    pose proof SBC as [[[SBL _] _] _]. cbn in SBL. apply u8arr_of_rw_cells in SBC.
    destruct (u8arr_u32arr _ (p_data v) sbs (p_wpl v * p_h v) SBC ltac:(rewrite SBL; clear - DSZ; lia)) as (ws & UAS & UASL). clear SBC SBL.
    pose proof DBC as [[[DBL _] _] _]. cbn in DBL. apply u8arr_of_rw_cells in DBC. rewrite ERS in DBL.
    destruct (u8arr_u32arr _ dat dbs (p_wpl v * p_h v) DBC ltac:(rewrite DBL; clear - DSZ; lia)) as (wd & UAD & UADL). clear DBC DBL.
    pose proof QBC as [[[QBL _] _] _]. cbn in QBL. apply u8arr_of_rw_cells in QBC.
    destruct (u8arr_u32arr _ tab qbs 256 QBC ltac:(rewrite QBL; clear; lia)) as (qws & UAQ & UAQL). clear QBC QBL.
    lazymatch goal with |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mm _))) _ =>
      assert (ACS : acc asegs mm (p_data v) (4 * (p_wpl v * p_h v))) by assumption;
      assert (ACD : acc asegs mm dat (4 * (p_wpl v * p_h v))) by (rewrite <- ERS; assumption);
      assert (ACQ : acc asegs mm tab 1024) by assumption end.
    assert (Q1 : Z.of_nat (Z.to_nat (p_h v)) = p_h v - 0) by (clear - HH1; lia).
    assert (Q3 : (1 <= Z.to_nat (p_h v))%nat) by (clear - HH1; lia).
    idtac "MARK clone rows premises".
    Time walk_to AF MST [(dat, dat + 4 * (p_wpl v * p_h v))] [0xa0040].
    eapply evt_cut.
    { eapply EVQ_thr.
      { eapply (thr_rows (Z.to_nat (p_h v)) 0) with (datat := p_data v) (datad := dat) (qtab := tab) (wpl := p_wpl v) (w := p_w v) (h := p_h v) (pw := fr + 80) (ph := fr + 96) (sb := usp + -256)
                                                (wt := ws) (wd := wd) (qws := qws).
        all: lazymatch goal with
         | |- Z.of_nat (Z.to_nat _) = _ => exact Q1
         | |- 0 <= 0 => clear; lia
         | |- (1 <= _)%nat => exact Q3
         | |- 0 < _ <= 20000 => first [exact HW1 | exact HH1]
         | |- _ = (_ * 8 + 31) / 32 => exact HWPL
         | |- 4 * _ <= _ => exact HRS1
         | |- u32arr _ _ _ _ => first [exact UAS | exact UAD | exact UAQ]
         | |- Z.of_nat (length _) = _ => first [assumption | idtac "LEFT-len"]
         | |- acc _ _ _ _ => first [assumption | idtac "LEFT-acc"]
         | |- 0 < _ => first [assumption | idtac "LEFT-pos"]
         | |- _ mod _ = 0 => first [assumption | idtac "LEFT-mod"]
         | |- _ + _ <= 2 ^ _ => first [assumption | idtac "LEFT-hi"]
         | |- mem_inv _ _ => first [assumption | idtac "LEFT-mi"]
         | |- rw_cells _ ?mm ?A ?cs => first [ assumption | match goal with H : rw_cells _ mm ?B cs |- _ => replace A with B by (clear; lia); exact H end | idtac "LEFT-cells" A ]
         | |- _ \/ _ => first [ assumption | exact SSH | exact SSG | exact TSH | exact TSG | exact QSH | exact QSG | exact ASD' | exact AQD' | exact WSEP | exact PSEP | exact BSEP | idtac "LEFT-disj" ]
         | |- ?g => idtac "LEFT:" g
         end. }
      cbn [mkR].
      repeat first [ lazymatch goal with |- @eq Z _ _ => clear; lia end | progress f_equal | reflexivity ]. }
    idtac "MARK clone rows applied".
    intros ms' PO. unfold thr_rows_exit in PO.
    destruct PO as (t0w & a0w & a2w & a3w & a5w & a6w & a7w & s4w & s8w & mw & wdw & -> & MUw & WMw & MIw & UASw & ACSw & UAQw & ACQw & UADw & UADLw & ACDw & T80w & T96w & S144w).
    clear T80 T96 S144 UAS UASL UAD UADL UAQ UAQL ACS ACD ACQ Q1 Q3 T80w T96w S144w UASw UAQw UADw UADLw ACSw ACQw ACDw ws wd qws sbs dbs qbs.
    loop_art RT AF Σr mw lo MUw ltac:(cbn [ivls_client]; split; [intros zz Hzz; right; right; left; exists dat, rs; split; [exact DDINr| clear - Hzz ERS; lia]| exact I]).
    idtac "MARK clone loop_art".
    lazymatch type of MUw with munch _ ?ma ?mb =>
      loop_transport ma mb MUw ltac:(fun Hx => lazymatch type of Hx with (?A <= _ < _)%Z =>
        lazymatch A with
        | fr => clear - Hx FCDD ERS
        | (fr + _)%Z => clear - Hx FCDD ERS
        | (fr / 8 + _)%Z => clear - Hx FCSD ERS FR64 FR0 FRSEG FRSH
        | pix => clear - Hx ADP ERS
        | pixd => clear - Hx ADX ERS
        | cmap => clear - Hx ADCM ERS
        | (usp + _)%Z => clear - Hx CKRD ERS LOW LOR FRHI
        | (usp - _)%Z => clear - Hx CKRD ERS LOW LOR FRHI
        | lo => clear - Hx CKRD ERS LOW LOR FRHI
        | _ => clear - Hx CKSD ERS FRSEG
        end; unfold parked in *; unfold SEGTOP_A, shad, SHB in *; repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia] end) end.
    idtac "MARK clone loop_transport".
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; right; right; left; exists dat, rs; split; [exact DDINr| clear - Hzz ERS; lia]| exact I]).
    lazymatch goal with MUx : munch _ ?mm mw |- _ =>
      agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; destruct Hx as [Hx Ho]; pose proof (NCD _ Hx) as NCx; clear - NCx ERS; repeat split; try exact I; lia) end.
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
    ctx_gc RT.
    idtac "MARK clone after rows".
    (* [comment removed for export] *)
    Time walk_to AF MST [(usp - 320, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [e_free].
    assert (TRF : In (0xa00ec :: bv_unsigned ra :: ras) CLIENT_TRACES) by (rewrite RAF, RAS; unfold RA_FUZZ_OP6, D_libiface.RA_TOP; apply ct_mem_In; vm_compute; reflexivity).
    pose proof FR as FRrec. split_before FRrec (C8 s0) FRrec2. clear FRrec.
    lazymatch goal with A : ART RT Σr ?mm |- _ =>
      assert (NXTB : parked (pix <> tab)) by (exact (fresh_chunk_ne RT AF Σr mm [(dat, rs); (pixd, 64)] tab 1024 ((carr, 1024) :: (cmap, 24) :: rt_live RT Σ) (pix, 64) A LVR ltac:(cbn [app In]; do 4 right; exact PIN) ltac:(clear; lia) ltac:(cbn; clear; lia)));
      assert (NCMTB : parked (cmap <> tab)) by (exact (fresh_chunk_ne RT AF Σr mm [(dat, rs); (pixd, 64)] tab 1024 ((carr, 1024) :: (cmap, 24) :: rt_live RT Σ) (cmap, 24) A LVR ltac:(cbn; tauto) ltac:(clear; lia) ltac:(cbn; clear; lia)));
      assert (NETB : forall e, In e ([(dat, rs); (pixd, 64)] ++ (carr, 1024) :: (cmap, 24) :: rt_live RT Σ) -> fst e <> tab)
        by (intros e He; apply (fresh_chunk_ne RT AF Σr mm [(dat, rs); (pixd, 64)] tab 1024 ((carr, 1024) :: (cmap, 24) :: rt_live RT Σ) e A LVR He ltac:(clear; lia));
            destruct e as [q k]; cbn [app In] in He; cbn [snd]; destruct He as [E|[E|[E|[E|He]]]];
            [injection E as <- <-; exact DDN| injection E as <- <-; clear; lia| injection E as <- <-; clear; lia| injection E as <- <-; clear; lia| exact (LVP q k He)]) end.
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                  ltac:(fun Hx => cbn [outside]; destruct Hx as [Hx Ho]; pose proof (PFS _ Hx) as P1; destruct (NFA _ Hx) as [N1 N2]; clear - P1 N1 N2 LOW LOR SPT SPA SPB FR0 FR64;
                        unfold shad, SHB in *; repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
    eapply cps_seq.
    { pose proof (gp_free RT GP) as FC; unfold free_contractC in FC; eapply FC with (lo := lo) (p := tab) (n := 1024); rt_side idtac.
      all: lazymatch goal with
           | |- In _ _ => exact TBINr
           | |- unwind_okC _ _ _ _ =>
               exists (bv_unsigned ra :: ras); rewrite ?unsigned_lit by ul; split; [| exact TRF];
               apply CHAIN; [apply AGS1; exact AGF|];
               lazymatch type of FRrec2 with rw_cells _ _ ?A _ => replace (usp + -16) with A by (clear; lia) end; exact FRrec2
           | |- ?g => idtac "LEFT:" g
           end. }
    idtac "MARK clone free applied".
    clear FRrec2.
    after_call RT AF.
    lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ => rename S into Σf; rename A into ARTF end.
    lazymatch goal with H : rt_live RT Σf = live_remove tab _ |- _ => rename H into LVFr end.
    assert (LVFq : rt_live RT Σf = (dat, rs) :: (pixd, 64) :: (carr, 1024) :: (cmap, 24) :: rt_live RT Σ).
    { rewrite LVFr, LVR. rewrite ?live_remove_other by assumption. rewrite live_remove_head.
      rewrite (live_remove_fresh tab); [reflexivity|]. intros e He. apply NETB. cbn [app]; do 2 right; exact He. }
    fold_ag ltac:(fun Hx => destruct Hx as [Hx Ho]; apply (aclient_mono LVF _ usp _ _ _ _ Hx); [intros e He; rewrite LVFq; do 4 right; exact He| solve [frames_sub_tac]| clear; lia]).
    idtac "MARK clone after free".
    lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ => rename mm into mf end.
    assert (FRSf : rt_frames RT Σf = (fr, 2%nat) :: rt_frames RT Σ) by (repeat match goal with E : rt_frames RT Σf = _ |- _ => rewrite E end; exact FRSr).
    assert (SP0f : rt_sp0 RT Σf = rt_sp0 RT Σ) by (repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; reflexivity).
    assert (CRf : rt_credit RT Σ - (2 * RASTER_COST + 44) <= rt_credit RT Σf) by (repeat match goal with E : rt_credit RT Σf = _ |- _ => rewrite E end; exact CRr).
    assert (LVPf : forall e, In e (rt_live RT Σf) -> 0 < snd e).
    { intros [q k] Hq. rewrite LVFq in Hq. cbn [In] in Hq. cbn [snd].
      destruct Hq as [E|[E|[E|[E|Hq]]]]; [injection E as <- <-; exact DDN| injection E as <- <-; clear; lia| injection E as <- <-; clear; lia| injection E as <- <-; clear; lia| exact (LVP q k Hq)]. }
    sigma_gc RT Σ Σf.
    assert (LSUBf : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σf)) by (intros e He; rewrite LVFq; do 4 right; exact He).
    assert (PDINf : In (pixd, 64) (rt_live RT Σf)) by (rewrite LVFq; right; left; reflexivity).
    assert (DDINf : In (dat, rs) (rt_live RT Σf)) by (rewrite LVFq; left; reflexivity).
    assert (CMINf : In (cmap, 24) (rt_live RT Σf)) by (rewrite LVFq; do 3 right; left; reflexivity).
    assert (CAINf : In (carr, 1024) (rt_live RT Σf)) by (rewrite LVFq; do 2 right; left; reflexivity).
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
    ctx_gc RT.
    (* [comment removed for export] *)
    Time walk_to AF MST [(usp - 320, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [e_pixDestroy].
    split_before FRM (C8 (Z_to_bv 64 pix)) FPT. split_at FPT 1%nat FRMb.
    pose proof FSH as SHT. split_at SHT 20%nat SHT2. split_at SHT2 1%nat SHT3. clear SHT SHT3.
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                  ltac:(fun Hx => cbn [outside]; destruct Hx as [Hx Ho]; pose proof (PFS _ Hx) as P1; destruct (NFA _ Hx) as [N1 N2]; clear - P1 N1 N2 LOW LOR SPT SPA SPB FR0 FR64;
                        unfold shad, SHB in *; repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
    unfold hid in POBJ0. pose proof POBJ0 as PB. hide POBJ0.
    destruct PB as (_ & CH & HOK & HD & _).
    destruct HD as [HD|[HDa HDb]]; [exfalso; unpark VDATA; exact (VDATA HD)|].
    lazymatch goal with PS : rw_cells asegs ?mc pix _ |- cps _ (ASTA RT Σf _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
      assert (POR2 : pix_obj_rc (rt_live RT Σf) mc pix v cv 2)
        by (split; [unfold pix_cells_rc; rewrite D8; exact PS|]; split; [exact (chunk_mono _ _ _ _ LSUBf CH)|]; split; [exact HOK|];
            split; [right; split; [exact (chunk_mono _ _ _ _ LSUBf HDa)| exact HDb]| left; exact CMZ]) end.
    clear CH HOK HDa HDb.
    idtac "MARK objs for destroy_rc".
    eapply cps_seq.
    { pose proof PDRC as PD; unfold pixDestroy_rc_cps in PD.
      eapply PD with (lo := lo) (pp := fr + 160) (pix := pix) (v := v) (cv := cv) (rc := 2).
      - exact FDO.
      - exact MST.
      - reflexivity.
      - reflexivity.
      - unfold optrL. split.
        + right. exists fr, 2%nat. rewrite FRSf. change (fs_size 2) with 256. split; [left; reflexivity|]. split; [clear; lia|]. split; [clear; lia|].
          split; [clear - FR64; Z.div_mod_to_equations; lia|]. split; [clear - FR0; lia|]. split; [clear - FRHI SP0R1; lia|].
          replace (shad (fr + 160)) with (fr / 8 + 2147450900) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia). destruct SHT2 as [[_ B] _]. exact B.
        + pose proof FRSH as Q; unfold parked in Q. clear - Q FR0 FR64 FRSEG. unfold SEGTOP_A. repeat split; first [lia | Z.div_mod_to_equations; lia].
      - exact FPT.
      - exact POR2.
      - clear; lia.
      - clear - FCD; unfold parked in FCD; lia.
      - lenv_tac.
      - unfold lres; rewrite FRSf, LVFq; cbn [length]; unfold FRAMES_MAX, LIVE_MAX in *; unfold LVF in *;
        repeat split; [clear - FRB; lia| clear - LVB; lia| clear - CRf CRB; unfold RASTER_COST in *; lia| intros p n Hp; exact (LVPf (p, n) ltac:(rewrite LVFq; exact Hp))]. }
    idtac "MARK destroy_rc applied".
    clear POR2 FPT SHT2. lazymatch goal with PS : rw_cells asegs _ pix _ |- _ => clear PS end.
    (* [comment removed for export] *)
    hide FSH.
    osd_mark LOW. osd_mark LOR. osd_mark SPT. osd_mark SPB. osd_mark STa. osd_mark SP0R0. osd_mark SP0R1. osd_mark FR0. osd_mark FRHI. osd_mark FRSEG. osd_mark FR64.
    osd_mark CKR. osd_mark CKS. osd_mark FCD. osd_mark APP. osd_mark FCD1. osd_mark FCD5. osd_mark ACMX.
    assert (OSDS : osd_strict) by exact I.
    after_call RT AF.
    osd_clear.
    unfold hid in FSH.
    lazymatch goal with AGx : agree_on (fun a => aclient _ _ _ a /\ outside _ a) ?ma ?mb |- _ =>
      lazymatch type of FSH with rw_cells asegs ma ?A ?cs =>
        apply (rw_cells_agree_nw asegs ma mb A cs) in FSH;
        [ | eapply agree_sub; [exact AGx|]; cbv beta; intros xa Hxa; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Hxa; split;
            [ right; right; right; right; exists fr, 2%nat; split; [frames_in_tac | change (fs_size 2%nat) with 256; clear - Hxa FR64; unfold shad, SHB in *; Z.div_mod_to_equations; lia]
            | cbn [outside]; clear - Hxa FR64 FRSH FCS; unfold parked in *; repeat split; try exact I; Z.div_mod_to_equations; lia ] ] end end.
    fold_ag ltac:(fun Hx => destruct Hx as [Hx Ho]; split; [apply (aclient_mono LVF _ usp _ _ _ _ Hx); [first [solve [live_add_tac] | intros e He; repeat match goal with E : rt_live RT _ = _ |- _ => rewrite E end; do 4 right; exact He]| solve [frames_sub_tac]| clear; lia]|
                                    cbn [outside]; cbn [outside] in Ho; destruct (NFA _ Hx) as [N1 N2]; clear - N1 N2 Ho; repeat split; try exact I; lia]).
    idtac "MARK clone after destroy".
    lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ => rename S into Σz; rename A into ARTZ; rename mm into mz end.
    assert (FRSz : rt_frames RT Σz = (fr, 2%nat) :: rt_frames RT Σ) by (repeat match goal with E : rt_frames RT Σz = _ |- _ => rewrite E end; exact FRSf).
    assert (SP0z : rt_sp0 RT Σz = rt_sp0 RT Σ) by (repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; reflexivity).
    assert (CRz : rt_credit RT Σ - (2 * RASTER_COST + 45) <= rt_credit RT Σz) by (lazymatch goal with E : rt_credit RT Σf - 1 <= rt_credit RT Σz |- _ => clear - CRf E; lia end).
    assert (LVZ : rt_live RT Σz = (dat, rs) :: (pixd, 64) :: (carr, 1024) :: (cmap, 24) :: rt_live RT Σ) by (repeat match goal with E : rt_live RT Σz = _ |- _ => rewrite E end; exact LVFq).
    (* [comment removed for export] *)
    assert (FZP : forall e, In e (rt_live RT Σ) -> fst e <> pixd) by (intros e He; apply (fresh_chunk_ne RT AF Σz mz [(dat, rs)] pixd 64 _ e ARTZ LVZ); [cbn [app In]; do 3 right; exact He| clear; lia| destruct e as [eq ek]; exact (LVP eq ek He)]).
    assert (FZD : forall e, In e (rt_live RT Σ) -> fst e <> dat) by (intros e He; apply (fresh_chunk_ne RT AF Σz mz [] dat rs _ e ARTZ LVZ); [cbn [app In]; do 3 right; exact He| clear - DDN; lia| destruct e as [eq ek]; exact (LVP eq ek He)]).
    assert (FZA : forall e, In e (rt_live RT Σ) -> fst e <> carr) by (intros e He; apply (fresh_chunk_ne RT AF Σz mz [(dat, rs); (pixd, 64)] carr 1024 _ e ARTZ LVZ); [cbn [app In]; do 3 right; exact He| clear; lia| destruct e as [eq ek]; exact (LVP eq ek He)]).
    assert (FZC : forall e, In e (rt_live RT Σ) -> fst e <> cmap) by (intros e He; apply (fresh_chunk_ne RT AF Σz mz [(dat, rs); (pixd, 64); (carr, 1024)] cmap 24 _ e ARTZ LVZ); [cbn [app In]; do 3 right; exact He| clear; lia| destruct e as [eq ek]; exact (LVP eq ek He)]).
    sigma_gc RT Σ Σz.
    assert (LSUBz : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σz)) by (intros e He; rewrite LVZ; do 4 right; exact He).
    assert (PDINz : In (pixd, 64) (rt_live RT Σz)) by (rewrite LVZ; right; left; reflexivity).
    assert (DDINz : In (dat, rs) (rt_live RT Σz)) by (rewrite LVZ; left; reflexivity).
    assert (CMINz : In (cmap, 24) (rt_live RT Σz)) by (rewrite LVZ; do 3 right; left; reflexivity).
    assert (CAINz : In (carr, 1024) (rt_live RT Σz)) by (rewrite LVZ; do 2 right; left; reflexivity).
    assert (PXINz : In (pix, 64) (rt_live RT Σz)) by (apply LSUBz; exact PIN).
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
    ctx_gc RT.
    idtac "MARK clone names z".
    forget_junk FR. forget_junk FRM. try forget_junk FRMb.
    (* [comment removed for export] *)
    lazymatch goal with H : rw_cells asegs _ pix (pix_cells_rc v _) |- _ => rename H into PXS end.
    lazymatch goal with H : rw_cells asegs _ cmap _ |- _ => rename H into CMC end.
    hide PXS. hide PXD. hide CMC.
    clear_acc.
    repeat match goal with H : u32arr _ _ _ _ |- _ => clear H end.
    hide VDATA1. hide DDNE. hide NPCM. hide NPCA. hide NDCM. hide NDCA. hide CNE.
    hide FRSH.   (* [comment removed for export] *)
    repeat match goal with H : parked (fr + 256 <= ?b \/ _ <= fr) |- _ => lazymatch b with pix => hide H | pixd => hide H | cmap => hide H | _ => clear H end end.
    repeat match goal with H : parked (?b + _ <= fr / 8 + 2147450880 \/ _ <= ?b) |- _ => lazymatch b with pix => hide H | pixd => hide H | cmap => hide H | _ => clear H end end.
    repeat match goal with H : parked _ |- _ => clear H end.
    unfold hid in FRSH. unpark FRSH.
    idtac "MARK clone diet".
    (* [comment removed for export] *)
    Time walk_to AF MST [(usp - 320, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [0x9fe94].
    idtac "MARK clone at pokes".
    split_at FRM 1%nat FRMr.
    Time (eapply evt_cut;
    [ eapply EVQ_thr;
      [ eapply thr_exit_x1; [exact FR0| exact FR64| clear - FRHI SP0R1; lia| exact FRM| exact FSH| reflexivity| assumption]
      | cbn [mkR]; repeat first [ lazymatch goal with |- @eq Z _ _ => clear; lia end | progress f_equal | reflexivity ] ]
    | ]).
    clear FRM FSH. intros ms' PO. destruct PO as (mx & -> & MUx & WMx & MIx & FRM & FSH). unfold thr_exit_W, SHB in MUx. unfold thr_sh_f5 in FSH.
    idtac "MARK clone pokes applied".
    Time loop_art RT AF Σz mx lo MUx ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
    Time (lazymatch type of MUx with munch _ ?ma ?mb =>
      loop_transport ma mb MUx ltac:(fun Hx => cbn [outside]; unfold shad, SHB in *; clear - Hx FRHI FRSH FRSEG LOW LOR FR64 FR0 SP0R1 SP0R0 SP0W; repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end).
    idtac "MARK clone at flag load".
    repeat match goal with H : hid (parked _) |- _ => unfold hid in H end.
    Time (lazymatch goal with AGFx : agree_on ?PFx _ ?mm, MUy : munch _ ?mm _ |- _ =>
      carry_mu MUy PXS ltac:(fun Hx => seg_side fr pix FR64 LOW LOR Hx);
      carry_mu MUy PXD ltac:(fun Hx => seg_side fr pixd FR64 LOW LOR Hx);
      carry_mu MUy CMC ltac:(fun Hx => seg_side fr cmap FR64 LOW LOR Hx) end).
    hide PXS. hide PXD. hide CMC.
    join_cells FRM FRMr.
    idtac "MARK clone carried x".
    frame_release_g RT AF GP MST Σ fr 2%nat 256 PF AGF PFS1 usp lo 0x9ff4c
        ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
        ltac:(fun Hx => cbn [outside]; destruct Hx as [Hx Ho]; pose proof (PFS _ Hx) as P1; destruct (NFA _ Hx) as [N1 N2]; clear - P1 N1 N2 LOW LOR SPT SPA SPB FR0 FR64;
                        unfold shad, SHB in *; repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia])
        ltac:(fun Hx => exact (proj1 Hx))
        ltac:(fun fl FLN => idtac).
    idtac "MARK clone released".
    lazymatch goal with MUx : munch [(?fl, ?fl + 1)] _ ?mb |- _ =>
      carry_mu MUx PXS ltac:(fun Hx => flag_side fl pix Hx);
      carry_mu MUx PXD ltac:(fun Hx => flag_side fl pixd Hx);
      carry_mu MUx CMC ltac:(fun Hx => flag_side fl cmap Hx) end.
    hide PXS. hide PXD. hide CMC.
    clear_acc. refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj. park_ne.
    (* [comment removed for export] *)
    change (bv_unsigned sp) with usp. rewrite ESP.
    Time walk_to AF MST [(usp - 320, usp)] (@nil Z).
    
    lazymatch goal with MUx : munch _ _ ?mb |- evt _ _ (MS _ _ _ _ _ ?mb _) =>
      carry_mu MUx PXS ltac:(fun Hx => stk_side pix LOW LOR Hx);
      carry_mu MUx PXD ltac:(fun Hx => stk_side pixd LOW LOR Hx);
      carry_mu MUx CMC ltac:(fun Hx => stk_side cmap LOW LOR Hx) end.
    cps_stop.
    try fold_mkR.
    unfold hid in VDATA1, DDNE, NPCM, NPCA, NDCM, NDCA, CNE.
    idtac "MARK clone epilogue".
    (* [comment removed for export] *)
    apply cps_finish. intros c Hc. subst QF. cbv beta.
    set (vf := mkPixv (p_w v) (p_h v) 8 (p_spp v1) (p_wpl v) (p_xres v) (p_yres v) (p_inf v) (p_spec v1) cmap dat).
    unfold hid in POBJ0, HOKD.
    assert (LVE : rt_live RT S2 = (dat, rs) :: (pixd, 64) :: (carr, 1024) :: (cmap, 24) :: LVF) by (rewrite LV2; exact LVZ).
    assert (LSUB2 : forall e, In e LVF -> In e (rt_live RT S2)) by (intros e He; rewrite LVE; do 4 right; exact He).
    exists S2, pixd, vf, (mkCmapv carr 8 256 5).
    split.
    + eapply (ASTA_conseq RT); [exact Hc|]. intros ms <-. eexists.
      split; [unfold ret_st; rewrite ?ESP; do 16 eexists; reflexivity|].
      split; [unfold rt_after_f; split; [split; [exact ART2| split; assumption]| split; assumption]|].
      split; [intros a Ha Ho; apply AGF; split; [exact Ha| exact Ho]|].
      split.
      { destruct POBJ0 as (_ & CH & HOK & HD & HCM).
        split; [lazymatch goal with PS : rw_cells asegs _ pix (pix_cells_rc v _) |- _ => exact PS end|].
        split; [exact (chunk_mono _ _ _ _ LSUB2 CH)|].
        split; [exact HOK|].
        split; [destruct HD as [HD|[HDa HDb]]; [left; exact HD| right; split; [exact (chunk_mono _ _ _ _ LSUB2 HDa)| exact HDb]]|].
        left; exact CMZ. }
      right. split; [| cbn [p_data]; unpark VDATA1; exact VDATA1].
      split; [unfold pix_cells; cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data]; lazymatch goal with PX : rw_cells asegs _ pixd _ |- _ => exact PX end|].
      split; [split; [rewrite LVE; right; left; reflexivity| split; [exact PD0| split; [exact PD16| clear; lia]]]|].
      split; [unfold pix_hdr_ok; cbn [p_w p_h p_d p_wpl]; unfold pix_hdr_ok in HOKD; rewrite VW, VH, VD, EWD in HOKD; exact HOKD|].
      split; [right; unfold vf, rsize; cbn [p_data p_wpl p_h]; split; [split; [rewrite LVE, ERS; left; reflexivity| split; [exact DD0| split; [exact DD16| clear - DDN ERS; lia]]]| unpark DDNE; exact DDNE]|].
      right. cbn [p_cmap p_data c_arr].
      split.
      { split; [exists cpad; unfold cmap_cells; cbn [c_arr c_depth c_nalloc c_n]; lazymatch goal with CC : rw_cells asegs _ cmap _ |- _ => exact CC end|].
        split; [split; [rewrite LVE; do 3 right; left; reflexivity| split; [exact CM0| split; [exact CM16| clear; lia]]]|].
        split; [cbn [c_arr c_nalloc]; split; [rewrite LVE; do 2 right; left; reflexivity| split; [exact CA0| split; [exact CA16| clear; lia]]]|].
        split; [exact COK| cbn [c_arr]; unpark CNE; exact CNE]. }
      unpark NPCM; unpark NPCA; unpark NDCM; unpark NDCA.
      repeat split; intro E; [apply NPCM | apply NPCA | apply NDCM | apply NDCA]; symmetry; exact E.
    + split; [intros Z0; exfalso; clear - Z0 PD0; lia|].
      split.
      { intros _. rewrite LVE. unfold LVF.
        unpark VDATA1; unpark DDNE; unpark NPCM; unpark NPCA; unpark NDCM; unpark NDCA; unpark CNE.
        apply (live_destroy_thr (rt_live RT Σ) pixd dat rs cmap carr 1024 vf (mkCmapv carr 8 256 5));
          [reflexivity| reflexivity| reflexivity| exact VDATA1| clear - CM0; lia| clear - CA0; lia
          | exact DDNE| exact NDCA| exact NDCM| intro E; apply NPCA; symmetry; exact E| intro E; apply NPCM; symmetry; exact E| intro E; apply CNE; symmetry; exact E
          | exact FZP| exact FZD| exact FZC| exact FZA]. }
      split.
      { intros p n Hp. rewrite LVE in Hp. cbn [In] in Hp.
        destruct Hp as [E|[E|[E|[E|Hp]]]]; [injection E as <- <-; exact DDN| injection E as <- <-; clear; lia| injection E as <- <-; clear; lia| injection E as <- <-; clear; lia| exact (LVP p n Hp)]. }
      split; [rewrite LVE; unfold LVF; cbn [length]; lia|].
      split; [rewrite FRS2; first [reflexivity | exact FRSz]|]. split; [rewrite SP2; first [exact SP0z | reflexivity]|].
      rewrite D8. cbn [Z.eqb Pos.eqb]. rewrite CR2. clear - CRz. unfold RASTER_COST in *. lia.
  - (* [comment removed for export] *)
    idtac "MARK fresh case".
    rename x4 into pixt. rename x5 into vt.
    specialize (LVR1 CMNZ). clear LVR0.
    set (dtt := p_data vt) in *. set (rst := 4 * (p_wpl vt * p_h vt)) in *.
    assert (LVR : rt_live RT Σr = (dtt, rst) :: (pixt, 64) :: (dat, rs) :: (pixd, 64) :: (tab, 1024) :: (carr, 1024) :: (cmap, 24) :: rt_live RT Σ) by (rewrite LVR1, LVS; reflexivity).
    clear LVR1.
    sigma_gc RT Σ Σr.
    pose proof POTR as (PXT & (PTIN & PT0 & PT16 & _) & HOKT & PTDATA & _).
    destruct PTDATA as [PTZ|((DTIN & DT0 & DT16 & DTN) & DTNE)]; [exfalso; exact (VDATAT PTZ)|].
    unfold rsize in DTIN, DTN. change (p_data vt) with dtt in DTIN, DT0, DT16, DTN, DTNE. change (4 * (p_wpl vt * p_h vt)) with rst in DTIN, DTN.
    unfold pix_cells in PXT. rewrite VWT, VHT, VDT, VCMAPT in PXT. change (p_data vt) with dtt in PXT.
    pose proof POSR as (PXS & _). unfold pix_cells in PXS. rewrite D8 in PXS || idtac.
    assert (EWT : p_wpl vt = p_wpl v) by (destruct HOKT as (_ & _ & _ & Q4 & _); rewrite VWT, VDT in Q4; rewrite Q4, HWPL; reflexivity).
    rewrite EWT in PXT.
    assert (ERST : rst = 4 * (p_wpl v * p_h v)) by (unfold rst; rewrite EWT, VHT; reflexivity).
    (* [comment removed for export] *)
    assert (SUBT : forall e, In e ((dat, rs) :: (pixd, 64) :: (tab, 1024) :: (carr, 1024) :: (cmap, 24) :: rt_live RT Σ) -> In e (rt_live RT Σr) /\ fst e <> pixt)
      by (intros e He; split; [rewrite LVR; right; right; exact He|];
          apply (fresh_chunk_ne RT AF Σr _ [(dtt, rst)] pixt 64 _ e ARTR LVR); [cbn [app]; right; exact He| clear; lia|];
          destruct e as [eq ek]; cbn [In] in He; cbn [snd];
          destruct He as [E|[E|[E|[E|[E|He]]]]]; [injection E as <- <-; exact DDN| injection E as <- <-; clear; lia| injection E as <- <-; clear; lia| injection E as <- <-; clear; lia| injection E as <- <-; clear; lia| exact (LVP eq ek He)]).
    assert (SUBDT : forall e, In e ((dat, rs) :: (pixd, 64) :: (tab, 1024) :: (carr, 1024) :: (cmap, 24) :: rt_live RT Σ) -> In e (rt_live RT Σr) /\ fst e <> dtt)
      by (intros e He; split; [rewrite LVR; right; right; exact He|];
          apply (fresh_chunk_ne RT AF Σr _ [] dtt rst _ e ARTR LVR); [cbn [app]; right; exact He| exact DTN|];
          destruct e as [eq ek]; cbn [In] in He; cbn [snd];
          destruct He as [E|[E|[E|[E|[E|He]]]]]; [injection E as <- <-; exact DDN| injection E as <- <-; clear; lia| injection E as <- <-; clear; lia| injection E as <- <-; clear; lia| injection E as <- <-; clear; lia| exact (LVP eq ek He)]).
    assert (LSUBr : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σr)) by (intros e He; rewrite LVR; do 7 right; exact He).
    assert (DTINr : In (dtt, rst) (rt_live RT Σr)) by (rewrite LVR; left; reflexivity).
    assert (PTINr : In (pixt, 64) (rt_live RT Σr)) by (rewrite LVR; right; left; reflexivity).
    assert (DDINr : In (dat, rs) (rt_live RT Σr)) by (rewrite LVR; do 2 right; left; reflexivity).
    assert (PDINr : In (pixd, 64) (rt_live RT Σr)) by (rewrite LVR; do 3 right; left; reflexivity).
    assert (TBINr : In (tab, 1024) (rt_live RT Σr)) by (rewrite LVR; do 4 right; left; reflexivity).
    assert (CAINr : In (carr, 1024) (rt_live RT Σr)) by (rewrite LVR; do 5 right; left; reflexivity).
    assert (CMINr : In (cmap, 24) (rt_live RT Σr)) by (rewrite LVR; do 6 right; left; reflexivity).
    assert (PXINr : In (pix, 64) (rt_live RT Σr)) by (apply LSUBr; exact PIN).
    (* [comment removed for export] *)
    assert (FTD : dat <> pixt) by (exact (proj2 (SUBT (dat, rs) ltac:(left; reflexivity)))).
    assert (FTX : pixd <> pixt) by (exact (proj2 (SUBT (pixd, 64) ltac:(right; left; reflexivity)))).
    assert (FTQ : tab <> pixt) by (exact (proj2 (SUBT (tab, 1024) ltac:(do 2 right; left; reflexivity)))).
    assert (FTP : pix <> pixt) by (exact (proj2 (SUBT (pix, 64) ltac:(do 5 right; exact PIN)))).
    assert (FUD : dat <> dtt) by (exact (proj2 (SUBDT (dat, rs) ltac:(left; reflexivity)))).
    assert (FUX : pixd <> dtt) by (exact (proj2 (SUBDT (pixd, 64) ltac:(right; left; reflexivity)))).
    assert (FUQ : tab <> dtt) by (exact (proj2 (SUBDT (tab, 1024) ltac:(do 2 right; left; reflexivity)))).
    assert (FUP : pix <> dtt) by (exact (proj2 (SUBDT (pix, 64) ltac:(do 5 right; exact PIN)))).
    assert (FUCM : cmap <> dtt) by (exact (proj2 (SUBDT (cmap, 24) ltac:(do 4 right; left; reflexivity)))).
    assert (FTCM : cmap <> pixt) by (exact (proj2 (SUBT (cmap, 24) ltac:(do 4 right; left; reflexivity)))).
    chunk_facts RT AF GP pixt 64. chunk_facts RT AF GP dtt rst.
    fframe_chunk RT AF fr 2%nat 256 pixt 64. fframe_chunk RT AF fr 2%nat 256 dtt rst.
    apart2 RT AF BUD dtt rst dat rs FUD. apart2 RT AF BTD pixt 64 dat rs FTD. apart2 RT AF BUQ dtt rst tab 1024 FUQ.
    apart2 RT AF BUP dtt rst pix 64 FUP. apart2 RT AF BTP pixt 64 pix 64 FTP. apart2 RT AF BUX dtt rst pixd 64 FUX. apart2 RT AF BTX pixt 64 pixd 64 FTX.
    apart2 RT AF BUCM dtt rst cmap 24 FUCM. apart2 RT AF BTCM pixt 64 cmap 24 FTCM.
    park_disj. park_ne.
    hide SUBT. hide SUBDT. hide HOKT. clear POTR POSR.
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
    ctx_gc RT.
    idtac "MARK fresh names".
    (* [comment removed for export] *)
    Time walk_to AF MST [(usp - 320, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [0xa0018; 0xa0000; 0xa00e4].
    try fold_mkR.
    idtac "MARK fresh at loop setup".
    (* [comment removed for export] *)
    assert (HW1 : 0 < p_w v <= 20000) by (clear - HW0 HW2; lia). assert (HH1 : 0 < p_h v <= 20000) by (clear - HH0 HH2; lia).
    assert (WPLB : 0 < p_wpl v <= 5001) by (rewrite HWPL; clear - HW1; Z.div_mod_to_equations; lia).
    rewrite !(sx32_small (p_h v)) by (clear - HH1; lia). rewrite !(sx32_small (p_wpl v)) by (clear - WPLB; lia).
    lstep. brF.
    Time awalk [0xa0040; 0xa00e4].
    rewrite ?(unsigned_lit (p_wpl v)) by (clear - WPLB; lia). replace (p_wpl v * 4) with (4 * p_wpl v) by (clear; lia).
    try fold_mkR.
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
    lazymatch goal with MUx : munch _ ?mm _, A : ART RT _ ?mm |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
      agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; destruct Hx as [Hx Ho]; pose proof (PFS _ Hx) as P1; destruct (NFA _ Hx) as [N1 N2]; clear - P1 N1 N2 LOW LOR SPT SPA SPB FR0 FR64;
                                         unfold shad, SHB in *; repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end.
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
    ctx_gc RT.
    idtac "MARK fresh rows art".
    rewrite (sx32_small (p_w v)) in FRM by (clear - HW1; lia). rewrite (sx32_small (p_h v)) in FRM by (clear - HH1; lia).
    pose proof FRM as T. split_before T (C4 (Z_to_bv 64 (p_w v))) T80. split_at T80 1%nat T2. clear T T2.
    pose proof FRM as T. split_before T (C4 (Z_to_bv 64 (p_h v))) T96. split_at T96 1%nat T2. clear T T2.
    pose proof FR as T. split_before T (C8 (Z_to_bv 64 tab)) S144. split_at S144 1%nat T2. clear T T2.
    lazymatch goal with H : dtt + rst <= rt_sp0 RT Σ - _ |- _ => rename H into CKRU end.
    lazymatch goal with H : parked (dtt + rst <= 2147446784 \/ _) |- _ => rename H into CKHU end.
    lazymatch goal with H : parked (dtt + rst <= 65536 \/ _) |- _ => rename H into CKSU end.
    assert (S8 : dtt mod 8 = 0) by (clear - DT16; Z.div_mod_to_equations; lia).
    assert (SHI : dtt + 4 * (p_wpl v * p_h v) <= 2 ^ 47) by (clear - CKRU ERST SP0R1; lia).
    assert (SSH : dtt + 4 * (p_wpl v * p_h v) <= 0x7fff7000 \/ 0x10007fff8000 <= dtt) by (clear - CKHU ERST; unfold parked in CKHU; lia).
    assert (SSG : dtt + 4 * (p_wpl v * p_h v) <= 0x10000 \/ SEGTOP_A <= dtt) by (clear - CKSU ERST; unfold parked in CKSU; unfold SEGTOP_A; lia).
    assert (T8 : dat mod 8 = 0) by (clear - DD16; Z.div_mod_to_equations; lia).
    lazymatch goal with H : dat + rs <= rt_sp0 RT Σ - _ |- _ => rename H into CKRD end.
    lazymatch goal with H : parked (dat + rs <= 2147446784 \/ _) |- _ => rename H into CKHD end.
    lazymatch goal with H : parked (dat + rs <= 65536 \/ _) |- _ => rename H into CKSD end.
    lazymatch goal with H : parked (fr + 256 <= dat \/ _) |- _ => rename H into FCDD end.
    lazymatch goal with H : parked (dat + rs <= fr / 8 + _ \/ _) |- _ => rename H into FCSD end.
    lazymatch goal with H : tab + 1024 <= rt_sp0 RT Σ - _ |- _ => rename H into CKRT end.
    lazymatch goal with H : parked (tab + 1024 <= 2147446784 \/ _) |- _ => rename H into CKHT end.
    lazymatch goal with H : parked (tab + 1024 <= 65536 \/ _) |- _ => rename H into CKST end.
    assert (THI : dat + 4 * (p_wpl v * p_h v) <= 2 ^ 47) by (clear - CKRD ERS SP0R1; lia).
    assert (TSH : dat + 4 * (p_wpl v * p_h v) <= 0x7fff7000 \/ 0x10007fff8000 <= dat) by (clear - CKHD ERS; unfold parked in CKHD; lia).
    assert (TSG : dat + 4 * (p_wpl v * p_h v) <= 0x10000 \/ SEGTOP_A <= dat) by (clear - CKSD ERS; unfold parked in CKSD; unfold SEGTOP_A; lia).
    assert (Q8 : tab mod 8 = 0) by (clear - TB16; Z.div_mod_to_equations; lia).
    assert (QHI : tab + 1024 <= 2 ^ 47) by (clear - CKRT SP0R1; lia).
    assert (QSH : tab + 1024 <= 0x7fff7000 \/ 0x10007fff8000 <= tab) by (clear - CKHT; unfold parked in CKHT; lia).
    assert (QSG : tab + 1024 <= 0x10000 \/ SEGTOP_A <= tab) by (clear - CKST; unfold parked in CKST; unfold SEGTOP_A; lia).
    lazymatch goal with A : ART RT Σr ?mm |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mm _))) _ =>
      pose proof (live_apart2 RT AF Σr mm tab 1024 dat rs A TBINr DDINr ltac:(intros E; injection E as E1 E2; unpark NDTB; exact (NDTB (eq_sym E1)))) as AQD end.
    assert (ASD' : dtt + 4 * (p_wpl v * p_h v) <= dat \/ dat + 4 * (p_wpl v * p_h v) <= dtt) by (clear - BUD ERS ERST; unpark BUD; lia).
    assert (AQD' : tab + 1024 <= dat \/ dat + 4 * (p_wpl v * p_h v) <= tab) by (clear - AQD ERS; lia). clear AQD.
    assert (W0 : 0 < fr + 80) by (clear - FR0; lia). assert (WHI : fr + 80 + 4 <= 2 ^ 47) by (clear - FRHI SP0R1; lia).
    assert (WSEP : fr + 80 + 4 <= dat \/ dat + 4 * (p_wpl v * p_h v) <= fr + 80) by (clear - FCDD ERS; unfold parked in FCDD; lia).
    assert (P0 : 0 < fr + 96) by (clear - FR0; lia). assert (PHI : fr + 96 + 4 <= 2 ^ 47) by (clear - FRHI SP0R1; lia).
    assert (PSEP : fr + 96 + 4 <= dat \/ dat + 4 * (p_wpl v * p_h v) <= fr + 96) by (clear - FCDD ERS; unfold parked in FCDD; lia).
    assert (B0 : 0 < usp + -256) by (clear - LOR STa; lia).
    assert (B8 : (usp + -256) mod 8 = 0) by (clear - SPA; Z.div_mod_to_equations; lia).
    assert (BHI : usp + -256 + 152 <= 2 ^ 47) by (clear - SPT; lia).
    assert (BSEP : usp + -256 + 152 <= dat \/ dat + 4 * (p_wpl v * p_h v) <= usp + -256 + 144) by (clear - CKRD ERS LOW LOR; lia).
    (* [comment removed for export] *)
    lazymatch goal with A : ART RT Σr ?mm |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mm _))) _ =>
      destruct (wr_at_rw_CB mm dtt rst (proj1 (af_acc_live RT AF Σr mm _ _ A DTINr)) ltac:(clear - DTN; lia)) as (sbs & SBC);
      destruct (wr_at_rw_CB mm dat rs (proj1 (af_acc_live RT AF Σr mm _ _ A DDINr)) ltac:(clear - DDN; lia)) as (dbs & DBC);
      destruct (wr_at_rw_CB mm tab 1024 (proj1 (af_acc_live RT AF Σr mm _ _ A TBINr)) ltac:(clear; lia)) as (qbs & QBC) end.
    pose proof SBC as [[[SBL _] _] _]. cbn in SBL. apply u8arr_of_rw_cells in SBC. rewrite ERST in SBL.
    destruct (u8arr_u32arr _ dtt sbs (p_wpl v * p_h v) SBC ltac:(rewrite SBL; clear - DSZ; lia)) as (ws & UAS & UASL). clear SBC SBL.
    pose proof DBC as [[[DBL _] _] _]. cbn in DBL. apply u8arr_of_rw_cells in DBC. rewrite ERS in DBL.
    destruct (u8arr_u32arr _ dat dbs (p_wpl v * p_h v) DBC ltac:(rewrite DBL; clear - DSZ; lia)) as (wd & UAD & UADL). clear DBC DBL.
    pose proof QBC as [[[QBL _] _] _]. cbn in QBL. apply u8arr_of_rw_cells in QBC.
    destruct (u8arr_u32arr _ tab qbs 256 QBC ltac:(rewrite QBL; clear; lia)) as (qws & UAQ & UAQL). clear QBC QBL.
    lazymatch goal with |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mm _))) _ =>
      assert (ACS : acc asegs mm dtt (4 * (p_wpl v * p_h v))) by (rewrite <- ERST; assumption);
      assert (ACD : acc asegs mm dat (4 * (p_wpl v * p_h v))) by (rewrite <- ERS; assumption);
      assert (ACQ : acc asegs mm tab 1024) by assumption end.
    assert (Q1 : Z.of_nat (Z.to_nat (p_h v)) = p_h v - 0) by (clear - HH1; lia).
    assert (Q3 : (1 <= Z.to_nat (p_h v))%nat) by (clear - HH1; lia).
    idtac "MARK fresh rows premises".
    Time walk_to AF MST [(dat, dat + 4 * (p_wpl v * p_h v))] [0xa0040].
    eapply evt_cut.
    { eapply EVQ_thr.
      { eapply (thr_rows (Z.to_nat (p_h v)) 0) with (datat := dtt) (datad := dat) (qtab := tab) (wpl := p_wpl v) (w := p_w v) (h := p_h v) (pw := fr + 80) (ph := fr + 96) (sb := usp + -256)
                                                (wt := ws) (wd := wd) (qws := qws).
        all: lazymatch goal with
         | |- Z.of_nat (Z.to_nat _) = _ => exact Q1
         | |- 0 <= 0 => clear; lia
         | |- (1 <= _)%nat => exact Q3
         | |- 0 < _ <= 20000 => first [exact HW1 | exact HH1]
         | |- _ = (_ * 8 + 31) / 32 => exact HWPL
         | |- 4 * _ <= _ => exact HRS1
         | |- u32arr _ _ _ _ => first [exact UAS | exact UAD | exact UAQ]
         | |- Z.of_nat (length _) = _ => first [assumption | idtac "LEFT-len"]
         | |- acc _ _ _ _ => first [assumption | idtac "LEFT-acc"]
         | |- 0 < _ => first [assumption | idtac "LEFT-pos"]
         | |- _ mod _ = 0 => first [assumption | idtac "LEFT-mod"]
         | |- _ + _ <= 2 ^ _ => first [assumption | idtac "LEFT-hi"]
         | |- mem_inv _ _ => first [assumption | idtac "LEFT-mi"]
         | |- rw_cells _ ?mm ?A ?cs => first [ assumption | match goal with H : rw_cells _ mm ?B cs |- _ => replace A with B by (clear; lia); exact H end | idtac "LEFT-cells" A ]
         | |- _ \/ _ => first [ assumption | exact SSH | exact SSG | exact TSH | exact TSG | exact QSH | exact QSG | exact ASD' | exact AQD' | exact WSEP | exact PSEP | exact BSEP | idtac "LEFT-disj" ]
         | |- ?g => idtac "LEFT:" g
         end. }
      cbn [mkR].
      repeat first [ lazymatch goal with |- @eq Z _ _ => clear; lia end | progress f_equal | reflexivity ]. }
    idtac "MARK fresh rows applied".
    intros ms' PO. unfold thr_rows_exit in PO.
    destruct PO as (t0w & a0w & a2w & a3w & a5w & a6w & a7w & s4w & s8w & mw & wdw & -> & MUw & WMw & MIw & UASw & ACSw & UAQw & ACQw & UADw & UADLw & ACDw & T80w & T96w & S144w).
    clear T80 T96 S144 UAS UASL UAD UADL UAQ UAQL ACS ACD ACQ Q1 Q3 T80w T96w S144w UASw UAQw UADw UADLw ACSw ACQw ACDw ws wd qws sbs dbs qbs.
    loop_art RT AF Σr mw lo MUw ltac:(cbn [ivls_client]; split; [intros zz Hzz; right; right; left; exists dat, rs; split; [exact DDINr| clear - Hzz ERS; lia]| exact I]).
    idtac "MARK fresh loop_art".
    lazymatch type of MUw with munch _ ?ma ?mb =>
      loop_transport ma mb MUw ltac:(fun Hx => lazymatch type of Hx with (?A <= _ < _)%Z =>
        lazymatch A with
        | fr => clear - Hx FCDD ERS
        | (fr + _)%Z => clear - Hx FCDD ERS
        | (fr / 8 + _)%Z => clear - Hx FCSD ERS FR64 FR0 FRSEG FRSH
        | pix => clear - Hx ADP ERS
        | pixd => clear - Hx ADX ERS
        | pixt => clear - Hx BTD ERS
        | cmap => clear - Hx ADCM ERS
        | (usp + _)%Z => clear - Hx CKRD ERS LOW LOR FRHI
        | (usp - _)%Z => clear - Hx CKRD ERS LOW LOR FRHI
        | lo => clear - Hx CKRD ERS LOW LOR FRHI
        | _ => clear - Hx CKSD ERS FRSEG
        end; unfold parked in *; unfold SEGTOP_A, shad, SHB in *; repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia] end) end.
    idtac "MARK fresh loop_transport".
    cps_stop.
    art_now RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; right; right; left; exists dat, rs; split; [exact DDINr| clear - Hzz ERS; lia]| exact I]).
    lazymatch goal with MUx : munch _ ?mm mw |- _ =>
      agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; destruct Hx as [Hx Ho]; pose proof (NCD _ Hx) as NCx; clear - NCx ERS; repeat split; try exact I; lia) end.
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. clear_acc. park_disj.
    ctx_gc RT.
    idtac "MARK fresh after rows".
    (* [comment removed for export] *)
    Time walk_to AF MST [(usp - 320, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [e_free].
    assert (TRF : In (0xa00ec :: bv_unsigned ra :: ras) CLIENT_TRACES) by (rewrite RAF, RAS; unfold RA_FUZZ_OP6, D_libiface.RA_TOP; apply ct_mem_In; vm_compute; reflexivity).
    pose proof FR as FRrec. split_before FRrec (C8 s0) FRrec2. clear FRrec.
    lazymatch goal with A : ART RT Σr ?mm |- _ =>
      assert (NXTB : parked (pix <> tab)) by (exact (fresh_chunk_ne RT AF Σr mm [(dtt, rst); (pixt, 64); (dat, rs); (pixd, 64)] tab 1024 ((carr, 1024) :: (cmap, 24) :: rt_live RT Σ) (pix, 64) A LVR ltac:(cbn [app In]; do 6 right; exact PIN) ltac:(clear; lia) ltac:(cbn; clear; lia)));
      assert (NCMTB : parked (cmap <> tab)) by (exact (fresh_chunk_ne RT AF Σr mm [(dtt, rst); (pixt, 64); (dat, rs); (pixd, 64)] tab 1024 ((carr, 1024) :: (cmap, 24) :: rt_live RT Σ) (cmap, 24) A LVR ltac:(cbn [app In]; do 5 right; left; reflexivity) ltac:(clear; lia) ltac:(cbn; clear; lia)));
      assert (NETB : forall e, In e ([(dtt, rst); (pixt, 64); (dat, rs); (pixd, 64)] ++ (carr, 1024) :: (cmap, 24) :: rt_live RT Σ) -> fst e <> tab)
        by (intros e He; apply (fresh_chunk_ne RT AF Σr mm [(dtt, rst); (pixt, 64); (dat, rs); (pixd, 64)] tab 1024 ((carr, 1024) :: (cmap, 24) :: rt_live RT Σ) e A LVR He ltac:(clear; lia));
            destruct e as [q k]; cbn [app In] in He; cbn [snd]; destruct He as [E|[E|[E|[E|[E|[E|He]]]]]];
            [injection E as <- <-; exact DTN| injection E as <- <-; clear; lia| injection E as <- <-; exact DDN| injection E as <- <-; clear; lia| injection E as <- <-; clear; lia| injection E as <- <-; clear; lia| exact (LVP q k He)]) end.
    assert (TQU : dtt <> tab) by (unpark FUQ; intro E; apply FUQ; symmetry; exact E).
    assert (TQT : pixt <> tab) by (unpark FTQ; intro E; apply FTQ; symmetry; exact E).
    park_ne.
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                  ltac:(fun Hx => cbn [outside]; destruct Hx as [Hx Ho]; pose proof (PFS _ Hx) as P1; destruct (NFA _ Hx) as [N1 N2]; clear - P1 N1 N2 LOW LOR SPT SPA SPB FR0 FR64;
                        unfold shad, SHB in *; repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
    eapply cps_seq.
    { pose proof (gp_free RT GP) as FC; unfold free_contractC in FC; eapply FC with (lo := lo) (p := tab) (n := 1024); rt_side idtac.
      all: lazymatch goal with
           | |- In _ _ => exact TBINr
           | |- unwind_okC _ _ _ _ =>
               exists (bv_unsigned ra :: ras); rewrite ?unsigned_lit by ul; split; [| exact TRF];
               apply CHAIN; [apply AGS1; exact AGF|];
               lazymatch type of FRrec2 with rw_cells _ _ ?A _ => replace (usp + -16) with A by (clear; lia) end; exact FRrec2
           | |- ?g => idtac "LEFT:" g
           end. }
    idtac "MARK fresh free applied".
    clear FRrec2.
    after_call RT AF.
    lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ => rename S into Σf; rename A into ARTF end.
    lazymatch goal with H : rt_live RT Σf = live_remove tab _ |- _ => rename H into LVFr end.
    assert (LVFq : rt_live RT Σf = (dtt, rst) :: (pixt, 64) :: (dat, rs) :: (pixd, 64) :: (carr, 1024) :: (cmap, 24) :: rt_live RT Σ).
    { rewrite LVFr, LVR. unpark TQU; unpark TQT; unpark NPTB; unpark NDTB. rewrite ?live_remove_other by assumption. rewrite live_remove_head.
      rewrite (live_remove_fresh tab); [reflexivity|]. intros e He. apply NETB. cbn [app]; do 4 right; exact He. }
    park_ne.
    fold_ag ltac:(fun Hx => destruct Hx as [Hx Ho]; apply (aclient_mono LVF _ usp _ _ _ _ Hx); [intros e He; rewrite LVFq; do 6 right; exact He| solve [frames_sub_tac]| clear; lia]).
    idtac "MARK fresh after free".
    lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ => rename mm into mf end.
    assert (FRSf : rt_frames RT Σf = (fr, 2%nat) :: rt_frames RT Σ) by (repeat match goal with E : rt_frames RT Σf = _ |- _ => rewrite E end; exact FRSr).
    assert (SP0f : rt_sp0 RT Σf = rt_sp0 RT Σ) by (repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; reflexivity).
    assert (CRf : rt_credit RT Σ - (2 * RASTER_COST + 44) <= rt_credit RT Σf) by (repeat match goal with E : rt_credit RT Σf = _ |- _ => rewrite E end; exact CRr).
    assert (LVPf : forall e, In e (rt_live RT Σf) -> 0 < snd e).
    { intros [q k] Hq. rewrite LVFq in Hq. cbn [In] in Hq. cbn [snd].
      destruct Hq as [E|[E|[E|[E|[E|[E|Hq]]]]]]; [injection E as <- <-; exact DTN| injection E as <- <-; clear; lia| injection E as <- <-; exact DDN| injection E as <- <-; clear; lia| injection E as <- <-; clear; lia| injection E as <- <-; clear; lia| exact (LVP q k Hq)]. }
    unfold hid in SUBT, SUBDT.
    assert (SUBT' : forall e, In e ((dat, rs) :: (pixd, 64) :: (tab, 1024) :: (carr, 1024) :: (cmap, 24) :: rt_live RT Σ) -> fst e <> pixt) by (intros e He; exact (proj2 (SUBT e He))).
    assert (SUBDT' : forall e, In e ((dat, rs) :: (pixd, 64) :: (tab, 1024) :: (carr, 1024) :: (cmap, 24) :: rt_live RT Σ) -> fst e <> dtt) by (intros e He; exact (proj2 (SUBDT e He))).
    clear SUBT SUBDT.
    sigma_gc RT Σ Σf.
    assert (LSUBf : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σf)) by (intros e He; rewrite LVFq; do 6 right; exact He).
    assert (DTINf : In (dtt, rst) (rt_live RT Σf)) by (rewrite LVFq; left; reflexivity).
    assert (PTINf : In (pixt, 64) (rt_live RT Σf)) by (rewrite LVFq; right; left; reflexivity).
    assert (DDINf : In (dat, rs) (rt_live RT Σf)) by (rewrite LVFq; do 2 right; left; reflexivity).
    assert (PDINf : In (pixd, 64) (rt_live RT Σf)) by (rewrite LVFq; do 3 right; left; reflexivity).
    assert (CAINf : In (carr, 1024) (rt_live RT Σf)) by (rewrite LVFq; do 4 right; left; reflexivity).
    assert (CMINf : In (cmap, 24) (rt_live RT Σf)) by (rewrite LVFq; do 5 right; left; reflexivity).
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj. park_ne.
    ctx_gc RT.
    (* [comment removed for export] *)
    Time walk_to AF MST [(usp - 320, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [e_pixDestroy].
    split_before FRM (C8 (Z_to_bv 64 pixt)) FPT. split_at FPT 1%nat FRMb.
    pose proof FSH as SHT. split_at SHT 20%nat SHT2. split_at SHT2 1%nat SHT3. clear SHT SHT3.
    pose proof FR as FRrec. split_before FRrec (C8 s0) FRrec2. clear FRrec.
    at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
                  ltac:(fun Hx => cbn [outside]; destruct Hx as [Hx Ho]; pose proof (PFS _ Hx) as P1; destruct (NFA _ Hx) as [N1 N2]; clear - P1 N1 N2 LOW LOR SPT SPA SPB FR0 FR64;
                        unfold shad, SHB in *; repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]).
    unfold hid in HOKT.
    lazymatch goal with PT : rw_cells asegs ?mc pixt _ |- cps _ (ASTA RT Σf _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
      assert (POT4 : pix_obj (rt_live RT Σf) mc pixt vt (mkCmapv 0 0 0 0))
        by (split; [unfold pix_cells; rewrite VWT, VHT, VDT, VCMAPT, EWT; exact PT|];
            split; [split; [exact PTINf| split; [exact PT0| split; [exact PT16| clear; lia]]]|];
            split; [exact HOKT|];
            split; [right; split; [split; [exact DTINf| split; [exact DT0| split; [exact DT16| exact DTN]]]| unpark DTNE; exact DTNE]| left; exact VCMAPT]);
      assert (OPP : optrL RT (live_destroy pixt vt (mkCmapv 0 0 0 0) (rt_live RT Σf)) Σf mc (fr + 160) 8)
        by (unfold optrL; split;
            [ right; exists fr, 2%nat; rewrite FRSf; change (fs_size 2) with 256; split; [left; reflexivity|]; split; [clear; lia|]; split; [clear; lia|];
              split; [clear - FR64; Z.div_mod_to_equations; lia|]; split; [clear - FR0; lia|]; split; [clear - FRHI SP0R1; lia|];
              replace (shad (fr + 160)) with (fr / 8 + 2147450900) by (unfold shad, SHB; clear - FR64; Z.div_mod_to_equations; lia); destruct SHT2 as [[_ B] _]; exact B
            | pose proof FRSH as Q; unfold parked in Q; clear - Q FR0 FR64 FRSEG; unfold SEGTOP_A; repeat split; first [lia | Z.div_mod_to_equations; lia] ]) end.
    hide HOKT.
    idtac "MARK fresh destroy args".
    eapply cps_seq.
    { pose proof PDY as PD; unfold pixDestroy_cps in PD.
      eapply PD with (lo := lo) (pp := fr + 160) (pix := pixt) (v := vt) (cv := mkCmapv 0 0 0 0) (ras := bv_unsigned ra :: ras).
      - exact FDO.
      - exact MST.
      - reflexivity.
      - reflexivity.
      - exact OPP.
      - exact FPT.
      - exact POT4.
      - unfold uctx. rewrite !unsigned_lit by (clear - USP0 USP1 LOR STa; lia). apply CHAIN; [apply AGS1; exact AGF|].
        lazymatch type of FRrec2 with rw_cells _ _ ?A _ => replace (usp + -16) with A by (clear; lia) end. exact FRrec2.
      - rewrite RAF, RAS. unfold DESTROY_FREE_RAS, RA_FUZZ_OP6, D_libiface.RA_TOP. rewrite unsigned_lit by (clear; lia).
        repeat (apply Forall_cons; [apply ct_mem_In; vm_compute; reflexivity |]). apply Forall_nil.
      - lenv_tac.
      - unfold lres; rewrite FRSf, LVFq; cbn [length]; unfold FRAMES_MAX, LIVE_MAX in *; unfold LVF in *;
        repeat split; [clear - FRB; lia| clear - LVB; lia| clear - CRf CRB; unfold RASTER_COST in *; lia| intros p n Hp; exact (LVPf (p, n) ltac:(rewrite LVFq; exact Hp))]. }
    idtac "MARK fresh destroy applied".
    clear POT4 OPP FPT SHT2 FRrec2. lazymatch goal with PT : rw_cells asegs _ pixt _ |- _ => clear PT end.
    (* [comment removed for export] *)
    hide FRM. hide FRMb. hide FSH. hide PXD. hide PXS. hide CMCc.
    clear_acc.
    after_call RT AF.
    lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ _) _ => rename S into Σz; rename A into ARTZ; rename mm into mz end.
    assert (LVZ : rt_live RT Σz = (dat, rs) :: (pixd, 64) :: (carr, 1024) :: (cmap, 24) :: rt_live RT Σ).
    { repeat match goal with E : rt_live RT Σz = _ |- _ => rewrite E end. rewrite LVFq.
      pose proof (live_destroy_tmpl ((dat, rs) :: (pixd, 64) :: (carr, 1024) :: (cmap, 24) :: rt_live RT Σ) pixt dtt rst 0 0 0 vt (mkCmapv 0 0 0 0) eq_refl VCMAPT
                    (fun N => False_ind _ (N eq_refl)) ltac:(clear - DT0; lia) ltac:(unpark DTNE; exact DTNE) (fun N => False_ind _ (N eq_refl))
                    ltac:(intros e He; cbn [In] in He; split; [apply (SUBT' e) | apply (SUBDT' e)];
                          (cbn [In]; destruct He as [He|[He|He]]; [left; exact He| right; left; exact He| do 3 right; exact He]))
                    (fun N => False_ind _ (N eq_refl))) as LD.
      cbn [Z.eqb] in LD. exact LD. }
    assert (FRSz : rt_frames RT Σz = (fr, 2%nat) :: rt_frames RT Σ) by (repeat match goal with E : rt_frames RT Σz = _ |- _ => rewrite E end; exact FRSf).
    assert (SP0z : rt_sp0 RT Σz = rt_sp0 RT Σ) by (repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; reflexivity).
    assert (CRz : rt_credit RT Σ - (2 * RASTER_COST + 45) <= rt_credit RT Σz) by (lazymatch goal with E : rt_credit RT Σf - 1 <= rt_credit RT Σz |- _ => clear - CRf E; lia end).
    assert (LSUBz : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σz)) by (intros e He; rewrite LVZ; do 4 right; exact He).
    clear SUBT' SUBDT'.
    lazymatch goal with AGx : agree_on _ _ ?mb, A : ART RT _ ?mb |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mb _))) _ =>
      carry AGx FRM ltac:(fun x Hx => right; right; right; left; exists fr, 2%nat; split; [frames_in_tac| change (fs_size 2%nat) with 256; clear - Hx; lia]) ltac:(fun Hx => clear - Hx; lia);
      carry AGx FRMb ltac:(fun x Hx => right; right; right; left; exists fr, 2%nat; split; [frames_in_tac| change (fs_size 2%nat) with 256; clear - Hx; lia]) ltac:(fun Hx => clear - Hx; lia);
      carry AGx FSH ltac:(fun x Hx => right; right; right; right; exists fr, 2%nat; split; [frames_in_tac| change (fs_size 2%nat) with 256; unfold shad, SHB; clear - Hx FR64; Z.div_mod_to_equations; lia])
                    ltac:(fun Hx => unfold parked in FRSH; unfold shad, SHB in *; clear - Hx FR64 FRSH; first [lia | Z.div_mod_to_equations; lia]);
      carry AGx PXD ltac:(fun x Hx => right; right; left; exists pixd, 64; split; [rewrite LVZ; right; left; reflexivity| exact Hx]) ltac:(fun Hx => unfold parked in FCD1; clear - Hx FCD1; lia);
      carry AGx PXS ltac:(fun x Hx => right; right; left; exists pix, 64; split; [rewrite LVZ; do 4 right; exact PIN| exact Hx]) ltac:(fun Hx => unfold parked in FCD; clear - Hx FCD; lia);
      carry AGx CMCc ltac:(fun x Hx => right; right; left; exists cmap, 24; split; [rewrite LVZ; do 3 right; left; reflexivity| exact Hx]) ltac:(fun Hx => unfold parked in FCD5; clear - Hx FCD5; lia) end.
    park_disj.
    idtac "MARK fresh carried z".
    fold_ag ltac:(fun Hx => destruct Hx as [Hx Ho]; split; [apply (aclient_mono LVF _ usp _ _ _ _ Hx); [first [solve [live_add_tac] | intros e He; repeat match goal with E : rt_live RT _ = _ |- _ => rewrite E end; do 4 right; exact He]| solve [frames_sub_tac]| clear; lia]|
                                    cbn [outside]; cbn [outside] in Ho; destruct (NFA _ Hx) as [N1 N2]; clear - N1 N2 Ho; repeat split; try exact I; lia]).
    idtac "MARK fresh after destroy".
    (* [comment removed for export] *)
    assert (FZP : forall e, In e (rt_live RT Σ) -> fst e <> pixd) by (intros e He; apply (fresh_chunk_ne RT AF Σz mz [(dat, rs)] pixd 64 _ e ARTZ LVZ); [cbn [app In]; do 3 right; exact He| clear; lia| destruct e as [eq ek]; exact (LVP eq ek He)]).
    assert (FZD : forall e, In e (rt_live RT Σ) -> fst e <> dat) by (intros e He; apply (fresh_chunk_ne RT AF Σz mz [] dat rs _ e ARTZ LVZ); [cbn [app In]; do 3 right; exact He| clear - DDN; lia| destruct e as [eq ek]; exact (LVP eq ek He)]).
    assert (FZA : forall e, In e (rt_live RT Σ) -> fst e <> carr) by (intros e He; apply (fresh_chunk_ne RT AF Σz mz [(dat, rs); (pixd, 64)] carr 1024 _ e ARTZ LVZ); [cbn [app In]; do 3 right; exact He| clear; lia| destruct e as [eq ek]; exact (LVP eq ek He)]).
    assert (FZC : forall e, In e (rt_live RT Σ) -> fst e <> cmap) by (intros e He; apply (fresh_chunk_ne RT AF Σz mz [(dat, rs); (pixd, 64); (carr, 1024)] cmap 24 _ e ARTZ LVZ); [cbn [app In]; do 3 right; exact He| clear; lia| destruct e as [eq ek]; exact (LVP eq ek He)]).
    sigma_gc RT Σ Σz.
    assert (PDINz : In (pixd, 64) (rt_live RT Σz)) by (rewrite LVZ; right; left; reflexivity).
    assert (DDINz : In (dat, rs) (rt_live RT Σz)) by (rewrite LVZ; left; reflexivity).
    assert (CMINz : In (cmap, 24) (rt_live RT Σz)) by (rewrite LVZ; do 3 right; left; reflexivity).
    assert (CAINz : In (carr, 1024) (rt_live RT Σz)) by (rewrite LVZ; do 2 right; left; reflexivity).
    assert (PXINz : In (pix, 64) (rt_live RT Σz)) by (apply LSUBz; exact PIN).
    refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj. park_ne.
    ctx_gc RT.
    idtac "MARK fresh names z".
    forget_junk FR. forget_junk FRM. try forget_junk FRMb.
    (* [comment removed for export] *)
    try (lazymatch goal with H : rw_cells asegs _ pix (pix_cells_rc v _) |- _ => rename H into PXS end).
    lazymatch goal with H : rw_cells asegs _ cmap _ |- _ => rename H into CMC end.
    hide PXS. hide PXD. hide CMC.
    clear_acc.
    repeat match goal with H : u32arr _ _ _ _ |- _ => clear H end.
    hide VDATA1. hide DDNE. hide NPCM. hide NPCA. hide NDCM. hide NDCA. hide CNE.
    hide FRSH.   (* [comment removed for export] *)
    repeat match goal with H : parked (fr + 256 <= ?b \/ _ <= fr) |- _ => lazymatch b with pix => hide H | pixd => hide H | cmap => hide H | _ => clear H end end.
    repeat match goal with H : parked (?b + _ <= fr / 8 + 2147450880 \/ _ <= ?b) |- _ => lazymatch b with pix => hide H | pixd => hide H | cmap => hide H | _ => clear H end end.
    repeat match goal with H : parked _ |- _ => clear H end.
    unfold hid in FRSH. unpark FRSH.
    idtac "MARK fresh diet".
    (* [comment removed for export] *)
    Time walk_to AF MST [(usp - 320, usp); (fr, fr + 248); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 32)] [0x9fe94].
    idtac "MARK fresh at pokes".
    split_at FRM 1%nat FRMr.
    Time (eapply evt_cut;
    [ eapply EVQ_thr;
      [ eapply thr_exit_x1; [exact FR0| exact FR64| clear - FRHI SP0R1; lia| exact FRM| exact FSH| reflexivity| assumption]
      | cbn [mkR]; repeat first [ lazymatch goal with |- @eq Z _ _ => clear; lia end | progress f_equal | reflexivity ] ]
    | ]).
    clear FRM FSH. intros ms' PO. destruct PO as (mx & -> & MUx & WMx & MIx & FRM & FSH). unfold thr_exit_W, SHB in MUx. unfold thr_sh_f5 in FSH.
    idtac "MARK fresh pokes applied".
    Time loop_art RT AF Σz mx lo MUx ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]]).
    Time (lazymatch type of MUx with munch _ ?ma ?mb =>
      loop_transport ma mb MUx ltac:(fun Hx => cbn [outside]; unfold shad, SHB in *; clear - Hx FRHI FRSH FRSEG LOW LOR FR64 FR0 SP0R1 SP0R0 SP0W; repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia]) end).
    idtac "MARK fresh at flag load".
    repeat match goal with H : hid (parked _) |- _ => unfold hid in H end.
    Time (lazymatch goal with AGFx : agree_on ?PFx _ ?mm, MUy : munch _ ?mm _ |- _ =>
      carry_mu MUy PXS ltac:(fun Hx => seg_side fr pix FR64 LOW LOR Hx);
      carry_mu MUy PXD ltac:(fun Hx => seg_side fr pixd FR64 LOW LOR Hx);
      carry_mu MUy CMC ltac:(fun Hx => seg_side fr cmap FR64 LOW LOR Hx) end).
    hide PXS. hide PXD. hide CMC.
    join_cells FRM FRMr.
    idtac "MARK fresh carried x".
    frame_release_g RT AF GP MST Σ fr 2%nat 256 PF AGF PFS1 usp lo 0x9ff4c
        ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; fframe_tac | split; [intros zz Hzz; fframe_tac| exact I]]])
        ltac:(fun Hx => cbn [outside]; destruct Hx as [Hx Ho]; pose proof (PFS _ Hx) as P1; destruct (NFA _ Hx) as [N1 N2]; clear - P1 N1 N2 LOW LOR SPT SPA SPB FR0 FR64;
                        unfold shad, SHB in *; repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia])
        ltac:(fun Hx => exact (proj1 Hx))
        ltac:(fun fl FLN => idtac).
    idtac "MARK fresh released".
    lazymatch goal with MUx : munch [(?fl, ?fl + 1)] _ ?mb |- _ =>
      carry_mu MUx PXS ltac:(fun Hx => flag_side fl pix Hx);
      carry_mu MUx PXD ltac:(fun Hx => flag_side fl pixd Hx);
      carry_mu MUx CMC ltac:(fun Hx => flag_side fl cmap Hx) end.
    hide PXS. hide PXD. hide CMC.
    clear_acc. refresh RT AF. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj. park_ne.
    (* [comment removed for export] *)
    change (bv_unsigned sp) with usp. rewrite ESP.
    Time walk_to AF MST [(usp - 320, usp)] (@nil Z).
    
    lazymatch goal with MUx : munch _ _ ?mb |- evt _ _ (MS _ _ _ _ _ ?mb _) =>
      carry_mu MUx PXS ltac:(fun Hx => stk_side pix LOW LOR Hx);
      carry_mu MUx PXD ltac:(fun Hx => stk_side pixd LOW LOR Hx);
      carry_mu MUx CMC ltac:(fun Hx => stk_side cmap LOW LOR Hx) end.
    cps_stop.
    try fold_mkR.
    unfold hid in VDATA1, DDNE, NPCM, NPCA, NDCM, NDCA, CNE.
    idtac "MARK fresh epilogue".
    (* [comment removed for export] *)
    apply cps_finish. intros c Hc. subst QF. cbv beta.
    set (vf := mkPixv (p_w v) (p_h v) 8 (p_spp v1) (p_wpl v) (p_xres v) (p_yres v) (p_inf v) (p_spec v1) cmap dat).
    unfold hid in POBJ0, HOKD.
    assert (LVE : rt_live RT S2 = (dat, rs) :: (pixd, 64) :: (carr, 1024) :: (cmap, 24) :: LVF) by (rewrite LV2; exact LVZ).
    assert (LSUB2 : forall e, In e LVF -> In e (rt_live RT S2)) by (intros e He; rewrite LVE; do 4 right; exact He).
    exists S2, pixd, vf, (mkCmapv carr 8 256 5).
    split.
    + eapply (ASTA_conseq RT); [exact Hc|]. intros ms <-. eexists.
      split; [unfold ret_st; rewrite ?ESP; do 16 eexists; reflexivity|].
      split; [unfold rt_after_f; split; [split; [exact ART2| split; assumption]| split; assumption]|].
      split; [intros a Ha Ho; apply AGF; split; [exact Ha| exact Ho]|].
      split.
      { (* [comment removed for export] *)
        lazymatch goal with |- pix_obj _ ?mc _ _ _ =>
          apply (pix_obj_mono LVF _ mc pix v cv LSUB2);
          apply (pix_obj_agree_cm LVF PF m mc pix v cv POBJ0 AGF);
          [ intros NZ a Ha;
            assert (PCIN : In (p_cmap v, 24) LVF) by (destruct POBJ0 as (_ & _ & _ & _ & [Z0|((_ & (CI & _) & _) & _)]); [exfalso; exact (NZ Z0)| exact CI]);
            pose proof (live_apart2 RT AF S2 mc (p_cmap v) 24 pix 64 ART2 (LSUB2 _ PCIN) (LSUB2 _ PIN) ltac:(clear; intros E; injection E; lia)) as APC;
            split; [exact (PML _ _ a PCIN Ha)| cbn [outside]; clear - Ha APC; split; [lia| exact I]]
          | unfold pix_cells; rewrite D8; lazymatch goal with PS : rw_cells asegs mc pix _ |- _ => exact PS end ] end. }
      right. split; [| cbn [p_data]; unpark VDATA1; exact VDATA1].
      split; [unfold pix_cells; cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data]; lazymatch goal with PX : rw_cells asegs _ pixd _ |- _ => exact PX end|].
      split; [split; [rewrite LVE; right; left; reflexivity| split; [exact PD0| split; [exact PD16| clear; lia]]]|].
      split; [unfold pix_hdr_ok; cbn [p_w p_h p_d p_wpl]; unfold pix_hdr_ok in HOKD; rewrite VW, VH, VD, EWD in HOKD; exact HOKD|].
      split; [right; unfold vf, rsize; cbn [p_data p_wpl p_h]; split; [split; [rewrite LVE, ERS; left; reflexivity| split; [exact DD0| split; [exact DD16| clear - DDN ERS; lia]]]| unpark DDNE; exact DDNE]|].
      right. cbn [p_cmap p_data c_arr].
      split.
      { split; [exists cpad; unfold cmap_cells; cbn [c_arr c_depth c_nalloc c_n]; lazymatch goal with CC : rw_cells asegs _ cmap _ |- _ => exact CC end|].
        split; [split; [rewrite LVE; do 3 right; left; reflexivity| split; [exact CM0| split; [exact CM16| clear; lia]]]|].
        split; [cbn [c_arr c_nalloc]; split; [rewrite LVE; do 2 right; left; reflexivity| split; [exact CA0| split; [exact CA16| clear; lia]]]|].
        split; [exact COK| cbn [c_arr]; unpark CNE; exact CNE]. }
      unpark NPCM; unpark NPCA; unpark NDCM; unpark NDCA.
      repeat split; intro E; [apply NPCM | apply NPCA | apply NDCM | apply NDCA]; symmetry; exact E.
    + split; [intros Z0; exfalso; clear - Z0 PD0; lia|].
      split.
      { intros _. rewrite LVE. unfold LVF.
        unpark VDATA1; unpark DDNE; unpark NPCM; unpark NPCA; unpark NDCM; unpark NDCA; unpark CNE.
        apply (live_destroy_thr (rt_live RT Σ) pixd dat rs cmap carr 1024 vf (mkCmapv carr 8 256 5));
          [reflexivity| reflexivity| reflexivity| exact VDATA1| clear - CM0; lia| clear - CA0; lia
          | exact DDNE| exact NDCA| exact NDCM| intro E; apply NPCA; symmetry; exact E| intro E; apply NPCM; symmetry; exact E| intro E; apply CNE; symmetry; exact E
          | exact FZP| exact FZD| exact FZC| exact FZA]. }
      split.
      { intros p n Hp. rewrite LVE in Hp. cbn [In] in Hp.
        destruct Hp as [E|[E|[E|[E|Hp]]]]; [injection E as <- <-; exact DDN| injection E as <- <-; clear; lia| injection E as <- <-; clear; lia| injection E as <- <-; clear; lia| exact (LVP p n Hp)]. }
      split; [rewrite LVE; unfold LVF; cbn [length]; lia|].
      split; [rewrite FRS2; first [reflexivity | exact FRSz]|]. split; [rewrite SP2; first [exact SP0z | reflexivity]|].
      rewrite D8. cbn [Z.eqb Pos.eqb]. rewrite CR2. clear - CRz. unfold RASTER_COST in *. lia.
Qed.
End THR_c0.
