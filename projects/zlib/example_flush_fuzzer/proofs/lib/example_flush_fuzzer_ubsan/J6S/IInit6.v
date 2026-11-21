(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool FMapPositive.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1 Require Import SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux RomRead STower.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import Prog ZIface InflateState InflateFast InflateArms Inflate
     InflateInv HarnessKit HarnessFacts HarnessSmallFacts.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.FMQ6 Require Import CallocLib6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6S Require Import Segs6 Callee6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1 Require Import MemFill.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S Require Import ISLayout IS6 InflMem InflRod6 InflCtx6 InflArmLib6.
Local Ltac Zify.zify_post_hook ::= idtac.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

Definition pc6_ii : Z := 0x1ce50.

Definition KI6 : Z := 7.
Definition is0c : inflate_state :=
  mkIS 16180 0 5 0 (-1) 32768 0 0 0 15 0 0 0 (arr_make 0 0) None 0 0 0 0 0 (CDyn 0) (CDyn 0) 0 0 0 0 0 0 0
       (arr_make 320 0) (arr_make 288 0) (arr_make 1444 0) 1 (-1) 0 7%N.
Lemma is0_eq : is0 KI6 = is0c.
Proof. reflexivity. Qed.
Lemma arr_get_make0 : forall n i, arr_get (arr_make n 0) i = 0.
Proof. intros n i. unfold arr_get, arr_make. cbn. rewrite FMapPositive.PositiveMap.gempty. destruct (_ && _)%bool; reflexivity. Qed.

Lemma cell_av : forall m a a' (w : nat) v v',
  cell s6_segs m a w v -> a = a' -> v mod 2 ^ (8 * Z.of_nat w) = v' mod 2 ^ (8 * Z.of_nat w) -> cell s6_segs m a' w v'.
Proof. intros m a a' w v v' H <- E. exact (cell_eqm s6_segs m a w v v' H E). Qed.
Lemma cell_sd_lo : forall m a v, 0 <= a -> a + 8 <= 2 ^ 64 ->
  cell s6_segs (wbytes m (zw a) (Z_to_le_bytes 8 v)) a 4 v.
Proof.
  intros m a v Ha Hb. rewrite wbytes_sd_split.
  apply cell_write_other; [apply cell_write_same; cbn; lia | lia | cbn; lia | lia | cbn; lia | cbn; lia].
Qed.
Lemma cell_sd_hi : forall m a v, 0 <= a -> a + 8 <= 2 ^ 64 ->
  cell s6_segs (wbytes m (zw a) (Z_to_le_bytes 8 v)) (a + 4) 4 (Z.shiftr v 32).
Proof. intros m a v Ha Hb. rewrite wbytes_sd_split. apply cell_write_same; cbn; lia. Qed.
Definition zblock (m : word -> option byte) (P N : Z) : Prop :=
  forall x : word, P <= bv_unsigned x < P + N -> m x = Some (Z_to_bv 8 0).
Lemma cell_zero_of_zblock : forall m P N a (w : nat),
  zblock m P N -> P <= a -> a + Z.of_nat w <= P + N -> 0 <= P -> P + N < 2 ^ 64 ->
  cell s6_segs m a w 0.
Proof.
  intros m P N a w Hz H1 H2 H3 H4. unfold cell.
  apply rdn_pointwise; [apply length_Z_to_le_bytes | rewrite u_zw_small by lia; lia |].
  intros j Hj. rewrite u_zw_small by lia.
  rewrite (Hz (Z_to_bv 64 (a + Z.of_nat j))) by (change (Z_to_bv 64 (a + Z.of_nat j)) with (zw (a + Z.of_nat j)); rewrite u_zw_small by lia; lia).
  f_equal. clear. revert j. induction w as [|w IH]; intros [|j]; cbn; try reflexivity. apply IH.
Qed.
Lemma cells_zero_of_zblock : forall m P N Q st (w : nat) n f,
  zblock m P N -> (forall i, f i = 0) -> Z.of_nat w <= st ->
  P <= Q -> Q + st * n <= P + N -> 0 <= P -> P + N < 2 ^ 64 -> 0 <= n ->
  cells s6_segs m Q st w n f.
Proof.
  intros m P N Q st w n f Hz Hf Hw H1 H2 H3 H4 Hn i Hi. rewrite Hf.
  apply (cell_zero_of_zblock m P N); [exact Hz | nia | nia | lia | lia].
Qed.

End FXG.
Ltac pg := match goal with |- ?G => idtac "SIDE-FAIL" G; fail end.
Ltac lenlia := cbn [length Z_to_le_bytes Z.of_nat Pos.of_succ_nat Pos.succ Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul]; lia.
Ltac hcell_other base_tac :=
  apply cell_write_other; [ | first [lia|pg] | first [lenlia|pg] | first [lia|pg] | first [lenlia|pg] | first [lenlia | pg] ].
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.
End FXG.
Ltac zcell ZP :=
  lazymatch type of ZP with zblock ?M ?P ?N =>
  lazymatch goal with |- cell _ _ ?a ?w ?v =>
    apply (cell_av M a a w 0 v); [apply (cell_zero_of_zblock M P N); [exact ZP | lia | lenlia | lia | lia] | reflexivity | cbn; reflexivity]
  end end.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.
End FXG.
Ltac split_addr A :=
  lazymatch A with
  | ?B + ?k => constr:((B, k))
  | _ => constr:((A, 0))
  end.
Ltac hcell base_tac :=
  rewrite ?word_le_Z;
  lazymatch goal with
  | |- cell _ (wbytes _ (zw ?A) (Z_to_le_bytes ?wn ?v)) ?A' ?w _ =>
      let Bk := split_addr A in let Bo := split_addr A' in
      lazymatch Bk with (?B, ?k) =>
      lazymatch Bo with (?B', ?o) =>
      tryif constr_eq B B' then
       (let same := eval cbv in (Z.eqb o k && Nat.eqb w wn) in
        lazymatch same with
        | true => eapply cell_av; [apply cell_write_same; cbn; lia | lia | first [f_equal; lia | cbn; reflexivity] ]
        | false =>
            let lo := eval cbv in (Z.eqb o k && Nat.eqb w 4 && Nat.eqb wn 8) in
            lazymatch lo with
            | true => eapply cell_av; [apply cell_sd_lo; cbn; lia | lia | first [f_equal; lia | cbn; reflexivity] ]
            | false =>
                let hi := eval cbv in (Z.eqb o (k + 4) && Nat.eqb w 4 && Nat.eqb wn 8) in
                lazymatch hi with
                | true => eapply cell_av; [apply cell_sd_hi; cbn; lia | lia | first [f_equal; lia | cbn; reflexivity] ]
                | false => hcell_other base_tac; hcell base_tac
                end
            end
        end)
      else (hcell_other base_tac; hcell base_tac)
      end end
  | |- cell _ (wbytes _ _ _) _ _ _ => hcell_other base_tac; hcell base_tac
  | |- _ => first [ base_tac | match goal with |- ?G => idtac "HCELL-BASE-FAIL" G; fail end ]
  end.
Ltac hcells base_tac :=
  rewrite ?word_le_Z;
  lazymatch goal with
  | |- cells _ (wbytes _ _ _) _ _ _ _ _ =>
      apply cells_write_other; [ | lenlia | lia | lenlia | lia | lenlia | lenlia]; hcells base_tac
  | |- _ => first [ base_tac | match goal with |- ?G => idtac "HCELLS-BASE-FAIL" G; fail end ]
  end.
Ltac hagree :=
  lazymatch goal with
  | |- agree_out _ _ (wbytes _ _ _) =>
      apply agree_out_wbytes; [hagree | lia | cbn; lia
        | cbn [length Z_to_le_bytes Z.of_nat Pos.of_succ_nat Pos.succ];
          repeat first [ apply sub_franges_here; lia | apply sub_franges_later ] ]
  | |- _ => apply agree_out_refl
  end.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

Definition IIF (t strm p : Z) : franges := [(t - 80, 80); (strm, 112); (p, 7176)].

(* 1.4: inflateInit_ clears state + 8 .. state + 7176 with memset (0x1ce08) after zalloc, then sets the
   fields and calls inflateReset (which replaces 1.3.1's inflateReset2 here). So the walk is: to the memset call,
   memset's spec, then to the return. *)
Lemma ii_run : forall (R : bvmap 5 word) (M : word -> option byte) (t p strm ra v16 v24 v32 : Z),
  memset_run6 ->
  getr R 2 = zw (t - 32) -> getr R 10 = zw p -> getr R 9 = zw strm ->
  cell s6_segs M (strm + 64) 8 0x19ff8 -> cell s6_segs M (strm + 72) 8 0x1a008 ->
  cell s6_segs M (t + -8) 8 ra -> cell s6_segs M (t + -16) 8 v16 -> cell s6_segs M (t + -24) 8 v24 -> cell s6_segs M (t + -32) 8 v32 ->
  zblock M p 7176 ->
  0 < p -> p + 7176 < 2 ^ 63 -> 80 <= t -> t < 2 ^ 63 -> 0 < strm -> strm + 112 < 2 ^ 63 ->
  0 <= ra < 2 ^ 64 -> ra mod 2 = 0 -> 0 <= v16 < 2 ^ 64 -> 0 <= v24 < 2 ^ 64 -> 0 <= v32 < 2 ^ 64 ->
  sep (t - 80) 80 p 7176 -> sep (t - 80) 80 strm 112 -> sep strm 112 p 7176 ->
  mapped M (t - 80) 80 -> mapped M p 7176 -> mapped M strm 112 ->
  exists R' M',
    msteps s6_segs (mkst R (Z_to_bv 64 pc6_ii) M s6_rom) (mkst R' (Z_to_bv 64 ra) M' s6_rom)
    /\ getr R' 2 = zw t /\ getr R' 10 = zw 0 /\ getr R' 8 = zw v16 /\ getr R' 9 = zw v24 /\ getr R' 18 = zw v32
    (* 1.4: memset (memset_clob) and inflateReset's a5 also clobber caller-saved registers *)
    /\ (forall rg, reg_in rg [1; 2; 5; 6; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 28; 29; 30; 31]%bv = false -> getr R' rg = getr R rg)
    /\ is6_scalars M' p (ISP strm 0) is0c /\ is6_arrays M' p is0c
    /\ cell s6_segs M' (strm + 16) 8 0 /\ cell s6_segs M' (strm + 40) 8 0 /\ cell s6_segs M' (strm + 48) 8 0
    /\ cell s6_segs M' (strm + 56) 8 p /\ cell s6_segs M' (strm + 64) 8 0x19ff8 /\ cell s6_segs M' (strm + 72) 8 0x1a008
    /\ cell s6_segs M' (strm + 96) 8 1
    (* 1.4: inflateResetKeep now clears strm->data_type (`sw zero,88(s0)` at 0x1cd20), so strm + 88 is no longer kept *)
    /\ (forall a (w : nat) v, In a [strm; strm + 8; strm + 24; strm + 32; strm + 80] -> cell s6_segs M a w v -> (w <= 8)%nat -> cell s6_segs M' a w v)
    /\ agree_out (IIF t strm p) M M' /\ mem_grows M M'.
Proof.
  intros R M t p strm ra v16 v24 v32 MS6 G2 G10 G9 C64 C72 Cm8 Cm16 Cm24 Cm32 ZP Hp0 Hp1 Ht0 Ht1 Hs0 Hs1 Hra RA2 Hv16 Hv24 Hv32 SEP1 SEP2 SEP3 MF MP MS.
  unfold mapped, sep in *.
  (* part 1: from zalloc's return to the memset call: state != 0, s0 := state, memset (state + 8, 0, 7168) *)
  symex s6_segs (CFG [] [] [] [A6_MEMSET] []) 20%nat [false] (@nil (option expr))
    [(2, EAdd (EVar 32%nat) (ELit (-32))); (10, EVar 33%nat); (9, EVar 34%nat)]
    [(32%nat, 2 ^ 63); (33%nat, 2 ^ 63); (34%nat, 2 ^ 63)]
    NoRegions [t; p; strm] NoVals F0 F0'
    (mkst R (Z_to_bv 64 pc6_ii) M s6_rom) R1 HR1 Hfr1 Hms1.
  all: match goal with |- exists _, _ => idtac | |- ?G => idtac "II1-LEFT" G end.
  symex_reg HR1 (1%bv : reg) as A1. symex_reg HR1 (10%bv : reg) as A10. symex_reg HR1 (11%bv : reg) as A11.
  symex_reg HR1 (12%bv : reg) as A12. symex_reg HR1 (8%bv : reg) as A8.
  (* part 2: memset's spec *)
  destruct (MS6 M R1 (p + 8) 0 7168 (zw 0x1ce6c) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(unfold mapped; intros x Hx; apply MP; lia) ltac:(apply ret_ok_lit; [lia | reflexivity])
              ltac:(change (reg_get R1 1) with (getr R1 1); rewrite A1; reflexivity)
              ltac:(change (reg_get R1 10) with (getr R1 10); rewrite A10; f_equal; lia)
              ltac:(change (reg_get R1 11) with (getr R1 11); rewrite A11; reflexivity)
              ltac:(change (reg_get R1 12) with (getr R1 12); rewrite A12; f_equal; lia))
    as (R2 & M2 & Hms2 & B10 & Hfr2 & FL2 & SO2 & GR2).
  assert (AG2 : agree_out [(p + 8, 7168)] M M2).
  { intros x Hx. apply SO2. intros Hin. apply Hx. cbn [in_franges]. left. lia. }
  assert (ZP2 : zblock M2 p 7176).
  { intros x Hx. destruct (Z_lt_le_dec (bv_unsigned x) (p + 8)) as [L|L].
    - rewrite (SO2 x) by lia. exact (ZP x Hx).
    - rewrite (FL2 x) by lia. reflexivity. }
  assert (TR : forall a (w : nat) v, cell s6_segs M a w v -> 0 <= a -> a + Z.of_nat w <= 2 ^ 64 ->
                 (a + Z.of_nat w <= p + 8 \/ p + 8 + 7168 <= a) -> cell s6_segs M2 a w v).
  { intros a w v Hc H0 H1 Hd. apply (cell_agree_out s6_segs [(p + 8, 7168)] M M2 a w v AG2); [| exact H0 | exact H1 | exact Hc].
    intros x Hx Hin. destruct Hin as [Hin|[]]. lia. }
  pose proof (TR _ _ _ C64 ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia)) as C64'.
  pose proof (TR _ _ _ C72 ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia)) as C72'.
  pose proof (TR _ _ _ Cm8 ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia)) as Cm8'.
  pose proof (TR _ _ _ Cm16 ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia)) as Cm16'.
  pose proof (TR _ _ _ Cm24 ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia)) as Cm24'.
  pose proof (TR _ _ _ Cm32 ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia)) as Cm32'.
  assert (H2s : getr R2 2 = zw (t - 32)) by (rewrite (Hfr2 (2%bv : reg) eq_refl), (Hfr1 (2%bv : reg) eq_refl); exact G2).
  assert (H8s : getr R2 8 = zw p) by (rewrite (Hfr2 (8%bv : reg) eq_refl); exact A8).
  assert (H9s : getr R2 9 = zw strm) by (rewrite (Hfr2 (9%bv : reg) eq_refl), (Hfr1 (9%bv : reg) eq_refl); exact G9).
  clear Cm8 Cm16 Cm24 Cm32 HR1.
  (* the stores of part 3 need the three blocks mapped in M2 (memset only grows the map) *)
  assert (MF2 : mapped M2 (t - 80) 80) by (unfold mapped; intros x Hx; apply GR2; exact (MF x Hx)).
  assert (MP2 : mapped M2 p 7176) by (unfold mapped; intros x Hx; apply GR2; exact (MP x Hx)).
  assert (MS2 : mapped M2 strm 112) by (unfold mapped; intros x Hx; apply GR2; exact (MS x Hx)).
  unfold mapped in MF2, MP2, MS2.
  (* part 3: the fields, inflateReset (inlined walk), the epilogue *)
  symex s6_segs (CFG [] [] [EVar 35%nat] [] []) 200%nat
    [false; false; false; false; false; true; false; true; false; false; false; false; false; true]
    [RVal (ELit 0x19ff8); RVal (ELit 0x1a008);
     RVal (EVar 35%nat); RVal (EVar 36%nat); RVal (EVar 37%nat); RVal (EVar 38%nat)]
    [(2, EAdd (EVar 32%nat) (ELit (-32))); (8, EVar 33%nat); (9, EVar 34%nat)]
    [(32%nat, 2 ^ 63); (33%nat, 2 ^ 63); (34%nat, 2 ^ 63); (35%nat, 2 ^ 64); (36%nat, 2 ^ 64); (37%nat, 2 ^ 64); (38%nat, 2 ^ 64)]
    NoRegions [t; p; strm; ra; v16; v24; v32] NoVals F0 F0'
    (mkst R2 (Z_to_bv 64 0x1ce6c) M2 s6_rom) R' HR' Hfr Hms.
  all: try (rewrite (land_m2_even ra) by exact RA2; reflexivity).
  all: match goal with |- exists _, exists _, _ => idtac | |- ?G => idtac "II-LEFT" G end.
  match type of Hms with msteps _ _ (mkst _ _ ?Mx _) => exists R', Mx end.
  split.
  { apply (msteps_trans _ _ (mkst R1 (Z_to_bv 64 A6_MEMSET) M s6_rom)); [by_run Hms1|].
    apply (msteps_trans _ _ (mkst R2 (Z_to_bv 64 0x1ce6c) M2 s6_rom)); [by_run Hms2 | by_run Hms]. }
  clear Hms Hms1 Hms2.
  symex_reg HR' (2%bv : reg) as Q2. symex_reg HR' (10%bv : reg) as Q10. symex_reg HR' (8%bv : reg) as Q8.
  symex_reg HR' (9%bv : reg) as Q9. symex_reg HR' (18%bv : reg) as Q18.
  split; [first [exact Q2 | rewrite Q2; f_equal; lia]|]. split; [exact Q10|]. split; [exact Q8|]. split; [exact Q9|]. split; [exact Q18|].
  split.
  { intros rg Hrg. rewrite (Hfr rg) by (eapply reg_in_sub; [| exact Hrg]; reflexivity).
    rewrite (Hfr2 rg) by (eapply reg_in_sub; [| exact Hrg]; reflexivity).
    apply Hfr1. eapply reg_in_sub; [| exact Hrg]; reflexivity. }
  clear HR' Hfr Hfr1 Hfr2 Q2 Q10 Q8 Q9 Q18.
  clear - ZP ZP2 TR AG2 GR2 Hp0 Hp1 Ht0 Ht1 Hs0 Hs1 SEP1 SEP2 SEP3 C64' C72'.
  split.
  { unfold is6_scalars, is6_vals, isl_vals, is6_layout, isl_layout.
    cbn -[Z.add Z.mul Z.shiftr wbytes Z_to_le_bytes word_to_le_bytes zw s6_segs getr].
    repeat match goal with |- _ /\ _ => split end; try exact I.
    all: hcell ltac:(idtac; zcell ZP2). }
  split.
  { unfold is6_arrays, is6_lensA, is6_workA, is6_codesA.
    split; [| split]; hcells ltac:(idtac; apply (cells_zero_of_zblock M2 p 7176); [exact ZP2 | intros i; cbn [is_lens is_work is_codes is0c]; apply arr_get_make0 | lenlia | lia | lia | lia | lia | lia]). }
  split; [hcell ltac:(fail)|]. split; [hcell ltac:(fail)|]. split; [hcell ltac:(fail)|]. split; [hcell ltac:(fail)|].
  split; [hcell ltac:(idtac; exact C64')|]. split; [hcell ltac:(idtac; exact C72')|]. split; [hcell ltac:(fail)|].
  split.
  { intros a w v Ha Hc Hw. cbn in Ha.
    assert (Hw8 : Z.of_nat w <= 8) by (clear - Hw; lia).
    repeat (destruct Ha as [<- | Ha]); [ .. | destruct Ha];
      repeat (apply cell_write_other; [ | first [lia|pg] | first [lenlia|pg] | first [lia|pg] | first [lenlia|pg] | first [lenlia|pg] ]);
      (apply (TR _ _ _ Hc); lia). }
  split.
  { unfold IIF. apply (agree_out_trans _ M M2).
    - apply (agree_out_weaken _ _ M M2 AG2). intros x [Hx|[]]. cbn [in_franges]. right. right. left. lia.
    - hagree. }
  intros x Hx; repeat apply wbytes_grows; apply GR2; exact Hx.
Time Qed.
End FXG.
