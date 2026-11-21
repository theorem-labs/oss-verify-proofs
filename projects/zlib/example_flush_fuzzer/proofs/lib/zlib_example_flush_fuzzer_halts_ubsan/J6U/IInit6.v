(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool FMapPositive.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1 Require Import SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux RomRead STower.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import Prog ZIface InflateState InflateFast InflateArms Inflate
     InflateInv HarnessKit HarnessFacts HarnessSmallFacts.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.FMQ6 Require Import CallocLib6u.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6U Require Import Segs6u.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6S Require Import ISLayout InflMem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require Import IS6 InflRod6 InflCtx6 InflArmLib6.
Local Ltac Zify.zify_post_hook ::= idtac.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.

Definition pc6_ii : Z := 0x1edec.

Definition KI6 : Z := 7.
Definition is0c : inflate_state :=
  mkIS 16180 0 5 0 (-1) 32768 0 0 0 15 0 0 0 (arr_make 0 0) None 0 0 0 0 0 (CDyn 0) (CDyn 0) 0 0 0 0 0 0 0
       (arr_make 320 0) (arr_make 288 0) (arr_make 1444 0) 1 (-1) 0 7%N.
Lemma is0_eq : is0 KI6 = is0c.
Proof using. reflexivity. Qed.
Lemma arr_get_make0 : forall n i, arr_get (arr_make n 0) i = 0.
Proof using. intros n i. unfold arr_get, arr_make. cbn. rewrite FMapPositive.PositiveMap.gempty. destruct (_ && _)%bool; reflexivity. Qed.

Lemma cell_av : forall m a a' (w : nat) v v',
  cell s6u_segs m a w v -> a = a' -> v mod 2 ^ (8 * Z.of_nat w) = v' mod 2 ^ (8 * Z.of_nat w) -> cell s6u_segs m a' w v'.
Proof using. intros m a a' w v v' H <- E. exact (cell_eqm s6u_segs m a w v v' H E). Qed.
Lemma cell_sd_lo : forall m a v, 0 <= a -> a + 8 <= 2 ^ 64 ->
  cell s6u_segs (wbytes m (zw a) (Z_to_le_bytes 8 v)) a 4 v.
Proof using.
  intros m a v Ha Hb. rewrite wbytes_sd_split.
  apply cell_write_other; [apply cell_write_same; cbn; lia | lia | cbn; lia | lia | cbn; lia | cbn; lia].
Qed.
Lemma cell_sd_hi : forall m a v, 0 <= a -> a + 8 <= 2 ^ 64 ->
  cell s6u_segs (wbytes m (zw a) (Z_to_le_bytes 8 v)) (a + 4) 4 (Z.shiftr v 32).
Proof using. intros m a v Ha Hb. rewrite wbytes_sd_split. apply cell_write_same; cbn; lia. Qed.
Definition zblock (m : word -> option byte) (P N : Z) : Prop :=
  forall x : word, P <= bv_unsigned x < P + N -> m x = Some (Z_to_bv 8 0).
Lemma cell_zero_of_zblock : forall m P N a (w : nat),
  zblock m P N -> P <= a -> a + Z.of_nat w <= P + N -> 0 <= P -> P + N < 2 ^ 64 ->
  cell s6u_segs m a w 0.
Proof using.
  intros m P N a w Hz H1 H2 H3 H4. unfold cell.
  apply rdn_pointwise; [apply length_Z_to_le_bytes | rewrite u_zw_small by lia; lia |].
  intros j Hj. rewrite u_zw_small by lia.
  rewrite (Hz (Z_to_bv 64 (a + Z.of_nat j))) by (change (Z_to_bv 64 (a + Z.of_nat j)) with (zw (a + Z.of_nat j)); rewrite u_zw_small by lia; lia).
  f_equal. clear. revert j. induction w as [|w IH]; intros [|j]; cbn; try reflexivity. apply IH.
Qed.
Lemma cells_zero_of_zblock : forall m P N Q st (w : nat) n f,
  zblock m P N -> (forall i, f i = 0) -> Z.of_nat w <= st ->
  P <= Q -> Q + st * n <= P + N -> 0 <= P -> P + N < 2 ^ 64 -> 0 <= n ->
  cells s6u_segs m Q st w n f.
Proof using.
  intros m P N Q st w n f Hz Hf Hw H1 H2 H3 H4 Hn i Hi. rewrite Hf.
  apply (cell_zero_of_zblock m P N); [exact Hz | nia | nia | lia | lia].
Qed.

End FXG.
Ltac pg := match goal with |- ?G => idtac "SIDE-FAIL" G; fail end.
Ltac lenlia := cbn [length Z_to_le_bytes Z.of_nat Pos.of_succ_nat Pos.succ Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul]; lia.
Ltac hcell_other base_tac :=
  apply cell_write_other; [ | first [lia|pg] | first [lenlia|pg] | first [lia|pg] | first [lenlia|pg] | first [lenlia | pg] ].
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.
End FXG.
Ltac zcell ZP :=
  lazymatch type of ZP with zblock ?M ?P ?N =>
  lazymatch goal with |- cell _ _ ?a ?w ?v =>
    apply (cell_av M a a w 0 v); [apply (cell_zero_of_zblock M P N); [exact ZP | lia | lenlia | lia | lia] | reflexivity | cbn; reflexivity]
  end end.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.
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
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.

Lemma land7_zero : forall a, (8 | a) -> Z.land a 7 = 0.
Proof using.
  intros a H. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
  apply Z.mod0_divide. exact H.
Qed.
Lemma div8_of_mod16 : forall a, a mod 16 = 0 -> (8 | a).
Proof using.
  intros a H. apply (Z.divide_trans 8 16 a); [exists 2; reflexivity | apply Z.mod_divide; [lia | exact H]].
Qed.
Lemma div8_of_mod8 : forall a, a mod 8 = 0 -> (8 | a).
Proof using. intros a H. apply Z.mod_divide; [lia | exact H]. Qed.
End FXG.
Ltac div8 :=
  first [ apply div8_of_mod16; assumption
        | apply div8_of_mod8; assumption
        | lazymatch goal with
          | |- (8 | ?a + ?b) => apply Z.divide_add_r; [div8 | div8]
          | |- (8 | ?a - ?b) => apply Z.divide_sub_r; [div8 | div8]
          | |- (8 | ?k) => let q := eval cbv in (k / 8) in exists q; reflexivity
          end ].
Ltac ub_align :=
  lazymatch goal with
  | |- Z.land ?a 7 = 0 => apply land7_zero; div8
  | |- Z.land ?a 7 mod ?m = 0 => rewrite (land7_zero a); [reflexivity | div8]
  | |- ?a mod 2 ^ 3 = 0 => change (a mod 8 = 0); apply Z.mod0_divide; div8
  | |- ?a mod 8 = 0 => apply Z.mod0_divide; div8
  | |- ~ (_ <> 0) => let H := fresh in intros H; apply H; ub_align
  | |- _ <> 0 -> False => let H := fresh in intros H; apply H; ub_align
  end.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.

Definition IIF (t strm p : Z) : franges := [(t - 80, 80); (strm, 112); (p, 7176)].

Lemma ii_segA : forall (R : bvmap 5 word) (M : word -> option byte) (p : Z),
  getr R 10 = zw p -> getr R 9 = zw 7176 -> 0 < p -> p < 2 ^ 63 ->
  exists R1, msteps s6u_segs (mkst R (Z_to_bv 64 pc6_ii) M s6u_rom) (mkst R1 (0x2ac28 : word) M s6u_rom)
    /\ getr R1 1 = zw 0x1ee00 /\ getr R1 10 = zw p /\ getr R1 11 = zw 0 /\ getr R1 12 = zw 7176
    /\ getr R1 8 = zw p /\ getr R1 9 = zw 7176
    /\ (forall rg, reg_in rg [1; 8; 10; 11; 12]%bv = false -> getr R1 rg = getr R rg).
Proof.
  intros R M p G10 G9 Hp0 Hp1.
  symex s6u_segs (CFG [] [] [] [0x2ac28] []) 30%nat [false]
    NoReads [(10, EVar 32%nat); (9, ELit 7176)] [(32%nat, 2 ^ 63)] NoRegions [p] NoVals F0 F0'
    (mkst R (Z_to_bv 64 pc6_ii) M s6u_rom) R1 HR Hfr Hms.
  all: try (symex_auto; lia).
  exists R1. split; [exact Hms|].
  symex_reg HR (1%bv : reg) as A1. symex_reg HR (10%bv : reg) as A10. symex_reg HR (11%bv : reg) as A11. symex_reg HR (12%bv : reg) as A12.
  symex_reg HR (8%bv : reg) as A8. symex_reg HR (9%bv : reg) as A9.
  rewrite ?zw_u in *.
  split; [exact A1|]. split; [exact A10|]. split; [exact A11|]. split; [exact A12|]. split; [exact A8|]. split; [exact A9|].
  intros r Hr; apply Hfr; eapply reg_in_sub; [|exact Hr]; reflexivity.
Qed.
Lemma ii_segB : forall (R : bvmap 5 word) (M : word -> option byte) (t p strm ra v16 v24 v32 : Z),
  getr R 2 = zw (t - 32) -> getr R 10 = zw p -> getr R 18 = zw strm -> getr R 9 = zw 7176 -> getr R 8 = zw p ->
  strm mod 8 = 0 -> p mod 16 = 0 ->
  cell s6u_segs M (strm + 64) 8 0x1a9f4 -> cell s6u_segs M (strm + 72) 8 0x1aa04 ->
  cell s6u_segs M (t + -8) 8 ra -> cell s6u_segs M (t + -16) 8 v16 -> cell s6u_segs M (t + -24) 8 v24 -> cell s6u_segs M (t + -32) 8 v32 ->
  zblock M p 7176 ->
  0 < p -> p + 7176 < 2 ^ 63 -> 80 <= t -> t < 2 ^ 63 -> 0 < strm -> strm + 112 < 2 ^ 63 ->
  0 <= ra < 2 ^ 64 -> ra mod 2 = 0 -> 0 <= v16 < 2 ^ 64 -> 0 <= v24 < 2 ^ 64 -> 0 <= v32 < 2 ^ 64 ->
  sep (t - 80) 80 p 7176 -> sep (t - 80) 80 strm 112 -> sep strm 112 p 7176 ->
  mapped M (t - 80) 80 -> mapped M p 7176 -> mapped M strm 112 ->
  exists R' M',
    msteps s6u_segs (mkst R (0x1ee00 : word) M s6u_rom) (mkst R' (Z_to_bv 64 ra) M' s6u_rom)
    /\ getr R' 2 = zw t /\ getr R' 10 = zw 0 /\ getr R' 8 = zw v16 /\ getr R' 9 = zw v24 /\ getr R' 18 = zw v32
    (* 1.4: the success path calls inflateReset (and memset), which may leave any
       caller-saved register changed (inflateReset sets a5 = 32768); the clause keeps the callee-saved ones only *)
    /\ (forall rg, reg_in rg [1; 2; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 28; 29; 30; 31]%bv = false -> getr R' rg = getr R rg)
    /\ is6_scalars M' p (ISP strm 0) is0c /\ is6_arrays M' p is0c
    /\ cell s6u_segs M' (strm + 16) 8 0 /\ cell s6u_segs M' (strm + 40) 8 0 /\ cell s6u_segs M' (strm + 48) 8 0
    /\ cell s6u_segs M' (strm + 56) 8 p /\ cell s6u_segs M' (strm + 64) 8 0x1a9f4 /\ cell s6u_segs M' (strm + 72) 8 0x1aa04
    /\ cell s6u_segs M' (strm + 96) 8 1
    /\ (forall a (w : nat) v, In a [strm; strm + 8; strm + 24; strm + 32; strm + 80] -> cell s6u_segs M a w v -> (w <= 8)%nat -> cell s6u_segs M' a w v)
    /\ agree_out (IIF t strm p) M M' /\ mem_grows M M'.
Proof using.
  intros R M t p strm ra v16 v24 v32 G2 G10 G18 G9 G8 Hs8 Hp16 C64 C72 Cm8 Cm16 Cm24 Cm32 ZP Hp0 Hp1 Ht0 Ht1 Hs0 Hs1 Hra RA2 Hv16 Hv24 Hv32 SEP1 SEP2 SEP3 MF MP MS.
  unfold mapped, sep in *.
  symex s6u_segs (CFG [] [] [EVar 35%nat] [] []) 160%nat
    [false; false; false; false; false; false; false; false; true; false; true; false; false; false; false; false; false; false; true]
    [RVal (ELit 0x1a9f4); RVal (ELit 0x1aa04); RVal (EVar 35%nat); RVal (EVar 36%nat); RVal (EVar 37%nat); RVal (EVar 38%nat)]
    [(2, EAdd (EVar 32%nat) (ELit (-32))); (10, EVar 33%nat); (18, EVar 34%nat); (8, EVar 33%nat); (9, ELit 7176)]
    [(32%nat, 2 ^ 63); (33%nat, 2 ^ 63); (34%nat, 2 ^ 63); (35%nat, 2 ^ 64); (36%nat, 2 ^ 64); (37%nat, 2 ^ 64); (38%nat, 2 ^ 64)]
    NoRegions [t; p; strm; ra; v16; v24; v32] NoVals F0 F0'
    (mkst R (0x1ee00 : word) M s6u_rom) R' HR' Hfr Hms.
  all: try (lazymatch goal with |- exists _, _ => fail | |- _ => ub_align end).
  all: try (rewrite (land_m2_even ra) by exact RA2; reflexivity).
  all: match goal with |- exists _, _ => idtac | |- ?G => idtac "II-LEFT" G end.
  clear Cm8 Cm16 Cm24 Cm32.
  match type of Hms with msteps _ _ (mkst _ _ ?Mx _) => exists R', Mx end.
  split; [by_run Hms|]. clear Hms.
  symex_reg HR' (2%bv : reg) as Q2. symex_reg HR' (10%bv : reg) as Q10. symex_reg HR' (8%bv : reg) as Q8.
  symex_reg HR' (9%bv : reg) as Q9. symex_reg HR' (18%bv : reg) as Q18.
  split; [first [exact Q2 | rewrite Q2; f_equal; lia]|]. split; [exact Q10|]. split; [exact Q8|]. split; [exact Q9|]. split; [exact Q18|].
  split; [intros rg Hrg; apply Hfr; eapply reg_in_sub; [|exact Hrg]; reflexivity|]. clear HR' Hfr Q2 Q10 Q8 Q9 Q18.
  clear - ZP Hp0 Hp1 Ht0 Ht1 Hs0 Hs1 SEP1 SEP2 SEP3 C64 C72.
  split.
  { unfold is6_scalars, is6_vals, isl_vals, is6_layout, isl_layout.
    cbn -[Z.add Z.mul Z.shiftr wbytes Z_to_le_bytes word_to_le_bytes zw s6u_segs getr].
    repeat match goal with |- _ /\ _ => split end; try exact I.
    all: hcell ltac:(idtac; zcell ZP). }
  split.
  { unfold is6_arrays, is6_lensA, is6_workA, is6_codesA.
    split; [| split]; hcells ltac:(idtac; apply (cells_zero_of_zblock M p 7176); [exact ZP | intros i; cbn [is_lens is_work is_codes is0c]; apply arr_get_make0 | lenlia | lia | lia | lia | lia | lia]). }
  split; [hcell ltac:(fail)|]. split; [hcell ltac:(fail)|]. split; [hcell ltac:(fail)|]. split; [hcell ltac:(fail)|].
  split; [hcell ltac:(idtac; exact C64)|]. split; [hcell ltac:(idtac; exact C72)|]. split; [hcell ltac:(fail)|].
  split.
  { intros a w v Ha Hc Hw. cbn in Ha.
    assert (Hw8 : Z.of_nat w <= 8) by (clear - Hw; lia).
    repeat (destruct Ha as [<- | Ha]); [ .. | destruct Ha];
      repeat (apply cell_write_other; [ | first [lia|pg] | first [lenlia|pg] | first [lia|pg] | first [lenlia|pg] | first [lenlia|pg] ]); exact Hc. }
  split; [unfold IIF; hagree|].
  intros x Hx; repeat apply wbytes_grows; exact Hx.
Time Qed.
Lemma disj1 : forall lo n p m a w, sep lo n p m -> lo <= a -> a + Z.of_nat w <= lo + n -> disj_franges [(p, m)] a (Z.of_nat w).
Proof. intros lo n p m a w H H1 H2 x Hx [Hin|Hin]; [unfold sep in H; simpl in Hin; lia | exact Hin]. Qed.
Lemma reg_get_getr : forall (R : bvmap 5 word) r, bv_eqb r 0%bv = false -> reg_get R r = getr R r.
Proof. intros R r E. unfold getr. rewrite E. reflexivity. Qed.
(* 1.4 (a worker, from a worker's FlLibStmtU fl_ii): s1 holds the state size 7176 at pc6_ii, and 1.4's
   inflateInit_ calls memset(p, 0, s1) and then inflateReset before it returns *)
Lemma ii_run : forall (R : bvmap 5 word) (M : word -> option byte) (t p strm ra v16 v24 v32 : Z),
  getr R 2 = zw (t - 32) -> getr R 10 = zw p -> getr R 18 = zw strm -> getr R 9 = zw 7176 ->
  strm mod 8 = 0 -> p mod 16 = 0 ->
  cell s6u_segs M (strm + 64) 8 0x1a9f4 -> cell s6u_segs M (strm + 72) 8 0x1aa04 ->
  cell s6u_segs M (t + -8) 8 ra -> cell s6u_segs M (t + -16) 8 v16 -> cell s6u_segs M (t + -24) 8 v24 -> cell s6u_segs M (t + -32) 8 v32 ->
  zblock M p 7176 ->
  0 < p -> p + 7176 < 2 ^ 63 -> 80 <= t -> t < 2 ^ 63 -> 0 < strm -> strm + 112 < 2 ^ 63 ->
  0 <= ra < 2 ^ 64 -> ra mod 2 = 0 -> 0 <= v16 < 2 ^ 64 -> 0 <= v24 < 2 ^ 64 -> 0 <= v32 < 2 ^ 64 ->
  sep (t - 80) 80 p 7176 -> sep (t - 80) 80 strm 112 -> sep strm 112 p 7176 ->
  mapped M (t - 80) 80 -> mapped M p 7176 -> mapped M strm 112 ->
  exists R' M',
    msteps s6u_segs (mkst R (Z_to_bv 64 pc6_ii) M s6u_rom) (mkst R' (Z_to_bv 64 ra) M' s6u_rom)
    /\ getr R' 2 = zw t /\ getr R' 10 = zw 0 /\ getr R' 8 = zw v16 /\ getr R' 9 = zw v24 /\ getr R' 18 = zw v32
    (* 1.4: the success path calls inflateReset (and memset), which may leave any
       caller-saved register changed (inflateReset sets a5 = 32768); the clause keeps the callee-saved ones only *)
    /\ (forall rg, reg_in rg [1; 2; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 28; 29; 30; 31]%bv = false -> getr R' rg = getr R rg)
    /\ is6_scalars M' p (ISP strm 0) is0c /\ is6_arrays M' p is0c
    /\ cell s6u_segs M' (strm + 16) 8 0 /\ cell s6u_segs M' (strm + 40) 8 0 /\ cell s6u_segs M' (strm + 48) 8 0
    /\ cell s6u_segs M' (strm + 56) 8 p /\ cell s6u_segs M' (strm + 64) 8 0x1a9f4 /\ cell s6u_segs M' (strm + 72) 8 0x1aa04
    /\ cell s6u_segs M' (strm + 96) 8 1
    (* 1.4: inflateReset writes strm->data_type (strm + 88), so it is not kept *)
    /\ (forall a (w : nat) v, In a [strm; strm + 8; strm + 24; strm + 32; strm + 80] -> cell s6u_segs M a w v -> (w <= 8)%nat -> cell s6u_segs M' a w v)
    /\ agree_out (IIF t strm p) M M' /\ mem_grows M M'.
Proof using.
  intros R M t p strm ra v16 v24 v32 G2 G10 G18 G9 Hs8 Hp16 C64 C72 Cm8 Cm16 Cm24 Cm32 ZP Hp0 Hp1 Ht0 Ht1 Hs0 Hs1 Hra RA2 Hv16 Hv24 Hv32 SEP1 SEP2 SEP3 MF MP MS.
  destruct (ii_segA R M p G10 G9 Hp0 ltac:(lia)) as (R1 & HA & A1 & A10 & A11 & A12 & A8 & A9 & Afr).
  destruct (OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6U.Memset6u_run.memset_run6u_ok M R1 p 0 7176 (zw 0x1ee00)
              ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) MP
              ltac:(apply ret_ok_even; rewrite u_zw_small by lia; reflexivity)
              ltac:(rewrite reg_get_getr by reflexivity; exact A1)
              ltac:(rewrite reg_get_getr by reflexivity; exact A10)
              ltac:(rewrite reg_get_getr by reflexivity; exact A11)
              ltac:(rewrite reg_get_getr by reflexivity; exact A12))
    as (R2 & M1 & Hms & B10 & Hfr & Hfill & Hso & Hgr).
  replace (zw 0x2ac28) with (0x2ac28%bv : word) in Hms by (apply bv_eq; reflexivity).
  replace (zw 0x1ee00) with (0x1ee00%bv : word) in Hms by (apply bv_eq; reflexivity).
  assert (HR2 : forall rg, reg_in rg [1; 2; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 28; 29; 30; 31]%bv = false -> getr R2 rg = getr R rg).
  { intros rg Hrg. rewrite (Hfr rg) by (eapply reg_in_sub; [|exact Hrg]; reflexivity).
    apply Afr. eapply reg_in_sub; [|exact Hrg]; reflexivity. }
  assert (AG : agree_out [(p, 7176)] M M1).
  { intros x Hx. apply Hso. intro H. apply Hx. simpl. left. exact H. }
  assert (AG2 : agree_out (IIF t strm p) M M1).
  { eapply agree_out_weaken; [exact AG|]. intros x Hx. unfold IIF. simpl. simpl in Hx. tauto. }
  assert (HC : forall a (w : nat) v, cell s6u_segs M a w v -> (a + Z.of_nat w <= p \/ p + 7176 <= a) -> 0 <= a -> a + Z.of_nat w <= 2 ^ 64 ->
                 cell s6u_segs M1 a w v).
  { intros a w v Hc H1 H3 H4. eapply cell_agree_out; [exact AG | | lia | lia | exact Hc].
    intros x Hx [Hin|Hin]; simpl in Hin; lia. }
  unfold mapped, sep in *.
  assert (ZP1 : zblock M1 p 7176).
  { intros x Hx. rewrite (Hfill x) by lia. reflexivity. }
  assert (MF1 : forall a n, mapped M a n -> mapped M1 a n).
  { intros a n Hm x Hx. apply Hgr. apply Hm. exact Hx. }
  destruct (ii_segB R2 M1 t p strm ra v16 v24 v32
    ltac:(rewrite (Hfr 2%bv) by reflexivity; rewrite (Afr 2%bv) by reflexivity; exact G2)
    ltac:(rewrite <- (reg_get_getr R2 10%bv) by reflexivity; exact B10)
    ltac:(rewrite (Hfr 18%bv) by reflexivity; rewrite (Afr 18%bv) by reflexivity; exact G18)
    ltac:(rewrite (Hfr 9%bv) by reflexivity; exact A9)
    ltac:(rewrite (Hfr 8%bv) by reflexivity; exact A8)
    Hs8 Hp16
    (HC _ _ _ C64 ltac:(lia) ltac:(lia) ltac:(lia)) (HC _ _ _ C72 ltac:(lia) ltac:(lia) ltac:(lia))
    (HC _ _ _ Cm8 ltac:(lia) ltac:(lia) ltac:(lia)) (HC _ _ _ Cm16 ltac:(lia) ltac:(lia) ltac:(lia))
    (HC _ _ _ Cm24 ltac:(lia) ltac:(lia) ltac:(lia)) (HC _ _ _ Cm32 ltac:(lia) ltac:(lia) ltac:(lia))
    ZP1 Hp0 Hp1 Ht0 Ht1 Hs0 Hs1 Hra RA2 Hv16 Hv24 Hv32 SEP1 SEP2 SEP3
    (MF1 _ _ MF) (MF1 _ _ MP) (MF1 _ _ MS))
    as (R' & M' & HB & B2 & B10' & B8 & B9 & B18 & Bfr & Bsc & Bar & Bc16 & Bc40 & Bc48 & Bc56 & Bc64 & Bc72 & Bc96 & Bin & Bag & Bgr).
  exists R', M'.
  split; [eapply msteps_trans; [exact HA | eapply msteps_trans; [exact Hms | exact HB]]|].
  repeat (split; [assumption|]).
  split; [intros rg Hrg; rewrite (Bfr rg Hrg); apply HR2; exact Hrg|].
  repeat (split; [assumption|]).
  split.
  { intros a w v Ha Hc Hw. apply Bin; [exact Ha | | exact Hw].
    apply (HC _ _ _ Hc); cbn in Ha; destruct Ha as [<-|[<-|[<-|[<-|[<-|[]]]]]]; lia. }
  split; [eapply agree_out_trans; [exact AG2 | exact Bag]|].
  intros x Hx. apply Bgr. apply Hgr. exact Hx.
Time Qed.
End FXG.
