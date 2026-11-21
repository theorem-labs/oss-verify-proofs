(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain Require Import
  PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.E1 Require Import
  SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import ZIface DeflateState DeflateLz.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.D6S Require Import Segs6 DS6.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.PropExec.FPState}.

Record svals : Type := SV { v8 : Z; v9 : Z; v18 : Z; v19 : Z; v20 : Z; v21 : Z; v22 : Z }.

Lemma mod64_neg_small : forall d, - 2 ^ 64 <= d < 0 -> d mod 2 ^ 64 = d + 2 ^ 64.
Proof.
  intros d Hd. replace d with ((d + 2 ^ 64) + (-1) * 2 ^ 64) at 1 by lia.
  rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Lemma lm_limit_eq : forall st ws, 0 <= st < 2 ^ 31 -> 262 <= ws < 2 ^ 31 ->
  Z.land (szwrap 32 ((if st <? (szwrap 32 (st - ws + 262)) mod 2 ^ 64 then 1 else 0) + -1))
         (szwrap 32 (st - ws + 262))
  = (if ws - 262 <? st then st - (ws - 262) else 0).
Proof.
  intros st ws Hst Hws.
  rewrite (szwrap32_small (st - ws + 262)) by lia.
  destruct (Z.ltb_spec (ws - 262) st) as [C|C].
  - rewrite (Z.mod_small (st - ws + 262)) by lia.
    destruct (Z.ltb_spec st (st - ws + 262)); [lia|].
    rewrite szwrap32_small by lia. rewrite Z.land_m1_l. lia.
  - destruct (Z.eq_dec (st - ws + 262) 0) as [E|E].
    + rewrite E. apply Z.land_0_r.
    + rewrite mod64_neg_small by lia.
      destruct (Z.ltb_spec st (st - ws + 262 + 2 ^ 64)); [|lia].
      rewrite szwrap32_small by lia. apply Z.land_0_l.
Qed.

Lemma lm_chain_eq : forall mc pl good, 0 <= mc < 2 ^ 31 ->
  zaluw ALU_SRL mc (Z.lxor (if pl <? good then 1 else 0) 1 * 2 ^ 1)
  = (if good <=? pl then Z.shiftr mc 2 else mc).
Proof.
  intros mc pl good Hmc.
  destruct (Z.ltb_spec pl good); destruct (Z.leb_spec good pl); try lia.
  - change (Z.lxor 1 1 * 2 ^ 1) with 0. rewrite zaluw_srl_small by lia. apply Z.div_1_r.
  - change (Z.lxor 0 1 * 2 ^ 1) with 2. rewrite zaluw_srl_small by lia. rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Lemma mod8_pos_ge : forall a, 0 < a -> a mod 8 = 0 -> 8 <= a.
Proof. intros a Ha Hm. pose proof (Z.div_mod a 8 ltac:(lia)). assert (0 < a / 8) by lia. lia. Qed.

End FXG.
Ltac zw_ifs :=
  repeat match goal with
  | |- context [if ?a <? ?b then _ else _] => destruct (Z.ltb_spec a b)
  | |- context [if ?a <=? ?b then _ else _] => destruct (Z.leb_spec a b)
  | |- context [if ?a =? ?b then _ else _] => destruct (Z.eqb_spec a b)
  end.
Ltac zw_solve := first [ reflexivity | assumption | f_equal; first [lia | zw_ifs; lia] ].
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.PropExec.FPState}.

Section Walk.
Variable mem : word -> option byte.
Variables (S sp : Z) (p : ds_ptrs) (ds : deflate_state) (ra : word).
Local Abbreviation W := (p_window p).
Local Abbreviation PV := (p_prev p).
Local Abbreviation w := (ds_window ds).
Local Abbreviation pv := (ds_prev ds).
Local Abbreviation WL := (arr_len (ds_window ds)).
Local Abbreviation PL := (arr_len (ds_prev ds)).
Local Abbreviation strstart := (ds_strstart ds).
Local Abbreviation strend := (ds_strstart ds + 258).

Hypothesis Hret : ret_ok ra.
Hypothesis Hsc : ds6_scalars mem S p ds.
Hypothesis Hwin : ds6_windowA mem p ds.
Hypothesis Hprev : ds6_prevA mem p ds.
Hypothesis Hwb : forall i, 0 <= i < WL -> 0 <= arr_get w i < 256.
Hypothesis Hpb : forall i, 0 <= i < PL -> 0 <= arr_get pv i < 65536.
Hypothesis HS : 0 <= S /\ S + ds6_SIZE <= 2 ^ 63.
Hypothesis HW : 0 <= W /\ W + WL <= 2 ^ 63.
Hypothesis HPV : 0 <= PV /\ PV + 2 * PL <= 2 ^ 63.
Hypothesis Hsp : 64 <= sp /\ sp <= 2 ^ 63.
Hypothesis Hdisj_spS : sp <= S \/ S + ds6_SIZE <= sp - 64.
Hypothesis Hdisj_spW : sp <= W \/ W + WL <= sp - 64.
Hypothesis Hdisj_spP : sp <= PV \/ PV + 2 * PL <= sp - 64.
Hypothesis Hdisj_SW : S + ds6_SIZE <= W \/ W + WL <= S.
Hypothesis Hdisj_SP : S + ds6_SIZE <= PV \/ PV + 2 * PL <= S.
Hypothesis Hmap_sp : mapped mem (sp - 64) 64.
Hypothesis Hmap_S : mapped mem S ds6_SIZE.
Hypothesis Hstr : 0 <= strstart /\ strstart + 258 < WL /\ WL <= 2 ^ 31.
Hypothesis Hwm : 0 <= ds_w_mask ds < PL /\ PL <= 2 ^ 31.
Hypothesis Hpl : 1 <= ds_prev_length ds <= 258.
Hypothesis Hnice : 0 <= ds_nice_match ds <= 258.
Hypothesis Hlook : 0 <= ds_lookahead ds < 2 ^ 31.
Hypothesis Hgood : 0 <= ds_good_match ds < 2 ^ 31.
Hypothesis Hchain : 0 <= ds_max_chain_length ds < 2 ^ 31.
Hypothesis Hwsz : 262 <= ds_w_size ds < 2 ^ 31.

Definition LF : franges := [(sp - 64, 64); (S + 176, 4)].

Definition LINV (m : word -> option byte) (ms : Z) (sv : svals) : Prop :=
  agree_out LF mem m
  /\ cell s6_segs m (S + 176) 4 ms
  /\ cell s6_segs m (sp - 64 + 56) 8 (v8 sv)
  /\ cell s6_segs m (sp - 64 + 48) 8 (v9 sv)
  /\ cell s6_segs m (sp - 64 + 40) 8 (v18 sv)
  /\ cell s6_segs m (sp - 64 + 32) 8 (v19 sv)
  /\ cell s6_segs m (sp - 64 + 24) 8 (v20 sv)
  /\ cell s6_segs m (sp - 64 + 16) 8 (v21 sv)
  /\ cell s6_segs m (sp - 64 + 8) 8 (v22 sv)
  /\ mapped m (sp - 64) 64 /\ mapped m S ds6_SIZE
  /\ (forall x, mem x <> None -> m x <> None).

Lemma LINV_win : forall m ms sv, LINV m ms sv -> cells s6_segs m W 1 1 WL (wb w).
Proof.
  intros m ms sv (Hag & _).
  assert (H0 : cells s6_segs mem W 1 1 WL (wb w)).
  { intros i Hi. unfold wb. rewrite Z.mod_small by (apply Hwb; lia). exact (Hwin i Hi). }
  refine (cells_agree_out s6_segs LF mem m W 1 1 WL (wb w) Hag _ _ _ _ H0); try lia.
  unfold LF. apply disj_franges_cons; [lia|]. apply disj_franges_cons; [unfold ds6_SIZE in *; lia|].
  apply disj_franges_nil.
Qed.

Lemma LINV_prev : forall m ms sv, LINV m ms sv -> cells s6_segs m PV 2 2 PL (pb pv).
Proof.
  intros m ms sv (Hag & _).
  assert (H0 : cells s6_segs mem PV 2 2 PL (pb pv)).
  { intros i Hi. unfold pb. rewrite Z.mod_small by (apply Hpb; lia). exact (Hprev i Hi). }
  refine (cells_agree_out s6_segs LF mem m PV 2 2 PL (pb pv) Hag _ _ _ _ H0); try lia.
  unfold LF. apply disj_franges_cons; [lia|]. apply disj_franges_cons; [unfold ds6_SIZE in *; lia|].
  apply disj_franges_nil.
Qed.

Lemma LINV_write_ms : forall m ms sv v,
  LINV m ms sv -> LINV (wbytes m (zw (S + 176)) (Z_to_le_bytes 4 v)) v sv.
Proof.
  intros m ms sv v (Hag & Hms & H8 & H9 & H18 & H19 & H20 & H21 & H22 & Hm1 & Hm2 & Hgr). unfold LINV.
  unfold ds6_SIZE in *.
  split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]]]].
  - apply agree_out_wbytes; rewrite ?length_Z_to_le_bytes; try lia; [exact Hag|].
    unfold LF. apply sub_franges_later. apply sub_franges_here; cbn; lia.
  - apply cell_write_same; cbn; lia.
  - apply cell_write_other; rewrite ?length_Z_to_le_bytes; try (cbn; lia). exact H8.
  - apply cell_write_other; rewrite ?length_Z_to_le_bytes; try (cbn; lia). exact H9.
  - apply cell_write_other; rewrite ?length_Z_to_le_bytes; try (cbn; lia). exact H18.
  - apply cell_write_other; rewrite ?length_Z_to_le_bytes; try (cbn; lia). exact H19.
  - apply cell_write_other; rewrite ?length_Z_to_le_bytes; try (cbn; lia). exact H20.
  - apply cell_write_other; rewrite ?length_Z_to_le_bytes; try (cbn; lia). exact H21.
  - apply cell_write_other; rewrite ?length_Z_to_le_bytes; try (cbn; lia). exact H22.
  - apply mapped_wbytes. exact Hm1.
  - apply mapped_wbytes. exact Hm2.
  - intros x Hx. apply wbytes_grows. exact (Hgr x Hx).
Qed.


Let F1 : nat -> Z -> Z := fun f => match f with 0%nat => wb w | _ => pb pv end.
Let HF0 : forall x, 0 <= F1 0%nat x < 256 := fun x => wb_range w x.
Let HF1 : forall x, 0 <= F1 1%nat x < 65536 := fun x => pb_range pv x.

Let wb_eqI : forall i j, arr_get w i = arr_get w j -> wb w i = wb w j := wb_eqI w.
Let wb_neI : forall i j, 0 <= i < WL -> 0 <= j < WL -> arr_get w i <> arr_get w j -> wb w i <> wb w j
  := wb_neI w Hwb.
Let wb_get : forall i, 0 <= i < WL -> wb w i = arr_get w i := wb_get w Hwb.
Let pb_get : forall i, 0 <= i < PL -> pb pv i = arr_get pv i := pb_get pv Hpb.

Definition L_PRO : Z := 0x19da0.
   Definition L_EXIT : Z := 0x19fc0.

Definition lmX : cfg :=
  CFG [(0%nat, 256); (1%nat, 65536)] [] [EVar 1%nat]
      [0x19e34; 0x19e6c; 0x19f84; 0x19fa4; 0x19fc0]
      [AV (EAdd (EVar 36) (EVar 33)) 0 1 0 (EVar 33);
       AV (EAdd (EAdd (EVar 36) (EVar 33)) (EVar 34)) 0 1 0 (EAdd (EVar 33) (EVar 34));
       AV (EAdd (EVar 36) (EVar 37)) 0 1 0 (EVar 37);
       AV (EAdd (EAdd (EVar 36) (EVar 37)) (EVar 46)) 0 1 0 (EAdd (EVar 37) (EVar 46));
       AV (EAdd (EAdd (EVar 36) (EVar 37)) (EVar 34)) 0 1 0 (EAdd (EVar 37) (EVar 34));
       AV (EAdd (EVar 40) (EShl (EAnd (EVar 33) (EVar 41)) 1)) 0 2 1 (EAnd (EVar 33) (EVar 41))].

Local Ltac fr_weak Hfr :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; apply Hfr; eapply reg_in_sub; [| exact Hr]; reflexivity.

Local Ltac via1 Ha H :=
  lazymatch type of H with getr _ ?r = _ => rewrite (Ha r eq_refl); exact H end.
Local Ltac via2 Hb Ha H :=
  lazymatch type of H with getr _ ?r = _ => rewrite (Hb r eq_refl), (Ha r eq_refl); exact H end.
Local Ltac via3 Hc Hb Ha H :=
  lazymatch type of H with getr _ ?r = _ => rewrite (Hc r eq_refl), (Hb r eq_refl), (Ha r eq_refl); exact H end.


Definition m_pro (sv : svals) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (zw (sp + -8)) (Z_to_le_bytes 8 (v8 sv)))
    (zw (sp + -16)) (Z_to_le_bytes 8 (v9 sv)))
    (zw (sp + -24)) (Z_to_le_bytes 8 (v18 sv)))
    (zw (sp + -32)) (Z_to_le_bytes 8 (v19 sv)))
    (zw (sp + -40)) (Z_to_le_bytes 8 (v20 sv)))
    (zw (sp + -48)) (Z_to_le_bytes 8 (v21 sv)))
    (zw (sp + -56)) (Z_to_le_bytes 8 (v22 sv)).

Definition sv_of (regs : bvmap 5 word) : svals :=
  SV (bv_unsigned (getr regs 8)) (bv_unsigned (getr regs 9)) (bv_unsigned (getr regs 18))
     (bv_unsigned (getr regs 19)) (bv_unsigned (getr regs 20)) (bv_unsigned (getr regs 21))
     (bv_unsigned (getr regs 22)).

Definition pro_clob : list reg := [2; 5; 6; 7; 8; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%bv.

Local Ltac prun dirs cur :=
  let R := fresh "R" in let HR := fresh "HR" in let Hfr := fresh "Hfr" in let Hms := fresh "Hms" in
  let A := fresh "A" in
  lazymatch goal with |- context [mkst ?regs _ ?m s6_rom] =>
  symex s6_segs lmX 40%nat dirs
    [RVal (EVar 47); RVal (EVar 36); RVal (EVar 48); RVal (EVar 37); RVal (EVar 44); RVal (EVar 34);
     RVal (EVar 35); RVal (EVar 43); RVal (EVar 41); RVal (EVar 40)]
    [(10, EVar 32); (11, EVar 33); (2, EVar 45)]
    [(32%nat, 2 ^ 63); (33%nat, 2 ^ 31); (34%nat, 259); (35%nat, 2 ^ 31); (36%nat, 2 ^ 63); (37%nat, 2 ^ 31);
     (40%nat, 2 ^ 63); (41%nat, 2 ^ 31); (43%nat, 259); (44%nat, 2 ^ 31); (45%nat, 2 ^ 63 + 1);
     (47%nat, 2 ^ 31); (48%nat, 2 ^ 31)]
    NoRegions
    [S; cur; ds_prev_length ds; ds_max_chain_length ds; W; strstart; 0; 0; PV; ds_w_mask ds; 0; ds_nice_match ds;
     ds_lookahead ds; sp; 0; ds_w_size ds; ds_good_match ds] NoVals F1 F0'
    (mkst regs (0x19da0 : word) m s6_rom) R HR Hfr Hms;
  first
    [ unfold F1; rewrite ?szwrap32_small by lia; rewrite ?Z.mod_small by lia; lia
    | exists R; split; [exact Hms|];
      repeat lazymatch goal with
      | |- getr R ?r = _ /\ _ =>
          split; [ symex_reg HR r as A; unfold F1 in A; rewrite A;
                   rewrite ?lm_limit_eq, ?lm_chain_eq by lia; rewrite ?wb_get by lia; zw_solve |]
      end;
      fr_weak Hfr ]
  end.

Lemma prologue_step : forall regs cur,
  getr regs 10 = zw S -> getr regs 11 = zw cur -> getr regs 2 = zw sp -> 0 <= cur < 2 ^ 31 ->
  let pl := ds_prev_length ds in
  let mc := ds_max_chain_length ds in
  let chain := if ds_good_match ds <=? pl then Z.shiftr mc 2 else mc in
  let nice := if ds_lookahead ds <? ds_nice_match ds then ds_lookahead ds else ds_nice_match ds in
  let limit := if ds_w_size ds - 262 <? strstart then strstart - (ds_w_size ds - 262) else 0 in
  exists R,
    msteps s6_segs (mkst regs (0x19da0 : word) mem s6_rom) (mkst R (0x19e34 : word) (m_pro (sv_of regs)) s6_rom)
    /\ getr R 12 = zw pl /\ getr R 13 = zw (ds_lookahead ds) /\ getr R 14 = zw W
    /\ getr R 15 = zw (W + strstart) /\ getr R 16 = zw nice /\ getr R 17 = zw limit
    /\ getr R 5 = zw (ds_w_mask ds) /\ getr R 6 = zw PV /\ getr R 7 = zw (W + strstart + 258)
    /\ getr R 28 = zw chain /\ getr R 29 = zw (W + 5) /\ getr R 30 = zw 250
    /\ getr R 31 = zw (arr_get w (strstart + pl - 1)) /\ getr R 8 = zw (arr_get w (strstart + pl))
    /\ getr R 2 = zw (sp - 64)
    /\ (forall r : reg, reg_in r pro_clob = false -> getr R r = getr regs r).
Proof.
  intros regs cur H10 H11 H2 Hcur.
  pose proof (fun j (_ : 0 <= j < WL) => wb_range w j) as Hwr.
  assert (Hcw : cells s6_segs mem W 1 1 WL (wb w)).
  { intros i Hi. unfold wb. rewrite Z.mod_small by (apply Hwb; lia). exact (Hwin i Hi). }
  pose proof (ds6_max_chain_length _ _ _ _ Hsc) as F1_. pose proof (ds6_window _ _ _ _ Hsc) as F2_.
  pose proof (ds6_strstart _ _ _ _ Hsc) as F3_. pose proof (ds6_prev_length _ _ _ _ Hsc) as F4_.
  pose proof (ds6_nice_match _ _ _ _ Hsc) as F5_. pose proof (ds6_w_size _ _ _ _ Hsc) as F6_.
  pose proof (ds6_prev _ _ _ _ Hsc) as F7_. pose proof (ds6_w_mask _ _ _ _ Hsc) as F8_.
  pose proof (ds6_good_match _ _ _ _ Hsc) as F9_. pose proof (ds6_lookahead _ _ _ _ Hsc) as F10_.
  pose proof Hmap_sp as Hm1. unfold mapped in Hm1. unfold ds6_SIZE in *.
  cbn zeta.
  destruct (Z_lt_le_dec (ds_nice_match ds) (ds_lookahead ds)) as [C3|C3].
  - prun [true] cur.
  - prun [false] cur.
Qed.



Local Ltac ltb_tf :=
  repeat (cbn [andb orb negb];
          match goal with
          | |- context [?a <? ?b] =>
              first [ rewrite (proj2 (Z.ltb_lt a b)) by lia | rewrite (proj2 (Z.ltb_ge a b)) by lia ]
          | |- context [?a <=? ?b] =>
              first [ rewrite (proj2 (Z.leb_le a b)) by lia | rewrite (proj2 (Z.leb_gt a b)) by lia ]
          | |- context [?a =? ?b] =>
              first [ rewrite (proj2 (Z.eqb_eq a b)) by lia | rewrite (proj2 (Z.eqb_neq a b)) by lia ]
          end);
  cbn [andb orb negb].

Local Ltac sc_close :=
  unfold F1 in *; rewrite ?szwrap64_32_small by lia; rewrite ?szwrap32_small by lia;
  first [ lia
        |
          lazymatch goal with
          | |- exists bs, rdn ?sg ?m (zw (?P + ?i * 2 ^ 1)) 2%nat = Some bs /\ bytes_le_to_Z bs = ?v =>
              match goal with
              | H : cells sg m P 2 2%nat ?len ?f |- _ =>
                  eapply (u16_read_at sg m P len f i _ v H);
                  [ lia | cells_range_auto | change (2 ^ 1) with 2; lia | first [reflexivity | f_equal; lia] ]
              end
          end
        | symex_read_auto | symex_sok_auto | symex_store_auto ].

Local Ltac lrun dirs cur best se se1 :=
  let R := fresh "R" in let HR := fresh "HR" in let Hfr := fresh "Hfr" in let Hms := fresh "Hms" in
  let A := fresh "A" in let B := fresh "B" in
  lazymatch goal with |- context [mkst ?regs _ ?m s6_rom] =>
  symex s6_segs lmX 30%nat dirs NoReads
    [(11, EVar 33); (12, EVar 34); (14, EVar 36); (15, EAdd (EVar 36) (EVar 37));
     (8, EVar 38); (31, EVar 39); (29, EAdd (EVar 36) (ELit 5))]
    [(33%nat, 2 ^ 31); (34%nat, 259); (36%nat, 2 ^ 63); (37%nat, 2 ^ 31); (38%nat, 256); (39%nat, 256)]
    NoRegions
    [0; cur; best; 0; W; strstart; se; se1] NoVals F1 F0'
    (mkst regs (0x19e34 : word) m s6_rom) R HR Hfr Hms;
  first
    [ sc_close
    | exists R; split; [exact Hms|];
      split; [ first [ intros; discriminate
                     | intros _; symex_reg HR (18%bv : reg) as A; symex_reg HR (9%bv : reg) as B;
                       split; [rewrite A; zw_solve | rewrite B; zw_solve] ] |];
      fr_weak Hfr ]
  end.

Lemma body_step : forall regs m ms sv cur best se se1,
  LINV m ms sv ->
  getr regs 11 = zw cur -> getr regs 12 = zw best -> getr regs 14 = zw W ->
  getr regs 15 = zw (W + strstart) -> getr regs 8 = zw se -> getr regs 31 = zw se1 -> getr regs 29 = zw (W + 5) ->
  0 <= cur < strstart -> 1 <= best <= 258 -> 0 <= se < 256 -> 0 <= se1 < 256 ->
  let rej := negb (arr_get w (cur + best) =? se)
             || negb (arr_get w (cur + best - 1) =? se1)
             || negb (arr_get w cur =? arr_get w strstart)
             || negb (arr_get w (cur + 1) =? arr_get w (strstart + 1)) in
  exists R,
    msteps s6_segs (mkst regs (0x19e34 : word) m s6_rom)
          (mkst R (if rej then (0x19fa4 : word) else (0x19e6c : word)) m s6_rom)
    /\ (rej = false -> getr R 18 = zw 0 /\ getr R 9 = zw (W + cur + 5))
    /\ (forall r : reg, reg_in r [9; 18; 19]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m ms sv cur best se se1 HI H11 H12 H14 H15 H8 H31 H29 Hcur Hbest Hse Hse1.
  pose proof (LINV_win m ms sv HI) as Hcw.
  pose proof (fun j (_ : 0 <= j < WL) => wb_range w j) as Hwr.
  unfold ds6_SIZE in *.
  pose proof (wb_get (cur + best) ltac:(lia)) as E1.
  pose proof (wb_get (cur + best + -1) ltac:(lia)) as E2. replace (cur + best + -1) with (cur + best - 1) in E2 at 2 by lia.
  pose proof (wb_get cur ltac:(lia)) as E3. pose proof (wb_get strstart ltac:(lia)) as E4.
  pose proof (wb_get (cur + 1) ltac:(lia)) as E5. pose proof (wb_get (strstart + 1) ltac:(lia)) as E6.
  cbn zeta.
  destruct (Z.eqb_spec (arr_get w (cur + best)) se) as [C1|C1]; cbn [negb orb].
  2: { lrun [true] cur best se se1. }
  destruct (Z.eqb_spec (arr_get w (cur + best - 1)) se1) as [C2|C2]; cbn [negb orb].
  2: { lrun [false; true] cur best se se1. }
  destruct (Z.eqb_spec (arr_get w cur) (arr_get w strstart)) as [C3|C3]; cbn [negb orb].
  2: { lrun [false; false; true] cur best se se1. }
  destruct (Z.eqb_spec (arr_get w (cur + 1)) (arr_get w (strstart + 1))) as [C4|C4]; cbn [negb orb].
  2: { lrun [false; false; false; true] cur best se se1. }
  lrun [false; false; false; false] cur best se se1.
Qed.


Definition lmC : cfg :=
  CFG [(0%nat, 256); (1%nat, 65536)] [] [EVar 1%nat]
      [0x19e34; 0x19e6c; 0x19f84; 0x19fa4; 0x19fc0]
      [AV (EAdd (EAdd (EVar 32) (EVar 33)) (EVar 35)) 0 1 0 (EAdd (EVar 33) (EVar 35));
       AV (EAdd (EAdd (EVar 32) (EVar 34)) (EVar 35)) 0 1 0 (EAdd (EVar 34) (EVar 35))].

Local Ltac norm_idx :=
  repeat match goal with
  | |- context [?x + Zpos ?a + Zpos ?b] =>
      let c := eval vm_compute in (Zpos a + Zpos b) in
      replace (x + Zpos a + Zpos b) with (x + c) by lia
  end.

Local Ltac crun dirs k cur best :=
  let R := fresh "R" in let HR := fresh "HR" in let Hfr := fresh "Hfr" in let Hms := fresh "Hms" in
  let A9 := fresh "A9" in let A18 := fresh "A18" in
  lazymatch goal with |- context [mkst ?regs _ ?m s6_rom] =>
  symex s6_segs lmC 60%nat dirs NoReads
     [(15, EAdd (EVar 32) (EVar 33)); (9, EAdd (EAdd (EVar 32) (EVar 34)) (ELit 5)); (18, EVar 35);
      (7, EAdd (EAdd (EVar 32) (EVar 33)) (ELit 258)); (12, EVar 36); (30, ELit 250)]
     [(32%nat, 2 ^ 63); (33%nat, 2 ^ 31); (34%nat, 2 ^ 31); (35%nat, 2 ^ 31); (36%nat, 259)] NoRegions
     [W; strstart; cur; k; best] NoVals F1 F0' (mkst regs (0x19e6c : word) m s6_rom) R HR Hfr Hms;
  first
    [ sc_close
    | symex_reg HR (9%bv : reg) as A9; symex_reg HR (18%bv : reg) as A18;
      eexists R, _, _, _; split; [reflexivity|]; ltb_tf;
      split; [exact Hms|];
      split; [first [intros; discriminate | intros _; split; [rewrite A18; zw_solve | rewrite A9; zw_solve]] |];
      split; [first [intros; discriminate
                    | intros _; split; [rewrite A9; rewrite ?szwrap32_small by lia; zw_solve | rewrite A18; zw_solve]] |];
      fr_weak Hfr ]
  end.

Lemma cmp_round : forall regs m ms sv k cur best,
  LINV m ms sv ->
  getr regs 15 = zw (W + strstart) -> getr regs 9 = zw (W + cur + 5) -> getr regs 18 = zw k ->
  getr regs 7 = zw (W + strstart + 258) -> getr regs 12 = zw best -> getr regs 30 = zw 250 ->
  0 <= k <= 248 -> 0 <= cur < strstart -> 0 <= best <= 258 ->
  exists R sc' mt' (ok : bool),
    lm_cmpk 8 w (strstart + k + 2) (cur + k + 2) = (sc', mt', ok)
    /\ msteps s6_segs (mkst regs (0x19e6c : word) m s6_rom)
              (mkst R (if ok && (sc' <? strend) then (0x19e6c : word)
                       else if best <? sc' - strstart then (0x19f84 : word) else (0x19fa4 : word)) m s6_rom)
    /\ (ok && (sc' <? strend) = true -> getr R 18 = zw (k + 8) /\ getr R 9 = zw (W + cur + 5))
    /\ (ok && (sc' <? strend) = false -> getr R 9 = zw (sc' - strstart) /\ getr R 18 = zw (sc' - strstart - 258))
    /\ (forall r : reg, reg_in r [9; 18; 19; 20; 21; 22]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m ms sv k cur best HI H15 H9 H18 H7 H12 H30 Hk Hcur Hbest.
  pose proof (LINV_win m ms sv HI) as Hcw.
  pose proof (fun j (_ : 0 <= j < WL) => wb_range w j) as Hwr.
  clear HI pb_get Hsc Hwin Hprev Hpb HS HPV Hsp Hdisj_spS Hdisj_spW Hdisj_spP Hdisj_SW Hdisj_SP
        Hmap_sp Hmap_S Hwm Hpl Hnice Hlook Hgood Hchain Hwsz Hret.
  cbn [lm_cmpk]. norm_idx.
  destruct (Z.eqb_spec (arr_get w (strstart + k + 3)) (arr_get w (cur + k + 3))) as [E1|N1].
  2: { pose proof (wb_neI (strstart + k + 3) (cur + k + 3) ltac:(lia) ltac:(lia) N1) as Nw1.
       destruct (Z_lt_le_dec best (k + 3)); [crun [true; true] k cur best | crun [true; false] k cur best]. }
  pose proof (wb_eqI _ _ E1) as Ew1.
  destruct (Z.eqb_spec (arr_get w (strstart + k + 4)) (arr_get w (cur + k + 4))) as [E2|N2].
  2: { pose proof (wb_neI (strstart + k + 4) (cur + k + 4) ltac:(lia) ltac:(lia) N2) as Nw2.
       destruct (Z_lt_le_dec best (k + 4)); [crun [false; true; true] k cur best | crun [false; true; false] k cur best]. }
  pose proof (wb_eqI _ _ E2) as Ew2.
  destruct (Z.eqb_spec (arr_get w (strstart + k + 5)) (arr_get w (cur + k + 5))) as [E3|N3].
  2: { pose proof (wb_neI (strstart + k + 5) (cur + k + 5) ltac:(lia) ltac:(lia) N3) as Nw3.
       destruct (Z_lt_le_dec best (k + 5)); [crun [false; false; true; true] k cur best | crun [false; false; true; false] k cur best]. }
  pose proof (wb_eqI _ _ E3) as Ew3.
  destruct (Z.eqb_spec (arr_get w (strstart + k + 6)) (arr_get w (cur + k + 6))) as [E4|N4].
  2: { pose proof (wb_neI (strstart + k + 6) (cur + k + 6) ltac:(lia) ltac:(lia) N4) as Nw4.
       destruct (Z_lt_le_dec best (k + 6));
       [crun [false; false; false; true; true] k cur best | crun [false; false; false; true; false] k cur best]. }
  pose proof (wb_eqI _ _ E4) as Ew4.
  destruct (Z.eqb_spec (arr_get w (strstart + k + 7)) (arr_get w (cur + k + 7))) as [E5|N5].
  2: { pose proof (wb_neI (strstart + k + 7) (cur + k + 7) ltac:(lia) ltac:(lia) N5) as Nw5.
       destruct (Z_lt_le_dec best (k + 7));
       [crun [false; false; false; false; true; true] k cur best | crun [false; false; false; false; true; false] k cur best]. }
  pose proof (wb_eqI _ _ E5) as Ew5.
  destruct (Z.eqb_spec (arr_get w (strstart + k + 8)) (arr_get w (cur + k + 8))) as [E6|N6].
  2: { pose proof (wb_neI (strstart + k + 8) (cur + k + 8) ltac:(lia) ltac:(lia) N6) as Nw6.
       destruct (Z_lt_le_dec best (k + 8));
       [crun [false; false; false; false; false; true; true] k cur best
       |crun [false; false; false; false; false; true; false] k cur best]. }
  pose proof (wb_eqI _ _ E6) as Ew6.
  destruct (Z.eqb_spec (arr_get w (strstart + k + 9)) (arr_get w (cur + k + 9))) as [E7|N7].
  2: { pose proof (wb_neI (strstart + k + 9) (cur + k + 9) ltac:(lia) ltac:(lia) N7) as Nw7.
       destruct (Z_lt_le_dec best (k + 9));
       [crun [false; false; false; false; false; false; true; false] k cur best
       |crun [false; false; false; false; false; false; true; true] k cur best]. }
  pose proof (wb_eqI _ _ E7) as Ew7.
  destruct (Z.eqb_spec (arr_get w (strstart + k + 10)) (arr_get w (cur + k + 10))) as [E8|N8].
  2: { pose proof (wb_neI (strstart + k + 10) (cur + k + 10) ltac:(lia) ltac:(lia) N8) as Nw8.
       destruct (Z_lt_le_dec best (k + 10));
       [crun [false; false; false; false; false; false; false; true; true] k cur best
       |crun [false; false; false; false; false; false; false; true; false] k cur best]. }
  pose proof (wb_eqI _ _ E8) as Ew8.
  destruct (Z_lt_le_dec (k + 10) 258) as [L|L].
  - crun [false; false; false; false; false; false; false; false; true] k cur best.
  - destruct (Z_lt_le_dec best (k + 10));
    [crun [false; false; false; false; false; false; false; false; false; true] k cur best
    |crun [false; false; false; false; false; false; false; false; false; false] k cur best].
Qed.


Lemma cmp_loop : forall n regs m ms sv k cur best,
  LINV m ms sv ->
  getr regs 15 = zw (W + strstart) -> getr regs 9 = zw (W + cur + 5) -> getr regs 18 = zw k ->
  getr regs 7 = zw (W + strstart + 258) -> getr regs 12 = zw best -> getr regs 30 = zw 250 ->
  0 <= k <= 248 -> (256 - k) mod 8 = 0 -> 256 - k <= 8 * Z.of_nat n -> 0 <= cur < strstart -> 0 <= best <= 258 ->
  let len := lm_cmp_loop n w (strstart + k + 2) (cur + k + 2) strend - strstart in
  exists R, msteps s6_segs (mkst regs (0x19e6c : word) m s6_rom)
              (mkst R (if best <? len then (0x19f84 : word) else (0x19fa4 : word)) m s6_rom)
    /\ getr R 9 = zw len /\ getr R 18 = zw (len - 258)
    /\ (forall r : reg, reg_in r [9; 18; 19; 20; 21; 22]%bv = false -> getr R r = getr regs r).
Proof.
  induction n as [|n IH]; intros regs m ms sv k cur best HI H15 H9 H18 H7 H12 H30 Hk Hmod Hfuel Hcur Hbest; [lia|].
  destruct (cmp_round regs m ms sv k cur best HI H15 H9 H18 H7 H12 H30 Hk Hcur Hbest)
    as (R1 & sc' & mt' & ok & Hck & Hms1 & HC & HX & Hfr1).
  pose proof (lm_cmpk_bound _ _ _ _ _ _ _ Hck) as Hb. change (Z.of_nat 8) with 8 in Hb.
  cbn zeta. cbn [lm_cmp_loop]. rewrite Hck.
  destruct ok.
  - destruct (lm_cmpk_true _ _ _ _ _ _ Hck) as [-> ->]. change (Z.of_nat 8) with 8 in *.
    destruct (Z_lt_le_dec (strstart + k + 2 + 8) strend) as [L|L].
    +
      rewrite (proj2 (Z.ltb_lt _ _) L) in Hms1, HC, HX |- *. cbn [andb] in Hms1, HC, HX |- *.
      destruct (HC eq_refl) as [A18 A9].
      assert (Hm8 : (256 - k - 8) mod 8 = 0) by (rewrite Zminus_mod, Hmod; reflexivity).
      pose proof (mod8_pos_ge (256 - k - 8) ltac:(lia) Hm8) as Hk8.
      destruct (IH R1 m ms sv (k + 8) cur best HI ltac:(via1 Hfr1 H15) A9 A18 ltac:(via1 Hfr1 H7)
                  ltac:(via1 Hfr1 H12) ltac:(via1 Hfr1 H30) ltac:(lia)
                  ltac:(replace (256 - (k + 8)) with (256 - k - 8) by lia; exact Hm8)
                  ltac:(lia) Hcur Hbest)
        as (R2 & Hms2 & B9 & B18 & Hfr2).
      replace (strstart + (k + 8) + 2) with (strstart + k + 2 + 8) in * by lia.
      replace (cur + (k + 8) + 2) with (cur + k + 2 + 8) in * by lia.
      exists R2. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|].
      split; [exact B9|]. split; [exact B18|]. intros r Hr. rewrite (Hfr2 r Hr). exact (Hfr1 r Hr).
    + rewrite (proj2 (Z.ltb_ge _ _) L) in Hms1, HC, HX |- *. cbn [andb] in Hms1, HC, HX |- *.
      destruct (HX eq_refl) as [A9 A18].
      exists R1. split; [exact Hms1|]. split; [exact A9|]. split; [exact A18 | exact Hfr1].
  - cbn [andb] in Hms1, HX. destruct (HX eq_refl) as [A9 A18].
    exists R1. split; [exact Hms1|]. split; [exact A9|]. split; [exact A18 | exact Hfr1].
Qed.


Local Ltac nbrun dirs cur len nice :=
  let R := fresh "R" in let HR := fresh "HR" in let Hfr := fresh "Hfr" in let Hms := fresh "Hms" in
  let A := fresh "A" in let B := fresh "B" in let C := fresh "C" in
  lazymatch goal with |- context [mkst ?regs _ ?m s6_rom] =>
  symex s6_segs lmX 30%nat dirs [RVal (EApp1 0 (EAdd (EAdd (EVar 37) (EVar 46)) (ELit (-1))))]
    [(10, EVar 32); (11, EVar 33); (9, EVar 46); (16, EVar 43); (18, EAdd (EVar 46) (ELit (-258)));
     (15, EAdd (EVar 36) (EVar 37))]
    [(32%nat, 2 ^ 63); (33%nat, 2 ^ 31); (36%nat, 2 ^ 63); (37%nat, 2 ^ 31); (43%nat, 259); (46%nat, 259)]
    NoRegions
    [S; cur; 0; 0; W; strstart; 0; 0; 0; 0; 0; nice; 0; 0; len] NoVals F1 F0'
    (mkst regs (0x19f84 : word) m s6_rom) R HR Hfr Hms;
  first
    [ sc_close
    | exists R; split; [exact Hms|];
      symex_reg HR (12%bv : reg) as A; split; [rewrite A; zw_solve|];
      split; [ first [ intros; discriminate
                     | intros _; symex_reg HR (31%bv : reg) as B; symex_reg HR (8%bv : reg) as C;
                       unfold F1 in B, C; rewrite wb_get in B by lia; rewrite wb_get in C by lia;
                       split; [rewrite B; zw_solve | rewrite C; zw_solve] ] |];
      split; [ first [ intros; discriminate
                     | intros _; split; apply Hfr; reflexivity ] |];
      fr_weak Hfr ]
  end.

Lemma nb_step : forall regs m ms sv cur len nice,
  LINV m ms sv ->
  getr regs 10 = zw S -> getr regs 11 = zw cur -> getr regs 9 = zw len -> getr regs 16 = zw nice ->
  getr regs 18 = zw (len + -258) -> getr regs 15 = zw (W + strstart) ->
  0 <= cur < 2 ^ 31 -> 2 <= len <= 258 -> 0 <= nice <= 258 ->
  exists R,
    msteps s6_segs (mkst regs (0x19f84 : word) m s6_rom)
          (mkst R (if nice <=? len then (0x19fc0 : word) else (0x19fa4 : word))
                  (wbytes m (zw (S + 176)) (Z_to_le_bytes 4 cur)) s6_rom)
    /\ getr R 12 = zw len
    /\ (nice <=? len = false ->
        getr R 31 = zw (arr_get w (strstart + len - 1)) /\ getr R 8 = zw (arr_get w (strstart + len)))
    /\ (nice <=? len = true -> getr R 31 = getr regs 31 /\ getr R 8 = getr regs 8)
    /\ (forall r : reg, reg_in r [8; 12; 31]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m ms sv cur len nice HI H10 H11 H9 H16 H18 H15 Hcur Hlen Hnice0.
  pose proof (LINV_win m ms sv HI) as Hcw.
  pose proof (fun j (_ : 0 <= j < WL) => wb_range w j) as Hwr.
  destruct HI as (Hag & Hms0 & _ & _ & _ & _ & _ & _ & _ & Hm1 & Hm2 & Hgr). unfold mapped in Hm1, Hm2.
  clear pb_get Hsc Hwin Hprev Hpb HPV Hdisj_spW Hdisj_spP Hdisj_SP Hmap_sp Hmap_S Hwm Hpl Hnice Hlook Hgood Hchain Hwsz Hret.
  unfold ds6_SIZE in *.
  destruct (Z.leb_spec nice len) as [C1|C1].
  - nbrun [true] cur len nice.
  - nbrun [false] cur len nice.
Qed.


Local Ltac nrun dirs cur chain limit Hpv :=
  let R := fresh "R" in let HR := fresh "HR" in let Hfr := fresh "Hfr" in let Hms := fresh "Hms" in
  let A := fresh "A" in let B := fresh "B" in
  lazymatch goal with |- context [mkst ?regs _ ?m s6_rom] =>
  symex s6_segs lmX 20%nat dirs NoReads
      [(11, EVar 33); (5, EVar 41); (6, EVar 40); (17, EVar 42); (28, EVar 35)]
      [(33%nat, 2 ^ 31); (35%nat, 2 ^ 31); (40%nat, 2 ^ 63); (41%nat, 2 ^ 31); (42%nat, 2 ^ 31)] NoRegions
      [0; cur; 0; chain; 0; 0; 0; 0; PV; ds_w_mask ds; limit] NoVals F1 F0'
      (mkst regs (0x19fa4 : word) m s6_rom) R HR Hfr Hms;
  first [ unfold F1 in *; rewrite ?Hpv; rewrite ?szwrap32_small by lia; rewrite ?Z.mod_small by lia; lia
        | sc_close
        | exists R; split; [exact Hms|];
          symex_reg HR (11%bv : reg) as A; unfold F1 in A; rewrite Hpv in A;
          symex_reg HR (28%bv : reg) as B; rewrite ?szwrap32_small in B by lia;
          split; [exact A|]; split; [rewrite B; zw_solve|]; fr_weak Hfr ]
  end.

Lemma next_step : forall regs m ms sv cur chain limit,
  LINV m ms sv ->
  getr regs 11 = zw cur -> getr regs 5 = zw (ds_w_mask ds) -> getr regs 6 = zw PV ->
  getr regs 17 = zw limit -> getr regs 28 = zw chain ->
  0 <= cur < 2 ^ 31 -> 1 <= chain < 2 ^ 31 -> 0 <= limit < 2 ^ 31 ->
  let cur' := arr_get pv (Z.land cur (ds_w_mask ds)) in
  let cont := (limit <? cur') && negb (Z.eqb (chain - 1) 0) in
  exists R, msteps s6_segs (mkst regs (0x19fa4 : word) m s6_rom)
              (mkst R (if cont then (0x19e34 : word) else (0x19fc0 : word)) m s6_rom)
    /\ getr R 11 = zw cur'
    /\ getr R 28 = zw (if limit <? cur' then chain - 1 else chain)
    /\ (forall r : reg, reg_in r [11; 28]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m ms sv cur chain limit HI H11 H5 H6 H17 H28 Hcur Hch Hlim.
  pose proof (LINV_prev m ms sv HI) as Hcp.
  pose proof (fun j (_ : 0 <= j < PL) => pb_range pv j) as Hpr.
  pose proof (land_upper_both cur (ds_w_mask ds) ltac:(lia) ltac:(lia)) as Hl.
  assert (Hidx : 0 <= Z.land cur (ds_w_mask ds) < PL) by lia.
  pose proof (pb_get (Z.land cur (ds_w_mask ds)) Hidx) as Hpv.
  pose proof (pb_range pv (Z.land cur (ds_w_mask ds))) as Hcr.
  clear HI Hsc Hwin Hprev HS HW Hdisj_spS Hdisj_spW Hdisj_spP Hdisj_SW Hdisj_SP Hmap_sp Hmap_S
        Hpl Hnice Hlook Hgood Hchain Hwsz Hret Hstr.
  cbn zeta.
  destruct (Z.ltb_spec limit (arr_get pv (Z.land cur (ds_w_mask ds)))) as [C1|C1]; cbn [andb negb].
  - destruct (Z.eqb_spec (chain - 1) 0) as [C2|C2].
    + nrun [false; false] cur chain limit Hpv.
    + nrun [false; true] cur chain limit Hpv.
  - nrun [true] cur chain limit Hpv.
Qed.


Definition sv_ok (sv : svals) : Prop :=
  0 <= v8 sv < 2 ^ 64 /\ 0 <= v9 sv < 2 ^ 64 /\ 0 <= v18 sv < 2 ^ 64 /\ 0 <= v19 sv < 2 ^ 64
  /\ 0 <= v20 sv < 2 ^ 64 /\ 0 <= v21 sv < 2 ^ 64 /\ 0 <= v22 sv < 2 ^ 64.

Lemma sv_of_ok : forall regs, sv_ok (sv_of regs).
Proof. intros regs. unfold sv_ok, sv_of; cbn [v8 v9 v18 v19 v20 v21 v22]. repeat split; apply u64_range. Qed.

Local Ltac erun dirs best sv H1 :=
  let R := fresh "R" in let HR := fresh "HR" in let Hfr := fresh "Hfr" in let Hms := fresh "Hms" in
  let A := fresh "A" in
  lazymatch goal with |- context [mkst ?regs _ ?m s6_rom] =>
  symex s6_segs lmX 20%nat dirs [RFresh; RFresh; RFresh; RFresh; RFresh; RFresh; RFresh]
    [(12, EVar 34); (13, EVar 44); (2, EVar 45)]
    [(34%nat, 259); (44%nat, 2 ^ 31); (45%nat, 2 ^ 63)]
    NoRegions
    [0; 0; best; 0; 0; 0; 0; 0; 0; 0; 0; 0; ds_lookahead ds; sp - 64]
    [v8 sv; v9 sv; v18 sv; v19 sv; v20 sv; v21 sv; v22 sv] F1 F0'
    (mkst regs (0x19fc0 : word) m s6_rom) R HR Hfr Hms;
  first
  [ sc_close
  | exists R; rewrite H1 in Hms; split; [exact Hms|];
    repeat lazymatch goal with
      | |- getr R ?r = _ /\ _ => split; [ symex_reg HR r as A; rewrite A; zw_solve |]
      end;
    fr_weak Hfr ]
  end.

Lemma exit_step : forall regs m ms sv best,
  LINV m ms sv -> sv_ok sv ->
  getr regs 12 = zw best -> getr regs 13 = zw (ds_lookahead ds) -> getr regs 2 = zw (sp - 64) ->
  getr regs 1 = ra -> 0 <= best <= 258 ->
  exists R, msteps s6_segs (mkst regs (0x19fc0 : word) m s6_rom) (mkst R ra m s6_rom)
    /\ getr R 10 = zw (if best <=? ds_lookahead ds then best else ds_lookahead ds)
    /\ getr R 8 = zw (v8 sv) /\ getr R 9 = zw (v9 sv) /\ getr R 18 = zw (v18 sv)
    /\ getr R 19 = zw (v19 sv) /\ getr R 20 = zw (v20 sv) /\ getr R 21 = zw (v21 sv)
    /\ getr R 22 = zw (v22 sv) /\ getr R 2 = zw sp
    /\ (forall r : reg, reg_in r [2; 8; 9; 10; 12; 18; 19; 20; 21; 22]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m ms sv best HI Hsv H12 H13 H2 H1 Hbest.
  destruct HI as (Hag & Hms0 & C8 & C9 & C18 & C19 & C20 & C21 & C22 & Hm1 & Hm2 & Hgr).
  destruct Hsv as (R8 & R9 & R18 & R19 & R20 & R21 & R22).
  clear pb_get Hsc Hwin Hprev Hpb HS HW HPV Hdisj_spS Hdisj_spW Hdisj_spP Hdisj_SW Hdisj_SP Hmap_sp Hmap_S
        Hwm Hpl Hnice Hgood Hchain Hwsz Hstr.
  destruct (Z_lt_le_dec best (ds_lookahead ds)) as [C1|C1].
  - erun [true] best sv H1.
  - erun [false] best sv H1.
Qed.


Definition trip_clob : list reg := [8; 9; 11; 12; 18; 19; 20; 21; 22; 28; 31]%bv.

Lemma trip : forall regs m ms sv cur best chain se se1 nice limit,
  LINV m ms sv ->
  getr regs 10 = zw S -> getr regs 11 = zw cur -> getr regs 12 = zw best -> getr regs 28 = zw chain ->
  getr regs 14 = zw W -> getr regs 15 = zw (W + strstart) -> getr regs 7 = zw (W + strstart + 258) ->
  getr regs 8 = zw se -> getr regs 31 = zw se1 -> getr regs 6 = zw PV -> getr regs 5 = zw (ds_w_mask ds) ->
  getr regs 17 = zw limit -> getr regs 16 = zw nice -> getr regs 29 = zw (W + 5) -> getr regs 30 = zw 250 ->
  0 <= cur < strstart -> 1 <= best <= 258 -> 1 <= chain < 2 ^ 31 -> 0 <= se < 256 -> 0 <= se1 < 256 ->
  0 <= nice <= 258 -> 0 <= limit < 2 ^ 31 ->
  let '(s', best', se1', se', cur', chain', cont) :=
    longest_match_body (set_match_start ds ms) cur chain best nice limit se1 se in
  exists R m' ms',
    msteps s6_segs (mkst regs (0x19e34 : word) m s6_rom)
          (mkst R (if cont then (0x19e34 : word) else (0x19fc0 : word)) m' s6_rom)
    /\ LINV m' ms' sv /\ s' = set_match_start ds ms'
    /\ getr R 11 = zw cur' /\ getr R 12 = zw best' /\ getr R 28 = zw chain'
    /\ getr R 8 = zw se' /\ getr R 31 = zw se1'
    /\ 1 <= best' <= 258 /\ 0 <= se' < 256 /\ 0 <= se1' < 256 /\ 0 <= cur' < 2 ^ 31
    /\ (cont = true -> 1 <= chain' < chain)
    /\ (forall r : reg, reg_in r trip_clob = false -> getr R r = getr regs r).
Proof.
  intros regs m ms sv cur best chain se se1 nice limit HI H10 H11 H12 H28 H14 H15 H7 H8 H31 H6 H5 H17 H16 H29 H30
         Hcur Hbest Hch Hse Hse1 Hnice0 Hlim.
  pose proof (body_step regs m ms sv cur best se se1 HI H11 H12 H14 H15 H8 H31 H29 Hcur Hbest Hse Hse1) as HB.
  cbn zeta in HB. destruct HB as (R1 & Hms1 & HC & Hfr1).
  unfold longest_match_body, MAX_MATCH. cbv zeta. rewrite ?sms_window, ?sms_strstart.
  pose proof (land_upper_both cur (ds_w_mask ds) ltac:(lia) ltac:(lia)) as Hl.
  assert (Hwm' : 0 <= Z.land cur (ds_w_mask ds) < PL) by lia.
  pose proof (Hpb _ Hwm') as Hcur'.
  destruct (negb (arr_get w (cur + best) =? se) || negb (arr_get w (cur + best - 1) =? se1)
            || negb (arr_get w cur =? arr_get w strstart)
            || negb (arr_get w (cur + 1) =? arr_get w (strstart + 1))) eqn:Hrej.
  -
    cbv beta iota zeta. rewrite ?sms_prev, ?sms_w_mask.
    destruct (next_step R1 m ms sv cur chain limit HI
                ltac:(via1 Hfr1 H11) ltac:(via1 Hfr1 H5) ltac:(via1 Hfr1 H6) ltac:(via1 Hfr1 H17)
                ltac:(via1 Hfr1 H28) ltac:(lia) Hch Hlim) as (R2 & Hms2 & A11 & A28 & Hfr2).
    rewrite wrap32_id by lia.
    destruct (Z.ltb_spec limit (arr_get pv (Z.land cur (ds_w_mask ds)))) as [Cl|Cl];
      [destruct (Z.eqb_spec (chain - 1) 0) as [Cz|Cz]|]; cbn [andb negb] in Hms2 |- *; cbv beta iota zeta.
    all: exists R2, m, ms.
    all: split; [eapply msteps_trans; [exact Hms1 | exact Hms2] |].
    all: split; [exact HI|]. all: split; [reflexivity|].
    all: split; [exact A11|]. all: split; [via2 Hfr2 Hfr1 H12|]. all: split; [exact A28|].
    all: split; [via2 Hfr2 Hfr1 H8|]. all: split; [via2 Hfr2 Hfr1 H31|].
    all: split; [lia|]. all: split; [lia|]. all: split; [lia|]. all: split; [lia|].
    all: split; [first [discriminate | intros _; lia] |].
    all: intros r Hr; rewrite (Hfr2 r) by (eapply reg_in_sub; [| exact Hr]; reflexivity);
         rewrite (Hfr1 r) by (eapply reg_in_sub; [| exact Hr]; reflexivity); reflexivity.
  -
    destruct (HC eq_refl) as [A18 A9].
    destruct (cmp_loop 33 R1 m ms sv 0 cur best HI
                ltac:(via1 Hfr1 H15) ltac:(rewrite A9; f_equal; lia) A18 ltac:(via1 Hfr1 H7)
                ltac:(via1 Hfr1 H12) ltac:(via1 Hfr1 H30)
                ltac:(lia) ltac:(reflexivity) ltac:(change (Z.of_nat 33) with 33; lia) Hcur ltac:(lia))
      as (R2 & Hms2 & B9 & B18 & Hfr2).
    pose proof (lm_cmp_loop_bound 33 w (strstart + 0 + 2) (cur + 0 + 2) (strstart + 258) ltac:(lia)
                  ltac:(replace (strstart + 258 - (strstart + 0 + 2)) with 256 by lia; reflexivity)) as Hsc'.
    replace (strstart + 2) with (strstart + 0 + 2) by lia. replace (cur + 2) with (cur + 0 + 2) by lia.
    set (scan' := lm_cmp_loop 33 w (strstart + 0 + 2) (cur + 0 + 2) (strstart + 258)) in *.
    replace (258 - (strstart + 258 - scan')) with (scan' - strstart) by lia.
    cbn zeta in Hms2, B9, B18.
    assert (Hfr21 : forall r : reg, reg_in r [9; 18; 19; 20; 21; 22]%bv = false -> getr R2 r = getr regs r).
    { intros r Hr. rewrite (Hfr2 r) by (eapply reg_in_sub; [| exact Hr]; reflexivity).
      apply Hfr1. eapply reg_in_sub; [| exact Hr]; reflexivity. }
    destruct (Z.ltb_spec best (scan' - strstart)) as [Cb|Cb]; cbn [andb negb] in Hms2 |- *.
    +
      rewrite ?set_ms_twice.
      destruct (nb_step R2 m ms sv cur (scan' - strstart) nice HI
                  ltac:(via1 Hfr21 H10) ltac:(via1 Hfr21 H11) B9 ltac:(via1 Hfr21 H16)
                  ltac:(rewrite B18; f_equal; lia) ltac:(via1 Hfr21 H15) ltac:(lia) ltac:(lia) Hnice0)
        as (R3 & Hms3 & C12 & CE & CK & Hfr3).
      set (m2 := wbytes m (zw (S + 176)) (Z_to_le_bytes 4 cur)) in *.
      pose proof (LINV_write_ms m ms sv cur HI) as HI2. fold m2 in HI2.
      assert (Hfr31 : forall r : reg, reg_in r [8; 9; 12; 18; 19; 20; 21; 22; 31]%bv = false -> getr R3 r = getr regs r).
      { intros r Hr. rewrite (Hfr3 r) by (eapply reg_in_sub; [| exact Hr]; reflexivity).
        apply Hfr21. eapply reg_in_sub; [| exact Hr]; reflexivity. }
      pose proof (Hwb (strstart + (scan' - strstart)) ltac:(lia)) as Hr1.
      pose proof (Hwb (strstart + (scan' - strstart) - 1) ltac:(lia)) as Hr2.
      destruct (Z.leb_spec nice (scan' - strstart)) as [Cn|Cn]; cbn [andb negb] in Hms3, CE |- *.
      *
        cbv beta iota zeta.
        exists R3, m2, cur.
        split; [eapply msteps_trans; [exact Hms1 | eapply msteps_trans; [exact Hms2 | exact Hms3]] |].
        split; [exact HI2|]. split; [reflexivity|].
        destruct (CK eq_refl) as [K31 K8].
        split; [via1 Hfr31 H11|]. split; [exact C12|]. split; [via1 Hfr31 H28|].
        split; [rewrite K8; via1 Hfr21 H8|]. split; [rewrite K31; via1 Hfr21 H31|].
        split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [discriminate|].
        intros r Hr; apply Hfr31; eapply reg_in_sub; [| exact Hr]; reflexivity.
      *
        destruct (CE eq_refl) as [C31 C8].
        cbv beta iota zeta. rewrite ?sms_prev, ?sms_w_mask.
        destruct (next_step R3 m2 cur sv cur chain limit HI2
                    ltac:(via1 Hfr31 H11) ltac:(via1 Hfr31 H5) ltac:(via1 Hfr31 H6) ltac:(via1 Hfr31 H17)
                    ltac:(via1 Hfr31 H28) ltac:(lia) Hch Hlim) as (R4 & Hms4 & D11 & D28 & Hfr4).
        rewrite wrap32_id by lia.
        destruct (Z.ltb_spec limit (arr_get pv (Z.land cur (ds_w_mask ds)))) as [Cl|Cl];
          [destruct (Z.eqb_spec (chain - 1) 0) as [Cz|Cz]|]; cbn [andb negb] in Hms4 |- *; cbv beta iota zeta.
        all: exists R4, m2, cur.
        all: split; [eapply msteps_trans; [exact Hms1 | eapply msteps_trans; [exact Hms2 | eapply msteps_trans; [exact Hms3 | exact Hms4]]] |].
        all: split; [exact HI2|]. all: split; [reflexivity|].
        all: split; [exact D11|]. all: split; [via1 Hfr4 C12|]. all: split; [exact D28|].
        all: split; [via1 Hfr4 C8|]. all: split; [via1 Hfr4 C31|].
        all: split; [lia|]. all: split; [lia|]. all: split; [lia|]. all: split; [lia|].
        all: split; [first [discriminate | intros _; lia] |].
        all: intros r Hr; rewrite (Hfr4 r) by (eapply reg_in_sub; [| exact Hr]; reflexivity);
             apply Hfr31; eapply reg_in_sub; [| exact Hr]; reflexivity.
    +
      cbv beta iota zeta. rewrite ?sms_prev, ?sms_w_mask.
      destruct (next_step R2 m ms sv cur chain limit HI
                  ltac:(via1 Hfr21 H11) ltac:(via1 Hfr21 H5) ltac:(via1 Hfr21 H6) ltac:(via1 Hfr21 H17)
                  ltac:(via1 Hfr21 H28) ltac:(lia) Hch Hlim) as (R4 & Hms4 & D11 & D28 & Hfr4).
      rewrite wrap32_id by lia.
      destruct (Z.ltb_spec limit (arr_get pv (Z.land cur (ds_w_mask ds)))) as [Cl|Cl];
        [destruct (Z.eqb_spec (chain - 1) 0) as [Cz|Cz]|]; cbn [andb negb] in Hms4 |- *; cbv beta iota zeta.
      all: exists R4, m, ms.
      all: split; [eapply msteps_trans; [exact Hms1 | eapply msteps_trans; [exact Hms2 | exact Hms4]] |].
      all: split; [exact HI|]. all: split; [reflexivity|].
      all: split; [exact D11|]. all: split; [via2 Hfr4 Hfr21 H12|]. all: split; [exact D28|].
      all: split; [via2 Hfr4 Hfr21 H8|]. all: split; [via2 Hfr4 Hfr21 H31|].
      all: split; [lia|]. all: split; [lia|]. all: split; [lia|]. all: split; [lia|].
      all: split; [first [discriminate | intros _; lia] |].
      all: intros r Hr; rewrite (Hfr4 r) by (eapply reg_in_sub; [| exact Hr]; reflexivity);
           apply Hfr21; eapply reg_in_sub; [| exact Hr]; reflexivity.
Qed.



Lemma chain_loop : forall n regs m ms sv cur best chain se se1 nice limit,
  LINV m ms sv ->
  getr regs 10 = zw S -> getr regs 11 = zw cur -> getr regs 12 = zw best -> getr regs 28 = zw chain ->
  getr regs 14 = zw W -> getr regs 15 = zw (W + strstart) -> getr regs 7 = zw (W + strstart + 258) ->
  getr regs 8 = zw se -> getr regs 31 = zw se1 -> getr regs 6 = zw PV -> getr regs 5 = zw (ds_w_mask ds) ->
  getr regs 17 = zw limit -> getr regs 16 = zw nice -> getr regs 29 = zw (W + 5) -> getr regs 30 = zw 250 ->
  1 <= best <= 258 -> 1 <= chain < 2 ^ 31 -> 0 <= se < 256 -> 0 <= se1 < 256 ->
  0 <= nice <= 258 -> 0 <= limit < 2 ^ 31 -> chain <= Z.of_nat n ->
  Forall (fun c => 0 <= c < strstart) (lm_curs n (set_match_start ds ms) cur chain best nice limit se1 se) ->
  let '(s', best') := longest_match_loop n (set_match_start ds ms) cur chain best nice limit se1 se in
  exists R m' ms',
    msteps s6_segs (mkst regs (0x19e34 : word) m s6_rom) (mkst R (0x19fc0 : word) m' s6_rom)
    /\ LINV m' ms' sv /\ s' = set_match_start ds ms'
    /\ getr R 12 = zw best' /\ 1 <= best' <= 258
    /\ (forall r : reg, reg_in r trip_clob = false -> getr R r = getr regs r).
Proof.
  induction n as [|n IH]; intros regs m ms sv cur best chain se se1 nice limit HI H10 H11 H12 H28 H14 H15 H7 H8 H31
    H6 H5 H17 H16 H29 H30 Hbest Hch Hse Hse1 Hnice0 Hlim Hfuel Hcurs; [lia|].
  cbn [lm_curs] in Hcurs. pose proof (Forall_inv Hcurs) as Hcur. cbn beta in Hcur.
  pose proof (Forall_inv_tail Hcurs) as Hcurs'. clear Hcurs.
  pose proof (trip regs m ms sv cur best chain se se1 nice limit HI H10 H11 H12 H28 H14 H15 H7 H8 H31
                H6 H5 H17 H16 H29 H30 Hcur Hbest Hch Hse Hse1 Hnice0 Hlim) as HT.
  cbn [longest_match_loop]. revert HT Hcurs'.
  destruct (longest_match_body (set_match_start ds ms) cur chain best nice limit se1 se)
    as [[[[[[s1 b1] se1'] se'] cur'] ch'] cont].
  intros HT Hcurs'.
  destruct HT as (R1 & m1 & ms1 & Hms1 & HI1 & -> & A11 & A12 & A28 & A8 & A31 & Hb1 & Hse' & Hse1' & Hcur'0 & Hch' & Hfr1).
  destruct cont.
  - specialize (Hch' eq_refl).
    specialize (IH R1 m1 ms1 sv cur' b1 ch' se' se1' nice limit HI1
                  ltac:(via1 Hfr1 H10) A11 A12 A28 ltac:(via1 Hfr1 H14) ltac:(via1 Hfr1 H15) ltac:(via1 Hfr1 H7)
                  A8 A31 ltac:(via1 Hfr1 H6) ltac:(via1 Hfr1 H5) ltac:(via1 Hfr1 H17) ltac:(via1 Hfr1 H16)
                  ltac:(via1 Hfr1 H29) ltac:(via1 Hfr1 H30)
                  Hb1 ltac:(lia) Hse' Hse1' Hnice0 Hlim ltac:(lia) Hcurs').
    destruct (longest_match_loop n (set_match_start ds ms1) cur' ch' b1 nice limit se1' se') as [s' best'].
    destruct IH as (R2 & m2 & ms2 & Hms2 & HI2 & -> & B12 & Hb2 & Hfr2).
    exists R2, m2, ms2. split; [eapply msteps_trans; [exact Hms1 | exact Hms2] |].
    split; [exact HI2|]. split; [reflexivity|]. split; [exact B12|]. split; [exact Hb2|].
    intros r Hr. rewrite (Hfr2 r Hr). exact (Hfr1 r Hr).
  - exists R1, m1, ms1. split; [exact Hms1|]. split; [exact HI1|]. split; [reflexivity|].
    split; [exact A12|]. split; [exact Hb1|]. exact Hfr1.
Qed.


Lemma LINV_init : forall sv, LINV (m_pro sv) (ds_match_start ds) sv.
Proof.
  intros sv. unfold LINV, m_pro, ds6_SIZE in *.
  replace (sp - 64 + 56) with (sp + -8) by lia. replace (sp - 64 + 48) with (sp + -16) by lia.
  replace (sp - 64 + 40) with (sp + -24) by lia. replace (sp - 64 + 32) with (sp + -32) by lia.
  replace (sp - 64 + 24) with (sp + -40) by lia. replace (sp - 64 + 16) with (sp + -48) by lia.
  replace (sp - 64 + 8) with (sp + -56) by lia.
  split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]]]].
  - do 7 (apply agree_out_wbytes; rewrite ?length_Z_to_le_bytes; try lia; [| unfold LF; apply sub_franges_here; cbn; lia]).
    apply agree_out_refl.
  - do 7 (apply cell_write_other; rewrite ?length_Z_to_le_bytes; try (cbn; lia)).
    exact (ds6_match_start _ _ _ _ Hsc).
  - do 6 (apply cell_write_other; rewrite ?length_Z_to_le_bytes; try (cbn; lia)). apply cell_write_same; lia.
  - do 5 (apply cell_write_other; rewrite ?length_Z_to_le_bytes; try (cbn; lia)). apply cell_write_same; lia.
  - do 4 (apply cell_write_other; rewrite ?length_Z_to_le_bytes; try (cbn; lia)). apply cell_write_same; lia.
  - do 3 (apply cell_write_other; rewrite ?length_Z_to_le_bytes; try (cbn; lia)). apply cell_write_same; lia.
  - do 2 (apply cell_write_other; rewrite ?length_Z_to_le_bytes; try (cbn; lia)). apply cell_write_same; lia.
  - do 1 (apply cell_write_other; rewrite ?length_Z_to_le_bytes; try (cbn; lia)). apply cell_write_same; lia.
  - apply cell_write_same; lia.
  - do 7 apply mapped_wbytes. exact Hmap_sp.
  - do 7 apply mapped_wbytes. exact Hmap_S.
  - intros x Hx. do 7 apply wbytes_grows. exact Hx.
Qed.

Lemma ds6_final : forall m' ms', agree_out LF mem m' -> cell s6_segs m' (S + 176) 4 ms' ->
  ds6_scalars m' S p (set_match_start ds ms').
Proof.
  intros m' ms' Hag Hc. unfold ds6_scalars, ds6_SIZE in *.
  refine (fields_agree_field s6_segs LF mem m' S ds6_layout (ds6_vals ds p S) ds6_SIZE 28 176 4%nat ms'
           Hsc eq_refl ltac:(vm_compute; reflexivity) ds6_layout_within Hag _ Hc ltac:(lia)
           ltac:(unfold ds6_SIZE; lia)).
  unfold LF, ds6_SIZE. cbn [in_franges]. intros x Hx HxS. lia.
Qed.


Definition lmatch_clob : list reg :=
  [2; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 28; 29; 30; 31]%bv.

Theorem longest_match_correct : forall regs cur,
  reg_get regs 1 = ra -> reg_get regs 2 = zw sp -> reg_get regs 10 = zw S -> reg_get regs 11 = zw cur ->
  1 <= (if ds_good_match ds <=? ds_prev_length ds
        then Z.shiftr (ds_max_chain_length ds) 2 else ds_max_chain_length ds) ->
  0 <= cur < 2 ^ 31 ->
  Forall (fun c => 0 <= c < strstart) (lm_visited ds cur) ->
  exists regs' mem',
    msteps s6_segs (mkst regs (0x19da0 : word) mem s6_rom) (mkst regs' ra mem' s6_rom)
    /\ reg_get regs' 10 = zw (snd (longest_match ds cur))
    /\ reg_get regs' 2 = zw sp
    /\ reg_get regs' 8 = reg_get regs 8 /\ reg_get regs' 9 = reg_get regs 9
    /\ reg_get regs' 18 = reg_get regs 18 /\ reg_get regs' 19 = reg_get regs 19
    /\ reg_get regs' 20 = reg_get regs 20 /\ reg_get regs' 21 = reg_get regs 21
    /\ reg_get regs' 22 = reg_get regs 22
    /\ (forall r : reg, reg_in r lmatch_clob = false -> getr regs' r = getr regs r)
    /\ ds6_scalars mem' S p (fst (longest_match ds cur))
    /\ agree_out [(sp - 64, 64); (S + 176, 4)] mem mem'
    /\ (forall x, mem x <> None -> mem' x <> None).
Proof.
  intros regs cur H1 H2 H10 H11 Hch1 Hcur Hvis.
  change (getr regs 1 = ra) in H1. change (getr regs 2 = zw sp) in H2.
  change (getr regs 10 = zw S) in H10. change (getr regs 11 = zw cur) in H11.
  destruct (prologue_step regs cur H10 H11 H2 Hcur)
    as (R1 & Hms1 & A12 & A13 & A14 & A15 & A16 & A17 & A5 & A6 & A7 & A28 & A29 & A30 & A31 & A8 & A2 & Hfr1).
  pose proof (LINV_init (sv_of regs)) as HI1.
  unfold lm_visited, MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH, NIL in Hvis. cbv zeta in Hvis.
  replace (ds_w_size ds - (258 + 3 + 1)) with (ds_w_size ds - 262) in Hvis by lia.
  unfold longest_match, MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH, NIL. cbv zeta.
  replace (ds_w_size ds - (258 + 3 + 1)) with (ds_w_size ds - 262) by lia.
  set (chain := if ds_good_match ds <=? ds_prev_length ds
                then Z.shiftr (ds_max_chain_length ds) 2 else ds_max_chain_length ds) in *.
  set (nice := if ds_lookahead ds <? ds_nice_match ds then ds_lookahead ds else ds_nice_match ds) in *.
  set (limit := if ds_w_size ds - 262 <? strstart then strstart - (ds_w_size ds - 262) else 0) in *.
  assert (Hchain' : 1 <= chain < 2 ^ 31).
  { subst chain. destruct (ds_good_match ds <=? ds_prev_length ds); [|lia].
    rewrite Z.shiftr_div_pow2 in * by lia. split; [exact Hch1|].
    apply Z.div_lt_upper_bound; lia. }
  assert (Hnice' : 0 <= nice <= 258) by (subst nice; destruct (Z.ltb_spec (ds_lookahead ds) (ds_nice_match ds)); lia).
  assert (Hlim' : 0 <= limit < 2 ^ 31) by (subst limit; destruct (Z.ltb_spec (ds_w_size ds - 262) strstart); lia).
  pose proof (Hwb (strstart + ds_prev_length ds) ltac:(lia)) as Hse.
  pose proof (Hwb (strstart + ds_prev_length ds - 1) ltac:(lia)) as Hse1.
  pose proof (chain_loop (Z.to_nat chain) R1 _ (ds_match_start ds) _ cur (ds_prev_length ds) chain
                (arr_get w (strstart + ds_prev_length ds)) (arr_get w (strstart + ds_prev_length ds - 1))
                nice limit HI1
                ltac:(via1 Hfr1 H10) ltac:(via1 Hfr1 H11) A12 A28 A14 A15 A7 A8 A31 A6 A5 A17 A16 A29 A30
                Hpl Hchain' Hse Hse1 Hnice' Hlim' ltac:(lia)) as HL.
  rewrite (set_ms_self ds) in HL. specialize (HL Hvis).
  destruct (longest_match_loop (Z.to_nat chain) ds cur chain (ds_prev_length ds) nice limit
              (arr_get w (strstart + ds_prev_length ds - 1)) (arr_get w (strstart + ds_prev_length ds)))
    as [s' best'].
  destruct HL as (R2 & m2 & ms2 & Hms2 & HI2 & Es' & B12 & Hb2 & Hfr2).
  destruct (exit_step R2 m2 ms2 (sv_of regs) best' HI2 (sv_of_ok regs) B12 ltac:(via1 Hfr2 A13)
              ltac:(via1 Hfr2 A2) ltac:(via2 Hfr2 Hfr1 H1) ltac:(lia))
    as (R3 & Hms3 & C10 & C8 & C9 & C18 & C19 & C20 & C21 & C22 & C2 & Hfr3).
  exists R3, m2. rewrite Es'. rewrite !sms_lookahead.
  split; [eapply msteps_trans; [exact Hms1 | eapply msteps_trans; [exact Hms2 | exact Hms3]] |].
  split.
  { change (reg_get R3 10) with (getr R3 10). rewrite C10.
    destruct (best' <=? ds_lookahead ds); reflexivity. }
  split; [exact C2|].
  unfold sv_of in C8, C9, C18, C19, C20, C21, C22; cbn [v8 v9 v18 v19 v20 v21 v22] in C8, C9, C18, C19, C20, C21, C22.
  rewrite zw_u in C8, C9, C18, C19, C20, C21, C22.
  split; [exact C8|]. split; [exact C9|]. split; [exact C18|]. split; [exact C19|].
  split; [exact C20|]. split; [exact C21|]. split; [exact C22|].
  split.
  { intros r Hr. rewrite (Hfr3 r) by (eapply reg_in_sub; [| exact Hr]; reflexivity).
    rewrite (Hfr2 r) by (eapply reg_in_sub; [| exact Hr]; reflexivity).
    apply Hfr1. eapply reg_in_sub; [| exact Hr]; reflexivity. }
  destruct HI2 as (Hag2 & Hcms2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hgr2).
  split.
  { replace (fst (if best' <=? ds_lookahead ds then (set_match_start ds ms2, best')
                  else (set_match_start ds ms2, ds_lookahead ds))) with (set_match_start ds ms2)
      by (destruct (best' <=? ds_lookahead ds); reflexivity).
    apply ds6_final; assumption. }
  split; [exact Hag2 | exact Hgr2].
Qed.

End Walk.

End FXG.
