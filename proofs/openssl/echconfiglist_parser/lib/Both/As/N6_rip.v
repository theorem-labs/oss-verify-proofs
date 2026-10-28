(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge TacX SFModel.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import InNth.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst N6_tac N6_mem_is_zero.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import N8Store.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.   (* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition memtoshadow_entry := 0x1c0bdc%Z.
Definition rip_entry := 0x1c1068%Z.
Definition RIP_STACK := 80%Z.

(* [comment removed for export] *)
Definition in_mem (p : Z) : Prop := (0 <= p < ASHADOW_BASE) \/ (AHI_LO <= p < AAPP_HI).
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma ACONST_layout : forall m, ACONST m ->
  rw_cells asegs m 6191128 [C8 (Z_to_bv 64 6990072)] /\ rw_cells asegs m 6990072 [C8 (Z_to_bv 64 2147450880)] /\
  rw_cells asegs m 6191136 [C8 (Z_to_bv 64 6993384)] /\ rw_cells asegs m 6191144 [C8 (Z_to_bv 64 6993392)] /\
  rw_cells asegs m 6191152 [C8 (Z_to_bv 64 6993376)] /\
  rw_cells asegs m 6993376 [C8 (Z_to_bv 64 (2^47 - 1)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].
Proof.
  intros m AC.
  change 6191128 with AGOT_SHBASE. change 6990072 with ASHBASE_CELL. change 2147450880 with ASHADOW_BASE.
  change 6191136 with AGOT_MIDBEG. change 6993384 with AMIDBEG_CELL. change 6191144 with AGOT_MIDEND.
  change 6993392 with AMIDEND_CELL. change 6191152 with AGOT_HIEND. change 6993376 with AHIEND_CELL.
  repeat split; (eapply ACONST_cell; [exact AC| in_nth]).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition memtoshadow_post (ra sp gp tp t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (p : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 a2 a3 a4 a5 a6 a7,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (sh p)) (Z_to_bv 64 ASHADOW_BASE) a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m (seg_rom asegs).

Section MTS.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p : Z).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis G1 : rw_cells asegs m 6191128 [C8 (Z_to_bv 64 6990072)].
  Hypothesis C1 : rw_cells asegs m 6990072 [C8 (Z_to_bv 64 2147450880)].
  Hypothesis G2 : rw_cells asegs m 6191136 [C8 (Z_to_bv 64 6993384)].
  Hypothesis G3 : rw_cells asegs m 6191144 [C8 (Z_to_bv 64 6993392)].
  Hypothesis G4 : rw_cells asegs m 6191152 [C8 (Z_to_bv 64 6993376)].
  Hypothesis C4 : rw_cells asegs m 6993376 [C8 (Z_to_bv 64 (2 ^ 47 - 1)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].
  Hypothesis INM : in_mem p.

  Lemma memtoshadow_body : forall a1 : word,
    evt asegs (memtoshadow_post ra sp gp tp t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc p m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 memtoshadow_entry) fc None m (seg_rom asegs)).
  Proof.
    intros a1. unfold memtoshadow_entry.
    unfold in_mem, AHI_LO, AAPP_HI in INM. rewrite ASHADOW_BASE_val in *.
    do 7 zstep.
    replace (Z.land (Z.land (Z.b2z (2147450880 <? 2147450879) + -1) 18446744073709551615) 2147450879)
      with 2147450879 by reflexivity.
    zstep. if_cases K1; zify_cond K1.
    - (* [comment removed for export] *) zstep. zstep. rewrite Z.add_comm, sh_shiftr by lia. zstep. unfold memtoshadow_post. finish.
    - do 7 zstep.
      replace (0 + -1) with (-1) by reflexivity.
      zstep. if_cases K2; zify_cond K2; [| exfalso; lia].
      do 5 zstep.
      change (Z.shiftr (2^47 - 1) 3 + 2147450880) with 17594333495295.
      zstep. if_cases K3; zify_cond K3; [exfalso; lia|].
      zstep. if_cases K4; zify_cond K4; [exfalso; lia|].
      zstep. zstep. rewrite Z.add_comm, sh_shiftr by lia. zstep. unfold memtoshadow_post. finish.
  Qed.
End MTS.

(* [comment removed for export] *)
Ltac call_pure SPEC :=
  eapply evt_cut; [ eapply SPEC | ];
  [ .. | let ms' := fresh "ms'" in let PO := fresh "POST" in
         intros ms' PO; destruct_exs PO; subst ms';
         try (lazymatch goal with
              | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
                  replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
              end) ].

(* [comment removed for export] *)
Ltac head_of t := lazymatch t with ?f _ => head_of f | _ => t end.
Ltac call2 SPEC :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
      eapply evt_cut; [ eapply SPEC | let ms' := fresh "ms'" in let PO := fresh "POST" in
                                       intros ms' PO;
                                       (let T := type of PO in let h := head_of T in try unfold h in PO);
                                       zsimp_in PO; revert ms' PO; post_call segs m ]
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma sh_range_app : forall x, 0 <= x < AAPP_HI -> ASHADOW_BASE <= sh x < AHI_LO.
Proof. intros x Hx. unfold sh, AHI_LO, AAPP_HI in *. rewrite ASHADOW_BASE_val in *. Z.div_mod_to_equations. lia. Qed.

Lemma accessible_byte : forall m a n x, accessible m a n -> a <= x < a + n ->
  exists v, 0 <= v < 8 /\ bytes_at asegs m (sh x) [b8 v] /\ byte_ok v x.
Proof.
  intros m a n x (A0 & A1 & AA) Hx. destruct (AA x Hx) as (v & Hv & RD & OK).
  pose proof (sh_range_app x ltac:(lia)) as SR. unfold AHI_LO in SR. rewrite ASHADOW_BASE_val in SR.
  exists v. split; [exact Hv|]. split; [|exact OK].
  split; [lia|]. split; [cbn [length]; lia|]. intros i Hi. cbn [length] in Hi.
  destruct i; [|lia]. cbn [nth_error]. rewrite Z.add_0_r. exact RD.
Qed.

(* [comment removed for export] *)
Lemma accessible_zeros : forall m a n, accessible m a n -> 0 <= n ->
  bytes_at asegs m (ASHADOW_BASE + (a + 7) / 8) (zeros (Z.to_nat ((a + n) / 8 - (a + 7) / 8))).
Proof.
  intros m a n (A0 & A1 & AA) N0. unfold AAPP_HI in A1. rewrite ASHADOW_BASE_val.
  split; [Z.div_mod_to_equations; lia|]. split; [rewrite zeros_length; Z.div_mod_to_equations; lia|].
  intros i Hi. rewrite zeros_length in Hi. rewrite zeros_nth by exact Hi.
  set (x := 8 * ((a + 7) / 8) + 8 * Z.of_nat i + 7).
  assert (Hx : a <= x < a + n) by (subst x; Z.div_mod_to_equations; lia).
  destruct (AA x Hx) as (v & Hv & RD & OK).
  replace (2147450880 + (a + 7) / 8 + Z.of_nat i) with (sh x).
  2:{ unfold sh. rewrite ASHADOW_BASE_val. subst x. Z.div_mod_to_equations. lia. }
  rewrite RD. f_equal. f_equal. destruct OK as [->|OK]; [reflexivity|]. exfalso. subst x. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rip_post (ra sp gp tp t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 a1 a2 a3 a4 a5 a6 a7 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp) /\ ACONST m'.

Section RIP.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (a n lo : Z).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis AC : ACONST m.
  Hypothesis ACC : accessible m a n.
  Hypothesis Hn : 0 <= n <= 2^40.
  Hypothesis INM : in_app_mem a (a + n).
  Hypothesis ST0 : stk asegs m lo (bv_unsigned sp).
  Hypothesis LO : lo + RIP_STACK <= bv_unsigned sp.
  Hypothesis CEIL : AHI_LO <= lo.

  Notation POST := (rip_post ra sp gp tp t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo m).
  Notation SP64 := (Z_to_bv 64 (bv_unsigned sp + -64)).
  (* [comment removed for export] *)
  Notation RST pc x1 x5 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 mm :=
    (MS (mkR x1 SP64 gp tp x5 t1 t2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).

  Lemma shr3_sh : forall x, 0 <= x -> 2147450880 + Z.shiftr x 3 = sh x.
  Proof. intros x Hx. rewrite <- sh_shiftr' by exact Hx. rewrite ASHADOW_BASE_val. reflexivity. Qed.

  Section Inside.
    Variables (mm : word -> option byte) (junk : list byte).
    Hypothesis MIm : mem_inv asegs mm.
    Hypothesis FR : rw_cells asegs mm (bv_unsigned sp + -64) [CB 8 junk; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
    Hypothesis STm : stk asegs mm lo (bv_unsigned sp + -64).
    Hypothesis MU : munch [(bv_unsigned sp - RIP_STACK, bv_unsigned sp)] m mm.
    Hypothesis WM : wmono asegs m mm.
    Hypothesis G1 : rw_cells asegs mm 6191128 [C8 (Z_to_bv 64 6990072)].
    Hypothesis C1 : rw_cells asegs mm 6990072 [C8 (Z_to_bv 64 2147450880)].
    Hypothesis G2 : rw_cells asegs mm 6191136 [C8 (Z_to_bv 64 6993384)].
    Hypothesis G3 : rw_cells asegs mm 6191144 [C8 (Z_to_bv 64 6993392)].
    Hypothesis G4 : rw_cells asegs mm 6191152 [C8 (Z_to_bv 64 6993376)].
    Hypothesis C4 : rw_cells asegs mm 6993376 [C8 (Z_to_bv 64 (2 ^ 47 - 1)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].

    (* [comment removed for export] *)
    Lemma rip_exit : forall x1 x5 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21,
      evt asegs POST (RST 0x1c11e0 x1 x5 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 mm).
    Proof.
      intros. unfold RIP_STACK in *. unfold AHI_LO in CEIL.
      pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
      do 11 zstep.
      release_frame FR STm (bv_unsigned sp).
      assert (AC' : ACONST mm).
      { eapply ACONST_frame; [exact AC | exact MU | exact WM |].
        constructor; [|constructor]. apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia. }
      finish.
    Qed.
  End Inside.

  Section J.
      Variables (mm : word -> option byte) (junk : list byte).
      Hypothesis MIm : mem_inv asegs mm.
      Hypothesis FR : rw_cells asegs mm (bv_unsigned sp + -64) [CB 8 junk; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
      Hypothesis STm : stk asegs mm lo (bv_unsigned sp + -64).
      Hypothesis MU : munch [(bv_unsigned sp - RIP_STACK, bv_unsigned sp)] m mm.
      Hypothesis WM : wmono asegs m mm.
      Hypothesis G1 : rw_cells asegs mm 6191128 [C8 (Z_to_bv 64 6990072)].
      Hypothesis C1 : rw_cells asegs mm 6990072 [C8 (Z_to_bv 64 2147450880)].
      Hypothesis G2 : rw_cells asegs mm 6191136 [C8 (Z_to_bv 64 6993384)].
      Hypothesis G3 : rw_cells asegs mm 6191144 [C8 (Z_to_bv 64 6993392)].
      Hypothesis G4 : rw_cells asegs mm 6191152 [C8 (Z_to_bv 64 6993376)].
      Hypothesis C4 : rw_cells asegs mm 6993376 [C8 (Z_to_bv 64 (2 ^ 47 - 1)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].
      Variables (v1 v2 : Z).
      Hypothesis N0 : 0 < n.
      Hypothesis V1 : 0 <= v1 < 8.
      Hypothesis B1 : bytes_at asegs mm (sh a) [b8 v1].
      Hypothesis OK1 : byte_ok v1 a.
      Hypothesis V2 : 0 <= v2 < 8.
      Hypothesis B2 : bytes_at asegs mm (sh (a + n - 1)) [b8 v2].
      Hypothesis OK2 : byte_ok v2 (a + n - 1).
      Hypothesis ZB : bytes_at asegs mm (2147450880 + (a + 7) / 8) (zeros (Z.to_nat ((a + n) / 8 - (a + 7) / 8))).

      Lemma sh_mul8 : forall q, sh (8 * q) = 2147450880 + q.
      Proof. intros q. unfold sh. rewrite ASHADOW_BASE_val, Z.mul_comm, Z.div_mul by lia. reflexivity. Qed.

(* [comment removed for export] *)
      Lemma rip_j4 : forall x1 x5 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21,
        evt asegs POST (RST 0x1c11cc x1 x5 (Z_to_bv 64 a) (Z_to_bv 64 n) (Z_to_bv 64 (sh (8 * ((a + n) / 8)))) x11 x12 x13 x14 x15 x16 x17
                            x18 (Z_to_bv 64 (sh (8 * ((a + 7) / 8)))) x20 x21 mm).
      Proof.
        intros. unfold RIP_STACK in *. unfold AHI_LO in CEIL.
        pose proof INM as INM'. unfold in_app_mem, AHI_LO, AAPP_HI in INM'. rewrite ASHADOW_BASE_val in INM'.
        pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
        rewrite !sh_mul8.
        zstep. if_cases K1; zify_cond K1.
        { eapply rip_exit; eassumption. }
        zstep. zstep.
        match goal with |- context [Z_to_bv 64 ?e] =>
          lazymatch e with context [_ - _] =>
            replace e with ((a + n) / 8 - (a + 7) / 8) by (Z.div_mod_to_equations; lia) end end.
        zstep. call2 miz_body; try eassumption;
          [ Z.div_mod_to_equations; lia
          | rewrite unsigned_lit by lia; exact STm
          | rewrite unsigned_lit by lia; lia
          | left; Z.div_mod_to_equations; lia
          | Z.div_mod_to_equations; lia
          | ].
        try rewrite unsigned_lit in * by lia.
        zstep. if_cases K2; zify_cond K2; [exfalso; lia|].
        eapply rip_exit; try eassumption.
      Qed.

      (* [comment removed for export] *)
      Lemma rip_j3 : forall x1 x5 x12 x13 x14 x15 x16 x17 x20 x21,
        evt asegs POST (RST 0x1c1178 x1 x5 (Z_to_bv 64 a) (Z_to_bv 64 n) (Z_to_bv 64 (sh (8 * ((a + n) / 8)))) (Z_to_bv 64 2147450880)
                            x12 x13 x14 x15 x16 x17
                            (Z_to_bv 64 (a + n)) (Z_to_bv 64 (sh (8 * ((a + 7) / 8)))) x20 x21 mm).
      Proof.
        intros. unfold RIP_STACK in *. unfold AHI_LO in CEIL.
        pose proof INM as INM'. unfold in_app_mem, AHI_LO, AAPP_HI in INM'. rewrite ASHADOW_BASE_val in INM'.
        pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
        do 3 zstep. rewrite shr3_sh by lia. replace (a + n + -1) with (a + n - 1) by lia.
        pose proof (bytes_at_read asegs _ _ _ 0 1 B2 ltac:(lia) ltac:(cbn; lia)) as RD2.
        change (firstn 1 (skipn (Z.to_nat 0) [b8 v2])) with [b8 v2] in RD2. rewrite Z.add_0_r in RD2.
        zstep. unfold sxb. rewrite b8_signed_small by lia.
        zstep. if_cases K2; zify_cond K2.
        - apply rip_j4.
        - zstep. rewrite land_7. pose proof (Z.mod_pos_bound (a + n - 1) 8 ltac:(lia)) as MB.
          zstep. if_cases K3; zify_cond K3; rewrite !signed_of_Z in K3 by lia.
          + apply rip_j4.
          + exfalso. destruct OK2 as [?|?]; lia.
      Qed.

      (* [comment removed for export] *)
      Lemma rip_j2 : forall x1 x5 x10 x12 x13 x14 x15 x16 x17 x19 x20,
        evt asegs POST (RST 0x1c113c x1 x5 (Z_to_bv 64 a) (Z_to_bv 64 n) x10 (Z_to_bv 64 2147450880) x12 x13 x14 x15 x16 x17
                            (Z_to_bv 64 (a + n)) x19 x20 (Z_to_bv 64 6990072) mm).
      Proof.
        intros. unfold RIP_STACK in *. unfold AHI_LO in CEIL.
        pose proof INM as INM'. unfold in_app_mem, AHI_LO, AAPP_HI in INM'. rewrite ASHADOW_BASE_val in INM'.
        pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
        zstep. if_cases K1; zify_cond K1. { exfalso. lia. }
        do 3 zstep. rewrite !land_m8 by lia.
        zstep. call_pure memtoshadow_body. all: try eassumption.
        { unfold in_mem, AHI_LO, AAPP_HI. rewrite ASHADOW_BASE_val. Z.div_mod_to_equations. lia. }
        do 2 zstep.
        zstep. call_pure memtoshadow_body. all: try eassumption.
        { unfold in_mem, AHI_LO, AAPP_HI. rewrite ASHADOW_BASE_val. Z.div_mod_to_equations. lia. }
        do 3 zstep. rewrite shr3_sh by lia.
        pose proof (bytes_at_read asegs _ _ _ 0 1 B1 ltac:(lia) ltac:(cbn; lia)) as RD1.
        change (firstn 1 (skipn (Z.to_nat 0) [b8 v1])) with [b8 v1] in RD1. rewrite Z.add_0_r in RD1.
        zstep. unfold sxb. rewrite b8_signed_small by lia.
        zstep. if_cases K2; zify_cond K2.
        - apply rip_j3.
        - zstep. rewrite land_7. pose proof (Z.mod_pos_bound a 8 ltac:(lia)) as MB.
          zstep. if_cases K3; zify_cond K3; rewrite !signed_of_Z in K3 by lia.
          + exfalso. destruct OK1 as [?|?]; lia.
          + apply rip_j3.
      Qed.

      (* [comment removed for export] *)
      Lemma rip_j1 : forall x1 x5 x10 x13 x14 x15 x16 x17 x19 x20,
        evt asegs POST (RST 0x1c10f4 x1 x5 (Z_to_bv 64 a) (Z_to_bv 64 n) x10 (Z_to_bv 64 2147450880) (Z_to_bv 64 2147450879)
                            x13 x14 x15 x16 x17 s2 x19 x20 (Z_to_bv 64 6990072) mm).
      Proof.
        intros. unfold RIP_STACK in *. unfold AHI_LO in CEIL.
        pose proof INM as INM'. unfold in_app_mem, AHI_LO, AAPP_HI in INM'. rewrite ASHADOW_BASE_val in INM'.
        pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
        zstep. replace (n + a) with (a + n) by lia.
        zstep. if_cases K1; zify_cond K1.
        - apply rip_j2.
        - do 7 zstep. replace (0 + -1) with (-1) by reflexivity.
          zstep. if_cases K2; zify_cond K2; [| exfalso; lia].
          do 5 zstep.
          change (Z.shiftr (2^47 - 1) 3 + 2147450880) with 17594333495295.
          zstep. if_cases K3; zify_cond K3; [exfalso; lia|].
          zstep. if_cases K4; zify_cond K4; [exfalso; lia|].
          apply rip_j2.
      Qed.
  End J.

  Lemma rip_body : forall a1 : word,
    evt asegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 a) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 rip_entry) fc None m (seg_rom asegs)).
  Proof.
    intros a1. unfold rip_entry. pose proof LO as LO'. unfold RIP_STACK in LO.
    destruct (ACONST_layout m AC) as (G1 & C1 & G2 & G3 & G4 & C4).
    pose proof INM as INM'. unfold in_app_mem, AHI_LO, AAPP_HI in INM. pose proof CEIL as CEIL'. unfold AHI_LO in CEIL.
    rewrite ASHADOW_BASE_val in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
    pose proof (munch_refl [(bv_unsigned sp - RIP_STACK, bv_unsigned sp)] m) as MU. unfold RIP_STACK in MU.
    pose proof (wmono_refl asegs m) as WM.
    destruct (Z.eq_dec n 0) as [N0|N0].
    - pose proof ST0 as ST. carve_frame 64%nat ST.
      do 8 zstep.
      zstep. if_cases K0; zify_cond K0; [| exfalso; lia].
      eapply rip_exit; eassumption.
    - assert (N0' : 0 < n) by lia.
      destruct (accessible_byte m a n a ACC ltac:(lia)) as (v1 & V1 & B1 & OK1).
      destruct (accessible_byte m a n (a + n - 1) ACC ltac:(lia)) as (v2 & V2 & B2 & OK2).
      pose proof (accessible_zeros m a n ACC ltac:(lia)) as ZB. rewrite ASHADOW_BASE_val in ZB.
      pose proof (zeros_length (Z.to_nat ((a + n) / 8 - (a + 7) / 8))) as LZ.
      pose proof (sh_range_app a ltac:(unfold AAPP_HI; lia)) as SR1.
      pose proof (sh_range_app (a + n - 1) ltac:(unfold AAPP_HI; lia)) as SR2.
      unfold AHI_LO in SR1, SR2. rewrite ASHADOW_BASE_val in SR1, SR2.
      assert (SR3 : 2147450880 + (a + 7) / 8 + Z.of_nat (length (zeros (Z.to_nat ((a + n) / 8 - (a + 7) / 8)))) < 17594333495296).
      { rewrite LZ. Z.div_mod_to_equations. lia. }
      pose proof ST0 as ST. carve_frame 64%nat ST.
      do 8 zstep.
      zstep. if_cases K0; zify_cond K0; [exfalso; lia|].
      do 9 zstep.
      replace (Z.land (Z.land (Z.b2z (2147450880 <? 2147450879) + -1) 18446744073709551615) 2147450879)
        with 2147450879 by reflexivity.
      zstep. if_cases K1; zify_cond K1.
      + eapply (rip_j1 _ _ MI FR ST MU WM G1 C1 G2 G3 G4 C4 v1 v2 N0' V1 B1 OK1 V2 B2 OK2 ZB).
      + do 7 zstep. replace (0 + -1) with (-1) by reflexivity.
        zstep. if_cases K2; zify_cond K2; [| exfalso; lia].
        do 5 zstep.
        change (Z.shiftr (2^47 - 1) 3 + 2147450880) with 17594333495295.
        zstep. if_cases K3; zify_cond K3; [exfalso; lia|].
        zstep. if_cases K4; zify_cond K4; [exfalso; lia|].
        eapply (rip_j1 _ _ MI FR ST MU WM G1 C1 G2 G3 G4 C4 v1 v2 N0' V1 B1 OK1 V2 B2 OK2 ZB).
  Qed.
End RIP.

(* [comment removed for export] *)
Lemma rip_body_w :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0w a1w a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
    mem_inv asegs m -> ACONST m -> accessible m (bv_unsigned a0w) (bv_unsigned a1w) ->
    0 <= bv_unsigned a1w <= 2^40 -> in_app_mem (bv_unsigned a0w) (bv_unsigned a0w + bv_unsigned a1w) ->
    stk asegs m lo (bv_unsigned sp) -> lo + RIP_STACK <= bv_unsigned sp -> AHI_LO <= lo ->
    evt asegs (rip_post ra sp gp tp t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0w a1w a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 rip_entry) fc None m (seg_rom asegs)).
Proof.
  intros. pose proof (rip_body ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
                        (bv_unsigned a0w) (bv_unsigned a1w) lo) as R.
  rewrite !Z_to_bv_bv_unsigned in R. apply R; assumption.
Qed.
