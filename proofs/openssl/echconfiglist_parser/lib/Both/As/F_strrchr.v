(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes Frame.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import STRW_tac.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface N6_tac.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope bv_scope.
Definition amemrchr_entry := 0x569de0%Z.
Definition astrrchr_real_entry := 0x56a5f8%Z.
(* [comment removed for export] *)
Definition ASTRRCHR_REAL_STACK : Z := (32 + AINTRIN_STACK)%Z.

(* [comment removed for export] *)
Fixpoint rfind (l : list byte) (c : byte) : option nat :=
  match l with
  | [] => None
  | x :: l' => match rfind l' c with
               | Some i => Some (S i)
               | None => if (bv_unsigned x =? bv_unsigned c)%Z then Some 0%nat else None
               end
  end.
Definition rfind_ret (A : Z) (r : option nat) : Z := match r with Some i => (A + Z.of_nat i)%Z | None => 0%Z end.

Lemma rfind_app_hit : forall l1 l2 c i, rfind l2 c = Some i -> rfind (l1 ++ l2) c = Some (length l1 + i)%nat.
Proof. induction l1 as [|x l1 IH]; intros l2 c i H; cbn; [exact H|]. rewrite (IH _ _ _ H). reflexivity. Qed.
Lemma rfind_app_miss : forall l1 l2 c, rfind l2 c = None -> rfind (l1 ++ l2) c = rfind l1 c.
Proof. induction l1 as [|x l1 IH]; intros l2 c H; cbn; [exact H|]. rewrite (IH _ _ H). reflexivity. Qed.
Lemma rfind_lt : forall l c i, rfind l c = Some i -> (i < length l)%nat.
Proof.
  induction l as [|x l IH]; intros c i H; cbn in H; [discriminate|].
  destruct (rfind l c) as [j|] eqn:E. { inversion H; subst. cbn. specialize (IH _ _ E). lia. }
  destruct (bv_unsigned x =? bv_unsigned c)%Z; inversion H; subst. cbn. lia.
Qed.
Lemma rfind1 : forall x c, rfind [x] c = (if (bv_unsigned x =? bv_unsigned c)%Z then Some 0%nat else None).
Proof. reflexivity. Qed.

Lemma skipn_nth_cons : forall (l : list byte) k x, nth_error l k = Some x -> skipn k l = x :: skipn (S k) l.
Proof.
  induction l as [|y l IH]; intros [|k] x H; cbn in H |- *; try discriminate.
  - inversion H. reflexivity.
  - exact (IH k x H).
Qed.

(* [comment removed for export] *)
Definition memrchr_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A : Z) (l : list byte) (c : byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (rfind_ret A (rfind l c))) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m (seg_rom asegs).

Section MR.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (l : list byte) (A : Z) (c : byte).
  Hypothesis BY : bytes_at asegs m A l.
  Hypothesis LEN : (Z.of_nat (length l) < 2^64)%Z.
  Notation POST := (memrchr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A l c m).
  Notation ST pc x10 x12 x13 x14 :=
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x10 (Z_to_bv 64 (bv_unsigned c)) x12 x13 x14 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom asegs)).

  (* [comment removed for export] *)
  Lemma mr_loop : forall (k : nat) x10 x14,
    (k <= length l)%nat -> rfind (skipn k l) c = None ->
    evt asegs POST (ST 0x569dec x10 (Z_to_bv 64 (A + Z.of_nat k)) (Z_to_bv 64 (- Z.of_nat k)) x14).
  Proof.
    induction k as [|k IH]; intros x10 x14 Hk NF; pose proof (bytes_at_bound _ _ _ _ BY) as AB; pose proof (byte_range c) as CR.
    - (* [comment removed for export] *)
      zstep. if_true. zstep. zstep. change (skipn 0 l) with l in NF. unfold memrchr_post, rfind_ret. rewrite NF. finish.
    - destruct (nth_error l k) as [x|] eqn:HX. 2:{ exfalso. apply nth_error_None in HX. lia. }
      pose proof (byte_range x) as XR.
      zstep. if_cases K0; zify_cond K0. { exfalso. revert K0. rewrite ?unsigned_lit_wrap, ?land_ones64. intros K0. Z.div_mod_to_equations. lia. }
      (* [comment removed for export] *)
      pose proof (u8ro_read asegs m A l (Z.of_nat k) x (Z_to_bv 64 (A + Z.of_nat (S k) + -1)) BY ltac:(rewrite Nat2Z.id; exact HX) ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
      zstep. clear RD.
      lazymatch goal with |- evt _ _ ?ms => let ms' := eval cbv beta in ms in change ms with ms' end.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. if_cases K; zify_cond K.
      + (* [comment removed for export] *)
        replace (A + Z.of_nat (S k) + -1)%Z with (A + Z.of_nat k)%Z by lia. replace (- Z.of_nat (S k) + 1)%Z with (- Z.of_nat k)%Z by lia.
        apply IH; [lia|].
        rewrite (skipn_nth_cons l k x HX). change (x :: skipn (S k) l) with ([x] ++ skipn (S k) l).
        rewrite (rfind_app_miss [x] _ _ NF). rewrite rfind1. rewrite ?unsigned_lit in K by lia.
        destruct (Z.eqb_spec (bv_unsigned x) (bv_unsigned c)); [exfalso; apply K; congruence| reflexivity].
      + (* [comment removed for export] *)
        zstep. unfold memrchr_post, rfind_ret.
        replace (rfind l c) with (Some k).
        2:{ rewrite <- (firstn_skipn k l). rewrite (skipn_nth_cons l k x HX). change (x :: skipn (S k) l) with ([x] ++ skipn (S k) l).
            symmetry. rewrite (rfind_app_hit (firstn k l) ([x] ++ skipn (S k) l) c 0); [rewrite length_firstn; f_equal; lia|].
            rewrite (rfind_app_miss [x] _ _ NF), rfind1. rewrite ?unsigned_lit in K by lia.
            destruct (Z.eqb_spec (bv_unsigned x) (bv_unsigned c)); [reflexivity| exfalso; lia]. }
        replace (A + Z.of_nat (S k) + -1)%Z with (A + Z.of_nat k)%Z by lia. finish.
  Qed.
End MR.

Section HC.
  Context {HCEIL : HeapCeil}.
  (* [comment removed for export] *)
  Hypothesis SL : strlen_icpt_stmt.

(* [comment removed for export] *)
Definition astrrchr_real_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A : Z) (c : word) (str slack : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (rfind_ret A (rfind (str ++ [Z_to_bv 8 0]) (Z_to_bv 8 (bv_unsigned c))))) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 4128, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ bytes_at asegs m' A (str ++ Z_to_bv 8 0 :: slack)
    /\ ACONST m'.   (* [comment removed for export] *)

Lemma astrrchr_real_body : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (str slack : list byte) (lo : Z),
  bytes_at asegs m (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack) ->
  ~ In (Z_to_bv 8 0) str ->
  ((- (bv_unsigned a0 + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z ->
  accessible m (bv_unsigned a0) (Z.of_nat (length str) + 1) ->
  shvis m (bv_unsigned a0) (bv_unsigned a0 + Z.of_nat (length str) + 1) ->
  stk asegs m lo (bv_unsigned sp) -> (aceil <= lo)%Z -> (lo <= bv_unsigned sp - ASTRRCHR_REAL_STACK)%Z ->
  mem_inv asegs m -> ACONST m ->
  (Z.of_nat (length str) + 1 <= 2^40)%Z -> in_app_mem (bv_unsigned a0) (bv_unsigned a0 + Z.of_nat (length str) + 1) ->
  (bv_unsigned a0 + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= lo \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
  evt asegs (astrrchr_real_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0) a1 str slack lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 astrrchr_real_entry) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros STR NONUL PAD ACC SV ST CEIL LO MI AC N40 INM DJ.
  unfold astrrchr_real_entry, ASTRRCHR_REAL_STACK, AINTRIN_STACK in *.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64)%Z in SPR.
  pose proof (bv_unsigned_in_range _ a1) as CR. change (bv_modulus 64) with (2^64)%Z in CR.
  pose proof (bytes_at_bound _ _ _ _ STR) as SB. rewrite length_app in SB. cbn [length] in SB.
  pose proof aceil_range as CP.
  pose proof (munch_refl [(bv_unsigned sp - (32 + 4096), bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof ST as ST0. carve_frame 32%nat ST. zstep. zstep. zstep. zstep. zstep. zstep.
  (* [comment removed for export] *)
  pose proof INM as INM'. unfold in_app_mem, AHI_LO, AAPP_HI in INM'. rewrite ASHADOW_BASE_val in INM'.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    assert (ACCm : accessible mx (bv_unsigned a0) (Z.of_nat (length str) + 1));
    [ eapply accessible_transport; [exact ACC | exact MU |];
      intros x Hx; destruct ACC as (? & ? & _); cbn; unfold sh, AAPP_HI in *; rewrite ASHADOW_BASE_val in *; Z.div_mod_to_equations; lia
    | assert (SVm : shvis mx (bv_unsigned a0) (bv_unsigned a0 + Z.of_nat (length str) + 1));
      [ eapply shvis_transport; [exact SV | exact MU | exact WM |];
        unfold disjoint_from, sh, hull_lo, hull_hi; rewrite ASHADOW_BASE_val; cbn [fst snd]; constructor; [| constructor];
        Z.div_mod_to_equations; lia
      | assert (ACm : ACONST mx);
        [ eapply ACONST_frame; [exact AC | exact MU | exact WM |];
          constructor; [| constructor]; apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia | ] ] ]
  end.
  (* [comment removed for export] *)
  zstep. zstep. eapply evt_cut.
  { eapply (SL _ _ gp tp t0 t1 t2 a1 a0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc _ str slack lo);
      rewrite ?unsigned_lit by lia;
      [ exact STR | exact NONUL | exact PAD | exact ACCm | exact SVm
      | exact ST | exact CEIL | unfold AINTRIN_STACK; lia | eassumption | exact ACm | exact N40 | exact INM | lia ]. }
  intros ms2 PC. unfold astrlen_post in PC.
  destruct PC as (u0 & u1 & u2 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & u3 & u4 & u5 & u6 & m2 & -> & MU2 & WM2 & MI2 & ST2lo & BY2 & AC2).
  rewrite ?unsigned_lit in MU2, ST2lo by lia. unfold AINTRIN_STACK in MU2.
  replace (ret_pc (Z_to_bv 64 0x56a618)) with (Z_to_bv 64 0x56a618) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  lazymatch type of FR with rw_cells _ _ _ ?cs => assert (FR2 : rw_cells asegs m2 (bv_unsigned sp + -32) cs) end.
  { eapply rw_cells_transport; [exact FR| exact MU2| exact WM2|]. cbn. lia. }
  assert (ST2 : stk asegs m2 lo (bv_unsigned sp + -32)) by exact ST2lo.
  assert (MU' : munch [(bv_unsigned sp - (32 + 4096), bv_unsigned sp)]%Z m m2).
  { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU2]. intros x Hx. cbn in Hx |- *. lia. }
  assert (WM' : wmono asegs m m2) by (eapply wmono_trans; [exact WM| exact WM2]).
  clear MU WM MU2 WM2 FR ST MI STR.
  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  release_frame FR2 ST2 (bv_unsigned sp).
  (* [comment removed for export] *)
  zstep. zstep. zstep.
  set (c := Z_to_bv 8 (bv_unsigned a1)).
  assert (EC : Z.land (bv_unsigned a1) 255 = bv_unsigned c).
  { subst c. rewrite Z_to_bv_unsigned. change 255%Z with (Z.ones 8). rewrite Z.land_ones by lia. reflexivity. }
  rewrite EC.
  assert (BYc : bytes_at asegs m2 (bv_unsigned a0) (str ++ [Z_to_bv 8 0])).
  { change (str ++ Z_to_bv 8 0 :: slack) with (str ++ ([Z_to_bv 8 0] ++ slack)) in BY2. rewrite app_assoc in BY2. apply bytes_at_app in BY2. exact (proj1 BY2). }
  replace (bv_unsigned a0 + (Z.of_nat (length str) + 1))%Z with (bv_unsigned a0 + Z.of_nat (S (length str)))%Z by lia.
  replace (0 - (Z.of_nat (length str) + 1))%Z with (- Z.of_nat (S (length str)))%Z by lia.
  eapply evt_mono.
  { apply (mr_loop ra sp gp tp u0 u1 u2 s0 s1 w5 w6 w7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F fc m2 (str ++ [Z_to_bv 8 0]) (bv_unsigned a0) c BYc
             ltac:(rewrite length_app; cbn [length]; lia) (S (length str))); [rewrite length_app; cbn [length]; lia|].
    rewrite skipn_all2 by (rewrite length_app; cbn [length]; lia). reflexivity. }
  intros ms3 PM. unfold memrchr_post in PM. destruct PM as (v0 & v1 & v2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & v3 & v4 & v5 & v6 & ->).
  unfold astrrchr_real_post. subst c. do 15 eexists. split; [reflexivity|].
  rewrite ?unsigned_lit by lia. auto 10.
Qed.
End HC.
