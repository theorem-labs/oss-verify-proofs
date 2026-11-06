(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import SFModel Arr.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Prelim StrFun ScanInt.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import SFW1_lemmas.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Shadow.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ICP Require Import IcptKit I_memchr I_memcpy_i M_printf_lib N_ictx.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ICP Require Export M_shgetc_A.
Import ListNotations.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition rtext (T : Z) (txt pre post : list Z) : Prop :=
  txt = pre ++ 0%Z :: post /\ Forall (fun c => 0 < c < 256)%Z pre /\ Forall (fun c => 0 <= c < 256)%Z txt /\
  ((- (T + zlength pre + 1)) mod 8 <= zlength post)%Z /\ (zlength txt <= 2^40)%Z.

Definition win (p co : Z) : Z := if (p - co <? 257)%Z then p else (co + 257)%Z.
Lemma win_range : forall p co, (0 <= co <= p)%Z -> (co <= win p co <= p /\ (co < p -> co < win p co) /\ win p co <= co + 257)%Z.
Proof. intros p co H. unfold win. destruct (Z.ltb_spec0 (p - co) 257); lia. Qed.

Lemma nonul_pos : forall l, Forall (fun c => 0 < c < 256)%Z l -> ~ In (Z_to_bv 8 0) (zbytes l).
Proof.
  intros l H IN. unfold zbytes in IN. apply in_map_iff in IN. destruct IN as [c [E INc]].
  pose proof (proj1 (Forall_forall _ _) H c INc) as X. cbv beta in X.
  pose proof (f_equal bv_unsigned E) as E2. rewrite !unsigned_lit8 in E2 by lia. lia.
Qed.
Lemma Forall_skipn' : forall {A} (P : A -> Prop) k l, Forall P l -> Forall P (skipn k l).
Proof. intros A P k l H. rewrite <- (firstn_skipn k l) in H. apply Forall_app in H. LiaTuning.ctauto. Qed.
Lemma skipn_hd : forall (l : list byte) k b, nth_error l k = Some b -> skipn k l = b :: skipn (S k) l.
Proof.
  induction l as [|x l IH]; intros k b H; [destruct k; discriminate H|].
  destruct k as [|k]; cbn in H |- *; [injection H as ->; reflexivity|]. exact (IH k b H).
Qed.
Lemma hd_eq : forall (l : list byte) b, nth_error l 0 = Some b -> l = b :: skipn 1 l.
Proof. intros [|x l] b H; [discriminate H|]. cbn in H |- *. injection H as ->. reflexivity. Qed.
Lemma rw_cells_CB1 : forall m A bs, rw_cells asegs m A [CB 1 bs] -> exists b, rw_cells asegs m A [CB 1 [b]].
Proof.
  intros m A bs H. pose proof H as H'. destruct H as [[[W _] _] _]. cbn in W.
  destruct bs as [|b [|]]; try discriminate W. exists b. exact H'.
Qed.
Lemma rw_cells_CB0 : forall m A cs, rw_cells asegs m A cs -> rw_cells asegs m A (CB 0 [] :: cs).
Proof. intros m A cs [[W B] R]. split; [split|]; [split; [reflexivity | exact W] | exact B | exact R]. Qed.
Lemma rw_cells_unCB0 : forall m A cs, rw_cells asegs m A (CB 0 [] :: cs) -> rw_cells asegs m A cs.
Proof. intros m A cs [[[_ W] B] R]. split; [split|]; [exact W | exact B | exact R]. Qed.

Definition sread_len (off p : Z) : Z := if (off <? p)%Z then 1 else 0.

Definition sread_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Fp T D p off : Z) (txt : list Z) (dj : byte) (mode : word) (shend : Z) (shl shc : word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (sread_len off p)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(q - 2304, q); (Fp, Fp + 232); (D, D + 1)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' (q - 2304) (q)
    /\ rw_cells asegs m' Fp (ss_cells T (T + off + sread_len off p) (T + win p off) mode (T + win p off) shend shl shc)
    /\ rw_cells asegs m' D [CB 1 [if (off <? p)%Z then Z_to_bv 8 (znth txt off) else dj]]
    /\ bytes_at asegs m' T (zbytes txt).

Definition sread_stmt : Prop :=
  forall (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Fp T D p off rpos rend shend : Z) (txt pre post : list Z) (dj : byte) (mode shl shc : word) (lox qx : Z),
  rw_cells asegs m Fp (ss_cells T rpos rend mode (T + off) shend shl shc) ->
  rtext T txt pre post -> p = zlength pre -> (0 <= off <= p)%Z ->
  bytes_at asegs m T (zbytes txt) -> rw_cells asegs m D [CB 1 [dj]] ->
  (4096 <= T)%Z -> (T + 2^41 <= 2^63)%Z -> (0 <= rpos < 2^64)%Z -> (0 <= rend < 2^64)%Z -> (0 <= shend < 2^64)%Z ->
  (D + 1 <= Fp \/ Fp + 232 <= D)%Z -> (D + 1 <= T \/ T + zlength txt <= D)%Z -> (Fp + 232 <= T \/ T + zlength txt <= Fp)%Z ->
  stk asegs m (q - 2304) (q) -> (4096 <= q)%Z -> (q <= Fp)%Z -> (Fp + 232 <= 2^63)%Z ->
  (q <= D)%Z -> (D + 1 <= 2^63)%Z -> (T + zlength txt <= q - 2304 \/ q <= T)%Z ->
  (0 <= q)%Z -> (q < 2^63)%Z ->
  mem_inv asegs m ->
  ictx T p lox qx m -> iwin T p lox qx tp -> (lox <= q - 2304)%Z -> (D + 1 < qx)%Z ->
  evt asegs (sread_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp T D p off txt dj mode shend shl shc m)
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) (Z_to_bv 64 D) (Z_to_bv 64 1) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 STRING_READ) fc None m (seg_rom asegs)).

Lemma sread_spec : sread_stmt.
Proof.
  unfold sread_stmt. intros until qx. intros FC TXT Hp Hoff BY DC T0 T1 Rrp Rre Rsh SEP1 SEP2 SEP3 ST SPLO SPF SPF2 SPD SPD2 SPT Q0 Q1 MI IC IW LOX QXD.
  pose proof IW as IW'. destruct IW' as (CWT & W2T & NST & KLOX & LQX & QX47 & TPLO & TPHI).
  pose proof (munch_refl [(q - 2304, q); (Fp, Fp + 232); (D, D + 1)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  destruct TXT as (Htxt & NZ & BYT & AL & L40).
  pose proof (rw_cells_bound _ _ _ _ FC) as B. unfold ss_cells, w0 in FC. cbn [cells_size csize Nat.add] in B.
  assert (LTX : length (zbytes txt) = length txt) by apply zbytes_length.
  assert (LT3 : length txt = (length pre + S (length post))%nat) by (rewrite Htxt, length_app; reflexivity).
  pose proof (bytes_at_bound _ _ _ _ BY) as BB. rewrite LTX in BB.
  unfold STRING_READ, M64 in *. unfold zlength in *. pose_word_ranges.
  zs. carve_frame 64%nat ST.
  do 10 zs.

  set (k := Z.to_nat off).
  assert (SPLIT : zbytes txt = firstn k (zbytes pre) ++ (zbytes (skipn k pre) ++ Z_to_bv 8 0 :: zbytes post)).
  { rewrite Htxt, zbytes_app. cbn [zbytes map]. rewrite app_assoc. f_equal. rewrite zbytes_skipn. symmetry. apply firstn_skipn. }
  assert (LK : length (firstn k (zbytes pre)) = k) by (rewrite firstn_length, zbytes_length; lia).
  pose proof BY as BY2. rewrite SPLIT in BY2. apply bytes_at_app in BY2. destruct BY2 as [_ BY2]. rewrite LK in BY2.
  replace (T + Z.of_nat k)%Z with (T + off)%Z in BY2 by lia.
  assert (LSK : length (zbytes (skipn k pre)) = (length pre - k)%nat) by (rewrite zbytes_length, skipn_length; lia).
  zs. zs. zs. zs. zs.
  zs.

  assert (NN : ~ In (Z_to_bv 8 0) (zbytes (skipn k pre))) by (apply nonul_pos; apply Forall_skipn'; exact NZ).
  pose proof (memchr_res_cstr (T + off) 257 (zbytes (skipn k pre)) (zbytes post) NN) as MRC. rewrite LSK in MRC.
  set (RG := (if (Z.of_nat (length pre - k) <? 257)%Z then Z.of_nat (length pre - k) + 1 else 257)%Z).
  assert (RNG : ((if (memchr_res (T + off) 0 257 (zbytes (skipn k pre) ++ Z_to_bv 8 0 :: zbytes post) =? 0)%Z then 257
                  else memchr_res (T + off) 0 257 (zbytes (skipn k pre) ++ Z_to_bv 8 0 :: zbytes post) - (T + off) + 1) = RG)%Z).
  { rewrite MRC. unfold RG. destruct (Z.ltb_spec0 (Z.of_nat (length pre - k)) 257); [| reflexivity].
    replace (T + off + Z.of_nat (length pre - k) =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia). lia. }
  assert (RB : (1 <= RG /\ T + off + RG <= T + p + 1)%Z) by (unfold RG; destruct (Z.ltb_spec0 (Z.of_nat (length pre - k)) 257); lia).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
    assert (IC1 : ictx T p lox qx m1) by (eapply ictx_frame; [exact IC| exact IW| exact MU| exact WM| shw_solve]) end.
  destruct (ictx_text _ _ _ _ _ (T + off)%Z RG IC1 ltac:(lia) (proj2 RB) ltac:(lia)) as [ACm RDm].
  destruct (iwin_text _ _ _ _ _ (T + off)%Z RG IW ltac:(lia) (proj2 RB) ltac:(lia)) as (CWm & W2m & NSm).
  callx (eapply memchr_i_spec with (lo := (q - 2304)%Z) (A := (T + off)%Z) (c := 0%Z) (n := 257%Z) (buf := zbytes (skipn k pre) ++ Z_to_bv 8 0 :: zbytes post);
    [ exact BY2
    | apply memchr_ok_cstr; [exact NN | rewrite LSK, zbytes_length; clear -AL LT3 Hoff Hp T0; Z.div_mod_to_equations; lia ]
    | cbv zeta; rewrite RNG; exact ACm | cbv zeta; rewrite RNG; exact RDm | exact (ictx_env _ _ _ _ _ IC1)
    | cbv zeta; rewrite RNG; exact CWm | cbv zeta; rewrite RNG; exact W2m | cbv zeta; rewrite RNG; exact NSm
    | replace (q - 2304)%Z with (q + -64 - 2240)%Z by lia; replace (q + -64 - 2240)%Z with (q - 2304)%Z by lia; exact ST
    | lia | lia | lia
    | rewrite length_app; cbn [length]; rewrite LSK, zbytes_length; lia
    | hyp | reflexivity | reflexivity | reflexivity | lia | lia ]).
  clear IC1 ACm RDm.
  rewrite memchr_res_cstr in * by (apply nonul_pos; apply Forall_skipn'; exact NZ). rewrite LSK in *.
  clear RNG MRC. rename POST into BY2.
  destruct (Z.ltb_spec0 (Z.of_nat (length pre - k)) 257) as [WIN|WIN].
  -
    replace (T + off + Z.of_nat (length pre - k))%Z with (T + p)%Z by lia.
    assert (Ew : win p off = p) by (unfold win; rewrite (proj2 (Z.ltb_lt _ _)) by lia; reflexivity).
    zs. br K0. zs. zs. zs. br K1.
    +
      assert (Eo : off = p) by lia. replace (T + p - (T + off))%Z with 0%Z by lia.
      zs. zs. zs. zs. lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
   assert (IC2 : ictx T p lox qx m1) by (eapply ictx_frame; [exact IC| exact IW| exact MU| exact WM| shw_solve]) end.
 callx (eapply memcpy_i_spec with (lo := (q - 2304)%Z) (D := D) (S := (T + off)%Z) (n := 0%Z) (src := []) (junk := []);
   [ apply (proj1 (proj1 (rw_cells_app asegs _ D [CB 0 []] _) (rw_cells_CB0 _ _ _ DC))) | apply (proj1 (proj1 (bytes_at_app asegs _ (T + off) [] _) BY2)) | reflexivity | lia
   | exact (proj1 (ictx_stack _ _ _ _ _ D 0%Z IC2 ltac:(lia) ltac:(lia) ltac:(lia))) | exact (proj2 (ictx_stack _ _ _ _ _ D 0%Z IC2 ltac:(lia) ltac:(lia) ltac:(lia)))
   | exact (proj1 (ictx_text _ _ _ _ _ (T + off)%Z 0%Z IC2 ltac:(lia) ltac:(lia) ltac:(lia))) | exact (proj2 (ictx_text _ _ _ _ _ (T + off)%Z 0%Z IC2 ltac:(lia) ltac:(lia) ltac:(lia)))
   | exact (ictx_env _ _ _ _ _ IC2)
   | exact (proj1 (iwin_stack _ _ _ _ _ D 0%Z IW ltac:(lia) ltac:(lia) ltac:(lia))) | exact (proj1 (iwin_text _ _ _ _ _ (T + off)%Z 0%Z IW ltac:(lia) ltac:(lia) ltac:(lia)))
   | lia | lia | exact ST | lia | lia | lia | lia | lia | hyp | reflexivity | reflexivity | reflexivity ]).
 clear IC2.
      clear POST. replace (T + off + 0)%Z with (T + p)%Z by lia.
      do 15 zs.
      release_frame FR ST q.
      apply evt_done. unfold sread_post, sread_len. rewrite Ew. replace (off <? p) with false by (symmetry; apply Z.ltb_ge; lia).
      repeat (lazymatch goal with |- ex _ => eexists end).
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
      split; [unfold ss_cells, w0; rewrite Z.add_0_r; subst off; hyp|]. split; [hyp | hyp].
    +
      assert (NTH : nth_error (zbytes (skipn k pre)) 0 = Some (Z_to_bv 8 (znth txt off))).
      { rewrite zbytes_skipn, nth_error_skipn, Nat.add_0_r. subst k. rewrite zbytes_nth by (unfold zlength; lia).
        rewrite Htxt, znth_app_l by (unfold zlength; lia). reflexivity. }
      pose proof (hd_eq _ _ NTH) as SK. rewrite SK in BY2. cbn [app] in BY2.
      replace (T + p - (T + off))%Z with (p - off)%Z by lia.
      zs. zs. zs. zs. zs. lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
   assert (IC2 : ictx T p lox qx m1) by (eapply ictx_frame; [exact IC| exact IW| exact MU| exact WM| shw_solve]) end.
 callx (eapply memcpy_i_spec with (lo := (q - 2304)%Z) (D := D) (S := (T + off)%Z) (n := 1%Z) (src := [Z_to_bv 8 (znth txt off)]) (junk := [dj]);
   [ exact DC | apply (proj1 (proj1 (bytes_at_app asegs _ (T + off) [_] _) BY2)) | reflexivity | lia
   | exact (proj1 (ictx_stack _ _ _ _ _ D 1%Z IC2 ltac:(lia) ltac:(lia) ltac:(lia))) | exact (proj2 (ictx_stack _ _ _ _ _ D 1%Z IC2 ltac:(lia) ltac:(lia) ltac:(lia)))
   | exact (proj1 (ictx_text _ _ _ _ _ (T + off)%Z 1%Z IC2 ltac:(lia) ltac:(lia) ltac:(lia))) | exact (proj2 (ictx_text _ _ _ _ _ (T + off)%Z 1%Z IC2 ltac:(lia) ltac:(lia) ltac:(lia)))
   | exact (ictx_env _ _ _ _ _ IC2)
   | exact (proj1 (iwin_stack _ _ _ _ _ D 1%Z IW ltac:(lia) ltac:(lia) ltac:(lia))) | exact (proj1 (iwin_text _ _ _ _ _ (T + off)%Z 1%Z IW ltac:(lia) ltac:(lia) ltac:(lia)))
   | lia | lia | exact ST | lia | lia | lia | lia | lia | hyp | reflexivity | reflexivity | reflexivity ]).
 clear IC2.
      clear POST.
      do 15 zs.
      replace (T + off + (p - off))%Z with (T + p)%Z in * by lia.
      release_frame FR ST q.
      apply evt_done. unfold sread_post, sread_len. rewrite Ew. replace (off <? p) with true by (symmetry; apply Z.ltb_lt; lia).
      repeat (lazymatch goal with |- ex _ => eexists end).
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
      split; [unfold ss_cells, w0; hyp|]. split; [hyp | hyp].
  -
    assert (Ew : win p off = (off + 257)%Z) by (unfold win; rewrite (proj2 (Z.ltb_ge _ _)) by lia; reflexivity).
    assert (NTH : nth_error (zbytes (skipn k pre)) 0 = Some (Z_to_bv 8 (znth txt off))).
    { rewrite zbytes_skipn, nth_error_skipn, Nat.add_0_r. subst k. rewrite zbytes_nth by (unfold zlength; lia).
      rewrite Htxt, znth_app_l by (unfold zlength; lia). reflexivity. }
    pose proof (hd_eq _ _ NTH) as SK. rewrite SK in BY2. cbn [app] in BY2.
    zs. br K0. zs. zs. br K1.
    zs. zs. zs. zs. zs. lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
   assert (IC2 : ictx T p lox qx m1) by (eapply ictx_frame; [exact IC| exact IW| exact MU| exact WM| shw_solve]) end.
 callx (eapply memcpy_i_spec with (lo := (q - 2304)%Z) (D := D) (S := (T + off)%Z) (n := 1%Z) (src := [Z_to_bv 8 (znth txt off)]) (junk := [dj]);
   [ exact DC | apply (proj1 (proj1 (bytes_at_app asegs _ (T + off) [_] _) BY2)) | reflexivity | lia
   | exact (proj1 (ictx_stack _ _ _ _ _ D 1%Z IC2 ltac:(lia) ltac:(lia) ltac:(lia))) | exact (proj2 (ictx_stack _ _ _ _ _ D 1%Z IC2 ltac:(lia) ltac:(lia) ltac:(lia)))
   | exact (proj1 (ictx_text _ _ _ _ _ (T + off)%Z 1%Z IC2 ltac:(lia) ltac:(lia) ltac:(lia))) | exact (proj2 (ictx_text _ _ _ _ _ (T + off)%Z 1%Z IC2 ltac:(lia) ltac:(lia) ltac:(lia)))
   | exact (ictx_env _ _ _ _ _ IC2)
   | exact (proj1 (iwin_stack _ _ _ _ _ D 1%Z IW ltac:(lia) ltac:(lia) ltac:(lia))) | exact (proj1 (iwin_text _ _ _ _ _ (T + off)%Z 1%Z IW ltac:(lia) ltac:(lia) ltac:(lia)))
   | lia | lia | exact ST | lia | lia | lia | lia | lia | hyp | reflexivity | reflexivity | reflexivity ]).
 clear IC2.
    clear POST.
    do 15 zs.
    release_frame FR ST q.
    apply evt_done. unfold sread_post, sread_len. rewrite Ew. replace (off <? p) with true by (symmetry; apply Z.ltb_lt; lia).
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
    split; [unfold ss_cells, w0; hyp_cells|]. split; [hyp | hyp].
Qed.
