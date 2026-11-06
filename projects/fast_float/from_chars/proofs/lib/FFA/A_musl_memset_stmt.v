(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
Import ListNotations.

Module A_imemmove_stmt.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.

Notation ASEGS := Asan.M.loaded_segments.

Definition imemmove_entry : Z := 0x733e8.

Definition imemmove_post
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (n : Z) (bs : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (a1 a2 a3 a4 a5 a6 : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ASEGS)
    /\ munch [(bv_unsigned a0, bv_unsigned a0 + n)]%Z m m'
    /\ wmono ASEGS m m'
    /\ u8arr ASEGS m' (bv_unsigned a0) bs.

Definition imemmove_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs old : list byte),
    bytes_at ASEGS m (bv_unsigned a1) bs ->
    u8arr ASEGS m (bv_unsigned a0) old ->
    length old = length bs ->
    Z.of_nat (length bs) = bv_unsigned a2 ->
    (bv_unsigned a2 < 2^63)%Z ->
    (bv_unsigned a0 + bv_unsigned a2 < 2^64)%Z ->
    (bv_unsigned a1 + bv_unsigned a2 < 2^64)%Z ->
    evt ASEGS (imemmove_post ra sp gp tp t0 t1 t2 s0 s1 a0 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                 F fc (bv_unsigned a2) bs m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x733e8) fc None m (seg_rom ASEGS)).
End A_imemmove_stmt.

Module A_imemmove.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FFA.A_musl_memset_stmt.A_imemmove_stmt.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma split1_back : forall {A} (l : list A), (1 <= length l)%nat ->
  exists l' b, l = l' ++ [b] /\ length l' = (length l - 1)%nat.
Proof.
  intros A l H.
  pose proof (firstn_skipn (length l - 1) l) as E.
  assert (L : length (skipn (length l - 1) l) = 1%nat) by (rewrite skipn_length; lia).
  destruct (skipn (length l - 1) l) as [|b [|x l']]; cbn in L; try lia.
  exists (firstn (length l - 1) l), b. split; [symmetry; exact E|].
  rewrite firstn_length. lia.
Qed.

Section Proof.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs : list byte).
  Notation D := (bv_unsigned a0). Notation S := (bv_unsigned a1). Notation N := (bv_unsigned a2).
  Notation POST := (imemmove_post ra sp gp tp t0 t1 t2 s0 s1 a0 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc N bs m).
  Hypothesis LBS : Z.of_nat (length bs) = N.
  Hypothesis BD : (0 <= D /\ D + N < 2^64)%Z.
  Hypothesis BS : (0 <= S /\ S + N < 2^64)%Z.

  (* [comment removed for export] *)
  #[using="LBS BD BS"] Lemma loopF : forall (k : nat) (K : Z) (mq : word -> option byte) (done todo rest : list byte) (a4 a5 a6 : word),
    (Z.to_nat (N - K) <= k)%nat ->
    u8arr ASEGS mq D done -> u8arr ASEGS mq (D + K) todo -> bytes_at ASEGS mq (S + K) rest ->
    Z.of_nat (length done) = K -> length todo = length rest -> done ++ rest = bs ->
    munch [(D, D + N)]%Z m mq -> wmono ASEGS m mq ->
    (D < S)%Z -> (0 <= K < N)%Z ->
    forall (w1 w2 w3 : word), w1 = Z_to_bv 64 (S + K) -> w2 = Z_to_bv 64 (D + N) -> w3 = Z_to_bv 64 (D + K) ->
    evt ASEGS POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 w1 w2 w3 a4 a5 a6 a7
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x733f8) fc None mq (seg_rom ASEGS)).
  Proof. LiaFast.lf_pins (fun (LBS BD BS : LiaFast.U) => LiaFast.u0).
    induction k as [|k IH]; intros K mq done todo rest a4 a5 a6 Hk DONE TODO SRCR Ld Lt Hbs MU WM DS HK w1 w2 w3 -> -> ->; [lia|].
    pose proof (bytes_at_bound _ _ _ _ SRCR) as Br.
    assert (Lr : (1 <= length rest)%nat).
    { apply (f_equal (@length byte)) in Hbs. rewrite app_length in Hbs. lia. }
    destruct rest as [|b rest']; [cbn in Lr; lia|].
    destruct todo as [|c todo']; [cbn in Lt; lia|].
    (* [comment removed for export] *)
    pose proof (bytes_at_read ASEGS mq (S + K) (b :: rest') 0 1 SRCR ltac:(lia) ltac:(cbn; lia)) as RD.
    change (firstn 1 (skipn (Z.to_nat 0) (b :: rest'))) with [b] in RD. rewrite Z.add_0_r in RD.
    step. (* [comment removed for export] *)
    clear RD.
    (* [comment removed for export] *)
    change (c :: todo') with ([c] ++ todo') in TODO. change (b :: rest') with ([b] ++ rest') in SRCR.
    apply (proj1 (u8arr_app ASEGS mq (D + K) [c] todo')) in TODO. destruct TODO as [HEAD TODO].
    cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in TODO.
    apply bytes_at_app in SRCR. destruct SRCR as [_ SRCR]. cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in SRCR.
    pose proof (u8arr_store_ok ASEGS mq (D + K) [c] 0 _ HEAD ltac:(cbn; lia) eq_refl) as SOK.
    rewrite Z.add_0_r in SOK.
    step. (* [comment removed for export] *)
    rewrite le1_zxb.
    pose proof (u8arr_write_all ASEGS mq (D + K) [c] [b] HEAD eq_refl) as HEAD'.
    clear HEAD SOK.
    store_done.
    (* [comment removed for export] *)
    assert (DONE' : u8arr ASEGS m0 D (done ++ [b])).
    { apply (proj2 (u8arr_app ASEGS m0 D done [b])). split; [exact DONE|]. rewrite Ld. exact HEAD'. }
    clear DONE HEAD'.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hc.
    - (* [comment removed for export] *)
      cond_cleanup Hc.
      eapply (IH (K + 1)%Z m0 (done ++ [b]) todo' rest'); try eassumption; try lia.
      all: first [ replace (D + (K + 1))%Z with (D + K + 1)%Z by lia; exact TODO
                 | replace (S + (K + 1))%Z with (S + K + 1)%Z by lia; exact SRCR
                 | rewrite app_length; cbn; lia
                 | cbn in Lt; lia
                 | rewrite <- app_assoc; exact Hbs
                 | reflexivity
                 | f_equal; lia ].
    - (* [comment removed for export] *)
      cond_cleanup Hc.
      assert (rest' = []) as ->.
      { apply (f_equal (@length byte)) in Hbs. rewrite !app_length in Hbs. cbn in Hbs.
        destruct rest'; [reflexivity| cbn in Hbs; exfalso; lia]. }
      subst bs.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      apply evt_done. unfold imemmove_post.
      do 7 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. exact DONE'.
  Qed.

  (* [comment removed for export] *)
  #[using="LBS BD"] Lemma loopB : forall (k : nat) (K : Z) (mq : word -> option byte) (todo done rest : list byte) (a4 a5 a6 : word),
    (Z.to_nat K <= k)%nat ->
    u8arr ASEGS mq D todo -> u8arr ASEGS mq (D + K) done -> bytes_at ASEGS mq S rest ->
    Z.of_nat (length todo) = K -> length rest = length todo -> rest ++ done = bs ->
    munch [(D, D + N)]%Z m mq -> wmono ASEGS m mq ->
    (S < D)%Z -> (1 <= K <= N)%Z ->
    forall (w3 : word), w3 = Z_to_bv 64 (K - 1) ->
    evt ASEGS POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 (Z_to_bv 64 1) w3 a4 a5 a6 a7
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x73420) fc None mq (seg_rom ASEGS)).
  Proof. LiaFast.lf_pins (fun (LBS BD : LiaFast.U) => LiaFast.u0).
    induction k as [|k IH]; intros K mq todo done rest a4 a5 a6 Hk TODO DONE SRCR Lt Lr Hbs MU WM DS HK w3 ->; [lia|].
    pose proof (bytes_at_bound _ _ _ _ SRCR) as Br.
    pose proof (u8arr_bound _ _ _ _ DONE) as Bdn.
    destruct (split1_back rest ltac:(lia)) as (rest0 & b & -> & Lr0).
    destruct (split1_back todo ltac:(lia)) as (todo0 & c & -> & Lt0).
    rewrite app_length in Lr0, Lt0. cbn in Lr0, Lt0.
    (* [comment removed for export] *)
    apply bytes_at_app in SRCR. destruct SRCR as [SRC0 SRCB].
    replace (Z.of_nat (length rest0)) with (K - 1)%Z in SRCB by (rewrite app_length in Lr; cbn in Lr; lia).
    step. (* [comment removed for export] *)
    pose proof (bytes_at_read ASEGS mq (S + (K - 1)) [b] 0 1 SRCB ltac:(lia) ltac:(cbn; lia)) as RD.
    change (firstn 1 (skipn (Z.to_nat 0) [b])) with [b] in RD.
    replace (wa (S + (K - 1) + 0)) with (Z_to_bv 64 (S + (K - 1)))%Z in RD by (unfold wa; f_equal; lia).
    step. (* [comment removed for export] *)
    clear RD SRCB.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    (* [comment removed for export] *)
    apply (proj1 (u8arr_app ASEGS mq D todo0 [c])) in TODO. destruct TODO as [TODO LAST].
    assert (EK : Z.of_nat (length todo0) = (K - 1)%Z) by (rewrite app_length in Lt; cbn in Lt; lia).
    assert (ER : Z.of_nat (length rest0) = (K - 1)%Z) by (rewrite !app_length in Lr; cbn in Lr; lia).
    rewrite EK in LAST. clear Lr0 Lt0.
    pose proof (u8arr_store_ok ASEGS mq (D + (K - 1)) [c] 0 _ LAST ltac:(cbn; lia) eq_refl) as SOK.
    replace (wa (D + (K - 1) + 0)) with (Z_to_bv 64 (D + (K - 1)))%Z in SOK by (unfold wa; f_equal; lia).
    step. (* [comment removed for export] *)
    rewrite le1_zxb.
    pose proof (u8arr_write_all ASEGS mq (D + (K - 1)) [c] [b] LAST eq_refl) as LAST'.
    clear LAST SOK.
    store_done.
    (* [comment removed for export] *)
    assert (DONE' : u8arr ASEGS m0 (D + (K - 1)) ([b] ++ done)).
    { apply (proj2 (u8arr_app ASEGS m0 (D + (K - 1)) [b] done)). split; [exact LAST'|].
      replace (D + (K - 1) + Z.of_nat (length [b]))%Z with (D + K)%Z by (change (length [b]) with 1%nat; lia). exact DONE. }
    clear DONE LAST'.
    step. (* [comment removed for export] *)
    if_cases Hc.
    - (* [comment removed for export] *)
      cond_cleanup Hc.
      eapply (IH (K - 1)%Z m0 todo0 ([b] ++ done) rest0); try eassumption; try lia.
      all: first [ exact TODO | exact DONE' | exact SRC0
                 | rewrite <- app_assoc in Hbs; exact Hbs
                 | reflexivity
                 | lia
                 | f_equal; lia ].
    - (* [comment removed for export] *)
      cond_cleanup Hc.
      assert (todo0 = []) as ->. { destruct todo0; [reflexivity| cbn in EK; exfalso; lia]. }
      assert (rest0 = []) as ->. { destruct rest0; [reflexivity| cbn in ER; exfalso; lia]. }
      cbn [app] in Hbs. subst bs.
      step. (* [comment removed for export] *)
      apply evt_done. unfold imemmove_post.
      do 7 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
      replace D with (D + (K - 1))%Z by lia. exact DONE'.
  Qed.
End Proof.

Lemma imemmove_spec : imemmove_stmt.
Proof.
  unfold imemmove_stmt. intros until old. intros SRC DST LEN N N63 NW0 NW1.
  pose proof (bytes_at_bound _ _ _ _ SRC) as Bs.
  pose proof (u8arr_bound _ _ _ _ DST) as Bd.
  pose proof (bv_unsigned_in_range 64 a2) as R2. unfold bv_modulus in R2.
  pose proof (munch_refl [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z m) as MU.
  pose proof (wmono_refl ASEGS m) as WM.
  step. (* [comment removed for export] *)
  if_cases Hge.
  - (* [comment removed for export] *)
    cond_cleanup Hge.
    step. (* [comment removed for export] *)
    if_cases Hge2.
    + (* [comment removed for export] *)
      cond_cleanup Hge2.
      assert (E : bv_unsigned a1 = bv_unsigned a0) by lia.
      step. (* [comment removed for export] *)
      apply evt_done. unfold imemmove_post.
      do 7 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
      destruct DST as [_ WR]. split; [rewrite <- E; exact SRC| rewrite LEN in WR; exact WR].
    + cond_cleanup Hge2.
      step. (* [comment removed for export] *)
      if_cases Hle.
      * (* [comment removed for export] *)
        cond_cleanup Hle.
        assert (HN0 : bv_unsigned a2 = 0%Z).
        { destruct (Z.ltb_spec0 0 (bv_unsigned a2)); destruct (Z.ltb_spec0 (bv_unsigned a2) 9223372036854775808); cbn in Hle; try discriminate; lia. }
        assert (bs = []) as ->. { destruct bs; [reflexivity| cbn in N; exfalso; lia]. }
        assert (old = []) as ->. { destruct old; [reflexivity| cbn in LEN; exfalso; lia]. }
        step. (* [comment removed for export] *)
        apply evt_done. unfold imemmove_post.
        do 7 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. exact DST.
      * cond_cleanup Hle.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        eapply loopB with (k := Z.to_nat (bv_unsigned a2)) (K := bv_unsigned a2) (todo := old) (done := []) (rest := bs);
          try eassumption; try lia.
        all: first [ (* [comment removed for export] *)
                     destruct DST as [BY WR]; split; [apply bytes_at_nil; lia|];
                     cbn; destruct WR as (? & ? & W); split; [lia|]; split; [lia|]; intros i Hi; lia
                   | rewrite app_nil_r; reflexivity
                   | f_equal; lia ].
  - (* [comment removed for export] *)
    cond_cleanup Hge.
    step. (* [comment removed for export] *)
    if_cases Hle.
    + cond_cleanup Hle.
      assert (HN0 : bv_unsigned a2 = 0%Z).
      { destruct (Z.ltb_spec0 0 (bv_unsigned a2)); destruct (Z.ltb_spec0 (bv_unsigned a2) 9223372036854775808); cbn in Hle; try discriminate; lia. }
      assert (bs = []) as ->. { destruct bs; [reflexivity| cbn in N; exfalso; lia]. }
      assert (old = []) as ->. { destruct old; [reflexivity| cbn in LEN; exfalso; lia]. }
      step. (* [comment removed for export] *)
      apply evt_done. unfold imemmove_post.
      do 7 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. exact DST.
    + cond_cleanup Hle.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      eapply loopF with (k := Z.to_nat (bv_unsigned a2)) (K := 0%Z) (done := []) (todo := old) (rest := bs);
        try eassumption; try lia.
      all: first [ rewrite Z.add_0_r; exact DST
                 | rewrite Z.add_0_r; exact SRC
                 | reflexivity
                 | rewrite Z.add_0_r; symmetry; apply Z_to_bv_bv_unsigned
                 | f_equal; lia
                 | (* [comment removed for export] *)
                   destruct DST as [BY WR]; split; [apply bytes_at_nil; lia|];
                   cbn; destruct WR as (? & ? & W); split; [lia|]; split; [lia|]; intros i Hi; lia ].
Qed.
End A_imemmove.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Open Scope bv_scope.

Notation ASEGS := Asan.M.loaded_segments.

Definition memset_entry : Z := 0xd3088.

(* [comment removed for export] *)
Definition fillb (c : word) : byte := Z_to_bv 8 (bv_unsigned c).

Lemma fillb_zero : fillb (Z_to_bv 64 0) = Z_to_bv 8 0.
Proof. reflexivity. Qed.

Definition memset_post
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (c : word) (n : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (a1 a2 a3 a4 a5 a6 : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ASEGS)
    /\ munch [(bv_unsigned a0, bv_unsigned a0 + n)]%Z m m'
    /\ wmono ASEGS m m'
    /\ u8arr ASEGS m' (bv_unsigned a0) (repeat (fillb c) (Z.to_nat n)).

Definition memset_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (old : list byte),
    u8arr ASEGS m (bv_unsigned a0) old ->
    Z.of_nat (length old) = bv_unsigned a2 ->
    (bv_unsigned a0 mod 8 = 0)%Z ->
    evt ASEGS (memset_post ra sp gp tp t0 t1 t2 s0 s1 a0 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                 F fc a1 (bv_unsigned a2) m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0xd3088) fc None m (seg_rom ASEGS)).
